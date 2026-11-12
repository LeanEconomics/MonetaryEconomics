/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5Distorted67

/-!
# The branch of distorted steady states with transactions frictions (Proposition 6.7)

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1, (4.6), p. 421, Assumption 6.1, p. 422,
and Appendix E.4, (E.15)–(E.16), pp. 699–700.

`TidyR5Distorted67.prop67_distorted` takes a branch `(Ȳ_b, m̄_b)` of distorted steady states of
the smooth extension `Ũ` as a hypothesis. Here:

* **`branch67`**: the branch is CONSTRUCTED by the two-dimensional inverse function theorem
  (Mathlib's `HasStrictFDerivAt.localInverse`) applied to
  `Ψ(Y, m) = (1 − v_y/ũ_c, ũ_m/ũ_c)`, whose Jacobian at `(Y*, mˢ)` has determinant `Ω_mc/η_i` up to
  the factor `1/(Y*mˢ)` (`psi67_deriv_inj`); it is locally unique.
* **`prop67_on_branch`**: Proposition 6.7 around the constructed steady state, with no
  steady-state hypothesis left.
* **`foc_actual`**, **`prop67_actual_distorted`** (the smooth-extension caveat): if `U` is flat in
  `m` at and above satiation (Assumption 6.1: `u_m = 0` for `m ≥ mˢ`), a steady state of the
  ACTUAL utility with `Δ̄ ≠ 0` and `u_c ≠ 0` lies strictly below satiation, where `U = Ũ`, so its
  conditions are those of `Ũ`; Proposition 6.7 then holds with the steady-state conditions stated
  for `U` itself. When `Δ̄ = 0` the actual conditions are `u_m = 0`, which every `m̄ ≥ mˢ`
  satisfies (`foc_actual_flat`): the actual utility does not determine `m̄`, and the expansion
  needs the choice of `m̄` made by `Ũ`. This is the exact extent of the caveat.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedBranch67

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610 TidyR5Distorted67
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-- Woodford (2003), §4.1 (bookkeeping for families): if `P` holds at `x₀` and near `x₀`, and
`q_b → x₀`, there is a family `q′` with `P(q′_b)` for EVERY `b` and `q′ = q` eventually. -/
theorem modify_gen {X : Type*} [TopologicalSpace X] {x0 : X} {P : X → Prop} (h0 : P x0)
    (hev : ∀ᶠ x in 𝓝 x0, P x) {q : B → X} (hT : Tendsto q L (𝓝 x0)) :
    ∃ q' : B → X, (∀ b, P (q' b)) ∧ q' =ᶠ[L] q := by
  classical
  refine ⟨fun b => if P (q b) then q b else x0, fun b => ?_, ?_⟩
  · by_cases hb : P (q b)
    · simp only [hb, ite_true]
    · simp only [hb, ite_false]; exact h0
  · filter_upwards [hT.eventually hev] with b hb
    simp only [hb, ite_true]

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (4.6) and (E.16) (**the Jacobian of the steady-state conditions is
invertible**): if `(σ⁻¹ + ω)y − χm = 0` and `v̄χy − m/η_i = 0` with `η_y = χη_iv̄`,
`Ω_mc ≠ 0`, `η_i ≠ 0`, then `y = m = 0`. -/
theorem psi67_deriv_inj (P : Transactions.TxParams) (hey : P.etaY = P.chi * P.etaI * P.vbar)
    (hΩ : Transactions.omegaMC P ≠ 0) (hi : P.etaI ≠ 0) {y m : ℝ}
    (h1 : (P.sigInv + P.omega) * y - P.chi * m = 0)
    (h2 : P.vbar * P.chi * y - m / P.etaI = 0) : y = 0 ∧ m = 0 := by
  have hm : m = P.etaY * y := by
    rw [hey]; field_simp at h2; linarith
  have hy : Transactions.omegaMC P * y = 0 := by
    simp only [Transactions.omegaMC]; rw [hm] at h1; linarith
  have hy0 : y = 0 := (mul_eq_zero.1 hy).resolve_left hΩ
  exact ⟨hy0, by rw [hm, hy0, mul_zero]⟩

/-- **Woodford (2003), (4.6), p. 421 and (E.15)–(E.16) (the distorted steady states with
transactions frictions exist and are locally unique).** Under the efficient satiated conditions
of `distorted_ss67`, there is `g : ℝ × ℝ → ℝ × ℝ` with `g(0, 0) = (Y*, mˢ)`, `g → (Y*, mˢ)`, and
for all small `(Φ, Δ̄)` the point `(Ȳ, m̄) = g(Φ, Δ̄)` satisfies `v_y(Ȳ) = (1 − Φ)ũ_c(Ȳ, m̄)` and
`ũ_m(Ȳ, m̄) = Δ̄ũ_c(Ȳ, m̄)`; near `(Y*, mˢ)` every such point is `g(Φ, Δ̄)`. -/
theorem branch67 {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {v : ℝ × Ξ → ℝ}
    (hv : ContDiff ℝ 3 v) {Ys ms : ℝ} (hYs : 0 < Ys) (hms : 0 < ms)
    (P : Transactions.TxParams) (hvel : P.vbar * ms = Ys)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0) (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys) :
    ∃ g : ℝ × ℝ → ℝ × ℝ, g 0 = (Ys, ms) ∧ Tendsto g (𝓝 0) (𝓝 (Ys, ms)) ∧
      (∀ᶠ q in 𝓝 0, dY v ((g q).1, 0) = (1 - q.1) * fderiv ℝ Ut ((g q).1, (g q).2, 0) (1, 0, 0)
        ∧ fderiv ℝ Ut ((g q).1, (g q).2, 0) (0, 1, 0) =
          q.2 * fderiv ℝ Ut ((g q).1, (g q).2, 0) (1, 0, 0)) ∧
      ∀ᶠ p in 𝓝 (Ys, ms), ∀ q : ℝ × ℝ,
        dY v (p.1, 0) = (1 - q.1) * fderiv ℝ Ut (p.1, p.2, 0) (1, 0, 0) →
        fderiv ℝ Ut (p.1, p.2, 0) (0, 1, 0) = q.2 * fderiv ℝ Ut (p.1, p.2, 0) (1, 0, 0) →
          g q = p := by
  set p0 : ℝ × ℝ := (Ys, ms) with hp0
  set uY : ℝ × ℝ → ℝ := fun p => fderiv ℝ Ut (p.1, p.2, 0) (1, 0, 0) with huY
  set uM : ℝ × ℝ → ℝ := fun p => fderiv ℝ Ut (p.1, p.2, 0) (0, 1, 0) with huM
  set vY : ℝ × ℝ → ℝ := fun p => dY v (p.1, 0) with hvY
  set Ψ : ℝ × ℝ → ℝ × ℝ := fun p => (1 - vY p * (uY p)⁻¹, uM p * (uY p)⁻¹) with hΨ
  set uc := fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) with huc_def
  -- smoothness
  have hι : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1, p.2, (0 : Ξ)) : ℝ × ℝ × Ξ)) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hF2 : ContDiff ℝ 2 (fderiv ℝ Ut) := hUt.fderiv_right (m := 2) (by norm_num)
  have huYc : ContDiff ℝ 2 uY := (hF2.comp hι).clm_apply contDiff_const
  have huMc : ContDiff ℝ 2 uM := (hF2.comp hι).clm_apply contDiff_const
  have hvYc : ContDiff ℝ 2 vY := (contDiff_dY hv).comp contDiff_fst
  have hΨc : ContDiffAt ℝ 2 Ψ p0 :=
    (contDiffAt_const.sub (hvYc.contDiffAt.mul (huYc.contDiffAt.inv huc))).prodMk
      (huMc.contDiffAt.mul (huYc.contDiffAt.inv huc))
  -- the derivative
  set ιL : ℝ × ℝ →L[ℝ] ℝ × ℝ × Ξ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0) with hιL
  have hιd : HasFDerivAt (fun p : ℝ × ℝ => ((p.1, p.2, (0 : Ξ)) : ℝ × ℝ × Ξ)) ιL p0 :=
    ιL.hasFDerivAt
  set D2 := fderiv ℝ (fderiv ℝ Ut) (Ys, ms, (0 : Ξ)) with hD2
  have hFd : HasFDerivAt (fderiv ℝ Ut) D2 (Ys, ms, (0 : Ξ)) :=
    ((hUt.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hcomp : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ Ut (p.1, p.2, 0)) (D2.comp ιL) p0 :=
    hFd.comp p0 hιd
  have huYd : HasFDerivAt uY ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : Ξ))).comp
      (D2.comp ιL)) p0 := by
    have h := (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : Ξ))).hasFDerivAt.comp p0
      hcomp
    exact h
  have huMd : HasFDerivAt uM ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ), (0 : Ξ))).comp
      (D2.comp ιL)) p0 := by
    have h := (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ), (0 : Ξ))).hasFDerivAt.comp p0
      hcomp
    exact h
  have hvYd : HasFDerivAt vY ((ContinuousLinearMap.toSpanSingleton ℝ (dYY v (Ys, 0))).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) p0 :=
    by
    have h := (hasDerivAt_dY (hv.of_le (by norm_num)) Ys).hasFDerivAt.comp p0
      (hasFDerivAt_fst (p := p0) (𝕜 := ℝ))
    exact h
  have hinvd := (hasFDerivAt_inv (𝕜 := ℝ) huc).comp p0 huYd
  have hΨd := ((hasFDerivAt_const (1 : ℝ) p0).sub (hvYd.mul hinvd)).prodMk (huMd.mul hinvd)
  set D := ((0 : ℝ × ℝ →L[ℝ] ℝ) - (vY p0 • ((ContinuousLinearMap.toSpanSingleton ℝ
      (-(uY p0 ^ 2)⁻¹)).comp ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : Ξ))).comp
        (D2.comp ιL))) + (uY p0)⁻¹ • ((ContinuousLinearMap.toSpanSingleton ℝ
          (dYY v (Ys, 0))).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)))).prod
      (uM p0 • ((ContinuousLinearMap.toSpanSingleton ℝ (-(uY p0 ^ 2)⁻¹)).comp
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : Ξ))).comp (D2.comp ιL))) +
        (uY p0)⁻¹ • ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ), (0 : Ξ))).comp
          (D2.comp ιL))) with hDdef
  have hΨD : HasFDerivAt Ψ D p0 := hΨd
  -- the derivative is injective
  have hinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).2 ?_
    intro ac hac
    obtain ⟨a, c⟩ := ac
    obtain ⟨d1, d2⟩ := ss67_D2 hUt hYs hms P hvel hi hvb h11 h12 h22 a c
    have e := congrArg Prod.fst hac
    have e' := congrArg Prod.snd hac
    simp only [hDdef, ContinuousLinearMap.prod_apply,
      FunLike.coe_sub, FunLike.coe_add, FunLike.coe_smul,
      ContinuousLinearMap.coe_comp, Function.comp_apply, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, Prod.fst_zero,
      Prod.snd_zero, hιL, ContinuousLinearMap.coe_snd', FunLike.coe_zero, Pi.zero_apply] at e e'
    simp only [huY, huM, hvY, hp0] at e e'
    rw [← hD2] at d1 d2
    simp only [← huc_def] at e e' d1 d2
    rw [d1] at e
    rw [d2, hsat] at e'
    rw [hvy, hvyy, hvy] at e
    have k1 : uc ^ 2 * (uc ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 huc)
    have k2 : uc⁻¹ * uc = 1 := inv_mul_cancel₀ huc
    have E1 : (P.sigInv + P.omega) * (a / Ys) - P.chi * (c / ms) = 0 := by
      linear_combination -e - (P.sigInv * (a / Ys) - P.chi * (c / ms)) * k1 -
        (P.omega * (a / Ys)) * k2
    have E2 : P.vbar * P.chi * (a / Ys) - c / ms / P.etaI = 0 := by
      linear_combination e' - (P.vbar * P.chi * (a / Ys) - c / ms / P.etaI) * k2
    obtain ⟨y0, m0⟩ := psi67_deriv_inj P hey hΩ hi E1 E2
    have ha : a = 0 := by
      have := div_eq_zero_iff.1 y0; exact this.resolve_right hYs.ne'
    have hc : c = 0 := by
      have := div_eq_zero_iff.1 m0; exact this.resolve_right hms.ne'
    rw [ha, hc]; rfl
  set E := (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv with hE
  have hED : (E : ℝ × ℝ →L[ℝ] ℝ × ℝ) = D := by
    ext <;> rfl
  have hs : HasStrictFDerivAt Ψ (E : ℝ × ℝ →L[ℝ] ℝ × ℝ) p0 := by
    rw [hED]; exact hΨc.hasStrictFDerivAt' hΨD (by norm_num)
  have hΨ0 : Ψ p0 = 0 := by
    simp only [hΨ, huY, huM, hvY, hp0, hvy, hsat, zero_mul]
    rw [mul_inv_cancel₀ huc, sub_self]; rfl
  set g := hs.localInverse Ψ E p0 with hg
  have hT : Tendsto g (𝓝 (Ψ p0)) (𝓝 p0) := hs.localInverse_tendsto
  rw [hΨ0] at hT
  have hg0 : g 0 = p0 := by
    have := hs.localInverse_apply_image
    rw [hΨ0] at this
    exact this
  have hR : ∀ᶠ q in 𝓝 (Ψ p0), Ψ (g q) = q := hs.eventually_right_inverse
  rw [hΨ0] at hR
  have hkne : ∀ᶠ p in 𝓝 p0, uY p ≠ 0 := huYc.continuous.continuousAt.eventually_ne huc
  refine ⟨g, hg0, hT, ?_, ?_⟩
  · filter_upwards [hR, hT.eventually hkne] with q h1 h2
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    simp only [hΨ, huY, huM, hvY] at e1 e2 h2
    refine ⟨?_, ?_⟩
    · field_simp at e1; linear_combination -e1
    · field_simp at e2; linear_combination e2
  · filter_upwards [hs.eventually_left_inverse, hkne] with p h1 h2 q hq1 hq2
    have : Ψ p = q := by
      simp only [hΨ, huY, huM, hvY] at h2 ⊢
      ext
      · simp only; rw [hq1]; field_simp; ring
      · simp only; rw [hq2]; field_simp
    rw [← this]
    exact h1

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, around the CONSTRUCTED distorted steady
state.** Let `g₀` be a branch of distorted steady states (as given by `branch67`). Along any
family with `Φ_b, d̄_b = O(ε)`, with `(Ȳ_b, m̄_b) = g₀(Φ_b, 1 − e^{−d̄_b})`, the conclusion of
`prop67_distorted` holds; no steady-state hypothesis on the family remains. -/
theorem prop67_on_branch (hs : Tendsto s L (𝓝 0)) {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys : ℝ} (hYs : 0 < Ys)
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹) (hvel : P.vbar * ms = Ys)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0) (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    {g0 : ℝ × ℝ → ℝ × ℝ} (hg0 : g0 0 = (Ys, ms)) (hgT : Tendsto g0 (𝓝 0) (𝓝 (Ys, ms)))
    (hgS : ∀ᶠ q in 𝓝 0, dY v ((g0 q).1, 0) =
        (1 - q.1) * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0) ∧
      fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (0, 1, 0) =
        q.2 * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0))
    {Phi dbar : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hdbar : dbar =O[L] fun b => s b ^ 1)
    {yd : B → ι → ℝ} {md d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hmd : md =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => md b - (P.etaY * logYidx w θ (yd b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log ((g0 (Phi b, 1 - Real.exp (-dbar b))).2 / ms) ≤ 0) :
    (fun b => periodUT U v w θ ((g0 (Phi b, 1 - Real.exp (-dbar b))).1)
        ((g0 (Phi b, 1 - Real.exp (-dbar b))).2) (yd b) (md b) (xu b) (xv b) -
      (tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txDist P (logYidx w θ (yd b)) (d b) (g b) (q b) (eps b) (Phi b)
            (1 - Real.exp (-dbar b)) (crossVar w (yd b)) (md b)) / 2))) =O[L]
      fun b => s b ^ 3 := by
  set m : ℝ × ℝ → ℝ × ℝ := fun x => (x.1, 1 - Real.exp (-x.2)) with hm
  have hm0 : m 0 = 0 := by
    simp only [hm, Prod.fst_zero, Prod.snd_zero, neg_zero, Real.exp_zero, sub_self]; rfl
  have hmT : Tendsto m (𝓝 0) (𝓝 0) := by
    have hc : Continuous m := continuous_fst.prodMk (continuous_const.sub
      (Real.continuous_exp.comp continuous_snd.neg))
    have := hc.tendsto 0
    rwa [hm0] at this
  set Pr : ℝ × ℝ → Prop := fun x => 0 < (g0 (m x)).1 ∧ 0 < (g0 (m x)).2 ∧
    dY v ((g0 (m x)).1, 0) = (1 - (m x).1) * fderiv ℝ Ut ((g0 (m x)).1, (g0 (m x)).2, 0)
      (1, 0, 0) ∧ fderiv ℝ Ut ((g0 (m x)).1, (g0 (m x)).2, 0) (0, 1, 0) =
        (m x).2 * fderiv ℝ Ut ((g0 (m x)).1, (g0 (m x)).2, 0) (1, 0, 0) with hPr
  have hP0 : Pr 0 := by
    simp only [hPr, hm0, hg0, Prod.fst_zero, Prod.snd_zero, sub_zero, one_mul, zero_mul, hvy,
      hsat]
    exact ⟨hYs, hms, trivial, trivial⟩
  have hpos : ∀ᶠ p in 𝓝 ((Ys, ms) : ℝ × ℝ), 0 < p.1 ∧ 0 < p.2 :=
    (continuous_fst.tendsto _ |>.eventually (lt_mem_nhds hYs)).and
      (continuous_snd.tendsto _ |>.eventually (lt_mem_nhds hms))
  have hPev : ∀ᶠ x in 𝓝 0, Pr x := by
    filter_upwards [hmT.eventually hgS, hmT.eventually (hgT.eventually hpos)] with x h1 h2
    exact ⟨h2.1, h2.2, h1.1, h1.2⟩
  obtain ⟨q', hq', hqe⟩ := modify_gen hP0 hPev
    ((tendsto_of_o_one hs hPhi).prodMk_nhds (tendsto_of_o_one hs hdbar) |>.congr' (by rfl))
  have h1 : (fun b => (q' b).1) =ᶠ[L] Phi := hqe.mono fun b hb => by
    change (q' b).1 = Phi b; rw [hb]
  have h2 : (fun b => (q' b).2) =ᶠ[L] dbar := hqe.mono fun b hb => by
    change (q' b).2 = dbar b; rw [hb]
  have hPhi' : (fun b => (q' b).1) =O[L] fun b => s b ^ 1 := hPhi.congr' h1.symm EventuallyEq.rfl
  have hdbar' : (fun b => (q' b).2) =O[L] fun b => s b ^ 1 :=
    hdbar.congr' h2.symm EventuallyEq.rfl
  have hq'T : Tendsto q' L (𝓝 0) := by
    have := (tendsto_of_o_one hs hPhi').prodMk_nhds (tendsto_of_o_one hs hdbar')
    exact this
  have hGT : Tendsto (fun b => g0 (m (q' b))) L (𝓝 (Ys, ms)) := hgT.comp (hmT.comp hq'T)
  have hleft' : ∀ᶠ b in L, md b + Real.log ((g0 (m (q' b))).2 / ms) ≤ 0 := by
    filter_upwards [hleft, hqe] with b hb hb'
    simp only [hm, hb']
    exact hb
  have h := prop67_distorted hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy (Yb := fun b => (g0 (m (q' b))).1)
    (mb := fun b => (g0 (m (q' b))).2) (fun b => (hq' b).1) (fun b => (hq' b).2.1)
    ((continuous_fst.tendsto _).comp hGT) ((continuous_snd.tendsto _).comp hGT) hPhi' hdbar'
    (fun b => (hq' b).2.2.1)
    (fun b => (hq' b).2.2.2) hg heps hq hyd hmd hd hgO hqO hepsO hxu hxv hr hleft'
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hqe] with b hb
  simp only [hm, hb]

/-- Woodford (2003), Assumption 6.1, p. 422 and (E.16) (**an actual steady state with `Δ̄ ≠ 0` lies
strictly below satiation**): if `U = Ũ` for `m ≤ mˢ` and `u_m = 0` at and above satiation (the
Fréchet derivative of `U` in the `m` direction vanishes for `m ≥ mˢ`; Assumption 6.1), then at a
point where `u_m = Δ̄u_c` with `Δ̄ ≠ 0` and `u_c ≠ 0`, `m < mˢ` and the derivative of `U` is that of
`Ũ`. -/
theorem foc_actual {U Ut : ℝ × ℝ × Ξ → ℝ} {ms : ℝ} (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
    (hUm : ∀ z : ℝ × ℝ × Ξ, ms ≤ z.2.1 → fderiv ℝ U z (0, 1, 0) = 0) {Y m Δ : ℝ}
    (hΔ : Δ ≠ 0) (hc : fderiv ℝ U (Y, m, 0) (1, 0, 0) ≠ 0)
    (h2 : fderiv ℝ U (Y, m, 0) (0, 1, 0) = Δ * fderiv ℝ U (Y, m, 0) (1, 0, 0)) :
    m < ms ∧ fderiv ℝ U (Y, m, 0) = fderiv ℝ Ut (Y, m, 0) := by
  have hlt : m < ms := by
    by_contra hge
    have h0 := hUm (Y, m, 0) (not_lt.1 hge)
    rw [h0] at h2
    exact mul_ne_zero hΔ hc h2.symm
  refine ⟨hlt, ?_⟩
  have hU : U =ᶠ[𝓝 ((Y, m, 0) : ℝ × ℝ × Ξ)] Ut :=
    Filter.eventuallyEq_of_mem ((isOpen_lt (continuous_fst.comp continuous_snd)
      continuous_const).mem_nhds hlt) fun z hz => hEq (show z.2.1 ≤ ms from le_of_lt hz)
  exact hU.fderiv_eq

/-- Woodford (2003), Assumption 6.1 (**why `Δ̄ = 0` is different**): under the flatness of
`foc_actual`, every `m ≥ mˢ` satisfies the money condition `u_m = 0·u_c` of the actual utility,
so with `Δ̄ = 0` the actual steady-state conditions do not determine `m̄`. -/
theorem foc_actual_flat {U : ℝ × ℝ × Ξ → ℝ} {ms : ℝ}
    (hUm : ∀ z : ℝ × ℝ × Ξ, ms ≤ z.2.1 → fderiv ℝ U z (0, 1, 0) = 0) (Y m : ℝ) (hm : ms ≤ m) :
    fderiv ℝ U (Y, m, 0) (0, 1, 0) = 0 * fderiv ℝ U (Y, m, 0) (1, 0, 0) := by
  rw [zero_mul]; exact hUm (Y, m, 0) hm

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, with the steady-state conditions of the
ACTUAL utility.** As `prop67_distorted`, but the distorted steady state solves the conditions
of `U` itself (`v_y = (1 − Φ)u_c`, `u_m = Δ̄u_c`), `U` is flat in `m` at and above satiation
(Assumption 6.1), `d̄_b ≠ 0` (so `Δ̄_b ≠ 0`) and `u_c ≠ 0` there: by `foc_actual` the steady
state lies below satiation and its conditions are those of `Ũ`. -/
theorem prop67_actual_distorted (hs : Tendsto s L (𝓝 0)) {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys : ℝ} (hYs : 0 < Ys)
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹) (hvel : P.vbar * ms = Ys)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0) (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    (hUm : ∀ z : ℝ × ℝ × Ξ, ms ≤ z.2.1 → fderiv ℝ U z (0, 1, 0) = 0)
    {Yb mb Phi dbar : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hmb0 : ∀ b, 0 < mb b)
    (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hdbar : dbar =O[L] fun b => s b ^ 1)
    (hd0 : ∀ b, dbar b ≠ 0) (hUc : ∀ b, fderiv ℝ U (Yb b, mb b, 0) (1, 0, 0) ≠ 0)
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ U (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ U (Yb b, mb b, 0) (0, 1, 0) =
      (1 - Real.exp (-dbar b)) * fderiv ℝ U (Yb b, mb b, 0) (1, 0, 0))
    {yd : B → ι → ℝ} {md d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hmd : md =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => md b - (P.etaY * logYidx w θ (yd b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log (mb b / ms) ≤ 0) :
    (fun b => periodUT U v w θ (Yb b) (mb b) (yd b) (md b) (xu b) (xv b) -
      (tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txDist P (logYidx w θ (yd b)) (d b) (g b) (q b) (eps b) (Phi b)
            (1 - Real.exp (-dbar b)) (crossVar w (yd b)) (md b)) / 2))) =O[L]
      fun b => s b ^ 3 := by
  have hΔ : ∀ b, 1 - Real.exp (-dbar b) ≠ 0 := fun b h => by
    have : Real.exp (-dbar b) = 1 := by linarith
    rw [Real.exp_eq_one_iff, neg_eq_zero] at this
    exact hd0 b this
  have hfd : ∀ b, fderiv ℝ U (Yb b, mb b, 0) = fderiv ℝ Ut (Yb b, mb b, 0) := fun b =>
    (foc_actual hEq hUm (hΔ b) (hUc b) (hF2 b)).2
  exact prop67_distorted hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy hYb0 hmb0 hYb hmb hPhi hdbar (fun b => by rw [← hfd b]; exact hF1 b)
    (fun b => by rw [← hfd b]; exact hF2 b) hg heps hq hyd hmd hd hgO hqO hepsO hxu hxv hr hleft

end Woodford.StabilizationWelfare.TidyR5DistortedBranch67
