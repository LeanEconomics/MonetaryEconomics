/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5Distorted610
import StabilizationWelfare.BridgeLinks

/-!
# Proposition 6.7 expanded around the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1, Proposition 6.7, (4.9), p. 422, with
`x* = (Φ_y + s_mη_y)/Ω_mc`, (4.6), p. 421, `s_m = Δ̄/v̄`, and Appendix E.4, (E.15)–(E.18),
pp. 699–700.

`BridgeExtensions.prop67_actual` expands the actual utility with transactions frictions around
the EFFICIENT SATIATED steady state `(Y*, mˢ)` (`Φ_y = Δ̄ = 0`). The book's (4.9) is an
expansion around the DISTORTED steady state `(Ȳ, m̄)`, where the output distortion `Φ_y` and
the steady-state interest differential `Δ̄ = (ī − īᵐ)/(1 + ī)` are both nonzero (so `m̄ < mˢ`).
Here both distortions are small (`O(ε)`), which is what a second-order expansion requires.

* **`distorted_ss67`**: the two-equation distorted steady state
  `v_y(Ȳ) = (1 − Φ)u_c(Ȳ, m̄)`, `u_m(Ȳ, m̄) = Δ̄u_c(Ȳ, m̄)` (`Δ̄ = 1 − e^{−d̄}`), along a branch
  converging to `(Y*, mˢ)`: `log(Ȳ/Y*) = −x* + O(ε²)` and
  `log(m̄/mˢ) = η_y log(Ȳ/Y*) − η_i d̄ + O(ε²)` (the steady-state money demand). The first-order
  bound `log(Ȳ/Y*), log(m̄/mˢ) = O(ε)` is part of the proof (the Jacobian has determinant
  `−Ω_mc/η_i ≠ 0`).
* `periodUT_shift`: the actual utility is the same function of the actual outputs and balances.
* `txDist`, `loss49_txDist`: the point of `Transactions.prop_6_7_layerA` at the distorted
  steady state, and its loss written at the satiated point.
* **`prop67_distorted`**, **`prop67_distorted_layerB`**: Proposition 6.7 around the distorted
  steady state, with the loss (4.9) `Ω_mc(Ŷ − Ŷⁿ − x*)² + v̄⁻¹η_i(î − îᵐ + Δ̄)² + (θ⁻¹ + ω)var`.
-/

namespace Woodford.StabilizationWelfare.TidyR5Distorted67

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}
variable {Ξ : Type*}
variable {ι : Type*} [Fintype ι]

/-! ## The distorted point of Proposition 6.7 -/

/-- Woodford (2003), (4.9) and App. E.4: the point of `Transactions.prop_6_7_layerA` at the
DISTORTED steady state, with output distortion `Φ_y`, steady-state interest differential `Δ̄`,
and the money-demand residual `r` of (4.1) (`e₂ = e₃ = 0`). -/
def txDist (P : Transactions.TxParams) (Y d g q eps Phi Delta V m : ℝ) : Transactions.TxPoint :=
  ⟨Y, d, g, q, eps, Phi, Delta, V, m - (P.etaY * Y - P.etaI * d + eps), 0, 0⟩

/-- Woodford (2003), (4.9), p. 422: the loss at the distorted point is the loss at the satiated
point of the shifted variables `Ŷ − x*` and `(î − îᵐ) + Δ̄`. -/
theorem loss49_txDist (P : Transactions.TxParams) (Y d g q eps Phi Delta V m m' : ℝ) :
    Transactions.loss49 P (txDist P Y d g q eps Phi Delta V m) =
      Transactions.loss49 P (txSat P (Y - Transactions.xStar P Phi Delta) (d + Delta) g q eps
        V m') := by
  simp only [Transactions.loss49, txDist, txSat, Transactions.xStar, Transactions.sM, zero_div,
    zero_mul, add_zero]
  ring

/-- Woodford (2003), §4.1, (4.1)–(4.2), p. 420 (**the actual utility does not depend on the
reference point**): the period utility with outputs `Ȳe^{ŷ(i)}` and balances `m̄e^{m̂}` equals
the one with reference `(Y*, mˢ)` and log deviations `ŷ(i) + log(Ȳ/Y*)`, `m̂ + log(m̄/mˢ)`. -/
theorem periodUT_shift {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ : θ ≠ 1) (U : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) {Ys ms Yb mb : ℝ} (hYs : 0 < Ys)
    (hms : 0 < ms) (hYb : 0 < Yb) (hmb : 0 < mb) (yd : ι → ℝ) (md : ℝ) (xu xv : Ξ) :
    periodUT U v w θ Ys ms (fun i => yd i + Real.log (Yb / Ys)) (md + Real.log (mb / ms)) xu xv =
      periodUT U v w θ Yb mb yd md xu xv := by
  have hy : ∀ (Y Y' x : ℝ), 0 < Y → 0 < Y' → Y * Real.exp (x + Real.log (Y' / Y)) =
      Y' * Real.exp x := fun Y Y' x hY hY' => by
    rw [Real.exp_add, Real.exp_log (div_pos hY' hY)]
    field_simp
  unfold periodUT
  rw [logYidx_shift hw0 hw1 hθ, hy _ _ _ hYs hYb, hy _ _ _ hms hmb]
  simp only [hy _ _ _ hYs hYb]

/-! ## The distorted steady state -/

/-- Woodford (2003), (E.15)–(E.16), p. 699: the remainder `ρ₁` of the linearised output
condition of the distorted steady state, `−Φ G + ((1 − Φ)o₁ − o_v)/u_c` with
`G = −σ⁻¹y + χm` the first-order change of `u_c/u_c(Y*, mˢ)`. -/
noncomputable def ssRho1 (P : Transactions.TxParams) (uc y m Phi o1 oV : ℝ) : ℝ :=
  -(Phi * (-P.sigInv * y + P.chi * m)) + ((1 - Phi) * o1 - oV) * uc⁻¹

/-- Woodford (2003), (E.16), p. 700: the remainder `ρ₂` of the linearised money-demand
condition of the distorted steady state, `Δ̄G + (Δ̄o₁ − o₂)/u_c`. -/
noncomputable def ssRho2 (P : Transactions.TxParams) (uc y m Δ o1 o2 : ℝ) : ℝ :=
  Δ * (-P.sigInv * y + P.chi * m) + (Δ * o1 - o2) * uc⁻¹

/-- Woodford (2003), (4.6), p. 421 and (E.16) (**solving the linearised steady state**): if
`y = Ȳ/Y* − 1`, `m = m̄/mˢ − 1` satisfy the two steady-state conditions written with their
remainders `o₁, o₂, o_v` (`v_y = (1 − Φ)u_c`, `u_m = Δ̄u_c`), then
`y = (−Φ − χη_iΔ̄ + ρ₁ − χη_iρ₂)/Ω_mc` and `m = η_yy − η_iΔ̄ − η_iρ₂`. -/
theorem ss67_algebra (P : Transactions.TxParams) (hey : P.etaY = P.chi * P.etaI * P.vbar)
    (hΩ : Transactions.omegaMC P ≠ 0) (hi : P.etaI ≠ 0) {uc y m Phi Δ o1 o2 oV : ℝ}
    (huc : uc ≠ 0)
    (E1 : uc + uc * P.omega * y + oV =
      (1 - Phi) * (uc + uc * (-P.sigInv * y + P.chi * m) + o1))
    (E2 : uc * (P.vbar * P.chi * y - m / P.etaI) + o2 =
      Δ * (uc + uc * (-P.sigInv * y + P.chi * m) + o1)) :
    y = (-Phi - P.chi * P.etaI * Δ + (ssRho1 P uc y m Phi o1 oV -
      P.chi * P.etaI * ssRho2 P uc y m Δ o1 o2)) / Transactions.omegaMC P ∧
      m = P.etaY * y - P.etaI * Δ - P.etaI * ssRho2 P uc y m Δ o1 o2 := by
  have hinv : uc⁻¹ * uc = 1 := inv_mul_cancel₀ huc
  have I1 : (P.sigInv + P.omega) * y - P.chi * m = -Phi + ssRho1 P uc y m Phi o1 oV := by
    simp only [ssRho1]
    linear_combination uc⁻¹ * E1 - ((P.sigInv + P.omega) * y - P.chi * m + Phi +
      Phi * (-P.sigInv * y + P.chi * m)) * hinv
  have I2 : P.vbar * P.chi * y - m / P.etaI = Δ + ssRho2 P uc y m Δ o1 o2 := by
    simp only [ssRho2]
    linear_combination uc⁻¹ * E2 - (P.vbar * P.chi * y - m / P.etaI - Δ -
      Δ * (-P.sigInv * y + P.chi * m)) * hinv
  have I2' : m = P.etaI * (P.vbar * P.chi * y) - P.etaI * (Δ + ssRho2 P uc y m Δ o1 o2) := by
    rw [← I2]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hΩ]
    simp only [Transactions.omegaMC, hey]
    linear_combination I1 + P.chi * I2'
  · rw [hey]
    linear_combination I2'

variable [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.15), p. 699: the second derivatives of `Ũ` at the satiated point,
applied to a level deviation `(a, c, 0)`: `D²Ũ((a, c, 0), e₁) = u_c(−σ⁻¹a/Y* + χc/mˢ)` and
`D²Ũ((a, c, 0), e₂) = u_c(v̄χa/Y* − (c/mˢ)/η_i)` (with `v̄ = Y*/mˢ`). -/
theorem ss67_D2 {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {Ys ms : ℝ} (hYs : 0 < Ys)
    (hms : 0 < ms) (P : Transactions.TxParams) (hvel : P.vbar * ms = Ys) (hi : P.etaI ≠ 0)
    (hvb : P.vbar ≠ 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2)) (a c : ℝ) :
    fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (a, c, 0) (1, 0, 0) =
        fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * (-P.sigInv * (a / Ys) + P.chi * (c / ms)) ∧
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (a, c, 0) (0, 1, 0) =
        fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * (P.vbar * P.chi * (a / Ys) - c / ms / P.etaI) := by
  set D2 := fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) with hD2
  set uc := fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) with huc
  have hsym : IsSymmSndFDerivAt ℝ Ut (Ys, ms, 0) :=
    (hUt.contDiffAt (x := (Ys, ms, 0))).isSymmSndFDerivAt (by simp; norm_num)
  have h12' : D2 (1, 0, 0) (0, 1, 0) = P.chi * uc / ms := by
    have := hsym (1, 0, 0) (0, 1, 0)
    linarith [h12]
  have h21' : D2 (0, 1, 0) (1, 0, 0) = P.chi * uc / ms := by
    have := hsym (1, 0, 0) (0, 1, 0)
    linarith [h12]
  have hsplit : ((a, c, 0) : ℝ × ℝ × Ξ) = a • ((1 : ℝ), (0 : ℝ), (0 : Ξ)) +
      c • ((0 : ℝ), (1 : ℝ), (0 : Ξ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [h11, h21', h12', h22]
  refine ⟨by field_simp, ?_⟩
  rw [← hvel]
  field_simp
  ring

/-- Woodford (2003), (4.6), p. 421 (**the distorted steady state is first order**): under the
hypotheses of `distorted_ss67`, `Ȳ_b − Y* = O(ε)` and `m̄_b − mˢ = O(ε)`. The Jacobian of the
two steady-state conditions has determinant `−Ω_mc/η_i ≠ 0`, so the remainders `o(‖Ȳ − Y*‖ +
‖m̄ − mˢ‖)` are absorbed. -/
theorem distorted_ss67_first (hs : Tendsto s L (𝓝 0)) {Ut : ℝ × ℝ × Ξ → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys ms : ℝ} (hYs : 0 < Ys)
    (hms : 0 < ms) (P : Transactions.TxParams) (hvel : P.vbar * ms = Ys)
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
    {Yb mb Phi Δ : B → ℝ} (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hΔ : Δ =O[L] fun b => s b ^ 1)
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ Ut (Yb b, mb b, 0) (0, 1, 0) =
      Δ b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0)) :
    (fun b => Yb b - Ys) =O[L] (fun b => s b ^ 1) ∧
      (fun b => mb b - ms) =O[L] fun b => s b ^ 1 := by
  set z0 : ℝ × ℝ × Ξ := (Ys, ms, 0) with hz0
  set uc := fderiv ℝ Ut z0 (1, 0, 0) with huc_def
  set D2 := fderiv ℝ (fderiv ℝ Ut) z0 with hD2
  set h : B → ℝ × ℝ × Ξ := fun b => (Yb b - Ys, mb b - ms, 0) with hh
  have hpt : ∀ b, z0 + h b = (Yb b, mb b, 0) := fun b => by
    simp only [hz0, hh, Prod.mk_add_mk, add_zero, add_sub_cancel]
  set o1 := fun b => fderiv ℝ Ut (z0 + h b) (1, 0, 0) - uc - D2 (h b) (1, 0, 0) with ho1
  set o2 := fun b => fderiv ℝ Ut (z0 + h b) (0, 1, 0) - 0 - D2 (h b) (0, 1, 0) with ho2
  set oV := fun b => dY v (Yb b, 0) - dY v (Ys, 0) - (Yb b - Ys) * dYY v (Ys, 0) with hoV
  set y := fun b => (Yb b - Ys) / Ys with hy
  set m' := fun b => (mb b - ms) / ms with hm'
  have sol : ∀ b, y b = (-Phi b - P.chi * P.etaI * Δ b + (ssRho1 P uc (y b) (m' b) (Phi b)
      (o1 b) (oV b) - P.chi * P.etaI * ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b))) /
        Transactions.omegaMC P ∧ m' b = P.etaY * y b - P.etaI * Δ b -
          P.etaI * ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b) := fun b => by
    obtain ⟨d1, d2⟩ := ss67_D2 hUt hYs hms P hvel hi hvb h11 h12 h22 (Yb b - Ys) (mb b - ms)
    refine ss67_algebra P hey hΩ hi huc ?_ ?_
    · have e := hF1 b
      rw [← hpt b] at e
      have eo : fderiv ℝ Ut (z0 + h b) (1, 0, 0) = uc + D2 (h b) (1, 0, 0) + o1 b := by
        simp only [ho1]; ring
      have ev : dY v (Yb b, 0) = uc + uc * P.omega * y b + oV b := by
        simp only [hoV, hvyy, hvy, hy]; ring
      rw [eo, ev] at e
      rw [e]
      change (1 - Phi b) * (uc + D2 (Yb b - Ys, mb b - ms, 0) (1, 0, 0) + o1 b) = _
      rw [d1]
    · have e := hF2 b
      rw [← hpt b] at e
      have eo1 : fderiv ℝ Ut (z0 + h b) (1, 0, 0) = uc + D2 (h b) (1, 0, 0) + o1 b := by
        simp only [ho1]; ring
      have eo2 : fderiv ℝ Ut (z0 + h b) (0, 1, 0) = D2 (h b) (0, 1, 0) + o2 b := by
        simp only [ho2]; ring
      rw [eo1, eo2] at e
      change D2 (Yb b - Ys, mb b - ms, 0) (0, 1, 0) + o2 b =
        Δ b * (uc + D2 (Yb b - Ys, mb b - ms, 0) (1, 0, 0) + o1 b) at e
      rw [d1, d2] at e
      exact e
  -- little-o remainders
  have hF : HasFDerivAt (fderiv ℝ Ut) D2 z0 :=
    (((hUt.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) z0).hasFDerivAt
  have hh0 : Tendsto h L (𝓝 0) := by
    have := (hYb.sub_const Ys).prodMk_nhds ((hmb.sub_const ms).prodMk_nhds
      (tendsto_const_nhds (x := (0 : Ξ))))
    have e : Tendsto h L (𝓝 ((0 : ℝ), (0 : ℝ), (0 : Ξ))) := by simpa [hh] using this
    exact e
  have hz : Tendsto (fun b => z0 + h b) L (𝓝 z0) := by
    simpa using (tendsto_const_nhds (x := z0)).add hh0
  have lo : (fun b => fderiv ℝ Ut (z0 + h b) - fderiv ℝ Ut z0 - D2 (h b)) =o[L] h :=
    (hF.isLittleO.comp_tendsto hz).congr (fun b => by simp) (fun b => by simp)
  have ev : ∀ w : ℝ × ℝ × Ξ, (fun b => fderiv ℝ Ut (z0 + h b) w - fderiv ℝ Ut z0 w -
      D2 (h b) w) =o[L] h := fun w =>
    (((ContinuousLinearMap.apply ℝ ℝ w).isBigO_comp _ _).trans_isLittleO lo).congr_left
      fun b => by simp
  set q := fun b => |Yb b - Ys| + |mb b - ms| with hq
  have hq0 : ∀ b, 0 ≤ q b := fun b => by simp only [hq]; positivity
  have hhq : h =O[L] q := IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    simp only [hh, one_mul, Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_of_nonneg (hq0 b)]
    refine max_le (by simp only [hq]; linarith [abs_nonneg (mb b - ms)]) (max_le (by
      simp only [hq]; linarith [abs_nonneg (Yb b - Ys)]) (hq0 b)))
  have haq : (fun b => Yb b - Ys) =O[L] q := IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 b)]
    simp only [hq]; linarith [abs_nonneg (mb b - ms)])
  have hcq : (fun b => mb b - ms) =O[L] q := IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 b)]
    simp only [hq]; linarith [abs_nonneg (Yb b - Ys)])
  have ho1q : o1 =o[L] q := ((ev (1, 0, 0)).trans_isBigO hhq).congr_left fun b => by
    simp only [ho1, huc_def]
  have ho2q : o2 =o[L] q := ((ev (0, 1, 0)).trans_isBigO hhq).congr_left fun b => by
    simp only [ho2, hsat]
  have hV : HasDerivAt (fun y => dY v (y, 0)) (dYY v (Ys, 0)) Ys :=
    hasDerivAt_dY (hv.of_le (by norm_num)) Ys
  have hoVq : oV =o[L] q :=
    ((hV.isLittleO.comp_tendsto hYb).trans_isBigO haq).congr_left fun b => by
      simp only [hoV, Function.comp_apply, smul_eq_mul]
  have hyq : y =O[L] q := (haq.const_mul_left Ys⁻¹).congr_left fun b => by
    simp only [hy]; ring
  have hmq : m' =O[L] q := (hcq.const_mul_left ms⁻¹).congr_left fun b => by
    simp only [hm']; ring
  have hGq : (fun b => -P.sigInv * y b + P.chi * m' b) =O[L] q :=
    (hyq.const_mul_left (-P.sigInv)).add (hmq.const_mul_left P.chi)
  have hPhi0 : Phi =o[L] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 (tendsto_of_o_one hs hPhi)
  have hΔ0 : Δ =o[L] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 (tendsto_of_o_one hs hΔ)
  have h1Phi : (fun b => 1 - Phi b) =O[L] (fun _ => (1 : ℝ)) :=
    (isBigO_const_const (1 : ℝ) one_ne_zero L).sub hPhi0.isBigO
  have hρ1q : (fun b => ssRho1 P uc (y b) (m' b) (Phi b) (o1 b) (oV b)) =o[L] q :=
    ((hPhi0.mul_isBigO hGq).neg_left.add (((h1Phi.mul_isLittleO ho1q).sub
      ((isBigO_const_const (1 : ℝ) one_ne_zero L).mul_isLittleO hoVq)).const_mul_left
        uc⁻¹)).congr (fun b => by simp only [ssRho1]; ring) (fun b => by ring)
  have hρ2q : (fun b => ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b)) =o[L] q :=
    ((hΔ0.mul_isBigO hGq).add (((hΔ0.isBigO.mul_isLittleO ho1q).sub
      ((isBigO_const_const (1 : ℝ) one_ne_zero L).mul_isLittleO ho2q)).const_mul_left
        uc⁻¹)).congr (fun b => by simp only [ssRho2]; ring) (fun b => by ring)
  -- the first-order bound `q = O(ε)`
  set Ω := Transactions.omegaMC P with hΩd
  set A1 := fun b => Ys * ((-Phi b - P.chi * P.etaI * Δ b) / Ω) with hA1
  set A2 := fun b => ms * (P.etaY * ((-Phi b - P.chi * P.etaI * Δ b) / Ω) - P.etaI * Δ b)
    with hA2
  have hA1O : A1 =O[L] fun b => s b ^ 1 :=
    ((hPhi.neg_left.sub (hΔ.const_mul_left (P.chi * P.etaI))).const_mul_left
      (Ys / Ω)).congr_left fun b => by simp only [hA1]; ring
  have hA2O : A2 =O[L] fun b => s b ^ 1 :=
    (((hPhi.neg_left.sub (hΔ.const_mul_left (P.chi * P.etaI))).const_mul_left
      (ms * P.etaY / Ω)).sub (hΔ.const_mul_left (ms * P.etaI))).congr_left
        fun b => by simp only [hA2]; ring
  set k1 := fun b => Yb b - Ys - A1 b with hk1
  set k2 := fun b => mb b - ms - A2 b with hk2
  have hk1q : k1 =o[L] q := by
    refine ((hρ1q.sub (hρ2q.const_mul_left (P.chi * P.etaI))).const_mul_left
      (Ys / Ω)).congr_left fun b => ?_
    have hYy : Yb b - Ys = Ys * y b := by simp only [hy]; field_simp
    simp only [hk1, hA1]
    rw [hYy]
    linear_combination (-Ys) * (sol b).1
  have hk2q : k2 =o[L] q := by
    refine (((hρ1q.sub (hρ2q.const_mul_left (P.chi * P.etaI))).const_mul_left
      (ms * P.etaY / Ω)).sub (hρ2q.const_mul_left (ms * P.etaI))).congr_left fun b => ?_
    have hmm : mb b - ms = ms * m' b := by simp only [hm']; field_simp
    simp only [hk2, hA2]
    rw [hmm]
    linear_combination (-(ms * P.etaY)) * (sol b).1 - ms * (sol b).2
  have hkq : (fun b => |k1 b| + |k2 b|) =o[L] q :=
    (hk1q.norm_left.add hk2q.norm_left).congr_left fun b => by simp [Real.norm_eq_abs]
  have hqO : q =O[L] fun b => s b ^ 1 := by
    obtain ⟨C1, hC1⟩ := hA1O.bound
    obtain ⟨C2, hC2⟩ := hA2O.bound
    refine IsBigO.of_bound (2 * (C1 + C2)) ?_
    filter_upwards [hC1, hC2, hkq.bound (by norm_num : (0 : ℝ) < 1 / 2)] with b b1 b2 b3
    simp only [Real.norm_eq_abs] at b1 b2 b3 ⊢
    rw [abs_of_nonneg (hq0 b)] at b3 ⊢
    rw [abs_of_nonneg (by positivity : 0 ≤ |k1 b| + |k2 b|)] at b3
    have t1 : |Yb b - Ys| ≤ |A1 b| + |k1 b| := by
      rw [show Yb b - Ys = A1 b + k1 b by simp only [hk1]; ring]; exact abs_add_le _ _
    have t2 : |mb b - ms| ≤ |A2 b| + |k2 b| := by
      rw [show mb b - ms = A2 b + k2 b by simp only [hk2]; ring]; exact abs_add_le _ _
    have : q b ≤ 2 * (|A1 b| + |A2 b|) := by simp only [hq] at b3 ⊢; linarith
    nlinarith [abs_nonneg (s b ^ 1)]
  exact ⟨haq.trans hqO, hcq.trans hqO⟩

/-- **Woodford (2003), (4.6), p. 421, (E.15)–(E.16), pp. 699–700 (the distorted steady state
with transactions frictions).** At the efficient satiated steady state `(Y*, mˢ, 0)` of the
`C³` utility `Ũ` (`u_m = 0`, the coefficients `σ⁻¹`, `χ`, `(η_iv̄)⁻¹`, `ω` as in
`BridgeExtensions.prop67_actual`, velocity `v̄ = Y*/mˢ`, `η_y = χη_iv̄`), let `(Ȳ_b, m̄_b)`
converge to `(Y*, mˢ)` and satisfy the steady-state conditions `v_y(Ȳ) = (1 − Φ_b)u_c(Ȳ, m̄)`
and `u_m(Ȳ, m̄) = Δ̄_bu_c(Ȳ, m̄)`, `Δ̄_b = 1 − e^{−d̄_b}`, with `Φ_b, d̄_b = O(ε)`. Then
`log(Ȳ_b/Y*)`, `log(m̄_b/mˢ)` are `O(ε)` (`distorted_ss67_first`),
`log(Ȳ_b/Y*) + x*(Φ_b, Δ̄_b) = O(ε²)` (`Transactions.xStar`) and
`log(m̄_b/mˢ) − (η_y log(Ȳ_b/Y*) − η_id̄_b) = O(ε²)`. -/
theorem distorted_ss67 (hs : Tendsto s L (𝓝 0)) {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys ms : ℝ} (hYs : 0 < Ys) (hms : 0 < ms)
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
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    {Yb mb Phi dbar : B → ℝ} (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hdbar : dbar =O[L] fun b => s b ^ 1)
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ Ut (Yb b, mb b, 0) (0, 1, 0) =
      (1 - Real.exp (-dbar b)) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0)) :
    (fun b => Real.log (Yb b / Ys)) =O[L] (fun b => s b ^ 1) ∧
      (fun b => Real.log (mb b / ms)) =O[L] (fun b => s b ^ 1) ∧
      (fun b => Real.log (Yb b / Ys) + Transactions.xStar P (Phi b) (1 - Real.exp (-dbar b)))
        =O[L] (fun b => s b ^ 2) ∧
      (fun b => Real.log (mb b / ms) - (P.etaY * Real.log (Yb b / Ys) - P.etaI * dbar b))
        =O[L] fun b => s b ^ 2 := by
  set Δ := fun b => 1 - Real.exp (-dbar b) with hΔdef
  have hΔd : (fun b => Δ b - dbar b) =O[L] fun b => s b ^ 2 :=
    (BridgeLinks.exp_sub_one_sub_o hs hdbar.neg_left).neg_left.congr_left fun b => by
      simp only [hΔdef]; ring
  have hΔ : Δ =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hΔd).add hdbar).congr_left fun b => by ring
  obtain ⟨haO, hcO⟩ := distorted_ss67_first hs hUt hv hYs hms P hvel hey hΩ hi hvb huc hsat h11
    h12 h22 hvy hvyy hYb hmb hPhi hΔ hF1 hF2
  set z0 : ℝ × ℝ × Ξ := (Ys, ms, 0) with hz0
  set uc := fderiv ℝ Ut z0 (1, 0, 0) with huc_def
  set D2 := fderiv ℝ (fderiv ℝ Ut) z0 with hD2
  set h : B → ℝ × ℝ × Ξ := fun b => (Yb b - Ys, mb b - ms, 0) with hh
  have hpt : ∀ b, z0 + h b = (Yb b, mb b, 0) := fun b => by
    simp only [hz0, hh, Prod.mk_add_mk, add_zero, add_sub_cancel]
  set o1 := fun b => fderiv ℝ Ut (z0 + h b) (1, 0, 0) - uc - D2 (h b) (1, 0, 0) with ho1
  set o2 := fun b => fderiv ℝ Ut (z0 + h b) (0, 1, 0) - 0 - D2 (h b) (0, 1, 0) with ho2
  set oV := fun b => dY v (Yb b, 0) - dY v (Ys, 0) - (Yb b - Ys) * dYY v (Ys, 0) with hoV
  set y := fun b => (Yb b - Ys) / Ys with hy
  set m' := fun b => (mb b - ms) / ms with hm'
  have sol : ∀ b, y b = (-Phi b - P.chi * P.etaI * Δ b + (ssRho1 P uc (y b) (m' b) (Phi b)
      (o1 b) (oV b) - P.chi * P.etaI * ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b))) /
        Transactions.omegaMC P ∧ m' b = P.etaY * y b - P.etaI * Δ b -
          P.etaI * ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b) := fun b => by
    obtain ⟨d1, d2⟩ := ss67_D2 hUt hYs hms P hvel hi hvb h11 h12 h22 (Yb b - Ys) (mb b - ms)
    refine ss67_algebra P hey hΩ hi huc ?_ ?_
    · have e := hF1 b
      rw [← hpt b] at e
      have eo : fderiv ℝ Ut (z0 + h b) (1, 0, 0) = uc + D2 (h b) (1, 0, 0) + o1 b := by
        simp only [ho1]; ring
      have ev : dY v (Yb b, 0) = uc + uc * P.omega * y b + oV b := by
        simp only [hoV, hvyy, hvy, hy]; ring
      rw [eo, ev] at e
      rw [e]
      change (1 - Phi b) * (uc + D2 (Yb b - Ys, mb b - ms, 0) (1, 0, 0) + o1 b) = _
      rw [d1]
    · have e := hF2 b
      rw [← hpt b] at e
      have eo1 : fderiv ℝ Ut (z0 + h b) (1, 0, 0) = uc + D2 (h b) (1, 0, 0) + o1 b := by
        simp only [ho1]; ring
      have eo2 : fderiv ℝ Ut (z0 + h b) (0, 1, 0) = D2 (h b) (0, 1, 0) + o2 b := by
        simp only [ho2]; ring
      rw [eo1, eo2] at e
      change D2 (Yb b - Ys, mb b - ms, 0) (0, 1, 0) + o2 b =
        Δ b * (uc + D2 (Yb b - Ys, mb b - ms, 0) (1, 0, 0) + o1 b) at e
      rw [d1, d2] at e
      exact e
  -- second-order remainders
  have hhO : h =O[L] fun b => s b ^ 1 := haO.prod_left (hcO.prod_left (isBigO_zero _ _))
  have T := BridgeLinks.taylor1_family (hUt.fderiv_right (m := 2) (by norm_num)) z0 hs hhO
  have T' : ∀ w : ℝ × ℝ × Ξ, (fun b => fderiv ℝ Ut (z0 + h b) w - fderiv ℝ Ut z0 w -
      D2 (h b) w) =O[L] fun b => s b ^ 2 := fun w =>
    (((ContinuousLinearMap.apply ℝ ℝ w).isBigO_comp _ _).trans T).congr_left fun b => by
      simp [hD2]
  have ho1O : o1 =O[L] fun b => s b ^ 2 := (T' (1, 0, 0)).congr_left fun b => by
    simp only [ho1, huc_def]
  have ho2O : o2 =O[L] fun b => s b ^ 2 := (T' (0, 1, 0)).congr_left fun b => by
    simp only [ho2, hsat]
  have hV : HasDerivAt (fun y => dY v (y, 0)) (dYY v (Ys, 0)) Ys :=
    hasDerivAt_dY (hv.of_le (by norm_num)) Ys
  have hoVO : oV =O[L] fun b => s b ^ 2 := by
    have T2 := BridgeLinks.taylor1_family (contDiff_dY hv) Ys hs haO
    refine T2.congr_left fun b => ?_
    rw [hV.hasFDerivAt.fderiv]
    simp only [hoV, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, add_sub_cancel]
  have hyO : y =O[L] fun b => s b ^ 1 := (haO.const_mul_left Ys⁻¹).congr_left fun b => by
    simp only [hy]; ring
  have hmO : m' =O[L] fun b => s b ^ 1 := (hcO.const_mul_left ms⁻¹).congr_left fun b => by
    simp only [hm']; ring
  have hGO : (fun b => -P.sigInv * y b + P.chi * m' b) =O[L] fun b => s b ^ 1 :=
    (hyO.const_mul_left (-P.sigInv)).add (hmO.const_mul_left P.chi)
  have h1Phi : (fun b => 1 - Phi b) =O[L] (fun _ => (1 : ℝ)) :=
    (isBigO_const_const (1 : ℝ) one_ne_zero L).sub
      ((isLittleO_one_iff ℝ).2 (tendsto_of_o_one hs hPhi)).isBigO
  have hρ1O : (fun b => ssRho1 P uc (y b) (m' b) (Phi b) (o1 b) (oV b)) =O[L]
      fun b => s b ^ 2 :=
    ((o_mul hPhi hGO (by norm_num : 1 + 1 = 2)).neg_left.add
      ((((h1Phi.mul ho1O).congr_right fun b => by ring).sub hoVO).const_mul_left
        uc⁻¹)).congr_left fun b => by simp only [ssRho1]; ring
  have hρ2O : (fun b => ssRho2 P uc (y b) (m' b) (Δ b) (o1 b) (o2 b)) =O[L]
      fun b => s b ^ 2 :=
    ((o_mul hΔ hGO (by norm_num : 1 + 1 = 2)).add
      (((o_weaken hs (by norm_num : 2 ≤ 3) (o_mul hΔ ho1O (by norm_num : 1 + 2 = 3))).sub
        ho2O).const_mul_left uc⁻¹)).congr_left fun b => by simp only [ssRho2]; ring
  have hlY := log_move hYs hs haO
  have hlm := log_move hms hs hcO
  have hcY : (fun b => Real.log (Yb b / Ys)) =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hlY).add hyO).congr_left fun b => by
      simp only [hy]; ring
  have hcm : (fun b => Real.log (mb b / ms)) =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hlm).add hmO).congr_left fun b => by
      simp only [hm']; ring
  have hyx : (fun b => y b + Transactions.xStar P (Phi b) (Δ b)) =O[L] fun b => s b ^ 2 := by
    refine ((hρ1O.sub (hρ2O.const_mul_left (P.chi * P.etaI))).const_mul_left
      (Transactions.omegaMC P)⁻¹).congr_left fun b => ?_
    have hx : Transactions.xStar P (Phi b) (Δ b) =
        (Phi b + P.chi * P.etaI * Δ b) / Transactions.omegaMC P := by
      simp only [Transactions.xStar, Transactions.sM, hey]
      field_simp
    rw [hx]
    linear_combination -(sol b).1
  refine ⟨hcY, hcm, (hlY.add hyx).congr_left fun b => by simp only [hy, hΔdef]; ring, ?_⟩
  refine ((((hlm.sub (hlY.const_mul_left P.etaY)).sub (hρ2O.const_mul_left P.etaI)).sub
    (hΔd.const_mul_left P.etaI))).congr_left fun b => ?_
  have e := (sol b).2
  simp only [hy, hm'] at e ⊢
  linear_combination -e

/-! ## Proposition 6.7 around the distorted steady state -/

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, expanded around the DISTORTED steady
state.** Under the hypotheses of `BridgeExtensions.prop67_actual` at the efficient satiated
point `(Y*, mˢ)` (with velocity `v̄ = Y*/mˢ` and `u_c ≠ 0`), let `(Ȳ_b, m̄_b)` be a branch of
distorted steady states (`distorted_ss67`: `Φ_b = O(ε)`, `Δ̄_b = 1 − e^{−d̄_b}`, `d̄_b = O(ε)`).
Measure outputs and balances relative to the distorted steady state
(`y(i) = Ȳ_be^{ŷ(i)}`, `m = m̄_be^{m̂}`) and the interest differential relative to its steady
state value (`î − îᵐ = d̄_b + d`); let the distorted money demand (4.1) hold up to `O(ε²)` and
real balances stay below satiation. Then the actual period utility is
`t.i.p. − ½Y*u_c·(4.9) + O(ε³)`, where (4.9) is
`Ω_mc(Ŷ − Ŷⁿ − x*)² + v̄⁻¹η_i(d + Δ̄)² + (θ⁻¹ + ω)var_i ŷ` with `x* = (Φ + s_mη_y)/Ω_mc`,
`s_m = Δ̄/v̄` (the loss of `Transactions.prop_6_7_layerA` at `txDist`). -/
theorem prop67_distorted (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
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
    {Yb mb Phi dbar : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hmb0 : ∀ b, 0 < mb b)
    (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hdbar : dbar =O[L] fun b => s b ^ 1)
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ Ut (Yb b, mb b, 0) (0, 1, 0) =
      (1 - Real.exp (-dbar b)) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
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
  obtain ⟨hcY, hcm, hcx, hcmr⟩ := distorted_ss67 hs hUt hv hYs hms P hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy hYb hmb hPhi hdbar hF1 hF2
  set cY := fun b => Real.log (Yb b / Ys) with hcYd
  set cm := fun b => Real.log (mb b / ms) with hcmd
  set Δ := fun b => 1 - Real.exp (-dbar b) with hΔdef
  have hΔd : (fun b => Δ b - dbar b) =O[L] fun b => s b ^ 2 :=
    (BridgeLinks.exp_sub_one_sub_o hs hdbar.neg_left).neg_left.congr_left fun b => by
      simp only [hΔdef]; ring
  have hΔ : Δ =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hΔd).add hdbar).congr_left fun b => by ring
  have he : (fun b => fun i => yd b i + cY b) =O[L] fun b => s b ^ 1 :=
    isBigO_pi.2 fun i => (coord_o hyd i).add hcY
  have hrs : (fun b => (md b + cm b) - (P.etaY * logYidx w θ (fun i => yd b i + cY b) -
      P.etaI * (d b + dbar b) + eps b)) =O[L] fun b => s b ^ 2 :=
    (hr.add hcmr).congr_left fun b => by
      rw [logYidx_shift hw0 hw1 hθ]; ring
  have hW := prop67_actual hs hw0 hw1 hθ hUt hms hEq hv P hθi hey hΩ hi hvb hsat h11 h12 h22
    hvy hvyy hg heps hq he (hmd.add hcm) (hd.add hdbar) hgO hqO hepsO hxu hxv hrs hleft
  have hYO : (fun b => logYidx w θ (yd b)) =O[L] fun b => s b ^ 1 :=
    logYidx_o hs hw0 hw1 hθ hyd
  have hnat : (fun b => Transactions.natRate P (g b) (q b) (eps b)) =O[L] fun b => s b ^ 1 :=
    ((((hgO.const_mul_left P.sigInv).add (hqO.const_mul_left P.omega)).add
      (hepsO.const_mul_left P.chi)).const_mul_left (Transactions.omegaMC P)⁻¹).congr_left
        fun b => by unfold Transactions.natRate; ring
  have hx : (fun b => Transactions.xStar P (Phi b) (Δ b)) =O[L] fun b => s b ^ 1 :=
    ((hPhi.add (hΔ.const_mul_left (P.etaY / P.vbar))).const_mul_left
      (Transactions.omegaMC P)⁻¹).congr_left fun b => by
        simp only [Transactions.xStar, Transactions.sM]; ring
  have hgap : (fun b => 2 * (logYidx w θ (yd b) - Transactions.natRate P (g b) (q b) (eps b)) +
      cY b - Transactions.xStar P (Phi b) (Δ b)) =O[L] fun b => s b ^ 1 :=
    (((hYO.sub hnat).const_mul_left 2).add hcY).sub hx
  have hdgap : (fun b => 2 * d b + dbar b + Δ b) =O[L] fun b => s b ^ 1 :=
    ((hd.const_mul_left 2).add hdbar).add hΔ
  have hdiff := ((o_mul hcx hgap (by norm_num : 2 + 1 = 3)).const_mul_left
      (Transactions.omegaMC P)).add
    ((o_mul hΔd.neg_left hdgap (by norm_num : 2 + 1 = 3)).const_mul_left (P.etaI / P.vbar))
  refine (hW.sub (hdiff.const_mul_left
    (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / 2))).congr_left fun b => ?_
  have pU := periodUT_shift hw0 hw1 hθ U v hYs hms (hYb0 b) (hmb0 b) (yd b) (md b) (xu b) (xv b)
  have v1 : crossVar w (fun i => yd b i + cY b) = crossVar w (yd b) := by
    rw [← ExpLogCES.crossVar_const_add hw1 (cY b) (yd b)]
    congr 1
    funext i
    ring
  have s1 := logYidx_shift hw0 hw1 hθ (cY b) (yd b)
  simp only [hcYd, hcmd] at pU v1 s1 ⊢
  rw [pU, s1, v1]
  simp only [Transactions.loss49, txSat, txDist, Transactions.xStar, Transactions.sM, hΔdef,
    zero_div, zero_mul, add_zero]
  ring

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, LAYER B around the distorted steady
state**: under the hypotheses of `prop67_distorted`, if the family has a first-order solution
(`Φ = εΦ¹ + O(ε²)`, `d̄ = εd̄¹ + O(ε²)`, `ŷ = εŷ¹ + O(ε²)`, `Ŷ, d, g, q, εᵐ = ε × first order +
O(ε²)`, all first-order objects bounded), then
`W(ε) = t.i.p.(ε) − (ε²/2)·Y*u_c·(4.9)(first-order solution) + O(ε³)`, the first-order loss
having distortions `(Φ¹, d̄¹)`. -/
theorem prop67_distorted_layerB (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
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
    {Yb mb Phi dbar : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hmb0 : ∀ b, 0 < mb b)
    (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ Ut (Yb b, mb b, 0) (0, 1, 0) =
      (1 - Real.exp (-dbar b)) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    {yd y1 : B → ι → ℝ} {md d g q eps Phi1 dbar1 Y1 d1 g1 q1 eps1 : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hmd : md =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => md b - (P.etaY * logYidx w θ (yd b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log (mb b / ms) ≤ 0)
    (hy1 : y1 =O[L] fun _ => (1 : ℝ)) (hY1 : Y1 =O[L] fun _ => (1 : ℝ))
    (hd1 : d1 =O[L] fun _ => (1 : ℝ)) (hg1 : g1 =O[L] fun _ => (1 : ℝ))
    (hq1 : q1 =O[L] fun _ => (1 : ℝ)) (heps1 : eps1 =O[L] fun _ => (1 : ℝ))
    (hPhi1 : Phi1 =O[L] fun _ => (1 : ℝ)) (hdbar1 : dbar1 =O[L] fun _ => (1 : ℝ))
    (hydd : (fun b => yd b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θ (yd b) - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hqd : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (hepsd : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2)
    (hPhid : (fun b => Phi b - s b * Phi1 b) =O[L] fun b => s b ^ 2)
    (hdbard : (fun b => dbar b - s b * dbar1 b) =O[L] fun b => s b ^ 2) :
    (fun b => periodUT U v w θ (Yb b) (mb b) (yd b) (md b) (xu b) (xv b) -
      ((tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        Transactions.tip P (g b) (q b) (eps b) 0 0) -
        s b ^ 2 / 2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * Transactions.loss49 P
          (txDist P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (Phi1 b) (dbar1 b) (crossVar w (y1 b))
            0)))) =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop67_distorted hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy hYb0 hmb0 hYb hmb (fo Phi Phi1 hPhid hPhi1)
    (fo dbar dbar1 hdbard hdbar1) hF1 hF2 hg heps hq hyd hmd (fo d d1 hdd hd1)
    (fo g g1 hgd hg1) (fo q q1 hqd hq1) (fo eps eps1 hepsd heps1) hxu hxv hr hleft
  have hΔd : (fun b => (1 - Real.exp (-dbar b)) - dbar b) =O[L] fun b => s b ^ 2 :=
    (BridgeLinks.exp_sub_one_sub_o hs (fo dbar dbar1 hdbard hdbar1).neg_left).neg_left.congr_left
      fun b => by ring
  have hΔ1 : (fun b => (1 - Real.exp (-dbar b)) - s b * dbar1 b) =O[L] fun b => s b ^ 2 :=
    (hΔd.add hdbard).congr_left fun b => by ring
  set c1 := (Transactions.omegaMC P)⁻¹
  set c2 := P.etaY / P.vbar / Transactions.omegaMC P
  have hYx : (fun b => (logYidx w θ (yd b) - Transactions.xStar P (Phi b)
      (1 - Real.exp (-dbar b))) - s b * (Y1 b - Transactions.xStar P (Phi1 b) (dbar1 b)))
      =O[L] fun b => s b ^ 2 :=
    ((hYd.sub (hPhid.const_mul_left c1)).sub (hΔ1.const_mul_left c2)).congr_left fun b => by
      simp only [Transactions.xStar, Transactions.sM, c1, c2]; ring
  have bYx : (fun b => Y1 b - Transactions.xStar P (Phi1 b) (dbar1 b)) =O[L] fun _ => (1 : ℝ) :=
    ((hY1.sub (hPhi1.const_mul_left c1)).sub (hdbar1.const_mul_left c2)).congr_left fun b => by
      simp only [Transactions.xStar, Transactions.sM, c1, c2]; ring
  have hdx : (fun b => (d b + (1 - Real.exp (-dbar b))) - s b * (d1 b + dbar1 b))
      =O[L] fun b => s b ^ 2 :=
    (hdd.add hΔ1).congr_left fun b => by ring
  have hL := loss49_first_order hs P (m := md) (m1 := fun _ => 0) hYx hdx hgd hqd hepsd
    (crossVar_first_order hs hw0 hw1 hydd hy1) bYx (hd1.add hdbar1) hg1 hq1 heps1
  set K := Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) with hK
  have hW' : (fun b => periodUT U v w θ (Yb b) (mb b) (yd b) (md b) (xu b) (xv b) -
      ((tipT Ut v Ys ms (xu b) (xv b) + K * Transactions.tip P (g b) (q b) (eps b) 0 0) -
        K * Transactions.loss49 P (txDist P (logYidx w θ (yd b)) (d b) (g b) (q b) (eps b)
          (Phi b) (1 - Real.exp (-dbar b)) (crossVar w (yd b)) (md b)) / 2)) =O[L]
      fun b => s b ^ 3 := hW.congr_left fun b => by ring
  have hL' : (fun b => Transactions.loss49 P (txDist P (logYidx w θ (yd b)) (d b) (g b) (q b)
      (eps b) (Phi b) (1 - Real.exp (-dbar b)) (crossVar w (yd b)) (md b)) -
      s b ^ 2 * Transactions.loss49 P (txDist P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (Phi1 b)
        (dbar1 b) (crossVar w (y1 b)) 0)) =O[L] fun b => s b ^ 3 := by
    refine hL.congr_left fun b => ?_
    simp only [Transactions.loss49, txDist, txSat, Transactions.xStar, Transactions.sM,
      zero_div, zero_mul, add_zero]
    ring
  exact bridge_first_order hW' hL'

end Woodford.StabilizationWelfare.TidyR5Distorted67
