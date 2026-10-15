/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.NKPC
import NominalRigidities.FlexiblePrices
import NominalRigidities.StrategicComplementarity
import NominalRigidities.SpendingGrowth
import NominalRigidities.Delays
import NominalRigidities.StickyWages

/-!
# Cross-chain links

Woodford (2003), *Interest and Prices*, Chapter 3: §1.1–1.3 (pp. 146–163), §2.1–2.2
(pp. 177–188, Propositions 3.4–3.5) and App. B.3–B.4 (pp. 659–662).

The Calvo modules take the marginal-profit function
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ e^y, z)` as an abstract primitive and assume the relation
`ζ(Ŷ − Ŷⁿ) = (1 + ω̃θ)⁻¹ ŝ` between the output gap and real marginal cost. This module
instantiates `mp` with the baseline profit function (1.18) of `FlexiblePrices` and the real
marginal cost function (1.10) of `MarginalCost`, and derives the relation and its coefficients.

## The baseline marginal profit

* `baseMP`: `Π₁(eˣ, eˣ, 1; Ȳ e^y, ξ̃(z))` for (1.18), along a direction `d = (a, ξ)` of the
  disturbances `ξ̃ = (A, ξ) = (e^{z a}, z ξ)`; `baselineProfit_hasDerivAt`: it is the derivative
  of `FlexiblePrices.baselineProfit` in the own price at a symmetric point.
* `baseMP_hasFDerivAt`: `mp` is Fréchet differentiable at the zero-inflation steady state, with
  derivative `baseD`, `(θ − 1)Ȳ (Dŝ(y − θx, y, za, zξ) − x)`; `baseD_coeffs`: hence
  `ψ_p = −(θ − 1)Ȳ(1 + ωθ)`, `ψ_y = (θ − 1)Ȳ(ω + σ⁻¹)` with `ω = ω_w + ω_p` and `σ⁻¹` the
  elasticities (1.16) of `MarginalCost`; `baseD_zeta`: `ζ = −ψ_y/ψ_p` is (1.35)
  (`StrategicComplementarity.zetaGen θ 0 ω σ⁻¹`).
* `baseD_gap_rmc`: with the natural rate `ŷⁿ = −(ψ_z/ψ_y) z`, `ζ(ŷ − ŷⁿ) = (1 + ωθ)⁻¹ ŝ`,
  where `ŝ = Dŝ(ŷ, ŷ, za, zξ)` is real marginal cost (1.15) linearised exactly; `baseD_natRate`:
  this `ŷⁿ` is the derivative of the natural rate of `MarginalCost.naturalRate_deriv`.

## Propositions 3.4–3.7 from primitives

* `prop35_baseline`: Proposition 3.5 and (2.14) for the baseline model, with `ζ` of (1.35) and
  `κ = (ω + σ⁻¹)ξ` derived, not assumed; `eq26_iff_eq28_baseline`: (2.6) ⟺ (2.8) (the setting of
  Proposition 3.4) with the `ŝ` relation derived.
* `persistence_nkpc_iff`, `prop35_persistence`: the price-level (2.12) of `Persistence` and
  `SpendingGrowth` is Proposition 3.5's NKPC; `calvo_eq_eqmP`: the Calvo equilibrium is the
  equilibrium of Propositions 3.6–3.7; `prop_3_6_calvo`: Proposition 3.6 for it.
* `nkpc_iff_delayed_zero`: the NKPC is the `d = 0` case of (3.2) in `Delays`.
* `flexible_wages_slope_eq_kappa`: the flexible-wage limit of (4.15) in `StickyWages` is (2.13)
  with `ζ` of (1.37).
-/

namespace Woodford.NominalRigidities.Links

open Filter Topology
open MarginalCost (Technology rmc logRmcGap omegaW omegaP sigmaInv)
open FlexiblePrices (dem)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The baseline marginal profit `mp` -/

/-- Woodford (2003), eq. (1.18), p. 153, and (2.4), p. 179: the marginal profit
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ e^y, ξ̃)` of the baseline profit function, with the disturbance
`ξ̃ = (A, ξ) = (e^{z a}, z ξ)` moving along the direction `d = (a, ξ)`:
`y(eˣ)[(1 − θ) + θ s(y(eˣ), Ȳe^y; ξ̃)/eˣ]`, `y(p) = Ȳ e^y p^{−θ}`
(`FlexiblePrices.hasDerivAt_profit` with nominal marginal cost (1.8) at the industry wage). -/
noncomputable def baseMP (T : Technology) (vh uc : ℝ → F → ℝ) (θ Ybar : ℝ) (d : ℝ × F)
    (x y z : ℝ) : ℝ :=
  dem (Ybar * Real.exp y) 1 θ (Real.exp x) *
    ((1 - θ) + θ * rmc T vh uc (dem (Ybar * Real.exp y) 1 θ (Real.exp x)) (Ybar * Real.exp y)
      (Real.exp (d.1 * z)) (z • d.2) / Real.exp x)

/-- Woodford (2003), eq. (1.18), p. 153, and p. 158 (`Π₁` at a symmetric point): the own-price
derivative of `FlexiblePrices.baselineProfit` at `p = p^I = eˣ`, `P = 1`, `Y = Ȳ e^y`, with the
disturbance `(e^{z a}, z ξ)`, is `baseMP x y z`. -/
theorem baselineProfit_hasDerivAt (T : Technology) (vh uc : ℝ → F → ℝ) {θ Ybar : ℝ}
    (hY : 0 < Ybar) (d : ℝ × F) (x y z : ℝ) :
    HasDerivAt (fun p => FlexiblePrices.baselineProfit T vh uc θ p (Real.exp x) 1
        (Ybar * Real.exp y) (Real.exp (d.1 * z), z • d.2))
      (baseMP T vh uc θ Ybar d x y z) (Real.exp x) := by
  set Y := Ybar * Real.exp y with hYdef
  set A := Real.exp (d.1 * z) with hA
  have hY0 : 0 < Y := mul_pos hY (Real.exp_pos y)
  have hA0 : 0 < A := Real.exp_pos _
  set w := vh (T.finv (dem Y 1 θ (Real.exp x) / A)) (z • d.2) / uc Y (z • d.2) * 1 with hw
  have hC : ∀ q, 0 < q → HasDerivAt (fun q => w * T.finv (q / A)) (w / A * T.Psi (q / A)) q :=
    fun q hq => T.hasDerivAt_variableCost w hA0 hq
  have h := FlexiblePrices.hasDerivAt_profit (θ := θ) hY0 one_pos (Real.exp_pos x) hC
  refine HasDerivAt.congr_deriv h ?_
  simp only [baseMP, rmc, hw]
  ring

/-- Woodford (2003), eq. (1.12), p. 151: at `P = 1`, `y(eˣ) = Ȳ e^y (eˣ)^{−θ} = Ȳ e^{y − θx}`. -/
theorem dem_exp (Ybar θ x y : ℝ) :
    dem (Ybar * Real.exp y) 1 θ (Real.exp x) = Ybar * Real.exp (y - θ * x) := by
  rw [dem, div_one, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
  ring_nf

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Woodford (2003), eq. (1.10), p. 149: real marginal cost is positive when `v_h > 0` at
positive hours, `u_c > 0` and `y, A > 0`. -/
theorem rmc_pos (T : Technology) {vh uc : ℝ → F → ℝ} (hvh : ∀ ξ h, 0 < h → 0 < vh h ξ)
    (huc : ∀ ξ Y, 0 < Y → 0 < uc Y ξ) {y Y A : ℝ} (hy : 0 < y) (hYp : 0 < Y) (hA : 0 < A)
    (ξ : F) : 0 < rmc T vh uc y Y A ξ :=
  mul_pos (div_pos (hvh ξ _ (T.finv_pos _ (div_pos hy hA))) (mul_pos (huc ξ Y hYp) hA))
    (T.Psi_pos (div_pos hy hA))

/-- Woodford (2003), (2.6), p. 180: the linear map `(x, y, z) ↦ (y − θx, y, a z, z ξ)` sending a
perturbation of (relative price, output, disturbance) to the arguments `(ŷ, Ŷ, log A, ξ)` of
log real marginal cost (1.15) of a firm charging `eˣ` (its output is `ŷ = Ŷ − θx`). -/
noncomputable def shockLin (θ : ℝ) (d : ℝ × F) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ × F :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) -
      θ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
      ((d.1 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).prod
        (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight d.2)))

/-- Woodford (2003), (2.6), p. 180: `shockLin θ d (x, y, z) = (y − θx, y, a z, z ξ)`. -/
theorem shockLin_apply (θ : ℝ) (d : ℝ × F) (x y z : ℝ) :
    shockLin θ d (x, y, z) = (y - θ * x, y, d.1 * z, z • d.2) := by
  simp [shockLin]

/-- Woodford (2003), eqs. (1.14)–(1.15), p. 152, and (1.18), p. 153 (**the baseline marginal
profit in log-deviation form**): if `v_h, u_c > 0` and the steady state is the zero-inflation
one, `μ s̄ = 1` (`θ s̄ = θ − 1`, `s̄ = s(Ȳ, Ȳ; 1, 0)`), then
`mp(x, y, z) = (θ − 1) Ȳ e^{y − θx} (e^{ŝ(y − θx, y, za, zξ) − x} − 1)`, with `ŝ` the log real
marginal cost gap `MarginalCost.logRmcGap`. -/
theorem baseMP_eq (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar : ℝ} (hY : 0 < Ybar)
    (hvh : ∀ ξ h, 0 < h → 0 < vh h ξ) (huc : ∀ ξ Y, 0 < Y → 0 < uc Y ξ)
    (hss : θ * rmc T vh uc Ybar Ybar 1 0 = θ - 1) (d : ℝ × F) (x y z : ℝ) :
    baseMP T vh uc θ Ybar d x y z = (θ - 1) * (Ybar * Real.exp (y - θ * x)) *
      (Real.exp (logRmcGap T vh uc Ybar (shockLin θ d (x, y, z)) - x) - 1) := by
  have hs : 0 < rmc T vh uc Ybar Ybar 1 0 := rmc_pos T hvh huc hY hY one_pos 0
  have hr : 0 < rmc T vh uc (Ybar * Real.exp (y - θ * x)) (Ybar * Real.exp y)
      (Real.exp (d.1 * z)) (z • d.2) :=
    rmc_pos T hvh huc (mul_pos hY (Real.exp_pos _)) (mul_pos hY (Real.exp_pos _))
      (Real.exp_pos _) _
  have hG : Real.exp (logRmcGap T vh uc Ybar (shockLin θ d (x, y, z))) =
      rmc T vh uc (Ybar * Real.exp (y - θ * x)) (Ybar * Real.exp y) (Real.exp (d.1 * z))
        (z • d.2) / rmc T vh uc Ybar Ybar 1 0 := by
    rw [shockLin_apply, logRmcGap, Real.exp_sub, Real.exp_log hr]
    simp [Real.exp_log hs]
  rw [Real.exp_sub (logRmcGap T vh uc Ybar (shockLin θ d (x, y, z))) x, hG, baseMP, dem_exp]
  have hx := Real.exp_pos x
  have key : θ * rmc T vh uc (Ybar * Real.exp (y - θ * x)) (Ybar * Real.exp y)
      (Real.exp (d.1 * z)) (z • d.2) / Real.exp x = (θ - 1) * (rmc T vh uc
        (Ybar * Real.exp (y - θ * x)) (Ybar * Real.exp y) (Real.exp (d.1 * z)) (z • d.2) /
          rmc T vh uc Ybar Ybar 1 0 / Real.exp x) := by
    rw [← hss]
    field_simp
  rw [key]
  ring

/-- Woodford (2003), eq. (2.6), p. 180: the derivative of the baseline `mp` at the steady state,
`D(x, y, z) = (θ − 1) Ȳ (Dŝ(y − θx, y, za, zξ) − x)`, `Dŝ` the derivative of (1.15). -/
noncomputable def baseD (T : Technology) (vh uc : ℝ → F → ℝ) (θ Ybar : ℝ) (d : ℝ × F) :
    ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  ((θ - 1) * Ybar) • ((fderiv ℝ (logRmcGap T vh uc Ybar) 0).comp (shockLin θ d) -
    ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))

/-- Woodford (2003), eq. (2.6), p. 180, and (1.15), p. 152 (**the baseline `mp` is Fréchet
differentiable at the zero-inflation steady state**): under the regularity of
`MarginalCost.logRmcGap_differentiableAt`, positive `v_h, u_c` and `μ s̄ = 1`,
`D mp(x, y, z) = (θ − 1) Ȳ (Dŝ(y − θx, y, za, zξ) − x)`. -/
theorem baseMP_hasFDerivAt (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar d2f : ℝ}
    (hY : 0 < Ybar) (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ ξ h, 0 < h → 0 < vh h ξ) (huc : ∀ ξ Y, 0 < Y → 0 < uc Y ξ)
    (hss : θ * rmc T vh uc Ybar Ybar 1 0 = θ - 1) (d : ℝ × F) :
    HasFDerivAt (fun v : ℝ × ℝ × ℝ => baseMP T vh uc θ Ybar d v.1 v.2.1 v.2.2)
      (baseD T vh uc θ Ybar d) 0 := by
  set G := logRmcGap T vh uc Ybar with hGdef
  set L := shockLin (F := F) θ d with hLdef
  have hG : HasFDerivAt G (fderiv ℝ G 0) (L 0) := by
    rw [map_zero]
    exact (MarginalCost.logRmcGap_differentiableAt T vh uc hY hd2f hvhd hucd
      (hvh 0 _ (T.finv_pos _ hY)) (huc 0 _ hY)).hasFDerivAt
  have h1 := (hG.comp (0 : ℝ × ℝ × ℝ) L.hasFDerivAt).sub
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))
  have h2 := h1.exp.sub_const 1
  have h3d : DifferentiableAt ℝ
      (fun v : ℝ × ℝ × ℝ => (θ - 1) * (Ybar * Real.exp (v.2.1 - θ * v.1))) 0 := by
    fun_prop
  have h4 := h3d.hasFDerivAt.mul h2
  refine (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)).congr_fderiv ?_
  · obtain ⟨x, y, z⟩ := v
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    rw [baseMP_eq T hY hvh huc hss d x y z]
  · have h00 : logRmcGap T vh uc Ybar 0 = 0 := by simp [logRmcGap]
    ext <;> simp [baseD, hGdef, hLdef, h00]

/-- Woodford (2003), eq. (1.15)–(1.16), p. 152, and (2.6), p. 180: the derivative of the baseline
`mp` in terms of the elasticities `ω = ω_w + ω_p` and `σ⁻¹` of `MarginalCost`:
`D(x, y, z) = (θ − 1)Ȳ (ω(y − θx) + σ⁻¹y − (1 + ω)az + Dŝ(0, 0, 0, zξ) − x)`. -/
theorem baseD_apply (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0) (d : ℝ × F) (x y z : ℝ) :
    baseD T vh uc θ Ybar d (x, y, z) = (θ - 1) * Ybar *
      ((omegaW T vh vhh Ybar + omegaP T d2f Ybar) * (y - θ * x) + sigmaInv uc ucc Ybar * y
        - (1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar)) * (d.1 * z)
        + fderiv ℝ (logRmcGap T vh uc Ybar) 0 (0, 0, 0, z • d.2) - x) := by
  simp only [baseD, FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', shockLin_apply, smul_eq_mul]
  rw [MarginalCost.fderiv_logRmcGap T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc]

/-- Woodford (2003), p. 164 and (2.6), p. 180 (**the coefficients of the baseline `mp`**):
`ψ_p = D(1, 0, 0) = −(θ − 1)Ȳ(1 + ωθ)` and `ψ_y = D(0, 1, 0) = (θ − 1)Ȳ(ω + σ⁻¹)`. -/
theorem baseD_coeffs (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0) (d : ℝ × F) :
    baseD T vh uc θ Ybar d (1, 0, 0) =
        -((θ - 1) * Ybar * (1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ)) ∧
      baseD T vh uc θ Ybar d (0, 1, 0) =
        (θ - 1) * Ybar * (omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar) := by
  constructor
  · rw [baseD_apply T hY hvhh hd2f hucc hvhd hucd hvh huc]
    simp only [zero_smul, mul_zero, sub_zero]
    rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : F)) = 0 from rfl, map_zero]
    ring
  · rw [baseD_apply T hY hvhh hd2f hucc hvhd hucd hvh huc]
    simp only [zero_smul, mul_zero, sub_zero]
    rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : F)) = 0 from rfl, map_zero]
    ring

/-- Woodford (2003), eq. (1.35), p. 164 (**the baseline `ζ` from primitives**): for the baseline
`mp`, `ζ = −ψ_y/ψ_p = (ω + σ⁻¹)/(1 + ωθ)`, the value (1.35)
`StrategicComplementarity.zetaGen θ 0 ω σ⁻¹`, with `ω = ω_w + ω_p` and `σ⁻¹` the elasticities
(1.16) of `MarginalCost` (`θ ≠ 1`, `Ȳ > 0`). -/
theorem baseD_zeta (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hθ : θ ≠ 1) (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0) (d : ℝ × F) :
    -baseD T vh uc θ Ybar d (0, 1, 0) / baseD T vh uc θ Ybar d (1, 0, 0) =
      StrategicComplementarity.zetaGen θ 0 (omegaW T vh vhh Ybar + omegaP T d2f Ybar)
        (sigmaInv uc ucc Ybar) := by
  obtain ⟨h1, h2⟩ := baseD_coeffs (θ := θ) T hY hvhh hd2f hucc hvhd hucd hvh huc d
  rw [h1, h2, StrategicComplementarity.zeta_1_35]
  have hθ1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hY0 : Ybar ≠ 0 := hY.ne'
  rw [neg_div_neg_eq, mul_div_mul_left _ _ (mul_ne_zero hθ1 hY0)]

/-- Woodford (2003), (1.15), p. 152, (1.30), p. 158, and (2.14), p. 188 (**the gap–marginal-cost
relation, derived**): for the baseline `mp`, with `ψ = D mp(0)`, `ζ = −ψ_y/ψ_p` and the natural
rate `ŷⁿ = −(ψ_z/ψ_y) z` of `Calvo.natRate_deriv`, `ζ(ŷ − ŷⁿ) = (1 + ωθ)⁻¹ ŝ` with
`ŝ = Dŝ(ŷ, ŷ, za, zξ)` real marginal cost (1.15) at the symmetric point, linearised exactly
(`θ ≠ 1`, `1 + ωθ ≠ 0`, `ω + σ⁻¹ ≠ 0`). This is the hypothesis of `Calvo.eq26_iff_eq28` and
`NKPC.nkpc_iff_eq214`, with `ω̃ = ω`. -/
theorem baseD_gap_rmc (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hθ : θ ≠ 1) (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    (hωθ : 1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ ≠ 0)
    (hωσ : omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar ≠ 0)
    (d : ℝ × F) (y z : ℝ) :
    -baseD T vh uc θ Ybar d (0, 1, 0) / baseD T vh uc θ Ybar d (1, 0, 0) *
        (y - -(baseD T vh uc θ Ybar d (0, 0, 1) / baseD T vh uc θ Ybar d (0, 1, 0)) * z) =
      (1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ)⁻¹ *
        fderiv ℝ (logRmcGap T vh uc Ybar) 0 (y, y, d.1 * z, z • d.2) := by
  obtain ⟨h1, h2⟩ := baseD_coeffs (θ := θ) T hY hvhh hd2f hucc hvhd hucd hvh huc d
  set D := baseD T vh uc θ Ybar d
  have hlin : D (0, y, z) = y * D (0, 1, 0) + z * D (0, 0, 1) := by
    have e : ((0 : ℝ), y, z) =
        y • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + z • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hval : D (0, y, z) = (θ - 1) * Ybar *
      fderiv ℝ (logRmcGap T vh uc Ybar) 0 (y, y, d.1 * z, z • d.2) := by
    simp [D, baseD, shockLin_apply]
  have hθ1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hy : D (0, 1, 0) ≠ 0 := by
    rw [h2]; exact mul_ne_zero (mul_ne_zero hθ1 hY.ne') hωσ
  have hp : D (1, 0, 0) ≠ 0 := by
    rw [h1]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hθ1 hY.ne') hωθ)
  have key : -D (0, 1, 0) / D (1, 0, 0) * (y - -(D (0, 0, 1) / D (0, 1, 0)) * z) =
      -(y * D (0, 1, 0) + z * D (0, 0, 1)) / D (1, 0, 0) := by
    field_simp
    ring
  rw [key, ← hlin, hval, h1]
  field_simp

/-- Woodford (2003), (1.15), p. 152, and (1.21), p. 154 (**the two natural rates agree**): the
natural rate of the baseline `mp`, `ŷⁿ = −(ψ_z/ψ_y) z` (`Calvo.natRate_deriv`), is the
derivative `Dn(za, zξ)` of the natural rate of `MarginalCost.naturalRate_deriv`, defined by
`ŝ(n, n, a, ξ) = 0`. -/
theorem baseD_natRate (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hθ : θ ≠ 1) (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    (hωσ : omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar ≠ 0)
    {n : ℝ × F → ℝ} {Dn : ℝ × F →L[ℝ] ℝ} (hn : HasFDerivAt n Dn 0) (hn0 : n 0 = 0)
    (hnat : ∀ᶠ q in 𝓝 (0 : ℝ × F), logRmcGap T vh uc Ybar (n q, n q, q.1, q.2) = 0)
    (d : ℝ × F) (z : ℝ) :
    -(baseD T vh uc θ Ybar d (0, 0, 1) / baseD T vh uc θ Ybar d (0, 1, 0)) * z =
      Dn (d.1 * z, z • d.2) := by
  obtain ⟨-, h2⟩ := baseD_coeffs (θ := θ) T hY hvhh hd2f hucc hvhd hucd hvh huc d
  have h3 := baseD_apply (θ := θ) T hY hvhh hd2f hucc hvhd hucd hvh huc d 0 0 1
  have hn' := MarginalCost.naturalRate_deriv T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc hn hn0
    hnat (d.1 * z) (z • d.2)
  have hlin : fderiv ℝ (logRmcGap T vh uc Ybar) 0 (0, 0, 0, z • d.2) =
      z * fderiv ℝ (logRmcGap T vh uc Ybar) 0 (0, 0, 0, d.2) := by
    rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ), z • d.2) = z • ((0 : ℝ), (0 : ℝ), (0 : ℝ), d.2) by simp,
      map_smul, smul_eq_mul]
  rw [one_smul] at h3
  have hθ1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hY0 : Ybar ≠ 0 := hY.ne'
  rw [h2, h3, mul_div_mul_left _ _ (mul_ne_zero hθ1 hY0)]
  rw [hlin] at hn'
  field_simp
  linarith [hn']

/-! ### Propositions 3.4 and 3.5 from the primitives of §1 -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), **Proposition 3.5** (p. 187) and (2.14), p. 188, **from primitives**: for
the baseline model (1.18) with real marginal cost (1.10), let `x_t = ŷ_t − ŷⁿ_t` be the output
gap with the natural rate `ŷⁿ = −(ψ_z/ψ_y) ẑ` of the baseline `mp`, and `ŝ_t` real marginal cost
(1.15) linearised exactly. Then, given (2.5) and the hypotheses of `NKPC.prop35`, (2.6) with
`ζ = (ω + σ⁻¹)/(1 + ωθ)` of (1.35) holds iff the NKPC (2.12) with `κ = (1 − α)(1 − αβ)ζ/α`
holds, iff `π_t = ξ ŝ_t + β E_t π_{t+1}` with `ξ` of (2.11), `ω̃ = ω`; and `κ = (ω + σ⁻¹)ξ`. -/
theorem prop35_baseline (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hθ : 1 < θ) (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    (hωθ : 1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ ≠ 0)
    (hωσ : omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar ≠ 0) (d : ℝ × F)
    {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {P pstar x shat yhat zhat : ℕ → Ω → ℝ} (hPa : ∀ t, 𝔼.E t (P t) = P t)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hπ : Calvo.BoundedIncr P) (hxa : 𝔼.Adapted x)
    (hxb : BoundedProc x) (h25 : Calvo.Eq25 α P pstar)
    (hx : ∀ t ω, x t ω = yhat t ω -
      -(baseD T vh uc θ Ybar d (0, 0, 1) / baseD T vh uc θ Ybar d (0, 1, 0)) * zhat t ω)
    (hs : ∀ t ω, shat t ω = fderiv ℝ (logRmcGap T vh uc Ybar) 0
      (yhat t ω, yhat t ω, d.1 * zhat t ω, zhat t ω • d.2)) :
    (Calvo.Eq26 𝔼 α β P pstar (fun τ ω => StrategicComplementarity.zetaGen θ 0
        (omegaW T vh vhh Ybar + omegaP T d2f Ybar) (sigmaInv uc ucc Ybar) * x τ ω) ↔
      NKPC.NKPCurve 𝔼 β (QuadraticRoots.kappa α β (StrategicComplementarity.zetaGen θ 0
        (omegaW T vh vhh Ybar + omegaP T d2f Ybar) (sigmaInv uc ucc Ybar))) (NKPC.infl P) x) ∧
    (NKPC.NKPCurve 𝔼 β (QuadraticRoots.kappa α β (StrategicComplementarity.zetaGen θ 0
        (omegaW T vh vhh Ybar + omegaP T d2f Ybar) (sigmaInv uc ucc Ybar))) (NKPC.infl P) x ↔
      NKPC.NKPCurve 𝔼 β (QuadraticRoots.calvoXi α β
        ((omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ)) (NKPC.infl P) shat) ∧
    QuadraticRoots.kappa α β (StrategicComplementarity.zetaGen θ 0
        (omegaW T vh vhh Ybar + omegaP T d2f Ybar) (sigmaInv uc ucc Ybar)) =
      (omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar) *
        QuadraticRoots.calvoXi α β ((omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ) := by
  refine ⟨NKPC.prop35 𝔼 hα0 hα1 hβ0 hβ1 hPa hpre hπ hxa hxb h25,
    NKPC.nkpc_iff_eq214 𝔼 hα0 hωθ fun t ω => ?_, ?_⟩
  · rw [← baseD_zeta (θ := θ) T hθ.ne' hY hvhh hd2f hucc hvhd hucd hvh huc d, hx t ω, hs t ω]
    exact baseD_gap_rmc T hθ.ne' hY hvhh hd2f hucc hvhd hucd hvh huc hωθ hωσ d _ _
  · rw [StrategicComplementarity.zeta_1_35, NKPC.kappa_baseline]

/-- Woodford (2003), (2.6) ⟺ (2.8), p. 181, **from primitives** (the setting of Proposition 3.4):
for the baseline model, (2.6) with `ζ` of (1.35) and the output gap `x = ŷ − ŷⁿ` is equivalent to
(2.8) with `ω̃θ = ωθ` and log nominal marginal cost `log S_T = ŝ_T − log µ + log P_T`, where `ŝ`
is real marginal cost (1.15) linearised exactly; `p*` known at `t`, `0 < αβ < 1`. -/
theorem eq26_iff_eq28_baseline (T : Technology) {vh uc : ℝ → F → ℝ} {θ Ybar vhh d2f ucc : ℝ}
    (hθ : 1 < θ) (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    (hωθ : 1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ ≠ 0)
    (hωσ : omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar ≠ 0) (d : ℝ × F)
    {α β m : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1)
    {P pstar x shat yhat zhat : ℕ → Ω → ℝ} (hpa : ∀ t, 𝔼.E t (pstar t) = pstar t)
    (hx : ∀ t ω, x t ω = yhat t ω -
      -(baseD T vh uc θ Ybar d (0, 0, 1) / baseD T vh uc θ Ybar d (0, 1, 0)) * zhat t ω)
    (hs : ∀ t ω, shat t ω = fderiv ℝ (logRmcGap T vh uc Ybar) 0
      (yhat t ω, yhat t ω, d.1 * zhat t ω, zhat t ω • d.2)) :
    Calvo.Eq26 𝔼 α β P pstar (fun τ ω => StrategicComplementarity.zetaGen θ 0
        (omegaW T vh vhh Ybar + omegaP T d2f Ybar) (sigmaInv uc ucc Ybar) * x τ ω) ↔
      Calvo.Eq28 𝔼 α β ((omegaW T vh vhh Ybar + omegaP T d2f Ybar) * θ) m
        (fun τ ω => shat τ ω - m + P (τ + 1) ω) P pstar := by
  refine Calvo.eq26_iff_eq28 𝔼 hab0 hab1 hωθ hpa fun t ω => ?_
  rw [← baseD_zeta (θ := θ) T hθ.ne' hY hvhh hd2f hucc hvhd hucd hvh huc d, hx t ω,
    baseD_gap_rmc T hθ.ne' hY hvhh hd2f hucc hvhd hucd hvh huc hωθ hωσ d, hs t ω]
  ring

/-! ### (2.12) of §2.3–2.4 and §3 is Proposition 3.5's NKPC -/

/-- Woodford (2003), (2.12), p. 187, written as on p. 189: the price-level form
`Persistence.NKPC` (with nominal spending `x` and inherited price level `log P_{−1}`) is the NKPC
`NKPC.NKPCurve` of Proposition 3.5 for inflation `π_t = log P_t − log P_{t−1}` of the price index
`P = prev (log P_{−1}) p` (indexed as in `Calvo`, `P (t + 1) = log P_t`) and the output gap
`x − p`. -/
theorem persistence_nkpc_iff (β κ : ℝ) (pm1 : Ω → ℝ) (x p : ℕ → Ω → ℝ) :
    Persistence.NKPC 𝔼 β κ pm1 x p ↔
      NKPC.NKPCurve 𝔼 β κ (NKPC.infl (Persistence.prev pm1 p)) (fun t => x t - p t) :=
  Iff.rfl

/-- Woodford (2003), **(2.12) is derived** (Proposition 3.5, p. 187, applied to §2.3, p. 189): in
the Calvo model with price index `P = prev (log P_{−1}) p` satisfying (2.5), with bounded
inflation, adapted `p`, and adapted bounded output gap `x − p`, the pricing condition (2.6)
(with `ζ(Ŷ − Ŷⁿ) = ζ(x − p)`) holds iff `p` solves the price-level NKPC `Persistence.NKPC` with
`κ = (1 − α)(1 − αβ)ζ/α` — the equation from which Propositions 3.6 and 3.7 start. -/
theorem prop35_persistence {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {pm1 : Ω → ℝ} {x p pstar : ℕ → Ω → ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1) (hpa : 𝔼.Adapted p)
    (hπ : Calvo.BoundedIncr (Persistence.prev pm1 p)) (hga : 𝔼.Adapted fun t => x t - p t)
    (hgb : BoundedProc fun t => x t - p t) (h25 : Calvo.Eq25 α (Persistence.prev pm1 p) pstar) :
    Calvo.Eq26 𝔼 α β (Persistence.prev pm1 p) pstar (fun T ω => ζ * (x T ω - p T ω)) ↔
      Persistence.NKPC 𝔼 β (QuadraticRoots.kappa α β ζ) pm1 x p := by
  have hPa : ∀ t, 𝔼.E t (Persistence.prev pm1 p t) = Persistence.prev pm1 p t := by
    intro t
    cases t with
    | zero => exact hpm1
    | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hpa t)
  have hpre : ∀ t, 𝔼.E t (Persistence.prev pm1 p (t + 1)) = Persistence.prev pm1 p (t + 1) :=
    fun t => hpa t
  rw [persistence_nkpc_iff]
  exact NKPC.prop35 𝔼 hα0 hα1 hβ0 hβ1 hPa hpre hπ hga hgb h25

/-- Woodford (2003), §2.3, p. 189, and App. B.5 (**the Calvo equilibrium is the equilibrium of
Propositions 3.6–3.7**): under the hypotheses of `prop35_persistence`, if (2.6) holds, nominal
spending `x` has bounded increments and `x₀`, `log P_{−1}` are bounded, then `p` is the unique
adapted solution of (2.12) with linearly growing expected prices, `Persistence.eqmP`. -/
theorem calvo_eq_eqmP {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hζ : 0 < ζ) {pm1 : Ω → ℝ} {x p pstar : ℕ → Ω → ℝ} {M B₀ B₁ : ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1)
    (hpa : 𝔼.Adapted p) (hxa : 𝔼.Adapted x) (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M)
    (hx0 : ∀ ω, |x 0 ω| ≤ B₀) (hpm : ∀ ω, |pm1 ω| ≤ B₁)
    (hπ : Calvo.BoundedIncr (Persistence.prev pm1 p))
    (hgb : BoundedProc fun t => x t - p t) (h25 : Calvo.Eq25 α (Persistence.prev pm1 p) pstar)
    (h26 : Calvo.Eq26 𝔼 α β (Persistence.prev pm1 p) pstar fun T ω => ζ * (x T ω - p T ω)) :
    p = Persistence.eqmP 𝔼 β (QuadraticRoots.kappa α β ζ) pm1 x := by
  have hga : 𝔼.Adapted fun t => x t - p t := fun t => by
    simp only [map_sub, hxa t, hpa t]
  have hκ := QuadraticRoots.kappa_pos hα0 hα1 hβ1 hζ
  have hn := (prop35_persistence 𝔼 hα0 hα1 hβ0 hβ1 hpm1 hpa hπ hga hgb h25).1 h26
  obtain ⟨q, -, hq⟩ := Persistence.nkpc_existsUnique 𝔼 hβ0 hκ hpm1 hxa hx hx0 hpm
  have h1 := hq p ⟨hpa, hn, Persistence.linGrowth_of_gap 𝔼 hx hx0 hgb⟩
  have h2 := hq (Persistence.eqmP 𝔼 β (QuadraticRoots.kappa α β ζ) pm1 x)
    ⟨Persistence.eqmP_adapted 𝔼 hβ0 hκ hpm1 hxa hx, Persistence.eqmP_nkpc 𝔼 hβ0 hκ hpm1 hxa hx,
      Persistence.eqmP_linGrowth 𝔼 hβ0 hκ hx hx0 hpm⟩
  rw [h1, h2]

/-- Woodford (2003), **Proposition 3.6** (p. 190) **for the model derived in §2.1–2.2**: if `p`
and `q` are Calvo equilibria ((2.5), (2.6), as in `prop35_persistence`) for nominal spending `x`
and for `x` shocked by date-`s` news `c ε` that permanently raises nominal spending, then
`E_s log P_{s+k}` rises by `c(1 − λ^{k+1})ε` and `E_s(log Y − log Yⁿ)_{s+k}` by `cλ^{k+1}ε`,
`λ = λ₁` of (2.19) with `κ = (1 − α)(1 − αβ)ζ/α`. -/
theorem prop_3_6_calvo {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hζ : 0 < ζ) {pm1 : Ω → ℝ} {x p q pstar qstar : ℕ → Ω → ℝ} {M B₀ : ℝ}
    (hpm1 : 𝔼.E 0 pm1 = pm1) (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    {s : ℕ} {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0)
    (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) (c : ℝ)
    (hpa : 𝔼.Adapted p) (hπp : Calvo.BoundedIncr (Persistence.prev pm1 p))
    (hgpa : 𝔼.Adapted fun t => x t - p t) (hgpb : BoundedProc fun t => x t - p t)
    (h25p : Calvo.Eq25 α (Persistence.prev pm1 p) pstar)
    (h26p : Calvo.Eq26 𝔼 α β (Persistence.prev pm1 p) pstar fun T ω => ζ * (x T ω - p T ω))
    (hqa : 𝔼.Adapted q) (hπq : Calvo.BoundedIncr (Persistence.prev pm1 q))
    (hgqa : 𝔼.Adapted fun t => x t + c • Persistence.shockPath s (fun _ => 1) ε t - q t)
    (hgqb : BoundedProc fun t => x t + c • Persistence.shockPath s (fun _ => 1) ε t - q t)
    (h25q : Calvo.Eq25 α (Persistence.prev pm1 q) qstar)
    (h26q : Calvo.Eq26 𝔼 α β (Persistence.prev pm1 q) qstar fun T ω =>
      ζ * ((x T + c • Persistence.shockPath s (fun _ => 1) ε T) ω - q T ω)) (k : ℕ) :
    𝔼.E s (q (s + k)) = 𝔼.E s (p (s + k)) +
        (c * (1 - QuadraticRoots.lam1 β (QuadraticRoots.kappa α β ζ) ^ (k + 1))) • ε ∧
      𝔼.E s (x (s + k) + c • Persistence.shockPath s (fun _ => 1) ε (s + k) - q (s + k)) =
        𝔼.E s (x (s + k) - p (s + k)) +
          (c * QuadraticRoots.lam1 β (QuadraticRoots.kappa α β ζ) ^ (k + 1)) • ε := by
  have hκ := QuadraticRoots.kappa_pos hα0 hα1 hβ1 hζ
  have hp := (prop35_persistence 𝔼 hα0 hα1 hβ0 hβ1 hpm1 hpa hπp hgpa hgpb h25p).1 h26p
  have hq := (prop35_persistence 𝔼 hα0 hα1 hβ0 hβ1 hpm1 hqa hπq hgqa hgqb h25q).1 h26q
  obtain ⟨Mε, hMε⟩ := hεb
  have hxq : ∀ t ω, |(x (t + 1) + c • Persistence.shockPath s (fun _ => 1) ε (t + 1)) ω -
      (x t + c • Persistence.shockPath s (fun _ => 1) ε t) ω| ≤ M + |c| * (2 * |Mε|) := by
    intro t ω
    have hsp : ∀ r, |Persistence.shockPath s (fun _ => 1) ε r ω| ≤ |Mε| := by
      intro r
      simp only [Persistence.shockPath]
      split_ifs
      · simpa using (hMε ω).trans (le_abs_self Mε)
      · simp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : x (t + 1) ω + c * Persistence.shockPath s (fun _ => 1) ε (t + 1) ω -
        (x t ω + c * Persistence.shockPath s (fun _ => 1) ε t ω) = (x (t + 1) ω - x t ω) +
        c * (Persistence.shockPath s (fun _ => 1) ε (t + 1) ω -
          Persistence.shockPath s (fun _ => 1) ε t ω) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (hx t ω) ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg c)
    linarith [hsp (t + 1), hsp t]
  have hpg := Persistence.linGrowth_of_gap 𝔼 hx hx0 hgpb
  have hqg := Persistence.linGrowth_of_gap 𝔼 hxq (B₀ := B₀ + |c| * |Mε|) (fun ω => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hx0 ω) ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    simp only [Persistence.shockPath]
    split_ifs
    · simpa using (hMε ω).trans (le_abs_self Mε)
    · simp) hgqb
  obtain ⟨-, h2, h3⟩ := Persistence.prop_3_6_stochastic 𝔼 hβ0 hκ hp hpa hpg hεs hunf
    ⟨Mε, hMε⟩ c hq hqa hqg k
  exact ⟨h2, h3⟩

/-- Woodford (2003), §3, eq. (3.1), p. 205: Proposition 3.5's NKPC `NKPC.NKPCurve` is the
`d = 0` case of the delayed system (3.2) of `Delays` (for an adapted gap). -/
theorem nkpc_iff_delayed_zero {κ β : ℝ} {π gap : ℕ → Ω → ℝ} (hga : 𝔼.Adapted gap) :
    NKPC.NKPCurve 𝔼 β κ π gap ↔ Delays.DelayedNKPC 𝔼 κ β 0 π gap := by
  unfold NKPC.NKPCurve Delays.DelayedNKPC
  simp only [add_zero, hga _]

/-! ### Sticky wages: the flexible-wage limit is (2.13) with (1.37) -/

/-- Woodford (2003), p. 226 (**the flexible-wage limit of (4.15) is the NKPC slope (2.13) with
`ζ` of (1.37)**): with `ω = ω_w + ω_p`, the limit `ξ_p(σ⁻¹ + ω)` of `StickyWages` equals
`QuadraticRoots.kappa α_p β ζ` with `ζ = StrategicComplementarity.zetaGen θ_p 0 ω_p (ω_w + σ⁻¹)`
(eq. (1.37)). -/
theorem flexible_wages_slope_eq_kappa (αp β ωw ωp θp σi : ℝ) :
    QuadraticRoots.calvoXi αp β (ωp * θp) * (σi + (ωw + ωp)) =
      QuadraticRoots.kappa αp β (StrategicComplementarity.zetaGen θp 0 ωp (ωw + σi)) := by
  rw [StickyWages.kappaBar_flexible_wages_eq, StrategicComplementarity.zeta_1_37,
    QuadraticRoots.kappa]
  ring

end Woodford.NominalRigidities.Links
