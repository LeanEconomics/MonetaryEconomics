/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.Invertibility

/-!
# The permanent–transitory surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 2, §2.4,
eqs. (2.27)–(2.34), pp. 607–611.

The surplus is the sum of a persistent and a transitory AR(1),
`s_t = z_t + x_t`, `z_t = η_z z_{t−1} + ε_{z,t}`, `x_t = η_x x_{t−1} + ε_{x,t}`. Letting long-run
policy respond to transitory shocks as in (2.31), `a(ρ) = β_s` and `Δπ = −β_s ε_s`; with
`β_s = 0` all debt is repaid, the univariate surplus process is a non-invertible ARMA(2,1), an
autoregression recovers the wrong (invertible) representation (2.33), while the VAR in surplus and
debt (2.34) recovers the structural shocks — and has a *positive* coefficient of surplus on lagged
debt although surpluses are exogenous.

## Main results

* `pt_forecast`, `pt_revision`: `E_t s_{t+k} = η_zᵏz_t + η_xᵏx_t`,
  `Δ_{t+1}s_{t+1+j} = η_zʲε_{z,t+1} + η_xʲε_{x,t+1}`; `pt_pv_revision` (2.30).
* `pt_eps_s`, `pt_inflation_eq`, `pt_eps_z_zero`, `pt_no_inflation` ((2.31) and the lines after it):
  `ε_s = ρ(η_z − η_x)ε_x/D`, the present-value revision is `β_s ε_s` (so `Δπ = −β_sε_s`),
  `β_s = 1/(1 − ρη_x)` gives `ε_z = 0`.
* `ptCoeff`, `pt_coeff_zero`, `pt_revision_eps_s`, `pt_aRho` ("you can quickly verify
  `a(ρ) = β_s`").
* `pt_arma21_coeffs`, `pt_arma21_time`, `pt_theta_zero` (ARMA(2,1) form and (2.32)).
* `ar2ma1Coeff`, `ar2ma1_genFn`, `pt_fitted_aRho`, `pt_fit_ar1` ((2.33), the `ρ = η_z` case,
  fitted `a(ρ) = (1 − ρ²)/((1 − η_xρ)(1 − η_zρ))`); `pt_coeff_eq_ar2ma1`.
* `pt_wold` ((2.32)–(2.33) in the Hilbert space: with `β_s = 0` the autoregression's innovation
  `w` gives `(1 − η_xL)(1 − η_zL)s = (1 − ρL)w`; the structural shock is not recoverable from the
  surplus history), `pt_wold_ar1` (with `ρ = η_z`: `s_t − η_xs_{t−1} = w_t`, "exactly the wrong
  AR(1)").
* `pt_value` (corrected (p. 611), survey E16: `v_t = E_t∑_{j≥0}ρʲs_{t+j}`), `pt_value_printed`,
  `pt_value_printed_eq`, `printed_value_ne`; `pt_var` (2.34), `pt_var_tr_det`,
  `pt_coeff_pos` (positive surplus-on-debt coefficient), `pt_debt_coeff_gt_one`,
  `pt_shocks_recoverable`, `printed_value_var_fails` (E16: the printed `v` does not obey (2.34)).
-/

namespace Cochrane.DebtDeficitsInflation.PermanentTransitory

open Filter Topology VARIdentities Invertibility
open Cochrane.DebtDeficitsInflation.Innovations (gen IsMDSNat innov innov_apply)
open scoped Matrix

variable {Ω : Type*}

/-! ### Forecasts and revisions -/

/-- Cochrane (2023), Online Appendix eqs. (2.27)–(2.29), p. 607: `E_t s_{t+k} = η_zᵏz_t + η_xᵏx_t`
for `s = z + x`, both AR(1) with martingale-difference shocks. -/
theorem pt_forecast (𝔼 : ExpectationSystem Ω) {ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (t k : ℕ) :
    𝔼.E t (z (t + k) + x (t + k)) = ηz ^ k • z t + ηx ^ k • x t := by
  rw [map_add, 𝔼.ar1_iterate hz, 𝔼.ar1_iterate hx]

/-- Cochrane (2023), Online Appendix eqs. (2.27)–(2.29), p. 607: an AR(1) driven by
martingale-difference shocks is an `IsAR1` process. -/
theorem isAR1_of_shocks (𝔼 : ExpectationSystem Ω) {η : ℝ} {z ε : ℕ → Ω → ℝ}
    (hεm : IsMDSNat 𝔼 ε) (hzad : 𝔼.Adapted z) (hz : ∀ t, z (t + 1) = η • z t + ε (t + 1)) :
    𝔼.IsAR1 η z :=
  ⟨hzad, fun t => by rw [hz t, map_add, map_smul, hzad t, hεm.2 t, add_zero]⟩

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608: the revision of surplus forecasts,
`Δ_{t+1}s_{t+1+j} = η_zʲε_{z,t+1} + η_xʲε_{x,t+1}`. -/
theorem pt_revision (𝔼 : ExpectationSystem Ω) {ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (t j : ℕ) :
    innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) = ηz ^ j • εz (t + 1) + ηx ^ j • εx (t + 1) := by
  have hzA := isAR1_of_shocks 𝔼 hεz hzad hz
  have hxA := isAR1_of_shocks 𝔼 hεx hxad hx
  rw [innov_apply, pt_forecast 𝔼 hzA hxA (t + 1) j,
    show t + 1 + j = t + (j + 1) by omega, pt_forecast 𝔼 hzA hxA t (j + 1), hz t, hx t]
  simp only [pow_succ, smul_add, smul_smul]
  abel

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608: the news in the present value of
surpluses, `Δ_{t+1}∑ρʲs_{t+1+j} = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)` (so, in the constant-discount
short-debt model, `Δπ_{t+1}` is minus this). -/
theorem pt_pv_revision (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) w)
      (εz (t + 1) w / (1 - ρ * ηz) + εx (t + 1) w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (εz (t + 1) w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (εx (t + 1) w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [pt_revision 𝔼 hεz hεx hzad hxad hz hx t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-! ### The policy response (2.31), `a(ρ) = β_s` -/

/-- Cochrane (2023), Online Appendix eq. (2.31), p. 608: the response of long-run policy to the
transitory shock, `ε_z = −k ε_x` with
`k = [1 − (1 − ρη_x)β_s](1 − ρη_z)/([1 − (1 − ρη_z)β_s](1 − ρη_x))`. -/
noncomputable def kcoef (ρ ηx ηz βs : ℝ) : ℝ :=
  (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx))

/-- Cochrane (2023), Online Appendix p. 608: the surplus innovation
`ε_s = ε_z + ε_x = ρ(η_z − η_x)ε_x/([1 − (1 − ρη_z)β_s](1 − ρη_x))`. -/
theorem pt_eps_s {ρ ηx ηz βs : ℝ} (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (hD2 : 1 - ρ * ηx ≠ 0)
    (ex : ℝ) :
    -kcoef ρ ηx ηz βs * ex + ex =
      ρ * (ηz - ηx) / ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx)) * ex := by
  rw [kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("the inflation innovation is `ΔE_{t+1}π_{t+1} =
−β_sε_{s,t+1}`"): under (2.31) the present-value revision (2.30) equals `β_s ε_s`. -/
theorem pt_inflation_eq {ρ ηx ηz βs : ℝ} (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0)
    (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) (ex : ℝ) :
    (-kcoef ρ ηx ηz βs * ex) / (1 - ρ * ηz) + ex / (1 - ρ * ηx) =
      βs * (-kcoef ρ ηx ηz βs * ex + ex) := by
  rw [kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("for `β_s = 1/(1 − ρη_x)`, we have `ε_{z,t} = 0`"):
then there is no long-run tax response and the model reduces to the AR(1). -/
theorem pt_eps_z_zero {ρ ηx ηz : ℝ} (hx1 : 1 - ρ * ηx ≠ 0) :
    kcoef ρ ηx ηz (1 / (1 - ρ * ηx)) = 0 := by
  rw [kcoef]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("for `β_s = 0`, the government fully pays back
debts, and there is no inflation"): with `β_s = 0` the present-value revision is zero. -/
theorem pt_no_inflation {ρ ηx ηz : ℝ} (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) (ex : ℝ) :
    (-kcoef ρ ηx ηz 0 * ex) / (1 - ρ * ηz) + ex / (1 - ρ * ηx) = 0 := by
  rw [pt_inflation_eq (by simp) hz1 hx1, zero_mul]

/-- Cochrane (2023), Online Appendix p. 608: the moving-average coefficients of the surplus on
`ε_s`, `a_j = (D η_xʲ − N η_zʲ)/(ρ(η_z − η_x))` with `D = [1 − (1 − ρη_z)β_s](1 − ρη_x)` and
`N = [1 − (1 − ρη_x)β_s](1 − ρη_z)` (the difference of two AR(1)s). -/
noncomputable def ptCoeff (ρ ηx ηz βs : ℝ) (j : ℕ) : ℝ :=
  ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) * ηx ^ j -
    (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) * ηz ^ j) / (ρ * (ηz - ηx))

/-- Cochrane (2023), Online Appendix p. 608: the impact coefficient is one, `a₀ = 1`. -/
theorem pt_coeff_zero {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) : ptCoeff ρ ηx ηz βs 0 = 1 := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  rw [ptCoeff]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 608: under (2.31) the surplus responds to its own
innovation `ε_s = ε_z + ε_x` with the coefficients `ptCoeff`,
`Δ_{t+1}s_{t+1+j} = a_j ε_{s,t+1}`. -/
theorem pt_revision_eps_s (𝔼 : ExpectationSystem Ω) {ρ ηz ηx βs : ℝ} (hρ : ρ ≠ 0)
    (hne : ηz ≠ ηx) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hpol : ∀ t, εz t = -kcoef ρ ηx ηz βs • εx t) (t j : ℕ) :
    innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) =
      ptCoeff ρ ηx ηz βs j • (εz (t + 1) + εx (t + 1)) := by
  rw [pt_revision 𝔼 hεz hεx hzad hxad hz hx t j, hpol (t + 1)]
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ptCoeff, kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("you can quickly verify `a(ρ) = β_s`"). -/
theorem pt_aRho {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1)
    (hρx : |ρ * ηx| < 1) : gen (ptCoeff ρ ηx ηz βs) ρ = βs := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hgx := (hasSum_geometric_of_abs_lt_one hρx).mul_left
    ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) / (ρ * (ηz - ηx)))
  have hgz := (hasSum_geometric_of_abs_lt_one hρz).mul_left
    ((1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / (ρ * (ηz - ηx)))
  have hs := hgx.sub hgz
  rw [gen, (hs.congr_fun fun j => ?_).tsum_eq]
  · field_simp
    ring
  · simp only [ptCoeff, mul_pow]
    field_simp

/-! ### The ARMA(2,1) form (2.32) -/

/-- Cochrane (2023), Online Appendix p. 609: the MA coefficient of the condensed ARMA(2,1),
`θ = [1 − β_s(1 − ρη_x)(1 − ρη_z)]/ρ`. -/
noncomputable def ptTheta (ρ ηx ηz βs : ℝ) : ℝ := (1 - βs * (1 - ρ * ηx) * (1 - ρ * ηz)) / ρ

/-- Cochrane (2023), Online Appendix p. 609 ("we can also condense the surplus process into a
single lag operator"): the coefficients satisfy
`(1 − η_xL)(1 − η_zL)a(L) = 1 − θL`, i.e. `a₀ = 1`, `a₁ − (η_x + η_z)a₀ = −θ`,
`a_{k+2} − (η_x + η_z)a_{k+1} + η_xη_z a_k = 0`. -/
theorem pt_arma21_coeffs {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) :
    ptCoeff ρ ηx ηz βs 0 = 1 ∧
    ptCoeff ρ ηx ηz βs 1 - (ηx + ηz) * ptCoeff ρ ηx ηz βs 0 = -ptTheta ρ ηx ηz βs ∧
    ∀ k, ptCoeff ρ ηx ηz βs (k + 2) - (ηx + ηz) * ptCoeff ρ ηx ηz βs (k + 1) -
      (-(ηx * ηz)) * ptCoeff ρ ηx ηz βs k = 0 := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨pt_coeff_zero hρ hne, ?_, fun k => ?_⟩
  · simp only [ptCoeff, ptTheta]
    field_simp
    ring
  · simp only [ptCoeff]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 609, in the time domain: under (2.31) at every date,
`s_{t+2} − (η_x + η_z)s_{t+1} + η_xη_z s_t = ε_{s,t+2} − θ ε_{s,t+1}`. -/
theorem pt_arma21_time {ρ ηz ηx βs : ℝ} (hρ : ρ ≠ 0) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0)
    (hx1 : 1 - ρ * ηx ≠ 0) {z x εz εx : ℕ → Ω → ℝ}
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hpol : ∀ t, εz t = -kcoef ρ ηx ηz βs • εx t) (t : ℕ) :
    (z (t + 2) + x (t + 2)) - (ηx + ηz) • (z (t + 1) + x (t + 1)) + (ηx * ηz) • (z t + x t) =
      (εz (t + 2) + εx (t + 2)) - ptTheta ρ ηx ηz βs • (εz (t + 1) + εx (t + 1)) := by
  funext w
  have h1 := congrFun (hz (t + 1)) w
  have h2 := congrFun (hz t) w
  have h3 := congrFun (hx (t + 1)) w
  have h4 := congrFun (hx t) w
  have h5 := congrFun (hpol (t + 1)) w
  have h6 := congrFun (hpol (t + 2)) w
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    neg_mul] at h1 h2 h3 h4 h5 h6 ⊢
  rw [h1, h2, h3, h4, h6, h5]
  rw [kcoef, ptTheta]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix eq. (2.32), p. 609: with `β_s = 0` the MA numerator is
`1 − ρ⁻¹L`. -/
theorem pt_theta_zero (ρ ηx ηz : ℝ) : ptTheta ρ ηx ηz 0 = ρ⁻¹ := by
  simp [ptTheta]

/-! ### The fitted representation (2.33) -/

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609 (tool): the impulse response of the AR(2)
`1/((1 − η_xL)(1 − η_zL))`, `h_j = (η_z^{j+1} − η_x^{j+1})/(η_z − η_x)`. -/
noncomputable def ar2Impulse (ηx ηz : ℝ) (j : ℕ) : ℝ := (ηz ^ (j + 1) - ηx ^ (j + 1)) / (ηz - ηx)

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609: the MA coefficients of
`(1 − θL)/((1 − η_xL)(1 − η_zL))`. -/
noncomputable def ar2ma1Coeff (ηx ηz θ : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => ar2Impulse ηx ηz (j + 1) - θ * ar2Impulse ηx ηz j

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609: `a(ρ) = (1 − θρ)/((1 − η_xρ)(1 − η_zρ))`
for the ARMA(2,1) `(1 − θL)/((1 − η_xL)(1 − η_zL))`. -/
theorem ar2ma1_genFn {ηx ηz θ ρ : ℝ} (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1)
    (hρx : |ρ * ηx| < 1) :
    gen (ar2ma1Coeff ηx ηz θ) ρ = (1 - θ * ρ) / ((1 - ηx * ρ) * (1 - ηz * ρ)) := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hz1' : 1 - ηz * ρ ≠ 0 := by rwa [mul_comm]
  have hx1' : 1 - ηx * ρ ≠ 0 := by rwa [mul_comm]
  have hH : HasSum (fun j => ar2Impulse ηx ηz j * ρ ^ j)
      (1 / ((1 - ηx * ρ) * (1 - ηz * ρ))) := by
    have hgz := (hasSum_geometric_of_abs_lt_one hρz).mul_left (ηz / (ηz - ηx))
    have hgx := (hasSum_geometric_of_abs_lt_one hρx).mul_left (ηx / (ηz - ηx))
    convert hgz.sub hgx using 1
    · funext j
      simp only [ar2Impulse, mul_pow, pow_succ]
      field_simp
    · field_simp
      ring
  have hfirst : HasSum (fun j => ar2ma1Coeff ηx ηz θ (j + 1) * ρ ^ (j + 1))
      (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)) - 1 - θ * ρ * (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)))) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hH
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at h1
    have h0 : ar2Impulse ηx ηz 0 = 1 := by simp [ar2Impulse, div_self h]
    rw [h0] at h1
    refine (h1.sub (hH.mul_left (θ * ρ))).congr_fun fun j => ?_
    simp only [ar2ma1Coeff, pow_succ]
    ring
  have hall : HasSum (fun j => ar2ma1Coeff ηx ηz θ j * ρ ^ j)
      (1 + (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)) - 1 -
        θ * ρ * (1 / ((1 - ηx * ρ) * (1 - ηz * ρ))))) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [ar2ma1Coeff] using hfirst
  rw [gen, hall.tsum_eq]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 610 ("you measure `a(ρ) = (1 − ρ²)/((1 − η_xρ)(1 − η_zρ))`,
not the correct answer `a(ρ) = 0`"): the fitted (2.33), numerator `1 − ρL`. -/
theorem pt_fitted_aRho {ηx ηz ρ : ℝ} (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) :
    gen (ar2ma1Coeff ηx ηz ρ) ρ = (1 - ρ ^ 2) / ((1 - ηx * ρ) * (1 - ηz * ρ)) := by
  rw [ar2ma1_genFn hne hρz hρx, sq]

/-- Cochrane (2023), Online Appendix pp. 609–610 ("in the not-unreasonable case `ρ = η_z`, you
recover exactly the wrong AR(1) response function with coefficient `η_x`"): the coefficients of
`(1 − η_zL)/((1 − η_xL)(1 − η_zL))` are `η_xʲ`. -/
theorem pt_fit_ar1 {ηx ηz : ℝ} (hne : ηz ≠ ηx) (j : ℕ) : ar2ma1Coeff ηx ηz ηz j = ηx ^ j := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  cases j with
  | zero => rfl
  | succ j =>
    simp only [ar2ma1Coeff, ar2Impulse]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 609: the surplus MA coefficients `ptCoeff` are those of
the ARMA(2,1) `(1 − θL)/((1 − η_xL)(1 − η_zL))` with `θ = ptTheta`. -/
theorem pt_coeff_eq_ar2ma1 {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) (j : ℕ) :
    ptCoeff ρ ηx ηz βs j = ar2ma1Coeff ηx ηz (ptTheta ρ ηx ηz βs) j := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  cases j with
  | zero => rw [pt_coeff_zero hρ hne]; rfl
  | succ j =>
    simp only [ptCoeff, ar2ma1Coeff, ar2Impulse, ptTheta]
    field_simp
    ring


/-! ### The Wold representation fitted by an autoregression (2.32)–(2.33) -/

namespace HilbertPT

open Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Cochrane (2023), Online Appendix p. 609 (tool): the surplus coefficients are absolutely
summable when `|η_x|, |η_z| < 1`. -/
theorem summable_abs_ptCoeff {ρ ηx ηz βs : ℝ} (hηx : |ηx| < 1) (hηz : |ηz| < 1) :
    Summable (fun j => |ptCoeff ρ ηx ηz βs j|) := by
  set c1 := (1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) / (ρ * (ηz - ηx))
  set c2 := (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / (ρ * (ηz - ηx))
  have h : Summable (fun j => |c1| * |ηx| ^ j + |c2| * |ηz| ^ j) :=
    ((summable_geometric_of_lt_one (abs_nonneg _) hηx).mul_left _).add
      ((summable_geometric_of_lt_one (abs_nonneg _) hηz).mul_left _)
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_) h
  have e : ptCoeff ρ ηx ηz βs j = c1 * ηx ^ j - c2 * ηz ^ j := by
    simp only [ptCoeff, c1, c2]; ring
  rw [e]
  refine (abs_sub _ _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_pow]

/-- Cochrane (2023), Online Appendix eqs. (2.32)–(2.33), pp. 609–610 ("you cannot recover this
surplus response from running autoregressions … you recover an estimated model (2.33) …
`ρ` not `ρ⁻¹` in the moving-average term, and the regression error `w_t` is not the true
shock"): with `β_s = 0` (all debt repaid), `0 < ρ < 1`, `|η_x|, |η_z| < 1`, `η_z ≠ η_x`, the
Wold innovation `w` of the surplus gives
`s_t − (η_x + η_z)s_{t−1} + η_xη_z s_{t−2} = w_t − ρw_{t−1}`, `s_t − w_t` is the projection of
`s_t` on its past, `w` has variance `σ²/ρ²`, and the structural shock `e_t` is not in the closed
span of current and past surpluses. -/
theorem pt_wold {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ ηx ηz : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hηx : |ηx| < 1) (hηz : |ηz| < 1) (hne : ηz ≠ ηx) (t : ℤ) :
    maProc (ptCoeff ρ ηx ηz 0) e t - (ηx + ηz) • maProc (ptCoeff ρ ηx ηz 0) e (t - 1) +
        (ηx * ηz) • maProc (ptCoeff ρ ηx ηz 0) e (t - 1 - 1) =
      woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t - ρ • woldInnov ρ⁻¹ (maOne ρ⁻¹ e) (t - 1) ∧
    (haveI : (pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) (t - 1)).starProjection
        (maProc (ptCoeff ρ ηx ηz 0) e t)) =
      maProc (ptCoeff ρ ηx ηz 0) e t - woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t ∧
    ⟪woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t, woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t⟫ = σ2 / ρ ^ 2 ∧
    e t ∉ pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) t := by
  set a := ptCoeff ρ ηx ηz 0 with ha_def
  have hρne : ρ ≠ 0 := hρ0.ne'
  have ha := summable_abs_ptCoeff (ρ := ρ) (βs := 0) hηx hηz
  have hθ : 1 < |ρ⁻¹| := by
    rw [abs_inv, abs_of_pos hρ0]; exact one_lt_inv₀ hρ0 |>.mpr hρ1
  have hρz : |ρ * ηz| < 1 := by
    rw [abs_mul, abs_of_pos hρ0]; nlinarith [abs_nonneg ηz]
  have hρx : |ρ * ηx| < 1 := by
    rw [abs_mul, abs_of_pos hρ0]; nlinarith [abs_nonneg ηx]
  have hroot : gen a ρ⁻¹⁻¹ = 0 := by rw [inv_inv, ha_def, pt_aRho hρne hne hρz hρx]
  obtain ⟨hc0, hc1, hc2⟩ := pt_arma21_coeffs (βs := 0) hρne hne
  rw [pt_theta_zero] at hc1
  have hfilt : ∀ τ, maProc a e τ - (ηx + ηz) • maProc a e (τ - 1) -
      (-(ηx * ηz)) • maProc a e (τ - 1 - 1) = maOne ρ⁻¹ e τ := fun τ =>
    ar2_filter_eq_maOne he ha hc0 hc1 hc2 τ
  have hm : ∀ τ, maOne ρ⁻¹ e τ - maProc a e τ ∈ pastSpan (maProc a e) (τ - 1) := by
    intro τ
    rw [← hfilt τ, show maProc a e τ - (ηx + ηz) • maProc a e (τ - 1) -
      (-(ηx * ηz)) • maProc a e (τ - 1 - 1) - maProc a e τ =
      -((ηx + ηz) • maProc a e (τ - 1)) + (ηx * ηz) • maProc a e (τ - 1 - 1) by
        rw [neg_smul]; abel]
    refine Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · simpa using mem_pastSpan_self (maProc a e) (τ - 1) 0
    · simpa using mem_pastSpan_self (maProc a e) (τ - 1) 1
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ := wold_innovation he hσ hθ ha hc0 hroot hm t
  refine ⟨?_, hproj, ?_, hnot⟩
  · rw [inv_inv] at hrec
    rw [← hrec, ← hfilt t, neg_smul, sub_neg_eq_add]
  · rw [hnorm, inv_pow]
    field_simp

/-- Cochrane (2023), Online Appendix pp. 609–610 ("in the not-unreasonable case `ρ = η_z`, you
recover exactly the wrong AR(1) response function with coefficient `η_x` … as if the taxes were
not there at all"): with `β_s = 0` and `η_z = ρ`, the surplus satisfies `s_t − η_xs_{t−1} = w_t`,
an AR(1) in its own Wold innovation. -/
theorem pt_wold_ar1 {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ ηx : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hηx : |ηx| < 1) (hne : ρ ≠ ηx) (t : ℤ) :
    maProc (ptCoeff ρ ηx ρ 0) e t - ηx • maProc (ptCoeff ρ ηx ρ 0) e (t - 1) =
      woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t := by
  have hηz : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  set s := maProc (ptCoeff ρ ηx ρ 0) e with hs
  set w := woldInnov ρ⁻¹ (maOne ρ⁻¹ e) with hw
  set y : ℤ → H := fun τ => s τ - ηx • s (τ - 1) - w τ with hy
  have hrel : ∀ τ, y τ = ρ • y (τ - 1) := by
    intro τ
    have h := (pt_wold he hσ hρ0 hρ1 hηx hηz hne τ).1
    simp only [hy]
    rw [show τ - 1 - 1 = τ - 1 - 1 by rfl] at h
    have : s τ - ηx • s (τ - 1) - w τ - ρ • (s (τ - 1) - ηx • s (τ - 1 - 1) - w (τ - 1)) =
        (s τ - (ηx + ρ) • s (τ - 1) + (ηx * ρ) • s (τ - 1 - 1)) -
          (w τ - ρ • w (τ - 1)) := by
      simp only [add_smul, mul_smul, smul_sub]
      rw [smul_comm ρ ηx]
      abel
    rw [← sub_eq_zero, this, h, sub_self]
  -- bounds
  have ha := summable_abs_ptCoeff (ρ := ρ) (βs := 0) hηx hηz
  set B1 := (∑' k, |ptCoeff ρ ηx ρ 0 k|) * ‖e 0‖
  have hsb : ∀ τ, ‖s τ‖ ≤ B1 := by
    intro τ
    have hk : ∀ k : ℕ, ‖ptCoeff ρ ηx ρ 0 k • e (τ - k)‖ = |ptCoeff ρ ηx ρ 0 k| * ‖e 0‖ :=
      fun k => by rw [norm_smul, Real.norm_eq_abs, he.norm_eq (τ - k)]
    have hn : Summable (fun k : ℕ => ‖ptCoeff ρ ηx ρ 0 k • e (τ - k)‖) :=
      (ha.mul_right ‖e 0‖).congr fun k => (hk k).symm
    refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq ?_)
    simp_rw [hk]
    exact tsum_mul_right
  have hwb : ∀ τ, ‖w τ‖ = ‖w 0‖ := by
    intro τ
    have h1 := (pt_wold he hσ hρ0 hρ1 hηx hηz hne τ).2.2.1
    have h2 := (pt_wold he hσ hρ0 hρ1 hηx hηz hne 0).2.2.1
    rw [real_inner_self_eq_norm_sq] at h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)
  set B := B1 + |ηx| * B1 + ‖w 0‖
  have hyb : ∀ τ, ‖y τ‖ ≤ B := by
    intro τ
    calc ‖y τ‖ ≤ ‖s τ‖ + ‖ηx • s (τ - 1)‖ + ‖w τ‖ := by
          simp only [hy]
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ B1 + |ηx| * B1 + ‖w 0‖ := by
          rw [norm_smul, Real.norm_eq_abs, hwb τ]
          gcongr
          · exact hsb τ
          · exact hsb _
  have hiter : ∀ n : ℕ, y t = ρ ^ n • y (t - n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, hrel (t - n), smul_smul, ← pow_succ]
      congr 2
      push_cast
      ring
  have hle : ∀ n : ℕ, ‖y t‖ ≤ ρ ^ n * B := by
    intro n
    rw [hiter n, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hρ0]
    exact mul_le_mul_of_nonneg_left (hyb _) (pow_nonneg hρ0.le _)
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const B
  have h0 : ‖y t‖ ≤ 0 := ge_of_tendsto' hlim hle
  have : y t = 0 := norm_le_zero_iff.mp h0
  simp only [hy] at this
  exact sub_eq_zero.mp this

end HilbertPT

/-! ### The value of debt and the VAR (2.34) -/

/-- Cochrane (2023), Online Appendix p. 611 (corrected, survey E16): the value of debt
`v_t = E_t∑_{j≥0}ρʲs_{t+j} = z_t/(1 − ρη_z) + x_t/(1 − ρη_x)` (the current surplus included). -/
theorem pt_value (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (z (t + j) + x (t + j)) w)
      (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (z t w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (x t w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [pt_forecast 𝔼 hz hx t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the printed sum
`E_t∑_{j≥1}ρ^{j−1}s_{t+j}` equals `η_zz_t/(1 − ρη_z) + η_xx_t/(1 − ρη_x)`, not the printed
`z_t/(1 − ρη_z) + x_t/(1 − ρη_x)`. -/
theorem pt_value_printed (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (z (t + 1 + j) + x (t + 1 + j)) w)
      (ηz * z t w / (1 - ρ * ηz) + ηx * x t w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (ηz * z t w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (ηx * x t w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [show t + 1 + j = t + (j + 1) by omega, pt_forecast 𝔼 hz hx t (j + 1)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the printed-index value is
`(v_t − s_t)/ρ`. -/
theorem pt_value_printed_eq {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0)
    (hx1 : 1 - ρ * ηx ≠ 0) (zt xt : ℝ) :
    ηz * zt / (1 - ρ * ηz) + ηx * xt / (1 - ρ * ηx) =
      ((zt / (1 - ρ * ηz) + xt / (1 - ρ * ηx)) - (zt + xt)) / ρ := by
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hZ : (1 - ρ * ηz) * (zt / (1 - ρ * ηz)) = zt := mul_div_cancel₀ zt hz1
  have hX : (1 - ρ * ηx) * (xt / (1 - ρ * ηx)) = xt := mul_div_cancel₀ xt hx1
  linear_combination (-ρ⁻¹) * hZ + (-ρ⁻¹) * hX -
    (ηz * (zt / (1 - ρ * ηz)) + ηx * (xt / (1 - ρ * ηx))) * hr

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the two definitions really differ —
at `z_t = 1`, `x_t = 0` they are `1/(1 − ρη_z)` and `η_z/(1 − ρη_z)`, unequal unless `η_z = 1`. -/
theorem printed_value_ne {ρ ηz : ℝ} (hz1 : 1 - ρ * ηz ≠ 0) (hηz : ηz ≠ 1) :
    1 / (1 - ρ * ηz) ≠ ηz / (1 - ρ * ηz) := by
  intro h
  rw [div_eq_div_iff hz1 hz1] at h
  exact hηz (mul_right_cancel₀ hz1 h).symm

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611: with `v = z/(1 − ρη_z) + x/(1 − ρη_x)`,
`s = z + x`, the surplus and debt follow the VAR
`s_t = (η_x + η_z − ρ⁻¹)s_{t−1} + ρ⁻¹(1 − ρη_x)(1 − ρη_z)v_{t−1} + ε_{s,t}`,
`v_t = −ρ⁻¹s_{t−1} + ρ⁻¹v_{t−1} + ε_{v,t}`, with `ε_s = ε_z + ε_x`,
`ε_v = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)`. -/
theorem pt_var {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    (z0 x0 ez ex : ℝ) :
    (ηz * z0 + ez) + (ηx * x0 + ex) =
        (ηx + ηz - ρ⁻¹) * (z0 + x0) + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) *
          (z0 / (1 - ρ * ηz) + x0 / (1 - ρ * ηx)) + (ez + ex) ∧
    (ηz * z0 + ez) / (1 - ρ * ηz) + (ηx * x0 + ex) / (1 - ρ * ηx) =
        -ρ⁻¹ * (z0 + x0) + ρ⁻¹ * (z0 / (1 - ρ * ηz) + x0 / (1 - ρ * ηx)) +
          (ez / (1 - ρ * ηz) + ex / (1 - ρ * ηx)) := by
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hZ : (1 - ρ * ηz) * (z0 / (1 - ρ * ηz)) = z0 := mul_div_cancel₀ z0 hz1
  have hX : (1 - ρ * ηx) * (x0 / (1 - ρ * ηx)) = x0 := mul_div_cancel₀ x0 hx1
  constructor
  · linear_combination (ηx * z0 + ηz * x0) * hr - ρ⁻¹ * (1 - ρ * ηx) * hZ -
      ρ⁻¹ * (1 - ρ * ηz) * hX
  · linear_combination (-ρ⁻¹) * hZ + (-ρ⁻¹) * hX -
      (ηz * (z0 / (1 - ρ * ηz)) + ηx * (x0 / (1 - ρ * ηx))) * hr

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611, for the model's processes: if
`z_{t+1} = η_z z_t + ε_{z,t+1}`, `x_{t+1} = η_x x_t + ε_{x,t+1}`, then `(s, v)` obey the VAR (2.34)
at every date and state. -/
theorem pt_var_process {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    {z x εz εx : ℕ → Ω → ℝ} (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1))
    (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1)) (t : ℕ) (w : Ω) :
    z (t + 1) w + x (t + 1) w =
        (ηx + ηz - ρ⁻¹) * (z t w + x t w) + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) *
          (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) + (εz (t + 1) w + εx (t + 1) w) ∧
    z (t + 1) w / (1 - ρ * ηz) + x (t + 1) w / (1 - ρ * ηx) =
        -ρ⁻¹ * (z t w + x t w) + ρ⁻¹ * (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) +
          (εz (t + 1) w / (1 - ρ * ηz) + εx (t + 1) w / (1 - ρ * ηx)) := by
  have h1 := congrFun (hz t) w
  have h2 := congrFun (hx t) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2]
  exact pt_var hρ hz1 hx1 _ _ _ _

/-- Cochrane (2023), Online Appendix p. 611 ("the construction already gives us a diagonalization
of the VAR transition matrix verifying stable eigenvalues `η_z`, `η_x`"): the (2.34) matrix has
trace `η_x + η_z` and determinant `η_xη_z`. -/
theorem pt_var_tr_det {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) :
    tr2 !![ηx + ηz - ρ⁻¹, ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz); -ρ⁻¹, ρ⁻¹] = ηx + ηz ∧
    det2 !![ηx + ηz - ρ⁻¹, ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz); -ρ⁻¹, ρ⁻¹] = ηx * ηz := by
  simp only [tr2, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · ring
  · field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 611 ("the regression coefficient of surplus `s_t` on
value `v_{t−1}` is positive"): `ρ⁻¹(1 − ρη_x)(1 − ρη_z) > 0` for `ρ > 0`, `ρη_x, ρη_z < 1` —
although surpluses are exogenous, debt Granger-causes surpluses. -/
theorem pt_coeff_pos {ρ ηz ηx : ℝ} (hρ : 0 < ρ) (hx : ρ * ηx < 1) (hz : ρ * ηz < 1) :
    0 < ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) := by
  have h1 : 0 < 1 - ρ * ηx := by linarith
  have h2 : 0 < 1 - ρ * ηz := by linarith
  positivity

/-- Cochrane (2023), Online Appendix p. 611 ("the coefficient `ρ⁻¹ > 1` of debt on lagged debt
warns us to be careful about misinterpreting individual regression coefficients for
eigenvalues"): `ρ⁻¹ > 1` for `0 < ρ < 1`, while both eigenvalues `η_z, η_x` are stable. -/
theorem pt_debt_coeff_gt_one {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 1 < ρ⁻¹ :=
  (one_lt_inv₀ hρ0).mpr hρ1

/-- Cochrane (2023), Online Appendix p. 611 ("the structural shocks `ε_{z,t}, ε_{x,t}` are
recoverable from the regression residuals"): the VAR innovations
`u_s = ε_z + ε_x`, `u_v = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)` determine the structural shocks when
`η_z ≠ η_x`. -/
theorem pt_shocks_recoverable {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx)
    (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) {ez ex us uv : ℝ} (hus : us = ez + ex)
    (huv : uv = ez / (1 - ρ * ηz) + ex / (1 - ρ * ηx)) :
    ex = (uv - us / (1 - ρ * ηz)) / (1 / (1 - ρ * ηx) - 1 / (1 - ρ * ηz)) ∧ ez = us - ex := by
  have hBA : 1 / (1 - ρ * ηx) - 1 / (1 - ρ * ηz) ≠ 0 := by
    rw [div_sub_div _ _ hx1 hz1]
    refine div_ne_zero ?_ (mul_ne_zero hx1 hz1)
    intro h
    have : ρ * (ηx - ηz) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hρ h'
    · exact hne (by linarith)
  constructor
  · rw [eq_div_iff hBA, huv, hus]
    simp only [div_eq_mul_inv]
    ring
  · rw [hus]; ring

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611, survey E16: with the printed definition
`v'_t = η_zz_t/(1 − ρη_z) + η_xx_t/(1 − ρη_x)` the VAR (2.34) fails — at `z = 1`, `x = 0` and no
shocks the next surplus is `η_z`, but (2.34) predicts
`(η_x + η_z − ρ⁻¹) + ρ⁻¹(1 − ρη_x)(1 − ρη_z)·η_z/(1 − ρη_z) = η_z + (η_x − ρ⁻¹)(1 − η_z)`. -/
theorem printed_value_var_fails {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0)
    (hηz : ηz ≠ 1) (hηx : ηx ≠ ρ⁻¹) :
    (ηx + ηz - ρ⁻¹) * 1 + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) * (ηz / (1 - ρ * ηz)) ≠ ηz := by
  intro h
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hW : (1 - ρ * ηz) * (ηz / (1 - ρ * ηz)) = ηz := mul_div_cancel₀ ηz hz1
  have key : (ηx - ρ⁻¹) * (1 - ηz) = 0 := by
    linear_combination h + ηx * ηz * hr - ρ⁻¹ * (1 - ρ * ηx) * hW
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hηx (by linarith)
  · exact hηz (by linarith)

end Cochrane.DebtDeficitsInflation.PermanentTransitory
