/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.MIUSeparable
import ClassicalMonetaryModel.Expectations
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Money in the utility function: the nonseparable example

Galí (2015), Chapter 2, §2.5.2 (pp. 34–40).

## The household

Period utility is `U(X, N) = (X^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)` with the CES composite
`X = ((1 − ϑ) C^{1−ν} + ϑ (M/P)^{1−ν})^{1/(1−ν)}` (`X = C^{1−ϑ} (M/P)^ϑ` for `ν = 1`),
`composite`, `nsUtil`, with `0 < ϑ < 1`, `σ, ν > 0`.

* `hasDerivAt_composite_path`, `hasDerivAt_nsUtil_C`, `hasDerivAt_nsUtil_m`: the marginal
  utilities `U_c = (1 − ϑ) X^{ν−σ} C^{−ν}`, `U_m = ϑ X^{ν−σ} (M/P)^{−ν}` (p. 35).
* `labour_foc_necessary` (eq. (37)), `money_foc_necessary` + `money_demand_39_iff`
  (eq. (39)), `uc_ratio` + `euler5_iff_miuEuler` (eq. (38) from (5)), all from the
  variational arguments of
  pp. 19–20 and 33. `labour_supply_nu_eq_sigma`, `miuEuler_nu_eq_sigma`: for `ν = σ`
  (37)–(38) reduce to the separable case. `moneyDemand39_homogeneous`,
  `hasFDerivAt_log_money_demand_40`: fn. 10 (unit consumption elasticity for all `ν, σ`)
  and eq. (40) as an exact derivative.
* `labour_supply_log`: the log form of (37), `w − p = σc + φn + (ν − σ)(c − x)`, exactly.

## Steady state and the coefficients `χ`, `k_m`, `ϖ`

* `hasFDerivAt_gap`: `c − x` as a function of `(c, m − p)` has derivative
  `χ (dc − d(m − p))` with `χ = share ϑ ν (m − p − c)`; at the zero-inflation steady state
  (`km_money_demand`: `M/P = k_m C`, `k_m = (ϑ/((1 − β)(1 − ϑ)))^{1/ν}`),
  `share_at_km`: `χ = k_m(1 − β)/(1 + k_m(1 − β))`, `chi1_eq_chi`: the printed first form
  equals it; `chi_mem`: `χ ∈ [0, 1)`.
* `eta_steady_state`, `varpi_eq`: `ϖ = η χ (ν − σ) = k_m β (1 − σ/ν)/(1 + k_m(1 − β))`;
  `eq41`: eq. (41).

## The log-linear equilibrium

* `eq43`: (42)–(43), `y = ψ_ya a + ψ_yi i + const`, `ψ_yi = −ϖ(1 − α)/D`;
  `psiYi_neg_iff`, `varpi_pos_iff`.
* `tendsto_psiYi_nu`, `psiYi_limit_calib`, `tendsto_calib_beta_one` and the numerical
  bounds `psiYi_limit_km_base`, `psiYi_limit_km_m2` (p. 38).
* `eq44_45`, `Theta_mem`: (44)–(45), `Θ ∈ [0, 1)`.
* `miuEuler_iff_moment`, `pf_miuEuler_iff` (exact), `hasDerivAt_log_miuMoment_family`
  (exact derivative under uncertainty), `linearisedMIUEuler_eq_zero_iff`,
  `eulerGap_iff_eulerLinear`: eqs. (46)–(47).
* `real_balance_eq_iff`, `price_level_48`, `price_level_48_exists`: eq. (48), the unique
  solution with bounded real balances, via `eq_forwardSeries`.
* `real_wage_countercyclical`, `real_wage_strictly_countercyclical`,
  `real_wage_acyclical_of_alpha_zero`: p. 39–40.
-/

namespace Gali.ClassicalMonetaryModel.MIUNonseparable

open Filter Topology

/-! ### The composite index `X` -/

/-- Galí (2015), p. 35: the composite of consumption and real balances,
`X = ((1 − ϑ) C^{1−ν} + ϑ m^{1−ν})^{1/(1−ν)}` for `ν ≠ 1` and `X = C^{1−ϑ} m^ϑ` for `ν = 1`. -/
noncomputable def composite (ϑ ν C m : ℝ) : ℝ :=
  if ν = 1 then C ^ (1 - ϑ) * m ^ ϑ
  else ((1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν)) ^ (1 / (1 - ν))

/-- Galí (2015), p. 35: the composite is positive for positive `C`, `m` and `0 < ϑ < 1`. -/
theorem composite_pos {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hC : 0 < C) (hm : 0 < m) :
    0 < composite ϑ ν C m := by
  unfold composite
  split_ifs
  · exact mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hm _)
  · exact Real.rpow_pos_of_pos (add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hC _))
      (mul_pos hϑ0 (Real.rpow_pos_of_pos hm _))) _

/-- Galí (2015), p. 35: the composite is homogeneous of degree one,
`X(λC, λm) = λ X(C, m)` for `λ > 0`. -/
theorem composite_homogeneous {ϑ ν C m l : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hC : 0 < C)
    (hm : 0 < m) (hl : 0 < l) : composite ϑ ν (l * C) (l * m) = l * composite ϑ ν C m := by
  unfold composite
  split_ifs with hν
  · rw [Real.mul_rpow hl.le hC.le, Real.mul_rpow hl.le hm.le]
    have : l ^ (1 - ϑ) * l ^ ϑ = l := by
      rw [← Real.rpow_add hl, sub_add_cancel, Real.rpow_one]
    calc l ^ (1 - ϑ) * C ^ (1 - ϑ) * (l ^ ϑ * m ^ ϑ)
        = (l ^ (1 - ϑ) * l ^ ϑ) * (C ^ (1 - ϑ) * m ^ ϑ) := by ring
      _ = l * (C ^ (1 - ϑ) * m ^ ϑ) := by rw [this]
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hS : 0 < (1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν) :=
      add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hC _))
        (mul_pos hϑ0 (Real.rpow_pos_of_pos hm _))
    rw [Real.mul_rpow hl.le hC.le, Real.mul_rpow hl.le hm.le]
    have e : (1 - ϑ) * (l ^ (1 - ν) * C ^ (1 - ν)) + ϑ * (l ^ (1 - ν) * m ^ (1 - ν))
        = l ^ (1 - ν) * ((1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν)) := by ring
    rw [e, Real.mul_rpow (Real.rpow_pos_of_pos hl _).le hS.le, ← Real.rpow_mul hl.le,
      mul_one_div_cancel hs, Real.rpow_one]

/-- Galí (2015), p. 35: derivative of the composite along a differentiable path
`y ↦ (c y, q y)` of consumption and real balances:
`dX = X^ν ((1 − ϑ) C^{−ν} dC + ϑ m^{−ν} dm)`. -/
theorem hasDerivAt_composite_path {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) {c q : ℝ → ℝ}
    {c' q' x : ℝ} (hc : HasDerivAt c c' x) (hq : HasDerivAt q q' x) (hcx : 0 < c x)
    (hqx : 0 < q x) :
    HasDerivAt (fun y => composite ϑ ν (c y) (q y))
      (composite ϑ ν (c x) (q x) ^ ν * ((1 - ϑ) * c x ^ (-ν) * c' + ϑ * q x ^ (-ν) * q')) x := by
  by_cases hν : ν = 1
  · subst hν
    have hfun : (fun y => composite ϑ 1 (c y) (q y)) = fun y => c y ^ (1 - ϑ) * q y ^ ϑ := by
      funext y
      simp [composite]
    rw [hfun]
    have h1 := hc.rpow_const (p := 1 - ϑ) (Or.inl hcx.ne')
    have h2 := hq.rpow_const (p := ϑ) (Or.inl hqx.ne')
    refine (h1.mul h2).congr_deriv ?_
    simp only [composite, ↓reduceIte, Real.rpow_one]
    rw [show (1 : ℝ) - ϑ - 1 = (1 - ϑ) + (-1) by ring, show ϑ - 1 = ϑ + (-1) by ring,
      Real.rpow_add hcx, Real.rpow_add hqx]
    ring
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hfun : (fun y => composite ϑ ν (c y) (q y))
        = fun y => ((1 - ϑ) * c y ^ (1 - ν) + ϑ * q y ^ (1 - ν)) ^ (1 / (1 - ν)) := by
      funext y
      simp [composite, hν]
    have hSpos : 0 < (1 - ϑ) * c x ^ (1 - ν) + ϑ * q x ^ (1 - ν) :=
      add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hcx _))
        (mul_pos hϑ0 (Real.rpow_pos_of_pos hqx _))
    have hSd := ((hc.rpow_const (p := 1 - ν) (Or.inl hcx.ne')).const_mul (1 - ϑ)).add
      ((hq.rpow_const (p := 1 - ν) (Or.inl hqx.ne')).const_mul ϑ)
    rw [hfun]
    refine (hSd.rpow_const (p := 1 / (1 - ν)) (Or.inl hSpos.ne')).congr_deriv ?_
    have hX : composite ϑ ν (c x) (q x)
        = ((1 - ϑ) * c x ^ (1 - ν) + ϑ * q x ^ (1 - ν)) ^ (1 / (1 - ν)) := by
      simp [composite, hν]
    simp only [Pi.add_apply]
    rw [hX, ← Real.rpow_mul hSpos.le, show 1 / (1 - ν) - 1 = 1 / (1 - ν) * ν by field_simp; ring,
      show (1 : ℝ) - ν - 1 = -ν by ring]
    field_simp

/-! ### Utility and marginal utilities -/

/-- Galí (2015), p. 34: period utility `U(X, N) = (X^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)`
(log branch for `σ = 1`), as a function of consumption `C`, real balances `m` and hours. -/
noncomputable def nsUtil (σ φ ϑ ν C m N : ℝ) : ℝ :=
  MIUSeparable.utilPow σ (composite ϑ ν C m) - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 35: derivative of utility along a path of `(C, m)` with hours fixed:
`X^{ν−σ}((1 − ϑ) C^{−ν} dC + ϑ m^{−ν} dm)`. -/
theorem hasDerivAt_nsUtil_path (σ φ N : ℝ) {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    {c q : ℝ → ℝ} {c' q' x : ℝ} (hc : HasDerivAt c c' x) (hq : HasDerivAt q q' x)
    (hcx : 0 < c x) (hqx : 0 < q x) :
    HasDerivAt (fun y => nsUtil σ φ ϑ ν (c y) (q y) N)
      (composite ϑ ν (c x) (q x) ^ (ν - σ) *
        ((1 - ϑ) * c x ^ (-ν) * c' + ϑ * q x ^ (-ν) * q')) x := by
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hcx hqx
  have h := ((MIUSeparable.hasDerivAt_utilPow σ hX).comp x
    (hasDerivAt_composite_path hϑ0 hϑ1 hc hq hcx hqx)).sub_const (N ^ (1 + φ) / (1 + φ))
  refine h.congr_deriv ?_
  rw [show ν - σ = -σ + ν by ring, Real.rpow_add hX]
  ring

/-- Galí (2015), p. 35: the marginal utility of consumption `U_c = (1 − ϑ) X^{ν−σ} C^{−ν}`. -/
theorem hasDerivAt_nsUtil_C (σ φ N : ℝ) {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun C' => nsUtil σ φ ϑ ν C' m N)
      ((1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν)) C := by
  have := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 (hasDerivAt_id C)
    (hasDerivAt_const C m) hC hm
  refine this.congr_deriv ?_
  simp only [id]
  ring

/-- Galí (2015), p. 35: the marginal utility of real balances `U_m = ϑ X^{ν−σ} m^{−ν}`. -/
theorem hasDerivAt_nsUtil_m (σ φ N : ℝ) {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun m' => nsUtil σ φ ϑ ν C m' N)
      (ϑ * composite ϑ ν C m ^ (ν - σ) * m ^ (-ν)) m := by
  have := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 (hasDerivAt_const m C)
    (hasDerivAt_id m) hC hm
  refine this.congr_deriv ?_
  simp only [id]
  ring

/-- Galí (2015), p. 35: the marginal rate of substitution between real balances and
consumption, `U_m / U_c = (ϑ/(1 − ϑ)) (m/C)^{−ν}`. -/
theorem um_div_uc {ϑ ν σ C m X : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hm : 0 < m) (hX : 0 < X) :
    ϑ * X ^ (ν - σ) * m ^ (-ν) / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν))
      = ϑ / (1 - ϑ) * (m / C) ^ (-ν) := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC (-ν)).ne'
  rw [Real.div_rpow hm.le hC.le]
  field_simp

/-! ### Eq. (37): labour supply -/

/-- Galí (2015), eq. (37), p. 35: the marginal rate of substitution
`−U_n/U_c = N^φ / ((1 − ϑ) X^{ν−σ} C^{−ν}) = N^φ X^{σ−ν} C^ν (1 − ϑ)⁻¹`. -/
theorem mrs_eq {ϑ ν σ φ N C X : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hX : 0 < X) :
    N ^ φ / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν)) = N ^ φ * X ^ (σ - ν) * C ^ ν / (1 - ϑ) := by
  have h1 : (1 : ℝ) - ϑ ≠ 0 := by linarith
  rw [show σ - ν = -(ν - σ) by ring, Real.rpow_neg hX.le, Real.rpow_neg hC.le]
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC ν).ne'
  field_simp

/-- Galí (2015), eq. (37), p. 35 (**necessity**): if hours `N` are a local optimum along the
budget line `P C = W N + Y₀` (the perturbation `P dC = W dN` of p. 19, real balances `m` and
everything else unchanged), with `C, m > 0`, then `W/P = N^φ X^{σ−ν} C^ν (1 − ϑ)⁻¹`. -/
theorem labour_foc_necessary {σ φ ϑ ν P W Y₀ C m N : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C) (hm : 0 < m) (hbud : P * C = W * N + Y₀)
    (hloc : IsLocalMax (fun N' => nsUtil σ φ ϑ ν ((W * N' + Y₀) / P) m N') N) :
    W / P = N ^ φ * composite ϑ ν C m ^ (σ - ν) * C ^ ν / (1 - ϑ) := by
  have hCeq : (W * N + Y₀) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + Y₀) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const Y₀).div_const P
    simpa using this
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hC hm
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    have : (1 : ℝ) + φ ≠ 0 := by linarith
    field_simp
  have hp := hasDerivAt_composite_path (ν := ν) hϑ0 hϑ1 hin (hasDerivAt_const N m)
    (by rw [hCeq]; exact hC) hm
  have hu := (MIUSeparable.hasDerivAt_utilPow σ (composite_pos (ν := ν) hϑ0 hϑ1
    (by rw [hCeq]; exact hC) hm)).comp N hp
  have hg := HasDerivAt.sub hu hd
  have h0 := hloc.hasDerivAt_eq_zero hg
  simp only [hCeq, mul_zero, add_zero] at h0
  rw [← mrs_eq (φ := φ) (N := N) (σ := σ) (ν := ν) hϑ1 hC hX]
  have hUc : 0 < (1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν) :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hX _)) (Real.rpow_pos_of_pos hC _)
  rw [eq_div_iff hUc.ne']
  have e : composite ϑ ν C m ^ (-σ) * (composite ϑ ν C m ^ ν * ((1 - ϑ) * C ^ (-ν) * (W / P)))
      = W / P * ((1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν)) := by
    rw [show ν - σ = -σ + ν by ring, Real.rpow_add hX]
    ring
  linarith

/-- Galí (2015), p. 35: with `ν = σ` the labour supply (37) is
`W/P = N^φ C^σ (1 − ϑ)⁻¹`, the separable case up to the constant factor `(1 − ϑ)⁻¹`. -/
theorem labour_supply_nu_eq_sigma (ϑ σ φ N X C : ℝ) :
    N ^ φ * X ^ (σ - σ) * C ^ σ / (1 - ϑ) = N ^ φ * C ^ σ / (1 - ϑ) := by
  rw [sub_self, Real.rpow_zero, mul_one]

/-- Galí (2015), p. 36: the log form of (37), exactly,
`log(N^φ X^{σ−ν} C^ν/(1 − ϑ)) = σ c + φ n + (ν − σ)(c − x) − log(1 − ϑ)`. -/
theorem labour_supply_log {σ φ ϑ ν N X C : ℝ} (hϑ1 : ϑ < 1) (hN : 0 < N) (hX : 0 < X)
    (hC : 0 < C) :
    Real.log (N ^ φ * X ^ (σ - ν) * C ^ ν / (1 - ϑ))
      = σ * Real.log C + φ * Real.log N + (ν - σ) * (Real.log C - Real.log X)
        - Real.log (1 - ϑ) := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hX,
    Real.log_rpow hC]
  ring

/-! ### Eq. (39): money demand -/

/-- Galí (2015), eq. (39), p. 35 (**necessity**, eq. (33) for the nonseparable utility): if the
money perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)` (p. 33) cannot raise utility, then
`U_m = (1 − Q) U_c`, i.e. `ϑ m^{−ν} = (1 − Q)(1 − ϑ) C^{−ν}` with `m = M/P`. -/
theorem money_foc_necessary {σ φ ϑ ν P Q C M N : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hP : 0 < P)
    (hC : 0 < C) (hM : 0 < M)
    (hloc : IsLocalMax (fun δ => nsUtil σ φ ϑ ν (C - (1 - Q) * δ / P) ((M + δ) / P) N) 0) :
    ϑ * (M / P) ^ (-ν) = (1 - Q) * ((1 - ϑ) * C ^ (-ν)) := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have h := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 hc1 hc2 (by simpa using hC)
    (by simpa using div_pos hM hP)
  have h0 := hloc.hasDerivAt_eq_zero h
  simp only [mul_zero, zero_div, sub_zero, add_zero] at h0
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hC (div_pos hM hP)
  have h1 := (mul_eq_zero.1 h0).resolve_left (Real.rpow_pos_of_pos hX _).ne'
  field_simp at h1
  linarith

/-- Galí (2015), eq. (39), p. 35: the money demand
`M/P = C (1 − e^{−i})^{−1/ν} (ϑ/(1 − ϑ))^{1/ν}`. -/
noncomputable def moneyDemand39 (ϑ ν C i : ℝ) : ℝ :=
  C * (1 - Real.exp (-i)) ^ (-1 / ν) * (ϑ / (1 - ϑ)) ^ (1 / ν)

/-- Galí (2015), eq. (39), p. 35 (**exact**): for `i > 0`, the optimality condition
`ϑ m^{−ν} = (1 − e^{−i})(1 − ϑ) C^{−ν}` is equivalent to the money demand (39). -/
theorem money_demand_39_iff {ϑ ν i C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hν : 0 < ν)
    (hi : 0 < i) (hC : 0 < C) (hm : 0 < m) :
    ϑ * m ^ (-ν) = (1 - Real.exp (-i)) * ((1 - ϑ) * C ^ (-ν)) ↔ m = moneyDemand39 ϑ ν C i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have hr : 0 < ϑ / (1 - ϑ) := div_pos hϑ0 h1
  have hp1 : 0 < ϑ * m ^ (-ν) := mul_pos hϑ0 (Real.rpow_pos_of_pos hm _)
  have hp2 : 0 < (1 - Real.exp (-i)) * ((1 - ϑ) * C ^ (-ν)) :=
    mul_pos hk (mul_pos h1 (Real.rpow_pos_of_pos hC _))
  have hp3 : 0 < moneyDemand39 ϑ ν C i := by
    unfold moneyDemand39
    exact mul_pos (mul_pos hC (Real.rpow_pos_of_pos hk _)) (Real.rpow_pos_of_pos hr _)
  rw [← Real.log_injOn_pos.eq_iff hp1 hp2, ← Real.log_injOn_pos.eq_iff hm hp3]
  unfold moneyDemand39
  rw [Real.log_mul hϑ0.ne' (Real.rpow_pos_of_pos hm _).ne', Real.log_rpow hm,
    Real.log_mul hk.ne' (mul_pos h1 (Real.rpow_pos_of_pos hC _)).ne',
    Real.log_mul h1.ne' (Real.rpow_pos_of_pos hC _).ne', Real.log_rpow hC,
    Real.log_mul (mul_pos hC (Real.rpow_pos_of_pos hk _)).ne' (Real.rpow_pos_of_pos hr _).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_rpow hr,
    Real.log_div hϑ0.ne' h1.ne']
  have key : Real.log C + -1 / ν * Real.log (1 - Real.exp (-i))
      + 1 / ν * (Real.log ϑ - Real.log (1 - ϑ))
      = (ν * Real.log C - Real.log (1 - Real.exp (-i)) + (Real.log ϑ - Real.log (1 - ϑ))) / ν := by
    field_simp
    ring
  rw [key, eq_div_iff hν.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), fn. 10, p. 36: the money demand (39) is homogeneous of degree one in
consumption (unit consumption elasticity), whatever `ν` and `σ`. -/
theorem moneyDemand39_homogeneous (ϑ ν C i l : ℝ) :
    moneyDemand39 ϑ ν (l * C) i = l * moneyDemand39 ϑ ν C i := by
  unfold moneyDemand39
  ring

/-- Galí (2015), eq. (40), p. 36 (**exact**): for `i > 0`,
`log(M/P) = c − ν⁻¹ log(1 − e^{−i}) + ν⁻¹ log(ϑ/(1 − ϑ))` with `c = log C`. -/
theorem log_moneyDemand39 {ϑ ν i C : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hν : ν ≠ 0)
    (hi : 0 < i) (hC : 0 < C) :
    Real.log (moneyDemand39 ϑ ν C i)
      = MIUSeparable.logMoneyDemand ν ν (Real.log C) i + 1 / ν * Real.log (ϑ / (1 - ϑ)) := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hr : 0 < ϑ / (1 - ϑ) := div_pos hϑ0 (by linarith)
  unfold moneyDemand39 MIUSeparable.logMoneyDemand
  rw [Real.log_mul (mul_pos hC (Real.rpow_pos_of_pos hk _)).ne' (Real.rpow_pos_of_pos hr _).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_rpow hr]
  rw [div_self hν]
  ring

/-- Galí (2015), eq. (40), p. 36 (**exact derivative**): for `ν ≠ 0`, `i > 0`, the log money
demand `(c, i) ↦ c − ν⁻¹ log(1 − e^{−i}) + const` has derivative `(dc, di) ↦ dc − η di`,
`η = 1/(ν(e^i − 1))`: to first order `m − p = c − η i` (up to a constant). -/
theorem hasFDerivAt_log_money_demand_40 (ϑ c : ℝ) {ν i : ℝ} (hν : ν ≠ 0) (hi : 0 < i) :
    HasFDerivAt
      (fun x : ℝ × ℝ => MIUSeparable.logMoneyDemand ν ν x.1 x.2 + 1 / ν * Real.log (ϑ / (1 - ϑ)))
      (ContinuousLinearMap.fst ℝ ℝ ℝ - MIUSeparable.eta ν i • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c, i) :=
  (MIUSeparable.hasFDerivAt_logMoneyDemand_unit c hν hi).add_const _

/-! ### `χ`: the log-linearised composite -/

/-- Galí (2015), p. 36: the share of real balances in the composite, as a function of
`d = log(M/P) − log C`: `ϑ e^{(1−ν)d}/((1 − ϑ) + ϑ e^{(1−ν)d})`. -/
noncomputable def share (ϑ ν d : ℝ) : ℝ :=
  ϑ * Real.exp ((1 - ν) * d) / ((1 - ϑ) + ϑ * Real.exp ((1 - ν) * d))

/-- Galí (2015), p. 36: `x = log X` as a function of `c = log C` and `q = log(M/P)`. -/
noncomputable def logX (ϑ ν c q : ℝ) : ℝ := Real.log (composite ϑ ν (Real.exp c) (Real.exp q))

/-- Galí (2015), p. 36: by homogeneity `x(c, q) = c + x(0, q − c)`. -/
theorem logX_homogeneous {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (c q : ℝ) :
    logX ϑ ν c q = c + logX ϑ ν 0 (q - c) := by
  unfold logX
  have h1 : Real.exp c = Real.exp c * Real.exp 0 := by rw [Real.exp_zero, mul_one]
  have h2 : Real.exp q = Real.exp c * Real.exp (q - c) := by
    rw [← Real.exp_add, add_sub_cancel]
  rw [h1, h2, composite_homogeneous hϑ0 hϑ1 (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _),
    Real.log_mul (Real.exp_pos _).ne' (composite_pos hϑ0 hϑ1 (Real.exp_pos _)
      (Real.exp_pos _)).ne', Real.log_exp, Real.exp_zero]

/-- Galí (2015), p. 36: `d ↦ x(0, d)` has derivative `share ϑ ν d` (both for `ν ≠ 1` and
for the Cobb–Douglas case `ν = 1`, where the share is `ϑ`). -/
theorem hasDerivAt_logX_zero {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (d : ℝ) :
    HasDerivAt (fun d' => logX ϑ ν 0 d') (share ϑ ν d) d := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  by_cases hν : ν = 1
  · subst hν
    have hfun : (fun d' => logX ϑ 1 0 d') = fun d' => ϑ * d' := by
      funext d'
      simp only [logX, composite, ↓reduceIte, Real.exp_zero, Real.one_rpow, one_mul]
      rw [Real.log_rpow (Real.exp_pos _), Real.log_exp]
    rw [hfun]
    refine ((hasDerivAt_id d).const_mul ϑ).congr_deriv ?_
    simp [share]
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hfun : (fun d' => logX ϑ ν 0 d')
        = fun d' => 1 / (1 - ν) * Real.log ((1 - ϑ) + ϑ * Real.exp ((1 - ν) * d')) := by
      funext d'
      have hS : 0 < (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d') :=
        add_pos h1 (mul_pos hϑ0 (Real.exp_pos _))
      simp only [logX, composite, hν, ↓reduceIte, Real.exp_zero, Real.one_rpow, mul_one]
      rw [← Real.exp_mul, mul_comm d', Real.log_rpow hS]
    rw [hfun]
    have hS : 0 < (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d) :=
      add_pos h1 (mul_pos hϑ0 (Real.exp_pos _))
    have hin : HasDerivAt (fun d' => (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d'))
        (ϑ * (Real.exp ((1 - ν) * d) * (1 - ν))) d := by
      have := (((hasDerivAt_id d).const_mul (1 - ν)).exp.const_mul ϑ).const_add (1 - ϑ)
      simpa using this
    refine ((hin.log hS.ne').const_mul (1 / (1 - ν))).congr_deriv ?_
    unfold share
    field_simp

/-- Galí (2015), p. 36 (**exact derivative**): `c − x` as a function of `(c, q)`, `q = m − p`,
has total derivative `χ (dc − dq)` at `(c, q)`, with `χ = share ϑ ν (q − c)`: to first
order `c − x = χ (c − (m − p))` (up to a constant). -/
theorem hasFDerivAt_gap {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (c q : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => x.1 - logX ϑ ν x.1 x.2)
      (share ϑ ν (q - c) • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
      (c, q) := by
  have hfun : (fun x : ℝ × ℝ => x.1 - logX ϑ ν x.1 x.2)
      = fun x : ℝ × ℝ => -logX ϑ ν 0 (x.2 - x.1) := by
    funext x
    rw [logX_homogeneous hϑ0 hϑ1 x.1 x.2]
    ring
  rw [hfun]
  have hl : HasFDerivAt (fun x : ℝ × ℝ => x.2 - x.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (c, q) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have h := ((hasDerivAt_logX_zero (ν := ν) hϑ0 hϑ1 (q - c)).comp_hasFDerivAt (c, q) hl).neg
  refine h.congr_fderiv ?_
  ext <;> simp

/-- Galí (2015), p. 36: the steady-state inverse consumption velocity
`k_m = (ϑ/((1 − β)(1 − ϑ)))^{1/ν}`. -/
noncomputable def km (ϑ β ν : ℝ) : ℝ := (ϑ / ((1 - β) * (1 - ϑ))) ^ (1 / ν)

/-- Galí (2015), p. 37: `χ = k_m(1 − β)/(1 + k_m(1 − β))`, written as a function of `k`. -/
noncomputable def chi (k β : ℝ) : ℝ := k * (1 - β) / (1 + k * (1 - β))

/-- Galí (2015), p. 36: the first printed form
`χ = ϑ^{1/ν}(1 − β)^{1−1/ν}/((1 − ϑ)^{1/ν} + ϑ^{1/ν}(1 − β)^{1−1/ν})`. -/
noncomputable def chi1 (ϑ β ν : ℝ) : ℝ :=
  ϑ ^ (1 / ν) * (1 - β) ^ (1 - 1 / ν) /
    ((1 - ϑ) ^ (1 / ν) + ϑ ^ (1 / ν) * (1 - β) ^ (1 - 1 / ν))

/-- Galí (2015), p. 36: `k_m > 0`. -/
theorem km_pos {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) : 0 < km ϑ β ν :=
  Real.rpow_pos_of_pos (div_pos hϑ0 (mul_pos (by linarith) (by linarith))) _

/-- Galí (2015), p. 36: `k_m` is the steady-state ratio `(M/P)/C` implied by the money demand
(39) at the zero-inflation steady state `i = ρ = −log β`. -/
theorem km_money_demand {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (C : ℝ) : moneyDemand39 ϑ ν C (-Real.log β) = C * km ϑ β ν := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  unfold moneyDemand39 km
  rw [neg_neg, Real.exp_log hβ0, mul_assoc]
  congr 1
  rw [show ϑ / ((1 - β) * (1 - ϑ)) = (1 - β)⁻¹ * (ϑ / (1 - ϑ)) by field_simp,
    Real.mul_rpow (inv_nonneg.2 h2.le) (div_pos hϑ0 h1).le, Real.inv_rpow h2.le, neg_div,
    Real.rpow_neg h2.le]

/-- Galí (2015), p. 36: at the steady-state ratio `M/P = k_m C` the share equals
`χ = k_m(1 − β)/(1 + k_m(1 − β))` (p. 37). -/
theorem share_at_km {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) (hν : 0 < ν) :
    share ϑ ν (Real.log (km ϑ β ν)) = chi (km ϑ β ν) β := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  have hk := km_pos (ν := ν) hϑ0 hϑ1 hβ1
  have hb : 0 < ϑ / ((1 - β) * (1 - ϑ)) := div_pos hϑ0 (mul_pos h2 h1)
  have hexp : Real.exp ((1 - ν) * Real.log (km ϑ β ν)) = km ϑ β ν * ((1 - β) * (1 - ϑ) / ϑ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hk, sub_eq_add_neg, Real.rpow_add hk, Real.rpow_one]
    congr 1
    unfold km
    rw [← Real.rpow_mul hb.le, show 1 / ν * -ν = -1 by field_simp, Real.rpow_neg_one, inv_div]
  unfold share chi
  rw [hexp]
  field_simp

/-- Galí (2015), pp. 36–37: the two printed forms of `χ` agree,
`ϑ^{1/ν}(1 − β)^{1−1/ν}/((1 − ϑ)^{1/ν} + ϑ^{1/ν}(1 − β)^{1−1/ν}) = k_m(1 − β)/(1 + k_m(1 − β))`. -/
theorem chi1_eq_chi {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) :
    chi1 ϑ β ν = chi (km ϑ β ν) β := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  have a1 := Real.rpow_pos_of_pos h1 (1 / ν)
  have a2 := Real.rpow_pos_of_pos h2 (1 / ν)
  have a3 := Real.rpow_pos_of_pos hϑ0 (1 / ν)
  unfold chi1 chi km
  rw [Real.div_rpow hϑ0.le (mul_pos h2 h1).le, Real.mul_rpow h2.le h1.le,
    Real.rpow_sub h2, Real.rpow_one]
  field_simp

/-- Galí (2015), p. 36: `χ ∈ [0, 1)` for `k ≥ 0` and `β < 1`. -/
theorem chi_mem {k β : ℝ} (hk : 0 ≤ k) (hβ1 : β < 1) : 0 ≤ chi k β ∧ chi k β < 1 := by
  have h : 0 ≤ k * (1 - β) := mul_nonneg hk (by linarith)
  unfold chi
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- Galí (2015), p. 36: `χ` is the partial derivative of `log X` with respect to `log(M/P)` at
the zero-inflation steady state `q = c + log k_m`; with the two printed forms. -/
theorem hasDerivAt_logX_steady_state {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1)
    (hν : 0 < ν) (c : ℝ) :
    HasDerivAt (fun q => logX ϑ ν c q) (chi (km ϑ β ν) β) (c + Real.log (km ϑ β ν)) ∧
      chi1 ϑ β ν = chi (km ϑ β ν) β := by
  refine ⟨?_, chi1_eq_chi hϑ0 hϑ1 hβ1⟩
  have hfun : (fun q => logX ϑ ν c q) = fun q => c + logX ϑ ν 0 (q - c) :=
    funext fun q => logX_homogeneous hϑ0 hϑ1 c q
  rw [hfun, ← share_at_km hϑ0 hϑ1 hβ1 hν]
  have h := (hasDerivAt_logX_zero (ν := ν) hϑ0 hϑ1 (c + Real.log (km ϑ β ν) - c)).comp
    (c + Real.log (km ϑ β ν)) ((hasDerivAt_id _).sub_const c)
  have h2 := h.const_add c
  simp only [add_sub_cancel_left, mul_one] at h2
  exact h2

/-! ### `η` and `ϖ` at the steady state; eq. (41) -/

/-- Galí (2015), p. 37: at the zero-inflation steady state `i = ρ = −log β`,
`η = 1/(ν(e^ρ − 1)) = β/(ν(1 − β))`. -/
theorem eta_steady_state {ν β : ℝ} (hν : ν ≠ 0) (hβ0 : 0 < β) (hβ1 : β < 1) :
    MIUSeparable.eta ν (-Real.log β) = β / (ν * (1 - β)) := by
  unfold MIUSeparable.eta
  rw [Real.exp_neg, Real.exp_log hβ0]
  have : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp

/-- Galí (2015), eq. (41), p. 37: `ϖ = k_m β (1 − σ/ν)/(1 + k_m(1 − β))`. -/
noncomputable def varpi (k β σ ν : ℝ) : ℝ := k * β * (1 - σ / ν) / (1 + k * (1 - β))

/-- Galí (2015), p. 37: `η χ (ν − σ) = ϖ` with the steady-state `η = β/(ν(1 − β))`. -/
theorem varpi_eq {k β σ ν : ℝ} (hν : ν ≠ 0) (hβ1 : β < 1) (hk : 0 ≤ k) :
    β / (ν * (1 - β)) * chi k β * (ν - σ) = varpi k β σ ν := by
  have : (1 : ℝ) - β ≠ 0 := by linarith
  have : 1 + k * (1 - β) ≠ 0 := by nlinarith
  unfold chi varpi
  field_simp

/-- Galí (2015), p. 37: for `k_m > 0`, `0 < β < 1`, `ν > 0`: `ϖ > 0 ⟺ ν > σ`. -/
theorem varpi_pos_iff {k β σ ν : ℝ} (hk : 0 < k) (hβ0 : 0 < β) (hβ1 : β < 1) (hν : 0 < ν) :
    0 < varpi k β σ ν ↔ σ < ν := by
  have hA : 0 < 1 + k * (1 - β) := by nlinarith
  have hkb : 0 < k * β := mul_pos hk hβ0
  unfold varpi
  rw [div_pos_iff_of_pos_right hA, mul_pos_iff_of_pos_left hkb, sub_pos, div_lt_one hν]

/-- Galí (2015), eq. (41), p. 37 (the log-linear model): from the log form of (37),
`c − x = χ (c − (m − p))` and (40) `m − p = c − η i`, the labour supply is
`w − p = σ c + φ n + χ (ν − σ)(c − (m − p)) = σ c + φ n + ϖ i` with `ϖ = η χ (ν − σ)`. -/
theorem eq41 {σ φ ν χ η ϖ w c n x mp i : ℝ} (hϖ : ϖ = η * χ * (ν - σ))
    (hls : w = σ * c + φ * n + (ν - σ) * (c - x)) (hx : c - x = χ * (c - mp))
    (h40 : mp = c - η * i) :
    w = σ * c + φ * n + χ * (ν - σ) * (c - mp) ∧ w = σ * c + φ * n + ϖ * i := by
  constructor
  · rw [hls, hx]
    ring
  · rw [hls, hx, h40, hϖ]
    ring

/-! ### Eqs. (42)–(43): output and the nominal rate -/

/-- Galí (2015), p. 23: `D = σ(1 − α) + φ + α`. -/
noncomputable def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), p. 37: `ψ_ya = (1 + φ)/D`. -/
noncomputable def psiYa (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), p. 37: `ψ_yi = −ϖ(1 − α)/D`. -/
noncomputable def psiYi (ϖ σ φ α : ℝ) : ℝ := -(ϖ * (1 - α)) / bigD σ φ α

/-- Galí (2015), eqs. (42)–(43), p. 37 (the log-linear model): labour-market clearing
`σ c + φ n + ϖ i = a − α n + log(1 − α)` with `y = c` and `y = a + (1 − α) n` give exactly
`y = ψ_ya a + ψ_yi i + (1 − α) log(1 − α)/D` (the additive constant made explicit). -/
theorem eq43 {σ φ α ϖ y a n i c : ℝ} (hD : bigD σ φ α ≠ 0)
    (h42 : σ * c + φ * n + ϖ * i = a - α * n + Real.log (1 - α)) (hyc : y = c)
    (h17 : y = a + (1 - α) * n) :
    y = psiYa σ φ α * a + psiYi ϖ σ φ α * i + (1 - α) * Real.log (1 - α) / bigD σ φ α := by
  have key : bigD σ φ α * y = (1 + φ) * a - ϖ * (1 - α) * i + (1 - α) * Real.log (1 - α) := by
    unfold bigD
    linear_combination (1 - α) * h42 + σ * (1 - α) * hyc + (φ + α) * h17
  unfold psiYa psiYi
  field_simp
  linear_combination key

/-- Galí (2015), p. 37: for `D > 0` and `α < 1`, `ψ_yi < 0 ⟺ ϖ > 0`. -/
theorem psiYi_neg_iff {ϖ σ φ α : ℝ} (hD : 0 < bigD σ φ α) (hα : α < 1) :
    psiYi ϖ σ φ α < 0 ↔ 0 < ϖ := by
  unfold psiYi
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · linarith
    · nlinarith
  · intro h
    right
    exact ⟨by nlinarith, hD⟩

/-- Galí (2015), p. 38: as `ν → ∞` with `k_m`, `β` fixed,
`ψ_yi → −k_m β (1 − α)/(D (1 + k_m (1 − β)))`. -/
theorem tendsto_psiYi_nu (k β σ φ α : ℝ) :
    Tendsto (fun ν => psiYi (varpi k β σ ν) σ φ α) atTop
      (𝓝 (-(k * β * (1 - α)) / (bigD σ φ α * (1 + k * (1 - β))))) := by
  have h1 : Tendsto (fun ν : ℝ => σ / ν) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h3 := (((((tendsto_const_nhds (x := (1 : ℝ))).sub h1).const_mul (k * β)).div_const
    (1 + k * (1 - β))).mul_const (1 - α)).neg.div_const (bigD σ φ α)
  have hfun : (fun ν => psiYi (varpi k β σ ν) σ φ α)
      = fun ν => -(k * β * (1 - σ / ν) / (1 + k * (1 - β)) * (1 - α)) / bigD σ φ α := by
    funext ν
    simp only [psiYi, varpi]
  rw [hfun]
  convert h3 using 2
  rw [sub_zero, mul_one, div_mul_eq_mul_div, neg_div, neg_div, div_div,
    mul_comm (1 + k * (1 - β))]

/-- Galí (2015), p. 38: with `σ = 1`, `φ = 5`, `α = 1/4` (`D = 6`) the `ν → ∞` limit of
`ψ_yi` is `−k_m β/(8(1 + k_m(1 − β)))`. -/
theorem psiYi_limit_calib (k β : ℝ) :
    -(k * β * (1 - 1 / 4)) / (bigD 1 5 (1 / 4) * (1 + k * (1 - β)))
      = -(k * β) / (8 * (1 + k * (1 - β))) := by
  unfold bigD
  by_cases h : 1 + k * (1 - β) = 0
  · simp [h]
  · field_simp
    ring

/-- Galí (2015), p. 38 (`ψ_yi ≃ −k_m/8`): as `β → 1` the calibrated limit
`−k_m β/(8(1 + k_m(1 − β)))` tends to `−k_m/8`. -/
theorem tendsto_calib_beta_one (k : ℝ) :
    Tendsto (fun β : ℝ => -(k * β) / (8 * (1 + k * (1 - β)))) (𝓝 1) (𝓝 (-k / 8)) := by
  have hc : ContinuousAt (fun β : ℝ => -(k * β) / (8 * (1 + k * (1 - β)))) 1 :=
    ((continuousAt_const.mul continuousAt_id).neg).div
      (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
        (continuousAt_const.sub continuousAt_id)))) (by norm_num)
  simpa using hc.tendsto

/-- Galí (2015), p. 38: the `ν → ∞` limit of `ψ_yi` at `σ = 1`, `φ = 5`, `α = 1/4`, as a
function of `k_m` and `β` (`tendsto_psiYi_nu`). -/
noncomputable def calibLimit (k β : ℝ) : ℝ :=
  -(k * β * (1 - 1 / 4)) / (bigD 1 5 (1 / 4) * (1 + k * (1 - β)))

/-- Galí (2015), p. 38, monetary base (`k_m = 0.3`, `β = 0.99`, `σ = 1`, `φ = 5`,
`α = 1/4`): the limit multiplier lies in `(−0.04, −0.035)` (book: `≃ −0.04`), and a
one-point annual (`0.25` quarterly) rise in `i` moves quarterly output by between
`−0.01` and `−0.009` percent (book: about `0.01` percent). -/
theorem psiYi_limit_km_base :
    -(4 / 100) < calibLimit (3 / 10) (99 / 100) ∧ calibLimit (3 / 10) (99 / 100) < -(35 / 1000) ∧
      -(1 / 100) < calibLimit (3 / 10) (99 / 100) / 4 ∧
      calibLimit (3 / 10) (99 / 100) / 4 < -(9 / 1000) := by
  simp only [calibLimit, bigD]
  norm_num

/-- Galí (2015), p. 38, M2 (`k_m = 3`, `β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`): the limit
multiplier lies in `(−0.37, −0.36)` (book: `≃ −0.4`, i.e. `−k_m/8 = −0.375` rounded), and a
one-point annual rise in `i` moves quarterly output by between `−0.1` and `−0.09` percent
(book: `0.1` percent). -/
theorem psiYi_limit_km_m2 :
    -(37 / 100) < calibLimit 3 (99 / 100) ∧ calibLimit 3 (99 / 100) < -(36 / 100) ∧
      -(1 / 10) < calibLimit 3 (99 / 100) / 4 ∧ calibLimit 3 (99 / 100) / 4 < -(9 / 100) := by
  simp only [calibLimit, bigD]
  norm_num

/-! ### Eqs. (44)–(45) -/

/-- Galí (2015), p. 38: `Θ = ϖ(1 − α)/(η D + ϖ(1 − α))`. -/
noncomputable def Theta (ϖ η σ φ α : ℝ) : ℝ := ϖ * (1 - α) / (η * bigD σ φ α + ϖ * (1 - α))

/-- Galí (2015), p. 39: `Λ = η(α + φ)/(η D + ϖ(1 − α))`. -/
noncomputable def Lambda (ϖ η σ φ α : ℝ) : ℝ := η * (α + φ) / (η * bigD σ φ α + ϖ * (1 - α))

/-- Galí (2015), eqs. (44)–(45), p. 38 (the log-linear model, `a = 0`): from (43)
`y = ψ_yi i` and (40) `m − p = y − η i`: `y = Θ (m − p)` and
`i = −η⁻¹ (1 − Θ)(m − p)`. -/
theorem eq44_45 {ϖ η σ φ α y q i : ℝ} (hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0) (hη : η ≠ 0)
    (hD : bigD σ φ α ≠ 0) (h43 : y = psiYi ϖ σ φ α * i) (h40 : q = y - η * i) :
    y = Theta ϖ η σ φ α * q ∧ i = -(1 / η) * (1 - Theta ϖ η σ φ α) * q := by
  have h43' : y * bigD σ φ α = -(ϖ * (1 - α)) * i := by
    rw [h43, psiYi]
    field_simp
  have hi : i * (η * bigD σ φ α + ϖ * (1 - α)) = -(bigD σ φ α * q) := by
    linear_combination bigD σ φ α * h40 + h43'
  have hi' : i = -(bigD σ φ α * q) / (η * bigD σ φ α + ϖ * (1 - α)) := by
    rw [eq_div_iff hK]
    exact hi
  constructor
  · rw [h43, hi', psiYi, Theta]
    field_simp
  · rw [hi', show 1 - Theta ϖ η σ φ α = η * bigD σ φ α / (η * bigD σ φ α + ϖ * (1 - α)) by
      unfold Theta; field_simp; ring]
    field_simp

/-- Galí (2015), p. 38: `Θ ∈ [0, 1)` for `η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`. -/
theorem Theta_mem {ϖ η σ φ α : ℝ} (hη : 0 < η) (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ) (hα : α < 1) :
    0 ≤ Theta ϖ η σ φ α ∧ Theta ϖ η σ φ α < 1 := by
  have h1 : 0 ≤ ϖ * (1 - α) := mul_nonneg hϖ (by linarith)
  have h2 : 0 < η * bigD σ φ α := mul_pos hη hD
  unfold Theta
  exact ⟨div_nonneg h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- Galí (2015), p. 39: `Λ ≥ 0` for `η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`, `α + φ ≥ 0`. -/
theorem Lambda_nonneg {ϖ η σ φ α : ℝ} (hη : 0 < η) (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ)
    (hα : α < 1) (hαφ : 0 ≤ α + φ) : 0 ≤ Lambda ϖ η σ φ α := by
  have h1 : 0 ≤ ϖ * (1 - α) := mul_nonneg hϖ (by linarith)
  have h2 : 0 < η * bigD σ φ α := mul_pos hη hD
  unfold Lambda
  exact div_nonneg (mul_nonneg hη.le hαφ) (by linarith)

/-- Galí (2015), p. 39 (the algebra behind (48)): `η + ϖ(1 − Θ) − σ Θ η = η + ϖ Λ`. -/
theorem coef_identity {ϖ η σ φ α : ℝ} (hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0) :
    η + ϖ * (1 - Theta ϖ η σ φ α) - σ * Theta ϖ η σ φ α * η = η + ϖ * Lambda ϖ η σ φ α := by
  unfold Theta Lambda
  field_simp
  unfold bigD
  ring

/-! ### Eqs. (38), (46)–(47): the Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (38), p. 35: the marginal-utility ratio entering (5),
`U_c(C', X')/U_c(C, X) = (C'/C)^{−ν}(X'/X)^{ν−σ}`. -/
theorem uc_ratio {ϑ ν σ C X C' X' : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hX : 0 < X) (hC' : 0 ≤ C')
    (hX' : 0 ≤ X') :
    (1 - ϑ) * X' ^ (ν - σ) * C' ^ (-ν) / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν))
      = (C' / C) ^ (-ν) * (X' / X) ^ (ν - σ) := by
  have h1 : (1 : ℝ) - ϑ ≠ 0 := by linarith
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC (-ν)).ne'
  rw [Real.div_rpow hC' hC.le, Real.div_rpow hX' hX.le]
  field_simp

/-- Galí (2015), eq. (38), p. 35: the Euler equation at date `t`, node by node,
`Q_t = β E_t[(C_{t+1}/C_t)^{−ν}(X_{t+1}/X_t)^{ν−σ} P_t/P_{t+1}]` (date-`t` values enter as
numbers at the node `ω`). -/
def MIUEuler (β σ ν : ℝ) (Q C X P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * 𝔼.E t (fun ω' => (C (t + 1) ω' / C t ω) ^ (-ν) *
    (X (t + 1) ω' / X t ω) ^ (ν - σ) * (P t ω / P (t + 1) ω')) ω

/-- Galí (2015), eq. (38), p. 35, from eq. (5), p. 19: the Euler equation
`Q_t = β E_t[(U_{c,t+1}/U_{c,t})(P_t/P_{t+1})]` with the marginal utility
`U_c = (1 − ϑ) X^{ν−σ} C^{−ν}` is exactly (38) (positive `C`, `X`). -/
theorem euler5_iff_miuEuler {β σ ν ϑ : ℝ} (hϑ1 : ϑ < 1) {Q C X P : ℕ → Ω → ℝ} {t : ℕ}
    (hC : ∀ ω, 0 < C t ω) (hX : ∀ ω, 0 < X t ω) (hC1 : ∀ ω, 0 ≤ C (t + 1) ω)
    (hX1 : ∀ ω, 0 ≤ X (t + 1) ω) :
    (∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (1 - ϑ) * X (t + 1) ω' ^ (ν - σ) * C (t + 1) ω' ^ (-ν) /
        ((1 - ϑ) * X t ω ^ (ν - σ) * C t ω ^ (-ν)) * (P t ω / P (t + 1) ω')) ω) ↔
      MIUEuler 𝔼 β σ ν Q C X P t := by
  unfold MIUEuler
  refine forall_congr' fun ω => ?_
  have h : (fun ω' => (1 - ϑ) * X (t + 1) ω' ^ (ν - σ) * C (t + 1) ω' ^ (-ν) /
      ((1 - ϑ) * X t ω ^ (ν - σ) * C t ω ^ (-ν)) * (P t ω / P (t + 1) ω'))
      = fun ω' => (C (t + 1) ω' / C t ω) ^ (-ν) * (X (t + 1) ω' / X t ω) ^ (ν - σ) *
        (P t ω / P (t + 1) ω') := by
    funext ω'
    rw [uc_ratio hϑ1 (hC ω) (hX ω) (hC1 ω') (hX1 ω')]
  rw [h]

/-- Galí (2015), p. 35: with `ν = σ` the Euler equation (38) is the separable-case Euler
equation `Q_t = β E_t[(C_{t+1}/C_t)^{−σ} P_t/P_{t+1}]`. -/
theorem miuEuler_nu_eq_sigma (β σ : ℝ) (Q C X P : ℕ → Ω → ℝ) (t : ℕ) :
    MIUEuler 𝔼 β σ σ Q C X P t ↔ ∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω')) ω := by
  simp [MIUEuler]

/-- Galí (2015), p. 39: the Euler moment of (38) in logs,
`E_t[exp(i_t − ρ − ν Δc_{t+1} + (ν − σ) Δx_{t+1} − Δp_{t+1})]` at the node `ω`. -/
noncomputable def miuMoment (σ ν ρ : ℝ) (i c x p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - ν * (c (t + 1) ω' - c t ω)
    + (ν - σ) * (x (t + 1) ω' - x t ω) - (p (t + 1) ω' - p t ω))) ω

/-- Galí (2015), eq. (38), p. 35 (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`,
`X = e^x`, `P = e^p`, the Euler equation holds iff the Euler moment is one at every node. -/
theorem miuEuler_iff_moment (σ ν ρ : ℝ) (i c x p : ℕ → Ω → ℝ) (t : ℕ) :
    MIUEuler 𝔼 (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (x t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, miuMoment 𝔼 σ ν ρ i c x p t ω = 1 := by
  unfold MIUEuler
  refine forall_congr' fun ω => ?_
  set G : Ω → ℝ := fun ω' => (Real.exp (c (t + 1) ω') / Real.exp (c t ω)) ^ (-ν) *
    (Real.exp (x (t + 1) ω') / Real.exp (x t ω)) ^ (ν - σ) *
    (Real.exp (p t ω) / Real.exp (p (t + 1) ω')) with hG
  have hmom : miuMoment 𝔼 σ ν ρ i c x p t ω = Real.exp (i t ω - ρ) * 𝔼.E t G ω := by
    have hfun : (fun ω' => Real.exp (i t ω - ρ - ν * (c (t + 1) ω' - c t ω)
        + (ν - σ) * (x (t + 1) ω' - x t ω) - (p (t + 1) ω' - p t ω)))
        = Real.exp (i t ω - ρ) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hG]
      rw [← Real.exp_sub, ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_mul, ← Real.exp_mul,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [miuMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hmom]
  have e1 : Real.exp (i t ω - ρ) = Real.exp (i t ω) * Real.exp (-ρ) := by
    rw [← Real.exp_add]
    ring_nf
  have e2 : Real.exp (i t ω) * Real.exp (-i t ω) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [e1]
  constructor
  · intro h
    rw [mul_assoc, ← h, e2]
  · intro h
    calc Real.exp (-i t ω)
        = Real.exp (-i t ω) * (Real.exp (i t ω) * Real.exp (-ρ) * 𝔼.E t G ω) := by
          rw [h, mul_one]
      _ = (Real.exp (i t ω) * Real.exp (-i t ω)) * (Real.exp (-ρ) * 𝔼.E t G ω) := by ring
      _ = Real.exp (-ρ) * 𝔼.E t G ω := by rw [e2, one_mul]

/-- Galí (2015), eq. (46), p. 39, first line (**exact under perfect foresight**): the Euler
equation (38) holds at date `t` iff
`c_t = c_{t+1} − σ⁻¹(i_t − π_{t+1} − (ν − σ)((c_{t+1} − x_{t+1}) − (c_t − x_t)) − ρ)`. -/
theorem pf_miuEuler_iff {σ : ℝ} (hσ : σ ≠ 0) (ν ρ : ℝ) (i c x p : ℕ → Unit → ℝ) (t : ℕ) :
    MIUEuler perfectForesight (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (x t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, c t ω = c (t + 1) ω - σ⁻¹ * (i t ω - (p (t + 1) ω - p t ω)
        - (ν - σ) * ((c (t + 1) ω - x (t + 1) ω) - (c t ω - x t ω)) - ρ) := by
  rw [miuEuler_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [miuMoment, perfectForesight, LinearMap.id_apply]
  rw [Real.exp_eq_one_iff]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (restated from the Chapter 3 project): for a bounded
random variable `Y`, `s ↦ E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω) (𝔼.E t Y ω) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero]
  have hO : (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
      - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω) =O[𝓝 0]
      fun s : ℝ => s ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (M ^ 2)
    have hcont : Continuous (fun s : ℝ => |s| * M) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [abs_zero, zero_mul] at this
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos)] with s hs
    have key : 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
        - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω
        = 𝔼.E t (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω') ω := by
      have h1 : (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω')
          = (fun ω' => Real.exp (s * Y ω')) - (fun _ => (1 : ℝ)) - s • Y := by
        funext ω'
        simp
      have h2 : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
        funext ω'
        simp
      rw [h1, h2, map_sub, map_sub, map_smul, 𝔼.const]
      simp
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
    apply 𝔼.abs_E_le
    intro ω'
    have hy : |s * Y ω'| ≤ 1 := by
      rw [abs_mul]
      calc |s| * |Y ω'| ≤ |s| * M := mul_le_mul_of_nonneg_left (hY ω') (abs_nonneg s)
        _ ≤ 1 := hs
    have hsq : (s * Y ω') ^ 2 ≤ M ^ 2 * |s ^ 2| := by
      rw [abs_pow, sq_abs, mul_pow, mul_comm]
      have : Y ω' ^ 2 ≤ M ^ 2 := by
        have := hY ω'
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    exact (Real.abs_exp_sub_one_sub_id_le hy).trans hsq
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (restated from the Chapter 3 project): for bounded `Y`,
`s ↦ log E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_log_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω))
      (𝔼.E t Y ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω = 1 := by
    have : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
      funext ω'
      simp
    rw [this, 𝔼.const]
  have := (hasDerivAt_E_exp 𝔼 hY t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  exact this

/-- Galí (2015), eq. (46), p. 39: the linear expression obtained by linearising the Euler
moment of (38), in deviations from the zero-inflation steady state:
`î_t − ν(E_t ĉ_{t+1} − ĉ_t) + (ν − σ)(E_t x̂_{t+1} − x̂_t) − (E_t p̂_{t+1} − p̂_t)`. -/
noncomputable def linearisedMIUEuler (σ ν : ℝ) (ih ch xh ph : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - ν * (𝔼.E t (ch (t + 1)) ω - ch t ω)
    + (ν - σ) * (𝔼.E t (xh (t + 1)) ω - xh t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)

/-- Galí (2015), p. 39: at the zero-inflation steady state (`i = ρ`, constant `c̄, x̄, p̄`) the
Euler moment of (38) equals one. -/
theorem miuMoment_family_zero (σ ν ρ cbar xbar pbar : ℝ) (ih ch xh ph : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    miuMoment 𝔼 σ ν ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => xbar + 0 * xh t ω) (fun t ω => pbar + 0 * ph t ω) t ω = 1 := by
  simp only [miuMoment, zero_mul, add_zero, sub_self, mul_zero, Real.exp_zero]
  rw [𝔼.const]

/-- Galí (2015), eq. (46), p. 39, as an **exact derivative**: along the family of stochastic
paths `i = ρ + s î`, `c = c̄ + s ĉ`, `x = x̄ + s x̂`, `p = p̄ + s p̂` around the zero-inflation
steady state, with bounded deviations, `s ↦ log E_t[exp(i_t − ρ − νΔc + (ν − σ)Δx − Δp)](ω)`
has derivative at `s = 0` equal to `linearisedMIUEuler σ ν î ĉ x̂ p̂ t ω`. -/
theorem hasDerivAt_log_miuMoment_family (σ ν ρ cbar xbar pbar : ℝ) {ih ch xh ph : ℕ → Ω → ℝ}
    (hc : BoundedProc ch) (hx : BoundedProc xh) (hp : BoundedProc ph) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (miuMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => xbar + s * xh t ω)
        (fun t ω => pbar + s * ph t ω) t ω))
      (linearisedMIUEuler 𝔼 σ ν ih ch xh ph t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨Mp, hMp⟩ := hp
  set a : ℝ := ih t ω + ν * ch t ω - (ν - σ) * xh t ω + ph t ω with ha
  set Y : Ω → ℝ := fun ω' => a + (-ν * ch (t + 1) ω' + (ν - σ) * xh (t + 1) ω' - ph (t + 1) ω')
    with hY
  have hbd : ∀ ω', |Y ω'| ≤ |a| + |ν| * Mc + |ν - σ| * Mx + Mp := by
    intro ω'
    have h1 := abs_le.1 (show |ν * ch (t + 1) ω'| ≤ |ν| * Mc by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMc _ _) (abs_nonneg ν))
    have h2 := abs_le.1 (show |(ν - σ) * xh (t + 1) ω'| ≤ |ν - σ| * Mx by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMx _ _) (abs_nonneg _))
    have h3 := abs_le.1 (hMp (t + 1) ω')
    have h4 := abs_le.1 (le_refl |a|)
    rw [abs_le]
    simp only [hY]
    constructor <;> linarith
  have hfam : ∀ s : ℝ, miuMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => xbar + s * xh t ω)
      (fun t ω => pbar + s * ph t ω) t ω = 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω := by
    intro s
    unfold miuMoment
    refine congrArg (fun z => 𝔼.E t z ω) (funext fun ω' => ?_)
    congr 1
    simp only [hY, ha]
    ring
  simp_rw [hfam]
  have hval : 𝔼.E t Y ω = linearisedMIUEuler 𝔼 σ ν ih ch xh ph t ω := by
    have hfun : Y = (fun _ => a) + ((-ν) • ch (t + 1) + (ν - σ) • xh (t + 1) - ph (t + 1)) := by
      funext ω'
      simp [hY, smul_eq_mul]
    rw [hfun, map_add, 𝔼.const, map_sub, map_add, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedMIUEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), eq. (46), p. 39, first line, as a model equation:
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − (ν − σ)(E_t g_{t+1} − g_t) − ρ)` with
`g = c − x`. -/
def EulerGap (σ ν ρ : ℝ) (c g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))
    - (ν - σ) • (𝔼.E t (g (t + 1)) - g t) - fun _ => ρ)

/-- Galí (2015), eqs. (46)–(47), p. 39, last line, as a model equation:
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ E_t Δi_{t+1} − ρ)`. -/
def EulerLinear (σ ϖ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))
    - ϖ • (𝔼.E t (i (t + 1)) - i t) - fun _ => ρ)

/-- Galí (2015), eq. (46), p. 39 (**the first-order condition is exactly (46), first line**):
for `σ ≠ 0`, an adapted price level `p̂` and `π_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler
expression vanishes at every date iff `EulerGap` holds for `ĉ`, `ĝ = ĉ − x̂`, `i = ρ + î`. -/
theorem linearisedMIUEuler_eq_zero_iff {σ ν ρ : ℝ} (hσ : σ ≠ 0) {ih ch xh ph infl : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted ph) (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) :
    (∀ t, linearisedMIUEuler 𝔼 σ ν ih ch xh ph t = 0) ↔
      EulerGap 𝔼 σ ν ρ ch (fun t => ch t - xh t) (fun t => (fun _ => ρ) + ih t) infl := by
  unfold EulerGap
  refine forall_congr' fun t => ?_
  rw [hinfl, map_sub, hp t, map_sub]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [linearisedMIUEuler, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [linearisedMIUEuler, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢
    field_simp at e
    linear_combination e

/-- Galí (2015), eq. (46), p. 39 (the log-linear model): if `c − x = κ i + const` at every date
(from `c − x = χ(c − (m − p))` and (40), `κ = χ η`), then the first line of (46) is
equivalent to its last line with `ϖ = (ν − σ) κ`. -/
theorem eulerGap_iff_eulerLinear {σ ν ρ κ k : ℝ} {c g i infl : ℕ → Ω → ℝ}
    (hg : ∀ t, g t = κ • i t + fun _ => k) :
    EulerGap 𝔼 σ ν ρ c g i infl ↔ EulerLinear 𝔼 σ ((ν - σ) * κ) ρ c i infl := by
  unfold EulerGap EulerLinear
  refine forall_congr' fun t => ?_
  have h : (ν - σ) • (𝔼.E t (g (t + 1)) - g t) = ((ν - σ) * κ) • (𝔼.E t (i (t + 1)) - i t) := by
    rw [hg (t + 1), hg t, map_add, map_smul, 𝔼.const, mul_smul, smul_sub κ]
    congr 1
    abel
  rw [h]

/-- Galí (2015), eq. (47), p. 39: with goods-market clearing `y = c`, (46) in consumption is
(47) in output. -/
theorem eq47_of_clearing {σ ϖ ρ : ℝ} {c y i infl : ℕ → Ω → ℝ} (hyc : y = c) :
    EulerLinear 𝔼 σ ϖ ρ y i infl ↔ EulerLinear 𝔼 σ ϖ ρ c i infl := by
  rw [hyc]

/-! ### Eq. (48): the price level -/

/-- Galí (2015), p. 39 (the algebra behind (48)): with `y = Θ q`, `i = −η⁻¹(1 − Θ) q`
(`q = m − p`), and `Δ = E_t m_{t+1} − m_t`, `π̄ = E_t p_{t+1} − p_t = Δ − (E_t q_{t+1} − q_t)`,
the Euler equation (47) (deviations) at a node is equivalent to
`(1 − Θ + B) q_t = B E_t q_{t+1} − η Δ`, `B = η + ϖ(1 − Θ) − σ Θ η`. -/
theorem real_balance_eq_iff_real {σ η ϖ Θ qt Eq Em mt : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) :
    Θ * qt = Θ * Eq - σ⁻¹ * (-(1 / η) * (1 - Θ) * qt - ((Em - Eq) - (mt - qt))
      - ϖ * (-(1 / η) * (1 - Θ) * Eq - -(1 / η) * (1 - Θ) * qt)) ↔
    (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt
      = (η + ϖ * (1 - Θ) - σ * Θ * η) * Eq - η * (Em - mt) := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt)]
  have key : Θ * qt - (Θ * Eq - σ⁻¹ * (-(1 / η) * (1 - Θ) * qt - ((Em - Eq) - (mt - qt))
      - ϖ * (-(1 / η) * (1 - Θ) * Eq - -(1 / η) * (1 - Θ) * qt)))
      = -(σ * η)⁻¹ * ((1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt
        - ((η + ϖ * (1 - Θ) - σ * Θ * η) * Eq - η * (Em - mt))) := by
    field_simp
    ring
  rw [key, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right (inv_ne_zero (mul_ne_zero hσ hη))]

/-- Galí (2015), p. 39 (the algebra behind (48)): for `d ≠ 0`, `d q = B E − η Δ` iff
`q = (B/d) E − (η/d) Δ`. -/
theorem solve_forward {d B q E η Δ : ℝ} (hd : d ≠ 0) :
    d * q = B * E - η * Δ ↔ q = B / d * E + -(η / d) * Δ := by
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), p. 39 (the algebra behind (48)): given (44), (45) with `q = m − p`,
`π_{t+1} = p_{t+1} − p_t` and an adapted `p`, the Euler equation (47) in deviations holds
iff real balances satisfy `q_t = a E_t q_{t+1} + u_t` with
`a = B/(1 − Θ + B)` and `u_t = −η/(1 − Θ + B) (E_t m_{t+1} − m_t)`. -/
theorem real_balance_eq_iff {σ η ϖ Θ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (hB : 1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η) ≠ 0) {m p y i infl : ℕ → Ω → ℝ}
    (hpA : 𝔼.Adapted p) (h44 : ∀ t, y t = Θ • (m t - p t))
    (h45 : ∀ t, i t = (-(1 / η) * (1 - Θ)) • (m t - p t))
    (hπ : ∀ t, infl (t + 1) = p (t + 1) - p t) :
    EulerLinear 𝔼 σ ϖ 0 y i infl ↔ ∀ t, (fun t => m t - p t) t =
      ((η + ϖ * (1 - Θ) - σ * Θ * η) / (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η))) •
        𝔼.E t ((fun t => m t - p t) (t + 1)) +
      (-(η / (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)))) • (𝔼.E t (m (t + 1)) - m t) := by
  unfold EulerLinear
  refine forall_congr' fun t => ?_
  rw [h44 t, h44 (t + 1), h45 t, h45 (t + 1), hπ t]
  simp only [map_sub, map_smul, hpA t, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_zero]
  have hiff := real_balance_eq_iff_real (ϖ := ϖ) (Θ := Θ) (qt := m t ω - p t ω)
    (Eq := 𝔼.E t (m (t + 1)) ω - 𝔼.E t (p (t + 1)) ω) (Em := 𝔼.E t (m (t + 1)) ω)
    (mt := m t ω) hσ hη
  have e : 𝔼.E t (p (t + 1)) ω - p t ω = (𝔼.E t (m (t + 1)) ω
      - (𝔼.E t (m (t + 1)) ω - 𝔼.E t (p (t + 1)) ω)) - (m t ω - (m t ω - p t ω)) := by ring
  rw [e, hiff]
  exact solve_forward hB

/-- Galí (2015), (48) p. 39: the forward series of real balances is adapted:
`E_t` of the date-`t` forward series is itself (uses `E_tsum`). -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ a ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg ha0 k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω = _
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, ExpectationSystem.E_E_self, Pi.smul_apply, smul_eq_mul]

/-- Galí (2015), (48) p. 39: the forcing term `u_t = c (E_t m_{t+1} − m_t)` of the
real-balance equation is adapted and bounded when money growth is bounded. -/
theorem forcing_bounded_adapted {M c : ℝ} {m : ℕ → Ω → ℝ} (hmA : 𝔼.Adapted m)
    (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M) :
    (∀ t ω, |(c • (𝔼.E t (m (t + 1)) - m t)) ω| ≤ |c| * M) ∧
      𝔼.Adapted (fun t => c • (𝔼.E t (m (t + 1)) - m t)) := by
  have hE : ∀ t, 𝔼.E t (m (t + 1)) - m t = 𝔼.E t (m (t + 1) - m t) := by
    intro t
    rw [map_sub, hmA t]
  constructor
  · intro t ω
    rw [hE t, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => hΔ t ω') t ω) (abs_nonneg c)
  · intro t
    simp only
    rw [hE t, map_smul, ExpectationSystem.E_E_self]

/-- Galí (2015), (48) p. 39: the forward series of the forcing term, rewritten with expected
money growth: `∑ aᵏ E_t u_{t+k} = c ∑ aᵏ E_t Δm_{t+k+1}`. -/
theorem forwardSeries_money (a c : ℝ) {m : ℕ → Ω → ℝ} (hmA : 𝔼.Adapted m) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun t => c • (𝔼.E t (m (t + 1)) - m t)) t ω
      = c * ∑' k, a ^ k * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
  unfold ExpectationSystem.forwardSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h : 𝔼.E t (c • (𝔼.E (t + k) (m (t + k + 1)) - m (t + k)))
      = c • 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') := by
    rw [map_smul, map_sub, 𝔼.tower (Nat.le_add_right t k), ← hmA (t + k),
      𝔼.tower (Nat.le_add_right t k), hmA (t + k), ← map_sub]
    rfl
  rw [h, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (48), p. 39 (**uniqueness**): in the log-linear model (44), (45), (47)
(deviations, `a = 0`) with `σ, η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`, `α + φ ≥ 0`, adapted money
`m` with bounded growth, every adapted price level with bounded real balances `m − p` is
`p_t = m_t + η/(η + ϖΛ) ∑_{k≥1} ((η + ϖΛ)/(1 − Θ + η + ϖΛ))ᵏ E_t Δm_{t+k}`
(the sum written with index `k + 1`, `k ≥ 0`). -/
theorem price_level_48 {σ η ϖ φ α M : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hD : 0 < bigD σ φ α)
    (hϖ : 0 ≤ ϖ) (hα : α < 1) (hαφ : 0 ≤ α + φ) {m p y i infl : ℕ → Ω → ℝ}
    (hmA : 𝔼.Adapted m) (hpA : 𝔼.Adapted p) (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M)
    (h44 : ∀ t, y t = Theta ϖ η σ φ α • (m t - p t))
    (h45 : ∀ t, i t = (-(1 / η) * (1 - Theta ϖ η σ φ α)) • (m t - p t))
    (hπ : ∀ t, infl (t + 1) = p (t + 1) - p t) (h47 : EulerLinear 𝔼 σ ϖ 0 y i infl)
    (hqb : BoundedProc (fun t => m t - p t)) (t : ℕ) (ω : Ω) :
    p t ω = m t ω + η / (η + ϖ * Lambda ϖ η σ φ α) * ∑' k,
      ((η + ϖ * Lambda ϖ η σ φ α) / (1 - Theta ϖ η σ φ α + (η + ϖ * Lambda ϖ η σ φ α))) ^ (k + 1)
        * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
  set Θ := Theta ϖ η σ φ α with hΘ
  set Λ := Lambda ϖ η σ φ α with hΛ
  have hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0 := by
    have := mul_pos hη hD
    have := mul_nonneg hϖ (show (0 : ℝ) ≤ 1 - α by linarith)
    linarith
  have hTh := Theta_mem hη hD hϖ hα
  have hL : 0 ≤ Λ := Lambda_nonneg hη hD hϖ hα hαφ
  have hBid := coef_identity (σ := σ) (φ := φ) hK
  set B := η + ϖ * Λ with hBdef
  have hB0 : 0 < B := by have := mul_nonneg hϖ hL; linarith
  have hden : 0 < 1 - Θ + B := by linarith [hTh.2]
  have hr := (real_balance_eq_iff 𝔼 hσ.ne' hη.ne' (by rw [hBid]; exact hden.ne') hpA
    h44 h45 hπ).1 h47
  rw [hBid] at hr
  set a := B / (1 - Θ + B) with ha
  have ha0 : 0 ≤ a := div_nonneg hB0.le hden.le
  have ha1 : a < 1 := (div_lt_one hden).2 (by linarith [hTh.2])
  obtain ⟨hub, huA⟩ := forcing_bounded_adapted 𝔼 (c := -(η / (1 - Θ + B))) hmA hΔ
  have hq := 𝔼.eq_forwardSeries ha0 ha1 hub huA hr hqb
  have hqt := congrFun (congrFun hq t) ω
  simp only [Pi.sub_apply] at hqt
  rw [forwardSeries_money 𝔼 a _ hmA t ω] at hqt
  have hp : p t ω = m t ω + η / (1 - Θ + B) *
      ∑' k, a ^ k * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
    linarith
  rw [hp, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [pow_succ, ha]
  field_simp

/-- Galí (2015), eq. (48), p. 39 (**existence**): under the hypotheses of `price_level_48`
the price level `p_t = m_t − q_t`, with `q` the forward series of the real-balance equation,
is adapted, has bounded real balances, and with `y`, `i`, `π` from (44), (45) satisfies the
Euler equation (47); it is therefore the unique such equilibrium. -/
theorem price_level_48_exists {σ η ϖ φ α M : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ) (hα : α < 1) (hαφ : 0 ≤ α + φ) {m : ℕ → Ω → ℝ}
    (hmA : 𝔼.Adapted m) (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M) :
    ∃ p : ℕ → Ω → ℝ, 𝔼.Adapted p ∧ BoundedProc (fun t => m t - p t) ∧
      EulerLinear 𝔼 σ ϖ 0 (fun t => Theta ϖ η σ φ α • (m t - p t))
        (fun t => (-(1 / η) * (1 - Theta ϖ η σ φ α)) • (m t - p t))
        (fun t => match t with
          | 0 => 0
          | s + 1 => p (s + 1) - p s) := by
  set Θ := Theta ϖ η σ φ α with hΘ
  set Λ := Lambda ϖ η σ φ α with hΛ
  have hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0 := by
    have := mul_pos hη hD
    have := mul_nonneg hϖ (show (0 : ℝ) ≤ 1 - α by linarith)
    linarith
  have hTh := Theta_mem hη hD hϖ hα
  have hL : 0 ≤ Λ := Lambda_nonneg hη hD hϖ hα hαφ
  have hBid := coef_identity (σ := σ) (φ := φ) hK
  have hB0 : 0 < η + ϖ * Λ := by have := mul_nonneg hϖ hL; linarith
  have hden : 0 < 1 - Θ + (η + ϖ * Λ) := by linarith [hTh.2]
  set a := (η + ϖ * Λ) / (1 - Θ + (η + ϖ * Λ)) with ha
  have ha0 : 0 ≤ a := div_nonneg hB0.le hden.le
  have ha1 : a < 1 := (div_lt_one hden).2 (by linarith [hTh.2])
  obtain ⟨hub, huA⟩ := forcing_bounded_adapted 𝔼 (c := -(η / (1 - Θ + (η + ϖ * Λ)))) hmA hΔ
  set u := fun t => (-(η / (1 - Θ + (η + ϖ * Λ)))) • (𝔼.E t (m (t + 1)) - m t) with hu
  set q := 𝔼.forwardSeries a u with hq
  have hqA : 𝔼.Adapted q := forwardSeries_adapted 𝔼 ha0 ha1 hub
  refine ⟨fun t => m t - q t, ?_, ?_, ?_⟩
  · intro t
    simp only
    rw [map_sub, hmA t, hqA t]
  · have hb := 𝔼.forwardSeries_bounded ha0 ha1 hub
    have e : (fun t => m t - (fun t => m t - q t) t) = q := by
      funext t
      simp
    rw [e]
    exact hb
  · have hpA : 𝔼.Adapted (fun t => m t - q t) := by
      intro t
      simp only
      rw [map_sub, hmA t, hqA t]
    refine (real_balance_eq_iff 𝔼 hσ.ne' hη.ne' (by rw [hBid]; exact hden.ne') hpA
      (fun t => rfl) (fun t => rfl) (fun t => rfl)).2 ?_
    rw [hBid]
    intro t
    have hs := 𝔼.forwardSeries_solves ha0 ha1 hub huA t
    have e : ∀ s, m s - (m s - q s) = q s := fun s => sub_sub_cancel _ _
    simp only [e]
    exact hs

/-! ### The real wage after a monetary shock (pp. 39–40) -/

/-- Galí (2015), pp. 39–40: with technology unchanged, two equilibria (e.g. before and after a
monetary shock) on the labour demand schedule `ω = a − α n + log(1 − α)` with
`y = a + (1 − α) n` satisfy `ω₁ − ω₂ = −(α/(1 − α))(y₁ − y₂)`, so
`(ω₁ − ω₂)(y₁ − y₂) ≤ 0`: the real wage is (weakly) countercyclical. -/
theorem real_wage_countercyclical {α a n₁ n₂ y₁ y₂ w₁ w₂ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hd₁ : w₁ = a - α * n₁ + Real.log (1 - α)) (hd₂ : w₂ = a - α * n₂ + Real.log (1 - α))
    (hy₁ : y₁ = a + (1 - α) * n₁) (hy₂ : y₂ = a + (1 - α) * n₂) :
    w₁ - w₂ = -(α / (1 - α)) * (y₁ - y₂) ∧ (w₁ - w₂) * (y₁ - y₂) ≤ 0 := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have e : w₁ - w₂ = -(α / (1 - α)) * (y₁ - y₂) := by
    rw [hd₁, hd₂, hy₁, hy₂]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 ≤ α / (1 - α) := div_nonneg hα0 (by linarith)
  nlinarith [sq_nonneg (y₁ - y₂)]

/-- Galí (2015), pp. 39–40: for `0 < α < 1`, a monetary shock that changes output
moves the real wage in the opposite direction: `(ω₁ − ω₂)(y₁ − y₂) < 0`. -/
theorem real_wage_strictly_countercyclical {α a n₁ n₂ y₁ y₂ w₁ w₂ : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hd₁ : w₁ = a - α * n₁ + Real.log (1 - α))
    (hd₂ : w₂ = a - α * n₂ + Real.log (1 - α)) (hy₁ : y₁ = a + (1 - α) * n₁)
    (hy₂ : y₂ = a + (1 - α) * n₂) (hy : y₁ ≠ y₂) : (w₁ - w₂) * (y₁ - y₂) < 0 := by
  obtain ⟨e, -⟩ := real_wage_countercyclical hα0.le hα1 hd₁ hd₂ hy₁ hy₂
  rw [e]
  have : 0 < α / (1 - α) := div_pos hα0 (by linarith)
  have : 0 < (y₁ - y₂) ^ 2 := by
    have : y₁ - y₂ ≠ 0 := sub_ne_zero.2 hy
    positivity
  nlinarith

/-- Galí (2015), pp. 39–40 (**the claim needs `α > 0`**): with `α = 0` the labour demand
schedule is flat and the real wage does not move at all after a monetary shock. -/
theorem real_wage_acyclical_of_alpha_zero {a n₁ n₂ w₁ w₂ : ℝ}
    (hd₁ : w₁ = a - 0 * n₁ + Real.log (1 - 0)) (hd₂ : w₂ = a - 0 * n₂ + Real.log (1 - 0)) :
    w₁ = w₂ := by
  rw [hd₁, hd₂]
  ring

end Gali.ClassicalMonetaryModel.MIUNonseparable
