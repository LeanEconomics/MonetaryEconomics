/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfBridge

/-!
# Chapter 6 welfare machinery for Chapter 7 (III): transactions frictions

Woodford (2003), *Interest and Prices*, Chapter 6, §§1–2 and §4.1 (pp. 383–405, 420–426) and
Appendix E.1–E.4 (pp. 692–699): the second-order welfare machinery that Chapter 7 uses
("the approximation to welfare of Chapter 6", Woodford (2003), p. 471, fn. 6), restated from
the Woodford Chapter 6 StabilizationWelfare project with the namespace renamed (the original
module names are kept as nested namespaces; that project's Sequences is SeqW here).
Only the declarations needed by the Chapter 7 welfare bridge are copied; proofs are verbatim.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfFrictions

open Woodford.GainsFromCommitment.TidyR6WelfBase
open Woodford.GainsFromCommitment.TidyR6WelfBridge

namespace Transactions

open Filter Topology Asymptotics
open Moments (calvoK)
/-- Woodford (2003), Assumption 6.1, p. 422: satiation in real balances at the finite level
`m̄ > 0` (for output `Ȳ`); the second partial derivatives have finite limits as `m → m̄` from
below, and the limit of u_mm from below is negative. `um m` is `u_m(Ȳ, m)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
structure Assumption61 where
  /-- The satiation level of real balances `m̄`. -/
  mbar : ℝ
  /-- `u_m(Ȳ, m)` as a function of `m`. -/
  um : ℝ → ℝ
  /-- `u_mm(Ȳ, m)` for `m < m̄`. -/
  umm : ℝ → ℝ
  /-- The left limit `u_mm(m̄−)`. -/
  ummL : ℝ
  /-- `u_cm(Ȳ, m)` for `m < m̄`. -/
  ucm : ℝ → ℝ
  /-- The left limit `u_cm(m̄−)`. -/
  ucmL : ℝ
  /-- The marginal utility of expenditure at satiation. -/
  uc : ℝ
  /-- `m̄ > 0`. -/
  mbar_pos : 0 < mbar
  /-- `u_c > 0`. -/
  uc_pos : 0 < uc
  /-- Below satiation, money has positive marginal utility. -/
  um_pos : ∀ m, m < mbar → 0 < um m
  /-- At and above satiation, `u_m = 0`. -/
  um_sat : ∀ m, mbar ≤ m → um m = 0
  /-- u_m is continuous at `m̄` from below. -/
  um_cont : ContinuousWithinAt um (Set.Iic mbar) mbar
  /-- u_mm is the derivative of u_m below satiation. -/
  hasDerivAt_um : ∀ m, m < mbar → HasDerivAt um (umm m) m
  /-- The finite left limit of u_mm. -/
  umm_tendsto : Tendsto umm (𝓝[<] mbar) (𝓝 ummL)
  /-- The finite left limit of u_cm. -/
  ucm_tendsto : Tendsto ucm (𝓝[<] mbar) (𝓝 ucmL)
  /-- `u_mm(m̄−) < 0`. -/
  ummL_neg : ummL < 0

namespace Assumption61

variable (A : Assumption61)

/-- Woodford (2003), p. 422: the limiting interest semi-elasticity of money demand,
`η_i = −u_c/(m̄ u_mm)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def etaI : ℝ := -A.uc / (A.mbar * A.ummL)

end Assumption61

/-- Woodford (2003), §4.1 and App. E.4: the structural coefficients entering (4.1)–(4.9):
`σ⁻¹`, `ω`, `θ⁻¹`, `χ = m̄u_cm/u_c`, `η_i`, `v̄ = Ȳ/m̄` and the money-demand income elasticity
`η_y`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
structure TxParams where
  /-- `σ⁻¹`. -/
  sigInv : ℝ
  /-- `ω`, the elasticity of real marginal cost with respect to own output. -/
  omega : ℝ
  /-- `θ⁻¹`, the inverse elasticity of substitution between goods. -/
  thetaInv : ℝ
  /-- `χ = m̄ u_cm / u_c`. -/
  chi : ℝ
  /-- `η_i`, the interest semi-elasticity of money demand. -/
  etaI : ℝ
  /-- `v̄ = Ȳ/m̄`, steady-state velocity. -/
  vbar : ℝ
  /-- `η_y`, the income elasticity of money demand. -/
  etaY : ℝ

/-- Woodford (2003), App. E.4: a point of the expansion: the endogenous variables `Ŷ`,
`d = î − îᵐ`, `V = var_i ŷ(i)`, the money-demand residual `r` of (4.1) (footnote 4, p. 700: of
second order), the exogenous `g`, `q`, `ε^m`, the distortions `Φ_y`, `Δ̄`, and the coefficient
gaps `e₂ = s_mσ_m⁻¹ − (η_i v̄)⁻¹`, `e₃ = η_y − χη_i v̄` (both `O(Δ̄)` by (E.16)).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
structure TxPoint where
  /-- `Ŷ_t`. -/
  Y : ℝ
  /-- `î_t − î_tᵐ`. -/
  d : ℝ
  /-- g_t. -/
  g : ℝ
  /-- q_t. -/
  q : ℝ
  /-- `ε_tᵐ`. -/
  eps : ℝ
  /-- `Φ_y`. -/
  Phi : ℝ
  /-- `Δ̄`. -/
  Delta : ℝ
  /-- `var_i ŷ_t(i)`. -/
  V : ℝ
  /-- The residual of the log-linear money demand (4.1). -/
  r : ℝ
  /-- `e₂ = s_m σ_m⁻¹ − (η_i v̄)⁻¹`. -/
  e2 : ℝ
  /-- `e₃ = η_y − χ η_i v̄`. -/
  e3 : ℝ

variable (P : TxParams)

/-- Woodford (2003), eq. (4.3), p. 420: `Ω_mc = σ⁻¹ + ω − χ η_y`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def omegaMC : ℝ := P.sigInv + P.omega - P.chi * P.etaY

/-- Woodford (2003), eq. (4.5), p. 420: `Ŷⁿ = (σ⁻¹g + ωq + χ εᵐ)/Ω_mc`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def natRate (g q eps : ℝ) : ℝ :=
  (P.sigInv * g + P.omega * q + P.chi * eps) / omegaMC P

/-- Woodford (2003), (E.15) p. 699 with the consistent normalisation (survey error 20):
`s_m = Δ̄/v̄`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def sM (Δ : ℝ) : ℝ := Δ / P.vbar

/-- Woodford (2003), eq. (4.6), p. 421: `x* = (Φ_y + s_m η_y)/Ω_mc`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def xStar (Φ Δ : ℝ) : ℝ := (Φ + sM P Δ * P.etaY) / omegaMC P

/-- Woodford (2003), eq. (4.1), p. 420: `m̂ = η_y Ŷ − η_i(î − îᵐ) + εᵐ` plus the residual `r`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def mHat (x : TxPoint) : ℝ := P.etaY * x.Y - P.etaI * x.d + x.eps + x.r

/-- Woodford (2003), (E.5) p. 694: `E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def mOne (x : TxPoint) : ℝ := x.Y - (1 - P.thetaInv) / 2 * x.V

/-- Woodford (2003), p. 700: `s_m σ_m⁻¹ = (η_i v̄)⁻¹ + e₂`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def smSig (x : TxPoint) : ℝ := 1 / (P.etaI * P.vbar) + x.e2

/-- Woodford (2003), eq. (E.15), p. 699: the second-order expansion of `u(Y, m; ξ)` (divided
by `Ȳu_c`, policy-independent terms omitted).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def uTaylor (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * mHat P x +
    (sM P x.Delta - smSig P x) / 2 * mHat P x ^ 2 + P.chi * mHat P x * x.Y +
    sM P x.Delta * P.sigInv * x.g * mHat P x +
    (sM P x.Delta * P.chi + smSig P x) * x.eps * mHat P x

/-- Woodford (2003), eq. (E.17), p. 700.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def uE17 (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * mHat P x +
    P.chi * mHat P x * x.Y - 1 / (P.etaI * P.vbar) / 2 * (mHat P x - x.eps) ^ 2

/-- Woodford (2003), eq. (E.18), p. 700.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def uE18 (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * P.etaY * x.Y -
    sM P x.Delta * P.etaI * x.d + P.chi * P.etaY / 2 * x.Y ^ 2 + P.chi * x.eps * x.Y -
    P.etaI / P.vbar / 2 * x.d ^ 2

/-- Woodford (2003), eqs. (E.3) integrated over goods, p. 694: the disutility of supply in
terms of `E_i ŷ` and `E_i ŷ² = (E_i ŷ)² + var_i ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vTaylor (x : TxPoint) : ℝ :=
  (1 - x.Phi) * mOne P x + (1 + P.omega) / 2 * (mOne P x ^ 2 + x.V) - P.omega * x.q * mOne P x

/-- Woodford (2003), eq. (E.4), p. 694.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vE4 (x : TxPoint) : ℝ :=
  (1 - x.Phi) * x.Y + (1 + P.omega) / 2 * x.Y ^ 2 - P.omega * x.q * x.Y +
    (P.thetaInv + P.omega) / 2 * x.V

/-- Woodford (2003), eq. (4.9), p. 422 / (E.14): the quadratic form
`Ω_mc (x − x*)² + v̄⁻¹η_i(î − îᵐ + Δ̄)² + (θ⁻¹ + ω) var_i ŷ` with `x = Ŷ − Ŷⁿ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def loss49 (x : TxPoint) : ℝ :=
  omegaMC P * (x.Y - natRate P x.g x.q x.eps - xStar P x.Phi x.Delta) ^ 2 +
    P.etaI / P.vbar * (x.d + x.Delta) ^ 2 + (P.thetaInv + P.omega) * x.V

/-- Woodford (2003), (4.9): the terms independent of policy, an explicit function of the
exogenous disturbances `g, q, εᵐ` and the distortions `Φ_y, Δ̄` only.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def tip (g q eps Φ Δ : ℝ) : ℝ :=
  omegaMC P / 2 * (natRate P g q eps + xStar P Φ Δ) ^ 2 + P.etaI / P.vbar / 2 * Δ ^ 2 +
    Δ / P.vbar * eps + eps ^ 2 / (2 * (P.etaI * P.vbar))

/-- The s_m-terms dropped between (E.15) and (E.17), with the money residual scaled by `s`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remA (s : ℝ) (x : TxPoint) : ℝ :=
  x.Delta / P.vbar * ((P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) ^ 2 / 2 +
    P.sigInv * x.g * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) +
    P.chi * x.eps * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r))

/-- The `e₂`-terms dropped between (E.15) and (E.17).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remB (s : ℝ) (x : TxPoint) : ℝ :=
  x.e2 * (x.eps * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) -
    (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) ^ 2 / 2)

/-- The money-demand-residual terms produced in (E.18).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remC (s : ℝ) (x : TxPoint) : ℝ :=
  x.Delta / P.vbar * x.r + P.chi * x.r * x.Y -
    1 / (P.etaI * P.vbar) * (P.etaY * x.Y - P.etaI * x.d) * x.r -
    1 / (P.etaI * P.vbar) / 2 * s * x.r ^ 2

/-- The `e₃`-terms produced by writing `χη_iv̄` for `η_y` in quadratic coefficients (p. 700).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remD (x : TxPoint) : ℝ :=
  x.e3 * (1 / (P.etaI * P.vbar) * P.etaI * x.d * x.Y -
    1 / (P.etaI * P.vbar) / 2 * P.etaY * x.Y ^ 2)

/-- The terms dropped between (E.3) and (E.4) (using (E.5)).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remE (s : ℝ) (x : TxPoint) : ℝ :=
  x.Phi * ((1 - P.thetaInv) / 2) * x.V - (1 + P.omega) * ((1 - P.thetaInv) / 2) * x.Y * x.V +
    (1 + P.omega) / 2 * ((1 - P.thetaInv) / 2) ^ 2 * s * x.V ^ 2 +
    P.omega * x.q * ((1 - P.thetaInv) / 2) * x.V

/-- Woodford (2003), (4.9): the explicit remainder `O(‖Φ, ŷ, Δ̂, ξ̃‖³)`, written along the ray
of scale `s` (`remainder P 1` is the remainder itself; see remainder_scale).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def remainder (s : ℝ) (x : TxPoint) : ℝ :=
  remA P s x + remB P s x + remC P s x + remD P x - remE P s x

/-- Woodford (2003), (E.15) ⟶ (E.17), pp. 699–700: dropping the `O(Δ̄)` quadratic coefficients
leaves the explicit cubic terms `remA + remB` and the policy-independent `(εᵐ)²/(2η_iv̄)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem E15_to_E17 (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint) :
    uTaylor P x = uE17 P x + x.eps ^ 2 / (2 * (P.etaI * P.vbar)) + remA P 1 x + remB P 1 x := by
  simp only [uTaylor, uE17, remA, remB, smSig, sM, mHat]
  field_simp
  ring

/-- Woodford (2003), (E.17) ⟶ (E.18), p. 700: substituting the money demand (4.1); the
`χ m̂ Ŷ` cross terms cancel exactly against those of `−½(η_iv̄)⁻¹(m̂ − εᵐ)²` once
`η_y = χη_i v̄ + e₃`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem E17_to_E18 (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint)
    (he3 : P.etaY = P.chi * P.etaI * P.vbar + x.e3) :
    uE17 P x = uE18 P x + x.Delta / P.vbar * x.eps + remC P 1 x + remD P x := by
  simp only [uE17, uE18, remC, remD, sM, mHat]
  rw [he3]
  field_simp
  ring

/-- Woodford (2003), (E.3) ⟶ (E.4), p. 694: integrating over goods and using (E.5).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem E3_to_E4 (x : TxPoint) : vTaylor P x = vE4 P x + remE P 1 x := by
  simp only [vTaylor, vE4, remE, mOne]
  ring

/-- Woodford (2003), App. E.4, last display p. 700: (E.18) minus (E.4) is EXACTLY
`−½[Ω_mc(x − x*)² + v̄⁻¹η_i(î − îᵐ + Δ̄)² + (θ⁻¹+ω)var_i ŷ]` plus policy-independent terms,
given the consistent normalisation `s_m = Δ̄/v̄`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem E18_minus_E4 (hΩ : omegaMC P ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint) :
    uE18 P x - vE4 P x = -loss49 P x / 2 +
      (omegaMC P / 2 * (natRate P x.g x.q x.eps + xStar P x.Phi x.Delta) ^ 2 +
        P.etaI / P.vbar / 2 * x.Delta ^ 2) := by
  have hs : P.sigInv = omegaMC P - P.omega + P.chi * P.etaY := by unfold omegaMC; ring
  simp only [uE18, vE4, loss49, natRate, xStar, sM]
  rw [hs]
  field_simp
  ring

/-- Woodford (2003), Proposition 6.7, eq. (4.9), p. 422 (proof (E.15)–(E.18), pp. 698–700),
Layer A: the period utility expansion (E.15) minus the disutility expansion (E.3) equals
`−½ × (4.9)` plus terms independent of policy (`tip`, a function of `g, q, εᵐ, Φ_y, Δ̄` only)
plus the explicit remainder `remainder P 1 x`, of weighted degree `≥ 3` (remainder_scale).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop_6_7_layerA (hΩ : omegaMC P ≠ 0) (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0)
    (x : TxPoint) (he3 : P.etaY = P.chi * P.etaI * P.vbar + x.e3) :
    uTaylor P x - vTaylor P x =
      -loss49 P x / 2 + tip P x.g x.q x.eps x.Phi x.Delta + remainder P 1 x := by
  rw [E15_to_E17 P hi hv, E17_to_E18 P hi hv x he3, E3_to_E4]
  have h := E18_minus_E4 P hΩ hv x
  simp only [tip, remainder]
  linear_combination h

/-- Woodford (2003), eq. (4.8), p. 421: `κ = (1−α)(1−αβ)/α · Ω_mc/(1+ωθ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def kappaCalvo (α β θ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * omegaMC P / (1 + P.omega * θ)

/-- Woodford (2003), eq. (4.11), p. 423: `λ_x = κ/θ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lambdaX (α β θ : ℝ) : ℝ := kappaCalvo P α β θ / θ

/-- Woodford (2003), eq. (4.11), p. 423: `λ_i = η_i λ_x/(v̄ Ω_mc)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lambdaI (lx : ℝ) : ℝ := P.etaI * lx / (P.vbar * omegaMC P)

/-- Woodford (2003), eq. (4.10), p. 423: `L_t = π_t² + λ_x(x_t − x*)² + λ_i(î_t − îᵐ_t + Δ̄)²`;
here `xg = x_t − x*` and `dd = î_t − îᵐ_t + Δ̄`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def loss410 (α β θ infl xg dd : ℝ) : ℝ :=
  infl ^ 2 + lambdaX P α β θ * xg ^ 2 + lambdaI P (lambdaX P α β θ) * dd ^ 2

/-- Woodford (2003), (4.11), p. 423: `λ_x > 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lambdaX_pos {α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hθ : 0 < θ) (hω : 0 ≤ P.omega) (hΩ : 0 < omegaMC P) : 0 < lambdaX P α β θ := by
  unfold lambdaX kappaCalvo
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < 1 + P.omega * θ := by nlinarith
  have h3 : 0 < 1 - α := by linarith
  positivity

/-- Woodford (2003), Proposition 6.8, (4.10)–(4.11), p. 423, with genuine discounted sums.
Given the discounted sums of the (expected) per-period terms `X2 t = (x_t − x*)²`,
`I2 t = (î_t − îᵐ_t + Δ̄)²`, `P2 t = π_t²`, and the Calvo dispersion relation of Props. 6.3/6.4
(restated as the hypothesis hV: `Σβᵗ var_i ŷ_t = θ²(ψ Σβᵗ π_t² + T₀)`, `T₀` independent of
policy), the discounted sum of the bracket of (4.9) equals `Λ Σβᵗ L_t + t.i.p.` with
`Λ = θ(1+ωθ)ψ > 0` and L_t the loss (4.10) with the weights (4.11).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop_6_8 {α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ)
    (hθi : P.thetaInv = 1 / θ) (hω : 0 ≤ P.omega) (hΩ : 0 < omegaMC P) (hv : P.vbar ≠ 0)
    {X2 I2 P2 V : ℕ → ℝ} {A B Sπ T0 : ℝ} (hX : HasSum (fun t => β ^ t * X2 t) A)
    (hI : HasSum (fun t => β ^ t * I2 t) B) (hP : HasSum (fun t => β ^ t * P2 t) Sπ)
    (hV : HasSum (fun t => β ^ t * V t) (θ ^ 2 * (calvoK α β * Sπ + T0))) :
    HasSum (fun t => β ^ t * (omegaMC P * X2 t + P.etaI / P.vbar * I2 t +
        (P.thetaInv + P.omega) * V t))
      (θ * (1 + P.omega * θ) * calvoK α β *
          (Sπ + lambdaX P α β θ * A + lambdaI P (lambdaX P α β θ) * B) +
        (P.thetaInv + P.omega) * θ ^ 2 * T0) ∧
    HasSum (fun t => β ^ t * (P2 t + lambdaX P α β θ * X2 t +
        lambdaI P (lambdaX P α β θ) * I2 t))
      (Sπ + lambdaX P α β θ * A + lambdaI P (lambdaX P α β θ) * B) := by
  have hαβ : α * β < 1 := by nlinarith
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 : (1 + P.omega * θ) ≠ 0 := by nlinarith
  have h3 : (1 - α) ≠ 0 := by linarith
  have hΩ' := hΩ.ne'
  have hθ' := hθ.ne'
  have hα' := hα0.ne'
  have hsum := ((hX.mul_left (omegaMC P)).add (hI.mul_left (P.etaI / P.vbar))).add
    (hV.mul_left (P.thetaInv + P.omega))
  have hsum2 := (hP.add (hX.mul_left (lambdaX P α β θ))).add
    (hI.mul_left (lambdaI P (lambdaX P α β θ)))
  refine ⟨?_, ?_⟩
  · convert hsum using 1
    · funext t; ring
    · simp only [lambdaI, lambdaX, kappaCalvo, calvoK]
      rw [hθi]
      field_simp
      ring
  · convert hsum2 using 1
    funext t; ring

end Transactions

namespace BridgeExtensions

open Filter Topology Asymptotics
open ExpLogCES (crossMean crossVar expRem rlog)
variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-- Woodford (2003), (2.11), p. 395 (orders along any filter): `O(sᵐ) · O(sⁿ) = O(sᵐ⁺ⁿ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem o_mul {f g : B → ℝ} {m n k : ℕ} (hf : f =O[L] fun b => s b ^ m)
    (hg : g =O[L] fun b => s b ^ n) (hk : m + n = k) :
    (fun b => f b * g b) =O[L] fun b => s b ^ k := by
  subst hk
  exact (hf.mul hg).congr_right fun b => by ring

/-- Woodford (2003), (2.11), p. 395 (orders along any filter): `O(sⁿ) ⊆ O(sᵐ)` for `m ≤ n`
when `s → 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem o_weaken (hs : Tendsto s L (𝓝 0)) {f : B → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hf : f =O[L] fun b => s b ^ n) : f =O[L] fun b => s b ^ m := by
  refine hf.trans ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h1 : (fun b => s b ^ k) =O[L] (fun _ => (1 : ℝ)) := (hs.pow k).isBigO_one ℝ
  have h2 := (isBigO_refl (fun b => s b ^ m) L).mul h1
  refine h2.congr (fun b => by ring) (fun b => by ring)

/-- Woodford (2003), p. 385: a first-order quantity tends to zero with the amplitude `s`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem tendsto_of_o_one (hs : Tendsto s L (𝓝 0)) {E : Type*} [NormedAddCommGroup E]
    {f : B → E} (hf : f =O[L] fun b => s b ^ 1) : Tendsto f L (𝓝 0) :=
  hf.trans_tendsto (by simpa using hs.pow 1)

/-- Woodford (2003), App. E, p. 693: powers of a first-order quantity, `fⁿ = O(sⁿ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem o_pow {f : B → ℝ} (hf : f =O[L] fun b => s b ^ 1) (n : ℕ) :
    (fun b => f b ^ n) =O[L] fun b => s b ^ n :=
  (hf.pow n).congr_right fun b => by ring

/-- Woodford (2003), App. E, p. 693: the exponential atom `r₃(x) = eˣ − 1 − x − x²/2` of a
first-order quantity is of third order.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem expRem_o (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} (hx : x =O[L] fun b => s b ^ 1) :
    (fun b => expRem (x b)) =O[L] fun b => s b ^ 3 := by
  have h := ExpLogCES.exp_taylor2_isBigO.comp_tendsto (tendsto_of_o_one hs hx)
  refine (h.trans (o_pow hx 3)).congr_left fun b => ?_
  simp only [Function.comp, expRem]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Woodford (2003), eq. (1.2), p. 385, along a one-parameter family with a MOVING base point:
if `U` is `C³`, the expansion points `z̄_b` converge to `z̄₀` and the deviations z_b are
`O(s)`, then `U(z̄_b + z_b) − [U(z̄_b) + DU(z̄_b) z_b + ½ D²U(z̄_b)(z_b, z_b)] = O(s³)`. The
constant is uniform because `D²U` is Lipschitz on a fixed ball around `z̄₀`. (A moving base
point is the steady state of a distorted economy whose distortion shrinks with `s`.)
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor_family_moving {U : F → ℝ} (hU : ContDiff ℝ 3 U) {z0 : F} {zb z : B → F}
    (hzb : Tendsto zb L (𝓝 z0)) (hs : Tendsto s L (𝓝 0)) (hz : z =O[L] fun b => s b ^ 1) :
    (fun b => U (zb b + z b) - ApproxTheory.quadApprox (U (zb b)) (fderiv ℝ U (zb b))
      (fderiv ℝ (fderiv ℝ U) (zb b)) (z b)) =O[L] fun b => s b ^ 3 := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) := h1.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h2.contDiffAt.exists_lipschitzOnWith (x := z0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hz0 : Tendsto z L (𝓝 0) := tendsto_of_o_one hs hz
  have hzn : (fun b => ‖z b‖ ^ 3) =O[L] fun b => s b ^ 3 :=
    (hz.norm_left.pow 3).congr_right fun b => by ring
  refine (IsBigO.of_bound K ?_).trans hzn
  filter_upwards [hzb.eventually_mem (Metric.ball_mem_nhds z0 hδ2),
    hz0.eventually_mem (Metric.ball_mem_nhds 0 hδ2)] with b hb hzb'
  have hsub : Metric.ball (zb b) (δ / 2) ⊆ Metric.ball z0 δ := by
    intro w hw
    rw [Metric.mem_ball] at hw hb ⊢
    calc dist w z0 ≤ dist w (zb b) + dist (zb b) z0 := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add hw hb
      _ = δ := by ring
  have hzb0 : zb b ∈ Metric.ball z0 δ := hsub (Metric.mem_ball_self hδ2)
  have key := ApproxTheory.taylor2_multivar_bound (U1 := fderiv ℝ U)
    (U2 := fderiv ℝ (fderiv ℝ U)) (zbar := zb b) (δ := δ / 2) K.coe_nonneg
    (fun w _ => (hU.differentiable (by norm_num) w).hasFDerivAt)
    (fun w _ => (h1.differentiable (by norm_num) w).hasFDerivAt)
    (fun w hw => by
      have := hK.dist_le_mul w (hball (hsub hw)) (zb b) (hball hzb0)
      simpa [dist_eq_norm] using this)
    (by simpa using hzb')
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
  exact key

/-- Woodford (2003), eq. (1.2), p. 385, along a one-parameter family with a fixed base point
`z̄`: `U(z̄ + z_b) − [Ū + DU z_b + ½ D²U(z_b, z_b)] = O(s³)` when `z_b = O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor_family {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) (hs : Tendsto s L (𝓝 0))
    {z : B → F} (hz : z =O[L] fun b => s b ^ 1) :
    (fun b => U (zbar + z b) - ApproxTheory.quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) (z b)) =O[L] fun b => s b ^ 3 :=
  taylor_family_moving (zb := fun _ => zbar) hU tendsto_const_nhds hs hz

/-- Woodford (2003), Assumption 6.1 and (E.15), p. 699 (ONE-SIDED expansion): if the actual
utility `U` agrees on a set `S` (e.g. `m ≤ m̄`, the region below satiation) with a `C³`
function `Ũ` (its smooth extension from that side), and the family eventually stays in `S`,
then `U` has the second-order expansion of `Ũ` along the family, with the one-sided derivatives
of `U` (those of `Ũ`) as coefficients.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor_family_of_eqOn {U Ut : F → ℝ} (hU : ContDiff ℝ 3 Ut) {S : Set F}
    (hEq : Set.EqOn U Ut S) (zbar : F) (hs : Tendsto s L (𝓝 0)) {z : B → F}
    (hz : z =O[L] fun b => s b ^ 1) (hS : ∀ᶠ b in L, zbar + z b ∈ S) :
    (fun b => U (zbar + z b) - ApproxTheory.quadApprox (Ut zbar) (fderiv ℝ Ut zbar)
      (fderiv ℝ (fderiv ℝ Ut) zbar) (z b)) =O[L] fun b => s b ^ 3 := by
  refine (taylor_family hU zbar hs hz).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hS] with b hb
  rw [hEq hb]

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2), p. 692: the marginal utility `u_c = ∂U/∂Y` at `z`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def dY (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) : ℝ := fderiv ℝ U z (1, 0)

/-- Woodford (2003), (E.2), p. 692: the second derivative `u_cc = ∂²U/∂Y²` at `z`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def dYY (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) : ℝ := fderiv ℝ (fderiv ℝ U) z (1, 0) (1, 0)

/-- Woodford (2003), (E.2), p. 692: the shock derivative `u_ξ ξ̃` at `z`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def dXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ := fderiv ℝ U z (0, ξ)

/-- Woodford (2003), (E.2), p. 692: the (symmetrised) cross derivative `u_cξ ξ̃` at `z`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def dYXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ :=
  (fderiv ℝ (fderiv ℝ U) z (1, 0) (0, ξ) + fderiv ℝ (fderiv ℝ U) z (0, ξ) (1, 0)) / 2

/-- Woodford (2003), (E.2), p. 692: the shock quadratic form `ξ̃′u_ξξ ξ̃` at `z`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def dXiXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ :=
  fderiv ℝ (fderiv ℝ U) z (0, ξ) (0, ξ)

/-- Woodford (2003), (E.2)–(E.3), pp. 692–693: on `ℝ × Ξ` the quadratic approximation of
eq. (1.2) at `(Ȳ, 0)` is exactly the book's polynomial `Prop61.uTaylor` in the level deviation
`Ỹ` with the derivatives u_c, u_cc, `u_ξξ̃`, `u_cξξ̃`, `ξ̃′u_ξξξ̃`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem quadApprox_prod (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (a : ℝ) (ξ : Ξ) :
    ApproxTheory.quadApprox (U z) (fderiv ℝ U z) (fderiv ℝ (fderiv ℝ U) z) (a, ξ) =
      Prop61.uTaylor (U z) (dY U z) (dYY U z) (dXi U z ξ) (dYXi U z ξ) (dXiXi U z ξ) a := by
  have e : ((a, ξ) : ℝ × Ξ) = a • ((1 : ℝ), (0 : Ξ)) + ((0 : ℝ), ξ) := by
    ext <;> simp
  rw [e]
  simp only [ApproxTheory.quadApprox, Prop61.uTaylor, dY, dYY, dXi, dYXi, dXiXi, map_add,
    map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2), p. 692, as an analytic statement: for `C³` utility `U(Y, ξ)` and a
family with level deviation `Ỹ_b = O(s)` and disturbance `ξ_b = O(s)`,
`U(Ȳ + Ỹ_b, ξ_b) − uTaylor(Ỹ_b) = O(s³)`, the coefficients being the actual derivatives.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uTaylor_family {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (Ybar : ℝ)
    (hs : Tendsto s L (𝓝 0)) {Yt : B → ℝ} {ξ : B → Ξ} (hY : Yt =O[L] fun b => s b ^ 1)
    (hξ : ξ =O[L] fun b => s b ^ 1) :
    (fun b => U (Ybar + Yt b, ξ b) - Prop61.uTaylor (U (Ybar, 0)) (dY U (Ybar, 0))
      (dYY U (Ybar, 0)) (dXi U (Ybar, 0) (ξ b)) (dYXi U (Ybar, 0) (ξ b))
      (dXiXi U (Ybar, 0) (ξ b)) (Yt b)) =O[L] fun b => s b ^ 3 := by
  have h := taylor_family (z := fun b => (Yt b, ξ b)) hU (Ybar, 0) hs (hY.prod_left hξ)
  refine h.congr_left fun b => ?_
  rw [quadApprox_prod]
  simp

/-- Woodford (2003), (E.2), p. 692, in log deviations: with `Y = Ȳ e^{x}` and
`Ỹ = Ȳ(x + x²/2 + r₃(x))` (`Prop61.levelDev_eq`), `U(Ȳe^{x_b}, ξ_b) − uTaylor(Ỹ_b) = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uTaylor_family_exp {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (Ybar : ℝ)
    (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} {ξ : B → Ξ} (hx : x =O[L] fun b => s b ^ 1)
    (hξ : ξ =O[L] fun b => s b ^ 1) :
    (fun b => U (Ybar * Real.exp (x b), ξ b) - Prop61.uTaylor (U (Ybar, 0)) (dY U (Ybar, 0))
      (dYY U (Ybar, 0)) (dXi U (Ybar, 0) (ξ b)) (dYXi U (Ybar, 0) (ξ b))
      (dXiXi U (Ybar, 0) (ξ b)) (Ybar * (x b + x b ^ 2 / 2 + expRem (x b))))
      =O[L] fun b => s b ^ 3 := by
  have hYt : (fun b => Ybar * (Real.exp (x b) - 1)) =O[L] fun b => s b ^ 1 := by
    have h2 := o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hx 2)
    have h3 := o_weaken hs (by norm_num : 1 ≤ 3) (expRem_o hs hx)
    refine (((hx.add (h2.const_mul_left (1 / 2))).add h3).const_mul_left Ybar).congr_left
      fun b => ?_
    rw [ExpLogCES.exp_sub_one_eq]
    ring
  refine (uTaylor_family hU Ybar hs hYt hξ).congr_left fun b => ?_
  have e1 : Ybar + Ybar * (Real.exp (x b) - 1) = Ybar * Real.exp (x b) := by ring
  have e2 : Ybar * (Real.exp (x b) - 1) = Ybar * (x b + x b ^ 2 / 2 + expRem (x b)) := by
    rw [ExpLogCES.exp_sub_one_eq]
  rw [e1, e2]

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (2.6), p. 393: `Ŷ = log(Y/Ȳ)`, the log of the Dixit–Stiglitz index
(elasticity `θ`) of the relative outputs `e^{ŷ(i)} = y(i)/Ȳ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def logYidx (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) : ℝ :=
  Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i)))

/-- Woodford (2003), App. E, p. 693: each good's `ŷ(i)` is `O(s)` when the cross-section is
`O(s)` in the sup norm.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem coord_o {yh : B → ι → ℝ} (hyh : yh =O[L] fun b => s b ^ 1) (i : ι) :
    (fun b => yh b i) =O[L] fun b => s b ^ 1 :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    rw [one_mul]; exact norm_le_pi_norm (yh b) i)).trans hyh

/-- Woodford (2003), App. E, p. 693: `E_i ŷ = O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_o {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) : (fun b => crossMean w (yh b)) =O[L] fun b => s b ^ 1 :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw0 hw1 (yh b))).trans hyh

/-- Woodford (2003), App. E, p. 693: `var_i ŷ = O(s²)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossVar_o {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) : (fun b => crossVar w (yh b)) =O[L] fun b => s b ^ 2 := by
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans
    ((hyh.norm_left.pow 2).congr_right fun b => by ring)
  have h := ExpLogCES.crossVar_le hw0 hw1 (yh b)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_pow, abs_norm]
  exact h.2

/-- Woodford (2003), (E.5), p. 694: the log output index `Ŷ` of an `O(s)` cross-section is
`O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem logYidx_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) :
    (fun b => logYidx w θ (yh b)) =O[L] fun b => s b ^ 1 := by
  have h := (ExpLogCES.log_outputIndex_expansion hw0 hw1 hθ).comp_tendsto
    (tendsto_of_o_one hs hyh)
  have h3 : (fun b => ‖yh b‖ ^ 3) =O[L] fun b => s b ^ 3 :=
    (hyh.norm_left.pow 3).congr_right fun b => by ring
  have hr := o_weaken hs (by norm_num : 1 ≤ 3) (h.trans h3)
  have hm := crossMean_o hw0 hw1 hyh
  have hv := o_weaken hs (by norm_num : 1 ≤ 2) (crossVar_o hw0 hw1 hyh)
  refine ((hr.add hm).add (hv.const_mul_left (1 / 2 * (1 - θ⁻¹)))).congr_left fun b => ?_
  simp only [Function.comp, logYidx]
  ring

/-- Woodford (2003), (E.5), p. 694: the CES atom r_C of an `O(s)` cross-section is `O(s³)`
(`Links.CES.cesAtom_isBigO` along the family).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cesAtom_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) :
    (fun b => Links.CES.cesAtom w θ (yh b)) =O[L] fun b => s b ^ 3 :=
  ((Links.CES.cesAtom_isBigO hw0 hw1 hθ).comp_tendsto (tendsto_of_o_one hs hyh)).trans
    ((hyh.norm_left.pow 3).congr_right fun b => by ring)

/-- Woodford (2003), (E.3) with `Φ` absorbed in the coefficients (§5): the remainder
`Rv 0` is `O(s³)` whenever `q, ŷ = O(s)` and its atom `r = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem Rv0_o (hs : Tendsto s L (𝓝 0)) (ω : ℝ) {q y r : B → ℝ}
    (hq : q =O[L] fun b => s b ^ 1) (hy : y =O[L] fun b => s b ^ 1)
    (hr : r =O[L] fun b => s b ^ 3) :
    (fun b => Prop61.Rv 0 ω (q b) (y b) (r b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => y b ^ 2 / 2 + r b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hy 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hr)).congr_left
      fun b => by ring
  have hB : (fun b => 2 * y b + (y b ^ 2 / 2 + r b)) =O[L] fun b => s b ^ 1 :=
    (hy.const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  have h1 := o_mul hA hB (by norm_num : 2 + 1 = 3)
  have h2 := o_mul hq hA (by norm_num : 1 + 2 = 3)
  refine ((hr.add (h1.const_mul_left (ω / 2))).sub (h2.const_mul_left ω)).congr_left
    fun b => ?_
  unfold Prop61.Rv
  ring

variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), §2, p. 394: a uniform order bound gives ONE constant for every index.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uniform_bound {J : Type*} {f : A × J → ℝ} {g : A → ℝ}
    (h : f =O[l ×ˢ (⊤ : Filter J)] fun p => g p.1) :
    ∃ C, ∀ᶠ a in l, ∀ j, |f (a, j)| ≤ C * |g a| := by
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨C, ?_⟩
  rw [Filter.prod_top, Filter.eventually_comap] at hC
  filter_upwards [hC] with a ha j
  simpa [Real.norm_eq_abs] using ha (a, j) rfl

/-- Woodford (2003), §2, p. 394: the amplitude, viewed on `A × (ℕ × Ω)`, still tends to `0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem tendsto_amp {J : Type*} (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun p : A × J => e p.1) (l ×ˢ (⊤ : Filter J)) (𝓝 0) :=
  he.comp tendsto_fst

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), §1, pp. 386–389 (welfare ranking along any filter, with common
policy-independent terms `T`): if `W_X = T − ε² k L_X + O(ε³)` for both policies, `k > 0`,
`ε → 0`, `ε ≠ 0` eventually, and `L_A < L_B`, then `W_B < W_A` eventually.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ranking_of_common (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ a in l, e a ≠ 0)
    {WA WB T : A → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun a => WA a - (T a - e a ^ 2 * (k * LA))) =O[l] fun a => e a ^ 3)
    (hB : (fun a => WB a - (T a - e a ^ 2 * (k * LB))) =O[l] fun a => e a ^ 3)
    (hL : LA < LB) : ∀ᶠ a in l, WB a < WA a := by
  refine OneParamTaylor.eventually_lt_of_quadratic_gap (s := e)
    (q := fun a => e a ^ 2 * (k * (LB - LA))) (c := k * (LB - LA)) he
    (mul_pos hk (by linarith)) (Eventually.of_forall fun a => le_of_eq (by ring)) hne ?_
  exact (hA.sub hB).congr_left fun a => by ring

/-- Woodford (2003), App. E (first-order solutions): if `x = εx₁ + O(ε²)` with `x₁` bounded,
then `x² = ε²x₁² + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sq_sub_o (hs : Tendsto s L (𝓝 0)) {x x1 : B → ℝ}
    (hd : (fun b => x b - s b * x1 b) =O[L] fun b => s b ^ 2)
    (h1 : x1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => x b ^ 2 - s b ^ 2 * x1 b ^ 2) =O[L] fun b => s b ^ 3 := by
  have hsx : (fun b => s b * x1 b) =O[L] fun b => s b ^ 1 :=
    ((isBigO_refl s L).mul h1).congr_right fun b => by ring
  have hsum : (fun b => x b - s b * x1 b + 2 * (s b * x1 b)) =O[L] fun b => s b ^ 1 :=
    (o_weaken hs (by norm_num : 1 ≤ 2) hd).add (hsx.const_mul_left 2)
  exact (o_mul hd hsum (by norm_num : 2 + 1 = 3)).congr_left fun b => by ring

/-- Woodford (2003), (E.15), p. 699: the first and second derivatives of `U(Y, m, ξ)` along the
coordinate directions `e₁ = (1, 0, 0)`, `e₂ = (0, 1, 0)` and the disturbance `(0, 0, ξ)`
give the quadratic approximation of eq. (1.2) on `ℝ × ℝ × Ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem quadApprox_triple (U : ℝ × ℝ × Ξ → ℝ) (z : ℝ × ℝ × Ξ) (a c : ℝ) (ξ : Ξ) :
    ApproxTheory.quadApprox (U z) (fderiv ℝ U z) (fderiv ℝ (fderiv ℝ U) z) (a, c, ξ) =
      U z + fderiv ℝ U z (1, 0, 0) * a + fderiv ℝ U z (0, 1, 0) * c + fderiv ℝ U z (0, 0, ξ) +
        1 / 2 * (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (1, 0, 0) * a ^ 2 +
          (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (0, 1, 0) +
            fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (1, 0, 0)) * (a * c) +
          fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (0, 1, 0) * c ^ 2 +
          (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (0, 0, ξ) +
            fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (1, 0, 0)) * a +
          (fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (0, 0, ξ) +
            fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (0, 1, 0)) * c +
          fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (0, 0, ξ)) := by
  have e : ((a, c, ξ) : ℝ × ℝ × Ξ) =
      a • ((1 : ℝ), (0 : ℝ), (0 : Ξ)) + c • ((0 : ℝ), (1 : ℝ), (0 : Ξ)) +
        ((0 : ℝ), (0 : ℝ), ξ) := by
    ext <;> simp
  rw [e]
  simp only [ApproxTheory.quadApprox, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.15)–(E.17), pp. 699–700: the cubic discrepancy between the utility
expansion in LEVEL deviations `Ȳ(Ŷ + Ŷ²/2 + r₃)`, `m̄(m̂ + m̂²/2 + r₃)` at satiation (where
`u_m = 0`) and the book's polynomial in `Ŷ`, `m̂` (`smS = s_mσ_m⁻¹ = (η_iv̄)⁻¹`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def txAtom (σ χ smS g eps Y m rY rm : ℝ) : ℝ :=
  ((Y + Y ^ 2 / 2 + rY) - σ / 2 * (Y + Y ^ 2 / 2 + rY) ^ 2 +
      χ * (Y + Y ^ 2 / 2 + rY) * (m + m ^ 2 / 2 + rm) - smS / 2 * (m + m ^ 2 / 2 + rm) ^ 2 +
      σ * g * (Y + Y ^ 2 / 2 + rY) + smS * eps * (m + m ^ 2 / 2 + rm)) -
    (Y + (1 - σ) / 2 * Y ^ 2 + σ * g * Y - smS / 2 * m ^ 2 + χ * m * Y + smS * eps * m)

/-- Woodford (2003), (E.15): `txAtom = O(s³)` for first-order `Ŷ, m̂, g, εᵐ` and third-order
exponential atoms.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem txAtom_o (hs : Tendsto s L (𝓝 0)) (σ χ smS : ℝ) {g eps Y m rY rm : B → ℝ}
    (hg : g =O[L] fun b => s b ^ 1) (heps : eps =O[L] fun b => s b ^ 1)
    (hY : Y =O[L] fun b => s b ^ 1) (hm : m =O[L] fun b => s b ^ 1)
    (hrY : rY =O[L] fun b => s b ^ 3) (hrm : rm =O[L] fun b => s b ^ 3) :
    (fun b => txAtom σ χ smS (g b) (eps b) (Y b) (m b) (rY b) (rm b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => Y b ^ 2 / 2 + rY b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hY 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hrY)).congr_left
      fun b => by ring
  have hC : (fun b => m b ^ 2 / 2 + rm b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hm 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hrm)).congr_left
      fun b => by ring
  have hA1 : (fun b => 2 * Y b + (Y b ^ 2 / 2 + rY b)) =O[L] fun b => s b ^ 1 :=
    (hY.const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  have hC1 : (fun b => 2 * m b + (m b ^ 2 / 2 + rm b)) =O[L] fun b => s b ^ 1 :=
    (hm.const_mul_left 2).add (o_weaken hs (by norm_num) hC)
  have hm1 : (fun b => m b + (m b ^ 2 / 2 + rm b)) =O[L] fun b => s b ^ 1 :=
    hm.add (o_weaken hs (by norm_num) hC)
  have t1 := o_mul hA hA1 (by norm_num : 2 + 1 = 3)
  have t2 := o_mul hA hm1 (by norm_num : 2 + 1 = 3)
  have t3 := o_mul hY hC (by norm_num : 1 + 2 = 3)
  have t4 := o_mul hC hC1 (by norm_num : 2 + 1 = 3)
  have t5 := o_mul hg hA (by norm_num : 1 + 2 = 3)
  have t6 := o_mul heps hC (by norm_num : 1 + 2 = 3)
  refine (((((hrY.sub (t1.const_mul_left (σ / 2))).add ((t2.add t3).const_mul_left χ)).sub
    (t4.const_mul_left (smS / 2))).add (t5.const_mul_left σ)).add
    (t6.const_mul_left smS)).congr_left fun b => ?_
  unfold txAtom
  ring

/-- Woodford (2003), (E.3)–(E.5), p. 694, at `Φ_y = 0`: the cubic discrepancy between the
integrated disutility (exact mean `m₁ + r_C`, per-good remainders Rv) and the book's
polynomial in `m₁ = Ŷ − ½(1 − θ⁻¹)var_i ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vAtom (ω q m1 rC Rvbar : ℝ) : ℝ :=
  rC + (1 + ω) / 2 * (2 * m1 * rC + rC ^ 2) - ω * q * rC + Rvbar

/-- Woodford (2003), (E.3)–(E.5): `vAtom = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem vAtom_o (hs : Tendsto s L (𝓝 0)) (ω : ℝ) {q m1 rC Rvbar : B → ℝ}
    (hq : q =O[L] fun b => s b ^ 1) (hm1 : m1 =O[L] fun b => s b ^ 1)
    (hrC : rC =O[L] fun b => s b ^ 3) (hRv : Rvbar =O[L] fun b => s b ^ 3) :
    (fun b => vAtom ω (q b) (m1 b) (rC b) (Rvbar b)) =O[L] fun b => s b ^ 3 := by
  have h1 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hm1 hrC (by norm_num : 1 + 3 = 4))
  have h2 := o_weaken hs (by norm_num : 3 ≤ 6) (o_mul hrC hrC (by norm_num : 3 + 3 = 6))
  have h3 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hq hrC (by norm_num : 1 + 3 = 4))
  refine (((hrC.add (((h1.const_mul_left 2).add h2).const_mul_left ((1 + ω) / 2))).sub
    (h3.const_mul_left ω)).add hRv).congr_left fun b => ?_
  unfold vAtom
  ring

/-- Woodford (2003), (4.9) and (E.15)–(E.18): the explicit remainder `Transactions.remainder`
is `O(s³)` along ANY family in which `Ŷ, î − îᵐ, g, q, εᵐ, Φ_y, Δ̄, e₂, e₃` are `O(s)` and
`var_i ŷ`, the money-demand residual `r` are `O(s²)` (not only along weighted rays as in
Transactions.remainder_isBigO).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem txRemainder_o (hs : Tendsto s L (𝓝 0)) (P : Transactions.TxParams)
    {x : B → Transactions.TxPoint}
    (hY : (fun b => (x b).Y) =O[L] fun b => s b ^ 1)
    (hd : (fun b => (x b).d) =O[L] fun b => s b ^ 1)
    (hg : (fun b => (x b).g) =O[L] fun b => s b ^ 1)
    (hq : (fun b => (x b).q) =O[L] fun b => s b ^ 1)
    (heps : (fun b => (x b).eps) =O[L] fun b => s b ^ 1)
    (hPhi : (fun b => (x b).Phi) =O[L] fun b => s b ^ 1)
    (hDel : (fun b => (x b).Delta) =O[L] fun b => s b ^ 1)
    (hV : (fun b => (x b).V) =O[L] fun b => s b ^ 2)
    (hr : (fun b => (x b).r) =O[L] fun b => s b ^ 2)
    (he2 : (fun b => (x b).e2) =O[L] fun b => s b ^ 1)
    (he3 : (fun b => (x b).e3) =O[L] fun b => s b ^ 1) :
    (fun b => Transactions.remainder P 1 (x b)) =O[L] fun b => s b ^ 3 := by
  have hr1 := o_weaken hs (by norm_num : 1 ≤ 2) hr
  have hm : (fun b => P.etaY * (x b).Y - P.etaI * (x b).d + (x b).eps + 1 * (x b).r)
      =O[L] fun b => s b ^ 1 :=
    (((hY.const_mul_left P.etaY).sub (hd.const_mul_left P.etaI)).add heps).add
      (hr1.const_mul_left 1)
  have hm2 := o_mul hm hm (by norm_num : 1 + 1 = 2)
  have hgm := o_mul hg hm (by norm_num : 1 + 1 = 2)
  have hem := o_mul heps hm (by norm_num : 1 + 1 = 2)
  have hA : (fun b => Transactions.remA P 1 (x b)) =O[L] fun b => s b ^ 3 :=
    ((o_mul hDel (((hm2.const_mul_left (1 / 2)).add (hgm.const_mul_left P.sigInv)).add
      (hem.const_mul_left P.chi)) (by norm_num : 1 + 2 = 3)).const_mul_left
        P.vbar⁻¹).congr_left fun b => by unfold Transactions.remA; ring
  have hB : (fun b => Transactions.remB P 1 (x b)) =O[L] fun b => s b ^ 3 :=
    (o_mul he2 (hem.sub (hm2.const_mul_left (1 / 2))) (by norm_num : 1 + 2 = 3)).congr_left
      fun b => by unfold Transactions.remB; ring
  have hlin : (fun b => P.etaY * (x b).Y - P.etaI * (x b).d) =O[L] fun b => s b ^ 1 :=
    (hY.const_mul_left P.etaY).sub (hd.const_mul_left P.etaI)
  have hC : (fun b => Transactions.remC P 1 (x b)) =O[L] fun b => s b ^ 3 := by
    have c1 := o_mul hDel hr (by norm_num : 1 + 2 = 3)
    have c2 := o_mul hr hY (by norm_num : 2 + 1 = 3)
    have c3 := o_mul hlin hr (by norm_num : 1 + 2 = 3)
    have c4 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hr hr (by norm_num : 2 + 2 = 4))
    refine ((((c1.const_mul_left P.vbar⁻¹).add (c2.const_mul_left P.chi)).sub
      (c3.const_mul_left (1 / (P.etaI * P.vbar)))).sub
      (c4.const_mul_left (1 / (P.etaI * P.vbar) / 2))).congr_left fun b => ?_
    unfold Transactions.remC
    ring
  have hD : (fun b => Transactions.remD P (x b)) =O[L] fun b => s b ^ 3 := by
    have d1 := o_mul hd hY (by norm_num : 1 + 1 = 2)
    have d2 := o_mul hY hY (by norm_num : 1 + 1 = 2)
    refine (o_mul he3 ((d1.const_mul_left (1 / (P.etaI * P.vbar) * P.etaI)).sub
      (d2.const_mul_left (1 / (P.etaI * P.vbar) / 2 * P.etaY))) (by norm_num : 1 + 2 = 3)
      ).congr_left fun b => ?_
    unfold Transactions.remD
    ring
  have hE : (fun b => Transactions.remE P 1 (x b)) =O[L] fun b => s b ^ 3 := by
    have e1 := o_mul hPhi hV (by norm_num : 1 + 2 = 3)
    have e2' := o_mul hY hV (by norm_num : 1 + 2 = 3)
    have e3' := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hV hV (by norm_num : 2 + 2 = 4))
    have e4 := o_mul hq hV (by norm_num : 1 + 2 = 3)
    refine ((((e1.const_mul_left ((1 - P.thetaInv) / 2)).sub
      (e2'.const_mul_left ((1 + P.omega) * ((1 - P.thetaInv) / 2)))).add
      (e3'.const_mul_left ((1 + P.omega) / 2 * ((1 - P.thetaInv) / 2) ^ 2))).add
      (e4.const_mul_left (P.omega * ((1 - P.thetaInv) / 2)))).congr_left fun b => ?_
    unfold Transactions.remE
    ring
  exact ((((hA.add hB).add hC).add hD).sub hE).congr_left fun b => by
    unfold Transactions.remainder; ring

/-- Woodford (2003), §4.1, eq. (4.1)–(4.2), p. 420: the ACTUAL period utility with transactions
frictions, `u(Y, m; ξ) − ∫v(y(i); ξ)di`, for outputs `y(i) = Ȳe^{ŷ(i)}`, the Dixit–Stiglitz
aggregate `Y = Ȳe^{Ŷ}` and real balances `m = m̄e^{m̂}`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def periodUT (U : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (w : ι → ℝ) (θ Ybar mbar : ℝ)
    (yh : ι → ℝ) (mh : ℝ) (xu xv : Ξ) : ℝ :=
  U (Ybar * Real.exp (logYidx w θ yh), mbar * Real.exp mh, xu) -
    ∑ i, w i * v (Ybar * Real.exp (yh i), xv)

/-- Woodford (2003), (E.15) and (E.3): the policy-independent terms of the expansion at the
satiated steady state `(Ȳ, m̄, 0)` (functions of the disturbances only).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def tipT (Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (Ybar mbar : ℝ) (xu xv : Ξ) : ℝ :=
  (Ut (Ybar, mbar, 0) + fderiv ℝ Ut (Ybar, mbar, 0) (0, 0, xu) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu) (0, 0, xu) / 2) -
    (v (Ybar, 0) + dXi v (Ybar, 0) xv + dXiXi v (Ybar, 0) xv / 2)

/-- Woodford (2003), App. E.4: the expansion point of `Transactions.prop_6_7_layerA` at the
satiated efficient steady state (`Φ_y = Δ̄ = e₂ = e₃ = 0`), with the money-demand residual
`r` given by `m̂ = η_yŶ − η_i(î − îᵐ) + εᵐ + r` (eq. (4.1)).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def txSat (P : Transactions.TxParams) (Y d g q eps V m : ℝ) : Transactions.TxPoint :=
  ⟨Y, d, g, q, eps, 0, 0, V, m - (P.etaY * Y - P.etaI * d + eps), 0, 0⟩

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B from the ACTUAL utility,
with the ONE-SIDED expansion at satiation (Assumption 6.1, (E.15)–(E.18)): the utility `U` of
output, real balances and disturbances coincides for `m ≤ m̄` with a `C³` function `Ũ` (its
extension from below satiation), `u_m(m̄) = 0`; `v` is `C³`; the coefficients at the
efficient satiated steady state `(Ȳ, m̄, 0)` define `σ⁻¹`, `χ`, `s_mσ_m⁻¹ = (η_iv̄)⁻¹`, `ω` and
the composite disturbances `g`, `εᵐ`, `q` (h11–hq); `η_y = χη_iv̄` there ((E.16)). Along any
family with `ŷ(i), m̂, î − îᵐ, ξ = O(s)`, the money-demand residual `O(s²)` and real balances
BELOW satiation (`m̂ ≤ 0`, i.e. `Δ̄ = εΔ₁ > 0`), the actual period utility is
`t.i.p. + Ȳu_c[tip − ½(4.9)] + O(s³)`, with the quadratic form (4.9)
`Ω_mc(Ŷ − Ŷⁿ)² + v̄⁻¹η_i(î − îᵐ)² + (θ⁻¹ + ω) var_i ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop67_actual (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : dYY v (Ybar, 0) = P.omega * dY v (Ybar, 0) / Ybar)
    {yh : B → ι → ℝ} {mh d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * eps b))
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(P.omega * dY v (Ybar, 0) * q b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hmh : mh =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => mh b - (P.etaY * logYidx w θ (yh b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, mh b ≤ 0) :
    (fun b => periodUT U v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
      (tipT Ut v Ybar mbar (xu b) (xv b) + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txSat P (logYidx w θ (yh b)) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) /
            2))) =O[L] fun b => s b ^ 3 := by
  set z0 : ℝ × ℝ × Ξ := (Ybar, mbar, 0) with hz0
  set uc := fderiv ℝ Ut z0 (1, 0, 0) with huc
  set smS := 1 / (P.etaI * P.vbar) with hsmS
  set Yh := fun b => logYidx w θ (yh b) with hYh
  have hYO : Yh =O[L] fun b => s b ^ 1 := logYidx_o hs hw0 hw1 hθ hyh
  have lev : ∀ (c : ℝ) (x : B → ℝ), x =O[L] (fun b => s b ^ 1) →
      (fun b => c * (Real.exp (x b) - 1)) =O[L] fun b => s b ^ 1 := fun c x hx => by
    have h2 := o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hx 2)
    have h3 := o_weaken hs (by norm_num : 1 ≤ 3) (expRem_o hs hx)
    refine (((hx.add (h2.const_mul_left (1 / 2))).add h3).const_mul_left c).congr_left
      fun b => ?_
    rw [ExpLogCES.exp_sub_one_eq]
    ring
  -- (1) the one-sided Taylor expansion of `U` at satiation
  have hU1 := taylor_family_of_eqOn hUt hEq z0 hs
    (z := fun b => (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b))
    ((lev Ybar Yh hYO).prod_left ((lev mbar mh hmh).prod_left hxu)) (by
      filter_upwards [hleft] with b hb
      have h1 : Real.exp (mh b) ≤ 1 := Real.exp_le_one_iff.mpr hb
      change (z0 + _).2.1 ≤ mbar
      simp only [hz0, Prod.snd_add, Prod.fst_add]
      nlinarith)
  -- (2) the disutility, good by good
  have hvs := IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (uTaylor_family_exp hv Ybar hs (coord_o hyh i) hxv).const_mul_left (w i)
  -- (3) the cubic atoms and the Layer-A remainder
  have hRv : (fun b => ∑ i, w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i)))
      =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ =>
      (Rv0_o hs P.omega hqO (coord_o hyh i) (expRem_o hs (coord_o hyh i))).const_mul_left (w i)
  have hV := crossVar_o hw0 hw1 hyh
  have hm1 : (fun b => Yh b - (1 - θ⁻¹) / 2 * crossVar w (yh b)) =O[L] fun b => s b ^ 1 :=
    hYO.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hV).const_mul_left _)
  have hA1 := txAtom_o hs P.sigInv P.chi smS hgO hepsO hYO hmh (expRem_o hs hYO)
    (expRem_o hs hmh)
  have hA2 := vAtom_o hs P.omega hqO hm1 (cesAtom_o hs hw0 hw1 hθ hyh) hRv
  have hzero : (fun _ : B => (0 : ℝ)) =O[L] fun b => s b ^ 1 := isBigO_zero _ _
  have hA3 := txRemainder_o hs P
    (x := fun b => txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b))
    hYO hd hgO hqO hepsO hzero hzero hV hr hzero hzero
  refine (((hU1.sub hvs).add (((hA1.sub hA2).add hA3).const_mul_left (Ybar * uc)))).congr_left
    fun b => ?_
  -- (4) the exact identity at `b`
  have key := Transactions.prop_6_7_layerA P hΩ hi hvb
    (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b))
    (by simp only [txSat]; rw [hey]; ring)
  have eU : z0 + (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b) =
      (Ybar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b) := by
    simp only [hz0, Prod.mk_add_mk, zero_add]
    congr 1 <;> [ring; (congr 1; ring)]
  have eQ : ApproxTheory.quadApprox (Ut z0) (fderiv ℝ Ut z0) (fderiv ℝ (fderiv ℝ Ut) z0)
      (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b) =
      (Ut z0 + fderiv ℝ Ut z0 (0, 0, xu b) +
        fderiv ℝ (fderiv ℝ Ut) z0 (0, 0, xu b) (0, 0, xu b) / 2) +
      Ybar * uc * (Transactions.uTaylor P
        (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) +
        txAtom P.sigInv P.chi smS (g b) (eps b) (Yh b) (mh b) (expRem (Yh b))
          (expRem (mh b))) := by
    rw [quadApprox_triple, hsat, h11, h12, h22, hg b, heps b, ExpLogCES.exp_sub_one_eq,
      ExpLogCES.exp_sub_one_eq]
    simp only [Transactions.uTaylor, txAtom, txSat, Transactions.mHat, Transactions.sM,
      Transactions.smSig, hsmS]
    field_simp
    ring
  have eV : ∑ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
      (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
      (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) =
      (v (Ybar, 0) + dXi v (Ybar, 0) (xv b) + dXiXi v (Ybar, 0) (xv b) / 2) +
      Ybar * uc * (Transactions.vTaylor P
        (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) +
        vAtom P.omega (q b) (Yh b - (1 - θ⁻¹) / 2 * crossVar w (yh b))
          (Links.CES.cesAtom w θ (yh b))
          (∑ i, w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i)))) := by
    have hper : ∀ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
        (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) =
        (v (Ybar, 0) + dXi v (Ybar, 0) (xv b) + dXiXi v (Ybar, 0) (xv b) / 2) * w i +
          Ybar * uc * (w i * Prop61.Tv 0 P.omega (q b) (yh b i) +
            w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i))) := by
      intro i
      rw [Prop61.uTaylor, hvyy, hq b, hvy]
      unfold Prop61.Tv Prop61.Rv
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => hper i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1]
    rw [TwoSectorWelfare.sum_Tv hw1, Links.CES.ces_relation w θ (yh b)]
    simp only [Transactions.vTaylor, Transactions.mOne, txSat, vAtom, TwoSectorWelfare.TvSec,
      hθi, hYh, logYidx]
    ring
  have hsum : ∑ i, w i * (v (Ybar * Real.exp (yh b i), xv b) -
      Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) (xv b))
        (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) =
      ∑ i, w i * v (Ybar * Real.exp (yh b i), xv b) -
        ∑ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
          (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
          (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htip : Transactions.tip P
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).g
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).q
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).eps
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).Phi
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).Delta =
      Transactions.tip P (g b) (q b) (eps b) 0 0 := rfl
  rw [htip] at key
  simp only [periodUT, tipT]
  rw [← hz0, hsum, eV, eU, eQ]
  linear_combination (-(Ybar * uc)) * key

/-- Woodford (2003), App. E.1 (first-order solutions): if the cross-section is
`ŷ = εŷ₁ + O(ε²)` with `ŷ₁` bounded, then `var_i ŷ = ε² var_i ŷ₁ + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossVar_first_order (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {y y1 : B → ι → ℝ}
    (hd : (fun b => y b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (h1 : y1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => crossVar w (y b) - s b ^ 2 * crossVar w (y1 b)) =O[L] fun b => s b ^ 3 := by
  have hc : ∀ i, (fun b => (y b i - crossMean w (y b)) - s b * (y1 b i - crossMean w (y1 b)))
      =O[L] fun b => s b ^ 2 := by
    intro i
    have hm : (fun b => crossMean w (y b - s b • y1 b)) =O[L] fun b => s b ^ 2 :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul, Real.norm_eq_abs]
        exact ExpLogCES.abs_crossMean_le hw0 hw1 _)).trans hd
    have hi : (fun b => y b i - s b * y1 b i) =O[L] fun b => s b ^ 2 :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul]
        simpa using norm_le_pi_norm (y b - s b • y1 b) i)).trans hd
    refine (hi.sub hm).congr_left fun b => ?_
    simp only [crossMean, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ x, w x * (y b x - s b * y1 b x) = ∑ x, w x * y b x - s b * ∑ x, w x * y1 b x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this]
    ring
  have h1c : ∀ i, (fun b => y1 b i - crossMean w (y1 b)) =O[L] fun _ => (1 : ℝ) := by
    intro i
    have hcoord : (fun b => y1 b i) =O[L] fun _ => (1 : ℝ) :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul]; exact norm_le_pi_norm (y1 b) i)).trans h1
    have hmean : (fun b => crossMean w (y1 b)) =O[L] fun _ => (1 : ℝ) :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw0 hw1 _)).trans h1
    exact hcoord.sub hmean
  refine (IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (sq_sub_o hs (hc i) (h1c i)).const_mul_left (w i)).congr_left fun b => ?_
  simp only [crossVar, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Woodford (2003), (4.9), p. 422: along a family with first-order solution
`(Ŷ₁, (î − îᵐ)₁, g₁, q₁, εᵐ₁, var_i ŷ₁)` (each variable `= ε × first order + O(ε²)`, the variance
`= ε² var₁ + O(ε³)`), the quadratic form (4.9) at the satiated point satisfies
`(4.9)(ε) = ε²(4.9)(first-order solution) + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem loss49_first_order (hs : Tendsto s L (𝓝 0)) (P : Transactions.TxParams)
    {Y d g q eps V m Y1 d1 g1 q1 eps1 V1 m1 : B → ℝ}
    (hY : (fun b => Y b - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hg : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hq : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (heps : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2)
    (hV : (fun b => V b - s b ^ 2 * V1 b) =O[L] fun b => s b ^ 3)
    (hY1 : Y1 =O[L] fun _ => (1 : ℝ)) (hd1 : d1 =O[L] fun _ => (1 : ℝ))
    (hg1 : g1 =O[L] fun _ => (1 : ℝ)) (hq1 : q1 =O[L] fun _ => (1 : ℝ))
    (heps1 : eps1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => Transactions.loss49 P (txSat P (Y b) (d b) (g b) (q b) (eps b) (V b) (m b)) -
      s b ^ 2 * Transactions.loss49 P
        (txSat P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (V1 b) (m1 b))) =O[L] fun b => s b ^ 3 := by
  set c1 := P.sigInv / Transactions.omegaMC P
  set c2 := P.omega / Transactions.omegaMC P
  set c3 := P.chi / Transactions.omegaMC P
  have hG : (fun b => (Y b - (c1 * g b + c2 * q b + c3 * eps b)) -
      s b * (Y1 b - (c1 * g1 b + c2 * q1 b + c3 * eps1 b))) =O[L] fun b => s b ^ 2 :=
    (hY.sub (((hg.const_mul_left c1).add (hq.const_mul_left c2)).add
      (heps.const_mul_left c3))).congr_left fun b => by ring
  have hG1 : (fun b => Y1 b - (c1 * g1 b + c2 * q1 b + c3 * eps1 b)) =O[L] fun _ => (1 : ℝ) :=
    hY1.sub (((hg1.const_mul_left c1).add (hq1.const_mul_left c2)).add (heps1.const_mul_left c3))
  refine ((((sq_sub_o hs hG hG1).const_mul_left (Transactions.omegaMC P)).add
    ((sq_sub_o hs hd hd1).const_mul_left (P.etaI / P.vbar))).add
    (hV.const_mul_left (P.thetaInv + P.omega))).congr_left fun b => ?_
  simp only [Transactions.loss49, txSat, Transactions.natRate, Transactions.xStar,
    Transactions.sM, c1, c2, c3]
  ring

/-- Woodford (2003), §1 (survey §4, Layer B): the generic bridge. If the actual welfare is
`T − (K/2) L(ε) + O(ε³)` (Layer A plus the Taylor step) and the loss satisfies
`L(ε) = ε² L₁ + O(ε³)` (first-order solution), then `W = T − (ε²/2) K L₁ + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem bridge_first_order {W T Lq L1 : B → ℝ} {K : ℝ}
    (hW : (fun b => W b - (T b - K * Lq b / 2)) =O[L] fun b => s b ^ 3)
    (hL : (fun b => Lq b - s b ^ 2 * L1 b) =O[L] fun b => s b ^ 3) :
    (fun b => W b - (T b - s b ^ 2 / 2 * (K * L1 b))) =O[L] fun b => s b ^ 3 :=
  (hW.sub (hL.const_mul_left (K / 2))).congr_left fun b => by ring

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B: under the hypotheses of
`prop67_actual`, if the family has the first-order solution
`(ŷ₁(i), Ŷ₁, (î − îᵐ)₁, g₁, q₁, εᵐ₁)` (`ŷ = εŷ₁ + O(ε²)` etc., all first-order objects bounded),
then the actual period utility is
`W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·(4.9)(first-order solution) + O(ε³)`, where the t.i.p.
`tipT + Ȳu_c·Transactions.tip` depends on the disturbances only.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop67_layerB (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : dYY v (Ybar, 0) = P.omega * dY v (Ybar, 0) / Ybar)
    {yh y1 : B → ι → ℝ} {mh d g q eps Y1 d1 g1 q1 eps1 : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * eps b))
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(P.omega * dY v (Ybar, 0) * q b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hmh : mh =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => mh b - (P.etaY * logYidx w θ (yh b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, mh b ≤ 0)
    (hy1 : y1 =O[L] fun _ => (1 : ℝ)) (hY1 : Y1 =O[L] fun _ => (1 : ℝ))
    (hd1 : d1 =O[L] fun _ => (1 : ℝ)) (hg1 : g1 =O[L] fun _ => (1 : ℝ))
    (hq1 : q1 =O[L] fun _ => (1 : ℝ)) (heps1 : eps1 =O[L] fun _ => (1 : ℝ))
    (hyd : (fun b => yh b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θ (yh b) - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hqd : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (hepsd : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2) :
    (fun b => periodUT U v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
      ((tipT Ut v Ybar mbar (xu b) (xv b) + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        Transactions.tip P (g b) (q b) (eps b) 0 0) -
        s b ^ 2 / 2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * Transactions.loss49 P
          (txSat P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (crossVar w (y1 b)) 0))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop67_actual hs hw0 hw1 hθ hUt hmbar hEq hv P hθi hey hΩ hi hvb hsat h11 h12 h22
    hvy hvyy hg heps hq hyh hmh (fo d d1 hdd hd1) (fo g g1 hgd hg1) (fo q q1 hqd hq1)
    (fo eps eps1 hepsd heps1) hxu hxv hr hleft
  have hL := loss49_first_order hs P (m := mh) (m1 := fun _ => 0) hYd hdd hgd hqd hepsd
    (crossVar_first_order hs hw0 hw1 hyd hy1) hY1 hd1 hg1 hq1 heps1
  exact bridge_first_order (hW.congr_left fun b => by ring) hL

/-- Woodford (2003), Propositions 6.7, 6.10 and 6.12 and §1, pp. 386–389 (the WELFARE
RANKING): for two policies facing the same disturbances (same t.i.p.), each with a Layer-B
expansion `W = T − (ε²/2)K L(first-order solution) + O(ε³)` (`prop67_layerB`,
prop610_layerB, prop612_layerB) with `K = Ȳu_c > 0`, the policy whose first-order solution
has the smaller quadratic loss is strictly better for every small `ε ≠ 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ranking_layerB {A' : Type*} {l' : Filter A'} {e' : A' → ℝ}
    (he : Tendsto e' l' (𝓝 0)) (hne : ∀ᶠ a in l', e' a ≠ 0) {K : ℝ} (hK : 0 < K)
    {WA WB T : A' → ℝ} {LA LB : ℝ}
    (hA : (fun a => WA a - (T a - e' a ^ 2 / 2 * (K * LA))) =O[l'] fun a => e' a ^ 3)
    (hB : (fun a => WB a - (T a - e' a ^ 2 / 2 * (K * LB))) =O[l'] fun a => e' a ^ 3)
    (hL : LA < LB) : ∀ᶠ a in l', WB a < WA a :=
  ranking_of_common he hne (WA := WA) (WB := WB) (T := T) (k := K / 2) (by linarith)
    (hA.congr_left fun a => by ring) (hB.congr_left fun a => by ring) hL

/-- Woodford (2003), (4.10)–(4.11), p. 423 (uniform orders and discounting along a path): if
`f_t = O(g)` uniformly in `t` and `0 ≤ β < 1`, then `∑βᵗf_t = O(g)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem tsum_o {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : A → ℕ → ℝ} {g : A → ℝ}
    (h : (fun p : A × ℕ => f p.1 p.2) =O[l ×ˢ (⊤ : Filter ℕ)] fun p => g p.1) :
    (fun a => ∑' t, β ^ t * f a t) =O[l] g := by
  obtain ⟨C, hC⟩ := uniform_bound h
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with a ha
  have h1 := SeqW.abs_tsum_le (f := f a) (fun t => ha t) hβ0 hβ1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc _ ≤ C * |g a| / (1 - β) := h1
    _ = C / (1 - β) * |g a| := by ring

/-- Woodford (2003), §2, p. 394: a sequence family that is uniformly `O(eᵏ)` is bounded for
every amplitude close enough to `0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem seq_bdd_of_o (he : Tendsto e l (𝓝 0)) {f : A → ℕ → ℝ} {k : ℕ}
    (h : (fun p : A × ℕ => f p.1 p.2) =O[l ×ˢ (⊤ : Filter ℕ)] fun p => e p.1 ^ k) :
    ∀ᶠ a in l, SeqW.Bdd (f a) := by
  obtain ⟨C, hC⟩ := uniform_bound (g := fun a => e a ^ k) h
  have h1 : ∀ᶠ a in l, |e a| ≤ 1 := by
    filter_upwards [he.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with a ha
    simpa [Real.dist_eq] using ha
  filter_upwards [hC, h1] with a ha h1a
  refine ⟨|C|, fun t => ?_⟩
  have hp : |e a ^ k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1a
  calc |f a t| ≤ C * |e a ^ k| := ha t
    _ ≤ |C| * |e a ^ k| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = |C| := mul_one _

/-- Woodford (2003), **Proposition 6.8**, (4.10)–(4.11), p. 423, LAYER B along a path: if the
period utility has the expansion of `prop67_actual` (`W = τ − (K/2)(4.9) + O(ε³)`, `τ`
policy-independent, `K = Ȳu_c`) UNIFORMLY in the date (that theorem applies verbatim on the
filter `l ×ˢ ⊤`), the first-order variables are uniformly `O(ε)`, the
mean-price inflation `π̄` satisfies `π̄ − π = O(ε²)` and the Calvo dispersion law
`∑βᵗvar_i ŷ_t = θ²(ψ∑βᵗπ̄_t² + T₀)` holds (`T₀` policy-independent), then
`∑βᵗW_t = ∑βᵗτ_t − (K/2)[Λ ∑βᵗL_t + (θ⁻¹ + ω)θ²T₀] + O(ε³)` with L_t the loss (4.10)
evaluated at the actual path (with `π`, not `π̄`) and `Λ = θ(1 + ωθ)ψ > 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop68_layerB (P : Transactions.TxParams) {α β θ K : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ) (hθi : P.thetaInv = 1 / θ) (hω : 0 ≤ P.omega)
    (hΩ : 0 < Transactions.omegaMC P) (hv : P.vbar ≠ 0) (he : Tendsto e l (𝓝 0))
    {W τ Y d g q eps V pib infl : A → ℕ → ℝ} {T0 : A → ℝ} (hτ : ∀ a, SeqW.Bdd (τ a))
    (hP : (fun p : A × ℕ => W p.1 p.2 - (τ p.1 p.2 - K * Transactions.loss49 P
      (txSat P (Y p.1 p.2) (d p.1 p.2) (g p.1 p.2) (q p.1 p.2) (eps p.1 p.2) (V p.1 p.2) 0) / 2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3)
    (hY : (fun p : A × ℕ => Y p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hd : (fun p : A × ℕ => d p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hg : (fun p : A × ℕ => g p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hq : (fun p : A × ℕ => q p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (heps : (fun p : A × ℕ => eps p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hi : (fun p : A × ℕ => infl p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hpO : (fun p : A × ℕ => pib p.1 p.2 - infl p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hV : ∀ a, HasSum (fun t => β ^ t * V a t)
      (θ ^ 2 * (Moments.calvoK α β * ∑' t, β ^ t * pib a t ^ 2 + T0 a))) :
    (fun a => ∑' t, β ^ t * W a t - (∑' t, β ^ t * τ a t - K / 2 *
      (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t * Transactions.loss410 P α β θ
        (infl a t) (Y a t - Transactions.natRate P (g a t) (q a t) (eps a t)) (d a t) +
        (P.thetaInv + P.omega) * θ ^ 2 * T0 a))) =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  set R : A → ℕ → ℝ := fun a t => W a t - (τ a t - K * Transactions.loss49 P
    (txSat P (Y a t) (d a t) (g a t) (q a t) (eps a t) (V a t) 0) / 2) with hR
  set X : A → ℕ → ℝ := fun a t => Y a t - Transactions.natRate P (g a t) (q a t) (eps a t)
    with hX
  have hXO : (fun p : A × ℕ => X p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    (hY.sub ((((hg.const_mul_left P.sigInv).add (hq.const_mul_left P.omega)).add
      (heps.const_mul_left P.chi)).const_mul_left (Transactions.omegaMC P)⁻¹)).congr_left
        fun p => by simp only [hX, Transactions.natRate]; ring
  have hpib : (fun p : A × ℕ => pib p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hpO).add hi).congr_left fun p => by ring
  have hPO : (fun p : A × ℕ => pib p.1 p.2 ^ 2 - infl p.1 p.2 ^ 2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    (o_mul hpO ((o_weaken hs (by norm_num : 1 ≤ 2) hpO).add (hi.const_mul_left 2))
      (by norm_num : 2 + 1 = 3)).congr_left fun p => by ring
  have bR := seq_bdd_of_o (f := R) he hP
  have bX := seq_bdd_of_o (f := fun a t => X a t ^ 2) he (o_pow hXO 2)
  have bI := seq_bdd_of_o (f := fun a t => d a t ^ 2) he (o_pow hd 2)
  have bp := seq_bdd_of_o (f := fun a t => pib a t ^ 2) he (o_pow hpib 2)
  have bi := seq_bdd_of_o (f := fun a t => infl a t ^ 2) he (o_pow hi 2)
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * W a t - (∑' t, β ^ t * τ a t - K / 2 *
      (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t * Transactions.loss410 P α β θ
        (infl a t) (X a t) (d a t) + (P.thetaInv + P.omega) * θ ^ 2 * T0 a)) =
      ∑' t, β ^ t * R a t - K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β) *
        ∑' t, β ^ t * (pib a t ^ 2 - infl a t ^ 2) := by
    filter_upwards [bR, bX, bI, bp, bi] with a hRa hXa hIa hpa hia
    have sR := (hRa.summable hβ0 hβ1).hasSum
    have sX := (hXa.summable hβ0 hβ1).hasSum
    have sI := (hIa.summable hβ0 hβ1).hasSum
    have sP := (hpa.summable hβ0 hβ1).hasSum
    have si := (hia.summable hβ0 hβ1).hasSum
    have sτ := ((hτ a).summable hβ0 hβ1).hasSum
    obtain ⟨h1, -⟩ := Transactions.prop_6_8 P hα0 hα1 hβ1 hθ hθi hω hΩ hv sX sI sP (hV a)
    have hW : HasSum (fun t => β ^ t * W a t)
        (∑' t, β ^ t * τ a t - K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β *
          (∑' t, β ^ t * pib a t ^ 2 + Transactions.lambdaX P α β θ * ∑' t, β ^ t * X a t ^ 2 +
            Transactions.lambdaI P (Transactions.lambdaX P α β θ) * ∑' t, β ^ t * d a t ^ 2) +
          (P.thetaInv + P.omega) * θ ^ 2 * T0 a) + ∑' t, β ^ t * R a t) := by
      refine ((sτ.sub (h1.mul_left (K / 2))).add sR).congr_fun fun t => ?_
      simp only [hR, hX, Transactions.loss49, txSat, Transactions.xStar, Transactions.sM]
      ring
    have hL : HasSum (fun t => β ^ t * Transactions.loss410 P α β θ (infl a t) (X a t) (d a t))
        (∑' t, β ^ t * infl a t ^ 2 + Transactions.lambdaX P α β θ * ∑' t, β ^ t * X a t ^ 2 +
          Transactions.lambdaI P (Transactions.lambdaX P α β θ) * ∑' t, β ^ t * d a t ^ 2) := by
      refine ((si.add (sX.mul_left (Transactions.lambdaX P α β θ))).add
        (sI.mul_left (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_fun
          fun t => ?_
      simp only [Transactions.loss410]
      ring
    have hD : HasSum (fun t => β ^ t * (pib a t ^ 2 - infl a t ^ 2))
        (∑' t, β ^ t * pib a t ^ 2 - ∑' t, β ^ t * infl a t ^ 2) :=
      (sP.sub si).congr_fun fun t => by ring
    rw [hW.tsum_eq, hL.tsum_eq, hD.tsum_eq]
    ring
  exact ((tsum_o (f := R) hβ0 hβ1 hP).sub ((tsum_o hβ0 hβ1 hPO).const_mul_left
    (K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β)))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), (4.10), p. 423, with a first-order solution along a path: if
`π = επ₁ + O(ε²)`, `x − x* = ε(x − x*)₁ + O(ε²)` and `î − îᵐ = ε(î − îᵐ)₁ + O(ε²)` uniformly
(first-order sequences bounded), then `∑βᵗL_t = ε²∑βᵗL_t(first-order solution) + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem loss410_first_order (P : Transactions.TxParams) {α β θ : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (he : Tendsto e l (𝓝 0)) {infl xg d : A → ℕ → ℝ} {infl1 xg1 d1 : ℕ → ℝ}
    (hi1 : SeqW.Bdd infl1) (hx1 : SeqW.Bdd xg1) (hd1 : SeqW.Bdd d1)
    (hid : (fun p : A × ℕ => infl p.1 p.2 - e p.1 * infl1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hxd : (fun p : A × ℕ => xg p.1 p.2 - e p.1 * xg1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hdd : (fun p : A × ℕ => d p.1 p.2 - e p.1 * d1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2) :
    (fun a => ∑' t, β ^ t * Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t) -
      e a ^ 2 * ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  have b1 : ∀ {u : ℕ → ℝ}, SeqW.Bdd u →
      (fun p : A × ℕ => u p.2) =O[l ×ˢ ⊤] fun _ => (1 : ℝ) := fun {u} hu => by
    obtain ⟨M, hM⟩ := hu
    exact IsBigO.of_bound M (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, norm_one, mul_one]; exact hM _)
  have hD : (fun p : A × ℕ => Transactions.loss410 P α β θ (infl p.1 p.2) (xg p.1 p.2) (d p.1 p.2)
      - e p.1 ^ 2 * Transactions.loss410 P α β θ (infl1 p.2) (xg1 p.2) (d1 p.2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    (((sq_sub_o hs hid (b1 hi1)).add ((sq_sub_o hs hxd (b1 hx1)).const_mul_left
      (Transactions.lambdaX P α β θ))).add ((sq_sub_o hs hdd (b1 hd1)).const_mul_left
      (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_left fun p => by
        simp only [Transactions.loss410]; ring
  have hfo : ∀ {x : A → ℕ → ℝ} {x1 : ℕ → ℝ}, SeqW.Bdd x1 →
      (fun p : A × ℕ => x p.1 p.2 - e p.1 * x1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 2) →
      (fun p : A × ℕ => x p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := fun {x} {x1} h1 hd =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl (fun p : A × ℕ => e p.1) _).mul (b1 h1)).congr_right fun p => by
        ring)).congr_left fun p => by ring
  have hL1 : SeqW.Bdd (fun t => Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t)) := by
    obtain ⟨M1, hM1⟩ := hi1
    obtain ⟨M2, hM2⟩ := hx1
    obtain ⟨M3, hM3⟩ := hd1
    refine ⟨M1 ^ 2 + |Transactions.lambdaX P α β θ| * M2 ^ 2 +
      |Transactions.lambdaI P (Transactions.lambdaX P α β θ)| * M3 ^ 2, fun t => ?_⟩
    have e1 : |infl1 t| ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM1 t) 2
    have e2 : |xg1 t| ^ 2 ≤ M2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM2 t) 2
    have e3 : |d1 t| ^ 2 ≤ M3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM3 t) 2
    unfold Transactions.loss410
    calc _ ≤ |infl1 t ^ 2| + |Transactions.lambdaX P α β θ * xg1 t ^ 2| +
          |Transactions.lambdaI P (Transactions.lambdaX P α β θ) * d1 t ^ 2| :=
          abs_add_three _ _ _
      _ = |infl1 t| ^ 2 + |Transactions.lambdaX P α β θ| * |xg1 t| ^ 2 +
          |Transactions.lambdaI P (Transactions.lambdaX P α β θ)| * |d1 t| ^ 2 := by
          simp only [abs_mul, abs_pow]
      _ ≤ _ := by gcongr
  have bL := seq_bdd_of_o (f := fun a t => Transactions.loss410 P α β θ (infl a t) (xg a t)
    (d a t)) he ((((o_mul (hfo hi1 hid) (hfo hi1 hid) (by norm_num : 1 + 1 = 2)).add
      ((o_mul (hfo hx1 hxd) (hfo hx1 hxd) (by norm_num : 1 + 1 = 2)).const_mul_left
        (Transactions.lambdaX P α β θ))).add
      ((o_mul (hfo hd1 hdd) (hfo hd1 hdd) (by norm_num : 1 + 1 = 2)).const_mul_left
        (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_left fun p => by
          simp only [Transactions.loss410]; ring)
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * (Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t)
      - e a ^ 2 * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t)) =
      ∑' t, β ^ t * Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t) -
        e a ^ 2 * ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t) := by
    filter_upwards [bL] with a ha
    have h1 := (ha.summable hβ0 hβ1).hasSum
    have h2 := ((hL1.summable hβ0 hβ1).hasSum).mul_left (e a ^ 2)
    exact ((h1.sub h2).congr_fun fun t => by ring).tsum_eq
  exact (tsum_o hβ0 hβ1 hD).congr' hev (Eventually.of_forall fun _ => rfl)

variable {J : Type*} [Fintype J]

end BridgeExtensions

end Woodford.GainsFromCommitment.TidyR6WelfFrictions
