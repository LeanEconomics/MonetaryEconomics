/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.ForwardSolution
import StabilizationWelfare.Sequences
import StabilizationWelfare.Moments
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Habit persistence and the welfare criterion (Proposition 6.6)

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2, pp. 403–405 (Proposition 6.6, eqs.
(2.26)–(2.31)), and Appendix E, §E.3, pp. 696–698 (eqs. (E.9)–(E.13)).

All model objects are second-order Taylor polynomials (Layer A of the survey): the period
utility `Useq` is the exact second-order polynomial of
`u((Y_t − G_t) − η(Y_{t−1} − G_{t−1}); ξ_t) − ∫ v(y_t(i); ξ_t) di` (in units of `Ȳ u_c`), every
identity is exact, "t.i.p." is an explicit function of exogenous data and initial conditions, and
"O(3)" is an explicit remainder with a scaling lemma. Discounted sums are genuine `tsum`s of
bounded sequences. Statements hold path by path, and under an arbitrary `ExpectationSystem`.

## Main results

* (E.10): `E10_identity`, `E10rem_scaling`; (E.3)–(E.5): `E4_identity`, `vRem_scaling`,
  `RU_scaling`.
* (E.11): `E11_period`, `E11_discounted` (pathwise), `E11_expectation` (with `E_t g_{t+1}`).
* (E.12): `E12_period`, `E12_discounted`; (E.13): `E13_period`, `E13_discounted`.
* The flexible-price relation ("one can also show", p. 697) PROVED as an exact derivative of the
  nonlinear flexible-price condition with habits: `flex_loglinear`; its equivalence with
  `E_t r_t = 0`: `flexE_iff`; consistency with (E.6) and a new sign misprint (`−ωq_t` in (E.12) and
  in the flexible-price relation should be `+ωq_t`): `flexE_eta_zero`.
* The sum-of-squares identity (p. 698): `sos_period`, `sos_discounted`; completing the square:
  `csq_period`; `δ₀ ≡ μ_x/(1 − βη)`: `muX_eq`; `delta0_mul`, `delta0_delta`, `delta0_xhat`,
  `muX_pos`, `xhat_nonneg`; `δ` from Ch. 5 (restated): `habDelta`, `habKappa`, ….
* **Proposition 6.6 corrected (survey error 16):** `prop66_corrected` (pathwise),
  `prop66_corrected_expectation` (any `ExpectationSystem` with pull-out): the dispersion weight is
  `(1 − βη)(θ⁻¹ + ω)`, not `θ⁻¹ + ω` (equivalently `μ_x` should be `δ₀`). Refutations of the printed
  statement: `printed_E9_discounted_false` (wrong weights even for discounted sums) and
  `printed_E9_per_period_false` (no per-period version: a first-order term `βηŶ_t` survives).
* (2.28)–(2.29): `loss_form`, `welfare228`, `welfare229`, `welfare228_expectation`;
  `lam_eq_kappa_div_theta` (`λ = κ/θ`, `κ` from Ch. 5 (1.29)); the printed weights give
  `λ = (1 − βη)κ/θ`: `lamPrinted_eq`, `lamPrinted_eq_lam_iff`, `printed_lambda_false`.
* The dispersion law (2.20)/(2.24) in discounted form is `Sequences.disp_bdd`,
  `Sequences.disp_discounted`; the Calvo factors `ξ_p`, `α/((1−α)(1−αβ))` are `Moments.calvoXi`,
  `Moments.calvoK`; bounded sequences, lags and discounted shifts are `Sequences.Bdd`,
  `Sequences.lagS`, `Sequences.lagP`, `Sequences.tsum_telescope_add`.
* p. 404: `gap_rewrite` (`δ < 1`), `delta_one_case` (`x̂* ≠ 0` at `δ = 1`), `eta_zero_reduction`
  (`η = 0` gives Proposition 6.1's weights and `x*`).
* (2.30)–(2.31): `AS231_iff`, `AS230_iff` (with `as_identity` restated from Ch. 5).
-/

namespace Woodford.StabilizationWelfare.HabitWelfare

open Filter Topology
open Woodford.StabilizationWelfare.Sequences
open Moments (calvoK calvoXi)

/-! ### (E.10): the second-order expansion of the utility of habit-adjusted expenditure

All utility terms are normalised by `Ȳ u_c` (the common factor in (E.9)–(E.13)). -/

/-- Woodford (2003), App. E.1, p. 693: `Y/Ȳ − 1 = Ŷ + Ŷ²/2 + O(Ŷ³)`; `ePoly` is the second-order
polynomial. -/
noncomputable def ePoly (y : ℝ) : ℝ := y + y ^ 2 / 2

/-- Woodford (2003), (E.10), p. 696: habit-adjusted expenditure
`(Y_t − G_t) − η(Y_{t−1} − G_{t−1})` relative to steady state, divided by `Ȳ`, to second order:
`[e(Ŷ_t) − η e(Ŷ_{t−1})] − (Ĝ_t − η Ĝ_{t−1})` (`Ĝ ≡ (G − Ḡ)/Ȳ`). -/
noncomputable def cDevAt (η y ym G Gm : ℝ) : ℝ := (ePoly y - η * ePoly ym) - (G - η * Gm)

/-- Woodford (2003), (E.10), p. 696: the second-order Taylor polynomial of `u(c; ξ_t)` in the
deviation `c` (normalised by `Ȳ u_c`, terms in `ξ` alone omitted as t.i.p.):
`c − σ⁻¹c²/2 + σ⁻¹ gᵖ c`, using `Ȳ u_cc/u_c = −σ⁻¹` and `u_cξ ξ/u_c = σ⁻¹ gᵖ` with
`gᵖ ≡ −u_cξ ξ/(Ȳ u_cc)` (App. E.1, p. 693). -/
noncomputable def uTaylor (sinv c gp : ℝ) : ℝ := c - sinv / 2 * c ^ 2 + sinv * gp * c

/-- Woodford (2003), (E.10), p. 696: the policy-relevant braces
`(Ŷ_t − ηŶ_{t−1}) + ½[Ŷ_t² − ηŶ_{t−1}² − σ⁻¹(Ŷ_t − ηŶ_{t−1})²]
+ σ⁻¹(g_t − ηĜ_{t−1})(Ŷ_t − ηŶ_{t−1})` with `g_t = Ĝ_t + gᵖ_t`. -/
noncomputable def E10braceAt (sinv η y ym G Gm gp : ℝ) : ℝ :=
  (y - η * ym) + (y ^ 2 - η * ym ^ 2 - sinv * (y - η * ym) ^ 2) / 2 +
    sinv * ((G + gp) - η * Gm) * (y - η * ym)

/-- Woodford (2003), (E.10), p. 696: the terms independent of policy (functions of `Ĝ_t`,
`Ĝ_{t−1}`, `gᵖ_t` only). -/
noncomputable def E10tipAt (sinv η G Gm gp : ℝ) : ℝ :=
  -(G - η * Gm) - sinv / 2 * (G - η * Gm) ^ 2 - sinv * gp * (G - η * Gm)

/-- Woodford (2003), (E.10), p. 696: the explicit third-order remainder, with
`Q = (Ŷ_t² − ηŶ_{t−1}²)/2`. -/
noncomputable def E10remAt (sinv η y ym G Gm gp : ℝ) : ℝ :=
  -sinv * ((y ^ 2 - η * ym ^ 2) / 2) * ((y - η * ym) - (G - η * Gm)) -
    sinv / 2 * ((y ^ 2 - η * ym ^ 2) / 2) ^ 2 + sinv * gp * ((y ^ 2 - η * ym ^ 2) / 2)

/-- **Woodford (2003), eq. (E.10), p. 696 (Layer A, exact).** The second-order Taylor polynomial
of the utility of habit-adjusted expenditure equals the braces of (E.10) plus explicit
t.i.p. plus an explicit remainder of weighted degree three (`E10rem_scaling`). -/
theorem E10_identity (sinv η y ym G Gm gp : ℝ) :
    uTaylor sinv (cDevAt η y ym G Gm) gp =
      E10braceAt sinv η y ym G Gm gp + E10tipAt sinv η G Gm gp +
        E10remAt sinv η y ym G Gm gp := by
  unfold uTaylor cDevAt ePoly E10braceAt E10tipAt E10remAt
  ring

/-- Woodford (2003), (E.10), p. 696: the cofactor of `s³` in the scaled remainder. -/
noncomputable def E10remHat (s sinv η y ym G Gm gp : ℝ) : ℝ :=
  -sinv * ((y ^ 2 - η * ym ^ 2) / 2) * ((y - η * ym) - (G - η * Gm)) -
    s * (sinv / 2 * ((y ^ 2 - η * ym ^ 2) / 2) ^ 2) + sinv * gp * ((y ^ 2 - η * ym ^ 2) / 2)

/-- **Woodford (2003), (E.10), p. 696: the remainder is `O(‖ŷ, ξ̃‖³)`** (scaling lemma: scaling
all variables by `s` scales the remainder by `s³` times a polynomial in `s`). -/
theorem E10rem_scaling (s sinv η y ym G Gm gp : ℝ) :
    E10remAt sinv η (s * y) (s * ym) (s * G) (s * Gm) (s * gp) =
      s ^ 3 * E10remHat s sinv η y ym G Gm gp := by
  unfold E10remAt E10remHat
  ring

/-! ### (E.3)–(E.5): the disutility of supply with habit (`v_y = (1 − βη)(1 − Φ) u_c`) -/

/-- Woodford (2003), (E.3)–(E.4), pp. 693–694: the integrated second-order Taylor polynomial of
`ṽ(y(i); ξ)` (normalised by `Ȳ v_y/(1 − Φ)`, i.e. before multiplying by `(1 − βη)` in the habit
case): `(1 − Φ)[E_i ŷ + ½(1 + ω) E_i ŷ² − ω q E_i ŷ]`, with `m1 = E_i ŷ`, `m2 = E_i ŷ²`.
No `Φ`-terms are dropped. -/
noncomputable def vTaylor (Φ ω m1 m2 q : ℝ) : ℝ := (1 - Φ) * (m1 + (1 + ω) / 2 * m2 - ω * q * m1)

/-- Woodford (2003), (E.5), p. 694: `E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ` (the CES aggregator to
second order). -/
noncomputable def m1Of (θ y V : ℝ) : ℝ := y - (1 - θ⁻¹) / 2 * V

/-- Woodford (2003), p. 694: `E_i ŷ² = var_i ŷ + (E_i ŷ)²`. -/
noncomputable def m2Of (θ y V : ℝ) : ℝ := V + m1Of θ y V ^ 2

/-- Woodford (2003), (E.4), p. 694: the second-order part,
`(1 − Φ)Ŷ + ½(1 + ω)Ŷ² − ω q Ŷ + ½(θ⁻¹ + ω) var_i ŷ`. -/
noncomputable def vMainAt (Φ θ ω y q V : ℝ) : ℝ :=
  (1 - Φ) * y + (1 + ω) / 2 * y ^ 2 - ω * q * y + (θ⁻¹ + ω) / 2 * V

/-- Woodford (2003), (E.4), p. 694: the explicit third-order remainder (all terms of weighted
degree ≥ 3 when `Ŷ, q, Φ` have weight 1 and `var_i ŷ` weight 2). -/
noncomputable def vRemAt (Φ θ ω y q V : ℝ) : ℝ :=
  -(Φ * ((θ⁻¹ + ω) / 2 * V)) - Φ * ((1 + ω) / 2 * y ^ 2 - ω * q * y) +
    (1 - Φ) * (-((1 + ω) * ((1 - θ⁻¹) / 2) * y * V) +
      (1 + ω) / 2 * ((1 - θ⁻¹) / 2) ^ 2 * V ^ 2 + ω * q * ((1 - θ⁻¹) / 2) * V)

/-- **Woodford (2003), eq. (E.4), p. 694 (Layer A, exact).** Substituting (E.5) into the
integrated disutility gives the second-order part plus an explicit remainder. -/
theorem E4_identity (Φ θ ω y q V : ℝ) :
    vTaylor Φ ω (m1Of θ y V) (m2Of θ y V) q = vMainAt Φ θ ω y q V + vRemAt Φ θ ω y q V := by
  unfold vTaylor m2Of m1Of vMainAt vRemAt
  ring

/-- Woodford (2003), (E.4), p. 694: the cofactor of `s³` in the scaled remainder. -/
noncomputable def vRemHat (s Φ θ ω y q V : ℝ) : ℝ :=
  -(Φ * ((θ⁻¹ + ω) / 2 * V)) - Φ * ((1 + ω) / 2 * y ^ 2 - ω * q * y) +
    (1 - s * Φ) * (-((1 + ω) * ((1 - θ⁻¹) / 2) * y * V) +
      s * ((1 + ω) / 2 * ((1 - θ⁻¹) / 2) ^ 2 * V ^ 2) + ω * q * ((1 - θ⁻¹) / 2) * V)

/-- **Woodford (2003), (E.4), p. 694: the remainder is `O(‖Φ, ŷ, ξ̃‖³)`** (scaling `Φ, Ŷ, q` by `s`
and `var_i ŷ` by `s²` scales it by `s³`). -/
theorem vRem_scaling (s Φ θ ω y q V : ℝ) :
    vRemAt (s * Φ) θ ω (s * y) (s * q) (s ^ 2 * V) = s ^ 3 * vRemHat s Φ θ ω y q V := by
  unfold vRemAt vRemHat
  ring

/-! ### The habit-persistence parameters and the exogenous data -/

/-- Woodford (2003), Prop. 6.6, pp. 403–404: the structural parameters `β, η, φ, ω, θ, Φ`
(`φ ≡ (1 − βη)⁻¹σ⁻¹`, Ch. 5 eq. (1.25)). -/
structure Par where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The degree of habit persistence `η`. -/
  η : ℝ
  /-- `φ ≡ (1 − βη)⁻¹ σ⁻¹`. -/
  φ : ℝ
  /-- The elasticity `ω` of real marginal cost with respect to own output. -/
  ω : ℝ
  /-- The elasticity of substitution `θ` between differentiated goods. -/
  θ : ℝ
  /-- The steady-state distortion `Φ_y`. -/
  Φ : ℝ

namespace Par

/-- Woodford (2003), p. 697: `σ⁻¹ = (1 − βη)φ`. -/
noncomputable def sinv (P : Par) : ℝ := (1 - P.β * P.η) * P.φ

/-- Woodford (2003), p. 404: `A ≡ ω + φ(1 + βη²)` (the bracket in `μ_x`). -/
noncomputable def A (P : Par) : ℝ := P.ω + P.φ * (1 + P.β * P.η ^ 2)

end Par

/-- Woodford (2003), App. E.3, pp. 696–697: the exogenous data (paths are realisations): `Ĝ_t`
with `Ĝ_{−1}`, the preference part `gᵖ_t` of `g_t = Ĝ_t + gᵖ_t`, `q_t`, and the natural rate
`Ŷⁿ_t` with `Ŷⁿ_{−1}`. -/
structure Exo where
  /-- Government purchases `Ĝ_t ≡ (G_t − Ḡ)/Ȳ`. -/
  G : ℕ → ℝ
  /-- The initial value `Ĝ_{−1}`. -/
  Gm1 : ℝ
  /-- The preference-shock part `gᵖ_t = −u_cξ ξ_t/(Ȳ u_cc)` of `g_t`. -/
  gp : ℕ → ℝ
  /-- The supply shock `q_t ≡ −v_yξ ξ_t/(Ȳ v_yy)`. -/
  q : ℕ → ℝ
  /-- The natural rate of output `Ŷⁿ_t`. -/
  n : ℕ → ℝ
  /-- The initial value `Ŷⁿ_{−1}`. -/
  nm1 : ℝ

/-- Woodford (2003), App. E.3, p. 697: all exogenous sequences are bounded. -/
def Exo.Bounded (e : Exo) : Prop := Bdd e.G ∧ Bdd e.gp ∧ Bdd e.q ∧ Bdd e.n

/-- Woodford (2003), App. E.1, p. 693: `g_t = Ĝ_t + gᵖ_t`. -/
def gS (e : Exo) (t : ℕ) : ℝ := e.G t + e.gp t

/-- Woodford (2003), (E.11), p. 697: `g̃_t ≡ (g_t − ηĜ_{t−1}) − βη(g_{t+1} − ηĜ_t)` along a
realised path (the book's `E_t g_{t+1}` is restored under `E_0` in `E11_expectation`). -/
noncomputable def gTil (P : Par) (e : Exo) (t : ℕ) : ℝ :=
  (gS e t - P.η * lagS e.Gm1 e.G t) - P.β * P.η * (gS e (t + 1) - P.η * e.G t)

/-- Woodford (2003), (2.26) and (E.10)–(E.12), pp. 403, 696–697: the period utility polynomial
`U_t` (in units of `Ȳ u_c`): the expansion of `u((Y_t − G_t) − η(Y_{t−1} − G_{t−1}); ξ_t)` minus
`(1 − βη)` times the integrated disutility (since `v_y = (1 − βη)(1 − Φ) u_c`). The
endogenous variables are output `Ŷ_t` (with `Ŷ_{−1}`) and dispersion `V_t = var_i ŷ_t(i)`. -/
noncomputable def Useq (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) : ℝ :=
  uTaylor P.sinv (cDevAt P.η (Y t) (lagS Ym1 Y t) (e.G t) (lagS e.Gm1 e.G t)) (e.gp t) -
    (1 - P.β * P.η) * vTaylor P.Φ P.ω (m1Of P.θ (Y t) (V t)) (m2Of P.θ (Y t) (V t)) (e.q t)

/-- Woodford (2003), (E.10), p. 696: the braces of (E.10) along a path. -/
noncomputable def braceSeq (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  E10braceAt P.sinv P.η (Y t) (lagS Ym1 Y t) (e.G t) (lagS e.Gm1 e.G t) (e.gp t)

/-- Woodford (2003), (E.11), p. 697: the summand
`(1 − βη)Ŷ_t + ½[(1 − βη) − σ⁻¹(1 + βη²)]Ŷ_t² + ησ⁻¹Ŷ_tŶ_{t−1} + σ⁻¹g̃_tŶ_t`. -/
noncomputable def E11seq (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - P.β * P.η) * Y t + ((1 - P.β * P.η) - P.sinv * (1 + P.β * P.η ^ 2)) / 2 * Y t ^ 2 +
    P.η * P.sinv * Y t * lagS Ym1 Y t + P.sinv * gTil P e t * Y t

/-- Woodford (2003), (E.11), p. 697: the lagged terms moved forward (an initial-condition term
at `t = 0`). -/
noncomputable def K1 (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  -(P.η * lagS Ym1 Y t) - P.η / 2 * lagS Ym1 Y t ^ 2 - P.sinv * P.η ^ 2 / 2 * lagS Ym1 Y t ^ 2 -
    P.sinv * P.η * (gS e t - P.η * lagS e.Gm1 e.G t) * lagS Ym1 Y t

/-- **Woodford (2003), (E.10) ⇒ (E.11), pp. 696–697, period by period:** the braces of (E.10)
equal the summand of (E.11) plus `K_t − βK_{t+1}`. -/
theorem E11_period (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) :
    braceSeq P e Ym1 Y t = E11seq P e Ym1 Y t + (K1 P e Ym1 Y t - P.β * K1 P e Ym1 Y (t + 1)) := by
  unfold braceSeq E10braceAt E11seq K1 gTil gS
  simp only [lagS_succ]
  ring

/-- **Woodford (2003), eq. (E.11), p. 697 (pathwise, genuine discounted sums).** For bounded
`Ŷ, Ĝ, gᵖ` and `0 ≤ β < 1`:
`∑ βᵗ {(E.10) braces} = ∑ βᵗ {(E.11) summand} + K_0`, where
`K_0 = −ηŶ_{−1} − (η/2)Ŷ_{−1}² − (σ⁻¹η²/2)Ŷ_{−1}² − σ⁻¹η(g_0 − ηĜ_{−1})Ŷ_{−1}` is t.i.p. -/
theorem E11_discounted (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (h0 : 0 ≤ P.β) (h1 : P.β < 1)
    (hY : Bdd Y) (he : e.Bounded) :
    ∑' t, P.β ^ t * braceSeq P e Ym1 Y t =
      ∑' t, P.β ^ t * E11seq P e Ym1 Y t + K1 P e Ym1 Y 0 := by
  obtain ⟨hG, hgp, -, -⟩ := he
  refine tsum_telescope_add h0 h1 ?_ ?_ (E11_period P e Ym1 Y)
  · unfold E11seq gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  · unfold K1 gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])

/-! ### (E.12): subtracting the disutility of supply -/

/-- Woodford (2003), (E.12), p. 697: the summand
`Φ Ŷ_t − ½[ω + φ(1 + βη²)]Ŷ_t² + ηφŶ_tŶ_{t−1} + (φ g̃_t + ω q_t)Ŷ_t − ½(θ⁻¹ + ω) var_i ŷ_t`.
**The sign of `ω q_t` is `+`** (the book prints `−ω q_t` in (E.12) and in the flexible-price
relation; see `flexE_eta_zero`). -/
noncomputable def E12seq (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) : ℝ :=
  P.Φ * Y t - P.A / 2 * Y t ^ 2 + P.η * P.φ * Y t * lagS Ym1 Y t +
    (P.φ * gTil P e t + P.ω * e.q t) * Y t - (P.θ⁻¹ + P.ω) / 2 * V t

/-- Woodford (2003), (E.10), p. 696: the t.i.p. of the period utility along a path. -/
noncomputable def tipSeq (P : Par) (e : Exo) (t : ℕ) : ℝ :=
  E10tipAt P.sinv P.η (e.G t) (lagS e.Gm1 e.G t) (e.gp t)

/-- Woodford (2003), (E.10)–(E.12): the total third-order remainder of the period utility. -/
noncomputable def RUseq (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) : ℝ :=
  E10remAt P.sinv P.η (Y t) (lagS Ym1 Y t) (e.G t) (lagS e.Gm1 e.G t) (e.gp t) -
    (1 - P.β * P.η) * vRemAt P.Φ P.θ P.ω (Y t) (e.q t) (V t)

/-- **Woodford (2003), (E.10)–(E.12), pp. 696–697, period by period (Layer A, exact).**
`U_t = (1 − βη)·{(E.12) summand} + t.i.p._t + R_t + (K_t − βK_{t+1})`. -/
theorem E12_period (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) :
    Useq P e Ym1 Y V t = (1 - P.β * P.η) * E12seq P e Ym1 Y V t + tipSeq P e t +
      RUseq P e Ym1 Y V t + (K1 P e Ym1 Y t - P.β * K1 P e Ym1 Y (t + 1)) := by
  unfold Useq E12seq tipSeq RUseq
  rw [E10_identity, E4_identity]
  have h := E11_period P e Ym1 Y t
  unfold braceSeq at h
  rw [h]
  unfold E11seq vMainAt Par.sinv Par.A
  ring

/-- **Woodford (2003), eq. (E.12), p. 697 (pathwise, genuine discounted sums).** For bounded
paths and `0 ≤ β < 1`,
`∑ βᵗ U_t = (1 − βη)∑ βᵗ{(E.12) summand} + ∑ βᵗ t.i.p._t + ∑ βᵗ R_t + K_0`. -/
theorem E12_discounted (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (h0 : 0 ≤ P.β)
    (h1 : P.β < 1) (hY : Bdd Y) (hV : Bdd V) (he : e.Bounded) :
    ∑' t, P.β ^ t * Useq P e Ym1 Y V t =
      (1 - P.β * P.η) * ∑' t, P.β ^ t * E12seq P e Ym1 Y V t + ∑' t, P.β ^ t * tipSeq P e t +
        ∑' t, P.β ^ t * RUseq P e Ym1 Y V t + K1 P e Ym1 Y 0 := by
  obtain ⟨hG, hgp, hq, -⟩ := he
  have hE : Bdd (E12seq P e Ym1 Y V) := by
    unfold E12seq gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hT : Bdd (tipSeq P e) := by
    unfold tipSeq E10tipAt
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hR : Bdd (RUseq P e Ym1 Y V) := by
    unfold RUseq E10remAt vRemAt
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hK : Bdd (K1 P e Ym1 Y) := by
    unfold K1 gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  rw [tsum_telescope_add h0 h1 ((((Bdd.const _).mul hE).add hT).add hR) hK
    (E12_period P e Ym1 Y V), tsum_add3 h0 h1 _ hE hT hR]

/-! ### (E.13): the output gap -/

/-- Woodford (2003), App. E.3, p. 697: the output gap `x_t ≡ Ŷ_t − Ŷⁿ_t`. -/
def xS (e : Exo) (Y : ℕ → ℝ) (t : ℕ) : ℝ := Y t - e.n t

/-- Woodford (2003), App. E.3, p. 697: the flexible-price residual
`r_t = [ω + φ(1 + βη²)]Ŷⁿ_t − ηφŶⁿ_{t−1} − βηφŶⁿ_{t+1} − (φ g̃_t + ω q_t)` along a realised path;
the book's flexible-price relation is `E_t r_t = 0` (`flexE_iff`). -/
noncomputable def rS (P : Par) (e : Exo) (t : ℕ) : ℝ :=
  P.A * e.n t - P.η * P.φ * lagS e.nm1 e.n t - P.β * P.η * P.φ * e.n (t + 1) -
    (P.φ * gTil P e t + P.ω * e.q t)

/-- Woodford (2003), (E.13), p. 697: the terms in `Ŷⁿ` alone (t.i.p.). -/
noncomputable def tipN (P : Par) (e : Exo) (t : ℕ) : ℝ :=
  P.Φ * e.n t - P.A / 2 * e.n t ^ 2 + P.η * P.φ * e.n t * lagS e.nm1 e.n t +
    (P.φ * gTil P e t + P.ω * e.q t) * e.n t

/-- Woodford (2003), (E.13), p. 697: the cross term `ηφ Ŷⁿ_t x_{t−1}` moved forward. -/
noncomputable def kS (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  P.η * P.φ * e.n t * lagS (Ym1 - e.nm1) (xS e Y) t

/-- Woodford (2003), (E.13), p. 697: the summand
`Φ x_t − ½[ω + φ(1 + βη²)]x_t² + ηφ x_t x_{t−1} − ½(θ⁻¹ + ω) var_i ŷ_t`. -/
noncomputable def E13main (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) : ℝ :=
  P.Φ * xS e Y t - P.A / 2 * xS e Y t ^ 2 +
    P.η * P.φ * xS e Y t * lagS (Ym1 - e.nm1) (xS e Y) t - (P.θ⁻¹ + P.ω) / 2 * V t

/-- **Woodford (2003), (E.12) ⇒ (E.13), p. 697, period by period (exact).** Substituting
`Ŷ = x + Ŷⁿ`: `(E.12) summand = (E.13) summand − r_t x_t + t.i.p._t + (k_t − βk_{t+1})`. -/
theorem E13_period (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) :
    E12seq P e Ym1 Y V t = E13main P e Ym1 Y V t - rS P e t * xS e Y t + tipN P e t +
      (kS P e Ym1 Y t - P.β * kS P e Ym1 Y (t + 1)) := by
  unfold E12seq E13main rS tipN kS
  have hl : ∀ s, lagS (Ym1 - e.nm1) (xS e Y) s = lagS Ym1 Y s - lagS e.nm1 e.n s :=
    fun s => lagS_sub Ym1 e.nm1 Y e.n s
  rw [hl, hl]
  unfold xS
  simp only [lagS_succ]
  ring

/-- Woodford (2003), (E.13), p. 697: the policy-independent part of the period utility in gap
form, `t.i.p._t + (1 − βη)·(terms in Ŷⁿ)`. -/
noncomputable def tipU (P : Par) (e : Exo) (t : ℕ) : ℝ :=
  tipSeq P e t + (1 - P.β * P.η) * tipN P e t

/-- **Woodford (2003), eq. (E.13), p. 697 (pathwise, genuine discounted sums).**
`∑ βᵗ U_t = (1 − βη)∑ βᵗ[(E.13) summand − r_t x_t] + ∑ βᵗ t.i.p._t + ∑ βᵗ R_t
+ K_0 + (1 − βη)k_0`; the `r_t x_t` terms vanish under perfect foresight with the
flexible-price relation, and in expectation in general (`prop66_corrected_expectation`). -/
theorem E13_discounted (P : Par) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (h0 : 0 ≤ P.β)
    (h1 : P.β < 1) (hY : Bdd Y) (hV : Bdd V) (he : e.Bounded) :
    ∑' t, P.β ^ t * Useq P e Ym1 Y V t =
      (1 - P.β * P.η) * ∑' t, P.β ^ t * (E13main P e Ym1 Y V t - rS P e t * xS e Y t) +
        ∑' t, P.β ^ t * tipU P e t + ∑' t, P.β ^ t * RUseq P e Ym1 Y V t +
          (K1 P e Ym1 Y 0 + (1 - P.β * P.η) * kS P e Ym1 Y 0) := by
  obtain ⟨hG, hgp, hq, hn⟩ := he
  have hx : Bdd (xS e Y) := hY.sub hn
  have hM : Bdd (fun t => E13main P e Ym1 Y V t - rS P e t * xS e Y t) := by
    unfold E13main rS gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hT : Bdd (tipU P e) := by
    unfold tipU tipSeq E10tipAt tipN gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hR : Bdd (RUseq P e Ym1 Y V) := by
    unfold RUseq E10remAt vRemAt
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hK : Bdd (fun t => K1 P e Ym1 Y t + (1 - P.β * P.η) * kS P e Ym1 Y t) := by
    unfold K1 kS gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  rw [tsum_telescope_add h0 h1 ((((Bdd.const _).mul hM).add hT).add hR) hK (fun t => ?_),
    tsum_add3 h0 h1 _ hM hT hR]
  rw [E12_period, E13_period]
  unfold tipU
  ring

/-! ### The sum-of-squares identity and completing the square (p. 698) -/

/-- **Woodford (2003), App. E.3, p. 698 (the sum-of-squares relation), period by period.**
If `δ₀(1 + βδ²) = A` and `δ₀δ = b`, then
`−(A/2)x_t² + b x_t x_{t−1} = −(δ₀/2)(x_t − δx_{t−1})² + (J_t − βJ_{t+1})`,
`J_t = (δ₀δ²/2) x_{t−1}²`. -/
theorem sos_period {A b β δ δ₀ xm1 : ℝ} (x : ℕ → ℝ) (hA : δ₀ * (1 + β * δ ^ 2) = A)
    (hb : δ₀ * δ = b) (t : ℕ) :
    -(A / 2) * x t ^ 2 + b * x t * lagS xm1 x t =
      -(δ₀ / 2) * (x t - δ * lagS xm1 x t) ^ 2 +
        (δ₀ * δ ^ 2 / 2 * lagS xm1 x t ^ 2 - β * (δ₀ * δ ^ 2 / 2 * lagS xm1 x (t + 1) ^ 2)) := by
  rw [lagS_succ, ← hA, ← hb]
  ring

/-- **Woodford (2003), App. E.3, p. 698: the sum-of-squares identity**
`∑ βᵗ{−½[ω + φ(1 + βη²)]x_t² + ηφ x_t x_{t−1}} = ½δ₀δ²x_{−1}² − ½δ₀ ∑ βᵗ(x_t − δx_{t−1})²`
(genuine discounted sums of a bounded path, `0 ≤ β < 1`), for any `δ, δ₀` with
`δ₀(1 + βδ²) = A`, `δ₀δ = b`. -/
theorem sos_discounted {A b β δ δ₀ xm1 : ℝ} {x : ℕ → ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (hx : Bdd x)
    (hA : δ₀ * (1 + β * δ ^ 2) = A) (hb : δ₀ * δ = b) :
    ∑' t, β ^ t * (-(A / 2) * x t ^ 2 + b * x t * lagS xm1 x t) =
      δ₀ * δ ^ 2 / 2 * xm1 ^ 2 - δ₀ / 2 * ∑' t, β ^ t * (x t - δ * lagS xm1 x t) ^ 2 := by
  have hsq : Bdd (fun t => (x t - δ * lagS xm1 x t) ^ 2) :=
    (hx.sub ((Bdd.const δ).mul (hx.lagS xm1))).pow 2
  have hJ : Bdd (fun t => δ₀ * δ ^ 2 / 2 * lagS xm1 x t ^ 2) := (Bdd.const _).mul
    ((hx.lagS xm1).pow 2)
  rw [tsum_telescope_add h0 h1 ((Bdd.const (-(δ₀ / 2))).mul hsq) hJ
    (fun t => sos_period x hA hb t)]
  have hfun : (fun t => β ^ t * (-(δ₀ / 2) * (x t - δ * lagS xm1 x t) ^ 2)) =
      fun t => -(δ₀ / 2) * (β ^ t * (x t - δ * lagS xm1 x t) ^ 2) := by
    funext t; ring
  rw [hfun, tsum_mul_left, lagS_zero]
  ring

/-- **Woodford (2003), App. E.3, p. 698 (completing the square), period by period.** If moreover
`δ₀ x̂*(1 − βδ) = Φ`, then
`Φx_t − (A/2)x_t² + b x_t x_{t−1} = −(δ₀/2)(x_t − δx_{t−1} − x̂*)² + δ₀x̂*²/2 + (J_t − βJ_{t+1})`
with `J_t = (δ₀δ²/2)x_{t−1}² + δ₀δx̂* x_{t−1}`. -/
theorem csq_period {A b β δ δ₀ Φ xh xm1 : ℝ} (x : ℕ → ℝ) (hA : δ₀ * (1 + β * δ ^ 2) = A)
    (hb : δ₀ * δ = b) (hΦ : δ₀ * xh * (1 - β * δ) = Φ) (t : ℕ) :
    Φ * x t - A / 2 * x t ^ 2 + b * x t * lagS xm1 x t =
      -(δ₀ / 2) * (x t - δ * lagS xm1 x t - xh) ^ 2 + δ₀ * xh ^ 2 / 2 +
        ((δ₀ * δ ^ 2 / 2 * lagS xm1 x t ^ 2 + δ₀ * δ * xh * lagS xm1 x t) -
          β * (δ₀ * δ ^ 2 / 2 * lagS xm1 x (t + 1) ^ 2 + δ₀ * δ * xh * lagS xm1 x (t + 1))) := by
  rw [lagS_succ, ← hA, ← hb, ← hΦ]
  ring


/-! ### The coefficient `δ` of Chapter 5, (1.28)–(1.29)

Restated from the Woodford Chapter 5 project (`PolicyResponseDynamics.Habit`): `δ` is the
smaller root of `ηφ(1 + βδ²) = [ω + φ(1 + βη²)]δ`, written without division by `η`, and
`κ = ξ_p ηφ/δ`, written without division by `δ`. -/

/-- Woodford (2003), (1.28), p. 335: `B ≡ ω + φ(1 + βη²)`, the coefficient of `δ`. -/
noncomputable def habB (β ω vphi η : ℝ) : ℝ := ω + vphi * (1 + β * η ^ 2)

/-- Woodford (2003), (1.28), p. 335: the discriminant `B² − 4β(ηφ)²` of
`βηφ δ² − B δ + ηφ = 0`. -/
noncomputable def habDisc (β ω vphi η : ℝ) : ℝ := habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2

/-- Woodford (2003), (1.28), p. 335: the smaller root of (1.28), written without division by
`η`: `δ = 2ηφ/(B + √(B² − 4β(ηφ)²))` (so `δ = 0` at `η = 0`). -/
noncomputable def habDelta (β ω vphi η : ℝ) : ℝ :=
  2 * η * vphi / (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η))

/-- Woodford (2003), (1.29), p. 335: `κ`, written without division by `δ`:
`κ = ξ_p (B + √(B² − 4β(ηφ)²))/2` (equal to `ξ_p ηφ/δ` for `η > 0`, `habKappa_eq`). -/
noncomputable def habKappa (ξp β ω vphi η : ℝ) : ℝ :=
  ξp * (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η)) / 2

/-- Woodford (2003), p. 335: the discriminant of (1.28) is nonnegative (`β ≥ 0`, `ω ≥ 0`,
`φ > 0`), since `(1 + βη²)² − 4βη² = (1 − βη²)²`. -/
theorem habDisc_nonneg {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 ≤ habDisc β ω vphi η := by
  unfold habDisc habB
  have h1 : vphi * (1 + β * η ^ 2) ≤ ω + vphi * (1 + β * η ^ 2) := by linarith
  have h0 : 0 ≤ vphi * (1 + β * η ^ 2) := by positivity
  have h2 : (vphi * (1 + β * η ^ 2)) ^ 2 ≤ (ω + vphi * (1 + β * η ^ 2)) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (vphi * (1 - β * η ^ 2))]

/-- Woodford (2003), p. 335: `B + √D > 0`. -/
theorem habB_add_sqrt_pos {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 < habB β ω vphi η + Real.sqrt (habDisc β ω vphi η) := by
  have : 0 < habB β ω vphi η := by unfold habB; positivity
  linarith [Real.sqrt_nonneg (habDisc β ω vphi η)]

/-- **Woodford (2003), (1.28), p. 335: `δ` is a root**, `ηφ(1 + βδ²) = [ω + φ(1 + βη²)] δ`. -/
theorem habDelta_root {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    η * vphi * (1 + β * habDelta β ω vphi η ^ 2) =
      habB β ω vphi η * habDelta β ω vphi η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ hω hφ)
  unfold habDelta
  set S := Real.sqrt (habDisc β ω vphi η)
  set B := habB β ω vphi η
  field_simp
  linear_combination η * hs

/-- Woodford (2003), (1.29), p. 335: `κδ = ξ_p ηφ` (for every `η ≥ 0`, no division). -/
theorem habKappa_mul_delta {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habKappa ξp β ω vphi η * habDelta β ω vphi η = ξp * η * vphi := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  unfold habKappa habDelta
  field_simp

/-- Woodford (2003), (1.27)–(1.29), p. 335: `κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))`. -/
theorem habKappa_mul {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habKappa ξp β ω vphi η * (1 + β * habDelta β ω vphi η ^ 2) =
      ξp * (ω + vphi * (1 + β * η ^ 2)) := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ hω hφ)
  unfold habKappa habDelta
  rw [show ω + vphi * (1 + β * η ^ 2) = habB β ω vphi η from rfl]
  set S := Real.sqrt (habDisc β ω vphi η)
  set B := habB β ω vphi η
  field_simp
  linear_combination ξp * hs

/-- **Woodford (2003), (1.29), p. 335:** for `η > 0`, `κ = ξ_p ηφ/δ`. -/
theorem habKappa_eq {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) : habKappa ξp β ω vphi η = ξp * η * vphi / habDelta β ω vphi η := by
  have hd : 0 < habDelta β ω vphi η := by
    unfold habDelta
    exact div_pos (by positivity) (habB_add_sqrt_pos hβ hω hφ)
  rw [eq_div_iff hd.ne', habKappa_mul_delta hβ hω hφ]

/-- Woodford (2003), (1.29), p. 335: `κ > 0` (`ξ_p > 0`). -/
theorem habKappa_pos {ξp β ω vphi η : ℝ} (hξ : 0 < ξp) (hβ : 0 ≤ β) (hω : 0 ≤ ω)
    (hφ : 0 < vphi) : 0 < habKappa ξp β ω vphi η := by
  unfold habKappa
  exact div_pos (mul_pos hξ (habB_add_sqrt_pos hβ hω hφ)) two_pos

/-- Woodford (2003), p. 335: `δ ≥ 0` for `η ≥ 0`. -/
theorem habDelta_nonneg {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 ≤ η) : 0 ≤ habDelta β ω vphi η :=
  div_nonneg (by positivity) (habB_add_sqrt_pos hβ hω hφ).le

/-- Woodford (2003), p. 335 (strictness at the lower end): `δ > 0 ↔ η > 0`. -/
theorem habDelta_pos_iff {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 < habDelta β ω vphi η ↔ 0 < η := by
  unfold habDelta
  rw [div_pos_iff_of_pos_right (habB_add_sqrt_pos hβ hω hφ)]
  constructor
  · intro h; nlinarith
  · intro h; positivity

/-- Woodford (2003), p. 335: `2φ − B ≤ √D`, with `D − (2φ − B)² = 4φω`. -/
theorem two_vphi_sub_le_sqrt {β ω vphi η : ℝ} (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    2 * vphi - habB β ω vphi η ≤ Real.sqrt (habDisc β ω vphi η) := by
  have hD : (2 * vphi - habB β ω vphi η) ^ 2 + 4 * vphi * ω = habDisc β ω vphi η := by
    unfold habDisc habB; ring
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith

/-- **Woodford (2003), p. 335: `0 ≤ δ ≤ η`.** -/
theorem habDelta_le {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) (hη : 0 ≤ η) :
    habDelta β ω vphi η ≤ η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have h2 := two_vphi_sub_le_sqrt (β := β) (η := η) hω hφ
  unfold habDelta
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Woodford (2003), p. 335 (strictness at the upper end): for `η > 0` and `ω > 0`, `δ < η`. -/
theorem habDelta_lt {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 < ω) (hφ : 0 < vphi) (hη : 0 < η) :
    habDelta β ω vphi η < η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω.le hφ
  have hlt : 2 * vphi - habB β ω vphi η < Real.sqrt (habDisc β ω vphi η) := by
    rcases lt_or_ge (2 * vphi - habB β ω vphi η) 0 with h | h
    · exact lt_of_lt_of_le h (Real.sqrt_nonneg _)
    · have hD : (2 * vphi - habB β ω vphi η) ^ 2 + 4 * vphi * ω = habDisc β ω vphi η := by
        unfold habDisc habB; ring
      rw [Real.lt_sqrt h, ← hD]
      nlinarith [mul_pos hφ hω]
  unfold habDelta
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- Woodford (2003), p. 335 (strictness at the upper end): with `ω = 0` (and `βη² ≤ 1`),
`δ = η`. -/
theorem habDelta_eq_of_omega_zero {β vphi η : ℝ} (hφ : 0 < vphi)
    (hb : β * η ^ 2 ≤ 1) : habDelta β 0 vphi η = η := by
  have hD : habDisc β 0 vphi η = (vphi * (1 - β * η ^ 2)) ^ 2 := by
    unfold habDisc habB; ring
  have hS : Real.sqrt (habDisc β 0 vphi η) = vphi * (1 - β * η ^ 2) := by
    rw [hD, Real.sqrt_sq (by nlinarith)]
  unfold habDelta
  rw [hS]
  unfold habB
  have : (0 : ℝ) + vphi * (1 + β * η ^ 2) + vphi * (1 - β * η ^ 2) = 2 * vphi := by ring
  rw [this]
  field_simp

/-- **Woodford (2003), p. 335: exact strictness of `0 ≤ δ ≤ η`.** For `0 < η` with
`βη² ≤ 1`: `δ < η ↔ ω > 0` (and `δ > 0 ↔ η > 0`, `habDelta_pos_iff`). -/
theorem habDelta_lt_iff {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) (hb : β * η ^ 2 ≤ 1) : habDelta β ω vphi η < η ↔ 0 < ω := by
  constructor
  · intro h
    rcases hω.lt_or_eq with h' | h'
    · exact h'
    · subst h'
      rw [habDelta_eq_of_omega_zero hφ hb] at h
      exact absurd h (lt_irrefl _)
  · intro h
    exact habDelta_lt hβ h hφ hη

/-- Woodford (2003), (1.28), p. 335: the larger root `δ' = (B + √D)/(2βηφ)`. -/
noncomputable def habDelta2 (β ω vphi η : ℝ) : ℝ :=
  (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η)) / (2 * β * η * vphi)

/-- **Woodford (2003), (1.28), p. 335: `δ` is the smaller root.** For `β, η > 0`, every root
`d` of (1.28) is `δ` or `δ'`, `δ δ' = β⁻¹`, and `δ ≤ δ'`; when moreover `η ≤ 1` and `β < 1`,
`δ' > 1`. -/
theorem habDelta_smaller_root {β ω vphi η : ℝ} (hβ : 0 < β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) :
    (∀ d, η * vphi * (1 + β * d ^ 2) = habB β ω vphi η * d →
      d = habDelta β ω vphi η ∨ d = habDelta2 β ω vphi η) ∧
    habDelta β ω vphi η * habDelta2 β ω vphi η = β⁻¹ ∧
    habDelta β ω vphi η ≤ habDelta2 β ω vphi η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ.le hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ.le hω hφ)
  have hprod : habDelta β ω vphi η * habDelta2 β ω vphi η = β⁻¹ := by
    unfold habDelta habDelta2
    field_simp
  have hsum : habDelta β ω vphi η + habDelta2 β ω vphi η =
      habB β ω vphi η / (β * η * vphi) := by
    unfold habDelta habDelta2
    field_simp
    linear_combination hs
  refine ⟨fun d hd => ?_, hprod, ?_⟩
  · have hfac : β * η * vphi * ((d - habDelta β ω vphi η) * (d - habDelta2 β ω vphi η)) = 0 := by
      have e : (d - habDelta β ω vphi η) * (d - habDelta2 β ω vphi η) =
          d ^ 2 - (habDelta β ω vphi η + habDelta2 β ω vphi η) * d +
            habDelta β ω vphi η * habDelta2 β ω vphi η := by ring
      rw [e, hsum, hprod]
      field_simp
      linear_combination hd
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso; have : 0 < β * η * vphi := by positivity
      linarith
    · rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
  · unfold habDelta habDelta2
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [Real.sqrt_nonneg (habDisc β ω vphi η), hs]


/-! ### The weights of Proposition 6.6 -/

namespace Par

/-- Woodford (2003), Prop. 6.6, p. 403: `δ`, the smaller root of Ch. 5 (1.28). -/
noncomputable def δ (P : Par) : ℝ := habDelta P.β P.ω P.φ P.η

/-- Woodford (2003), App. E.3, p. 698: `δ₀ ≡ [ω + φ(1 + βη²)]/(1 + βδ²)` (the book writes
`δ₀ ≡ μ_x/(1 − βη)`, `muX_eq`). -/
noncomputable def δ0 (P : Par) : ℝ := P.A / (1 + P.β * P.δ ^ 2)

/-- Woodford (2003), (2.27), p. 404: the printed weight
`μ_x ≡ (1 − βη)/(1 + βδ²) · [ω + φ(1 + βη²)]`. -/
noncomputable def muX (P : Par) : ℝ := (1 - P.β * P.η) / (1 + P.β * P.δ ^ 2) * P.A

/-- Woodford (2003), (2.27), p. 404: the target
`x̂* ≡ (1 + βδ²)/(1 − βδ) · Φ_y/[ω + φ(1 + βη²)]`. -/
noncomputable def xhat (P : Par) : ℝ := (1 + P.β * P.δ ^ 2) / (1 - P.β * P.δ) * (P.Φ / P.A)

/-- Woodford (2003), Prop. 6.6, p. 403: the maintained parameter restrictions
`0 ≤ β < 1`, `0 ≤ η ≤ 1`, `φ > 0`, `ω ≥ 0`. -/
def Std (P : Par) : Prop := 0 ≤ P.β ∧ P.β < 1 ∧ 0 ≤ P.η ∧ P.η ≤ 1 ∧ 0 < P.φ ∧ 0 ≤ P.ω

end Par

/-- Woodford (2003), p. 404: `A = ω + φ(1 + βη²) > 0`. -/
theorem A_pos {P : Par} (hP : P.Std) : 0 < P.A := by
  obtain ⟨hβ0, -, -, -, hφ, hω⟩ := hP
  unfold Par.A; positivity

/-- Woodford (2003), p. 404: `A` is the `habB` coefficient of Ch. 5 (1.28). -/
theorem A_eq_habB (P : Par) : P.A = habB P.β P.ω P.φ P.η := rfl

/-- Woodford (2003), p. 403: `0 ≤ δ ≤ η`. -/
theorem delta_mem {P : Par} (hP : P.Std) : 0 ≤ P.δ ∧ P.δ ≤ P.η := by
  obtain ⟨hβ0, -, hη0, -, hφ, hω⟩ := hP
  exact ⟨habDelta_nonneg hβ0 hω hφ hη0, habDelta_le hβ0 hω hφ hη0⟩

/-- Woodford (2003), p. 404: `1 + βδ² > 0`. -/
theorem one_add_pos {P : Par} (hP : P.Std) : 0 < 1 + P.β * P.δ ^ 2 := by
  have := hP.1; positivity

/-- Woodford (2003), p. 404: `βδ < 1` (so `x̂*` is well defined). -/
theorem beta_delta_lt {P : Par} (hP : P.Std) : P.β * P.δ < 1 := by
  obtain ⟨hd0, hd1⟩ := delta_mem hP
  obtain ⟨hβ0, hβ1, -, hη1, -, -⟩ := hP
  nlinarith

/-- Woodford (2003), p. 404: `βη < 1`. -/
theorem beta_eta_lt {P : Par} (hP : P.Std) : P.β * P.η < 1 := by
  obtain ⟨hβ0, hβ1, hη0, hη1, -, -⟩ := hP
  nlinarith

/-- Woodford (2003), App. E.3, p. 698: `δ₀(1 + βδ²) = ω + φ(1 + βη²)`. -/
theorem delta0_mul {P : Par} (hP : P.Std) : P.δ0 * (1 + P.β * P.δ ^ 2) = P.A := by
  unfold Par.δ0; field_simp [(one_add_pos hP).ne']

/-- Woodford (2003), App. E.3, p. 698: `δ₀δ = ηφ` (Ch. 5 (1.28)). -/
theorem delta0_delta {P : Par} (hP : P.Std) : P.δ0 * P.δ = P.η * P.φ := by
  obtain ⟨hβ0, -, -, -, hφ, hω⟩ := hP
  have hr := habDelta_root (η := P.η) hβ0 hω hφ
  have hpos : 0 < 1 + P.β * P.δ ^ 2 := by positivity
  unfold Par.δ0
  rw [div_mul_eq_mul_div, div_eq_iff hpos.ne', A_eq_habB]
  unfold Par.δ
  linear_combination -hr

/-- Woodford (2003), App. E.3, p. 698: `δ₀ x̂*(1 − βδ) = Φ_y` (the linear terms are absorbed by
the target `x̂*`). -/
theorem delta0_xhat {P : Par} (hP : P.Std) : P.δ0 * P.xhat * (1 - P.β * P.δ) = P.Φ := by
  have h1 := (one_add_pos hP).ne'
  have h2 : 1 - P.β * P.δ ≠ 0 := (sub_pos.mpr (beta_delta_lt hP)).ne'
  have h3 := (A_pos hP).ne'
  unfold Par.δ0 Par.xhat
  field_simp

/-- **Woodford (2003), App. E.3, p. 698: `δ₀ ≡ μ_x/(1 − βη)`**, i.e. `μ_x = (1 − βη)δ₀`. -/
theorem muX_eq (P : Par) : P.muX = (1 - P.β * P.η) * P.δ0 := by
  unfold Par.muX Par.δ0; ring

/-- Woodford (2003), p. 404: `μ_x > 0` and `δ₀ > 0`. -/
theorem muX_pos {P : Par} (hP : P.Std) : 0 < P.muX ∧ 0 < P.δ0 := by
  have hA := A_pos hP
  have h1 := one_add_pos hP
  have h2 : 0 < 1 - P.β * P.η := sub_pos.mpr (beta_eta_lt hP)
  refine ⟨?_, div_pos hA h1⟩
  unfold Par.muX; positivity

/-- Woodford (2003), p. 404: `x̂* ≥ 0` when `Φ_y ≥ 0`. -/
theorem xhat_nonneg {P : Par} (hP : P.Std) (hΦ : 0 ≤ P.Φ) : 0 ≤ P.xhat := by
  have hA := A_pos hP
  have h1 := one_add_pos hP
  have h2 : 0 < 1 - P.β * P.δ := sub_pos.mpr (beta_delta_lt hP)
  unfold Par.xhat; positivity

/-! ### Proposition 6.6, corrected -/

/-- Woodford (2003), App. E.3, p. 698: the policy-independent terms of the corrected
Proposition 6.6 — a function of the exogenous data and the initial conditions
`Ŷ_{−1}`, `x_{−1} = Ŷ_{−1} − Ŷⁿ_{−1}` only (not of the policy-dependent paths `Ŷ`, `var_i ŷ`). -/
noncomputable def tipTotal (P : Par) (e : Exo) (Ym1 : ℝ) : ℝ :=
  ∑' t, P.β ^ t * (tipU P e t + (1 - P.β * P.η) * (P.δ0 * P.xhat ^ 2 / 2)) +
    (-(P.η * Ym1) - P.η / 2 * Ym1 ^ 2 - P.sinv * P.η ^ 2 / 2 * Ym1 ^ 2 -
      P.sinv * P.η * (gS e 0 - P.η * e.Gm1) * Ym1) +
    (1 - P.β * P.η) * (P.η * P.φ * e.n 0 * (Ym1 - e.nm1) +
      (P.δ0 * P.δ ^ 2 / 2 * (Ym1 - e.nm1) ^ 2 + P.δ0 * P.δ * P.xhat * (Ym1 - e.nm1)))

/-- Woodford (2003), (2.27), p. 403: the squared quasi-differenced gap
`(x_t − δx_{t−1} − x̂*)²`. -/
noncomputable def gapSq (P : Par) (e : Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  (xS e Y t - P.δ * lagS (Ym1 - e.nm1) (xS e Y) t - P.xhat) ^ 2

/-- Woodford (2003), App. E.3, p. 698: the combined period identity behind the corrected
Proposition 6.6. -/
theorem prop66_period {P : Par} (hP : P.Std) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ) (t : ℕ) :
    Useq P e Ym1 Y V t =
      -((1 - P.β * P.η) / 2) * (P.δ0 * gapSq P e Ym1 Y t + (P.θ⁻¹ + P.ω) * V t) +
        -(1 - P.β * P.η) * (rS P e t * xS e Y t) +
          (tipU P e t + (1 - P.β * P.η) * (P.δ0 * P.xhat ^ 2 / 2)) + RUseq P e Ym1 Y V t +
        ((K1 P e Ym1 Y t + (1 - P.β * P.η) * (kS P e Ym1 Y t +
          (P.δ0 * P.δ ^ 2 / 2 * lagS (Ym1 - e.nm1) (xS e Y) t ^ 2 +
            P.δ0 * P.δ * P.xhat * lagS (Ym1 - e.nm1) (xS e Y) t))) -
        P.β * (K1 P e Ym1 Y (t + 1) + (1 - P.β * P.η) * (kS P e Ym1 Y (t + 1) +
          (P.δ0 * P.δ ^ 2 / 2 * lagS (Ym1 - e.nm1) (xS e Y) (t + 1) ^ 2 +
            P.δ0 * P.δ * P.xhat * lagS (Ym1 - e.nm1) (xS e Y) (t + 1))))) := by
  have hc := csq_period (xm1 := Ym1 - e.nm1) (xS e Y) (delta0_mul hP) (delta0_delta hP)
    (delta0_xhat hP) t
  rw [E12_period, E13_period]
  unfold E13main gapSq tipU
  rw [hc]
  ring

/-- **Woodford (2003), Proposition 6.6 and (E.9), pp. 403–404, 696–698, CORRECTED (pathwise,
genuine discounted sums; survey error 16).** For bounded paths and the standard parameter
restrictions,
`∑ βᵗ U_t = −½ ∑ βᵗ [μ_x (x_t − δx_{t−1} − x̂*)² + (1 − βη)(θ⁻¹ + ω) var_i ŷ_t]
  − (1 − βη) ∑ βᵗ r_t x_t + t.i.p. + ∑ βᵗ R_t`,
with `R_t` of weighted degree three (`RU_scaling`) and t.i.p. `tipTotal` a function of the
exogenous data and initial conditions only. Equivalently the bracket is
`(1 − βη)[δ₀(·)² + (θ⁻¹ + ω) var_i ŷ_t]`: the dispersion weight carries the factor `1 − βη`
that the printed (2.27) omits (`printed_E9_discounted_false`). The `r_t x_t` sum is zero in
expectation (`prop66_corrected_expectation`). -/
theorem prop66_corrected {P : Par} (hP : P.Std) (e : Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ)
    (hY : Bdd Y) (hV : Bdd V) (he : e.Bounded) :
    ∑' t, P.β ^ t * Useq P e Ym1 Y V t =
      -(1 / 2) * ∑' t, P.β ^ t * (P.muX * gapSq P e Ym1 Y t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * V t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (rS P e t * xS e Y t) +
        tipTotal P e Ym1 + ∑' t, P.β ^ t * RUseq P e Ym1 Y V t := by
  have h0 := hP.1
  have h1 := hP.2.1
  obtain ⟨hG, hgp, hq, hn⟩ := he
  have hx : Bdd (xS e Y) := hY.sub hn
  have hS : Bdd (gapSq P e Ym1 Y) := by
    unfold gapSq
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hW : Bdd (fun t => P.δ0 * gapSq P e Ym1 Y t + (P.θ⁻¹ + P.ω) * V t) :=
    ((Bdd.const _).mul hS).add ((Bdd.const _).mul hV)
  have hrx : Bdd (fun t => rS P e t * xS e Y t) := by
    unfold rS gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hT : Bdd (fun t => tipU P e t + (1 - P.β * P.η) * (P.δ0 * P.xhat ^ 2 / 2)) := by
    unfold tipU tipSeq E10tipAt tipN gTil gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hR : Bdd (RUseq P e Ym1 Y V) := by
    unfold RUseq E10remAt vRemAt
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hK : Bdd (fun t => K1 P e Ym1 Y t + (1 - P.β * P.η) * (kS P e Ym1 Y t +
      (P.δ0 * P.δ ^ 2 / 2 * lagS (Ym1 - e.nm1) (xS e Y) t ^ 2 +
        P.δ0 * P.δ * P.xhat * lagS (Ym1 - e.nm1) (xS e Y) t))) := by
    unfold K1 kS gS
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  rw [tsum_telescope_add h0 h1 (((((Bdd.const _).mul hW).add ((Bdd.const _).mul hrx)).add
    hT).add hR) hK (prop66_period hP e Ym1 Y V)]
  have hsplit := tsum_add3 h0 h1 1 (((Bdd.const (-((1 - P.β * P.η) / 2))).mul hW).add
    ((Bdd.const (-(1 - P.β * P.η))).mul hrx)) hT hR
  simp only [one_mul] at hsplit
  rw [hsplit]
  have hsum2 : ∑' t, P.β ^ t * (-((1 - P.β * P.η) / 2) * (P.δ0 * gapSq P e Ym1 Y t +
      (P.θ⁻¹ + P.ω) * V t) + -(1 - P.β * P.η) * (rS P e t * xS e Y t)) =
      -(1 / 2) * ∑' t, P.β ^ t * (P.muX * gapSq P e Ym1 Y t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * V t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (rS P e t * xS e Y t) := by
    have hA' := (hW.summable h0 h1).mul_left (-((1 - P.β * P.η) / 2))
    have hB' := (hrx.summable h0 h1).mul_left (-(1 - P.β * P.η))
    have hfun : (fun t => P.β ^ t * (-((1 - P.β * P.η) / 2) * (P.δ0 * gapSq P e Ym1 Y t +
        (P.θ⁻¹ + P.ω) * V t) + -(1 - P.β * P.η) * (rS P e t * xS e Y t))) =
        fun t => -((1 - P.β * P.η) / 2) * (P.β ^ t * (P.δ0 * gapSq P e Ym1 Y t +
          (P.θ⁻¹ + P.ω) * V t)) + -(1 - P.β * P.η) * (P.β ^ t * (rS P e t * xS e Y t)) := by
      funext t; ring
    have hfun2 : (fun t => P.β ^ t * (P.muX * gapSq P e Ym1 Y t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * V t)) =
        fun t => (1 - P.β * P.η) * (P.β ^ t * (P.δ0 * gapSq P e Ym1 Y t +
          (P.θ⁻¹ + P.ω) * V t)) := by
      funext t; rw [muX_eq]; ring
    rw [hfun, hA'.tsum_add hB', tsum_mul_left, tsum_mul_left, hfun2, tsum_mul_left]
    ring
  rw [hsum2]
  unfold tipTotal K1 kS
  simp only [lagS_zero]
  ring


/-- **Woodford (2003), (E.10)–(E.12): the total remainder is `O(‖Φ, ŷ, ξ̃‖³)`** (scaling
the weight-one variables by `s` and `var_i ŷ` by `s²` scales it by `s³`). -/
theorem RU_scaling (s k sinv η Φ θ ω y ym G Gm gp q V : ℝ) :
    E10remAt sinv η (s * y) (s * ym) (s * G) (s * Gm) (s * gp) -
        k * vRemAt (s * Φ) θ ω (s * y) (s * q) (s ^ 2 * V) =
      s ^ 3 * (E10remHat s sinv η y ym G Gm gp - k * vRemHat s Φ θ ω y q V) := by
  rw [E10rem_scaling, vRem_scaling]
  ring

/-! ### The printed weights of (2.27)/(E.9) are wrong (survey error 16) -/

/-- Woodford (2003), App. E.3: if `|a| ≤ K s` for all `s ∈ (0, 1]` then `a = 0`. -/
theorem eq_zero_of_abs_le_mul {a K : ℝ} (h : ∀ s, 0 < s → s ≤ 1 → |a| ≤ K * s) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.mpr ha
  have hK1 : 0 < |K| + 1 := by positivity
  set s := min 1 (|a| / (2 * (|K| + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs2 : s * (2 * (|K| + 1)) ≤ |a| := by
    have := min_le_right 1 (|a| / (2 * (|K| + 1)))
    rw [← hs, le_div_iff₀ (by positivity)] at this
    exact this
  have h1 := h s hs0 (min_le_left _ _)
  have h2 : K * s ≤ |K| * s := mul_le_mul_of_nonneg_right (le_abs_self K) hs0.le
  nlinarith [abs_nonneg K]

/-- Woodford (2003), App. E.3 (the meaning of `O(3)`): if `|c + a s + b s²| ≤ C|s|³` for all
`|s| ≤ 1`, then `c = a = b = 0`. -/
theorem poly2_zero {c a b C : ℝ}
    (h : ∀ s : ℝ, |s| ≤ 1 → |c + a * s + b * s ^ 2| ≤ C * |s| ^ 3) :
    c = 0 ∧ a = 0 ∧ b = 0 := by
  have hc : c = 0 := by
    have := h 0 (by simp)
    simpa using this
  subst hc
  have hpos : ∀ s : ℝ, 0 < s → s ≤ 1 → |a + b * s| ≤ |C| * s ^ 2 := by
    intro s hs hs1
    have h1 := h s (by rw [abs_of_pos hs]; exact hs1)
    have e : 0 + a * s + b * s ^ 2 = s * (a + b * s) := by ring
    rw [e, abs_mul, abs_of_pos hs] at h1
    have h2 : |a + b * s| ≤ C * s ^ 2 := by
      have h3 : s * |a + b * s| ≤ s * (C * s ^ 2) := by linarith
      exact le_of_mul_le_mul_left h3 hs
    have : C * s ^ 2 ≤ |C| * s ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith
  have ha : a = 0 := by
    refine eq_zero_of_abs_le_mul (K := |C| + |b|) (fun s hs hs1 => ?_)
    have h1 := hpos s hs hs1
    have h2 : |a| ≤ |a + b * s| + |b * s| := by
      have := abs_sub (a + b * s) (b * s)
      simpa using this
    rw [abs_mul, abs_of_pos hs] at h2
    have h3 : |C| * s ^ 2 ≤ |C| * s := by
      have : s ^ 2 ≤ s := by nlinarith
      exact mul_le_mul_of_nonneg_left this (abs_nonneg C)
    linarith
  subst ha
  refine ⟨rfl, rfl, eq_zero_of_abs_le_mul (K := |C|) (fun s hs hs1 => ?_)⟩
  have h1 := hpos s hs hs1
  rw [zero_add, abs_mul, abs_of_pos hs] at h1
  have h2 : |b| * s ≤ (|C| * s) * s := by nlinarith
  exact le_of_mul_le_mul_right h2 hs

/-- Woodford (2003), App. E.3: `|d s³ + e s⁴| ≤ (|d| + |e|)|s|³` for `|s| ≤ 1`. -/
theorem abs_cubic_le {d e s : ℝ} (hs : |s| ≤ 1) :
    |d * s ^ 3 + e * s ^ 4| ≤ (|d| + |e|) * |s| ^ 3 := by
  have h4 : |s| ^ 4 ≤ |s| ^ 3 := by
    have : |s| ^ 4 = |s| ^ 3 * |s| := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hs
  calc |d * s ^ 3 + e * s ^ 4| ≤ |d * s ^ 3| + |e * s ^ 4| := abs_add_le _ _
    _ = |d| * |s| ^ 3 + |e| * |s| ^ 4 := by rw [abs_mul, abs_mul, abs_pow, abs_pow]
    _ ≤ |d| * |s| ^ 3 + |e| * |s| ^ 3 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h4 (abs_nonneg e))
    _ = (|d| + |e|) * |s| ^ 3 := by ring

/-- Woodford (2003), App. E.3: zero exogenous data (all shocks and the natural rate zero), so
that every t.i.p. is a constant. -/
def exo0 : Exo := ⟨fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, 0⟩

/-- Woodford (2003), (2.27): with `Φ_y = 0` the target `x̂*` is zero. -/
theorem xhat_of_Phi_zero {P : Par} (hΦ : P.Φ = 0) : P.xhat = 0 := by
  unfold Par.xhat; rw [hΦ]; simp

/-- **Woodford (2003), (2.27)/(E.9), pp. 403, 696: the approximation does NOT hold period by
period (survey error 16).** Take `Φ_y = 0`, zero shocks and initial conditions (so t.i.p. is a
constant `c`), `Ŷ_t = s`, `var_i ŷ_t = 0`. If `βη ≠ 0` there is no constant `c` and no `C` with
`|U_t − (−½[μ_x(x_t − δx_{t−1} − x̂*)² + (θ⁻¹ + ω)var_i ŷ_t] + c)| ≤ C|s|³` for `|s| ≤ 1`: the
period utility has the first-order term `βη Ŷ_t`, which only disappears in the discounted sum
(it telescopes against `−ηŶ_{t−1}`). -/
theorem printed_E9_per_period_false {P : Par} (hΦ : P.Φ = 0) (hβη : P.β * P.η ≠ 0) :
    ¬ ∃ c C : ℝ, ∀ s : ℝ, |s| ≤ 1 →
      |Useq P exo0 0 (fun _ => s) (fun _ => 0) 0 -
        (-(1 / 2) * (P.muX * gapSq P exo0 0 (fun _ => s) 0 + (P.θ⁻¹ + P.ω) * 0) + c)| ≤
        C * |s| ^ 3 := by
  rintro ⟨c, C, h⟩
  have hx := xhat_of_Phi_zero hΦ
  set b := 1 / 2 - P.sinv / 2 - (1 - P.β * P.η) * (1 + P.ω) / 2 + P.muX / 2 with hb
  have key : ∀ s : ℝ, Useq P exo0 0 (fun _ => s) (fun _ => 0) 0 -
      (-(1 / 2) * (P.muX * gapSq P exo0 0 (fun _ => s) 0 + (P.θ⁻¹ + P.ω) * 0) + c) =
      (-c + P.β * P.η * s + b * s ^ 2) + (-(P.sinv / 2) * s ^ 3 + -(P.sinv / 8) * s ^ 4) := by
    intro s
    simp only [Useq, gapSq, xS, exo0, uTaylor, cDevAt, ePoly, vTaylor, m1Of, m2Of, hΦ, hx,
      lagS_zero, hb]
    ring
  have h2 : ∀ s : ℝ, |s| ≤ 1 → |-c + P.β * P.η * s + b * s ^ 2| ≤
      (C + (|-(P.sinv / 2)| + |-(P.sinv / 8)|)) * |s| ^ 3 := by
    intro s hs
    have h1 := h s hs
    rw [key] at h1
    have h3 := abs_cubic_le (d := -(P.sinv / 2)) (e := -(P.sinv / 8)) hs
    have h4 := abs_sub (-c + P.β * P.η * s + b * s ^ 2 +
      (-(P.sinv / 2) * s ^ 3 + -(P.sinv / 8) * s ^ 4)) (-(P.sinv / 2) * s ^ 3 +
        -(P.sinv / 8) * s ^ 4)
    simp only [add_sub_cancel_right] at h4
    nlinarith
  exact hβη (poly2_zero h2).2.1

/-- Woodford (2003), App. E.3: the dispersion path `var_i ŷ_0 = s²`, zero afterwards. -/
noncomputable def Vone (s : ℝ) (t : ℕ) : ℝ := if t = 0 then s ^ 2 else 0

/-- **Woodford (2003), (2.27)/(E.9), pp. 403, 696–698: the printed relative weights are wrong
even in discounted-sum form (survey error 16, confirmed).** Take `Φ_y = 0`, zero shocks and
initial conditions, `Ŷ ≡ 0`, and dispersion `s²` at date 0 only. If `βη(θ⁻¹ + ω) ≠ 0`, there is
no constant `c` (t.i.p.) and no `C` with
`|∑ βᵗU_t − (−½∑ βᵗ[μ_x(x_t − δx_{t−1} − x̂*)² + (θ⁻¹ + ω)var_i ŷ_t] + c)| ≤ C|s|³`: the true
dispersion weight is `(1 − βη)(θ⁻¹ + ω)` (`prop66_corrected`). -/
theorem printed_E9_discounted_false {P : Par} (hΦ : P.Φ = 0)
    (hθω : P.β * P.η * (P.θ⁻¹ + P.ω) ≠ 0) :
    ¬ ∃ c C : ℝ, ∀ s : ℝ, |s| ≤ 1 →
      |∑' t, P.β ^ t * Useq P exo0 0 (fun _ => 0) (Vone s) t -
        (-(1 / 2) * ∑' t, P.β ^ t * (P.muX * gapSq P exo0 0 (fun _ => 0) t +
          (P.θ⁻¹ + P.ω) * Vone s t) + c)| ≤ C * |s| ^ 3 := by
  rintro ⟨c, C, h⟩
  have hx := xhat_of_Phi_zero hΦ
  have hU : ∀ s : ℝ, ∑' t, P.β ^ t * Useq P exo0 0 (fun _ => 0) (Vone s) t =
      -(1 - P.β * P.η) * ((P.θ⁻¹ + P.ω) / 2 * s ^ 2 +
        (1 + P.ω) / 2 * ((1 - P.θ⁻¹) / 2) ^ 2 * s ^ 4) := by
    intro s
    rw [tsum_eq_single 0 (fun t ht => by
      simp [Useq, Vone, ht, exo0, uTaylor, cDevAt, ePoly, vTaylor, m1Of, m2Of])]
    simp only [Useq, Vone, exo0, uTaylor, cDevAt, ePoly, vTaylor, m1Of, m2Of, hΦ, lagS_zero,
      ↓reduceIte, pow_zero, one_mul]
    ring
  have hR : ∀ s : ℝ, ∑' t, P.β ^ t * (P.muX * gapSq P exo0 0 (fun _ => 0) t +
      (P.θ⁻¹ + P.ω) * Vone s t) = (P.θ⁻¹ + P.ω) * s ^ 2 := by
    intro s
    rw [tsum_eq_single 0 (fun t ht => by
      cases t with
      | zero => exact absurd rfl ht
      | succ t => simp [gapSq, Vone, xS, exo0, hx])]
    simp [gapSq, Vone, xS, exo0, hx]
  set b := P.β * P.η * (P.θ⁻¹ + P.ω) / 2 with hb
  set e := -(1 - P.β * P.η) * ((1 + P.ω) / 2 * ((1 - P.θ⁻¹) / 2) ^ 2) with he
  have h2 : ∀ s : ℝ, |s| ≤ 1 → |-c + 0 * s + b * s ^ 2| ≤ (C + (|0| + |e|)) * |s| ^ 3 := by
    intro s hs
    have h1 := h s hs
    rw [hU, hR] at h1
    have key : -(1 - P.β * P.η) * ((P.θ⁻¹ + P.ω) / 2 * s ^ 2 +
        (1 + P.ω) / 2 * ((1 - P.θ⁻¹) / 2) ^ 2 * s ^ 4) -
        (-(1 / 2) * ((P.θ⁻¹ + P.ω) * s ^ 2) + c) =
        (-c + 0 * s + b * s ^ 2) + (0 * s ^ 3 + e * s ^ 4) := by
      rw [hb, he]; ring
    rw [key] at h1
    have h3 := abs_cubic_le (d := 0) (e := e) hs
    have h4 := abs_sub (-c + 0 * s + b * s ^ 2 + (0 * s ^ 3 + e * s ^ 4))
      (0 * s ^ 3 + e * s ^ 4)
    simp only [add_sub_cancel_right] at h4
    nlinarith
  have hb0 := (poly2_zero h2).2.2
  apply hθω
  linarith

/-! ### Calvo pricing: the loss function (2.28)–(2.29) with `λ = κ/θ` -/

namespace Par

/-- Woodford (2003), (2.28), p. 405, with Ch. 5 (1.29): `κ = ξ_p ηφ/δ` (division-free form
`habKappa`). -/
noncomputable def kappa (P : Par) (α : ℝ) : ℝ := habKappa (calvoXi α P.β P.ω P.θ) P.β P.ω P.φ P.η

/-- Woodford (2003), (2.28), p. 404: the relative weight implied by the CORRECTED Proposition 6.6,
`λ = δ₀/[θ(1 + ωθ)α/((1 − α)(1 − αβ))]` (equal to `κ/θ`, `lam_eq_kappa_div_theta`). -/
noncomputable def lam (P : Par) (α : ℝ) : ℝ :=
  P.δ0 / (P.θ * (1 + P.ω * P.θ) * calvoK α P.β)

/-- Woodford (2003), (2.21), p. 400: the normalising factor
`Λ = ½(1 − βη)θ(1 + ωθ)α/[(1 − α)(1 − αβ)]` (the `Λ` of (2.21), in units of `Ȳ u_c`). -/
noncomputable def Lam (P : Par) (α : ℝ) : ℝ :=
  (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ) * calvoK α P.β)

/-- Woodford (2003), (2.27)–(2.28), pp. 403–405: the relative weight implied by the PRINTED
weights of (2.27), `μ_x/[θ(1 + ωθ)α/((1 − α)(1 − αβ))]`. -/
noncomputable def lamPrinted (P : Par) (α : ℝ) : ℝ :=
  P.muX / (P.θ * (1 + P.ω * P.θ) * calvoK α P.β)

end Par

/-- Woodford (2003), (1.29) of Ch. 5: `κ = ξ_p δ₀`. -/
theorem kappa_eq {P : Par} (hP : P.Std) (α : ℝ) : P.kappa α = calvoXi α P.β P.ω P.θ * P.δ0 := by
  obtain ⟨hβ0, -, -, -, hφ, hω⟩ := hP
  have hk := habKappa_mul (ξp := calvoXi α P.β P.ω P.θ) (η := P.η) hβ0 hω hφ
  have hpos : 0 < 1 + P.β * P.δ ^ 2 := by positivity
  unfold Par.kappa Par.δ0
  rw [A_eq_habB, eq_comm, mul_div_assoc', div_eq_iff hpos.ne']
  unfold Par.δ habB
  linear_combination -hk

/-- **Woodford (2003), (2.28), pp. 404–405: `λ = κ/θ`** with `κ` from Ch. 5 (1.29) — valid for
the CORRECTED weights of Proposition 6.6. -/
theorem lam_eq_kappa_div_theta {P : Par} (hP : P.Std) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < P.θ) : P.lam α = P.kappa α / P.θ := by
  have hβ0 := hP.1
  have hβ1 := hP.2.1
  have hω := hP.2.2.2.2.2
  rw [kappa_eq hP]
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * P.β := by nlinarith
  have h3 : 0 < 1 + P.ω * P.θ := by positivity
  unfold Par.lam calvoK calvoXi
  field_simp

/-- **Woodford (2003), (2.27)–(2.28) (survey error 16):** the printed weights give
`λ = (1 − βη)κ/θ`. -/
theorem lamPrinted_eq {P : Par} (hP : P.Std) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < P.θ) : P.lamPrinted α = (1 - P.β * P.η) * (P.kappa α / P.θ) := by
  rw [← lam_eq_kappa_div_theta hP hα0 hα1 hθ]
  unfold Par.lamPrinted Par.lam
  rw [muX_eq]
  ring

/-- Woodford (2003), (1.29) of Ch. 5: `κ > 0` (`0 < α < 1`, `θ > 0`). -/
theorem kappa_pos {P : Par} (hP : P.Std) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) :
    0 < P.kappa α := by
  obtain ⟨hβ0, hβ1, -, -, hφ, hω⟩ := hP
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * P.β := by nlinarith
  exact habKappa_pos (by unfold calvoXi; positivity) hβ0 hω hφ

/-- **Woodford (2003), (2.28) (survey error 16): the printed weights reproduce `λ = κ/θ` iff
`βη = 0`**, i.e. only without habit persistence. -/
theorem lamPrinted_eq_lam_iff {P : Par} (hP : P.Std) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < P.θ) : P.lamPrinted α = P.lam α ↔ P.β * P.η = 0 := by
  rw [lamPrinted_eq hP hα0 hα1 hθ, lam_eq_kappa_div_theta hP hα0 hα1 hθ]
  have hk : 0 < P.kappa α / P.θ := div_pos (kappa_pos hP hα0 hα1 hθ) hθ
  constructor
  · intro h
    have : (P.β * P.η) * (P.kappa α / P.θ) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hk.ne'
  · intro h; rw [h]; ring

/-- **Woodford (2003), (2.28): a concrete counterexample to the printed weights** (`β = 0.99`,
`η = 1/2`, `φ = 1`, `ω = 1`, `θ = 6`, `Φ = 0`, `α = 2/3`): `(1 − βη)κ/θ ≠ κ/θ`. -/
theorem printed_lambda_false :
    ∃ (P : Par) (α : ℝ), P.Std ∧ 0 < α ∧ α < 1 ∧ 0 < P.θ ∧ P.lamPrinted α ≠ P.lam α := by
  refine ⟨⟨99 / 100, 1 / 2, 1, 1, 6, 0⟩, 2 / 3, ⟨by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [Ne, lamPrinted_eq_lam_iff ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Woodford (2003), (2.21), p. 400: `Λ > 0`. -/
theorem Lam_pos {P : Par} (hP : P.Std) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) :
    0 < P.Lam α := by
  have hβη := beta_eta_lt hP
  obtain ⟨hβ0, hβ1, -, -, -, hω⟩ := hP
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * P.β := by nlinarith
  have h3 : 0 < 1 - P.β * P.η := by linarith
  unfold Par.Lam calvoK; positivity

/-- **Woodford (2003), (2.21)–(2.22) and (2.28), pp. 400, 404–405 (the loss form).** With the
dispersion law (2.20) for `p` and `var_i ŷ_t = θ²Δ_t` ((2.12)), the corrected welfare bracket is
`∑ βᵗ[μ_x sq_t + (1 − βη)(θ⁻¹ + ω)θ²Δ_t] = 2Λ ∑ βᵗ[p_t² + λ sq_t] + t.i.p.` with `λ = κ/θ`. -/
theorem loss_form {P : Par} (hP : P.Std) {α Δm1 : ℝ} {Δ p sq : ℕ → ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hθ : 0 < P.θ) (hp : Bdd p) (hsq : Bdd sq)
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2) :
    ∑' t, P.β ^ t * (P.muX * sq t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * (P.θ ^ 2 * Δ t)) =
      2 * P.Lam α * ∑' t, P.β ^ t * (p t ^ 2 + P.lam α * sq t) +
        (1 - P.β * P.η) * (P.θ * (1 + P.ω * P.θ)) * (α * Δm1 / (1 - α * P.β)) := by
  have h0 := hP.1
  have h1 := hP.2.1
  have hω := hP.2.2.2.2.2
  have hΔ := disp_bdd hα0.le hα1 hp hrec
  have hD := disp_discounted h0 h1 hα0.le hα1 hp hrec
  have hs1 := hsq.summable h0 h1
  have hs2 := hΔ.summable h0 h1
  have hs3 := (hp.pow 2).summable h0 h1
  have hL : ∑' t, P.β ^ t * (P.muX * sq t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * (P.θ ^ 2 * Δ t)) =
      P.muX * ∑' t, P.β ^ t * sq t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * P.θ ^ 2 * ∑' t, P.β ^ t * Δ t := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hs1.mul_left _).tsum_add (hs2.mul_left _)]
    congr 1; funext t; ring
  have hR : ∑' t, P.β ^ t * (p t ^ 2 + P.lam α * sq t) =
      ∑' t, P.β ^ t * p t ^ 2 + P.lam α * ∑' t, P.β ^ t * sq t := by
    rw [← tsum_mul_left, ← hs3.tsum_add (hs1.mul_left _)]
    congr 1; funext t; ring
  rw [hL, hR, hD, muX_eq]
  have h1α : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * P.β := by nlinarith
  have h3 : 0 < 1 + P.ω * P.θ := by positivity
  have h1' := h1α.ne'
  have h2' := h2.ne'
  have h3' := h3.ne'
  have hθ' := hθ.ne'
  have h4' : 1 - P.β * α ≠ 0 := by rw [mul_comm]; exact h2'
  generalize (∑' t, P.β ^ t * sq t) = A1
  generalize (∑' t, P.β ^ t * p t ^ 2) = A2
  unfold Par.Lam Par.lam calvoK
  field_simp
  ring

/-- **Woodford (2003), (2.21) with (2.28), pp. 400, 404–405: the welfare-theoretic loss under
habit persistence and Calvo pricing (pathwise, genuine discounted sums).** With the CORRECTED
Proposition 6.6, the dispersion law (2.20) (`p = π`) and `var_i ŷ_t = θ²Δ_t`,
`∑ βᵗU_t = −Λ ∑ βᵗ L_t − (1 − βη)∑ βᵗ r_t x_t + t.i.p. + ∑ βᵗR_t`,
`L_t = π_t² + λ(x_t − δx_{t−1} − x̂*)²`, `λ = κ/θ` (`lam_eq_kappa_div_theta`). With
`p_t = π_t − γπ_{t−1}` and the indexation law (2.24) this is (2.29). -/
theorem welfare228 {P : Par} (hP : P.Std) {α Δm1 : ℝ} {Δ p : ℕ → ℝ} (e : Exo) (Ym1 : ℝ)
    (Y V : ℕ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) (hY : Bdd Y) (hp : Bdd p)
    (he : e.Bounded) (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2)
    (hV : ∀ t, V t = P.θ ^ 2 * Δ t) :
    ∑' t, P.β ^ t * Useq P e Ym1 Y V t =
      -P.Lam α * ∑' t, P.β ^ t * (p t ^ 2 + P.lam α * gapSq P e Ym1 Y t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (rS P e t * xS e Y t) +
        (tipTotal P e Ym1 -
          (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ)) * (α * Δm1 / (1 - α * P.β))) +
        ∑' t, P.β ^ t * RUseq P e Ym1 Y V t := by
  have hVfun : V = fun t => P.θ ^ 2 * Δ t := funext hV
  have hΔ := disp_bdd hα0.le hα1 hp hrec
  have hVb : Bdd V := by rw [hVfun]; exact (Bdd.const _).mul hΔ
  have hS : Bdd (gapSq P e Ym1 Y) := by
    obtain ⟨-, -, -, hn⟩ := he
    have hx : Bdd (xS e Y) := hY.sub hn
    unfold gapSq
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  rw [prop66_corrected hP e Ym1 Y V hY hVb he]
  have hlf := loss_form hP (Δm1 := Δm1) hα0 hα1 hθ hp hS hrec
  have hsub : ∑' t, P.β ^ t * (P.muX * gapSq P e Ym1 Y t +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * V t) =
      ∑' t, P.β ^ t * (P.muX * gapSq P e Ym1 Y t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * (P.θ ^ 2 * Δ t)) := by
    rw [hVfun]
  rw [hsub, hlf]
  ring

/-- **Woodford (2003), (2.29), p. 405 (indexation).** The loss under indexation to the lagged
price index: (2.21) with `L_t = (π_t − γπ_{t−1})² + λ(x_t − δx_{t−1} − x̂*)²` and the same
`λ = κ/θ`, from the indexation dispersion law (2.24). -/
theorem welfare229 {P : Par} (hP : P.Std) {α Δm1 γ πm1 : ℝ} {Δ π : ℕ → ℝ} (e : Exo) (Ym1 : ℝ)
    (Y V : ℕ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) (hY : Bdd Y) (hπ : Bdd π)
    (he : e.Bounded)
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * (π t - γ * lagS πm1 π t) ^ 2)
    (hV : ∀ t, V t = P.θ ^ 2 * Δ t) :
    ∑' t, P.β ^ t * Useq P e Ym1 Y V t =
      -P.Lam α * ∑' t, P.β ^ t * ((π t - γ * lagS πm1 π t) ^ 2 +
        P.lam α * gapSq P e Ym1 Y t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (rS P e t * xS e Y t) +
        (tipTotal P e Ym1 -
          (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ)) * (α * Δm1 / (1 - α * P.β))) +
        ∑' t, P.β ^ t * RUseq P e Ym1 Y V t :=
  welfare228 hP (p := fun t => π t - γ * lagS πm1 π t) e Ym1 Y V hα0 hα1 hθ hY
    (hπ.sub ((Bdd.const γ).mul (hπ.lagS πm1))) he hrec hV

/-! ### Special cases of Proposition 6.6 -/

/-- **Woodford (2003), p. 404: the `δ < 1` rewrite.** If `δ ≠ 1`,
`x_t − δx_{t−1} − x̂* = (x_t − x*) − δ(x_{t−1} − x*)` with `x* = x̂*/(1 − δ)`. -/
theorem gap_rewrite {δ xh x xm : ℝ} (hδ : δ ≠ 1) :
    x - δ * xm - xh = (x - xh / (1 - δ)) - δ * (xm - xh / (1 - δ)) := by
  have : 1 - δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hδ)
  field_simp
  ring

/-- **Woodford (2003), p. 404: the case `δ = 1`** (`ω = 0`, `η = 1`): then `δ = 1` and
`x̂* = Φ_y/((1 − β)φ)`, which is positive when `Φ_y > 0` ("`x̂*` need not equal zero"). -/
theorem delta_one_case {P : Par} (hP : P.Std) (hω : P.ω = 0) (hη : P.η = 1) :
    P.δ = 1 ∧ P.xhat = P.Φ / ((1 - P.β) * P.φ) ∧ (0 < P.Φ → 0 < P.xhat) := by
  obtain ⟨hβ0, hβ1, -, -, hφ, -⟩ := hP
  have hd : P.δ = 1 := by
    unfold Par.δ
    rw [hω, hη, habDelta_eq_of_omega_zero hφ (by rw [hη] at *; nlinarith)]
  have h1 : 0 < 1 - P.β := by linarith
  have hx : P.xhat = P.Φ / ((1 - P.β) * P.φ) := by
    unfold Par.xhat Par.A
    rw [hd, hω, hη]
    field_simp
    ring
  refine ⟨hd, hx, fun hΦ => ?_⟩
  rw [hx]; positivity

/-- **Woodford (2003), pp. 403–404: `η = 0` recovers Proposition 6.1.** Then `δ = 0`,
`μ_x = δ₀ = ω + φ` (`φ = σ⁻¹`) and `x̂* = Φ_y/(ω + σ⁻¹) = x*` of (2.17). -/
theorem eta_zero_reduction (P : Par) (hη : P.η = 0) :
    P.δ = 0 ∧ P.δ0 = P.ω + P.φ ∧ P.muX = P.ω + P.φ ∧ P.xhat = P.Φ / (P.ω + P.φ) := by
  have hd : P.δ = 0 := by unfold Par.δ habDelta; rw [hη]; simp
  refine ⟨hd, ?_, ?_, ?_⟩
  · unfold Par.δ0 Par.A; rw [hd, hη]; ring
  · unfold Par.muX Par.A; rw [hd, hη]; ring
  · unfold Par.xhat Par.A; rw [hd, hη]; ring


/-! ### Processes under an arbitrary `ExpectationSystem` -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), Ch. 5 §1.2, p. 333 (restated): the quasi-difference
`x̃_t ≡ (x_t − ηx_{t−1}) − βη E_t(x_{t+1} − ηx_t) = E_t[(1 − ηL)(1 − βηL⁻¹)x_t]`. -/
noncomputable def xTildeP (β η : ℝ) (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (x t - η • lagP xm1 x t) - (β * η) • 𝔼.E t (x (t + 1) - η • x t)

/-- Woodford (2003), (1.26) ⟺ (1.27) of Ch. 5, p. 335 (restated from the Chapter 5 project):
for adapted `x`, if `κδ = ξ_p ηφ` and `κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))` then
`ξ_p[ωx_t + φx̃_t(η)] = κ x̃_t(δ)`. -/
theorem as_identity {ξp ω vphi β η κ δ : ℝ} (h1 : κ * δ = ξp * η * vphi)
    (h2 : κ * (1 + β * δ ^ 2) = ξp * (ω + vphi * (1 + β * η ^ 2))) {xm1 : Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    ξp • (ω • x t + vphi • xTildeP 𝔼 β η xm1 x t) = κ • xTildeP 𝔼 β δ xm1 x t := by
  unfold xTildeP
  simp only [map_sub, map_smul, hx t]
  funext ω'
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (lagP xm1 x t ω' + β * 𝔼.E t (x (t + 1)) ω') * h1 - x t ω' * h2

/-- Woodford (2003), (2.31), p. 405, in marginal-cost form (Ch. 5 (1.26) with the indexation of
Ch. 3 §3.2; a hypothesis-level restatement):
`π_t − γπ_{t−1} = ξ_p[ωx_t + φx̃_t] + βE_t(π_{t+1} − γπ_t)`. -/
def ASmcIdx (ξp ω vphi β η γ : ℝ) (πm1 xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t - γ • lagP πm1 π t =
    ξp • (ω • x t + vphi • xTildeP 𝔼 β η xm1 x t) + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), eq. (2.31), p. 405:
`π_t − γπ_{t−1} = κ[(x_t − δx_{t−1}) − βδE_t(x_{t+1} − δx_t)] + βE_t(π_{t+1} − γπ_t)`. -/
def AS231 (κ δ β γ : ℝ) (πm1 xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t - γ • lagP πm1 π t = κ • xTildeP 𝔼 β δ xm1 x t + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), eq. (2.30), p. 405:
`π_t = κ[(x_t − δx_{t−1}) − βδE_t(x_{t+1} − δx_t)] + βE_tπ_{t+1}`. -/
def AS230 (κ δ β : ℝ) (xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • xTildeP 𝔼 β δ xm1 x t + β • 𝔼.E t (π (t + 1))

/-- **Woodford (2003), (2.31), p. 405.** With `κ`, `δ` from Ch. 5 (1.28)–(1.29) (the same
coefficients as in (2.28)), the marginal-cost form with indexation is equivalent to (2.31), for
adapted `x` (any `η ≥ 0`). -/
theorem AS231_iff {ξp ω vphi β η γ : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    {πm1 xm1 : Ω → ℝ} {x π : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    ASmcIdx 𝔼 ξp ω vphi β η γ πm1 xm1 x π ↔
      AS231 𝔼 (habKappa ξp β ω vphi η) (habDelta β ω vphi η) β γ πm1 xm1 x π := by
  unfold ASmcIdx AS231
  refine forall_congr' fun t => ?_
  rw [as_identity 𝔼 (habKappa_mul_delta hβ hω hφ) (habKappa_mul hβ hω hφ) hx t]

/-- **Woodford (2003), (2.30), p. 405:** (2.30) is (2.31) with `γ = 0`; hence (2.30) is
equivalent to Ch. 5 (1.26) (`AS231_iff` at `γ = 0`). -/
theorem AS230_iff (κ δ β : ℝ) (πm1 xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) :
    AS230 𝔼 κ δ β xm1 x π ↔ AS231 𝔼 κ δ β 0 πm1 xm1 x π := by
  unfold AS230 AS231
  simp only [zero_smul, sub_zero]

/-! ### The flexible-price relation (p. 697, "one can also show") -/

/-- Woodford (2003), p. 697: the exogenous data as processes. -/
structure ExoP (Ω : Type*) where
  /-- `Ĝ_t`. -/
  G : ℕ → Ω → ℝ
  /-- `Ĝ_{−1}`. -/
  Gm1 : Ω → ℝ
  /-- `gᵖ_t`. -/
  gp : ℕ → Ω → ℝ
  /-- `q_t`. -/
  q : ℕ → Ω → ℝ
  /-- `Ŷⁿ_t`. -/
  n : ℕ → Ω → ℝ
  /-- `Ŷⁿ_{−1}`. -/
  nm1 : Ω → ℝ

/-- Woodford (2003), p. 697: the realised exogenous path in state `w`. -/
def ExoP.at (E : ExoP Ω) (w : Ω) : Exo :=
  ⟨fun t => E.G t w, E.Gm1 w, fun t => E.gp t w, fun t => E.q t w, fun t => E.n t w, E.nm1 w⟩

/-- Woodford (2003), (E.11), p. 697: `g̃_t ≡ (g_t − ηĜ_{t−1}) − βηE_t(g_{t+1} − ηĜ_t)` (the
book's form, with the expectation). -/
noncomputable def gTilE (β η : ℝ) (E : ExoP Ω) (t : ℕ) : Ω → ℝ :=
  (E.G t + E.gp t - η • lagP E.Gm1 E.G t) -
    (β * η) • 𝔼.E t ((E.G (t + 1) + E.gp (t + 1)) - η • E.G t)

/-- **Woodford (2003), p. 697: the flexible-price relation**
`E_t{[ω + φ(1 − ηL)(1 − βηL⁻¹)]Ŷⁿ_t} = φg̃_t + ωq_t`, written `ωŶⁿ_t + φx̃_t(Ŷⁿ) = φg̃_t + ωq_t`
(**`+ωq_t`**: the book prints `−ωq_t`, see `flexE_eta_zero`). -/
def FlexE (P : Par) (E : ExoP Ω) : Prop :=
  ∀ t, P.ω • E.n t + P.φ • xTildeP 𝔼 P.β P.η E.nm1 E.n t =
    P.φ • gTilE 𝔼 P.β P.η E t + P.ω • E.q t

/-- Woodford (2003), §A.3, p. 634 (restated from the Chapter 5 project, `hasDerivAt_E`): on a
finite state space `E_t` commutes with differentiation. -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {g : Ω → ℝ} {x : ℝ}
    (hf : ∀ ω, HasDerivAt (fun ε => f ε ω) (g ω) x) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t g ω) x := by
  have := Fintype.ofFinite Ω
  have hF : HasDerivAt f g x := hasDerivAt_pi.mpr hf
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt x hF
  have := hasDerivAt_pi.mp hL ω
  simpa using this

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Woodford (2003), p. 333 (restated from the Chapter 5 project, `lamOf_hasDerivAt`): the
derivative of `ε ↦ f(a + εA, ξ̄ + εv)` at `0` is `A·L(1, 0) + L(0, v)`. -/
theorem hcurve {f : ℝ → X → ℝ} {L : ℝ × X →L[ℝ] ℝ} {a : ℝ} {ξbar : X}
    (hU : HasFDerivAt (fun p : ℝ × X => f p.1 p.2) L (a, ξbar)) (A : ℝ) (v : X) :
    HasDerivAt (fun ε : ℝ => f (a + ε * A) (ξbar + ε • v)) (A * L (1, 0) + L (0, v)) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => a + ε * A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const A).const_add a
  have h2 : HasDerivAt (fun ε : ℝ => ξbar + ε • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξbar
  have h := hU.comp_hasDerivAt_of_eq (0 : ℝ) (h1.prodMk h2) (by simp)
  have hL : L (A, v) = A * L (1, 0) + L (0, v) := by
    have : ((A, v) : ℝ × X) = A • ((1 : ℝ), (0 : X)) + ((0 : ℝ), v) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [← hL]
  exact h

/-- Woodford (2003), (2.26), p. 403: habit-adjusted expenditure
`(Y_t − G_t) − η(Y_{t−1} − G_{t−1})` along the flexible-price family `Y_t = Ȳ(1 + εŶⁿ_t)`,
`G_t = Ḡ + εȲĜ_t`. -/
def habArgF (η Ybar Gbar ε : ℝ) (E : ExoP Ω) (t : ℕ) (w : Ω) : ℝ :=
  ((Ybar + ε * Ybar * E.n t w) - (Gbar + ε * Ybar * E.G t w)) -
    η * ((Ybar + ε * Ybar * lagP E.nm1 E.n t w) - (Gbar + ε * Ybar * lagP E.Gm1 E.G t w))

/-- Woodford (2003), p. 403: `habArgF = (1 − η)(Ȳ − Ḡ) + ε Ȳ c_t`,
`c_t = (Ŷⁿ_t − Ĝ_t) − η(Ŷⁿ_{t−1} − Ĝ_{t−1})`. -/
theorem habArgF_eq (η Ybar Gbar ε : ℝ) (E : ExoP Ω) (t : ℕ) (w : Ω) :
    habArgF η Ybar Gbar ε E t w = (1 - η) * (Ybar - Gbar) +
      ε * (Ybar * ((E.n t w - E.G t w) - η * (lagP E.nm1 E.n t w - lagP E.Gm1 E.G t w))) := by
  unfold habArgF; ring

/-- Woodford (2003), Ch. 5 eq. (1.23), p. 333 (restated): the marginal utility of income
`λ_t = u_c(c_t; ξ_t) − βηE_t u_c(c_{t+1}; ξ_{t+1})` along the family (taste shocks
`ξ̄ + εξ̂_t`). -/
noncomputable def lamF (β η Ybar Gbar ε : ℝ) (uc : ℝ → X → ℝ) (ξbar : X) (ξh : ℕ → Ω → X)
    (E : ExoP Ω) (t : ℕ) : Ω → ℝ :=
  (fun w => uc (habArgF η Ybar Gbar ε E t w) (ξbar + ε • ξh t w)) -
    (β * η) • 𝔼.E t (fun w => uc (habArgF η Ybar Gbar ε E (t + 1) w) (ξbar + ε • ξh (t + 1) w))

/-- Woodford (2003), p. 697 (the flexible-price equilibrium with habits): every supplier
produces `Yⁿ_t` and the marginal disutility of supply equals `(1 − Φ)` times the marginal
utility of income, `v_y(Yⁿ_t; ξ_t) = (1 − Φ)λ_t`, along the whole family. -/
def FlexNL (β η Φ Ybar Gbar : ℝ) (uc vy : ℝ → X → ℝ) (ξbar : X) (ξh : ℕ → Ω → X)
    (E : ExoP Ω) : Prop :=
  ∀ (ε : ℝ) t, (fun w => vy (Ybar + ε * Ybar * E.n t w) (ξbar + ε • ξh t w)) =
    (1 - Φ) • lamF 𝔼 β η Ybar Gbar ε uc ξbar ξh E t


/-- **Woodford (2003), p. 697: the flexible-price relation with habit persistence ("one can also
show") — PROVED as an exact derivative of the nonlinear flexible-price condition.** Along a
family of flexible-price allocations `Yⁿ_t = Ȳ(1 + εŶⁿ_t)`, `G_t = Ḡ + εȲĜ_t`, taste shocks
`ξ̄ + εξ̂_t`, satisfying `v_y(Yⁿ_t; ξ_t) = (1 − Φ)λ_t` for every `ε` (`FlexNL`), with
`σ⁻¹ ≡ −Ȳu_cc/u_c`, `φ ≡ σ⁻¹/(1 − βη)`, `ω ≡ Ȳv_yy/v_y`, `gᵖ ≡ −u_cξ ξ̂/(Ȳu_cc)` and
`q ≡ −v_yξ ξ̂/(Ȳv_yy)`, the first-order terms satisfy
`ωŶⁿ_t + φ[(Ŷⁿ_t − ηŶⁿ_{t−1}) − βηE_t(Ŷⁿ_{t+1} − ηŶⁿ_t)] = φg̃_t + ωq_t`, i.e.
`E_t{[ω + φ(1 − ηL)(1 − βηL⁻¹)]Ŷⁿ_t} = φg̃_t + ωq_t`. Finite state space. The steady-state
relation `v_y = (1 − βη)(1 − Φ)u_c` is derived (date-`0` value of the family), not assumed. -/
theorem flex_loglinear [Finite Ω] {β η Φ Ybar Gbar : ℝ} (θ : ℝ) {uc vy : ℝ → X → ℝ}
    {ξbar : X} {Lu Lv : ℝ × X →L[ℝ] ℝ}
    (hU : HasFDerivAt (fun p : ℝ × X => uc p.1 p.2) Lu ((1 - η) * (Ybar - Gbar), ξbar))
    (hV : HasFDerivAt (fun p : ℝ × X => vy p.1 p.2) Lv (Ybar, ξbar))
    (hY : Ybar ≠ 0) (hLu : Lu (1, 0) ≠ 0) (hLv : Lv (1, 0) ≠ 0)
    (huc : uc ((1 - η) * (Ybar - Gbar)) ξbar ≠ 0) (hβη : 1 - β * η ≠ 0) (hΦ : 1 - Φ ≠ 0)
    (ξh : ℕ → Ω → X) (E : ExoP Ω)
    (hgp : ∀ t w, E.gp t w = -Lu (0, ξh t w) / (Ybar * Lu (1, 0)))
    (hq : ∀ t w, E.q t w = -Lv (0, ξh t w) / (Ybar * Lv (1, 0)))
    (hflex : FlexNL 𝔼 β η Φ Ybar Gbar uc vy ξbar ξh E) :
    FlexE 𝔼 ⟨β, η, (-(Lu (1, 0) * Ybar) / uc ((1 - η) * (Ybar - Gbar)) ξbar) / (1 - β * η),
      Lv (1, 0) * Ybar / vy Ybar ξbar, θ, Φ⟩ E := by
  intro t
  funext w
  set ucb := uc ((1 - η) * (Ybar - Gbar)) ξbar with hucb
  have hc0 : ∀ s w', habArgF η Ybar Gbar 0 E s w' = (1 - η) * (Ybar - Gbar) := by
    intro s w'; rw [habArgF_eq]; ring
  have hss : vy Ybar ξbar = (1 - Φ) * ((1 - β * η) * ucb) := by
    have h := congrFun (hflex 0 t) w
    simp only [zero_mul, add_zero, zero_smul] at h
    rw [h]
    unfold lamF
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hc0, zero_smul, add_zero]
    rw [𝔼.const]
    ring
  set cc : ℕ → Ω → ℝ := fun s w' =>
    (E.n s w' - E.G s w') - η * (lagP E.nm1 E.n s w' - lagP E.Gm1 E.G s w') with hcc
  have hu : ∀ s w', HasDerivAt (fun ε => uc (habArgF η Ybar Gbar ε E s w') (ξbar + ε • ξh s w'))
      (Ybar * cc s w' * Lu (1, 0) + Lu (0, ξh s w')) 0 := by
    intro s w'
    simp only [habArgF_eq]
    exact hcurve hU _ _
  have hL : HasDerivAt (fun ε => vy (Ybar + ε * Ybar * E.n t w) (ξbar + ε • ξh t w))
      (Ybar * E.n t w * Lv (1, 0) + Lv (0, ξh t w)) 0 := by
    have e : (fun ε : ℝ => vy (Ybar + ε * Ybar * E.n t w) (ξbar + ε • ξh t w)) =
        fun ε => vy (Ybar + ε * (Ybar * E.n t w)) (ξbar + ε • ξh t w) := by
      funext ε; congr 1; ring
    rw [e]
    exact hcurve hV _ _
  have hR : HasDerivAt (fun ε => ((1 - Φ) • lamF 𝔼 β η Ybar Gbar ε uc ξbar ξh E t) w)
      ((1 - Φ) * ((Ybar * cc t w * Lu (1, 0) + Lu (0, ξh t w)) - (β * η) *
        𝔼.E t (fun w' => Ybar * cc (t + 1) w' * Lu (1, 0) + Lu (0, ξh (t + 1) w')) w)) 0 := by
    unfold lamF
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact HasDerivAt.const_mul (1 - Φ) (HasDerivAt.sub (hu t w)
      (HasDerivAt.const_mul (β * η) (hasDerivAt_E 𝔼 (fun w' => hu (t + 1) w') t w)))
  have hfun : (fun ε => vy (Ybar + ε * Ybar * E.n t w) (ξbar + ε • ξh t w)) =
      fun ε => ((1 - Φ) • lamF 𝔼 β η Ybar Gbar ε uc ξbar ξh E t) w := by
    funext ε; exact congrFun (hflex ε t) w
  rw [hfun] at hL
  have D := hL.unique hR
  have hEt : 𝔼.E t (fun w' => Ybar * cc (t + 1) w' * Lu (1, 0) + Lu (0, ξh (t + 1) w')) =
      (Ybar * Lu (1, 0)) • (𝔼.E t (E.n (t + 1) - η • E.n t) -
        𝔼.E t ((E.G (t + 1) + E.gp (t + 1)) - η • E.G t)) := by
    have e : (fun w' => Ybar * cc (t + 1) w' * Lu (1, 0) + Lu (0, ξh (t + 1) w')) =
        (Ybar * Lu (1, 0)) • ((E.n (t + 1) - η • E.n t) -
          ((E.G (t + 1) + E.gp (t + 1)) - η • E.G t)) := by
      funext w'
      simp only [hcc, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, lagP, hgp]
      field_simp
      ring
    rw [e, map_smul, map_sub]
  rw [hEt] at D
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at D
  unfold xTildeP gTilE
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hq t w, hgp t w, hss]
  simp only [hcc] at D
  field_simp
  linear_combination D


/-- **Woodford (2003), (E.6), p. 694, and the sign of `q` in (E.12) (new misprint).** At `η = 0`
the flexible-price relation reads `(ω + φ)Ŷⁿ_t = φg_t + ωq_t`, which is (E.6)
`Ŷⁿ = (σ⁻¹g + ωq)/(σ⁻¹ + ω)` (`φ = σ⁻¹`). The printed relation (p. 697)
`… = φg̃_t − ωq_t` (and the printed `(φg̃_t − ωq_t)Ŷ_t` in (E.12)) would contradict (E.6)
unless `ωq_t = 0`. The two printed signs are consistent with each other, so (E.13) is
unaffected. -/
theorem flexE_eta_zero {P : Par} (hη : P.η = 0) {E : ExoP Ω} (hflex : FlexE 𝔼 P E) (t : ℕ) :
    (P.ω + P.φ) • E.n t = P.φ • (E.G t + E.gp t) + P.ω • E.q t ∧
      ((P.ω + P.φ) • E.n t = P.φ • (E.G t + E.gp t) - P.ω • E.q t → P.ω • E.q t = 0) := by
  have h := hflex t
  unfold xTildeP gTilE at h
  rw [hη] at h
  simp only [zero_smul, sub_zero, mul_zero] at h
  have h1 : (P.ω + P.φ) • E.n t = P.φ • (E.G t + E.gp t) + P.ω • E.q t := by
    rw [add_smul]; exact h
  refine ⟨h1, fun h2 => ?_⟩
  have h3 := h1.symm.trans h2
  funext w
  have := congrFun h3 w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
  linarith

/-- Woodford (2003), p. 697: the exogenous processes are adapted (with `Ĝ_{−1}`, `Ŷⁿ_{−1}` known
at date 0). -/
def ExoP.Adapted (E : ExoP Ω) : Prop :=
  𝔼.Adapted E.G ∧ 𝔼.Adapted E.gp ∧ 𝔼.Adapted E.q ∧ 𝔼.Adapted E.n ∧ 𝔼.E 0 E.Gm1 = E.Gm1 ∧
    𝔼.E 0 E.nm1 = E.nm1

/-- Woodford (2003), p. 697: the realised flexible-price residual as a process,
`r_t = [ω + φ(1 + βη²)]Ŷⁿ_t − ηφŶⁿ_{t−1} − βηφŶⁿ_{t+1} − (φg̃_t + ωq_t)`. -/
theorem rS_fun (P : Par) (E : ExoP Ω) (t : ℕ) :
    (fun w => rS P (E.at w) t) = P.A • E.n t - (P.η * P.φ) • lagP E.nm1 E.n t -
      (P.β * P.η * P.φ) • E.n (t + 1) - (P.φ • ((E.G t + E.gp t - P.η • lagP E.Gm1 E.G t) -
        (P.β * P.η) • ((E.G (t + 1) + E.gp (t + 1)) - P.η • E.G t)) + P.ω • E.q t) := by
  funext w
  simp only [rS, gTil, gS, ExoP.at, lagP_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

/-- **Woodford (2003), p. 697: the book's flexible-price relation is `E_t r_t = 0`.** For
adapted exogenous processes, `FlexE ↔ ∀ t, E_t r_t = 0` (`r` the realised residual `rS`). -/
theorem flexE_iff {P : Par} {E : ExoP Ω} (hE : E.Adapted 𝔼) :
    FlexE 𝔼 P E ↔ ∀ t, 𝔼.E t (fun w => rS P (E.at w) t) = 0 := by
  obtain ⟨hG, hgp, hq, hn, hG0, hn0⟩ := hE
  have key : ∀ t, 𝔼.E t (fun w => rS P (E.at w) t) =
      (P.ω • E.n t + P.φ • xTildeP 𝔼 P.β P.η E.nm1 E.n t) -
        (P.φ • gTilE 𝔼 P.β P.η E t + P.ω • E.q t) := by
    intro t
    rw [rS_fun]
    unfold xTildeP gTilE
    simp only [map_sub, map_add, map_smul, hG t, hgp t, hq t, hn t, lagP_known 𝔼 hn0 hn t,
      lagP_known 𝔼 hG0 hG t]
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    unfold Par.A
    ring
  refine forall_congr' fun t => ?_
  rw [key t, sub_eq_zero]

/-! ### Proposition 6.6 under uncertainty -/

/-- Woodford (2003), App. E.3: a bounded process, uniformly in date and state. -/
def UBdd (x : ℕ → Ω → ℝ) : Prop := Bdd (fun p : ℕ × Ω => x p.1 p.2)

/-- Woodford (2003), App. E.3: the one-period-ahead shift of a uniformly bounded process. -/
theorem ubdd_shift {x : ℕ → Ω → ℝ} (hx : Bdd (fun p : ℕ × Ω => x p.1 p.2)) :
    Bdd (fun p : ℕ × Ω => x (p.1 + 1) p.2) := hx.comp (fun p : ℕ × Ω => (p.1 + 1, p.2))

/-- Woodford (2003), App. E.3: the lag of a uniformly bounded process (bounded initial value). -/
theorem ubdd_lag {x : ℕ → Ω → ℝ} {xm1 : Ω → ℝ} (hx : Bdd (fun p : ℕ × Ω => x p.1 p.2))
    (hm : Bdd xm1) : Bdd (fun p : ℕ × Ω => lagS (xm1 p.2) (fun s => x s p.2) p.1) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hm
  refine ⟨max A B, fun p => ?_⟩
  rcases p with ⟨t, w⟩
  cases t with
  | zero => exact le_max_of_le_right (hB w)
  | succ t => exact le_max_of_le_left (hA (t, w))

/-- Woodford (2003), App. E.3: the date-`t` slice of a uniformly bounded process is bounded. -/
theorem ubdd_slice {x : ℕ → Ω → ℝ} (hx : UBdd x) (w : Ω) :
    Bdd (fun t => x t w) := Bdd.comp hx (fun t => (t, w))

/-- Woodford (2003), p. 697: uniformly bounded exogenous processes. -/
def ExoP.UBounded (E : ExoP Ω) : Prop :=
  UBdd E.G ∧ UBdd E.gp ∧ UBdd E.q ∧ UBdd E.n ∧ Bdd E.Gm1 ∧ Bdd E.nm1

/-- Woodford (2003), p. 697: realised paths of uniformly bounded processes are bounded. -/
theorem ExoP.UBounded.at {E : ExoP Ω} (hE : E.UBounded) (w : Ω) : (E.at w).Bounded :=
  ⟨ubdd_slice hE.1 w, ubdd_slice hE.2.1 w, ubdd_slice hE.2.2.1 w, ubdd_slice hE.2.2.2.1 w⟩

/-- **Woodford (2003), App. E.3 (cross terms vanish in expectation).** If `E_t c_t = 0` and `y`
is adapted (both uniformly bounded, `0 ≤ β < 1`, pull-out), then
`E_0 ∑ βᵗ c_t y_t = 0`. -/
theorem E0_tsum_mul_zero (hPO : 𝔼.PullOut) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1)
    {c y : ℕ → Ω → ℝ} (hc : UBdd c) (hy : UBdd y) (hya : 𝔼.Adapted y)
    (hc0 : ∀ t, 𝔼.E t (c t) = 0) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * (c t w' * y t w')) w = 0 := by
  obtain ⟨Mc, hMc0, hMc⟩ := Bdd.nonneg_bound hc
  obtain ⟨My, -, hMy⟩ := Bdd.nonneg_bound hy
  have hu : Summable (fun k : ℕ => β ^ k * (Mc * My)) :=
    (summable_geometric_of_lt_one h0 h1).mul_right _
  have hf : ∀ k w', |β ^ k * (c k w' * y k w')| ≤ β ^ k * (Mc * My) := by
    intro k w'
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hMc (k, w')) (hMy (k, w')) (abs_nonneg _)
      hMc0) (pow_nonneg h0 k)
  rw [ForwardSolution.E_tsum_dom 𝔼 hu hf 0 w]
  have hz : ∀ k, 𝔼.E 0 (fun w' => β ^ k * (c k w' * y k w')) w = 0 := by
    intro k
    have e : (fun w' => β ^ k * (c k w' * y k w')) = β ^ k • (y k * c k) := by
      funext w'; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
    rw [e, map_smul, ← 𝔼.tower (Nat.zero_le k), hPO k (y k) (c k) (hya k), hc0 k, mul_zero,
      map_zero, smul_zero]
    rfl
  simp [hz]

/-- **Woodford (2003), (E.11), p. 697 (the expectation in `g̃`).** Under `E_0` the realised
`g_{t+1}` may be replaced by `E_t g_{t+1}`: for adapted `y` and uniformly bounded `c`,
`E_0 ∑ βᵗ c_t y_t = E_0 ∑ βᵗ (E_t c_t) y_t` (pull-out). -/
theorem E0_tsum_mul_E (hPO : 𝔼.PullOut) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1)
    {c y : ℕ → Ω → ℝ} (hc : UBdd c) (hy : UBdd y) (hya : 𝔼.Adapted y) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * (c t w' * y t w')) w =
      𝔼.E 0 (fun w' => ∑' t, β ^ t * (𝔼.E t (c t) w' * y t w')) w := by
  obtain ⟨Mc, hMc0, hMc⟩ := Bdd.nonneg_bound hc
  obtain ⟨My, -, hMy⟩ := Bdd.nonneg_bound hy
  have hu : Summable (fun k : ℕ => β ^ k * (Mc * My)) :=
    (summable_geometric_of_lt_one h0 h1).mul_right _
  have hf : ∀ k w', |β ^ k * (c k w' * y k w')| ≤ β ^ k * (Mc * My) := by
    intro k w'
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hMc (k, w')) (hMy (k, w')) (abs_nonneg _)
      hMc0) (pow_nonneg h0 k)
  have hf' : ∀ k w', |β ^ k * (𝔼.E k (c k) w' * y k w')| ≤ β ^ k * (Mc * My) := by
    intro k w'
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (𝔼.abs_E_le (fun w'' => hMc (k, w'')) k w')
      (hMy (k, w')) (abs_nonneg _) hMc0) (pow_nonneg h0 k)
  rw [ForwardSolution.E_tsum_dom 𝔼 hu hf 0 w, ForwardSolution.E_tsum_dom 𝔼 hu hf' 0 w]
  refine tsum_congr fun k => ?_
  have e1 : (fun w' => β ^ k * (c k w' * y k w')) = β ^ k • (y k * c k) := by
    funext w'; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have e2 : (fun w' => β ^ k * (𝔼.E k (c k) w' * y k w')) = β ^ k • (y k * 𝔼.E k (c k)) := by
    funext w'; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [e1, e2, map_smul, map_smul, ← 𝔼.tower (Nat.zero_le k) (y k * c k),
    hPO k (y k) (c k) (hya k)]

/-- Woodford (2003), App. E.3: passing a pathwise identity `F = aA − kR + T + S` through `E_0`
when `E_0 R = 0`. -/
theorem E0_of_pathwise {F A R T S : Ω → ℝ} (a k : ℝ)
    (h : ∀ w, F w = a * A w - k * R w + T w + S w) (w : Ω)
    (hR : 𝔼.E 0 R w = 0) :
    𝔼.E 0 F w = a * 𝔼.E 0 A w + 𝔼.E 0 T w + 𝔼.E 0 S w := by
  have e : F = a • A - k • R + T + S := by
    funext w'; rw [h w']; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e, map_add, map_add, map_sub, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hR]
  ring

/-- **Woodford (2003), Proposition 6.6, CORRECTED, under uncertainty (survey error 16).** For an
arbitrary `ExpectationSystem` with the pull-out property, uniformly bounded adapted processes,
and a natural rate satisfying the flexible-price relation (`FlexE`, e.g. from
`flex_loglinear`):
`E_0 ∑ βᵗU_t = −½ E_0 ∑ βᵗ[μ_x(x_t − δx_{t−1} − x̂*)² + (1 − βη)(θ⁻¹ + ω)var_i ŷ_t]
  + E_0[t.i.p.] + E_0 ∑ βᵗR_t`. -/
theorem prop66_corrected_expectation (hPO : 𝔼.PullOut) {P : Par} (hP : P.Std) (E : ExoP Ω)
    (Ym1 : Ω → ℝ) (Y V : ℕ → Ω → ℝ) (hYb : UBdd Y) (hVb : UBdd V) (hEb : E.UBounded)
    (hYa : 𝔼.Adapted Y) (hEa : E.Adapted 𝔼) (hflex : FlexE 𝔼 P E) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
      Useq P (E.at w') (Ym1 w') (fun t => Y t w') (fun t => V t w') t) w =
      -(1 / 2) * 𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
        (P.muX * gapSq P (E.at w') (Ym1 w') (fun t => Y t w') t +
          (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * V t w')) w +
      𝔼.E 0 (fun w' => tipTotal P (E.at w') (Ym1 w')) w +
      𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
        RUseq P (E.at w') (Ym1 w') (fun t => Y t w') (fun t => V t w') t) w := by
  refine E0_of_pathwise 𝔼 (-(1 / 2)) (1 - P.β * P.η) (fun w' => prop66_corrected hP (E.at w')
    (Ym1 w')
    (fun t => Y t w') (fun t => V t w') (ubdd_slice hYb w') (ubdd_slice hVb w') (hEb.at w')) w ?_
  obtain ⟨hG, hgp, hq, hn, hG0, hn0⟩ := hEb
  have hr : UBdd (fun t w => rS P (E.at w) t) := by
    change Bdd (fun p : ℕ × Ω => rS P (E.at p.2) p.1)
    simp only [rS, gTil, gS, ExoP.at]
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      ubdd_shift, ubdd_lag, Bdd.const])
  have hx : UBdd (fun t w => Y t w - E.n t w) := hYb.sub hn
  have hxa : 𝔼.Adapted (fun t w => Y t w - E.n t w) := by
    intro t
    change 𝔼.E t (Y t - E.n t) = Y t - E.n t
    rw [map_sub, hYa t, hEa.2.2.2.1 t]
  exact E0_tsum_mul_zero 𝔼 hPO hP.1 hP.2.1 hr hx hxa ((flexE_iff 𝔼 hEa).mp hflex) w


/-- Woodford (2003), App. E.3: the realised flexible-price residual is uniformly bounded. -/
theorem rS_ubdd (P : Par) {E : ExoP Ω} (hEb : E.UBounded) :
    UBdd (fun t w => rS P (E.at w) t) := by
  obtain ⟨hG, hgp, hq, hn, hG0, hn0⟩ := hEb
  change Bdd (fun p : ℕ × Ω => rS P (E.at p.2) p.1)
  simp only [rS, gTil, gS, ExoP.at]
  aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
    ubdd_shift, ubdd_lag, Bdd.const])

/-- **Woodford (2003), (2.28) under uncertainty.** The expected discounted utility under habit
persistence and Calvo pricing (dispersion law (2.20) state by state, `var_i ŷ_t = θ²Δ_t`):
`E_0 ∑ βᵗU_t = −Λ E_0 ∑ βᵗ[p_t² + λ(x_t − δx_{t−1} − x̂*)²] + E_0[t.i.p.] + E_0 ∑ βᵗR_t`,
`λ = κ/θ`. -/
theorem welfare228_expectation (hPO : 𝔼.PullOut) {P : Par} (hP : P.Std) {α : ℝ}
    (Δm1 : Ω → ℝ) (Δ p : ℕ → Ω → ℝ) (E : ExoP Ω) (Ym1 : Ω → ℝ) (Y V : ℕ → Ω → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) (hYb : UBdd Y) (hpb : UBdd p)
    (hEb : E.UBounded) (hYa : 𝔼.Adapted Y) (hEa : E.Adapted 𝔼) (hflex : FlexE 𝔼 P E)
    (hrec : ∀ t w, Δ t w = α * lagS (Δm1 w) (fun s => Δ s w) t + α / (1 - α) * p t w ^ 2)
    (hV : ∀ t w, V t w = P.θ ^ 2 * Δ t w) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
      Useq P (E.at w') (Ym1 w') (fun t => Y t w') (fun t => V t w') t) w =
      -P.Lam α * 𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
        (p t w' ^ 2 + P.lam α * gapSq P (E.at w') (Ym1 w') (fun t => Y t w') t)) w +
      𝔼.E 0 (fun w' => tipTotal P (E.at w') (Ym1 w') -
        (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ)) * (α * Δm1 w' / (1 - α * P.β))) w +
      𝔼.E 0 (fun w' => ∑' t, P.β ^ t *
        RUseq P (E.at w') (Ym1 w') (fun t => Y t w') (fun t => V t w') t) w := by
  refine E0_of_pathwise 𝔼 (-P.Lam α) (1 - P.β * P.η) (fun w' => welfare228 hP (E.at w')
    (Ym1 w') (fun t => Y t w') (fun t => V t w') hα0 hα1 hθ (ubdd_slice hYb w')
    (ubdd_slice hpb w') (hEb.at w') (hrec · w') (hV · w')) w ?_
  have hx : UBdd (fun t w => Y t w - E.n t w) := hYb.sub hEb.2.2.2.1
  have hxa : 𝔼.Adapted (fun t w => Y t w - E.n t w) := by
    intro t
    change 𝔼.E t (Y t - E.n t) = Y t - E.n t
    rw [map_sub, hYa t, hEa.2.2.2.1 t]
  exact E0_tsum_mul_zero 𝔼 hPO hP.1 hP.2.1 (rS_ubdd P hEb) hx hxa
    ((flexE_iff 𝔼 hEa).mp hflex) w

/-- Woodford (2003), (E.11), p. 697: the summand of (E.11) without the `g̃` term. -/
noncomputable def E11core (P : Par) (Ym1 : ℝ) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - P.β * P.η) * Y t + ((1 - P.β * P.η) - P.sinv * (1 + P.β * P.η ^ 2)) / 2 * Y t ^ 2 +
    P.η * P.sinv * Y t * lagS Ym1 Y t

/-- Woodford (2003), (E.11): the realised `g̃_t` has conditional expectation the book's `g̃_t`
(adapted exogenous processes). -/
theorem E_gTil {P : Par} {E : ExoP Ω} (hEa : E.Adapted 𝔼) (t : ℕ) :
    𝔼.E t (fun w => gTil P (E.at w) t) = gTilE 𝔼 P.β P.η E t := by
  obtain ⟨hG, hgp, -, -, hG0, -⟩ := hEa
  have e : (fun w => gTil P (E.at w) t) = (E.G t + E.gp t - P.η • lagP E.Gm1 E.G t) -
      (P.β * P.η) • ((E.G (t + 1) + E.gp (t + 1)) - P.η • E.G t) := by
    funext w
    simp only [gTil, gS, ExoP.at, lagP_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [e]
  unfold gTilE
  rw [map_sub (𝔼.E t), map_smul, map_sub (𝔼.E t), map_add, hG t, hgp t, map_smul,
    lagP_known 𝔼 hG0 hG t]

/-- **Woodford (2003), eq. (E.11), p. 697, with the book's `E_t g_{t+1}` (under uncertainty).**
`E_0 ∑ βᵗ{(E.10) braces} = E_0 ∑ βᵗ[(1 − βη)Ŷ_t + ½((1 − βη) − σ⁻¹(1 + βη²))Ŷ_t²
+ ησ⁻¹Ŷ_tŶ_{t−1} + σ⁻¹g̃_tŶ_t] + E_0 K_0`, with
`g̃_t = (g_t − ηĜ_{t−1}) − βηE_t(g_{t+1} − ηĜ_t)`. -/
theorem E11_expectation (hPO : 𝔼.PullOut) {P : Par} (hP : P.Std) (E : ExoP Ω) (Ym1 : Ω → ℝ)
    (Y : ℕ → Ω → ℝ) (hYb : UBdd Y) (hEb : E.UBounded) (hYa : 𝔼.Adapted Y)
    (hEa : E.Adapted 𝔼) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, P.β ^ t * braceSeq P (E.at w') (Ym1 w') (fun t => Y t w') t) w =
      𝔼.E 0 (fun w' => ∑' t, P.β ^ t * (E11core P (Ym1 w') (fun t => Y t w') t +
        P.sinv * (gTilE 𝔼 P.β P.η E t w' * Y t w'))) w +
      𝔼.E 0 (fun w' => K1 P (E.at w') (Ym1 w') (fun t => Y t w') 0) w := by
  have h0 := hP.1
  have h1 := hP.2.1
  have hc : UBdd (fun t w => gTil P (E.at w) t) := by
    obtain ⟨hG, hgp, hq, hn, hG0, hn0⟩ := hEb
    change Bdd (fun p : ℕ × Ω => gTil P (E.at p.2) p.1)
    simp only [gTil, gS, ExoP.at]
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      ubdd_shift, ubdd_lag, Bdd.const])
  have hcore : ∀ w', Bdd (E11core P (Ym1 w') (fun t => Y t w')) := by
    intro w'
    have hY' := ubdd_slice hYb w'
    unfold E11core
    aesop (add safe apply [Bdd.add, Bdd.sub, Bdd.mul, Bdd.neg, Bdd.div_const, Bdd.pow,
      Bdd.shift, Bdd.lagS, Bdd.const])
  have hgY : ∀ w', Bdd (fun t => gTil P (E.at w') t * Y t w') :=
    fun w' => (ubdd_slice hc w').mul (ubdd_slice hYb w')
  have hEgY : ∀ w', Bdd (fun t => gTilE 𝔼 P.β P.η E t w' * Y t w') := by
    intro w'
    obtain ⟨M, hM⟩ := hc
    refine (show Bdd (fun t => gTilE 𝔼 P.β P.η E t w') from ⟨M, fun t => ?_⟩).mul
      (ubdd_slice hYb w')
    change |gTilE 𝔼 P.β P.η E t w'| ≤ M
    rw [← E_gTil 𝔼 hEa t]
    exact 𝔼.abs_E_le (fun w'' => hM (t, w'')) t w'
  have hL : ∀ w', ∑' t, P.β ^ t * braceSeq P (E.at w') (Ym1 w') (fun t => Y t w') t =
      ∑' t, P.β ^ t * E11core P (Ym1 w') (fun t => Y t w') t +
        P.sinv * ∑' t, P.β ^ t * (gTil P (E.at w') t * Y t w') +
        K1 P (E.at w') (Ym1 w') (fun t => Y t w') 0 := by
    intro w'
    rw [E11_discounted P (E.at w') (Ym1 w') (fun t => Y t w') h0 h1 (ubdd_slice hYb w')
      (hEb.at w')]
    congr 1
    rw [← tsum_mul_left, ← ((hcore w').summable h0 h1).tsum_add
      (((hgY w').summable h0 h1).mul_left _)]
    congr 1
    funext t
    unfold E11seq E11core
    ring
  have hR : ∀ w', ∑' t, P.β ^ t * (E11core P (Ym1 w') (fun t => Y t w') t +
      P.sinv * (gTilE 𝔼 P.β P.η E t w' * Y t w')) =
      ∑' t, P.β ^ t * E11core P (Ym1 w') (fun t => Y t w') t +
        P.sinv * ∑' t, P.β ^ t * (gTilE 𝔼 P.β P.η E t w' * Y t w') := by
    intro w'
    rw [← tsum_mul_left, ← ((hcore w').summable h0 h1).tsum_add
      (((hEgY w').summable h0 h1).mul_left _)]
    congr 1
    funext t
    ring
  have eL : (fun w' => ∑' t, P.β ^ t * braceSeq P (E.at w') (Ym1 w') (fun t => Y t w') t) =
      (fun w' => ∑' t, P.β ^ t * E11core P (Ym1 w') (fun t => Y t w') t) +
        P.sinv • (fun w' => ∑' t, P.β ^ t * (gTil P (E.at w') t * Y t w')) +
        (fun w' => K1 P (E.at w') (Ym1 w') (fun t => Y t w') 0) := by
    funext w'
    rw [hL w']
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have eR : (fun w' => ∑' t, P.β ^ t * (E11core P (Ym1 w') (fun t => Y t w') t +
      P.sinv * (gTilE 𝔼 P.β P.η E t w' * Y t w'))) =
      (fun w' => ∑' t, P.β ^ t * E11core P (Ym1 w') (fun t => Y t w') t) +
        P.sinv • (fun w' => ∑' t, P.β ^ t * (gTilE 𝔼 P.β P.η E t w' * Y t w')) := by
    funext w'
    rw [hR w']
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hkey := E0_tsum_mul_E 𝔼 hPO h0 h1 hc hYb hYa w
  simp only [E_gTil 𝔼 hEa] at hkey
  rw [eL, eR, map_add, map_add, map_add, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hkey]

end Woodford.StabilizationWelfare.HabitWelfare
