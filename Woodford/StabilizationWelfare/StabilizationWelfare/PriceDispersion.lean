/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Prop61
import StabilizationWelfare.Expectations

/-!
# Inflation and relative-price distortions

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2 (pp. 396–405) and Appendix E.2
(pp. 694–696): Propositions 6.2–6.5.

## The New Classical model (pp. 397–398)

* (2.14) `kappaNC`, `kappaNC_pos`.
* `surprise_eq`: with the price index `log P = ι log p¹ + (1−ι) log p² + a` and the predetermined
  sticky price `log p² = E_{t−1} log p¹ + b` (2.15), unexpected inflation is
  `π − E_{t−1}π = ι(log p¹ − log p²) + (ι b + a − E_{t−1} a)`, for any `ExpectationSystem`.
* `twoPoint_index`: the index error is second order, `|a| ≤ |1−θ| ι(1−ι)(p¹ − p²)²`.
* **Proposition 6.2** `prop62`, `prop62_layerA`: `U_t = −Θ L_t + t.i.p. + R`,
  `L_t = (π_t − E_{t−1}π_t)² + λ(x_t − x*)²`, `λ = κ/θ` (`prop62_weight`), `Θ > 0`, with the
  remainder explicit (weighted degree three).

## The Calvo model

* **Proposition 6.3** (2.20) `prop63_layerA`: from the exact (E.8)
  (`CrossSection.goods_calvo_var`) and the exact bound `|log P − P̄| ≤ |1−θ| Δ`,
  `Δ_t = α Δ_{t−1} + (α/(1−α)) π_t² + R63` with `|R63| ≤ (α/(1−α))(2|π_t| D + D²)`,
  `D = |1−θ|(Δ_t + Δ_{t−1})`: the book's `P̄_t = log P_t + O(2)` is proved, not asserted.
  The survey's error 25 (uniform-in-`t` bounds are needed for discounted sums; `π = O(φ, ξ̃)`
  is asserted) is handled by explicit hypotheses: `disp_uniform_bound`, `prop63_uniform`.
* **Proposition 6.4** (2.21)–(2.22) `prop64`: the discounted sum of period welfare equals
  `−Θ ∑ βᵗ (π_t² + λ (x_t − x*)²) + t.i.p. + R` with `λ = κ/θ`, `κ` from (2.19)
  (`calvo_weight`), genuine `tsum`s, the t.i.p. explicit (initial dispersion `Δ_{−1}` and the
  exogenous terms) and the remainder explicit and bounded (`Sequences.abs_tsum_le`).
  Footnote 26: `fn26_value` (`16κ/θ = 0.0487…`), `fn26_kappa_consistent`.
* **Proposition 6.5** (2.23)–(2.25) `index_layerA`, `prop65`: indexation to lagged inflation,
  `Δ_t = α Δ_{t−1} + (α/(1−α))(π_t − γ π_{t−1})² + R` and the loss `(π_t − γπ_{t−1})² + λ x̃²`.

Dating: index `0` is date `−1` (`D 0 = Δ_{−1}`, `infl 0 = π_{−1}`); index `t + 1` is date `t`.
The identities hold state by state, so they also hold after applying `E_0` (linear).
-/

namespace Woodford.StabilizationWelfare.PriceDispersion

open MeasureTheory Filter Topology
open Woodford.StabilizationWelfare.CrossSection Woodford.StabilizationWelfare.Prop61
open Moments (calvoKappa)
open Sequences (summable_norm_geom_bdd disp_discounted_hasSum)

variable {G : Type*} [MeasurableSpace G]

/-! ### The New Classical model: (2.14)–(2.17), Proposition 6.2 -/

/-- Woodford (2003), eq. (2.14), p. 397: the slope of the New Classical aggregate-supply
relation, `κ = (ι/(1−ι)) (σ⁻¹ + ω)/(1 + ωθ)`. -/
noncomputable def kappaNC (ι sinv omega θ : ℝ) : ℝ :=
  ι / (1 - ι) * ((sinv + omega) / (1 + omega * θ))

/-- Woodford (2003), p. 397: `κ > 0` for `0 < ι < 1`, `σ⁻¹ + ω > 0`, `1 + ωθ > 0`. -/
theorem kappaNC_pos {ι sinv omega θ : ℝ} (hι0 : 0 < ι) (hι1 : ι < 1) (hs : 0 < sinv + omega)
    (hd : 0 < 1 + omega * θ) : 0 < kappaNC ι sinv omega θ := by
  unfold kappaNC
  have : 0 < 1 - ι := by linarith
  positivity

/-- Woodford (2003), p. 397 (**unexpected inflation in the two-price model, exact**). Let the
log price index at date `t+1` be `log P_{t+1} = ι p¹ + (1−ι) p² + a` (`a` the index error), the
sticky price `p²` be known at `t`, and `log P_t` be known at `t`. Then
`π_{t+1} − E_t π_{t+1} = ι(p¹ − p²) + (ι(p² − E_t p¹) + (a − E_t a))`; with (2.15)
`p² = E_t p¹ + b` the bracket is `ι b + a − E_t a`, of second order. -/
theorem surprise_eq {Ω : Type*} (𝔼 : ExpectationSystem Ω) {t : ℕ} {ι : ℝ}
    {logP : ℕ → Ω → ℝ} {p₁ p₂ a : Ω → ℝ} (hP : logP (t + 1) = ι • p₁ + (1 - ι) • p₂ + a)
    (hp₂ : 𝔼.E t p₂ = p₂) (hPt : 𝔼.E t (logP t) = logP t) :
    (logP (t + 1) - logP t) - 𝔼.E t (logP (t + 1) - logP t) =
      ι • (p₁ - p₂) + (ι • (p₂ - 𝔼.E t p₁) + (a - 𝔼.E t a)) := by
  rw [map_sub, hPt, hP]
  simp only [map_add, map_smul, hp₂]
  module

/-- Woodford (2003), p. 397: the second-order error of unexpected inflation is bounded by the
pricing error and the index error: `|ι b + a − E_t a| ≤ ι |b| + 2 A` when `|a| ≤ A`. -/
theorem surprise_err_le {Ω : Type*} (𝔼 : ExpectationSystem Ω) (t : ℕ) {ι A : ℝ} (hι : 0 ≤ ι)
    {a b : Ω → ℝ} (ha : ∀ ω, |a ω| ≤ A) (ω : Ω) :
    |ι * b ω + a ω - 𝔼.E t a ω| ≤ ι * |b ω| + 2 * A := by
  have h1 := 𝔼.abs_E_le ha t ω
  have h2 := abs_sub (ι * b ω + a ω) (𝔼.E t a ω)
  have h3 := abs_add_le (ι * b ω) (a ω)
  rw [abs_mul, abs_of_nonneg hι] at h3
  linarith [ha ω]

/-- Woodford (2003), p. 397 (**`log P_t = ι log p¹ + (1−ι) log p² + O(ξ̃²)`, exact bound**): for a
goods population with a fraction `ι` at `p¹` and `1 − ι` at `p²`, the Dixit–Stiglitz log price
index `logMeanExp μ (1 − θ)` satisfies
`|log P − (ι p¹ + (1−ι) p²)| ≤ |1 − θ| ι(1−ι)(p¹ − p²)²` when `|1 − θ| |p¹ − p²| ≤ 1`. -/
theorem twoPoint_index (μ : Measure G) [IsProbabilityMeasure μ] {F : Set G}
    (hF : MeasurableSet F) {ι p₁ p₂ θ : ℝ} (hι : μ.real F = ι) (hι0 : 0 ≤ ι) (hι1 : ι ≤ 1)
    {x : G → ℝ} (h1 : ∀ i ∈ F, x i = p₁) (h2 : ∀ i ∉ F, x i = p₂) (hθ : θ ≠ 1)
    (hsmall : |1 - θ| * |p₁ - p₂| ≤ 1) :
    |logMeanExp μ (1 - θ) x - (ι * p₁ + (1 - ι) * p₂)| ≤
      |1 - θ| * (ι * (1 - ι) * (p₁ - p₂) ^ 2) := by
  obtain ⟨hm, hv⟩ := twoPoint_var μ hF hι h1 h2
  have hxe : x = fun i => p₂ + (p₁ - p₂) * F.indicator (fun _ => (1 : ℝ)) i := by
    funext i
    by_cases h : i ∈ F
    · rw [Set.indicator_of_mem h, h1 i h]; ring
    · rw [Set.indicator_of_notMem h, h2 i h]; ring
  have hxm : Measurable x := by
    rw [hxe]
    exact measurable_const.add (measurable_const.mul (measurable_const.indicator hF))
  have hB : ∀ i, |x i - crossMean μ x| ≤ |p₁ - p₂| := by
    intro i
    rw [hm]
    by_cases h : i ∈ F
    · rw [h1 i h, show p₁ - (ι * p₁ + (1 - ι) * p₂) = (1 - ι) * (p₁ - p₂) by ring, abs_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ι)]
      have := abs_nonneg (p₁ - p₂)
      nlinarith
    · rw [h2 i h, show p₂ - (ι * p₁ + (1 - ι) * p₂) = -(ι * (p₁ - p₂)) by ring, abs_neg,
        abs_mul, abs_of_nonneg hι0]
      have := abs_nonneg (p₁ - p₂)
      nlinarith
  have hr : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h := logMeanExp_sub_mean_le μ hxm hB hr hsmall
  rwa [hm, hv] at h

/-- Woodford (2003), Prop. 6.2, p. 398: the factor `Θ = θ(1 + ωθ)(1 − ι)/(2ι)` multiplying the
loss (in units of `Ȳ u_c`). -/
noncomputable def ThetaNC (θ omega ι : ℝ) : ℝ := θ * (1 + omega * θ) * (1 - ι) / ι / 2

/-- Woodford (2003), Prop. 6.2: `Θ > 0`. -/
theorem ThetaNC_pos {θ omega ι : ℝ} (hθ : 0 < θ) (hd : 0 < 1 + omega * θ) (hι0 : 0 < ι)
    (hι1 : ι < 1) : 0 < ThetaNC θ omega ι := by
  unfold ThetaNC
  have : 0 < 1 - ι := by linarith
  positivity

/-- Woodford (2003), eq. (2.16), p. 398 (**`λ = κ/θ`**): the relative weight
`(σ⁻¹ + ω)/(2Θ)` on the output gap equals `κ/θ` with `κ` of (2.14). -/
theorem prop62_weight {θ omega ι sinv : ℝ} (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0) (hι0 : ι ≠ 0)
    (hι1 : 1 - ι ≠ 0) :
    ThetaNC θ omega ι * (kappaNC ι sinv omega θ / θ) = (sinv + omega) / 2 := by
  have hd' : 1 + θ * omega ≠ 0 := by rwa [mul_comm]
  unfold ThetaNC kappaNC
  field_simp

/-- Woodford (2003), **Proposition 6.2, eqs. (2.16)–(2.17), p. 398 (Layer A, exact)**: with
`var_i log p = ι(1−ι)(p¹ − p²)²` and unexpected inflation `S = ι(p¹ − p²) + e`,
`−½[(σ⁻¹+ω) X² + θ(1+ωθ) var_i log p] = −Θ [S² + (κ/θ) X²] − ½ θ(1+ωθ) twoPointRem`. -/
theorem prop62 {θ omega ι sinv dp e S X : ℝ} (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0)
    (hι0 : ι ≠ 0) (hι1 : 1 - ι ≠ 0) (hS : S = ι * dp + e) :
    -(1 / 2) * ((sinv + omega) * X ^ 2 + θ * (1 + omega * θ) * (ι * (1 - ι) * dp ^ 2)) =
      -ThetaNC θ omega ι * (S ^ 2 + kappaNC ι sinv omega θ / θ * X ^ 2) -
        θ * (1 + omega * θ) / 2 * twoPointRem ι dp e := by
  have h := twoPoint_subst (p₁ := dp) (p₂ := 0) (s := S) (e := e) hι0
    (by rw [sub_zero]; exact hS)
  rw [sub_zero] at h
  rw [h]
  unfold ThetaNC kappaNC
  field_simp
  ring

/-- Woodford (2003), **Proposition 6.2 under uncertainty (Layer A, exact, state by state)**:
for any `ExpectationSystem`, with the index and pricing structure of `surprise_eq`, in every
state `ω` the dispersion part of (2.13) equals
`−Θ[(π_{t+1} − E_t π_{t+1})² + (κ/θ) X²] − ½θ(1+ωθ) twoPointRem ι (p¹ − p²) e`, where the
second-order error is `e = ι(p² − E_t p¹) + (a − E_t a)` (`surprise_err_le`). -/
theorem prop62_expectations {Ω : Type*} (𝔼 : ExpectationSystem Ω) {t : ℕ}
    {ι θ omega sinv : ℝ} {logP : ℕ → Ω → ℝ} {p₁ p₂ a : Ω → ℝ}
    (hP : logP (t + 1) = ι • p₁ + (1 - ι) • p₂ + a) (hp₂ : 𝔼.E t p₂ = p₂)
    (hPt : 𝔼.E t (logP t) = logP t) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0) (hι0 : ι ≠ 0)
    (hι1 : 1 - ι ≠ 0) (X : Ω → ℝ) (ω : Ω) :
    -(1 / 2) * ((sinv + omega) * X ω ^ 2 +
        θ * (1 + omega * θ) * (ι * (1 - ι) * (p₁ ω - p₂ ω) ^ 2)) =
      -ThetaNC θ omega ι *
          (((logP (t + 1) - logP t) - 𝔼.E t (logP (t + 1) - logP t)) ω ^ 2 +
            kappaNC ι sinv omega θ / θ * X ω ^ 2) -
        θ * (1 + omega * θ) / 2 *
          twoPointRem ι (p₁ ω - p₂ ω) (ι * (p₂ ω - 𝔼.E t p₁ ω) + (a ω - 𝔼.E t a ω)) := by
  have h := congrFun (surprise_eq 𝔼 hP hp₂ hPt) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  exact prop62 hθ hd hι0 hι1 h

/-- Woodford (2003), **Proposition 6.2 assembled with Proposition 6.1 (Layer A, exact)**: in
the New Classical model, `Tu − E_i Tv = −Θ [S² + (κ/θ)(x − x*)²] + tipA + R` with
`R = R3 − ½ θ(1+ωθ) twoPointRem`, a remainder of weighted degree at least three
(`R3_scale`, `twoPointRem_scale`), and `x − x*` the welfare-relevant gap. -/
theorem prop62_layerA {sinv omega θ ι g q Φ Y e n k dp eS S : ℝ}
    (hden : sinv + omega ≠ 0) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0) (hι0 : ι ≠ 0)
    (hι1 : 1 - ι ≠ 0) (hS : S = ι * dp + eS) :
    Tu sinv g Y - ((1 - Φ) * (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * (ι * (1 - ι) * dp ^ 2)) - e) +
        (1 + omega) / 2 * (θ ^ 2 * (ι * (1 - ι) * dp ^ 2) +
          (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * (ι * (1 - ι) * dp ^ 2)) - e) ^ 2) -
        omega * q * (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * (ι * (1 - ι) * dp ^ 2)) - e)) =
      -ThetaNC θ omega ι * (S ^ 2 + kappaNC ι sinv omega θ / θ *
          ((Y - (natLin sinv omega g q + n)) - (xStarLin sinv omega Φ + k)) ^ 2) +
        tipA sinv omega g q Φ +
        (R3 sinv omega θ g q Φ Y (θ ^ 2 * (ι * (1 - ι) * dp ^ 2)) e n k -
          θ * (1 + omega * θ) / 2 * twoPointRem ι dp eS) := by
  rw [prop61_disp (n := n) (k := k) hden hθ, prop62 hθ hd hι0 hι1 hS]
  ring

/-- Woodford (2003), p. 398 (after Prop. 6.2): under (2.14) with `π − E_{t−1}π = S`, the output
gap is proportional to unexpected inflation, `x = S/κ`, so the loss is
`S² + (κ/θ)(S/κ − x*)²`: no tension between the two goals. -/
theorem nc_loss_surprise {κ θ S x xstar : ℝ} (hκ : κ ≠ 0) (hAS : S = κ * x) :
    S ^ 2 + κ / θ * (x - xstar) ^ 2 = S ^ 2 + κ / θ * (S / κ - xstar) ^ 2 := by
  rw [hAS, mul_div_cancel_left₀ x hκ]

/-! ### Proposition 6.3: the Calvo dispersion recursion (2.20) -/

/-- Woodford (2003), (E.7)–(E.8), p. 695: the remainder produced by substituting inflation
`π` for the change `π + d` in the mean log price, `(α/(1−α))(2πd + d²)`. -/
noncomputable def R63 (α π d : ℝ) : ℝ := α / (1 - α) * (2 * π * d + d ^ 2)

/-- Woodford (2003), (E.8) to (E.7): if `Δ' = αΔ + (α/(1−α)) m²` and `m = π + d`, then
`Δ' = αΔ + (α/(1−α)) π² + R63 α π d`. -/
theorem disp_subst {α Δ Δ' m π d : ℝ} (hrec : Δ' = α * Δ + α / (1 - α) * m ^ 2)
    (hm : m = π + d) : Δ' = α * Δ + α / (1 - α) * π ^ 2 + R63 α π d := by
  rw [hrec, hm]
  unfold R63
  ring

/-- Woodford (2003), (E.7): `|R63| ≤ (α/(1−α))(2|π| D + D²)` when `|d| ≤ D`, `0 ≤ α < 1`. -/
theorem R63_bound {α π d D : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hd : |d| ≤ D) :
    |R63 α π d| ≤ α / (1 - α) * (2 * |π| * D + D ^ 2) := by
  unfold R63
  have hc : 0 ≤ α / (1 - α) := div_nonneg hα0 (by linarith)
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 := abs_add_le (2 * π * d) (d ^ 2)
  have h2 : |2 * π * d| ≤ 2 * |π| * D := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have h3 : |d ^ 2| ≤ D ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg d) hd 2
  linarith

/-- Woodford (2003), (E.7) "`O(‖Δ^{1/2}, φ, ξ̃‖³)`" (**scaling lemma**): `π` of weight one and
`d` (of the order of `Δ`) of weight two give `R63(sπ, s²d) = s³ (α/(1−α))(2πd + s d²)`. -/
theorem R63_scale (α π d s : ℝ) :
    R63 α (s * π) (s ^ 2 * d) = s ^ 3 * (α / (1 - α) * (2 * π * d + s * d ^ 2)) := by
  unfold R63
  ring

/-- Woodford (2003), (2.20)/(2.24) and App. E.2, pp. 695–696 (**one Calvo step with an
indexation shift `d`, Layer A**). A goods population with log prices `xo` (date `t−1`) and
`xn` (date `t`): goods in the reset set `R` (measure `1 − α`) set `p`, the others keep `xo + d`,
and the non-resetters are representative of the old cross-section. If both cross-sections lie
within `Bo`, `Bn` of their means with `|1 − θ| Bo ≤ 1`, `|1 − θ| Bn ≤ 1`, then with the
Dixit–Stiglitz index `log P = logMeanExp μ (1 − θ)` and inflation `π = log P_t − log P_{t−1}`:
`Δ_t = α Δ_{t−1} + (α/(1−α))(π − d)² + R63 α (π − d) dd` exactly, where the error
`dd = (P̄_t − P̄_{t−1}) − π` satisfies `|dd| ≤ |1 − θ|(Δ_t + Δ_{t−1})`. -/
theorem step_layerA (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {α p d θ Bo Bn : ℝ} (hα : α ≠ 1) (hRm : μ.real R = 1 - α)
    {xo xn : G → ℝ} (hxo : Measurable xo) (hBo : ∀ i, |xo i - crossMean μ xo| ≤ Bo)
    (hBn : ∀ i, |xn i - crossMean μ xn| ≤ Bn) (hθ : θ ≠ 1) (hso : |1 - θ| * Bo ≤ 1)
    (hsn : |1 - θ| * Bn ≤ 1)
    (hrep1 : ∫ i in Rᶜ, xo i ∂μ = α * ∫ i, xo i ∂μ)
    (hrep2 : ∫ i in Rᶜ, xo i ^ 2 ∂μ = α * ∫ i, xo i ^ 2 ∂μ)
    (hn1 : ∀ i ∈ R, xn i = p) (hn2 : ∀ i ∉ R, xn i = xo i + d) :
    crossVar μ xn = α * crossVar μ xo +
        α / (1 - α) * (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo - d) ^ 2 +
        R63 α (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo - d)
          ((crossMean μ xn - crossMean μ xo) -
            (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo)) ∧
      |(crossMean μ xn - crossMean μ xo) -
          (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo)| ≤
        |1 - θ| * (crossVar μ xn + crossVar μ xo) := by
  classical
  obtain ⟨h1, -, -, -, -, -⟩ := centred_facts μ hxo hBo 0
  have h2 : Integrable (fun i => xo i ^ 2) μ := by
    obtain ⟨-, -, hz2, -, -, -⟩ := centred_facts μ hxo hBo 0
    have : (fun i => xo i ^ 2) = fun i => (xo i - crossMean μ xo) ^ 2 +
        2 * crossMean μ xo * xo i - crossMean μ xo ^ 2 := by
      funext i; ring
    rw [this]
    exact (hz2.add (h1.const_mul _)).sub (integrable_const _)
  have hxn : Measurable xn := by
    have : xn = R.piecewise (fun _ => p) (fun i => xo i + d) := by
      funext i
      by_cases h : i ∈ R
      · rw [Set.piecewise_eq_of_mem _ _ _ h, hn1 i h]
      · rw [Set.piecewise_eq_of_notMem _ _ _ h, hn2 i h]
    rw [this]
    exact Measurable.piecewise hR measurable_const (hxo.add_const d)
  obtain ⟨-, hvar⟩ := goods_index_var μ hR hα hRm h1 h2 hrep1 hrep2 hn1 hn2
  have hr : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have ho := logMeanExp_sub_mean_le μ hxo hBo hr hso
  have hn := logMeanExp_sub_mean_le μ hxn hBn hr hsn
  refine ⟨?_, ?_⟩
  · exact disp_subst hvar (by ring)
  · have e : (crossMean μ xn - crossMean μ xo) -
        (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo) =
        -(logMeanExp μ (1 - θ) xn - crossMean μ xn) +
          (logMeanExp μ (1 - θ) xo - crossMean μ xo) := by ring
    rw [e]
    have := abs_add_le (-(logMeanExp μ (1 - θ) xn - crossMean μ xn))
      (logMeanExp μ (1 - θ) xo - crossMean μ xo)
    rw [abs_neg] at this
    linarith

/-- Woodford (2003), **Proposition 6.3, eq. (2.20)/(E.7), p. 399 (Layer A)**: one Calvo step
(no indexation): `Δ_t = α Δ_{t−1} + (α/(1−α)) π_t² + R63 α π_t dd` exactly, where
`π_t = log P_t − log P_{t−1}` is inflation of the Dixit–Stiglitz index and
`|dd| ≤ |1 − θ|(Δ_t + Δ_{t−1})`, so `|R63| ≤ (α/(1−α))(2|π_t| D + D²)` with
`D = |1−θ|(Δ_t + Δ_{t−1})` (`R63_bound`): weighted degree three in `(Δ^{1/2}, π)`. -/
theorem prop63_layerA (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {α p θ Bo Bn : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hRm : μ.real R = 1 - α)
    {xo xn : G → ℝ} (hxo : Measurable xo) (hBo : ∀ i, |xo i - crossMean μ xo| ≤ Bo)
    (hBn : ∀ i, |xn i - crossMean μ xn| ≤ Bn) (hθ : θ ≠ 1) (hso : |1 - θ| * Bo ≤ 1)
    (hsn : |1 - θ| * Bn ≤ 1)
    (hrep1 : ∫ i in Rᶜ, xo i ∂μ = α * ∫ i, xo i ∂μ)
    (hrep2 : ∫ i in Rᶜ, xo i ^ 2 ∂μ = α * ∫ i, xo i ^ 2 ∂μ)
    (hn1 : ∀ i ∈ R, xn i = p) (hn2 : ∀ i ∉ R, xn i = xo i) :
    ∃ dd : ℝ, crossVar μ xn = α * crossVar μ xo +
        α / (1 - α) * (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo) ^ 2 +
        R63 α (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo) dd ∧
      |dd| ≤ |1 - θ| * (crossVar μ xn + crossVar μ xo) ∧
      |R63 α (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo) dd| ≤
        α / (1 - α) * (2 * |logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo| *
          (|1 - θ| * (crossVar μ xn + crossVar μ xo)) +
          (|1 - θ| * (crossVar μ xn + crossVar μ xo)) ^ 2) := by
  obtain ⟨h1, h2⟩ := step_layerA μ hR (d := 0) hα1.ne hRm hxo hBo hBn hθ hso hsn hrep1 hrep2
    hn1 (fun i hi => by rw [hn2 i hi, add_zero])
  simp only [sub_zero] at h1
  exact ⟨_, h1, h2, R63_bound hα0 hα1 h2⟩

/-- Woodford (2003), p. 400 and survey error 25 (**a uniform-in-`t` dispersion bound**): if
`Δ_{t+1} = α Δ_t + c q_t` with `0 ≤ α < 1`, `c ≥ 0`, `0 ≤ q_t ≤ M` and `Δ_0 ≥ 0`, then
`0 ≤ Δ_t ≤ Δ_0 + c M/(1 − α)` for every `t`. With `q_t` the squared change in the mean log
price (bounded by `ε²`), dispersion stays of second order uniformly in `t`. -/
theorem disp_uniform_bound {α c M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    {D q : ℕ → ℝ} (hD0 : 0 ≤ D 0) (hq0 : ∀ t, 0 ≤ q t) (hqM : ∀ t, q t ≤ M)
    (hrec : ∀ t, D (t + 1) = α * D t + c * q t) (t : ℕ) :
    0 ≤ D t ∧ D t ≤ D 0 + c * M / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith
  have hM : 0 ≤ M := (hq0 0).trans (hqM 0)
  have hcM : 0 ≤ c * M / (1 - α) := div_nonneg (mul_nonneg hc hM) h1α.le
  induction t with
  | zero => exact ⟨hD0, by linarith⟩
  | succ t ih =>
    rw [hrec t]
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨add_nonneg (mul_nonneg hα0 ih0) (mul_nonneg hc (hq0 t)), ?_⟩
    have e : c * M / (1 - α) = α * (c * M / (1 - α)) + c * M := by
      field_simp
      ring
    have h3 : α * D t ≤ α * (D 0 + c * M / (1 - α)) := mul_le_mul_of_nonneg_left ih1 hα0
    have h4 : c * q t ≤ c * M := mul_le_mul_of_nonneg_left (hqM t) hc
    have h5 : α * D 0 ≤ D 0 := by nlinarith
    linarith

/-- Woodford (2003), (E.7) and survey error 25 (**uniform cubic bound on the residual**): if
`|π_t| ≤ ε`, dispersion is uniformly `Δ ≤ K ε²` and the index error satisfies
`|dd_t| ≤ |1 − θ|(Δ_t + Δ_{t−1})`, then `|R63| ≤ (α/(1−α))(4|1−θ| K ε³ + 4(1−θ)² K² ε⁴)`,
uniformly in `t`. -/
theorem prop63_uniform {α θ ε K π dd Δ Δ' : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hπ : |π| ≤ ε) (hΔ : Δ ≤ K * ε ^ 2) (hΔ' : Δ' ≤ K * ε ^ 2)
    (hdd : |dd| ≤ |1 - θ| * (Δ' + Δ)) :
    |R63 α π dd| ≤ α / (1 - α) * (4 * |1 - θ| * K * ε ^ 3 + 4 * (1 - θ) ^ 2 * K ^ 2 * ε ^ 4) := by
  have hD : |dd| ≤ |1 - θ| * (2 * K * ε ^ 2) :=
    hdd.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  refine (R63_bound hα0 hα1 hD).trans ?_
  have hc : 0 ≤ α / (1 - α) := div_nonneg hα0 (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hK : 0 ≤ |1 - θ| * (2 * K * ε ^ 2) := (abs_nonneg _).trans hD
  have h1 : 2 * |π| * (|1 - θ| * (2 * K * ε ^ 2)) ≤ 2 * ε * (|1 - θ| * (2 * K * ε ^ 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hK
  have h2 : (|1 - θ| * (2 * K * ε ^ 2)) ^ 2 = 4 * (1 - θ) ^ 2 * K ^ 2 * ε ^ 4 := by
    rw [mul_pow, sq_abs]
    ring
  nlinarith

/-! ### Propositions 6.4 and 6.5: the discounted loss -/

/-- Woodford (2003), Prop. 6.4, p. 400: the factor
`Θ = ½ θ(1 + ωθ) α/((1−α)(1−αβ))` multiplying the loss (in units of `Ȳ u_c`). -/
noncomputable def ThetaCalvo (α β θ omega : ℝ) : ℝ :=
  θ * (1 + omega * θ) / 2 * (α / ((1 - α) * (1 - α * β)))

/-- Woodford (2003), Prop. 6.4: `Θ > 0` for `0 < α < 1`, `β < 1`, `θ > 0`, `1 + ωθ > 0`. -/
theorem ThetaCalvo_pos {α β θ omega : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hθ : 0 < θ) (hd : 0 < 1 + omega * θ) : 0 < ThetaCalvo α β θ omega := by
  unfold ThetaCalvo
  have : 0 < 1 - α := by linarith
  have : 0 < 1 - α * β := by nlinarith
  positivity

/-- Woodford (2003), eq. (2.22), p. 400 (**`λ = κ/θ` with `κ` of (2.19)**):
`Θ (κ/θ) = (σ⁻¹ + ω)/2`. -/
theorem calvo_weight {α β θ omega sinv : ℝ} (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0)
    (hαβ : 1 - α * β ≠ 0) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0) :
    ThetaCalvo α β θ omega * (calvoKappa α β omega θ sinv / θ) = (sinv + omega) / 2 := by
  have hd' : 1 + θ * omega ≠ 0 := by rwa [mul_comm]
  unfold ThetaCalvo calvoKappa
  rw [add_comm omega sinv]
  field_simp

/-- Woodford (2003), Props. 6.4–6.5, (2.21), p. 400 (**the discounted loss, Layer A, genuine
`tsum`s**). Suppose the dispersion recursion `Δ_t = α Δ_{t−1} + (α/(1−α)) qd_t² + R_t` (index
`t+1` is date `t`; `qd_t = π_t` for Prop. 6.4, `π_t − γπ_{t−1}` for Prop. 6.5) and period
welfare (in units of `Ȳ u_c`) `W_t = −½[(σ⁻¹+ω) X_t² + θ(1+ωθ) Δ_t] + tip_t + rem_t` (the form of
(2.13), `X_t = x_t − x*`), with all sequences bounded. Then `∑ βᵗ W_t` converges and equals
`−Θ ∑ βᵗ (qd_t² + (κ/θ) X_t²) + TIP + REM`, where
`TIP = ∑ βᵗ tip_t − ½θ(1+ωθ) α Δ_{−1}/(1−αβ)` depends only on exogenous terms and the initial
dispersion, and `REM = ∑ βᵗ rem_t − ½θ(1+ωθ)/(1−αβ) ∑ βᵗ R_t`. -/
theorem calvo_welfare_sum {α β θ omega sinv M : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0)
    {D qd X tip rem R W : ℕ → ℝ}
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * qd t ^ 2 + R t)
    (hW : ∀ t, W t = -(1 / 2) * ((sinv + omega) * X t ^ 2 + θ * (1 + omega * θ) * D (t + 1)) +
      tip t + rem t)
    (hqd : ∀ t, |qd t| ≤ M) (hX : ∀ t, |X t| ≤ M) (hR : ∀ t, |R t| ≤ M)
    (htip : ∀ t, |tip t| ≤ M) (hrem : ∀ t, |rem t| ≤ M) :
    HasSum (fun t => β ^ t * W t)
      (-ThetaCalvo α β θ omega *
          ∑' t, β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2) +
        (∑' t, β ^ t * tip t - θ * (1 + omega * θ) / 2 * (α * D 0 / (1 - α * β))) +
        (∑' t, β ^ t * rem t -
          θ * (1 + omega * θ) / 2 / (1 - α * β) * ∑' t, β ^ t * R t)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hX 0)
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hαβ : α * β < 1 := by nlinarith
  have hne1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - α * β ≠ 0 := by linarith
  have hq2 : ∀ t, |qd t ^ 2| ≤ M ^ 2 := fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hqd t) 2
  have hX2 : ∀ t, |X t ^ 2| ≤ M ^ 2 := fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hX t) 2
  have sq := (summable_norm_geom_bdd hβ hq2).of_norm
  have sX := (summable_norm_geom_bdd hβ hX2).of_norm
  have sR := (summable_norm_geom_bdd hβ hR).of_norm
  have stip := (summable_norm_geom_bdd hβ htip).of_norm
  have srem := (summable_norm_geom_bdd hβ hrem).of_norm
  -- the dispersion sum
  have hQ : ∀ t, |α / (1 - α) * qd t ^ 2 + R t| ≤ α / (1 - α) * M ^ 2 + M := fun t => by
    have hc : 0 ≤ α / (1 - α) := div_nonneg hα0.le (by linarith)
    have := abs_add_le (α / (1 - α) * qd t ^ 2) (R t)
    rw [abs_mul, abs_of_nonneg hc] at this
    have := mul_le_mul_of_nonneg_left (hq2 t) hc
    linarith [hR t]
  have hD := disp_discounted_hasSum (c := 1) (V := D) hα0.le hβ0 hαβ
    (q := fun t => α / (1 - α) * qd t ^ 2 + R t) (fun t => by rw [hrec t]; ring)
    (summable_norm_geom_bdd hβ hQ)
  have hQsum : ∑' t, β ^ t * (α / (1 - α) * qd t ^ 2 + R t) =
      α / (1 - α) * ∑' t, β ^ t * qd t ^ 2 + ∑' t, β ^ t * R t := by
    have : (fun t => β ^ t * (α / (1 - α) * qd t ^ 2 + R t)) =
        fun t => α / (1 - α) * (β ^ t * qd t ^ 2) + β ^ t * R t := by
      funext t; ring
    rw [this, (sq.mul_left _).tsum_add sR, tsum_mul_left]
  rw [hQsum] at hD
  -- assemble
  have hsum := ((((sX.hasSum.mul_left (-(1 / 2) * (sinv + omega))).add
    (hD.mul_left (-(1 / 2) * (θ * (1 + omega * θ))))).add stip.hasSum).add srem.hasSum)
  have hL : ∑' t, β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2) =
      ∑' t, β ^ t * qd t ^ 2 + calvoKappa α β omega θ sinv / θ * ∑' t, β ^ t * X t ^ 2 := by
    have : (fun t => β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2)) =
        fun t => β ^ t * qd t ^ 2 + calvoKappa α β omega θ sinv / θ * (β ^ t * X t ^ 2) := by
      funext t; ring
    rw [this, sq.tsum_add (sX.mul_left _), tsum_mul_left]
  rw [hL]
  convert hsum using 1
  · funext t
    rw [hW t]
    ring
  · unfold ThetaCalvo calvoKappa
    have hα : α ≠ 0 := hα0.ne'
    have hd' : 1 + θ * omega ≠ 0 := by rwa [mul_comm]
    field_simp
    ring

/-- Woodford (2003), **Proposition 6.4, eqs. (2.21)–(2.22), p. 400 (Layer A)**: with
`Δ_t = α Δ_{t−1} + (α/(1−α)) π_t² + R_t` ((2.20), `prop63_layerA`),
`∑ βᵗ W_t = −Θ ∑ βᵗ (π_t² + λ (x_t − x*)²) + TIP + REM` with `λ = κ/θ` (`calvo_weight`, `κ`
from (2.19)) and `Θ > 0` (`ThetaCalvo_pos`). -/
theorem prop64 {α β θ omega sinv M : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0)
    {D infl X tip rem R W : ℕ → ℝ}
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * infl (t + 1) ^ 2 + R t)
    (hW : ∀ t, W t = -(1 / 2) * ((sinv + omega) * X t ^ 2 + θ * (1 + omega * θ) * D (t + 1)) +
      tip t + rem t)
    (hinfl : ∀ t, |infl t| ≤ M) (hX : ∀ t, |X t| ≤ M) (hR : ∀ t, |R t| ≤ M)
    (htip : ∀ t, |tip t| ≤ M) (hrem : ∀ t, |rem t| ≤ M) :
    HasSum (fun t => β ^ t * W t)
      (-ThetaCalvo α β θ omega *
          ∑' t, β ^ t * (infl (t + 1) ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2) +
        (∑' t, β ^ t * tip t - θ * (1 + omega * θ) / 2 * (α * D 0 / (1 - α * β))) +
        (∑' t, β ^ t * rem t -
          θ * (1 + omega * θ) / 2 / (1 - α * β) * ∑' t, β ^ t * R t)) :=
  calvo_welfare_sum hα0 hα1 hβ0 hβ1 hθ hd hrec hW (fun t => hinfl (t + 1)) hX hR htip hrem

/-- Woodford (2003), (2.23)–(2.24), p. 402 (**Layer A**): with indexation of non-reset prices
to lagged inflation, `log p_t(i) = log p_{t−1}(i) + γ π_{t−1}`, one step of the cross-section
gives `Δ_t = α Δ_{t−1} + (α/(1−α))(π_t − γπ_{t−1})² + R63 α (π_t − γπ_{t−1}) dd` exactly, with
`|dd| ≤ |1 − θ|(Δ_t + Δ_{t−1})` (the special case `d = γ π_{t−1}` of `step_layerA`). -/
theorem index_layerA (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {α p θ γ πprev Bo Bn : ℝ} (hα : α ≠ 1) (hRm : μ.real R = 1 - α)
    {xo xn : G → ℝ} (hxo : Measurable xo) (hBo : ∀ i, |xo i - crossMean μ xo| ≤ Bo)
    (hBn : ∀ i, |xn i - crossMean μ xn| ≤ Bn) (hθ : θ ≠ 1) (hso : |1 - θ| * Bo ≤ 1)
    (hsn : |1 - θ| * Bn ≤ 1)
    (hrep1 : ∫ i in Rᶜ, xo i ∂μ = α * ∫ i, xo i ∂μ)
    (hrep2 : ∫ i in Rᶜ, xo i ^ 2 ∂μ = α * ∫ i, xo i ^ 2 ∂μ)
    (hn1 : ∀ i ∈ R, xn i = p) (hn2 : ∀ i ∉ R, xn i = xo i + γ * πprev) :
    ∃ dd : ℝ, crossVar μ xn = α * crossVar μ xo +
        α / (1 - α) * (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo - γ * πprev) ^ 2 +
        R63 α (logMeanExp μ (1 - θ) xn - logMeanExp μ (1 - θ) xo - γ * πprev) dd ∧
      |dd| ≤ |1 - θ| * (crossVar μ xn + crossVar μ xo) := by
  obtain ⟨h1, h2⟩ := step_layerA μ hR hα hRm hxo hBo hBn hθ hso hsn hrep1 hrep2 hn1 hn2
  exact ⟨_, h1, h2⟩

/-- Woodford (2003), **Proposition 6.5, eq. (2.25), p. 402 (Layer A)**: with indexation,
`Δ_t = α Δ_{t−1} + (α/(1−α))(π_t − γπ_{t−1})² + R_t` ((2.24), `index_layerA`; `infl 0 = π_{−1}`),
`∑ βᵗ W_t = −Θ ∑ βᵗ ((π_t − γπ_{t−1})² + λ (x_t − x*)²) + TIP + REM` with the same `λ = κ/θ`. -/
theorem prop65 {α β θ omega sinv γ M : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0)
    {D infl X tip rem R W : ℕ → ℝ}
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * (infl (t + 1) - γ * infl t) ^ 2 + R t)
    (hW : ∀ t, W t = -(1 / 2) * ((sinv + omega) * X t ^ 2 + θ * (1 + omega * θ) * D (t + 1)) +
      tip t + rem t)
    (hqd : ∀ t, |infl (t + 1) - γ * infl t| ≤ M) (hX : ∀ t, |X t| ≤ M) (hR : ∀ t, |R t| ≤ M)
    (htip : ∀ t, |tip t| ≤ M) (hrem : ∀ t, |rem t| ≤ M) :
    HasSum (fun t => β ^ t * W t)
      (-ThetaCalvo α β θ omega *
          ∑' t, β ^ t * ((infl (t + 1) - γ * infl t) ^ 2 +
            calvoKappa α β omega θ sinv / θ * X t ^ 2) +
        (∑' t, β ^ t * tip t - θ * (1 + omega * θ) / 2 * (α * D 0 / (1 - α * β))) +
        (∑' t, β ^ t * rem t -
          θ * (1 + omega * θ) / 2 / (1 - α * β) * ∑' t, β ^ t * R t)) :=
  calvo_welfare_sum hα0 hα1 hβ0 hβ1 hθ hd hrec hW hqd hX hR htip hrem

/-! ### Footnote 26 and Table 6.1 -/

/-- Woodford (2003), fn. 26, p. 401, and Table 6.1, p. 431: with `κ = .024` and `θ = 7.88`,
the weight on the gap relative to annualised inflation is `16κ/θ = 0.04873…`, "on the order of
.05" (and reported as `0.048` in Table 6.1). -/
theorem fn26_value : (0.0487 : ℝ) < 16 * 0.024 / 7.88 ∧ 16 * (0.024 : ℝ) / 7.88 < 0.0488 := by
  constructor <;> norm_num

/-- Woodford (2003), Table 6.1, p. 431 (**consistency of `κ = .024` with `θ = 7.88`**): with
`α = .66`, `β = .99`, `σ⁻¹ + ω = .63`, `σ⁻¹ = .16` (so `ω = .47`), formula (2.19) gives
`κ ∈ (.0239, .0240)` at `θ = 7.88`, which rounds to the tabulated `.024`. -/
theorem fn26_kappa_consistent :
    (0.0239 : ℝ) < calvoKappa 0.66 0.99 0.47 7.88 0.16 ∧
      calvoKappa 0.66 0.99 0.47 7.88 0.16 < 0.0240 := by
  unfold calvoKappa
  constructor <;> norm_num

end Woodford.StabilizationWelfare.PriceDispersion
