/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Predetermined

/-!
# Strategic complementarity in pricesetting

Woodford (2003), *Interest and Prices*, Chapter 3, §1.3 (pp. 161–163: the notional
short-run aggregate-supply curve and strategic complementarity) and §1.4 "Sources of strategic
complementarity" (pp. 163–173), including Proposition 3.3 and Table 3.1.

The notional SRAS curve is the implicit solution `x(Ŷ)` (log relative price of an industry as a
function of aggregate output) of the log of the desired-price condition (1.39),
`x = log(µ(y/Y)/µ(1)) + log(µ s(y, Y))`, with log demand `ŷ = Ŷ + d(x)`. Its elasticity `ζ` is
obtained as an exact derivative at the steady state: any differentiable solution has slope `ζ`
(`notional_sras_slope`), and by the implicit function theorem a unique local solution exists
(`notional_sras_exists`). The primitives are the elasticities: `ε_µ = m'(0)` of the desired
markup, `−θ = d'(0)` of demand, and `s_y, s_Y`, the partial elasticities of real marginal cost.

## Main results

* `notional_sras_general` ((1.34), from the general `Π₁` formalism of Assumption 3.1) and
  `sras_gap_form`: the notional SRAS is `log(p^I/P) = ζ (Ŷ − Ŷⁿ)`.
* `best_response_hasDerivAt`, `strategic_complements_iff`, `strategic_substitutes_iff`:
  `∂ log p^I/∂ log P = 1 − ζ` with nominal spending fixed; complements iff `ζ < 1`.
* `notional_sras_slope`, `notional_sras_exists`: (1.40)–(1.41),
  `ζ = (s_y + s_Y)/(1 + θ(ε_µ + s_y))`.
* Sources: `specific_factor_elasticities` ((1.15)–(1.16): `ω = ω_w + ω_p`, `σ⁻¹`),
  `common_labour_elasticities` (`ω_p`, `ω_w + σ⁻¹`), `homogeneous_factor_elasticities`
  (`0`, `ω + σ⁻¹`), `intermediate_input_elasticities` ((B.8): factor `1 − µ s_m`).
* `zeta_1_35`, `zeta_lt_one_linear_utility`, `zeta_homogeneous`, `zeta_homogeneous_gt_one`,
  `zeta_1_37`, `zeta_1_37_between` and the Chari et al. numbers.
* `zetaGen_strictAntiOn_markup`, `zetaGen_tendsto_zero_markup`, `bergin_feenstra`,
  `bergin_feenstra_passthrough_half`, Kimball special cases.
* `prop_3_3_formula`, `prop_3_3` (Proposition 3.3, (1.43)), `zeta33_tendsto_zero`,
  `zeta33_homogeneous_factor`, footnote 23, and **Table 3.1** (`table31_row1`–`table31_row4`
  exact values, `table31_rounding` agreement with every printed entry to two decimals).
-/

namespace Woodford.NominalRigidities.StrategicComplementarity

open Filter Topology

/-! ### (1.34): the notional SRAS in the general formalism -/

/-- Woodford (2003), eq. (1.34), p. 162: the notional SRAS curve is defined by
`Π₁(p^I, p^I, P; Y, ξ̃) = 0`. With `J((v, Ŷ), x) = Π₁(e^x, e^x, 1; Ȳ e^Ŷ, ξ̃(v))`, `x = log(p^I/P)`,
strictly differentiable at the steady state with derivative `ψ_p x + g v + ψ_y Ŷ`, `ψ_p ≠ 0`, and
the natural rate satisfying `g = −ψ_y Ŷⁿ'(0)` (`Predetermined.linearisation_gap_form`), the curve
exists locally, is unique, and has derivative `ζ (Ŷ − Ŷⁿ'(0) v)` with `ζ = −ψ_y/ψ_p`. -/
theorem notional_sras_general {J : (ℝ × ℝ) × ℝ → ℝ} {L : (ℝ × ℝ) × ℝ →L[ℝ] ℝ}
    {ψp g ψy n' : ℝ} (hJ : HasStrictFDerivAt J L 0)
    (hL : ∀ q, L q = ψp * q.2 + g * q.1.1 + ψy * q.1.2) (hψp : ψp ≠ 0) (hg : g = -ψy * n') :
    ∃ x : ℝ × ℝ → ℝ, x 0 = 0 ∧ (∀ᶠ w in 𝓝 0, J (w, x w) = J 0) ∧
      (∀ᶠ q in 𝓝 0, J q = J 0 ↔ x q.1 = q.2) ∧
      ∀ L' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt x L' 0 →
        ∀ v y, L' (v, y) = (-ψy / ψp) * (y - n' * v) := by
  have hc : L (0, 1) ≠ 0 := by rw [hL]; simpa using hψp
  obtain ⟨x, h1, h2, h3, h4⟩ := Predetermined.implicit_function_scalar hJ hc
  refine ⟨x, by simpa using h1, by simpa using h2, by simpa using h3, fun L' hL' v y => ?_⟩
  rw [hL'.unique h4.hasFDerivAt]
  simp [hL, hg]
  field_simp
  ring

/-- Woodford (2003), eq. (1.34), p. 162 (with shocks): if the notional SRAS `x(v, Ŷ)` has
derivative `L(v, Ŷ) = c v + ζ Ŷ` at the steady state and the natural rate `Ŷⁿ(v)` is where the
desired relative price is one, `x(v, Ŷⁿ(v)) = 0`, then `L(v, Ŷ) = ζ (Ŷ − Ŷⁿ'(0) v)`: to first
order `log(p^I/P) = ζ (Ŷ − Ŷⁿ)`. -/
theorem sras_gap_form {x : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {c ζ n' : ℝ} {n : ℝ → ℝ}
    (hx : HasFDerivAt x L 0) (hL : ∀ q, L q = c * q.1 + ζ * q.2) (hζ : ζ ≠ 0)
    (hn : HasDerivAt n n' 0) (hn0 : n 0 = 0) (hzero : ∀ᶠ v in 𝓝 0, x (v, n v) = 0) :
    ∀ v y, L (v, y) = ζ * (y - n' * v) :=
  (Predetermined.linearisation_gap_form hx hL hζ hn hn0 hzero).2

/-! ### Best responses and strategic complementarity (pp. 161–162) -/

/-- Woodford (2003), p. 162: the best response of an industry, obtained by substituting
`Y = 𝒴/P` into the notional SRAS: `log p^I = log P + x(log 𝒴 − log P − log Ȳ)`. If the notional
SRAS has slope `ζ`, the best response has slope `∂ log p^I/∂ log P = 1 − ζ`. -/
theorem best_response_hasDerivAt {x : ℝ → ℝ} {ζ lN lYbar lP : ℝ}
    (hx : HasDerivAt x ζ (lN - lP - lYbar)) :
    HasDerivAt (fun q => q + x (lN - q - lYbar)) (1 - ζ) lP := by
  have hin : HasDerivAt (fun q : ℝ => lN - q - lYbar) (-1) lP := by
    simpa using ((hasDerivAt_id lP).const_sub lN).sub_const lYbar
  have h2 : HasDerivAt (fun q => x (lN - q - lYbar)) (ζ * -1) lP := hx.comp lP hin
  have := (hasDerivAt_id' lP).add h2
  convert this using 1
  ring

/-- Woodford (2003), p. 162: pricing decisions are strategic complements (the best response
increases with the other prices) if and only if `ζ < 1`. -/
theorem strategic_complements_iff (ζ : ℝ) : 0 < 1 - ζ ↔ ζ < 1 := sub_pos

/-- Woodford (2003), p. 162: pricing decisions are strategic substitutes (the best response
decreases with the other prices) if and only if `ζ > 1`. -/
theorem strategic_substitutes_iff (ζ : ℝ) : 1 - ζ < 0 ↔ 1 < ζ := sub_neg

/-! ### (1.40)–(1.41): the elasticity of the notional SRAS -/

/-- Woodford (2003), eq. (1.41), p. 169: `ζ = (s_y + s_Y)/(1 + θ(ε_µ + s_y))`. -/
noncomputable def zetaGen (θ εμ sy sY : ℝ) : ℝ := (sy + sY) / (1 + θ * (εμ + sy))

/-- Woodford (2003), (1.39)–(1.40), p. 168: the log of the desired-price condition in deviations,
`F(Ŷ, x) = x − m(d(x)) − ŝ(Ŷ + d(x), Ŷ)`, where `x = log(p/P)`, `d` is log relative demand
(`ŷ − Ŷ = d(x)`), `m(u) = log(µ(eᵘ)/µ(1))` the log desired markup and
`ŝ(a, b) = log(µ s(Ȳ eᵃ, Ȳ eᵇ))` log real marginal cost. The notional SRAS is `F = 0`. -/
noncomputable def sras (m d : ℝ → ℝ) (shat : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  q.2 - m (d q.2) - shat (q.1 + d q.2, q.1)

/-- Woodford (2003), eqs. (1.40)–(1.41), pp. 168–169: if `m'(0) = ε_µ`, `d'(0) = −θ`, `ŝ` has
partial elasticities `s_y, s_Y` at the steady state and `1 + θ(ε_µ + s_y) ≠ 0`, then every
notional SRAS curve `x(Ŷ)` differentiable at `0` with `x(0) = 0` has slope
`ζ = (s_y + s_Y)/(1 + θ(ε_µ + s_y))`. -/
theorem notional_sras_slope {m d x : ℝ → ℝ} {shat : ℝ × ℝ → ℝ} {S : ℝ × ℝ →L[ℝ] ℝ}
    {θ εμ sy sY x' : ℝ} (hm : HasDerivAt m εμ 0) (hd : HasDerivAt d (-θ) 0) (hd0 : d 0 = 0)
    (hs : HasFDerivAt shat S 0) (hS : ∀ q, S q = sy * q.1 + sY * q.2)
    (hden : 1 + θ * (εμ + sy) ≠ 0) (hx : HasDerivAt x x' 0) (hx0 : x 0 = 0)
    (hsol : ∀ᶠ y in 𝓝 0, sras m d shat (y, x y) = 0) :
    x' = zetaGen θ εμ sy sY := by
  have hdx : HasDerivAt (fun y => d (x y)) (-θ * x') 0 := by
    have hd' : HasDerivAt d (-θ) (x 0) := by rw [hx0]; exact hd
    exact (hd'.comp 0 hx).congr_deriv (by ring)
  have hdx0 : d (x 0) = 0 := by rw [hx0, hd0]
  have hmx : HasDerivAt (fun y => m (d (x y))) (εμ * (-θ * x')) 0 := by
    have hm' : HasDerivAt m εμ (d (x 0)) := by rw [hdx0]; exact hm
    exact (hm'.comp 0 hdx).congr_deriv (by ring)
  have hpath : HasDerivAt (fun y => ((y + d (x y), y) : ℝ × ℝ)) ((1 + -θ * x'), (1 : ℝ)) 0 :=
    ((hasDerivAt_id 0).add hdx).prodMk (hasDerivAt_id 0)
  have hs' : HasFDerivAt shat S ((0 : ℝ) + d (x 0), (0 : ℝ)) := by
    rw [hdx0, zero_add]; exact hs
  have hsc := HasFDerivAt.comp_hasDerivAt (f := fun y => ((y + d (x y), y) : ℝ × ℝ)) 0 hs'
    hpath
  have hF := (hx.sub hmx).sub hsc
  have h0 : HasDerivAt (fun y => sras m d shat (y, x y)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hsol
  have hu := hF.unique h0
  rw [hS] at hu
  simp only at hu
  unfold zetaGen
  field_simp
  linear_combination hu

/-- Woodford (2003), eqs. (1.40)–(1.41), pp. 168–169 (existence): under strict differentiability
of `m`, `d` and `ŝ` at the steady state (`d(0) = 0`, `m(0) = ŝ(0) = 0`) and
`1 + θ(ε_µ + s_y) ≠ 0`, the notional SRAS `x(Ŷ)` exists near `Ŷ = 0`, is the unique local
solution, and has strict derivative `ζ = zetaGen θ ε_µ s_y s_Y` at `0`. -/
theorem notional_sras_exists {m d : ℝ → ℝ} {shat : ℝ × ℝ → ℝ} {S : ℝ × ℝ →L[ℝ] ℝ}
    {θ εμ sy sY : ℝ} (hm : HasStrictDerivAt m εμ 0) (hd : HasStrictDerivAt d (-θ) 0)
    (hd0 : d 0 = 0) (hm0 : m 0 = 0) (hs : HasStrictFDerivAt shat S 0) (hs0 : shat 0 = 0)
    (hS : ∀ q, S q = sy * q.1 + sY * q.2) (hden : 1 + θ * (εμ + sy) ≠ 0) :
    ∃ x : ℝ → ℝ, x 0 = 0 ∧ (∀ᶠ y in 𝓝 0, sras m d shat (y, x y) = 0) ∧
      (∀ᶠ q in 𝓝 (0 : ℝ × ℝ), sras m d shat q = 0 ↔ x q.1 = q.2) ∧
      HasStrictDerivAt x (zetaGen θ εμ sy sY) 0 := by
  have hd2 : HasStrictFDerivAt (fun q : ℝ × ℝ => d q.2)
      ((-θ) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) hd hasStrictFDerivAt_snd rfl
  have hmd : HasStrictFDerivAt (fun q : ℝ × ℝ => m (d q.2))
      (εμ • ((-θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) hm hd2 (by simp [hd0])
  have hpath : HasStrictFDerivAt (fun q : ℝ × ℝ => ((q.1 + d q.2, q.1) : ℝ × ℝ))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ + (-θ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) 0 :=
    (hasStrictFDerivAt_fst.add hd2).prodMk hasStrictFDerivAt_fst
  have hs' : HasStrictFDerivAt shat S
      ((fun q : ℝ × ℝ => ((q.1 + d q.2, q.1) : ℝ × ℝ)) 0) := by
    change HasStrictFDerivAt shat S ((0 : ℝ) + d 0, (0 : ℝ))
    rw [hd0, zero_add]
    exact hs
  have hsc := hs'.comp (x := (0 : ℝ × ℝ)) hpath
  have hF := (hasStrictFDerivAt_snd.sub hmd).sub hsc
  have hs0' : shat ((0 : ℝ), (0 : ℝ)) = 0 := hs0
  have hF0 : sras m d shat 0 = 0 := by simp [sras, hd0, hm0, hs0']
  set L' : ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ - εμ • ((-θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) -
      S.comp ((ContinuousLinearMap.fst ℝ ℝ ℝ + (-θ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) with hL'
  have v01 : L' (0, 1) = 1 + θ * (εμ + sy) := by
    simp [hL', hS]; ring
  have v10 : L' (1, 0) = -(sy + sY) := by
    simp [hL', hS]
  have hF' : HasStrictFDerivAt (sras m d shat) L' 0 := hF
  obtain ⟨x, h1, h2, h3, h4⟩ := Predetermined.implicit_function_real hF' (by rw [v01]; exact hden)
  simp only [Prod.fst_zero, Prod.snd_zero, hF0] at h1 h2 h3 h4
  refine ⟨x, h1, h2, h3, ?_⟩
  convert h4 using 1
  rw [v01, v10]
  unfold zetaGen
  ring

/-! ### Sources of strategic complementarity: exact elasticity computations -/

/-- Woodford (2003), eqs. (1.10), (1.15)–(1.16), pp. 149–153 (specific factor markets): real
marginal cost `s(y, Y) = W(y) Ψ(y)/Λ(Y)` (real wage demand, inverse marginal product, marginal
utility of income). If the log elasticities at `Ȳ` are `ω_w`, `ω_p` and `−σ⁻¹`, then
`ŝ(a, b) = log s(Ȳ eᵃ, Ȳ eᵇ) − log s(Ȳ, Ȳ)` has strict derivative `(ω_w + ω_p) a + σ⁻¹ b`:
`s_y = ω = ω_w + ω_p` and `s_Y = σ⁻¹`. -/
theorem specific_factor_elasticities {W Ψ Λ : ℝ → ℝ} {Ybar ωw ωp σinv : ℝ} (hY : 0 < Ybar)
    (hW : ∀ y, 0 < y → 0 < W y) (hΨ : ∀ y, 0 < y → 0 < Ψ y) (hΛ : ∀ y, 0 < y → 0 < Λ y)
    (dW : HasStrictDerivAt (fun a => Real.log (W (Ybar * Real.exp a))) ωw 0)
    (dΨ : HasStrictDerivAt (fun a => Real.log (Ψ (Ybar * Real.exp a))) ωp 0)
    (dΛ : HasStrictDerivAt (fun a => Real.log (Λ (Ybar * Real.exp a))) (-σinv) 0) :
    HasStrictFDerivAt
      (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.1) * Ψ (Ybar * Real.exp q.1) /
          Λ (Ybar * Real.exp q.2)) - Real.log (W Ybar * Ψ Ybar / Λ Ybar))
      ((ωw + ωp) • ContinuousLinearMap.fst ℝ ℝ ℝ + σinv • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  have hp : ∀ a, 0 < Ybar * Real.exp a := fun a => mul_pos hY (Real.exp_pos a)
  have e : (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.1) * Ψ (Ybar * Real.exp q.1) /
      Λ (Ybar * Real.exp q.2)) - Real.log (W Ybar * Ψ Ybar / Λ Ybar)) =
      fun q => (Real.log (W (Ybar * Real.exp q.1)) + Real.log (Ψ (Ybar * Real.exp q.1)) -
        Real.log (Λ (Ybar * Real.exp q.2))) - Real.log (W Ybar * Ψ Ybar / Λ Ybar) := by
    funext q
    rw [Real.log_div (mul_pos (hW _ (hp _)) (hΨ _ (hp _))).ne' (hΛ _ (hp _)).ne',
      Real.log_mul (hW _ (hp _)).ne' (hΨ _ (hp _)).ne']
  rw [e]
  have h1 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.1)))
      (ωw • ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dW hasStrictFDerivAt_fst rfl
  have h2 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (Ψ (Ybar * Real.exp q.1)))
      (ωp • ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dΨ hasStrictFDerivAt_fst rfl
  have h3 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (Λ (Ybar * Real.exp q.2)))
      ((-σinv) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dΛ hasStrictFDerivAt_snd rfl
  have := ((h1.add h2).sub h3).sub_const (Real.log (W Ybar * Ψ Ybar / Λ Ybar))
  convert this using 1
  ext <;> simp

/-- Woodford (2003), p. 167 (common labour market, firm-specific capital): real marginal cost
`s(y, Y) = w(Y) Ψ(y)/Λ(Y)` with the economy-wide real wage demand `w(Y)` (elasticity `ω_w`):
`ŝ` has strict derivative `ω_p a + (ω_w + σ⁻¹) b`, i.e. `s_y = ω_p`, `s_Y = ω_w + σ⁻¹`. -/
theorem common_labour_elasticities {W Ψ Λ : ℝ → ℝ} {Ybar ωw ωp σinv : ℝ} (hY : 0 < Ybar)
    (hW : ∀ y, 0 < y → 0 < W y) (hΨ : ∀ y, 0 < y → 0 < Ψ y) (hΛ : ∀ y, 0 < y → 0 < Λ y)
    (dW : HasStrictDerivAt (fun a => Real.log (W (Ybar * Real.exp a))) ωw 0)
    (dΨ : HasStrictDerivAt (fun a => Real.log (Ψ (Ybar * Real.exp a))) ωp 0)
    (dΛ : HasStrictDerivAt (fun a => Real.log (Λ (Ybar * Real.exp a))) (-σinv) 0) :
    HasStrictFDerivAt
      (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.2) * Ψ (Ybar * Real.exp q.1) /
          Λ (Ybar * Real.exp q.2)) - Real.log (W Ybar * Ψ Ybar / Λ Ybar))
      (ωp • ContinuousLinearMap.fst ℝ ℝ ℝ + (ωw + σinv) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  have hp : ∀ a, 0 < Ybar * Real.exp a := fun a => mul_pos hY (Real.exp_pos a)
  have e : (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.2) * Ψ (Ybar * Real.exp q.1) /
      Λ (Ybar * Real.exp q.2)) - Real.log (W Ybar * Ψ Ybar / Λ Ybar)) =
      fun q => (Real.log (W (Ybar * Real.exp q.2)) + Real.log (Ψ (Ybar * Real.exp q.1)) -
        Real.log (Λ (Ybar * Real.exp q.2))) - Real.log (W Ybar * Ψ Ybar / Λ Ybar) := by
    funext q
    rw [Real.log_div (mul_pos (hW _ (hp _)) (hΨ _ (hp _))).ne' (hΛ _ (hp _)).ne',
      Real.log_mul (hW _ (hp _)).ne' (hΨ _ (hp _)).ne']
  rw [e]
  have h1 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (W (Ybar * Real.exp q.2)))
      (ωw • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dW hasStrictFDerivAt_snd rfl
  have h2 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (Ψ (Ybar * Real.exp q.1)))
      (ωp • ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dΨ hasStrictFDerivAt_fst rfl
  have h3 : HasStrictFDerivAt (fun q : ℝ × ℝ => Real.log (Λ (Ybar * Real.exp q.2)))
      ((-σinv) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
    HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : ℝ × ℝ) dΛ hasStrictFDerivAt_snd rfl
  have := ((h1.add h2).sub h3).sub_const (Real.log (W Ybar * Ψ Ybar / Λ Ybar))
  convert this using 1
  ext <;> simp

/-- Woodford (2003), p. 165 (homogeneous factor markets): marginal cost `S = P s(X, Y)` is common
to all firms, with `X = Y` along symmetric allocations, so `ŝ(a, b) = ŝ₀(b, b)` does not depend on
own output: if `ŝ₀` has partial elasticities `ω` and `σ⁻¹`, then `s_y = 0` and `s_Y = ω + σ⁻¹`. -/
theorem homogeneous_factor_elasticities {shat0 : ℝ × ℝ → ℝ} {S0 : ℝ × ℝ →L[ℝ] ℝ} {ω σinv : ℝ}
    (hs : HasStrictFDerivAt shat0 S0 0) (hS : ∀ q, S0 q = ω * q.1 + σinv * q.2) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => shat0 (q.2, q.2))
      ((ω + σinv) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  have hpath : HasStrictFDerivAt (fun q : ℝ × ℝ => ((q.2, q.2) : ℝ × ℝ))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 :=
    hasStrictFDerivAt_snd.prodMk hasStrictFDerivAt_snd
  have hs' : HasStrictFDerivAt shat0 S0 ((fun q : ℝ × ℝ => ((q.2, q.2) : ℝ × ℝ)) 0) := by
    change HasStrictFDerivAt shat0 S0 ((0 : ℝ), (0 : ℝ))
    exact hs
  have := hs'.comp (x := (0 : ℝ × ℝ)) hpath
  convert this using 1
  ext <;> simp [hS]

/-- Woodford (2003), eq. (B.8), p. 657, and p. 658 (intermediate inputs): gross-output real
marginal cost is `s = (1 − s_m) s^{VA} + s_m`. If `s^{VA} = s̄^{VA} e^{ℓ}` with the steady-state
value (B.9) `s̄^{VA} = (1 − µ s_m)/(µ(1 − s_m))` and `ℓ` (log VA marginal cost) has strict
derivative `Lℓ` (partial elasticities `s_y, s_Y`), then `ŝ = log(µ s)` vanishes at the steady
state and has strict derivative `(1 − µ s_m) Lℓ`, i.e. `(1 − µ s_m)(s_y a + s_Y b)`:
"log-linearization of (B.8)". Needs `s_m ≠ 1`, `µ ≠ 0`. -/
theorem intermediate_input_elasticities {ell : ℝ × ℝ → ℝ} {Lℓ : ℝ × ℝ →L[ℝ] ℝ}
    {μ sm : ℝ} (hμ : μ ≠ 0) (hsm : sm ≠ 1)
    (hℓ : HasStrictFDerivAt ell Lℓ 0) (hℓ0 : ell 0 = 0) :
    Real.log (μ * ((1 - sm) * ((1 - μ * sm) / (μ * (1 - sm)) * Real.exp (ell 0)) + sm)) = 0 ∧
    HasStrictFDerivAt
      (fun q => Real.log (μ * ((1 - sm) * ((1 - μ * sm) / (μ * (1 - sm)) *
        Real.exp (ell q)) + sm)))
      ((1 - μ * sm) • Lℓ) 0 := by
  have h1sm : (1 : ℝ) - sm ≠ 0 := sub_ne_zero.mpr (Ne.symm hsm)
  have hval : μ * ((1 - sm) * ((1 - μ * sm) / (μ * (1 - sm)) * Real.exp (ell 0)) + sm) = 1 := by
    rw [hℓ0, Real.exp_zero]
    field_simp
    ring
  refine ⟨by rw [hval, Real.log_one], ?_⟩
  have hin := ((hℓ.exp.const_mul ((1 - μ * sm) / (μ * (1 - sm)))).const_mul (1 - sm)).add_const
    sm |>.const_mul μ
  have hlog := hin.log (by rw [hval]; exact one_ne_zero)
  convert hlog using 1
  rw [hval, hℓ0, Real.exp_zero]
  simp only [inv_one, one_smul, smul_smul]
  congr 1
  field_simp

/-! ### The elasticity `ζ` in the special cases of §1.4 -/

/-- Woodford (2003), eq. (1.35), p. 164 (specific factor markets, Dixit–Stiglitz):
`s_y = ω`, `s_Y = σ⁻¹`, `ε_µ = 0` give `ζ = (ω + σ⁻¹)/(1 + ωθ)`. -/
theorem zeta_1_35 (θ ω σinv : ℝ) : zetaGen θ 0 ω σinv = (ω + σinv) / (1 + ω * θ) := by
  unfold zetaGen; ring_nf

/-- Woodford (2003), p. 164: (1.35) is positive for `ω, σ⁻¹ > 0`, `θ > 1`. -/
theorem zeta_1_35_pos {θ ω σinv : ℝ} (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σinv) :
    0 < zetaGen θ 0 ω σinv := by
  rw [zeta_1_35]; apply div_pos <;> nlinarith

/-- Woodford (2003), p. 164: with linear utility (`σ⁻¹ = 0`) and `θ > 1`,
`ζ = ω/(1 + ωθ) < 1`: pricing decisions are necessarily strategic complements. -/
theorem zeta_lt_one_linear_utility {θ ω : ℝ} (hθ : 1 < θ) (hω : 0 < ω) : zetaGen θ 0 ω 0 < 1 := by
  rw [zeta_1_35, add_zero, div_lt_one (by nlinarith)]
  nlinarith

/-- Woodford (2003), p. 165 (homogeneous factor markets): `s_y = 0`, `s_Y = ω + σ⁻¹`,
`ε_µ = 0` give `ζ = ω + σ⁻¹`. -/
theorem zeta_homogeneous (θ ω σinv : ℝ) : zetaGen θ 0 0 (ω + σinv) = ω + σinv := by
  unfold zetaGen; simp

/-- Woodford (2003), p. 165: with homogeneous factor markets and `σ = 1`, `ζ = ω + 1 > 1` for
every `ω > 0`: strategic substitutes. -/
theorem zeta_homogeneous_gt_one (θ : ℝ) {ω : ℝ} (hω : 0 < ω) : 1 < zetaGen θ 0 0 (ω + 1) := by
  rw [zeta_homogeneous]; linarith

/-- Woodford (2003), p. 166 (Chari et al. 2000, `ω = 1.25`, `σ = 1`, `θ = 10`): `ζ = 2.25` with
homogeneous factor markets, `ζ = 1.25` if also `σ⁻¹ = 0`, and `ζ = 1/6 ≈ 0.17` with specific
factor markets. -/
theorem chari_numbers :
    zetaGen 10 0 0 ((5 / 4 : ℝ) + 1) = 9 / 4 ∧ zetaGen 10 0 0 ((5 / 4 : ℝ) + 0) = 5 / 4 ∧
      zetaGen 10 0 (5 / 4) 1 = 1 / 6 ∧ |(1 / 6 : ℝ) - 0.17| < 0.005 := by
  unfold zetaGen; norm_num [abs_lt]

/-- Woodford (2003), eq. (1.37), p. 167 (common labour, specific capital): `s_y = ω_p`,
`s_Y = ω_w + σ⁻¹` give `ζ = (ω + σ⁻¹)/(1 + ω_p θ)` with `ω = ω_w + ω_p`. -/
theorem zeta_1_37 (θ ωw ωp σinv : ℝ) :
    zetaGen θ 0 ωp (ωw + σinv) = (ωw + ωp + σinv) / (1 + ωp * θ) := by
  unfold zetaGen; ring_nf

/-- Woodford (2003), p. 167: (1.37) lies strictly between (1.35) and the homogeneous-markets
value `ω + σ⁻¹`, given `ω_w > 0` (finite Frisch elasticity), `ω_p > 0` and `θ > 0`. -/
theorem zeta_1_37_between {θ ωw ωp σinv : ℝ} (hθ : 0 < θ) (hw : 0 < ωw) (hp : 0 < ωp)
    (hσ : 0 ≤ σinv) :
    zetaGen θ 0 (ωw + ωp) σinv < zetaGen θ 0 ωp (ωw + σinv) ∧
      zetaGen θ 0 ωp (ωw + σinv) < ωw + ωp + σinv := by
  rw [zeta_1_37, zeta_1_35]
  have h1 : 0 < 1 + ωp * θ := by positivity
  have h2 : 0 < 1 + (ωw + ωp) * θ := by positivity
  have hn : 0 < ωw + ωp + σinv := by linarith
  constructor
  · exact div_lt_div_of_pos_left hn h1 (by nlinarith [mul_pos hw hθ])
  · exact div_lt_self hn (by nlinarith [mul_pos hp hθ])

/-- Woodford (2003), p. 167: with the Chari et al. values (`ω_p = 0.5`, `ω_w = 0.75`, `σ = 1`,
`θ = 10`) (1.37) gives `ζ = 0.375 ≈ 0.38`. -/
theorem chari_common_labour : zetaGen 10 0 (1 / 2) ((3 / 4 : ℝ) + 1) = 3 / 8 ∧
    |(3 / 8 : ℝ) - 0.38| ≤ 0.005 := by
  unfold zetaGen; norm_num [abs_le]

/-- Woodford (2003), p. 169: "a positive ε_µ lowers the value of ζ": for `θ > 0`, `s_y ≥ 0`
and `s_y + s_Y > 0`, `ζ` is strictly decreasing in `ε_µ ≥ 0`. -/
theorem zetaGen_strictAntiOn_markup {θ sy sY : ℝ} (hθ : 0 < θ) (hsy : 0 ≤ sy)
    (hs : 0 < sy + sY) : StrictAntiOn (fun ε => zetaGen θ ε sy sY) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold zetaGen
  apply div_lt_div_of_pos_left hs (by positivity)
  nlinarith

/-- Woodford (2003), p. 169: "ζ → 0 as ε_µ → ∞" (for `θ > 0`). -/
theorem zetaGen_tendsto_zero_markup {θ sy sY : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => zetaGen θ ε sy sY) atTop (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => 1 + θ * (ε + sy)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Tendsto.const_mul_atTop hθ
    exact tendsto_atTop_add_const_right _ sy tendsto_id
  exact Tendsto.div_atTop tendsto_const_nhds h

/-- Woodford (2003), p. 169 (Bergin and Feenstra): the desired price `log p` solves
`log p = m(d(log p − log P)) + log S`. With `m'(0) = ε_µ`, `d'(0) = −θ` (strict) and
`1 + θ ε_µ ≠ 0`, it is locally a unique function of `(log S, log P)` with derivative
`(log S, log P) ↦ (log S + θ ε_µ log P)/(1 + θ ε_µ)`. -/
theorem bergin_feenstra {m d : ℝ → ℝ} {θ εμ : ℝ} (hm : HasStrictDerivAt m εμ 0)
    (hd : HasStrictDerivAt d (-θ) 0) (hd0 : d 0 = 0) (hm0 : m 0 = 0)
    (hden : 1 + θ * εμ ≠ 0) :
    ∃ lp : ℝ × ℝ → ℝ, lp 0 = 0 ∧
      (∀ᶠ w in 𝓝 0, lp w = m (d (lp w - w.2)) + w.1) ∧
      ∀ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt lp L 0 →
        ∀ a b, L (a, b) = (a + θ * εμ * b) / (1 + θ * εμ) := by
  set f : (ℝ × ℝ) × ℝ → ℝ := fun q => q.2 - m (d (q.2 - q.1.2)) - q.1.1
  have hlin : HasStrictFDerivAt (fun q : (ℝ × ℝ) × ℝ => q.2 - q.1.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)) 0 :=
    hasStrictFDerivAt_snd.sub (hasStrictFDerivAt_snd.comp (x := (0 : (ℝ × ℝ) × ℝ))
      hasStrictFDerivAt_fst)
  have hd2 := HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : (ℝ × ℝ) × ℝ) hd hlin
    (by simp)
  have hmd := HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq (0 : (ℝ × ℝ) × ℝ) hm hd2
    (by simp [hd0])
  have h11 : HasStrictFDerivAt (fun q : (ℝ × ℝ) × ℝ => q.1.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)) 0 :=
    hasStrictFDerivAt_fst.comp (x := (0 : (ℝ × ℝ) × ℝ)) hasStrictFDerivAt_fst
  set L' : (ℝ × ℝ) × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ - εμ • (-θ) •
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)) -
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) with hL'
  have hf : HasStrictFDerivAt f L' 0 := (hasStrictFDerivAt_snd.sub hmd).sub h11
  have v01 : L' (0, 1) = 1 + θ * εμ := by simp [hL']; ring
  have vab : ∀ a b : ℝ, L' ((a, b), 0) = -(a + θ * εμ * b) := fun a b => by simp [hL']; ring
  obtain ⟨lp, h1, h2, -, h4⟩ := Predetermined.implicit_function_scalar hf
    (by rw [v01]; exact hden)
  have hf0 : f 0 = 0 := by simp [f, hd0, hm0]
  refine ⟨lp, by simpa using h1, ?_, fun L hL a b => ?_⟩
  · filter_upwards [h2] with w hw
    rw [hf0] at hw
    simp only [f] at hw
    linarith
  · rw [hL.unique h4.hasFDerivAt]
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, v01, vab]
    field_simp

/-- Woodford (2003), p. 169: with `θ ε_µ = 1` (Bergin and Feenstra's calibration), the
elasticity of the desired price with respect to marginal cost is `1/(1 + θ ε_µ) = 1/2`, matching
pass-through of about 0.5. -/
theorem bergin_feenstra_passthrough_half {θ εμ : ℝ} (h : θ * εμ = 1) :
    1 / (1 + θ * εμ) = 1 / 2 ∧ θ * εμ / (1 + θ * εμ) = 1 / 2 := by
  rw [h]; norm_num

/-- Woodford (2003), p. 169: with Kimball preferences and homogeneous factor markets
(`s_y = 0`, `s_Y = ω + σ⁻¹`), `ζ = (ω + σ⁻¹)/(1 + θ ε_µ)`; `θ ε_µ = 1` halves `ζ`. -/
theorem zeta_kimball_homogeneous (θ εμ ω σinv : ℝ) :
    zetaGen θ εμ 0 (ω + σinv) = (ω + σinv) / (1 + θ * εμ) ∧
      (θ * εμ = 1 → zetaGen θ εμ 0 (ω + σinv) = zetaGen θ 0 0 (ω + σinv) / 2) := by
  unfold zetaGen
  refine ⟨by simp, fun h => ?_⟩
  simp only [add_zero, zero_add, mul_zero, h]
  ring

/-- Woodford (2003), p. 170: with Kimball preferences and specific factor markets
`ζ = (ω + σ⁻¹)/(1 + θ(ε_µ + ω))`; for the Chari et al. values with `θ ε_µ = 1` this is
`9/58 ≈ 0.16` (down from `1/6 ≈ 0.17`). -/
theorem zeta_kimball_specific (θ εμ ω σinv : ℝ) :
    zetaGen θ εμ ω σinv = (ω + σinv) / (1 + θ * (εμ + ω)) ∧
      zetaGen 10 (1 / 10) (5 / 4) 1 = 9 / 58 ∧ |(9 / 58 : ℝ) - 0.16| < 0.005 := by
  unfold zetaGen; norm_num [abs_lt]

/-! ### Proposition 3.3 and Table 3.1 -/

/-- Woodford (2003), eq. (1.43), p. 171:
`ζ = (1 − µ s_m)(s_y + s_Y)/(1 + θ[ε_µ + (1 − µ s_m) s_y])`, written with the composite
parameter `µ s_m`. -/
noncomputable def zeta33 (θ εμ μsm sy sY : ℝ) : ℝ :=
  (1 - μsm) * (sy + sY) / (1 + θ * (εμ + (1 - μsm) * sy))

/-- Woodford (2003), Proposition 3.3, p. 171: (1.43) is (1.41) with the value-added
elasticities `s_y, s_Y` scaled by `1 − µ s_m` (`intermediate_input_elasticities`). -/
theorem prop_3_3_formula (θ εμ μsm sy sY : ℝ) :
    zetaGen θ εμ ((1 - μsm) * sy) ((1 - μsm) * sY) = zeta33 θ εμ μsm sy sY := by
  unfold zetaGen zeta33; ring_nf

/-- **Proposition 3.3** (Woodford (2003), (1.43), p. 171; proof App. B.2, pp. 657–658): with
Kimball preferences (`m'(0) = ε_µ`, `d'(0) = −θ`) and the Leontief gross-output technology,
gross-output log marginal cost `ŝ` having partial elasticities `(1 − µ s_m) s_y` and
`(1 − µ s_m) s_Y` (`intermediate_input_elasticities`), the notional SRAS exists locally, is
unique, and has slope `ζ = zeta33 θ ε_µ (µ s_m) s_y s_Y`. -/
theorem prop_3_3 {m d : ℝ → ℝ} {shat : ℝ × ℝ → ℝ} {S : ℝ × ℝ →L[ℝ] ℝ}
    {θ εμ μsm sy sY : ℝ} (hm : HasStrictDerivAt m εμ 0) (hd : HasStrictDerivAt d (-θ) 0)
    (hd0 : d 0 = 0) (hm0 : m 0 = 0) (hs : HasStrictFDerivAt shat S 0) (hs0 : shat 0 = 0)
    (hS : ∀ q, S q = (1 - μsm) * sy * q.1 + (1 - μsm) * sY * q.2)
    (hden : 1 + θ * (εμ + (1 - μsm) * sy) ≠ 0) :
    ∃ x : ℝ → ℝ, x 0 = 0 ∧ (∀ᶠ y in 𝓝 0, sras m d shat (y, x y) = 0) ∧
      (∀ᶠ q in 𝓝 (0 : ℝ × ℝ), sras m d shat q = 0 ↔ x q.1 = q.2) ∧
      HasStrictDerivAt x (zeta33 θ εμ μsm sy sY) 0 := by
  rw [← prop_3_3_formula]
  exact notional_sras_exists hm hd hd0 hm0 hs hs0 hS hden

/-- Woodford (2003), p. 171: "ζ → 0 as s_m → µ⁻¹": the factor `1 − µ s_m` vanishes (provided
`1 + θ ε_µ ≠ 0`). -/
theorem zeta33_tendsto_zero {θ εμ μ sy sY : ℝ} (hμ : μ ≠ 0) (hden : 1 + θ * εμ ≠ 0) :
    Tendsto (fun sm => zeta33 θ εμ (μ * sm) sy sY) (𝓝 μ⁻¹) (𝓝 0) := by
  have hc : ContinuousAt (fun sm => zeta33 θ εμ (μ * sm) sy sY) μ⁻¹ := by
    unfold zeta33
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp [mul_inv_cancel₀ hμ, hden]
  have := hc.tendsto
  simpa [zeta33, mul_inv_cancel₀ hμ] using this

/-- Woodford (2003), p. 171: with homogeneous factor markets (`s_y = 0`), `µ s_m = 0.6`
multiplies `ζ` by `0.4` ("reduced by a factor of 2.5"). -/
theorem zeta33_homogeneous_factor (θ εμ sY : ℝ) :
    zeta33 θ εμ 0.6 0 sY = 0.4 * zeta33 θ εμ 0 0 sY := by
  unfold zeta33; ring_nf

/-- Woodford (2003), p. 171, footnote 23: with `θ = 10` (`µ = 10/9`), `µ s_m = 0.6` corresponds
to a materials share `s_m = 0.54`, and `s_m = 0.9` gives `µ s_m = 1` and hence `ζ = 0`. -/
theorem footnote_23 (εμ sy sY : ℝ) :
    (0.6 : ℝ) / (10 / 9) = 0.54 ∧ (10 / 9 : ℝ) * 0.9 = 1 ∧
      zeta33 10 εμ ((10 / 9) * 0.9) sy sY = 0 := by
  unfold zeta33; norm_num

/-- Woodford (2003), Table 3.1, p. 172, row `θ ε_µ = 0`, `µ s_m = 0` (`θ = 10`): exact values
`9/4`, `1/6`, `63/100`, `21/190` (homogeneous/specific, left/right calibrations). -/
theorem table31_row1 :
    zeta33 10 0 0 0 ((5 / 4 : ℝ) + 1) = 9 / 4 ∧ zeta33 10 0 0 (5 / 4) 1 = 1 / 6 ∧
      zeta33 10 0 0 0 ((47 / 100 : ℝ) + 16 / 100) = 63 / 100 ∧
      zeta33 10 0 0 (47 / 100) (16 / 100) = 21 / 190 := by
  unfold zeta33; norm_num

/-- Woodford (2003), Table 3.1, row `θ ε_µ = 1`, `µ s_m = 0`: `9/8`, `9/58`, `63/200`, `63/670`. -/
theorem table31_row2 :
    zeta33 10 (1 / 10) 0 0 ((5 / 4 : ℝ) + 1) = 9 / 8 ∧
      zeta33 10 (1 / 10) 0 (5 / 4) 1 = 9 / 58 ∧
      zeta33 10 (1 / 10) 0 0 ((47 / 100 : ℝ) + 16 / 100) = 63 / 200 ∧
      zeta33 10 (1 / 10) 0 (47 / 100) (16 / 100) = 63 / 670 := by
  unfold zeta33; norm_num

/-- Woodford (2003), Table 3.1, row `θ ε_µ = 0`, `µ s_m = 0.6`: `9/10`, `3/20`, `63/250`,
`7/80`. -/
theorem table31_row3 :
    zeta33 10 0 (6 / 10) 0 ((5 / 4 : ℝ) + 1) = 9 / 10 ∧
      zeta33 10 0 (6 / 10) (5 / 4) 1 = 3 / 20 ∧
      zeta33 10 0 (6 / 10) 0 ((47 / 100 : ℝ) + 16 / 100) = 63 / 250 ∧
      zeta33 10 0 (6 / 10) (47 / 100) (16 / 100) = 7 / 80 := by
  unfold zeta33; norm_num

/-- Woodford (2003), Table 3.1, row `θ ε_µ = 1`, `µ s_m = 0.6`: `9/20`, `9/70`, `63/500`,
`63/970`. -/
theorem table31_row4 :
    zeta33 10 (1 / 10) (6 / 10) 0 ((5 / 4 : ℝ) + 1) = 9 / 20 ∧
      zeta33 10 (1 / 10) (6 / 10) (5 / 4) 1 = 9 / 70 ∧
      zeta33 10 (1 / 10) (6 / 10) 0 ((47 / 100 : ℝ) + 16 / 100) = 63 / 500 ∧
      zeta33 10 (1 / 10) (6 / 10) (47 / 100) (16 / 100) = 63 / 970 := by
  unfold zeta33; norm_num

/-- Woodford (2003), Table 3.1, p. 172: every printed entry is the exact value rounded to two
decimals (`|exact − printed| ≤ 0.005`): 2.25, 0.17, 0.63, 0.11 / 1.13, 0.16, 0.32, 0.09 /
0.90, 0.15, 0.25, 0.09 / 0.45, 0.13, 0.13, 0.06. -/
theorem table31_rounding :
    |(9 / 4 : ℝ) - 2.25| ≤ 0.005 ∧ |(1 / 6 : ℝ) - 0.17| ≤ 0.005 ∧
    |(63 / 100 : ℝ) - 0.63| ≤ 0.005 ∧ |(21 / 190 : ℝ) - 0.11| ≤ 0.005 ∧
    |(9 / 8 : ℝ) - 1.13| ≤ 0.005 ∧ |(9 / 58 : ℝ) - 0.16| ≤ 0.005 ∧
    |(63 / 200 : ℝ) - 0.32| ≤ 0.005 ∧ |(63 / 670 : ℝ) - 0.09| ≤ 0.005 ∧
    |(9 / 10 : ℝ) - 0.90| ≤ 0.005 ∧ |(3 / 20 : ℝ) - 0.15| ≤ 0.005 ∧
    |(63 / 250 : ℝ) - 0.25| ≤ 0.005 ∧ |(7 / 80 : ℝ) - 0.09| ≤ 0.005 ∧
    |(9 / 20 : ℝ) - 0.45| ≤ 0.005 ∧ |(9 / 70 : ℝ) - 0.13| ≤ 0.005 ∧
    |(63 / 500 : ℝ) - 0.13| ≤ 0.005 ∧ |(63 / 970 : ℝ) - 0.06| ≤ 0.005 := by
  norm_num [abs_le]

/-- Woodford (2003), p. 172: the two corrections together reduce the homogeneous-markets value
of Chari et al. to one-fifth (`0.45` instead of `2.25`). -/
theorem table31_one_fifth :
    zeta33 10 (1 / 10) (6 / 10) 0 ((5 / 4 : ℝ) + 1) =
      zeta33 10 0 0 0 ((5 / 4 : ℝ) + 1) / 5 := by
  unfold zeta33; norm_num

end Woodford.NominalRigidities.StrategicComplementarity
