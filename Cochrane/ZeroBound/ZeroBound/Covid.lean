/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBPeg
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The Covid inflation: model claims

Cochrane (2023), Chapter 21, pp. 486–494. Only the model claims of this chapter are formalised;
the rest is data and speculation.

## Main results

* Helicopter drop (pp. 487, 490), frictionless one-period debt `B/P = S` (valuation equation):
  more debt with unchanged surpluses raises the price level proportionally
  (`helicopter_exact`, 30% more debt ⇒ 30% higher prices, `helicopter_thirty`); with a fraction
  `f` of the new debt backed, `P′/P = (1 + Δ)/(1 + fΔ)` and the real value of debt rises by the
  factor `1 + fΔ` (`partial_backing`). p. 488, survey error E10, confirmed: two-thirds backing
  of 30% new debt gives 8.33% inflation (`P′/P = 13/12`), not 10%, while "+20% real value" is
  exact (`partial_backing_example`, `e10_printed_pair_inconsistent`); 10% is the first-order term
  `d(P′/P)/dΔ|₀ = 1 − f` (`hasDerivAt_priceRatio`) with exact remainder
  `−f(1 − f)Δ²/(1 + fΔ)` (`priceRatio_remainder`). More backing, less inflation
  (`priceRatio_strictAnti`); only reserves unbacked (`reserves_only_unbacked`).
* p. 491: in the frictionless model, fiscal news moves only unexpected inflation
  (`fiscal_news_only_unexpected`, (5.10)–(5.12)).
* p. 492: under an interest-rate peg with fiscal backing, inflation returns to the peg
  (`peg_inflation_returns`, from `ZLBPeg`).
* p. 493: Phillips-curve disinflation algebra (`pc_output`, `disinflation_joint`,
  `disinflation_alone`, `joint_less_painful`, `painless_limit`, `fisherian_rate_fall`).
* p. 493: interest-cost arithmetic (`interest_cost_four_times`) and the 1981 bond windfall,
  survey error E11, confirmed: the real return is 11.5%, not 12% (`windfall_real_return`).
* Data arithmetic (pp. 486, 488): `cpi_rise`, `table_21_1`, `debt_increase_nearly_30`.
-/

namespace Cochrane.ZeroBound.Covid

open Filter Topology
open Cochrane.ZeroBound

/-! ## The helicopter drop -/

/-- Cochrane (2023), p. 487 (frictionless valuation equation `B_{t−1}/P_t = E_t∑βʲs_{t+j}`, §2):
the price level `P = B/S` given nominal debt `B` and the present value of surpluses `S`. -/
noncomputable def priceLevel (B S : ℝ) : ℝ := B / S

/-- Cochrane (2023), p. 490 ("If the expansion came with no change at all in expected future
surpluses, that will result in a cumulative 30% price-level rise"): with `S` unchanged,
`(1 + Δ)B` of debt gives `P′/P = 1 + Δ`. -/
theorem helicopter_exact {B S Δ : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) :
    priceLevel ((1 + Δ) * B) S / priceLevel B S = 1 + Δ := by
  unfold priceLevel
  field_simp

/-- Cochrane (2023), pp. 487, 490: a 30% debt expansion with no new backing gives a 30% price
rise. -/
theorem helicopter_thirty {B S : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) :
    priceLevel ((1 + 3 / 10) * B) S / priceLevel B S - 1 = 3 / 10 := by
  rw [helicopter_exact hB hS]
  ring

/-- Cochrane (2023), p. 488 ("If people expect two thirds of the debt to be repaid"): the price
ratio `(1 + Δ)/(1 + fΔ)` when debt grows by the fraction `Δ` and the fraction `f` of the new debt
is backed by new surpluses. -/
noncomputable def priceRatio (f Δ : ℝ) : ℝ := (1 + Δ) / (1 + f * Δ)

/-- Cochrane (2023), p. 488: with debt `(1 + Δ)B` and surpluses `S′ = (1 + fΔ)S` (the fraction
`f` of the new debt backed at the old price level), `P′/P = (1 + Δ)/(1 + fΔ)` and the real
value of debt rises by the factor `1 + fΔ`. -/
theorem partial_backing {B S f Δ : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) (hΔ : 1 + Δ ≠ 0) :
    priceLevel ((1 + Δ) * B) ((1 + f * Δ) * S) / priceLevel B S = priceRatio f Δ ∧
      (1 + Δ) * B / priceLevel ((1 + Δ) * B) ((1 + f * Δ) * S) =
        (1 + f * Δ) * (B / priceLevel B S) := by
  unfold priceLevel priceRatio
  constructor <;> field_simp

/-- Cochrane (2023), p. 488, survey error E10: with 30% new debt of which two thirds is backed,
the price level rises by the factor `13/12` (8.33%), and the real value of debt by exactly
`6/5` (+20%). -/
theorem partial_backing_example :
    priceRatio (2 / 3) (3 / 10) = 13 / 12 ∧ priceRatio (2 / 3) (3 / 10) - 1 < 1 / 10 ∧
      1 + (2 / 3 : ℝ) * (3 / 10) = 6 / 5 := by
  unfold priceRatio
  norm_num

/-- Cochrane (2023), p. 488, survey error E10: the printed pair "inflation stops at a cumulative
10% and the real value of debt rises by 20%" is inconsistent with a 30% rise in nominal debt,
since `1.1 × 1.2 ≠ 1.3`. -/
theorem e10_printed_pair_inconsistent : (1 + 1 / 10 : ℝ) * (1 + 1 / 5) ≠ 1 + 3 / 10 := by
  norm_num

/-- Cochrane (2023), p. 488: the 10% of the text is the first-order effect,
`d/dΔ [(1 + Δ)/(1 + fΔ)] = 1 − f` at `Δ = 0` (`= 1/3` for two-thirds backing, times `Δ = 0.3`). -/
theorem hasDerivAt_priceRatio (f : ℝ) : HasDerivAt (priceRatio f) (1 - f) 0 := by
  have h1 : HasDerivAt (fun Δ : ℝ => 1 + Δ) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun Δ : ℝ => 1 + f * Δ) f 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul f).const_add 1
  have h := HasDerivAt.div h1 h2 (by simp)
  unfold priceRatio
  convert h using 1
  simp

/-- Cochrane (2023), p. 488: the exact remainder of the first-order approximation,
`(1 + Δ)/(1 + fΔ) − 1 − (1 − f)Δ = −f(1 − f)Δ²/(1 + fΔ)`. -/
theorem priceRatio_remainder {f Δ : ℝ} (h : 1 + f * Δ ≠ 0) :
    priceRatio f Δ - 1 - (1 - f) * Δ = -(f * (1 - f) * Δ ^ 2) / (1 + f * Δ) := by
  unfold priceRatio
  rw [eq_div_iff h, sub_mul, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- Cochrane (2023), p. 488: at two-thirds backing of 30% new debt the first-order term is
exactly the book's 10%. -/
theorem first_order_example : (1 - 2 / 3 : ℝ) * (3 / 10) = 1 / 10 := by norm_num

/-- Cochrane (2023), p. 490 ("if people expect partial repayment, the price-level increase will
be smaller"): for `Δ > 0` the price ratio is strictly decreasing in the backed fraction
`f ≥ 0`. -/
theorem priceRatio_strictAnti {Δ : ℝ} (hΔ : 0 < Δ) :
    StrictAntiOn (fun f => priceRatio f Δ) (Set.Ici 0) := by
  intro f₁ hf₁ f₂ hf₂ hlt
  simp only [Set.mem_Ici] at hf₁ hf₂
  unfold priceRatio
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  nlinarith

/-- Cochrane (2023), p. 490 ("If only the increase in reserves is considered unbacked"): with
3/5 of the 30% new debt in unbacked reserves (`f = 2/5`) the price level rises by `65/56`,
less than the 30% of a fully unbacked expansion. -/
theorem reserves_only_unbacked :
    priceRatio (2 / 5) (3 / 10) = 65 / 56 ∧ priceRatio (2 / 5) (3 / 10) < 1 + 3 / 10 := by
  unfold priceRatio
  norm_num

/-! ## Fiscal news and unexpected inflation (p. 491) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 491 ("bad fiscal news can only affect unexpected inflation"), in the
frictionless model (5.10)–(5.12): if `i_t = E_tπ_{t+1}` and `π_{t+1} − E_tπ_{t+1} = −ε_{t+1}`
in two economies with the same interest-rate path but different fiscal news `ε`, `ε′`, expected
inflation is the same and `π_{t+1} = i_t − ε_{t+1}`. -/
theorem fiscal_news_only_unexpected {i π π' ε ε' : ℕ → Ω → ℝ}
    (hf : ∀ t, i t = 𝔼.E t (π (t + 1))) (hf' : ∀ t, i t = 𝔼.E t (π' (t + 1)))
    (hv : ∀ t, π (t + 1) - 𝔼.E t (π (t + 1)) = -ε (t + 1))
    (hv' : ∀ t, π' (t + 1) - 𝔼.E t (π' (t + 1)) = -ε' (t + 1)) (t : ℕ) :
    𝔼.E t (π (t + 1)) = 𝔼.E t (π' (t + 1)) ∧ π (t + 1) = i t - ε (t + 1) ∧
      π (t + 1) - π' (t + 1) = ε' (t + 1) - ε (t + 1) := by
  refine ⟨by rw [← hf t, ← hf' t], ?_, ?_⟩
  · rw [hf t, sub_eq_add_neg, ← hv t]
    abel
  · have a := hv t
    have b := hv' t
    rw [← hf t] at a
    rw [← hf' t] at b
    rw [show π (t + 1) = i t + -ε (t + 1) by rw [← a]; abel,
      show π' (t + 1) = i t + -ε' (t + 1) by rw [← b]; abel]
    abel

/-- Cochrane (2023), p. 492 ("If the Fed left the interest rate alone, inflation would
eventually return"): in the sticky-price model at a peg with the fiscal valuation equation, the
unique equilibrium (`ZLBPeg.fiscal_selects`) has expected inflation converging back to the
peg. -/
theorem peg_inflation_returns {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (ZLBPeg.pegPi ibar (ZLBPeg.fiscalP β σ κ ρ ε) (s + k)) ω) atTop
      (𝓝 ibar) :=
  ZLBPeg.fiscal_stable 𝔼 hβ hσκ hκ hρ0 hρ1 hεa hεb hεmd s ω

/-! ## Phillips-curve disinflation (p. 493) -/

/-- Cochrane (2023), p. 493: the Phillips curve `π_t = βE_tπ_{t+1} + κx_t` determines output,
`x_t = (π_t − βE_tπ_{t+1})/κ`. -/
theorem pc_output {β κ π Eπ x : ℝ} (hκ : κ ≠ 0) :
    π = β * Eπ + κ * x ↔ x = (π - β * Eπ) / κ := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), p. 493 ("inflation reduction can be relatively painless if expected
inflation declines"): lowering both `π_t` and `E_tπ_{t+1}` by `d` changes output by
`−(1 − β)d/κ`. -/
theorem disinflation_joint (β κ π Eπ d : ℝ) :
    (π - d - β * (Eπ - d)) / κ - (π - β * Eπ) / κ = -((1 - β) * d / κ) := by
  ring

/-- Cochrane (2023), p. 493 ("and painful if it does not decline"): lowering `π_t` by `d` with
`E_tπ_{t+1}` unchanged changes output by `−d/κ`. -/
theorem disinflation_alone (β κ π Eπ d : ℝ) :
    (π - d - β * Eπ) / κ - (π - β * Eπ) / κ = -(d / κ) := by
  ring

/-- Cochrane (2023), p. 493: for `0 < β < 1`, `κ > 0`, `d > 0`, the output cost of a credible
joint disinflation is strictly smaller than that of a disinflation without lower expected
inflation. -/
theorem joint_less_painful {β κ d : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hd : 0 < d) :
    |-((1 - β) * d / κ)| < |-(d / κ)| := by
  rw [abs_neg, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  apply div_lt_div_of_pos_right _ hκ
  nlinarith

/-- Cochrane (2023), p. 493 ("relatively painless"): the output cost `(1 − β)d/κ` of a joint
disinflation vanishes as `β → 1`. -/
theorem painless_limit (κ d : ℝ) :
    Tendsto (fun β : ℝ => (1 - β) * d / κ) (𝓝 1) (𝓝 0) := by
  have h : Continuous (fun β : ℝ => (1 - β) * d / κ) := by fun_prop
  simpa using h.tendsto 1

/-- Cochrane (2023), p. 493 ("nominal interest rates fall immediately in Fisherian fashion"):
with `i_t = r + E_tπ_{t+1}`, lowering expected inflation by `d` lowers the nominal rate by `d`
at once. -/
theorem fisherian_rate_fall (r Eπ d : ℝ) : (r + (Eπ - d)) - (r + Eπ) = -d := by ring

/-! ## Interest costs and the 1981 windfall (p. 493) -/

/-- Cochrane (2023), p. 493 ("four times larger real interest costs … 5% real interest rates mean
5% of GDP additional deficit"): the interest cost `r·b` at `r = 5%` is 5% of GDP at a 100%
debt ratio, four times the cost at the 25% ratio of 1980. -/
theorem interest_cost_four_times :
    (5 / 100 : ℝ) * 1 = 5 / 100 ∧ ((5 / 100 : ℝ) * 1) / ((5 / 100) * (1 / 4)) = 4 := by
  norm_num

/-- Cochrane (2023), p. 493: for any real rate `r ≠ 0`, the interest cost at a 100% debt ratio is
four times that at 25%. -/
theorem interest_cost_ratio {r : ℝ} (hr : r ≠ 0) : (r * 1) / (r * (1 / 4)) = 4 := by
  field_simp

/-- Cochrane (2023), p. 493, survey error E11: a 15.84% nominal yield with 3.9% inflation gives
the real return `(1 + y)/(1 + π) − 1 = (y − π)/(1 + π)`, which is between 11.49% and 11.5%,
not 12% (12% is the approximation `y − π = 11.94%`). -/
theorem windfall_real_return :
    (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 = (1584 / 10000 - 39 / 1000) / (1 + 39 / 1000) ∧
      1149 / 10000 < (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 ∧
      (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 < 115 / 1000 ∧
      (1584 / 10000 - 39 / 1000 : ℝ) = 1194 / 10000 := by
  norm_num

/-! ## Data arithmetic (pp. 486, 488) -/

/-- Cochrane (2023), p. 486: the CPI rose from 263.161 to 276.724, i.e. by 5.15%, and over the
eight months this is a 7.8% annual rate: `r^{3/2} ∈ (1.078, 1.079)`, stated as
`r³ ∈ (1.078², 1.079²)`. -/
theorem cpi_rise :
    (515 / 10000 : ℝ) < 276.724 / 263.161 - 1 ∧ (276.724 / 263.161 : ℝ) - 1 < 516 / 10000 ∧
      (1.078 : ℝ) ^ 2 < (276.724 / 263.161) ^ 3 ∧ ((276.724 : ℝ) / 263.161) ^ 3 < 1.079 ^ 2 := by
  norm_num

/-- Cochrane (2023), Table 21.1, p. 488: the arithmetic of the table (A + B − C and the
differences). -/
theorem table_21_1 :
    (17187 + 3427 - 2329 : ℝ) = 18285 ∧ (22304 + 6389 - 5431 : ℝ) = 23262 ∧
      (23262 - 18285 : ℝ) = 4977 ∧ (22304 - 17187 : ℝ) = 5117 ∧ (6389 - 3427 : ℝ) = 2962 ∧
      (5431 - 2329 : ℝ) = 3102 ∧ (20994 - 15325 : ℝ) = 5669 := by
  norm_num

/-- Cochrane (2023), p. 486 ("$5 trillion is a nearly 30% increase in the $17 trillion of debt
outstanding"): `5/17 ∈ (0.29, 0.30)`. -/
theorem debt_increase_nearly_30 : (29 / 100 : ℝ) < 5 / 17 ∧ (5 / 17 : ℝ) < 3 / 10 := by
  norm_num

end Cochrane.ZeroBound.Covid
