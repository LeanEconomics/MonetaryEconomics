/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Prop61
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Asymmetric disturbances: welfare in the two-sector model

Woodford (2003), *Interest and Prices*, Chapter 6, §4.3 "Asymmetric Disturbances",
pp. 435–443, and Appendix E, §§E.6–E.7, pp. 703–706.

The welfare approximation for the two-sector model of Chapter 3, §2.5 (asymmetric disturbances,
possibly different price stickiness), Propositions 6.10 and 6.11, and the discussion of
stabilisation objectives that follows (Aoki's flexible-sector limit, equal stickiness, gap
targeting). Results from Chapter 3 (Proposition 3.8's `κ_j`, `γ_j`) are restated, not imported.

## Main results

* Cross-sectional moments of a finite weighted population are those of `ExpLogCES`
  (`crossMean`, `crossVar`) with the identities of `Moments` (`crossMean_affine`,
  `crossVar_affine` ((2.12): `var log y = θ² var log p`), `mean_quadratic`, and the exact Calvo
  mixture (E.8) `Moments.mix_var`, in each sector: App. E.7); here `var_two`.
* CES aggregators as exact derivatives (the derivatives are `ExpLogCES`'s, along the ray):
  `lse`, `hasDerivAt_lse`, `hasDerivAt_lseD_zero`
  (second derivative = variance), `log_cesIdx`, `ces_taylor` ((E.5)/(E.28), and the price index
  `log P = E log p + ½(1 − θ) var log p`); the two-sector aggregator `upperCES`,
  `log_upperCES`, `upperCES_taylor` ((E.27) as exact derivatives), `upperCES_E27` (the printed
  (E.27) equals the exact Taylor polynomial up to t.i.p. and a cubic term), `abs_S_le`.
* **Proposition 6.10, Layer A**: `prop_6_10_layerA` ((E.27)–(E.31): exact identity with explicit
  t.i.p. `tip610` and explicit remainder `R610`), `R610_scale`/`R610_isBigO` (weighted degree
  three), `natural_rates` (the natural rates from the flexible-price conditions), `prop_6_10`
  ((4.24)/(E.26) in relative prices and price dispersion), `dispersion_coeff`, `relprice_coeff`.
* **Proposition 6.11**: `dispersion_tsum` (the sectoral Proposition 6.3: discounted dispersion
  equals `α_j/((1 − α_j)(1 − α_jβ))` times discounted squared inflation plus t.i.p.),
  `infl_discrepancy`, `sq_discrepancy_le`, `rem_discrepancy_le`, `calvo_coeff`, `wJ_sum`
  (`w₁ + w₂ = 1`), `weights_pos`, `prop_6_11` (the discounted loss (4.25) with
  `w_j = n_jκ/κ_j`, `λ_x = κ/θ`, `λ_R = n₁n₂η(1 + ωη)λ_x/(σ⁻¹ + ω)`).
* `κ` is a weighted **harmonic** mean (survey error 23): `kappaH_mem`, `kappaH_lt_geom`,
  `printed_geometric_average_false`.
* Equal stickiness: `equal_stickiness_weights`, `half_sq_identity`, `weighted_sq_identity`,
  `loss_equal_stickiness`, `printed_half_weights_iff`, `relPrice_policy_invariant` (via
  `exists_stable_root`, `second_order_unique`), `equal_stickiness_optimal`.
* Aoki's limit: `kappaJ_inv`, `wJ_eq_inv`, `aoki_weights_tendsto` (`w₁ → 0` as `α₁ → 0⁺`),
  `aoki_relgap`, `aoki_slope_pos`, `aoki_policy`, `loss425_nonneg`, `aoki_optimal`.
* Gap targeting: `gamma_div_kappa`, `weighted_slopes`, `gap_targeting_pc`
  (`π̄ = κx + βE π̄'`), `gap_iff_pibar`, `targ_phi_eq_w1` (`φ = w₁`).
* Table 6.3: `table_6_3_lamR`.
* Taylor coefficients of the primitives as exact derivatives: `ray_taylor` (first and second
  derivatives of `W(X̄e^{εx}, εξ)` for a Fréchet-differentiable `W(X, ξ)`), `uTaylor_coeffs`,
  `uTaylor_ray` ((E.2)), `vTaylor_coeffs`, `vTaylor_ray` ((E.29), including the `Φ × quadratic`
  term the book drops), `PhiSec`, `sum_PhiTerm`, `PhiSec_scale`, `prop_6_10_exact`
  (Proposition 6.10 with the exact (E.29)).
* The Calvo process: `lmass`, `lmean`, `lsq`, `lvar`, `calvoStep`, `lsum_sq_dev`,
  `lsum_mul_const`, `lvar_eq_sum`, `lmap_scale`, `calvoStep_moments`, `calvoStep_var`,
  `calvoPop`, `lagMean`, `calvo_recursion` (the dispersion recursion as a theorem),
  `lmoments_bound`, `calvoPop_invariants`, `calvo_bdd`, `infl_discrepancy_rho`, and
  `prop_6_11_calvo` (Proposition 6.11 from the Calvo dynamics).

## Corrections to the book

* p. 437 and p. 706 (survey error 23): `κ = (n₁κ₁⁻¹ + n₂κ₂⁻¹)⁻¹` is a weighted *harmonic* mean,
  strictly below the weighted geometric mean unless `κ₁ = κ₂`.
* p. 705: the display `(σ⁻¹ + ω)Ŷⁿ = σ⁻¹g + ∑ n_j q_j` omits the factor `ω` on `∑ n_j q_j`
  (`natural_rates`, `printed_natY_iff`); the proof of (E.31) needs the corrected form.
* p. 438: with equal stickiness the weights are `w_j = n_j`; the printed `w₁ = w₂ = 0.5` and the
  coefficient `¼` hold only for `n₁ = n₂ = ½` (`printed_half_weights_iff`); in general the
  coefficient is `n₁n₂` (`loss_equal_stickiness`).
* p. 441 (survey error 24, recorded, no formal content): the losses of output-gap targeting are
  plotted in Figure 6.2 (whose vertical axis is `Ê[L]`), not in Figure 6.3 (whose vertical axis is
  the index weight `φ`). The same slip recurs on p. 447 ("As in Figure 6.3, distortions can be
  reduced to zero only in the two extreme cases" refers to the loss plot, Figure 6.2).
-/

namespace Woodford.StabilizationWelfare.TwoSectorWelfare

open Filter Topology
open Sequences hiding dispersion_tsum
open ExpLogCES (crossMean crossVar crossVar_eq cesMoment cesMoment1 cesMoment_pos cesIndex
  cesIndex_mul log_cesIndex_exp cumulant hasDerivAt_cesMoment_eps cumulant_eps_second_deriv)
open Moments (crossMean_affine crossVar_affine mean_quadratic sum_sq_eq calvoKappa)
open Prop61 (Tu Tv xStarLin)

/-! ### Cross-sectional moments of a finite weighted population -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), p. 396 and App. E.6, p. 703: the variance of a two-point distribution with
masses `n₁`, `n₂ = 1 − n₁` is `n₁ n₂ (z₂ − z₁)²`. -/
theorem var_two (n1 z1 z2 : ℝ) :
    crossVar ![n1, 1 - n1] ![z1, z2] = n1 * (1 - n1) * (z2 - z1) ^ 2 := by
  simp only [crossVar, crossMean, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-! ### Exact derivatives of the CES aggregators: (E.5), (E.27), (E.28)

All the CES aggregators of the chapter are, in log deviations from the steady state, of the form
`r⁻¹ log ∑ w_i exp(z_i)`. Along a ray `ε ↦ ε z` the first derivative at `0` is the mean of `z` and
the second derivative is its variance; this is the exact content of the second-order expansions
(E.5), (E.27) and (E.28). -/

/-- Woodford (2003), App. E, (E.5)/(E.28): the log-sum-exp `ε ↦ log ∑ w_i exp(ε z_i)`. -/
noncomputable def lse (w z : ι → ℝ) (ε : ℝ) : ℝ := Real.log (∑ i, w i * Real.exp (ε * z i))

/-- Woodford (2003), App. E, (E.5)/(E.28): the derivative of `lse`,
`(∑ w_i z_i exp(ε z_i)) / ∑ w_i exp(ε z_i)`. -/
noncomputable def lseD (w z : ι → ℝ) (ε : ℝ) : ℝ :=
  (∑ i, w i * z i * Real.exp (ε * z i)) / ∑ i, w i * Real.exp (ε * z i)

/-- Woodford (2003), App. E (**exact derivative**): `lse` has derivative `lseD` everywhere. -/
theorem hasDerivAt_lse {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (z : ι → ℝ)
    (ε : ℝ) : HasDerivAt (lse w z) (lseD w z ε) ε := by
  have e : lse w z = fun e => Real.log (cesMoment w 1 (fun i => e * z i)) := by
    funext e; simp only [lse, cesMoment, one_mul]
  rw [e]
  refine ((hasDerivAt_cesMoment_eps w 1 z ε).log (cesMoment_pos hw0 hw 1 _).ne').congr_deriv ?_
  simp only [lseD, cesMoment1, cesMoment, one_mul]

/-- Woodford (2003), App. E: `lse(0) = 0` (normalised weights). -/
theorem lse_zero {w : ι → ℝ} (hw : ∑ i, w i = 1) (z : ι → ℝ) : lse w z 0 = 0 := by
  simp [lse, hw]

/-- Woodford (2003), App. E (first-order term of (E.5)/(E.28)): `lse'(0) = E z`. -/
theorem lseD_zero {w : ι → ℝ} (hw : ∑ i, w i = 1) (z : ι → ℝ) :
    lseD w z 0 = crossMean w z := by
  simp [lseD, hw, crossMean]

/-- Woodford (2003), App. E (**second-order term of (E.5)/(E.28)**, exact derivative):
`lse''(0) = var z`. -/
theorem hasDerivAt_lseD_zero {w : ι → ℝ} (hw : ∑ i, w i = 1)
    (z : ι → ℝ) : HasDerivAt (lseD w z) (crossVar w z) 0 := by
  have e : lseD w z = fun ε => 1 / 1 * (cesMoment1 w 1 z ε / cesMoment w 1 (fun i => ε * z i)) := by
    funext e; simp only [lseD, cesMoment1, cesMoment, one_mul, div_one]
  rw [e]
  exact (cumulant_eps_second_deriv hw one_ne_zero z).congr_deriv (one_mul _)

/-- Woodford (2003), (E.5)/(E.28): in log deviations, with `y_i = Ȳ exp(ε ŷ_i)`,
`log(CES/Ȳ) = r⁻¹ lse(r ŷ)(ε)` exactly (homogeneity `ExpLogCES.cesIndex_mul` and the cumulant
form `ExpLogCES.log_cesIndex_exp` of the Dixit–Stiglitz index `ExpLogCES.cesIndex`). -/
theorem log_cesIdx {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {r Ybar : ℝ}
    (hr : r ≠ 0) (hY : 0 < Ybar) (yh : ι → ℝ) (ε : ℝ) :
    Real.log (cesIndex w r (fun i => Ybar * Real.exp (ε * yh i)) / Ybar) =
      r⁻¹ * lse w (fun i => r * yh i) ε := by
  have hp : ∀ i, 0 < Real.exp (ε * yh i) := fun i => Real.exp_pos _
  have h2 := log_cesIndex_exp hw0 hw r (fun i => ε * yh i)
  rw [cesIndex_mul hw0 hr hY hp, mul_div_cancel_left₀ _ hY.ne', h2]
  unfold cumulant cesMoment lse
  rw [one_div]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring_nf

/-- Woodford (2003), eqs. (E.5) and (E.28), pp. 694 and 704 (**exact derivatives**): along the
ray `y_i = Ȳ exp(ε ŷ_i)`, the log CES index `F(ε) = log(CES/Ȳ)` satisfies `F(0) = 0`,
`F'(0) = E_i ŷ` and `F''(0) = r var_i ŷ`. With `r = 1 − θ⁻¹` this is
`Ŷ = E_i ŷ + ½(1 − θ⁻¹) var_i ŷ + O(‖ŷ‖³)`; with `r = 1 − θ` (prices) it is
`log P = E_i log p + ½(1 − θ) var_i log p + O(3)`. -/
theorem ces_taylor {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {r Ybar : ℝ}
    (hr : r ≠ 0) (hY : 0 < Ybar) (yh : ι → ℝ) :
    (fun ε => Real.log (cesIndex w r (fun i => Ybar * Real.exp (ε * yh i)) / Ybar)) 0 = 0 ∧
    (∀ ε, HasDerivAt (fun e => Real.log (cesIndex w r (fun i => Ybar * Real.exp (e * yh i)) / Ybar))
      (r⁻¹ * lseD w (fun i => r * yh i) ε) ε) ∧
    r⁻¹ * lseD w (fun i => r * yh i) 0 = crossMean w yh ∧
    HasDerivAt (fun ε => r⁻¹ * lseD w (fun i => r * yh i) ε) (r * crossVar w yh) 0 := by
  have hF : (fun e => Real.log (cesIndex w r (fun i => Ybar * Real.exp (e * yh i)) / Ybar)) =
      fun e => r⁻¹ * lse w (fun i => r * yh i) e := funext fun e => log_cesIdx hw0 hw hr hY yh e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF]; simp [lse_zero hw]
  · intro ε; rw [hF]; exact (hasDerivAt_lse hw0 hw _ ε).const_mul _
  · rw [lseD_zero hw]
    have := crossMean_affine hw 0 r yh
    simp only [zero_add] at this
    rw [this]; field_simp
  · have h := (hasDerivAt_lseD_zero hw (fun i => r * yh i)).const_mul r⁻¹
    refine h.congr_deriv ?_
    have := crossVar_affine hw 0 r yh
    simp only [zero_add] at this
    rw [this]; field_simp

/-! ### The two-sector aggregator (E.27) -/

/-- Woodford (2003), eq. (2.22) of Chapter 3, p. 200: the two-sector consumption aggregator
`[(n₁φ₁)^{1/η} C₁^{(η−1)/η} + (n₂φ₂)^{1/η} C₂^{(η−1)/η}]^{η/(η−1)}`, `n₂ = 1 − n₁`. -/
noncomputable def upperCES (n1 η φ1 φ2 C1 C2 : ℝ) : ℝ :=
  ((n1 * φ1) ^ (1 / η) * C1 ^ ((η - 1) / η) +
    ((1 - n1) * φ2) ^ (1 / η) * C2 ^ ((η - 1) / η)) ^ (η / (η - 1))

/-- Woodford (2003), App. E.6, p. 703: in log deviations (`φ_j = exp(ε φ̂_j)`,
`C_j = n_j Ȳ exp(ε Ŷ_j)`, the steady state being `φ_j = 1`, `C_j = n_j Ȳ`), the two-sector
aggregator is a CES index over the two sectors with weights `n_j`:
`log(C/Ȳ) = r⁻¹ lse_n(z)(ε)`, `z_j = η⁻¹ φ̂_j + r Ŷ_j`, `r = (η − 1)/η`. -/
theorem log_upperCES {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hY : 0 < Ybar) (f1 f2 Y1 Y2 ε : ℝ) :
    Real.log (upperCES n1 η (Real.exp (ε * f1)) (Real.exp (ε * f2))
        (n1 * Ybar * Real.exp (ε * Y1)) ((1 - n1) * Ybar * Real.exp (ε * Y2)) / Ybar) =
      ((η - 1) / η)⁻¹ * lse ![n1, 1 - n1]
        ![η⁻¹ * f1 + (η - 1) / η * Y1, η⁻¹ * f2 + (η - 1) / η * Y2] ε := by
  set r := (η - 1) / η with hr
  have hr0 : r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hη1) hη.ne'
  have hn2 : 0 < 1 - n1 := by linarith
  have hw0 : ∀ i, 0 ≤ (![n1, 1 - n1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hn0.le, hn2.le]
  have hw : ∑ i, (![n1, 1 - n1] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
  set z : Fin 2 → ℝ := ![η⁻¹ * f1 + r * Y1, η⁻¹ * f2 + r * Y2] with hz
  have key := log_cesIdx hw0 hw hr0 hY (fun i => z i / r) ε
  have hzr : (fun i => r * (z i / r)) = z := funext fun i => by field_simp
  rw [hzr] at key
  rw [← key]
  congr 2
  have hterm : ∀ (n f Y zz : ℝ), 0 < n → zz = η⁻¹ * f + r * Y →
      (n * Real.exp (ε * f)) ^ (1 / η) * (n * Ybar * Real.exp (ε * Y)) ^ r =
        n * (Ybar * Real.exp (ε * (zz / r))) ^ r := by
    intro n f Y zz hn hzz
    rw [Real.rpow_def_of_pos (mul_pos hn (Real.exp_pos _)),
      Real.rpow_def_of_pos (mul_pos (mul_pos hn hY) (Real.exp_pos _)),
      Real.rpow_def_of_pos (mul_pos hY (Real.exp_pos _)),
      Real.log_mul hn.ne' (Real.exp_pos _).ne', Real.log_mul (mul_pos hn hY).ne'
        (Real.exp_pos _).ne', Real.log_mul hn.ne' hY.ne', Real.log_mul hY.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp, Real.log_exp, ← Real.exp_add]
    conv_rhs => rw [← Real.exp_log hn, ← Real.exp_add]
    congr 1
    rw [hzz, hr]
    field_simp
    ring
  unfold upperCES cesIndex
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hterm n1 f1 Y1 _ hn0 rfl, hterm (1 - n1) f2 Y2 _ hn2 rfl]
  congr 1
  rw [hr]
  field_simp

/-- Woodford (2003), eq. (E.27), p. 703 (**exact derivatives**): along the ray
`(φ̂, Ŷ_j) ↦ (ε φ̂, ε Ŷ_j)`, `G(ε) = log(Y/Ȳ)` has `G(0) = 0`,
`G'(0) = r⁻¹η⁻¹(n₁φ̂₁ + n₂φ̂₂) + (n₁Ŷ₁ + n₂Ŷ₂)` and
`G''(0) = r⁻¹ n₁n₂ (η⁻¹(φ̂₂ − φ̂₁) + r(Ŷ₂ − Ŷ₁))²`, where `r = (η − 1)/η = 1 − η⁻¹`. -/
theorem upperCES_taylor {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η)
    (hη1 : η ≠ 1) (hY : 0 < Ybar) (f1 f2 Y1 Y2 : ℝ) :
    let G := fun ε => Real.log (upperCES n1 η (Real.exp (ε * f1)) (Real.exp (ε * f2))
        (n1 * Ybar * Real.exp (ε * Y1)) ((1 - n1) * Ybar * Real.exp (ε * Y2)) / Ybar)
    let z : Fin 2 → ℝ := ![η⁻¹ * f1 + (1 - η⁻¹) * Y1, η⁻¹ * f2 + (1 - η⁻¹) * Y2]
    G 0 = 0 ∧ (∀ ε, HasDerivAt G ((1 - η⁻¹)⁻¹ * lseD ![n1, 1 - n1] z ε) ε) ∧
      (1 - η⁻¹)⁻¹ * lseD ![n1, 1 - n1] z 0 =
        (1 - η⁻¹)⁻¹ * η⁻¹ * (n1 * f1 + (1 - n1) * f2) + (n1 * Y1 + (1 - n1) * Y2) ∧
      HasDerivAt (fun ε => (1 - η⁻¹)⁻¹ * lseD ![n1, 1 - n1] z ε)
        ((1 - η⁻¹)⁻¹ * (n1 * (1 - n1) * (η⁻¹ * (f2 - f1) + (1 - η⁻¹) * (Y2 - Y1)) ^ 2)) 0 := by
  intro G z
  have hr : (η - 1) / η = 1 - η⁻¹ := by field_simp
  have hr0 : (1 : ℝ) - η⁻¹ ≠ 0 := by rw [← hr]; exact div_ne_zero (sub_ne_zero.mpr hη1) hη.ne'
  have hn2 : 0 < 1 - n1 := by linarith
  have hw0 : ∀ i, 0 ≤ (![n1, 1 - n1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hn0.le, hn2.le]
  have hw : ∑ i, (![n1, 1 - n1] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
  have hG : G = fun ε => (1 - η⁻¹)⁻¹ * lse ![n1, 1 - n1] z ε := by
    funext ε
    simp only [G, z]
    rw [log_upperCES hn0 hn1 hη hη1 hY, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hG]; simp [lse_zero hw]
  · intro ε; rw [hG]; exact (hasDerivAt_lse hw0 hw _ ε).const_mul _
  · rw [lseD_zero hw]
    simp only [crossMean, z, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · refine ((hasDerivAt_lseD_zero hw z).const_mul _).congr_deriv ?_
    simp only [z]
    rw [var_two]
    ring

/-- Woodford (2003), eq. (E.27), p. 703 (**Layer A**): the second-order Taylor polynomial
`G'(0) + ½G''(0)` of the two-sector aggregator equals the printed (E.27)
`∑ n_j(1 + η⁻¹φ̂_j)Ŷ_j + ½n₁n₂(1 − η⁻¹)(Ŷ₂ − Ŷ₁)²` plus the purely exogenous term
`τ = r⁻¹η⁻¹ S + ½ n₁n₂ r⁻¹η⁻² (φ̂₂ − φ̂₁)²` (t.i.p.) minus `η⁻¹ S (n₁Ŷ₁ + n₂Ŷ₂)`, where
`S = n₁φ̂₁ + n₂φ̂₂` and `r = 1 − η⁻¹`. The last term is third order because the normalisation
`n₁φ₁ + n₂φ₂ = 1` makes `S` second order (`abs_S_le`). -/
theorem upperCES_E27 {ηi : ℝ} (hr : 1 - ηi ≠ 0) (n1 f1 f2 Y1 Y2 : ℝ) :
    (1 - ηi)⁻¹ * ηi * (n1 * f1 + (1 - n1) * f2) + (n1 * Y1 + (1 - n1) * Y2) +
        (1 - ηi)⁻¹ * (n1 * (1 - n1) * (ηi * (f2 - f1) + (1 - ηi) * (Y2 - Y1)) ^ 2) / 2 =
      (n1 * (1 + ηi * f1) * Y1 + (1 - n1) * (1 + ηi * f2) * Y2 +
          n1 * (1 - n1) * (1 - ηi) / 2 * (Y2 - Y1) ^ 2) +
        ((1 - ηi)⁻¹ * ηi * (n1 * f1 + (1 - n1) * f2) +
          n1 * (1 - n1) * (1 - ηi)⁻¹ * ηi ^ 2 / 2 * (f2 - f1) ^ 2) -
        ηi * (n1 * f1 + (1 - n1) * f2) * (n1 * Y1 + (1 - n1) * Y2) := by
  field_simp
  ring

/-- Woodford (2003), p. 201 (the normalisation `n₁φ₁ + n₂φ₂ = 1`): with `φ_j = exp φ̂_j` and
`|φ̂_j| ≤ 1`, the size-weighted mean `S = n₁φ̂₁ + n₂φ̂₂` is second order,
`|S| ≤ n₁φ̂₁² + n₂φ̂₂²`. -/
theorem abs_S_le {n1 f1 f2 : ℝ} (hn0 : 0 ≤ n1) (hn1 : n1 ≤ 1)
    (hnorm : n1 * Real.exp f1 + (1 - n1) * Real.exp f2 = 1) (h1 : |f1| ≤ 1) (h2 : |f2| ≤ 1) :
    |n1 * f1 + (1 - n1) * f2| ≤ n1 * f1 ^ 2 + (1 - n1) * f2 ^ 2 := by
  have e1 := Real.abs_exp_sub_one_sub_id_le h1
  have e2 := Real.abs_exp_sub_one_sub_id_le h2
  have hS : n1 * f1 + (1 - n1) * f2 =
      -(n1 * (Real.exp f1 - 1 - f1) + (1 - n1) * (Real.exp f2 - 1 - f2)) := by
    linear_combination hnorm
  rw [hS, abs_neg]
  have hn2 : 0 ≤ 1 - n1 := by linarith
  calc |n1 * (Real.exp f1 - 1 - f1) + (1 - n1) * (Real.exp f2 - 1 - f2)|
      ≤ |n1 * (Real.exp f1 - 1 - f1)| + |(1 - n1) * (Real.exp f2 - 1 - f2)| := abs_add_le _ _
    _ = n1 * |Real.exp f1 - 1 - f1| + (1 - n1) * |Real.exp f2 - 1 - f2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn0, abs_of_nonneg hn2]
    _ ≤ n1 * f1 ^ 2 + (1 - n1) * f2 ^ 2 := by gcongr

/-! ### Proposition 6.10, Layer A: the exact second-order identity (E.27)–(E.31)

Everything is measured in units of `Ȳ u_c`. The endogenous variables are the sectoral output
indices `Ŷ_j` and the within-sector output dispersions `V_j = var_i^j ŷ(i)`; the exogenous ones
are `g`, `q_j`, the relative demand shock `d = φ̂₂ − φ̂₁`, the exogenous part `τ` of the
aggregator's Taylor polynomial (`upperCES_E27`) and the distortion `Φ`. Weighted degree: `Ŷ_j`,
`d`, `g`, `q_j`, `Φ` have weight one; `V_j` and `τ` weight two. -/

/-- Woodford (2003), App. E.6, p. 704: (E.29) integrated over a sector, in terms of the
sectoral mean `m = E_iʲ ŷ` and variance `V = var_iʲ ŷ`. -/
noncomputable def TvSec (ω Phi q m V : ℝ) : ℝ :=
  (1 - Phi) * m + (1 + ω) / 2 * (m ^ 2 + V) - ω * q * m

/-- Woodford (2003), App. E.6, p. 704 ("integrating (E.29) over the goods `i` belonging to
sector `j`"): `∑ w_i Tv(ŷ_i) = TvSec(E ŷ, var ŷ)`. -/
theorem sum_Tv {w : ι → ℝ} (hw : ∑ i, w i = 1) (ω Phi q : ℝ) (y : ι → ℝ) :
    ∑ i, w i * Tv Phi ω q (y i) = TvSec ω Phi q (crossMean w y) (crossVar w y) := by
  have h : ∀ i, w i * Tv Phi ω q (y i) =
      w i * ((1 - Phi - ω * q) * y i + (1 + ω) / 2 * y i ^ 2) := fun i => by unfold Tv; ring
  simp only [h, mean_quadratic hw]
  unfold TvSec; ring

/-- Woodford (2003), eq. (E.28), p. 704: the sectoral mean in terms of the sectoral index,
`E_iʲ ŷ = Ŷ_j − ½(1 − θ⁻¹) var_iʲ ŷ` (the second-order relation of `ces_taylor`). -/
noncomputable def meanE28 (θi Yj V : ℝ) : ℝ := Yj - (1 - θi) / 2 * V

/-- Woodford (2003), App. E.6, p. 704: the third-order remainder created in sector `j` by
substituting (E.28) into the integrated (E.29). -/
noncomputable def Rsec (ω θi Phi q Yj V : ℝ) : ℝ :=
  Phi * (1 - θi) / 2 * V - (1 + ω) * (1 - θi) / 2 * Yj * V +
    (1 + ω) * (1 - θi) ^ 2 / 8 * V ^ 2 + ω * q * (1 - θi) / 2 * V

/-- Woodford (2003), App. E.6, p. 704 (the display after (E.29), exact): substituting (E.28),
`TvSec = (1 − Φ)Ŷ_j + ½(1 + ω)Ŷ_j² − ωq_jŶ_j + ½(θ⁻¹ + ω) V_j + R_j`. -/
theorem TvSec_E28 (ω θi Phi q Yj V : ℝ) :
    TvSec ω Phi q (meanE28 θi Yj V) V =
      (1 - Phi) * Yj + (1 + ω) / 2 * Yj ^ 2 - ω * q * Yj + (θi + ω) / 2 * V +
        Rsec ω θi Phi q Yj V := by
  unfold TvSec meanE28 Rsec; ring

/-- Woodford (2003), eq. (E.27), p. 703: `Ŷ − (n₁Ŷ₁ + n₂Ŷ₂)` according to the exact Taylor
polynomial of the aggregator (`upperCES_taylor`, `upperCES_E27`):
`η⁻¹n₁n₂ d (Ŷ₂ − Ŷ₁) + ½n₁n₂(1 − η⁻¹)(Ŷ₂ − Ŷ₁)² + τ`. -/
noncomputable def ET (ηi n1 d Y1 Y2 τ : ℝ) : ℝ :=
  ηi * n1 * (1 - n1) * d * (Y2 - Y1) + n1 * (1 - n1) * (1 - ηi) / 2 * (Y2 - Y1) ^ 2 + τ

/-- Woodford (2003), (E.6) and p. 705 (corrected, see `natural_rates`): the natural rate of
output `Ŷⁿ = (σ⁻¹g + ω(n₁q₁ + n₂q₂))/(σ⁻¹ + ω)`. -/
noncomputable def natY (σi ω n1 g q1 q2 : ℝ) : ℝ :=
  (σi * g + ω * (n1 * q1 + (1 - n1) * q2)) / (σi + ω)

/-- Woodford (2003), p. 705: the natural relative output
`Ŷ₂ⁿ − Ŷ₁ⁿ = (η⁻¹ d + ω(q₂ − q₁))/(η⁻¹ + ω)`. -/
noncomputable def natD (ηi ω d q1 q2 : ℝ) : ℝ := (ηi * d + ω * (q2 - q1)) / (ηi + ω)

/-- Woodford (2003), (E.31), p. 705: the terms independent of policy, an explicit function of
the exogenous variables `g, q_j, d, τ, Φ` only. -/
noncomputable def tip610 (σi ω ηi n1 Phi g q1 q2 d τ : ℝ) : ℝ :=
  (Phi + σi * g + ω * (n1 * q1 + (1 - n1) * q2)) ^ 2 / (2 * (σi + ω)) +
    n1 * (1 - n1) * (ηi * d + ω * (q2 - q1)) ^ 2 / (2 * (ηi + ω)) + τ

/-- Woodford (2003), (E.31), p. 705: the explicit remainder `O(‖Φ, ŷ, ξ̃‖³)` of the two-sector
welfare approximation, in terms of `n₁Ŷ₁ + n₂Ŷ₂`, `ET` and the sectoral remainders. -/
noncomputable def R610 (ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ : ℝ) : ℝ :=
  -Phi * ET ηi n1 d Y1 Y2 τ + (1 + ω) * (n1 * Y1 + (1 - n1) * Y2) * ET ηi n1 d Y1 Y2 τ +
    (1 + ω) / 2 * ET ηi n1 d Y1 Y2 τ ^ 2 - ω * (n1 * q1 + (1 - n1) * q2) * ET ηi n1 d Y1 Y2 τ -
    (n1 * Rsec ω θi Phi q1 Y1 V1 + (1 - n1) * Rsec ω θi Phi q2 Y2 V2)

/-- Woodford (2003), **(E.30)–(E.31)**, pp. 704–705 (**Layer A of Proposition 6.10**): with the
aggregate `Ŷ = n₁Ŷ₁ + n₂Ŷ₂ + ET` (the exact second-order aggregator) and the sectoral means
from (E.28), the second-order utility `Tu(Ŷ) − ∑_j n_j TvSec_j` equals
`−½[(σ⁻¹ + ω)(Ŷ − Ŷⁿ − x*)² + n₁n₂(η⁻¹ + ω)(x_R)² + (θ⁻¹ + ω)∑ n_j V_j] + t.i.p. + R`,
where `x_R = (Ŷ₂ − Ŷ₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ)`, the t.i.p. `tip610` depends on exogenous variables only
and the remainder `R610` has weighted degree three (`R610_scale`). -/
theorem prop_6_10_layerA {σi ω θi ηi n1 : ℝ} (hσω : σi + ω ≠ 0) (hηω : ηi + ω ≠ 0)
    {Y Y1 Y2 V1 V2 g q1 q2 d τ Phi : ℝ} (hY : Y = n1 * Y1 + (1 - n1) * Y2 + ET ηi n1 d Y1 Y2 τ) :
    Tu σi g Y - (n1 * TvSec ω Phi q1 (meanE28 θi Y1 V1) V1 +
        (1 - n1) * TvSec ω Phi q2 (meanE28 θi Y2 V2) V2) =
      -((σi + ω) * (Y - natY σi ω n1 g q1 q2 - xStarLin σi ω Phi) ^ 2 +
          n1 * (1 - n1) * (ηi + ω) * ((Y2 - Y1) - natD ηi ω d q1 q2) ^ 2 +
          (θi + ω) * (n1 * V1 + (1 - n1) * V2)) / 2 +
        tip610 σi ω ηi n1 Phi g q1 q2 d τ + R610 ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ := by
  rw [TvSec_E28, TvSec_E28, hY]
  unfold Tu natY xStarLin natD tip610 R610 ET
  field_simp
  ring

/-- Woodford (2003), App. E.6: `ET` has weighted degree two. -/
theorem ET_scale (ηi n1 d Y1 Y2 τ s : ℝ) :
    ET ηi n1 (s * d) (s * Y1) (s * Y2) (s ^ 2 * τ) = s ^ 2 * ET ηi n1 d Y1 Y2 τ := by
  unfold ET; ring

/-- Woodford (2003), App. E.6: the rescaled sectoral remainder, `Rsec(s·) = s³ RsecHat s`. -/
noncomputable def RsecHat (s ω θi Phi q Yj V : ℝ) : ℝ :=
  Phi * (1 - θi) / 2 * V - (1 + ω) * (1 - θi) / 2 * Yj * V +
    s * ((1 + ω) * (1 - θi) ^ 2 / 8 * V ^ 2) + ω * q * (1 - θi) / 2 * V

/-- Woodford (2003), App. E.6 (**scaling lemma**): `R_j` has weighted degree at least three. -/
theorem Rsec_scale (ω θi Phi q Yj V s : ℝ) :
    Rsec ω θi (s * Phi) (s * q) (s * Yj) (s ^ 2 * V) = s ^ 3 * RsecHat s ω θi Phi q Yj V := by
  unfold Rsec RsecHat; ring

/-- Woodford (2003), App. E.6: the rescaled remainder of Proposition 6.10,
`R610(s·) = s³ R610Hat s`. -/
noncomputable def R610Hat (s ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ : ℝ) : ℝ :=
  -Phi * ET ηi n1 d Y1 Y2 τ + (1 + ω) * (n1 * Y1 + (1 - n1) * Y2) * ET ηi n1 d Y1 Y2 τ +
    s * ((1 + ω) / 2 * ET ηi n1 d Y1 Y2 τ ^ 2) -
    ω * (n1 * q1 + (1 - n1) * q2) * ET ηi n1 d Y1 Y2 τ -
    (n1 * RsecHat s ω θi Phi q1 Y1 V1 + (1 - n1) * RsecHat s ω θi Phi q2 Y2 V2)

/-- Woodford (2003), (E.31), p. 705 (**scaling lemma**, the meaning of `O(‖Φ, ŷ, ξ̃‖³)`):
scaling every weight-one variable by `s` and every weight-two variable by `s²` scales the
remainder by `s³` times a polynomial in `s`. -/
theorem R610_scale (ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ s : ℝ) :
    R610 ω θi ηi n1 (s * Phi) (s * q1) (s * q2) (s * Y1) (s * Y2) (s ^ 2 * V1) (s ^ 2 * V2)
        (s * d) (s ^ 2 * τ) =
      s ^ 3 * R610Hat s ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ := by
  unfold R610 R610Hat
  rw [ET_scale, Rsec_scale, Rsec_scale]
  ring

/-- Woodford (2003), (E.31), p. 705: along any scaled family the remainder is `O(s³)`. -/
theorem R610_isBigO (ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ : ℝ) :
    (fun s : ℝ => R610 ω θi ηi n1 (s * Phi) (s * q1) (s * q2) (s * Y1) (s * Y2) (s ^ 2 * V1)
      (s ^ 2 * V2) (s * d) (s ^ 2 * τ)) =O[𝓝 0] fun s => s ^ 3 := by
  refine OneParamTaylor.isBigO_cube_of_scaling
    (fun s => R610_scale ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ s) ?_
  apply Continuous.continuousAt
  unfold R610Hat RsecHat; fun_prop

/-- Woodford (2003), p. 705 (the natural rates "defined in Chapter 3"): under flexible prices
each sector's relative price equals its real marginal cost,
`p̂_jⁿ = ω(Ŷ_jⁿ − q_j) + σ⁻¹(Ŷⁿ − g)`, the relative prices satisfy `n₁p̂₁ⁿ + n₂p̂₂ⁿ = 0`, and
sectoral demand is `Ŷ_jⁿ = φ̂_j + Ŷⁿ − η p̂_jⁿ` with `φ̂₁ = S − n₂d`, `φ̂₂ = S + n₁d`. Then
`(σ⁻¹ + ω)Ŷⁿ = σ⁻¹g + ω(n₁q₁ + n₂q₂) − ωS` and `(η⁻¹ + ω)(Ŷ₂ⁿ − Ŷ₁ⁿ) = η⁻¹d + ω(q₂ − q₁)`.
(`S` is second order, `abs_S_le`; the printed first display omits the factor `ω`, see
`printed_natY_iff`.) -/
theorem natural_rates {σi ω η n1 g q1 q2 S d Yn Y1n Y2n p1n p2n : ℝ} (hη : η ≠ 0)
    (hf1 : ω * (Y1n - q1) + σi * (Yn - g) = p1n) (hf2 : ω * (Y2n - q2) + σi * (Yn - g) = p2n)
    (hidx : n1 * p1n + (1 - n1) * p2n = 0)
    (hd1 : Y1n = S - (1 - n1) * d + Yn - η * p1n) (hd2 : Y2n = S + n1 * d + Yn - η * p2n) :
    (σi + ω) * Yn = σi * g + ω * (n1 * q1 + (1 - n1) * q2) - ω * S ∧
      (η⁻¹ + ω) * (Y2n - Y1n) = η⁻¹ * d + ω * (q2 - q1) := by
  constructor
  · linear_combination n1 * hf1 + (1 - n1) * hf2 - ω * n1 * hd1 - ω * (1 - n1) * hd2 +
      (1 + ω * η) * hidx
  · have h1 : p2n - p1n = η⁻¹ * (S + n1 * d + Yn - Y2n - (S - (1 - n1) * d + Yn - Y1n)) := by
      rw [hd1, hd2]; field_simp; ring
    have h2 : ω * (Y2n - Y1n) - ω * (q2 - q1) = p2n - p1n := by linear_combination hf2 - hf1
    rw [h1] at h2
    linear_combination h2

/-- Woodford (2003), p. 705 (**misprint**): the printed display `(σ⁻¹ + ω)Ŷⁿ = σ⁻¹g + ∑ n_j q_j`
agrees with the natural rate (`natural_rates`, with `S = 0`) only when `ω = 1` or
`n₁q₁ + n₂q₂ = 0`; the correct display is `(σ⁻¹ + ω)Ŷⁿ = σ⁻¹g + ω ∑ n_j q_j`, consistent with
(E.6). -/
theorem printed_natY_iff {σi ω n1 g q1 q2 Yn : ℝ}
    (hYn : (σi + ω) * Yn = σi * g + ω * (n1 * q1 + (1 - n1) * q2)) :
    (σi + ω) * Yn = σi * g + (n1 * q1 + (1 - n1) * q2) ↔
      ω = 1 ∨ n1 * q1 + (1 - n1) * q2 = 0 := by
  rw [hYn]
  constructor
  · intro h
    have : (ω - 1) * (n1 * q1 + (1 - n1) * q2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · left; linarith
    · right; exact h'
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- Woodford (2003), **Proposition 6.10**, eq. (4.24), p. 436 and (E.26), p. 703 (**Layer A**):
using the sectoral demands `Ŷ₂ − Ŷ₁ = d − η p̂_R` and `Ŷ₂ⁿ − Ŷ₁ⁿ = d − η p̂_Rⁿ` (Chapter 3,
p. 204) and the within-sector demands `log y(i) = log Y_j − θ(log p(i) − log P_j)` (so
`V_j = θ² var_iʲ log p`, `Moments.crossVar_affine`), the second-order utility is
`−½[(σ⁻¹ + ω)(x − x*)² + n₁n₂η(1 + ωη)(p̂_R − p̂_Rⁿ)² + θ(1 + ωθ)∑ n_j var_iʲ log p]`
`+ t.i.p. + R`, with `R` of weighted degree three. -/
theorem prop_6_10 {σ ω θ η n1 : ℝ} (hσω : σ⁻¹ + ω ≠ 0) (hη : 0 < η) (hηω : η⁻¹ + ω ≠ 0)
    (hθ : θ ≠ 0) {Y Y1 Y2 Vp1 Vp2 g q1 q2 d τ Phi pR pRn : ℝ}
    (hY : Y = n1 * Y1 + (1 - n1) * Y2 + ET η⁻¹ n1 d Y1 Y2 τ) (hD : Y2 - Y1 = d - η * pR)
    (hDn : natD η⁻¹ ω d q1 q2 = d - η * pRn) :
    Tu σ⁻¹ g Y - (n1 * TvSec ω Phi q1 (meanE28 θ⁻¹ Y1 (θ ^ 2 * Vp1)) (θ ^ 2 * Vp1) +
        (1 - n1) * TvSec ω Phi q2 (meanE28 θ⁻¹ Y2 (θ ^ 2 * Vp2)) (θ ^ 2 * Vp2)) =
      -((σ⁻¹ + ω) * (Y - natY σ⁻¹ ω n1 g q1 q2 - xStarLin σ⁻¹ ω Phi) ^ 2 +
          n1 * (1 - n1) * η * (1 + ω * η) * (pR - pRn) ^ 2 +
          θ * (1 + ω * θ) * (n1 * Vp1 + (1 - n1) * Vp2)) / 2 +
        tip610 σ⁻¹ ω η⁻¹ n1 Phi g q1 q2 d τ +
        R610 ω θ⁻¹ η⁻¹ n1 Phi q1 q2 Y1 Y2 (θ ^ 2 * Vp1) (θ ^ 2 * Vp2) d τ := by
  rw [prop_6_10_layerA hσω hηω hY, hD, hDn]
  have h1 : (η⁻¹ + ω) * (d - η * pR - (d - η * pRn)) ^ 2 = η * (1 + ω * η) * (pR - pRn) ^ 2 := by
    field_simp; ring
  have h2 : (θ⁻¹ + ω) * (n1 * (θ ^ 2 * Vp1) + (1 - n1) * (θ ^ 2 * Vp2)) =
      θ * (1 + ω * θ) * (n1 * Vp1 + (1 - n1) * Vp2) := by
    field_simp
  have h3 : n1 * (1 - n1) * (η⁻¹ + ω) * (d - η * pR - (d - η * pRn)) ^ 2 =
      n1 * (1 - n1) * η * (1 + ω * η) * (pR - pRn) ^ 2 := by
    rw [mul_assoc (n1 * (1 - n1)), h1]; ring
  rw [h3, h2]

/-- Woodford (2003), (E.31)→(E.26), p. 705 (conversion of the dispersion term):
`(θ⁻¹ + ω)θ² = θ(1 + ωθ)`. -/
theorem dispersion_coeff {θ ω : ℝ} (hθ : θ ≠ 0) : (θ⁻¹ + ω) * θ ^ 2 = θ * (1 + ω * θ) := by
  field_simp

/-- Woodford (2003), (E.31)→(E.26), p. 705 (conversion of the relative-price term):
`n₁n₂(η⁻¹ + ω)η² = n₁n₂η(1 + ωη)` (survey check). -/
theorem relprice_coeff {η ω n1 : ℝ} (hη : η ≠ 0) :
    n1 * (1 - n1) * (η⁻¹ + ω) * η ^ 2 = n1 * (1 - n1) * η * (1 + ω * η) := by
  field_simp

/-! ### Discounted sums of bounded sequences -/

/-! ### The sectoral Proposition 6.3 ("the same steps as in the proof of Proposition 6.3") -/

/-- Woodford (2003), App. E.7, p. 706: the sectoral dispersion recursion
`Δ_t = α Δ_{t−1} + α/(1 − α) π̄_t²` (with `Δ_{−1}` given), summed with discount factor `β`:
`∑ βᵗ Δ_t = α/((1 − α)(1 − αβ)) ∑ βᵗ π̄_t² + αΔ_{−1}/(1 − αβ)` — the second term is t.i.p.
(it depends only on the initial dispersion). Exact, for bounded sequences. -/
theorem dispersion_tsum {α β Δm1 : ℝ} {Δ pb : ℕ → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hΔ : Bdd Δ) (hpb : Bdd pb)
    (h0 : Δ 0 = α * Δm1 + α / (1 - α) * pb 0 ^ 2)
    (hs : ∀ t, Δ (t + 1) = α * Δ t + α / (1 - α) * pb (t + 1) ^ 2) :
    ∑' t, β ^ t * Δ t =
      α / ((1 - α) * (1 - α * β)) * ∑' t, β ^ t * pb t ^ 2 + α * Δm1 / (1 - α * β) := by
  have hab : 0 < 1 - α * β := by nlinarith
  have h1a : (1 : ℝ) - α ≠ 0 := by linarith
  obtain ⟨M, hM⟩ := hΔ.lagS Δm1
  obtain ⟨N, hN⟩ := hpb.pow 2
  have h := Sequences.dispersion_tsum (β := β) (k := α / (1 - α)) (p := fun t => pb t ^ 2)
    (by rw [abs_of_nonneg hβ0]; exact hβ1) hM hN (fun t => by
      cases t with
      | zero => simpa using h0
      | succ t => simpa using hs t)
  simp only [lagS_succ, lagS_zero] at h
  set S := ∑' t, β ^ t * pb t ^ 2
  rw [show α / ((1 - α) * (1 - α * β)) * S + α * Δm1 / (1 - α * β) =
    (α * Δm1 + α / (1 - α) * S) / (1 - α * β) by field_simp; ring, eq_div_iff hab.ne']
  linarith

/-- Woodford (2003), App. E.2, p. 695 and E.7: with the second-order price index
`log P_t = P̄_t + ½(1 − θ)Δ_t` (`ces_taylor` with `r = 1 − θ`), the inflation rate
`π_t = log P_t − log P_{t−1}` differs from `π̄_t = P̄_t − P̄_{t−1}` by
`½(1 − θ)(Δ_t − Δ_{t−1})`, a second-order term. -/
theorem infl_discrepancy {θ lP lPm Pb Pbm Δ Δm : ℝ} (h : lP = Pb + (1 - θ) / 2 * Δ)
    (hm : lPm = Pbm + (1 - θ) / 2 * Δm) :
    Pb - Pbm = (lP - lPm) - (1 - θ) / 2 * (Δ - Δm) := by
  rw [h, hm]; ring

/-- Woodford (2003), App. E.7, p. 706 (the bound on the residual): if `|π| ≤ ε ≤ 1` and the
discrepancy `e = π̄ − π` satisfies `|e| ≤ Cε²`, then `|π̄² − π²| ≤ C(2 + C)ε³`. -/
theorem sq_discrepancy_le {π e ε C : ℝ} (hπ : |π| ≤ ε) (he : |e| ≤ C * ε ^ 2) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) : |(π + e) ^ 2 - π ^ 2| ≤ C * (2 + C) * ε ^ 3 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hπ
  have hfac : (π + e) ^ 2 - π ^ 2 = e * (2 * π + e) := by ring
  rw [hfac, abs_mul]
  have h2 : |2 * π + e| ≤ 2 * ε + C * ε ^ 2 := by
    calc |2 * π + e| ≤ |2 * π| + |e| := abs_add_le _ _
      _ = 2 * |π| + |e| := by rw [abs_mul, abs_two]
      _ ≤ 2 * ε + C * ε ^ 2 := by linarith
  have hεε : ε ^ 2 ≤ ε := by nlinarith
  have h3 : 2 * ε + C * ε ^ 2 ≤ (2 + C) * ε := by nlinarith [mul_le_mul_of_nonneg_left hεε hC]
  calc |e| * |2 * π + e| ≤ (C * ε ^ 2) * ((2 + C) * ε) :=
        mul_le_mul he (h2.trans h3) (abs_nonneg _) (by positivity)
    _ = C * (2 + C) * ε ^ 3 := by ring

/-! ### Proposition 6.11 -/

/-- Woodford (2003), Proposition 6.11, p. 437: `κ ≡ (n₁κ₁⁻¹ + n₂κ₂⁻¹)⁻¹`. -/
noncomputable def kappaH (n1 κ1 κ2 : ℝ) : ℝ := (n1 / κ1 + (1 - n1) / κ2)⁻¹

/-- Woodford (2003), Proposition 6.11, p. 437: the weight `w_j ≡ n_j κ/κ_j`. -/
noncomputable def wJ (nj κj κ : ℝ) : ℝ := nj * κ / κj

/-- Woodford (2003), Proposition 6.11, p. 437: `λ_x ≡ κ/θ`. -/
noncomputable def lamX (κ θ : ℝ) : ℝ := κ / θ

/-- Woodford (2003), Proposition 6.11, p. 437: `λ_R ≡ n₁n₂η(1 + ωη)λ_x/(σ⁻¹ + ω)`. -/
noncomputable def lamR (n1 η ω σi κ θ : ℝ) : ℝ :=
  n1 * (1 - n1) * η * (1 + ω * η) / (σi + ω) * lamX κ θ

/-- Woodford (2003), eq. (4.25), p. 437: the period loss
`L = w₁π₁² + w₂π₂² + λ_x(x − x*)² + λ_R(p̂_R − p̂_Rⁿ)²`. -/
def loss425 (w1 w2 lx lR π1 π2 x xs gR : ℝ) : ℝ :=
  w1 * π1 ^ 2 + w2 * π2 ^ 2 + lx * (x - xs) ^ 2 + lR * gR ^ 2

/-- Woodford (2003), Proposition 6.11, p. 437: `w₁ + w₂ = 1`. -/
theorem wJ_sum {n1 κ1 κ2 : ℝ} (hd : n1 / κ1 + (1 - n1) / κ2 ≠ 0) :
    wJ n1 κ1 (kappaH n1 κ1 κ2) + wJ (1 - n1) κ2 (kappaH n1 κ1 κ2) = 1 := by
  unfold wJ kappaH
  rw [show n1 * (n1 / κ1 + (1 - n1) / κ2)⁻¹ / κ1 + (1 - n1) * (n1 / κ1 + (1 - n1) / κ2)⁻¹ / κ2
    = (n1 / κ1 + (1 - n1) / κ2)⁻¹ * (n1 / κ1 + (1 - n1) / κ2) by ring]
  exact inv_mul_cancel₀ hd

/-- Woodford (2003), Proposition 6.11, p. 437: `κ > 0` for `0 ≤ n₁ ≤ 1`, `κ_j > 0`. -/
theorem kappaH_pos {n1 κ1 κ2 : ℝ} (hn0 : 0 ≤ n1) (hn1 : n1 ≤ 1) (hκ1 : 0 < κ1) (hκ2 : 0 < κ2) :
    0 < kappaH n1 κ1 κ2 := by
  unfold kappaH
  apply inv_pos.mpr
  rcases eq_or_lt_of_le hn0 with h | h
  · rw [← h]; simp [hκ2]
  · have : 0 ≤ (1 - n1) / κ2 := div_nonneg (by linarith) hκ2.le
    have : 0 < n1 / κ1 := div_pos h hκ1
    linarith

/-- Woodford (2003), Proposition 6.11, p. 437: `w_j > 0`, `λ_x > 0`, `λ_R > 0`. -/
theorem weights_pos {n1 κ1 κ2 θ η ω σi : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hκ1 : 0 < κ1)
    (hκ2 : 0 < κ2) (hθ : 0 < θ) (hη : 0 < η) (hωη : 0 < 1 + ω * η) (hσω : 0 < σi + ω) :
    0 < wJ n1 κ1 (kappaH n1 κ1 κ2) ∧ 0 < wJ (1 - n1) κ2 (kappaH n1 κ1 κ2) ∧
      0 < lamX (kappaH n1 κ1 κ2) θ ∧ 0 < lamR n1 η ω σi (kappaH n1 κ1 κ2) θ := by
  have hκ := kappaH_pos hn0.le hn1.le hκ1 hκ2
  have hn2 : 0 < 1 - n1 := by linarith
  unfold wJ lamR lamX
  refine ⟨by positivity, by positivity, by positivity, by positivity⟩

/-- Woodford (2003), App. E.7, p. 706 (the Calvo coefficient): with `κ_j` from Proposition 3.8,
`θ(1 + ωθ) α_j/((1 − α_j)(1 − α_jβ)) = θ(σ⁻¹ + ω)/κ_j`. -/
theorem calvo_coeff {α β ω θ σi : ℝ} (hα : α ≠ 0) (h1α : 1 - α ≠ 0) (h1αβ : 1 - α * β ≠ 0)
    (hωσ : ω + σi ≠ 0) :
    θ * (1 + ω * θ) * (α / ((1 - α) * (1 - α * β))) = θ * (σi + ω) / calvoKappa α β ω θ σi := by
  unfold calvoKappa
  field_simp
  ring

/-- Woodford (2003), **Proposition 6.11**, eq. (4.25), p. 437 and (E.32), p. 706 (**Layer A,
discounted form**). Suppose the period utility is Proposition 6.10's quadratic form (`hU`, in
units with `K = Ȳu_c`, plus a t.i.p. sequence `tipU` and a remainder `R`), and the sectoral
dispersions obey the exact Calvo recursions `Δ_{j,t} = α_jΔ_{j,t−1} + α_j/(1 − α_j) π̄_{j,t}²`
(`Moments.mix_var`, `calvo_recursion`). Then for bounded sequences
`∑ βᵗU_t = −Ω ∑ βᵗ L_t + T.I.P. + REM`, with `L_t` the loss (4.25) with the weights `w_j`,
`λ_x = κ/θ`, `λ_R`, `Ω = (K/2)θ(σ⁻¹ + ω)/κ > 0`, T.I.P. depending only on `tipU` and the initial
dispersions `Δ_{j,−1}`, and
REM `= ∑ βᵗR_t − (K/2)θ(σ⁻¹ + ω)∑_j (n_j/κ_j)∑ βᵗ(π̄_{j,t}² − π_{j,t}²)`,
third order by `sq_discrepancy_le` and `infl_discrepancy`. -/
theorem prop_6_11 {K σi ω θ η n1 β α1 α2 xs Δ1m Δ2m : ℝ}
    {U x gR π1 π2 pb1 pb2 Δ1 Δ2 tipU R : ℕ → ℝ}
    (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hn0 : 0 < n1) (hn1 : n1 < 1) (hθ : 0 < θ) (hωθ : 0 < 1 + ω * θ)
    (hσω : 0 < σi + ω)
    (hU : ∀ t, U t = -K / 2 * ((σi + ω) * (x t - xs) ^ 2 +
        n1 * (1 - n1) * η * (1 + ω * η) * gR t ^ 2 +
        θ * (1 + ω * θ) * (n1 * Δ1 t + (1 - n1) * Δ2 t)) + tipU t + R t)
    (h10 : Δ1 0 = α1 * Δ1m + α1 / (1 - α1) * pb1 0 ^ 2)
    (h1s : ∀ t, Δ1 (t + 1) = α1 * Δ1 t + α1 / (1 - α1) * pb1 (t + 1) ^ 2)
    (h20 : Δ2 0 = α2 * Δ2m + α2 / (1 - α2) * pb2 0 ^ 2)
    (h2s : ∀ t, Δ2 (t + 1) = α2 * Δ2 t + α2 / (1 - α2) * pb2 (t + 1) ^ 2)
    (hx : Bdd x) (hgR : Bdd gR) (hπ1 : Bdd π1) (hπ2 : Bdd π2) (hpb1 : Bdd pb1)
    (hpb2 : Bdd pb2) (hΔ1 : Bdd Δ1) (hΔ2 : Bdd Δ2) (htip : Bdd tipU) (hR : Bdd R) :
    let κ1 := calvoKappa α1 β ω θ σi
    let κ2 := calvoKappa α2 β ω θ σi
    let κ := kappaH n1 κ1 κ2
    ∑' t, β ^ t * U t =
      -(K / 2 * (θ * (σi + ω) / κ)) * ∑' t, β ^ t * loss425 (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ)
          (lamX κ θ) (lamR n1 η ω σi κ θ) (π1 t) (π2 t) (x t) xs (gR t) +
        (∑' t, β ^ t * tipU t - K / 2 * (θ * (1 + ω * θ)) *
          (n1 * (α1 * Δ1m / (1 - α1 * β)) + (1 - n1) * (α2 * Δ2m / (1 - α2 * β)))) +
        (∑' t, β ^ t * R t - K / 2 * (θ * (σi + ω)) *
          (n1 / κ1 * ∑' t, β ^ t * (pb1 t ^ 2 - π1 t ^ 2) +
            (1 - n1) / κ2 * ∑' t, β ^ t * (pb2 t ^ 2 - π2 t ^ 2))) := by
  intro κ1 κ2 κ
  have hβa1 : α1 * β < 1 := by nlinarith
  have hβa2 : α2 * β < 1 := by nlinarith
  have hk1 : 0 < κ1 := by
    simp only [κ1, calvoKappa]
    have : 0 < 1 - α1 * β := by linarith
    have : 0 < 1 - α1 := by linarith
    have : 0 < ω + σi := by linarith
    positivity
  have hk2 : 0 < κ2 := by
    simp only [κ2, calvoKappa]
    have : 0 < 1 - α2 * β := by linarith
    have : 0 < 1 - α2 := by linarith
    have : 0 < ω + σi := by linarith
    positivity
  have hk : 0 < κ := kappaH_pos hn0.le hn1.le hk1 hk2
  have c1 : θ * (1 + ω * θ) * (α1 / ((1 - α1) * (1 - α1 * β))) = θ * (σi + ω) / κ1 :=
    calvo_coeff (θ := θ) ha10.ne' (by linarith : (1 : ℝ) - α1 ≠ 0)
    (by linarith : (1 : ℝ) - α1 * β ≠ 0) (by linarith : ω + σi ≠ 0)
  have c2 : θ * (1 + ω * θ) * (α2 / ((1 - α2) * (1 - α2 * β))) = θ * (σi + ω) / κ2 :=
    calvo_coeff (θ := θ) ha20.ne' (by linarith : (1 : ℝ) - α2 ≠ 0)
    (by linarith : (1 : ℝ) - α2 * β ≠ 0) (by linarith : ω + σi ≠ 0)
  have d1 := dispersion_tsum (β := β) ha10.le ha11 hβ0 hβ1 hΔ1 hpb1 h10 h1s
  have d2 := dispersion_tsum (β := β) ha20.le ha21 hβ0 hβ1 hΔ2 hpb2 h20 h2s
  -- summability of the pieces
  have sL : Summable fun t => β ^ t * loss425 (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ) (lamX κ θ)
      (lamR n1 η ω σi κ θ) (π1 t) (π2 t) (x t) xs (gR t) := by
    have hb : Bdd fun t => loss425 (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ) (lamX κ θ)
        (lamR n1 η ω σi κ θ) (π1 t) (π2 t) (x t) xs (gR t) := by
      have h1 := ((hπ1.pow 2).lin (hπ2.pow 2) (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ))
      have h2 := (((hx.lin (Bdd.const xs) 1 (-1)).pow 2).lin (hgR.pow 2) (lamX κ θ)
        (lamR n1 η ω σi κ θ))
      convert h1.lin h2 1 1 using 2 with t
      unfold loss425; ring
    exact hb.summable hβ0 hβ1
  have sT := htip.summable hβ0 hβ1
  have sR := hR.summable hβ0 hβ1
  have sD1 := hΔ1.summable hβ0 hβ1
  have sD2 := hΔ2.summable hβ0 hβ1
  have sP1 := (hπ1.pow 2).summable hβ0 hβ1
  have sP2 := (hπ2.pow 2).summable hβ0 hβ1
  have sQ1 := (hpb1.pow 2).summable hβ0 hβ1
  have sQ2 := (hpb2.pow 2).summable hβ0 hβ1
  -- the pointwise identity
  set Ω := K / 2 * (θ * (σi + ω) / κ) with hΩ
  set c1' := α1 / ((1 - α1) * (1 - α1 * β)) with hc1'
  set c2' := α2 / ((1 - α2) * (1 - α2 * β)) with hc2'
  have hw1 : Ω * wJ n1 κ1 κ = K / 2 * (θ * (1 + ω * θ)) * n1 * c1' := by
    have e : Ω * wJ n1 κ1 κ = K / 2 * n1 * (θ * (σi + ω) / κ1) := by
      rw [hΩ]; unfold wJ; field_simp
    rw [e, ← c1]; ring
  have hw2 : Ω * wJ (1 - n1) κ2 κ = K / 2 * (θ * (1 + ω * θ)) * (1 - n1) * c2' := by
    have e : Ω * wJ (1 - n1) κ2 κ = K / 2 * (1 - n1) * (θ * (σi + ω) / κ2) := by
      rw [hΩ]; unfold wJ; field_simp
    rw [e, ← c2]; ring
  have hlx : Ω * lamX κ θ = K / 2 * (σi + ω) := by
    rw [hΩ]; unfold lamX; field_simp
  have hlr : Ω * lamR n1 η ω σi κ θ = K / 2 * (n1 * (1 - n1) * η * (1 + ω * η)) := by
    rw [hΩ]; unfold lamR lamX; field_simp
  have hpt : ∀ t, β ^ t * U t =
      -Ω * (β ^ t * loss425 (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ) (lamX κ θ) (lamR n1 η ω σi κ θ)
          (π1 t) (π2 t) (x t) xs (gR t)) + β ^ t * tipU t + β ^ t * R t -
        K / 2 * (θ * (1 + ω * θ)) * (n1 * (β ^ t * Δ1 t - c1' * (β ^ t * π1 t ^ 2)) +
          (1 - n1) * (β ^ t * Δ2 t - c2' * (β ^ t * π2 t ^ 2))) := by
    intro t
    rw [hU t]
    unfold loss425
    linear_combination (β ^ t * (x t - xs) ^ 2) * hlx + (β ^ t * gR t ^ 2) * hlr +
      (β ^ t * π1 t ^ 2) * hw1 + (β ^ t * π2 t ^ 2) * hw2
  have H := (((sL.hasSum.mul_left (-Ω)).add sT.hasSum).add sR.hasSum).sub
    ((((sD1.hasSum.sub (sP1.hasSum.mul_left c1')).mul_left n1).add
      ((sD2.hasSum.sub (sP2.hasSum.mul_left c2')).mul_left (1 - n1))).mul_left
        (K / 2 * (θ * (1 + ω * θ))))
  rw [funext hpt, H.tsum_eq, d1, d2]
  have t1 : ∑' t, β ^ t * (pb1 t ^ 2 - π1 t ^ 2) =
      ∑' t, β ^ t * pb1 t ^ 2 - ∑' t, β ^ t * π1 t ^ 2 := by
    rw [← sQ1.tsum_sub sP1]; congr 1; funext t; ring
  have t2 : ∑' t, β ^ t * (pb2 t ^ 2 - π2 t ^ 2) =
      ∑' t, β ^ t * pb2 t ^ 2 - ∑' t, β ^ t * π2 t ^ 2 := by
    rw [← sQ2.tsum_sub sP2]; congr 1; funext t; ring
  rw [t1, t2]
  linear_combination (-(K / 2 * n1 * (∑' t, β ^ t * pb1 t ^ 2 - ∑' t, β ^ t * π1 t ^ 2))) * c1 -
    (K / 2 * (1 - n1) * (∑' t, β ^ t * pb2 t ^ 2 - ∑' t, β ^ t * π2 t ^ 2)) * c2

/-- Woodford (2003), App. E.7, p. 706 (the residual of (2.21)): if `|π_t| ≤ ε ≤ 1` and
`|π̄_t − π_t| ≤ Cε²` for all `t`, the discrepancy term of `prop_6_11` is third order:
`|∑ βᵗ(π̄_t² − π_t²)| ≤ C(2 + C)ε³/(1 − β)`. -/
theorem rem_discrepancy_le {π pb : ℕ → ℝ} {ε C β : ℝ} (hπ : ∀ t, |π t| ≤ ε)
    (he : ∀ t, |pb t - π t| ≤ C * ε ^ 2) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    |∑' t, β ^ t * (pb t ^ 2 - π t ^ 2)| ≤ C * (2 + C) * ε ^ 3 / (1 - β) := by
  refine abs_tsum_le (fun t => ?_) hβ0 hβ1
  have := sq_discrepancy_le (hπ t) (he t) hε1 hC
  rwa [add_sub_cancel] at this

/-! ### `κ` is a weighted harmonic mean (survey error 23) -/

/-- Woodford (2003), Proposition 6.11, p. 437: `κ = (n₁κ₁⁻¹ + n₂κ₂⁻¹)⁻¹` is the weighted
**harmonic** mean of `κ₁, κ₂`; it lies between them. -/
theorem kappaH_mem {n1 κ1 κ2 : ℝ} (hn0 : 0 ≤ n1) (hn1 : n1 ≤ 1) (hκ1 : 0 < κ1) (hκ2 : 0 < κ2) :
    min κ1 κ2 ≤ kappaH n1 κ1 κ2 ∧ kappaH n1 κ1 κ2 ≤ max κ1 κ2 := by
  have hm : 0 < min κ1 κ2 := lt_min hκ1 hκ2
  have hM : 0 < max κ1 κ2 := lt_max_of_lt_left hκ1
  have hS : 0 < n1 / κ1 + (1 - n1) / κ2 := by
    have := kappaH_pos hn0 hn1 hκ1 hκ2; unfold kappaH at this; exact inv_pos.mp this
  have hlo : n1 / κ1 + (1 - n1) / κ2 ≤ 1 / min κ1 κ2 := by
    have e1 : 1 / κ1 ≤ 1 / min κ1 κ2 := one_div_le_one_div_of_le hm (min_le_left _ _)
    have e2 : 1 / κ2 ≤ 1 / min κ1 κ2 := one_div_le_one_div_of_le hm (min_le_right _ _)
    have : n1 / κ1 + (1 - n1) / κ2 = n1 * (1 / κ1) + (1 - n1) * (1 / κ2) := by ring
    rw [this]; nlinarith
  have hhi : 1 / max κ1 κ2 ≤ n1 / κ1 + (1 - n1) / κ2 := by
    have e1 : 1 / max κ1 κ2 ≤ 1 / κ1 := one_div_le_one_div_of_le hκ1 (le_max_left _ _)
    have e2 : 1 / max κ1 κ2 ≤ 1 / κ2 := one_div_le_one_div_of_le hκ2 (le_max_right _ _)
    have : n1 / κ1 + (1 - n1) / κ2 = n1 * (1 / κ1) + (1 - n1) * (1 / κ2) := by ring
    rw [this]; nlinarith
  unfold kappaH
  constructor
  · rw [← one_div]; rw [le_div_iff₀ hS]
    calc min κ1 κ2 * (n1 / κ1 + (1 - n1) / κ2) ≤ min κ1 κ2 * (1 / min κ1 κ2) :=
          mul_le_mul_of_nonneg_left hlo hm.le
      _ = 1 := by field_simp
  · rw [← one_div, div_le_iff₀ hS]
    calc 1 = max κ1 κ2 * (1 / max κ1 κ2) := by field_simp
      _ ≤ max κ1 κ2 * (n1 / κ1 + (1 - n1) / κ2) := mul_le_mul_of_nonneg_left hhi hM.le

/-- Woodford (2003), Proposition 6.11, p. 437 (**survey error 23**): the weighted harmonic mean
is strictly below the weighted geometric mean `κ₁^{n₁} κ₂^{n₂}` unless `κ₁ = κ₂`
(`0 < n₁ < 1`, `κ_j > 0`), so `κ` is not "a geometric average" of `κ₁, κ₂`. -/
theorem kappaH_lt_geom {n1 κ1 κ2 : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hκ1 : 0 < κ1)
    (hκ2 : 0 < κ2) (hne : κ1 ≠ κ2) : kappaH n1 κ1 κ2 < κ1 ^ n1 * κ2 ^ (1 - n1) := by
  have hn2 : 0 < 1 - n1 := by linarith
  have key := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
    ![n1, 1 - n1] ![κ1⁻¹, κ2⁻¹] (fun i _ => by fin_cases i <;> simp [hn0, hn2])
    (by simp [Fin.sum_univ_two])
    (fun i _ => by fin_cases i <;> simp [hκ1.le, hκ2.le])).mpr
    ⟨0, Finset.mem_univ _, 1, Finset.mem_univ _, by simp [inv_inj, hne]⟩
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at key
  rw [Real.inv_rpow hκ1.le, Real.inv_rpow hκ2.le, ← mul_inv] at key
  have hG : 0 < κ1 ^ n1 * κ2 ^ (1 - n1) :=
    mul_pos (Real.rpow_pos_of_pos hκ1 _) (Real.rpow_pos_of_pos hκ2 _)
  have hS : n1 * κ1⁻¹ + (1 - n1) * κ2⁻¹ = n1 / κ1 + (1 - n1) / κ2 := by ring
  rw [hS] at key
  unfold kappaH
  rw [← inv_inv (κ1 ^ n1 * κ2 ^ (1 - n1))]
  exact inv_strictAnti₀ (inv_pos.mpr hG) key

/-- Woodford (2003), Proposition 6.11, p. 437 (**survey error 23, counterexample**): with
`n₁ = n₂ = ½`, `κ₁ = 1`, `κ₂ = 4` the printed "geometric average" `κ₁^{n₁}κ₂^{n₂} = 2` differs
from `κ = (½·1 + ½·¼)⁻¹ = 8/5`. -/
theorem printed_geometric_average_false :
    kappaH (1 / 2) 1 4 = 8 / 5 ∧
      kappaH (1 / 2) 1 4 ≠ (1 : ℝ) ^ (1 / 2 : ℝ) * 4 ^ (1 - 1 / 2 : ℝ) := by
  refine ⟨by unfold kappaH; norm_num, ?_⟩
  exact (kappaH_lt_geom (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num)).ne

/-- Woodford (2003), Proposition 6.11, p. 437: the weights in terms of the inverse slopes,
`w_j = n_jκ_j⁻¹/(n₁κ₁⁻¹ + n₂κ₂⁻¹)` (an identity). -/
theorem wJ_eq_inv (n1 κ1 κ2 : ℝ) :
    wJ n1 κ1 (kappaH n1 κ1 κ2) = n1 * κ1⁻¹ / (n1 * κ1⁻¹ + (1 - n1) * κ2⁻¹) ∧
      wJ (1 - n1) κ2 (kappaH n1 κ1 κ2) = (1 - n1) * κ2⁻¹ / (n1 * κ1⁻¹ + (1 - n1) * κ2⁻¹) := by
  unfold wJ kappaH
  constructor <;> ring

/-! ### Equal stickiness (pp. 438–439) -/

/-- Woodford (2003), p. 438: when `α₁ = α₂` (so `κ₁ = κ₂ = κ̄`) the weights are `w_j = n_j` and
`κ = κ̄`. -/
theorem equal_stickiness_weights {n1 k : ℝ} (hk : k ≠ 0) :
    kappaH n1 k k = k ∧ wJ n1 k (kappaH n1 k k) = n1 ∧
      wJ (1 - n1) k (kappaH n1 k k) = 1 - n1 := by
  have hκ : kappaH n1 k k = k := by unfold kappaH; field_simp; ring
  refine ⟨hκ, ?_, ?_⟩ <;> rw [hκ] <;> unfold wJ <;> field_simp

/-- Woodford (2003), p. 438 (the printed rewrite, `n₁ = n₂ = ½`):
`½a² + ½b² = ((a + b)/2)² + ¼(a − b)²`. -/
theorem half_sq_identity (a b : ℝ) :
    a ^ 2 / 2 + b ^ 2 / 2 = ((a + b) / 2) ^ 2 + (a - b) ^ 2 / 4 := by ring

/-- Woodford (2003), p. 438 (general sector sizes): `n₁a² + n₂b² = (n₁a + n₂b)² + n₁n₂(a − b)²`
(`n₂ = 1 − n₁`). -/
theorem weighted_sq_identity (n1 a b : ℝ) :
    n1 * a ^ 2 + (1 - n1) * b ^ 2 = (n1 * a + (1 - n1) * b) ^ 2 + n1 * (1 - n1) * (a - b) ^ 2 := by
  ring

/-- Woodford (2003), p. 438 (the equal-stickiness loss, corrected): with `w_j = n_j` and
`π₂ − π₁ = p̂_R − p̂_{R,−1}` (Chapter 3, (2.28)), the loss (4.25) is
`π² + n₁n₂(p̂_R − p̂_{R,−1})² + λ_x(x − x*)² + λ_R(p̂_R − p̂_Rⁿ)²`, `π = n₁π₁ + n₂π₂`. -/
theorem loss_equal_stickiness {n1 lx lR π1 π2 x xs gR pR pRm : ℝ} (h228 : π2 - π1 = pR - pRm) :
    loss425 n1 (1 - n1) lx lR π1 π2 x xs gR =
      (n1 * π1 + (1 - n1) * π2) ^ 2 + n1 * (1 - n1) * (pR - pRm) ^ 2 + lx * (x - xs) ^ 2 +
        lR * gR ^ 2 := by
  unfold loss425
  rw [← h228]; ring

/-- Woodford (2003), p. 438 (**imprecision**): the printed `w₁ = w₂ = 0.5` and the coefficient
`¼` on `(p̂_R − p̂_{R,−1})²` require equal sector sizes: with equal stickiness `w₁ = w₂ = ½`
iff `n₁ = ½`, and `n₁n₂ = ¼` iff `n₁ = ½`. -/
theorem printed_half_weights_iff {n1 k : ℝ} (hk : k ≠ 0) :
    (wJ n1 k (kappaH n1 k k) = 1 / 2 ↔ n1 = 1 / 2) ∧ (n1 * (1 - n1) = 1 / 4 ↔ n1 = 1 / 2) := by
  obtain ⟨-, h1, -⟩ := equal_stickiness_weights (n1 := n1) hk
  refine ⟨by rw [h1], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩⟩
  have : (n1 - 1 / 2) ^ 2 = 0 := by linear_combination -h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-! ### Sectoral Phillips curves: gap targeting, the Aoki limit, equal stickiness -/

/-- Woodford (2003), **Proposition 3.8**, p. 203 (restated from the Chapter 3 project):
`γ₁ = n₂(1 − α₁)(1 − α₁β)/α₁ · (1 + ωη)/(1 + ωθ)`. -/
noncomputable def gamma1 (n1 α1 β ω θ η : ℝ) : ℝ :=
  (1 - n1) * ((1 - α1) * (1 - α1 * β) / α1) * ((1 + ω * η) / (1 + ω * θ))

/-- Woodford (2003), **Proposition 3.8**, p. 203 (restated from the Chapter 3 project):
`γ₂ = −n₁(1 − α₂)(1 − α₂β)/α₂ · (1 + ωη)/(1 + ωθ)`. -/
noncomputable def gamma2 (n1 α2 β ω θ η : ℝ) : ℝ :=
  -n1 * ((1 - α2) * (1 - α2 * β) / α2) * ((1 + ω * η) / (1 + ω * θ))

/-- Woodford (2003), p. 442: `γ_j/κ_j` does not depend on the stickiness of sector `j`:
`γ₁/κ₁ = n₂(1 + ωη)/(ω + σ⁻¹)` and `γ₂/κ₂ = −n₁(1 + ωη)/(ω + σ⁻¹)`. -/
theorem gamma_div_kappa {n1 α1 α2 β ω θ η σi : ℝ}
    (h1 : (1 - α1) * (1 - α1 * β) / α1 ≠ 0) (h2 : (1 - α2) * (1 - α2 * β) / α2 ≠ 0)
    (hωθ : 1 + ω * θ ≠ 0) (hωσ : ω + σi ≠ 0) :
    gamma1 n1 α1 β ω θ η / calvoKappa α1 β ω θ σi = (1 - n1) * (1 + ω * η) / (ω + σi) ∧
      gamma2 n1 α2 β ω θ η / calvoKappa α2 β ω θ σi = -n1 * (1 + ω * η) / (ω + σi) := by
  unfold gamma1 gamma2 calvoKappa
  generalize (1 - α1) * (1 - α1 * β) / α1 = X1 at h1 ⊢
  generalize (1 - α2) * (1 - α2 * β) / α2 = X2 at h2 ⊢
  constructor <;> field_simp

/-- Woodford (2003), p. 442: with `w_j = n_jκ/κ_j`, `w₁κ₁ + w₂κ₂ = κ` and `w₁γ₁ + w₂γ₂ = 0`. -/
theorem weighted_slopes {n1 α1 α2 β ω θ η σi : ℝ}
    (h1 : (1 - α1) * (1 - α1 * β) / α1 ≠ 0) (h2 : (1 - α2) * (1 - α2 * β) / α2 ≠ 0)
    (hωθ : 1 + ω * θ ≠ 0) (hωσ : ω + σi ≠ 0) :
    let κ1 := calvoKappa α1 β ω θ σi
    let κ2 := calvoKappa α2 β ω θ σi
    let κ := kappaH n1 κ1 κ2
    wJ n1 κ1 κ * κ1 + wJ (1 - n1) κ2 κ * κ2 = κ ∧
      wJ n1 κ1 κ * gamma1 n1 α1 β ω θ η + wJ (1 - n1) κ2 κ * gamma2 n1 α2 β ω θ η = 0 := by
  intro κ1 κ2 κ
  have hk1 : κ1 ≠ 0 := by
    simp only [κ1, calvoKappa]; exact mul_ne_zero h1 (div_ne_zero hωσ hωθ)
  have hk2 : κ2 ≠ 0 := by
    simp only [κ2, calvoKappa]; exact mul_ne_zero h2 (div_ne_zero hωσ hωθ)
  obtain ⟨g1, g2⟩ := gamma_div_kappa (n1 := n1) (η := η) h1 h2 hωθ hωσ
  constructor
  · unfold wJ; field_simp; ring
  · have e1 : wJ n1 κ1 κ * gamma1 n1 α1 β ω θ η = n1 * κ * (gamma1 n1 α1 β ω θ η / κ1) := by
      unfold wJ; ring
    have e2 : wJ (1 - n1) κ2 κ * gamma2 n1 α2 β ω θ η =
        (1 - n1) * κ * (gamma2 n1 α2 β ω θ η / κ2) := by
      unfold wJ; ring
    rw [e1, e2, g1, g2]; ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 442 (**gap targeting**): multiplying the sectoral Phillips curves
(2.27) of Chapter 3, `π_j = κ_j x + γ_j(p̂_R − p̂_Rⁿ) + β E_t π_{j,t+1}`, by `w_j` and summing
gives `π̄_t = κ x_t + β E_t π̄_{t+1}` with `π̄ = w₁π₁ + w₂π₂`. -/
theorem gap_targeting_pc {n1 α1 α2 β ω θ η σi : ℝ}
    (h1 : (1 - α1) * (1 - α1 * β) / α1 ≠ 0) (h2 : (1 - α2) * (1 - α2 * β) / α2 ≠ 0)
    (hωθ : 1 + ω * θ ≠ 0) (hωσ : ω + σi ≠ 0) {π1 π2 x gR : ℕ → Ω → ℝ}
    (hpc1 : ∀ t, π1 t = calvoKappa α1 β ω θ σi • x t + gamma1 n1 α1 β ω θ η • gR t +
      β • 𝔼.E t (π1 (t + 1)))
    (hpc2 : ∀ t, π2 t = calvoKappa α2 β ω θ σi • x t + gamma2 n1 α2 β ω θ η • gR t +
      β • 𝔼.E t (π2 (t + 1))) (t : ℕ) :
    let κ := kappaH n1 (calvoKappa α1 β ω θ σi) (calvoKappa α2 β ω θ σi)
    let w1 := wJ n1 (calvoKappa α1 β ω θ σi) κ
    let w2 := wJ (1 - n1) (calvoKappa α2 β ω θ σi) κ
    w1 • π1 t + w2 • π2 t = κ • x t + β • 𝔼.E t (w1 • π1 (t + 1) + w2 • π2 (t + 1)) := by
  intro κ w1 w2
  obtain ⟨hk, hg⟩ := weighted_slopes (n1 := n1) (η := η) h1 h2 hωθ hωσ
  funext o
  have e1 := congrFun (hpc1 t) o
  have e2 := congrFun (hpc2 t) o
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul] at e1 e2 ⊢
  rw [e1, e2]
  linear_combination (x t o) * hk + (gR t o) * hg

/-- Woodford (2003), p. 442: "output-gap stabilization is equivalent to stabilization of `π̄`":
for `κ ≠ 0`, `|β| < 1` and bounded `π̄` satisfying `π̄_t = κx_t + βE_tπ̄_{t+1}`,
`x ≡ 0 ⟺ π̄ ≡ 0`. -/
theorem gap_iff_pibar {κ β : ℝ} (hκ : κ ≠ 0) (hβ : |β| < 1) {pibar x : ℕ → Ω → ℝ}
    (hb : BoundedProc pibar) (hpc : ∀ t, pibar t = κ • x t + β • 𝔼.E t (pibar (t + 1))) :
    (∀ t, x t = 0) ↔ ∀ t, pibar t = 0 := by
  constructor
  · intro hx
    have h1 : ∀ t, pibar t = β • 𝔼.E t (pibar (t + 1)) + 0 := fun t => by
      rw [hpc t, hx t]; simp [add_comm]
    have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
      simp
    have := 𝔼.forward_unique hβ h1 h0 hb ⟨0, fun _ _ => by simp⟩
    intro t; rw [this]; rfl
  · intro hp t
    have h := hpc t
    rw [hp t, hp (t + 1), map_zero, smul_zero, add_zero] at h
    funext o
    have := congrFun h o
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    have := (mul_eq_zero.mp this.symm).resolve_left hκ
    simpa using this

/-- Woodford (2003), (4.26), p. 439 and p. 442: the targeting rule with `φ = w₁` stabilises
`π̄ = w₁π₁ + w₂π₂` (since `w₁ + w₂ = 1`). -/
theorem targ_phi_eq_w1 {w1 w2 : ℝ} (hw : w1 + w2 = 1) (π1 π2 : ℝ) :
    w1 * π1 + (1 - w1) * π2 = w1 * π1 + w2 * π2 := by
  rw [show 1 - w1 = w2 by linarith]

/-- Woodford (2003), p. 438: `κ_j⁻¹ = α_j(1 + ωθ)/((1 − α_j)(1 − α_jβ)(ω + σ⁻¹))`
(an identity). -/
theorem kappaJ_inv (α β ω θ σi : ℝ) :
    (calvoKappa α β ω θ σi)⁻¹ = α * (1 + ω * θ) / ((1 - α) * (1 - α * β) * (ω + σi)) := by
  unfold calvoKappa
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- Woodford (2003), p. 438 (**the Aoki limit**, `κ_j⁻¹ = 0 ⟹ w_j = 0`): as prices in sector 1
become fully flexible (`α₁ → 0⁺`, so `κ₁⁻¹ → 0`), `w₁ → 0` and `w₂ → 1`. -/
theorem aoki_weights_tendsto {n1 β ω θ σi κ2 : ℝ} (hn1 : n1 < 1) (hωσ : ω + σi ≠ 0)
    (hκ2 : κ2 ≠ 0) :
    Tendsto (fun α1 => wJ n1 (calvoKappa α1 β ω θ σi) (kappaH n1 (calvoKappa α1 β ω θ σi) κ2))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun α1 => wJ (1 - n1) κ2 (kappaH n1 (calvoKappa α1 β ω θ σi) κ2)) (𝓝[>] 0)
        (𝓝 1) := by
  have hg : Tendsto (fun α : ℝ => (calvoKappa α β ω θ σi)⁻¹) (𝓝 0) (𝓝 0) := by
    simp only [kappaJ_inv]
    have hnum : Tendsto (fun α : ℝ => α * (1 + ω * θ)) (𝓝 0) (𝓝 (0 * (1 + ω * θ))) :=
      tendsto_id.mul_const _
    have hden := (by fun_prop : Continuous fun α : ℝ => (1 - α) * (1 - α * β) * (ω + σi)).tendsto' 0
      ((1 - 0) * (1 - 0 * β) * (ω + σi)) (by simp)
    have := hnum.div hden (by simpa using hωσ)
    rwa [show (0 : ℝ) * (1 + ω * θ) / ((1 - 0) * (1 - 0 * β) * (ω + σi)) = 0 by simp] at this
  have hc : (1 - n1) * κ2⁻¹ ≠ 0 := mul_ne_zero (by linarith) (inv_ne_zero hκ2)
  have hden : Tendsto (fun α : ℝ => n1 * (calvoKappa α β ω θ σi)⁻¹ + (1 - n1) * κ2⁻¹) (𝓝 0)
      (𝓝 (n1 * 0 + (1 - n1) * κ2⁻¹)) := (hg.const_mul n1).add_const _
  constructor
  · have h := ((hg.const_mul n1).div hden (by simpa using hc)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [mul_zero, zero_div] at h
    refine h.congr fun α => ?_
    rw [(wJ_eq_inv n1 _ κ2).1]
    rfl
  · have hconst : Tendsto (fun _ : ℝ => (1 - n1) * κ2⁻¹) (𝓝 0) (𝓝 ((1 - n1) * κ2⁻¹)) :=
      tendsto_const_nhds
    have h := hconst.div hden (by simpa using hc)
    rw [show (1 - n1) * κ2⁻¹ / (n1 * 0 + (1 - n1) * κ2⁻¹) = 1 by
      rw [mul_zero, zero_add]; exact div_self hc] at h
    refine (h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).congr fun α => ?_
    rw [(wJ_eq_inv n1 _ κ2).2]
    rfl

/-- Woodford (2003), p. 438 (**Aoki: the relative-price gap is a multiple of the output gap**):
if sector 1 has flexible prices (its real marginal cost equals its relative price, `s₁ = p̂₁`),
then from Chapter 3's `ŝ₁ − p̂₁ = (ω + σ⁻¹)x − (1 + ωη)(p̂₁ − p̂₁ⁿ)` and `p̂₁ = −n₂p̂_R`,
`p̂₁ⁿ = −n₂p̂_Rⁿ`: `p̂_R − p̂_Rⁿ = −(ω + σ⁻¹)/(n₂(1 + ωη)) · x`, whatever the policy. -/
theorem aoki_relgap {ω σi η n1 x s1 p1 p1n pR pRn : ℝ}
    (hmc : s1 - p1 = (ω + σi) * x - (1 + ω * η) * (p1 - p1n)) (hflex : s1 = p1)
    (hp1 : p1 = -(1 - n1) * pR) (hp1n : p1n = -(1 - n1) * pRn) (hn : 1 - n1 ≠ 0)
    (hωη : 1 + ω * η ≠ 0) :
    pR - pRn = -(ω + σi) / ((1 - n1) * (1 + ω * η)) * x := by
  rw [hflex, sub_self, hp1, hp1n] at hmc
  field_simp
  linear_combination -hmc

/-- Woodford (2003), p. 438: in the Aoki case the relative-price-gap coefficient
`c = −(ω + σ⁻¹)/(n₂(1 + ωη))` and `γ₂` are both negative, so the sticky sector's effective slope
`κ₂ + γ₂c` is positive. -/
theorem aoki_slope_pos {κ2 γ2 c : ℝ} (hκ : 0 < κ2) (hγ : γ2 < 0) (hc : c < 0) :
    0 < κ2 + γ2 * c := by nlinarith

/-- Woodford (2003), p. 438 (**Aoki: one policy stabilises everything**): if the relative-price
gap is `c·x` (`aoki_relgap`) and sector 2's Phillips curve is
`π₂ = κ₂x + γ₂(p̂_R − p̂_Rⁿ) + βE_tπ₂,_{t+1}` with `κ₂ + γ₂c ≠ 0`, `|β| < 1` and bounded `π₂`, then
complete stabilisation of the output gap is equivalent to zero inflation in the sticky sector,
and it also closes the relative-price gap. -/
theorem aoki_policy {κ2 γ2 c β : ℝ} (hβ : |β| < 1) (hdet : κ2 + γ2 * c ≠ 0)
    {π2 x gR : ℕ → Ω → ℝ} (hb : BoundedProc π2) (hgap : ∀ t, gR t = c • x t)
    (hpc : ∀ t, π2 t = κ2 • x t + γ2 • gR t + β • 𝔼.E t (π2 (t + 1))) :
    ((∀ t, x t = 0) ↔ ∀ t, π2 t = 0) ∧ ((∀ t, x t = 0) → ∀ t, gR t = 0) := by
  have hpc' : ∀ t, π2 t = (κ2 + γ2 * c) • x t + β • 𝔼.E t (π2 (t + 1)) := fun t => by
    rw [hpc t, hgap t, smul_smul, ← add_smul]
  refine ⟨gap_iff_pibar 𝔼 hdet hβ hb hpc', fun hx t => by rw [hgap t, hx t, smul_zero]⟩

/-- Woodford (2003), (4.25), p. 437: the loss is nonnegative when its weights are. -/
theorem loss425_nonneg {w1 w2 lx lR : ℝ} (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (hx : 0 ≤ lx) (hR : 0 ≤ lR)
    (π1 π2 x xs gR : ℝ) : 0 ≤ loss425 w1 w2 lx lR π1 π2 x xs gR := by
  unfold loss425; positivity

/-- Woodford (2003), p. 438 (**Aoki: the policy is optimal**): with `w₁ = 0` (flexible sector 1)
and `x* = 0`, the allocation with `π₂ = 0`, `x = 0`, `p̂_R = p̂_Rⁿ` has zero loss, which is the
minimum of the nonnegative loss (4.25) — whatever `π₁` is. -/
theorem aoki_optimal {w2 lx lR : ℝ} (h2 : 0 ≤ w2) (hx : 0 ≤ lx) (hR : 0 ≤ lR) (π1 : ℝ) :
    loss425 0 w2 lx lR π1 0 0 0 0 = 0 ∧
      ∀ π1' π2' x' gR', loss425 0 w2 lx lR π1 0 0 0 0 ≤ loss425 0 w2 lx lR π1' π2' x' 0 gR' := by
  have h0 : loss425 0 w2 lx lR π1 0 0 0 0 = 0 := by unfold loss425; ring
  exact ⟨h0, fun _ _ _ _ => by rw [h0]; exact loss425_nonneg le_rfl h2 hx hR _ _ _ _ _⟩

/-! ### Equal stickiness: the relative price does not depend on policy -/

/-- Woodford (2003), p. 439 (via Chapter 3): the characteristic polynomial
`βλ² − (1 + β + c)λ + 1` has a root `λ₁ ∈ (0, 1)` for `c > 0`. -/
theorem exists_stable_root {β c : ℝ} (hc : 0 < c) :
    ∃ l, 0 < l ∧ l < 1 ∧ β * l ^ 2 - (1 + β + c) * l + 1 = 0 := by
  have hcont : ContinuousOn (fun l : ℝ => β * l ^ 2 - (1 + β + c) * l + 1) (Set.Icc 0 1) := by
    fun_prop
  have h := intermediate_value_Ioo' (zero_le_one' ℝ) hcont
  have hf1 : (fun l : ℝ => β * l ^ 2 - (1 + β + c) * l + 1) 1 < 0 := by
    simp only; nlinarith
  have hf0 : 0 < (fun l : ℝ => β * l ^ 2 - (1 + β + c) * l + 1) 0 := by
    simp only; norm_num
  obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := h ⟨hf1, hf0⟩
  exact ⟨l, hl0, hl1, hl⟩

/-- Woodford (2003), p. 439 (via Chapter 3, (2.27)–(2.28)): **uniqueness** for the
second-order equation `β E_t d_{t+1} = (1 + β + c) d_t − d_{t−1}` with `d_{−1} = 0`: for
`0 ≤ β < 1`, `c > 0`, the only bounded adapted solution is `d ≡ 0`. (Factorisation through the
stable root `λ₁`: `e_t = d_t − λ₁d_{t−1}` satisfies `e_t = βλ₁ E_t e_{t+1}`.) -/
theorem second_order_unique {β c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc : 0 < c)
    {d : ℕ → Ω → ℝ} (hda : 𝔼.Adapted d) (hb : BoundedProc d)
    (h : ∀ t, β • 𝔼.E t (d (t + 1)) = (1 + β + c) • d t - lagP 0 d t) : d = 0 := by
  obtain ⟨l, hl0, hl1, hl⟩ := exists_stable_root (β := β) hc
  set e : ℕ → Ω → ℝ := fun t => d t - l • lagP 0 d t with he
  have hkey : ∀ t, e t = (β * l) • 𝔼.E t (e (t + 1)) + 0 := by
    intro t
    have hE : 𝔼.E t (e (t + 1)) = 𝔼.E t (d (t + 1)) - l • d t := by
      simp only [he, lagP, map_sub, map_smul, hda t]
    rw [hE, add_zero]
    funext o
    have k := congrFun (h t) o
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at k ⊢
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : l * (β * 𝔼.E t (d (t + 1)) o) = l * ((1 + β + c) * d t o - lagP 0 d t o) := by
      rw [k]
    linear_combination (-1 : ℝ) * this + (d t o) * hl
  have heb : BoundedProc e := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M + |l| * M, fun t o => ?_⟩
    have hlag : |lagP 0 d t o| ≤ M := by
      cases t with
      | zero => simp only [lagP, Pi.zero_apply, abs_zero]; exact (abs_nonneg _).trans (hM 0 o)
      | succ t => exact hM t o
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hM t o) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlag (abs_nonneg _)
  have hbl : |β * l| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hβ0 hl0.le)]; nlinarith
  have he0 : e = 0 := 𝔼.forward_unique hbl hkey (fun t => by simp) heb ⟨0, fun _ _ => by simp⟩
  have hd : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero => simpa [he, lagP] using congrFun he0 0
    | succ t ih => simpa [he, lagP, ih] using congrFun he0 (t + 1)
  funext t; exact hd t

/-- Woodford (2003), p. 439 ("the relative price `p̂_Rt` evolves in the same way regardless of
monetary policy"): with equally sticky sectors (`κ₁ = κ₂ = k`), the difference of the two
sectoral Phillips curves and (2.28), `π₂ − π₁ = p̂_R − p̂_{R,−1}`, give a second-order equation
in `p̂_R` alone (`c = γ₁ − γ₂ > 0`); any two bounded adapted equilibria with the same `p̂_{R,−1}`
and the same `p̂_Rⁿ` have the same relative-price path. -/
theorem relPrice_policy_invariant {k γ1 γ2 β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : γ2 < γ1) {pRm1 : Ω → ℝ} {pRn : ℕ → Ω → ℝ}
    {π1 π2 x pR π1' π2' x' pR' : ℕ → Ω → ℝ}
    (h1 : ∀ t, π1 t = k • x t + γ1 • (pR t - pRn t) + β • 𝔼.E t (π1 (t + 1)))
    (h2 : ∀ t, π2 t = k • x t + γ2 • (pR t - pRn t) + β • 𝔼.E t (π2 (t + 1)))
    (h228 : ∀ t, π2 t - π1 t = pR t - lagP pRm1 pR t)
    (h1' : ∀ t, π1' t = k • x' t + γ1 • (pR' t - pRn t) + β • 𝔼.E t (π1' (t + 1)))
    (h2' : ∀ t, π2' t = k • x' t + γ2 • (pR' t - pRn t) + β • 𝔼.E t (π2' (t + 1)))
    (h228' : ∀ t, π2' t - π1' t = pR' t - lagP pRm1 pR' t)
    (ha : 𝔼.Adapted pR) (ha' : 𝔼.Adapted pR') (hb : BoundedProc pR) (hb' : BoundedProc pR') :
    pR = pR' := by
  set d : ℕ → Ω → ℝ := fun t => pR t - pR' t with hd
  have hlag : ∀ t, lagP pRm1 pR t - lagP pRm1 pR' t = lagP 0 d t := by
    intro t; cases t <;> simp [lagP, hd]
  have heq : ∀ t, β • 𝔼.E t (d (t + 1)) = (1 + β + (γ1 - γ2)) • d t - lagP 0 d t := by
    intro t
    have r : ∀ (pRx : ℕ → Ω → ℝ) (p1 p2 xx : ℕ → Ω → ℝ),
        (∀ t, p1 t = k • xx t + γ1 • (pRx t - pRn t) + β • 𝔼.E t (p1 (t + 1))) →
        (∀ t, p2 t = k • xx t + γ2 • (pRx t - pRn t) + β • 𝔼.E t (p2 (t + 1))) →
        (∀ t, p2 t - p1 t = pRx t - lagP pRm1 pRx t) → 𝔼.Adapted pRx →
        pRx t - lagP pRm1 pRx t =
          (γ2 - γ1) • (pRx t - pRn t) + β • (𝔼.E t (pRx (t + 1)) - pRx t) := by
      intro pRx p1 p2 xx e1 e2 e3 hax
      have hE : 𝔼.E t (p2 (t + 1)) - 𝔼.E t (p1 (t + 1)) = 𝔼.E t (pRx (t + 1)) - pRx t := by
        rw [← map_sub, e3 (t + 1)]
        simp only [lagP, map_sub, hax t]
      rw [← e3 t, e2 t, e1 t]
      funext o
      have h0 := congrFun hE o
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 ⊢
      linear_combination β * h0
    have k1 := r pR π1 π2 x h1 h2 h228 ha
    have k2 := r pR' π1' π2' x' h1' h2' h228' ha'
    have hdE : 𝔼.E t (d (t + 1)) = 𝔼.E t (pR (t + 1)) - 𝔼.E t (pR' (t + 1)) := by
      simp [hd, map_sub]
    rw [hdE, ← hlag t]
    funext o
    have e1 := congrFun k1 o
    have e2 := congrFun k2 o
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at e1 e2 ⊢
    simp only [hd, Pi.sub_apply]
    linear_combination e2 - e1
  have hda : 𝔼.Adapted d := fun t => by simp [hd, map_sub, ha t, ha' t]
  have hdb : BoundedProc d := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    exact ⟨M + M', fun t o => (abs_sub _ _).trans (add_le_add (hM t o) (hM' t o))⟩
  have := second_order_unique 𝔼 hβ0 hβ1 (by linarith) hda hdb heq
  funext t o
  have := congrFun (congrFun this t) o
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-- Woodford (2003), pp. 438–439 (**equal stickiness: complete stabilisation of aggregate
inflation is optimal**): with `κ₁ = κ₂ = k > 0`, `w_j = n_j`, `x* = 0` and nonnegative
`λ_x, λ_R`, an equilibrium with `π = n₁π₁ + n₂π₂ ≡ 0` has, date by date and state by state, a
loss (4.25) no larger than any other bounded equilibrium with the same initial relative price. -/
theorem equal_stickiness_optimal {k γ1 γ2 β n1 lx lR : ℝ} (hk : k ≠ 0) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hγ : γ2 < γ1) (hn1 : n1 * γ1 + (1 - n1) * γ2 = 0) (hx : 0 ≤ lx)
    {pRm1 : Ω → ℝ} {pRn : ℕ → Ω → ℝ}
    {π1 π2 x pR π1' π2' x' pR' : ℕ → Ω → ℝ}
    (h1 : ∀ t, π1 t = k • x t + γ1 • (pR t - pRn t) + β • 𝔼.E t (π1 (t + 1)))
    (h2 : ∀ t, π2 t = k • x t + γ2 • (pR t - pRn t) + β • 𝔼.E t (π2 (t + 1)))
    (h228 : ∀ t, π2 t - π1 t = pR t - lagP pRm1 pR t)
    (h1' : ∀ t, π1' t = k • x' t + γ1 • (pR' t - pRn t) + β • 𝔼.E t (π1' (t + 1)))
    (h2' : ∀ t, π2' t = k • x' t + γ2 • (pR' t - pRn t) + β • 𝔼.E t (π2' (t + 1)))
    (h228' : ∀ t, π2' t - π1' t = pR' t - lagP pRm1 pR' t)
    (ha : 𝔼.Adapted pR) (ha' : 𝔼.Adapted pR') (hb : BoundedProc pR) (hb' : BoundedProc pR')
    (hstab : ∀ t, n1 • π1 t + (1 - n1) • π2 t = 0) (t : ℕ) (o : Ω) :
    loss425 n1 (1 - n1) lx lR (π1 t o) (π2 t o) (x t o) 0 (pR t o - pRn t o) ≤
      loss425 n1 (1 - n1) lx lR (π1' t o) (π2' t o) (x' t o) 0 (pR' t o - pRn t o) := by
  have hsame := relPrice_policy_invariant 𝔼 hβ0 hβ1 hγ h1 h2 h228 h1' h2' h228' ha ha' hb hb'
  -- aggregate Phillips curve: n₁π₁ + n₂π₂ = k x + β E(...)
  have hagg : ∀ s, n1 • π1 s + (1 - n1) • π2 s =
      k • x s + β • 𝔼.E s (n1 • π1 (s + 1) + (1 - n1) • π2 (s + 1)) := by
    intro s
    funext o'
    have e1 := congrFun (h1 s) o'
    have e2 := congrFun (h2 s) o'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul, Pi.sub_apply]
      at e1 e2 ⊢
    rw [e1, e2]
    linear_combination (pR s o' - pRn s o') * hn1
  have hx0 : x t o = 0 := by
    have := congrFun (hagg t) o
    rw [hstab t, hstab (t + 1), map_zero, smul_zero, add_zero] at this
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hk
  have hp : n1 * π1 t o + (1 - n1) * π2 t o = 0 := by
    simpa using congrFun (hstab t) o
  have hl : π2 t o - π1 t o = π2' t o - π1' t o := by
    have a := congrFun (h228 t) o
    have b := congrFun (h228' t) o
    simp only [Pi.sub_apply] at a b
    rw [a, b, hsame]
  unfold loss425
  have hw : n1 * π1 t o ^ 2 + (1 - n1) * π2 t o ^ 2 ≤
      n1 * π1' t o ^ 2 + (1 - n1) * π2' t o ^ 2 := by
    rw [weighted_sq_identity n1 (π1 t o), weighted_sq_identity n1 (π1' t o), hp]
    have : π1 t o - π2 t o = π1' t o - π2' t o := by linarith
    rw [this]
    nlinarith [sq_nonneg (n1 * π1' t o + (1 - n1) * π2' t o)]
  rw [hx0, hsame]
  nlinarith [mul_nonneg hx (sq_nonneg (x' t o - 0))]

/-! ### Send-back (1): the Taylor coefficients of `ũ` and `ṽ` as exact derivatives

A primitive `W(X, ξ)` (utility of production `ũ`, disutility of supplying a good `ṽ`, or of
supplying labour `v`) is evaluated along the ray `(X̄ e^{εx}, εξ)` through the steady state
`(X̄, 0)`, `ξ` a direction in the space of disturbances. Its first two derivatives at `ε = 0` are
the Taylor coefficients of (E.2), (E.29), (E.34). -/

/-- Woodford (2003), (E.2)/(E.3)/(E.29)/(E.34) (**exact derivatives along a ray**): if `W` has
partial derivatives `W_X, W_ξ` everywhere (as a Fréchet derivative on `ℝ × ℝ`), and these are
differentiable at `(X̄, 0)` with second partials `W_XX, W_Xξ, W_ξX, W_ξξ`, then
`F(ε) = W(X̄e^{εx}, εξ)` has `F'(ε) = W_X·X̄e^{εx}x + W_ξ·ξ`,
`F'(0) = X̄W_X x + W_ξ ξ` and
`F''(0) = (X̄²W_XX + X̄W_X)x² + X̄(W_Xξ + W_ξX)xξ + W_ξξ ξ²`. -/
theorem ray_taylor {W WX Wξ : ℝ × ℝ → ℝ} {Xbar WXX WXξ WξX Wξξ : ℝ} (x ξ : ℝ)
    (hW : ∀ p, HasFDerivAt W (WX p • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Wξ p • ContinuousLinearMap.snd ℝ ℝ ℝ) p)
    (hWX : HasFDerivAt WX (WXX • ContinuousLinearMap.fst ℝ ℝ ℝ +
      WXξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Xbar, 0))
    (hWξ : HasFDerivAt Wξ (WξX • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Wξξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Xbar, 0)) :
    (∀ ε, HasDerivAt (fun e => W (Xbar * Real.exp (e * x), e * ξ))
      (WX (Xbar * Real.exp (ε * x), ε * ξ) * (Xbar * Real.exp (ε * x) * x) +
        Wξ (Xbar * Real.exp (ε * x), ε * ξ) * ξ) ε) ∧
    HasDerivAt (fun e => WX (Xbar * Real.exp (e * x), e * ξ) * (Xbar * Real.exp (e * x) * x) +
        Wξ (Xbar * Real.exp (e * x), e * ξ) * ξ)
      ((Xbar ^ 2 * WXX + Xbar * WX (Xbar, 0)) * x ^ 2 + Xbar * (WXξ + WξX) * x * ξ +
        Wξξ * ξ ^ 2) 0 := by
  have h1 : ∀ ε, HasDerivAt (fun e => Xbar * Real.exp (e * x)) (Xbar * Real.exp (ε * x) * x) ε :=
    fun ε => ((((hasDerivAt_id ε).mul_const x).exp).const_mul Xbar).congr_deriv (by simp; ring)
  have h2 : ∀ ε, HasDerivAt (fun e : ℝ => e * ξ) ξ ε := fun ε =>
    ((hasDerivAt_id ε).mul_const ξ).congr_deriv (by simp)
  have hγ : ∀ ε, HasDerivAt (fun e => (Xbar * Real.exp (e * x), e * ξ))
      (Xbar * Real.exp (ε * x) * x, ξ) ε := fun ε => (h1 ε).prodMk (h2 ε)
  refine ⟨fun ε => ?_, ?_⟩
  · have := (hW _).comp_hasDerivAt ε (hγ ε)
    refine this.congr_deriv ?_
    simp [smul_eq_mul]
  · have hγ0 : (fun e => (Xbar * Real.exp (e * x), e * ξ)) 0 = (Xbar, 0) := by simp
    have hX := (hγ0 ▸ hWX).comp_hasDerivAt (0 : ℝ) (hγ 0)
    have hξ := (hγ0 ▸ hWξ).comp_hasDerivAt (0 : ℝ) (hγ 0)
    have h1' : HasDerivAt (fun e => Xbar * Real.exp (e * x) * x) (Xbar * Real.exp (0 * x) * x * x)
        0 := (h1 0).mul_const x
    have := (hX.mul h1').add (hξ.mul_const ξ)
    refine this.congr_deriv ?_
    simp [smul_eq_mul]
    ring

/-- Woodford (2003), eq. (E.2), p. 692 (**exact Taylor coefficients of `ũ`**): with
`u_c = W_X(Ȳ, 0)`, `u_cc = W_XX`, `u_cξ ξ = ½(W_Xξ + W_ξX)ξ`, `σ⁻¹ = −Ȳu_cc/u_c` and
`g = −u_cξ ξ/(Ȳu_cc)`, the second-order Taylor polynomial `F'(0) + ½F''(0)` along the ray
`(Ȳe^{εŶ}, εξ)` is `(u_ξξ + ½ξu_ξξξ) + Ȳu_c[Ŷ + ½(1 − σ⁻¹)Ŷ² + σ⁻¹gŶ]`: t.i.p. plus
`Ȳu_c Tu`. -/
theorem uTaylor_coeffs {Ybar uc ucc cross uξ uξξ : ℝ} (hY : Ybar ≠ 0) (huc : uc ≠ 0)
    (hucc : ucc ≠ 0) (Yh ξ : ℝ) :
    (Ybar * uc * Yh + uξ * ξ) +
        ((Ybar ^ 2 * ucc + Ybar * uc) * Yh ^ 2 + Ybar * (2 * cross) * Yh * ξ + uξξ * ξ ^ 2) / 2 =
      (uξ * ξ + uξξ / 2 * ξ ^ 2) +
        Ybar * uc * Tu (-(Ybar * ucc / uc)) (-(cross * ξ / (Ybar * ucc))) Yh := by
  unfold Tu
  field_simp
  ring

/-- Woodford (2003), eq. (E.3)/(E.29), pp. 693–704 (**exact Taylor coefficients of `ṽ`**):
with `ṽ_y = W_X(Ȳ, 0) = (1 − Φ)u_c` (the steady state (2.7)–(2.8)), `ṽ_yy = W_XX`,
`v_yξ ξ = ½(W_Xξ + W_ξX)ξ`, `ω = Ȳṽ_yy/ṽ_y` and `q = −v_yξ ξ/(Ȳṽ_yy)`, the second-order
Taylor polynomial along `(Ȳe^{εŷ}, εξ)` is t.i.p. plus
`Ȳu_c[Tv(ŷ) − Φ(½(1 + ω)ŷ² − ωqŷ)]`; the last term (dropped in (E.3)/(E.29) "given that `Φ` is an
expansion parameter") has weighted degree three. -/
theorem vTaylor_coeffs {Ybar uc vy vyy cross vξ vξξ Phi : ℝ} (hY : Ybar ≠ 0)
    (hvy : vy = (1 - Phi) * uc) (hvy0 : vy ≠ 0) (hvyy : vyy ≠ 0) (yh ξ : ℝ) :
    (Ybar * vy * yh + vξ * ξ) +
        ((Ybar ^ 2 * vyy + Ybar * vy) * yh ^ 2 + Ybar * (2 * cross) * yh * ξ + vξξ * ξ ^ 2) / 2 =
      (vξ * ξ + vξξ / 2 * ξ ^ 2) + Ybar * uc *
        (Tv Phi (Ybar * vyy / vy) (-(cross * ξ / (Ybar * vyy))) yh -
          Phi * ((1 + Ybar * vyy / vy) / 2 * yh ^ 2 -
            Ybar * vyy / vy * (-(cross * ξ / (Ybar * vyy))) * yh)) := by
  have hΦ : (1 - Phi) * uc ≠ 0 := hvy ▸ hvy0
  have h1 : 1 - Phi ≠ 0 := left_ne_zero_of_mul hΦ
  have h2 : uc ≠ 0 := right_ne_zero_of_mul hΦ
  rw [hvy]
  unfold Tv
  field_simp
  ring

/-- Woodford (2003), eq. (E.2), p. 692 (**`ũ` from the primitive**): for `ũ(Y, ξ)` with the
differentiability of `ray_taylor`, `F(ε) = ũ(Ȳe^{εŶ}, εξ)` satisfies
`F'(0) + ½F''(0) = (u_ξξ + ½u_ξξξ²) + Ȳu_c Tu(σ⁻¹, Ŷ, g)` with `u_c = ũ_Y(Ȳ, 0)`,
`σ⁻¹ = −Ȳu_YY/u_c`, `g = −u_cξ ξ/(Ȳu_YY)`, `u_cξ = ½(u_Yξ + u_ξY)`. -/
theorem uTaylor_ray {u uY uξ : ℝ × ℝ → ℝ} {Ybar uYY uYξ uξY uξξ : ℝ} (hY : Ybar ≠ 0)
    (huc : uY (Ybar, 0) ≠ 0) (hucc : uYY ≠ 0) (Yh ξ : ℝ)
    (hu : ∀ p, HasFDerivAt u (uY p • ContinuousLinearMap.fst ℝ ℝ ℝ +
      uξ p • ContinuousLinearMap.snd ℝ ℝ ℝ) p)
    (huY : HasFDerivAt uY (uYY • ContinuousLinearMap.fst ℝ ℝ ℝ +
      uYξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, 0))
    (huξ : HasFDerivAt uξ (uξY • ContinuousLinearMap.fst ℝ ℝ ℝ +
      uξξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, 0)) :
    let F' := fun e => uY (Ybar * Real.exp (e * Yh), e * ξ) * (Ybar * Real.exp (e * Yh) * Yh) +
      uξ (Ybar * Real.exp (e * Yh), e * ξ) * ξ
    let B := (Ybar ^ 2 * uYY + Ybar * uY (Ybar, 0)) * Yh ^ 2 + Ybar * (uYξ + uξY) * Yh * ξ +
      uξξ * ξ ^ 2
    (∀ ε, HasDerivAt (fun e => u (Ybar * Real.exp (e * Yh), e * ξ)) (F' ε) ε) ∧
      HasDerivAt F' B 0 ∧
      F' 0 + B / 2 = (uξ (Ybar, 0) * ξ + uξξ / 2 * ξ ^ 2) + Ybar * uY (Ybar, 0) *
        Tu (-(Ybar * uYY / uY (Ybar, 0))) (-((uYξ + uξY) / 2 * ξ / (Ybar * uYY))) Yh := by
  intro F' B
  obtain ⟨h1, h2⟩ := ray_taylor Yh ξ hu huY huξ
  refine ⟨h1, h2, ?_⟩
  have e := uTaylor_coeffs (cross := (uYξ + uξY) / 2) (uξ := uξ (Ybar, 0)) (uξξ := uξξ) hY huc
    hucc Yh ξ
  simp only [F', B, zero_mul, Real.exp_zero, mul_one]
  rw [← e]; ring

/-- Woodford (2003), eq. (E.29), p. 704 (**`ṽ` from the primitive**): for `ṽ(y, ξʲ)` with the
differentiability of `ray_taylor` and the steady state `ṽ_y(Ȳ, 0) = (1 − Φ)u_c`,
`F'(0) + ½F''(0) = (v_ξξ + ½v_ξξξ²) + Ȳu_c[Tv(ŷ) − Φ(½(1 + ω)ŷ² − ωqŷ)]` with
`ω = Ȳv_yy/v_y` and `q = −v_yξ ξ/(Ȳv_yy)`. -/
theorem vTaylor_ray {v vy vξ : ℝ × ℝ → ℝ} {Ybar uc vyy vyξ vξy vξξ Phi : ℝ} (hY : Ybar ≠ 0)
    (hss : vy (Ybar, 0) = (1 - Phi) * uc) (hvy0 : vy (Ybar, 0) ≠ 0) (hvyy : vyy ≠ 0)
    (yh ξ : ℝ)
    (hv : ∀ p, HasFDerivAt v (vy p • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vξ p • ContinuousLinearMap.snd ℝ ℝ ℝ) p)
    (hvY : HasFDerivAt vy (vyy • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vyξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, 0))
    (hvξ : HasFDerivAt vξ (vξy • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vξξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, 0)) :
    let F' := fun e => vy (Ybar * Real.exp (e * yh), e * ξ) * (Ybar * Real.exp (e * yh) * yh) +
      vξ (Ybar * Real.exp (e * yh), e * ξ) * ξ
    let B := (Ybar ^ 2 * vyy + Ybar * vy (Ybar, 0)) * yh ^ 2 + Ybar * (vyξ + vξy) * yh * ξ +
      vξξ * ξ ^ 2
    let ω := Ybar * vyy / vy (Ybar, 0)
    let q := -((vyξ + vξy) / 2 * ξ / (Ybar * vyy))
    (∀ ε, HasDerivAt (fun e => v (Ybar * Real.exp (e * yh), e * ξ)) (F' ε) ε) ∧
      HasDerivAt F' B 0 ∧
      F' 0 + B / 2 = (vξ (Ybar, 0) * ξ + vξξ / 2 * ξ ^ 2) + Ybar * uc *
        (Tv Phi ω q yh - Phi * ((1 + ω) / 2 * yh ^ 2 - ω * q * yh)) := by
  intro F' B ω q
  obtain ⟨h1, h2⟩ := ray_taylor yh ξ hv hvY hvξ
  refine ⟨h1, h2, ?_⟩
  have e := vTaylor_coeffs (cross := (vyξ + vξy) / 2) (vξ := vξ (Ybar, 0)) (vξξ := vξξ) hY hss
    hvy0 hvyy yh ξ
  simp only [F', B, zero_mul, Real.exp_zero, mul_one]
  rw [← e]; ring

/-- Woodford (2003), (E.29) integrated over sector `j` (with the dropped term kept): the
dropped `Φ × quadratic` terms of a sector, in moments, `Φ(½(1 + ω)(m² + V) − ωqm)`. -/
noncomputable def PhiSec (ω Phi q m V : ℝ) : ℝ :=
  Phi * ((1 + ω) / 2 * (m ^ 2 + V) - ω * q * m)

/-- Woodford (2003), (E.29): the population form of the dropped terms,
`∑ w_i Φ(½(1 + ω)ŷ_i² − ωqŷ_i) = PhiSec(E ŷ, var ŷ)`. -/
theorem sum_PhiTerm {w : ι → ℝ} (hw : ∑ i, w i = 1) (ω Phi q : ℝ) (y : ι → ℝ) :
    ∑ i, w i * (Phi * ((1 + ω) / 2 * y i ^ 2 - ω * q * y i)) =
      PhiSec ω Phi q (crossMean w y) (crossVar w y) := by
  have h : ∀ i, w i * (Phi * ((1 + ω) / 2 * y i ^ 2 - ω * q * y i)) =
      w i * (-(Phi * ω * q) * y i + Phi * (1 + ω) / 2 * y i ^ 2) := fun i => by ring
  simp only [h, mean_quadratic hw]
  unfold PhiSec; ring

/-- Woodford (2003), (E.31) with the exact (E.29): `PhiSec` at `m = meanE28` has weighted degree
three. -/
theorem PhiSec_scale (ω θi Phi q Yj V s : ℝ) :
    PhiSec ω (s * Phi) (s * q) (meanE28 θi (s * Yj) (s ^ 2 * V)) (s ^ 2 * V) =
      s ^ 3 * (Phi * ((1 + ω) / 2 * ((Yj - s * ((1 - θi) / 2 * V)) ^ 2 + V) -
        ω * q * (Yj - s * ((1 - θi) / 2 * V)))) := by
  unfold PhiSec meanE28; ring

/-- Woodford (2003), **Proposition 6.10 from the primitives' Taylor coefficients**: with the
exact (E.29) (`vTaylor_coeffs`: `Tv − Φ × quadratic` per good, integrated with `sum_Tv`,
`sum_PhiTerm`), the identity of `prop_6_10_layerA` holds with the additional remainder
`∑ n_j PhiSec_j`, itself of weighted degree three (`PhiSec_scale`). -/
theorem prop_6_10_exact {σi ω θi ηi n1 : ℝ} (hσω : σi + ω ≠ 0) (hηω : ηi + ω ≠ 0)
    {Y Y1 Y2 V1 V2 g q1 q2 d τ Phi : ℝ} (hY : Y = n1 * Y1 + (1 - n1) * Y2 + ET ηi n1 d Y1 Y2 τ) :
    Tu σi g Y - (n1 * (TvSec ω Phi q1 (meanE28 θi Y1 V1) V1 -
          PhiSec ω Phi q1 (meanE28 θi Y1 V1) V1) +
        (1 - n1) * (TvSec ω Phi q2 (meanE28 θi Y2 V2) V2 -
          PhiSec ω Phi q2 (meanE28 θi Y2 V2) V2)) =
      -((σi + ω) * (Y - natY σi ω n1 g q1 q2 - xStarLin σi ω Phi) ^ 2 +
          n1 * (1 - n1) * (ηi + ω) * ((Y2 - Y1) - natD ηi ω d q1 q2) ^ 2 +
          (θi + ω) * (n1 * V1 + (1 - n1) * V2)) / 2 +
        tip610 σi ω ηi n1 Phi g q1 q2 d τ + (R610 ω θi ηi n1 Phi q1 q2 Y1 Y2 V1 V2 d τ +
          (n1 * PhiSec ω Phi q1 (meanE28 θi Y1 V1) V1 +
            (1 - n1) * PhiSec ω Phi q2 (meanE28 θi Y2 V2) V2)) := by
  have h := prop_6_10_layerA (θi := θi) (ω := ω) (V1 := V1) (V2 := V2) (Phi := Phi) (g := g)
    (q1 := q1) (q2 := q2) hσω hηω hY
  linear_combination h

/-! ### Send-back (2): the Calvo dispersion recursion derived from the Calvo dynamics

The cross-section of (log) prices is a finite weighted list of `(weight, price)` pairs. Each
period the Calvo step keeps every old pair with its weight scaled by `α` and adds the atom
`(1 − α, p*_t)`. The dispersion recursion used by `prop_6_11` and `prop_6_13` is then a theorem
about this process (`calvo_recursion`), with boundedness derived from bounded prices. -/

/-- Woodford (2003), App. E.2: total mass `∑ w` of a weighted list. -/
def lmass (L : List (ℝ × ℝ)) : ℝ := (L.map fun x => x.1).sum

/-- Woodford (2003), App. E.2: `P̄ = ∑ w p`. -/
def lmean (L : List (ℝ × ℝ)) : ℝ := (L.map fun x => x.1 * x.2).sum

/-- Woodford (2003), App. E.2: `∑ w p²`. -/
def lsq (L : List (ℝ × ℝ)) : ℝ := (L.map fun x => x.1 * x.2 ^ 2).sum

/-- Woodford (2003), App. E.2: `Δ = ∑ w p² − P̄²` (the variance when the mass is one,
`lvar_eq_sum`). -/
def lvar (L : List (ℝ × ℝ)) : ℝ := lsq L - lmean L ^ 2

/-- Woodford (2003), App. E.2, p. 695: the Calvo step — old prices kept with probability `α`,
an atom of mass `1 − α` at the new price `p*`. -/
def calvoStep (α pstar : ℝ) (L : List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  (1 - α, pstar) :: L.map fun x => (α * x.1, x.2)

/-- Woodford (2003), App. E.2 (list algebra): `∑ w (p − c)² = ∑ w p² − 2c ∑ w p + c² ∑ w`. -/
theorem lsum_sq_dev (L : List (ℝ × ℝ)) (c : ℝ) :
    (L.map fun x => x.1 * (x.2 - c) ^ 2).sum = lsq L - 2 * c * lmean L + c ^ 2 * lmass L := by
  induction L with
  | nil => simp [lsq, lmean, lmass]
  | cons y L ih =>
    simp only [lsq, lmean, lmass, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

/-- Woodford (2003), App. E.2 (list algebra): `∑ w c = c ∑ w`. -/
theorem lsum_mul_const (L : List (ℝ × ℝ)) (c : ℝ) :
    (L.map fun x => x.1 * c).sum = lmass L * c := by
  induction L with
  | nil => simp [lmass]
  | cons y L ih =>
    simp only [lmass, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

/-- Woodford (2003), App. E.2: `lvar` is the weighted variance `∑ w (p − P̄)²` for unit mass. -/
theorem lvar_eq_sum {L : List (ℝ × ℝ)} (hm : lmass L = 1) :
    lvar L = (L.map fun x => x.1 * (x.2 - lmean L) ^ 2).sum := by
  rw [lsum_sq_dev, hm]; unfold lvar; ring

/-- Woodford (2003), App. E.2: scaling all weights by `α` scales the moments by `α`. -/
theorem lmap_scale (L : List (ℝ × ℝ)) (α : ℝ) :
    lmass (L.map fun x => (α * x.1, x.2)) = α * lmass L ∧
      lmean (L.map fun x => (α * x.1, x.2)) = α * lmean L ∧
      lsq (L.map fun x => (α * x.1, x.2)) = α * lsq L := by
  induction L with
  | nil => simp [lmass, lmean, lsq]
  | cons y L ih =>
    obtain ⟨a, b, c⟩ := ih
    simp only [lmass, lmean, lsq, List.map_cons, List.sum_cons] at a b c ⊢
    exact ⟨by rw [a]; ring, by rw [b]; ring, by rw [c]; ring⟩

/-- Woodford (2003), App. E.2: the Calvo step's moments. -/
theorem calvoStep_moments (α pstar : ℝ) (L : List (ℝ × ℝ)) :
    lmass (calvoStep α pstar L) = (1 - α) + α * lmass L ∧
      lmean (calvoStep α pstar L) = (1 - α) * pstar + α * lmean L ∧
      lsq (calvoStep α pstar L) = (1 - α) * pstar ^ 2 + α * lsq L := by
  obtain ⟨a, b, c⟩ := lmap_scale L α
  unfold calvoStep
  simp only [lmass, lmean, lsq, List.map_cons, List.sum_cons] at a b c ⊢
  exact ⟨by rw [a], by rw [b], by rw [c]⟩

/-- Woodford (2003), eq. (E.8), p. 695 (**exact, on the Calvo process**): for a unit-mass list
and `α ≠ 1`, `Δ⁺ = αΔ + α/(1 − α)(P̄⁺ − P̄)²`, and the mass stays one. -/
theorem calvoStep_var {α : ℝ} (hα : α ≠ 1) (pstar : ℝ) {L : List (ℝ × ℝ)} (hm : lmass L = 1) :
    lmass (calvoStep α pstar L) = 1 ∧
      lvar (calvoStep α pstar L) =
        α * lvar L + α / (1 - α) * (lmean (calvoStep α pstar L) - lmean L) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := calvoStep_moments α pstar L
  refine ⟨by rw [h1, hm]; ring, ?_⟩
  unfold lvar
  have h := Moments.mix_var_meanChange (m := lmean L) (s := lsq L) (d := 0) (p := pstar)
    (m' := lmean (calvoStep α pstar L)) (s' := lsq (calvoStep α pstar L)) hα
    (by rw [h2]; ring) (by rw [h3]; ring)
  simpa only [sub_zero] using h

/-- Woodford (2003), App. E.2/E.7: the Calvo cross-section at date `t`, starting from the
date-`(−1)` cross-section `L0` with reset prices `p*_t`. -/
def calvoPop (α : ℝ) (L0 : List (ℝ × ℝ)) (pstar : ℕ → ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => calvoStep α (pstar 0) L0
  | t + 1 => calvoStep α (pstar (t + 1)) (calvoPop α L0 pstar t)

/-- Woodford (2003), App. E.2: the lagged mean `P̄_{t−1}` (with `P̄_{−1}` from `L0`). -/
noncomputable def lagMean (α : ℝ) (L0 : List (ℝ × ℝ)) (pstar : ℕ → ℝ) : ℕ → ℝ
  | 0 => lmean L0
  | t + 1 => lmean (calvoPop α L0 pstar t)

/-- Woodford (2003), App. E.2/E.7 (**the dispersion recursion as a theorem**): along the Calvo
process, with `Δ_t = lvar(pop_t)` and `π̄_t = P̄_t − P̄_{t−1}`,
`Δ_0 = αΔ_{−1} + α/(1 − α)π̄_0²` and `Δ_{t+1} = αΔ_t + α/(1 − α)π̄_{t+1}²` — exactly the
hypotheses of `dispersion_tsum`, `prop_6_11` and `prop_6_13`. -/
theorem calvo_recursion {α : ℝ} (hα : α ≠ 1) {L0 : List (ℝ × ℝ)} (hm : lmass L0 = 1)
    (pstar : ℕ → ℝ) :
    let Δ := fun t => lvar (calvoPop α L0 pstar t)
    let pb := fun t => lmean (calvoPop α L0 pstar t) - lagMean α L0 pstar t
    Δ 0 = α * lvar L0 + α / (1 - α) * pb 0 ^ 2 ∧
      ∀ t, Δ (t + 1) = α * Δ t + α / (1 - α) * pb (t + 1) ^ 2 := by
  intro Δ pb
  have hmass : ∀ t, lmass (calvoPop α L0 pstar t) = 1 := by
    intro t
    induction t with
    | zero => exact (calvoStep_var hα _ hm).1
    | succ t ih => exact (calvoStep_var hα _ ih).1
  exact ⟨(calvoStep_var hα _ hm).2, fun t => (calvoStep_var hα _ (hmass t)).2⟩

/-- Woodford (2003), App. E.2 (bounds): if all weights are nonnegative, the mass is one and all
prices satisfy `|p| ≤ M`, then `|P̄| ≤ M` and `|Δ| ≤ M²`. -/
theorem lmoments_bound {L : List (ℝ × ℝ)} {M : ℝ} (hw : ∀ x ∈ L, 0 ≤ x.1)
    (hp : ∀ x ∈ L, |x.2| ≤ M) (hm : lmass L = 1) : |lmean L| ≤ M ∧ |lvar L| ≤ M ^ 2 := by
  have hM : ∀ x ∈ L, x.1 * x.2 ≤ x.1 * M ∧ -(x.1 * M) ≤ x.1 * x.2 ∧ x.1 * x.2 ^ 2 ≤ x.1 * M ^ 2 ∧
      0 ≤ x.1 * x.2 ^ 2 := by
    intro x hx
    have h1 := hw x hx
    have h2 := abs_le.mp (hp x hx)
    have h3 : x.2 ^ 2 ≤ M ^ 2 := by
      have := sq_abs x.2 ▸ pow_le_pow_left₀ (abs_nonneg _) (hp x hx) 2; exact this
    exact ⟨mul_le_mul_of_nonneg_left h2.2 h1, by nlinarith, mul_le_mul_of_nonneg_left h3 h1,
      mul_nonneg h1 (sq_nonneg _)⟩
  have hmM : (L.map fun x => x.1 * M).sum = M := by
    rw [lsum_mul_const, hm, one_mul]
  have hmM2 : (L.map fun x => x.1 * M ^ 2).sum = M ^ 2 := by
    rw [lsum_mul_const, hm, one_mul]
  have e1 : lmean L ≤ M := by
    unfold lmean; rw [← hmM]; exact List.sum_le_sum fun x hx => (hM x hx).1
  have e2 : -M ≤ lmean L := by
    unfold lmean
    have : (L.map fun x => x.1 * (-M)).sum = -M := by
      rw [lsum_mul_const, hm, one_mul]
    rw [← this]
    exact List.sum_le_sum fun x hx => by have := (hM x hx).2.1; linarith
  have e3 : lsq L ≤ M ^ 2 := by
    unfold lsq; rw [← hmM2]; exact List.sum_le_sum fun x hx => (hM x hx).2.2.1
  have e4 : 0 ≤ lsq L := by
    unfold lsq; exact List.sum_nonneg fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact (hM x hx).2.2.2
  refine ⟨abs_le.mpr ⟨e2, e1⟩, ?_⟩
  have hv0 : 0 ≤ lvar L := by
    rw [lvar_eq_sum hm]
    exact List.sum_nonneg fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact mul_nonneg (hw x hx) (sq_nonneg _)
  rw [abs_of_nonneg hv0]
  unfold lvar
  nlinarith [sq_nonneg (lmean L)]

/-- Woodford (2003), App. E.2: the Calvo process preserves nonnegative weights, unit mass and
the price bound `M` (when `0 ≤ α ≤ 1` and `|p*_t| ≤ M`). -/
theorem calvoPop_invariants {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L0 : List (ℝ × ℝ)}
    (hw : ∀ x ∈ L0, 0 ≤ x.1) (hp : ∀ x ∈ L0, |x.2| ≤ M) (hm : lmass L0 = 1)
    {pstar : ℕ → ℝ} (hps : ∀ t, |pstar t| ≤ M) (t : ℕ) :
    (∀ x ∈ calvoPop α L0 pstar t, 0 ≤ x.1) ∧ (∀ x ∈ calvoPop α L0 pstar t, |x.2| ≤ M) ∧
      lmass (calvoPop α L0 pstar t) = 1 := by
  have step : ∀ (L : List (ℝ × ℝ)) (q : ℝ), (∀ x ∈ L, 0 ≤ x.1) → (∀ x ∈ L, |x.2| ≤ M) →
      lmass L = 1 → |q| ≤ M → (∀ x ∈ calvoStep α q L, 0 ≤ x.1) ∧
        (∀ x ∈ calvoStep α q L, |x.2| ≤ M) ∧ lmass (calvoStep α q L) = 1 := by
    intro L q hw hp hm hq
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [calvoStep, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · simp; linarith
      · exact mul_nonneg hα0 (hw y hy)
    · intro x hx
      simp only [calvoStep, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact hq
      · exact hp y hy
    · rw [(calvoStep_moments α q L).1, hm]; ring
  induction t with
  | zero => exact step L0 _ hw hp hm (hps 0)
  | succ t ih => exact step _ _ ih.1 ih.2.1 ih.2.2 (hps (t + 1))

/-- Woodford (2003), App. E.2: along the Calvo process with prices bounded by `M`, the
dispersion `Δ_t` and the mean-price inflation `π̄_t` are bounded sequences. -/
theorem calvo_bdd {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L0 : List (ℝ × ℝ)}
    (hw : ∀ x ∈ L0, 0 ≤ x.1) (hp : ∀ x ∈ L0, |x.2| ≤ M) (hm : lmass L0 = 1)
    {pstar : ℕ → ℝ} (hps : ∀ t, |pstar t| ≤ M) :
    Bdd (fun t => lvar (calvoPop α L0 pstar t)) ∧
      Bdd (fun t => lmean (calvoPop α L0 pstar t) - lagMean α L0 pstar t) := by
  have hb := fun t => calvoPop_invariants hα0 hα1 hw hp hm hps t
  have hmb := fun t => lmoments_bound (hb t).1 (hb t).2.1 (hb t).2.2
  have h0 := lmoments_bound hw hp hm
  refine ⟨⟨M ^ 2, fun t => (hmb t).2⟩, ⟨M + M, fun t => ?_⟩⟩
  have hl : |lagMean α L0 pstar t| ≤ M := by
    cases t with
    | zero => exact h0.1
    | succ t => exact (hmb t).1
  exact (abs_sub _ _).trans (add_le_add (hmb t).1 hl)

/-- Woodford (2003), App. E.7 (the per-period remainder, exact): if the log price index is
`log P_t = P̄_t + ½(1 − θ)Δ_t + ρ_t` (`ρ_t` the CES remainder, third order by `ces_taylor`), then
`π̄_t − π_t = −½(1 − θ)(Δ_t − Δ_{t−1}) − (ρ_t − ρ_{t−1})`. -/
theorem infl_discrepancy_rho {θ lP lPm Pb Pbm Δ Δm ρ ρm : ℝ}
    (h : lP = Pb + (1 - θ) / 2 * Δ + ρ) (hm : lPm = Pbm + (1 - θ) / 2 * Δm + ρm) :
    (Pb - Pbm) - (lP - lPm) = -((1 - θ) / 2 * (Δ - Δm)) - (ρ - ρm) := by
  rw [h, hm]; ring

/-- Woodford (2003), **Proposition 6.11 from the Calvo model**: the conclusion of `prop_6_11`
holds with the sectoral dispersions and mean-price inflation rates generated by the Calvo
process in each sector (`calvoPop`, initial cross-sections `L01`, `L02` with nonnegative weights,
unit mass and prices bounded by `M`, reset prices bounded by `M`); the dispersion recursion and
its boundedness are no longer assumed (`calvo_recursion`, `calvo_bdd`). -/
theorem prop_6_11_calvo {K σi ω θ η n1 β α1 α2 xs M : ℝ}
    {U x gR π1 π2 tipU R ps1 ps2 : ℕ → ℝ} {L01 L02 : List (ℝ × ℝ)}
    (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hn0 : 0 < n1) (hn1 : n1 < 1) (hθ : 0 < θ) (hωθ : 0 < 1 + ω * θ)
    (hσω : 0 < σi + ω)
    (hw1 : ∀ z ∈ L01, 0 ≤ z.1) (hp1 : ∀ z ∈ L01, |z.2| ≤ M) (hm1 : lmass L01 = 1)
    (hw2 : ∀ z ∈ L02, 0 ≤ z.1) (hp2 : ∀ z ∈ L02, |z.2| ≤ M) (hm2 : lmass L02 = 1)
    (hps1 : ∀ t, |ps1 t| ≤ M) (hps2 : ∀ t, |ps2 t| ≤ M)
    (hU : ∀ t, U t = -K / 2 * ((σi + ω) * (x t - xs) ^ 2 +
        n1 * (1 - n1) * η * (1 + ω * η) * gR t ^ 2 +
        θ * (1 + ω * θ) * (n1 * lvar (calvoPop α1 L01 ps1 t) +
          (1 - n1) * lvar (calvoPop α2 L02 ps2 t))) + tipU t + R t)
    (hx : Bdd x) (hgR : Bdd gR) (hπ1 : Bdd π1) (hπ2 : Bdd π2) (htip : Bdd tipU) (hR : Bdd R) :
    let κ1 := calvoKappa α1 β ω θ σi
    let κ2 := calvoKappa α2 β ω θ σi
    let κ := kappaH n1 κ1 κ2
    let pb1 := fun t => lmean (calvoPop α1 L01 ps1 t) - lagMean α1 L01 ps1 t
    let pb2 := fun t => lmean (calvoPop α2 L02 ps2 t) - lagMean α2 L02 ps2 t
    ∑' t, β ^ t * U t =
      -(K / 2 * (θ * (σi + ω) / κ)) * ∑' t, β ^ t * loss425 (wJ n1 κ1 κ) (wJ (1 - n1) κ2 κ)
          (lamX κ θ) (lamR n1 η ω σi κ θ) (π1 t) (π2 t) (x t) xs (gR t) +
        (∑' t, β ^ t * tipU t - K / 2 * (θ * (1 + ω * θ)) *
          (n1 * (α1 * lvar L01 / (1 - α1 * β)) + (1 - n1) * (α2 * lvar L02 / (1 - α2 * β)))) +
        (∑' t, β ^ t * R t - K / 2 * (θ * (σi + ω)) *
          (n1 / κ1 * ∑' t, β ^ t * (pb1 t ^ 2 - π1 t ^ 2) +
            (1 - n1) / κ2 * ∑' t, β ^ t * (pb2 t ^ 2 - π2 t ^ 2))) := by
  intro κ1 κ2 κ pb1 pb2
  obtain ⟨r10, r1s⟩ := calvo_recursion (ne_of_lt ha11) hm1 ps1
  obtain ⟨r20, r2s⟩ := calvo_recursion (ne_of_lt ha21) hm2 ps2
  obtain ⟨bΔ1, bp1⟩ := calvo_bdd ha10.le ha11.le hw1 hp1 hm1 hps1
  obtain ⟨bΔ2, bp2⟩ := calvo_bdd ha20.le ha21.le hw2 hp2 hm2 hps2
  exact prop_6_11 ha10 ha11 ha20 ha21 hβ0 hβ1 hn0 hn1 hθ hωθ hσω hU r10 r1s r20 r2s hx hgR
    hπ1 hπ2 bp1 bp2 bΔ1 bΔ2 htip hR

/-! ### Table 6.3 -/

/-- Woodford (2003), Table 6.3, p. 440: with `n₁ = n₂ = ½`, `η = 1`, `ω = .47`, `σ⁻¹ = .16`
(Table 4.1) and `λ_x = .048`, the formula `λ_R = n₁n₂η(1 + ωη)λ_x/(σ⁻¹ + ω)` gives exactly
`λ_R = .028` (both weights carry the same factor 16 of footnote 61, so the ratio is unaffected). -/
theorem table_6_3_lamR :
    (1 / 2 : ℝ) * (1 - 1 / 2) * 1 * (1 + 0.47 * 1) / (0.16 + 0.47) * 0.048 = 0.028 := by
  norm_num

end Woodford.StabilizationWelfare.TwoSectorWelfare
