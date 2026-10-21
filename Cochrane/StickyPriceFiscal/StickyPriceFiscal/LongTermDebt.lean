/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.FiscalNK
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Long-term debt in the sticky-price fiscal-theory model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.2, eqs. (5.17)–(5.21),
pp. 127–129, with Fig. 5.4; Online Appendix A1, §1.3, eqs. (1.21)–(1.25), pp. 561–564, and
§1.10, p. 578.

The bond-portfolio return of a geometric maturity structure is linearised as an **exact
derivative** (A1 (1.22)); its coefficient is `ω̃ = ω/(1 + i)`, which the book then replaces by
`ω` in (1.24) (survey error E23). The model is stated with the exact coefficient `ω̃` (written
`om`), as the survey recommends.

## Main results

* A1 §1.3: `geomQ_hasSum` ((1.23), `Q = 1/(1 + i − ω)`), `ss_ratios`, `bondReturn`,
  `bondReturn_eq`, `bondReturn_hasFDerivAt` ((1.22) as an exact derivative), `bondReturn_ss`
  (value `log(1 + i)` and coefficient `ω/(1 + i)` at the steady state), `e23_coef_lt` (the
  exact coefficient is strictly below `ω` when `ω, i > 0`).
* (5.21) iterated (survey error E22): `bond_iterate`, `bond_price_sum`
  (`q_t = −∑_{j≥1} ω̃^{j−1} r_{t+j}`), `e22_printed_fails`; (1.25): `eq_1_25`.
* The model (5.17)–(5.21): `LTD`, `ltd_iff_eqm`, `bond_price` (the bond price is the forward
  sum of rates), `rnOf`, `ltd_determinate` ("one more explosive root", p. 128: exactly one bounded
  equilibrium).
* The link to one-period debt: `sAdj`, `ltd_to_ftplnk`; irrelevance (p. 129):
  `rn_eq_i_iff_no_news`, `ltd_no_news` (no bond-price news ⇒ the one-period-debt equilibrium),
  `ltd_anticipated_no_news` (deterministic rate paths carry no news), `ltd_fiscal_shock`
  (with `i ≡ 0` the fiscal-shock response is unaltered); survey error E30:
  `ltd_anticipated_moves_before`; `perm_bond_price` (`q ≡ −1/(1 − ω̃)` under a permanent peg).
* Fig. 5.4 (unexpected permanent rise): `ltd_perm_rise` —
  `π_{1+j} = 1 − [(1 − ρ/λ₁)/(1 − ω̃)] λ₁^{−j}` — `ltd_disinflation_iff` (**disinflation on impact
  iff `ω̃ > ρ/λ₁`**), `ltd_strictAnti_om` (longer maturity, lower inflation at every date),
  `ltd_pi0_strictAnti_kappa` (flexible prices, larger decline), `ltd_kappa_atTop`
  (κ → ∞: `π₁ → −ω̃/(1 − ω̃)`, `π_{1+j} → 1`), `ltd_tendsto_one` (inflation eventually rises to
  the new rate: "stepping on a rake").
* (3.20) at p. 129: `eq_3_20`.
* A1 §§1.3, 1.10: `ss_return_indep` (at steady-state prices every maturity structure earns
  `1 + i`), `geom_portfolio_payoff` (the payoff `1 + ωQ_{t+1}` of (1.21)), `a1_1_10` (the
  first-order form of §1.10 under a peg).
* §5.3, a persistent (AR(1)) rise `i_t = ηᵗ`: `ar1A`, `ar1C`, `ltd_ar1` (closed form),
  `ar1_impact` (impact response), `ar1_impact_rho_eq_beta`, `ar1_disinflation_iff_rho_eq_beta`
  (with `ρ = β`: impact disinflation iff `ω̃ > ρ/λ₁`, for every persistence `η`),
  `ar1_magnitude_rho_eq_beta` (persistence magnifies the disinflation),
  `ar1_short_debt_no_disinflation`.
* The calibration of Fig. 5.4: `fig54_impact` (π₁ ≈ −1.49 for the caption's `ω = 0.85` with the
  exact weight, −2.62 for `ω = 0.9`; −0.90 for the text's `ω = 0.8`, survey error E29; −1.63
  with (1.24)'s weight, E23), `fig54_flexible` (κ = ∞: −85/16 vs −17/3).
-/

namespace Cochrane.StickyPriceFiscal.LongTermDebt

open Filter Topology NKModel TwoSidedMA FiscalNK

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### A1 §1.3: the geometric maturity structure -/

/-- Cochrane (2023), A1 eq. (1.23), p. 563: the steady-state price of the geometric portfolio,
`Q = ∑_{j≥1} ω^{j−1}/(1 + i)ʲ = 1/(1 + i − ω)`, for `0 ≤ ω < 1 + i`. -/
theorem geomQ_hasSum {ω i : ℝ} (hi : 0 < 1 + i) (hω0 : 0 ≤ ω) (hω : ω < 1 + i) :
    HasSum (fun j : ℕ => ω ^ j / (1 + i) ^ (j + 1)) (1 / (1 + i - ω)) := by
  have h := ForwardSolution.hasSum_geometric_ratio (A := 1 + i) (B := ω) 1
    (by rw [abs_of_nonneg hω0, abs_of_pos hi]; exact hω)
  simpa using h

/-- Cochrane (2023), A1 p. 563: at `Q = 1/(1 + i − ω)`, `(1 + ωQ)/Q = 1 + i` and
`ωQ/(1 + ωQ) = ω/(1 + i)`. -/
theorem ss_ratios {ω i : ℝ} (hi : 0 < 1 + i) (hω : ω < 1 + i) :
    (1 + ω * (1 / (1 + i - ω))) / (1 / (1 + i - ω)) = 1 + i ∧
      ω * (1 / (1 + i - ω)) / (1 + ω * (1 / (1 + i - ω))) = ω / (1 + i) := by
  have h1 : 1 + i - ω ≠ 0 := by linarith
  have h2 : 1 + i ≠ 0 := hi.ne'
  constructor
  · field_simp; ring
  · have h3 : 1 + i - ω + ω ≠ 0 := by rw [sub_add_cancel]; exact h2
    field_simp
    ring_nf

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the log return of the geometric bond portfolio,
`r^n_{t+1} = log(1 + ω Q_{t+1}) − log Q_t`, as a function of the log price deviations
`(q̃_{t+1}, q̃_t)` around the steady-state price `Q`. -/
noncomputable def bondReturn (ω Q : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.log (1 + ω * (Q * Real.exp p.1)) - Real.log (Q * Real.exp p.2)

/-- Cochrane (2023), A1 eq. (1.22): `r^n_{t+1} = log(1 + ωQe^{q̃_{t+1}}) − log Q − q̃_t` exactly. -/
theorem bondReturn_eq {ω Q : ℝ} (hQ : 0 < Q) (p : ℝ × ℝ) :
    bondReturn ω Q p = Real.log (1 + ω * (Q * Real.exp p.1)) - Real.log Q - p.2 := by
  unfold bondReturn
  rw [Real.log_mul hQ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Cochrane (2023), A1 eq. (1.22), p. 563, **as an exact derivative**: for `ω ≥ 0`, `Q > 0`,
the return map has derivative `(dq̃_{t+1}, dq̃_t) ↦ ωQ/(1 + ωQ) dq̃_{t+1} − dq̃_t` at the
steady state. -/
theorem bondReturn_hasFDerivAt {ω Q : ℝ} (hω : 0 ≤ ω) (hQ : 0 < Q) :
    HasFDerivAt (bondReturn ω Q)
      ((ω * Q / (1 + ω * Q)) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)
      (0, 0) := by
  have hpos : 0 < 1 + ω * Q := by positivity
  have hg : HasDerivAt (fun a => Real.log (1 + ω * (Q * Real.exp a))) (ω * Q / (1 + ω * Q))
      ((0, 0) : ℝ × ℝ).1 := by
    have h1 : HasDerivAt (fun a => 1 + ω * (Q * Real.exp a)) (ω * (Q * Real.exp 0)) 0 :=
      (((Real.hasDerivAt_exp 0).const_mul Q).const_mul ω).const_add 1
    have h2 := h1.log (by simp only [Real.exp_zero, mul_one]; exact hpos.ne')
    simp only [Real.exp_zero, mul_one] at h2
    exact h2
  have hf := ((hg.comp_hasFDerivAt ((0, 0) : ℝ × ℝ)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), (0 : ℝ))))).sub_const (Real.log Q)).sub
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), (0 : ℝ))))
  have heq : bondReturn ω Q = fun p => ((fun a => Real.log (1 + ω * (Q * Real.exp a))) ∘
      Prod.fst) p - Real.log Q - p.2 := by
    funext p
    rw [bondReturn_eq hQ]
    rfl
  rw [heq]
  exact hf

/-- Cochrane (2023), A1 p. 563: at the steady-state price `Q = 1/(1 + i − ω)` the return is
`log(1 + i)` and the derivative coefficient on `q̃_{t+1}` is `ω/(1 + i)`, so
`r^n_{t+1} ≈ log(1 + i) + ω/(1 + i) q̃_{t+1} − q̃_t`. -/
theorem bondReturn_ss {ω i : ℝ} (hi : 0 < 1 + i) (hω0 : 0 ≤ ω) (hω : ω < 1 + i) :
    bondReturn ω (1 / (1 + i - ω)) (0, 0) = Real.log (1 + i) ∧
      ω * (1 / (1 + i - ω)) / (1 + ω * (1 / (1 + i - ω))) = ω / (1 + i) := by
  have hQ : 0 < 1 / (1 + i - ω) := by
    have : 0 < 1 + i - ω := by linarith
    positivity
  refine ⟨?_, (ss_ratios hi hω).2⟩
  rw [bondReturn_eq hQ]
  simp only [Real.exp_zero, mul_one, sub_zero]
  rw [← Real.log_div (by positivity) hQ.ne', (ss_ratios hi hω).1]

/-- Cochrane (2023), A1 p. 563, survey error E23: (1.24) replaces the exact first-order
coefficient `ω/(1 + i)` by `ω`; for `ω > 0`, `i > 0` the exact coefficient is strictly
smaller, so the model is written with `ω̃ = ω/(1 + i)`. -/
theorem e23_coef_lt {ω i : ℝ} (hω : 0 < ω) (hi : 0 < i) : ω / (1 + i) < ω := by
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-! ### (5.21) iterated: the bond price as a sum of returns (survey error E22) -/

/-- Cochrane (2023), A1 p. 564: iterating `r_{t+1} = ω̃ q_{t+1} − q_t`,
`q_t = ω̃ᵏ q_{t+k} − ∑_{j<k} ω̃ʲ r_{t+1+j}`. -/
theorem bond_iterate {om : ℝ} {q r : ℕ → ℝ} (h : ∀ t, r (t + 1) = om * q (t + 1) - q t)
    (t k : ℕ) : q t = om ^ k * q (t + k) - ∑ j ∈ Finset.range k, om ^ j * r (t + 1 + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Finset.sum_range_succ, show t + 1 + k = t + k + 1 by omega, h (t + k), pow_succ,
      show t + (k + 1) = t + k + 1 by omega]
    ring

/-- Cochrane (2023), A1 pp. 561, 564 (corrected, survey error E22): for `|ω̃| < 1` and a bounded
price, `q_t = −∑_{j≥1} ω̃^{j−1} r_{t+j}` (a convergent series). -/
theorem bond_price_sum {om M : ℝ} (hom : |om| < 1) {q r : ℕ → ℝ}
    (h : ∀ t, r (t + 1) = om * q (t + 1) - q t) (hq : ∀ t, |q t| ≤ M) (t : ℕ) :
    HasSum (fun j : ℕ => om ^ j * r (t + 1 + j)) (-q t) := by
  have hrb : ∀ j, |r (t + 1 + j)| ≤ |om| * M + M := fun j => by
    rw [show t + 1 + j = t + j + 1 by omega, h (t + j)]
    refine (abs_sub _ _).trans (add_le_add ?_ (hq _))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hq _) (abs_nonneg om)
  have hs : Summable (fun j : ℕ => om ^ j * r (t + 1 + j)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg om) hom).mul_right
      (|om| * M + M)) (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hrb j) (pow_nonneg (abs_nonneg om) j))
  have hlim : Tendsto (fun k => ∑ j ∈ Finset.range k, om ^ j * r (t + 1 + j)) atTop
      (𝓝 (-q t)) := by
    have hdec : Tendsto (fun k => om ^ k * q (t + k)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg om) hom).mul_const M
      rw [zero_mul] at hg
      refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hg
      rw [Function.comp_apply, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hq _) (pow_nonneg (abs_nonneg om) k)
    have := hdec.sub_const (q t)
    rw [zero_sub] at this
    refine this.congr fun k => ?_
    rw [bond_iterate h t k]
    ring
  rw [tendsto_nhds_unique hlim hs.hasSum.tendsto_sum_nat] at *
  exact hs.hasSum

/-- Cochrane (2023), A1 pp. 561, 564, survey error E22: the printed `q̃_t = −∑_{j≥1} ωʲ r̃_{t+j}`
is false: with `ω̃ = 1/2`, a constant price `q ≡ −1` and hence returns `r ≡ 1/2`, the printed
sum is `−1/2 ≠ −1 = q_t`, while the corrected sum `bond_price_sum` gives `−1`. -/
theorem e22_printed_fails :
    (∀ t : ℕ, (fun _ : ℕ => (1 / 2 : ℝ)) (t + 1) = 1 / 2 * (fun _ : ℕ => (-1 : ℝ)) (t + 1) -
      (fun _ : ℕ => (-1 : ℝ)) t) ∧
    HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * (1 / 2)) (1 / 2) ∧
    -(1 / 2 : ℝ) ≠ -1 := by
  refine ⟨fun t => by norm_num, ?_, by norm_num⟩
  have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (1 / 4 : ℝ)
  convert this using 1
  · funext j
    rw [pow_succ]
    ring
  · norm_num

/-- Cochrane (2023), A1 eq. (1.25), p. 564: for bounded adapted prices and returns with
`r_{t+1} = ω̃ q_{t+1} − q_t` and `0 ≤ ω̃ < 1`,
`ΔE_{t+1} r_{t+1} = −∑_{j≥1} ω̃ʲ ΔE_{t+1} r_{t+1+j}` (a convergent series). -/
theorem eq_1_25 {om Mq : ℝ} (hom0 : 0 ≤ om) (hom1 : om < 1) {q r : ℕ → Ω → ℝ}
    (hqa : 𝔼.Adapted q) (hqb : ∀ t ω, |q t ω| ≤ Mq) (h : ∀ t, r (t + 1) = om • q (t + 1) - q t)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => om ^ (j + 1) * (𝔼.E (t + 1) (r (t + 1 + (j + 1))) ω -
      𝔼.E t (r (t + 1 + (j + 1))) ω))
      (-(𝔼.E (t + 1) (r (t + 1)) ω - 𝔼.E t (r (t + 1)) ω)) := by
  have hom : |om| < 1 := by rw [abs_of_nonneg hom0]; exact hom1
  have hrb : ∀ j ω', |r (j + 1) ω'| ≤ om * Mq + Mq := fun j ω' => by
    rw [h j]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ (hqb _ _))
    rw [abs_mul, abs_of_nonneg hom0]
    exact mul_le_mul_of_nonneg_left (hqb _ _) hom0
  have hrb' : ∀ k ω', |r (t + 1 + 1 + k) ω'| ≤ om * Mq + Mq := fun k ω' => by
    have := hrb (t + 1 + k) ω'
    rwa [show t + 1 + k + 1 = t + 1 + 1 + k by omega] at this
  -- pathwise: q_{t+1} = −∑_k ω̃ᵏ r_{t+2+k}
  have hpath : ∀ ω', HasSum (fun k : ℕ => om ^ k * r (t + 1 + 1 + k) ω') (-q (t + 1) ω') :=
    fun ω' => bond_price_sum (q := fun s => q s ω') (r := fun s => r s ω') hom
      (fun s => by have := congrFun (h s) ω'; simpa using this) (fun s => hqb s ω') (t + 1)
  have hqfun : q (t + 1) = fun ω' => -∑' k, om ^ k * r (t + 1 + 1 + k) ω' := by
    funext ω'
    rw [(hpath ω').tsum_eq, neg_neg]
  have hb : ∀ k ω', |om ^ k * r (t + 1 + 1 + k) ω'| ≤ om ^ k * (om * Mq + Mq) := fun k ω' => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hom0 k)]
    exact mul_le_mul_of_nonneg_left (hrb' k ω') (pow_nonneg hom0 k)
  have hEs : ∀ s, s ≤ t + 1 → 𝔼.E s (q (t + 1)) ω =
      -∑' k, om ^ k * 𝔼.E s (r (t + 1 + 1 + k)) ω := by
    intro s _
    rw [hqfun]
    have : (fun ω' => -∑' k, om ^ k * r (t + 1 + 1 + k) ω') =
        -(fun ω' => ∑' k, om ^ k * r (t + 1 + 1 + k) ω') := rfl
    rw [this, map_neg, Pi.neg_apply, 𝔼.E_tsum hom0 hom1 hb s ω]
    congr 1
    refine tsum_congr fun k => ?_
    have : (fun ω' => om ^ k * r (t + 1 + 1 + k) ω') = om ^ k • r (t + 1 + 1 + k) := rfl
    rw [this, map_smul]
    rfl
  have hsum : ∀ s, Summable (fun k : ℕ => om ^ k * 𝔼.E s (r (t + 1 + 1 + k)) ω) := fun s =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hom0 hom1).mul_right (om * Mq + Mq))
      (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hom0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hrb' k) s ω) (pow_nonneg hom0 k))
  have hinn : 𝔼.E (t + 1) (r (t + 1)) ω - 𝔼.E t (r (t + 1)) ω =
      om * (𝔼.E (t + 1) (q (t + 1)) ω - 𝔼.E t (q (t + 1)) ω) := by
    rw [h t, map_sub, map_sub, map_smul, map_smul,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hqa t), hqa t]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hinn, hEs (t + 1) le_rfl, hEs t (Nat.le_succ t)]
  have := (((hsum (t + 1)).hasSum.sub (hsum t).hasSum).mul_left om)
  convert this using 1
  · funext j
    rw [pow_succ, show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
    ring
  · ring

/-! ### The model (5.17)–(5.21) -/

/-- Cochrane (2023), eqs. (5.17)–(5.21), p. 127, with the exact coefficient `ω̃ = om` (survey
error E23): the new-Keynesian model, the flow `ρ v_{t+1} = v_t + r^n_{t+1} − π_{t+1} − s̃_{t+1}`,
the expectations hypothesis `E_t r^n_{t+1} = i_t` and the return `r^n_{t+1} = ω̃ q_{t+1} − q_t`,
from pre-sample values `v_{−1}`, `q_{−1}` (`vm1`, `qm1`, known at date 0). -/
def LTD (σ β κ ρ om : ℝ) (i s : ℕ → Ω → ℝ) (vm1 qm1 : Ω → ℝ) (x π v q rn : ℕ → Ω → ℝ) :
    Prop :=
  NK 𝔼 σ β κ i x π ∧ (∀ t, ρ • v (t + 1) = v t + rn (t + 1) - π (t + 1) - s (t + 1)) ∧
    ρ • v 0 = vm1 + rn 0 - π 0 - s 0 ∧ (∀ t, 𝔼.E t (rn (t + 1)) = i t) ∧
    (∀ t, rn (t + 1) = om • q (t + 1) - q t) ∧ rn 0 = om • q 0 - qm1

/-- Cochrane (2023), pp. 127–128: the long-term-debt model is the general fiscal model of
§5.1.2 with flow forcing `e_t = s̃_t − r^n_t` and `b_0 = v_{−1}`, plus the bond equations. -/
theorem ltd_iff_eqm {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x π v q rn : ℕ → Ω → ℝ} :
    LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q rn ↔
      Eqm 𝔼 σ β κ ρ i (fun t => s t - rn t) vm1 x π v ∧ (∀ t, 𝔼.E t (rn (t + 1)) = i t) ∧
        (∀ t, rn (t + 1) = om • q (t + 1) - q t) ∧ rn 0 = om • q 0 - qm1 := by
  unfold LTD Eqm Flow
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, fun t => ?_, ?_⟩, h4⟩
    · rw [h2 t]; funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · rw [h3]; funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, fun t => ?_, ?_, h4⟩
    · rw [h2 t]; funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · rw [h3]; funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-- Cochrane (2023), eqs. (5.20)–(5.21) and A1 p. 564: with `0 ≤ ω̃ < 1` and bounded adapted
`i`, a bounded adapted bond price is the forward sum `q_t = −∑_{k≥0} ω̃ᵏ E_t i_{t+k}` ("solved
forward, gives one more explosive root", p. 128). -/
theorem bond_price {om Mi : ℝ} (hom0 : 0 ≤ om) (hom1 : om < 1) {i q rn : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hqa : 𝔼.Adapted q) (hqb : BoundedProc q)
    (h20 : ∀ t, 𝔼.E t (rn (t + 1)) = i t) (h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t) :
    q = 𝔼.forwardSeries om (-i) := by
  refine 𝔼.eq_forwardSeries hom0 hom1 (M := Mi) (fun t ω => by simpa using hib t ω)
    (fun t => by rw [Pi.neg_apply, map_neg, hi t]) (fun t => ?_) hqb
  have := h20 t
  rw [h21 t, map_sub, map_smul, hqa t] at this
  rw [Pi.neg_apply, ← this]
  abel

/-- Cochrane (2023), eq. (5.21): the returns implied by a price path and a pre-sample price. -/
def rnOf (om : ℝ) (q : ℕ → Ω → ℝ) (qm1 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => om • q 0 - qm1
  | t + 1 => om • q (t + 1) - q t

/-- Cochrane (2023), p. 128 — **determinacy with long-term debt**: for `0 < ρ < 1`,
`0 ≤ ω̃ < 1`, bounded adapted `i`, `s̃` and bounded date-0 pre-sample values, there is exactly
one equilibrium of (5.17)–(5.21) with bounded output, inflation, debt and (adapted) bond
prices. -/
theorem ltd_determinate {σ β κ ρ om Mi Ms Mv Mq : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {i s : ℕ → Ω → ℝ}
    {vm1 qm1 : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ Ms) (hv0 : 𝔼.E 0 vm1 = vm1) (hvb : ∀ ω, |vm1 ω| ≤ Mv)
    (hq0 : 𝔼.E 0 qm1 = qm1) (hqb : ∀ ω, |qm1 ω| ≤ Mq) :
    ∃ x π v q rn, (LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q rn ∧ 𝔼.Adapted q ∧ BoundedProc x ∧
      BoundedProc π ∧ BoundedProc v ∧ BoundedProc q) ∧
      ∀ x' π' v' q' rn', LTD 𝔼 σ β κ ρ om i s vm1 qm1 x' π' v' q' rn' → 𝔼.Adapted q' →
        BoundedProc π' → BoundedProc v' → BoundedProc q' →
        x' = x ∧ π' = π ∧ v' = v ∧ q' = q ∧ rn' = rn := by
  set q := 𝔼.forwardSeries om (-i) with hqdef
  have hib' : ∀ t ω, |(-i) t ω| ≤ Mi := fun t ω => by simpa using hib t ω
  have hia' : 𝔼.Adapted (-i) := fun t => by rw [Pi.neg_apply, map_neg, hi t]
  have hqs : ∀ t, q t = om • 𝔼.E t (q (t + 1)) + (-i) t :=
    𝔼.forwardSeries_solves hom0 hom1 hib' hia'
  have hqa : 𝔼.Adapted q := 𝔼.forwardSeries_adapted hom0 hom1 hib'
  obtain ⟨MQ, hMQ⟩ : BoundedProc q := 𝔼.forwardSeries_bounded hom0 hom1 hib'
  set rn := rnOf om q qm1 with hrndef
  have hrna : 𝔼.Adapted rn := by
    intro t
    cases t with
    | zero =>
      change 𝔼.E 0 (om • q 0 - qm1) = om • q 0 - qm1
      rw [map_sub, map_smul, hqa 0, hq0]
    | succ t =>
      change 𝔼.E (t + 1) (om • q (t + 1) - q t) = om • q (t + 1) - q t
      rw [map_sub, map_smul, hqa, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hqa t)]
  have hrnb : ∀ t ω, |rn t ω| ≤ om * MQ + (MQ + Mq) := by
    intro t ω
    have hMQ0 : 0 ≤ MQ := (abs_nonneg _).trans (hMQ 0 ω)
    have hMq0 : 0 ≤ Mq := (abs_nonneg _).trans (hqb ω)
    cases t with
    | zero =>
      change |(om • q 0 - qm1) ω| ≤ _
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hom0]
      nlinarith [hMQ 0 ω, hqb ω, mul_le_mul_of_nonneg_left (hMQ 0 ω) hom0]
    | succ t =>
      change |(om • q (t + 1) - q t) ω| ≤ _
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hom0]
      nlinarith [hMQ (t + 1) ω, hMQ t ω, mul_le_mul_of_nonneg_left (hMQ (t + 1) ω) hom0]
  have h20 : ∀ t, 𝔼.E t (rn (t + 1)) = i t := fun t => by
    change 𝔼.E t (om • q (t + 1) - q t) = i t
    rw [map_sub, map_smul, hqa t, hqs t]
    simp
  have h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t := fun t => rfl
  have h21' : rn 0 = om • q 0 - qm1 := rfl
  set e : ℕ → Ω → ℝ := fun t => s t - rn t with hedef
  have hea : 𝔼.Adapted e := fun t => by simp only [hedef]; rw [map_sub, hs t, hrna t]
  have heb : ∀ t ω, |e t ω| ≤ Ms + (om * MQ + (MQ + Mq)) := fun t ω =>
    (abs_sub _ _).trans (add_le_add (hsb t ω) (hrnb t ω))
  obtain ⟨x, π, v, ⟨hE, hxb, hπb, hvb'⟩, huniq⟩ :=
    eqm_determinate 𝔼 hσ hκ hβ hρ0 hρ1 hi hib hea heb hv0 hvb
  refine ⟨x, π, v, q, rn, ⟨(ltd_iff_eqm 𝔼).mpr ⟨hE, h20, h21, h21'⟩, hqa, hxb, hπb, hvb',
    ⟨MQ, hMQ⟩⟩, fun x' π' v' q' rn' h' hqa' hπb' hvb'' hqb' => ?_⟩
  obtain ⟨hE', h20', h21'', h0'⟩ := (ltd_iff_eqm 𝔼).mp h'
  have hqq : q' = q := bond_price 𝔼 hom0 hom1 hi hib hqa' hqb' h20' h21''
  have hrr : rn' = rn := by
    funext t
    cases t with
    | zero => rw [h0', hqq]; rfl
    | succ t => rw [h21'' t, hqq]; rfl
  rw [hrr] at hE'
  obtain ⟨hx, hπ, hv⟩ := huniq x' π' v' hE' hπb' hvb''
  exact ⟨hx, hπ, hv, hqq, hrr⟩

/-! ### The link with one-period debt, and irrelevance (p. 129) -/

/-- Cochrane (2023), p. 129: the surplus path that makes the one-period-debt flow reproduce the
long-term-debt flow, `s''_0 = s̃_0 − r^n_0`, `s''_{t+1} = s̃_{t+1} − r^n_{t+1} + i_t`. -/
def sAdj (i s rn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => s 0 - rn 0
  | t + 1 => s (t + 1) - rn (t + 1) + i t

/-- Cochrane (2023), pp. 128–129: an equilibrium of the long-term-debt model is an equilibrium
of the one-period-debt model (5.15)–(5.16) with surpluses `sAdj` and `b_0 = v_{−1}`: long-term
debt matters only through the gap between the realised return and the rate. -/
theorem ltd_to_ftplnk {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x π v q rn : ℕ → Ω → ℝ} (h : LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q rn) :
    FTPLNK 𝔼 σ β κ ρ i (sAdj i s rn) vm1 x π v := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨h1, fun t => ?_, ?_⟩
  · rw [h2 t]
    funext ω
    simp only [sAdj, Pi.add_apply, Pi.sub_apply]
    ring
  · rw [h3]
    funext ω
    simp only [sAdj, Pi.add_apply, Pi.sub_apply]
    ring

/-- Cochrane (2023), p. 129 ("only an unanticipated shock to bond prices can lower their
value"): given (5.20)–(5.21) and adapted prices, the realised return equals the rate,
`r^n_{t+1} = i_t`, iff there is no bond-price news, `ω̃ (q_{t+1} − E_t q_{t+1}) = 0`. -/
theorem rn_eq_i_iff_no_news {om : ℝ} {i q rn : ℕ → Ω → ℝ} (hqa : 𝔼.Adapted q)
    (h20 : ∀ t, 𝔼.E t (rn (t + 1)) = i t) (h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t)
    (t : ℕ) : rn (t + 1) = i t ↔ om • (q (t + 1) - 𝔼.E t (q (t + 1))) = 0 := by
  have hE := h20 t
  rw [h21 t, map_sub, map_smul, hqa t] at hE
  rw [h21 t, ← hE, smul_sub]
  constructor
  · intro h
    rw [sub_eq_zero]
    have := congrArg (· + q t) h
    simpa using this
  · intro h
    rw [sub_eq_zero] at h
    rw [h]

/-- Cochrane (2023), p. 129 (irrelevance of maturity without bond-price news): if the realised
return always equals the rate, the long-term-debt equilibrium is an equilibrium of the
one-period-debt model with `b_0 = v_{−1} + r^n_0`. -/
theorem ltd_no_news {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x π v q rn : ℕ → Ω → ℝ} (h : LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q rn)
    (hnn : ∀ t, rn (t + 1) = i t) : FTPLNK 𝔼 σ β κ ρ i s (vm1 + rn 0) x π v := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨h1, fun t => ?_, ?_⟩
  · rw [h2 t, hnn t]
  · rw [h3]

/-- Cochrane (2023), p. 129 ("Long-term debt has no effect on the responses to a fully-anticipated
interest-rate rise"): for a deterministic (perfectly anticipated) bounded rate path, any bounded
adapted bond price carries no news, so `r^n_{t+1} = i_t` and `ltd_no_news` applies. -/
theorem ltd_anticipated_no_news {om Mi : ℝ} (hom0 : 0 ≤ om) (hom1 : om < 1) {c : ℕ → ℝ}
    (hcb : ∀ t, |c t| ≤ Mi) {q rn : ℕ → Ω → ℝ} (hqa : 𝔼.Adapted q) (hqb : BoundedProc q)
    (h20 : ∀ t, 𝔼.E t (rn (t + 1)) = (fun _ => c t))
    (h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t) (t : ℕ) : rn (t + 1) = fun _ => c t := by
  have hi : 𝔼.Adapted (fun t (_ : Ω) => c t) := fun t => 𝔼.const t (c t)
  have hq := bond_price 𝔼 hom0 hom1 hi (fun t _ => hcb t) hqa hqb h20 h21
  have hdet : ∀ s, q s = fun _ => ∑' k, om ^ k * -c (s + k) := fun s => by
    rw [hq]
    funext ω
    unfold ExpectationSystem.forwardSeries
    refine tsum_congr fun k => ?_
    have : (-fun t (_ : Ω) => c t) (s + k) = fun _ => -c (s + k) := rfl
    rw [this, 𝔼.const]
  have hc : rn (t + 1) = fun _ =>
      om * ∑' k, om ^ k * -c (t + 1 + k) - ∑' k, om ^ k * -c (t + k) := by
    rw [h21 t, hdet (t + 1), hdet t]
    rfl
  have hk : 𝔼.E t (rn (t + 1)) = rn (t + 1) := by rw [hc, 𝔼.const]
  rw [← hk, h20 t]

/-- Cochrane (2023), p. 129 ("Long-term debt has no effect at all on the response to a fiscal
shock when interest rates do not change … Figure 5.3 is also completely unaltered"): with
`i ≡ 0` and `q_{−1} = 0`, every long-term-debt equilibrium with bounded adapted bond prices has
`q ≡ 0`, `r^n ≡ 0`, and is the one-period-debt equilibrium with `b_0 = v_{−1}`. -/
theorem ltd_fiscal_shock {σ β κ ρ om : ℝ} (hom0 : 0 ≤ om) (hom1 : om < 1) {s : ℕ → Ω → ℝ}
    {vm1 : Ω → ℝ} {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun _ _ => 0) s vm1 0 x π v q rn) (hqa : 𝔼.Adapted q)
    (hqb : BoundedProc q) : q = 0 ∧ rn = 0 ∧ FTPLNK 𝔼 σ β κ ρ (fun _ _ => 0) s vm1 x π v := by
  have hi : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun t => 𝔼.const t 0
  have hq := bond_price 𝔼 hom0 hom1 hi (Mi := 0) (fun _ _ => by simp) hqa hqb h.2.2.2.1
    h.2.2.2.2.1
  have hq0 : q = 0 := by
    rw [hq]
    funext t ω
    unfold ExpectationSystem.forwardSeries
    have : ∀ k, (-fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) (t + k) = 0 := fun k => by
      funext ω'; simp
    simp [this]
  have hrn : rn = 0 := by
    funext t
    cases t with
    | zero => rw [h.2.2.2.2.2, hq0]; simp
    | succ t => rw [h.2.2.2.2.1 t, hq0]; simp
  refine ⟨hq0, hrn, ?_⟩
  have := ltd_no_news 𝔼 h (fun t => by rw [hrn]; rfl)
  rwa [hrn, Pi.zero_apply, add_zero] at this

/-- Cochrane (2023), p. 129, survey error E30: "Inflation rises one period after the
interest-rate rise" is false with sticky prices, with or without long-term debt — in every
long-term-debt equilibrium with bounded inflation, a rise announced for date `S + 1` moves
inflation at date `S` or `S + 1`. -/
theorem ltd_anticipated_moves_before [Nonempty Ω] {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (S : ℕ) {s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ} {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun t _ => if S + 1 ≤ t then 1 else 0) s vm1 qm1 x π v q rn)
    (hπb : BoundedProc π) : ¬ (π S = 0 ∧ π (S + 1) = 0) :=
  anticipated_moves_before 𝔼 hσ hκ hβ S hπb h.1

/-! ### Fig. 5.4: an unexpected permanent rise with long-term debt -/

/-- Cochrane (2023), Fig. 5.4, pp. 128–129: an unexpected permanent rate rise (`i ≡ 1`,
unchanged surpluses, `v_{−1} = q_{−1} = 0`) with long-term debt. Every equilibrium with bounded
inflation, debt and adapted bounded bond prices has `q_t = −1/(1 − ω̃)` and
`π_{1+j} = 1 − [(1 − ρ/λ₁)/(1 − ω̃)] λ₁^{−j}`,
`κ x_{1+j} = (1 − β) − [(1 − ρ/λ₁)(1 − β/λ₁)/(1 − ω̃)] λ₁^{−j}`,
`v_{1+j} = −λ₁^{−(j+1)}/(1 − ω̃)`; one exists (`ltd_determinate`). -/
theorem ltd_perm_rise {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun _ _ => 1) (fun _ _ => 0) 0 0 x π v q rn) (hqa : 𝔼.Adapted q)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q) (t : ℕ) (ω : Ω) :
    q t ω = -1 / (1 - om) ∧
    π t ω = 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) * (lam1 σ β κ)⁻¹ ^ t ∧
    κ * x t ω = (1 - β) - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) / (1 - om) *
      (lam1 σ β κ)⁻¹ ^ t ∧
    v t ω = -(lam1 σ β κ)⁻¹ ^ (t + 1) / (1 - om) := by
  have hom : 1 - om ≠ 0 := by linarith
  have hi : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) := fun t => 𝔼.const t 1
  have hq := bond_price 𝔼 hom0 hom1 hi (Mi := 1) (fun _ _ => by simp) hqa hqb h.2.2.2.1
    h.2.2.2.2.1
  have hqc : q = fun _ _ => -1 / (1 - om) := by
    rw [hq]
    refine (𝔼.eq_forwardSeries hom0 hom1 (M := 1) (fun _ _ => by simp)
      (fun t => by rw [Pi.neg_apply, map_neg, hi t]) (fun t => ?_) ⟨|-1 / (1 - om)|,
        fun _ _ => le_rfl⟩).symm
    rw [𝔼.const]
    funext ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
    ring
  set c := om / (1 - om) with hcdef
  set s' : ℕ → ℝ := fun t => if t = 0 then c else 0 with hs'
  have hsadj : sAdj (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) rn = fun t _ => s' t := by
    funext t ω
    cases t with
    | zero =>
      simp only [sAdj, Pi.sub_apply, hs', ↓reduceIte]
      rw [h.2.2.2.2.2, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hcdef]
      field_simp
      ring
    | succ t =>
      simp only [sAdj, Pi.add_apply, Pi.sub_apply, hs', Nat.succ_ne_zero, ↓reduceIte]
      rw [h.2.2.2.2.1 t, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hft := ltd_to_ftplnk 𝔼 h
  rw [hsadj] at hft
  have hs'b : ∀ j, |s' j| ≤ |c| := fun j => by
    simp only [hs']; split_ifs <;> simp
  obtain ⟨hx, hπ, hv⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 1 0 hs'b (by exact hft) hπb hvb
  have hpv : pvS ρ s' = c := by
    unfold pvS
    have : (fun j => ρ ^ j * s' j) = fun j => if j = 0 then c else 0 := by
      funext j
      simp only [hs']
      split_ifs with hj
      · rw [hj, pow_zero, one_mul]
      · rw [mul_zero]
    rw [this, tsum_ite_eq]
  have htail : ∀ j, s' (t + 1 + j) = 0 := fun j => by simp [hs']
  refine ⟨by rw [hqc], ?_, ?_, ?_⟩
  · rw [hπ]
    simp only [piDet, hpv, hcdef]
    field_simp
    ring
  · rw [hx]
    simp only [xDet, piDet, hpv, hcdef]
    field_simp
    ring
  · rw [hv]
    simp only [vDet, hpv, htail, mul_zero, tsum_zero, add_zero, hcdef]
    field_simp
    ring

/-- Cochrane (2023), p. 128 (Fig. 5.4) — **disinflation on impact iff `ω̃ > ρ/λ₁`**: for
`ω̃ < 1`, `π_1 = 1 − (1 − ρ/λ₁)/(1 − ω̃) < 0` iff `ρ/λ₁ < ω̃`. (With one-period debt, `ω̃ = 0`,
there is never an impact disinflation.) -/
theorem ltd_disinflation_iff {ρq om : ℝ} (hom1 : om < 1) :
    1 - (1 - ρq) / (1 - om) < 0 ↔ ρq < om := by
  have h : 0 < 1 - om := by linarith
  rw [sub_neg, one_lt_div h]
  constructor <;> intro hh <;> linarith

/-- Cochrane (2023), p. 129 ("a longer maturity structure produces a larger and more protracted
disinflation"): for `0 < ρ/λ₁ < 1`, inflation at every date is strictly decreasing in `ω̃ < 1`. -/
theorem ltd_strictAnti_om {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ1 : ρ < 1)
    (t : ℕ) : StrictAntiOn (fun om => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) *
      (lam1 σ β κ)⁻¹ ^ t) (Set.Iio 1) := by
  intro o₁ h₁ o₂ h₂ hlt
  simp only [Set.mem_Iio] at h₁ h₂
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 := inv_lt_one_of_one_lt₀ h1
  have hA : 0 < (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t := by
    refine mul_pos ?_ (pow_pos hq0 t)
    rcases le_or_gt ρ 0 with h | h <;> nlinarith
  have hd : 1 / (1 - o₁) < 1 / (1 - o₂) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  simp only
  have e : ∀ o, 1 - o ≠ 0 → (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - o) * (lam1 σ β κ)⁻¹ ^ t =
      (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t * (1 / (1 - o)) := fun o ho => by
    field_simp
  rw [e o₁ (by linarith), e o₂ (by linarith)]
  nlinarith [mul_lt_mul_of_pos_left hd hA]

/-- Cochrane (2023), p. 129 ("The initial decline in inflation is larger when prices are less
sticky"): for `ω̃ < 1`, the impact response `1 − (1 − ρ/λ₁)/(1 − ω̃)` is strictly decreasing in
`κ`. -/
theorem ltd_pi0_strictAnti_kappa {σ β ρ om : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hom1 : om < 1) :
    StrictAntiOn (fun κ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om)) (Set.Ioi 0) := by
  intro κ₁ h₁ κ₂ h₂ hlt
  have := perm_rise_pi0_strictAnti hσ hβ hρ0 h₁ h₂ hlt
  simp only at this ⊢
  have h : 0 < 1 - om := by linarith
  rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right h]
  linarith

/-- Cochrane (2023), p. 129 (the flexible-price limit, "π, κ = ∞" in Fig. 5.4): as `κ → ∞`,
`π_1 → −ω̃/(1 − ω̃)` and `π_{1+j} → 1` for `j ≥ 1` — "the inflation decline lasts one period and
then inflation rises immediately". -/
theorem ltd_kappa_atTop {σ β ρ om : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hom1 : om < 1) :
    Tendsto (fun κ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om)) atTop (𝓝 (-om / (1 - om))) ∧
    ∀ t, 1 ≤ t → Tendsto (fun κ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) *
      (lam1 σ β κ)⁻¹ ^ t) atTop (𝓝 1) := by
  have hq := (tendsto_lam1_atTop hσ hβ).inv_tendsto_atTop
  have hom : 1 - om ≠ 0 := by linarith
  refine ⟨?_, fun t ht => ?_⟩
  · have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul ρ)).div_const (1 - om))
    convert this using 2
    field_simp
    ring
  · have hqt : Tendsto (fun κ => (lam1 σ β κ)⁻¹ ^ t) atTop (𝓝 0) := by
      have := hq.pow t
      rwa [zero_pow (by omega)] at this
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul ρ)).div_const (1 - om)).mul hqt)
    simpa using this

/-- Cochrane (2023), p. 128 ("Higher inflation eventually reemerges"; Sims's "stepping on a
rake"): with long-term debt inflation still converges to the new rate, `π_{1+j} → 1`. -/
theorem ltd_tendsto_one {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) * (lam1 σ β κ)⁻¹ ^ t) atTop
      (𝓝 1) := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith))
    (inv_lt_one_of_one_lt₀ h1)).const_mul ((1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om))
  rw [mul_zero] at this
  simpa using this.const_sub 1

/-! ### (3.20) at p. 129 -/

/-- Cochrane (2023), p. 129 (the identity (3.20) quoted there): with the long-term-debt flow,
bounded adapted `v` and bounded `π`, `r^n`, `s̃`, and `0 ≤ ρ < 1`,
`ΔE_{t+1} π_{t+1} − ΔE_{t+1} r^n_{t+1} = ∑_{j≥1} ρʲ ΔE_{t+1}(r^n_{t+1+j} − π_{t+1+j})
  − ∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j}`. -/
theorem eq_3_20 {ρ Ms Mπ Mr : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s v π rn : ℕ → Ω → ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ Ms) (hπb : ∀ t ω, |π t ω| ≤ Mπ) (hrb : ∀ t ω, |rn t ω| ≤ Mr)
    (hva : 𝔼.Adapted v) (hvb : BoundedProc v)
    (h : ∀ t, ρ • v (t + 1) = v t + rn (t + 1) - π (t + 1) - s (t + 1)) (t : ℕ) (ω : Ω) :
    (𝔼.E (t + 1) (π (t + 1)) ω - 𝔼.E t (π (t + 1)) ω) -
      (𝔼.E (t + 1) (rn (t + 1)) ω - 𝔼.E t (rn (t + 1)) ω) =
      ∑' j : ℕ, ρ ^ (j + 1) * (𝔼.E (t + 1) (rn (t + 1 + j + 1) - π (t + 1 + j + 1)) ω -
        𝔼.E t (rn (t + 1 + j + 1) - π (t + 1 + j + 1)) ω) -
      ∑' j : ℕ, ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω) := by
  obtain ⟨πt, hπt⟩ : ∃ f : ℕ → Ω → ℝ, f = fun k => π k - rn k := ⟨_, rfl⟩
  have hi0 : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun k => 𝔼.const k 0
  have hfl : FlowShort ρ (fun _ _ => 0) s v πt := fun k => by
    rw [h k, hπt]
    funext ω'
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hπtb : ∀ k ω', |πt k ω'| ≤ Mπ + Mr := fun k ω' => by
    rw [hπt]
    exact (abs_sub _ _).trans (add_le_add (hπb k ω') (hrb k ω'))
  obtain ⟨_, _, h13⟩ := eq_5_13 𝔼 hρ0 hρ1 hi0 (Mi := 0) (fun _ _ => by simp) hsb hπtb
    hva hvb hfl t ω
  have hterm : ∀ j : ℕ, ((fun (_ : Ω) => (0 : ℝ)) - πt (t + 1 + j + 1)) =
      rn (t + 1 + j + 1) - π (t + 1 + j + 1) := fun j => by
    rw [hπt]
    funext ω'
    simp only [Pi.sub_apply]
    ring
  simp only [hterm] at h13
  rw [← h13, hπt]
  simp only [map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 128: under a permanent peg `i ≡ 1`, every bounded adapted bond price
solving (5.20)–(5.21) is the constant `q_t = −1/(1 − ω̃)`. -/
theorem perm_bond_price {om : ℝ} (hom0 : 0 ≤ om) (hom1 : om < 1) {q rn : ℕ → Ω → ℝ}
    (hqa : 𝔼.Adapted q) (hqb : BoundedProc q)
    (h20 : ∀ t, 𝔼.E t (rn (t + 1)) = (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t)
    (h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t) : q = fun _ _ => -1 / (1 - om) := by
  have hom : 1 - om ≠ 0 := by linarith
  have hi : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) := fun t => 𝔼.const t 1
  have hq := bond_price 𝔼 hom0 hom1 hi (Mi := 1) (fun _ _ => by simp) hqa hqb h20 h21
  rw [hq]
  refine (𝔼.eq_forwardSeries hom0 hom1 (M := 1) (fun _ _ => by simp)
    (fun t => by rw [Pi.neg_apply, map_neg, hi t]) (fun t => ?_) ⟨|-1 / (1 - om)|,
      fun _ _ => le_rfl⟩).symm
  rw [𝔼.const]
  funext ω'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

/-! ### A1 §§1.3, 1.10: further algebra -/

/-- Cochrane (2023), A1 eq. (1.21), p. 562 (steady state): at bond prices `Q^{(j)} = (1 + i)^{−j}`
every maturity structure `w_j` earns the same return: if `∑_{j≥1} w_j/(1 + i)ʲ` converges to a
nonzero value, then `∑_{j≥1} w_j/(1 + i)^{j−1}` converges to `1 + i` times it. -/
theorem ss_return_indep {i Qs : ℝ} (hi : 0 < 1 + i) {w : ℕ → ℝ}
    (hw : HasSum (fun j : ℕ => w j / (1 + i) ^ (j + 1)) Qs) (hQ : Qs ≠ 0) :
    HasSum (fun j : ℕ => w j / (1 + i) ^ j) ((1 + i) * Qs) ∧ (1 + i) * Qs / Qs = 1 + i := by
  refine ⟨(hw.mul_left (1 + i)).congr_fun fun j => ?_, by field_simp⟩
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), A1 eq. (1.21), p. 562 (geometric maturity `w_j = ω^{j−1}`): with the
maturing bond priced at one, the payoff of the portfolio is `1 + ω Q_{t+1}`,
`∑_{j≥0} ωʲ P_j = P_0 + ω ∑_{j≥0} ωʲ P_{j+1}` (summable prices). -/
theorem geom_portfolio_payoff {ω : ℝ} {P : ℕ → ℝ} (hP0 : P 0 = 1)
    (hs : Summable (fun j : ℕ => ω ^ j * P j)) :
    ∑' j : ℕ, ω ^ j * P j = 1 + ω * ∑' j : ℕ, ω ^ j * P (j + 1) := by
  rw [hs.tsum_eq_zero_add, hP0, pow_zero, one_mul, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ]
  ring

/-- Cochrane (2023), A1 §1.10, p. 578 (first-order form, interest-rate peg `θ_{iπ} = 0`,
`w_t = i_t`): every equilibrium of (5.17)–(5.21) with adapted bond prices satisfies
`x_{t+1} = (1 + σκ/β) x_t − (σ/β) π_t + σ i_t + δ_{x,t+1}`,
`π_{t+1} = −(κ/β) x_t + π_t/β + δ_{π,t+1}`, `q_{t+1} = q_t/ω̃ + i_t/ω̃ + δ_{q,t+1}`,
`v_{t+1} = κ/(ρβ) x_t − π_t/(ρβ) + v_t/ρ + i_t/ρ − s̃_{t+1}/ρ − δ_{π,t+1}/ρ + (ω̃/ρ) δ_{q,t+1}`,
with `δ_{y,t+1} = y_{t+1} − E_t y_{t+1}` the expectational errors (the book's matrix rows, with
surpluses not yet written as an AR(1)). -/
theorem a1_1_10 {σ β κ ρ om : ℝ} (hβ : β ≠ 0) (hρ : ρ ≠ 0) (hom : om ≠ 0) {i s : ℕ → Ω → ℝ}
    {vm1 qm1 : Ω → ℝ} {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q rn) (hqa : 𝔼.Adapted q) (t : ℕ) (ω : Ω) :
    x (t + 1) ω = (1 + σ * κ / β) * x t ω - σ / β * π t ω + σ * i t ω +
        (x (t + 1) ω - 𝔼.E t (x (t + 1)) ω) ∧
    π (t + 1) ω = -(κ / β) * x t ω + π t ω / β + (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω) ∧
    q (t + 1) ω = q t ω / om + i t ω / om + (q (t + 1) ω - 𝔼.E t (q (t + 1)) ω) ∧
    v (t + 1) ω = κ / (ρ * β) * x t ω - π t ω / (ρ * β) + v t ω / ρ + i t ω / ρ -
        s (t + 1) ω / ρ - (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω) / ρ +
        om / ρ * (q (t + 1) ω - 𝔼.E t (q (t + 1)) ω) := by
  obtain ⟨⟨his, hpc⟩, hfl, _, h20, h21, _⟩ := h
  have e1 := congrFun (hpc t) ω
  have e2 := congrFun (his t) ω
  have e4 := congrFun (h21 t) ω
  have e5 := h20 t
  rw [h21 t, map_sub, map_smul, hqa t] at e5
  have e5ω := congrFun e5 ω
  have e6 := congrFun (hfl t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e4 e5ω e6
  have hEπ : 𝔼.E t (π (t + 1)) ω = (π t ω - κ * x t ω) / β := by
    field_simp; linarith
  have hEq : 𝔼.E t (q (t + 1)) ω = (q t ω + i t ω) / om := by
    field_simp; linarith
  have hEx : 𝔼.E t (x (t + 1)) ω = x t ω + σ * i t ω - σ * ((π t ω - κ * x t ω) / β) := by
    rw [← hEπ]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEx]
    field_simp
    ring
  · rw [hEπ]
    field_simp
    ring
  · rw [hEq]
    field_simp
    ring
  · rw [e4] at e6
    have hv' : v (t + 1) ω = (v t ω + om * q (t + 1) ω - q t ω - π (t + 1) ω - s (t + 1) ω) / ρ :=
      by rw [eq_div_iff hρ]; linarith
    rw [hv', hEπ, hEq]
    field_simp
    ring

/-! ### The calibration of Fig. 5.4 (survey errors E23, E29) -/

/-- Cochrane (2023), Fig. 5.4, p. 128, and survey errors E23/E29: at `r = 0.01`, `σ = 1`,
`κ = 0.25`, the impact response `π_1 = 1 − (1 − ρ/λ₁)/(1 − ω̃)` is in `(−1.49, −1.48)` for the
caption's `ω = 0.85` with the exact weight `ω̃ = 0.85/1.01`; in `(−2.62, −2.61)` for `ω = 0.9`
(the dashed line); in `(−0.90, −0.89)` for the text's `ω = 0.8`; and in `(−1.63, −1.62)` with
(1.24)'s weight `ω̃ = 0.85`. The figure (≈ −1.5, −2.6) matches the caption with the exact
weight, not the text's `ω = 0.8` (E29) nor (1.24)'s approximation (E23). -/
theorem fig54_impact :
    let pi1 := fun om : ℝ => 1 - (1 - 100 / 101 * (lam1 1 (100 / 101) (1 / 4))⁻¹) / (1 - om)
    (-149 / 100 : ℝ) < pi1 (85 / 101) ∧ pi1 (85 / 101) < -148 / 100 ∧
    (-262 / 100 : ℝ) < pi1 (90 / 101) ∧ pi1 (90 / 101) < -261 / 100 ∧
    (-90 / 100 : ℝ) < pi1 (80 / 101) ∧ pi1 (80 / 101) < -89 / 100 ∧
    (-163 / 100 : ℝ) < pi1 (85 / 100) ∧ pi1 (85 / 100) < -162 / 100 := by
  intro pi1
  obtain ⟨h1, h2⟩ := lam1_calib
  have hL : 0 < lam1 1 (100 / 101) (1 / 4) := by linarith
  have hu1 : (1000000 / 1634275 : ℝ) < (lam1 1 (100 / 101) (1 / 4))⁻¹ := by
    rw [← one_div, div_lt_div_iff₀ (by norm_num) hL]; linarith
  have hu2 : (lam1 1 (100 / 101) (1 / 4))⁻¹ < (100000 / 163425 : ℝ) := by
    rw [← one_div, div_lt_div_iff₀ hL (by norm_num)]; linarith
  have e : ∀ d : ℝ, 1 - (1 - 100 / 101 * (lam1 1 (100 / 101) (1 / 4))⁻¹) / d =
      1 - 1 / d + 100 / 101 / d * (lam1 1 (100 / 101) (1 / 4))⁻¹ := fun d => by ring
  simp only [pi1, e]
  norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Cochrane (2023), Fig. 5.4, p. 129 ("π, κ = ∞"), and survey error E23: the flexible-price
impact response `−ω̃/(1 − ω̃)` (`ltd_kappa_atTop`) is exactly `−85/16 = −5.3125` with the exact
weight `ω̃ = 0.85/1.01`, against `−17/3 ≈ −5.67` with (1.24)'s `ω̃ = 0.85`; the figure shows
≈ −5.3. -/
theorem fig54_flexible :
    -(85 / 101 : ℝ) / (1 - 85 / 101) = -85 / 16 ∧ -(85 / 100 : ℝ) / (1 - 85 / 100) = -17 / 3 := by
  constructor <;> norm_num

/-! ### §5.3: a persistent (AR(1)) rate rise with long-term debt -/

/-- Cochrane (2023), p. 131: the coefficient on `ηᵗ` in inflation after an AR(1) rate rise
`i_t = ηᵗ`, `A = σκ/((λ₁η − 1)(1 − λ₂η))`. -/
noncomputable def ar1A (σ β κ η : ℝ) : ℝ :=
  σ * κ / ((lam1 σ β κ * η - 1) * (1 - lam2 σ β κ * η))

/-- Cochrane (2023), p. 131: the coefficient on `λ₁^{−t}`, pinned by the valuation equation,
`C = (1 − ρ/λ₁)[(ρ − A)/(1 − ρη) − ω̃/(1 − ω̃η)]`. -/
noncomputable def ar1C (σ β κ ρ om η : ℝ) : ℝ :=
  (1 - ρ * (lam1 σ β κ)⁻¹) * ((ρ - ar1A σ β κ η) / (1 - ρ * η) - om / (1 - om * η))

/-- Cochrane (2023), §5.3, p. 131 ("the interest-rate rise must be persistent and unexpected"):
an unexpected AR(1) rate path `i_t = ηᵗ` (`0 ≤ η < 1`, `λ₁η ≠ 1`) with long-term debt
(`0 ≤ ω̃ < 1`), unchanged surpluses and `v_{−1} = q_{−1} = 0`. In every equilibrium with bounded
inflation, debt and adapted bounded bond prices, `q_t = −ηᵗ/(1 − ω̃η)` and
`π_t = A ηᵗ + C λ₁^{−t}` (`ar1A`, `ar1C`); one exists by `ltd_determinate`. -/
theorem ltd_ar1 {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hres : lam1 σ β κ * η ≠ 1) {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn) (hqa : 𝔼.Adapted q)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q) (t : ℕ) (ω : Ω) :
    q t ω = -η ^ t / (1 - om * η) ∧
      π t ω = ar1A σ β κ η * η ^ t + ar1C σ β κ ρ om η * (lam1 σ β κ)⁻¹ ^ t := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hq : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hoη : 0 < 1 - om * η := by nlinarith
  have hl2η : 0 < 1 - lam2 σ β κ * η := by nlinarith
  have hρη : 0 < 1 - ρ * η := by nlinarith
  have hρq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0.le hq0
  have hρq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by nlinarith
  have hηb : ∀ t, |η ^ t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (pow_nonneg hη0 t)]; exact pow_le_one₀ hη0 hη1.le
  -- the bond price
  have hi : 𝔼.Adapted (fun t (_ : Ω) => η ^ t) := fun t => 𝔼.const t _
  have hqc : q = fun t _ => -η ^ t / (1 - om * η) := by
    rw [bond_price 𝔼 hom0 hom1 hi (Mi := 1) (fun t _ => hηb t) hqa hqb h.2.2.2.1 h.2.2.2.2.1]
    refine (𝔼.eq_forwardSeries hom0 hom1 (M := 1) (fun t _ => by simpa using hηb t)
      (fun t => by rw [Pi.neg_apply, map_neg, hi t]) (fun t => ?_)
      ⟨1 / (1 - om * η), fun t _ => ?_⟩).symm
    · rw [𝔼.const]
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      field_simp
      ring
    · rw [abs_div, abs_neg, abs_of_pos hoη]
      exact div_le_div_of_nonneg_right (hηb t) hoη.le
  set c0 := om / (1 - om * η) with hc0
  set s'' : ℕ → ℝ := fun t => if t = 0 then c0 else 0 with hs''
  have hsadj : sAdj (fun t _ => η ^ t) (fun _ _ => (0 : ℝ)) rn = fun t _ => s'' t := by
    funext t ω'
    cases t with
    | zero =>
      simp only [sAdj, Pi.sub_apply, hs'', ↓reduceIte]
      rw [h.2.2.2.2.2, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hc0, pow_zero]
      field_simp
      ring
    | succ t =>
      simp only [sAdj, Pi.add_apply, Pi.sub_apply, hs'', Nat.succ_ne_zero, ↓reduceIte]
      rw [h.2.2.2.2.1 t, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hft := ltd_to_ftplnk 𝔼 h
  rw [hsadj] at hft
  set A := ar1A σ β κ η with hAdef
  set C := ar1C σ β κ ρ om η with hCdef
  set l1 := lam1 σ β κ with hl1
  set l2 := lam2 σ β κ with hl2
  have hA : A * (1 - l1 * η) = -(σ * κ / (1 - l2 * η)) := by
    rw [hAdef, ar1A, ← hl1, ← hl2]
    have : l1 * η - 1 ≠ 0 := sub_ne_zero.mpr hres
    field_simp
    ring
  have hFd : ∀ t, ∑' k, l2 ^ k * η ^ (t + k) = η ^ t / (1 - l2 * η) := by
    intro t
    have := ((hasSum_geometric_of_lt_one (mul_nonneg h2.le hη0) (by nlinarith)).mul_left
      (η ^ t)).tsum_eq
    rw [← div_eq_mul_inv] at this
    rw [← this]
    exact tsum_congr fun k => by rw [pow_add, mul_pow]; ring
  have hfac : ∀ t, (A * η ^ t + C * l1⁻¹ ^ t) - l1 * (A * η ^ (t + 1) + C * l1⁻¹ ^ (t + 1)) =
      -(σ * κ) * ∑' k, l2 ^ k * η ^ (t + k) := by
    intro t
    rw [hFd t]
    rw [pow_succ, pow_succ]
    linear_combination η ^ t * hA - (C * l1⁻¹ ^ t) * hq
  have hps : HasSum (fun j : ℕ => ρ ^ j * ((A * η ^ j + C * l1⁻¹ ^ j) + s'' j))
      (A * (1 - ρ * η)⁻¹ + C * (1 - ρ * l1⁻¹)⁻¹ + c0) := by
    have hs0 : HasSum (fun j : ℕ => if j = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    have := (((hasSum_geometric_of_lt_one (mul_nonneg hρ0.le hη0) (by nlinarith)).mul_left
      A).add ((hasSum_geometric_of_lt_one hρq0 hρq1).mul_left C)).add hs0
    convert this using 1
    funext j
    simp only [hs'']
    split_ifs with hj
    · subst hj; ring
    · rw [mul_pow, mul_pow]; ring
  have hηs : ∑' j, ρ ^ j * η ^ j = (1 - ρ * η)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (mul_nonneg hρ0.le hη0) (by nlinarith)]
    exact tsum_congr fun j => by rw [mul_pow]
  have hfis : ∑' j, ρ ^ j * ((A * η ^ j + C * l1⁻¹ ^ j) + s'' j) -
      ρ * ∑' j, ρ ^ j * η ^ j = 0 := by
    have e2 : (1 : ℝ) - ρ * l1⁻¹ ≠ 0 := by linarith
    rw [hps.tsum_eq, hηs, hCdef, ar1C, ← hAdef, ← hl1, mul_comm (1 - ρ * l1⁻¹), mul_assoc,
      mul_inv_cancel₀ e2, mul_one, ← hc0]
    ring
  have hpb : ∀ t, |A * η ^ t + C * l1⁻¹ ^ t| ≤ |A| + |C| := fun t => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hηb t)
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1.le)
  have hsb : ∀ t, |s'' t| ≤ |c0| := fun t => by
    simp only [hs'']; split_ifs <;> simp
  have hdp := det_path 𝔼 hσ hκ hβ hρ0 hρ1 0 (c := fun t => η ^ t) hηb hsb hpb hfac hfis
  have hπ := (hdp.2 x π v (by exact hft) hπb hvb).1
  refine ⟨by rw [hqc], ?_⟩
  rw [hπ]

/-- Cochrane (2023), p. 131: the impact response to the AR(1) rise, in closed form,
`π_1 = A + C = ρ/(1 − ρη)·[(1 − ρ/λ₁) − (1 − λ₁⁻¹)(1 − λ₂)/(1 − λ₂η)]
  − (1 − ρ/λ₁) ω̃/(1 − ω̃η)`
(the resonance `λ₁η = 1` cancels). The last term is the devaluation of long-term debt,
`ω̃/(1 − ω̃η)`, which grows with persistence. -/
theorem ar1_impact {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρη : 1 - ρ * η ≠ 0) (hoη : 1 - om * η ≠ 0) (hl2η : 1 - lam2 σ β κ * η ≠ 0)
    (hres : lam1 σ β κ * η ≠ 1) :
    ar1A σ β κ η + ar1C σ β κ ρ om η =
      ρ / (1 - ρ * η) * ((1 - ρ * (lam1 σ β κ)⁻¹) -
        (1 - (lam1 σ β κ)⁻¹) * (1 - lam2 σ β κ) / (1 - lam2 σ β κ * η)) -
      (1 - ρ * (lam1 σ β κ)⁻¹) * (om / (1 - om * η)) := by
  have ha := mul_pos hσ hκ
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hr : lam1 σ β κ * η - 1 ≠ 0 := sub_ne_zero.mpr hres
  have h1' : 1 - η * ρ ≠ 0 := by rwa [mul_comm]
  have h2' : 1 - η * om ≠ 0 := by rwa [mul_comm]
  have h3' : 1 - η * lam2 σ β κ ≠ 0 := by rwa [mul_comm]
  have h4' : η * lam1 σ β κ - 1 ≠ 0 := by rwa [mul_comm]
  unfold ar1C ar1A
  rw [sigma_kappa_eq ha hβ]
  field_simp
  ring

/-- Cochrane (2023), §5.3, p. 131, with `ρ = β` (the book's calibrations): the impact response
simplifies to `π_1 = (1 − λ₂)[(ρ/λ₁)/(1 − (ρ/λ₁)η) − ω̃/(1 − ω̃η)]`. -/
theorem ar1_impact_rho_eq_beta {σ β κ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρη : 1 - β * η ≠ 0) (hoη : 1 - om * η ≠ 0) (hl2η : 1 - lam2 σ β κ * η ≠ 0)
    (hqη : 1 - β * (lam1 σ β κ)⁻¹ * η ≠ 0) (hres : lam1 σ β κ * η ≠ 1) :
    ar1A σ β κ η + ar1C σ β κ β om η = (1 - lam2 σ β κ) *
      (β * (lam1 σ β κ)⁻¹ / (1 - β * (lam1 σ β κ)⁻¹ * η) - om / (1 - om * η)) := by
  have ha := mul_pos hσ hκ
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hl2 : lam2 σ β κ = β * (lam1 σ β κ)⁻¹ := by
    have := lam_prod ha hβ
    field_simp
    linarith
  rw [ar1_impact hσ hκ hβ hρη hoη hl2η hres]
  rw [hl2] at hl2η ⊢
  have h1' : 1 - η * β ≠ 0 := by rwa [mul_comm]
  have h2' : 1 - η * om ≠ 0 := by rwa [mul_comm]
  have h5 : lam1 σ β κ - β * η ≠ 0 := by
    intro h0
    apply hqη
    field_simp
    linarith
  have h5' : lam1 σ β κ - η * β ≠ 0 := by rwa [mul_comm η β]
  field_simp
  ring

/-- Cochrane (2023), §5.3, p. 131, and survey-style correction: with `ρ = β`, an AR(1) rate rise
of **any** persistence `0 ≤ η < 1` lowers inflation on impact iff `ω̃ > ρ/λ₁` — exactly the
condition for a permanent rise (`ltd_disinflation_iff`). Persistence is not needed for the
sign of the impact effect ("the interest-rate rise must be persistent" is not a precondition
in the model). -/
theorem ar1_disinflation_iff_rho_eq_beta {σ β κ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hres : lam1 σ β κ * η ≠ 1) :
    ar1A σ β κ η + ar1C σ β κ β om η < 0 ↔ β * (lam1 σ β κ)⁻¹ < om := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have h21 := lam2_lt_one ha hβ
  have h2 := lam2_pos ha hβ
  have hq0 : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  set a := β * (lam1 σ β κ)⁻¹ with hadef
  have ha0 : 0 < a := mul_pos hβ hq0
  have ha1 : a < 1 := by nlinarith
  have haη : 0 < 1 - a * η := by nlinarith
  have hoη : 0 < 1 - om * η := by nlinarith
  rw [ar1_impact_rho_eq_beta hσ hκ hβ (by nlinarith) hoη.ne' (by nlinarith) haη.ne' hres]
  rw [mul_neg_iff]
  have hl : 0 < 1 - lam2 σ β κ := by linarith
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rw [sub_neg, div_lt_div_iff₀ haη hoη] at h
      nlinarith
    · linarith
  · intro h
    refine Or.inl ⟨hl, ?_⟩
    rw [sub_neg, div_lt_div_iff₀ haη hoη]
    nlinarith

/-- Cochrane (2023), §5.3, p. 131 ("A sudden shock, that is believed to be long-lasting … is most
likely to be disinflationary"), precise form with `ρ = β`: when `ω̃ > ρ/λ₁`, the impact
disinflation `(1 − λ₂)[a/(1 − aη) − ω̃/(1 − ω̃η)]` (`a = ρ/λ₁`) is strictly larger the more
persistent the rise — persistence magnifies, but does not create, the disinflation. -/
theorem ar1_magnitude_rho_eq_beta {l2 a om : ℝ} (hl2 : l2 < 1) (ha0 : 0 ≤ a)
    (hom1 : om < 1) (hlt : a < om) :
    StrictAntiOn (fun η => (1 - l2) * (a / (1 - a * η) - om / (1 - om * η))) (Set.Ico 0 1) := by
  intro η₁ h₁ η₂ h₂ hη
  simp only [Set.mem_Ico] at h₁ h₂
  have hom0 : 0 < om := by linarith
  have e : ∀ η, 0 ≤ η → η < 1 → a / (1 - a * η) - om / (1 - om * η) =
      (a - om) / ((1 - a * η) * (1 - om * η)) := fun η h0 h1 => by
    have e1 : 1 - a * η ≠ 0 := by nlinarith
    have e2 : 1 - om * η ≠ 0 := by nlinarith
    rw [div_sub_div _ _ e1 e2]
    ring
  simp only
  rw [e η₁ h₁.1 h₁.2, e η₂ h₂.1 h₂.2]
  have d1 : 0 < (1 - a * η₂) * (1 - om * η₂) := mul_pos (by nlinarith) (by nlinarith)
  have d2 : (1 - a * η₂) * (1 - om * η₂) < (1 - a * η₁) * (1 - om * η₁) := by
    have hx : 1 - a * η₂ ≤ 1 - a * η₁ := by nlinarith
    have hy : 1 - om * η₂ < 1 - om * η₁ := by nlinarith
    exact mul_lt_mul' hx hy (by nlinarith) (by nlinarith)
  have hl : 0 < 1 - l2 := by linarith
  refine mul_lt_mul_of_pos_left ?_ hl
  rw [div_lt_div_iff₀ d1 (d1.trans d2)]
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr d2)]

/-- Cochrane (2023), p. 131 ("there must be long-term debt outstanding"), AR(1) form: with
one-period debt (`ω̃ = 0`) an AR(1) rate rise of any persistence raises inflation on impact
(any `0 < ρ < 1`). -/
theorem ar1_short_debt_no_disinflation {σ β κ ρ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 ≤ η) (hη1 : η < 1) (hres : lam1 σ β κ * η ≠ 1) :
    0 < ar1A σ β κ η + ar1C σ β κ ρ 0 η := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hq0 : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hρη : 0 < 1 - ρ * η := by nlinarith
  have hl2η : 0 < 1 - lam2 σ β κ * η := by nlinarith
  rw [ar1_impact hσ hκ hβ hρη.ne' (by simp) hl2η.ne' hres]
  simp only [zero_mul, sub_zero, zero_div, mul_zero]
  refine mul_pos (div_pos hρ0 hρη) ?_
  have hfrac : (1 - lam2 σ β κ) / (1 - lam2 σ β κ * η) ≤ 1 := by
    rw [div_le_one hl2η]; nlinarith
  have : (1 - (lam1 σ β κ)⁻¹) * (1 - lam2 σ β κ) / (1 - lam2 σ β κ * η) ≤
      1 - (lam1 σ β κ)⁻¹ := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by linarith) hfrac
  nlinarith

end Cochrane.StickyPriceFiscal.LongTermDebt
