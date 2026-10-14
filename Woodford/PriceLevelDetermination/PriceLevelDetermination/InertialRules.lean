/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.ForwardSolution
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt

/-!
# Inertial responses to inflation variation

Woodford (2003), *Interest and Prices*, Chapter 2, §2.3, pp. 94–101, eqs. (2.8)–(2.17),
Propositions 2.7–2.10, with the proofs of Appendix A, §§A.7–A.10, pp. 639–643.

The flexible-price Fisher equation (1.32) `î_t = r̂_t + E_t π_{t+1}` is combined with
two inertial interest-rate rules:

* (2.9) `î_t = ī_t + Φ_π π̄_t`, where `π̄_t = (1 − δ)π_t + δ π̄_{t−1}` is the exponentially
  smoothed inflation rate (2.8);
* (2.12) `î_t = ī_t + ρ(î_{t−1} − ī_{t−1}) + φ_π π_t`, the partial-adjustment rule.

Both start from a predetermined initial condition (`π̄_{−1}`, resp. `î_{−1} − ī_{−1}`), known at
date `0`. All model statements hold for an arbitrary `ExpectationSystem`. An equilibrium is a
pair of bounded adapted processes `(π, î)`; determinacy means a unique one for every bounded
adapted `{r̂, ī}` and every bounded initial condition.

## Main results

* `gap_equation`, `interest_equation`: the (A.8) equation `(φ_π + ρ)x_t = E_t x_{t+1} +
  φ_π(r̂_t − ī_t)` for `x = î − ī` (and its printed form in `î`).
* `determinate8_iff`: rule (2.12) is determinate **iff** `φ_π ≠ 0` and `|φ_π + ρ| > 1` (A.22);
  `prop_2_8`: for `φ_π, ρ ≥ 0` iff `φ_π > 0` and `φ_π + ρ > 1` (2.13);
  `determinate8_superinertial_neg`, `determinate8_exists_neg`, `determinate8_large_neg`: the
  negative-`φ_π` extensions of §A.8; `not_determinate8_zero`; `continuum_eqm8`: a continuum
  of equilibria when (A.22) fails; `eq_2_15`, `eq_2_14`: the solution.
* `smoothedRule_iff_inertialRule`: (2.9) is (2.12) with `ρ = δ`, `φ_π = (1 − δ)Φ_π`
  (exactly, for every `δ`), and `inertialRule_iff_smoothedRule` (`ρ ≠ 1`, `φ_π ≠ 0`,
  `Φ_π = φ_π/(1 − ρ)`); `determinate7_iff`, `prop_2_7`: Prop. 2.7 (`Φ_π > 1`);
  `eq_A_20`, `eq_2_10`, `eq_2_11`: its proof and solution; `taylor_principle_equiv`:
  `Φ_π > 1 ⟺ φ_π + ρ > 1` for `ρ < 1`.
* `partialAdjust_iff_series`: with an infinite past, `y_t = δ y_{t−1} + c π_t` (bounded) iff
  `y_t = c ∑ δʲ π_{t−j}`; hence (2.8) (`eq_2_8_recursion`) and the moving-average form of
  (2.12) for `ρ < 1` (`rule_iff_smoothed_series`).
* AR(1) natural rate, `ī = 0`: `ar1_interest` (`î = φ_π/(φ_π+ρ−ρ_r) r̂`), `ar1_inflation`,
  `ar1_innovation_loadings` (the `(ρ_r − ρ)` ratio of p. 97), the impulse responses
  `irfR`, `irfI`, `irfPi` with `ma_rep_r`, `ma_rep_i`, `ma_rep_pi` (pathwise MA representation
  of the equilibrium) and `stationary_ma_pi` (infinite past), persistence facts.
* Beveridge–Nelson (2.16): `bn_innovation` (the innovation is
  `(1−ρ)(1−ρ_r)⁻¹(φ_π+ρ−ρ_r)⁻¹ ε_t`), `bn_limit`, `bn_coeff_eq_zero_iff` (zero iff `ρ = 1`).
* Fn. 32: `fn32_first_difference`.
* Variances as sums of squared impulse responses (`msq`, `acov1`): `msq_irfR`, `msq_irfI`,
  `acov1_irfI`, `msq_irfPi` (A.24), `var_pi_book_route`.
* **Prop. 2.9 corrected** (error E2): `prop_2_9_corrected` (under `var(π) ≤ var(r̂)`),
  `msq_irfI_eq_sq` (the corrected (A.25) with the square), and the refutations
  `prop_2_9_false`, `prop_2_9_printed_false`, `e2_counterexample` (`ρ_r = .8`,
  `var(π) = 2 var(r̂)`: the required `φ_π` is negative, and `var(î)/var(r̂)` rises from
  `13/5 − 4√10/5 ≈ 0.070` at `ρ = 2` to at least `4/25 = 0.16` at `ρ = 5`).
* Prop. 2.10: `prop_2_10` (via the predetermined forward solution on a shifted expectation
  system `shiftE`).

The nonlinear "local determinacy" part of Props 2.7–2.8 and the remark on p. 100 (only the
rule's values on the bounded range matter) concern the nonlinear model and are not treated here.
-/

namespace Woodford.PriceLevelDetermination.InertialRules

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Lags and the model -/

/-- Woodford (2003), (2.12), p. 96: the one-period lag `x_{t−1}` of a process `x`, with the
predetermined initial value `x_{−1} = x₀`. -/
def lag (x₀ : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => x₀
  | t + 1 => x t

/-- Woodford (2003), (2.12), p. 96: the lag of an adapted process with an initial value known
at date `0` is adapted. -/
theorem lag_adapted {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 x₀ = x₀) (hx : 𝔼.Adapted x) :
    𝔼.Adapted (lag x₀ x) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t =>
    change 𝔼.E (t + 1) (x t) = x t
    calc 𝔼.E (t + 1) (x t) = 𝔼.E (t + 1) (𝔼.E t (x t)) := by rw [hx t]
      _ = 𝔼.E t (x t) := 𝔼.known (Nat.le_succ t) _
      _ = x t := hx t

/-- Woodford (2003), (2.12), p. 96: the lag of a bounded process with a bounded initial value
is bounded. -/
theorem lag_bounded {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} {M₀ M : ℝ} (h0 : ∀ ω, |x₀ ω| ≤ M₀)
    (hx : ∀ t ω, |x t ω| ≤ M) (t : ℕ) (ω : Ω) : |lag x₀ x t ω| ≤ max M₀ M := by
  cases t with
  | zero => exact (h0 ω).trans (le_max_left _ _)
  | succ t => exact (hx t ω).trans (le_max_right _ _)

/-- Woodford (2003), eq. (1.32), p. 79: the log-linear Fisher equation
`î_t = r̂_t + E_t π_{t+1}`. -/
def Fisher (r π i : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (π (t + 1))

/-- Woodford (2003), eq. (2.12), p. 96: the inertial rule
`î_t − ī_t = ρ(î_{t−1} − ī_{t−1}) + φ_π π_t`, with predetermined `î_{−1} − ī_{−1} = x₀`. -/
def InertialRule (φ ρ : ℝ) (ibar : ℕ → Ω → ℝ) (x₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t - ibar t = ρ • lag x₀ (fun s => i s - ibar s) t + φ • π t

/-- Woodford (2003), Prop. 2.8, p. 96: `(π, î)` is a bounded rational-expectations equilibrium
under rule (2.12): bounded, adapted, the Fisher equation (1.32) and the rule (2.12). -/
def IsEqm8 (φ ρ : ℝ) (r ibar : ℕ → Ω → ℝ) (x₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  BoundedProc π ∧ BoundedProc i ∧ 𝔼.Adapted π ∧ 𝔼.Adapted i ∧ Fisher 𝔼 r π i ∧
    InertialRule φ ρ ibar x₀ π i

/-- Woodford (2003), §2.3, pp. 95–96: admissible exogenous data — bounded adapted `{r̂, ī}`
and a bounded initial condition known at date `0`. -/
def Exog (r ibar : ℕ → Ω → ℝ) (x₀ : Ω → ℝ) : Prop :=
  BoundedProc r ∧ BoundedProc ibar ∧ 𝔼.Adapted r ∧ 𝔼.Adapted ibar ∧ 𝔼.E 0 x₀ = x₀ ∧
    ∃ M, ∀ ω, |x₀ ω| ≤ M

/-- Woodford (2003), Prop. 2.8, p. 96: rule (2.12) is determinate — for all admissible
exogenous data there is exactly one bounded equilibrium `(π, î)`. -/
def Determinate8 (φ ρ : ℝ) : Prop :=
  ∀ r ibar : ℕ → Ω → ℝ, ∀ x₀ : Ω → ℝ, Exog 𝔼 r ibar x₀ →
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), IsEqm8 𝔼 φ ρ r ibar x₀ q.1 q.2

/-- Woodford (2003), proof of Prop. 2.8, §A.8, pp. 640–641: in any equilibrium of (1.32) and
(2.12) with `î, ī` adapted, the gap `x = î − ī` satisfies
`(φ_π + ρ)x_t = E_t x_{t+1} + φ_π(r̂_t − ī_t)`. -/
theorem gap_equation {φ ρ : ℝ} {r ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hia : 𝔼.Adapted i)
    (hba : 𝔼.Adapted ibar) (hF : Fisher 𝔼 r π i) (hR : InertialRule φ ρ ibar x₀ π i)
    (t : ℕ) :
    (φ + ρ) • (i t - ibar t) = 𝔼.E t (i (t + 1) - ibar (t + 1)) + φ • (r t - ibar t) := by
  have h1 : i (t + 1) - ibar (t + 1) = ρ • (i t - ibar t) + φ • π (t + 1) := hR (t + 1)
  have h2 : 𝔼.E t (i (t + 1) - ibar (t + 1)) =
      ρ • (i t - ibar t) + φ • 𝔼.E t (π (t + 1)) := by
    rw [h1, map_add, map_smul, map_smul, map_sub, hia t, hba t]
  rw [h2]
  funext ω
  have h3 := congrFun (hF t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h3 ⊢
  linear_combination φ * h3

/-- Woodford (2003), §A.8, p. 641 (the printed equation):
`(φ_π + ρ)î_t = E_t î_{t+1} + φ_π r̂_t + ρ ī_t − E_t ī_{t+1}`. -/
theorem interest_equation {φ ρ : ℝ} {r ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hia : 𝔼.Adapted i) (hba : 𝔼.Adapted ibar) (hF : Fisher 𝔼 r π i)
    (hR : InertialRule φ ρ ibar x₀ π i) (t : ℕ) :
    (φ + ρ) • i t = 𝔼.E t (i (t + 1)) + φ • r t + ρ • ibar t - 𝔼.E t (ibar (t + 1)) := by
  have h := gap_equation 𝔼 hia hba hF hR t
  rw [map_sub] at h
  funext ω
  have h' := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
  linear_combination h'

/-- Woodford (2003), §A.8, p. 641: for `φ_π + ρ ≠ 0` the gap equation is of the form (A.14),
`x_t = a E_t x_{t+1} + a φ_π (r̂_t − ī_t)` with `a = (φ_π + ρ)⁻¹`. -/
theorem gap_forward {φ ρ : ℝ} (hne : φ + ρ ≠ 0) {r ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hia : 𝔼.Adapted i) (hba : 𝔼.Adapted ibar) (hF : Fisher 𝔼 r π i)
    (hR : InertialRule φ ρ ibar x₀ π i) (t : ℕ) :
    i t - ibar t = (φ + ρ)⁻¹ • 𝔼.E t (i (t + 1) - ibar (t + 1)) +
      ((φ + ρ)⁻¹ * φ) • (r t - ibar t) := by
  have h := gap_equation 𝔼 hia hba hF hR t
  funext ω
  have h' := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
  have hx : i t ω - ibar t ω = (φ + ρ)⁻¹ * ((φ + ρ) * (i t ω - ibar t ω)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hx, h']
  ring

/-- Woodford (2003), §A.8, p. 641: inverting (2.12), `π_t = φ_π⁻¹(x_t − ρ x_{t−1})`. -/
theorem infl_eq {φ ρ : ℝ} (hφ : φ ≠ 0) {ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hR : InertialRule φ ρ ibar x₀ π i) (t : ℕ) :
    π t = φ⁻¹ • ((i t - ibar t) - ρ • lag x₀ (fun s => i s - ibar s) t) := by
  rw [hR t, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hφ, one_smul]

/-- Woodford (2003), §A.8, p. 641, and Lemma (A.14)–(A.16): if `|φ_π + ρ| > 1`, the gap
`x = î − ī` of every bounded equilibrium is the forward series. -/
theorem eqm8_gap_eq {φ ρ : ℝ} (hc : 1 < |φ + ρ|) {r ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hex : Exog 𝔼 r ibar x₀) (hq : IsEqm8 𝔼 φ ρ r ibar x₀ π i) :
    (fun s => i s - ibar s) =
      𝔼.forwardSeries (φ + ρ)⁻¹ (fun t => ((φ + ρ)⁻¹ * φ) • (r t - ibar t)) := by
  obtain ⟨⟨Mr, hr⟩, ⟨Mi, hi⟩, hra, hia, -, -⟩ := hex
  obtain ⟨-, ⟨Mx, hMx⟩, -, hqa, hF, hR⟩ := hq
  have hne : φ + ρ ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have ha : |(φ + ρ)⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  have hub : ∀ t ω, |(((φ + ρ)⁻¹ * φ) • (r t - ibar t)) ω| ≤ |(φ + ρ)⁻¹ * φ| * (Mr + Mi) := by
    intro t ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω)))
      (by positivity)
  have hua : 𝔼.Adapted (fun t => ((φ + ρ)⁻¹ * φ) • (r t - ibar t)) := fun t => by
    simp only [map_smul, map_sub, hra t, hia t]
  refine 𝔼.forward_unique ha (fun t => gap_forward 𝔼 hne hqa hia hF hR t)
    (fun t => ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua t) ⟨Mx + Mi, fun t ω => ?_⟩
    (ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub)
  exact (abs_sub _ _).trans (add_le_add (hMx t ω) (hi t ω))

/-! ### Prop. 2.8: sufficiency -/

/-- Woodford (2003), Prop. 2.8, p. 96, and §A.8, pp. 640–641 (sufficiency, in the exact form
(A.22)): if `φ_π ≠ 0` and `|φ_π + ρ| > 1`, rule (2.12) is determinate. -/
theorem determinate8_of {φ ρ : ℝ} (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|) : Determinate8 𝔼 φ ρ := by
  intro r ibar x₀ hex
  obtain ⟨⟨Mr, hr⟩, ⟨Mi, hi⟩, hra, hia, h0, ⟨M0, hM0⟩⟩ := hex
  have hne : φ + ρ ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have ha : |(φ + ρ)⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  set a : ℝ := (φ + ρ)⁻¹ with ha_def
  set u : ℕ → Ω → ℝ := fun t => (a * φ) • (r t - ibar t) with hu_def
  have hub : ∀ t ω, |u t ω| ≤ |a * φ| * (Mr + Mi) := by
    intro t ω
    simp only [hu_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω)))
      (by positivity)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu_def, map_smul, map_sub, hra t, hia t]
  set x := 𝔼.forwardSeries a u with hx_def
  have hxs : ∀ t, x t = a • 𝔼.E t (x (t + 1)) + u t :=
    ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua
  obtain ⟨Mx, hMx⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub
  have hxa : 𝔼.Adapted x := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hub
  have hla : 𝔼.Adapted (lag x₀ x) := lag_adapted 𝔼 h0 hxa
  -- the key relation `E_t x_{t+1} − ρ x_t = φ (x_t − (r_t − ī_t))`
  have hkey : ∀ t ω, 𝔼.E t (x (t + 1)) ω = (φ + ρ) * x t ω - φ * (r t ω - ibar t ω) := by
    intro t ω
    have h := congrFun (hxs t) ω
    simp only [hu_def, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ha_def] at h
    rw [h]
    field_simp
    ring
  refine ⟨(fun t => φ⁻¹ • (x t - ρ • lag x₀ x t), fun t => ibar t + x t),
    ⟨⟨|φ⁻¹| * (Mx + |ρ| * max M0 Mx), fun t ω => ?_⟩, ⟨Mi + Mx, fun t ω => ?_⟩,
      fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) ?_))
      (abs_nonneg _)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (lag_bounded hM0 hMx t ω) (abs_nonneg _)
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hi t ω) (hMx t ω))
  · simp only [map_smul, map_sub, hxa t, hla t]
  · simp only [map_add, hia t, hxa t]
  · funext ω
    change ibar t ω + x t ω = r t ω + 𝔼.E t (φ⁻¹ • (x (t + 1) - ρ • x t)) ω
    rw [map_smul, map_sub, map_smul, hxa t]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hkey t ω]
    field_simp
    ring
  · have hix : (fun s => ibar s + x s - ibar s) = x := by
      funext s; exact add_sub_cancel_left _ _
    change ibar t + x t - ibar t = ρ • lag x₀ (fun s => ibar s + x s - ibar s) t +
      φ • φ⁻¹ • (x t - ρ • lag x₀ x t)
    rw [hix, smul_inv_smul₀ hφ, add_sub_cancel_left, add_sub_cancel]
  · rintro ⟨π', i'⟩ hq
    have hgap := eqm8_gap_eq 𝔼 hc ⟨⟨Mr, hr⟩, ⟨Mi, hi⟩, hra, hia, h0, ⟨M0, hM0⟩⟩ hq
    have hx' : (fun s => i' s - ibar s) = x := hgap
    have hi' : i' = fun t => ibar t + x t := by
      funext t
      rw [← congrFun hx' t]
      exact (add_sub_cancel _ _).symm
    refine Prod.ext ?_ hi'
    funext t
    change π' t = φ⁻¹ • (x t - ρ • lag x₀ x t)
    have hR : InertialRule φ ρ ibar x₀ π' i' := hq.2.2.2.2.2
    rw [infl_eq hφ hR t, hx', show i' t - ibar t = x t from congrFun hx' t]

/-! ### Prop. 2.8: necessity -/

/-- Woodford (2003), Prop. 2.8, p. 96: with `r̂ = ī = 0` and `x₀ = 0`, `(π, î) = (0, 0)` is a
bounded equilibrium under every rule (2.12). -/
theorem zero_isEqm8 (φ ρ : ℝ) : IsEqm8 𝔼 φ ρ 0 0 0 0 0 := by
  refine ⟨⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, fun t => map_zero _,
    fun t => map_zero _, fun t => ?_, fun t => ?_⟩
  · simp
  · cases t <;> simp [lag]

/-- Woodford (2003), §2.3: zero exogenous data are admissible. -/
theorem exog_zero : Exog 𝔼 0 0 0 :=
  ⟨⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, fun _ => map_zero _, fun _ => map_zero _,
    map_zero _, ⟨0, fun _ => by simp⟩⟩

/-- Woodford (2003), §A.8, p. 641 (necessity): if `φ_π = 0` or `|φ_π + ρ| ≤ 1`, then with
`r̂ = ī = 0` and `x₀ = 0` there is a bounded equilibrium other than `(0, 0)`. For `φ_π = 0`
inflation at date `0` is free (`π = (1, 0, 0, …)`, `î = 0`: Prop. 2.5 applies); otherwise
`î_t = (φ_π + ρ)ᵗ`, `π_0 = φ_π⁻¹`, `π_{t+1} = (φ_π + ρ)ᵗ`. -/
theorem exists_other_eqm8 [Nonempty Ω] {φ ρ : ℝ} (h : ¬ (φ ≠ 0 ∧ 1 < |φ + ρ|)) :
    ∃ q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), IsEqm8 𝔼 φ ρ 0 0 0 q.1 q.2 ∧ q ≠ 0 := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  by_cases hφ : φ = 0
  · subst hφ
    refine ⟨(lag (fun _ => 1) 0, 0), ⟨⟨max 1 0, fun t ω => lag_bounded (M₀ := 1)
      (fun _ => by simp) (fun _ _ => by simp) t ω⟩, ⟨0, fun _ _ => by simp⟩,
      lag_adapted 𝔼 (𝔼.const 0 1) (fun _ => map_zero _), fun _ => map_zero _,
      fun t => ?_, fun t => ?_⟩, ?_⟩
    · change (0 : Ω → ℝ) = 0 + 𝔼.E t 0
      simp
    · cases t <;> simp [lag]
    · intro hq
      have := congrFun (congrFun (congrArg Prod.fst hq) 0) ω₀
      simp [lag] at this
  · have hc : |φ + ρ| ≤ 1 := by
      by_contra hc
      exact h ⟨hφ, lt_of_not_ge hc⟩
    set c := φ + ρ with hc_def
    have hpow : ∀ t, |c ^ t| ≤ 1 := fun t => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
    refine ⟨(lag (fun _ => φ⁻¹) (fun t _ => c ^ t), fun t _ => c ^ t),
      ⟨⟨max |φ⁻¹| 1, fun t ω => lag_bounded (fun _ => le_rfl) (fun t _ => hpow t) t ω⟩,
      ⟨1, fun t _ => hpow t⟩, lag_adapted 𝔼 (𝔼.const 0 _) (fun t => 𝔼.const t _),
      fun t => 𝔼.const t _, fun t => ?_, fun t => ?_⟩, ?_⟩
    · change (fun _ => c ^ t) = 0 + 𝔼.E t (fun _ => c ^ t)
      rw [𝔼.const, zero_add]
    · funext ω
      cases t with
      | zero => simp [lag, hφ]
      | succ t =>
        simp only [lag, Pi.sub_apply, Pi.zero_apply, sub_zero, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, pow_succ, hc_def]
        ring
    · intro hq
      have := congrFun (congrFun (congrArg Prod.snd hq) 0) ω₀
      simp at this

/-- Woodford (2003), §A.8, p. 641: with zero exogenous data the equilibrium conditions are
linear and homogeneous, so equilibria can be rescaled. -/
theorem isEqm8_zero_smul {φ ρ : ℝ} {π i : ℕ → Ω → ℝ} (hq : IsEqm8 𝔼 φ ρ 0 0 0 π i) (k : ℝ) :
    IsEqm8 𝔼 φ ρ 0 0 0 (k • π) (k • i) := by
  obtain ⟨⟨Mπ, hMπ⟩, ⟨Mi, hMi⟩, hπa, hia, hF, hR⟩ := hq
  refine ⟨⟨|k| * Mπ, fun t ω => ?_⟩, ⟨|k| * Mi, fun t ω => ?_⟩, fun t => ?_, fun t => ?_,
    fun t => ?_, fun t => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMπ t ω) (abs_nonneg k)
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMi t ω) (abs_nonneg k)
  · simp only [Pi.smul_apply, map_smul, hπa t]
  · simp only [Pi.smul_apply, map_smul, hia t]
  · funext ω
    have h := congrFun (hF t) ω
    simp only [Pi.smul_apply, map_smul, Pi.add_apply, Pi.zero_apply, smul_eq_mul,
      zero_add] at h ⊢
    rw [h]
  · funext ω
    have h := congrFun (hR t) ω
    cases t <;>
    simp only [lag, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul,
      sub_zero] at h ⊢ <;>
    linear_combination k * h

/-- Woodford (2003), §A.8, p. 641: if `φ_π = 0` or `|φ_π + ρ| ≤ 1` there is a continuum
(an injective real-indexed family) of bounded equilibria for the same data `r̂ = ī = 0`,
`x₀ = 0` ("an uncountably infinite number of solutions"). -/
theorem continuum_eqm8 [Nonempty Ω] {φ ρ : ℝ} (h : ¬ (φ ≠ 0 ∧ 1 < |φ + ρ|)) :
    ∃ fam : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Function.Injective fam ∧ ∀ k, IsEqm8 𝔼 φ ρ 0 0 0 (fam k).1 (fam k).2 := by
  obtain ⟨q, hq, hne⟩ := exists_other_eqm8 𝔼 h
  exact ⟨fun k => k • q, smul_left_injective ℝ hne, fun k => isEqm8_zero_smul 𝔼 hq k⟩

/-- Woodford (2003), Prop. 2.8, p. 96, and §A.8, pp. 640–641, exact form: rule (2.12) is
determinate if and only if `φ_π ≠ 0` and `|φ_π + ρ| > 1` (condition (A.22)). -/
theorem determinate8_iff [Nonempty Ω] (φ ρ : ℝ) :
    Determinate8 𝔼 φ ρ ↔ (φ ≠ 0 ∧ 1 < |φ + ρ|) := by
  refine ⟨fun hdet => ?_, fun h => determinate8_of 𝔼 h.1 h.2⟩
  by_contra h
  obtain ⟨q, hq, hne⟩ := exists_other_eqm8 𝔼 h
  obtain ⟨q₀, -, huniq⟩ := hdet 0 0 0 (exog_zero 𝔼)
  have e1 := huniq q hq
  have e2 := huniq (0, 0) (zero_isEqm8 𝔼 φ ρ)
  exact hne (e1.trans (e2.symm.trans rfl))

/-- Woodford (2003), **Proposition 2.8**, p. 96: for `φ_π, ρ ≥ 0`, rule (2.12) is determinate
if and only if `φ_π > 0` and `φ_π + ρ > 1` (2.13). -/
theorem prop_2_8 [Nonempty Ω] {φ ρ : ℝ} (hφ : 0 ≤ φ) (hρ : 0 ≤ ρ) :
    Determinate8 𝔼 φ ρ ↔ (0 < φ ∧ 1 < φ + ρ) := by
  rw [determinate8_iff, abs_of_nonneg (by linarith)]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne hφ (Ne.symm h1), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.ne', h2⟩

/-- Woodford (2003), p. 97 and §A.8, p. 641: every nonzero `φ_π > −(ρ − 1)` gives
determinacy. (No hypothesis on `ρ` is needed; for a superinertial rule, `ρ > 1`, the range
includes moderately negative values, `determinate8_exists_neg`.) -/
theorem determinate8_superinertial_neg {φ ρ : ℝ} (h1 : 1 - ρ < φ) (h0 : φ ≠ 0) :
    Determinate8 𝔼 φ ρ :=
  determinate8_of 𝔼 h0 (by rw [abs_of_pos (by linarith)]; linarith)

/-- Woodford (2003), p. 97: for a superinertial rule (`ρ > 1`) some negative inflation
response, e.g. `φ_π = (1 − ρ)/2`, gives a determinate equilibrium. -/
theorem determinate8_exists_neg {ρ : ℝ} (hρ : 1 < ρ) : ∃ φ < 0, Determinate8 𝔼 φ ρ :=
  ⟨(1 - ρ) / 2, by linarith, determinate8_superinertial_neg 𝔼 (by linarith) (by linarith)⟩

/-- Woodford (2003), §A.8, p. 641: every `φ_π < −(1 + ρ)` gives determinacy (for any
`ρ ≥ 0`, even `ρ < 1`). -/
theorem determinate8_large_neg {φ ρ : ℝ} (hρ : 0 ≤ ρ) (h : φ < -(1 + ρ)) :
    Determinate8 𝔼 φ ρ :=
  determinate8_of 𝔼 (by intro h'; linarith) (by rw [abs_of_neg (by linarith)]; linarith)

/-- Woodford (2003), p. 97: determinacy requires `φ_π ≠ 0` (Prop. 2.5 applies otherwise),
whatever the inertia `ρ`. -/
theorem not_determinate8_zero [Nonempty Ω] (ρ : ℝ) : ¬ Determinate8 𝔼 0 ρ := by
  rw [determinate8_iff]; exact fun h => h.1 rfl

/-- Woodford (2003), eq. (2.15), p. 96: in the determinate case the interest rate is
`î_t = ī_t + ∑_j φ_π (φ_π + ρ)^{−(j+1)} E_t[r̂_{t+j} − ī_{t+j}]`. -/
theorem eq_2_15 {φ ρ : ℝ} (hc : 1 < |φ + ρ|) {r ibar π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hex : Exog 𝔼 r ibar x₀) (hq : IsEqm8 𝔼 φ ρ r ibar x₀ π i) (t : ℕ) (ω : Ω) :
    i t ω = ibar t ω +
      ∑' j, φ * ((φ + ρ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω := by
  have h : i t ω - ibar t ω = 𝔼.forwardSeries (φ + ρ)⁻¹
      (fun t => ((φ + ρ)⁻¹ * φ) • (r t - ibar t)) t ω :=
    congrFun (congrFun (eqm8_gap_eq 𝔼 hc hex hq) t) ω
  rw [← sub_add_cancel (i t ω) (ibar t ω), h, add_comm]
  congr 1
  change ∑' k, _ = _
  refine tsum_congr fun k => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), eq. (2.14), p. 96: in the determinate case inflation is
`π_t = −(ρ/φ_π)(î_{t−1} − ī_{t−1}) + ∑_j (φ_π + ρ)^{−(j+1)} E_t[r̂_{t+j} − ī_{t+j}]`. -/
theorem eq_2_14 {φ ρ : ℝ} (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|) {r ibar π i : ℕ → Ω → ℝ}
    {x₀ : Ω → ℝ} (hex : Exog 𝔼 r ibar x₀) (hq : IsEqm8 𝔼 φ ρ r ibar x₀ π i) (t : ℕ)
    (ω : Ω) :
    π t ω = -(ρ / φ) * lag x₀ (fun s => i s - ibar s) t ω +
      ∑' j, ((φ + ρ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω := by
  have h15 := eq_2_15 𝔼 hc hex hq t ω
  have hπ := congrFun (infl_eq hφ hq.2.2.2.2.2 t) ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hπ
  rw [hπ, h15]
  have hs : ∑' j, φ * ((φ + ρ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω =
      φ * ∑' j, ((φ + ρ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [add_sub_cancel_left, hs]
  field_simp
  ring

/-! ### Prop. 2.7: the smoothed-inflation rule (2.9) -/

/-- Woodford (2003), eq. (2.8), p. 94, in the partial-adjustment form of p. 95: smoothed
inflation `π̄_t = (1 − δ)π_t + δ π̄_{t−1}`, from a predetermined `π̄_{−1} = pb₀`. -/
def smoothed (δ : ℝ) (pb₀ : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => (1 - δ) • π 0 + δ • pb₀
  | t + 1 => (1 - δ) • π (t + 1) + δ • smoothed δ pb₀ π t

/-- Woodford (2003), p. 95: `π̄_t = (1 − δ)π_t + δ π̄_{t−1}` at every date. -/
theorem smoothed_eq (δ : ℝ) (pb₀ : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    smoothed δ pb₀ π t = (1 - δ) • π t + δ • lag pb₀ (smoothed δ pb₀ π) t := by
  cases t <;> rfl

/-- Woodford (2003), eq. (2.11), p. 95 (and (A.19)): inverting (2.8),
`π_t = (π̄_t − δ π̄_{t−1})/(1 − δ)`. -/
theorem eq_2_11 {δ : ℝ} (hδ : δ ≠ 1) (pb₀ : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    π t = (1 - δ)⁻¹ • (smoothed δ pb₀ π t - δ • lag pb₀ (smoothed δ pb₀ π) t) := by
  rw [smoothed_eq δ pb₀ π t, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hδ.symm), one_smul]

/-- Woodford (2003), eq. (2.8), p. 94, with a finite history: `π̄_t = (1 − δ)∑_{j ≤ t} δʲ π_{t−j}
+ δ^{t+1} π̄_{−1}`. -/
theorem smoothed_finite (δ : ℝ) (pb₀ : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    smoothed δ pb₀ π t ω =
      (1 - δ) * ∑ j ∈ Finset.range (t + 1), δ ^ j * π (t - j) ω + δ ^ (t + 1) * pb₀ ω := by
  induction t with
  | zero => simp [smoothed]
  | succ t ih =>
    have hs : ∑ j ∈ Finset.range (t + 1 + 1), δ ^ j * π (t + 1 - j) ω =
        δ * ∑ j ∈ Finset.range (t + 1), δ ^ j * π (t - j) ω + π (t + 1) ω := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [Nat.add_sub_add_right, pow_zero, one_mul, Nat.sub_zero]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [smoothed, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ih, hs]
    ring

/-- Woodford (2003), p. 95: smoothed inflation is adapted when inflation is and `π̄_{−1}` is
known at date `0`. -/
theorem smoothed_adapted {δ : ℝ} {pb₀ : Ω → ℝ} {π : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 pb₀ = pb₀)
    (hπ : 𝔼.Adapted π) : 𝔼.Adapted (smoothed δ pb₀ π) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 ((1 - δ) • π 0 + δ • pb₀) = _
    rw [map_add, map_smul, map_smul, hπ 0, h0]
    rfl
  | succ t ih =>
    change 𝔼.E (t + 1) ((1 - δ) • π (t + 1) + δ • smoothed δ pb₀ π t) = _
    have hk : 𝔼.E (t + 1) (smoothed δ pb₀ π t) = smoothed δ pb₀ π t := by
      calc _ = 𝔼.E (t + 1) (𝔼.E t (smoothed δ pb₀ π t)) := by rw [ih]
        _ = 𝔼.E t (smoothed δ pb₀ π t) := 𝔼.known (Nat.le_succ t) _
        _ = _ := ih
    rw [map_add, map_smul, map_smul, hπ (t + 1), hk]
    rfl

/-- Woodford (2003), eq. (2.9), p. 95: the rule `î_t = ī_t + Φ_π π̄_t`. -/
def SmoothedRule (Φ δ : ℝ) (ibar : ℕ → Ω → ℝ) (pb₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = ibar t + Φ • smoothed δ pb₀ π t

/-- Woodford (2003), Prop. 2.7, p. 95: `(π, î)` is a bounded equilibrium under rule (2.9). -/
def IsEqm7 (Φ δ : ℝ) (r ibar : ℕ → Ω → ℝ) (pb₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  BoundedProc π ∧ BoundedProc i ∧ 𝔼.Adapted π ∧ 𝔼.Adapted i ∧ Fisher 𝔼 r π i ∧
    SmoothedRule Φ δ ibar pb₀ π i

/-- Woodford (2003), Prop. 2.7, p. 95: rule (2.9) is determinate. -/
def Determinate7 (Φ δ : ℝ) : Prop :=
  ∀ r ibar : ℕ → Ω → ℝ, ∀ pb₀ : Ω → ℝ, Exog 𝔼 r ibar pb₀ →
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), IsEqm7 𝔼 Φ δ r ibar pb₀ q.1 q.2

/-- Woodford (2003), p. 96, "(2.12) ⟺ (2.9)": the smoothed-inflation rule (2.9) with decay
`δ` and response `Φ_π` is exactly the inertial rule (2.12) with `ρ = δ`, `φ_π = (1 − δ)Φ_π`
and initial gap `x₀ = Φ_π π̄_{−1}` (for every `δ`, every inflation path). -/
theorem smoothedRule_iff_inertialRule (Φ δ : ℝ) (ibar : ℕ → Ω → ℝ) (pb₀ : Ω → ℝ)
    (π i : ℕ → Ω → ℝ) :
    SmoothedRule Φ δ ibar pb₀ π i ↔ InertialRule ((1 - δ) * Φ) δ ibar (Φ • pb₀) π i := by
  constructor
  · intro h
    have hx : (fun s => i s - ibar s) = fun s => Φ • smoothed δ pb₀ π s := by
      funext s; rw [h s, add_sub_cancel_left]
    intro t
    rw [hx, h t, add_sub_cancel_left]
    funext ω
    cases t with
    | zero => simp only [smoothed, lag, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    | succ t => simp only [smoothed, lag, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · intro h
    have hx : ∀ t, i t - ibar t = Φ • smoothed δ pb₀ π t := by
      intro t
      induction t with
      | zero =>
        rw [h 0]
        funext ω
        simp only [smoothed, lag, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      | succ t ih =>
        rw [h (t + 1)]
        change δ • (i t - ibar t) + ((1 - δ) * Φ) • π (t + 1) = _
        rw [ih]
        funext ω
        simp only [smoothed, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    intro t
    rw [← hx t, add_sub_cancel]

/-- Woodford (2003), p. 96: for `ρ ≠ 1` and `φ_π ≠ 0`, rule (2.12) is rule (2.9) with
`δ = ρ` and `Φ_π = φ_π/(1 − ρ)`. -/
theorem inertialRule_iff_smoothedRule {φ ρ : ℝ} (hφ : φ ≠ 0) (hρ : ρ ≠ 1)
    (ibar : ℕ → Ω → ℝ) (x₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) :
    InertialRule φ ρ ibar x₀ π i ↔
      SmoothedRule (φ / (1 - ρ)) ρ ibar ((φ / (1 - ρ))⁻¹ • x₀) π i := by
  have h1 : (1 - ρ) ≠ 0 := sub_ne_zero.mpr hρ.symm
  have hΦ : φ / (1 - ρ) ≠ 0 := div_ne_zero hφ h1
  rw [smoothedRule_iff_inertialRule, smul_inv_smul₀ hΦ, mul_div_cancel₀ φ h1]

/-- Woodford (2003), p. 96: an equilibrium under (2.9) is an equilibrium under the
corresponding rule (2.12), and conversely. -/
theorem eqm7_iff_eqm8 (Φ δ : ℝ) (r ibar : ℕ → Ω → ℝ) (pb₀ : Ω → ℝ) (π i : ℕ → Ω → ℝ) :
    IsEqm7 𝔼 Φ δ r ibar pb₀ π i ↔ IsEqm8 𝔼 ((1 - δ) * Φ) δ r ibar (Φ • pb₀) π i := by
  unfold IsEqm7 IsEqm8
  rw [smoothedRule_iff_inertialRule]

/-- Woodford (2003), §2.3: scaling the initial condition keeps the data admissible. -/
theorem exog_smul (Φ : ℝ) {r ibar : ℕ → Ω → ℝ} {pb₀ : Ω → ℝ} (hex : Exog 𝔼 r ibar pb₀) :
    Exog 𝔼 r ibar (Φ • pb₀) := by
  obtain ⟨hr, hi, hra, hia, h0, ⟨M, hM⟩⟩ := hex
  refine ⟨hr, hi, hra, hia, by rw [map_smul, h0], ⟨|Φ| * M, fun ω => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg Φ)

/-- Woodford (2003), Prop. 2.7, p. 95, and §A.7, pp. 639–640, exact form: for `0 < δ < 1`,
rule (2.9) is determinate if and only if `|δ + (1 − δ)Φ_π| > 1`. -/
theorem determinate7_iff [Nonempty Ω] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (Φ : ℝ) :
    Determinate7 𝔼 Φ δ ↔ 1 < |δ + (1 - δ) * Φ| := by
  constructor
  · intro hdet
    by_contra hc
    have h8 : ¬ ((1 - δ) * Φ ≠ 0 ∧ 1 < |(1 - δ) * Φ + δ|) := by
      rintro ⟨-, h⟩; exact hc (by rwa [add_comm])
    obtain ⟨q, hq, hne⟩ := exists_other_eqm8 𝔼 h8
    have hq' : IsEqm7 𝔼 Φ δ 0 0 0 q.1 q.2 :=
      (eqm7_iff_eqm8 𝔼 _ _ _ _ _ _ _).mpr (by rw [smul_zero]; exact hq)
    have hz : IsEqm7 𝔼 Φ δ 0 0 0 0 0 :=
      (eqm7_iff_eqm8 𝔼 _ _ _ _ _ _ _).mpr (by rw [smul_zero]; exact zero_isEqm8 𝔼 _ _)
    obtain ⟨q₀, -, huniq⟩ := hdet 0 0 0 (exog_zero 𝔼)
    exact hne ((huniq q hq').trans ((huniq (0, 0) hz).symm.trans rfl))
  · intro hc
    have hΦ : Φ ≠ 0 := by
      rintro rfl
      rw [mul_zero, add_zero, abs_of_pos hδ0] at hc
      linarith
    have h8 := determinate8_of 𝔼 (mul_ne_zero (sub_pos.mpr hδ1).ne' hΦ)
      (by rwa [add_comm] : 1 < |(1 - δ) * Φ + δ|)
    intro r ibar pb₀ hex
    obtain ⟨q, hq, huniq⟩ := h8 r ibar (Φ • pb₀) (exog_smul 𝔼 Φ hex)
    exact ⟨q, (eqm7_iff_eqm8 𝔼 _ _ _ _ _ _ _).mpr hq,
      fun q' hq' => huniq q' ((eqm7_iff_eqm8 𝔼 _ _ _ _ _ _ _).mp hq')⟩

/-- Woodford (2003), **Proposition 2.7**, p. 95: for `0 < δ < 1` and `Φ_π ≥ 0`, rule (2.9) is
determinate if and only if `Φ_π > 1` (the Taylor principle). -/
theorem prop_2_7 [Nonempty Ω] {δ Φ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hΦ : 0 ≤ Φ) :
    Determinate7 𝔼 Φ δ ↔ 1 < Φ := by
  have h1 : 0 < 1 - δ := sub_pos.mpr hδ1
  rw [determinate7_iff 𝔼 hδ0 hδ1, abs_of_nonneg (by nlinarith)]
  constructor
  · intro h
    by_contra h'
    nlinarith
  · intro h
    nlinarith

/-- Woodford (2003), (A.20), p. 640: in an equilibrium under (2.9), smoothed inflation solves
`[δ + (1 − δ)Φ_π] π̄_t = E_t π̄_{t+1} + (1 − δ)(r̂_t − ī_t)`. -/
theorem eq_A_20 {Φ δ : ℝ} {r ibar π i : ℕ → Ω → ℝ} {pb₀ : Ω → ℝ} (hF : Fisher 𝔼 r π i)
    (hR : SmoothedRule Φ δ ibar pb₀ π i) (hsa : 𝔼.Adapted (smoothed δ pb₀ π)) (t : ℕ) :
    (δ + (1 - δ) * Φ) • smoothed δ pb₀ π t =
      𝔼.E t (smoothed δ pb₀ π (t + 1)) + (1 - δ) • (r t - ibar t) := by
  have h1 : 𝔼.E t (smoothed δ pb₀ π (t + 1)) =
      (1 - δ) • 𝔼.E t (π (t + 1)) + δ • smoothed δ pb₀ π t := by
    change 𝔼.E t ((1 - δ) • π (t + 1) + δ • smoothed δ pb₀ π t) = _
    rw [map_add, map_smul, map_smul, hsa t]
  rw [h1]
  funext ω
  have h2 := congrFun (hF t) ω
  have h3 := congrFun (hR t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 h3 ⊢
  linear_combination (1 - δ) * (h2 - h3)

/-- Woodford (2003), eq. (2.10), p. 95 (and (A.18)): in the determinate case
`π̄_t = (1 − δ) ∑_j (δ + (1 − δ)Φ_π)^{−(j+1)} E_t[r̂_{t+j} − ī_{t+j}]`. -/
theorem eq_2_10 {Φ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : 1 < |δ + (1 - δ) * Φ|)
    {r ibar π i : ℕ → Ω → ℝ} {pb₀ : Ω → ℝ} (hex : Exog 𝔼 r ibar pb₀)
    (hq : IsEqm7 𝔼 Φ δ r ibar pb₀ π i) (t : ℕ) (ω : Ω) :
    smoothed δ pb₀ π t ω = (1 - δ) *
      ∑' j, ((δ + (1 - δ) * Φ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω := by
  have hΦ : Φ ≠ 0 := by
    rintro rfl
    rw [mul_zero, add_zero, abs_of_pos hδ0] at hc
    linarith
  have hq8 := (eqm7_iff_eqm8 𝔼 _ _ _ _ _ _ _).mp hq
  have h15 := eq_2_15 𝔼 (by rwa [add_comm] : 1 < |(1 - δ) * Φ + δ|) (exog_smul 𝔼 Φ hex) hq8 t ω
  have hR := congrFun (hq.2.2.2.2.2 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hR
  rw [hR, add_right_inj, add_comm ((1 - δ) * Φ) δ] at h15
  have hs : ∑' j, (1 - δ) * Φ * ((δ + (1 - δ) * Φ)⁻¹) ^ (j + 1) *
      𝔼.E t (r (t + j) - ibar (t + j)) ω = Φ * ((1 - δ) *
      ∑' j, ((δ + (1 - δ) * Φ)⁻¹) ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [hs] at h15
  exact mul_left_cancel₀ hΦ h15

/-- Woodford (2003), p. 96: for `ρ < 1` the two forms of the Taylor principle agree:
`φ_π/(1 − ρ) > 1 ⟺ φ_π + ρ > 1`. -/
theorem taylor_principle_equiv {φ ρ : ℝ} (hρ : ρ < 1) : 1 < φ / (1 - ρ) ↔ 1 < φ + ρ := by
  rw [lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-! ### The infinite-past representation (2.8) -/

/-- Woodford (2003), eq. (2.8), p. 94: the geometric moving average
`S_t = ∑_j δʲ π_{t−j}` of a bounded sequence on `ℤ` satisfies `S_t = π_t + δ S_{t−1}`. -/
theorem geomSeries_rec {δ M : ℝ} (hδ : |δ| < 1) {π : ℤ → ℝ} (hπ : ∀ t, |π t| ≤ M) (t : ℤ) :
    ∑' j : ℕ, δ ^ j * π (t - j) = π t + δ * ∑' j : ℕ, δ ^ j * π (t - 1 - j) := by
  have hsum : Summable (fun j : ℕ => δ ^ j * π (t - j)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg δ) hδ).mul_right M)
      (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hπ _) (pow_nonneg (abs_nonneg δ) j))
  rw [hsum.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
  ring

/-- Woodford (2003), p. 95, and (for `c = φ_π`, `δ = ρ`) p. 96: with an infinite past and
`|δ| < 1`, a bounded `y` satisfies the partial-adjustment law `y_t = δ y_{t−1} + c π_t` if and
only if `y_t = c ∑_j δʲ π_{t−j}` (bounded `π`). -/
theorem partialAdjust_iff_series {δ c Mπ My : ℝ} (hδ : |δ| < 1) {π y : ℤ → ℝ}
    (hπ : ∀ t, |π t| ≤ Mπ) (hy : ∀ t, |y t| ≤ My) :
    (∀ t, y t = δ * y (t - 1) + c * π t) ↔ ∀ t, y t = c * ∑' j : ℕ, δ ^ j * π (t - j) := by
  constructor
  · intro h
    have hS : ∀ t, |∑' j : ℕ, δ ^ j * π (t - j)| ≤ Mπ / (1 - |δ|) := fun t => by
      have hg : HasSum (fun k : ℕ => Mπ * |δ| ^ k) (Mπ / (1 - |δ|)) := by
        have := (hasSum_geometric_of_lt_one (abs_nonneg δ) hδ).mul_left Mπ
        simpa [div_eq_mul_inv] using this
      have := tsum_of_norm_bounded hg (f := fun j : ℕ => δ ^ j * π (t - j)) fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm Mπ]
        exact mul_le_mul_of_nonneg_left (hπ _) (pow_nonneg (abs_nonneg δ) j)
      simpa [Real.norm_eq_abs] using this
    set B := My + |c| * (Mπ / (1 - |δ|)) with hB
    set d : ℤ → ℝ := fun t => y t - c * ∑' j : ℕ, δ ^ j * π (t - j) with hd
    have hdrec : ∀ t, d t = δ * d (t - 1) := fun t => by
      simp only [hd]
      rw [h t, geomSeries_rec hδ hπ t]
      ring
    have hdb : ∀ t, |d t| ≤ B := fun t => by
      simp only [hd, hB]
      refine (abs_sub _ _).trans (add_le_add (hy t) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hS t) (abs_nonneg c)
    have hiter : ∀ (k : ℕ) t, d t = δ ^ k * d (t - k) := by
      intro k
      induction k with
      | zero => intro t; simp
      | succ k ih =>
        intro t
        rw [ih t, hdrec (t - k), show t - ((k + 1 : ℕ) : ℤ) = t - k - 1 by push_cast; ring,
          pow_succ]
        ring
    intro t
    have hle : ∀ k : ℕ, |d t| ≤ |δ| ^ k * B := fun k => by
      rw [hiter k t, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hdb _) (pow_nonneg (abs_nonneg δ) k)
    have hlim : Tendsto (fun k : ℕ => |δ| ^ k * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg δ) hδ).mul_const B
    have h0 : |d t| ≤ 0 := ge_of_tendsto' hlim hle
    have h1 : d t = 0 := abs_nonpos_iff.mp h0
    simp only [hd] at h1
    linarith
  · intro h t
    rw [h t, h (t - 1), geomSeries_rec hδ hπ t]
    ring

/-- Woodford (2003), eq. (2.8) and p. 95: the infinite moving average
`π̄_t = (1 − δ)∑_j δʲ π_{t−j}` satisfies `π̄_t = (1 − δ)π_t + δ π̄_{t−1}`. -/
theorem eq_2_8_recursion {δ M : ℝ} (hδ : |δ| < 1) {π : ℤ → ℝ} (hπ : ∀ t, |π t| ≤ M)
    (t : ℤ) :
    (1 - δ) * ∑' j : ℕ, δ ^ j * π (t - j) =
      (1 - δ) * π t + δ * ((1 - δ) * ∑' j : ℕ, δ ^ j * π (t - 1 - j)) := by
  rw [geomSeries_rec hδ hπ t]
  ring

/-- Woodford (2003), p. 96: with an infinite past and `|ρ| < 1`, a bounded interest-rate gap
follows (2.12), `x_t = ρ x_{t−1} + φ_π π_t`, if and only if it follows (2.9),
`x_t = Φ_π π̄_t` with `Φ_π = φ_π/(1 − ρ)` and `π̄` the moving average (2.8) with `δ = ρ`. -/
theorem rule_iff_smoothed_series {φ ρ Mπ Mx : ℝ} (hρ : |ρ| < 1) {π x : ℤ → ℝ}
    (hπ : ∀ t, |π t| ≤ Mπ) (hx : ∀ t, |x t| ≤ Mx) :
    (∀ t, x t = ρ * x (t - 1) + φ * π t) ↔
      ∀ t, x t = φ / (1 - ρ) * ((1 - ρ) * ∑' j : ℕ, ρ ^ j * π (t - j)) := by
  have h1 : (1 - ρ) ≠ 0 := by
    intro h
    have : ρ = 1 := by linarith
    rw [this, abs_one] at hρ
    exact lt_irrefl _ hρ
  rw [partialAdjust_iff_series hρ hπ hx]
  have he : ∀ S : ℝ, φ / (1 - ρ) * ((1 - ρ) * S) = φ * S := fun S => by field_simp
  simp only [he]

/-! ### Footnote 32 -/

/-- Woodford (2003), fn. 32, p. 99: with `ρ = 1`, (2.12) is the first difference of the
Wicksellian rule (1.34) `î_t = ī_t + φ_p P̂_t`, where `P̂_t − P̂_{t−1} = π_t`. -/
theorem fn32_first_difference {φ : ℝ} {ibar P π i : ℕ → Ω → ℝ} {P₀ : Ω → ℝ}
    (hP : ∀ t, P t - lag P₀ P t = π t) (hW : ∀ t, i t = ibar t + φ • P t) :
    InertialRule φ 1 ibar (φ • P₀) π i := by
  have hx : (fun s => i s - ibar s) = fun s => φ • P s := by
    funext s; rw [hW s, add_sub_cancel_left]
  intro t
  rw [hx, hW t, add_sub_cancel_left, ← hP t, one_smul]
  funext ω
  cases t <;> simp only [lag, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;> ring

/-! ### AR(1) natural rate of interest (p. 97) -/

/-- Woodford (2003), p. 97 and §A.9, p. 642: with `ī = 0` and an AR(1) natural rate
(`E_t r̂_{t+1} = ρ_r r̂_t`, `|ρ_r| < 1`), in the determinate case the interest rate is
`î_t = φ_π/(φ_π + ρ − ρ_r) · r̂_t`, perfectly correlated with the natural rate. -/
theorem ar1_interest {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hc : 1 < |φ + ρ|) {r π i : ℕ → Ω → ℝ}
    {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r) (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i)
    (t : ℕ) : i t = (φ / (φ + ρ - ρr)) • r t := by
  obtain ⟨-, ⟨Mi, hMi⟩, -, hia, hF, hR⟩ := hq
  obtain ⟨Mr, hMr⟩ := hrb
  have hne : φ + ρ ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have hD : φ + ρ - ρr ≠ 0 := by
    intro h
    have h' : φ + ρ = ρr := by linarith
    rw [h'] at hc
    linarith
  have ha : |(φ + ρ)⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  have h0a : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
  have hx := gap_forward 𝔼 hne hia h0a hF hR
  simp only [Pi.zero_apply, sub_zero] at hx
  have hk : ∀ t, (φ / (φ + ρ - ρr)) • r t = (φ + ρ)⁻¹ • 𝔼.E t ((φ / (φ + ρ - ρr)) • r (t + 1)) +
      ((φ + ρ)⁻¹ * φ) • r t := by
    intro t
    rw [map_smul, hr.2 t, smul_smul, smul_smul, ← add_smul]
    congr 1
    field_simp
    ring
  have := 𝔼.forward_unique ha hx hk ⟨Mi, hMi⟩ ⟨|φ / (φ + ρ - ρr)| * Mr, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMr t ω) (abs_nonneg _)⟩
  exact congrFun this t

/-- Woodford (2003), p. 97 and §A.9, p. 642: in the AR(1) case inflation is
`π_{t+1} = (φ_π + ρ − ρ_r)⁻¹(r̂_{t+1} − ρ r̂_t)` (inverting (2.12)). -/
theorem ar1_inflation {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) (t : ℕ) :
    π (t + 1) = (φ + ρ - ρr)⁻¹ • (r (t + 1) - ρ • r t) := by
  have hD : φ + ρ - ρr ≠ 0 := by
    intro h
    have h' : φ + ρ = ρr := by linarith
    rw [h'] at hc
    linarith
  have hi := ar1_interest 𝔼 hρr hc hr hrb hq
  rw [infl_eq hφ hq.2.2.2.2.2 (t + 1)]
  change φ⁻¹ • ((i (t + 1) - (0 : ℕ → Ω → ℝ) (t + 1)) - ρ • (i t - (0 : ℕ → Ω → ℝ) t)) = _
  simp only [Pi.zero_apply, sub_zero, hi]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp

/-- Woodford (2003), p. 97: in the AR(1) case inflation at date `0` is
`π_0 = φ_π⁻¹(φ_π/(φ_π + ρ − ρ_r) r̂_0 − ρ x₀)`, where `x₀ = î_{−1} − ī_{−1}`. -/
theorem ar1_inflation_zero {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) :
    π 0 = φ⁻¹ • ((φ / (φ + ρ - ρr)) • r 0 - ρ • x₀) := by
  rw [infl_eq hφ hq.2.2.2.2.2 0]
  change φ⁻¹ • ((i 0 - (0 : ℕ → Ω → ℝ) 0) - ρ • x₀) = _
  rw [Pi.zero_apply, sub_zero, ar1_interest 𝔼 hρr hc hr hrb hq 0]

/-- Woodford (2003), p. 97: in the AR(1) case expected inflation is
`E_t π_{t+1} = (ρ_r − ρ)/(φ_π + ρ − ρ_r) · r̂_t`. -/
theorem ar1_expected_inflation {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) (t : ℕ) :
    𝔼.E t (π (t + 1)) = ((ρr - ρ) / (φ + ρ - ρr)) • r t := by
  rw [ar1_inflation 𝔼 hρr hφ hc hr hrb hq t, map_smul, map_sub, map_smul, hr.2 t, hr.1 t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 97: the innovation `ε_t = r̂_t − ρ_r r̂_{t−1}` of the natural rate
(with `r̂_{−1} = 0`, so `ε_0 = r̂_0`). -/
def innov (ρr : ℝ) (r : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => r 0
  | t + 1 => r (t + 1) - ρr • r t

/-- Woodford (2003), p. 97: the innovation is unforecastable, `E_t ε_{t+1} = 0`. -/
theorem innov_unforecastable {ρr : ℝ} {r : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (t : ℕ) :
    𝔼.E t (innov ρr r (t + 1)) = 0 := by
  change 𝔼.E t (r (t + 1) - ρr • r t) = 0
  rw [map_sub, map_smul, hr.2 t, hr.1 t, sub_self]

/-- Woodford (2003), p. 97: "the effect of an innovation in the real rate at date `t` upon
`E_t π_{t+1}` is `(ρ_r − ρ)` times its effect upon `π_t`": given `r̂_t`, the date-`(t+1)`
innovation `ε` loads on `π_{t+1}` with `D⁻¹` and on `E_{t+1}π_{t+2}` with `(ρ_r − ρ)D⁻¹`,
`D = φ_π + ρ − ρ_r`. -/
theorem ar1_innovation_loadings {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0)
    (hc : 1 < |φ + ρ|) {r π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r)
    (hrb : BoundedProc r) (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) (t : ℕ) :
    π (t + 1) = (φ + ρ - ρr)⁻¹ • innov ρr r (t + 1) + ((ρr - ρ) / (φ + ρ - ρr)) • r t ∧
      𝔼.E (t + 1) (π (t + 1 + 1)) = ((ρr - ρ) / (φ + ρ - ρr)) • innov ρr r (t + 1) +
        ((ρr - ρ) / (φ + ρ - ρr) * ρr) • r t := by
  constructor
  · rw [ar1_inflation 𝔼 hρr hφ hc hr hrb hq t]
    funext ω
    simp only [innov, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rw [ar1_expected_inflation 𝔼 hρr hφ hc hr hrb hq (t + 1)]
    funext ω
    simp only [innov, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Woodford (2003), p. 97: impulse response of the natural rate, `ρ_rʲ`. -/
def irfR (ρr : ℝ) (j : ℕ) : ℝ := ρr ^ j

/-- Woodford (2003), p. 97 and Fig. 2.1(a): impulse response of the interest rate,
`φ_π/(φ_π + ρ − ρ_r) · ρ_rʲ`. -/
noncomputable def irfI (φ ρ ρr : ℝ) (j : ℕ) : ℝ := φ / (φ + ρ - ρr) * ρr ^ j

/-- Woodford (2003), p. 97 and Fig. 2.1(b): impulse response of inflation, `D⁻¹` on impact and
`(ρ_r − ρ)D⁻¹ρ_r^{j}` at horizon `j + 1`, `D = φ_π + ρ − ρ_r`. -/
noncomputable def irfPi (φ ρ ρr : ℝ) : ℕ → ℝ
  | 0 => (φ + ρ - ρr)⁻¹
  | j + 1 => (ρr - ρ) / (φ + ρ - ρr) * ρr ^ j

/-- Woodford (2003), p. 97: the AR(1) natural rate is the moving average of its innovations,
`r̂_t = ∑_{s ≤ t} ρ_r^{t−s} ε_s`. -/
theorem ma_rep_r (ρr : ℝ) (r : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    r t ω = ∑ s ∈ Finset.range (t + 1), irfR ρr (t - s) * innov ρr r s ω := by
  induction t with
  | zero => simp [innov, irfR]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hs : ∑ s ∈ Finset.range (t + 1), irfR ρr (t + 1 - s) * innov ρr r s ω =
        ρr * r t ω := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [show t + 1 - s = (t - s) + 1 by omega]
      simp only [irfR, pow_succ]
      ring
    rw [hs, Nat.sub_self]
    simp only [innov, irfR, pow_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Woodford (2003), p. 97 and Fig. 2.1(a): in the AR(1) equilibrium the interest rate is
`î_t = ∑_{s ≤ t} irfI(t − s) ε_s`. -/
theorem ma_rep_i {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hc : 1 < |φ + ρ|) {r π i : ℕ → Ω → ℝ}
    {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r) (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i)
    (t : ℕ) (ω : Ω) :
    i t ω = ∑ s ∈ Finset.range (t + 1), irfI φ ρ ρr (t - s) * innov ρr r s ω := by
  rw [ar1_interest 𝔼 hρr hc hr hrb hq t, Pi.smul_apply, smul_eq_mul, ma_rep_r ρr r t ω,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [irfI, irfR]
  ring

/-- Woodford (2003), p. 97 and Fig. 2.1(b): starting from the steady state (`x₀ = 0`), the AR(1)
equilibrium inflation rate is `π_t = ∑_{s ≤ t} irfPi(t − s) ε_s`: `irfPi` is the impulse
response of inflation to a natural-rate innovation. -/
theorem ma_rep_pi {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 0 π i) (t : ℕ) (ω : Ω) :
    π t ω = ∑ s ∈ Finset.range (t + 1), irfPi φ ρ ρr (t - s) * innov ρr r s ω := by
  have hD : φ + ρ - ρr ≠ 0 := by
    intro h
    have h' : φ + ρ = ρr := by linarith
    rw [h'] at hc
    linarith
  cases t with
  | zero =>
    rw [ar1_inflation_zero 𝔼 hρr hφ hc hr hrb hq]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self, irfPi, innov,
      Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    ring
  | succ t =>
    rw [ar1_inflation 𝔼 hρr hφ hc hr hrb hq t, Finset.sum_range_succ]
    have hs : ∑ s ∈ Finset.range (t + 1), irfPi φ ρ ρr (t + 1 - s) * innov ρr r s ω =
        (ρr - ρ) / (φ + ρ - ρr) * r t ω := by
      rw [ma_rep_r ρr r t ω, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [show t + 1 - s = (t - s) + 1 by omega]
      simp only [irfPi, irfR]
      ring
    rw [hs, Nat.sub_self]
    simp only [irfPi, innov, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Woodford (2003), p. 97 (stationary equilibrium, infinite past): if
`r̂_t = ∑_j ρ_rʲ ε_{t−j}` and `π_t = D⁻¹(r̂_t − ρ r̂_{t−1})` (`ar1_inflation`), then
`π_t = ∑_j irfPi(j) ε_{t−j}`: `irfPi` is the MA(∞) coefficient sequence of inflation. -/
theorem stationary_ma_pi {φ ρ ρr M : ℝ} (hρr : |ρr| < 1) {ε : ℤ → ℝ} (hε : ∀ t, |ε t| ≤ M)
    (t : ℤ) :
    (φ + ρ - ρr)⁻¹ * (∑' j : ℕ, ρr ^ j * ε (t - j) - ρ * ∑' j : ℕ, ρr ^ j * ε (t - 1 - j)) =
      ∑' j : ℕ, irfPi φ ρ ρr j * ε (t - j) := by
  have hs1 : Summable (fun j : ℕ => ρr ^ j * ε (t - 1 - j)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg ρr) hρr).mul_right M)
      (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hε _) (pow_nonneg (abs_nonneg ρr) j))
  have hsh : ∀ j : ℕ, irfPi φ ρ ρr (j + 1) * ε (t - ((j + 1 : ℕ) : ℤ)) =
      (ρr - ρ) / (φ + ρ - ρr) * (ρr ^ j * ε (t - 1 - j)) := fun j => by
    rw [show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
    simp only [irfPi]
    ring
  have hsum : Summable (fun j : ℕ => irfPi φ ρ ρr j * ε (t - j)) := by
    rw [← summable_nat_add_iff 1]
    exact (hs1.mul_left ((ρr - ρ) / (φ + ρ - ρr))).congr fun j => (hsh j).symm
  rw [hsum.tsum_eq_zero_add, geomSeries_rec hρr hε t, tsum_congr hsh, tsum_mul_left]
  simp only [irfPi, Nat.cast_zero, sub_zero]
  ring

/-- Woodford (2003), p. 97 (stationary equilibrium): `î_t = φ_π/D · r̂_t = ∑_j irfI(j) ε_{t−j}`. -/
theorem stationary_ma_i (φ ρ ρr : ℝ) (ε : ℤ → ℝ) (t : ℤ) :
    φ / (φ + ρ - ρr) * ∑' j : ℕ, ρr ^ j * ε (t - j) = ∑' j : ℕ, irfI φ ρ ρr j * ε (t - j) := by
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by simp only [irfI]; ring

/-- Woodford (2003), p. 97: the first-period persistence of inflation is `ρ_r − ρ`:
`irfPi(1) = (ρ_r − ρ) irfPi(0)`, against `ρ_r` for the natural rate. -/
theorem irfPi_one (φ ρ ρr : ℝ) : irfPi φ ρ ρr 1 = (ρr - ρ) * irfPi φ ρ ρr 0 := by
  simp only [irfPi, pow_zero, mul_one]
  ring

/-- Woodford (2003), p. 97: after the first period inflation responses decay at rate `ρ_r`. -/
theorem irfPi_succ_succ (φ ρ ρr : ℝ) (j : ℕ) :
    irfPi φ ρ ρr (j + 2) = ρr * irfPi φ ρ ρr (j + 1) := by
  simp only [irfPi, pow_succ]
  ring

/-- Woodford (2003), p. 97: "If `ρ = ρ_r`, the inflation fluctuations become purely
transitory." -/
theorem irfPi_transitory {φ ρ ρr : ℝ} (h : ρ = ρr) (j : ℕ) : irfPi φ ρ ρr (j + 1) = 0 := by
  simp [irfPi, h]

/-- Woodford (2003), p. 97: "for larger values of `ρ`, they actually become antipersistent":
with `D = φ_π + ρ − ρ_r > 0` and `ρ > ρ_r`, the response one period after the shock has the
opposite sign to the impact response. -/
theorem irfPi_antipersistent {φ ρ ρr : ℝ} (hD : 0 < φ + ρ - ρr) (h : ρr < ρ) :
    0 < irfPi φ ρ ρr 0 ∧ irfPi φ ρ ρr 1 < 0 := by
  refine ⟨by simp only [irfPi]; positivity, ?_⟩
  simp only [irfPi, pow_zero, mul_one]
  exact div_neg_of_neg_of_pos (by linarith) hD

/-- Woodford (2003), p. 97: inflation is less persistent than the natural rate (`ρ > 0`):
`irfPi(1) < ρ_r irfPi(0)`, while `irfR(1) = ρ_r irfR(0)`. -/
theorem irfPi_less_persistent {φ ρ ρr : ℝ} (hD : 0 < φ + ρ - ρr) (hρ : 0 < ρ) :
    irfPi φ ρ ρr 1 < ρr * irfPi φ ρ ρr 0 := by
  rw [irfPi_one]
  have : 0 < irfPi φ ρ ρr 0 := by simp only [irfPi]; positivity
  nlinarith

/-- Woodford (2003), p. 97: for `φ_π > 0` and `D > 0` the interest rate moves in the same
direction as the natural rate. -/
theorem irfI_pos {φ ρ ρr : ℝ} (hφ : 0 < φ) (hD : 0 < φ + ρ - ρr) (hρr : 0 < ρr) (j : ℕ) :
    0 < irfI φ ρ ρr j := by
  simp only [irfI]
  positivity

/-! ### The Beveridge–Nelson trend (2.16) -/

/-- Woodford (2003), (2.16) and p. 99: the innovation in the long-run price level,
`∑_j (E_t π_{t+j} − E_{t−1} π_{t+j})`, equals `(1 − ρ)(1 − ρ_r)⁻¹(φ_π + ρ − ρ_r)⁻¹ ε_t`
(here at date `t = s + 1`, as a genuine convergent series). -/
theorem bn_innovation {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) (s : ℕ) (ω : Ω) :
    HasSum (fun j => 𝔼.E (s + 1) (π (s + 1 + j)) ω - 𝔼.E s (π (s + 1 + j)) ω)
      ((1 - ρ) / ((1 - ρr) * (φ + ρ - ρr)) * innov ρr r (s + 1) ω) := by
  have hD : φ + ρ - ρr ≠ 0 := by
    intro h
    have h' : φ + ρ = ρr := by linarith
    rw [h'] at hc
    linarith
  have hρr1 : 1 - ρr ≠ 0 := by
    have := (abs_lt.mp hρr).2
    linarith
  have hπ := ar1_inflation 𝔼 hρr hφ hc hr hrb hq
  have hE : ∀ t k, 𝔼.E t (r (t + k)) ω = ρr ^ k * r t ω := fun t k => by
    rw [𝔼.ar1_iterate hr t k]
    rfl
  have a1 : ∀ n : ℕ, 𝔼.E (s + 1) (π (s + 1 + (n + 1))) ω =
      (φ + ρ - ρr)⁻¹ * (ρr ^ (n + 1) * r (s + 1) ω - ρ * (ρr ^ n * r (s + 1) ω)) := by
    intro n
    have h := hπ (s + 1 + n)
    rw [show s + 1 + n + 1 = s + 1 + (n + 1) by omega] at h
    rw [h, map_smul, map_sub, map_smul, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hE (s + 1) (n + 1), hE (s + 1) n]
  have a2 : ∀ n : ℕ, 𝔼.E s (π (s + 1 + (n + 1))) ω =
      (φ + ρ - ρr)⁻¹ * (ρr ^ (n + 2) * r s ω - ρ * (ρr ^ (n + 1) * r s ω)) := by
    intro n
    have h := hπ (s + 1 + n)
    rw [show s + 1 + n + 1 = s + (n + 2) by omega, show s + 1 + n = s + (n + 1) by omega] at h
    rw [show s + 1 + (n + 1) = s + (n + 2) by omega, h, map_smul, map_sub, map_smul,
      Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hE s (n + 2),
      hE s (n + 1)]
  have a3 : 𝔼.E (s + 1) (π (s + 1 + 0)) ω = (φ + ρ - ρr)⁻¹ * (r (s + 1) ω - ρ * r s ω) := by
    rw [add_zero, hq.2.2.1 (s + 1), hπ s]
    rfl
  have a4 : 𝔼.E s (π (s + 1 + 0)) ω = (φ + ρ - ρr)⁻¹ * (ρr * r s ω - ρ * r s ω) := by
    rw [add_zero, hπ s, map_smul, map_sub, map_smul, hr.2 s, hr.1 s]
    rfl
  have key : HasSum (fun n : ℕ => 𝔼.E (s + 1) (π (s + 1 + (n + 1))) ω -
      𝔼.E s (π (s + 1 + (n + 1))) ω)
      ((ρr - ρ) / (φ + ρ - ρr) * innov ρr r (s + 1) ω * (1 - ρr)⁻¹) := by
    convert (hasSum_geometric_of_abs_lt_one hρr).mul_left
      ((ρr - ρ) / (φ + ρ - ρr) * innov ρr r (s + 1) ω) using 1
    funext n
    rw [a1 n, a2 n]
    simp only [innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hT : (1 - ρ) / ((1 - ρr) * (φ + ρ - ρr)) * innov ρr r (s + 1) ω =
      (ρr - ρ) / (φ + ρ - ρr) * innov ρr r (s + 1) ω * (1 - ρr)⁻¹ +
        (𝔼.E (s + 1) (π (s + 1 + 0)) ω - 𝔼.E s (π (s + 1 + 0)) ω) := by
    rw [a3, a4]
    simp only [innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Finset.sum_range_one]
  rw [hT, add_sub_cancel_right]
  exact key

/-- Woodford (2003), (2.16), p. 99: with `log P_{t+1} = log P_t + π_{t+1}` (and mean inflation
zero), the revision `E_t log P_{t+j} − E_{t−1} log P_{t+j}` of the long-run price-level
forecast converges, as `j → ∞`, to the Beveridge–Nelson innovation
`(1 − ρ)(1 − ρ_r)⁻¹(φ_π + ρ − ρ_r)⁻¹ ε_t` (here `t = s + 1`). -/
theorem bn_limit {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hc : 1 < |φ + ρ|)
    {r π i logP : ℕ → Ω → ℝ} {x₀ : Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (hrb : BoundedProc r)
    (hq : IsEqm8 𝔼 φ ρ r 0 x₀ π i) (hPa : 𝔼.Adapted logP)
    (hP : ∀ t, logP (t + 1) = logP t + π (t + 1)) (s : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E (s + 1) (logP (s + 1 + j)) ω - 𝔼.E s (logP (s + 1 + j)) ω) atTop
      (𝓝 ((1 - ρ) / ((1 - ρr) * (φ + ρ - ρr)) * innov ρr r (s + 1) ω)) := by
  have hsum := bn_innovation 𝔼 hρr hφ hc hr hrb hq s ω
  have h1 : 𝔼.E (s + 1) (logP s) = logP s := by
    calc _ = 𝔼.E (s + 1) (𝔼.E s (logP s)) := by rw [hPa s]
      _ = 𝔼.E s (logP s) := 𝔼.known (Nat.le_succ s) _
      _ = logP s := hPa s
  have hpart : ∀ j, 𝔼.E (s + 1) (logP (s + 1 + j)) ω - 𝔼.E s (logP (s + 1 + j)) ω =
      ∑ k ∈ Finset.range (j + 1), (𝔼.E (s + 1) (π (s + 1 + k)) ω - 𝔼.E s (π (s + 1 + k)) ω) := by
    intro j
    induction j with
    | zero =>
      simp only [add_zero, zero_add, Finset.sum_range_one]
      rw [hP s, map_add, map_add]
      simp only [Pi.add_apply, h1, hPa s]
      ring
    | succ j ih =>
      rw [Finset.sum_range_succ, ← ih, show s + 1 + (j + 1) = s + 1 + j + 1 by omega,
        hP (s + 1 + j), map_add, map_add]
      simp only [Pi.add_apply]
      ring
  exact Tendsto.congr (fun j => (hpart j).symm)
    (hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))

/-- Woodford (2003), p. 99: the Beveridge–Nelson innovation coefficient vanishes if and only if
`ρ = 1` (then the long-run price level is deterministic). -/
theorem bn_coeff_eq_zero_iff {φ ρ ρr : ℝ} (hρr : ρr ≠ 1) (hD : φ + ρ - ρr ≠ 0) :
    (1 - ρ) / ((1 - ρr) * (φ + ρ - ρr)) = 0 ↔ ρ = 1 := by
  have h1 : (1 - ρr) * (φ + ρ - ρr) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hρr.symm) hD
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h h1
  · intro h; left; linarith

/-! ### Variances as sums of squared impulse responses -/

/-- Woodford (2003), §A.9, p. 642: the unconditional variance of a stationary process with
impulse responses `ψ` per unit innovation variance, `var = ∑_j ψ_j²`. -/
noncomputable def msq (ψ : ℕ → ℝ) : ℝ := ∑' j, ψ j ^ 2

/-- Woodford (2003), §A.9, p. 642: the first-order autocovariance `cov(x_t, x_{t−1}) =
∑_j ψ_{j+1} ψ_j` per unit innovation variance. -/
noncomputable def acov1 (ψ : ℕ → ℝ) : ℝ := ∑' j, ψ (j + 1) * ψ j

/-- Woodford (2003), §A.9: `∑_j (ρ_rʲ)² = (1 − ρ_r²)⁻¹`. -/
theorem hasSum_irfR_sq {ρr : ℝ} (hρr : |ρr| < 1) :
    HasSum (fun j => irfR ρr j ^ 2) (1 - ρr ^ 2)⁻¹ := by
  have h : |ρr ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) hρr two_ne_zero
  convert hasSum_geometric_of_abs_lt_one h using 1
  funext j
  simp only [irfR]
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- Woodford (2003), §A.9, p. 642: `var(r̂) = (1 − ρ_r²)⁻¹` (per unit innovation variance). -/
theorem msq_irfR {ρr : ℝ} (hρr : |ρr| < 1) : msq (irfR ρr) = (1 - ρr ^ 2)⁻¹ :=
  (hasSum_irfR_sq hρr).tsum_eq

/-- Woodford (2003), (A.23), p. 642: `var(î) = (φ_π/(φ_π + ρ − ρ_r))² var(r̂)`. -/
theorem msq_irfI {ρr : ℝ} (hρr : |ρr| < 1) (φ ρ : ℝ) :
    msq (irfI φ ρ ρr) = (φ / (φ + ρ - ρr)) ^ 2 * msq (irfR ρr) := by
  rw [msq_irfR hρr]
  refine HasSum.tsum_eq ?_
  convert (hasSum_irfR_sq hρr).mul_left ((φ / (φ + ρ - ρr)) ^ 2) using 1
  funext j
  simp only [irfI, irfR]
  ring

/-- Woodford (2003), (A.23), p. 642: `cov(î_t, î_{t−1}) = ρ_r var(î)`. -/
theorem acov1_irfI {ρr : ℝ} (hρr : |ρr| < 1) (φ ρ : ℝ) :
    acov1 (irfI φ ρ ρr) = ρr * msq (irfI φ ρ ρr) := by
  rw [msq_irfI hρr, msq_irfR hρr]
  refine HasSum.tsum_eq ?_
  convert (hasSum_irfR_sq hρr).mul_left (ρr * (φ / (φ + ρ - ρr)) ^ 2) using 1
  · funext j
    simp only [irfI, irfR]
    ring
  · ring

/-- Woodford (2003), (A.24), p. 642: `var(π) = (1 − 2ρ_rρ + ρ²)/(φ_π + ρ − ρ_r)² · var(r̂)`. -/
theorem msq_irfPi {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hD : φ + ρ - ρr ≠ 0) :
    msq (irfPi φ ρ ρr) = (1 - 2 * ρr * ρ + ρ ^ 2) / (φ + ρ - ρr) ^ 2 * msq (irfR ρr) := by
  have hr2 : 1 - ρr ^ 2 ≠ 0 := by
    have : ρr ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρr).mpr hρr
    linarith
  have h1 : HasSum (fun n => irfPi φ ρ ρr (n + 1) ^ 2)
      (((ρr - ρ) / (φ + ρ - ρr)) ^ 2 * (1 - ρr ^ 2)⁻¹) := by
    convert (hasSum_irfR_sq hρr).mul_left (((ρr - ρ) / (φ + ρ - ρr)) ^ 2) using 1
    funext n
    simp only [irfPi, irfR]
    ring
  have h2 : HasSum (fun j => irfPi φ ρ ρr j ^ 2)
      (((ρr - ρ) / (φ + ρ - ρr)) ^ 2 * (1 - ρr ^ 2)⁻¹ + irfPi φ ρ ρr 0 ^ 2) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [Finset.sum_range_one, add_sub_cancel_right]
    exact h1
  rw [msq, h2.tsum_eq, msq_irfR hρr]
  simp only [irfPi]
  field_simp
  ring

/-- Woodford (2003), §A.9, p. 642: inverting (2.12) at the level of impulse responses,
`φ_π irfPi(0) = irfI(0)` and `φ_π irfPi(j+1) = irfI(j+1) − ρ irfI(j)`. -/
theorem irfPi_from_irfI {φ ρ ρr : ℝ} (hφ : φ ≠ 0) (hD : φ + ρ - ρr ≠ 0) :
    φ * irfPi φ ρ ρr 0 = irfI φ ρ ρr 0 ∧
      ∀ j, φ * irfPi φ ρ ρr (j + 1) = irfI φ ρ ρr (j + 1) - ρ * irfI φ ρ ρr j := by
  refine ⟨by simp only [irfPi, irfI, pow_zero, mul_one]; field_simp, fun j => ?_⟩
  simp only [irfPi, irfI, pow_succ]
  field_simp

/-- Woodford (2003), (A.24), p. 642, the book's route:
`var(π) = φ_π⁻²[(1 + ρ²)var(î) − 2ρ cov(î_t, î_{t−1})]`. -/
theorem var_pi_book_route {φ ρ ρr : ℝ} (hρr : |ρr| < 1) (hφ : φ ≠ 0) (hD : φ + ρ - ρr ≠ 0) :
    msq (irfPi φ ρ ρr) =
      φ⁻¹ ^ 2 * ((1 + ρ ^ 2) * msq (irfI φ ρ ρr) - 2 * ρ * acov1 (irfI φ ρ ρr)) := by
  rw [msq_irfPi hρr hD, acov1_irfI hρr, msq_irfI hρr]
  field_simp
  ring

/-! ### Proposition 2.9, corrected (error E2) -/

/-- Woodford (2003), §A.9, p. 643: `1 − 2ρ_rρ + ρ² = (1 − ρ_r²) + (ρ − ρ_r)²`. -/
theorem Q_eq (ρr ρ : ℝ) : 1 - 2 * ρr * ρ + ρ ^ 2 = (1 - ρr ^ 2) + (ρ - ρr) ^ 2 := by ring

/-- Woodford (2003), §A.9, p. 643: `(ρ − ρ_r)² < 1 − 2ρ_rρ + ρ²` for `|ρ_r| < 1`. -/
theorem sq_lt_Q {ρr : ℝ} (hρr : |ρr| < 1) (ρ : ℝ) : (ρ - ρr) ^ 2 < 1 - 2 * ρr * ρ + ρ ^ 2 := by
  have : ρr ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρr).mpr hρr
  rw [Q_eq]
  linarith

/-- Woodford (2003), §A.9: the natural-rate variance is positive. -/
theorem msq_irfR_pos {ρr : ℝ} (hρr : |ρr| < 1) : 0 < msq (irfR ρr) := by
  rw [msq_irfR hρr]
  have : ρr ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρr).mpr hρr
  exact inv_pos.mpr (by linarith)

/-- Woodford (2003), §A.9, p. 642, solving (A.24): on the branch `φ_π + ρ − ρ_r > 0`, the rule
achieves `var(π) = V_π > 0` if and only if `φ_π = √((1 − 2ρ_rρ + ρ²) var(r̂)/V_π) + ρ_r − ρ`. -/
theorem achieve_iff {φ ρ ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ) (hD : 0 < φ + ρ - ρr) :
    msq (irfPi φ ρ ρr) = Vπ ↔
      φ = √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) + ρr - ρ := by
  rw [msq_irfPi hρr hD.ne']
  have hVr := msq_irfR_pos hρr
  have hQ : 0 < 1 - 2 * ρr * ρ + ρ ^ 2 := lt_of_le_of_lt (sq_nonneg _) (sq_lt_Q hρr ρ)
  have hQ' := hQ.ne'
  have hVr' := hVr.ne'
  have hD' := hD.ne'
  have hVπ' := hVπ.ne'
  constructor
  · intro h
    have hD2 : (φ + ρ - ρr) ^ 2 = (1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ := by
      rw [eq_div_iff hVπ', ← h]
      field_simp
    have : √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) = φ + ρ - ρr := by
      rw [← hD2]
      exact Real.sqrt_sq hD.le
    linarith
  · intro h
    have hs : φ + ρ - ρr = √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) := by linarith
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp

/-- Woodford (2003), §A.9, p. 642: any rule satisfying (2.13) (`φ_π + ρ > 1`) that achieves
`var(π) = V_π` is the positive-root solution of (A.24). -/
theorem prop_2_9_unique {φ ρ ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ) (h1 : 1 < φ + ρ)
    (hach : msq (irfPi φ ρ ρr) = Vπ) :
    φ = √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) + ρr - ρ := by
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  exact (achieve_iff hρr hVπ (by linarith)).mp hach

/-- Woodford (2003), Prop. 2.9, p. 98, first claim, **corrected** (E2): if
`0 < V_π ≤ var(r̂)`, then for every `ρ ≥ 1` the rule with
`φ_π = √((1 − 2ρ_rρ + ρ²) var(r̂)/V_π) + ρ_r − ρ` has `φ_π > 0`, satisfies (2.13) and achieves
`var(π) = V_π`. -/
theorem prop_2_9_exists {ρ ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ)
    (hle : Vπ ≤ msq (irfR ρr)) (hρ : 1 ≤ ρ) :
    let φ := √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) + ρr - ρ
    0 < φ ∧ 1 < φ + ρ ∧ msq (irfPi φ ρ ρr) = Vπ := by
  intro φ
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  have hQ : 0 < 1 - 2 * ρr * ρ + ρ ^ 2 := lt_of_le_of_lt (sq_nonneg _) (sq_lt_Q hρr ρ)
  have hge : √(1 - 2 * ρr * ρ + ρ ^ 2) ≤
      √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) := by
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hVπ]
    exact mul_le_mul_of_nonneg_left hle hQ.le
  have habs : |ρ - ρr| < √(1 - 2 * ρr * ρ + ρ ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    exact sq_lt_Q hρr ρ
  have hlt : ρ - ρr < √((1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) / Vπ) :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le habs hge)
  have hφ0 : 0 < φ := by simp only [φ]; linarith
  have hφ1 : 1 < φ + ρ := by simp only [φ]; linarith
  refine ⟨hφ0, hφ1, (achieve_iff hρr hVπ (by linarith)).mpr rfl⟩

/-- Woodford (2003), (A.25), p. 643, **corrected**: on the branch `φ_π + ρ − ρ_r > 0`, a rule
achieving `var(π) = V_π` has
`var(î) = (σ(r̂) − h(ρ)σ(π))²`, `h(ρ) = (ρ − ρ_r)/(1 − 2ρ_rρ + ρ²)^{1/2}`; the book's (A.25)
`σ(î) = σ(r̂) − h(ρ)σ(π)` holds only when the right side is nonnegative (`sigma_i_formula`). -/
theorem msq_irfI_eq_sq {φ ρ ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ) (hD : 0 < φ + ρ - ρr)
    (hach : msq (irfPi φ ρ ρr) = Vπ) :
    msq (irfI φ ρ ρr) =
      (√(msq (irfR ρr)) - (ρ - ρr) / √(1 - 2 * ρr * ρ + ρ ^ 2) * √Vπ) ^ 2 := by
  have hφ := (achieve_iff hρr hVπ hD).mp hach
  have hVr := msq_irfR_pos hρr
  have hQ : 0 < 1 - 2 * ρr * ρ + ρ ^ 2 := lt_of_le_of_lt (sq_nonneg _) (sq_lt_Q hρr ρ)
  have hsQ : 0 < √(1 - 2 * ρr * ρ + ρ ^ 2) := Real.sqrt_pos.mpr hQ
  have hsV : 0 < √(msq (irfR ρr)) := Real.sqrt_pos.mpr hVr
  have hsP : 0 < √Vπ := Real.sqrt_pos.mpr hVπ
  have hsQ' := hsQ.ne'
  have hsV' := hsV.ne'
  have hsP' := hsP.ne'
  have hDs : φ + ρ - ρr = √(1 - 2 * ρr * ρ + ρ ^ 2) * √(msq (irfR ρr)) / √Vπ := by
    rw [← Real.sqrt_mul hQ.le, ← Real.sqrt_div (by positivity)]
    linarith
  have hφ' : φ = √(1 - 2 * ρr * ρ + ρ ^ 2) * √(msq (irfR ρr)) / √Vπ - (ρ - ρr) := by
    linarith
  have key : φ / (φ + ρ - ρr) * √(msq (irfR ρr)) =
      √(msq (irfR ρr)) - (ρ - ρr) / √(1 - 2 * ρr * ρ + ρ ^ 2) * √Vπ := by
    rw [hDs, hφ']
    field_simp
  rw [msq_irfI hρr, ← key, mul_pow, Real.sq_sqrt hVr.le]

/-- Woodford (2003), (A.25), p. 643, corrected with the absolute value:
`σ(î) = |σ(r̂) − h(ρ)σ(π)|`. -/
theorem sigma_i_formula {φ ρ ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ) (hD : 0 < φ + ρ - ρr)
    (hach : msq (irfPi φ ρ ρr) = Vπ) :
    √(msq (irfI φ ρ ρr)) =
      |√(msq (irfR ρr)) - (ρ - ρr) / √(1 - 2 * ρr * ρ + ρ ^ 2) * √Vπ| := by
  rw [msq_irfI_eq_sq hρr hVπ hD hach, Real.sqrt_sq_eq_abs]

/-- Woodford (2003), §A.9, p. 643: `u ↦ u/(c + u²)^{1/2}` is strictly increasing for `c > 0`
(so `h(ρ) = (ρ − ρ_r)/[(1 − ρ_r²) + (ρ − ρ_r)²]^{1/2}` increases with `ρ`). -/
theorem hfun_strictMono {c : ℝ} (hc : 0 < c) : StrictMono (fun u : ℝ => u / √(c + u ^ 2)) := by
  have hpos : ∀ u : ℝ, 0 < √(c + u ^ 2) := fun u => Real.sqrt_pos.mpr (by positivity)
  have hnn : ∀ u v : ℝ, 0 ≤ u → u < v → u / √(c + u ^ 2) < v / √(c + v ^ 2) := by
    intro u v hu huv
    rw [div_lt_div_iff₀ (hpos u) (hpos v)]
    have huv2 : u ^ 2 < v ^ 2 := by nlinarith
    have h1 : (u * √(c + v ^ 2)) ^ 2 < (v * √(c + u ^ 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left huv2 hc]
    exact lt_of_pow_lt_pow_left₀ 2 (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) h1
  intro u v huv
  simp only
  rcases le_or_gt 0 u with hu | hu
  · exact hnn u v hu huv
  · rcases le_or_gt v 0 with hv | hv
    · have h := hnn (-v) (-u) (by linarith) (by linarith)
      simp only [neg_sq, neg_div] at h
      linarith
    · have h1 : u / √(c + u ^ 2) < 0 := div_neg_of_neg_of_pos hu (hpos u)
      have h2 : 0 < v / √(c + v ^ 2) := div_pos hv (hpos v)
      linarith

/-- Woodford (2003), Prop. 2.9, p. 98, second claim, **corrected** (E2): if
`0 < V_π ≤ var(r̂)`, then among rules satisfying (2.13) that achieve `var(π) = V_π`, a larger
`ρ` gives a strictly smaller `var(î)`. -/
theorem prop_2_9_monotone {ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ)
    (hle : Vπ ≤ msq (irfR ρr)) {ρ₁ ρ₂ φ₁ φ₂ : ℝ} (h12 : ρ₁ < ρ₂) (h1 : 1 < φ₁ + ρ₁)
    (h2 : 1 < φ₂ + ρ₂) (ha₁ : msq (irfPi φ₁ ρ₁ ρr) = Vπ) (ha₂ : msq (irfPi φ₂ ρ₂ ρr) = Vπ) :
    msq (irfI φ₂ ρ₂ ρr) < msq (irfI φ₁ ρ₁ ρr) := by
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  rw [msq_irfI_eq_sq hρr hVπ (by linarith) ha₁, msq_irfI_eq_sq hρr hVπ (by linarith) ha₂]
  have hc : 0 < 1 - ρr ^ 2 := by
    have : ρr ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρr).mpr hρr
    linarith
  have hmono := hfun_strictMono hc (show ρ₁ - ρr < ρ₂ - ρr by linarith)
  simp only at hmono
  rw [← Q_eq, ← Q_eq] at hmono
  have hlt1 : ∀ ρ : ℝ, (ρ - ρr) / √(1 - 2 * ρr * ρ + ρ ^ 2) < 1 := fun ρ => by
    have hQ : 0 < 1 - 2 * ρr * ρ + ρ ^ 2 := lt_of_le_of_lt (sq_nonneg _) (sq_lt_Q hρr ρ)
    rw [div_lt_one (Real.sqrt_pos.mpr hQ)]
    have habs : |ρ - ρr| < √(1 - 2 * ρr * ρ + ρ ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
      exact sq_lt_Q hρr ρ
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hsP : 0 < √Vπ := Real.sqrt_pos.mpr hVπ
  have hsle : √Vπ ≤ √(msq (irfR ρr)) := Real.sqrt_le_sqrt hle
  have hb2 : 0 < √(msq (irfR ρr)) - (ρ₂ - ρr) / √(1 - 2 * ρr * ρ₂ + ρ₂ ^ 2) * √Vπ := by
    nlinarith [hlt1 ρ₂]
  refine pow_lt_pow_left₀ ?_ hb2.le two_ne_zero
  nlinarith

/-- Woodford (2003), **Proposition 2.9**, pp. 97–98, **corrected** (E2): for a stationary AR(1)
natural rate (`|ρ_r| < 1`) and a target `0 < V_π ≤ var(r̂)`: (i) for every `ρ ≥ 1` there is a
unique `φ_π` with `φ_π > 0`, `φ_π + ρ > 1` (2.13) and `var(π) = V_π`; (ii) the larger `ρ`, the
smaller `var(î)` in that equilibrium. (The hypothesis `V_π ≤ var(r̂)` cannot be dropped:
`prop_2_9_printed_false`, `e2_counterexample`.) -/
theorem prop_2_9_corrected {ρr Vπ : ℝ} (hρr : |ρr| < 1) (hVπ : 0 < Vπ)
    (hle : Vπ ≤ msq (irfR ρr)) :
    (∀ ρ : ℝ, 1 ≤ ρ → ∃! φ : ℝ, 0 < φ ∧ 1 < φ + ρ ∧ msq (irfPi φ ρ ρr) = Vπ) ∧
      ∀ ρ₁ ρ₂ φ₁ φ₂ : ℝ, ρ₁ < ρ₂ → 1 < φ₁ + ρ₁ → 1 < φ₂ + ρ₂ →
        msq (irfPi φ₁ ρ₁ ρr) = Vπ → msq (irfPi φ₂ ρ₂ ρr) = Vπ →
          msq (irfI φ₂ ρ₂ ρr) < msq (irfI φ₁ ρ₁ ρr) := by
  refine ⟨fun ρ hρ => ⟨_, prop_2_9_exists hρr hVπ hle hρ, fun φ hφ =>
    prop_2_9_unique hρr hVπ hφ.2.1 hφ.2.2⟩, fun ρ₁ ρ₂ φ₁ φ₂ h12 h1 h2 ha₁ ha₂ =>
    prop_2_9_monotone hρr hVπ hle h12 h1 h2 ha₁ ha₂⟩

/-- Woodford (2003), Prop. 2.9, p. 98, as printed, is **false** when `V_π > var(r̂)` (E2): for
all large `ρ` no rule with `φ_π > 0` and `φ_π + ρ > 1` achieves `var(π) = V_π`. -/
theorem prop_2_9_false {ρr Vπ : ℝ} (hρr : |ρr| < 1) (hlt : msq (irfR ρr) < Vπ) :
    ∃ ρ₀ : ℝ, ∀ ρ, ρ₀ ≤ ρ → ∀ φ, 0 < φ → 1 < φ + ρ → msq (irfPi φ ρ ρr) ≠ Vπ := by
  have hVr := msq_irfR_pos hρr
  have hgap : 0 < Vπ - msq (irfR ρr) := sub_pos.mpr hlt
  refine ⟨ρr + 1 + msq (irfR ρr) / (Vπ - msq (irfR ρr)), fun ρ hρ φ hφ h1 hach => ?_⟩
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  have hD : 0 < φ + ρ - ρr := by linarith
  rw [msq_irfPi hρr hD.ne'] at hach
  have hVπ : 0 < Vπ := by linarith
  have hk : (1 - 2 * ρr * ρ + ρ ^ 2) * msq (irfR ρr) = Vπ * (φ + ρ - ρr) ^ 2 := by
    rw [← hach]
    field_simp
  have hdiv : msq (irfR ρr) / (Vπ - msq (irfR ρr)) ≤ ρ - ρr - 1 := by linarith
  rw [div_le_iff₀ hgap] at hdiv
  have hu1 : 1 ≤ ρ - ρr := by
    have := div_nonneg hVr.le hgap.le
    linarith
  have hDu : ρ - ρr < φ + ρ - ρr := by linarith
  have hD2 : (ρ - ρr) ^ 2 < (φ + ρ - ρr) ^ 2 := by nlinarith
  have hc1 : (1 - ρr ^ 2) * msq (irfR ρr) ≤ msq (irfR ρr) := by nlinarith [sq_nonneg ρr]
  rw [Q_eq] at hk
  nlinarith [mul_lt_mul_of_pos_left hD2 hVπ, mul_le_mul_of_nonneg_right hu1 hgap.le]

/-- Woodford (2003), Prop. 2.9, p. 98: the printed claim "for any large enough value of `ρ`
there exists `φ_π > 0` satisfying (2.13) with `var(π) = V_π`" fails whenever
`V_π > var(r̂)` (E2). -/
theorem prop_2_9_printed_false {ρr Vπ : ℝ} (hρr : |ρr| < 1) (hlt : msq (irfR ρr) < Vπ) :
    ¬ ∃ ρ₀ : ℝ, ∀ ρ, ρ₀ ≤ ρ → ∃ φ, 0 < φ ∧ 1 < φ + ρ ∧ msq (irfPi φ ρ ρr) = Vπ := by
  rintro ⟨ρ₀, h⟩
  obtain ⟨ρ₁, h1⟩ := prop_2_9_false hρr hlt
  obtain ⟨φ, hφ, hφ1, hach⟩ := h (max ρ₀ ρ₁) (le_max_left _ _)
  exact h1 _ (le_max_right _ _) φ hφ hφ1 hach

/-- Woodford (2003), Prop. 2.9 counterexample (E2), `ρ_r = 0.8`, `var(π) = 2 var(r̂)`, `ρ = 2`:
a determinate rule (`φ_π ≠ 0`, `|φ_π + ρ| > 1`) achieves the target only for
`φ_π = 3√10/10 − 6/5 ≈ −0.25 < 0`, and then `var(î) = (13/5 − 4√10/5) var(r̂) ≈ 0.070 var(r̂)`. -/
theorem e2_rho_two :
    (3 * √10 / 10 - 6 / 5 : ℝ) < 0 ∧ 1 < |(3 * √10 / 10 - 6 / 5 : ℝ) + 2| ∧
      msq (irfPi (3 * √10 / 10 - 6 / 5) 2 (4 / 5)) = 2 * msq (irfR (4 / 5)) ∧
      msq (irfI (3 * √10 / 10 - 6 / 5) 2 (4 / 5)) = (13 / 5 - 4 * √10 / 5) * msq (irfR (4 / 5)) ∧
      ∀ φ : ℝ, 1 < |φ + 2| → msq (irfPi φ 2 (4 / 5)) = 2 * msq (irfR (4 / 5)) →
        φ = 3 * √10 / 10 - 6 / 5 := by
  have hρr : |(4 / 5 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  set w := √10 with hw_def
  have hw : w ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hw0 : 0 < w := Real.sqrt_pos.mpr (by norm_num)
  have hw3 : 3 < w := by nlinarith
  have hw4 : w < 4 := by nlinarith
  have hD : (3 * w / 10 - 6 / 5) + 2 - 4 / 5 = 3 * w / 10 := by ring
  have hK : (1 - (4 / 5 : ℝ) ^ 2)⁻¹ ≠ 0 := by norm_num
  refine ⟨by linarith, by rw [abs_of_pos (by linarith)]; linarith, ?_, ?_, ?_⟩
  · rw [msq_irfPi hρr (by rw [hD]; positivity), hD, msq_irfR hρr]
    congr 1
    field_simp
    nlinarith
  · rw [msq_irfI hρr, hD]
    have h1 : (3 * w / 10 - 6 / 5) / (3 * w / 10) = 1 - 2 * w / 5 := by
      rw [div_eq_iff (by positivity)]
      linear_combination (3 / 25 : ℝ) * hw
    rw [h1]
    congr 1
    linear_combination (4 / 25 : ℝ) * hw
  · intro φ hc hach
    have hDne : φ + 2 - 4 / 5 ≠ 0 := by
      intro h
      have h' : φ + 2 = 4 / 5 := by linarith
      rw [h', abs_of_pos (by norm_num)] at hc
      norm_num at hc
    rw [msq_irfPi hρr hDne, msq_irfR hρr] at hach
    have h' := mul_right_cancel₀ hK hach
    rw [div_eq_iff (pow_ne_zero 2 hDne)] at h'
    have hprod : (φ + 2 - 4 / 5 - 3 * w / 10) * (φ + 2 - 4 / 5 + 3 * w / 10) = 0 := by
      linear_combination (-1 / 2 : ℝ) * h' - (9 / 100 : ℝ) * hw
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso
      have hlo : φ + 2 = 4 / 5 - 3 * w / 10 := by linarith
      rw [hlo, abs_of_neg (by linarith : (4 / 5 : ℝ) - 3 * w / 10 < 0)] at hc
      linarith

/-- Woodford (2003), Prop. 2.9 counterexample (E2), `ρ_r = 0.8`, `var(π) = 2 var(r̂)`, `ρ = 5`:
the determinate rules achieving the target are `φ_π = −6/5` (with `var(î) = (4/25) var(r̂)`) and
`φ_π = −36/5`; every one of them has `φ_π < 0` and `var(î) ≥ (4/25) var(r̂)`. -/
theorem e2_rho_five :
    1 < |(-6 / 5 : ℝ) + 5| ∧ msq (irfPi (-6 / 5) 5 (4 / 5)) = 2 * msq (irfR (4 / 5)) ∧
      msq (irfI (-6 / 5) 5 (4 / 5)) = 4 / 25 * msq (irfR (4 / 5)) ∧
      ∀ φ : ℝ, 1 < |φ + 5| → msq (irfPi φ 5 (4 / 5)) = 2 * msq (irfR (4 / 5)) →
        φ < 0 ∧ 4 / 25 * msq (irfR (4 / 5)) ≤ msq (irfI φ 5 (4 / 5)) := by
  have hρr : |(4 / 5 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hVr := msq_irfR_pos hρr
  have hK : (1 - (4 / 5 : ℝ) ^ 2)⁻¹ ≠ 0 := by norm_num
  refine ⟨by norm_num [abs_of_pos], ?_, ?_, ?_⟩
  · rw [msq_irfPi hρr (by norm_num), msq_irfR hρr]
    norm_num
  · rw [msq_irfI hρr]
    norm_num
  · intro φ hc hach
    have hDne : φ + 5 - 4 / 5 ≠ 0 := by
      intro h
      have h' : φ + 5 = 4 / 5 := by linarith
      rw [h', abs_of_pos (by norm_num)] at hc
      norm_num at hc
    rw [msq_irfPi hρr hDne, msq_irfR hρr] at hach
    have h' := mul_right_cancel₀ hK hach
    rw [div_eq_iff (pow_ne_zero 2 hDne)] at h'
    have hprod : (φ + 5 - 4 / 5 - 3) * (φ + 5 - 4 / 5 + 3) = 0 := by
      linear_combination (-1 / 2 : ℝ) * h'
    rw [msq_irfI hρr]
    rcases mul_eq_zero.mp hprod with h | h
    · obtain rfl : φ = -6 / 5 := by linarith
      norm_num
    · obtain rfl : φ = -36 / 5 := by linarith
      norm_num
      nlinarith

/-- Woodford (2003), Prop. 2.9, pp. 97–98, **counterexample** (E2): with `ρ_r = 0.8` and
`var(π) = 2 var(r̂)`, the rules achieving the target at `ρ = 2` and `ρ = 5` all have
`φ_π < 0` (so none satisfies the proposition's `φ_π > 0`), and `var(î)` is *larger* at
`ρ = 5` (at least `0.16 var(r̂)`) than at `ρ = 2` (`≈ 0.070 var(r̂)`): `var(î)` is not
decreasing in `ρ`. -/
theorem e2_counterexample :
    (∀ φ : ℝ, 1 < |φ + 2| → msq (irfPi φ 2 (4 / 5)) = 2 * msq (irfR (4 / 5)) → φ < 0) ∧
      (∀ φ : ℝ, 1 < |φ + 5| → msq (irfPi φ 5 (4 / 5)) = 2 * msq (irfR (4 / 5)) → φ < 0) ∧
      ∀ φ : ℝ, 1 < |φ + 5| → msq (irfPi φ 5 (4 / 5)) = 2 * msq (irfR (4 / 5)) →
        msq (irfI (3 * √10 / 10 - 6 / 5) 2 (4 / 5)) < msq (irfI φ 5 (4 / 5)) := by
  obtain ⟨hneg2, -, -, hI2, huniq2⟩ := e2_rho_two
  obtain ⟨-, -, -, h5⟩ := e2_rho_five
  have hρr : |(4 / 5 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hVr := msq_irfR_pos hρr
  have hw : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hw0 : 0 < √10 := Real.sqrt_pos.mpr (by norm_num)
  have hw61 : 61 / 20 < √10 := by nlinarith
  refine ⟨fun φ hc hach => (huniq2 φ hc hach) ▸ hneg2, fun φ hc hach => (h5 φ hc hach).1,
    fun φ hc hach => ?_⟩
  rw [hI2]
  have := (h5 φ hc hach).2
  nlinarith

/-! ### Proposition 2.10: the superinertial rule as a forecast-targeting rule -/

/-- Woodford (2003), §A.10, p. 643: the expectation system seen from date `n` on,
`E'_t = E_{t+n}` (used to apply the forward-solution lemma from a starting date). -/
def shiftE (n : ℕ) : ExpectationSystem Ω where
  E t := 𝔼.E (t + n)
  const t := 𝔼.const (t + n)
  mono t := 𝔼.mono (t + n)
  tower h x := 𝔼.tower (Nat.add_le_add_right h n) x
  known h x := 𝔼.known (Nat.add_le_add_right h n) x

/-- Woodford (2003), **Proposition 2.10**, pp. 100–101, and §A.10, p. 643: let `ρ > 1` and let
`{π, î, ī}` be bounded adapted processes. Then (2.12) holds at every date `t + 1` with
`t ≥ t₀` (the rule is in force from `t₀ + 1`, so `î_{t₀} − ī_{t₀}` is the first lagged gap) if
and only if the forecast-targeting criterion (2.17)
`∑_j ρ^{−(j+1)} φ_π E_{t+1} π_{t+1+j} = −(î_t − ī_t)` holds at every such date. -/
theorem prop_2_10 {φ ρ : ℝ} (hρ : 1 < ρ) (t₀ : ℕ) {π i ibar : ℕ → Ω → ℝ}
    (hπb : BoundedProc π) (hib : BoundedProc i) (hbb : BoundedProc ibar)
    (hπa : 𝔼.Adapted π) (hia : 𝔼.Adapted i) (hba : 𝔼.Adapted ibar) :
    (∀ t, t₀ ≤ t → i (t + 1) - ibar (t + 1) = ρ • (i t - ibar t) + φ • π (t + 1)) ↔
      ∀ t, t₀ ≤ t → ∀ ω, ∑' j : ℕ, (ρ⁻¹) ^ (j + 1) * φ * 𝔼.E (t + 1) (π (t + 1 + j)) ω =
        -(i t ω - ibar t ω) := by
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Mb, hMb⟩ := hbb
  have hρ0 : ρ ≠ 0 := by positivity
  set 𝔽 := shiftE 𝔼 (t₀ + 1) with h𝔽
  have ha0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  set u : ℕ → Ω → ℝ := fun k => (-(ρ⁻¹ * φ)) • π (k + t₀ + 1) with hu_def
  set z : ℕ → Ω → ℝ := fun k => i (k + t₀) - ibar (k + t₀) with hz_def
  have hub : ∀ k ω, |u k ω| ≤ |ρ⁻¹| * |φ| * Mπ := by
    intro k ω
    simp only [hu_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hMπ _ ω) (by positivity)
  have hua : 𝔽.Adapted u := fun k => by
    change 𝔼.E (k + (t₀ + 1)) ((-(ρ⁻¹ * φ)) • π (k + t₀ + 1)) = (-(ρ⁻¹ * φ)) • π (k + t₀ + 1)
    rw [map_smul, show k + (t₀ + 1) = k + t₀ + 1 by omega, hπa]
  have hzE : ∀ k, 𝔽.E k (z (k + 1)) = z (k + 1) := fun k => by
    change 𝔼.E (k + (t₀ + 1)) (i (k + 1 + t₀) - ibar (k + 1 + t₀)) =
      i (k + 1 + t₀) - ibar (k + 1 + t₀)
    rw [show k + (t₀ + 1) = k + 1 + t₀ by omega, map_sub, hia, hba]
  have hzb : BoundedProc z :=
    ⟨Mi + Mb, fun k ω => (abs_sub _ _).trans (add_le_add (hMi _ ω) (hMb _ ω))⟩
  have hFS : ∀ k ω, 𝔽.forwardSeries ρ⁻¹ u k ω =
      -(∑' j : ℕ, (ρ⁻¹) ^ (j + 1) * φ * 𝔼.E (k + t₀ + 1) (π (k + t₀ + 1 + j)) ω) := by
    intro k ω
    change ∑' j, ρ⁻¹ ^ j * 𝔼.E (k + (t₀ + 1)) (u (k + j)) ω = _
    rw [← tsum_neg]
    refine tsum_congr fun j => ?_
    simp only [hu_def]
    rw [map_smul, Pi.smul_apply, smul_eq_mul, show k + j + t₀ + 1 = k + t₀ + 1 + j by omega,
      show k + (t₀ + 1) = k + t₀ + 1 by omega, pow_succ]
    ring
  have hstep : ∀ k, (i (k + t₀ + 1) - ibar (k + t₀ + 1) =
      ρ • (i (k + t₀) - ibar (k + t₀)) + φ • π (k + t₀ + 1)) ↔
      z k = ρ⁻¹ • 𝔽.E k (z (k + 1)) + u k := by
    intro k
    rw [hzE k]
    simp only [hz_def, hu_def, show k + 1 + t₀ = k + t₀ + 1 by omega]
    constructor
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    · intro h
      funext ω
      have h' := congrFun h ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
      rw [h']
      field_simp
      ring
  constructor
  · intro hR t ht ω
    have hz : z = 𝔽.forwardSeries ρ⁻¹ u :=
      𝔽.eq_forwardSeries ha0 ha1 hub hua (fun k => (hstep k).mp (hR (k + t₀) (by omega))) hzb
    obtain ⟨k, rfl⟩ : ∃ k, t = k + t₀ := ⟨t - t₀, by omega⟩
    have h := congrFun (congrFun hz k) ω
    rw [hFS k ω] at h
    simp only [hz_def, Pi.sub_apply] at h
    linarith
  · intro hG t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + t₀ := ⟨t - t₀, by omega⟩
    have hz : z = 𝔽.forwardSeries ρ⁻¹ u := by
      funext m ω
      rw [hFS m ω, hG (m + t₀) (by omega) ω]
      simp only [hz_def, Pi.sub_apply]
      ring
    refine (hstep k).mpr ?_
    have h := 𝔽.forwardSeries_solves ha0 ha1 hub hua k
    rw [← hz] at h
    exact h

end Woodford.PriceLevelDetermination.InertialRules
