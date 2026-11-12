/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.ConditioningDownMeasure

/-!
# Conditioning down with integrable processes, and at `|ρ| = 1`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, pp. 101–102, and
Online Appendix Chapter 2, §2.1.7, eqs. (2.22)–(2.23), pp. 602–603; the identities conditioned
down are (3.17)–(3.20), pp. 63–65, and (4.2), p. 87.

`ConditioningDownMeasure` proved the conditioning-down results for essentially bounded
processes and `|ρ| < 1`. Here the boundedness is replaced by integrability with discounted
summability of the `L¹` norms, `∑_j |ρ|ʲ E|x_{k+j}| < ∞` (`DiscL1`), which holds

* for `|ρ| < 1` and processes bounded in `L¹` (`DiscL1.of_integral_bdd`) or in `L²`
  (`DiscL1.of_sq_bdd`), in particular for bounded processes (`DiscL1.of_bdd`), and
* for every `|ρ| ≤ 1`, including `ρ = ±1`, when `∑_j E|x_j| < ∞` (`DiscL1.of_summable`).

The key tool is that conditional expectations commute with `L¹`-summable series
(`E_hasSum_L1`, from Mathlib's `condExp_tsum`). At `|ρ| = 1` with merely bounded processes the
ex-post present value is false (`pv_unit_root_fails`: `x_t = ρᵗ`, no payoff); the correct
statement for every `ρ` and integrable processes is that the present value converges iff the
corresponding terminal condition holds (`pv_E_iff_tvc`, `innov_pv_iff_tvc`,
`condDown_flow_iff_tvc`), as in the core's `ρ = 1` treatment with ordinary convergence of series,
and with partial sums converging in `L¹` the econometrician's forecasts converge in `L¹` to
`E(v_t|I_t)` (`condDown_valuation_tendsto_L1`).

## Main results

* Tools: `ae_summable_abs`, `E_hasSum_L1`, `DiscL1` and its constructors.
* `|ρ|`-general `L¹` versions of `ConditioningDownMeasure`: `pv_ex_post_L1`, `pv_E_L1`,
  `pv_agents_L1`, `condDown_valuation_L1`, `condDown_valuation_L1_iff`, `condDown_flow_iff_L1`,
  `innov_pv_L1`, `unexpected_inflation_any_L1`, `unexpected_inflation_agents_L1`,
  `simple_model_any_L1`, `simple_model_agents_L1`, `simple_model_econ_iff_L1`;
  the bounded originals are special cases (`condDown_valuation_iff_of_bdd`).
* Every `ρ`, integrable processes, exact characterisations: `E_rec_finite`, `pv_E_iff_tvc`,
  `innov_pv_iff_tvc`, `condDown_flow_iff_tvc`; `L¹` convergence: `pv_E_tendsto_L1`,
  `condDown_valuation_tendsto_L1`, `condDown_valuation_tendsto_L1_iff`.
* `|ρ| = 1`: `pv_unit_root_fails` (the bounded statements fail), `condDown_flow_unit_root`
  (the corrected statement under `∑E|x_j| < ∞`).
-/

namespace Cochrane.DebtDeficitsInflation.TidyR6ConditioningDownL1

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.DebtDeficitsInflation.ExpectationsMeasure
open Cochrane.DebtDeficitsInflation.ConditioningDownMeasure
open Cochrane.DebtDeficitsInflation.LinearizedIdentities (Recursion Flow rec_finite SeriesTo
  seriesTo_of_hasSum flow_iff_recursion)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Series of integrable random variables -/

/-- Cochrane (2023), eq. (3.19), p. 64 (tool): for an integrable real variable,
`∫⁻ ‖g‖ₑ = ENNReal.ofReal (E|g|)`. -/
theorem lintegral_enorm_eq {μ : Measure Ω} {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫⁻ ω, ‖g ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, |g ω| ∂μ) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hg]
  simp only [Real.norm_eq_abs]

/-- Cochrane (2023), eq. (3.19), p. 64 (tool): `∑_j E|g_j| < ∞` in extended form. -/
theorem tsum_lintegral_ne_top {μ : Measure Ω} {g : ℕ → Ω → ℝ} (hi : ∀ j, Integrable (g j) μ)
    (hs : Summable fun j => ∫ ω, |g j ω| ∂μ) : ∑' j, ∫⁻ ω, ‖g j ω‖ₑ ∂μ ≠ ⊤ := by
  simp_rw [lintegral_enorm_eq (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun _ => abs_nonneg _) hs]
  exact ENNReal.ofReal_ne_top

/-- Cochrane (2023), eq. (3.19), p. 64 (tool): if `∑_j E|g_j| < ∞`, then `∑_j |g_j|` converges
almost surely (monotone convergence). -/
theorem ae_summable_abs {μ : Measure Ω} {g : ℕ → Ω → ℝ} (hi : ∀ j, Integrable (g j) μ)
    (hs : Summable fun j => ∫ ω, |g j ω| ∂μ) : ∀ᵐ ω ∂μ, Summable fun j => |g j ω| := by
  have hm : ∀ j, AEMeasurable (fun ω => ‖g j ω‖ₑ) μ := fun j => (hi j).aemeasurable.enorm
  have hlt : ∫⁻ ω, ∑' j, ‖g j ω‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hm]
    exact tsum_lintegral_ne_top hi hs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hlt] with ω hω
  have h1 : ∑' j, ((‖g j ω‖₊ : NNReal) : ENNReal) ≠ ⊤ := by
    simpa [enorm_eq_nnnorm] using hω.ne
  have h2 := NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  simpa [coe_nnnorm, Real.norm_eq_abs] using h2

/-- Cochrane (2023), eq. (3.19), p. 64, and Online Appendix (2.23), p. 602 (survey "new
infrastructure"): **conditional expectations commute with `L¹`-summable series**. If the `g_j`
are integrable with `∑_j E|g_j| < ∞`, then a.e. `∑_j E_m g_j = E_m ∑_j g_j`, a genuine `HasSum`
(no boundedness, any information). -/
theorem E_hasSum_L1 (T : MeasExpectationSystem Ω) {g : ℕ → Ω → ℝ}
    (hi : ∀ j, Integrable (g j) T.μ) (hs : Summable fun j => ∫ ω, |g j ω| ∂T.μ) (m : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => T.E m (g j) ω) (T.E m (fun ω' => ∑' j, g j ω') ω) := by
  have hc := condExp_tsum (μ := T.μ) (m := T.𝓕 m) (fun j => (hi j).aestronglyMeasurable)
    (tsum_lintegral_ne_top hi hs)
  have hsE : Summable fun j => ∫ ω, |T.E m (g j) ω| ∂T.μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_abs_condExp_le _) hs
  filter_upwards [hc, ae_summable_abs (fun j => T.integrable_E m (g j)) hsE] with ω h1 h2
  have h3 : T.E m (fun ω' => ∑' j, g j ω') ω = ∑' j, T.E m (g j) ω := h1
  rw [h3]
  exact (Summable.of_norm (by simpa [Real.norm_eq_abs] using h2)).hasSum

/-! ### Discounted `L¹` summability -/

/-- Cochrane (2023), eq. (3.19), p. 64 ("assuming that the sums converge"), the integrable
replacement for bounded processes: every `x_t` is integrable and the discounted `L¹` norms are
summable from every date on, `∑_j |ρ|ʲ E|x_{k+j}| < ∞`. -/
def DiscL1 (μ : Measure Ω) (ρ : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (x t) μ) ∧ ∀ k, Summable fun j => |ρ| ^ j * ∫ ω, |x (k + j) ω| ∂μ

/-- Cochrane (2023), eq. (3.19), p. 64: for `|ρ| < 1` a process bounded in `L¹`
(`E|x_t| ≤ K`) is `DiscL1`. -/
theorem DiscL1.of_integral_bdd {μ : Measure Ω} {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ}
    (hi : ∀ t, Integrable (x t) μ) {K : ℝ} (hK : ∀ t, ∫ ω, |x t ω| ∂μ ≤ K) : DiscL1 μ ρ x :=
  ⟨hi, fun k => Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (pow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => abs_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left (hK (k + j)) (pow_nonneg (abs_nonneg _) _))
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K)⟩

/-- Cochrane (2023), eq. (3.19), p. 64: for `|ρ| < 1` a process bounded in `L²`
(`E x_t² ≤ K`) on a probability space is `DiscL1` (`|x| ≤ 1 + x²`). -/
theorem DiscL1.of_sq_bdd {μ : Measure Ω} [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : |ρ| < 1)
    {x : ℕ → Ω → ℝ} (hm : ∀ t, MemLp (x t) 2 μ) {K : ℝ} (hK : ∀ t, ∫ ω, x t ω ^ 2 ∂μ ≤ K) :
    DiscL1 μ ρ x := by
  refine DiscL1.of_integral_bdd hρ (fun t => (hm t).integrable one_le_two) (K := 1 + K)
    fun t => ?_
  have hsq : Integrable (fun ω => x t ω ^ 2) μ := (hm t).integrable_sq
  calc ∫ ω, |x t ω| ∂μ ≤ ∫ ω, (1 + x t ω ^ 2) ∂μ := by
        refine integral_mono ((hm t).integrable one_le_two).abs ((integrable_const 1).add hsq)
          fun ω => ?_
        nlinarith [abs_nonneg (x t ω), sq_abs (x t ω)]
    _ = 1 + ∫ ω, x t ω ^ 2 ∂μ := by
        rw [integral_add (integrable_const 1) hsq]
        simp
    _ ≤ 1 + K := by linarith [hK t]

/-- Cochrane (2023), eq. (3.19), p. 64: for `|ρ| < 1` an essentially bounded measurable process
on a probability space is `DiscL1` (so the results below contain those of
`ConditioningDownMeasure`). -/
theorem DiscL1.of_bdd {μ : Measure Ω} [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : |ρ| < 1)
    {x : ℕ → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (x t) μ) {K : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂μ, |x t ω| ≤ K) : DiscL1 μ ρ x := by
  have hi : ∀ t, Integrable (x t) μ := fun t =>
    Integrable.of_bound (hm t) K ((hb t).mono fun ω h => by rwa [Real.norm_eq_abs])
  refine DiscL1.of_integral_bdd hρ hi (K := K) fun t => ?_
  calc ∫ ω, |x t ω| ∂μ ≤ ∫ _, K ∂μ := integral_mono_ae (hi t).abs (integrable_const K) (hb t)
    _ = K := by simp

/-- Cochrane (2023), eq. (3.19), p. 64, at `|ρ| ≤ 1` (including `ρ = ±1`): a process with
`∑_j E|x_j| < ∞` is `DiscL1`. -/
theorem DiscL1.of_summable {μ : Measure Ω} {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → Ω → ℝ}
    (hi : ∀ t, Integrable (x t) μ) (hs : Summable fun t => ∫ ω, |x t ω| ∂μ) : DiscL1 μ ρ x :=
  ⟨hi, fun k => Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => abs_nonneg _))
    (fun j => mul_le_of_le_one_left (integral_nonneg fun _ => abs_nonneg _)
      (pow_le_one₀ (abs_nonneg _) hρ))
    (((summable_nat_add_iff k).2 hs).congr fun j => by rw [add_comm j k])⟩

/-- Cochrane (2023), eq. (3.17), p. 63 (tool): `DiscL1` is closed under sums. -/
theorem DiscL1.add {μ : Measure Ω} {ρ : ℝ} {x y : ℕ → Ω → ℝ} (hx : DiscL1 μ ρ x)
    (hy : DiscL1 μ ρ y) : DiscL1 μ ρ (fun t => x t + y t) :=
  ⟨fun t => (hx.1 t).add (hy.1 t), fun k => Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => abs_nonneg _))
    (fun j => by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
      rw [← integral_add (hx.1 _).abs (hy.1 _).abs]
      exact integral_mono ((hx.1 _).add (hy.1 _)).abs ((hx.1 _).abs.add (hy.1 _).abs)
        fun ω => abs_add_le _ _)
    ((hx.2 k).add (hy.2 k))⟩

/-- Cochrane (2023), eq. (3.17), p. 63 (tool): `DiscL1` is closed under differences. -/
theorem DiscL1.sub {μ : Measure Ω} {ρ : ℝ} {x y : ℕ → Ω → ℝ} (hx : DiscL1 μ ρ x)
    (hy : DiscL1 μ ρ y) : DiscL1 μ ρ (fun t => x t - y t) :=
  ⟨fun t => (hx.1 t).sub (hy.1 t), fun k => Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => abs_nonneg _))
    (fun j => by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
      rw [← integral_add (hx.1 _).abs (hy.1 _).abs]
      exact integral_mono ((hx.1 _).sub (hy.1 _)).abs ((hx.1 _).abs.add (hy.1 _).abs)
        fun ω => abs_sub _ _)
    ((hx.2 k).add (hy.2 k))⟩

/-- Cochrane (2023), eq. (3.17), p. 63 (tool): the zero process is `DiscL1`. -/
theorem DiscL1.zero (μ : Measure Ω) (ρ : ℝ) : DiscL1 μ ρ (fun _ => 0) :=
  ⟨fun _ => integrable_zero _ _ _, fun _ => by simp⟩

/-- Cochrane (2023), eq. (3.19), p. 64 (tool): the discounted terms `ρʲx_{k+j}` have summable
`L¹` norms. -/
theorem DiscL1.summable_integral {μ : Measure Ω} {ρ : ℝ} {x : ℕ → Ω → ℝ} (hx : DiscL1 μ ρ x)
    (k : ℕ) : Summable fun j => ∫ ω, |ρ ^ j * x (k + j) ω| ∂μ :=
  (hx.2 k).congr fun j => by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [abs_mul, abs_pow])

/-- Cochrane (2023), eq. (3.19), p. 64 (tool): a.e. `∑_j |ρʲx_{k+j}|` converges. -/
theorem DiscL1.ae_summable {μ : Measure Ω} {ρ : ℝ} {x : ℕ → Ω → ℝ} (hx : DiscL1 μ ρ x)
    (k : ℕ) : ∀ᵐ ω ∂μ, Summable fun j => |ρ ^ j * x (k + j) ω| :=
  ae_summable_abs (fun _ => (hx.1 _).const_mul _) (hx.summable_integral k)

/-! ### Present values with integrable processes, for every `ρ` -/

/-- Cochrane (2023), eq. (3.18), p. 63, ex post, with integrable processes and any `ρ`: if
`x_t = ρx_{t+1} + f_{t+1}` holds state by state and `x`, `f` are `DiscL1`, then a.e.
`x_t = ∑_{j≥0} ρʲ f_{t+1+j}` (a genuine `HasSum`).
The `L¹` version of `ConditioningDownMeasure.pv_ex_post`. -/
theorem pv_ex_post_L1 {μ : Measure Ω} {ρ : ℝ} {x f : ℕ → Ω → ℝ} (hrec : Recursion ρ x f)
    (hx : DiscL1 μ ρ x) (hf : DiscL1 μ ρ f) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ρ ^ j * f (t + 1 + j) ω) (x t ω) := by
  filter_upwards [hx.ae_summable t, hf.ae_summable (t + 1)] with ω h1 h2
  have htvc : Tendsto (fun T => ρ ^ T * x (t + T) ω) atTop (𝓝 0) :=
    (Summable.of_norm (by simpa [Real.norm_eq_abs] using h1)).tendsto_atTop_zero
  have hs : Summable fun j => ‖ρ ^ j * f (t + 1 + j) ω‖ := by
    simpa [Real.norm_eq_abs] using h2
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs]
  have hfin : (fun T => ∑ j ∈ Finset.range T, ρ ^ j * f (t + 1 + j) ω) =
      fun T => x t ω - ρ ^ T * x (t + T) ω := by
    funext T
    have := congrFun (rec_finite hrec t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  rw [hfin]
  simpa using tendsto_const_nhds.sub htvc

/-- Cochrane (2023), eq. (3.19), p. 64, under ANY information, with integrable processes and any
`ρ`: with the recursion holding ex post and `x`, `f` `DiscL1`, for every date `m`, a.e.
`∑_{j≥0} ρʲ E_m f_{t+1+j} = E_m x_t`.
The `L¹` version of `ConditioningDownMeasure.pv_E`. -/
theorem pv_E_L1 (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ} (hrec : Recursion ρ x f)
    (hx : DiscL1 T.μ ρ x) (hf : DiscL1 T.μ ρ f) (t m : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.E m (f (t + 1 + j)) ω) (T.E m (x t) ω) := by
  have hE := E_hasSum_L1 T (g := fun j ω => ρ ^ j * f (t + 1 + j) ω)
    (fun _ => (hf.1 _).const_mul _) (hf.summable_integral (t + 1)) m
  have hsmul : ∀ j, T.E m (fun ω => ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ]
      fun ω => ρ ^ j * T.E m (f (t + 1 + j)) ω := fun j => T.E_smul (ρ ^ j) (f (t + 1 + j)) m
  have hX : (fun ω => ∑' j, ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ] x t := by
    filter_upwards [pv_ex_post_L1 hrec hx hf t] with ω hω
    exact hω.tsum_eq
  filter_upwards [hE, ae_all_iff.2 hsmul, T.E_congr hX m] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eq. (3.19), p. 64, for the agents, with integrable processes and any `ρ`:
the discounted forecasts of the payoff sum to `v_t` itself.
The `L¹` version of `ConditioningDownMeasure.pv_agents`. -/
theorem pv_agents_L1 (S : MeasExpectationSystem Ω) {ρ : ℝ} {v f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ v f) (hvm : StronglyAdapted S.𝓕 v) (hv : DiscL1 S.μ ρ v)
    (hf : DiscL1 S.μ ρ f) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (f (t + 1 + j)) ω) (v t ω) := by
  have hE : S.E t (v t) = v t := S.E_of_stronglyMeasurable (hvm t) (hv.1 t)
  filter_upwards [pv_E_L1 S hrec hv hf t t] with ω hω
  rwa [hE] at hω

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101, with integrable surpluses and any
`ρ` (including `ρ = ±1` when `∑E|s_j| < ∞`): if `v_t = E(∑ρʲs_{t+1+j}|Ω_t)` a.e. and `s` is
`DiscL1`, the econometrician's discounted forecasts sum to `E(v_t|I_t)` a.e.
The `L¹` version of `ConditioningDownMeasure.condDown_valuation`. -/
theorem condDown_valuation_L1 {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} {s : ℕ → Ω → ℝ} (hs : DiscL1 S.μ ρ s) {t : ℕ} {v : Ω → ℝ}
    (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω)
      ((coarsen S 𝓖).E t v ω) := by
  set G := coarsen S 𝓖
  have hE := E_hasSum_L1 G (g := fun j ω => ρ ^ j * s (t + 1 + j) ω)
    (fun _ => (hs.1 _).const_mul _) (hs.summable_integral (t + 1)) t
  have hsmul : ∀ j, G.E t (fun ω => ρ ^ j * s (t + 1 + j) ω) =ᵐ[S.μ]
      fun ω => ρ ^ j * G.E t (s (t + 1 + j)) ω := fun j => G.E_smul (ρ ^ j) (s (t + 1 + j)) t
  filter_upwards [hE, ae_all_iff.2 hsmul, condDown_general h hv] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101 ("this conditioning down is valid, so
long as `v_t ∈ I_t`"), with integrable surpluses and any `ρ`: the econometrician's discounted
forecasts sum to `v_t` a.e. **iff** `v_t` is in the VAR information.
The `L¹` version of `ConditioningDownMeasure.condDown_valuation_iff`. -/
theorem condDown_valuation_L1_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} {s : ℕ → Ω → ℝ} (hs : DiscL1 S.μ ρ s) {t : ℕ} {v : Ω → ℝ}
    (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω) (v ω)) ↔
      KnownAE S.μ 𝓖 t v := by
  have hi : Integrable v S.μ := (S.integrable_E t _).congr hv.symm
  rw [← known_iff_E_eq S 𝓖 hi]
  have hH := condDown_valuation_L1 h hs hv
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, link: the bounded statement
`ConditioningDownMeasure.condDown_valuation_iff` (`|ρ| < 1`, bounded measurable surpluses) is the
special case `DiscL1.of_bdd` of `condDown_valuation_L1_iff`. -/
theorem condDown_valuation_iff_of_bdd {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ j, AEStronglyMeasurable (s j) S.μ) {K : ℝ} (hs : ∀ j, ∀ᵐ ω ∂S.μ, |s j ω| ≤ K)
    {t : ℕ} {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    DiscL1 S.μ ρ s ∧
    ((∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω) (v ω)) ↔
      KnownAE S.μ 𝓖 t v) :=
  ⟨DiscL1.of_bdd hρ hsm hs, condDown_valuation_L1_iff h (DiscL1.of_bdd hρ hsm hs) hv⟩

/-- Cochrane (2023), p. 101, and Online Appendix p. 602, with the flow identity (3.17) ex post,
integrable `DiscL1` processes and any `ρ`: the econometrician's discounted forecasts of
`s̃ + g − r` sum to `E(v_t|I_t)`, hence to `v_t` iff `v_t ∈ I_t`.
The `L¹` version of `ConditioningDownMeasure.condDown_flow_iff`. -/
theorem condDown_flow_iff_L1 {S : MeasExpectationSystem Ω} (𝓖 : Filtration ℕ mΩ) {ρ : ℝ}
    {v r g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hv : DiscL1 S.μ ρ v)
    (hf : DiscL1 S.μ ρ (fun t => s t + g t - r t)) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω)) ∧
    ((∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) (v t ω)) ↔ KnownAE S.μ 𝓖 t (v t)) := by
  have hrec := (flow_iff_recursion ρ v r g s).1 hflow
  have hH := pv_E_L1 (coarsen S 𝓖) hrec hv hf t t
  refine ⟨hH, ?_⟩
  rw [← known_iff_E_eq S 𝓖 (hv.1 t)]
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-! ### Unexpected inflation with integrable processes, for every `ρ` -/

/-- Cochrane (2023), eq. (3.20), p. 65 (tool): discounted news about a `DiscL1` process is
summable a.e. (`E|Δ_{t+1}x| ≤ 2E|x|`).
The `L¹` version of `ConditioningDownMeasure.summable_innov`. -/
theorem summable_innov_L1 (T : MeasExpectationSystem Ω) {ρ : ℝ} {x : ℕ → Ω → ℝ}
    (hx : DiscL1 T.μ ρ x) (t k : ℕ) :
    ∀ᵐ ω ∂T.μ, Summable fun j => ρ ^ j * T.innov t (x (k + j)) ω := by
  have hi : ∀ j, Integrable (fun ω => ρ ^ j * T.innov t (x (k + j)) ω) T.μ := fun j =>
    ((T.integrable_E (t + 1) _).sub (T.integrable_E t _)).const_mul _
  have hle : ∀ j, ∫ ω, |ρ ^ j * T.innov t (x (k + j)) ω| ∂T.μ ≤
      2 * (|ρ| ^ j * ∫ ω, |x (k + j) ω| ∂T.μ) := fun j => by
    have h1 : ∫ ω, |ρ ^ j * T.innov t (x (k + j)) ω| ∂T.μ =
        |ρ| ^ j * ∫ ω, |T.innov t (x (k + j)) ω| ∂T.μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [abs_mul, abs_pow])
    have h2 : ∫ ω, |T.innov t (x (k + j)) ω| ∂T.μ ≤ 2 * ∫ ω, |x (k + j) ω| ∂T.μ := by
      have hE1 := T.integrable_E (t + 1) (x (k + j))
      have hE0 := T.integrable_E t (x (k + j))
      calc ∫ ω, |T.innov t (x (k + j)) ω| ∂T.μ
          ≤ ∫ ω, (|T.E (t + 1) (x (k + j)) ω| + |T.E t (x (k + j)) ω|) ∂T.μ :=
            integral_mono (hE1.sub hE0).abs (hE1.abs.add hE0.abs) fun ω => abs_sub _ _
        _ = ∫ ω, |T.E (t + 1) (x (k + j)) ω| ∂T.μ + ∫ ω, |T.E t (x (k + j)) ω| ∂T.μ :=
            integral_add hE1.abs hE0.abs
        _ ≤ ∫ ω, |x (k + j) ω| ∂T.μ + ∫ ω, |x (k + j) ω| ∂T.μ :=
            add_le_add (integral_abs_condExp_le _) (integral_abs_condExp_le _)
        _ = 2 * ∫ ω, |x (k + j) ω| ∂T.μ := by ring
    rw [h1]
    nlinarith [pow_nonneg (abs_nonneg ρ) j]
  have hs : Summable fun j => ∫ ω, |ρ ^ j * T.innov t (x (k + j)) ω| ∂T.μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _) hle
      ((hx.2 k).mul_left 2)
  filter_upwards [ae_summable_abs hi hs] with ω h
  exact Summable.of_norm (by simpa [Real.norm_eq_abs] using h)

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information, with integrable processes and any
`ρ`: with the recursion `x_t = ρx_{t+1} + f_{t+1}` ex post (`DiscL1` `x`, `f`), a.e.
`∑_{j≥0} ρʲ Δ_{t+1} f_{t+1+j} = Δ_{t+1} x_t`.
The `L¹` version of `ConditioningDownMeasure.innov_pv`. -/
theorem innov_pv_L1 (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) (hx : DiscL1 T.μ ρ x) (hf : DiscL1 T.μ ρ f) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.innov t (f (t + 1 + j)) ω) (T.innov t (x t) ω) := by
  filter_upwards [pv_E_L1 T hrec hx hf t (t + 1), pv_E_L1 T hrec hx hf t t] with ω h1 h2
  refine (h1.sub h2).congr_fun fun j => ?_
  simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information, with integrable (`DiscL1`)
processes and any `ρ` (the `L¹` version of `ConditioningDownMeasure.unexpected_inflation_any`):
if (3.17) holds ex post with `r = rⁿ − π`, then a.e.
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j} + Δ_{t+1}v_t`. -/
theorem unexpected_inflation_any_L1 (T : MeasExpectationSystem Ω) {ρ : ℝ}
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hv : DiscL1 T.μ ρ v) (hs : DiscL1 T.μ ρ s) (hg : DiscL1 T.μ ρ g) (hrb : DiscL1 T.μ ρ r)
    (hrn : ∀ t, Integrable (rn t) T.μ) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, T.innov t (infl (t + 1)) ω - T.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * T.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * T.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω + T.innov t (v t) ω := by
  have hsi := hs.1
  have hgi := hg.1
  have hri := hrb.1
  have hfb : DiscL1 T.μ ρ (fun t => s t + g t - r t) := (hs.add hg).sub hrb
  have hH := innov_pv_L1 T ((flow_iff_recursion ρ v r g s).1 hflow) hv hfb t
  have hlin : ∀ j, ∀ᵐ ω ∂T.μ, T.innov t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω =
      T.innov t (s (t + 1 + j)) ω + T.innov t (g (t + 1 + j)) ω -
        T.innov t (r (t + 1 + j)) ω := fun j => by
    have hsg := (hsi (t + 1 + j)).add (hgi (t + 1 + j))
    filter_upwards [T.E_sub hsg (hri (t + 1 + j)) (t + 1), T.E_sub hsg (hri (t + 1 + j)) t,
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) (t + 1),
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) t] with ω h1 h2 h3 h4
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply] at *
    rw [h1, h2, h3, h4]
    ring
  have hinfl : ∀ᵐ ω ∂T.μ, T.innov t (r (t + 1)) ω =
      T.innov t (rn (t + 1)) ω - T.innov t (infl (t + 1)) ω := by
    have hii : Integrable (infl (t + 1)) T.μ := by
      have : infl (t + 1) = rn (t + 1) - r (t + 1) := by rw [hr (t + 1)]; abel
      rw [this]
      exact (hrn (t + 1)).sub (hri (t + 1))
    filter_upwards [T.E_sub (hrn (t + 1)) hii (t + 1), T.E_sub (hrn (t + 1)) hii t] with ω h1 h2
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
    rw [hr (t + 1), h1, h2, Pi.sub_apply, Pi.sub_apply]
    ring
  filter_upwards [hH, ae_all_iff.2 hlin, hinfl, summable_innov_L1 T hs t (t + 1),
    summable_innov_L1 T hg t (t + 1), summable_innov_L1 T hrb t (t + 1)]
    with ω h1 h2 h3 h4 h5 h6
  have hsum : HasSum (fun j => ρ ^ j * T.innov t (s (t + 1 + j)) ω +
      ρ ^ j * T.innov t (g (t + 1 + j)) ω - ρ ^ j * T.innov t (r (t + 1 + j)) ω)
      (T.innov t (v t) ω) := h1.congr_fun fun j => by rw [h2 j]; ring
  have hsplit := (h4.hasSum.add h5.hasSum).sub h6.hasSum
  have heq := hsum.unique hsplit
  have hr0 := h6.tsum_eq_zero_add
  simp only [pow_zero, one_mul, add_zero] at hr0
  have hr1 : ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 1 + (j + 1))) ω =
      ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω :=
    tsum_congr fun j => by rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  rw [hr1, h3] at hr0
  linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (the book's form, for the agents), with integrable
processes and any `ρ`: when `v_t` is known at `t` the extra term vanishes.
The `L¹` version of `ConditioningDownMeasure.unexpected_inflation_agents`. -/
theorem unexpected_inflation_agents_L1 (S : MeasExpectationSystem Ω) {ρ : ℝ}
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hvm : StronglyAdapted S.𝓕 v) (hv : DiscL1 S.μ ρ v) (hs : DiscL1 S.μ ρ s)
    (hg : DiscL1 S.μ ρ g) (hrb : DiscL1 S.μ ρ r) (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * S.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * S.innov t (r (t + 2 + j)) ω := by
  have h0 : S.innov t (v t) = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov,
      S.E_of_stronglyMeasurable ((hvm t).mono (S.𝓕.mono (Nat.le_succ t))) (hv.1 t),
      S.E_of_stronglyMeasurable (hvm t) (hv.1 t), sub_self]
  filter_upwards [unexpected_inflation_any_L1 S hflow hr hv hs hg hrb hrn t] with ω hω
  rw [hω, h0, Pi.zero_apply, add_zero]

/-- Cochrane (2023), eq. (4.2), p. 87, and (3.24), p. 66 (the simple model), under ANY
information nested in the agents', with integrable processes and any `ρ`: a.e.
`Δ^Iπ_{t+1} − Δ^Irⁿ_{t+1} = −∑ρʲΔ^I s̃_{t+1+j} + Δ^I_{t+1} v_t`.
The `L¹` version of `ConditioningDownMeasure.simple_model_any`. -/
theorem simple_model_any_L1 {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    (hv : DiscL1 S.μ ρ v) (hs : DiscL1 S.μ ρ s) (hrb : DiscL1 S.μ ρ r)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω +
        (coarsen S 𝓖).innov t (v t) ω := by
  have hg0 : (coarsen S 𝓖).innov t 0 = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov, (coarsen S 𝓖).E_zero,
      (coarsen S 𝓖).E_zero, sub_self]
  filter_upwards [unexpected_inflation_any_L1 (coarsen S 𝓖) hflow hr hv hs (DiscL1.zero _ ρ)
    hrb hrn t, ae_all_iff.2 (innov_return_condDown h hc t)] with ω h1 h2
  rw [h1]
  have e1 : ∑' j, ρ ^ j * (coarsen S 𝓖).innov t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω = 0 := by
    simp [hg0]
  have e2 : ∑' j, ρ ^ (j + 1) * (coarsen S 𝓖).innov t (r (t + 2 + j)) ω = 0 := by
    simp only [h2, Pi.zero_apply, mul_zero, tsum_zero]
  rw [e1, e2]
  ring

/-- Cochrane (2023), eq. (4.2), p. 87 (`Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}`), for the agents, with
integrable processes and any `ρ`: in the simple model with one-period debt and `v_t` known at
`t`, a.e. the discounted surplus news sums to minus unexpected inflation.
The `L¹` version of `ConditioningDownMeasure.simple_model_agents`. -/
theorem simple_model_agents_L1 (S : MeasExpectationSystem Ω) {ρ : ℝ}
    {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    (hvm : StronglyAdapted S.𝓕 v) (hrnm : ∀ t, StronglyMeasurable[S.𝓕 t] (rn (t + 1)))
    (hv : DiscL1 S.μ ρ v) (hs : DiscL1 S.μ ρ s) (hrb : DiscL1 S.μ ρ r)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω)
      (-S.innov t (infl (t + 1)) ω) := by
  have hN : Nested S S.𝓕 := fun _ => le_rfl
  have hk : S.innov t (v t) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 (hv.1 t) ⟨v t, hvm t, ae_eq_refl _⟩
  have hkr : S.innov t (rn (t + 1)) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 (hrn (t + 1)) ⟨rn (t + 1), hrnm t, ae_eq_refl _⟩
  filter_upwards [simple_model_any_L1 hN hflow hr hc hv hs hrb hrn t, hk, hkr,
    summable_innov_L1 S hs t (t + 1)] with ω h1 h2 h3 h4
  change S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
    -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω + S.innov t (v t) ω at h1
  rw [h2, h3, Pi.zero_apply] at h1
  have : -S.innov t (infl (t + 1)) ω = ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω := by linarith
  rw [this]
  exact h4.hasSum

/-- Cochrane (2023), eq. (4.2), p. 87, p. 101 and Online Appendix p. 602, for the econometrician,
with integrable processes and any `ρ`: the book's decomposition with the econometrician's news
holds a.e. **iff** `Δ^I_{t+1} v_t = 0` a.e.
The `L¹` version of `ConditioningDownMeasure.simple_model_econ_iff`. -/
theorem simple_model_econ_iff_L1 {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hflow : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t) {c : ℝ}
    (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    (hv : DiscL1 S.μ ρ v) (hs : DiscL1 S.μ ρ s) (hrb : DiscL1 S.μ ρ r)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω)
      (-((coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω))) ↔
      (coarsen S 𝓖).innov t (v t) =ᵐ[S.μ] 0 := by
  have hid := simple_model_any_L1 h hflow hr hc hv hs hrb hrn t
  have hsum := summable_innov_L1 (coarsen S 𝓖) hs t (t + 1)
  constructor
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [a.tsum_eq] at b
    rw [Pi.zero_apply]
    linarith
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [Pi.zero_apply] at a
    rw [b, a]
    simpa using c.hasSum

/-! ### Every `ρ`, integrable processes: present values iff terminal conditions -/

/-- Cochrane (2023), eq. (3.18), p. 63 (tool): if `a = S_n + b_n` for every `n`, then `S_n → a`
iff `b_n → 0`. -/
theorem tendsto_iff_of_eq {a : ℝ} {S b : ℕ → ℝ} (h : ∀ n, a = S n + b n) :
    Tendsto S atTop (𝓝 a) ↔ Tendsto b atTop (𝓝 0) := by
  have hb : b = fun n => a - S n := funext fun n => by rw [h n]; ring
  have hS : S = fun n => a - b n := funext fun n => by rw [h n]; ring
  constructor
  · intro h1
    rw [hb]
    have := (tendsto_const_nhds (x := a)).sub h1
    rwa [sub_self] at this
  · intro h1
    rw [hS]
    have := (tendsto_const_nhds (x := a)).sub h1
    rwa [sub_zero] at this

omit mΩ in
/-- Cochrane (2023), eq. (3.18), p. 63, for every `ρ` (including `|ρ| = 1`), state by state: under
the recursion `x_t = ρx_{t+1} + f_{t+1}`, the ex-post present value converges to `x_t` iff the
terminal condition `ρᵀx_{t+T} → 0` holds. -/
theorem pv_ex_post_iff_tvc {ρ : ℝ} {x f : ℕ → Ω → ℝ} (hrec : Recursion ρ x f) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j * f (t + 1 + j) ω) (x t ω) ↔
      Tendsto (fun T => ρ ^ T * x (t + T) ω) atTop (𝓝 0) := by
  refine tendsto_iff_of_eq fun T => ?_
  have := congrFun (rec_finite hrec t T) ω
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

/-- Cochrane (2023), eq. (3.19), p. 64 (tool), under ANY information, for every `ρ` and integrable
processes: forward iteration of the forecasts, a.e.
`E_m x_t = ∑_{j<T} ρʲE_m f_{t+1+j} + ρᵀE_m x_{t+T}` for all `T` simultaneously. -/
theorem E_rec_finite (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) (hxi : ∀ t, Integrable (x t) T.μ) (hfi : ∀ t, Integrable (f t) T.μ)
    (t m : ℕ) :
    ∀ᵐ ω ∂T.μ, ∀ n, T.E m (x t) ω = ∑ j ∈ Finset.range n, ρ ^ j * T.E m (f (t + 1 + j)) ω +
      ρ ^ n * T.E m (x (t + n)) ω := by
  rw [ae_all_iff]
  intro n
  have h := rec_finite hrec t n
  have hsi : Integrable (∑ j ∈ Finset.range n, ρ ^ j • f (t + 1 + j)) T.μ :=
    integrable_finsetSum' _ fun j _ => (hfi (t + 1 + j)).smul (ρ ^ j)
  have hsm : ∀ j, T.E m (ρ ^ j • f (t + 1 + j)) =ᵐ[T.μ] ρ ^ j • T.E m (f (t + 1 + j)) :=
    fun j => T.E_smul (ρ ^ j) (f (t + 1 + j)) m
  filter_upwards [T.E_add hsi ((hxi (t + n)).smul (ρ ^ n)) m,
    condExp_finsetSum (μ := T.μ) (m := T.𝓕 m) (s := Finset.range n)
      (fun j _ => (hfi (t + 1 + j)).smul (ρ ^ j)),
    ae_all_iff.2 hsm, T.E_smul (ρ ^ n) (x (t + n)) m] with ω h1 h2 h3 h4
  rw [h]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h4
  rw [h1, h4]
  congr 1
  have h2' : T.E m (∑ j ∈ Finset.range n, ρ ^ j • f (t + 1 + j)) ω =
      ∑ j ∈ Finset.range n, T.E m (ρ ^ j • f (t + 1 + j)) ω :=
    h2.trans (Finset.sum_apply ω _ _)
  rw [h2']
  refine Finset.sum_congr rfl fun j _ => ?_
  have := h3 j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact this

/-- Cochrane (2023), eq. (3.19), p. 64, **for every `ρ`, including `|ρ| = 1`**, under ANY
information and with merely integrable processes: a.e., the discounted forecasts
`∑ρʲE_m f_{t+1+j}` converge (as an ordinary series) to `E_m x_t` iff the forecast terminal
condition `ρᵀE_m x_{t+T} → 0` holds. -/
theorem pv_E_iff_tvc (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) (hxi : ∀ t, Integrable (x t) T.μ) (hfi : ∀ t, Integrable (f t) T.μ)
    (t m : ℕ) :
    ∀ᵐ ω ∂T.μ, (SeriesTo (fun j => ρ ^ j * T.E m (f (t + 1 + j)) ω) (T.E m (x t) ω) ↔
      Tendsto (fun n => ρ ^ n * T.E m (x (t + n)) ω) atTop (𝓝 0)) := by
  filter_upwards [E_rec_finite T hrec hxi hfi t m] with ω h
  exact tendsto_iff_of_eq h

/-- Cochrane (2023), eq. (3.20), p. 65, **for every `ρ`, including `|ρ| = 1`** (the measure
analogue of the core's innovation terminal condition), with integrable processes: a.e.
`∑ρʲΔ_{t+1}f_{t+1+j}` converges to `Δ_{t+1}x_t` iff `ρᵀΔ_{t+1}x_{t+T} → 0`. -/
theorem innov_pv_iff_tvc (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) (hxi : ∀ t, Integrable (x t) T.μ) (hfi : ∀ t, Integrable (f t) T.μ)
    (t : ℕ) :
    ∀ᵐ ω ∂T.μ, (SeriesTo (fun j => ρ ^ j * T.innov t (f (t + 1 + j)) ω) (T.innov t (x t) ω) ↔
      Tendsto (fun n => ρ ^ n * T.innov t (x (t + n)) ω) atTop (𝓝 0)) := by
  filter_upwards [E_rec_finite T hrec hxi hfi t (t + 1), E_rec_finite T hrec hxi hfi t t]
    with ω h1 h2
  refine tendsto_iff_of_eq fun n => ?_
  simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  rw [h1 n, h2 n]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Cochrane (2023), p. 101, and Online Appendix p. 602, **for every `ρ`, including `|ρ| = 1`**,
with the flow identity ex post and integrable processes: (i) a.e. the econometrician's discounted
forecasts of `s̃ + g − r` converge to `E(v_t|I_t)` iff the econometrician's terminal condition
`ρᵀE(v_{t+T}|I_t) → 0` holds; (ii) when that terminal condition holds a.e., they converge to `v_t`
a.e. iff `v_t ∈ I_t`. -/
theorem condDown_flow_iff_tvc {S : MeasExpectationSystem Ω} (𝓖 : Filtration ℕ mΩ) {ρ : ℝ}
    {v r g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hvi : ∀ t, Integrable (v t) S.μ)
    (hfi : ∀ t, Integrable (s t + g t - r t) S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, (SeriesTo (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω) ↔
      Tendsto (fun n => ρ ^ n * (coarsen S 𝓖).E t (v (t + n)) ω) atTop (𝓝 0))) ∧
    ((∀ᵐ ω ∂S.μ, Tendsto (fun n => ρ ^ n * (coarsen S 𝓖).E t (v (t + n)) ω) atTop (𝓝 0)) →
      ((∀ᵐ ω ∂S.μ, SeriesTo (fun j => ρ ^ j * (coarsen S 𝓖).E t
        (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) (v t ω)) ↔
        KnownAE S.μ 𝓖 t (v t))) := by
  have hrec := (flow_iff_recursion ρ v r g s).1 hflow
  have hH := pv_E_iff_tvc (coarsen S 𝓖) hrec hvi hfi t t
  refine ⟨hH, fun htvc => ?_⟩
  have hconv : ∀ᵐ ω ∂S.μ, SeriesTo (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω) := by
    filter_upwards [hH, htvc] with ω a b
    exact a.2 b
  rw [← known_iff_E_eq S 𝓖 (hvi t)]
  constructor
  · intro h1
    filter_upwards [h1, hconv] with ω a b
    exact tendsto_nhds_unique a b
  · intro h1
    filter_upwards [h1, hconv] with ω a b
    rw [a]
    exact b

/-! ### Every `ρ`: convergence in `L¹` -/

/-- Cochrane (2023), eq. (3.19), p. 64, **for every `ρ`**, in `L¹`: under the recursion with
integrable processes, if the terminal condition holds in `L¹` (`E|ρᵀx_{t+T}| → 0`), then the
discounted forecasts converge to `E_m x_t` in `L¹`, under ANY information. -/
theorem pv_E_tendsto_L1 (T : MeasExpectationSystem Ω) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) (hxi : ∀ t, Integrable (x t) T.μ) (hfi : ∀ t, Integrable (f t) T.μ)
    (t m : ℕ) (htvc : Tendsto (fun n => ∫ ω, |ρ ^ n * x (t + n) ω| ∂T.μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |T.E m (x t) ω -
      ∑ j ∈ Finset.range n, ρ ^ j * T.E m (f (t + 1 + j)) ω| ∂T.μ) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) htvc
  have hEq : (fun ω => |T.E m (x t) ω - ∑ j ∈ Finset.range n, ρ ^ j * T.E m (f (t + 1 + j)) ω|)
      =ᵐ[T.μ] fun ω => |ρ| ^ n * |T.E m (x (t + n)) ω| := by
    filter_upwards [E_rec_finite T hrec hxi hfi t m] with ω h
    rw [h n, add_sub_cancel_left, abs_mul, abs_pow]
  rw [integral_congr_ae hEq, integral_const_mul]
  have h2 : ∫ ω, |ρ ^ n * x (t + n) ω| ∂T.μ = |ρ| ^ n * ∫ ω, |x (t + n) ω| ∂T.μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [abs_mul, abs_pow])
  rw [h2]
  exact mul_le_mul_of_nonneg_left (integral_abs_condExp_le _) (pow_nonneg (abs_nonneg _) _)

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101, **for every `ρ`** (the valuation
equation with conditionally convergent present values, e.g. `ρ = 1`), in `L¹`: if the partial
sums `∑_{j<n}ρʲs_{t+1+j}` converge in `L¹` to `X` and `v_t = E(X|Ω_t)`, then the econometrician's
discounted forecasts converge in `L¹` to `E(v_t|I_t)`. -/
theorem condDown_valuation_tendsto_L1 {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} {s : ℕ → Ω → ℝ} (hsi : ∀ j, Integrable (s j) S.μ) {t : ℕ}
    {X : Ω → ℝ} (hXi : Integrable X S.μ)
    (hX : Tendsto (fun n => ∫ ω, |∑ j ∈ Finset.range n, ρ ^ j * s (t + 1 + j) ω - X ω| ∂S.μ)
      atTop (𝓝 0)) {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    Tendsto (fun n => ∫ ω, |∑ j ∈ Finset.range n, ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω -
      (coarsen S 𝓖).E t v ω| ∂S.μ) atTop (𝓝 0) := by
  set G := coarsen S 𝓖
  refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hX
  set P : Ω → ℝ := fun ω => ∑ j ∈ Finset.range n, ρ ^ j * s (t + 1 + j) ω with hP
  have hPs : P = ∑ j ∈ Finset.range n, ρ ^ j • s (t + 1 + j) := by
    funext ω
    simp [hP, Finset.sum_apply]
  have hPi : Integrable P S.μ := by
    rw [hPs]
    exact integrable_finsetSum' _ fun j _ => (hsi (t + 1 + j)).smul (ρ ^ j)
  have hEP : G.E t P =ᵐ[S.μ] fun ω => ∑ j ∈ Finset.range n, ρ ^ j * G.E t (s (t + 1 + j)) ω := by
    rw [hPs]
    filter_upwards [condExp_finsetSum (μ := S.μ) (m := 𝓖 t) (s := Finset.range n)
      (fun j _ => (hsi (t + 1 + j)).smul (ρ ^ j)),
      ae_all_iff.2 fun j => G.E_smul (ρ ^ j) (s (t + 1 + j)) t] with ω h1 h2
    have h1' : G.E t (∑ j ∈ Finset.range n, ρ ^ j • s (t + 1 + j)) ω =
        ∑ j ∈ Finset.range n, G.E t (ρ ^ j • s (t + 1 + j)) ω :=
      h1.trans (Finset.sum_apply ω _ _)
    rw [h1']
    refine Finset.sum_congr rfl fun j _ => ?_
    have := h2 j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hEq : (fun ω => |∑ j ∈ Finset.range n, ρ ^ j * G.E t (s (t + 1 + j)) ω - G.E t v ω|)
      =ᵐ[S.μ] fun ω => |G.E t (P - X) ω| := by
    filter_upwards [hEP, G.E_sub hPi hXi t, condDown_general h hv] with ω h1 h2 h3
    rw [h2, Pi.sub_apply, h1, h3]
  rw [integral_congr_ae hEq]
  exact integral_abs_condExp_le _

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101 ("so long as `v_t ∈ I_t`"), **for
every `ρ`**, in `L¹`: under the hypotheses of `condDown_valuation_tendsto_L1`, the
econometrician's discounted forecasts converge in `L¹` to `v_t` **iff** `v_t ∈ I_t`. -/
theorem condDown_valuation_tendsto_L1_iff {S : MeasExpectationSystem Ω}
    {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖) {ρ : ℝ} {s : ℕ → Ω → ℝ}
    (hsi : ∀ j, Integrable (s j) S.μ) {t : ℕ} {X : Ω → ℝ} (hXi : Integrable X S.μ)
    (hX : Tendsto (fun n => ∫ ω, |∑ j ∈ Finset.range n, ρ ^ j * s (t + 1 + j) ω - X ω| ∂S.μ)
      atTop (𝓝 0)) {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    Tendsto (fun n => ∫ ω, |∑ j ∈ Finset.range n, ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω -
      v ω| ∂S.μ) atTop (𝓝 0) ↔ KnownAE S.μ 𝓖 t v := by
  set G := coarsen S 𝓖
  have hvi : Integrable v S.μ := (S.integrable_E t X).congr hv.symm
  have hEv := condDown_valuation_tendsto_L1 h hsi hXi hX hv
  rw [← known_iff_E_eq S 𝓖 hvi]
  set Q : ℕ → Ω → ℝ := fun n ω => ∑ j ∈ Finset.range n, ρ ^ j * G.E t (s (t + 1 + j)) ω
  have hQi : ∀ n, Integrable (Q n) S.μ := fun n => by
    have hQs : Q n = ∑ j ∈ Finset.range n, ρ ^ j • G.E t (s (t + 1 + j)) := by
      funext ω
      simp [Q, Finset.sum_apply]
    rw [hQs]
    exact integrable_finsetSum' _ fun j _ => (G.integrable_E t (s (t + 1 + j))).smul (ρ ^ j)
  have hGi : Integrable (G.E t v) S.μ := G.integrable_E t v
  constructor
  · intro h1
    have hle : ∀ n, ∫ ω, |v ω - G.E t v ω| ∂S.μ ≤
        ∫ ω, |Q n ω - v ω| ∂S.μ + ∫ ω, |Q n ω - G.E t v ω| ∂S.μ := fun n => by
      refine le_trans (integral_mono (hvi.sub hGi).abs
        (((hQi n).sub hvi).abs.add ((hQi n).sub hGi).abs) fun ω => ?_)
        (le_of_eq (integral_add ((hQi n).sub hvi).abs ((hQi n).sub hGi).abs))
      calc |v ω - G.E t v ω| = |(Q n ω - G.E t v ω) - (Q n ω - v ω)| := by ring_nf
        _ ≤ |Q n ω - G.E t v ω| + |Q n ω - v ω| := abs_sub _ _
        _ = _ := add_comm _ _
    have hlim := h1.add hEv
    rw [add_zero] at hlim
    have h0 : ∫ ω, |v ω - G.E t v ω| ∂S.μ ≤ 0 :=
      ge_of_tendsto hlim (Eventually.of_forall hle)
    have h00 : ∫ ω, |v ω - G.E t v ω| ∂S.μ = 0 :=
      le_antisymm h0 (integral_nonneg fun _ => abs_nonneg _)
    have hz := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) (hvi.sub hGi).abs).1 h00
    filter_upwards [hz] with ω hω
    have : |v ω - G.E t v ω| = 0 := hω
    linarith [abs_eq_zero.1 this]
  · intro h1
    refine hEv.congr fun n => integral_congr_ae ?_
    filter_upwards [h1] with ω hω
    rw [← hω]

/-! ### `|ρ| = 1` -/

/-- Cochrane (2023), eq. (3.18), p. 63, at `|ρ| = 1`, **counterexample**: the bounded-process
statements of `ConditioningDownMeasure` (`ConditioningDownMeasure.pv_ex_post`,
`ConditioningDownMeasure.pv_E`, `ConditioningDownMeasure.condDown_flow_iff`) need `|ρ| < 1`.
With `ρ = ±1`, `x_t = ρᵗ` and no payoff, the recursion holds and `x` is bounded, but neither the
ex-post nor the forecast present value equals `x_0 = 1`; and `x` is not `DiscL1`. -/
theorem pv_unit_root_fails (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| = 1)
    (m : ℕ) :
    Recursion ρ (fun t (_ : Ω) => ρ ^ t) (fun _ _ => 0) ∧ (∀ t, |ρ ^ t| ≤ 1) ∧
    ¬ (∀ᵐ _ω ∂T.μ, HasSum (fun j => ρ ^ j * (0 : ℝ)) (ρ ^ 0)) ∧
    ¬ (∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.E m (fun _ => (0 : ℝ)) ω)
      (T.E m (fun _ => ρ ^ 0) ω)) ∧
    ¬ DiscL1 T.μ ρ (fun t (_ : Ω) => ρ ^ t) := by
  have hρ2 : ρ ^ 2 = 1 := by rw [← sq_abs, hρ, one_pow]
  have hnot : ¬ HasSum (fun j => ρ ^ j * (0 : ℝ)) (ρ ^ 0) := by
    intro h
    have h0 : HasSum (fun j : ℕ => ρ ^ j * (0 : ℝ)) 0 := by
      simp only [mul_zero]
      exact hasSum_zero
    have := h.unique h0
    simp at this
  refine ⟨fun t => ?_, fun t => by rw [abs_pow, hρ, one_pow], fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero]
    rw [show ρ * ρ ^ (t + 1) = ρ ^ t * ρ ^ 2 by ring, hρ2, mul_one]
  · obtain ⟨ω, hω⟩ := h.exists
    exact hnot hω
  · obtain ⟨ω, hω⟩ := h.exists
    rw [T.E_const, T.E_const] at hω
    exact hnot hω
  · have h1 := h.2 0
    simp only [zero_add, abs_pow, hρ, one_pow, one_mul, integral_const, smul_eq_mul,
      mul_one] at h1
    have h2 : (T.μ.real Set.univ) = 1 := by simp
    rw [h2] at h1
    exact (summable_const_iff (1 : ℝ)).not.mpr one_ne_zero h1

/-- Cochrane (2023), p. 101 and Online Appendix p. 602, **the corrected statement at `|ρ| = 1`**
(`ρ = ±1`): with the flow identity ex post and `∑_t E|v_t| < ∞`, `∑_t E|s̃_t + g_t − r_t| < ∞`
(integrable, not necessarily bounded), the econometrician's discounted forecasts sum to
`E(v_t|I_t)`, and to `v_t` iff `v_t ∈ I_t`. -/
theorem condDown_flow_unit_root {S : MeasExpectationSystem Ω} (𝓖 : Filtration ℕ mΩ) {ρ : ℝ}
    (hρ : |ρ| = 1) {v r g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s)
    (hvi : ∀ t, Integrable (v t) S.μ) (hvs : Summable fun t => ∫ ω, |v t ω| ∂S.μ)
    (hfi : ∀ t, Integrable (s t + g t - r t) S.μ)
    (hfs : Summable fun t => ∫ ω, |(s t + g t - r t) ω| ∂S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω)) ∧
    ((∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) (v t ω)) ↔ KnownAE S.μ 𝓖 t (v t)) :=
  condDown_flow_iff_L1 𝓖 hflow (DiscL1.of_summable hρ.le hvi hvs)
    (DiscL1.of_summable hρ.le hfi hfs) t

end Cochrane.DebtDeficitsInflation.TidyR6ConditioningDownL1
