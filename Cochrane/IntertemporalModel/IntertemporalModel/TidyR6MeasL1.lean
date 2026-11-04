/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasFiscal

/-!
# Integrable surpluses: the equilibrium results without bounded surpluses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23 ((2.4)–(2.7)),
§2.4, pp. 29–33, §2.7, pp. 42–43 (AR(1) surpluses, the s-shape) and §2.9, p. 48 ((2.28), the
two-step process), on a probability space (`MeasExpectationSystem`).

The results of `TidyR5Meas` and `TidyR6MeasFiscal` that pass `E_t` through an infinite sum
assumed surpluses bounded almost surely. Here that hypothesis is replaced by the natural one,
`SurplusL1`: every `s_t` is integrable and `∑ⱼ |β|ʲ E|s_{k+j}| < ∞` from every date on. The key
tool is that conditional expectations commute with `L¹`-summable series (`E_hasSum_L1`, with
`ae_summable_abs`, restated from the DebtDeficitsInflation project, where it is
TidyR6ConditioningDownL1.E_hasSum_L1, from Mathlib's `condExp_tsum`).

## Main results

* Tools: `ae_summable_abs`, `E_hasSum_L1`, `SurplusL1` with `SurplusL1.of_bdd` (bounded
  surpluses and `|β| < 1`) and `SurplusL1.of_integral_bdd` (surpluses bounded in `L¹`).
* Present values: `E_shift_hasSum`, `forwardSol_hasSum_L1`, `forwardSol_solves_L1`,
  `pv_eq_add_pvEx_L1`, `tail_tendsto_L1`.
* The two notions: `mFlowTvc_iff_valuation_L1`, `mEquilibrium_iff_mIsEqm_L1` (both directions);
  `Junk.l1_needed`: without the summability the ⇐ direction fails (point mass, `s_t = 2ᵗ`,
  `β = 1/2`: the present value is a junk `tsum`).
* `mFlow_L1` ((2.4)/(2.26)), `mTreasury_rule_L1` ((2.28)), `mTwoStep_eq_pegP_L1`,
  `mTwoStep_debt_L1`, `mTwoStep_equilibrium_L1`.
* AR(1): `ar1_E_L1`, `mAr1_pv_L1`, `mAr1_pv_news_L1`, `mAr1_unexpected_inflation_L1`,
  `mAr1_printed_fails_L1`, `mAr1_value_news_L1`, `mAr1_value_falls_L1`.
* The s-shape: `mNews_pv_tsum_L1`, `mSShape_L1`.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasL1

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Series of integrable random variables (restated from the DebtDeficitsInflation
project) -/

/-- Cochrane (2023), eq. (2.7), p. 22 (tool, restated from the DebtDeficitsInflation project):
for an integrable real variable, `∫⁻ ‖g‖ₑ = ENNReal.ofReal (E|g|)`.
Original: DebtDeficitsInflation TidyR6ConditioningDownL1.lintegral_enorm_eq. -/
theorem lintegral_enorm_eq {μ : Measure Ω} {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫⁻ ω, ‖g ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, |g ω| ∂μ) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hg]
  simp only [Real.norm_eq_abs]

/-- Cochrane (2023), eq. (2.7), p. 22 (tool, restated from the DebtDeficitsInflation project):
`∑_j E|g_j| < ∞` in extended form.
Original: DebtDeficitsInflation TidyR6ConditioningDownL1.tsum_lintegral_ne_top. -/
theorem tsum_lintegral_ne_top {μ : Measure Ω} {g : ℕ → Ω → ℝ} (hi : ∀ j, Integrable (g j) μ)
    (hs : Summable fun j => ∫ ω, |g j ω| ∂μ) : ∑' j, ∫⁻ ω, ‖g j ω‖ₑ ∂μ ≠ ⊤ := by
  simp_rw [lintegral_enorm_eq (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun _ => abs_nonneg _) hs]
  exact ENNReal.ofReal_ne_top

/-- Cochrane (2023), eq. (2.7), p. 22 (tool, restated from the DebtDeficitsInflation project):
if `∑_j E|g_j| < ∞`, then `∑_j |g_j|` converges almost surely.
Original: DebtDeficitsInflation TidyR6ConditioningDownL1.ae_summable_abs. -/
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

/-- Cochrane (2023), eq. (2.7), p. 22 (restated from the DebtDeficitsInflation project,
TidyR6ConditioningDownL1.E_hasSum_L1): **conditional expectations commute with
`L¹`-summable series**: if the `g_j` are integrable with `∑_j E|g_j| < ∞`, then almost surely
`∑_j E_m g_j = E_m ∑_j g_j`, a genuine `HasSum`. -/
theorem E_hasSum_L1 {g : ℕ → Ω → ℝ} (hi : ∀ j, Integrable (g j) S.μ)
    (hs : Summable fun j => ∫ ω, |g j ω| ∂S.μ) (m : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => S.E m (g j) ω) (S.E m (fun ω' => ∑' j, g j ω') ω) := by
  have hc := condExp_tsum (μ := S.μ) (m := S.𝓕 m) (fun j => (hi j).aestronglyMeasurable)
    (tsum_lintegral_ne_top hi hs)
  have hsE : Summable fun j => ∫ ω, |S.E m (g j) ω| ∂S.μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_abs_condExp_le _) hs
  filter_upwards [hc, ae_summable_abs (fun j => S.integrable_E m (g j)) hsE] with ω h1 h2
  have h3 : S.E m (fun ω' => ∑' j, g j ω') ω = ∑' j, S.E m (g j) ω := h1
  rw [h3]
  exact (Summable.of_norm (by simpa [Real.norm_eq_abs] using h2)).hasSum

/-! ### Integrable surpluses -/

/-- Cochrane (2023), eq. (2.7), p. 22 (the present value must be a genuine sum): every surplus is
integrable and the discounted `L¹` norms are summable from every date on,
`∑ⱼ |β|ʲ E|s_{k+j}| < ∞`. -/
def SurplusL1 (β : ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (s t) S.μ) ∧ ∀ k, Summable fun j => |β| ^ j * ∫ ω, |s (k + j) ω| ∂S.μ

variable {S} {β : ℝ} {s : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.7), p. 22: for `|β| < 1`, surpluses bounded in `L¹` are
`SurplusL1`. -/
theorem SurplusL1.of_integral_bdd (hβ : |β| < 1) (hi : ∀ t, Integrable (s t) S.μ) {K : ℝ}
    (hK : ∀ t, ∫ ω, |s t ω| ∂S.μ ≤ K) : SurplusL1 S β s :=
  ⟨hi, fun k => Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (pow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => abs_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left (hK (k + j)) (pow_nonneg (abs_nonneg _) _))
    ((summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right K)⟩

/-- Cochrane (2023), eq. (2.7), p. 22: for `|β| < 1`, measurable surpluses bounded almost surely
are `SurplusL1` (so every bounded statement is a special case). -/
theorem SurplusL1.of_bdd (hβ : |β| < 1) (hm : ∀ t, AEStronglyMeasurable (s t) S.μ) {K : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ K) : SurplusL1 S β s := by
  have hi : ∀ t, Integrable (s t) S.μ := fun t =>
    Integrable.of_bound (hm t) K ((hb t).mono fun ω h => by rwa [Real.norm_eq_abs])
  refine SurplusL1.of_integral_bdd hβ hi (K := K) fun t => ?_
  calc ∫ ω, |s t ω| ∂S.μ ≤ ∫ _, K ∂S.μ :=
        integral_mono_ae (hi t).abs (integrable_const K) (hb t)
    _ = K := by simp

/-- Cochrane (2023), eq. (2.7), p. 22 (tool): the discounted terms have summable `L¹` norms. -/
theorem SurplusL1.summable_integral (hs : SurplusL1 S β s) (k : ℕ) :
    Summable fun j => ∫ ω, |β ^ j * s (k + j) ω| ∂S.μ :=
  (hs.2 k).congr fun j => by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [abs_mul, abs_pow])

/-! ### Present values of integrable surpluses -/

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space with integrable surpluses: for every
dates `m` and `n`, almost surely `∑ₖ βᵏ E_m s_{n+k} = E_m ∑ₖ βᵏ s_{n+k}` (a genuine
`HasSum`). -/
theorem E_shift_hasSum (hs : SurplusL1 S β s) (m n : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k * S.E m (s (n + k)) ω)
      (S.E m (MeasExpectationSystem.discSum β s n) ω) := by
  have hE := E_hasSum_L1 S (g := fun k ω => β ^ k * s (n + k) ω)
    (fun _ => (hs.1 _).const_mul _) (hs.summable_integral n) m
  have hsmul : ∀ k, S.E m (fun ω => β ^ k * s (n + k) ω) =ᵐ[S.μ]
      fun ω => β ^ k * S.E m (s (n + k)) ω := fun k => S.E_smul (β ^ k) (s (n + k)) m
  filter_upwards [hE, ae_all_iff.2 hsmul] with ω h1 h2
  exact h1.congr_fun fun k => (h2 k).symm

/-- Cochrane (2023), eq. (2.7), p. 22, with integrable surpluses: the present value is the genuine
forward sum `PV_t = ∑ₖ βᵏ E_t s_{t+k}` almost surely.
Generalises `TidyR6MeasHyp.forwardSol_hasSum_dom` and
`ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum`. -/
theorem forwardSol_hasSum_L1 (hs : SurplusL1 S β s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k * S.E t (s (t + k)) ω) (S.forwardSol β s t ω) :=
  E_shift_hasSum hs t t

/-- Cochrane (2023), eq. (2.26), p. 42, with integrable adapted surpluses: the present value
solves `PV_t = s_t + β E_t PV_{t+1}` almost surely.
Generalises `ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves`. -/
theorem forwardSol_solves_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s) :
    S.Solves β s (S.forwardSol β s) := by
  intro t
  have hk : S.E t (s t) = s t := S.E_of_stronglyMeasurable (hsad t) (hs.1 t)
  filter_upwards [forwardSol_hasSum_L1 hs t, E_shift_hasSum hs t (t + 1),
    S.E_tower (Nat.le_succ t) (MeasExpectationSystem.discSum β s (t + 1))] with ω h1 h2 h3
  have h3' : S.E t (S.forwardSol β s (t + 1)) ω =
      S.E t (MeasExpectationSystem.discSum β s (t + 1)) ω := h3
  have h4 : HasSum (fun k => β ^ k * S.E t (s (t + k)) ω)
      (s t ω + β * S.E t (MeasExpectationSystem.discSum β s (t + 1)) ω) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have h5 := h2.mul_left β
    rw [Finset.sum_range_one, pow_zero, one_mul, add_zero, hk, add_sub_cancel_left]
    convert h5 using 1
    funext k
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3', h1.unique h4]
  ring

/-- Cochrane (2023), eq. (2.26), p. 42, with integrable adapted surpluses:
`PV_t = s_t + PVex_t` almost surely.
Generalises `TidyR5Meas.pv_eq_add_pvEx`. -/
theorem pv_eq_add_pvEx_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s) (t : ℕ) :
    S.forwardSol β s t =ᵐ[S.μ] s t + pvExM S β s t := by
  filter_upwards [forwardSol_solves_L1 hsad hs t] with ω h
  rw [h, Pi.add_apply, Pi.add_apply]
  simp only [pvExM, Pi.smul_apply]
  ring

/-- Cochrane (2023), eq. (2.6), p. 22, with integrable surpluses: the discounted forecast of a
distant present value vanishes, `β^N E_t PV_{t+N} → 0` almost surely. -/
theorem tail_tendsto_L1 (hs : SurplusL1 S β s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (S.forwardSol β s (t + N)) ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂S.μ, ∀ N, S.E t (S.forwardSol β s (t + N)) ω =
      ∑' k, β ^ k * S.E t (s (t + N + k)) ω := ae_all_iff.2 fun N => by
    filter_upwards [S.E_tower (Nat.le_add_right t N)
      (MeasExpectationSystem.discSum β s (t + N)), E_shift_hasSum hs t (t + N)] with ω h1 h2
    have h1' : S.E t (S.forwardSol β s (t + N)) ω =
        S.E t (MeasExpectationSystem.discSum β s (t + N)) ω := h1
    rw [h1', h2.tsum_eq]
  filter_upwards [hall] with ω h
  have e : ∀ N, β ^ N * S.E t (S.forwardSol β s (t + N)) ω =
      ∑' k, (fun j => β ^ j * S.E t (s (t + j)) ω) (k + N) := fun N => by
    rw [h N, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    change β ^ N * (β ^ k * S.E t (s (t + N + k)) ω) = β ^ (k + N) * S.E t (s (t + (k + N))) ω
    rw [show t + (k + N) = t + N + k by omega, pow_add]
    ring
  exact (tendsto_sum_nat_add (fun j => β ^ j * S.E t (s (t + j)) ω)).congr fun N => (e N).symm

/-! ### The two equilibrium notions with integrable surpluses -/

variable {B P i : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ}

/-- Cochrane (2023), eqs. (2.4)–(2.7), p. 22, on a probability space, **both directions, with
integrable surpluses** (`TidyR5Meas.mFlowTvc_iff_valuation` with `SurplusL1` in place of
bounded surpluses): the nominal flow condition (2.4) and the transversality condition (2.6) hold
almost surely at every date iff the valuation equation (2.7) does. -/
theorem mFlowTvc_iff_valuation_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    {Bm Q : ℕ → Ω → ℝ} (hPa : StronglyAdapted S.𝓕 P)
    (hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (Bm (t + 1))) (hP : ∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω)
    (hQ : ∀ t, Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω))
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => Bm t ω / P t ω) S.μ) :
    ((∀ t, ∀ᵐ ω ∂S.μ, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω)
        atTop (𝓝 0)) ↔
      ∀ t, (fun ω => Bm t ω / P t ω) =ᵐ[S.μ] S.forwardSol β s t := by
  rw [nominal_iff_real S hPa hBm hP hQ hPP hx]
  constructor
  · rintro ⟨hflow, htvc⟩ t
    have htel := ae_all_iff.2 (HouseholdMeasureTVC.telescope_ae hflow hsad hs.1 t)
    filter_upwards [htel, htvc t, forwardSol_hasSum_L1 hs t] with ω h1 h2 h3
    have hlim1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
        atTop (𝓝 (S.forwardSol β s t ω)) :=
      h3.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have h2' : Tendsto (fun N => β ^ (N + 1) *
        S.E t (fun ω => Bm (t + N + 1) ω / P (t + N + 1) ω) ω) atTop (𝓝 0) :=
      h2.comp (tendsto_add_atTop_nat 1)
    have hlim2 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
        atTop (𝓝 (Bm t ω / P t ω)) := by
      have e : ∀ N, ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω =
          Bm t ω / P t ω - β ^ (N + 1) *
            S.E t (fun ω => Bm (t + N + 1) ω / P (t + N + 1) ω) ω := fun N => by
        rw [h1 N]
        ring
      simp_rw [e]
      simpa using (tendsto_const_nhds (x := Bm t ω / P t ω)).sub h2'
    exact tendsto_nhds_unique hlim2 hlim1
  · intro hv
    have hflow : ∀ t, (fun ω => Bm t ω / P t ω) =ᵐ[S.μ]
        s t + β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := fun t => by
      filter_upwards [hv t, forwardSol_solves_L1 hsad hs t, S.E_congr (hv (t + 1)) t]
        with ω h1 h2 h3
      rw [h1, h2, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, h3]
      ring
    refine ⟨hflow, fun t => ?_⟩
    have hE : ∀ᵐ ω ∂S.μ, ∀ N, S.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω =
        S.E t (S.forwardSol β s (t + N)) ω :=
      ae_all_iff.2 fun N => S.E_congr (hv (t + N)) t
    filter_upwards [hE, tail_tendsto_L1 hs t] with ω h1 h2
    simp_rw [h1]
    exact h2

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space, **with integrable
surpluses**: `MEquilibrium` is exactly `MIsEqm` together with adapted debt and rate, integrable
`P_t/P_{t+1}` and integrable real debt (`TidyR6MeasHyp.mEquilibrium_iff_mIsEqm_reg` with
`SurplusL1` in place of bounded surpluses; no bound on surpluses and no `β < 1`). -/
theorem mEquilibrium_iff_mIsEqm_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s) :
    MEquilibrium S β Bm1 s B P i ↔
      MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹) ∧
        StronglyAdapted S.𝓕 B ∧ StronglyAdapted S.𝓕 i ∧
        (∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ) ∧
        ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ := by
  constructor
  · intro h
    have hx := TidyR6MeasHyp.mEqm_realDebt_integrable S h
    have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (GeneralLinks.debtPath Bm1 B (t + 1)) := h.2.2.1
    obtain ⟨hPa, hP, hBa, hia, hPP, ⟨hv0, hv⟩, hbp⟩ := h
    have hval : ∀ t, (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) =ᵐ[S.μ]
        S.forwardSol β s t := fun t => by
      cases t with
      | zero => exact hv0
      | succ t => exact hv t
    obtain ⟨hflow, htvc⟩ :=
      (mFlowTvc_iff_valuation_L1 hsad hs hPa hBm hP hbp hPP hx).mpr hval
    exact ⟨⟨hP, hPa, hbp, hflow, htvc⟩, hBa, hia, hPP, hx⟩
  · rintro ⟨⟨hP, hPa, hbp, hflow, htvc⟩, hBa, hia, hPP, hx⟩
    have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (GeneralLinks.debtPath Bm1 B (t + 1)) := hBa
    have hval := (mFlowTvc_iff_valuation_L1 hsad hs hPa hBm hP hbp hPP hx).mp ⟨hflow, htvc⟩
    exact ⟨hPa, hP, hBa, hia, hPP, ⟨hval 0, fun t => hval (t + 1)⟩, hbp⟩

/-! ### The summability is needed -/

namespace Junk

open TidyR6MeasHyp.PointMass

/-- Cochrane (2023), eq. (2.7), p. 22: surpluses `s_t = 2ᵗ`, integrable at every date (in the
point-mass economy) but with no convergent present value at `β = 1/2`. -/
def sGrow : ℕ → Bool → ℝ := fun t _ => 2 ^ t

/-- Cochrane (2023), eq. (2.7), p. 22, counterexample: at `β = 1/2` the "present value" of
`s_t = 2ᵗ` (a junk `tsum`, `0`) is not `SurplusL1`, and it violates the recursion
`PV_t = s_t + β E_t PV_{t+1}`; hence the valuation equation `x = PV` holds for `x = PV` while the
flow condition fails, so the ⇐ direction of `mFlowTvc_iff_valuation_L1` needs the summability. -/
theorem l1_needed :
    (∀ t, Integrable (sGrow t) ptSystem.μ) ∧ ¬ SurplusL1 ptSystem (1 / 2) sGrow ∧
      (∀ t, ptSystem.forwardSol (1 / 2) sGrow t = 0) ∧
      ¬ ptSystem.Solves (1 / 2) sGrow (ptSystem.forwardSol (1 / 2) sGrow) := by
  have hd : ∀ t, MeasExpectationSystem.discSum (1 / 2 : ℝ) sGrow t = 0 := fun t => by
    funext ω
    simp only [MeasExpectationSystem.discSum, sGrow, Pi.zero_apply]
    have e : (fun k : ℕ => (1 / 2 : ℝ) ^ k * 2 ^ (t + k)) = fun _ => 2 ^ t := by
      funext k
      rw [pow_add, ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ k), mul_assoc, ← mul_pow]
      norm_num
    rw [e]
    exact tsum_eq_zero_of_not_summable ((summable_const_iff _).not.mpr (by positivity))
  have hpv : ∀ t, ptSystem.forwardSol (1 / 2) sGrow t = 0 := fun t => by
    change ptSystem.E t _ = 0
    rw [hd t, ptSystem.E_zero]
  refine ⟨fun t => integrable_const _, fun h => ?_, hpv, fun h => ?_⟩
  · have h1 := h.2 0
    have e : (fun j : ℕ => |(1 / 2 : ℝ)| ^ j * ∫ ω, |sGrow (0 + j) ω| ∂ptSystem.μ) =
        fun _ => 1 := by
      funext j
      change |(1 / 2 : ℝ)| ^ j * ∫ ω, |sGrow (0 + j) ω| ∂(Measure.dirac true) = 1
      rw [integral_dirac]
      simp only [sGrow, zero_add]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ j), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        ← mul_pow]
      norm_num
    rw [e] at h1
    exact one_ne_zero ((summable_const_iff _).mp h1)
  · have h0 := ae_pt.mp (h 0)
    rw [hpv 0, hpv 1] at h0
    simp [sGrow] at h0

end Junk

/-! ### (2.4)/(2.26), the Treasury rule and the two-step process -/

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42, on a probability space **with integrable
surpluses** (`TidyR5Meas.mFlow` without bounded surpluses or `β < 1`): in every equilibrium
`B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1})` almost surely (`β > 0`, positive present
values). -/
theorem mFlow_L1 (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (h : MEquilibrium S β Bm1 s B P i) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) :
    ∀ᵐ ω ∂S.μ, B t ω / P (t + 1) ω =
      s (t + 1) ω + B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ := by
  filter_upwards [h.2.2.2.2.2.1.2 t, pv_eq_add_pvEx_L1 hsad hs (t + 1),
    mDebt_eq S hβ0 h (t + 1) (hpv (t + 2)), h.2.1 (t + 1),
    mEqm_rate_gt S hβ0 h (t + 1)] with ω h1 h2 h3 h4 h5
  have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
  rw [e1, h2, Pi.add_apply, h3]
  have := h4.ne'
  have : 1 + i (t + 1) ω ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), eq. (2.28), p. 48, **with integrable surpluses**: in every equilibrium the
debt sold follows the Treasury rule `B_{t+1} = (B_t − P_{t+1} s_{t+1})(1 + i_{t+1})` almost
surely.
Generalises `TidyR6MeasFiscal.mTreasury_rule`. -/
theorem mTreasury_rule_L1 (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (h : MEquilibrium S β Bm1 s B P i) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) :
    B (t + 1) =ᵐ[S.μ] fun ω => (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  filter_upwards [mFlow_L1 hβ0 hsad hs h hpv t, h.2.1 (t + 1),
    mEqm_rate_gt S hβ0 h (t + 1)] with ω h1 h2 h3
  have hi : 1 + i (t + 1) ω ≠ 0 := by linarith
  have hP := h2.ne'
  have h4 : B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ =
      B t ω / P (t + 1) ω - s (t + 1) ω := by linarith
  have key : B (t + 1) ω = (B t ω / P (t + 1) ω - s (t + 1) ω) * (1 + i (t + 1) ω) *
      P (t + 1) ω := by
    rw [← h4, mul_assoc (B (t + 1) ω / P (t + 1) ω), inv_mul_cancel₀ hi, mul_one,
      div_mul_cancel₀ _ hP]
  rw [key, show (B t ω / P (t + 1) ω - s (t + 1) ω) * (1 + i (t + 1) ω) * P (t + 1) ω =
    (B t ω / P (t + 1) ω * P (t + 1) ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) by
    ring, div_mul_cancel₀ _ hP]

/-- Cochrane (2023), §2.9, p. 48, **with integrable surpluses**: the two-step process produces the
interest-rate-target price level, `D_t/PV_t = mPegP_t` almost surely.
Generalises `TidyR6MeasFiscal.mTwoStep_eq_pegP`. -/
theorem mTwoStep_eq_pegP_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ) :
    (fun ω => TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) =ᵐ[S.μ]
      mPegP S β Bm1 s i t := by
  induction t with
  | zero => exact Eventually.of_forall fun ω => rfl
  | succ t ih =>
    filter_upwards [ih, pv_eq_add_pvEx_L1 hsad hs t, hpv t] with ω h1 h2 h3
    change (TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω -
      TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω * s t ω) * (1 + i t ω) /
        S.forwardSol β s (t + 1) ω = (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
          S.forwardSol β s (t + 1) ω
    have h1' : TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω =
      mPegP S β Bm1 s i t ω := h1
    have h2' : S.forwardSol β s t ω = s t ω + pvExM S β s t ω := by
      rw [h2, Pi.add_apply]
    rw [← h1']
    congr 1
    have := h3.ne'
    rw [show pvExM S β s t ω = S.forwardSol β s t ω - s t ω by linarith]
    field_simp

/-- Cochrane (2023), §2.9, p. 48, **with integrable surpluses**: the debt the Treasury sells in
the two-step process is the target debt almost surely.
Generalises `TidyR6MeasFiscal.mTwoStep_debt`. -/
theorem mTwoStep_debt_L1 (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ) :
    TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1) =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  filter_upwards [mTwoStep_eq_pegP_L1 (Bm1 := Bm1) (i := i) hsad hs hpv (t + 1), hpv (t + 1)]
    with ω h1 h2
  have h1' : TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1) ω / S.forwardSol β s (t + 1) ω =
      (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω / S.forwardSol β s (t + 1) ω := h1
  exact (div_left_inj' h2.ne').mp h1'

/-- Cochrane (2023), §2.9, p. 48, **with integrable surpluses**: under the hypotheses of
`TidyR6MeasHyp.mPeg_equilibrium_pos` the two-step process is an equilibrium with the target.
Generalises `TidyR6MeasFiscal.mTwoStep_equilibrium`. -/
theorem mTwoStep_equilibrium_L1 (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) :
    MEquilibrium S β Bm1 s (fun t => TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1))
      (fun t ω => TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) i :=
  TidyR5MeasFamily.mEquilibrium_congr S
    (TidyR6MeasHyp.mPeg_equilibrium_pos S hβ0 hBm1 hB hia hi hQi hpv)
    (fun t => ((TidyR6MeasFiscal.mTwoStep_sm S hBm1 hsad hia t).1.measurable.div
      (S.forwardSol_adapted β s t).measurable).stronglyMeasurable)
    (fun t => (TidyR6MeasFiscal.mTwoStep_sm S hBm1 hsad hia t).2)
    (fun t => mTwoStep_eq_pegP_L1 hsad hs hpv t)
    (fun t => mTwoStep_debt_L1 hsad hs hpv t)

/-! ### AR(1) surpluses with integrable shocks -/

variable {η : ℝ} {e : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 43, on a probability space, **with integrable surpluses**: for an adapted
integrable AR(1) `s_{t+1} = η s_t + e_{t+1}` with `E_t e_{t+1} = 0` a.s.,
`E_t s_{t+j} = ηʲ s_t` almost surely.
Generalises `ExpectationsMeasure.MeasExpectationSystem.ar1_E`. -/
theorem ar1_E_L1 (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hsad : StronglyAdapted S.𝓕 s)
    (hsi : ∀ t, Integrable (s t) S.μ) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (t j : ℕ) :
    S.E t (s (t + j)) =ᵐ[S.μ] η ^ j • s t := by
  have hεi : ∀ u, Integrable (e (u + 1)) S.μ := fun u => by
    have h : e (u + 1) = s (u + 1) - η • s u := by rw [hrec u, add_sub_cancel_left]
    rw [h]
    exact (hsi _).sub ((hsi u).smul η)
  induction j with
  | zero => rw [add_zero, pow_zero, one_smul, S.E_of_stronglyMeasurable (hsad t) (hsi t)]
  | succ j ih =>
    have e1 : s (t + (j + 1)) = η • s (t + j) + e (t + j + 1) := hrec (t + j)
    have hz : S.E t (e (t + j + 1)) =ᵐ[S.μ] 0 := by
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (e (t + j + 1))).symm,
        S.E_congr (hmd (t + j)) t] with ω h1 h2
      rw [h1, h2, S.E_zero]
    rw [e1]
    filter_upwards [S.E_add ((hsi _).smul η) (hεi (t + j)) t, S.E_smul η (s (t + j)) t, ih, hz]
      with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
    ring

/-- Cochrane (2023), p. 43, **with integrable surpluses**: for the AR(1) surplus with
`|βη| < 1`, `PV_t = s_t/(1 − βη)` almost surely.
Generalises `TidyR6MeasFiscal.mAr1_pv`. -/
theorem mAr1_pv_L1 (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (t : ℕ) : S.forwardSol β s t =ᵐ[S.μ] (1 - β * η)⁻¹ • s t := by
  filter_upwards [forwardSol_hasSum_L1 hs t,
    ae_all_iff.2 fun j => ar1_E_L1 hrec hsad hs.1 hmd t j] with ω h1 h2
  have h3 : HasSum (fun k => β ^ k * S.E t (s (t + k)) ω) ((1 - β * η)⁻¹ * s t ω) := by
    have hg := (hasSum_geometric_of_abs_lt_one hβη).mul_right (s t ω)
    convert hg using 1
    funext k
    rw [h2 k, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  rw [Pi.smul_apply, smul_eq_mul]
  exact h1.unique h3

/-- Cochrane (2023), p. 43, **with integrable surpluses**: the present-value news of the AR(1)
surplus is `e_{t+1}/(1 − βη)` almost surely.
Generalises `TidyR6MeasFiscal.mAr1_pv_news`. -/
theorem mAr1_pv_news_L1 (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1))
    (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    S.innov t (S.forwardSol β s (t + 1)) =ᵐ[S.μ] (1 - β * η)⁻¹ • e (t + 1) := by
  have hpv := mAr1_pv_L1 hβη hsad hs hrec hmd (t + 1)
  have h1 : S.E t (s (t + 1)) =ᵐ[S.μ] η • s t := by
    simpa using ar1_E_L1 hrec hsad hs.1 hmd t 1
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [hpv, S.E_congr hpv t, S.E_smul (1 - β * η)⁻¹ (s (t + 1)) t, h1]
    with ω e1 e2 e3 e4
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  rw [e1, e2, e3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e4, Pi.smul_apply, smul_eq_mul, hrec t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 43, corrected (survey E5), **with integrable surpluses**: in every
equilibrium `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = e_{t+1}/(1 − βη)` almost surely.
Generalises `TidyR6MeasFiscal.mAr1_unexpected_inflation`. -/
theorem mAr1_unexpected_inflation_L1 (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1))
    (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω * S.innov t (fun ω => P t ω / P (t + 1) ω) ω) =ᵐ[S.μ]
      (1 - β * η)⁻¹ • e (t + 1) :=
  (mUnexpected_inflation S h t).trans (mAr1_pv_news_L1 hβη hsad hs hrec hmd t)

/-- Cochrane (2023), p. 43 (survey E5), **with integrable surpluses**: almost surely, wherever the
shock is nonzero and `B_t/P_t ≠ 1`, the printed formula fails.
Generalises `TidyR6MeasFiscal.mAr1_printed_fails`. -/
theorem mAr1_printed_fails_L1 (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1))
    (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, e (t + 1) ω ≠ 0 → B t ω / P t ω ≠ 1 →
      S.innov t (fun ω => P t ω / P (t + 1) ω) ω ≠ (1 - β * η)⁻¹ * e (t + 1) ω := by
  have h1 : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hβη).2
    linarith
  filter_upwards [mAr1_unexpected_inflation_L1 hβη hsad hs hrec hmd h t]
    with ω hω he hV heq
  simp only [Pi.smul_apply, smul_eq_mul] at hω
  rw [heq] at hω
  apply hV
  have hx : (1 - β * η)⁻¹ * e (t + 1) ω ≠ 0 := mul_ne_zero (inv_ne_zero h1) he
  apply mul_right_cancel₀ hx
  rw [one_mul, hω]

/-- Cochrane (2023), p. 43, **with integrable surpluses**: the news about the value of the debt
sold is `ΔE_{t+1} PVex_{t+1} = βη/(1 − βη) e_{t+1}` almost surely.
Generalises `TidyR6MeasFiscal.mAr1_value_news`. -/
theorem mAr1_value_news_L1 (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1))
    (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    S.innov t (pvExM S β s (t + 1)) =ᵐ[S.μ] (β * η * (1 - β * η)⁻¹) • e (t + 1) := by
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hβη).2
    linarith
  have hsi := hs.1 (t + 1)
  have hpe : pvExM S β s (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1) - s (t + 1) := by
    filter_upwards [pv_eq_add_pvEx_L1 hsad hs (t + 1)] with ω h1
    rw [Pi.sub_apply, h1, Pi.add_apply]
    ring
  have hns : S.innov t (s (t + 1)) =ᵐ[S.μ] e (t + 1) := by
    have hk : S.E (t + 1) (s (t + 1)) = s (t + 1) := S.E_of_stronglyMeasurable (hsad (t + 1)) hsi
    have h1 : S.E t (s (t + 1)) =ᵐ[S.μ] η • s t := by
      simpa using ar1_E_L1 hrec hsad hs.1 hmd t 1
    filter_upwards [h1] with ω h1
    rw [MeasExpectationSystem.innov, Pi.sub_apply, hk, h1, hrec t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hIP : Integrable (S.forwardSol β s (t + 1)) S.μ := S.integrable_E _ _
  filter_upwards [TidyR6MeasFiscal.innov_congr S hpe t, S.E_sub hIP hsi (t + 1),
    S.E_sub hIP hsi t, mAr1_pv_news_L1 hβη hsad hs hrec hmd t, hns] with ω e1 e2 e3 e4 e5
  rw [e1]
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e4 e5 ⊢
  rw [e2, e3]
  simp only [Pi.sub_apply]
  have hc : (1 - β * η) * (1 - β * η)⁻¹ = 1 := mul_inv_cancel₀ h1η
  linear_combination e4 - e5 + e (t + 1) ω * hc

/-- Cochrane (2023), p. 43, **with integrable surpluses**: for `0 < βη < 1`, almost surely a
deficit shock lowers the value of the debt.
Generalises `TidyR6MeasFiscal.mAr1_value_falls`. -/
theorem mAr1_value_falls_L1 (hpos : 0 < β * η) (hlt : β * η < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, e (t + 1) ω < 0 → S.innov t (pvExM S β s (t + 1)) ω < 0 := by
  have hβη : |β * η| < 1 := by rwa [abs_of_pos hpos]
  filter_upwards [mAr1_value_news_L1 hβη hsad hs hrec hmd t] with ω h hε
  rw [h, Pi.smul_apply, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (mul_pos hpos (inv_pos.mpr (by linarith))) hε

/-! ### The s-shape with integrable surpluses -/

/-- Cochrane (2023), p. 43, **with integrable surpluses**: almost surely the present-value news
is the discounted sum of surplus news, `ΔE_{t+1} PV_{t+1} = ∑ βʲ ΔE_{t+1} s_{t+1+j}`.
Generalises `TidyR6MeasFiscal.mNews_pv_tsum`. -/
theorem mNews_pv_tsum_L1 (hs : SurplusL1 S β s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.innov t (s (t + 1 + j)) ω)
      (S.innov t (S.forwardSol β s (t + 1)) ω) := by
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [E_shift_hasSum hs (t + 1) (t + 1), E_shift_hasSum hs t (t + 1),
    S.E_tower (Nat.le_succ t) (MeasExpectationSystem.discSum β s (t + 1))] with ω e1 e2 e3
  have e3' : S.E t (S.forwardSol β s (t + 1)) ω =
      S.E t (MeasExpectationSystem.discSum β s (t + 1)) ω := e3
  have e1' : HasSum (fun k => β ^ k * S.E (t + 1) (s (t + 1 + k)) ω)
      (S.forwardSol β s (t + 1) ω) := e1
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  rw [e3']
  convert e1'.sub e2 using 1
  funext j
  ring

/-- Cochrane (2023), p. 43, "the surplus process must have an s-shaped moving average", **with
integrable surpluses** (`β > 0`): almost surely, zero present-value news and a current deficit
shock force a later positive surplus shock.
Generalises `TidyR6MeasFiscal.mSShape`. -/
theorem mSShape_L1 (hβ0 : 0 < β) (hs : SurplusL1 S β s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (S.forwardSol β s (t + 1)) ω = 0 → S.innov t (s (t + 1)) ω < 0 →
      ∃ j, 1 ≤ j ∧ 0 < S.innov t (s (t + 1 + j)) ω := by
  filter_upwards [mNews_pv_tsum_L1 hs t] with ω h h0 hd
  exact FiscalMonetary.sShape_seq hβ0 h.summable (by rw [h.tsum_eq]; exact h0)
    (by simpa using hd)

end Cochrane.IntertemporalModel.TidyR6MeasL1
