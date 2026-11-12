/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR6InnovGrowth
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The linear innovation identities for integrable processes on a probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, pp. 63–71
((3.17)–(3.28)), and Online Appendix A1.3, pp. 561–564.

The core `ExpectationSystem` defines `E_t` on all functions with exact equalities; a stationary
Gaussian process (unbounded across states) does not fit it. Here expectations are Mathlib's
conditional expectations `μ[· | 𝓕 t]` on a finite measure space with a filtration, and every
identity holds almost everywhere. The processes need not be bounded in any sense: they are
integrable with **`L¹` norms growing at most at rate `γ`, `∫|x_n| ≤ Kγⁿ`, with `ργ < 1`**
(`L1Growth`, `MGrowthEconomy`). Square-integrable processes with `L²` norms growing at rate `γ`
qualify (`L2Growth.toL1`); stationary `L²` processes are `γ = 1`.

* Summable `L¹` norms give almost-everywhere absolute convergence (`ae_summable_abs`), so the
  present-value series and the terminal terms behave a.e. (`ae_summable_E`, `ae_terminal`).
* (3.18) a.e. for every horizon (`m_fin_horizon`); (3.19) a.e. (`m_pv_319`); the innovation sum
  `∑ρ^jΔE_{t+1}(s̃ + g − r)_{t+1+j} = 0` a.e. and (3.20) a.e. (`m_innov_pv`, `m_identity_3_20`).
* The bond identities with a log bond price of `L¹` growth `γ`, `|ω̂|γ < 1`: the forward
  bond-price sum a.e. (`m_bondPrice_forward`), (3.21) a.e. (`m_bondReturn_innov`, through
  Mathlib's `condExp_tsum`), (3.22) a.e. (`m_weighted_inflation`).
* The special cases a.e.: (3.23) (`m_special_constant_long`), (3.24) (`m_identity_3_24`), (3.25)
  (`m_identity_3_25`), (3.27) (`m_special_constant_short`), (3.28) (`m_monetary_disinflation`)
  and §3.5.4 (`m_perpetuity`).

A pathwise algebraic core (`real_innov_pv`, `real_identity_3_20`) is shared by all a.e.
statements.
-/

namespace Cochrane.Generality.TidyR6InnovMeasure

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-! ### Pathwise algebra -/

/-- Cochrane (2023), p. 64 ("Taking time `t + 1` innovations of (3.19)"), pathwise: if
`∑ρ^jA_j = v₀`, `∑ρ^jB_{j+1} = v₁`, `B_0 = z` and `v₀ − z = ρv₁` (the flow), then
`∑ρ^j(B_j − A_j) = 0`. -/
theorem real_innov_pv {ρ v₀ v₁ z : ℝ} {A B : ℕ → ℝ} (ha : HasSum (fun j => ρ ^ j * A j) v₀)
    (hb : HasSum (fun j => ρ ^ j * B (j + 1)) v₁) (hz : B 0 = z) (hflow : v₀ - z = ρ * v₁) :
    HasSum (fun j => ρ ^ j * (B j - A j)) 0 := by
  have hb' : HasSum (fun j => ρ ^ j * B j) v₀ := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, hz]
    convert hb.mul_left ρ using 1
    funext j
    rw [pow_succ]
    ring
  have h := hb'.sub ha
  rw [sub_self] at h
  convert h using 1
  funext j
  ring

/-- Cochrane (2023), (3.20), p. 65, pathwise: with `A_j, B_j` the date-`t` and date-`t + 1`
forecasts of `(s̃ + g − r)_{t+1+j}`, split into forecasts of `s̃`, `g`, `r^n`, `π`, the identity
`∑ρ^j(B_j − A_j) = 0` and summability give the unexpected-inflation identity. -/
theorem real_identity_3_20 {ρ : ℝ} {A B Sa Sb Ga Gb Ra Rb Pa Pb : ℕ → ℝ}
    (h0 : HasSum (fun j => ρ ^ j * (B j - A j)) 0)
    (hA : ∀ j, A j = Sa j + Ga j - (Ra j - Pa j)) (hB : ∀ j, B j = Sb j + Gb j - (Rb j - Pb j))
    (hSa : Summable fun j => ρ ^ j * Sa j) (hSb : Summable fun j => ρ ^ j * Sb j)
    (hGa : Summable fun j => ρ ^ j * Ga j) (hGb : Summable fun j => ρ ^ j * Gb j)
    (hRa : Summable fun j => ρ ^ j * Ra j) (hRb : Summable fun j => ρ ^ j * Rb j)
    (hPa : Summable fun j => ρ ^ j * Pa j) (hPb : Summable fun j => ρ ^ j * Pb j) :
    (Pb 0 - Pa 0) - (Rb 0 - Ra 0) =
      -(∑' j, ρ ^ j * (Sb j - Sa j)) - (∑' j, ρ ^ j * (Gb j - Ga j)) +
        ∑' j, ρ ^ (j + 1) * ((Rb (j + 1) - Ra (j + 1)) - (Pb (j + 1) - Pa (j + 1))) := by
  have hS : Summable fun j => ρ ^ j * (Sb j - Sa j) := by
    simpa [mul_sub] using hSb.sub hSa
  have hG : Summable fun j => ρ ^ j * (Gb j - Ga j) := by
    simpa [mul_sub] using hGb.sub hGa
  have hR : Summable fun j => ρ ^ j * ((Rb j - Ra j) - (Pb j - Pa j)) := by
    have := (hRb.sub hRa).sub (hPb.sub hPa)
    convert this using 1
    funext j
    ring
  have hsplit : ∀ j, ρ ^ j * (B j - A j) = ρ ^ j * (Sb j - Sa j) + ρ ^ j * (Gb j - Ga j) -
      ρ ^ j * ((Rb j - Ra j) - (Pb j - Pa j)) := fun j => by
    rw [hA, hB]
    ring
  have h := h0.tsum_eq
  rw [tsum_congr hsplit, (hS.add hG).tsum_sub hR, hS.tsum_add hG] at h
  have hr0 : ∑' j, ρ ^ j * ((Rb j - Ra j) - (Pb j - Pa j)) = ((Rb 0 - Ra 0) - (Pb 0 - Pa 0)) +
      ∑' j, ρ ^ (j + 1) * ((Rb (j + 1) - Ra (j + 1)) - (Pb (j + 1) - Pa (j + 1))) := by
    rw [hR.tsum_eq_zero_add]
    simp
  rw [hr0] at h
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Summable `L¹` norms -/

/-- Cochrane (2023), (3.19), p. 64 (auxiliary): if `∫|f_k| ≤ c_k` with `∑c_k < ∞`, then
`∑_k ∫⁻‖f_k‖ < ∞`. -/
theorem tsum_lintegral_ne_top {f : ℕ → Ω → ℝ} (hf : ∀ k, Integrable (f k) μ) {c : ℕ → ℝ}
    (hc : Summable c) (hfc : ∀ k, ∫ ω, |f k ω| ∂μ ≤ c k) : ∑' k, ∫⁻ ω, ‖f k ω‖ₑ ∂μ ≠ ∞ := by
  have h1 : ∀ k, ∫⁻ ω, ‖f k ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, |f k ω| ∂μ) := fun k => by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf k)]
    simp only [Real.norm_eq_abs]
  have hc0 : ∀ k, 0 ≤ c k := fun k => (integral_nonneg fun ω => abs_nonneg _).trans (hfc k)
  simp_rw [h1]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' k, c k)) ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hc0 hc]
  exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hfc k)

/-- Cochrane (2023), (3.19), p. 64 (auxiliary, a Borel–Cantelli step): if `∫|f_k| ≤ c_k` with
`∑c_k < ∞`, then `∑_k |f_k(ω)| < ∞` for almost every `ω`. -/
theorem ae_summable_abs {f : ℕ → Ω → ℝ} (hf : ∀ k, Integrable (f k) μ) {c : ℕ → ℝ}
    (hc : Summable c) (hfc : ∀ k, ∫ ω, |f k ω| ∂μ ≤ c k) :
    ∀ᵐ ω ∂μ, Summable fun k => |f k ω| := by
  have hmeas : ∀ k, AEMeasurable (fun ω => ‖f k ω‖ₑ) μ := fun k =>
    (hf k).aestronglyMeasurable.enorm
  have h2 : ∫⁻ ω, ∑' k, ‖f k ω‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    exact tsum_lintegral_ne_top hf hc hfc
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) h2] with ω hω
  have h3 : ∑' k, (‖f k ω‖₊ : ℝ≥0∞) ≠ ∞ := hω.ne
  have h5 := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h3)
  simpa [Real.norm_eq_abs] using h5

/-- Cochrane (2023), p. 64 ("expected to grow no faster than `ρ^{−t}`"), in `L¹`: `x_n` is
integrable and `∫|x_n| ≤ Kγⁿ`. -/
def L1Growth (μ : Measure Ω) (γ : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  ∃ K, ∀ n, Integrable (x n) μ ∧ ∫ ω, |x n ω| ∂μ ≤ K * γ ^ n

/-- Cochrane (2023), (3.18): `L¹` growth bounds add. -/
theorem L1Growth.add {γ : ℝ} {x y : ℕ → Ω → ℝ} (hx : L1Growth μ γ x) (hy : L1Growth μ γ y) :
    L1Growth μ γ (x + y) := by
  obtain ⟨K, hK⟩ := hx
  obtain ⟨L, hL⟩ := hy
  refine ⟨K + L, fun n => ⟨(hK n).1.add (hL n).1, ?_⟩⟩
  calc ∫ ω, |(x + y) n ω| ∂μ ≤ ∫ ω, (|x n ω| + |y n ω|) ∂μ :=
        integral_mono (((hK n).1.add (hL n).1).abs) ((hK n).1.abs.add (hL n).1.abs)
          fun ω => abs_add_le _ _
    _ = ∫ ω, |x n ω| ∂μ + ∫ ω, |y n ω| ∂μ := integral_add (hK n).1.abs (hL n).1.abs
    _ ≤ (K + L) * γ ^ n := by rw [add_mul]; exact add_le_add (hK n).2 (hL n).2

/-- Cochrane (2023), (3.18): `L¹` growth bounds subtract. -/
theorem L1Growth.sub {γ : ℝ} {x y : ℕ → Ω → ℝ} (hx : L1Growth μ γ x) (hy : L1Growth μ γ y) :
    L1Growth μ γ (x - y) := by
  obtain ⟨K, hK⟩ := hx
  obtain ⟨L, hL⟩ := hy
  refine ⟨K + L, fun n => ⟨(hK n).1.sub (hL n).1, ?_⟩⟩
  calc ∫ ω, |(x - y) n ω| ∂μ ≤ ∫ ω, (|x n ω| + |y n ω|) ∂μ :=
        integral_mono (((hK n).1.sub (hL n).1).abs) ((hK n).1.abs.add (hL n).1.abs)
          fun ω => abs_sub _ _
    _ = ∫ ω, |x n ω| ∂μ + ∫ ω, |y n ω| ∂μ := integral_add (hK n).1.abs (hL n).1.abs
    _ ≤ (K + L) * γ ^ n := by rw [add_mul]; exact add_le_add (hK n).2 (hL n).2

/-- Cochrane (2023), p. 64, in `L²`: `x_n` is square integrable with `∫x_n² ≤ (Kγⁿ)²`, `K > 0`
(stationary `L²` processes are `γ = 1`). -/
def L2Growth (μ : Measure Ω) (γ : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  ∃ K, 0 < K ∧ ∀ n, Integrable (x n) μ ∧ Integrable (fun ω => x n ω ^ 2) μ ∧
    ∫ ω, x n ω ^ 2 ∂μ ≤ (K * γ ^ n) ^ 2

/-- Cochrane (2023), p. 64: on a finite measure space `L²` growth at rate `γ > 0` implies `L¹`
growth at rate `γ` (by `2λ|x| ≤ λ² + x²` with `λ = Kγⁿ`). -/
theorem L2Growth.toL1 [IsFiniteMeasure μ] {γ : ℝ} (hγ : 0 < γ) {x : ℕ → Ω → ℝ}
    (hx : L2Growth μ γ x) : L1Growth μ γ x := by
  obtain ⟨K, hK, h⟩ := hx
  refine ⟨K * (μ.real Set.univ + 1) / 2, fun n => ⟨(h n).1, ?_⟩⟩
  set l := K * γ ^ n with hl
  have hl0 : 0 < l := mul_pos hK (pow_pos hγ n)
  have hpt : ∀ ω, |x n ω| ≤ (l + x n ω ^ 2 / l) / 2 := fun ω => by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), add_div' _ _ _ hl0.ne', le_div_iff₀ hl0]
    nlinarith [sq_nonneg (|x n ω| - l), sq_abs (x n ω)]
  have hint : Integrable (fun ω => (l + x n ω ^ 2 / l) / 2) μ :=
    ((integrable_const l).add ((h n).2.1.div_const l)).div_const 2
  calc ∫ ω, |x n ω| ∂μ ≤ ∫ ω, (l + x n ω ^ 2 / l) / 2 ∂μ :=
        integral_mono (h n).1.abs hint hpt
    _ = (l * μ.real Set.univ + (∫ ω, x n ω ^ 2 ∂μ) / l) / 2 := by
        rw [integral_div, integral_add (integrable_const l) ((h n).2.1.div_const l),
          integral_const, integral_div, smul_eq_mul, mul_comm]
    _ ≤ (l * μ.real Set.univ + l ^ 2 / l) / 2 := by
        gcongr
        exact (h n).2.2
    _ = K * (μ.real Set.univ + 1) / 2 * γ ^ n := by
        rw [hl]
        field_simp

/-- Cochrane (2023), (3.19)–(3.22) (auxiliary): if `x` has `L¹` growth `γ` and `|a|γ < 1`, then
for any sub-σ-algebra `m`, `∑_j aʲ μ[x_{t+j+c} | m](ω)` converges absolutely for a.e. `ω`. -/
theorem ae_summable_E {m : MeasurableSpace Ω} {a γ : ℝ} (hγ : 0 ≤ γ) (ha : |a| * γ < 1)
    {x : ℕ → Ω → ℝ} (hx : L1Growth μ γ x) (t c : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun j => a ^ j * μ[x (t + j + c) | m] ω := by
  obtain ⟨K, hK⟩ := hx
  have hf : ∀ j, Integrable (fun ω => a ^ j * μ[x (t + j + c) | m] ω) μ := fun j =>
    integrable_condExp.const_mul _
  have hb : ∀ j, ∫ ω, |a ^ j * μ[x (t + j + c) | m] ω| ∂μ ≤
      K * γ ^ (t + c) * (|a| * γ) ^ j := fun j => by
    simp_rw [abs_mul]
    rw [integral_const_mul]
    calc |a ^ j| * ∫ ω, |μ[x (t + j + c) | m] ω| ∂μ ≤ |a ^ j| * ∫ ω, |x (t + j + c) ω| ∂μ :=
          mul_le_mul_of_nonneg_left (integral_abs_condExp_le _) (abs_nonneg _)
      _ ≤ |a ^ j| * (K * γ ^ (t + j + c)) :=
          mul_le_mul_of_nonneg_left (hK _).2 (abs_nonneg _)
      _ = K * γ ^ (t + c) * (|a| * γ) ^ j := by
          rw [abs_pow, mul_pow, show t + j + c = (t + c) + j by omega, pow_add]
          ring
  filter_upwards [ae_summable_abs hf ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg a) hγ) ha).mul_left _) hb] with ω hω
  exact hω.of_abs

/-- Cochrane (2023), p. 64 (the terminal term): if `x` has `L¹` growth `γ` and `|a|γ < 1`, then
`aᵀ μ[x_{t+T} | m](ω) → 0` for almost every `ω`. -/
theorem ae_terminal {m : MeasurableSpace Ω} {a γ : ℝ} (hγ : 0 ≤ γ) (ha : |a| * γ < 1)
    {x : ℕ → Ω → ℝ} (hx : L1Growth μ γ x) (t : ℕ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T => a ^ T * μ[x (t + T) | m] ω) atTop (𝓝 0) := by
  have h := ae_summable_E (m := m) hγ ha hx t 0
  filter_upwards [h] with ω hω
  simpa using hω.tendsto_atTop_zero

/-! ### The economy and (3.18)–(3.20) almost everywhere -/

variable [IsFiniteMeasure μ]

variable (μ) (𝓕 : Filtration ℕ mΩ) (ρ γ : ℝ) (v rn infl g sT : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.5, pp. 63–65, on a finite measure space: (3.17) at every date and state,
processes adapted to the filtration, `ρ > 0`, `γ ≥ 0`, `ργ < 1`, and all five processes
integrable with `L¹` growth `γ`. -/
structure MGrowthEconomy where
  flow : LogLinearIdentities.Flow317 ρ v rn infl g sT
  v_meas : ∀ t, StronglyMeasurable[𝓕 t] (v t)
  rn_meas : ∀ t, StronglyMeasurable[𝓕 t] (rn t)
  infl_meas : ∀ t, StronglyMeasurable[𝓕 t] (infl t)
  g_meas : ∀ t, StronglyMeasurable[𝓕 t] (g t)
  s_meas : ∀ t, StronglyMeasurable[𝓕 t] (sT t)
  rho_pos : 0 < ρ
  gamma_nonneg : 0 ≤ γ
  rho_gamma : ρ * γ < 1
  v_growth : L1Growth μ γ v
  rn_growth : L1Growth μ γ rn
  infl_growth : L1Growth μ γ infl
  g_growth : L1Growth μ γ g
  s_growth : L1Growth μ γ sT

/-- Cochrane (2023), (2.13) and p. 64: the innovation `ΔE_{t+1}x = μ[x | 𝓕(t+1)] − μ[x | 𝓕 t]`. -/
noncomputable def innovM (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := μ[x | 𝓕 (t + 1)] - μ[x | 𝓕 t]

variable {μ 𝓕 ρ γ v rn infl g sT}

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), (3.18): `s̃ + g − r` has `L¹` growth `γ`. -/
theorem MGrowthEconomy.zp_growth (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) :
    L1Growth μ γ (LogLinearIdentities.zp rn infl g sT) :=
  (hM.s_growth.add hM.g_growth).sub (hM.rn_growth.sub hM.infl_growth)

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), (3.18): `s̃ + g − r` is adapted. -/
theorem MGrowthEconomy.zp_meas (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (LogLinearIdentities.zp rn infl g sT t) :=
  ((hM.s_meas t).add (hM.g_meas t)).sub ((hM.rn_meas t).sub (hM.infl_meas t))

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), §3.5: `|ρ|γ < 1`. -/
theorem MGrowthEconomy.abs_rho_gamma (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) :
    |ρ| * γ < 1 := by
  rw [abs_of_pos hM.rho_pos]; exact hM.rho_gamma

/-- Cochrane (2023), (3.18), p. 63, almost everywhere, for every horizon `T`:
`v_t = ∑_{j<T} ρ^j E_t(s̃ + g − r)_{t+1+j} + ρ^T E_t v_{t+T}`. -/
theorem m_fin_horizon (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (t T : ℕ) :
    ∀ᵐ ω ∂μ, v t ω = ∑ j ∈ Finset.range T,
      ρ ^ j * μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 t] ω +
        ρ ^ T * μ[v (t + T) | 𝓕 t] ω := by
  obtain ⟨Kv, hKv⟩ := hM.v_growth
  obtain ⟨Kz, hKz⟩ := hM.zp_growth
  induction T with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add, add_zero]
    rw [condExp_of_stronglyMeasurable (𝓕.le t) (hM.v_meas t) (hKv t).1]
  | succ T ih =>
    have hrec : v (t + T) = LogLinearIdentities.zp rn infl g sT (t + T + 1) +
        ρ • v (t + T + 1) := by
      funext ω
      have := hM.flow (t + T) ω
      simp only [LogLinearIdentities.zp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      linarith
    have hE : μ[v (t + T) | 𝓕 t] =ᵐ[μ] μ[LogLinearIdentities.zp rn infl g sT (t + T + 1) | 𝓕 t]
        + ρ • μ[v (t + T + 1) | 𝓕 t] := by
      rw [hrec]
      exact (condExp_add (hKz _).1 ((hKv _).1.smul ρ) _).trans
        (EventuallyEq.add (EventuallyEq.refl _ _) (condExp_smul ρ _ _))
    filter_upwards [ih, hE] with ω h1 h2
    rw [h1, Finset.sum_range_succ, h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      show t + T + 1 = t + (T + 1) by omega, pow_succ]
    ring

/-- Cochrane (2023), (3.19), p. 64, **for integrable processes with `L¹` growth `γ < 1/ρ`**:
almost surely `v_t = ∑_{j≥1} ρ^{j−1} E_t(s̃ + g − r)_{t+j}`, as a convergent sum. -/
theorem m_pv_319 (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ρ ^ j * μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 t] ω)
      (v t ω) := by
  filter_upwards [ae_all_iff.2 (m_fin_horizon hM t),
    ae_summable_E (m := 𝓕 t) hM.gamma_nonneg hM.abs_rho_gamma hM.zp_growth t 1,
    ae_terminal (m := 𝓕 t) hM.gamma_nonneg hM.abs_rho_gamma hM.v_growth t] with ω h1 h2 h3
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T,
      ρ ^ j * μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 t] ω) atTop (𝓝 (v t ω)) := by
    have h4 := (tendsto_const_nhds (x := v t ω)).sub h3
    rw [sub_zero] at h4
    refine h4.congr fun T => ?_
    rw [h1 T]
    ring
  rw [← tendsto_nhds_unique h2.hasSum.tendsto_sum_nat hlim]
  exact h2.hasSum

/-- Cochrane (2023), p. 64, almost everywhere: the innovations of the discounted flow sum to
zero, `∑_j ρ^jΔE_{t+1}(s̃ + g − r)_{t+1+j} = 0`. -/
theorem m_innov_pv (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ρ ^ j *
      innovM μ 𝓕 t (LogLinearIdentities.zp rn infl g sT (t + j + 1)) ω) 0 := by
  obtain ⟨Kz, hKz⟩ := hM.zp_growth
  have hz : μ[LogLinearIdentities.zp rn infl g sT (t + 1) | 𝓕 (t + 1)] =
      LogLinearIdentities.zp rn infl g sT (t + 1) :=
    condExp_of_stronglyMeasurable (𝓕.le _) (hM.zp_meas (t + 1)) (hKz _).1
  have e : ∀ j, t + 1 + j + 1 = t + (j + 1) + 1 := fun j => by omega
  filter_upwards [m_pv_319 hM t, m_pv_319 hM (t + 1)] with ω ha hb
  simp only [e] at hb
  have h := real_innov_pv (A := fun j => μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 t] ω)
    (B := fun j => μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 (t + 1)] ω) ha hb
    (by simp only [add_zero]; rw [hz]) (by
      have := hM.flow t ω
      simp only [LogLinearIdentities.zp, Pi.add_apply, Pi.sub_apply]
      linarith)
  simpa [innovM] using h

/-- Cochrane (2023), (3.20), p. 65, **almost everywhere, for integrable processes with `L¹`
growth `γ < 1/ρ`**:
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑ρ^jΔE_{t+1}s̃_{t+1+j} − ∑ρ^jΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1}ρ^j(ΔE_{t+1}r^n_{t+1+j} − ΔE_{t+1}π_{t+1+j})`. -/
theorem m_identity_3_20 (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (t : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (infl (t + 1)) ω - innovM μ 𝓕 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innovM μ 𝓕 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * (innovM μ 𝓕 t (rn (t + j + 2)) ω -
          innovM μ 𝓕 t (infl (t + j + 2)) ω) := by
  obtain ⟨Ks, hKs⟩ := hM.s_growth
  obtain ⟨Kg, hKg⟩ := hM.g_growth
  obtain ⟨Kr, hKr⟩ := hM.rn_growth
  obtain ⟨Kp, hKp⟩ := hM.infl_growth
  have hγ := hM.gamma_nonneg
  have hρ := hM.abs_rho_gamma
  have hsplit : ∀ (s j : ℕ), μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 s] =ᵐ[μ]
      μ[sT (t + j + 1) | 𝓕 s] + μ[g (t + j + 1) | 𝓕 s] -
        (μ[rn (t + j + 1) | 𝓕 s] - μ[infl (t + j + 1) | 𝓕 s]) := fun s j => by
    have e : LogLinearIdentities.zp rn infl g sT (t + j + 1) =
        (sT (t + j + 1) + g (t + j + 1)) - (rn (t + j + 1) - infl (t + j + 1)) := rfl
    rw [e]
    refine (condExp_sub ((hKs _).1.add (hKg _).1) ((hKr _).1.sub (hKp _).1) _).trans ?_
    exact EventuallyEq.sub (condExp_add (hKs _).1 (hKg _).1 _)
      (condExp_sub (hKr _).1 (hKp _).1 _)
  filter_upwards [m_innov_pv hM t, ae_all_iff.2 (hsplit t), ae_all_iff.2 (hsplit (t + 1)),
    ae_summable_E (m := 𝓕 t) hγ hρ hM.s_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.s_growth t 1,
    ae_summable_E (m := 𝓕 t) hγ hρ hM.g_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.g_growth t 1,
    ae_summable_E (m := 𝓕 t) hγ hρ hM.rn_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.rn_growth t 1,
    ae_summable_E (m := 𝓕 t) hγ hρ hM.infl_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.infl_growth t 1]
    with ω h0 hA hB hSa hSb hGa hGb hRa hRb hPa hPb
  have h0' : HasSum (fun j => ρ ^ j *
      (μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 (t + 1)] ω -
        μ[LogLinearIdentities.zp rn infl g sT (t + j + 1) | 𝓕 t] ω)) 0 := by
    simpa [innovM] using h0
  have h := real_identity_3_20 h0' (fun j => by simpa using hA j) (fun j => by simpa using hB j)
    hSa hSb hGa hGb hRa hRb hPa hPb
  simp only [innovM, Pi.sub_apply]
  simp only [add_zero] at h
  convert h using 3

/-! ### The bond identities (3.21)–(3.22) almost everywhere -/

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), (3.19), p. 64 (auxiliary, without conditioning): if `x` has `L¹` growth `γ`
and `|a|γ < 1`, then `∑_j |aʲx_{t+j+c}(ω)| < ∞` for almost every `ω`. -/
theorem ae_summable_path {a γ' : ℝ} (hγ : 0 ≤ γ') (ha : |a| * γ' < 1) {x : ℕ → Ω → ℝ}
    (hx : L1Growth μ γ' x) (t c : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun j => |a ^ j * x (t + j + c) ω| := by
  obtain ⟨K, hK⟩ := hx
  refine ae_summable_abs (fun j => (hK _).1.const_mul _) ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg a) hγ) ha).mul_left (K * γ' ^ (t + c))) fun j => ?_
  simp_rw [abs_mul]
  rw [integral_const_mul, abs_pow]
  calc |a| ^ j * ∫ ω, |x (t + j + c) ω| ∂μ ≤ |a| ^ j * (K * γ' ^ (t + j + c)) :=
        mul_le_mul_of_nonneg_left (hK _).2 (pow_nonneg (abs_nonneg _) _)
    _ = K * γ' ^ (t + c) * (|a| * γ') ^ j := by
        rw [mul_pow, show t + j + c = (t + c) + j by omega, pow_add]
        ring

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 (1.24), p. 563: if the log bond price has `L¹` growth `γ`, so does the
bond return, `∫|r^n_{n+1}| ≤ K(|ω̂|γ + 1)γⁿ`. -/
theorem m_rn_growth {ωh γ' : ℝ} {q rn' : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet ωh q rn')
    (hq : L1Growth μ γ' q) : L1Growth μ γ' fun n => rn' (n + 1) := by
  obtain ⟨K, hK⟩ := hq
  have he : ∀ n, rn' (n + 1) = ωh • q (n + 1) - q n := fun n => by
    funext ω
    rw [hret n ω]
    rfl
  refine ⟨K * (|ωh| * γ' + 1), fun n => ⟨by
    change Integrable (rn' (n + 1)) μ
    rw [he]; exact ((hK _).1.smul ωh).sub (hK n).1, ?_⟩⟩
  change ∫ ω, |rn' (n + 1) ω| ∂μ ≤ _
  rw [he]
  calc ∫ ω, |(ωh • q (n + 1) - q n) ω| ∂μ ≤ ∫ ω, (|ωh| * |q (n + 1) ω| + |q n ω|) ∂μ := by
        refine integral_mono ((((hK _).1.smul ωh).sub (hK n).1).abs)
          (((hK _).1.abs.const_mul _).add (hK n).1.abs) fun ω => ?_
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact (abs_sub _ _).trans (by rw [abs_mul])
    _ = |ωh| * ∫ ω, |q (n + 1) ω| ∂μ + ∫ ω, |q n ω| ∂μ := by
        rw [integral_add ((hK _).1.abs.const_mul _) (hK n).1.abs, integral_const_mul]
    _ ≤ |ωh| * (K * γ' ^ (n + 1)) + K * γ' ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left (hK _).2 (abs_nonneg _)) (hK n).2
    _ = K * (|ωh| * γ' + 1) * γ' ^ n := by ring

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 p. 564 (the corrected box formula, survey E16), **almost everywhere for a
log bond price of `L¹` growth `γ` with `|ω̂|γ < 1`**: `q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`. -/
theorem m_bondPrice_forward {ωh γ' : ℝ} {q rn' : ℕ → Ω → ℝ}
    (hret : LogLinearIdentities.BondRet ωh q rn') (hγ : 0 ≤ γ') (hq : L1Growth μ γ' q)
    (hω : |ωh| * γ' < 1) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ωh ^ j * rn' (t + j + 1) ω) (-q t ω) := by
  filter_upwards [ae_summable_path hγ hω (m_rn_growth hret hq) t 0,
    ae_summable_path hγ hω hq t 0] with ω hs hT
  have hrec : ∀ n, q n ω = -rn' (n + 1) ω + ωh * q (n + 1) ω := fun n => by
    rw [hret n ω]; ring
  have hs' : Summable fun j => (∏ k ∈ Finset.range j, ωh) * -rn' (t + j + 1) ω := by
    simp only [Finset.prod_const, Finset.card_range]
    refine (hs.of_abs.neg).congr fun j => ?_
    simp only [add_zero]
    ring
  have hterm : Tendsto (fun T => (∏ k ∈ Finset.range T, ωh) * q (t + T) ω) atTop (𝓝 0) := by
    simp only [Finset.prod_const, Finset.card_range]
    simpa using hT.of_abs.tendsto_atTop_zero
  have h := (Money.pv_discount_iff (x := fun n => q n ω) (a := fun n => -rn' (n + 1) ω)
    (b := fun _ => ωh) hrec t hs').mp hterm
  simp only [Finset.prod_const, Finset.card_range] at h hs'
  have h2 : HasSum (fun j => ωh ^ j * rn' (t + j + 1) ω)
      (-(∑' j, ωh ^ j * -rn' (t + j + 1) ω)) := by
    have := hs'.hasSum.neg
    convert this using 1
    funext j
    ring
  rw [← h] at h2
  exact h2

/-- Cochrane (2023), (3.21) and A1 (1.25), p. 564, **almost everywhere for an adapted log bond
price of `L¹` growth `γ` with `|ω̂|γ < 1`**: `ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^jΔE_{t+1}r^n_{t+1+j}`
(the conditional expectation passes through the series by `condExp_tsum`). -/
theorem m_bondReturn_innov {ωh γ' : ℝ} {q rn' : ℕ → Ω → ℝ}
    (hret : LogLinearIdentities.BondRet ωh q rn') (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t))
    (hγ : 0 ≤ γ') (hq : L1Growth μ γ' q) (hω : |ωh| * γ' < 1) (t : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (rn' (t + 1)) ω =
      -∑' j, ωh ^ j * ωh * innovM μ 𝓕 t (rn' (t + j + 2)) ω := by
  have hr := m_rn_growth hret hq
  obtain ⟨Kr, hKr⟩ := hr
  obtain ⟨Kq, hKq⟩ := hq
  set f : ℕ → Ω → ℝ := fun j => ωh ^ j • rn' (t + j + 2) with hf
  have hfi : ∀ j, Integrable (f j) μ := fun j => (hKr _).1.smul _
  have hfb : ∀ j, ∫ ω, |f j ω| ∂μ ≤ Kr * γ' ^ (t + 1) * (|ωh| * γ') ^ j := fun j => by
    simp only [hf, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [integral_const_mul, abs_pow]
    calc |ωh| ^ j * ∫ ω, |rn' (t + j + 2) ω| ∂μ ≤ |ωh| ^ j * (Kr * γ' ^ (t + j + 1)) :=
          mul_le_mul_of_nonneg_left (hKr (t + j + 1)).2 (pow_nonneg (abs_nonneg _) _)
      _ = Kr * γ' ^ (t + 1) * (|ωh| * γ') ^ j := by
          rw [mul_pow, show t + j + 1 = (t + 1) + j by omega, pow_add]
          ring
  have hne := tsum_lintegral_ne_top hfi ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg ωh) hγ) hω).mul_left _) hfb
  set F : Ω → ℝ := fun ω => ∑' j, f j ω with hF
  have hqF : q (t + 1) =ᵐ[μ] -F := by
    filter_upwards [m_bondPrice_forward hret hγ ⟨Kq, hKq⟩ hω (t + 1)] with ω h
    have e : ∀ j, t + 1 + j + 1 = t + j + 2 := fun j => by omega
    simp only [e] at h
    simp only [hF, hf, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, h.tsum_eq, neg_neg]
  have hEq : ∀ s, μ[q (t + 1) | 𝓕 s] =ᵐ[μ]
      fun ω => -∑' j, ωh ^ j * μ[rn' (t + j + 2) | 𝓕 s] ω := fun s => by
    have h1 := condExp_congr_ae (m := 𝓕 s) hqF
    have h2 := condExp_neg (μ := μ) F (𝓕 s)
    have h3 := condExp_tsum (m := 𝓕 s) (fun j => (hfi j).aestronglyMeasurable) hne
    have h4 : ∀ᵐ ω ∂μ, ∀ j, μ[f j | 𝓕 s] ω = ωh ^ j * μ[rn' (t + j + 2) | 𝓕 s] ω :=
      ae_all_iff.2 fun j => by
        filter_upwards [condExp_smul (m := 𝓕 s) (μ := μ) (ωh ^ j) (rn' (t + j + 2))] with ω h
        rw [h, Pi.smul_apply, smul_eq_mul]
    filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
    rw [e1, e2, Pi.neg_apply, e3]
    simp only [e4]
  have hrn : rn' (t + 1) = ωh • q (t + 1) - q t := by
    funext ω
    rw [hret t ω]
    rfl
  have hErn : ∀ s, t ≤ s → μ[rn' (t + 1) | 𝓕 s] =ᵐ[μ] ωh • μ[q (t + 1) | 𝓕 s] - q t := by
    intro s hs
    rw [hrn]
    refine (condExp_sub ((hKq _).1.smul ωh) (hKq t).1 _).trans ?_
    rw [condExp_of_stronglyMeasurable (𝓕.le s) ((hqm t).mono (𝓕.mono hs)) (hKq t).1]
    exact EventuallyEq.sub (condExp_smul _ _ _) (EventuallyEq.refl _ _)
  filter_upwards [hEq t, hEq (t + 1), hErn t le_rfl, hErn (t + 1) (Nat.le_succ t),
    ae_summable_E (m := 𝓕 t) hγ hω ⟨Kr, hKr⟩ t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hω ⟨Kr, hKr⟩ t 1] with ω e0 e1 r0 r1 s0 s1
  simp only [innovM, Pi.sub_apply]
  rw [r0, r1]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e0, e1]
  have e : ∀ j, t + j + 1 + 1 = t + j + 2 := fun j => by omega
  simp only [e] at s0 s1
  rw [show (∑' j, ωh ^ j * ωh * (μ[rn' (t + j + 2) | 𝓕 (t + 1)] ω -
      μ[rn' (t + j + 2) | 𝓕 t] ω)) = ωh * (∑' j, ωh ^ j * μ[rn' (t + j + 2) | 𝓕 (t + 1)] ω -
      ∑' j, ωh ^ j * μ[rn' (t + j + 2) | 𝓕 t] ω) by
    rw [← s1.tsum_sub s0, ← tsum_mul_left]
    exact tsum_congr fun j => by ring]
  ring

/-- Cochrane (2023), (3.22), p. 65, pathwise: from (3.20) and (3.21) at one state, with the needed
summability, the weighted inflation identity. Here `R_j`, `P_j` are the innovations of `r^n` and
`π` at `t + 1 + j`. -/
theorem real_weighted {ρ ωh S G : ℝ} {R P : ℕ → ℝ}
    (h20 : P 0 - R 0 = -S - G + ∑' j, ρ ^ (j + 1) * (R (j + 1) - P (j + 1)))
    (h21 : R 0 = -∑' j, ωh ^ j * ωh * R (j + 1))
    (hP : Summable fun j => ωh ^ j * P j) (hRω : Summable fun j => ωh ^ j * R (j + 1))
    (hRρ : Summable fun j => ρ ^ j * R (j + 1)) (hPρ : Summable fun j => ρ ^ j * P (j + 1)) :
    ∑' j, ωh ^ j * P j =
      -S - G + ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) * (R (j + 1) - P (j + 1)) := by
  have hP1 : Summable fun j => ωh ^ j * P (j + 1) := by
    have := ((summable_nat_add_iff 1).mpr hP).mul_left ωh⁻¹
    by_cases h0 : ωh = 0
    · simp only [h0]
      refine (summable_nat_add_iff 1).mp ?_
      simp
    · refine this.congr fun j => ?_
      rw [pow_succ]
      field_simp
  have e1 : ∑' j, ωh ^ j * P j = P 0 + ∑' j, ωh ^ (j + 1) * P (j + 1) := by
    rw [hP.tsum_eq_zero_add]
    simp
  have hA : Summable fun j => ρ ^ (j + 1) * (R (j + 1) - P (j + 1)) := by
    have := (hRρ.sub hPρ).mul_left ρ
    convert this using 1
    funext j
    ring
  have hB : Summable fun j => ωh ^ (j + 1) * (R (j + 1) - P (j + 1)) := by
    have := (hRω.sub hP1).mul_left ωh
    convert this using 1
    funext j
    ring
  have hC : Summable fun j => ωh ^ (j + 1) * P (j + 1) := by
    have := hP1.mul_left ωh
    convert this using 1
    funext j
    ring
  have e2 : ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) * (R (j + 1) - P (j + 1)) =
      ∑' j, ρ ^ (j + 1) * (R (j + 1) - P (j + 1)) -
        ∑' j, ωh ^ (j + 1) * (R (j + 1) - P (j + 1)) := by
    rw [← hA.tsum_sub hB]
    exact tsum_congr fun j => by ring
  have e3 : ∑' j, ωh ^ (j + 1) * (R (j + 1) - P (j + 1)) =
      ∑' j, ωh ^ j * ωh * R (j + 1) - ∑' j, ωh ^ (j + 1) * P (j + 1) := by
    have hD : Summable fun j => ωh ^ j * ωh * R (j + 1) := by
      have := hRω.mul_left ωh
      convert this using 1
      funext j
      ring
    rw [← hD.tsum_sub hC]
    exact tsum_congr fun j => by ring
  rw [e1, e2, e3]
  linarith

/-- Cochrane (2023), (3.22), p. 65, **almost everywhere**, in an economy of `L¹` growth `γ < 1/ρ`
with an adapted log bond price of `L¹` growth `γ`, `|ω̂|γ < 1`:
`∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = −∑ρ^jΔE_{t+1}s̃_{t+1+j} − ∑ρ^jΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1}(ρ^j − ω̂^j)(ΔE_{t+1}r^n_{t+1+j} − ΔE_{t+1}π_{t+1+j})`. -/
theorem m_weighted_inflation (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet ωh q rn)
    (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t)) (hq : L1Growth μ γ q) (hω : |ωh| * γ < 1)
    (t : ℕ) :
    ∀ᵐ ω ∂μ, ∑' j, ωh ^ j * innovM μ 𝓕 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innovM μ 𝓕 t (g (t + j + 1)) ω) +
        ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) * (innovM μ 𝓕 t (rn (t + j + 2)) ω -
          innovM μ 𝓕 t (infl (t + j + 2)) ω) := by
  have hγ := hM.gamma_nonneg
  have hρ := hM.abs_rho_gamma
  filter_upwards [m_identity_3_20 hM t, m_bondReturn_innov hret hqm hγ hq hω t,
    ae_summable_E (m := 𝓕 t) hγ hω hM.infl_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hω hM.infl_growth t 1,
    ae_summable_E (m := 𝓕 t) hγ hω hM.rn_growth t 2,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hω hM.rn_growth t 2,
    ae_summable_E (m := 𝓕 t) hγ hρ hM.rn_growth t 2,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.rn_growth t 2,
    ae_summable_E (m := 𝓕 t) hγ hρ hM.infl_growth t 2,
    ae_summable_E (m := 𝓕 (t + 1)) hγ hρ hM.infl_growth t 2]
    with ω h20 h21 p0 p1 rw0 rw1 rr0 rr1 pr0 pr1
  have e : ∀ j, t + (j + 1) + 1 = t + j + 2 := fun j => by omega
  refine real_weighted (R := fun j => innovM μ 𝓕 t (rn (t + j + 1)) ω)
    (P := fun j => innovM μ 𝓕 t (infl (t + j + 1)) ω) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [e] using h20
  · simpa [e] using h21
  · simpa [innovM, mul_sub] using p1.sub p0
  · simpa [innovM, mul_sub, e] using rw1.sub rw0
  · simpa [innovM, mul_sub, e] using rr1.sub rr0
  · simpa [innovM, mul_sub, e] using pr1.sub pr0

/-! ### The special cases (3.23)–(3.28) almost everywhere -/

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), p. 66 (no growth): the innovation of the zero variable is zero. -/
theorem innovM_zero (t : ℕ) : innovM μ 𝓕 t 0 = 0 := by
  simp [innovM, condExp_zero]

/-- Cochrane (2023), p. 66, almost everywhere: with constant expected real returns
(`E_n(r^n_{n+1} − π_{n+1}) = 0` a.e.), real returns beyond `t + 1` have no innovation at `t + 1`:
`ΔE_{t+1}r^n_{t+j+2} − ΔE_{t+1}π_{t+j+2} = 0` a.e. -/
theorem m_innov_r_zero (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT)
    (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t j : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (rn (t + j + 2)) ω - innovM μ 𝓕 t (infl (t + j + 2)) ω = 0 := by
  obtain ⟨Kr, hKr⟩ := hM.rn_growth
  obtain ⟨Kp, hKp⟩ := hM.infl_growth
  have hs : ∀ s, s ≤ t + j + 1 → μ[rn (t + j + 2) | 𝓕 s] - μ[infl (t + j + 2) | 𝓕 s] =ᵐ[μ] 0 := by
    intro s hs
    refine (condExp_sub (hKr _).1 (hKp _).1 _).symm.trans ?_
    refine (condExp_condExp_of_le (𝓕.mono hs) (𝓕.le (t + j + 1))).symm.trans ?_
    refine (condExp_congr_ae (hc (t + j + 1))).trans ?_
    rw [condExp_zero]
  filter_upwards [hs t (by omega), hs (t + 1) (by omega)] with ω h0 h1
  simp only [innovM, Pi.sub_apply, Pi.zero_apply] at h0 h1 ⊢
  linarith

/-- Cochrane (2023), (3.24), p. 68, almost everywhere: with constant expected returns and no
growth, `ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0}ρ^jΔE_{t+1}s̃_{t+1+j}`. -/
theorem m_identity_3_24 (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) (hg : ∀ n, g n = 0)
    (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (infl (t + 1)) ω - innovM μ 𝓕 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω := by
  filter_upwards [m_identity_3_20 hM t, ae_all_iff.2 (m_innov_r_zero hM hc t)] with ω h hr
  simp only [hg, innovM_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, hr,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.27), p. 69, almost everywhere: with one-period debt (`ω̂ = 0`), constant
expected returns and no growth, `ΔE_{t+1}π_{t+1} = −∑_{j≥0}ρ^jΔE_{t+1}s̃_{t+1+j}`. -/
theorem m_special_constant_short (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT)
    {q : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet 0 q rn)
    (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t)) (hg : ∀ n, g n = 0)
    (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω := by
  obtain ⟨Kr, hKr⟩ := hM.rn_growth
  have he : rn (t + 1) = -q t := by
    funext ω
    rw [hret t ω, zero_mul, zero_sub]
    rfl
  have hm : StronglyMeasurable[𝓕 t] (rn (t + 1)) := by rw [he]; exact (hqm t).neg
  have h0 : innovM μ 𝓕 t (rn (t + 1)) = 0 := by
    simp only [innovM]
    rw [condExp_of_stronglyMeasurable (𝓕.le _) (hm.mono (𝓕.mono (Nat.le_succ t))) (hKr _).1,
      condExp_of_stronglyMeasurable (𝓕.le _) hm (hKr _).1, sub_self]
  filter_upwards [m_identity_3_24 hM hg hc t] with ω h
  rw [h0, Pi.zero_apply, sub_zero] at h
  exact h

/-- Cochrane (2023), (3.23), p. 67, almost everywhere: with constant expected returns and no
growth, `∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = −∑_{j≥0} ρ^jΔE_{t+1}s̃_{t+1+j}`. -/
theorem m_special_constant_long (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet ωh q rn)
    (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t)) (hq : L1Growth μ γ q) (hω : |ωh| * γ < 1)
    (hg : ∀ n, g n = 0) (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∑' j, ωh ^ j * innovM μ 𝓕 t (infl (t + j + 1)) ω =
      -∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω := by
  filter_upwards [m_weighted_inflation hM hret hqm hq hω t,
    ae_all_iff.2 (m_innov_r_zero hM hc t)] with ω h hr
  simp only [hr, mul_zero, tsum_zero, add_zero] at h
  simp only [hg, innovM, condExp_zero, sub_zero, Pi.zero_apply, mul_zero, tsum_zero] at h
  simpa [innovM] using h

/-- Cochrane (2023), (3.28), p. 69, almost everywhere: with no surplus news (a.e.), constant
expected returns and no growth, `∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = 0`, hence
`ΔE_{t+1}π_{t+1} = −∑_{j≥1} ω̂^jΔE_{t+1}π_{t+1+j}`. -/
theorem m_monetary_disinflation (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet ωh q rn)
    (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t)) (hq : L1Growth μ γ q) (hω : |ωh| * γ < 1)
    (hg : ∀ n, g n = 0) (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t : ℕ)
    (hs : ∀ j, ∀ᵐ ω ∂μ, innovM μ 𝓕 t (sT (t + j + 1)) ω = 0) :
    ∀ᵐ ω ∂μ, ∑' j, ωh ^ j * innovM μ 𝓕 t (infl (t + j + 1)) ω = 0 ∧
      innovM μ 𝓕 t (infl (t + 1)) ω =
        -∑' j, ωh ^ (j + 1) * innovM μ 𝓕 t (infl (t + j + 2)) ω := by
  filter_upwards [m_special_constant_long hM hret hqm hq hω hg hc t, ae_all_iff.2 hs,
    ae_summable_E (m := 𝓕 t) hM.gamma_nonneg hω hM.infl_growth t 1,
    ae_summable_E (m := 𝓕 (t + 1)) hM.gamma_nonneg hω hM.infl_growth t 1]
    with ω h hs' p0 p1
  simp only [hs', mul_zero, tsum_zero, neg_zero] at h
  refine ⟨h, ?_⟩
  have hP : Summable fun j => ωh ^ j * innovM μ 𝓕 t (infl (t + j + 1)) ω := by
    simpa [innovM, mul_sub] using p1.sub p0
  rw [hP.tsum_eq_zero_add] at h
  simp only [pow_zero, one_mul, add_zero] at h
  have e : ∀ j, t + (j + 1) + 1 = t + j + 2 := fun j => by omega
  simp only [e] at h
  linarith

/-- Cochrane (2023), (3.25), p. 68, almost everywhere: with constant expected returns,
`ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^jΔE_{t+1}π_{t+1+j}`. -/
theorem m_identity_3_25 (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : LogLinearIdentities.BondRet ωh q rn)
    (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t)) (hq : L1Growth μ γ q) (hω : |ωh| * γ < 1)
    (hc : ∀ n, μ[rn (n + 1) - infl (n + 1) | 𝓕 n] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, innovM μ 𝓕 t (rn (t + 1)) ω =
      -∑' j, ωh ^ j * ωh * innovM μ 𝓕 t (infl (t + j + 2)) ω := by
  filter_upwards [m_bondReturn_innov hret hqm hM.gamma_nonneg hq hω t,
    ae_all_iff.2 (m_innov_r_zero hM hc t)] with ω h hr
  rw [h]
  congr 1
  exact tsum_congr fun j => by rw [sub_eq_zero.mp (hr j)]

/-- Cochrane (2023), §3.5.4, p. 71, almost everywhere: with perpetuities (`ω̂ = ρ`) and an
adapted log bond price of `L¹` growth `γ`, the discount-rate terms drop out of (3.22). -/
theorem m_perpetuity (hM : MGrowthEconomy μ 𝓕 ρ γ v rn infl g sT) {q : ℕ → Ω → ℝ}
    (hret : LogLinearIdentities.BondRet ρ q rn) (hqm : ∀ t, StronglyMeasurable[𝓕 t] (q t))
    (hq : L1Growth μ γ q) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∑' j, ρ ^ j * innovM μ 𝓕 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innovM μ 𝓕 t (sT (t + j + 1)) ω) -
        ∑' j, ρ ^ j * innovM μ 𝓕 t (g (t + j + 1)) ω := by
  filter_upwards [m_weighted_inflation hM hret hqm hq hM.abs_rho_gamma t] with ω h
  simpa using h

end Cochrane.Generality.TidyR6InnovMeasure
