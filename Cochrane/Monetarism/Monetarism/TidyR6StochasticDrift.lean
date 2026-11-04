/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.CashInAdvance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The stochastic `E_t d(·)` forms of Online Appendix §1.6

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–569, eqs. (1.31)–(1.34). The deterministic forms of (1.33)–(1.34)
(`ContinuousTime.money_printing_iff`, `ContinuousTime.money_interest_iff`) and the ex-post
discounting forms (1.35)–(1.37) are in `ContinuousTime`. The forms (1.32)–(1.34) use `E_t d(·)`, the
expected increment of a continuous-time stochastic process. Mathlib has conditional
expectations and martingales but no stochastic integral and no Itô calculus, so `E_t d(·)` is
given exactly the content that can be made precise without them.

## What is proved

**A. Discrete time with step `Δ > 0`, any `ExpectationSystem` with the pull-out property.**
`E_t d X` is read as the conditional increment `E_k[X_{k+1}] − X_k`, the nominal rate by
`(1 + i_kΔ)E_k[Λ_{k+1}/P_{k+1}] = Λ_k/P_k` (the discrete form of
`E_t d(Λ/P)/(Λ/P) = −i dt`), and the flow (1.31) by
`B_{k+1} + M_{k+1} = (1 + i_kΔ)B_k + (1 + i^m_kΔ)M_k − P_ks_kΔ`.
* `rate_increment`, `rate_increment_tendsto`: the conditional increment of `Λ/P` per unit time
  and per unit of `Λ/P` is `−i/(1 + iΔ)`, which tends to `−i` as `Δ → 0`.
* `incr_1_32`: the exact discrete (1.32): with `i^m = 0`,
  `E_k[n_{k+1}B_{k+1}] − n_kB_k = −n_k(P_ks_kΔ + ΔM_k)/(1 + i_kΔ)`, `n = Λ/P`.
* `incr_1_34`: the exact discrete (1.34) form:
  `E_k[n_{k+1}(B + M)_{k+1}] − n_k(B + M)_k = −n_k(P_ks_k + (i_k − i^m_k)M_k)Δ/(1 + i_kΔ)`.
* `valuation_1_33`, `valuation_1_34`: the integrated forms: the valuation equations hold at a
  state iff the conditional transversality condition does.

**B. Continuous time on a probability space with a filtration indexed by `ℝ`.** `E_t dX = a dt`
is DEFINED (`HasDrift`) as: `X_t − X_s − ∫_s^t a` has zero conditional expectation given
`𝓕_s` for all `s ≤ t` (the martingale property of `X − ∫a`, i.e. `a` is the drift of `X`).
* `valuation_of_drift`: if `E_t dY = −g dt`, then `Y_s = E_s[Y_T] + E_s ∫_s^T g` for `T ≥ s`
  (the integration step from (1.32) to (1.33), and from the (1.34) flow to (1.34)).
* `valuation_iff_tvc`: if moreover `∫_s^T g → G` in `L¹` (`G = ∫_s^∞ g`), then
  `Y_s = E_s[G]` a.s. iff `E_s[Y_T] → 0` in `L¹`: valuation ⇔ transversality, (1.33)/(1.34)
  under uncertainty.
* `hasDrift_of_pathwise`: a process with `C¹` paths has drift equal to its pathwise derivative
  (no conditional expectation is needed: the bracket vanishes identically).
* `drift_1_32_fv`: **(1.32) for finite-variation discount factors**: if `n = Λ/P` has `C¹` paths
  with `ṅ = −in` (the nominal rate as the expected rate of decline of `Λ/P`, here exact) and
  debt follows the flow (1.31) `Ḃ = iB − Ps − Ṁ` (`i^m = 0`), then
  `E_t d(nB) = −(Λs + ΛṀ/P) dt` in the sense of `HasDrift`, and with `valuation_iff_tvc` this
  gives (1.33).

## What cannot be done, and why

When `Λ/P` has a martingale part (Brownian or jump surprises), the step in (1.32)
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)` is the product rule for a semimartingale: it needs the
stochastic integral `∫ B d(Λ/P)` (and, for jumps or diffusive `B`, the quadratic covariation
`d⟨B, Λ/P⟩`). Mathlib v4.34 has neither stochastic integrals with respect to continuous-time
martingales nor Itô's formula; it has no Lebesgue–Stieltjes calculus for signed finite-variation
paths either (only measures of monotone right-continuous functions). The alternative route for
`C¹` debt, `E_s ∫_s^t (n_t − n_r)Ḃ_r dr = 0`, needs Fubini for conditional expectations of
progressively measurable processes, which is also absent. So the product step is proved only
for `C¹` (finite-variation, continuous) `Λ/P` (`drift_1_32_fv`), exactly on the `Δ`-grid
(`incr_1_32`, `incr_1_34`), and the integration steps (1.33)–(1.34) in full generality
(`valuation_of_drift`, `valuation_iff_tvc`).
-/

namespace Cochrane.Monetarism.TidyR6StochasticDrift

open MeasureTheory Filter Topology

/-! ## A. The `Δ`-grid -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: with the nominal rate defined by
`(1 + i_kΔ)E_k[n_{k+1}] = n_k`, the conditional increment of `n = Λ/P` per unit time and per
unit of `n` is `(E_k[n_{k+1}] − n_k)/(n_kΔ) = −i_k/(1 + i_kΔ)`. -/
theorem rate_increment {Δ ik nk Enk1 : ℝ} (hΔ : Δ ≠ 0) (hn : nk ≠ 0) (hi : 1 + ik * Δ ≠ 0)
    (hrate : (1 + ik * Δ) * Enk1 = nk) : (Enk1 - nk) / (nk * Δ) = -ik / (1 + ik * Δ) := by
  have e : Enk1 = nk / (1 + ik * Δ) := by rw [eq_div_iff hi]; linarith
  rw [e]
  field_simp
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567, `E_t d(Λ/P)/(Λ/P) = −i dt` as a limit of
discrete conditional increments: `−i/(1 + iΔ) → −i` as `Δ → 0`. -/
theorem rate_increment_tendsto (ik : ℝ) :
    Tendsto (fun Δ : ℝ => -ik / (1 + ik * Δ)) (𝓝 0) (𝓝 (-ik)) := by
  have h : Tendsto (fun Δ : ℝ => 1 + ik * Δ) (𝓝 0) (𝓝 (1 + ik * 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
  simp only [mul_zero, add_zero] at h
  have := (tendsto_const_nhds (x := -ik)).div h one_ne_zero
  rw [div_one] at this
  exact this

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, exact on the `Δ`-grid.** With the pull-out
property, `B_{k+1}` known at `k`, the nominal rate `(1 + i_kΔ)E_k[n_{k+1}] = n_k` (`1 + i_kΔ ≠ 0`)
and the flow (1.31) with `i^m = 0`, `B_{k+1} = (1 + i_kΔ)B_k − (M_{k+1} − M_k) − P_ks_kΔ`:
`E_k[n_{k+1}B_{k+1}] − n_kB_k = −n_k(P_ks_kΔ + (M_{k+1} − M_k))/(1 + i_kΔ)`. -/
theorem incr_1_32 (hPO : 𝔼.PullOut) {Δ : ℝ} {n B M P s i : ℕ → Ω → ℝ} {k : ℕ} {ω : Ω}
    (hB : 𝔼.E k (B (k + 1)) = B (k + 1)) (hi : 1 + i k ω * Δ ≠ 0)
    (hrate : (1 + i k ω * Δ) * 𝔼.E k (n (k + 1)) ω = n k ω)
    (hflow : B (k + 1) ω = (1 + i k ω * Δ) * B k ω - (M (k + 1) ω - M k ω) - P k ω * s k ω * Δ) :
    𝔼.E k (n (k + 1) * B (k + 1)) ω - n k ω * B k ω =
      -(n k ω * (P k ω * s k ω * Δ + (M (k + 1) ω - M k ω)) / (1 + i k ω * Δ)) := by
  rw [mul_comm (n (k + 1)), hPO k _ _ hB, Pi.mul_apply, hflow]
  have e : 𝔼.E k (n (k + 1)) ω = n k ω / (1 + i k ω * Δ) := by
    rw [eq_div_iff hi]; linarith
  rw [e]
  field_simp
  ring

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, exact on the `Δ`-grid.** With the pull-out
property, `B_{k+1} + M_{k+1}` known at `k`, the nominal rate as in `incr_1_32` and the flow
(1.31) `B_{k+1} + M_{k+1} = (1 + i_kΔ)B_k + (1 + i^m_kΔ)M_k − P_ks_kΔ`:
`E_k[n_{k+1}(B + M)_{k+1}] − n_k(B + M)_k = −n_k(P_ks_k + (i_k − i^m_k)M_k)Δ/(1 + i_kΔ)`. -/
theorem incr_1_34 (hPO : 𝔼.PullOut) {Δ : ℝ} {n W B M P s i im : ℕ → Ω → ℝ} {k : ℕ} {ω : Ω}
    (hW : ∀ j, W j = B j + M j) (hWk : 𝔼.E k (W (k + 1)) = W (k + 1))
    (hi : 1 + i k ω * Δ ≠ 0) (hrate : (1 + i k ω * Δ) * 𝔼.E k (n (k + 1)) ω = n k ω)
    (hflow : B (k + 1) ω + M (k + 1) ω =
      (1 + i k ω * Δ) * B k ω + (1 + im k ω * Δ) * M k ω - P k ω * s k ω * Δ) :
    𝔼.E k (n (k + 1) * W (k + 1)) ω - n k ω * W k ω =
      -(n k ω * (P k ω * s k ω + (i k ω - im k ω) * M k ω) * Δ / (1 + i k ω * Δ)) := by
  rw [mul_comm (n (k + 1)), hPO k _ _ hWk, Pi.mul_apply, hW (k + 1), hW k, Pi.add_apply,
    Pi.add_apply, hflow]
  have e : 𝔼.E k (n (k + 1)) ω = n k ω / (1 + i k ω * Δ) := by
    rw [eq_div_iff hi]; linarith
  rw [e]
  field_simp
  ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, on the `Δ`-grid: valuation iff
transversality.** If `X_k = n_kB_k` satisfies `X_k = E_kX_{k+1} + g_k` (the content of
`incr_1_32`, with `g_k = n_k(P_ks_kΔ + ΔM_k)/(1 + i_kΔ)` known at `k`) and the expected flows are
summable at `ω`, then `n_kB_k = Σ_j E_k g_{k+j}` at `ω` iff `E_k[n_{k+T}B_{k+T}] → 0` at `ω`.
An application of `CashInAdvance.Stochastic.pv_iff_tvc`. -/
theorem valuation_1_33 {X g : ℕ → Ω → ℝ} (hrec : ∀ k, X k = 𝔼.E k (X (k + 1)) + g k)
    (hg : ∀ k, 𝔼.E k (g k) = g k) (k : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E k (g (k + j)) ω) :
    Tendsto (fun T => 𝔼.E k (X (k + T)) ω) atTop (𝓝 0) ↔
      X k ω = ∑' j, 𝔼.E k (g (k + j)) ω :=
  CashInAdvance.Stochastic.pv_iff_tvc 𝔼 hrec hg k ω hs

/-- Cochrane (2023), A1 §1.6, (1.32)–(1.33), p. 567, on the `Δ`-grid: `incr_1_32` at every date
and state is exactly the recursion `n_kB_k = E_k[n_{k+1}B_{k+1}] + g_k` used by
`valuation_1_33`. -/
theorem rec_of_incr_1_32 (hPO : 𝔼.PullOut) {Δ : ℝ} {n B M P s i : ℕ → Ω → ℝ}
    (hB : ∀ k, 𝔼.E k (B (k + 1)) = B (k + 1)) (hi : ∀ k ω, 1 + i k ω * Δ ≠ 0)
    (hrate : ∀ k ω, (1 + i k ω * Δ) * 𝔼.E k (n (k + 1)) ω = n k ω)
    (hflow : ∀ k ω,
      B (k + 1) ω = (1 + i k ω * Δ) * B k ω - (M (k + 1) ω - M k ω) - P k ω * s k ω * Δ) :
    ∀ k, (n k * B k) = 𝔼.E k (n (k + 1) * B (k + 1)) +
      fun ω => n k ω * (P k ω * s k ω * Δ + (M (k + 1) ω - M k ω)) / (1 + i k ω * Δ) := by
  intro k
  funext ω
  have := incr_1_32 𝔼 hPO (hB k) (hi k ω) (hrate k ω) (hflow k ω)
  simp only [Pi.add_apply, Pi.mul_apply]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, on the `Δ`-grid: valuation iff
transversality** for `Z_k = n_k(B_k + M_k)` with the interest-cost flow
`h_k = n_k(P_ks_k + (i_k − i^m_k)M_k)Δ/(1 + i_kΔ)`.
An application of `CashInAdvance.Stochastic.pv_iff_tvc`. -/
theorem valuation_1_34 {Z h : ℕ → Ω → ℝ} (hrec : ∀ k, Z k = 𝔼.E k (Z (k + 1)) + h k)
    (hh : ∀ k, 𝔼.E k (h k) = h k) (k : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E k (h (k + j)) ω) :
    Tendsto (fun T => 𝔼.E k (Z (k + T)) ω) atTop (𝓝 0) ↔
      Z k ω = ∑' j, 𝔼.E k (h (k + j)) ω :=
  CashInAdvance.Stochastic.pv_iff_tvc 𝔼 hrec hh k ω hs

/-! ## B. Continuous time: drifts on a filtered probability space -/

variable {mΩ : MeasurableSpace Ω}
variable (μ0 : Measure Ω) (𝓕0 : Filtration ℝ mΩ) (X0 a0 : ℝ → Ω → ℝ)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **`E_t dX = a dt`** for processes indexed by
`ℝ`: for all `s ≤ t`, `X_t − X_s − ∫_s^t a` is integrable with zero conditional expectation
given `𝓕_s` (the martingale property of `X − ∫a`; `a` is the drift of `X`). -/
structure HasDrift where
  int : ∀ s t, s ≤ t → Integrable (fun ω => X0 t ω - X0 s ω - ∫ r in s..t, a0 r ω) μ0
  mart : ∀ s t, s ≤ t → μ0[fun ω => X0 t ω - X0 s ω - ∫ r in s..t, a0 r ω | 𝓕0 s] =ᵐ[μ0] 0

/-- **Cochrane (2023), A1 §1.6, (1.32) ⇒ (1.33), p. 567: integrating the expected increment.**
If `E_t dY = −g dt` (`HasDrift` with drift `−g`), `Y_s` is `𝓕_s`-measurable, and `Y_s`, `Y_T`,
`∫_s^T g` are integrable (`s ≤ T`), then `Y_s = E_s[Y_T] + E_s[∫_s^T g]` almost surely. -/
theorem valuation_of_drift {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {Y g : ℝ → Ω → ℝ} (hY : HasDrift μ 𝓕 Y fun r ω => -g r ω) {s T : ℝ} (hsT : s ≤ T)
    (hYs : StronglyMeasurable[𝓕 s] (Y s)) (hYsi : Integrable (Y s) μ)
    (hYTi : Integrable (Y T) μ) (hgi : Integrable (fun ω => ∫ r in s..T, g r ω) μ) :
    Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[fun ω => ∫ r in s..T, g r ω | 𝓕 s] := by
  have hm := hY.mart s T hsT
  have e : (fun ω => Y T ω - Y s ω - ∫ r in s..T, -g r ω) =
      (Y T + fun ω => ∫ r in s..T, g r ω) - Y s := by
    funext ω; simp only [intervalIntegral.integral_neg, Pi.add_apply, Pi.sub_apply]; ring
  rw [e] at hm
  have h1 := condExp_sub (m := 𝓕 s) (hYTi.add hgi) hYsi
  have h2 := condExp_add (m := 𝓕 s) hYTi hgi
  have h3 : μ[Y s | 𝓕 s] = Y s := condExp_of_stronglyMeasurable (𝓕.le s) hYs hYsi
  filter_upwards [hm, h1, h2] with ω e1 e2 e3
  rw [e2, h3] at e1
  simp only [Pi.sub_apply, Pi.zero_apply] at e1
  have e3' : μ[Y T + fun ω => ∫ r in s..T, g r ω | 𝓕 s] ω =
      μ[Y T | 𝓕 s] ω + μ[fun ω => ∫ r in s..T, g r ω | 𝓕 s] ω := by rw [e3]; rfl
  rw [Pi.add_apply]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567, under uncertainty: valuation iff
transversality.** Under the hypotheses of `valuation_of_drift` for every `T ≥ s`, and if
`∫_s^T g → G` in `L¹` as `T → ∞` (`G = ∫_s^∞ g`, integrable), then
`Y_s = E_s[G]` almost surely iff `E_s[Y_T] → 0` in `L¹`.
Continuous-time form of `HouseholdMeasureTVC.pv_iff_tvc_ae` and
`CashInAdvance.Stochastic.pv_iff_tvc`. -/
theorem valuation_iff_tvc {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {Y g : ℝ → Ω → ℝ} (hY : HasDrift μ 𝓕 Y fun r ω => -g r ω) {s : ℝ}
    (hYs : StronglyMeasurable[𝓕 s] (Y s)) (hYi : ∀ T, Integrable (Y T) μ)
    (hgi : ∀ T, Integrable (fun ω => ∫ r in s..T, g r ω) μ) {G : Ω → ℝ} (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |(∫ r in s..T, g r ω) - G ω| ∂μ) atTop (𝓝 0)) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  set b : Ω → ℝ := fun ω => Y s ω - μ[G | 𝓕 s] ω with hb
  have hbi : Integrable b μ := (hYi s).sub integrable_condExp
  -- `E_s[Y_T] = Y_s − E_s[∫_s^T g]` and the distance to `b`
  have hclose : ∀ T, s ≤ T → |∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ - ∫ ω, |b ω| ∂μ| ≤
      ∫ ω, |(∫ r in s..T, g r ω) - G ω| ∂μ := by
    intro T hsT
    have hv := valuation_of_drift hY hsT hYs (hYi s) (hYi T) (hgi T)
    have hsub := condExp_sub (m := 𝓕 s) (hgi T) hG
    have hae : ∀ᵐ ω ∂μ, |μ[Y T | 𝓕 s] ω| - |b ω| ≤
        |μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω| ∧
        |b ω| - |μ[Y T | 𝓕 s] ω| ≤ |μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω| := by
      filter_upwards [hv, hsub] with ω e1 e2
      simp only [Pi.add_apply] at e1
      have e2' : μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω =
          μ[fun ω => ∫ r in s..T, g r ω | 𝓕 s] ω - μ[G | 𝓕 s] ω := by
        rw [← Pi.sub_apply (μ[fun ω => ∫ r in s..T, g r ω | 𝓕 s]), ← e2]; rfl
      have ea : μ[Y T | 𝓕 s] ω = b ω - μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω := by
        rw [e2']; simp only [hb]; linarith
      rw [ea]
      constructor
      · have := abs_sub (b ω) (μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω)
        linarith
      · have := abs_sub_abs_le_abs_sub (b ω)
          (b ω - μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω)
        simp only [sub_sub_cancel] at this
        linarith
    have hYTc : Integrable (fun ω => |μ[Y T | 𝓕 s] ω|) μ := integrable_condExp.abs
    have hbc : Integrable (fun ω => |b ω|) μ := hbi.abs
    have hdc : Integrable (fun ω => |μ[fun ω => (∫ r in s..T, g r ω) - G ω | 𝓕 s] ω|) μ :=
      integrable_condExp.abs
    have hle := integral_abs_condExp_le (μ := μ) (m := 𝓕 s)
      (fun ω => (∫ r in s..T, g r ω) - G ω)
    rw [abs_le]
    constructor
    · have := integral_mono_ae (hbc.sub hYTc) hdc (by
        filter_upwards [hae] with ω h; simp only [Pi.sub_apply]; linarith [h.2])
      simp only [Pi.sub_apply] at this
      rw [integral_sub hbc hYTc] at this
      linarith
    · have := integral_mono_ae (hYTc.sub hbc) hdc (by
        filter_upwards [hae] with ω h; simp only [Pi.sub_apply]; linarith [h.1])
      simp only [Pi.sub_apply] at this
      rw [integral_sub hYTc hbc] at this
      linarith
  have hlim : Tendsto (fun T => ∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ) atTop (𝓝 (∫ ω, |b ω| ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hconv
    filter_upwards [eventually_ge_atTop s] with T hT
    rw [Real.norm_eq_abs]
    exact hclose T hT
  constructor
  · intro h
    have hb0 : ∫ ω, |b ω| ∂μ = 0 := by
      have : (fun ω => |b ω|) =ᵐ[μ] 0 := by
        filter_upwards [h] with ω hω; simp [hb, hω]
      rw [integral_congr_ae this]; simp
    rwa [hb0] at hlim
  · intro h
    have hb0 : ∫ ω, |b ω| ∂μ = 0 := tendsto_nhds_unique hlim h
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (b ω)) hbi.abs).1 hb0
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero, hb] at hω
    linarith

/-- Cochrane (2023), A1 §1.6, p. 568 ("`P_tW_t` is differentiable"): **a process with `C¹`
paths has drift equal to its pathwise derivative.** If every path `t ↦ X_t(ω)` has derivative
`a_t(ω)` and `t ↦ a_t(ω)` is continuous, then `X_t − X_s − ∫_s^t a = 0` identically, so
`E_t dX = a dt` (for any finite measure and filtration). -/
theorem hasDrift_of_pathwise {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {X a : ℝ → Ω → ℝ}
    (hd : ∀ ω r, HasDerivAt (fun t => X t ω) (a r ω) r) (hc : ∀ ω, Continuous fun r => a r ω) :
    HasDrift μ 𝓕 X a := by
  have hz : ∀ s t, (fun ω => X t ω - X s ω - ∫ r in s..t, a r ω) = 0 := by
    intro s t
    funext ω
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd ω r)
      ((hc ω).intervalIntegrable s t)]
    simp
  refine ⟨fun s t _ => by rw [hz s t]; exact integrable_zero _ _ _, fun s t _ => ?_⟩
  rw [hz s t, condExp_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, for finite-variation discount factors.** Let
`n = Λ/P` have `C¹` paths with `ṅ = −in` (the nominal rate is the rate of decline of `Λ/P`),
and debt have `C¹` paths following the flow (1.31) with `i^m = 0`, `Ḃ = iB − Ps − Ṁ` (`dM` the
money growth `Ṁ`), with `n(Ps + Ṁ)` continuous. Then `E_t d(nB) = −(ΛP⁻¹·Ps + ΛP⁻¹Ṁ) dt`,
i.e. `HasDrift` of `nB` with drift
`−n(Ps + Ṁ)`; by `valuation_iff_tvc` this gives (1.33). -/
theorem drift_1_32_fv {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {n B P s i dM : ℝ → Ω → ℝ}
    (hn : ∀ ω r, HasDerivAt (fun t => n t ω) (-(i r ω * n r ω)) r)
    (hB : ∀ ω r, HasDerivAt (fun t => B t ω) (i r ω * B r ω - P r ω * s r ω - dM r ω) r)
    (hc : ∀ ω, Continuous fun r => n r ω * (P r ω * s r ω + dM r ω)) :
    HasDrift μ 𝓕 (fun t ω => n t ω * B t ω) fun r ω => -(n r ω * (P r ω * s r ω + dM r ω)) := by
  refine hasDrift_of_pathwise (fun ω r => ((hn ω r).mul (hB ω r)).congr_deriv (by ring))
    fun ω => (hc ω).neg

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, under uncertainty with a finite-variation
discount factor: valuation iff transversality.** Under the hypotheses of `drift_1_32_fv`, with
`n_sB_s` `𝓕_s`-measurable, `n_TB_T` and `∫_s^T n(Ps + Ṁ)` integrable, and `∫_s^T n(Ps + Ṁ) → G`
in `L¹`: `n_sB_s = E_s[G]` (`B_s/P_s = E_s∫_s^∞ (Λ_τ/Λ_s)(s_τ + Ṁ_τ/P_τ)dτ`) almost surely iff
`E_s[n_TB_T] → 0` in `L¹`.
Stochastic form of `ContinuousTime.money_printing_iff`. -/
theorem valuation_1_33_fv {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {n B P s i dM : ℝ → Ω → ℝ}
    (hn : ∀ ω r, HasDerivAt (fun t => n t ω) (-(i r ω * n r ω)) r)
    (hB : ∀ ω r, HasDerivAt (fun t => B t ω) (i r ω * B r ω - P r ω * s r ω - dM r ω) r)
    (hc : ∀ ω, Continuous fun r => n r ω * (P r ω * s r ω + dM r ω)) {t0 : ℝ}
    (hYs : StronglyMeasurable[𝓕 t0] fun ω => n t0 ω * B t0 ω)
    (hYi : ∀ T, Integrable (fun ω => n T ω * B T ω) μ)
    (hgi : ∀ T, Integrable (fun ω => ∫ r in t0..T, n r ω * (P r ω * s r ω + dM r ω)) μ)
    {G : Ω → ℝ} (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |(∫ r in t0..T, n r ω * (P r ω * s r ω + dM r ω)) - G ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => n t0 ω * B t0 ω) =ᵐ[μ] μ[G | 𝓕 t0] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => n T ω * B T ω | 𝓕 t0] ω| ∂μ) atTop (𝓝 0) :=
  valuation_iff_tvc (Y := fun t ω => n t ω * B t ω)
    (g := fun r ω => n r ω * (P r ω * s r ω + dM r ω)) (drift_1_32_fv hn hB hc) hYs hYi hgi hG
    hconv

end Cochrane.Monetarism.TidyR6StochasticDrift
