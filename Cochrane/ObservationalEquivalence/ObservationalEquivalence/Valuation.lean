/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.FiscalRec
import ObservationalEquivalence.ExpectationTools

/-!
# The government debt valuation equation in the frictionless linear model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–497,
eq. (22.2) (and (16.20)–(16.22), p. 373): the frictionless linear model
`i_t = E_t π_{t+1}` (`Fisher`) and `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`Flow`), with
`v_t` the real value of debt at the end of date `t` and `s̃` the real primary surplus.

"The government debt valuation formula results from iterating (22.2) forward and imposing the
transversality condition" (p. 495), and "the government debt valuation equation is an equilibrium
condition for all of these models" (p. 497). This module proves both: the valuation equation
`v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j}` and the unexpected-inflation identity
`ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑_{j ≥ 0} ρʲ s̃_{t+1+j}` follow from the Fisher equation, the flow
condition and the transversality condition alone — no policy rule is used, so they hold in every
regime (`valuation_all_regimes` in `StarredModel`).

## Main results

* `flow_iff_surprise`: given the Fisher equation, (22.2) is
  `ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}` ((16.22), (22.11)).
* `E_realReturn`: the ex-post real return `r_{t+1} = i_t − π_{t+1}` has `E_t r_{t+1+j} = 0`.
* `telescope` (ex post) and `telescope_E`:
  `v_t = ∑_{j<T} ρʲ E_t s̃_{t+1+j} + ρᵀ E_t v_{t+T}`.
* `tvc_iff_valuation`: the transversality condition `ρᵀ E_t v_{t+T} → 0` holds iff the partial
  sums of the present value converge to `v_t` (both directions); `valuation_tsum`,
  `valuation_E_exPost`: with bounded surpluses, `v_t = ∑' ρʲ E_t s̃_{t+1+j} = E_t ∑' ρʲ s̃_{t+1+j}`.
* `unexpected_inflation`, `unexpected_inflation_news`:
  `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`.
* `tvc_of_bounded`: bounded debt satisfies the transversality condition.

The innovation operator `innov` (`ΔE_{t+1}`), the ex-post present value `pvExPost` and the
flow-iteration lemmas `flow_telescope`, `pv_of_flow` are shared with chain B and live in
`ExpectationTools`; `surprise_eq_innov` identifies the surprise of an adapted process with its
innovation.
-/

namespace Cochrane.ObservationalEquivalence.Valuation

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply pvExPost
  summable_pow_mul_of_bounded tendsto_pow_mul_of_bounded flow_telescope pv_of_flow)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Definitions -/

/-- Cochrane (2023), eq. (22.2), p. 495 (and (16.20), p. 373): the Fisher equation
`i_t = E_t π_{t+1}`. -/
def Fisher (i π : ℕ → Ω → ℝ) : Prop := ∀ t, i t = 𝔼.E t (π (t + 1))

/-- Cochrane (2023), eq. (22.2), p. 495, and (22.11), p. 501: the linearised flow condition
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def Flow (ρ : ℝ) (v i π s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), (22.1), p. 495: unexpected inflation `ΔE_{t+1} x_{t+1} = x_{t+1} − E_t x_{t+1}`
of an adapted process. -/
def surprise (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := x (t + 1) - 𝔼.E t (x (t + 1))

/-- Cochrane (2023), §22.1, p. 495 (the real return in (22.2)): the ex-post real return on
one-period nominal debt, `r_{t+1} = i_t − π_{t+1}`. -/
def realReturn (i π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := i t - π (t + 1)

/-- Cochrane (2023), §22.1, p. 495 ("imposing the transversality condition"): at every date and
state, `lim_{T→∞} ρᵀ E_t v_{t+T} = 0`. -/
def TVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), §22.1, p. 495: the present value of surpluses as seen at date `m`,
`E_m ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`, written termwise as a genuine infinite sum. -/
noncomputable def pvE (ρ : ℝ) (s : ℕ → Ω → ℝ) (m t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω

/-! ### Expectational facts -/

/-- Cochrane (2023), (22.1), p. 495: surprises are unforecastable, `E_t ΔE_{t+1} x_{t+1} = 0`. -/
theorem E_surprise (x : ℕ → Ω → ℝ) (t : ℕ) : 𝔼.E t (surprise 𝔼 x t) = 0 := by
  rw [surprise, map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), (22.1), p. 495: later surprises are unforecastable,
`E_t ΔE_{t+k+1} x_{t+k+1} = 0`. -/
theorem E_surprise_later (x : ℕ → Ω → ℝ) (t k : ℕ) : 𝔼.E t (surprise 𝔼 x (t + k)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), E_surprise, map_zero]

/-- Cochrane (2023), (22.1), p. 495: for an adapted process the surprise is the revision of
expectations, `x_{t+1} − E_t x_{t+1} = ΔE_{t+1} x_{t+1}`. -/
theorem surprise_eq_innov {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    surprise 𝔼 x t = innov 𝔼 t (x (t + 1)) := by
  rw [surprise, innov_apply, hx (t + 1)]

/-- Cochrane (2023), (22.2), p. 495: with the Fisher equation the flow condition reads
`ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}` ((16.22), p. 373; (22.10)–(22.11), p. 501). -/
theorem flow_iff_surprise {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) :
    Flow ρ v i π s ↔ ∀ t, ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) := by
  refine forall_congr' fun t => ?_
  rw [hF t, surprise]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), (22.2), p. 495: the flow condition in terms of the ex-post real return,
`ρ v_{t+1} = v_t + r_{t+1} − s̃_{t+1}`. -/
theorem flow_iff_realReturn {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} :
    Flow ρ v i π s ↔ ∀ t, ρ • v (t + 1) = v t + realReturn i π t - s (t + 1) := by
  refine forall_congr' fun t => ?_
  rw [realReturn]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), §22.1, p. 495: with the Fisher equation, expected real returns are zero at
every horizon, `E_t r_{t+1+j} = 0` (constant real rate in the frictionless model). -/
theorem E_realReturn {i π : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) (t j : ℕ) :
    𝔼.E t (realReturn i π (t + j)) = 0 := by
  rw [realReturn, hF (t + j), map_sub, 𝔼.tower (Nat.le_add_right t j), sub_self]

/-! ### Iterating the flow condition -/

omit 𝔼 in
/-- Cochrane (2023), §22.1, p. 495 (iterating (22.2) forward, ex post):
`v_t = ∑_{j<T} ρʲ (s̃_{t+1+j} − r_{t+1+j}) + ρᵀ v_{t+T}`. -/
theorem telescope {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (h : Flow ρ v i π s) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • (s (t + 1 + j) - realReturn i π (t + j)) +
      ρ ^ T • v (t + T) := by
  rw [flow_telescope (ρ := ρ) (v := v) (y := fun k => s (k + 1) - realReturn i π k)
    (fun k => by rw [h k, realReturn]; abel) t T]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show t + j + 1 = t + 1 + j by omega]

/-- Cochrane (2023), §22.1, p. 495 (iterating (22.2) forward under expectations):
`v_t = ∑_{j<T} ρʲ E_t s̃_{t+1+j} + ρᵀ E_t v_{t+T}`. -/
theorem telescope_E {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • 𝔼.E t (s (t + 1 + j)) + ρ ^ T • 𝔼.E t (v (t + T)) := by
  have h1 := congrArg (𝔼.E t) (telescope h t T)
  rw [hv t] at h1
  rw [h1, map_add, map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_sub, E_realReturn 𝔼 hF t j, sub_zero]

/-- Cochrane (2023), §22.1, p. 495: iterating (22.2) and imposing the transversality condition
gives the valuation equation: the partial sums `∑_{j<T} ρʲ E_t s̃_{t+1+j}` converge to `v_t`. -/
theorem valuation_of_tvc {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) atTop
      (𝓝 (v t ω)) := by
  have hy : ∀ k, ρ • v (k + 1) = v k - (s (k + 1) - realReturn i π (k + 1 - 1)) :=
    fun k => by
      rw [Nat.add_sub_cancel, h k, realReturn]
      abel
  refine (pv_of_flow 𝔼 (y := fun m => s m - realReturn i π (m - 1)) hy t (hv t) ω
    (htvc t ω)).congr fun T =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [show t + 1 + j - 1 = t + j by omega, map_sub, Pi.sub_apply, E_realReturn 𝔼 hF t j,
    Pi.zero_apply, sub_zero]

/-- Cochrane (2023), §22.1, p. 495 (converse): if the present value converges to `v_t` at every
date and state, the transversality condition holds. -/
theorem tvc_of_valuation {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (hpv : ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
      atTop (𝓝 (v t ω))) : TVC 𝔼 ρ v := by
  intro t ω
  have hT : ∀ T, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω := by
    intro T
    have := congrFun (telescope_E 𝔼 hF h hv t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
    linarith
  simp_rw [hT]
  simpa using (tendsto_const_nhds (x := v t ω)).sub (hpv t ω)

/-- Cochrane (2023), §22.1, p. 495 (both directions): given the Fisher equation and the flow
condition, the transversality condition holds iff the valuation equation holds at every date. -/
theorem tvc_iff_valuation {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v) :
    TVC 𝔼 ρ v ↔ ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
      atTop (𝓝 (v t ω)) :=
  ⟨fun htvc => valuation_of_tvc 𝔼 hF h hv htvc, tvc_of_valuation 𝔼 hF h hv⟩

/-! ### Genuine infinite sums -/

/-- Cochrane (2023), §22.1, p. 495: with `|ρ| < 1` and bounded surpluses the present value is
absolutely summable. -/
theorem pvE_summable {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (m t : ℕ) (ω : Ω) : Summable (fun j => ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω) :=
  summable_pow_mul_of_bounded hρ (x := fun j => 𝔼.E m (s (t + 1 + j)) ω)
    fun j => 𝔼.abs_E_le (hs (t + 1 + j)) m ω

/-- Cochrane (2023), §22.1, p. 495: the present value of bounded surpluses is bounded by
`M/(1 − |ρ|)`. -/
theorem abs_pvE_le {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (m t : ℕ) (ω : Ω) : |pvE 𝔼 ρ s m t ω| ≤ M / (1 - |ρ|) := by
  have hg : HasSum (fun j : ℕ => M * |ρ| ^ j) (M / (1 - |ρ|)) := by
    have := (hasSum_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun j => ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1 + j)) m ω)
      (pow_nonneg (abs_nonneg ρ) j)
  simpa [pvE, Real.norm_eq_abs] using this

/-- Cochrane (2023), §22.1, p. 495: the valuation equation as a genuine infinite sum,
`v_t = ∑_{j ≥ 0} ρʲ E_t s̃_{t+1+j}` (bounded surpluses, `|ρ| < 1`). -/
theorem valuation_tsum {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) : v t = pvE 𝔼 ρ s t t := by
  funext ω
  exact tendsto_nhds_unique (valuation_of_tvc 𝔼 hF h hv htvc t ω)
    (pvE_summable 𝔼 hρ hs t t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), §22.1, p. 495: `E_m` of the ex-post present value is the present value of
expected surpluses, `E_m ∑ ρʲ s̃_{t+1+j} = ∑ ρʲ E_m s̃_{t+1+j}` (`|ρ| < 1`, bounded `s̃`). -/
theorem E_pvExPost {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (m t : ℕ) : 𝔼.E m (pvExPost ρ s t) = pvE 𝔼 ρ s m t := by
  funext ω
  have hb : ∀ j ω', |(fun j ω => ρ ^ j * s (t + 1 + j) ω) j ω'| ≤ |ρ| ^ j * M :=
    fun j ω' => by
      simp only
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hs _ ω') (pow_nonneg (abs_nonneg ρ) j)
  have h1 := 𝔼.E_tsum (abs_nonneg ρ) hρ hb m ω
  change 𝔼.E m (fun ω' => ∑' j, ρ ^ j * s (t + 1 + j) ω') ω = _
  rw [h1]
  refine tsum_congr fun j => ?_
  change 𝔼.E m (ρ ^ j • s (t + 1 + j)) ω = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), §22.1, p. 495: the valuation equation in the book's form
`v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`. -/
theorem valuation_E_exPost {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) : v t = 𝔼.E t (pvExPost ρ s t) := by
  rw [E_pvExPost 𝔼 hρ hs, valuation_tsum 𝔼 hρ hs hF h hv htvc]

/-- Cochrane (2023), §22.1, p. 495: splitting off the first term,
`E_{t+1} ∑ ρʲ s̃_{t+1+j} = s̃_{t+1} + ρ E_{t+1} ∑ ρʲ s̃_{t+2+j}` (adapted, bounded `s̃`). -/
theorem pvE_succ_split {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (hsa : 𝔼.Adapted s) (t : ℕ) :
    pvE 𝔼 ρ s (t + 1) t = s (t + 1) + ρ • pvE 𝔼 ρ s (t + 1) (t + 1) := by
  funext ω
  simp only [pvE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [(pvE_summable 𝔼 hρ hs (t + 1) t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero,
    hsa (t + 1), ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), §22.1, p. 495 and (16.24), p. 373: unexpected inflation equals minus the
revision in the present value of surpluses,
`ΔE_{t+1}π_{t+1} = −(E_{t+1} − E_t) ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`. -/
theorem unexpected_inflation {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -(pvE 𝔼 ρ s (t + 1) t - pvE 𝔼 ρ s t t) := by
  have h1 := ((flow_iff_surprise 𝔼 hF).mp h) t
  have e1 := valuation_tsum 𝔼 hρ hs hF h hv htvc t
  have e2 := valuation_tsum 𝔼 hρ hs hF h hv htvc (t + 1)
  rw [pvE_succ_split 𝔼 hρ hs hsa t, ← e2, ← e1]
  funext ω
  have := congrFun h1 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
  linarith

/-- Cochrane (2023), §22.1, p. 495 (`|ρ| < 1`): unexpected inflation is minus the news about
the ex-post present value of surpluses, `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`. -/
theorem unexpected_inflation_news {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -innov 𝔼 t (pvExPost ρ s t) := by
  rw [unexpected_inflation 𝔼 hρ hs hsa hF h hv htvc t, innov_apply, E_pvExPost 𝔼 hρ hs,
    E_pvExPost 𝔼 hρ hs]

/-- Cochrane (2023), §22.1, p. 495: bounded debt satisfies the transversality condition when
`|ρ| < 1`. -/
theorem tvc_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v) :
    TVC 𝔼 ρ v := by
  obtain ⟨M, hM⟩ := hv
  intro t ω
  exact tendsto_pow_mul_of_bounded hρ (x := fun T => 𝔼.E t (v (t + T)) ω)
    fun T => 𝔼.abs_E_le (hM (t + T)) t ω

/-- Cochrane (2023), §22.1, p. 495: the transversality condition is linear — it holds for a
difference of two processes that satisfy it. -/
theorem tvc_sub {ρ : ℝ} {v w : ℕ → Ω → ℝ} (hv : TVC 𝔼 ρ v) (hw : TVC 𝔼 ρ w) :
    TVC 𝔼 ρ (fun t => v t - w t) := by
  intro t ω
  have := (hv t ω).sub (hw t ω)
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  simp only [map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), §22.1, p. 495: the transversality condition holds for a sum of two processes
that satisfy it. -/
theorem tvc_add {ρ : ℝ} {v w : ℕ → Ω → ℝ} (hv : TVC 𝔼 ρ v) (hw : TVC 𝔼 ρ w) :
    TVC 𝔼 ρ (fun t => v t + w t) := by
  intro t ω
  have := (hv t ω).add (hw t ω)
  rw [add_zero] at this
  refine this.congr fun T => ?_
  simp only [map_add, Pi.add_apply]
  ring

end Cochrane.ObservationalEquivalence.Valuation
