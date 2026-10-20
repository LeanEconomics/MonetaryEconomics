/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.ForwardSolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The simple new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, eqs. (5.1)–(5.4),
(5.6), (5.8), pp. 117–120 and p. 123; Online Appendix A1, §1.7, pp. 569–570.

The model is stated for an arbitrary `ExpectationSystem`, so every result holds under perfect
foresight and under genuine uncertainty.

## Main results

* (5.1)–(5.2): `IS`, `PC`, `NK`. The Euler-equation derivation (p. 118): `euler_log_form` (the
  exact consumer first-order condition is `log(1 + I_t) − δ = −log E_t[exp(X_{t+1})]`,
  `X = −γΔc − π`), `euler_deriv` (along any bounded direction that map has derivative
  `γ E_t Δc_{t+1} + E_t π_{t+1}` at the steady state), and `is_iff_linear_euler` (the derivative
  equation is (5.1) with `σ = 1/γ`, the constant `δ` suppressed).
* (5.3): `is_iterate`, `eq_5_3` — the sum converges to `−x_t/σ` iff `E_t x_{t+k} → 0`.
* (5.4): `pc_iterate`, `eq_5_4_tvc` (iff form), `eq_5_4` (bounded processes, genuine `tsum`).
* The flexible-price limit (p. 119): `abs_x_le` (`|x| ≤ (1 + β)M/κ`), `tendsto_x_kappa`.
* (5.6): `lam1`, `lam2`, `disc_pos`, `lam_sum`, `lam_prod`, `lam1_root`, `lam2_root`,
  `sigma_kappa_eq`, `one_lt_lam1`, `lam2_lt_one`, `lam2_pos`, `lam2_lt_lam1`.
* (5.8): `eq_5_8`, `long_run_one` (A1 p. 570), `coeff_sum_one` (the coefficients of (5.5) sum
  to one, as genuine geometric series).
* Comparative statics used later: `lam1_strictMonoOn` (λ₁ is strictly increasing in κ),
  `tendsto_lam1_zero` (λ₁ → 1 as κ → 0⁺), `tendsto_lam1_atTop` (λ₁ → ∞ as κ → ∞),
  `tendsto_lam2_atTop` (λ₂ → 0), `tendsto_coef_atTop` (`σκ/(λ₁ − λ₂) → 1`).
* Long-run tradeoff (p. 123): `pc_const_iff`, `tradeoff`, `nk_const_iff` (constant equilibria
  are Fisherian, `i = π`), `no_tradeoff_beta_one`; the indexed Phillips curve `IPC`,
  `ipc_const_iff`, `ipc_no_tradeoff`.
-/

namespace Cochrane.StickyPriceFiscal.NKModel

open Filter Topology Asymptotics

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model (5.1)–(5.2) -/

/-- Cochrane (2023), eq. (5.1), p. 118: the intertemporal-substitution ("IS") equation
`x_t = E_t x_{t+1} − σ(i_t − E_t π_{t+1})`. -/
def IS (σ : ℝ) (i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1)))

/-- Cochrane (2023), eq. (5.2), p. 118: the new-Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ x_t`. -/
def PC (β κ : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118: the simple new-Keynesian model. -/
def NK (σ β κ : ℝ) (i x π : ℕ → Ω → ℝ) : Prop := IS 𝔼 σ i x π ∧ PC 𝔼 β κ x π

/-! ### The Euler equation behind (5.1) -/

/-- Cochrane (2023), p. 118: the consumer first-order condition
`1 = E_t[β (C_{t+1}/C_t)^{−γ} (1 + I_t) P_t/P_{t+1}]` at date `t`. -/
def EulerExact (β γ : ℝ) (I C P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  𝔼.E t (fun ω => β * (C (t + 1) ω / C t ω) ^ (-γ) * (1 + I t ω) * (P t ω / P (t + 1) ω)) =
    fun _ => 1

/-- Cochrane (2023), p. 118: the log growth term `X_{t+1} = −γ(c_{t+1} − c_t) − π_{t+1}` with
`c = log C` and `π_{t+1} = log(P_{t+1}/P_t)`. -/
noncomputable def eulerX (γ : ℝ) (C P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => -γ * (Real.log (C (t + 1) ω) - Real.log (C t ω)) -
    (Real.log (P (t + 1) ω) - Real.log (P t ω))

/-- Cochrane (2023), p. 118: with positive consumption and prices, a date-`t` known rate and
`E_t` pulling out known factors, the first-order condition holds iff, with `δ = −log β`,
`log(1 + I_t) − δ = −log E_t[exp(X_{t+1})]` (the exact form of the Euler equation; the book's
equation is its first-order expansion, `euler_deriv`). -/
theorem euler_log_form (hpull : 𝔼.PullOut) {β γ : ℝ} (hβ : 0 < β) {I C P : ℕ → Ω → ℝ}
    (t : ℕ) (hC : ∀ s ω, 0 < C s ω) (hP : ∀ s ω, 0 < P s ω) (hI : ∀ ω, 0 < 1 + I t ω)
    (hIa : 𝔼.E t (I t) = I t)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => Real.exp (eulerX γ C P t ω')) ω) :
    EulerExact 𝔼 β γ I C P t ↔ ∀ ω, Real.log (1 + I t ω) - (-Real.log β) =
      -Real.log (𝔼.E t (fun ω' => Real.exp (eulerX γ C P t ω')) ω) := by
  set a : Ω → ℝ := fun ω => β * (1 + I t ω) with ha
  have hint : (fun ω => β * (C (t + 1) ω / C t ω) ^ (-γ) * (1 + I t ω) * (P t ω / P (t + 1) ω))
      = a * fun ω' => Real.exp (eulerX γ C P t ω') := by
    funext ω
    have h1 := hC (t + 1) ω
    have h2 := hC t ω
    have h3 := hP t ω
    have h4 := hP (t + 1) ω
    simp only [ha, Pi.mul_apply, eulerX]
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div h1.ne' h2.ne', Real.exp_sub,
      Real.exp_sub (Real.log _), Real.exp_log h4, Real.exp_log h3,
      mul_comm (Real.log (C (t + 1) ω) - Real.log (C t ω)) (-γ)]
    field_simp
  have haE : 𝔼.E t a = a := by
    have : a = (fun _ => β) + β • I t + fun _ => (0 : ℝ) := by
      funext ω
      simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, map_add, map_add, map_smul, 𝔼.const, 𝔼.const, hIa]
  unfold EulerExact
  rw [hint, hpull t a _ haE, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.mul_apply, ha]
  have hEω := hE ω
  have hIω := hI ω
  rw [sub_neg_eq_add, ← Real.log_inv, ← Real.log_mul hIω.ne' hβ.ne']
  constructor
  · intro h
    congr 1
    field_simp
    linarith
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (inv_pos.mpr hEω)) h
    field_simp at h'
    linarith

/-- Cochrane (2023), p. 118 (derivative of an expectation, used to linearise): for a
bounded random variable `X`, `ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0` (restated from
the Woodford Chapter 2 project). -/
theorem hasDerivAt_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω) (𝔼.E t X ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : ℝ => 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
      𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω) =O[𝓝 0] fun h => h ^ 2 := by
    refine IsBigO.of_bound (|K| ^ 2) ?_
    have hball : Metric.ball (0 : ℝ) (1 / (|K| + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
      intro ω'
      have hx : |h * X ω'| ≤ 1 := by
        rw [abs_mul]
        have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
        have h2 : |h| * (|K| + 1) ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hh
          exact hh.le
        nlinarith [abs_nonneg h, abs_nonneg (X ω')]
      refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
      rw [mul_pow, mul_comm (|K| ^ 2)]
      have : X ω' ^ 2 ≤ |K| ^ 2 := by
        rw [← sq_abs (X ω')]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
    have heq : 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
        𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω =
        𝔼.E t (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') ω := by
      have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
          (fun ω' => Real.exp (h * X ω')) - (fun _ => (1 : ℝ)) - h • X := by
        funext ω'
        simp
      rw [hfun, map_sub, map_sub, map_smul, 𝔼.const]
      simp [𝔼.const]
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact 𝔼.abs_E_le hrem t ω
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

/-- Cochrane (2023), p. 118 ("linearize"): along a bounded direction `X`,
`ε ↦ −log E_t[exp(ε X)]` has derivative `−E_t X` at the steady state `ε = 0`. -/
theorem hasDerivAt_log_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω))
      (-𝔼.E t X ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h := (hasDerivAt_E_exp 𝔼 hX t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at h
  exact h.neg

/-- Cochrane (2023), p. 118: along a bounded direction of log deviations `(c, π)` (with `c`
adapted), the right-hand side of the exact Euler equation `euler_log_form`, scaled by `ε`, has
derivative `γ(E_t c_{t+1} − c_t) + E_t π_{t+1}` at the steady state. -/
theorem euler_deriv {K γ : ℝ} {c π : ℕ → Ω → ℝ} (hca : 𝔼.Adapted c) (t : ℕ)
    (hb : ∀ ω, |-γ * (c (t + 1) ω - c t ω) - π (t + 1) ω| ≤ K) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (ε * (-γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω'))) ω))
      (γ * (𝔼.E t (c (t + 1)) ω - c t ω) + 𝔼.E t (π (t + 1)) ω) 0 := by
  have h := hasDerivAt_log_E_exp 𝔼 (X := fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω')
    hb t ω
  convert h using 1
  have hfun : (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω') =
      (-γ) • (c (t + 1) - c t) - π (t + 1) := rfl
  rw [hfun, map_sub, map_smul, map_sub, hca t]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 118: the linearised Euler equation
`i_t − δ = γ(E_t x_{t+1} − x_t) + E_t π_{t+1}` (`euler_deriv` with `c = x`) is (5.1)
`x_t = E_t x_{t+1} − σ((i_t − δ) − E_t π_{t+1})` with `σ = 1/γ`; measuring `i` as a deviation
from `δ` ("suppressing constants") gives (5.1) exactly. -/
theorem is_iff_linear_euler {γ σ δ : ℝ} (hγσ : γ * σ = 1) (it xt Ex Eπ : ℝ) :
    it - δ = γ * (Ex - xt) + Eπ ↔ xt = Ex - σ * ((it - δ) - Eπ) := by
  have hγ : γ ≠ 0 := by
    rintro rfl
    simp at hγσ
  constructor
  · intro h
    rw [h]
    linear_combination (Ex - xt) * hγσ
  · intro h
    rw [h]
    linear_combination (-(it - δ - Eπ)) * hγσ

/-! ### (5.3): integrating the IS equation forward -/

/-- Cochrane (2023), eq. (5.1), p. 118: with an adapted rate, every solution of the IS equation
is adapted. -/
theorem is_adapted {σ : ℝ} {i x π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (h : IS 𝔼 σ i x π) :
    𝔼.Adapted x := by
  intro t
  conv_lhs => rw [h t]
  rw [map_sub, map_smul, map_sub, 𝔼.E_E_self, 𝔼.E_E_self, hi t, ← h t]

/-- Cochrane (2023), eq. (5.3), p. 118 (finite horizon):
`x_t = E_t x_{t+k} − σ ∑_{j<k} E_t(i_{t+j} − π_{t+j+1})`. -/
theorem is_iterate {σ : ℝ} {i x π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (h : IS 𝔼 σ i x π)
    (t k : ℕ) : x t = 𝔼.E t (x (t + k)) -
      σ • ∑ j ∈ Finset.range k, 𝔼.E t (i (t + j) - π (t + j + 1)) := by
  induction k with
  | zero => simp [is_adapted 𝔼 hi h t]
  | succ k ih =>
    have hk := h (t + k)
    have hE : 𝔼.E t (x (t + k)) = 𝔼.E t (x (t + (k + 1))) -
        σ • 𝔼.E t (i (t + k) - π (t + k + 1)) := by
      conv_lhs => rw [hk]
      rw [map_sub, map_smul, map_sub, 𝔼.tower (Nat.le_add_right t k),
        𝔼.tower (Nat.le_add_right t k), map_sub]
      rfl
    rw [ih, hE, Finset.sum_range_succ, smul_add]
    abel

/-- Cochrane (2023), eq. (5.3), p. 118: the infinite-horizon form
`x_t = −σ E_t ∑_{j≥0} (i_{t+j} − π_{t+j+1})` holds (partial sums converging to `−x_t/σ`) **iff**
`E_t x_{t+k} → 0`; the book's integration silently assumes this terminal condition. -/
theorem eq_5_3 {σ : ℝ} (hσ : σ ≠ 0) {i x π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i)
    (h : IS 𝔼 σ i x π) (t : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E t (x (t + k)) ω) atTop (𝓝 0) ↔
      Tendsto (fun k => ∑ j ∈ Finset.range k, 𝔼.E t (i (t + j) - π (t + j + 1)) ω) atTop
        (𝓝 (-x t ω / σ)) := by
  have hS : ∀ k, ∑ j ∈ Finset.range k, 𝔼.E t (i (t + j) - π (t + j + 1)) ω =
      (𝔼.E t (x (t + k)) ω - x t ω) / σ := by
    intro k
    have := congrFun (is_iterate 𝔼 hi h t k) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
    field_simp
    linarith
  simp_rw [hS]
  constructor
  · intro hx
    have := (hx.sub_const (x t ω)).div_const σ
    simpa using this
  · intro hs
    have := (hs.const_mul σ).add_const (x t ω)
    have hlim : σ * (-x t ω / σ) + x t ω = 0 := by field_simp; ring
    rw [hlim] at this
    refine this.congr fun k => ?_
    field_simp
    ring

/-! ### (5.4): integrating the Phillips curve forward -/

/-- Cochrane (2023), eq. (5.2), p. 118: the Phillips curve is the scalar forward equation
`π_t = β E_t π_{t+1} + (κ x)_t` of the core module. -/
theorem pc_iff_solves {β κ : ℝ} {x π : ℕ → Ω → ℝ} :
    PC 𝔼 β κ x π ↔ ForwardSolution.Solves 𝔼 β (κ • x) π := Iff.rfl

/-- Cochrane (2023), eq. (5.4), p. 119 (finite horizon):
`π_t = βᵏ E_t π_{t+k} + κ ∑_{j<k} βʲ E_t x_{t+j}`. -/
theorem pc_iterate {β κ : ℝ} {x π : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (h : PC 𝔼 β κ x π)
    (t k : ℕ) (ω : Ω) : π t ω = β ^ k * 𝔼.E t (π (t + k)) ω +
      κ * ∑ j ∈ Finset.range k, β ^ j * 𝔼.E t (x (t + j)) ω := by
  have hxa : 𝔼.Adapted (κ • x) := fun s => by
    rw [Pi.smul_apply, map_smul, hx s]
  have := congrFun (ForwardSolution.iterate_A15 𝔼 hxa h t k) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_smul] at this
  rw [this, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Cochrane (2023), eq. (5.4), p. 119: `π_t = κ E_t ∑ βʲ x_{t+j}` (partial sums converging)
**iff** `βᵏ E_t π_{t+k} → 0`. -/
theorem eq_5_4_tvc {β κ : ℝ} {x π : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (h : PC 𝔼 β κ x π)
    (t : ℕ) (ω : Ω) : Tendsto (fun k => β ^ k * 𝔼.E t (π (t + k)) ω) atTop (𝓝 0) ↔
      Tendsto (fun k => κ * ∑ j ∈ Finset.range k, β ^ j * 𝔼.E t (x (t + j)) ω) atTop
        (𝓝 (π t ω)) := by
  have hS : ∀ k, κ * ∑ j ∈ Finset.range k, β ^ j * 𝔼.E t (x (t + j)) ω =
      π t ω - β ^ k * 𝔼.E t (π (t + k)) ω := fun k => by
    rw [pc_iterate 𝔼 hx h t k ω]; ring
  simp_rw [hS]
  constructor
  · intro h0
    simpa using h0.const_sub (π t ω)
  · intro h1
    have := h1.const_sub (π t ω)
    simp only [sub_sub_cancel, sub_self] at this
    exact this

/-- Cochrane (2023), eq. (5.4), p. 119: for `0 ≤ β < 1`, bounded adapted `x` and bounded `π`,
the Phillips curve holds iff `π_t = κ ∑_{j≥0} βʲ E_t x_{t+j}` (a convergent `tsum`). -/
theorem eq_5_4 {β κ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x π : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (hxb : ∀ t ω, |x t ω| ≤ M) (hπ : BoundedProc π) :
    PC 𝔼 β κ x π ↔ ∀ t ω, π t ω = κ * ∑' j, β ^ j * 𝔼.E t (x (t + j)) ω := by
  have hxa : 𝔼.Adapted (κ • x) := fun s => by
    rw [Pi.smul_apply, map_smul, hx s]
  have hub : ∀ t ω, |(κ • x) t ω| ≤ |κ| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hxb t ω) (abs_nonneg κ)
  have hfs : ∀ t ω, 𝔼.forwardSeries β (κ • x) t ω = κ * ∑' j, β ^ j * 𝔼.E t (x (t + j)) ω := by
    intro t ω
    unfold ExpectationSystem.forwardSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [Pi.smul_apply, map_smul, smul_eq_mul]
    ring
  constructor
  · intro h t ω
    rw [← hfs, ← 𝔼.eq_forwardSeries hβ0 hβ1 hub hxa h hπ]
  · intro h
    have hπeq : π = 𝔼.forwardSeries β (κ • x) := by
      funext t ω
      rw [h t ω, hfs]
    rw [pc_iff_solves, hπeq]
    exact 𝔼.forwardSeries_solves hβ0 hβ1 hub hxa

/-! ### The flexible-price limit κ → ∞ (p. 119) -/

/-- Cochrane (2023), p. 119: from (5.2), `|x_t| ≤ (1 + β) M / κ` whenever `|π| ≤ M`; output is
pinned at zero as `κ → ∞` whatever inflation is. -/
theorem abs_x_le {β κ M : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) {x π : ℕ → Ω → ℝ}
    (h : PC 𝔼 β κ x π) (hπ : ∀ t ω, |π t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |x t ω| ≤ (1 + β) * M / κ := by
  have hx : x t ω = (π t ω - β * 𝔼.E t (π (t + 1)) ω) / κ := by
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    field_simp
    linarith
  have hE := 𝔼.abs_E_le (hπ (t + 1)) t ω
  rw [hx, abs_div, abs_of_pos hκ, div_le_div_iff_of_pos_right hκ]
  calc |π t ω - β * 𝔼.E t (π (t + 1)) ω| ≤ |π t ω| + β * |𝔼.E t (π (t + 1)) ω| := by
        have h := abs_sub (π t ω) (β * 𝔼.E t (π (t + 1)) ω)
        rwa [abs_mul, abs_of_nonneg hβ] at h
    _ ≤ M + β * M := by gcongr; exact hπ t ω
    _ = (1 + β) * M := by ring

/-- Cochrane (2023), p. 119: for a family of Phillips-curve solutions indexed by `κ`, with
inflation bounded uniformly in `κ`, output tends to zero as `κ → ∞`. -/
theorem tendsto_x_kappa {β M : ℝ} (hβ : 0 ≤ β) {x π : ℝ → ℕ → Ω → ℝ}
    (h : ∀ κ, 0 < κ → PC 𝔼 β κ (x κ) (π κ)) (hπ : ∀ κ t ω, |π κ t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Tendsto (fun κ => x κ t ω) atTop (𝓝 0) := by
  have hb : Tendsto (fun κ : ℝ => (1 + β) * M / κ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hb
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  exact abs_x_le 𝔼 hβ hκ (h κ hκ) (hπ κ) t ω

/-! ### (5.6): the roots -/

/-- Cochrane (2023), eq. (5.6), p. 119: the larger root
`λ₁ = [(1 + β + σκ) + √((1 + β + σκ)² − 4β)]/2`. -/
noncomputable def lam1 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ + Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the smaller root
`λ₂ = [(1 + β + σκ) − √((1 + β + σκ)² − 4β)]/2`. -/
noncomputable def lam2 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ - Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the discriminant is positive when `σκ > 0`, `β > 0`. -/
theorem disc_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    0 < (1 + β + σ * κ) ^ 2 - 4 * β := by
  nlinarith [sq_nonneg (1 - β), sq_nonneg (σ * κ)]

/-- Cochrane (2023), eq. (5.6) and A1 p. 570: `λ₁ + λ₂ = 1 + β + σκ`. -/
theorem lam_sum (σ β κ : ℝ) : lam1 σ β κ + lam2 σ β κ = 1 + β + σ * κ := by
  unfold lam1 lam2; ring

/-- Cochrane (2023), eq. (5.6) and A1 p. 570: `λ₁ λ₂ = β`. -/
theorem lam_prod {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam1 σ β κ * lam2 σ β κ = β := by
  unfold lam1 lam2
  have h := Real.sq_sqrt (disc_pos ha hβ).le
  nlinarith [h]

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁` is a root of `λ² − (1 + β + σκ)λ + β`. -/
theorem lam1_root {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam1 σ β κ ^ 2 - (1 + β + σ * κ) * lam1 σ β κ + β = 0 := by
  linear_combination lam1 σ β κ * lam_sum σ β κ - lam_prod ha hβ

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂` is a root of `λ² − (1 + β + σκ)λ + β`. -/
theorem lam2_root {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam2 σ β κ ^ 2 - (1 + β + σ * κ) * lam2 σ β κ + β = 0 := by
  linear_combination lam2 σ β κ * lam_sum σ β κ - lam_prod ha hβ

/-- Cochrane (2023), A1 p. 570: `σκ = (λ₁ − 1)(1 − λ₂)` (the key identity behind (5.8)). -/
theorem sigma_kappa_eq {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    σ * κ = (lam1 σ β κ - 1) * (1 - lam2 σ β κ) := by
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  linear_combination -h1 + h2

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ < λ₁`. -/
theorem lam2_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam2 σ β κ < lam1 σ β κ := by
  unfold lam1 lam2
  have := Real.sqrt_pos.mpr (disc_pos ha hβ)
  linarith

/-- Cochrane (2023), p. 119: `λ₁ > 1`. -/
theorem one_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 1 < lam1 σ β κ := by
  by_contra hc
  push Not at hc
  have h := sigma_kappa_eq ha hβ
  have h2 := lam2_lt_lam1 ha hβ
  nlinarith

/-- Cochrane (2023), p. 119: `λ₂ < 1`. -/
theorem lam2_lt_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : lam2 σ β κ < 1 := by
  have h := sigma_kappa_eq ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-- Cochrane (2023), p. 119: `λ₂ > 0`. -/
theorem lam2_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < lam2 σ β κ := by
  have h := lam_prod ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ > 0` (used for divisions). -/
theorem lam1_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < lam1 σ β κ :=
  one_pos.trans (one_lt_lam1 ha hβ)

/-! ### (5.8): the coefficients sum to one -/

/-- Cochrane (2023), eq. (5.8), p. 120:
`σκ/(λ₁ − λ₂) = [1 + λ₁⁻¹/(1 − λ₁⁻¹) + λ₂/(1 − λ₂)]⁻¹`. -/
theorem eq_5_8 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    σ * κ / (lam1 σ β κ - lam2 σ β κ) =
      (1 + (lam1 σ β κ)⁻¹ / (1 - (lam1 σ β κ)⁻¹) + lam2 σ β κ / (1 - lam2 σ β κ))⁻¹ := by
  have h1 := one_lt_lam1 ha hβ
  have h2 := lam2_lt_one ha hβ
  have h3 := lam2_lt_lam1 ha hβ
  have hk := sigma_kappa_eq ha hβ
  have hl1 : lam1 σ β κ - 1 ≠ 0 := by linarith
  have hl2 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hl3 : lam1 σ β κ - lam2 σ β κ ≠ 0 := by linarith
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have hinv : 1 - (lam1 σ β κ)⁻¹ = (lam1 σ β κ - 1) / lam1 σ β κ := by field_simp
  have e : 1 + (lam1 σ β κ)⁻¹ / ((lam1 σ β κ - 1) / lam1 σ β κ) + lam2 σ β κ / (1 - lam2 σ β κ)
      = (lam1 σ β κ - lam2 σ β κ) / ((lam1 σ β κ - 1) * (1 - lam2 σ β κ)) := by
    field_simp
    ring
  rw [hinv, e, inv_div, hk]

/-- Cochrane (2023), Online Appendix A1, §1.7, p. 570: the long-run impulse response is one,
`σκ / ((λ₁ − 1)(1 − λ₂)) = 1`. -/
theorem long_run_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    σ * κ / ((lam1 σ β κ - 1) * (1 - lam2 σ β κ)) = 1 := by
  rw [sigma_kappa_eq ha hβ]
  have h1 := one_lt_lam1 ha hβ
  have h2 := lam2_lt_one ha hβ
  exact div_self (mul_ne_zero (by linarith) (by linarith))

/-- Cochrane (2023), eq. (5.8), p. 120 ("the sum of the coefficients in (5.5) is one"): with
`c = σκ/(λ₁ − λ₂)`, `c (∑_{j≥0} λ₁^{−j} + ∑_{j≥1} λ₂ʲ) = 1`, both series convergent. -/
theorem coeff_sum_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    HasSum (fun j : ℕ => ((lam1 σ β κ)⁻¹) ^ j) (1 - (lam1 σ β κ)⁻¹)⁻¹ ∧
      HasSum (fun j : ℕ => lam2 σ β κ ^ (j + 1)) (lam2 σ β κ / (1 - lam2 σ β κ)) ∧
      σ * κ / (lam1 σ β κ - lam2 σ β κ) *
        ((1 - (lam1 σ β κ)⁻¹)⁻¹ + lam2 σ β κ / (1 - lam2 σ β κ)) = 1 := by
  have h1 := one_lt_lam1 ha hβ
  have h2 := lam2_lt_one ha hβ
  have h0 := lam2_pos ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  refine ⟨hasSum_geometric_of_lt_one hq0 hq1, ?_, ?_⟩
  · have := (hasSum_geometric_of_lt_one h0.le h2).mul_left (lam2 σ β κ)
    simp_rw [pow_succ, mul_comm _ (lam2 σ β κ)]
    convert this using 1
    field_simp
  · have h58 := eq_5_8 ha hβ
    have hl0 : lam1 σ β κ ≠ 0 := by linarith
    have hinv : (1 - (lam1 σ β κ)⁻¹)⁻¹ = 1 + (lam1 σ β κ)⁻¹ / (1 - (lam1 σ β κ)⁻¹) := by
      have : 1 - (lam1 σ β κ)⁻¹ ≠ 0 := by linarith
      rw [one_add_div this, sub_add_cancel, one_div]
    rw [hinv, h58]
    have : 1 + (lam1 σ β κ)⁻¹ / (1 - (lam1 σ β κ)⁻¹) + lam2 σ β κ / (1 - lam2 σ β κ) ≠ 0 := by
      have : 0 < (lam1 σ β κ)⁻¹ / (1 - (lam1 σ β κ)⁻¹) := div_pos (by positivity) (by linarith)
      have : 0 < lam2 σ β κ / (1 - lam2 σ β κ) := div_pos h0 (by linarith)
      linarith
    exact inv_mul_cancel₀ this

/-! ### Comparative statics in κ -/

/-- Cochrane (2023), pp. 122–123 (stickier prices): for `σ > 0` and `0 < β < 1`, `λ₁` is strictly
increasing in `κ > 0`. -/
theorem lam1_strictMonoOn {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    StrictMonoOn (fun κ => lam1 σ β κ) (Set.Ioi 0) := by
  intro κ₁ hκ₁ κ₂ hκ₂ hlt
  simp only [Set.mem_Ioi] at hκ₁ hκ₂
  simp only [lam1]
  have hT : σ * κ₁ < σ * κ₂ := mul_lt_mul_of_pos_left hlt hσ
  have hd1 := disc_pos (mul_pos hσ hκ₁) hβ
  have hs : Real.sqrt ((1 + β + σ * κ₁) ^ 2 - 4 * β) <
      Real.sqrt ((1 + β + σ * κ₂) ^ 2 - 4 * β) := by
    apply Real.sqrt_lt_sqrt hd1.le
    have h0 : 0 < 1 + β + σ * κ₁ := by nlinarith [mul_pos hσ hκ₁]
    nlinarith
  linarith

/-- Cochrane (2023), p. 123 (κ → 0): `λ₁ → 1` as `κ → 0⁺` (for `0 < β < 1`). -/
theorem tendsto_lam1_zero {σ β : ℝ} (hβ1 : β < 1) :
    Tendsto (fun κ => lam1 σ β κ) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous (fun κ => lam1 σ β κ) := by
    unfold lam1; fun_prop
  have h0 : lam1 σ β 0 = 1 := by
    unfold lam1
    have : (1 + β + σ * 0) ^ 2 - 4 * β = (1 - β) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by linarith)]
    ring
  rw [← h0]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Cochrane (2023), pp. 119, 123 (κ → ∞): `λ₁ → ∞`. -/
theorem tendsto_lam1_atTop {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    Tendsto (fun κ => lam1 σ β κ) atTop atTop := by
  have hlin : Tendsto (fun κ : ℝ => σ * κ / 2) atTop atTop := by
    apply Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    exact tendsto_id.const_mul_atTop hσ
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  unfold lam1
  have := Real.sqrt_nonneg ((1 + β + σ * κ) ^ 2 - 4 * β)
  linarith

/-- Cochrane (2023), p. 119 (κ → ∞): `λ₂ = β/λ₁ → 0`. -/
theorem tendsto_lam2_atTop {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    Tendsto (fun κ => lam2 σ β κ) atTop (𝓝 0) := by
  have h := (tendsto_lam1_atTop hσ hβ).inv_tendsto_atTop.const_mul β
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have hp := lam_prod (mul_pos hσ hκ) hβ
  have h1 := lam1_pos (mul_pos hσ hκ) hβ
  change β * (lam1 σ β κ)⁻¹ = lam2 σ β κ
  field_simp
  linarith

/-- Cochrane (2023), pp. 119–120 (κ → ∞): the coefficient `c = σκ/(λ₁ − λ₂)` of (5.5) tends to
one, so (5.5) tends to the flexible-price (5.9). -/
theorem tendsto_coef_atTop {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    Tendsto (fun κ => σ * κ / (lam1 σ β κ - lam2 σ β κ)) atTop (𝓝 1) := by
  have hq := (tendsto_lam1_atTop hσ hβ).inv_tendsto_atTop
  have h2 := tendsto_lam2_atTop hσ hβ
  have hlim : Tendsto (fun κ => (1 - (lam1 σ β κ)⁻¹) * (1 - lam2 σ β κ) /
      (1 - lam2 σ β κ * (lam1 σ β κ)⁻¹)) atTop (𝓝 ((1 - 0) * (1 - 0) / (1 - 0 * 0))) :=
    (((tendsto_const_nhds.sub hq).mul (tendsto_const_nhds.sub h2)).div
      (tendsto_const_nhds.sub (h2.mul hq)) (by norm_num))
  norm_num at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have ha := mul_pos hσ hκ
  rw [sigma_kappa_eq ha hβ]
  have h1 := one_lt_lam1 ha hβ
  have h3 := lam2_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have hl3 : lam1 σ β κ - lam2 σ β κ ≠ 0 := by linarith
  field_simp

/-! ### Steady states and the long-run tradeoff (p. 123) -/

/-- Cochrane (2023), p. 123: constant `(x̄, π̄)` satisfy (5.2) iff `κ x̄ = (1 − β) π̄`. -/
theorem pc_const_iff [Nonempty Ω] {β κ xb πb : ℝ} :
    PC 𝔼 β κ (fun _ _ => xb) (fun _ _ => πb) ↔ κ * xb = (1 - β) * πb := by
  have hc : ∀ t, 𝔼.E t (fun _ => πb) = fun _ => πb := fun t => 𝔼.const t πb
  constructor
  · intro h
    have := congrFun (h 0) (Classical.arbitrary Ω)
    simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · intro h t
    funext ω
    simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

/-- Cochrane (2023), p. 123: the permanent output–inflation tradeoff `x = (1 − β) π / κ`. -/
theorem tradeoff [Nonempty Ω] {β κ xb πb : ℝ} (hκ : κ ≠ 0)
    (h : PC 𝔼 β κ (fun _ _ => xb) (fun _ _ => πb)) : xb = (1 - β) / κ * πb := by
  have := (pc_const_iff 𝔼).mp h
  field_simp
  linarith

/-- Cochrane (2023), p. 123: with `β = 1` there is no long-run tradeoff: every constant
equilibrium of (5.2) has `x̄ = 0`. -/
theorem no_tradeoff_beta_one [Nonempty Ω] {κ xb πb : ℝ} (hκ : κ ≠ 0)
    (h : PC 𝔼 1 κ (fun _ _ => xb) (fun _ _ => πb)) : xb = 0 := by
  have := tradeoff 𝔼 hκ h
  simpa using this

/-- Cochrane (2023), pp. 123 and 132: constant `(ī, x̄, π̄)` solve (5.1)–(5.2) iff the steady
state is Fisherian, `ī = π̄`, with the tradeoff `κ x̄ = (1 − β) π̄`. -/
theorem nk_const_iff [Nonempty Ω] {σ β κ ib xb πb : ℝ} (hσ : σ ≠ 0) :
    NK 𝔼 σ β κ (fun _ _ => ib) (fun _ _ => xb) (fun _ _ => πb) ↔
      ib = πb ∧ κ * xb = (1 - β) * πb := by
  unfold NK
  rw [pc_const_iff]
  have hc : ∀ t (c : ℝ), 𝔼.E t (fun _ => c) = fun _ => c := fun t c => 𝔼.const t c
  have his : IS 𝔼 σ (fun _ _ => ib) (fun _ _ => xb) (fun _ _ => πb) ↔ ib = πb := by
    constructor
    · intro h
      have := congrFun (h 0) (Classical.arbitrary Ω)
      simp only [hc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : σ * (ib - πb) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hσ
      · linarith
    · intro h t
      funext ω
      simp only [hc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, sub_self, Pi.zero_apply,
        mul_zero, sub_zero]
  rw [his]

/-- Cochrane (2023), p. 123: the indexed Phillips curve
`π_t = (1 − θ) π_{t−1} + θ E_t π_{t+1} + κ x_t` (stated at dates `t + 1 ≥ 1`). -/
def IPC (θ κ : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π (t + 1) = (1 - θ) • π t + θ • 𝔼.E (t + 1) (π (t + 2)) + κ • x (t + 1)

/-- Cochrane (2023), p. 123: constant `(x̄, π̄)` satisfy the indexed Phillips curve iff
`κ x̄ = 0`. -/
theorem ipc_const_iff [Nonempty Ω] {θ κ xb πb : ℝ} :
    IPC 𝔼 θ κ (fun _ _ => xb) (fun _ _ => πb) ↔ κ * xb = 0 := by
  have hc : ∀ t, 𝔼.E t (fun _ => πb) = fun _ => πb := fun t => 𝔼.const t πb
  constructor
  · intro h
    have := congrFun (h 0) (Classical.arbitrary Ω)
    simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · intro h t
    funext ω
    simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

/-- Cochrane (2023), p. 123: with indexation there is no long-run output–inflation tradeoff:
every constant inflation rate is a steady state with `x̄ = 0`, and only `x̄ = 0` is. -/
theorem ipc_no_tradeoff [Nonempty Ω] {θ κ : ℝ} (hκ : κ ≠ 0) (xb πb : ℝ) :
    IPC 𝔼 θ κ (fun _ _ => xb) (fun _ _ => πb) ↔ xb = 0 := by
  rw [ipc_const_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hκ
    · exact h
  · intro h; rw [h, mul_zero]

end Cochrane.StickyPriceFiscal.NKModel
