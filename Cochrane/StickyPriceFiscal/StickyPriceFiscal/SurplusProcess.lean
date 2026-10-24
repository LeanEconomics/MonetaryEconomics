/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.SharedTools
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Ring.GeomSum

/-!
# A surplus process with an s-shaped moving average

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4 up to §5.4.1,
eqs. (5.22)–(5.28), pp. 134–137 (including the facts plotted in Figure 5.5), and Online
Appendix A2, eqs. (2.1)–(2.3), p. 595.

The surplus process (5.22)–(5.24) is
`s̃_{t+1} = α v*_t + u_{t+1}`, `ρ v*_{t+1} = v*_t + β_s ε_{t+1} − s̃_{t+1}`,
`u_{t+1} = η u_t + ε_{t+1}`. Time is indexed by `ℕ`; processes start from zero pre-sample
states, so a moving average `a(L) ε_t` is the finite sum `∑_{k<t} a_k ε_{t−k}` (`ma`). All
statements hold for an arbitrary `ExpectationSystem` (perfect foresight or genuine uncertainty).

## Main results

* `ma_representation`, `vstar_display`, `s_ma_525`: the moving-average representations of
  `u`, `v*` (first display, p. 135) and `s̃` ((5.25) and (5.26)), with coefficients `vCoef`,
  `aCoef`, `dCoef`, `eCoef`.
* `aCoef_526`: (5.26) as the coefficient identity `(1 − gL) a(L) = (1 − ρ⁻¹L) a_u(L) + β_s α ρ⁻¹ L`
  with `g = (1 − α)/ρ`; `aCoef_conv`: (5.25) ⇒ (5.26); `aCoef_two_geom`: the two-geometric form.
* `hasSum_aCoef`: (5.28) `a(ρ) = ∑ ρᵏ a_k = β_s`, for `0 < α < 2` and `|ρη| < 1` (the upper
  bound `α < 2` is missing in the book, survey E31); `hasSum_dCoef`, `hasSum_eCoef`: the first
  term of (5.25) has `a(ρ) = 0`, the second `β_s`.
* `s_shape`: for `0 ≤ η < g`, `0 < α < 1` and `β_s` below an explicit bound, the response
  `a_k` is positive, then negative from some date on: exactly one sign change.
* `innov_ma`: the innovation of an MA process, `ΔE_{t+1} x_{t+1+j} = c_j ε_{t+1}`.
* `vstar_tvc`, `summable_pv`, `vstar_eq_pv`: `v*` satisfies the transversality condition and
  is the present value of surpluses; `innov_pv`: `ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} = β_s ε_{t+1}`.
* `unexpected_inflation_527`, `equilibrium_528`: in the frictionless model (5.27),
  `ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`; with the surplus process this is
  `−β_s ε_{t+1}`, and debt equals `v*` (p. 136).
* Figure 5.5 facts: `fig55_pv_response`, `fig55_betaS_zero`, `fig55_betaS_one`,
  `fig55_initial_debt`, `fig55_debt_rises`, `fig55_u_pv`.
* Online Appendix A2: `appA2_21` ((2.1)–(2.2) with `a_u = 1`), `appA2_23_coef`,
  `appA2_23_arma`, `appA2_23_iid` ((2.3) and `β_s = 1` ⇒ i.i.d.).
* Survey E31: `aCoef_not_summable` (without `α < 2` the series `a(ρ)` need not exist).
* `E_pv_eq_tsum`: for `0 ≤ ρ < 1` and bounded surpluses the book's `E_t ∑ ρʲ s̃_{t+1+j}` equals
  the series of forecasts `∑ ρʲ E_t s̃_{t+1+j}` used throughout.
* `dCoef_succ_neg`, `ma_impulse`: the one-then-negative pattern of (5.25) and impulse responses.
-/

namespace Cochrane.StickyPriceFiscal.SurplusProcess

open Filter Topology
open SharedTools (TVC summable_of_rec)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Shocks and moving averages -/

/-- Cochrane (2023), §5.4, p. 134: the shock `ε_{t+1}` has conditional mean zero,
`E_t ε_{t+1} = 0` (a martingale-difference sequence). -/
def MeanZero (ε : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (ε (t + 1)) = 0

/-- Cochrane (2023), §5.4, p. 134: under `MeanZero`, every later shock has date-`t` forecast
zero, `E_t ε_{t+1+j} = 0`. -/
theorem E_future_eq_zero {ε : ℕ → Ω → ℝ} (hε : MeanZero 𝔼 ε) (t j : ℕ) :
    𝔼.E t (ε (t + 1 + j)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t j), show t + 1 + j = t + j + 1 by omega, hε (t + j),
    map_zero]

/-- Cochrane (2023), §5.4, p. 134: the date-`s` forecast of an adapted mean-zero shock `ε_r` is
`ε_r` when `r ≤ s` and zero otherwise. -/
theorem E_shock {ε : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (s r : ℕ) :
    𝔼.E s (ε r) = if r ≤ s then ε r else 0 := by
  split_ifs with h
  · exact ForwardSolution.E_of_known 𝔼 h (ha r)
  · obtain ⟨j, rfl⟩ : ∃ j, r = s + 1 + j := ⟨r - (s + 1), by omega⟩
    exact E_future_eq_zero 𝔼 hε s j

/-- Cochrane (2023), (5.25)–(5.26), p. 135: the moving average `c(L) x_t = ∑_{k<t} c_k x_{t−k}`
of a process started at date 1 (zero pre-sample values). -/
def ma (c : ℕ → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range t, c k • x (t - k)

/-- Cochrane (2023), (5.25), p. 135: pointwise form of the moving average. -/
theorem ma_apply (c : ℕ → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ma c x t ω = ∑ k ∈ Finset.range t, c k * x (t - k) ω := by
  simp [ma, Finset.sum_apply]

/-- Cochrane (2023), (5.25), p. 135: the moving average is zero before the first shock. -/
theorem ma_zero (c : ℕ → ℝ) (x : ℕ → Ω → ℝ) : ma c x 0 = 0 := by
  simp [ma]

/-- Cochrane (2023), (5.25), p. 135: `c(L) x_{t+1} = c_0 x_{t+1} + (c(L) − c_0) x_{t+1}`. -/
theorem ma_succ (c : ℕ → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ma c x (t + 1) ω = c 0 * x (t + 1) ω + ma (fun k => c (k + 1)) x t ω := by
  rw [ma_apply, ma_apply, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.add_sub_add_right]

/-- Cochrane (2023), (5.25), p. 135: the moving average is linear in its coefficients. -/
theorem ma_add_mul (a b : ℝ) (c d : ℕ → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ma (fun k => a * c k + b * d k) x t ω = a * ma c x t ω + b * ma d x t ω := by
  simp only [ma_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), (5.25), p. 135: the moving average is linear in the process. -/
theorem ma_add_proc (c : ℕ → ℝ) (a b : ℝ) (x y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ma c (fun r => a • x r + b • y r) t ω = a * ma c x t ω + b * ma c y t ω := by
  simp only [ma_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), (5.27), p. 135 (and Chapter 4's `ΔE_{t+1} s_{t+1+j} = a_j ε_{t+1}`): for an
adapted mean-zero shock, the innovation of a moving average `x = c(L) ε` is
`(E_{t+1} − E_t) x_{t+1+j} = c_j ε_{t+1}`. -/
theorem innov_ma {ε : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (c : ℕ → ℝ)
    (t j : ℕ) :
    𝔼.E (t + 1) (ma c ε (t + 1 + j)) - 𝔼.E t (ma c ε (t + 1 + j)) = c j • ε (t + 1) := by
  simp only [ma, map_sum, map_smul, E_shock 𝔼 ha hε, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · have h3 : t + 1 + j - j = t + 1 := by omega
    rw [h3]
    simp
  · intro k hk hkj
    rw [Finset.mem_range] at hk
    by_cases hlt : k < j
    · have h1 : ¬ t + 1 + j - k ≤ t + 1 := by omega
      have h2 : ¬ t + 1 + j - k ≤ t := by omega
      simp only [h1, h2, ↓reduceIte, sub_self]
    · have h1 : t + 1 + j - k ≤ t + 1 := by omega
      have h2 : t + 1 + j - k ≤ t := by omega
      simp only [h1, h2, ↓reduceIte, sub_self]
  · intro hj
    exact absurd (Finset.mem_range.mpr (by omega)) hj

/-! ### The surplus process (5.22)–(5.24) and its moving average -/

/-- Cochrane (2023), eqs. (5.22)–(5.24), p. 134: the surplus process
`s̃_{t+1} = α v*_t + u_{t+1}`, `ρ v*_{t+1} = v*_t + β_s ε_{t+1} − s̃_{t+1}`,
`u_{t+1} = η u_t + ε_{t+1}` (`η` is the book's `η_s`). -/
def IsSurplusProc (ρ α βs η : ℝ) (ε s vs u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, s (t + 1) = α • vs t + u (t + 1) ∧
    ρ • vs (t + 1) = vs t + βs • ε (t + 1) - s (t + 1) ∧ u (t + 1) = η • u t + ε (t + 1)

variable {ρ α βs η : ℝ} {ε s vs u : ℕ → Ω → ℝ}

/-- Cochrane (2023), eqs. (5.22)–(5.24), p. 134: the three equations at a state `ω`. -/
theorem IsSurplusProc.apply (h : IsSurplusProc ρ α βs η ε s vs u) (t : ℕ) (ω : Ω) :
    s (t + 1) ω = α * vs t ω + u (t + 1) ω ∧
      ρ * vs (t + 1) ω = vs t ω + βs * ε (t + 1) ω - s (t + 1) ω ∧
      u (t + 1) ω = η * u t ω + ε (t + 1) ω := by
  obtain ⟨h1, h2, h3⟩ := h t
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrFun h1 ω
  · simpa using congrFun h2 ω
  · simpa using congrFun h3 ω

/-- Cochrane (2023), p. 134 (display after (5.24)): substituting (5.22) in (5.23),
`ρ v*_{t+1} = (1 − α) v*_t + β_s ε_{t+1} − u_{t+1}`. -/
theorem vstar_rec (h : IsSurplusProc ρ α βs η ε s vs u) (t : ℕ) :
    ρ • vs (t + 1) = (1 - α) • vs t + βs • ε (t + 1) - u (t + 1) := by
  obtain ⟨h1, h2, -⟩ := h t
  rw [h2, h1, sub_smul, one_smul]
  abel

/-- Cochrane (2023), p. 135: the autoregressive root `g = (1 − α)/ρ` of the latent debt. -/
noncomputable def gRoot (ρ α : ℝ) : ℝ := (1 - α) / ρ

/-- Cochrane (2023), p. 135: the coefficients of `1/((1 − gL)(1 − ηL))`,
`∑_{i ≤ k} gⁱ η^{k−i}`. -/
def geomConv (g η : ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), g ^ i * η ^ (k - i)

/-- Cochrane (2023), p. 135: the recursion `c_{k+1} = g c_k + η^{k+1}` of `geomConv`. -/
theorem geomConv_succ (g η : ℝ) (k : ℕ) :
    geomConv g η (k + 1) = g * geomConv g η k + η ^ (k + 1) := by
  unfold geomConv
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_sub_add_right, pow_succ]
    ring
  · simp

/-- Cochrane (2023), p. 135 (first display): the moving-average coefficients of
`v*_{t+1} = ρ⁻¹ (β_s ε_{t+1} − u_{t+1})/(1 − gL)` in terms of `ε`,
`ρ⁻¹ (β_s gᵏ − ∑_{i ≤ k} gⁱ η^{k−i})`. -/
noncomputable def vCoef (ρ α βs η : ℝ) (k : ℕ) : ℝ :=
  ρ⁻¹ * (βs * gRoot ρ α ^ k - geomConv (gRoot ρ α) η k)

/-- Cochrane (2023), eq. (5.26), p. 135: the moving-average coefficients `a_k` of the surplus,
`a_0 = 1`, `a_{k+1} = η^{k+1} + α · vCoef_k`. -/
noncomputable def aCoef (ρ α βs η : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => η ^ (k + 1) + α * vCoef ρ α βs η k

/-- Cochrane (2023), eq. (5.25), p. 135: the coefficients of the first lag polynomial,
`1 − αρ⁻¹L/(1 − gL) = 1 − (α/ρ)[L + gL² + g²L³ + …]`. -/
noncomputable def dCoef (ρ α : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => -(α / ρ) * gRoot ρ α ^ k

/-- Cochrane (2023), eq. (5.25), p. 135: the coefficients of `β_s αρ⁻¹L/(1 − gL)`. -/
noncomputable def eCoef (ρ α βs : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => βs * α / ρ * gRoot ρ α ^ k

/-- Cochrane (2023), eq. (5.26), p. 135: the coefficients of the numerator
`(1 − ρ⁻¹L) a_u(L) + β_s αρ⁻¹L` with `a_u(L) = 1/(1 − ηL)`. -/
noncomputable def nCoef (ρ α βs η : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => η ^ (k + 1) - ρ⁻¹ * η ^ k + if k = 0 then βs * α * ρ⁻¹ else 0

/-- Cochrane (2023), p. 135: `vCoef_0 = ρ⁻¹(β_s − 1)`. -/
theorem vCoef_zero : vCoef ρ α βs η 0 = ρ⁻¹ * (βs - 1) := by
  simp [vCoef, geomConv]

/-- Cochrane (2023), p. 135: `vCoef_{k+1} = g vCoef_k − ρ⁻¹ η^{k+1}`. -/
theorem vCoef_succ (k : ℕ) :
    vCoef ρ α βs η (k + 1) = gRoot ρ α * vCoef ρ α βs η k + (-ρ⁻¹) * η ^ (k + 1) := by
  unfold vCoef
  rw [geomConv_succ, pow_succ]
  ring

/-- Cochrane (2023), eqs. (5.24)–(5.26), p. 135: with zero pre-sample states the surplus
process has the moving-average representations `u = a_u(L) ε`,
`v* = vCoef(L) ε` and `s̃_{t+1} = a(L) ε_{t+1}`. -/
theorem ma_representation (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u)
    (hv0 : vs 0 = 0) (hu0 : u 0 = 0) (t : ℕ) :
    u t = ma (fun k => η ^ k) ε t ∧ vs t = ma (vCoef ρ α βs η) ε t ∧
      s (t + 1) = ma (aCoef ρ α βs η) ε (t + 1) := by
  have hUV : ∀ t, u t = ma (fun k => η ^ k) ε t ∧ vs t = ma (vCoef ρ α βs η) ε t := by
    intro t
    induction t with
    | zero => exact ⟨by rw [hu0, ma_zero], by rw [hv0, ma_zero]⟩
    | succ t ih =>
      obtain ⟨ihu, ihv⟩ := ih
      have hu1 : u (t + 1) = ma (fun k => η ^ k) ε (t + 1) := by
        funext ω
        obtain ⟨-, -, h3⟩ := h.apply t ω
        rw [h3, ma_succ, ihu,
          show (fun k => η ^ (k + 1)) = fun k => η * η ^ k + 0 * (0 : ℝ) from
            funext fun k => by ring, ma_add_mul]
        ring
      refine ⟨hu1, ?_⟩
      funext ω
      have hr := congrFun (vstar_rec h t) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
      have hv1 : vs (t + 1) ω = ρ⁻¹ * (ρ * vs (t + 1) ω) := by field_simp
      have hM := congrFun hu1 ω
      rw [ma_succ] at hM
      rw [hv1, hr, ma_succ, ihv, hM, show (fun k => vCoef ρ α βs η (k + 1)) =
          fun k => gRoot ρ α * vCoef ρ α βs η k + (-ρ⁻¹) * η ^ (k + 1) from
            funext fun k => vCoef_succ k, ma_add_mul, vCoef_zero, gRoot]
      field_simp
      ring
  refine ⟨(hUV t).1, (hUV t).2, ?_⟩
  funext ω
  obtain ⟨h1, -, -⟩ := h.apply t ω
  have hM := congrFun (hUV (t + 1)).1 ω
  rw [ma_succ] at hM
  rw [h1, (hUV t).2, hM, ma_succ, show (fun k => aCoef ρ α βs η (k + 1)) =
      fun k => 1 * η ^ (k + 1) + α * vCoef ρ α βs η k from funext fun k => by simp [aCoef],
    ma_add_mul]
  simp [aCoef]
  ring

/-- Cochrane (2023), p. 135 (first display): with `v*_0 = 0`,
`v*_t = ρ⁻¹ ∑_{k<t} gᵏ (β_s ε − u)_{t−k}`, i.e. `v*_{t+1} = ρ⁻¹(β_s ε_{t+1} − u_{t+1})/(1 − gL)`. -/
theorem vstar_display (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0)
    (t : ℕ) : vs t = ma (fun k => ρ⁻¹ * gRoot ρ α ^ k) (fun r => βs • ε r - u r) t := by
  induction t with
  | zero => rw [hv0, ma_zero]
  | succ t ih =>
    funext ω
    have hr := congrFun (vstar_rec h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
    have hv1 : vs (t + 1) ω = ρ⁻¹ * (ρ * vs (t + 1) ω) := by field_simp
    rw [hv1, hr, ma_succ, ih, show (fun k => ρ⁻¹ * gRoot ρ α ^ (k + 1)) =
        fun k => gRoot ρ α * (ρ⁻¹ * gRoot ρ α ^ k) + 0 * (0 : ℝ) from
          funext fun k => by ring, ma_add_mul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gRoot]
    field_simp
    ring

/-- Cochrane (2023), p. 135: the moving average commutes with a scalar factor on the
coefficients. -/
theorem ma_mul (a : ℝ) (c : ℕ → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ma (fun k => a * c k) x t ω = a * ma c x t ω := by
  simp only [ma_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), eq. (5.25), p. 135: with `v*_0 = 0`,
`s̃_{t+1} = [1 − αρ⁻¹L/(1 − gL)] u_{t+1} + β_s αρ⁻¹L/(1 − gL) ε_{t+1}`. -/
theorem s_ma_525 (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0)
    (t : ℕ) : s (t + 1) = ma (dCoef ρ α) u (t + 1) + ma (eCoef ρ α βs) ε (t + 1) := by
  funext ω
  obtain ⟨h1, -, -⟩ := h.apply t ω
  have hd := congrFun (vstar_display hρ h hv0 t) ω
  rw [show (fun r => βs • ε r - u r) = fun r => βs • ε r + (-1 : ℝ) • u r from
    funext fun r => by rw [neg_one_smul, sub_eq_add_neg], ma_add_proc] at hd
  rw [Pi.add_apply, h1, ma_succ, ma_succ,
    show (fun k => dCoef ρ α (k + 1)) = fun k => (-α) * (ρ⁻¹ * gRoot ρ α ^ k) from
      funext fun k => by simp only [dCoef]; ring,
    show (fun k => eCoef ρ α βs (k + 1)) = fun k => (βs * α) * (ρ⁻¹ * gRoot ρ α ^ k) from
      funext fun k => by simp only [eCoef]; ring, ma_mul (-α), ma_mul (βs * α), hd]
  simp only [dCoef, eCoef]
  ring

/-- Cochrane (2023), eq. (5.26), p. 135: the lag-polynomial identity
`(1 − gL) a(L) = (1 − ρ⁻¹L) a_u(L) + β_s αρ⁻¹L`, coefficient by coefficient. -/
theorem aCoef_526 :
    aCoef ρ α βs η 0 = nCoef ρ α βs η 0 ∧
      ∀ k, aCoef ρ α βs η (k + 1) - gRoot ρ α * aCoef ρ α βs η k = nCoef ρ α βs η (k + 1) := by
  refine ⟨rfl, fun k => ?_⟩
  rcases k with _ | k
  · simp only [aCoef, nCoef, vCoef_zero, ↓reduceIte, gRoot]
    ring
  · simp only [aCoef, nCoef, vCoef_succ, gRoot, Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-- Cochrane (2023), eqs. (5.25)–(5.26), p. 135 ("we can go further"): the coefficients of
(5.26) are those of (5.25) with `u = a_u(L) ε`: `a_k = ∑_{i ≤ k} d_i η^{k−i} + e_k`. -/
theorem aCoef_conv (k : ℕ) :
    aCoef ρ α βs η k =
      ∑ i ∈ Finset.range (k + 1), dCoef ρ α i * η ^ (k - i) + eCoef ρ α βs k := by
  rcases k with _ | k
  · simp [aCoef, dCoef, eCoef]
  · rw [Finset.sum_range_succ']
    simp only [dCoef, eCoef, aCoef, vCoef, geomConv, Nat.add_sub_add_right, Nat.sub_zero,
      one_mul]
    have : ∑ i ∈ Finset.range (k + 1), -(α / ρ) * gRoot ρ α ^ i * η ^ (k - i) =
        -(α / ρ) * ∑ i ∈ Finset.range (k + 1), gRoot ρ α ^ i * η ^ (k - i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    ring

/-- Cochrane (2023), p. 135 (survey's two-geometric form of (5.26)): for `η ≠ g`,
`a_{k+1} = A η^{k+1} + B g^{k+1} + β_s αρ⁻¹ gᵏ` with `A = (η − ρ⁻¹)/(η − g)` and
`B = (g − ρ⁻¹)/(g − η)`. -/
theorem aCoef_two_geom (hηg : η ≠ gRoot ρ α) (k : ℕ) :
    aCoef ρ α βs η (k + 1) = (η - ρ⁻¹) / (η - gRoot ρ α) * η ^ (k + 1) +
      (gRoot ρ α - ρ⁻¹) / (gRoot ρ α - η) * gRoot ρ α ^ (k + 1) +
      βs * α * ρ⁻¹ * gRoot ρ α ^ k := by
  have hG : geomConv (gRoot ρ α) η k * (gRoot ρ α - η) = gRoot ρ α ^ (k + 1) - η ^ (k + 1) := by
    have := geom_sum₂_mul (gRoot ρ α) η (k + 1)
    simpa [geomConv] using this
  have h1 : η - gRoot ρ α ≠ 0 := sub_ne_zero.mpr hηg
  have h2 : gRoot ρ α - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hηg)
  have hGe : geomConv (gRoot ρ α) η k =
      (gRoot ρ α ^ (k + 1) - η ^ (k + 1)) / (gRoot ρ α - η) := by
    rw [eq_div_iff h2]; exact hG
  have hαρ : α * ρ⁻¹ = ρ⁻¹ - gRoot ρ α := by unfold gRoot; ring
  simp only [aCoef, vCoef]
  rw [hGe]
  have e1 : (η - ρ⁻¹) / (η - gRoot ρ α) = 1 + α * ρ⁻¹ / (gRoot ρ α - η) := by
    rw [hαρ]; field_simp; ring
  have e2 : (gRoot ρ α - ρ⁻¹) / (gRoot ρ α - η) = -(α * ρ⁻¹) / (gRoot ρ α - η) := by
    rw [hαρ]; ring
  rw [e1, e2]
  field_simp
  ring

/-! ### `a(ρ) = β_s`: equation (5.28) -/

/-- Cochrane (2023), p. 135: `|1 − α| < 1` means `0 < α < 2`. -/
theorem alpha_pos_of (hα : |1 - α| < 1) : 0 < α ∧ α < 2 := by
  rw [abs_lt] at hα
  constructor <;> linarith [hα.1, hα.2]

/-- Cochrane (2023), (5.28), p. 135: with `ρ g = 1 − α`,
`∑ ρᵏ ∑_{i ≤ k} gⁱ η^{k−i} = 1/((1 − (1 − α))(1 − ρη))` (a Cauchy product). -/
theorem hasSum_geomConv (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * geomConv (gRoot ρ α) η k) (α⁻¹ * (1 - ρ * η)⁻¹) := by
  have h1 : Summable fun k : ℕ => ‖(1 - α) ^ k‖ := by
    simpa [norm_pow, Real.norm_eq_abs] using summable_geometric_of_lt_one (abs_nonneg _) hα
  have h2 : Summable fun k : ℕ => ‖(ρ * η) ^ k‖ := by
    simpa [norm_pow, Real.norm_eq_abs] using summable_geometric_of_lt_one (abs_nonneg _) hη
  have H := hasSum_sum_range_mul_of_summable_norm h1 h2
  rw [tsum_geometric_of_abs_lt_one hα, tsum_geometric_of_abs_lt_one hη, sub_sub_cancel] at H
  convert H using 1
  funext k
  unfold geomConv gRoot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show ρ ^ k = ρ ^ i * ρ ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], mul_pow,
    div_pow]
  field_simp

/-- Cochrane (2023), p. 135: the latent-debt coefficients sum to
`∑ ρᵏ vCoef_k = ρ⁻¹ (β_s/α − 1/(α(1 − ρη)))`. -/
theorem hasSum_vCoef (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * vCoef ρ α βs η k)
      (ρ⁻¹ * (βs * α⁻¹ - α⁻¹ * (1 - ρ * η)⁻¹)) := by
  have hg : HasSum (fun k : ℕ => (1 - α) ^ k) α⁻¹ := by
    simpa [sub_sub_cancel] using hasSum_geometric_of_abs_lt_one hα
  have H := ((hg.mul_left βs).sub (hasSum_geomConv hρ hα hη)).mul_left ρ⁻¹
  convert H using 1
  funext k
  unfold vCoef
  rw [show (1 - α) ^ k = ρ ^ k * gRoot ρ α ^ k by
    rw [← mul_pow, gRoot, mul_div_cancel₀ _ hρ]]
  ring

/-- Cochrane (2023), eq. (5.28), p. 135: `a(ρ) = ∑_k ρᵏ a_k = β_s`. Hypotheses: `ρ ≠ 0`,
`0 < α < 2` (written `|1 − α| < 1`; the book states only `α > 1 − ρ`, survey E31) and
`|ρη| < 1`. -/
theorem hasSum_aCoef (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * aCoef ρ α βs η k) βs := by
  obtain ⟨hα0, -⟩ := alpha_pos_of hα
  have hη1 : 1 - ρ * η ≠ 0 := by
    intro h0
    rw [show ρ * η = 1 by linarith, abs_one] at hη
    exact lt_irrefl _ hη
  rw [← hasSum_nat_add_iff' 1]
  have hg : HasSum (fun k : ℕ => (ρ * η) ^ k) (1 - ρ * η)⁻¹ := hasSum_geometric_of_abs_lt_one hη
  have H := (hg.mul_left (ρ * η)).add ((hasSum_vCoef (βs := βs) hρ hα hη).mul_left (α * ρ))
  convert H using 1
  · funext k
    simp only [aCoef]
    ring
  · simp only [Finset.range_one, Finset.sum_singleton, pow_zero, aCoef]
    field_simp
    ring

/-- Cochrane (2023), eq. (5.25), p. 135 ("all deficits are paid"): the first lag polynomial
`1 − αρ⁻¹L/(1 − gL)` has `∑ ρᵏ d_k = 0`. -/
theorem hasSum_dCoef (hρ : ρ ≠ 0) (hα : |1 - α| < 1) :
    HasSum (fun k => ρ ^ k * dCoef ρ α k) 0 := by
  obtain ⟨hα0, -⟩ := alpha_pos_of hα
  rw [← hasSum_nat_add_iff' 1]
  have hg : HasSum (fun k : ℕ => (1 - α) ^ k) α⁻¹ := by
    simpa [sub_sub_cancel] using hasSum_geometric_of_abs_lt_one hα
  convert hg.mul_left (-α) using 1
  · funext k
    simp only [dCoef]
    rw [show (1 - α) ^ k = ρ ^ k * gRoot ρ α ^ k by
      rw [← mul_pow, gRoot, mul_div_cancel₀ _ hρ]]
    field_simp
    ring
  · simp [dCoef]
    field_simp

/-- Cochrane (2023), eq. (5.25), p. 135: the second lag polynomial `β_s αρ⁻¹L/(1 − gL)` has
`∑ ρᵏ e_k = β_s`. -/
theorem hasSum_eCoef (hρ : ρ ≠ 0) (hα : |1 - α| < 1) :
    HasSum (fun k => ρ ^ k * eCoef ρ α βs k) βs := by
  obtain ⟨hα0, -⟩ := alpha_pos_of hα
  rw [← hasSum_nat_add_iff' 1]
  have hg : HasSum (fun k : ℕ => (1 - α) ^ k) α⁻¹ := by
    simpa [sub_sub_cancel] using hasSum_geometric_of_abs_lt_one hα
  convert hg.mul_left (βs * α) using 1
  · funext k
    simp only [eCoef]
    rw [show (1 - α) ^ k = ρ ^ k * gRoot ρ α ^ k by
      rw [← mul_pow, gRoot, mul_div_cancel₀ _ hρ]]
    field_simp
    ring
  · simp [eCoef]
    field_simp

/-- Cochrane (2023), p. 595, eq. (2.3) of Online Appendix A2: with `a_u(L) = 1` (`η = 0`),
`∑_{i ≤ k} gⁱ 0^{k−i} = gᵏ`. -/
theorem geomConv_zero (g : ℝ) (k : ℕ) : geomConv g 0 k = g ^ k := by
  unfold geomConv
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    have : 0 < k - i := by
      have := Finset.mem_range.mp hi
      omega
    rw [zero_pow this.ne', mul_zero]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- Cochrane (2023), Online Appendix A2, eq. (2.3), p. 595 (second form): with `a_u = 1`,
`a_0 = 1` and `a_{k+1} = −(α(1 − β_s)/ρ) gᵏ`. -/
theorem appA2_23_coef (k : ℕ) :
    aCoef ρ α βs 0 (k + 1) = -(α * (1 - βs) / ρ) * gRoot ρ α ^ k := by
  simp only [aCoef, vCoef, geomConv_zero]
  rw [zero_pow (Nat.succ_ne_zero k)]
  ring

/-- Cochrane (2023), Online Appendix A2, eq. (2.3), p. 595 (first, ARMA(1,1) form): with
`a_u = 1`, `a(L) = (1 − ((1 − αβ_s)/ρ) L)/(1 − gL)`, i.e. `a_1 − g a_0 = −(1 − αβ_s)/ρ` and
`a_{k+2} = g a_{k+1}`. -/
theorem appA2_23_arma :
    aCoef ρ α βs 0 1 - gRoot ρ α * aCoef ρ α βs 0 0 = -((1 - α * βs) / ρ) ∧
      ∀ k, aCoef ρ α βs 0 (k + 2) = gRoot ρ α * aCoef ρ α βs 0 (k + 1) := by
  refine ⟨?_, fun k => ?_⟩
  · rw [appA2_23_coef]
    simp only [aCoef, gRoot, pow_zero]
    ring
  · rw [appA2_23_coef, appA2_23_coef, pow_succ]
    ring

/-- Cochrane (2023), Online Appendix A2, p. 595: with `a_u = 1` and `β_s = 1` "the roots cancel
and we recover the i.i.d. shock": `a_{k+1} = 0`. -/
theorem appA2_23_iid (k : ℕ) : aCoef ρ α 1 0 (k + 1) = 0 := by
  rw [appA2_23_coef]
  ring

/-- Cochrane (2023), Online Appendix A2, eqs. (2.1)–(2.2), p. 595: with `a_u(L) = 1` (`η = 0`)
the process (5.22)–(5.24) is `s_{t+1} = α v*_t + ε_{t+1}`,
`ρ v*_{t+1} = v*_t + β_s ε_{t+1} − s_{t+1}` (the appendix writes `v` for `v*`). -/
theorem appA2_21 (h : IsSurplusProc ρ α βs 0 ε s vs u) (t : ℕ) :
    u (t + 1) = ε (t + 1) ∧ s (t + 1) = α • vs t + ε (t + 1) ∧
      ρ • vs (t + 1) = vs t + βs • ε (t + 1) - s (t + 1) := by
  obtain ⟨h1, h2, h3⟩ := h t
  have hu : u (t + 1) = ε (t + 1) := by rw [h3, zero_smul, zero_add]
  exact ⟨hu, by rw [h1, hu], h2⟩

/-- Cochrane (2023), (5.28), p. 135, and survey E31: the bound `α < 2` cannot be dropped. With
`a_u = 1`, `β_s ≠ 1` and `|1 − α| ≥ 1`, `α ≠ 0`, the terms `ρᵏ a_k` do not tend to zero, so
`a(ρ) = ∑ ρᵏ a_k` does not exist. -/
theorem aCoef_not_summable (hρ : ρ ≠ 0) (hα : 1 ≤ |1 - α|) (hα0 : α ≠ 0) (hβ : βs ≠ 1) :
    ¬ Summable (fun k => ρ ^ k * aCoef ρ α βs 0 k) := by
  intro hs
  have ht := ((summable_nat_add_iff 1).mpr hs).tendsto_atTop_zero
  have hc : 0 < |α * (1 - βs)| := abs_pos.mpr (mul_ne_zero hα0 (sub_ne_zero.mpr (Ne.symm hβ)))
  have hlow : ∀ k : ℕ, |α * (1 - βs)| ≤ |ρ ^ (k + 1) * aCoef ρ α βs 0 (k + 1)| := by
    intro k
    rw [appA2_23_coef, show ρ ^ (k + 1) * (-(α * (1 - βs) / ρ) * gRoot ρ α ^ k) =
        -(α * (1 - βs)) * (ρ * gRoot ρ α) ^ k by rw [mul_pow, pow_succ]; field_simp,
      gRoot, mul_div_cancel₀ _ hρ, abs_mul (-(α * (1 - βs))), abs_neg, abs_pow]
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hα)
  have ht' : Tendsto (fun n => |ρ ^ (n + 1) * aCoef ρ α βs 0 (n + 1)|) atTop (𝓝 0) := by
    simpa using ht.abs
  obtain ⟨k, hk⟩ := (ht'.eventually (gt_mem_nhds hc)).exists
  exact absurd (hlow k) (not_le.mpr hk)

/-! ### The s-shape and the facts of Figure 5.5 -/

/-- Cochrane (2023), p. 135: for `ρ > 0` and `0 < α < 1`, the first lag polynomial of (5.25),
`1 − (α/ρ)[L + gL² + …]`, is "a movement in one direction, 1, followed by a string of small
negative movements in the opposite direction". -/
theorem dCoef_succ_neg (hρ : 0 < ρ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    dCoef ρ α (k + 1) < 0 := by
  have hg : 0 < gRoot ρ α := div_pos (by linarith) hρ
  simp only [dCoef]
  have := pow_pos hg k
  have : 0 < α / ρ := div_pos hα0 hρ
  nlinarith

/-- Cochrane (2023), pp. 135, 137 (the s-shaped response; survey's `s_shape`): for `ρ > 0`,
`0 < α < 1`, `0 ≤ η < g` and `β_s < −Bρg/α` with `B = (g − ρ⁻¹)/(g − η)`, the surplus response
`a_k` is positive up to some date `K ≥ 1`, and negative after it: one sign change. -/
theorem s_shape (hρ : 0 < ρ) (hα0 : 0 < α) (hα1 : α < 1) (hη0 : 0 ≤ η)
    (hηg : η < gRoot ρ α)
    (hβ : βs < -((gRoot ρ α - ρ⁻¹) / (gRoot ρ α - η)) * ρ * gRoot ρ α / α) :
    ∃ K, 1 ≤ K ∧ (∀ k < K, 0 < aCoef ρ α βs η k) ∧ aCoef ρ α βs η K ≤ 0 ∧
      ∀ k, K < k → aCoef ρ α βs η k < 0 := by
  classical
  set g := gRoot ρ α with hgdef
  have hg0 : 0 < g := div_pos (by linarith) hρ
  have hgρ : g < ρ⁻¹ := by
    rw [hgdef, gRoot, div_eq_mul_inv]
    have := inv_pos.mpr hρ
    nlinarith
  set A := (η - ρ⁻¹) / (η - g) with hA
  set B := (g - ρ⁻¹) / (g - η) with hB
  set C := B + βs * α * ρ⁻¹ / g with hC
  have hA0 : 0 < A := div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hC0 : C < 0 := by
    have hβ' : βs * α / (ρ * g) < -B := by
      rw [div_lt_iff₀ (mul_pos hρ hg0)]
      have := (lt_div_iff₀ hα0).mp (by simpa [hB, mul_assoc] using hβ)
      nlinarith
    have : βs * α * ρ⁻¹ / g = βs * α / (ρ * g) := by field_simp
    rw [hC, this]
    linarith
  set q := η / g with hq
  have hq0 : 0 ≤ q := div_nonneg hη0 hg0.le
  have hq1 : q < 1 := (div_lt_one hg0).mpr hηg
  set h : ℕ → ℝ := fun k => A * q ^ (k + 1) + C with hh
  have hclosed : ∀ k, aCoef ρ α βs η (k + 1) = g ^ (k + 1) * h k := by
    intro k
    rw [aCoef_two_geom hηg.ne]
    simp only [hh, hq, hA, hC, hB, ← hgdef, div_pow]
    field_simp
    ring
  have hex : ∃ k, aCoef ρ α βs η k ≤ 0 := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (neg_pos.mpr hC0) hA0) hq1
    refine ⟨N + 1, ?_⟩
    rw [hclosed]
    have hle : q ^ (N + 1) ≤ q ^ N := pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ N)
    have : h N < 0 := by
      simp only [hh]
      rw [lt_div_iff₀ hA0] at hN
      nlinarith
    exact (mul_neg_of_pos_of_neg (pow_pos hg0 _) this).le
  set K := Nat.find hex with hK
  have hKspec : aCoef ρ α βs η K ≤ 0 := Nat.find_spec hex
  have hK1 : 1 ≤ K := by
    by_contra h0
    have : K = 0 := by omega
    rw [this] at hKspec
    simp only [aCoef] at hKspec
    linarith
  refine ⟨K, hK1, fun k hk => not_le.mp (Nat.find_min hex hk), hKspec, fun k hk => ?_⟩
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hhK : h K' ≤ 0 := by
    rw [hK', hclosed] at hKspec
    by_contra hc
    exact absurd hKspec (not_le.mpr (mul_pos (pow_pos hg0 _) (not_le.mp hc)))
  have hhk : h k' < 0 := by
    rcases hη0.lt_or_eq with hηpos | hη00
    · have hqpos : 0 < q := div_pos hηpos hg0
      have : q ^ (k' + 1) < q ^ (K' + 1) := pow_lt_pow_right_of_lt_one₀ hqpos hq1 (by omega)
      have : h k' < h K' := by
        simp only [hh]
        nlinarith
      linarith
    · simp only [hh, hq, ← hη00, zero_div, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_add]
      exact hC0
  rw [hclosed]
  exact mul_neg_of_pos_of_neg (pow_pos hg0 _) hhk

/-- Cochrane (2023), p. 136 (Figure 5.5): the response of a moving average to a single shock
`ε_1 = e` (zero otherwise) is `x_{k+1} = c_k e`. -/
theorem ma_impulse (c : ℕ → ℝ) (e : ℝ) (k : ℕ) (ω : Ω) :
    ma c (fun t (_ : Ω) => if t = 1 then e else 0) (k + 1) ω = c k * e := by
  rw [ma_apply, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    have := Finset.mem_range.mp hj
    have h1 : k + 1 - j ≠ 1 := by omega
    simp [h1]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- Cochrane (2023), p. 136 (Figure 5.5): after a unit deficit shock `ε_{s,1} = −1` the
discounted surplus response is `∑_{j ≥ 1} ρ^{j−1} s̃_j = −a(ρ) = −β_s`. -/
theorem fig55_pv_response (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * (aCoef ρ α βs η k * (-1))) (-βs) := by
  simpa [mul_assoc] using (hasSum_aCoef (βs := βs) hρ hα hη).mul_right (-1)

/-- Cochrane (2023), p. 136 (Figure 5.5, dashed lines): with `β_s = 0` the surpluses exactly
pay off the initial deficits, `∑_{j ≥ 1} ρ^{j−1} s̃_j = 0`, and there is no unexpected
inflation. -/
theorem fig55_betaS_zero (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * (aCoef ρ α 0 η k * (-1))) 0 := by
  simpa using fig55_pv_response (βs := 0) hρ hα hη

/-- Cochrane (2023), p. 136 (Figure 5.5, solid lines): with `β_s = 1`,
`∑_{j ≥ 1} ρ^{j−1} s̃_j = −1`: the whole initial deficit is inflated away. -/
theorem fig55_betaS_one (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * (aCoef ρ α 1 η k * (-1))) (-1) :=
  fig55_pv_response (βs := 1) hρ hα hη

/-- Cochrane (2023), p. 136 (Figure 5.5, `β_s = 1`): "the initial debt response is zero",
`v*_1 = ρ⁻¹(β_s − 1) ε_1 = 0`. -/
theorem fig55_initial_debt : vCoef ρ α 1 η 0 = 0 := by
  rw [vCoef_zero]
  ring

/-- Cochrane (2023), p. 136 (Figure 5.5, `β_s = 1`): "Debt rises subsequently". For `ρ > 0`,
`α ≤ 1` and `η > 0`, the response of `v*_{k+2}` to the deficit shock `ε_1 = −1` is
`−vCoef_{k+1} > 0`. -/
theorem fig55_debt_rises (hρ : 0 < ρ) (hα : α ≤ 1) (hη : 0 < η) (k : ℕ) :
    0 < -vCoef ρ α 1 η (k + 1) := by
  have hg : 0 ≤ gRoot ρ α := div_nonneg (by linarith) hρ.le
  have hpos : 0 < ∑ i ∈ Finset.range (k + 1), gRoot ρ α ^ i * η ^ (k + 1 - i) := by
    refine Finset.sum_pos' (fun i _ => mul_nonneg (pow_nonneg hg _) (pow_pos hη _).le)
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k), by simpa using pow_pos hη (k + 1)⟩
  have hsplit : geomConv (gRoot ρ α) η (k + 1) =
      ∑ i ∈ Finset.range (k + 1), gRoot ρ α ^ i * η ^ (k + 1 - i) + gRoot ρ α ^ (k + 1) := by
    rw [geomConv, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  unfold vCoef
  rw [hsplit]
  have := inv_pos.mpr hρ
  nlinarith

/-- Cochrane (2023), p. 136 (Figure 5.5): the disturbance alone has cumulative response
`∑_{j ≥ 1} ρ^{j−1} u_j = −1/(1 − ρη)` to `ε_{s,1} = −1`. -/
theorem fig55_u_pv (hη : |ρ * η| < 1) :
    HasSum (fun k => ρ ^ k * (η ^ k * (-1))) (-(1 - ρ * η)⁻¹) := by
  have := (hasSum_geometric_of_abs_lt_one hη).mul_right (-1)
  convert this using 1
  · funext k
    rw [mul_pow]
    ring
  · ring

/-- Cochrane (2023), p. 136 (Figure 5.5, `ρ = 1`, `η_s = 0.7`): the disturbance's cumulative
response is `−1/(1 − 0.7) = −3.33`. -/
theorem fig55_u_pv_value :
    HasSum (fun k => (1 : ℝ) ^ k * ((7 / 10 : ℝ) ^ k * (-1))) (-(10 / 3)) := by
  have h := fig55_u_pv (ρ := 1) (η := 7 / 10) (by norm_num [abs_of_pos])
  convert h using 1
  norm_num

/-! ### Present values and innovations under an `ExpectationSystem` -/

/-- Cochrane (2023), p. 136: iterating `v_t = s̃_{t+1} + ρ v_{t+1} + δ_t` with `E_t δ_t = 0`
forward gives `v_t = ∑_{j<T} ρʲ E_t s̃_{t+1+j} + ρᵀ E_t v_{t+T}`. -/
theorem partial_pv {v s δ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hrec : ∀ t, v t = s (t + 1) + ρ • v (t + 1) + δ t) (hδ : ∀ t, 𝔼.E t (δ t) = 0)
    (t T : ℕ) (ω : Ω) :
    v t ω = ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω +
      ρ ^ T * 𝔼.E t (v (t + T)) ω := by
  induction T with
  | zero => simp [hv t]
  | succ T ih =>
    have hδ' : 𝔼.E t (δ (t + T)) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right t T), hδ, map_zero]
    have h := congrArg (𝔼.E t) (hrec (t + T))
    rw [map_add, map_add, map_smul, hδ', add_zero] at h
    have h' := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
    rw [ih, Finset.sum_range_succ, h', show t + T + 1 = t + 1 + T by omega,
      show t + (T + 1) = t + 1 + T by omega, pow_succ]
    ring

/-- Cochrane (2023), p. 136 (valuation equation): under the transversality condition, a
process with `v_t = s̃_{t+1} + ρ v_{t+1} + δ_t`, `E_t δ_t = 0`, is the present value
`v_t = ∑_j ρʲ E_t s̃_{t+1+j}` (an absolutely convergent series). -/
theorem hasSum_pv {v s δ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hrec : ∀ t, v t = s (t + 1) + ρ • v (t + 1) + δ t) (hδ : ∀ t, 𝔼.E t (δ t) = 0)
    (t : ℕ) (ω : Ω) (hsum : Summable (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω))
    (htvc : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (v t ω) := by
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) atTop
      (𝓝 (v t ω)) := by
    have hEq : (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) =
        fun T => v t ω - ρ ^ T * 𝔼.E t (v (t + T)) ω := by
      funext T
      rw [partial_pv 𝔼 hv hrec hδ t T ω]
      ring
    rw [hEq]
    simpa using (tendsto_const_nhds (x := v t ω)).sub htvc
  have := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hsum.hasSum

/-- Cochrane (2023), (5.27), p. 135 (innovation of the present value): if
`v_t = s̃_{t+1} + ρ v_{t+1} + δ_t` and `v` is the present value at `t` and `t + 1`, then
`ΔE_{t+1} ∑_j ρʲ s̃_{t+1+j} = −δ_t`. -/
theorem innov_pv_generic {v s δ : ℕ → Ω → ℝ}
    (hrec : ∀ t, v t = s (t + 1) + ρ • v (t + 1) + δ t) (t : ℕ)
    (hs1 : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1)) (ω : Ω)
    (h0 : HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (v t ω))
    (h1 : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + 1 + j)) ω) (v (t + 1) ω)) :
    HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω))
      (-δ t ω) := by
  have H1 : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * v (t + 1) ω) := by
    rw [← hasSum_nat_add_iff' 1]
    convert h1.mul_left ρ using 1
    · funext n
      rw [show t + 1 + (n + 1) = t + 1 + 1 + n by omega, pow_succ]
      ring
    · simp [hs1]
  have hr := congrFun (hrec t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
  convert H1.sub h0 using 1
  · funext j
    ring
  · rw [hr]
    ring

variable {i π v : ℕ → Ω → ℝ}

/-- Cochrane (2023), §5.4, pp. 135–136 (the adaptedness of the surplus process): if `ε` is
adapted and the initial states are known at date 0, then `u` and `v*` are adapted and `s̃_{t+1}`
is known at `t + 1`. -/
theorem proc_adapted (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) :
    𝔼.Adapted u ∧ 𝔼.Adapted vs ∧ ∀ t, 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
  have hUV : ∀ t, 𝔼.E t (u t) = u t ∧ 𝔼.E t (vs t) = vs t := by
    intro t
    induction t with
    | zero => exact ⟨hu0, hv0⟩
    | succ t ih =>
      have hu : 𝔼.E (t + 1) (u (t + 1)) = u (t + 1) := by
        rw [(h t).2.2, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.1,
          hεa (t + 1)]
      refine ⟨hu, ?_⟩
      have hvs : vs (t + 1) = ρ⁻¹ • ((1 - α) • vs t + βs • ε (t + 1) - u (t + 1)) := by
        rw [← vstar_rec h t, inv_smul_smul₀ hρ]
      rw [hvs, map_smul, map_sub, map_add, map_smul, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.2, hεa (t + 1), hu]
  refine ⟨fun t => (hUV t).1, fun t => (hUV t).2, fun t => ?_⟩
  rw [(h t).1, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hUV t).2,
    (hUV (t + 1)).1]

/-- Cochrane (2023), eq. (5.24), p. 134: `u` is an AR(1) with persistence `η`. -/
theorem u_isAR1 (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) :
    𝔼.IsAR1 η u := by
  have had := (proc_adapted 𝔼 hρ h hεa hv0 hu0).1
  exact ⟨had, fun t => by rw [(h t).2.2, map_add, map_smul, had t, hε t, add_zero]⟩

/-- Cochrane (2023), pp. 135–137: the expected path of the latent debt,
`ρ E_t v*_{t+j+1} = (1 − α) E_t v*_{t+j} − η^{j+1} u_t`. -/
theorem E_vstar_rec (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (t j : ℕ) :
    ρ • 𝔼.E t (vs (t + j + 1)) = (1 - α) • 𝔼.E t (vs (t + j)) - η ^ (j + 1) • u t := by
  have hAR := u_isAR1 𝔼 hρ h hεa hε hv0 hu0
  have hr := congrArg (𝔼.E t) (vstar_rec h (t + j))
  rw [map_smul, map_sub, map_add, map_smul, map_smul,
    show t + j + 1 = t + 1 + j by omega, E_future_eq_zero 𝔼 hε t j, smul_zero, add_zero,
    show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hAR t (j + 1)] at hr
  rw [show t + j + 1 = t + (j + 1) by omega]
  exact hr

/-- Cochrane (2023), pp. 137–138: for `0 < α < 2` and `|ρη| < 1` the discounted forecasts
`ρʲ E_t v*_{t+j}` are absolutely summable (in particular they vanish: `vstar_tvc`). -/
theorem summable_vstar (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (t : ℕ)
    (ω : Ω) : Summable (fun j => ρ ^ j * 𝔼.E t (vs (t + j)) ω) := by
  refine summable_of_rec hα ((summable_geometric_of_abs_lt_one hη).mul_left (-(η * u t ω)))
    (fun j => ?_)
  have hr := congrFun (E_vstar_rec 𝔼 hρ h hεa hε hv0 hu0 t j) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [show t + (j + 1) = t + j + 1 by omega, pow_succ, mul_assoc, hr, mul_pow]
  ring

/-- Cochrane (2023), pp. 136–138: the latent debt `v*` satisfies the transversality condition
`ρᵀ E_t v*_{t+T} → 0` for `0 < α < 2`, `|ρη| < 1` (also at `ρ = 1`). -/
theorem vstar_tvc (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) :
    TVC 𝔼 ρ vs := fun t ω =>
  (summable_vstar 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω).tendsto_atTop_zero

/-- Cochrane (2023), p. 136: the discounted surplus forecasts `ρʲ E_t s̃_{t+1+j}` are absolutely
summable, so the present value is a genuine infinite sum. -/
theorem summable_pv (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (t : ℕ)
    (ω : Ω) : Summable (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) := by
  have hAR := u_isAR1 𝔼 hρ h hεa hε hv0 hu0
  have H := ((summable_vstar 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω).mul_left α).add
    ((summable_geometric_of_abs_lt_one hη).mul_left (η * u t ω))
  refine H.congr fun j => ?_
  have e1 : s (t + 1 + j) = α • vs (t + j) + u (t + (j + 1)) := by
    rw [show t + 1 + j = t + j + 1 by omega, (h (t + j)).1, show t + j + 1 = t + (j + 1) by omega]
  rw [e1, map_add, map_smul, 𝔼.ar1_iterate hAR t (j + 1)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring

/-- Cochrane (2023), p. 136 ("taking the present value … using the surplus moving average"):
the latent variable is the present value of surpluses, `v*_t = ∑_j ρʲ E_t s̃_{t+1+j}`. -/
theorem vstar_eq_pv (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (t : ℕ)
    (ω : Ω) : HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (vs t ω) := by
  refine hasSum_pv 𝔼 (δ := fun t => -(βs • ε (t + 1)))
    (proc_adapted 𝔼 hρ h hεa hv0 hu0).2.1 (fun t => ?_) (fun t => ?_) t ω
    (summable_pv 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω)
    (vstar_tvc 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω)
  · rw [(h t).2.1]
    abel
  · rw [map_neg, map_smul, hε t, smul_zero, neg_zero]

/-- Cochrane (2023), eq. (5.28), p. 135, in innovation form: the surprise in the present value
of surpluses is `ΔE_{t+1} ∑_j ρʲ s̃_{t+1+j} = β_s ε_{t+1}` (`a(ρ) ε_{t+1}` with
`a(ρ) = β_s`). -/
theorem innov_pv (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (t : ℕ)
    (ω : Ω) :
    HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω))
      (βs * ε (t + 1) ω) := by
  have H := innov_pv_generic 𝔼 (v := vs) (δ := fun t => -(βs • ε (t + 1))) (fun t => by
      rw [(h t).2.1]; abel) t ((proc_adapted 𝔼 hρ h hεa hv0 hu0).2.2 t) ω
    (vstar_eq_pv 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω)
    (vstar_eq_pv 𝔼 hρ hα hη h hεa hε hv0 hu0 (t + 1) ω)
  simpa using H

/-- Cochrane (2023), eqs. (5.26)–(5.28), p. 135: with zero pre-sample states, the surplus
innovations are the moving-average coefficients, `ΔE_{t+1} s̃_{t+1+j} = a_j ε_{t+1}`, so the
present-value innovation of `innov_pv` is `∑ ρʲ a_j ε_{t+1} = a(ρ) ε_{t+1}`. -/
theorem innov_s_eq_aCoef (hρ : ρ ≠ 0) (h : IsSurplusProc ρ α βs η ε s vs u)
    (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (hv0 : vs 0 = 0) (hu0 : u 0 = 0) (t j : ℕ) :
    𝔼.E (t + 1) (s (t + 1 + j)) - 𝔼.E t (s (t + 1 + j)) = aCoef ρ α βs η j • ε (t + 1) := by
  rw [show t + 1 + j = t + j + 1 by omega, (ma_representation hρ h hv0 hu0 (t + j)).2.2,
    show t + j + 1 = t + 1 + j by omega]
  exact innov_ma 𝔼 hεa hε _ t j

/-- Cochrane (2023), eq. (5.27), p. 135, and (3.17): the frictionless model with one-period
debt, `i_t = E_t π_{t+1}` and `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def Frictionless (ρ : ℝ) (i π s v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), p. 136: unexpected inflation `ΔE_{t+1} π_{t+1} = π_{t+1} − E_t π_{t+1}`
(indexed by `t`). -/
def surprise (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := π (t + 1) - 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 136: unexpected inflation has date-`t` forecast zero. -/
theorem E_surprise (π : ℕ → Ω → ℝ) (t : ℕ) : 𝔼.E t (surprise 𝔼 π t) = 0 := by
  rw [surprise, map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), p. 136: with `i_t = E_t π_{t+1}` the debt identity reads
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s̃_{t+1}`. -/
theorem frictionless_flow (h : Frictionless 𝔼 ρ i π s v) (t : ℕ) :
    ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) := by
  obtain ⟨hi, hv⟩ := h t
  rw [hv, hi, surprise]
  abel

/-- Cochrane (2023), p. 136: the debt identity solved for `v_t`. -/
theorem frictionless_debt (h : Frictionless 𝔼 ρ i π s v) (t : ℕ) :
    v t = s (t + 1) + ρ • v (t + 1) + surprise 𝔼 π t := by
  rw [frictionless_flow 𝔼 h t]
  abel

/-- Cochrane (2023), eq. (5.27), p. 135: in the frictionless model, if debt satisfies the
transversality condition and the present values converge absolutely, unexpected inflation is
the negative of the innovation in the present value of surpluses,
`ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑_j ρʲ s̃_{t+1+j}`. -/
theorem unexpected_inflation_527 (h : Frictionless 𝔼 ρ i π s v) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) (hs1 : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1)) (ω : Ω)
    (hsum0 : Summable (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω))
    (hsum1 : Summable (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + 1 + j)) ω)) :
    HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω))
      (-surprise 𝔼 π t ω) :=
  innov_pv_generic 𝔼 (frictionless_debt 𝔼 h) t hs1 ω
    (hasSum_pv 𝔼 hv (frictionless_debt 𝔼 h) (E_surprise 𝔼 π) t ω hsum0 (htvc t ω))
    (hasSum_pv 𝔼 hv (frictionless_debt 𝔼 h) (E_surprise 𝔼 π) (t + 1) ω hsum1 (htvc (t + 1) ω))

/-- Cochrane (2023), eqs. (5.27)–(5.28), p. 135, and p. 136: in the frictionless model with the
surplus process (5.22)–(5.24), any debt path satisfying the transversality condition has
`ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}`, and debt equals the latent variable, `v_t = v*_t`
("in equilibrium, debt `v_t` turns out to be equal to the latent variable `v*_t`"). -/
theorem equilibrium_528 (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0)
    (hf : Frictionless 𝔼 ρ i π s v) (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) :
    ∀ t, v t = vs t ∧ surprise 𝔼 π t = -(βs • ε (t + 1)) := by
  have hvv : ∀ t, v t = vs t := fun t => funext fun ω =>
    (hasSum_pv 𝔼 hv (frictionless_debt 𝔼 hf) (E_surprise 𝔼 π) t ω
      (summable_pv 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω) (htvc t ω)).unique
      (vstar_eq_pv 𝔼 hρ hα hη h hεa hε hv0 hu0 t ω)
  refine fun t => ⟨hvv t, ?_⟩
  have h1 := frictionless_flow 𝔼 hf t
  have h2 := (h t).2.1
  rw [hvv t, hvv (t + 1)] at h1
  rw [h1] at h2
  have : surprise 𝔼 π t = vs t - s (t + 1) - (vs t + βs • ε (t + 1) - s (t + 1)) := by
    rw [← h2]
    abel
  rw [this]
  abel

/-- Cochrane (2023), p. 136 (`v_t = E_t ∑_{j ≥ 0} ρʲ s_{t+1+j}`): for `0 ≤ ρ < 1` and bounded
surpluses, the expectation of the discounted sum equals the sum of the discounted forecasts. -/
theorem E_pv_eq_tsum (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {M : ℝ} (hM : ∀ t ω, |s t ω| ≤ M) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (fun ω' => ∑' j, ρ ^ j * s (t + 1 + j) ω') ω =
      ∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω := by
  have hu : Summable (fun j : ℕ => ρ ^ j * M) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_right M
  rw [ForwardSolution.E_tsum_dom 𝔼 hu (f := fun j ω' => ρ ^ j * s (t + 1 + j) ω') (fun j ω' => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
    exact mul_le_mul_of_nonneg_left (hM _ _) (pow_nonneg hρ0 j)) t ω]
  refine tsum_congr fun j => ?_
  change 𝔼.E t (ρ ^ j • s (t + 1 + j)) ω = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

end Cochrane.StickyPriceFiscal.SurplusProcess
