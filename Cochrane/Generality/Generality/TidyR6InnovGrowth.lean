/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.LogLinearIdentities
import Generality.ExpectationsFiniteTree

/-!
# The linear innovation identities beyond bounded processes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, pp. 63–71
((3.17)–(3.28)), and Online Appendix A1.3, pp. 561–564.

`LogLinearIdentities` proved (3.19)–(3.28) for bounded ("stationary", p. 64) processes with
`0 < ρ < 1` (`LogLinearIdentities.LinearEconomy`). The book says (p. 64) that the terminal term
vanishes when debt/GDP "is expected to grow no faster than `ρ^{−t}`", and that with `ρ = 1`
(3.19) "continues to hold describing deviations from" the mean. This module settles the general
case on an arbitrary `ExpectationSystem`.

## Exact characterisation (any `ρ`, only summability)

With the present-value series summable at `t` and `t + 1`, the terminal terms
`L_t = lim ρ^T E_t v_{t+T}` exist (`terminal_tendsto`), and the innovations of the discounted
flow sum to `L_t − ρL_{t+1}` (`innov_pv_general`). Hence the unexpected-inflation identity (3.20)
holds with the extra term `L_t − ρL_{t+1}` (`identity_3_20_general`), and the printed (3.20)
holds **iff** `L_t = ρL_{t+1}` (`identity_3_20_iff`). In particular it holds under the
transversality conditions (`identity_3_20_of_tvc`) and, for `ρ = 1`, when `E_t v_{t+T}` and
`E_{t+1}v_{t+1+T}` converge to the same constant mean (`identity_3_20_rho_one_mean`, the book's
"deviations from this mean").

## Exponential growth below `1/ρ`

`GrowthBound γ x`: `|x_n| ≤ Kγⁿ` in every state. `GrowthEconomy`: (3.17), adapted processes,
`ρ > 0`, `γ ≥ 0`, `ργ < 1`, all five processes with growth `γ`; every `LinearEconomy` is one with
`γ = 1` (`LinearEconomy.toGrowth`), and `ρ ≥ 1` is allowed when `γ < 1/ρ`. In it: (3.19)
(`g_pv_319`), the innovation sum (`g_innov_pv`), (3.20) (`g_identity_3_20`); with a log bond price
of growth `γ` and `|ω̂|γ < 1`: the bond-price forward sum (`g_bondPrice_forward`), (3.21)
(`g_bondReturn_innov`), (3.22) (`g_weighted_inflation`), and the special cases (3.23)
(`g_special_constant_long`), (3.24) (`g_identity_3_24`), (3.25) (`g_identity_3_25`), (3.27)
(`g_special_constant_short`), (3.28) (`g_monetary_disinflation`) and §3.5.4
(`g_perpetuity`).

## The boundary `γ = 1/ρ` (counterexamples)

On the coin-flip tree, for every `ρ > 0` an economy with every process of growth `1/ρ` (so
`ργ = 1`) violates (3.20) at date 0 in every state and (3.19) at date 1
(`Boundary.boundary_3_20`); at `ρ = 1` all its processes are bounded
(`Boundary.rho_one_bounded`), so boundedness alone does not give (3.20) with `ρ = 1`. Likewise a
log bond price of growth `1/|ω̂|` violates (3.21) (`Boundary.boundary_3_21`). So "no faster than
`ρ^{−t}`" (p. 64) must be read as "strictly slower" (or as the transversality condition
itself).
-/

namespace Cochrane.Generality.TidyR6InnovGrowth

open Filter Topology
open Cochrane.Generality.LogLinearIdentities

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Exact characterisation under summability -/

variable {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ}

/-- Cochrane (2023), (3.18), p. 63: `s̃ + g − r` is adapted when its components are. -/
theorem zp_adapted' (hs : 𝔼.Adapted sT) (hg : 𝔼.Adapted g) (hr : 𝔼.Adapted rn)
    (hi : 𝔼.Adapted infl) : 𝔼.Adapted (zp rn infl g sT) := by
  intro n
  simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub, hs n, hg n, hr n, hi n]

/-- Cochrane (2023), (3.18)–(3.19), pp. 63–64: if the present-value series is summable, the
terminal term converges, `ρ^T E_t v_{t+T} → v_t − ∑_j ρ^j E_t(s̃ + g − r)_{t+1+j}`. -/
theorem terminal_tendsto (hf : Flow317 ρ v rn infl g sT) (hv : 𝔼.Adapted v) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 (v t ω - ∑' j, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)) := by
  have he : ∀ T, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
    intro T
    have h := congrFun (pv_318_E 𝔼 hf hv t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  simp_rw [he]
  exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat

/-- Cochrane (2023), p. 64, "Taking time `t + 1` innovations of (3.19)", **in general**: if the
present-value series are summable at `t` and `t + 1` and the terminal terms converge,
`ρ^T E_t v_{t+T} → L₀` and `ρ^T E_{t+1} v_{t+1+T} → L₁`, then the innovations of the discounted
flow sum to `L₀ − ρL₁`: `∑_j ρ^j ΔE_{t+1}(s̃ + g − r)_{t+1+j} = L₀ − ρL₁`. -/
theorem innov_pv_general (hf : Flow317 ρ v rn infl g sT) (hv : 𝔼.Adapted v)
    (hz : 𝔼.Adapted (zp rn infl g sT)) (t : ℕ) (ω : Ω) {L₀ L₁ : ℝ}
    (hs0 : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
    (hs1 : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
    (hL0 : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 L₀))
    (hL1 : Tendsto (fun T => ρ ^ T * 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 L₁)) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω) (L₀ - ρ * L₁) := by
  have e0 := tendsto_nhds_unique (terminal_tendsto 𝔼 hf hv t ω hs0) hL0
  have e1 := tendsto_nhds_unique (terminal_tendsto 𝔼 hf hv (t + 1) ω hs1) hL1
  have ha : HasSum (fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) (v t ω - L₀) := by
    convert hs0.hasSum using 1
    linarith
  have hb : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
      (v (t + 1) ω - L₁) := by
    convert hs1.hasSum using 1
    linarith
  have hflow : v t ω - zp rn infl g sT (t + 1) ω = ρ * v (t + 1) ω := by
    simp only [zp, Pi.add_apply, Pi.sub_apply]
    linarith [hf t ω]
  have hb' : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + j + 1)) ω)
      (v t ω - ρ * L₁) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero]
    rw [hz (t + 1)]
    convert hb.mul_left ρ using 1
    · funext j
      rw [show t + (j + 1) + 1 = t + 1 + j + 1 by omega, pow_succ]
      ring
    · linarith
  have h := hb'.sub ha
  convert h using 1
  · funext j
    rw [innov_apply]
    ring
  · ring

/-- Cochrane (2023), (3.20), p. 65, **in general**: under summability of the present-value
series at `t`, `t + 1` and of the innovation series, with terminal limits `L₀`, `L₁`,
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑ρ^jΔE_{t+1}s̃_{t+1+j} − ∑ρ^jΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1}ρ^jΔE_{t+1}r_{t+1+j} + (L₀ − ρL₁)`. -/
theorem identity_3_20_general (hf : Flow317 ρ v rn infl g sT) (hv : 𝔼.Adapted v)
    (hz : 𝔼.Adapted (zp rn infl g sT)) (t : ℕ) (ω : Ω) {L₀ L₁ : ℝ}
    (hs0 : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
    (hs1 : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
    (hL0 : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 L₀))
    (hL1 : Tendsto (fun T => ρ ^ T * 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 L₁))
    (hS : Summable fun j => ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω)
    (hG : Summable fun j => ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω)
    (hR : Summable fun j => ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω + (L₀ - ρ * L₁) := by
  have h := (innov_pv_general 𝔼 hf hv hz t ω hs0 hs1 hL0 hL1).tsum_eq
  have hsplit : ∀ j, ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω =
      ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω + ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω -
        ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω := by
    intro j
    simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub]
    ring
  rw [tsum_congr hsplit, (hS.add hG).tsum_sub hR, hS.tsum_add hG] at h
  have hr0 : ∑' j, ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω =
      (innov 𝔼 t (rn (t + 1)) ω - innov 𝔼 t (infl (t + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
    rw [hR.tsum_eq_zero_add]
    congr 1
    simp only [pow_zero, one_mul, add_zero, Pi.sub_apply, map_sub]
  rw [hr0] at h
  linarith

/-- Cochrane (2023), (3.20), p. 65, **necessary and sufficient condition**: under the hypotheses
of `identity_3_20_general`, the printed unexpected-inflation identity holds iff the terminal
limits satisfy `L₀ = ρL₁`. -/
theorem identity_3_20_iff (hf : Flow317 ρ v rn infl g sT) (hv : 𝔼.Adapted v)
    (hz : 𝔼.Adapted (zp rn infl g sT)) (t : ℕ) (ω : Ω) {L₀ L₁ : ℝ}
    (hs0 : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
    (hs1 : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
    (hL0 : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 L₀))
    (hL1 : Tendsto (fun T => ρ ^ T * 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 L₁))
    (hS : Summable fun j => ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω)
    (hG : Summable fun j => ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω)
    (hR : Summable fun j => ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω ↔ L₀ = ρ * L₁ := by
  rw [identity_3_20_general 𝔼 hf hv hz t ω hs0 hs1 hL0 hL1 hS hG hR]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, sub_self, add_zero]

/-- Cochrane (2023), (3.20), p. 65: under the transversality conditions at `t` and `t + 1`
(`ρ^T E_t v_{t+T} → 0`), the printed identity holds, for any `ρ` and any processes with the
stated summability. -/
theorem identity_3_20_of_tvc (hf : Flow317 ρ v rn infl g sT) (hv : 𝔼.Adapted v)
    (hz : 𝔼.Adapted (zp rn infl g sT)) (t : ℕ) (ω : Ω)
    (hs0 : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
    (hs1 : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
    (hL0 : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0))
    (hL1 : Tendsto (fun T => ρ ^ T * 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 0))
    (hS : Summable fun j => ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω)
    (hG : Summable fun j => ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω)
    (hR : Summable fun j => ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω :=
  (identity_3_20_iff 𝔼 hf hv hz t ω hs0 hs1 hL0 hL1 hS hG hR).mpr (by ring)

/-- Cochrane (2023), p. 64 ("If we use `ρ = 1`, then `E_t v_{t+T} → E(v)`, and equation (3.19)
continues to hold describing deviations from this mean"), for (3.20): with `ρ = 1`, if
`E_t v_{t+T}` and `E_{t+1} v_{t+1+T}` converge to the **same constant** `v̄` and the series are
summable, the innovation identity (3.20) holds. -/
theorem identity_3_20_rho_one_mean {v rn infl g sT : ℕ → Ω → ℝ}
    (hf : Flow317 1 v rn infl g sT) (hv : 𝔼.Adapted v)
    (hz : 𝔼.Adapted (zp rn infl g sT)) (t : ℕ) (ω : Ω) {vbar : ℝ}
    (hs0 : Summable fun j => (1 : ℝ) ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
    (hs1 : Summable fun j => (1 : ℝ) ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + 1 + j + 1)) ω)
    (hL0 : Tendsto (fun T => 𝔼.E t (v (t + T)) ω) atTop (𝓝 vbar))
    (hL1 : Tendsto (fun T => 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 vbar))
    (hS : Summable fun j => (1 : ℝ) ^ j * innov 𝔼 t (sT (t + j + 1)) ω)
    (hG : Summable fun j => (1 : ℝ) ^ j * innov 𝔼 t (g (t + j + 1)) ω)
    (hR : Summable fun j => (1 : ℝ) ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, (1 : ℝ) ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, (1 : ℝ) ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, (1 : ℝ) ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h0 : Tendsto (fun T => (1 : ℝ) ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 vbar) := by
    simpa using hL0
  have h1 : Tendsto (fun T => (1 : ℝ) ^ T * 𝔼.E (t + 1) (v (t + 1 + T)) ω) atTop (𝓝 vbar) := by
    simpa using hL1
  exact (identity_3_20_iff 𝔼 hf hv hz t ω hs0 hs1 h0 h1 hS hG hR).mpr (by ring)

/-! ### Exponential growth below `1/ρ` -/

/-- Cochrane (2023), p. 64 ("expected to grow no faster than `ρ^{−t}`"): the process grows at most
at rate `γ`, `|x_n| ≤ Kγⁿ` in every state, with `K ≥ 0`. -/
def GrowthBound (γ : ℝ) (x : ℕ → Ω → ℝ) : Prop := ∃ K, 0 ≤ K ∧ ∀ n ω, |x n ω| ≤ K * γ ^ n

/-- Cochrane (2023), (3.17)–(3.18): growth bounds add. -/
theorem GrowthBound.add {γ : ℝ} {x y : ℕ → Ω → ℝ} (hx : GrowthBound γ x) (hy : GrowthBound γ y) :
    GrowthBound γ (x + y) := by
  obtain ⟨K, hK, hxK⟩ := hx
  obtain ⟨L, hL, hyL⟩ := hy
  exact ⟨K + L, add_nonneg hK hL, fun n ω => (abs_add_le _ _).trans (by
    rw [add_mul]; exact add_le_add (hxK n ω) (hyL n ω))⟩

/-- Cochrane (2023), (3.17)–(3.18): growth bounds subtract. -/
theorem GrowthBound.sub {γ : ℝ} {x y : ℕ → Ω → ℝ} (hx : GrowthBound γ x) (hy : GrowthBound γ y) :
    GrowthBound γ (x - y) := by
  obtain ⟨K, hK, hxK⟩ := hx
  obtain ⟨L, hL, hyL⟩ := hy
  exact ⟨K + L, add_nonneg hK hL, fun n ω => (abs_sub _ _).trans (by
    rw [add_mul]; exact add_le_add (hxK n ω) (hyL n ω))⟩

variable (ρ) (γ : ℝ) (v rn infl g sT)

/-- Cochrane (2023), §3.5, pp. 63–65, beyond bounded processes: (3.17) at every date, adapted
processes, `ρ > 0`, a growth rate `γ ≥ 0` with `ργ < 1`, and debt, returns, inflation, growth and
surpluses all growing at most at rate `γ` ("no faster than `ρ^{−t}`", p. 64, strictly). -/
structure GrowthEconomy where
  flow : Flow317 ρ v rn infl g sT
  v_adapted : 𝔼.Adapted v
  rn_adapted : 𝔼.Adapted rn
  infl_adapted : 𝔼.Adapted infl
  g_adapted : 𝔼.Adapted g
  s_adapted : 𝔼.Adapted sT
  rho_pos : 0 < ρ
  gamma_nonneg : 0 ≤ γ
  rho_gamma : ρ * γ < 1
  v_growth : GrowthBound γ v
  rn_growth : GrowthBound γ rn
  infl_growth : GrowthBound γ infl
  g_growth : GrowthBound γ g
  s_growth : GrowthBound γ sT

variable {𝔼 ρ γ v rn infl g sT}

/-- Cochrane (2023), §3.5, p. 64: every bounded linear economy (`LogLinearIdentities.LinearEconomy`)
is a growth economy with `γ = 1`. -/
theorem LinearEconomy.toGrowth (hL : LinearEconomy 𝔼 ρ v rn infl g sT) :
    GrowthEconomy 𝔼 ρ v rn infl g sT 1 := by
  have hb : ∀ {x : ℕ → Ω → ℝ}, BoundedProc x → GrowthBound 1 x := fun {x} hx => by
    obtain ⟨M, hM⟩ := hx
    exact ⟨max M 0, le_max_right _ _, fun n ω => by
      rw [one_pow, mul_one]; exact (hM n ω).trans (le_max_left _ _)⟩
  exact ⟨hL.flow, hL.v_adapted, hL.rn_adapted, hL.infl_adapted, hL.g_adapted, hL.s_adapted,
    hL.rho_pos, zero_le_one, by rw [mul_one]; exact hL.rho_lt_one, hb hL.v_bdd, hb hL.rn_bdd,
    hb hL.infl_bdd, hb hL.g_bdd, hb hL.s_bdd⟩

variable (𝔼) in
/-- Cochrane (2023), (3.19)–(3.22) (auxiliary): `∑_j aʲE_s x_{t+j+c}` converges absolutely when
`x` grows at rate `γ` and `|a|γ < 1`. -/
theorem summable_E_growth {a γ K : ℝ} (hγ : 0 ≤ γ) (ha : |a| * γ < 1)
    {x : ℕ → Ω → ℝ} (hx : ∀ n ω, |x n ω| ≤ K * γ ^ n) (s t c : ℕ) (ω : Ω) :
    Summable fun j => a ^ j * 𝔼.E s (x (t + j + c)) ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg a) hγ) ha).mul_left (K * γ ^ (t + c))) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |a| ^ j * |𝔼.E s (x (t + j + c)) ω| ≤ |a| ^ j * (K * γ ^ (t + j + c)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx (t + j + c)) s ω) (pow_nonneg (abs_nonneg a) j)
    _ = K * γ ^ (t + c) * (|a| * γ) ^ j := by
        rw [mul_pow, show t + j + c = (t + c) + j by omega, pow_add]
        ring

variable (𝔼) in
/-- Cochrane (2023), (3.20)–(3.22) (auxiliary): `∑_j aʲΔE_{t+1}x_{t+j+c}` converges absolutely when
`x` grows at rate `γ` and `|a|γ < 1`. -/
theorem summable_innov_growth {a γ K : ℝ} (hγ : 0 ≤ γ) (ha : |a| * γ < 1)
    {x : ℕ → Ω → ℝ} (hx : ∀ n ω, |x n ω| ≤ K * γ ^ n) (t c : ℕ) (ω : Ω) :
    Summable fun j => a ^ j * innov 𝔼 t (x (t + j + c)) ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg a) hγ) ha).mul_left (2 * K * γ ^ (t + c))) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |a| ^ j * |innov 𝔼 t (x (t + j + c)) ω| ≤ |a| ^ j * (2 * (K * γ ^ (t + j + c))) :=
        mul_le_mul_of_nonneg_left (abs_innov_le (hx (t + j + c)) t ω) (pow_nonneg (abs_nonneg a) j)
    _ = 2 * K * γ ^ (t + c) * (|a| * γ) ^ j := by
        rw [mul_pow, show t + j + c = (t + c) + j by omega, pow_add]
        ring

variable (𝔼) in
/-- Cochrane (2023), p. 64: if `v` grows at rate `γ` and `|a|γ < 1`, the terminal term
`aᵀE_t v_{t+T}` vanishes. -/
theorem terminal_growth {a γ K : ℝ} (hγ : 0 ≤ γ) (ha : |a| * γ < 1) {x : ℕ → Ω → ℝ}
    (hx : ∀ n ω, |x n ω| ≤ K * γ ^ n) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => a ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (a := fun T => K * γ ^ t * (|a| * γ) ^ T) (fun T => ?_) ?_
  · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow]
    calc |a| ^ T * |𝔼.E t (x (t + T)) ω| ≤ |a| ^ T * (K * γ ^ (t + T)) :=
          mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx (t + T)) t ω) (pow_nonneg (abs_nonneg a) T)
      _ = K * γ ^ t * (|a| * γ) ^ T := by rw [mul_pow, pow_add]; ring
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (abs_nonneg a) hγ)
      ha).const_mul (K * γ ^ t)

/-- Cochrane (2023), (3.18), p. 63: `s̃ + g − r` grows at rate `γ` in a growth economy. -/
theorem GrowthEconomy.zp_growth (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) :
    GrowthBound γ (zp rn infl g sT) :=
  (hG.s_growth.add hG.g_growth).sub (hG.rn_growth.sub hG.infl_growth)

/-- Cochrane (2023), §3.5: `|ρ|γ < 1` in a growth economy. -/
theorem GrowthEconomy.abs_rho_gamma (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) : |ρ| * γ < 1 := by
  rw [abs_of_pos hG.rho_pos]; exact hG.rho_gamma

/-- Cochrane (2023), (3.19), p. 64, **for processes growing at rate `γ < 1/ρ`**: the infinite
present-value identity `v_t = ∑_{j≥1} ρ^{j−1}E_t(s̃ + g − r)_{t+j}` holds as a convergent sum. -/
theorem g_pv_319 (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) (v t ω) := by
  obtain ⟨K, hK, hzK⟩ := hG.zp_growth
  obtain ⟨Kv, -, hvK⟩ := hG.v_growth
  have hs := summable_E_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hzK t t 1 ω
  have h := (pv_319_iff 𝔼 hG.flow hG.v_adapted t ω hs).mp
    (terminal_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hvK t ω)
  rw [h]
  exact hs.hasSum

/-- Cochrane (2023), p. 64, for growth economies: `∑_j ρ^jΔE_{t+1}(s̃ + g − r)_{t+1+j} = 0`. -/
theorem g_innov_pv (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω) 0 := by
  obtain ⟨K, hK, hzK⟩ := hG.zp_growth
  obtain ⟨Kv, -, hvK⟩ := hG.v_growth
  have hz := zp_adapted' 𝔼 hG.s_adapted hG.g_adapted hG.rn_adapted hG.infl_adapted
  have h := innov_pv_general 𝔼 hG.flow hG.v_adapted hz t ω
    (summable_E_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hzK t t 1 ω)
    (summable_E_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hzK (t + 1) (t + 1) 1 ω)
    (terminal_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hvK t ω)
    (terminal_growth 𝔼 hG.gamma_nonneg hG.abs_rho_gamma hvK (t + 1) ω)
  simpa using h

/-- Cochrane (2023), (3.20), p. 65, **for processes growing at rate `γ < 1/ρ`** (any `ρ > 0`):
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑ρ^jΔE_{t+1}s̃_{t+1+j} − ∑ρ^jΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1}ρ^jΔE_{t+1}r_{t+1+j}`. -/
theorem g_identity_3_20 (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  obtain ⟨K, hK, hzK⟩ := hG.zp_growth
  obtain ⟨Kv, -, hvK⟩ := hG.v_growth
  obtain ⟨Ks, hKs, hsK⟩ := hG.s_growth
  obtain ⟨Kg, hKg, hgK⟩ := hG.g_growth
  obtain ⟨Kr, hKr, hrK⟩ := hG.rn_growth.sub hG.infl_growth
  have hγ := hG.gamma_nonneg
  have hρ := hG.abs_rho_gamma
  exact identity_3_20_of_tvc 𝔼 hG.flow hG.v_adapted
    (zp_adapted' 𝔼 hG.s_adapted hG.g_adapted hG.rn_adapted hG.infl_adapted) t ω
    (summable_E_growth 𝔼 hγ hρ hzK t t 1 ω)
    (summable_E_growth 𝔼 hγ hρ hzK (t + 1) (t + 1) 1 ω)
    (terminal_growth 𝔼 hγ hρ hvK t ω) (terminal_growth 𝔼 hγ hρ hvK (t + 1) ω)
    (summable_innov_growth 𝔼 hγ hρ hsK t 1 ω) (summable_innov_growth 𝔼 hγ hρ hgK t 1 ω)
    (summable_innov_growth 𝔼 hγ hρ hrK t 1 ω)

/-! ### The bond identities (3.21)–(3.22) with growth -/

/-- Cochrane (2023), A1 (1.24), p. 563: if the log bond price grows at rate `γ`, so does the
bond return: `|r^n_{n+1}| ≤ K(|ω̂|γ + 1)γⁿ`. -/
theorem g_rn_bound {ωh γ K : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hK : ∀ n ω, |q n ω| ≤ K * γ ^ n) (n : ℕ) (ω : Ω) :
    |rn (n + 1) ω| ≤ K * (|ωh| * γ + 1) * γ ^ n := by
  rw [hret]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (hK (n + 1) ω) (abs_nonneg ωh)
  have h2 := hK n ω
  have e : K * (|ωh| * γ + 1) * γ ^ n = |ωh| * (K * γ ^ (n + 1)) + K * γ ^ n := by ring
  rw [e]
  exact add_le_add h1 h2

/-- Cochrane (2023), A1 p. 564 (the corrected box formula, survey E16), **for a log bond price
growing at rate `γ` with `|ω̂|γ < 1`**: `q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`. -/
theorem g_bondPrice_forward {ωh γ : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hγ : 0 ≤ γ) (hq : GrowthBound γ q) (hω : |ωh| * γ < 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-q t ω) := by
  obtain ⟨K, hK0, hK⟩ := hq
  have hrec : ∀ n, q n ω = -rn (n + 1) ω + ωh * q (n + 1) ω := fun n => by
    rw [hret n ω]; ring
  have hs : Summable fun j => (∏ k ∈ Finset.range j, ωh) * -rn (t + j + 1) ω := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one
      (mul_nonneg (abs_nonneg ωh) hγ) hω).mul_left (K * (|ωh| * γ + 1) * γ ^ t)) fun j => ?_
    rw [Finset.prod_const, Finset.card_range, Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
    calc |ωh| ^ j * |rn (t + j + 1) ω| ≤ |ωh| ^ j * (K * (|ωh| * γ + 1) * γ ^ (t + j)) :=
          mul_le_mul_of_nonneg_left (g_rn_bound hret hK (t + j) ω)
            (pow_nonneg (abs_nonneg _) j)
      _ = K * (|ωh| * γ + 1) * γ ^ t * (|ωh| * γ) ^ j := by rw [mul_pow, pow_add]; ring
  have hterm : Tendsto (fun T => (∏ k ∈ Finset.range T, ωh) * q (t + T) ω) atTop (𝓝 0) := by
    simp only [Finset.prod_const, Finset.card_range]
    simpa [perfectForesight] using terminal_growth perfectForesight (a := ωh) hγ hω
      (x := fun n _ => q n ω) (fun n _ => hK n ω) t ()
  have h := (Money.pv_discount_iff (x := fun n => q n ω) (a := fun n => -rn (n + 1) ω)
    (b := fun _ => ωh) hrec t hs).mp hterm
  simp only [Finset.prod_const, Finset.card_range] at h hs
  have h2 : HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-(∑' j, ωh ^ j * -rn (t + j + 1) ω)) := by
    have := hs.hasSum.neg
    convert this using 1
    funext j
    ring
  rw [← h] at h2
  exact h2

/-- Cochrane (2023), (3.21) and A1 (1.25), p. 564, **for a log bond price growing at rate `γ`
with `|ω̂|γ < 1`**: `ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}r^n_{t+1+j}`. -/
theorem g_bondReturn_innov {ωh γ : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hqa : 𝔼.Adapted q) (hγ : 0 ≤ γ) (hq : GrowthBound γ q) (hω : |ωh| * γ < 1) (t : ℕ)
    (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω := by
  obtain ⟨K, hK0, hK⟩ := hq
  have hfwd : q (t + 1) = fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω' := by
    funext ω'
    have h := (g_bondPrice_forward hret hγ ⟨K, hK0, hK⟩ hω (t + 1) ω').tsum_eq
    have e : ∑' j, ωh ^ j * rn (t + j + 2) ω' = ∑' j, ωh ^ j * rn (t + 1 + j + 1) ω' :=
      tsum_congr fun j => by rw [show t + 1 + j + 1 = t + j + 2 by omega]
    rw [e, h, neg_neg]
  set C := K * (|ωh| * γ + 1) * γ ^ (t + 1) with hC
  have hu : Summable fun j : ℕ => C * (|ωh| * γ) ^ j :=
    (summable_geometric_of_lt_one (mul_nonneg (abs_nonneg ωh) hγ) hω).mul_left _
  have hb : ∀ j ω', |(ωh ^ j • rn (t + j + 2)) ω'| ≤ C * (|ωh| * γ) ^ j := by
    intro j ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |ωh| ^ j * |rn (t + j + 1 + 1) ω'| ≤ |ωh| ^ j * (K * (|ωh| * γ + 1) * γ ^ (t + j + 1)) :=
          mul_le_mul_of_nonneg_left (g_rn_bound hret hK (t + j + 1) ω')
            (pow_nonneg (abs_nonneg _) j)
      _ = C * (|ωh| * γ) ^ j := by
          rw [hC, mul_pow, show t + j + 1 = (t + 1) + j by omega, pow_add]; ring
  have hE : ∀ s, 𝔼.E s (q (t + 1)) ω = -∑' j, ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := by
    intro s
    have h := ForwardSolution.E_tsum_dom 𝔼 hu hb s ω
    simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
    rw [hfwd, show (fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω') =
      -(fun ω' => ∑' j, ωh ^ j * rn (t + j + 2) ω') from rfl, map_neg, Pi.neg_apply, h]
  have hsum : ∀ s, Summable fun j => ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := fun s =>
    Summable.of_norm_bounded hu fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have h1 := 𝔼.abs_E_le (fun ω' => (hb j ω')) s ω
      simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h1
      rw [abs_mul, abs_pow] at h1
      exact h1
  have hrn : rn (t + 1) = ωh • q (t + 1) - q t := by
    funext ω'
    rw [hret t ω']
    rfl
  have hq0 : innov 𝔼 t (q t) = 0 := innov_known (hqa t)
  have key : ∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh * (∑' j, ωh ^ j * 𝔼.E (t + 1) (rn (t + j + 2)) ω -
        ∑' j, ωh ^ j * 𝔼.E t (rn (t + j + 2)) ω) := by
    rw [← (hsum (t + 1)).tsum_sub (hsum t), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [innov_apply, pow_succ]
    ring
  rw [hrn, map_sub, map_smul, hq0, sub_zero, Pi.smul_apply, smul_eq_mul, innov_apply, hE, hE,
    key]
  ring

/-- Cochrane (2023), (3.22), p. 65, **in a growth economy with a log bond price of growth `γ`
and `|ω̂|γ < 1`**: `∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = −∑ρ^jΔE_{t+1}s̃_{t+1+j}
  − ∑ρ^jΔE_{t+1}g_{t+1+j} + ∑_{j≥1}(ρ^j − ω̂^j)ΔE_{t+1}r_{t+1+j}`. -/
theorem g_weighted_inflation (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hqa : 𝔼.Adapted q) (hq : GrowthBound γ q)
    (hω : |ωh| * γ < 1) (t : ℕ) (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
          innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h20 := g_identity_3_20 hG t ω
  have h21 := g_bondReturn_innov hret hqa hG.gamma_nonneg hq hω t ω
  have hγ := hG.gamma_nonneg
  have hρ := hG.abs_rho_gamma
  obtain ⟨Kr, hKr, hr⟩ := hG.rn_growth.sub hG.infl_growth
  obtain ⟨K4, hK4, h4⟩ := hG.infl_growth
  have hRρ := (summable_innov_growth 𝔼 hγ hρ hr t 2 ω).mul_left ρ
  have hRω := (summable_innov_growth 𝔼 hγ hω hr t 2 ω).mul_left ωh
  have hPiω := (summable_innov_growth 𝔼 hγ hω h4 t 2 ω).mul_left ωh
  have hPi0 := summable_innov_growth 𝔼 hγ hω h4 t 1 ω
  simp only [← mul_assoc, ← pow_succ'] at hRρ hRω hPiω
  have hsplit : ∀ j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω +
        ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    intro j
    simp only [Pi.sub_apply, map_sub]
    ring
  rw [tsum_congr hsplit, hRω.tsum_add hPiω] at h21
  have hL0 : ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    rw [hPi0.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    rfl
  have hdiff : ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
      innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω =
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω := by
    rw [← Summable.tsum_sub
      (f := fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω) hRρ hRω]
    refine tsum_congr fun j => ?_
    simp only [Pi.sub_apply]
    ring
  rw [hL0, hdiff]
  change _ = -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
      (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
      (∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω)
  linarith

/-! ### The special cases (3.23)–(3.28) with growth -/

/-- Cochrane (2023), §3.5.2, p. 66, and (3.27), p. 69, in a growth economy: with constant expected
returns, one-period debt (`ω̂ = 0`) and no growth,
`ΔE_{t+1}π_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem g_special_constant_short (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) {q : ℕ → Ω → ℝ}
    (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := g_identity_3_20 hG t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero, (short_debt_return_known hret hq t).2] at h
  exact h

/-- Cochrane (2023), (3.23), p. 67, in a growth economy with a log bond price of growth `γ`,
`|ω̂|γ < 1`: with constant expected returns and no growth,
`∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = −∑_{j≥0} ρ^jΔE_{t+1}s̃_{t+1+j}`. -/
theorem g_special_constant_long (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hqa : 𝔼.Adapted q) (hq : GrowthBound γ q)
    (hω : |ωh| * γ < 1) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := g_weighted_inflation hG hret hqa hq hω t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.24), p. 68, in a growth economy: with constant expected returns and no
growth, `ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0} ρ^jΔE_{t+1}s̃_{t+1+j}`. -/
theorem g_identity_3_24 (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := g_identity_3_20 hG t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.25), p. 68, for a log bond price of growth `γ` with `|ω̂|γ < 1`: with
constant expected returns, `ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^jΔE_{t+1}π_{t+1+j}`. -/
theorem g_identity_3_25 {ωh : ℝ} {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hqa : 𝔼.Adapted q)
    (hγ : 0 ≤ γ) (hq : GrowthBound γ q) (hω : |ωh| * γ < 1)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  rw [g_bondReturn_innov hret hqa hγ hq hω t ω]
  congr 1
  refine tsum_congr fun j => ?_
  have e : rn (t + j + 2) = (rn (t + j + 2) - infl (t + j + 2)) + infl (t + j + 2) := by
    rw [sub_add_cancel]
  rw [e, map_add, innov_r_zero hc, zero_add]

/-- Cochrane (2023), (3.28), p. 69, in a growth economy with a log bond price of growth `γ`,
`|ω̂|γ < 1`: with no surplus news, constant expected returns and no growth,
`∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j} = 0`, hence
`ΔE_{t+1}π_{t+1} = −∑_{j≥1} ω̂^jΔE_{t+1}π_{t+1+j}`. -/
theorem g_monetary_disinflation (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hqa : 𝔼.Adapted q) (hq : GrowthBound γ q)
    (hω : |ωh| * γ < 1) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω)
    (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω = 0 ∧
      innov 𝔼 t (infl (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  have h := g_special_constant_long hG hret hqa hq hω hg hc t ω
  simp only [hs, mul_zero, tsum_zero, neg_zero] at h
  refine ⟨h, ?_⟩
  obtain ⟨K4, -, h4⟩ := hG.infl_growth
  have hPi0 := summable_innov_growth 𝔼 hG.gamma_nonneg hω h4 t 1 ω
  rw [hPi0.tsum_eq_zero_add] at h
  simp only [pow_zero, one_mul, add_zero] at h
  change innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω = 0
    at h
  linarith

/-- Cochrane (2023), §3.5.4, p. 71, in a growth economy: with perpetuities (`ω̂ = ρ`) and a log
bond price of growth `γ`, the discount-rate terms drop out of (3.22). -/
theorem g_perpetuity (hG : GrowthEconomy 𝔼 ρ v rn infl g sT γ) {q : ℕ → Ω → ℝ}
    (hret : BondRet ρ q rn) (hqa : 𝔼.Adapted q) (hq : GrowthBound γ q) (t : ℕ) (ω : Ω) :
    ∑' j, ρ ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        ∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω := by
  have h := g_weighted_inflation hG hret hqa hq hG.abs_rho_gamma t ω
  simp only [sub_self, zero_mul, tsum_zero, add_zero] at h
  exact h

/-! ### The boundary `γ = 1/ρ`: counterexamples on the coin-flip tree -/

namespace Boundary

open Cochrane.Generality.ExpectationsFiniteTree

/-- Cochrane (2023), p. 64 (counterexample): the first coin flip `±1`, revealed at date 1. -/
def cs1 : Bool × Bool → ℝ := coinShock 1

/-- Cochrane (2023), p. 64 (counterexample): `cs1 = ±1`, so it is nonzero and bounded by one. -/
theorem cs1_ne_zero (ω : Bool × Bool) : cs1 ω ≠ 0 ∧ |cs1 ω| ≤ 1 := by
  rcases ω with ⟨b1, b2⟩
  cases b1 <;> simp [cs1, coinShock]

/-- Cochrane (2023), p. 64 (counterexample): on the coin-flip tree, `E_t(a·cs1)` is `0` at date 0
(the flip is mean zero) and `a·cs1` from date 1 on (it is known). -/
theorem E_cs1 (a : ℝ) (t : ℕ) :
    coinSystem.E t (a • cs1) = if t = 0 then 0 else a • cs1 := by
  rw [map_smul]
  rcases t with _ | t
  · simp only [↓reduceIte]
    have h := coinShock_mean_zero 0
    simp only [zero_add] at h
    rw [cs1, h, smul_zero]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    congr 1
    funext ω
    rw [coinSystem, FiniteTree.toExpectationSystem_E]
    exact coinTree.condE_of_const_on_cell fun ω' h =>
      coinShock_measurable 1 (coinTree.refines (Nat.le_add_left 1 t) ω' ω h)

/-- Cochrane (2023), p. 64 (counterexample): a process `a_t·cs1` with `a_0 = 0` is adapted. -/
theorem adapted_smul (a : ℕ → ℝ) (ha : a 0 = 0) :
    coinSystem.Adapted fun t => a t • cs1 := by
  intro t
  rw [E_cs1]
  rcases t with _ | t
  · simp [ha]
  · simp

/-- Cochrane (2023), p. 64 (counterexample): the innovation at date 0 of `a·cs1` is `a·cs1`. -/
theorem innov_cs1 (a : ℝ) (ω : Bool × Bool) :
    innov coinSystem 0 (a • cs1) ω = a * cs1 ω := by
  rw [innov_apply, E_cs1, E_cs1]
  simp

/-- Cochrane (2023), p. 64 (counterexample): debt growing at exactly `ρ^{−t}`,
`v_t = ρ^{−t}·cs1` for `t ≥ 1`, `v_0 = 0` (a stochastic bubble). -/
noncomputable def vB (ρ : ℝ) : ℕ → Bool × Bool → ℝ :=
  fun t => (if t = 0 then 0 else ρ⁻¹ ^ t) • cs1

/-- Cochrane (2023), p. 64 (counterexample): the surpluses that make `vB` satisfy (3.17):
`s̃_1 = −cs1`, all others zero. -/
noncomputable def sB : ℕ → Bool × Bool → ℝ := fun t => (if t = 1 then (-1 : ℝ) else 0) • cs1

/-- Cochrane (2023), p. 64 (counterexample): the zero process (returns, inflation, growth). -/
def zB : ℕ → Bool × Bool → ℝ := fun _ _ => 0

/-- Cochrane (2023), (3.17), p. 63 (counterexample): the bubble economy satisfies the flow. -/
theorem flow_B {ρ : ℝ} (hρ : ρ ≠ 0) : Flow317 ρ (vB ρ) zB zB zB sB := by
  intro t ω
  simp only [vB, sB, zB, Pi.smul_apply, smul_eq_mul, sub_zero, add_zero]
  rcases t with _ | t
  · simp only [↓reduceIte, zero_add, pow_one, zero_mul, one_ne_zero]
    field_simp
    ring
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show t + 1 + 1 ≠ 1 by omega, zero_mul,
      sub_zero]
    rw [pow_succ]
    field_simp

/-- Cochrane (2023), p. 64 (counterexample): every process of the bubble economy is adapted. -/
theorem adapted_B (ρ : ℝ) :
    coinSystem.Adapted (vB ρ) ∧ coinSystem.Adapted sB ∧ coinSystem.Adapted zB := by
  refine ⟨adapted_smul _ (by simp), adapted_smul _ (by simp), fun t => ?_⟩
  change coinSystem.E t (fun _ => (0 : ℝ)) = fun _ => 0
  exact coinSystem.const t 0

/-- Cochrane (2023), p. 64 (counterexample): every process of the bubble economy grows at most at
rate `γ = ρ⁻¹`, the boundary `ργ = 1`. -/
theorem growth_B {ρ : ℝ} (hρ : 0 < ρ) :
    GrowthBound ρ⁻¹ (vB ρ) ∧ GrowthBound ρ⁻¹ sB ∧ GrowthBound ρ⁻¹ zB ∧ ρ * ρ⁻¹ = 1 := by
  refine ⟨⟨1, zero_le_one, fun n ω => ?_⟩, ⟨ρ, hρ.le, fun n ω => ?_⟩,
    ⟨0, le_rfl, fun n ω => by simp [zB]⟩, mul_inv_cancel₀ hρ.ne'⟩
  · simp only [vB, Pi.smul_apply, smul_eq_mul, abs_mul, one_mul]
    have h1 := (cs1_ne_zero ω).2
    have h2 : 0 ≤ ρ⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hρ.le) n
    split_ifs
    · rw [abs_zero, zero_mul]
      exact h2
    · rw [abs_of_nonneg h2]
      nlinarith [abs_nonneg (cs1 ω)]
  · simp only [sB, Pi.smul_apply, smul_eq_mul, abs_mul]
    have h1 := (cs1_ne_zero ω).2
    split_ifs with hn
    · subst hn
      rw [pow_one, mul_inv_cancel₀ hρ.ne', abs_neg, abs_one, one_mul]
      exact h1
    · rw [abs_zero, zero_mul]
      exact mul_nonneg hρ.le (pow_nonneg (inv_nonneg.mpr hρ.le) n)

/-- Cochrane (2023), (3.20), p. 65, and p. 64 (**the boundary `γ = 1/ρ` fails**): for every
`ρ > 0` the bubble economy on the coin-flip tree satisfies (3.17), all its processes are adapted
and grow at most at rate `ρ⁻¹` (so `ργ = 1`), yet at date 0 the unexpected-inflation identity
(3.20) fails in every state, and the present-value identity (3.19) fails at date 1 in every
state. -/
theorem boundary_3_20 {ρ : ℝ} (hρ : 0 < ρ) (ω : Bool × Bool) :
    ¬ (innov coinSystem 0 (zB (0 + 1)) ω - innov coinSystem 0 (zB (0 + 1)) ω =
      -(∑' j, ρ ^ j * innov coinSystem 0 (sB (0 + j + 1)) ω) -
        (∑' j, ρ ^ j * innov coinSystem 0 (zB (0 + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov coinSystem 0 (zB (0 + j + 2) - zB (0 + j + 2)) ω) ∧
      ¬ HasSum (fun j => ρ ^ j * coinSystem.E 1 (zp zB zB zB sB (1 + j + 1)) ω) (vB ρ 1 ω) := by
  have hz : ∀ (t : ℕ), innov coinSystem 0 (zB t) ω = 0 := fun t => by
    rw [innov_apply]
    change coinSystem.E 1 (fun _ => (0 : ℝ)) ω - coinSystem.E 0 (fun _ => (0 : ℝ)) ω = 0
    rw [coinSystem.const, coinSystem.const, sub_self]
  have hzz : ∀ t : ℕ, zB t - zB t = zB t := fun t => by funext; simp [zB]
  have hs : ∑' j, ρ ^ j * innov coinSystem 0 (sB (0 + j + 1)) ω = -cs1 ω := by
    rw [tsum_eq_single 0 fun j hj => by
      rw [sB, innov_cs1]
      simp [hj]]
    rw [sB, innov_cs1]
    simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [hz, hzz, mul_zero, tsum_zero, sub_zero, add_zero, sub_self, hs, neg_neg] at h
    exact (cs1_ne_zero ω).1 h.symm
  · have h0 : ∀ j : ℕ, ρ ^ j * coinSystem.E 1 (zp zB zB zB sB (1 + j + 1)) ω = 0 := by
      intro j
      have e : zp zB zB zB sB (1 + j + 1) = 0 := by
        funext ω'
        simp [zp, zB, sB]
      rw [e, map_zero, Pi.zero_apply, mul_zero]
    simp only [h0] at h
    have := h.unique hasSum_zero
    simp only [vB, Nat.one_ne_zero, ↓reduceIte, pow_one, Pi.smul_apply, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact (inv_ne_zero hρ.ne') h1
    · exact (cs1_ne_zero ω).1 h1

/-- Cochrane (2023), p. 64 ("If we use `ρ = 1` …"): at `ρ = 1` the bubble economy is a bounded
economy (all processes bounded by one) satisfying (3.17) with `ρ = 1`; by `boundary_3_20` (3.20)
fails in it, so with `ρ = 1` boundedness is not enough: the limit of `E_t v_{t+T}` must be the
same constant at `t` and `t + 1` (`identity_3_20_rho_one_mean`). -/
theorem rho_one_bounded :
    BoundedProc (vB 1) ∧ BoundedProc sB ∧ BoundedProc zB ∧ Flow317 1 (vB 1) zB zB zB sB := by
  have hb := growth_B (ρ := 1) one_pos
  have hc : ∀ {x : ℕ → Bool × Bool → ℝ}, GrowthBound (1 : ℝ)⁻¹ x → BoundedProc x := by
    intro x hx
    obtain ⟨K, -, hK⟩ := hx
    exact ⟨K, fun n ω => by simpa using hK n ω⟩
  exact ⟨hc hb.1, hc hb.2.1, hc hb.2.2.1, flow_B one_ne_zero⟩

/-- Cochrane (2023), A1 (1.24), p. 563 (counterexample): a log bond price growing at exactly
`|ω̂|^{−t}`, `q_t = ω̂^{−t}·cs1` for `t ≥ 1`, `q_0 = 0`. -/
noncomputable def qB (ωh : ℝ) : ℕ → Bool × Bool → ℝ :=
  fun t => (if t = 0 then 0 else ωh⁻¹ ^ t) • cs1

/-- Cochrane (2023), A1 (1.24) (counterexample): the bond returns of `qB`, `r^n_1 = cs1`, all
others zero. -/
noncomputable def rnB : ℕ → Bool × Bool → ℝ := fun t => (if t = 1 then (1 : ℝ) else 0) • cs1

/-- Cochrane (2023), (3.21), p. 65, and A1 (1.25) (**the boundary `γ = 1/|ω̂|` fails**): for
every `ω̂ ≠ 0`, the log bond price `qB ω̂` is adapted, grows at most at rate `|ω̂|⁻¹` (so
`|ω̂|γ = 1`) and satisfies the bond-return identity (1.24) with `rnB`, yet the bond-return
innovation identity (3.21) fails at date 0 in every state. -/
theorem boundary_3_21 {ωh : ℝ} (hω : ωh ≠ 0) :
    BondRet ωh (qB ωh) rnB ∧ coinSystem.Adapted (qB ωh) ∧ GrowthBound |ωh|⁻¹ (qB ωh) ∧
      |ωh| * |ωh|⁻¹ = 1 ∧ ∀ ω, innov coinSystem 0 (rnB (0 + 1)) ω ≠
        -∑' j, ωh ^ (j + 1) * innov coinSystem 0 (rnB (0 + j + 2)) ω := by
  refine ⟨fun t ω => ?_, adapted_smul _ (by simp), ⟨1, zero_le_one, fun n ω => ?_⟩,
    mul_inv_cancel₀ (abs_ne_zero.mpr hω), fun ω h => ?_⟩
  · simp only [qB, rnB, Pi.smul_apply, smul_eq_mul]
    rcases t with _ | t
    · simp only [zero_add, ↓reduceIte, pow_one, Nat.one_ne_zero]
      field_simp
      ring
    · simp only [show t + 1 + 1 ≠ 1 by omega, Nat.add_one_ne_zero, ↓reduceIte, zero_mul]
      rw [pow_succ]
      field_simp
      ring
  · simp only [qB, Pi.smul_apply, smul_eq_mul, abs_mul, one_mul]
    have h1 := (cs1_ne_zero ω).2
    have h2 : 0 ≤ |ωh|⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) n
    split_ifs
    · rw [abs_zero, zero_mul]
      exact h2
    · rw [abs_pow, abs_inv]
      nlinarith [abs_nonneg (cs1 ω)]
  · have h0 : ∀ j : ℕ, ωh ^ (j + 1) * innov coinSystem 0 (rnB (0 + j + 2)) ω = 0 := by
      intro j
      rw [rnB, innov_cs1]
      simp
    rw [tsum_congr h0, tsum_zero, neg_zero, rnB, innov_cs1] at h
    simp only [zero_add, ↓reduceIte, one_mul] at h
    exact (cs1_ne_zero ω).1 h

end Boundary

end Cochrane.Generality.TidyR6InnovGrowth
