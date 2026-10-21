/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.FullModel

/-!
# Optimal policy in the full new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5 "Optimal policy,
determinacy and selection" and §17.5.1 "Optimal policy", eqs. (17.22)–(17.28), pp. 417–420.

Policy is written in King's form (17.22), `i_t = i*_t + φ(π_t − π*_t)` (`KingRule`); in the
equilibrium `i = i*`, `π = π*` and `φ` drops out (`king_equilibrium`, `king_iff_standard`: the
same rule is `i_t = φ π_t + u_{i,t}` with the stochastic intercept `u_{i,t} = i*_t − φ π*_t`).
The starred model (17.23)–(17.24) (`Starred`) is the full model (`starred_iff_model`).

* (17.27): for `σ, κ ≠ 0`, `(i*, x*, π*)` solves the starred model iff
  `x* = (π* − β E π*' − u_π)/κ` and
  `i*_t = (1/σκ)[−β E_t π*_{t+2} + (1 + β + σκ) E_t π*_{t+1} − π*_t]
    + (1/σκ)[−E_t u_{π,t+1} + u_{π,t}] + u_{x,t}/σ` (`eq_17_27`). Hence **any** inflation
  path is attainable exactly, with bounded output and rate if everything is bounded
  (`any_pi_attainable`), and any output path is attainable (`any_x_attainable`).
* (17.25): zero inflation (`eq_17_25`). (17.26): zero output gap, with the unique bounded
  inflation `π* = E_t ∑ βʲ u_{π,t+j}` (`eq_17_26`, `E_forwardSeries_succ`).
* Survey error E9 (p. 418): with `x* = 0` the intercept is
  `i* − φπ* = (1 − φβ) E_t ∑ βʲ u_{π,t+1+j} − φ u_{π,t} + u_{x,t}/σ` (`e9_intercept`), not the
  printed `(1 − φ) E_t ∑ βʲ u_{π,t+1+j} + u_{x,t}/σ`; the two differ by
  `φ[(1 − β) E_t ∑ βʲ u_{π,t+1+j} − u_{π,t}]` (`e9_difference`), e.g. `−160/67` vs `−70/67` for
  an AR(1) cost-push shock with `ρ = 0.7`, `β = 0.95`, `φ = 1.5` (`e9_counterexample`).
* Woodford's loss `λ var(x) + (1 − λ) var(π)`: `x* = 0` and `π* = 0` are its corners
  (`loss_corner_x`, `loss_corner_pi`).
* (17.28): the rule with long-run target, natural rate and systematic responses is a rule with
  total inflation coefficient `θ_π + φ_π` (`rule_17_28_eq`).
* p. 419, "different values of φ without a time-varying intercept cannot fully stabilize
  inflation or output": zero inflation under `i_t = φ π_t + c` requires the IS shock to be
  `u_x = σc + (E_t u_{π,t+1} − u_{π,t})/κ`, whatever `φ` (`pi_zero_constant_intercept`), so with
  no IS shock and a non-constant geometric cost-push shock no `(φ, c)` works
  (`no_rule_stabilises_inflation`); zero output under a constant intercept forces `φ = ρ`,
  `c = 0` for an AR(1) cost-push shock (`x_zero_constant_intercept`), i.e. `φ < 1`, where
  the equilibrium is not determinate (`TaylorDeterminacy`).
-/

namespace Cochrane.KeynesianStickyPrices.OptimalPolicy

open Filter Topology FullModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### King's form of the rule and the starred model -/

/-- Cochrane (2023), eq. (17.22), p. 417: `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingRule (φ : ℝ) (i istar π πstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = istar t + φ • (π t - πstar t)

/-- Cochrane (2023), p. 418: King's rule is `i_t = φ π_t + u_{i,t}` with the stochastic
intercept (monetary-policy disturbance) `u_{i,t} = i*_t − φ π*_t`. -/
theorem king_iff_standard (φ : ℝ) (i istar π πstar : ℕ → Ω → ℝ) :
    KingRule φ i istar π πstar ↔ ∀ t, i t = φ • π t + (istar t - φ • πstar t) := by
  refine forall_congr' fun t => ?_
  rw [smul_sub]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), p. 417 ("we only observe `i_t = i*_t` and `π_t = π*_t`, so φ disappears
from equilibrium dynamics"): the starred paths satisfy King's rule for **every** `φ`. -/
theorem king_equilibrium (φ : ℝ) (istar πstar : ℕ → Ω → ℝ) :
    KingRule φ istar istar πstar πstar := fun t => by simp

/-- Cochrane (2023), eqs. (17.23)–(17.24), p. 417: the starred model
`x*_t = E_t x*_{t+1} − σ(i*_t − E_t π*_{t+1}) + u_{x,t}`,
`π*_t = β E_t π*_{t+1} + κ x*_t + u_{π,t}`. -/
def Starred (σ β κ : ℝ) (ux uπ i x π : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1))) + ux t) ∧
    ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + uπ t

/-- Cochrane (2023), eqs. (17.23)–(17.24): the starred model is (17.15)–(17.17) with the real
rate `r_t = i_t − E_t π_{t+1}`. -/
theorem starred_iff_model (σ β κ : ℝ) (ux uπ i x π : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x π ↔
      Model 𝔼 σ β κ ux uπ i (fun t => i t - 𝔼.E t (π (t + 1))) x π := by
  unfold Starred Model IS PC
  rw [fisher_iff]
  simp

/-- Cochrane (2023), eq. (17.27), p. 418: for `σ, κ ≠ 0`, `(i*, x*, π*)` solves the starred
model iff `x*_t = κ⁻¹(π*_t − β E_t π*_{t+1} − u_{π,t})` and
`i*_t = (σκ)⁻¹[−β E_t π*_{t+2} + (1 + β + σκ) E_t π*_{t+1} − π*_t]
  + (σκ)⁻¹[−E_t u_{π,t+1} + u_{π,t}] + σ⁻¹ u_{x,t}`. -/
theorem eq_17_27 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ i x π : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x π ↔
      (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)) ∧
      ∀ t, i t = (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) -
          π t) + (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) + σ⁻¹ • ux t := by
  rw [starred_iff_model, eq_17_18_shocks 𝔼 hκ]
  have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
  simp only [true_and]
  refine and_congr_right fun _ => forall_congr' fun t => ?_
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply,
      neg_mul] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply,
      neg_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), eq. (17.25), p. 417: zero inflation `π* = 0` is achieved iff
`x*_t = −u_{π,t}/κ` and `i*_t = (1/σκ)(−E_t u_{π,t+1} + u_{π,t}) + u_{x,t}/σ`. -/
theorem eq_17_25 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ i x : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x 0 ↔
      (∀ t, x t = -κ⁻¹ • uπ t) ∧
      ∀ t, i t = (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) + σ⁻¹ • ux t := by
  rw [eq_17_27 𝔼 hσ hκ]
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_sub, add_zero, sub_zero,
    zero_add, smul_neg, neg_smul]

/-- Cochrane (2023), eq. (17.26), p. 417: `E_t π*_{t+1} = E_t ∑_{j≥0} βʲ u_{π,t+1+j}` for the
forward series `π* = ∑ βʲ E_t u_{π,t+j}` (bounded `u_π`, `0 ≤ β < 1`). -/
theorem E_forwardSeries_succ {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries β u (t + 1)) ω = ∑' j, β ^ j * 𝔼.E t (u (t + 1 + j)) ω := by
  have hb : ∀ k ω', |β ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (17.26), p. 417: for `σ ≠ 0`, `0 ≤ β < 1` and bounded adapted `u_π`,
a zero output gap `x* = 0` with bounded inflation is achieved iff
`π*_t = E_t ∑ βʲ u_{π,t+j}` (the forward series) and
`i*_t = E_t π*_{t+1} + u_{x,t}/σ = E_t ∑ βʲ u_{π,t+1+j} + u_{x,t}/σ` (`E_forwardSeries_succ`). -/
theorem eq_17_26 {σ β κ M : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ux uπ i π : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |uπ t ω| ≤ M) (hua : 𝔼.Adapted uπ) (hπb : BoundedProc π) :
    Starred 𝔼 σ β κ ux uπ i 0 π ↔
      π = 𝔼.forwardSeries β uπ ∧
      i = fun t => 𝔼.E t (𝔼.forwardSeries β uπ (t + 1)) + σ⁻¹ • ux t := by
  constructor
  · rintro ⟨his, hpc⟩
    have hπ : π = 𝔼.forwardSeries β uπ :=
      𝔼.eq_forwardSeries hβ0 hβ1 hu hua (fun t => by simpa using hpc t) hπb
    refine ⟨hπ, funext fun t => funext fun ω => ?_⟩
    have e := congrFun (his t) ω
    rw [← hπ]
    simp only [Pi.zero_apply, map_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    field_simp
    linear_combination e
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω
      simp only [Pi.zero_apply, map_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      field_simp
      ring
    · rw [𝔼.forwardSeries_solves hβ0 hβ1 hu hua t]
      simp

/-- Survey error E9, Cochrane (2023), p. 418 (corrected): with `x* = 0` the
intercept/disturbance is
`i*_t − φ π*_t = (1 − φβ) E_t ∑ βʲ u_{π,t+1+j} − φ u_{π,t} + u_{x,t}/σ`. -/
theorem e9_intercept {σ β κ M φ : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ux uπ i π : ℕ → Ω → ℝ} (hu : ∀ t ω, |uπ t ω| ≤ M) (hua : 𝔼.Adapted uπ)
    (hπb : BoundedProc π) (h : Starred 𝔼 σ β κ ux uπ i 0 π) (t : ℕ) (ω : Ω) :
    i t ω - φ * π t ω =
      (1 - φ * β) * ∑' j, β ^ j * 𝔼.E t (uπ (t + 1 + j)) ω - φ * uπ t ω + σ⁻¹ * ux t ω := by
  obtain ⟨hπ, hi⟩ := (eq_17_26 𝔼 hσ hβ0 hβ1 hu hua hπb).mp h
  have hs := congrFun (𝔼.forwardSeries_solves hβ0 hβ1 hu hua t) ω
  rw [hi, hπ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs ⊢
  rw [hs, E_forwardSeries_succ 𝔼 hβ0 hβ1 hu t ω]
  ring

/-- Survey error E9, Cochrane (2023), p. 418: the correct intercept minus the printed one,
`(1 − φβ) S − φ u + u_x/σ − [(1 − φ) S + u_x/σ] = φ[(1 − β) S − u]`; it vanishes (for
`φ ≠ 0`) only if `(1 − β) E_t ∑ βʲ u_{π,t+1+j} = u_{π,t}`. -/
theorem e9_difference (φ β S u uxσ : ℝ) :
    ((1 - φ * β) * S - φ * u + uxσ) - ((1 - φ) * S + uxσ) = φ * ((1 - β) * S - u) := by ring

/-- Survey error E9, Cochrane (2023), p. 418, counterexample: perfect foresight,
`u_{π,t} = 0.7ᵗ`, `u_x = 0`, `β = 0.95`, `φ = 1.5`. Then `S_0 = ∑ βʲ u_{π,1+j} = 140/67`, the
correct intercept `(1 − φβ) S_0 − φ u_{π,0} = −160/67 ≈ −2.388` (`e9_intercept`), the printed
`(1 − φ) S_0 = −70/67 ≈ −1.045`. -/
theorem e9_counterexample :
    ∑' j : ℕ, (19 / 20 : ℝ) ^ j * (7 / 10) ^ (1 + j) = 140 / 67 ∧
      (1 - 3 / 2 * (19 / 20 : ℝ)) * (140 / 67) - 3 / 2 * (7 / 10) ^ 0 = -160 / 67 ∧
      (1 - 3 / 2 : ℝ) * (140 / 67) = -70 / 67 ∧ (-160 / 67 : ℝ) ≠ -70 / 67 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  have h : ∀ j : ℕ, (19 / 20 : ℝ) ^ j * (7 / 10) ^ (1 + j) = 7 / 10 * (133 / 200) ^ j := by
    intro j
    rw [pow_add, pow_one, show (133 / 200 : ℝ) = 19 / 20 * (7 / 10) by norm_num, mul_pow]
    ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-! ### Any path is attainable -/

/-- A bounded process stays bounded under `E_t` applied to a shifted date. -/
theorem boundedProc_E {y : ℕ → Ω → ℝ} (hy : BoundedProc y) (k : ℕ) :
    BoundedProc fun t => 𝔼.E t (y (t + k)) := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨M, fun t ω => 𝔼.abs_E_le (hM (t + k)) t ω⟩

/-- Sums and scalar multiples of bounded processes are bounded. -/
theorem boundedProc_add_smul {y z : ℕ → Ω → ℝ} (hy : BoundedProc y) (hz : BoundedProc z)
    (a b : ℝ) : BoundedProc fun t => a • y t + b • z t := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨N, hN⟩ := hz
  refine ⟨|a| * M + |b| * N, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t ω) (abs_nonneg b)

/-- Cochrane (2023), p. 418 ("monetary policy in this model can still attain … any given
inflation path … exactly"; "the interest-rate policy `i*_t` that generates any desired
inflation path"): for `σ, κ ≠ 0` and **any** target `π*`, the output gap and the rate given by
(17.27) solve the starred model; if `π*`, `u_π`, `u_x` are bounded so are `x*` and `i*`. -/
theorem any_pi_attainable {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ π : ℕ → Ω → ℝ) :
    let x := fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)
    let i := fun t => (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) +
      (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) - π t) + (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) +
      σ⁻¹ • ux t
    Starred 𝔼 σ β κ ux uπ i x π ∧
      (BoundedProc π → BoundedProc uπ → BoundedProc ux → BoundedProc x ∧ BoundedProc i) := by
  intro x i
  refine ⟨(eq_17_27 𝔼 hσ hκ ux uπ i x π).mpr ⟨fun t => rfl, fun t => rfl⟩, ?_⟩
  intro hπ hu hx
  have e1 := boundedProc_E 𝔼 hπ 1
  have e2 := boundedProc_E 𝔼 hπ 2
  have e0 := boundedProc_E 𝔼 hu 1
  have hneg : ∀ {y : ℕ → Ω → ℝ}, BoundedProc y → BoundedProc fun t => -y t := by
    intro y ⟨M, hM⟩
    exact ⟨M, fun t ω => by simpa using hM t ω⟩
  refine ⟨?_, ?_⟩
  · have h := boundedProc_add_smul (boundedProc_add_smul hπ e1 1 (-β)) hu 1 (-1)
    obtain ⟨M, hM⟩ := boundedProc_add_smul h h κ⁻¹ 0
    refine ⟨M, fun t ω => ?_⟩
    have := hM t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, one_mul,
      neg_one_mul] at this
    simp only [x, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    convert this using 2
    ring
  · have a1 := boundedProc_add_smul (boundedProc_add_smul e2 e1 (-β) (1 + β + σ * κ)) hπ 1 (-1)
    have a2 := boundedProc_add_smul (hneg e0) hu 1 1
    have a3 := boundedProc_add_smul (boundedProc_add_smul a1 a2 (σ * κ)⁻¹ (σ * κ)⁻¹) hx 1 σ⁻¹
    obtain ⟨M, hM⟩ := a3
    refine ⟨M, fun t ω => ?_⟩
    have := hM t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, one_mul,
      neg_one_mul] at this
    simp only [i, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul,
      neg_mul]
    convert this using 2
    ring

/-- Cochrane (2023), p. 418 ("… or any given output path exactly"): for `0 ≤ β < 1`, `σ ≠ 0`
and bounded adapted target output `x*` and cost-push shock `u_π`, inflation
`π* = ∑ βʲ E_t(κ x*_{t+j} + u_{π,t+j})` and
`i*_t = E_t π*_{t+1} + (E_t x*_{t+1} − x*_t + u_{x,t})/σ` solve the starred model, with `π*`
bounded. -/
theorem any_x_attainable {σ β κ M : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ux uπ x : ℕ → Ω → ℝ} (hb : ∀ t ω, |κ * x t ω + uπ t ω| ≤ M)
    (ha : 𝔼.Adapted fun t => κ • x t + uπ t) :
    let π := 𝔼.forwardSeries β fun t => κ • x t + uπ t
    let i := fun t => 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t + ux t)
    Starred 𝔼 σ β κ ux uπ i x π ∧ BoundedProc π := by
  intro π i
  have hb' : ∀ t ω, |(fun t => κ • x t + uπ t) t ω| ≤ M := fun t ω => by simpa using hb t ω
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, 𝔼.forwardSeries_bounded hβ0 hβ1 hb'⟩
  · funext ω
    simp only [i, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · change 𝔼.forwardSeries β (fun t => κ • x t + uπ t) t =
      β • 𝔼.E t (𝔼.forwardSeries β (fun t => κ • x t + uπ t) (t + 1)) + κ • x t + uπ t
    rw [𝔼.forwardSeries_solves hβ0 hβ1 hb' ha t]
    abel

/-! ### Woodford's loss and the rule (17.28) -/

/-- Cochrane (2023), p. 418: Woodford's loss `λ V(x) + (1 − λ) V(π)` for a variance-like
functional `V`. -/
def woodfordLoss (V : (ℕ → Ω → ℝ) → ℝ) (lam : ℝ) (x π : ℕ → Ω → ℝ) : ℝ :=
  lam * V x + (1 - lam) * V π

/-- Cochrane (2023), p. 418 ("the choices `x* = 0` and `π* = 0` are simple examples of such
policies"): for `V ≥ 0` with `V 0 = 0`, `x* = 0` minimises the loss with `λ = 1`. -/
theorem loss_corner_x (V : (ℕ → Ω → ℝ) → ℝ) (hV : ∀ y, 0 ≤ V y) (hV0 : V 0 = 0)
    (π x' π' : ℕ → Ω → ℝ) : woodfordLoss V 1 0 π ≤ woodfordLoss V 1 x' π' := by
  unfold woodfordLoss
  rw [hV0]
  linarith [hV x']

/-- Cochrane (2023), p. 418: `π* = 0` minimises the loss with `λ = 0`. -/
theorem loss_corner_pi (V : (ℕ → Ω → ℝ) → ℝ) (hV : ∀ y, 0 ≤ V y) (hV0 : V 0 = 0)
    (x x' π' : ℕ → Ω → ℝ) : woodfordLoss V 0 x 0 ≤ woodfordLoss V 0 x' π' := by
  unfold woodfordLoss
  rw [hV0]
  linarith [hV π']

/-- Cochrane (2023), eq. (17.28), p. 419:
`i_t = r*_t + π^T + θ_π π_t + θ_x x_t + φ_π (π_t − π^T) + u_{i,t}`. -/
def Rule1728 (θπ θx φπ πT : ℝ) (rstar u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rstar t + (fun _ => πT) + θπ • π t + θx • x t + φπ • (π t - fun _ => πT) + u t

/-- Cochrane (2023), eq. (17.28), p. 419: the rule responds to inflation with total coefficient
`θ_π + φ_π`, with intercept `r*_t + (1 − φ_π) π^T + u_{i,t}`. -/
theorem rule_17_28_eq {θπ θx φπ πT : ℝ} {rstar u i x π : ℕ → Ω → ℝ} :
    Rule1728 θπ θx φπ πT rstar u i x π ↔
      ∀ t, i t = (θπ + φπ) • π t + θx • x t + (rstar t + (fun _ => (1 - φπ) * πT) + u t) := by
  refine forall_congr' fun t => ?_
  have : ∀ a b : Ω → ℝ, a = b ↔ ∀ ω, a ω = b ω := fun a b => funext_iff
  rw [this, this]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> rw [h] <;> ring

/-! ### A constant intercept cannot fully stabilise -/

/-- Cochrane (2023), p. 419 ("different values of φ without a time-varying intercept cannot
fully stabilize inflation"): zero inflation is an equilibrium under `i_t = φ π_t + c` (constant
`c`) only if the IS disturbance is exactly `u_{x,t} = σc + (E_t u_{π,t+1} − u_{π,t})/κ` —
a condition that does not involve `φ`. -/
theorem pi_zero_constant_intercept {σ β κ φ c : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {ux uπ i x : ℕ → Ω → ℝ} (h : Starred 𝔼 σ β κ ux uπ i x 0)
    (hrule : ∀ t, i t = φ • (0 : ℕ → Ω → ℝ) t + fun _ => c) (t : ℕ) :
    ux t = (fun _ => σ * c) + κ⁻¹ • (𝔼.E t (uπ (t + 1)) - uπ t) := by
  obtain ⟨-, hi⟩ := (eq_17_25 𝔼 hσ hκ ux uπ i x).mp h
  have e := hi t
  rw [hrule t] at e
  funext ω
  have e' := congrFun e ω
  simp only [Pi.zero_apply, smul_zero, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply, Pi.sub_apply] at e' ⊢
  rw [e']
  field_simp
  ring

/-- Cochrane (2023), p. 419: with no IS disturbance and a geometric cost-push shock
`u_{π,t} = ρᵗ u₀` (`ρ ≠ 1`, `u₀ ≠ 0`), no rule `i_t = φ π_t + c` with a constant intercept has
zero inflation as an equilibrium, whatever `φ` and `c` (perfect foresight). -/
theorem no_rule_stabilises_inflation {σ β κ ρ u0 : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hρ : ρ ≠ 1)
    (hu0 : u0 ≠ 0) (φ c : ℝ) (i x : ℕ → Unit → ℝ) :
    ¬ (Starred perfectForesight σ β κ 0 (fun t _ => ρ ^ t * u0) i x 0 ∧
      ∀ t, i t = φ • (0 : ℕ → Unit → ℝ) t + fun _ => c) := by
  rintro ⟨h, hrule⟩
  have e0 := congrFun (pi_zero_constant_intercept perfectForesight hσ hκ h hrule 0) ()
  have e1 := congrFun (pi_zero_constant_intercept perfectForesight hσ hκ h hrule 1) ()
  simp only [perfectForesight, LinearMap.id_apply, Pi.zero_apply, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, pow_zero, pow_one, zero_add] at e0 e1
  have key : κ⁻¹ * ((ρ - 1) ^ 2 * u0) = 0 := by linear_combination e0 - e1
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hκ (inv_eq_zero.mp h1)
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hρ (by nlinarith [pow_eq_zero_iff (n := 2) (a := ρ - 1) two_ne_zero |>.mp h2])
    · exact hu0 h2

/-- Cochrane (2023), p. 419 ("… or output"; perfect foresight): with no IS disturbance and an
AR(1) cost-push shock `u_{π,t} = ρᵗ u₀` (`|ρ| < 1`, `u₀ ≠ 0`, `0 ≤ β < 1`), if a zero output
gap with bounded inflation is an equilibrium under a rule `i_t = φ π_t + c` with constant
intercept, then `φ = ρ` and `c = 0`: the coefficient is pinned to the shock persistence, below
one — where the three-equation model is indeterminate (`TaylorDeterminacy`). -/
theorem x_zero_constant_intercept {β ρ u0 φ c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    (hu0 : u0 ≠ 0) {i π : ℕ → ℝ} (hpc : ∀ t, π t = β * π (t + 1) + ρ ^ t * u0)
    (hb : BoundedS π) (his : ∀ t, i t = π (t + 1)) (hrule : ∀ t, i t = φ * π t + c) :
    φ = ρ ∧ c = 0 := by
  have hβρ : β * ρ < 1 := by
    have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0
    have h2 : β * |ρ| < 1 := by nlinarith [abs_nonneg ρ]
    linarith
  have hK : 1 - β * ρ ≠ 0 := by linarith
  set K := u0 / (1 - β * ρ) with hKdef
  have hK0 : K ≠ 0 := div_ne_zero hu0 hK
  -- inflation is `K ρᵗ`
  have hd := homog_zero (q := β) (by rw [abs_of_nonneg hβ0]; exact hβ1)
    (d := fun t => π t - K * ρ ^ t) (fun t => by
      rw [hpc t, hKdef, pow_succ]
      field_simp
      ring)
    (by
      obtain ⟨M, hM⟩ := hb
      refine ⟨M + |K|, fun t => (abs_sub _ _).trans (add_le_add (hM t) ?_)⟩
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg K) (pow_le_one₀ (abs_nonneg ρ) hρ.le))
  have hπ : ∀ t, π t = K * ρ ^ t := fun t => by
    have := congrFun hd t
    simp only [Pi.zero_apply] at this
    linarith
  have e0 := hrule 0
  have e1 := hrule 1
  rw [his, hπ, hπ] at e0 e1
  simp only [pow_zero, pow_one, mul_one, zero_add] at e0 e1
  have hρ1 : ρ - 1 ≠ 0 := by
    intro h
    have : ρ = 1 := by linarith
    rw [this, abs_one] at hρ
    exact lt_irrefl _ hρ
  have key : K * (ρ - 1) * (ρ - φ) = 0 := by linear_combination e1 - e0 - ρ * e0 + ρ * e0
  have hφ : φ = ρ := by
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hK0
      · exact absurd h' hρ1
    · linarith
  refine ⟨hφ, ?_⟩
  rw [hφ] at e0
  linarith

end Cochrane.KeynesianStickyPrices.OptimalPolicy
