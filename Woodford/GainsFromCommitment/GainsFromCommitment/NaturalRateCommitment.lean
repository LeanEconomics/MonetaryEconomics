/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ImpulseResponses
import GainsFromCommitment.DateZeroCommitment

/-!
# Optimal commitment and fluctuations in the natural rate of interest

Woodford (2003), *Interest and Prices*, Chapter 7, §2.2, pp. 501–507.

With the loss (1.2) (no interest-rate term), natural-rate disturbances can be completely
neutralised: zero inflation and a zero output gap are feasible (the interest rate tracks `rⁿ`)
and optimal, under commitment and under discretion. With an interest-rate stabilisation term
(2.24), and in the limiting case `κ = 0` (inflation identically zero), the first-order conditions
(1.17)–(1.18) reduce to the condition on p. 506, and combined with the IS relation (2.23) to the
second-order expectational difference equation (2.28), whose unique bounded solution is
the partial-adjustment rule (2.29) towards the desired rate (2.30).

Dates: Lean date `0` is the economic date `t₀ − 1` (the lagged interest rate `i_{t₀−1}` and the
initial multiplier), Lean date `t + 1` is the economic date `t₀ + t`.

## Main results

* `zero_gap_feasible`, `IS_never_binds`, `zero_gap_optimal`, `zero_gap_unique_pf`,
  `discretion_zero` (p. 501): with loss (1.2) and `x* = 0`, `π = x = 0`, `i = rⁿ` is attainable
  and optimal, uniquely under perfect foresight, and also the discretionary outcome.
* `periodLoss` (2.24), `InitialT0` (2.25), `TimelessConstraint` (2.26).
* `foc_kappa0` (p. 506): (1.17)–(1.18) with `κ = 0` give
  `σλₓ(x_t − x*) − λᵢ[(i_t − i*) − β⁻¹(i_{t−1} − i*)] = 0`; `foc_IS_iff_228`: with this
  condition, the IS relation (2.23) is equivalent to (2.28).
* `shiftSys_E`, `workhorse_iff`, `workhorse_existsUnique` (the second-order workhorse of survey
  §4.3, `βE_t y_{t+1} − (1 + β + c)y_t + y_{t−1} = f_t`, from Lean date 1, through the shared
  shifted system `SecondOrderRE.shiftSys 𝔼 1`). The AS relation without cost-push shocks is the
  shared `DateZeroCommitment.AS`; the roots are the shared `SecondOrderRE.mu1`, `mu2`.
* `charEq_roots` (p. 506): `μ² − (1 + β⁻¹ + λₓσ²/λᵢ)μ + β⁻¹ = 0` has roots `0 < μ₁ < 1 < μ₂`.
* `eq228_iff_229`, `eq228_existsUnique` ((2.29)–(2.30)); `ibar_weights` (positive weights summing
  to one); survey error E8 confirmed: `printed_230_weights` (the printed `(1 − μ₂)` weights sum to
  `−μ₂`) and `not_printed_230` (the printed rule does not solve (2.28)).
* `mu1_strictAnti`, `mu1_strictMono` (p. 506): `μ₁` is increasing in `λᵢ/(λₓσ²)`.
* `ibar_ar1`, `slope_pos_lt_one`, `slope_strictMono`, `slope_tendsto_one` (p. 506): for an AR(1)
  natural rate (2.27), `ī_t = r̄ + s(rⁿ_t − r̄)` with `0 < s < 1`, `s` increasing in `ρ` and
  `s → 1` as `ρ → 1`.
* `sufficiency_kappa0`, `optimal_plan_kappa0`, `optimal_plan_kappa0_t0` (p. 506, footnote 26):
  Lagrangian sufficiency — the plan (2.29) with the output gap from the first-order condition
  minimises the expected discounted loss (2.24) (with `κ = 0`) among all bounded adapted plans
  satisfying (2.23) and the timeless constraint `x_{t₀} = x̄_{t₀}` (2.26) (or, for the
  `t₀`-optimal plan, with initial multiplier (2.25)).
-/

namespace Woodford.GainsFromCommitment.NaturalRateCommitment

open Filter Topology ImpulseResponses
open SecondOrderRE (mu1 mu2 shiftSys)
open DateZeroCommitment (AS)
open Sequences (tsum_telescope_inv)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Page 501: with loss (1.2), natural-rate shocks are completely neutralised -/

/-- Woodford (2003), eq. (2.23), p. 502: the intertemporal IS relation
`x_t = E_t x_{t+1} − σ(i_t − E_t π_{t+1} − rⁿ_t)` at every date. -/
def IS (σ : ℝ) (rn π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1)) - rn t)

/-- Woodford (2003), p. 501: zero inflation and a zero output gap, with the nominal rate equal to
the natural rate, satisfy (2.1) (without cost-push shocks) and (2.23) for every natural-rate
process. -/
theorem zero_gap_feasible (β κ σ : ℝ) (rn : ℕ → Ω → ℝ) :
    AS 𝔼 β κ 0 0 ∧ IS 𝔼 σ rn 0 0 rn := by
  refine ⟨fun t => by simp, fun t => by simp⟩

/-- Woodford (2003), p. 501 and §1.2 ("one may omit the constraint terms corresponding to the IS
relation, as these constraints never bind"): for `σ ≠ 0`, any paths of inflation and the output
gap are consistent with (2.23) for exactly one interest-rate path,
`i_t = rⁿ_t + E_tπ_{t+1} + σ⁻¹(E_t x_{t+1} − x_t)`. -/
theorem IS_never_binds {σ : ℝ} (hσ : σ ≠ 0) (rn π x : ℕ → Ω → ℝ) :
    ∃! i : ℕ → Ω → ℝ, IS 𝔼 σ rn π x i := by
  refine ⟨fun t => rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t), fun t => ?_,
    fun i hi => funext fun t => ?_⟩
  · funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have h := congrFun (hi t)
    funext ω
    have h1 := h ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    field_simp
    linear_combination h1

/-- Woodford (2003), p. 501: with `x* = 0` and `λ ≥ 0` the expected discounted loss (1.2) of any
bounded plan is nonnegative, and the zero plan attains `0`: complete stabilisation is optimal
(under commitment, and equally under discretion). -/
theorem zero_gap_optimal {β lam : ℝ} (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam) (π x : ℕ → Ω → ℝ) (s : ℕ)
    (ω : Ω) :
    𝔼.E s (fun ω' => ∑' k, β ^ k * ((0 : ℕ → Ω → ℝ) (s + k) ω' ^ 2 +
        lam * (0 : ℕ → Ω → ℝ) (s + k) ω' ^ 2)) ω = 0 ∧
      0 ≤ 𝔼.E s (fun ω' => ∑' k, β ^ k * (π (s + k) ω' ^ 2 + lam * x (s + k) ω' ^ 2)) ω := by
  constructor
  · simp only [Pi.zero_apply]
    simp [𝔼.const]
  · have hnn : (0 : Ω → ℝ) ≤ fun ω' => ∑' k, β ^ k * (π (s + k) ω' ^ 2 + lam * x (s + k) ω' ^ 2) :=
      fun ω' => tsum_nonneg fun k => mul_nonneg (pow_nonneg hβ0 k)
        (add_nonneg (sq_nonneg _) (mul_nonneg hlam (sq_nonneg _)))
    have := 𝔼.mono s hnn ω
    rwa [map_zero] at this

/-- Woodford (2003), p. 501 (uniqueness under perfect foresight): with `β > 0`, `λ > 0`, a
deterministic plan whose (summable) discounted loss is zero has `π = x = 0` at every date. -/
theorem zero_gap_unique_pf {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) {π x : ℕ → ℝ}
    (hs : Summable (fun k => β ^ k * (π k ^ 2 + lam * x k ^ 2)))
    (h0 : ∑' k, β ^ k * (π k ^ 2 + lam * x k ^ 2) = 0) : ∀ k, π k = 0 ∧ x k = 0 := by
  have hnn : ∀ k, 0 ≤ β ^ k * (π k ^ 2 + lam * x k ^ 2) := fun k =>
    mul_nonneg (pow_nonneg hβ.le k) (add_nonneg (sq_nonneg _) (mul_nonneg hlam.le (sq_nonneg _)))
  have hz := (hasSum_zero_iff_of_nonneg hnn).mp (h0 ▸ hs.hasSum)
  intro k
  have hk := congrFun hz k
  simp only [Pi.zero_apply] at hk
  have hk' : π k ^ 2 + lam * x k ^ 2 = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd h (pow_ne_zero k hβ.ne')
    · exact h
  have h1 : π k ^ 2 = 0 := by nlinarith [sq_nonneg (π k), sq_nonneg (x k)]
  have h2 : lam * x k ^ 2 = 0 := by linarith
  refine ⟨pow_eq_zero_iff (two_ne_zero) |>.mp h1, ?_⟩
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hlam.ne'
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h

/-- Woodford (2003), p. 501 (footnote 16 and the discretion case): a discretionary optimiser
that expects zero future inflation chooses, among pairs on the AS line `π = κx`, the unique
minimiser `(0, 0)` of `π² + λx²` (`λ > 0`). -/
theorem discretion_zero {κ lam : ℝ} (hlam : 0 < lam) (π x : ℝ) (h : π = κ * x) :
    (0 : ℝ) ^ 2 + lam * 0 ^ 2 ≤ π ^ 2 + lam * x ^ 2 ∧
      (π ^ 2 + lam * x ^ 2 = 0 ^ 2 + lam * 0 ^ 2 → π = 0 ∧ x = 0) := by
  refine ⟨by nlinarith [sq_nonneg π, sq_nonneg x], fun h0 => ?_⟩
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg π, sq_nonneg x]
  have hx0 : x = 0 := pow_eq_zero_iff two_ne_zero |>.mp hx
  exact ⟨by rw [h, hx0, mul_zero], hx0⟩

/-! ### The problem with interest-rate stabilisation: (2.24)–(2.26) and the `κ = 0` FOC -/

/-- Woodford (2003), eq. (2.24), p. 503: the period loss `π² + λₓ(x − x*)² + λᵢ(i − i*)²`. -/
def periodLoss (lamx lami xs is π x i : ℝ) : ℝ :=
  π ^ 2 + lamx * (x - xs) ^ 2 + lami * (i - is) ^ 2

/-- Woodford (2003), eq. (2.25), p. 503: the initial conditions of the `t₀`-optimal commitment,
`φ_{1,t₀−1} = φ_{2,t₀−1} = 0`. -/
def InitialT0 (φ1 φ2 : ℕ → Ω → ℝ) : Prop := φ1 0 = 0 ∧ φ2 0 = 0

/-- Woodford (2003), eq. (2.26), p. 503: the timeless initial constraints
`π_{t₀} = π̄_{t₀}`, `x_{t₀} = x̄_{t₀}` (state-contingent values known at `t₀`). -/
def TimelessConstraint (π x : ℕ → Ω → ℝ) (pibar xbar : Ω → ℝ) : Prop :=
  π 1 = pibar ∧ x 1 = xbar

/-- Woodford (2003), p. 506: with `κ = 0` the first-order conditions (1.17)
`λₓ(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1} = 0` and (1.18) `λᵢ(i_t − i*) + σφ_{1t} = 0`
(for `t ≥ t₀`, and (1.18) also at `t₀ − 1`, footnote 26) imply
`σλₓ(x_t − x*) − λᵢ[(i_t − i*) − β⁻¹(i_{t−1} − i*)] = 0` for `t ≥ t₀`. -/
theorem foc_kappa0 {β σ lamx lami xs is : ℝ} {x i φ : ℕ → Ω → ℝ}
    (h117 : ∀ t, lamx • (x (t + 1) - fun _ => xs) + φ (t + 1) - β⁻¹ • φ t = 0)
    (h118 : ∀ t, lami • (i t - fun _ => is) + σ • φ t = 0) (t : ℕ) :
    (σ * lamx) • (x (t + 1) - fun _ => xs) -
      lami • ((i (t + 1) - fun _ => is) - β⁻¹ • (i t - fun _ => is)) = 0 := by
  funext ω
  have h1 := congrFun (h117 t) ω
  have h2 := congrFun (h118 (t + 1)) ω
  have h3 := congrFun (h118 t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 h3 ⊢
  linear_combination σ * h1 - h2 + β⁻¹ * h3

/-- Woodford (2003), eq. (2.28), p. 506: `i_t − β⁻¹i_{t−1} = E_t[i_{t+1} − β⁻¹i_t] −
λᵢ⁻¹λₓσ²(i_t − rⁿ_t)` for `t ≥ t₀` (here `c = λₓσ²/λᵢ`). -/
def Eq228 (β c : ℝ) (rn i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) - β⁻¹ • i t =
    𝔼.E (t + 1) (i (t + 2) - β⁻¹ • i (t + 1)) - c • (i (t + 1) - rn (t + 1))

/-- Woodford (2003), p. 506 (footnote 27, `κ = 0` and zero inflation): when the output gap is
given by the first-order condition of p. 506,
`x_t = x* + (λᵢ/(σλₓ))[(i_t − i*) − β⁻¹(i_{t−1} − i*)]`, the IS relation (2.23) holds at every
`t ≥ t₀` iff (2.28) does (`c = λₓσ²/λᵢ`). -/
theorem foc_IS_iff_228 {β σ lamx lami xs is : ℝ} (hσ : σ ≠ 0) (hlx : lamx ≠ 0)
    (hli : lami ≠ 0) {rn x i : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i)
    (hx : ∀ t, x (t + 1) = (fun _ => xs) +
      (lami / (σ * lamx)) • ((i (t + 1) - fun _ => is) - β⁻¹ • (i t - fun _ => is))) :
    (∀ t, x (t + 1) = 𝔼.E (t + 1) (x (t + 2)) - σ • (i (t + 1) - rn (t + 1))) ↔
      Eq228 𝔼 β (lamx * σ ^ 2 / lami) rn i := by
  refine forall_congr' fun t => ?_
  have hEx : 𝔼.E (t + 1) (x (t + 2)) = (fun _ => xs) + (lami / (σ * lamx)) •
      ((𝔼.E (t + 1) (i (t + 2)) - fun _ => is) - β⁻¹ • (i (t + 1) - fun _ => is)) := by
    rw [show t + 2 = t + 1 + 1 by ring, hx (t + 1)]
    simp only [map_add, map_sub, map_smul, 𝔼.const, hia (t + 1)]
  rw [hEx, hx t, map_sub, map_smul, hia (t + 1), funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-! ### The second-order workhorse (survey §4.3) -/

/-- Woodford (2003), survey §4.3: in the shifted system `E'_t = E_{1+t}` (the shared
`SecondOrderRE.shiftSys` with `s = 1`), `E'_t = E_{t+1}`, so a variable known at `t + 1` is
"adapted" for `E'`. -/
theorem shiftSys_E (t : ℕ) (x : Ω → ℝ) : (shiftSys 𝔼 1).E t x = 𝔼.E (t + 1) x := by
  rw [SecondOrderRE.shiftSys_E, add_comm]

/-- Woodford (2003), survey §4.3: forward series under the shifted system,
`∑_k aᵏ E_{t+1} f_{t+1+k}`. -/
theorem shift_forwardSeries (a : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) :
    (shiftSys 𝔼 1).forwardSeries a (fun n => f (n + 1)) t = 𝔼.forwardSeries a f (t + 1) := by
  funext ω
  unfold ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  simp only [shiftSys_E]
  rw [show t + 1 + k = t + k + 1 by ring]

/-- Woodford (2003), (2.30), p. 506: forward series are linear in the forcing,
`∑ aᵏ E_t(b f_{t+k}) = b ∑ aᵏ E_t f_{t+k}`. -/
theorem forwardSeries_smul (a b : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.forwardSeries a (fun n => b • f n) t = b • 𝔼.forwardSeries a f t := by
  funext ω
  unfold ExpectationSystem.forwardSeries
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-- Woodford (2003), (2.29), p. 506: a stable recursion `y_{t+1} = μ₁y_t + g_{t+1}` with bounded
forcing and bounded initial value stays bounded. -/
theorem rec_bounded {μ1 B0 Mg : ℝ} (hμ1 : |μ1| < 1) {y g : ℕ → Ω → ℝ}
    (hrec : ∀ t, y (t + 1) = μ1 • y t + g (t + 1)) (hy0 : ∀ ω, |y 0 ω| ≤ B0)
    (hg : ∀ t ω, |g t ω| ≤ Mg) : BoundedProc y := by
  have hpos : 0 < 1 - |μ1| := by linarith
  set K := max B0 (Mg / (1 - |μ1|)) with hK
  have hMK : Mg ≤ (1 - |μ1|) * K := by
    have : Mg / (1 - |μ1|) ≤ K := le_max_right _ _
    rw [div_le_iff₀ hpos] at this
    linarith
  refine ⟨K, fun t ω => ?_⟩
  induction t with
  | zero => exact (hy0 ω).trans (le_max_left _ _)
  | succ t ih =>
    rw [hrec t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |μ1 * y t ω + g (t + 1) ω| ≤ |μ1| * |y t ω| + |g (t + 1) ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |μ1| * K + Mg := add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg _)) (hg _ _)
      _ ≤ K := by linarith

/-- Woodford (2003), survey §4.3 (the workhorse), Chapter 7 (2.7), (2.29): for
`βμ² − (1 + β + c)μ + 1 = β(μ − μ₁)(μ − μ₂)` with `0 < μ₁ < 1 < μ₂`, bounded adapted forcing `f`
and a bounded adapted `y`, the equation `βE_t y_{t+1} − (1 + β + c)y_t + y_{t−1} = f_t`
(`t ≥ t₀`) holds iff `y_t = μ₁y_{t−1} − β⁻¹∑_j μ₂^{−j−1}E_t f_{t+j}` (`t ≥ t₀`). -/
theorem workhorse_iff {β c μ1 μ2 M : ℝ} (hβ : 0 < β) (hr : RootPair β c μ1 μ2)
    {f y : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) (hya : 𝔼.Adapted y)
    (hyb : BoundedProc y) :
    (∀ t, β • 𝔼.E (t + 1) (y (t + 2)) - (1 + β + c) • y (t + 1) + y t = f (t + 1)) ↔
      ∀ t, y (t + 1) = μ1 • y t - (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ f (t + 1) := by
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hμ20 : μ2 ≠ 0 := by linarith
  have hβ0 : β ≠ 0 := hβ.ne'
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  obtain ⟨-, -, -, hs, hp⟩ := hr
  have hs' : β * (μ1 + μ2) = 1 + β + c := by rw [hs]; field_simp
  have hp' : β * (μ1 * μ2) = 1 := by rw [hp]; field_simp
  -- the factorisation `βE y' − (1+β+c) y + y₋ = β(E y' − μ₁ y) − βμ₂(y − μ₁ y₋)`
  have key : ∀ EY2 Y1 Y0 : ℝ, β * EY2 - (1 + β + c) * Y1 + Y0 =
      β * (EY2 - μ1 * Y1) - β * μ2 * (Y1 - μ1 * Y0) := fun EY2 Y1 Y0 => by
    linear_combination Y1 * hs' - Y0 * hp'
  set g : ℕ → Ω → ℝ := fun n => (-(β⁻¹ * μ2⁻¹)) • f (n + 1) with hg_def
  have hg : ∀ t ω, |g t ω| ≤ |β⁻¹ * μ2⁻¹| * M := fun t ω => by
    simp only [hg_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hf _ ω) (by positivity)
  have hga : (shiftSys 𝔼 1).Adapted g := fun t => by
    simp only [hg_def, shiftSys_E, map_smul, hfa (t + 1)]
  have hgS : ∀ t, (shiftSys 𝔼 1).forwardSeries μ2⁻¹ g t =
      (-(β⁻¹ * μ2⁻¹)) • 𝔼.forwardSeries μ2⁻¹ f (t + 1) := fun t => by
    rw [← shift_forwardSeries, ← forwardSeries_smul]
  constructor
  · intro h
    set w : ℕ → Ω → ℝ := fun t => y (t + 1) - μ1 • y t with hw_def
    have hw : ForwardSolution.Solves (shiftSys 𝔼 1) μ2⁻¹ g w := by
      intro t
      have hEw : (shiftSys 𝔼 1).E t (w (t + 1)) = 𝔼.E (t + 1) (y (t + 2)) - μ1 • y (t + 1) := by
        rw [shiftSys_E, hw_def]
        simp only [map_sub, map_smul, hya (t + 1)]
      rw [hEw]
      funext ω
      have h1 := congrFun (h t) ω
      simp only [hw_def, hg_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        at h1 ⊢
      rw [key] at h1
      have h3 : y (t + 1) ω - μ1 * y t ω = μ2⁻¹ * (𝔼.E (t + 1) (y (t + 2)) ω -
          μ1 * y (t + 1) ω) - β⁻¹ * μ2⁻¹ * f (t + 1) ω := by
        field_simp
        linear_combination -h1
      linear_combination h3
    obtain ⟨My, hMy⟩ := hyb
    have hwb : BoundedProc w := ⟨My + |μ1| * My, fun t ω => by
      simp only [hw_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      calc |y (t + 1) ω - μ1 * y t ω| ≤ |y (t + 1) ω| + |μ1 * y t ω| := abs_sub _ _
        _ ≤ My + |μ1| * My := by
          rw [abs_mul]
          exact add_le_add (hMy _ _) (mul_le_mul_of_nonneg_left (hMy _ _) (abs_nonneg _))⟩
    have heq := ForwardSolution.eq_forwardSeries_abs (shiftSys 𝔼 1) hq hg hga hw hwb
    intro t
    have ht := congrFun heq t
    rw [hgS] at ht
    funext ω
    have h2 := congrFun ht ω
    simp only [hw_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
    linarith
  · intro h t
    have hS := ForwardSolution.forwardSeries_solves_abs 𝔼 hq hf hfa (t + 1)
    have hE : 𝔼.E (t + 1) (y (t + 2)) = μ1 • y (t + 1) -
        (β⁻¹ * μ2⁻¹) • 𝔼.E (t + 1) (𝔼.forwardSeries μ2⁻¹ f (t + 1 + 1)) := by
      rw [show t + 2 = t + 1 + 1 by ring, h (t + 1), map_sub, map_smul, map_smul, hya (t + 1)]
    rw [hE]
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun hS ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [key]
    have e1 : β * (β⁻¹ * μ2⁻¹) = μ2⁻¹ := by field_simp
    have e2 : β * μ2 * (β⁻¹ * μ2⁻¹) = 1 := by field_simp
    linear_combination (-(β * μ2)) * h1 + h2 +
      (-(𝔼.E (t + 1) (𝔼.forwardSeries μ2⁻¹ f (t + 1 + 1)) ω)) * e1 +
      𝔼.forwardSeries μ2⁻¹ f (t + 1) ω * e2

/-- Woodford (2003), survey §4.3 (the workhorse): given `y_{t₀−1}` (known at `t₀ − 1`, bounded),
`βE_t y_{t+1} − (1 + β + c)y_t + y_{t−1} = f_t` has exactly one bounded adapted solution. -/
theorem workhorse_existsUnique {β c μ1 μ2 M B0 : ℝ} (hβ : 0 < β) (hr : RootPair β c μ1 μ2)
    {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {y0 : Ω → ℝ}
    (hy0 : 𝔼.E 0 y0 = y0) (hy0b : ∀ ω, |y0 ω| ≤ B0) :
    ∃! y : ℕ → Ω → ℝ, y 0 = y0 ∧ 𝔼.Adapted y ∧ BoundedProc y ∧
      ∀ t, β • 𝔼.E (t + 1) (y (t + 2)) - (1 + β + c) • y (t + 1) + y t = f (t + 1) := by
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hμ1 : |μ1| < 1 := by rw [abs_of_pos hr.1]; exact hr.2.1
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  set g : ℕ → Ω → ℝ := fun t => (-(β⁻¹ * μ2⁻¹)) • 𝔼.forwardSeries μ2⁻¹ f t with hg_def
  obtain ⟨MS, hMS⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 hq hf
  have hSa := ForwardSolution.forwardSeries_adapted_abs 𝔼 hq hf
  have hgb : ∀ t ω, |g t ω| ≤ |β⁻¹ * μ2⁻¹| * MS := fun t ω => by
    simp only [hg_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hMS _ _) (by positivity)
  set y := multPath μ1 0 (fun t => (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ f t) y0 with hy_def
  have hrec : ∀ t, y (t + 1) = μ1 • y t + g (t + 1) := fun t => by
    funext ω
    simp only [hy_def, hg_def, multPath, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hya : 𝔼.Adapted y := by
    intro t
    induction t with
    | zero => exact hy0
    | succ t ih =>
      rw [hrec t, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, hg_def,
        map_smul, hSa (t + 1)]
  have hyb : BoundedProc y := rec_bounded hμ1 hrec hy0b hgb
  have hrec' : ∀ t, y (t + 1) = μ1 • y t - (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ f (t + 1) :=
    fun t => by
      rw [hrec t, hg_def]
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  refine ⟨y, ⟨rfl, hya, hyb, (workhorse_iff 𝔼 hβ hr hf hfa hya hyb).mpr hrec'⟩, ?_⟩
  rintro z ⟨hz0, hza, hzb, hz⟩
  have hzr := (workhorse_iff 𝔼 hβ hr hf hfa hza hzb).mp hz
  funext t
  induction t with
  | zero => exact hz0
  | succ t ih => rw [hzr t, hrec' t, ih]

/-! ### (2.28)–(2.30): partial adjustment towards the desired rate -/

/-- Woodford (2003), p. 506: the characteristic equation `μ² − (1 + β⁻¹ + λₓσ²/λᵢ)μ + β⁻¹ = 0`
(with `c = λₓσ²/λᵢ > 0`) has two real roots `0 < μ₁ < 1 < μ₂`; they are the roots of
`βμ² − (1 + β + βc)μ + 1 = 0`. -/
theorem charEq_roots {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    RootPair β (β * c) (mu1 β (β * c)) (mu2 β (β * c)) ∧
      mu1 β (β * c) ^ 2 - (1 + β⁻¹ + c) * mu1 β (β * c) + β⁻¹ = 0 ∧
      mu2 β (β * c) ^ 2 - (1 + β⁻¹ + c) * mu2 β (β * c) + β⁻¹ = 0 := by
  have hr := rootPair_exists hβ (mul_pos hβ hc)
  have h1 := rootPair_root_lo hβ hr
  have h2 := rootPair_root_hi hβ hr
  have hβ0 : β ≠ 0 := hβ.ne'
  refine ⟨hr, ?_, ?_⟩
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

/-- Woodford (2003), eq. (2.30), p. 506 (corrected, survey error E8): the desired interest rate
`ī_t = (1 − μ₂⁻¹)∑_j μ₂^{−j}E_t rⁿ_{t+j}`. -/
noncomputable def ibar (μ2 : ℝ) (rn : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (1 - μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ rn t

/-- Woodford (2003), (2.28), p. 506: (2.28) is the workhorse equation with `c' = βλₓσ²/λᵢ` and
forcing `−βλₓσ²λᵢ⁻¹ rⁿ_t`. -/
theorem eq228_iff_workhorse {β c : ℝ} (hβ : 0 < β) {rn i : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i) :
    Eq228 𝔼 β c rn i ↔ ∀ t, β • 𝔼.E (t + 1) (i (t + 2)) - (1 + β + β * c) • i (t + 1) + i t =
      (-(β * c)) • rn (t + 1) := by
  refine forall_congr' fun t => ?_
  rw [map_sub, map_smul, hia (t + 1), funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hβ0 : β ≠ 0 := hβ.ne'
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    field_simp
    linear_combination -h

/-- **Equations (2.29)–(2.30)** (Woodford (2003), p. 506, with E8 corrected): for bounded adapted
`rⁿ`, a bounded adapted interest-rate path solves (2.28) iff it follows the partial-adjustment
rule `i_t = μ₁i_{t−1} + (1 − μ₁)ī_t`, `ī_t = (1 − μ₂⁻¹)∑_j μ₂^{−j}E_t rⁿ_{t+j}`, where
`μ₁, μ₂` are the roots of the characteristic equation (`c = λₓσ²/λᵢ`). -/
theorem eq228_iff_229 {β c μ1 μ2 M : ℝ} (hβ : 0 < β) (hr : RootPair β (β * c) μ1 μ2)
    {rn i : ℕ → Ω → ℝ} (hrn : ∀ t ω, |rn t ω| ≤ M) (hrna : 𝔼.Adapted rn) (hia : 𝔼.Adapted i)
    (hib : BoundedProc i) :
    Eq228 𝔼 β c rn i ↔ ∀ t, i (t + 1) = μ1 • i t + (1 - μ1) • ibar 𝔼 μ2 rn (t + 1) := by
  have hf : ∀ t ω, |((-(β * c)) • rn) t ω| ≤ |β * c| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hrn t ω) (by positivity)
  have hfa : 𝔼.Adapted ((-(β * c)) • rn) := fun t => by
    simp only [Pi.smul_apply, map_smul, hrna t]
  rw [eq228_iff_workhorse 𝔼 hβ hia]
  have hw := workhorse_iff 𝔼 hβ hr hf hfa hia hib
  simp only [Pi.smul_apply] at hw
  rw [hw]
  have hid := rootPair_identity hβ hr
  have hμ2 : μ2 ≠ 0 := by linarith [hr.2.2.1]
  have hβ0 : β ≠ 0 := hβ.ne'
  have hfs : ∀ t, 𝔼.forwardSeries μ2⁻¹ (fun n => (-(β * c)) • rn n) t =
      (-(β * c)) • 𝔼.forwardSeries μ2⁻¹ rn t := fun t => forwardSeries_smul 𝔼 _ _ rn t
  refine forall_congr' fun t => ?_
  rw [show (-(β * c)) • rn = fun n => (-(β * c)) • rn n from rfl, hfs]
  unfold ibar
  rw [smul_smul, smul_smul]
  have hid' : (1 - μ1) * (μ2 - 1) = c :=
    mul_left_cancel₀ hβ0 (by linear_combination hid)
  have hcoef : -(β⁻¹ * μ2⁻¹ * -(β * c)) = (1 - μ1) * (1 - μ2⁻¹) := by
    field_simp
    linear_combination -hid'
  rw [sub_eq_add_neg, ← neg_smul, hcoef]

/-- **Equations (2.29)–(2.30)** (Woodford (2003), p. 506: "this equation has a unique bounded
solution of the form (2.29) in the case of any bounded process for the disturbance"): given
`i_{t₀−1}`, (2.28) has exactly one bounded adapted solution, and it is the partial-adjustment
rule (2.29). -/
theorem eq228_existsUnique {β c μ1 μ2 M B0 : ℝ} (hβ : 0 < β) (hr : RootPair β (β * c) μ1 μ2)
    {rn : ℕ → Ω → ℝ} (hrn : ∀ t ω, |rn t ω| ≤ M) (hrna : 𝔼.Adapted rn) {i0 : Ω → ℝ}
    (hi0 : 𝔼.E 0 i0 = i0) (hi0b : ∀ ω, |i0 ω| ≤ B0) :
    (∃! i : ℕ → Ω → ℝ, i 0 = i0 ∧ 𝔼.Adapted i ∧ BoundedProc i ∧ Eq228 𝔼 β c rn i) ∧
      ∀ i : ℕ → Ω → ℝ, 𝔼.Adapted i → BoundedProc i → Eq228 𝔼 β c rn i →
        ∀ t, i (t + 1) = μ1 • i t + (1 - μ1) • ibar 𝔼 μ2 rn (t + 1) := by
  have hf : ∀ t ω, |((-(β * c)) • rn) t ω| ≤ |β * c| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hrn t ω) (by positivity)
  have hfa : 𝔼.Adapted ((-(β * c)) • rn) := fun t => by
    simp only [Pi.smul_apply, map_smul, hrna t]
  refine ⟨?_, fun i hia hib h => (eq228_iff_229 𝔼 hβ hr hrn hrna hia hib).mp h⟩
  obtain ⟨y, ⟨hy0, hya, hyb, hy⟩, huniq⟩ := workhorse_existsUnique 𝔼 hβ hr hf hfa hi0 hi0b
  refine ⟨y, ⟨hy0, hya, hyb, (eq228_iff_workhorse 𝔼 hβ hya).mpr hy⟩, ?_⟩
  rintro z ⟨hz0, hza, hzb, hz⟩
  exact huniq z ⟨hz0, hza, hzb, (eq228_iff_workhorse 𝔼 hβ hza).mp hz⟩

/-- Woodford (2003), p. 506 ("the desired level ī_t is a weighted average of current and
expected future natural rates"): the weights `(1 − μ₂⁻¹)μ₂^{−j}` of (2.30) are positive and sum
to one. -/
theorem ibar_weights {μ2 : ℝ} (hμ2 : 1 < μ2) :
    (∀ j : ℕ, 0 < (1 - μ2⁻¹) * μ2⁻¹ ^ j) ∧ ∑' j : ℕ, (1 - μ2⁻¹) * μ2⁻¹ ^ j = 1 := by
  have hq0 : 0 < μ2⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  refine ⟨fun j => mul_pos (by linarith) (pow_pos hq0 j), ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
  have : μ2 - 1 ≠ 0 := by linarith
  have : μ2 ≠ 0 := by linarith
  field_simp

/-- **Survey error E8 confirmed** (Woodford (2003), (2.30), p. 506): the printed weights
`(1 − μ₂)μ₂^{−j}` are negative and sum to `−μ₂ ≠ 1`. -/
theorem printed_230_weights {μ2 : ℝ} (hμ2 : 1 < μ2) :
    (∀ j : ℕ, (1 - μ2) * μ2⁻¹ ^ j < 0) ∧ ∑' j : ℕ, (1 - μ2) * μ2⁻¹ ^ j = -μ2 := by
  have hq0 : 0 < μ2⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  refine ⟨fun j => mul_neg_of_neg_of_pos (by linarith) (pow_pos hq0 j), ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
  have : μ2 - 1 ≠ 0 := by linarith
  have : μ2 ≠ 0 := by linarith
  field_simp
  ring

/-- Woodford (2003), (2.30), p. 506, as printed: `(1 − μ₂)∑_j μ₂^{−j}E_t rⁿ_{t+j}`. -/
noncomputable def ibarPrinted (μ2 : ℝ) (rn : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (1 - μ2) • 𝔼.forwardSeries μ2⁻¹ rn t

/-- **Survey error E8 confirmed** (Woodford (2003), (2.29)–(2.30), p. 506): under perfect
foresight with a constant natural rate `rⁿ ≡ r̄ ≠ 0`, no interest-rate path following the printed
rule `i_t = μ₁i_{t−1} + (1 − μ₁)(1 − μ₂)∑_j μ₂^{−j}E_t rⁿ_{t+j}` solves (2.28). -/
theorem not_printed_230 {β c μ1 μ2 rbar : ℝ} (hβ : 0 < β) (hr : RootPair β (β * c) μ1 μ2)
    (hrbar : rbar ≠ 0) {i : ℕ → Unit → ℝ}
    (hi : ∀ t, i (t + 1) = μ1 • i t +
      (1 - μ1) • ibarPrinted perfectForesight μ2 (fun _ _ => rbar) (t + 1)) :
    ¬ Eq228 perfectForesight β c (fun _ _ => rbar) i := by
  intro h
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hμ1 : |μ1| < 1 := by rw [abs_of_pos hr.1]; exact hr.2.1
  have hq0 : 0 ≤ μ2⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  have hconst : ∀ t, perfectForesight.forwardSeries μ2⁻¹ (fun _ _ => rbar) t =
      fun _ => rbar * (1 - μ2⁻¹)⁻¹ := fun t => by
    funext ω
    unfold ExpectationSystem.forwardSeries
    change ∑' k, μ2⁻¹ ^ k * rbar = _
    rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, mul_comm]
  have hrn : ∀ t (ω : Unit), |(fun _ _ => rbar : ℕ → Unit → ℝ) t ω| ≤ |rbar| :=
    fun _ _ => le_rfl
  have hib : BoundedProc i := by
    refine rec_bounded (g := fun n => (1 - μ1) • ibarPrinted perfectForesight μ2
      (fun _ _ => rbar) n) hμ1 hi (B0 := |i 0 ()|) (fun ω => le_rfl) (Mg := |(1 - μ1) *
      ((1 - μ2) * (rbar * (1 - μ2⁻¹)⁻¹))|) (fun t ω => ?_)
    unfold ibarPrinted
    rw [hconst]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact le_of_eq (by ring_nf)
  have h229 := (eq228_iff_229 perfectForesight hβ hr hrn (fun _ => rfl) (fun _ => rfl) hib).mp h 0
  have h0 := congrFun ((hi 0).symm.trans h229) ()
  unfold ibarPrinted ibar at h0
  rw [hconst] at h0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at h0
  have h1 : 1 - μ1 ≠ 0 := by linarith [hr.2.1]
  have hq : 1 - μ2⁻¹ ≠ 0 := by linarith
  have hμ20 : μ2 ≠ 0 := by linarith
  have hμ21 : μ2 - 1 ≠ 0 := by linarith
  field_simp at h0
  nlinarith [h0, hμ2, sq_nonneg μ2]

/-! ### Comparative statics of `μ₁` and of the slope of `ī` (p. 506) -/

/-- Woodford (2003), p. 506: the smaller root of `βμ² − (1 + β + βc)μ + 1` is strictly
decreasing in `c = λₓσ²/λᵢ > 0`. -/
theorem mu1_strictAnti {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (fun c => mu1 β (β * c)) (Set.Ioi 0) := by
  intro c hc c' hc' hlt
  simp only [Set.mem_Ioi] at hc hc'
  have hr := rootPair_exists hβ (mul_pos hβ hc)
  have hr' := rootPair_exists hβ (mul_pos hβ hc')
  set m := mu1 β (β * c)
  have hm := rootPair_root_lo hβ hr
  have hfac := rootPair_factor hβ hr' m
  have hneg : β * (m - mu1 β (β * c')) * (m - mu2 β (β * c')) < 0 := by
    rw [← hfac]
    nlinarith [mul_pos (mul_pos hβ (sub_pos.mpr hlt)) hr.1]
  have hlo := hr'.2.1
  have hhi := hr'.2.2.1
  simp only
  by_contra hge
  push Not at hge
  have h1 : m - mu1 β (β * c') ≤ 0 := by linarith
  have h2 : m - mu2 β (β * c') < 0 := by linarith
  have h3 : 0 ≤ (m - mu1 β (β * c')) * (m - mu2 β (β * c')) :=
    mul_nonneg_of_nonpos_of_nonpos h1 h2.le
  nlinarith [mul_nonneg hβ.le h3]

/-- Woodford (2003), p. 506 ("the optimal inertia coefficient `μ₁` ... is an increasing function
of `λᵢ/(λₓσ²)`"): as a function of `q = λᵢ/(λₓσ²) > 0`, `μ₁ = mu1 β (β/q)` is strictly
increasing. -/
theorem mu1_strictMono {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun q => mu1 β (β * q⁻¹)) (Set.Ioi 0) := by
  intro q hq q' hq' hlt
  simp only [Set.mem_Ioi] at hq hq'
  exact mu1_strictAnti hβ (Set.mem_Ioi.mpr (inv_pos.mpr hq')) (Set.mem_Ioi.mpr (inv_pos.mpr hq))
    (inv_strictAnti₀ hq hlt)

/-- Woodford (2003), p. 506: for the AR(1) natural rate (2.27), `rⁿ_t = r̄ + r̂_t` with
`E_t r̂_{t+1} = ρ r̂_t`, `|ρ| < 1`, the desired rate is `ī_t = r̄ + s(rⁿ_t − r̄)` with slope
`s = (1 − μ₂⁻¹)/(1 − ρμ₂⁻¹) = (μ₂ − 1)/(μ₂ − ρ)`. -/
theorem ibar_ar1 {μ2 ρ rbar : ℝ} (hμ2 : 1 < μ2) (hρ : |ρ| < 1) {rh : ℕ → Ω → ℝ}
    (hr : 𝔼.IsAR1 ρ rh) (t : ℕ) :
    ibar 𝔼 μ2 (fun n => (fun _ => rbar) + rh n) t =
      (fun _ => rbar) + ((μ2 - 1) / (μ2 - ρ)) • rh t := by
  have hq0 : 0 ≤ μ2⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  have hqρ : |μ2⁻¹ * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg hq0]
    calc μ2⁻¹ * |ρ| ≤ 1 * |ρ| := mul_le_mul_of_nonneg_right hq1.le (abs_nonneg ρ)
      _ < 1 := by linarith
  funext ω
  unfold ibar ExpectationSystem.forwardSeries
  have hterm : ∀ k, μ2⁻¹ ^ k * 𝔼.E t ((fun _ => rbar) + rh (t + k)) ω =
      rbar * μ2⁻¹ ^ k + rh t ω * (μ2⁻¹ * ρ) ^ k := fun k => by
    rw [map_add, 𝔼.const, 𝔼.ar1_iterate hr t k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hterm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [((summable_geometric_of_lt_one hq0 hq1).mul_left rbar).tsum_add
      ((summable_geometric_of_abs_lt_one hqρ).mul_left (rh t ω)),
    tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1,
    tsum_geometric_of_abs_lt_one hqρ]
  have h1 : μ2 ≠ 0 := by linarith
  have h2 : μ2 - ρ ≠ 0 := by
    have := (abs_lt.mp hρ).2
    linarith
  have h3 : 1 - μ2⁻¹ ≠ 0 := by linarith
  have h4 : 1 - μ2⁻¹ * ρ ≠ 0 := by linarith [(abs_lt.mp hqρ).2]
  have h5 : μ2 - 1 ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), p. 506 ("an increasing linear function of `rⁿ_t` ... with a slope less than
one"): for `ρ < 1 < μ₂`, the slope `s = (μ₂ − 1)/(μ₂ − ρ)` lies in `(0, 1)`. -/
theorem slope_pos_lt_one {μ2 ρ : ℝ} (hμ2 : 1 < μ2) (hρ : ρ < 1) :
    0 < (μ2 - 1) / (μ2 - ρ) ∧ (μ2 - 1) / (μ2 - ρ) < 1 := by
  have hd : 0 < μ2 - ρ := by linarith
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [div_lt_one hd]
  linarith

/-- Woodford (2003), p. 506 ("though it gets closer to one as the fluctuations in the natural
rate become more persistent"): the slope is strictly increasing in `ρ` (for `ρ < μ₂`). -/
theorem slope_strictMono {μ2 : ℝ} (hμ2 : 1 < μ2) :
    StrictMonoOn (fun ρ => (μ2 - 1) / (μ2 - ρ)) (Set.Iio μ2) := by
  intro ρ hρ ρ' hρ' hlt
  simp only [Set.mem_Iio] at hρ hρ'
  simp only
  exact div_lt_div_of_pos_left (by linarith) (by linarith) (by linarith)

/-- Woodford (2003), p. 506: the slope tends to one as `ρ → 1`. -/
theorem slope_tendsto_one {μ2 : ℝ} (hμ2 : 1 < μ2) :
    Tendsto (fun ρ => (μ2 - 1) / (μ2 - ρ)) (𝓝[<] 1) (𝓝 1) := by
  have hc : ContinuousAt (fun ρ => (μ2 - 1) / (μ2 - ρ)) 1 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simp; linarith)
  have h1 : (μ2 - 1) / (μ2 - 1) = 1 := div_self (by linarith)
  have := hc.tendsto
  simp only [h1] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### Lagrangian sufficiency for the `κ = 0` problem (p. 506 and footnote 26) -/

/-- **Lagrangian sufficiency** (Woodford (2003), p. 506, footnote 26, and the method of §2.1;
survey §4.4), for the `κ = 0` problem: let `(x̂, î)` satisfy the IS relation (2.23) (with zero
inflation) and the first-order conditions (1.17)–(1.18) with a bounded adapted multiplier `φ`.
Then for every bounded plan `(x, i)` satisfying (2.23) with the same initial condition —
`φ_{t₀−1}(x_{t₀} − x̂_{t₀}) = 0`, i.e. either the timeless constraint `x_{t₀} = x̂_{t₀}` (2.26) or
`φ_{t₀−1} = 0` (2.25) — the expected discounted loss (2.24) (`π ≡ 0`) of `(x̂, î)` is no larger:
`E_{t₀}∑βᵏ[λₓ(x̂ − x*)² + λᵢ(î − i*)²] ≤ E_{t₀}∑βᵏ[λₓ(x − x*)² + λᵢ(i − i*)²]`. Requires the
pull-out property (true for finite event trees and perfect foresight). -/
theorem sufficiency_kappa0 (hpo : 𝔼.PullOut) {β σ lamx lami xs is : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hlx : 0 ≤ lamx) (hli : 0 ≤ lami) {rn xh ih φ x i : ℕ → Ω → ℝ}
    (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) (hxhb : BoundedProc xh) (hihb : BoundedProc ih)
    (hxb : BoundedProc x) (hib : BoundedProc i)
    (h117 : ∀ t, lamx • (xh (t + 1) - fun _ => xs) + φ (t + 1) - β⁻¹ • φ t = 0)
    (h118 : ∀ t, lami • (ih (t + 1) - fun _ => is) + σ • φ (t + 1) = 0)
    (hISh : ∀ t, xh (t + 1) = 𝔼.E (t + 1) (xh (t + 2)) - σ • (ih (t + 1) - rn (t + 1)))
    (hIS : ∀ t, x (t + 1) = 𝔼.E (t + 1) (x (t + 2)) - σ • (i (t + 1) - rn (t + 1)))
    (hinit : φ 0 * (x 1 - xh 1) = 0) (ω : Ω) :
    𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (xh (k + 1) ω' - xs) ^ 2 +
        lami * (ih (k + 1) ω' - is) ^ 2)) ω ≤
      𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (x (k + 1) ω' - xs) ^ 2 +
        lami * (i (k + 1) ω' - is) ^ 2)) ω := by
  obtain ⟨Mφ, hMφ⟩ := hφb
  obtain ⟨Mxh, hMxh⟩ := hxhb
  obtain ⟨Mih, hMih⟩ := hihb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mi, hMi⟩ := hib
  -- bounds on the period losses
  have hsqb : ∀ (y : ℕ → Ω → ℝ) (My c : ℝ), (∀ t ω, |y t ω| ≤ My) →
      ∀ t ω, |(y t ω - c) ^ 2| ≤ (My + |c|) ^ 2 := fun y My c hy t ω => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hy t ω) le_rfl)) 2
  have hLb : ∀ (y z : ℕ → Ω → ℝ) (My Mz : ℝ), (∀ t ω, |y t ω| ≤ My) → (∀ t ω, |z t ω| ≤ Mz) →
      ∀ k ω', |β ^ k * (lamx * (y (k + 1) ω' - xs) ^ 2 + lami * (z (k + 1) ω' - is) ^ 2)| ≤
        β ^ k * (lamx * (My + |xs|) ^ 2 + lami * (Mz + |is|) ^ 2) := by
    intro y z My Mz hy hz k ω'
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0.le k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le k)
    calc |lamx * (y (k + 1) ω' - xs) ^ 2 + lami * (z (k + 1) ω' - is) ^ 2|
        ≤ |lamx * (y (k + 1) ω' - xs) ^ 2| + |lami * (z (k + 1) ω' - is) ^ 2| := abs_add_le _ _
      _ ≤ lamx * (My + |xs|) ^ 2 + lami * (Mz + |is|) ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hlx, abs_of_nonneg hli]
          gcongr
          · exact hsqb y My xs hy (k + 1) ω'
          · exact hsqb z Mz is hz (k + 1) ω'
  rw [𝔼.E_tsum hβ0.le hβ1 (hLb xh ih Mxh Mih hMxh hMih) 1 ω,
    𝔼.E_tsum hβ0.le hβ1 (hLb x i Mx Mi hMx hMi) 1 ω]
  -- the Lagrangian lower bound
  set D : ℕ → Ω → ℝ := fun n => x n - xh n with hD
  set a : ℕ → ℝ := fun k => 𝔼.E 1 (φ k * D (k + 1)) ω with ha
  have hab : ∀ k, |a k| ≤ Mφ * (Mx + Mxh) := fun k => by
    refine 𝔼.abs_E_le (fun ω' => ?_) 1 ω
    simp only [hD, Pi.mul_apply, Pi.sub_apply, abs_mul]
    exact mul_le_mul (hMφ _ _) ((abs_sub _ _).trans (add_le_add (hMx _ _) (hMxh _ _)))
      (abs_nonneg _) ((abs_nonneg _).trans (hMφ 0 ω'))
  set G : ℕ → Ω → ℝ := fun k => (2 * β⁻¹) • (φ k * D (k + 1)) -
    (2 : ℝ) • (φ (k + 1) * 𝔼.E (k + 1) (D (k + 2))) with hG
  have hGle : ∀ k ω', G k ω' ≤ (lamx * (x (k + 1) ω' - xs) ^ 2 + lami * (i (k + 1) ω' - is) ^ 2) -
      (lamx * (xh (k + 1) ω' - xs) ^ 2 + lami * (ih (k + 1) ω' - is) ^ 2) := by
    intro k ω'
    have f1 := congrFun (h117 k) ω'
    have f2 := congrFun (h118 k) ω'
    have f3 := congrFun (hISh k) ω'
    have f4 := congrFun (hIS k) ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at f1 f2 f3 f4
    have hED : 𝔼.E (k + 1) (D (k + 2)) ω' = 𝔼.E (k + 1) (x (k + 2)) ω' -
        𝔼.E (k + 1) (xh (k + 2)) ω' := by
      simp only [hD, map_sub, Pi.sub_apply]
    simp only [hG, hD, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [hED]
    have key : (lamx * (x (k + 1) ω' - xs) ^ 2 + lami * (i (k + 1) ω' - is) ^ 2) -
        (lamx * (xh (k + 1) ω' - xs) ^ 2 + lami * (ih (k + 1) ω' - is) ^ 2) -
        (2 * β⁻¹ * (φ k ω' * (x (k + 1) ω' - xh (k + 1) ω')) -
          2 * (φ (k + 1) ω' * (𝔼.E (k + 1) (x (k + 2)) ω' - 𝔼.E (k + 1) (xh (k + 2)) ω'))) =
        lamx * (x (k + 1) ω' - xh (k + 1) ω') ^ 2 + lami * (i (k + 1) ω' - ih (k + 1) ω') ^ 2 := by
      linear_combination 2 * (x (k + 1) ω' - xh (k + 1) ω') * f1 +
        2 * (i (k + 1) ω' - ih (k + 1) ω') * f2 - 2 * φ (k + 1) ω' * f4 + 2 * φ (k + 1) ω' * f3
    nlinarith [mul_nonneg hlx (sq_nonneg (x (k + 1) ω' - xh (k + 1) ω')),
      mul_nonneg hli (sq_nonneg (i (k + 1) ω' - ih (k + 1) ω'))]
  have hEG : ∀ k, 𝔼.E 1 (G k) ω = 2 * (β⁻¹ * a k - a (k + 1)) := by
    intro k
    have hpull : φ (k + 1) * 𝔼.E (k + 1) (D (k + 2)) = 𝔼.E (k + 1) (φ (k + 1) * D (k + 2)) :=
      (hpo (k + 1) _ _ (hφa (k + 1))).symm
    simp only [hG, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpull, 𝔼.tower (by omega : 1 ≤ k + 1)]
    simp only [ha]
    ring
  -- termwise comparison
  have hterm : ∀ k, 𝔼.E 1 (fun ω' => β ^ k * (lamx * (xh (k + 1) ω' - xs) ^ 2 +
      lami * (ih (k + 1) ω' - is) ^ 2)) ω + β ^ k * (2 * (β⁻¹ * a k - a (k + 1))) ≤
      𝔼.E 1 (fun ω' => β ^ k * (lamx * (x (k + 1) ω' - xs) ^ 2 +
        lami * (i (k + 1) ω' - is) ^ 2)) ω := by
    intro k
    have hle : (fun ω' => β ^ k * (lamx * (xh (k + 1) ω' - xs) ^ 2 +
        lami * (ih (k + 1) ω' - is) ^ 2)) + β ^ k • G k ≤
        fun ω' => β ^ k * (lamx * (x (k + 1) ω' - xs) ^ 2 + lami * (i (k + 1) ω' - is) ^ 2) := by
      intro ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left (hGle k ω') (pow_nonneg hβ0.le k)
      linarith
    have := 𝔼.mono 1 hle ω
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hEG, smul_eq_mul] at this
    exact this
  have hsE : ∀ (y z : ℕ → Ω → ℝ) (My Mz : ℝ), (∀ t ω, |y t ω| ≤ My) →
      (∀ t ω, |z t ω| ≤ Mz) → Summable (fun k => 𝔼.E 1 (fun ω' => β ^ k *
        (lamx * (y (k + 1) ω' - xs) ^ 2 + lami * (z (k + 1) ω' - is) ^ 2)) ω) :=
    fun y z My Mz hy hz => Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right
        (lamx * (My + |xs|) ^ 2 + lami * (Mz + |is|) ^ 2))
      (fun k => by
        rw [Real.norm_eq_abs]
        exact 𝔼.abs_E_le (fun ω' => hLb y z My Mz hy hz k ω') 1 ω)
  obtain ⟨hts, htv⟩ := tsum_telescope_inv hβ0 hβ1 hab
  have ha0 : a 0 = 0 := by
    simp only [ha, hD, zero_add]
    rw [hinit, map_zero]
    rfl
  have hsum2 : Summable (fun k => β ^ k * (2 * (β⁻¹ * a k - a (k + 1)))) :=
    (hts.mul_left 2).congr fun k => by ring
  have hval2 : ∑' k, β ^ k * (2 * (β⁻¹ * a k - a (k + 1))) = 0 := by
    rw [show (fun k => β ^ k * (2 * (β⁻¹ * a k - a (k + 1)))) =
      fun k => 2 * (β ^ k * (β⁻¹ * a k - a (k + 1))) from funext fun k => by ring,
      tsum_mul_left, htv, ha0]
    ring
  calc ∑' k, 𝔼.E 1 (fun ω' => β ^ k * (lamx * (xh (k + 1) ω' - xs) ^ 2 +
        lami * (ih (k + 1) ω' - is) ^ 2)) ω
      = ∑' k, (𝔼.E 1 (fun ω' => β ^ k * (lamx * (xh (k + 1) ω' - xs) ^ 2 +
          lami * (ih (k + 1) ω' - is) ^ 2)) ω + β ^ k * (2 * (β⁻¹ * a k - a (k + 1)))) := by
        rw [(hsE xh ih Mxh Mih hMxh hMih).tsum_add hsum2, hval2, add_zero]
    _ ≤ _ := Summable.tsum_le_tsum hterm ((hsE xh ih Mxh Mih hMxh hMih).add hsum2)
        (hsE x i Mx Mi hMx hMi)

/-- Woodford (2003), p. 506: the output gap implied by the first-order condition with `κ = 0`,
`x_t = x* + (λᵢ/(σλₓ))[(i_t − i*) − β⁻¹(i_{t−1} − i*)]` (Lean dates `t ≥ 1`). -/
noncomputable def xFromFoc (β σ lamx lami xs is : ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => xs) +
    (lami / (σ * lamx)) • ((i t - fun _ => is) - β⁻¹ • (i (t - 1) - fun _ => is))

/-- **The optimal policy with `κ = 0`** (Woodford (2003), (2.29)–(2.30), p. 506, footnote 26):
let `μ₁ < μ₂` be the roots of the characteristic equation with `c = λₓσ²/λᵢ`. Given the
predetermined `i_{t₀−1}`, the bounded adapted interest-rate path solving (2.28) exists, is
unique, follows the partial-adjustment rule (2.29)–(2.30), and together with the output gap of
the first-order condition satisfies the IS relation (2.23); and this plan minimises the expected
discounted loss (2.24) (with `κ = 0`, so `π ≡ 0`) among all bounded plans satisfying (2.23) and
the timeless constraint `x_{t₀} = x̄_{t₀}` (2.26), `x̄_{t₀}` being the plan's own date-`t₀` gap. -/
theorem optimal_plan_kappa0 (hpo : 𝔼.PullOut) {β σ lamx lami xs is M B0 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hlx : 0 < lamx) (hli : 0 < lami) {rn : ℕ → Ω → ℝ}
    (hrn : ∀ t ω, |rn t ω| ≤ M) (hrna : 𝔼.Adapted rn) {i0 : Ω → ℝ} (hi0 : 𝔼.E 0 i0 = i0)
    (hi0b : ∀ ω, |i0 ω| ≤ B0) :
    ∃ ih : ℕ → Ω → ℝ, ih 0 = i0 ∧ 𝔼.Adapted ih ∧ BoundedProc ih ∧
      Eq228 𝔼 β (lamx * σ ^ 2 / lami) rn ih ∧
      (∀ t, ih (t + 1) = mu1 β (β * (lamx * σ ^ 2 / lami)) • ih t +
        (1 - mu1 β (β * (lamx * σ ^ 2 / lami))) •
          ibar 𝔼 (mu2 β (β * (lamx * σ ^ 2 / lami))) rn (t + 1)) ∧
      (∀ t, xFromFoc β σ lamx lami xs is ih (t + 1) =
        𝔼.E (t + 1) (xFromFoc β σ lamx lami xs is ih (t + 2)) - σ • (ih (t + 1) - rn (t + 1))) ∧
      ∀ x i : ℕ → Ω → ℝ, BoundedProc x → BoundedProc i →
        (∀ t, x (t + 1) = 𝔼.E (t + 1) (x (t + 2)) - σ • (i (t + 1) - rn (t + 1))) →
        x 1 = xFromFoc β σ lamx lami xs is ih 1 → ∀ ω,
        𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (xFromFoc β σ lamx lami xs is ih (k + 1) ω' - xs) ^ 2
            + lami * (ih (k + 1) ω' - is) ^ 2)) ω ≤
          𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (x (k + 1) ω' - xs) ^ 2 +
            lami * (i (k + 1) ω' - is) ^ 2)) ω := by
  set c := lamx * σ ^ 2 / lami with hc
  have hcpos : 0 < c := by positivity
  have hr := (charEq_roots hβ0 hcpos).1
  obtain ⟨⟨ih, ⟨hih0, hiha, hihb, h228⟩, -⟩, h229⟩ :=
    eq228_existsUnique 𝔼 hβ0 hr hrn hrna hi0 hi0b
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hlx0 : lamx ≠ 0 := hlx.ne'
  have hli0 : lami ≠ 0 := hli.ne'
  set xh := xFromFoc β σ lamx lami xs is ih with hxh
  have hxh1 : ∀ t, xh (t + 1) = (fun _ => xs) +
      (lami / (σ * lamx)) • ((ih (t + 1) - fun _ => is) - β⁻¹ • (ih t - fun _ => is)) :=
    fun t => rfl
  have hISh := (foc_IS_iff_228 𝔼 hσ0 hlx0 hli0 hiha hxh1).mpr h228
  refine ⟨ih, hih0, hiha, hihb, h228, h229 ih hiha hihb h228, hISh, ?_⟩
  intro x i hxb hib hIS hx1 ω
  set φ : ℕ → Ω → ℝ := fun t => (-(lami / σ)) • (ih t - fun _ => is) with hφ
  have hφa : 𝔼.Adapted φ := fun t => by
    simp only [hφ, map_smul, map_sub, hiha t, 𝔼.const]
  obtain ⟨Mh, hMh⟩ := hihb
  have hφb : BoundedProc φ := ⟨|lami / σ| * (Mh + |is|), fun t ω => by
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMh t ω) le_rfl))
      (abs_nonneg _)⟩
  have hxhb : BoundedProc xh := ⟨|xs| + |lami / (σ * lamx)| * ((Mh + |is|) + |β⁻¹| * (Mh + |is|)),
    fun t ω => by
      simp only [hxh, xFromFoc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 : |ih t ω - is| ≤ Mh + |is| := (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
      have h2 : |ih (t - 1) ω - is| ≤ Mh + |is| :=
        (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
      calc |xs + lami / (σ * lamx) * (ih t ω - is - β⁻¹ * (ih (t - 1) ω - is))|
          ≤ |xs| + |lami / (σ * lamx)| * (|ih t ω - is| + |β⁻¹| * |ih (t - 1) ω - is|) := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (le_of_eq ?_)) (abs_nonneg _)
            rw [abs_mul]
        _ ≤ _ := by gcongr⟩
  have h117 : ∀ t, lamx • (xh (t + 1) - fun _ => xs) + φ (t + 1) - β⁻¹ • φ t = 0 := by
    intro t
    rw [hxh1 t]
    funext ω
    simp only [hφ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  have h118 : ∀ t, lami • (ih (t + 1) - fun _ => is) + σ • φ (t + 1) = 0 := by
    intro t
    funext ω
    simp only [hφ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  exact sufficiency_kappa0 𝔼 hpo hβ0 hβ1 hlx.le hli.le hφa hφb hxhb ⟨Mh, hMh⟩ hxb hib h117 h118
    hISh hIS (by rw [hx1, sub_self, mul_zero]) ω

/-- **The `t₀`-optimal plan with `κ = 0`** (Woodford (2003), (2.25), p. 503, and p. 506): with
the initial multiplier `φ_{t₀−1} = 0` (equivalently the fictitious lagged rate `i_{t₀−1} = i*`
in (1.18)), the solution of (2.28) from `i*` with the first-order-condition output gap minimises
the expected discounted loss among **all** bounded plans satisfying (2.23), without any
initial constraint. -/
theorem optimal_plan_kappa0_t0 (hpo : 𝔼.PullOut) {β σ lamx lami xs is M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hlx : 0 < lamx) (hli : 0 < lami) {rn : ℕ → Ω → ℝ}
    (hrn : ∀ t ω, |rn t ω| ≤ M) (hrna : 𝔼.Adapted rn) :
    ∃ ih : ℕ → Ω → ℝ, ih 0 = (fun _ => is) ∧ 𝔼.Adapted ih ∧ BoundedProc ih ∧
      Eq228 𝔼 β (lamx * σ ^ 2 / lami) rn ih ∧
      (∀ t, xFromFoc β σ lamx lami xs is ih (t + 1) =
        𝔼.E (t + 1) (xFromFoc β σ lamx lami xs is ih (t + 2)) - σ • (ih (t + 1) - rn (t + 1))) ∧
      ∀ x i : ℕ → Ω → ℝ, BoundedProc x → BoundedProc i →
        (∀ t, x (t + 1) = 𝔼.E (t + 1) (x (t + 2)) - σ • (i (t + 1) - rn (t + 1))) → ∀ ω,
        𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (xFromFoc β σ lamx lami xs is ih (k + 1) ω' - xs) ^ 2
            + lami * (ih (k + 1) ω' - is) ^ 2)) ω ≤
          𝔼.E 1 (fun ω' => ∑' k, β ^ k * (lamx * (x (k + 1) ω' - xs) ^ 2 +
            lami * (i (k + 1) ω' - is) ^ 2)) ω := by
  set c := lamx * σ ^ 2 / lami with hc
  have hcpos : 0 < c := by positivity
  have hr := (charEq_roots hβ0 hcpos).1
  obtain ⟨⟨ih, ⟨hih0, hiha, hihb, h228⟩, -⟩, -⟩ :=
    eq228_existsUnique 𝔼 hβ0 hr hrn hrna (i0 := fun _ => is) (𝔼.const 0 is)
      (B0 := |is|) (fun _ => le_rfl)
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hlx0 : lamx ≠ 0 := hlx.ne'
  have hli0 : lami ≠ 0 := hli.ne'
  set xh := xFromFoc β σ lamx lami xs is ih with hxh
  have hxh1 : ∀ t, xh (t + 1) = (fun _ => xs) +
      (lami / (σ * lamx)) • ((ih (t + 1) - fun _ => is) - β⁻¹ • (ih t - fun _ => is)) :=
    fun t => rfl
  have hISh := (foc_IS_iff_228 𝔼 hσ0 hlx0 hli0 hiha hxh1).mpr h228
  refine ⟨ih, hih0, hiha, hihb, h228, hISh, ?_⟩
  intro x i hxb hib hIS ω
  set φ : ℕ → Ω → ℝ := fun t => (-(lami / σ)) • (ih t - fun _ => is) with hφ
  have hφa : 𝔼.Adapted φ := fun t => by
    simp only [hφ, map_smul, map_sub, hiha t, 𝔼.const]
  obtain ⟨Mh, hMh⟩ := hihb
  have hφb : BoundedProc φ := ⟨|lami / σ| * (Mh + |is|), fun t ω => by
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMh t ω) le_rfl))
      (abs_nonneg _)⟩
  have hxhb : BoundedProc xh := ⟨|xs| + |lami / (σ * lamx)| * ((Mh + |is|) + |β⁻¹| * (Mh + |is|)),
    fun t ω => by
      simp only [hxh, xFromFoc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 : |ih t ω - is| ≤ Mh + |is| := (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
      have h2 : |ih (t - 1) ω - is| ≤ Mh + |is| :=
        (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
      calc |xs + lami / (σ * lamx) * (ih t ω - is - β⁻¹ * (ih (t - 1) ω - is))|
          ≤ |xs| + |lami / (σ * lamx)| * (|ih t ω - is| + |β⁻¹| * |ih (t - 1) ω - is|) := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (le_of_eq ?_)) (abs_nonneg _)
            rw [abs_mul]
        _ ≤ _ := by gcongr⟩
  have h117 : ∀ t, lamx • (xh (t + 1) - fun _ => xs) + φ (t + 1) - β⁻¹ • φ t = 0 := by
    intro t
    rw [hxh1 t]
    funext ω
    simp only [hφ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  have h118 : ∀ t, lami • (ih (t + 1) - fun _ => is) + σ • φ (t + 1) = 0 := by
    intro t
    funext ω
    simp only [hφ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, hih0, sub_self, smul_zero]
  exact sufficiency_kappa0 𝔼 hpo hβ0 hβ1 hlx.le hli.le hφa hφb hxhb ⟨Mh, hMh⟩ hxb hib h117 h118
    hISh hIS (by rw [hφ0, zero_mul]) ω

end Woodford.GainsFromCommitment.NaturalRateCommitment
