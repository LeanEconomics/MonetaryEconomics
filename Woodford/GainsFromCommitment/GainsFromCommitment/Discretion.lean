/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Expectations
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Discretionary policy with cost-push shocks

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, pp. 486–488.

The aggregate-supply relation with a cost-push shock is (2.1),
`π_t = κ x_t + β E_t π_{t+1} + u_t`. Under discretion the central bank takes the private
sector's expectation `E_t π_{t+1}` as given and each period minimises the period loss
`π_t² + λ (x_t − x*)²` subject to (2.1). Its first-order condition is (1.4),
`π_t + (λ/κ)(x_t − x*) = 0`, and substituting it into (2.1) gives (2.2),
`π_t = (1 + κ²/λ)⁻¹ (κ x* + u_t + β E_t π_{t+1})`.

Everything holds for an arbitrary `ExpectationSystem`, so both under perfect foresight and
under genuine uncertainty.

## Main results

* `isMinOn_iff_foc`: the static problem is solved exactly by the pairs on the constraint
  line satisfying (1.4) (necessity and sufficiency), and `foc_as_iff` gives (2.2).
* `exists_unique_static`: the static problem has exactly one minimiser.
* `infl23`: the Markov inflation process (2.3).
* `prop_7_5`: **Proposition 7.5** in its exact linear-quadratic form. A bounded adapted pair
  `(π, x)` is a discretionary equilibrium if and only if `π` is (2.3) and
  `x_t = x* − (κ/λ) π_t`. The equilibrium exists (`discretionEq_infl23`), and (2.3) is the unique
  bounded solution of (2.2) (`eq_infl23_of_solves22`), because the coefficient
  `βλ/(λ + κ²)` is below one.
* `markov_dependence`, `ar1_closed_form`, `ar1_persistence`: when `u` is Markov,
  `π_t` and `x_t` depend only on the current `u_t`. For an AR(1) shock the effects are only as
  persistent as the shock.
* `infl23_const_eq_bias`: the constant term of (2.3) is the deterministic discretionary
  inflation rate (1.6), the fixed point of (1.5).

The book's Proposition 7.5 also contains an approximation statement (error of order
`O(‖Δ_{−1}^{1/2}, Δ_y, ξ̃‖²)`) about the nonlinear model. This module proves the exact
statements about the linear-quadratic problem to which the approximation refers.
-/

namespace Woodford.GainsFromCommitment.Discretion

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The static problem of the discretionary central bank -/

/-- Woodford (2003), eq. (1.2), p. 469 (and p. 487): the period loss `π² + λ (x − x*)²`. -/
def periodLoss (lam xs p y : ℝ) : ℝ := p ^ 2 + lam * (y - xs) ^ 2

/-- Woodford (2003), eq. (2.1), p. 486: the inflation–output pairs `(π, x)` that satisfy the
aggregate-supply relation `π = κ x + β e + v` for a given expectation `e = E_t π_{t+1}` and
a given cost-push shock `v = u_t` (the constraint the discretionary bank perceives, p. 487). -/
def staticSet (β κ e v : ℝ) : Set (ℝ × ℝ) := {q | q.1 = κ * q.2 + β * e + v}

/-- Woodford (2003), p. 487: exact expansion of the period loss along the constraint line
(2.1). For two feasible pairs the loss difference is a positive quadratic plus a linear term
in the first-order condition `κ π + λ (x − x*)`. -/
theorem periodLoss_sub {β κ e v lam xs : ℝ} {q r : ℝ × ℝ} (hq : q ∈ staticSet β κ e v)
    (hr : r ∈ staticSet β κ e v) :
    periodLoss lam xs r.1 r.2 - periodLoss lam xs q.1 q.2 =
      (κ ^ 2 + lam) * (r.2 - q.2) ^ 2 + 2 * (r.2 - q.2) * (κ * q.1 + lam * (q.2 - xs)) := by
  have h1 : r.1 = q.1 + κ * (r.2 - q.2) := by
    simp only [staticSet, Set.mem_ofPred_eq] at hq hr
    rw [hr, hq]
    ring
  rw [periodLoss, periodLoss, h1]
  ring

/-- Woodford (2003), eq. (1.4), p. 471 (used again on p. 487): with `κ ≠ 0` the first-order
condition `π + (λ/κ)(x − x*) = 0` is equivalent to `κ π + λ (x − x*) = 0`. -/
theorem foc_iff_mul {κ lam xs p y : ℝ} (hκ : κ ≠ 0) :
    p + lam / κ * (y - xs) = 0 ↔ κ * p + lam * (y - xs) = 0 := by
  have h : p + lam / κ * (y - xs) = (κ * p + lam * (y - xs)) / κ := by
    field_simp
  rw [h, div_eq_zero_iff, or_iff_left hκ]

/-- Woodford (2003), eq. (1.4), pp. 471 and 487: a pair on the constraint line (2.1) minimises
`π² + λ (x − x*)²` over that line **if and only if** it satisfies the first-order condition
`π + (λ/κ)(x − x*) = 0`. -/
theorem isMinOn_iff_foc {β κ e v lam xs : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) {q : ℝ × ℝ}
    (hq : q ∈ staticSet β κ e v) :
    IsMinOn (fun r : ℝ × ℝ => periodLoss lam xs r.1 r.2) (staticSet β κ e v) q ↔
      q.1 + lam / κ * (q.2 - xs) = 0 := by
  rw [foc_iff_mul hκ.ne', isMinOn_iff]
  have hK : 0 < κ ^ 2 + lam := by positivity
  constructor
  · intro h
    by_contra hg
    set g := κ * q.1 + lam * (q.2 - xs) with hg_def
    set d := -g / (κ ^ 2 + lam) with hd
    have hr : (q.1 + κ * d, q.2 + d) ∈ staticSet β κ e v := by
      simp only [staticSet, Set.mem_ofPred_eq] at hq ⊢
      rw [hq]
      ring
    have hmin := h _ hr
    have hdiff := periodLoss_sub (lam := lam) (xs := xs) hq hr
    simp only [add_sub_cancel_left] at hdiff
    have hval : (κ ^ 2 + lam) * d ^ 2 + 2 * d * g = -(g ^ 2 / (κ ^ 2 + lam)) := by
      rw [hd]
      field_simp
      ring
    have hpos : 0 < g ^ 2 / (κ ^ 2 + lam) :=
      div_pos (lt_of_le_of_ne (sq_nonneg g) (Ne.symm (pow_ne_zero 2 hg))) hK
    simp only at hmin
    linarith
  · intro hg r hr
    have hdiff := periodLoss_sub (lam := lam) (xs := xs) hq hr
    rw [hg, mul_zero, add_zero] at hdiff
    have : 0 ≤ (κ ^ 2 + lam) * (r.2 - q.2) ^ 2 := by positivity
    linarith

/-- Woodford (2003), eq. (2.2), p. 487 (generalising (1.5), p. 471): the constraint (2.1)
together with the first-order condition (1.4) is equivalent to the best-response formula
`π = (1 + κ²/λ)⁻¹ (κ x* + u + β E_t π_{t+1})` with `x = x* − (κ/λ) π`. -/
theorem foc_as_iff {β κ e v lam xs p y : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) :
    (p = κ * y + β * e + v ∧ p + lam / κ * (y - xs) = 0) ↔
      (p = (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + v + β * e) ∧ y = xs - κ / lam * p) := by
  have hK : 0 < lam + κ ^ 2 := by positivity
  have hinv : (1 + κ ^ 2 / lam)⁻¹ = lam / (lam + κ ^ 2) := by
    field_simp
  rw [hinv, foc_iff_mul hκ.ne']
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = xs - κ / lam * p := by
      field_simp
      linarith
    refine ⟨?_, hy⟩
    rw [hy] at h1
    field_simp
    field_simp at h1
    linarith
  · rintro ⟨h1, h2⟩
    have h2' : lam * (y - xs) = -(κ * p) := by
      rw [h2]
      field_simp
      ring
    refine ⟨?_, by linarith⟩
    rw [h2]
    field_simp
    field_simp at h1
    nlinarith [h1]

/-- Woodford (2003), p. 487: the static problem of the discretionary bank has exactly one
minimiser on the constraint line (2.1), namely the pair given by (2.2). -/
theorem exists_unique_static {β κ e v lam xs : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) :
    ∃! q : ℝ × ℝ, q ∈ staticSet β κ e v ∧
      IsMinOn (fun r : ℝ × ℝ => periodLoss lam xs r.1 r.2) (staticSet β κ e v) q := by
  set p := (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + v + β * e) with hp
  set y := xs - κ / lam * p with hy
  have hboth := (foc_as_iff (β := β) (e := e) (v := v) (xs := xs) (p := p) (y := y) hκ hlam).mpr
    ⟨hp, hy⟩
  refine ⟨(p, y), ⟨hboth.1, (isMinOn_iff_foc hκ hlam hboth.1).mpr hboth.2⟩, ?_⟩
  rintro ⟨p', y'⟩ ⟨hmem, hmin⟩
  have hfoc := (isMinOn_iff_foc hκ hlam hmem).mp hmin
  have h := (foc_as_iff (y := y') hκ hlam).mp ⟨hmem, hfoc⟩
  simp only at h
  have hp' : p' = p := h.1
  rw [hp', ← hy] at h
  rw [Prod.mk.injEq]
  exact ⟨hp', h.2⟩

/-! ### Discretionary equilibrium -/

/-- Woodford (2003), §2.1, pp. 486–487: a **discretionary (Markov) equilibrium**. The pair
`(π, x)` is bounded and adapted, and in every period and state the bank's choice minimises the
period loss over the pairs satisfying (2.1), taking the private sector's expectation
`E_t π_{t+1}` and the shock `u_t` as given (its action cannot affect them in a Markov
equilibrium, p. 487). Membership of the constraint set is (2.1) itself. -/
def DiscretionEq (β κ lam xs : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧
    ∀ t ω, (π t ω, x t ω) ∈ staticSet β κ (𝔼.E t (π (t + 1)) ω) (u t ω) ∧
      IsMinOn (fun r : ℝ × ℝ => periodLoss lam xs r.1 r.2)
        (staticSet β κ (𝔼.E t (π (t + 1)) ω) (u t ω)) (π t ω, x t ω)

/-- Woodford (2003), eq. (2.2), p. 487, as an expectational difference equation:
`π_t = (1 + κ²/λ)⁻¹ (κ x* + u_t + β E_t π_{t+1})` at every date. -/
def Solves22 (β κ lam xs : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + u t ω + β * 𝔼.E t (π (t + 1)) ω)

/-- Woodford (2003), eq. (2.3), p. 487: the Markov inflation process
`π_t = κλ x*/((1 − β)λ + κ²) + ∑_{j ≥ 0} βʲ (λ/(λ + κ²))^{j+1} E_t u_{t+j}`. -/
noncomputable def infl23 (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => κ * lam / ((1 - β) * lam + κ ^ 2) * xs +
    ∑' j : ℕ, β ^ j * (lam / (lam + κ ^ 2)) ^ (j + 1) * 𝔼.E t (u (t + j)) ω

/-- Woodford (2003), p. 487: the output gap that goes with (2.3), obtained from (1.4),
`x_t = x* − (κ/λ) π_t`. -/
noncomputable def gap23 (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => xs - κ / lam * infl23 𝔼 β κ lam xs u t ω

/-- Woodford (2003), eq. (2.2), p. 487: the forcing term `(λ/(λ + κ²)) (κ x* + u_t)` of (2.2)
written as a forward equation `π_t = a β E_t π_{t+1} + a (κ x* + u_t)`. -/
def forcing22 (a κ xs : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => a * (κ * xs + u t ω)

/-- Woodford (2003), eq. (2.2), p. 487: `(1 + κ²/λ)⁻¹ = λ/(λ + κ²)`. -/
theorem coeff_eq {κ lam : ℝ} (hlam : 0 < lam) : (1 + κ ^ 2 / lam)⁻¹ = lam / (lam + κ ^ 2) := by
  have : 0 < lam + κ ^ 2 := by positivity
  field_simp

/-- Woodford (2003), p. 487 (survey §1, Prop 7.5): the discount factor of the forward equation
(2.2) is `β λ/(λ + κ²) ∈ [0, 1)`. -/
theorem coeff_lt_one {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) :
    0 ≤ lam / (lam + κ ^ 2) * β ∧ lam / (lam + κ ^ 2) * β < 1 := by
  have hK : 0 < lam + κ ^ 2 := by positivity
  have ha : lam / (lam + κ ^ 2) ≤ 1 := by
    rw [div_le_one hK]
    nlinarith [sq_nonneg κ]
  refine ⟨by positivity, ?_⟩
  have ha0 : 0 ≤ lam / (lam + κ ^ 2) := by positivity
  nlinarith

/-- Woodford (2003), eq. (2.2), p. 487: (2.2) is the forward equation
`π_t = a β E_t π_{t+1} + a (κ x* + u_t)` with `a = λ/(λ + κ²)`. -/
theorem solves22_iff {β κ lam xs : ℝ} (hlam : 0 < lam) (u π : ℕ → Ω → ℝ) :
    Solves22 𝔼 β κ lam xs u π ↔
      ∀ t, π t = (lam / (lam + κ ^ 2) * β) • 𝔼.E t (π (t + 1)) +
        forcing22 (lam / (lam + κ ^ 2)) κ xs u t := by
  rw [Solves22, coeff_eq hlam]
  constructor
  · intro h t
    funext ω
    rw [h t ω]
    simp only [forcing22, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h t ω
    rw [h t]
    simp only [forcing22, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Woodford (2003), p. 487: the forcing term of (2.2) is bounded when `u` is. -/
theorem forcing22_bounded {a κ xs M : ℝ} {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) :
    ∀ t ω, |forcing22 a κ xs u t ω| ≤ |a| * (|κ * xs| + M) := by
  intro t ω
  simp only [forcing22]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith [hu t ω]))
    (abs_nonneg a)

/-- Woodford (2003), p. 487: the forcing term of (2.2) is adapted when `u` is. -/
theorem forcing22_E {a κ xs : ℝ} (u : ℕ → Ω → ℝ) (s t : ℕ) :
    𝔼.E s (forcing22 a κ xs u t) = fun ω => a * (κ * xs + 𝔼.E s (u t) ω) := by
  have h : forcing22 a κ xs u t = (fun _ => a * (κ * xs)) + a • u t := by
    funext ω
    simp only [forcing22, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, map_add, map_smul, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (2.3), p. 487: the forward series of (2.2) is exactly (2.3). The
constant collects to `a κ x*/(1 − a β) = κλ x*/((1 − β)λ + κ²)` and the shock weights are
`(aβ)ʲ a = βʲ (λ/(λ + κ²))^{j+1}`. -/
theorem forwardSeries_eq_infl23 {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) :
    𝔼.forwardSeries (lam / (lam + κ ^ 2) * β) (forcing22 (lam / (lam + κ ^ 2)) κ xs u) t =
      infl23 𝔼 β κ lam xs u t := by
  set a := lam / (lam + κ ^ 2) with ha
  have hK : 0 < lam + κ ^ 2 := by positivity
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  rw [← ha] at hab0 hab1
  have ha0 : 0 ≤ a := by positivity
  funext ω
  simp only [ExpectationSystem.forwardSeries, infl23]
  rw [← ha]
  have hterm : ∀ k : ℕ, (a * β) ^ k * 𝔼.E t (forcing22 a κ xs u (t + k)) ω =
      (a * β) ^ k * (a * κ * xs) + β ^ k * a ^ (k + 1) * 𝔼.E t (u (t + k)) ω := by
    intro k
    rw [forcing22_E]
    ring
  simp_rw [hterm]
  have hs1 : Summable (fun k : ℕ => (a * β) ^ k * (a * κ * xs)) :=
    (summable_geometric_of_lt_one hab0 hab1).mul_right _
  have hs2 : Summable (fun k : ℕ => β ^ k * a ^ (k + 1) * 𝔼.E t (u (t + k)) ω) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hab0 hab1).mul_right (a * M)) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hβ0,
      abs_of_nonneg ha0]
    have hE := 𝔼.abs_E_le (hu (t + k)) t ω
    have heq : (a * β) ^ k * (a * M) = β ^ k * a ^ (k + 1) * M := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  rw [hs1.tsum_add hs2, tsum_mul_right, tsum_geometric_of_lt_one hab0 hab1]
  congr 1
  have h1 : 1 - a * β ≠ 0 := by linarith
  have h2 : (1 - β) * lam + κ ^ 2 ≠ 0 := by nlinarith [sq_nonneg κ]
  rw [ha]
  field_simp
  ring

/-- Woodford (2003), eq. (2.3), p. 487: (2.3) is bounded. -/
theorem infl23_bounded {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (infl23 𝔼 β κ lam xs u) := by
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  have h := 𝔼.forwardSeries_bounded hab0 hab1
    (forcing22_bounded (a := lam / (lam + κ ^ 2)) (κ := κ) (xs := xs) hu)
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun t ω => by rw [← forwardSeries_eq_infl23 𝔼 hβ0 hβ1 hlam hu]; exact hB t ω⟩

/-- Woodford (2003), eq. (2.3), p. 487: (2.3) is adapted. -/
theorem infl23_adapted {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (infl23 𝔼 β κ lam xs u) := by
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  intro t
  rw [← forwardSeries_eq_infl23 𝔼 hβ0 hβ1 hlam hu]
  exact 𝔼.forwardSeries_adapted hab0 hab1
    (forcing22_bounded (a := lam / (lam + κ ^ 2)) (κ := κ) (xs := xs) hu) t

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 487: (2.3) solves (2.2). -/
theorem infl23_solves22 {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    Solves22 𝔼 β κ lam xs u (infl23 𝔼 β κ lam xs u) := by
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  rw [solves22_iff 𝔼 hlam]
  have hfa : 𝔼.Adapted (forcing22 (lam / (lam + κ ^ 2)) κ xs u) := by
    intro t
    rw [forcing22_E]
    funext ω
    rw [hua t]
    rfl
  intro t
  have h := 𝔼.forwardSeries_solves hab0 hab1
    (forcing22_bounded (a := lam / (lam + κ ^ 2)) (κ := κ) (xs := xs) hu) hfa t
  simp only [forwardSeries_eq_infl23 𝔼 hβ0 hβ1 hlam hu] at h
  exact h

/-- Woodford (2003), p. 487 (Proposition 7.5, uniqueness): (2.3) is the **unique bounded
solution** of (2.2), because (2.2) is a forward equation with coefficient
`βλ/(λ + κ²) < 1` (forward iteration / contraction). -/
theorem eq_infl23_of_solves22 {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    {u π : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (hπ : Solves22 𝔼 β κ lam xs u π) (hπb : BoundedProc π) :
    π = infl23 𝔼 β κ lam xs u := by
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  have hfa : 𝔼.Adapted (forcing22 (lam / (lam + κ ^ 2)) κ xs u) := by
    intro t
    rw [forcing22_E]
    funext ω
    rw [hua t]
    rfl
  rw [solves22_iff 𝔼 hlam] at hπ
  have h := 𝔼.eq_forwardSeries hab0 hab1
    (forcing22_bounded (a := lam / (lam + κ ^ 2)) (κ := κ) (xs := xs) hu) hfa hπ hπb
  rw [h]
  funext t
  exact forwardSeries_eq_infl23 𝔼 hβ0 hβ1 hlam hu t

/-- Woodford (2003), p. 487: in a discretionary equilibrium the pair satisfies (1.4) and (2.1)
in every state, hence (2.2). -/
theorem solves22_of_discretionEq {β κ lam xs : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    {u π x : ℕ → Ω → ℝ} (h : DiscretionEq 𝔼 β κ lam xs u π x) :
    Solves22 𝔼 β κ lam xs u π ∧ ∀ t ω, x t ω = xs - κ / lam * π t ω := by
  obtain ⟨-, -, -, -, h⟩ := h
  have hb : ∀ t ω, π t ω = (1 + κ ^ 2 / lam)⁻¹ *
      (κ * xs + u t ω + β * 𝔼.E t (π (t + 1)) ω) ∧ x t ω = xs - κ / lam * π t ω := by
    intro t ω
    obtain ⟨hmem, hmin⟩ := h t ω
    have hfoc := (isMinOn_iff_foc hκ hlam hmem).mp hmin
    exact (foc_as_iff hκ hlam).mp ⟨hmem, hfoc⟩
  exact ⟨fun t ω => (hb t ω).1, fun t ω => (hb t ω).2⟩

/-- Woodford (2003), **Proposition 7.5**, p. 487, existence: the pair ((2.3), `x* − (κ/λ)·(2.3)`)
is a discretionary equilibrium for every bounded adapted cost-push process. -/
theorem discretionEq_infl23 {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    DiscretionEq 𝔼 β κ lam xs u (infl23 𝔼 β κ lam xs u) (gap23 𝔼 β κ lam xs u) := by
  have had := infl23_adapted 𝔼 (xs := xs) (κ := κ) hβ0 hβ1 hlam hu
  obtain ⟨B, hB⟩ := infl23_bounded 𝔼 (xs := xs) (κ := κ) hβ0 hβ1 hlam hu
  have hsol := infl23_solves22 𝔼 (xs := xs) (κ := κ) hβ0 hβ1 hlam hu hua
  refine ⟨had, ?_, ⟨B, hB⟩, ⟨|xs| + |κ / lam| * B, ?_⟩, ?_⟩
  · intro t
    have h : gap23 𝔼 β κ lam xs u t =
        (fun _ => xs) + (-(κ / lam)) • infl23 𝔼 β κ lam xs u t := by
      funext ω
      simp only [gap23, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, map_add, map_smul, 𝔼.const, had t]
  · intro t ω
    simp only [gap23]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hB t ω
  · intro t ω
    have hboth := (foc_as_iff (β := β) (e := 𝔼.E t (infl23 𝔼 β κ lam xs u (t + 1)) ω)
      (v := u t ω) (xs := xs) (p := infl23 𝔼 β κ lam xs u t ω)
      (y := gap23 𝔼 β κ lam xs u t ω) hκ hlam).mpr ⟨hsol t ω, rfl⟩
    exact ⟨hboth.1, (isMinOn_iff_foc hκ hlam hboth.1).mpr hboth.2⟩

/-- Woodford (2003), **Proposition 7.5**, p. 487, in its exact linear-quadratic form: for a
bounded adapted cost-push process, a pair `(π, x)` is a discretionary equilibrium **if and only
if** inflation is the Markov process (2.3) and `x_t = x* − (κ/λ) π_t`. In particular the
discretionary equilibrium exists and is unique. -/
theorem prop_7_5 {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (π x : ℕ → Ω → ℝ) :
    DiscretionEq 𝔼 β κ lam xs u π x ↔
      π = infl23 𝔼 β κ lam xs u ∧ x = gap23 𝔼 β κ lam xs u := by
  constructor
  · intro h
    have hb := h.2.2.1
    obtain ⟨hsol, hx⟩ := solves22_of_discretionEq 𝔼 hκ hlam h
    have hπ := eq_infl23_of_solves22 𝔼 hβ0 hβ1 hlam hu hua hsol hb
    refine ⟨hπ, ?_⟩
    funext t ω
    rw [hx t ω, hπ]
    rfl
  · rintro ⟨rfl, rfl⟩
    exact discretionEq_infl23 𝔼 hβ0 hβ1 hκ hlam hu hua

/-- Woodford (2003), **Proposition 7.5**, p. 487: there is exactly one discretionary
equilibrium. -/
theorem existsUnique_discretionEq {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), DiscretionEq 𝔼 β κ lam xs u p.1 p.2 := by
  refine ⟨(infl23 𝔼 β κ lam xs u, gap23 𝔼 β κ lam xs u),
    discretionEq_infl23 𝔼 hβ0 hβ1 hκ hlam hu hua, ?_⟩
  rintro ⟨π, x⟩ h
  obtain ⟨h1, h2⟩ := (prop_7_5 𝔼 hβ0 hβ1 hκ hlam hu hua π x).mp h
  rw [h1, h2]

/-- Woodford (2003), p. 487: "the corresponding Markov solution for output can be obtained by
substituting this solution for inflation into (2.1)": in the discretionary equilibrium
`κ x_t = π_t − β E_t π_{t+1} − u_t`. -/
theorem gap23_from_as {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (t : ℕ) (ω : Ω) :
    κ * gap23 𝔼 β κ lam xs u t ω = infl23 𝔼 β κ lam xs u t ω -
      β * 𝔼.E t (infl23 𝔼 β κ lam xs u (t + 1)) ω - u t ω := by
  have h := ((discretionEq_infl23 𝔼 (xs := xs) hβ0 hβ1 hκ hlam hu hua).2.2.2.2 t ω).1
  simp only [staticSet, Set.mem_ofPred_eq] at h
  linarith

/-! ### Markov shocks -/

/-- Woodford (2003), p. 487: if the cost-push shock is a (time-homogeneous) Markov process
whose value is revealed in period `t`, i.e. `E_t u_{t+j} = G_j(u_t)` for some functions `G_j`,
then equilibrium inflation and output depend **only on the current disturbance** `u_t`. -/
theorem markov_dependence {β κ lam xs M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (G : ℕ → ℝ → ℝ) (hG : ∀ t j ω, 𝔼.E t (u (t + j)) ω = G j (u t ω)) {π x : ℕ → Ω → ℝ}
    (h : DiscretionEq 𝔼 β κ lam xs u π x) :
    ∃ fπ fx : ℝ → ℝ, ∀ t ω, π t ω = fπ (u t ω) ∧ x t ω = fx (u t ω) := by
  obtain ⟨rfl, rfl⟩ := (prop_7_5 𝔼 hβ0 hβ1 hκ hlam hu hua π x).mp h
  set fπ : ℝ → ℝ := fun v => κ * lam / ((1 - β) * lam + κ ^ 2) * xs +
    ∑' j : ℕ, β ^ j * (lam / (lam + κ ^ 2)) ^ (j + 1) * G j v with hfπ
  have hπ : ∀ t ω, infl23 𝔼 β κ lam xs u t ω = fπ (u t ω) := by
    intro t ω
    simp only [infl23, hfπ, hG]
  refine ⟨fπ, fun v => xs - κ / lam * fπ v, fun t ω => ⟨hπ t ω, ?_⟩⟩
  simp only [gap23, hπ]

/-- Woodford (2003), p. 487, AR(1) case: if `E_t u_{t+1} = ρ u_t` with `|ρ| ≤ 1`, then
`π_t = κλ x*/((1 − β)λ + κ²) + a/(1 − aβρ) · u_t` with `a = λ/(λ + κ²)`, a function of `u_t`
alone. -/
theorem ar1_closed_form {β κ lam xs ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) (ω : Ω) :
    infl23 𝔼 β κ lam xs u t ω = κ * lam / ((1 - β) * lam + κ ^ 2) * xs +
      lam / (lam + κ ^ 2) / (1 - lam / (lam + κ ^ 2) * β * ρ) * u t ω := by
  set a := lam / (lam + κ ^ 2) with ha
  obtain ⟨hab0, hab1⟩ := coeff_lt_one (κ := κ) hβ0 hβ1 hlam
  rw [← ha] at hab0 hab1
  have hq : |a * β * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg hab0]
    calc a * β * |ρ| ≤ a * β * 1 := mul_le_mul_of_nonneg_left hρ hab0
      _ < 1 := by linarith
  simp only [infl23]
  rw [← ha]
  congr 1
  have hterm : ∀ j : ℕ, β ^ j * a ^ (j + 1) * 𝔼.E t (u (t + j)) ω =
      a * u t ω * (a * β * ρ) ^ j := by
    intro j
    rw [𝔼.ar1_iterate hu t j]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hq]
  ring

/-- Woodford (2003), p. 487: with an AR(1) shock the effects of a disturbance on inflation are
only as persistent as the disturbance itself: `E_t π_{t+k} − π̄ = ρᵏ (π_t − π̄)` where `π̄` is
the constant term of (2.3). -/
theorem ar1_persistence {β κ lam xs ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t k : ℕ) (ω : Ω) :
    𝔼.E t (infl23 𝔼 β κ lam xs u (t + k)) ω - κ * lam / ((1 - β) * lam + κ ^ 2) * xs =
      ρ ^ k * (infl23 𝔼 β κ lam xs u t ω - κ * lam / ((1 - β) * lam + κ ^ 2) * xs) := by
  set c := κ * lam / ((1 - β) * lam + κ ^ 2) * xs with hc
  set b := lam / (lam + κ ^ 2) / (1 - lam / (lam + κ ^ 2) * β * ρ) with hb
  have hform : infl23 𝔼 β κ lam xs u (t + k) = (fun _ => c) + b • u (t + k) := by
    funext ω'
    rw [ar1_closed_form 𝔼 hβ0 hβ1 hlam hρ hu]
    rfl
  rw [hform, map_add, map_smul, 𝔼.const, 𝔼.ar1_iterate hu t k,
    ar1_closed_form 𝔼 hβ0 hβ1 hlam hρ hu]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hc, ← hb]
  ring

/-- Woodford (2003), p. 487: with no cost-push shocks (2.3) is the constant
`κλ x*/((1 − β)λ + κ²)`. -/
theorem infl23_zero_shock (β κ lam xs : ℝ) (t : ℕ) (ω : Ω) :
    infl23 𝔼 β κ lam xs (fun _ _ => 0) t ω = κ * lam / ((1 - β) * lam + κ ^ 2) * xs := by
  simp only [infl23]
  have h : 𝔼.E t (fun _ => (0 : ℝ)) = fun _ => 0 := 𝔼.const t 0
  simp [h]

/-- Woodford (2003), p. 487 with (1.5)–(1.6), p. 471: the constant term of (2.3) (the long-run
average inflation rate under discretion) is the deterministic discretionary inflation rate
(1.6). It is the unique fixed point `πᵉ = (1 + κ²/λ)⁻¹ (κ x* + β πᵉ)` of (1.5). -/
theorem infl23_const_eq_bias {β κ lam xs : ℝ} (hβ1 : β < 1) (hlam : 0 < lam) (pe : ℝ) :
    pe = (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + β * pe) ↔
      pe = κ * lam / ((1 - β) * lam + κ ^ 2) * xs := by
  have hK : 0 < lam + κ ^ 2 := by positivity
  have hD : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  rw [coeff_eq hlam]
  have key1 : pe = lam / (lam + κ ^ 2) * (κ * xs + β * pe) ↔
      pe * ((1 - β) * lam + κ ^ 2) = κ * lam * xs := by
    rw [div_mul_eq_mul_div, eq_div_iff hK.ne']
    constructor <;> intro h <;> linarith
  have key2 : pe = κ * lam / ((1 - β) * lam + κ ^ 2) * xs ↔
      pe * ((1 - β) * lam + κ ^ 2) = κ * lam * xs := by
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
  rw [key1, key2]

end Woodford.GainsFromCommitment.Discretion
