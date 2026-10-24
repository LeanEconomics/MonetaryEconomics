/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.SecondOrderRE
import GainsFromCommitment.LQSufficiency
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The optimal commitment from the standpoint of date zero

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1, eqs. (1.1)–(1.2) and (1.7)–(1.13),
pp. 469–474.

The problem: minimise (1.2) `∑ βᵗ [π_t² + λ(x_t − x*)²]` over bounded paths satisfying the
aggregate-supply relation (1.1) `π_t = κx_t + βE_tπ_{t+1}` for all `t ≥ 0`. Everything is stated
for an arbitrary `ExpectationSystem` (with the pull-out property for the optimality theorems); the
deterministic problem of the book is the perfect-foresight case, restated for sequences.

## Main results

* `hasDerivAt_lagrangian_pi`, `hasDerivAt_lagrangian_x`, `stationary_iff_foc`: the partial
  derivatives of the Lagrangian of p. 472 are `βᵗ(π_t + φ_t − φ_{t−1})` and
  `βᵗ(λ(x_t − x*) − κφ_t)` with `φ_{−1} = 0`, so stationarity is exactly (1.7)–(1.9).
* `as_iff_multiplier` (1.10): given (1.7)–(1.8), the AS relation is equivalent to
  `βE_tφ_{t+1} − (1 + β + κ²/λ)φ_t + φ_{t−1} = κx*`.
* `multPath_zero` (1.12), `inflPath_zero` (1.13), `gapPath_zero`; `foc_system_unique`: the
  system (1.1), (1.7)–(1.9) has exactly one bounded adapted solution (for any initial multiplier,
  which `Timeless` reuses).
* `plan_optimal`, `dateZero_optimal`: the path (1.13) minimises the expected loss, state by
  state, among all bounded adapted paths satisfying (1.1) (via `LQSufficiency`), and is the unique
  minimiser; `isDateZeroOptimal_iff`: the deterministic statement.
* `loss_identity` (p. 473, survey E1): for bounded paths satisfying (1.1),
  `(1.2) = ∑ βᵗ(π_t² + λx_t²) − 2(λ/κ)x*π_0 + λx*²/(1 − β)`; `loss_identity_book`: with
  `λ = κ/θ` the initial term is the book's `−2(x*/θ)π_0`; `zero_minimises_loss0`: the remaining
  terms are minimised by zero inflation whatever `x*` is.
* `time_inconsistent`: for `x* ≠ 0` the date-0 plan, continued from date 1, is not the date-1
  optimal plan; it is feasible but strictly worse.
-/

namespace Woodford.GainsFromCommitment.DateZeroCommitment

open Filter Topology

/-! ### The Lagrangian and its partial derivatives (deterministic, p. 472) -/

/-- Woodford (2003), p. 472: the date-`t` term of the Lagrangian
`βᵗ [½(π_t² + λ(x_t − x*)²) + φ_t(π_t − κx_t − βπ_{t+1})]`. -/
noncomputable def lagTerm (β κ lam xs : ℝ) (φ π x : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * ((π t ^ 2 + lam * (x t - xs) ^ 2) / 2 + φ t * (π t - κ * x t - β * π (t + 1)))

/-- Woodford (2003), p. 472: the Lagrangian `ℒ = ∑_{t ≥ 0} βᵗ [½(π_t² + λ(x_t − x*)²) +
φ_t(π_t − κx_t − βπ_{t+1})]`. -/
noncomputable def lagrangian (β κ lam xs : ℝ) (φ π x : ℕ → ℝ) : ℝ :=
  ∑' t, lagTerm β κ lam xs φ π x t

/-- Woodford (2003), p. 472: the sequence `s` with its date-`n` entry moved by `h`. -/
def bump (n : ℕ) (h : ℝ) (s : ℕ → ℝ) : ℕ → ℝ := fun t => if t = n then s t + h else s t

/-- Woodford (2003), p. 472: for bounded paths and multipliers the Lagrangian series converges. -/
theorem lagTerm_summable {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M) :
    Summable (lagTerm β κ lam xs φ π x) := by
  obtain ⟨A, hA⟩ := hφ
  obtain ⟨B, hB⟩ := hπ
  obtain ⟨C, hC⟩ := hx
  set K := (B ^ 2 + |lam| * (C + |xs|) ^ 2) / 2 + A * (B + |κ| * C + β * B) with hK
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    (fun t => ?_)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [Real.norm_eq_abs, lagTerm, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have h1 : |π t ^ 2| ≤ B ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have h2 : |(x t - xs) ^ 2| ≤ (C + |xs|) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hC t) le_rfl)) 2
  have h3 : |π t - κ * x t - β * π (t + 1)| ≤ B + |κ| * C + β * B := by
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hB t) ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul_of_nonneg_left (hB (t + 1)) hβ0
  calc |(π t ^ 2 + lam * (x t - xs) ^ 2) / 2 + φ t * (π t - κ * x t - β * π (t + 1))|
      ≤ (|π t ^ 2| + |lam| * |(x t - xs) ^ 2|) / 2 + |φ t| * |π t - κ * x t - β * π (t + 1)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (abs_mul _ _).le)
        rw [abs_div, abs_two]
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_mul])
    _ ≤ K := by
        rw [hK]
        gcongr
        · exact hA t

/-- Woodford (2003), p. 472: moving `π_n` by `h` changes the Lagrangian by
`βⁿ(π_n h + h²/2 + φ_n h) − βⁿ φ_{n−1} h` (with `φ_{−1} = 0`). -/
theorem lagrangian_bump_pi {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M)
    (n : ℕ) (h : ℝ) :
    lagrangian β κ lam xs φ (bump n h π) x = lagrangian β κ lam xs φ π x +
      β ^ n * (π n * h + h ^ 2 / 2 + φ n * h - Sequences.lagged 0 φ n * h) := by
  have hb : ∃ M, ∀ t, |bump n h π t| ≤ M := by
    obtain ⟨B, hB⟩ := hπ
    refine ⟨B + |h|, fun t => ?_⟩
    unfold bump
    split_ifs
    · exact (abs_add_le _ _).trans (add_le_add (hB t) le_rfl)
    · exact (hB t).trans (by linarith [abs_nonneg h])
  set A := β ^ n * (π n * h + h ^ 2 / 2 + φ n * h) with hA
  set D : ℕ → ℝ := fun t => (if t = n then A else 0) +
    (if t + 1 = n then -(β ^ (t + 1) * φ t * h) else 0) with hD
  have hdiff : ∀ t, lagTerm β κ lam xs φ (bump n h π) x t = lagTerm β κ lam xs φ π x t + D t := by
    intro t
    simp only [hD, lagTerm, bump]
    by_cases h1 : t = n
    · subst h1
      have h2 : ¬ t + 1 = t := by omega
      simp only [h2, ↓reduceIte, hA]
      ring
    · by_cases h3 : t + 1 = n
      · subst h3
        simp only [h1, ↓reduceIte]
        ring
      · simp only [h1, h3, ↓reduceIte]
        ring
  have hDsum : HasSum D (A - β ^ n * Sequences.lagged 0 φ n * h) := by
    have hs1 : HasSum (fun t => if t = n then A else 0) A := hasSum_ite_eq n A
    cases n with
    | zero =>
      have hD0 : D = fun t => if t = 0 then A else 0 := by
        funext t
        simp only [hD]
        have : ¬ t + 1 = 0 := by omega
        simp only [this, ↓reduceIte, add_zero]
      rw [hD0, Sequences.lagged_zero, mul_zero, zero_mul, sub_zero]
      exact hs1
    | succ m =>
      have hs2 : HasSum (fun t : ℕ => if t + 1 = m + 1 then -(β ^ (t + 1) * φ t * h) else 0)
          (-(β ^ (m + 1) * φ m * h)) := by
        convert hasSum_ite_eq m (-(β ^ (m + 1) * φ m * h)) using 1
        funext t
        by_cases ht : t = m
        · subst ht; simp
        · have : ¬ t + 1 = m + 1 := by omega
          simp only [this, ht, ↓reduceIte]
      convert hs1.add hs2 using 1
      simp only [Sequences.lagged_succ]
      ring
  have hsum := (lagTerm_summable (κ := κ) (lam := lam) (xs := xs) hβ0 hβ1 hφ hb hx).hasSum
  have hsum0 := (lagTerm_summable (κ := κ) (lam := lam) (xs := xs) hβ0 hβ1 hφ hπ hx).hasSum.add
    hDsum
  have heq : (fun t => lagTerm β κ lam xs φ (bump n h π) x t) =
      fun t => lagTerm β κ lam xs φ π x t + D t := funext hdiff
  rw [← heq] at hsum0
  rw [lagrangian, hsum0.tsum_eq, lagrangian, hA]
  ring

/-- Woodford (2003), p. 472: moving `x_n` by `h` changes the Lagrangian by
`βⁿ(λ(x_n − x*)h + λh²/2 − κφ_n h)`. -/
theorem lagrangian_bump_x {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M)
    (n : ℕ) (h : ℝ) :
    lagrangian β κ lam xs φ π (bump n h x) = lagrangian β κ lam xs φ π x +
      β ^ n * (lam * (x n - xs) * h + lam * h ^ 2 / 2 - κ * φ n * h) := by
  have hb : ∃ M, ∀ t, |bump n h x t| ≤ M := by
    obtain ⟨B, hB⟩ := hx
    refine ⟨B + |h|, fun t => ?_⟩
    unfold bump
    split_ifs
    · exact (abs_add_le _ _).trans (add_le_add (hB t) le_rfl)
    · exact (hB t).trans (by linarith [abs_nonneg h])
  set A := β ^ n * (lam * (x n - xs) * h + lam * h ^ 2 / 2 - κ * φ n * h) with hA
  have hdiff : ∀ t, lagTerm β κ lam xs φ π (bump n h x) t =
      lagTerm β κ lam xs φ π x t + (if t = n then A else 0) := by
    intro t
    simp only [lagTerm, bump]
    by_cases h1 : t = n
    · subst h1
      simp only [↓reduceIte, hA]
      ring
    · simp only [h1, ↓reduceIte]
      ring
  have hsum0 := (lagTerm_summable (κ := κ) (lam := lam) (xs := xs) hβ0 hβ1 hφ hπ hx).hasSum.add
    (hasSum_ite_eq n A)
  have heq : (fun t => lagTerm β κ lam xs φ π (bump n h x) t) =
      fun t => lagTerm β κ lam xs φ π x t + (if t = n then A else 0) := funext hdiff
  rw [← heq] at hsum0
  rw [lagrangian, hsum0.tsum_eq, lagrangian]

/-- Woodford (2003), p. 472 ("differentiation of the Lagrangian with respect to each of its
arguments"): `∂ℒ/∂π_n = βⁿ(π_n + φ_n − φ_{n−1})` with `φ_{−1} = 0`, the left side of (1.7). -/
theorem hasDerivAt_lagrangian_pi {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M) (n : ℕ) :
    HasDerivAt (fun h => lagrangian β κ lam xs φ (bump n h π) x)
      (β ^ n * (π n + φ n - Sequences.lagged 0 φ n)) 0 := by
  have e : (fun h => lagrangian β κ lam xs φ (bump n h π) x) = fun h =>
      lagrangian β κ lam xs φ π x +
        β ^ n * ((π n + φ n - Sequences.lagged 0 φ n) * h + h ^ 2 / 2) := by
    funext h
    rw [lagrangian_bump_pi hβ0 hβ1 hφ hπ hx n h]
    ring
  rw [e]
  have hd : HasDerivAt (fun h : ℝ => (π n + φ n - Sequences.lagged 0 φ n) * h + h ^ 2 / 2)
      ((π n + φ n - Sequences.lagged 0 φ n) * 1 + (2 : ℝ) * 0 ^ (2 - 1) / 2) 0 :=
    HasDerivAt.add ((hasDerivAt_id 0).const_mul _) ((hasDerivAt_pow 2 0).div_const 2)
  have := (hd.const_mul (β ^ n)).const_add (lagrangian β κ lam xs φ π x)
  simpa using this

/-- Woodford (2003), p. 472: `∂ℒ/∂x_n = βⁿ(λ(x_n − x*) − κφ_n)`, the left side of (1.8). -/
theorem hasDerivAt_lagrangian_x {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M) (n : ℕ) :
    HasDerivAt (fun h => lagrangian β κ lam xs φ π (bump n h x))
      (β ^ n * (lam * (x n - xs) - κ * φ n)) 0 := by
  have e : (fun h => lagrangian β κ lam xs φ π (bump n h x)) = fun h =>
      lagrangian β κ lam xs φ π x + β ^ n * ((lam * (x n - xs) - κ * φ n) * h + lam * (h ^ 2 / 2))
      := by
    funext h
    rw [lagrangian_bump_x hβ0 hβ1 hφ hπ hx n h]
    ring
  rw [e]
  have hd : HasDerivAt (fun h : ℝ => (lam * (x n - xs) - κ * φ n) * h + lam * (h ^ 2 / 2))
      ((lam * (x n - xs) - κ * φ n) * 1 + lam * ((2 : ℝ) * 0 ^ (2 - 1) / 2)) 0 :=
    HasDerivAt.add ((hasDerivAt_id 0).const_mul _) (((hasDerivAt_pow 2 0).div_const 2).const_mul _)
  have := (hd.const_mul (β ^ n)).const_add (lagrangian β κ lam xs φ π x)
  simpa using this

/-- Woodford (2003), (1.7)–(1.9), p. 472 (deterministic): the first-order conditions
`π_t + φ_t − φ_{t−1} = 0` and `λ(x_t − x*) − κφ_t = 0` for all `t ≥ 0`, with `φ_{−1} = 0`. -/
def DetFOC (κ lam xs : ℝ) (π x φ : ℕ → ℝ) : Prop :=
  ∀ t, π t + φ t - Sequences.lagged 0 φ t = 0 ∧ lam * (x t - xs) - κ * φ t = 0

/-- Woodford (2003), (1.7)–(1.9), p. 472: the Lagrangian is stationary in every `π_n` and `x_n`
(all partial derivatives vanish) iff the first-order conditions (1.7)–(1.8) hold with
`φ_{−1} = 0`. -/
theorem stationary_iff_foc {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {φ π x : ℕ → ℝ}
    (hφ : ∃ M, ∀ t, |φ t| ≤ M) (hπ : ∃ M, ∀ t, |π t| ≤ M) (hx : ∃ M, ∀ t, |x t| ≤ M) :
    (∀ n, deriv (fun h => lagrangian β κ lam xs φ (bump n h π) x) 0 = 0 ∧
      deriv (fun h => lagrangian β κ lam xs φ π (bump n h x)) 0 = 0) ↔ DetFOC κ lam xs π x φ := by
  refine forall_congr' fun n => ?_
  rw [(hasDerivAt_lagrangian_pi hβ0.le hβ1 hφ hπ hx n).deriv,
    (hasDerivAt_lagrangian_x hβ0.le hβ1 hφ hπ hx n).deriv]
  have hb : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
  simp only [mul_eq_zero, hb, false_or]

/-! ### The stochastic model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (1.1), p. 469 (and (2.1), p. 487, without disturbances): the
aggregate-supply relation `π_t = κx_t + βE_tπ_{t+1}` for all `t ≥ 0`. -/
def AS (β κ : ℝ) (π x : ℕ → Ω → ℝ) : Prop := ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), pp. 469, 472: an admissible path: bounded and adapted, satisfying (1.1). -/
def Admissible (β κ : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 β κ π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Woodford (2003), eq. (1.2), p. 469: the expected discounted loss
`E_0 ∑_{t ≥ 0} βᵗ [π_t² + λ(x_t − x*)²]`. -/
noncomputable def loss (β lam xs : ℝ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, β ^ t * (π t ω ^ 2 + lam * (x t ω - xs) ^ 2))

/-- Woodford (2003), (1.7)–(1.8), p. 472, with initial multiplier `φ_{−1} = φm` ((1.9) is
`φm = 0`): `π_t + φ_t − φ_{t−1} = 0` and `λ(x_t − x*) − κφ_t = 0` for all `t ≥ 0`. -/
def FOC (κ lam xs φm : ℝ) (π x φ : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + φ t ω - Sequences.lagged (fun _ => φm) φ t ω = 0 ∧
    lam * (x t ω - xs) - κ * φ t ω = 0

/-- Woodford (2003), eq. (1.10), p. 472: given the first-order conditions (1.7)–(1.8) with an
adapted multiplier, the AS relation (1.1) holds iff the multiplier solves
`βE_tφ_{t+1} − (1 + β + κ²/λ)φ_t + φ_{t−1} = κx*` with `φ_{−1} = φm`. -/
theorem as_iff_multiplier {β κ lam xs φm : ℝ} (hlam : lam ≠ 0) {π x φ : ℕ → Ω → ℝ}
    (hfoc : FOC κ lam xs φm π x φ) (hφa : 𝔼.Adapted φ) :
    AS 𝔼 β κ π x ↔ SecondOrderRE.SecondOrderEq 𝔼 β (κ ^ 2 / lam) (fun _ _ => κ * xs)
      (fun _ => φm) φ := by
  have hπ1 : ∀ t, π (t + 1) = φ t - φ (t + 1) := fun t => by
    funext ω
    have := (hfoc (t + 1) ω).1
    simp only [Sequences.lagged_succ] at this
    simp only [Pi.sub_apply]
    linarith
  refine forall_congr' fun t => ?_
  rw [hπ1 t, map_sub, hφa t, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  have h1 := (hfoc t ω).1
  have h2 := (hfoc t ω).2
  have hx : x t ω = xs + κ / lam * φ t ω := by field_simp; linarith
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx, show π t ω = Sequences.lagged (fun _ => φm) φ t ω - φ t ω by linarith]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-! ### The solution (1.12)–(1.13), for an arbitrary initial multiplier -/

/-- Woodford (2003), eq. (1.12), p. 473 (general initial multiplier `φ_{−1} = φm`): the multiplier
path `φ_t = −(λ/κ)x* + μ₁^{t+1}(φm + (λ/κ)x*)`, the bounded solution of (1.10). -/
noncomputable def multPath (β κ lam xs φm : ℝ) (t : ℕ) : ℝ :=
  -(lam / κ * xs) + SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) * (φm + lam / κ * xs)

/-- Woodford (2003), eq. (1.13), p. 473 (general initial multiplier): inflation
`π_t = φ_{t−1} − φ_t`. -/
noncomputable def inflPath (β κ lam xs φm : ℝ) (t : ℕ) : ℝ :=
  Sequences.lagged φm (multPath β κ lam xs φm) t - multPath β κ lam xs φm t

/-- Woodford (2003), eq. (1.8), p. 472 (general initial multiplier): the output gap
`x_t = x* + (κ/λ)φ_t`. -/
noncomputable def gapPath (β κ lam xs φm : ℝ) (t : ℕ) : ℝ :=
  xs + κ / lam * multPath β κ lam xs φm t

/-- Woodford (2003), eq. (1.13), p. 473: `π_t = (1 − μ₁)μ₁ᵗ(φm + (λ/κ)x*)`. -/
theorem inflPath_eq (β κ lam xs φm : ℝ) (t : ℕ) :
    inflPath β κ lam xs φm t = (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) *
      SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ t * (φm + lam / κ * xs) := by
  cases t with
  | zero => simp only [inflPath, Sequences.lagged_zero, multPath]; ring
  | succ t => simp only [inflPath, Sequences.lagged_succ, multPath]; ring

/-- Woodford (2003), eq. (1.8), p. 472: `x_t = (κ/λ)μ₁^{t+1}(φm + (λ/κ)x*)`. -/
theorem gapPath_eq {β κ lam xs φm : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (t : ℕ) :
    gapPath β κ lam xs φm t =
      κ / lam * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) * (φm + lam / κ * xs) := by
  unfold gapPath multPath
  field_simp
  ring

/-- **Woodford (2003), eq. (1.12), p. 473**: with `φ_{−1} = 0`,
`φ_t = −(λ/κ)x*(1 − μ₁^{t+1})`. -/
theorem multPath_zero (β κ lam xs : ℝ) (t : ℕ) :
    multPath β κ lam xs 0 t =
      -(lam / κ) * xs * (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1)) := by
  unfold multPath; ring

/-- **Woodford (2003), eq. (1.13), p. 473**: with `φ_{−1} = 0`,
`π_t = (1 − μ₁)(λ/κ)x*μ₁ᵗ`. -/
theorem inflPath_zero (β κ lam xs : ℝ) (t : ℕ) :
    inflPath β κ lam xs 0 t = (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * (lam / κ) * xs *
      SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ t := by
  rw [inflPath_eq]; ring

/-- Woodford (2003), (1.8) and (1.12), p. 473: with `φ_{−1} = 0`, `x_t = x*μ₁^{t+1}`. -/
theorem gapPath_zero {β κ lam xs : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (t : ℕ) :
    gapPath β κ lam xs 0 t = xs * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) := by
  rw [gapPath_eq hκ hlam]; field_simp; ring

/-- Woodford (2003), (1.12), p. 473: the multiplier path is the constant-forcing solution of the
workhorse with forcing `κx*`. -/
theorem multPath_eq_constSol {β κ lam xs φm : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) :
    multPath β κ lam xs φm = SecondOrderRE.constSol β (κ ^ 2 / lam) (κ * xs) φm := by
  funext t
  unfold multPath SecondOrderRE.constSol
  have : κ * xs / (κ ^ 2 / lam) = lam / κ * xs := by field_simp
  rw [this, neg_div, this]

/-- Woodford (2003), (1.12)–(1.13), p. 473: the lift of a deterministic sequence to a process
(the same value in every state). -/
def lift (s : ℕ → ℝ) (t : ℕ) : Ω → ℝ := fun _ => s t

/-- **Woodford (2003), eq. (1.11), p. 472**: the characteristic equation
`βμ² − (1 + β + κ²/λ)μ + 1 = 0` has two real roots `0 < μ₁ < 1 < μ₂`, with `μ₁μ₂ = β⁻¹`. -/
theorem roots_1_11 {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) :
    SecondOrderRE.charPoly β (κ ^ 2 / lam) (SecondOrderRE.mu1 β (κ ^ 2 / lam)) = 0 ∧
      SecondOrderRE.charPoly β (κ ^ 2 / lam) (SecondOrderRE.mu2 β (κ ^ 2 / lam)) = 0 ∧
      0 < SecondOrderRE.mu1 β (κ ^ 2 / lam) ∧ SecondOrderRE.mu1 β (κ ^ 2 / lam) < 1 ∧
      1 < SecondOrderRE.mu2 β (κ ^ 2 / lam) ∧
      SecondOrderRE.mu1 β (κ ^ 2 / lam) * SecondOrderRE.mu2 β (κ ^ 2 / lam) = β⁻¹ := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  obtain ⟨r1, r2, r3⟩ := SecondOrderRE.root_location hβ hc
  exact ⟨SecondOrderRE.charPoly_mu1 hβ hc, SecondOrderRE.charPoly_mu2 hβ hc, r1, r2, r3,
    SecondOrderRE.mu1_mul_mu2 hβ hc⟩

/-- Woodford (2003), (1.7)–(1.8), p. 472: the paths (1.12)–(1.13) satisfy the first-order
conditions with the initial multiplier `φm`. -/
theorem plan_foc {β κ lam xs : ℝ} (hlam : lam ≠ 0) (φm : ℝ) :
    FOC κ lam xs φm (lift (inflPath β κ lam xs φm) : ℕ → Ω → ℝ) (lift (gapPath β κ lam xs φm))
      (lift (multPath β κ lam xs φm)) := by
  intro t ω
  refine ⟨?_, ?_⟩
  · cases t <;> simp [lift, inflPath]
  · simp only [lift, gapPath]; field_simp; ring

/-- Woodford (2003), (1.10)–(1.13), p. 473: the paths (1.12)–(1.13) satisfy the AS relation (1.1)
under any expectation system. -/
theorem plan_AS {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (φm : ℝ) :
    AS 𝔼 β κ (lift (inflPath β κ lam xs φm)) (lift (gapPath β κ lam xs φm)) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  refine (as_iff_multiplier 𝔼 hlam.ne' (plan_foc hlam.ne' φm) (fun t => 𝔼.const t _)).mpr ?_
  intro t
  rw [show lift (Ω := Ω) (multPath β κ lam xs φm) (t + 1) =
    fun _ => multPath β κ lam xs φm (t + 1) from rfl, 𝔼.const]
  funext ω
  have := SecondOrderRE.constSol_eq hβ hc (κ * xs) φm t
  rw [← multPath_eq_constSol hκ.ne' hlam.ne'] at this
  cases t <;> simpa [lift] using this

/-- Woodford (2003), p. 473: the paths (1.12)–(1.13) are bounded (`0 < μ₁ < 1`). -/
theorem plan_bounded {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (φm : ℝ) :
    BoundedProc (lift (inflPath β κ lam xs φm) : ℕ → Ω → ℝ) ∧
      BoundedProc (lift (gapPath β κ lam xs φm) : ℕ → Ω → ℝ) ∧
      BoundedProc (lift (multPath β κ lam xs φm) : ℕ → Ω → ℝ) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := SecondOrderRE.mu1_pos hβ hc
  have h1 := SecondOrderRE.mu1_lt_one hβ hc
  set μ := SecondOrderRE.mu1 β (κ ^ 2 / lam) with hμ
  set A := φm + lam / κ * xs with hA
  have hp : ∀ n : ℕ, |μ ^ n| ≤ 1 := fun n => by
    rw [abs_pow, abs_of_pos h0]; exact pow_le_one₀ h0.le h1.le
  refine ⟨⟨|1 - μ| * |A|, fun t _ => ?_⟩, ⟨|κ / lam| * |A|, fun t _ => ?_⟩,
    ⟨|lam / κ * xs| + |A|, fun t _ => ?_⟩⟩
  · simp only [lift, inflPath_eq, ← hμ, ← hA, abs_mul]
    calc |1 - μ| * |μ ^ t| * |A| ≤ |1 - μ| * 1 * |A| := by gcongr; exact hp t
      _ = |1 - μ| * |A| := by ring
  · simp only [lift, gapPath_eq hκ.ne' hlam.ne', ← hμ, ← hA, abs_mul]
    calc |κ / lam| * |μ ^ (t + 1)| * |A| ≤ |κ / lam| * 1 * |A| := by gcongr; exact hp (t + 1)
      _ = |κ / lam| * |A| := by ring
  · simp only [lift, multPath, ← hμ, ← hA]
    refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]) ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hp (t + 1))

/-- Woodford (2003), pp. 472–473: the paths (1.12)–(1.13) are admissible. -/
theorem plan_admissible {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (φm : ℝ) :
    Admissible 𝔼 β κ (lift (inflPath β κ lam xs φm)) (lift (gapPath β κ lam xs φm)) :=
  ⟨plan_AS 𝔼 hβ hκ hlam φm, fun t => 𝔼.const t _, fun t => 𝔼.const t _,
    (plan_bounded hβ hκ hlam φm).1, (plan_bounded hβ hκ hlam φm).2.1⟩

/-- **Woodford (2003), eqs. (1.10) and (1.12), p. 473**: the multiplier path
`φ_t = −(λ/κ)x* + μ₁^{t+1}(φm + (λ/κ)x*)` (with `φm = 0`: (1.12)) solves (1.10)
`βφ_{t+1} − (1 + β + κ²/λ)φ_t + φ_{t−1} = κx*` with `φ_{−1} = φm`, and it is the unique
bounded solution. -/
theorem multPath_solves_1_10 {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (φm : ℝ) :
    SecondOrderRE.SecondOrderDet β (κ ^ 2 / lam) (fun _ => κ * xs) φm (multPath β κ lam xs φm) ∧
      ∀ φ : ℕ → ℝ, (∃ K, ∀ t, |φ t| ≤ K) →
        SecondOrderRE.SecondOrderDet β (κ ^ 2 / lam) (fun _ => κ * xs) φm φ →
          φ = multPath β κ lam xs φm := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hsol : SecondOrderRE.SecondOrderDet β (κ ^ 2 / lam) (fun _ => κ * xs) φm
      (multPath β κ lam xs φm) := by
    intro t
    rw [multPath_eq_constSol hκ.ne' hlam.ne']
    exact SecondOrderRE.constSol_eq hβ hc (κ * xs) φm t
  obtain ⟨⟨y, -, hy⟩, -⟩ := SecondOrderRE.bounded_solution_unique_det hβ hc
    (f := fun _ => κ * xs) (M := |κ * xs|) (fun _ => le_rfl) φm
  have hb : ∃ K, ∀ t, |multPath β κ lam xs φm t| ≤ K := by
    obtain ⟨-, -, ⟨K, hK⟩⟩ := plan_bounded (Ω := Unit) (xs := xs) hβ hκ hlam φm
    exact ⟨K, fun t => hK t ()⟩
  refine ⟨hsol, fun φ hφb hφ => ?_⟩
  rw [hy φ ⟨hφb, hφ⟩, hy _ ⟨hb, hsol⟩]

/-- **Woodford (2003), (1.10)–(1.13), p. 473 ("(1.10) has a unique nonexplosive solution
consistent with the initial condition")**: every bounded adapted solution `(π, x, φ)` of (1.1),
(1.7)–(1.8) with initial multiplier `φm` is the path (1.12)–(1.13) (the multiplier is then
automatically bounded and adapted, by (1.8)). -/
theorem foc_system_unique {β κ lam xs φm : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {π x φ : ℕ → Ω → ℝ} (hadm : Admissible 𝔼 β κ π x) (hfoc : FOC κ lam xs φm π x φ) :
    φ = lift (multPath β κ lam xs φm) ∧ π = lift (inflPath β κ lam xs φm) ∧
      x = lift (gapPath β κ lam xs φm) := by
  obtain ⟨has, -, hxa, -, ⟨X, hX⟩⟩ := hadm
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hφx : ∀ t, φ t = (lam / κ) • (x t - fun _ => xs) := fun t => by
    funext ω
    have := (hfoc t ω).2
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linarith
  have hφa : 𝔼.Adapted φ := fun t => by rw [hφx t, map_smul, map_sub, hxa t, 𝔼.const]
  have hφb : BoundedProc φ := ⟨|lam / κ| * (X + |xs|), fun t ω => by
    rw [hφx t]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hX t ω) le_rfl))
      (abs_nonneg _)⟩
  have hso := (as_iff_multiplier 𝔼 hlam.ne' hfoc hφa).mp has
  have hφ := SecondOrderRE.eq_constant_forcing 𝔼 hβ hc (κ * xs) φm hφb hφa hso
  rw [← multPath_eq_constSol hκ.ne' hlam.ne'] at hφ
  refine ⟨hφ, ?_, ?_⟩
  · funext t ω
    have := (hfoc t ω).1
    rw [hφ] at this
    simp only [lift, inflPath]
    cases t <;> simp only [Sequences.lagged_zero, Sequences.lagged_succ] at this ⊢ <;>
      linarith
  · funext t ω
    have := (hfoc t ω).2
    rw [hφ] at this
    simp only [lift, gapPath] at this ⊢
    field_simp
    linarith

/-! ### Optimality, via Lagrangian sufficiency -/

/-- Woodford (2003), (1.1)–(1.2), p. 469: the problem as a linear-quadratic problem in the
two variables `(π, x)` (weights `1, λ`, targets `0, x*`) and the single constraint
`π_t − κx_t − βE_tπ_{t+1} = 0`. -/
noncomputable def lqProblem (β κ lam xs : ℝ) : LQSufficiency.LQProblem Ω (Fin 2) (Fin 1) where
  β := β
  w := ![1, lam]
  target := fun _ => ![fun _ => 0, fun _ => xs]
  lagCoef := 0
  curCoef := fun _ => ![1, -κ]
  leadCoef := fun _ => ![-β, 0]
  forcing := 0
  init := 0

/-- Woodford (2003), p. 472: the plan `(π, x)` as a vector process. -/
def toVec (π x : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![π t, x t]

/-- Woodford (2003), (1.1), p. 469: feasibility in the linear-quadratic form is the AS
relation. -/
theorem feasible_iff (β κ lam xs : ℝ) (π x : ℕ → Ω → ℝ) :
    LQSufficiency.Feasible 𝔼 (lqProblem β κ lam xs) (toVec π x) ↔ AS 𝔼 β κ π x := by
  unfold LQSufficiency.Feasible AS
  simp only [lqProblem, toVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply, zero_mul, zero_add]
  constructor
  · intro h t
    funext ω
    have := h t 0 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h t _ ω
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith

/-- Woodford (2003), pp. 469, 472: admissibility in the linear-quadratic form. -/
theorem plan_iff (β κ lam xs : ℝ) (π x : ℕ → Ω → ℝ) :
    LQSufficiency.Plan 𝔼 (lqProblem β κ lam xs) (toVec π x) ↔ Admissible 𝔼 β κ π x := by
  unfold LQSufficiency.Plan Admissible
  rw [feasible_iff]
  constructor
  · rintro ⟨h1, h2, M, hM⟩
    exact ⟨h1, fun t => h2 t 0, fun t => h2 t 1, ⟨M, fun t ω => hM t 0 ω⟩,
      ⟨M, fun t ω => hM t 1 ω⟩⟩
  · rintro ⟨h1, h2, h3, ⟨A, hA⟩, ⟨B, hB⟩⟩
    refine ⟨h1, fun t i => ?_, |A| + |B|, fun t i ω => ?_⟩
    · fin_cases i
      · exact h2 t
      · exact h3 t
    · fin_cases i
      · exact (hA t ω).trans (by linarith [le_abs_self A, abs_nonneg B])
      · exact (hB t ω).trans (by linarith [le_abs_self B, abs_nonneg A])

/-- Woodford (2003), eq. (1.2), p. 469: the linear-quadratic loss is the loss (1.2). -/
theorem expLoss_eq (β κ lam xs : ℝ) (π x : ℕ → Ω → ℝ) :
    LQSufficiency.expLoss 𝔼 (lqProblem β κ lam xs) (toVec π x) = loss 𝔼 β lam xs π x := by
  unfold LQSufficiency.expLoss loss LQSufficiency.periodLoss
  simp [lqProblem, toVec, Fin.sum_univ_two]

/-- Woodford (2003), (1.7)–(1.9), p. 472: the first-order conditions (1.7)–(1.8) are the
first-order conditions of the linear-quadratic form, with multiplier `φ` on the AS relation. -/
theorem foc_lq {β κ lam xs φm : ℝ} (hβ : β ≠ 0) {π x φ : ℕ → Ω → ℝ}
    (hfoc : FOC κ lam xs φm π x φ) :
    LQSufficiency.FOC 𝔼 (lqProblem β κ lam xs) (toVec π x) (fun _ _ => φm) (fun t _ => φ t) := by
  intro t i ω
  have hl : Sequences.lagged (fun _ _ => φm) (fun t (_ : Fin 1) => φ t) t 0 ω =
      Sequences.lagged (fun _ => φm) φ t ω := by cases t <;> rfl
  have h1 := (hfoc t ω).1
  have h2 := (hfoc t ω).2
  fin_cases i
  · simp [lqProblem, toVec, hl]
    field_simp
    linarith
  · simp [lqProblem, toVec]
    linarith

/-- **Woodford (2003), pp. 472–475 (optimality of the paths (1.12)–(1.13), any initial
multiplier)**: the path with initial multiplier `φm` minimises the expected loss (1.2), state by
state, among all admissible paths `(π, x)` that respect its initial commitment: no restriction
if `φm = 0`, and `π_0 = π*_0` otherwise. A path with the same expected loss at `ω` coincides with
it in conditional mean square at `ω`. -/
theorem plan_optimal (hpo : 𝔼.PullOut) {β κ lam xs φm : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) {π x : ℕ → Ω → ℝ} (hadm : Admissible 𝔼 β κ π x)
    (hinit : φm = 0 ∨ ∀ ω, π 0 ω = inflPath β κ lam xs φm 0) (ω : Ω) :
    loss 𝔼 β lam xs (lift (inflPath β κ lam xs φm)) (lift (gapPath β κ lam xs φm)) ω ≤
        loss 𝔼 β lam xs π x ω ∧
      (loss 𝔼 β lam xs π x ω =
          loss 𝔼 β lam xs (lift (inflPath β κ lam xs φm)) (lift (gapPath β κ lam xs φm)) ω →
        ∀ t, 𝔼.E 0 (fun ω => (π t ω - inflPath β κ lam xs φm t) ^ 2) ω = 0 ∧
          𝔼.E 0 (fun ω => (x t ω - gapPath β κ lam xs φm t) ^ 2) ω = 0) := by
  set P := (lqProblem β κ lam xs : LQSufficiency.LQProblem Ω (Fin 2) (Fin 1)) with hP
  have hz := (plan_iff 𝔼 β κ lam xs π x).mpr hadm
  have hzs := (plan_iff 𝔼 β κ lam xs _ _).mpr (plan_admissible 𝔼 hβ0 hκ hlam (xs := xs) φm)
  have hfoc := foc_lq 𝔼 hβ0.ne'
    (plan_foc (Ω := Ω) (β := β) (κ := κ) (lam := lam) (xs := xs) hlam.ne' φm)
  have hw : ∀ i, 0 ≤ P.w i := fun i => by
    fin_cases i
    · simp [hP, lqProblem]
    · simp [hP, lqProblem, hlam.le]
  have hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T := ⟨|xs|, fun t i ω => by
    fin_cases i
    · simp [hP, lqProblem]
    · simp [hP, lqProblem]⟩
  obtain ⟨-, -, ⟨F, hF⟩⟩ := plan_bounded (Ω := Ω) (xs := xs) hβ0 hκ hlam φm
  have hφb : ∃ F, ∀ t (k : Fin 1) (ω : Ω), |(fun t (_ : Fin 1) => lift (Ω := Ω)
      (multPath β κ lam xs φm) t) t k ω| ≤ F := ⟨F, fun t _ ω => hF t ω⟩
  have hφa : ∀ t (k : Fin 1), 𝔼.E t ((fun t (_ : Fin 1) => lift (Ω := Ω)
      (multPath β κ lam xs φm) t) t k) =
        (fun t (_ : Fin 1) => lift (multPath β κ lam xs φm) t) t k :=
    fun t _ => 𝔼.const t _
  have hφmb : ∃ F, ∀ (k : Fin 1) (ω : Ω), |(fun _ _ => φm : Fin 1 → Ω → ℝ) k ω| ≤ F :=
    ⟨|φm|, fun _ _ => le_rfl⟩
  have hin : ∑ k, 𝔼.E 0 ((fun _ _ => φm : Fin 1 → Ω → ℝ) k * LQSufficiency.dotC (P.leadCoef k)
      (fun i => toVec π x 0 i - toVec (lift (inflPath β κ lam xs φm))
        (lift (gapPath β κ lam xs φm)) 0 i)) ω = 0 := by
    have hz0 : (fun _ _ => φm : Fin 1 → Ω → ℝ) 0 * LQSufficiency.dotC (P.leadCoef 0)
        (fun i => toVec π x 0 i - toVec (lift (inflPath β κ lam xs φm))
          (lift (gapPath β κ lam xs φm)) 0 i) = 0 := by
      funext ω'
      simp only [LQSufficiency.dotC, hP, lqProblem, toVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, lift]
      rcases hinit with h | h
      · rw [h]; ring
      · rw [h ω']; ring
    simp only [Fin.sum_univ_one, hz0, map_zero, Pi.zero_apply]
  have hle := LQSufficiency.expLoss_le_of_foc 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω hin
  rw [expLoss_eq, expLoss_eq] at hle
  refine ⟨hle, fun heq t => ?_⟩
  have heq' : LQSufficiency.expLoss 𝔼 P (toVec π x) ω = LQSufficiency.expLoss 𝔼 P
      (toVec (lift (inflPath β κ lam xs φm)) (lift (gapPath β κ lam xs φm))) ω := by
    rw [expLoss_eq, expLoss_eq]; exact heq
  have e0 := LQSufficiency.eq_of_expLoss_eq 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω hin
    heq' t 0 (by simp [hP, lqProblem])
  have e1 := LQSufficiency.eq_of_expLoss_eq 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω hin
    heq' t 1 (by simp [hP, lqProblem, hlam])
  exact ⟨by simpa [toVec, lift] using e0, by simpa [toVec, lift] using e1⟩

/-- **Woodford (2003), pp. 472–473 (the optimal commitment from the standpoint of date zero)**:
the path (1.13) `π_t = (1 − μ₁)(λ/κ)x*μ₁ᵗ`, `x_t = x*μ₁^{t+1}` is admissible and minimises the
expected loss (1.2), state by state, among all bounded adapted paths satisfying (1.1); any other
path with the same expected loss coincides with it in conditional mean square. -/
theorem dateZero_optimal (hpo : 𝔼.PullOut) {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) :
    Admissible 𝔼 β κ (lift (inflPath β κ lam xs 0)) (lift (gapPath β κ lam xs 0)) ∧
      ∀ π x, Admissible 𝔼 β κ π x → ∀ ω,
        loss 𝔼 β lam xs (lift (inflPath β κ lam xs 0)) (lift (gapPath β κ lam xs 0)) ω ≤
            loss 𝔼 β lam xs π x ω ∧
          (loss 𝔼 β lam xs π x ω =
              loss 𝔼 β lam xs (lift (inflPath β κ lam xs 0)) (lift (gapPath β κ lam xs 0)) ω →
            ∀ t, 𝔼.E 0 (fun ω => (π t ω - inflPath β κ lam xs 0 t) ^ 2) ω = 0 ∧
              𝔼.E 0 (fun ω => (x t ω - gapPath β κ lam xs 0 t) ^ 2) ω = 0) :=
  ⟨plan_admissible 𝔼 hβ0 hκ hlam 0, fun _ _ hadm ω =>
    plan_optimal 𝔼 hpo hβ0 hβ1 hκ hlam hadm (Or.inl rfl) ω⟩

/-! ### The deterministic problem -/

/-- Woodford (2003), eq. (1.1), p. 469 (perfect foresight): `π_t = κx_t + βπ_{t+1}`. -/
def DetAS (β κ : ℝ) (π x : ℕ → ℝ) : Prop := ∀ t, π t = κ * x t + β * π (t + 1)

/-- Woodford (2003), p. 472: a bounded sequence. -/
def DetBounded (s : ℕ → ℝ) : Prop := ∃ M, ∀ t, |s t| ≤ M

/-- Woodford (2003), eq. (1.2), p. 469: the deterministic loss
`∑_{t ≥ 0} βᵗ [π_t² + λ(x_t − x*)²]`. -/
noncomputable def detLoss (β lam xs : ℝ) (π x : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * (π t ^ 2 + lam * (x t - xs) ^ 2)

/-- Woodford (2003), p. 472: `(π, x)` is optimal from the standpoint of date zero: bounded,
satisfying (1.1), and with loss (1.2) no larger than any other bounded path satisfying (1.1). -/
def IsDateZeroOptimal (β κ lam xs : ℝ) (π x : ℕ → ℝ) : Prop :=
  DetAS β κ π x ∧ DetBounded π ∧ DetBounded x ∧ ∀ π' x', DetAS β κ π' x' → DetBounded π' →
    DetBounded x' → detLoss β lam xs π x ≤ detLoss β lam xs π' x'

/-- Woodford (2003), p. 469: deterministic admissibility is perfect-foresight admissibility of
the lifted paths. -/
theorem detAdmissible_iff (β κ : ℝ) (π x : ℕ → ℝ) :
    (DetAS β κ π x ∧ DetBounded π ∧ DetBounded x) ↔
      Admissible perfectForesight β κ (lift π) (lift x) := by
  constructor
  · rintro ⟨h1, ⟨A, hA⟩, ⟨B, hB⟩⟩
    refine ⟨fun t => ?_, fun _ => rfl, fun _ => rfl, ⟨A, fun t _ => hA t⟩, ⟨B, fun t _ => hB t⟩⟩
    funext ω
    simp only [lift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h1 t
  · rintro ⟨h1, -, -, ⟨A, hA⟩, ⟨B, hB⟩⟩
    refine ⟨fun t => ?_, ⟨A, fun t => hA t ()⟩, ⟨B, fun t => hB t ()⟩⟩
    have := congrFun (h1 t) ()
    simpa [lift, perfectForesight] using this

/-- **Woodford (2003), pp. 472–473 (deterministic)**: a bounded path satisfying (1.1) is optimal
from the standpoint of date zero iff it is the path (1.13): `π_t = (1 − μ₁)(λ/κ)x*μ₁ᵗ`,
`x_t = x*μ₁^{t+1}`. In particular the optimum exists and is unique. -/
theorem isDateZeroOptimal_iff {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (π x : ℕ → ℝ) :
    IsDateZeroOptimal β κ lam xs π x ↔
      π = inflPath β κ lam xs 0 ∧ x = gapPath β κ lam xs 0 := by
  have hopt := dateZero_optimal perfectForesight perfectForesight_pullOut (xs := xs) hβ0 hβ1 hκ
    hlam
  have hstar := (detAdmissible_iff β κ _ _).mpr hopt.1
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hadm := (detAdmissible_iff β κ π x).mp ⟨h1, h2, h3⟩
    have hle := (hopt.2 _ _ hadm ()).1
    have hge := h4 _ _ hstar.1 hstar.2.1 hstar.2.2
    have heq := (hopt.2 _ _ hadm ()).2 (le_antisymm hge hle)
    refine ⟨funext fun t => ?_, funext fun t => ?_⟩
    · have : (π t - inflPath β κ lam xs 0 t) ^ 2 = 0 := (heq t).1
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
    · have : (x t - gapPath β κ lam xs 0 t) ^ 2 = 0 := (heq t).2
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  · rintro ⟨rfl, rfl⟩
    refine ⟨hstar.1, hstar.2.1, hstar.2.2, fun π' x' h1 h2 h3 => ?_⟩
    exact (hopt.2 _ _ ((detAdmissible_iff β κ π' x').mp ⟨h1, h2, h3⟩) ()).1

/-! ### The loss identity of p. 473 (survey E1) -/

/-- Woodford (2003), p. 473 (survey E1): for an admissible path,
`∑_t βᵗ E_0 x_t = π_0/κ` (from (1.1) by telescoping). -/
theorem hasSum_disc_gap {β κ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    {π x : ℕ → Ω → ℝ} (hadm : Admissible 𝔼 β κ π x) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (x t) ω) (π 0 ω / κ) := by
  obtain ⟨has, hπa, -, ⟨A, hA⟩, ⟨B, hB⟩⟩ := hadm
  have hx : ∀ t, 𝔼.E 0 (x t) ω = (𝔼.E 0 (π t) ω - β * 𝔼.E 0 (π (t + 1)) ω) / κ := by
    intro t
    have h := congrArg (fun f => 𝔼.E 0 f ω) (has t)
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      𝔼.tower (Nat.zero_le t)] at h
    field_simp
    linarith
  have hs : Summable (fun t => β ^ t * 𝔼.E 0 (x t) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B) (fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB t) 0 ω) (pow_nonneg hβ0 t))
  have hpart : ∀ n, ∑ t ∈ Finset.range n, β ^ t * 𝔼.E 0 (x t) ω =
      (π 0 ω - β ^ n * 𝔼.E 0 (π n) ω) / κ := by
    intro n
    induction n with
    | zero => simp [hπa 0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hx n]
      field_simp
      ring
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range n, β ^ t * 𝔼.E 0 (x t) ω) atTop
      (𝓝 (π 0 ω / κ)) := by
    simp_rw [hpart]
    have h0 : Tendsto (fun n => β ^ n * 𝔼.E 0 (π n) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => β ^ n * A) (fun n => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hA n) 0 ω) (pow_nonneg hβ0 n)
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const A
    simpa using (h0.const_sub (π 0 ω)).div_const κ
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim]
  exact hs.hasSum

/-- Woodford (2003), eq. (1.2), p. 469: the loss of an admissible path is the convergent series
`∑ βᵗ E_0[π_t² + λ(x_t − x*)²]`. -/
theorem loss_hasSum {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    {π x : ℕ → Ω → ℝ} (hadm : Admissible 𝔼 β κ π x) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (fun ω => π t ω ^ 2 + lam * (x t ω - xs) ^ 2) ω)
      (loss 𝔼 β lam xs π x ω) := by
  have hz := (plan_iff 𝔼 β κ lam xs π x).mpr hadm
  have hw : ∀ i, 0 ≤ (lqProblem β κ lam xs : LQSufficiency.LQProblem Ω (Fin 2) (Fin 1)).w i :=
    fun i => by fin_cases i <;> simp [lqProblem, hlam]
  obtain ⟨M, hM⟩ := hz.2.2
  have h := LQSufficiency.expLoss_hasSum 𝔼 (lqProblem β κ lam xs) hβ0 hβ1 hw hM
    (T := |xs|) (fun t i ω => by fin_cases i <;> simp [lqProblem]) ω
  rw [expLoss_eq] at h
  convert h using 1
  funext t
  congr 1
  refine congrArg (fun f => 𝔼.E 0 f ω) ?_
  funext ω'
  simp [LQSufficiency.periodLoss, lqProblem, toVec, Fin.sum_univ_two]

/-- **Woodford (2003), p. 473 (the loss identity, corrected general-`λ` form; survey E1)**: for
every admissible path, `E_0 ∑ βᵗ[π_t² + λ(x_t − x*)²] = E_0 ∑ βᵗ[π_t² + λx_t²] −
2(λ/κ)x*π_0 + λx*²/(1 − β)`. -/
theorem loss_identity {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 ≤ lam) {π x : ℕ → Ω → ℝ} (hadm : Admissible 𝔼 β κ π x) (ω : Ω) :
    loss 𝔼 β lam xs π x ω = loss 𝔼 β lam 0 π x ω - 2 * (lam / κ) * xs * π 0 ω +
      lam * xs ^ 2 / (1 - β) := by
  have h1 := loss_hasSum 𝔼 (xs := xs) hβ0 hβ1 hlam hadm ω
  have h0 := loss_hasSum 𝔼 (xs := 0) hβ0 hβ1 hlam hadm ω
  have hg := hasSum_disc_gap 𝔼 hβ0 hβ1 hκ hadm ω
  have hc : HasSum (fun t : ℕ => lam * xs ^ 2 * β ^ t) (lam * xs ^ 2 / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (lam * xs ^ 2)
    simpa [div_eq_mul_inv] using this
  have hcomb := (h0.sub (hg.mul_left (2 * lam * xs))).add hc
  have hterm : ∀ t, β ^ t * 𝔼.E 0 (fun ω => π t ω ^ 2 + lam * (x t ω - xs) ^ 2) ω =
      β ^ t * 𝔼.E 0 (fun ω => π t ω ^ 2 + lam * (x t ω - 0) ^ 2) ω -
        2 * lam * xs * (β ^ t * 𝔼.E 0 (x t) ω) + lam * xs ^ 2 * β ^ t := by
    intro t
    have e : (fun ω => π t ω ^ 2 + lam * (x t ω - xs) ^ 2) =
        (fun ω => π t ω ^ 2 + lam * (x t ω - 0) ^ 2) - (2 * lam * xs) • x t +
          fun _ => lam * xs ^ 2 := by
      funext ω'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, map_add, map_sub, map_smul, 𝔼.const]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1.unique (hcomb.congr_fun hterm)]
  field_simp

/-- Woodford (2003), p. 473 (the book's form, survey E1): with the welfare-theoretic weight
`λ = κ/θ` of Chapter 6, the initial term is `−2(x*/θ)π_0`. -/
theorem loss_identity_book {β κ lam xs θ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hθ : θ ≠ 0) (hlamθ : lam = κ / θ) (hlam : 0 ≤ lam) {π x : ℕ → Ω → ℝ}
    (hadm : Admissible 𝔼 β κ π x) (ω : Ω) :
    loss 𝔼 β lam xs π x ω = -2 * (xs / θ) * π 0 ω + loss 𝔼 β lam 0 π x ω +
      lam * xs ^ 2 / (1 - β) := by
  rw [loss_identity 𝔼 hβ0 hβ1 hκ hlam hadm ω, hlamθ]
  field_simp
  ring

/-- Woodford (2003), p. 473 ("all the terms … except the initial one are minimized by choosing
`π_t = 0` each period, regardless of the value of" `x*` — survey E1, the book prints `π*`): the
zero path is admissible and minimises `E_0 ∑ βᵗ(π_t² + λx_t²)` among admissible paths. -/
theorem zero_minimises_loss0 {β κ lam : ℝ} (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam) :
    Admissible 𝔼 β κ 0 0 ∧ ∀ π x : ℕ → Ω → ℝ, ∀ ω, loss 𝔼 β lam 0 0 0 ω ≤ loss 𝔼 β lam 0 π x ω := by
  refine ⟨⟨fun t => by simp, fun t => by simp, fun t => by simp, ⟨0, fun _ _ => by simp⟩,
    ⟨0, fun _ _ => by simp⟩⟩, fun π x ω => ?_⟩
  have h0 : loss 𝔼 β lam 0 0 0 ω = 0 := by
    have e : (fun ω : Ω => ∑' t, β ^ t * ((0 : ℕ → Ω → ℝ) t ω ^ 2 +
        lam * ((0 : ℕ → Ω → ℝ) t ω - 0) ^ 2)) = fun _ => 0 := by
      funext ω'; simp
    rw [loss, e, 𝔼.const]
  rw [h0]
  exact LQSufficiency.E_nonneg 𝔼 (fun ω => tsum_nonneg fun t =>
    mul_nonneg (pow_nonneg hβ0 t) (by positivity)) 0 ω

/-! ### Time inconsistency (p. 473) -/

/-- Woodford (2003), p. 473 ("the inflation rate `π_t` varies with the date `t` in (1.13)"): for
`x* ≠ 0` the date-0 optimal inflation path is not shift-invariant, `π_{t+1} ≠ π_t` (here at
`t = 0`). -/
theorem inflPath_succ_ne {β κ lam xs : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hxs : xs ≠ 0) : inflPath β κ lam xs 0 1 ≠ inflPath β κ lam xs 0 0 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := SecondOrderRE.mu1_pos hβ0 hc
  have h1 := SecondOrderRE.mu1_lt_one hβ0 hc
  rw [inflPath_zero, inflPath_zero]
  intro h
  have hk : (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * (lam / κ) * xs *
      (SecondOrderRE.mu1 β (κ ^ 2 / lam) - 1) = 0 := by linear_combination h
  have ha : 1 - SecondOrderRE.mu1 β (κ ^ 2 / lam) ≠ 0 := by linarith
  have hb : SecondOrderRE.mu1 β (κ ^ 2 / lam) - 1 ≠ 0 := by linarith
  have hlk : lam / κ ≠ 0 := by positivity
  simp only [mul_eq_zero, ha, hb, hlk, hxs, or_self] at hk

/-- **Woodford (2003), p. 473 (time inconsistency of the date-0 optimal plan)**: for `x* ≠ 0`,
the continuation from date 1 of the date-0 optimal plan, `(π_{t+1}, x_{t+1})`, is a bounded path
satisfying (1.1) from date 1 on, but it is not the optimal plan from the standpoint of date 1:
because the problem is time-invariant, the date-1 problem is the date-0 problem for the shifted
sequences, and the continuation has a strictly larger loss than its optimum. -/
theorem time_inconsistent {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hxs : xs ≠ 0) :
    DetAS β κ (fun t => inflPath β κ lam xs 0 (t + 1)) (fun t => gapPath β κ lam xs 0 (t + 1)) ∧
      DetBounded (fun t => inflPath β κ lam xs 0 (t + 1)) ∧
      DetBounded (fun t => gapPath β κ lam xs 0 (t + 1)) ∧
      ¬ IsDateZeroOptimal β κ lam xs (fun t => inflPath β κ lam xs 0 (t + 1))
        (fun t => gapPath β κ lam xs 0 (t + 1)) ∧
      detLoss β lam xs (inflPath β κ lam xs 0) (gapPath β κ lam xs 0) <
        detLoss β lam xs (fun t => inflPath β κ lam xs 0 (t + 1))
          (fun t => gapPath β κ lam xs 0 (t + 1)) := by
  have hopt := dateZero_optimal perfectForesight perfectForesight_pullOut (xs := xs) hβ0 hβ1 hκ
    hlam
  obtain ⟨has, ⟨A, hA⟩, ⟨B, hB⟩⟩ := (detAdmissible_iff β κ _ _).mpr hopt.1
  have has' : DetAS β κ (fun t => inflPath β κ lam xs 0 (t + 1))
      (fun t => gapPath β κ lam xs 0 (t + 1)) := fun t => has (t + 1)
  have hb1 : DetBounded (fun t => inflPath β κ lam xs 0 (t + 1)) := ⟨A, fun t => hA (t + 1)⟩
  have hb2 : DetBounded (fun t => gapPath β κ lam xs 0 (t + 1)) := ⟨B, fun t => hB (t + 1)⟩
  have hne : (fun t => inflPath β κ lam xs 0 (t + 1)) ≠ inflPath β κ lam xs 0 := fun h =>
    inflPath_succ_ne hβ0 hκ hlam hxs (congrFun h 0)
  have hadm := (detAdmissible_iff β κ _ _).mp ⟨has', hb1, hb2⟩
  refine ⟨has', hb1, hb2, fun h => hne ((isDateZeroOptimal_iff hβ0 hβ1 hκ hlam _ _).mp h).1,
    lt_of_le_of_ne (hopt.2 _ _ hadm ()).1 fun heq => hne (funext fun t => ?_)⟩
  have := ((hopt.2 _ _ hadm ()).2 heq.symm t).1
  have h2 : (inflPath β κ lam xs 0 (t + 1) - inflPath β κ lam xs 0 t) ^ 2 = 0 := this
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

end Woodford.GainsFromCommitment.DateZeroCommitment
