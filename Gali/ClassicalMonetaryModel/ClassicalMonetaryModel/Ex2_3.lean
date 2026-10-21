/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Ex2_2
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Exercise 2.3: equilibrium indeterminacy and interest rate rules

Galí (2015), Chapter 2, Exercise 2.3, pp. 47–48 (based on Woodford 2003). The real rate `r_t`
is exogenous (bounded, adapted) and the Fisher equation `i_t = r_t + E_t π_{t+1}` holds.

## Determinacy with one predetermined variable

The partial-adjustment rule makes `i_{t−1}` a predetermined state, so the core criterion for
two non-predetermined variables (`ExpectationSystem.determinate_iff`) does not apply. This
module proves the Blanchard–Kahn criterion for the system
`k_{t+1} = b₁₁ k_t + b₁₂ x_t + f¹_t`, `E_t x_{t+1} = b₂₁ k_t + b₂₂ x_t + f²_t` (`SolvesPred`),
`k` predetermined (`k_0` given), `x` a jump variable:
* `saddle_unique`, `saddle_exists`: if one root `μ` lies outside the unit circle, the other
  root `b₁₁ + b₂₂ − μ` inside, and a left eigenvector `(w₁, w₂)` of `μ` has `w₂ ≠ 0` (the rank
  condition; `leftEigen_of_b12` supplies one when `b₁₂ ≠ 0`), then for every `k_0` there is
  exactly one bounded solution.
* `stable_not_unique`: if both roots lie inside (Schur–Cohn), every bounded solution has a
  second one with the same `k_0` (multiplicity).
* `outside_nonexistence`: if both roots lie outside (`BothOutside`, see
  `bothOutside_roots`), two bounded solutions agree at date 0, so for all initial conditions but
  at most one there is no bounded solution (non-existence).
* `exists_bounded_forward`: the scalar forward equation `z_t = a E_t z_{t+1} + u_t` has a
  bounded solution for every `|a| < 1` (also `a < 0`).

## a. Partial adjustment `i_t = φ_i i_{t−1} + (1 − φ_i)(ρ + φ_π π_t)`

* `pa_iff_system`: the equilibrium is the system above with `k_t = i_{t−1} − ρ`, `x_t = π_t`,
  roots `0` and `λ = φ_i + (1 − φ_i)φ_π`.
* `pa_determinate_iff`: for `0 ≤ φ_i < 1`, the equilibrium is unique for every bounded real
  rate and initial `i_{−1}` iff `|λ| > 1`; `pa_determinate_iff_of_nonneg`: for `φ_π ≥ 0` iff
  `φ_π > 1`.
* `pa_interest_forward`: for `φ_π > 1` the equilibrium interest rate is
  `i_t − ρ = ∑_{k ≥ 0} λ^{−(k+1)} (1 − φ_i)φ_π E_t r̂_{t+k}` and inflation is
  `π_t = (î_t − φ_i î_{t−1})/((1 − φ_i)φ_π)` (`pa_inflation_eq`).
* `pa_boundary_nonexistence`: at `φ_π = 1` a constant `r̂ ≠ 0` has no bounded equilibrium,
  so both failure modes occur.
* `pa_phi_i_one_not_determinate` (**correction**): the book allows `φ_i ∈ [0, 1]`, but for
  `φ_i = 1` the equilibrium is never unique, whatever `φ_π`; the claim needs `φ_i < 1`.

## b–c. Moving-average inflation targeting `i_t = ρ + φ_π π̄_t`

* `maBar`: `π̄_t = (1 − δ)∑_{k ≥ 0} δᵏ π_{t−k}`, a genuine infinite sum over the whole past
  (pre-sample inflation `h` is part of the data); `maBar_succ`: `π̄_t = δ π̄_{t−1} + (1−δ) π_t`.
* `ma_iff_pa` (c): the moving-average rule is exactly the partial-adjustment rule with
  `φ_i = δ` and `i_{−1} = ρ + φ_π π̄_{−1}`; `ma_equilibrium_iff_pa`; `pa_as_ma`: conversely
  every partial-adjustment rule with `φ_π ≠ 0` is a moving-average rule for a suitable history.
* `ma_determinate_iff` (b): for `0 ≤ δ < 1`, determinacy iff `|δ + (1 − δ)φ_π| > 1`;
  `ma_determinate_iff_of_nonneg`: for `φ_π ≥ 0` iff `φ_π > 1`.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_3

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Scalar forward equations with a negative coefficient -/

/-- Galí (2015), (25) p. 27 (forward solutions), for any `|a| < 1`: the equation
`z_t = a E_t z_{t+1} + u_t` with bounded adapted `u` has a bounded adapted solution. For
`a < 0` it is `(−1)ᵗ` times the forward series of `|a|` applied to `(−1)ᵗ u_t`. -/
theorem exists_bounded_forward {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    ∃ z : ℕ → Ω → ℝ, (∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) ∧ 𝔼.Adapted z ∧
      BoundedProc z := by
  rcases le_or_gt 0 a with ha0 | ha0
  · have ha1 : a < 1 := (le_abs_self a).trans_lt ha
    exact ⟨𝔼.forwardSeries a u, 𝔼.forwardSeries_solves ha0 ha1 hu hua,
      Ex2_2.forwardSeries_adapted 𝔼 ha0 ha1 hu hua, 𝔼.forwardSeries_bounded ha0 ha1 hu⟩
  · set b := -a with hb
    have hb0 : 0 ≤ b := by linarith
    have hb1 : b < 1 := by rw [abs_of_neg ha0] at ha; linarith
    set v : ℕ → Ω → ℝ := fun t => ((-1 : ℝ) ^ t) • u t with hv
    have hvb : ∀ t ω, |v t ω| ≤ M := fun t ω => by
      simp only [hv, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact hu t ω
    have hva : 𝔼.Adapted v := fun t => by rw [hv]; simp only; rw [map_smul, hua t]
    set F := 𝔼.forwardSeries b v with hF
    have hFs := 𝔼.forwardSeries_solves hb0 hb1 hvb hva
    have hFa := Ex2_2.forwardSeries_adapted 𝔼 hb0 hb1 hvb hva
    obtain ⟨K, hK⟩ := 𝔼.forwardSeries_bounded hb0 hb1 hvb
    have hsq : ∀ t : ℕ, ((-1 : ℝ) ^ t) * (-1) ^ t = 1 := fun t => by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    refine ⟨fun t => ((-1 : ℝ) ^ t) • F t, fun t => ?_, fun t => ?_, ⟨K, fun t ω => ?_⟩⟩
    · change ((-1 : ℝ) ^ t) • F t = a • 𝔼.E t (((-1 : ℝ) ^ (t + 1)) • F (t + 1)) + u t
      rw [hF, hFs t, map_smul]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, hb, pow_succ]
      have := hsq t
      linear_combination (u t ω) * this
    · rw [map_smul, hFa t]
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact hK t ω

/-! ### Systems with one predetermined variable -/

/-- Galí (2015), Exercise 2.3, p. 47 (and Blanchard–Kahn 1980): `(k, x)` solves the system
with predetermined `k` and jump variable `x`:
`k_{t+1} = b₁₁ k_t + b₁₂ x_t + f¹_t` and `E_t x_{t+1} = b₂₁ k_t + b₂₂ x_t + f²_t`. -/
def SolvesPred (b11 b12 b21 b22 : ℝ) (f1 f2 k x : ℕ → Ω → ℝ) : Prop :=
  (∀ t, k (t + 1) = b11 • k t + b12 • x t + f1 t) ∧
    ∀ t, 𝔼.E t (x (t + 1)) = b21 • k t + b22 • x t + f2 t

/-- Galí (2015), p. 25 (information): what is known at `t` is known at `t + 1`. -/
theorem known_succ {t : ℕ} {y : Ω → ℝ} (h : 𝔼.E t y = y) : 𝔼.E (t + 1) y = y := by
  rw [← h, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 2.3: in a solution with `k_0` known at `0` and adapted `x`, `f¹`,
the predetermined variable is known one period ahead: `E_t k_t = k_t` and
`E_t k_{t+1} = k_{t+1}`. -/
theorem pred_known {b11 b12 b21 b22 : ℝ} {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hk0 : 𝔼.E 0 (k 0) = k 0)
    (hx : 𝔼.Adapted x) (hf1 : 𝔼.Adapted f1) :
    ∀ t, 𝔼.E t (k t) = k t ∧ 𝔼.E t (k (t + 1)) = k (t + 1) := by
  have step : ∀ t, 𝔼.E t (k t) = k t → 𝔼.E t (k (t + 1)) = k (t + 1) := fun t h => by
    rw [hs.1 t, map_add, map_add, map_smul, map_smul, h, hx t, hf1 t]
  have hk : ∀ t, 𝔼.E t (k t) = k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => exact known_succ 𝔼 (step t ih)
  exact fun t => ⟨hk t, step t (hk t)⟩

/-- Galí (2015), Exercise 2.3 (Blanchard–Kahn): along a solution, `z_t = w₁ k_t + w₂ x_t` for
a left eigenvector `(w₁, w₂)` of the root `μ` satisfies the scalar forward equation
`z_t = μ^{−1} E_t z_{t+1} − μ^{−1}(w₁ f¹_t + w₂ f²_t)`. -/
theorem saddle_z_eq {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hμ : μ ≠ 0) {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hk : ∀ t, 𝔼.E t (k (t + 1)) = k (t + 1))
    (t : ℕ) :
    (fun t => w1 • k t + w2 • x t) t = μ⁻¹ • 𝔼.E t ((fun t => w1 • k t + w2 • x t) (t + 1))
      + (-μ⁻¹) • (w1 • f1 t + w2 • f2 t) := by
  simp only
  rw [map_add, map_smul, map_smul, hk t, hs.2 t, hs.1 t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination (-(k t ω)) * hw1 - (x t ω) * hw2

/-- Galí (2015), Exercise 2.3 (**uniqueness on the saddle path**): if `|μ| > 1` is a root with
left eigenvector `(w₁, w₂)`, `w₂ ≠ 0`, then two bounded solutions with the same initial
`k_0` (known at date 0) coincide. -/
theorem saddle_unique {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hw20 : w2 ≠ 0) (hμ : 1 < |μ|)
    {f1 f2 k x k' x' : ℕ → Ω → ℝ} (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x)
    (hs' : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x') (hk0 : k 0 = k' 0)
    (hk0a : 𝔼.E 0 (k 0) = k 0) (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x') (hf1 : 𝔼.Adapted f1)
    (hkb : BoundedProc k) (hxb : BoundedProc x) (hkb' : BoundedProc k')
    (hxb' : BoundedProc x') : k = k' ∧ x = x' := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμ
    linarith
  have hk := fun t => (pred_known 𝔼 hs hk0a hx hf1 t).2
  have hk' := fun t => (pred_known 𝔼 hs' (by rw [← hk0]; exact hk0a) hx' hf1 t).2
  have ha : |μ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ
  have hzb : ∀ {k x : ℕ → Ω → ℝ}, BoundedProc k → BoundedProc x →
      BoundedProc (fun t => w1 • k t + w2 • x t) := by
    intro k x ⟨M1, hM1⟩ ⟨M2, hM2⟩
    refine ⟨|w1| * M1 + |w2| * M2, fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact hM1 t ω
    · exact hM2 t ω
  have hz := 𝔼.forward_unique ha (saddle_z_eq 𝔼 hw1 hw2 hμ0 hs hk)
    (saddle_z_eq 𝔼 hw1 hw2 hμ0 hs' hk') (hzb hkb hxb) (hzb hkb' hxb')
  have hxk : ∀ t, k t = k' t → x t = x' t := by
    intro t ht
    have h := congrFun hz t
    simp only [ht] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have h2 : w2 * x t ω = w2 * x' t ω := by linarith
    exact mul_left_cancel₀ hw20 h2
  have hkk : ∀ t, k t = k' t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hs.1 t, hs'.1 t, ih, hxk t ih]
  exact ⟨funext hkk, funext fun t => hxk t (hkk t)⟩

/-- Galí (2015), Exercise 2.3: the path of the predetermined variable on the saddle path,
`k_0` given and `k_{t+1} = μ₁ k_t + c z_t + f¹_t`. -/
def kPath (k0 : Ω → ℝ) (μ1 c : ℝ) (z f1 : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => k0
  | t + 1 => μ1 • kPath k0 μ1 c z f1 t + c • z t + f1 t

/-- Galí (2015), Exercise 2.3: for `|μ₁| < 1` and bounded `k_0`, `z`, `f¹`, the saddle-path
`k` is bounded by `max K₀ ((|c| |M_z| + |M_f|)/(1 − |μ₁|))`. -/
theorem kPath_bounded {k0 : Ω → ℝ} {μ1 c K0 Mz Mf : ℝ} {z f1 : ℕ → Ω → ℝ} (hμ1 : |μ1| < 1)
    (hk0 : ∀ ω, |k0 ω| ≤ K0) (hz : ∀ t ω, |z t ω| ≤ Mz) (hf : ∀ t ω, |f1 t ω| ≤ Mf) :
    ∀ t ω, |kPath k0 μ1 c z f1 t ω| ≤ max K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|)) := by
  set B := max K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|)) with hB
  have h1 : 0 < 1 - |μ1| := by linarith
  have hD : |c| * |Mz| + |Mf| ≤ (1 - |μ1|) * B := by
    have := le_max_right K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|))
    rw [← hB, div_le_iff₀ h1] at this
    linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) (le_max_right _ _)
  intro t
  induction t with
  | zero => exact fun ω => (hk0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    simp only [kPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h3 : |μ1 * kPath k0 μ1 c z f1 t ω| ≤ |μ1| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have h4 : |c * z t ω| ≤ |c| * |Mz| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hz t ω).trans (le_abs_self _)) (abs_nonneg _)
    have h5 : |f1 t ω| ≤ |Mf| := (hf t ω).trans (le_abs_self _)
    calc |μ1 * kPath k0 μ1 c z f1 t ω + c * z t ω + f1 t ω|
        ≤ |μ1 * kPath k0 μ1 c z f1 t ω| + |c * z t ω| + |f1 t ω| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ |μ1| * B + (|c| * |Mz| + |Mf|) := by linarith
      _ ≤ B := by nlinarith

/-- Galí (2015), Exercise 2.3 (**existence on the saddle path**): if `|μ| > 1` is a root with
left eigenvector `(w₁, w₂)`, `w₂ ≠ 0`, the other root `b₁₁ + b₂₂ − μ` has modulus below one,
and the forcing terms and `k_0` are bounded and known when dated, then there is a bounded
solution starting from `k_0`. -/
theorem saddle_exists {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hw20 : w2 ≠ 0) (hμ : 1 < |μ|)
    (hμ1 : |b11 + b22 - μ| < 1) {f1 f2 : ℕ → Ω → ℝ} {k0 : Ω → ℝ} (hf1b : BoundedProc f1)
    (hf2b : BoundedProc f2) (hf1 : 𝔼.Adapted f1) (hf2 : 𝔼.Adapted f2)
    (hk0b : ∃ M, ∀ ω, |k0 ω| ≤ M) (hk0 : 𝔼.E 0 k0 = k0) :
    ∃ k x : ℕ → Ω → ℝ, SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x ∧ k 0 = k0 ∧ 𝔼.Adapted x ∧
      BoundedProc k ∧ BoundedProc x := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμ
    linarith
  obtain ⟨M1, hM1⟩ := hf1b
  obtain ⟨M2, hM2⟩ := hf2b
  obtain ⟨K0, hK0⟩ := hk0b
  set g : ℕ → Ω → ℝ := fun t => w1 • f1 t + w2 • f2 t with hg
  have hu : ∀ t ω, |((-μ⁻¹) • g t) ω| ≤ |μ⁻¹| * (|w1| * M1 + |w2| * M2) := fun t ω => by
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact hM1 t ω
    · exact hM2 t ω
  have hua : 𝔼.Adapted (fun t => (-μ⁻¹) • g t) := fun t => by
    simp only [hg]
    rw [map_smul, map_add, map_smul, map_smul, hf1 t, hf2 t]
  have ha : |μ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ
  obtain ⟨z, hz, hza, ⟨Mz, hMz⟩⟩ := exists_bounded_forward 𝔼 ha hu hua
  set μ1 := b11 + b22 - μ with hμ1def
  set c := b12 / w2 with hc
  set k := kPath k0 μ1 c z f1 with hk
  have hkb := kPath_bounded (c := c) hμ1 hK0 hMz hM1
  -- the predetermined variable is known one period ahead
  have hkk : ∀ t, 𝔼.E t (k t) = k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      refine known_succ 𝔼 ?_
      change 𝔼.E t (μ1 • k t + c • z t + f1 t) = μ1 • k t + c • z t + f1 t
      rw [map_add, map_add, map_smul, map_smul, ih, hza t, hf1 t]
  have hk1 : ∀ t, 𝔼.E t (k (t + 1)) = k (t + 1) := by
    intro t
    change 𝔼.E t (μ1 • k t + c • z t + f1 t) = μ1 • k t + c • z t + f1 t
    rw [map_add, map_add, map_smul, map_smul, hkk t, hza t, hf1 t]
  -- `E_t z_{t+1} = μ z_t + g_t`
  have hEz : ∀ t ω, 𝔼.E t (z (t + 1)) ω = μ * z t ω + g t ω := by
    intro t ω
    have := congrFun (hz t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    field_simp at this
    linarith
  refine ⟨k, fun t => w2⁻¹ • (z t - w1 • k t), ⟨fun t => ?_, fun t => ?_⟩, rfl, fun t => ?_,
    ⟨_, hkb⟩, ⟨|w2⁻¹| * (|Mz| + |w1| * max K0 ((|c| * |Mz| + |M1|) / (1 - |μ1|))),
      fun t ω => ?_⟩⟩
  · change μ1 • k t + c • z t + f1 t = b11 • k t + b12 • (w2⁻¹ • (z t - w1 • k t)) + f1 t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hμ1def, hc]
    field_simp
    linear_combination (k t ω) * hw2
  · rw [map_smul, map_sub, map_smul, hk1 t]
    funext ω
    have hkt : k (t + 1) ω = μ1 * k t ω + c * z t ω + f1 t ω := rfl
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hEz, hkt, hg, hμ1def,
      hc]
    field_simp
    linear_combination (-(w2 * k t ω)) * hw1 + (-(z t ω)) * hw2
  · rw [map_smul, map_sub, map_smul, hza t, hkk t]
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    gcongr
    refine (abs_sub _ _).trans (add_le_add ((hMz t ω).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    gcongr
    exact hkb t ω

/-- Galí (2015), Exercise 2.3 (rank condition): if `b₁₂ ≠ 0` and `μ` is a root of the
characteristic polynomial `μ² − (b₁₁ + b₂₂)μ + (b₁₁b₂₂ − b₁₂b₂₁)`, then
`(w₁, w₂) = (μ − b₂₂, b₁₂)` is a left eigenvector for `μ` with `w₂ ≠ 0`. -/
theorem leftEigen_of_b12 {b11 b12 b21 b22 μ : ℝ}
    (hroot : μ ^ 2 - (b11 + b22) * μ + (b11 * b22 - b12 * b21) = 0) :
    (μ - b22) * b11 + b12 * b21 = μ * (μ - b22) ∧ (μ - b22) * b12 + b12 * b22 = μ * b12 := by
  constructor
  · linear_combination (-1 : ℝ) * hroot
  · ring

/-- Galí (2015), Exercise 2.3 (**multiplicity when both roots are inside the unit circle**):
under the Schur–Cohn condition every bounded solution `(k, x)` has a different bounded
solution with the same `k_0`, obtained by adding the deterministic path
`(k, x)_t ↦ (k, x)_t + Bᵗ (0, 1)`. -/
theorem stable_not_unique [Nonempty Ω] {b11 b12 b21 b22 : ℝ}
    (hA : SchurStable (b11 + b22) (b11 * b22 - b12 * b21)) {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hx : 𝔼.Adapted x) (hkb : BoundedProc k)
    (hxb : BoundedProc x) :
    ∃ k' x' : ℕ → Ω → ℝ, SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x' ∧ k' 0 = k 0 ∧
      𝔼.Adapted x' ∧ BoundedProc k' ∧ BoundedProc x' ∧ x' ≠ x := by
  set B : Matrix (Fin 2) (Fin 2) ℝ := !![b11, b12; b21, b22] with hB
  have hS : SchurStable (tr2 B) (det2 B) := by
    simpa [tr2, det2, hB] using hA
  set d : ℕ → Fin 2 → ℝ := fun t i => (B ^ t) i 1 with hd
  have hrec : ∀ t i, d (t + 1) i = B i 0 * d t 0 + B i 1 * d t 1 := by
    intro t i
    simp only [hd, pow_succ', Matrix.mul_apply, Fin.sum_univ_two]
  have hdb : ∀ i, ∃ C, ∀ t, |d t i| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_range_of_tendsto _ (tendsto_pow_entry hS i 1)).exists_norm_le
    exact ⟨C, fun t => by simpa using hC _ ⟨t, rfl⟩⟩
  obtain ⟨C0, hC0⟩ := hdb 0
  obtain ⟨C1, hC1⟩ := hdb 1
  obtain ⟨Mk, hMk⟩ := hkb
  obtain ⟨Mx, hMx⟩ := hxb
  refine ⟨fun t ω => k t ω + d t 0, fun t ω => x t ω + d t 1, ⟨fun t => ?_, fun t => ?_⟩,
    ?_, fun t => ?_, ⟨Mk + C0, fun t ω => ?_⟩, ⟨Mx + C1, fun t ω => ?_⟩, fun h => ?_⟩
  · funext ω
    have := congrFun (hs.1 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this, hrec t 0]
    simp [hB]
    ring
  · have hfun : (fun ω => x (t + 1) ω + d (t + 1) 1) = x (t + 1) + fun _ => d (t + 1) 1 := rfl
    change 𝔼.E t (fun ω => x (t + 1) ω + d (t + 1) 1) = _
    rw [hfun, map_add, 𝔼.const, hs.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrec t 1]
    simp [hB]
    ring
  · funext ω
    simp [hd]
  · have hfun : (fun ω => x t ω + d t 1) = x t + fun _ => d t 1 := rfl
    change 𝔼.E t (fun ω => x t ω + d t 1) = fun ω => x t ω + d t 1
    rw [hfun, map_add, 𝔼.const, hx t]
  · exact (abs_add_le _ _).trans (add_le_add (hMk t ω) (hC0 t))
  · exact (abs_add_le _ _).trans (add_le_add (hMx t ω) (hC1 t))
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [hd] at this

/-- Galí (2015), Exercise 2.3: both roots of `z² − T z + D` lie strictly outside the unit
circle (`bothOutside_roots`); equivalently the reversed polynomial is Schur–Cohn stable. -/
def BothOutside (T D : ℝ) : Prop := 1 < |D| ∧ |T| < |1 + D|

/-- Galí (2015), Exercise 2.3: under `BothOutside T D` the inverse matrix, with trace `T/D` and
determinant `1/D`, satisfies the Schur–Cohn condition. -/
theorem schurStable_inv_of_bothOutside {T D : ℝ} (h : BothOutside T D) :
    SchurStable (T / D) (1 / D) := by
  obtain ⟨hD, hT⟩ := h
  have hD0 : 0 < |D| := by linarith
  have h1 : |1 / D| < 1 := by
    rw [abs_div, abs_one, div_lt_one hD0]
    exact hD
  refine ⟨h1, ?_⟩
  have hpos : 0 < 1 + 1 / D := by
    have := neg_abs_le (1 / D)
    linarith
  have e : |1 + D| / |D| = 1 + 1 / D := by
    have e1 : (1 + D) / D = 1 + 1 / D := by rw [add_div, div_self (abs_pos.1 hD0), add_comm]
    rw [← abs_div, e1, abs_of_pos hpos]
  rw [abs_div, ← e]
  exact div_lt_div_of_pos_right hT hD0

/-- Galí (2015), Exercise 2.3: under `BothOutside T D` every complex root of `z² − T z + D`
has modulus greater than one. -/
theorem bothOutside_roots {T D : ℝ} (h : BothOutside T D) {z : ℂ}
    (hz : z ^ 2 - T * z + D = 0) : 1 < ‖z‖ := by
  have hD0 : D ≠ 0 := fun h0 => by
    have := h.1
    rw [h0, abs_zero] at this
    linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    have h2 : ((D : ℝ) : ℂ) = 0 := by simpa using hz
    exact hD0 (by exact_mod_cast h2)
  have hw : z⁻¹ ^ 2 - ((T / D : ℝ) : ℂ) * z⁻¹ + ((1 / D : ℝ) : ℂ) = 0 := by
    have hD0' : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
    push_cast
    field_simp
    linear_combination hz
  have hroots := (schurStable_iff_roots _ _).1 (schurStable_inv_of_bothOutside h)
  have hlt : ‖z⁻¹‖ < 1 := by
    rcases eq_root_of_eq hw with h1 | h1
    · rw [h1]; exact hroots.1
    · rw [h1]; exact hroots.2
  rw [norm_inv] at hlt
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rwa [inv_lt_one₀ hpos] at hlt

/-- Galí (2015), Exercise 2.3 (**non-existence when both roots are outside the unit
circle**): two bounded solutions with the same forcing terms, both with `k_0` known at date 0
and adapted `x`, agree at date 0. So for every forcing there is at most one initial condition
`k_0` with a bounded solution. -/
theorem outside_nonexistence {b11 b12 b21 b22 : ℝ}
    (hout : BothOutside (b11 + b22) (b11 * b22 - b12 * b21)) {f1 f2 k x k' x' : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x)
    (hs' : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x') (hk0 : 𝔼.E 0 (k 0) = k 0)
    (hk0' : 𝔼.E 0 (k' 0) = k' 0) (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x')
    (hkb : BoundedProc k) (hxb : BoundedProc x) (hkb' : BoundedProc k')
    (hxb' : BoundedProc x') : k 0 = k' 0 ∧ x 0 = x' 0 := by
  set D := b11 * b22 - b12 * b21 with hDdef
  have hD0 : D ≠ 0 := fun h0 => by
    have := hout.1
    rw [h0, abs_zero] at this
    linarith
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![b22 / D, -b12 / D; -b21 / D, b11 / D] with hA
  have hS : SchurStable (tr2 A) (det2 A) := by
    have e1 : tr2 A = (b11 + b22) / D := by simp [tr2, hA]; ring
    have e2 : det2 A = 1 / D := by
      simp only [det2, hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      rw [hDdef]
      ring
    rw [e1, e2]
    exact schurStable_inv_of_bothOutside hout
  obtain ⟨Mk, hMk⟩ := hkb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mk', hMk'⟩ := hkb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  -- the date-0 expectation of the difference follows the deterministic recursion
  have key : ∀ ω, 𝔼.E 0 (k 0 - k' 0) ω = 0 ∧ 𝔼.E 0 (x 0 - x' 0) ω = 0 := by
    intro ω
    set y : ℕ → Fin 2 → ℝ := fun t => ![𝔼.E 0 (k t - k' t) ω, 𝔼.E 0 (x t - x' t) ω] with hy
    have hrec0 : ∀ t, 𝔼.E 0 (k (t + 1) - k' (t + 1)) ω
        = b11 * 𝔼.E 0 (k t - k' t) ω + b12 * 𝔼.E 0 (x t - x' t) ω := by
      intro t
      rw [hs.1 t, hs'.1 t]
      have : b11 • k t + b12 • x t + f1 t - (b11 • k' t + b12 • x' t + f1 t)
          = b11 • (k t - k' t) + b12 • (x t - x' t) := by
        funext ω'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, map_add, map_smul, map_smul]
      rfl
    have hrec1 : ∀ t, 𝔼.E 0 (x (t + 1) - x' (t + 1)) ω
        = b21 * 𝔼.E 0 (k t - k' t) ω + b22 * 𝔼.E 0 (x t - x' t) ω := by
      intro t
      rw [← 𝔼.tower (Nat.zero_le t), map_sub, hs.2 t, hs'.2 t]
      have : b21 • k t + b22 • x t + f2 t - (b21 • k' t + b22 • x' t + f2 t)
          = b21 • (k t - k' t) + b22 • (x t - x' t) := by
        funext ω'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, map_add, map_smul, map_smul]
      rfl
    have hhom : ∀ t, y t = A.mulVec (y (t + 1)) := by
      intro t
      funext i
      fin_cases i
      · simp only [hy, hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
        rw [hrec0, hrec1]
        field_simp
        rw [hDdef]
        ring
      · simp only [hy, hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
        rw [hrec0, hrec1]
        field_simp
        rw [hDdef]
        ring
    have hyb : BoundedSeq y := by
      refine ⟨Mk + Mk' + (Mx + Mx'), fun t i => ?_⟩
      have h1 : |𝔼.E 0 (k t - k' t) ω| ≤ Mk + Mk' :=
        𝔼.abs_E_le (fun ω' => (abs_sub _ _).trans (add_le_add (hMk t ω') (hMk' t ω'))) 0 ω
      have h2 : |𝔼.E 0 (x t - x' t) ω| ≤ Mx + Mx' :=
        𝔼.abs_E_le (fun ω' => (abs_sub _ _).trans (add_le_add (hMx t ω') (hMx' t ω'))) 0 ω
      have h0 : 0 ≤ Mk + Mk' := (abs_nonneg _).trans h1
      have h0' : 0 ≤ Mx + Mx' := (abs_nonneg _).trans h2
      fin_cases i
      · simp only [hy, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp only [hy, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith
    have h0 := homogeneous_eq_zero hS hhom hyb
    have e0 := congrFun (congrFun h0 0) 0
    have e1 := congrFun (congrFun h0 0) 1
    simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply] at e0 e1
    exact ⟨e0, e1⟩
  constructor
  · funext ω
    have := (key ω).1
    rw [map_sub, hk0, hk0'] at this
    simpa [sub_eq_zero] using this
  · funext ω
    have := (key ω).2
    rw [map_sub, hx 0, hx' 0] at this
    simpa [sub_eq_zero] using this

/-! ### a. The partial-adjustment rule -/

/-- Galí (2015), Exercise 2.3(a), p. 47: the lagged interest rate `i_{t−1}`, with the given
initial value `i_{−1}` at `t = 0`. -/
def lagI (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => im1
  | t + 1 => i t

/-- Galí (2015), Exercise 2.3(a): `i_{−1}` at date 0. -/
theorem lagI_zero (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) : lagI im1 i 0 = im1 := rfl

/-- Galí (2015), Exercise 2.3(a): `i_{(t+1)−1} = i_t`. -/
theorem lagI_succ (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) : lagI im1 i (t + 1) = i t := rfl

/-- Galí (2015), Exercise 2.3(a), p. 47: equilibrium under the partial-adjustment rule
`i_t = φ_i i_{t−1} + (1 − φ_i)(ρ + φ_π π_t)` with the Fisher equation
`i_t = r_t + E_t π_{t+1}`. -/
def PAEquilibrium (φi φπ ρ : ℝ) (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ) (i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t = r t + 𝔼.E t (infl (t + 1))) ∧
    ∀ t ω, i t ω = φi * lagI im1 i t ω + (1 - φi) * (ρ + φπ * infl t ω)

/-- Galí (2015), Exercise 2.3(a), p. 47: the partial-adjustment equilibrium is the system
`k_{t+1} = φ_i k_t + κ π_t`, `E_t π_{t+1} = φ_i k_t + κ π_t − r̂_t` in the predetermined
`k_t = i_{t−1} − ρ` and the jump variable `π_t`, with `κ = (1 − φ_i)φ_π`; its matrix has roots
`0` and `λ = φ_i + κ`. -/
theorem pa_iff_system (φi φπ ρ : ℝ) (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ) (i infl : ℕ → Ω → ℝ) :
    PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ↔
      SolvesPred 𝔼 φi ((1 - φi) * φπ) φi ((1 - φi) * φπ) (fun _ _ => 0)
        (fun t ω => ρ - r t ω) (fun t ω => lagI im1 i t ω - ρ) infl := by
  constructor
  · rintro ⟨hf, hr⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hr t ω]
      ring
    · have := congrFun (hf t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [hr t ω] at this
      linarith
  · rintro ⟨h1, h2⟩
    have hrule : ∀ t ω, i t ω = φi * lagI im1 i t ω + (1 - φi) * (ρ + φπ * infl t ω) := by
      intro t ω
      have := congrFun (h1 t) ω
      simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    refine ⟨fun t => funext fun ω => ?_, hrule⟩
    have := congrFun (h2 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    linarith [hrule t ω]

/-- Galí (2015), Exercise 2.3: with an adapted real rate, the Fisher equation makes the nominal
rate adapted. -/
theorem pa_i_adapted {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) : 𝔼.Adapted i := by
  intro t
  rw [heq.1 t, map_add, hra t, 𝔼.E_E_self]

/-- Galí (2015), Exercise 2.3(a): the deviation `i_{t−1} − ρ` of a bounded interest path with a
bounded initial condition is bounded. -/
theorem lag_bounded {ρ : ℝ} {im1 : Ω → ℝ} {i : ℕ → Ω → ℝ} (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M)
    (hib : BoundedProc i) : BoundedProc (fun t ω => lagI im1 i t ω - ρ) := by
  obtain ⟨M1, hM1⟩ := him1
  obtain ⟨M2, hM2⟩ := hib
  refine ⟨max M1 M2 + |ρ|, fun t ω => (abs_sub _ _).trans ?_⟩
  cases t with
  | zero => simp only [lagI_zero]; linarith [hM1 ω, le_max_left M1 M2]
  | succ t => simp only [lagI_succ]; linarith [hM2 t ω, le_max_right M1 M2]

/-- Galí (2015), Exercise 2.3(a): with `i_{−1}` known at date 0, `E_0 k_0 = k_0` for
`k_0 = i_{−1} − ρ`. -/
theorem E_zero_k0 {ρ : ℝ} {im1 : Ω → ℝ} (him1a : 𝔼.E 0 im1 = im1) (i : ℕ → Ω → ℝ) :
    𝔼.E 0 ((fun t ω => lagI im1 i t ω - ρ) 0) = (fun t ω => lagI im1 i t ω - ρ) 0 := by
  change 𝔼.E 0 (fun ω => im1 ω - ρ) = fun ω => im1 ω - ρ
  rw [Ex2_2.E_sub_const, him1a]

/-- Galí (2015), Exercise 2.3(a) (**uniqueness**): for `0 ≤ φ_i < 1` and
`|φ_i + (1 − φ_i)φ_π| > 1`, two bounded partial-adjustment equilibria with the same real rate
and the same `i_{−1}` (known at date 0) coincide. -/
theorem pa_unique {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1)
    (hlam : 1 < |φi + (1 - φi) * φπ|) {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ}
    (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M) (him1a : 𝔼.E 0 im1 = im1) {i infl i' infl' : ℕ → Ω → ℝ}
    (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl)
    (heq' : PAEquilibrium 𝔼 φi φπ ρ r im1 i' infl') (hx : 𝔼.Adapted infl)
    (hx' : 𝔼.Adapted infl') (hib : BoundedProc i) (hxb : BoundedProc infl)
    (hib' : BoundedProc i') (hxb' : BoundedProc infl') : i = i' ∧ infl = infl' := by
  have hκ : (1 - φi) * φπ ≠ 0 := by
    intro h0
    rw [h0, add_zero, abs_of_nonneg hφi0] at hlam
    linarith
  obtain ⟨hk, hxx⟩ := saddle_unique 𝔼 (b11 := φi) (b12 := (1 - φi) * φπ) (b21 := φi)
    (b22 := (1 - φi) * φπ) (μ := φi + (1 - φi) * φπ) (w1 := φi)
    (w2 := (1 - φi) * φπ) (by ring) (by ring) hκ hlam ((pa_iff_system 𝔼 _ _ _ _ _ _ _).1 heq)
    ((pa_iff_system 𝔼 _ _ _ _ _ _ _).1 heq') rfl (E_zero_k0 𝔼 him1a i) hx hx'
    (fun t => 𝔼.const t 0) (lag_bounded him1 hib) hxb (lag_bounded him1 hib') hxb'
  refine ⟨funext fun t => funext fun ω => ?_, hxx⟩
  have := congrFun (congrFun hk (t + 1)) ω
  simp only [lagI_succ] at this
  linarith

/-- Galí (2015), Exercise 2.3(a) (**existence**): for `0 ≤ φ_i < 1` and
`|φ_i + (1 − φ_i)φ_π| > 1`, for every bounded adapted real rate and bounded `i_{−1}` known at
date 0 there is a bounded adapted partial-adjustment equilibrium. -/
theorem pa_exists {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1)
    (hlam : 1 < |φi + (1 - φi) * φπ|) {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} (hrb : BoundedProc r)
    (hra : 𝔼.Adapted r) (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M) (him1a : 𝔼.E 0 im1 = im1) :
    ∃ i infl, PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl := by
  have hκ : (1 - φi) * φπ ≠ 0 := by
    intro h0
    rw [h0, add_zero, abs_of_nonneg hφi0] at hlam
    linarith
  obtain ⟨Mr, hMr⟩ := hrb
  obtain ⟨M1, hM1⟩ := him1
  have hf2b : BoundedProc (fun t ω => ρ - r t ω) :=
    ⟨|ρ| + Mr, fun t ω => (abs_sub _ _).trans (by linarith [hMr t ω])⟩
  have hf2a : 𝔼.Adapted (fun t ω => ρ - r t ω) := fun t => by
    change 𝔼.E t ((fun _ => ρ) - r t) = (fun _ => ρ) - r t
    rw [map_sub, 𝔼.const, hra t]
  have hk0b : ∃ M, ∀ ω, |(fun ω => im1 ω - ρ) ω| ≤ M :=
    ⟨M1 + |ρ|, fun ω => (abs_sub _ _).trans (by linarith [hM1 ω])⟩
  have hk0a : 𝔼.E 0 (fun ω => im1 ω - ρ) = fun ω => im1 ω - ρ := by
    rw [Ex2_2.E_sub_const, him1a]
  obtain ⟨k, x, hs, hk0, hxa, ⟨Mk, hMk⟩, hxb⟩ := saddle_exists 𝔼 (b11 := φi)
    (b12 := (1 - φi) * φπ) (b21 := φi) (b22 := (1 - φi) * φπ) (μ := φi + (1 - φi) * φπ)
    (w1 := φi) (w2 := (1 - φi) * φπ) (by ring) (by ring) hκ hlam
    (by rw [show φi + (1 - φi) * φπ - (φi + (1 - φi) * φπ) = 0 by ring, abs_zero]; exact one_pos)
    ⟨0, fun t ω => by simp⟩ hf2b (fun t => 𝔼.const t 0) hf2a hk0b hk0a
  have hkn := pred_known 𝔼 hs (by rw [hk0]; exact hk0a) hxa (fun t => 𝔼.const t 0)
  set i : ℕ → Ω → ℝ := fun t ω => ρ + k (t + 1) ω with hi
  have hlag : (fun t ω => lagI im1 i t ω - ρ) = k := by
    funext t ω
    cases t with
    | zero => simp only [lagI_zero]; rw [hk0]
    | succ t => simp only [lagI_succ, hi]; ring
  refine ⟨i, x, ?_, fun t => ?_, hxa, ⟨|ρ| + Mk, fun t ω => ?_⟩, hxb⟩
  · rw [pa_iff_system, hlag]
    exact hs
  · change 𝔼.E t ((fun _ => ρ) + k (t + 1)) = (fun _ => ρ) + k (t + 1)
    rw [map_add, 𝔼.const, (hkn t).2]
  · exact (abs_add_le _ _).trans (by linarith [hMk (t + 1) ω])

/-- Galí (2015), Exercise 2.3(a): in an equilibrium with an adapted real rate,
`E_t i_{t+1} − ρ = λ(i_t − ρ) − κ(r_t − ρ)` with `λ = φ_i + κ`, `κ = (1 − φ_i)φ_π`: the
interest rate obeys a scalar forward equation. -/
theorem pa_interest_eq {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (t : ℕ) (ω : Ω) :
    𝔼.E t (i (t + 1)) ω - ρ = (φi + (1 - φi) * φπ) * (i t ω - ρ) - (1 - φi) * φπ * (r t ω - ρ) := by
  have hia := pa_i_adapted 𝔼 hra heq
  have hfun : i (t + 1) = (fun _ => (1 - φi) * ρ) + φi • i t + ((1 - φi) * φπ) • infl (t + 1) := by
    funext ω'
    rw [heq.2 (t + 1) ω']
    simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_add, map_smul, map_smul, 𝔼.const, hia t]
  have hf := congrFun (heq.1 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf ⊢
  rw [show 𝔼.E t (infl (t + 1)) ω = i t ω - r t ω by linarith]
  ring

/-- Galí (2015), Exercise 2.3(a) (**solution for the interest rate**): for `0 ≤ φ_i < 1` and
`φ_π > 1`, in any bounded equilibrium with bounded adapted `r̂ = r − ρ`,
`i_t − ρ = ∑_{k ≥ 0} λ^{−k} E_t[λ^{−1} κ r̂_{t+k}]`, `λ = φ_i + κ > 1`, `κ = (1 − φ_i)φ_π`. -/
theorem pa_interest_forward {φi φπ ρ M : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1) (hφπ : 1 < φπ)
    {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ} (hr : ∀ t ω, |r t ω - ρ| ≤ M)
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (hib : BoundedProc i) :
    (fun t ω => i t ω - ρ) = 𝔼.forwardSeries (φi + (1 - φi) * φπ)⁻¹
      (fun t => ((φi + (1 - φi) * φπ)⁻¹ * ((1 - φi) * φπ)) • fun ω => r t ω - ρ) := by
  set lam := φi + (1 - φi) * φπ with hlam
  set κ := (1 - φi) * φπ with hκ
  have hlam1 : 1 < lam := by
    have : 0 < (1 - φi) * (φπ - 1) := mul_pos (by linarith) (by linarith)
    rw [hlam]
    nlinarith
  have ha0 : 0 ≤ lam⁻¹ := inv_nonneg.2 (by linarith)
  have ha1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
  have hu : ∀ t ω, |((lam⁻¹ * κ) • fun ω => r t ω - ρ) ω| ≤ |lam⁻¹ * κ| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    gcongr
    exact hr t ω
  have hua : 𝔼.Adapted (fun t => (lam⁻¹ * κ) • fun ω => r t ω - ρ) := fun t => by
    rw [map_smul, Ex2_2.E_sub_const, hra t]
  obtain ⟨Mi, hMi⟩ := hib
  refine 𝔼.eq_forwardSeries ha0 ha1 hu hua (fun t => funext fun ω => ?_)
    ⟨Mi + |ρ|, fun t ω => (abs_sub _ _).trans (by linarith [hMi t ω])⟩
  have h := pa_interest_eq 𝔼 hra heq t ω
  have hE : 𝔼.E t (fun ω => i (t + 1) ω - ρ) ω = 𝔼.E t (i (t + 1)) ω - ρ :=
    congrFun (Ex2_2.E_sub_const 𝔼 t (i (t + 1)) ρ) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hE, h]
  field_simp
  ring

/-- Galí (2015), Exercise 2.3(a) (**equilibrium inflation**): the rule gives
`κ π_t = (i_t − ρ) − φ_i (i_{t−1} − ρ)`, `κ = (1 − φ_i)φ_π`, so with `i` from
`pa_interest_forward`, `π_t = (î_t − φ_i î_{t−1})/κ`. -/
theorem pa_inflation_eq {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (t : ℕ) (ω : Ω) :
    (1 - φi) * φπ * infl t ω = (i t ω - ρ) - φi * (lagI im1 i t ω - ρ) := by
  rw [heq.2 t ω]
  ring

/-- Galí (2015), Exercise 2.3(a): determinacy of the partial-adjustment rule: for every bounded
adapted real rate and every bounded `i_{−1}` known at date 0 there is exactly one bounded
adapted equilibrium. -/
def PADeterminate (φi φπ ρ : ℝ) : Prop :=
  ∀ (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ), BoundedProc r → 𝔼.Adapted r → (∃ M, ∀ ω, |im1 ω| ≤ M) →
    𝔼.E 0 im1 = im1 →
    (∃ i infl, PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl) ∧
    ∀ i infl i' infl', PAEquilibrium 𝔼 φi φπ ρ r im1 i infl →
      PAEquilibrium 𝔼 φi φπ ρ r im1 i' infl' → 𝔼.Adapted infl → 𝔼.Adapted infl' →
      BoundedProc i → BoundedProc infl → BoundedProc i' → BoundedProc infl' →
      i = i' ∧ infl = infl'

/-- Galí (2015), Exercise 2.3(a) (**self-fulfilling deviation**): with `r_t = ρ` and
`i_{−1} = ρ`, besides `(i, π) = (ρ, 0)` the deterministic path `π_0 = 1`,
`π_{t+1} = κ λᵗ`, `i_t = ρ + κ λᵗ` is an equilibrium (`κ = (1 − φ_i)φ_π`, `λ = φ_i + κ`). -/
theorem pa_two_solutions (φi φπ ρ : ℝ) :
    PAEquilibrium 𝔼 φi φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ) (fun _ _ => 0) ∧
      PAEquilibrium 𝔼 φi φπ ρ (fun _ _ => ρ) (fun _ => ρ)
        (fun t _ => ρ + (1 - φi) * φπ * (φi + (1 - φi) * φπ) ^ t)
        (fun t _ => if t = 0 then 1 else (1 - φi) * φπ * (φi + (1 - φi) * φπ) ^ (t - 1)) := by
  refine ⟨⟨fun t => ?_, fun t ω => ?_⟩, ⟨fun t => ?_, fun t ω => ?_⟩⟩
  · rw [𝔼.const]
    funext ω
    simp
  · cases t <;> simp [lagI_zero, lagI_succ] <;> ring
  · rw [𝔼.const]
    funext ω
    simp
  · cases t with
    | zero => simp [lagI_zero]; ring
    | succ t => simp [lagI_succ, pow_succ]; ring

/-- Galí (2015), Exercise 2.3(a) (**indeterminacy for `|λ| ≤ 1`**): for
`|φ_i + (1 − φ_i)φ_π| ≤ 1` the partial-adjustment rule is not determinate. -/
theorem pa_not_determinate [Nonempty Ω] {φi φπ ρ : ℝ} (hlam : |φi + (1 - φi) * φπ| ≤ 1) :
    ¬ PADeterminate 𝔼 φi φπ ρ := by
  intro hdet
  obtain ⟨h0, h1⟩ := pa_two_solutions 𝔼 φi φπ ρ
  set κ := (1 - φi) * φπ
  set lam := φi + (1 - φi) * φπ
  have hpow : ∀ t : ℕ, |κ * lam ^ t| ≤ |κ| := fun t => by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hlam)
  have hu := (hdet (fun _ _ => ρ) (fun _ => ρ) ⟨|ρ|, fun t ω => le_rfl⟩ (fun t => 𝔼.const t ρ)
    ⟨|ρ|, fun ω => le_rfl⟩ (𝔼.const 0 ρ)).2 _ _ _ _ h0 h1 (fun t => 𝔼.const t 0)
    (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩ ⟨0, fun t ω => by simp⟩
    ⟨|ρ| + |κ|, fun t ω => (abs_add_le _ _).trans (by linarith [hpow t])⟩
    ⟨1 + |κ|, fun t ω => ?_⟩
  · have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
    simp at this
  · cases t with
    | zero => simp
    | succ t => simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; linarith [hpow t]

/-- Galí (2015), Exercise 2.3(a) (**determinacy criterion**): for `0 ≤ φ_i < 1` the rule of
partial adjustment is determinate iff `|φ_i + (1 − φ_i)φ_π| > 1`. -/
theorem pa_determinate_iff [Nonempty Ω] {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1) :
    PADeterminate 𝔼 φi φπ ρ ↔ 1 < |φi + (1 - φi) * φπ| := by
  constructor
  · intro hdet
    by_contra h
    exact pa_not_determinate 𝔼 (not_lt.1 h) hdet
  · intro hlam r im1 hrb hra him1 him1a
    exact ⟨pa_exists 𝔼 hφi0 hφi1 hlam hrb hra him1 him1a,
      fun i infl i' infl' heq heq' hx hx' hib hxb hib' hxb' =>
        pa_unique 𝔼 hφi0 hφi1 hlam him1 him1a heq heq' hx hx' hib hxb hib' hxb'⟩

/-- Galí (2015), Exercise 2.3(a) (**the book's answer**): for `0 ≤ φ_i < 1` and `φ_π ≥ 0` the
rule of partial adjustment is determinate iff `φ_π > 1`. -/
theorem pa_determinate_iff_of_nonneg [Nonempty Ω] {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi)
    (hφi1 : φi < 1) (hφπ : 0 ≤ φπ) : PADeterminate 𝔼 φi φπ ρ ↔ 1 < φπ := by
  rw [pa_determinate_iff 𝔼 hφi0 hφi1, abs_of_nonneg (by positivity)]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

/-- Galí (2015), Exercise 2.3(a) (**correction**: the book allows `φ_i ∈ [0, 1]`): for
`φ_i = 1` the rule is `i_t = i_{t−1}` and the equilibrium is never unique, whatever `φ_π`:
with `r_t = i_{−1} = ρ`, both `π ≡ 0` and `π_0 = 1, π_{t+1} = 0` are bounded equilibria. -/
theorem pa_phi_i_one_not_determinate [Nonempty Ω] (φπ ρ : ℝ) : ¬ PADeterminate 𝔼 1 φπ ρ := by
  intro hdet
  have h0 : PAEquilibrium 𝔼 1 φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ) (fun _ _ => 0) :=
    ⟨fun t => by rw [𝔼.const]; funext ω; simp,
      fun t ω => by cases t <;> simp [lagI_zero, lagI_succ]⟩
  have h1 : PAEquilibrium 𝔼 1 φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ)
      (fun t _ => if t = 0 then 1 else 0) :=
    ⟨fun t => by rw [𝔼.const]; funext ω; simp,
      fun t ω => by cases t <;> simp [lagI_zero, lagI_succ]⟩
  have hu := (hdet (fun _ _ => ρ) (fun _ => ρ) ⟨|ρ|, fun t ω => le_rfl⟩ (fun t => 𝔼.const t ρ)
    ⟨|ρ|, fun ω => le_rfl⟩ (𝔼.const 0 ρ)).2 _ _ _ _ h0 h1 (fun t => 𝔼.const t 0)
    (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩ ⟨0, fun t ω => by simp⟩
    ⟨|ρ|, fun t ω => le_rfl⟩ ⟨1, fun t ω => by dsimp only; split_ifs <;> simp⟩
  have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
  simp at this

/-- Galí (2015), Exercise 2.3(a) (**non-existence at the boundary**): for `0 ≤ φ_i < 1`,
`φ_π = 1` (so `λ = 1`) and the constant real rate `r_t = ρ + 1`, there is no bounded
equilibrium: `E_0 i_t − ρ = (i_0 − ρ) − (1 − φ_i) t` drifts. -/
theorem pa_boundary_nonexistence [Nonempty Ω] {φi ρ : ℝ} (hφi1 : φi < 1) (im1 : Ω → ℝ)
    {i infl : ℕ → Ω → ℝ} (heq : PAEquilibrium 𝔼 φi 1 ρ (fun _ _ => ρ + 1) im1 i infl) :
    ¬ BoundedProc i := by
  rintro ⟨M, hM⟩
  have hra : 𝔼.Adapted (fun _ _ => ρ + 1) := fun t => 𝔼.const t _
  have hia := pa_i_adapted 𝔼 hra heq
  have hstep : ∀ t ω, 𝔼.E t (i (t + 1)) ω = i t ω - (1 - φi) := by
    intro t ω
    have := pa_interest_eq 𝔼 hra heq t ω
    linarith
  have hdrift : ∀ t ω, 𝔼.E 0 (i t) ω = i 0 ω - (1 - φi) * t := by
    intro t
    induction t with
    | zero => intro ω; rw [hia 0]; simp
    | succ t ih =>
      intro ω
      rw [← 𝔼.tower (Nat.zero_le t)]
      have : 𝔼.E t (i (t + 1)) = i t - fun _ => 1 - φi := funext fun ω => by
        rw [hstep t ω]; rfl
      rw [this, map_sub, 𝔼.const]
      simp only [Pi.sub_apply]
      rw [ih ω]
      push_cast
      ring
  set ω := Classical.arbitrary Ω
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / (1 - φi))
  have h1 := 𝔼.abs_E_le (hM n) 0 ω
  rw [hdrift n ω] at h1
  have h2 := hM 0 ω
  rw [div_lt_iff₀ (by linarith)] at hn
  have h3 := neg_abs_le (i 0 ω - (1 - φi) * n)
  have h4 := le_abs_self (i 0 ω)
  nlinarith

/-! ### b–c. Moving-average inflation targeting -/

/-- Galí (2015), Exercise 2.3(b), p. 48: inflation over the whole past: `π_s` for dates
`s ≥ 0` and the pre-sample history `π_{−1−j} = h_j`. -/
def extInfl (infl h : ℕ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun s => if 0 ≤ s then infl s.toNat else h (-s - 1).toNat

/-- Galí (2015), Exercise 2.3(b), p. 48: the moving average
`π̄_s = (1 − δ) ∑_{k ≥ 0} δᵏ π_{s−k}` (a genuine infinite sum). -/
noncomputable def maBar (δ : ℝ) (e : ℤ → Ω → ℝ) (s : ℤ) : Ω → ℝ :=
  fun ω => (1 - δ) * ∑' k : ℕ, δ ^ k * e (s - k) ω

/-- Galí (2015), Exercise 2.3(b): the pre-sample moving average
`π̄_{−1} = (1 − δ) ∑_{j ≥ 0} δʲ h_j`. -/
noncomputable def hbar (δ : ℝ) (h : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => (1 - δ) * ∑' j : ℕ, δ ^ j * h j ω

/-- Galí (2015), Exercise 2.3(b)–(c), p. 48: for `0 ≤ δ < 1` and bounded inflation,
`π̄_s = δ π̄_{s−1} + (1 − δ) π_s`. -/
theorem maBar_succ {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {e : ℤ → Ω → ℝ}
    (he : ∀ s ω, |e s ω| ≤ M) (s : ℤ) (ω : Ω) :
    maBar δ e s ω = δ * maBar δ e (s - 1) ω + (1 - δ) * e s ω := by
  have hsum : Summable (fun k : ℕ => δ ^ k * e (s - k) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ0]
      exact mul_le_mul_of_nonneg_left (he _ ω) (pow_nonneg hδ0 k))
  unfold maBar
  rw [hsum.tsum_eq_zero_add]
  have e1 : ∑' k : ℕ, δ ^ (k + 1) * e (s - ((k + 1 : ℕ) : ℤ)) ω
      = δ * ∑' k : ℕ, δ ^ k * e (s - 1 - k) ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show s - ((k + 1 : ℕ) : ℤ) = s - 1 - k by push_cast; ring, pow_succ]
    ring
  rw [e1]
  simp
  ring

/-- Galí (2015), Exercise 2.3(b): at the sample dates the extended path is `π`. -/
theorem extInfl_nat (infl h : ℕ → Ω → ℝ) (t : ℕ) : extInfl infl h t = infl t := by
  simp [extInfl]

/-- Galí (2015), Exercise 2.3(b): before the sample the extended path is the history `h`. -/
theorem extInfl_neg (infl h : ℕ → Ω → ℝ) (j : ℕ) : extInfl infl h (-1 - j) = h j := by
  have h1 : ¬ (0 : ℤ) ≤ -1 - j := by omega
  have h2 : (-(-1 - (j : ℤ)) - 1).toNat = j := by omega
  simp only [extInfl, h1, ↓reduceIte, h2]

/-- Galí (2015), Exercise 2.3(b): `π̄_{−1}` depends only on the pre-sample history. -/
theorem maBar_neg_one (δ : ℝ) (infl h : ℕ → Ω → ℝ) (ω : Ω) :
    maBar δ (extInfl infl h) (-1) ω = hbar δ h ω := by
  unfold maBar hbar
  congr 1
  refine tsum_congr fun k => ?_
  rw [extInfl_neg]

/-- Galí (2015), Exercise 2.3(b): a bound for the extended inflation path. -/
theorem extInfl_bounded {infl h : ℕ → Ω → ℝ} {M1 M2 : ℝ} (h1 : ∀ t ω, |infl t ω| ≤ M1)
    (h2 : ∀ j ω, |h j ω| ≤ M2) : ∀ s ω, |extInfl infl h s ω| ≤ max M1 M2 := by
  intro s ω
  unfold extInfl
  split_ifs
  · exact (h1 _ ω).trans (le_max_left _ _)
  · exact (h2 _ ω).trans (le_max_right _ _)

/-- Galí (2015), Exercise 2.3(c), p. 48 (**equivalence of the two rules**): for `0 ≤ δ < 1` and
bounded inflation and history, `i_t = ρ + φ_π π̄_t` at every date iff
`i_t = δ i_{t−1} + (1 − δ)(ρ + φ_π π_t)` at every date with `i_{−1} = ρ + φ_π π̄_{−1}`: the
moving-average rule is the partial-adjustment rule with `φ_i = δ`. -/
theorem ma_iff_pa {δ φπ ρ M1 M2 : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {infl h : ℕ → Ω → ℝ}
    (h1 : ∀ t ω, |infl t ω| ≤ M1) (h2 : ∀ j ω, |h j ω| ≤ M2) (i : ℕ → Ω → ℝ) :
    (∀ t ω, i t ω = ρ + φπ * maBar δ (extInfl infl h) t ω) ↔
      ∀ t ω, i t ω = δ * lagI (fun ω => ρ + φπ * hbar δ h ω) i t ω
        + (1 - δ) * (ρ + φπ * infl t ω) := by
  have hb := extInfl_bounded h1 h2
  have hrec : ∀ (t : ℕ) ω, maBar δ (extInfl infl h) t ω
      = δ * maBar δ (extInfl infl h) ((t : ℤ) - 1) ω + (1 - δ) * infl t ω := by
    intro t ω
    rw [maBar_succ hδ0 hδ1 hb, extInfl_nat]
  constructor
  · intro hma t ω
    rw [hma t ω, hrec t ω]
    cases t with
    | zero =>
      simp only [lagI_zero, Nat.cast_zero, zero_sub]
      rw [maBar_neg_one]
      ring
    | succ t =>
      simp only [lagI_succ]
      rw [show ((t + 1 : ℕ) : ℤ) - 1 = t by push_cast; ring, hma t ω]
      ring
  · intro hpa t
    induction t with
    | zero =>
      intro ω
      rw [hpa 0 ω, hrec 0 ω]
      simp only [lagI_zero, Nat.cast_zero, zero_sub]
      rw [maBar_neg_one]
      ring
    | succ t ih =>
      intro ω
      rw [hpa (t + 1) ω, hrec (t + 1) ω]
      simp only [lagI_succ]
      rw [show ((t + 1 : ℕ) : ℤ) - 1 = t by push_cast; ring, ih ω]
      ring

/-- Galí (2015), Exercise 2.3(b), p. 48: equilibrium under the moving-average rule
`i_t = ρ + φ_π π̄_t` with the Fisher equation, given the pre-sample history `h`. -/
def MAEquilibrium (δ φπ ρ : ℝ) (r h i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t = r t + 𝔼.E t (infl (t + 1))) ∧
    ∀ t ω, i t ω = ρ + φπ * maBar δ (extInfl infl h) t ω

/-- Galí (2015), Exercise 2.3(c), p. 48: for bounded inflation and history the moving-average
equilibria are exactly the partial-adjustment equilibria with `φ_i = δ` and
`i_{−1} = ρ + φ_π π̄_{−1}`. -/
theorem ma_equilibrium_iff_pa {δ φπ ρ M1 M2 : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {r h i infl : ℕ → Ω → ℝ} (h1 : ∀ t ω, |infl t ω| ≤ M1) (h2 : ∀ j ω, |h j ω| ≤ M2) :
    MAEquilibrium 𝔼 δ φπ ρ r h i infl ↔
      PAEquilibrium 𝔼 δ φπ ρ r (fun ω => ρ + φπ * hbar δ h ω) i infl :=
  and_congr_right fun _ => ma_iff_pa hδ0 hδ1 h1 h2 i

/-- Galí (2015), Exercise 2.3(c): conversely, for `φ_π ≠ 0` every initial condition `i_{−1}` of
the partial-adjustment rule is produced by a moving-average history (the constant history
`h_j = (i_{−1} − ρ)/φ_π`). -/
theorem pa_as_ma {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hφπ : φπ ≠ 0) (im1 : Ω → ℝ) :
    (fun ω => ρ + φπ * hbar δ (fun _ ω => (im1 ω - ρ) / φπ) ω) = im1 := by
  funext ω
  unfold hbar
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
  have : (1 - δ) ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), Exercise 2.3(b): bounds for the pre-sample moving average. -/
theorem hbar_bounded {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ℕ → Ω → ℝ}
    (hh : ∀ j ω, |h j ω| ≤ M) (ω : Ω) : |hbar δ h ω| ≤ M := by
  unfold hbar
  have hs : HasSum (fun k : ℕ => δ ^ k * M) ((1 - δ)⁻¹ * M) :=
    (hasSum_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hb := tsum_of_norm_bounded (f := fun j => δ ^ j * h j ω) hs (fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_left (hh k ω) (pow_nonneg hδ0 k))
  rw [Real.norm_eq_abs] at hb
  have h1 : 0 < 1 - δ := by linarith
  rw [abs_mul, abs_of_pos h1]
  calc (1 - δ) * |∑' j, δ ^ j * h j ω| ≤ (1 - δ) * ((1 - δ)⁻¹ * M) := by gcongr
    _ = M := by field_simp

/-- Galí (2015), Exercise 2.3(b): a pre-sample history known at date 0 gives `π̄_{−1}` known at
date 0. -/
theorem hbar_known {δ M ρ φπ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ℕ → Ω → ℝ}
    (hh : ∀ j ω, |h j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (h j) = h j) :
    𝔼.E 0 (fun ω => ρ + φπ * hbar δ h ω) = fun ω => ρ + φπ * hbar δ h ω := by
  have hfun : (fun ω => ρ + φπ * hbar δ h ω)
      = (fun _ => ρ) + (φπ * (1 - δ)) • fun ω => ∑' j : ℕ, δ ^ j * h j ω := by
    funext ω
    simp only [hbar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_smul, 𝔼.const]
  congr 2
  funext ω
  rw [𝔼.E_tsum hδ0 hδ1 (f := fun j ω => δ ^ j * h j ω) (M := M) (fun k ω => by
    rw [abs_mul, abs_pow, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_left (hh k ω) (pow_nonneg hδ0 k)) 0 ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E 0 (δ ^ k • h k) ω = _
  rw [map_smul, hha k]
  rfl

/-- Galí (2015), Exercise 2.3(b): determinacy of the moving-average rule: for every bounded
adapted real rate and every bounded pre-sample history known at date 0 there is exactly one
bounded adapted equilibrium. -/
def MADeterminate (δ φπ ρ : ℝ) : Prop :=
  ∀ (r h : ℕ → Ω → ℝ), BoundedProc r → 𝔼.Adapted r → BoundedProc h →
    (∀ j, 𝔼.E 0 (h j) = h j) →
    (∃ i infl, MAEquilibrium 𝔼 δ φπ ρ r h i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl) ∧
    ∀ i infl i' infl', MAEquilibrium 𝔼 δ φπ ρ r h i infl →
      MAEquilibrium 𝔼 δ φπ ρ r h i' infl' → 𝔼.Adapted infl → 𝔼.Adapted infl' →
      BoundedProc i → BoundedProc infl → BoundedProc i' → BoundedProc infl' →
      i = i' ∧ infl = infl'

/-- Galí (2015), Exercise 2.3(b) (**determinacy criterion**): for `0 ≤ δ < 1` the
moving-average rule is determinate iff `|δ + (1 − δ)φ_π| > 1`. -/
theorem ma_determinate_iff [Nonempty Ω] {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    MADeterminate 𝔼 δ φπ ρ ↔ 1 < |δ + (1 - δ) * φπ| := by
  constructor
  · intro hdet
    by_contra hlam
    push Not at hlam
    obtain ⟨p0, p1⟩ := pa_two_solutions 𝔼 δ φπ ρ
    have hh0 : (fun (ω : Ω) => ρ + φπ * hbar δ (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) ω)
        = fun _ => ρ := by
      funext ω
      simp [hbar]
    set κ := (1 - δ) * φπ
    set lam := δ + (1 - δ) * φπ
    have hpow : ∀ t : ℕ, |κ * lam ^ t| ≤ |κ| := fun t => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hlam)
    have hb1 : ∀ t (ω : Ω), |(if t = 0 then 1 else κ * lam ^ (t - 1))| ≤ 1 + |κ| := by
      intro t ω
      cases t with
      | zero => simp
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        linarith [hpow t]
    have m0 : MAEquilibrium 𝔼 δ φπ ρ (fun _ _ => ρ) (fun _ _ => 0) (fun _ _ => ρ)
        (fun _ _ => 0) := by
      rw [ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 (M1 := 0) (M2 := 0) (fun t ω => by simp)
        (fun j ω => by simp), hh0]
      exact p0
    have m1 : MAEquilibrium 𝔼 δ φπ ρ (fun _ _ => ρ) (fun _ _ => 0)
        (fun t _ => ρ + κ * lam ^ t) (fun t _ => if t = 0 then 1 else κ * lam ^ (t - 1)) := by
      rw [ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 (M1 := 1 + |κ|) (M2 := 0) (fun t ω => hb1 t ω)
        (fun j ω => by simp), hh0]
      exact p1
    have hu := (hdet (fun _ _ => ρ) (fun _ _ => 0) ⟨|ρ|, fun t ω => le_rfl⟩
      (fun t => 𝔼.const t ρ) ⟨0, fun t ω => by simp⟩ (fun j => 𝔼.const 0 0)).2 _ _ _ _ m0 m1
      (fun t => 𝔼.const t 0) (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩
      ⟨0, fun t ω => by simp⟩
      ⟨|ρ| + |κ|, fun t ω => (abs_add_le _ _).trans (by linarith [hpow t])⟩
      ⟨1 + |κ|, hb1⟩
    have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
    simp at this
  · intro hlam r h hrb hra ⟨Mh, hMh⟩ hha
    have him1 : ∃ M, ∀ ω, |(fun ω => ρ + φπ * hbar δ h ω) ω| ≤ M :=
      ⟨|ρ| + |φπ| * Mh, fun ω => (abs_add_le _ _).trans (by
        rw [abs_mul]
        gcongr
        exact hbar_bounded hδ0 hδ1 hMh ω)⟩
    have him1a := hbar_known 𝔼 (ρ := ρ) (φπ := φπ) hδ0 hδ1 hMh hha
    refine ⟨?_, fun i infl i' infl' heq heq' hx hx' hib hxb hib' hxb' => ?_⟩
    · obtain ⟨i, infl, heq, hia, hxa, hib, ⟨Mx, hMx⟩⟩ :=
        pa_exists 𝔼 hδ0 hδ1 hlam hrb hra him1 him1a
      exact ⟨i, infl, (ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx hMh).2 heq, hia, hxa, hib,
        ⟨Mx, hMx⟩⟩
    · obtain ⟨Mx, hMx⟩ := hxb
      obtain ⟨Mx', hMx'⟩ := hxb'
      exact pa_unique 𝔼 hδ0 hδ1 hlam him1 him1a
        ((ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx hMh).1 heq)
        ((ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx' hMh).1 heq') hx hx' hib ⟨Mx, hMx⟩ hib'
        ⟨Mx', hMx'⟩

/-- Galí (2015), Exercise 2.3(b) (**the book's answer**): for `0 ≤ δ < 1` and `φ_π ≥ 0` the
moving-average rule is determinate iff `φ_π > 1`. -/
theorem ma_determinate_iff_of_nonneg [Nonempty Ω] {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hφπ : 0 ≤ φπ) : MADeterminate 𝔼 δ φπ ρ ↔ 1 < φπ := by
  rw [ma_determinate_iff 𝔼 hδ0 hδ1, abs_of_nonneg (by positivity)]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

end Gali.ClassicalMonetaryModel.Ex2_3
