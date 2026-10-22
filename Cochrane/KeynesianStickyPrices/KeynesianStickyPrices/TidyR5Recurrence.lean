/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.FullModelTidy

/-!
# Second-order recursions: explosions, boundedness and decay, for every coefficient pair

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2, p. 421 (real
explosions) and Online Appendix A1, eq. (1.57), p. 587 (the eigenvalues of the deviation
system are the roots of `λ² − tr λ + det`).

FullModelTidy characterised the solutions of `y_{t+2} = A y_{t+1} − B y_t` only for the
coefficient pairs that arise with `φ_x = 0`. With an output response, `A` and `B` range over all
of `ℝ²`, so this module proves the three characterisations for **every** real `A`, `B`
(`Rec A B y`):

* `exists_atTop_iff`: some solution tends to `+∞` iff `1 − A + B < 0` (a real root above one)
  or `2 ≤ A` and `4B ≤ A²` (a real root at least one, with the double root `1` giving
  `y_t = t`); `exists_atBot_iff` is the same condition.
* `exists_unbounded_iff`: some solution is unbounded iff `B > 1`, `1 + B < |A|` or
  `B = 1 ∧ |A| = 2` (a root outside the closed unit disc, or a double root `±1`).
* `exists_not_tendsto_zero_iff`: some solution does not tend to zero iff the Schur–Cohn
  condition `|B| < 1 ∧ |A| < 1 + B` fails (`tendsto_zero_of_schur` is the sufficiency half,
  through the companion matrix and `tendsto_pow_entry`).

The proofs use the invariant quadratic form of FullModelTidy for complex roots, and for real
roots `μ₁ ≥ μ₂` the first-order modes `y_{t+1} − μ₂ y_t = μ₁ᵗ (y_1 − μ₂ y_0)` and
`y_{t+1} − μ₁ y_t = μ₂ᵗ (y_1 − μ₁ y_0)` (`mode_pow`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5Recurrence

open Filter Topology FullModelTidy

/-- Cochrane (2023), A1 (1.57), p. 587: `y` solves `y_{t+2} = A y_{t+1} − B y_t` (`A` the trace,
`B` the determinant of the transition matrix). -/
def Rec (A B : ℝ) (y : ℕ → ℝ) : Prop := ∀ t, y (t + 2) = A * y (t + 1) - B * y t

/-- Cochrane (2023), A1 (1.57): the solution of `y_{t+2} = A y_{t+1} − B y_t` from `y_0 = a`,
`y_1 = b`. -/
def recSeq (A B a b : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | t + 2 => A * recSeq A B a b (t + 1) - B * recSeq A B a b t

/-- Cochrane (2023), A1 (1.57): `recSeq` solves the recursion. -/
theorem recSeq_rec (A B a b : ℝ) : Rec A B (recSeq A B a b) := fun t => by
  simp only [recSeq]

/-- Cochrane (2023), A1 (1.57): two solutions with the same `y_0`, `y_1` coincide. -/
theorem rec_ext {A B : ℝ} {y z : ℕ → ℝ} (hy : Rec A B y) (hz : Rec A B z) (h0 : y 0 = z 0)
    (h1 : y 1 = z 1) : y = z := by
  have key : ∀ t, y t = z t ∧ y (t + 1) = z (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [hy t, hz t, ih.1, ih.2]
  funext t
  exact (key t).1

/-- Cochrane (2023), A1 (1.57): a root `μ` of `μ² − Aμ + B` gives the solution `c μᵗ`. -/
theorem geom_rec {A B μ : ℝ} (hμ : μ ^ 2 = A * μ - B) (c : ℝ) :
    Rec A B (fun t => c * μ ^ t) := fun t => by
  simp only [pow_succ]
  linear_combination (c * μ ^ t) * hμ

/-- Cochrane (2023), A1 (1.57): the double root `1` (`A = 2`, `B = 1`) gives `y_t = t`. -/
theorem lin_rec : Rec 2 1 (fun t => (t : ℝ)) := fun t => by
  push_cast
  ring

/-- Cochrane (2023), A1 (1.57): the double root `−1` (`A = −2`, `B = 1`) gives
`y_t = t (−1)ᵗ`. -/
theorem altlin_rec : Rec (-2) 1 (fun t => (t : ℝ) * (-1) ^ t) := fun t => by
  push_cast
  simp only [pow_succ]
  ring

/-- Cochrane (2023), A1 (1.57): for real roots `μ₁ + μ₂ = A`, `μ₁ μ₂ = B`, the mode
`y_{t+1} − μ₂ y_t` is `μ₁ᵗ (y_1 − μ₂ y_0)`. -/
theorem mode_pow {A B m1 m2 : ℝ} (hs : m1 + m2 = A) (hp : m1 * m2 = B) {y : ℕ → ℝ}
    (hy : Rec A B y) (t : ℕ) : y (t + 1) - m2 * y t = m1 ^ t * (y 1 - m2 * y 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hy t, pow_succ, ← hs, ← hp]
    linear_combination m1 * ih

/-- The real roots `(A ± √(A² − 4B))/2` when `4B ≤ A²`: their sum is `A`, their product `B`,
and they are ordered. -/
theorem real_roots {A B : ℝ} (hD : 4 * B ≤ A ^ 2) :
    (A + Real.sqrt (A ^ 2 - 4 * B)) / 2 + (A - Real.sqrt (A ^ 2 - 4 * B)) / 2 = A ∧
      (A + Real.sqrt (A ^ 2 - 4 * B)) / 2 * ((A - Real.sqrt (A ^ 2 - 4 * B)) / 2) = B ∧
      (A - Real.sqrt (A ^ 2 - 4 * B)) / 2 ≤ (A + Real.sqrt (A ^ 2 - 4 * B)) / 2 := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A ^ 2 - 4 * B)
  have h0 := Real.sqrt_nonneg (A ^ 2 - 4 * B)
  refine ⟨by ring, by linear_combination (-1 / 4 : ℝ) * hs, by linarith⟩

/-- Cochrane (2023), p. 421 and A1 (1.57): if `1 − A + B ≤ 0` the larger root
`(A + √(A² − 4B))/2` is real and at least one, strictly above one if `1 − A + B < 0`. -/
theorem root_ge_one {A B : ℝ} (h : 1 - A + B ≤ 0) :
    4 * B ≤ A ^ 2 ∧ ((A + Real.sqrt (A ^ 2 - 4 * B)) / 2) ^ 2 =
      A * ((A + Real.sqrt (A ^ 2 - 4 * B)) / 2) - B ∧
      1 ≤ (A + Real.sqrt (A ^ 2 - 4 * B)) / 2 ∧
      (1 - A + B < 0 → 1 < (A + Real.sqrt (A ^ 2 - 4 * B)) / 2) := by
  have hD : 4 * B ≤ A ^ 2 := by nlinarith [sq_nonneg (A - 2)]
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A ^ 2 - 4 * B)
  have h0 := Real.sqrt_nonneg (A ^ 2 - 4 * B)
  set s := Real.sqrt (A ^ 2 - 4 * B)
  refine ⟨hD, by linear_combination (1 / 4 : ℝ) * hs, ?_, fun hlt => ?_⟩
  · nlinarith
  · nlinarith

/-- Cochrane (2023), p. 421: if `1 − A + B < 0` there is a real root above one. -/
theorem exists_root_gt_one {A B : ℝ} (h : 1 - A + B < 0) :
    ∃ μ : ℝ, 1 < μ ∧ μ ^ 2 = A * μ - B := by
  obtain ⟨_, h2, _, h4⟩ := root_ge_one h.le
  exact ⟨_, h4 h, h2⟩

/-- Cochrane (2023), A1 (1.57): if `1 − A + B ≤ 0` there is a real root at least one. -/
theorem exists_root_ge_one {A B : ℝ} (h : 1 - A + B ≤ 0) :
    ∃ μ : ℝ, 1 ≤ μ ∧ μ ^ 2 = A * μ - B := by
  obtain ⟨_, h2, h3, _⟩ := root_ge_one h
  exact ⟨_, h3, h2⟩

/-- Cochrane (2023), A1 (1.57): if `1 + A + B < 0` there is a real root below `−1`. -/
theorem exists_root_lt_neg_one {A B : ℝ} (h : 1 + A + B < 0) :
    ∃ μ : ℝ, μ < -1 ∧ μ ^ 2 = A * μ - B := by
  obtain ⟨μ, h1, h2⟩ := exists_root_gt_one (A := -A) (B := B) (by linarith)
  exact ⟨-μ, by linarith, by linear_combination h2⟩

/-- Cochrane (2023), A1 (1.57): if `1 + A + B ≤ 0` there is a real root at most `−1`. -/
theorem exists_root_le_neg_one {A B : ℝ} (h : 1 + A + B ≤ 0) :
    ∃ μ : ℝ, μ ≤ -1 ∧ μ ^ 2 = A * μ - B := by
  obtain ⟨μ, h1, h2⟩ := exists_root_ge_one (A := -A) (B := B) (by linarith)
  exact ⟨-μ, by linarith, by linear_combination h2⟩

/-- `|μ|ᵗ` is unbounded for `|μ| > 1`, so `μᵗ` is. -/
theorem pow_unbounded {μ : ℝ} (hμ : 1 < |μ|) : ¬ ∃ M, ∀ t, |1 * μ ^ t| ≤ M := by
  rintro ⟨M, hM⟩
  have h := tendsto_pow_atTop_atTop_of_one_lt hμ
  obtain ⟨t, ht⟩ := (h.eventually_gt_atTop M).exists
  have := hM t
  rw [one_mul, abs_pow] at this
  linarith

/-- `μᵗ` does not tend to zero for `|μ| ≥ 1`. -/
theorem pow_not_tendsto_zero {μ : ℝ} (hμ : 1 ≤ |μ|) :
    ¬ Tendsto (fun t : ℕ => 1 * μ ^ t) atTop (𝓝 0) := by
  intro h
  have h' := (h.abs).eventually (gt_mem_nhds (show |(0 : ℝ)| < 1 / 2 by norm_num))
  obtain ⟨t, ht⟩ := h'.exists
  simp only [one_mul, abs_pow] at ht
  have : 1 ≤ |μ| ^ t := one_le_pow₀ hμ
  linarith

/-! ### Decay under Schur–Cohn -/

/-- Cochrane (2023), A1 (1.57), p. 587: under the Schur–Cohn condition `|B| < 1`,
`|A| < 1 + B` (both roots inside the unit circle) every solution tends to zero. The proof writes
`(y_{t+1}, y_t) = Cᵗ (y_1, y_0)` for the companion matrix `C = [[A, −B], [1, 0]]`. -/
theorem tendsto_zero_of_schur {A B : ℝ} (h : SchurStable A B) {y : ℕ → ℝ} (hy : Rec A B y) :
    Tendsto y atTop (𝓝 0) := by
  set C : Matrix (Fin 2) (Fin 2) ℝ := !![A, -B; 1, 0] with hC
  have htr : tr2 C = A := by simp [tr2, hC]
  have hdet : det2 C = B := by simp [det2, hC]
  have key : ∀ t, y (t + 1) = (C ^ t) 0 0 * y 1 + (C ^ t) 0 1 * y 0 ∧
      y t = (C ^ t) 1 0 * y 1 + (C ^ t) 1 1 * y 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e00 : (C ^ (t + 1)) 0 0 = A * (C ^ t) 0 0 - B * (C ^ t) 1 0 := by
        rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [hC]; ring
      have e01 : (C ^ (t + 1)) 0 1 = A * (C ^ t) 0 1 - B * (C ^ t) 1 1 := by
        rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [hC]; ring
      have e10 : (C ^ (t + 1)) 1 0 = (C ^ t) 0 0 := by
        rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [hC]
      have e11 : (C ^ (t + 1)) 1 1 = (C ^ t) 0 1 := by
        rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [hC]
      refine ⟨?_, by rw [e10, e11]; exact ih.1⟩
      rw [hy t, ih.1, ih.2, e00, e01]
      ring
  have hS : SchurStable (tr2 C) (det2 C) := by rw [htr, hdet]; exact h
  have h10 := tendsto_pow_entry hS 1 0
  have h11 := tendsto_pow_entry hS 1 1
  have hlim := (h10.mul_const (y 1)).add (h11.mul_const (y 0))
  rw [zero_mul, zero_mul, add_zero] at hlim
  exact hlim.congr fun t => (key t).2.symm

/-! ### Explosions to `+∞` -/

/-- Cochrane (2023), p. 421 ("real explosions … `βʲ x_{t+j} → ∞`"), for the recursion with
**any** coefficients: some solution of `y_{t+2} = A y_{t+1} − B y_t` tends to `+∞` iff
`1 − A + B < 0` or (`2 ≤ A` and `4B ≤ A²`). -/
theorem exists_atTop_iff (A B : ℝ) :
    (∃ y, Rec A B y ∧ Tendsto y atTop atTop) ↔ 1 - A + B < 0 ∨ (2 ≤ A ∧ 4 * B ≤ A ^ 2) := by
  constructor
  · rintro ⟨y, hy, ht⟩
    by_contra hc
    push Not at hc
    obtain ⟨hp, hc2⟩ := hc
    by_cases hD : A ^ 2 < 4 * B
    · exact complex_not_atTop hD hy ht
    push Not at hD
    have hA2 : A < 2 := by
      by_contra h
      push Not at h
      exact absurd (hc2 h) (not_lt.mpr hD)
    obtain ⟨hsum, hprod, hle⟩ := real_roots hD
    set m1 := (A + Real.sqrt (A ^ 2 - 4 * B)) / 2
    set m2 := (A - Real.sqrt (A ^ 2 - 4 * B)) / 2
    have hp' : 0 ≤ (1 - m1) * (1 - m2) := by nlinarith
    have hm1 : m1 ≤ 1 := by nlinarith
    have hm2 : m2 < 1 := by linarith
    obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually_gt_atTop 0)
    by_cases hneg : m1 < -1
    · -- both roots below `−1`: the mode `y_{t+1} − m₁ y_t` must alternate in sign
      have hz := mode_pow (by linarith : m2 + m1 = A) (by linarith : m2 * m1 = B) hy
      have z1 : 0 < y (T + 1) - m1 * y T := by
        have := hT T le_rfl; have := hT (T + 1) (by omega); nlinarith
      have z2 : 0 < y (T + 1 + 1) - m1 * y (T + 1) := by
        have := hT (T + 1) (by omega); have := hT (T + 1 + 1) (by omega); nlinarith
      rw [hz] at z1 z2
      rw [pow_succ] at z2
      have : m2 ^ T * (y 1 - m1 * y 0) * m2 < 0 :=
        mul_neg_of_pos_of_neg z1 (by linarith)
      linarith
    push Not at hneg
    have hw := mode_pow hsum hprod hy
    set w0 := y 1 - m2 * y 0
    have hwb : ∀ t, |m1 ^ t * w0| ≤ |w0| := fun t => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨hneg, hm1⟩))
    set c := max m2 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hc1 : c < 1 := max_lt hm2 one_pos
    set K := max (y T) (|w0| / (1 - c))
    have hK : |w0| ≤ (1 - c) * K := by
      have : |w0| / (1 - c) ≤ K := le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    have hbound : ∀ n, y (T + n) ≤ K := by
      intro n
      induction n with
      | zero => exact le_max_left _ _
      | succ n ih =>
        have hpos := hT (T + n) (by omega)
        have e := hw (T + n)
        have h1 : m2 * y (T + n) ≤ c * y (T + n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le
        have h2 := (le_abs_self (m1 ^ (T + n) * w0)).trans (hwb (T + n))
        have h3 : c * y (T + n) ≤ c * K := mul_le_mul_of_nonneg_left ih hc0
        rw [show T + (n + 1) = T + n + 1 by omega]
        nlinarith
    obtain ⟨t, ht'⟩ := eventually_atTop.mp (ht.eventually_gt_atTop K)
    have := hbound (t + T - T)
    rw [show T + (t + T - T) = t + T by omega] at this
    linarith [ht' (t + T) (by omega)]
  · rintro (h | ⟨h2, hD⟩)
    · obtain ⟨μ, hμ1, hμ⟩ := exists_root_gt_one h
      refine ⟨_, geom_rec hμ 1, ?_⟩
      simpa using tendsto_pow_atTop_atTop_of_one_lt hμ1
    · obtain ⟨hr, hm⟩ := root_of_disc hD
      by_cases h1 : 1 < (A + Real.sqrt (A ^ 2 - 4 * B)) / 2
      · refine ⟨_, geom_rec (μ := (A + Real.sqrt (A ^ 2 - 4 * B)) / 2)
          (by linear_combination hr) 1, ?_⟩
        simpa using tendsto_pow_atTop_atTop_of_one_lt h1
      · push Not at h1
        have hA : A = 2 := by linarith
        have hs0 : Real.sqrt (A ^ 2 - 4 * B) = 0 := by linarith
        have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A ^ 2 - 4 * B)
        rw [hs0] at hs
        have hB : B = 1 := by rw [hA] at hs; linarith
        subst hA hB
        exact ⟨_, lin_rec, tendsto_natCast_atTop_atTop⟩

/-- Cochrane (2023), p. 421: the recursion is linear, so some solution tends to `−∞` iff some
solution tends to `+∞`. -/
theorem exists_atBot_iff (A B : ℝ) :
    (∃ y, Rec A B y ∧ Tendsto y atTop atBot) ↔ 1 - A + B < 0 ∨ (2 ≤ A ∧ 4 * B ≤ A ^ 2) := by
  rw [← exists_atTop_iff]
  constructor
  · rintro ⟨y, hy, ht⟩
    exact ⟨fun t => -y t, fun t => by simp only [hy t]; ring, tendsto_neg_atBot_atTop.comp ht⟩
  · rintro ⟨y, hy, ht⟩
    exact ⟨fun t => -y t, fun t => by simp only [hy t]; ring, tendsto_neg_atTop_atBot.comp ht⟩

/-! ### Unbounded solutions -/

/-- Cochrane (2023), A1 (1.57): if `B ≤ 1`, `|A| ≤ 1 + B` and there is no double root `±1`,
every solution is bounded. -/
theorem all_bounded_of {A B : ℝ} (hB : B ≤ 1) (hA : |A| ≤ 1 + B) (hd : B = 1 → |A| ≠ 2)
    {y : ℕ → ℝ} (hy : Rec A B y) : ∃ M, ∀ t, |y t| ≤ M := by
  by_cases hD : A ^ 2 < 4 * B
  · exact complex_bounded hD hB hy
  push Not at hD
  obtain ⟨hsum, hprod, hle⟩ := real_roots hD
  set m1 := (A + Real.sqrt (A ^ 2 - 4 * B)) / 2
  set m2 := (A - Real.sqrt (A ^ 2 - 4 * B)) / 2
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hp1 : 0 ≤ (1 - m1) * (1 - m2) := by nlinarith
  have hp2 : 0 ≤ (1 + m1) * (1 + m2) := by nlinarith
  have hAle : A ≤ 2 := by linarith
  have hAge : -2 ≤ A := by linarith
  have hm1 : m1 ≤ 1 := by nlinarith
  have hm2 : -1 ≤ m2 := by nlinarith
  have habs1 : |m1| ≤ 1 := abs_le.mpr ⟨by linarith, hm1⟩
  have habs2 : |m2| ≤ 1 := abs_le.mpr ⟨hm2, by linarith⟩
  by_cases h2 : |m2| < 1
  · have hw := mode_pow hsum hprod hy
    refine ⟨|y 0| + |y 1 - m2 * y 0| / (1 - |m2|), fun t =>
      FullModel.bounded_of_rec (abs_nonneg _) h2 (abs_nonneg _) le_rfl (fun t => ?_) t⟩
    have e : y (t + 1) = m2 * y t + m1 ^ t * (y 1 - m2 * y 0) := by linarith [hw t]
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have : |m1| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) habs1
    have : |m1| ^ t * |y 1 - m2 * y 0| ≤ |y 1 - m2 * y 0| :=
      mul_le_of_le_one_left (abs_nonneg _) this
    linarith
  by_cases h1 : |m1| < 1
  · have hz := mode_pow (by linarith : m2 + m1 = A) (by linarith : m2 * m1 = B) hy
    refine ⟨|y 0| + |y 1 - m1 * y 0| / (1 - |m1|), fun t =>
      FullModel.bounded_of_rec (abs_nonneg _) h1 (abs_nonneg _) le_rfl (fun t => ?_) t⟩
    have e : y (t + 1) = m1 * y t + m2 ^ t * (y 1 - m1 * y 0) := by linarith [hz t]
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have : |m2| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) habs2
    have : |m2| ^ t * |y 1 - m1 * y 0| ≤ |y 1 - m1 * y 0| :=
      mul_le_of_le_one_left (abs_nonneg _) this
    linarith
  push Not at h1 h2
  have e1 : |m1| = 1 := le_antisymm habs1 h1
  have e2 : |m2| = 1 := le_antisymm habs2 h2
  rcases abs_eq (zero_le_one' ℝ) |>.mp e1 with f1 | f1 <;>
    rcases abs_eq (zero_le_one' ℝ) |>.mp e2 with f2 | f2
  · exact absurd (by rw [abs_of_nonneg (by linarith)]; linarith) (hd (by nlinarith))
  · -- roots `1` and `−1`: `y_{t+2} = y_t`
    have hA0 : A = 0 := by linarith
    have hB0 : B = -1 := by rw [← hprod, f1, f2]; ring
    refine ⟨max |y 0| |y 1|, fun t => ?_⟩
    have key : ∀ t, |y t| ≤ max |y 0| |y 1| ∧ |y (t + 1)| ≤ max |y 0| |y 1| := by
      intro t
      induction t with
      | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
      | succ t ih =>
        refine ⟨ih.2, ?_⟩
        rw [hy t, hA0, hB0]
        simpa using ih.1
    exact (key t).1
  · linarith
  · exact absurd (by rw [abs_of_nonpos (by linarith)]; linarith) (hd (by nlinarith))

/-- Cochrane (2023), p. 421 (real explosion as unboundedness), for **any** coefficients: some
solution of `y_{t+2} = A y_{t+1} − B y_t` is unbounded iff `B > 1`, `1 + B < |A|`, or
`B = 1 ∧ |A| = 2`. -/
theorem exists_unbounded_iff (A B : ℝ) :
    (∃ y, Rec A B y ∧ ¬ ∃ M, ∀ t, |y t| ≤ M) ↔ 1 < B ∨ 1 + B < |A| ∨ (B = 1 ∧ |A| = 2) := by
  constructor
  · rintro ⟨y, hy, hu⟩
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    exact hu (all_bounded_of h1 h2 h3 hy)
  · rintro (h | h | ⟨hB, hA⟩)
    · refine ⟨recSeq A B 1 0, recSeq_rec A B 1 0, unbounded_of_Q h (recSeq_rec A B 1 0) ?_⟩
      simp only [recSeq, Qf]
      linarith
    · rcases lt_abs.mp h with h' | h'
      · obtain ⟨μ, hμ1, hμ⟩ := exists_root_gt_one (A := A) (B := B) (by linarith)
        exact ⟨_, geom_rec hμ 1, pow_unbounded (by rw [abs_of_pos (by linarith)]; exact hμ1)⟩
      · obtain ⟨μ, hμ1, hμ⟩ := exists_root_lt_neg_one (A := A) (B := B) (by linarith)
        exact ⟨_, geom_rec hμ 1, pow_unbounded (by rw [abs_of_neg (by linarith)]; linarith)⟩
    · subst hB
      have hunb : ∀ z : ℕ → ℝ, (∀ t, |z t| = t) → ¬ ∃ M, ∀ t, |z t| ≤ M := by
        rintro z hz ⟨M, hM⟩
        obtain ⟨t, ht⟩ := exists_nat_gt M
        have := hM t
        rw [hz t] at this
        linarith
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).mp hA with e | e
      · subst e
        exact ⟨_, lin_rec, hunb _ fun t => by simp⟩
      · subst e
        exact ⟨_, altlin_rec, hunb _ fun t => by simp [abs_mul]⟩

/-! ### Solutions that do not decay -/

/-- Cochrane (2023), p. 421 (the real transversality condition `βᵗ x̃_t → 0`), for **any**
coefficients: some solution of `y_{t+2} = A y_{t+1} − B y_t` fails to tend to zero iff the
Schur–Cohn condition `|B| < 1 ∧ |A| < 1 + B` fails. -/
theorem exists_not_tendsto_zero_iff (A B : ℝ) :
    (∃ y, Rec A B y ∧ ¬ Tendsto y atTop (𝓝 0)) ↔ ¬ SchurStable A B := by
  constructor
  · rintro ⟨y, hy, hn⟩ hS
    exact hn (tendsto_zero_of_schur hS hy)
  · intro hS
    by_cases hB1 : 1 < B
    · obtain ⟨y, hy, hu⟩ := (exists_unbounded_iff A B).mpr (Or.inl hB1)
      exact ⟨y, hy, fun h => hu (bounded_of_tendsto h)⟩
    by_cases hBe : B = 1
    · refine ⟨recSeq A B 1 0, recSeq_rec A B 1 0, not_tendsto_zero_of_Q hBe
        (recSeq_rec A B 1 0) ?_⟩
      simp only [recSeq, Qf, hBe]
      norm_num
    have hB : B < 1 := lt_of_le_of_ne (not_lt.mp hB1) hBe
    have hor : 1 - A + B ≤ 0 ∨ 1 + A + B ≤ 0 := by
      unfold SchurStable at hS
      by_contra hc
      push Not at hc
      exact hS ⟨abs_lt.mpr ⟨by linarith, hB⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    rcases hor with h | h
    · obtain ⟨μ, hμ1, hμ⟩ := exists_root_ge_one h
      exact ⟨_, geom_rec hμ 1, pow_not_tendsto_zero (by rw [abs_of_pos (by linarith)]; exact hμ1)⟩
    · obtain ⟨μ, hμ1, hμ⟩ := exists_root_le_neg_one h
      exact ⟨_, geom_rec hμ 1, pow_not_tendsto_zero (by rw [abs_of_neg (by linarith)]; linarith)⟩

end Cochrane.KeynesianStickyPrices.TidyR5Recurrence
