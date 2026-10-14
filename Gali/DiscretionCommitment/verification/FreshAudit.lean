import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.InfinitePi
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Determinacy of two-dimensional linear systems

Galí (2015), Chapter 3, p. 65, and Woodford (2003), Appendix C.1,
Proposition C.1. A linear rational-expectations system
`x_t = A E_t x_{t+1} + B u_t` in two non-predetermined variables has a unique
bounded solution if and only if both eigenvalues of `A` lie strictly inside
the unit circle. For a real `2 × 2` matrix with trace `T` and determinant `D`
this is the Schur–Cohn condition

  `|D| < 1  ∧  |T| < 1 + D`.

This module is the deterministic half of that statement. It proves:

* `schurStable_iff_roots`: the Schur–Cohn condition holds iff both roots of the
  characteristic polynomial `z² − T z + D` have modulus less than one;
* `tendsto_pow_entry`: under the condition, every entry of `Aᵏ` tends to zero,
  with the explicit bound `bound_pow_entry`;
* `exists_bounded_homogeneous`: without it, the homogeneous recursion
  `x_t = A x_{t+1}` has a bounded solution that is not identically zero.

The roots are written explicitly through the discriminant, so no spectral
theory is needed: powers of `A` are controlled through the Cayley–Hamilton
recursion `A^{k+2} = p_{k+1} A − D p_k I` and the identity
`p_k = ∑_{j ≤ k} r₁ʲ r₂^{k−j}`.

Restated from the `Gali/MonetaryPolicyDesign` project (each project in this
repository is self-contained).
-/

namespace Gali.DiscretionCommitment

open Filter Topology

/-- The Schur–Cohn condition for a real quadratic `z² − T z + D`: both roots
lie strictly inside the unit circle (Woodford, Prop. C.1, p. 670). -/
def SchurStable (T D : ℝ) : Prop := |D| < 1 ∧ |T| < 1 + D

/-- The discriminant `T² − 4D` of `z² − T z + D`. -/
def disc (T D : ℝ) : ℝ := T ^ 2 - 4 * D

/-- The first root of `z² − T z + D`. -/
noncomputable def root₁ (T D : ℝ) : ℂ :=
  if 0 ≤ disc T D then ((T + Real.sqrt (disc T D)) / 2 : ℝ)
  else ⟨T / 2, Real.sqrt (-disc T D) / 2⟩

/-- The second root of `z² − T z + D`. -/
noncomputable def root₂ (T D : ℝ) : ℂ :=
  if 0 ≤ disc T D then ((T - Real.sqrt (disc T D)) / 2 : ℝ)
  else ⟨T / 2, -(Real.sqrt (-disc T D) / 2)⟩

theorem root_sum (T D : ℝ) : root₁ T D + root₂ T D = T := by
  unfold root₁ root₂
  split_ifs with h
  · push_cast; ring
  · apply Complex.ext <;> simp

theorem root_prod (T D : ℝ) : root₁ T D * root₂ T D = D := by
  unfold root₁ root₂
  split_ifs with h
  · rw [← Complex.ofReal_mul]
    congr 1
    have hs := Real.sq_sqrt h
    have hd : disc T D = T ^ 2 - 4 * D := rfl
    nlinarith [hs]
  · have h' : 0 ≤ -disc T D := by linarith [not_le.mp h]
    have hs := Real.sq_sqrt h'
    have hd : disc T D = T ^ 2 - 4 * D := rfl
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re]
      nlinarith [hs]
    · simp only [Complex.mul_im, Complex.ofReal_im]
      ring

/-- Both roots solve `z² − T z + D = 0`. -/
theorem root_eq (T D : ℝ) (z : ℂ) (hz : z = root₁ T D ∨ z = root₂ T D) :
    z ^ 2 - T * z + D = 0 := by
  rw [← root_sum T D, ← root_prod T D]
  rcases hz with rfl | rfl <;> ring

/-- In the complex case both roots have squared modulus `D`. -/
theorem normSq_root_of_neg {T D : ℝ} (h : disc T D < 0) :
    ‖root₁ T D‖ ^ 2 = D ∧ ‖root₂ T D‖ ^ 2 = D := by
  have h' : 0 ≤ -disc T D := by linarith
  have hs := Real.sq_sqrt h'
  have hd : disc T D = T ^ 2 - 4 * D := rfl
  have hn : ¬ 0 ≤ disc T D := not_le.mpr h
  unfold root₁ root₂
  simp only [hn, ↓reduceIte, Complex.sq_norm, Complex.normSq_mk]
  constructor <;> nlinarith [hs]

/-- In the real case the roots are the real numbers `(T ± √(T² − 4D))/2`. -/
theorem norm_root_of_nonneg {T D : ℝ} (h : 0 ≤ disc T D) :
    ‖root₁ T D‖ = |(T + Real.sqrt (disc T D)) / 2| ∧
      ‖root₂ T D‖ = |(T - Real.sqrt (disc T D)) / 2| := by
  unfold root₁ root₂
  refine ⟨?_, ?_⟩ <;> simp only [h, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]

/-- **Schur–Cohn for quadratics** (Woodford, Prop. C.1, p. 670): both roots of
`z² − T z + D` lie strictly inside the unit circle iff `|D| < 1` and
`|T| < 1 + D`. -/
theorem schurStable_iff_roots (T D : ℝ) :
    SchurStable T D ↔ ‖root₁ T D‖ < 1 ∧ ‖root₂ T D‖ < 1 := by
  unfold SchurStable
  by_cases h : 0 ≤ disc T D
  · obtain ⟨h1, h2⟩ := norm_root_of_nonneg h
    rw [h1, h2]
    set s := Real.sqrt (disc T D) with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = T ^ 2 - 4 * D := by rw [hs_def, Real.sq_sqrt h]; rfl
    constructor
    · rintro ⟨hD, hT⟩
      rw [abs_lt] at hD hT
      have hT2 : T < 2 := by linarith
      have hT2' : -2 < T := by linarith
      have ha : s < 2 - T := by nlinarith
      have hb : s < 2 + T := by nlinarith
      constructor <;> rw [abs_lt] <;> constructor <;> linarith
    · rintro ⟨h1, h2⟩
      rw [abs_lt] at h1 h2
      have hD : D = ((T + s) / 2) * ((T - s) / 2) := by nlinarith
      refine ⟨?_, ?_⟩
      · rw [hD, abs_lt]
        constructor <;> nlinarith
      · rw [abs_lt]
        constructor <;> nlinarith
  · have hneg : disc T D < 0 := not_le.mp h
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    unfold disc at hneg
    have hD0 : 0 < D := by nlinarith [sq_nonneg T]
    constructor
    · rintro ⟨hD, -⟩
      rw [abs_lt] at hD
      constructor
      · have := norm_nonneg (root₁ T D)
        nlinarith
      · have := norm_nonneg (root₂ T D)
        nlinarith
    · rintro ⟨hr, -⟩
      have hn := norm_nonneg (root₁ T D)
      have hDlt : D < 1 := by nlinarith
      refine ⟨by rw [abs_lt]; constructor <;> linarith, ?_⟩
      -- `T² < 4D` and `4D ≤ (1 + D)²`
      have hsq : T ^ 2 < (1 + D) ^ 2 := by nlinarith [sq_nonneg (1 - D)]
      exact abs_lt_of_sq_lt_sq hsq (by linarith)

/-! ### Powers of a `2 × 2` matrix -/

/-- The scalar sequence of the Cayley–Hamilton recursion:
`p₀ = 1`, `p₁ = T`, `p_{k+2} = T p_{k+1} − D p_k`. -/
def chSeq (T D : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => T
  | k + 2 => T * chSeq T D (k + 1) - D * chSeq T D k

/-- The geometric-convolution sequence `S_k = ∑_{j ≤ k} r₁ʲ r₂^{k−j}`, given
recursively by `S₀ = 1`, `S_{k+1} = r₁^{k+1} + r₂ S_k`. -/
def convSeq (r₁ r₂ : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => r₁ ^ (k + 1) + r₂ * convSeq r₁ r₂ k

theorem convSeq_rec (r₁ r₂ : ℂ) (k : ℕ) :
    convSeq r₁ r₂ (k + 2) = (r₁ + r₂) * convSeq r₁ r₂ (k + 1) - r₁ * r₂ * convSeq r₁ r₂ k := by
  simp only [convSeq]
  ring

/-- The Cayley–Hamilton sequence is the geometric convolution of the roots. -/
theorem chSeq_eq_convSeq (T D : ℝ) (k : ℕ) :
    (chSeq T D k : ℂ) = convSeq (root₁ T D) (root₂ T D) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [chSeq, convSeq]
    | 1, _ => simp [chSeq, convSeq, ← root_sum T D]
    | k + 2, ih =>
      rw [convSeq_rec, root_sum, root_prod, ← ih k (by omega), ← ih (k + 1) (by omega)]
      simp [chSeq]

/-- `‖S_k‖ ≤ (k + 1) ρᵏ` when both roots have modulus at most `ρ`. -/
theorem norm_convSeq_le {r₁ r₂ : ℂ} {ρ : ℝ} (h1 : ‖r₁‖ ≤ ρ) (h2 : ‖r₂‖ ≤ ρ) (k : ℕ) :
    ‖convSeq r₁ r₂ k‖ ≤ (k + 1) * ρ ^ k := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans h1
  induction k with
  | zero => simp [convSeq]
  | succ k ih =>
    simp only [convSeq]
    calc ‖r₁ ^ (k + 1) + r₂ * convSeq r₁ r₂ k‖
        ≤ ‖r₁‖ ^ (k + 1) + ‖r₂‖ * ‖convSeq r₁ r₂ k‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow, norm_mul]
      _ ≤ ρ ^ (k + 1) + ρ * ((k + 1) * ρ ^ k) := by
          gcongr
      _ = ((k + 1 : ℕ) + 1) * ρ ^ (k + 1) := by push_cast; ring

/-- `|p_k| ≤ (k + 1) ρᵏ` for `ρ` the larger root modulus. -/
theorem abs_chSeq_le (T D : ℝ) (k : ℕ) :
    |chSeq T D k| ≤ (k + 1) * max ‖root₁ T D‖ ‖root₂ T D‖ ^ k := by
  have he : |chSeq T D k| = ‖(chSeq T D k : ℂ)‖ := by simp
  rw [he, chSeq_eq_convSeq]
  exact norm_convSeq_le (le_max_left _ _) (le_max_right _ _) k

/-- Under the Schur–Cohn condition the Cayley–Hamilton sequence tends to zero. -/
theorem tendsto_chSeq {T D : ℝ} (h : SchurStable T D) :
    Tendsto (chSeq T D) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots T D).mp h
  set ρ := max ‖root₁ T D‖ ‖root₂ T D‖
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * ρ ^ k) atTop (𝓝 0) := by
    have ha := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have hb := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    simpa [add_mul] using ha.add hb
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  exact abs_chSeq_le T D k

/-- The trace of a `2 × 2` matrix. -/
def tr2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A 0 0 + A 1 1

/-- The determinant of a `2 × 2` matrix. -/
def det2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A 0 0 * A 1 1 - A 0 1 * A 1 0

theorem tr2_eq_trace (A : Matrix (Fin 2) (Fin 2) ℝ) : tr2 A = A.trace :=
  (Matrix.trace_fin_two A).symm

theorem det2_eq_det (A : Matrix (Fin 2) (Fin 2) ℝ) : det2 A = A.det :=
  (Matrix.det_fin_two A).symm

/-- Cayley–Hamilton for `2 × 2` matrices: `A² = T A − D I`. -/
theorem sq_eq_cayleyHamilton (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 = tr2 A • A - det2 A • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, tr2, det2] <;> ring

/-- Powers of a `2 × 2` matrix through the Cayley–Hamilton sequence:
`A^{k+1} = p_k A − D p_{k−1} I` (with `p_{−1} = 0`). -/
theorem pow_succ_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) :
    A ^ (k + 2) = chSeq (tr2 A) (det2 A) (k + 1) • A
      - (det2 A * chSeq (tr2 A) (det2 A) k) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  induction k with
  | zero =>
    rw [sq_eq_cayleyHamilton]
    simp [chSeq]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, chSeq, tr2, det2, Matrix.one_apply] <;> ring

/-- An entrywise bound on `Aᵏ` through the Cayley–Hamilton sequence. -/
theorem abs_pow_entry_le (A : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (i j : Fin 2) :
    |(A ^ (k + 2)) i j| ≤ |chSeq (tr2 A) (det2 A) (k + 1)| * |A i j|
      + |det2 A| * |chSeq (tr2 A) (det2 A) k| := by
  have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  rw [pow_succ_eq]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
  rw [abs_mul, abs_mul]
  calc |det2 A| * |chSeq (tr2 A) (det2 A) k| * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
      ≤ |det2 A| * |chSeq (tr2 A) (det2 A) k| * 1 := by gcongr
    _ = _ := mul_one _

/-- Under the Schur–Cohn condition every entry of `Aᵏ` tends to zero. -/
theorem tendsto_pow_entry {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 A) (det2 A)) (i j : Fin 2) :
    Tendsto (fun k => (A ^ k) i j) atTop (𝓝 0) := by
  have hc := tendsto_chSeq h
  have hlim : Tendsto (fun k => |chSeq (tr2 A) (det2 A) (k + 1)| * |A i j|
      + |det2 A| * |chSeq (tr2 A) (det2 A) k|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |chSeq (tr2 A) (det2 A) (k + 1)|) atTop (𝓝 0) := by
      simpa using ((tendsto_add_atTop_iff_nat 1).mpr hc).abs
    have h2 : Tendsto (fun k => |chSeq (tr2 A) (det2 A) k|) atTop (𝓝 0) := by
      simpa using hc.abs
    simpa using (h1.mul_const |A i j|).add (h2.const_mul |det2 A|)
  rw [← tendsto_add_atTop_iff_nat 2]
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  exact abs_pow_entry_le A k i j

/-! ### Bounded solutions of the homogeneous recursion -/

/-- A sequence of vectors is bounded. -/
def BoundedSeq (x : ℕ → Fin 2 → ℝ) : Prop := ∃ M, ∀ t i, |x t i| ≤ M

/-- Iterating `x_t = A x_{t+1}` gives `x_t = Aᵏ x_{t+k}`. -/
theorem homogeneous_iterate {A : Matrix (Fin 2) (Fin 2) ℝ} {x : ℕ → Fin 2 → ℝ}
    (hx : ∀ t, x t = A.mulVec (x (t + 1))) (t k : ℕ) :
    x t = (A ^ k).mulVec (x (t + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, hx (t + k), Matrix.mulVec_mulVec, ← pow_succ, add_assoc]

/-- A bound `|v i| ≤ ∑_j |M i j| · C` for `v = M w` with `|w j| ≤ C`. -/
theorem abs_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) {C : ℝ}
    (hw : ∀ j, |w j| ≤ C) (i : Fin 2) :
    |M.mulVec w i| ≤ (|M i 0| + |M i 1|) * C := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, add_mul]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw 0)
  gcongr
  · exact hw 0
  · exact hw 1

/-- **Uniqueness under Schur–Cohn**: if both roots lie inside the unit circle,
the only bounded solution of `x_t = A x_{t+1}` is zero. -/
theorem homogeneous_eq_zero {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 A) (det2 A)) {x : ℕ → Fin 2 → ℝ}
    (hx : ∀ t, x t = A.mulVec (x (t + 1))) (hb : BoundedSeq x) : x = 0 := by
  obtain ⟨M, hM⟩ := hb
  funext t i
  have hle : ∀ k, |x t i| ≤ (|(A ^ k) i 0| + |(A ^ k) i 1|) * M := by
    intro k
    rw [homogeneous_iterate hx t k]
    exact abs_mulVec_le _ _ (hM (t + k)) i
  have hlim : Tendsto (fun k => (|(A ^ k) i 0| + |(A ^ k) i 1|) * M) atTop (𝓝 0) := by
    simpa using (((tendsto_pow_entry h i 0).abs.add (tendsto_pow_entry h i 1).abs).mul_const M)
  have h0 : |x t i| ≤ 0 := ge_of_tendsto' hlim hle
  simpa using h0

/-- Every root of `z² − T z + D` is one of `root₁`, `root₂`. -/
theorem eq_root_of_eq {T D : ℝ} {z : ℂ} (hz : z ^ 2 - T * z + D = 0) :
    z = root₁ T D ∨ z = root₂ T D := by
  have h : (z - root₁ T D) * (z - root₂ T D) = 0 := by
    have hs := root_sum T D
    have hp := root_prod T D
    linear_combination hz - z * hs + hp
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- A complex eigenvector with nonzero real part for each root of the
characteristic polynomial of a real `2 × 2` matrix. -/
theorem exists_eigenvector (A : Matrix (Fin 2) (Fin 2) ℝ) {r : ℂ}
    (hr : r ^ 2 - tr2 A * r + det2 A = 0) :
    ∃ v : Fin 2 → ℂ, (∃ i, (v i).re ≠ 0) ∧
      ∀ i, (A i 0 : ℂ) * v 0 + A i 1 * v 1 = r * v i := by
  -- the characteristic equation in entries: (r − a)(r − d) = b c
  have hch : (r - A 0 0) * (r - A 1 1) = (A 0 1 : ℂ) * A 1 0 := by
    unfold tr2 det2 at hr
    push_cast at hr
    linear_combination hr
  -- an eigenvector, not yet normalised
  obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 2 → ℂ, w ≠ 0 ∧
      ∀ i, (A i 0 : ℂ) * w 0 + A i 1 * w 1 = r * w i := by
    by_cases h1 : (A 0 1 : ℂ) = 0 ∧ r - A 0 0 = 0
    · by_cases h2 : r - A 1 1 = 0 ∧ (A 1 0 : ℂ) = 0
      · refine ⟨![1, 0], fun h => by simpa using congrFun h 0, fun i => ?_⟩
        fin_cases i
        · simp; linear_combination -h1.2
        · simp [h2.2]
      · refine ⟨![r - A 1 1, A 1 0], fun h => h2 ⟨by simpa using congrFun h 0,
          by simpa using congrFun h 1⟩, fun i => ?_⟩
        fin_cases i
        · simp; linear_combination -hch
        · simp; ring
    · refine ⟨![A 0 1, r - A 0 0], fun h => h1 ⟨by simpa using congrFun h 0,
        by simpa using congrFun h 1⟩, fun i => ?_⟩
      fin_cases i
      · simp; ring
      · simp; linear_combination -hch
  -- normalise so that some real part is nonzero
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  by_cases hre : (w j).re = 0
  · refine ⟨fun i => Complex.I * w i, ⟨j, ?_⟩, fun i => ?_⟩
    · have him : (w j).im ≠ 0 := fun him => hj (Complex.ext hre him)
      simpa using him
    · linear_combination Complex.I * hw i
  · exact ⟨w, ⟨j, hre⟩, hw⟩

/-- **Multiplicity without Schur–Cohn**: if a root of `z² − T z + D` lies on or
outside the unit circle, then `x_t = A x_{t+1}` has a bounded solution that is
not identically zero, `x_t = Re (r^{−t} v)` for an eigenvector `v`. -/
theorem exists_bounded_homogeneous {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : ¬ SchurStable (tr2 A) (det2 A)) :
    ∃ x : ℕ → Fin 2 → ℝ, (∀ t, x t = A.mulVec (x (t + 1))) ∧ BoundedSeq x ∧ x ≠ 0 := by
  rw [schurStable_iff_roots, not_and_or, not_lt, not_lt] at h
  obtain ⟨r, hr1, hroot⟩ : ∃ r : ℂ, 1 ≤ ‖r‖ ∧ r ^ 2 - tr2 A * r + det2 A = 0 := by
    rcases h with h | h
    · exact ⟨_, h, root_eq _ _ _ (Or.inl rfl)⟩
    · exact ⟨_, h, root_eq _ _ _ (Or.inr rfl)⟩
  have hr0 : r ≠ 0 := fun h0 => by norm_num [h0] at hr1
  obtain ⟨v, ⟨j, hj⟩, hv⟩ := exists_eigenvector A hroot
  set x : ℕ → Fin 2 → ℝ := fun t i => ((r⁻¹) ^ t * v i).re with hx_def
  refine ⟨x, fun t => ?_, ⟨‖v 0‖ + ‖v 1‖, fun t i => ?_⟩, fun h0 => ?_⟩
  · funext i
    simp only [hx_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hc : ∀ (a : ℝ) (z : ℂ), a * z.re = ((a : ℂ) * z).re := by
      intro a z; simp
    rw [hc, hc, ← Complex.add_re]
    congr 1
    have := hv i
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
    calc (r⁻¹) ^ t * v i = (r⁻¹) ^ (t + 1) * (r * v i) := by
          linear_combination (-(r⁻¹ ^ t * v i)) * hrr
      _ = _ := by rw [← this]; ring
  · have hrt : ‖(r⁻¹) ^ t‖ ≤ 1 := by
      rw [norm_pow, norm_inv]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
    calc |x t i| ≤ ‖(r⁻¹) ^ t * v i‖ := Complex.abs_re_le_norm _
      _ ≤ 1 * ‖v i‖ := by rw [norm_mul]; gcongr
      _ ≤ ‖v 0‖ + ‖v 1‖ := by
          fin_cases i <;> simp
  · have := congrFun (congrFun h0 0) j
    exact hj (by simpa [hx_def] using this)

end Gali.DiscretionCommitment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Rational expectations

The models of Galí (2015) are systems of expectational difference equations
`x_t = A E_t x_{t+1} + B u_t`. Every result in the book uses only a few
properties of the conditional expectation `E_t`: it is linear, it leaves
constants unchanged, it is monotone, and it satisfies the law of iterated
expectations. This module axiomatises exactly these properties as an
`ExpectationSystem` on random variables `Ω → ℝ`, so every theorem holds both
under perfect foresight (`perfectForesight`, where `E_t` is the identity) and
under uncertainty.

## Main results

* `ExpectationSystem.abs_E_le`: `|E_t x| ≤ M` whenever `|x| ≤ M`.
* `ExpectationSystem.ar1_iterate`: for an AR(1) process `E_t u_{t+k} = ρᵏ u_t`.
* `forwardSeries_solves`, `eq_forwardSeries`: for `0 ≤ a < 1` and bounded adapted
  forcing, the forward series `∑ aᵏ E_t u_{t+k}` is the unique bounded solution of
  `z_t = a E_t z_{t+1} + u_t` (Galí, (25) p. 27 and (28) p. 29).
* `forward_unique`: a scalar equation `z_t = a E_t z_{t+1} + u_t` with
  `|a| < 1` has at most one bounded adapted solution.
* `system_unique`: a two-variable system `x_t = A E_t x_{t+1} + B u_t` has at
  most one bounded adapted solution when `A` satisfies the Schur–Cohn
  condition.
* `system_not_unique`: otherwise every bounded solution has a second bounded
  solution next to it, a deterministic self-fulfilling path.
* `determinate_iff`: determinacy (uniqueness of bounded adapted solutions) is
  equivalent to the Schur–Cohn condition on `A` (Galí, p. 65; Blanchard and
  Kahn 1980).

Restated from the `Gali/MonetaryPolicyDesign` project (each project in this
repository is self-contained).
-/

namespace Gali.DiscretionCommitment

open Filter Topology

/-- A family of conditional expectation operators `E_t` on random variables
`Ω → ℝ`, indexed by dates `t : ℕ`, with the properties the book uses:
linearity, constants, monotonicity and the law of iterated expectations. -/
structure ExpectationSystem (Ω : Type*) where
  /-- The expectation conditional on date-`t` information. -/
  E : ℕ → (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)
  /-- Constants are known at every date. -/
  const : ∀ t (c : ℝ), E t (fun _ => c) = fun _ => c
  /-- Expectations preserve the pointwise order. -/
  mono : ∀ t {x y : Ω → ℝ}, x ≤ y → E t x ≤ E t y
  /-- The law of iterated expectations: `E_s E_t = E_s` for `s ≤ t`. -/
  tower : ∀ {s t : ℕ}, s ≤ t → ∀ x, E s (E t x) = E s x
  /-- Earlier information is known later: `E_t E_s = E_s` for `s ≤ t`. -/
  known : ∀ {s t : ℕ}, s ≤ t → ∀ x, E t (E s x) = E s x

/-- Perfect foresight: a single state, and `E_t` is the identity. -/
def perfectForesight : ExpectationSystem Unit where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- A process is bounded. -/
def BoundedProc {Ω : Type*} (x : ℕ → Ω → ℝ) : Prop := ∃ M, ∀ t ω, |x t ω| ≤ M

/-- A vector process is bounded. -/
def BoundedVec {Ω : Type*} (x : ℕ → Fin 2 → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |x t i ω| ≤ M

namespace ExpectationSystem

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- A process is adapted when its date-`t` value is known at date `t`. -/
def Adapted (x : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (x t) = x t

/-- An AR(1) process with persistence `ρ`: adapted, with `E_t u_{t+1} = ρ u_t`. -/
def IsAR1 (ρ : ℝ) (u : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted u ∧ ∀ t, 𝔼.E t (u (t + 1)) = ρ • u t

theorem E_neg (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (-x) = -𝔼.E t x := map_neg _ _

theorem E_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) : 𝔼.E t (c • x) = c • 𝔼.E t x :=
  map_smul _ _ _

theorem E_E_self (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (𝔼.E t x) = 𝔼.E t x :=
  𝔼.tower le_rfl x

/-- `E_t` is bounded by the bound of its argument. -/
theorem abs_E_le {M : ℝ} {x : Ω → ℝ} (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    |𝔼.E t x ω| ≤ M := by
  have hu : x ≤ fun _ => M := fun ω => (le_abs_self _).trans (hx ω)
  have hl : (fun _ => -M) ≤ x := fun ω => by
    have := neg_abs_le (x ω); linarith [hx ω]
  have h1 := 𝔼.mono t hu ω
  have h2 := 𝔼.mono t hl ω
  rw [𝔼.const] at h1 h2
  exact _root_.abs_le.mpr ⟨h2, h1⟩

/-- Conditional expectations of a bounded process are bounded by the same constant. -/
theorem bounded_E {x : ℕ → Ω → ℝ} {M : ℝ} (hx : ∀ t ω, |x t ω| ≤ M) (s t : ℕ) (ω : Ω) :
    |𝔼.E s (x t) ω| ≤ M :=
  𝔼.abs_E_le (hx t) s ω

/-- Iterating an AR(1) law: `E_t u_{t+k} = ρᵏ u_t`. -/
theorem ar1_iterate {ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t k : ℕ) :
    𝔼.E t (u (t + k)) = ρ ^ k • u t := by
  induction k with
  | zero => simpa using hu.1 t
  | succ k ih =>
    rw [← 𝔼.tower (Nat.le_add_right t k), ← add_assoc, hu.2 (t + k), E_smul, ih,
      smul_smul, pow_succ, mul_comm]

/-! ### Scalar forward equations -/

/-- Iterating a homogeneous forward equation: if `d_t = a E_t d_{t+1}` for an
adapted `d`, then `d_t = aᵏ E_t d_{t+k}`. -/
theorem forward_iterate {a : ℝ} {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d t = a • 𝔼.E t (d (t + 1))) (t k : ℕ) :
    d t = a ^ k • 𝔼.E t (d (t + k)) := by
  induction k with
  | zero =>
    have h := hd t
    rw [pow_zero, one_smul, add_zero]
    calc d t = a • 𝔼.E t (d (t + 1)) := h
      _ = 𝔼.E t (a • 𝔼.E t (d (t + 1))) := by rw [E_smul, E_E_self]
      _ = 𝔼.E t (d t) := by rw [← h]
  | succ k ih =>
    rw [ih, hd (t + k), E_smul, 𝔼.tower (Nat.le_add_right t k), smul_smul, ← pow_succ,
      add_assoc]

/-- **Forward uniqueness** (Galí, p. 61 and passim): with `|a| < 1`, the
equation `z_t = a E_t z_{t+1} + u_t` has at most one bounded solution. -/
theorem forward_unique {a : ℝ} (ha : |a| < 1) {u z₁ z₂ : ℕ → Ω → ℝ}
    (h₁ : ∀ t, z₁ t = a • 𝔼.E t (z₁ (t + 1)) + u t)
    (h₂ : ∀ t, z₂ t = a • 𝔼.E t (z₂ (t + 1)) + u t)
    (hb₁ : BoundedProc z₁) (hb₂ : BoundedProc z₂) : z₁ = z₂ := by
  obtain ⟨M₁, hM₁⟩ := hb₁
  obtain ⟨M₂, hM₂⟩ := hb₂
  set d : ℕ → Ω → ℝ := fun t => z₁ t - z₂ t with hd_def
  have hd : ∀ t, d t = a • 𝔼.E t (d (t + 1)) := by
    intro t
    simp only [hd_def, map_sub, smul_sub]
    rw [h₁ t, h₂ t]; abel
  have hdb : ∀ t ω, |d t ω| ≤ M₁ + M₂ := fun t ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))
  funext t ω
  have hle : ∀ k, |d t ω| ≤ |a| ^ k * (M₁ + M₂) := by
    intro k
    rw [𝔼.forward_iterate hd t k]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    gcongr
    exact 𝔼.abs_E_le (hdb (t + k)) t ω
  have hlim : Tendsto (fun k : ℕ => |a| ^ k * (M₁ + M₂)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const (M₁ + M₂)
  have h0 : |d t ω| ≤ 0 := ge_of_tendsto' hlim hle
  have : d t ω = 0 := abs_nonpos_iff.mp h0
  simpa [hd_def, sub_eq_zero] using this

/-- The forward solution of `z_t = a E_t z_{t+1} + u_t` for an AR(1) forcing
process: `z_t = u_t / (1 − a ρ)`. -/
theorem forward_ar1_solves {a ρ : ℝ} (h : 1 - a * ρ ≠ 0) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (t : ℕ) :
    (1 - a * ρ)⁻¹ • u t = a • 𝔼.E t ((1 - a * ρ)⁻¹ • u (t + 1)) + u t := by
  rw [E_smul, hu.2 t, smul_smul, smul_smul]
  have hc : (1 - a * ρ)⁻¹ = a * ((1 - a * ρ)⁻¹ * ρ) + 1 := by
    field_simp
    ring
  conv_lhs => rw [hc]
  rw [add_smul, one_smul, mul_assoc a]

/-! ### Forward solutions as genuine infinite sums -/

/-- Galí (2015), pp. 27, 29 (forward solutions): `E_t` commutes with a series
dominated by a geometric series `|f_k| ≤ aᵏ M`, `0 ≤ a < 1`. -/
theorem E_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' k, f k ω') ω = ∑' k, 𝔼.E t (f k) ω := by
  have hgeo : Summable (fun k : ℕ => a ^ k * M) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_right M
  have hsum : ∀ ω', Summable (fun k => f k ω') := fun ω' =>
    Summable.of_norm_bounded hgeo (fun k => by rw [Real.norm_eq_abs]; exact hf k ω')
  have hEs : Summable (fun k => 𝔼.E t (f k) ω) :=
    Summable.of_norm_bounded hgeo (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  -- tail bound for the partial sums
  have htail : ∀ N ω', |(∑' k, f k ω') - ∑ k ∈ Finset.range N, f k ω'| ≤
      a ^ N * M / (1 - a) := by
    intro N ω'
    have hsplit := (hsum ω').sum_add_tsum_nat_add N
    have hsN : Summable (fun k => f (k + N) ω') := (summable_nat_add_iff N).mpr (hsum ω')
    have hgN : Summable (fun k : ℕ => a ^ N * M * a ^ k) :=
      (summable_geometric_of_lt_one ha0 ha1).mul_left (a ^ N * M)
    have hb : ∀ k, |f (k + N) ω'| ≤ a ^ N * M * a ^ k := fun k => by
      have := hf (k + N) ω'
      rw [pow_add] at this
      linarith [show a ^ k * a ^ N * M = a ^ N * M * a ^ k by ring]
    have hval : ∑' k : ℕ, a ^ N * M * a ^ k = a ^ N * M / (1 - a) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
    have hup : ∑' k, f (k + N) ω' ≤ a ^ N * M / (1 - a) := by
      rw [← hval]
      exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hsN hgN
    have hlo : -(a ^ N * M / (1 - a)) ≤ ∑' k, f (k + N) ω' := by
      rw [← hval, ← tsum_neg]
      exact Summable.tsum_le_tsum (fun k => by linarith [neg_abs_le (f (k + N) ω'), hb k])
        hgN.neg hsN
    rw [← hsplit, add_sub_cancel_left, abs_le]
    exact ⟨hlo, hup⟩
  have hlim1 : Tendsto (fun N => ∑ k ∈ Finset.range N, 𝔼.E t (f k) ω) atTop
      (𝓝 (𝔼.E t (fun ω' => ∑' k, f k ω') ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun N => a ^ N * M / (1 - a)) (fun N => ?_) ?_
    · rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
      have hE : ∑ k ∈ Finset.range N, 𝔼.E t (f k) ω =
          𝔼.E t (∑ k ∈ Finset.range N, f k) ω := by
        rw [map_sum, Finset.sum_apply]
      rw [hE, ← Pi.sub_apply, ← map_sub]
      refine 𝔼.abs_E_le (fun ω' => ?_) t ω
      rw [Pi.sub_apply, Finset.sum_apply]
      exact htail N ω'
    · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const M).div_const
        (1 - a)
  exact tendsto_nhds_unique hlim1 hEs.hasSum.tendsto_sum_nat

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward solution `z_t = ∑_{k ≥ 0} aᵏ E_t u_{t+k}` of
`z_t = a E_t z_{t+1} + u_t`. -/
noncomputable def forwardSeries (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series is summable for bounded forcing. -/
theorem forwardSeries_summable {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => a ^ k * 𝔼.E t (u (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series solves
`z_t = a E_t z_{t+1} + u_t` for bounded
adapted forcing `u` and `0 ≤ a < 1`. -/
theorem forwardSeries_solves {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) (t : ℕ) :
    𝔼.forwardSeries a u t = a • 𝔼.E t (𝔼.forwardSeries a u (t + 1)) + u t := by
  funext ω
  have hE : 𝔼.E t (𝔼.forwardSeries a u (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
    have hb : ∀ k ω', |a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ a ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_pow, abs_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω')
        (pow_nonneg ha0 k)
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum ha0 ha1 hb t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [hE, (𝔼.forwardSeries_summable ha0 ha1 hu t ω).tsum_eq_zero_add,
    pow_zero, one_mul, add_zero, hadapt t, ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series is bounded by `M / (1 − a)`. -/
theorem forwardSeries_bounded {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (𝔼.forwardSeries a u) := by
  refine ⟨M / (1 - a), fun t ω => ?_⟩
  have hs := 𝔼.forwardSeries_summable ha0 ha1 hu t ω
  have hg : Summable (fun k : ℕ => M * a ^ k) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  have hval : ∑' k : ℕ, M * a ^ k = M / (1 - a) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
  have hb : ∀ k, |a ^ k * 𝔼.E t (u (t + k)) ω| ≤ M * a ^ k := fun k => by
    rw [abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)
  have hlo : ∀ k, -(M * a ^ k) ≤ a ^ k * 𝔼.E t (u (t + k)) ω := fun k => by
    have := neg_abs_le (a ^ k * 𝔼.E t (u (t + k)) ω)
    linarith [hb k]
  change |∑' k, a ^ k * 𝔼.E t (u (t + k)) ω| ≤ _
  rw [abs_le, ← hval]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum hlo hg.neg hs
  · exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hs hg

/-- Galí (2015), (25) p. 27 and (28) p. 29: any bounded solution of
`z_t = a E_t z_{t+1} + u_t` (bounded
adapted `u`, `0 ≤ a < 1`) is the forward series. -/
theorem eq_forwardSeries {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u)
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hzb : BoundedProc z) :
    z = 𝔼.forwardSeries a u := by
  have ha : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  exact 𝔼.forward_unique ha hz (𝔼.forwardSeries_solves ha0 ha1 hu hadapt) hzb
    (𝔼.forwardSeries_bounded ha0 ha1 hu)

/-! ### Two-variable systems -/

/-- A vector process `x : ℕ → Fin 2 → Ω → ℝ` solves `x_t = A E_t x_{t+1} + w_t`. -/
def Solves (A : Matrix (Fin 2) (Fin 2) ℝ) (w x : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, x t i = A i 0 • 𝔼.E t (x (t + 1) 0) + A i 1 • 𝔼.E t (x (t + 1) 1) + w t i

/-- A vector process is adapted. -/
def AdaptedVec (x : ℕ → Fin 2 → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (x t i) = x t i

/-- Iterating the homogeneous system: `d_t = Aᵏ E_t d_{t+k}`. -/
theorem system_iterate {A : Matrix (Fin 2) (Fin 2) ℝ} {d : ℕ → Fin 2 → Ω → ℝ}
    (hd : 𝔼.Solves A 0 d) (had : 𝔼.AdaptedVec d) (t k : ℕ) (i : Fin 2) :
    d t i = (A ^ k) i 0 • 𝔼.E t (d (t + k) 0) + (A ^ k) i 1 • 𝔼.E t (d (t + k) 1) := by
  induction k generalizing i with
  | zero =>
    fin_cases i <;> simp [had t 0, had t 1]
  | succ k ih =>
    rw [ih i]
    have h0 := hd (t + k) 0
    have h1 := hd (t + k) 1
    simp only [Pi.zero_apply, add_zero] at h0 h1
    rw [h0, h1]
    simp only [map_add, map_smul, 𝔼.tower (Nat.le_add_right t k), pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul, ← add_assoc]
    abel_nf

/-- **Uniqueness under Schur–Cohn**: if `A` satisfies the Schur–Cohn
condition, `x_t = A E_t x_{t+1} + w_t` has at most one bounded adapted
solution (Galí, p. 65). -/
theorem system_unique {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : SchurStable (tr2 A) (det2 A))
    {w x y : ℕ → Fin 2 → Ω → ℝ} (hx : 𝔼.Solves A w x) (hy : 𝔼.Solves A w y)
    (hax : 𝔼.AdaptedVec x) (hay : 𝔼.AdaptedVec y)
    (hbx : BoundedVec x) (hby : BoundedVec y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → Fin 2 → Ω → ℝ := fun t i => x t i - y t i with hd_def
  have hd : 𝔼.Solves A 0 d := by
    intro t i
    simp only [hd_def, map_sub, smul_sub, Pi.zero_apply, add_zero]
    rw [hx t i, hy t i]; abel
  have had : 𝔼.AdaptedVec d := by
    intro t i
    simp only [hd_def, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  funext t i ω
  have hle : ∀ k, |d t i ω| ≤ (|(A ^ k) i 0| + |(A ^ k) i 1|) * (M₁ + M₂) := by
    intro k
    rw [𝔼.system_iterate hd had t k i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, add_mul]
    gcongr
    · exact 𝔼.abs_E_le (hdb (t + k) 0) t ω
    · exact 𝔼.abs_E_le (hdb (t + k) 1) t ω
  have hlim : Tendsto (fun k => (|(A ^ k) i 0| + |(A ^ k) i 1|) * (M₁ + M₂)) atTop (𝓝 0) := by
    simpa using
      (((tendsto_pow_entry hA i 0).abs.add (tendsto_pow_entry hA i 1).abs).mul_const (M₁ + M₂))
  have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
  have : d t i ω = 0 := abs_nonpos_iff.mp h0
  simpa [hd_def, sub_eq_zero] using this

/-- **Multiplicity without Schur–Cohn**: if `A` fails the Schur–Cohn
condition, then next to any bounded adapted solution of
`x_t = A E_t x_{t+1} + w_t` there is a different one, obtained by adding a
deterministic self-fulfilling path (Galí, p. 65). -/
theorem system_not_unique [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ¬ SchurStable (tr2 A) (det2 A)) {w x : ℕ → Fin 2 → Ω → ℝ}
    (hx : 𝔼.Solves A w x) (hax : 𝔼.AdaptedVec x) (hbx : BoundedVec x) :
    ∃ y, 𝔼.Solves A w y ∧ 𝔼.AdaptedVec y ∧ BoundedVec y ∧ y ≠ x := by
  obtain ⟨s, hs, ⟨Ms, hMs⟩, hs0⟩ := exists_bounded_homogeneous hA
  obtain ⟨M, hM⟩ := hbx
  refine ⟨fun t i => x t i + fun _ => s t i, fun t i => ?_, fun t i => ?_, ⟨M + Ms, ?_⟩, ?_⟩
  · simp only [map_add, 𝔼.const, smul_add]
    rw [hx t i]
    have hsi := congrFun (hs t) i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hsi
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsi]
    ring
  · simp only [map_add, hax t i, 𝔼.const]
  · intro t i ω
    exact (abs_add_le _ _).trans (add_le_add (hM t i ω) (hMs t i))
  · intro h
    apply hs0
    funext t i
    have := congrFun (congrFun (congrFun h t) i) (Classical.arbitrary Ω)
    simpa using this

/-- Determinacy: the system `x_t = A E_t x_{t+1} + w_t` has at most one
bounded adapted solution. -/
def Determinate (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ w x y : ℕ → Fin 2 → Ω → ℝ, 𝔼.Solves A w x → 𝔼.Solves A w y →
    𝔼.AdaptedVec x → 𝔼.AdaptedVec y → BoundedVec x → BoundedVec y → x = y

/-- **Determinacy iff Schur–Cohn** (Galí, p. 65): a two-variable system in
non-predetermined variables is determinate if and only if both eigenvalues of
`A` lie inside the unit circle, i.e. `|det A| < 1` and `|tr A| < 1 + det A`. -/
theorem determinate_iff [Nonempty Ω] (A : Matrix (Fin 2) (Fin 2) ℝ) :
    𝔼.Determinate A ↔ SchurStable (tr2 A) (det2 A) := by
  constructor
  · intro hdet
    by_contra hA
    have hz : 𝔼.Solves A 0 0 := fun t i => by simp
    obtain ⟨y, hy, hay, hby, hne⟩ :=
      𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    exact hne (hdet 0 y 0 hy hz hay (fun t i => by simp) hby ⟨0, fun t i ω => by simp⟩)
  · intro hA w x y hx hy hax hay hbx hby
    exact 𝔼.system_unique hA hx hy hax hay hbx hby

end ExpectationSystem

end Gali.DiscretionCommitment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expectations on a finite event tree

Galí (2015), Chapter 3, writes every equilibrium condition with conditional
expectations `E_t` (e.g. eqs. (22)–(23), p. 63, and (34), p. 75). The module
`Expectations` axiomatises `E_t` as an `ExpectationSystem`. This module shows
that the axioms are satisfiable under genuine uncertainty, so that the theorems
proved for an arbitrary `ExpectationSystem` are not about perfect foresight only.

The model is a finite state space `Ω` with strictly positive probabilities and
an information structure given by a refining sequence of partitions
`info t : Setoid Ω` (finer as `t` grows). The conditional expectation at date
`t` is the probability-weighted average over the information cell:

  `E_t x ω = (∑_{ω' ~_t ω} p ω' x ω') / (∑_{ω' ~_t ω} p ω')`.

## Main results

* `FiniteTree.toExpectationSystem`: every finite tree gives an
  `ExpectationSystem` (linearity, constants, monotonicity, the law of iterated
  expectations, and knowledge of earlier information are all proved).
* `FiniteTree.condE_of_trivial`: with no information, `E_t` is the unconditional
  mean `∑ p ω x ω`.
* `coinSystem_not_perfectForesight`: in a two-period coin-flip tree, `E_0` is
  not the identity, so the instance is genuinely stochastic.
* `coinAR1_isAR1`: the AR(1) process `u_{t+1} = ρ u_t + ε_{t+1}` driven by
  mean-zero coin-flip innovations satisfies `IsAR1`.

## Why not Mathlib's `condExp`

Mathlib's `MeasureTheory.condExp` on a filtration is defined only up to
almost-everywhere equality: `μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁]`, not `=`. The fields
of `ExpectationSystem` are exact equalities of functions, so `condExp` does not
give an instance directly. On a finite space with strictly positive weights
a.e. equality is equality, and the explicit cell averages below are exactly the
conditional expectations.

Restated from the `Gali/MonetaryPolicyDesign` project (each project in this
repository is self-contained).
-/

namespace Gali.DiscretionCommitment.ExpectationsFiniteTree

variable (Ω : Type*) [Fintype Ω]

/-- A finite event tree (Galí 2015, ch. 3, the uncertainty behind `E_t`, p. 63): strictly
positive state probabilities summing to one, and partitions `info t` that refine over time. -/
structure FiniteTree where
  /-- The probability of each state. -/
  prob : Ω → ℝ
  /-- Every state has strictly positive probability. -/
  prob_pos : ∀ ω, 0 < prob ω
  /-- Probabilities sum to one. -/
  prob_sum : ∑ ω, prob ω = 1
  /-- The information partition at date `t`: `ω ~_t ω'` iff indistinguishable at `t`. -/
  info : ℕ → Setoid Ω
  /-- Information accumulates: date-`t` cells are subsets of date-`s` cells for `s ≤ t`. -/
  refines : ∀ {s t : ℕ}, s ≤ t → ∀ a b, info t a b → info s a b

namespace FiniteTree

variable {Ω} (T : FiniteTree Ω)

open Classical in
/-- Galí (2015), ch. 3, p. 63 (meaning of `E_t`): the probability of the date-`t`
information cell of `ω`. -/
noncomputable def mass (t : ℕ) (ω : Ω) : ℝ :=
  ∑ ω', if T.info t ω' ω then T.prob ω' else 0

open Classical in
/-- Galí (2015), ch. 3, p. 63 (meaning of `E_t`): the probability-weighted sum of `x`
over the date-`t` information cell of `ω`. -/
noncomputable def num (t : ℕ) (x : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ ω', if T.info t ω' ω then T.prob ω' * x ω' else 0

/-- Galí (2015), ch. 3, p. 63: the conditional expectation `E_t x` on a finite tree,
the cell average of `x`. -/
noncomputable def condE (t : ℕ) (x : Ω → ℝ) : Ω → ℝ :=
  fun ω => T.num t x ω / T.mass t ω

/-- Galí (2015), ch. 3, p. 63: every information cell has strictly positive probability. -/
theorem mass_pos (t : ℕ) (ω : Ω) : 0 < T.mass t ω := by
  classical
  unfold mass
  have hle : ∀ ω' ∈ Finset.univ,
      (0 : ℝ) ≤ if T.info t ω' ω then T.prob ω' else 0 := fun ω' _ => by
    split_ifs
    · exact (T.prob_pos ω').le
    · exact le_rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hle (Finset.mem_univ ω))
  simp only [(T.info t).refl ω, ↓reduceIte]
  exact T.prob_pos ω

/-- Galí (2015), ch. 3, p. 63: indistinguishable states have the same cell probability. -/
theorem mass_congr {t : ℕ} {ω₁ ω₂ : Ω} (h : T.info t ω₁ ω₂) : T.mass t ω₁ = T.mass t ω₂ := by
  unfold mass
  refine Finset.sum_congr rfl fun ω' _ => ?_
  have : T.info t ω' ω₁ ↔ T.info t ω' ω₂ :=
    ⟨fun h' => (T.info t).trans h' h, fun h' => (T.info t).trans h' ((T.info t).symm h)⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

/-- Galí (2015), ch. 3, p. 63: indistinguishable states have the same weighted cell sum. -/
theorem num_congr {t : ℕ} (x : Ω → ℝ) {ω₁ ω₂ : Ω} (h : T.info t ω₁ ω₂) :
    T.num t x ω₁ = T.num t x ω₂ := by
  unfold num
  refine Finset.sum_congr rfl fun ω' _ => ?_
  have : T.info t ω' ω₁ ↔ T.info t ω' ω₂ :=
    ⟨fun h' => (T.info t).trans h' h, fun h' => (T.info t).trans h' ((T.info t).symm h)⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

/-- Galí (2015), ch. 3, p. 63: `E_t x` is constant on date-`t` information cells. -/
theorem condE_congr {t : ℕ} (x : Ω → ℝ) {ω₁ ω₂ : Ω} (h : T.info t ω₁ ω₂) :
    T.condE t x ω₁ = T.condE t x ω₂ := by
  unfold condE
  rw [T.num_congr x h, T.mass_congr h]

/-- Galí (2015), ch. 3, p. 63: a variable constant on the date-`t` cell of `ω` is its own
conditional expectation at `ω` (what is known is not forecast). -/
theorem condE_of_const_on_cell {t : ℕ} {y : Ω → ℝ} {ω : Ω}
    (hy : ∀ ω', T.info t ω' ω → y ω' = y ω) : T.condE t y ω = y ω := by
  classical
  unfold condE num
  have hn : (∑ ω', if T.info t ω' ω then T.prob ω' * y ω' else 0) = T.mass t ω * y ω := by
    unfold mass
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    by_cases h : T.info t ω' ω
    · simp only [h, ↓reduceIte, hy ω' h]
    · simp only [h, ↓reduceIte, zero_mul]
  rw [hn, mul_div_cancel_left₀ _ (T.mass_pos t ω).ne']

/-- Galí (2015), ch. 3, p. 63: conditional expectation is additive. -/
theorem condE_add (t : ℕ) (x y : Ω → ℝ) : T.condE t (x + y) = T.condE t x + T.condE t y := by
  funext ω
  simp only [condE, num, Pi.add_apply, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  split_ifs <;> ring

/-- Galí (2015), ch. 3, p. 63: conditional expectation is homogeneous. -/
theorem condE_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) : T.condE t (c • x) = c • T.condE t x := by
  funext ω
  simp only [condE, num, Pi.smul_apply, smul_eq_mul, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  split_ifs <;> ring

/-- Galí (2015), ch. 3, p. 63: conditional expectation as a linear map. -/
noncomputable def condELin (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun := T.condE t
  map_add' := T.condE_add t
  map_smul' := T.condE_smul t

/-- Galí (2015), ch. 3, p. 63: constants are their own conditional expectation. -/
theorem condE_const (t : ℕ) (c : ℝ) : T.condE t (fun _ => c) = fun _ => c := by
  funext ω
  exact T.condE_of_const_on_cell fun _ _ => rfl

/-- Galí (2015), ch. 3, p. 63: conditional expectation preserves the pointwise order. -/
theorem condE_mono (t : ℕ) {x y : Ω → ℝ} (h : x ≤ y) : T.condE t x ≤ T.condE t y := by
  intro ω
  unfold condE
  refine div_le_div_of_nonneg_right ?_ (T.mass_pos t ω).le
  unfold num
  refine Finset.sum_le_sum fun ω' _ => ?_
  split_ifs
  · exact mul_le_mul_of_nonneg_left (h ω') (T.prob_pos ω').le
  · exact le_rfl

/-- Galí (2015), ch. 3, p. 63: earlier forecasts are known later, `E_t E_s = E_s` for
`s ≤ t`, because date-`t` cells lie inside date-`s` cells. -/
theorem condE_known {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    T.condE t (T.condE s x) = T.condE s x := by
  funext ω
  exact T.condE_of_const_on_cell fun ω' h => T.condE_congr x (T.refines hst ω' ω h)

/-- Galí (2015), ch. 3, p. 63: the law of iterated expectations, `E_s E_t = E_s` for
`s ≤ t`, proved by splitting each date-`s` cell into date-`t` cells. -/
theorem condE_tower {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    T.condE s (T.condE t x) = T.condE s x := by
  classical
  funext ω
  change T.num s (T.condE t x) ω / T.mass s ω = T.num s x ω / T.mass s ω
  congr 1
  change (∑ ω', if T.info s ω' ω then T.prob ω' * T.condE t x ω' else 0) =
    ∑ ω', if T.info s ω' ω then T.prob ω' * x ω' else 0
  -- expand the inner expectation and swap the order of summation
  have hexp : ∀ ω',
      (if T.info s ω' ω then T.prob ω' * T.condE t x ω' else 0) =
        ∑ ω'', if T.info s ω'' ω ∧ T.info t ω' ω'' then
          T.prob ω' * (T.prob ω'' * x ω'' / T.mass t ω'') else 0 := by
    intro ω'
    unfold condE num
    by_cases hs : T.info s ω' ω
    · simp only [hs, ↓reduceIte]
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω'' _ => ?_
      by_cases ht : T.info t ω'' ω'
      · have ht' : T.info t ω' ω'' := (T.info t).symm ht
        have hs'' : T.info s ω'' ω := (T.info s).trans (T.refines hst ω'' ω' ht) hs
        simp only [ht, ht', hs'', and_self, ↓reduceIte, T.mass_congr ht]
      · have ht' : ¬ T.info t ω' ω'' := fun h => ht ((T.info t).symm h)
        simp only [ht, ht', and_false, ↓reduceIte, zero_div, mul_zero]
    · simp only [hs, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun ω'' _ => ?_
      by_cases h : T.info s ω'' ω ∧ T.info t ω' ω''
      · exact absurd ((T.info s).trans (T.refines hst ω' ω'' h.2) h.1) hs
      · simp only [h, ↓reduceIte]
  rw [Finset.sum_congr rfl fun ω' _ => hexp ω', Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' _ => ?_
  by_cases hs : T.info s ω'' ω
  · simp only [hs, true_and, ↓reduceIte]
    have hm : (∑ ω', if T.info t ω' ω'' then T.prob ω' else 0) = T.mass t ω'' := rfl
    calc (∑ ω', if T.info t ω' ω'' then
            T.prob ω' * (T.prob ω'' * x ω'' / T.mass t ω'') else 0)
        = (∑ ω', if T.info t ω' ω'' then T.prob ω' else 0) *
            (T.prob ω'' * x ω'' / T.mass t ω'') := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω' _ => ?_
          split_ifs <;> ring
      _ = T.prob ω'' * x ω'' := by
          rw [hm]
          field_simp [(T.mass_pos t ω'').ne']
  · simp only [hs, false_and, ↓reduceIte, Finset.sum_const_zero]

/-- Galí (2015), ch. 3, p. 63: a finite event tree defines an `ExpectationSystem`, so the
axioms behind every `E_t` in the book are satisfiable under genuine uncertainty. -/
noncomputable def toExpectationSystem : ExpectationSystem Ω where
  E := T.condELin
  const := T.condE_const
  mono := fun t _ _ h => T.condE_mono t h
  tower := fun hst x => T.condE_tower hst x
  known := fun hst x => T.condE_known hst x

/-- Galí (2015), ch. 3, p. 63: the expectation operator of the tree is the cell average. -/
theorem toExpectationSystem_E (t : ℕ) (x : Ω → ℝ) :
    T.toExpectationSystem.E t x = T.condE t x := rfl

/-- Galí (2015), ch. 3, p. 63: with no information at date `t` (one cell), `E_t` is the
unconditional mean `∑ p ω x ω`. -/
theorem condE_of_trivial {t : ℕ} (htriv : ∀ a b, T.info t a b) (x : Ω → ℝ) (ω : Ω) :
    T.condE t x ω = ∑ ω', T.prob ω' * x ω' := by
  unfold condE num mass
  simp only [htriv, ↓reduceIte, T.prob_sum, div_one]

end FiniteTree

/-! ### A two-period coin-flip tree -/

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): what is observed of two coin flips at
date `t`; the first flip is revealed at date 1 and the second at date 2. -/
def coinObs (t : ℕ) (ω : Bool × Bool) : Bool × Bool :=
  (if 1 ≤ t then ω.1 else false, if 2 ≤ t then ω.2 else false)

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): two fair coin flips revealed one per
period, with nothing known at date 0. -/
noncomputable def coinTree : FiniteTree (Bool × Bool) where
  prob := fun _ => 1 / 4
  prob_pos := fun _ => by norm_num
  prob_sum := by simp
  info := fun t => Setoid.ker (coinObs t)
  refines := by
    intro s t hst a b h
    rw [Setoid.ker_def] at h ⊢
    simp only [coinObs, Prod.mk.injEq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    constructor
    · by_cases hs : 1 ≤ s
      · have ht : 1 ≤ t := le_trans hs hst
        simpa [hs, ht] using h1
      · simp [hs]
    · by_cases hs : 2 ≤ s
      · have ht : 2 ≤ t := le_trans hs hst
        simpa [hs, ht] using h2
      · simp [hs]

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the expectation system of the
coin-flip tree. -/
noncomputable def coinSystem : ExpectationSystem (Bool × Bool) :=
  coinTree.toExpectationSystem

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the indicator of heads on the first
flip. -/
def firstHeads (ω : Bool × Bool) : ℝ := if ω.1 then 1 else 0

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): at date 0 the forecast of the first
flip is `1/2` in every state. -/
theorem coinSystem_E0_firstHeads (ω : Bool × Bool) : coinSystem.E 0 firstHeads ω = 1 / 2 := by
  have htriv : ∀ a b, coinTree.info 0 a b := fun a b => by
    change Setoid.ker (coinObs 0) a b
    rw [Setoid.ker_def]
    simp [coinObs]
  rw [coinSystem, FiniteTree.toExpectationSystem_E, coinTree.condE_of_trivial htriv]
  simp [coinTree, firstHeads, Fintype.sum_prod_type]
  norm_num

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the coin-flip system is not perfect
foresight, since `E_0` differs from the identity. -/
theorem coinSystem_not_perfectForesight : coinSystem.E 0 firstHeads ≠ firstHeads := by
  intro h
  have := congrFun h (true, true)
  rw [coinSystem_E0_firstHeads] at this
  norm_num [firstHeads] at this

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the mean-zero innovation `ε_t`, equal
to `±1` with the first flip at date 1, `±1` with the second flip at date 2, zero otherwise. -/
def coinShock (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 1 then (if ω.1 then 1 else -1) else if t = 2 then (if ω.2 then 1 else -1) else 0

/-- Galí (2015), ch. 3, p. 63 (uncertainty example; AR(1) as in (6), p. 55): the process
`u_0 = 0`, `u_{t+1} = ρ u_t + ε_{t+1}`. -/
def coinAR1 (ρ : ℝ) : ℕ → Bool × Bool → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => ρ * coinAR1 ρ t ω + coinShock (t + 1) ω

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the date-`t` innovation is known at `t`. -/
theorem coinShock_measurable (t : ℕ) {ω ω' : Bool × Bool} (h : coinTree.info t ω' ω) :
    coinShock t ω' = coinShock t ω := by
  change Setoid.ker (coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [coinObs, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  unfold coinShock
  by_cases ht1 : t = 1
  · subst ht1
    simp only [le_refl, ↓reduceIte] at h1
    simp [h1]
  · by_cases ht2 : t = 2
    · subst ht2
      simp only [↓reduceIte, le_refl] at h2
      simp [h2]
    · simp [ht1, ht2]

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the AR(1) process is adapted. -/
theorem coinAR1_measurable (ρ : ℝ) (t : ℕ) {ω ω' : Bool × Bool} (h : coinTree.info t ω' ω) :
    coinAR1 ρ t ω' = coinAR1 ρ t ω := by
  induction t generalizing ω ω' with
  | zero => rfl
  | succ t ih =>
    simp only [coinAR1]
    rw [ih (coinTree.refines (Nat.le_succ t) ω' ω h), coinShock_measurable (t + 1) h]

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): innovations have conditional mean
zero, `E_t ε_{t+1} = 0`. -/
theorem coinShock_mean_zero (t : ℕ) : coinSystem.E t (coinShock (t + 1)) = 0 := by
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  rcases t with _ | _ | t
  · have htriv : ∀ a b, coinTree.info 0 a b := fun a b => by
      change Setoid.ker (coinObs 0) a b
      rw [Setoid.ker_def]
      simp [coinObs]
    rw [coinTree.condE_of_trivial htriv]
    simp [coinTree, coinShock, Fintype.sum_prod_type]
  · unfold FiniteTree.condE FiniteTree.num
    have hcell : ∀ ω' : Bool × Bool, coinTree.info 1 ω' ω ↔ ω'.1 = ω.1 := fun ω' => by
      change Setoid.ker (coinObs 1) ω' ω ↔ _
      rw [Setoid.ker_def]
      simp [coinObs]
    simp only [hcell]
    rcases ω with ⟨b1, b2⟩
    cases b1 <;> simp [coinTree, coinShock, Fintype.sum_prod_type]
  · have h0 : coinShock (t + 1 + 1 + 1) = 0 := by
      funext ω'
      simp [coinShock]
    rw [h0]
    have := coinTree.condE_smul (t + 1 + 1) 0 0
    simp only [zero_smul] at this
    rw [this]

/-- Galí (2015), ch. 3, p. 63 (uncertainty example; AR(1) as in (6), p. 55): the process
`u_{t+1} = ρ u_t + ε_{t+1}` is an AR(1) in the sense of `IsAR1` under genuine uncertainty. -/
theorem coinAR1_isAR1 (ρ : ℝ) : coinSystem.IsAR1 ρ (coinAR1 ρ) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext ω
    rw [coinSystem, FiniteTree.toExpectationSystem_E]
    exact coinTree.condE_of_const_on_cell fun ω' h => coinAR1_measurable ρ t h
  · have hsplit : coinAR1 ρ (t + 1) = ρ • coinAR1 ρ t + coinShock (t + 1) := by
      funext ω
      simp [coinAR1]
    have had : coinSystem.E t (coinAR1 ρ t) = coinAR1 ρ t := by
      funext ω
      rw [coinSystem, FiniteTree.toExpectationSystem_E]
      exact coinTree.condE_of_const_on_cell fun ω' h => coinAR1_measurable ρ t h
    rw [hsplit, map_add, map_smul, had, coinShock_mean_zero, add_zero]

/-- Galí (2015), ch. 3, p. 63 (uncertainty example): the AR(1) process is genuinely random:
at date 1 it differs across states (`u_1 = ±1`), while its date-0 forecast is `ρ u_0 = 0`. -/
theorem coinAR1_nondegenerate (ρ : ℝ) :
    coinAR1 ρ 1 (true, true) = 1 ∧ coinAR1 ρ 1 (false, true) = -1 ∧
      coinSystem.E 0 (coinAR1 ρ 1) = 0 := by
  refine ⟨by simp [coinAR1, coinShock], by simp [coinAR1, coinShock], ?_⟩
  rw [(coinAR1_isAR1 ρ).2 0]
  funext ω
  simp [coinAR1]

end Gali.DiscretionCommitment.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The loss function and the NKPC with a cost-push shock

Galí (2015), Chapter 5, §5.2 introduction (pp. 127–129) and Appendix 5.1 (pp. 154–156).

## The loss (1) and the weight `ϑ = κ/ε`

* `vartheta_eq_weight_ratio`: the Chapter 4 welfare criterion
  `½ ∑ βᵗ [(σ + (φ+α)/(1−α)) x_t² + (ε/λ) π_t²]` has gap weight relative to inflation
  `(σ + (φ+α)/(1−α))/(ε/λ) = κ/ε = ϑ` (exact).
* `periodLoss_eq_scaled`, `hasSum_welfare_of_loss`, `expected_welfare_eq_scaled_loss`,
  `welfare_le_iff_loss_le`: the welfare loss is exactly `(ε/(2λ))` times
  `∑ βᵗ (π_t² + ϑ x_t²)`, the loss (1), path by path and in conditional expectation, so the
  two criteria rank policies identically.

## The NKPC (2) with a cost-push shock

* `nkpc_iff_costPush`: the Chapter 3 NKPC in `y − y^n` holds iff (2)
  `π_t = β E_t π_{t+1} + κ x_t + u_t` holds with `x = y − y^e`, `u = κ(y^e − y^n)`.
* `costPush_eq_zero_iff`, `zero_outcome_iff`: `π ≡ x ≡ 0` is an equilibrium outcome iff
  `u ≡ 0` iff `y^e = y^n` (the tradeoff of p. 128).

## Appendix 5.1: a small steady-state distortion

* `distortion_iff`: `−U_n/U_c = MPN (1 − Φ)` with `MPN = (1 − α) Y/N` is
  `U_n N = −(1 − Φ)(1 − α) U_c C`.
* `secondOrderUtility_eq_distorted` (**exact completing the square**): the second-order
  polynomial of period utility equals
  `U_c C [Φ x̂ − ½(Γ x̂² + (ε/Θ) var_i p(i))] + t.i.p. + (third-order terms) + U_c C Φ Q`
  with `x̂ = ŷ − ψ_ya a` and an explicit second-order `Q`.
* `small_distortion_polynomial`: along one-parameter families with `Φ = O(s)`, the book's
  approximation is correct to `O(s³)`.
* `period_utility_small_distortion` (**the analytic bridge**): for actual `C³` utility at a
  fixed distorted steady state, period utility equals the book's expression plus
  `U_c C Φ Q(s)` plus `O(s³)`, with `Q = O(s²)`: the neglected term is exactly
  "the product of `Φ` with a second-order term".
* `welfare_small_distortion`: summing with Lemma 2 (restated from the Chapter 4 project), the
  welfare loss is exactly `W = −∑ βᵗ [Φ x̂_t − ½((ε/λ) π_t² + (σ + (φ+α)/(1−α)) x̂_t²)]`;
  `welfareW_efficient`: for `Φ = 0` this is `(ε/(2λ)) ∑ βᵗ (π_t² + ϑ x_t²)`, the loss (1).

The Taylor-expansion machinery and Lemma 2 are restated from the Chapter 4 project
(`MonetaryPolicyDesign/Welfare.lean`).
-/

namespace Gali.DiscretionCommitment.LossAndCostPush

open Asymptotics Filter Topology

/-! ### Parameters (restated from the Chapter 4 project) -/

/-- Galí (2015), p. 111 and App. 5.1, p. 155: the output-gap coefficient of the loss,
`Γ = σ + (φ + α)/(1 − α)` (restated from the Chapter 4 project). -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), App. 5.1, p. 155 (and ch. 3, p. 62): `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`,
so that efficient output is `ŷ^e_t = ψ_ya a_t` (restated from the Chapter 4 project). -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), ch. 3, p. 61: `Θ = (1 − α)/(1 − α + αε)` (restated from the Chapter 4
project). -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), ch. 3, p. 61: `λ = (1 − θ)(1 − βθ)Θ/θ` (restated from the Chapter 4
project). -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), ch. 3, p. 63: `κ = λ(σ + (φ + α)/(1 − α))` (restated from the Chapter 4
project). -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * gapCoeff σ φ α

/-- Galí (2015), p. 128: the relative weight of the welfare-relevant output gap in the loss
(1), `ϑ = κ/ε`. -/
noncomputable def vartheta (β θ σ φ α ε : ℝ) : ℝ := kappaNK β θ σ φ α ε / ε

/-- Galí (2015), ch. 3, p. 61: `Θ > 0` for `0 ≤ α < 1`, `ε > 0`. -/
theorem bigTheta_pos {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    0 < bigTheta α ε := by
  unfold bigTheta
  have : 0 ≤ α * ε := mul_nonneg hα0 hε.le
  exact div_pos (by linarith) (by linarith)

/-- Galí (2015), ch. 3, p. 61: `λ > 0` for `0 < θ < 1`, `β < 1`, `0 ≤ α < 1`, `ε > 0`. -/
theorem lambdaNK_pos {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < lambdaNK β θ α ε := by
  unfold lambdaNK
  have h1 : 0 < 1 - β * θ := by nlinarith
  have h2 : 0 < 1 - θ := by linarith
  exact mul_pos (div_pos (mul_pos h2 h1) hθ0) (bigTheta_pos hα0 hα1 hε)

/-- Galí (2015), p. 111: `σ + (φ + α)/(1 − α) > 0` for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem gapCoeff_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < gapCoeff σ φ α := by
  unfold gapCoeff
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 128: under the standing assumptions (`0 < θ < 1`, `0 < β < 1`,
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `ε > 1`), `ϑ = κ/ε > 0`. -/
theorem vartheta_pos {β θ σ φ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) :
    0 < vartheta β θ σ φ α ε := by
  unfold vartheta kappaNK
  exact div_pos (mul_pos (lambdaNK_pos hθ0 hθ1 hβ1 hα0 hα1 (by linarith))
    (gapCoeff_pos hσ hφ hα0 hα1)) (by linarith)

/-! ### The loss function (1) -/

/-- Galí (2015), p. 128 (**`ϑ = κ/ε` from the welfare criterion, exact**): in the Chapter 4
welfare loss `½[(σ + (φ+α)/(1−α)) x² + (ε/λ) π²]` the weight of the gap relative to inflation
is `(σ + (φ+α)/(1−α))/(ε/λ) = κ/ε = ϑ`. -/
theorem vartheta_eq_weight_ratio {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0) :
    gapCoeff σ φ α / (ε / lambdaNK β θ α ε) = vartheta β θ σ φ α ε := by
  unfold vartheta kappaNK
  field_simp

/-- Galí (2015), p. 128 and App. 5.1, p. 156 (the period loss, exact): the Chapter 4 period
welfare loss is `ε/(2λ)` times the period loss of (1):
`½[(σ + (φ+α)/(1−α)) x² + (ε/λ) π²] = (ε/(2λ)) (π² + ϑ x²)`. -/
theorem periodLoss_eq_scaled {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    (x infl : ℝ) :
    (gapCoeff σ φ α * x ^ 2 + ε / lambdaNK β θ α ε * infl ^ 2) / 2
      = ε / (2 * lambdaNK β θ α ε) * (infl ^ 2 + vartheta β θ σ φ α ε * x ^ 2) := by
  unfold vartheta kappaNK
  field_simp
  ring

/-- Galí (2015), eq. (1), p. 128 (**the welfare loss is proportional to (1), exact**): if
`∑ βᵗ (π_t² + ϑ x_t²)` converges to `L`, then the welfare loss
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) x_t² + (ε/λ) π_t²]` converges to `(ε/(2λ)) L`. -/
theorem hasSum_welfare_of_loss {β θ σ φ α ε L : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    {x infl : ℕ → ℝ}
    (hL : HasSum (fun t => β ^ t * (infl t ^ 2 + vartheta β θ σ φ α ε * x t ^ 2)) L) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * x t ^ 2 +
      ε / lambdaNK β θ α ε * infl t ^ 2) / 2)) (ε / (2 * lambdaNK β θ α ε) * L) := by
  convert hL.mul_left (ε / (2 * lambdaNK β θ α ε)) using 1
  funext t
  rw [periodLoss_eq_scaled hlam hε]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (1), p. 128 (**in expectation**): if, state by state, the welfare loss
converges to `W ω` and `∑ βᵗ (π_t² + ϑ x_t²)` converges to `L ω`, then
`E_0 W = (ε/(2λ)) E_0 L`: the expected welfare loss is proportional to (1). -/
theorem expected_welfare_eq_scaled_loss {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0)
    (hε : ε ≠ 0) {x infl : ℕ → Ω → ℝ} {W L : Ω → ℝ}
    (hW : ∀ ω, HasSum (fun t => β ^ t * ((gapCoeff σ φ α * x t ω ^ 2 +
      ε / lambdaNK β θ α ε * infl t ω ^ 2) / 2)) (W ω))
    (hL : ∀ ω, HasSum (fun t => β ^ t * (infl t ω ^ 2 +
      vartheta β θ σ φ α ε * x t ω ^ 2)) (L ω)) :
    𝔼.E 0 W = (ε / (2 * lambdaNK β θ α ε)) • 𝔼.E 0 L := by
  have hWL : W = (ε / (2 * lambdaNK β θ α ε)) • L := funext fun ω =>
    (hW ω).unique (hasSum_welfare_of_loss hlam hε (hL ω))
  rw [hWL, map_smul]

/-- Galí (2015), p. 128: since `ε/(2λ) > 0`, the welfare loss and the loss (1) rank any two
policies identically. -/
theorem welfare_le_iff_loss_le {β θ α ε L₁ L₂ : ℝ} (hlam : 0 < lambdaNK β θ α ε) (hε : 0 < ε) :
    ε / (2 * lambdaNK β θ α ε) * L₁ ≤ ε / (2 * lambdaNK β θ α ε) * L₂ ↔ L₁ ≤ L₂ :=
  mul_le_mul_iff_of_pos_left (div_pos hε (by linarith))

/-! ### The NKPC with a cost-push shock (2) -/

/-- Galí (2015), eq. (2), p. 128: the cost-push shock `u_t = κ (y^e_t − y^n_t)`. -/
def costPush (κ : ℝ) (ye yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => κ • (ye t - yn t)

/-- Galí (2015), ch. 3 (eq. (22), p. 63), recalled on p. 128: the NKPC in the output gap
relative to natural output, `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`. -/
def NKPCNatural (β κ : ℝ) (y yn infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - yn t)

/-- Galí (2015), eq. (2), p. 128: `π_t = β E_t π_{t+1} + κ x_t + u_t`, with `x` the
welfare-relevant output gap. -/
def NKPC (β κ : ℝ) (x u infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), eq. (2), p. 128 (**exact**): substituting `y_t − y^n_t = (y_t − y^e_t) +
(y^e_t − y^n_t)`, the Chapter 3 NKPC holds iff (2) holds with the welfare-relevant gap
`x = y − y^e` and the cost-push shock `u = κ(y^e − y^n)`. -/
theorem nkpc_iff_costPush {β κ : ℝ} {y ye yn infl : ℕ → Ω → ℝ} :
    NKPCNatural 𝔼 β κ y yn infl ↔
      NKPC 𝔼 β κ (fun t => y t - ye t) (costPush κ ye yn) infl := by
  have key : ∀ t, κ • (y t - yn t) = κ • (y t - ye t) + costPush κ ye yn t := fun t => by
    funext ω
    simp only [costPush, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  constructor
  · intro h t
    rw [h t, key t, add_assoc]
  · intro h t
    rw [h t, key t, add_assoc]

/-- Galí (2015), p. 128: for `κ ≠ 0` the cost-push shock vanishes identically iff efficient
and natural output coincide (the Chapter 4 case). -/
theorem costPush_eq_zero_iff {κ : ℝ} (hκ : κ ≠ 0) {ye yn : ℕ → Ω → ℝ} :
    costPush κ ye yn = 0 ↔ ye = yn := by
  constructor
  · intro h
    funext t ω
    have := congrFun (congrFun h t) ω
    simp only [costPush, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply,
      mul_eq_zero, hκ, false_or] at this
    linarith
  · rintro rfl
    funext t ω
    simp [costPush]

/-- Galí (2015), p. 128 (**the tradeoff**): zero inflation together with an efficient level
of activity, `π ≡ 0` and `x ≡ 0`, satisfies (2) iff `u ≡ 0`. Hence any variation in `u`
makes the two goals jointly unattainable. -/
theorem zero_outcome_iff {β κ : ℝ} {u : ℕ → Ω → ℝ} : NKPC 𝔼 β κ 0 u 0 ↔ u = 0 := by
  constructor
  · intro h
    funext t
    have := h t
    simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at this
    exact this.symm
  · rintro rfl t
    simp

/-! ### Orders of magnitude and Taylor expansions (restated from the Chapter 4 project) -/

/-- Orders of magnitude multiply: `f = O(sᵃ)` and `g = O(sᵇ)` give `f g = O(sᵃ⁺ᵇ)`
(Galí 2015, App. 5.1, p. 155; restated from the Chapter 4 project). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Higher orders are smaller near `0`: `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b` (Galí 2015, App. 5.1,
p. 155; restated from the Chapter 4 project). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- A quantity that is `O(s)` tends to `0` (Galí 2015, App. 5.1; restated from the Chapter 4
project). -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-- Galí (2015), App. 4.1, p. 117, used in App. 5.1, p. 154 (second-order Taylor expansion
with a cubic remainder; restated from the Chapter 4 project): if `f` is `C³` near `x₀`, then
`f x = f x₀ + f'(x₀)(x − x₀) + f''(x₀)/2 (x − x₀)² + O((x − x₀)³)`. -/
theorem taylor_two {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 3 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) - iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      =O[𝓝 x₀] fun x => (x - x₀) ^ 3 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 3 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have e3 := iteratedDerivWithin_of_isOpen (n := 3) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) -
      iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      = fun x => (f x - taylorWithinEval f 3 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 3 f x₀ / 6 * (x - x₀) ^ 3 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      e3, iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 4.1, p. 117: `e^x = 1 + x + x²/2 + O(x³)` (restated from the Chapter 4
project). -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 4.1, p. 117: `e^x − 1 = O(x)` (restated from the Chapter 4 project). -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 4.1, p. 117 (second-order expansion in log deviations; restated from
the Chapter 4 project): if `f` is `C³` near `X`, then with `X_t = X e^{x}`,
`f(X_t) − f(X) = f'(X) X (x + x²/2) + f''(X) X² x²/2 + O(x³)`. -/
theorem logdev_taylor {f : ℝ → ℝ} {X : ℝ} (hf : ContDiffAt ℝ 3 f X) :
    (fun x => f (X * Real.exp x) - f X - deriv f X * X * (x + x ^ 2 / 2) -
        iteratedDeriv 2 f X / 2 * X ^ 2 * x ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
  have hT := taylor_two hf
  have hg : Tendsto (fun x => X * Real.exp x) (𝓝 0) (𝓝 X) := by
    have := ((Real.continuous_exp.tendsto 0).const_mul X)
    simpa using this
  have hE1 := exp_sub_one_bigO
  have h1 : (fun x => f (X * Real.exp x) - f X - deriv f X * (X * Real.exp x - X) -
      iteratedDeriv 2 f X / 2 * (X * Real.exp x - X) ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
    refine (hT.comp_tendsto hg).trans ?_
    have hc : (fun x => (X * Real.exp x - X) ^ 3) =O[𝓝 0] fun x => x ^ 3 := by
      have : (fun x => (X * Real.exp x - X) ^ 3) = fun x => X ^ 3 * (Real.exp x - 1) ^ 3 := by
        funext x
        ring
      rw [this]
      have := hE1.pow 3
      simp only [← pow_mul] at this
      exact this.const_mul_left _
    exact hc
  have h2 : (fun x => deriv f X * X * (Real.exp x - 1 - x - x ^ 2 / 2)) =O[𝓝 0]
      fun x => x ^ 3 := exp_taylor_two.const_mul_left _
  have hA : (fun x => Real.exp x - 1 - x) =O[𝓝 0] fun x => x ^ 2 := by
    have : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 2 :=
      (isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left (fun x => by ring)
    refine ((bigO_weaken (by norm_num : 2 ≤ 3) exp_taylor_two).add this).congr_left
      fun x => ?_
    ring
  have hB : (fun x => Real.exp x - 1 + x) =O[𝓝 0] fun x => x ^ 1 :=
    hE1.add (by simpa using isBigO_refl (fun x : ℝ => x) (𝓝 0))
  have h3 : (fun x => iteratedDeriv 2 f X / 2 * X ^ 2 *
      ((Real.exp x - 1 - x) * (Real.exp x - 1 + x))) =O[𝓝 0] fun x => x ^ 3 :=
    (bigO_mul hA hB).const_mul_left _
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  ring

/-! ### Appendix 5.1: exact algebra with a distorted steady state -/

/-- Galí (2015), App. 5.1, p. 154 (the second-order polynomial in log deviations, restated
from the Chapter 4 project): with `Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y`
(output = consumption), `n` (hours) and `z` (preference shifter),
`Ū(z + z²/2) + K(y + (1−σ)/2 y²) + U_n N(n + (1+φ)/2 n²) + K y z + U_n N n z`. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 5.1, p. 155 (terms independent of policy, restated from the Chapter 4
project): an explicit function of the shocks `a`, `z` only. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 5.1, p. 155: the quadratic part
`−(K/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) var_i p(i)]`. -/
noncomputable def welfareQuadratic (K σ φ α ε y a v : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + ε / bigTheta α ε * v)

/-- Galí (2015), App. 5.1, p. 155: the welfare-relevant output gap in deviations,
`x̂ = ŷ − ŷ^e` with `ŷ^e = ψ_ya a`. -/
noncomputable def xhat (σ φ α y a : ℝ) : ℝ := y - psiYA σ φ α * a

/-- Galí (2015), App. 5.1, p. 155: the second-order term multiplying `Φ` that the
"small distortion" assumption neglects, `Q = d + (1 − α)((1+φ)/2 n² + n z)`. -/
noncomputable def distRemainder (φ α n z d : ℝ) : ℝ :=
  d + (1 - α) * ((1 + φ) / 2 * n ^ 2 + n * z)

/-- Galí (2015), App. 5.1, p. 155: a steady state with distortion `Φ`, `−U_n/U_c = MPN(1 − Φ)`
with `MPN = (1 − α) Y/N` and `Y = C`, is equivalent to `U_n N = −(1 − Φ)(1 − α) U_c C`. -/
theorem distortion_iff {α Φ Uc Un C N : ℝ} (hUc : Uc ≠ 0) (hN : N ≠ 0) :
    -Un / Uc = (1 - α) * C / N * (1 - Φ) ↔ Un * N = -(1 - Φ) * (1 - α) * (Uc * C) := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Galí (2015), App. 4.1, p. 119: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)` (restated from
the Chapter 4 project). -/
theorem gapCoeff_mul_psiYA {σ φ α : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), App. 4.1, pp. 117–119 (completing the square at an efficient steady state,
exact; restated from the Chapter 4 project): with `U_n N = −(1 − α) U_c C` and
`(1 − α) n = y − a + d`, the polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + K((ε/2Θ) v − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²)
+ d z)`. -/
theorem secondOrderUtility_eq_efficient {Ubar K UnN σ φ α ε y n z a d v : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = welfareQuadratic K σ φ α ε y a v + tip Ubar K σ φ α a z +
        K * (ε / (2 * bigTheta α ε) * v - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = (y - a + d) / (1 - α) := by
    field_simp
    linarith
  have hgp := gapCoeff_mul_psiYA (σ := σ) (φ := φ) hα hden
  have hgp2 : gapCoeff σ φ α * psiYA σ φ α ^ 2 = (1 + φ) / (1 - α) * psiYA σ φ α := by
    rw [← hgp]
    ring
  have hg : gapCoeff σ φ α = σ + (φ + α) / (1 - α) := rfl
  subst hUn hn'
  unfold secondOrderUtility welfareQuadratic tip
  rw [hgp2]
  have hexp : gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2
      = gapCoeff σ φ α * y ^ 2 - 2 * (gapCoeff σ φ α * psiYA σ φ α) * a * y +
        (1 + φ) / (1 - α) * psiYA σ φ α * a ^ 2 := by
    rw [← hgp2]
    ring
  rw [hexp, hgp, hg]
  field_simp
  ring

/-- Galí (2015), App. 5.1, pp. 154–155 (**completing the square with a distorted steady state,
exact**). If `U_n N = −(1 − Φ)(1 − α) U_c C` and `(1 − α) n = y − a + d`, then the
second-order polynomial equals
`K Φ x̂ − (K/2)[Γ x̂² + (ε/Θ) v] + t.i.p. + K Φ (ψ_ya − 1) a`
`+ K((ε/2Θ) v − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z) + K Φ Q`,
with `x̂ = y − ψ_ya a`, `Q = d + (1 − α)((1+φ)/2 n² + n z)`. The term `K Φ (ψ_ya − 1) a`
is independent of policy; the last three terms are third order when `d − (ε/2Θ)v = O(s³)`,
`d = O(s²)`, and (for the last) `Φ = O(s)`. -/
theorem secondOrderUtility_eq_distorted {Ubar K UnN σ φ α ε Φ y n z a d v : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - Φ) * (1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = K * Φ * xhat σ φ α y a + welfareQuadratic K σ φ α ε y a v + tip Ubar K σ φ α a z +
        K * Φ * (psiYA σ φ α - 1) * a + K * (ε / (2 * bigTheta α ε) * v - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) +
        K * Φ * distRemainder φ α n z d := by
  have hlin : secondOrderUtility Ubar K UnN σ φ y n z
      = secondOrderUtility Ubar K (-(1 - α) * K) σ φ y n z +
        Φ * (1 - α) * K * (n + (1 + φ) / 2 * n ^ 2 + n * z) := by
    rw [hUn]
    unfold secondOrderUtility
    ring
  rw [hlin, secondOrderUtility_eq_efficient (ε := ε) (v := v) hα hden rfl hn]
  unfold xhat distRemainder
  linear_combination (K * Φ) * hn

/-- Galí (2015), App. 5.1, p. 155 (**the small-distortion approximation, polynomial layer**).
Along a one-parameter family of size `s` with a small distortion `Φ(s) = O(s)`, log
deviations `y, a, z = O(s)`, `v = O(s²)`, `d − (ε/2Θ) v = O(s³)` (Lemma 1) and the exact
employment identity, the second-order polynomial at `U_n N = −(1 − Φ)(1 − α) U_c C`, divided
by `K = U_c C`, equals `Φ x̂ − ½[(σ + (φ+α)/(1−α)) x̂² + (ε/Θ) v] + t.i.p.` up to `O(s³)`. -/
theorem small_distortion_polynomial {Ubar K σ φ α ε : ℝ} {Φ y n z a d v : ℝ → ℝ} (hK : K ≠ 0)
    (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) (hΦ : Φ =O[𝓝 0] fun s => s ^ 1)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => secondOrderUtility Ubar K (-(1 - Φ s) * (1 - α) * K) σ φ (y s) (n s) (z s) / K
        - (Φ s * xhat σ φ α (y s) (a s) - (gapCoeff σ φ α * xhat σ φ α (y s) (a s) ^ 2 +
            ε / bigTheta α ε * v s) / 2 +
          (tip Ubar K σ φ α (a s) (z s) / K + Φ s * (psiYA σ φ α - 1) * a s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have T6 : (fun s => c * v s - d s) =O[𝓝 0] fun s => s ^ 3 :=
    hd.neg_left.congr_left fun s => by ring
  have T7 : (fun s => (1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3
  have hQ : (fun s => distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0] fun s => s ^ 2 := by
    have e1 : (fun s => n s ^ 2) =O[𝓝 0] fun s => s ^ (1 + 1) :=
      (bigO_mul hn1 hn1).congr_left fun s => by ring
    have e2 : (fun s => n s * z s) =O[𝓝 0] fun s => s ^ (1 + 1) := bigO_mul hn1 hz
    exact (hd2.add (((e1.const_mul_left ((1 + φ) / 2)).add e2).const_mul_left (1 - α)))
  have T8 : (fun s => Φ s * distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0]
      fun s => s ^ (1 + 2) := bigO_mul hΦ hQ
  refine ((T6.sub T7).add T8).congr_left fun s => ?_
  rw [secondOrderUtility_eq_distorted (ε := ε) (v := v s) hα hden rfl (hn s)]
  unfold welfareQuadratic xhat
  field_simp
  ring

/-! ### Appendix 5.1: the analytic bridge -/

/-- Galí (2015), App. 4.1, p. 117 and App. 5.1, p. 154 (**period utility to second order,
any steady state**). Period utility is `U(C, N; Z) = (u(C) + w(N)) Z` (separable, `Z = e^z`),
`u`, `w` of class `C³` near the steady state `(C, N)`, `σ = −U_cc C/U_c`, `φ = U_nn N/U_n`.
Along a one-parameter family with log deviations `y, n, z = O(s)`, period utility minus its
steady-state value equals the second-order polynomial up to `O(s³)`. No efficiency of the
steady state is needed (this is the first display of App. 5.1). Adapted from the Chapter 4
project. -/
theorem period_utility_sub_polynomial {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n z : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (hn1 : n =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - secondOrderUtility (u C + w N) (deriv u C * C) (deriv w N * N) σ φ (y s) (n s) (z s))
      =O[𝓝 0] fun s => s ^ 3 := by
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  have cube : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 3) =O[𝓝 0] fun s => s ^ 3 := fun {f} hf => by
    have := hf.pow 3
    simpa [← pow_mul] using this
  have hRu : (fun s => u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hu).comp_tendsto (tendsto_zero_of_bigO hy)).trans (cube hy)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(C / 2 * y s ^ 2)) * hσ
  have hRw : (fun s => w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hw).comp_tendsto (tendsto_zero_of_bigO hn1)).trans (cube hn1)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(N / 2 * n s ^ 2)) * hφ
  have hRe : (fun s => Real.exp (z s) - 1 - z s - z s ^ 2 / 2) =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hz)).trans (cube hz)
  have hez : (fun s => Real.exp (z s)) =O[𝓝 0] fun s => s ^ 0 := by
    have ht : Tendsto (fun s => Real.exp (z s)) (𝓝 0) (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp (tendsto_zero_of_bigO hz)
      rw [Real.exp_zero] at this
      exact this
    simpa using ht.isBigO_one ℝ
  have hsq : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 2) =O[𝓝 0] fun s => s ^ 2 := fun {f} hf => by
    have := hf.pow 2
    simpa [← pow_mul] using this
  have hpoly : ∀ {f : ℝ → ℝ} (k₁ k₂ : ℝ), f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => k₁ * f s + k₂ * f s ^ 2) =O[𝓝 0] fun s => s ^ 1 := fun {f} k₁ k₂ hf =>
    (hf.const_mul_left k₁).add (bigO_weaken (by norm_num) ((hsq hf).const_mul_left k₂))
  have T1 := hRe.const_mul_left Ubar
  have T2 : (fun s => (K * (1 - σ) / 2 * y s ^ 2 + UnN * (1 + φ) / 2 * n s ^ 2) *
      (z s + z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (2 + 1) :=
    bigO_mul (((hsq hy).const_mul_left _).add ((hsq hn1).const_mul_left _))
      ((hpoly 1 (1 / 2) hz).congr_left fun s => by ring)
  have T3 : (fun s => (K * y s + UnN * n s) * (z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (1 + 2) :=
    bigO_mul ((hy.const_mul_left _).add (hn1.const_mul_left _))
      (((hsq hz).const_mul_left (1 / 2)).congr_left fun s => by ring)
  have T4 : (fun s => (K * (y s + (1 - σ) / 2 * y s ^ 2) + UnN * (n s + (1 + φ) / 2 * n s ^ 2)) *
      (Real.exp (z s) - 1 - z s - z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ 3 :=
    bigO_weaken (by norm_num : 3 ≤ 1 + 3) (bigO_mul
      ((((hpoly 1 ((1 - σ) / 2) hy).const_mul_left K).add
        ((hpoly 1 ((1 + φ) / 2) hn1).const_mul_left UnN)).congr_left fun s => by ring) hRe)
  have T5 : (fun s => ((u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2)) +
      (w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))) *
      Real.exp (z s)) =O[𝓝 0] fun s => s ^ (3 + 0) := bigO_mul (hRu.add hRw) hez
  refine ((((T1.add T2).add T3).add T4).add T5).congr_left fun s => ?_
  unfold secondOrderUtility
  ring

/-- Galí (2015), App. 5.1, pp. 154–155 (**period utility with a small steady-state
distortion, rigorous form**). At a steady state with distortion `Φ`,
`U_n N = −(1 − Φ)(1 − α) U_c C`, along a one-parameter family with `y, a, z = O(s)`,
`v = O(s²)`, `d − (ε/2Θ) v = O(s³)` and `(1 − α) n = y − a + d`, period utility satisfies
`U_t − U = K[Φ x̂ − ½(Γ x̂² + (ε/Θ) v)] + t.i.p. + K Φ Q(s) + O(s³)` with `K = U_c C`,
`t.i.p. = tip + K Φ (ψ_ya − 1) a`, and the neglected term `Q(s) = O(s²)`: exactly the
"product of `Φ` with a second-order term" that the book drops. -/
theorem period_utility_small_distortion {u w : ℝ → ℝ} {C N σ φ α ε Φ : ℝ}
    {y n a z d v : ℝ → ℝ} (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hDist : deriv w N * N = -(1 - Φ) * (1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (deriv u C * C * Φ * xhat σ φ α (y s) (a s) +
          welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s) (v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s) +
          deriv u C * C * Φ * (psiYA σ φ α - 1) * a s)
        - deriv u C * C * Φ * distRemainder φ α (n s) (z s) (d s))
      =O[𝓝 0] (fun s => s ^ 3) ∧
    (fun s => distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0] fun s => s ^ 2 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have hB := period_utility_sub_polynomial hu hw hσ hφ hy hn1 hz
  have T6 : (fun s => K * (c * v s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left K).congr_left fun s => by ring
  have T7 : (fun s => K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3).const_mul_left K)
  refine ⟨((hB.add T6).sub T7).congr_left fun s => ?_, ?_⟩
  · rw [secondOrderUtility_eq_distorted (ε := ε) (v := v s) hα hden hDist (hn s)]
    ring
  · have e1 : (fun s => n s ^ 2) =O[𝓝 0] fun s => s ^ (1 + 1) :=
      (bigO_mul hn1 hn1).congr_left fun s => by ring
    have e2 : (fun s => n s * z s) =O[𝓝 0] fun s => s ^ (1 + 1) := bigO_mul hn1 hz
    exact (hd2.add (((e1.const_mul_left ((1 + φ) / 2)).add e2).const_mul_left (1 - α)))

/-! ### Lemma 2 and the welfare loss `W` (restated from the Chapter 4 project) -/

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2, partial sums; restated from the Chapter 4
project): if `V_{t+1} = θ V_t + c q_t`, then
`∑_{t ≤ N} βᵗ V_{t+1} = θ V_0 + θβ ∑_{t < N} βᵗ V_{t+1} + c ∑_{t ≤ N} βᵗ q_t`. -/
theorem lemma2_partial {θ β c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = θ * V t + c * q t)
    (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * V (t + 1)
      = θ * V 0 + θ * β * ∑ t ∈ Finset.range N, β ^ t * V (t + 1) +
        c * ∑ t ∈ Finset.range (N + 1), β ^ t * q t := by
  have h : ∀ t, β ^ (t + 1) * V (t + 1 + 1) = θ * β * (β ^ t * V (t + 1)) +
      c * (β ^ (t + 1) * q (t + 1)) := fun t => by
    rw [hrec (t + 1)]
    ring
  rw [Finset.sum_range_succ' (fun t => β ^ t * V (t + 1)),
    Finset.sum_range_succ' (fun t => β ^ t * q t), Finset.sum_congr rfl (fun t _ => h t),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrec 0]
  ring

/-- Galí (2015), App. 4.1, p. 119 (restated from the Chapter 4 project): a variance
recursion `V_{t+1} = θ V_t + c q_t` with nonnegative data stays nonnegative. -/
theorem lemma2_nonneg {θ c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hV0 : 0 ≤ V 0)
    (hq : ∀ t, 0 ≤ q t) (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) : ∀ t, 0 ≤ V t := by
  intro t
  induction t with
  | zero => exact hV0
  | succ t ih =>
    rw [hrec t]
    have := mul_nonneg hc (hq t)
    have := mul_nonneg hθ ih
    linarith

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2, general form, exact; restated from the Chapter 4
project): if `V_{t+1} = θ V_t + c q_t` with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`, `q ≥ 0` and
`∑ βᵗ q_t` summable, then `∑ βᵗ V_{t+1} = (θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. -/
theorem lemma2_hasSum {θ β c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hβθ : β * θ < 1)
    (hc : 0 ≤ c) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      ((θ * V 0 + c * ∑' t, β ^ t * q t) / (1 - β * θ)) := by
  have hV := lemma2_nonneg hθ hc hV0 hq hrec
  have hf0 : ∀ t, 0 ≤ β ^ t * V (t + 1) := fun t => mul_nonneg (pow_nonneg hβ t) (hV _)
  have hq0 : ∀ t, 0 ≤ β ^ t * q t := fun t => mul_nonneg (pow_nonneg hβ t) (hq t)
  set Q := ∑' t, β ^ t * q t with hQdef
  have hQle : ∀ N, ∑ t ∈ Finset.range N, β ^ t * q t ≤ Q := fun N =>
    hQ.sum_le_tsum _ (fun i _ => hq0 i)
  have hpos : 0 < 1 - β * θ := by linarith
  have hQ0 : 0 ≤ Q := tsum_nonneg hq0
  have hbound : ∀ N, ∑ t ∈ Finset.range N, β ^ t * V (t + 1) ≤
      (θ * V 0 + c * Q) / (1 - β * θ) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (add_nonneg (mul_nonneg hθ hV0) (mul_nonneg hc hQ0)) hpos.le
    | succ M =>
      rw [le_div_iff₀ hpos]
      have hp := lemma2_partial (β := β) hrec M
      have hmono : ∑ t ∈ Finset.range M, β ^ t * V (t + 1) ≤
          ∑ t ∈ Finset.range (M + 1), β ^ t * V (t + 1) := by
        rw [Finset.sum_range_succ]
        linarith [hf0 M]
      have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hθ hβ)
      have h2 := mul_le_mul_of_nonneg_left (hQle (M + 1)) hc
      nlinarith
  have hsum : Summable fun t => β ^ t * V (t + 1) := summable_of_sum_range_le hf0 hbound
  have hg : Summable fun t => β ^ t * V t := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun t => β ^ (t + 1) * V (t + 1)) = fun t => β * (β ^ t * V (t + 1)) := by
      funext t
      ring
    rw [this]
    exact hsum.mul_left β
  have hg0 := hg.tsum_eq_zero_add
  have hshift : ∑' t, β ^ (t + 1) * V (t + 1) = β * ∑' t, β ^ t * V (t + 1) := by
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have hS : ∑' t, β ^ t * V (t + 1) = θ * ∑' t, β ^ t * V t + c * Q := by
    have : (fun t => β ^ t * V (t + 1)) = fun t => θ * (β ^ t * V t) + c * (β ^ t * q t) := by
      funext t
      rw [hrec t]
      ring
    rw [this, (hg.mul_left θ).tsum_add (hQ.mul_left c), tsum_mul_left, tsum_mul_left]
  rw [hg0, hshift] at hS
  simp only [pow_zero, one_mul] at hS
  have hval : ∑' t, β ^ t * V (t + 1) = (θ * V 0 + c * Q) / (1 - β * θ) := by
    rw [eq_div_iff hpos.ne']
    linarith
  rw [← hval]
  exact hsum.hasSum

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2 as printed, exact; restated from the Chapter 4
project): with no inherited dispersion and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
`∑ βᵗ V_{t+1} = θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`. -/
theorem lemma2 {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : V 0 = 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0.ge hq hrec hQ
  rw [hV0] at h
  convert h using 1
  field_simp
  ring

/-- Galí (2015), App. 4.1, p. 119 and App. 5.1, p. 156: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`
(restated from the Chapter 4 project). -/
theorem inflWeight_of_dispersion {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaNK β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), App. 5.1, p. 156 (**the welfare loss with a small distortion**), for given
paths of the welfare-relevant gap `x̂` and inflation `π`:
`W = −∑ βᵗ [Φ x̂_t − ½((ε/λ) π_t² + (σ + (φ+α)/(1−α)) x̂_t²)]`. -/
noncomputable def welfareW (β θ σ φ α ε Φ : ℝ) (xh infl : ℕ → ℝ) : ℝ :=
  -∑' t, β ^ t * (Φ * xh t -
    (ε / lambdaNK β θ α ε * infl t ^ 2 + gapCoeff σ φ α * xh t ^ 2) / 2)

/-- Galí (2015), App. 5.1, pp. 155–156 (**from the cross-sectional variance to inflation,
exact**). If the cross-sectional variance follows the Calvo recursion
`V_{t+1} = θ V_t + (θ/(1−θ)) π_t²` with no inherited dispersion (Chapter 4, Lemma 2), and
`∑ βᵗ x̂_t`, `∑ βᵗ x̂_t²`, `∑ βᵗ π_t²` converge, then
`−∑ βᵗ [Φ x̂_t − ½(Γ x̂_t² + (ε/Θ) V_{t+1})]` converges to `W` of `welfareW`. -/
theorem welfare_small_distortion {β θ σ φ α ε Φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1) {xh infl V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * infl t ^ 2)
    (hX1 : Summable fun t => β ^ t * xh t) (hX2 : Summable fun t => β ^ t * xh t ^ 2)
    (hD : Summable fun t => β ^ t * infl t ^ 2) :
    HasSum (fun t => -(β ^ t * (Φ * xh t -
        (gapCoeff σ φ α * xh t ^ 2 + ε / bigTheta α ε * V (t + 1)) / 2)))
      (welfareW β θ σ φ α ε Φ xh infl) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => infl t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hB : HasSum (fun t => β ^ t * (Φ * xh t -
      (ε / lambdaNK β θ α ε * infl t ^ 2 + gapCoeff σ φ α * xh t ^ 2) / 2))
      (Φ * ∑' t, β ^ t * xh t - (ε / lambdaNK β θ α ε * ∑' t, β ^ t * infl t ^ 2 +
        gapCoeff σ φ α * ∑' t, β ^ t * xh t ^ 2) / 2) := by
    have := (hX1.hasSum.mul_left Φ).sub (((hD.hasSum.mul_left (ε / lambdaNK β θ α ε)).add
      (hX2.hasSum.mul_left (gapCoeff σ φ α))).div_const 2)
    convert this using 1
    funext t
    ring
  have hA := ((hX1.hasSum.mul_left Φ).sub (((hX2.hasSum.mul_left (gapCoeff σ φ α)).add
    (hL.mul_left (ε / bigTheta α ε))).div_const 2)).neg
  rw [welfareW, hB.tsum_eq, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), App. 5.1, p. 156, last paragraph, and eq. (1), p. 128 (**the efficient case,
exact**): with `Φ = 0` the welfare loss is `(ε/(2λ)) ∑ βᵗ (π_t² + ϑ x_t²)`, i.e. proportional
to the loss function (1) with `ϑ = κ/ε`. -/
theorem welfareW_efficient {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    (x infl : ℕ → ℝ) :
    welfareW β θ σ φ α ε 0 x infl
      = ε / (2 * lambdaNK β θ α ε) * ∑' t, β ^ t * (infl t ^ 2 + vartheta β θ σ φ α ε * x t ^ 2)
    := by
  rw [welfareW, ← tsum_neg, ← tsum_mul_left]
  congr 1
  funext t
  have h := periodLoss_eq_scaled (σ := σ) (φ := φ) hlam hε (x t) (infl t)
  linear_combination (β ^ t) * h

end Gali.DiscretionCommitment.LossAndCostPush

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sources of cost-push shocks

Galí (2015), Chapter 5, Appendix 5.2 (pp. 156–157). Constant returns to labour (`α = 0`) as
in the book, so `λ = (1 − θ)(1 − βθ)/θ` and `κ = λ(σ + φ)`.

## Exogenous variations in desired price markups

* `resetPrice_solves`: the optimal reset price
  `p*_t = (1 − βθ) ∑_{k ≥ 0} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}` (a genuine infinite sum) satisfies
  the recursion `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`.
* `inflation_eq_markupGap`: with the Calvo index `p_t = θ p_{t−1} + (1 − θ) p*_t`, this gives
  `π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)` exactly.
* `nkpc_priceMarkup`: with flexible wages and a subsidy that corrects the steady-state markup,
  `μ_t − μ = −(σ + φ)(y_t − y^e_t)` and `π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with
  `u_t = λ μ̂ⁿ_t`.
* **C5-7** (the printed sums start at `k = 1`): `weights_sum_k0` (the weights
  `(1 − βθ)(βθ)ᵏ`, `k ≥ 0`, sum to one), `weights_sum_k1` (from `k = 1` they sum to `βθ ≠ 1`),
  `printedResetPrice_const` (the printed rule sets `p* = βθ (μⁿ + ψ)` in a steady state instead
  of `μⁿ + ψ`), and `printed_priceSetting_breaks_nkpc`: a perfect-foresight steady state that
  satisfies the printed price-setting rule and the Calvo index but violates the NKPC.

## Exogenous variations in wage markups

* `priceMarkup_eq`: `μ_t = p_t − (w_t − a_t) = −μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t`.
* **C5-6** (sign): `printed_markup_line_iff` (the printed line `μ_t = +μ_{w,t} − …` holds iff
  `μ_{w,t} = 0`), `markupGap_wage`, `nkpc_wageMarkup` (`u_t = +λ(μ_{w,t} − μ_w)`),
  `printed_wage_costPush_contradiction` (the printed `u_t = −λ(μ_{w,t} − μ_w)` contradicts the
  derivation whenever `λ ≠ 0` and the wage markup is away from steady state), and
  `wageMarkup_costPush_pos` (a higher wage markup is inflationary).
-/

namespace Gali.DiscretionCommitment.CostPushSources

open Gali.DiscretionCommitment.LossAndCostPush

/-- Galí (2015), App. 5.2, p. 157 (with `α = 0`; ch. 3, p. 61): the slope of inflation with
respect to the markup gap, `λ = (1 − θ)(1 − βθ)/θ`. -/
noncomputable def lambdaCalvo (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), App. 5.2, p. 156: with constant returns (`α = 0`), `Θ = 1` and the general
`λ` of chapter 3 reduces to `(1 − θ)(1 − βθ)/θ`. -/
theorem lambdaNK_alpha_zero (β θ ε : ℝ) : lambdaNK β θ 0 ε = lambdaCalvo β θ := by
  unfold lambdaNK bigTheta lambdaCalvo
  simp

/-- Galí (2015), App. 5.2, p. 156: `λ > 0` for `0 < θ < 1` and `β < 1`. -/
theorem lambdaCalvo_pos {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < lambdaCalvo β θ := by
  unfold lambdaCalvo
  have h1 : 0 < 1 - β * θ := by nlinarith
  exact div_pos (mul_pos (by linarith) h1) hθ0

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Desired price markups: the price-setting rule and the Calvo index -/

/-- Galí (2015), App. 5.2, p. 156 (corrected, C5-7): the optimal reset price
`p*_t = (1 − βθ) ∑_{k ≥ 0} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}`, `ψ` nominal marginal cost and
`μⁿ` the desired markup. -/
noncomputable def resetPrice (β θ : ℝ) (μn ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (1 - β * θ) • 𝔼.forwardSeries (β * θ) (fun s => μn s + ψ s) t

/-- Galí (2015), App. 5.2, p. 156 (C5-7): the price-setting rule **as printed**, with the sums
starting at `k = 1`: `(1 − βθ) ∑_{k ≥ 1} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}`. -/
noncomputable def printedResetPrice (β θ : ℝ) (μn ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 - β * θ) * ∑' k, (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω

/-- Galí (2015), App. 5.2, p. 156 (and ch. 3, eq. (11), p. 57): for bounded adapted desired
markups and marginal costs and `0 ≤ βθ < 1`, the reset price (a genuine infinite sum) satisfies
the recursion `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`. -/
theorem resetPrice_solves {β θ M : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) {μn ψ : ℕ → Ω → ℝ}
    (hb : ∀ t ω, |μn t ω + ψ t ω| ≤ M) (ha : 𝔼.Adapted fun s => μn s + ψ s) (t : ℕ) :
    resetPrice 𝔼 β θ μn ψ t
      = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (resetPrice 𝔼 β θ μn ψ (t + 1)) := by
  unfold resetPrice
  rw [𝔼.forwardSeries_solves h0 h1 (u := fun s => μn s + ψ s) hb ha t, map_smul, smul_add,
    smul_comm (1 - β * θ) (β * θ)]
  abel

/-- Galí (2015), App. 5.2, pp. 156–157 (**the inflation equation, exact**). Let prices be
adapted, `p_{t+1} = θ p_t + (1 − θ) p*_{t+1}` (the Calvo index, log-linear), and the reset
price satisfy `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`. Then, with the markup
`μ_t = p_t − ψ_t` and `π_t = p_t − p_{t−1}`, at every date `t ≥ 1`
`π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)`. -/
theorem inflation_eq_markupGap {β θ : ℝ} (hθ : θ ≠ 0) {p pstar μn ψ : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) (hcalvo : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hreset : ∀ t, pstar t = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (pstar (t + 1)))
    (t : ℕ) :
    p (t + 1) - p t = β • 𝔼.E (t + 1) (p (t + 2) - p (t + 1)) -
      lambdaCalvo β θ • ((p (t + 1) - ψ (t + 1)) - μn (t + 1)) := by
  have hE : 𝔼.E (t + 1) (p (t + 2)) =
      θ • p (t + 1) + (1 - θ) • 𝔼.E (t + 1) (pstar (t + 2)) := by
    rw [hcalvo (t + 1), map_add, map_smul, map_smul, hp (t + 1)]
  funext ω
  have c1 := congrFun (hcalvo t) ω
  have c2 := congrFun hE ω
  have r := congrFun (hreset (t + 1)) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at c1 c2 r
  rw [show t + 1 + 1 = t + 2 from rfl] at r
  simp only [map_sub, hp (t + 1), Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hl : lambdaCalvo β θ * θ = (1 - θ) * (1 - β * θ) := by
    unfold lambdaCalvo
    field_simp
  apply mul_left_cancel₀ hθ
  linear_combination c1 - θ * β * c2 + (1 - θ) * r +
    (p (t + 1) ω - ψ (t + 1) ω - μn (t + 1) ω) * hl

/-- Galí (2015), App. 5.2, p. 157: with constant returns, flexible wages `w_t − p_t = mrs_t`,
`mrs_t = σ y_t + φ n_t`, `n_t = y_t − a_t`, nominal marginal cost `ψ_t = w_t − a_t`, and
efficient output defined by the subsidy-corrected steady-state markup,
`μ = −(σ + φ) y^e_t + (1 + φ) a_t`, the markup gap is `μ_t − μ = −(σ + φ)(y_t − y^e_t)`. -/
theorem markupGap_price {σ φ μbar p w ψ y n a ye : ℝ} (hmrs : w - p = σ * y + φ * n)
    (hn : n = y - a) (hψ : ψ = w - a) (hye : μbar = -(σ + φ) * ye + (1 + φ) * a) :
    (p - ψ) - μbar = -(σ + φ) * (y - ye) := by
  subst hn hψ hye
  linear_combination -hmrs

/-- Galí (2015), App. 5.2, p. 157 (**desired price markup shocks as cost-push shocks**): under
the hypotheses of `inflation_eq_markupGap` and `markupGap_price` (at every date), inflation
satisfies `π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with `κ = λ(σ + φ)` and
`u_t = λ μ̂ⁿ_t`, `μ̂ⁿ_t = μⁿ_t − μ`. -/
theorem nkpc_priceMarkup {β θ σ φ μbar : ℝ} (hθ : θ ≠ 0) {p pstar μn ψ w y n a ye : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) (hcalvo : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hreset : ∀ t, pstar t = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (pstar (t + 1)))
    (hmrs : ∀ t ω, w t ω - p t ω = σ * y t ω + φ * n t ω) (hn : ∀ t ω, n t ω = y t ω - a t ω)
    (hψ : ∀ t ω, ψ t ω = w t ω - a t ω)
    (hye : ∀ t ω, μbar = -(σ + φ) * ye t ω + (1 + φ) * a t ω) (t : ℕ) :
    p (t + 1) - p t = β • 𝔼.E (t + 1) (p (t + 2) - p (t + 1)) +
      (lambdaCalvo β θ * (σ + φ)) • (y (t + 1) - ye (t + 1)) +
      lambdaCalvo β θ • (μn (t + 1) - fun _ => μbar) := by
  rw [inflation_eq_markupGap 𝔼 hθ hp hcalvo hreset t]
  funext ω
  have hg := markupGap_price (hmrs (t + 1) ω) (hn (t + 1) ω) (hψ (t + 1) ω) (hye (t + 1) ω)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-lambdaCalvo β θ) * hg

/-! ### C5-7: the printed sums from `k = 1` -/

/-- Galí (2015), App. 5.2, p. 156 (corrected, C5-7): the weights `(1 − βθ)(βθ)ᵏ`, `k ≥ 0`,
sum to one. -/
theorem weights_sum_k0 {β θ : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) :
    HasSum (fun k : ℕ => (1 - β * θ) * (β * θ) ^ k) 1 := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - β * θ)
  rwa [mul_inv_cancel₀ (by linarith)] at h

/-- Galí (2015), App. 5.2, p. 156 (**C5-7**): the printed weights `(1 − βθ)(βθ)ᵏ`, `k ≥ 1`,
sum to `βθ`, which is not one for `0 ≤ βθ < 1`. -/
theorem weights_sum_k1 {β θ : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) :
    HasSum (fun k : ℕ => (1 - β * θ) * (β * θ) ^ (k + 1)) (β * θ) ∧ β * θ ≠ 1 := by
  refine ⟨?_, h1.ne⟩
  have h := ((hasSum_geometric_of_lt_one h0 h1).mul_left (1 - β * θ)).mul_left (β * θ)
  rw [mul_inv_cancel₀ (by linarith), mul_one] at h
  convert h using 1
  funext k
  ring

/-- Galí (2015), App. 5.2, p. 156: with constant `μⁿ + ψ = c` the correct rule sets the reset
price at `p* = c` (the frictionless markup over marginal cost). -/
theorem resetPrice_const {β θ c : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) {μn ψ : ℕ → Ω → ℝ}
    (hc : ∀ t, μn t + ψ t = fun _ => c) (t : ℕ) :
    resetPrice 𝔼 β θ μn ψ t = fun _ => c := by
  funext ω
  unfold resetPrice ExpectationSystem.forwardSeries
  beta_reduce
  simp only [Pi.smul_apply, smul_eq_mul]
  have he : ∀ k, (β * θ) ^ k * 𝔼.E t (μn (t + k) + ψ (t + k)) ω = c * (β * θ) ^ k := by
    intro k
    rw [hc (t + k), 𝔼.const]
    ring
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [show (1 : ℝ) - β * θ ≠ 0 by linarith]

/-- Galí (2015), App. 5.2, p. 156 (**C5-7**): with constant `μⁿ + ψ = c` the printed rule
(sums from `k = 1`) sets `p* = βθ c ≠ c` (for `c ≠ 0`): the reset price is not the
frictionless markup over marginal cost even in a steady state. -/
theorem printedResetPrice_const {β θ c : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1)
    {μn ψ : ℕ → Ω → ℝ} (hc : ∀ t, μn t + ψ t = fun _ => c) (t : ℕ) :
    printedResetPrice 𝔼 β θ μn ψ t = fun _ => β * θ * c := by
  funext ω
  unfold printedResetPrice
  have he : ∀ k : ℕ, (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω
      = c * (β * θ) * (β * θ) ^ k := by
    intro k
    rw [hc, 𝔼.const]
    ring
  rw [show (fun k : ℕ => (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω) =
      fun k => c * (β * θ) * (β * θ) ^ k from funext he, tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1]
  field_simp [show (1 : ℝ) - β * θ ≠ 0 by linarith]

/-- Galí (2015), App. 5.2, pp. 156–157 (**C5-7: the printed rule does not yield the NKPC**).
For every `0 < β < 1`, `0 < θ < 1` there is a perfect-foresight path (a steady state with
price level `1`, marginal cost `1/(βθ)` and `μⁿ = 0`) that satisfies the printed price-setting
rule (sums from `k = 1`) and the Calvo index, but violates
`π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)`. -/
theorem printed_priceSetting_breaks_nkpc {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ p pstar μn ψ : ℕ → Unit → ℝ,
      (∀ t, pstar t = printedResetPrice perfectForesight β θ μn ψ t) ∧
      (∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1)) ∧
      ¬ ∀ t, p (t + 1) - p t = β • perfectForesight.E (t + 1) (p (t + 2) - p (t + 1)) -
        lambdaCalvo β θ • ((p (t + 1) - ψ (t + 1)) - μn (t + 1)) := by
  have hbt0 : 0 < β * θ := mul_pos hβ0 hθ0
  have hbt1 : β * θ < 1 := by nlinarith
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 0, fun _ _ => 1 / (β * θ), fun t => ?_,
    fun t => ?_, fun h => ?_⟩
  · rw [printedResetPrice_const perfectForesight hbt0.le hbt1 (c := 1 / (β * θ))
      (fun t => by funext ω; simp)]
    funext ω
    field_simp
  · funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have h0 := congrFun (h 0) ()
    simp only [perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sub_self, Pi.zero_apply, mul_zero, zero_sub, sub_zero] at h0
    have hl := lambdaCalvo_pos hθ0 hθ1 hβ1
    have hne : 1 - 1 / (β * θ) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hbt0.ne']
      exact fun h => hbt1.ne h.symm
    have : lambdaCalvo β θ * (1 - 1 / (β * θ)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hl.ne' h1
    · exact hne h1

/-! ### Wage markups (C5-6) -/

/-- Galí (2015), App. 5.2, p. 157, first two lines (correct as printed): with `α = 0` the price
markup is `μ_t = p_t − (w_t − a_t)`; with the wage markup `μ_{w,t} = (w_t − p_t) − mrs_t`,
`mrs_t = σ y_t + φ n_t` and `n_t = y_t − a_t`,
`μ_t = −μ_{w,t} − mrs_t + a_t = −μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t`. -/
theorem priceMarkup_eq {σ φ μ μw p w a mrs y n : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a) :
    μ = -μw - mrs + a ∧ μ = -μw - (σ + φ) * y + (1 + φ) * a := by
  subst hμ hμw hmrs hn
  constructor <;> ring

/-- Galí (2015), App. 5.2, p. 157, third line (**C5-6**): given the definitions, the printed
line `μ_t = μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t` holds iff `μ_{w,t} = 0`. It is false whenever
the wage markup is nonzero; the correct sign is `−μ_{w,t}`. -/
theorem printed_markup_line_iff {σ φ μ μw p w a mrs y n : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a) :
    μ = μw - (σ + φ) * y + (1 + φ) * a ↔ μw = 0 := by
  have h := (priceMarkup_eq hμ hμw hmrs hn).2
  constructor
  · intro h'
    linarith
  · intro h'
    rw [h, h']
    ring

/-- Galí (2015), App. 5.2, p. 157 (**C5-6, corrected markup gap**): with the subsidy-corrected
steady state `μ = −μ_w − (σ + φ) y^e_t + (1 + φ) a_t` (corrected sign), the markup gap is
`μ_t − μ = −(σ + φ)(y_t − y^e_t) − (μ_{w,t} − μ_w)`. -/
theorem markupGap_wage {σ φ μ μbar μw μwbar p w a mrs y n ye : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a)
    (hss : μbar = -μwbar - (σ + φ) * ye + (1 + φ) * a) :
    μ - μbar = -(σ + φ) * (y - ye) - (μw - μwbar) := by
  rw [(priceMarkup_eq hμ hμw hmrs hn).2, hss]
  ring

/-- Galí (2015), App. 5.2, p. 157 (**C5-6, wage-markup shocks as cost-push shocks,
corrected**): if `π_t = β E_t π_{t+1} − λ(μ_t − μ)` (chapter 3) with the price markup of
`priceMarkup_eq` and the steady state of `markupGap_wage` at every date, then
`π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with `κ = λ(σ + φ)` and
`u_t = +λ(μ_{w,t} − μ_w)`. -/
theorem nkpc_wageMarkup {β lam σ φ μbar μwbar : ℝ}
    {infl μ μw p w a mrs y n ye : ℕ → Ω → ℝ}
    (hpc : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - lam • (μ t - fun _ => μbar))
    (hμ : ∀ t ω, μ t ω = p t ω - (w t ω - a t ω))
    (hμw : ∀ t ω, μw t ω = (w t ω - p t ω) - mrs t ω)
    (hmrs : ∀ t ω, mrs t ω = σ * y t ω + φ * n t ω) (hn : ∀ t ω, n t ω = y t ω - a t ω)
    (hss : ∀ t ω, μbar = -μwbar - (σ + φ) * ye t ω + (1 + φ) * a t ω) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) +
      lam • (μw t - fun _ => μwbar) := by
  rw [hpc t]
  funext ω
  have hg := markupGap_wage (hμ t ω) (hμw t ω) (hmrs t ω) (hn t ω) (hss t ω)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-lam) * hg

/-- Galí (2015), App. 5.2, p. 157 (**C5-6: the printed sign contradicts the derivation**): if
inflation satisfied both the derived equation (`u_t = +λ(μ_{w,t} − μ_w)`) and the printed one
(`u_t = −λ(μ_{w,t} − μ_w)`) at some date and state, then `λ(μ_{w,t} − μ_w) = 0`. So for
`λ ≠ 0` the printed cost-push term is wrong whenever the wage markup is away from its steady
state. -/
theorem printed_wage_costPush_contradiction {β lam σ φ μwbar : ℝ}
    {infl μw y ye : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω)
    (hder : infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) +
      lam • (μw t - fun _ => μwbar))
    (hprint : infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) -
      lam • (μw t - fun _ => μwbar)) (hlam : lam ≠ 0) :
    μw t ω = μwbar := by
  have h1 := congrFun hder ω
  have h2 := congrFun hprint ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have : lam * (μw t ω - μwbar) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hlam
  · linarith

/-- Galí (2015), App. 5.2, p. 157 (C5-6): with the corrected sign a wage-markup increase is a
genuine cost-push shock: `u_t = λ(μ_{w,t} − μ_w) > 0` when `μ_{w,t} > μ_w` and `λ > 0`, whereas
the printed sign would make it disinflationary. -/
theorem wageMarkup_costPush_pos {lam μw μwbar : ℝ} (hlam : 0 < lam) (h : μwbar < μw) :
    0 < lam * (μw - μwbar) ∧ -(lam * (μw - μwbar)) < 0 := by
  have := mul_pos hlam (sub_pos.mpr h)
  exact ⟨this, by linarith⟩

end Gali.DiscretionCommitment.CostPushSources

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal discretionary policy

Galí (2015), Chapter 5, §5.2.1 (pp. 129–133). The central bank minimises
`E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to (2) `π_t = β E_t π_{t+1} + κ x_t + u_t`, with the
cost-push shock `u` an AR(1) (3) with `ρ_u ∈ [0, 1)`, but cannot commit.

## The period problem and the targeting rule (4)

* `period_problem_iff`: `(π, x)` minimises `π² + ϑ x²` on the line `π = κ x + υ` iff
  `x = −(κ/ϑ) π` (necessary and sufficient, `ϑ > 0`); `period_solution` gives the unique
  minimiser.
* `discretionEq_iff`: a discretionary equilibrium (the NKPC and, date by date and state by
  state, the period problem solved taking `υ_t = β E_t π_{t+1} + u_t` as given) is exactly the
  NKPC together with the targeting rule (4).

## The equilibrium (5)–(6)

* `inflation_forward`: under (4), `π_t = a E_t π_{t+1} + (ϑ/(ϑ+κ²)) u_t`,
  `a = ϑβ/(ϑ+κ²) ∈ [0, 1)`.
* `discretion_iff_forwardSeries`: for any bounded adapted `u`, the bounded adapted
  discretionary equilibrium exists and is unique: `π_t = ∑ aᵏ E_t[(ϑ/(ϑ+κ²)) u_{t+k}]`.
* `discretionEq_iff_msv`, `discretion_msv_isEq`: with AR(1) `u`, the unique bounded adapted
  equilibrium is (5) `π = ϑ/(κ² + ϑ(1 − βρ_u)) u`, (6) `x = −κ/(κ² + ϑ(1 − βρ_u)) u`.

## Dampening (p. 131)

* `zeroGap_iff`: holding `x ≡ 0`, the unique bounded inflation is `u/(1 − βρ_u)`.
* `psiPi_lt`, `dampening`: the discretionary inflation response is positive and strictly
  smaller in absolute value at every horizon `E_t π_{t+k}` where the shock matters.
* `expected_priceLevel_hasSum`, `priceLevel_response_strictMonoOn`: the cumulated (expected)
  inflation, i.e. the permanent change in the price level, is `Ψ_π u_t/(1 − ρ_u)` and is
  strictly increasing in the persistence `ρ_u`.

## Implementation (7)–(10)

* `dis_welfareGap_iff`: the DIS in the natural gap with `r^n` is equivalent to (7), the DIS in
  the welfare-relevant gap with the efficient rate `r^e`; `efficientRate_eq`:
  `σ E_t Δy^e_{t+1} = −σ(1 − ρ_a) ψ_ya a_t`.
* `interestRate_iff`, `psiI_pos`: (8) `i_t = r^e_t + Ψ_i u_t`, `Ψ_i > 0`.
* `rule8_iff_solves`, `AO_eigenvalues`, `AO_not_schurStable`, `rule8_indeterminate`: the
  "rule" (8) gives (9) with exactly one eigenvalue of `A_O` outside the unit circle, hence a
  bounded equilibrium other than the discretionary one.
* `rule10_eq`, `rule10_iff_solves`, `AT_schurStable_iff`, `rule10_implements`,
  `rule10_indeterminate`: (10) `i_t = r^e_t + Ψ'_i u_t + φ_π π_t` implements the
  discretionary equilibrium as the unique bounded equilibrium iff `φ_π > 1` (for `φ_π ≥ 0`).
-/

namespace Gali.DiscretionCommitment.Discretion

open Filter Topology Gali.DiscretionCommitment.LossAndCostPush

/-! ### The period problem (p. 129) -/

/-- Galí (2015), p. 129: the period objective as a function of the output gap `x`, after
substituting the constraint `π = κ x + υ`: `(κ x + υ)² + ϑ x²`. -/
def periodObj (κ ϑ υ x : ℝ) : ℝ := (κ * x + υ) ^ 2 + ϑ * x ^ 2

/-- Galí (2015), p. 130 (completing the square): the change of the period objective is
`(κ² + ϑ)(x' − x)² + 2 (x' − x)((κ² + ϑ) x + κ υ)`. -/
theorem periodObj_sub (κ ϑ υ x x' : ℝ) :
    periodObj κ ϑ υ x' - periodObj κ ϑ υ x
      = (κ ^ 2 + ϑ) * (x' - x) ^ 2 + 2 * (x' - x) * ((κ ^ 2 + ϑ) * x + κ * υ) := by
  unfold periodObj
  ring

/-- Galí (2015), eq. (4), p. 130 (**necessary and sufficient**): for `ϑ > 0`, `x` minimises
the period objective iff the targeting rule `x = −(κ/ϑ)(κ x + υ)` holds. -/
theorem periodObj_isMinOn_iff {κ ϑ υ x : ℝ} (hϑ : 0 < ϑ) :
    IsMinOn (periodObj κ ϑ υ) Set.univ x ↔ x = -(κ / ϑ) * (κ * x + υ) := by
  have hA : 0 < κ ^ 2 + ϑ := by positivity
  have hfoc : x = -(κ / ϑ) * (κ * x + υ) ↔ (κ ^ 2 + ϑ) * x + κ * υ = 0 := by
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [hfoc]
  constructor
  · intro h
    set g := (κ ^ 2 + ϑ) * x + κ * υ
    have hle := h (Set.mem_univ (x - g / (κ ^ 2 + ϑ)))
    simp only [Set.mem_ofPred_eq] at hle
    have hd := periodObj_sub κ ϑ υ x (x - g / (κ ^ 2 + ϑ))
    have hval : (κ ^ 2 + ϑ) * (x - g / (κ ^ 2 + ϑ) - x) ^ 2 +
        2 * (x - g / (κ ^ 2 + ϑ) - x) * g = -(g ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + ϑ) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h x' _
    have hd := periodObj_sub κ ϑ υ x x'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + ϑ) * (x' - x) ^ 2 := by positivity
    simp only [Set.mem_ofPred_eq]
    linarith

/-- Galí (2015), p. 129 and eq. (4), p. 130 (**the period problem, necessary and
sufficient**): for `ϑ > 0`, `(π, x)` minimises `π² + ϑ x²` subject to `π = κ x + υ` iff it is
feasible and satisfies the targeting rule `x = −(κ/ϑ) π`. -/
theorem period_problem_iff {κ ϑ υ π x : ℝ} (hϑ : 0 < ϑ) :
    (π = κ * x + υ ∧ ∀ π' x', π' = κ * x' + υ → π ^ 2 + ϑ * x ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2) ↔
      (π = κ * x + υ ∧ x = -(κ / ϑ) * π) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ ϑ υ) Set.univ x := fun x' _ => by
      have := hmin _ x' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hϑ).mp this
  · rintro ⟨hc, hx⟩
    refine ⟨hc, fun π' x' hc' => ?_⟩
    rw [hc] at hx
    have := (periodObj_isMinOn_iff hϑ).mpr hx (Set.mem_univ x')
    simp only [Set.mem_ofPred_eq, periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), pp. 129–130: the unique solution of the period problem,
`x = −κ υ/(κ² + ϑ)`, `π = ϑ υ/(κ² + ϑ)`. -/
theorem period_solution {κ ϑ υ π x : ℝ} (hϑ : 0 < ϑ) :
    (π = κ * x + υ ∧ x = -(κ / ϑ) * π) ↔
      (x = -κ * υ / (κ ^ 2 + ϑ) ∧ π = ϑ * υ / (κ ^ 2 + ϑ)) := by
  have hA : κ ^ 2 + ϑ ≠ 0 := by positivity
  constructor
  · rintro ⟨hc, hx⟩
    have hx' : (κ ^ 2 + ϑ) * x = -κ * υ := by
      field_simp at hx
      rw [hc] at hx
      linarith
    have hxv : x = -κ * υ / (κ ^ 2 + ϑ) := by
      field_simp
      linarith
    refine ⟨hxv, ?_⟩
    rw [hc, hxv]
    field_simp
    ring
  · rintro ⟨hx, hp⟩
    constructor
    · rw [hx, hp]
      field_simp
      ring
    · rw [hx, hp]
      field_simp

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The discretionary equilibrium -/

/-- Galí (2015), eq. (4), p. 130: the targeting rule `x_t = −(κ/ϑ) π_t` at every date. -/
def TargetingRule (κ ϑ : ℝ) (x infl : ℕ → Ω → ℝ) : Prop := ∀ t, x t = (-(κ / ϑ)) • infl t

/-- Galí (2015), §5.2.1, pp. 129–130: a **discretionary equilibrium**. The NKPC (2) holds and,
at each date and in each state, `(π_t, x_t)` solves the period problem: it minimises
`π² + ϑ x²` over the line `π = κ x + υ_t`, taking `υ_t = β E_t π_{t+1} + u_t` as given. -/
def DiscretionEq (β κ ϑ : ℝ) (u x infl : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ x u infl ∧ ∀ t ω, ∀ π' x' : ℝ,
    π' = κ * x' + (β * 𝔼.E t (infl (t + 1)) ω + u t ω) →
      infl t ω ^ 2 + ϑ * x t ω ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2

/-- Galí (2015), p. 130: for `ϑ > 0` a discretionary equilibrium is exactly a pair satisfying
the NKPC (2) and the targeting rule (4). -/
theorem discretionEq_iff {β κ ϑ : ℝ} (hϑ : 0 < ϑ) {u x infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔ NKPC 𝔼 β κ x u infl ∧ TargetingRule κ ϑ x infl := by
  have hpt : ∀ (h : NKPC 𝔼 β κ x u infl) t ω,
      infl t ω = κ * x t ω + (β * 𝔼.E t (infl (t + 1)) ω + u t ω) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  constructor
  · rintro ⟨h, hmin⟩
    refine ⟨h, fun t => funext fun ω => ?_⟩
    have := ((period_problem_iff hϑ).mp ⟨hpt h t ω, hmin t ω⟩).2
    simpa using this
  · rintro ⟨h, hr⟩
    refine ⟨h, fun t ω => ((period_problem_iff hϑ).mpr ⟨hpt h t ω, ?_⟩).2⟩
    have := congrFun (hr t) ω
    simpa using this

/-- Galí (2015), p. 130: the discount factor of the discretionary inflation equation,
`a = ϑβ/(ϑ + κ²)`. -/
noncomputable def aDisc (β κ ϑ : ℝ) : ℝ := ϑ * β / (ϑ + κ ^ 2)

/-- Galí (2015), p. 130: `0 ≤ a < 1` for `ϑ > 0`, `0 ≤ β < 1`. -/
theorem aDisc_mem {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ aDisc β κ ϑ ∧ aDisc β κ ϑ < 1 := by
  unfold aDisc
  have hA : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), p. 130, unnumbered display: under the targeting rule (4) the NKPC becomes
`π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (ϑ/(ϑ + κ²)) u_t`. Conversely, this equation together
with (4) gives back the NKPC. -/
theorem inflation_forward_iff {β κ ϑ : ℝ} (hϑ : 0 < ϑ) {u x infl : ℕ → Ω → ℝ}
    (hr : TargetingRule κ ϑ x infl) :
    NKPC 𝔼 β κ x u infl ↔
      ∀ t, infl t = aDisc β κ ϑ • 𝔼.E t (infl (t + 1)) + (ϑ / (ϑ + κ ^ 2)) • u t := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hϑ' : ϑ ≠ 0 := hϑ.ne'
  constructor
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r] at p
    unfold aDisc
    field_simp
    field_simp at p
    linarith
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r]
    unfold aDisc at p
    field_simp at p
    field_simp
    linarith

/-- Galí (2015), p. 130: the forward series of a bounded process is adapted (`E_t` leaves
`∑ aᵏ E_t u_{t+k}` unchanged). A general lemma not in the core. -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ a ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg ha0 k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω =
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, 𝔼.E_E_self]
  rfl

/-- Galí (2015), eqs. (4)–(5), p. 130 (**existence and uniqueness, general shocks**): for
`ϑ > 0`, `0 ≤ β < 1` and bounded adapted `u`, bounded adapted `(x, π)` form a discretionary
equilibrium iff `π_t = ∑_{k ≥ 0} aᵏ E_t[(ϑ/(ϑ + κ²)) u_{t+k}]` (`a = ϑβ/(ϑ + κ²)`) and
`x = −(κ/ϑ) π` (only boundedness of `π` is needed for uniqueness). -/
theorem discretion_iff_forwardSeries {β κ ϑ M : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u x infl : ℕ → Ω → ℝ} (hub : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔
      infl = 𝔼.forwardSeries (aDisc β κ ϑ) (fun t => (ϑ / (ϑ + κ ^ 2)) • u t) ∧
        x = fun t => (-(κ / ϑ)) • infl t := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  set c := ϑ / (ϑ + κ ^ 2)
  have hcb : ∀ t ω, |(c • u t) ω| ≤ |c| * M := fun t ω => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hub t ω) (abs_nonneg c)
  have hca : 𝔼.Adapted fun t => c • u t := fun t => by rw [map_smul, hua t]
  rw [discretionEq_iff 𝔼 hϑ]
  constructor
  · rintro ⟨h, hr⟩
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp h
    exact ⟨𝔼.eq_forwardSeries ha0 ha1 hcb hca hf hpb, funext hr⟩
  · rintro ⟨hp, hx⟩
    have hr : TargetingRule κ ϑ x infl := fun t => by rw [hx]
    refine ⟨(inflation_forward_iff 𝔼 hϑ hr).mpr fun t => ?_, hr⟩
    rw [hp]
    exact 𝔼.forwardSeries_solves ha0 ha1 hcb hca t

/-- Galí (2015), eq. (5), p. 130 (**existence, general shocks**): for bounded adapted `u` the
forward-series pair is a bounded adapted discretionary equilibrium. -/
theorem discretion_forwardSeries_isEq {β κ ϑ M : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℕ → Ω → ℝ} (hub : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    let infl := 𝔼.forwardSeries (aDisc β κ ϑ) (fun t => (ϑ / (ϑ + κ ^ 2)) • u t)
    DiscretionEq 𝔼 β κ ϑ u (fun t => (-(κ / ϑ)) • infl t) infl ∧
      BoundedProc infl ∧ 𝔼.Adapted infl ∧
      BoundedProc (fun t => (-(κ / ϑ)) • infl t) ∧ 𝔼.Adapted (fun t => (-(κ / ϑ)) • infl t) := by
  intro infl
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  set c := ϑ / (ϑ + κ ^ 2)
  have hcb : ∀ t ω, |(c • u t) ω| ≤ |c| * M := fun t ω => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hub t ω) (abs_nonneg c)
  have hpb : BoundedProc infl := 𝔼.forwardSeries_bounded ha0 ha1 hcb
  have hpa : 𝔼.Adapted infl := forwardSeries_adapted 𝔼 ha0 ha1 hcb
  obtain ⟨B, hB⟩ := hpb
  have hxb : BoundedProc (fun t => (-(κ / ϑ)) • infl t) := ⟨|κ / ϑ| * B, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)⟩
  refine ⟨(discretion_iff_forwardSeries 𝔼 hϑ hβ0 hβ1 hub hua ⟨B, hB⟩).mpr ⟨rfl, rfl⟩,
    ⟨B, hB⟩, hpa, hxb, fun t => by rw [map_smul, hpa t]⟩

/-! ### The MSV solution with AR(1) cost-push shocks: (5) and (6) -/

/-- Galí (2015), eq. (5), p. 130: `Ψ_π = ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiPi (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (6), p. 130: `Ψ_x = −κ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), p. 130: the common denominator `κ² + ϑ(1 − βρ_u)` is positive. -/
theorem den_pos {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1) :
    0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
  have : β * ρ < 1 := by nlinarith
  have : 0 < ϑ * (1 - β * ρ) := mul_pos hϑ (by linarith)
  positivity

/-- Galí (2015), eqs. (4)–(6), p. 130: `Ψ_x = −(κ/ϑ) Ψ_π`. -/
theorem psiX_eq {β κ ϑ ρ : ℝ} (hϑ : ϑ ≠ 0) : psiX β κ ϑ ρ = -(κ / ϑ) * psiPi β κ ϑ ρ := by
  unfold psiX psiPi
  field_simp

/-- Galí (2015), eq. (5), p. 130: `Ψ_π = (ϑ/(ϑ+κ²))/(1 − aρ_u)` with `a = ϑβ/(ϑ+κ²)`: the
forward solution of the inflation equation for an AR(1) shock. -/
theorem psiPi_eq_forward {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) :
    psiPi β κ ϑ ρ = (1 - aDisc β κ ϑ * ρ)⁻¹ * (ϑ / (ϑ + κ ^ 2)) := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have h1 : 1 - aDisc β κ ϑ * ρ ≠ 0 := by
    unfold aDisc
    rw [div_mul_eq_mul_div, one_sub_div hA]
    exact div_ne_zero (by nlinarith) hA
  unfold psiPi
  rw [eq_inv_mul_iff_mul_eq₀ h1]
  unfold aDisc
  field_simp
  ring

/-- Galí (2015), eqs. (5)–(6), p. 130 (**existence**): with AR(1) cost-push shocks, the MSV
pair `π = Ψ_π u`, `x = Ψ_x u` is a discretionary equilibrium. -/
theorem discretion_msv_isEq {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEq 𝔼 β κ ϑ u (fun t => psiX β κ ϑ ρ • u t) (fun t => psiPi β κ ϑ ρ • u t) := by
  have hr : TargetingRule κ ϑ (fun t => psiX β κ ϑ ρ • u t) (fun t => psiPi β κ ϑ ρ • u t) :=
    fun t => by rw [psiX_eq hϑ.ne', smul_smul]
  rw [discretionEq_iff 𝔼 hϑ, inflation_forward_iff 𝔼 hϑ hr]
  refine ⟨fun t => ?_, hr⟩
  rw [map_smul, hu.2 t, smul_smul]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [psiPi_eq_forward hϑ hβ0 hβ1 hρ1]
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have h1 : 1 - aDisc β κ ϑ * ρ ≠ 0 := by
    have := psiPi_eq_forward (κ := κ) hϑ hβ0 hβ1 hρ1
    intro h0
    rw [h0, inv_zero, zero_mul] at this
    have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
    unfold psiPi at this
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hϑ.ne' h
    · exact hD.ne' h
  field_simp
  ring

/-- Galí (2015), eqs. (5)–(6), p. 130 (**existence and uniqueness among bounded processes**):
with a bounded AR(1) cost-push shock (`0 ≤ ρ_u < 1`), bounded adapted `(x, π)` form a
discretionary equilibrium iff `π = ϑ/(κ² + ϑ(1 − βρ_u)) u` and
`x = −κ/(κ² + ϑ(1 − βρ_u)) u`. -/
theorem discretionEq_iff_msv {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u x infl : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (hxb : BoundedProc x) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔
      infl = (fun t => psiPi β κ ϑ ρ • u t) ∧ x = (fun t => psiX β κ ϑ ρ • u t) := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  have ha : |aDisc β κ ϑ| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  obtain ⟨M, hM⟩ := hub
  have hmsvb : BoundedProc (fun t => psiPi β κ ϑ ρ • u t) := ⟨|psiPi β κ ϑ ρ| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hmsv := discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0 hβ1 hρ1 hu
  constructor
  · intro h
    obtain ⟨hn, hr⟩ := (discretionEq_iff 𝔼 hϑ).mp h
    obtain ⟨hn', hr'⟩ := (discretionEq_iff 𝔼 hϑ).mp hmsv
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp hn
    have hf' := (inflation_forward_iff 𝔼 hϑ hr').mp hn'
    have hp : infl = fun t => psiPi β κ ϑ ρ • u t := 𝔼.forward_unique ha hf hf' hpb hmsvb
    refine ⟨hp, funext fun t => ?_⟩
    simp only [hr t, hp, psiX_eq hϑ.ne', smul_smul]
  · rintro ⟨rfl, rfl⟩
    exact hmsv

/-! ### Dampening relative to `x ≡ 0` (p. 131) -/

/-- Galí (2015), p. 131: if the output gap were held at zero, the NKPC
`π_t = β E_t π_{t+1} + u_t` would have the unique bounded adapted solution
`π_t = u_t/(1 − βρ_u)`. -/
theorem zeroGap_iff {β κ ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1)
    {u infl : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hpb : BoundedProc infl) :
    NKPC 𝔼 β κ 0 u infl ↔ infl = fun t => (1 - β * ρ)⁻¹ • u t := by
  have hβρ : β * ρ < 1 := by nlinarith
  have hne : 1 - β * ρ ≠ 0 := by linarith
  have ha : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hiff : NKPC 𝔼 β κ 0 u infl ↔ ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + u t := by
    unfold NKPC
    simp only [Pi.zero_apply, smul_zero, add_zero]
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc (fun t => (1 - β * ρ)⁻¹ • u t) := ⟨|(1 - β * ρ)⁻¹| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hsol : ∀ t, (1 - β * ρ)⁻¹ • u t =
      β • 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + 1)) + u t := 𝔼.forward_ar1_solves hne hu
  rw [hiff]
  constructor
  · intro h
    exact 𝔼.forward_unique ha h hsol hpb hcb
  · rintro rfl
    exact hsol

/-- Galí (2015), p. 131 (**dampening**): for `κ ≠ 0`, `ϑ > 0`,
`0 < ϑ/(κ² + ϑ(1 − βρ_u)) < 1/(1 − βρ_u)`. -/
theorem psiPi_lt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) :
    0 < psiPi β κ ϑ ρ ∧ psiPi β κ ϑ ρ < (1 - β * ρ)⁻¹ := by
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have hβρ : 0 < 1 - β * ρ := by nlinarith
  have hk : 0 < κ ^ 2 := by positivity
  refine ⟨div_pos hϑ hD, ?_⟩
  unfold psiPi
  rw [div_lt_iff₀ hD, inv_mul_eq_div, lt_div_iff₀ hβρ]
  nlinarith

/-- Galí (2015), p. 131 (**dampening at all horizons**): let `π^d = Ψ_π u` be discretionary
inflation and `π⁰ = u/(1 − βρ_u)` inflation with the gap held at zero. Then for every date
`t`, horizon `k` and state, `E_t π^d_{t+k} = Ψ_π ρ_uᵏ u_t` and `E_t π⁰_{t+k} = ρ_uᵏ u_t/(1 − βρ_u)`
have the same sign, `|E_t π^d_{t+k}| ≤ |E_t π⁰_{t+k}|`, and the inequality is strict whenever
`ρ_uᵏ u_t ≠ 0`. -/
theorem dampening {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t k : ℕ) (ω : Ω) :
    𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω = psiPi β κ ϑ ρ * (ρ ^ k * u t ω) ∧
      𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω = (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) ∧
      0 ≤ 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω * 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω ∧
      |𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω| ≤ |𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω| ∧
      (ρ ^ k * u t ω ≠ 0 →
        |𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω| < |𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω|) := by
  obtain ⟨h0, h1⟩ := psiPi_lt hκ hϑ hβ0 hβ1 hρ1
  have e1 : 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω = psiPi β κ ϑ ρ * (ρ ^ k * u t ω) := by
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp
  have e2 : 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω = (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) := by
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp
  have hpos : 0 < (1 - β * ρ)⁻¹ := h0.trans h1
  refine ⟨e1, e2, ?_, ?_, fun hne => ?_⟩
  · rw [e1, e2]
    have : 0 ≤ psiPi β κ ϑ ρ * (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) ^ 2 := by positivity
    nlinarith
  · rw [e1, e2, abs_mul (psiPi β κ ϑ ρ), abs_mul (1 - β * ρ)⁻¹, abs_of_pos h0,
      abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
  · rw [e1, e2, abs_mul (psiPi β κ ϑ ρ), abs_mul (1 - β * ρ)⁻¹, abs_of_pos h0,
      abs_of_pos hpos]
    exact mul_lt_mul_of_pos_right h1 (abs_pos.mpr hne)

/-- Galí (2015), pp. 131–132 (**a permanent change in the price level**): under discretion the
expected cumulated inflation from date `t` on, `∑_{k ≥ 0} E_t π_{t+k}`, converges to
`Ψ_π u_t/(1 − ρ_u)`: the (expected) price level shifts permanently. -/
theorem expected_priceLevel_hasSum {β κ ϑ ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω)
      (psiPi β κ ϑ ρ / (1 - ρ) * u t ω) := by
  have h := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (psiPi β κ ϑ ρ * u t ω))
  convert h using 1
  · funext k
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · field_simp

/-- Galí (2015), p. 132 (**the size of the price-level shift increases with persistence**):
for `κ ≠ 0`, `ϑ > 0`, `0 ≤ β < 1`, the long-run price-level response to a unit cost-push shock,
`Ψ_π(ρ_u)/(1 − ρ_u) = ϑ/((κ² + ϑ(1 − βρ_u))(1 − ρ_u))`, is strictly increasing in
`ρ_u ∈ [0, 1)`. -/
theorem priceLevel_response_strictMonoOn {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    StrictMonoOn (fun ρ => psiPi β κ ϑ ρ / (1 - ρ)) (Set.Ico 0 1) := by
  intro ρ₁ h₁ ρ₂ h₂ hlt
  obtain ⟨h₁0, h₁1⟩ := h₁
  obtain ⟨h₂0, h₂1⟩ := h₂
  have hD₁ := den_pos (κ := κ) hϑ hβ0 hβ1 h₁1
  have hD₂ := den_pos (κ := κ) hϑ hβ0 hβ1 h₂1
  have hg₂ : 0 < (κ ^ 2 + ϑ * (1 - β * ρ₂)) * (1 - ρ₂) := mul_pos hD₂ (by linarith)
  simp only [psiPi, div_div]
  apply div_lt_div_of_pos_left hϑ hg₂
  have hk : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hb : 0 ≤ ϑ * β := mul_nonneg hϑ.le hβ0
  nlinarith [mul_pos (sub_pos.mpr hlt) hϑ, mul_nonneg hb (sub_pos.mpr hlt).le]

/-! ### The DIS in the welfare-relevant gap (7) -/

/-- Galí (2015), eq. (7), p. 132: the dynamic IS equation in a gap `x` with real rate `r`,
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r_t)`. -/
def DIS (σ : ℝ) (x i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - r t)

/-- Galí (2015), p. 132: the real rate consistent with an output path `y^v` (natural or
efficient), `r_t = ζ_t + σ E_t{Δy^v_{t+1}}`, where `ζ_t = ρ + (1 − ρ_z) z_t` collects the
discount-rate and preference terms common to `r^n` and `r^e`. -/
def rateOf (σ : ℝ) (ζ yv : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ζ t + σ • (𝔼.E t (yv (t + 1)) - yv t)

/-- Galí (2015), eq. (7), p. 132 (**exact**): for `σ ≠ 0`, the DIS in the natural-output gap
`y − y^n` with the natural rate `r^n` holds iff the DIS (7) in the welfare-relevant gap
`x = y − y^e` with the efficient rate `r^e` holds. -/
theorem dis_welfareGap_iff {σ : ℝ} (hσ : σ ≠ 0) {y yn ye i infl ζ : ℕ → Ω → ℝ} :
    DIS 𝔼 σ (fun t => y t - yn t) i infl (rateOf 𝔼 σ ζ yn) ↔
      DIS 𝔼 σ (fun t => y t - ye t) i infl (rateOf 𝔼 σ ζ ye) := by
  have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (ye (t + 1)) ω - ye t ω - 𝔼.E t (yn (t + 1)) ω + yn t ω) *
      hinv
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (yn (t + 1)) ω - yn t ω - 𝔼.E t (ye (t + 1)) ω + ye t ω) *
      hinv

/-- Galí (2015), p. 132: with efficient output `y^e_t = ψ_ya a_t` (in deviations) and AR(1)
technology `a`, `σ E_t{Δy^e_{t+1}} = −σ(1 − ρ_a) ψ_ya a_t`, so
`r^e_t = ζ_t − σ(1 − ρ_a) ψ_ya a_t`. -/
theorem efficientRate_eq {σ ψ ρa : ℝ} {ζ a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    rateOf 𝔼 σ ζ (fun s => ψ • a s) t = ζ t - (σ * (1 - ρa) * ψ) • a t := by
  unfold rateOf
  rw [map_smul, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The equilibrium interest rate (8) -/

/-- Galí (2015), eq. (8), p. 133: `Ψ_i = (ϑρ_u + σκ(1 − ρ_u))/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiI (β σ κ ϑ ρ : ℝ) : ℝ :=
  (ϑ * ρ + σ * κ * (1 - ρ)) / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (8), p. 133: `Ψ_i = ρ_u Ψ_π + σ(ρ_u − 1) Ψ_x`. -/
theorem psiI_eq (β σ κ ϑ ρ : ℝ) :
    psiI β σ κ ϑ ρ = psiPi β κ ϑ ρ * ρ + σ * psiX β κ ϑ ρ * (ρ - 1) := by
  unfold psiI psiPi psiX
  ring

/-- Galí (2015), eq. (8), p. 133 (**the interest-rate path under discretion, exact**): along
the discretionary equilibrium (5)–(6) with AR(1) `u`, the DIS (7) holds iff
`i_t = r^e_t + Ψ_i u_t`. -/
theorem interestRate_iff {β σ κ ϑ ρ : ℝ} (hσ : σ ≠ 0) {u i re : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) :
    DIS 𝔼 σ (fun t => psiX β κ ϑ ρ • u t) i (fun t => psiPi β κ ϑ ρ • u t) re ↔
      ∀ t, i t = re t + psiI β σ κ ϑ ρ • u t := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hinv' : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [map_smul, hu.2 t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [psiI_eq]
    linear_combination σ * e - (i t ω - psiPi β κ ϑ ρ * (ρ * u t ω) - re t ω) * hinv
  · intro h t
    funext ω
    have hi := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [psiI_eq] at hi
    simp only [map_smul, hu.2 t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination σ⁻¹ * hi - psiX β κ ϑ ρ * (1 - ρ) * u t ω * hinv'

/-- Galí (2015), eq. (8), p. 133: `Ψ_i > 0` for `σ, κ, ϑ > 0`, `0 ≤ β < 1`, `0 ≤ ρ_u < 1`. -/
theorem psiI_pos {β σ κ ϑ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : 0 < psiI β σ κ ϑ ρ := by
  unfold psiI
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have h1 : 0 < σ * κ * (1 - ρ) := mul_pos (mul_pos hσ hκ) (by linarith)
  have h2 : 0 ≤ ϑ * ρ := mul_nonneg hϑ.le hρ0
  exact div_pos (by linarith) hD

/-! ### The "rule" (8) and indeterminacy (9) -/

/-- Galí (2015), eq. (9), p. 133: the stacked vector `(x_t, π_t)` (restated from the
Chapter 4 project). -/
def stack (x infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the Chapter 4
project; Galí 2015, p. 133). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the Chapter 4
project; Galí 2015, p. 133). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), eq. (9), p. 133: `A_O = [[1, σ⁻¹], [κ, β + κσ⁻¹]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, σ⁻¹; κ, β + κ * σ⁻¹]

/-- Galí (2015), eq. (9), p. 133: the forcing `B_O u_t` for a rule `i_t = r^e_t + ψ u_t`,
`B_O = (−σ⁻¹ψ, 1 − κσ⁻¹ψ)`. -/
noncomputable def wO (σ κ ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ * σ⁻¹)) • u t, (1 - κ * ψ * σ⁻¹) • u t]

/-- Galí (2015), eq. (9), p. 133 (**exact**): under a rule `i_t = r^e_t + ψ u_t` (in
particular (8), `ψ = Ψ_i`), the NKPC (2) and the DIS (7) hold iff `(x, π)` solves
`(x_t, π_t) = A_O E_t (x_{t+1}, π_{t+1}) + B_O u_t`. -/
theorem rule8_iff_solves {β σ κ ψ : ℝ} {u x infl i re : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = re t + ψ • u t) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re) ↔
      𝔼.Solves (AO β σ κ) (wO σ κ ψ u) (stack x infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO, wO]
      linear_combination e
    · simp [stack, AO, wO]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO, wO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO, wO] at e0
      simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- Galí (2015), eq. (9), p. 133: `tr A_O = 1 + β + κσ⁻¹`. -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ * σ⁻¹ := by
  simp only [tr2, AO, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), eq. (9), p. 133: `det A_O = β`. -/
theorem det2_AO (β σ κ : ℝ) : det2 (AO β σ κ) = β := by
  simp only [det2, AO, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), p. 133: for `σ, κ > 0` and `β ≥ 0`, `A_O` fails the Schur–Cohn condition. -/
theorem AO_not_schurStable {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rw [tr2_AO, det2_AO]
  rintro ⟨-, h⟩
  have hk : 0 < κ * σ⁻¹ := mul_pos hκ (inv_pos.mpr hσ)
  have := le_abs_self (1 + β + κ * σ⁻¹)
  linarith

/-- Galí (2015), p. 133 (**"A_O has always one eigenvalue outside the unit circle"**): for
`σ, κ > 0` and `0 < β < 1`, the characteristic polynomial of `A_O` factors as
`(z − r₁)(z − r₂)` with real roots `0 < r₁ < 1 < r₂`: exactly one eigenvalue lies outside the
unit circle. -/
theorem AO_eigenvalues {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < 1 ∧ 1 < r₂ ∧
      ∀ z, z ^ 2 - tr2 (AO β σ κ) * z + det2 (AO β σ κ) = (z - r₁) * (z - r₂) := by
  rw [tr2_AO, det2_AO]
  set T := 1 + β + κ * σ⁻¹ with hT
  have hk : 0 < κ * σ⁻¹ := mul_pos hκ (inv_pos.mpr hσ)
  have hT1 : 1 + β < T := by linarith
  have hsq : (1 + β) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith) hT1.le 2
  have hdisc : 0 ≤ T ^ 2 - 4 * β := by nlinarith [sq_nonneg (1 - β)]
  set s := Real.sqrt (T ^ 2 - 4 * β) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = T ^ 2 - 4 * β := Real.sq_sqrt hdisc
  refine ⟨(T - s) / 2, (T + s) / 2, ?_, ?_, ?_, fun z => ?_⟩
  · have : s < T := by nlinarith
    linarith
  · have : T - 2 < s := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · have : 2 - T < s := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · linear_combination (1 / 4 : ℝ) * hs2

/-- Galí (2015), eq. (9), p. 133 (**the "rule" (8) does not determine the equilibrium**): with
bounded AR(1) cost-push shocks, `σ, κ, ϑ > 0` and `0 < β < 1`, if the nominal rate follows
`i_t = r^e_t + Ψ_i u_t` there is a bounded adapted equilibrium of (2) and (7) other than the
discretionary one (5)–(6). -/
theorem rule8_indeterminate [Nonempty Ω] {β σ κ ϑ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1) {u re : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    ∃ x infl : ℕ → Ω → ℝ, NKPC 𝔼 β κ x u infl ∧
      DIS 𝔼 σ x (fun t => re t + psiI β σ κ ϑ ρ • u t) infl re ∧
      𝔼.Adapted x ∧ 𝔼.Adapted infl ∧ BoundedProc x ∧ BoundedProc infl ∧
      (x ≠ (fun t => psiX β κ ϑ ρ • u t) ∨ infl ≠ (fun t => psiPi β κ ϑ ρ • u t)) := by
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  have hrule : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hn := ((discretionEq_iff 𝔼 hϑ).mp (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0 hβ1 hρ1 hu)).1
  have hd : DIS 𝔼 σ (fun t => psiX β κ ϑ ρ • u t) (fun t => re t + psiI β σ κ ϑ ρ • u t)
      (fun t => psiPi β κ ϑ ρ • u t) re := (interestRate_iff 𝔼 hσ.ne' hu).mpr hrule
  have hs := (rule8_iff_solves 𝔼 hrule).mp ⟨hn, hd⟩
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique (AO_not_schurStable hσ hκ) hs
    (adaptedVec_stack 𝔼 (had _) (had _)) (boundedVec_stack (hbd _) (hbd _))
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  obtain ⟨hn', hd'⟩ := (rule8_iff_solves 𝔼 (β := β) (x := fun t => y t 0)
    (infl := fun t => y t 1) hrule).mpr (hst ▸ hy)
  refine ⟨fun t => y t 0, fun t => y t 1, hn', hd', fun t => hay t 0, fun t => hay t 1,
    ⟨B, fun t ω => hB t 0 ω⟩, ⟨B, fun t ω => hB t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### An implementing rule (10) -/

/-- Galí (2015), eq. (10), p. 133: `Ψ'_i = (σκ(1 − ρ_u) − ϑ(φ_π − ρ_u))/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiIprime (β σ κ ϑ ρ φπ : ℝ) : ℝ :=
  (σ * κ * (1 - ρ) - ϑ * (φπ - ρ)) / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (10), p. 133 (the two forms of the rule agree, exact):
`r^e_t + Ψ_i u_t + φ_π(π_t − Ψ_π u_t) = r^e_t + Ψ'_i u_t + φ_π π_t`. -/
theorem rule10_eq (β σ κ ϑ ρ φπ : ℝ) (re u infl : ℕ → Ω → ℝ) (t : ℕ) :
    re t + psiI β σ κ ϑ ρ • u t + φπ • (infl t - psiPi β κ ϑ ρ • u t) =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t := by
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  unfold psiI psiIprime psiPi
  ring

/-- Galí (2015), p. 133 (the system under rule (10); ch. 4, eq. (13) with `φ_y = 0`):
`A_T = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def AT (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), p. 133: the forcing of the system under a rule
`i_t = r^e_t + ψ u_t + φ_π π_t`: `(σ + κφ_π)⁻¹ (−(ψ + φ_π), σ − κψ) u_t`. -/
noncomputable def wT (σ κ φπ ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ + φπ) / (σ + κ * φπ)) • u t, ((σ - κ * ψ) / (σ + κ * φπ)) • u t]

/-- Galí (2015), p. 133 (**exact**): under a rule `i_t = r^e_t + ψ u_t + φ_π π_t` (in
particular (10), `ψ = Ψ'_i`), the NKPC (2) and the DIS (7) hold iff `(x, π)` solves
`(x_t, π_t) = A_T E_t (x_{t+1}, π_{t+1}) + w_t`. Adapted from the Chapter 4 project. -/
theorem rule10_iff_solves {β σ κ φπ ψ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {u x infl i re : ℕ → Ω → ℝ} (hrule : ∀ t, i t = re t + ψ • u t + φπ • infl t) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re) ↔
      𝔼.Solves (AT β σ κ φπ) (wT σ κ φπ ψ u) (stack x infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    have s : σ * x t ω + φπ * infl t ω
        = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * u t ω := by
      linear_combination σ * e -
        (ψ * u t ω + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω) * hinv
    fin_cases j
    · simp [stack, AT, wT]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AT, wT]
      field_simp
      linear_combination κ * s + σ * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have s : σ * x t ω + φπ * infl t ω
          = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * u t ω := by
        apply mul_left_cancel₀ hS
        linear_combination σ * e0 + φπ * e1
      linear_combination σ⁻¹ * s - (x t ω - 𝔼.E t (x (t + 1)) ω) * hinv

/-- Galí (2015), p. 133: `tr A_T = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 133: `det A_T = σβ/(σ + κφ_π)`. -/
theorem det2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 133 (**the Taylor principle for rule (10)**; ch. 4, eq. (14) with
`φ_y = 0`): for `σ, κ > 0`, `0 < β < 1`, `φ_π ≥ 0`, both eigenvalues of `A_T` lie inside the
unit circle iff `φ_π > 1`. -/
theorem AT_schurStable_iff {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    SchurStable (tr2 (AT β σ κ φπ)) (det2 (AT β σ κ φπ)) ↔ 1 < φπ := by
  have hS : 0 < σ + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ) / (σ + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ) / (σ + κ * φπ) < 1 + σ * β / (σ + κ * φπ)
      ↔ σ * (1 + β) + κ < σ + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    exact ⟨hD1, by nlinarith⟩

/-- Galí (2015), eq. (10), p. 133 (**rule (10) implements the discretionary equilibrium
uniquely**): for `σ, κ, ϑ > 0`, `0 < β < 1`, `ρ_u < 1`, bounded AR(1) `u` and any `φ_π > 1`,
bounded adapted `(x, π)` and a nominal rate `i` satisfy the NKPC (2), the DIS (7) and the rule
`i_t = r^e_t + Ψ'_i u_t + φ_π π_t` iff `(x, π)` is the discretionary equilibrium (5)–(6) and
`i_t = r^e_t + Ψ_i u_t` (8). -/
theorem rule10_implements {β σ κ ϑ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφ : 1 < φπ) {u re x infl i : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hxa : 𝔼.Adapted x) (hpa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hpb : BoundedProc infl) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re ∧
        ∀ t, i t = re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t) ↔
      (x = (fun t => psiX β κ ϑ ρ • u t) ∧ infl = (fun t => psiPi β κ ϑ ρ • u t) ∧
        ∀ t, i t = re t + psiI β σ κ ϑ ρ • u t) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  -- the discretionary triple satisfies (2), (7) and (10)
  have hn := ((discretionEq_iff 𝔼 hϑ).mp
    (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0.le hβ1 hρ1 hu)).1
  have hrule8 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hd := (interestRate_iff 𝔼 (β := β) (κ := κ) (ϑ := ϑ) hσ.ne' hu).mpr hrule8
  have hrule10 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => psiPi β κ ϑ ρ • u t) t := by
    intro t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold psiI psiIprime psiPi
    ring
  constructor
  · rintro ⟨hp, hdis, hr⟩
    have hs := (rule10_iff_solves 𝔼 hσ.ne' hS hr).mp ⟨hp, hdis⟩
    have hs' := (rule10_iff_solves 𝔼 hσ.ne' hS hrule10).mp ⟨hn, hd⟩
    have heq := 𝔼.system_unique ((AT_schurStable_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ)
      hs hs' (adaptedVec_stack 𝔼 hxa hpa) (adaptedVec_stack 𝔼 (had _) (had _))
      (boundedVec_stack hxb hpb) (boundedVec_stack (hbd _) (hbd _))
    have h1 : x = fun t => psiX β κ ϑ ρ • u t := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = fun t => psiPi β κ ϑ ρ • u t := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, fun t => ?_⟩
    rw [hr t, h2]
    exact (hrule10 t).symm
  · rintro ⟨rfl, rfl, hi⟩
    have hieq : i = fun t => re t + psiI β σ κ ϑ ρ • u t := funext hi
    subst hieq
    exact ⟨hn, hd, hrule10⟩

/-- Galí (2015), p. 133 (**the Taylor principle is needed**): for `0 ≤ φ_π ≤ 1` the rule (10)
does not determine the equilibrium: there is a bounded adapted equilibrium of (2), (7) and (10)
other than the discretionary one. -/
theorem rule10_indeterminate [Nonempty Ω] {β σ κ ϑ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    {u re : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    ∃ x infl : ℕ → Ω → ℝ, NKPC 𝔼 β κ x u infl ∧
      DIS 𝔼 σ x (fun t => re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t) infl re ∧
      𝔼.Adapted x ∧ 𝔼.Adapted infl ∧ BoundedProc x ∧ BoundedProc infl ∧
      (x ≠ (fun t => psiX β κ ϑ ρ • u t) ∨ infl ≠ (fun t => psiPi β κ ϑ ρ • u t)) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  have hn := ((discretionEq_iff 𝔼 hϑ).mp
    (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0.le hβ1 hρ1 hu)).1
  have hrule8 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hd := (interestRate_iff 𝔼 (β := β) (κ := κ) (ϑ := ϑ) hσ.ne' hu).mpr hrule8
  have hrule10 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => psiPi β κ ϑ ρ • u t) t := by
    intro t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold psiI psiIprime psiPi
    ring
  have hs := (rule10_iff_solves 𝔼 hσ.ne' hS hrule10).mp ⟨hn, hd⟩
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ)) (det2 (AT β σ κ φπ)) := by
    rw [AT_schurStable_iff hσ hκ hβ0 hβ1 hφ0]
    linarith
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique hns hs
    (adaptedVec_stack 𝔼 (had _) (had _)) (boundedVec_stack (hbd _) (hbd _))
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  have hr' : ∀ t, (fun t => re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • y t 1) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => y t 1) t := fun _ => rfl
  obtain ⟨hn', hd'⟩ := (rule10_iff_solves 𝔼 (β := β) (x := fun t => y t 0) hσ.ne' hS hr').mpr
    (hst ▸ hy)
  refine ⟨fun t => y t 0, fun t => y t 1, hn', hd', fun t => hay t 0, fun t => hay t 1,
    ⟨B, fun t ω => hB t 0 ω⟩, ⟨B, fun t ω => hB t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

end Gali.DiscretionCommitment.Discretion

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy under commitment

Galí (2015), Section 5.2.2, pp. 133–138. The central bank chooses `{π_t, x_t}` to minimise
`E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_t`
for all `t ≥ 0`.

## Main results

* The coefficients: `four_beta_gam_sq_lt_one` (`4βγ² < 1`), `del_quad` (`γβδ² − δ + γ = 0`),
  `del_lt_one_iff`, `del_mem_Ioo_iff` (`δ ∈ (0, 1)` iff `κ > 0`, C5-9), `del_kappa_zero`
  (`δ = 1` at `κ = 0`), `one_sub_gam_beta_del` (`1 − γβδ = γ/δ`), `kappa_sq_del`
  (`κ²δ/ϑ = (1 − δ)(1 − βδ)`), `quad_roots` (the roots are `δ` and `1/(βδ) > 1`).
* (11)–(13): `foc_iff_targeting`, `targeting_iff_eleven_twelve`; (14): `nkpc_iff_priceEq`.
* (15): the factorisation `priceEq_iff_w`; `pHat_priceEq` and `priceEq_unique` (the unique bounded
  solution with `p̂_{−1} = 0`); AR(1) closed forms `pHat_ar1` (15), `gapC_ar1` (16), `gapC_zero`.
* **Deterministic optimal-policy theorem** (`Det`): for a bounded known shock path, the
  commitment path is feasible with finite loss (`candD_feasible`, `candD_finiteLoss`), is optimal
  among all feasible finite-loss paths (`candD_isOptimal`, via the Lagrangian identity
  `loss_sub_hasSum` with the transversality term), and is the unique optimum
  (`isOptimal_iff`, `existsUnique_optimal`); the first-order conditions / the targeting rule are
  necessary and sufficient (`isOptimal_iff_foc`).
* **Stochastic optimal-policy theorem**: `commitment_optimal` — among all bounded adapted plans,
  the commitment plan minimises the expected loss state by state; any plan with the same expected
  loss agrees with it in conditional mean square. The Lagrangian argument uses the tower property,
  `E_tsum` and the pull-out property `PullOut` (true for perfect foresight and finite trees,
  `perfectForesight_pullOut`, `finiteTree_pullOut`, but not one of the `ExpectationSystem` fields).
* `targeting_unique`: the targeting rule and the Phillips curve pin down the commitment plan.
* p. 137: `iterated_nkpc`. p. 138 (`ρ_u = 0`): `dis_iff_rate_rho0` (`i_t = r^e_t −
  (1 − δ)(1 − σκ/ϑ) p̂_t`, C5-1), `pHat_rho0_sum`, and `rule_implements` (the price-level rule
  with `φ_p > 0` implements the allocation uniquely; algebra restated from the Chapter 4 project).
-/

namespace Gali.DiscretionCommitment.Commitment

open Filter Topology

/-! ### The coefficients `γ` and `δ` -/

/-- Galí (2015), (14), p. 135: `γ ≡ ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), (15), p. 136: `δ ≡ (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - √(1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), (14), p. 135: `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), (14), p. 135: `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Galí (2015), (14), p. 135: `γ (1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), (14)–(15), pp. 135–136: `γ (1 + β) < 1` iff `κ ≠ 0`. -/
theorem gam_mul_lt_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (1 + β) < 1 ↔ κ ≠ 0 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_lt_one hD]
  constructor
  · intro h hκ
    rw [hκ] at h
    linarith
  · intro hκ
    have := pow_pos (abs_pos.2 hκ) 2
    rw [sq_abs] at this
    linarith

/-- Galí (2015), (15), p. 136: `4βγ² < 1`, so `δ` is real (for every `κ`). -/
theorem four_beta_gam_sq_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    4 * β * gam β κ ϑ ^ 2 < 1 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have h1 : (gam β κ ϑ * (1 + β)) ^ 2 ≤ 1 := by
    have : 0 ≤ gam β κ ϑ * (1 + β) := by positivity
    nlinarith
  have h2 : 0 < gam β κ ϑ ^ 2 * (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- Galí (2015), (15), p. 136: the square root `s = √(1 − 4βγ²)` satisfies `s² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Galí (2015), (15), p. 136: `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), (15), p. 136: `δ · 2γβ = 1 − √(1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - √(1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Galí (2015), (15), p. 136: `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), (15), p. 136 and footnote 4: `δ` is a root of `γβδ² − δ + γ = 0`, the
undetermined-coefficients condition for `p̂_t = δ p̂_{t−1} + b u_t` to solve (14). -/
theorem del_quad {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    gam β κ ϑ * β * del β κ ϑ ^ 2 - del β κ ϑ + gam β κ ϑ = 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hδ := del_mul (κ := κ) hβ0 hϑ
  have hs2 := sqrt_sq_eq (κ := κ) hβ0 hβ1 hϑ
  set g := gam β κ ϑ
  set s := √(1 - 4 * β * g ^ 2)
  set d := del β κ ϑ
  have h4 : (4 * g * β) * (g * β * d ^ 2 - d + g) = 0 := by
    linear_combination (2 * g * β * d + (1 - s) - 2) * hδ + hs2
  rcases mul_eq_zero.1 h4 with h | h
  · exfalso; have : 0 < 4 * g * β := by positivity
    linarith
  · exact h

/-- Galí (2015), (15), p. 136 (C5-9): `δ < 1` if and only if `κ ≠ 0`. -/
theorem del_lt_one_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ < 1 ↔ κ ≠ 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have hiff := gam_mul_lt_iff (κ := κ) hβ0 hϑ
  set g := gam β κ ϑ
  have h0 : 0 ≤ 1 - 2 * g * β := by nlinarith
  have hgb : 0 < g * β := by positivity
  rw [del, div_lt_one (by positivity), ← hiff]
  constructor
  · intro h
    have h1 : 1 - 2 * g * β < √(1 - 4 * β * g ^ 2) := by linarith
    have h2 := (Real.lt_sqrt h0).1 h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hgb.le (sub_nonneg.2 hc)]
  · intro h
    have h2 : (1 - 2 * g * β) ^ 2 < 1 - 4 * β * g ^ 2 := by nlinarith
    have := (Real.lt_sqrt h0).2 h2
    linarith

/-- Galí (2015), (15), p. 136 (C5-9): for `κ ≥ 0`, `δ ∈ (0, 1)` if and only if `κ > 0`. -/
theorem del_mem_Ioo_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : 0 ≤ κ) :
    (0 < del β κ ϑ ∧ del β κ ϑ < 1) ↔ 0 < κ := by
  rw [del_lt_one_iff hβ0 hβ1 hϑ]
  exact ⟨fun h => lt_of_le_of_ne hκ (Ne.symm h.2), fun h => ⟨del_pos hβ0 hϑ, h.ne'⟩⟩

/-- Galí (2015), (15), p. 136 (C5-9, the boundary case): with `κ = 0`, `δ = 1`. -/
theorem del_kappa_zero {β ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β 0 ϑ = 1 := by
  have hg := gam_pos (κ := 0) hβ0 hϑ
  have hg1 : gam β 0 ϑ * (1 + β) = 1 := by
    unfold gam
    have : 0 < ϑ * (1 + β) := by positivity
    field_simp
    ring
  set g := gam β 0 ϑ
  have hs : √(1 - 4 * β * g ^ 2) = g * (1 - β) := by
    have hnn : 0 ≤ g * (1 - β) := mul_nonneg hg.le (by linarith)
    rw [← Real.sqrt_sq hnn]
    congr 1
    linear_combination (-(1 : ℝ)) * (g * (1 + β) + 1) * hg1
  rw [del, hs, div_eq_one_iff_eq (by positivity)]
  linear_combination -hg1

/-- Galí (2015), (15), p. 136: `1 − γβδ = γ/δ` (used to get `b = δ/(1 − δβρ_u)`). -/
theorem one_sub_gam_beta_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    1 - gam β κ ϑ * β * del β κ ϑ = gam β κ ϑ / del β κ ϑ := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  rw [eq_div_iff hd.ne']
  linear_combination -hq

/-- Galí (2015), (15), p. 136: `δ/γ = 1 + βδ²`. -/
theorem del_div_gam {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ / gam β κ ϑ = 1 + β * del β κ ϑ ^ 2 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  rw [div_eq_iff hg.ne']
  linear_combination -hq

/-- Galí (2015), p. 143 (key identity, used for (15) and (24)): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Galí (2015), (15), p. 136 (factorisation): `γβz² − z + γ = γβ (z − δ)(z − 1/(βδ))`, so the
roots of the characteristic equation of (14) are `δ` and `1/(βδ)`. -/
theorem quad_factor {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (z : ℝ) :
    gam β κ ϑ * β * z ^ 2 - z + gam β κ ϑ =
      gam β κ ϑ * β * (z - del β κ ϑ) * (z - 1 / (β * del β κ ϑ)) := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have h1 := one_sub_gam_beta_del (κ := κ) hβ0 hβ1 hϑ
  have h2 : gam β κ ϑ * β * (z - del β κ ϑ) * (z - 1 / (β * del β κ ϑ)) =
      gam β κ ϑ * β * z ^ 2 - z * (gam β κ ϑ * β * del β κ ϑ + gam β κ ϑ / del β κ ϑ) +
        gam β κ ϑ := by
    field_simp
    ring
  rw [h2, ← h1]
  ring

/-- Galí (2015), (15), p. 136: for `κ ≠ 0`, `δ` is the unique root of `γβz² − z + γ = 0`
inside the unit interval; the other root `1/(βδ)` exceeds one. -/
theorem quad_roots {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    (∀ z, gam β κ ϑ * β * z ^ 2 - z + gam β κ ϑ = 0 ↔ z = del β κ ϑ ∨ z = 1 / (β * del β κ ϑ))
      ∧ 1 < 1 / (β * del β κ ϑ) := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  have hg := gam_pos (κ := κ) hβ0 hϑ
  refine ⟨fun z => ?_, ?_⟩
  · rw [quad_factor hβ0 hβ1 hϑ z]
    have : gam β κ ϑ * β ≠ 0 := by positivity
    simp only [mul_eq_zero, this, false_or, sub_eq_zero]
  · rw [lt_div_iff₀ (by positivity), one_mul]
    nlinarith

/-! ### Lags, the price-level gap and the targeting rule -/

/-- Galí (2015), p. 135: the lag operator with zero initial condition, `(lag p)_0 = 0` and
`(lag p)_{t+1} = p_t`; it encodes `ξ_{−1} = 0` and `p̂_{−1} = 0`. -/
def lag {α : Type*} [Zero α] (p : ℕ → α) : ℕ → α
  | 0 => 0
  | t + 1 => p t

/-- Galí (2015), p. 135: `(lag p)_0 = 0`. -/
@[simp] theorem lag_zero {α : Type*} [Zero α] (p : ℕ → α) : lag p 0 = 0 := rfl

/-- Galí (2015), p. 135: `(lag p)_{t+1} = p_t`. -/
@[simp] theorem lag_succ {α : Type*} [Zero α] (p : ℕ → α) (t : ℕ) : lag p (t + 1) = p t := rfl

/-- Galí (2015), p. 135: the lag commutes with scalar multiplication. -/
theorem lag_smul {α : Type*} [AddCommGroup α] [Module ℝ α] (c : ℝ) (p : ℕ → α) (t : ℕ) :
    lag (fun s => c • p s) t = c • lag p t := by
  cases t <;> simp

/-- Galí (2015), p. 135: the lag commutes with negation. -/
theorem lag_neg {α : Type*} [AddCommGroup α] (p : ℕ → α) (t : ℕ) :
    lag (fun s => -p s) t = -lag p t := by
  cases t <;> simp

/-- Galí (2015), p. 135: the price-level gap `p̂_t = p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceGap {α : Type*} [AddCommMonoid α] (π : ℕ → α) (t : ℕ) : α :=
  ∑ s ∈ Finset.range (t + 1), π s

/-- Galí (2015), p. 135: `p̂_t − p̂_{t−1} = π_t` (with `p̂_{−1} = 0`). -/
theorem priceGap_sub_lag {α : Type*} [AddCommGroup α] (π : ℕ → α) (t : ℕ) :
    priceGap π t - lag (priceGap π) t = π t := by
  cases t with
  | zero => simp [priceGap]
  | succ t => simp [priceGap, Finset.sum_range_succ _ (t + 1)]

/-- Galí (2015), p. 135: conversely, any `p` is the price-level gap of `p_t − p_{t−1}`. -/
theorem priceGap_of_sub_lag {α : Type*} [AddCommGroup α] (p : ℕ → α) :
    priceGap (fun t => p t - lag p t) = p := by
  funext t
  induction t with
  | zero => simp [priceGap]
  | succ t ih =>
    rw [priceGap, Finset.sum_range_succ, ← priceGap, ih]
    simp

/-! ### The commitment first-order conditions and the targeting rule (11)–(13) -/

/-- Galí (2015), p. 134–135: the first-order conditions of the commitment problem,
`ϑ x_t − κ ξ_t = 0` and `π_t + ξ_t − ξ_{t−1} = 0` for all `t ≥ 0`, with `ξ_{−1} = 0`
(statewise; the book's "differentiating with respect to `y_t`" should read `x_t`, C5-4). -/
def FOC (κ ϑ : ℝ) (π x ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * x t = κ * ξ t ∧ π t + ξ t - lag ξ t = 0

/-- Galí (2015), (13), p. 135: the first-order conditions hold for some multipliers iff the
targeting rule in levels `x_t = −(κ/ϑ) p̂_t` holds; then `ξ_t = −p̂_t`. -/
theorem foc_iff_targeting {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (π x : ℕ → ℝ) :
    (∃ ξ, FOC κ ϑ π x ξ) ↔ ∀ t, x t = -(κ / ϑ) * priceGap π t := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have hξp : ∀ t, ξ t = -priceGap π t := by
      intro t
      induction t with
      | zero =>
        have := (hξ 0).2
        simp only [lag_zero] at this
        simp only [priceGap, zero_add, Finset.range_one, Finset.sum_singleton]
        linarith
      | succ t ih =>
        have := (hξ (t + 1)).2
        simp only [lag_succ] at this
        rw [priceGap, Finset.sum_range_succ, ← priceGap]
        linarith
    intro t
    have := (hξ t).1
    rw [hξp t] at this
    field_simp
    linarith
  · intro h
    refine ⟨fun t => -priceGap π t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp
    · have := priceGap_sub_lag π t
      rw [lag_neg]
      linarith

/-- Galí (2015), (11)–(13), p. 135: the targeting rule in levels (13) is equivalent to
`x_0 = −(κ/ϑ) π_0` (11) together with `x_t − x_{t−1} = −(κ/ϑ) π_t` for `t ≥ 1` (12). -/
theorem targeting_iff_eleven_twelve (κ ϑ : ℝ) (π x : ℕ → ℝ) :
    (∀ t, x t = -(κ / ϑ) * priceGap π t) ↔
      (x 0 = -(κ / ϑ) * π 0 ∧ ∀ t, x (t + 1) - x t = -(κ / ϑ) * π (t + 1)) := by
  constructor
  · intro h
    refine ⟨by rw [h 0]; simp [priceGap], fun t => ?_⟩
    rw [h (t + 1), h t, priceGap, Finset.sum_range_succ, ← priceGap]
    ring
  · rintro ⟨h0, h1⟩ t
    induction t with
    | zero => rw [h0]; simp [priceGap]
    | succ t ih =>
      rw [priceGap, Finset.sum_range_succ, ← priceGap]
      linear_combination h1 t + ih

/-! ### The model under uncertainty -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (2), p. 128: the New Keynesian Phillips curve with a cost-push shock,
`π_t = β E_t π_{t+1} + κ x_t + u_t` (`x` is the welfare-relevant output gap). -/
def NKPC (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + u t

/-- Galí (2015), (14), p. 135: `p̂_t = γ p̂_{t−1} + γβ E_t p̂_{t+1} + γ u_t`, `p̂_{−1} = 0`. -/
def PriceEq (β κ ϑ : ℝ) (u p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = gam β κ ϑ • lag p t + (gam β κ ϑ * β) • 𝔼.E t (p (t + 1)) + gam β κ ϑ • u t

/-- Galí (2015), p. 135: inflation implied by a price-level gap, `π_t = p̂_t − p̂_{t−1}`. -/
def inflOf (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - lag p t

/-- Galí (2015), (13), p. 135: the output gap implied by the targeting rule,
`x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapOf (κ ϑ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(κ / ϑ)) • p t

/-- Galí (2015), p. 135: the lag of an adapted process is adapted (`p̂_{t−1}` is known at `t`). -/
theorem lag_adapted {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) : 𝔼.Adapted (lag p) := by
  intro t
  cases t with
  | zero => exact map_zero _
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    have := 𝔼.known (Nat.le_succ t) (p t)
    rwa [hp t] at this

/-- Galí (2015), p. 135 (pointwise algebra): with `x_t = −(κ/ϑ) p̂_t`, the Phillips curve
`p̂_t − p̂_{t−1} = β (E_t p̂_{t+1} − p̂_t) + κ x_t + u_t` is equivalent to (14). -/
theorem pc_iff_fourteen {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (P L Ep U : ℝ) :
    P - L = β * (Ep - P) + κ * (-(κ / ϑ) * P) + U ↔
      P = gam β κ ϑ * L + gam β κ ϑ * β * Ep + gam β κ ϑ * U := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam]
  constructor <;> intro h
  · field_simp at h ⊢
    linarith
  · field_simp at h ⊢
    linarith

/-- Galí (2015), (14), p. 135: under the targeting rule (13), the Phillips curve (2) holds iff
the price-level gap satisfies (14). -/
theorem nkpc_iff_priceEq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) {u p : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) :
    NKPC 𝔼 β κ u (inflOf p) (gapOf κ ϑ p) ↔ PriceEq 𝔼 β κ ϑ u p := by
  have hE : ∀ t, 𝔼.E t (inflOf p (t + 1)) = 𝔼.E t (p (t + 1)) - p t := fun t => by
    change 𝔼.E t (p (t + 1) - p t) = _
    rw [map_sub, hp t]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE] at e
    simp only [inflOf, gapOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (pc_iff_fourteen hβ0 hϑ _ _ _ _).1 e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE]
    simp only [inflOf, gapOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (pc_iff_fourteen hβ0 hϑ _ _ _ _).2 e

/-! ### Factorisation of (14) -/

/-- Galí (2015), (15), p. 136: the quasi-difference `w_t = p̂_t − δ p̂_{t−1}`. -/
noncomputable def wOf (β κ ϑ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  p t - del β κ ϑ • lag p t

/-- Galí (2015), (15), p. 136 (pointwise algebra): (14) holds iff the quasi-difference solves
the forward equation `w_t = βδ E_t w_{t+1} + δ u_t`; this is the factorisation
`(1 − γL − γβL⁻¹) = (γ/δ)(1 − δL)(1 − βδL⁻¹)`. -/
theorem fourteen_iff_w {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (P L Ep U : ℝ) :
    P = gam β κ ϑ * L + gam β κ ϑ * β * Ep + gam β κ ϑ * U ↔
      P - del β κ ϑ * L = β * del β κ ϑ * (Ep - del β κ ϑ * P) + del β κ ϑ * U := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hdg : del β κ ϑ = gam β κ ϑ * (1 + β * del β κ ϑ ^ 2) := by
    rw [← del_div_gam hβ0 hβ1 hϑ]; field_simp
  set g := gam β κ ϑ
  set d := del β κ ϑ
  have key : P - d * L - β * d * (Ep - d * P) - d * U =
      (1 + β * d ^ 2) * (P - (g * L + g * β * Ep + g * U)) := by
    linear_combination (-(L + β * Ep + U)) * hdg
  have hpos : 0 < 1 + β * d ^ 2 := by positivity
  constructor
  · intro h
    linear_combination key + (1 + β * d ^ 2) * h
  · intro h
    have : (1 + β * d ^ 2) * (P - (g * L + g * β * Ep + g * U)) = 0 := by
      rw [← key, h]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith

/-- Galí (2015), (15), p. 136: for an adapted price-level gap, (14) holds iff the
quasi-difference `w` solves `w_t = βδ E_t w_{t+1} + δ u_t`. -/
theorem priceEq_iff_w {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    PriceEq 𝔼 β κ ϑ u p ↔ ∀ t, wOf β κ ϑ p t =
      (β * del β κ ϑ) • 𝔼.E t (wOf β κ ϑ p (t + 1)) + del β κ ϑ • u t := by
  have hE : ∀ t, 𝔼.E t (wOf β κ ϑ p (t + 1)) = 𝔼.E t (p (t + 1)) - del β κ ϑ • p t :=
    fun t => by
      change 𝔼.E t (p (t + 1) - del β κ ϑ • p t) = _
      rw [map_sub, map_smul, hp t]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE]
    simp only [wOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (fourteen_iff_w hβ0 hβ1 hϑ _ _ _ _).1 e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE] at e
    simp only [wOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (fourteen_iff_w hβ0 hβ1 hϑ _ _ _ _).2 e

/-! ### The commitment path -/

/-- Galí (2015), (15), p. 136: `0 ≤ βδ < 1` for `κ ≠ 0`. -/
theorem beta_del_mem {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    0 ≤ β * del β κ ϑ ∧ β * del β κ ϑ < 1 := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  exact ⟨by positivity, by nlinarith⟩

/-- Galí (2015), (15), p. 136: the forward part `w_t = δ ∑_{k ≥ 0} (βδ)ᵏ E_t u_{t+k}` of the
commitment solution (the unique bounded solution of `w_t = βδ E_t w_{t+1} + δ u_t`). -/
noncomputable def fwd (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  del β κ ϑ • 𝔼.forwardSeries (β * del β κ ϑ) u t

/-- Galí (2015), (15), p. 136: the commitment price-level gap, `p̂_t = δ p̂_{t−1} + w_t`,
`p̂_{−1} = 0`. -/
noncomputable def pHat (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fwd 𝔼 β κ ϑ u 0
  | t + 1 => del β κ ϑ • pHat β κ ϑ u t + fwd 𝔼 β κ ϑ u (t + 1)

/-- Galí (2015), (15), p. 136: `p̂_t = δ p̂_{t−1} + w_t` for all `t ≥ 0` (`p̂_{−1} = 0`). -/
theorem pHat_eq (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ • lag (pHat 𝔼 β κ ϑ u) t + fwd 𝔼 β κ ϑ u t := by
  cases t with
  | zero => simp [pHat]
  | succ t => rfl

/-- Galí (2015), (15), p. 136: the commitment inflation path `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def inflC (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := inflOf (pHat 𝔼 β κ ϑ u)

/-- Galí (2015), (13) and (16), p. 135–136: the commitment output gap `x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapC (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  gapOf κ ϑ (pHat 𝔼 β κ ϑ u)

/-- Galí (2015), (15), p. 136: `w_t = βδ E_t w_{t+1} + δ u_t`. -/
theorem fwd_solves {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (t : ℕ) :
    fwd 𝔼 β κ ϑ u t = (β * del β κ ϑ) • 𝔼.E t (fwd 𝔼 β κ ϑ u (t + 1)) + del β κ ϑ • u t := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  rw [fwd, fwd, 𝔼.forwardSeries_solves ha0 ha1 hu hua t, map_smul, smul_add, smul_comm]

/-- Galí (2015), (15), p. 136: `w` is bounded. -/
theorem fwd_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (fwd 𝔼 β κ ϑ u) := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  obtain ⟨B, hB⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hu
  refine ⟨del β κ ϑ * B, fun t ω => ?_⟩
  have hd := del_pos (κ := κ) hβ0 hϑ
  simp only [fwd, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd]
  exact mul_le_mul_of_nonneg_left (hB t ω) hd.le

/-- Galí (2015), (15), p. 136: `w` is adapted. -/
theorem fwd_adapted {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (fwd 𝔼 β κ ϑ u) := by
  intro t
  conv_lhs => rw [fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t]
  rw [map_add, map_smul, map_smul, 𝔼.E_E_self, hua t, ← fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t]

/-- Galí (2015), (15), p. 136: the commitment price-level gap is adapted. -/
theorem pHat_adapted {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (pHat 𝔼 β κ ϑ u) := by
  have hf := fwd_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua
  intro t
  induction t with
  | zero => exact hf 0
  | succ t ih =>
    change 𝔼.E (t + 1) (del β κ ϑ • pHat 𝔼 β κ ϑ u t + fwd 𝔼 β κ ϑ u (t + 1)) = _
    have h1 : 𝔼.E (t + 1) (pHat 𝔼 β κ ϑ u t) = pHat 𝔼 β κ ϑ u t := by
      have := 𝔼.known (Nat.le_succ t) (pHat 𝔼 β κ ϑ u t)
      rwa [ih] at this
    rw [map_add, map_smul, h1, hf (t + 1)]
    rfl

/-- Galí (2015), (15), p. 136: the commitment price-level gap is bounded,
`|p̂_t| ≤ B/(1 − δ)` when `|w_t| ≤ B`. -/
theorem pHat_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (pHat 𝔼 β κ ϑ u) := by
  obtain ⟨B, hB⟩ := fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  have h1d : 0 < 1 - del β κ ϑ := by linarith
  refine ⟨B / (1 - del β κ ϑ), fun t ω => ?_⟩
  induction t with
  | zero =>
    change |fwd 𝔼 β κ ϑ u 0 ω| ≤ _
    have hB0 := hB 0 ω
    have : 0 ≤ B := (abs_nonneg _).trans hB0
    rw [le_div_iff₀ h1d]
    nlinarith
  | succ t ih =>
    change |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω + fwd 𝔼 β κ ϑ u (t + 1) ω| ≤ _
    have h2 := hB (t + 1) ω
    have h3 : |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω| ≤ del β κ ϑ * (B / (1 - del β κ ϑ)) := by
      rw [abs_mul, abs_of_pos hd]
      exact mul_le_mul_of_nonneg_left ih hd.le
    have h4 : del β κ ϑ * (B / (1 - del β κ ϑ)) + B = B / (1 - del β κ ϑ) := by
      field_simp; ring
    calc _ ≤ |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω| + |fwd 𝔼 β κ ϑ u (t + 1) ω| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- Galí (2015), (15), p. 136: the quasi-difference of the commitment price-level gap is `w`. -/
theorem wOf_pHat (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    wOf β κ ϑ (pHat 𝔼 β κ ϑ u) t = fwd 𝔼 β κ ϑ u t := by
  rw [wOf, pHat_eq 𝔼 β κ ϑ u t]
  abel

/-- **Galí (2015), (14)–(15), pp. 135–136**: the commitment price-level gap solves (14) with
`p̂_{−1} = 0`. -/
theorem pHat_priceEq {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    PriceEq 𝔼 β κ ϑ u (pHat 𝔼 β κ ϑ u) := by
  rw [priceEq_iff_w 𝔼 hβ0 hβ1 hϑ (pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua)]
  intro t
  rw [wOf_pHat, wOf_pHat]
  exact fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t

/-- **Galí (2015), (15), p. 136 (uniqueness)**: the commitment price-level gap is the unique
bounded adapted solution of (14) with `p̂_{−1} = 0`. -/
theorem priceEq_unique {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {q : ℕ → Ω → ℝ}
    (hq : PriceEq 𝔼 β κ ϑ u q) (hqa : 𝔼.Adapted q) (hqb : BoundedProc q) :
    q = pHat 𝔼 β κ ϑ u := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have hw := (priceEq_iff_w 𝔼 hβ0 hβ1 hϑ hqa).1 hq
  obtain ⟨Mq, hMq⟩ := hqb
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hwb : BoundedProc (wOf β κ ϑ q) := by
    refine ⟨Mq + del β κ ϑ * Mq, fun t ω => ?_⟩
    have hl : |lag q t ω| ≤ Mq := by
      cases t with
      | zero => simpa using (abs_nonneg (q 0 ω)).trans (hMq 0 ω)
      | succ t => exact hMq t ω
    simp only [wOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc _ ≤ |q t ω| + |del β κ ϑ * lag q t ω| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos hd]
        exact add_le_add (hMq t ω) (mul_le_mul_of_nonneg_left hl hd.le)
  have hweq : wOf β κ ϑ q = fwd 𝔼 β κ ϑ u :=
    𝔼.forward_unique (by rw [abs_of_nonneg ha0]; exact ha1) hw
      (fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua) hwb (fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu)
  funext t
  induction t with
  | zero =>
    have := congrFun hweq 0
    simpa [wOf, pHat] using this
  | succ t ih =>
    have := congrFun hweq (t + 1)
    simp only [wOf, lag_succ, ih] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
    rfl

/-- Galí (2015), (14), p. 135: the commitment path satisfies the Phillips curve (2). -/
theorem cand_nkpc {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    NKPC 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) :=
  (nkpc_iff_priceEq 𝔼 hβ0 hϑ (pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua)).2
    (pHat_priceEq 𝔼 hβ0 hβ1 hϑ hκ hu hua)

/-- Galí (2015), (15)–(16), p. 136: the commitment inflation and output gap are adapted and
bounded. -/
theorem cand_adapted_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (inflC 𝔼 β κ ϑ u) ∧ 𝔼.Adapted (gapC 𝔼 β κ ϑ u) ∧
      BoundedProc (inflC 𝔼 β κ ϑ u) ∧ BoundedProc (gapC 𝔼 β κ ϑ u) := by
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua
  have hla := lag_adapted 𝔼 hpa
  obtain ⟨B, hB⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
  have hl : ∀ t ω, |lag (pHat 𝔼 β κ ϑ u) t ω| ≤ B := fun t ω => by
    cases t with
    | zero => simpa using (abs_nonneg (pHat 𝔼 β κ ϑ u 0 ω)).trans (hB 0 ω)
    | succ t => exact hB t ω
  refine ⟨fun t => ?_, fun t => ?_, ⟨B + B, fun t ω => ?_⟩, ⟨|κ / ϑ| * B, fun t ω => ?_⟩⟩
  · change 𝔼.E t (pHat 𝔼 β κ ϑ u t - lag (pHat 𝔼 β κ ϑ u) t) = _
    rw [map_sub, hpa t, hla t]; rfl
  · change 𝔼.E t ((-(κ / ϑ)) • pHat 𝔼 β κ ϑ u t) = _
    rw [map_smul, hpa t]; rfl
  · change |pHat 𝔼 β κ ϑ u t ω - lag (pHat 𝔼 β κ ϑ u) t ω| ≤ _
    exact (abs_sub _ _).trans (add_le_add (hB t ω) (hl t ω))
  · change |(-(κ / ϑ)) * pHat 𝔼 β κ ϑ u t ω| ≤ _
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-! ### AR(1) cost-push shocks: (15) and (16) -/

/-- Galí (2015), (15), p. 136: `1 − δβρ_u > 0` for `|ρ_u| < 1`. -/
theorem one_sub_dbr_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) : 0 < 1 - del β κ ϑ * β * ρ := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have h1 : del β κ ϑ * β * ρ ≤ β * del β κ ϑ * |ρ| := by
    rw [mul_comm (del β κ ϑ) β]
    exact mul_le_mul_of_nonneg_left (le_abs_self ρ) ha0
  have h2 : β * del β κ ϑ * |ρ| < 1 := by
    calc β * del β κ ϑ * |ρ| ≤ β * del β κ ϑ * 1 :=
          mul_le_mul_of_nonneg_left hρ.le ha0
      _ < 1 := by rw [mul_one]; exact ha1
  linarith

/-- Galí (2015), (15), p. 136 and footnote 4: with an AR(1) shock, the forward part is
`w_t = δ/(1 − δβρ_u) u_t`. -/
theorem fwd_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    fwd 𝔼 β κ ϑ u t = (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have hpos := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  set c := del β κ ϑ / (1 - del β κ ϑ * β * ρ)
  have hsol : ∀ t, (fun t => c • u t) t =
      (β * del β κ ϑ) • 𝔼.E t ((fun t => c • u t) (t + 1)) + del β κ ϑ • u t := by
    intro t
    simp only [map_smul, har.2 t, smul_smul, ← add_smul]
    congr 1
    simp only [c]
    field_simp
    ring
  have hb : BoundedProc (fun t => c • u t) := by
    refine ⟨|c| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg c)
  have := 𝔼.forward_unique (by rw [abs_of_nonneg ha0]; exact ha1)
    (fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu har.1) hsol (fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu) hb
  exact congrFun this t

/-- **Galí (2015), (15), p. 136**: with an AR(1) cost-push shock the commitment price-level gap
follows `p̂_t = δ p̂_{t−1} + δ/(1 − δβρ_u) u_t` for `t ≥ 0`, `p̂_{−1} = 0`. -/
theorem pHat_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ • lag (pHat 𝔼 β κ ϑ u) t +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t := by
  rw [pHat_eq, fwd_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]

/-- **Galí (2015), (16), p. 136**: the commitment output gap follows
`x_t = δ x_{t−1} − κδ/(ϑ(1 − δβρ_u)) u_t` for `t ≥ 1`, and (with `x_{−1} = 0`) at `t = 0`. -/
theorem gapC_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    gapC 𝔼 β κ ϑ u t = del β κ ϑ • lag (gapC 𝔼 β κ ϑ u) t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u t := by
  have hpos := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  have hl : lag (gapC 𝔼 β κ ϑ u) t = (-(κ / ϑ)) • lag (pHat 𝔼 β κ ϑ u) t :=
    lag_smul _ _ t
  rw [hl, gapC, gapOf, pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har t, smul_add, smul_smul, smul_smul,
    smul_smul, sub_eq_add_neg (G := Ω → ℝ), ← neg_smul]
  congr 2
  · ring
  · field_simp

/-- **Galí (2015), p. 136**: the impact response of the output gap under commitment,
`x_0 = −κδ/(ϑ(1 − δβρ_u)) u_0`. -/
theorem gapC_zero {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    gapC 𝔼 β κ ϑ u 0 = (-(κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ)))) • u 0 := by
  rw [gapC_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har 0, neg_smul]
  simp

/-! ### The Lagrangian argument: telescoping with a transversality term -/

/-- Galí (2015), p. 134 (the Lagrangian argument, abstract form): if
`g_t = D_t + 2 (h_t − h_{t+1})` with `D_t ≥ 0`, `h_0 = 0` (the constraint of period `−1` does
not bind, `ξ_{−1} = 0`) and `h_t → 0` (transversality), and `∑ g_t = G`, then `∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + 2 * (h t - h (t + 1))) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t + 2 * h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.add (hh.const_mul 2)

/-! ### Optimality under uncertainty -/

/-- Galí (2015), p. 134 ("the law of iterated expectations has been used"): the pull-out
property `E_t (a y) = a E_t y` for `a` known at `t`. It holds for true conditional expectations
(`perfectForesight_pullOut`, `finiteTree_pullOut`) but is not among the `ExpectationSystem`
fields, so the stochastic optimality theorems take it as a hypothesis. -/
def PullOut : Prop := ∀ t (a y : Ω → ℝ), 𝔼.E t a = a → 𝔼.E t (a * y) = a * 𝔼.E t y

/-- Galí (2015), p. 134: perfect foresight has the pull-out property. -/
theorem perfectForesight_pullOut : PullOut perfectForesight := fun _ _ _ _ => rfl

/-- Galí (2015), p. 134: the cell-average expectations of a finite event tree have the pull-out
property, so the hypothesis is satisfiable under genuine uncertainty. -/
theorem finiteTree_pullOut {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    PullOut T.toExpectationSystem := by
  classical
  intro t a y ha
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at ha ⊢
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  have hcell : ∀ ω', T.info t ω' ω → a ω' = a ω := fun ω' h => by
    rw [← ha, T.condE_congr a h]
  simp only [ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num,
    Pi.mul_apply]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  by_cases h : T.info t ω' ω
  · simp only [h, ↓reduceIte, hcell ω' h]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

/-- Galí (2015), p. 134: the period loss `π_t² + ϑ x_t²`. -/
def periodLoss (ϑ : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => π t ω ^ 2 + ϑ * x t ω ^ 2

/-- Galí (2015), p. 134: the expected loss `E_0 ∑_{t ≥ 0} βᵗ (π_t² + ϑ x_t²)` (a date-0 random
variable). -/
noncomputable def expLoss (β ϑ : ℝ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, β ^ t * periodLoss ϑ π x t ω)

/-- Galí (2015), p. 134: an admissible plan: bounded adapted inflation and output gap
satisfying the Phillips curve (2) at every date and state. -/
def Plan (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ u π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Galí (2015), p. 134: for a bounded plan the expected loss is the genuine infinite sum
`∑ βᵗ E_0(π_t² + ϑ x_t²)` (`E_0` commutes with the geometrically dominated series). -/
theorem expLoss_hasSum {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (periodLoss ϑ π x t) ω) (expLoss 𝔼 β ϑ π x ω) := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨B, hB⟩ := hx
  have hpl : ∀ t ω, |periodLoss ϑ π x t ω| ≤ A ^ 2 + ϑ * B ^ 2 := by
    intro t ω
    have h1 : π t ω ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t ω) 2
    have h2 : x t ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t ω) 2
    unfold periodLoss
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hϑ]
  have hf : ∀ k ω, |β ^ k * periodLoss ϑ π x k ω| ≤ β ^ k * (A ^ 2 + ϑ * B ^ 2) := by
    intro k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hpl k ω) (pow_nonneg hβ0 k)
  have hE : 𝔼.E 0 (fun ω' => ∑' k, β ^ k * periodLoss ϑ π x k ω') ω =
      ∑' k, 𝔼.E 0 (fun ω' => β ^ k * periodLoss ϑ π x k ω') ω := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => β ^ k * periodLoss ϑ π x k ω') ω =
      β ^ k * 𝔼.E 0 (periodLoss ϑ π x k) ω := fun k => by
    have : (fun ω' => β ^ k * periodLoss ϑ π x k ω') = β ^ k • periodLoss ϑ π x k := rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => β ^ t * 𝔼.E 0 (periodLoss ϑ π x t) ω) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2)) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hpl k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, β ^ k * periodLoss ϑ π x k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-- Galí (2015), p. 134 (the Lagrangian identity, one period): if `(π*, x*)` satisfies the
first-order conditions with an adapted multiplier `ξ` and `(π, x)` is any other solution of the
Phillips curve, then, with `d = (π, x) − (π*, x*)`,
`E_0 ℓ_t − E_0 ℓ*_t = E_0(dπ_t² + ϑ dx_t²) + 2 E_0(ξ_{t−1} dπ_t) − 2β E_0(ξ_t dπ_{t+1})`
(the conditional expectation in the constraint is removed by the law of iterated expectations
and the pull-out property). -/
theorem E0_identity (hpo : PullOut 𝔼) {β κ ϑ : ℝ} {u π x πs xs ξ : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hns : NKPC 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (periodLoss ϑ π x t) ω - 𝔼.E 0 (periodLoss ϑ πs xs t) ω =
      𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) ω +
        2 * 𝔼.E 0 (fun ω => lag ξ t ω * (π t ω - πs t ω)) ω -
          2 * β * 𝔼.E 0 (fun ω => lag ξ (t + 1) ω * (π (t + 1) ω - πs (t + 1) ω)) ω := by
  have hfun : periodLoss ϑ π x t - periodLoss ϑ πs xs t =
      (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) +
        (2 : ℝ) • (fun ω => lag ξ t ω * (π t ω - πs t ω)) -
          (2 * β) • (ξ t * (𝔼.E t (π (t + 1)) - 𝔼.E t (πs (t + 1)))) := by
    funext ω'
    have n1 := congrFun (hn t) ω'
    have n2 := congrFun (hns t) ω'
    have f1 := congrFun (hfoc t).1 ω'
    have f2 := congrFun (hfoc t).2 ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n1 n2 f1 f2
    simp only [periodLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.mul_apply]
    linear_combination 2 * (π t ω' - πs t ω') * f2 + 2 * (x t ω' - xs t ω') * f1 -
      2 * ξ t ω' * (n1 - n2)
  have hpull : 𝔼.E 0 (ξ t * (𝔼.E t (π (t + 1)) - 𝔼.E t (πs (t + 1)))) =
      𝔼.E 0 (fun ω => lag ξ (t + 1) ω * (π (t + 1) ω - πs (t + 1) ω)) := by
    rw [← map_sub, ← hpo t _ _ (hξa t), 𝔼.tower (Nat.zero_le t)]
    rfl
  have := congrFun (congrArg (𝔼.E 0) hfun) ω
  rw [map_sub, map_sub, map_add, map_smul, map_smul, hpull] at this
  simpa [mul_assoc] using this

/-- Galí (2015), p. 134: `E_0` of a nonnegative random variable is nonnegative. -/
theorem E0_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

/-- **Galí (2015), pp. 134–135 (sufficiency of the first-order conditions, stochastic)**: if a
plan `(π*, x*)` satisfies the commitment first-order conditions `ϑ x*_t = κ ξ_t`,
`π*_t = ξ_{t−1} − ξ_t` (`ξ_{−1} = 0`) with a bounded adapted multiplier, then for every other
plan `(π, x)` the excess expected loss is the genuine infinite sum
`E_0 L(π, x) − E_0 L(π*, x*) = ∑ βᵗ E_0((π_t − π*_t)² + ϑ (x_t − x*_t)²)`. -/
theorem expLoss_sub_hasSum (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hϑ : 0 ≤ ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) ω)
      (expLoss 𝔼 β ϑ π x ω - expLoss 𝔼 β ϑ πs xs ω) := by
  obtain ⟨hn, -, -, hπb, hxb⟩ := hp
  obtain ⟨hns, -, -, hπsb, hxsb⟩ := hps
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨As, hAs⟩ := hπsb
  obtain ⟨Z, hZ⟩ := hξb
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0 ω)
  have hlag : ∀ t ω, |lag ξ t ω| ≤ Z := fun t ω => by
    cases t with
    | zero => simpa using hZ0
    | succ t => exact hZ t ω
  have hH : ∀ t ω, |lag ξ t ω * (π t ω - πs t ω)| ≤ Z * (A + As) := fun t ω => by
    rw [abs_mul]
    exact mul_le_mul (hlag t ω) ((abs_sub _ _).trans (add_le_add (hA t ω) (hAs t ω)))
      (abs_nonneg _) hZ0
  refine hasSum_of_telescope
    ((expLoss_hasSum 𝔼 hβ0 hβ1 hϑ ⟨A, hA⟩ hxb ω).sub (expLoss_hasSum 𝔼 hβ0 hβ1 hϑ ⟨As, hAs⟩ hxsb ω))
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω))
    (h := fun t => β ^ t * 𝔼.E 0 (fun ω => lag ξ t ω * (π t ω - πs t ω)) ω)
    (fun t => ?_) ?_ ?_
  · rw [← mul_sub, E0_identity 𝔼 hpo hn hns hξa hfoc t ω, pow_succ]
    ring
  · simp only [lag_zero, Pi.zero_apply, zero_mul, pow_zero, one_mul]
    rw [𝔼.const 0 0]
  · refine squeeze_zero_norm (a := fun t => β ^ t * (Z * (A + As))) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hH t) 0 ω) (pow_nonneg hβ0 t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (Z * (A + As))

/-- **Galí (2015), pp. 134–135 (optimality)**: a plan satisfying the first-order conditions with
a bounded adapted multiplier has the smallest expected loss among all plans, state by state. -/
theorem expLoss_le_of_foc (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hϑ : 0 ≤ ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω) :
    expLoss 𝔼 β ϑ πs xs ω ≤ expLoss 𝔼 β ϑ π x ω :=
  sub_nonneg.1 ((expLoss_sub_hasSum 𝔼 hpo hβ0 hβ1 hϑ hp hps hξa hξb hfoc ω).nonneg
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω)))

/-- **Galí (2015), pp. 134–135 (uniqueness of the optimum, stochastic)**: a plan attaining the
same expected loss in state `ω` as a plan satisfying the first-order conditions coincides with it
in conditional mean square: `E_0 (π_t − π*_t)² = E_0 (x_t − x*_t)² = 0` at `ω`, for every `t`
(under perfect foresight this is equality of the paths). -/
theorem eq_of_expLoss_eq (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω)
    (heq : expLoss 𝔼 β ϑ π x ω = expLoss 𝔼 β ϑ πs xs ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by
  have hs := expLoss_sub_hasSum 𝔼 hpo hβ0.le hβ1 hϑ.le hp hps hξa hξb hfoc ω
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω))).1 hs
  have ht := congrFun hz t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  have hsplit : (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) =
      (fun ω => (π t ω - πs t ω) ^ 2) + ϑ • (fun ω => (x t ω - xs t ω) ^ 2) := rfl
  rw [hsplit, map_add, map_smul] at ht
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
  have h1 := E0_nonneg 𝔼 (f := fun ω => (π t ω - πs t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E0_nonneg 𝔼 (f := fun ω => (x t ω - xs t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h3 := mul_nonneg hϑ.le h2
  constructor
  · linarith
  · have : ϑ * 𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hϑ.ne'
    · exact h

/-- Galí (2015), p. 135: the commitment path satisfies the first-order conditions with the
multiplier `ξ_t = −p̂_t`. -/
theorem cand_foc {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    ϑ • gapC 𝔼 β κ ϑ u t = κ • (fun s => -pHat 𝔼 β κ ϑ u s) t ∧
      inflC 𝔼 β κ ϑ u t = lag (fun s => -pHat 𝔼 β κ ϑ u s) t - (fun s => -pHat 𝔼 β κ ϑ u s) t := by
  refine ⟨?_, ?_⟩
  · simp only [gapC, gapOf, smul_smul, smul_neg, ← neg_smul]
    congr 1
    field_simp
  · rw [lag_neg]
    simp only [inflC, inflOf, sub_neg_eq_add]
    abel

/-- **Galí (2015), §5.2.2, pp. 133–136 (THE OPTIMAL POLICY UNDER COMMITMENT, stochastic)**:
for a bounded adapted cost-push process, the path (15)–(16) (in general form `p̂_t = δ p̂_{t−1} +
δ ∑ (βδ)ᵏ E_t u_{t+k}`, `π_t = p̂_t − p̂_{t−1}`, `x_t = −(κ/ϑ) p̂_t`) is an admissible plan and,
state by state, minimises the expected loss `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` among all bounded adapted
plans; any plan with the same expected loss at `ω` equals it in conditional mean square. -/
theorem commitment_optimal (hpo : PullOut 𝔼) {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) (hκ : κ ≠ 0) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    Plan 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ∧
      ∀ π x, Plan 𝔼 β κ u π x → ∀ ω,
        expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω ≤ expLoss 𝔼 β ϑ π x ω ∧
        (expLoss 𝔼 β ϑ π x ω = expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω →
          ∀ t, 𝔼.E 0 (fun ω => (π t ω - inflC 𝔼 β κ ϑ u t ω) ^ 2) ω = 0 ∧
            𝔼.E 0 (fun ω => (x t ω - gapC 𝔼 β κ ϑ u t ω) ^ 2) ω = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := cand_adapted_bounded 𝔼 hβ0 hβ1 hϑ hκ hu hua
  have hplan : Plan 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) :=
    ⟨cand_nkpc 𝔼 hβ0 hβ1 hϑ hκ hu hua, h1, h2, h3, h4⟩
  have hξa : 𝔼.Adapted (fun s => -pHat 𝔼 β κ ϑ u s) := fun t => by
    simp only [map_neg, pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua t]
  have hξb : BoundedProc (fun s => -pHat 𝔼 β κ ϑ u s) := by
    obtain ⟨B, hB⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
    exact ⟨B, fun t ω => by simpa using hB t ω⟩
  refine ⟨hplan, fun π x hp ω => ⟨?_, ?_⟩⟩
  · exact expLoss_le_of_foc 𝔼 hpo hβ0.le hβ1 hϑ.le hp hplan hξa hξb (cand_foc 𝔼 hϑ u) ω
  · intro heq
    exact eq_of_expLoss_eq 𝔼 hpo hβ0 hβ1 hϑ hp hplan hξa hξb (cand_foc 𝔼 hϑ u) ω heq

/-! ### The deterministic problem: a known cost-push path and finite loss -/

namespace Det

/-- Galí (2015), p. 134 (perfect foresight): the constraints `π_t = β π_{t+1} + κ x_t + u_t`,
`t ≥ 0`. -/
def Feasible (β κ : ℝ) (u π x : ℕ → ℝ) : Prop := ∀ t, π t = β * π (t + 1) + κ * x t + u t

/-- Galí (2015), p. 134: the discounted period loss `βᵗ (π_t² + ϑ x_t²)`. -/
def lossTerm (β ϑ : ℝ) (π x : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 134: the loss `∑ βᵗ (π_t² + ϑ x_t²)` is finite. -/
def FiniteLoss (β ϑ : ℝ) (π x : ℕ → ℝ) : Prop := Summable (lossTerm β ϑ π x)

/-- Galí (2015), p. 134: the loss `∑_{t ≥ 0} βᵗ (π_t² + ϑ x_t²)` (used on finite-loss paths). -/
noncomputable def loss (β ϑ : ℝ) (π x : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ π x t

/-- Galí (2015), p. 134: `(π, x)` solves the commitment problem: it is feasible, has finite loss,
and its loss is no larger than that of any feasible path with finite loss. -/
def IsOptimal (β κ ϑ : ℝ) (u π x : ℕ → ℝ) : Prop :=
  Feasible β κ u π x ∧ FiniteLoss β ϑ π x ∧
    ∀ π' x', Feasible β κ u π' x' → FiniteLoss β ϑ π' x' → loss β ϑ π x ≤ loss β ϑ π' x'

/-- Galí (2015), p. 134 (transversality): on a finite-loss path `βᵗ π_t² → 0` and
`βᵗ x_t² → 0`. -/
theorem tendsto_disc_sq {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) {π x : ℕ → ℝ}
    (hl : FiniteLoss β ϑ π x) :
    Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * x t ^ 2) atTop (𝓝 0) := by
  have hL := hl.tendsto_atTop_zero
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    simp only [lossTerm]
    nlinarith
  · have hL' := hL.div_const ϑ
    rw [zero_div] at hL'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL'
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * π t ^ 2 := by positivity
    simp only [lossTerm]
    rw [le_div_iff₀ hϑ]
    nlinarith

/-- **Galí (2015), pp. 134–135 (sufficiency of the first-order conditions, deterministic)**:
if a feasible finite-loss path `(π*, x*)` satisfies the first-order conditions with multipliers
`ξ` (`ξ_{−1} = 0`), then for every feasible finite-loss path `(π, x)`
`L(π, x) − L(π*, x*) = ∑ βᵗ ((π_t − π*_t)² + ϑ (x_t − x*_t)²)`: the Lagrangian cross terms
telescope to `−2β^{T+1} ξ_T (π_{T+1} − π*_{T+1}) → 0` (transversality). -/
theorem loss_sub_hasSum {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u π x πs xs ξ : ℕ → ℝ} (hf : Feasible β κ u π x) (hl : FiniteLoss β ϑ π x)
    (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs) (hξ : FOC κ ϑ πs xs ξ) :
    HasSum (fun t => β ^ t * ((π t - πs t) ^ 2 + ϑ * (x t - xs t) ^ 2))
      (loss β ϑ π x - loss β ϑ πs xs) := by
  have hξx : ∀ t, ξ t = ϑ / κ * xs t := fun t => by
    field_simp; linarith [(hξ t).1]
  obtain ⟨hπ0, -⟩ := tendsto_disc_sq hβ0 hϑ hl
  obtain ⟨hπs0, hxs0⟩ := tendsto_disc_sq hβ0 hϑ hls
  have hξ0 : Tendsto (fun t => β ^ t * ξ t ^ 2) atTop (𝓝 0) := by
    have : (fun t => β ^ t * ξ t ^ 2) = fun t => (ϑ / κ) ^ 2 * (β ^ t * xs t ^ 2) := by
      funext t; rw [hξx t]; ring
    rw [this]
    simpa using hxs0.const_mul ((ϑ / κ) ^ 2)
  have hlag0 : Tendsto (fun t => β ^ t * lag ξ t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * lag ξ (t + 1) ^ 2) = fun t => β * (β ^ t * ξ t ^ 2) := by
      funext t; rw [lag_succ, pow_succ]; ring
    rw [this]
    simpa using hξ0.const_mul β
  have hd0 : Tendsto (fun t => β ^ t * (π t - πs t) ^ 2) atTop (𝓝 0) := by
    have hup := (hπ0.const_mul 2).add (hπs0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun t => by positivity) (fun t => ?_)
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have : (π t - πs t) ^ 2 ≤ 2 * π t ^ 2 + 2 * πs t ^ 2 := by nlinarith [sq_nonneg (π t + πs t)]
    have := mul_le_mul_of_nonneg_left this hb
    simp only
    nlinarith
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum)
    (fun t => by positivity) (h := fun t => β ^ t * lag ξ t * (π t - πs t))
    (fun t => ?_) (by simp) ?_
  · have n1 := hf t
    have n2 := hfs t
    have f1 := (hξ t).1
    have f2 := (hξ t).2
    simp only [lossTerm, lag_succ]
    linear_combination β ^ t * (2 * (π t - πs t) * f2 + 2 * (x t - xs t) * f1 -
      2 * ξ t * (n1 - n2))
  · have hup := hlag0.add hd0
    rw [add_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have hab : |lag ξ t * (π t - πs t)| ≤ lag ξ t ^ 2 + (π t - πs t) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (lag ξ t + (π t - πs t)),
        sq_nonneg (lag ξ t - (π t - πs t))]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hb]
    nlinarith [mul_le_mul_of_nonneg_left hab hb]

/-- **Galí (2015), pp. 134–135 (optimality, deterministic)**: a feasible finite-loss path
satisfying the first-order conditions is optimal. -/
theorem isOptimal_of_foc {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u πs xs ξ : ℕ → ℝ} (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs)
    (hξ : FOC κ ϑ πs xs ξ) : IsOptimal β κ ϑ u πs xs :=
  ⟨hfs, hls, fun _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hϑ hκ hf hl hfs hls hξ).nonneg (fun t => by positivity))⟩

/-- **Galí (2015), pp. 134–135 (uniqueness, deterministic)**: a feasible finite-loss path with the
same loss as a path satisfying the first-order conditions coincides with it (strict convexity:
the excess loss is `∑ βᵗ (dπ_t² + ϑ dx_t²)`). -/
theorem eq_of_loss_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u π x πs xs ξ : ℕ → ℝ} (hf : Feasible β κ u π x) (hl : FiniteLoss β ϑ π x)
    (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs) (hξ : FOC κ ϑ πs xs ξ)
    (heq : loss β ϑ π x = loss β ϑ πs xs) : π = πs ∧ x = xs := by
  have hs := loss_sub_hasSum hβ0.le hϑ hκ hf hl hfs hls hξ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, (π t - πs t) ^ 2 + ϑ * (x t - xs t) ^ 2 = 0 := fun t => by
    have := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have h1 := ht t
    have : (π t - πs t) ^ 2 = 0 := by nlinarith [sq_nonneg (π t - πs t), sq_nonneg (x t - xs t)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · have h1 := ht t
    have h2 : ϑ * (x t - xs t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (π t - πs t), sq_nonneg (x t - xs t)]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hϑ.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith

/-- Galí (2015), p. 136: a known cost-push path as a (trivially adapted) process on the
one-point state space of perfect foresight. -/
def lift (u : ℕ → ℝ) : ℕ → Unit → ℝ := fun t _ => u t

/-- **Galí (2015), (15), p. 136 (deterministic)**: the commitment price-level gap for a known
cost-push path, `p̂_t = δ p̂_{t−1} + δ ∑_{k ≥ 0} (βδ)ᵏ u_{t+k}`, `p̂_{−1} = 0`. -/
noncomputable def pHatD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  pHat perfectForesight β κ ϑ (lift u) t ()

/-- Galí (2015), (15), p. 136 (deterministic): commitment inflation `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def inflD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  pHatD β κ ϑ u t - lag (pHatD β κ ϑ u) t

/-- Galí (2015), (13), (16), pp. 135–136 (deterministic): commitment output gap
`x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ := -(κ / ϑ) * pHatD β κ ϑ u t

/-- Galí (2015), p. 136: the lag commutes with evaluation at the single state. -/
theorem lag_pHatD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    lag (pHatD β κ ϑ u) t = lag (pHat perfectForesight β κ ϑ (lift u)) t () := by
  cases t <;> rfl

/-- Galí (2015), (15), p. 136 (deterministic): the commitment price-level gap is bounded. -/
theorem pHatD_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : ∃ B, ∀ t, |pHatD β κ ϑ u t| ≤ B := by
  obtain ⟨B, hB⟩ := pHat_bounded perfectForesight hβ0 hβ1 hϑ hκ (u := lift u)
    (fun t _ => hu t)
  exact ⟨B, fun t => hB t ()⟩

/-- Galí (2015), (14)–(16), pp. 135–136 (deterministic): the commitment path is feasible. -/
theorem candD_feasible {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) :
    Feasible β κ u (inflD β κ ϑ u) (gapD β κ ϑ u) := by
  intro t
  have h := congrFun (cand_nkpc perfectForesight hβ0 hβ1 hϑ hκ (u := lift u) (fun t _ => hu t)
    (fun _ => rfl) t) ()
  simp only [inflD, gapD, lag_pHatD]
  exact h

/-- Galí (2015), p. 135 (deterministic): the commitment path satisfies the first-order
conditions with `ξ_t = −p̂_t`. -/
theorem candD_foc {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → ℝ) :
    FOC κ ϑ (inflD β κ ϑ u) (gapD β κ ϑ u) (fun t => -pHatD β κ ϑ u t) := by
  intro t
  have h := cand_foc perfectForesight (β := β) (κ := κ) hϑ (lift u) t
  have h1 := congrFun h.1 ()
  have h2 := congrFun h.2 ()
  refine ⟨h1, ?_⟩
  have hl : lag (fun t => -pHatD β κ ϑ u t) t =
      lag (fun s => -pHat perfectForesight β κ ϑ (lift u) s) t () := by
    cases t <;> rfl
  rw [hl]
  simp only [inflD, lag_pHatD]
  change inflC perfectForesight β κ ϑ (lift u) t () + _ - _ = 0
  rw [h2]
  simp only [Pi.sub_apply, Pi.neg_apply, pHatD]
  ring

/-- Galí (2015), p. 134 (deterministic): a bounded path has finite loss. -/
theorem finiteLoss_of_bounded {β ϑ A B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {π x : ℕ → ℝ} (hπ : ∀ t, |π t| ≤ A) (hx : ∀ t, |x t| ≤ B) : FiniteLoss β ϑ π x := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2))
  have h1 : π t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπ t) 2
  have h2 : x t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx t) 2
  unfold lossTerm
  exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h2 hϑ])
    (pow_nonneg hβ0 t)

/-- Galí (2015), (15)–(16), p. 136 (deterministic): the commitment path has finite loss. -/
theorem candD_finiteLoss {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : FiniteLoss β ϑ (inflD β κ ϑ u) (gapD β κ ϑ u) := by
  obtain ⟨B, hB⟩ := pHatD_bounded hβ0 hβ1 hϑ hκ hu
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (A := B + B) (B := |κ / ϑ| * B)
    (fun t => ?_) (fun t => ?_)
  · have hl : |lag (pHatD β κ ϑ u) t| ≤ B := by
      cases t with
      | zero => simpa using hB0
      | succ t => exact hB t
    exact (abs_sub _ _).trans (add_le_add (hB t) hl)
  · simp only [gapD, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg _)

/-- **Galí (2015), §5.2.2, pp. 133–136 (THE OPTIMAL POLICY UNDER COMMITMENT, deterministic)**:
for a bounded known cost-push path, the commitment path is optimal among all feasible paths
with finite loss. -/
theorem candD_isOptimal {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : IsOptimal β κ ϑ u (inflD β κ ϑ u) (gapD β κ ϑ u) :=
  isOptimal_of_foc hβ0.le hϑ hκ (candD_feasible hβ0 hβ1 hϑ hκ hu)
    (candD_finiteLoss hβ0 hβ1 hϑ hκ hu) (candD_foc hϑ u)

/-- **Galí (2015), §5.2.2 (uniqueness, deterministic)**: the commitment path is the only
optimal path. -/
theorem isOptimal_iff {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) (π x : ℕ → ℝ) :
    IsOptimal β κ ϑ u π x ↔ π = inflD β κ ϑ u ∧ x = gapD β κ ϑ u := by
  have hc := candD_isOptimal hβ0 hβ1 hϑ hκ hu
  constructor
  · rintro ⟨hf, hl, hmin⟩
    have h1 := hmin _ _ hc.1 hc.2.1
    have h2 := hc.2.2 _ _ hf hl
    exact eq_of_loss_eq hβ0 hϑ hκ hf hl hc.1 hc.2.1 (candD_foc hϑ u) (le_antisymm h1 h2)
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- **Galí (2015), §5.2.2 (existence and uniqueness, deterministic)**: the commitment problem
has exactly one solution. -/
theorem existsUnique_optimal {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ), IsOptimal β κ ϑ u p.1 p.2 := by
  refine ⟨(inflD β κ ϑ u, gapD β κ ϑ u), candD_isOptimal hβ0 hβ1 hϑ hκ hu, ?_⟩
  rintro ⟨π, x⟩ h
  obtain ⟨h1, h2⟩ := (isOptimal_iff hβ0 hβ1 hϑ hκ hu π x).1 h
  rw [h1, h2]

/-- **Galí (2015), pp. 134–135 (necessity and sufficiency of the first-order conditions)**: a
feasible finite-loss path is optimal iff it satisfies the first-order conditions for some
multipliers, iff it satisfies the targeting rule `x_t = −(κ/ϑ) p̂_t` (13). -/
theorem isOptimal_iff_foc {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) {π x : ℕ → ℝ} (hf : Feasible β κ u π x)
    (hl : FiniteLoss β ϑ π x) :
    (IsOptimal β κ ϑ u π x ↔ ∃ ξ, FOC κ ϑ π x ξ) ∧
      (IsOptimal β κ ϑ u π x ↔ ∀ t, x t = -(κ / ϑ) * priceGap π t) := by
  have h1 : IsOptimal β κ ϑ u π x ↔ ∃ ξ, FOC κ ϑ π x ξ := by
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := (isOptimal_iff hβ0 hβ1 hϑ hκ hu π x).1 h
      exact ⟨_, candD_foc hϑ u⟩
    · rintro ⟨ξ, hξ⟩
      exact isOptimal_of_foc hβ0.le hϑ hκ hf hl hξ
  exact ⟨h1, h1.trans (foc_iff_targeting hϑ.ne' π x)⟩

end Det

namespace Det

/-- **Galí (2015), (15), p. 136 (deterministic, general shock path)**: the commitment price-level
gap is `p̂_t = δ p̂_{t−1} + δ ∑_{k ≥ 0} (βδ)ᵏ u_{t+k}`, `p̂_{−1} = 0`. -/
theorem pHatD_eq (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    pHatD β κ ϑ u t = del β κ ϑ * lag (pHatD β κ ϑ u) t +
      del β κ ϑ * ∑' k, (β * del β κ ϑ) ^ k * u (t + k) := by
  rw [lag_pHatD]
  exact congrFun (pHat_eq perfectForesight β κ ϑ (lift u) t) ()

end Det

/-! ### The targeting rule pins down the commitment path -/

/-- **Galí (2015), (13)–(15), pp. 135–136**: the commitment path is the only bounded adapted
plan satisfying the Phillips curve and the targeting rule `x_t = −(κ/ϑ) p̂_t`,
`p̂_t = ∑_{s ≤ t} π_s`. -/
theorem targeting_unique {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hxa : 𝔼.Adapted x) (hxb : BoundedProc x)
    (ht : ∀ t, x t = (-(κ / ϑ)) • priceGap π t) :
    π = inflC 𝔼 β κ ϑ u ∧ x = gapC 𝔼 β κ ϑ u := by
  have hp : ∀ t, priceGap π t = (-(ϑ / κ)) • x t := fun t => by
    rw [ht t, smul_smul]
    have : -(ϑ / κ) * -(κ / ϑ) = 1 := by field_simp
    rw [this, one_smul]
  have hpa : 𝔼.Adapted (priceGap π) := fun t => by rw [hp t, map_smul, hxa t]
  have hpb : BoundedProc (priceGap π) := by
    obtain ⟨B, hB⟩ := hxb
    refine ⟨|ϑ / κ| * B, fun t ω => ?_⟩
    rw [hp t]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
  have hπ : inflOf (priceGap π) = π := funext fun t => priceGap_sub_lag π t
  have hx : gapOf κ ϑ (priceGap π) = x := funext fun t => (ht t).symm
  have hn' : NKPC 𝔼 β κ u (inflOf (priceGap π)) (gapOf κ ϑ (priceGap π)) := by
    rw [hπ, hx]; exact hn
  have heq := priceEq_unique 𝔼 hβ0 hβ1 hϑ hκ hu hua
    ((nkpc_iff_priceEq 𝔼 hβ0 hϑ hpa).1 hn') hpa hpb
  refine ⟨?_, ?_⟩
  · rw [← hπ, heq]; rfl
  · rw [← hx, heq]; rfl

/-! ### The iterated Phillips curve (p. 137) -/

/-- **Galí (2015), p. 137**: iterating (2) forward, in any bounded adapted plan with an AR(1)
cost-push shock,
`π_t = κ x_t + κ ∑_{k ≥ 1} βᵏ E_t x_{t+k} + u_t/(1 − βρ_u)`. -/
theorem iterated_nkpc {β κ ρ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u π x : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u)
    (hn : NKPC 𝔼 β κ u π x) (hπb : BoundedProc π) (hxa : 𝔼.Adapted x) (hxb : BoundedProc x)
    (t : ℕ) (ω : Ω) :
    π t ω = κ * x t ω + κ * ∑' k, β ^ (k + 1) * 𝔼.E t (x (t + (k + 1))) ω +
      (1 - β * ρ)⁻¹ * u t ω := by
  obtain ⟨B, hB⟩ := hxb
  set w : ℕ → Ω → ℝ := fun t => κ • x t + u t with hw
  have hwb : ∀ t ω, |w t ω| ≤ |κ| * B + M := fun t ω => by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hu t ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg κ)
  have hwa : 𝔼.Adapted w := fun t => by
    simp only [hw, map_add, map_smul, hxa t, har.1 t]
  have hπ : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + w t := fun t => by
    rw [hn t, hw, add_assoc]
  have hfs := 𝔼.eq_forwardSeries hβ0 hβ1 hwb hwa hπ hπb
  have hβρ : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg hβ0]
    calc β * |ρ| ≤ 1 * |ρ| := mul_le_mul_of_nonneg_right hβ1.le (abs_nonneg ρ)
      _ < 1 := by rw [one_mul]; exact hρ
  have hterm : ∀ k, β ^ k * 𝔼.E t (w (t + k)) ω =
      κ * (β ^ k * 𝔼.E t (x (t + k)) ω) + (β * ρ) ^ k * u t ω := fun k => by
    simp only [hw, map_add, map_smul, 𝔼.ar1_iterate har t k, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hs1 : Summable (fun k => β ^ k * 𝔼.E t (x (t + k)) ω) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB (t + k)) t ω) (pow_nonneg hβ0 k)
  have hs2 : Summable (fun k => (β * ρ) ^ k * u t ω) :=
    (summable_geometric_of_abs_lt_one hβρ).mul_right _
  rw [hfs]
  change ∑' k, β ^ k * 𝔼.E t (w (t + k)) ω = _
  rw [tsum_congr hterm, (hs1.mul_left κ).tsum_add hs2, tsum_mul_left, tsum_mul_right,
    tsum_geometric_of_abs_lt_one hβρ, hs1.tsum_eq_zero_add, pow_zero, one_mul, add_zero,
    hxa t]
  ring

/-! ### The interest-rate path with serially uncorrelated shocks (p. 138) -/

/-- Galí (2015), (7), p. 132: the dynamic IS equation in the welfare-relevant gap,
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^e_t)`. -/
def DIS (σ : ℝ) (re i π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (π (t + 1)) - re t)

/-- Galí (2015), p. 138: with `ρ_u = 0`, `E_t p̂_{t+1} = δ p̂_t` under commitment. -/
theorem E_pHat_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) (t : ℕ) :
    𝔼.E t (pHat 𝔼 β κ ϑ u (t + 1)) = del β κ ϑ • pHat 𝔼 β κ ϑ u t := by
  have h := pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har (t + 1)
  rw [lag_succ] at h
  rw [h, map_add, map_smul, map_smul, pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu har.1 t, har.2 t,
    zero_smul, smul_zero, add_zero]

/-- **Galí (2015), p. 138 (with C5-1)**: with `ρ_u = 0`, the commitment allocation satisfies the
dynamic IS equation iff the nominal rate is `i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) p̂_t` (the book prints
`α_x` for `ϑ`, a first-edition remnant). -/
theorem dis_iff_rate_rho0 {β κ ϑ σ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) (hσ : 0 < σ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u)
    (re i : ℕ → Ω → ℝ) :
    DIS 𝔼 σ re i (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ↔
      ∀ t, i t = re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t := by
  have hEp := E_pHat_rho0 𝔼 hβ0 hβ1 hϑ hκ hu har
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu har.1
  have hEx : ∀ t, 𝔼.E t (gapC 𝔼 β κ ϑ u (t + 1)) =
      (-(κ / ϑ) * del β κ ϑ) • pHat 𝔼 β κ ϑ u t := fun t => by
    change 𝔼.E t ((-(κ / ϑ)) • pHat 𝔼 β κ ϑ u (t + 1)) = _
    rw [map_smul, hEp, smul_smul]
  have hEπ : ∀ t, 𝔼.E t (inflC 𝔼 β κ ϑ u (t + 1)) =
      (del β κ ϑ - 1) • pHat 𝔼 β κ ϑ u t := fun t => by
    change 𝔼.E t (pHat 𝔼 β κ ϑ u (t + 1) - pHat 𝔼 β κ ϑ u t) = _
    rw [map_sub, hEp, hpa t, sub_smul, one_smul]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hEx, hEπ] at e
    simp only [gapC, gapOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    rw [hEx, hEπ, h t]
    simp only [gapC, gapOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- **Galí (2015), p. 138**: with `ρ_u = 0`, `p̂_t = ∑_{k=0}^{t} δ^{k+1} u_{t−k}`, so the
commitment nominal rate is `i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) ∑_{k=0}^{t} δ^{k+1} u_{t−k}`. -/
theorem pHat_rho0_sum {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ (k + 1) • u (t - k) := by
  have h := pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har
  simp only [mul_zero, sub_zero, div_one] at h
  induction t with
  | zero => rw [h 0]; simp
  | succ t ih =>
    rw [h (t + 1), lag_succ, ih, Finset.sum_range_succ' _ (t + 1), Finset.smul_sum]
    simp only [zero_add, pow_one, Nat.sub_zero, smul_smul, ← pow_succ']
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_add_right]

/-! ### The implementing rule with a price-level response (p. 138, footnote 6)

The deviations of any equilibrium under the rule from the commitment allocation solve the
system of Galí (2015), Exercise 4.6 (price-level rule, natural rate zero, `p̂_{−1} = 0`). The
algebra of that exercise (characteristic polynomial, reduction to a two-dimensional forward
system, Schur stability for `φ_p > 0`) is restated from the Chapter 4 project
(`MonetaryPolicyDesign/Ex4_6.lean`); the book's footnote 6 cites "exercise 4.5", which is the
first-edition numbering (C5-2). -/

namespace Rule

/-- Galí (2015), Ex. 4.6, p. 125: the characteristic polynomial
`P(λ) = σ (λ − 1)² (1 − βλ) − κ λ (1 + φ_p − λ)` of the equilibrium dynamics. -/
def charPoly (σ κ β φ r : ℝ) : ℝ := σ * (r - 1) ^ 2 * (1 - β * r) - κ * r * (1 + φ - r)

/-- Galí (2015), Ex. 4.6: the loading `c(λ) = −(1 − λ)(1 − βλ)/κ` of the output gap on the
lagged price level in the `λ`-mode. -/
noncomputable def loadY (κ β r : ℝ) : ℝ := -((1 - r) * (1 - β * r)) / κ

/-- Galí (2015), Ex. 4.6: the coefficient `e(λ) = σ c(λ) − φ_p − 1 + λ` of the reduced IS
equation. -/
noncomputable def eCoef (σ κ β φ r : ℝ) : ℝ := σ * loadY κ β r - φ - 1 + r

/-- Galí (2015), Ex. 4.6: the coefficient `1 + β − βλ` of the reduced Phillips curve. -/
def mCoef (β r : ℝ) : ℝ := 1 + β - β * r

/-- Galí (2015), Ex. 4.6: the forward matrix `A(λ)` of the reduced system
`(w_t, v_t) = A(λ) E_t (w_{t+1}, v_{t+1})`. -/
noncomputable def fwdA (σ κ β φ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r / σ * (σ * β + κ), r / σ * (κ * σ);
    r / σ * (eCoef σ κ β φ r * β + mCoef β r), r / σ * (mCoef β r * σ)]

/-- Galí (2015), Ex. 4.6: `κ c(λ) = −(1 − λ)(1 − βλ)`. -/
theorem loadY_mul {κ : ℝ} (hκ : κ ≠ 0) (β r : ℝ) :
    κ * loadY κ β r = -((1 - r) * (1 - β * r)) := by
  unfold loadY; field_simp

/-- Galí (2015), Ex. 4.6: `P(0) = σ`. -/
theorem charPoly_zero (σ κ β φ : ℝ) : charPoly σ κ β φ 0 = σ := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(1) = −κ φ_p`. -/
theorem charPoly_one (σ κ β φ : ℝ) : charPoly σ κ β φ 1 = -(κ * φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(−1) = 4σ(1 + β) + κ(2 + φ_p)`. -/
theorem charPoly_neg_one (σ κ β φ : ℝ) :
    charPoly σ κ β φ (-1) = 4 * σ * (1 + β) + κ * (2 + φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P` is continuous. -/
theorem continuous_charPoly (σ κ β φ : ℝ) : Continuous (charPoly σ κ β φ) := by
  unfold charPoly; fun_prop

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ c(λ)(1 − λ) + λ (1 + φ_p − λ) = 0`, the
coefficient of `p̂_{t−1}` in the reduced IS equation. -/
theorem is_coef_zero {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * loadY κ β r * (1 - r) + r * (1 + φ - r) = 0 := by
  have h := loadY_mul hκ β r
  apply mul_left_cancel₀ hκ
  unfold charPoly at hP
  linear_combination σ * (1 - r) * h - hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `λ (σ (1 + β − βλ) − κ e(λ)) = σ`; the
determinant of the reduced system's left-hand matrix is `σ/λ`. -/
theorem delta_eq {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    r * (σ * mCoef β r - κ * eCoef σ κ β φ r) = σ := by
  have h := loadY_mul hκ β r
  unfold eCoef mCoef
  unfold charPoly at hP
  linear_combination (-(r * σ)) * h - hP

/-! ### The reduction, pointwise -/

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the Phillips curve
`(1 + β) p̂_t − p̂_{t−1} = β E_t p̂_{t+1} + κ ỹ_t` holds iff
`(1 + β − βλ) w_t − κ v_t = β E_t w_{t+1}`, for any `λ`. -/
theorem pc_iff {κ β r : ℝ} (hκ : κ ≠ 0) (k p y Ep : ℝ) :
    (1 + β) * p - k = β * Ep + κ * y ↔
      mCoef β r * (p - r * k) - κ * (y - loadY κ β r * k) = β * (Ep - r * p) := by
  have h := loadY_mul hκ β r
  unfold mCoef
  constructor <;> intro e
  · linear_combination e + k * h
  · linear_combination e - k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): at a root `λ` of `P`, the IS equation
`σ ỹ_t = σ E_t ỹ_{t+1} − ((φ_p + 1) p̂_t − E_t p̂_{t+1})` holds iff
`σ v_t = σ E_t v_{t+1} + e(λ) w_t + E_t w_{t+1}`. -/
theorem is_iff {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) (k p y Ep Ey : ℝ) :
    σ * y = σ * Ey - ((φ + 1) * p - Ep) ↔
      σ * (y - loadY κ β r * k) =
        σ * (Ey - loadY κ β r * p) + eCoef σ κ β φ r * (p - r * k) + (Ep - r * p) := by
  have h := is_coef_zero hκ hP
  unfold eCoef
  constructor <;> intro e
  · linear_combination e - k * h
  · linear_combination e + k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the reduced Phillips curve and IS equation give
the forward form `(w, v) = A(λ) (E w', E v')`. -/
theorem fwd_of {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0)
    {w v Ew Ev : ℝ} (h1 : mCoef β r * w - κ * v = β * Ew)
    (h2 : σ * v = σ * Ev + eCoef σ κ β φ r * w + Ew) :
    w = r / σ * (σ * β + κ) * Ew + r / σ * (κ * σ) * Ev ∧
      v = r / σ * (eCoef σ κ β φ r * β + mCoef β r) * Ew + r / σ * (mCoef β r * σ) * Ev := by
  have hΔ := delta_eq hκ hP
  constructor
  · field_simp
    linear_combination r * (σ * h1 + κ * h2) - w * hΔ
  · field_simp
    linear_combination r * (mCoef β r * h2 + eCoef σ κ β φ r * h1) - v * hΔ

/-! ### The forward matrix: determinant, trace and Schur stability -/

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `det A(λ) = βλ`. -/
theorem det2_fwdA {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    det2 (fwdA σ κ β φ r) = β * r := by
  have hΔ := delta_eq hκ hP
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hΔ
    exact hσ hΔ.symm
  have hm : σ * mCoef β r - κ * eCoef σ κ β φ r = σ / r := by
    rw [eq_div_iff hr]; linarith
  calc det2 (fwdA σ κ β φ r)
      = (r / σ) ^ 2 * σ * β * (σ * mCoef β r - κ * eCoef σ κ β φ r) := by
        simp only [det2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        ring
    _ = β * r := by rw [hm]; field_simp

/-- Galí (2015), Ex. 4.6: `tr A(λ) = λ (σβ + κ + σ(1 + β − βλ))/σ`. -/
theorem tr2_fwdA (σ κ β φ r : ℝ) :
    tr2 (fwdA σ κ β φ r) = r / σ * (σ * β + κ) + r / σ * (mCoef β r * σ) := by
  simp only [tr2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 − λ)(1 − tr A + det A) = κ φ_p λ`. -/
theorem key_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) = κ * φ * r := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  unfold charPoly at hP
  field_simp
  linear_combination hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 + λ)(1 + tr A + det A) = λ P(−1)`. -/
theorem key_neg_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) =
      r * charPoly σ κ β φ (-1) := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  have hP' := hP
  unfold charPoly at hP' ⊢
  field_simp
  linear_combination hP'

/-- Galí (2015), Ex. 4.6: if `λ` is a root of `P` with `|λ| < 1`, `φ_p λ > 0` and
`λ P(−1) > 0`, the forward matrix `A(λ)` is Schur stable (both eigenvalues inside the unit
circle). -/
theorem schur_fwdA {σ κ β φ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hP : charPoly σ κ β φ r = 0) (hr : |r| < 1) (h1 : 0 < φ * r)
    (h2 : 0 < r * charPoly σ κ β φ (-1)) :
    SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r)) := by
  have k1 := key_one hσ.ne' hκ.ne' hP
  have k2 := key_neg_one hσ.ne' hκ.ne' hP
  rw [det2_fwdA hσ.ne' hκ.ne' hP] at k1 k2 ⊢
  obtain ⟨hr0, hr1⟩ := abs_lt.1 hr
  have hpos1 : 0 < σ * (1 - r) := mul_pos hσ (by linarith)
  have hpos2 : 0 < σ * (1 + r) := mul_pos hσ (by linarith)
  have e1 : 0 < 1 - tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + β * r) := by
      rw [k1]; nlinarith
    exact pos_of_mul_pos_right this hpos1.le
  have e2 : 0 < 1 + tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + β * r) := by rw [k2]; exact h2
    exact pos_of_mul_pos_right this hpos2.le
  refine ⟨?_, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  rw [abs_mul, abs_of_pos hβ0]
  nlinarith [abs_nonneg r]


/-- Galí (2015), Ex. 4.6: for `φ_p > 0` the polynomial has a root in `(0, 1)` (`P(0) = σ > 0`,
`P(1) = −κφ_p < 0`). -/
theorem exists_root_pos {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ) :
    ∃ r, 0 < r ∧ r < 1 ∧ charPoly σ κ β φ r = 0 := by
  have h := intermediate_value_Ioo' (zero_le_one' ℝ)
    (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ 1) (charPoly σ κ β φ 0) by
      rw [charPoly_one, charPoly_zero]; exact ⟨by nlinarith, hσ⟩)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), p. 138: the stacked vector `(a_t, b_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- **Galí (2015), p. 138 and Ex. 4.6 (uniqueness of the zero deviation)**: for `φ_p > 0`, the
only bounded adapted solution of the deviation system
`σ y_t = σ E_t y_{t+1} − ((φ_p + 1) q_t − E_t q_{t+1})`,
`(1 + β) q_t − q_{t−1} = β E_t q_{t+1} + κ y_t`, `q_{−1} = 0`, is zero. -/
theorem dev_zero {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 < φ) {y q : ℕ → Ω → ℝ} (hya : 𝔼.Adapted y) (hqa : 𝔼.Adapted q)
    (hyb : BoundedProc y) (hqb : BoundedProc q)
    (he : ∀ t ω, σ * y t ω = σ * 𝔼.E t (y (t + 1)) ω - ((φ + 1) * q t ω - 𝔼.E t (q (t + 1)) ω) ∧
      (1 + β) * q t ω - lag q t ω = β * 𝔼.E t (q (t + 1)) ω + κ * y t ω) :
    y = 0 ∧ q = 0 := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_pos (β := β) hσ hκ hφ
  have hP1 : 0 < charPoly σ κ β φ (-1) := by rw [charPoly_neg_one]; positivity
  have hr : |r| < 1 := abs_lt.2 ⟨by linarith, hr1⟩
  have hA := schur_fwdA hσ hκ hβ0 hβ1 hP hr (mul_pos hφ hr0) (mul_pos hr0 hP1)
  have hla := lag_adapted 𝔼 hqa
  set X : ℕ → Fin 2 → Ω → ℝ :=
    stack (fun t => q t - r • lag q t) (fun t => y t - loadY κ β r • lag q t) with hX
  have hs : 𝔼.Solves (fwdA σ κ β φ r) 0 X := by
    intro t j
    funext ω
    obtain ⟨e1, e2⟩ := he t ω
    have h1 := (pc_iff (r := r) hκ.ne' _ _ _ _).1 e2
    have h2 := (is_iff (k := lag q t ω) hκ.ne' hP _ _ _ _).1 e1
    have hfw := fwd_of hσ.ne' hκ.ne' hP h1 h2
    have hEw : 𝔼.E t (q (t + 1) - r • q t) ω = 𝔼.E t (q (t + 1)) ω - r * q t ω := by
      rw [map_sub, map_smul, hqa t]; rfl
    have hEv : 𝔼.E t (y (t + 1) - loadY κ β r • q t) ω =
        𝔼.E t (y (t + 1)) ω - loadY κ β r * q t ω := by
      rw [map_sub, map_smul, hqa t]; rfl
    fin_cases j
    · simp only [hX, stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, lag_succ]
      rw [hEw, hEv]
      simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hfw.1
    · simp only [hX, stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Pi.zero_apply, add_zero, lag_succ]
      rw [hEw, hEv]
      simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hfw.2
  have hav : 𝔼.AdaptedVec X := by
    intro t j
    fin_cases j
    · change 𝔼.E t (q t - r • lag q t) = q t - r • lag q t
      rw [map_sub, map_smul, hqa t, hla t]
    · change 𝔼.E t (y t - loadY κ β r • lag q t) = y t - loadY κ β r • lag q t
      rw [map_sub, map_smul, hya t, hla t]
  obtain ⟨My, hMy⟩ := hyb
  obtain ⟨Mq, hMq⟩ := hqb
  have hbv : BoundedVec X := by
    refine ⟨Mq + |r| * Mq + My + |loadY κ β r| * Mq, fun t j ω => ?_⟩
    have hMq0 : 0 ≤ Mq := (abs_nonneg _).trans (hMq 0 ω)
    have hlb : |lag q t ω| ≤ Mq := by
      cases t with
      | zero => simpa using hMq0
      | succ t => exact hMq t ω
    have h1 := abs_nonneg (q t ω)
    have h2 := abs_nonneg (y t ω)
    have h3 : |r * lag q t ω| ≤ |r| * Mq := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlb (abs_nonneg r)
    have h4 : |loadY κ β r * lag q t ω| ≤ |loadY κ β r| * Mq := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlb (abs_nonneg _)
    have h5 := abs_nonneg (r * lag q t ω)
    have h6 := abs_nonneg (loadY κ β r * lag q t ω)
    fin_cases j
    · change |q t ω - r * lag q t ω| ≤ _
      linarith [abs_sub (q t ω) (r * lag q t ω), hMq t ω, hMy t ω]
    · change |y t ω - loadY κ β r * lag q t ω| ≤ _
      linarith [abs_sub (y t ω) (loadY κ β r * lag q t ω), hMq t ω, hMy t ω]
  have h0 : 𝔼.Solves (fwdA σ κ β φ r) 0 0 := fun t j => by simp
  have heq := 𝔼.system_unique hA hs h0 hav (fun t j => map_zero _) hbv ⟨0, fun t j ω => by simp⟩
  have hw : ∀ t, q t = r • lag q t := fun t => by
    have := congrFun (congrFun heq t) 0
    simp only [hX, stack, Matrix.cons_val_zero, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hv : ∀ t, y t = loadY κ β r • lag q t := fun t => by
    have := congrFun (congrFun heq t) 1
    simp only [hX, stack, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hq0 : ∀ t, q t = 0 := by
    intro t
    induction t with
    | zero => rw [hw 0]; simp
    | succ t ih => rw [hw (t + 1), lag_succ, ih, smul_zero]
  refine ⟨funext fun t => ?_, funext hq0⟩
  rw [hv t]
  cases t with
  | zero => simp
  | succ t => rw [lag_succ, hq0 t, smul_zero]; rfl

end Rule

/-- Galí (2015), p. 138 (with C5-1): the implementing rule
`i_t = r^e_t − (φ_p + (1 − δ)(1 − σκ/ϑ)) ∑_{k=0}^{t} δ^{k+1} u_{t−k} + φ_p p̂_t`. -/
noncomputable def ruleRate (β κ ϑ σ φ : ℝ) (re u p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  re t - (φ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ)) •
    ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ (k + 1) • u (t - k) + φ • p t

/-- Galí (2015), p. 138: an equilibrium under the implementing rule, given `p̂_{−1} = 0`: the
dynamic IS equation (7), the Phillips curve (2) with `π_t = p̂_t − p̂_{t−1}`, and the rule. -/
def RuleEq (β κ ϑ σ φ : ℝ) (re u x p i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ re i (inflOf p) x ∧ NKPC 𝔼 β κ u (inflOf p) x ∧ ∀ t, i t = ruleRate β κ ϑ σ φ re u p t

/-- Galí (2015), (7), p. 132 (pointwise algebra): `x = E x' − σ⁻¹ (i − E π' − r)` iff
`σ x = σ E x' − (i − E π' − r)`. -/
theorem dis_pointwise {σ : ℝ} (hσ : σ ≠ 0) (X EX I EP R : ℝ) :
    X = EX - σ⁻¹ * (I - EP - R) ↔ σ * X = σ * EX - (I - EP - R) := by
  constructor <;> intro h
  · rw [h]; field_simp
  · field_simp; linarith

/-- **Galí (2015), p. 138 (the implementing rule)**: with `ρ_u = 0` and any `φ_p > 0`, the rule
`i_t = r^e_t − (φ_p + (1 − δ)(1 − σκ/ϑ)) ∑_{k=0}^{t} δ^{k+1} u_{t−k} + φ_p p̂_t` (with `ϑ` in
place of the book's `α_x`, C5-1) supports the commitment allocation as an equilibrium, along which
`i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) p̂_t`, and it is the unique bounded adapted equilibrium. -/
theorem rule_implements {β κ ϑ σ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : 0 < κ) (hσ : 0 < σ) (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (har : 𝔼.IsAR1 0 u) (re : ℕ → Ω → ℝ) :
    (RuleEq 𝔼 β κ ϑ σ φ re u (gapC 𝔼 β κ ϑ u) (pHat 𝔼 β κ ϑ u)
        (ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u)) ∧
      ∀ t, ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) t =
        re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t) ∧
    ∀ x p i, RuleEq 𝔼 β κ ϑ σ φ re u x p i → 𝔼.Adapted x → 𝔼.Adapted p → BoundedProc x →
      BoundedProc p →
        x = gapC 𝔼 β κ ϑ u ∧ p = pHat 𝔼 β κ ϑ u ∧
          i = ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) := by
  have hκ' := hκ.ne'
  have hrate : ∀ t, ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) t =
      re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t := fun t => by
    rw [ruleRate, ← pHat_rho0_sum 𝔼 hβ0 hβ1 hϑ hκ' hu har t, add_smul]
    abel
  have hdis := (dis_iff_rate_rho0 𝔼 hβ0 hβ1 hϑ hκ' hσ hu har re
    (ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u))).2 hrate
  have hnk := cand_nkpc 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  obtain ⟨-, hga, -, hgb⟩ := cand_adapted_bounded 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  refine ⟨⟨⟨hdis, hnk, fun t => rfl⟩, hrate⟩, fun x p i he hxa hpa' hxb hpb => ?_⟩
  obtain ⟨hd, hn, hi⟩ := he
  have hEi : ∀ (q : ℕ → Ω → ℝ), 𝔼.Adapted q → ∀ t,
      𝔼.E t (inflOf q (t + 1)) = 𝔼.E t (q (t + 1)) - q t := fun q hq t => by
    change 𝔼.E t (q (t + 1) - q t) = _
    rw [map_sub, hq t]
  have hlagsub : ∀ t ω, lag (fun s => p s - pHat 𝔼 β κ ϑ u s) t ω =
      lag p t ω - lag (pHat 𝔼 β κ ϑ u) t ω := fun t ω => by
    cases t <;> simp
  obtain ⟨Bx, hBx⟩ := hxb
  obtain ⟨Bg, hBg⟩ := hgb
  obtain ⟨Bp, hBp⟩ := hpb
  obtain ⟨Bs, hBs⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ' hu
  have hdev := Rule.dev_zero 𝔼 (y := fun t => x t - gapC 𝔼 β κ ϑ u t)
    (q := fun t => p t - pHat 𝔼 β κ ϑ u t) hσ hκ hβ0 hβ1 hφ
    (fun t => by simp only [map_sub, hxa t, hga t])
    (fun t => by simp only [map_sub, hpa' t, hpa t])
    ⟨Bx + Bg, fun t ω => (abs_sub _ _).trans (add_le_add (hBx t ω) (hBg t ω))⟩
    ⟨Bp + Bs, fun t ω => (abs_sub _ _).trans (add_le_add (hBp t ω) (hBs t ω))⟩
    (fun t ω => ?_)
  · obtain ⟨hx0, hp0⟩ := hdev
    have hx : x = gapC 𝔼 β κ ϑ u := funext fun t => sub_eq_zero.1 (congrFun hx0 t)
    have hp : p = pHat 𝔼 β κ ϑ u := funext fun t => sub_eq_zero.1 (congrFun hp0 t)
    refine ⟨hx, hp, funext fun t => ?_⟩
    rw [hi t, hp]
  · have e1 := congrFun (hd t) ω
    have e1s := congrFun (hdis t) ω
    have e2 := congrFun (hn t) ω
    have e2s := congrFun (hnk t) ω
    have e3 := congrFun (hi t) ω
    rw [hEi p hpa' t] at e1 e2
    simp only [inflC] at e1s e2s
    rw [hEi _ hpa t] at e1s e2s
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inflOf] at e1 e1s e2 e2s
    rw [dis_pointwise hσ.ne'] at e1 e1s
    simp only [map_sub, Pi.sub_apply, hlagsub, ruleRate, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e3 e1s ⊢
    constructor
    · linear_combination e1 - e1s - e3
    · linear_combination e2 - e2s

end Gali.DiscretionCommitment.Commitment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Commitment versus discretion

Galí (2015), Section 5.2, pp. 130–137. Under discretion the central bank follows the targeting
rule `x_t = −(κ/ϑ) π_t` ((4), p. 130), and with an AR(1) cost-push shock the (minimal state
variable) equilibrium is `π_t = ϑ/(κ² + ϑ(1 − βρ_u)) u_t`, `x_t = −κ/(κ² + ϑ(1 − βρ_u)) u_t`
((5)–(6), p. 130). This module compares it with the optimal policy under commitment of the module
`Commitment`.

## Main results

* `disc_nkpc`, `disc_targeting`, `disc_unique`: the discretionary path solves the Phillips curve,
  satisfies (4), and is the unique bounded adapted plan doing so.
* `commitment_le_discretion` (p. 137): commitment weakly beats discretion, state by state,
  because the discretionary plan is feasible for the commitment problem;
  `commitment_lt_discretion`: strictly wherever `u_0 ≠ 0`.
* `del_lt_disc_coef`: `δ < ϑ/(ϑ + κ²)`, the source of the stabilisation gain.
* `impact_inflation`, `impact_gap` (p. 137): for every `|ρ_u| < 1`, commitment lowers the impact
  response of inflation and of the absolute output gap; `impact_rho0` gives the closed forms for
  `ρ_u = 0`: `π_0 = δ u_0` vs `ϑ/(κ² + ϑ) u_0` and `x_0 = −(κδ/ϑ) u_0` vs `−κ/(κ² + ϑ) u_0`.
* `impulse_rho0` (p. 136): after a one-time shock, commitment keeps the price level, inflation and
  the output gap away from zero for ever (`p̂_t = δ^{t+1} u_0`), while under discretion inflation
  and the output gap return to zero one period after the shock.
-/

namespace Gali.DiscretionCommitment.CommitmentVsDiscretion

open Gali.DiscretionCommitment.Commitment

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The discretionary equilibrium -/

/-- Galí (2015), (5), p. 130: the discretionary inflation coefficient
`ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiPi (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), (6), p. 130: the discretionary output-gap coefficient
`−κ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), (5), p. 130: discretionary inflation `π_t = ϑ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def inflDisc (β κ ϑ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  psiPi β κ ϑ ρ • u t

/-- Galí (2015), (6), p. 130: the discretionary output gap `x_t = −κ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def gapDisc (β κ ϑ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  psiX β κ ϑ ρ • u t

/-- Galí (2015), (5)–(6), p. 130: `1 − βρ_u > 0` for `|ρ_u| < 1`, so the discretionary
denominator `κ² + ϑ(1 − βρ_u)` is positive. -/
theorem denom_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) :
    0 < 1 - β * ρ ∧ 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
  have h1 : β * ρ < 1 := by
    have := le_abs_self ρ
    have : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left this hβ0.le
    have : β * |ρ| < 1 := by nlinarith [abs_nonneg ρ]
    linarith
  have h2 : 0 < 1 - β * ρ := by linarith
  exact ⟨h2, by positivity⟩

/-- Galí (2015), (4), p. 130: the discretionary path satisfies the targeting rule
`x_t = −(κ/ϑ) π_t`. -/
theorem disc_targeting {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    gapDisc β κ ϑ ρ u t = (-(κ / ϑ)) • inflDisc β κ ϑ ρ u t := by
  rw [gapDisc, inflDisc, smul_smul, psiX, psiPi]
  congr 1
  field_simp

/-- Galí (2015), (5)–(6), p. 130: the discretionary path solves the Phillips curve (2) with an
AR(1) cost-push shock. -/
theorem disc_nkpc {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (har : 𝔼.IsAR1 ρ u) :
    NKPC 𝔼 β κ u (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) := by
  obtain ⟨-, hD⟩ := denom_pos (κ := κ) hβ0 hβ1 hϑ hρ
  intro t
  funext ω
  simp only [inflDisc, gapDisc, map_smul, har.2 t, smul_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [psiPi, psiX]
  field_simp
  ring

/-- Galí (2015), (5)–(6), p. 130: the discretionary path is a bounded adapted plan. -/
theorem disc_plan {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    Plan 𝔼 β κ u (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) := by
  refine ⟨disc_nkpc 𝔼 hβ0 hβ1 hϑ hρ har, fun t => ?_, fun t => ?_, ⟨|psiPi β κ ϑ ρ| * M,
    fun t ω => ?_⟩, ⟨|psiX β κ ϑ ρ| * M, fun t ω => ?_⟩⟩
  · simp only [inflDisc, map_smul, har.1 t]
  · simp only [gapDisc, map_smul, har.1 t]
  · simp only [inflDisc, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg _)
  · simp only [gapDisc, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg _)

/-- **Galí (2015), (5)–(6), p. 130**: the discretionary path is the only bounded adapted plan
that satisfies the Phillips curve and the discretionary targeting rule (4)
(`π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (ϑ/(ϑ + κ²)) u_t` has a unique bounded solution). -/
theorem disc_unique {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) {π x : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hπb : BoundedProc π)
    (ht : ∀ t, x t = (-(κ / ϑ)) • π t) :
    π = inflDisc β κ ϑ ρ u ∧ x = gapDisc β κ ϑ ρ u := by
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ / (ϑ + κ ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hD]; nlinarith [sq_nonneg κ]
  have hab : |a * β| < 1 := by
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hred : ∀ (p : ℕ → Ω → ℝ), NKPC 𝔼 β κ u p (fun t => (-(κ / ϑ)) • p t) →
      ∀ t, p t = (a * β) • 𝔼.E t (p (t + 1)) + a • u t := fun p hp t => by
    funext ω
    have e := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [ha]
    field_simp at e ⊢
    linarith
  have hx : x = fun t => (-(κ / ϑ)) • π t := funext ht
  have hdisc : NKPC 𝔼 β κ u (inflDisc β κ ϑ ρ u) (fun t => (-(κ / ϑ)) • inflDisc β κ ϑ ρ u t) := by
    have := disc_nkpc (κ := κ) 𝔼 hβ0 hβ1 hϑ hρ har
    intro t
    rw [this t, disc_targeting hϑ u t]
  obtain ⟨-, -, -, hdb, -⟩ := disc_plan (κ := κ) 𝔼 hβ0 hβ1 hϑ hρ hu har
  have heq := 𝔼.forward_unique hab (hred π (hx ▸ hn)) (hred _ hdisc) hπb hdb
  refine ⟨heq, ?_⟩
  rw [hx, heq]
  funext t
  exact (disc_targeting hϑ u t).symm

/-! ### The stabilisation gain: `δ < ϑ/(ϑ + κ²)` -/

/-- **Galí (2015), p. 137 (key inequality)**: for `κ ≠ 0`, `δ < ϑ/(ϑ + κ²)`. The characteristic
polynomial `γβz² − z + γ` equals `γβa(a − 1) < 0` at `a = ϑ/(ϑ + κ²)`, so `a` lies strictly between
its roots `δ` and `1/(βδ)`. -/
theorem del_lt_disc_coef {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    del β κ ϑ < ϑ / (ϑ + κ ^ 2) := by
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ / (ϑ + κ ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one hD]; linarith
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hval : gam β κ ϑ * β * a ^ 2 - a + gam β κ ϑ = gam β κ ϑ * β * a * (a - 1) := by
    rw [ha, gam]
    have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
    field_simp
    ring
  rw [quad_factor hβ0 hβ1 hϑ a] at hval
  have hd := del_pos (κ := κ) hβ0 hϑ
  obtain ⟨-, hroot⟩ := quad_roots hβ0 hβ1 hϑ hκ
  have hneg : gam β κ ϑ * β * a * (a - 1) < 0 := by
    have : 0 < gam β κ ϑ * β * a := by positivity
    nlinarith
  have h2 : a - 1 / (β * del β κ ϑ) < 0 := by linarith
  have hgb : 0 < gam β κ ϑ * β := by positivity
  by_contra hc
  push Not at hc
  have h3 : 0 ≤ (a - del β κ ϑ) * (a - 1 / (β * del β κ ϑ)) := by nlinarith
  nlinarith [mul_nonneg hgb.le h3]

/-- Galí (2015), p. 137: the commitment impact coefficient of inflation is below the
discretionary one, `δ/(1 − δβρ_u) < ϑ/(κ² + ϑ(1 − βρ_u))`, for every `|ρ_u| < 1`. -/
theorem commit_coef_lt {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) :
    0 < del β κ ϑ / (1 - del β κ ϑ * β * ρ) ∧
      del β κ ϑ / (1 - del β κ ϑ * β * ρ) < psiPi β κ ϑ ρ := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have h1 := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  obtain ⟨-, hD⟩ := denom_pos (κ := κ) hβ0 hβ1 hϑ hρ
  have hlt := del_lt_disc_coef hβ0 hβ1 hϑ hκ
  refine ⟨div_pos hd h1, ?_⟩
  rw [psiPi, div_lt_div_iff₀ h1 hD]
  rw [lt_div_iff₀ (by positivity)] at hlt
  nlinarith

/-! ### Welfare: commitment beats discretion -/

/-- **Galí (2015), p. 137 (welfare ranking)**: with an AR(1) cost-push shock, the expected loss
under commitment is no larger than under discretion, state by state, since the discretionary plan
is feasible for the commitment problem. -/
theorem commitment_le_discretion (hpo : PullOut 𝔼) {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω ≤
      expLoss 𝔼 β ϑ (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) ω :=
  ((commitment_optimal 𝔼 hpo hβ0 hβ1 hϑ hκ hu har.1).2 _ _
    (disc_plan 𝔼 hβ0 hβ1 hϑ hρ hu har) ω).1

/-- Galí (2015), (15), p. 136: commitment inflation on impact is `π_0 = δ/(1 − δβρ_u) u_0`. -/
theorem inflC_zero {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    inflC 𝔼 β κ ϑ u 0 = (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u 0 := by
  change pHat 𝔼 β κ ϑ u 0 - lag (pHat 𝔼 β κ ϑ u) 0 = _
  rw [pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har 0]
  simp

/-- **Galí (2015), p. 137 (strict welfare gain)**: wherever the initial cost-push shock is
nonzero, commitment yields a strictly lower expected loss than discretion. -/
theorem commitment_lt_discretion (hpo : PullOut 𝔼) {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) (hu0 : u 0 ω ≠ 0) :
    expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω <
      expLoss 𝔼 β ϑ (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) ω := by
  obtain ⟨hplan, hopt⟩ := commitment_optimal 𝔼 hpo hβ0 hβ1 hϑ hκ hu har.1
  obtain ⟨hle, heq⟩ := hopt _ _ (disc_plan 𝔼 hβ0 hβ1 hϑ hρ hu har) ω
  refine lt_of_le_of_ne hle fun h => ?_
  have h0 := (heq h.symm 0).1
  set c := psiPi β κ ϑ ρ - del β κ ϑ / (1 - del β κ ϑ * β * ρ) with hc
  have hc0 : c ≠ 0 := by
    have := (commit_coef_lt hβ0 hβ1 hϑ hκ hρ).2
    rw [hc]; linarith
  have hfun : (fun ω => (inflDisc β κ ϑ ρ u 0 ω - inflC 𝔼 β κ ϑ u 0 ω) ^ 2) =
      c ^ 2 • (u 0 * u 0) := by
    funext ω'
    rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]
    simp only [inflDisc, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hc]
    ring
  rw [hfun, map_smul, hpo 0 _ _ (har.1 0), har.1 0] at h0
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_eq_zero, pow_eq_zero_iff',
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true, or_self] at h0
  rcases h0 with h0 | h0
  · exact hc0 h0
  · exact hu0 h0

/-! ### Impact responses (p. 137) -/

/-- **Galí (2015), p. 137**: on impact, inflation is closer to zero under commitment than under
discretion, `|π_0^C| ≤ |π_0^D|`, strictly when `u_0 ≠ 0`, for every `|ρ_u| < 1`. -/
theorem impact_inflation {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    |inflC 𝔼 β κ ϑ u 0 ω| ≤ |inflDisc β κ ϑ ρ u 0 ω| ∧
      (u 0 ω ≠ 0 → |inflC 𝔼 β κ ϑ u 0 ω| < |inflDisc β κ ϑ ρ u 0 ω|) := by
  obtain ⟨h0, h1⟩ := commit_coef_lt hβ0 hβ1 hϑ hκ hρ
  rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]
  simp only [inflDisc, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h0,
    abs_of_pos (h0.trans h1)]
  refine ⟨mul_le_mul_of_nonneg_right h1.le (abs_nonneg _), fun hu0 => ?_⟩
  exact mul_lt_mul_of_pos_right h1 (abs_pos.2 hu0)

/-- **Galí (2015), p. 137**: on impact, the output gap is smaller in absolute value under
commitment than under discretion, `|x_0^C| ≤ |x_0^D|`, strictly when `u_0 ≠ 0`. -/
theorem impact_gap {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    |gapC 𝔼 β κ ϑ u 0 ω| ≤ |gapDisc β κ ϑ ρ u 0 ω| ∧
      (u 0 ω ≠ 0 → |gapC 𝔼 β κ ϑ u 0 ω| < |gapDisc β κ ϑ ρ u 0 ω|) := by
  have hC : gapC 𝔼 β κ ϑ u 0 ω = -(κ / ϑ) * inflC 𝔼 β κ ϑ u 0 ω := by
    change -(κ / ϑ) * pHat 𝔼 β κ ϑ u 0 ω =
      -(κ / ϑ) * (pHat 𝔼 β κ ϑ u 0 ω - lag (pHat 𝔼 β κ ϑ u) 0 ω)
    simp
  have hD : gapDisc β κ ϑ ρ u 0 ω = -(κ / ϑ) * inflDisc β κ ϑ ρ u 0 ω := by
    rw [disc_targeting hϑ u 0]; rfl
  obtain ⟨h1, h2⟩ := impact_inflation 𝔼 hβ0 hβ1 hϑ hκ hρ hu har ω
  have hk : 0 < |κ / ϑ| := abs_pos.2 (div_ne_zero hκ hϑ.ne')
  rw [hC, hD, abs_mul, abs_mul, abs_neg]
  exact ⟨mul_le_mul_of_nonneg_left h1 hk.le, fun hu0 => mul_lt_mul_of_pos_left (h2 hu0) hk⟩

/-- **Galí (2015), p. 137 (closed forms for `ρ_u = 0`)**: on impact, `π_0 = δ u_0` and
`x_0 = −(κδ/ϑ) u_0` under commitment, against `π_0 = ϑ/(κ² + ϑ) u_0` and
`x_0 = −κ/(κ² + ϑ) u_0` under discretion, with `δ < ϑ/(κ² + ϑ)`. -/
theorem impact_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) :
    inflC 𝔼 β κ ϑ u 0 = del β κ ϑ • u 0 ∧
      gapC 𝔼 β κ ϑ u 0 = (-(κ * del β κ ϑ / ϑ)) • u 0 ∧
      inflDisc β κ ϑ 0 u 0 = (ϑ / (κ ^ 2 + ϑ)) • u 0 ∧
      gapDisc β κ ϑ 0 u 0 = (-κ / (κ ^ 2 + ϑ)) • u 0 ∧
      del β κ ϑ < ϑ / (κ ^ 2 + ϑ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har]; simp
  · rw [gapC_zero 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har]; simp
  · simp [inflDisc, psiPi]
  · simp [gapDisc, psiX]
  · rw [add_comm]; exact del_lt_disc_coef hβ0 hβ1 hϑ hκ

/-! ### Persistence after a one-time shock (p. 136) -/

/-- **Galí (2015), p. 136 (Figure 5.1, transitory shock)**: if `u_0` is the only shock
(`ρ_u = 0`, `u_t = 0` for `t ≥ 1`), then under commitment `p̂_t = δ^{t+1} u_0`,
`π_{t+1} = −(1 − δ) δ^{t+1} u_0` and `x_t = −(κ/ϑ) δ^{t+1} u_0` (deviations persist, decaying
geometrically, and the price level returns to its initial level), while under discretion
`π_{t+1} = x_{t+1} = 0`. -/
theorem impulse_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u)
    (himp : ∀ t, u (t + 1) = 0) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ ^ (t + 1) • u 0 ∧
      inflC 𝔼 β κ ϑ u (t + 1) = (-((1 - del β κ ϑ) * del β κ ϑ ^ (t + 1))) • u 0 ∧
      gapC 𝔼 β κ ϑ u t = (-(κ / ϑ) * del β κ ϑ ^ (t + 1)) • u 0 ∧
      inflDisc β κ ϑ 0 u (t + 1) = 0 ∧ gapDisc β κ ϑ 0 u (t + 1) = 0 := by
  have hp : ∀ s, pHat 𝔼 β κ ϑ u s = del β κ ϑ ^ (s + 1) • u 0 := by
    intro s
    rw [pHat_rho0_sum 𝔼 hβ0 hβ1 hϑ hκ hu har s, Finset.sum_eq_single s]
    · simp
    · intro k hk hks
      have : s - k = (s - k - 1) + 1 := by
        have := Finset.mem_range.1 hk
        omega
      rw [this, himp, smul_zero]
    · intro h; exact absurd (Finset.self_mem_range_succ s) h
  refine ⟨hp t, ?_, ?_, ?_, ?_⟩
  · change pHat 𝔼 β κ ϑ u (t + 1) - pHat 𝔼 β κ ϑ u t = _
    rw [hp, hp, ← sub_smul]
    congr 1
    ring
  · change (-(κ / ϑ)) • pHat 𝔼 β κ ϑ u t = _
    rw [hp, smul_smul]
  · simp [inflDisc, himp]
  · simp [gapDisc, himp]

end Gali.DiscretionCommitment.CommitmentVsDiscretion

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy with a distorted steady state

Galí (2015), Section 5.3, pp. 139–144.

When the zero-inflation steady state is inefficient (distortion `Φ > 0`), the policy-relevant
welfare loss acquires a linear term `−Λ x̂_t`, `Λ = Φ λ / ε` (eq. (17)), and the Phillips curve
is written in the gap `x̂_t` from its steady-state value (eq. (18)).

## Main results

* `loss_rescale`, `nkpc_in_xhat`: the loss (17) and the Phillips curve (18) from the
  Appendix 5.1 welfare expression and the Phillips curve in the output gap.
* `discretion_period_optimal_iff`: (19) is necessary and sufficient for the per-period
  problem under discretion.
* `discretion_exists`, `discretion_unique`: (20) and the `x̂` formula give the unique bounded
  equilibrium under discretion; `inflationBias_pos`, `strictMono_inflationBias`,
  `strictMono_inflationBias_Phi`: the inflation bias is positive and increasing in `Λ` and `Φ`.
* `γ`, `δ` and their lemmas (`del_pos`, `del_lt_one_iff`, `kappa_sq_del`:
  `κ² δ / ϑ = (1 − δ)(1 − β δ)`) are imported from `Commitment`; `gam_lt_one` is added here.
* `commitment_eq21`, `commitment_eq22`, `commitment_exists`, `commitment_unique`,
  `commitment_eq23`, `commitment_eq24`: commitment with distortion, (21)–(24).
* `commitment_eq25`, `commitment_eq26_corrected`, `commitment_eq27_corrected`: the output gap.
  The book's (26)–(27) deterministic term `(1 − δ) Λ / ϑ` is wrong (`printed_eq26_false`); the
  correct term is `δ^{t+1} Λ / ϑ`.
* `tendsto_priceLevel_zeroShock`, `tendsto_gap_zeroShock`, `tendsto_infl_zeroShock`: no
  long-run inflation bias under commitment.
* `lagrangian_identity`, `lagrangian_sufficiency`, `det_optimal_iff`, `det_commitment_optimal`:
  in the deterministic problem, the Lagrangian conditions are necessary and sufficient for
  optimality among bounded paths, and the optimum exists and is unique for every bounded
  cost-push sequence; `det_zeroShock_optimal`: the explicit plan without shocks;
  `zero_path_not_optimal`: with `Λ ≠ 0` the optimum is not the zero path.
-/

namespace Gali.DiscretionCommitment.DistortedSS

open Filter Topology
open Gali.DiscretionCommitment.Commitment (gam del gam_pos gam_mul_lt_iff del_pos
  del_lt_one_iff kappa_sq_del lag lag_zero lag_succ lag_adapted)

/-! ### The loss function and the Phillips curve, (17)–(18) -/

/-- Galí (2015), (17), p. 139: the period loss `½ (π² + ϑ x̂²) − Λ x̂`. -/
noncomputable def periodLoss (ϑ Λ infl x : ℝ) : ℝ := (infl ^ 2 + ϑ * x ^ 2) / 2 - Λ * x

/-- Galí (2015), (17), p. 139: the weight of the linear term, `Λ ≡ Φ λ / ε`. -/
noncomputable def distLambda (Φ lam ε : ℝ) : ℝ := Φ * lam / ε

/-- Galí (2015), p. 139: with a steady-state gross markup `M > 1` and no subsidy, the
distortion is `Φ = 1 − 1/M > 0`. -/
theorem markup_distortion_pos {M : ℝ} (hM : 1 < M) : 0 < 1 - 1 / M := by
  have : 1 / M < 1 := by rw [div_lt_one (by linarith)]; exact hM
  linarith

/-- Galí (2015), p. 139: `Λ = Φ λ / ε > 0` when `Φ, λ, ε > 0`. -/
theorem distLambda_pos {Φ lam ε : ℝ} (hΦ : 0 < Φ) (hlam : 0 < lam) (hε : 0 < ε) :
    0 < distLambda Φ lam ε := by
  unfold distLambda; positivity

/-- Galí (2015), (17), p. 139, and Appendix 5.1, p. 156: multiplying the period welfare loss
`−[Φ x̂ − ½ ((ε/λ) π² + c x̂²)]` of Appendix 5.1 (`c = σ + (φ+α)/(1−α)`) by `λ/ε` gives the
period loss of (17), with `κ = λ c`, `ϑ = κ/ε` and `Λ = Φ λ/ε`. -/
theorem loss_rescale {lam ε c Φ κ ϑ Λ : ℝ} (hlam : lam ≠ 0) (hε : ε ≠ 0) (hκ : κ = lam * c)
    (hϑ : ϑ = κ / ε) (hΛ : Λ = distLambda Φ lam ε) (infl x : ℝ) :
    lam / ε * -(Φ * x - ((ε / lam) * infl ^ 2 + c * x ^ 2) / 2) = periodLoss ϑ Λ infl x := by
  subst hκ hϑ hΛ
  unfold periodLoss distLambda
  field_simp
  ring

/-- Galí (2015), (17), p. 139: completing the square, the period loss is
`½ π² + (ϑ/2)(x̂ − Λ/ϑ)² − Λ²/(2ϑ)`, so the loss is minimised at `x̂ = Λ/ϑ` when `π = 0`
is free. -/
theorem periodLoss_complete_square {ϑ : ℝ} (hϑ : ϑ ≠ 0) (Λ infl x : ℝ) :
    periodLoss ϑ Λ infl x = infl ^ 2 / 2 + ϑ / 2 * (x - Λ / ϑ) ^ 2 - Λ ^ 2 / (2 * ϑ) := by
  unfold periodLoss
  field_simp
  ring

/-- Galí (2015), (18), p. 139: the Phillips curve `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`
rewritten in `x̂_t ≡ x_t − x̄`, where `x_t = y_t − y^e_t` and `x̄ = y^n − y^e` is its
steady-state value, reads `π_t = β E_t π_{t+1} + κ x̂_t + u_t` with
`u_t ≡ κ (ŷ^e_t − ŷ^n_t)` (hats: deviations from the steady states `y^e`, `y^n`). -/
theorem nkpc_in_xhat {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ yne yee : ℝ}
    {infl y yn ye : ℕ → Ω → ℝ}
    (h : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - yn t)) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ((y t - ye t) - fun _ => yne - yee) +
      κ • ((ye t - fun _ => yee) - (yn t - fun _ => yne)) := by
  rw [h t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-! ### Optimal discretionary policy, (19)–(20) -/

/-- Galí (2015), (19), p. 140: the per-period problem under discretion: minimise
`½(π² + ϑ x̂²) − Λ x̂` subject to `π = κ x̂ + υ`, `υ` taken as given. The first-order
condition `x̂ = Λ/ϑ − (κ/ϑ) π` is necessary and sufficient for a minimum. -/
theorem discretion_period_optimal_iff {κ ϑ Λ υ x : ℝ} (hϑ : 0 < ϑ) :
    (∀ x', periodLoss ϑ Λ (κ * x + υ) x ≤ periodLoss ϑ Λ (κ * x' + υ) x') ↔
      x = Λ / ϑ - κ / ϑ * (κ * x + υ) := by
  set F := κ * (κ * x + υ) + ϑ * x - Λ with hF
  have hdiff : ∀ y, periodLoss ϑ Λ (κ * y + υ) y - periodLoss ϑ Λ (κ * x + υ) x =
      (y - x) * F + (κ ^ 2 + ϑ) / 2 * (y - x) ^ 2 := by
    intro y; unfold periodLoss; rw [hF]; ring
  have hpos : 0 < κ ^ 2 + ϑ := by positivity
  have hiff : x = Λ / ϑ - κ / ϑ * (κ * x + υ) ↔ F = 0 := by
    rw [hF]
    constructor
    · intro h; field_simp at h; linarith
    · intro h; field_simp; linarith
  rw [hiff]
  constructor
  · intro hmin
    have h1 := hmin (x - F / (κ ^ 2 + ϑ))
    have h2 := hdiff (x - F / (κ ^ 2 + ϑ))
    have h3 : (x - F / (κ ^ 2 + ϑ) - x) * F + (κ ^ 2 + ϑ) / 2 * (x - F / (κ ^ 2 + ϑ) - x) ^ 2
        = -(F ^ 2 / (2 * (κ ^ 2 + ϑ))) := by
      field_simp; ring
    have h4 : F ^ 2 / (2 * (κ ^ 2 + ϑ)) ≤ 0 := by linarith
    have h5 : F ^ 2 ≤ 0 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (κ ^ 2 + ϑ))).mp h4
      linarith
    nlinarith [sq_nonneg F]
  · intro h0 y
    have := hdiff y
    rw [h0, mul_zero, zero_add] at this
    nlinarith [sq_nonneg (y - x)]

/-- Galí (2015), (19), p. 140: under the first-order condition, the per-period optimum is
strict: any other `x̂'` gives a strictly larger loss. -/
theorem discretion_period_strict {κ ϑ Λ υ x x' : ℝ} (hϑ : 0 < ϑ)
    (hfoc : x = Λ / ϑ - κ / ϑ * (κ * x + υ)) (hne : x' ≠ x) :
    periodLoss ϑ Λ (κ * x + υ) x < periodLoss ϑ Λ (κ * x' + υ) x' := by
  have hF : κ * (κ * x + υ) + ϑ * x - Λ = 0 := by
    field_simp at hfoc; linarith
  have hd : periodLoss ϑ Λ (κ * x' + υ) x' - periodLoss ϑ Λ (κ * x + υ) x =
      (x' - x) * (κ * (κ * x + υ) + ϑ * x - Λ) + (κ ^ 2 + ϑ) / 2 * (x' - x) ^ 2 := by
    unfold periodLoss; ring
  rw [hF, mul_zero, zero_add] at hd
  have : 0 < (x' - x) ^ 2 := by
    have : x' - x ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have : 0 < (κ ^ 2 + ϑ) / 2 * (x' - x) ^ 2 := by positivity
  linarith

/-- Galí (2015), (18)–(19), p. 140: an equilibrium under discretion with a distorted steady
state: the Phillips curve (18) and the targeting rule (19), at every date. -/
def DiscretionEqm {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ : ℝ)
    (u infl x : ℕ → Ω → ℝ) : Prop :=
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t) ∧
    ∀ t, x t = (fun _ => Λ / ϑ) - (κ / ϑ) • infl t

/-- Galí (2015), p. 141: the average inflation (inflation bias) under discretion,
`π̄ = κ Λ / (κ² + ϑ (1 − β))`. -/
noncomputable def inflationBias (β κ ϑ Λ : ℝ) : ℝ := κ * Λ / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), p. 141: the average output gap under discretion,
`x̄ = (1 − β) Λ / (κ² + ϑ (1 − β))`. -/
noncomputable def gapBias (β κ ϑ Λ : ℝ) : ℝ := (1 - β) * Λ / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), (20), p. 140: the discretionary inflation path
`π_t = π̄ + ϑ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def discInfl {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => inflationBias β κ ϑ Λ) + (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))) • u t

/-- Galí (2015), p. 141: the discretionary output-gap path
`x̂_t = x̄ − κ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def discGap {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => gapBias β κ ϑ Λ) - (κ / (κ ^ 2 + ϑ * (1 - β * ρ))) • u t

/-- Galí (2015), p. 130: `1 − βρ > 0` for `0 < β < 1` and `|ρ| < 1`. -/
theorem one_sub_mul_pos {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) :
    0 < 1 - β * ρ := by
  have : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    nlinarith [abs_nonneg ρ]
  linarith [le_abs_self (β * ρ)]

/-- Galí (2015), (20), p. 140, and p. 141: the discretionary paths (20) and
`x̂_t = x̄ − κ/(κ² + ϑ(1 − βρ_u)) u_t` form an equilibrium under discretion (existence of the
MSV solution) for an AR(1) cost-push process. -/
theorem discretion_exists {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEqm 𝔼 β κ ϑ Λ u (discInfl β κ ϑ Λ ρ u) (discGap β κ ϑ Λ ρ u) := by
  have h1 : 0 < 1 - β * ρ := one_sub_mul_pos hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by positivity
  have hD1 : 0 < κ ^ 2 + ϑ * (1 - β) := by
    have : 0 < 1 - β := by linarith
    positivity
  have hD' := hD.ne'
  have hD1' := hD1.ne'
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hE : 𝔼.E t (discInfl β κ ϑ Λ ρ u (t + 1)) = (fun _ => inflationBias β κ ϑ Λ) +
        (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ)) * ρ) • u t := by
      unfold discInfl; rw [map_add, 𝔼.const, 𝔼.E_smul, hu.2 t, smul_smul]
    rw [hE]; funext ω
    unfold discInfl discGap inflationBias gapBias
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · have hc : gapBias β κ ϑ Λ = Λ / ϑ - κ / ϑ * inflationBias β κ ϑ Λ := by
      unfold gapBias inflationBias
      rw [eq_sub_iff_add_eq, div_mul_div_comm, div_add_div _ _ hD1' (by positivity),
        div_eq_div_iff (by positivity) hϑ.ne']
      ring
    have hk : κ / (κ ^ 2 + ϑ * (1 - β * ρ)) = κ / ϑ * (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))) := by
      rw [div_mul_div_comm, mul_comm κ ϑ, mul_div_mul_left _ _ hϑ.ne']
    funext ω
    unfold discInfl discGap
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hc, hk]
    ring

/-- Galí (2015), p. 140: under discretion, combining (18) and (19), inflation solves the
scalar forward equation `π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (κΛ + ϑ u_t)/(ϑ + κ²)`. -/
theorem discretion_forward {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ : ℝ}
    (hϑ : 0 < ϑ) {u infl x : ℕ → Ω → ℝ} (hE : DiscretionEqm 𝔼 β κ ϑ Λ u infl x) (t : ℕ) :
    infl t = (ϑ * β / (ϑ + κ ^ 2)) • 𝔼.E t (infl (t + 1)) +
      ((fun _ => κ * Λ / (ϑ + κ ^ 2)) + (ϑ / (ϑ + κ ^ 2)) • u t) := by
  have h1 := hE.1 t
  rw [hE.2 t] at h1
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 ⊢
  field_simp at h2 ⊢
  linear_combination h2

/-- Galí (2015), (20), p. 140, and p. 141: uniqueness. Any equilibrium under discretion with
bounded inflation coincides with (20) and the `x̂` formula of p. 141 (for a bounded AR(1)
cost-push process, `0 < β < 1`, `ϑ > 0`, `|ρ_u| < 1`). -/
theorem discretion_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u infl x : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hE : DiscretionEqm 𝔼 β κ ϑ Λ u infl x)
    (hb : BoundedProc infl) :
    infl = discInfl β κ ϑ Λ ρ u ∧ x = discGap β κ ϑ Λ ρ u := by
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  have ha0 : 0 ≤ ϑ * β / (ϑ + κ ^ 2) := by positivity
  have ha1 : ϑ * β / (ϑ + κ ^ 2) < 1 := by
    rw [div_lt_one hD]; nlinarith [sq_nonneg κ]
  have ha : |ϑ * β / (ϑ + κ ^ 2)| < 1 := by rwa [abs_of_nonneg ha0]
  have hc := discretion_exists 𝔼 hβ0 hβ1 hϑ hρ (Λ := Λ) (κ := κ) hu
  have hcb : BoundedProc (discInfl β κ ϑ Λ ρ u) := by
    obtain ⟨M, hM⟩ := hub
    refine ⟨|inflationBias β κ ϑ Λ| + |ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))| * M, fun t ω => ?_⟩
    unfold discInfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hM t ω
  have hπ : infl = discInfl β κ ϑ Λ ρ u :=
    𝔼.forward_unique ha (discretion_forward 𝔼 hϑ hE) (discretion_forward 𝔼 hϑ hc) hb hcb
  refine ⟨hπ, ?_⟩
  funext t
  rw [hE.2 t, hc.2 t, hπ]

/-- Galí (2015), p. 141: the inflation bias `π̄ = κΛ/(κ² + ϑ(1 − β))` is positive when the
steady state is inefficient (`Λ > 0`). -/
theorem inflationBias_pos {β κ ϑ Λ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) :
    0 < inflationBias β κ ϑ Λ := by
  have : 0 < 1 - β := by linarith
  unfold inflationBias; positivity

/-- Galí (2015), p. 141: the average output gap under discretion,
`x̄ = (1 − β)Λ/(κ² + ϑ(1 − β))`, is positive when `Λ > 0`. -/
theorem gapBias_pos {β κ ϑ Λ : ℝ} (hβ1 : β < 1) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) :
    0 < gapBias β κ ϑ Λ := by
  have : 0 < 1 - β := by linarith
  unfold gapBias; positivity

/-- Galí (2015), p. 141: the inflation bias is strictly increasing in `Λ`. -/
theorem strictMono_inflationBias {β κ ϑ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    StrictMono (fun Λ => inflationBias β κ ϑ Λ) := by
  intro Λ₁ Λ₂ h
  have : 0 < 1 - β := by linarith
  have hD : 0 < κ ^ 2 + ϑ * (1 - β) := by positivity
  simp only [inflationBias]
  gcongr

/-- Galí (2015), p. 141: the inflation bias is strictly increasing in the steady-state
distortion `Φ` (through `Λ = Φλ/ε`, `λ, ε > 0`). -/
theorem strictMono_inflationBias_Phi {β κ ϑ lam ε : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hlam : 0 < lam) (hε : 0 < ε) :
    StrictMono (fun Φ => inflationBias β κ ϑ (distLambda Φ lam ε)) := by
  intro Φ₁ Φ₂ h
  refine strictMono_inflationBias hβ1 hκ hϑ ?_
  simp only [distLambda]
  gcongr

/-- Galí (2015), p. 141: without cost-push shocks, inflation under discretion is constant at
the bias `π̄` at every date: the inflation bias is permanent. -/
theorem discretion_zeroShock {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (t : ℕ) :
    discInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => inflationBias β κ ϑ Λ := by
  unfold discInfl; simp

/-- Galí (2015), p. 141: the distortion does not affect the response to cost-push shocks under
discretion: the discretionary paths with `Λ` differ from those with `Λ = 0` by the constants
`π̄`, `x̄` only. -/
theorem discretion_shock_response_indep {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    discInfl β κ ϑ Λ ρ u t - discInfl β κ ϑ 0 ρ u t = (fun _ => inflationBias β κ ϑ Λ) ∧
      discGap β κ ϑ Λ ρ u t - discGap β κ ϑ 0 ρ u t = (fun _ => gapBias β κ ϑ Λ) := by
  unfold discInfl discGap inflationBias gapBias
  constructor <;> funext ω <;> simp

/-! ### The coefficients `γ` and `δ` -/

/-- Galí (2015), (22), p. 142: `γ ∈ (0, 1)` when `κ > 0` (derived from the `γ` lemmas of
`Commitment`, where `γ` and `δ` are defined). -/
theorem gam_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) : gam β κ ϑ < 1 := by
  have h := (gam_mul_lt_iff hβ0 hϑ).mpr hκ.ne'
  have := gam_pos (κ := κ) hβ0 hϑ
  nlinarith

/-- Galí (2015), p. 142: `1 − δβρ > 0` for `|ρ| ≤ 1`. -/
theorem one_sub_del_mul_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) : 0 < 1 - del β κ ϑ * β * ρ := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have : |del β κ ϑ * β * ρ| < 1 := by
    rw [abs_mul, abs_mul, abs_of_pos h0, abs_of_pos hβ0]
    have : del β κ ϑ * β < 1 := by nlinarith
    nlinarith [abs_nonneg ρ, mul_pos h0 hβ0]
  linarith [le_abs_self (del β κ ϑ * β * ρ)]

/-! ### Optimal policy under commitment: structure, (21)–(22) -/

/-- Galí (2015), (21), p. 142: the (log) price level relative to its initial value,
`p̂_t ≡ p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceLevel {α : Type*} [AddCommMonoid α] (infl : ℕ → α) (t : ℕ) : α :=
  ∑ s ∈ Finset.range (t + 1), infl s

/-- Galí (2015), p. 142: `π_t = p̂_t − p̂_{t−1}` (with `p̂_{−1} = 0`). -/
theorem infl_eq_priceLevel_sub {α : Type*} [AddCommGroup α] (infl : ℕ → α) (t : ℕ) :
    infl t = priceLevel infl t - lag (priceLevel infl) t := by
  cases t with
  | zero => simp [priceLevel]
  | succ t =>
    rw [lag_succ, priceLevel, Finset.sum_range_succ _ (t + 1)]
    simp [priceLevel]

/-- Galí (2015), p. 142: the commitment problem's optimality conditions with a distorted
steady state: the Phillips curve (18), `ϑ x̂_t − κ ξ_t − Λ = 0` and `π_t + ξ_t − ξ_{t−1} = 0`
with `ξ_{−1} = 0`, at every date. -/
def CommitmentFOC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ : ℝ)
    (u infl x ξ : ℕ → Ω → ℝ) : Prop :=
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t) ∧
    (∀ t, ϑ • x t - κ • ξ t - (fun _ => Λ) = 0) ∧ ∀ t, infl t + ξ t - lag ξ t = 0

/-- Galí (2015), p. 142: eliminating the multiplier, `ξ_t = −p̂_t`. -/
theorem mult_eq_neg_priceLevel {α : Type*} [AddCommGroup α] {infl ξ : ℕ → α}
    (h : ∀ t, infl t + ξ t - lag ξ t = 0) (t : ℕ) : ξ t = -priceLevel infl t := by
  induction t with
  | zero =>
    have h0 := h 0
    rw [lag_zero, sub_zero] at h0
    simp only [priceLevel, zero_add, Finset.sum_range_one]
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h0
  | succ t ih =>
    have h1 := h (t + 1)
    rw [lag_succ, ih] at h1
    rw [priceLevel, Finset.sum_range_succ _ (t + 1), ← sub_eq_zero, ← h1]
    simp only [priceLevel]
    abel

/-- Galí (2015), p. 142: the price level of an adapted inflation process is adapted. -/
theorem priceLevel_adapted {Ω : Type*} (𝔼 : ExpectationSystem Ω) {infl : ℕ → Ω → ℝ}
    (h : 𝔼.Adapted infl) : 𝔼.Adapted (priceLevel infl) := by
  intro t
  unfold priceLevel
  rw [map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hst : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [← h s]
  exact 𝔼.known hst _

/-- Galí (2015), (21), p. 142: `ϑ x̂_t = −κ p̂_t + Λ`. -/
theorem commitment_eq21 {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    {u infl x ξ : ℕ → Ω → ℝ} (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (t : ℕ) :
    ϑ • x t = -(κ • priceLevel infl t) + fun _ => Λ := by
  have h1 := hE.2.1 t
  rw [mult_eq_neg_priceLevel hE.2.2 t] at h1
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linarith

/-- Galí (2015), (18) and (21), p. 142: pointwise form of the Phillips curve in the price
level, `p̂_t − p̂_{t−1} = β (E_t p̂_{t+1} − p̂_t) + κ x̂_t + u_t`. -/
theorem commitment_core {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    {u infl x ξ : ℕ → Ω → ℝ} (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ)
    (ha : 𝔼.Adapted infl) (t : ℕ) (ω : Ω) :
    priceLevel infl t ω - lag (priceLevel infl) t ω =
      β * (𝔼.E t (priceLevel infl (t + 1)) ω - priceLevel infl t ω) + κ * x t ω + u t ω := by
  have h1 := hE.1 t
  have hi := infl_eq_priceLevel_sub infl
  rw [hi t, hi (t + 1), lag_succ, map_sub, priceLevel_adapted 𝔼 ha t] at h1
  have h2 := congrFun h1 ω
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h2

/-- Galí (2015), (22), p. 142: the price level satisfies
`p̂_t = γ p̂_{t−1} + γβ E_t p̂_{t+1} + γκΛ/ϑ + γ u_t`. -/
theorem commitment_eq22 {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    (hβ0 : 0 < β) (hϑ : 0 < ϑ) {u infl x ξ : ℕ → Ω → ℝ}
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (t : ℕ) :
    priceLevel infl t = gam β κ ϑ • lag (priceLevel infl) t +
      (gam β κ ϑ * β) • 𝔼.E t (priceLevel infl (t + 1)) +
      (fun _ => gam β κ ϑ * (κ * Λ / ϑ)) + gam β κ ϑ • u t := by
  funext ω
  have hc := commitment_core hE ha t ω
  have hx := congrFun (commitment_eq21 hE t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hx ⊢
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  unfold gam
  field_simp
  linear_combination ϑ * hc + κ * hx

/-! ### The commitment solution, (23)–(24) -/

/-- Galí (2015), (23), p. 142: the coefficient on `u_t`, `b = δ / (1 − δβρ_u)`. -/
noncomputable def commB (β κ ϑ ρ : ℝ) : ℝ := del β κ ϑ / (1 - del β κ ϑ * β * ρ)

/-- Galí (2015), (23), p. 142: the constant `c = (δ / (1 − δβ)) (κΛ/ϑ)`. -/
noncomputable def commConst (β κ ϑ Λ : ℝ) : ℝ := del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ)

/-- Galí (2015), (24), p. 142: backward recursion `y_0 = w_0`, `y_{t+1} = d y_t + w_{t+1}`. -/
def backRec {α : Type*} [Add α] [SMul ℝ α] (d : ℝ) (w : ℕ → α) : ℕ → α
  | 0 => w 0
  | t + 1 => d • backRec d w t + w (t + 1)

/-- Galí (2015), (24), p. 142: the backward sum `y_t = ∑_{k ≤ t} dᵏ w_{t−k}`. -/
theorem backRec_eq_sum {α : Type*} [AddCommGroup α] [Module ℝ α] (d : ℝ) (w : ℕ → α)
    (t : ℕ) : backRec d w t = ∑ k ∈ Finset.range (t + 1), d ^ k • w (t - k) := by
  induction t with
  | zero => simp [backRec]
  | succ t ih =>
    rw [backRec, ih, Finset.sum_range_succ' _ (t + 1), Finset.smul_sum]
    simp only [pow_zero, one_smul, Nat.sub_zero, smul_smul, ← pow_succ']
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < t + 1 := Finset.mem_range.mp hk
    congr 2
    omega

/-- Galí (2015), (23), p. 142: the commitment price level, the solution of
`p̂_t = δ p̂_{t−1} + b u_t + c` with `p̂_{−1} = 0`. -/
noncomputable def commPrice {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  backRec (del β κ ϑ) (fun t => commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ)

/-- Galí (2015), (21), p. 142: the commitment output gap `x̂_t = Λ/ϑ − (κ/ϑ) p̂_t`. -/
noncomputable def commGap {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => Λ / ϑ) - (κ / ϑ) • commPrice β κ ϑ Λ ρ u t

/-- Galí (2015), p. 142: commitment inflation `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def commInfl {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  commPrice β κ ϑ Λ ρ u t - lag (commPrice β κ ϑ Λ ρ u) t

/-- Galí (2015), p. 142: the commitment multiplier `ξ_t = −p̂_t`. -/
noncomputable def commMult {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -commPrice β κ ϑ Λ ρ u t

/-- Galí (2015), (23), p. 142: the candidate satisfies
`p̂_t = δ p̂_{t−1} + b u_t + c` at every date, with `p̂_{−1} = 0`. -/
theorem commPrice_eq23 {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ u t = del β κ ϑ • lag (commPrice β κ ϑ Λ ρ u) t +
      commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ := by
  cases t with
  | zero => simp [commPrice, backRec]
  | succ t => rw [lag_succ, commPrice, backRec, add_assoc]

/-- Galí (2015), p. 142: `b (1 − δβρ_u) = δ`. -/
theorem commB_rel {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : |ρ| ≤ 1) : commB β κ ϑ ρ * (1 - del β κ ϑ * β * ρ) = del β κ ϑ := by
  unfold commB
  exact div_mul_cancel₀ _ (one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ).ne'

/-- Galí (2015), p. 142: `c (1 − δβ) = δ κΛ/ϑ`. -/
theorem commConst_rel {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    commConst β κ ϑ Λ * (1 - del β κ ϑ * β) = del β κ ϑ * (κ * Λ / ϑ) := by
  have h := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at h
  unfold commConst
  field_simp

/-- Galí (2015), p. 143: `κ c = (1 − δ) Λ`, i.e. `κ²δΛ / ((1 − δβ)ϑ) = (1 − δ)Λ`, from the
key identity `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_commConst {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    κ * commConst β κ ϑ Λ = (1 - del β κ ϑ) * Λ := by
  have h := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at h
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  unfold commConst
  field_simp
  linear_combination Λ * hk

/-- Galí (2015), p. 142: `b (ϑ(1 + β − βδ − βρ_u) + κ²) = ϑ` (the `u_t` coefficient identity
behind (23)). -/
theorem commB_X {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : |ρ| ≤ 1) :
    commB β κ ϑ ρ * (ϑ * (1 + β - β * del β κ ϑ - β * ρ) + κ ^ 2) = ϑ := by
  have h := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  unfold commB
  field_simp
  linear_combination hk

/-- Galí (2015), p. 142: `c (ϑ(1 − βδ) + κ²) = κΛ` (the constant identity behind (23)). -/
theorem commConst_X {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    commConst β κ ϑ Λ * (ϑ * (1 - β * del β κ ϑ) + κ ^ 2) = κ * Λ := by
  have h1 := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have h2 := commConst_rel (Λ := Λ) hβ0 hβ1 hκ hϑ
  have h3 : ϑ * (del β κ ϑ * (κ * Λ / ϑ)) = del β κ ϑ * (κ * Λ) := by
    field_simp
  linear_combination ϑ * h2 + κ * h1 + h3

/-- Galí (2015), (23), p. 142: the commitment price level is adapted. -/
theorem commPrice_adapted {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ ρ : ℝ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) : 𝔼.Adapted (commPrice β κ ϑ Λ ρ u) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 (commB β κ ϑ ρ • u 0 + fun _ => commConst β κ ϑ Λ) = _
    rw [map_add, 𝔼.E_smul, hu 0, 𝔼.const]
    rfl
  | succ t ih =>
    change 𝔼.E (t + 1) (del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ)) = _
    rw [map_add, map_add, 𝔼.E_smul, 𝔼.E_smul, hu (t + 1), 𝔼.const, ← ih,
      𝔼.known (Nat.le_succ t), ih]
    rfl

/-- Galí (2015), (23), p. 142: `E_t p̂_{t+1} = δ p̂_t + bρ_u u_t + c` along the commitment
solution. -/
theorem commPrice_E_succ {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ ρ : ℝ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) :
    𝔼.E t (commPrice β κ ϑ Λ ρ u (t + 1)) = del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ * ρ) • u t + fun _ => commConst β κ ϑ Λ := by
  change 𝔼.E t (del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ)) = _
  rw [map_add, map_add, 𝔼.E_smul, 𝔼.E_smul, hu.2 t, 𝔼.const,
    commPrice_adapted 𝔼 β κ ϑ Λ ρ hu.1 t, smul_smul, add_assoc]

/-- Galí (2015), (21), p. 142: `ϑ x̂_t = Λ − κ p̂_t` along the commitment solution. -/
theorem commGap_mul {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ϑ * commGap β κ ϑ Λ ρ u t ω = Λ - κ * commPrice β κ ϑ Λ ρ u t ω := by
  unfold commGap
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Galí (2015), (23)–(24), p. 142: the commitment price level is bounded for a bounded
cost-push process. -/
theorem commPrice_bounded {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hub : BoundedProc u) :
    BoundedProc (commPrice β κ ϑ Λ ρ u) := by
  obtain ⟨M, hM⟩ := hub
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  set d := del β κ ϑ
  set N := |commB β κ ϑ ρ| * |M| + |commConst β κ ϑ Λ|
  have hN : 0 ≤ N := by positivity
  have hw : ∀ t ω, |(commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ : Ω → ℝ) ω| ≤ N := by
    intro t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := (hM t ω).trans (le_abs_self M)
    have := mul_le_mul_of_nonneg_left this (abs_nonneg (commB β κ ϑ ρ))
    simp only [N]
    linarith
  refine ⟨N / (1 - d), fun t ω => ?_⟩
  have hK : N ≤ N / (1 - d) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  induction t with
  | zero => exact (hw 0 ω).trans hK
  | succ t ih =>
    change |(d • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ) : Ω → ℝ) ω| ≤ _
    rw [Pi.add_apply]
    refine (abs_add_le _ _).trans ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    have := hw (t + 1) ω
    have hd1 : 1 - d ≠ 0 := (by linarith : (0 : ℝ) < 1 - d).ne'
    have hdK : d * (N / (1 - d)) + N = N / (1 - d) := by
      field_simp; ring
    nlinarith

/-- Galí (2015), (21)–(23), p. 142: **existence**. The commitment paths built from (23)
satisfy the Phillips curve and both optimality conditions, are adapted, and are bounded
(bounded AR(1) cost-push process, `0 < β < 1`, `κ, ϑ > 0`, `|ρ_u| ≤ 1`). -/
theorem commitment_exists {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    CommitmentFOC 𝔼 β κ ϑ Λ u (commInfl β κ ϑ Λ ρ u) (commGap β κ ϑ Λ ρ u)
        (commMult β κ ϑ Λ ρ u) ∧
      𝔼.Adapted (commInfl β κ ϑ Λ ρ u) ∧ BoundedProc (commPrice β κ ϑ Λ ρ u) ∧
      BoundedProc (commGap β κ ϑ Λ ρ u) ∧ BoundedProc (commInfl β κ ϑ Λ ρ u) := by
  have hPa := commPrice_adapted 𝔼 β κ ϑ Λ ρ hu.1
  obtain ⟨K, hK⟩ := commPrice_bounded (Λ := Λ) (ρ := ρ) hβ0 hβ1 hκ hϑ hub
  have hlagK : ∀ t ω, |lag (commPrice β κ ϑ Λ ρ u) t ω| ≤ |K| := by
    intro t ω
    cases t with
    | zero => simp
    | succ t => exact (hK t ω).trans (le_abs_self K)
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, fun t => ?_, ⟨K, hK⟩, ?_, ?_⟩
  · funext ω
    have hE : 𝔼.E t (commInfl β κ ϑ Λ ρ u (t + 1)) ω =
        del β κ ϑ * commPrice β κ ϑ Λ ρ u t ω + commB β κ ϑ ρ * ρ * u t ω +
          commConst β κ ϑ Λ - commPrice β κ ϑ Λ ρ u t ω := by
      unfold commInfl
      rw [lag_succ, map_sub, commPrice_E_succ 𝔼 β κ ϑ Λ ρ hu t, hPa t]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
    have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
      rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
    have hB := commB_X hβ0 hβ1 hκ hϑ hρ
    have hC := commConst_X (Λ := Λ) hβ0 hβ1 hκ hϑ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hE]
    unfold commInfl
    simp only [Pi.sub_apply]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (ϑ * (1 - β * del β κ ϑ + β) + κ ^ 2) * hP - κ * hx +
      lag (commPrice β κ ϑ Λ ρ u) t ω * hk + u t ω * hB + hC
  · funext ω
    have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    unfold commMult
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination hx
  · funext ω
    cases t with
    | zero => simp [commInfl, commMult]
    | succ t =>
      simp only [commInfl, commMult, lag_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Pi.zero_apply]
      ring
  · unfold commInfl
    rw [map_sub, hPa t, lag_adapted 𝔼 hPa t]
  · refine ⟨|Λ / ϑ| + |κ / ϑ| * K, fun t ω => ?_⟩
    unfold commGap
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hK t ω
  · refine ⟨K + |K|, fun t ω => ?_⟩
    unfold commInfl
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK t ω) (hlagK t ω))

/-- Galí (2015), (21)–(23), p. 142: **uniqueness**. Any adapted solution of the commitment
optimality conditions with a bounded output gap coincides with the commitment paths of (23):
price level, inflation, output gap and multiplier. -/
theorem commitment_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x) :
    priceLevel infl = commPrice β κ ϑ Λ ρ u ∧ infl = commInfl β κ ϑ Λ ρ u ∧
      x = commGap β κ ϑ Λ ρ u ∧ ξ = commMult β κ ϑ Λ ρ u := by
  set P := priceLevel infl with hPdef
  set d := del β κ ϑ with hd
  set b := commB β κ ϑ ρ
  set c := commConst β κ ϑ Λ
  have h0 : 0 < d := del_pos hβ0 hϑ
  have h1 : d < 1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hPa : 𝔼.Adapted P := priceLevel_adapted 𝔼 ha
  have hx : ∀ t ω, ϑ * x t ω = Λ - κ * P t ω := by
    intro t ω
    have := congrFun (commitment_eq21 hE t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this
    linarith
  obtain ⟨M, hM⟩ := hb
  have hPb : ∀ t ω, |P t ω| ≤ (|Λ| + ϑ * M) / κ := by
    intro t ω
    rw [le_div_iff₀ hκ]
    have h2 : κ * P t ω = Λ - ϑ * x t ω := by linarith [hx t ω]
    have h3 : |κ * P t ω| ≤ |Λ| + ϑ * M := by
      rw [h2]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos hϑ]
      gcongr
      exact hM t ω
    rw [abs_mul, abs_of_pos hκ] at h3
    linarith
  set K := (|Λ| + ϑ * M) / κ
  have hlagb : ∀ t ω, |lag P t ω| ≤ |K| := by
    intro t ω
    cases t with
    | zero => simp
    | succ t => exact (hPb t ω).trans (le_abs_self K)
  -- the quasi-difference z_t = p̂_t − δ p̂_{t−1} solves a stable forward equation
  set z : ℕ → Ω → ℝ := fun t => P t - d • lag P t with hz
  set w : ℕ → Ω → ℝ := fun t => (fun _ => d * (κ * Λ / ϑ)) + d • u t with hw
  set zc : ℕ → Ω → ℝ := fun t => b • u t + fun _ => c with hzc
  have hkl : ϑ * (κ * Λ / ϑ) = κ * Λ := by field_simp
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  have hzeq : ∀ t, z t = (d * β) • 𝔼.E t (z (t + 1)) + w t := by
    intro t
    funext ω
    have hc := commitment_core hE ha t ω
    have hEz : 𝔼.E t (z (t + 1)) ω = 𝔼.E t (P (t + 1)) ω - d * P t ω := by
      simp only [hz, lag_succ, map_sub, 𝔼.E_smul, hPa t, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEz]
    simp only [hz, hw, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (d * ϑ) * hc - P t ω * hk + (d * κ) * hx t ω - d * hkl
  have hzceq : ∀ t, zc t = (d * β) • 𝔼.E t (zc (t + 1)) + w t := by
    intro t
    have hB := commB_rel hβ0 hβ1 hκ hϑ hρ
    have hC := commConst_rel (Λ := Λ) hβ0 hβ1 hκ hϑ
    have hEz : 𝔼.E t (zc (t + 1)) = (b * ρ) • u t + fun _ => c := by
      simp only [hzc, map_add, 𝔼.E_smul, hu.2 t, 𝔼.const, smul_smul]
    rw [hEz]
    funext ω
    simp only [hzc, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * hB + hC
  have hdb : |d * β| < 1 := by
    rw [abs_of_pos (mul_pos h0 hβ0)]; nlinarith
  have hzb : BoundedProc z := by
    refine ⟨K + d * |K|, fun t ω => ?_⟩
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hPb t ω) ?_)
    rw [abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hlagb t ω) h0.le
  have hzcb : BoundedProc zc := by
    obtain ⟨Mu, hMu⟩ := hub
    refine ⟨|b| * Mu + |c|, fun t ω => ?_⟩
    simp only [hzc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left (hMu t ω) (abs_nonneg b)
    linarith
  have hzz : z = zc := 𝔼.forward_unique hdb hzeq hzceq hzb hzcb
  have hPeq : P = commPrice β κ ϑ Λ ρ u := by
    funext t
    induction t with
    | zero =>
      have := congrFun hzz 0
      simp only [hz, hzc, lag_zero, smul_zero, sub_zero] at this
      rw [this]
      rfl
    | succ t ih =>
      have := congrFun hzz (t + 1)
      simp only [hz, hzc, lag_succ] at this
      rw [sub_eq_iff_eq_add] at this
      rw [this, ih, add_comm]
      rfl
  refine ⟨hPeq, ?_, ?_, ?_⟩
  · funext t
    rw [infl_eq_priceLevel_sub infl t, ← hPdef, hPeq]
    rfl
  · funext t ω
    have h2 := hx t ω
    have h3 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    rw [hPeq] at h2
    apply mul_left_cancel₀ hϑ.ne'
    rw [h2, h3]
  · funext t
    rw [mult_eq_neg_priceLevel hE.2.2 t, ← hPdef, hPeq]
    rfl

/-- Galí (2015), (23), p. 142: along the (unique bounded) commitment equilibrium,
`p̂_t = δ p̂_{t−1} + δ/(1 − δβρ_u) u_t + (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commitment_eq23 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x)
    (t : ℕ) :
    priceLevel infl t = del β κ ϑ • lag (priceLevel infl) t +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t +
      fun _ => del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ) := by
  rw [(commitment_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub hE ha hb).1]
  exact commPrice_eq23 β κ ϑ Λ ρ u t

/-- Galí (2015), (24), p. 142: solving (23) backward,
`p̂_t = ((1 − δ^{t+1})/(1 − δ)) (δ/(1 − δβ)) (κΛ/ϑ) + (δ/(1 − δβρ_u)) ∑_{k ≤ t} δᵏ u_{t−k}`. -/
theorem commitment_eq24 {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ u t =
      (fun _ => (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
        (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne : del β κ ϑ - 1 ≠ 0 := (by linarith : del β κ ϑ - 1 < 0).ne
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  unfold commPrice
  rw [backRec_eq_sum]
  funext ω
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_mul, geom_sum_eq (by linarith) (t + 1), Finset.mul_sum, add_comm]
  congr 1
  · unfold commConst
    field_simp
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    unfold commB
    ring

/-! ### The output gap under commitment, (25)–(27), corrected -/

/-- Galí (2015), (25), p. 143: `x̂_{t+1} = δ x̂_t − (κδ/(ϑ(1 − δβρ_u))) u_{t+1}` along the
commitment solution. -/
theorem commGap_eq25 {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commGap β κ ϑ Λ ρ u (t + 1) = del β κ ϑ • commGap β κ ϑ Λ ρ u t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u (t + 1) := by
  funext ω
  have hx1 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u (t + 1) ω
  have hx0 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
  have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u (t + 1)) ω
  simp only [lag_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) = κ * commB β κ ϑ ρ := by
    unfold commB; field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx1 - del β κ ϑ * hx0 + u (t + 1) ω * hcoef - κ * hP - hkc

/-- Galí (2015), (26) **corrected**, p. 143: along the commitment solution
`x̂_0 = δΛ/ϑ − (κδ/(ϑ(1 − δβρ_u))) u_0` (the book prints `(1 − δ)Λ/ϑ` as the constant). -/
theorem commGap_eq26_corrected {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) :
    commGap β κ ϑ Λ ρ u 0 = (fun _ => del β κ ϑ * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u 0 := by
  funext ω
  have hx0 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u 0 ω
  have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u 0) ω
  simp only [lag_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) = κ * commB β κ ϑ ρ := by
    unfold commB; field_simp
  have hdl : ϑ * (del β κ ϑ * Λ / ϑ) = del β κ ϑ * Λ := by field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx0 - hdl + u 0 ω * hcoef - κ * hP - hkc

/-- Galí (2015), (27) **corrected**, p. 143: along the commitment solution
`x̂_t = δ^{t+1}Λ/ϑ − (κδ/(ϑ(1 − δβρ_u))) ∑_{k ≤ t} δᵏ u_{t−k}`. -/
theorem commGap_eq27_corrected {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commGap β κ ϑ Λ ρ u t = (fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  funext ω
  have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
  have hP := congrFun (commitment_eq24 (Λ := Λ) (ρ := ρ) hβ0 hβ1 hκ hϑ u t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hS : κ * ((1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
      (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) = (1 - del β κ ϑ ^ (t + 1)) * Λ := by
    have : κ * (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ)) = (1 - del β κ ϑ) * Λ := by
      rw [← hkc]; rfl
    calc _ = (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
          (κ * (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) := by ring
      _ = _ := by rw [this]; field_simp
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) =
      κ * (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) := by
    field_simp
  have hdl : ϑ * (del β κ ϑ ^ (t + 1) * Λ / ϑ) = del β κ ϑ ^ (t + 1) * Λ := by field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx - hdl + (∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k)) ω * hcoef -
    κ * hP - hS

/-- Galí (2015), (25)–(27), p. 143, for the commitment equilibrium itself: any adapted
solution of the commitment conditions with bounded output gap satisfies (25), the corrected
(26) and the corrected (27). -/
theorem commitment_eq25_eq27 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x) :
    (∀ t, x (t + 1) = del β κ ϑ • x t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u (t + 1)) ∧
    x 0 = (fun _ => del β κ ϑ * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u 0 ∧
    ∀ t, x t = (fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  rw [(commitment_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub hE ha hb).2.2.1]
  exact ⟨commGap_eq25 hβ0 hβ1 hκ hϑ hρ u, commGap_eq26_corrected hβ0 hβ1 hκ hϑ hρ u,
    commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ u⟩

/-! ### The printed (26)–(27) are false -/

/-- Galí (2015), (26), p. 143, as printed, is false: without cost-push shocks (`u ≡ 0`) and
with `Λ ≠ 0`, the commitment output gap at `t = 0` equals the printed `(1 − δ)Λ/ϑ` if and
only if `δ = 1/2`. (The correct value is `δΛ/ϑ`.) -/
theorem printed_eq26_iff {Ω : Type*} [Nonempty Ω] {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : Λ ≠ 0) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) 0 = (fun _ => (1 - del β κ ϑ) * Λ / ϑ) ↔
      del β κ ϑ = 1 / 2 := by
  rw [commGap_eq26_corrected hβ0 hβ1 hκ hϑ hρ]
  simp only [Pi.zero_apply, smul_zero, sub_zero]
  constructor
  · intro h
    have h2 := congrFun h (Classical.arbitrary Ω)
    field_simp at h2
    linarith
  · intro h
    funext ω
    rw [h]
    ring

/-- Galí (2015), (27), p. 143, as printed (deterministic term `(1 − δ)δᵗΛ/ϑ`), is false: with
`u ≡ 0` and `Λ ≠ 0`, the commitment output gap at date `t` equals the printed value if and only
if `δ = 1/2`. (The correct deterministic term is `δ^{t+1}Λ/ϑ`.) -/
theorem printed_eq27_iff {Ω : Type*} [Nonempty Ω] {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : Λ ≠ 0) (t : ℕ) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t =
        (fun _ => (1 - del β κ ϑ) * del β κ ϑ ^ t * Λ / ϑ) ↔ del β κ ϑ = 1 / 2 := by
  rw [commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ]
  have h0 := del_pos (κ := κ) hβ0 hϑ
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero]
  constructor
  · intro h
    have h2 := congrFun h (Classical.arbitrary Ω)
    field_simp at h2
    have hp : 0 < del β κ ϑ ^ t := pow_pos h0 t
    have : (2 * del β κ ϑ - 1) * del β κ ϑ ^ t = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h3 | h3
    · linarith
    · linarith
  · intro h
    funext ω
    rw [h, pow_succ]
    ring

/-- Galí (2015), (27), p. 143, read with the sum over `k` also applied to the deterministic
term: `∑_{k ≤ t} (1 − δ)δᵏΛ/ϑ = (1 − δ^{t+1})Λ/ϑ`, which tends to `Λ/ϑ`, not to `0`; so this
reading contradicts the book's own `lim x̂_T = 0` (and its `t = 0` term is the false (26)). -/
theorem printed_eq27_sum_tendsto {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    Tendsto (fun t : ℕ => ∑ k ∈ Finset.range (t + 1), (1 - del β κ ϑ) * del β κ ϑ ^ k * Λ / ϑ)
      atTop (𝓝 (Λ / ϑ)) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne : del β κ ϑ - 1 ≠ 0 := (by linarith : del β κ ϑ - 1 < 0).ne
  have heq : ∀ t : ℕ, ∑ k ∈ Finset.range (t + 1), (1 - del β κ ϑ) * del β κ ϑ ^ k * Λ / ϑ =
      (1 - del β κ ϑ ^ (t + 1)) * (Λ / ϑ) := by
    intro t
    simp only [mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [geom_sum_eq (by linarith) (t + 1)]
    field_simp
    ring
  simp only [heq]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  simpa using (hp.const_sub 1).mul_const (Λ / ϑ)

/-- Galí (2015), p. 142: a parameter point at which `δ = 1/4`: `β = 1/2`, `κ = 1`,
`ϑ = 8/21` (then `γ = 8/33` and `√(1 − 4βγ²) = 31/33`). -/
theorem del_example : del (1 / 2) 1 (8 / 21) = 1 / 4 := by
  unfold del gam
  have h : (1 : ℝ) - 4 * (1 / 2) * (8 / 21 / (8 / 21 * (1 + 1 / 2) + 1 ^ 2)) ^ 2 =
      (31 / 33) ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Galí (2015), (26)–(27), p. 143: **counterexample** to the printed formulas. With
`β = 1/2`, `κ = 1`, `ϑ = 8/21`, `Λ = 1` and no cost-push shocks, the commitment equilibrium has
`x̂_0 = δΛ/ϑ = 21/32`, whereas the printed (26) gives `(1 − δ)Λ/ϑ = 63/32`. -/
theorem printed_eq26_false :
    commGap (1 / 2) 1 (8 / 21) 1 0 (0 : ℕ → Unit → ℝ) 0 () = 21 / 32 ∧
      (1 - del (1 / 2) 1 (8 / 21)) * 1 / (8 / 21) = 63 / 32 ∧
      commGap (1 / 2) 1 (8 / 21) 1 0 (0 : ℕ → Unit → ℝ) 0 () ≠
        (1 - del (1 / 2) 1 (8 / 21)) * 1 / (8 / 21) := by
  have h := congrFun (commGap_eq26_corrected (Λ := 1) (ρ := 0) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 8 / 21) (by norm_num)
    (0 : ℕ → Unit → ℝ)) ()
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at h
  rw [h, del_example]
  norm_num

/-! ### No long-run inflation bias under commitment -/

/-- Galí (2015), (24), p. 142, with `u ≡ 0`:
`p̂_t = ((1 − δ^{t+1})/(1 − δ)) (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commPrice_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t =
      fun _ => (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) * commConst β κ ϑ Λ := by
  rw [commitment_eq24 hβ0 hβ1 hκ hϑ]
  funext ω
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, add_zero, commConst]

/-- Galí (2015), (27) corrected, p. 143, with `u ≡ 0`: `x̂_t = δ^{t+1}Λ/ϑ`. -/
theorem commGap_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (t : ℕ) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ := by
  rw [commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ]
  funext ω
  simp

/-- Galí (2015), p. 143, with `u ≡ 0`: commitment inflation is `π_t = δᵗ c`,
`c = (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commInfl_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (t : ℕ) :
    commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => del β κ ϑ ^ t * commConst β κ ϑ Λ := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  unfold commInfl
  funext ω
  cases t with
  | zero =>
    simp only [lag_zero, Pi.sub_apply, Pi.zero_apply, sub_zero, pow_zero, one_mul]
    rw [commPrice_zeroShock hβ0 hβ1 hκ hϑ]
    field_simp
    ring
  | succ t =>
    simp only [lag_succ, Pi.sub_apply]
    rw [commPrice_zeroShock hβ0 hβ1 hκ hϑ, commPrice_zeroShock hβ0 hβ1 hκ hϑ]
    field_simp
    ring

/-- Galí (2015), p. 143: with `u ≡ 0` the price level converges,
`lim p̂_T = δκΛ / ((1 − δβ)(1 − δ)ϑ)`. -/
theorem tendsto_priceLevel_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (ω : Ω) :
    Tendsto (fun t => commPrice β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop
      (𝓝 (del β κ ϑ * κ * Λ / ((1 - del β κ ϑ * β) * (1 - del β κ ϑ) * ϑ))) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  simp only [commPrice_zeroShock hβ0 hβ1 hκ hϑ]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  have := ((hp.const_sub 1).div_const (1 - del β κ ϑ)).mul_const (commConst β κ ϑ Λ)
  convert this using 2
  unfold commConst
  rw [mul_one] at hb
  field_simp
  ring

/-- Galí (2015), p. 143: in the long run the marginal benefit of output equals the cost of
cumulative inflation, `κ lim p̂_T = Λ`. -/
theorem kappa_limit_priceLevel {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    κ * (del β κ ϑ * κ * Λ / ((1 - del β κ ϑ * β) * (1 - del β κ ϑ) * ϑ)) = Λ := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at hb
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  field_simp
  linear_combination Λ * hk

/-- Galí (2015), p. 143: with `u ≡ 0`, `lim x̂_T = 0`: output returns to its natural level
under commitment (no long-run output bias). -/
theorem tendsto_gap_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (ω : Ω) :
    Tendsto (fun t => commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop (𝓝 0) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  simp only [commGap_zeroShock hβ0 hβ1 hκ hϑ hρ]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  simpa using (hp.mul_const Λ).div_const ϑ

/-- Galí (2015), p. 143: with `u ≡ 0`, commitment inflation converges to zero: no long-run
inflation bias. -/
theorem tendsto_infl_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (ω : Ω) :
    Tendsto (fun t => commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop (𝓝 0) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  simp only [commInfl_zeroShock hβ0 hβ1 hκ hϑ]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).mul_const (commConst β κ ϑ Λ)

/-- Galí (2015), p. 143: with `u ≡ 0` and `Λ > 0`, output and inflation stay above their
steady-state values at every date (`x̂_t > 0`, `π_t > 0`): persistent deterministic
transitional dynamics. -/
theorem commitment_zeroShock_pos {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : 0 < Λ) (t : ℕ) (ω : Ω) :
    0 < commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω ∧ 0 < commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at hb
  rw [commGap_zeroShock hβ0 hβ1 hκ hϑ hρ, commInfl_zeroShock hβ0 hβ1 hκ hϑ]
  unfold commConst
  constructor <;> positivity

/-- Galí (2015), pp. 143–144: commitment versus discretion without cost-push shocks. Under
discretion inflation equals the bias `π̄ > 0` at every date; under commitment it converges to
zero, so it eventually falls (and stays) below `π̄`. -/
theorem commitment_vs_discretion_longrun {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) (ω : Ω) :
    (∀ t, discInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω = inflationBias β κ ϑ Λ) ∧
      0 < inflationBias β κ ϑ Λ ∧
      ∀ᶠ t in atTop, commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω < inflationBias β κ ϑ Λ := by
  have hpos := inflationBias_pos hβ1 hκ hϑ hΛ
  refine ⟨fun t => by rw [discretion_zeroShock], hpos, ?_⟩
  exact (tendsto_infl_zeroShock hβ0 hβ1 hκ hϑ ω).eventually (gt_mem_nhds hpos)

/-! ### Optimality of the commitment plan in the deterministic problem -/

/-- Galí (2015), p. 141: a bounded real sequence (the admissible paths of the deterministic
problem). -/
def BddSeq (s : ℕ → ℝ) : Prop := ∃ M, ∀ t, |s t| ≤ M

/-- Galí (2015), (18), p. 139, under perfect foresight: a path `(π, x̂)` is feasible when
`π_t = β π_{t+1} + κ x̂_t + u_t` at every date. -/
def DetFeasible (β κ : ℝ) (u infl x : ℕ → ℝ) : Prop :=
  ∀ t, infl t = β * infl (t + 1) + κ * x t + u t

/-- Galí (2015), p. 142: the Lagrangian first-order conditions `ϑ x̂_t − κ ξ_t − Λ = 0`,
`π_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def DetFOC (κ ϑ Λ : ℝ) (infl x ξ : ℕ → ℝ) : Prop :=
  (∀ t, ϑ * x t - κ * ξ t - Λ = 0) ∧ ∀ t, infl t + ξ t - lag ξ t = 0

/-- Galí (2015), (17), p. 139, under perfect foresight: the discounted loss
`∑ βᵗ (½(π_t² + ϑ x̂_t²) − Λ x̂_t)`. -/
noncomputable def detLoss (β ϑ Λ : ℝ) (infl x : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss ϑ Λ (infl t) (x t)

/-- Galí (2015), (17), p. 139: the period loss is bounded on bounded arguments. -/
theorem abs_periodLoss_le {ϑ Λ a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |periodLoss ϑ Λ a b| ≤ (A ^ 2 + |ϑ| * B ^ 2) / 2 + |Λ| * B := by
  have hA : a ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hB : b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  unfold periodLoss
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_two]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
    gcongr
  · rw [abs_mul]; gcongr

/-- Galí (2015), (17), p. 139: discounted bounded sequences are summable, so the loss of a
bounded path is a genuine (convergent) infinite sum. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {g : ℕ → ℝ} {K : ℝ}
    (hg : ∀ t, |g t| ≤ K) : Summable (fun t => β ^ t * g t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hg t) (pow_nonneg hβ0 t)

/-- Galí (2015), (17), p. 139: the discounted loss of a bounded path is summable. -/
theorem detLoss_summable {β ϑ Λ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {infl x : ℕ → ℝ}
    (hb : BddSeq infl) (hbx : BddSeq x) :
    Summable (fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t)) := by
  obtain ⟨A, hA⟩ := hb
  obtain ⟨B, hB⟩ := hbx
  exact summable_disc hβ0 hβ1 (fun t => abs_periodLoss_le (hA t) (hB t))

/-- Galí (2015), pp. 141–142: **Lagrangian identity**. If a bounded feasible path
`(π⁰, x̂⁰)` satisfies the first-order conditions with a bounded multiplier, then for every
bounded feasible path `(π, x̂)`
`L(π, x̂) = L(π⁰, x̂⁰) + ∑ βᵗ ½((π_t − π⁰_t)² + ϑ(x̂_t − x̂⁰_t)²)`.
The linear terms telescope to zero, using `ξ_{−1} = 0` and `βᵗ ξ_{t−1} → 0`. -/
theorem lagrangian_identity {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u infl₀ x₀ ξ infl x : ℕ → ℝ} (hF₀ : DetFeasible β κ u infl₀ x₀)
    (hFOC : DetFOC κ ϑ Λ infl₀ x₀ ξ) (hb₀ : BddSeq infl₀) (hbx₀ : BddSeq x₀)
    (hbξ : BddSeq ξ) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl) (hbx : BddSeq x) :
    detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ +
      ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) := by
  obtain ⟨A₀, hA₀⟩ := hb₀
  obtain ⟨B₀, hB₀⟩ := hbx₀
  obtain ⟨A, hA⟩ := hb
  obtain ⟨B, hB⟩ := hbx
  obtain ⟨Ξ, hΞ⟩ := hbξ
  have hdA : ∀ t, |infl t - infl₀ t| ≤ A + A₀ := fun t =>
    (abs_sub _ _).trans (add_le_add (hA t) (hA₀ t))
  have hdB : ∀ t, |x t - x₀ t| ≤ B + B₀ := fun t =>
    (abs_sub _ _).trans (add_le_add (hB t) (hB₀ t))
  have hS : Summable (fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t)) :=
    detLoss_summable hβ0.le hβ1 ⟨A, hA⟩ ⟨B, hB⟩
  have hS₀ : Summable (fun t => β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t)) :=
    detLoss_summable hβ0.le hβ1 ⟨A₀, hA₀⟩ ⟨B₀, hB₀⟩
  have hSq : Summable (fun t => β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) :=
    summable_disc hβ0.le hβ1 (fun t => abs_periodLoss_le (hdA t) (hdB t))
  -- the linear part `βᵗ ℓ_t` telescopes: `βᵗ ℓ_t = a_t − a_{t+1}`
  set a : ℕ → ℝ := fun t => β ^ t * (lag ξ t * (infl t - infl₀ t)) with ha
  set ℓ : ℕ → ℝ := fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t) -
    β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t) -
    β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) with hℓ
  have hℓa : ∀ t, ℓ t = a t - a (t + 1) := by
    intro t
    have h1 := hFOC.1 t
    have h2 := hFOC.2 t
    have h3 := hF t
    have h4 := hF₀ t
    simp only [hℓ, ha, lag_succ, periodLoss, pow_succ]
    linear_combination (β ^ t * (x t - x₀ t)) * h1 + (β ^ t * (infl t - infl₀ t)) * h2 -
      (β ^ t * ξ t) * h3 + (β ^ t * ξ t) * h4
  have hℓS : Summable ℓ := (hS.sub hS₀).sub hSq
  have hℓ0 : ∑' t, ℓ t = 0 := by
    have hpart : ∀ N, ∑ t ∈ Finset.range N, ℓ t = -a N := by
      intro N
      rw [Finset.sum_congr rfl (fun t _ => hℓa t), Finset.sum_range_sub']
      simp [ha]
    have haN : Tendsto a atTop (𝓝 0) := by
      have hb' : ∀ N, ‖a N‖ ≤ β ^ N * (|Ξ| * (A + A₀)) := by
        intro N
        have hL : |lag ξ N| ≤ |Ξ| := by
          cases N with
          | zero => simp
          | succ N => exact (hΞ N).trans (le_abs_self Ξ)
        have hval : ‖a N‖ = β ^ N * (|lag ξ N| * |infl N - infl₀ N|) := by
          simp only [ha, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        rw [hval]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hL (hdA N) (abs_nonneg _) (abs_nonneg _)) (pow_nonneg hβ0.le N)
      refine squeeze_zero_norm hb' ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (|Ξ| * (A + A₀))
    have h1 := hℓS.hasSum.tendsto_sum_nat
    simp only [hpart] at h1
    have h2 : Tendsto (fun N => -a N) atTop (𝓝 0) := by simpa using haN.neg
    exact tendsto_nhds_unique h1 h2
  have hsplit : ∀ t, β ^ t * periodLoss ϑ Λ (infl t) (x t) =
      (β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t) +
        β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) + ℓ t := by
    intro t; simp only [hℓ]; ring
  unfold detLoss
  rw [tsum_congr hsplit, (hS₀.add hSq).tsum_add hℓS, hℓ0, add_zero, hS₀.tsum_add hSq]

/-- Galí (2015), pp. 141–142: **Lagrangian sufficiency**. A bounded feasible path satisfying
the first-order conditions with a bounded multiplier minimises the loss among all bounded
feasible paths, strictly: any other bounded feasible path has a strictly larger loss. -/
theorem lagrangian_sufficiency {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u infl₀ x₀ ξ infl x : ℕ → ℝ} (hF₀ : DetFeasible β κ u infl₀ x₀)
    (hFOC : DetFOC κ ϑ Λ infl₀ x₀ ξ) (hb₀ : BddSeq infl₀) (hbx₀ : BddSeq x₀)
    (hbξ : BddSeq ξ) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl) (hbx : BddSeq x) :
    detLoss β ϑ Λ infl₀ x₀ ≤ detLoss β ϑ Λ infl x ∧
      (detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ → infl = infl₀ ∧ x = x₀) := by
  have hid := lagrangian_identity hβ0 hβ1 hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx
  have hnn : ∀ t, 0 ≤ β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) := by
    intro t
    simp only [periodLoss, zero_mul, sub_zero]
    have := pow_pos hβ0 t
    positivity
  refine ⟨?_, fun heq => ?_⟩
  · have h : 0 ≤ ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) :=
      tsum_nonneg hnn
    rw [hid]
    linarith
  · obtain ⟨A₀, hA₀⟩ := hb₀
    obtain ⟨B₀, hB₀⟩ := hbx₀
    obtain ⟨A, hA⟩ := hb
    obtain ⟨B, hB⟩ := hbx
    have hSq : Summable (fun t => β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) :=
      summable_disc hβ0.le hβ1 (fun t => abs_periodLoss_le
        ((abs_sub _ _).trans (add_le_add (hA t) (hA₀ t)))
        ((abs_sub _ _).trans (add_le_add (hB t) (hB₀ t))))
    have h0 : ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) = 0 := by
      linarith
    have hz := (hasSum_zero_iff_of_nonneg hnn).mp (h0 ▸ hSq.hasSum)
    have hpt : ∀ t, infl t - infl₀ t = 0 ∧ x t - x₀ t = 0 := by
      intro t
      have h1 := congrFun hz t
      have hp := pow_pos hβ0 t
      simp only [Pi.zero_apply, mul_eq_zero, hp.ne', false_or, periodLoss] at h1
      have h2 : (infl t - infl₀ t) ^ 2 + ϑ * (x t - x₀ t) ^ 2 = 0 := by linarith
      have h3 : 0 ≤ ϑ * (x t - x₀ t) ^ 2 := by positivity
      have h4 : (infl t - infl₀ t) ^ 2 = 0 := by nlinarith [sq_nonneg (infl t - infl₀ t)]
      have h5 : (x t - x₀ t) ^ 2 = 0 := by
        have : ϑ * (x t - x₀ t) ^ 2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hϑ.ne'
        · exact h
      exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4,
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5⟩
    exact ⟨funext fun t => sub_eq_zero.mp (hpt t).1, funext fun t => sub_eq_zero.mp (hpt t).2⟩

/-- Galí (2015), p. 142, fn. 8, under perfect foresight with an arbitrary bounded cost-push
sequence `u`: **existence** of a bounded feasible path satisfying the first-order conditions
with a bounded multiplier. The price level solves `p̂_t = δ p̂_{t−1} + δ z_t`, where
`z_t = ∑_{k ≥ 0} (δβ)ᵏ (κΛ/ϑ + u_{t+k})` is the forward solution of
`z_t = δβ z_{t+1} + κΛ/ϑ + u_t` (for AR(1) shocks this is (23)). -/
theorem det_commitment_exists {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → ℝ} (hu : BddSeq u) :
    ∃ infl₀ x₀ ξ : ℕ → ℝ, DetFeasible β κ u infl₀ x₀ ∧ DetFOC κ ϑ Λ infl₀ x₀ ξ ∧
      BddSeq infl₀ ∧ BddSeq x₀ ∧ BddSeq ξ := by
  obtain ⟨M, hM⟩ := hu
  set d := del β κ ϑ with hd
  have h0 : 0 < d := del_pos hβ0 hϑ
  have h1 : d < 1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hdb0 : 0 ≤ d * β := by positivity
  have hdb1 : d * β < 1 := by nlinarith
  set W : ℕ → Unit → ℝ := fun t _ => κ * Λ / ϑ + u t with hW
  have hWb : ∀ t ω, |W t ω| ≤ |κ * Λ / ϑ| + M := fun t _ =>
    (abs_add_le _ _).trans (add_le_add le_rfl (hM t))
  have hWa : perfectForesight.Adapted W := fun _ => rfl
  set z : ℕ → ℝ := fun t => perfectForesight.forwardSeries (d * β) W t () with hz
  have hzeq : ∀ t, z t = d * β * z (t + 1) + (κ * Λ / ϑ + u t) := by
    intro t
    have := congrFun (perfectForesight.forwardSeries_solves hdb0 hdb1 hWb hWa t) ()
    exact this
  obtain ⟨Kz, hKz⟩ := perfectForesight.forwardSeries_bounded hdb0 hdb1 hWb
  set P : ℕ → ℝ := backRec d (fun t => d * z t) with hP
  have hPrec : ∀ t, P t = d * lag P t + d * z t := by
    intro t
    cases t with
    | zero => simp [hP, backRec]
    | succ t => rfl
  set K := d * |Kz| / (1 - d)
  have hne : 1 - d ≠ 0 := (by linarith : (0 : ℝ) < 1 - d).ne'
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - d := by linarith
    positivity
  have hPb : ∀ t, |P t| ≤ K := by
    intro t
    induction t with
    | zero =>
      rw [hPrec 0, lag_zero, mul_zero, zero_add, abs_mul, abs_of_pos h0]
      have : |z 0| ≤ |Kz| := (hKz 0 ()).trans (le_abs_self Kz)
      have hKK : d * |Kz| ≤ K := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (mul_nonneg h0.le (abs_nonneg Kz)) h0.le]
      nlinarith
    | succ t ih =>
      rw [hPrec (t + 1), lag_succ]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos h0]
      have : |z (t + 1)| ≤ |Kz| := (hKz (t + 1) ()).trans (le_abs_self Kz)
      have hKK : d * K + d * |Kz| = K := by
        simp only [K]; field_simp; ring
      nlinarith
  have hlagb : ∀ t, |lag P t| ≤ K := by
    intro t
    cases t with
    | zero => simpa using hK0
    | succ t => exact hPb t
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  have hkl : ϑ * (κ * Λ / ϑ) = κ * Λ := by field_simp
  refine ⟨fun t => P t - lag P t, fun t => Λ / ϑ - κ / ϑ * P t, fun t => -P t, ?_, ⟨?_, ?_⟩,
    ⟨K + K, fun t => (abs_sub _ _).trans (add_le_add (hPb t) (hlagb t))⟩,
    ⟨|Λ / ϑ| + |κ / ϑ| * K, fun t => ?_⟩, ⟨K, fun t => by rw [abs_neg]; exact hPb t⟩⟩
  · intro t
    have hp := hPrec t
    have hp' := hPrec (t + 1)
    rw [lag_succ] at hp'
    have hzt := hzeq t
    have hx : ϑ * (Λ / ϑ - κ / ϑ * P t) = Λ - κ * P t := by field_simp
    simp only [lag_succ]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (ϑ - ϑ * β * d + ϑ * β + κ ^ 2) * hp - ϑ * β * hp' - κ * hx +
      ϑ * hzt + hkl + (lag P t + z t) * hk
  · intro t
    field_simp
    ring
  · intro t
    cases t with
    | zero => simp
    | succ t => simp only [lag_succ]; ring
  · refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hPb t

/-- Galí (2015), pp. 141–142, deterministic problem: **the Lagrangian conditions are
necessary and sufficient**. For a bounded cost-push sequence, a bounded feasible path
minimises the loss (17) among all bounded feasible paths if and only if it satisfies the
first-order conditions with some bounded multiplier `ξ` (`ξ_{−1} = 0`). -/
theorem det_optimal_iff {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {u infl x : ℕ → ℝ} (hu : BddSeq u) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl)
    (hbx : BddSeq x) :
    (∀ infl' x', DetFeasible β κ u infl' x' → BddSeq infl' → BddSeq x' →
      detLoss β ϑ Λ infl x ≤ detLoss β ϑ Λ infl' x') ↔
      ∃ ξ, BddSeq ξ ∧ DetFOC κ ϑ Λ infl x ξ := by
  constructor
  · intro hopt
    obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
      det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hu
    have hs := lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx
    have heq : detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ :=
      le_antisymm (hopt infl₀ x₀ hF₀ hb₀ hbx₀) hs.1
    obtain ⟨h1, h2⟩ := hs.2 heq
    subst h1 h2
    exact ⟨ξ, hbξ, hFOC⟩
  · rintro ⟨ξ, hbξ, hFOC⟩ infl' x' hF' hb' hbx'
    exact (lagrangian_sufficiency hβ0 hβ1 hϑ hF hFOC hb hbx hbξ hF' hb' hbx').1

/-- Galí (2015), pp. 141–143, deterministic problem: **existence and uniqueness of the
optimal commitment plan**. For every bounded cost-push sequence there is a bounded feasible
path whose loss is no larger than that of any bounded feasible path, and it is the only
bounded feasible path attaining that loss. -/
theorem det_commitment_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → ℝ} (hu : BddSeq u) :
    ∃ infl₀ x₀ : ℕ → ℝ, DetFeasible β κ u infl₀ x₀ ∧ BddSeq infl₀ ∧ BddSeq x₀ ∧
      ∀ infl x, DetFeasible β κ u infl x → BddSeq infl → BddSeq x →
        detLoss β ϑ Λ infl₀ x₀ ≤ detLoss β ϑ Λ infl x ∧
          (detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ → infl = infl₀ ∧ x = x₀) := by
  obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
    det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hu
  exact ⟨infl₀, x₀, hF₀, hb₀, hbx₀, fun infl x hF hb hbx =>
    lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx⟩

/-- Galí (2015), p. 143: **the linear term makes the optimum non-zero**. Without cost-push
shocks the zero path is feasible, but when `Λ ≠ 0` some bounded feasible path has strictly
smaller loss (with `Λ = 0` the zero path would be optimal: it gives zero loss). -/
theorem zero_path_not_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hΛ : Λ ≠ 0) :
    DetFeasible β κ 0 0 0 ∧ ∃ infl x, DetFeasible β κ 0 infl x ∧ BddSeq infl ∧ BddSeq x ∧
      detLoss β ϑ Λ infl x < detLoss β ϑ Λ 0 0 := by
  have hF0 : DetFeasible β κ 0 0 0 := fun t => by simp
  have hb0 : BddSeq (0 : ℕ → ℝ) := ⟨0, fun t => by simp⟩
  refine ⟨hF0, ?_⟩
  obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
    det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hb0
  refine ⟨infl₀, x₀, hF₀, hb₀, hbx₀, ?_⟩
  have hs := lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF0 hb0 hb0
  refine lt_of_le_of_ne hs.1 fun heq => ?_
  obtain ⟨h1, h2⟩ := hs.2 heq.symm
  have hx := hFOC.1 0
  have hi := hFOC.2 0
  rw [← h1] at hi
  rw [← h2] at hx
  simp only [Pi.zero_apply, lag_zero, zero_add, sub_zero, mul_zero, zero_sub] at hx hi
  rw [hi, mul_zero, neg_zero, zero_sub, neg_eq_zero] at hx
  exact hΛ hx

/-- Galí (2015), p. 143, deterministic problem without cost-push shocks: the commitment path
`π_t = δᵗ (δ/(1 − δβ)) κΛ/ϑ`, `x̂_t = δ^{t+1} Λ/ϑ` is feasible and minimises the loss (17)
among all bounded feasible paths. -/
theorem det_zeroShock_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    DetFeasible β κ 0 (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
        (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) ∧
      ∀ infl x, DetFeasible β κ 0 infl x → BddSeq infl → BddSeq x →
        detLoss β ϑ Λ (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
          (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) ≤ detLoss β ϑ Λ infl x := by
  have hu : perfectForesight.IsAR1 0 (0 : ℕ → Unit → ℝ) :=
    ⟨fun _ => rfl, fun _ => by simp⟩
  have hub : BoundedProc (0 : ℕ → Unit → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨hE, -, ⟨Kp, hKp⟩, ⟨Kx, hKx⟩, ⟨Ki, hKi⟩⟩ :=
    commitment_exists perfectForesight (Λ := Λ) hβ0 hβ1 hκ hϑ (by simp) hu hub
  have hI : ∀ t, commInfl β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t () = del β κ ϑ ^ t * commConst β κ ϑ Λ :=
    fun t => congrFun (commInfl_zeroShock hβ0 hβ1 hκ hϑ t) ()
  have hG : ∀ t, commGap β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t () = del β κ ϑ ^ (t + 1) * Λ / ϑ :=
    fun t => congrFun (commGap_zeroShock hβ0 hβ1 hκ hϑ (by simp) t) ()
  have hF₀ : DetFeasible β κ 0 (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
      (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) := by
    intro t
    have := congrFun (hE.1 t) ()
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    beta_reduce
    rw [← hI t, ← hI (t + 1), ← hG t]
    exact this
  have hFOC : DetFOC κ ϑ Λ (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
      (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ)
      (fun t => commMult β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t ()) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have := congrFun (hE.2.1 t) ()
      beta_reduce
      rw [← hG t]
      exact this
    · have := congrFun (hE.2.2 t) ()
      beta_reduce
      rw [← hI t]
      cases t with
      | zero => exact this
      | succ t => exact this
  have hbξ : BddSeq (fun t => commMult β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t ()) :=
    ⟨Kp, fun t => by simp only [commMult, Pi.neg_apply, abs_neg]; exact hKp t ()⟩
  have hb₀ : BddSeq (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ) :=
    ⟨Ki, fun t => by beta_reduce; rw [← hI t]; exact hKi t ()⟩
  have hbx₀ : BddSeq (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) :=
    ⟨Kx, fun t => by beta_reduce; rw [← hG t]; exact hKx t ()⟩
  exact ⟨hF₀, fun infl x hF hb hbx =>
    (lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx).1⟩

end Gali.DiscretionCommitment.DistortedSS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal discretionary policy under a zero lower bound

Galí (2015), Section 5.4 and Subsection 5.4.1, pp. 144–148.

The economy is deterministic (perfect foresight after the date-0 surprise), so all paths are
plain sequences `ℕ → ℝ`. The non-policy block is the Phillips curve (29) and the dynamic IS
equation (30); the nominal rate obeys the zero lower bound (28). The natural rate (p. 145) is
`−η` on `[0, t_Z]` and `ρ > 0` afterwards. The book calls the drop `ǫ`; we write `η` because
`ε` is the elasticity of substitution in `ϑ = κ / ε` on the same pages (correction C5-5).

## Main results

* `firstBest_rate`, `firstBest_violates_zlb`, `firstBest_eqm_of_nonneg`: the first best
  `x = π = 0` needs `i = rⁿ`, which the ZLB rules out while `rⁿ < 0` (p. 145).
* `periodKKT_sufficient`, `periodKKT_necessary`, `periodOptimal_iff_kkt`: the KKT conditions
  (31)–(33) are necessary and sufficient for the per-period problem;
  `periodOptimal_iff_sol`, `periodOptimal_exists`, `periodOptimal_unique`: its unique solution
  is `x = min υ₁ (−κ υ₀ / (κ² + ϑ))`.
* `zlb_iff_le_ups1`, `periodKKT_iff_book`, `eq33`: (32) is (28) + (30), and the KKT system in the
  book's form with `ξ₂ i = 0`.
* `eq34_matrix`, `eq34_iff`: the binding-ZLB system (34) with the matrices `A`, `B`.
* `Amat_pos`, `Bvec_pos`, `backState_neg`: the sign lemma — `A`, `B` entrywise positive, hence
  `x_t < 0`, `π_t < 0` on `[0, t_Z]`, so `ξ₂,t > 0` (p. 147).
* `disc_exists`: the path of p. 147 (`i = 0`, (34) on `[0, t_Z]`; `i = ρ`, `x = π = 0` after)
  is a discretionary equilibrium. `disc_unique`: it is the only discretionary equilibrium in
  which `(x, π)` converges to the target `(0, 0)`.
* `deflation_discEq`, `deflation_bounded`, `deflation_ne_disc`: correction — boundedness alone
  does not give uniqueness. The deflationary steady state `π = −ρ`, `i = 0` after `t_Z` (glued
  to the binding phase) is another bounded discretionary equilibrium, so the book's "from
  `t_Z + 1` onward `i_t = ρ`" (p. 146) is a selection (footnote 10's rule), not an implication.
-/

namespace Gali.DiscretionCommitment.ZLBDiscretion

/-! ## The setup, eqs. (28)–(30) -/

/-- Galí (2015), p. 145: the natural rate path, `−η` for `t ≤ t_Z` and `ρ` afterwards (the book's
drop `ǫ` is renamed `η`, C5-5). -/
noncomputable def natRate (ρ η : ℝ) (tZ t : ℕ) : ℝ := if t ≤ tZ then -η else ρ

/-- Galí (2015), p. 145: the natural rate on the shock interval. -/
theorem natRate_of_le {ρ η : ℝ} {tZ t : ℕ} (ht : t ≤ tZ) : natRate ρ η tZ t = -η := by
  simp [natRate, ht]

/-- Galí (2015), p. 145: the natural rate after the shock interval. -/
theorem natRate_of_lt {ρ η : ℝ} {tZ t : ℕ} (ht : tZ < t) : natRate ρ η tZ t = ρ := by
  simp [natRate, Nat.not_le.mpr ht]

/-- Galí (2015), eq. (29), p. 145: the (deterministic) New Keynesian Phillips curve. -/
def NKPC (β κ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : Prop := π t = β * π (t + 1) + κ * x t

/-- Galí (2015), eq. (30), p. 145: the dynamic IS equation. -/
def DIS (σ : ℝ) (rn x π i : ℕ → ℝ) (t : ℕ) : Prop :=
  x t = x (t + 1) - (1 / σ) * (i t - π (t + 1) - rn t)

/-- Galí (2015), p. 152: the nominal rate implied by the dynamic IS equation,
`i_t = rⁿ_t + π_{t+1} + σ (x_{t+1} − x_t)`. -/
noncomputable def impliedRate (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  rn t + π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), eq. (30) and p. 152: the dynamic IS equation pins down the nominal rate. -/
theorem dis_iff {σ : ℝ} (hσ : σ ≠ 0) {rn x π i : ℕ → ℝ} {t : ℕ} :
    DIS σ rn x π i t ↔ i t = impliedRate σ rn x π t := by
  unfold DIS impliedRate
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), p. 145: the first best `x = π = 0` satisfies the IS equation only with
`i_t = rⁿ_t`. -/
theorem firstBest_rate {σ : ℝ} (hσ : σ ≠ 0) {rn i : ℕ → ℝ} {t : ℕ}
    (h : DIS σ rn (fun _ => 0) (fun _ => 0) i t) : i t = rn t := by
  rw [dis_iff hσ] at h
  simp [h, impliedRate]

/-- Galí (2015), p. 145: the ZLB rules out the first best while the natural rate is negative. -/
theorem firstBest_violates_zlb {σ ρ η : ℝ} (hσ : σ ≠ 0) (hη : 0 < η) {tZ t : ℕ} (ht : t ≤ tZ)
    {i : ℕ → ℝ} :
    ¬ (DIS σ (natRate ρ η tZ) (fun _ => 0) (fun _ => 0) i t ∧ 0 ≤ i t) := by
  rintro ⟨h, hi⟩
  have := firstBest_rate hσ h
  rw [natRate_of_le ht] at this
  linarith

/-- Galí (2015), p. 145 (and Ch. 4): whenever `rⁿ_t ≥ 0`, the first best with `i_t = rⁿ_t` solves
(29), (30) and the ZLB (28). -/
theorem firstBest_eqm_of_nonneg {β κ σ : ℝ} (hσ : σ ≠ 0) {rn : ℕ → ℝ} {t : ℕ}
    (h : 0 ≤ rn t) :
    NKPC β κ (fun _ => 0) (fun _ => 0) t ∧ DIS σ rn (fun _ => 0) (fun _ => 0) rn t ∧
      0 ≤ rn t := by
  refine ⟨by simp [NKPC], ?_, h⟩
  rw [dis_iff hσ]
  simp [impliedRate]

/-! ## The per-period problem (31)–(33) -/

/-- Galí (2015), eqs. (31)–(32), p. 146: feasibility in the per-period problem,
`π = κ x + υ₀` and `x ≤ υ₁`. -/
def PeriodFeasible (κ υ0 υ1 x π : ℝ) : Prop := π = κ * x + υ0 ∧ x ≤ υ1

/-- Galí (2015), p. 146: `(x, π)` minimises `π² + ϑ x²` subject to (31)–(32). -/
def PeriodOptimal (κ ϑ υ0 υ1 x π : ℝ) : Prop :=
  PeriodFeasible κ υ0 υ1 x π ∧
    ∀ x' π', PeriodFeasible κ υ0 υ1 x' π' → π ^ 2 + ϑ * x ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2

/-- Galí (2015), p. 146: the KKT system of the per-period problem — feasibility, the two
first-order conditions `π + ξ₁ = 0`, `ϑ x − κ ξ₁ + ξ₂ = 0`, `ξ₂ ≥ 0` and slackness. -/
def PeriodKKT (κ ϑ υ0 υ1 x π ξ1 ξ2 : ℝ) : Prop :=
  PeriodFeasible κ υ0 υ1 x π ∧ π + ξ1 = 0 ∧ ϑ * x - κ * ξ1 + ξ2 = 0 ∧ 0 ≤ ξ2 ∧
    ξ2 * (υ1 - x) = 0

/-- Galí (2015), p. 146: the loss change along the constraint line,
`(κ x' + υ₀)² + ϑ x'² − (κ x + υ₀)² − ϑ x² = 2 h c + h² (κ² + ϑ)` with `h = x' − x`,
`c = κ π + ϑ x`. -/
theorem period_loss_change (κ ϑ υ0 x x' : ℝ) :
    (κ * x' + υ0) ^ 2 + ϑ * x' ^ 2 - ((κ * x + υ0) ^ 2 + ϑ * x ^ 2) =
      2 * (x' - x) * (κ * (κ * x + υ0) + ϑ * x) + (x' - x) ^ 2 * (κ ^ 2 + ϑ) := by
  ring

/-- Galí (2015), (31)–(33), p. 146: SUFFICIENCY of the KKT conditions for the per-period
problem (convexity of the loss, linearity of the constraints). -/
theorem periodKKT_sufficient {κ ϑ υ0 υ1 x π ξ1 ξ2 : ℝ} (hϑ : 0 ≤ ϑ)
    (h : PeriodKKT κ ϑ υ0 υ1 x π ξ1 ξ2) : PeriodOptimal κ ϑ υ0 υ1 x π := by
  obtain ⟨⟨hπ, hx⟩, h1, h2, h3, h4⟩ := h
  refine ⟨⟨hπ, hx⟩, fun x' π' hf => ?_⟩
  obtain ⟨hπ', hx'⟩ := hf
  have e1 : ξ1 = -π := by linarith
  have e2 : ξ2 = κ * ξ1 - ϑ * x := by linarith
  subst hπ hπ' e1
  rw [e2] at h3 h4
  have key := period_loss_change κ ϑ υ0 x x'
  have hle : 0 ≤ (κ * -(κ * x + υ0) - ϑ * x) * (υ1 - x') :=
    mul_nonneg h3 (by linarith)
  nlinarith [sq_nonneg (x' - x), mul_nonneg (sq_nonneg (x' - x)) hϑ]

/-- Galí (2015), (31)–(33), p. 146: NECESSITY of the KKT conditions for the per-period problem,
with multipliers `ξ₁ = −π`, `ξ₂ = −(κ π + ϑ x)`. -/
theorem periodKKT_necessary {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ)
    (h : PeriodOptimal κ ϑ υ0 υ1 x π) :
    PeriodKKT κ ϑ υ0 υ1 x π (-π) (-(κ * π + ϑ * x)) := by
  obtain ⟨⟨hπ, hx⟩, hopt⟩ := h
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  subst hπ
  set c := κ * (κ * x + υ0) + ϑ * x with hc
  -- `c ≤ 0`: otherwise lowering `x` reduces the loss
  have hc0 : c ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have hfe : PeriodFeasible κ υ0 υ1 (x - c / (κ ^ 2 + ϑ)) (κ * (x - c / (κ ^ 2 + ϑ)) + υ0) :=
      ⟨rfl, by have : 0 < c / (κ ^ 2 + ϑ) := div_pos hneg hD; linarith⟩
    have h1 := hopt _ _ hfe
    have h2 := period_loss_change κ ϑ υ0 x (x - c / (κ ^ 2 + ϑ))
    rw [← hc] at h2
    have h3 : 2 * (x - c / (κ ^ 2 + ϑ) - x) * c + (x - c / (κ ^ 2 + ϑ) - x) ^ 2 * (κ ^ 2 + ϑ)
        = -(c ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have h4 : 0 < c ^ 2 / (κ ^ 2 + ϑ) := div_pos (by positivity) hD
    linarith
  -- slackness: if `x < υ₁` and `c < 0`, raising `x` reduces the loss
  have hslack : -c * (υ1 - x) = 0 := by
    rcases eq_or_lt_of_le hx with hxe | hxl
    · rw [hxe]; ring
    rcases eq_or_lt_of_le hc0 with hce | hcl
    · rw [hce]; ring
    exfalso
    set hstep := min (υ1 - x) (-c / (κ ^ 2 + ϑ)) with hhs
    have hpos : 0 < hstep := lt_min (by linarith) (div_pos (by linarith) hD)
    have hle1 : hstep ≤ υ1 - x := min_le_left _ _
    have hle2 : hstep ≤ -c / (κ ^ 2 + ϑ) := min_le_right _ _
    have hle2' : hstep * (κ ^ 2 + ϑ) ≤ -c := by
      rwa [le_div_iff₀ hD] at hle2
    have hfe : PeriodFeasible κ υ0 υ1 (x + hstep) (κ * (x + hstep) + υ0) :=
      ⟨rfl, by linarith⟩
    have h1 := hopt _ _ hfe
    have h2 := period_loss_change κ ϑ υ0 x (x + hstep)
    rw [← hc] at h2
    have h5 : hstep * (2 * c + hstep * (κ ^ 2 + ϑ)) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    nlinarith
  refine ⟨⟨rfl, hx⟩, by ring, by ring, by linarith, by linarith⟩

/-- Galí (2015), (31)–(33), p. 146: the KKT conditions are necessary and sufficient. -/
theorem periodOptimal_iff_kkt {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ) :
    PeriodOptimal κ ϑ υ0 υ1 x π ↔ ∃ ξ1 ξ2, PeriodKKT κ ϑ υ0 υ1 x π ξ1 ξ2 :=
  ⟨fun h => ⟨_, _, periodKKT_necessary hϑ h⟩,
    fun ⟨_, _, h⟩ => periodKKT_sufficient hϑ.le h⟩

/-- Galí (2015), p. 146: the explicit solution of the per-period problem,
`x = min υ₁ (−κ υ₀ / (κ² + ϑ))` (the unconstrained optimum, capped by the ZLB). -/
noncomputable def periodSol (κ ϑ υ0 υ1 : ℝ) : ℝ := min υ1 (-(κ * υ0) / (κ ^ 2 + ϑ))

/-- Galí (2015), p. 146: `(x, π)` solves the per-period problem iff `x = periodSol` and
`π = κ x + υ₀`. -/
theorem periodOptimal_iff_sol {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ) :
    PeriodOptimal κ ϑ υ0 υ1 x π ↔ x = periodSol κ ϑ υ0 υ1 ∧ π = κ * x + υ0 := by
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  constructor
  · intro h
    obtain ⟨⟨hπ, hx⟩, -, -, h3, h4⟩ := periodKKT_necessary hϑ h
    refine ⟨?_, hπ⟩
    subst hπ
    have hxle : x ≤ -(κ * υ0) / (κ ^ 2 + ϑ) := by
      rw [le_div_iff₀ hD]; nlinarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · have hxe : x = -(κ * υ0) / (κ ^ 2 + ϑ) := by
        field_simp; linarith
      unfold periodSol
      rw [min_eq_right (hxe ▸ hx)]
      exact hxe
    · have hxe : x = υ1 := by linarith
      unfold periodSol
      rw [min_eq_left (hxe ▸ hxle)]
      exact hxe
  · rintro ⟨hx, hπ⟩
    refine periodKKT_sufficient hϑ.le (ξ1 := -π) (ξ2 := -(κ * π + ϑ * x)) ?_
    have hle1 : x ≤ υ1 := hx ▸ min_le_left _ _
    have hle2 : x ≤ -(κ * υ0) / (κ ^ 2 + ϑ) := hx ▸ min_le_right _ _
    rw [le_div_iff₀ hD] at hle2
    refine ⟨⟨hπ, hle1⟩, by ring, by ring, by rw [hπ]; nlinarith, ?_⟩
    unfold periodSol at hx
    rcases le_total υ1 (-(κ * υ0) / (κ ^ 2 + ϑ)) with hm | hm
    · rw [min_eq_left hm] at hx
      rw [hx]; ring
    · rw [min_eq_right hm] at hx
      have : κ * π + ϑ * x = 0 := by
        rw [hπ, hx]; field_simp; ring
      rw [this]; ring

/-- Galí (2015), p. 146: the per-period problem has a solution. -/
theorem periodOptimal_exists {κ ϑ : ℝ} (hϑ : 0 < ϑ) (υ0 υ1 : ℝ) :
    PeriodOptimal κ ϑ υ0 υ1 (periodSol κ ϑ υ0 υ1) (κ * periodSol κ ϑ υ0 υ1 + υ0) :=
  (periodOptimal_iff_sol hϑ).mpr ⟨rfl, rfl⟩

/-- Galí (2015), p. 146: the solution of the per-period problem is unique. -/
theorem periodOptimal_unique {κ ϑ υ0 υ1 x π x' π' : ℝ} (hϑ : 0 < ϑ)
    (h : PeriodOptimal κ ϑ υ0 υ1 x π) (h' : PeriodOptimal κ ϑ υ0 υ1 x' π') :
    x = x' ∧ π = π' := by
  rw [periodOptimal_iff_sol hϑ] at h h'
  obtain ⟨hx, hπ⟩ := h
  obtain ⟨hx', hπ'⟩ := h'
  refine ⟨hx.trans hx'.symm, ?_⟩
  rw [hπ, hπ', hx, hx']

/-! ## The per-period problem inside the model -/

/-- Galí (2015), p. 146: `υ₀,t ≡ β π_{t+1}`. -/
def ups0 (β : ℝ) (π : ℕ → ℝ) (t : ℕ) : ℝ := β * π (t + 1)

/-- Galí (2015), p. 146: `υ₁,t ≡ x_{t+1} + (1/σ)(π_{t+1} + rⁿ_t)`. -/
noncomputable def ups1 (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  x (t + 1) + (π (t + 1) + rn t) / σ

/-- Galí (2015), p. 146: the implied rate is `σ (υ₁,t − x_t)`. -/
theorem impliedRate_eq {σ : ℝ} (hσ : σ ≠ 0) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = σ * (ups1 σ rn x π t - x t) := by
  unfold impliedRate ups1
  field_simp
  ring

/-- Galí (2015), eq. (31), p. 146: the Phillips curve (29) is (31) with `υ₀,t = β π_{t+1}`. -/
theorem nkpc_iff_eq31 {β κ : ℝ} {x π : ℕ → ℝ} {t : ℕ} :
    NKPC β κ x π t ↔ π t = κ * x t + ups0 β π t := by
  unfold NKPC ups0
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (32), p. 146: given the IS equation (30), the ZLB (28) is `x_t ≤ υ₁,t`. -/
theorem zlb_iff_le_ups1 {σ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ} {t : ℕ}
    (hD : DIS σ rn x π i t) : 0 ≤ i t ↔ x t ≤ ups1 σ rn x π t := by
  rw [dis_iff hσ.ne', impliedRate_eq hσ.ne'] at hD
  rw [hD]
  constructor
  · intro h
    have := (mul_nonneg_iff_of_pos_left hσ).mp h
    linarith
  · intro h
    exact mul_nonneg hσ.le (by linarith)

/-- Galí (2015), p. 146: given (30), the KKT system of the per-period problem is the book's
system — the FOCs, `ξ₂ ≥ 0`, `i ≥ 0`, `ξ₂ i = 0` — together with (29). -/
theorem periodKKT_iff_book {β κ σ ϑ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ} {t : ℕ}
    (hD : DIS σ rn x π i t) (ξ1 ξ2 : ℝ) :
    PeriodKKT κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) ξ1 ξ2 ↔
      (NKPC β κ x π t ∧ π t + ξ1 = 0 ∧ ϑ * x t - κ * ξ1 + ξ2 = 0 ∧ 0 ≤ ξ2 ∧ 0 ≤ i t ∧
        ξ2 * i t = 0) := by
  have hi : i t = σ * (ups1 σ rn x π t - x t) := by
    rw [dis_iff hσ.ne', impliedRate_eq hσ.ne'] at hD; exact hD
  have hz := zlb_iff_le_ups1 hσ hD
  unfold PeriodKKT PeriodFeasible
  rw [← nkpc_iff_eq31, hz]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3, h4, h5⟩
    refine ⟨h0, h2, h3, h4, h1, ?_⟩
    rw [hi, mul_left_comm, h5, mul_zero]
  · rintro ⟨h0, h2, h3, h4, h1, h5⟩
    refine ⟨⟨h0, h1⟩, h2, h3, h4, ?_⟩
    rw [hi, mul_left_comm] at h5
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h hσ.ne'
    · exact h

/-- Galí (2015), eq. (33), p. 146: the two first-order conditions combine to
`ϑ x_t = −κ π_t − ξ₂,t`. -/
theorem eq33 {κ ϑ x π ξ1 ξ2 : ℝ} (h1 : π + ξ1 = 0) (h2 : ϑ * x - κ * ξ1 + ξ2 = 0) :
    ϑ * x = -κ * π - ξ2 := by
  have : ξ1 = -π := by linarith
  subst this
  linarith

/-- Galí (2015), p. 146: a discretionary equilibrium under the ZLB — at every date the IS
equation (30) holds and `(x_t, π_t)` solves the per-period problem (31)–(32), taking
`υ₀,t, υ₁,t` (i.e. the future path) as given. -/
def DiscEq (β κ σ ϑ : ℝ) (rn x π i : ℕ → ℝ) : Prop :=
  ∀ t, DIS σ rn x π i t ∧ PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t)

/-- Galí (2015), pp. 145–146: a discretionary equilibrium satisfies (29) and the ZLB (28). -/
theorem DiscEq.nkpc_zlb {β κ σ ϑ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ}
    (h : DiscEq β κ σ ϑ rn x π i) (t : ℕ) : NKPC β κ x π t ∧ 0 ≤ i t := by
  obtain ⟨hD, ⟨h1, h2⟩, -⟩ := h t
  exact ⟨nkpc_iff_eq31.mpr h1, (zlb_iff_le_ups1 hσ hD).mpr h2⟩


/-- Galí (2015), p. 146: at a date where the ZLB binds (`x_t = υ₁,t`, i.e. `i_t = 0`) and the
Phillips curve holds, `κ π_t + ϑ x_t ≤ 0` (i.e. `ξ₂,t ≥ 0` in (33)) makes `(x_t, π_t)` optimal. -/
theorem binding_optimal {β κ σ ϑ : ℝ} (hϑ : 0 ≤ ϑ) {rn x π : ℕ → ℝ} {t : ℕ}
    (hb : x t = ups1 σ rn x π t) (hN : NKPC β κ x π t) (hs : κ * π t + ϑ * x t ≤ 0) :
    PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) := by
  refine periodKKT_sufficient hϑ (ξ1 := -π t) (ξ2 := -(κ * π t + ϑ * x t)) ?_
  refine ⟨⟨nkpc_iff_eq31.mp hN, hb.le⟩, by ring, by ring, by linarith, ?_⟩
  rw [← hb]; ring

/-- Galí (2015), pp. 146–147: if `x_{t+1} = π_{t+1} = 0` and `rⁿ_t ≥ 0`, then `x_t = π_t = 0`
solves the per-period problem (the first best, with `i_t = rⁿ_t`). -/
theorem slack_zero_optimal {β κ σ ϑ : ℝ} (hσ : 0 < σ) (hϑ : 0 ≤ ϑ) {rn x π : ℕ → ℝ} {t : ℕ}
    (hx : x t = 0) (hπ : π t = 0) (hx1 : x (t + 1) = 0) (hπ1 : π (t + 1) = 0)
    (hr : 0 ≤ rn t) :
    PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) := by
  refine periodKKT_sufficient hϑ (ξ1 := 0) (ξ2 := 0) ?_
  unfold ups0 ups1
  rw [hx, hπ, hx1, hπ1]
  refine ⟨⟨by ring, ?_⟩, by ring, by ring, le_rfl, by ring⟩
  simp only [zero_add]
  exact div_nonneg hr hσ.le

/-! ## The binding-ZLB system (34) -/

/-- Galí (2015), eq. (34), p. 147: one backward step of the binding-ZLB system,
`(x_t, π_t) = A (x_{t+1}, π_{t+1}) − B η`. -/
noncomputable def backStep (β κ σ η : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 / σ - η / σ, κ * s.1 + (β + κ / σ) * s.2 - κ * η / σ)

/-- Galí (2015), eq. (34), p. 147: `n` backward steps from the terminal state `s_T`. -/
noncomputable def backState (β κ σ η : ℝ) (sT : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sT
  | n + 1 => backStep β κ σ η (backState β κ σ η sT n)

/-- Galí (2015), p. 147: the matrix `A ≡ [1, 1/σ; κ, β + κ/σ]`. -/
noncomputable def Amat (β κ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), p. 147: the vector `B ≡ [1/σ; κ/σ]`. -/
noncomputable def Bvec (κ σ : ℝ) : Fin 2 → ℝ := ![1 / σ, κ / σ]

/-- Galí (2015), eq. (34), p. 147: `backStep` is the matrix recursion `A s − B η`. -/
theorem eq34_matrix (β κ σ η : ℝ) (s : ℝ × ℝ) :
    ![(backStep β κ σ η s).1, (backStep β κ σ η s).2] =
      Matrix.mulVec (Amat β κ σ) ![s.1, s.2] - η • Bvec κ σ := by
  ext j
  fin_cases j <;>
    simp [backStep, Amat, Bvec] <;> ring

/-- Galí (2015), eq. (34), p. 147: on `[0, t_Z]`, the Phillips curve (29) and the IS equation
(30) with `i_t = 0` are exactly the backward system (34). -/
theorem eq34_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : t ≤ tZ) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) := by
  rw [dis_iff hσ]
  unfold NKPC impliedRate backStep
  rw [natRate_of_le ht, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t = x (t + 1) + π (t + 1) / σ - η / σ := by
      rw [h3] at h2
      field_simp
      linarith
    refine ⟨h3, hx, ?_⟩
    simp only
    rw [h1, hx]
    ring
  · rintro ⟨h3, hx, hπ⟩
    simp only at hx hπ
    refine ⟨?_, ?_, h3⟩
    · rw [hπ, hx]; ring
    · rw [h3, hx]; field_simp; ring

/-- Galí (2015), p. 147: the entries of `A` are positive. -/
theorem Amat_pos {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (i j : Fin 2) :
    0 < Amat β κ σ i j := by
  fin_cases i <;> fin_cases j
  · change (0 : ℝ) < 1; exact one_pos
  · change (0 : ℝ) < 1 / σ; positivity
  · change (0 : ℝ) < κ; exact hκ
  · change (0 : ℝ) < β + κ / σ; positivity

/-- Galí (2015), p. 147: the entries of `B` are positive. -/
theorem Bvec_pos {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (i : Fin 2) : 0 < Bvec κ σ i := by
  fin_cases i
  · change (0 : ℝ) < 1 / σ; positivity
  · change (0 : ℝ) < κ / σ; positivity

/-- Galí (2015), p. 147: the sign lemma, one step — with `A, B` entrywise positive and
`η > 0`, a nonpositive `(x_{t+1}, π_{t+1})` gives a strictly negative `(x_t, π_t)`. -/
theorem backStep_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {s : ℝ × ℝ} (h1 : s.1 ≤ 0) (h2 : s.2 ≤ 0) :
    (backStep β κ σ η s).1 < 0 ∧ (backStep β κ σ η s).2 < 0 := by
  unfold backStep
  have a1 : s.2 / σ ≤ 0 := div_nonpos_iff.mpr (Or.inr ⟨h2, hσ.le⟩)
  have a2 : 0 < η / σ := div_pos hη hσ
  have a3 : κ * s.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ.le h1
  have a4 : (β + κ / σ) * s.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
  have a5 : 0 < κ * η / σ := by positivity
  exact ⟨by simp only; linarith, by simp only; linarith⟩

/-- Galí (2015), p. 147: the sign lemma — from a nonpositive terminal state, every backward
iterate of (34) is nonpositive. -/
theorem backState_nonpos {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (n : ℕ) :
    (backState β κ σ η sT n).1 ≤ 0 ∧ (backState β κ σ η sT n).2 ≤ 0 := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
    have := backStep_neg hβ hκ hσ hη ih.1 ih.2
    exact ⟨this.1.le, this.2.le⟩

/-- Galí (2015), p. 147: the sign lemma — from a nonpositive terminal state (e.g. `0`), every
backward iterate of (34) is strictly negative. -/
theorem backState_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (n : ℕ) :
    (backState β κ σ η sT (n + 1)).1 < 0 ∧ (backState β κ σ η sT (n + 1)).2 < 0 := by
  have := backState_nonpos hβ hκ hσ hη h1 h2 n
  exact backStep_neg hβ hκ hσ hη this.1 this.2

/-- Galí (2015), p. 147: the path solving (34) backward on `[0, t_Z]` from the terminal state
`s_T` at `t_Z + 1`, and equal to `s_T` after `t_Z`. -/
noncomputable def zlbPath (β κ σ η : ℝ) (tZ : ℕ) (sT : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η sT (tZ + 1 - t) else sT

/-- Galí (2015), eq. (34), p. 147: on `[0, t_Z]` the path obeys (34). -/
theorem zlbPath_of_le {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : t ≤ tZ) :
    zlbPath β κ σ η tZ sT t = backStep β κ σ η (zlbPath β κ σ η tZ sT (t + 1)) := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 := by omega
  simp only [ht, ↓reduceIte, e, backState]
  by_cases h : t + 1 ≤ tZ
  · simp only [h, ↓reduceIte]
  · have e2 : tZ + 1 - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e2, backState]

/-- Galí (2015), p. 147: after `t_Z` the path is at its terminal state. -/
theorem zlbPath_of_lt {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : tZ < t) :
    zlbPath β κ σ η tZ sT t = sT := by
  simp [zlbPath, Nat.not_le.mpr ht]

/-- Galí (2015), p. 147: from a nonpositive terminal state the path is strictly negative on
`[0, t_Z]`. -/
theorem zlbPath_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {tZ t : ℕ} {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (ht : t ≤ tZ) :
    (zlbPath β κ σ η tZ sT t).1 < 0 ∧ (zlbPath β κ σ η tZ sT t).2 < 0 := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ - t) + 1 := by omega
  simp only [ht, ↓reduceIte, e]
  exact backState_neg hβ hκ hσ hη h1 h2 _

/-- Galí (2015), pp. 146–147: the glued path is a discretionary equilibrium on `[0, t_Z]`, with
`i_t = 0` there, whenever its terminal state is nonpositive. -/
theorem zlbPath_binding {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) {tZ t : ℕ} {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0)
    (ht : t ≤ tZ) :
    PeriodOptimal κ ϑ (ups0 β (fun s => (zlbPath β κ σ η tZ sT s).2) t)
        (ups1 σ (natRate ρ η tZ) (fun s => (zlbPath β κ σ η tZ sT s).1)
          (fun s => (zlbPath β κ σ η tZ sT s).2) t)
        (zlbPath β κ σ η tZ sT t).1 (zlbPath β κ σ η tZ sT t).2 ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (zlbPath β κ σ η tZ sT s).1)
        (fun s => (zlbPath β κ σ η tZ sT s).2) t = 0 := by
  have hstep := zlbPath_of_le (β := β) (κ := κ) (σ := σ) (η := η) (sT := sT) ht
  have hneg := zlbPath_neg hβ hκ hσ hη h1 h2 ht
  have hx : (zlbPath β κ σ η tZ sT t).1 =
      (zlbPath β κ σ η tZ sT (t + 1)).1 + (zlbPath β κ σ η tZ sT (t + 1)).2 / σ - η / σ := by
    rw [hstep]; rfl
  have hπ : (zlbPath β κ σ η tZ sT t).2 = κ * (zlbPath β κ σ η tZ sT (t + 1)).1 +
      (β + κ / σ) * (zlbPath β κ σ η tZ sT (t + 1)).2 - κ * η / σ := by
    rw [hstep]; rfl
  constructor
  · refine binding_optimal hϑ.le ?_ ?_ ?_
    · simp only [ups1, natRate_of_le ht]
      rw [hx]; ring
    · simp only [NKPC]
      rw [hπ, hx]; ring
    · nlinarith [hneg.1, hneg.2]
  · simp only [impliedRate, natRate_of_le ht]
    rw [hx]; field_simp; ring

/-! ## Existence and uniqueness of the discretionary equilibrium -/

/-- Galí (2015), p. 147: the discretionary output gap (34) on `[0, t_Z]`, `0` afterwards. -/
noncomputable def discX (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).1

/-- Galí (2015), p. 147: the discretionary inflation path (34) on `[0, t_Z]`, `0` afterwards. -/
noncomputable def discPi (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).2

/-- Galí (2015), pp. 146–147: the discretionary nominal rate, from the IS equation. -/
noncomputable def discI (β κ σ ρ η : ℝ) (tZ : ℕ) : ℕ → ℝ :=
  impliedRate σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ)

/-- Galí (2015), pp. 146–147: EXISTENCE — the path of p. 147 is a discretionary equilibrium
under the ZLB. On `[0, t_Z]`: `i_t = 0`, `x_t < 0`, `π_t < 0`, and `ξ₂,t = −(κ π_t + ϑ x_t) > 0`
(consistent with a binding ZLB); after `t_Z`: `x_t = π_t = 0` and `i_t = ρ`. -/
theorem disc_exists {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    DiscEq β κ σ ϑ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ)
        (discI β κ σ ρ η tZ) ∧
      (∀ t, t ≤ tZ → discX β κ σ η tZ t < 0 ∧ discPi β κ σ η tZ t < 0 ∧
        discI β κ σ ρ η tZ t = 0 ∧
        0 < -(κ * discPi β κ σ η tZ t + ϑ * discX β κ σ η tZ t)) ∧
      (∀ t, tZ < t → discX β κ σ η tZ t = 0 ∧ discPi β κ σ η tZ t = 0 ∧
        discI β κ σ ρ η tZ t = ρ) := by
  have hafter : ∀ t, tZ < t → discX β κ σ η tZ t = 0 ∧ discPi β κ σ η tZ t = 0 := by
    intro t ht
    simp [discX, discPi, zlbPath_of_lt ht]
  have hbind := fun t (ht : t ≤ tZ) =>
    zlbPath_binding (ϑ := ϑ) (ρ := ρ) hβ hκ hσ hϑ hη (sT := (0, 0)) le_rfl le_rfl ht
  refine ⟨fun t => ⟨(dis_iff hσ.ne').mpr rfl, ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).1
    · exact slack_zero_optimal hσ hϑ.le (hafter t ht).1 (hafter t ht).2
        (hafter (t + 1) (by omega)).1 (hafter (t + 1) (by omega)).2
        (by rw [natRate_of_lt ht]; exact hρ.le)
  · have hneg := zlbPath_neg hβ hκ hσ hη (sT := (0, 0)) le_rfl le_rfl ht
    refine ⟨hneg.1, hneg.2, (hbind t ht).2, ?_⟩
    have := mul_neg_of_pos_of_neg hκ hneg.2
    have := mul_neg_of_pos_of_neg hϑ hneg.1
    simp only [discX, discPi]
    linarith
  · refine ⟨(hafter t ht).1, (hafter t ht).2, ?_⟩
    simp only [discI, impliedRate, natRate_of_lt ht, (hafter t ht).1,
      (hafter (t + 1) (by omega)).1, (hafter (t + 1) (by omega)).2]
    ring

/-- Galí (2015), p. 147: backward induction — a property holding from some date `N` on and
propagating from `t + 1` to `t` holds at every date. -/
theorem down_induction {P : ℕ → Prop} (N : ℕ) (hN : ∀ t, N ≤ t → P t)
    (hstep : ∀ t, P (t + 1) → P t) (t : ℕ) : P t := by
  have key : ∀ n t, N ≤ t + n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact hN t (by omega)
    | succ n ih => intro t ht; exact hstep t (ih (t + 1) (by omega))
  exact key N t (by omega)

/-- Galí (2015), pp. 146–147: UNIQUENESS — the path of p. 147 is the only discretionary
equilibrium under the ZLB in which `(x_t, π_t)` converges to the target `(0, 0)`.
(Convergence cannot be weakened to boundedness: see `deflation_discEq`.) -/
theorem disc_unique {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π i : ℕ → ℝ}
    (h : DiscEq β κ σ ϑ (natRate ρ η tZ) x π i)
    (hx : Filter.Tendsto x Filter.atTop (nhds 0)) (hπ : Filter.Tendsto π Filter.atTop (nhds 0)) :
    x = discX β κ σ η tZ ∧ π = discPi β κ σ η tZ ∧ i = discI β κ σ ρ η tZ := by
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  set lam := β * ϑ / (κ ^ 2 + ϑ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hD]
    nlinarith [sq_pos_of_pos hκ]
  -- Step A: eventually the ZLB is slack
  have hlim : Filter.Tendsto (fun t => x (t + 1) + (π (t + 1) + ρ) / σ +
      κ * (β * π (t + 1)) / (κ ^ 2 + ϑ)) Filter.atTop (nhds (0 + (0 + ρ) / σ + κ * (β * 0) /
        (κ ^ 2 + ϑ))) := by
    have hx1 := hx.comp (Filter.tendsto_add_atTop_nat 1)
    have hπ1 := hπ.comp (Filter.tendsto_add_atTop_nat 1)
    refine ((hx1.add ((hπ1.add_const ρ).div_const σ)).add
      (((hπ1.const_mul β).const_mul κ).div_const _))
  have hpos : (0 : ℝ) < 0 + (0 + ρ) / σ + κ * (β * 0) / (κ ^ 2 + ϑ) := by
    simp only [zero_add, mul_zero, zero_div, add_zero]
    exact div_pos hρ hσ
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds hpos))
  set N := max T (tZ + 1) with hN
  have hslack : ∀ t, N ≤ t → x t = -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) ∧
      π t = lam * π (t + 1) := by
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htZ : tZ < t := by have := le_max_right T (tZ + 1); omega
    have hlt := hT t htT
    obtain ⟨hxs, hπs⟩ := (periodOptimal_iff_sol hϑ).mp (h t).2
    have hlt' : -(κ * ups0 β π t) / (κ ^ 2 + ϑ) < ups1 σ (natRate ρ η tZ) x π t := by
      simp only [ups0, ups1, natRate_of_lt htZ]
      have : -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) =
          -(κ * (β * π (t + 1)) / (κ ^ 2 + ϑ)) := by ring
      linarith
    have hxe : x t = -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) := by
      rw [hxs, periodSol, min_eq_right hlt'.le]; rfl
    refine ⟨hxe, ?_⟩
    rw [hπs, hxe, hlam, ups0]
    field_simp
    ring
  -- Step B: from `N` on, `π = 0` and `x = 0`
  have hiter : ∀ t, N ≤ t → ∀ k, π t = lam ^ k * π (k + t) := by
    intro t ht k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, (hslack (k + t) (by omega)).2, pow_succ]
      have : k + t + 1 = k + 1 + t := by omega
      rw [this]; ring
  have hzero : ∀ t, N ≤ t → π t = 0 := by
    intro t ht
    have h0 : Filter.Tendsto (fun k => lam ^ k * π (k + t)) Filter.atTop (nhds (0 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul
        (hπ.comp (Filter.tendsto_add_atTop_nat t))
    rw [mul_zero] at h0
    have h1 : Filter.Tendsto (fun _ : ℕ => π t) Filter.atTop (nhds 0) :=
      h0.congr (fun k => (hiter t ht k).symm)
    exact tendsto_const_nhds_iff.mp h1
  -- Step C: backward induction from `N`
  obtain ⟨hDE, -, hafter⟩ := disc_exists (ϑ := ϑ) hβ hκ hσ hϑ hρ hη tZ
  have hall : ∀ t, x t = discX β κ σ η tZ t ∧ π t = discPi β κ σ η tZ t := by
    refine down_induction N (fun t ht => ?_) (fun t ih => ?_)
    · have htZ : tZ < t := by have := le_max_right T (tZ + 1); omega
      refine ⟨?_, ?_⟩
      · rw [(hslack t ht).1, hzero (t + 1) (by omega), (hafter t htZ).1]; ring
      · rw [hzero t ht, (hafter t htZ).2.1]
    · have e0 : ups0 β π t = ups0 β (discPi β κ σ η tZ) t := by
        simp only [ups0, ih.2]
      have e1 : ups1 σ (natRate ρ η tZ) x π t =
          ups1 σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) t := by
        simp only [ups1, ih.1, ih.2]
      have h1 := (h t).2
      rw [e0, e1] at h1
      exact periodOptimal_unique hϑ h1 (hDE t).2
  have hxe : x = discX β κ σ η tZ := funext fun t => (hall t).1
  have hπe : π = discPi β κ σ η tZ := funext fun t => (hall t).2
  refine ⟨hxe, hπe, funext fun t => ?_⟩
  rw [(dis_iff hσ.ne').mp (h t).1, discI, hxe, hπe]

/-! ## Correction: boundedness alone does not give uniqueness -/

/-- Galí (2015), p. 146 (correction): the deflationary steady-state output gap
`x̄ = −(1 − β) ρ / κ`, at which `π = −ρ` and `i = 0` forever. -/
noncomputable def deflGap (β κ ρ : ℝ) : ℝ := -((1 - β) * ρ / κ)

/-- Galí (2015), p. 146 (correction): the deflationary path — (34) on `[0, t_Z]` glued to the
deflationary steady state `(x̄, −ρ)` after `t_Z`. -/
noncomputable def deflPath (β κ σ ρ η : ℝ) (tZ t : ℕ) : ℝ × ℝ :=
  zlbPath β κ σ η tZ (deflGap β κ ρ, -ρ) t

/-- Galí (2015), p. 146 (correction): the nominal rate along the deflationary path. -/
noncomputable def deflI (β κ σ ρ η : ℝ) (tZ : ℕ) : ℕ → ℝ :=
  impliedRate σ (natRate ρ η tZ) (fun t => (deflPath β κ σ ρ η tZ t).1)
    (fun t => (deflPath β κ σ ρ η tZ t).2)

/-- Galí (2015), pp. 146–147 (correction): the deflationary path is ALSO a discretionary
equilibrium under the ZLB, with `i_t = 0` at every date and `π_t = −ρ` after `t_Z`. -/
theorem deflation_discEq {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    DiscEq β κ σ ϑ (natRate ρ η tZ) (fun t => (deflPath β κ σ ρ η tZ t).1)
        (fun t => (deflPath β κ σ ρ η tZ t).2) (deflI β κ σ ρ η tZ) ∧
      (∀ t, deflI β κ σ ρ η tZ t = 0) ∧
      (∀ t, tZ < t → (deflPath β κ σ ρ η tZ t).2 = -ρ) := by
  have hg : deflGap β κ ρ ≤ 0 := by
    unfold deflGap
    have : 0 ≤ (1 - β) * ρ / κ := div_nonneg (mul_nonneg (by linarith) hρ.le) hκ.le
    linarith
  have hafter : ∀ t, tZ < t → deflPath β κ σ ρ η tZ t = (deflGap β κ ρ, -ρ) :=
    fun t ht => zlbPath_of_lt ht
  have hbind := fun t (ht : t ≤ tZ) =>
    zlbPath_binding (ϑ := ϑ) (ρ := ρ) hβ hκ hσ hϑ hη (sT := (deflGap β κ ρ, -ρ)) hg
      (by simp only; linarith) ht
  have hi_after : ∀ t, tZ < t → deflI β κ σ ρ η tZ t = 0 := by
    intro t ht
    simp only [deflI, impliedRate, natRate_of_lt ht, hafter t ht, hafter (t + 1) (by omega)]
    ring
  refine ⟨fun t => ⟨(dis_iff hσ.ne').mpr rfl, ?_⟩, fun t => ?_, fun t ht => by
    rw [hafter t ht]⟩
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).1
    · refine binding_optimal hϑ.le ?_ ?_ ?_
      · simp only [ups1, natRate_of_lt ht, hafter t ht, hafter (t + 1) (by omega)]
        ring
      · simp only [NKPC, hafter t ht, hafter (t + 1) (by omega), deflGap]
        field_simp
        ring
      · simp only [hafter t ht]
        nlinarith
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).2
    · exact hi_after t ht

/-- Galí (2015), p. 146 (correction): the deflationary path is bounded. -/
theorem deflation_bounded (β κ σ ρ η : ℝ) (tZ : ℕ) :
    ∃ C, ∀ t, |(deflPath β κ σ ρ η tZ t).1| ≤ C ∧ |(deflPath β κ σ ρ η tZ t).2| ≤ C := by
  refine ⟨∑ s ∈ Finset.range (tZ + 1),
      (|(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|) +
      (|deflGap β κ ρ| + |ρ|), fun t => ?_⟩
  have hS : 0 ≤ ∑ s ∈ Finset.range (tZ + 1),
      (|(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases le_or_gt t tZ with ht | ht
  · have hle := Finset.single_le_sum
      (f := fun s => |(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    have a1 := abs_nonneg (deflPath β κ σ ρ η tZ t).1
    have a2 := abs_nonneg (deflPath β κ σ ρ η tZ t).2
    have a3 := abs_nonneg (deflGap β κ ρ)
    have a4 := abs_nonneg ρ
    constructor <;> linarith
  · have e : deflPath β κ σ ρ η tZ t = (deflGap β κ ρ, -ρ) := zlbPath_of_lt ht
    rw [e]
    have a3 := abs_nonneg (deflGap β κ ρ)
    have a4 := abs_nonneg ρ
    simp only [abs_neg]
    constructor <;> linarith

/-- Galí (2015), p. 146 (correction): the deflationary equilibrium differs from the path of
p. 147 (inflation at `t_Z + 1` is `−ρ ≠ 0`). Hence uniqueness among BOUNDED paths fails; the
book's "from `t_Z + 1` onward `i_t = ρ`" selects the target steady state. -/
theorem deflation_ne_disc {β κ σ ρ η : ℝ} (hρ : 0 < ρ) (tZ : ℕ) :
    (fun t => (deflPath β κ σ ρ η tZ t).2) ≠ discPi β κ σ η tZ := by
  intro h
  have := congrFun h (tZ + 1)
  simp only [deflPath, discPi, zlbPath_of_lt (Nat.lt_succ_self tZ)] at this
  linarith

end Gali.DiscretionCommitment.ZLBDiscretion

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy with commitment under a zero lower bound

Galí (2015), Subsection 5.4.2, pp. 148–152.

At date 0 the central bank chooses `{x_t, π_t}` to minimise `∑ β^t (π_t² + ϑ x_t²)` subject to
the Phillips curve and the IS-plus-ZLB inequality `x_t ≤ x_{t+1} + (π_{t+1} + rⁿ_t)/σ` at every
date (p. 149). The economy is deterministic, so paths are sequences `ℕ → ℝ`; the loss is a
genuine infinite sum (`tsum`), and optimality is over all feasible paths with finite loss (a
path with non-summable loss has partial sums tending to `+∞`, `loss_partial_tendsto_top`).

## Main results

* `lagrangian_identity`, `kkt_sufficient`, `kkt_optimal`, `kkt_unique`: SUFFICIENCY — any
  feasible path satisfying the FOCs (35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, `ξ₂ ≥ 0` and `ξ₂ i = 0`
  (with bounded multipliers and finite loss) is optimal, and it is the unique optimum: the loss
  of any other feasible path exceeds it by at least `∑ β^t ((Δπ_t)² + ϑ (Δx_t)²)`.
* `optimal_unique`: strict convexity — two optimal paths coincide.
* `γ`, `δ` and their properties are imported from `DiscretionCommitment.Commitment` (`gam`, `del`,
  `del_pos`, `del_lt_one_iff`, `del_quad`, `kappa_sq_del`).
* `post_eq37`, `post_eq38`, `post_eq39`, `post_priceLevel`, `post_eq40`, `post_second_order`,
  `post_eq41`, `post_eq42_pos`, `post_eq43_pos`, `post_unique_bounded`: the post-liftoff
  dynamics (37)–(43); with `ξ₁,t_C+1 > 0`, `x > 0` and `π > 0` after liftoff, and the closed form
  is the unique bounded solution.
* `liftoff_iff`, `Nmat_det`, `eq47`, `eq47_iff`: the liftoff-period conditions (44)–(46) and the
  matrix `M` of (47).
* `eq48_iff`, `eq49_iff`, `eq49_matrix`, `eq50_iff`: the ZLB-phase dynamics with `A`, `B`, `H`, `J`.
* `post_rate`, `post_rate_nonneg`: after liftoff `i_t = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`, so the
  infinitely many conditions `i_t ≥ 0` reduce to two.
* `algorithm_verification`: the algorithm of p. 152 as a verification theorem — if the candidate
  built for a guessed `t_C` has `ξ₂,t ≥ 0` on `[0, t_C]` and `i ≥ 0` at `t_C + 1, t_C + 2`, it is
  the unique optimal path, with `i_t = 0` exactly on the announced ZLB spell `[0, t_C]`.
* `equation_count`: (C5-9) the book's "`4(t_C + 2)` equations" counts (46) and `ξ₂,t_C+1 = 0`
  alongside (47)–(50), with (50) used only for `t ≤ t_C`.
-/

namespace Gali.DiscretionCommitment.ZLBCommitment

open Gali.DiscretionCommitment.ZLBDiscretion

/-! ## The commitment problem -/

/-- Galí (2015), p. 149: the constraints of the commitment problem — the Phillips curve (29)
and `x_t ≤ x_{t+1} + (1/σ)(π_{t+1} + rⁿ_t)` ((28) and (30) combined) at every date. -/
def Feasible (β κ σ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  ∀ t, NKPC β κ x π t ∧ x t ≤ ups1 σ rn x π t

/-- Galí (2015), p. 149: feasibility is (29) together with a nonnegative implied rate. -/
theorem feasible_iff {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ} :
    Feasible β κ σ rn x π ↔ ∀ t, NKPC β κ x π t ∧ 0 ≤ impliedRate σ rn x π t := by
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  rw [impliedRate_eq hσ.ne']
  constructor
  · intro h; exact mul_nonneg hσ.le (by linarith)
  · intro h
    have := (mul_nonneg_iff_of_pos_left hσ).mp h
    linarith

/-- Galí (2015), p. 148: the period-`t` term `β^t (π_t² + ϑ x_t²)` of the loss. -/
noncomputable def lossTerm (β ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 148: the loss `∑_{t ≥ 0} β^t (π_t² + ϑ x_t²)`. -/
noncomputable def loss (β ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x π t

/-- Galí (2015), p. 148: the loss terms are nonnegative. -/
theorem lossTerm_nonneg {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) (x π : ℕ → ℝ) (t : ℕ) :
    0 ≤ lossTerm β ϑ x π t := by
  unfold lossTerm; positivity

/-- Galí (2015), p. 148: a path whose loss terms are not summable has partial losses tending to
`+∞`, so it is worse than any path with finite loss. -/
theorem loss_partial_tendsto_top {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) {x π : ℕ → ℝ}
    (h : ¬ Summable (lossTerm β ϑ x π)) :
    Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, lossTerm β ϑ x π t) Filter.atTop
      Filter.atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (lossTerm_nonneg hβ hϑ x π)).mp h

/-- Galí (2015), p. 148: `(x, π)` solves the commitment problem — it is feasible, has finite
loss, and its loss is no larger than that of any feasible path with finite loss. -/
def Optimal (β κ σ ϑ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ Summable (lossTerm β ϑ x π) ∧
    ∀ y q, Feasible β κ σ rn y q → Summable (lossTerm β ϑ y q) → loss β ϑ x π ≤ loss β ϑ y q

/-- Galí (2015), p. 149: the lag operator with the initial conditions `ξ₋₁ = 0`. -/
def lag (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => f t

/-- Galí (2015), p. 149: `lag f (t + 1) = f t`. -/
@[simp] theorem lag_succ (f : ℕ → ℝ) (t : ℕ) : lag f (t + 1) = f t := rfl

/-- Galí (2015), p. 149: `lag f 0 = 0` (the initial conditions `ξ₁,₋₁ = ξ₂,₋₁ = 0`). -/
@[simp] theorem lag_zero (f : ℕ → ℝ) : lag f 0 = 0 := rfl

/-- Galí (2015), eq. (35), p. 149: `π_t + ξ₁,t − ξ₁,t−1 − ξ₂,t−1/(βσ) = 0`. -/
def FOC35 (β σ : ℝ) (π ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  π t + ξ1 t - lag ξ1 t - lag ξ2 t / (β * σ) = 0

/-- Galí (2015), eq. (36), p. 149: `ϑ x_t − κ ξ₁,t + ξ₂,t − ξ₂,t−1/β = 0`. -/
def FOC36 (β κ ϑ : ℝ) (x ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  ϑ * x t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0

/-- Galí (2015), pp. 149: the KKT system of the commitment problem — feasibility, the FOCs
(35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, and the slackness conditions `ξ₂ ≥ 0`, `ξ₂ i = 0`. -/
def KKT (β κ σ ϑ : ℝ) (rn x π ξ1 ξ2 : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ ∀ t, FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t ∧ 0 ≤ ξ2 t ∧
    ξ2 t * impliedRate σ rn x π t = 0

/-- Galí (2015), p. 149: the Lagrangian identity (summation by parts). For a direction
`(dx, dπ)` satisfying the linearised Phillips curve, the first variation of the truncated loss
equals the inequality-multiplier terms plus a boundary term. -/
theorem lagrangian_identity {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {x π ξ1 ξ2 dx dπ : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (π t * dπ t + ϑ * x t * dx t) =
      ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * (dx (s + 1) + dπ (s + 1) / σ - dx s)) -
        β ^ T * ξ2 T * dx T - β ^ (T + 1) * ξ1 T * dπ (T + 1) := by
  induction T with
  | zero =>
    have a := h35 0
    have b := h36 0
    simp only [FOC35, FOC36, lag_zero, zero_div, sub_zero] at a b
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, pow_zero,
      pow_one, one_mul, zero_sub]
    linear_combination dπ 0 * a + dx 0 * b - ξ1 0 * hd 0
  | succ T ih =>
    have a := h35 (T + 1)
    have b := h36 (T + 1)
    simp only [FOC35, FOC36, lag_succ] at a b
    have e1 : β ^ (T + 1) * (ξ2 T / (β * σ)) = β ^ T * ξ2 T / σ := by
      rw [pow_succ]; field_simp
    have e2 : β ^ (T + 1) * (ξ2 T / β) = β ^ T * ξ2 T := by
      rw [pow_succ]; field_simp
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    linear_combination β ^ (T + 1) * dπ (T + 1) * a + β ^ (T + 1) * dx (T + 1) * b -
      β ^ (T + 1) * ξ1 (T + 1) * hd (T + 1) + dπ (T + 1) * e1 + dx (T + 1) * e2

/-- Galí (2015), p. 149: if `∑ β^t a_t²` is summable-small (`β^t a_t² → 0`) and `0 ≤ β < 1`,
then `β^t |a_t| → 0`. -/
theorem tendsto_pow_mul_abs {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ}
    (h : Filter.Tendsto (fun t => β ^ t * a t ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => β ^ t * |a t|) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun t => (β ^ t + β ^ t * a t ^ 2) / 2) Filter.atTop
      (nhds ((0 + 0) / 2)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).add h).div_const 2
  rw [add_zero, zero_div] at hg
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hg
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have : |a t| ≤ (1 + a t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a t| - 1), sq_abs (a t)]
  nlinarith

/-- Galí (2015), p. 149: SUFFICIENCY of the KKT system (Lagrangian + convexity). If `(x, π)`
satisfies the KKT system with bounded multipliers and has finite loss, then for every feasible
`(y, q)` with finite loss, `loss (x, π) + ∑ β^t ((q_t − π_t)² + ϑ (y_t − x_t)²) ≤ loss (y, q)`. -/
theorem kkt_sufficient {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q)) :
    Summable (fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2)) ∧
      loss β ϑ x π + ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) ≤
        loss β ϑ y q := by
  obtain ⟨hF, hK⟩ := hK
  obtain ⟨C, hC⟩ := hb
  set D : ℕ → ℝ := fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hsy.add hs).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2 ≤
        2 * ((q t ^ 2 + ϑ * y t ^ 2) + (π t ^ 2 + ϑ * x t ^ 2)) := by
      nlinarith [sq_nonneg (q t + π t), sq_nonneg (y t + x t)]
    nlinarith
  refine ⟨hDs, ?_⟩
  -- the boundary terms vanish
  have hD_lim := hDs.tendsto_atTop_zero
  have hdx : Filter.Tendsto (fun t => β ^ t * |y t - x t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      (by simpa using hD_lim.div_const ϑ))
    simp only [hDdef]
    rw [le_div_iff₀ hϑ]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [sq_nonneg (q t - π t)]
  have hdπ : Filter.Tendsto (fun t => β ^ t * |q t - π t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      hD_lim)
    simp only [hDdef]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [mul_nonneg hp (mul_nonneg hϑ.le (sq_nonneg (y t - x t)))]
  set b : ℕ → ℝ := fun T => C * (β ^ T * |y T - x T|) +
    C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) with hbdef
  have hb_lim : Filter.Tendsto (fun T => -(2 * b T)) Filter.atTop (nhds 0) := by
    have := ((hdx.const_mul C).add ((hdπ.comp (Filter.tendsto_add_atTop_nat 1)).const_mul C))
    simpa [hbdef] using (this.const_mul 2).neg
  -- partial sums
  have hlimL : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t)
      Filter.atTop (nhds (loss β ϑ y q - loss β ϑ x π - ∑' t, D t)) := by
    have h1 := hsy.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h3 := hDs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact (h1.sub h2).sub h3
  have hineq : ∀ T, -(2 * b T) ≤ ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t := by
    intro T
    have hsplit : ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
        ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t =
        2 * ∑ t ∈ Finset.range (T + 1),
          β ^ t * (π t * (q t - π t) + ϑ * x t * (y t - x t)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, hDdef]
      ring
    have hd : ∀ t, q t - π t = β * (q (t + 1) - π (t + 1)) + κ * (y t - x t) := by
      intro t
      have h1 := (hy t).1
      have h2 := (hF t).1
      unfold NKPC at h1 h2
      linarith
    have hid := lagrangian_identity hβ.ne' hσ.ne' (fun t => (hK t).1) (fun t => (hK t).2.1)
      (dx := fun t => y t - x t) (dπ := fun t => q t - π t) hd T
    rw [hsplit, hid]
    have hsum : 0 ≤ ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * ((y (s + 1) - x (s + 1)) +
        (q (s + 1) - π (s + 1)) / σ - (y s - x s))) := by
      refine Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hβ.le s) ?_
      have hslack : ξ2 s * (ups1 σ rn x π s - x s) = 0 := by
        have h := (hK s).2.2.2
        rw [impliedRate_eq hσ.ne'] at h
        rw [mul_left_comm] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hσ.ne'
        · exact h'
      have hfy : 0 ≤ ξ2 s * (ups1 σ rn y q s - y s) :=
        mul_nonneg (hK s).2.2.1 (by linarith [(hy s).2])
      have e : ξ2 s * ((y (s + 1) - x (s + 1)) + (q (s + 1) - π (s + 1)) / σ - (y s - x s)) =
          ξ2 s * (ups1 σ rn y q s - y s) - ξ2 s * (ups1 σ rn x π s - x s) := by
        unfold ups1; ring
      rw [e, hslack]
      linarith
    have hC1 := (hC T).2
    have hC2 := (hC T).1
    have hp : 0 ≤ β ^ T := pow_nonneg hβ.le T
    have hp1 : 0 ≤ β ^ (T + 1) := pow_nonneg hβ.le (T + 1)
    have k1 : |β ^ T * ξ2 T * (y T - x T)| ≤ C * (β ^ T * |y T - x T|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp]
      have := abs_nonneg (y T - x T)
      nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (mul_nonneg hp this)]
    have k2 : |β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1))| ≤
        C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp1]
      have := abs_nonneg (q (T + 1) - π (T + 1))
      nlinarith [mul_nonneg (sub_nonneg.mpr hC2) (mul_nonneg hp1 this)]
    have k3 := le_abs_self (β ^ T * ξ2 T * (y T - x T))
    have k4 := le_abs_self (β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1)))
    simp only [hbdef]
    linarith
  have := le_of_tendsto_of_tendsto' hb_lim hlimL hineq
  unfold loss at this ⊢
  linarith

/-- Galí (2015), p. 149: a KKT path with bounded multipliers and finite loss is optimal. -/
theorem kkt_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π)) :
    Optimal β κ σ ϑ rn x π := by
  refine ⟨hK.1, hs, fun y q hy hsy => ?_⟩
  obtain ⟨hDs, hle⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have : 0 ≤ ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) :=
    tsum_nonneg fun t => by positivity
  linarith

/-- Galí (2015), p. 149: a nonnegative summable sequence with nonpositive sum vanishes. -/
theorem eq_zero_of_tsum_nonpos {D : ℕ → ℝ} (h0 : ∀ t, 0 ≤ D t) (hs : Summable D)
    (h : ∑' t, D t ≤ 0) (t : ℕ) : D t = 0 :=
  le_antisymm ((hs.le_tsum t fun j _ => h0 j).trans h) (h0 t)

/-- Galí (2015), p. 149: a weighted sum of squares `β^t (a² + ϑ b²)` vanishes only at
`a = b = 0`. -/
theorem sq_terms_zero {β ϑ a b : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (t : ℕ)
    (h : β ^ t * (a ^ 2 + ϑ * b ^ 2) = 0) : a = 0 ∧ b = 0 := by
  have hp : 0 < β ^ t := pow_pos hβ t
  have h2 : a ^ 2 + ϑ * b ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hp.ne'
    · exact h'
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hϑ.le (sq_nonneg b)]
  have hb : ϑ * b ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp hb).resolve_left hϑ.ne')⟩

/-- Galí (2015), p. 149: UNIQUENESS — a KKT path (bounded multipliers, finite loss) is the
only feasible path with finite loss whose loss is no larger. -/
theorem kkt_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q))
    (hle : loss β ϑ y q ≤ loss β ϑ x π) : y = x ∧ q = π := by
  obtain ⟨hDs, hle2⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have hz := eq_zero_of_tsum_nonpos (fun t => by positivity) hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Galí (2015), p. 149: STRICT CONVEXITY — two optimal paths of the commitment problem
coincide (the midpoint would do strictly better otherwise). -/
theorem optimal_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x1 π1 x2 π2 : ℕ → ℝ}
    (h1 : Optimal β κ σ ϑ rn x1 π1) (h2 : Optimal β κ σ ϑ rn x2 π2) : x1 = x2 ∧ π1 = π2 := by
  obtain ⟨hF1, hs1, ho1⟩ := h1
  obtain ⟨hF2, hs2, ho2⟩ := h2
  set xm : ℕ → ℝ := fun t => (x1 t + x2 t) / 2 with hxm
  set πm : ℕ → ℝ := fun t => (π1 t + π2 t) / 2 with hπm
  have hFm : Feasible β κ σ rn xm πm := by
    intro t
    obtain ⟨a1, b1⟩ := hF1 t
    obtain ⟨a2, b2⟩ := hF2 t
    unfold NKPC at a1 a2
    refine ⟨?_, ?_⟩
    · unfold NKPC; simp only [hxm, hπm]; linarith
    · have e : ups1 σ rn xm πm t = (ups1 σ rn x1 π1 t + ups1 σ rn x2 π2 t) / 2 := by
        simp only [ups1, hxm, hπm]; ring
      rw [e]; simp only [hxm]; linarith
  set D : ℕ → ℝ := fun t => β ^ t * ((π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hs1.add hs2).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2 ≤
        2 * ((π1 t ^ 2 + ϑ * x1 t ^ 2) + (π2 t ^ 2 + ϑ * x2 t ^ 2)) := by
      nlinarith [sq_nonneg (π1 t + π2 t), sq_nonneg (x1 t + x2 t)]
    nlinarith
  have hterm : ∀ t, lossTerm β ϑ xm πm t =
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 := by
    intro t; simp only [lossTerm, hDdef, hxm, hπm]; ring
  have hsm : Summable (lossTerm β ϑ xm πm) := by
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    exact ((hs1.add hs2).div_const 2).sub (hDs.div_const 4)
  have hlm : loss β ϑ xm πm = (loss β ϑ x1 π1 + loss β ϑ x2 π2) / 2 - (∑' t, D t) / 4 := by
    unfold loss
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    rw [((hs1.add hs2).div_const 2).tsum_sub (hDs.div_const 4), tsum_div_const,
      tsum_div_const, hs1.tsum_add hs2]
  have l12 := ho1 x2 π2 hF2 hs2
  have l21 := ho2 x1 π1 hF1 hs1
  have l1m := ho1 xm πm hFm hsm
  have hz := eq_zero_of_tsum_nonpos hD0 hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-! ## Post-liftoff dynamics (37)–(43) -/

/-- Galí (2015), eq. (42), p. 150: `x_{t_C+2+k} = κ δ^{k+1} ξ / ϑ`, `ξ = ξ₁,t_C+1`. -/
noncomputable def postX (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := κ * Commitment.del β κ ϑ ^ (k + 1) * ξ / ϑ

/-- Galí (2015), eq. (43), p. 150: `π_{t_C+2+k} = (1 − δ) δ^k ξ`. -/
noncomputable def postPi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ :=
  (1 - Commitment.del β κ ϑ) * Commitment.del β κ ϑ ^ k * ξ

/-- Galí (2015), pp. 149–150: the multiplier `ξ₁,t_C+1+k = δ^k ξ` (from (38) and (42)). -/
noncomputable def postXi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := Commitment.del β κ ϑ ^ k * ξ

/-- Galí (2015), eq. (41), p. 150: the price-level gap `p̂_{t_C+1+k} = p_{t_C+1+k} − p* =
−δ^k ξ`. -/
noncomputable def postP (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := -(Commitment.del β κ ϑ ^ k * ξ)

/-- Galí (2015), eq. (37), p. 149: `π_t + ξ₁,t − ξ₁,t−1 = 0` after liftoff. -/
theorem post_eq37 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k + postXi β κ ϑ ξ (k + 1) - postXi β κ ϑ ξ k = 0 := by
  unfold postPi postXi; ring

/-- Galí (2015), eq. (38), p. 149: `ϑ x_t − κ ξ₁,t = 0` after liftoff. -/
theorem post_eq38 {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    ϑ * postX β κ ϑ ξ k - κ * postXi β κ ϑ ξ (k + 1) = 0 := by
  unfold postX postXi; field_simp; ring

/-- Galí (2015), eq. (39), p. 149: the Phillips curve `π_t = β π_{t+1} + κ x_t` after liftoff. -/
theorem post_eq39 {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k = β * postPi β κ ϑ ξ (k + 1) + κ * postX β κ ϑ ξ k := by
  have key : κ ^ 2 * Commitment.del β κ ϑ =
      ϑ * (1 - Commitment.del β κ ϑ) * (1 - β * Commitment.del β κ ϑ) := by
    have h := Commitment.kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  unfold postPi postX
  set δ := Commitment.del β κ ϑ
  field_simp
  linear_combination (-(δ ^ k * ξ)) * key

/-- Galí (2015), p. 150: (37) and `p_t = p_{t−1} + π_t` make `p_t + ξ₁,t` constant after
liftoff, equal to `p* ≡ p_{t_C+1} + ξ₁,t_C+1` (here `L = t_C + 1`). -/
theorem post_priceLevel {L : ℕ} {p π ξ1 : ℕ → ℝ}
    (hp : ∀ k, p (L + (k + 1)) = p (L + k) + π (L + (k + 1)))
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0) (k : ℕ) :
    p (L + k) + ξ1 (L + k) = p L + ξ1 L := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have a := hp k
    have b := h37 k
    linarith

/-- Galí (2015), eq. (40), p. 150: (37), (38) give `x_t = −(κ/ϑ)(p_t − p*)` after liftoff. -/
theorem post_eq40 {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) {L : ℕ} {p x π ξ1 : ℕ → ℝ}
    (hp : ∀ k, p (L + (k + 1)) = p (L + k) + π (L + (k + 1)))
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0)
    (h38 : ∀ k, ϑ * x (L + (k + 1)) - κ * ξ1 (L + (k + 1)) = 0) (k : ℕ) :
    x (L + (k + 1)) = -(κ / ϑ) * (p (L + (k + 1)) - (p L + ξ1 L)) := by
  have h1 := post_priceLevel hp h37 (k + 1)
  have h2 := h38 k
  rw [← h1]
  field_simp
  linarith

/-- Galí (2015), p. 150: (39) and (40) give the second-order equation
`p̂_t = γ p̂_{t−1} + γ β p̂_{t+1}` (with `a, b, c` the gaps at `t − 1, t, t + 1`). -/
theorem post_second_order {β κ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {a b c x πt πt1 : ℝ}
    (hπ : πt = b - a) (hπ1 : πt1 = c - b) (hx : x = -(κ / ϑ) * b) (h39 : πt = β * πt1 + κ * x) :
    b = Commitment.gam β κ ϑ * a + Commitment.gam β κ ϑ * β * c := by
  subst hπ hπ1 hx
  unfold Commitment.gam
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp at h39
  have hm : b * (ϑ * (1 + β) + κ ^ 2) = ϑ * a + ϑ * β * c := by linear_combination h39
  field_simp
  linear_combination hm

/-- Galí (2015), eq. (41), p. 150: `p̂_{t+1} = δ p̂_t` after liftoff, with `p̂_{t_C+1} = −ξ`. -/
theorem post_eq41 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postP β κ ϑ ξ (k + 1) = Commitment.del β κ ϑ * postP β κ ϑ ξ k ∧ postP β κ ϑ ξ 0 = -ξ := by
  unfold postP; constructor <;> ring

/-- Galí (2015), p. 150: the closed form `p̂ = −δ^k ξ` solves the second-order equation. -/
theorem postP_second_order {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postP β κ ϑ ξ (k + 1) =
      Commitment.gam β κ ϑ * postP β κ ϑ ξ k +
        Commitment.gam β κ ϑ * β * postP β κ ϑ ξ (k + 2) := by
  have h := Commitment.del_quad (κ := κ) hβ hβ1 hϑ
  unfold postP
  linear_combination (Commitment.del β κ ϑ ^ k * ξ) * h

/-- Galí (2015), eqs. (40)–(42), p. 150: `x_{t_C+2+k} = −(κ/ϑ) p̂_{t_C+2+k}` and
`p̂_{t_C+2+k} = −δ^{k+1} ξ`. -/
theorem post_eq40_closed {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    postX β κ ϑ ξ k = -(κ / ϑ) * postP β κ ϑ ξ (k + 1) := by
  unfold postX postP; field_simp

/-- Galí (2015), eq. (42), p. 150: with `ξ₁,t_C+1 > 0`, the output gap is positive after
liftoff. -/
theorem post_eq42_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : 0 < ξ)
    (k : ℕ) : 0 < postX β κ ϑ ξ k := by
  have := Commitment.del_pos (κ := κ) hβ hϑ
  unfold postX; positivity

/-- Galí (2015), eq. (43), p. 150: with `ξ₁,t_C+1 > 0`, inflation is positive after liftoff. -/
theorem post_eq43_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hξ : 0 < ξ)
    (k : ℕ) : 0 < postPi β κ ϑ ξ k := by
  have h0 := Commitment.del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold postPi; positivity

/-- Galí (2015), p. 150: inflation and the output gap converge to zero after liftoff. -/
theorem post_tendsto_zero {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (ξ : ℝ) :
    Filter.Tendsto (postX β κ ϑ ξ) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (postPi β κ ϑ ξ) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Commitment.del_pos (κ := κ) hβ hϑ).le
    ((Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne')
  have h1 := h.comp (Filter.tendsto_add_atTop_nat 1)
  refine ⟨?_, ?_⟩
  · have := ((h1.const_mul κ).mul_const ξ).div_const ϑ
    rw [mul_zero, zero_mul, zero_div] at this
    exact this
  · have := (h.const_mul (1 - Commitment.del β κ ϑ)).mul_const ξ
    rw [mul_zero, zero_mul] at this
    exact this

/-- Galí (2015), p. 150: UNIQUENESS of the post-liftoff path — among solutions of (37)–(39)
for `t ≥ t_C + 2` with a bounded output gap, the closed form (41)–(43) is the only one
(`L = t_C + 1`, `ξ = ξ₁,L`). -/
theorem post_unique_bounded {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {L : ℕ} {x π ξ1 : ℕ → ℝ}
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0)
    (h38 : ∀ k, ϑ * x (L + (k + 1)) - κ * ξ1 (L + (k + 1)) = 0)
    (h39 : ∀ k, π (L + (k + 1)) = β * π (L + (k + 2)) + κ * x (L + (k + 1)))
    (hb : ∃ C, ∀ t, |x t| ≤ C) (k : ℕ) :
    ξ1 (L + k) = postXi β κ ϑ (ξ1 L) k ∧ x (L + (k + 1)) = postX β κ ϑ (ξ1 L) k ∧
      π (L + (k + 1)) = postPi β κ ϑ (ξ1 L) k := by
  obtain ⟨C, hC⟩ := hb
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have key : κ ^ 2 * Commitment.del β κ ϑ =
      ϑ * (1 - Commitment.del β κ ϑ) * (1 - β * Commitment.del β κ ϑ) := by
    have h := Commitment.kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  set δ := Commitment.del β κ ϑ with hδ
  set q : ℕ → ℝ := fun k => ξ1 (L + k) with hq
  have hπq : ∀ k, π (L + (k + 1)) = q k - q (k + 1) := fun k => by
    simp only [hq]; linarith [h37 k]
  have hxq : ∀ k, ϑ * x (L + (k + 1)) = κ * q (k + 1) := fun k => by
    simp only [hq]; linarith [h38 k]
  have hrec : ∀ k, ϑ * (q k - q (k + 1)) = ϑ * β * (q (k + 1) - q (k + 2)) +
      κ ^ 2 * q (k + 1) := by
    intro k
    have a := h39 k
    rw [hπq k, show L + (k + 2) = L + (k + 1 + 1) by omega, hπq (k + 1)] at a
    have b := hxq k
    linear_combination ϑ * a + κ * b
  set w : ℕ → ℝ := fun k => q (k + 1) - δ * q k with hw
  have hstep : ∀ k, β * δ * w (k + 1) = w k := by
    intro k
    apply mul_left_cancel₀ hϑ.ne'
    simp only [hw]
    linear_combination δ * hrec k + q (k + 1) * key
  -- bounds
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set B := ϑ * C / κ + |q 0| with hB
  have hqB : ∀ k, |q k| ≤ B := by
    intro k
    rcases k with _ | k
    · have : 0 ≤ ϑ * C / κ := by positivity
      simp only [hB]; linarith
    · have e : q (k + 1) = ϑ * x (L + (k + 1)) / κ := by
        rw [hxq k]; field_simp
      rw [e, abs_div, abs_mul, abs_of_pos hϑ, abs_of_pos hκ]
      have h1 : ϑ * |x (L + (k + 1))| / κ ≤ ϑ * C / κ := by
        gcongr; exact hC _
      have := abs_nonneg (q 0)
      simp only [hB]; linarith
  have hwB : ∀ k, |w k| ≤ (1 + δ) * B := by
    intro k
    simp only [hw]
    calc |q (k + 1) - δ * q k| ≤ |q (k + 1)| + |δ * q k| := abs_sub _ _
      _ = |q (k + 1)| + δ * |q k| := by rw [abs_mul, abs_of_pos hδ0]
      _ ≤ B + δ * B := by gcongr <;> exact hqB _
      _ = (1 + δ) * B := by ring
  have hiter : ∀ k, w 0 = (β * δ) ^ k * w k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [ih, ← hstep k, pow_succ]; ring
  have hβδ0 : 0 ≤ β * δ := by positivity
  have hβδ1 : β * δ < 1 := by nlinarith
  have hw0 : w 0 = 0 := by
    have hlim : Filter.Tendsto (fun k => (β * δ) ^ k * ((1 + δ) * B)) Filter.atTop
        (nhds (0 * ((1 + δ) * B))) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβδ0 hβδ1).mul_const _
    rw [zero_mul] at hlim
    have hle : ∀ k, |w 0| ≤ (β * δ) ^ k * ((1 + δ) * B) := by
      intro k
      rw [hiter k, abs_mul, abs_of_nonneg (pow_nonneg hβδ0 k)]
      exact mul_le_mul_of_nonneg_left (hwB k) (pow_nonneg hβδ0 k)
    have := ge_of_tendsto' hlim hle
    exact abs_nonpos_iff.mp this
  have hwz : ∀ k, w k = 0 := by
    intro k
    induction k with
    | zero => exact hw0
    | succ k ih =>
      have := hstep k
      rw [ih] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
  have hqk : ∀ k, q k = δ ^ k * q 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hwz k
      simp only [hw] at this
      rw [pow_succ]; linear_combination this + δ * ih
  have hq0 : q 0 = ξ1 L := by simp [hq]
  refine ⟨?_, ?_, ?_⟩
  · have := hqk k; simp only [hq, postXi] at this ⊢; rw [this, ← hq0]
  · have e := hxq k
    rw [hqk (k + 1), hq0] at e
    unfold postX
    field_simp
    linear_combination e
  · rw [hπq k, hqk k, hqk (k + 1), hq0]
    unfold postPi
    ring

/-! ## The liftoff period (44)–(47) -/

/-- Galí (2015), eq. (44), p. 150: `π_{t_C+1} + ξ₁,t_C+1 − ξ₁,t_C − ξ₂,t_C/(βσ) = 0` (eq. (35)
at `t_C + 1` with `ξ₂,t_C+1 = 0`). -/
def Eq44 (β σ xiL πL xi1c xi2c : ℝ) : Prop := πL + xiL - xi1c - xi2c / (β * σ) = 0

/-- Galí (2015), eq. (45), p. 150: `ϑ x_{t_C+1} − κ ξ₁,t_C+1 − ξ₂,t_C/β = 0` (eq. (36) at
`t_C + 1` with `ξ₂,t_C+1 = 0`). -/
def Eq45 (β κ ϑ xiL xL xi2c : ℝ) : Prop := ϑ * xL - κ * xiL - xi2c / β = 0

/-- Galí (2015), eq. (46), p. 150: `π_{t_C+1} = β (1 − δ) ξ₁,t_C+1 + κ x_{t_C+1}` (eq. (29) at
`t_C + 1` with `π_{t_C+2} = (1 − δ) ξ₁,t_C+1` from (43)). -/
def Eq46 (β κ ϑ xiL xL πL : ℝ) : Prop := πL = β * (1 - Commitment.del β κ ϑ) * xiL + κ * xL

/-- Galí (2015), p. 151: the left matrix of (47),
`N = [−κ, 1 + β(1 − δ); β(1 − δ) + κ²/ϑ, −κ/ϑ]`. -/
noncomputable def Nmat (β κ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-κ, 1 + β * (1 - Commitment.del β κ ϑ); β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ, -κ / ϑ]

/-- Galí (2015), p. 151: the right matrix of (47), `K = [β(1 − δ), (1 − δ)/σ; 0, (1 − δ)/ϑ]`. -/
noncomputable def Kmat (β κ σ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β * (1 - Commitment.del β κ ϑ), (1 - Commitment.del β κ ϑ) / σ;
    0, (1 - Commitment.del β κ ϑ) / ϑ]

/-- Galí (2015), p. 151: `M ≡ N⁻¹ K`. -/
noncomputable def Mmat (β κ σ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (Nmat β κ ϑ)⁻¹ * Kmat β κ σ ϑ

/-- Galí (2015), p. 151: `det N = −β(1 − δ)(1 + β(1 − δ) + κ²/ϑ) ≠ 0`, so `M` is well defined. -/
theorem Nmat_det {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    (Nmat β κ ϑ).det = -(β * (1 - Commitment.del β κ ϑ) *
      (1 + β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ)) ∧
      (Nmat β κ ϑ).det ≠ 0 := by
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  have e : (Nmat β κ ϑ).det =
      -(β * (1 - Commitment.del β κ ϑ) * (1 + β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ)) := by
    rw [Nmat, Matrix.det_fin_two_of]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e, neg_ne_zero]
  positivity

/-- Galí (2015), pp. 150–151: (44)–(46) are equivalent to the two rows of `N (x, π)' = K ξ`
together with `ξ₁,t_C+1 = (π − κ x) / (β (1 − δ))` (eliminating `ξ₁,t_C+1` with (46)). -/
theorem liftoff_iff {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (xiL xL πL xi1c xi2c : ℝ) :
    (Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) ↔
      (-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL =
          β * (1 - Commitment.del β κ ϑ) * xi1c + (1 - Commitment.del β κ ϑ) / σ * xi2c ∧
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL =
          (1 - Commitment.del β κ ϑ) / ϑ * xi2c ∧
        xiL = (πL - κ * xL) / (β * (1 - Commitment.del β κ ϑ))) := by
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold Eq44 Eq45 Eq46
  set d := Commitment.del β κ ϑ
  have ha : β * (1 - d) ≠ 0 := by positivity
  constructor
  · rintro ⟨a, b, c⟩
    have hxi : xiL = (πL - κ * xL) / (β * (1 - d)) := by
      rw [eq_div_iff ha]; linarith
    refine ⟨?_, ?_, hxi⟩
    · have e : β * (1 - d) * (xi2c / (β * σ)) = (1 - d) / σ * xi2c := by
        field_simp
      linear_combination β * (1 - d) * a + c + e
    · rw [hxi] at b
      field_simp at b
      have hm : (β * (1 - d) * ϑ + κ ^ 2) * xL - κ * πL = (1 - d) * xi2c := by
        linear_combination b
      field_simp
      linear_combination hm
  · rintro ⟨a, b, c⟩
    have c' : β * (1 - d) * xiL = πL - κ * xL := by rw [c]; field_simp
    refine ⟨?_, ?_, by linarith⟩
    · have e : β * (1 - d) * (xi2c / (β * σ)) = (1 - d) / σ * xi2c := by
        field_simp
      apply mul_left_cancel₀ ha
      linear_combination a + c' - e
    · apply mul_left_cancel₀ ha
      have e : β * (1 - d) * (xi2c / β) = (1 - d) * xi2c := by field_simp
      field_simp at b
      linear_combination b - κ * c' - e

/-- Galí (2015), p. 151: `N (x, π)'` written out. -/
theorem Nmat_mulVec (β κ ϑ xL πL : ℝ) :
    Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] =
      ![-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL,
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL] := by
  ext j
  fin_cases j <;> simp [Nmat] <;> ring

/-- Galí (2015), p. 151: `K (ξ₁,t_C, ξ₂,t_C)'` written out. -/
theorem Kmat_mulVec (β κ σ ϑ a b : ℝ) :
    Matrix.mulVec (Kmat β κ σ ϑ) ![a, b] =
      ![β * (1 - Commitment.del β κ ϑ) * a + (1 - Commitment.del β κ ϑ) / σ * b,
        (1 - Commitment.del β κ ϑ) / ϑ * b] := by
  ext j
  fin_cases j <;> simp [Kmat] <;> ring

/-- Galí (2015), eq. (47), p. 151: (44)–(46) hold iff `(x_{t_C+1}, π_{t_C+1})' =
M (ξ₁,t_C, ξ₂,t_C)'` and `ξ₁,t_C+1 = (π_{t_C+1} − κ x_{t_C+1}) / (β (1 − δ))`. -/
theorem eq47_iff {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (xiL xL πL xi1c xi2c : ℝ) :
    (Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) ↔
      (![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] ∧
        xiL = (πL - κ * xL) / (β * (1 - Commitment.del β κ ϑ))) := by
  rw [liftoff_iff hβ hβ1 hκ hσ hϑ]
  have hU : IsUnit (Nmat β κ ϑ).det := isUnit_iff_ne_zero.mpr (Nmat_det hβ hβ1 hκ hϑ).2
  have hNK : (-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL =
          β * (1 - Commitment.del β κ ϑ) * xi1c + (1 - Commitment.del β κ ϑ) / σ * xi2c ∧
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL =
          (1 - Commitment.del β κ ϑ) / ϑ * xi2c) ↔
      Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] = Matrix.mulVec (Kmat β κ σ ϑ) ![xi1c, xi2c] := by
    rw [Nmat_mulVec, Kmat_mulVec]
    constructor
    · rintro ⟨a, b⟩
      ext j
      fin_cases j
      · exact a
      · exact b
    · intro h
      exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  have hM : Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] = Matrix.mulVec (Kmat β κ σ ϑ) ![xi1c, xi2c] ↔
      ![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] := by
    constructor
    · intro h
      rw [Mmat, ← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    · intro h
      rw [h, Mmat, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU,
        Matrix.one_mul]
  rw [← hM, ← hNK, and_assoc]

/-- Galí (2015), eq. (47), p. 151: (44)–(46) imply `(x_{t_C+1}, π_{t_C+1})' = M (ξ₁,t_C, ξ₂,t_C)'`.
-/
theorem eq47 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {xiL xL πL xi1c xi2c : ℝ}
    (h : Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) :
    ![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] :=
  ((eq47_iff hβ hβ1 hκ hσ hϑ xiL xL πL xi1c xi2c).mp h).1

/-! ## The ZLB phase (48)–(50) -/

/-- Galí (2015), eq. (48), p. 151: on `[0, t_Z]` with `i_t = 0`, the system is (34):
`(x_t, π_t)' = A (x_{t+1}, π_{t+1})' − B ε` (restated from `eq34_iff`). -/
theorem eq48_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : t ≤ tZ) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) :=
  eq34_iff hσ ht

/-- Galí (2015), eq. (49), p. 151: on `(t_Z, t_C]` with `i_t = 0` and `rⁿ_t = ρ`, the system is
`(x_t, π_t)' = A (x_{t+1}, π_{t+1})' + B ρ` (`backStep` with drop `−ρ`). -/
theorem eq49_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : tZ < t) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) := by
  rw [dis_iff hσ]
  unfold NKPC impliedRate backStep
  rw [natRate_of_lt ht, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t = x (t + 1) + π (t + 1) / σ - -ρ / σ := by
      rw [h3] at h2
      field_simp
      linarith
    refine ⟨h3, hx, ?_⟩
    simp only
    rw [h1, hx]
    ring
  · rintro ⟨h3, hx, hπ⟩
    simp only at hx hπ
    refine ⟨?_, ?_, h3⟩
    · rw [hπ, hx]; ring
    · rw [h3, hx]; field_simp; ring

/-- Galí (2015), eq. (49), p. 151: the matrix form `A s + B ρ`. -/
theorem eq49_matrix (β κ σ ρ : ℝ) (s : ℝ × ℝ) :
    ![(backStep β κ σ (-ρ) s).1, (backStep β κ σ (-ρ) s).2] =
      Matrix.mulVec (Amat β κ σ) ![s.1, s.2] + ρ • Bvec κ σ := by
  rw [eq34_matrix, neg_smul, sub_neg_eq_add]

/-- Galí (2015), p. 151: `H ≡ [1, 1/(βσ); κ, (1/β)(1 + κ/σ)]`. -/
noncomputable def Hmat (β κ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / (β * σ); κ, 1 / β * (1 + κ / σ)]

/-- Galí (2015), p. 151: `J ≡ [0, 1; ϑ, κ]`. -/
def Jmat (κ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; ϑ, κ]

/-- Galí (2015), eq. (50), p. 151: the FOCs (35)–(36) are
`(ξ₁,t, ξ₂,t)' = H (ξ₁,t−1, ξ₂,t−1)' − J (x_t, π_t)'`, with `ξ₁,₋₁ = ξ₂,₋₁ = 0`. -/
theorem eq50_iff {β κ σ ϑ : ℝ} {x π ξ1 ξ2 : ℕ → ℝ} (t : ℕ) :
    (FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t) ↔
      ![ξ1 t, ξ2 t] = Matrix.mulVec (Hmat β κ σ) ![lag ξ1 t, lag ξ2 t] -
        Matrix.mulVec (Jmat κ ϑ) ![x t, π t] := by
  have hv : Matrix.mulVec (Hmat β κ σ) ![lag ξ1 t, lag ξ2 t] -
      Matrix.mulVec (Jmat κ ϑ) ![x t, π t] =
      ![lag ξ1 t + lag ξ2 t / (β * σ) - π t,
        κ * lag ξ1 t + 1 / β * (1 + κ / σ) * lag ξ2 t - (ϑ * x t + κ * π t)] := by
    ext j
    fin_cases j <;> simp [Hmat, Jmat] <;> ring
  rw [hv]
  unfold FOC35 FOC36
  constructor
  · rintro ⟨a, b⟩
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination a
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination b + κ * a
  · intro h
    have a := congrFun h 0
    have b := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a b
    exact ⟨by linear_combination a, by linear_combination b - κ * a⟩

/-! ## The algorithm of p. 152 as a verification theorem -/

/-- Galí (2015), p. 152: after liftoff the implied rate is
`i_{t_C+2+k} = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`. -/
theorem post_rate {β κ σ ϑ ρ η : ℝ} (hϑ : ϑ ≠ 0) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    {ξ : ℝ} (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k) (k : ℕ) :
    impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) =
      ρ + (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (k + 1) * ξ := by
  unfold impliedRate
  rw [natRate_of_lt (by omega), show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hx, hπ]
  unfold postX postPi
  field_simp
  ring

/-- Galí (2015), p. 152: the infinitely many conditions `i_t ≥ 0`, `t ≥ t_C + 2`, reduce to the
single condition `i_{t_C+2} ≥ 0` (the rate moves monotonically towards `ρ > 0`). -/
theorem post_rate_nonneg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ} {ξ : ℝ}
    (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k) (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k)
    (h0 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (k : ℕ) :
    0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) := by
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have e0 : impliedRate σ (natRate ρ η tZ) x π (tC + 2) =
      ρ + (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (0 + 1) * ξ :=
    post_rate hϑ.ne' htC hx hπ 0
  rw [e0] at h0
  rw [post_rate hϑ.ne' htC hx hπ k]
  set A := (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  have hk : (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (k + 1) * ξ =
      A * Commitment.del β κ ϑ ^ (k + 1) := by rw [hA]; ring
  have h0' : (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (0 + 1) * ξ =
      A * Commitment.del β κ ϑ := by rw [hA]; ring
  rw [hk]
  rw [h0'] at h0
  have hp : Commitment.del β κ ϑ ^ (k + 1) ≤ Commitment.del β κ ϑ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1.le)
  have hp0 : 0 ≤ Commitment.del β κ ϑ ^ (k + 1) := pow_nonneg hδ0.le _
  rcases le_or_gt 0 A with hA0 | hA0
  · have := mul_nonneg hA0 hp0; linarith
  · nlinarith

/-- Galí (2015), p. 152: one backward step of (48)/(49) gives the Phillips curve and `i_t = 0`. -/
theorem backStep_nkpc_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) (hr : rn t = -e) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hr, hx]; field_simp; ring

/-- Galí (2015), p. 152: the candidate built for a guessed `t_C` satisfies (44)–(46), hence the
matrix relation (47). -/
theorem algorithm_eq47 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ)
    {tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (h50 : FOC35 β σ π ξ1 ξ2 (tC + 1) ∧ FOC36 β κ ϑ x ξ1 ξ2 (tC + 1))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) :
    Eq44 β σ (ξ1 (tC + 1)) (π (tC + 1)) (ξ1 tC) (ξ2 tC) ∧
      Eq45 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (ξ2 tC) ∧
      Eq46 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (π (tC + 1)) ∧
      ![x (tC + 1), π (tC + 1)] = Matrix.mulVec (Mmat β κ σ ϑ) ![ξ1 tC, ξ2 tC] := by
  obtain ⟨a, b⟩ := h50
  unfold FOC35 at a
  unfold FOC36 at b
  rw [lag_succ, lag_succ] at a
  rw [lag_succ, hξ2] at b
  have h44 : Eq44 β σ (ξ1 (tC + 1)) (π (tC + 1)) (ξ1 tC) (ξ2 tC) := by
    unfold Eq44; linarith
  have h45 : Eq45 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (ξ2 tC) := by
    unfold Eq45; linarith
  have h46' : Eq46 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (π (tC + 1)) := by
    unfold Eq46
    unfold NKPC at h46
    rw [h46, show tC + 1 + 1 = tC + 2 by omega, hπ2]
    unfold postPi; ring
  exact ⟨h44, h45, h46', eq47 hβ hβ1 hκ hσ hϑ ⟨h44, h45, h46'⟩⟩

/-- Galí (2015), p. 152, VERIFICATION THEOREM for the algorithm. Guess `t_C ≥ t_Z`. Suppose the
candidate path satisfies (48) on `[0, t_Z]`, (49) on `(t_Z, t_C]`, (50) for `t ≤ t_C + 1`, the
Phillips curve at `t_C + 1` (i.e. (46)), `ξ₂,t_C+1 = 0`, and follows (42)–(43) (with
`ξ₁,t = δ^{t−t_C−1} ξ₁,t_C+1`, `ξ₂,t = 0`) after `t_C + 1`. If the sign conditions
`ξ₂,t ≥ 0` hold on `[0, t_C]` and `i ≥ 0` at `t_C + 1` and `t_C + 2`, then the candidate
satisfies the KKT system, is optimal, keeps `i_t = 0` on `[0, t_C]` (with `i ≥ 0` everywhere),
and is the unique optimal path. -/
theorem algorithm_verification {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) :
    KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, 0 ≤ impliedRate σ (natRate ρ η tZ) x π t) ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact backStep_nkpc_rate hσ.ne' (h48 t h) (by rw [hrn, natRate_of_le h])
    · exact backStep_nkpc_rate hσ.ne' (h49 t h ht) (by rw [hrn, natRate_of_lt h, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrate : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hi1
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        exact post_rate_nonneg hβ hβ1 hκ hϑ hρ htC hx hπ hi2 k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨(feasible_iff hσ).mpr fun t => ⟨hnkpc t, hrate t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1 : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2 : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1, l2, x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2, x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  -- bounded multipliers
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : Commitment.del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  -- finite loss
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - Commitment.del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * Commitment.del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * Commitment.del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  refine ⟨hK, kkt_optimal hβ hβ1 hσ hϑ hK hb hs, fun t ht => (hbind t ht).2, hrate,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Galí (2015), p. 152 (C5-9): the count of the algorithm's equations. The unknowns are
`(x_t, π_t, ξ₁,t, ξ₂,t)` for `t = 0, …, t_C + 1`, i.e. `4 (t_C + 2)`. The equations matching
them are (48)–(49) for `t ≤ t_C` (`2 (t_C + 1)`), (50) for `t ≤ t_C` (`2 (t_C + 1)`), (47) (`2`),
and — silently in the book — (46) and `ξ₂,t_C+1 = 0` (`1 + 1`); compare `algorithm_eq47`, which
derives (47) from (50) at `t_C + 1`, (46) and `ξ₂,t_C+1 = 0`. -/
theorem equation_count (tC : ℕ) :
    2 * (tC + 1) + 2 * (tC + 1) + 2 + 1 + 1 = 4 * (tC + 2) := by
  ring

end Gali.DiscretionCommitment.ZLBCommitment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.1: an optimized Taylor rule

Galí (2015), Chapter 5, Exercise 5.1, p. 159. The economy is
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + z_t`, `π_t = β E_t π_{t+1} + κ x_t + u_t`,
with i.i.d. mutually uncorrelated demand and supply shocks `z`, `u` (variances `σ_z²`, `σ_u²`),
and the central bank follows `i_t = ρ + φ_π π_t`.

## (a) The equilibrium
* `msv_equilibrium`: `x_t = (σ z_t − φ_π u_t)/(σ + κ φ_π)`,
  `π_t = σ (κ z_t + u_t)/(σ + κ φ_π)` is an equilibrium (i.i.d. shocks: `E_t z_{t+1} = 0`,
  `E_t u_{t+1} = 0`).
* `ex5_1a_unique`: for `φ_π > 1` every equilibrium whose deviation from it is bounded and
  adapted coincides with it (Galí's convention, also for unbounded, e.g. normal, shocks);
  `ex5_1a_unique_bounded`: in particular it is the unique bounded equilibrium for bounded shocks.
* `ex5_1a_not_unique`: for `0 ≤ φ_π ≤ 1` there are other bounded equilibria next to it, so
  `φ_π > 1` is exactly the determinacy region (`schurStable_A_iff`).

## (b) The optimal inflation coefficient
With a covariance form `B` (any bilinear form, e.g. the covariance) and uncorrelated shocks,
`ex5_1b_loss_eq`: `ϑ var x_t + var π_t = L(φ_π) = (ϑ σ_u² φ_π² + C)/(σ + κ φ_π)²`,
`C = σ² ((ϑ + κ²) σ_z² + σ_u²)`. `lossFn_eq` (a Lagrange identity) writes
`L(φ) = L* + (a σ φ − κ C)²/((a σ² + κ² C)(σ + κ φ)²)`, `a = ϑ σ_u²`, so
`φ_π* = (κσ/ϑ)[1 + (ϑ + κ²) σ_z²/σ_u²]` (`phiStar`, `phiStar_foc`) is the unique global
minimiser among all `φ` with `σ + κφ ≠ 0` (`lossFn_ge`, `lossFn_phiStar`). Over the
determinacy region:
`ex5_1b_optimal` (if `φ_π* > 1`, `φ_π*` is the unique minimiser over `φ_π > 1`, also in
terms of equilibrium losses, `ex5_1b_equilibrium_optimal`) and `ex5_1b_corner` (if
`φ_π* ≤ 1`, the loss is strictly increasing on `(1, ∞)` and has no minimiser there;
`lossFn_strictMonoOn`).

## (c) Comparative statics
`phiStar_eq_phiR`, `phiR_eq`: `φ_π* = φ(r) = κσ/ϑ + κσ r + κ³σ r/ϑ`, `r = σ_z²/σ_u²`;
`phiR_strictAntiOn_weight` (decreasing in `ϑ`), `phiR_strictMono_ratio` (increasing in `r`),
`phiR_strictMono_sigma`, `phiR_strictMonoOn_kappa`; `tendsto_phiR_weight_zero`,
`tendsto_phiR_ratio_atTop` (aggressive responses, `φ_π* → ∞`, when the weight on output
vanishes or demand shocks dominate), `tendsto_phiR_weight_atTop` (`φ_π* → κσ r`) and
`tendsto_phiR_ratio_zero` (`φ_π* → κσ/ϑ` with supply shocks only). The verbal discussion
of part (c) is not formalised beyond these statements.
-/

namespace Gali.DiscretionCommitment.Ex5_1

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Exercise 5.1, p. 159: the dynamic IS equation
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + z_t`. -/
def DIS (σ ρ : ℝ) (x infl i z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) + z t

/-- Galí (2015), Exercise 5.1, p. 159: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ x_t + u_t`. -/
def NKPC (β κ : ℝ) (x infl u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), Exercise 5.1, p. 159: the simple Taylor rule `i_t = ρ + φ_π π_t`. -/
def TaylorRule (ρ φ : ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φ • infl t

/-- Galí (2015), Exercise 5.1, p. 159: an equilibrium under the Taylor rule. -/
def Equilibrium (β σ κ ρ φ : ℝ) (z u x infl i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ ρ x infl i z ∧ NKPC 𝔼 β κ x infl u ∧ TaylorRule ρ φ infl i

/-- Galí (2015), Exercise 5.1(a): the homogeneous system satisfied by the difference of two
equilibria, `d^x_t = E_t d^x_{t+1} − σ⁻¹(φ_π d^π_t − E_t d^π_{t+1})`,
`d^π_t = β E_t d^π_{t+1} + κ d^x_t`. -/
def HomEq (β σ κ φ : ℝ) (dx dp : ℕ → Ω → ℝ) : Prop :=
  ∀ t, dx t = 𝔼.E t (dx (t + 1)) - σ⁻¹ • (φ • dp t - 𝔼.E t (dp (t + 1))) ∧
    dp t = β • 𝔼.E t (dp (t + 1)) + κ • dx t

/-- Galí (2015), Exercise 5.1(a): stacking `(x, π)` into a vector process. -/
def stack (x p : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, p t]

/-- Galí (2015), Exercise 5.1(a) (cf. ch. 4, eq. (13), p. 107, with `φ_y = 0`): the matrix
`A = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [κσ, κ + βσ]]` of the system `x_t = A E_t x_{t+1}`. -/
noncomputable def A (β σ κ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φ), (1 - β * φ) / (σ + κ * φ);
    κ * σ / (σ + κ * φ), (κ + β * σ) / (σ + κ * φ)]

/-- Galí (2015), Exercise 5.1(a): `tr A = (σ + κ + βσ)/(σ + κφ_π)`. -/
theorem tr2_A (β σ κ φ : ℝ) : tr2 (A β σ κ φ) = (σ + κ + β * σ) / (σ + κ * φ) := by
  simp only [tr2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), Exercise 5.1(a): `det A = βσ/(σ + κφ_π)`. -/
theorem det2_A {β σ κ φ : ℝ} (hD : σ + κ * φ ≠ 0) :
    det2 (A β σ κ φ) = β * σ / (σ + κ * φ) := by
  simp only [det2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Exercise 5.1(a), determinacy region** (Galí 2015, p. 159; ch. 4, (14) with
`φ_y = 0`): for `σ, κ > 0`, `0 < β < 1` and `φ_π ≥ 0`, the Schur–Cohn condition on `A` holds
iff `φ_π > 1`. -/
theorem schurStable_A_iff {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 ≤ φ) : SchurStable (tr2 (A β σ κ φ)) (det2 (A β σ κ φ)) ↔ 1 < φ := by
  have hD : 0 < σ + κ * φ := by positivity
  rw [tr2_A, det2_A hD.ne', SchurStable]
  have hdet : |β * σ / (σ + κ * φ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hD]
    nlinarith [mul_nonneg hκ.le hφ]
  have htr : |(σ + κ + β * σ) / (σ + κ * φ)| = (σ + κ + β * σ) / (σ + κ * φ) :=
    abs_of_pos (by positivity)
  rw [htr]
  constructor
  · rintro ⟨-, h⟩
    rw [div_lt_iff₀ hD, add_mul, one_mul, div_mul_cancel₀ _ hD.ne'] at h
    nlinarith
  · intro h
    refine ⟨hdet, ?_⟩
    rw [div_lt_iff₀ hD, add_mul, one_mul, div_mul_cancel₀ _ hD.ne']
    nlinarith

/-- Galí (2015), Exercise 5.1(a): the homogeneous structural system is the system
`d_t = A E_t d_{t+1}` in `(d^x, d^π)`. -/
theorem homEq_iff_solves {β σ κ φ : ℝ} (hσ : σ ≠ 0) (hD : σ + κ * φ ≠ 0)
    (dx dp : ℕ → Ω → ℝ) :
    HomEq 𝔼 β σ κ φ dx dp ↔ 𝔼.Solves (A β σ κ φ) 0 (stack dx dp) := by
  constructor
  · intro h t i
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have e1' : σ * dx t ω = σ * 𝔼.E t (dx (t + 1)) ω - (φ * dp t ω - 𝔼.E t (dp (t + 1)) ω) := by
      rw [e1]; field_simp
    fin_cases i <;>
      simp only [stack, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Fin.zero_eta, Fin.mk_one] <;>
      field_simp
    · linear_combination e1' - φ * e2
    · linear_combination κ * e1' + σ * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.zero_apply, add_zero] at h0 h1
    constructor
    · funext ω
      have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e0, e1]
      field_simp
      ring
    · funext ω
      have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e0, e1]
      field_simp
      ring

/-! ### (a) Existence and uniqueness -/

/-- Galí (2015), Exercise 5.1(a), p. 159: the output gap `x_t = (σ z_t − φ_π u_t)/(σ + κφ_π)`. -/
noncomputable def xs (σ κ φ : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ / (σ + κ * φ)) • z t + (-φ / (σ + κ * φ)) • u t

/-- Galí (2015), Exercise 5.1(a), p. 159: inflation `π_t = σ (κ z_t + u_t)/(σ + κφ_π)`. -/
noncomputable def ps (σ κ φ : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ * κ / (σ + κ * φ)) • z t + (σ / (σ + κ * φ)) • u t

/-- Galí (2015), Exercise 5.1, p. 159: the nominal rate implied by the rule, `ρ + φ_π π_t`. -/
def rate (ρ φ : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + φ • infl t

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): linear combinations of bounded processes are bounded. -/
theorem bounded_comb {z u : ℕ → Ω → ℝ} (hz : BoundedProc z) (hu : BoundedProc u) (a b : ℝ) :
    BoundedProc fun t => a • z t + b • u t := by
  obtain ⟨M, hM⟩ := hz
  obtain ⟨N, hN⟩ := hu
  refine ⟨|a| * M + |b| * N, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t ω) (abs_nonneg b)

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): differences of bounded processes are bounded. -/
theorem bounded_sub {x y : ℕ → Ω → ℝ} (hx : BoundedProc x) (hy : BoundedProc y) :
    BoundedProc (x - y) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hy
  exact ⟨M + N, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hN t ω))⟩

/-- Galí (2015), Exercise 5.1(a): linear combinations of adapted processes are adapted. -/
theorem adapted_comb {z u : ℕ → Ω → ℝ} (hz : 𝔼.Adapted z) (hu : 𝔼.Adapted u) (a b : ℝ) :
    𝔼.Adapted fun t => a • z t + b • u t := by
  intro t
  simp only [map_add, map_smul, hz t, hu t]

/-- **Exercise 5.1(a), existence** (Galí 2015, p. 159): with i.i.d. shocks
(`E_t z_{t+1} = E_t u_{t+1} = 0`), `x_t = (σ z_t − φ_π u_t)/(σ + κφ_π)`,
`π_t = σ (κ z_t + u_t)/(σ + κφ_π)`, `i_t = ρ + φ_π π_t` is an equilibrium. -/
theorem msv_equilibrium {β σ κ ρ φ : ℝ} (hσ : σ ≠ 0) (hD : σ + κ * φ ≠ 0)
    {z u : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u) :
    Equilibrium 𝔼 β σ κ ρ φ z u (xs σ κ φ z u) (ps σ κ φ z u) (rate ρ φ (ps σ κ φ z u)) := by
  have hEz : ∀ t, 𝔼.E t (z (t + 1)) = 0 := fun t => by rw [hz.2 t, zero_smul]
  have hEu : ∀ t, 𝔼.E t (u (t + 1)) = 0 := fun t => by rw [hu.2 t, zero_smul]
  have hEx : ∀ t, 𝔼.E t (xs σ κ φ z u (t + 1)) = 0 := fun t => by
    simp only [xs, map_add, map_smul, hEz, hEu, smul_zero, add_zero]
  have hEp : ∀ t, 𝔼.E t (ps σ κ φ z u (t + 1)) = 0 := fun t => by
    simp only [ps, map_add, map_smul, hEz, hEu, smul_zero, add_zero]
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · rw [hEx, hEp]
    funext ω
    simp only [xs, ps, rate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    field_simp
    ring
  · rw [hEp]
    funext ω
    simp only [xs, ps, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring

/-- Galí (2015), Exercise 5.1(a): the difference of two equilibria solves the homogeneous
system. -/
theorem equilibrium_sub {β σ κ ρ φ : ℝ} {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (h' : Equilibrium 𝔼 β σ κ ρ φ z u x' p' i') :
    HomEq 𝔼 β σ κ φ (x - x') (p - p') := by
  obtain ⟨hd, hn, hr⟩ := h
  obtain ⟨hd', hn', hr'⟩ := h'
  intro t
  have a1 := hd t
  have a2 := hd' t
  have b1 := hn t
  have b2 := hn' t
  rw [hr t] at a1
  rw [hr' t] at a2
  constructor
  · funext ω
    have e1 := congrFun a1 ω
    have e2 := congrFun a2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun b1 ω
    have e2 := congrFun b2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 ⊢
    rw [e1, e2]
    ring

/-- Galí (2015), Exercise 5.1(a): adding a solution of the homogeneous system to an
equilibrium gives an equilibrium. -/
theorem equilibrium_add_hom {β σ κ ρ φ : ℝ} {z u x p dx dp : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β σ κ ρ φ z u x p (rate ρ φ p)) (hd : HomEq 𝔼 β σ κ φ dx dp) :
    Equilibrium 𝔼 β σ κ ρ φ z u (x + dx) (p + dp) (rate ρ φ (p + dp)) := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (hd t).1 ω
    simp only [rate, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      map_add] at e1 e2 ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun (h2 t) ω
    have e2 := congrFun (hd t).2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] at e1 e2 ⊢
    rw [e1, e2]
    ring

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): stacking bounded processes. -/
theorem boundedVec_stack {x p : ℕ → Ω → ℝ} (hx : BoundedProc x) (hp : BoundedProc p) :
    BoundedVec (stack x p) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine ⟨max M N, fun t i ω => ?_⟩
  fin_cases i
  · exact (hM t ω).trans (le_max_left _ _)
  · exact (hN t ω).trans (le_max_right _ _)

/-- Galí (2015), Exercise 5.1(a): stacking adapted processes. -/
theorem adaptedVec_stack {x p : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hp : 𝔼.Adapted p) :
    𝔼.AdaptedVec (stack x p) := by
  intro t i
  fin_cases i
  · exact hx t
  · exact hp t

/-- Galí (2015), Exercise 5.1(a): the equilibrium output gap and inflation are adapted. -/
theorem msv_adapted {σ κ φ : ℝ} {z u : ℕ → Ω → ℝ} (hz : 𝔼.Adapted z) (hu : 𝔼.Adapted u) :
    𝔼.Adapted (xs σ κ φ z u) ∧ 𝔼.Adapted (ps σ κ φ z u) :=
  ⟨adapted_comb 𝔼 hz hu _ _, adapted_comb 𝔼 hz hu _ _⟩

/-- **Exercise 5.1(a), uniqueness** (Galí 2015, p. 159): for `φ_π > 1`, every equilibrium
`(x, π, i)` with adapted `x, π` whose deviation from the solution above is bounded coincides
with it. -/
theorem ex5_1a_unique {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u)) :
    x = xs σ κ φ z u ∧ p = ps σ κ φ z u ∧ i = rate ρ φ (ps σ κ φ z u) := by
  have hD : 0 < σ + κ * φ := by nlinarith
  have hS := (schurStable_A_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ
  have hhom := equilibrium_sub 𝔼 he (msv_equilibrium 𝔼 (ρ := ρ) (β := β) hσ.ne' hD.ne' hz hu)
  have hsol := (homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mp hhom
  obtain ⟨hxa, hpa⟩ := msv_adapted 𝔼 (σ := σ) (κ := κ) (φ := φ) hz.1 hu.1
  have had : 𝔼.AdaptedVec (stack (x - xs σ κ φ z u) (p - ps σ κ φ z u)) :=
    adaptedVec_stack 𝔼 (fun t => by simp only [Pi.sub_apply, map_sub, hax t, hxa t])
      (fun t => by simp only [Pi.sub_apply, map_sub, hap t, hpa t])
  have h0 : 𝔼.Solves (A β σ κ φ) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hS hsol h0 had (fun t i => by simp) (boundedVec_stack hbx hbp)
    ⟨0, fun t i ω => by simp⟩
  have hx : x = xs σ κ φ z u := by
    funext t
    have := congrFun (congrFun heq t) 0
    simpa [stack, sub_eq_zero] using this
  have hp : p = ps σ κ φ z u := by
    funext t
    have := congrFun (congrFun heq t) 1
    simpa [stack, sub_eq_zero] using this
  refine ⟨hx, hp, ?_⟩
  funext t
  rw [he.2.2 t, hp]
  rfl

/-- **Exercise 5.1(a)** (Galí 2015, p. 159; Galí's convention): with bounded i.i.d. shocks and
`φ_π > 1`, the solution above is the unique equilibrium with bounded adapted `x` and `π`. -/
theorem ex5_1a_unique_bounded {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (hzb : BoundedProc z) (hub : BoundedProc u) (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i)
    (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p) (hbx : BoundedProc x) (hbp : BoundedProc p) :
    x = xs σ κ φ z u ∧ p = ps σ κ φ z u ∧ i = rate ρ φ (ps σ κ φ z u) :=
  ex5_1a_unique 𝔼 hσ hκ hβ0 hβ1 hφ hz hu he hax hap
    (bounded_sub hbx (bounded_comb hzb hub _ _)) (bounded_sub hbp (bounded_comb hzb hub _ _))

/-- **Exercise 5.1(a), indeterminacy** (Galí 2015, p. 159): for `0 ≤ φ_π ≤ 1` there is
another equilibrium, with adapted `x, π` at a bounded (nonzero) distance from the solution
above. -/
theorem ex5_1a_not_unique [Nonempty Ω] {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {z u : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z)
    (hu : 𝔼.IsAR1 0 u) :
    ∃ x p i, Equilibrium 𝔼 β σ κ ρ φ z u x p i ∧ 𝔼.Adapted x ∧ 𝔼.Adapted p ∧
      BoundedProc (x - xs σ κ φ z u) ∧ BoundedProc (p - ps σ κ φ z u) ∧
      ¬ (x = xs σ κ φ z u ∧ p = ps σ κ φ z u) := by
  have hD : 0 < σ + κ * φ := by positivity
  have hS : ¬ SchurStable (tr2 (A β σ κ φ)) (det2 (A β σ κ φ)) := by
    rw [schurStable_A_iff hσ hκ hβ0 hβ1 hφ0]; linarith
  have h0 : 𝔼.Solves (A β σ κ φ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ :=
    𝔼.system_not_unique hS h0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t i
    fin_cases i <;> rfl
  have hhom : HomEq 𝔼 β σ κ φ (fun t => y t 0) (fun t => y t 1) :=
    (homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mpr (by rw [hst]; exact hy)
  obtain ⟨hxa, hpa⟩ := msv_adapted 𝔼 (σ := σ) (κ := κ) (φ := φ) hz.1 hu.1
  refine ⟨xs σ κ φ z u + fun t => y t 0, ps σ κ φ z u + fun t => y t 1, _,
    equilibrium_add_hom 𝔼 (msv_equilibrium 𝔼 hσ.ne' hD.ne' hz hu) hhom,
    fun t => by simp only [Pi.add_apply, map_add, hxa t, hay t 0],
    fun t => by simp only [Pi.add_apply, map_add, hpa t, hay t 1],
    ⟨M, fun t ω => by simpa using hM t 0 ω⟩, ⟨M, fun t ω => by simpa using hM t 1 ω⟩, ?_⟩
  rintro ⟨h1, h2⟩
  apply hne
  funext t i
  fin_cases i
  · funext ω
    have := congrFun (congrFun h1 t) ω
    simpa using this
  · funext ω
    have := congrFun (congrFun h2 t) ω
    simpa using this

/-! ### (b) The loss and its minimiser -/

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(b): for a bilinear covariance form `B` and uncorrelated `z, u`,
`var (a z + b u) = a² var z + b² var u` (restated from the Chapter 4 project, Ex. 4.2). -/
theorem bilin_quad (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (a b : ℝ) (z u : Ω → ℝ)
    (h1 : B z u = 0) (h2 : B u z = 0) :
    B (a • z + b • u) (a • z + b • u) = a ^ 2 * B z z + b ^ 2 * B u u := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Galí (2015), Exercise 5.1(b), p. 159: the loss `ϑ var x_t + var π_t` under the rule as a
function of `φ_π`: `L(φ_π) = (ϑ σ_u² φ_π² + σ²((ϑ + κ²) σ_z² + σ_u²))/(σ + κφ_π)²`. -/
noncomputable def lossFn (ϑ σ κ vz vu φ : ℝ) : ℝ :=
  (ϑ * vu * φ ^ 2 + σ ^ 2 * ((ϑ + κ ^ 2) * vz + vu)) / (σ + κ * φ) ^ 2

/-- Galí (2015), Exercise 5.1(b): the constant `C = σ²((ϑ + κ²) σ_z² + σ_u²)` of the loss. -/
def lossC (ϑ σ κ vz vu : ℝ) : ℝ := σ ^ 2 * ((ϑ + κ ^ 2) * vz + vu)

/-- Galí (2015), Exercise 5.1(b): the minimum loss `L* = a C/(a σ² + κ² C)`, `a = ϑ σ_u²`. -/
noncomputable def lossMin (ϑ σ κ vz vu : ℝ) : ℝ :=
  ϑ * vu * lossC ϑ σ κ vz vu / (ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu)

/-- **Exercise 5.1(b), the optimal coefficient** (Galí 2015, p. 159):
`φ_π* = (κσ/ϑ)[1 + (ϑ + κ²) σ_z²/σ_u²]`. -/
noncomputable def phiStar (ϑ σ κ vz vu : ℝ) : ℝ := κ * σ / ϑ * (1 + (ϑ + κ ^ 2) * vz / vu)

/-- Galí (2015), Exercise 5.1(b): the equilibrium loss is `L(φ_π)`. For `φ_π > 1`, in the
unique equilibrium, with `var z_t = σ_z²`, `var u_t = σ_u²` and `z_t, u_t` uncorrelated
under the covariance form `B`, `ϑ var x_t + var π_t = L(φ_π)`. -/
theorem ex5_1b_loss_eq (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρ φ ϑ vz vu : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ)
    {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u)) (t : ℕ)
    (hvz : B (z t) (z t) = vz) (hvu : B (u t) (u t) = vu) (h1 : B (z t) (u t) = 0)
    (h2 : B (u t) (z t) = 0) :
    ϑ * B (x t) (x t) + B (p t) (p t) = lossFn ϑ σ κ vz vu φ := by
  obtain ⟨hx, hp, -⟩ := ex5_1a_unique 𝔼 hσ hκ hβ0 hβ1 hφ hz hu he hax hap hbx hbp
  have hD : σ + κ * φ ≠ 0 := by nlinarith
  rw [hx, hp]
  simp only [xs, ps]
  rw [bilin_quad B _ _ _ _ h1 h2, bilin_quad B _ _ _ _ h1 h2, hvz, hvu, lossFn]
  field_simp
  ring

/-- **Exercise 5.1(b), the Lagrange identity** (Galí 2015, p. 159): with `a = ϑ σ_u²`,
`L(φ) = L* + (a σ φ − κ C)²/((a σ² + κ² C)(σ + κ φ)²)`. -/
theorem lossFn_eq {ϑ σ κ vz vu φ : ℝ} (hD : σ + κ * φ ≠ 0)
    (hK : ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu ≠ 0) :
    lossFn ϑ σ κ vz vu φ = lossMin ϑ σ κ vz vu +
      (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
        ((ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu) * (σ + κ * φ) ^ 2) := by
  unfold lossFn lossMin
  rw [div_add_div _ _ hK (mul_ne_zero hK (pow_ne_zero 2 hD)), div_eq_div_iff (pow_ne_zero 2 hD)
    (mul_ne_zero hK (mul_ne_zero hK (pow_ne_zero 2 hD)))]
  unfold lossC
  ring

/-- Galí (2015), Exercise 5.1(b): `C > 0`. -/
theorem lossC_pos {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hvz : 0 ≤ vz) (hvu : 0 < vu) :
    0 < lossC ϑ σ κ vz vu := by
  unfold lossC; positivity

/-- Galí (2015), Exercise 5.1(b): `φ_π* > 0`. -/
theorem phiStar_pos {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) : 0 < phiStar ϑ σ κ vz vu := by
  unfold phiStar; positivity

/-- Galí (2015), Exercise 5.1(b): `φ_π*` is the root of the first-order condition,
`a σ φ_π* = κ C`. -/
theorem phiStar_foc {ϑ σ κ vz vu : ℝ} (hϑ : ϑ ≠ 0) (hvu : vu ≠ 0) :
    ϑ * vu * σ * phiStar ϑ σ κ vz vu = κ * lossC ϑ σ κ vz vu := by
  unfold phiStar lossC
  field_simp
  ring

/-- **Exercise 5.1(b), global minimum** (Galí 2015, p. 159): `L* ≤ L(φ)` for every `φ` with
`σ + κφ ≠ 0`, with equality iff `φ = φ_π*`. -/
theorem lossFn_ge {ϑ σ κ vz vu φ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hvz : 0 ≤ vz) (hvu : 0 < vu)
    (hD : σ + κ * φ ≠ 0) :
    lossMin ϑ σ κ vz vu ≤ lossFn ϑ σ κ vz vu φ ∧
      (lossFn ϑ σ κ vz vu φ = lossMin ϑ σ κ vz vu ↔ φ = phiStar ϑ σ κ vz vu) := by
  have hC := lossC_pos (κ := κ) hϑ hσ hvz hvu
  have hK : 0 < ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu := by positivity
  rw [lossFn_eq hD hK.ne']
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have hfoc := phiStar_foc (σ := σ) (κ := κ) (vz := vz) hϑ.ne' hvu.ne'
  constructor
  · intro h
    have h0 : (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
        ((ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu) * (σ + κ * φ) ^ 2) = 0 := by linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have h00 : ϑ * vu * σ * φ = ϑ * vu * σ * phiStar ϑ σ κ vz vu := by
        rw [hfoc]; linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h0]
      exact mul_left_cancel₀ (by positivity) h00
    · exact absurd h0 (mul_ne_zero hK.ne' (pow_ne_zero 2 hD))
  · intro h
    rw [h, hfoc, sub_self]
    simp

/-- **Exercise 5.1(b)** (Galí 2015, p. 159): `L(φ_π*) = L*`. -/
theorem lossFn_phiStar {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) : lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) = lossMin ϑ σ κ vz vu := by
  have hD : σ + κ * phiStar ϑ σ κ vz vu ≠ 0 := by
    have := phiStar_pos hϑ hσ hκ hvz hvu; positivity
  exact ((lossFn_ge hϑ hσ hvz hvu hD).2).mpr rfl

/-- **Exercise 5.1(b), the optimal rule** (Galí 2015, p. 159): if `φ_π* > 1`, then `φ_π*` is
the unique minimiser of `L` over the determinacy region `φ_π > 1`. -/
theorem ex5_1b_optimal {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) (h1 : 1 < phiStar ϑ σ κ vz vu) :
    phiStar ϑ σ κ vz vu ∈ Set.Ioi (1 : ℝ) ∧
      (∀ φ ∈ Set.Ioi (1 : ℝ), lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) ≤ lossFn ϑ σ κ vz vu φ) ∧
      ∀ φ ∈ Set.Ioi (1 : ℝ),
        lossFn ϑ σ κ vz vu φ = lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) →
          φ = phiStar ϑ σ κ vz vu := by
  rw [lossFn_phiStar hϑ hσ hκ hvz hvu]
  refine ⟨h1, fun φ hφ => ?_, fun φ hφ h => ?_⟩
  · have hD : σ + κ * φ ≠ 0 := by
      have : (1 : ℝ) < φ := hφ
      nlinarith
    exact (lossFn_ge hϑ hσ hvz hvu hD).1
  · have hD : σ + κ * φ ≠ 0 := by
      have : (1 : ℝ) < φ := hφ
      nlinarith
    exact ((lossFn_ge hϑ hσ hvz hvu hD).2).mp h

/-- Galí (2015), Exercise 5.1(b): the loss is strictly increasing to the right of `φ_π*`
(where `σ + κφ > 0`). -/
theorem lossFn_strictMonoOn {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hvz : 0 ≤ vz) (hvu : 0 < vu) :
    StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ici (phiStar ϑ σ κ vz vu)) := by
  intro φ₁ h₁ φ₂ h₂ h12
  simp only [Set.mem_Ici] at h₁ h₂
  have hp := phiStar_pos hϑ hσ hκ hvz hvu
  have hC := lossC_pos (κ := κ) hϑ hσ hvz hvu
  have hK : 0 < ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu := by positivity
  have hD1 : 0 < σ + κ * φ₁ := by nlinarith
  have hD2 : 0 < σ + κ * φ₂ := by nlinarith
  have hfoc := phiStar_foc (σ := σ) (κ := κ) (vz := vz) hϑ.ne' hvu.ne'
  have ha : 0 < ϑ * vu * σ := by positivity
  rw [lossFn_eq hD1.ne' hK.ne', lossFn_eq hD2.ne' hK.ne', add_lt_add_iff_left]
  set K := ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu
  set g := fun φ : ℝ => (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) / (σ + κ * φ) with hg
  have hrw : ∀ φ : ℝ, 0 < σ + κ * φ → (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
      (K * (σ + κ * φ) ^ 2) = g φ ^ 2 / K := by
    intro φ hφ
    simp only [hg]
    field_simp
  rw [hrw φ₁ hD1, hrw φ₂ hD2]
  have hg1 : 0 ≤ g φ₁ := by
    simp only [hg]
    refine div_nonneg ?_ hD1.le
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha.le]
  have hg12 : g φ₂ - g φ₁ = K * (φ₂ - φ₁) / ((σ + κ * φ₁) * (σ + κ * φ₂)) := by
    simp only [hg, K]
    rw [div_sub_div _ _ hD2.ne' hD1.ne', div_eq_div_iff (mul_ne_zero hD2.ne' hD1.ne')
      (mul_ne_zero hD1.ne' hD2.ne')]
    unfold lossC
    ring
  have hlt : g φ₁ < g φ₂ := by
    have : 0 < K * (φ₂ - φ₁) / ((σ + κ * φ₁) * (σ + κ * φ₂)) := by
      apply div_pos (mul_pos hK (by linarith)) (mul_pos hD1 hD2)
    linarith
  exact div_lt_div_of_pos_right (by nlinarith) hK

/-- **Exercise 5.1(b), the corner case** (Galí 2015, p. 159): if `φ_π* ≤ 1`, the loss is
strictly increasing on the determinacy region `φ_π > 1`, so it has no minimiser there. -/
theorem ex5_1b_corner {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) (h1 : phiStar ϑ σ κ vz vu ≤ 1) :
    StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ioi 1) ∧
      ¬ ∃ φ ∈ Set.Ioi (1 : ℝ), ∀ φ' ∈ Set.Ioi (1 : ℝ),
        lossFn ϑ σ κ vz vu φ ≤ lossFn ϑ σ κ vz vu φ' := by
  have hmono : StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ioi 1) :=
    (lossFn_strictMonoOn hϑ hσ hκ hvz hvu).mono fun φ hφ => by
      simp only [Set.mem_Ioi] at hφ
      simp only [Set.mem_Ici]
      linarith
  refine ⟨hmono, ?_⟩
  rintro ⟨φ, hφ, hmin⟩
  simp only [Set.mem_Ioi] at hφ
  have hm : (1 + φ) / 2 ∈ Set.Ioi (1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have := hmono hm (Set.mem_Ioi.mpr hφ) (by linarith)
  linarith [hmin _ hm]

/-- **Exercise 5.1(b) in terms of equilibria** (Galí 2015, p. 159): if `φ_π* > 1`, the
equilibrium loss `ϑ var x_t + var π_t` under `φ_π*` is at most that under any `φ_π > 1`, and
strictly smaller unless `φ_π = φ_π*`. -/
theorem ex5_1b_equilibrium_optimal (B : LinearMap.BilinForm ℝ (Ω → ℝ))
    {β σ κ ρ φ ϑ vz vu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) (hvz0 : 0 ≤ vz) (hvu0 : 0 < vu) (h1 : 1 < phiStar ϑ σ κ vz vu) (hφ : 1 < φ)
    {z u x p i x' p' i' : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u))
    (he' : Equilibrium 𝔼 β σ κ ρ (phiStar ϑ σ κ vz vu) z u x' p' i') (hax' : 𝔼.Adapted x')
    (hap' : 𝔼.Adapted p') (hbx' : BoundedProc (x' - xs σ κ (phiStar ϑ σ κ vz vu) z u))
    (hbp' : BoundedProc (p' - ps σ κ (phiStar ϑ σ κ vz vu) z u)) (t : ℕ)
    (hvz : B (z t) (z t) = vz) (hvu : B (u t) (u t) = vu) (hzu : B (z t) (u t) = 0)
    (huz : B (u t) (z t) = 0) :
    ϑ * B (x' t) (x' t) + B (p' t) (p' t) ≤ ϑ * B (x t) (x t) + B (p t) (p t) ∧
      (ϑ * B (x t) (x t) + B (p t) (p t) = ϑ * B (x' t) (x' t) + B (p' t) (p' t) →
        φ = phiStar ϑ σ κ vz vu) := by
  rw [ex5_1b_loss_eq 𝔼 B hσ hκ hβ0 hβ1 hφ hz hu he hax hap hbx hbp t hvz hvu hzu huz,
    ex5_1b_loss_eq 𝔼 B hσ hκ hβ0 hβ1 h1 hz hu he' hax' hap' hbx' hbp' t hvz hvu hzu huz]
  obtain ⟨-, hle, huniq⟩ := ex5_1b_optimal hϑ hσ hκ hvz0 hvu0 h1
  exact ⟨hle φ hφ, huniq φ hφ⟩

/-! ### (c) Comparative statics -/

/-- Galí (2015), Exercise 5.1(c): `φ_π*` as a function of the variance ratio
`r = σ_z²/σ_u²`, `φ(r) = (κσ/ϑ)(1 + (ϑ + κ²) r)`. -/
noncomputable def phiR (ϑ σ κ r : ℝ) : ℝ := κ * σ / ϑ * (1 + (ϑ + κ ^ 2) * r)

/-- Galí (2015), Exercise 5.1(c): `φ_π* = φ(σ_z²/σ_u²)`. -/
theorem phiStar_eq_phiR (ϑ σ κ vz vu : ℝ) : phiStar ϑ σ κ vz vu = phiR ϑ σ κ (vz / vu) := by
  unfold phiStar phiR; ring

/-- Galí (2015), Exercise 5.1(c): `φ(r) = κσ/ϑ + κσ r + κ³σ r/ϑ`. -/
theorem phiR_eq {ϑ : ℝ} (hϑ : ϑ ≠ 0) (σ κ r : ℝ) :
    phiR ϑ σ κ r = κ * σ * (1 + κ ^ 2 * r) / ϑ + κ * σ * r := by
  unfold phiR; field_simp; ring

/-- **Exercise 5.1(c), the weight on output** (Galí 2015, p. 159): `φ_π*` is strictly
decreasing in `ϑ > 0`. -/
theorem phiR_strictAntiOn_weight {σ κ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    StrictAntiOn (fun ϑ => phiR ϑ σ κ r) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only [phiR_eq ha.ne', phiR_eq hb.ne', add_lt_add_iff_right]
  exact div_lt_div_of_pos_left (by positivity) ha hab

/-- **Exercise 5.1(c), the variance ratio** (Galí 2015, p. 159): `φ_π*` is strictly increasing
in `r = σ_z²/σ_u²`. -/
theorem phiR_strictMono_ratio {ϑ σ κ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono (fun r => phiR ϑ σ κ r) := by
  intro a b hab
  simp only [phiR]
  have : 0 < κ * σ / ϑ := by positivity
  have : 0 < ϑ + κ ^ 2 := by positivity
  nlinarith [mul_pos this (sub_pos.mpr hab), mul_pos ‹0 < κ * σ / ϑ› (mul_pos this
    (sub_pos.mpr hab))]

/-- Galí (2015), Exercise 5.1(c): `φ_π*` is strictly increasing in `σ` (for `r ≥ 0`). -/
theorem phiR_strictMono_sigma {ϑ κ r : ℝ} (hϑ : 0 < ϑ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    StrictMono (fun σ => phiR ϑ σ κ r) := by
  intro a b hab
  simp only [phiR]
  have h : 0 < κ / ϑ * (1 + (ϑ + κ ^ 2) * r) := by positivity
  have ea : κ * a / ϑ * (1 + (ϑ + κ ^ 2) * r) = a * (κ / ϑ * (1 + (ϑ + κ ^ 2) * r)) := by ring
  have eb : κ * b / ϑ * (1 + (ϑ + κ ^ 2) * r) = b * (κ / ϑ * (1 + (ϑ + κ ^ 2) * r)) := by ring
  rw [ea, eb]
  exact mul_lt_mul_of_pos_right hab h

/-- Galí (2015), Exercise 5.1(c): `φ_π*` is strictly increasing in the slope `κ > 0`
(for `r ≥ 0`). -/
theorem phiR_strictMonoOn_kappa {ϑ σ r : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hr : 0 ≤ r) :
    StrictMonoOn (fun κ => phiR ϑ σ κ r) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only [phiR_eq hϑ.ne']
  have h1 : a * σ * (1 + a ^ 2 * r) < b * σ * (1 + b ^ 2 * r) := by
    have h3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha.le hab.le 3
    have ea : a * σ * (1 + a ^ 2 * r) = a * σ + σ * r * a ^ 3 := by ring
    have eb : b * σ * (1 + b ^ 2 * r) = b * σ + σ * r * b ^ 3 := by ring
    rw [ea, eb]
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hσ.le hr),
      mul_lt_mul_of_pos_right hab hσ]
  have h2 : a * σ * r ≤ b * σ * r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab.le hσ.le) hr
  have := div_lt_div_of_pos_right h1 hϑ
  linarith

/-- **Exercise 5.1(c), aggressive responses** (Galí 2015, p. 159): as the weight on output
`ϑ → 0⁺`, `φ_π* → ∞`. -/
theorem tendsto_phiR_weight_zero {σ κ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    Tendsto (fun ϑ => phiR ϑ σ κ r) (𝓝[>] 0) atTop := by
  have hc : 0 < κ * σ * (1 + κ ^ 2 * r) := by positivity
  have h : Tendsto (fun ϑ : ℝ => κ * σ * (1 + κ ^ 2 * r) * ϑ⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [self_mem_nhdsWithin] with ϑ hϑ
  simp only [Set.mem_Ioi] at hϑ
  rw [phiR_eq hϑ.ne', ← div_eq_mul_inv]
  have : 0 ≤ κ * σ * r := by positivity
  linarith

/-- **Exercise 5.1(c), aggressive responses** (Galí 2015, p. 159): as demand shocks dominate,
`r = σ_z²/σ_u² → ∞`, `φ_π* → ∞`. -/
theorem tendsto_phiR_ratio_atTop {ϑ σ κ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun r => phiR ϑ σ κ r) atTop atTop := by
  have hc : 0 < κ * σ / ϑ * (ϑ + κ ^ 2) := by positivity
  have h : Tendsto (fun r : ℝ => κ * σ / ϑ + κ * σ / ϑ * (ϑ + κ ^ 2) * r) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hc)
  refine h.congr fun r => ?_
  simp only [phiR]
  ring

/-- Galí (2015), Exercise 5.1(c): as `ϑ → ∞`, `φ_π* → κσ r`. -/
theorem tendsto_phiR_weight_atTop (σ κ r : ℝ) :
    Tendsto (fun ϑ => phiR ϑ σ κ r) atTop (𝓝 (κ * σ * r)) := by
  have h : Tendsto (fun ϑ : ℝ => κ * σ * (1 + κ ^ 2 * r) / ϑ + κ * σ * r) atTop
      (𝓝 (0 + κ * σ * r)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ϑ hϑ
  rw [phiR_eq hϑ.ne']

/-- Galí (2015), Exercise 5.1(c): with supply shocks only (`r → 0`), `φ_π* → κσ/ϑ`. -/
theorem tendsto_phiR_ratio_zero (ϑ σ κ : ℝ) :
    Tendsto (fun r => phiR ϑ σ κ r) (𝓝 0) (𝓝 (κ * σ / ϑ)) := by
  have hc : Continuous fun r : ℝ => phiR ϑ σ κ r := by
    unfold phiR; fun_prop
  have := hc.tendsto 0
  simpa [phiR] using this

end Gali.DiscretionCommitment.Ex5_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.2: optimal Markovian policy

Galí (2015), Chapter 5, Exercise 5.2, p. 160. Inflation follows the New Keynesian Phillips
curve `π_t = β E_t π_{t+1} + κ x_t + u_t` with an AR(1) cost-push shock
(`E_t u_{t+1} = ρ_u u_t`). In period 0 the central bank chooses, once and for all, a policy
`x_t = ψ_x u_t`, `π_t = ψ_π u_t` minimising `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to the
Phillips curve at every date.

The loss is a genuine infinite sum, `loss x π ω = ∑' t, βᵗ E_0[π_t² + ϑ x_t²](ω)`, summable for
bounded processes (`loss_summable`). For a Markov policy it factors as
`(ψ_π² + ϑ ψ_x²) W`, `W = ∑' t, βᵗ E_0[u_t²]` (`loss_markov`, `shockWeight_pos`).

## (a) The optimal Markov policy
`markov_feasible_iff`: the policy satisfies the Phillips curve at every date iff
`ψ_π (1 − βρ_u) = κ ψ_x + 1` (for a shock that is not identically zero). `objective_eq`:
on that line `ψ_π² + ϑψ_x² = ϑ/Δ + (ψ_π − ψ_π*)² + ϑ (ψ_x − ψ_x*)²` with
`Δ = κ² + ϑ(1 − βρ_u)²`, `ψ_π* = ϑ(1 − βρ_u)/Δ`, `ψ_x* = −κ/Δ`; hence `ex5_2a` (the unique
minimiser of the loss among feasible Markov policies).

## (b) Comparison with discretion
`discretion_unique`: the discretionary targeting rule `x_t = −(κ/ϑ) π_t` (text, eq. (4)) has
the unique bounded solution `π_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))`, `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))`
(text, eqs. (5)–(6)); it is a feasible Markov policy. `ex5_2b`: the optimal Markov policy is
weakly better than discretion, **strictly better iff `ρ_u ≠ 0`** (for either sign of `ρ_u`), and
coincides with discretion when `ρ_u = 0`.

## (c) Comparison with commitment
`ex5_2c`: for every `|ρ_u| < 1` there is a feasible (bounded, adapted) commitment path with a
strictly lower loss than the optimal Markov policy, built by perturbing the Markov path at
dates 0 (`ρ_u ≠ 0`) or 0 and 1 (`ρ_u = 0`). Hence (`ex5_2c_commitment`) any optimal policy
under commitment is strictly better than the optimal Markov policy (in particular weakly
better), and the optimal Markov policy is not optimal under commitment.
-/

namespace Gali.DiscretionCommitment.Ex5_2

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model and the loss -/

/-- Galí (2015), Exercise 5.2, p. 160: the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_t`
at every date. -/
def NKPC (β κ : ℝ) (x infl u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), Exercise 5.2, p. 160: the date-`t` term `βᵗ E_0[π_t² + ϑ x_t²]` of the loss. -/
noncomputable def lossTerm (β ϑ : ℝ) (x infl : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  β ^ t * 𝔼.E 0 (fun ω' => infl t ω' ^ 2 + ϑ * x t ω' ^ 2) ω

/-- Galí (2015), Exercise 5.2, p. 160: the loss `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` (in state `ω`). -/
noncomputable def loss (β ϑ : ℝ) (x infl : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, lossTerm 𝔼 β ϑ x infl ω t

/-- Galí (2015), Exercise 5.2: the shock weight `W = ∑' t, βᵗ E_0[u_t²]`. -/
noncomputable def shockWeight (β : ℝ) (u : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => u t ω' ^ 2) ω

/-- Galí (2015), Exercise 5.2: a Markov policy `x_t = ψ_x u_t`, `π_t = ψ_π u_t`. -/
def markov (ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψ • u t

/-- Galí (2015), Exercise 5.2: `E_t` of a nonnegative random variable is nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : 0 ≤ f) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have h := 𝔼.mono t hf ω
  simpa using h

/-- Galí (2015), Exercise 5.2: for bounded processes the loss series is summable
(`0 ≤ β < 1`, `ϑ ≥ 0`). -/
theorem loss_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) {x p : ℕ → Ω → ℝ}
    (hx : BoundedProc x) (hp : BoundedProc p) (ω : Ω) :
    Summable (lossTerm 𝔼 β ϑ x p ω) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (N ^ 2 + ϑ * M ^ 2)) (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) 0 ω) (pow_nonneg hβ0 t)
  have h1 : p t ω' ^ 2 ≤ N ^ 2 := by
    have := hN t ω'; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : x t ω' ^ 2 ≤ M ^ 2 := by
    have := hM t ω'; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-- Galí (2015), Exercise 5.2: the shock-weight series is summable for bounded `u`. -/
theorem shockWeight_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (ω : Ω) :
    Summable (fun t => β ^ t * 𝔼.E 0 (fun ω' => u t ω' ^ 2) ω) := by
  have h := loss_summable 𝔼 hβ0 hβ1 le_rfl (x := 0) ⟨0, fun _ _ => by simp⟩ hu ω
  refine h.congr fun t => ?_
  simp [lossTerm]

/-- Galí (2015), Exercise 5.2: `W ≥ E_0[u_0²] > 0` when `E_0[u_0²] > 0`. -/
theorem shockWeight_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    0 < shockWeight 𝔼 β u ω := by
  have hs := shockWeight_summable 𝔼 hβ0 hβ1 hu ω
  have hle := hs.le_tsum 0 (fun t _ =>
    mul_nonneg (pow_nonneg hβ0 t) (E_nonneg 𝔼 (fun ω' => sq_nonneg _) 0 ω))
  simp only [pow_zero, one_mul] at hle
  exact h0.trans_le hle

/-- Galí (2015), Exercise 5.2, p. 160: the loss of a Markov policy is
`(ψ_π² + ϑ ψ_x²) ∑' t, βᵗ E_0[u_t²]`. -/
theorem loss_markov (β ϑ ψx ψp : ℝ) (u : ℕ → Ω → ℝ) (ω : Ω) :
    loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω = (ψp ^ 2 + ϑ * ψx ^ 2) * shockWeight 𝔼 β u ω := by
  unfold loss shockWeight lossTerm
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  have hf : (fun ω' => markov ψp u t ω' ^ 2 + ϑ * markov ψx u t ω' ^ 2) =
      (ψp ^ 2 + ϑ * ψx ^ 2) • fun ω' => u t ω' ^ 2 := by
    funext ω'
    simp only [markov, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (a) The optimal Markov policy -/

/-- Galí (2015), Exercise 5.2(a): at date `t` a Markov policy satisfies the Phillips curve iff
`(ψ_π (1 − βρ_u) − κψ_x − 1) u_t = 0`. -/
theorem markov_nkpc_iff {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) :
    markov ψp u t = β • 𝔼.E t (markov ψp u (t + 1)) + κ • markov ψx u t + u t ↔
      (ψp * (1 - β * ρ) - κ * ψx - 1) • u t = 0 := by
  simp only [markov, map_smul, hu.2 t, smul_smul]
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this

/-- Galí (2015), Exercise 5.2(a): a Markov policy on the constraint line
`ψ_π (1 − βρ_u) = κ ψ_x + 1` satisfies the Phillips curve at every date. -/
theorem markov_feasible {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (h : ψp * (1 - β * ρ) = κ * ψx + 1) : NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u := by
  intro t
  refine (markov_nkpc_iff 𝔼 hu t).mpr ?_
  rw [show ψp * (1 - β * ρ) - κ * ψx - 1 = 0 by linarith, zero_smul]

/-- Galí (2015), Exercise 5.2(a): a Markov policy satisfies the Phillips curve at every date
iff `ψ_π (1 − βρ_u) = κ ψ_x + 1`, for a shock that is not identically zero. -/
theorem markov_feasible_iff {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hne : ∃ t ω, u t ω ≠ 0) :
    NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u ↔ ψp * (1 - β * ρ) = κ * ψx + 1 := by
  refine ⟨fun h => ?_, markov_feasible 𝔼 hu⟩
  obtain ⟨t, ω, hω⟩ := hne
  have h1 := congrFun ((markov_nkpc_iff 𝔼 hu t).mp (h t)) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · linarith
  · exact absurd h1 hω

/-- Galí (2015), Exercise 5.2(a): `Δ = κ² + ϑ(1 − βρ_u)²`. -/
def delta2 (β κ ϑ ρ : ℝ) : ℝ := κ ^ 2 + ϑ * (1 - β * ρ) ^ 2

/-- **Exercise 5.2(a)** (Galí 2015, p. 160): the optimal `ψ_π* = ϑ(1 − βρ_u)/Δ`. -/
noncomputable def psiP (β κ ϑ ρ : ℝ) : ℝ := ϑ * (1 - β * ρ) / delta2 β κ ϑ ρ

/-- **Exercise 5.2(a)** (Galí 2015, p. 160): the optimal `ψ_x* = −κ/Δ`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / delta2 β κ ϑ ρ

/-- Galí (2015), Exercise 5.2(a): the objective `ψ_π² + ϑ ψ_x²` per unit of shock weight. -/
def objective (ϑ ψx ψp : ℝ) : ℝ := ψp ^ 2 + ϑ * ψx ^ 2

/-- Galí (2015), Exercise 5.2(a): `Δ > 0` for `κ ≠ 0`, `ϑ ≥ 0`. -/
theorem delta2_pos {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) : 0 < delta2 β κ ϑ ρ := by
  unfold delta2; positivity

/-- Galí (2015), Exercise 5.2(a): `(ψ_x*, ψ_π*)` satisfies the constraint. -/
theorem psi_feasible {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    psiP β κ ϑ ρ * (1 - β * ρ) = κ * psiX β κ ϑ ρ + 1 := by
  have := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  unfold psiP psiX
  field_simp
  unfold delta2
  ring

/-- **Exercise 5.2(a), the key identity** (Galí 2015, p. 160): on the constraint line,
`ψ_π² + ϑψ_x² = ϑ/Δ + (ψ_π − ψ_π*)² + ϑ(ψ_x − ψ_x*)²`. -/
theorem objective_eq {β κ ϑ ρ ψx ψp : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ)
    (h : ψp * (1 - β * ρ) = κ * ψx + 1) :
    objective ϑ ψx ψp = ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 := by
  have hΔ := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  have key : objective ϑ ψx ψp - (ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2) =
      2 * ϑ / delta2 β κ ϑ ρ * (ψp * (1 - β * ρ) - κ * ψx - 1) := by
    unfold objective psiP psiX
    field_simp
    unfold delta2
    ring
  rw [show ψp * (1 - β * ρ) - κ * ψx - 1 = 0 by linarith, mul_zero, sub_eq_zero] at key
  exact key

/-- Galí (2015), Exercise 5.2(a): the minimal objective is `ϑ/Δ`. -/
theorem objective_opt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) = ϑ / delta2 β κ ϑ ρ := by
  rw [objective_eq hκ hϑ (psi_feasible hκ hϑ)]
  ring

/-- **Exercise 5.2(a), the optimal Markov policy** (Galí 2015, p. 160): with `κ ≠ 0`,
`ϑ > 0` and a shock that is not identically zero, `ψ_x* = −κ/Δ`, `ψ_π* = ϑ(1 − βρ_u)/Δ` is
feasible, and every feasible Markov policy has a loss at least as large, strictly larger
unless it is `(ψ_x*, ψ_π*)` (when `W > 0`, e.g. `shockWeight_pos`). -/
theorem ex5_2a {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hne : ∃ t ω, u t ω ≠ 0) (ω : Ω) (hW : 0 < shockWeight 𝔼 β u ω) :
    NKPC 𝔼 β κ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) u ∧
      loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω =
        ϑ / delta2 β κ ϑ ρ * shockWeight 𝔼 β u ω ∧
      ∀ ψx ψp, NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u →
        loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
          loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω ∧
        (loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω =
          loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω →
            ψx = psiX β κ ϑ ρ ∧ ψp = psiP β κ ϑ ρ) := by
  refine ⟨markov_feasible 𝔼 hu (psi_feasible hκ hϑ.le), ?_, fun ψx ψp hf => ?_⟩
  · rw [loss_markov, ← objective_opt (β := β) (ρ := ρ) hκ hϑ.le]
    rfl
  have hc := (markov_feasible_iff 𝔼 hu hne).mp hf
  have he := objective_eq (β := β) (ρ := ρ) hκ hϑ.le hc
  rw [loss_markov, loss_markov]
  change objective ϑ _ _ * _ ≤ objective ϑ _ _ * _ ∧ (objective ϑ _ _ * _ = objective ϑ _ _ * _ → _)
  rw [objective_opt hκ hϑ.le, he]
  have hle : ϑ / delta2 β κ ϑ ρ ≤ ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 := by
    nlinarith [sq_nonneg (ψp - psiP β κ ϑ ρ), sq_nonneg (ψx - psiX β κ ϑ ρ)]
  refine ⟨mul_le_mul_of_nonneg_right hle hW.le, fun h => ?_⟩
  have h2 : (ψp - psiP β κ ϑ ρ) ^ 2 + ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 = 0 := by
    have := mul_right_cancel₀ hW.ne' h
    linarith
  have hq1 := sq_nonneg (ψp - psiP β κ ϑ ρ)
  have hq2 := mul_nonneg hϑ.le (sq_nonneg (ψx - psiX β κ ϑ ρ))
  have h3 : (ψp - psiP β κ ϑ ρ) ^ 2 = 0 := by linarith
  have h4 : ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 = 0 := by linarith
  rw [mul_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact absurd h4 hϑ.ne'
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)⟩

/-! ### (b) Comparison with discretion -/

/-- Galí (2015), eqs. (5)–(6), p. 130: `Δ_d = κ² + ϑ(1 − βρ_u)`. -/
def deltaD (β κ ϑ ρ : ℝ) : ℝ := κ ^ 2 + ϑ * (1 - β * ρ)

/-- Galí (2015), eq. (5), p. 130: discretionary inflation `π_t = ϑ u_t/Δ_d`. -/
noncomputable def discP (β κ ϑ ρ : ℝ) : ℝ := ϑ / deltaD β κ ϑ ρ

/-- Galí (2015), eq. (6), p. 130: the discretionary output gap `x_t = −κ u_t/Δ_d`. -/
noncomputable def discX (β κ ϑ ρ : ℝ) : ℝ := -κ / deltaD β κ ϑ ρ

/-- Galí (2015), Exercise 5.2: `βρ_u < 1` for `0 < β < 1`, `|ρ_u| < 1`. -/
theorem beta_rho_lt_one {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) : β * ρ < 1 := by
  have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0.le
  have h2 : β * |ρ| < β * 1 := mul_lt_mul_of_pos_left hρ hβ0
  linarith

/-- Galí (2015), eqs. (5)–(6): `Δ_d > 0`. -/
theorem deltaD_pos {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) (hβρ : β * ρ < 1) :
    0 < deltaD β κ ϑ ρ := by
  unfold deltaD
  have : 0 < 1 - β * ρ := by linarith
  positivity

/-- Galí (2015), eq. (4), p. 130: the discretionary coefficients satisfy the targeting rule
`x_t = −(κ/ϑ) π_t`. -/
theorem disc_targeting {β κ ϑ ρ : ℝ} (hϑ : ϑ ≠ 0) :
    discX β κ ϑ ρ = -(κ / ϑ) * discP β κ ϑ ρ := by
  unfold discX discP
  by_cases h : deltaD β κ ϑ ρ = 0
  · simp [h]
  · field_simp

/-- Galí (2015), Exercise 5.2(b): discretion is a feasible Markov policy. -/
theorem disc_feasible {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) (hβρ : β * ρ < 1) :
    discP β κ ϑ ρ * (1 - β * ρ) = κ * discX β κ ϑ ρ + 1 := by
  have := (deltaD_pos hκ hϑ hβρ).ne'
  unfold discP discX
  field_simp
  unfold deltaD
  ring

/-- **Galí (2015), eqs. (4)–(6), p. 130 (discretion)**: if the output gap follows the targeting
rule `x_t = −(κ/ϑ) π_t` and the Phillips curve holds, the unique bounded inflation process is
`π_t = ϑ u_t/Δ_d`, and `x_t = −κ u_t/Δ_d`. -/
theorem discretion_unique {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hn : NKPC 𝔼 β κ x p u) (ht : ∀ t, x t = -(κ / ϑ) • p t) (hpb : BoundedProc p) :
    p = markov (discP β κ ϑ ρ) u ∧ x = markov (discX β κ ϑ ρ) u := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD := deltaD_pos hκ hϑ.le hβρ
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  set b := ϑ / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [sq_nonneg κ, pow_pos (abs_pos.mpr hκ) 2]
  have h1 : ∀ t, p t = a • 𝔼.E t (p (t + 1)) + b • u t := by
    intro t
    funext ω
    have e1 := congrFun (hn t) ω
    have e2 := congrFun (ht t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e2] at e1
    simp only [a, b]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - p t ω * κ ^ 2 * hinv
  have h2 : ∀ t, markov (discP β κ ϑ ρ) u t =
      a • 𝔼.E t (markov (discP β κ ϑ ρ) u (t + 1)) + b • u t := by
    intro t
    funext ω
    simp only [markov, map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b,
      discP]
    unfold deltaD at hD ⊢
    field_simp
    ring
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc (markov (discP β κ ϑ ρ) u) :=
    ⟨|discP β κ ϑ ρ| * M, fun t ω => by
      simp only [markov, Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hp := 𝔼.forward_unique ha h1 h2 hpb hcb
  refine ⟨hp, ?_⟩
  funext t
  rw [ht t, hp]
  simp only [markov, smul_smul, disc_targeting (β := β) (ρ := ρ) hϑ.ne']

/-- **Exercise 5.2(b)** (Galí 2015, p. 160): the optimal Markov policy is weakly better than
discretion; it is **strictly** better iff `ρ_u ≠ 0`; for `ρ_u = 0` the two coincide. -/
theorem ex5_2b_objective {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) :
    objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) ≤ objective ϑ (discX β κ ϑ ρ) (discP β κ ϑ ρ) ∧
      (objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) <
          objective ϑ (discX β κ ϑ ρ) (discP β κ ϑ ρ) ↔ ρ ≠ 0) ∧
      (ρ = 0 → psiX β κ ϑ ρ = discX β κ ϑ ρ ∧ psiP β κ ϑ ρ = discP β κ ϑ ρ) := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD := deltaD_pos hκ hϑ.le hβρ
  have hΔ := delta2_pos (β := β) (ρ := ρ) hκ hϑ.le
  have he := objective_eq (β := β) (ρ := ρ) hκ hϑ.le (disc_feasible hκ hϑ.le hβρ)
  rw [objective_opt hκ hϑ.le, he]
  have hzero : ρ = 0 → psiX β κ ϑ ρ = discX β κ ϑ ρ ∧ psiP β κ ϑ ρ = discP β κ ϑ ρ := by
    rintro rfl
    constructor <;> simp [psiX, psiP, discX, discP, delta2, deltaD]
  refine ⟨by nlinarith [sq_nonneg (discP β κ ϑ ρ - psiP β κ ϑ ρ),
    sq_nonneg (discX β κ ϑ ρ - psiX β κ ϑ ρ)], ⟨fun h hρ0 => ?_, fun hρ0 => ?_⟩, hzero⟩
  · obtain ⟨h1, h2⟩ := hzero hρ0
    rw [h1, h2, sub_self, sub_self] at h
    simp at h
  · have hne : discX β κ ϑ ρ ≠ psiX β κ ϑ ρ := by
      intro h
      unfold discX psiX at h
      rw [div_eq_div_iff hD.ne' hΔ.ne'] at h
      have h' : κ * (deltaD β κ ϑ ρ - delta2 β κ ϑ ρ) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h' | h'
      · exact hκ h'
      · unfold deltaD delta2 at h'
        have h'' : ϑ * (1 - β * ρ) * (β * ρ) = 0 := by linarith
        rcases mul_eq_zero.mp h'' with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hϑ.ne' h4
          · linarith
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hβ0.ne' h4
          · exact hρ0 h4
    have : 0 < ϑ * (discX β κ ϑ ρ - psiX β κ ϑ ρ) ^ 2 :=
      mul_pos hϑ (sq_pos_iff.mpr (sub_ne_zero.mpr hne))
    nlinarith [sq_nonneg (discP β κ ϑ ρ - psiP β κ ϑ ρ)]

/-- **Exercise 5.2(b), in terms of the loss** (Galí 2015, p. 160): the optimal Markov policy
has a loss no larger than discretion's, and strictly smaller iff `ρ_u ≠ 0` (when `W > 0`). -/
theorem ex5_2b {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) (u : ℕ → Ω → ℝ) (ω : Ω) (hW : 0 < shockWeight 𝔼 β u ω) :
    loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
        loss 𝔼 β ϑ (markov (discX β κ ϑ ρ) u) (markov (discP β κ ϑ ρ) u) ω ∧
      (loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω <
          loss 𝔼 β ϑ (markov (discX β κ ϑ ρ) u) (markov (discP β κ ϑ ρ) u) ω ↔ ρ ≠ 0) := by
  obtain ⟨h1, h2, -⟩ := ex5_2b_objective hβ0 hβ1 hκ hϑ hρ
  rw [loss_markov, loss_markov]
  change objective ϑ _ _ * _ ≤ objective ϑ _ _ * _ ∧ (objective ϑ _ _ * _ < objective ϑ _ _ * _ ↔ _)
  refine ⟨mul_le_mul_of_nonneg_right h1 hW.le, ?_⟩
  rw [mul_lt_mul_iff_left₀ hW]
  exact h2

/-! ### (c) Comparison with commitment -/

/-- Galí (2015), §5.2.2 and Exercise 5.2(c): a path is feasible under commitment if it is
bounded, adapted and satisfies the Phillips curve at every date. -/
def CommitFeasible (β κ : ℝ) (u x p : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted x ∧ 𝔼.Adapted p ∧ BoundedProc x ∧ BoundedProc p ∧ NKPC 𝔼 β κ x p u

/-- Galí (2015), Exercise 5.2(c): two bounded paths that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {x p x' p' : ℕ → Ω → ℝ} (hx : BoundedProc x) (hp : BoundedProc p) (hx' : BoundedProc x')
    (hp' : BoundedProc p') (k : ℕ)
    (heq : ∀ t, x' (t + k) = x (t + k) ∧ p' (t + k) = p (t + k)) (ω : Ω) :
    loss 𝔼 β ϑ x' p' ω = loss 𝔼 β ϑ x p ω +
      ∑ t ∈ Finset.range k, (lossTerm 𝔼 β ϑ x' p' ω t - lossTerm 𝔼 β ϑ x p ω t) := by
  unfold loss
  rw [← (loss_summable 𝔼 hβ0 hβ1 hϑ hx' hp' ω).sum_add_tsum_nat_add k,
    ← (loss_summable 𝔼 hβ0 hβ1 hϑ hx hp ω).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm 𝔼 β ϑ x' p' ω (t + k) = ∑' t, lossTerm 𝔼 β ϑ x p ω (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2]
  rw [this]
  ring

omit 𝔼 in
/-- Galí (2015), Exercise 5.2: a Markov policy driven by a bounded shock is bounded. -/
theorem markov_bounded {u : ℕ → Ω → ℝ} (hub : BoundedProc u) (ψ : ℝ) :
    BoundedProc (markov ψ u) := by
  obtain ⟨M, hM⟩ := hub
  exact ⟨|ψ| * M, fun t ω => by
    simp only [markov, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩

/-- Galí (2015), Exercise 5.2: a Markov policy driven by an adapted shock is adapted. -/
theorem markov_adapted {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (ψ : ℝ) :
    𝔼.Adapted (markov ψ u) := fun t => by simp only [markov, map_smul, hu t]

omit 𝔼 in
/-- Galí (2015), Exercise 5.2(c): a bounded process plus a bounded multiple of `u_0` is
bounded. -/
theorem bounded_add_smul {u y : ℕ → Ω → ℝ} (hub : BoundedProc u) (hy : BoundedProc y)
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ t, |g t| ≤ C) : BoundedProc fun t => y t + g t • u 0 := by
  obtain ⟨M, hM⟩ := hub
  obtain ⟨N, hN⟩ := hy
  refine ⟨N + C * M, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  refine (abs_add_le _ _).trans (add_le_add (hN t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul (hg t) (hM 0 ω) (abs_nonneg _) ((abs_nonneg _).trans (hg t))

/-- Galí (2015), Exercise 5.2(c): `u_0` is known at every date, `E_t u_0 = u_0`. -/
theorem E_u0 {ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) : 𝔼.E t (u 0) = u 0 := by
  rw [← hu.1 0, 𝔼.known (Nat.zero_le t)]

/-- Galí (2015), Exercise 5.2(c): adding a multiple of `u_0` keeps a process adapted. -/
theorem adapted_add_smul {ρ : ℝ} {u y : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hy : 𝔼.Adapted y)
    (g : ℕ → ℝ) : 𝔼.Adapted fun t => y t + g t • u 0 := fun t => by
  simp only [map_add, map_smul, hy t, E_u0 𝔼 hu t]

/-- Galí (2015), Exercise 5.2(c): `E_0[k u_t²] = k E_0[u_t²]` in the form used below. -/
theorem E0_sq_smul {f : Ω → ℝ} {k : ℝ} {g : Ω → ℝ} (hg : g = k • fun ω' => f ω' ^ 2)
    (ω : Ω) : 𝔼.E 0 g ω = k * 𝔼.E 0 (fun ω' => f ω' ^ 2) ω := by
  rw [hg, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **Exercise 5.2(c), the date-0 improvement** (Galí 2015, p. 160): if a feasible Markov
policy has `κψ_π + ϑψ_x ≠ 0`, perturbing it at date 0 alone, by
`(Δx_0, Δπ_0) = (ε u_0, κ ε u_0)` with `ε = −(κψ_π + ϑψ_x)/(κ² + ϑ)`, gives a feasible
commitment path whose loss is lower by `(κψ_π + ϑψ_x)²/(κ² + ϑ) · E_0[u_0²]`. -/
theorem improve_date0 {β κ ϑ ρ ψx ψp : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hcon : ψp * (1 - β * ρ) = κ * ψx + 1) (hc : κ * ψp + ϑ * ψx ≠ 0) {ω : Ω}
    (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω := by
  set c := κ * ψp + ϑ * ψx with hc_def
  have hK : 0 < κ ^ 2 + ϑ := by positivity
  set ε := -c / (κ ^ 2 + ϑ) with hε
  set gx : ℕ → ℝ := fun t => if t = 0 then ε else 0 with hgx
  set gp : ℕ → ℝ := fun t => if t = 0 then κ * ε else 0 with hgp
  set x : ℕ → Ω → ℝ := fun t => markov ψx u t + gx t • u 0 with hx
  set p : ℕ → Ω → ℝ := fun t => markov ψp u t + gp t • u 0 with hp
  have hm := markov_feasible 𝔼 hu hcon
  have hbx : BoundedProc x := bounded_add_smul hub (markov_bounded hub ψx) (C := |ε|)
    (fun t => by simp only [hgx]; split_ifs <;> simp)
  have hbp : BoundedProc p := bounded_add_smul hub (markov_bounded hub ψp) (C := |κ * ε|)
    (fun t => by
      simp only [hgp]
      split_ifs
      · exact le_rfl
      · simp only [abs_zero]; positivity)
  have hfeas : CommitFeasible 𝔼 β κ u x p := by
    refine ⟨adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψx) gx,
      adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψp) gp, hbx, hbp, fun t => ?_⟩
    have e := hm t
    funext ω'
    have e' := congrFun e ω'
    simp only [hx, hp, hgx, hgp, map_add, map_smul, E_u0 𝔼 hu, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e' ⊢
    rcases t with _ | n
    · simp only [↓reduceIte, Nat.add_one_ne_zero, zero_mul, add_zero] at e' ⊢
      linear_combination e'
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_mul, add_zero] at e' ⊢
      linear_combination e'
  refine ⟨x, p, hfeas, ?_⟩
  rw [loss_eq_of_eq_after 𝔼 hβ0 hβ1 hϑ.le (markov_bounded hub ψx) (markov_bounded hub ψp)
    hbx hbp 1 (fun t => by simp [hx, hp, hgx, hgp]) ω, Finset.sum_range_one]
  have e1 : lossTerm 𝔼 β ϑ x p ω 0 =
      ((ψp + κ * ε) ^ 2 + ϑ * (ψx + ε) ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, pow_zero, one_mul]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 0 =
      (ψp ^ 2 + ϑ * ψx ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, pow_zero, one_mul]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [markov, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e2, ← sub_mul]
  have hcoef : (ψp + κ * ε) ^ 2 + ϑ * (ψx + ε) ^ 2 - (ψp ^ 2 + ϑ * ψx ^ 2) =
      -(c ^ 2 / (κ ^ 2 + ϑ)) := by
    rw [hε, hc_def]
    field_simp
    ring
  rw [hcoef]
  have : 0 < c ^ 2 / (κ ^ 2 + ϑ) := div_pos (sq_pos_iff.mpr hc) hK
  nlinarith

/-- **Exercise 5.2(c), the date-1 improvement** (Galí 2015, p. 160): if a feasible Markov
policy has `κψ_π + ϑψ_x = 0` but `ψ_π ≠ 0` (the case `ρ_u = 0`), the perturbation
`Δx_1 = ε u_0`, `Δπ_1 = κ ε u_0`, `Δπ_0 = βκ ε u_0` (a promise about date-1 policy that lowers
inflation expectations at date 0), with `ε = −κψ_π/(βκ² + κ² + ϑ)`, is feasible and lowers the
loss by `β κ² ψ_π²/(βκ² + κ² + ϑ) · E_0[u_0²]`. -/
theorem improve_date1 {β κ ϑ ρ ψx ψp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hcon : ψp * (1 - β * ρ) = κ * ψx + 1) (hc : κ * ψp + ϑ * ψx = 0) (hψ : ψp ≠ 0)
    {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω := by
  have hK : 0 < β * κ ^ 2 + κ ^ 2 + ϑ := by positivity
  set ε := -(ψp * κ) / (β * κ ^ 2 + κ ^ 2 + ϑ) with hε
  set gx : ℕ → ℝ := fun t => if t = 1 then ε else 0 with hgx
  set gp : ℕ → ℝ := fun t => if t = 0 then β * κ * ε else if t = 1 then κ * ε else 0 with hgp
  set x : ℕ → Ω → ℝ := fun t => markov ψx u t + gx t • u 0 with hx
  set p : ℕ → Ω → ℝ := fun t => markov ψp u t + gp t • u 0 with hp
  have hm := markov_feasible 𝔼 hu hcon
  have hbx : BoundedProc x := bounded_add_smul hub (markov_bounded hub ψx) (C := |ε|)
    (fun t => by simp only [hgx]; split_ifs <;> simp)
  have hbp : BoundedProc p := bounded_add_smul hub (markov_bounded hub ψp)
    (C := |β * κ * ε| + |κ * ε|)
    (fun t => by
      simp only [hgp]
      split_ifs
      · linarith [abs_nonneg (κ * ε)]
      · linarith [abs_nonneg (β * κ * ε)]
      · simp only [abs_zero]; positivity)
  have hfeas : CommitFeasible 𝔼 β κ u x p := by
    refine ⟨adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψx) gx,
      adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψp) gp, hbx, hbp, fun t => ?_⟩
    have e := hm t
    funext ω'
    have e' := congrFun e ω'
    simp only [hx, hp, hgx, hgp, map_add, map_smul, E_u0 𝔼 hu, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e' ⊢
    rcases t with _ | _ | n
    · simp at e' ⊢
      linear_combination e'
    · simp at e' ⊢
      linear_combination e'
    · simp at e' ⊢
      linear_combination e'
  refine ⟨x, p, hfeas, ?_⟩
  rw [loss_eq_of_eq_after 𝔼 hβ0.le hβ1 hϑ.le (markov_bounded hub ψx) (markov_bounded hub ψp)
    hbx hbp 2 (fun t => by simp [hx, hp, hgx, hgp]) ω, Finset.sum_range_succ,
    Finset.sum_range_one]
  have e1 : lossTerm 𝔼 β ϑ x p ω 0 - lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 0 =
      (2 * ψp * β * κ * ε + β ^ 2 * κ ^ 2 * ε ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, lossTerm, pow_zero, one_mul, one_mul, ← Pi.sub_apply, ← map_sub]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp
    ring
  have e2 : lossTerm 𝔼 β ϑ x p ω 1 - lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 1 =
      β * (ε ^ 2 * (κ ^ 2 + ϑ)) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, lossTerm, pow_one, ← mul_sub, ← Pi.sub_apply, ← map_sub, mul_assoc]
    congr 1
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp
    linear_combination (2 * ε * u 0 ω' * u 1 ω') * hc
  rw [e1, e2, ← add_mul]
  have hcoef : 2 * ψp * β * κ * ε + β ^ 2 * κ ^ 2 * ε ^ 2 + β * (ε ^ 2 * (κ ^ 2 + ϑ)) =
      -(β * κ ^ 2 * ψp ^ 2 / (β * κ ^ 2 + κ ^ 2 + ϑ)) := by
    rw [hε]
    field_simp
    ring
  rw [hcoef]
  have : 0 < β * κ ^ 2 * ψp ^ 2 / (β * κ ^ 2 + κ ^ 2 + ϑ) :=
    div_pos (by have := sq_pos_iff.mpr hψ; have := sq_pos_iff.mpr hκ; positivity) hK
  nlinarith

/-- Galí (2015), Exercise 5.2(c): for the optimal Markov policy,
`κψ_π* + ϑψ_x* = −κϑβρ_u/Δ`. -/
theorem coef_opt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    κ * psiP β κ ϑ ρ + ϑ * psiX β κ ϑ ρ = -(κ * ϑ * β * ρ) / delta2 β κ ϑ ρ := by
  have := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  unfold psiP psiX
  field_simp
  ring

/-- **Exercise 5.2(c)** (Galí 2015, p. 160): for every `|ρ_u| < 1` there is a path feasible
under commitment (bounded, adapted, satisfying the Phillips curve) with a strictly lower loss
than the optimal Markov policy (when `E_0[u_0²] > 0`). -/
theorem ex5_2c {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) {ω : Ω}
    (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω := by
  have hcon := psi_feasible (β := β) (ρ := ρ) hκ hϑ.le
  have hΔ := delta2_pos (β := β) (ρ := ρ) hκ hϑ.le
  by_cases hρ0 : ρ = 0
  · subst hρ0
    refine improve_date1 𝔼 hβ0 hβ1 hκ hϑ hu hub hcon ?_ ?_ h0
    · rw [coef_opt hκ hϑ.le]; simp
    · unfold psiP
      simp only [mul_zero, sub_zero, mul_one]
      exact div_ne_zero hϑ.ne' hΔ.ne'
  · refine improve_date0 𝔼 hβ0.le hβ1 hϑ hu hub hcon ?_ h0
    rw [coef_opt hκ hϑ.le]
    refine div_ne_zero ?_ hΔ.ne'
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκ hϑ.ne') hβ0.ne') hρ0

/-- **Exercise 5.2(c), commitment versus the optimal Markov policy** (Galí 2015, p. 160): the
optimal Markov policy is feasible under commitment but not optimal there; any optimal policy
under commitment has a strictly lower loss (in particular a weakly lower one). -/
theorem ex5_2c_commitment {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    CommitFeasible 𝔼 β κ u (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ∧
      (¬ ∀ x p, CommitFeasible 𝔼 β κ u x p →
        loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
          loss 𝔼 β ϑ x p ω) ∧
      ∀ xc pc, CommitFeasible 𝔼 β κ u xc pc →
        (∀ x p, CommitFeasible 𝔼 β κ u x p → loss 𝔼 β ϑ xc pc ω ≤ loss 𝔼 β ϑ x p ω) →
          loss 𝔼 β ϑ xc pc ω <
            loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω := by
  obtain ⟨x, p, hf, hlt⟩ := ex5_2c 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub h0
  refine ⟨⟨markov_adapted 𝔼 hu.1 _, markov_adapted 𝔼 hu.1 _, markov_bounded hub _,
    markov_bounded hub _, markov_feasible 𝔼 hu (psi_feasible hκ hϑ.le)⟩,
    fun h => absurd (h x p hf) (not_le.mpr hlt), fun xc pc _ hopt => ?_⟩
  exact (hopt x p hf).trans_lt hlt

end Gali.DiscretionCommitment.Ex5_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.3: optimal policy with transaction frictions

Galí (2015), Chapter 5, Exercise 5.3, pp. 160–161 (based on Woodford 2003b). The planner
minimises `∑ βᵗ (π_t² + ϑ y_t² + α_i i_t²)` (the welfare loss up to the factor `1/2`) subject
to `π_t = β π_{t+1} + κ y_t` and `y_t = −σ⁻¹(i_t − π_{t+1} − r^n_t) + y_{t+1}` for `t ≥ 0`.
Following the chapter (§5.2.2 and the survey's advice), the problem is studied in its
deterministic (perfect-foresight) form for an arbitrary bounded natural-rate path `r^n`, over
bounded paths (Galí's convention).

## (a) The optimality conditions
With multipliers `ξ_1` (Phillips curve) and `ξ_2` (IS curve), `ξ_{1,−1} = ξ_{2,−1} = 0`:
`π_t + ξ_{1,t} − ξ_{1,t−1} − ξ_{2,t−1}/(σβ) = 0`, `ϑ y_t − κ ξ_{1,t} + ξ_{2,t} − ξ_{2,t−1}/β = 0`,
`α_i i_t + ξ_{2,t}/σ = 0` (`FOC`).
* `partial_sum_identity`: summation by parts against any homogeneous feasible direction.
* `ex5_3a_sufficient`: a bounded feasible plan satisfying the FOCs is optimal among bounded
  feasible plans, and it is the unique optimum.
* `ex5_3a_necessary`: every optimal bounded feasible plan satisfies the FOCs (with
  `ξ_2 = −σ α_i i`, `ξ_1 = (ϑ y + ξ_2 − ξ_{2,−1}/β)/κ`); the proof uses the feasible
  finitely supported directions `direction` (`dπ = 𝟙_s`).
* `ex5_3a_optimal_iff`: optimal ⟺ FOCs.

## (b) The implementing rule
`ex5_3b_rule_iff`: the FOCs hold for some multipliers iff the plan satisfies
`i_t = (1 + κ/(σβ)) i_{t−1} + β⁻¹ Δi_{t−1} + (κ/(α_i σ)) π_t + (ϑ/(α_i σ)) Δy_t`
at every `t ≥ 0` (with `i_{−1} = i_{−2} = y_{−1} = 0`), a rule that does not involve `r^n`.
`ex5_3b`: a bounded feasible plan is optimal iff it satisfies the rule. Determinacy of the
rule (that, with the constraints, it has a unique bounded solution) is not claimed in the
exercise and is not proved here. The stochastic version (state-contingent plans) is not
formalised; `y` stands for the welfare-relevant gap `ỹ`.
-/

namespace Gali.DiscretionCommitment.Ex5_3

open Filter Topology

/-! ### The problem -/

/-- Galí (2015), §5.2.2, p. 134: the lag with zero initial condition, `x_{−1} = 0`. -/
def lag (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => x t

/-- Galí (2015), Exercise 5.3, p. 161: feasibility, `π_t = β π_{t+1} + κ y_t` and
`y_t = −σ⁻¹(i_t − π_{t+1} − r^n_t) + y_{t+1}` for all `t ≥ 0`. -/
def Feasible (β κ σ : ℝ) (rn p y i : ℕ → ℝ) : Prop :=
  ∀ t, p t = β * p (t + 1) + κ * y t ∧ y t = -(1 / σ) * (i t - p (t + 1) - rn t) + y (t + 1)

/-- Galí (2015), Exercise 5.3: the homogeneous constraints satisfied by the difference of two
feasible plans. -/
def HomFeasible (β κ σ : ℝ) (dp dy di : ℕ → ℝ) : Prop :=
  ∀ t, dp t = β * dp (t + 1) + κ * dy t ∧ dy t = -(1 / σ) * (di t - dp (t + 1)) + dy (t + 1)

/-- Galí (2015), Exercise 5.3: a path is bounded. -/
def Bdd (x : ℕ → ℝ) : Prop := ∃ M, ∀ t, |x t| ≤ M

/-- Galí (2015), Exercise 5.3, p. 160: the date-`t` loss term `βᵗ (π_t² + ϑ y_t² + α_i i_t²)`. -/
def lossTerm (β ϑ αi : ℝ) (p y i : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (p t ^ 2 + ϑ * y t ^ 2 + αi * i t ^ 2)

/-- Galí (2015), Exercise 5.3, p. 160: the loss `∑ βᵗ (π_t² + ϑ y_t² + α_i i_t²)`. -/
noncomputable def loss (β ϑ αi : ℝ) (p y i : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ αi p y i t

/-- Galí (2015), Exercise 5.3(a): the plan is optimal among bounded feasible plans. -/
def Optimal (β κ σ ϑ αi : ℝ) (rn p y i : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn p y i ∧ Bdd p ∧ Bdd y ∧ Bdd i ∧
    ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
      loss β ϑ αi p y i ≤ loss β ϑ αi p' y' i'

/-- **Exercise 5.3(a), the optimality conditions** (Galí 2015, p. 161): the first-order
conditions of the Lagrangian with multipliers `ξ_1, ξ_2` and `ξ_{1,−1} = ξ_{2,−1} = 0`. -/
def FOC (β κ σ ϑ αi : ℝ) (p y i ξ1 ξ2 : ℕ → ℝ) : Prop :=
  ∀ t, p t + ξ1 t - lag ξ1 t - lag ξ2 t / (σ * β) = 0 ∧
    ϑ * y t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0 ∧ αi * i t + ξ2 t / σ = 0

/-- Galí (2015), Exercise 5.3: the residual of the inflation FOC. -/
noncomputable def resid (β σ : ℝ) (p ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : ℝ :=
  p t + ξ1 t - lag ξ1 t - lag ξ2 t / (σ * β)

/-- Galí (2015), Exercise 5.3: the cross term `βᵗ(π_t dπ_t + ϑ y_t dy_t + α_i i_t di_t)`. -/
def cross (β ϑ αi : ℝ) (p y i dp dy di : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (p t * dp t + ϑ * y t * dy t + αi * i t * di t)

/-- Galí (2015), Exercise 5.3(a) (**summation by parts**): if the `y`- and `i`-FOCs hold, then
for every homogeneous feasible direction `d`,
`∑_{t ≤ T} βᵗ(π dπ + ϑ y dy + α_i i di) = ∑_{t ≤ T} βᵗ R_t dπ_t
  − β^T (β ξ_{1,T} dπ_{T+1} + ξ_{2,T}(dπ_{T+1}/σ + dy_{T+1}))`, `R` the inflation residual. -/
theorem partial_sum_identity {β κ σ ϑ αi : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {p y i ξ1 ξ2 dp dy di : ℕ → ℝ}
    (hy : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β) (hi : ∀ t, αi * i t = -(ξ2 t / σ))
    (hd : HomFeasible β κ σ dp dy di) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t =
      ∑ t ∈ Finset.range (T + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dp t) -
        β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ + dy (T + 1))) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, cross, resid, pow_zero, one_mul]
    rw [hy 0, hi 0]
    obtain ⟨h1, h2⟩ := hd 0
    simp only [lag]
    linear_combination (norm := skip) (-ξ1 0) * h1 + (-ξ2 0) * h2
    field_simp
    ring
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => cross β ϑ αi p y i dp dy di t) (T + 1), ih,
      Finset.sum_range_succ (fun t => β ^ t * (resid β σ p ξ1 ξ2 t * dp t)) (T + 1)]
    generalize ∑ t ∈ Finset.range (T + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dp t) = S
    simp only [cross, resid]
    rw [hy (T + 1), hi (T + 1)]
    obtain ⟨h1, h2⟩ := hd (T + 1)
    simp only [lag]
    linear_combination (norm := skip) (-β ^ (T + 1) * ξ1 (T + 1)) * h1 +
      (-β ^ (T + 1) * ξ2 (T + 1)) * h2
    field_simp
    ring

/-! ### Bounded paths -/

/-- Galí (2015), Exercise 5.3: the lag of a bounded path is bounded. -/
theorem bdd_lag {x : ℕ → ℝ} (hx : Bdd x) : Bdd (lag x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, fun t => ?_⟩
  rcases t with _ | t
  · simpa [lag] using (abs_nonneg _).trans (hM 0)
  · exact hM t

/-- Galí (2015), Exercise 5.3: linear combinations of bounded paths are bounded. -/
theorem bdd_lin {x z : ℕ → ℝ} (hx : Bdd x) (hz : Bdd z) (a b : ℝ) :
    Bdd fun t => a * x t + b * z t := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hz
  refine ⟨|a| * M + |b| * N, fun t => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t) (abs_nonneg b)

/-- Galí (2015), Exercise 5.3: the lead of a bounded path is bounded. -/
theorem bdd_shift {x : ℕ → ℝ} (hx : Bdd x) : Bdd fun t => x (t + 1) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M, fun t => hM (t + 1)⟩

/-- Galí (2015), Exercise 5.3: the loss series of a bounded plan is summable
(`0 ≤ β < 1`, `ϑ, α_i ≥ 0`). -/
theorem loss_summable {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) (hα : 0 ≤ αi)
    {p y i : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) :
    Summable (lossTerm β ϑ αi p y i) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hy
  obtain ⟨C, hC⟩ := hi
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2 + αi * C ^ 2))
    (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have h1 : p t ^ 2 ≤ A ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
  have h2 : y t ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have h3 : i t ^ 2 ≤ C ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC t) 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hϑ, mul_le_mul_of_nonneg_left h3 hα]

/-- Galí (2015), Exercise 5.3: the cross series of bounded paths is summable. -/
theorem cross_summable {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p y i dp dy di : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) (hdp : Bdd dp)
    (hdy : Bdd dy) (hdi : Bdd di) : Summable (cross β ϑ αi p y i dp dy di) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hy
  obtain ⟨C, hC⟩ := hi
  obtain ⟨D, hD⟩ := hdp
  obtain ⟨E, hE⟩ := hdy
  obtain ⟨F, hF⟩ := hdi
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A * D + |ϑ| * B * E + |αi| * C * F))
    (fun t => ?_)
  rw [Real.norm_eq_abs, cross, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul (hA t) (hD t) (abs_nonneg _) hA0
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hB t) (hE t) (abs_nonneg _) hB0) (abs_nonneg _)
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hC t) (hF t) (abs_nonneg _) hC0) (abs_nonneg _)

/-- Galí (2015), Exercise 5.3: the difference of two feasible plans is a homogeneous feasible
direction. -/
theorem hom_of_feasible {β κ σ : ℝ} {rn p y i p' y' i' : ℕ → ℝ}
    (h : Feasible β κ σ rn p y i) (h' : Feasible β κ σ rn p' y' i') :
    HomFeasible β κ σ (fun t => p' t - p t) (fun t => y' t - y t) (fun t => i' t - i t) := by
  intro t
  obtain ⟨a1, a2⟩ := h t
  obtain ⟨b1, b2⟩ := h' t
  constructor
  · linear_combination b1 - a1
  · linear_combination b2 - a2

/-- Galí (2015), Exercise 5.3: a feasible plan plus a multiple of a homogeneous feasible
direction is feasible. -/
theorem feasible_add {β κ σ : ℝ} {rn p y i dp dy di : ℕ → ℝ} (h : Feasible β κ σ rn p y i)
    (hd : HomFeasible β κ σ dp dy di) (ε : ℝ) :
    Feasible β κ σ rn (fun t => p t + ε * dp t) (fun t => y t + ε * dy t)
      (fun t => i t + ε * di t) := by
  intro t
  obtain ⟨a1, a2⟩ := h t
  obtain ⟨b1, b2⟩ := hd t
  constructor
  · linear_combination a1 + ε * b1
  · linear_combination a2 + ε * b2

/-- Galí (2015), Exercise 5.3: the loss term of a perturbed plan,
`ℓ'_t = ℓ_t + 2 c_t + βᵗ(dπ² + ϑ dy² + α_i di²)`. -/
theorem lossTerm_add (β ϑ αi : ℝ) (p y i dp dy di : ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ αi (fun t => p t + dp t) (fun t => y t + dy t) (fun t => i t + di t) t =
      lossTerm β ϑ αi p y i t + 2 * cross β ϑ αi p y i dp dy di t +
        lossTerm β ϑ αi dp dy di t := by
  simp only [lossTerm, cross]
  ring

/-! ### (a) Sufficiency -/

/-- Galí (2015), Exercise 5.3(a): the multipliers of a bounded plan satisfying the `y`- and
`i`-FOCs are bounded. -/
theorem multipliers_bdd {β κ σ ϑ αi : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {p y i ξ1 ξ2 : ℕ → ℝ}
    (hfoc : FOC β κ σ ϑ αi p y i ξ1 ξ2) (hy : Bdd y) (hi : Bdd i) : Bdd ξ1 ∧ Bdd ξ2 := by
  have e2 : ξ2 = fun t => (-σ * αi) * i t + 0 * i t := by
    funext t
    have := (hfoc t).2.2
    field_simp at this
    linear_combination this
  have h2 : Bdd ξ2 := by rw [e2]; exact bdd_lin hi hi _ _
  have e1 : ξ1 = fun t => κ⁻¹ * (ϑ * y t + 1 * ξ2 t) + (-(κ⁻¹ / β)) * lag ξ2 t := by
    funext t
    have := (hfoc t).2.1
    field_simp
    linear_combination -this
  refine ⟨?_, h2⟩
  rw [e1]
  exact bdd_lin (bdd_lin hy h2 ϑ 1) (bdd_lag h2) _ _

/-- **Exercise 5.3(a), sufficiency** (Galí 2015, p. 161): a bounded feasible plan satisfying the
FOCs is optimal among bounded feasible plans, and it is the only optimal one. -/
theorem ex5_3a_sufficient {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i ξ1 ξ2 : ℕ → ℝ}
    (hf : Feasible β κ σ rn p y i) (hp : Bdd p) (hy : Bdd y) (hi : Bdd i)
    (hfoc : FOC β κ σ ϑ αi p y i ξ1 ξ2) :
    Optimal β κ σ ϑ αi rn p y i ∧
      ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
        loss β ϑ αi p' y' i' ≤ loss β ϑ αi p y i → p' = p ∧ y' = y ∧ i' = i := by
  obtain ⟨hξ1, hξ2⟩ := multipliers_bdd hκ hσ hfoc hy hi
  -- the key fact: for every alternative, loss' = loss + ∑ βᵗ (dπ² + ϑ dy² + α_i di²)
  have key : ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
      loss β ϑ αi p' y' i' = loss β ϑ αi p y i +
        loss β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t) (fun t => i' t - i t) := by
    intro p' y' i' hf' hp' hy' hi'
    set dp : ℕ → ℝ := fun t => p' t - p t
    set dy : ℕ → ℝ := fun t => y' t - y t
    set di : ℕ → ℝ := fun t => i' t - i t
    have hd : HomFeasible β κ σ dp dy di := hom_of_feasible hf hf'
    have hbdp : Bdd dp := by
      have := bdd_lin hp' hp 1 (-1); simpa [dp, sub_eq_add_neg] using this
    have hbdy : Bdd dy := by
      have := bdd_lin hy' hy 1 (-1); simpa [dy, sub_eq_add_neg] using this
    have hbdi : Bdd di := by
      have := bdd_lin hi' hi 1 (-1); simpa [di, sub_eq_add_neg] using this
    have hcs := cross_summable (ϑ := ϑ) (αi := αi) hβ0.le hβ1 hp hy hi hbdp hbdy hbdi
    -- partial sums of the cross series are minus the boundary term, which tends to zero
    have hyf : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β := fun t => by
      have := (hfoc t).2.1; linarith
    have hif : ∀ t, αi * i t = -(ξ2 t / σ) := fun t => by
      have := (hfoc t).2.2; linarith
    have hres : ∀ t, resid β σ p ξ1 ξ2 t = 0 := fun t => (hfoc t).1
    have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t =
        -(β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ + dy (T + 1)))) := by
      intro T
      rw [partial_sum_identity hβ0.ne' hσ hyf hif hd T]
      simp [hres]
    obtain ⟨A, hA⟩ := hξ1
    obtain ⟨B, hB⟩ := hξ2
    obtain ⟨D, hD⟩ := hbdp
    obtain ⟨E, hE⟩ := hbdy
    have hbound : ∀ T, ‖-(β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ +
        dy (T + 1))))‖ ≤ β ^ T * (β * A * D + B * (D / |σ| + E)) := by
      intro T
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le T)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_pos hβ0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hA T) hβ0.le) (hD (T + 1)) (abs_nonneg _)
          (by positivity)
      · rw [abs_mul]
        refine mul_le_mul (hB T) ((abs_add_le _ _).trans (add_le_add ?_ (hE (T + 1))))
          (abs_nonneg _) hB0
        rw [abs_div]
        exact div_le_div_of_nonneg_right (hD (T + 1)) (abs_nonneg _)
    have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t)
        atTop (𝓝 0) := by
      simp only [hpart]
      refine squeeze_zero_norm hbound ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
        (β * A * D + B * (D / |σ| + E))
    have htsum : ∑' t, cross β ϑ αi p y i dp dy di t = 0 :=
      tendsto_nhds_unique ((hcs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) hlim
    have hl := loss_summable hβ0.le hβ1 hϑ.le hα.le hp hy hi
    have hq := loss_summable hβ0.le hβ1 hϑ.le hα.le ⟨D, hD⟩ ⟨E, hE⟩ hbdi
    have hsplit : lossTerm β ϑ αi p' y' i' = fun t => lossTerm β ϑ αi p y i t +
        2 * cross β ϑ αi p y i dp dy di t + lossTerm β ϑ αi dp dy di t := by
      funext t
      have := lossTerm_add β ϑ αi p y i dp dy di t
      simpa [dp, dy, di] using this
    unfold loss
    rw [hsplit, (hl.add (hcs.mul_left 2)).tsum_add hq, hl.tsum_add (hcs.mul_left 2),
      tsum_mul_left, htsum, mul_zero, add_zero]
  have hqnn : ∀ dp dy di : ℕ → ℝ, ∀ t, 0 ≤ lossTerm β ϑ αi dp dy di t := fun dp dy di t => by
    unfold lossTerm; positivity
  refine ⟨⟨hf, hp, hy, hi, fun p' y' i' hf' hp' hy' hi' => ?_⟩,
    fun p' y' i' hf' hp' hy' hi' hle => ?_⟩
  · rw [key p' y' i' hf' hp' hy' hi']
    exact le_add_of_nonneg_right (tsum_nonneg (hqnn _ _ _))
  · rw [key p' y' i' hf' hp' hy' hi'] at hle
    have h0 : loss β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t)
        (fun t => i' t - i t) ≤ 0 := by linarith
    have hbd : ∀ (x x' : ℕ → ℝ), Bdd x → Bdd x' → Bdd fun t => x' t - x t := by
      intro x x' hx hx'
      have := bdd_lin hx' hx 1 (-1); simpa [sub_eq_add_neg] using this
    have hq := loss_summable hβ0.le hβ1 hϑ.le hα.le (hbd p p' hp hp') (hbd y y' hy hy')
      (hbd i i' hi hi')
    have hz : ∀ t, lossTerm β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t)
        (fun t => i' t - i t) t = 0 := fun t =>
      le_antisymm ((hq.le_tsum t (fun j _ => hqnn _ _ _ j)).trans h0) (hqnn _ _ _ t)
    have hall : ∀ t, p' t - p t = 0 ∧ y' t - y t = 0 ∧ i' t - i t = 0 := by
      intro t
      have h := hz t
      simp only [lossTerm] at h
      have hβt : 0 < β ^ t := pow_pos hβ0 t
      have hin : (p' t - p t) ^ 2 + ϑ * (y' t - y t) ^ 2 + αi * (i' t - i t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hβt.ne'
        · exact h
      have a1 := sq_nonneg (p' t - p t)
      have a2 := mul_nonneg hϑ.le (sq_nonneg (y' t - y t))
      have a3 := mul_nonneg hα.le (sq_nonneg (i' t - i t))
      refine ⟨pow_eq_zero_iff two_ne_zero |>.mp (by linarith), ?_, ?_⟩
      · have : (y' t - y t) ^ 2 = 0 := by
          rcases mul_eq_zero.mp (show ϑ * (y' t - y t) ^ 2 = 0 by linarith) with h | h
          · exact absurd h hϑ.ne'
          · exact h
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      · have : (i' t - i t) ^ 2 = 0 := by
          rcases mul_eq_zero.mp (show αi * (i' t - i t) ^ 2 = 0 by linarith) with h | h
          · exact absurd h hα.ne'
          · exact h
        exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨funext fun t => sub_eq_zero.mp (hall t).1, funext fun t => sub_eq_zero.mp (hall t).2.1,
      funext fun t => sub_eq_zero.mp (hall t).2.2⟩

/-! ### (a) Necessity -/

/-- Galí (2015), Exercise 5.3(a): the test direction `dπ = 𝟙_{t = s}`. -/
def dirP (s : ℕ) : ℕ → ℝ := fun t => if t = s then 1 else 0

/-- Galí (2015), Exercise 5.3(a): the output-gap part of the test direction,
`dy_t = (dπ_t − β dπ_{t+1})/κ`. -/
noncomputable def dirY (β κ : ℝ) (s : ℕ) : ℕ → ℝ :=
  fun t => (dirP s t - β * dirP s (t + 1)) / κ

/-- Galí (2015), Exercise 5.3(a): the interest-rate part of the test direction,
`di_t = dπ_{t+1} + σ(dy_{t+1} − dy_t)`. -/
noncomputable def dirI (β κ σ : ℝ) (s : ℕ) : ℕ → ℝ :=
  fun t => dirP s (t + 1) + σ * (dirY β κ s (t + 1) - dirY β κ s t)

/-- Galí (2015), Exercise 5.3(a): the test direction is homogeneous feasible. -/
theorem dir_hom {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (s : ℕ) :
    HomFeasible β κ σ (dirP s) (dirY β κ s) (dirI β κ σ s) := by
  intro t
  constructor
  · simp only [dirY]
    field_simp
    ring
  · simp only [dirI]
    field_simp
    ring

/-- Galí (2015), Exercise 5.3(a): the test direction is bounded. -/
theorem dir_bdd (β κ σ : ℝ) (s : ℕ) :
    Bdd (dirP s) ∧ Bdd (dirY β κ s) ∧ Bdd (dirI β κ σ s) := by
  have h0 : Bdd (dirP s) := ⟨1, fun t => by simp only [dirP]; split_ifs <;> simp⟩
  have h1 : Bdd (dirY β κ s) := by
    have := bdd_lin h0 (bdd_shift h0) κ⁻¹ (-β / κ)
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirY β κ s t = κ⁻¹ * dirP s t + -β / κ * dirP s (t + 1) := by
      simp only [dirY]; ring
    rw [e]; exact hM t
  have h2 : Bdd (dirI β κ σ s) := by
    have := bdd_lin (bdd_shift h0) (bdd_lin (bdd_shift h1) h1 σ (-σ)) 1 1
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirI β κ σ s t = 1 * dirP s (t + 1) +
        1 * (σ * dirY β κ s (t + 1) + -σ * dirY β κ s t) := by
      simp only [dirI]; ring
    rw [e]; exact hM t
  exact ⟨h0, h1, h2⟩

/-- Galí (2015), Exercise 5.3(a): the test direction vanishes after date `s`. -/
theorem dir_zero_after {β κ σ : ℝ} {s t : ℕ} (h : s < t) :
    dirP s t = 0 ∧ dirY β κ s t = 0 ∧ dirI β κ σ s t = 0 := by
  have hp : ∀ u, s < u → dirP s u = 0 := fun u hu => by
    simp only [dirP]
    split_ifs
    · omega
    · rfl
  have hy : ∀ u, s < u → dirY β κ s u = 0 := fun u hu => by
    simp only [dirY]; rw [hp u hu, hp (u + 1) (by omega)]; simp
  refine ⟨hp t h, hy t h, ?_⟩
  simp only [dirI]
  rw [hp (t + 1) (by omega), hy t h, hy (t + 1) (by omega)]
  simp

/-- Galí (2015), Exercise 5.3: two bounded plans that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    (hα : 0 ≤ αi) {p y i p' y' i' : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i)
    (hp' : Bdd p') (hy' : Bdd y') (hi' : Bdd i') (k : ℕ)
    (heq : ∀ t, p' (t + k) = p (t + k) ∧ y' (t + k) = y (t + k) ∧ i' (t + k) = i (t + k)) :
    loss β ϑ αi p' y' i' = loss β ϑ αi p y i +
      ∑ t ∈ Finset.range k, (lossTerm β ϑ αi p' y' i' t - lossTerm β ϑ αi p y i t) := by
  unfold loss
  rw [← (loss_summable hβ0 hβ1 hϑ hα hp' hy' hi').sum_add_tsum_nat_add k,
    ← (loss_summable hβ0 hβ1 hϑ hα hp hy hi).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm β ϑ αi p' y' i' (t + k) = ∑' t, lossTerm β ϑ αi p y i (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2.1, (heq t).2.2]
  rw [this]
  ring

/-- Galí (2015), Exercise 5.3(a): if `2εC + ε²Q ≥ 0` for every `ε` and `Q ≥ 0`, then `C = 0`. -/
theorem eq_zero_of_quadratic {C Q : ℝ} (hQ : 0 ≤ Q) (h : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q) :
    C = 0 := by
  have hQ1 : 0 < Q + 1 := by linarith
  have e : 2 * (-C / (Q + 1)) * C + (-C / (Q + 1)) ^ 2 * Q =
      -(C ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
    field_simp
    ring
  have h1 := h (-C / (Q + 1))
  rw [e] at h1
  have h2 : 0 ≤ -(C ^ 2 * (Q + 2)) := by
    have := mul_nonneg h1 (sq_nonneg (Q + 1))
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hQ1.ne')] at this
  have h3 : C ^ 2 = 0 := by nlinarith [sq_nonneg C]
  exact pow_eq_zero_iff two_ne_zero |>.mp h3

/-- Galí (2015), Exercise 5.3(a): the multiplier on the IS curve, `ξ_{2,t} = −σ α_i i_t`
(from the `i`-FOC). -/
def xi2 (σ αi : ℝ) (i : ℕ → ℝ) : ℕ → ℝ := fun t => -σ * αi * i t

/-- Galí (2015), Exercise 5.3(a): the multiplier on the Phillips curve,
`ξ_{1,t} = (ϑ y_t + ξ_{2,t} − ξ_{2,t−1}/β)/κ` (from the `y`-FOC). -/
noncomputable def xi1 (β κ ϑ : ℝ) (y ξ2 : ℕ → ℝ) : ℕ → ℝ :=
  fun t => (ϑ * y t + ξ2 t - lag ξ2 t / β) / κ

/-- **Exercise 5.3(a), necessity** (Galí 2015, p. 161): an optimal bounded feasible plan
satisfies the FOCs with `ξ_2 = −σ α_i i` and `ξ_1 = (ϑ y + ξ_2 − ξ_{2,−1}/β)/κ`. -/
theorem ex5_3a_necessary {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 ≤ ϑ) (hα : 0 ≤ αi) {rn p y i : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ αi rn p y i) :
    FOC β κ σ ϑ αi p y i (xi1 β κ ϑ y (xi2 σ αi i)) (xi2 σ αi i) := by
  obtain ⟨hf, hp, hy, hi, hmin⟩ := hopt
  set ξ2 := xi2 σ αi i
  set ξ1 := xi1 β κ ϑ y ξ2
  have hyf : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β := fun t => by
    simp only [ξ1, xi1]
    field_simp
    ring
  have hif : ∀ t, αi * i t = -(ξ2 t / σ) := fun t => by
    simp only [ξ2, xi2]
    field_simp
  intro s
  refine ⟨?_, by linarith [hyf s], by linarith [hif s]⟩
  -- test the plan against the direction concentrated at `s`
  obtain ⟨hdP, hdY, hdI⟩ := dir_bdd β κ σ s
  have hd := dir_hom (β := β) hκ hσ s
  set C := ∑ t ∈ Finset.range (s + 1),
    cross β ϑ αi p y i (dirP s) (dirY β κ s) (dirI β κ σ s) t
  set Q := ∑ t ∈ Finset.range (s + 1), lossTerm β ϑ αi (dirP s) (dirY β κ s) (dirI β κ σ s) t
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun t _ => by unfold lossTerm; positivity
  have hquad : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q := by
    intro ε
    have hb : ∀ x d : ℕ → ℝ, Bdd x → Bdd d → Bdd fun t => x t + ε * d t := fun x d hx hd' => by
      have := bdd_lin hx hd' 1 ε; simpa using this
    have hle := hmin _ _ _ (feasible_add hf hd ε) (hb _ _ hp hdP) (hb _ _ hy hdY)
      (hb _ _ hi hdI)
    rw [loss_eq_of_eq_after hβ0.le hβ1 hϑ hα hp hy hi (hb _ _ hp hdP) (hb _ _ hy hdY)
      (hb _ _ hi hdI) (s + 1) (fun t => by
        obtain ⟨h1, h2, h3⟩ := dir_zero_after (β := β) (κ := κ) (σ := σ) (s := s)
          (t := t + (s + 1)) (by omega)
        simp [h1, h2, h3])] at hle
    have hsum : ∑ t ∈ Finset.range (s + 1),
        (lossTerm β ϑ αi (fun t => p t + ε * dirP s t) (fun t => y t + ε * dirY β κ s t)
          (fun t => i t + ε * dirI β κ σ s t) t - lossTerm β ϑ αi p y i t) =
        2 * ε * C + ε ^ 2 * Q := by
      simp only [C, Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, cross]
      ring
    linarith
  have hC := eq_zero_of_quadratic hQ hquad
  have hid := partial_sum_identity (p := p) hβ0.ne' hσ hyf hif hd s
  obtain ⟨h1, h2, -⟩ := dir_zero_after (β := β) (κ := κ) (σ := σ) (s := s) (t := s + 1)
    (by omega)
  rw [h1, h2] at hid
  have hsingle : ∑ t ∈ Finset.range (s + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dirP s t) =
      β ^ s * resid β σ p ξ1 ξ2 s := by
    rw [Finset.sum_eq_single s (fun t _ hts => by simp [dirP, hts])
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self s)) h)]
    simp [dirP]
  rw [hsingle] at hid
  have : β ^ s * resid β σ p ξ1 ξ2 s = 0 := by
    have hC' : C = 0 := hC
    simp only [C] at hC'
    rw [hC'] at hid
    simp only [mul_zero, zero_div, add_zero, sub_zero] at hid
    linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (pow_ne_zero s hβ0.ne')
  · exact h

/-- **Exercise 5.3(a)** (Galí 2015, p. 161): a bounded feasible plan is optimal among bounded
feasible plans iff it satisfies the FOCs for some multipliers. -/
theorem ex5_3a_optimal_iff {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i : ℕ → ℝ}
    (hf : Feasible β κ σ rn p y i) (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) :
    Optimal β κ σ ϑ αi rn p y i ↔ ∃ ξ1 ξ2, FOC β κ σ ϑ αi p y i ξ1 ξ2 :=
  ⟨fun h => ⟨_, _, ex5_3a_necessary hβ0 hβ1 hκ hσ hϑ.le hα.le h⟩,
    fun ⟨_, _, h⟩ => (ex5_3a_sufficient hβ0 hβ1 hκ hσ hϑ hα hf hp hy hi h).1⟩

/-! ### (b) The implementing rule -/

/-- **Exercise 5.3(b), the rule** (Galí 2015, p. 161):
`i_t = (1 + κ/(σβ)) i_{t−1} + β⁻¹ Δi_{t−1} + (κ/(α_i σ)) π_t + (ϑ/(α_i σ)) Δy_t` with
`i_{−1} = i_{−2} = y_{−1} = 0`. -/
noncomputable def Rule (β κ σ ϑ αi : ℝ) (p y i : ℕ → ℝ) : Prop :=
  ∀ t, i t = (1 + κ / (σ * β)) * lag i t + (lag i t - lag (lag i) t) / β +
    κ / (αi * σ) * p t + ϑ / (αi * σ) * (y t - lag y t)

/-- Galí (2015), Exercise 5.3(b): lags commute with scaling. -/
theorem lag_mul {f g : ℕ → ℝ} {c : ℝ} (h : ∀ t, f t = c * g t) (t : ℕ) :
    lag f t = c * lag g t := by
  rcases t with _ | t
  · simp [lag]
  · exact h t

/-- Galí (2015), Exercise 5.3(b): the lagged `y`-FOC (with zero initial conditions). -/
theorem lag_yfoc {β κ ϑ : ℝ} {y ξ1 ξ2 : ℕ → ℝ}
    (h : ∀ t, ϑ * y t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0) (t : ℕ) :
    ϑ * lag y t - κ * lag ξ1 t + lag ξ2 t - lag (lag ξ2) t / β = 0 := by
  rcases t with _ | t
  · simp [lag]
  · exact h t

/-- **Exercise 5.3(b)** (Galí 2015, p. 161): the FOCs hold for some multipliers iff the plan
satisfies the interest-rate rule (which does not involve `r^n`). -/
theorem ex5_3b_rule_iff {β κ σ ϑ αi : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (hα : αi ≠ 0) {p y i : ℕ → ℝ} :
    (∃ ξ1 ξ2, FOC β κ σ ϑ αi p y i ξ1 ξ2) ↔ Rule β κ σ ϑ αi p y i := by
  constructor
  · rintro ⟨ξ1, ξ2, hfoc⟩ t
    have h4 : ∀ t, ξ2 t = (-σ * αi) * i t := fun t => by
      have := (hfoc t).2.2
      field_simp at this
      linear_combination this
    have E1 := (hfoc t).1
    have E2 := (hfoc t).2.1
    have E3 := lag_yfoc (fun t => (hfoc t).2.1) t
    rw [h4 t, lag_mul h4 t] at E2
    rw [lag_mul h4 t] at E1
    rw [lag_mul h4 t, lag_mul (lag_mul h4) t] at E3
    linear_combination (norm := skip) (-1 / (σ * αi)) * (κ * E1 + E2 - E3)
    field_simp
    ring
  · intro hr
    refine ⟨xi1 β κ ϑ y (xi2 σ αi i), xi2 σ αi i, fun t => ⟨?_, ?_, ?_⟩⟩
    · have h5 : ∀ t, xi2 σ αi i t = (-σ * αi) * i t := fun t => rfl
      have hl1 : lag (xi1 β κ ϑ y (xi2 σ αi i)) t =
          (ϑ * lag y t + lag (xi2 σ αi i) t - lag (lag (xi2 σ αi i)) t / β) / κ := by
        rcases t with _ | t
        · simp [lag]
        · rfl
      rw [hl1, lag_mul (lag_mul h5) t, lag_mul h5 t]
      simp only [xi1, xi2]
      rw [lag_mul h5 t]
      linear_combination (norm := skip) (-σ * αi / κ) * hr t
      field_simp
      ring
    · simp only [xi1]
      field_simp
      ring
    · simp only [xi2]
      field_simp
      ring

/-- **Exercise 5.3(b), implementation** (Galí 2015, p. 161): a bounded feasible plan is the
optimal plan iff it satisfies the interest-rate rule. -/
theorem ex5_3b {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i : ℕ → ℝ} (hf : Feasible β κ σ rn p y i) (hp : Bdd p)
    (hy : Bdd y) (hi : Bdd i) :
    Optimal β κ σ ϑ αi rn p y i ↔ Rule β κ σ ϑ αi p y i :=
  (ex5_3a_optimal_iff hβ0 hβ1 hκ hσ hϑ hα hf hp hy hi).trans
    (ex5_3b_rule_iff hβ0.ne' hκ hσ hα.ne')

end Gali.DiscretionCommitment.Ex5_3

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.4: inflation persistence and monetary policy

Galí (2015), Chapter 5, Exercise 5.4, p. 161 (based on Steinsson 2003). With partial
indexation `γ`, the loss is `½ E_0 ∑ βᵗ [ϑ x_t² + (π_t − γπ_{t−1})²]` and inflation follows
`π_t − γπ_{t−1} = κ x_t + β E_t (π_{t+1} − γπ_t) + u_t`. Write `π̃_t = π_t − γπ_{t−1}` (`tilde`,
with a given initial `π_{−1}`): the problem is the chapter's problem with `π̃` in place of `π`.

## (a) Discretion
* `period_loss_eq`, `period_opt_iff`, `period_targeting_iff`: given `v = β E_t π̃_{t+1} + u_t`
  (which, in an equilibrium where `π̃` depends only on current shocks, the current choice does
  not affect), `ϑ x² + (κ x + v)²` has the unique minimiser `x* = −κ v/(ϑ + κ²)`, which is
  characterised by the targeting rule `x = −(κ/ϑ) π̃`.
* `ex5_4a_period_optimal`: in the discretionary equilibrium each period's choice minimises the
  short-term loss.
* `ex5_4a_unique`: the unique equilibrium with bounded `π̃` and `x` is
  `π̃_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))`, `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))` (`ρ_u = 0` in the book:
  `π̃_t = ϑ u_t/(ϑ + κ²)`); `ex5_4a_exists` (constructed by `π_t = γπ_{t−1} + ψ u_t`,
  `discInfl`), `ex5_4a_inflation`: `π_t = γ π_{t−1} + ϑ u_t/(κ² + ϑ(1 − βρ_u))`.
* `period_foc_alt`: if instead `E_t π_{t+1}` were taken as given, the period FOC would be
  `ϑ (1 + βγ) x = −κ π̃` — a different, not Markov-perfect, condition (remark).

## (b) Commitment
Deterministic (perfect-foresight) problem over bounded `(x, π̃)`, as in §5.2.2:
minimise `∑ βᵗ (ϑ x_t² + π̃_t²)` subject to `π̃_t = κ x_t + β π̃_{t+1} + u_t`.
* `partial_sum_identity`, `ex5_4b_sufficient`, `ex5_4b_necessary`, `ex5_4b_optimal_iff`:
  optimal ⟺ the FOCs `ϑ x_t − κ ξ_t = 0`, `π̃_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`.
* `foc_iff_level_rule`: ⟺ `x_t = −(κ/ϑ) p̃_t` with `p̃_t = ∑_{s ≤ t} π̃_s` (the `p̃`-level
  rule), ⟺ `x_t − x_{t−1} = −(κ/ϑ) π̃_t`, `x_{−1} = 0` (`level_rule_iff_diff`).
* `cumsum_tilde_eq`: in terms of the log price level,
  `p̃_t = (p_t − p_{−1}) − γ (p_{t−1} − p_{−2})`; `ex5_4b`: the optimal plan is characterised by
  `x_t = −(κ/ϑ)[(p_t − p_{−1}) − γ(p_{t−1} − p_{−2})]`.

## (c) Discussion
Part (c) asks for a verbal discussion of how `γ` affects the responses; it is not formalised.
-/

namespace Gali.DiscretionCommitment.Ex5_4

open Filter Topology
open Gali.DiscretionCommitment.Ex5_3 (lag Bdd bdd_lin bdd_shift bdd_lag eq_zero_of_quadratic)

/-! ### (a) Discretion: the period problem -/

/-- Galí (2015), Exercise 5.4(a): the minimiser `x* = −κ v/(ϑ + κ²)` of the period loss
`ϑ x² + (κ x + v)²`. -/
noncomputable def periodOpt (ϑ κ v : ℝ) : ℝ := -κ * v / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 5.4(a): `ϑ x² + (κx + v)² = ϑ x*² + (κx* + v)² + (ϑ + κ²)(x − x*)²`. -/
theorem period_loss_eq {ϑ κ v : ℝ} (hK : ϑ + κ ^ 2 ≠ 0) (x : ℝ) :
    ϑ * x ^ 2 + (κ * x + v) ^ 2 = ϑ * periodOpt ϑ κ v ^ 2 + (κ * periodOpt ϑ κ v + v) ^ 2 +
      (ϑ + κ ^ 2) * (x - periodOpt ϑ κ v) ^ 2 := by
  unfold periodOpt
  field_simp
  ring

/-- **Exercise 5.4(a), the period problem** (Galí 2015, p. 161): `x` minimises
`ϑ x² + (κ x + v)²` iff `x = x*`. -/
theorem period_opt_iff {ϑ κ v x : ℝ} (hϑ : 0 < ϑ) :
    (∀ x', ϑ * x ^ 2 + (κ * x + v) ^ 2 ≤ ϑ * x' ^ 2 + (κ * x' + v) ^ 2) ↔
      x = periodOpt ϑ κ v := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  constructor
  · intro h
    have h1 := h (periodOpt ϑ κ v)
    rw [period_loss_eq hK.ne' x] at h1
    have h2 : (ϑ + κ ^ 2) * (x - periodOpt ϑ κ v) ^ 2 ≤ 0 := by linarith
    have h3 : (x - periodOpt ϑ κ v) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (x - periodOpt ϑ κ v)]) (sq_nonneg _)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  · rintro rfl x'
    rw [period_loss_eq hK.ne' x']
    nlinarith [sq_nonneg (x' - periodOpt ϑ κ v)]

/-- **Exercise 5.4(a), the targeting rule** (Galí 2015, p. 161): `x = x*` iff
`x = −(κ/ϑ) π̃` with `π̃ = κ x + v`. -/
theorem period_targeting_iff {ϑ κ v x : ℝ} (hϑ : 0 < ϑ) :
    x = periodOpt ϑ κ v ↔ x = -(κ / ϑ) * (κ * x + v) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  unfold periodOpt
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [eq_div_iff hK.ne']
    field_simp at h
    linear_combination h

/-- Galí (2015), Exercise 5.4(a) (**remark on timing**): if the central bank took `E_t π_{t+1}`
(rather than `E_t π̃_{t+1}`) as given, then `π_t = (κ x + w)/(1 + βγ)` and the period loss
`ϑ x² + (π_t − γπ_{t−1})²` would be minimised iff `ϑ (1 + βγ) x = −κ π̃`. -/
theorem period_foc_alt {ϑ κ β γ w pm x : ℝ} (hϑ : 0 < ϑ) (hb : 0 < 1 + β * γ) :
    (∀ x', ϑ * x ^ 2 + ((κ * x + w) / (1 + β * γ) - γ * pm) ^ 2 ≤
        ϑ * x' ^ 2 + ((κ * x' + w) / (1 + β * γ) - γ * pm) ^ 2) ↔
      ϑ * (1 + β * γ) * x = -κ * ((κ * x + w) / (1 + β * γ) - γ * pm) := by
  set k := κ / (1 + β * γ)
  set v := w / (1 + β * γ) - γ * pm
  have e : ∀ x', (κ * x' + w) / (1 + β * γ) - γ * pm = k * x' + v := fun x' => by
    simp only [k, v]; field_simp; ring
  simp only [e]
  rw [period_opt_iff hϑ, period_targeting_iff hϑ]
  have hk : κ = k * (1 + β * γ) := by simp only [k]; field_simp
  have key : x = -(k / ϑ) * (k * x + v) ↔ ϑ * x = -k * (k * x + v) := by
    constructor
    · intro h
      nth_rewrite 1 [h]
      field_simp
    · intro h
      field_simp
      linear_combination h
  rw [key, hk]
  constructor
  · intro h
    linear_combination (1 + β * γ) * h
  · intro h
    apply mul_left_cancel₀ hb.ne'
    linear_combination h

/-! ### (a) Discretion: the equilibrium -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 5.4: lagged inflation `π_{t−1}`, with the given initial `π_{−1}`. -/
def prev (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p0
  | t + 1 => p t

/-- Galí (2015), Exercise 5.4, p. 161: quasi-differenced inflation `π̃_t = π_t − γ π_{t−1}`. -/
def tilde (γ : ℝ) (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => p t - γ • prev p0 p t

/-- Galí (2015), Exercise 5.4, p. 161: the Phillips curve with indexation,
`π_t − γπ_{t−1} = κ x_t + β E_t(π_{t+1} − γπ_t) + u_t`. -/
def NKPCInd (β κ γ : ℝ) (p0 : Ω → ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, tilde γ p0 p t = κ • x t + β • 𝔼.E t (tilde γ p0 p (t + 1)) + u t

/-- Galí (2015), Exercise 5.4(a): the discretionary equilibrium, the Phillips curve together
with the targeting rule `x_t = −(κ/ϑ) π̃_t`. -/
def DiscretionEq (β κ γ ϑ : ℝ) (p0 : Ω → ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  NKPCInd 𝔼 β κ γ p0 x p u ∧ ∀ t, x t = -(κ / ϑ) • tilde γ p0 p t

omit 𝔼 in
/-- Galí (2015), Exercise 5.4: `π̃_{t+1} = π_{t+1} − γ π_t`. -/
theorem tilde_succ (γ : ℝ) (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) :
    tilde γ p0 p (t + 1) = p (t + 1) - γ • p t := rfl

/-- **Exercise 5.4(a), period optimality** (Galí 2015, p. 161): in the discretionary
equilibrium, at every date and state, `(x_t, π̃_t)` minimises `ϑ x² + π̃²` over the choices
`π̃ = κ x + v_t` with `v_t = β E_t π̃_{t+1} + u_t` given. -/
theorem ex5_4a_period_optimal {β κ γ ϑ : ℝ} (hϑ : 0 < ϑ) {p0 : Ω → ℝ} {x p u : ℕ → Ω → ℝ}
    (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u) (t : ℕ) (ω : Ω) (x' : ℝ) :
    ϑ * x t ω ^ 2 + tilde γ p0 p t ω ^ 2 ≤
      ϑ * x' ^ 2 + (κ * x' + (β * 𝔼.E t (tilde γ p0 p (t + 1)) ω + u t ω)) ^ 2 := by
  have h1 := congrFun (he.1 t) ω
  have h2 := congrFun (he.2 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  set v := β * 𝔼.E t (tilde γ p0 p (t + 1)) ω + u t ω
  have hp : tilde γ p0 p t ω = κ * x t ω + v := by rw [h1]; ring
  have hx : x t ω = periodOpt ϑ κ v :=
    (period_targeting_iff hϑ).mpr (by rw [← hp]; exact h2)
  rw [hp]
  exact (period_opt_iff hϑ).mpr hx x'

/-- Galí (2015), Exercise 5.4(a): `βρ_u < 1`. -/
theorem beta_rho_lt_one {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) : β * ρ < 1 := by
  have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0.le
  have h2 : β * |ρ| < β * 1 := mul_lt_mul_of_pos_left hρ hβ0
  linarith

/-- Galí (2015), Exercise 5.4(a): the discretionary coefficient `ψ = ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiD (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- **Exercise 5.4(a), uniqueness** (Galí 2015, p. 161): in every discretionary equilibrium with
bounded `π̃`, `π̃_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))` and `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))`. -/
theorem ex5_4a_unique {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {p0 : Ω → ℝ} {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u)
    (hb : BoundedProc (tilde γ p0 p)) :
    tilde γ p0 p = (fun t => psiD β κ ϑ ρ • u t) ∧
      x = fun t => (-(κ / ϑ) * psiD β κ ϑ ρ) • u t := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
    have : 0 < 1 - β * ρ := by linarith
    positivity
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  set b := ϑ / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [pow_pos (abs_pos.mpr hκ) 2, sq_abs κ]
  set q := tilde γ p0 p
  have h1 : ∀ t, q t = a • 𝔼.E t (q (t + 1)) + b • u t := by
    intro t
    funext ω
    have e1 := congrFun (he.1 t) ω
    have e2 := congrFun (he.2 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e2] at e1
    simp only [a, b]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - q t ω * κ ^ 2 * hinv
  have h2 : ∀ t, (fun t => psiD β κ ϑ ρ • u t) t =
      a • 𝔼.E t ((fun t => psiD β κ ϑ ρ • u t) (t + 1)) + b • u t := by
    intro t
    funext ω
    simp only [map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b, psiD]
    field_simp
    ring
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc fun t => psiD β κ ϑ ρ • u t :=
    ⟨|psiD β κ ϑ ρ| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hq := 𝔼.forward_unique ha h1 h2 hb hcb
  refine ⟨hq, ?_⟩
  funext t
  have hqt := congrFun hq t
  simp only [q] at hqt
  rw [he.2 t, hqt, smul_smul]

/-- Galí (2015), Exercise 5.4(a): inflation under discretion, constructed recursively by
`π_t = γ π_{t−1} + ψ u_t` from `π_{−1}`. -/
noncomputable def discInfl (γ ψ : ℝ) (p0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => γ • p0 + ψ • u 0
  | t + 1 => γ • discInfl γ ψ p0 u t + ψ • u (t + 1)

omit 𝔼 in
/-- Galí (2015), Exercise 5.4(a): `π̃ = ψ u` along the constructed path. -/
theorem tilde_discInfl (γ ψ : ℝ) (p0 : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    tilde γ p0 (discInfl γ ψ p0 u) t = ψ • u t := by
  rcases t with _ | t
  · simp [tilde, prev, discInfl]
  · simp [tilde, prev, discInfl]

/-- **Exercise 5.4(a), existence** (Galí 2015, p. 161): `π_t = γπ_{t−1} + ψ u_t`,
`x_t = −(κ/ϑ) ψ u_t` (`ψ = ϑ/(κ² + ϑ(1 − βρ_u))`) is a discretionary equilibrium. -/
theorem ex5_4a_exists {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    (p0 : Ω → ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEq 𝔼 β κ γ ϑ p0 (fun t => (-(κ / ϑ) * psiD β κ ϑ ρ) • u t)
      (discInfl γ (psiD β κ ϑ ρ) p0 u) u := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
    have : 0 < 1 - β * ρ := by linarith
    positivity
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [tilde_discInfl, tilde_discInfl]
    funext ω
    simp only [map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, psiD]
    field_simp
    ring
  · rw [tilde_discInfl, smul_smul]

/-- **Exercise 5.4(a), inflation persistence** (Galí 2015, p. 161): in every discretionary
equilibrium with bounded `π̃`, `π_t = γ π_{t−1} + ϑ u_t/(κ² + ϑ(1 − βρ_u))`. -/
theorem ex5_4a_inflation {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {p0 : Ω → ℝ} {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u)
    (hb : BoundedProc (tilde γ p0 p)) (t : ℕ) :
    p t = γ • prev p0 p t + psiD β κ ϑ ρ • u t := by
  have h := congrFun (ex5_4a_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub he hb).1 t
  simp only [tilde] at h
  rw [← h]
  abel

/-! ### (b) Commitment (deterministic) -/

/-- Galí (2015), Exercise 5.4(b): feasibility, `π̃_t = κ x_t + β π̃_{t+1} + u_t`. -/
def CFeasible (β κ : ℝ) (u x q : ℕ → ℝ) : Prop := ∀ t, q t = κ * x t + β * q (t + 1) + u t

/-- Galí (2015), Exercise 5.4(b): the date-`t` loss term `βᵗ (ϑ x_t² + π̃_t²)`. -/
def lossTerm (β ϑ : ℝ) (x q : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (ϑ * x t ^ 2 + q t ^ 2)

/-- Galí (2015), Exercise 5.4, p. 161: the loss `∑ βᵗ (ϑ x_t² + π̃_t²)` (up to the factor `½`). -/
noncomputable def loss (β ϑ : ℝ) (x q : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x q t

/-- Galí (2015), Exercise 5.4(b): optimality among bounded feasible plans. -/
def COptimal (β κ ϑ : ℝ) (u x q : ℕ → ℝ) : Prop :=
  CFeasible β κ u x q ∧ Bdd x ∧ Bdd q ∧
    ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' → loss β ϑ x q ≤ loss β ϑ x' q'

/-- **Exercise 5.4(b), the FOCs** (Galí 2015, p. 161; cf. p. 134): `ϑ x_t − κ ξ_t = 0`,
`π̃_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def CFOC (κ ϑ : ℝ) (x q ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * x t - κ * ξ t = 0 ∧ q t + ξ t - lag ξ t = 0

/-- Galí (2015), Exercise 5.4(b): the cross term `βᵗ (ϑ x_t dx_t + π̃_t dπ̃_t)`. -/
def cross (β ϑ : ℝ) (x q dx dq : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (ϑ * x t * dx t + q t * dq t)

/-- Galí (2015), Exercise 5.4(b) (**summation by parts**): if `ϑ x = κ ξ`, then for every
homogeneous direction (`dπ̃_t = κ dx_t + β dπ̃_{t+1}`),
`∑_{t ≤ T} βᵗ(ϑ x dx + π̃ dπ̃) = ∑_{t ≤ T} βᵗ R_t dπ̃_t − β^{T+1} ξ_T dπ̃_{T+1}`,
`R_t = π̃_t + ξ_t − ξ_{t−1}`. -/
theorem partial_sum_identity {β κ ϑ : ℝ} {x q ξ dx dq : ℕ → ℝ}
    (hx : ∀ t, ϑ * x t = κ * ξ t) (hd : ∀ t, dq t = κ * dx t + β * dq (t + 1)) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ((q t + ξ t - lag ξ t) * dq t) -
        β ^ (T + 1) * ξ T * dq (T + 1) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, cross, pow_zero, one_mul, pow_one]
    rw [hx 0]
    simp only [lag]
    linear_combination (-ξ 0) * hd 0
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => cross β ϑ x q dx dq t) (T + 1), ih,
      Finset.sum_range_succ (fun t => β ^ t * ((q t + ξ t - lag ξ t) * dq t)) (T + 1)]
    generalize ∑ t ∈ Finset.range (T + 1), β ^ t * ((q t + ξ t - lag ξ t) * dq t) = S
    simp only [cross]
    rw [hx (T + 1)]
    simp only [lag]
    linear_combination (-β ^ (T + 1) * ξ (T + 1)) * hd (T + 1)

/-- Galí (2015), Exercise 5.4(b): the loss series of bounded paths is summable. -/
theorem loss_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) {x q : ℕ → ℝ}
    (hx : Bdd x) (hq : Bdd q) : Summable (lossTerm β ϑ x q) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hq
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (ϑ * A ^ 2 + B ^ 2)) (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have h1 : x t ^ 2 ≤ A ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
  have h2 : q t ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hϑ]

/-- Galí (2015), Exercise 5.4(b): the cross series of bounded paths is summable. -/
theorem cross_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x q dx dq : ℕ → ℝ}
    (hx : Bdd x) (hq : Bdd q) (hdx : Bdd dx) (hdq : Bdd dq) :
    Summable (cross β ϑ x q dx dq) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hq
  obtain ⟨D, hD⟩ := hdx
  obtain ⟨E, hE⟩ := hdq
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (|ϑ| * A * D + B * E)) (fun t => ?_)
  rw [Real.norm_eq_abs, cross, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hA t) (hD t) (abs_nonneg _) hA0) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul (hB t) (hE t) (abs_nonneg _) hB0

/-- Galí (2015), Exercise 5.4(b): two bounded plans that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {x q x' q' : ℕ → ℝ} (hx : Bdd x) (hq : Bdd q) (hx' : Bdd x') (hq' : Bdd q') (k : ℕ)
    (heq : ∀ t, x' (t + k) = x (t + k) ∧ q' (t + k) = q (t + k)) :
    loss β ϑ x' q' = loss β ϑ x q +
      ∑ t ∈ Finset.range k, (lossTerm β ϑ x' q' t - lossTerm β ϑ x q t) := by
  unfold loss
  rw [← (loss_summable hβ0 hβ1 hϑ hx' hq').sum_add_tsum_nat_add k,
    ← (loss_summable hβ0 hβ1 hϑ hx hq).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm β ϑ x' q' (t + k) = ∑' t, lossTerm β ϑ x q (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2]
  rw [this]
  ring

/-- **Exercise 5.4(b), sufficiency** (Galí 2015, p. 161): a bounded feasible plan satisfying
the FOCs is optimal among bounded feasible plans, and it is the only optimal one. -/
theorem ex5_4b_sufficient {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x q ξ : ℕ → ℝ} (hf : CFeasible β κ u x q) (hx : Bdd x) (hq : Bdd q)
    (hfoc : CFOC κ ϑ x q ξ) :
    COptimal β κ ϑ u x q ∧
      ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' → loss β ϑ x' q' ≤ loss β ϑ x q →
        x' = x ∧ q' = q := by
  have hξe : ξ = fun t => (ϑ / κ) * x t + 0 * x t := by
    funext t
    have := (hfoc t).1
    field_simp
    linear_combination -this
  have hξ : Bdd ξ := by rw [hξe]; exact bdd_lin hx hx _ _
  have hbd : ∀ (z z' : ℕ → ℝ), Bdd z → Bdd z' → Bdd fun t => z' t - z t := by
    intro z z' hz hz'
    have := bdd_lin hz' hz 1 (-1); simpa [sub_eq_add_neg] using this
  have key : ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' →
      loss β ϑ x' q' = loss β ϑ x q + loss β ϑ (fun t => x' t - x t) (fun t => q' t - q t) := by
    intro x' q' hf' hx' hq'
    set dx : ℕ → ℝ := fun t => x' t - x t
    set dq : ℕ → ℝ := fun t => q' t - q t
    have hd : ∀ t, dq t = κ * dx t + β * dq (t + 1) := fun t => by
      simp only [dx, dq]; linear_combination hf' t - hf t
    have hbdx : Bdd dx := hbd x x' hx hx'
    have hbdq : Bdd dq := hbd q q' hq hq'
    have hcs := cross_summable (ϑ := ϑ) hβ0.le hβ1 hx hq hbdx hbdq
    have hxf : ∀ t, ϑ * x t = κ * ξ t := fun t => by linarith [(hfoc t).1]
    have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t =
        -(β ^ (T + 1) * ξ T * dq (T + 1)) := by
      intro T
      rw [partial_sum_identity hxf hd T]
      simp [(hfoc _).2]
    obtain ⟨A, hA⟩ := hξ
    obtain ⟨E, hE⟩ := hbdq
    have hbound : ∀ T, ‖-(β ^ (T + 1) * ξ T * dq (T + 1))‖ ≤ β ^ (T + 1) * (A * E) := by
      intro T
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos hβ0, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hA T) (hE (T + 1)) (abs_nonneg _) hA0)
        (pow_nonneg hβ0.le _)
    have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t)
        atTop (𝓝 0) := by
      simp only [hpart]
      refine squeeze_zero_norm hbound ?_
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const (A * E)
    have htsum : ∑' t, cross β ϑ x q dx dq t = 0 :=
      tendsto_nhds_unique ((hcs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) hlim
    have hl := loss_summable hβ0.le hβ1 hϑ.le hx hq
    have hqq := loss_summable hβ0.le hβ1 hϑ.le hbdx ⟨E, hE⟩
    have hsplit : lossTerm β ϑ x' q' = fun t => lossTerm β ϑ x q t +
        2 * cross β ϑ x q dx dq t + lossTerm β ϑ dx dq t := by
      funext t
      simp only [lossTerm, cross, dx, dq]
      ring
    unfold loss
    rw [hsplit, (hl.add (hcs.mul_left 2)).tsum_add hqq, hl.tsum_add (hcs.mul_left 2),
      tsum_mul_left, htsum, mul_zero, add_zero]
  have hqnn : ∀ dx dq : ℕ → ℝ, ∀ t, 0 ≤ lossTerm β ϑ dx dq t := fun dx dq t => by
    unfold lossTerm; positivity
  refine ⟨⟨hf, hx, hq, fun x' q' hf' hx' hq' => ?_⟩, fun x' q' hf' hx' hq' hle => ?_⟩
  · rw [key x' q' hf' hx' hq']
    exact le_add_of_nonneg_right (tsum_nonneg (hqnn _ _))
  · rw [key x' q' hf' hx' hq'] at hle
    have h0 : loss β ϑ (fun t => x' t - x t) (fun t => q' t - q t) ≤ 0 := by linarith
    have hs := loss_summable hβ0.le hβ1 hϑ.le (hbd x x' hx hx') (hbd q q' hq hq')
    have hz : ∀ t, lossTerm β ϑ (fun t => x' t - x t) (fun t => q' t - q t) t = 0 := fun t =>
      le_antisymm ((hs.le_tsum t (fun j _ => hqnn _ _ j)).trans h0) (hqnn _ _ t)
    have hall : ∀ t, x' t - x t = 0 ∧ q' t - q t = 0 := by
      intro t
      have h := hz t
      simp only [lossTerm] at h
      have hin : ϑ * (x' t - x t) ^ 2 + (q' t - q t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h (pow_ne_zero t hβ0.ne')
        · exact h
      have a1 := mul_nonneg hϑ.le (sq_nonneg (x' t - x t))
      have a2 := sq_nonneg (q' t - q t)
      refine ⟨?_, pow_eq_zero_iff two_ne_zero |>.mp (by linarith)⟩
      have : (x' t - x t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp (show ϑ * (x' t - x t) ^ 2 = 0 by linarith) with h | h
        · exact absurd h hϑ.ne'
        · exact h
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨funext fun t => sub_eq_zero.mp (hall t).1, funext fun t => sub_eq_zero.mp (hall t).2⟩

/-- Galí (2015), Exercise 5.4(b): the test direction `dπ̃ = 𝟙_{t = s}`. -/
def dirQ (s : ℕ) : ℕ → ℝ := fun t => if t = s then 1 else 0

/-- Galí (2015), Exercise 5.4(b): the output part of the test direction,
`dx_t = (dπ̃_t − β dπ̃_{t+1})/κ`. -/
noncomputable def dirX (β κ : ℝ) (s : ℕ) : ℕ → ℝ := fun t => (dirQ s t - β * dirQ s (t + 1)) / κ

/-- **Exercise 5.4(b), necessity** (Galí 2015, p. 161): an optimal bounded feasible plan
satisfies the FOCs with `ξ = (ϑ/κ) x`. -/
theorem ex5_4b_necessary {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ)
    {u x q : ℕ → ℝ} (hopt : COptimal β κ ϑ u x q) :
    CFOC κ ϑ x q (fun t => ϑ / κ * x t) := by
  obtain ⟨hf, hx, hq, hmin⟩ := hopt
  set ξ : ℕ → ℝ := fun t => ϑ / κ * x t
  have hxf : ∀ t, ϑ * x t = κ * ξ t := fun t => by simp only [ξ]; field_simp
  intro s
  refine ⟨by linarith [hxf s], ?_⟩
  have h0 : Bdd (dirQ s) := ⟨1, fun t => by simp only [dirQ]; split_ifs <;> simp⟩
  have h1 : Bdd (dirX β κ s) := by
    have := bdd_lin h0 (bdd_shift h0) κ⁻¹ (-β / κ)
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirX β κ s t = κ⁻¹ * dirQ s t + -β / κ * dirQ s (t + 1) := by
      simp only [dirX]; ring
    rw [e]; exact hM t
  have hd : ∀ t, dirQ s t = κ * dirX β κ s t + β * dirQ s (t + 1) := fun t => by
    simp only [dirX]; field_simp; ring
  have hz : ∀ t, s < t → dirQ s t = 0 ∧ dirX β κ s t = 0 := by
    have hp : ∀ u, s < u → dirQ s u = 0 := fun u hu => by
      simp only [dirQ]
      split_ifs
      · omega
      · rfl
    intro t ht
    refine ⟨hp t ht, ?_⟩
    simp only [dirX]; rw [hp t ht, hp (t + 1) (by omega)]; simp
  set C := ∑ t ∈ Finset.range (s + 1), cross β ϑ x q (dirX β κ s) (dirQ s) t
  set Q := ∑ t ∈ Finset.range (s + 1), lossTerm β ϑ (dirX β κ s) (dirQ s) t
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun t _ => by unfold lossTerm; positivity
  have hquad : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q := by
    intro ε
    have hb : ∀ z d : ℕ → ℝ, Bdd z → Bdd d → Bdd fun t => z t + ε * d t := fun z d hz' hd' => by
      have := bdd_lin hz' hd' 1 ε; simpa using this
    have hf' : CFeasible β κ u (fun t => x t + ε * dirX β κ s t) (fun t => q t + ε * dirQ s t) :=
      fun t => by linear_combination hf t + ε * hd t
    have hle := hmin _ _ hf' (hb _ _ hx h1) (hb _ _ hq h0)
    rw [loss_eq_of_eq_after hβ0.le hβ1 hϑ hx hq (hb _ _ hx h1) (hb _ _ hq h0) (s + 1)
      (fun t => by
        obtain ⟨a1, a2⟩ := hz (t + (s + 1)) (by omega)
        simp [a1, a2])] at hle
    have hsum : ∑ t ∈ Finset.range (s + 1),
        (lossTerm β ϑ (fun t => x t + ε * dirX β κ s t) (fun t => q t + ε * dirQ s t) t -
          lossTerm β ϑ x q t) = 2 * ε * C + ε ^ 2 * Q := by
      simp only [C, Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, cross]
      ring
    linarith
  have hC := eq_zero_of_quadratic hQ hquad
  have hid := partial_sum_identity (q := q) hxf hd s
  rw [(hz (s + 1) (by omega)).1] at hid
  have hsingle : ∑ t ∈ Finset.range (s + 1), β ^ t * ((q t + ξ t - lag ξ t) * dirQ s t) =
      β ^ s * (q s + ξ s - lag ξ s) := by
    rw [Finset.sum_eq_single s (fun t _ hts => by simp [dirQ, hts])
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self s)) h)]
    simp [dirQ]
  rw [hsingle] at hid
  have : β ^ s * (q s + ξ s - lag ξ s) = 0 := by
    have hC' : C = 0 := hC
    simp only [C] at hC'
    rw [hC'] at hid
    simp only [mul_zero, sub_zero] at hid
    linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (pow_ne_zero s hβ0.ne')
  · exact h

/-- **Exercise 5.4(b)** (Galí 2015, p. 161): a bounded feasible plan is optimal under commitment
iff it satisfies the FOCs for some multiplier. -/
theorem ex5_4b_optimal_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x q : ℕ → ℝ} (hf : CFeasible β κ u x q) (hx : Bdd x) (hq : Bdd q) :
    COptimal β κ ϑ u x q ↔ ∃ ξ, CFOC κ ϑ x q ξ :=
  ⟨fun h => ⟨_, ex5_4b_necessary hβ0 hβ1 hκ hϑ.le h⟩,
    fun ⟨_, h⟩ => (ex5_4b_sufficient hβ0 hβ1 hκ hϑ hf hx hq h).1⟩

/-- Galí (2015), Exercise 5.4(b): the quasi-differenced price level `p̃_t = ∑_{s ≤ t} π̃_s`. -/
def cumsum (q : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), q s

/-- **Exercise 5.4(b), the `p̃`-level rule** (Galí 2015, p. 161; cf. (13), p. 135): the FOCs
hold for some multiplier iff `x_t = −(κ/ϑ) p̃_t` for all `t`. -/
theorem foc_iff_level_rule {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) {x q : ℕ → ℝ} :
    (∃ ξ, CFOC κ ϑ x q ξ) ↔ ∀ t, x t = -(κ / ϑ) * cumsum q t := by
  constructor
  · rintro ⟨ξ, hfoc⟩
    have hξ : ∀ t, ξ t = -cumsum q t := by
      intro t
      induction t with
      | zero =>
        have := (hfoc 0).2
        simp only [lag] at this
        simp only [cumsum, zero_add, Finset.sum_range_one]
        linarith
      | succ t ih =>
        have := (hfoc (t + 1)).2
        simp only [lag] at this
        simp only [cumsum] at ih ⊢
        rw [Finset.sum_range_succ]
        linarith
    intro t
    have := (hfoc t).1
    rw [hξ t] at this
    field_simp
    linear_combination this
  · intro h
    refine ⟨fun t => -cumsum q t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp; ring
    · rcases t with _ | t
      · simp [lag, cumsum]
      · simp only [lag, cumsum]
        rw [Finset.sum_range_succ]
        ring

/-- Galí (2015), Exercise 5.4(b): the level rule is equivalent to the difference rule
`x_t − x_{t−1} = −(κ/ϑ) π̃_t` with `x_{−1} = 0`. -/
theorem level_rule_iff_diff {κ ϑ : ℝ} {x q : ℕ → ℝ} :
    (∀ t, x t = -(κ / ϑ) * cumsum q t) ↔ ∀ t, x t - lag x t = -(κ / ϑ) * q t := by
  constructor
  · intro h t
    rcases t with _ | t
    · simp [lag, h 0, cumsum]
    · simp only [lag, h (t + 1), h t, cumsum]
      rw [Finset.sum_range_succ]
      ring
  · intro h t
    induction t with
    | zero =>
      have := h 0
      simp only [lag, sub_zero] at this
      simp [cumsum, this]
    | succ t ih =>
      have := h (t + 1)
      simp only [lag] at this
      simp only [cumsum] at ih ⊢
      rw [Finset.sum_range_succ]
      linear_combination this + ih

/-- Galí (2015), Exercise 5.4(b): with the log price level `P` (`P 0 = p_{−2}`, `P 1 = p_{−1}`,
`P (t+2) = p_t`), inflation `π_t = p_t − p_{t−1}` and `π_{−1} = p_{−1} − p_{−2}`,
`p̃_t = ∑_{s ≤ t} (π_s − γ π_{s−1}) = (p_t − p_{−1}) − γ (p_{t−1} − p_{−2})`. -/
theorem cumsum_tilde_eq (γ : ℝ) (P : ℕ → ℝ) (t : ℕ) :
    cumsum (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) t =
      (P (t + 2) - P 1) - γ * (P (t + 1) - P 0) := by
  induction t with
  | zero => simp [cumsum]
  | succ t ih =>
    simp only [cumsum] at ih ⊢
    rw [Finset.sum_range_succ, ih]
    ring

/-- **Exercise 5.4(b), optimal commitment policy** (Galí 2015, p. 161): with
`π̃_t = π_t − γ π_{t−1}` and the log price level `P` as in `cumsum_tilde_eq`, a bounded feasible
plan is optimal under commitment iff
`x_t = −(κ/ϑ)[(p_t − p_{−1}) − γ (p_{t−1} − p_{−2})]` for all `t ≥ 0`. -/
theorem ex5_4b {β κ ϑ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x : ℕ → ℝ} (P : ℕ → ℝ)
    (hf : CFeasible β κ u x (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)))
    (hx : Bdd x) (hq : Bdd fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) :
    COptimal β κ ϑ u x (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) ↔
      ∀ t, x t = -(κ / ϑ) * ((P (t + 2) - P 1) - γ * (P (t + 1) - P 0)) := by
  rw [ex5_4b_optimal_iff hβ0 hβ1 hκ hϑ hf hx hq, foc_iff_level_rule hϑ.ne']
  simp only [cumsum_tilde_eq]

end Gali.DiscretionCommitment.Ex5_4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.5: optimal steady-state inflation and the zero lower bound

Galí (2015), Chapter 5, Exercise 5.5, p. 162. The model is
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ) + z_t` (`Ex5_1.DIS`) and
`π_t − π̄ = β E_t(π_{t+1} − π̄) + κ x_t + u_t` (`NKPCbar`), with independent, serially
uncorrelated normal shocks `z_t ~ N(0, σ_z²)`, `u_t ~ N(0, σ_u²)`, and the loss
`π̄ + E_0 ∑ βᵗ (ϑ x_t² + (π_t − π̄)²)`.

## (a) Discretion and the choice of `π̄`
* `ex5_5a_period_optimal`: the targeting rule `x_t = −(κ/ϑ)(π_t − π̄)` solves each period's
  problem (taking `β E_t(π_{t+1} − π̄) + u_t` as given).
* `ex5_5a_exists`, `ex5_5a_unique`: for every `π̄` the discretionary equilibrium is
  `x_t = −κu_t/(ϑ+κ²)`, `π_t = π̄ + ϑu_t/(ϑ+κ²)`, `i_t = ρ + π̄ + σz_t + σκu_t/(ϑ+κ²)`, unique among
  equilibria at a bounded distance (normal shocks are unbounded, so Galí's "bounded" convention
  is applied to deviations). Only `E_t u_{t+1} = 0` is used.
* `ex5_5a_loss_diff`: the stabilisation part of the loss does not depend on `π̄`, so the total
  loss is `π̄` plus a constant.
* With a genuine Gaussian law (`GaussianShocks`; `hasLaw_affine`, `hasLaw_rate`):
  `i_t ~ N(ρ + π̄, s²)`, `s² = σ²σ_z² + (σκ/(ϑ+κ²))² σ_u²` (`rateVar`), and
  `ex5_5a_prob`: `P(i_t < 0) = Φ(−(ρ + π̄)/s)` (`prob_neg`), `Φ = cdf N(0,1)` (`Phi`).
* The quantile `z_{0.05}` (`z05`) is constructed: `Φ` is continuous (`phi_continuous`, no atoms),
  strictly increasing (`phi_strictMono`, positive density) with limits 0 and 1, so by the
  intermediate value theorem `Φ(q) = 0.05` has a solution (`exists_quantile`), unique
  (`eq_z05_iff`).
* `ex5_5a`: with `π̄* = −ρ − s z_{0.05}` (`piStar`), the zero bound binds with probability exactly
  5%; the constraint `P(i_t < 0) ≤ 5%` holds iff `π̄ ≥ π̄*` (`constraint_iff`); and `π̄*` is the
  unique loss-minimising feasible steady-state inflation rate (the book's linear cost `π̄` puts no
  sign restriction on `π̄`; `π̄* < 0` when `ρ > s |z_{0.05}|`).

## (b) An implementing rule
`i_t = ρ + π̄ + σ z_t + ψ_u u_t + φ_π(π_t − π̄)`, `ψ_u = (σκ − φ_πϑ)/(ϑ + κ²)` (`RuleB`, `psiU`):
`ex5_5b_exists` (the allocation of (a) is an equilibrium), `ex5_5b_unique` (for `φ_π > 1` it is
the unique equilibrium with adapted `x, π` at a bounded distance, via the determinacy result of
Exercise 5.1), `ex5_5b_not_unique` (for `0 ≤ φ_π ≤ 1` it is not).

## Non-vacuity
`shockMeasure`, `concreteShocks`: the i.i.d. product law on `ℕ → ℝ × ℝ`; `truncE`: an
expectation system on it under which the shocks are i.i.d. (`concrete_iid`);
`ex5_5_nonvacuous`: there the equilibrium under `π̄*` exists and `P(i_t < 0) = 5%` exactly.
-/

namespace Gali.DiscretionCommitment.Ex5_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### The standard normal distribution function and its 5% quantile -/

/-- Galí (2015), Exercise 5.5(a), p. 162: the standard normal distribution function
`Φ = cdf N(0, 1)`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Galí (2015), Exercise 5.5(a): `Φ` is continuous (the normal law has no atoms). -/
theorem phi_continuous : Continuous Phi := by
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro a
  have hsing : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
    rw [measure_cdf]; exact measure_singleton a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hle := (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl a)
  have heq : Function.leftLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a :=
    le_antisymm hle (by linarith)
  unfold Phi
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rw [← continuousWithinAt_Iio_iff_Iic]
    exact ((cdf (gaussianReal 0 1)).mono.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  · exact (cdf (gaussianReal 0 1)).right_continuous a

/-- Galí (2015), Exercise 5.5(a): `Φ` is strictly increasing (the normal density is
positive). -/
theorem phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : (cdf (gaussianReal 0 1)).measure (Set.Ioc a b) = ENNReal.ofReal (Phi b - Phi a) :=
    StieltjesFunction.measure_Ioc _ a b
  rw [measure_cdf] at h1
  have h2 : gaussianReal 0 1 (Set.Ioc a b) ≠ 0 := by
    intro h
    have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
    linarith
  rw [h1, ne_eq, ENNReal.ofReal_eq_zero, not_le] at h2
  linarith

/-- Galí (2015), Exercise 5.5(a): every level `α ∈ (0, 1)` is attained by `Φ` (intermediate
value theorem). -/
theorem exists_quantile {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : ∃ q, Phi q = α := by
  obtain ⟨a, ha⟩ :=
    ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).eventually (gt_mem_nhds h0)).exists
  obtain ⟨b, hb⟩ :=
    ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).eventually (lt_mem_nhds h1)).exists
  have ha' : Phi a < α := ha
  have hb' : α < Phi b := hb
  have hab : a ≤ b := by
    by_contra h
    have := phi_strictMono.monotone (le_of_lt (not_le.mp h))
    linarith
  obtain ⟨q, -, hq⟩ := intermediate_value_Icc hab phi_continuous.continuousOn ⟨ha'.le, hb'.le⟩
  exact ⟨q, hq⟩

/-- Galí (2015), Exercise 5.5(a): the 5% quantile `z_{0.05}` of the standard normal
distribution, `Φ(z_{0.05}) = 0.05`. -/
noncomputable def z05 : ℝ :=
  Classical.choose (exists_quantile (α := 1 / 20) (by norm_num) (by norm_num))

/-- Galí (2015), Exercise 5.5(a): `Φ(z_{0.05}) = 1/20`. -/
theorem phi_z05 : Phi z05 = 1 / 20 :=
  Classical.choose_spec (exists_quantile (α := 1 / 20) (by norm_num) (by norm_num))

/-- Galí (2015), Exercise 5.5(a): `z_{0.05}` is the unique solution of `Φ(q) = 1/20`. -/
theorem eq_z05_iff (q : ℝ) : Phi q = 1 / 20 ↔ q = z05 := by
  constructor
  · intro h
    exact phi_strictMono.injective (h.trans phi_z05.symm)
  · rintro rfl
    exact phi_z05

/-! ### Laws -/

variable {Ω : Type*}

/-- Galí (2015), Exercise 5.5(a): if `Z ~ N(0, σ_z²)` and `U ~ N(0, σ_u²)` are independent, then
`c + a Z + b U ~ N(c, a² σ_z² + b² σ_u²)`. -/
theorem hasLaw_affine [MeasurableSpace Ω] {μ : Measure Ω} {Z U : Ω → ℝ} {vz vu : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 vz) μ) (hU : HasLaw U (gaussianReal 0 vu) μ)
    (hI : IndepFun Z U μ) (a b c : ℝ) :
    HasLaw (fun ω => c + (a * Z ω + b * U ω))
      (gaussianReal c (⟨a ^ 2, sq_nonneg a⟩ * vz + ⟨b ^ 2, sq_nonneg b⟩ * vu)) μ := by
  have hX := gaussianReal_const_mul hZ a
  have hY := gaussianReal_const_mul hU b
  have hI' : IndepFun (fun ω => a * Z ω) (fun ω => b * U ω) μ :=
    hI.comp (measurable_const_mul a) (measurable_const_mul b)
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hI' hX hY
  have hS : HasLaw ((fun ω => a * Z ω) + fun ω => b * U ω)
      (gaussianReal (a * 0 + b * 0) (⟨a ^ 2, sq_nonneg a⟩ * vz + ⟨b ^ 2, sq_nonneg b⟩ * vu)) μ :=
    ⟨hX.aemeasurable.add hY.aemeasurable, hmap⟩
  have := gaussianReal_const_add hS c
  simpa using this

/-- Galí (2015), Exercise 5.5(a): for `X ~ N(c, v)` with `v ≠ 0`,
`P(X < 0) = Φ(−c/√v)`. -/
theorem prob_neg [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal c v) μ) :
    μ.real {ω | X ω < 0} = Phi (-c / Real.sqrt v) := by
  rw [hX.measureReal_eq (p := fun x => x < 0) measurableSet_Iio]
  have := nullSingletonClass_gaussianReal (μ := c) hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have h1 : (gaussianReal c v).real {x : ℝ | x < 0} = (gaussianReal c v).real (Set.Iic 0) := by
    simp only [measureReal_def]
    rw [show {x : ℝ | x < 0} = Set.Iio 0 from rfl, measure_congr Iio_ae_eq_Iic]
  have hmap : (gaussianReal 0 1).map (fun x => c + Real.sqrt v * x) = gaussianReal c v := by
    have e1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
    rw [show (fun x => c + Real.sqrt v * x) = (fun x => c + x) ∘ (fun x => Real.sqrt v * x)
      from rfl, ← Measure.map_map (measurable_const_add c) (measurable_const_mul _), e1,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [h1, ← hmap,
    map_measureReal_apply (by fun_prop) measurableSet_Iic, Phi, cdf_eq_real]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-! ### The model and the discretionary equilibrium -/

variable (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 5.5, p. 162: the Phillips curve around steady-state inflation `π̄`,
`π_t − π̄ = β E_t(π_{t+1} − π̄) + κ x_t + u_t`. -/
def NKPCbar (β κ πbar : ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t - (fun _ => πbar) = β • 𝔼.E t (p (t + 1) - fun _ => πbar) + κ • x t + u t

/-- Galí (2015), Exercise 5.5(a): the discretionary targeting rule `x_t = −(κ/ϑ)(π_t − π̄)`. -/
def Targeting (κ ϑ πbar : ℝ) (x p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = -(κ / ϑ) • (p t - fun _ => πbar)

/-- Galí (2015), Exercise 5.5(a): the discretionary equilibrium given `π̄`: the IS curve
(`Ex5_1.DIS`), the Phillips curve and the targeting rule. -/
def DiscEq (β σ κ ϑ ρ πbar : ℝ) (z u x p i : ℕ → Ω → ℝ) : Prop :=
  Ex5_1.DIS 𝔼 σ ρ x p i z ∧ NKPCbar 𝔼 β κ πbar x p u ∧ Targeting κ ϑ πbar x p

/-- Galí (2015), Exercise 5.5(a): the discretionary output gap `x_t = −κ u_t/(ϑ + κ²)`. -/
noncomputable def xT (κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (-κ / (ϑ + κ ^ 2)) • u t

/-- Galí (2015), Exercise 5.5(a): discretionary inflation `π_t = π̄ + ϑ u_t/(ϑ + κ²)`. -/
noncomputable def pT (κ ϑ πbar : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => πbar) + (ϑ / (ϑ + κ ^ 2)) • u t

/-- Galí (2015), Exercise 5.5(a): the discretionary nominal rate
`i_t = (ρ + π̄) + σ z_t + σκ u_t/(ϑ + κ²)`. -/
noncomputable def iT (σ κ ϑ ρ πbar : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (ρ + πbar) + (σ * z t ω + σ * κ / (ϑ + κ ^ 2) * u t ω)

/-- Galí (2015), Exercise 5.5(a): with i.i.d. shocks the expectations of the discretionary
variables are `E_t x_{t+1} = 0`, `E_t π_{t+1} = π̄`. -/
theorem E_targets {κ ϑ πbar : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 0 u) (t : ℕ) :
    𝔼.E t (xT κ ϑ u (t + 1)) = 0 ∧ 𝔼.E t (pT κ ϑ πbar u (t + 1)) = fun _ => πbar := by
  have hEu : 𝔼.E t (u (t + 1)) = 0 := by rw [hu.2 t, zero_smul]
  constructor
  · simp only [xT, map_smul, hEu, smul_zero]
  · simp only [pT, map_add, map_smul, hEu, smul_zero, add_zero, 𝔼.const]

/-- **Exercise 5.5(a), existence** (Galí 2015, p. 162): with i.i.d. shocks, `x_t = −κu_t/(ϑ+κ²)`,
`π_t = π̄ + ϑu_t/(ϑ+κ²)`, `i_t = ρ + π̄ + σ z_t + σκ u_t/(ϑ+κ²)` is a discretionary equilibrium,
for every `π̄`. -/
theorem ex5_5a_exists {β σ κ ϑ ρ πbar : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    DiscEq 𝔼 β σ κ ϑ ρ πbar z u (xT κ ϑ u) (pT κ ϑ πbar u) (iT σ κ ϑ ρ πbar z u) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · obtain ⟨h1, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
    rw [h1, h2]
    funext ω
    simp only [xT, iT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · obtain ⟨-, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
    rw [map_sub, h2, 𝔼.const, sub_self]
    funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- **Exercise 5.5(a), period optimality** (Galí 2015, p. 162): in a discretionary equilibrium,
at every date and state, `(x_t, π_t − π̄)` minimises `ϑ x² + (π − π̄)²` over the choices
`π − π̄ = κ x + v_t`, `v_t = β E_t(π_{t+1} − π̄) + u_t` taken as given. -/
theorem ex5_5a_period_optimal {β σ κ ϑ ρ πbar : ℝ} (hϑ : 0 < ϑ) {z u x p i : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i) (t : ℕ) (ω : Ω) (x' : ℝ) :
    ϑ * x t ω ^ 2 + (p t ω - πbar) ^ 2 ≤
      ϑ * x' ^ 2 + (κ * x' + (β * 𝔼.E t (p (t + 1) - fun _ => πbar) ω + u t ω)) ^ 2 := by
  have h1 := congrFun (he.2.1 t) ω
  have h2 := congrFun (he.2.2 t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  set v := β * 𝔼.E t (p (t + 1) - fun _ => πbar) ω + u t ω
  have hp : p t ω - πbar = κ * x t ω + v := by rw [h1]; ring
  have hx : x t ω = Ex5_4.periodOpt ϑ κ v :=
    (Ex5_4.period_targeting_iff hϑ).mpr (by rw [← hp]; exact h2)
  rw [hp]
  exact (Ex5_4.period_opt_iff hϑ).mpr hx x'

/-- **Exercise 5.5(a), uniqueness** (Galí 2015, p. 162): every discretionary equilibrium whose
inflation differs from `π̄ + ϑu/(ϑ+κ²)` by a bounded process is the one above (normal shocks
are unbounded, so uniqueness is stated for bounded deviations). -/
theorem ex5_5a_unique {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {z u x p i : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i)
    (hb : BoundedProc (p - pT κ ϑ πbar u)) :
    x = xT κ ϑ u ∧ p = pT κ ϑ πbar u ∧ i = iT σ κ ϑ ρ πbar z u := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [pow_pos (abs_pos.mpr hκ) 2, sq_abs κ]
  have hEp : ∀ t, 𝔼.E t (pT κ ϑ πbar u (t + 1)) = fun _ => πbar := fun t =>
    (E_targets 𝔼 hu t).2
  have hd : ∀ t, (p - pT κ ϑ πbar u) t =
      a • 𝔼.E t ((p - pT κ ϑ πbar u) (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t
    funext ω
    have e1 := congrFun (he.2.1 t) ω
    have e2 := congrFun (he.2.2 t) ω
    have e3 := congrFun (hEp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, 𝔼.const]
      at e1 e2 e3 ⊢
    rw [e3]
    simp only [pT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    rw [e2] at e1
    simp only [a]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - (p t ω - πbar) * κ ^ 2 * hinv
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = a • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + (0 : ℕ → Ω → ℝ) t :=
    fun t => by simp
  have hzero := 𝔼.forward_unique ha hd h0 hb ⟨0, fun _ _ => by simp⟩
  have hp : p = pT κ ϑ πbar u := sub_eq_zero.mp hzero
  have hx : x = xT κ ϑ u := by
    funext t
    rw [he.2.2 t, hp]
    funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨hx, hp, ?_⟩
  funext t ω
  have e1 := congrFun (he.1 t) ω
  obtain ⟨h1, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
  rw [hx, hp, h1, h2] at e1
  simp only [xT, iT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at e1 ⊢
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  linear_combination σ * e1 - (i t ω - πbar - ρ) * hinv

/-- **Exercise 5.5(a), the loss** (Galí 2015, p. 162): for any stabilisation loss functional
`L(x, π − π̄)` (e.g. `E_0 ∑ βᵗ(ϑ x_t² + (π_t − π̄)²)`), the total loss `π̄ + L` of the
discretionary equilibria under two steady-state inflation rates differs exactly by the
difference of the rates: the stabilisation component does not depend on `π̄`. -/
theorem ex5_5a_loss_diff {β σ κ ϑ ρ πbar πbar' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i)
    (hb : BoundedProc (p - pT κ ϑ πbar u)) (he' : DiscEq 𝔼 β σ κ ϑ ρ πbar' z u x' p' i')
    (hb' : BoundedProc (p' - pT κ ϑ πbar' u))
    (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℝ) :
    (πbar + L x (fun t => p t - fun _ => πbar)) - (πbar' + L x' (fun t => p' t - fun _ => πbar'))
      = πbar - πbar' := by
  obtain ⟨hx, hp, -⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb
  obtain ⟨hx', hp', -⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he' hb'
  have e : (fun t => p t - fun _ => πbar) = fun t => p' t - fun _ => πbar' := by
    rw [hp, hp']
    funext t
    simp only [pT, add_sub_cancel_left]
  rw [e, hx, hx']
  ring

/-! ### (b) An implementing rule -/

/-- Galí (2015), Exercise 5.5(b), p. 162: the interest-rate rule
`i_t = ρ + π̄ + σ z_t + ψ_u u_t + φ_π (π_t − π̄)`. -/
def RuleB (ρ πbar σ φ ψu : ℝ) (z u p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = fun ω => ρ + πbar + σ * z t ω + ψu * u t ω + φ * (p t ω - πbar)

/-- Galí (2015), Exercise 5.5(b): the coefficient `ψ_u = (σκ − φ_π ϑ)/(ϑ + κ²)` that makes the
rule consistent with the discretionary allocation. -/
noncomputable def psiU (σ κ ϑ φ : ℝ) : ℝ := (σ * κ - φ * ϑ) / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 5.5(b): an equilibrium under the rule: the IS curve, the Phillips
curve and the rule. -/
def EqB (β σ κ ρ πbar φ ψu : ℝ) (z u x p i : ℕ → Ω → ℝ) : Prop :=
  Ex5_1.DIS 𝔼 σ ρ x p i z ∧ NKPCbar 𝔼 β κ πbar x p u ∧ RuleB ρ πbar σ φ ψu z u p i

/-- **Exercise 5.5(b), existence** (Galí 2015, p. 162): the discretionary allocation of (a),
with its nominal rate, is an equilibrium under the rule with `ψ_u = (σκ − φ_π ϑ)/(ϑ + κ²)`, for
every `φ_π`. -/
theorem ex5_5b_exists {β σ κ ϑ ρ πbar φ : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u (xT κ ϑ u) (pT κ ϑ πbar u)
      (iT σ κ ϑ ρ πbar z u) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  obtain ⟨h1, h2, -⟩ := ex5_5a_exists 𝔼 (β := β) (ρ := ρ) (πbar := πbar) (z := z) hσ hϑ hu
  refine ⟨h1, h2, fun t => ?_⟩
  funext ω
  simp only [iT, pT, psiU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Exercise 5.5(b): the difference of two equilibria under the rule solves the
homogeneous system of Exercise 5.1 (`Ex5_1.HomEq`). -/
theorem eqB_sub {β σ κ ρ πbar φ ψu : ℝ} {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (h : EqB 𝔼 β σ κ ρ πbar φ ψu z u x p i) (h' : EqB 𝔼 β σ κ ρ πbar φ ψu z u x' p' i') :
    Ex5_1.HomEq 𝔼 β σ κ φ (x - x') (p - p') := by
  obtain ⟨hd, hn, hr⟩ := h
  obtain ⟨hd', hn', hr'⟩ := h'
  intro t
  constructor
  · funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hd' t) ω
    have r1 := congrFun (hr t) ω
    have r2 := congrFun (hr' t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 r1 r2 ⊢
    rw [e1, e2, r1, r2]
    ring
  · funext ω
    have e1 := congrFun (hn t) ω
    have e2 := congrFun (hn' t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, 𝔼.const]
      at e1 e2 ⊢
    linear_combination e1 - e2

/-- Galí (2015), Exercise 5.5(b): adding a solution of the homogeneous system to an equilibrium
under the rule (and moving the rate by `φ_π dπ`) gives another equilibrium. -/
theorem eqB_add_hom {β σ κ ρ πbar φ ψu : ℝ} {z u x p i dx dp : ℕ → Ω → ℝ}
    (h : EqB 𝔼 β σ κ ρ πbar φ ψu z u x p i) (hd : Ex5_1.HomEq 𝔼 β σ κ φ dx dp) :
    EqB 𝔼 β σ κ ρ πbar φ ψu z u (x + dx) (p + dp) (i + fun t => φ • dp t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (hd t).1 ω
    have r := congrFun (h3 t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] at e1 e2 r ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun (h2 t) ω
    have e2 := congrFun (hd t).2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      𝔼.const] at e1 e2 ⊢
    linear_combination e1 + e2
  · funext ω
    have r := congrFun (h3 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
    rw [r]
    ring

/-- Galí (2015), Exercise 5.5(b): the discretionary output gap and inflation are adapted. -/
theorem targets_adapted {κ ϑ πbar : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (xT κ ϑ u) ∧ 𝔼.Adapted (pT κ ϑ πbar u) :=
  ⟨fun t => by simp only [xT, map_smul, hu t],
    fun t => by simp only [pT, map_add, map_smul, hu t, 𝔼.const]⟩

/-- **Exercise 5.5(b), determinacy** (Galí 2015, p. 162): for `φ_π > 1`, the discretionary
allocation is the unique equilibrium under the rule among those with adapted `x, π` at a
bounded distance from it. -/
theorem ex5_5b_unique {β σ κ ϑ ρ πbar φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 0 u)
    (he : EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u x p i) (hax : 𝔼.Adapted x)
    (hap : 𝔼.Adapted p) (hbx : BoundedProc (x - xT κ ϑ u))
    (hbp : BoundedProc (p - pT κ ϑ πbar u)) :
    x = xT κ ϑ u ∧ p = pT κ ϑ πbar u ∧ i = iT σ κ ϑ ρ πbar z u := by
  have hD : 0 < σ + κ * φ := by nlinarith
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  have hS := (Ex5_1.schurStable_A_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ
  have hhom := eqB_sub 𝔼 he (ex5_5b_exists 𝔼 (β := β) (ρ := ρ) (πbar := πbar) (φ := φ) (z := z)
    hσ.ne' hϑ hu)
  have hsol := (Ex5_1.homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mp hhom
  obtain ⟨hxa, hpa⟩ := targets_adapted 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu.1
  have had := Ex5_1.adaptedVec_stack 𝔼 (x := x - xT κ ϑ u) (p := p - pT κ ϑ πbar u)
    (fun t => by simp only [Pi.sub_apply, map_sub, hax t, hxa t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hap t, hpa t])
  have h0 : 𝔼.Solves (Ex5_1.A β σ κ φ) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hS hsol h0 had (fun t i => by simp)
    (Ex5_1.boundedVec_stack hbx hbp) ⟨0, fun t i ω => by simp⟩
  have hx : x = xT κ ϑ u := by
    funext t
    have := congrFun (congrFun heq t) 0
    simpa [Ex5_1.stack, sub_eq_zero] using this
  have hp : p = pT κ ϑ πbar u := by
    funext t
    have := congrFun (congrFun heq t) 1
    simpa [Ex5_1.stack, sub_eq_zero] using this
  refine ⟨hx, hp, ?_⟩
  funext t ω
  rw [he.2.2 t, hp]
  simp only [iT, pT, psiU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Exercise 5.5(b), indeterminacy for `φ_π ≤ 1`** (Galí 2015, p. 162): for `0 ≤ φ_π ≤ 1`
there is another equilibrium under the rule, with adapted `x, π` at a bounded distance from
the discretionary allocation. -/
theorem ex5_5b_not_unique [Nonempty Ω] {β σ κ ϑ ρ πbar φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    ∃ x p i, EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u x p i ∧ 𝔼.Adapted x ∧ 𝔼.Adapted p ∧
      BoundedProc (x - xT κ ϑ u) ∧ BoundedProc (p - pT κ ϑ πbar u) ∧
      ¬ (x = xT κ ϑ u ∧ p = pT κ ϑ πbar u) := by
  have hD : 0 < σ + κ * φ := by positivity
  have hS : ¬ SchurStable (tr2 (Ex5_1.A β σ κ φ)) (det2 (Ex5_1.A β σ κ φ)) := by
    rw [Ex5_1.schurStable_A_iff hσ hκ hβ0 hβ1 hφ0]; linarith
  have h0 : 𝔼.Solves (Ex5_1.A β σ κ φ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ :=
    𝔼.system_not_unique hS h0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : Ex5_1.stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t i
    fin_cases i <;> rfl
  have hhom : Ex5_1.HomEq 𝔼 β σ κ φ (fun t => y t 0) (fun t => y t 1) :=
    (Ex5_1.homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mpr (by rw [hst]; exact hy)
  obtain ⟨hxa, hpa⟩ := targets_adapted 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu.1
  refine ⟨xT κ ϑ u + fun t => y t 0, pT κ ϑ πbar u + fun t => y t 1, _,
    eqB_add_hom 𝔼 (ex5_5b_exists 𝔼 hσ.ne' hϑ hu) hhom,
    fun t => by simp only [Pi.add_apply, map_add, hxa t, hay t 0],
    fun t => by simp only [Pi.add_apply, map_add, hpa t, hay t 1],
    ⟨M, fun t ω => by simpa using hM t 0 ω⟩, ⟨M, fun t ω => by simpa using hM t 1 ω⟩, ?_⟩
  rintro ⟨h1, h2⟩
  apply hne
  funext t i
  fin_cases i
  · funext ω
    have := congrFun (congrFun h1 t) ω
    simpa using this
  · funext ω
    have := congrFun (congrFun h2 t) ω
    simpa using this

/-! ### Normal shocks and the zero lower bound -/

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- Galí (2015), Exercise 5.5, p. 162: normal shocks on a probability space: at every date
`z_t ~ N(0, σ_z²)` and `u_t ~ N(0, σ_u²)` are independent. -/
structure GaussianShocks where
  /-- The demand shock `z_t`. -/
  z : ℕ → Ω → ℝ
  /-- The cost-push shock `u_t`. -/
  u : ℕ → Ω → ℝ
  /-- The variance `σ_z²`. -/
  vz : ℝ≥0
  /-- The variance `σ_u²`. -/
  vu : ℝ≥0
  /-- `z_t ~ N(0, σ_z²)`. -/
  lawZ : ∀ t, HasLaw (z t) (gaussianReal 0 vz) μ
  /-- `u_t ~ N(0, σ_u²)`. -/
  lawU : ∀ t, HasLaw (u t) (gaussianReal 0 vu) μ
  /-- `z_t` and `u_t` are independent. -/
  indep : ∀ t, IndepFun (z t) (u t) μ

/-- Galí (2015), Exercise 5.5(a): the variance of the nominal rate,
`s² = σ² σ_z² + (σκ/(ϑ + κ²))² σ_u²`. -/
noncomputable def rateVar (σ κ ϑ : ℝ) (vz vu : ℝ≥0) : ℝ≥0 :=
  ⟨σ ^ 2, sq_nonneg σ⟩ * vz + ⟨(σ * κ / (ϑ + κ ^ 2)) ^ 2, sq_nonneg _⟩ * vu

/-- Galí (2015), Exercise 5.5(a): the standard deviation `s` of the nominal rate. -/
noncomputable def rateSd (σ κ ϑ : ℝ) (vz vu : ℝ≥0) : ℝ := Real.sqrt (rateVar σ κ ϑ vz vu)

/-- **Exercise 5.5(a), the optimal steady-state inflation** (Galí 2015, p. 162):
`π̄* = −ρ − s z_{0.05}` (`z_{0.05} < 0`, so `π̄* = s |z_{0.05}| − ρ`). -/
noncomputable def piStar (σ κ ϑ ρ : ℝ) (vz vu : ℝ≥0) : ℝ := -ρ - rateSd σ κ ϑ vz vu * z05

variable {μ}

/-- **Exercise 5.5(a), the law of the nominal rate** (Galí 2015, p. 162): in the discretionary
equilibrium `i_t ~ N(ρ + π̄, s²)`. -/
theorem hasLaw_rate (S : GaussianShocks μ) (σ κ ϑ ρ πbar : ℝ) (t : ℕ) :
    HasLaw (iT σ κ ϑ ρ πbar S.z S.u t) (gaussianReal (ρ + πbar) (rateVar σ κ ϑ S.vz S.vu)) μ :=
  hasLaw_affine (S.lawZ t) (S.lawU t) (S.indep t) σ (σ * κ / (ϑ + κ ^ 2)) (ρ + πbar)

/-- **Exercise 5.5(a), the probability of the zero bound** (Galí 2015, p. 162): in every
discretionary equilibrium (with bounded deviation), `P(i_t < 0) = Φ(−(ρ + π̄)/s)` at every
date. -/
theorem ex5_5a_prob (S : GaussianShocks μ) {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hv : rateVar σ κ ϑ S.vz S.vu ≠ 0)
    (hu : 𝔼.IsAR1 0 S.u) {x p i : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ πbar S.z S.u x p i) (hb : BoundedProc (p - pT κ ϑ πbar S.u))
    (t : ℕ) :
    μ.real {ω | i t ω < 0} = Phi (-(ρ + πbar) / rateSd σ κ ϑ S.vz S.vu) := by
  obtain ⟨-, -, hi⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb
  rw [hi]
  exact prob_neg hv (hasLaw_rate S σ κ ϑ ρ πbar t)

/-- Galí (2015), Exercise 5.5(a): `s > 0` when `s² ≠ 0`. -/
theorem rateSd_pos {σ κ ϑ : ℝ} {vz vu : ℝ≥0} (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    0 < rateSd σ κ ϑ vz vu :=
  Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))

/-- **Exercise 5.5(a), the constraint** (Galí 2015, p. 162): `Φ(−(ρ + π̄)/s) ≤ 0.05` iff
`π̄ ≥ π̄*`, with equality iff `π̄ = π̄*`. -/
theorem constraint_iff {σ κ ϑ ρ πbar : ℝ} {vz vu : ℝ≥0} (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    (Phi (-(ρ + πbar) / rateSd σ κ ϑ vz vu) ≤ 1 / 20 ↔ piStar σ κ ϑ ρ vz vu ≤ πbar) ∧
      (Phi (-(ρ + πbar) / rateSd σ κ ϑ vz vu) = 1 / 20 ↔ πbar = piStar σ κ ϑ ρ vz vu) := by
  have hs := rateSd_pos hv
  constructor
  · rw [← phi_z05, phi_strictMono.le_iff_le, div_le_iff₀ hs, piStar]
    constructor <;> intro h <;> nlinarith
  · rw [eq_z05_iff, div_eq_iff hs.ne', piStar]
    constructor <;> intro h <;> linarith

/-- **Exercise 5.5(a), optimal steady-state inflation** (Galí 2015, p. 162): with normal shocks
and `s > 0`, choose `π̄* = −ρ − s z_{0.05}`. Then (i) under `π̄*` the zero bound binds with
probability exactly 5% at every date; (ii) a discretionary equilibrium under `π̄` satisfies
the 5% constraint iff `π̄ ≥ π̄*`; (iii) among those, `π̄*` has the lowest total loss
`π̄ + L(x, π − π̄)`, strictly lower unless `π̄ = π̄*`. -/
theorem ex5_5a (S : GaussianShocks μ) {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hv : rateVar σ κ ϑ S.vz S.vu ≠ 0)
    (hu : 𝔼.IsAR1 0 S.u) {x p i x' p' i' : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ (piStar σ κ ϑ ρ S.vz S.vu) S.z S.u x p i)
    (hb : BoundedProc (p - pT κ ϑ (piStar σ κ ϑ ρ S.vz S.vu) S.u))
    (he' : DiscEq 𝔼 β σ κ ϑ ρ πbar S.z S.u x' p' i') (hb' : BoundedProc (p' - pT κ ϑ πbar S.u))
    (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℝ) (t : ℕ) :
    μ.real {ω | i t ω < 0} = 1 / 20 ∧
      (μ.real {ω | i' t ω < 0} ≤ 1 / 20 ↔ piStar σ κ ϑ ρ S.vz S.vu ≤ πbar) ∧
      (μ.real {ω | i' t ω < 0} ≤ 1 / 20 →
        piStar σ κ ϑ ρ S.vz S.vu + L x (fun t => p t - fun _ => piStar σ κ ϑ ρ S.vz S.vu) ≤
          πbar + L x' (fun t => p' t - fun _ => πbar) ∧
        (piStar σ κ ϑ ρ S.vz S.vu + L x (fun t => p t - fun _ => piStar σ κ ϑ ρ S.vz S.vu) =
          πbar + L x' (fun t => p' t - fun _ => πbar) → πbar = piStar σ κ ϑ ρ S.vz S.vu)) := by
  rw [ex5_5a_prob 𝔼 S hβ0 hβ1 hσ hκ hϑ hv hu he hb t,
    ex5_5a_prob 𝔼 S hβ0 hβ1 hσ hκ hϑ hv hu he' hb' t]
  have hd := ex5_5a_loss_diff 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb he' hb' L
  refine ⟨((constraint_iff hv).2).mpr rfl, (constraint_iff hv).1, fun hc => ?_⟩
  have hle := ((constraint_iff hv).1).mp hc
  constructor
  · linarith
  · intro h; linarith

/-! ### A concrete model (non-vacuity) -/

/-- Galí (2015), Exercise 5.5: truncation of a shock history at date `t` (later shocks are set
to their mean `0`). -/
def trunc (t : ℕ) (ω : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := fun s => if s ≤ t then ω s else 0

/-- Galí (2015), Exercise 5.5: truncations compose, `trunc t ∘ trunc s = trunc s ∘ trunc t =
trunc s` for `s ≤ t`. -/
theorem trunc_trunc {s t : ℕ} (h : s ≤ t) (ω : ℕ → ℝ × ℝ) :
    trunc t (trunc s ω) = trunc s ω ∧ trunc s (trunc t ω) = trunc s ω := by
  constructor <;> funext k <;> simp only [trunc] <;> split_ifs <;> first | rfl | omega

/-- Galí (2015), Exercise 5.5: the certainty-equivalent expectation system on shock histories,
`E_t f(ω) = f(ω_0, …, ω_t, 0, 0, …)`. It satisfies all the axioms of `ExpectationSystem` (for
affine functions of the shocks it agrees with the conditional expectation under any law with
mean-zero independent shocks; that agreement is not needed and not proved here). -/
def truncE : ExpectationSystem (ℕ → ℝ × ℝ) where
  E t := LinearMap.funLeft ℝ ℝ (trunc t)
  const _ _ := rfl
  mono _ _ _ h ω := h _
  tower {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply]
    rw [(trunc_trunc h ω).1]
  known {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply]
    rw [(trunc_trunc h ω).2]

/-- Galí (2015), Exercise 5.5: the i.i.d. product law `⊗ₜ N(0, σ_z²) ⊗ N(0, σ_u²)` on shock
histories. -/
noncomputable abbrev shockMeasure (vz vu : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => (gaussianReal 0 vz).prod (gaussianReal 0 vu)

/-- Galí (2015), Exercise 5.5: the date-`t` shock pair has the product normal law. -/
theorem hasLaw_pair (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => ω t) ((gaussianReal 0 vz).prod (gaussianReal 0 vu))
      (shockMeasure vz vu) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => (gaussianReal 0 vz).prod (gaussianReal 0 vu))
    t).hasLaw

/-- Galí (2015), Exercise 5.5: `z_t ~ N(0, σ_z²)` on the concrete space. -/
theorem hasLaw_z (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => (ω t).1) (gaussianReal 0 vz) (shockMeasure vz vu) :=
  HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: `u_t ~ N(0, σ_u²)` on the concrete space. -/
theorem hasLaw_u (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => (ω t).2) (gaussianReal 0 vu) (shockMeasure vz vu) :=
  HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: the concrete normal shocks. -/
noncomputable def concreteShocks (vz vu : ℝ≥0) : GaussianShocks (shockMeasure vz vu) where
  z t ω := (ω t).1
  u t ω := (ω t).2
  vz := vz
  vu := vu
  lawZ t := hasLaw_z vz vu t
  lawU t := hasLaw_u vz vu t
  indep t := (indepFun_iff_hasLaw_prodMk_prod (hasLaw_z vz vu t) (hasLaw_u vz vu t)).mpr
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: under `truncE` the concrete shocks are i.i.d. in the sense of the
expectation system: adapted, with `E_t z_{t+1} = E_t u_{t+1} = 0`. -/
theorem concrete_iid (vz vu : ℝ≥0) :
    truncE.IsAR1 0 (concreteShocks vz vu).z ∧ truncE.IsAR1 0 (concreteShocks vz vu).u := by
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ⟨fun t => ?_, fun t => ?_⟩⟩ <;> funext ω <;>
    simp [truncE, concreteShocks, trunc, LinearMap.funLeft_apply]

/-- Galí (2015), Exercise 5.5(a): `s² ≠ 0` when `σ ≠ 0` and `σ_z² ≠ 0`. -/
theorem rateVar_ne_zero {σ κ ϑ : ℝ} {vz : ℝ≥0} (vu : ℝ≥0) (hσ : σ ≠ 0) (hvz : vz ≠ 0) :
    rateVar σ κ ϑ vz vu ≠ 0 := by
  unfold rateVar
  intro h
  have h1 := (add_eq_zero.mp h).1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · apply hσ
    have : σ ^ 2 = 0 := congrArg NNReal.toReal h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  · exact hvz h2

/-- **Exercise 5.5(a), non-vacuity** (Galí 2015, p. 162): on the concrete space (normal shocks,
the expectation system `truncE`), the discretionary equilibrium under `π̄*` exists and the
nominal rate is negative with probability exactly 5% at every date. -/
theorem ex5_5_nonvacuous {β σ κ ϑ ρ : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (vz vu : ℝ≥0)
    (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    DiscEq truncE β σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z
        (concreteShocks vz vu).u (xT κ ϑ (concreteShocks vz vu).u)
        (pT κ ϑ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).u)
        (iT σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z (concreteShocks vz vu).u) ∧
      ∀ t, (shockMeasure vz vu).real
        {ω | iT σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z
          (concreteShocks vz vu).u t ω < 0} = 1 / 20 := by
  refine ⟨ex5_5a_exists truncE hσ hϑ (concrete_iid vz vu).2, fun t => ?_⟩
  rw [prob_neg hv (hasLaw_rate (concreteShocks vz vu) σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) t)]
  exact ((constraint_iff hv).2).mpr rfl

end Gali.DiscretionCommitment.Ex5_5

set_option linter.style.longLine false
#print axioms Gali.DiscretionCommitment.SchurStable
#print axioms Gali.DiscretionCommitment.disc
#print axioms Gali.DiscretionCommitment.root₁
#print axioms Gali.DiscretionCommitment.root₂
#print axioms Gali.DiscretionCommitment.root_sum
#print axioms Gali.DiscretionCommitment.root_prod
#print axioms Gali.DiscretionCommitment.root_eq
#print axioms Gali.DiscretionCommitment.normSq_root_of_neg
#print axioms Gali.DiscretionCommitment.norm_root_of_nonneg
#print axioms Gali.DiscretionCommitment.schurStable_iff_roots
#print axioms Gali.DiscretionCommitment.chSeq
#print axioms Gali.DiscretionCommitment.convSeq
#print axioms Gali.DiscretionCommitment.convSeq_rec
#print axioms Gali.DiscretionCommitment.chSeq_eq_convSeq
#print axioms Gali.DiscretionCommitment.norm_convSeq_le
#print axioms Gali.DiscretionCommitment.abs_chSeq_le
#print axioms Gali.DiscretionCommitment.tendsto_chSeq
#print axioms Gali.DiscretionCommitment.tr2
#print axioms Gali.DiscretionCommitment.det2
#print axioms Gali.DiscretionCommitment.tr2_eq_trace
#print axioms Gali.DiscretionCommitment.det2_eq_det
#print axioms Gali.DiscretionCommitment.sq_eq_cayleyHamilton
#print axioms Gali.DiscretionCommitment.pow_succ_eq
#print axioms Gali.DiscretionCommitment.abs_pow_entry_le
#print axioms Gali.DiscretionCommitment.tendsto_pow_entry
#print axioms Gali.DiscretionCommitment.BoundedSeq
#print axioms Gali.DiscretionCommitment.homogeneous_iterate
#print axioms Gali.DiscretionCommitment.abs_mulVec_le
#print axioms Gali.DiscretionCommitment.homogeneous_eq_zero
#print axioms Gali.DiscretionCommitment.eq_root_of_eq
#print axioms Gali.DiscretionCommitment.exists_eigenvector
#print axioms Gali.DiscretionCommitment.exists_bounded_homogeneous
#print axioms Gali.DiscretionCommitment.ExpectationSystem
#print axioms Gali.DiscretionCommitment.ExpectationSystem.mk
#print axioms Gali.DiscretionCommitment.ExpectationSystem.E
#print axioms Gali.DiscretionCommitment.ExpectationSystem.const
#print axioms Gali.DiscretionCommitment.ExpectationSystem.mono
#print axioms Gali.DiscretionCommitment.ExpectationSystem.tower
#print axioms Gali.DiscretionCommitment.ExpectationSystem.known
#print axioms Gali.DiscretionCommitment.perfectForesight
#print axioms Gali.DiscretionCommitment.BoundedProc
#print axioms Gali.DiscretionCommitment.BoundedVec
#print axioms Gali.DiscretionCommitment.ExpectationSystem.Adapted
#print axioms Gali.DiscretionCommitment.ExpectationSystem.IsAR1
#print axioms Gali.DiscretionCommitment.ExpectationSystem.E_neg
#print axioms Gali.DiscretionCommitment.ExpectationSystem.E_smul
#print axioms Gali.DiscretionCommitment.ExpectationSystem.E_E_self
#print axioms Gali.DiscretionCommitment.ExpectationSystem.abs_E_le
#print axioms Gali.DiscretionCommitment.ExpectationSystem.bounded_E
#print axioms Gali.DiscretionCommitment.ExpectationSystem.ar1_iterate
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forward_iterate
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forward_unique
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forward_ar1_solves
#print axioms Gali.DiscretionCommitment.ExpectationSystem.E_tsum
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forwardSeries
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forwardSeries_summable
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forwardSeries_solves
#print axioms Gali.DiscretionCommitment.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.DiscretionCommitment.ExpectationSystem.eq_forwardSeries
#print axioms Gali.DiscretionCommitment.ExpectationSystem.Solves
#print axioms Gali.DiscretionCommitment.ExpectationSystem.AdaptedVec
#print axioms Gali.DiscretionCommitment.ExpectationSystem.system_iterate
#print axioms Gali.DiscretionCommitment.ExpectationSystem.system_unique
#print axioms Gali.DiscretionCommitment.ExpectationSystem.system_not_unique
#print axioms Gali.DiscretionCommitment.ExpectationSystem.Determinate
#print axioms Gali.DiscretionCommitment.ExpectationSystem.determinate_iff
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinObs
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinTree
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinSystem
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.firstHeads
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinShock
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinAR1
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.DiscretionCommitment.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.DiscretionCommitment.LossAndCostPush.gapCoeff
#print axioms Gali.DiscretionCommitment.LossAndCostPush.psiYA
#print axioms Gali.DiscretionCommitment.LossAndCostPush.bigTheta
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lambdaNK
#print axioms Gali.DiscretionCommitment.LossAndCostPush.kappaNK
#print axioms Gali.DiscretionCommitment.LossAndCostPush.vartheta
#print axioms Gali.DiscretionCommitment.LossAndCostPush.bigTheta_pos
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lambdaNK_pos
#print axioms Gali.DiscretionCommitment.LossAndCostPush.gapCoeff_pos
#print axioms Gali.DiscretionCommitment.LossAndCostPush.vartheta_pos
#print axioms Gali.DiscretionCommitment.LossAndCostPush.vartheta_eq_weight_ratio
#print axioms Gali.DiscretionCommitment.LossAndCostPush.periodLoss_eq_scaled
#print axioms Gali.DiscretionCommitment.LossAndCostPush.hasSum_welfare_of_loss
#print axioms Gali.DiscretionCommitment.LossAndCostPush.expected_welfare_eq_scaled_loss
#print axioms Gali.DiscretionCommitment.LossAndCostPush.welfare_le_iff_loss_le
#print axioms Gali.DiscretionCommitment.LossAndCostPush.costPush
#print axioms Gali.DiscretionCommitment.LossAndCostPush.NKPCNatural
#print axioms Gali.DiscretionCommitment.LossAndCostPush.NKPC
#print axioms Gali.DiscretionCommitment.LossAndCostPush.nkpc_iff_costPush
#print axioms Gali.DiscretionCommitment.LossAndCostPush.costPush_eq_zero_iff
#print axioms Gali.DiscretionCommitment.LossAndCostPush.zero_outcome_iff
#print axioms Gali.DiscretionCommitment.LossAndCostPush.bigO_mul
#print axioms Gali.DiscretionCommitment.LossAndCostPush.bigO_weaken
#print axioms Gali.DiscretionCommitment.LossAndCostPush.tendsto_zero_of_bigO
#print axioms Gali.DiscretionCommitment.LossAndCostPush.taylor_two
#print axioms Gali.DiscretionCommitment.LossAndCostPush.exp_taylor_two
#print axioms Gali.DiscretionCommitment.LossAndCostPush.exp_sub_one_bigO
#print axioms Gali.DiscretionCommitment.LossAndCostPush.logdev_taylor
#print axioms Gali.DiscretionCommitment.LossAndCostPush.secondOrderUtility
#print axioms Gali.DiscretionCommitment.LossAndCostPush.tip
#print axioms Gali.DiscretionCommitment.LossAndCostPush.welfareQuadratic
#print axioms Gali.DiscretionCommitment.LossAndCostPush.xhat
#print axioms Gali.DiscretionCommitment.LossAndCostPush.distRemainder
#print axioms Gali.DiscretionCommitment.LossAndCostPush.distortion_iff
#print axioms Gali.DiscretionCommitment.LossAndCostPush.gapCoeff_mul_psiYA
#print axioms Gali.DiscretionCommitment.LossAndCostPush.secondOrderUtility_eq_efficient
#print axioms Gali.DiscretionCommitment.LossAndCostPush.secondOrderUtility_eq_distorted
#print axioms Gali.DiscretionCommitment.LossAndCostPush.small_distortion_polynomial
#print axioms Gali.DiscretionCommitment.LossAndCostPush.period_utility_sub_polynomial
#print axioms Gali.DiscretionCommitment.LossAndCostPush.period_utility_small_distortion
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lemma2_partial
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lemma2_nonneg
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lemma2_hasSum
#print axioms Gali.DiscretionCommitment.LossAndCostPush.lemma2
#print axioms Gali.DiscretionCommitment.LossAndCostPush.inflWeight_of_dispersion
#print axioms Gali.DiscretionCommitment.LossAndCostPush.welfareW
#print axioms Gali.DiscretionCommitment.LossAndCostPush.welfare_small_distortion
#print axioms Gali.DiscretionCommitment.LossAndCostPush.welfareW_efficient
#print axioms Gali.DiscretionCommitment.CostPushSources.lambdaCalvo
#print axioms Gali.DiscretionCommitment.CostPushSources.lambdaNK_alpha_zero
#print axioms Gali.DiscretionCommitment.CostPushSources.lambdaCalvo_pos
#print axioms Gali.DiscretionCommitment.CostPushSources.resetPrice
#print axioms Gali.DiscretionCommitment.CostPushSources.printedResetPrice
#print axioms Gali.DiscretionCommitment.CostPushSources.resetPrice_solves
#print axioms Gali.DiscretionCommitment.CostPushSources.inflation_eq_markupGap
#print axioms Gali.DiscretionCommitment.CostPushSources.markupGap_price
#print axioms Gali.DiscretionCommitment.CostPushSources.nkpc_priceMarkup
#print axioms Gali.DiscretionCommitment.CostPushSources.weights_sum_k0
#print axioms Gali.DiscretionCommitment.CostPushSources.weights_sum_k1
#print axioms Gali.DiscretionCommitment.CostPushSources.resetPrice_const
#print axioms Gali.DiscretionCommitment.CostPushSources.printedResetPrice_const
#print axioms Gali.DiscretionCommitment.CostPushSources.printed_priceSetting_breaks_nkpc
#print axioms Gali.DiscretionCommitment.CostPushSources.priceMarkup_eq
#print axioms Gali.DiscretionCommitment.CostPushSources.printed_markup_line_iff
#print axioms Gali.DiscretionCommitment.CostPushSources.markupGap_wage
#print axioms Gali.DiscretionCommitment.CostPushSources.nkpc_wageMarkup
#print axioms Gali.DiscretionCommitment.CostPushSources.printed_wage_costPush_contradiction
#print axioms Gali.DiscretionCommitment.CostPushSources.wageMarkup_costPush_pos
#print axioms Gali.DiscretionCommitment.Discretion.periodObj
#print axioms Gali.DiscretionCommitment.Discretion.periodObj_sub
#print axioms Gali.DiscretionCommitment.Discretion.periodObj_isMinOn_iff
#print axioms Gali.DiscretionCommitment.Discretion.period_problem_iff
#print axioms Gali.DiscretionCommitment.Discretion.period_solution
#print axioms Gali.DiscretionCommitment.Discretion.TargetingRule
#print axioms Gali.DiscretionCommitment.Discretion.DiscretionEq
#print axioms Gali.DiscretionCommitment.Discretion.discretionEq_iff
#print axioms Gali.DiscretionCommitment.Discretion.aDisc
#print axioms Gali.DiscretionCommitment.Discretion.aDisc_mem
#print axioms Gali.DiscretionCommitment.Discretion.inflation_forward_iff
#print axioms Gali.DiscretionCommitment.Discretion.forwardSeries_adapted
#print axioms Gali.DiscretionCommitment.Discretion.discretion_iff_forwardSeries
#print axioms Gali.DiscretionCommitment.Discretion.discretion_forwardSeries_isEq
#print axioms Gali.DiscretionCommitment.Discretion.psiPi
#print axioms Gali.DiscretionCommitment.Discretion.psiX
#print axioms Gali.DiscretionCommitment.Discretion.den_pos
#print axioms Gali.DiscretionCommitment.Discretion.psiX_eq
#print axioms Gali.DiscretionCommitment.Discretion.psiPi_eq_forward
#print axioms Gali.DiscretionCommitment.Discretion.discretion_msv_isEq
#print axioms Gali.DiscretionCommitment.Discretion.discretionEq_iff_msv
#print axioms Gali.DiscretionCommitment.Discretion.zeroGap_iff
#print axioms Gali.DiscretionCommitment.Discretion.psiPi_lt
#print axioms Gali.DiscretionCommitment.Discretion.dampening
#print axioms Gali.DiscretionCommitment.Discretion.expected_priceLevel_hasSum
#print axioms Gali.DiscretionCommitment.Discretion.priceLevel_response_strictMonoOn
#print axioms Gali.DiscretionCommitment.Discretion.DIS
#print axioms Gali.DiscretionCommitment.Discretion.rateOf
#print axioms Gali.DiscretionCommitment.Discretion.dis_welfareGap_iff
#print axioms Gali.DiscretionCommitment.Discretion.efficientRate_eq
#print axioms Gali.DiscretionCommitment.Discretion.psiI
#print axioms Gali.DiscretionCommitment.Discretion.psiI_eq
#print axioms Gali.DiscretionCommitment.Discretion.interestRate_iff
#print axioms Gali.DiscretionCommitment.Discretion.psiI_pos
#print axioms Gali.DiscretionCommitment.Discretion.stack
#print axioms Gali.DiscretionCommitment.Discretion.boundedVec_stack
#print axioms Gali.DiscretionCommitment.Discretion.adaptedVec_stack
#print axioms Gali.DiscretionCommitment.Discretion.AO
#print axioms Gali.DiscretionCommitment.Discretion.wO
#print axioms Gali.DiscretionCommitment.Discretion.rule8_iff_solves
#print axioms Gali.DiscretionCommitment.Discretion.tr2_AO
#print axioms Gali.DiscretionCommitment.Discretion.det2_AO
#print axioms Gali.DiscretionCommitment.Discretion.AO_not_schurStable
#print axioms Gali.DiscretionCommitment.Discretion.AO_eigenvalues
#print axioms Gali.DiscretionCommitment.Discretion.rule8_indeterminate
#print axioms Gali.DiscretionCommitment.Discretion.psiIprime
#print axioms Gali.DiscretionCommitment.Discretion.rule10_eq
#print axioms Gali.DiscretionCommitment.Discretion.AT
#print axioms Gali.DiscretionCommitment.Discretion.wT
#print axioms Gali.DiscretionCommitment.Discretion.rule10_iff_solves
#print axioms Gali.DiscretionCommitment.Discretion.tr2_AT
#print axioms Gali.DiscretionCommitment.Discretion.det2_AT
#print axioms Gali.DiscretionCommitment.Discretion.AT_schurStable_iff
#print axioms Gali.DiscretionCommitment.Discretion.rule10_implements
#print axioms Gali.DiscretionCommitment.Discretion.rule10_indeterminate
#print axioms Gali.DiscretionCommitment.Commitment.gam
#print axioms Gali.DiscretionCommitment.Commitment.del
#print axioms Gali.DiscretionCommitment.Commitment.gam_pos
#print axioms Gali.DiscretionCommitment.Commitment.gam_mul_denom
#print axioms Gali.DiscretionCommitment.Commitment.gam_mul_le
#print axioms Gali.DiscretionCommitment.Commitment.gam_mul_lt_iff
#print axioms Gali.DiscretionCommitment.Commitment.four_beta_gam_sq_lt_one
#print axioms Gali.DiscretionCommitment.Commitment.sqrt_sq_eq
#print axioms Gali.DiscretionCommitment.Commitment.sqrt_lt_one
#print axioms Gali.DiscretionCommitment.Commitment.del_mul
#print axioms Gali.DiscretionCommitment.Commitment.del_pos
#print axioms Gali.DiscretionCommitment.Commitment.del_quad
#print axioms Gali.DiscretionCommitment.Commitment.del_lt_one_iff
#print axioms Gali.DiscretionCommitment.Commitment.del_mem_Ioo_iff
#print axioms Gali.DiscretionCommitment.Commitment.del_kappa_zero
#print axioms Gali.DiscretionCommitment.Commitment.one_sub_gam_beta_del
#print axioms Gali.DiscretionCommitment.Commitment.del_div_gam
#print axioms Gali.DiscretionCommitment.Commitment.kappa_sq_del
#print axioms Gali.DiscretionCommitment.Commitment.quad_factor
#print axioms Gali.DiscretionCommitment.Commitment.quad_roots
#print axioms Gali.DiscretionCommitment.Commitment.lag
#print axioms Gali.DiscretionCommitment.Commitment.lag_zero
#print axioms Gali.DiscretionCommitment.Commitment.lag_succ
#print axioms Gali.DiscretionCommitment.Commitment.lag_smul
#print axioms Gali.DiscretionCommitment.Commitment.lag_neg
#print axioms Gali.DiscretionCommitment.Commitment.priceGap
#print axioms Gali.DiscretionCommitment.Commitment.priceGap_sub_lag
#print axioms Gali.DiscretionCommitment.Commitment.priceGap_of_sub_lag
#print axioms Gali.DiscretionCommitment.Commitment.FOC
#print axioms Gali.DiscretionCommitment.Commitment.foc_iff_targeting
#print axioms Gali.DiscretionCommitment.Commitment.targeting_iff_eleven_twelve
#print axioms Gali.DiscretionCommitment.Commitment.NKPC
#print axioms Gali.DiscretionCommitment.Commitment.PriceEq
#print axioms Gali.DiscretionCommitment.Commitment.inflOf
#print axioms Gali.DiscretionCommitment.Commitment.gapOf
#print axioms Gali.DiscretionCommitment.Commitment.lag_adapted
#print axioms Gali.DiscretionCommitment.Commitment.pc_iff_fourteen
#print axioms Gali.DiscretionCommitment.Commitment.nkpc_iff_priceEq
#print axioms Gali.DiscretionCommitment.Commitment.wOf
#print axioms Gali.DiscretionCommitment.Commitment.fourteen_iff_w
#print axioms Gali.DiscretionCommitment.Commitment.priceEq_iff_w
#print axioms Gali.DiscretionCommitment.Commitment.beta_del_mem
#print axioms Gali.DiscretionCommitment.Commitment.fwd
#print axioms Gali.DiscretionCommitment.Commitment.pHat
#print axioms Gali.DiscretionCommitment.Commitment.pHat_eq
#print axioms Gali.DiscretionCommitment.Commitment.inflC
#print axioms Gali.DiscretionCommitment.Commitment.gapC
#print axioms Gali.DiscretionCommitment.Commitment.fwd_solves
#print axioms Gali.DiscretionCommitment.Commitment.fwd_bounded
#print axioms Gali.DiscretionCommitment.Commitment.fwd_adapted
#print axioms Gali.DiscretionCommitment.Commitment.pHat_adapted
#print axioms Gali.DiscretionCommitment.Commitment.pHat_bounded
#print axioms Gali.DiscretionCommitment.Commitment.wOf_pHat
#print axioms Gali.DiscretionCommitment.Commitment.pHat_priceEq
#print axioms Gali.DiscretionCommitment.Commitment.priceEq_unique
#print axioms Gali.DiscretionCommitment.Commitment.cand_nkpc
#print axioms Gali.DiscretionCommitment.Commitment.cand_adapted_bounded
#print axioms Gali.DiscretionCommitment.Commitment.one_sub_dbr_pos
#print axioms Gali.DiscretionCommitment.Commitment.fwd_ar1
#print axioms Gali.DiscretionCommitment.Commitment.pHat_ar1
#print axioms Gali.DiscretionCommitment.Commitment.gapC_ar1
#print axioms Gali.DiscretionCommitment.Commitment.gapC_zero
#print axioms Gali.DiscretionCommitment.Commitment.hasSum_of_telescope
#print axioms Gali.DiscretionCommitment.Commitment.PullOut
#print axioms Gali.DiscretionCommitment.Commitment.perfectForesight_pullOut
#print axioms Gali.DiscretionCommitment.Commitment.finiteTree_pullOut
#print axioms Gali.DiscretionCommitment.Commitment.periodLoss
#print axioms Gali.DiscretionCommitment.Commitment.expLoss
#print axioms Gali.DiscretionCommitment.Commitment.Plan
#print axioms Gali.DiscretionCommitment.Commitment.expLoss_hasSum
#print axioms Gali.DiscretionCommitment.Commitment.E0_identity
#print axioms Gali.DiscretionCommitment.Commitment.E0_nonneg
#print axioms Gali.DiscretionCommitment.Commitment.expLoss_sub_hasSum
#print axioms Gali.DiscretionCommitment.Commitment.expLoss_le_of_foc
#print axioms Gali.DiscretionCommitment.Commitment.eq_of_expLoss_eq
#print axioms Gali.DiscretionCommitment.Commitment.cand_foc
#print axioms Gali.DiscretionCommitment.Commitment.commitment_optimal
#print axioms Gali.DiscretionCommitment.Commitment.Det.Feasible
#print axioms Gali.DiscretionCommitment.Commitment.Det.lossTerm
#print axioms Gali.DiscretionCommitment.Commitment.Det.FiniteLoss
#print axioms Gali.DiscretionCommitment.Commitment.Det.loss
#print axioms Gali.DiscretionCommitment.Commitment.Det.IsOptimal
#print axioms Gali.DiscretionCommitment.Commitment.Det.tendsto_disc_sq
#print axioms Gali.DiscretionCommitment.Commitment.Det.loss_sub_hasSum
#print axioms Gali.DiscretionCommitment.Commitment.Det.isOptimal_of_foc
#print axioms Gali.DiscretionCommitment.Commitment.Det.eq_of_loss_eq
#print axioms Gali.DiscretionCommitment.Commitment.Det.lift
#print axioms Gali.DiscretionCommitment.Commitment.Det.pHatD
#print axioms Gali.DiscretionCommitment.Commitment.Det.inflD
#print axioms Gali.DiscretionCommitment.Commitment.Det.gapD
#print axioms Gali.DiscretionCommitment.Commitment.Det.lag_pHatD
#print axioms Gali.DiscretionCommitment.Commitment.Det.pHatD_bounded
#print axioms Gali.DiscretionCommitment.Commitment.Det.candD_feasible
#print axioms Gali.DiscretionCommitment.Commitment.Det.candD_foc
#print axioms Gali.DiscretionCommitment.Commitment.Det.finiteLoss_of_bounded
#print axioms Gali.DiscretionCommitment.Commitment.Det.candD_finiteLoss
#print axioms Gali.DiscretionCommitment.Commitment.Det.candD_isOptimal
#print axioms Gali.DiscretionCommitment.Commitment.Det.isOptimal_iff
#print axioms Gali.DiscretionCommitment.Commitment.Det.existsUnique_optimal
#print axioms Gali.DiscretionCommitment.Commitment.Det.isOptimal_iff_foc
#print axioms Gali.DiscretionCommitment.Commitment.Det.pHatD_eq
#print axioms Gali.DiscretionCommitment.Commitment.targeting_unique
#print axioms Gali.DiscretionCommitment.Commitment.iterated_nkpc
#print axioms Gali.DiscretionCommitment.Commitment.DIS
#print axioms Gali.DiscretionCommitment.Commitment.E_pHat_rho0
#print axioms Gali.DiscretionCommitment.Commitment.dis_iff_rate_rho0
#print axioms Gali.DiscretionCommitment.Commitment.pHat_rho0_sum
#print axioms Gali.DiscretionCommitment.Commitment.Rule.charPoly
#print axioms Gali.DiscretionCommitment.Commitment.Rule.loadY
#print axioms Gali.DiscretionCommitment.Commitment.Rule.eCoef
#print axioms Gali.DiscretionCommitment.Commitment.Rule.mCoef
#print axioms Gali.DiscretionCommitment.Commitment.Rule.fwdA
#print axioms Gali.DiscretionCommitment.Commitment.Rule.loadY_mul
#print axioms Gali.DiscretionCommitment.Commitment.Rule.charPoly_zero
#print axioms Gali.DiscretionCommitment.Commitment.Rule.charPoly_one
#print axioms Gali.DiscretionCommitment.Commitment.Rule.charPoly_neg_one
#print axioms Gali.DiscretionCommitment.Commitment.Rule.continuous_charPoly
#print axioms Gali.DiscretionCommitment.Commitment.Rule.is_coef_zero
#print axioms Gali.DiscretionCommitment.Commitment.Rule.delta_eq
#print axioms Gali.DiscretionCommitment.Commitment.Rule.pc_iff
#print axioms Gali.DiscretionCommitment.Commitment.Rule.is_iff
#print axioms Gali.DiscretionCommitment.Commitment.Rule.fwd_of
#print axioms Gali.DiscretionCommitment.Commitment.Rule.det2_fwdA
#print axioms Gali.DiscretionCommitment.Commitment.Rule.tr2_fwdA
#print axioms Gali.DiscretionCommitment.Commitment.Rule.key_one
#print axioms Gali.DiscretionCommitment.Commitment.Rule.key_neg_one
#print axioms Gali.DiscretionCommitment.Commitment.Rule.schur_fwdA
#print axioms Gali.DiscretionCommitment.Commitment.Rule.exists_root_pos
#print axioms Gali.DiscretionCommitment.Commitment.Rule.stack
#print axioms Gali.DiscretionCommitment.Commitment.Rule.dev_zero
#print axioms Gali.DiscretionCommitment.Commitment.ruleRate
#print axioms Gali.DiscretionCommitment.Commitment.RuleEq
#print axioms Gali.DiscretionCommitment.Commitment.dis_pointwise
#print axioms Gali.DiscretionCommitment.Commitment.rule_implements
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.psiPi
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.psiX
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.inflDisc
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.gapDisc
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.denom_pos
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.disc_targeting
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.disc_nkpc
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.disc_plan
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.disc_unique
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.del_lt_disc_coef
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.commit_coef_lt
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.commitment_le_discretion
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.inflC_zero
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.commitment_lt_discretion
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.impact_inflation
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.impact_gap
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.impact_rho0
#print axioms Gali.DiscretionCommitment.CommitmentVsDiscretion.impulse_rho0
#print axioms Gali.DiscretionCommitment.DistortedSS.periodLoss
#print axioms Gali.DiscretionCommitment.DistortedSS.distLambda
#print axioms Gali.DiscretionCommitment.DistortedSS.markup_distortion_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.distLambda_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.loss_rescale
#print axioms Gali.DiscretionCommitment.DistortedSS.periodLoss_complete_square
#print axioms Gali.DiscretionCommitment.DistortedSS.nkpc_in_xhat
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_period_optimal_iff
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_period_strict
#print axioms Gali.DiscretionCommitment.DistortedSS.DiscretionEqm
#print axioms Gali.DiscretionCommitment.DistortedSS.inflationBias
#print axioms Gali.DiscretionCommitment.DistortedSS.gapBias
#print axioms Gali.DiscretionCommitment.DistortedSS.discInfl
#print axioms Gali.DiscretionCommitment.DistortedSS.discGap
#print axioms Gali.DiscretionCommitment.DistortedSS.one_sub_mul_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_exists
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_forward
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_unique
#print axioms Gali.DiscretionCommitment.DistortedSS.inflationBias_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.gapBias_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.strictMono_inflationBias
#print axioms Gali.DiscretionCommitment.DistortedSS.strictMono_inflationBias_Phi
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.discretion_shock_response_indep
#print axioms Gali.DiscretionCommitment.DistortedSS.gam_lt_one
#print axioms Gali.DiscretionCommitment.DistortedSS.one_sub_del_mul_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.priceLevel
#print axioms Gali.DiscretionCommitment.DistortedSS.infl_eq_priceLevel_sub
#print axioms Gali.DiscretionCommitment.DistortedSS.CommitmentFOC
#print axioms Gali.DiscretionCommitment.DistortedSS.mult_eq_neg_priceLevel
#print axioms Gali.DiscretionCommitment.DistortedSS.priceLevel_adapted
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_eq21
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_core
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_eq22
#print axioms Gali.DiscretionCommitment.DistortedSS.commB
#print axioms Gali.DiscretionCommitment.DistortedSS.commConst
#print axioms Gali.DiscretionCommitment.DistortedSS.backRec
#print axioms Gali.DiscretionCommitment.DistortedSS.backRec_eq_sum
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap
#print axioms Gali.DiscretionCommitment.DistortedSS.commInfl
#print axioms Gali.DiscretionCommitment.DistortedSS.commMult
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice_eq23
#print axioms Gali.DiscretionCommitment.DistortedSS.commB_rel
#print axioms Gali.DiscretionCommitment.DistortedSS.commConst_rel
#print axioms Gali.DiscretionCommitment.DistortedSS.kappa_commConst
#print axioms Gali.DiscretionCommitment.DistortedSS.commB_X
#print axioms Gali.DiscretionCommitment.DistortedSS.commConst_X
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice_adapted
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice_E_succ
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap_mul
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice_bounded
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_exists
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_unique
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_eq23
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_eq24
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap_eq25
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap_eq26_corrected
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap_eq27_corrected
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_eq25_eq27
#print axioms Gali.DiscretionCommitment.DistortedSS.printed_eq26_iff
#print axioms Gali.DiscretionCommitment.DistortedSS.printed_eq27_iff
#print axioms Gali.DiscretionCommitment.DistortedSS.printed_eq27_sum_tendsto
#print axioms Gali.DiscretionCommitment.DistortedSS.del_example
#print axioms Gali.DiscretionCommitment.DistortedSS.printed_eq26_false
#print axioms Gali.DiscretionCommitment.DistortedSS.commPrice_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.commGap_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.commInfl_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.tendsto_priceLevel_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.kappa_limit_priceLevel
#print axioms Gali.DiscretionCommitment.DistortedSS.tendsto_gap_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.tendsto_infl_zeroShock
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_zeroShock_pos
#print axioms Gali.DiscretionCommitment.DistortedSS.commitment_vs_discretion_longrun
#print axioms Gali.DiscretionCommitment.DistortedSS.BddSeq
#print axioms Gali.DiscretionCommitment.DistortedSS.DetFeasible
#print axioms Gali.DiscretionCommitment.DistortedSS.DetFOC
#print axioms Gali.DiscretionCommitment.DistortedSS.detLoss
#print axioms Gali.DiscretionCommitment.DistortedSS.abs_periodLoss_le
#print axioms Gali.DiscretionCommitment.DistortedSS.summable_disc
#print axioms Gali.DiscretionCommitment.DistortedSS.detLoss_summable
#print axioms Gali.DiscretionCommitment.DistortedSS.lagrangian_identity
#print axioms Gali.DiscretionCommitment.DistortedSS.lagrangian_sufficiency
#print axioms Gali.DiscretionCommitment.DistortedSS.det_commitment_exists
#print axioms Gali.DiscretionCommitment.DistortedSS.det_optimal_iff
#print axioms Gali.DiscretionCommitment.DistortedSS.det_commitment_optimal
#print axioms Gali.DiscretionCommitment.DistortedSS.zero_path_not_optimal
#print axioms Gali.DiscretionCommitment.DistortedSS.det_zeroShock_optimal
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.natRate
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.natRate_of_le
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.natRate_of_lt
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.NKPC
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.DIS
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.impliedRate
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.dis_iff
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.firstBest_rate
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.firstBest_violates_zlb
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.firstBest_eqm_of_nonneg
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.PeriodFeasible
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.PeriodOptimal
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.PeriodKKT
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.period_loss_change
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodKKT_sufficient
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodKKT_necessary
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodOptimal_iff_kkt
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodSol
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodOptimal_iff_sol
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodOptimal_exists
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodOptimal_unique
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.ups0
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.ups1
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.impliedRate_eq
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.nkpc_iff_eq31
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlb_iff_le_ups1
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.periodKKT_iff_book
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.eq33
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.DiscEq
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.DiscEq.nkpc_zlb
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.binding_optimal
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.slack_zero_optimal
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.backStep
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.backState
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.Amat
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.Bvec
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.eq34_matrix
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.eq34_iff
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.Amat_pos
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.Bvec_pos
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.backStep_neg
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.backState_nonpos
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.backState_neg
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlbPath
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlbPath_of_le
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlbPath_of_lt
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlbPath_neg
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.zlbPath_binding
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.discX
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.discPi
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.discI
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.disc_exists
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.down_induction
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.disc_unique
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflGap
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflPath
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflI
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflation_discEq
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflation_bounded
#print axioms Gali.DiscretionCommitment.ZLBDiscretion.deflation_ne_disc
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Feasible
#print axioms Gali.DiscretionCommitment.ZLBCommitment.feasible_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lossTerm
#print axioms Gali.DiscretionCommitment.ZLBCommitment.loss
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lossTerm_nonneg
#print axioms Gali.DiscretionCommitment.ZLBCommitment.loss_partial_tendsto_top
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Optimal
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lag
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lag_succ
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lag_zero
#print axioms Gali.DiscretionCommitment.ZLBCommitment.FOC35
#print axioms Gali.DiscretionCommitment.ZLBCommitment.FOC36
#print axioms Gali.DiscretionCommitment.ZLBCommitment.KKT
#print axioms Gali.DiscretionCommitment.ZLBCommitment.lagrangian_identity
#print axioms Gali.DiscretionCommitment.ZLBCommitment.tendsto_pow_mul_abs
#print axioms Gali.DiscretionCommitment.ZLBCommitment.kkt_sufficient
#print axioms Gali.DiscretionCommitment.ZLBCommitment.kkt_optimal
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq_zero_of_tsum_nonpos
#print axioms Gali.DiscretionCommitment.ZLBCommitment.sq_terms_zero
#print axioms Gali.DiscretionCommitment.ZLBCommitment.kkt_unique
#print axioms Gali.DiscretionCommitment.ZLBCommitment.optimal_unique
#print axioms Gali.DiscretionCommitment.ZLBCommitment.postX
#print axioms Gali.DiscretionCommitment.ZLBCommitment.postPi
#print axioms Gali.DiscretionCommitment.ZLBCommitment.postXi
#print axioms Gali.DiscretionCommitment.ZLBCommitment.postP
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq37
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq38
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq39
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_priceLevel
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq40
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_second_order
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq41
#print axioms Gali.DiscretionCommitment.ZLBCommitment.postP_second_order
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq40_closed
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq42_pos
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_eq43_pos
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_tendsto_zero
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_unique_bounded
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Eq44
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Eq45
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Eq46
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Nmat
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Kmat
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Mmat
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Nmat_det
#print axioms Gali.DiscretionCommitment.ZLBCommitment.liftoff_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Nmat_mulVec
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Kmat_mulVec
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq47_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq47
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq48_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq49_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq49_matrix
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Hmat
#print axioms Gali.DiscretionCommitment.ZLBCommitment.Jmat
#print axioms Gali.DiscretionCommitment.ZLBCommitment.eq50_iff
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_rate
#print axioms Gali.DiscretionCommitment.ZLBCommitment.post_rate_nonneg
#print axioms Gali.DiscretionCommitment.ZLBCommitment.backStep_nkpc_rate
#print axioms Gali.DiscretionCommitment.ZLBCommitment.algorithm_eq47
#print axioms Gali.DiscretionCommitment.ZLBCommitment.algorithm_verification
#print axioms Gali.DiscretionCommitment.ZLBCommitment.equation_count
#print axioms Gali.DiscretionCommitment.Ex5_1.DIS
#print axioms Gali.DiscretionCommitment.Ex5_1.NKPC
#print axioms Gali.DiscretionCommitment.Ex5_1.TaylorRule
#print axioms Gali.DiscretionCommitment.Ex5_1.Equilibrium
#print axioms Gali.DiscretionCommitment.Ex5_1.HomEq
#print axioms Gali.DiscretionCommitment.Ex5_1.stack
#print axioms Gali.DiscretionCommitment.Ex5_1.A
#print axioms Gali.DiscretionCommitment.Ex5_1.tr2_A
#print axioms Gali.DiscretionCommitment.Ex5_1.det2_A
#print axioms Gali.DiscretionCommitment.Ex5_1.schurStable_A_iff
#print axioms Gali.DiscretionCommitment.Ex5_1.homEq_iff_solves
#print axioms Gali.DiscretionCommitment.Ex5_1.xs
#print axioms Gali.DiscretionCommitment.Ex5_1.ps
#print axioms Gali.DiscretionCommitment.Ex5_1.rate
#print axioms Gali.DiscretionCommitment.Ex5_1.bounded_comb
#print axioms Gali.DiscretionCommitment.Ex5_1.bounded_sub
#print axioms Gali.DiscretionCommitment.Ex5_1.adapted_comb
#print axioms Gali.DiscretionCommitment.Ex5_1.msv_equilibrium
#print axioms Gali.DiscretionCommitment.Ex5_1.equilibrium_sub
#print axioms Gali.DiscretionCommitment.Ex5_1.equilibrium_add_hom
#print axioms Gali.DiscretionCommitment.Ex5_1.boundedVec_stack
#print axioms Gali.DiscretionCommitment.Ex5_1.adaptedVec_stack
#print axioms Gali.DiscretionCommitment.Ex5_1.msv_adapted
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1a_unique
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1a_unique_bounded
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1a_not_unique
#print axioms Gali.DiscretionCommitment.Ex5_1.bilin_quad
#print axioms Gali.DiscretionCommitment.Ex5_1.lossFn
#print axioms Gali.DiscretionCommitment.Ex5_1.lossC
#print axioms Gali.DiscretionCommitment.Ex5_1.lossMin
#print axioms Gali.DiscretionCommitment.Ex5_1.phiStar
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1b_loss_eq
#print axioms Gali.DiscretionCommitment.Ex5_1.lossFn_eq
#print axioms Gali.DiscretionCommitment.Ex5_1.lossC_pos
#print axioms Gali.DiscretionCommitment.Ex5_1.phiStar_pos
#print axioms Gali.DiscretionCommitment.Ex5_1.phiStar_foc
#print axioms Gali.DiscretionCommitment.Ex5_1.lossFn_ge
#print axioms Gali.DiscretionCommitment.Ex5_1.lossFn_phiStar
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1b_optimal
#print axioms Gali.DiscretionCommitment.Ex5_1.lossFn_strictMonoOn
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1b_corner
#print axioms Gali.DiscretionCommitment.Ex5_1.ex5_1b_equilibrium_optimal
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR
#print axioms Gali.DiscretionCommitment.Ex5_1.phiStar_eq_phiR
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR_eq
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR_strictAntiOn_weight
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR_strictMono_ratio
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR_strictMono_sigma
#print axioms Gali.DiscretionCommitment.Ex5_1.phiR_strictMonoOn_kappa
#print axioms Gali.DiscretionCommitment.Ex5_1.tendsto_phiR_weight_zero
#print axioms Gali.DiscretionCommitment.Ex5_1.tendsto_phiR_ratio_atTop
#print axioms Gali.DiscretionCommitment.Ex5_1.tendsto_phiR_weight_atTop
#print axioms Gali.DiscretionCommitment.Ex5_1.tendsto_phiR_ratio_zero
#print axioms Gali.DiscretionCommitment.Ex5_2.NKPC
#print axioms Gali.DiscretionCommitment.Ex5_2.lossTerm
#print axioms Gali.DiscretionCommitment.Ex5_2.loss
#print axioms Gali.DiscretionCommitment.Ex5_2.shockWeight
#print axioms Gali.DiscretionCommitment.Ex5_2.markov
#print axioms Gali.DiscretionCommitment.Ex5_2.E_nonneg
#print axioms Gali.DiscretionCommitment.Ex5_2.loss_summable
#print axioms Gali.DiscretionCommitment.Ex5_2.shockWeight_summable
#print axioms Gali.DiscretionCommitment.Ex5_2.shockWeight_pos
#print axioms Gali.DiscretionCommitment.Ex5_2.loss_markov
#print axioms Gali.DiscretionCommitment.Ex5_2.markov_nkpc_iff
#print axioms Gali.DiscretionCommitment.Ex5_2.markov_feasible
#print axioms Gali.DiscretionCommitment.Ex5_2.markov_feasible_iff
#print axioms Gali.DiscretionCommitment.Ex5_2.delta2
#print axioms Gali.DiscretionCommitment.Ex5_2.psiP
#print axioms Gali.DiscretionCommitment.Ex5_2.psiX
#print axioms Gali.DiscretionCommitment.Ex5_2.objective
#print axioms Gali.DiscretionCommitment.Ex5_2.delta2_pos
#print axioms Gali.DiscretionCommitment.Ex5_2.psi_feasible
#print axioms Gali.DiscretionCommitment.Ex5_2.objective_eq
#print axioms Gali.DiscretionCommitment.Ex5_2.objective_opt
#print axioms Gali.DiscretionCommitment.Ex5_2.ex5_2a
#print axioms Gali.DiscretionCommitment.Ex5_2.deltaD
#print axioms Gali.DiscretionCommitment.Ex5_2.discP
#print axioms Gali.DiscretionCommitment.Ex5_2.discX
#print axioms Gali.DiscretionCommitment.Ex5_2.beta_rho_lt_one
#print axioms Gali.DiscretionCommitment.Ex5_2.deltaD_pos
#print axioms Gali.DiscretionCommitment.Ex5_2.disc_targeting
#print axioms Gali.DiscretionCommitment.Ex5_2.disc_feasible
#print axioms Gali.DiscretionCommitment.Ex5_2.discretion_unique
#print axioms Gali.DiscretionCommitment.Ex5_2.ex5_2b_objective
#print axioms Gali.DiscretionCommitment.Ex5_2.ex5_2b
#print axioms Gali.DiscretionCommitment.Ex5_2.CommitFeasible
#print axioms Gali.DiscretionCommitment.Ex5_2.loss_eq_of_eq_after
#print axioms Gali.DiscretionCommitment.Ex5_2.markov_bounded
#print axioms Gali.DiscretionCommitment.Ex5_2.markov_adapted
#print axioms Gali.DiscretionCommitment.Ex5_2.bounded_add_smul
#print axioms Gali.DiscretionCommitment.Ex5_2.E_u0
#print axioms Gali.DiscretionCommitment.Ex5_2.adapted_add_smul
#print axioms Gali.DiscretionCommitment.Ex5_2.E0_sq_smul
#print axioms Gali.DiscretionCommitment.Ex5_2.improve_date0
#print axioms Gali.DiscretionCommitment.Ex5_2.improve_date1
#print axioms Gali.DiscretionCommitment.Ex5_2.coef_opt
#print axioms Gali.DiscretionCommitment.Ex5_2.ex5_2c
#print axioms Gali.DiscretionCommitment.Ex5_2.ex5_2c_commitment
#print axioms Gali.DiscretionCommitment.Ex5_3.lag
#print axioms Gali.DiscretionCommitment.Ex5_3.Feasible
#print axioms Gali.DiscretionCommitment.Ex5_3.HomFeasible
#print axioms Gali.DiscretionCommitment.Ex5_3.Bdd
#print axioms Gali.DiscretionCommitment.Ex5_3.lossTerm
#print axioms Gali.DiscretionCommitment.Ex5_3.loss
#print axioms Gali.DiscretionCommitment.Ex5_3.Optimal
#print axioms Gali.DiscretionCommitment.Ex5_3.FOC
#print axioms Gali.DiscretionCommitment.Ex5_3.resid
#print axioms Gali.DiscretionCommitment.Ex5_3.cross
#print axioms Gali.DiscretionCommitment.Ex5_3.partial_sum_identity
#print axioms Gali.DiscretionCommitment.Ex5_3.bdd_lag
#print axioms Gali.DiscretionCommitment.Ex5_3.bdd_lin
#print axioms Gali.DiscretionCommitment.Ex5_3.bdd_shift
#print axioms Gali.DiscretionCommitment.Ex5_3.loss_summable
#print axioms Gali.DiscretionCommitment.Ex5_3.cross_summable
#print axioms Gali.DiscretionCommitment.Ex5_3.hom_of_feasible
#print axioms Gali.DiscretionCommitment.Ex5_3.feasible_add
#print axioms Gali.DiscretionCommitment.Ex5_3.lossTerm_add
#print axioms Gali.DiscretionCommitment.Ex5_3.multipliers_bdd
#print axioms Gali.DiscretionCommitment.Ex5_3.ex5_3a_sufficient
#print axioms Gali.DiscretionCommitment.Ex5_3.dirP
#print axioms Gali.DiscretionCommitment.Ex5_3.dirY
#print axioms Gali.DiscretionCommitment.Ex5_3.dirI
#print axioms Gali.DiscretionCommitment.Ex5_3.dir_hom
#print axioms Gali.DiscretionCommitment.Ex5_3.dir_bdd
#print axioms Gali.DiscretionCommitment.Ex5_3.dir_zero_after
#print axioms Gali.DiscretionCommitment.Ex5_3.loss_eq_of_eq_after
#print axioms Gali.DiscretionCommitment.Ex5_3.eq_zero_of_quadratic
#print axioms Gali.DiscretionCommitment.Ex5_3.xi2
#print axioms Gali.DiscretionCommitment.Ex5_3.xi1
#print axioms Gali.DiscretionCommitment.Ex5_3.ex5_3a_necessary
#print axioms Gali.DiscretionCommitment.Ex5_3.ex5_3a_optimal_iff
#print axioms Gali.DiscretionCommitment.Ex5_3.Rule
#print axioms Gali.DiscretionCommitment.Ex5_3.lag_mul
#print axioms Gali.DiscretionCommitment.Ex5_3.lag_yfoc
#print axioms Gali.DiscretionCommitment.Ex5_3.ex5_3b_rule_iff
#print axioms Gali.DiscretionCommitment.Ex5_3.ex5_3b
#print axioms Gali.DiscretionCommitment.Ex5_4.periodOpt
#print axioms Gali.DiscretionCommitment.Ex5_4.period_loss_eq
#print axioms Gali.DiscretionCommitment.Ex5_4.period_opt_iff
#print axioms Gali.DiscretionCommitment.Ex5_4.period_targeting_iff
#print axioms Gali.DiscretionCommitment.Ex5_4.period_foc_alt
#print axioms Gali.DiscretionCommitment.Ex5_4.prev
#print axioms Gali.DiscretionCommitment.Ex5_4.tilde
#print axioms Gali.DiscretionCommitment.Ex5_4.NKPCInd
#print axioms Gali.DiscretionCommitment.Ex5_4.DiscretionEq
#print axioms Gali.DiscretionCommitment.Ex5_4.tilde_succ
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4a_period_optimal
#print axioms Gali.DiscretionCommitment.Ex5_4.beta_rho_lt_one
#print axioms Gali.DiscretionCommitment.Ex5_4.psiD
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4a_unique
#print axioms Gali.DiscretionCommitment.Ex5_4.discInfl
#print axioms Gali.DiscretionCommitment.Ex5_4.tilde_discInfl
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4a_exists
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4a_inflation
#print axioms Gali.DiscretionCommitment.Ex5_4.CFeasible
#print axioms Gali.DiscretionCommitment.Ex5_4.lossTerm
#print axioms Gali.DiscretionCommitment.Ex5_4.loss
#print axioms Gali.DiscretionCommitment.Ex5_4.COptimal
#print axioms Gali.DiscretionCommitment.Ex5_4.CFOC
#print axioms Gali.DiscretionCommitment.Ex5_4.cross
#print axioms Gali.DiscretionCommitment.Ex5_4.partial_sum_identity
#print axioms Gali.DiscretionCommitment.Ex5_4.loss_summable
#print axioms Gali.DiscretionCommitment.Ex5_4.cross_summable
#print axioms Gali.DiscretionCommitment.Ex5_4.loss_eq_of_eq_after
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4b_sufficient
#print axioms Gali.DiscretionCommitment.Ex5_4.dirQ
#print axioms Gali.DiscretionCommitment.Ex5_4.dirX
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4b_necessary
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4b_optimal_iff
#print axioms Gali.DiscretionCommitment.Ex5_4.cumsum
#print axioms Gali.DiscretionCommitment.Ex5_4.foc_iff_level_rule
#print axioms Gali.DiscretionCommitment.Ex5_4.level_rule_iff_diff
#print axioms Gali.DiscretionCommitment.Ex5_4.cumsum_tilde_eq
#print axioms Gali.DiscretionCommitment.Ex5_4.ex5_4b
#print axioms Gali.DiscretionCommitment.Ex5_5.Phi
#print axioms Gali.DiscretionCommitment.Ex5_5.phi_continuous
#print axioms Gali.DiscretionCommitment.Ex5_5.phi_strictMono
#print axioms Gali.DiscretionCommitment.Ex5_5.exists_quantile
#print axioms Gali.DiscretionCommitment.Ex5_5.z05
#print axioms Gali.DiscretionCommitment.Ex5_5.phi_z05
#print axioms Gali.DiscretionCommitment.Ex5_5.eq_z05_iff
#print axioms Gali.DiscretionCommitment.Ex5_5.hasLaw_affine
#print axioms Gali.DiscretionCommitment.Ex5_5.prob_neg
#print axioms Gali.DiscretionCommitment.Ex5_5.NKPCbar
#print axioms Gali.DiscretionCommitment.Ex5_5.Targeting
#print axioms Gali.DiscretionCommitment.Ex5_5.DiscEq
#print axioms Gali.DiscretionCommitment.Ex5_5.xT
#print axioms Gali.DiscretionCommitment.Ex5_5.pT
#print axioms Gali.DiscretionCommitment.Ex5_5.iT
#print axioms Gali.DiscretionCommitment.Ex5_5.E_targets
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a_exists
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a_period_optimal
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a_unique
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a_loss_diff
#print axioms Gali.DiscretionCommitment.Ex5_5.RuleB
#print axioms Gali.DiscretionCommitment.Ex5_5.psiU
#print axioms Gali.DiscretionCommitment.Ex5_5.EqB
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5b_exists
#print axioms Gali.DiscretionCommitment.Ex5_5.eqB_sub
#print axioms Gali.DiscretionCommitment.Ex5_5.eqB_add_hom
#print axioms Gali.DiscretionCommitment.Ex5_5.targets_adapted
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5b_unique
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5b_not_unique
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.mk
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.z
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.u
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.vz
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.vu
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.lawZ
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.lawU
#print axioms Gali.DiscretionCommitment.Ex5_5.GaussianShocks.indep
#print axioms Gali.DiscretionCommitment.Ex5_5.rateVar
#print axioms Gali.DiscretionCommitment.Ex5_5.rateSd
#print axioms Gali.DiscretionCommitment.Ex5_5.piStar
#print axioms Gali.DiscretionCommitment.Ex5_5.hasLaw_rate
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a_prob
#print axioms Gali.DiscretionCommitment.Ex5_5.rateSd_pos
#print axioms Gali.DiscretionCommitment.Ex5_5.constraint_iff
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5a
#print axioms Gali.DiscretionCommitment.Ex5_5.trunc
#print axioms Gali.DiscretionCommitment.Ex5_5.trunc_trunc
#print axioms Gali.DiscretionCommitment.Ex5_5.truncE
#print axioms Gali.DiscretionCommitment.Ex5_5.shockMeasure
#print axioms Gali.DiscretionCommitment.Ex5_5.hasLaw_pair
#print axioms Gali.DiscretionCommitment.Ex5_5.hasLaw_z
#print axioms Gali.DiscretionCommitment.Ex5_5.hasLaw_u
#print axioms Gali.DiscretionCommitment.Ex5_5.concreteShocks
#print axioms Gali.DiscretionCommitment.Ex5_5.concrete_iid
#print axioms Gali.DiscretionCommitment.Ex5_5.rateVar_ne_zero
#print axioms Gali.DiscretionCommitment.Ex5_5.ex5_5_nonvacuous
