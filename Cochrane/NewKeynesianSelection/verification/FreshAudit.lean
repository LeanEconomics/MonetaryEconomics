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
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
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
  with the explicit bound `abs_pow_entry_le`;
* `exists_bounded_homogeneous`: without it, the homogeneous recursion
  `x_t = A x_{t+1}` has a bounded solution that is not identically zero.

The roots are written explicitly through the discriminant, so no spectral
theory is needed: powers of `A` are controlled through the Cayley–Hamilton
recursion `A^{k+2} = p_{k+1} A − D p_k I` and the identity
`p_k = ∑_{j ≤ k} r₁ʲ r₂^{k−j}`.

Restated from the `Woodford/ReturnOfMonetaryRules` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Cochrane.NewKeynesianSelection

open Filter Topology

/-- The Schur–Cohn condition for a real quadratic `z² − T z + D`: both roots
lie strictly inside the unit circle (Woodford, Prop. C.1, p. 670). -/
def SchurStable (T D : ℝ) : Prop := |D| < 1 ∧ |T| < 1 + D

/-- The discriminant `T² − 4D` of `z² − T z + D`. -/
def discQ (T D : ℝ) : ℝ := T ^ 2 - 4 * D

/-- The first root of `z² − T z + D`. -/
noncomputable def root₁ (T D : ℝ) : ℂ :=
  if 0 ≤ discQ T D then ((T + Real.sqrt (discQ T D)) / 2 : ℝ)
  else ⟨T / 2, Real.sqrt (-discQ T D) / 2⟩

/-- The second root of `z² − T z + D`. -/
noncomputable def root₂ (T D : ℝ) : ℂ :=
  if 0 ≤ discQ T D then ((T - Real.sqrt (discQ T D)) / 2 : ℝ)
  else ⟨T / 2, -(Real.sqrt (-discQ T D) / 2)⟩

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
    have hd : discQ T D = T ^ 2 - 4 * D := rfl
    nlinarith [hs]
  · have h' : 0 ≤ -discQ T D := by linarith [not_le.mp h]
    have hs := Real.sq_sqrt h'
    have hd : discQ T D = T ^ 2 - 4 * D := rfl
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
theorem normSq_root_of_neg {T D : ℝ} (h : discQ T D < 0) :
    ‖root₁ T D‖ ^ 2 = D ∧ ‖root₂ T D‖ ^ 2 = D := by
  have h' : 0 ≤ -discQ T D := by linarith
  have hs := Real.sq_sqrt h'
  have hd : discQ T D = T ^ 2 - 4 * D := rfl
  have hn : ¬ 0 ≤ discQ T D := not_le.mpr h
  unfold root₁ root₂
  simp only [hn, ↓reduceIte, Complex.sq_norm, Complex.normSq_mk]
  constructor <;> nlinarith [hs]

/-- In the real case the roots are the real numbers `(T ± √(T² − 4D))/2`. -/
theorem norm_root_of_nonneg {T D : ℝ} (h : 0 ≤ discQ T D) :
    ‖root₁ T D‖ = |(T + Real.sqrt (discQ T D)) / 2| ∧
      ‖root₂ T D‖ = |(T - Real.sqrt (discQ T D)) / 2| := by
  unfold root₁ root₂
  refine ⟨?_, ?_⟩ <;> simp only [h, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]

/-- **Schur–Cohn for quadratics** (Woodford, Prop. C.1, p. 670): both roots of
`z² − T z + D` lie strictly inside the unit circle iff `|D| < 1` and
`|T| < 1 + D`. -/
theorem schurStable_iff_roots (T D : ℝ) :
    SchurStable T D ↔ ‖root₁ T D‖ < 1 ∧ ‖root₂ T D‖ < 1 := by
  unfold SchurStable
  by_cases h : 0 ≤ discQ T D
  · obtain ⟨h1, h2⟩ := norm_root_of_nonneg h
    rw [h1, h2]
    set s := Real.sqrt (discQ T D) with hs_def
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
  · have hneg : discQ T D < 0 := not_le.mp h
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    unfold discQ at hneg
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

end Cochrane.NewKeynesianSelection

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
* `PullOut`: the pull-out property, true for perfect foresight
  (`perfectForesight_pullOut`) and for finite event trees.
* `determinate_iff`: determinacy (uniqueness of bounded adapted solutions) is
  equivalent to the Schur–Cohn condition on `A` (Galí, p. 65; Blanchard and
  Kahn 1980).

Restated from the `Woodford/ReturnOfMonetaryRules` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Cochrane.NewKeynesianSelection

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

/-- The forward series of a bounded process is adapted: `E_t` leaves
`∑ aᵏ E_t u_{t+k}` unchanged (Galí, p. 130; restated from the Chapter 5 project). -/
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

/-- The pull-out property `E_t (a y) = a E_t y` for `a` known at `t` (Galí, p. 134). It holds
for true conditional expectations (`perfectForesight_pullOut`, and every finite event tree,
`ExpectationsFiniteTree.finiteTree_pullOut`) but is not implied by the `ExpectationSystem`
fields, so results that use it take it as a hypothesis (restated from the Chapter 5 project). -/
def PullOut : Prop := ∀ t (a y : Ω → ℝ), 𝔼.E t a = a → 𝔼.E t (a * y) = a * 𝔼.E t y

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

/-- Perfect foresight has the pull-out property (Galí, p. 134). -/
theorem perfectForesight_pullOut : perfectForesight.PullOut := fun _ _ _ _ => rfl

end Cochrane.NewKeynesianSelection

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

Restated from the `Woodford/ReturnOfMonetaryRules` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Cochrane.NewKeynesianSelection.ExpectationsFiniteTree

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

/-- The cell-average expectations of a finite event tree have the pull-out property, so the
`PullOut` hypothesis is satisfiable under genuine uncertainty (Galí, p. 134; restated from the
Chapter 5 project). -/
theorem finiteTree_pullOut {Ω' : Type*} [Fintype Ω'] (T : FiniteTree Ω') :
    T.toExpectationSystem.PullOut := by
  classical
  intro t a y ha
  rw [FiniteTree.toExpectationSystem_E] at ha ⊢
  rw [FiniteTree.toExpectationSystem_E]
  funext ω
  have hcell : ∀ ω', T.info t ω' ω → a ω' = a ω := fun ω' h => by
    rw [← ha, T.condE_congr a h]
  simp only [FiniteTree.condE, FiniteTree.num, Pi.mul_apply]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  by_cases h : T.info t ω' ω
  · simp only [h, ↓reduceIte, hcell ω' h]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

end Cochrane.NewKeynesianSelection.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The forward solution of `z_t = a E_t z_{t+1} + u_t`

Restated from the Woodford Chapter 2 and 3 projects.
Woodford (2003), *Interest and Prices*, Appendix A, §A.4, eqs. (A.14)–(A.17), pp. 636–637, and
§A.10, p. 643 (the predetermined-variable variant used for Proposition 2.10).

The scalar expectational difference equation (A.14) `z_t = a E_t z_{t+1} + u_t` recurs throughout
Chapter 2. This module proves everything Appendix A states about it, for an arbitrary
`ExpectationSystem` (so under perfect foresight and under genuine uncertainty), with genuine
infinite sums.

## Main results

* `iterate_A15`: (A.15) `z_t = aᵏ E_t z_{t+k} + ∑_{j<k} aʲ E_t u_{t+j}`;
  `tendsto_partial_A16`: for `|a| < 1` and bounded `z` the partial sums converge to `z_t` (the
  book's proof of (A.16)); `eq_forwardSeries_abs`: hence `z_t = ∑ aʲ E_t u_{t+j}`.
* `forwardSeries_solves_abs`, `forwardSeries_bounded_abs`, `forwardSeries_adapted_abs`,
  `existsUnique_bounded`: for `|a| < 1` (including negative `a`) and bounded adapted `u`, (A.16)
  is the unique bounded solution.
* `sunspotFamily` (A.17), `sunspotFamily_solves`, `sunspotFamily_bounded`,
  `eq_sunspotFamily`: for `|a| > 1` the recursion (A.17) driven by any martingale difference
  `ν` is a bounded solution, and every adapted solution is of this form.
* `bounded_solutions_not_countable`: for `|a| ≥ 1`, if one bounded solution exists there are
  uncountably many; `existsUnique_iff`: `|a| < 1` is necessary and sufficient for a unique
  bounded solution for every bounded adapted `u`.
* The case `|a| = 1` (survey error E12): the printed recursion
  `z_t = z̄_t + (z_{t-1} − z̄_{t-1}) + ν_t` is valid for `a = 1` (`printed_A17_one_solves`) but
  not for `a = −1` (`printed_A17_fails_neg_one`); the correct recursion is
  `d_t = a⁻¹ d_{t-1} + ν_t` (`unit_sunspot_solves`, bounded when `ν` vanishes after a date,
  `unit_sunspot_bounded`). The forward sum must be `∑ aʲ E_t u_{t+j}`
  (`forwardSeries_solves_of_decay`, e.g. a mean-zero AR(1) `u`, `ar1_decay`). For `a = −1`
  (and `a = 1`) a bounded solution need NOT exist (`no_bounded_solution_unit`, forcing
  `u_t = c aᵗ`, `c ≠ 0`); when one exists there are uncountably many, so the solution is never
  unique.
* `solves_iff_forwardSeries`, `predetermined_restriction` (§A.10): for `|a| < 1` a bounded
  process (adapted or predetermined) satisfies (A.14) iff it equals (A.16).
* The undivided form `A z_t = B E_t z_{t+1} + f_t` (survey L1, used by every later module):
  `ScalarEq`, `scalarSol`, `scalarSol_apply`, `scalarEq_iff`, `scalarEq_one_iff`,
  `scalar_existsUnique`, `scalar_homog`, `scalar_determinate_iff` (exactly one bounded solution
  for every bounded adapted `f` iff `|B| < |A|`, covering `A = 0`); `existsUnique_iff` is its
  case `A = 1`.
* Survey lemma L2: `hasSum_geometric_ratio`, `tsum_geometric_ratio`
  (`∑ c Bʲ/A^{j+1} = c/(A − B)`), the summation by parts `summable_geom_mul`, `abel_tsum`
  (any `|q| < 1`) and its `q ≥ 0` weighted form `tsum_weights_by_parts`; survey lemma L4:
  `abs_lt_abs_of_sub_pos_add_pos`, `abs_lt_abs_iff_of_add_pos`.
* `E_tsum_dom` (Woodford (2003), App. B.3 and B.7; added for the Chapter 3 modules): `E_t`
  commutes with a series of random variables dominated by a summable sequence.
-/

namespace Cochrane.NewKeynesianSelection.ForwardSolution

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (A.14), p. 636: `z` solves `z_t = a E_t z_{t+1} + u_t` at every date. -/
def Solves (a : ℝ) (u z : ℕ → Ω → ℝ) : Prop := ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t

/-- Woodford (2003), App. A, p. 636: a variable known at date `s` is known at every later
date `t`. -/
theorem E_of_known {s t : ℕ} (hst : s ≤ t) {x : Ω → ℝ} (hx : 𝔼.E s x = x) : 𝔼.E t x = x := by
  rw [← hx, 𝔼.known hst]

/-- Woodford (2003), eq. (A.14), p. 636: a solution of (A.14) with adapted forcing is adapted. -/
theorem solves_adapted {a : ℝ} {u z : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) (hz : Solves 𝔼 a u z) :
    𝔼.Adapted z := by
  intro t
  conv_lhs => rw [hz t]
  rw [map_add, map_smul, 𝔼.E_E_self, hua t, ← hz t]

/-- Woodford (2003), eq. (A.15), p. 636: iterating (A.14),
`z_t = aᵏ E_t z_{t+k} + ∑_{j<k} aʲ E_t u_{t+j}`. -/
theorem iterate_A15 {a : ℝ} {u z : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) (hz : Solves 𝔼 a u z)
    (t k : ℕ) :
    z t = a ^ k • 𝔼.E t (z (t + k)) + ∑ j ∈ Finset.range k, a ^ j • 𝔼.E t (u (t + j)) := by
  induction k with
  | zero =>
    simp only [pow_zero, one_smul, add_zero, Finset.range_zero, Finset.sum_empty]
    exact (solves_adapted 𝔼 hua hz t).symm
  | succ k ih =>
    have h := congrArg (𝔼.E t) (hz (t + k))
    rw [map_add, map_smul, 𝔼.tower (Nat.le_add_right t k)] at h
    rw [ih, h, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ, ← add_assoc t k 1]
    abel

/-- Woodford (2003), eq. (A.16), p. 636 (the book's proof): for `|a| < 1` and a bounded
solution `z`, the partial sums `∑_{j<k} aʲ E_t u_{t+j}` converge to `z_t`, because
`aᵏ E_t z_{t+k} → 0`. -/
theorem tendsto_partial_A16 {a : ℝ} (ha : |a| < 1) {u z : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (hz : Solves 𝔼 a u z) (hzb : BoundedProc z) (t : ℕ) (ω : Ω) :
    Tendsto (fun k => ∑ j ∈ Finset.range k, a ^ j * 𝔼.E t (u (t + j)) ω) atTop
      (𝓝 (z t ω)) := by
  obtain ⟨M, hM⟩ := hzb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (a := fun k => |a| ^ k * M) (fun k => ?_) ?_
  · have h := congrFun (iterate_A15 𝔼 hua hz t k) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
    have he : z t ω - ∑ j ∈ Finset.range k, a ^ j * 𝔼.E t (u (t + j)) ω =
        a ^ k * 𝔼.E t (z (t + k)) ω := by linarith
    rw [he, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + k)) t ω) (pow_nonneg (abs_nonneg a) k)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const M

/-- Woodford (2003), App. A, p. 636: the terms of (A.16) are absolutely summable for bounded
forcing and `|a| < 1`. -/
theorem summable_A16 {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (t : ℕ) (ω : Ω) : Summable (fun k => a ^ k * 𝔼.E t (u (t + k)) ω) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω)
        (pow_nonneg (abs_nonneg a) k))

/-- Woodford (2003), eq. (A.16), p. 636: every bounded solution of (A.14) with `|a| < 1` and
bounded adapted forcing is the forward sum `z_t = ∑ aʲ E_t u_{t+j}` (proved by the book's route,
the limit of (A.15)). -/
theorem eq_forwardSeries_abs {a M : ℝ} (ha : |a| < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (hz : Solves 𝔼 a u z)
    (hzb : BoundedProc z) : z = 𝔼.forwardSeries a u := by
  funext t ω
  exact tendsto_nhds_unique (tendsto_partial_A16 𝔼 ha hua hz hzb t ω)
    (summable_A16 𝔼 ha hu t ω).hasSum.tendsto_sum_nat

/-- Woodford (2003), eq. (A.16), p. 636 (existence, any `|a| < 1`, restated from the Woodford
Chapter 1 project): the forward sum solves (A.14) for bounded adapted `u`. -/
theorem forwardSeries_solves_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) : Solves 𝔼 a u (𝔼.forwardSeries a u) := by
  intro t
  have ha0 : 0 ≤ |a| := abs_nonneg a
  funext ω
  have hE : 𝔼.E t (𝔼.forwardSeries a u (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
    have hb : ∀ k ω', |a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ |a| ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω')
        (pow_nonneg ha0 k)
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum ha0 ha hb t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [hE, (summable_A16 𝔼 ha hu t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hadapt t,
    ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), eq. (A.16), p. 636 (restated from the Woodford Chapter 1 project): the
forward sum of a process bounded by `M` is bounded by `M/(1 − |a|)`. -/
theorem forwardSeries_bounded_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (𝔼.forwardSeries a u) := by
  refine ⟨M / (1 - |a|), fun t ω => ?_⟩
  have hg : HasSum (fun k : ℕ => M * |a| ^ k) (M / (1 - |a|)) := by
    have := (hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun k => a ^ k * 𝔼.E t (u (t + k)) ω) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg (abs_nonneg a) k)
  simpa [ExpectationSystem.forwardSeries, Real.norm_eq_abs] using this

/-- Woodford (2003), eq. (A.16), p. 636: the forward sum is adapted (any `|a| < 1`). -/
theorem forwardSeries_adapted_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ |a| ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg (abs_nonneg a) k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω =
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [𝔼.E_tsum (abs_nonneg a) ha hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, 𝔼.E_E_self]
  rfl

/-- Woodford (2003), App. A, p. 636 ("any expectational difference equation of the form (A.14)
has a unique bounded solution … in the case that `|a| < 1`"): existence and uniqueness. -/
theorem existsUnique_bounded {a : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ} (hub : BoundedProc u)
    (hua : 𝔼.Adapted u) : ∃! z, BoundedProc z ∧ Solves 𝔼 a u z := by
  obtain ⟨M, hM⟩ := hub
  exact ⟨_, ⟨forwardSeries_bounded_abs 𝔼 ha hM, forwardSeries_solves_abs 𝔼 ha hM hua⟩,
    fun z hz => eq_forwardSeries_abs 𝔼 ha hM hua hz.2 hz.1⟩

/-! ### The undivided form `A z_t = B E_t z_{t+1} + f_t` (survey L1) -/

/-- Woodford (2003), eq. (A.14), p. 636, written without dividing: the scalar expectational
difference equation `A z_t = B E_t z_{t+1} + f_t`. -/
def ScalarEq (A B : ℝ) (f z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, A • z t = B • 𝔼.E t (z (t + 1)) + f t

/-- Woodford (2003), eq. (A.14), p. 636: with `A = 1` the undivided form is (A.14) itself. -/
theorem scalarEq_one_iff (a : ℝ) (u z : ℕ → Ω → ℝ) : ScalarEq 𝔼 1 a u z ↔ Solves 𝔼 a u z := by
  simp only [ScalarEq, Solves, one_smul]

/-- Woodford (2003), eq. (A.16), p. 636: the forward solution of `A z_t = B E_t z_{t+1} + f_t`,
`z_t = ∑_k (B/A)ᵏ E_t (f_{t+k}/A)`. -/
noncomputable def scalarSol (A B : ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (B / A) (fun t => A⁻¹ • f t)

/-- Woodford (2003), eq. (A.16), p. 636: `z_t = ∑_k Bᵏ/A^{k+1} E_t f_{t+k}`. -/
theorem scalarSol_apply (A B : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    scalarSol 𝔼 A B f t ω = ∑' k, B ^ k / A ^ (k + 1) * 𝔼.E t (f (t + k)) ω := by
  unfold scalarSol ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (A.14), p. 636: for `A ≠ 0` the equation reads
`z_t = (B/A) E_t z_{t+1} + f_t/A`. -/
theorem scalarEq_iff {A B : ℝ} (hA : A ≠ 0) (f z : ℕ → Ω → ℝ) :
    ScalarEq 𝔼 A B f z ↔ ∀ t, z t = (B / A) • 𝔼.E t (z (t + 1)) + A⁻¹ • f t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), Lemma (A.14)–(A.16), pp. 636–637 (survey L1, L4): if `|B| < |A|`, then for
bounded adapted `f` the forward solution is a bounded adapted solution of
`A z_t = B E_t z_{t+1} + f_t`, and it is the only bounded solution. -/
theorem scalar_existsUnique {A B K : ℝ} (hAB : |B| < |A|) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ K) (hfa : 𝔼.Adapted f) :
    ScalarEq 𝔼 A B f (scalarSol 𝔼 A B f) ∧ BoundedProc (scalarSol 𝔼 A B f) ∧
      𝔼.Adapted (scalarSol 𝔼 A B f) ∧
      ∀ z, ScalarEq 𝔼 A B f z → BoundedProc z → z = scalarSol 𝔼 A B f := by
  have hA0 : 0 < |A| := lt_of_le_of_lt (abs_nonneg B) hAB
  have hA : A ≠ 0 := abs_pos.mp hA0
  have ha : |B / A| < 1 := by rw [abs_div, div_lt_one hA0]; exact hAB
  have hu : ∀ t ω, |(fun t => A⁻¹ • f t) t ω| ≤ |A⁻¹| * K := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted (fun t => A⁻¹ • f t) := fun t => by
    simp only [map_smul, hfa t]
  have hsol : ScalarEq 𝔼 A B f (scalarSol 𝔼 A B f) :=
    (scalarEq_iff 𝔼 hA f _).mpr fun t => forwardSeries_solves_abs 𝔼 ha hu hua t
  refine ⟨hsol, forwardSeries_bounded_abs 𝔼 ha hu, forwardSeries_adapted_abs 𝔼 ha hu,
    fun z hz hzb => ?_⟩
  exact eq_forwardSeries_abs 𝔼 ha hu hua ((scalarEq_iff 𝔼 hA f z).mp hz) hzb

/-- Woodford (2003), (A.17), p. 637: if `|A| ≤ |B|` and `B ≠ 0`, the deterministic path
`h_t = (A/B)ᵗ` is a bounded nonzero solution of the homogeneous equation
`A h_t = B E_t h_{t+1}`. -/
theorem scalar_homog {A B : ℝ} (hle : |A| ≤ |B|) (hB : B ≠ 0) :
    ScalarEq 𝔼 A B 0 (fun t _ => (A / B) ^ t) ∧
      BoundedProc (fun t (_ : Ω) => (A / B) ^ t) := by
  refine ⟨fun t => ?_, ⟨1, fun t _ => ?_⟩⟩
  · rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
    field_simp
  · rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_div]
    exact div_le_one_of_le₀ hle (abs_nonneg _)

/-- Woodford (2003), Lemma (A.14)–(A.17), pp. 636–637 (survey L1): for `(A, B) ≠ (0, 0)`, the
equation `A z_t = B E_t z_{t+1} + f_t` has exactly one bounded solution for every bounded adapted
forcing process if and only if `|B| < |A|`. -/
theorem scalar_determinate_iff [Nonempty Ω] {A B : ℝ} (hAB : A ≠ 0 ∨ B ≠ 0) :
    (∀ f : ℕ → Ω → ℝ, BoundedProc f → 𝔼.Adapted f →
      ∃! z, BoundedProc z ∧ ScalarEq 𝔼 A B f z) ↔ |B| < |A| := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hB : B ≠ 0 := by
      rintro rfl
      rcases hAB with hA | hB
      · exact hA (abs_nonpos_iff.mp (by simpa using hc))
      · exact hB rfl
    obtain ⟨hh, hhb⟩ := scalar_homog 𝔼 hc hB
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    obtain ⟨z, -, hu⟩ := h 0 ⟨0, fun _ _ => by simp⟩ hz
    have h0 : ScalarEq 𝔼 A B 0 0 := fun t => by simp
    have e1 := hu 0 ⟨⟨0, fun _ _ => by simp⟩, h0⟩
    have e2 := hu _ ⟨hhb, hh⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (e2.trans e1.symm) 0) ω
    simp at this
  · intro h f ⟨K, hK⟩ hfa
    obtain ⟨hs, hb, -, hu⟩ := scalar_existsUnique 𝔼 h hK hfa
    exact ⟨_, ⟨hb, hs⟩, fun z hz => hu z hz.2 hz.1⟩

/-! ### `|a| > 1`: the family (A.17) -/

/-- Woodford (2003), eq. (A.17), pp. 636–637: `z_0` given and
`z_{t+1} = a⁻¹(z_t − u_t) + ν_{t+1}`. -/
noncomputable def sunspotFamily (a : ℝ) (u ν : ℕ → Ω → ℝ) (z0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => z0
  | t + 1 => a⁻¹ • (sunspotFamily a u ν z0 t - u t) + ν (t + 1)

omit 𝔼 in
/-- Woodford (2003), eq. (A.17), p. 637: the recursion of the family. -/
theorem sunspotFamily_succ (a : ℝ) (u ν : ℕ → Ω → ℝ) (z0 : Ω → ℝ) (t : ℕ) :
    sunspotFamily a u ν z0 (t + 1) = a⁻¹ • (sunspotFamily a u ν z0 t - u t) + ν (t + 1) :=
  rfl

/-- Woodford (2003), eq. (A.17), p. 637: the family is adapted when `z_0`, `u` and `ν` are. -/
theorem sunspotFamily_adapted {a : ℝ} {u ν : ℕ → Ω → ℝ} {z0 : Ω → ℝ} (hz0 : 𝔼.E 0 z0 = z0)
    (hua : 𝔼.Adapted u) (hνa : 𝔼.Adapted ν) : 𝔼.Adapted (sunspotFamily a u ν z0) := by
  intro t
  induction t with
  | zero => exact hz0
  | succ t ih =>
    rw [sunspotFamily_succ, map_add, map_smul, map_sub, E_of_known 𝔼 (Nat.le_succ t) ih,
      E_of_known 𝔼 (Nat.le_succ t) (hua t), hνa (t + 1)]

/-- Woodford (2003), eq. (A.17), p. 637: for `a ≠ 0` and any `ν` with `E_t ν_{t+1} = 0`, the
family (A.17) solves (A.14). -/
theorem sunspotFamily_solves {a : ℝ} (ha : a ≠ 0) {u ν : ℕ → Ω → ℝ} {z0 : Ω → ℝ}
    (hz0 : 𝔼.E 0 z0 = z0) (hua : 𝔼.Adapted u) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Solves 𝔼 a u (sunspotFamily a u ν z0) := by
  intro t
  rw [sunspotFamily_succ, map_add, map_smul, map_sub, sunspotFamily_adapted 𝔼 hz0 hua hνa t,
    hua t, hmd t, add_zero, smul_smul, mul_inv_cancel₀ ha, one_smul, sub_add_cancel]

/-- Woodford (2003), eq. (A.17), p. 637: for `|a| > 1` the family is bounded whenever `z_0`, `u`
and `ν` are. -/
theorem sunspotFamily_bounded {a B Mu Mν : ℝ} (ha : 1 < |a|) {u ν : ℕ → Ω → ℝ} {z0 : Ω → ℝ}
    (hz0 : ∀ ω, |z0 ω| ≤ B) (hu : ∀ t ω, |u t ω| ≤ Mu) (hν : ∀ t ω, |ν t ω| ≤ Mν) :
    BoundedProc (sunspotFamily a u ν z0) := by
  set c := |a| with hc
  have hc0 : 0 < c := by linarith
  set K := |B| + (|Mu| + |Mν| * c) / (c - 1) with hK
  refine ⟨K, fun t => ?_⟩
  have hfrac : 0 ≤ (|Mu| + |Mν| * c) / (c - 1) :=
    div_nonneg (by positivity) (by linarith)
  induction t with
  | zero => exact fun ω => (hz0 ω).trans ((le_abs_self B).trans (by linarith))
  | succ t ih =>
    intro ω
    rw [sunspotFamily_succ]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h1 : |a⁻¹ * (sunspotFamily a u ν z0 t ω - u t ω)| ≤ c⁻¹ * (K + |Mu|) := by
      rw [abs_mul, abs_inv]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (ih ω) ?_))
        (inv_nonneg.mpr hc0.le)
      exact (hu t ω).trans (le_abs_self _)
    have h2 : |ν (t + 1) ω| ≤ |Mν| := (hν (t + 1) ω).trans (le_abs_self _)
    have h3 : c⁻¹ * (K + |Mu|) + |Mν| ≤ K := by
      have hKe : K * (c - 1) = |B| * (c - 1) + (|Mu| + |Mν| * c) := by
        rw [hK, add_mul, div_mul_cancel₀ _ (by linarith)]
      have hB : 0 ≤ |B| * (c - 1) := mul_nonneg (abs_nonneg B) (by linarith)
      rw [← sub_nonneg]
      have : K - (c⁻¹ * (K + |Mu|) + |Mν|) = c⁻¹ * (K * (c - 1) - |Mu| - |Mν| * c) := by
        field_simp
        ring
      rw [this]
      exact mul_nonneg (inv_nonneg.mpr hc0.le) (by linarith)
    exact (abs_add_le _ _).trans (by linarith)

/-- Woodford (2003), eq. (A.17), p. 637 (converse, not in the book): for `a ≠ 0` every adapted
solution of (A.14) is a member of the family (A.17), with `ν_{t+1} = z_{t+1} − E_t z_{t+1}`,
a martingale difference. -/
theorem eq_sunspotFamily {a : ℝ} (ha : a ≠ 0) {u z : ℕ → Ω → ℝ} (hz : Solves 𝔼 a u z) :
    (∀ t, 𝔼.E t (z (t + 1) - 𝔼.E t (z (t + 1))) = 0) ∧
      z = sunspotFamily a u (fun t => z t - 𝔼.E (t - 1) (z t)) (z 0) := by
  refine ⟨fun t => by rw [map_sub, 𝔼.E_E_self, sub_self], ?_⟩
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sunspotFamily_succ, ← ih, show t + 1 - 1 = t by omega]
    have h : z t - u t = a • 𝔼.E t (z (t + 1)) := by rw [hz t]; abel
    rw [h, smul_smul, inv_mul_cancel₀ ha, one_smul]
    abel

/-! ### `|a| ≥ 1`: multiplicity -/

/-- Woodford (2003), App. A, p. 637: for `a ≠ 0` the deterministic path `c a⁻ᵗ` solves the
homogeneous equation `d_t = a E_t d_{t+1}`. -/
theorem homog_solves {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    Solves 𝔼 a 0 (fun t _ => c * a⁻¹ ^ t) := by
  intro t
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, add_zero, pow_succ]
  field_simp

/-- Woodford (2003), App. A, p. 637: adding a solution of the homogeneous equation to a
solution of (A.14) gives a solution. -/
theorem solves_add_homog {a : ℝ} {u z d : ℕ → Ω → ℝ} (hz : Solves 𝔼 a u z)
    (hd : Solves 𝔼 a 0 d) : Solves 𝔼 a u (z + d) := by
  intro t
  have h1 := hz t
  have h2 := hd t
  simp only [Pi.zero_apply, add_zero] at h2
  simp only [Pi.add_apply, map_add, smul_add]
  rw [← h2, h1]
  abel

/-- Woodford (2003), App. A, p. 637 ("if (A.14) has any bounded solution, it must have an
uncountably infinite number of them"): for `|a| ≥ 1` (so in particular for `|a| = 1`), the set
of bounded solutions is uncountable as soon as it is nonempty. -/
theorem bounded_solutions_not_countable [Nonempty Ω] {a : ℝ} (ha : 1 ≤ |a|)
    {u zbar : ℕ → Ω → ℝ} (hz : Solves 𝔼 a u zbar) (hzb : BoundedProc zbar) :
    ¬ {z | BoundedProc z ∧ Solves 𝔼 a u z}.Countable := by
  intro hcount
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    linarith
  obtain ⟨M, hM⟩ := hzb
  let f : ℝ → ℕ → Ω → ℝ := fun c => zbar + fun t _ => c * a⁻¹ ^ t
  have hmaps : Set.MapsTo f Set.univ {z | BoundedProc z ∧ Solves 𝔼 a u z} := by
    intro c _
    refine ⟨⟨M + |c|, fun t ω => ?_⟩, solves_add_homog 𝔼 hz (homog_solves 𝔼 ha0 c)⟩
    simp only [f, Pi.add_apply]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_pow, abs_inv]
    have : (|a|)⁻¹ ^ t ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ ha)
    nlinarith [abs_nonneg c]
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun h 0) ω
    simpa [f] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Woodford (2003), App. A, p. 637: for `|a| > 1` a bounded solution always exists (the member
of (A.17) with `z_0 = 0`, `ν = 0`), so there are uncountably many bounded solutions. -/
theorem exists_bounded_of_one_lt [Nonempty Ω] {a : ℝ} (ha : 1 < |a|) {u : ℕ → Ω → ℝ}
    (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    (∃ z, BoundedProc z ∧ Solves 𝔼 a u z) ∧ ¬ {z | BoundedProc z ∧ Solves 𝔼 a u z}.Countable := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    linarith
  obtain ⟨Mu, hMu⟩ := hub
  have hz0 : 𝔼.E 0 (fun _ => (0 : ℝ)) = fun _ => 0 := 𝔼.const 0 0
  have hνa : 𝔼.Adapted (fun _ _ => (0 : ℝ)) := fun t => 𝔼.const t 0
  have hs := sunspotFamily_solves 𝔼 ha0 hz0 hua hνa (fun t => 𝔼.const t 0)
  have hb := sunspotFamily_bounded (a := a) (B := 0) (Mν := 0) ha (z0 := fun _ => 0)
    (ν := fun _ _ => 0) (fun _ => by simp) hMu (fun _ _ => by simp)
  exact ⟨⟨_, hb, hs⟩, bounded_solutions_not_countable 𝔼 ha.le hs hb⟩

/-- Woodford (2003), App. A, p. 637 ("the condition that `|a| < 1` is both necessary and
sufficient for the existence of a unique bounded solution to (A.14)"). -/
theorem existsUnique_iff [Nonempty Ω] (a : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! z, BoundedProc z ∧ Solves 𝔼 a u z) ↔
      |a| < 1 := by
  have h := scalar_determinate_iff 𝔼 (A := 1) (B := a) (Or.inl one_ne_zero)
  simp only [scalarEq_one_iff, abs_one] at h
  exact h

/-! ### `|a| = 1`: survey error E12 -/

/-- Woodford (2003), App. A, p. 637 (`|a| = 1`, `a = 1`): the printed construction
`z_t = z̄_t + (z_{t−1} − z̄_{t−1}) + ν_t` gives a solution when `a = 1` (it is the family
(A.17) for the difference `z − z̄`). -/
theorem printed_A17_one_solves {u zbar ν : ℕ → Ω → ℝ} {d0 : Ω → ℝ} (hzbar : Solves 𝔼 1 u zbar)
    (hd0 : 𝔼.E 0 d0 = d0) (hνa : 𝔼.Adapted ν) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) :
    Solves 𝔼 1 u (zbar + sunspotFamily 1 0 ν d0) ∧
      ∀ t, (zbar + sunspotFamily 1 0 ν d0) (t + 1) =
        zbar (t + 1) + ((zbar + sunspotFamily 1 0 ν d0) t - zbar t) + ν (t + 1) := by
  refine ⟨solves_add_homog 𝔼 hzbar
    (sunspotFamily_solves 𝔼 one_ne_zero hd0 (fun t => by simp) hνa hmd), fun t => ?_⟩
  simp only [Pi.add_apply, sunspotFamily_succ, inv_one, one_smul, Pi.zero_apply, sub_zero]
  abel

/-- Woodford (2003), App. A, p. 637, survey error E12: the printed construction fails for
`a = −1`. With `u = 0`, `z̄ = 0` (a bounded solution), `ν = 0` and `z_0 = 1` the printed
recursion gives `z_t ≡ 1`, which does not solve `z_t = −E_t z_{t+1}`. -/
theorem printed_A17_fails_neg_one [Nonempty Ω] :
    Solves 𝔼 (-1) 0 0 ∧ (∀ t, (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) (t + 1) =
      (0 : ℕ → Ω → ℝ) (t + 1) + ((fun _ _ => (1 : ℝ)) t - (0 : ℕ → Ω → ℝ) t) + 0) ∧
      ¬ Solves 𝔼 (-1) 0 (fun _ _ => 1) := by
  refine ⟨fun t => by simp, fun t => by simp, fun h => ?_⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (h 0) ω
  rw [𝔼.const] at this
  norm_num at this

/-- Woodford (2003), App. A, p. 637, corrected (E12): for `|a| = 1` (any `a ≠ 0`) the
difference from a solution must follow `d_t = a⁻¹ d_{t−1} + ν_t`; for `a = −1` this is
`d_t = −d_{t−1} + ν_t`. Every such `z̄ + d` solves (A.14). -/
theorem unit_sunspot_solves {a : ℝ} (ha : a ≠ 0) {u zbar ν : ℕ → Ω → ℝ} {d0 : Ω → ℝ}
    (hzbar : Solves 𝔼 a u zbar) (hd0 : 𝔼.E 0 d0 = d0) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Solves 𝔼 a u (zbar + sunspotFamily a 0 ν d0) :=
  solves_add_homog 𝔼 hzbar (sunspotFamily_solves 𝔼 ha hd0 (fun t => by simp) hνa hmd)

omit 𝔼 in
/-- Woodford (2003), App. A, p. 637 (the book's sufficient condition, corrected): for `|a| = 1`,
if `ν` is bounded and vanishes after date `T`, the sunspot difference `d_t = a⁻¹ d_{t−1} + ν_t`
is bounded. -/
theorem unit_sunspot_bounded {a B Mν : ℝ} (ha : |a| = 1) {ν : ℕ → Ω → ℝ} {d0 : Ω → ℝ} (T : ℕ)
    (hd0 : ∀ ω, |d0 ω| ≤ B) (hν : ∀ t ω, |ν t ω| ≤ Mν) (hT : ∀ t, T < t → ν t = 0) :
    BoundedProc (sunspotFamily a 0 ν d0) := by
  refine ⟨B + T * Mν, fun t => ?_⟩
  have key : ∀ t ω, |sunspotFamily a 0 ν d0 t ω| ≤ B + (min t T : ℕ) * Mν := by
    intro t
    induction t with
    | zero =>
      intro ω
      have h0 : (min 0 T : ℕ) = 0 := by omega
      rw [h0, Nat.cast_zero, zero_mul, add_zero]
      exact hd0 ω
    | succ t ih =>
      intro ω
      rw [sunspotFamily_succ]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero, smul_eq_mul]
      have h1 : |a⁻¹ * sunspotFamily a 0 ν d0 t ω| = |sunspotFamily a 0 ν d0 t ω| := by
        rw [abs_mul, abs_inv, ha, inv_one, one_mul]
      by_cases hlt : t < T
      · have hm : min (t + 1) T = min t T + 1 := by omega
        rw [hm, Nat.cast_add, Nat.cast_one]
        have := abs_add_le (a⁻¹ * sunspotFamily a 0 ν d0 t ω) (ν (t + 1) ω)
        linarith [ih ω, hν (t + 1) ω]
      · have hm : min (t + 1) T = min t T := by omega
        rw [hm, hT (t + 1) (by omega)]
        simp only [Pi.zero_apply, add_zero]
        rw [h1]
        exact ih ω
  intro ω
  have hMν : 0 ≤ Mν := (abs_nonneg _).trans (hν 0 ω)
  have hmin : ((min t T : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.min_le_right t T
  nlinarith [key t ω]

/-- Woodford (2003), App. A, p. 637, corrected (E12): if the forecasts of the forcing decay
geometrically, `|E_s u_{s+j}| ≤ M λʲ` with `0 ≤ λ < 1`, then for every `|a| ≤ 1` (in particular
`a = ±1`) the forward sum `∑ aʲ E_t u_{t+j}` (not `∑ E_t u_{t+j}` unless `a = 1`) is a bounded
solution of (A.14). -/
theorem forwardSeries_solves_of_decay {a lam M : ℝ} (ha : |a| ≤ 1) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) {u : ℕ → Ω → ℝ} (hdec : ∀ s j ω, |𝔼.E s (u (s + j)) ω| ≤ M * lam ^ j)
    (hua : 𝔼.Adapted u) :
    Solves 𝔼 a u (𝔼.forwardSeries a u) ∧ BoundedProc (𝔼.forwardSeries a u) := by
  have hterm : ∀ s k ω, |a ^ k * 𝔼.E s (u (s + k)) ω| ≤ lam ^ k * M := fun s k ω => by
    rw [abs_mul, abs_pow, mul_comm (lam ^ k)]
    calc |a| ^ k * |𝔼.E s (u (s + k)) ω| ≤ 1 * (M * lam ^ k) :=
          mul_le_mul (pow_le_one₀ (abs_nonneg a) ha) (hdec s k ω) (abs_nonneg _) zero_le_one
      _ = M * lam ^ k := one_mul _
  have hsum : ∀ s ω, Summable (fun k => a ^ k * 𝔼.E s (u (s + k)) ω) := fun s ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl1).mul_right M)
      (fun k => by rw [Real.norm_eq_abs]; exact hterm s k ω)
  refine ⟨fun t => ?_, ?_⟩
  · funext ω
    have hE : 𝔼.E t (𝔼.forwardSeries a u (t + 1)) ω =
        ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
      change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
      rw [𝔼.E_tsum hl0 hl1 (fun k ω' => hterm (t + 1) k ω') t ω]
      refine tsum_congr fun k => ?_
      change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
      rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
    rw [hE, (hsum t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hua t,
      ← tsum_mul_left, add_comm]
    congr 1
    refine tsum_congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  · refine ⟨M / (1 - lam), fun t ω => ?_⟩
    have hg : HasSum (fun k : ℕ => M * lam ^ k) (M / (1 - lam)) := by
      have := (hasSum_geometric_of_lt_one hl0 hl1).mul_left M
      simpa [div_eq_mul_inv] using this
    have := tsum_of_norm_bounded hg (f := fun k => a ^ k * 𝔼.E t (u (t + k)) ω) fun k => by
      rw [Real.norm_eq_abs, mul_comm M]
      exact hterm t k ω
    simpa [ExpectationSystem.forwardSeries, Real.norm_eq_abs] using this

/-- Woodford (2003), App. A, p. 637 ("any stationary ARMA process … with bounded innovations",
corrected to mean zero): a bounded AR(1) forcing `E_t u_{t+1} = ρ u_t` with `|ρ| < 1` has
geometrically decaying forecasts, so `forwardSeries_solves_of_decay` applies. -/
theorem ar1_decay {ρ M : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hM : ∀ t ω, |u t ω| ≤ M)
    (s j : ℕ) (ω : Ω) : |𝔼.E s (u (s + j)) ω| ≤ M * |ρ| ^ j := by
  rw [𝔼.ar1_iterate hu s j, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM s ω) (pow_nonneg (abs_nonneg ρ) j)

/-- Woodford (2003), App. A, p. 637, survey error E12 (existence at `|a| = 1`): for `a = 1` or
`a = −1` and the bounded forcing `u_t = c aᵗ` with `c ≠ 0` (for `a = 1` a constant: a
stationary process with nonzero mean; for `a = −1` the alternating `c (−1)ᵗ`), (A.14) has NO
bounded solution. So at `a = −1` existence is not automatic; by
`bounded_solutions_not_countable` it is never unique either. -/
theorem no_bounded_solution_unit [Nonempty Ω] {a c : ℝ} (ha : a ^ 2 = 1) (hc : c ≠ 0)
    {z : ℕ → Ω → ℝ} (hz : Solves 𝔼 a (fun t _ => c * a ^ t) z) : ¬ BoundedProc z := by
  rintro ⟨M, hM⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have habs : |a| = 1 := by
    have : |a| ^ 2 = 1 := by rw [sq_abs, ha]
    nlinarith [abs_nonneg a, sq_nonneg (|a| - 1), sq_nonneg (|a| + 1)]
  set w : ℕ → ℝ := fun t => a ^ t * 𝔼.E 0 (z t) ω with hw
  have hstep : ∀ t, w t = w (t + 1) + c := by
    intro t
    have h := congrArg (𝔼.E 0) (hz t)
    rw [map_add, map_smul, 𝔼.tower (Nat.zero_le t), 𝔼.const] at h
    have h' := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
    simp only [hw]
    rw [h', pow_succ]
    have : a ^ t * (c * a ^ t) = (a ^ 2) ^ t * c := by ring
    rw [mul_add, this, ha, one_pow, one_mul]
    ring
  have hdrift : ∀ t : ℕ, w t = w 0 - t * c := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => push_cast; linarith [hstep t]
  have hb : ∀ t, |w t| ≤ M := fun t => by
    simp only [hw, abs_mul, abs_pow, habs, one_pow, one_mul]
    exact 𝔼.abs_E_le (hM t) 0 ω
  have hc' : 0 < |c| := abs_pos.mpr hc
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / |c|)
  have h1 := hb n
  have h2 := hb 0
  rw [hdrift n] at h1
  have h3 : |(n : ℝ) * c| ≤ 2 * M := by
    calc |(n : ℝ) * c| = |w 0 - (w 0 - n * c)| := by ring_nf
      _ ≤ |w 0| + |w 0 - n * c| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [abs_mul, Nat.abs_cast] at h3
  rw [div_lt_iff₀ hc'] at hn
  linarith

/-! ### The predetermined-variable variant (§A.10) -/

/-- Woodford (2003), §A.10, p. 643: for `|a| < 1` and bounded adapted `u`, a bounded process `z`
(adapted or not, e.g. predetermined) satisfies (A.14) at all dates if and only if it equals the
forward sum (A.16) at all dates. -/
theorem solves_iff_forwardSeries {a M : ℝ} (ha : |a| < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (hzb : BoundedProc z) :
    Solves 𝔼 a u z ↔ ∀ t, z t = 𝔼.forwardSeries a u t := by
  constructor
  · intro hz t
    rw [eq_forwardSeries_abs 𝔼 ha hu hua hz hzb]
  · intro h
    have : z = 𝔼.forwardSeries a u := funext h
    rw [this]
    exact forwardSeries_solves_abs 𝔼 ha hu hua

/-- Woodford (2003), §A.10, p. 643: when `z_{t+1}` is predetermined (known at date `t`), a
bounded solution of (A.14) forces the restriction that the forward sum dated `t + 1` is already
known at date `t` — (2.17) restricts how the right-hand side may vary, rather than "solving"
for `z`. -/
theorem predetermined_restriction {a M : ℝ} (ha : |a| < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (hzb : BoundedProc z)
    (hpre : ∀ t, 𝔼.E t (z (t + 1)) = z (t + 1)) (hz : Solves 𝔼 a u z) (t : ℕ) :
    𝔼.E t (𝔼.forwardSeries a u (t + 1)) = 𝔼.forwardSeries a u (t + 1) := by
  rw [← (solves_iff_forwardSeries 𝔼 ha hu hua hzb).mp hz (t + 1), hpre t]

/-! ### Survey lemma L2: geometric-weight algebra -/

omit 𝔼 in
/-- Woodford (2003), App. A (used for (1.37), (2.7), (A.16), and Figure 2.3, pp. 119–120),
survey lemma L2: `∑_j c Bʲ / A^{j+1}` converges to `c/(A − B)` for `|B| < |A|`. -/
theorem hasSum_geometric_ratio {A B : ℝ} (c : ℝ) (h : |B| < |A|) :
    HasSum (fun j : ℕ => c * B ^ j / A ^ (j + 1)) (c / (A - B)) := by
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    linarith [abs_nonneg B]
  have hq : |B / A| < 1 := by
    rw [abs_div, div_lt_one (abs_pos.mpr hA)]
    exact h
  have hAB : A - B ≠ 0 := by
    intro h0
    have : A = B := by linarith
    rw [this] at h
    exact lt_irrefl _ h
  have hg := (hasSum_geometric_of_abs_lt_one hq).mul_left (c / A)
  have hval : c / A * (1 - B / A)⁻¹ = c / (A - B) := by
    rw [one_sub_div hA, inv_div]
    field_simp
  rw [hval] at hg
  refine hg.congr_fun fun j => ?_
  rw [div_pow, pow_succ]
  field_simp

omit 𝔼 in
/-- Woodford (2003), App. A (used for (1.37), (2.7), (A.16)), survey lemma L2:
`∑_j c Bʲ / A^{j+1} = c/(A − B)` for `|B| < |A|`. -/
theorem tsum_geometric_ratio {A B : ℝ} (c : ℝ) (h : |B| < |A|) :
    ∑' j : ℕ, c * B ^ j / A ^ (j + 1) = c / (A - B) :=
  (hasSum_geometric_ratio c h).tsum_eq

omit 𝔼 in
/-- Woodford (2003), survey L2 (summation by parts for (1.39), (3.7), (3.17)): with geometric
weights, `∑ qʲ x_j` converges (`|q| < 1`) when the increments of `x` are bounded. -/
theorem summable_geom_mul {q K : ℝ} (hq : |q| < 1) {x : ℕ → ℝ}
    (hx : ∀ j, |x (j + 1) - x j| ≤ K) : Summable (fun j => q ^ j * x j) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hx 0)
  have hgrow : ∀ j : ℕ, |x j| ≤ |x 0| + j * K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hx j
      have h2 : |x (j + 1)| ≤ |x j| + |x (j + 1) - x j| := by
        have := abs_add_le (x j) (x (j + 1) - x j)
        simpa using this
      push_cast
      linarith
  have h1 : Summable (fun j : ℕ => |x 0| * |q| ^ j) :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_left _
  have h2 : Summable (fun j : ℕ => K * ((j : ℝ) ^ 1 * |q| ^ j)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hq)).mul_left K
  refine Summable.of_norm_bounded (h1.add h2) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_one]
  calc |q| ^ j * |x j| ≤ |q| ^ j * (|x 0| + j * K) :=
        mul_le_mul_of_nonneg_left (hgrow j) (pow_nonneg (abs_nonneg q) j)
    _ = |x 0| * |q| ^ j + K * (j * |q| ^ j) := by ring

omit 𝔼 in
/-- Woodford (2003), survey L2 (summation by parts for (1.39), (3.7), (3.17)): for `|q| < 1`
and `x` with bounded increments, `(1 − q) ∑ qʲ x_j = x_0 + ∑ q^{j+1} (x_{j+1} − x_j)`. -/
theorem abel_tsum {q K : ℝ} (hq : |q| < 1) {x : ℕ → ℝ} (hx : ∀ j, |x (j + 1) - x j| ≤ K) :
    (1 - q) * ∑' j, q ^ j * x j = x 0 + ∑' j, q ^ (j + 1) * (x (j + 1) - x j) := by
  have hS := summable_geom_mul hq hx
  have hS1 : Summable (fun j => q ^ (j + 1) * x (j + 1)) :=
    (summable_nat_add_iff 1).mpr hS
  have hS2 : Summable (fun j => q ^ (j + 1) * x j) := by
    have := hS.mul_left q
    refine this.congr fun j => ?_
    ring
  have e1 := hS.tsum_eq_zero_add
  have e2 : ∑' j, q ^ (j + 1) * x j = q * ∑' j, q ^ j * x j := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e3 : ∑' j, q ^ (j + 1) * (x (j + 1) - x j) =
      ∑' j, q ^ (j + 1) * x (j + 1) - ∑' j, q ^ (j + 1) * x j := by
    rw [← hS1.tsum_sub hS2]
    exact tsum_congr fun j => by ring
  rw [e3, e2]
  simp only [pow_zero, one_mul] at e1
  linarith

omit 𝔼 in
/-- Woodford (2003), eq. (1.39), p. 83, survey lemma L2 (summation by parts, finite form):
with weights `(1 − q) qʲ`,
`∑_{j<N} (1 − q) qʲ X_j = X_0 (1 − q^N) + ∑_{k<N} q^{k+1}(X_{k+1} − X_k) − q^N (X_N − X_0)`. -/
theorem sum_weights_by_parts (q : ℝ) (X : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 - q) * q ^ j * X j =
      X 0 * (1 - q ^ N) + ∑ k ∈ Finset.range N, q ^ (k + 1) * (X (k + 1) - X k) -
        q ^ N * (X N - X 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

omit 𝔼 in
/-- Woodford (2003), eq. (1.39), p. 83, survey lemma L2 (summation by parts): for `0 ≤ q < 1`
and a sequence of bounded increments `|X_{k+1} − X_k| ≤ M` (so `X` grows at most linearly),
`∑_j (1 − q) qʲ X_j = X_0 + ∑_{k ≥ 0} q^{k+1}(X_{k+1} − X_k)`, both series converging
(the case `q ≥ 0` of `abel_tsum`). -/
theorem tsum_weights_by_parts {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (X : ℕ → ℝ)
    (hX : ∀ k, |X (k + 1) - X k| ≤ M) :
    Summable (fun j => (1 - q) * q ^ j * X j) ∧
      Summable (fun k => q ^ (k + 1) * (X (k + 1) - X k)) ∧
      ∑' j, (1 - q) * q ^ j * X j = X 0 + ∑' k, q ^ (k + 1) * (X (k + 1) - X k) := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hs1 : Summable (fun j => (1 - q) * q ^ j * X j) :=
    ((summable_geom_mul hq hX).mul_left (1 - q)).congr fun j => by ring
  have hs2 : Summable (fun k => q ^ (k + 1) * (X (k + 1) - X k)) := by
    refine Summable.of_norm_bounded
      (((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_right M) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0, pow_succ, mul_comm (q ^ k) q]
    exact mul_le_mul_of_nonneg_left (hX k) (by positivity)
  refine ⟨hs1, hs2, ?_⟩
  rw [← abel_tsum hq hX, ← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-! ### Survey lemma L4: determinacy sign lemma -/

/-- Woodford (2003), App. A, A.12–A.15, pp. 645–646 (survey lemma L4): if `A − B > 0` and
`A + B > 0` then `|B| < |A|`. -/
theorem abs_lt_abs_of_sub_pos_add_pos {A B : ℝ} (h1 : 0 < A - B) (h2 : 0 < A + B) :
    |B| < |A| := by
  rw [abs_of_pos (by linarith : 0 < A), abs_lt]
  constructor <;> linarith

/-- Woodford (2003), App. A, A.12–A.15, pp. 645–646 (survey lemma L4): if `A + B > 0` then
`|B| < |A| ↔ B < A`. -/
theorem abs_lt_abs_iff_of_add_pos {A B : ℝ} (h : 0 < A + B) : |B| < |A| ↔ B < A := by
  constructor
  · intro hlt
    by_contra hc
    push Not at hc
    rcases le_or_gt 0 A with hA | hA
    · rw [abs_of_nonneg hA] at hlt
      linarith [le_abs_self B]
    · rw [abs_of_neg hA] at hlt
      linarith [le_abs_self B]
  · intro hlt
    exact abs_lt_abs_of_sub_pos_add_pos (by linarith) h

/-- Woodford (2003), App. B.3, pp. 659–661, and App. B.7, p. 668 (and Galí (2015), p. 57):
`E_t` commutes with an infinite sum of random variables dominated by a summable sequence,
`|f_k| ≤ u_k` (added to the shared core for the Chapter 3 modules). -/
theorem E_tsum_dom {u : ℕ → ℝ} (hu : Summable u) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ u k) (t : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' k, f k ω') ω = ∑' k, 𝔼.E t (f k) ω := by
  set F : Ω → ℝ := fun ω' => ∑' k, f k ω' with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, f k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, u (k + n) with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add u
  have hsum : ∀ ω', Summable (fun k => f k ω') := fun ω' =>
    Summable.of_norm_bounded hu (fun k => by rw [Real.norm_eq_abs]; exact hf k ω')
  have htail : ∀ n ω', |F ω' - Fn n ω'| ≤ T n := by
    intro n ω'
    have hsplit := (hsum ω').sum_add_tsum_nat_add n
    have hFn' : Fn n ω' = ∑ k ∈ Finset.range n, f k ω' := by
      simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, f k ω' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => f (k + n) ω' := (summable_nat_add_iff n).mpr (hsum ω')
    have hg : Summable fun k => u (k + n) := (summable_nat_add_iff n).mpr hu
    calc |∑' k, f (k + n) ω'| ≤ ∑' k, |f (k + n) ω'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => f (k + n) ω')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := Summable.tsum_le_tsum (fun k => hf (k + n) ω') hs'.abs hg
  have hEFn : ∀ n, 𝔼.E t (Fn n) ω = ∑ k ∈ Finset.range n, 𝔼.E t (f k) ω := by
    intro n
    simp [hFn, map_sum, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ω' => htail n ω') t ω
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hbE : Summable (fun k => 𝔼.E t (f k) ω) :=
    Summable.of_norm_bounded hu (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (∑' k, 𝔼.E t (f k) ω)) := by
    simp_rw [hEFn]
    exact hbE.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

end Cochrane.NewKeynesianSelection.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Innovations `ΔE_{t+1} = E_{t+1} − E_t`

Cochrane (2023), *The Fiscal Theory of the Price Level*, notation `ΔE_{t+1} ≡ E_{t+1} − E_t`
(§2.4, p. 30), used throughout Chapter 16 (eqs. (16.3), (16.5), (16.7), (16.10), pp. 364–365).
Cochrane writes the new-Keynesian and fiscal-theory models in innovations: unexpected
inflation `ΔE_{t+1} π_{t+1}`, the fiscal shock `ε_{Σs,t+1}`, and the sunspots `δ_{t+1}` with
`E_t δ_{t+1} = 0`. This module provides the innovation operator for an arbitrary
`ExpectationSystem`, so every later result holds under perfect foresight and under genuine
uncertainty. The algebra of `innov` is restated from the Chapter 2 project
(`ExpectationTools`); the decomposition, shock and AR(1) results are new.

## Main results

* `innov` and its algebra: `innov_add`, `innov_sub`, `innov_smul`, `innov_neg`, `innov_const`,
  `innov_of_known`, `innov_eq_sub_E`, `innov_known_next`, `innov_E_succ`, `innov_mul_known`.
* `E_innov_zero`, `E_innov_zero_of_le`: `E_t ΔE_{t+1} x = 0` (innovations are unforecastable).
* The decomposition `x_{t+1} = E_t x_{t+1} + ΔE_{t+1} x_{t+1}` (`eq_E_add_innov`), and its
  uniqueness (`decomposition_unique`): a split into a date-`t` known part and an unforecastable
  part is necessarily this one. `telescope_innov`: `x = E_t x + ∑_{j<n} ΔE_{t+j+1} x` for `x`
  known at `t + n`.
* Shocks (`IsShock`: known at `t + 1`, `E_t ε_{t+1} = 0`): `innov_shock`, `innov_shock_later`,
  `isShock_iff_innov`, `isShock_smul`, `isShock_neg`; the innovation process of any adapted
  process is a shock (`innovProc_isShock`); `adapted_isShock_iff` (an adapted process with
  unforecastable increments is a shock; the notions differ only at date 0).
* AR(1) innovations: `ar1_of_shock` (a process `u_{t+1} = η u_t + ε_{t+1}` driven by a shock is
  `IsAR1 η`), `shock_of_ar1` (conversely the AR(1) residual is a shock and is the innovation),
  `innov_ar1` (`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`), `E_ar1_shift` (`E_s u_{t} = η^{t−s} u_s`).
* `innov_tsum`: the innovation of a dominated infinite sum is the sum of the innovations.
* `coinShock_adapted`, `coin_shock_ne_zero`: on the coin-flip event tree a genuinely random
  shock exists.
-/

namespace Cochrane.NewKeynesianSelection.Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The operator -/

/-- Cochrane (2023), §2.4, p. 30 (notation `ΔE_{t+1} ≡ E_{t+1} − E_t`, used in (16.3), p. 364):
the innovation of `x` between dates `t` and `t + 1`. -/
def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), p. 30: innovations are additive. -/
theorem innov_add (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x + y) = innov 𝔼 t x + innov 𝔼 t y := by
  unfold innov
  rw [map_add, map_add]
  abel

/-- Cochrane (2023), p. 30: innovations commute with subtraction. -/
theorem innov_sub (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x - y) = innov 𝔼 t x - innov 𝔼 t y := by
  unfold innov
  rw [map_sub, map_sub]
  abel

/-- Cochrane (2023), p. 30: innovations are homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) : innov 𝔼 t (c • x) = c • innov 𝔼 t x := by
  unfold innov
  rw [map_smul, map_smul, smul_sub]

/-- Cochrane (2023), p. 30: the innovation of a negative. -/
theorem innov_neg (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (-x) = -innov 𝔼 t x := by
  unfold innov
  rw [map_neg, map_neg]
  abel

/-- Cochrane (2023), p. 30: constants have no innovation. -/
theorem innov_const (t : ℕ) (c : ℝ) : innov 𝔼 t (fun _ => c) = 0 := by
  unfold innov
  rw [𝔼.const, 𝔼.const, sub_self]

/-- Cochrane (2023), p. 30: a variable known at date `t` has no date-`t + 1` innovation. -/
theorem innov_of_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  unfold innov
  rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx, hx, sub_self]

/-- Cochrane (2023), p. 30 and (16.5), p. 364 ("you can't expect future unexpected shocks"):
`E_t(ΔE_{t+1} x) = 0`. -/
theorem E_innov_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  unfold innov
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), p. 30: an earlier expectation of a later innovation is zero,
`E_s(ΔE_{t+1} x) = 0` for `s ≤ t`. -/
theorem E_innov_zero_of_le {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : 𝔼.E s (innov 𝔼 t x) = 0 := by
  rw [← 𝔼.tower hst, E_innov_zero, map_zero]

/-- Cochrane (2023), (16.3), p. 364: for `x` known at `t + 1`,
`ΔE_{t+1} x = x − E_t x` (the unexpected part of `x`). -/
theorem innov_eq_sub_E {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    innov 𝔼 t x = x - 𝔼.E t x := by
  rw [innov, hx]

/-- Cochrane (2023), p. 30: the date-`t + 1` innovation is known at date `t + 1`. -/
theorem innov_known_next (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  unfold innov
  rw [map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), p. 30: the innovation of `E_{t+1} x` is the innovation of `x`. -/
theorem innov_E_succ (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (𝔼.E (t + 1) x) = innov 𝔼 t x := by
  unfold innov
  rw [𝔼.E_E_self, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 30 (pull-out): a factor known at date `t` comes out of the innovation,
`ΔE_{t+1}(a y) = a ΔE_{t+1} y`. -/
theorem innov_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (y : Ω → ℝ) : innov 𝔼 t (a * y) = a * innov 𝔼 t y := by
  unfold innov
  rw [hPO (t + 1) a y (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ha), hPO t a y ha, mul_sub]

/-! ### The decomposition into expected and unexpected parts -/

/-- Cochrane (2023), p. 35 and (16.5), p. 364 (`π_{t+1} = E_t π_{t+1} + ΔE_{t+1} π_{t+1}`): any
random variable known at `t + 1` is its forecast plus its innovation. -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    x = 𝔼.E t x + innov 𝔼 t x := by
  unfold innov
  rw [hx]
  abel

/-- Cochrane (2023), (16.5), p. 364: the decomposition is unique. If `x = a + d` with `a` known
at `t` and `E_t d = 0`, then `a = E_t x` and, when `x` is known at `t + 1`, `d = ΔE_{t+1} x`. -/
theorem decomposition_unique {t : ℕ} {x a d : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x)
    (ha : 𝔼.E t a = a) (hd : 𝔼.E t d = 0) (hsplit : x = a + d) :
    a = 𝔼.E t x ∧ d = innov 𝔼 t x := by
  have hEa : 𝔼.E t x = a := by rw [hsplit, map_add, ha, hd, add_zero]
  refine ⟨hEa.symm, ?_⟩
  unfold innov
  rw [hx, hEa, hsplit]
  abel

/-- Cochrane (2023), p. 30 (iterating `ΔE`): a variable known at `t + n` is its date-`t`
forecast plus the sum of the `n` innovations from `t + 1` to `t + n`,
`x = E_t x + ∑_{j<n} ΔE_{t+j+1} x`. -/
theorem telescope_innov {t n : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + n) x = x) :
    x = 𝔼.E t x + ∑ j ∈ Finset.range n, innov 𝔼 (t + j) x := by
  have key : ∀ m, 𝔼.E (t + m) x = 𝔼.E t x + ∑ j ∈ Finset.range m, innov 𝔼 (t + j) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← add_assoc (𝔼.E t x), ← ih, ← add_assoc t m 1]
      unfold innov
      abel
  rw [← key n, hx]

/-! ### Shocks -/

/-- Cochrane (2023), p. 40 (terminology: a "shock" only moves unexpectedly) and (16.5), p. 364
(`E_t δ_{t+1} = 0`): `ε_{t+1}` is known at `t + 1` and `E_t ε_{t+1} = 0`. The date-0 value is
irrelevant. -/
def IsShock (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0

/-- Cochrane (2023), p. 40: a shock's innovation on arrival is the shock itself,
`ΔE_{t+1} ε_{t+1} = ε_{t+1}`. -/
theorem innov_shock {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t : ℕ) :
    innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  unfold innov
  rw [hε.1 t, hε.2 t, sub_zero]

/-- Cochrane (2023), p. 40: a later shock has no innovation at an earlier date,
`ΔE_{t+1} ε_{t+2+j} = 0`. -/
theorem innov_shock_later {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t j : ℕ) :
    innov 𝔼 t (ε (t + 2 + j)) = 0 := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e]
  unfold innov
  rw [← 𝔼.tower (show t + 1 ≤ t + 1 + j by omega), hε.2, map_zero,
    ← 𝔼.tower (show t ≤ t + 1 + j by omega), hε.2, map_zero, sub_zero]

/-- Cochrane (2023), (16.5), p. 364: a shock has zero forecast at every earlier date,
`E_s ε_{t+1} = 0` for `s ≤ t`. -/
theorem E_shock_of_le {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (ε (t + 1)) = 0 := by
  rw [← 𝔼.tower hst, hε.2 t, map_zero]

/-- Cochrane (2023), (16.5), p. 364: a process known at `t + 1` is a shock iff it equals its own
innovation at every date. -/
theorem isShock_iff_innov {ε : ℕ → Ω → ℝ} (hk : ∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) :
    IsShock 𝔼 ε ↔ ∀ t, innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  constructor
  · exact fun h t => innov_shock 𝔼 h t
  · intro h
    refine ⟨hk, fun t => ?_⟩
    rw [← h t, E_innov_zero]

/-- Cochrane (2023), (16.5), p. 364: the innovation process `ν_0 = 0`,
`ν_{t+1} = ΔE_{t+1} x_{t+1}` of a process `x`. -/
def innovProc (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => innov 𝔼 t (x (t + 1))

/-- Cochrane (2023), (16.5), p. 364: the innovation process of any process is a shock. -/
theorem innovProc_isShock (x : ℕ → Ω → ℝ) : IsShock 𝔼 (innovProc 𝔼 x) :=
  ⟨fun t => innov_known_next 𝔼 t (x (t + 1)), fun t => E_innov_zero 𝔼 t (x (t + 1))⟩

/-- Cochrane (2023), (16.5), p. 364: an adapted process is its own forecast plus its innovation
process, `x_{t+1} = E_t x_{t+1} + ν_{t+1}`. -/
theorem eq_E_add_innovProc {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    x (t + 1) = 𝔼.E t (x (t + 1)) + innovProc 𝔼 x (t + 1) :=
  eq_E_add_innov 𝔼 (hx (t + 1))

/-- Cochrane (2023), (16.5), p. 364: shocks are closed under linear combinations. -/
theorem isShock_lin {ε ν : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (hν : IsShock 𝔼 ν) (a b : ℝ) :
    IsShock 𝔼 (fun t => a • ε t + b • ν t) :=
  ⟨fun t => by simp only [map_add, map_smul, hε.1 t, hν.1 t],
    fun t => by simp only [map_add, map_smul, hε.2 t, hν.2 t, smul_zero, add_zero]⟩

/-- Cochrane (2023), (16.5), p. 364: a rescaled shock is a shock. -/
theorem isShock_smul {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (c : ℝ) :
    IsShock 𝔼 (fun t => c • ε t) :=
  ⟨fun t => by simp only [map_smul, hε.1 t], fun t => by simp only [map_smul, hε.2 t, smul_zero]⟩

/-- Cochrane (2023), (16.5), p. 364: the negative of a shock is a shock. -/
theorem isShock_neg {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) : IsShock 𝔼 (fun t => -ε t) :=
  ⟨fun t => by rw [map_neg, hε.1 t], fun t => by rw [map_neg, hε.2 t, neg_zero]⟩

/-- Cochrane (2023), p. 365 (a shock as an adapted process with `E_t ε_{t+1} = 0`): an adapted
process with unforecastable increments is a shock in the sense of `IsShock`, and the two notions
differ only by the irrelevant date-0 measurability of `ε_0`. -/
theorem adapted_isShock_iff {ε : ℕ → Ω → ℝ} :
    (𝔼.Adapted ε ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0) ↔ IsShock 𝔼 ε ∧ 𝔼.E 0 (ε 0) = ε 0 := by
  constructor
  · rintro ⟨ha, h0⟩
    exact ⟨⟨fun t => ha (t + 1), h0⟩, ha 0⟩
  · rintro ⟨hs, h0⟩
    refine ⟨fun t => ?_, hs.2⟩
    cases t with
    | zero => exact h0
    | succ t => exact hs.1 t

/-- Cochrane (2023), (16.5), p. 364: the zero process is a shock. -/
theorem isShock_zero : IsShock 𝔼 (0 : ℕ → Ω → ℝ) :=
  ⟨fun _ => map_zero _, fun _ => map_zero _⟩

/-! ### AR(1) innovations -/

/-- Cochrane (2023), p. 364 (`u_t = η u_{t−1} + ε_t`) and p. 365 (`u_{t+1} = η u_t + ε_{i,t+1}`):
the AR(1) law of motion driven by `ε`. -/
def AR1Law (η : ℝ) (u ε : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023), p. 364: an adapted process following the AR(1) law with shock innovations
satisfies `E_t u_{t+1} = η u_t`, i.e. is `IsAR1 η`. -/
theorem ar1_of_shock {η : ℝ} {u ε : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε)
    (hlaw : AR1Law η u ε) : 𝔼.IsAR1 η u :=
  ⟨hu, fun t => by rw [hlaw t, map_add, map_smul, hu t, hε.2 t, add_zero]⟩

/-- Cochrane (2023), p. 364: conversely, for `IsAR1 η u` the residual
`ε_{t+1} = u_{t+1} − η u_t` is a shock, it satisfies the AR(1) law, and it is the innovation
`ΔE_{t+1} u_{t+1}`. -/
theorem shock_of_ar1 {η : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    IsShock 𝔼 (fun t => u t - η • u (t - 1)) ∧ AR1Law η u (fun t => u t - η • u (t - 1)) ∧
      ∀ t, innov 𝔼 t (u (t + 1)) = u (t + 1) - η • u t := by
  have hk : ∀ t, 𝔼.E (t + 1) (u t) = u t := fun t =>
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu.1 t)
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, fun t => ?_⟩
  · simp only [Nat.add_sub_cancel, map_sub, map_smul, hu.1 (t + 1), hk t]
  · simp only [Nat.add_sub_cancel, map_sub, map_smul, hu.2 t, hu.1 t, sub_self]
  · simp only [Nat.add_sub_cancel]
    abel
  · unfold innov
    rw [hu.1 (t + 1), hu.2 t]

/-- Cochrane (2023), p. 365 and Figure 16.1 (the response of the disturbance to `ε_{i,t+1}`):
`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`. -/
theorem innov_ar1 {η : ℝ} {u ε : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε)
    (hlaw : AR1Law η u ε) (t j : ℕ) : innov 𝔼 t (u (t + 1 + j)) = η ^ j • ε (t + 1) := by
  induction j with
  | zero =>
    rw [add_zero, hlaw t, innov_add, innov_smul, innov_of_known 𝔼 (hu t), innov_shock 𝔼 hε,
      smul_zero, zero_add, pow_zero, one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, hlaw, innov_add, innov_smul, ih,
      show t + 1 + j + 1 = t + 2 + j by omega, innov_shock_later 𝔼 hε, add_zero, smul_smul,
      pow_succ, mul_comm η]

/-- Cochrane (2023), p. 364: forecasts of an AR(1) at every horizon, `E_s u_{s+k} = ηᵏ u_s`
(restating `ExpectationSystem.ar1_iterate`), so the date-`s` forecast of `u_t` is
`η^{t−s} u_s` for `s ≤ t`. -/
theorem E_ar1_shift {η : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (u t) = η ^ (t - s) • u s := by
  have := 𝔼.ar1_iterate hu s (t - s)
  rwa [Nat.add_sub_cancel' hst] at this

/-! ### Innovations of infinite sums -/

/-- Cochrane (2023), eq. (2.17), p. 35, and (16.3), p. 364 (the fiscal shock is the innovation in
a present value): the innovation of a dominated infinite sum of random variables is the sum of
the innovations, `ΔE_{t+1} ∑ₖ fₖ = ∑ₖ ΔE_{t+1} fₖ`, for `|fₖ| ≤ cₖ` with `∑ cₖ < ∞`. -/
theorem innov_tsum {c : ℕ → ℝ} (hc : Summable c) {f : ℕ → Ω → ℝ} (hf : ∀ k ω, |f k ω| ≤ c k)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, innov 𝔼 t (f k) ω := by
  unfold innov
  rw [Pi.sub_apply, ForwardSolution.E_tsum_dom 𝔼 hc hf (t + 1) ω,
    ForwardSolution.E_tsum_dom 𝔼 hc hf t ω]
  have h1 : Summable (fun k => 𝔼.E (t + 1) (f k) ω) :=
    Summable.of_norm_bounded hc (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) (t + 1) ω)
  have h2 : Summable (fun k => 𝔼.E t (f k) ω) :=
    Summable.of_norm_bounded hc (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  rw [← h1.tsum_sub h2]
  rfl

/-! ### Genuine uncertainty -/

/-- Cochrane (2023), p. 364 and p. 373 (uncertainty examples): the coin-flip shock is adapted on
the coin-flip event tree. -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := by
  intro t
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- Cochrane (2023), (16.5), p. 364 ("sunspot shocks `δ_{t+1}` can erupt at any time"): on the
coin-flip event tree the coin shock is a shock in the sense of `IsShock` and it is not
identically zero, so shocks are not restricted to perfect foresight. -/
theorem coin_shock_ne_zero :
    IsShock ExpectationsFiniteTree.coinSystem ExpectationsFiniteTree.coinShock ∧
      ExpectationsFiniteTree.coinShock 1 ≠ 0 := by
  refine ⟨⟨fun t => coinShock_adapted (t + 1), ExpectationsFiniteTree.coinShock_mean_zero⟩,
    fun h => ?_⟩
  have := congrFun h (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.NewKeynesianSelection.Innovation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The simple fiscal-theory model of monetary policy, and Chapter 12

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5–2.6, eqs. (2.16)–(2.25),
pp. 34–42, the model that Chapter 16 reads differently (eqs. (16.1)–(16.3), p. 364); and the
precise claims of Chapter 12, "Interest-rate targets", pp. 324–328.

The first part is restated from the Chapter 2 project (`LinearFTMP`), adapted to the
`Cochrane.NewKeynesianSelection` names and to the `Innovation` module. Variables are deviations
from steady state; inflation, rates and shocks are random variables at each date; expectations
are an arbitrary `ExpectationSystem`.

The fiscal-theory equilibrium notion: given an adapted interest-rate path (or an interest-rate
rule with adapted disturbance), a fiscal shock `ε_{Σs}` (the innovation in the present value of
surpluses, `pvNews`) and initial inflation `π_0` (set by date-0 fiscal news), an equilibrium is
an ADAPTED inflation process satisfying the Fisher equation `i_t = E_t π_{t+1}` and the fiscal
condition `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date. No boundedness is imposed: the price
level is determined by the valuation equation, not by ruling out explosive paths.

## Main results

* (2.17): `pvNews`, `innov_forwardSeries`, `pvNews_isShock` (the fiscal shock is a shock).
* (2.19): `pegModel_iff`, `peg_existsUnique`, `pegSol_bounded`; `irf_peg_impact`,
  `irf_peg_later`, `expected_inflation_ahead`.
* p. 39: `passiveShock_isShock`, `passive_any_innovation` (under passive fiscal policy every
  innovation is an equilibrium).
* (2.20)–(2.25): `ruleModel_iff`, `eq224_iff`, `rule_existsUnique` (every `θ`), `rule_eq_peg`,
  `ruleSol_bounded`, `ruleSol_unbounded`.
* Chapter 12, P3 (p. 326, "a peg can be stable, determinate and quiet"): `peg_stable_determinate`,
  `peg_quiet`, `peg_unexpected_sq` (the conditional variance of unexpected inflation is that of
  the fiscal shock; volatile fiscal policy means volatile unexpected inflation).
* Chapter 12, P2 contrast (p. 325, Sargent–Wallace): `fisher_alone_any_innovation` (the Fisher
  equation alone leaves unexpected inflation arbitrary).
* Chapter 12, P4–P5 (p. 326), with a real rate `r_t`: `PegModelR`, `pegR_iff`,
  `pegR_existsUnique`, `pegR_expected` (`E_t π_{t+1} = i_t − r_t`: the real rate passes one for
  one into expected inflation), `real_rate_passthrough`, `zero_peg_deflation` and
  `peg_steady_state_iff` (a peg at zero gives the deflation `π = −r`).
* Chapter 12, P6 (p. 327, "if `φ > 1`, inflation is determinate but unstable"):
  `rule_expected_path` (`E_t π_{t+j} = φʲ π_t`), `rule_determinate_unstable`
  (unique equilibrium for every `φ`, yet `|E_t π_{t+j}| → ∞` whenever `π_t ≠ 0` and
  `|φ| > 1`), `rule_stable` (`|φ| < 1`: expected inflation converges to zero).
-/

namespace Cochrane.NewKeynesianSelection.FTPLSimple

open Filter Topology Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.17): fiscal news (restated from the Chapter 2 project) -/

/-- Cochrane (2023), eqs. (2.7) and (2.17), pp. 22, 35: for bounded surpluses and `0 ≤ β < 1`
the discounted forecasts `∑ βᵏ E_n s_{t+k}` are absolutely summable.
(Restated from the Chapter 2 project, `ExpectationTools.summable_E_shift`.) -/
theorem summable_E_shift {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (n t : ℕ) (ω : Ω) :
    Summable (fun k => β ^ k * 𝔼.E n (s (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) n ω) (pow_nonneg h0 k)

/-- Cochrane (2023), eq. (2.17), p. 35: the shock to the present value of (scaled) surpluses,
`ε_{Σs,t+1} = ΔE_{t+1} ∑_{j ≥ 0} βʲ s̃_{t+1+j} = ∑_{j ≥ 0} βʲ ΔE_{t+1} s̃_{t+1+j}`.
(Restated from the Chapter 2 project.) -/
noncomputable def pvNews (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω

/-- Cochrane (2023), eqs. (2.17)–(2.18), p. 35: `E_t PV_{t+1} = ∑_{k ≥ 0} βᵏ E_t s_{t+1+k}`, with
`PV_{t+1} = E_{t+1} ∑ βᵏ s_{t+1+k}` the forward series (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem E_forwardSeries_succ {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries β s (t + 1)) ω = ∑' k, β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
  have hb : ∀ k ω', |β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1 + k)) (t + 1) ω') (pow_nonneg h0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum h0 h1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • 𝔼.E (t + 1) (s (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (2.17), p. 35: the innovation in the present value of surpluses is the
discounted sum of the innovations in each future surplus,
`ΔE_{t+1} PV_{t+1} = ∑_{k ≥ 0} βᵏ ΔE_{t+1} s_{t+1+k}` (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem innov_forwardSeries {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    innov 𝔼 t (𝔼.forwardSeries β s (t + 1)) = pvNews 𝔼 β s t := by
  funext ω
  unfold innov pvNews
  rw [𝔼.forwardSeries_adapted h0 h1 hs (t + 1), Pi.sub_apply,
    E_forwardSeries_succ 𝔼 h0 h1 hs t ω]
  change ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω - _ = _
  rw [← (summable_E_shift 𝔼 h0 h1 hs (t + 1) (t + 1) ω).tsum_sub
    (summable_E_shift 𝔼 h0 h1 hs t (t + 1) ω)]
  refine tsum_congr fun k => ?_
  rw [← mul_sub]
  rfl

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal news `ε_{Σs,t+1}` is a shock in the sense of
p. 40 (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem pvNews_isShock {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : IsShock 𝔼 (fun t => match t with
      | 0 => 0
      | t + 1 => pvNews 𝔼 β s t) := by
  have hb : ∀ t k ω', |β ^ k * innov 𝔼 t (s (t + 1 + k)) ω'| ≤ β ^ k * (2 * M) := by
    intro t k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 k)
    unfold innov
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hs _) _ ω') (𝔼.abs_E_le (hs _) _ ω'))
  constructor
  · intro t
    funext ω
    change 𝔼.E (t + 1) (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum h0 h1 (hb t) (t + 1) ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E (t + 1) (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = _
    rw [map_smul, innov_known_next, Pi.smul_apply, smul_eq_mul]
  · intro t
    funext ω
    change 𝔼.E t (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0
    rw [𝔼.E_tsum h0 h1 (hb t) t ω]
    have : ∀ k, 𝔼.E t (fun ω' => β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0 := by
      intro k
      change 𝔼.E t (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = 0
      rw [map_smul, E_innov_zero, smul_zero, Pi.zero_apply]
    simp only [this, tsum_zero]

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35 (the linear model, variables as deviations from
steady state): `i_t = E_t π_{t+1}` and `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date.
(Restated from the Chapter 2 project.) -/
def PegModel (i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: for adapted inflation, an adapted rate path and a fiscal
shock, the model (2.16)–(2.17) holds iff `π_{t+1} = i_t − ε_{Σs,t+1}` at every date.
(Restated from the Chapter 2 project.) -/
theorem pegModel_iff {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hi : 𝔼.Adapted i)
    (hε : IsShock 𝔼 ε) : PegModel 𝔼 i ε π ↔ ∀ t, π (t + 1) = i t - ε (t + 1) := by
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), ← (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    have hE : 𝔼.E t (π (t + 1)) = i t := by
      rw [h t, map_sub, hi t, hε.2 t, sub_zero]
    refine ⟨hE.symm, ?_⟩
    unfold innov
    rw [hE, h t, map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]
    abel

/-- Cochrane (2023), eq. (2.19), p. 36: the solution `π_0` given, `π_{t+1} = i_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def pegSol (i ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => i t - ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: the solution is adapted.
(Restated from the Chapter 2 project.) -/
theorem pegSol_adapted {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (pegSol i ε π0) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t =>
    change 𝔼.E (t + 1) (i t - ε (t + 1)) = i t - ε (t + 1)
    rw [map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]

/-- Cochrane (2023), eq. (2.19), p. 36 ("the full solution of the model"): for EVERY adapted rate
path `i` and every fiscal shock `ε_{Σs}`, given `π_0` (set by date-0 fiscal news), the model
(2.16)–(2.17) has exactly one adapted solution. No boundedness is imposed.
(Restated from the Chapter 2 project.) -/
theorem peg_existsUnique {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModel 𝔼 i ε π := by
  have ha := pegSol_adapted 𝔼 h0 hi hε
  refine ⟨pegSol i ε π0, ⟨ha, rfl, (pegModel_iff 𝔼 ha hi hε).mpr fun t => rfl⟩, ?_⟩
  rintro π ⟨hπ, hπ0, hm⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hm
  funext t
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), pp. 33, 37 ("inflation is stable under an interest-rate target"): with
bounded `π_0`, rates and shocks the solution (2.19) is bounded.
(Restated from the Chapter 2 project.) -/
theorem pegSol_bounded {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} {A Bi Be : ℝ} (h0 : ∀ ω, |π0 ω| ≤ A)
    (hi : ∀ t ω, |i t ω| ≤ Bi) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (pegSol i ε π0) := by
  refine ⟨|A| + |Bi| + |Be|, fun t ω => ?_⟩
  cases t with
  | zero =>
    have := (h0 ω).trans (le_abs_self A)
    change |π0 ω| ≤ _
    linarith [abs_nonneg Bi, abs_nonneg Be]
  | succ t =>
    change |i t ω - ε (t + 1) ω| ≤ _
    have h1 := (hi t ω).trans (le_abs_self Bi)
    have h2 := (hε (t + 1) ω).trans (le_abs_self Be)
    linarith [abs_sub (i t ω) (ε (t + 1) ω), abs_nonneg A]

/-- Cochrane (2023), Figure 2.1 and p. 36 ("there is no unexpected time-`t` inflation without a
fiscal shock"): on impact, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever the rate news.
(Restated from the Chapter 2 project.) -/
theorem irf_peg_impact {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  rw [h t, innov_sub, innov_of_known 𝔼 (hi t)]
  unfold innov
  rw [hε.1 t, hε.2 t]
  abel

/-- Cochrane (2023), Figure 2.1 and p. 36 ("inflation moves up one period later"): after impact
the inflation response is the rate response one period earlier,
`ΔE_{t+1} π_{t+2+j} = ΔE_{t+1} i_{t+1+j}`.
(Restated from the Chapter 2 project.) -/
theorem irf_peg_later {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 2 + j)) = innov 𝔼 t (i (t + 1 + j)) := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e, h, innov_sub, ← e, innov_shock_later 𝔼 hε, sub_zero]

/-- Cochrane (2023), p. 36 ("If `E_{t−k} i_t` rises, then `E_{t−k} π_{t+1}` rises"): for every
`s ≤ t`, `E_s π_{t+1} = E_s i_t`.
(Restated from the Chapter 2 project.) -/
theorem expected_inflation_ahead {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (π (t + 1)) = 𝔼.E s (i t) := by
  rw [h t, map_sub, ← 𝔼.tower hst (ε (t + 1)), hε.2 t, map_zero, sub_zero]

/-- Cochrane (2023), p. 39: the passive fiscal policy of the new-Keynesian reading,
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` "in response to whatever inflation happens".
(Restated from the Chapter 2 project.) -/
def passiveShock (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -innov 𝔼 t (π (t + 1))

/-- Cochrane (2023), p. 39 and (16.3), p. 364: the passive fiscal response
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` to any inflation process is a shock. -/
theorem passiveShock_isShock (π : ℕ → Ω → ℝ) : IsShock 𝔼 (passiveShock 𝔼 π) :=
  ⟨fun t => by simp only [passiveShock, map_neg, innov_known_next],
    fun t => by simp only [passiveShock, map_neg, E_innov_zero, neg_zero]⟩

/-- Cochrane (2023), p. 39: under passive fiscal policy the valuation equation holds for every
inflation path satisfying the Fisher equation.
(Restated from the Chapter 2 project.) -/
theorem passive_valuation_holds {i π : ℕ → Ω → ℝ} (hfis : ∀ t, i t = 𝔼.E t (π (t + 1))) :
    PegModel 𝔼 i (passiveShock 𝔼 π) π := fun t => ⟨hfis t, by
      change _ = -(-innov 𝔼 t (π (t + 1)))
      rw [neg_neg]⟩

/-- Cochrane (2023), p. 39 ("The bank threatens hyperinflation for any but one value of
unexpected inflation"): with passive fiscal policy, EVERY shock `ν` is an equilibrium inflation
innovation: `π_{t+1} = i_t + ν_{t+1}` is adapted, satisfies the model with the passive fiscal
response, and has `ΔE_{t+1} π_{t+1} = ν_{t+1}`.
(Restated from the Chapter 2 project.) -/
theorem passive_any_innovation {i ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hν : IsShock 𝔼 ν) :
    𝔼.Adapted (pegSol i (fun t => -ν t) π0) ∧
      PegModel 𝔼 i (passiveShock 𝔼 (pegSol i (fun t => -ν t) π0)) (pegSol i (fun t => -ν t) π0) ∧
      ∀ t, innov 𝔼 t (pegSol i (fun t => -ν t) π0 (t + 1)) = ν (t + 1) := by
  have hs : IsShock 𝔼 (fun t => -ν t) :=
    ⟨fun t => by rw [map_neg, hν.1 t], fun t => by rw [map_neg, hν.2 t, neg_zero]⟩
  have ha := pegSol_adapted 𝔼 h0 hi hs
  have hm := (pegModel_iff 𝔼 ha hi hs).mpr fun t => rfl
  refine ⟨ha, passive_valuation_holds 𝔼 fun t => (hm t).1, fun t => ?_⟩
  rw [(hm t).2, neg_neg]

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and the Taylor-type rule `i_t = θ π_t + u_t`.
(Restated from the Chapter 2 project.) -/
def RuleModel (θ : ℝ) (i u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1) ∧ i t = θ • π t + u t

/-- Cochrane (2023), eq. (2.23), p. 40: the serially correlated disturbance
`u_t = η u_{t−1} + ε_{i,t}`.
(Restated from the Chapter 2 project.) -/
def Disturbance (η : ℝ) (u εi : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + εi (t + 1)

/-- Cochrane (2023), eq. (2.24) with (2.21), p. 40: `E_t π_{t+1} = θ π_t + u_t` and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def Eq224 (θ : ℝ) (u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eqs. (2.20)–(2.24), p. 40 ("Eliminating the interest rate"): the model
(2.20)–(2.22) holds iff the rate is given by the rule and inflation satisfies (2.24), (2.21).
(Restated from the Chapter 2 project.) -/
theorem ruleModel_iff {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} :
    RuleModel 𝔼 θ i u ε π ↔ (∀ t, i t = θ • π t + u t) ∧ Eq224 𝔼 θ u ε π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2.2, fun t => ⟨(h t).1.symm.trans (h t).2.2, (h t).2.1⟩⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).1.symm, (h t).2, hi t⟩

/-- Cochrane (2023), eq. (2.25), p. 40: for adapted inflation and disturbance and a fiscal shock,
(2.24) with (2.21) holds iff `π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
theorem eq224_iff {θ : ℝ} {u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) :
    Eq224 𝔼 θ u ε π ↔ ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1) := by
  have hk : ∀ t, 𝔼.E t (θ • π t + u t) = θ • π t + u t := fun t => by
    rw [map_add, map_smul, hπ t, hu t]
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    refine ⟨?_, ?_⟩
    · rw [h t, map_sub, hk t, hε.2 t, sub_zero]
    · rw [h t, innov_sub, innov_of_known 𝔼 (hk t), innov_shock 𝔼 hε, zero_sub]

/-- Cochrane (2023), eq. (2.25), p. 40: the solution `π_0` given,
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def ruleSol (θ : ℝ) (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => θ • ruleSol θ u ε π0 t + u t - ε (t + 1)

/-- Cochrane (2023), eq. (2.25), p. 40: the solution is adapted.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_adapted {θ : ℝ} {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (ruleSol θ u ε π0) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    change 𝔼.E (t + 1) (θ • ruleSol θ u ε π0 t + u t - ε (t + 1)) = _
    rw [map_sub, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t), hε.1 t]
    rfl

/-- Cochrane (2023), eqs. (2.20)–(2.25), p. 40, the fiscal-theory point of §2.6: for EVERY rule
coefficient `θ ∈ ℝ` (no Taylor principle), every adapted disturbance `u` and every fiscal shock,
given `π_0`, there is exactly one equilibrium `(π, i)` of (2.20)–(2.22) with `π` adapted.
(Restated from the Chapter 2 project.) -/
theorem rule_existsUnique (θ : ℝ) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
      RuleModel 𝔼 θ q.2 u ε q.1 := by
  have ha := ruleSol_adapted 𝔼 (θ := θ) h0 hu hε
  refine ⟨(ruleSol θ u ε π0, fun t => θ • ruleSol θ u ε π0 t + u t), ⟨ha, rfl, ?_⟩, ?_⟩
  · exact (ruleModel_iff 𝔼).mpr ⟨fun t => rfl, (eq224_iff 𝔼 ha hu hε).mpr fun t => rfl⟩
  · rintro ⟨π, i⟩ ⟨hπ, hπ0, hm⟩
    obtain ⟨hi, h224⟩ := (ruleModel_iff 𝔼).mp hm
    have h := (eq224_iff 𝔼 hπ hu hε).mp h224
    dsimp only at hπ0 hi h
    have hπeq : π = ruleSol θ u ε π0 := by
      funext t
      induction t with
      | zero => exact hπ0
      | succ t ih =>
        rw [h t, ih]
        rfl
    refine Prod.ext hπeq ?_
    funext t
    change i t = θ • ruleSol θ u ε π0 t + u t
    rw [hi t, hπeq]

/-- Cochrane (2023), p. 40 ("if we had fed the equilibrium `{i_t}` response ... into the
calculation (2.19) ... as if that path were an exogenous time-varying peg, we would have obtained
the same result"): a solution of the rule model solves the peg model (2.16)–(2.17) with the
equilibrium rate, and equals the peg solution (2.19) for that rate.
(Restated from the Chapter 2 project.) -/
theorem rule_eq_peg {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) (hm : RuleModel 𝔼 θ i u ε π) :
    PegModel 𝔼 i ε π ∧ π = pegSol i ε (π 0) := by
  have hpeg : PegModel 𝔼 i ε π := fun t => ⟨(hm t).1, (hm t).2.1⟩
  have hi : 𝔼.Adapted i := fun t => by rw [(hm t).2.2, map_add, map_smul, hπ t, hu t]
  refine ⟨hpeg, ?_⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hpeg
  funext t
  cases t with
  | zero => rfl
  | succ t => exact h t

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| < 1` and bounded `π_0`, disturbance and
shocks, the equilibrium (2.25) is bounded.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_bounded {θ A Bu Be : ℝ} (hθ : |θ| < 1) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : ∀ ω, |π0 ω| ≤ A) (hu : ∀ t ω, |u t ω| ≤ Bu) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (ruleSol θ u ε π0) := by
  set K := |A| + (|Bu| + |Be|) / (1 - |θ|) with hK
  have h1 : 0 < 1 - |θ| := by linarith
  have hfrac : 0 ≤ (|Bu| + |Be|) / (1 - |θ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self A).trans (by linarith))
  | succ t ih =>
    intro ω
    change |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω| ≤ K
    have ha : |θ * ruleSol θ u ε π0 t ω| ≤ |θ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hu t ω).trans (le_abs_self Bu)
    have hc := (hε (t + 1) ω).trans (le_abs_self Be)
    have hKe : K * (1 - |θ|) = |A| * (1 - |θ|) + (|Bu| + |Be|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |A| * (1 - |θ|) := mul_nonneg (abs_nonneg A) h1.le
    calc |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω|
        ≤ |θ * ruleSol θ u ε π0 t ω + u t ω| + |ε (t + 1) ω| := abs_sub _ _
      _ ≤ |θ * ruleSol θ u ε π0 t ω| + |u t ω| + |ε (t + 1) ω| := by
          gcongr; exact abs_add_le _ _
      _ ≤ K := by nlinarith

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| > 1` the equilibrium is unbounded as soon
as inflation starts away from zero (no disturbances or shocks: `π_t = θᵗ π_0`), so the
linearisation of §2.5 is not justified along it; the equilibrium still exists and is unique.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_unbounded {θ : ℝ} (hθ : 1 < |θ|) {π0 : Ω → ℝ} {ω : Ω} (hω : π0 ω ≠ 0) :
    ¬ BoundedProc (ruleSol θ 0 0 π0) := by
  have hpow : ∀ t, ruleSol θ 0 0 π0 t ω = θ ^ t * π0 ω := by
    intro t
    induction t with
    | zero => simp [ruleSol]
    | succ t ih =>
      change θ * ruleSol θ 0 0 π0 t ω + 0 - 0 = _
      rw [ih, pow_succ]
      ring
  rintro ⟨M, hM⟩
  have hpos : 0 < |π0 ω| := abs_pos.mpr hω
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hθ).eventually_gt_atTop
    (M / |π0 ω|)).exists
  have h1 := hM t ω
  rw [hpow t, abs_mul, abs_pow] at h1
  rw [div_lt_iff₀ hpos] at ht
  linarith

/-! ### Chapter 12, P3: a peg can be stable, determinate and quiet -/

/-- Cochrane (2023), §12.1, p. 326 (P3: "an interest-rate peg can leave the price level and
inflation stable, determinate, and quiet"): under a peg, for every adapted rate path, every
fiscal shock and every `π_0` there is exactly one equilibrium (determinate); it is bounded when
the rate path, the shock and `π_0` are (stable); and its unexpected inflation is minus the fiscal
shock, whatever the rate path. -/
theorem peg_stable_determinate {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} {A Bi Be : ℝ}
    (h0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) (hA : ∀ ω, |π0 ω| ≤ A)
    (hBi : ∀ t ω, |i t ω| ≤ Bi) (hBe : ∀ t ω, |ε t ω| ≤ Be) :
    (∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModel 𝔼 i ε π) ∧ BoundedProc (pegSol i ε π0) ∧
      ∀ t, innov 𝔼 t (pegSol i ε π0 (t + 1)) = -ε (t + 1) :=
  ⟨peg_existsUnique 𝔼 h0 hi hε, pegSol_bounded hA hBi hBe,
    irf_peg_impact 𝔼 hi hε (fun _ => rfl)⟩

/-- Cochrane (2023), §12.1, p. 326 ("quiet (the opposite of volatile)"): with no fiscal news
there is no unexpected inflation under a peg, and inflation `π_{t+1} = i_t` is known one period
ahead. -/
theorem peg_quiet {i π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hi : 𝔼.Adapted i)
    (hm : PegModel 𝔼 i 0 π) (t : ℕ) : innov 𝔼 t (π (t + 1)) = 0 ∧ π (t + 1) = i t := by
  have h := (pegModel_iff 𝔼 hπ hi (isShock_zero 𝔼)).mp hm t
  refine ⟨?_, by rw [h, Pi.zero_apply, sub_zero]⟩
  rw [(hm t).2, Pi.zero_apply, neg_zero]

/-- Cochrane (2023), §12.1, p. 326 (P3: "Countries with volatile fiscal policies ... will see
volatile unexpected inflation under a peg"): the conditional variance of unexpected inflation
equals that of the fiscal shock, `E_t[(ΔE_{t+1} π_{t+1})²] = E_t[ε_{Σs,t+1}²]` (both have
conditional mean zero). -/
theorem peg_unexpected_sq {i ε π : ℕ → Ω → ℝ} (hm : PegModel 𝔼 i ε π) (t : ℕ) :
    𝔼.E t (innov 𝔼 t (π (t + 1)) ^ 2) = 𝔼.E t (ε (t + 1) ^ 2) ∧
      𝔼.E t (innov 𝔼 t (π (t + 1))) = 0 := by
  refine ⟨?_, E_innov_zero 𝔼 t _⟩
  rw [(hm t).2, neg_sq]

/-! ### Chapter 12, P2: the Fisher equation alone (Sargent and Wallace) -/

/-- Cochrane (2023), §12.1, p. 325 (P2, Sargent and Wallace: "unexpected inflation `ΔE_{t+1}π_{t+1}`
can be anything; it is indeterminate"): the Fisher equation alone, under a peg, leaves
unexpected inflation free: for every shock `δ` and every `π_0`, `π_{t+1} = i_t + δ_{t+1}` is
adapted, satisfies `i_t = E_t π_{t+1}`, and has `ΔE_{t+1} π_{t+1} = δ_{t+1}`. -/
theorem fisher_alone_any_innovation {i δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hδ : IsShock 𝔼 δ) :
    𝔼.Adapted (pegSol i (fun t => -δ t) π0) ∧
      (∀ t, i t = 𝔼.E t (pegSol i (fun t => -δ t) π0 (t + 1))) ∧
      ∀ t, innov 𝔼 t (pegSol i (fun t => -δ t) π0 (t + 1)) = δ (t + 1) := by
  obtain ⟨ha, hm, hinn⟩ := passive_any_innovation 𝔼 h0 hi hδ
  exact ⟨ha, fun t => (hm t).1, hinn⟩

/-- Cochrane (2023), §12.1, p. 325 (P2): without the fiscal condition the peg is indeterminate:
the adapted solutions of the Fisher equation `i_t = E_t π_{t+1}` form an uncountable set (already
the initial inflation `π_0` is free). -/
theorem fisher_alone_not_countable [Nonempty Ω] {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) :
    ¬ {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ ∀ t, i t = 𝔼.E t (π (t + 1))}.Countable := by
  intro hc
  let f : ℝ → ℕ → Ω → ℝ := fun c => pegSol i 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ
      {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ ∀ t, i t = 𝔼.E t (π (t + 1))} := by
    intro c _
    have ha := pegSol_adapted 𝔼 (𝔼.const 0 c) hi (isShock_zero 𝔼)
    have hm := (pegModel_iff 𝔼 ha hi (isShock_zero 𝔼)).mpr fun t => rfl
    exact ⟨ha, fun t => (hm t).1⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-! ### Chapter 12, P4–P5: a real interest rate -/

/-- Cochrane (2023), §12.1, pp. 324–326 (the Fisher relation `i_t = r_t + E_t π_{t+1}` with a
real rate `r_t`) with (2.21): the peg model with a real rate. -/
def PegModelR (r i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), §12.1, p. 326: for adapted inflation, real rate and nominal rate and a
fiscal shock, the model holds iff `π_{t+1} = i_t − r_t − ε_{Σs,t+1}`. -/
theorem pegR_iff {r i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hr : 𝔼.Adapted r)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    PegModelR 𝔼 r i ε π ↔ ∀ t, π (t + 1) = i t - r t - ε (t + 1) := by
  constructor
  · intro h t
    have hE : 𝔼.E t (π (t + 1)) = i t - r t := eq_sub_of_add_eq' (h t).1.symm
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), hE, (h t).2]
    abel
  · intro h t
    have hk : 𝔼.E t (i t - r t) = i t - r t := by rw [map_sub, hi t, hr t]
    have hE : 𝔼.E t (π (t + 1)) = i t - r t := by
      rw [h t, map_sub, hk, hε.2 t, sub_zero]
    refine ⟨by rw [hE]; abel, ?_⟩
    rw [h t, innov_sub, innov_of_known 𝔼 hk, innov_shock 𝔼 hε, zero_sub]

/-- Cochrane (2023), §12.1, p. 326 (P4–P5: a peg is determinate with a time-varying real rate):
for every adapted real rate, peg path, fiscal shock and `π_0` there is exactly one equilibrium. -/
theorem pegR_existsUnique {r i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hr : 𝔼.Adapted r) (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModelR 𝔼 r i ε π := by
  have hir : 𝔼.Adapted (fun t => i t - r t) := fun t => by
    simp only [map_sub, hi t, hr t]
  have ha := pegSol_adapted 𝔼 h0 hir hε
  refine ⟨pegSol (fun t => i t - r t) ε π0,
    ⟨ha, rfl, (pegR_iff 𝔼 ha hr hi hε).mpr fun t => rfl⟩, ?_⟩
  rintro π ⟨hπ, hπ0, hm⟩
  have h := (pegR_iff 𝔼 hπ hr hi hε).mp hm
  funext t
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), §12.1, p. 325 ("If the central bank pegs the interest rate `i`, then
`E_t π_{t+1}` settles down to `i − r` all on its own") and p. 326 (P5): in every equilibrium,
`E_t π_{t+1} = i_t − r_t`. -/
theorem pegR_expected {r i ε π : ℕ → Ω → ℝ} (hm : PegModelR 𝔼 r i ε π) (t : ℕ) :
    𝔼.E t (π (t + 1)) = i t - r t :=
  eq_sub_of_add_eq' (hm t).1.symm

/-- Cochrane (2023), §12.1, p. 326 (P5: "Under a peg, variation in the real rate of interest
`r_t` ... must express itself in varying expected inflation"): with the same peg, two real-rate
paths move expected inflation one for one, `E_t π'_{t+1} − E_t π_{t+1} = −(r'_t − r_t)`. -/
theorem real_rate_passthrough {r r' i ε ε' π π' : ℕ → Ω → ℝ} (hm : PegModelR 𝔼 r i ε π)
    (hm' : PegModelR 𝔼 r' i ε' π') (t : ℕ) :
    𝔼.E t (π' (t + 1)) - 𝔼.E t (π (t + 1)) = -(r' t - r t) := by
  rw [pegR_expected 𝔼 hm, pegR_expected 𝔼 hm']
  abel

/-- Cochrane (2023), §12.1, p. 326 (P4: "Even a peg at zero interest rate can work. If the
economy demands a positive real rate of interest, a slight deflation would emerge"): with
`i ≡ 0`, a constant real rate `r̄` and no fiscal shocks, every equilibrium has
`π_{t+1} = −r̄`. -/
theorem zero_peg_deflation {rbar : ℝ} {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : PegModelR 𝔼 (fun _ _ => rbar) 0 0 π) (t : ℕ) : π (t + 1) = fun _ => -rbar := by
  have hr : 𝔼.Adapted (fun _ _ => rbar) := fun t => 𝔼.const t rbar
  have hi0 : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have h := (pegR_iff 𝔼 hπ hr hi0 (isShock_zero 𝔼)).mp hm t
  rw [h]
  funext ω
  simp

/-- Cochrane (2023), §12.1, p. 326 (P4): the steady states of a peg `ī` with constant real rate
`r̄` and no fiscal shocks are exactly `π̄ = ī − r̄`; for the peg at zero, `π̄ = −r̄`. -/
theorem peg_steady_state_iff [Nonempty Ω] {rbar ibar pibar : ℝ} :
    PegModelR 𝔼 (fun _ _ => rbar) (fun _ _ => ibar) 0 (fun _ _ => pibar) ↔
      pibar = ibar - rbar := by
  constructor
  · intro h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have h1 := congrFun (h 0).1 ω
    rw [𝔼.const] at h1
    simp only [Pi.add_apply] at h1
    linarith
  · intro h t
    refine ⟨?_, ?_⟩
    · rw [𝔼.const]
      funext ω
      simp only [Pi.add_apply]
      linarith
    · rw [innov_const, Pi.zero_apply, neg_zero]

/-! ### Chapter 12, P6: `i_t = φ π_t` is determinate but unstable for `φ > 1` -/

/-- Cochrane (2023), §12.2, p. 327 (P6: "with `i_t = φπ_t` and `i_t = E_tπ_{t+1}`, equilibrium is
`E_tπ_{t+1} = φπ_t`"): in every equilibrium of the rule model with no disturbance,
`E_t π_{t+j} = φʲ π_t`. -/
theorem rule_expected_path {φ : ℝ} {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : RuleModel 𝔼 φ i 0 ε π) (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t := by
  induction j with
  | zero => simpa using hπ t
  | succ j ih =>
    have h1 : 𝔼.E (t + j) (π (t + j + 1)) = φ • π (t + j) := by
      rw [← (hm (t + j)).1, (hm (t + j)).2.2, Pi.zero_apply, add_zero]
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j), h1, map_smul, ih, smul_smul]
    congr 1
    ring

/-- Cochrane (2023), §12.2, p. 327 (P6: "If `φ > 1`, inflation is determinate but unstable"):
for `|φ| > 1` the fiscal-theory equilibrium exists and is unique given `π_0` and the fiscal shock
(determinate), yet in every equilibrium expected inflation explodes,
`|E_t π_{t+j}| → ∞`, at every date and state where `π_t ≠ 0` (unstable). -/
theorem rule_determinate_unstable {φ : ℝ} (hφ : 1 < |φ|) {ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : 𝔼.E 0 π0 = π0) (hε : IsShock 𝔼 ε) :
    (∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
      RuleModel 𝔼 φ q.2 0 ε q.1) ∧
    ∀ {i π : ℕ → Ω → ℝ}, 𝔼.Adapted π → RuleModel 𝔼 φ i 0 ε π → ∀ t ω, π t ω ≠ 0 →
      Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  refine ⟨rule_existsUnique 𝔼 φ h0 (fun t => by simp) hε, fun {i π} hπ hm t ω hω => ?_⟩
  have e : (fun j => |𝔼.E t (π (t + j)) ω|) = fun j => |φ| ^ j * |π t ω| := by
    funext j
    rw [rule_expected_path 𝔼 hπ hm t j, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hω)

/-- Cochrane (2023), §12.2, p. 327 (P6, the passive case): for `|φ| < 1` expected inflation
converges to zero in every equilibrium, `E_t π_{t+j} → 0` (stable), while the equilibrium is
still unique given the fiscal shock (`rule_existsUnique`). -/
theorem rule_stable {φ : ℝ} (hφ : |φ| < 1) {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : RuleModel 𝔼 φ i 0 ε π) (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π (t + j)) ω) = fun j => φ ^ j * π t ω := by
    funext j
    rw [rule_expected_path 𝔼 hπ hm t j, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π t ω)

end Cochrane.NewKeynesianSelection.FTPLSimple

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The simplest new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.1 "The simplest model",
eqs. (16.1)–(16.11) and Figure 16.1, pp. 363–366.

The model is `i_t = E_t π_{t+1}` (16.1), `i_t = φ π_t + u_t` (16.2) and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` (16.3), the same equations as the simplest fiscal-theory model
(`FTPLSimple.RuleModel`). The new-Keynesian reading makes fiscal policy passive, so (16.3) only
determines surpluses; the remaining condition is (16.4) `E_t π_{t+1} = φ π_t + u_t`. Its
equilibria are indexed by `π_0` and a sunspot shock `δ` (16.5). Selection rules out paths whose
expectations explode.

The equilibrium notions used here: an *equilibrium* of (16.4) is an adapted inflation process
satisfying (16.4) at every date; it is *locally bounded* (the new-Keynesian selection) when it is
a bounded process. The model is *determinate* when for every bounded adapted disturbance there
is exactly one bounded equilibrium.

## Main results

* (16.1)–(16.4): `nk_iff` (eliminating `i_t`); `passive_163` and `nk_passive_iff` (with passive
  fiscal policy (16.3) imposes nothing); `nk_with_163_iff_ruleModel` (with an exogenous fiscal
  shock the equations are exactly the fiscal-theory model).
* (16.5): `nkSol`, `nkSol_solves`, `eq164_iff_165`, `eq_nkSol`, `nkSol_inj`,
  `equilibria_bijOn` — the equilibria are in bijection with the pairs `(π_0, δ)`.
* `|φ| < 1` (p. 364, stable but indeterminate): `expected_succ`, `expected_bounded`
  (`E_t π_{t+j}` bounded in `j`), `expected_const_converges` (converges for any initial value),
  `converges_needs_convergent_u` (for a general bounded disturbance only boundedness holds),
  `sunspot_expected` and `sunspot_fades`, `indeterminate_of_abs_lt_one` (uncountably many
  bounded equilibria), `coin_sunspot` (a genuinely random sunspot equilibrium).
* `|φ| > 1` (p. 364, (16.6)): `fwdSol`, `fwdSol_apply` (`π_t = −∑ φ^{−(j+1)} E_t u_{t+j}`),
  `eq164_unique`, `fwdSol_existsUnique` (the unique bounded equilibrium),
  `explodes_of_ne_fwdSol` (every other
  equilibrium has `|E_t π_{t+j}| → ∞`), `determinate_iff` (determinate iff `|φ| > 1`, so
  `φ < −1` works as well as `φ > 1`).
* AR(1) disturbances (pp. 364–365): `ar1Pi`, `ar1Pi_eq164`, `ar1Pi_adapted`,
  `ar1Pi_bounded`, `ar1_solution` ((16.9) `π_t = −u_t/(φ − η)`),
  `ar1_rate` ((16.11)), `ar1_law_1610` ((16.10)), `ar1_selection` ((16.7)), `irf_ar1`.
* (16.8), the Wicksellian rule: `WicksellModel`, `wicksell_iff`, `wicksell_existsUnique`,
  `wicksell_apply` (`p_t = p* − ∑ (1+φ_p)^{−(j+1)} E_t u_{t+j}`), `wicksell_determinate_iff`
  (iff `φ_p > 0` or `φ_p < −2`), `printed_wicksell_false` (survey error E4: the printed formula
  with `1 + φ` is not a solution).
* Figure 16.1 (`φ = 1.25`, `η = 0.8`): `fig161_values`, `fig161_reverts`.
-/

namespace Cochrane.NewKeynesianSelection.SimplestModel

open Filter Topology Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (16.1)–(16.4) -/

/-- Cochrane (2023), eqs. (16.1)–(16.2), p. 364: the Fisher equation `i_t = E_t π_{t+1}` and the
Taylor-type rule `i_t = φ π_t + u_t` at every date. -/
def NKModel (φ : ℝ) (u i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ i t = φ • π t + u t

/-- Cochrane (2023), eq. (16.4), p. 364: the single equilibrium condition
`E_t π_{t+1} = φ π_t + u_t`. -/
def Eq164 (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + u t

/-- Cochrane (2023), eq. (16.4), p. 364 ("We then eliminate `i_t` from (16.1)–(16.2)"): the model
holds iff the rate is given by the rule and inflation satisfies (16.4). -/
theorem nk_iff {φ : ℝ} {u i π : ℕ → Ω → ℝ} :
    NKModel 𝔼 φ u i π ↔ (∀ t, i t = φ • π t + u t) ∧ Eq164 𝔼 φ u π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2, fun t => (h t).1.symm.trans (h t).2⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).symm, hi t⟩

/-- Cochrane (2023), eq. (16.3), p. 364 (passive fiscal policy: "(16.3) determines surpluses
`ε_{Σs,t+1}` for any unexpected inflation"): for every inflation process the passive fiscal shock
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` (`FTPLSimple.passiveShock`) is a shock and (16.3) holds with
it. -/
theorem passive_163 (π : ℕ → Ω → ℝ) :
    IsShock 𝔼 (FTPLSimple.passiveShock 𝔼 π) ∧
      ∀ t, innov 𝔼 t (π (t + 1)) = -FTPLSimple.passiveShock 𝔼 π (t + 1) := by
  refine ⟨FTPLSimple.passiveShock_isShock 𝔼 π, fun t => ?_⟩
  change _ = -(-innov 𝔼 t (π (t + 1)))
  rw [neg_neg]

/-- Cochrane (2023), p. 364 ("As (16.3) then does not influence the rest of the model ... we have
a single equilibrium condition (16.4)"): with passive fiscal policy, (16.1)–(16.3) hold iff
(16.1)–(16.2) hold. -/
theorem nk_passive_iff {φ : ℝ} {u i π : ℕ → Ω → ℝ} :
    (NKModel 𝔼 φ u i π ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -FTPLSimple.passiveShock 𝔼 π (t + 1)) ↔
      NKModel 𝔼 φ u i π :=
  ⟨fun h => h.1, fun h => ⟨h, (passive_163 𝔼 π).2⟩⟩

/-- Cochrane (2023), p. 364 ("the same set of equations as the simplest fiscal theory of monetary
policy model from Sections 2.5 and 2.6"): with an exogenous fiscal shock `ε`, (16.1)–(16.3) are
exactly the fiscal-theory rule model (2.20)–(2.22). -/
theorem nk_with_163_iff_ruleModel {φ : ℝ} {u i ε π : ℕ → Ω → ℝ} :
    (NKModel 𝔼 φ u i π ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -ε (t + 1)) ↔
      FTPLSimple.RuleModel 𝔼 φ i u ε π := by
  constructor
  · rintro ⟨h, h3⟩ t
    exact ⟨(h t).1, h3 t, (h t).2⟩
  · intro h
    exact ⟨fun t => ⟨(h t).1, (h t).2.2⟩, fun t => (h t).2.1⟩

/-! ### (16.5): the equilibria -/

/-- Cochrane (2023), eq. (16.5), p. 364: `π_0` given and `π_{t+1} = φ π_t + u_t + δ_{t+1}`. -/
def nkSol (φ : ℝ) (u δ : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => φ • nkSol φ u δ π0 t + u t + δ (t + 1)

/-- Cochrane (2023), eq. (16.5), p. 364: the family (16.5) is the fiscal-theory solution (2.25)
with the fiscal shock `ε_{Σs} = −δ`. -/
theorem nkSol_eq_ruleSol (φ : ℝ) (u δ : ℕ → Ω → ℝ) (π0 : Ω → ℝ) :
    nkSol φ u δ π0 = FTPLSimple.ruleSol φ u (fun t => -δ t) π0 := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change φ • nkSol φ u δ π0 t + u t + δ (t + 1) =
      φ • FTPLSimple.ruleSol φ u (fun t => -δ t) π0 t + u t - -δ (t + 1)
    rw [ih, sub_neg_eq_add]

/-- Cochrane (2023), eq. (16.5), p. 364: the members of (16.5) are adapted. -/
theorem nkSol_adapted {φ : ℝ} {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hδ : IsShock 𝔼 δ) : 𝔼.Adapted (nkSol φ u δ π0) := by
  have hs : IsShock 𝔼 (fun t => -δ t) :=
    ⟨fun t => by rw [map_neg, hδ.1 t], fun t => by rw [map_neg, hδ.2 t, neg_zero]⟩
  rw [nkSol_eq_ruleSol]
  exact FTPLSimple.ruleSol_adapted 𝔼 h0 hu hs

/-- Cochrane (2023), eq. (16.5), p. 364: every member of (16.5), for any `π_0` and any shock `δ`
(`E_t δ_{t+1} = 0`), is an equilibrium of (16.4). -/
theorem nkSol_solves {φ : ℝ} {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hδ : IsShock 𝔼 δ) : Eq164 𝔼 φ u (nkSol φ u δ π0) := by
  intro t
  have ha := nkSol_adapted 𝔼 (φ := φ) h0 hu hδ
  change 𝔼.E t (φ • nkSol φ u δ π0 t + u t + δ (t + 1)) = _
  rw [map_add, map_add, map_smul, ha t, hu t, hδ.2 t, add_zero]

/-- Cochrane (2023), eq. (16.5), p. 364: an adapted process satisfies (16.4) iff
`π_{t+1} = φ π_t + u_t + δ_{t+1}` with `δ` its own innovation process. -/
theorem eq164_iff_165 {φ : ℝ} {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 φ u π ↔ ∀ t, π (t + 1) = φ • π t + u t + innovProc 𝔼 π (t + 1) := by
  constructor
  · intro h t
    rw [← h t]
    exact eq_E_add_innovProc 𝔼 hπ t
  · intro h t
    rw [h t, map_add, map_add, map_smul, hπ t, hu t]
    rw [show innovProc 𝔼 π (t + 1) = innov 𝔼 t (π (t + 1)) from rfl, E_innov_zero, add_zero]

/-- Cochrane (2023), eq. (16.5), p. 364 ("Multiple equilibria are indexed by arbitrary initial
inflation `π_0`, and by the arbitrary random variables or sunspots `δ_{t+1}`"): every equilibrium
is the member of (16.5) with its own `π_0` and its own innovations. -/
theorem eq_nkSol {φ : ℝ} {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (h : Eq164 𝔼 φ u π) : π = nkSol φ u (innovProc 𝔼 π) (π 0) := by
  have h' := (eq164_iff_165 𝔼 hπ hu).mp h
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [h' t, ih]
    rfl

/-- Cochrane (2023), eq. (16.5), p. 364: different indices give different equilibria: if two
members of (16.5) agree, their `π_0` and their sunspots `δ_{t+1}` agree. -/
theorem nkSol_inj {φ : ℝ} {u δ δ' : ℕ → Ω → ℝ} {π0 π0' : Ω → ℝ}
    (h : nkSol φ u δ π0 = nkSol φ u δ' π0') : π0 = π0' ∧ ∀ t, δ (t + 1) = δ' (t + 1) := by
  refine ⟨congrFun h 0, fun t => ?_⟩
  have h1 := congrFun h (t + 1)
  have h2 := congrFun h t
  change φ • nkSol φ u δ π0 t + u t + δ (t + 1) = φ • nkSol φ u δ' π0' t + u t + δ' (t + 1)
    at h1
  rw [h2] at h1
  exact add_left_cancel h1

/-- Cochrane (2023), eq. (16.5), p. 364: the equilibria of (16.4) are in bijection with the pairs
`(π_0, δ)` of a date-0 known initial inflation and a shock (normalised by `δ_0 = 0`). -/
theorem equilibria_bijOn (φ : ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    Set.BijOn (fun p : (Ω → ℝ) × (ℕ → Ω → ℝ) => nkSol φ u p.2 p.1)
      {p | 𝔼.E 0 p.1 = p.1 ∧ IsShock 𝔼 p.2 ∧ p.2 0 = 0}
      {π | 𝔼.Adapted π ∧ Eq164 𝔼 φ u π} := by
  refine ⟨fun p hp => ⟨nkSol_adapted 𝔼 hp.1 hu hp.2.1, nkSol_solves 𝔼 hp.1 hu hp.2.1⟩,
    fun p hp q hq hpq => ?_, fun π hπ => ?_⟩
  · obtain ⟨h0, hδ⟩ := nkSol_inj hpq
    refine Prod.ext h0 (funext fun t => ?_)
    cases t with
    | zero => rw [hp.2.2, hq.2.2]
    | succ t => exact hδ t
  · refine ⟨(π 0, innovProc 𝔼 π), ⟨hπ.1 0, innovProc_isShock 𝔼 π, rfl⟩, ?_⟩
    exact (eq_nkSol 𝔼 hπ.1 hu hπ.2).symm

/-! ### Expected inflation -/

/-- Cochrane (2023), p. 364: expected inflation in an equilibrium of (16.4) obeys
`E_t π_{t+j+1} = φ E_t π_{t+j} + E_t u_{t+j}`. -/
theorem expected_succ {φ : ℝ} {u π : ℕ → Ω → ℝ} (h : Eq164 𝔼 φ u π) (t j : ℕ) :
    𝔼.E t (π (t + j + 1)) = φ • 𝔼.E t (π (t + j)) + 𝔼.E t (u (t + j)) := by
  rw [← 𝔼.tower (Nat.le_add_right t j), h (t + j), map_add, map_smul]

/-- Cochrane (2023), p. 364: the difference of two equilibria (same disturbance) is expected to
evolve as `E_t(π'_{t+j} − π_{t+j}) = φʲ (π'_t − π_t)`. -/
theorem sunspot_expected {φ : ℝ} {u π π' : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hπ' : 𝔼.Adapted π')
    (h : Eq164 𝔼 φ u π) (h' : Eq164 𝔼 φ u π') (t j : ℕ) :
    𝔼.E t (π' (t + j)) - 𝔼.E t (π (t + j)) = φ ^ j • (π' t - π t) := by
  induction j with
  | zero => rw [add_zero, hπ t, hπ' t, pow_zero, one_smul]
  | succ j ih =>
    rw [← add_assoc, expected_succ 𝔼 h, expected_succ 𝔼 h', pow_succ, mul_comm, ← smul_smul,
      ← ih, smul_sub]
    abel

/-- Cochrane (2023), p. 364 ("If `|φ| < 1`, this economy is stable. Expected inflation
`E_t π_{t+j}` converges going forward for any initial value"): with a constant disturbance
`u ≡ c` and `φ ≠ 1`, `E_t π_{t+j} − c/(1−φ) = φʲ (π_t − c/(1−φ))`, so for `|φ| < 1` expected
inflation converges to `c/(1 − φ)` from any initial value. -/
theorem expected_const_converges {φ c : ℝ} (hφ : |φ| < 1) {π : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (fun _ _ => c) π) (t : ℕ) (ω : Ω) :
    (∀ j, 𝔼.E t (π (t + j)) ω - c / (1 - φ) = φ ^ j * (π t ω - c / (1 - φ))) ∧
      Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 (c / (1 - φ))) := by
  have h1 : 1 - φ ≠ 0 := by
    have := (abs_lt.mp hφ).2
    linarith
  have key : ∀ j, 𝔼.E t (π (t + j)) ω - c / (1 - φ) = φ ^ j * (π t ω - c / (1 - φ)) := by
    intro j
    induction j with
    | zero => rw [add_zero, hπ t, pow_zero, one_mul]
    | succ j ih =>
      rw [← add_assoc, expected_succ 𝔼 h, 𝔼.const]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : 𝔼.E t (π (t + j)) ω = φ ^ j * (π t ω - c / (1 - φ)) + c / (1 - φ) := by
        linarith
      rw [e, pow_succ]
      field_simp
      ring
  refine ⟨key, ?_⟩
  have hlim : Tendsto (fun j => φ ^ j * (π t ω - c / (1 - φ)) + c / (1 - φ)) atTop
      (𝓝 (0 * (π t ω - c / (1 - φ)) + c / (1 - φ))) :=
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const _).add_const _
  rw [zero_mul, zero_add] at hlim
  refine hlim.congr fun j => ?_
  linarith [key j]

/-- Cochrane (2023), p. 364 ("stable"): for `|φ| < 1` and a bounded disturbance `|u| ≤ M`,
expected inflation in any equilibrium stays bounded at every horizon,
`|E_t π_{t+j}| ≤ |π_t| + M/(1 − |φ|)`. -/
theorem expected_bounded {φ M : ℝ} (hφ : |φ| < 1) {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : ∀ t ω, |u t ω| ≤ M) (h : Eq164 𝔼 φ u π) (t j : ℕ) (ω : Ω) :
    |𝔼.E t (π (t + j)) ω| ≤ |π t ω| + M / (1 - |φ|) := by
  have h1 : 0 < 1 - |φ| := by linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0 ω)
  have hK : 0 ≤ M / (1 - |φ|) := div_nonneg hM h1.le
  have hKe : |φ| * (M / (1 - |φ|)) + M = M / (1 - |φ|) := by
    field_simp
    ring
  induction j with
  | zero => rw [add_zero, hπ t]; linarith
  | succ j ih =>
    rw [← add_assoc, expected_succ 𝔼 h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hu' := 𝔼.abs_E_le (hu (t + j)) t ω
    calc |φ * 𝔼.E t (π (t + j)) ω + 𝔼.E t (u (t + j)) ω|
        ≤ |φ| * |𝔼.E t (π (t + j)) ω| + |𝔼.E t (u (t + j)) ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |φ| * (|π t ω| + M / (1 - |φ|)) + M := by gcongr
      _ ≤ |π t ω| + M / (1 - |φ|) := by
          nlinarith [abs_nonneg φ, abs_nonneg (π t ω)]

/-- Cochrane (2023), p. 364 (imprecision): "Expected inflation `E_t π_{t+j}` converges going
forward for any initial value" needs a convergent forecast path of the disturbance (e.g. constant,
`expected_const_converges`); for a general bounded disturbance only boundedness holds
(`expected_bounded`). Counterexample: perfect foresight, `φ = 0`, `u_t = (−1)ᵗ`: the equilibrium
`π_0 = 0`, `π_{t+1} = (−1)ᵗ` has `E_0 π_j = π_j` oscillating between `1` and `−1`. -/
theorem converges_needs_convergent_u :
    Eq164 perfectForesight 0 (fun t _ => (-1 : ℝ) ^ t) (nkSol 0 (fun t _ => (-1 : ℝ) ^ t) 0 0) ∧
      ¬ ∃ L, Tendsto (fun j => perfectForesight.E 0
        (nkSol 0 (fun t _ => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) atTop (𝓝 L) := by
  have hu : perfectForesight.Adapted (fun t (_ : Unit) => (-1 : ℝ) ^ t) := fun _ => rfl
  refine ⟨nkSol_solves perfectForesight rfl hu (isShock_zero _), ?_⟩
  rintro ⟨L, hL⟩
  have hval : ∀ k : ℕ, nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (k + 1) () = (-1) ^ k := by
    intro k
    change (0 : ℝ) • nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 k () + (-1) ^ k + 0 = _
    simp
  have h1 : Tendsto (fun k : ℕ => (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
  have h2 : Tendsto (fun k : ℕ => (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 2)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
  have e1 : ∀ k : ℕ, (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 1) = 1 := by
    intro k
    change nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + (2 * k + 1)) () = 1
    rw [zero_add, hval, pow_mul]
    simp
  have e2 : ∀ k : ℕ, (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 2) = -1 := by
    intro k
    change nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + (2 * k + 1 + 1)) () = -1
    rw [zero_add, hval, pow_succ, pow_mul]
    simp
  simp only [e1] at h1
  simp only [e2] at h2
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' (Eventually.of_forall fun _ => rfl)) h1
  have := (tendsto_nhds_unique tendsto_const_nhds h2).trans this.symm
  norm_num at this

/-- Cochrane (2023), p. 364 ("'Sunspot' shocks `δ_{t+1}` can erupt at any time, and fade
away"): for `|φ| < 1` the expected effect of any sunspot dies out: two equilibria satisfy
`E_t(π'_{t+j} − π_{t+j}) → 0`. -/
theorem sunspot_fades {φ : ℝ} (hφ : |φ| < 1) {u π π' : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hπ' : 𝔼.Adapted π') (h : Eq164 𝔼 φ u π) (h' : Eq164 𝔼 φ u π') (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π' (t + j)) ω - 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π' (t + j)) ω - 𝔼.E t (π (t + j)) ω) =
      fun j => φ ^ j * (π' t ω - π t ω) := by
    funext j
    have := congrFun (sunspot_expected 𝔼 hπ hπ' h h' t j) ω
    simpa using this
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π' t ω - π t ω)

/-- Cochrane (2023), eq. (16.5), p. 364: for `|φ| < 1` and bounded `π_0`, disturbance and
sunspot, the member of (16.5) is bounded. -/
theorem nkSol_bounded {φ A Mu Md : ℝ} (hφ : |φ| < 1) {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : ∀ ω, |π0 ω| ≤ A) (hu : ∀ t ω, |u t ω| ≤ Mu) (hδ : ∀ t ω, |δ t ω| ≤ Md) :
    BoundedProc (nkSol φ u δ π0) := by
  rw [nkSol_eq_ruleSol]
  exact FTPLSimple.ruleSol_bounded hφ h0 hu (fun t ω => by simpa using hδ t ω)

/-- Cochrane (2023), p. 364 ("But it remains indeterminate"): for `|φ| < 1` and every bounded
adapted disturbance the bounded equilibria of (16.4) form an uncountable set (already `π_0` is
free). -/
theorem indeterminate_of_abs_lt_one [Nonempty Ω] {φ : ℝ} (hφ : |φ| < 1) {u : ℕ → Ω → ℝ}
    (hub : BoundedProc u) (hu : 𝔼.Adapted u) :
    ¬ {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ BoundedProc π ∧ Eq164 𝔼 φ u π}.Countable := by
  intro hc
  obtain ⟨M, hM⟩ := hub
  let f : ℝ → ℕ → Ω → ℝ := fun c => nkSol φ u 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ
      {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ BoundedProc π ∧ Eq164 𝔼 φ u π} := by
    intro c _
    refine ⟨nkSol_adapted 𝔼 (𝔼.const 0 c) hu (isShock_zero 𝔼),
      nkSol_bounded (A := |c|) (Md := 0) hφ (fun _ => le_rfl) hM (fun _ _ => by simp),
      nkSol_solves 𝔼 (𝔼.const 0 c) hu (isShock_zero 𝔼)⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-- Cochrane (2023), p. 364 (sunspots under genuine uncertainty): on the coin-flip event tree,
with `u = 0` and `π_0 = 0`, the coin shock is a sunspot: `nkSol φ 0 coinShock 0` is an adapted
equilibrium of (16.4) different from the zero equilibrium with the same `π_0`, and it is bounded
for `|φ| < 1`. -/
theorem coin_sunspot {φ : ℝ} (hφ : |φ| < 1) :
    let π := nkSol (Ω := Bool × Bool) φ 0 ExpectationsFiniteTree.coinShock 0
    ExpectationsFiniteTree.coinSystem.Adapted π ∧ Eq164 ExpectationsFiniteTree.coinSystem φ 0 π ∧
      BoundedProc π ∧ π 0 = 0 ∧ π ≠ 0 := by
  intro π
  have hs := (coin_shock_ne_zero).1
  have h0 : ExpectationsFiniteTree.coinSystem.E 0 (0 : Bool × Bool → ℝ) = 0 := map_zero _
  have hu : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  refine ⟨nkSol_adapted _ h0 hu hs, nkSol_solves _ h0 hu hs,
    nkSol_bounded (A := 0) (Mu := 0) (Md := 1) hφ (fun _ => by simp) (fun _ _ => by simp)
      (fun t ω => ?_), rfl, fun h => ?_⟩
  · unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> simp
  · have := congrFun (congrFun h 1) (true, true)
    simp [π, nkSol, ExpectationsFiniteTree.coinShock] at this

/-! ### `|φ| > 1`: the locally bounded equilibrium (16.6) -/

/-- Cochrane (2023), p. 364: for `|φ| > 1`, (16.4) has at most one bounded solution (the
difference of two solutions solves `d_t = φ⁻¹ E_t d_{t+1}`); no bound or adaptedness of the
disturbance is needed. -/
theorem eq164_unique {φ : ℝ} (hφ : 1 < |φ|) {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Eq164 𝔼 φ u π₁)
    (h₂ : Eq164 𝔼 φ u π₂) (hb₁ : BoundedProc π₁) (hb₂ : BoundedProc π₂) : π₁ = π₂ := by
  have hφ0 : φ ≠ 0 := fun h => by rw [h, abs_zero] at hφ; linarith
  have ha : |φ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  have key : ∀ π : ℕ → Ω → ℝ, Eq164 𝔼 φ u π →
      ∀ t, π t = φ⁻¹ • 𝔼.E t (π (t + 1)) + -(φ⁻¹ • u t) := by
    intro π h t
    rw [h t, smul_add, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
    abel
  exact 𝔼.forward_unique ha (key π₁ h₁) (key π₂ h₂) hb₁ hb₂

/-- Cochrane (2023), eq. (16.4), p. 364: (16.4) is the undivided scalar equation
`φ π_t = E_t π_{t+1} − u_t` of the forward-solution module. -/
theorem eq164_iff_scalar (φ : ℝ) (u π : ℕ → Ω → ℝ) :
    Eq164 𝔼 φ u π ↔ ForwardSolution.ScalarEq 𝔼 φ 1 (fun t => -u t) π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, one_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.6), p. 364: the forward solution
`π_t = −∑_{j ≥ 0} φ^{−(j+1)} E_t u_{t+j}`. -/
noncomputable def fwdSol (φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ForwardSolution.scalarSol 𝔼 φ 1 (fun t => -u t)

/-- Cochrane (2023), eq. (16.6), p. 364: `π_t = −∑_{j ≥ 0} (φ^{j+1})⁻¹ E_t u_{t+j}`. -/
theorem fwdSol_apply (φ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdSol 𝔼 φ u t ω = -∑' j, (φ ^ (j + 1))⁻¹ * 𝔼.E t (u (t + j)) ω := by
  rw [fwdSol, ForwardSolution.scalarSol_apply, ← tsum_neg]
  refine tsum_congr fun j => ?_
  simp only [one_pow, map_neg, Pi.neg_apply]
  ring

/-- Cochrane (2023), eq. (16.4), p. 364: for `φ ≠ 0` every solution of (16.4) with adapted
disturbance is adapted (`π_t = φ⁻¹(E_t π_{t+1} − u_t)`). -/
theorem eq164_adapted {φ : ℝ} (hφ : φ ≠ 0) {u π : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u)
    (h : Eq164 𝔼 φ u π) : 𝔼.Adapted π := by
  intro t
  have e : π t = φ⁻¹ • (𝔼.E t (π (t + 1)) - u t) := by
    rw [h t, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  rw [e, map_smul, map_sub, 𝔼.E_E_self, hu t]

/-- Cochrane (2023), eq. (16.6), p. 364 ("we find the unique locally-bounded equilibrium by
solving the difference equation (16.4) forward"): for `|φ| > 1` and a bounded adapted
disturbance, the forward solution is a bounded adapted equilibrium of (16.4), and every bounded
solution of (16.4) equals it. -/
theorem fwdSol_existsUnique {φ M : ℝ} (hφ : 1 < |φ|) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 φ u (fwdSol 𝔼 φ u) ∧ BoundedProc (fwdSol 𝔼 φ u) ∧ 𝔼.Adapted (fwdSol 𝔼 φ u) ∧
      ∀ π, Eq164 𝔼 φ u π → BoundedProc π → π = fwdSol 𝔼 φ u := by
  have h1 : |(1 : ℝ)| < |φ| := by rwa [abs_one]
  have hf : ∀ t ω, |(fun t => -u t) t ω| ≤ M := fun t ω => by simpa using hM t ω
  have hfa : 𝔼.Adapted (fun t => -u t) := fun t => by simp only [map_neg, hu t]
  obtain ⟨hs, hb, ha, huniq⟩ := ForwardSolution.scalar_existsUnique 𝔼 h1 hf hfa
  exact ⟨(eq164_iff_scalar 𝔼 φ u _).mpr hs, hb, ha,
    fun π hπ hπb => huniq π ((eq164_iff_scalar 𝔼 φ u π).mp hπ) hπb⟩

/-- Cochrane (2023), p. 364 ("If `|φ| > 1`, all of these equilibria except one are expected
eventually to explode, i.e. `|E_t(π_{t+j})|` grows without bound"): for `|φ| > 1` and a bounded
adapted disturbance, every equilibrium other than (16.6) has, at some date and state,
`|E_t π_{t+j}| → ∞` as `j → ∞`. -/
theorem explodes_of_ne_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ u π)
    (hne : π ≠ fwdSol 𝔼 φ u) :
    ∃ t ω, Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  obtain ⟨hs, ⟨K, hK⟩, ha, -⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  have : ∃ t ω, π t ω ≠ fwdSol 𝔼 φ u t ω := by
    by_contra hc
    push Not at hc
    exact hne (funext fun t => funext fun ω => hc t ω)
  obtain ⟨t, ω, htω⟩ := this
  refine ⟨t, ω, ?_⟩
  have hd : 0 < |π t ω - fwdSol 𝔼 φ u t ω| := abs_pos.mpr (sub_ne_zero.mpr htω)
  have hlow : ∀ j, |φ| ^ j * |π t ω - fwdSol 𝔼 φ u t ω| + -K ≤ |𝔼.E t (π (t + j)) ω| := by
    intro j
    have e := congrFun (sunspot_expected 𝔼 ha hπ hs h t j) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    have hb := 𝔼.abs_E_le (hK (t + j)) t ω
    have h2 : |φ ^ j * (π t ω - fwdSol 𝔼 φ u t ω)| ≤
        |𝔼.E t (π (t + j)) ω| + |𝔼.E t (fwdSol 𝔼 φ u (t + j)) ω| := by
      rw [← e]
      exact abs_sub _ _
    rw [abs_mul, abs_pow] at h2
    linarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const hd)

/-- Cochrane (2023), p. 364 and p. 370 ("In this model `φ < −1` is as good as `φ > 1` to produce
local determinacy"): (16.4) has exactly one bounded equilibrium for every bounded adapted
disturbance if and only if `|φ| > 1`. -/
theorem determinate_iff [Nonempty Ω] (φ : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ Eq164 𝔼 φ u π) ↔
      1 < |φ| := by
  constructor
  · intro hdet
    by_contra hc
    push Not at hc
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    obtain ⟨z, -, huniq⟩ := hdet 0 ⟨0, fun _ _ => by simp⟩ hz
    have e0 : Eq164 𝔼 φ 0 0 := fun t => by simp
    have e1 : Eq164 𝔼 φ 0 (fun t _ => φ ^ t) := fun t => by
      rw [𝔼.const]
      funext ω
      simp [pow_succ, mul_comm]
    have hb1 : BoundedProc (fun t (_ : Ω) => φ ^ t) :=
      ⟨1, fun t _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg φ) hc⟩
    have a := huniq 0 ⟨⟨0, fun _ _ => by simp⟩, e0⟩
    have b := huniq _ ⟨hb1, e1⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (b.trans a.symm) 0) ω
    simp at this
  · intro hφ u ⟨M, hM⟩ hu
    obtain ⟨hs, hb, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
    exact ⟨_, ⟨hb, hs⟩, fun π hπ => huniq π hπ.2 hπ.1⟩

/-! ### AR(1) disturbances, (16.7) and (16.9)–(16.11) -/

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) inflation path `π_t = −u_t/(φ − η)`. -/
noncomputable def ar1Pi (φ η : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(φ - η)⁻¹) • u t

/-- Cochrane (2023), eq. (16.9), p. 365: for an AR(1) disturbance (`E_t u_{t+1} = η u_t`) and
any `φ ≠ η`, `π_t = −u_t/(φ − η)` solves (16.4); no bound and no condition on `|φ|`. -/
theorem ar1Pi_eq164 {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    Eq164 𝔼 φ u (ar1Pi φ η u) := by
  intro t
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  simp only [ar1Pi]
  rw [map_smul, hu.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) path is adapted when `u` is. -/
theorem ar1Pi_adapted (φ η : ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (ar1Pi φ η u) := fun t => by simp only [ar1Pi, map_smul, hu t]

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) path is bounded when `u` is,
`|π_t| ≤ |(φ − η)⁻¹| M`. -/
theorem ar1Pi_bounded (φ η : ℝ) {M : ℝ} {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M) :
    BoundedProc (ar1Pi φ η u) :=
  ⟨|(φ - η)⁻¹| * M, fun t ω => by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩

/-- Cochrane (2023), eq. (16.9), p. 365 (and p. 364): with an AR(1) disturbance
(`E_t u_{t+1} = η u_t`), bounded, `|φ| > 1` and `φ ≠ η`, the locally bounded equilibrium is
`π_t = −u_t/(φ − η)`. -/
theorem ar1_solution {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.IsAR1 η u) :
    fwdSol 𝔼 φ u = ar1Pi φ η u := by
  obtain ⟨-, -, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu.1
  exact (huniq _ (ar1Pi_eq164 𝔼 hφη hu) (ar1Pi_bounded φ η hM)).symm

/-- Cochrane (2023), eq. (16.11), p. 365 (and p. 363): in the AR(1) equilibrium the interest
rate is `i_t = φ π_t + u_t = −η u_t/(φ − η)`. -/
theorem ar1_rate {φ η : ℝ} (hφη : φ ≠ η) (u : ℕ → Ω → ℝ) (t : ℕ) :
    φ • ((-(φ - η)⁻¹) • u t) + u t = (-(η / (φ - η))) • u t := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), eq. (16.10), p. 365: in the AR(1) equilibrium, with
`u_{t+1} = η u_t + ε_{i,t+1}`, inflation follows `π_{t+1} = η π_t − ε_{i,t+1}/(φ − η)`. -/
theorem ar1_law_1610 {φ η : ℝ} {u εi : ℕ → Ω → ℝ} (hlaw : AR1Law η u εi) (t : ℕ) :
    (-(φ - η)⁻¹) • u (t + 1) = η • ((-(φ - η)⁻¹) • u t) + (-(φ - η)⁻¹) • εi (t + 1) := by
  rw [hlaw t, smul_add, smul_smul, smul_smul, mul_comm]

/-- Cochrane (2023), eq. (16.7), p. 365 ("by this criterion we select the variables `π_0`,
`{δ_{t+1}}`"): in the AR(1) equilibrium, `π_0 = −u_0/(φ − η)` and the selected sunspot is
`δ_{t+1} = ΔE_{t+1} π_{t+1} = −ε_{t+1}/(φ − η)`, with `ε_{t+1} = u_{t+1} − η u_t`. -/
theorem ar1_selection {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.IsAR1 η u) :
    fwdSol 𝔼 φ u 0 = (-(φ - η)⁻¹) • u 0 ∧
      ∀ t, innovProc 𝔼 (fwdSol 𝔼 φ u) (t + 1) = (-(φ - η)⁻¹) • (u (t + 1) - η • u t) := by
  rw [ar1_solution 𝔼 hφ hφη hM hu]
  refine ⟨rfl, fun t => ?_⟩
  change innov 𝔼 t ((-(φ - η)⁻¹) • u (t + 1)) = _
  rw [innov_smul, (shock_of_ar1 𝔼 hu).2.2 t]

/-- Cochrane (2023), Figure 16.1 and eqs. (16.9)–(16.11), p. 365: impulse responses of the AR(1)
equilibrium to a monetary-policy shock, as innovations: `ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`,
`ΔE_{t+1} π_{t+1+j} = −ηʲ/(φ − η) ε_{t+1}` and `ΔE_{t+1} i_{t+1+j} = −η^{j+1}/(φ − η) ε_{t+1}`. -/
theorem irf_ar1 {φ η : ℝ} {u εi : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 εi)
    (hlaw : AR1Law η u εi) (t j : ℕ) :
    innov 𝔼 t (u (t + 1 + j)) = η ^ j • εi (t + 1) ∧
      innov 𝔼 t ((-(φ - η)⁻¹) • u (t + 1 + j)) = (-(η ^ j / (φ - η))) • εi (t + 1) ∧
      innov 𝔼 t ((-(η / (φ - η))) • u (t + 1 + j)) =
        (-(η ^ (j + 1) / (φ - η))) • εi (t + 1) := by
  have h := innov_ar1 𝔼 hu hε hlaw t j
  refine ⟨h, ?_, ?_⟩
  · rw [innov_smul, h, smul_smul]
    congr 1
    ring
  · rw [innov_smul, h, smul_smul]
    congr 1
    ring

/-! ### Figure 16.1 -/

/-- Cochrane (2023), Figure 16.1, p. 366 (`φ = 1.25`, `η = 0.8`): the responses to a unit
monetary shock are `π = −(0.8)ʲ/0.45` and `i = −(0.8)^{j+1}/0.45`; on impact inflation falls by
`20/9 ≈ 2.22` and the rate by `16/9 ≈ 1.78` percentage points. -/
theorem fig161_values (j : ℕ) :
    -(((4 : ℝ) / 5) ^ j / ((5 : ℝ) / 4 - 4 / 5)) = -(20 / 9) * ((4 : ℝ) / 5) ^ j ∧
      -(((4 : ℝ) / 5) ^ (j + 1) / ((5 : ℝ) / 4 - 4 / 5)) = -(16 / 9) * ((4 : ℝ) / 5) ^ j ∧
      -(((4 : ℝ) / 5) ^ 0 / ((5 : ℝ) / 4 - 4 / 5)) = -(20 / 9) := by
  refine ⟨by ring, by ring, by norm_num⟩

/-- Cochrane (2023), Figure 16.1, p. 365 ("In response to a positive shock to the disturbance
`u_t`, inflation `π_t` declines immediately, and then reverts slowly"): the inflation response
`−(20/9)(0.8)ʲ` is negative, strictly increasing in `j`, and tends to zero; the same holds for
the rate response `−(16/9)(0.8)ʲ`. -/
theorem fig161_reverts :
    (∀ j : ℕ, -(20 / 9) * ((4 : ℝ) / 5) ^ j < 0) ∧
      (∀ j : ℕ, -(20 / 9) * ((4 : ℝ) / 5) ^ j < -(20 / 9) * ((4 : ℝ) / 5) ^ (j + 1)) ∧
      Tendsto (fun j : ℕ => -(20 / 9) * ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) ∧
      (∀ j : ℕ, -(16 / 9) * ((4 : ℝ) / 5) ^ j < -(16 / 9) * ((4 : ℝ) / 5) ^ (j + 1)) ∧
      Tendsto (fun j : ℕ => -(16 / 9) * ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) := by
  have hp : ∀ j : ℕ, 0 < ((4 : ℝ) / 5) ^ j := fun j => by positivity
  have hl : Tendsto (fun j : ℕ => ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨fun j => by nlinarith [hp j], fun j => ?_, by simpa using hl.const_mul (-(20 / 9)),
    fun j => ?_, by simpa using hl.const_mul (-(16 / 9))⟩
  · rw [pow_succ]; nlinarith [hp j]
  · rw [pow_succ]; nlinarith [hp j]

/-! ### (16.8): the Wicksellian rule -/

/-- Cochrane (2023), eq. (16.8), p. 365: the Fisher equation in the price level
`i_t = E_t p_{t+1} − p_t` and the Wicksellian rule `i_t = φ_p (p_t − p*) + u_t`. -/
def WicksellModel (φp pstar : ℝ) (u i p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (p (t + 1)) - p t ∧ i t = φp • (p t - fun _ => pstar) + u t

/-- Cochrane (2023), eq. (16.8), p. 365 ("substituting into the Fisher equation (16.1)"): for an
adapted price level, the model holds iff the rate follows the rule and the price gap
`x_t = p_t − p*` satisfies `E_t x_{t+1} = (1 + φ_p) x_t + u_t`. -/
theorem wicksell_iff {φp pstar : ℝ} {u i p : ℕ → Ω → ℝ} :
    WicksellModel 𝔼 φp pstar u i p ↔ (∀ t, i t = φp • (p t - fun _ => pstar) + u t) ∧
      Eq164 𝔼 (1 + φp) u (fun t => p t - fun _ => pstar) := by
  have hE : ∀ t, 𝔼.E t (p (t + 1) - fun _ => pstar) = 𝔼.E t (p (t + 1)) - fun _ => pstar :=
    fun t => by rw [map_sub, 𝔼.const]
  constructor
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    rw [hE t]
    funext ω
    have a := congrFun (h t).1 ω
    have b := congrFun (h t).2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith
  · rintro ⟨hi, h⟩ t
    refine ⟨?_, hi t⟩
    funext ω
    have a := congrFun (h t) ω
    have b := congrFun (hi t) ω
    rw [hE t] at a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith

/-- Cochrane (2023), eq. (16.8), p. 365 ("if `φ_p > 0` and if we rule out explosive equilibria,
then we have a unique locally-bounded equilibrium price level"): for `|1 + φ_p| > 1` and a
bounded adapted disturbance, `p_t = p* + (forward solution of the gap)` is a bounded adapted
price level whose gap satisfies (16.8), and every bounded price level whose gap satisfies (16.8)
equals it. -/
theorem wicksell_existsUnique {φp pstar M : ℝ} (hφ : 1 < |1 + φp|) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 (1 + φp) u (fun t => (fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) - fun _ => pstar) ∧
      BoundedProc (fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) ∧
      𝔼.Adapted (fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) ∧
      ∀ q : ℕ → Ω → ℝ, Eq164 𝔼 (1 + φp) u (fun t => q t - fun _ => pstar) → BoundedProc q →
        q = fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar := by
  obtain ⟨hs, ⟨K, hK⟩, ha, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  have hgap : (fun t => (fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) - fun _ => pstar) =
      fwdSol 𝔼 (1 + φp) u := by
    funext t
    exact add_sub_cancel_right _ _
  refine ⟨by rw [hgap]; exact hs, ⟨K + |pstar|, fun t ω => ?_⟩, fun t => ?_, fun q hq hqb => ?_⟩
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hK t ω) le_rfl)
  · simp only [map_add, ha t, 𝔼.const]
  · obtain ⟨Q, hQ⟩ := hqb
    have hb : BoundedProc (fun t => q t - fun _ => pstar) := ⟨Q + |pstar|, fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hQ t ω) le_rfl)⟩
    have e := huniq _ hq hb
    funext t
    rw [← congrFun e t]
    exact (sub_add_cancel _ _).symm

/-- Cochrane (2023), p. 365 (the display after (16.8), with `φ_p` for the printed `φ`, survey
E4): the unique locally bounded price level is
`p_t = p* − ∑_{j ≥ 0} ((1 + φ_p)^{j+1})⁻¹ E_t u_{t+j}`. -/
theorem wicksell_apply (φp pstar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fwdSol 𝔼 (1 + φp) u t + fun (_ : Ω) => pstar) ω =
      pstar - ∑' j, ((1 + φp) ^ (j + 1))⁻¹ * 𝔼.E t (u (t + j)) ω := by
  rw [Pi.add_apply, fwdSol_apply]
  ring

/-- Cochrane (2023), eq. (16.8), p. 365, and survey E4: the price gap `x = p − p*` is determinate
(exactly one bounded solution of `E_t x_{t+1} = (1 + φ_p) x_t + u_t` for every bounded adapted
disturbance) iff `φ_p > 0` or `φ_p < −2`. The book states only `φ_p > 0`. -/
theorem wicksell_determinate_iff [Nonempty Ω] (φp : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! x, BoundedProc x ∧ Eq164 𝔼 (1 + φp) u x) ↔ (0 < φp ∨ φp < -2) := by
  rw [determinate_iff 𝔼 (1 + φp), lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Cochrane (2023), p. 365, survey error E4: the printed formula
`p_t = p* − ∑ (1 + φ)^{−(j+1)} E_t u_{t+j}` uses the inflation-rule coefficient `φ` instead of
`φ_p`. Counterexample under perfect foresight with `φ_p = 1`, `φ = 2`, `u ≡ 1`: the printed sum
is `∑ 3^{−(j+1)} = 1/2`, and the constant gap `−1/2` does not satisfy (16.8), while the corrected
gap `−∑ 2^{−(j+1)} = −1` does. -/
theorem printed_wicksell_false :
    (∑' j : ℕ, ((1 + (2 : ℝ)) ^ (j + 1))⁻¹ * 1 = 1 / 2) ∧
      (∑' j : ℕ, ((1 + (1 : ℝ)) ^ (j + 1))⁻¹ * 1 = 1) ∧
      ¬ Eq164 perfectForesight (1 + 1) (fun _ _ => 1) (fun _ _ => -(1 / 2 : ℝ)) ∧
      Eq164 perfectForesight (1 + 1) (fun _ _ => 1) (fun _ _ => -(1 : ℝ)) := by
  refine ⟨?_, ?_, fun h => ?_, fun t => ?_⟩
  · have h := ForwardSolution.tsum_geometric_ratio (A := 3) (B := 1) 1 (by norm_num)
    calc ∑' j : ℕ, ((1 + (2 : ℝ)) ^ (j + 1))⁻¹ * 1 = ∑' j : ℕ, (1 : ℝ) * 1 ^ j / 3 ^ (j + 1) :=
          tsum_congr fun j => by norm_num
      _ = 1 / (3 - 1) := h
      _ = 1 / 2 := by norm_num
  · have h := ForwardSolution.tsum_geometric_ratio (A := 2) (B := 1) 1 (by norm_num)
    calc ∑' j : ℕ, ((1 + (1 : ℝ)) ^ (j + 1))⁻¹ * 1 = ∑' j : ℕ, (1 : ℝ) * 1 ^ j / 2 ^ (j + 1) :=
          tsum_congr fun j => by norm_num
      _ = 1 / (2 - 1) := h
      _ = 1 := by norm_num
  · have := congrFun (h 0) ()
    norm_num [perfectForesight] at this
  · funext ω
    norm_num [perfectForesight]

end Cochrane.NewKeynesianSelection.SimplestModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Inflation targets and equilibrium selection: King's form of the rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.2 "Inflation targets and
equilibrium selection", eqs. (16.12)–(16.14), pp. 366–368, and the `*`-notation statement of
§16.4, p. 369.

King's (2000) form of the policy rule is `i_t = i*_t + φ(π_t − π*_t)` (16.12) with the
interest-rate target `i*_t = E_t π*_{t+1}`. It translates into the standard form
`i_t = φ π_t + u_t` by `u_t = E_t π*_{t+1} − φ π*_t` (16.13), and back (for `|φ| > 1` and bounded
processes) by `π*_t = −∑ φ^{−(j+1)} E_t u_{t+j}`. With (16.1) the equilibrium condition becomes
`E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)` (16.14): for `|φ| > 1` the only bounded equilibrium is
`π = π*`, for any target process, so the central bank can achieve any bounded adapted inflation
path. Interest-rate policy `i*` sets expected inflation; equilibrium-selection policy `φ` sets
unexpected inflation. In the fiscal theory the same rate path with the fiscal shock
`ε_{Σs} = −ΔE π*` gives the same inflation.

## Main results

* (16.12)–(16.13): `KingRule`, `toU`, `kingRule_iff`, `kingModel_iff_nk`, `toU_bounded`,
  `toU_adapted`.
* The translation is a bijection: `fwdSol_toU`, `toU_fwdSol`, `translation_bijOn` (bounded adapted
  targets ↔ bounded adapted disturbances, for `|φ| > 1`).
* (16.14): `eq1614_iff`, `target_solves`, `eq_target_of_bounded` (the only bounded equilibrium is
  `π = π*`, for any disturbance process), `deviation_expected` (§16.4,
  `E_t(π_{t+j} − π*_{t+j}) = φʲ(π_t − π*_t)`), `deviation_explodes`.
* p. 367: `any_target_attainable` (every bounded adapted `π*` is the unique bounded equilibrium
  of the rule with `u = toU φ π*`), `eqm_rate_eq_target` (`i_t = i*_t` in equilibrium),
  `expected_set_by_rate`, `unexpected_set_by_selection`; `thetaRule_iff` (the rule with
  `i*_t = θ π*_t + u_t` is a standard rule with disturbance `(θ − φ)π*_t + u_t`).
* p. 367 (comparison with the fiscal theory): `ftpl_same_inflation`.
-/

namespace Cochrane.NewKeynesianSelection.KingForm

open Filter Topology Innovation SimplestModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (16.12)–(16.13) -/

/-- Cochrane (2023), eq. (16.12), p. 366: King's form of the rule,
`i_t = i*_t + φ(π_t − π*_t)` with the interest-rate target `i*_t = E_t π*_{t+1}`. -/
def KingRule (φ : ℝ) (pistar i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (pistar (t + 1)) + φ • (π t - pistar t)

/-- Cochrane (2023), eq. (16.13), p. 366: the translation
`u_t = i*_t − φπ*_t = E_t π*_{t+1} − φπ*_t` into the disturbance of the standard form (16.2). -/
def toU (φ : ℝ) (pistar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => 𝔼.E t (pistar (t + 1)) - φ • pistar t

/-- Cochrane (2023), eqs. (16.12)–(16.13), p. 366 ("This form of the policy rule is equivalent to
(16.2)"): King's rule holds iff `i_t = φπ_t + u_t` with `u` from (16.13). -/
theorem kingRule_iff {φ : ℝ} {pistar i π : ℕ → Ω → ℝ} :
    KingRule 𝔼 φ pistar i π ↔ ∀ t, i t = φ • π t + toU 𝔼 φ pistar t := by
  refine forall_congr' fun t => ?_
  rw [toU, smul_sub]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), eqs. (16.1), (16.12)–(16.13), p. 366: the Fisher equation with King's rule
is the simplest new-Keynesian model with the disturbance (16.13). -/
theorem kingModel_iff_nk {φ : ℝ} {pistar i π : ℕ → Ω → ℝ} :
    ((∀ t, i t = 𝔼.E t (π (t + 1))) ∧ KingRule 𝔼 φ pistar i π) ↔
      NKModel 𝔼 φ (toU 𝔼 φ pistar) i π := by
  rw [kingRule_iff]
  constructor
  · rintro ⟨h1, h2⟩ t
    exact ⟨h1 t, h2 t⟩
  · intro h
    exact ⟨fun t => (h t).1, fun t => (h t).2⟩

/-- Cochrane (2023), eq. (16.13), p. 366: a bounded target gives a bounded disturbance. -/
theorem toU_bounded {φ : ℝ} {pistar : ℕ → Ω → ℝ} (h : BoundedProc pistar) :
    BoundedProc (toU 𝔼 φ pistar) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + |φ| * M, fun t ω => ?_⟩
  simp only [toU, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hM (t + 1)) t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg φ)

/-- Cochrane (2023), eq. (16.13), p. 366: an adapted target gives an adapted disturbance. -/
theorem toU_adapted {φ : ℝ} {pistar : ℕ → Ω → ℝ} (h : 𝔼.Adapted pistar) :
    𝔼.Adapted (toU 𝔼 φ pistar) := fun t => by
  simp only [toU, map_sub, map_smul, 𝔼.E_E_self, h t]

/-! ### (16.14) -/

/-- Cochrane (2023), eq. (16.14), p. 367: with the disturbance (16.13), the equilibrium condition
(16.4) is `E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)`. -/
theorem eq1614_iff {φ : ℝ} {pistar π : ℕ → Ω → ℝ} :
    Eq164 𝔼 φ (toU 𝔼 φ pistar) π ↔
      ∀ t, 𝔼.E t (π (t + 1) - pistar (t + 1)) = φ • (π t - pistar t) := by
  refine forall_congr' fun t => ?_
  rw [toU, map_sub, smul_sub, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.14), p. 367: the target itself is an equilibrium of (16.4) with the
disturbance (16.13). -/
theorem target_solves (φ : ℝ) (pistar : ℕ → Ω → ℝ) : Eq164 𝔼 φ (toU 𝔼 φ pistar) pistar :=
  (eq1614_iff 𝔼).mpr fun t => by rw [sub_self, sub_self, map_zero, smul_zero]

/-- Cochrane (2023), eq. (16.14), p. 367 ("If the central bank follows `φ > 1`, the only
nonexplosive equilibrium is `π_t = π*_t`. We reach this conclusion quickly, for any process of
the monetary policy disturbance, not just an AR(1)"): for `|φ| > 1` and any bounded adapted target,
every bounded equilibrium equals the target. -/
theorem eq_target_of_bounded {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) (hπb : BoundedProc π)
    (h : ∀ t, 𝔼.E t (π (t + 1) - pistar (t + 1)) = φ • (π t - pistar t)) : π = pistar := by
  obtain ⟨M, hM⟩ := toU_bounded 𝔼 (φ := φ) hb
  obtain ⟨-, -, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM (toU_adapted 𝔼 ha)
  exact (huniq π ((eq1614_iff 𝔼).mpr h) hπb).trans
    (huniq pistar (target_solves 𝔼 φ pistar) hb).symm

/-- Cochrane (2023), §16.4, p. 369 ("In `*` notation, the central bank deliberately makes
inflation diverge away from its target, `E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)`"): in every
equilibrium, `E_t(π_{t+j} − π*_{t+j}) = φʲ(π_t − π*_t)`. -/
theorem deviation_expected {φ : ℝ} {pistar π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted pistar)
    (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) (t j : ℕ) :
    𝔼.E t (π (t + j) - pistar (t + j)) = φ ^ j • (π t - pistar t) := by
  rw [map_sub]
  exact sunspot_expected 𝔼 ha hπ (target_solves 𝔼 φ pistar) h t j

/-- Cochrane (2023), §16.2, p. 367 ("announces a threat to hyperinflate or deflate for any other
value of inflation"): for `|φ| > 1`, wherever inflation is off target the expected deviation
explodes, `|E_t(π_{t+j} − π*_{t+j})| → ∞`. -/
theorem deviation_explodes {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted pistar) (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) {t : ℕ}
    {ω : Ω} (hω : π t ω ≠ pistar t ω) :
    Tendsto (fun j => |𝔼.E t (π (t + j) - pistar (t + j)) ω|) atTop atTop := by
  have e : (fun j => |𝔼.E t (π (t + j) - pistar (t + j)) ω|) =
      fun j => |φ| ^ j * |π t ω - pistar t ω| := by
    funext j
    rw [deviation_expected 𝔼 ha hπ h t j, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const
    (abs_pos.mpr (sub_ne_zero.mpr hω))

/-! ### The translation is a bijection -/

/-- Cochrane (2023), p. 367 ("going in the other direction, `π*_t = −∑ φ^{−(j+1)} E_t u_{t+j}`"):
for `|φ| > 1` and a bounded adapted target, the forward solution of the translated disturbance
recovers the target. -/
theorem fwdSol_toU {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ} (hb : BoundedProc pistar)
    (ha : 𝔼.Adapted pistar) : fwdSol 𝔼 φ (toU 𝔼 φ pistar) = pistar :=
  (eq_target_of_bounded 𝔼 hφ hb ha
    (fwdSol_existsUnique 𝔼 hφ (toU_bounded 𝔼 hb).choose_spec (toU_adapted 𝔼 ha)).2.1
    ((eq1614_iff 𝔼).mp
      (fwdSol_existsUnique 𝔼 hφ (toU_bounded 𝔼 hb).choose_spec (toU_adapted 𝔼 ha)).1))

/-- Cochrane (2023), eq. (16.13), p. 366–367 (`i*_t = E_t π*_{t+1}` and `u_t = i*_t − φ π*_t`):
for `|φ| > 1` and a bounded adapted disturbance, translating the forward solution back gives the
disturbance. -/
theorem toU_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M)
    (hu : 𝔼.Adapted u) : toU 𝔼 φ (fwdSol 𝔼 φ u) = u := by
  obtain ⟨hs, -, -, -⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  funext t
  rw [toU, hs t]
  abel

/-- Cochrane (2023), p. 367 ("The `i*_t`, `π*_t` notation is just a different way of writing the
disturbance term `u_t`"): for `|φ| > 1` the translation (16.13) is a bijection from bounded
adapted targets onto bounded adapted disturbances, with inverse the forward solution. -/
theorem translation_bijOn {φ : ℝ} (hφ : 1 < |φ|) :
    Set.BijOn (toU 𝔼 φ) {p : ℕ → Ω → ℝ | BoundedProc p ∧ 𝔼.Adapted p}
      {u : ℕ → Ω → ℝ | BoundedProc u ∧ 𝔼.Adapted u} := by
  refine ⟨fun p hp => ⟨toU_bounded 𝔼 hp.1, toU_adapted 𝔼 hp.2⟩, fun p hp q hq hpq => ?_,
    fun u hu => ?_⟩
  · rw [← fwdSol_toU 𝔼 hφ hp.1 hp.2, ← fwdSol_toU 𝔼 hφ hq.1 hq.2, hpq]
  · obtain ⟨⟨M, hM⟩, ha⟩ := hu
    obtain ⟨-, hb, hfa, -⟩ := fwdSol_existsUnique 𝔼 hφ hM ha
    exact ⟨fwdSol 𝔼 φ u, ⟨hb, hfa⟩, toU_fwdSol 𝔼 hφ hM ha⟩

/-! ### Any target is attainable -/

/-- Cochrane (2023), p. 367 ("the central bank can achieve any value of inflation it wishes in
this model"): for `|φ| > 1` and every bounded adapted target `π*`, the rule with disturbance
`u = toU φ π*` has exactly one bounded equilibrium, and it is `π*`. -/
theorem any_target_attainable {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) :
    ∃! π, BoundedProc π ∧ Eq164 𝔼 φ (toU 𝔼 φ pistar) π := by
  refine ⟨pistar, ⟨hb, target_solves 𝔼 φ pistar⟩, fun π hπ => ?_⟩
  exact eq_target_of_bounded 𝔼 hφ hb ha hπ.1 ((eq1614_iff 𝔼).mp hπ.2)

/-- Cochrane (2023), p. 367 ("Interest-rate policy sets the path of interest rates which we
observe in equilibrium `i_t = i*_t`"): at the target equilibrium the rule gives `i_t = i*_t`. -/
theorem eqm_rate_eq_target {φ : ℝ} {pistar i : ℕ → Ω → ℝ} (h : KingRule 𝔼 φ pistar i pistar)
    (t : ℕ) : i t = 𝔼.E t (pistar (t + 1)) := by
  rw [h t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 367 ("and sets expected inflation via `i_t = E_t π_{t+1}`"): in every
equilibrium `E_t π_{t+1} = i*_t + φ(π_t − π*_t)`, which is `i*_t` at the target equilibrium. -/
theorem expected_set_by_rate {φ : ℝ} {pistar i π : ℕ → Ω → ℝ}
    (hf : ∀ t, i t = 𝔼.E t (π (t + 1))) (h : KingRule 𝔼 φ pistar i π) (t : ℕ) :
    𝔼.E t (π (t + 1)) = 𝔼.E t (pistar (t + 1)) + φ • (π t - pistar t) := by
  rw [← hf t, h t]

/-- Cochrane (2023), p. 367 ("Equilibrium-selection policy `φ(π_t − π*_t)` ... sets unexpected
inflation in this model"): at the selected equilibrium unexpected inflation is that of the
target, `ΔE_{t+1} π_{t+1} = ΔE_{t+1} π*_{t+1}`, and for `|φ| > 1` the selected equilibrium is the
only bounded one (`eq_target_of_bounded`). -/
theorem unexpected_set_by_selection {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) (hπb : BoundedProc π)
    (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1)) := by
  rw [eq_target_of_bounded 𝔼 hφ hb ha hπb ((eq1614_iff 𝔼).mp h)]

/-- Cochrane (2023), p. 367 ("Interest-rate policy can include rules, such as
`i*_t = θπ*_t + u_t`. Then the full monetary policy rule is `i_t = θπ*_t + u_t + φ(π_t − π*_t)`.
Again, we are just pulling more out of the disturbance term"): this rule is the standard form
`i_t = φπ_t + ũ_t` with `ũ_t = (θ − φ)π*_t + u_t`. -/
theorem thetaRule_iff {θ φ : ℝ} {pistar u i π : ℕ → Ω → ℝ} :
    (∀ t, i t = θ • pistar t + u t + φ • (π t - pistar t)) ↔
      ∀ t, i t = φ • π t + ((θ - φ) • pistar t + u t) := by
  refine forall_congr' fun t => ?_
  rw [smul_sub, sub_smul]
  constructor <;> intro h <;> rw [h] <;> abel

/-! ### Comparison with the fiscal theory (p. 367) -/

/-- Cochrane (2023), p. 367 ("The central bank determines the observed interest rate `i_t = i*_t`
in both cases ... In fiscal theory, shocks to the present value of surpluses determine
unexpected inflation"): in the fiscal-theory peg model with the rate path `i*_t = E_t π*_{t+1}`
and the fiscal shock `ε_{Σs,t+1} = −ΔE_{t+1} π*_{t+1}`, the unique equilibrium with `π_0 = π*_0`
is the target `π*`; no boundedness or `φ` is needed. -/
theorem ftpl_same_inflation {pistar : ℕ → Ω → ℝ} (ha : 𝔼.Adapted pistar) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = pistar 0 ∧
      FTPLSimple.PegModel 𝔼 (fun t => 𝔼.E t (pistar (t + 1))) (FTPLSimple.passiveShock 𝔼 pistar)
        π := by
  have hi : 𝔼.Adapted (fun t => 𝔼.E t (pistar (t + 1))) := fun t => 𝔼.E_E_self t _
  obtain ⟨π, hπ, huniq⟩ :=
    FTPLSimple.peg_existsUnique 𝔼 (ha 0) hi (FTPLSimple.passiveShock_isShock 𝔼 pistar)
  have htarget : 𝔼.Adapted pistar ∧ pistar 0 = pistar 0 ∧
      FTPLSimple.PegModel 𝔼 (fun t => 𝔼.E t (pistar (t + 1)))
        (FTPLSimple.passiveShock 𝔼 pistar) pistar :=
    ⟨ha, rfl, FTPLSimple.passive_valuation_holds 𝔼 fun _ => rfl⟩
  exact ⟨pistar, htarget, fun q hq => (huniq q hq).trans (huniq pistar htarget).symm⟩

end Cochrane.NewKeynesianSelection.KingForm

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hyperinflations and central-bank destabilisation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.3 "What's wrong with
hyperinflations?" (pp. 368–369) and §16.4 "Central bank destabilization?" (pp. 369–370).

§16.3: "There is no violation of the consumer's transversality condition in a path
`π_t = φᵗ π_0`" — nominal explosions are equilibria once fiscal policy is passive — while the
fiscal theory's transversality condition rules out real explosions of `B_{t−1}/P_t`. To state
these claims precisely we use the explicit frictionless economy of the book (the nonlinear Fisher
equation (16.25), the flow condition and the valuation equation (16.26), with the passive surplus
rule `s_t = (r/(1+r)) B_{t−1}/P_t` of p. 379). This module is the canonical home of the §16.8
fiscal block: `LowerBound` uses `real_debt_flow_scalar`, `passive_real_debt_const_real`,
`pv_partial` and `zero_bound_iff_scalar` from here, and `Links` connects `LowerBound`'s
equilibrium and transversality results to the ones below. Nominal debt is indexed by the date
it is redeemed: `D_t = B_{t−1}`, and real debt is `b_t = D_t/P_t`. The transversality
condition is the explicit limit `(1+r)^{−T} b_T → 0`, and the valuation equation is a genuine
`HasSum`.

## Main results

* (16.30): `real_debt_flow_scalar`, `real_debt_flow` (`b_{t+1} = (1+r)(b_t − s_t)`, from the
  Fisher equation and the flow condition, exactly); `pv_partial` (the iterated flow).
* Passive fiscal policy: `passive_real_debt_const_real`, `passive_real_debt_const` (real debt
  is constant), `passive_tvc`,
  `passive_valuation` ((16.26) holds), `any_price_path_eqm` (EVERY positive price path, however
  explosive, is a full perfect-foresight equilibrium with the transversality condition),
  `zero_bound_iff_scalar`, `zero_bound_iff` (error E2: the bound is weak).
* The hyperinflation `π_t = φᵗ π_0` as an exact nonlinear path: `hyperP`, `hyper_log_inflation`,
  `hyper_linear_eqm` (it solves (16.4) with `u = 0`), `hyper_rule` (it obeys the exact rule
  `1 + i_t = (1+r) Π_t^φ`, (16.27)–(16.29) with `Φ(Π) = Π^φ`), `hyper_explodes` (the price level
  and inflation go to infinity), `hyperinflation_satisfies_tvc` (yet it is an equilibrium with
  the transversality condition and constant real debt).
* Under uncertainty: `stoch_real_debt_martingale`, `stoch_expected_real_debt`, `stoch_tvc`,
  `stoch_valuation` (with passive fiscal policy every equilibrium price process satisfies the
  expected-value transversality condition and (16.26)).
* The fiscal theory (active fiscal policy, exogenous surpluses): `ftpl_discounted_debt`,
  `ftpl_tvc_iff` (TVC iff `b_0 = PV`), `ftpl_real_explosion` (a too-low price level makes real
  debt explode), `ftpl_price_level_iff` (`P_0 = B_{−1}/PV`).
* §16.4: `stable_of_abs_lt_one`, `unstable_of_one_lt_abs` (with `φ < 1` expectations converge;
  with `φ > 1` the bank makes them diverge), `oscillating_of_lt_neg_one` and
  `determinate_of_lt_neg_one` (`φ < −1` also gives local determinacy, with oscillating
  explosions).
-/

namespace Cochrane.NewKeynesianSelection.Hyperinflation

open Filter Topology Innovation SimplestModel

/-! ### The nonlinear perfect-foresight economy -/

/-- Cochrane (2023), eqs. (16.25) and (16.28), pp. 377–378: the perfect-foresight Fisher equation
`1 + i_t = (1 + r) P_{t+1}/P_t`. -/
def FisherPF (r : ℝ) (P i : ℕ → ℝ) : Prop := ∀ t, 1 + i t = (1 + r) * (P (t + 1) / P t)

/-- Cochrane (2023), p. 379 (flow condition, "proceeds of new debt sales + taxes = old debt
redemption"): `B_t/(1 + i_t) + P_t s_t = B_{t−1}`, with `D_t = B_{t−1}`. -/
def Flow (P D i s : ℕ → ℝ) : Prop := ∀ t, D (t + 1) / (1 + i t) + P t * s t = D t

/-- Cochrane (2023), p. 379: the passive surplus rule `s_t = (r/(1+r)) B_{t−1}/P_t`. -/
def PassiveRule (r : ℝ) (P D s : ℕ → ℝ) : Prop := ∀ t, s t = r / (1 + r) * (D t / P t)

/-- Cochrane (2023), §16.3, p. 368 (the consumer's transversality condition, as in Chapter 2):
`(1 + r)^{−T} B_{T−1}/P_T → 0`. -/
def TVC (r : ℝ) (P D : ℕ → ℝ) : Prop :=
  Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0)

/-- Cochrane (2023), eq. (16.26), p. 377 (perfect foresight): the valuation equation
`B_{t−1}/P_t = ∑_{j ≥ 0} βʲ s_{t+j}`, `β = 1/(1+r)`, at every date, as a genuine sum. -/
def Valuation (r : ℝ) (P D s : ℕ → ℝ) : Prop :=
  ∀ t, HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (D t / P t)

/-- Cochrane (2023), p. 379, eq. (16.30), one date at a time: from the flow condition
`B_t/(1 + i_t) + P_t s_t = B_{t−1}` and `1 + i_t = (1 + r)P_{t+1}/P_t`, real debt evolves as
`B_t/P_{t+1} = (1 + r)(B_{t−1}/P_t − s_t)`. Here `D = B_{t−1}`, `D' = B_t`. -/
theorem real_debt_flow_scalar {r i P P' D D' s : ℝ} (hr : 0 < 1 + r) (hP : 0 < P) (hP' : 0 < P')
    (hrate : 1 + i = (1 + r) * (P' / P)) (hflow : D' / (1 + i) + P * s = D) :
    D' / P' = (1 + r) * (D / P - s) := by
  have hi : 0 < 1 + i := by rw [hrate]; positivity
  have hD' : D' = (1 + i) * (D - P * s) := by
    field_simp at hflow
    linarith
  rw [hD', hrate]
  field_simp

/-- Cochrane (2023), eq. (16.30), p. 379: with the Fisher equation, the flow condition gives the
evolution of real debt, `B_t/P_{t+1} = (1 + r)(B_{t−1}/P_t − s_t)`. -/
theorem real_debt_flow {r : ℝ} (hr : 0 < 1 + r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (t : ℕ) :
    D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t) :=
  real_debt_flow_scalar hr (hP t) (hP (t + 1)) (hF t) (hflow t)

/-- Cochrane (2023), p. 379: under the passive rule `s_t = (r/(1+r)) B_{t−1}/P_t`, (16.30) gives
`B_t/P_{t+1} = B_{t−1}/P_t`: real debt `b_t` is constant. -/
theorem passive_real_debt_const_real {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (hrule : ∀ t, s t = r / (1 + r) * b t) :
    ∀ t, b t = b 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [hflow, hrule, ← ih]
    field_simp
    ring

/-- Cochrane (2023), p. 379 ("then the real value of government debt is constant"): with the
passive rule, real debt is constant, `B_{t−1}/P_t = B_{−1}/P_0`. -/
theorem passive_real_debt_const {r : ℝ} (hr : 0 < 1 + r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) (t : ℕ) :
    D t / P t = D 0 / P 0 :=
  passive_real_debt_const_real (b := fun t => D t / P t) hr (real_debt_flow hr hP hF hflow) hpas t

/-- Cochrane (2023), p. 379 ("With constant real debt and the flow condition (16.30) the
transversality condition holds"): with `r > 0` and the passive rule the transversality condition
holds, for every price path. -/
theorem passive_tvc {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) : TVC r P D := by
  have h1 : 0 < 1 + r := by linarith
  have e : (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) = fun T => (1 + r)⁻¹ ^ T * (D 0 / P 0) := by
    funext T
    rw [passive_real_debt_const h1 hP hF hflow hpas T]
  unfold TVC
  rw [e]
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (D 0 / P 0)

/-- Cochrane (2023), p. 379 ("and (16.30) implies (16.26)"): with `r > 0` and the passive rule the
valuation equation (16.26) holds at every date, for every price path. -/
theorem passive_valuation {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) :
    Valuation r P D s := by
  intro t
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs : ∀ j, s (t + j) = r / (1 + r) * (D 0 / P 0) := fun j => by
    rw [hpas (t + j), passive_real_debt_const h1 hP hF hflow hpas (t + j)]
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (r / (1 + r) * (D 0 / P 0))
  have hv : (1 - (1 + r)⁻¹)⁻¹ * (r / (1 + r) * (D 0 / P 0)) = D t / P t := by
    rw [passive_real_debt_const h1 hP hF hflow hpas t]
    have hr0 := hr.ne'
    have hP0 := (hP 0).ne'
    field_simp
    rw [add_sub_cancel_left]
    field_simp
  rw [hv] at hg
  simpa only [hs] using hg

/-- Cochrane (2023), §16.3, p. 368 ("Economics does not rule out nominal explosions") and
p. 379 ("There are lots of ways the government can implement such a policy. We only need to
exhibit one"): for `r > 0`, EVERY positive price path `P` and every initial real debt `b_0` is a
full perfect-foresight equilibrium: with `B_{t−1} = b_0 P_t`, the Fisher rate
`1 + i_t = (1+r)P_{t+1}/P_t` and the passive surplus, the Fisher equation, the flow condition,
the passive rule, the transversality condition and the valuation equation (16.26) all hold. -/
theorem any_price_path_eqm {r : ℝ} (hr : 0 < r) {P : ℕ → ℝ} (hP : ∀ t, 0 < P t) (b0 : ℝ) :
    let D : ℕ → ℝ := fun t => b0 * P t
    let i : ℕ → ℝ := fun t => (1 + r) * (P (t + 1) / P t) - 1
    let s : ℕ → ℝ := fun _ => r / (1 + r) * b0
    FisherPF r P i ∧ Flow P D i s ∧ PassiveRule r P D s ∧ TVC r P D ∧ Valuation r P D s ∧
      ∀ t, D t / P t = b0 := by
  intro D i s
  have h1 : 0 < 1 + r := by linarith
  have hF : FisherPF r P i := fun t => by simp only [i]; ring
  have hD : ∀ t, D t / P t = b0 := fun t => by
    simp only [D]
    field_simp [(hP t).ne']
  have hflow : Flow P D i s := by
    intro t
    have hPt := (hP t).ne'
    have hPt1 := (hP (t + 1)).ne'
    simp only [D, i, s, add_sub_cancel]
    field_simp
  have hpas : PassiveRule r P D s := fun t => by simp only [s]; rw [hD t]
  exact ⟨hF, hflow, hpas, passive_tvc hr hP hF hflow hpas,
    passive_valuation hr hP hF hflow hpas, hD⟩

/-- Cochrane (2023), p. 379, corrected (error E2), one date at a time: under perfect foresight
(16.28) `Π_{t+1} = β(1 + i_t)` the zero bound `i_t ≥ 0` is equivalent to `Π_{t+1} ≥ β` (the book
writes "we cannot have `Π_{t+1} ≤ β`"; the bound is weak). -/
theorem zero_bound_iff_scalar {r i Pi1 : ℝ} (hr : 0 < 1 + r) (h : Pi1 = (1 + r)⁻¹ * (1 + i)) :
    0 ≤ i ↔ (1 + r)⁻¹ ≤ Pi1 := by
  rw [h]
  constructor
  · intro hi
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + i)
      (inv_nonneg.mpr hr.le)
    simpa using this
  · intro hle
    have h2 : (1 + r)⁻¹ * 1 ≤ (1 + r)⁻¹ * (1 + i) := by simpa using hle
    have := le_of_mul_le_mul_left h2 (inv_pos.mpr hr)
    linarith

/-- Cochrane (2023), p. 379 ("the bound `i ≥ 0` means we cannot have `Π_{t+1} < β`"): in the
perfect-foresight equilibrium the nominal rate is nonnegative iff gross inflation is at least
`β = 1/(1+r)`. -/
theorem zero_bound_iff {r : ℝ} (hr : 0 < 1 + r) {P i : ℕ → ℝ} (hF : FisherPF r P i) (t : ℕ) :
    0 ≤ i t ↔ (1 + r)⁻¹ ≤ P (t + 1) / P t :=
  zero_bound_iff_scalar hr (by rw [hF t, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul])

/-! ### The hyperinflation `π_t = φᵗ π_0` -/

/-- Cochrane (2023), §16.3, p. 368 (the path `π_t = φᵗ π_0`): the price level with log inflation
`π_t = φᵗ π_0`, `P_{t+1} = P_t exp(φ^{t+1} π_0)`. -/
noncomputable def hyperP (P0 φ π0 : ℝ) : ℕ → ℝ
  | 0 => P0
  | t + 1 => hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0)

/-- Cochrane (2023), §16.3, p. 368: the hyperinflation price level is positive. -/
theorem hyperP_pos {P0 : ℝ} (hP0 : 0 < P0) (φ π0 : ℝ) (t : ℕ) : 0 < hyperP P0 φ π0 t := by
  induction t with
  | zero => exact hP0
  | succ t ih => exact mul_pos ih (Real.exp_pos _)

/-- Cochrane (2023), §16.3, p. 368: log inflation along the path is
`log(P_{t+1}/P_t) = φ^{t+1} π_0 = φ · φᵗ π_0`. -/
theorem hyper_log_inflation {P0 : ℝ} (hP0 : 0 < P0) (φ π0 : ℝ) (t : ℕ) :
    Real.log (hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) = φ * (φ ^ t * π0) := by
  have h := (hyperP_pos hP0 φ π0 t).ne'
  change Real.log (hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t) = _
  rw [mul_div_cancel_left₀ _ h, Real.log_exp, pow_succ]
  ring

/-- Cochrane (2023), §16.3, p. 368 and (16.4), p. 364: the log-inflation path `π_t = φᵗ π_0` is
an equilibrium of the linear model (16.4) with `u = 0` (under perfect foresight). -/
theorem hyper_linear_eqm (φ π0 : ℝ) :
    Eq164 perfectForesight φ 0 (fun t _ => φ ^ t * π0) := by
  intro t
  funext ω
  change φ ^ (t + 1) * π0 = φ * (φ ^ t * π0) + 0
  rw [pow_succ]
  ring

/-- Cochrane (2023), eqs. (16.27)–(16.29), p. 378, with `Φ(Π) = Π^φ` (the exact nonlinear form of
`i_t = φ π_t` in logs): along the path, gross inflation `Π_t = exp(φᵗ π_0)` obeys
`Π_{t+1} = Φ(Π_t) = Π_t^φ`, and with the Fisher equation the rate obeys the rule
`1 + i_t = (1 + r) Π_t^φ`. -/
theorem hyper_rule {P0 : ℝ} (hP0 : 0 < P0) (r φ π0 : ℝ) {i : ℕ → ℝ}
    (hF : FisherPF r (hyperP P0 φ π0) i) (t : ℕ) :
    hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t = Real.exp (φ ^ t * π0) ^ φ ∧
      1 + i t = (1 + r) * Real.exp (φ ^ t * π0) ^ φ := by
  have hd : hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t = Real.exp (φ ^ t * π0) ^ φ := by
    have h := (hyperP_pos hP0 φ π0 t).ne'
    change hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t = _
    rw [mul_div_cancel_left₀ _ h, ← Real.exp_mul, pow_succ]
    ring_nf
  exact ⟨hd, by rw [hF t, hd]⟩

/-- Cochrane (2023), §16.3, p. 368 (a nominal explosion): for `φ > 1` and `π_0 > 0`, the price
level and gross inflation both go to infinity. -/
theorem hyper_explodes {P0 φ π0 : ℝ} (hP0 : 0 < P0) (hφ : 1 < φ) (hπ0 : 0 < π0) :
    Tendsto (hyperP P0 φ π0) atTop atTop ∧
      Tendsto (fun t => hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) atTop atTop := by
  have hlow : ∀ t : ℕ, P0 * (1 + t * π0) ≤ hyperP P0 φ π0 t := by
    intro t
    induction t with
    | zero => simp [hyperP]
    | succ t ih =>
      rw [Nat.cast_succ]
      change P0 * (1 + ((t : ℝ) + 1) * π0) ≤ hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0)
      have hp : 1 ≤ φ ^ (t + 1) := one_le_pow₀ hφ.le
      have he : 1 + π0 ≤ Real.exp (φ ^ (t + 1) * π0) := by
        have := Real.add_one_le_exp (φ ^ (t + 1) * π0)
        nlinarith
      have hpos : 0 ≤ P0 * (1 + t * π0) := by positivity
      calc P0 * (1 + ((t : ℝ) + 1) * π0) ≤ P0 * (1 + t * π0) * (1 + π0) := by
            nlinarith [mul_pos hP0 (mul_pos hπ0 hπ0), Nat.cast_nonneg (α := ℝ) t]
        _ ≤ hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) :=
            mul_le_mul ih he (by linarith) (hyperP_pos hP0 φ π0 t).le
  refine ⟨tendsto_atTop_mono hlow ?_, ?_⟩
  · refine Tendsto.const_mul_atTop hP0 (tendsto_atTop_add_const_left _ 1 ?_)
    exact Tendsto.atTop_mul_const hπ0 tendsto_natCast_atTop_atTop
  · have e : (fun t => hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) =
        fun t => Real.exp (φ ^ (t + 1) * π0) := by
      funext t
      change hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t = _
      rw [mul_div_cancel_left₀ _ (hyperP_pos hP0 φ π0 t).ne']
    rw [e]
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_pow_atTop_atTop_of_one_lt hφ).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hπ0)

/-- Cochrane (2023), §16.3, p. 368 ("There is no violation of the consumer's transversality
condition in a path `π_t = φᵗ π_0`"): for `r > 0`, `φ > 1`, `π_0 > 0` and any initial real debt
`b_0`, the hyperinflation path is a full perfect-foresight equilibrium under the passive surplus
rule: the Fisher equation, the flow condition, the transversality condition and the valuation
equation (16.26) hold, the rate obeys the exact rule `1 + i_t = (1+r) Π_t^φ`, real debt stays at
`b_0`, and yet the price level explodes. -/
theorem hyperinflation_satisfies_tvc {r P0 φ π0 : ℝ} (hr : 0 < r) (hP0 : 0 < P0) (hφ : 1 < φ)
    (hπ0 : 0 < π0) (b0 : ℝ) :
    ∃ D i s : ℕ → ℝ, FisherPF r (hyperP P0 φ π0) i ∧ Flow (hyperP P0 φ π0) D i s ∧
      PassiveRule r (hyperP P0 φ π0) D s ∧ TVC r (hyperP P0 φ π0) D ∧
      Valuation r (hyperP P0 φ π0) D s ∧ (∀ t, D t / hyperP P0 φ π0 t = b0) ∧
      (∀ t, 1 + i t = (1 + r) * Real.exp (φ ^ t * π0) ^ φ) ∧
      Tendsto (hyperP P0 φ π0) atTop atTop := by
  obtain ⟨hF, hfl, hpas, htvc, hval, hD⟩ := any_price_path_eqm hr (hyperP_pos hP0 φ π0) b0
  exact ⟨_, _, _, hF, hfl, hpas, htvc, hval, hD, fun t => (hyper_rule hP0 r φ π0 hF t).2,
    (hyper_explodes hP0 hφ hπ0).1⟩

/-! ### Under uncertainty -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (16.25), p. 377: the Fisher equation under uncertainty,
`1/(1 + i_t) = β E_t(P_t/P_{t+1})`, `β = 1/(1+r)`. -/
def FisherE (r : ℝ) (P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 1 / (1 + i t ω) = (1 + r)⁻¹ * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω

/-- Cochrane (2023), p. 379: the flow condition `B_t/(1 + i_t) + P_t s_t = B_{t−1}` in every
state (`D_t = B_{t−1}`). -/
def FlowE (P D i s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, D (t + 1) ω / (1 + i t ω) + P t ω * s t ω = D t ω

/-- Cochrane (2023), p. 379: real debt `b_t = B_{t−1}/P_t`. -/
noncomputable def realDebt (P D : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => D t ω / P t ω

/-- Cochrane (2023), p. 379, under uncertainty: with the passive rule
`s_t = (r/(1+r)) B_{t−1}/P_t`, real debt is a martingale, `E_t b_{t+1} = b_t`. Hypotheses: the
pull-out property, positive prices, `B_t/P_t` known at `t` (debt is chosen at `t`). -/
theorem stoch_real_debt_martingale (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) :
    𝔼.E t (realDebt P D (t + 1)) = realDebt P D t := by
  have hsplit : realDebt P D (t + 1) =
      (fun ω => D (t + 1) ω / P t ω) * fun ω => P t ω / P (t + 1) ω := by
    funext ω
    have h1 := (hP t ω).ne'
    have h2 := (hP (t + 1) ω).ne'
    simp only [realDebt, Pi.mul_apply]
    field_simp
  rw [hsplit, hPO t _ _ (hk t)]
  funext ω
  have h1 := (hP t ω).ne'
  have hr' := hr.ne'
  have hi' := hi t ω
  have hE : 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = (1 + r) / (1 + i t ω) := by
    have := hF t ω
    field_simp at this ⊢
    linarith
  have hfl := hflow t ω
  rw [hpas t ω] at hfl
  simp only [Pi.mul_apply, realDebt]
  rw [hE]
  field_simp at hfl ⊢
  linear_combination hfl

/-- Cochrane (2023), p. 379, under uncertainty: with passive fiscal policy expected real debt is
constant at every horizon, `E_t b_{t+j} = b_t` (real debt adapted). -/
theorem stoch_expected_real_debt (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t j : ℕ) :
    𝔼.E t (realDebt P D (t + j)) = realDebt P D t := by
  induction j with
  | zero => exact hb t
  | succ j ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j),
      stoch_real_debt_martingale 𝔼 hPO hr hP hi hk hF hflow hpas (t + j), ih]

/-- Cochrane (2023), §16.3, p. 368, under uncertainty: with `r > 0` and passive fiscal policy,
every equilibrium price process satisfies the transversality condition
`β^T E_t b_{t+T} → 0`, however explosive the price level. -/
theorem stoch_tvc (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * 𝔼.E t (realDebt P D (t + T)) ω) atTop (𝓝 0) := by
  have h1 : 0 < 1 + r := by linarith
  have e : (fun T => (1 + r)⁻¹ ^ T * 𝔼.E t (realDebt P D (t + T)) ω) =
      fun T => (1 + r)⁻¹ ^ T * realDebt P D t ω := by
    funext T
    rw [stoch_expected_real_debt 𝔼 hPO h1 hP hi hk hb hF hflow hpas t T]
  rw [e]
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (realDebt P D t ω)

/-- Cochrane (2023), eq. (16.26), p. 377, under uncertainty: with `r > 0` and passive fiscal
policy, every equilibrium satisfies the valuation equation
`B_{t−1}/P_t = ∑_{j ≥ 0} βʲ E_t s_{t+j}`, as a genuine sum. -/
theorem stoch_valuation (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) (ω : Ω) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * 𝔼.E t (s (t + j)) ω) (realDebt P D t ω) := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs : ∀ j, 𝔼.E t (s (t + j)) ω = r / (1 + r) * realDebt P D t ω := by
    intro j
    have e : s (t + j) = (r / (1 + r)) • realDebt P D (t + j) := by
      funext ω'
      rw [hpas (t + j) ω']
      rfl
    rw [e, map_smul, stoch_expected_real_debt 𝔼 hPO h1 hP hi hk hb hF hflow hpas t j]
    rfl
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (r / (1 + r) * realDebt P D t ω)
  have hv : (1 - (1 + r)⁻¹)⁻¹ * (r / (1 + r) * realDebt P D t ω) = realDebt P D t ω := by
    have hr0 := hr.ne'
    have h1' := h1.ne'
    field_simp
    rw [add_sub_cancel_left]
    field_simp
  rw [hv] at hg
  simpa only [hs] using hg

/-! ### The fiscal theory: real explosions violate the transversality condition -/

/-- Cochrane (2023), eq. (16.30), p. 379, with an exogenous surplus sequence (active fiscal
policy): `b_{t+1} = (1 + r)(b_t − s_t)` for real debt `b_t = B_{t−1}/P_t`. -/
def RealDebtFlow (r : ℝ) (b s : ℕ → ℝ) : Prop := ∀ t, b (t + 1) = (1 + r) * (b t - s t)

/-- Cochrane (2023), (16.30) ⇒ (16.26), p. 379: iterating the real flow
`b_{t+1} = (1 + r)(b_t − s_t)` gives `b_t = Σ_{j<T} βʲ s_{t+j} + βᵀ b_{t+T}`, `β = (1 + r)⁻¹`. -/
theorem pv_partial {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t T : ℕ) :
    b t = ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j) + (1 + r)⁻¹ ^ T * b (t + T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, ← add_assoc t n 1, hflow (t + n), pow_succ]
    field_simp
    ring

/-- Cochrane (2023), eq. (16.30), p. 379, iterated: `β^T b_T = b_0 − ∑_{j<T} βʲ s_j`. -/
theorem ftpl_discounted_debt {r : ℝ} (hr : 0 < 1 + r) {b s : ℕ → ℝ} (h : RealDebtFlow r b s)
    (T : ℕ) : (1 + r)⁻¹ ^ T * b T = b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
  have := pv_partial hr h 0 T
  simp only [zero_add] at this
  linarith

/-- Cochrane (2023), §16.3, p. 369 ("The transversality condition rules out real explosions,
explosions of `B_{t−1}/P_t`"): with `r > 0`, bounded exogenous surpluses and (16.30), the
transversality condition `β^T b_T → 0` holds iff real debt equals the present value of
surpluses, `b_0 = ∑ βʲ s_j`. -/
theorem ftpl_tvc_iff {r M : ℝ} (hr : 0 < r) {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M)
    (h : RealDebtFlow r b s) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop (𝓝 0) ↔
      b 0 = ∑' j, (1 + r)⁻¹ ^ j * s j := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hsum : Summable (fun j => (1 + r)⁻¹ ^ j * s j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs j) (pow_nonneg hβ0 j)
  have hlim : Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop
      (𝓝 (b 0 - ∑' j, (1 + r)⁻¹ ^ j * s j)) := by
    have e : (fun T => (1 + r)⁻¹ ^ T * b T) =
        fun T => b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
      funext T
      exact ftpl_discounted_debt h1 h T
    rw [e]
    exact hsum.hasSum.tendsto_sum_nat.const_sub (b 0)
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h0
    rw [h0, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §16.3, p. 369 ("If the price level is too low, nominal government bonds
appear as net wealth"): with `r > 0` and bounded exogenous surpluses, real debt above the present
value of surpluses explodes, `b_T → ∞` (a real explosion). -/
theorem ftpl_real_explosion {r M : ℝ} (hr : 0 < r) {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M)
    (h : RealDebtFlow r b s) (hb : ∑' j, (1 + r)⁻¹ ^ j * s j < b 0) :
    Tendsto b atTop atTop := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hsum : Summable (fun j => (1 + r)⁻¹ ^ j * s j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs j) (pow_nonneg hβ0 j)
  have hlim : Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop
      (𝓝 (b 0 - ∑' j, (1 + r)⁻¹ ^ j * s j)) := by
    have e : (fun T => (1 + r)⁻¹ ^ T * b T) =
        fun T => b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
      funext T
      exact ftpl_discounted_debt h1 h T
    rw [e]
    exact hsum.hasSum.tendsto_sum_nat.const_sub (b 0)
  have hpow : Tendsto (fun T : ℕ => (1 + r) ^ T) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have e : b = fun T => (1 + r) ^ T * ((1 + r)⁻¹ ^ T * b T) := by
    funext T
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h1.ne', one_pow, one_mul]
  rw [e]
  exact hpow.atTop_mul_pos (sub_pos.mpr hb) hlim

/-- Cochrane (2023), §16.3, p. 369, and Chapter 2: with outstanding nominal debt `B_{−1} > 0`, a
positive present value of surpluses and `b_0 = B_{−1}/P_0`, the transversality condition holds
iff `P_0 = B_{−1}/PV`; a lower price level makes real debt explode. -/
theorem ftpl_price_level_iff {r M Bm P0 : ℝ} (hr : 0 < r) (hBm : 0 < Bm) (hP0 : 0 < P0)
    {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M) (h : RealDebtFlow r b s) (hb0 : b 0 = Bm / P0)
    (hpv : 0 < ∑' j, (1 + r)⁻¹ ^ j * s j) :
    (Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop (𝓝 0) ↔
      P0 = Bm / ∑' j, (1 + r)⁻¹ ^ j * s j) ∧
      (P0 < Bm / ∑' j, (1 + r)⁻¹ ^ j * s j → Tendsto b atTop atTop) := by
  rw [ftpl_tvc_iff hr hs h, hb0]
  refine ⟨?_, fun hlow => ftpl_real_explosion hr hs h ?_⟩
  · constructor
    · intro e
      rw [← e, div_div_cancel₀ hBm.ne']
    · intro e
      rw [e, div_div_cancel₀ hBm.ne']
  · rw [hb0, lt_div_iff₀ hP0]
    rwa [lt_div_iff₀ hpv, mul_comm] at hlow

/-! ### §16.4: central-bank destabilisation -/

/-- Cochrane (2023), §16.4, p. 369 (`E_t π_{t+1} = φ π_t`, no disturbance): in every equilibrium
`E_t π_{t+j} = φʲ π_t`. -/
theorem expected_path {φ : ℝ} {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ 0 π)
    (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t := by
  have h0 : Eq164 𝔼 φ 0 (0 : ℕ → Ω → ℝ) := fun t => by simp
  have := sunspot_expected 𝔼 (π := 0) (π' := π) (fun t => by simp) hπ h0 h t j
  simpa using this

/-- Cochrane (2023), §16.4, p. 369 ("with `φ < 1`, this economy is stable"): for `|φ| < 1`
expected inflation converges to zero from any initial value. -/
theorem stable_of_abs_lt_one {φ : ℝ} (hφ : |φ| < 1) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π (t + j)) ω) = fun j => φ ^ j * π t ω := by
    funext j
    rw [expected_path 𝔼 hπ h t j, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π t ω)

/-- Cochrane (2023), §16.4, p. 369 ("The central bank deliberately makes the economy unstable by
following `φ > 1`"): for `|φ| > 1`, wherever inflation is nonzero expected inflation diverges,
`|E_t π_{t+j}| → ∞`. -/
theorem unstable_of_one_lt_abs {φ : ℝ} (hφ : 1 < |φ|) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) {t : ℕ} {ω : Ω} (hω : π t ω ≠ 0) :
    Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  have e : (fun j => |𝔼.E t (π (t + j)) ω|) = fun j => |φ| ^ j * |π t ω| := by
    funext j
    rw [expected_path 𝔼 hπ h t j, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hω)

/-- Cochrane (2023), §16.4, p. 370 ("oscillating inflation and deflation are even ghastlier"):
for `φ < −1`, every equilibrium with `π_t > 0` is expected to alternate in sign,
`E_t π_{t+2j} > 0 > E_t π_{t+2j+1}`, with exploding magnitude. -/
theorem oscillating_of_lt_neg_one {φ : ℝ} (hφ : φ < -1) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) {t : ℕ} {ω : Ω} (hω : 0 < π t ω) :
    (∀ j, 0 < 𝔼.E t (π (t + 2 * j)) ω ∧ 𝔼.E t (π (t + (2 * j + 1))) ω < 0) ∧
      Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  have habs : 1 < |φ| := by
    rw [abs_of_neg (by linarith)]
    linarith
  refine ⟨fun j => ?_, unstable_of_one_lt_abs 𝔼 habs hπ h hω.ne'⟩
  rw [expected_path 𝔼 hπ h t, expected_path 𝔼 hπ h t]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h2 : 0 < φ ^ (2 * j) := by
    rw [pow_mul]
    exact pow_pos (by nlinarith) j
  constructor
  · exact mul_pos h2 hω
  · rw [pow_succ]
    have : φ ^ (2 * j) * φ < 0 := mul_neg_of_pos_of_neg h2 (by linarith)
    exact mul_neg_of_neg_of_pos this hω

/-- Cochrane (2023), §16.4, p. 370 ("In this model `φ < −1` is as good as `φ > 1` to produce local
determinacy"): for `φ < −1`, (16.4) has exactly one bounded equilibrium for every bounded adapted
disturbance. -/
theorem determinate_of_lt_neg_one [Nonempty Ω] {φ : ℝ} (hφ : φ < -1) :
    ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ Eq164 𝔼 φ u π := by
  refine (determinate_iff 𝔼 φ).mpr ?_
  rw [abs_of_neg (by linarith)]
  linarith

end Cochrane.NewKeynesianSelection.Hyperinflation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Identification of the new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.5 "Identification"
(pp. 370–372), §16.9 "Identification patches" (pp. 380–383) and §16.10.7 "Learning and other
selection devices" (pp. 394–395).

The simplest new-Keynesian model (16.1)–(16.2) is `i_t = E_t π_{t+1}`, `i_t = φ π_t + u_t`;
the new-Keynesian selection keeps the unique bounded ("locally bounded") solution of
(16.4) `E_t π_{t+1} = φ π_t + u_t`, which exists for `|φ| > 1`. The innovation operator and
shocks are those of `Innovation`, (16.4), its uniqueness lemma and the AR(1) path
`π = −u/(φ − η)` those of `SimplestModel` (`Eq164`, `eq164_unique`, `ar1Pi`, `ar1Pi_eq164`);
the equilibrium notions `NKEq`, `Selected`, `KingEq` and `FTPLEq` of this module are linked to
the `SimplestModel`, `KingForm` and `FTPLSimple` ones in `Links`.

Every result holds for an arbitrary `ExpectationSystem` (perfect foresight and genuine
uncertainty) and is **pathwise**: "observationally equivalent" means that the observable
processes are equal as functions `ℕ → Ω → ℝ`, which is stronger than equality of their laws
(`law_obs_eq`). Regression statements are finite-sample algebraic identities.

## Main results

* NI-1 (p. 371, reverse engineering): `reverse_nkEq`, `reverse_selected`: for every bounded
  adapted inflation process and EVERY `φ` with `|φ| > 1`, `u = i − φπ` makes it the selected
  equilibrium; `nk_fiber_eq` (the set of `φ` consistent with any data is all of `1 < |φ|`),
  `phi_not_identified`, `u_not_identified`. Conversely `u_eq_of_nkEq` (knowing `φ` gives `u`)
  and `phi_eq_of_same_u` (knowing `u` gives `φ`), as the book says.
* NI-2/NI-3, (16.9)–(16.11), (16.15)–(16.18): `ar1_selected`, `eq_16_10`, `eq_16_15`,
  `eq_16_16_innov`, `eq_16_18`, `ar1_obs`, `obs_selected_every_phi`, `ni2_same_iff`,
  `ni2_rescaled`.
* Finite-sample regressions: `olsNoInt_eq`, `olsSlope_eq`, `olsIntercept_eq_zero`,
  `ivEst_eq` (any instrument), `ni3_ols`, `ni3_ols_ne_phi`, `ni3_iv`, `ols_ar_eq`.
* NI-4, (16.19): `king_bounded_eq`, `king_eq_set`, `king_eq_set_indep`, `king_selection_zero`.
* §16.9: `thetaRule_eq_obs` (equilibrium data are `i = θπ + u`, free of `φ`),
  `iv_identifies_iff` (an instrument orthogonal to `u` measures `φ` iff `θ = φ`),
  `theta_eq_phi_no_shock_zero` (with `θ = φ`, `u = 0` the only bounded equilibrium is `π = 0`:
  identification needs other shocks), the real-rate-shock model `rr_iv_eq_phi_add` and
  `rr_iv_eq_phi_iff`, `rr_example` (a non-vacuous identified case).
* §16.10.7: `identified_iff_learnable`, `phi_not_learnable`, `ftpl_theta_identified`,
  `ftpl_theta_learnable`; `law_obs_eq` ("the likelihood does not involve `φ`").
-/

namespace Cochrane.NewKeynesianSelection.Identification

open Filter Topology
open Innovation (innov IsShock AR1Law innov_eq_sub_E isShock_smul)
open SimplestModel (Eq164 eq164_unique ar1Pi ar1Pi_eq164 ar1Pi_adapted ar1Pi_bounded)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Cochrane (2023), (16.1), p. 364: the interest rate implied by the Fisher equation,
`i_t = E_t π_{t+1}`. -/
def fisherRate (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (π (t + 1))

/-- Cochrane (2023), (16.1)–(16.2), p. 364: `(π, i)` is an equilibrium of the simplest
new-Keynesian model with rule `i_t = φ π_t + u_t`: `π` adapted, `i_t = E_t π_{t+1}`,
`i_t = φ π_t + u_t`. -/
def NKEq (φ : ℝ) (u π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • π t + u t

/-- Cochrane (2023), (16.4), p. 364: eliminating `i`, (16.1)–(16.2) hold iff (16.4) holds and
`i` is the Fisher rate. -/
theorem nkEq_iff (φ : ℝ) (u π i : ℕ → Ω → ℝ) :
    NKEq 𝔼 φ u π i ↔ 𝔼.Adapted π ∧ Eq164 𝔼 φ u π ∧ i = fisherRate 𝔼 π := by
  constructor
  · rintro ⟨ha, hf, hr⟩
    exact ⟨ha, fun t => (hf t).symm.trans (hr t), funext fun t => hf t⟩
  · rintro ⟨ha, h4, rfl⟩
    exact ⟨ha, fun t => rfl, fun t => h4 t⟩

/-- Cochrane (2023), (16.6), p. 364: the new-Keynesian selection. `π` is "the unique
locally-bounded equilibrium" given `(φ, u)`: it is bounded, adapted, solves (16.4), and every
bounded solution of (16.4) equals it. -/
def Selected (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  BoundedProc π ∧ 𝔼.Adapted π ∧ Eq164 𝔼 φ u π ∧
    ∀ π' : ℕ → Ω → ℝ, BoundedProc π' → Eq164 𝔼 φ u π' → π' = π

/-- Cochrane (2023), (16.6), p. 364: for `|φ| > 1` a bounded adapted solution of (16.4) is
the selected equilibrium. -/
theorem selected_of {φ : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ} (hb : BoundedProc π)
    (ha : 𝔼.Adapted π) (h : Eq164 𝔼 φ u π) : Selected 𝔼 φ u π :=
  ⟨hb, ha, h, fun _ hb' h' => eq164_unique 𝔼 hφ h' h hb' hb⟩

/-- Cochrane (2023), (16.6), p. 364: the selected equilibrium given `(φ, u)` is unique. -/
theorem selected_unique {φ : ℝ} {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Selected 𝔼 φ u π₁)
    (h₂ : Selected 𝔼 φ u π₂) : π₁ = π₂ :=
  h₂.2.2.2 π₁ h₁.1 h₁.2.2.1

/-! ### NI-1: reverse engineering (p. 371) -/

/-- Cochrane (2023), p. 371: the reverse-engineered disturbance `u_t = i_t − φ π_t` with
`i_t = E_t π_{t+1}`. -/
def reverseU (φ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fisherRate 𝔼 π t - φ • π t

/-- Cochrane (2023), p. 371 ("Choose any process `{π_t}` … Choose any `φ`. Construct
`u_t = i_t − φπ_t`"): every adapted inflation process with `i_t = E_t π_{t+1}` is an equilibrium
of (16.1)–(16.2) for every `φ`. -/
theorem reverse_nkEq {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (φ : ℝ) :
    NKEq 𝔼 φ (reverseU 𝔼 φ π) π (fisherRate 𝔼 π) :=
  ⟨ha, fun _ => rfl, fun t => by rw [reverseU]; abel⟩

/-- Cochrane (2023), p. 371: for every bounded adapted `π` and every `φ` with `|φ| > 1`, `π` is
the new-Keynesian selected (unique bounded) equilibrium of `(φ, u = i − φπ)`. -/
theorem reverse_selected {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (hb : BoundedProc π) {φ : ℝ}
    (hφ : 1 < |φ|) : Selected 𝔼 φ (reverseU 𝔼 φ π) π :=
  selected_of 𝔼 hφ hb ha fun t => by
    change fisherRate 𝔼 π t = φ • π t + (fisherRate 𝔼 π t - φ • π t)
    abel

/-- Cochrane (2023), p. 371 ("observation of `π_t` and `i_t` cannot tell us `φ` and `u_t`"):
every bounded equilibrium of (16.1)–(16.2), whatever `(φ₀, u₀)` generated it, is the selected
equilibrium of `(φ, i − φπ)` for every `φ` with `|φ| > 1`. -/
theorem every_eq_selected {φ₀ : ℝ} {u₀ π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ₀ u₀ π i)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) :
    NKEq 𝔼 φ (fun t => i t - φ • π t) π i ∧ Selected 𝔼 φ (fun t => i t - φ • π t) π := by
  have hi : i = fisherRate 𝔼 π := ((nkEq_iff 𝔼 _ _ _ _).mp h).2.2
  subst hi
  exact ⟨reverse_nkEq 𝔼 h.1 φ, reverse_selected 𝔼 h.1 hb hφ⟩

/-- Cochrane (2023), p. 371 ("If you could observe the parameter `φ`, you could calculate
`u_t = i_t − φπ_t`"): given `φ`, the disturbance is determined by the data. -/
theorem u_eq_of_nkEq {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t : ℕ) :
    u t = i t - φ • π t := by
  rw [h.2.2 t]; abel

/-- Cochrane (2023), p. 371 ("If you could observe monetary policy disturbances `u_t` directly,
you could infer `φ`"): two values of `φ` with the same `u` and the same data agree as soon as
inflation is nonzero somewhere. -/
theorem phi_eq_of_same_u {φ₁ φ₂ : ℝ} {u π i : ℕ → Ω → ℝ} (h₁ : NKEq 𝔼 φ₁ u π i)
    (h₂ : NKEq 𝔼 φ₂ u π i) {t : ℕ} {ω : Ω} (hπ : π t ω ≠ 0) : φ₁ = φ₂ := by
  have e := congrFun ((h₁.2.2 t).symm.trans (h₂.2.2 t)) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e
  exact mul_right_cancel₀ hπ e

/-- Cochrane (2023), p. 371: the reverse-engineered disturbances of two values of `φ` differ by
`(φ₂ − φ₁) π`, so the disturbance is not identified unless `π ≡ 0`. -/
theorem reverseU_sub (φ₁ φ₂ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    reverseU 𝔼 φ₁ π t - reverseU 𝔼 φ₂ π t = (φ₂ - φ₁) • π t := by
  simp only [reverseU, sub_smul]
  abel

/-! ### Identification and learnability as properties of a model class -/

/-- Cochrane (2023), §16.5, p. 370, and §16.10.7, p. 394: a parameter `par` is identified on
the set `S` of model specifications by the observation map `obs` if specifications in `S`
with the same observables have the same parameter. -/
def IdentifiedOn {M O P : Type*} (S : Set M) (obs : M → O) (par : M → P) : Prop :=
  ∀ m₁ ∈ S, ∀ m₂ ∈ S, obs m₁ = obs m₂ → par m₁ = par m₂

/-- Cochrane (2023), §16.10.7, p. 394 ("people in the economy cannot learn it any more than
econometricians can"): a parameter is identified iff some learning rule, a function of the
observables only, recovers it on the whole class. -/
theorem identified_iff_learnable {M O P : Type*} [Inhabited P] (S : Set M) (obs : M → O)
    (par : M → P) : IdentifiedOn S obs par ↔ ∃ L : O → P, ∀ m ∈ S, L (obs m) = par m := by
  classical
  constructor
  · intro h
    refine ⟨fun o => if hx : ∃ m ∈ S, obs m = o then par hx.choose else default,
      fun m hm => ?_⟩
    have hx : ∃ m' ∈ S, obs m' = obs m := ⟨m, hm, rfl⟩
    simp only [hx, ↓reduceDIte]
    exact h _ hx.choose_spec.1 m hm hx.choose_spec.2
  · rintro ⟨L, hL⟩ m₁ h₁ m₂ h₂ he
    rw [← hL m₁ h₁, ← hL m₂ h₂, he]

/-- Cochrane (2023), §16.5, p. 370: the class of new-Keynesian specifications `(φ, u, π)` with
`|φ| > 1` and `π` the selected equilibrium of `(φ, u)`. -/
def nkClass : Set (ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {m | 1 < |m.1| ∧ Selected 𝔼 m.1 m.2.1 m.2.2}

/-- Cochrane (2023), §16.5, p. 371: what is observed of a specification, the processes
`(π, i)` with `i_t = E_t π_{t+1}`. -/
def nkObs (m : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (m.2.2, fisherRate 𝔼 m.2.2)

/-- Cochrane (2023), p. 371 ("the observable dynamics are the same for any value of `φ`"): the
set of `φ` consistent with ANY observed equilibrium of the class is all of `{φ : 1 < |φ|}`. -/
theorem nk_fiber_eq {m : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)} (hm : m ∈ nkClass 𝔼) :
    {φ | ∃ m' ∈ nkClass 𝔼, nkObs 𝔼 m' = nkObs 𝔼 m ∧ m'.1 = φ} = {φ | 1 < |φ|} := by
  ext φ
  constructor
  · rintro ⟨m', hm', -, rfl⟩
    exact hm'.1
  · intro hφ
    exact ⟨(φ, reverseU 𝔼 φ m.2.2, m.2.2),
      ⟨hφ, reverse_selected 𝔼 hm.2.2.1 hm.2.1 hφ⟩, rfl, rfl⟩

/-- Cochrane (2023), p. 370 ("The parameter `φ` is not identified"): the zero process is the
selected equilibrium of `(φ, 0)` for every `|φ| > 1`. -/
theorem zero_selected {φ : ℝ} (hφ : 1 < |φ|) : Selected 𝔼 φ 0 0 :=
  selected_of 𝔼 hφ ⟨0, fun _ _ => by simp⟩ (fun t => by simp) fun t => by simp

/-- Cochrane (2023), §16.5, p. 370: `φ` is not identified from equilibrium time series. -/
theorem phi_not_identified : ¬ IdentifiedOn (nkClass 𝔼) (nkObs 𝔼) Prod.fst := by
  intro h
  have h2 : (2 : ℝ) ∈ {φ : ℝ | 1 < |φ|} := by norm_num
  have h3 : (3 : ℝ) ∈ {φ : ℝ | 1 < |φ|} := by norm_num
  have := h (2, 0, 0) ⟨h2, zero_selected 𝔼 h2⟩ (3, 0, 0) ⟨h3, zero_selected 𝔼 h3⟩ rfl
  norm_num at this

/-- Cochrane (2023), p. 371 ("The monetary-policy disturbances `u_t` are also not identified"):
whenever inflation is nonzero somewhere, the same data come from two different disturbance
processes. -/
theorem u_not_identified {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (hb : BoundedProc π) {t : ℕ}
    {ω : Ω} (hπ : π t ω ≠ 0) :
    ∃ m₁ ∈ nkClass 𝔼, ∃ m₂ ∈ nkClass 𝔼, nkObs 𝔼 m₁ = nkObs 𝔼 m₂ ∧ m₁.2.1 ≠ m₂.2.1 := by
  have h2 : 1 < |(2 : ℝ)| := by norm_num
  have h3 : 1 < |(3 : ℝ)| := by norm_num
  refine ⟨(2, reverseU 𝔼 2 π, π), ⟨h2, reverse_selected 𝔼 ha hb h2⟩,
    (3, reverseU 𝔼 3 π, π), ⟨h3, reverse_selected 𝔼 ha hb h3⟩, rfl, fun he => hπ ?_⟩
  have e := congrFun (reverseU_sub 𝔼 2 3 π t) ω
  have e2 : reverseU 𝔼 2 π t ω = reverseU 𝔼 3 π t ω := by
    rw [show reverseU 𝔼 2 π = reverseU 𝔼 3 π from he]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e2, sub_self] at e
  linarith

/-- Cochrane (2023), §16.10.7, p. 394 ("the parameter `φ` … not identified … People in the
economy cannot learn it"): no learning rule, i.e. no function of the observed equilibrium
processes, recovers `φ` on the new-Keynesian class. -/
theorem phi_not_learnable :
    ¬ ∃ L : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) → ℝ, ∀ m ∈ nkClass 𝔼, L (nkObs 𝔼 m) = m.1 := by
  rw [← identified_iff_learnable]
  exact phi_not_identified 𝔼

/-- Cochrane (2023), p. 371 ("The likelihood function does not involve `φ`"): for any
probability model on `Ω` and any measurable structure on the observation space, the law of the
observables generated by `(φ₁, i − φ₁π)` and by `(φ₂, i − φ₂π)` is the same. -/
theorem law_obs_eq [MeasurableSpace Ω] (mO : MeasurableSpace (ℕ → ℝ × ℝ))
    (μ : MeasureTheory.Measure Ω) {m₁ m₂ : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)}
    (he : nkObs 𝔼 m₁ = nkObs 𝔼 m₂) :
    μ.map (fun ω t => ((nkObs 𝔼 m₁).1 t ω, (nkObs 𝔼 m₁).2 t ω)) =
      μ.map (fun ω t => ((nkObs 𝔼 m₂).1 t ω, (nkObs 𝔼 m₂).2 t ω)) := by
  rw [he]

/-! ### The AR(1) disturbance: (16.9)–(16.11), (16.15)–(16.18) -/

/-- Cochrane (2023), p. 365: the AR(1) disturbance `u_{t+1} = η u_t + ε_{i,t+1}`: `u` adapted,
`ε` a shock (`Innovation.IsShock`) and the law of motion `Innovation.AR1Law`. -/
def AR1 (η : ℝ) (u ε : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted u ∧ IsShock 𝔼 ε ∧ AR1Law η u ε

/-- Cochrane (2023), p. 365: an AR(1) disturbance has `E_t u_{t+1} = η u_t`. -/
theorem AR1.E_succ {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    𝔼.E t (u (t + 1)) = η • u t := by
  rw [h.2.2 t, map_add, map_smul, h.1 t, h.2.1.2 t, add_zero]

/-- Cochrane (2023), p. 365: an AR(1) disturbance is `IsAR1 η` in the sense of the core. -/
theorem AR1.isAR1 {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) : 𝔼.IsAR1 η u :=
  ⟨h.1, h.E_succ 𝔼⟩

/-- Cochrane (2023), (16.6) and (16.9), p. 365: for `|φ| > 1`, `φ ≠ η` and a bounded AR(1)
disturbance, `π_t = −u_t/(φ − η)` is the selected equilibrium. -/
theorem ar1_selected {φ η : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ}
    (h : AR1 𝔼 η u ε) (hub : BoundedProc u) : Selected 𝔼 φ u (ar1Pi φ η u) := by
  obtain ⟨M, hM⟩ := hub
  exact selected_of 𝔼 hφ (ar1Pi_bounded φ η hM) (ar1Pi_adapted 𝔼 φ η h.1)
    (ar1Pi_eq164 𝔼 hφη (h.isAR1 𝔼))

/-- Cochrane (2023), (16.10), p. 365: `π_{t+1} = η π_t − ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_10 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    ar1Pi φ η u (t + 1) = η • ar1Pi φ η u t + (-(φ - η)⁻¹) • ε (t + 1) :=
  SimplestModel.ar1_law_1610 h.2.2 t

/-- Cochrane (2023), (16.11) and (16.15), p. 365 and p. 371: in the selected equilibrium
`i_t = E_t π_{t+1} = −η u_t/(φ − η) = η π_t`, with no error. -/
theorem eq_16_15 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    fisherRate 𝔼 (ar1Pi φ η u) t = η • ar1Pi φ η u t ∧
      fisherRate 𝔼 (ar1Pi φ η u) t = (-(η * (φ - η)⁻¹)) • u t := by
  have e : fisherRate 𝔼 (ar1Pi φ η u) t = η • ar1Pi φ η u t := by
    simp only [fisherRate, ar1Pi, map_smul, h.E_succ 𝔼 t, smul_smul, mul_comm]
  refine ⟨e, ?_⟩
  rw [e]
  simp only [ar1Pi, smul_smul]
  congr 1
  ring

/-- Cochrane (2023), (16.16), p. 371: the inflation innovation is
`ε_{π,t+1} = ΔE_{t+1} π_{t+1} = −ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_16_innov (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    innov 𝔼 t (ar1Pi φ η u (t + 1)) = (-(φ - η)⁻¹) • ε (t + 1) := by
  rw [innov_eq_sub_E 𝔼 (ar1Pi_adapted 𝔼 φ η h.1 (t + 1)), ← fisherRate, (eq_16_15 𝔼 φ h t).1,
    eq_16_10 𝔼 φ h t]
  abel

/-- Cochrane (2023), (16.3) and (16.18), pp. 364, 371: with the passive fiscal response
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}`, `ε_{π,t+1} = −ε_{Σs,t+1}` and
`ε_{Σs,t+1} = ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_18 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    innov 𝔼 t (ar1Pi φ η u (t + 1)) = -(-innov 𝔼 t (ar1Pi φ η u (t + 1))) ∧
      -innov 𝔼 t (ar1Pi φ η u (t + 1)) = (φ - η)⁻¹ • ε (t + 1) := by
  refine ⟨(neg_neg _).symm, ?_⟩
  rw [eq_16_16_innov 𝔼 φ h t, neg_smul, neg_neg]

/-- Cochrane (2023), (16.16)–(16.17), p. 371: the observable system. `π` is adapted,
`π_{t+1} = η π_t + ε_{π,t+1}` with `ε_π` a shock, and `i_t = η π_t`. -/
def ObsAR1 (η : ℝ) (π i επ : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ IsShock 𝔼 επ ∧ (∀ t, π (t + 1) = η • π t + επ (t + 1)) ∧ ∀ t, i t = η • π t

/-- Cochrane (2023), (16.16)–(16.18), p. 371 ("all we observe of the model"): the selected
AR(1) equilibrium obeys the observable system with persistence `η` and inflation shock
`ε_π = −ε_i/(φ − η)`; `φ` enters only through the scale of the shock. -/
theorem ar1_obs (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    ObsAR1 𝔼 η (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u))
      (fun t => (-(φ - η)⁻¹) • ε t) := by
  exact ⟨ar1Pi_adapted 𝔼 φ η h.1, isShock_smul 𝔼 h.2.1 _, eq_16_10 𝔼 φ h,
    fun t => (eq_16_15 𝔼 φ h t).1⟩

/-- Cochrane (2023), p. 371 ("The observable `{i_t, π_t, s_t}` dynamics are the same for any
value of `φ`"): conversely, any bounded process obeying the observable system (16.16)–(16.17)
is, for EVERY `φ` with `|φ| > 1` and `φ ≠ η`, the selected equilibrium of the AR(1) model with
disturbance `u = −(φ − η) π` and shock `ε_i = −(φ − η) ε_π`. -/
theorem obs_selected_every_phi {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) :
    AR1 𝔼 η (fun t => (-(φ - η)) • π t) (fun t => (-(φ - η)) • επ t) ∧
      ar1Pi φ η (fun t => (-(φ - η)) • π t) = π ∧
      Selected 𝔼 φ (fun t => (-(φ - η)) • π t) π ∧ i = fisherRate 𝔼 π := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  obtain ⟨ha, ⟨hεa, hε0⟩, hπ, hi⟩ := h
  have har : AR1 𝔼 η (fun t => (-(φ - η)) • π t) (fun t => (-(φ - η)) • επ t) :=
    ⟨fun s => by simp only [map_smul, ha s], ⟨fun s => by simp only [map_smul, hεa s],
      fun s => by simp only [map_smul, hε0 s, smul_zero]⟩,
      fun t => by simp only [hπ t, smul_add, smul_smul, mul_comm]⟩
  have hpi : ar1Pi φ η (fun t => (-(φ - η)) • π t) = π := by
    funext t
    simp only [ar1Pi, smul_smul]
    rw [show -(φ - η)⁻¹ * -(φ - η) = 1 by field_simp, one_smul]
  have hEπ : ∀ t, 𝔼.E t (π (t + 1)) = η • π t := fun t => by
    rw [hπ t, map_add, map_smul, ha t, hε0 t, add_zero]
  obtain ⟨M, hM⟩ := hb
  have hub : BoundedProc (fun t => (-(φ - η)) • π t) :=
    ⟨|φ - η| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  refine ⟨har, hpi, ?_, funext fun t => (hi t).trans (hEπ t).symm⟩
  have hs := ar1_selected 𝔼 hφ hφη har hub
  rwa [hpi] at hs

/-- Cochrane (2023), pp. 370–371 (NI-2): with the same `η`, the selected equilibria of
`(φ, u)` and `(φ', u')` coincide iff `u/(φ − η) = u'/(φ' − η)`; `φ` and the disturbance enter
only through this ratio. -/
theorem ni2_same_iff (φ φ' η : ℝ) (u u' : ℕ → Ω → ℝ) :
    ar1Pi φ η u = ar1Pi φ' η u' ↔
      (fun t => (φ - η)⁻¹ • u t) = fun t => (φ' - η)⁻¹ • u' t := by
  constructor
  · intro h
    funext t
    have := congrFun h t
    simp only [ar1Pi, neg_smul] at this
    exact neg_inj.mp this
  · intro h
    funext t
    have := congrFun h t
    simp only [ar1Pi, neg_smul, this]

/-- Cochrane (2023), pp. 370–371 (NI-2): rescaling the disturbance (and so its shock
`ε' = ε (φ' − η)/(φ − η)`) by `(φ' − η)/(φ − η)` leaves the selected equilibrium unchanged. -/
theorem ni2_rescaled {φ φ' η : ℝ} (hφη : φ ≠ η) (hφη' : φ' ≠ η) (u : ℕ → Ω → ℝ) :
    ar1Pi φ' η (fun t => ((φ' - η) / (φ - η)) • u t) = ar1Pi φ η u := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  have hne' : φ' - η ≠ 0 := sub_ne_zero.mpr hφη'
  funext t
  simp only [ar1Pi, smul_smul]
  congr 1
  field_simp

/-! ### Finite-sample regressions -/

/-- Cochrane (2023), (16.15), p. 371: the OLS coefficient of `y` on `x` without intercept on
the sample `t = 0, …, T − 1`, `∑ x y / ∑ x²`. -/
noncomputable def olsNoInt (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, x t * y t) / ∑ t ∈ Finset.range T, x t ^ 2

/-- Cochrane (2023), p. 371: the sample mean on `t = 0, …, T − 1`. -/
noncomputable def sampleMean (x : ℕ → ℝ) (T : ℕ) : ℝ := (∑ t ∈ Finset.range T, x t) / T

/-- Cochrane (2023), (16.15), p. 371: the OLS slope of `y` on `x` with an intercept,
`∑ (x − x̄)(y − ȳ) / ∑ (x − x̄)²`. -/
noncomputable def olsSlope (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (x t - sampleMean x T) * (y t - sampleMean y T)) /
    ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2

/-- Cochrane (2023), (16.15), p. 371: the OLS intercept `ȳ − b x̄`. -/
noncomputable def olsIntercept (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  sampleMean y T - olsSlope x y T * sampleMean x T

/-- Cochrane (2023), p. 371 ("No instrument can help") and p. 382: the instrumental-variables
estimate with instrument `z`, `∑ z y / ∑ z x`. -/
noncomputable def ivEst (z x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, z t * y t) / ∑ t ∈ Finset.range T, z t * x t

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample and `∑ x² ≠ 0`, the OLS
coefficient without intercept is exactly `η`. -/
theorem olsNoInt_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, x t ^ 2 ≠ 0) : olsNoInt x y T = η := by
  have e : ∑ t ∈ Finset.range T, x t * y t = η * ∑ t ∈ Finset.range T, x t ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [olsNoInt, e, mul_div_assoc, div_self hx, mul_one]

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample, `ȳ = η x̄`. -/
theorem sampleMean_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t) :
    sampleMean y T = η * sampleMean x T := by
  have e : ∑ t ∈ Finset.range T, y t = η * ∑ t ∈ Finset.range T, x t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht => h t (Finset.mem_range.mp ht)
  rw [sampleMean, sampleMean, e, mul_div_assoc]

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample and the sample variance of
`x` is positive, the OLS slope with intercept is exactly `η`. -/
theorem olsSlope_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 ≠ 0) : olsSlope x y T = η := by
  have e : ∑ t ∈ Finset.range T, (x t - sampleMean x T) * (y t - sampleMean y T) =
      η * ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 := by
    rw [Finset.mul_sum, sampleMean_eq h]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [olsSlope, e, mul_div_assoc, div_self hx, mul_one]

/-- Cochrane (2023), (16.15), p. 371 ("with no error"): if `y_t = η x_t` on the sample, the OLS
intercept is zero. -/
theorem olsIntercept_eq_zero {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 ≠ 0) : olsIntercept x y T = 0 := by
  rw [olsIntercept, olsSlope_eq h hx, sampleMean_eq h, sub_self]

/-- Cochrane (2023), p. 382: if `y_t = b x_t + e_t` on the sample, the IV estimate is
`b + ∑ z e / ∑ z x`. -/
theorem ivEst_eq_add {z x y e : ℕ → ℝ} {b : ℝ} {T : ℕ} (h : ∀ t < T, y t = b * x t + e t)
    (hzx : ∑ t ∈ Finset.range T, z t * x t ≠ 0) :
    ivEst z x y T = b + (∑ t ∈ Finset.range T, z t * e t) / ∑ t ∈ Finset.range T, z t * x t := by
  have e1 : ∑ t ∈ Finset.range T, z t * y t =
      b * ∑ t ∈ Finset.range T, z t * x t + ∑ t ∈ Finset.range T, z t * e t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [ivEst, e1, add_div, mul_div_assoc, div_self hzx, mul_one]

/-- Cochrane (2023), p. 371 ("No instrument can help"): if `y_t = η x_t` on the sample, every
instrument with `∑ z x ≠ 0` gives exactly `η`. -/
theorem ivEst_eq {z x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hzx : ∑ t ∈ Finset.range T, z t * x t ≠ 0) : ivEst z x y T = η := by
  rw [ivEst_eq_add (e := 0) (fun t ht => by rw [h t ht, Pi.zero_apply, add_zero]) hzx]
  simp

/-- Cochrane (2023), (16.15), p. 371 ("A regression of `i_t` on `π_t` in data from this model
produces `η` not `φ`"): in the selected AR(1) equilibrium, along every history `ω` and on every
sample with `∑ π² ≠ 0`, OLS of `i` on `π` gives exactly `η`, for every `φ`. -/
theorem ni3_ols (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, ar1Pi φ η u t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  olsNoInt_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hx

/-- Cochrane (2023), (16.15), p. 371: the same holds for OLS with an intercept. -/
theorem ni3_ols_slope (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, (ar1Pi φ η u t ω - sampleMean (fun t => ar1Pi φ η u t ω) T) ^ 2
      ≠ 0) :
    olsSlope (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  olsSlope_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hx

/-- Cochrane (2023), p. 371: so the regression does not measure `φ` whenever `φ ≠ η`. -/
theorem ni3_ols_ne_phi {φ η : ℝ} (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω)
    {T : ℕ} (hx : ∑ t ∈ Finset.range T, ar1Pi φ η u t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T ≠ φ := by
  rw [ni3_ols 𝔼 φ h ω hx]
  exact Ne.symm hφη

/-- Cochrane (2023), p. 371 ("No instrument can help"): every instrument gives `η`. -/
theorem ni3_iv (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) (z : ℕ → ℝ)
    {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * ar1Pi φ η u t ω ≠ 0) :
    ivEst z (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  ivEst_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hzx

/-- Cochrane (2023), (16.16), p. 371: the autoregression of observed inflation is the
finite-sample identity `b = η + ∑ π_t ε_{π,t+1} / ∑ π_t²`, which involves only observables. -/
theorem ols_ar_eq {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, π t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => π t ω) (fun t => π (t + 1) ω) T =
      η + (∑ t ∈ Finset.range T, π t ω * επ (t + 1) ω) / ∑ t ∈ Finset.range T, π t ω ^ 2 := by
  have hsq : ∀ t, π t ω ^ 2 = π t ω * π t ω := fun t => sq _
  have e := ivEst_eq_add (z := fun t => π t ω) (x := fun t => π t ω)
    (y := fun t => π (t + 1) ω) (e := fun t => επ (t + 1) ω) (b := η) (T := T)
    (fun t _ => by simp only [h.2.2.1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul])
    (by simpa only [hsq] using hx)
  simp only [ivEst, ← hsq] at e
  exact e

/-! ### NI-4: the King form (16.12)/(16.19) -/

/-- Cochrane (2023), (16.1) and (16.12)/(16.19), pp. 366, 371: `(π, i)` is an equilibrium with
the rule `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingEq (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = istar t + φ • (π t - pistar t)

/-- Cochrane (2023), p. 366: the targets respect private-sector equilibrium,
`i*_t = E_t π*_{t+1}`, with `π*` adapted. -/
def TargetsConsistent (istar pistar : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted pistar ∧ ∀ t, istar t = 𝔼.E t (pistar (t + 1))

/-- Cochrane (2023), (16.19), p. 371: the targets themselves are an equilibrium for every `φ`. -/
theorem king_target_eq (φ : ℝ) {istar pistar : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) : KingEq 𝔼 φ istar pistar pistar istar :=
  ⟨hc.1, hc.2, fun t => by simp⟩

/-- Cochrane (2023), (16.14) and (16.19), pp. 367, 371: for `|φ| > 1` and bounded targets, the
only bounded equilibrium is `π = π*`, `i = i*`. -/
theorem king_bounded_eq {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) : π = pistar ∧ i = istar := by
  have hd : Eq164 𝔼 φ 0 (fun t => π t - pistar t) := fun t => by
    rw [map_sub, ← h.2.1 t, ← hc.2 t, h.2.2 t, Pi.zero_apply, add_zero]
    abel
  have hz : Eq164 𝔼 φ 0 (fun _ => 0) := fun t => by simp
  obtain ⟨M, hM⟩ := hb
  obtain ⟨Ms, hMs⟩ := hbs
  have hdb : BoundedProc (fun t => π t - pistar t) :=
    ⟨M + Ms, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hMs t ω))⟩
  have h0 := eq164_unique 𝔼 hφ hd hz hdb ⟨0, fun _ _ => by simp⟩
  have hπ : π = pistar := funext fun t => sub_eq_zero.mp (congrFun h0 t)
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), (16.19), p. 371 ("In equilibrium `π_t = π*_t`, so there is no variation on
the right-hand side with which to measure `φ`"): the selection term vanishes identically. -/
theorem king_selection_zero {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) (t : ℕ) :
    φ • (π t - pistar t) = 0 := by
  rw [(king_bounded_eq 𝔼 hφ hc hbs h hb).1, sub_self, smul_zero]

/-- Cochrane (2023), (16.19), p. 371 (NI-4): for `|φ| > 1` the set of bounded equilibria is
exactly `{(π*, i*)}`. -/
theorem king_eq_set {φ : ℝ} (hφ : 1 < |φ|) {istar pistar : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar) :
    {p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | KingEq 𝔼 φ istar pistar p.1 p.2 ∧ BoundedProc p.1} =
      {(pistar, istar)} := by
  ext ⟨π, i⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h, hb⟩
    exact king_bounded_eq 𝔼 hφ hc hbs h hb
  · rintro ⟨rfl, rfl⟩
    exact ⟨king_target_eq 𝔼 φ hc, hbs⟩

/-- Cochrane (2023), (16.19), p. 371 (NI-4): the set of bounded equilibria is the same for
every pair of values `|φ₁|, |φ₂| > 1`; `φ` is not identified. -/
theorem king_eq_set_indep {φ₁ φ₂ : ℝ} (h₁ : 1 < |φ₁|) (h₂ : 1 < |φ₂|)
    {istar pistar : ℕ → Ω → ℝ} (hc : TargetsConsistent 𝔼 istar pistar)
    (hbs : BoundedProc pistar) :
    {p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | KingEq 𝔼 φ₁ istar pistar p.1 p.2 ∧ BoundedProc p.1} =
      {p | KingEq 𝔼 φ₂ istar pistar p.1 p.2 ∧ BoundedProc p.1} := by
  rw [king_eq_set 𝔼 h₁ hc hbs, king_eq_set 𝔼 h₂ hc hbs]

/-! ### §16.9 Identification patches -/

/-- Cochrane (2023), p. 382: equilibrium with the rule `i_t = θπ*_t + φ(π_t − π*_t) + u_t`. -/
def ThetaEq (θ φ : ℝ) (u pistar π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    ∀ t, i t = θ • pistar t + φ • (π t - pistar t) + u t

/-- Cochrane (2023), p. 382: the interest-rate policy `i*_t = θπ*_t + u_t` respects
`i*_t = E_t π*_{t+1}`. -/
def ThetaConsistent (θ : ℝ) (u pistar : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted pistar ∧ ∀ t, 𝔼.E t (pistar (t + 1)) = θ • pistar t + u t

/-- Cochrane (2023), pp. 367, 382: the θ-rule is the King rule with `i*_t = θπ*_t + u_t`. -/
theorem thetaEq_iff_king (θ φ : ℝ) (u pistar π i : ℕ → Ω → ℝ) :
    ThetaEq 𝔼 θ φ u pistar π i ↔
      KingEq 𝔼 φ (fun t => θ • pistar t + u t) pistar π i := by
  unfold ThetaEq KingEq
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  rw [add_right_comm]

/-- Cochrane (2023), p. 382: for every `φ` the target is an equilibrium of the θ-rule. -/
theorem thetaEq_target (φ : ℝ) {θ : ℝ} {u pistar : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) :
    ThetaEq 𝔼 θ φ u pistar pistar (fun t => θ • pistar t + u t) :=
  (thetaEq_iff_king 𝔼 _ _ _ _ _ _).mpr
    (king_target_eq 𝔼 φ ⟨hc.1, fun t => (hc.2 t).symm⟩)

/-- Cochrane (2023), p. 382: for `|φ| > 1` the bounded equilibrium of the θ-rule is `π = π*`
and the observed data obey `i_t = θ π_t + u_t`; `φ` does not appear. -/
theorem thetaRule_eq_obs {θ φ : ℝ} (hφ : 1 < |φ|) {u pistar π i : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) (hbs : BoundedProc pistar)
    (h : ThetaEq 𝔼 θ φ u pistar π i) (hb : BoundedProc π) :
    π = pistar ∧ ∀ t, i t = θ • π t + u t := by
  obtain ⟨hπ, hi⟩ := king_bounded_eq 𝔼 hφ ⟨hc.1, fun t => (hc.2 t).symm⟩ hbs
    ((thetaEq_iff_king 𝔼 _ _ _ _ _ _).mp h) hb
  exact ⟨hπ, fun t => by rw [hi, hπ]⟩

/-- Cochrane (2023), p. 382 ("the identifying assumptions that let us measure `φ` start with
`θ = φ`"): in the bounded equilibrium of the θ-rule, an instrument `z` orthogonal to `u` in the
sample (`∑ z u = 0`, `∑ z π ≠ 0`) measures `θ`; it measures `φ` if and only if `θ = φ`. -/
theorem iv_identifies_iff {θ φ : ℝ} (hφ : 1 < |φ|) {u pistar π i : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) (hbs : BoundedProc pistar)
    (h : ThetaEq 𝔼 θ φ u pistar π i) (hb : BoundedProc π) (ω : Ω) (z : ℕ → ℝ) {T : ℕ}
    (hzu : ∑ t ∈ Finset.range T, z t * u t ω = 0)
    (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T = θ ∧
      (ivEst z (fun t => π t ω) (fun t => i t ω) T = φ ↔ θ = φ) := by
  have hi := (thetaRule_eq_obs 𝔼 hφ hc hbs h hb).2
  have e := ivEst_eq_add (z := z) (x := fun t => π t ω) (y := fun t => i t ω)
    (e := fun t => u t ω) (b := θ) (fun t _ => by
    simp only [hi t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]) hzx
  rw [hzu, zero_div, add_zero] at e
  exact ⟨e, by rw [e]⟩

/-- Cochrane (2023), p. 382 ("φ is also identified if there is no disturbance … and if there
are shocks to other equations"): in the simplest model, with `θ = φ`, `u = 0` and `|φ| > 1`, the
only bounded target is `π* = 0`; the equilibrium data are identically zero, so identification
needs shocks from other equations. -/
theorem theta_eq_phi_no_shock_zero {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 φ 0 pistar) (hbs : BoundedProc pistar) : pistar = 0 :=
  eq164_unique 𝔼 hφ (u := 0) (fun t => hc.2 t) (fun t => by simp) hbs
    ⟨0, fun _ _ => by simp⟩

/-- Cochrane (2023), p. 382: an equilibrium of the model with a real-rate shock in the Fisher
equation, `i_t = r_t + E_t π_{t+1}`, and the rule `i_t = φ π_t + u_t`. -/
def RREq (φ : ℝ) (r u π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = r t + 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • π t + u t

/-- Cochrane (2023), p. 382: in any equilibrium of the real-rate model, the IV estimate with
instrument `z` is `φ + ∑ z u / ∑ z π`. -/
theorem rr_iv_eq_phi_add {φ : ℝ} {r u π i : ℕ → Ω → ℝ} (h : RREq 𝔼 φ r u π i) (ω : Ω)
    (z : ℕ → ℝ) {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T =
      φ + (∑ t ∈ Finset.range T, z t * u t ω) / ∑ t ∈ Finset.range T, z t * π t ω :=
  ivEst_eq_add (fun t _ => by simp only [h.2.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul])
    hzx

/-- Cochrane (2023), p. 382 ("We might try to assume that monetary-policy disturbances are
orthogonal to disturbances to the other equations"): the IV estimate equals `φ` iff the
instrument is orthogonal to `u` in the sample; if the bank responds to the other shocks
(`∑ z u ≠ 0`) it does not measure `φ`. -/
theorem rr_iv_eq_phi_iff {φ : ℝ} {r u π i : ℕ → Ω → ℝ} (h : RREq 𝔼 φ r u π i) (ω : Ω)
    (z : ℕ → ℝ) {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T = φ ↔
      ∑ t ∈ Finset.range T, z t * u t ω = 0 := by
  rw [rr_iv_eq_phi_add 𝔼 h ω z hzx]
  constructor
  · intro e
    have : (∑ t ∈ Finset.range T, z t * u t ω) / ∑ t ∈ Finset.range T, z t * π t ω = 0 := by
      linarith
    rcases div_eq_zero_iff.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hzx
  · intro e
    rw [e, zero_div, add_zero]

/-- Cochrane (2023), p. 382: in the real-rate model with `|φ| > 1`, the equilibrium is the
unique bounded solution of `E_t π_{t+1} = φ π_t + u_t − r_t`. -/
theorem rr_unique {φ : ℝ} (hφ : 1 < |φ|) {r u π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ}
    (h₁ : RREq 𝔼 φ r u π₁ i₁) (h₂ : RREq 𝔼 φ r u π₂ i₂) (hb₁ : BoundedProc π₁)
    (hb₂ : BoundedProc π₂) : π₁ = π₂ := by
  have key : ∀ π i, RREq 𝔼 φ r u π i → Eq164 𝔼 φ (fun t => u t - r t) π := by
    intro π i h t
    have e1 := h.2.1 t
    have e2 := h.2.2 t
    rw [e2] at e1
    rw [show 𝔼.E t (π (t + 1)) = φ • π t + u t - r t by rw [e1]; abel]
    abel_nf
  exact eq164_unique 𝔼 hφ (key _ _ h₁) (key _ _ h₂) hb₁ hb₂

/-- Cochrane (2023), p. 382: a non-vacuous identified example under perfect foresight. With
`φ = 2`, a constant real-rate shock `r = 1` and no disturbance, `π = 1`, `i = 2` is the unique
bounded equilibrium, and the IV estimate with instrument `r` on any nonempty sample is `φ = 2`. -/
theorem rr_example (T : ℕ) (hT : 0 < T) :
    RREq perfectForesight 2 (fun _ _ => 1) 0 (fun _ _ => 1) (fun _ _ => 2) ∧
      (∀ π i, RREq perfectForesight 2 (fun _ _ => 1) 0 π i → BoundedProc π →
        π = fun _ _ => 1) ∧
      ivEst (fun _ => 1) (fun t => (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) t ())
        (fun t => (fun (_ : ℕ) (_ : Unit) => (2 : ℝ)) t ()) T = 2 := by
  have h : RREq perfectForesight 2 (fun _ _ => 1) 0 (fun _ _ => 1) (fun _ _ => 2) := by
    refine ⟨fun t => rfl, fun t => ?_, fun t => ?_⟩
    · funext ω
      change (2 : ℝ) = 1 + 1
      norm_num
    · funext ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      norm_num
  refine ⟨h, fun π i h' hb => rr_unique perfectForesight (by norm_num) h' h hb
    ⟨1, fun _ _ => by simp⟩, ?_⟩
  have hs : ∑ t ∈ Finset.range T, (1 : ℝ) * 1 ≠ 0 := by
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact_mod_cast hT.ne'
  exact ivEst_eq (η := 2) (fun t _ => by norm_num) hs

/-! ### §16.10.7: the on-equilibrium parameter θ of the fiscal-theory model is identified -/

/-- Cochrane (2023), (2.20)–(2.22), p. 40: an equilibrium of the simple fiscal-theory model,
`i_t = E_t π_{t+1}`, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`, `i_t = θ π_t + u_t`. -/
def FTPLEq (θ : ℝ) (u εs π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    (∀ t, innov 𝔼 t (π (t + 1)) = -εs (t + 1)) ∧
    ∀ t, i t = θ • π t + u t

/-- Cochrane (2023), §16.10.7, p. 394: the class of fiscal-theory specifications
`(θ, ε_Σs, π)` with no monetary disturbance whose inflation is not identically zero. -/
def ftplClass : Set (ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {m | FTPLEq 𝔼 m.1 0 m.2.1 m.2.2 (fisherRate 𝔼 m.2.2) ∧ ∃ t ω, m.2.2 t ω ≠ 0}

/-- Cochrane (2023), §16.10.7, p. 394 ("In the passive-money active-fiscal equilibrium, `θ` …
is identified"): in an equilibrium with `u = 0`, `θ = i_t/π_t` at any date and state with
`π_t ≠ 0`. -/
theorem ftpl_theta_eq {θ : ℝ} {εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ 0 εs π i) {t : ℕ} {ω : Ω}
    (hπ : π t ω ≠ 0) : θ = i t ω / π t ω := by
  have e := congrFun (h.2.2.2 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, add_zero] at e
  rw [e, mul_div_assoc, div_self hπ, mul_one]

/-- Cochrane (2023), §16.10.7, p. 394: `θ` is identified on the fiscal-theory class. -/
theorem ftpl_theta_identified : IdentifiedOn (ftplClass 𝔼) (nkObs 𝔼) Prod.fst := by
  rintro ⟨θ₁, ε₁, π₁⟩ ⟨h₁, t, ω, hπ⟩ ⟨θ₂, ε₂, π₂⟩ ⟨h₂, -⟩ he
  simp only [nkObs, Prod.mk.injEq] at he
  obtain ⟨rfl, -⟩ := he
  exact (ftpl_theta_eq 𝔼 h₁ hπ).trans (ftpl_theta_eq 𝔼 h₂ hπ).symm

/-- Cochrane (2023), §16.10.7, p. 394 ("identified, and hence measurable by econometricians and
learnable to agents"): a learning rule recovers `θ` from the observables. -/
theorem ftpl_theta_learnable :
    ∃ L : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) → ℝ, ∀ m ∈ ftplClass 𝔼, L (nkObs 𝔼 m) = m.1 :=
  (identified_iff_learnable _ _ _).mp (ftpl_theta_identified 𝔼)

end Cochrane.NewKeynesianSelection.Identification

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Observational equivalence of new-Keynesian and fiscal-theory equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.6 "Observational
equivalence" (pp. 372–374), with the simple fiscal-theory model (2.20)–(2.25) of §2.6
(p. 40) and the `*`-notation fiscal rule of §5.4–5.5 ((5.29)–(5.38), pp. 137–139).

All statements hold for an arbitrary `ExpectationSystem` and are pathwise equalities of
processes.

## Main results

* (2.25): `ftpl_eq_225`, `ftpl_unique`, `ftpl_exists` — given `π_0` and the exogenous
  processes, the fiscal-theory equilibrium exists and is unique (for every `θ`); the path is
  the canonical `FTPLSimple.ruleSol`, and the implied fiscal shock `ε_Σs = −ΔEπ` is the
  canonical `FTPLSimple.passiveShock`.
* NI-5 (p. 372): `nk_is_ftpl` — the selected new-Keynesian AR(1) equilibrium `(φ, η, ε_i)` is
  the fiscal-theory equilibrium with `θ = η`, `u = 0`, `ε_Σs = ε_i/(φ − η)`;
  `nk_eq_ftpl_path` (equality with the fiscal-theory path), `passive_surplus_eq_active`, and
  equal impulse responses `obs_irf`, `nk_irf`, `ftpl_irf`, `nk_irf_eq_ftpl_irf`.
* "Any new-Keynesian model can be written as a fiscal theory model" (p. 373):
  `nk_to_ftpl` (every equilibrium, with any `θ`, in particular a time-varying peg),
  `ftpl_to_nk`, and the two-way set equalities `nkObsSet_eq_ftplObsSet`,
  `selectedObsSet_eq_boundedFtplObsSet`.
* The unified model (16.20)–(16.22): `MonetaryBlock`, `FiscalBlock`, `TVC`, `UnifiedEq`;
  deviation dynamics `e_dyn` (`ρ e_{t+1} = e_t − (ΔEπ − ΔEπ*)`, free of `γ`), `vs_dyn`,
  `v_dyn`; `tendsto_tvc` (`ρ^T E_t v_{t+T} → (α − γ)/α · (v_t − v*_t)`), `tvc_iff`.
* Regimes (p. 373) and survey error E6: `passive_of_eq` (`γ = α`: the TVC holds for every
  inflation path), `not_passive_of_ne`, `passive_iff` (fiscal policy is passive iff `γ = α`;
  the printed "`γ > 0`" and the conjectured "`0 < γ < 2`" are wrong), the concrete coin-flip
  counterexample `e6_counterexample`; `af_regime` (active fiscal: `ΔEπ = ΔEπ*`,
  `π_t − π*_t = φᵗ(π_0 − π*_0)`), `af_regime_phi_zero`, `am_regime`.
* NI-6 (16.23)–(16.24): `ObsFiscal`, `unifiedEq_obs` (every equilibrium of every regime
  satisfies (16.23)–(16.24)), `obs_unifiedEq` (every solution of (16.23)–(16.24) is an
  equilibrium of every regime), `eqObs_eq`, `eqObs_nonempty`,
  `regimes_observationally_equivalent`, `gamma_phi_not_identified`, `gamma_phi_not_learnable`
  (§16.10.7: "the argument admittedly cuts both ways").
* Survey error E6 resolved: with (16.21) as printed (the actual surplus `s_{t+1}` in both debt
  equations) passivity holds iff `γ = α`, not for all `γ > 0` and not for all `0 < γ < 2`
  (`0 < γ < 2` is the passivity range of the surplus rule `s_{t+1} = γ v_t + u_{s,t+1}` of
  (5.36)–(5.37), which is (16.20) with `γ = α`).
-/

namespace Cochrane.NewKeynesianSelection.ObservationalEquivalence

open Filter Topology Cochrane.NewKeynesianSelection.Identification
open Innovation (innov IsShock innov_eq_sub_E E_innov_zero_of_le innov_known_next isShock_smul
  isShock_neg coinShock_adapted)
open SimplestModel (ar1Pi ar1Pi_adapted)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The simple fiscal-theory model (2.20)–(2.25) -/

/-- Cochrane (2023), (2.25), p. 40: in a fiscal-theory equilibrium
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
theorem ftpl_eq_225 {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ u εs π i) (t : ℕ) :
    π (t + 1) = θ • π t + u t - εs (t + 1) := by
  have e := h.2.2.1 t
  rw [innov_eq_sub_E 𝔼 (h.1 (t + 1)), ← h.2.1 t, h.2.2.2 t] at e
  rw [show π (t + 1) = π (t + 1) - (θ • π t + u t) + (θ • π t + u t) by abel, e]
  abel

/-- Cochrane (2023), (2.20)–(2.25), p. 40: given the date-0 inflation and the exogenous
processes, the fiscal-theory equilibrium is unique (for every `θ`; no boundedness needed). -/
theorem ftpl_unique {θ : ℝ} {u εs π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ} (h₁ : FTPLEq 𝔼 θ u εs π₁ i₁)
    (h₂ : FTPLEq 𝔼 θ u εs π₂ i₂) (h0 : π₁ 0 = π₂ 0) : π₁ = π₂ ∧ i₁ = i₂ := by
  have hπ : π₁ = π₂ := by
    funext t
    induction t with
    | zero => exact h0
    | succ t ih => rw [ftpl_eq_225 𝔼 h₁ t, ftpl_eq_225 𝔼 h₂ t, ih]
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h₁.2.2.2 t, h₂.2.2.2 t, hπ]

/-- Cochrane (2023), (2.20)–(2.25), p. 40: for adapted `u`, a fiscal shock `ε_Σs` and a
date-0 inflation known at date 0, the path (2.25) (`FTPLSimple.ruleSol`) is a fiscal-theory
equilibrium. -/
theorem ftpl_exists (θ : ℝ) {u εs : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 εs) (h0 : 𝔼.E 0 π0 = π0) :
    FTPLEq 𝔼 θ u εs (FTPLSimple.ruleSol θ u εs π0)
      (fisherRate 𝔼 (FTPLSimple.ruleSol θ u εs π0)) := by
  have ha := FTPLSimple.ruleSol_adapted 𝔼 (θ := θ) h0 hu hε
  have h224 := (FTPLSimple.eq224_iff 𝔼 ha hu hε).mpr fun t => rfl
  exact ⟨ha, fun _ => rfl, fun t => (h224 t).2, fun t => (h224 t).1⟩

/-! ### NI-5: the new-Keynesian equilibrium is a fiscal-theory equilibrium (p. 372) -/

/-- Cochrane (2023), p. 372: the selected AR(1) new-Keynesian equilibrium (16.10) with
`(φ, η, ε_i)` is a fiscal-theory equilibrium (2.20)–(2.22) with `θ = η`, no monetary
disturbance and fiscal shock `ε_Σs = ε_i/(φ − η)`. -/
theorem nk_is_ftpl (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    FTPLEq 𝔼 η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) := by
  refine ⟨fun s => by simp only [ar1Pi, map_smul, h.1 s], fun _ => rfl, fun t => ?_,
    fun t => ?_⟩
  · rw [eq_16_16_innov 𝔼 φ h t, neg_smul]
  · rw [(eq_16_15 𝔼 φ h t).1, Pi.zero_apply, add_zero]

/-- Cochrane (2023), p. 372 ("the fiscal theory model produces exactly the same time series"):
the fiscal-theory path with `θ = η`, `u = 0`, `ε_Σs = ε_i/(φ − η)` and `π_0 = −u_0/(φ − η)` IS
the new-Keynesian selected path. -/
theorem nk_eq_ftpl_path (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    FTPLSimple.ruleSol η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u 0) = ar1Pi φ η u := by
  have hε : IsShock 𝔼 (fun t => (φ - η)⁻¹ • ε t) := isShock_smul 𝔼 h.2.1 _
  have h0 : 𝔼.E 0 (ar1Pi φ η u 0) = ar1Pi φ η u 0 := ar1Pi_adapted 𝔼 φ η h.1 0
  exact (ftpl_unique 𝔼 (ftpl_exists 𝔼 η (fun t => by simp) hε h0) (nk_is_ftpl 𝔼 φ h)
    rfl).1

/-- Cochrane (2023), p. 372 ("fiscal policy passively raises surpluses by
`ε_Σs,t+1 = −ΔE_{t+1}π_{t+1} = ε_{i,t+1}/(φ − η)`. This value is exactly the same as the fiscal
theory model's active fiscal shock"). -/
theorem passive_surplus_eq_active (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (t : ℕ) : -innov 𝔼 t (ar1Pi φ η u (t + 1)) = (fun s => (φ - η)⁻¹ • ε s) (t + 1) :=
  (eq_16_18 𝔼 φ h t).2

/-- Cochrane (2023), (16.16), p. 371: impulse responses of the observable system,
`E_{t+1} π_{t+1+k} − E_t π_{t+1+k} = ηᵏ ε_{π,t+1}`. -/
theorem obs_irf {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ) (t k : ℕ) :
    𝔼.E (t + 1) (π (t + 1 + k)) - 𝔼.E t (π (t + 1 + k)) = η ^ k • επ (t + 1) := by
  have har : 𝔼.IsAR1 η π := ⟨h.1, fun s => by
    rw [h.2.2.1 s, map_add, map_smul, h.1 s, h.2.1.2 s, add_zero]⟩
  rw [𝔼.ar1_iterate har, show t + 1 + k = t + (k + 1) by omega, 𝔼.ar1_iterate har,
    h.2.2.1 t, smul_add, pow_succ, ← smul_smul]
  abel

/-- Cochrane (2023), (16.10), p. 365 and Figure 16.1: the new-Keynesian response to a
monetary-policy shock, `ΔE_{t+1} π_{t+1+k} = −ηᵏ ε_{i,t+1}/(φ − η)`. -/
theorem nk_irf (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t k : ℕ) :
    𝔼.E (t + 1) (ar1Pi φ η u (t + 1 + k)) - 𝔼.E t (ar1Pi φ η u (t + 1 + k)) =
      (-(η ^ k * (φ - η)⁻¹)) • ε (t + 1) := by
  rw [obs_irf 𝔼 (ar1_obs 𝔼 φ h) t k, smul_smul]
  congr 1
  ring

/-- Cochrane (2023), (2.25), p. 40 and Figure 2.2: the fiscal-theory response to a fiscal shock
with `u = 0`, `ΔE_{t+1} π_{t+1+k} = −θᵏ ε_{Σs,t+1}`. -/
theorem ftpl_irf {θ : ℝ} {εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ 0 εs π i) (hε : IsShock 𝔼 εs)
    (t k : ℕ) :
    𝔼.E (t + 1) (π (t + 1 + k)) - 𝔼.E t (π (t + 1 + k)) = (-θ ^ k) • εs (t + 1) := by
  have hobs : ObsAR1 𝔼 θ π i (fun s => -εs s) :=
    ⟨h.1, isShock_neg 𝔼 hε,
      fun s => by rw [ftpl_eq_225 𝔼 h s, Pi.zero_apply, add_zero, sub_eq_add_neg],
      fun s => by rw [h.2.2.2 s, Pi.zero_apply, add_zero]⟩
  rw [obs_irf 𝔼 hobs t k, smul_neg, neg_smul]

/-- Cochrane (2023), p. 372 ("The new-Keynesian inflation response to a monetary policy shock
of Figure 16.1 is exactly the same as the fiscal-theory inflation response to a fiscal
shock"): with `θ = η` and `ε_Σs = ε_i/(φ − η)` the two impulse responses coincide. -/
theorem nk_irf_eq_ftpl_irf (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t k : ℕ) :
    𝔼.E (t + 1) (ar1Pi φ η u (t + 1 + k)) - 𝔼.E t (ar1Pi φ η u (t + 1 + k)) =
      (-η ^ k) • (fun s => (φ - η)⁻¹ • ε s) (t + 1) := by
  rw [nk_irf 𝔼 φ h, smul_smul]
  congr 1
  ring

/-! ### Any new-Keynesian equilibrium is a fiscal-theory equilibrium, and conversely -/

/-- Cochrane (2023), p. 373 ("Any new-Keynesian model can be written as a fiscal theory
model"): every equilibrium of (16.1)–(16.2), for any `φ` and `u` (selected or not), is, for
EVERY `θ`, a fiscal-theory equilibrium with monetary disturbance `u^F = i − θπ` and active
fiscal shock `ε_Σs = −ΔEπ`; it is the unique such equilibrium with its date-0 inflation. -/
theorem nk_to_ftpl {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (θ : ℝ) :
    FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π i ∧
      ∀ π' i', FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π' i' →
        π' 0 = π 0 → π' = π ∧ i' = i := by
  have hF : FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π i :=
    ⟨h.1, h.2.1, fun t => by simp only [FTPLSimple.passiveShock, neg_neg],
      fun t => (add_sub_cancel (θ • π t) (i t)).symm⟩
  exact ⟨hF, fun π' i' h' h0 => ftpl_unique 𝔼 h' hF h0⟩

/-- Cochrane (2023), pp. 367, 373: the special case of a time-varying interest-rate peg
`i_t = i*_t` (`θ = 0`, `u^F = i`). -/
theorem nk_to_peg {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) :
    FTPLEq 𝔼 0 i (FTPLSimple.passiveShock 𝔼 π) π i := by
  have := (nk_to_ftpl 𝔼 h 0).1
  simpa only [zero_smul, sub_zero] using this

/-- Cochrane (2023), p. 373 ("Observational equivalence goes both ways"): every bounded
fiscal-theory equilibrium is, for every `φ` with `|φ| > 1`, the new-Keynesian selected
equilibrium with `u = i − φπ`. -/
theorem ftpl_to_nk {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ u εs π i)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) :
    NKEq 𝔼 φ (fun t => i t - φ • π t) π i ∧ Selected 𝔼 φ (fun t => i t - φ • π t) π :=
  every_eq_selected 𝔼 ⟨h.1, h.2.1, h.2.2.2⟩ hb hφ

/-- Cochrane (2023), p. 373: the observables of new-Keynesian equilibria. -/
def nkObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) := {o | ∃ φ u, NKEq 𝔼 φ u o.1 o.2}

/-- Cochrane (2023), p. 373: the observables of fiscal-theory equilibria. -/
def ftplObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) := {o | ∃ θ u εs, FTPLEq 𝔼 θ u εs o.1 o.2}

/-- Cochrane (2023), p. 373 ("You can always fit the data at least as well with a fiscal theory
model as you can with an active-money model"): the two sets of observable equilibrium
processes are equal. -/
theorem nkObsSet_eq_ftplObsSet : nkObsSet 𝔼 = ftplObsSet 𝔼 := by
  ext ⟨π, i⟩
  constructor
  · rintro ⟨φ, u, h⟩
    exact ⟨φ, _, _, (nk_to_ftpl 𝔼 h φ).1⟩
  · rintro ⟨θ, u, εs, h⟩
    exact ⟨θ, u, h.1, h.2.1, h.2.2.2⟩

/-- Cochrane (2023), pp. 372–373: the observables of new-Keynesian SELECTED equilibria
(`|φ| > 1`, unique bounded solution). -/
def selectedObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | ∃ φ u, 1 < |φ| ∧ Selected 𝔼 φ u o.1 ∧ o.2 = fisherRate 𝔼 o.1}

/-- Cochrane (2023), pp. 372–373: the observables of bounded fiscal-theory equilibria. -/
def boundedFtplObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | (∃ θ u εs, FTPLEq 𝔼 θ u εs o.1 o.2) ∧ BoundedProc o.1}

/-- Cochrane (2023), pp. 372–373 (observational equivalence, both directions): the
new-Keynesian selected equilibria and the bounded fiscal-theory equilibria produce exactly
the same set of observable processes. -/
theorem selectedObsSet_eq_boundedFtplObsSet : selectedObsSet 𝔼 = boundedFtplObsSet 𝔼 := by
  ext ⟨π, i⟩
  constructor
  · rintro ⟨φ, u, -, hs, hi⟩
    simp only at hs hi
    subst hi
    have hN : NKEq 𝔼 φ u π (fisherRate 𝔼 π) :=
      (nkEq_iff 𝔼 _ _ _ _).mpr ⟨hs.2.1, hs.2.2.1, rfl⟩
    exact ⟨⟨φ, _, _, (nk_to_ftpl 𝔼 hN φ).1⟩, hs.1⟩
  · rintro ⟨⟨θ, u, εs, h⟩, hb⟩
    have h2 : 1 < |(2 : ℝ)| := by norm_num
    obtain ⟨hN, hs⟩ := ftpl_to_nk 𝔼 h hb h2
    exact ⟨2, _, h2, hs, ((nkEq_iff 𝔼 _ _ _ _).mp hN).2.2⟩

/-! ### The unified model (16.20)–(16.22) -/

/-- Cochrane (2023), (16.20), p. 373, monetary block: `i_t = E_t π_{t+1}`,
`i_t = i*_t + φ(π_t − π*_t)`, with consistent targets `i*_t = E_t π*_{t+1}`. -/
def MonetaryBlock (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) : Prop :=
  KingEq 𝔼 φ istar pistar π i ∧ TargetsConsistent 𝔼 istar pistar

/-- Cochrane (2023), (16.20)–(16.22), p. 373, fiscal block: the surplus rule
`s_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`, the target-debt evolution (16.21)
`ρ v*_{t+1} = v*_t − ΔE_{t+1} π*_{t+1} − s_{t+1}`, the debt evolution (16.22)
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s_{t+1}`, with `v`, `v*` adapted and the initial
condition `v_0 = v*_0` (the target debt starts at the actual debt). -/
def FiscalBlock (ρ α γ : ℝ) (us pistar π s v vs : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted v ∧ 𝔼.Adapted vs ∧ v 0 = vs 0 ∧
    (∀ t, s (t + 1) = α • vs t + γ • (v t - vs t) + us (t + 1)) ∧
    (∀ t, ρ • vs (t + 1) = vs t - innov 𝔼 t (pistar (t + 1)) - s (t + 1)) ∧
    ∀ t, ρ • v (t + 1) = v t - innov 𝔼 t (π (t + 1)) - s (t + 1)

/-- Cochrane (2023), p. 137 and p. 369: the transversality condition on the value of debt,
`ρ^T E_t v_{t+T} → 0` for every date and state. -/
def TVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), (16.20)–(16.22), p. 373: an equilibrium of the unified model. -/
def UnifiedEq (ρ α γ φ : ℝ) (us istar pistar π i s v vs : ℕ → Ω → ℝ) : Prop :=
  MonetaryBlock 𝔼 φ istar pistar π i ∧ FiscalBlock 𝔼 ρ α γ us pistar π s v vs ∧ TVC 𝔼 ρ v

/-- Cochrane (2023), (5.35), p. 137, for (16.21)–(16.22): the debt gap `e = v − v*` obeys
`ρ e_{t+1} = e_t − (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`; the surplus, hence `γ`, cancels. -/
theorem e_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • (v (t + 1) - vs (t + 1)) =
      (v t - vs t) - (innov 𝔼 t (π (t + 1)) - innov 𝔼 t (pistar (t + 1))) := by
  rw [smul_sub, h.2.2.2.2.2 t, h.2.2.2.2.1 t]
  abel

/-- Cochrane (2023), p. 138: substituting the surplus rule into (16.21),
`ρ v*_{t+1} = (1 − α) v*_t − γ(v_t − v*_t) − ΔE_{t+1} π*_{t+1} − u_{s,t+1}`. -/
theorem vs_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • vs (t + 1) =
      (1 - α) • vs t - γ • (v t - vs t) - innov 𝔼 t (pistar (t + 1)) - us (t + 1) := by
  rw [h.2.2.2.2.1 t, h.2.2.2.1 t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), p. 138: substituting the surplus rule into (16.22),
`ρ v_{t+1} = (1 − γ) v_t − (α − γ) v*_t − ΔE_{t+1} π_{t+1} − u_{s,t+1}`; with `γ = α` this is
the passive rule (5.37) `ρ v_{t+1} = (1 − α) v_t − ΔE π_{t+1} − u_{s,t+1}`. -/
theorem v_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • v (t + 1) = (1 - γ) • v t - (α - γ) • vs t - innov 𝔼 t (π (t + 1)) - us (t + 1) := by
  rw [h.2.2.2.2.2 t, h.2.2.2.1 t, sub_smul, sub_smul, one_smul, smul_sub]
  abel

/-- Cochrane (2023), p. 137: the expected debt gap grows at rate `1/ρ`,
`ρ^k E_t e_{t+k} = e_t`. -/
theorem E_gap {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t k : ℕ) (ω : Ω) :
    ρ ^ k * 𝔼.E t (v (t + k) - vs (t + k)) ω = v t ω - vs t ω := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, add_zero, map_sub, h.1 t, h.2.1 t, Pi.sub_apply]
  | succ k ih =>
    have e := congrArg (fun x => 𝔼.E t x ω) (e_dyn 𝔼 h (t + k))
    simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      E_innov_zero_of_le 𝔼 (Nat.le_add_right t k), Pi.zero_apply, sub_zero] at e
    rw [← add_assoc, pow_succ, mul_assoc, map_sub, Pi.sub_apply, e, ← ih, map_sub,
      Pi.sub_apply]

/-- Cochrane (2023), p. 138 (a linear recursion with converging forcing; general lemma not in
the core): if `W_{k+1} = q W_k + c_k` with `|q| < 1` and `c_k → L`, then
`W_k → L/(1 − q)`. -/
theorem rec_limit {q : ℝ} (hq : |q| < 1) {W c : ℕ → ℝ} {L : ℝ}
    (hW : ∀ k, W (k + 1) = q * W k + c k) (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto W atTop (𝓝 (L / (1 - q))) := by
  have hq1 : 0 < 1 - |q| := by linarith
  have hq0 : 1 - q ≠ 0 := by
    intro h0
    have : q = 1 := by linarith
    rw [this, abs_one] at hq
    exact lt_irrefl _ hq
  set Z : ℕ → ℝ := fun k => W k - L / (1 - q) with hZ
  have hZs : ∀ k, Z (k + 1) = q * Z k + (c k - L) := by
    intro k
    simp only [hZ, hW k]
    field_simp
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc' := (Metric.tendsto_atTop.mp hc) (ε * (1 - |q|) / 2) (by positivity)
  obtain ⟨N1, hN1⟩ := hc'
  have hbound : ∀ j, |Z (N1 + j)| ≤ |q| ^ j * |Z N1| + ε / 2 := by
    intro j
    induction j with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ j ih =>
      rw [← add_assoc, hZs, ← Real.dist_eq]
      have hd := hN1 (N1 + j) (Nat.le_add_right _ _)
      calc |q * Z (N1 + j) + (c (N1 + j) - L)|
          ≤ |q * Z (N1 + j)| + |c (N1 + j) - L| := abs_add_le _ _
        _ ≤ |q| * (|q| ^ j * |Z N1| + ε / 2) + ε * (1 - |q|) / 2 := by
            rw [abs_mul]
            rw [Real.dist_eq] at hd
            gcongr
        _ = |q| ^ (j + 1) * |Z N1| + ε / 2 := by ring
  have hgeo : Tendsto (fun j : ℕ => |q| ^ j * |Z N1|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq).mul_const |Z N1|
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hgeo) (ε / 2) (by positivity)
  refine ⟨N1 + J, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hbJ := hbound (J + j)
  have h2 := hJ (J + j) (Nat.le_add_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  rw [dist_zero_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  change |Z (N1 + J + j)| < ε
  rw [add_assoc]
  linarith

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and pp. 137–138: for `0 < ρ < 1`, `0 < α < 2`
and a bounded surplus disturbance, `ρ^T E_t v_{t+T} → ((α − γ)/α) (v_t − v*_t)`. -/
theorem tendsto_tvc {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us pistar π s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 ((α - γ) / α * (v t ω - vs t ω))) := by
  set e := v t ω - vs t ω with he
  set W : ℕ → ℝ := fun k => ρ ^ k * 𝔼.E t (vs (t + k)) ω with hWdef
  set g : ℕ → ℝ := fun k => 𝔼.E t (us (t + k + 1)) ω with hg
  have hW : ∀ k, W (k + 1) = (1 - α) * W k + (-γ * e - ρ ^ k * g k) := by
    intro k
    have e1 := congrArg (fun x => 𝔼.E t x ω) (vs_dyn 𝔼 h (t + k))
    simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      E_innov_zero_of_le 𝔼 (Nat.le_add_right t k), sub_zero] at e1
    have hgap := E_gap 𝔼 h t k ω
    rw [map_sub, Pi.sub_apply] at hgap
    simp only [hWdef, hg, ← add_assoc, pow_succ]
    rw [mul_assoc, e1]
    linear_combination (-γ) * hgap + γ * he
  have hgb : ∀ k, |g k| ≤ M := fun k => 𝔼.abs_E_le (hus _) t ω
  have hc : Tendsto (fun k => -γ * e - ρ ^ k * g k) atTop (𝓝 (-γ * e)) := by
    have h0 : Tendsto (fun k => ρ ^ k * g k) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const M)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hρ0 k)]
      exact mul_le_mul_of_nonneg_left (hgb k) (pow_pos hρ0 k).le
    simpa using tendsto_const_nhds.sub h0
  have hq : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hWlim := rec_limit hq hW hc
  have hsplit : ∀ T : ℕ, ρ ^ T * 𝔼.E t (v (t + T)) ω = W T + e := by
    intro T
    have hgap := E_gap 𝔼 h t T ω
    rw [map_sub, Pi.sub_apply] at hgap
    simp only [hWdef]
    linear_combination hgap - he
  simp only [hsplit]
  have hα : α ≠ 0 := hα0.ne'
  rw [show (1 : ℝ) - (1 - α) = α by ring] at hWlim
  convert hWlim.add_const e using 2
  field_simp
  ring

/-- Cochrane (2023), (16.21)–(16.22), p. 373: given the fiscal block, the transversality
condition holds iff `(α − γ)(v_t − v*_t) = 0` at every date and state. -/
theorem tvc_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us pistar π s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) :
    TVC 𝔼 ρ v ↔ ∀ t ω, (α - γ) * (v t ω - vs t ω) = 0 := by
  constructor
  · intro htvc t ω
    have e := tendsto_nhds_unique (tendsto_tvc 𝔼 hρ0 hρ1 hα0 hα2 hus h t ω) (htvc t ω)
    rw [div_mul_eq_mul_div, div_eq_zero_iff] at e
    rcases e with e | e
    · exact e
    · exact absurd e hα0.ne'
  · intro h0 t ω
    have := tendsto_tvc 𝔼 hρ0 hρ1 hα0 hα2 hus h t ω
    rwa [div_mul_eq_mul_div, h0 t ω, zero_div] at this

/-- Cochrane (2023), p. 137: with `v_0 = v*_0`, the debt gap vanishes at every date iff
unexpected inflation equals the target's unexpected inflation at every date. -/
theorem gap_zero_iff {ρ α γ : ℝ} (hρ : ρ ≠ 0) {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) :
    (∀ t, v t = vs t) ↔ ∀ t, innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1)) := by
  constructor
  · intro hv t
    have e := e_dyn 𝔼 h t
    rw [hv t, hv (t + 1), sub_self, sub_self, smul_zero, zero_sub, eq_comm, neg_eq_zero,
      sub_eq_zero] at e
    exact e
  · intro hd t
    induction t with
    | zero => exact h.2.2.1
    | succ t ih =>
      have e := e_dyn 𝔼 h t
      rw [ih, hd t, sub_self, sub_self, sub_zero] at e
      have := (smul_eq_zero.mp e).resolve_left hρ
      exact sub_eq_zero.mp this

/-! ### Regimes, passivity, and survey error E6 -/

/-- Cochrane (2023), p. 138 ("for `γ > 1 − ρ` … any unexpected inflation is an equilibrium"):
fiscal policy is passive if the transversality condition holds along every inflation path,
i.e. for every solution of the fiscal block. -/
def FiscalPassive (ρ α γ : ℝ) (us : ℕ → Ω → ℝ) : Prop :=
  ∀ pistar π s v vs : ℕ → Ω → ℝ, FiscalBlock 𝔼 ρ α γ us pistar π s v vs → TVC 𝔼 ρ v

/-- Cochrane (2023), p. 373 ("most simply `γ = α > 0`"): with `γ = α` fiscal policy is passive. -/
theorem passive_of_eq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) : FiscalPassive 𝔼 ρ α α us :=
  fun _ _ _ _ _ h => (tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus h).mpr fun t ω => by ring

/-- Cochrane (2023), (16.20)–(16.22), p. 373: the fiscal block has a solution for any inflation
and target paths: the pair `(v, v*)` defined by the recursions. -/
noncomputable def fiscalPath (ρ α γ : ℝ) (us pistar π : ℕ → Ω → ℝ) (v0 : Ω → ℝ) :
    ℕ → (Ω → ℝ) × (Ω → ℝ)
  | 0 => (v0, v0)
  | t + 1 =>
    (ρ⁻¹ • ((fiscalPath ρ α γ us pistar π v0 t).1 - innov 𝔼 t (π (t + 1)) -
        (α • (fiscalPath ρ α γ us pistar π v0 t).2 +
          γ • ((fiscalPath ρ α γ us pistar π v0 t).1 - (fiscalPath ρ α γ us pistar π v0 t).2) +
          us (t + 1))),
      ρ⁻¹ • ((fiscalPath ρ α γ us pistar π v0 t).2 - innov 𝔼 t (pistar (t + 1)) -
        (α • (fiscalPath ρ α γ us pistar π v0 t).2 +
          γ • ((fiscalPath ρ α γ us pistar π v0 t).1 - (fiscalPath ρ α γ us pistar π v0 t).2) +
          us (t + 1))))

/-- Cochrane (2023), (16.20), p. 373: the surplus along `fiscalPath` (zero at date 0, which
the fiscal block does not constrain). -/
noncomputable def fiscalSurplus (ρ α γ : ℝ) (us pistar π : ℕ → Ω → ℝ) (v0 : Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => α • (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 +
      γ • ((fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 - (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2) +
      us (t + 1)

/-- Cochrane (2023), (16.20)–(16.22), p. 373: for `ρ ≠ 0`, adapted `u_s` and `v_0` known at
date 0, `fiscalPath` solves the fiscal block. -/
theorem fiscalPath_block {ρ : ℝ} (hρ : ρ ≠ 0) (α γ : ℝ) {us pistar π : ℕ → Ω → ℝ}
    {v0 : Ω → ℝ} (hus : 𝔼.Adapted us) (hv0 : 𝔼.E 0 v0 = v0) :
    FiscalBlock 𝔼 ρ α γ us pistar π (fiscalSurplus 𝔼 ρ α γ us pistar π v0)
      (fun t => (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1)
      (fun t => (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2) := by
  have had : ∀ t, 𝔼.E t (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 =
      (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 ∧
      𝔼.E t (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 =
        (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 := by
    intro t
    induction t with
    | zero => exact ⟨hv0, hv0⟩
    | succ t ih =>
      have k1 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.1
      have k2 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.2
      constructor <;>
        simp only [fiscalPath, map_smul, map_sub, map_add, k1, k2, innov_known_next, hus (t + 1)]
  refine ⟨fun t => (had t).1, fun t => (had t).2, rfl, fun t => rfl, fun t => ?_, fun t => ?_⟩
  · simp only [fiscalPath, fiscalSurplus, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  · simp only [fiscalPath, fiscalSurplus, smul_smul, mul_inv_cancel₀ hρ, one_smul]

/-- Cochrane (2023), p. 373 and survey error E6: if `γ ≠ α` and some inflation path has
unexpected inflation different from the target's, fiscal policy is NOT passive: along that
path the transversality condition fails. -/
theorem not_passive_of_ne {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (husa : 𝔼.Adapted us) {pistar π : ℕ → Ω → ℝ} {t₀ : ℕ}
    (hne : innov 𝔼 t₀ (π (t₀ + 1)) ≠ innov 𝔼 t₀ (pistar (t₀ + 1))) :
    ¬ FiscalPassive 𝔼 ρ α γ us := by
  intro hP
  have hb := fiscalPath_block 𝔼 hρ0.ne' α γ (pistar := pistar) (π := π) (v0 := 0) husa
    (by simp)
  have htvc := hP _ _ _ _ _ hb
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hb] at htvc
  have hgap : ∀ t, (fiscalPath 𝔼 ρ α γ us pistar π 0 t).1 =
      (fiscalPath 𝔼 ρ α γ us pistar π 0 t).2 := fun t => funext fun ω => by
    have := htvc t ω
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hγ
    · exact sub_eq_zero.mp h0
  exact hne ((gap_zero_iff 𝔼 hρ0.ne' hb).mp hgap t₀)

/-- Cochrane (2023), p. 373 (corrected; survey error E6): on any expectation system with a
nonzero innovation, fiscal policy (16.20)–(16.22) is passive if and only if `γ = α`. The
printed "active-monetary passive-fiscal policy with `φ > 1`, `γ > 0`" is passive only for
`γ = α`; every `γ ≠ α` makes the fiscal rule active as well. -/
theorem passive_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us)
    (hnt : ∃ (x : ℕ → Ω → ℝ) (t : ℕ), innov 𝔼 t (x (t + 1)) ≠ 0) :
    FiscalPassive 𝔼 ρ α γ us ↔ γ = α := by
  constructor
  · intro hP
    by_contra hγ
    obtain ⟨x, t, hx⟩ := hnt
    have hne : innov 𝔼 t (x (t + 1)) ≠ innov 𝔼 t ((0 : ℕ → Ω → ℝ) (t + 1)) := by
      simpa [Innovation.innov] using hx
    exact not_passive_of_ne 𝔼 hρ0 hρ1 hα0 hα2 hγ hus husa hne hP
  · rintro rfl
    exact passive_of_eq 𝔼 hρ0 hρ1 hα0 hα2 hus

/-- Cochrane (2023), (16.20), p. 373: under the monetary block, the inflation gap
`x = π − π*` obeys `x_{t+1} = φ x_t + (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`. -/
theorem gap_succ {φ : ℝ} {istar pistar π i : ℕ → Ω → ℝ}
    (h : MonetaryBlock 𝔼 φ istar pistar π i) (t : ℕ) :
    π (t + 1) - pistar (t + 1) =
      φ • (π t - pistar t) + (innov 𝔼 t (π (t + 1)) - innov 𝔼 t (pistar (t + 1))) := by
  rw [innov_eq_sub_E 𝔼 (h.1.1 (t + 1)), innov_eq_sub_E 𝔼 (h.2.1 (t + 1)), ← h.1.2.1 t,
    ← h.2.2 t,
    h.1.2.2 t]
  abel

/-- Cochrane (2023), p. 373 (active fiscal, passive money): if `γ ≠ α`, every equilibrium has
`ΔE π = ΔE π*` and `v = v*` (for EVERY `φ`), and the inflation gap is `φᵗ(π_0 − π*_0)`; so
`π = π*` exactly when the date-0 inflation is on target. -/
theorem af_regime {ρ α γ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    (hγ : γ ≠ α) {us istar pistar π i s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) :
    (∀ t, innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1))) ∧ (∀ t, v t = vs t) ∧
      (∀ t, π t - pistar t = φ ^ t • (π 0 - pistar 0)) ∧
      (π 0 = pistar 0 → π = pistar ∧ i = istar) := by
  obtain ⟨hm, hf, htvc⟩ := h
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf] at htvc
  have hv : ∀ t, v t = vs t := fun t => funext fun ω => by
    rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hγ
    · exact sub_eq_zero.mp h0
  have hd := (gap_zero_iff 𝔼 hρ0.ne' hf).mp hv
  have hx : ∀ t, π t - pistar t = φ ^ t • (π 0 - pistar 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [gap_succ 𝔼 hm t, hd t, sub_self, add_zero, ih, smul_smul, pow_succ,
        mul_comm]
  refine ⟨hd, hv, hx, fun h0 => ?_⟩
  have hπ : π = pistar := funext fun t => by
    have := hx t
    rw [h0, sub_self, smul_zero] at this
    exact sub_eq_zero.mp this
  refine ⟨hπ, funext fun t => ?_⟩
  rw [hm.1.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 373 ("most simply `φ = 0`"): in the active-fiscal regime with `φ = 0`,
inflation equals its target from date 1 on, with no initial condition. -/
theorem af_regime_phi_zero {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) {us istar pistar π i s v vs : ℕ → Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ M) (h : UnifiedEq 𝔼 ρ α γ 0 us istar pistar π i s v vs)
    (t : ℕ) : π (t + 1) = pistar (t + 1) := by
  have := (af_regime 𝔼 hρ0 hρ1 hα0 hα2 hγ hus h).2.2.1 (t + 1)
  rw [zero_pow (Nat.succ_ne_zero t), zero_smul] at this
  exact sub_eq_zero.mp this

/-- Cochrane (2023), p. 373 (active money): if `|φ| > 1` and the targets are bounded, every
equilibrium with bounded inflation has `π = π*`, `i = i*` and `v = v*` (for EVERY `γ`). -/
theorem am_regime {ρ α γ φ : ℝ} (hρ0 : 0 < ρ) (hφ : 1 < |φ|)
    {us istar pistar π i s v vs : ℕ → Ω → ℝ}
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) (hbs : BoundedProc pistar)
    (hb : BoundedProc π) : π = pistar ∧ i = istar ∧ ∀ t, v t = vs t := by
  obtain ⟨hπ, hi⟩ := king_bounded_eq 𝔼 hφ h.1.2 hbs h.1.1 hb
  refine ⟨hπ, hi, (gap_zero_iff 𝔼 hρ0.ne' h.2.1).mpr fun t => by rw [hπ]⟩

/-! ### NI-6: (16.23)–(16.24) -/

/-- Cochrane (2023), (16.23)–(16.24), p. 373: the observable system `i_t = E_t π_{t+1}`,
`s_{t+1} = α v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s_{t+1}`, with `π`, `v`
adapted. -/
def ObsFiscal (ρ α : ℝ) (us π i s v : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ 𝔼.Adapted v ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    (∀ t, s (t + 1) = α • v t + us (t + 1)) ∧
    ∀ t, ρ • v (t + 1) = v t - innov 𝔼 t (π (t + 1)) - s (t + 1)

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6): in every regime (every `φ`, every `γ`),
the observables of every equilibrium satisfy (16.23)–(16.24), in which neither `φ` nor `γ`
appears. -/
theorem unifiedEq_obs {ρ α γ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us istar pistar π i s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) : ObsFiscal 𝔼 ρ α us π i s v := by
  obtain ⟨hm, hf, htvc⟩ := h
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf] at htvc
  refine ⟨hm.1.1, hf.1, hm.1.2.1, fun t => ?_, hf.2.2.2.2.2⟩
  rw [hf.2.2.2.1 t]
  by_cases hγ : γ = α
  · subst hγ
    rw [smul_sub, add_sub_cancel]
  · have hv : v t = vs t := funext fun ω => by
      rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0).symm hγ
      · exact sub_eq_zero.mp h0
    rw [hv, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6, converse): every solution of the observable
system is an equilibrium of EVERY regime `(φ, γ)`, with targets `i* = i`, `π* = π`, `v* = v`. -/
theorem obs_unifiedEq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us π i s v : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (h : ObsFiscal 𝔼 ρ α us π i s v)
    (γ φ : ℝ) : UnifiedEq 𝔼 ρ α γ φ us i π π i s v v := by
  have hf : FiscalBlock 𝔼 ρ α γ us π π s v v :=
    ⟨h.2.1, h.2.1, rfl, fun t => by rw [h.2.2.2.1 t, sub_self, smul_zero, add_zero],
      h.2.2.2.2, h.2.2.2.2⟩
  refine ⟨⟨⟨h.1, h.2.2.1, fun t => by rw [sub_self, smul_zero, add_zero]⟩,
    ⟨h.1, h.2.2.1⟩⟩, hf, ?_⟩
  exact (tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf).mpr fun t ω => by simp

/-- Cochrane (2023), p. 373: the observable processes `(π, i, s, v)` of the equilibria of the
regime `(φ, γ)`. -/
def eqObs (ρ α γ φ : ℝ) (us : ℕ → Ω → ℝ) :
    Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | ∃ istar pistar vs, UnifiedEq 𝔼 ρ α γ φ us istar pistar o.1 o.2.1 o.2.2.1 o.2.2.2 vs}

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6): for every regime, the set of observable
equilibrium processes is exactly the solution set of (16.23)–(16.24). -/
theorem eqObs_eq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (γ φ : ℝ) :
    eqObs 𝔼 ρ α γ φ us = {o | ObsFiscal 𝔼 ρ α us o.1 o.2.1 o.2.2.1 o.2.2.2} := by
  ext ⟨π, i, s, v⟩
  constructor
  · rintro ⟨istar, pistar, vs, h⟩
    exact unifiedEq_obs 𝔼 hρ0 hρ1 hα0 hα2 hus h
  · intro h
    exact ⟨i, π, v, obs_unifiedEq 𝔼 hρ0 hρ1 hα0 hα2 hus h γ φ⟩

/-- Cochrane (2023), p. 373 ("the regimes are observationally equivalent"): the
active-fiscal regime (`φ = 0`, `γ = 0`) and the active-money regime (`φ > 1`, `γ = α`), and
indeed any two regimes, have the same observable equilibrium processes. -/
theorem regimes_observationally_equivalent {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα0 : 0 < α) (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (γ₁ φ₁ γ₂ φ₂ : ℝ) : eqObs 𝔼 ρ α γ₁ φ₁ us = eqObs 𝔼 ρ α γ₂ φ₂ us := by
  rw [eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus, eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus]

/-- Cochrane (2023), p. 373 ("The fiscal parameter `γ` is just as unidentified as the monetary
parameter `φ`"): whenever an observed process is an equilibrium of one regime, it is an
equilibrium of every other regime. -/
theorem gamma_phi_not_identified {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {γ₁ φ₁ : ℝ}
    {o : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)}
    (ho : o ∈ eqObs 𝔼 ρ α γ₁ φ₁ us) (γ₂ φ₂ : ℝ) : o ∈ eqObs 𝔼 ρ α γ₂ φ₂ us := by
  rwa [regimes_observationally_equivalent 𝔼 hρ0 hρ1 hα0 hα2 hus γ₁ φ₁ γ₂ φ₂] at ho

/-- Cochrane (2023), (16.23)–(16.24), p. 373: for an adapted bounded surplus disturbance the
observable equilibrium set of every regime is nonempty (zero inflation and interest rate, with
the debt and surplus paths that (16.24) implies from `v_0 = 0`). -/
theorem eqObs_nonempty {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us) (γ φ : ℝ) :
    (eqObs 𝔼 ρ α γ φ us).Nonempty := by
  have hb := fiscalPath_block 𝔼 hρ0.ne' α α (us := us) (pistar := 0) (π := 0) (v0 := 0) husa
    (map_zero _)
  have hgap := (gap_zero_iff 𝔼 hρ0.ne' hb).mpr fun _ => rfl
  refine ⟨(0, 0, fiscalSurplus 𝔼 ρ α α us 0 0 0, fun t => (fiscalPath 𝔼 ρ α α us 0 0 0 t).1),
    ?_⟩
  rw [eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus γ φ]
  refine ⟨fun t => map_zero _, hb.1, fun t => (map_zero _).symm, fun t => ?_, hb.2.2.2.2.2⟩
  dsimp only
  rw [hb.2.2.2.1 t]
  dsimp only
  rw [hgap t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 373 and §16.10.7, p. 394: the class of unified-model specifications
`(γ, φ, observation)` whose observation is an equilibrium of the regime `(φ, γ)`. -/
def unifiedClass (ρ α : ℝ) (us : ℕ → Ω → ℝ) :
    Set (ℝ × ℝ × ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ))) :=
  {m | m.2.2 ∈ eqObs 𝔼 ρ α m.1 m.2.1 us}

/-- Cochrane (2023), p. 373 ("The fiscal parameter `γ` is just as unidentified as the monetary
parameter `φ`") and §16.10.7, p. 394 ("The argument admittedly cuts both ways"): neither `γ`
nor `φ` is identified, hence neither is learnable from equilibrium time series. -/
theorem gamma_phi_not_learnable {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us) :
    ¬ IdentifiedOn (unifiedClass 𝔼 ρ α us) (fun m => m.2.2) Prod.fst ∧
      ¬ IdentifiedOn (unifiedClass 𝔼 ρ α us) (fun m => m.2.2) (fun m => m.2.1) := by
  obtain ⟨o, ho⟩ := eqObs_nonempty 𝔼 hρ0 hρ1 hα0 hα2 hus husa 0 0
  have hmem : ∀ γ φ : ℝ, ((γ, φ, o) : ℝ × ℝ × _) ∈ unifiedClass 𝔼 ρ α us := fun γ φ =>
    gamma_phi_not_identified 𝔼 hρ0 hρ1 hα0 hα2 hus ho γ φ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h _ (hmem 0 0) _ (hmem 1 0) rfl
    norm_num at this
  · have := h _ (hmem 0 0) _ (hmem 0 1) rfl
    norm_num at this

/-! ### Survey error E6 on a genuine coin-flip tree -/

/-- Cochrane (2023), p. 364 (uncertainty example for E6): the coin-flip tree has a nonzero
innovation, `ΔE_1 ε_1 = ±1`. -/
theorem coin_innov_ne_zero :
    innov ExpectationsFiniteTree.coinSystem 0 (ExpectationsFiniteTree.coinShock 1) ≠ 0 := by
  intro h
  have e := congrFun h (true, true)
  rw [Innovation.innov, coinShock_adapted 1, ExpectationsFiniteTree.coinShock_mean_zero 0] at e
  simp [ExpectationsFiniteTree.coinShock] at e

/-- Cochrane (2023), p. 373 (survey error E6): on the coin-flip tree, fiscal policy
(16.20)–(16.22) is passive iff `γ = α`. -/
theorem coin_passive_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Bool × Bool → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (husa : ExpectationsFiniteTree.coinSystem.Adapted us) :
    FiscalPassive ExpectationsFiniteTree.coinSystem ρ α γ us ↔ γ = α :=
  passive_iff _ hρ0 hρ1 hα0 hα2 hus husa ⟨_, 0, coin_innov_ne_zero⟩

/-- Cochrane (2023), p. 373 (survey error E6): the printed active-money/passive-fiscal regime
"`γ > 0`" is not passive in general. With `ρ = α = 1/2` and `γ = 1` (so `γ > 0`, and also
`0 < γ < 2`) fiscal policy on the coin-flip tree is not passive. -/
theorem e6_printed_fails :
    ¬ FiscalPassive ExpectationsFiniteTree.coinSystem (1 / 2) (1 / 2) 1 0 := by
  rw [coin_passive_iff (M := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => by simp) (fun t => by simp)]
  norm_num

/-- Cochrane (2023), p. 373 (survey error E6): the off-target sunspot path
`π_{t+1} = φ π_t + ε_{t+1}`, `π_0 = 0`, on the coin-flip tree, with targets `π* = i* = 0`. -/
noncomputable def coinSunspot (φ : ℝ) : ℕ → Bool × Bool → ℝ :=
  ForwardSolution.sunspotFamily φ⁻¹ 0 ExpectationsFiniteTree.coinShock 0

/-- Cochrane (2023), p. 373 (survey error E6): for every `φ ≠ 0` the sunspot path solves the
monetary block with targets zero: it is a legitimate off-target monetary path. -/
theorem coinSunspot_monetary {φ : ℝ} (hφ : φ ≠ 0) :
    MonetaryBlock ExpectationsFiniteTree.coinSystem φ 0 0 (coinSunspot φ)
      (fisherRate ExpectationsFiniteTree.coinSystem (coinSunspot φ)) := by
  have hz0 : ExpectationsFiniteTree.coinSystem.E 0 (0 : Bool × Bool → ℝ) = 0 := map_zero _
  have hua : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  have hsol := ForwardSolution.sunspotFamily_solves ExpectationsFiniteTree.coinSystem
    (inv_ne_zero hφ) hz0 hua coinShock_adapted ExpectationsFiniteTree.coinShock_mean_zero
  have had := ForwardSolution.sunspotFamily_adapted ExpectationsFiniteTree.coinSystem
    (a := φ⁻¹) hz0 hua coinShock_adapted
  refine ⟨⟨had, fun _ => rfl, fun t => ?_⟩, ⟨fun t => map_zero _, fun t => (map_zero _).symm⟩⟩
  have e := hsol t
  simp only [Pi.zero_apply, add_zero] at e
  simp only [fisherRate, coinSunspot, Pi.zero_apply, zero_add, sub_zero]
  conv_rhs => rw [e]
  rw [smul_smul, mul_inv_cancel₀ hφ, one_smul]

/-- Cochrane (2023), p. 373 (survey error E6): for every `φ ≠ 0` and every `γ ≠ α`, the
off-target sunspot path, with the debt and surplus it implies through (16.20)–(16.22),
violates the transversality condition. So with `γ ≠ α` the fiscal rule itself rules out
off-target paths: it is not passive. -/
theorem e6_counterexample {ρ α γ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) (hφ : φ ≠ 0) :
    MonetaryBlock ExpectationsFiniteTree.coinSystem φ 0 0 (coinSunspot φ)
        (fisherRate ExpectationsFiniteTree.coinSystem (coinSunspot φ)) ∧
      FiscalBlock ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ)
        (fiscalSurplus ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0)
        (fun t => (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1)
        (fun t => (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).2)
        ∧ ¬ TVC ExpectationsFiniteTree.coinSystem ρ (fun t =>
          (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1) := by
  have hb := fiscalPath_block ExpectationsFiniteTree.coinSystem hρ0.ne' α γ
    (us := 0) (pistar := 0) (π := coinSunspot φ) (v0 := 0) (fun t => by simp) (map_zero _)
  refine ⟨coinSunspot_monetary hφ, hb, fun htvc => ?_⟩
  rw [tvc_iff _ (M := 0) hρ0 hρ1 hα0 hα2 (fun _ _ => by simp) hb] at htvc
  have hgap : ∀ t, (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1
      = (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).2 :=
    fun t => funext fun ω => by
      rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0).symm hγ
      · exact sub_eq_zero.mp h0
  have hd := (gap_zero_iff _ hρ0.ne' hb).mp hgap 0
  have h1 : coinSunspot φ 1 = ExpectationsFiniteTree.coinShock 1 := by
    funext ω
    simp [coinSunspot, ForwardSolution.sunspotFamily]
  have hz : innov ExpectationsFiniteTree.coinSystem 0 ((0 : ℕ → Bool × Bool → ℝ) (0 + 1)) = 0 :=
    by simp [Innovation.innov]
  rw [hz, h1] at hd
  exact coin_innov_ne_zero hd

end Cochrane.NewKeynesianSelection.ObservationalEquivalence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Responses in the simplest new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.7 "Responses"
(pp. 374–377).

All results hold for an arbitrary `ExpectationSystem`; the response examples are pathwise
(along any history `ω` with the stated shocks), and each is shown to be non-vacuous on the
coin-flip event tree, where the shock at date 1 is genuinely unexpected.

## Main results

* (16.13) with `η = 0` (p. 374): `u_shock_eq_target` — a shock `u_1 = 1` is a target
  `π*_1 = −1/φ`; `king_iff_nk` (the two forms of the rule).
* Alternative paths (p. 374): `alt_paths`
  `E_s π_{s+k} = −ηᵏ u_s/(φ − η) + φᵏ (π_s + u_s/(φ − η))` for every solution;
  `alt_paths_explode` (`|E_s π_{s+k}| → ∞` unless `π_s = −u_s/(φ − η)`),
  `nonExplosive_iff` (the non-explosive solution is exactly (16.9), with no uniform bound on
  `u`, so it covers `η = 1`).
* Fisherian responses (pp. 374–375): `real_rate_zero`, `expected_follows_rate`
  (`E_t π_{t+j+1} = E_t i_{t+j}`, p. 376), `fisherian_sign`, `impulse_path`,
  `impact_signs` (inflation and the interest rate fall on impact although `u_1 > 0`; the fall
  is entirely unexpected).
* Super-Fisherian (p. 375): `super_fisherian`, `super_fisherian_coin`; open-mouth (p. 375,
  survey error E5 is a typo only): `open_mouth`, `open_mouth_price_jump`, `open_mouth_coin`.
* The rule `i_t = φ E_t π_{t+1}` (p. 376): `ruleExp_trivial` (for `φ ≠ 1` every equilibrium
  has `E_t π_{t+1} = i_t = 0`), `ruleExp_solutions`, `ruleExp_has_solution` (so the printed
  "has no solution" is imprecise), `ruleExp_disturbance`.
* The fiscal requirement (pp. 376–377): `no_fiscal_no_surprise`, `nk3_ar1_fiscal_iff`,
  `no_eq_without_fiscal`, `disinflation_iff_contraction`.
-/

namespace Cochrane.NewKeynesianSelection.Responses

open Filter Topology Cochrane.NewKeynesianSelection.Identification
open Innovation (innov IsShock innov_eq_sub_E adapted_isShock_iff coinShock_adapted)
open SimplestModel (Eq164 ar1Pi ar1Pi_eq164)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The two forms of the rule and `u_1 = 1` as a target -/

/-- Cochrane (2023), (16.12)–(16.13), pp. 366–367: the rule `i_t = i*_t + φ(π_t − π*_t)` is the
rule `i_t = φ π_t + u_t` with `u_t = i*_t − φ π*_t`. -/
theorem king_iff_nk (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) :
    KingEq 𝔼 φ istar pistar π i ↔ NKEq 𝔼 φ (fun t => istar t - φ • pistar t) π i := by
  unfold KingEq NKEq
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Cochrane (2023), p. 374 ("From (16.13), the `u_1 = 1` shock is the same thing as a
`π*_1 = −1/φ` shock"): with a serially uncorrelated disturbance (`η = 0`) the target is
`π* = −u/φ`; it satisfies (16.13) `u_t = E_t π*_{t+1} − φ π*_t`, and `π*_t = −1/φ` exactly
where `u_t = 1`. -/
theorem u_shock_eq_target {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε) (t : ℕ)
    (ω : Ω) :
    u t = 𝔼.E t (ar1Pi φ 0 u (t + 1)) - φ • ar1Pi φ 0 u t ∧
      (ar1Pi φ 0 u t ω = -1 / φ ↔ u t ω = 1) := by
  refine ⟨?_, ?_⟩
  · rw [ar1Pi_eq164 𝔼 hφ (h.isAR1 𝔼) t]
    abel
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro e
      field_simp at e
      linarith
    · intro e
      rw [e]
      field_simp

/-! ### Alternative paths and explosions (p. 374) -/

/-- Cochrane (2023), p. 374: every adapted solution of (16.4) with an AR(1) disturbance
satisfies `E_s π_{s+k} = −ηᵏ u_s/(φ − η) + φᵏ (π_s + u_s/(φ − η))` (the book's display with
`s = 1`, `k = t`). -/
theorem alt_paths {φ η : ℝ} (hφη : φ ≠ η) {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) (s k : ℕ) :
    𝔼.E s (π (s + k)) =
      (-(η ^ k * (φ - η)⁻¹)) • u s + φ ^ k • (π s + (φ - η)⁻¹ • u s) := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  set c := (φ - η)⁻¹ with hc
  set d : ℕ → Ω → ℝ := fun t => π t + c • u t with hd
  have hdd : ∀ t, 𝔼.E t (d (t + 1)) = φ • d t := by
    intro t
    simp only [hd, map_add, map_smul, hπ t, h.E_succ 𝔼 t, smul_add, smul_smul]
    have : c * η = φ * c - 1 := by rw [hc]; field_simp; ring
    rw [this, sub_smul, one_smul]
    abel
  have hiter : ∀ k, 𝔼.E s (d (s + k)) = φ ^ k • d s := by
    intro k
    induction k with
    | zero => simp only [hd, add_zero, pow_zero, one_smul, map_add, map_smul, ha s, h.1 s]
    | succ k ih =>
      rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right s k), hdd, map_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have hu : ∀ k, 𝔼.E s (u (s + k)) = η ^ k • u s :=
    𝔼.ar1_iterate ⟨h.1, h.E_succ 𝔼⟩ s
  have e := hiter k
  simp only [hd, map_add, map_smul, hu k, smul_smul] at e
  rw [show 𝔼.E s (π (s + k)) = φ ^ k • (π s + c • u s) - (c * η ^ k) • u s by rw [← e]; abel]
  rw [neg_smul, sub_eq_add_neg, add_comm, mul_comm]

/-- Cochrane (2023), p. 364: a solution is non-explosive if, at every date and state, its
expected future path `k ↦ |E_s π_{s+k}|` is bounded. -/
def NonExplosive (π : ℕ → Ω → ℝ) : Prop :=
  ∀ s ω, BddAbove (Set.range fun k => |𝔼.E s (π (s + k)) ω|)

/-- Cochrane (2023), p. 374 ("Inflation explodes for any value of `π_1` but one"): for
`|φ| > 1 ≥ |η|`, if `π_s ≠ −u_s/(φ − η)` at a state, then `|E_s π_{s+k}| → ∞` there. -/
theorem alt_paths_explode {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) {s : ℕ}
    {ω : Ω} (hd : π s ω ≠ ar1Pi φ η u s ω) :
    Tendsto (fun k => |𝔼.E s (π (s + k)) ω|) atTop atTop := by
  have hD0 : π s ω + (φ - η)⁻¹ * u s ω ≠ 0 := by
    intro h0
    apply hd
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul]
    linarith
  have hlow : ∀ k, |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω| - |(φ - η)⁻¹ * u s ω| ≤
      |𝔼.E s (π (s + k)) ω| := by
    intro k
    rw [alt_paths 𝔼 hφη h ha hπ s k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set A := φ ^ k * (π s ω + (φ - η)⁻¹ * u s ω) with hA
    set B := -(η ^ k * (φ - η)⁻¹) * u s ω with hB
    have h1 : |B| ≤ |(φ - η)⁻¹ * u s ω| := by
      rw [hB, abs_mul, abs_neg, abs_mul, abs_pow, abs_mul]
      have : |η| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg η) hη
      nlinarith [abs_nonneg (φ - η)⁻¹, abs_nonneg (u s ω),
        mul_nonneg (abs_nonneg (φ - η)⁻¹) (abs_nonneg (u s ω))]
    have h2 : |A| = |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω| := by rw [hA, abs_mul, abs_pow]
    have h3 := abs_sub_abs_le_abs_sub A (-B)
    rw [abs_neg, sub_neg_eq_add, add_comm] at h3
    linarith
  have hT : Tendsto (fun k : ℕ => |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hD0)
  exact tendsto_atTop_mono hlow (by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-|(φ - η)⁻¹ * u s ω|) hT)

/-- Cochrane (2023), pp. 364, 374: for `|φ| > 1 ≥ |η|` and `φ ≠ η`, an adapted solution of
(16.4) is non-explosive iff it is (16.9) `π = −u/(φ − η)`. No uniform bound on `u` is needed,
so this covers the random-walk case `η = 1` of the super-Fisherian response. -/
theorem nonExplosive_iff {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) :
    NonExplosive 𝔼 π ↔ π = ar1Pi φ η u := by
  constructor
  · intro hne
    funext s ω
    by_contra hd
    exact not_bddAbove_of_tendsto_atTop (alt_paths_explode 𝔼 hφ hη hφη h ha hπ hd) (hne s ω)
  · rintro rfl s ω
    refine ⟨|(φ - η)⁻¹ * u s ω|, ?_⟩
    rintro _ ⟨k, rfl⟩
    change |𝔼.E s (ar1Pi φ η u (s + k)) ω| ≤ _
    rw [alt_paths 𝔼 hφη h ha hπ s k]
    simp only [ar1Pi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_add_cancel,
      mul_zero, add_zero]
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_pow, mul_assoc]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (abs_nonneg η) hη)

/-! ### Fisherian responses (pp. 374–376) -/

/-- Cochrane (2023), p. 374 ("The model is Fisherian `i_t = E_t π_{t+1}` throughout"): the
ex-ante real rate is identically zero in every equilibrium. -/
theorem real_rate_zero {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t : ℕ) :
    i t - 𝔼.E t (π (t + 1)) = 0 := by
  rw [h.2.1 t, sub_self]

/-- Cochrane (2023), p. 376 ("`E_t π_{t+1} = i_t` so `E_t π_{t+j+1} = E_t i_{t+j}`"):
anticipated interest rates move expected inflation one for one with a one-period lag. -/
theorem expected_follows_rate {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t j : ℕ) :
    𝔼.E t (π (t + j + 1)) = 𝔼.E t (i (t + j)) := by
  rw [h.2.1 (t + j), 𝔼.tower (Nat.le_add_right t j)]

/-- Cochrane (2023), p. 375 ("Someone observing data from this economy would see interest
rates and inflation always moving in the same direction"): in the selected AR(1) equilibrium
with `η ≥ 0`, `i_t π_t ≥ 0` at every date and state. -/
theorem fisherian_sign (φ : ℝ) {η : ℝ} (hη : 0 ≤ η) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (t : ℕ) (ω : Ω) : 0 ≤ fisherRate 𝔼 (ar1Pi φ η u) t ω * ar1Pi φ η u t ω := by
  rw [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_nonneg hη (mul_self_nonneg _)

/-- Cochrane (2023), Figure 16.1 and p. 374: the response to a monetary shock `ε_1` from the
steady state `u_0 = 0` with no later shocks: `π_{k+1} = −ηᵏ ε_1/(φ − η)` and
`i_{k+1} = −η^{k+1} ε_1/(φ − η)`. -/
theorem impulse_path (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) {ω : Ω}
    (hu0 : u 0 ω = 0) (hε : ∀ k, ε (k + 2) ω = 0) (k : ℕ) :
    ar1Pi φ η u (k + 1) ω = -(η ^ k * ε 1 ω / (φ - η)) ∧
      fisherRate 𝔼 (ar1Pi φ η u) (k + 1) ω = -(η ^ (k + 1) * ε 1 ω / (φ - η)) := by
  have hu : ∀ k, u (k + 1) ω = η ^ k * ε 1 ω := by
    intro k
    induction k with
    | zero =>
      have := congrFun (h.2.2 0) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0, mul_zero, zero_add] at this
      rw [this, pow_zero, one_mul]
    | succ k ih =>
      have := congrFun (h.2.2 (k + 1)) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih, hε k, add_zero] at this
      rw [this, pow_succ]
      ring
  have hπ : ar1Pi φ η u (k + 1) ω = -(η ^ k * ε 1 ω / (φ - η)) := by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu k]
    ring
  refine ⟨hπ, ?_⟩
  rw [(eq_16_15 𝔼 φ h (k + 1)).1, Pi.smul_apply, smul_eq_mul, hπ]
  ring

/-- Cochrane (2023), pp. 374–375: on a positive monetary-policy shock `ε_1 > 0` from the
steady state, with `φ > η > 0`: the disturbance rises (`u_1 > 0`), yet inflation and the
observed interest rate fall on impact (`π_1 < 0`, `i_1 = φπ_1 + u_1 < 0`, the endogenous part
`φπ_1` overwhelming `u_1`), and the inflation decline is entirely unexpected (`E_0 π_1 = 0`,
so `π_1 = ΔE_1 π_1`). -/
theorem impact_signs {φ η : ℝ} (hη : 0 < η) (hφη : η < φ) {u ε : ℕ → Ω → ℝ}
    (h : AR1 𝔼 η u ε) {ω : Ω} (hu0 : u 0 ω = 0) (hε : 0 < ε 1 ω) :
    0 < u 1 ω ∧ ar1Pi φ η u 1 ω < 0 ∧ fisherRate 𝔼 (ar1Pi φ η u) 1 ω < 0 ∧
      φ * ar1Pi φ η u 1 ω + u 1 ω < 0 ∧ 𝔼.E 0 (ar1Pi φ η u 1) ω = 0 ∧
      innov 𝔼 0 (ar1Pi φ η u 1) ω = ar1Pi φ η u 1 ω := by
  have hpos : 0 < φ - η := by linarith
  have hu1 : u 1 ω = ε 1 ω := by
    have := congrFun (h.2.2 0) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0, mul_zero, zero_add] at this
    exact this
  have hπ1 : ar1Pi φ η u 1 ω = -(ε 1 ω / (φ - η)) := by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu1]
    ring
  have hE0 : 𝔼.E 0 (ar1Pi φ η u 1) ω = 0 := by
    change fisherRate 𝔼 (ar1Pi φ η u) 0 ω = 0
    rw [(eq_16_15 𝔼 φ h 0).1]
    simp [ar1Pi, hu0]
  have hi1 : fisherRate 𝔼 (ar1Pi φ η u) 1 ω = η * ar1Pi φ η u 1 ω := by
    rw [(eq_16_15 𝔼 φ h 1).1, Pi.smul_apply, smul_eq_mul]
  have hq : 0 < ε 1 ω / (φ - η) := div_pos hε hpos
  refine ⟨by rw [hu1]; exact hε, by rw [hπ1]; linarith, ?_, ?_, hE0, ?_⟩
  · rw [hi1, hπ1]; nlinarith
  · rw [hπ1, hu1]
    have : φ * -(ε 1 ω / (φ - η)) + ε 1 ω = -(η * (ε 1 ω / (φ - η))) := by
      field_simp
      ring
    rw [this]
    nlinarith
  · have had : 𝔼.Adapted (ar1Pi φ η u) := fun s => by simp only [ar1Pi, map_smul, h.1 s]
    rw [innov_eq_sub_E 𝔼 (had 1), Pi.sub_apply, hE0, sub_zero]

/-! ### Super-Fisherian and open-mouth responses (p. 375) -/

/-- Cochrane (2023), p. 375 (super-Fisherian response): with `η = 1` and the shock
`ε_1 = u_1 = 1 − φ` (so `u_t = 1 − φ` for `t ≥ 1` along `ω`), the non-explosive equilibrium has
`π_t = i_t = 1` for all `t ≥ 1`: interest rates and inflation rise together, immediately and
permanently. -/
theorem super_fisherian {φ : ℝ} (hφ : 1 < |φ|) {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 1 u ε)
    (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) (hne : NonExplosive 𝔼 π) {ω : Ω}
    (hu : ∀ t, u (t + 1) ω = 1 - φ) (t : ℕ) :
    π (t + 1) ω = 1 ∧ fisherRate 𝔼 π (t + 1) ω = 1 := by
  have hφ1 : φ ≠ 1 := fun e => by rw [e, abs_one] at hφ; exact lt_irrefl _ hφ
  have hsub : φ - 1 ≠ 0 := sub_ne_zero.mpr hφ1
  have heq := (nonExplosive_iff 𝔼 hφ (by rw [abs_one]) hφ1 h ha hπ).mp hne
  have hπt : ∀ t, π (t + 1) ω = 1 := fun t => by
    rw [heq]
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu t]
    field_simp
    ring
  refine ⟨hπt t, ?_⟩
  rw [heq, (eq_16_15 𝔼 φ h (t + 1)).1, ← heq, Pi.smul_apply, smul_eq_mul, one_mul, hπt t]

/-- Cochrane (2023), p. 375 (open-mouth operation; survey error E5 — the printed
"`π_2 = π_2 = ..`" means `π_2 = π_3 = … = 0`): with `η = 0` and the one-period shock
`u_1 = ε_1 = −φ` (`u_t = 0` otherwise along `ω`), the selected equilibrium has `π_1 = 1`,
`π_t = 0` for `t ≠ 1`, and `i_t = 0` at every date and in every state: inflation moves with no
movement in interest rates at all. -/
theorem open_mouth {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε) {ω : Ω}
    (hu1 : u 1 ω = -φ) (hu : ∀ t, t ≠ 1 → u t ω = 0) :
    ar1Pi φ 0 u 1 ω = 1 ∧ (∀ t, t ≠ 1 → ar1Pi φ 0 u t ω = 0) ∧
      ∀ t, fisherRate 𝔼 (ar1Pi φ 0 u) t = 0 := by
  refine ⟨?_, fun t ht => ?_, fun t => ?_⟩
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul, hu1]
    field_simp
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul, hu t ht, mul_zero]
  · rw [(eq_16_15 𝔼 φ h t).1, zero_smul]

/-- Cochrane (2023), p. 375 ("The price level takes a permanent jump"): in the open-mouth
response the log price level `p_t = p_0 + ∑_{s=1}^{t} π_s` rises by exactly one at date 1 and
stays there. -/
theorem open_mouth_price_jump {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε)
    {ω : Ω} (hu1 : u 1 ω = -φ) (hu : ∀ t, t ≠ 1 → u t ω = 0) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 2), ar1Pi φ 0 u s ω = 1 := by
  obtain ⟨h1, h0, -⟩ := open_mouth 𝔼 hφ h hu1 hu
  induction t with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0 0 (by norm_num), h1, zero_add]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, h0 (t + 2) (by omega), add_zero]

/-! ### Non-vacuity: the responses on the coin-flip tree -/

/-- Cochrane (2023), p. 375 (examples): a shock arriving only at date 1, `ε_1 = c·(±1)` on the
first coin flip, `ε_t = 0` otherwise. -/
noncomputable def dateOneShock (c : ℝ) (t : ℕ) : Bool × Bool → ℝ :=
  if t = 1 then c • ExpectationsFiniteTree.coinShock 1 else 0

/-- Cochrane (2023), p. 375 (examples): the date-1 shock is a shock on the coin-flip tree,
and it is adapted at every date. -/
theorem dateOneShock_isShock (c : ℝ) :
    IsShock ExpectationsFiniteTree.coinSystem (dateOneShock c) ∧
      ExpectationsFiniteTree.coinSystem.Adapted (dateOneShock c) := by
  have ha : ExpectationsFiniteTree.coinSystem.Adapted (dateOneShock c) := fun t => by
    by_cases ht : t = 1
    · subst ht
      simp only [dateOneShock, ↓reduceIte, map_smul, coinShock_adapted 1]
    · simp only [dateOneShock, ht, ↓reduceIte, map_zero]
  refine ⟨⟨fun t => ha (t + 1), fun t => ?_⟩, ha⟩
  by_cases ht : t = 0
  · subst ht
    simp only [dateOneShock, zero_add, ↓reduceIte, map_smul,
      ExpectationsFiniteTree.coinShock_mean_zero 0, smul_zero]
  · have : t + 1 ≠ 1 := by omega
    simp only [dateOneShock, this, ↓reduceIte, map_zero]

/-- Cochrane (2023), p. 375 (super-Fisherian example): the random walk `u_0 = 0`,
`u_t = (1 − φ)·(±1)` for `t ≥ 1`, on the coin-flip tree. -/
noncomputable def superU (φ : ℝ) (t : ℕ) : Bool × Bool → ℝ :=
  if t = 0 then 0 else (1 - φ) • ExpectationsFiniteTree.coinShock 1

/-- Cochrane (2023), p. 375: `superU` is an AR(1) with `η = 1` driven by the date-1 shock. -/
theorem superU_ar1 (φ : ℝ) :
    AR1 ExpectationsFiniteTree.coinSystem 1 (superU φ) (dateOneShock (1 - φ)) := by
  refine ⟨fun t => ?_, (dateOneShock_isShock (1 - φ)).1, fun t => ?_⟩
  · by_cases ht : t = 0
    · subst ht
      simp only [superU, ↓reduceIte, map_zero]
    · simp only [superU, ht, ↓reduceIte, map_smul]
      rw [ForwardSolution.E_of_known _ (Nat.one_le_iff_ne_zero.mpr ht)
        (coinShock_adapted 1)]
  · by_cases ht : t = 0
    · subst ht
      simp [superU, dateOneShock]
    · simp [superU, dateOneShock, ht]

/-- Cochrane (2023), p. 375 (super-Fisherian response, non-vacuous): on the coin-flip tree,
for every `|φ| > 1`, the selected equilibrium `π = −u/(φ − 1)` of `superU` has, on the history
where the first flip is heads, `π_t = i_t = 1` for all `t ≥ 1`, while `E_0 π_1 = 0`. -/
theorem super_fisherian_coin {φ : ℝ} (hφ : 1 < |φ|) (b : Bool) (t : ℕ) :
    ar1Pi φ 1 (superU φ) (t + 1) (true, b) = 1 ∧
      fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) (t + 1) (true, b) = 1 ∧
      ExpectationsFiniteTree.coinSystem.E 0 (ar1Pi φ 1 (superU φ) 1) = 0 := by
  have hφ1 : φ ≠ 1 := fun e => by rw [e, abs_one] at hφ; exact lt_irrefl _ hφ
  have h := superU_ar1 φ
  have ha : ExpectationsFiniteTree.coinSystem.Adapted (ar1Pi φ 1 (superU φ)) := fun s => by
    simp only [ar1Pi, map_smul, h.1 s]
  have hπ := ar1Pi_eq164 ExpectationsFiniteTree.coinSystem hφ1 (h.isAR1 _)
  have hne : NonExplosive ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) :=
    (nonExplosive_iff _ hφ (by rw [abs_one]) hφ1 h ha hπ).mpr rfl
  have hu : ∀ t, superU φ (t + 1) (true, b) = 1 - φ := fun t => by
    simp [superU, ExpectationsFiniteTree.coinShock]
  obtain ⟨h1, h2⟩ := super_fisherian _ hφ h ha hπ hne hu t
  refine ⟨h1, h2, ?_⟩
  change fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) 0 = 0
  rw [(eq_16_15 _ φ h 0).1]
  funext ω
  simp [ar1Pi, superU]

/-- Cochrane (2023), p. 375 (open-mouth operation, non-vacuous): on the coin-flip tree, with
`u = ε` the date-1 shock `−φ·(±1)`, on the heads history `π_1 = 1`, `π_t = 0` for `t ≠ 1`, and
the interest rate is zero at every date in every state. -/
theorem open_mouth_coin {φ : ℝ} (hφ : φ ≠ 0) (b : Bool) :
    ar1Pi φ 0 (dateOneShock (-φ)) 1 (true, b) = 1 ∧
      (∀ t, t ≠ 1 → ar1Pi φ 0 (dateOneShock (-φ)) t (true, b) = 0) ∧
      ∀ t, fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 0 (dateOneShock (-φ))) t = 0 := by
  have h : AR1 ExpectationsFiniteTree.coinSystem 0 (dateOneShock (-φ)) (dateOneShock (-φ)) :=
    ⟨(dateOneShock_isShock (-φ)).2, (dateOneShock_isShock (-φ)).1, fun t => by simp⟩
  refine open_mouth _ hφ h ?_ fun t ht => ?_
  · simp [dateOneShock, ExpectationsFiniteTree.coinShock]
  · simp [dateOneShock, ht]

/-! ### The rule `i_t = φ E_t π_{t+1}` (p. 376) -/

/-- Cochrane (2023), p. 376: an equilibrium of the Fisher equation with the rule
`i_t = φ E_t π_{t+1}` (a rule that "raises real interest rates when inflation rises"). -/
def RuleExpEq (φ : ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 376 (corrected): for `φ ≠ 1`, every equilibrium of the rule
`i_t = φ E_t π_{t+1}` has `E_t π_{t+1} = 0` and `i_t = 0`: the rule cannot move the interest
rate or expected inflation at all. -/
theorem ruleExp_trivial {φ : ℝ} (hφ : φ ≠ 1) {π i : ℕ → Ω → ℝ} (h : RuleExpEq 𝔼 φ π i)
    (t : ℕ) : 𝔼.E t (π (t + 1)) = 0 ∧ i t = 0 := by
  have e := (h.2.1 t).symm.trans (h.2.2 t)
  have hz : (φ - 1) • 𝔼.E t (π (t + 1)) = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  have hE := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hφ)
  exact ⟨hE, by rw [h.2.1 t, hE]⟩

/-- Cochrane (2023), p. 376 (corrected): the rule has solutions — any shock process (a shock
with `δ_0` known at date 0, i.e. adapted with `E_t δ_{t+1} = 0`) is equilibrium inflation, with
`i = 0`; so inflation is entirely indeterminate. -/
theorem ruleExp_solutions (φ : ℝ) {δ : ℕ → Ω → ℝ} (hδ : IsShock 𝔼 δ)
    (h0 : 𝔼.E 0 (δ 0) = δ 0) : RuleExpEq 𝔼 φ δ (fun _ => 0) :=
  ⟨((adapted_isShock_iff 𝔼).mpr ⟨hδ, h0⟩).1, fun t => (hδ.2 t).symm,
    fun t => by rw [hδ.2 t, smul_zero]⟩

/-- Cochrane (2023), p. 376 ("would lead to an equilibrium condition `φ E_t π_{t+1} =
E_t π_{t+1}` which has no solution"): the printed claim is imprecise — `π = 0`, `i = 0` is a
solution for every `φ` and every expectation system. -/
theorem ruleExp_has_solution (φ : ℝ) : RuleExpEq 𝔼 φ (fun _ => 0) (fun _ => 0) :=
  ruleExp_solutions 𝔼 φ ⟨fun _ => map_zero _, fun _ => map_zero _⟩ (map_zero _)

/-- Cochrane (2023), p. 376: with a disturbance, `i_t = φ E_t π_{t+1} + u_t` and `φ ≠ 1`, the
rule pins expected inflation `E_t π_{t+1} = u_t/(1 − φ)`; the real rate `i_t − E_t π_{t+1}`
is still zero, so no rule raises real rates in this model. -/
theorem ruleExp_disturbance {φ : ℝ} (hφ : φ ≠ 1) {u π i : ℕ → Ω → ℝ}
    (hF : ∀ t, i t = 𝔼.E t (π (t + 1))) (hR : ∀ t, i t = φ • 𝔼.E t (π (t + 1)) + u t)
    (t : ℕ) : 𝔼.E t (π (t + 1)) = (1 - φ)⁻¹ • u t ∧ i t - 𝔼.E t (π (t + 1)) = 0 := by
  have hne : 1 - φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hφ)
  have e := (hF t).symm.trans (hR t)
  refine ⟨?_, by rw [hF t, sub_self]⟩
  have : (1 - φ) • 𝔼.E t (π (t + 1)) = u t := by
    rw [sub_smul, one_smul, sub_eq_iff_eq_add, add_comm (u t)]
    exact e
  rw [← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ### The fiscal requirement (pp. 376–377) -/

/-- Cochrane (2023), (16.1)–(16.3), p. 364: an equilibrium of the full simplest model, including
the debt-valuation equation `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`. -/
def NK3Eq (φ : ℝ) (u εs π i : ℕ → Ω → ℝ) : Prop :=
  NKEq 𝔼 φ u π i ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -εs (t + 1)

/-- Cochrane (2023), p. 376 ("if this passive fiscal contraction does not or cannot happen, the
unexpected inflation cannot happen"): with no fiscal shock, every equilibrium has no
unexpected inflation. -/
theorem no_fiscal_no_surprise {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NK3Eq 𝔼 φ u 0 π i) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = 0 := by
  rw [h.2 t, Pi.zero_apply, neg_zero]

/-- Cochrane (2023), pp. 372, 376: the selected AR(1) equilibrium is an equilibrium of the full
model (16.1)–(16.3) iff the fiscal shock is exactly `ε_Σs,t+1 = ε_{i,t+1}/(φ − η)`. -/
theorem nk3_ar1_fiscal_iff {φ η : ℝ} (hφη : φ ≠ η) {u ε εs : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    NK3Eq 𝔼 φ u εs (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) ↔
      ∀ t, εs (t + 1) = (φ - η)⁻¹ • ε (t + 1) := by
  have hN : NKEq 𝔼 φ u (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) :=
    (nkEq_iff 𝔼 _ _ _ _).mpr ⟨fun s => by simp only [ar1Pi, map_smul, h.1 s],
      ar1Pi_eq164 𝔼 hφη (h.isAR1 𝔼), rfl⟩
  constructor
  · intro h3 t
    have e := h3.2 t
    rw [eq_16_16_innov 𝔼 φ h t, neg_smul, neg_inj] at e
    exact e.symm
  · intro hs
    exact ⟨hN, fun t => by rw [eq_16_16_innov 𝔼 φ h t, hs t, neg_smul]⟩

/-- Cochrane (2023), pp. 376–377: if a monetary-policy shock occurs (`ε_{t+1} ≠ 0` somewhere)
and there is no fiscal response (`ε_Σs = 0`), then (16.1)–(16.3) has NO non-explosive
equilibrium (`|φ| > 1 ≥ |η|`): the new-Keynesian response exists only because of the
"passive" fiscal contraction. -/
theorem no_eq_without_fiscal {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) {t : ℕ} {ω : Ω} (hε : ε (t + 1) ω ≠ 0) :
    ¬ ∃ π i, NK3Eq 𝔼 φ u 0 π i ∧ NonExplosive 𝔼 π := by
  rintro ⟨π, i, h3, hne⟩
  have hN := (nkEq_iff 𝔼 _ _ _ _).mp h3.1
  have heq := (nonExplosive_iff 𝔼 hφ hη hφη h hN.1 hN.2.1).mp hne
  have e := congrFun (no_fiscal_no_surprise 𝔼 h3 t) ω
  rw [heq, eq_16_16_innov 𝔼 φ h t] at e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul, neg_eq_zero,
    mul_eq_zero, inv_eq_zero, sub_eq_zero] at e
  rcases e with e | e
  · exact hφη e
  · exact hε e

/-- Cochrane (2023), p. 376 ("the monetary policy shock lowers inflation because it induces a
fiscal contraction, and only because it induces a fiscal contraction"): in every equilibrium
of (16.1)–(16.3), unexpected inflation is negative exactly when the fiscal shock (the rise in
the present value of surpluses) is positive. -/
theorem disinflation_iff_contraction {φ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : NK3Eq 𝔼 φ u εs π i)
    (t : ℕ) (ω : Ω) : innov 𝔼 t (π (t + 1)) ω < 0 ↔ 0 < εs (t + 1) ω := by
  rw [h.2 t, Pi.neg_apply, neg_lt_zero]

end Cochrane.NewKeynesianSelection.Responses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Global multiplicity despite local determinacy (restated from the Woodford Chapter 2 project)

Cochrane (2023), Chapter 16, §16.8, pp. 377–380 and §16.10, pp. 383–396: the one-dimensional
perfect-foresight dynamics `Π_{t+1} = Φ(Π_t)` of Figure 16.2 are studied with the lemmas of this
module, restated verbatim (namespace adapted) from the Woodford Chapter 2 project, whose
docstrings cite Woodford (2003)'s pages.

Woodford (2003), *Interest and Prices*, Chapter 2, §4.1, pp. 123–131 (with the
one-dimensional dynamics lemma L5 of the chapter survey). Everything here is
perfect foresight: plain real sequences.

* **L5 (monotone one-dimensional maps).** `orbit_monotone_of_le`,
  `orbit_antitone_of_ge`: orbits of a map monotone on an invariant set are monotone;
  `monotone_orbit_atTop_or_fixed`, `antitone_orbit_atBot_or_fixed`: a monotone orbit
  diverges or converges, and its limit is a fixed point wherever the map is continuous;
  `repelling_of_one_lt_abs_deriv`: slope of modulus > 1 at a fixed point makes it
  repelling; `attracting_of_abs_deriv_lt_one`: slope of modulus < 1 makes it attracting.
* **(4.2), p. 124.** The fiscal rule `T = αW − ΔM` gives `Q_{t,t+1}W_{t+1} = (1−α)W_t`
  (`ricardian_step`), hence `Q_{t,T}W_T = (1−α)^{T−t}W_t → 0` (`ricardian_tvc`) for
  `0 < α ≤ 1`; for `α = 0` the TVC can fail (`ricardian_tvc_fails_of_alpha_zero`).
* **(4.5)–(4.6), p. 125.** `eq45_iff_fisher` derives (4.5) from the Fisher equation (4.3);
  `isPath45_iff_isPath46_of_const` gives (4.6) when `λ` is constant.
* **p. 125, fn. 58.** Every initial inflation rate starts a solution of (4.6)
  (`orbit46_isPath`), solutions are pinned down by `Π₀` (`isPath46_eq_orbit`), and
  (4.4) holds along any interest path when `λ` and `iL(i)` are bounded
  (`bound44_summable`): a continuum of perfect-foresight equilibria
  (`continuum_pf_equilibria`).
* **p. 125.** The Taylor coefficient at `Π*` is the slope of the map
  (`taylorCoeff_eq_slope`); under the local Taylor principle there is a second steady
  state `Π** ∈ [β, Π*)` at which the Taylor principle fails (`second_steady_state`).
* **p. 126.** Self-fulfilling deflations converge to `β` (`self_fulfilling_deflation46`,
  `deflation46_strictAnti`, `deflation46_eventually_deflation`), and the deflationary
  steady state is locally indeterminate (`deflationary_steady_state_indeterminate`).
* **p. 127, error E6.** "Inflation above target always rises without bound" needs a
  global hypothesis: `inflation_unbounded46` proves it when `φ(Π) > Π/β − 1` above `Π*`,
  `inflation_unbounded_iff` shows that this (no steady state above `Π*`) is exactly what
  is needed, and `e6_counterexample` gives a continuous increasing `φ ≥ 0` satisfying
  the Taylor principle at `Π*` with a bounded path starting above target.
* **p. 127.** Every path other than `Π*` leaves a neighbourhood of `Π*`
  (`target_locally_repelling`).
* **p. 127.** With real-balance effects: `λ` decreasing makes `Π/λ(φ(Π))` strictly
  increasing (`ratio_strictMonoOn`); then (4.5) has the same steady states
  (`steady_state45_iff`), at most one solution per `Π₀` (`isPath45_unique`), a solution for
  every `Π₀ ∈ (β, Π*)` (`deflation45_exists`), each converging to `β`
  (`self_fulfilling_deflation45`) and satisfying (4.4) (`deflation45_bound44`).
* **p. 127, fn. 61, "`λ` not too strongly increasing".** Without monotonicity of `λ`, the same
  holds under (H1) `Π/λ(φ(Π))` strictly increasing and (H2) `λ(i) ≤ (1 + i)λ(0)`
  (`step45_down_gen`, `self_fulfilling_deflation45_gen`, `deflation45_exists_gen`;
  `antitone_lam_gives_gen` shows the `u_cm > 0` case is included), and
  `deflation45_counterexample` shows a restriction is needed (`λ(i) = 1 + i`: a path starting
  in `(β, Π*)` jumps to `Π*`).
* **pp. 127–128, (4.4) along self-fulfilling deflations of (4.5)**, with no bound on `λ`
  assumed: `deflation45_bound44_gen` (via `bound44_summable_path`); boundedness of `λ` along the
  path is derived from continuity on the compact range `[0, φ(Π₀)]` of interest rates.
-/

namespace Cochrane.NewKeynesianSelection.GlobalDynamics

open Filter Topology

/-! ## L5: one-dimensional monotone maps -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (used in Woodford (2003), §4.1–4.3, pp. 123–138): if `g` is monotone on an
invariant set `S` and the orbit `x_{t+1} = g(x_t)` starts in `S` with `x₀ ≤ x₁`, the orbit is
monotone. -/
theorem orbit_monotone_of_le {g : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn g S)
    (hmaps : Set.MapsTo g S S) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) (h0 : x 0 ∈ S)
    (hle : x 0 ≤ x 1) : Monotone x := by
  have hmem : ∀ t, x t ∈ S := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => rw [hx]; exact hmaps ih
  refine monotone_nat_of_le_succ fun t => ?_
  induction t with
  | zero => exact hle
  | succ n ih =>
    calc x (n + 1) = g (x n) := hx n
      _ ≤ g (x (n + 1)) := hmono (hmem n) (hmem (n + 1)) ih
      _ = x (n + 1 + 1) := (hx (n + 1)).symm

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), §4.1–4.3): if `g` is monotone on an invariant set `S` and
the orbit starts in `S` with `x₁ ≤ x₀`, the orbit is antitone. -/
theorem orbit_antitone_of_ge {g : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn g S)
    (hmaps : Set.MapsTo g S S) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) (h0 : x 0 ∈ S)
    (hge : x 1 ≤ x 0) : Antitone x := by
  have hmem : ∀ t, x t ∈ S := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => rw [hx]; exact hmaps ih
  refine antitone_nat_of_succ_le fun t => ?_
  induction t with
  | zero => exact hge
  | succ n ih =>
    calc x (n + 1 + 1) = g (x (n + 1)) := hx (n + 1)
      _ ≤ g (x n) := hmono (hmem (n + 1)) (hmem n) ih
      _ = x (n + 1) := (hx n).symm

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), §4.1): a limit of an orbit `x_{t+1} = g(x_t)` at which
`g` is continuous is a fixed point of `g`. -/
theorem fixed_of_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) {L : ℝ}
    (hL : Tendsto x atTop (𝓝 L)) (hc : ContinuousAt g L) : g L = L := by
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).mpr hL
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g L)) := by
    have : (fun t => x (t + 1)) = g ∘ x := funext fun t => hx t
    rw [this]
    exact hc.tendsto.comp hL
  exact tendsto_nhds_unique h2 h1

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), §4.1): a monotone orbit either diverges to `+∞` or
converges to a limit bounding it from above, which is a fixed point wherever `g` is
continuous. -/
theorem monotone_orbit_atTop_or_fixed {g : ℝ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = g (x t)) (hmono : Monotone x) :
    Tendsto x atTop atTop ∨
      ∃ L, Tendsto x atTop (𝓝 L) ∧ (∀ t, x t ≤ L) ∧ (ContinuousAt g L → g L = L) := by
  by_cases hb : BddAbove (Set.range x)
  · right
    refine ⟨⨆ t, x t, tendsto_atTop_ciSup hmono hb, fun t => le_ciSup hb t, fun hc => ?_⟩
    exact fixed_of_tendsto hx (tendsto_atTop_ciSup hmono hb) hc
  · left
    refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
    rw [not_bddAbove_iff] at hb
    obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hb b
    exact ⟨t, hy.le⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), §4.1): an antitone orbit either diverges to `−∞` or
converges to a limit bounding it from below, which is a fixed point wherever `g` is
continuous. -/
theorem antitone_orbit_atBot_or_fixed {g : ℝ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = g (x t)) (hanti : Antitone x) :
    Tendsto x atTop atBot ∨
      ∃ L, Tendsto x atTop (𝓝 L) ∧ (∀ t, L ≤ x t) ∧ (ContinuousAt g L → g L = L) := by
  by_cases hb : BddBelow (Set.range x)
  · right
    refine ⟨⨅ t, x t, tendsto_atTop_ciInf hanti hb, fun t => ciInf_le hb t, fun hc => ?_⟩
    exact fixed_of_tendsto hx (tendsto_atTop_ciInf hanti hb) hc
  · left
    refine tendsto_atTop_atBot_of_antitone hanti fun b => ?_
    rw [not_bddBelow_iff] at hb
    obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hb b
    exact ⟨t, hy.le⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), p. 125): near a point where `f` has a positive derivative,
`f` is below `f x` just to the left and above `f x` just to the right. -/
theorem sign_near_of_deriv_pos {f : ℝ → ℝ} {x c : ℝ} (hd : HasDerivAt f c x) (hc : 0 < c) :
    ∃ δ > 0, (∀ y, x - δ < y → y < x → f y < f x) ∧ (∀ y, x < y → y < x + δ → f x < f y) := by
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (half_pos hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun y h1 h2 => ?_, fun y h1 h2 => ?_⟩
  · have hy : dist y x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hy
    simp only [Real.norm_eq_abs, smul_eq_mul] at this
    rw [abs_of_neg (by linarith : y - x < 0)] at this
    have := (abs_le.mp this).2
    nlinarith
  · have hy : dist y x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hy
    simp only [Real.norm_eq_abs, smul_eq_mul] at this
    rw [abs_of_pos (by linarith : 0 < y - x)] at this
    have := (abs_le.mp this).1
    nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5, "slope > 1 ⇒ repelling" (Woodford (2003), p. 127): if `g(x*) = x*` and
`|g'(x*)| > 1`, there is `δ > 0` such that every orbit not starting at `x*` eventually lies at
distance at least `δ` from `x*`. -/
theorem repelling_of_one_lt_abs_deriv {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : 1 < |d|) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → x 0 ≠ xs →
      ∃ t, δ ≤ |x t - xs| := by
  have hε : 0 < (|d| - 1) / 2 := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
  by_contra hcon
  push Not at hcon
  set k := (|d| + 1) / 2 with hk
  have hk1 : 1 < k := by rw [hk]; linarith
  have hstep : ∀ y, |y - xs| < δ → k * |y - xs| ≤ |g y - xs| := by
    intro y hy
    have h := hball (by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |(y - xs) * d| ≤ |g y - xs - (y - xs) * d| + |g y - xs| := by
      have := abs_sub (g y - xs) (g y - xs - (y - xs) * d)
      simp only [sub_sub_cancel] at this
      linarith [abs_sub_comm (g y - xs - (y - xs) * d) (g y - xs)]
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (y - xs)]
  have hgrow : ∀ t, k ^ t * |x 0 - xs| ≤ |x t - xs| := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      rw [hx n, pow_succ]
      have := hstep (x n) (hcon n)
      nlinarith [abs_nonneg (x n - xs)]
  have hpos : 0 < |x 0 - xs| := abs_pos.mpr (sub_ne_zero.mpr hx0)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / |x 0 - xs|) hk1
  have h3 : δ < k ^ n * |x 0 - xs| := by rwa [div_lt_iff₀ hpos] at hn
  linarith [hgrow n, hcon n]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Survey lemma L5 (Woodford (2003), p. 127, "local indeterminacy near `Π**`"): if
`g(x*) = x*` and `|g'(x*)| < 1`, every orbit starting within `δ` of `x*` stays within `δ` and
converges to `x*`. -/
theorem attracting_of_abs_deriv_lt_one {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : |d| < 1) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → |x 0 - xs| < δ →
      (∀ t, |x t - xs| < δ) ∧ Tendsto x atTop (𝓝 xs) := by
  have hε : 0 < (1 - |d|) / 2 := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
  set k := (|d| + 1) / 2 with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk1 : k < 1 := by rw [hk]; linarith
  have hstep : ∀ y, |y - xs| < δ → |g y - xs| ≤ k * |y - xs| := by
    intro y hy
    have h := hball (by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |g y - xs| ≤ |g y - xs - (y - xs) * d| + |(y - xs) * d| := by
      have := abs_add_le (g y - xs - (y - xs) * d) ((y - xs) * d)
      simpa using this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (y - xs)]
  have hbd : ∀ t, |x t - xs| ≤ k ^ t * |x 0 - xs| ∧ |x t - xs| < δ := by
    intro t
    induction t with
    | zero => exact ⟨by simp, hx0⟩
    | succ n ih =>
      rw [hx n]
      have h := hstep (x n) ih.2
      have hpow : k ^ (n + 1) * |x 0 - xs| = k * (k ^ n * |x 0 - xs|) := by ring
      refine ⟨by rw [hpow]; nlinarith [ih.1], ?_⟩
      nlinarith [ih.2, abs_nonneg (x n - xs)]
  refine ⟨fun t => (hbd t).2, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (hbd t).1) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x 0 - xs|

/-! ## (4.2): a Ricardian fiscal rule -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), eq. (1.8), p. 67: the opportunity cost of money
`Δ_t = (i_t − i^m_t)/(1 + i_t)`; with `i^m = 0` (as in (4.2)) it is `i/(1+i)`. -/
noncomputable def oppCost (i im : ℝ) : ℝ := (i - im) / (1 + i)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.2), p. 124: with `i^m = 0` the opportunity cost is `i/(1+i)`. -/
theorem oppCost_zero (i : ℝ) : oppCost i 0 = i / (1 + i) := by
  simp [oppCost]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), §1, p. 66: the perfect-foresight discount factor
`Q_{t,T} = ∏_{s=t}^{T-1} Q_{s,s+1}`. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.2), p. 124 with the government flow budget constraint (1.25), p. 73
(the text cites (1.7), error E9): under `T_t = αW_t − Δ_tM_t` the government budget gives
`Q_{t,t+1}W_{t+1} = (1 − α)W_t`. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.2), p. 124: iterating, `Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`. -/
theorem ricardian_discounted {q W Tx Δ M : ℕ → ℝ} {α : ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t n : ℕ) :
    discount q t (t + n) * W (t + n) = (1 - α) ^ n * W t := by
  induction n with
  | zero => simp [discount]
  | succ n ih =>
    have hd : discount q t (t + (n + 1)) = discount q t (t + n) * q (t + n) := by
      simp only [discount, ← add_assoc]
      exact Finset.prod_Ico_succ_top (Nat.le_add_right t n) q
    rw [hd, mul_assoc, ← add_assoc, ricardian_step (t + n) (hgov _) (hrule _), ← mul_assoc,
      mul_comm (discount q t (t + n)), mul_assoc, ih]
    ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.2), p. 124, "the transversality condition (1.18) necessarily holds":
for `0 < α ≤ 1`, `Q_{t,T}W_T → 0` as `T → ∞`, whatever the paths of the other variables. -/
theorem ricardian_tvc {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T => (1 - α) ^ (T - t) * W t) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - α)
      (by linarith)).comp (tendsto_sub_atTop_nat t)).mul_const (W t)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [ricardian_discounted hgov hrule t n]
  simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.2), p. 124: the hypothesis `α > 0` is needed; with `α = 0`,
`Q_{t,T}W_T = W_t` for all `T ≥ t`, so the transversality condition fails whenever `W_t ≠ 0`. -/
theorem ricardian_tvc_fails_of_alpha_zero {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 0 * W s - Δ s * M s) (t : ℕ) (hW : W t ≠ 0) :
    ¬ Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  intro h
  have hconst : Tendsto (fun T => discount q t T * W T) atTop (𝓝 (W t)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [ricardian_discounted hgov hrule t n]
    simp
  exact hW (tendsto_nhds_unique hconst h)

/-! ## (4.3) ⇒ (4.5) ⇒ (4.6) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.3) ⇔ (4.5), pp. 124–125: with constant output and no shocks the
perfect-foresight Fisher equation `1 + i_t = β⁻¹ [λ_{t+1}/λ_t · P_t/P_{t+1}]⁻¹` is equivalent to
`Π_{t+1}/λ_{t+1} = β(1 + i_t)/λ_t`, where `Π_{t+1} = P_{t+1}/P_t`. -/
theorem eq45_iff_fisher {β lt lt1 Pt Pt1 it : ℝ} (hβ : 0 < β) (hl : 0 < lt) (hl1 : 0 < lt1)
    (hP : 0 < Pt) (hP1 : 0 < Pt1) :
    (1 + it = β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹) ↔ (Pt1 / Pt) / lt1 = β * (1 + it) / lt := by
  have hβ' := hβ.ne'
  have hl' := hl.ne'
  have hl1' := hl1.ne'
  have hP' := hP.ne'
  have hP1' := hP1.ne'
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have h2 : Pt1 * lt = β * (1 + it) * lt1 * Pt := by
      rw [div_eq_div_iff (by positivity) hl', div_mul_eq_mul_div, div_eq_iff hP'] at h
      linarith
    rw [show β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹ = lt * Pt1 / (β * lt1 * Pt) by
      field_simp, eq_div_iff (by positivity)]
    linear_combination (-1 : ℝ) * h2

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), eq. (4.5), p. 125: a perfect-foresight inflation path under the rule
`i_t = φ(Π_t)`: positive inflation with
`Π_{t+1}/λ(φ(Π_{t+1})) = β(1 + φ(Π_t))/λ(φ(Π_t))` at all dates. -/
def IsPath45 (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧
    ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), eq. (4.6), p. 125: the cashless/separable dynamics
`Π_{t+1} = β(1 + φ(Π_t))` with positive inflation. -/
def IsPath46 (β : ℝ) (φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧ ∀ t, Pi_ (t + 1) = β * (1 + φ (Pi_ t))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.3) ⇒ (4.5), pp. 124–125, for whole paths: if `P > 0`,
`Π_{t+1} = P_{t+1}/P_t`, `i_t = φ(Π_t)` and `λ > 0`, the Fisher equation (4.3) at every date is
equivalent to (4.5) at every date. -/
theorem fisher_path_iff_eq45 {β : ℝ} {lam φ : ℝ → ℝ} {P Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hP : ∀ t, 0 < P t) (hPi : ∀ t, Pi_ (t + 1) = P (t + 1) / P t)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) :
    (∀ t, 1 + φ (Pi_ t) =
        β⁻¹ * ((lam (φ (Pi_ (t + 1))) / lam (φ (Pi_ t))) * (P t / P (t + 1)))⁻¹) ↔
      ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t)) := by
  refine forall_congr' fun t => ?_
  rw [show Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = (P (t + 1) / P t) / lam (φ (Pi_ (t + 1))) by
    rw [← hPi t]]
  exact eq45_iff_fisher hβ (hlam t) (hlam (t + 1)) (hP t) (hP (t + 1))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.5) ⇒ (4.6), p. 125: in the cashless limit / separable case `λ` is a
positive constant and (4.5) reduces to (4.6). -/
theorem isPath45_iff_isPath46_of_const {β c : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hc : 0 < c) :
    IsPath45 β (fun _ => c) φ Pi_ ↔ IsPath46 β φ Pi_ := by
  unfold IsPath45 IsPath46
  refine and_congr Iff.rfl (forall_congr' fun t => ?_)
  rw [div_left_inj' hc.ne']

/-! ## Existence of solutions and the bound (4.4) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), eq. (4.6), p. 125: the map `Π ↦ β(1 + φ(Π))` (the solid curve of
Figure 2.4). -/
def map46 (β : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => β * (1 + φ x)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125: the solution of (4.6) started from `Π₀`. -/
def orbit46 (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) : ℕ → ℝ := fun t => (map46 β φ)^[t] Pi0

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125: the orbit obeys (4.6). -/
theorem orbit46_succ (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) (t : ℕ) :
    orbit46 β φ Pi0 (t + 1) = map46 β φ (orbit46 β φ Pi0 t) :=
  Function.iterate_succ_apply' _ _ _

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125, "starting from any arbitrarily chosen initial inflation rate
`Π₀ > 0`, I can construct a sequence `{Π_t}` that satisfies (4.6)": for `β > 0` and `φ ≥ 0` the
orbit from any `Π₀ > 0` is a positive solution of (4.6). -/
theorem orbit46_isPath {β : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    {Pi0 : ℝ} (h0 : 0 < Pi0) : IsPath46 β φ (orbit46 β φ Pi0) := by
  have hpos : ∀ t, 0 < orbit46 β φ Pi0 t := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rw [orbit46_succ]
      have := hφ0 _ ih
      simp only [map46]
      positivity
  exact ⟨hpos, fun t => orbit46_succ β φ Pi0 t⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125: a solution of (4.6) is pinned down by its initial inflation
rate. -/
theorem isPath46_eq_orbit {β : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (h : IsPath46 β φ Pi_) :
    Pi_ = orbit46 β φ (Pi_ 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ n ih => rw [h.2 n, orbit46_succ, ih]; rfl

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), eq. (4.4), p. 124: the summand `β^T λ(i_T)[ȳ + i_T/(1+i_T) L(i_T)]`. -/
noncomputable def bound44Term (β ybar : ℝ) (lam L : ℝ → ℝ) (i : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * (lam (i T) * (ybar + i T / (1 + i T) * L (i T)))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.4), p. 125 and fn. 58: if `λ` is bounded along the path and `i L(i)` is
bounded (e.g. satiation in real balances), the bound (4.4) holds for every nonnegative interest
path: the series has nonnegative terms and converges. -/
theorem bound44_summable {β ybar Λ K : ℝ} {lam L : ℝ → ℝ} {i : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hi : ∀ T, 0 ≤ i T) (hlam0 : ∀ T, 0 < lam (i T))
    (hlamΛ : ∀ T, lam (i T) ≤ Λ) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j) (hLK : ∀ j, 0 ≤ j → j * L j ≤ K) :
    (∀ T, 0 ≤ bound44Term β ybar lam L i T) ∧ Summable (bound44Term β ybar lam L i) := by
  have hterm : ∀ T, 0 ≤ i T / (1 + i T) * L (i T) ∧ i T / (1 + i T) * L (i T) ≤ K := by
    intro T
    have h1 : 0 < 1 + i T := by linarith [hi T]
    have hL := hL0 _ (hi T)
    refine ⟨mul_nonneg (div_nonneg (hi T) h1.le) hL, ?_⟩
    have : i T / (1 + i T) * L (i T) ≤ i T * L (i T) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      nlinarith [mul_nonneg (mul_nonneg (hi T) hL) (hi T)]
    linarith [hLK _ (hi T)]
  have hnn : ∀ T, 0 ≤ bound44Term β ybar lam L i T := by
    intro T
    unfold bound44Term
    have := (hterm T).1
    have := (hlam0 T).le
    positivity
  refine ⟨hnn, Summable.of_nonneg_of_le hnn (fun T => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (Λ * (ybar + K)))⟩
  unfold bound44Term
  have hb : 0 ≤ β ^ T := pow_nonneg hβ0 T
  have h2 : lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ Λ * (ybar + K) := by
    have h3 := (hterm T).2
    have h4 := (hterm T).1
    have h5 := (hlam0 T).le
    calc lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ lam (i T) * (ybar + K) := by
          gcongr
      _ ≤ Λ * (ybar + K) := mul_le_mul_of_nonneg_right (hlamΛ T) (by linarith)
  exact mul_le_mul_of_nonneg_left h2 hb

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125, "there exists a continuum of perfect-foresight equilibria, one
corresponding to each possible initial inflation rate `Π₀`": in the separable case
(`λ ≡ c > 0`), with `φ ≥ 0` and `iL(i)` bounded, every `Π₀ > 0` starts a solution of (4.6)
whose interest path `i_t = φ(Π_t)` satisfies (4.4), and distinct `Π₀` give distinct paths. -/
theorem continuum_pf_equilibria {β ybar c K : ℝ} {φ L : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hy : 0 ≤ ybar) (hc : 0 < c) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j)
    (hLK : ∀ j, 0 ≤ j → j * L j ≤ K) :
    Set.InjOn (orbit46 β φ) (Set.Ioi 0) ∧
      ∀ Pi0, 0 < Pi0 → IsPath46 β φ (orbit46 β φ Pi0) ∧
        Summable (bound44Term β ybar (fun _ => c) L (fun t => φ (orbit46 β φ Pi0 t))) := by
  refine ⟨fun a _ b _ hab => by simpa [orbit46] using congrFun hab 0, fun Pi0 h0 => ?_⟩
  have hp := orbit46_isPath hβ0 hφ0 h0
  refine ⟨hp, (bound44_summable (Λ := c) hβ0.le hβ1 hy (fun T => hφ0 _ (hp.1 T))
    (fun _ => hc) (fun _ => le_rfl) hL0 hLK).2⟩

/-! ## Steady states -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 124: the target `Π*` with `φ(Π*) = β⁻¹Π* − 1` is a steady state of
(4.6). -/
theorem target_isFixed {β Pis : ℝ} {φ : ℝ → ℝ} (hβ : β ≠ 0) (htarget : φ Pis = Pis / β - 1) :
    map46 β φ Pis = Pis := by
  simp only [map46, htarget]
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125: the derivative of the map (4.6) is `βφ'`. -/
theorem hasDerivAt_map46 {β d x : ℝ} {φ : ℝ → ℝ} (hd : HasDerivAt φ d x) :
    HasDerivAt (map46 β φ) (β * d) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).add hd).const_mul β
  rw [zero_add] at h
  exact h

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125: the Taylor coefficient `φ_π = Π*φ'(Π*)/(1 + φ(Π*))` (the elasticity
of `1 + i` with respect to `Π` at the target) equals `βφ'(Π*)`, the slope of the curve of
Figure 2.4 at `Π*`; so "the Taylor principle" `φ_π > 1` is "the curve cuts the diagonal from
below". -/
theorem taylorCoeff_eq_slope {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : 0 < Pis)
    (htarget : φ Pis = Pis / β - 1) : Pis * d / (1 + φ Pis) = β * d := by
  rw [htarget, show 1 + (Pis / β - 1) = Pis / β by ring]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 125, "the fact that `φ(Π) ≥ 0` for all `Π` implies that there also must
be another steady state … at some lower rate of inflation. At this lower steady state, the
curve must cut the diagonal from above; thus … the Taylor principle cannot be globally valid":
under the local Taylor principle `βφ'(Π*) > 1` there is a steady state `Π** ∈ [β, Π*)` with the
curve strictly above the diagonal on `(0, Π**)`, and the Taylor principle fails weakly there
(`βφ'(Π**) ≤ 1` whenever `φ` is differentiable at `Π**`). -/
theorem second_steady_state {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : β < Pis)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ Pss, β ≤ Pss ∧ Pss < Pis ∧ map46 β φ Pss = Pss ∧
      (∀ x, 0 < x → x < Pss → x < map46 β φ x) ∧
      (∀ d', HasDerivAt φ d' Pss → β * d' ≤ 1) := by
  set f : ℝ → ℝ := fun x => map46 β φ x - x with hf
  have hfd : ∀ {x e}, HasDerivAt φ e x → HasDerivAt f (β * e - 1) x :=
    fun h => (hasDerivAt_map46 h).sub (hasDerivAt_id _)
  have hfPis : f Pis = 0 := by simp [hf, target_isFixed hβ.ne' htarget]
  have hfcont : ∀ a b, 0 < a → ContinuousOn f (Set.Icc a b) := by
    intro a b ha
    have hφc : ContinuousOn φ (Set.Icc a b) :=
      hcont.mono fun y hy => lt_of_lt_of_le ha hy.1
    exact (continuousOn_const.mul (continuousOn_const.add hφc)).sub continuousOn_id
  have hfβ : 0 ≤ f β := by
    simp only [hf, map46]
    nlinarith [hφ0 β hβ]
  -- a point just left of `Π*` where the curve is below the diagonal
  obtain ⟨δ, hδ, hleft, -⟩ := sign_near_of_deriv_pos (hfd hd) (by linarith)
  set y1 := max β (Pis - δ / 2) with hy1
  have hy1lt : y1 < Pis := max_lt hPis (by linarith)
  have hfy1 : f y1 < 0 := by
    have := hleft y1 (by rw [hy1]; exact lt_max_of_lt_right (by linarith)) hy1lt
    rwa [hfPis] at this
  have hβy1 : β ≤ y1 := le_max_left _ _
  set S := Set.Icc β y1 ∩ f ⁻¹' {0} with hS
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hβy1 (hfcont β y1 hβ) ⟨hfy1.le, hfβ⟩
    exact ⟨c, hc, hfc⟩
  have hSclosed : IsClosed S :=
    (hfcont β y1 hβ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddBelow S := ⟨β, fun z hz => hz.1.1⟩
  have hmem := hSclosed.csInf_mem hSne hSbdd
  set Pss := sInf S with hPss
  have hPssβ : β ≤ Pss := hmem.1.1
  have hPssfix : f Pss = 0 := hmem.2
  have habove : ∀ x, 0 < x → x < Pss → x < map46 β φ x := by
    intro x hx0 hxP
    by_cases hxβ : x < β
    · simp only [map46]
      nlinarith [hφ0 x hx0]
    · push Not at hxβ
      by_contra hcon
      push Not at hcon
      have hfx : f x ≤ 0 := by simp only [hf]; linarith
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hxβ (hfcont β x hβ) ⟨hfx, hfβ⟩
      have hcS : c ∈ S := ⟨⟨hc.1, by linarith [hc.2, hmem.1.2]⟩, hfc⟩
      have := csInf_le hSbdd hcS
      linarith [hc.2]
  refine ⟨Pss, hPssβ, by linarith [hmem.1.2], by simpa [hf, sub_eq_zero] using hPssfix,
    habove, fun d' hd' => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hl, -⟩ := sign_near_of_deriv_pos (hfd hd') (by linarith)
  set y := max (Pss / 2) (Pss - ε / 2) with hy
  have hPss0 : 0 < Pss := by linarith
  have hyP : y < Pss := max_lt (by linarith) (by linarith)
  have hy0 : 0 < y := lt_max_of_lt_left (by linarith)
  have h1 := hl y (lt_max_of_lt_right (by linarith)) hyP
  have h2 := habove y hy0 hyP
  simp only [hf] at h1 hPssfix
  linarith

/-! ## Self-fulfilling deflations (Figure 2.4) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 126: under `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, the map (4.6)
sends `[β, Π*)` into itself, weakly downward. -/
theorem map46_step_down {β Pis x : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis) :
    β ≤ map46 β φ x ∧ map46 β φ x ≤ x := by
  simp only [map46]
  refine ⟨by nlinarith [hφ0 x (by linarith)], ?_⟩
  rcases hx.lt_or_eq with hlt | heq
  · have h := hbelow x hlt hxP
    have : β * φ x < β * (x / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ x hβ.ne'] at this
    linarith
  · rw [← heq, hφβ]; simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 126, Figure 2.4, "a self-fulfilling deflation": if `φ ≥ 0` is continuous,
`φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, every solution of (4.6) starting in `(β, Π*)` is
nonincreasing, stays in `[β, Π₀]` and converges to the Friedman rate `Π** = β`. -/
theorem self_fulfilling_deflation46 {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath46 β φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := map46_step_down hβ hφ0 hφβ hbelow h0.1.le h0.2
      exact ⟨h0.1.le, le_rfl, by rw [hpath.2 0]; exact this.2⟩
    | succ n ih =>
      have hb : β ≤ Pi_ (n + 1) := by
        rw [hpath.2 n]
        exact (map46_step_down hβ hφ0 hφβ hbelow ih.1 (by linarith [h0.2, ih.2.1])).1
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      refine ⟨hb, hle, ?_⟩
      rw [hpath.2 (n + 1)]
      exact (map46_step_down hβ hφ0 hφβ hbelow hb (by linarith [h0.2])).2
  have hanti : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti, fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hcontL : ContinuousAt (map46 β φ) L := by
    have : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds (by linarith))
    exact continuousAt_const.mul (continuousAt_const.add this)
  have hfix := fixed_of_tendsto hpath.2 hlim hcontL
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have := (map46_step_down hβ hφ0 hφβ hbelow hLβ (by linarith [h0.2])).2
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 126: if moreover `φ > 0` on `(β, Π*)`, inflation declines strictly
monotonically and never reaches `β` ("approaching the value `Π** = β` asymptotically"). -/
theorem deflation46_strictAnti {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hφpos : ∀ x, β < x → x < Pis → 0 < φ x)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath46 β φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) : StrictAnti Pi_ ∧ ∀ t, β < Pi_ t := by
  have hstep : ∀ t, β < Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) < Pi_ t := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0.1, le_rfl, ?_⟩
      have h := hbelow _ h0.1 h0.2
      have : β * φ (Pi_ 0) < β * (Pi_ 0 / β - 1) := mul_lt_mul_of_pos_left h hβ
      rw [mul_sub, mul_div_cancel₀ _ hβ.ne'] at this
      rw [hpath.2 0]; linarith
    | succ n ih =>
      have hb : β < Pi_ (n + 1) := by
        rw [hpath.2 n]
        have := hφpos _ ih.1 (by linarith [h0.2, ih.2.1])
        nlinarith
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2.le ih.2.1
      refine ⟨hb, hle, ?_⟩
      have h := hbelow _ hb (by linarith [h0.2])
      have : β * φ (Pi_ (n + 1)) < β * (Pi_ (n + 1) / β - 1) := mul_lt_mul_of_pos_left h hβ
      rw [mul_sub, mul_div_cancel₀ _ hβ.ne'] at this
      rw [hpath.2 (n + 1)]; linarith
  exact ⟨strictAnti_nat_of_succ_lt fun t => (hstep t).2.2, fun t => (hstep t).1⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 126, "eventually, actual deflation": with `β < 1`, inflation along a
self-fulfilling deflation is eventually below one. -/
theorem deflation46_eventually_deflation {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1)
    (hpath : IsPath46 β φ Pi_) (h0 : Pi_ 0 ∈ Set.Ioo β Pis) : ∀ᶠ t in atTop, Pi_ t < 1 :=
  (self_fulfilling_deflation46 hβ hφ0 hcont hφβ hbelow hpath h0).2.2.eventually
    (gt_mem_nhds hβ1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, "equilibrium is indeterminate even locally, near the
deflationary steady state; for any neighborhood of `Π**`, there exists a continuum of distinct
equilibria in which inflation remains forever within this range": for every `ε > 0` each
`Π₀ ∈ (β, min(Π*, β + ε))` starts a solution of (4.6) that stays within `ε` of `β`, and distinct
`Π₀` give distinct solutions. -/
theorem deflationary_steady_state_indeterminate {β Pis : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hPis : β < Pis) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {ε : ℝ} (hε : 0 < ε) :
    (Set.Ioo β (min Pis (β + ε))).Nonempty ∧
      Set.InjOn (orbit46 β φ) (Set.Ioo β (min Pis (β + ε))) ∧
      ∀ Pi0 ∈ Set.Ioo β (min Pis (β + ε)),
        IsPath46 β φ (orbit46 β φ Pi0) ∧ ∀ t, |orbit46 β φ Pi0 t - β| < ε := by
  refine ⟨⟨(β + min Pis (β + ε)) / 2, by
      constructor <;> linarith [lt_min hPis (by linarith : β < β + ε)]⟩,
    fun a _ b _ hab => by simpa [orbit46] using congrFun hab 0, fun Pi0 hP => ?_⟩
  have h1 : Pi0 < Pis := lt_of_lt_of_le hP.2 (min_le_left _ _)
  have h2 : Pi0 < β + ε := lt_of_lt_of_le hP.2 (min_le_right _ _)
  have hp := orbit46_isPath hβ hφ0 (by linarith [hP.1] : 0 < Pi0)
  refine ⟨hp, fun t => ?_⟩
  have hd := self_fulfilling_deflation46 hβ hφ0 hcont hφβ hbelow hp
    (by simpa [orbit46] using (⟨hP.1, h1⟩ : Pi0 ∈ Set.Ioo β Pis))
  have hb := hd.2.1 t
  have h00 : orbit46 β φ Pi0 0 = Pi0 := rfl
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-! ## Self-fulfilling inflations (error E6) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, corrected (error E6): if `φ(Π) > β⁻¹Π − 1` for every `Π > Π*`
(no steady state above the target) and `φ` is continuous, every solution of (4.6) starting
above `Π*` is strictly increasing and grows without bound. -/
theorem inflation_unbounded46 {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (habove : ∀ x, Pis < x → x / β - 1 < φ x)
    (hpath : IsPath46 β φ Pi_) (h0 : Pis < Pi_ 0) :
    StrictMono Pi_ ∧ Tendsto Pi_ atTop atTop := by
  have hup : ∀ x, Pis < x → x < map46 β φ x := by
    intro x hx
    have : β * (x / β - 1) < β * φ x := mul_lt_mul_of_pos_left (habove x hx) hβ
    rw [mul_sub, mul_div_cancel₀ x hβ.ne'] at this
    simp only [map46]; linarith
  have hstep : ∀ t, Pis < Pi_ t ∧ Pi_ t < Pi_ (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hpath.2 0]; exact hup _ h0⟩
    | succ n ih =>
      have h1 : Pis < Pi_ (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hpath.2 (n + 1)]; exact hup _ h1⟩
  have hsm : StrictMono Pi_ := strictMono_nat_of_lt_succ fun t => (hstep t).2
  refine ⟨hsm, ?_⟩
  rcases monotone_orbit_atTop_or_fixed (g := map46 β φ) hpath.2 hsm.monotone with
    h | ⟨L, hL, hbd, hfix⟩
  · exact h
  · exfalso
    have hL0 : Pi_ 0 ≤ L := hbd 0
    have hcL : ContinuousAt (map46 β φ) L :=
      continuousAt_const.mul (continuousAt_const.add
        (hcont.continuousAt (Ioi_mem_nhds (by linarith [hpath.1 0]))))
    have hf := hfix hcL
    have hu := hup L (by linarith)
    simp only [map46] at hf hu
    linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, error E6, exact form: under continuity, `φ ≥ 0`, the target
condition and the local Taylor principle `βφ'(Π*) > 1`, *every* solution of (4.6) starting
above `Π*` grows without bound if and only if (4.6) has no steady state above `Π*`. -/
theorem inflation_unbounded_iff {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : 0 < Pis)
    (hcont : ContinuousOn φ (Set.Ioi 0))
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    (∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → Pis < Pi_ 0 → Tendsto Pi_ atTop atTop) ↔
      ∀ x, Pis < x → map46 β φ x ≠ x := by
  constructor
  · intro h x hx hfix
    have hp : IsPath46 β φ (fun _ => x) := ⟨fun _ => by linarith, fun _ => hfix.symm⟩
    have := (h _ hp hx).eventually (eventually_ge_atTop (x + 1))
    obtain ⟨t, ht⟩ := this.exists
    linarith
  · intro hno Pi_ hp h0
    set f : ℝ → ℝ := fun x => map46 β φ x - x with hf
    have hfd : HasDerivAt f (β * d - 1) Pis := (hasDerivAt_map46 hd).sub (hasDerivAt_id _)
    have hfPis : f Pis = 0 := by simp [hf, target_isFixed hβ.ne' htarget]
    obtain ⟨δ, hδ, -, hright⟩ := sign_near_of_deriv_pos hfd (by linarith)
    have habove : ∀ x, Pis < x → x / β - 1 < φ x := by
      intro x hx
      have hfx : 0 < f x := by
        by_contra hcon
        push Not at hcon
        have hne : f x ≠ 0 := by simp only [hf]; exact sub_ne_zero.mpr (hno x hx)
        have hneg : f x < 0 := lt_of_le_of_ne hcon hne
        set y := min (Pis + δ / 2) ((Pis + x) / 2) with hy
        have hyP : Pis < y := lt_min (by linarith) (by linarith)
        have hyx : y ≤ x := le_trans (min_le_right _ _) (by linarith)
        have hfy : 0 < f y := by
          have := hright y hyP (lt_of_le_of_lt (min_le_left _ _) (by linarith))
          rwa [hfPis] at this
        have hfc : ContinuousOn f (Set.Icc y x) := by
          have hφc : ContinuousOn φ (Set.Icc y x) :=
            hcont.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z)
          exact (continuousOn_const.mul (continuousOn_const.add hφc)).sub continuousOn_id
        obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hyx hfc ⟨hneg.le, hfy.le⟩
        exact hno c (by linarith [hc.1]) (by simpa [hf, sub_eq_zero] using hfc0)
      simp only [hf, map46] at hfx
      have : x < β * (1 + φ x) := by linarith
      rw [div_sub_one hβ.ne', div_lt_iff₀ hβ]
      linarith
    exact (inflation_unbounded46 hβ hcont habove hp h0).2

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, error E6: the policy function of the counterexample,
`φ(Π) = max(0, min(3Π − 2, 2))` (with `β = 1/2`, `Π* = 1`): it saturates at `2`, so the curve of
Figure 2.4 crosses the diagonal again at `Π = 3/2`. -/
noncomputable def phiCE (x : ℝ) : ℝ := max 0 (min (3 * x - 2) 2)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, error E6, counterexample: `φ = phiCE` is continuous, increasing and
nonnegative, hits the target `φ(Π*) = β⁻¹Π* − 1` at `Π* = 1` with `β = 1/2`, satisfies the Taylor
principle there (`βφ'(Π*) = 3/2 > 1`), and yet the constant path `Π_t = 3/2 > Π*` solves (4.6):
inflation above target need not rise, let alone without bound. -/
theorem e6_counterexample :
    Continuous phiCE ∧ Monotone phiCE ∧ (∀ x, 0 ≤ phiCE x) ∧ phiCE 1 = 1 / (1 / 2) - 1 ∧
      HasDerivAt phiCE 3 1 ∧ 1 < (1 / 2 : ℝ) * 3 ∧
      IsPath46 (1 / 2) phiCE (fun _ => 3 / 2) ∧ (1 : ℝ) < 3 / 2 ∧
      ¬ Tendsto (fun _ : ℕ => (3 / 2 : ℝ)) atTop atTop := by
  refine ⟨by unfold phiCE; fun_prop, ?_, fun x => le_max_left _ _, ?_, ?_, by norm_num,
    ⟨fun _ => by norm_num, fun _ => ?_⟩, by norm_num, ?_⟩
  · intro a b hab
    unfold phiCE
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · unfold phiCE; norm_num
  · have h : HasDerivAt (fun x : ℝ => 3 * x - 2) 3 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 3).sub_const 2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 4 / 3)] with x hx
    unfold phiCE
    rw [min_eq_left (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
  · unfold phiCE; norm_num
  · intro h
    obtain ⟨t, ht⟩ := (h.eventually (eventually_ge_atTop (2 : ℝ))).exists
    norm_num at ht

/-! ## Local repulsion at the target -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, "any deterministic equilibrium other than the one with `Π_t = Π*`
forever involves an inflation rate that diverges further and further from the target …
every other equilibrium eventually leaves a neighborhood of `Π*`": under the local Taylor
principle `βφ'(Π*) > 1` there is `δ > 0` such that every solution of (4.6) with `Π₀ ≠ Π*` is at
some date at distance at least `δ` from `Π*`. -/
theorem target_locally_repelling {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ δ > 0, ∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → Pi_ 0 ≠ Pis → ∃ t, δ ≤ |Pi_ t - Pis| := by
  obtain ⟨δ, hδ, h⟩ := repelling_of_one_lt_abs_deriv (target_isFixed hβ.ne' htarget)
    (hasDerivAt_map46 hd) (by rw [abs_of_pos (by linarith)]; exact htaylor)
  exact ⟨δ, hδ, fun Pi_ hp h0 => h Pi_ hp.2 h0⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127: consequently, under the local Taylor principle, the only solution
of (4.6) that remains forever in a small enough neighbourhood of `Π*` is `Π_t ≡ Π*`
(local determinacy). -/
theorem target_locally_unique {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ δ > 0, ∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → (∀ t, |Pi_ t - Pis| < δ) → ∀ t, Pi_ t = Pis := by
  obtain ⟨δ, hδ, h⟩ := target_locally_repelling hβ htarget hd htaylor
  refine ⟨δ, hδ, fun Pi_ hp hin => ?_⟩
  have h0 : Pi_ 0 = Pis := by
    by_contra hne
    obtain ⟨t, ht⟩ := h Pi_ hp hne
    linarith [hin t]
  intro t
  rw [isPath46_eq_orbit hp, h0]
  induction t with
  | zero => rfl
  | succ n ih => rw [orbit46_succ, ih, target_isFixed hβ.ne' htarget]

/-! ## Real-balance effects: (4.5) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, "in the case that real balances are complementary with private
expenditure (`u_cm > 0`) … `λ(i)` is a decreasing function, and this condition is necessarily
satisfied": if `λ > 0` is nonincreasing on `[0, ∞)` and `φ ≥ 0` is nondecreasing, then
`Π ↦ Π/λ(φ(Π))` is strictly increasing on `(0, ∞)`. -/
theorem ratio_strictMonoOn {lam φ : ℝ → ℝ} (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) :
    StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hφab : φ a ≤ φ b := hmono ha hb hab.le
  have hl : lam (φ b) ≤ lam (φ a) :=
    hanti (Set.mem_Ici.mpr (hφ0 a ha')) (Set.mem_Ici.mpr (hφ0 b hb')) hφab
  have hla := hlam _ (hφ0 a ha')
  have hlb := hlam _ (hφ0 b hb')
  calc a / lam (φ a) < b / lam (φ a) := div_lt_div_of_pos_right hab hla
    _ ≤ b / lam (φ b) := div_le_div_of_nonneg_left hb'.le hlb hl

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.5), p. 127: the steady states of (4.5) are those of (4.6), since `λ`
cancels at a constant inflation rate. -/
theorem steady_state45_iff {β x : ℝ} {lam φ : ℝ → ℝ} (hl : 0 < lam (φ x)) :
    x / lam (φ x) = β * (1 + φ x) / lam (φ x) ↔ map46 β φ x = x := by
  rw [div_left_inj' hl.ne', map46, eq_comm]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127: when `Π/λ(φ(Π))` is strictly increasing, a solution of (4.5) is
pinned down by its initial inflation rate. -/
theorem isPath45_unique {β : ℝ} {lam φ : ℝ → ℝ} {Pi_ Pi' : ℕ → ℝ}
    (hinj : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0)) (h1 : IsPath45 β lam φ Pi_)
    (h2 : IsPath45 β lam φ Pi') (h0 : Pi_ 0 = Pi' 0) : Pi_ = Pi' := by
  funext t
  induction t with
  | zero => exact h0
  | succ n ih =>
    have e1 := h1.2 n
    have e2 := h2.2 n
    rw [ih] at e1
    refine hinj.injOn (h1.1 (n + 1)) (h2.1 (n + 1)) ?_
    show Pi_ (n + 1) / lam (φ (Pi_ (n + 1))) = Pi' (n + 1) / lam (φ (Pi' (n + 1)))
    rw [e1, e2]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127: under `λ > 0` nonincreasing, `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on
`(β, Π*)`, the successor `Π'` of any `Π ∈ [β, Π*)` under (4.5) lies in `[β, Π]`. -/
theorem step45_down {β Pis x y : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis)
    (hy : 0 < y) (heq : y / lam (φ y) = β * (1 + φ x) / lam (φ x)) : β ≤ y ∧ y ≤ x := by
  have hsm := ratio_strictMonoOn hlam hanti hmono hφ0
  have hx0 : 0 < x := by linarith
  have hφx := hφ0 x hx0
  have hlx := hlam _ hφx
  have hdown := map46_step_down hβ hφ0 hφβ hbelow hx hxP
  have hl0 : lam (φ x) ≤ lam 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hφx) hφx
  have hlam0 := hlam 0 le_rfl
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : y / lam (φ y) < β / lam (φ β) := hsm hy hβ hcon
    rw [hφβ, heq] at h1
    have h2 : β / lam 0 ≤ β / lam (φ x) := div_le_div_of_nonneg_left hβ.le hlx hl0
    have h3 : β / lam (φ x) ≤ β * (1 + φ x) / lam (φ x) :=
      div_le_div_of_nonneg_right (by nlinarith) hlx.le
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : x / lam (φ x) < y / lam (φ y) := hsm hx0 hy hcon
    rw [heq] at h1
    have h2 : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
      div_le_div_of_nonneg_right hdown.2 hlx.le
    linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, "this suffices to imply the existence of a continuum of solutions
to (4.5) involving self-fulfilling deflation" (convergence part): if `λ > 0` is continuous and
nonincreasing on `[0, ∞)`, `φ ≥ 0` is continuous and nondecreasing, `φ(β) = 0` and
`φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, every solution of (4.5) starting in `(β, Π*)` is nonincreasing,
stays in `[β, Π₀]` and converges to `β`. -/
theorem self_fulfilling_deflation45 {β Pis : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h0.1.le h0.2 (hpath.1 1)
        (hpath.2 0)
      exact ⟨h0.1.le, le_rfl, this.2⟩
    | succ n ih =>
      have h1 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow ih.1
        (by linarith [h0.2, ih.2.1]) (hpath.1 (n + 1)) (hpath.2 n)
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      have h2 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h1.1
        (by linarith [h0.2]) (hpath.1 (n + 1 + 1)) (hpath.2 (n + 1))
      exact ⟨h1.1, hle, h2.2⟩
  have hanti' : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti', fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hLpos : 0 < L := by linarith
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hlcL : ContinuousAt (fun x => lam (φ x)) L := hlc.continuousAt (Ioi_mem_nhds hLpos)
  have hφcL : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds hLpos)
  have hlL := hlam _ (hφ0 L hLpos)
  have hhc : ContinuousAt (fun x => x / lam (φ x)) L := continuousAt_id.div hlcL hlL.ne'
  have hRc : ContinuousAt (fun x => β * (1 + φ x) / lam (φ x)) L :=
    (continuousAt_const.mul (continuousAt_const.add hφcL)).div hlcL hlL.ne'
  have hA : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (L / lam (φ L))) :=
    hhc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hB : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (β * (1 + φ L) / lam (φ L))) := by
    have : (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) =
        (fun x => β * (1 + φ x) / lam (φ x)) ∘ Pi_ := funext fun t => hpath.2 t
    rw [this]
    exact hRc.tendsto.comp hlim
  have hfix : map46 β φ L = L := (steady_state45_iff hlL).mp (tendsto_nhds_unique hA hB)
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127 (existence part): under the hypotheses of
`self_fulfilling_deflation45`, every `Π₀ ∈ (β, Π*)` starts a solution of (4.5); with
`isPath45_unique` this is a continuum of self-fulfilling deflations indexed by `Π₀`. -/
theorem deflation45_exists {β Pis : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {Pi0 : ℝ} (h0 : Pi0 ∈ Set.Ioo β Pis) :
    ∃ Pi_ : ℕ → ℝ, IsPath45 β lam φ Pi_ ∧ Pi_ 0 = Pi0 := by
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Ico β Pis →
      y ∈ Set.Icc β x ∧ y / lam (φ y) = β * (1 + φ x) / lam (φ x) := by
    intro x
    by_cases hx : x ∈ Set.Ico β Pis
    · have hx0 : 0 < x := by linarith [hx.1]
      have hφx := hφ0 x hx0
      have hlx := hlam _ hφx
      have hl0 : lam (φ x) ≤ lam 0 :=
        hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hφx) hφx
      have hdown := map46_step_down hβ hφ0 hφβ hbelow hx.1 hx.2
      have hcI : ContinuousOn (fun z => z / lam (φ z)) (Set.Icc β x) := by
        refine continuousOn_id.div (hlc.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z))
          fun z hz => (hlam _ (hφ0 z (by linarith [hz.1]))).ne'
      have hlo : β / lam (φ β) ≤ β * (1 + φ x) / lam (φ x) := by
        rw [hφβ]
        calc β / lam 0 ≤ β / lam (φ x) := div_le_div_of_nonneg_left hβ.le hlx hl0
          _ ≤ β * (1 + φ x) / lam (φ x) := div_le_div_of_nonneg_right (by nlinarith) hlx.le
      have hhi : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
        div_le_div_of_nonneg_right hdown.2 hlx.le
      obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx.1 hcI ⟨hlo, hhi⟩
      exact ⟨y, fun _ => ⟨hy, hyeq⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set Pi_ : ℕ → ℝ := fun t => g^[t] Pi0 with hPi
  have hsuccP : ∀ t, Pi_ (t + 1) = g (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ t, Pi_ t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, h0.2⟩
    | succ n ih =>
      rw [hsuccP]
      have := (hg _ ih).1
      exact ⟨this.1, lt_of_le_of_lt this.2 ih.2⟩
  refine ⟨Pi_, ⟨fun t => by linarith [(hmem t).1], fun t => ?_⟩, rfl⟩
  rw [hsuccP]
  exact (hg _ (hmem t)).2

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), pp. 127–128, "these solutions also satisfy (4.4) … as long as `iL(ȳ, i; 0)`
has a finite bound": along a self-fulfilling deflation of (4.5) with `λ` nonincreasing, the
interest path `i_t = φ(Π_t)` satisfies (4.4), because `λ(i_t) ≤ λ(0)`. -/
theorem deflation45_bound44 {β ybar K : ℝ} {lam φ L : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j) (hLK : ∀ j, 0 ≤ j → j * L j ≤ K)
    (hpath : IsPath45 β lam φ Pi_) :
    Summable (bound44Term β ybar lam L (fun t => φ (Pi_ t))) :=
  (bound44_summable (Λ := lam 0) hβ.le hβ1 hy (fun T => hφ0 _ (hpath.1 T))
    (fun T => hlam _ (hφ0 _ (hpath.1 T)))
    (fun T => hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (hφ0 _ (hpath.1 T)))
      (hφ0 _ (hpath.1 T))) hL0 hLK).2

/-! ## Real-balance effects without `λ` decreasing ("not too strongly increasing") -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, fn. 61, "it suffices that `λ` not be too strongly increasing in
`i`": the two conditions used. (H1) `Π ↦ Π/λ(φ(Π))` is strictly increasing on `(0, ∞)` (the text's
monotonicity condition); (H2) `λ(i) ≤ (1 + i)λ(0)` for `i ≥ 0` (implied by an elasticity of `λ`
with respect to `1 + i` of at most one). Under them the successor of `Π ∈ [β, Π*)` lies in
`[β, Π]`. -/
theorem step45_down_gen {β Pis x y : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x)
    (hxP : x < Pis) (hy : 0 < y) (heq : y / lam (φ y) = β * (1 + φ x) / lam (φ x)) :
    β ≤ y ∧ y ≤ x := by
  have hx0 : 0 < x := by linarith
  have hφx := hφ0 x hx0
  have hlx := hlam _ hφx
  have hlam0 := hlam 0 le_rfl
  have hdown := map46_step_down hβ hφ0 hφβ hbelow hx hxP
  have hR : β / lam 0 ≤ β * (1 + φ x) / lam (φ x) := by
    rw [div_le_div_iff₀ hlam0 hlx]
    have := hgrow _ hφx
    nlinarith
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : y / lam (φ y) < β / lam (φ β) := hsm hy hβ hcon
    rw [hφβ, heq] at h1
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : x / lam (φ x) < y / lam (φ y) := hsm hx0 hy hcon
    rw [heq] at h1
    have h2 : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
      div_le_div_of_nonneg_right hdown.2 hlx.le
    linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127 and fn. 61, the "not too strongly increasing" variant of the
self-fulfilling deflation result for (4.5): with `λ > 0` continuous on `[0, ∞)`, `φ ≥ 0`
continuous, `φ(β) = 0`, `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, and the conditions (H1), (H2) of
`step45_down_gen` (no monotonicity of `λ` assumed), every solution of (4.5) starting in
`(β, Π*)` is nonincreasing, stays in `[β, Π₀]` and converges to `β`. -/
theorem self_fulfilling_deflation45_gen {β Pis : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hβ : 0 < β) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow h0.1.le h0.2 (hpath.1 1)
        (hpath.2 0)
      exact ⟨h0.1.le, le_rfl, this.2⟩
    | succ n ih =>
      have h1 := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow ih.1
        (by linarith [h0.2, ih.2.1]) (hpath.1 (n + 1)) (hpath.2 n)
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      have h2 := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow h1.1
        (by linarith [h0.2]) (hpath.1 (n + 1 + 1)) (hpath.2 (n + 1))
      exact ⟨h1.1, hle, h2.2⟩
  have hanti' : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti', fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hLpos : 0 < L := by linarith
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hlcL : ContinuousAt (fun x => lam (φ x)) L := hlc.continuousAt (Ioi_mem_nhds hLpos)
  have hφcL : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds hLpos)
  have hlL := hlam _ (hφ0 L hLpos)
  have hhc : ContinuousAt (fun x => x / lam (φ x)) L := continuousAt_id.div hlcL hlL.ne'
  have hRc : ContinuousAt (fun x => β * (1 + φ x) / lam (φ x)) L :=
    (continuousAt_const.mul (continuousAt_const.add hφcL)).div hlcL hlL.ne'
  have hA : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (L / lam (φ L))) :=
    hhc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hB : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (β * (1 + φ L) / lam (φ L))) := by
    have : (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) =
        (fun x => β * (1 + φ x) / lam (φ x)) ∘ Pi_ := funext fun t => hpath.2 t
    rw [this]
    exact hRc.tendsto.comp hlim
  have hfix : map46 β φ L = L := (steady_state45_iff hlL).mp (tendsto_nhds_unique hA hB)
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127 and fn. 61 (existence part of the "not too strongly increasing"
variant): under (H2) and continuity, every `Π₀ ∈ (β, Π*)` starts a solution of (4.5) (unique
under (H1), by `isPath45_unique`). -/
theorem deflation45_exists_gen {β Pis : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0)
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {Pi0 : ℝ} (h0 : Pi0 ∈ Set.Ioo β Pis) :
    ∃ Pi_ : ℕ → ℝ, IsPath45 β lam φ Pi_ ∧ Pi_ 0 = Pi0 := by
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Ico β Pis →
      y ∈ Set.Icc β x ∧ y / lam (φ y) = β * (1 + φ x) / lam (φ x) := by
    intro x
    by_cases hx : x ∈ Set.Ico β Pis
    · have hx0 : 0 < x := by linarith [hx.1]
      have hφx := hφ0 x hx0
      have hlx := hlam _ hφx
      have hlam0 := hlam 0 le_rfl
      have hdown := map46_step_down hβ hφ0 hφβ hbelow hx.1 hx.2
      have hcI : ContinuousOn (fun z => z / lam (φ z)) (Set.Icc β x) := by
        refine continuousOn_id.div (hlc.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z))
          fun z hz => (hlam _ (hφ0 z (by linarith [hz.1]))).ne'
      have hlo : β / lam (φ β) ≤ β * (1 + φ x) / lam (φ x) := by
        rw [hφβ, div_le_div_iff₀ hlam0 hlx]
        have := hgrow _ hφx
        nlinarith
      have hhi : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
        div_le_div_of_nonneg_right hdown.2 hlx.le
      obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx.1 hcI ⟨hlo, hhi⟩
      exact ⟨y, fun _ => ⟨hy, hyeq⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set Pi_ : ℕ → ℝ := fun t => g^[t] Pi0 with hPi
  have hsuccP : ∀ t, Pi_ (t + 1) = g (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ t, Pi_ t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, h0.2⟩
    | succ n ih =>
      rw [hsuccP]
      have := (hg _ ih).1
      exact ⟨this.1, lt_of_le_of_lt this.2 ih.2⟩
  refine ⟨Pi_, ⟨fun t => by linarith [(hmem t).1], fun t => ?_⟩, rfl⟩
  rw [hsuccP]
  exact (hg _ (hmem t)).2

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127: the case `u_cm > 0` (`λ` nonincreasing, `φ` nondecreasing) satisfies
the conditions (H1), (H2) of the general variant. -/
theorem antitone_lam_gives_gen {lam φ : ℝ → ℝ} (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) :
    StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0) ∧
      ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0 := by
  refine ⟨ratio_strictMonoOn hlam hanti hmono hφ0, fun j hj => ?_⟩
  have h1 : lam j ≤ lam 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hj) hj
  nlinarith [hlam 0 le_rfl]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127: the policy rule of the counterexample showing that some restriction
on how strongly `λ` increases is needed: `φ(Π) = max(0, 3Π − 2)` (`β = 1/2`, `Π* = 1`). -/
noncomputable def phiCE45 (x : ℝ) : ℝ := max 0 (3 * x - 2)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), p. 127, "it suffices that `λ` not be too strongly increasing": some such
restriction is needed. With `β = 1/2`, `Π* = 1`, `φ = phiCE45` (continuous, nondecreasing,
`≥ 0`, `φ(β) = 0`, `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, `φ(Π*) = β⁻¹Π* − 1`) and the increasing
`λ(i) = 1 + i` (positive, continuous, satisfying (H2) with equality), `Π/λ(φ(Π))` is not
increasing (it takes the value `1/2` at both `β` and `Π*`), and the path `Π₀ = 3/5 ∈ (β, Π*)`,
`Π_t = 1` for `t ≥ 1` solves (4.5) but does not converge to `β` (it is not a self-fulfilling
deflation). -/
theorem deflation45_counterexample :
    Continuous phiCE45 ∧ Monotone phiCE45 ∧ (∀ x, 0 ≤ phiCE45 x) ∧ phiCE45 (1 / 2) = 0 ∧
      (∀ x, 1 / 2 < x → x < 1 → phiCE45 x < x / (1 / 2) - 1) ∧
      phiCE45 1 = 1 / (1 / 2) - 1 ∧
      (∀ j : ℝ, 0 ≤ j → 0 < 1 + j ∧ 1 + j ≤ (1 + j) * (1 + 0)) ∧
      (1 / 2) / (1 + phiCE45 (1 / 2)) = 1 / (1 + phiCE45 1) ∧
      IsPath45 (1 / 2) (fun i => 1 + i) phiCE45 (fun t => if t = 0 then 3 / 5 else 1) ∧
      ¬ Tendsto (fun t : ℕ => if t = 0 then (3 / 5 : ℝ) else 1) atTop (𝓝 (1 / 2)) := by
  have h35 : phiCE45 (3 / 5) = 0 := by unfold phiCE45; norm_num
  have h1 : phiCE45 1 = 1 := by unfold phiCE45; norm_num
  refine ⟨by unfold phiCE45; fun_prop, fun a b hab => max_le_max le_rfl (by linarith),
    fun x => le_max_left _ _, by unfold phiCE45; norm_num, fun x hx1 hx2 => ?_,
    by rw [h1]; norm_num,
    fun j hj => ⟨by linarith, by linarith⟩, by unfold phiCE45; norm_num,
    ⟨fun t => by
      change (0 : ℝ) < if t = 0 then 3 / 5 else 1
      split_ifs <;> norm_num, fun t => ?_⟩, ?_⟩
  · unfold phiCE45
    exact max_lt (by linarith) (by linarith)
  · rcases t with _ | t
    · norm_num [h1, h35]
    · norm_num [h1]
  · intro h
    have h2 : Tendsto (fun t : ℕ => if t = 0 then (3 / 5 : ℝ) else 1) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht' : t ≠ 0 := by omega
      simp [ht']
    have := tendsto_nhds_unique h h2
    norm_num at this

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), (4.4), p. 124, path-wise version: if along the interest path `λ(i_T) ≤ Λ`,
`L(i_T) ≥ 0` and `i_T L(i_T) ≤ K`, the series in (4.4) has nonnegative terms and converges. -/
theorem bound44_summable_path {β ybar Λ K : ℝ} {lam L : ℝ → ℝ} {i : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hi : ∀ T, 0 ≤ i T) (hlam0 : ∀ T, 0 < lam (i T))
    (hlamΛ : ∀ T, lam (i T) ≤ Λ) (hL0 : ∀ T, 0 ≤ L (i T)) (hLK : ∀ T, i T * L (i T) ≤ K) :
    Summable (bound44Term β ybar lam L i) := by
  have hterm : ∀ T, 0 ≤ i T / (1 + i T) * L (i T) ∧ i T / (1 + i T) * L (i T) ≤ K := by
    intro T
    have h1 : 0 < 1 + i T := by linarith [hi T]
    refine ⟨mul_nonneg (div_nonneg (hi T) h1.le) (hL0 T), ?_⟩
    have : i T / (1 + i T) * L (i T) ≤ i T * L (i T) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      nlinarith [mul_nonneg (mul_nonneg (hi T) (hL0 T)) (hi T)]
    linarith [hLK T]
  have hnn : ∀ T, 0 ≤ bound44Term β ybar lam L i T := by
    intro T
    unfold bound44Term
    have := (hterm T).1
    have := (hlam0 T).le
    positivity
  refine Summable.of_nonneg_of_le hnn (fun T => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (Λ * (ybar + K)))
  unfold bound44Term
  have hb : 0 ≤ β ^ T := pow_nonneg hβ0 T
  have h2 : lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ Λ * (ybar + K) := by
    have h3 := (hterm T).2
    have h4 := (hterm T).1
    have h5 := (hlam0 T).le
    calc lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ lam (i T) * (ybar + K) := by
          gcongr
      _ ≤ Λ * (ybar + K) := mul_le_mul_of_nonneg_right (hlamΛ T) (by linarith)
  exact mul_le_mul_of_nonneg_left h2 hb

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.8).
Woodford (2003), pp. 127–128, "these solutions also satisfy (4.4), and hence represent
perfect-foresight equilibria, as long as … `iL(ȳ, i; 0)` has a finite bound for `i` near zero",
with no bound on `λ` assumed: along any self-fulfilling deflation of (4.5) (hypotheses of
`self_fulfilling_deflation45_gen`, plus `φ` nondecreasing) the interest rate stays in
`[0, φ(Π₀)]`, so `λ`, continuous on `[0, ∞)`, is bounded along the path; if moreover `L ≥ 0` and
`iL(i)` is bounded on bounded sets of `i ≥ 0`, (4.4) holds. -/
theorem deflation45_bound44_gen {β Pis ybar : ℝ} {lam φ L : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hy : 0 ≤ ybar) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j)
    (hLK : ∀ b, ∃ K, ∀ j, 0 ≤ j → j ≤ b → j * L j ≤ K) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Summable (bound44Term β ybar lam L (fun t => φ (Pi_ t))) := by
  have hd := self_fulfilling_deflation45_gen hβ hlam hsm hgrow hlamc hφ0 hcont hφβ hbelow
    hpath h0
  set b := φ (Pi_ 0) with hb
  have hi : ∀ T, 0 ≤ φ (Pi_ T) ∧ φ (Pi_ T) ≤ b := fun T =>
    ⟨hφ0 _ (hpath.1 T), hmono (hpath.1 T) (hpath.1 0) (hd.2.1 T).2⟩
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hlamc.mono fun z hz => Set.mem_Ici.mpr hz.1)
  obtain ⟨K, hK⟩ := hLK b
  refine bound44_summable_path (Λ := Λ) (K := K) hβ.le hβ1 hy (fun T => (hi T).1)
    (fun T => hlam _ (hi T).1) (fun T => ?_) (fun T => hL0 _ (hi T).1)
    (fun T => hK _ (hi T).1 (hi T).2)
  have := hΛ _ ⟨(hi T).1, (hi T).2⟩
  rw [Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) this

end Cochrane.NewKeynesianSelection.GlobalDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A full nonlinear model and the lower bound

Cochrane (2023), Chapter 16, §16.8, pp. 377–380.

The frictionless model with the nonlinear Fisher equation (16.25) and the government debt
valuation equation (16.26); the interest-rate rule (16.27) `1 + i_t = (1 + r)Φ(Π_t)`; perfect
foresight (16.28) `Π_{t+1} = β(1 + i_t)`, `β = 1/(1+r)`; hence the inflation dynamics (16.29)
`Π_{t+1} = Φ(Π_t)` of Figure 16.2.

## Main results

* (16.25): `bondPricing_perfectForesight_iff` (the general bond-pricing equation for an arbitrary
  `ExpectationSystem` reduces to (16.28) under perfect foresight), `fisher_pf_iff`.
* Linearisation, exact: `hasDerivAt_log_bondPricing` — under any `ExpectationSystem`, the
  derivative of `log(1 + i_t)` with respect to the scale `ε` of log inflation `επ_{t+1}` at the
  zero-inflation steady state is `E_t π_{t+1}`, which is (16.1); `gateaux_log_bondPricing` (the
  same Gateaux derivative at any steady state `π*`, along every bounded direction, with
  `E_exp_pos`); `log_fisher_pf` (exact log
  Fisher equation); `hasDerivAt_log_rule` (the slope of the rule (16.27) in logs at `Π*` is
  `Φ′(Π*)`, so the linearised Taylor coefficient is `φ = Φ′(Π*)`).
* (16.27)–(16.29): `dynamics_iff`, `eq_orbit`.
* p. 378: `target_unique_locally_bounded` (with `Φ′(Π*) > 1`, `Π*` is the unique locally bounded
  equilibrium), `target_repelling`.
* p. 379, the zero bound: `Hyperinflation.zero_bound_iff_scalar` (`i ≥ 0 ⇔ Π_{t+1} ≥ β`,
  error E2: `Π_{t+1} = β` is allowed), `zero_bound_eq_iff`, `rule_respects_bound_iff`.
* p. 379, Π_L, corrected (E2): `lower_steady_state` (existence of a largest fixed point
  `Π_L ∈ [β, Π*)` with `Φ < id` on `(Π_L, Π*)` and `Φ′(Π_L) ≤ 1`); counterexample to
  `Φ′(Π_L) < 1` (`phiTan`, `e2_tangency_counterexample`, orbits from `(1, 2)` still converge,
  `phiTan_deflation_tendsto`, but `Π_L` is not two-sided stable, `phiTan_left_unstable`);
  continuity is needed (`phiJump`, `e2_discontinuous_counterexample`).
* pp. 379–380: deflations "trundle down gently" to Π_L (`deflation_tendsto_lower`,
  `deflation_strictAnti`); local indeterminacy near Π_L when `|Φ′(Π_L)| < 1`
  (`lower_locally_indeterminate`).
* p. 379, fiscal policy: (16.30) and the passive rule ⇒ constant real debt are the canonical
  `Hyperinflation.real_debt_flow_scalar`, `Hyperinflation.passive_real_debt_const_real` and
  `Hyperinflation.pv_partial` (§16.3 restates the §16.8 fiscal block); valuation (16.26) ⇔
  transversality given the flow
  (`valuation_of_tvc`, `tvc_of_valuation`, `valuation_iff_tvc`); the general passive rule
  `s_t = γB_{t−1}/P_t` satisfies the TVC for all debt iff `0 < γ < 2`
  (`passive_gamma_tvc_iff`, `passive_coefficient_mem`); the full equilibrium
  definition `IsEquilibrium`, its dynamics `equilibrium_dynamics`, and existence of an
  equilibrium for every initial inflation (`equilibrium_exists`, `continuum_of_equilibria`),
  including the deflations converging to Π_L (`deflationary_equilibria`).
* p. 379, the 2%/1% example: the truncated linear rule `truncRule`; `truncRule_orbit_gap`,
  `truncRule_hits_bound` (paths below `Π*` reach `i = 0` in finite time and stay);
  `example_two_one` (`Π* = 1.02`, `r = 1%`, start `1.0199`, inflation `β − 1 = −1/101`);
  `negative_real_rate_example` (p. 380: `r = −1%` puts `Π_L` near `1%`).
-/

namespace Cochrane.NewKeynesianSelection.LowerBound

open Filter Topology
open Cochrane.NewKeynesianSelection.GlobalDynamics

/-! ## (16.25): the nonlinear Fisher equation -/

/-- Cochrane (2023), eq. (16.25), p. 377: the bond-pricing (nonlinear Fisher) equation
`1/(1 + i_t) = (1 + r)⁻¹ E_t(1/Π_{t+1})` for an arbitrary expectation system (gross inflation
`Π_{t+1} = P_{t+1}/P_t`). -/
def BondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r : ℝ) (i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / (1 + i t ω)) = (1 + r)⁻¹ • 𝔼.E t (fun ω => 1 / infl (t + 1) ω)

/-- Cochrane (2023), eqs. (16.25) and (16.28), p. 378: under perfect foresight the bond-pricing
equation is `Π_{t+1} = β(1 + i_t)` with `β = 1/(1 + r)` (given `1 + i_t > 0`, `Π_{t+1} > 0`). -/
theorem bondPricing_perfectForesight_iff {r : ℝ} {i infl : ℕ → Unit → ℝ} (hr : 0 < 1 + r)
    (hi : ∀ t, 0 < 1 + i t ()) (hP : ∀ t, 0 < infl (t + 1) ()) :
    BondPricing perfectForesight r i infl ↔ ∀ t, infl (t + 1) () = (1 + r)⁻¹ * (1 + i t ()) := by
  refine forall_congr' fun t => ?_
  have h1 := hi t
  have h2 := hP t
  constructor
  · intro h
    have h' := congrFun h ()
    simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul] at h'
    field_simp at h'
    rw [eq_inv_mul_iff_mul_eq₀ hr.ne']
    linarith
  · intro h
    funext ω
    simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    field_simp

/-- Cochrane (2023), eq. (16.25), p. 377, perfect foresight with price levels:
`1/(1 + i_t) = β P_t/P_{t+1}` if and only if `P_{t+1}/P_t = β(1 + i_t)`, `β = (1 + r)⁻¹`. -/
theorem fisher_pf_iff {r i P P' : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) (hP : 0 < P)
    (hP' : 0 < P') : 1 / (1 + i) = (1 + r)⁻¹ * (P / P') ↔ P' / P = (1 + r)⁻¹ * (1 + i) := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, exact in logs: under perfect foresight
`log(1 + i_t) = log(1 + r) + log Π_{t+1}`, i.e. `i = r + π` with log rates. -/
theorem log_fisher_pf {r i Pi1 : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i)
    (h : Pi1 = (1 + r)⁻¹ * (1 + i)) : Real.log (1 + i) = Real.log (1 + r) + Real.log Pi1 := by
  rw [h, Real.log_mul (inv_ne_zero hr.ne') hi.ne', Real.log_inv]
  ring

/-- Cochrane (2023), (16.25), pp. 377–378: a second-order bound used for the exact
linearisation; for `|z| ≤ 1`, `|e^z − 1 − z| ≤ z²`. -/
theorem abs_exp_sub_le {z : ℝ} (hz : |z| ≤ 1) : |Real.exp z - 1 - z| ≤ z ^ 2 :=
  Real.abs_exp_sub_one_sub_id_le hz

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, the exact linearisation under uncertainty:
for an arbitrary expectation system and a bounded log-inflation variable `x = π_{t+1}`, the map
`ε ↦ E_t[exp(−εx)]` (the expected inverse gross inflation along the ray `επ_{t+1}` through the
zero-inflation steady state) has derivative `−E_t x` at `ε = 0`. -/
theorem hasDerivAt_E_exp {Ω : Type*} (𝔼 : ExpectationSystem Ω) {x : Ω → ℝ} {M : ℝ}
    (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω) (-(𝔼.E t x ω)) 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hball : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < min (1 / M) (c / M ^ 2) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ)
      (show 0 < min (1 / M) (c / M ^ 2) from lt_min (by positivity) (by positivity)))
      fun ε hε => by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε; exact hε
  filter_upwards [hball] with ε hε
  have hε1 : |ε| * M ≤ 1 := by
    have := (lt_min_iff.mp hε).1
    rw [lt_div_iff₀ hM] at this
    linarith
  have hε2 : |ε| * M ^ 2 ≤ c := by
    have := (lt_min_iff.mp hε).2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  -- the remainder `R(ω') = exp(−εx) − 1 + εx` is bounded by `ε²M²`
  set R : Ω → ℝ := fun ω' => Real.exp (-(ε * x ω')) - 1 - (-(ε * x ω')) with hR
  have hRb : ∀ ω', |R ω'| ≤ ε ^ 2 * M ^ 2 := by
    intro ω'
    have hz : |-(ε * x ω')| ≤ 1 := by
      rw [abs_neg, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hx ω') (abs_nonneg ε)) hε1
    have h := abs_exp_sub_le hz
    have hsq : (-(ε * x ω')) ^ 2 ≤ ε ^ 2 * M ^ 2 := by
      have : (-(ε * x ω')) ^ 2 = ε ^ 2 * (x ω') ^ 2 := by ring
      rw [this]
      have : (x ω') ^ 2 ≤ M ^ 2 := by
        have := hx ω'
        nlinarith [abs_nonneg (x ω'), sq_abs (x ω')]
      exact mul_le_mul_of_nonneg_left this (sq_nonneg ε)
    exact h.trans hsq
  have hdecomp : (fun ω' => Real.exp (-(ε * x ω'))) =
      (fun _ => (1 : ℝ)) + (-ε) • x + R := by
    funext ω'
    simp only [hR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hE0 : 𝔼.E t (fun ω' => Real.exp (-(0 * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  have hEε : 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω =
      1 + (-ε) * 𝔼.E t x ω + 𝔼.E t R ω := by
    rw [hdecomp, map_add, map_add, map_smul, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hER := 𝔼.abs_E_le hRb t ω
  simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero]
  rw [hEε, hE0]
  have : 1 + -ε * 𝔼.E t x ω + 𝔼.E t R ω - 1 - ε * -𝔼.E t x ω = 𝔼.E t R ω := by ring
  rw [this]
  calc |𝔼.E t R ω| ≤ ε ^ 2 * M ^ 2 := hER
    _ = |ε| * (|ε| * M ^ 2) := by rw [← sq_abs]; ring
    _ ≤ |ε| * c := mul_le_mul_of_nonneg_left hε2 (abs_nonneg ε)
    _ = c * |ε| := mul_comm _ _

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, exact linearisation: write the bond-pricing
equation as `log(1 + i_t(ε)) = log(1 + r) − log E_t[exp(−επ_{t+1})]` along the ray `επ_{t+1}`
of log inflation through the zero-inflation steady state. For an arbitrary expectation system and
bounded `π_{t+1}`, its derivative at `ε = 0` is `E_t π_{t+1}`: the linearised Fisher equation
`i_t = r + E_t π_{t+1}` (16.1). -/
theorem hasDerivAt_log_bondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r : ℝ) {x : Ω → ℝ}
    {M : ℝ} (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt
      (fun ε => Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω))
      (𝔼.E t x ω) 0 := by
  have h := hasDerivAt_E_exp 𝔼 hM hx t ω
  have h1 : 𝔼.E t (fun ω' => Real.exp (-((0 : ℝ) * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  have hlog := h.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  have := (hasDerivAt_const (0 : ℝ) (Real.log (1 + r))).sub hlog
  convert this using 1
  ring

/-- Cochrane (2023), (16.25), pp. 377–378: for bounded `x` (`|x| ≤ M`) and every `ε`, the
conditional expectation `E_t[exp(−εx)]` is at least `exp(−|ε|M) > 0`. -/
theorem E_exp_pos {Ω : Type*} (𝔼 : ExpectationSystem Ω) {x : Ω → ℝ} {M : ℝ}
    (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) (ε : ℝ) :
    0 < 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω := by
  have hle : (fun _ : Ω => Real.exp (-(|ε| * M))) ≤ fun ω' => Real.exp (-(ε * x ω')) := by
    intro ω'
    apply Real.exp_le_exp.mpr
    have h1 : |ε * x ω'| ≤ |ε| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx ω') (abs_nonneg ε)
    linarith [le_abs_self (ε * x ω')]
  have := 𝔼.mono t hle ω
  rw [𝔼.const] at this
  exact lt_of_lt_of_le (Real.exp_pos _) this

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, the exact linearisation as a Gateaux
derivative: at any deterministic steady state with log inflation `π*`, along *every* bounded
direction `x` of log inflation `π_{t+1} = π* + εx`, the map
`ε ↦ log(1 + i_t(ε)) = log(1 + r) − log E_t[exp(−(π* + εx))]` takes the value `log(1+r) + π*` at
`ε = 0` and has derivative `E_t x` there, for an arbitrary expectation system. So the linearised
Fisher equation `i_t = r + E_t π_{t+1}` (16.1) holds in every bounded direction, not only along
one ray. -/
theorem gateaux_log_bondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r pis : ℝ) {x : Ω → ℝ}
    {M : ℝ} (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + 0 * x ω'))) ω) =
        Real.log (1 + r) + pis ∧
      HasDerivAt
        (fun ε => Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω))
        (𝔼.E t x ω) 0 := by
  have hsplit : ∀ ε : ℝ, 𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω =
      Real.exp (-pis) * 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω := by
    intro ε
    have : (fun ω' => Real.exp (-(pis + ε * x ω'))) =
        Real.exp (-pis) • fun ω' => Real.exp (-(ε * x ω')) := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, neg_add, Real.exp_add]
    rw [this, map_smul]
    rfl
  have hfun : (fun ε => Real.log (1 + r) -
      Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω)) =
      fun ε => (Real.log (1 + r) + pis) -
        Real.log (𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω) := by
    funext ε
    rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (E_exp_pos 𝔼 hx t ω ε).ne', Real.log_exp]
    ring
  have h1 : 𝔼.E t (fun ω' => Real.exp (-((0 : ℝ) * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  refine ⟨?_, ?_⟩
  · rw [hsplit, h1, mul_one, Real.log_exp]
    ring
  · rw [hfun]
    have := hasDerivAt_log_bondPricing 𝔼 (r := r) hM hx t ω
    have h2 := this.const_add pis
    convert h2 using 1
    funext ε
    ring

/-- Cochrane (2023), eq. (16.27), p. 378, exact linearisation of the rule: if `Φ(Π*) = Π*` and
`Φ′(Π*) = d`, the rule in logs, `π ↦ log Φ(e^π)`, has slope `d` at `log Π*`; so the linearised
rule is `i_t − r = φ(π_t − π*)` with `φ = Φ′(Π*)`, and the linearised dynamics (16.29) are
`π_{t+1} − π* = φ(π_t − π*)`. -/
theorem hasDerivAt_log_rule {Φ : ℝ → ℝ} {Pis d : ℝ} (hPis : 0 < Pis) (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) :
    HasDerivAt (fun p => Real.log (Φ (Real.exp p))) d (Real.log Pis) := by
  have he : HasDerivAt Real.exp Pis (Real.log Pis) := by
    have := Real.hasDerivAt_exp (Real.log Pis)
    rwa [Real.exp_log hPis] at this
  have hd' : HasDerivAt Φ d (Real.exp (Real.log Pis)) := by rwa [Real.exp_log hPis]
  have hc := hd'.comp (Real.log Pis) he
  have hΦ : Φ (Real.exp (Real.log Pis)) ≠ 0 := by rw [Real.exp_log hPis, hfix]; exact hPis.ne'
  have hl := hc.log hΦ
  simp only [Function.comp_apply, Real.exp_log hPis, hfix] at hl
  convert hl using 1
  field_simp

/-! ## (16.27)–(16.29): the inflation dynamics -/

/-- Cochrane (2023), eqs. (16.27)–(16.29), p. 378: with `β(1 + r) = 1`, the rule
`1 + i_t = (1 + r)Φ(Π_t)` and perfect foresight `Π_{t+1} = β(1 + i_t)` hold at every date if and
only if the interest rate is given by the rule and inflation follows `Π_{t+1} = Φ(Π_t)`. -/
theorem dynamics_iff {r : ℝ} {Φ : ℝ → ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r) :
    ((∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ↔
      (∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, infl (t + 1) = Φ (infl t) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t => ?_⟩
    rw [h2, h1, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t => ?_⟩
    rw [h2, h1, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Cochrane (2023), eq. (16.29), p. 378: "initial inflation `Π₀` is the only indeterminacy":
a path of (16.29) is the orbit of `Φ` from `Π₀`. -/
theorem eq_orbit {Φ : ℝ → ℝ} {infl : ℕ → ℝ} (h : ∀ t, infl (t + 1) = Φ (infl t)) (t : ℕ) :
    infl t = Φ^[t] (infl 0) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [h, ih, Function.iterate_succ_apply']

/-- Cochrane (2023), eq. (16.29), p. 378: the orbit `Φ^[t](Π₀)` solves (16.29). -/
theorem orbit_succ (Φ : ℝ → ℝ) (Pi0 : ℝ) (t : ℕ) :
    Φ^[t + 1] Pi0 = Φ (Φ^[t] Pi0) :=
  Function.iterate_succ_apply' _ _ _

/-! ## p. 378: the active steady state -/

/-- Cochrane (2023), p. 378, "any `Π_t` that is `ε` above or below `Π*` leads away from `Π*`":
if `Φ(Π*) = Π*` and `Φ′(Π*) > 1`, there is `δ > 0` such that every path of (16.29) not starting at
`Π*` is at distance at least `δ` from `Π*` at some date. -/
theorem target_repelling {Φ : ℝ → ℝ} {Pis d : ℝ} (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → ℝ, (∀ t, infl (t + 1) = Φ (infl t)) → infl 0 ≠ Pis →
      ∃ t, δ ≤ |infl t - Pis| :=
  repelling_of_one_lt_abs_deriv hfix hd (by rw [abs_of_pos (by linarith)]; exact hd1)

/-- Cochrane (2023), p. 378, "the equilibrium `Π*` is a unique 'locally bounded' equilibrium":
with `Φ′(Π*) > 1` there is `δ > 0` such that the only path of (16.29) staying within `δ` of `Π*`
at all dates is `Π_t ≡ Π*`. -/
theorem target_unique_locally_bounded {Φ : ℝ → ℝ} {Pis d : ℝ} (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → ℝ, (∀ t, infl (t + 1) = Φ (infl t)) →
      (∀ t, |infl t - Pis| < δ) → ∀ t, infl t = Pis := by
  obtain ⟨δ, hδ, hrep⟩ := target_repelling hfix hd hd1
  refine ⟨δ, hδ, fun infl hpath hbd t => ?_⟩
  by_contra hne
  obtain ⟨s, hs⟩ := hrep (fun s => infl (t + s)) (fun s => by rw [← add_assoc]; exact hpath _)
    (by simpa using hne)
  linarith [hbd (t + s)]

/-! ## p. 379: the zero bound -/

/-- Cochrane (2023), p. 379, error E2: `Π_{t+1} = β` exactly when `i_t = 0`, which the zero bound
allows. -/
theorem zero_bound_eq_iff {r i Pi1 : ℝ} (hr : 0 < 1 + r) (h : Pi1 = (1 + r)⁻¹ * (1 + i)) :
    i = 0 ↔ Pi1 = (1 + r)⁻¹ := by
  rw [h]
  constructor
  · intro hi; rw [hi]; ring
  · intro he
    have h2 : (1 + r)⁻¹ * (1 + i) = (1 + r)⁻¹ * 1 := by rw [he]; ring
    have := mul_left_cancel₀ (inv_ne_zero hr.ne') h2
    linarith

/-- Cochrane (2023), pp. 378–379: the rule (16.27) respects the zero bound at `Π` iff
`Φ(Π) ≥ β`. -/
theorem rule_respects_bound_iff {r x : ℝ} {Φ : ℝ → ℝ} (hr : 0 < 1 + r) :
    0 ≤ (1 + r) * Φ x - 1 ↔ (1 + r)⁻¹ ≤ Φ x := by
  rw [inv_le_iff_one_le_mul₀' hr]
  constructor <;> intro h <;> linarith

/-! ## p. 379: the second steady state `Π_L` (error E2) -/

/-- Cochrane (2023), p. 379, "the function `Φ(Π)` must also have another stationary point,
labeled `Π_L`", corrected (error E2). If `Φ` is continuous on `[β, Π*]`, respects the zero bound
there (`Φ ≥ β`), `Φ(Π*) = Π*` and `Φ′(Π*) > 1`, then there is a largest fixed point
`Π_L ∈ [β, Π*)` below `Π*`: `Φ(Π) < Π` on `(Π_L, Π*)`, and `Φ′(Π_L) ≤ 1` whenever `Φ` is
differentiable at `Π_L`. (Only the weak inequality follows: see `e2_tangency_counterexample`.) -/
theorem lower_steady_state {Φ : ℝ → ℝ} {β Pis d : ℝ} (hβPis : β < Pis)
    (hcont : ContinuousOn Φ (Set.Icc β Pis)) (hbound : ∀ x ∈ Set.Icc β Pis, β ≤ Φ x)
    (hfix : Φ Pis = Pis) (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ PL, β ≤ PL ∧ PL < Pis ∧ Φ PL = PL ∧ (∀ x, PL < x → x < Pis → Φ x < x) ∧
      ∀ d', HasDerivAt Φ d' PL → d' ≤ 1 := by
  set f : ℝ → ℝ := fun x => Φ x - x with hf
  have hfd : ∀ {x e}, HasDerivAt Φ e x → HasDerivAt f (e - 1) x :=
    fun h => h.sub (hasDerivAt_id _)
  have hfc : ∀ a b, β ≤ a → b ≤ Pis → ContinuousOn f (Set.Icc a b) := fun a b ha hb =>
    ((hcont.mono fun y hy => ⟨ha.trans hy.1, hy.2.trans hb⟩).sub continuousOn_id)
  have hfPis : f Pis = 0 := by simp [hf, hfix]
  have hfβ : 0 ≤ f β := by simp only [hf]; linarith [hbound β ⟨le_rfl, hβPis.le⟩]
  obtain ⟨δ, hδ, hleft, -⟩ := sign_near_of_deriv_pos (hfd hd) (by linarith)
  have hneg : ∀ y, Pis - δ < y → y < Pis → f y < 0 := fun y h1 h2 => by
    have := hleft y h1 h2; rwa [hfPis] at this
  set y1 := max β (Pis - δ / 2) with hy1
  have hy1lt : y1 < Pis := max_lt hβPis (by linarith)
  have hfy1 : f y1 < 0 := hneg y1 (lt_max_of_lt_right (by linarith)) hy1lt
  have hβy1 : β ≤ y1 := le_max_left _ _
  set S := Set.Icc β y1 ∩ f ⁻¹' {0} with hS
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hβy1 (hfc β y1 le_rfl hy1lt.le)
      ⟨hfy1.le, hfβ⟩
    exact ⟨c, hc, hfc0⟩
  have hSclosed : IsClosed S :=
    (hfc β y1 le_rfl hy1lt.le).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddAbove S := ⟨y1, fun z hz => hz.1.2⟩
  have hmem := hSclosed.csSup_mem hSne hSbdd
  set PL := sSup S with hPL
  have hPLβ : β ≤ PL := hmem.1.1
  have hPLy1 : PL ≤ y1 := hmem.1.2
  have hPLfix : f PL = 0 := hmem.2
  have hbelow : ∀ x, PL < x → x < Pis → Φ x < x := by
    intro x hx1 hx2
    suffices f x < 0 by simp only [hf] at this; linarith
    by_cases hxy : x ≤ y1
    · by_contra hcon
      push Not at hcon
      obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hxy
        (hfc x y1 (by linarith) hy1lt.le) ⟨hfy1.le, hcon⟩
      have hcS : c ∈ S := ⟨⟨by linarith [hc.1], hc.2⟩, hfc0⟩
      have := le_csSup hSbdd hcS
      linarith [hc.1]
    · push Not at hxy
      exact hneg x (by linarith [le_max_right β (Pis - δ / 2)]) hx2
  refine ⟨PL, hPLβ, by linarith, by simpa [hf, sub_eq_zero] using hPLfix, hbelow,
    fun d' hd' => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, -, hright⟩ := sign_near_of_deriv_pos (hfd hd') (by linarith)
  set y := min (PL + ε / 2) ((PL + Pis) / 2) with hy
  have hPLP : PL < Pis := by linarith
  have hy1' : PL < y := lt_min (by linarith) (by linarith)
  have hy2 : y < Pis := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 := hright y hy1' (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h2 := hbelow y hy1' hy2
  rw [hPLfix] at h1
  simp only [hf] at h1
  linarith

/-- Cochrane (2023), p. 379, error E2 counterexample: the rule
`Φ(Π) = max(1/2, Π + (Π − 1/2)(Π − 1)²(Π − 2))` (with `β = 1/2`, i.e. `r = 1`). -/
noncomputable def phiTan (x : ℝ) : ℝ := max (1 / 2) (x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2))

/-- Cochrane (2023), p. 379, error E2: the polynomial branch of `phiTan` is at least `1/2` on
`[1/2, ∞)`. -/
theorem phiTan_poly_ge {x : ℝ} (hx : 1 / 2 ≤ x) :
    1 / 2 ≤ x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) := by
  have h : (x - 1) ^ 2 * (x - 2) ≥ -1 := by
    rcases le_or_gt 2 x with h2 | h2
    · nlinarith [sq_nonneg (x - 1)]
    · have hb : (x - 1) ^ 2 * (2 - x) ≤ 1 := by
        rcases le_or_gt x (3 / 2) with h3 | h3
        · have ha : (x - 1) ^ 2 ≤ 1 / 4 := by nlinarith
          have := mul_le_mul ha (by linarith : 2 - x ≤ 3 / 2) (by linarith) (by norm_num)
          linarith
        · have ha : (x - 1) ^ 2 ≤ 1 := by nlinarith
          have := mul_le_mul ha (by linarith : 2 - x ≤ 1 / 2) (by linarith) (by norm_num)
          linarith
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ x - 1 / 2)]

/-- Cochrane (2023), p. 379, error E2: on `[1/2, ∞)` the rule `phiTan` is its polynomial
branch. -/
theorem phiTan_eq {x : ℝ} (hx : 1 / 2 ≤ x) :
    phiTan x = x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) :=
  max_eq_right (phiTan_poly_ge hx)

/-- Cochrane (2023), p. 379, error E2: the derivative of the polynomial branch of `phiTan`. -/
theorem hasDerivAt_tanPoly (x : ℝ) :
    HasDerivAt (fun y : ℝ => y + (y - 1 / 2) * (y - 1) ^ 2 * (y - 2))
      (1 + ((x - 1) ^ 2 * (x - 2) + (x - 1 / 2) * (2 * (x - 1)) * (x - 2) +
        (x - 1 / 2) * (x - 1) ^ 2)) x := by
  have ha : HasDerivAt (fun y : ℝ => y - 1 / 2) 1 x := (hasDerivAt_id x).sub_const _
  have hb : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
    have := ((hasDerivAt_id x).sub_const (1 : ℝ)).pow 2
    convert this using 1
    · funext y; simp
    · simp
  have hc : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const _
  have h := (hasDerivAt_id x).add ((ha.mul hb).mul hc)
  convert h using 1
  · funext y; simp only [id_eq, Pi.add_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; ring

/-- Cochrane (2023), p. 379, error E2: `phiTan` equals its polynomial branch near any
`x > 1/2`, so it has the polynomial's derivative there. -/
theorem hasDerivAt_phiTan {x : ℝ} (hx : 1 / 2 < x) :
    HasDerivAt phiTan
      (1 + ((x - 1) ^ 2 * (x - 2) + (x - 1 / 2) * (2 * (x - 1)) * (x - 2) +
        (x - 1 / 2) * (x - 1) ^ 2)) x := by
  refine (hasDerivAt_tanPoly x).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact phiTan_eq (le_of_lt hy)

/-- Cochrane (2023), p. 379, error E2, the tangency counterexample: with `β = 1/2` the rule
`phiTan` is continuous, respects the zero bound everywhere (`Φ ≥ β`), has the active steady state
`Π* = 2` with `Φ′(Π*) = 5/2 > 1`, and the lower steady state given by `lower_steady_state` is
forced to be `Π_L = 1`, where `Φ′(Π_L) = 1`: the printed "`Φ′(Π_L) < 1`" fails. -/
theorem e2_tangency_counterexample :
    Continuous phiTan ∧ (∀ x, 1 / 2 ≤ phiTan x) ∧ phiTan 2 = 2 ∧ HasDerivAt phiTan (5 / 2) 2 ∧
      (∀ PL : ℝ, 1 / 2 ≤ PL → PL < 2 → phiTan PL = PL →
        (∀ x, PL < x → x < 2 → phiTan x < x) → PL = 1) ∧
      phiTan 1 = 1 ∧ (∀ x, 1 < x → x < 2 → phiTan x < x) ∧ HasDerivAt phiTan 1 1 ∧
      ¬ ((1 : ℝ) < 1) := by
  have hd2 := hasDerivAt_phiTan (by norm_num : (1 / 2 : ℝ) < 2)
  have hd1 := hasDerivAt_phiTan (by norm_num : (1 / 2 : ℝ) < 1)
  have hbelow : ∀ x : ℝ, 1 < x → x < 2 → phiTan x < x := by
    intro x h1 h2
    rw [phiTan_eq (by linarith)]
    have : (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) (by positivity)) (by linarith)
    linarith
  refine ⟨by unfold phiTan; fun_prop, fun x => le_max_left _ _,
    by rw [phiTan_eq (by norm_num)]; norm_num, by convert hd2 using 1; norm_num, ?_,
    by rw [phiTan_eq (by norm_num)]; norm_num, hbelow, by convert hd1 using 1; norm_num,
    lt_irrefl 1⟩
  intro PL h1 h2 hfix hb
  rw [phiTan_eq h1] at hfix
  have h0 : (PL - 1 / 2) * (PL - 1) ^ 2 * (PL - 2) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      have := hb 1 (by linarith) (by norm_num)
      rw [phiTan_eq (by norm_num)] at this
      norm_num at this
    · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h']
  · linarith

/-- Cochrane (2023), p. 379, error E2: in the tangency counterexample `Π_L = 1` is not stable
from the left: every path of (16.29) starting in `(1/2, 1)` stays at or below its initial value
(it drifts down towards the zero-bound rate `1/2`), so it never converges to `Π_L`. -/
theorem phiTan_left_unstable {infl : ℕ → ℝ} (hpath : ∀ t, infl (t + 1) = phiTan (infl t))
    (h0 : infl 0 ∈ Set.Ioo (1 / 2) 1) :
    (∀ t, 1 / 2 ≤ infl t ∧ infl t ≤ infl 0) ∧ ¬ Tendsto infl atTop (𝓝 1) := by
  have hstep : ∀ t, 1 / 2 ≤ infl t ∧ infl t ≤ infl 0 := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, le_rfl⟩
    | succ n ih =>
      rw [hpath]
      refine ⟨le_max_left _ _, ?_⟩
      rw [phiTan_eq ih.1]
      have : (infl n - 1 / 2) * (infl n - 1) ^ 2 * (infl n - 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [ih.1]) (sq_nonneg _))
          (by linarith [ih.2, h0.2])
      linarith [ih.2]
  refine ⟨hstep, fun hlim => ?_⟩
  have := le_of_tendsto' hlim fun t => (hstep t).2
  linarith [h0.2]

/-- Cochrane (2023), p. 379, error E2: continuity is needed for the existence of `Π_L`. The
discontinuous rule `Φ(Π) = Π + 1` for `Π < 3/2`, `Φ(Π) = 2Π − 2` for `Π ≥ 3/2`. -/
noncomputable def phiJump (x : ℝ) : ℝ := if x < 3 / 2 then x + 1 else 2 * x - 2

/-- Cochrane (2023), p. 379, error E2: with `β = 1/2`, `phiJump` respects the zero bound on
`(0, ∞)`, has `Π* = 2` with `Φ′(Π*) = 2 > 1`, and yet has no fixed point in `[β, Π*)`: without
continuity there need be no second steady state. -/
theorem e2_discontinuous_counterexample :
    (∀ x : ℝ, 0 < x → 1 / 2 ≤ phiJump x) ∧ phiJump 2 = 2 ∧ HasDerivAt phiJump 2 2 ∧
      ¬ ∃ PL : ℝ, 1 / 2 ≤ PL ∧ PL < 2 ∧ phiJump PL = PL := by
  refine ⟨fun x hx => ?_, by norm_num [phiJump], ?_, ?_⟩
  · unfold phiJump
    split_ifs with h
    · linarith
    · push Not at h; linarith
  · have h : HasDerivAt (fun x : ℝ => 2 * x - 2) 2 2 := by
      simpa using ((hasDerivAt_id (2 : ℝ)).const_mul 2).sub_const 2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2)] with x hx
    have : ¬ x < 3 / 2 := not_lt.mpr (le_of_lt hx)
    simp [phiJump, this]
  · rintro ⟨PL, -, h2, hfix⟩
    unfold phiJump at hfix
    split_ifs at hfix with h
    · linarith
    · linarith

/-! ## pp. 379–380: deflations converge to `Π_L` -/

/-- Cochrane (2023), pp. 379–380, "equilibria that start below `Π*` … trundle down gently to the
zero bound": if `Φ` is continuous on `[Π_L, Π*]`, `Φ(Π_L) = Π_L`, `Φ(Π) < Π` on `(Π_L, Π*)` and
`Φ(Π) ≥ Π_L` there (e.g. `Φ` nondecreasing), every path of (16.29) starting in `(Π_L, Π*)` is
nonincreasing, stays in `[Π_L, Π₀]` and converges to `Π_L`. -/
theorem deflation_tendsto_lower {Φ : ℝ → ℝ} {PL Pis : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Icc PL Pis)) (hfix : Φ PL = PL)
    (hbelow : ∀ x, PL < x → x < Pis → Φ x < x) (hge : ∀ x, PL < x → x < Pis → PL ≤ Φ x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ioo PL Pis) :
    Antitone infl ∧ (∀ t, PL ≤ infl t ∧ infl t ≤ infl 0) ∧ Tendsto infl atTop (𝓝 PL) := by
  have hstep : ∀ t, (PL ≤ infl t ∧ infl t ≤ infl 0) ∧ infl (t + 1) ≤ infl t := by
    have hinv : ∀ t, PL ≤ infl t ∧ infl t ≤ infl 0 := by
      intro t
      induction t with
      | zero => exact ⟨h0.1.le, le_rfl⟩
      | succ n ih =>
        rw [hpath]
        rcases ih.1.lt_or_eq with hlt | heq
        · have h2 : infl n < Pis := lt_of_le_of_lt ih.2 h0.2
          exact ⟨hge _ hlt h2, ((hbelow _ hlt h2).le.trans ih.2)⟩
        · rw [← heq, hfix]; exact ⟨le_rfl, h0.1.le⟩
    intro t
    refine ⟨hinv t, ?_⟩
    rw [hpath]
    rcases (hinv t).1.lt_or_eq with hlt | heq
    · exact (hbelow _ hlt (lt_of_le_of_lt (hinv t).2 h0.2)).le
    · rw [← heq, hfix]
  have hanti : Antitone infl := antitone_nat_of_succ_le fun t => (hstep t).2
  refine ⟨hanti, fun t => (hstep t).1, ?_⟩
  have hbdd : BddBelow (Set.range infl) := ⟨PL, by rintro _ ⟨t, rfl⟩; exact (hstep t).1.1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, infl t with hL
  have hLPL : PL ≤ L := le_ciInf fun t => (hstep t).1.1
  have hL0 : L ≤ infl 0 := ciInf_le hbdd 0
  have hmem : ∀ t, infl t ∈ Set.Icc PL Pis := fun t =>
    ⟨(hstep t).1.1, ((hstep t).1.2.trans h0.2.le)⟩
  have hLmem : L ∈ Set.Icc PL Pis := ⟨hLPL, hL0.trans h0.2.le⟩
  have hwithin : Tendsto infl atTop (𝓝[Set.Icc PL Pis] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hmem⟩
  have h1 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 (Φ L)) :=
    (hcont L hLmem).tendsto.comp hwithin
  have h2 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 L) := by
    have : (fun t => Φ (infl t)) = fun t => infl (t + 1) := funext fun t => (hpath t).symm
    rw [this]
    exact (tendsto_add_atTop_iff_nat 1).mpr hlim
  have hfixL : Φ L = L := tendsto_nhds_unique h1 h2
  rcases hLPL.lt_or_eq with hlt | heq
  · exfalso
    have := hbelow L hlt (lt_of_le_of_lt hL0 h0.2)
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Cochrane (2023), pp. 379–380: if moreover `Φ(Π) > Π_L` on `(Π_L, Π*)` (e.g. `Φ` strictly
increasing), inflation declines strictly and never reaches `Π_L`. -/
theorem deflation_strictAnti {Φ : ℝ → ℝ} {PL Pis : ℝ} {infl : ℕ → ℝ}
    (hbelow : ∀ x, PL < x → x < Pis → Φ x < x) (hgt : ∀ x, PL < x → x < Pis → PL < Φ x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ioo PL Pis) :
    StrictAnti infl ∧ ∀ t, PL < infl t := by
  have hstep : ∀ t, (PL < infl t ∧ infl t ≤ infl 0) ∧ infl (t + 1) < infl t := by
    have hinv : ∀ t, PL < infl t ∧ infl t ≤ infl 0 := by
      intro t
      induction t with
      | zero => exact ⟨h0.1, le_rfl⟩
      | succ n ih =>
        rw [hpath]
        have h2 : infl n < Pis := lt_of_le_of_lt ih.2 h0.2
        exact ⟨hgt _ ih.1 h2, ((hbelow _ ih.1 h2).le.trans ih.2)⟩
    intro t
    refine ⟨hinv t, ?_⟩
    rw [hpath]
    exact hbelow _ (hinv t).1 (lt_of_le_of_lt (hinv t).2 h0.2)
  exact ⟨strictAnti_nat_of_succ_lt fun t => (hstep t).2, fun t => (hstep t).1.1⟩

/-- Cochrane (2023), p. 379, error E2: in the tangency counterexample the economic conclusion
survives: every path starting in `(Π_L, Π*) = (1, 2)` converges to `Π_L = 1`. -/
theorem phiTan_deflation_tendsto {infl : ℕ → ℝ} (hpath : ∀ t, infl (t + 1) = phiTan (infl t))
    (h0 : infl 0 ∈ Set.Ioo 1 2) : Tendsto infl atTop (𝓝 1) := by
  obtain ⟨-, -, -, -, -, hfix1, hbelow, -, -⟩ := e2_tangency_counterexample
  refine (deflation_tendsto_lower (Pis := 2) ?_ hfix1 hbelow ?_ hpath h0).2.2
  · unfold phiTan; fun_prop
  · intro x h1 h2
    rw [phiTan_eq (by linarith)]
    have hq : -(1 / 4 : ℝ) ≤ (x - 1) * (x - 2) := by nlinarith [sq_nonneg (x - 3 / 2)]
    have hq2 : (x - 1) * (x - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (by linarith)
    have hp : -(3 / 8 : ℝ) ≤ (x - 1 / 2) * ((x - 1) * (x - 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right (by linarith : x - 1 / 2 ≤ 3 / 2)
        (by linarith : (0 : ℝ) ≤ -((x - 1) * (x - 2)))]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1)
      (by linarith : (0 : ℝ) ≤ 1 + (x - 1 / 2) * ((x - 1) * (x - 2)))]

/-- Cochrane (2023), p. 379, "many paths lead to `Π_L` and there are 'multiple local equilibria'
near this point": if `|Φ′(Π_L)| < 1`, there is `δ > 0` such that every `Π₀` within `δ` of `Π_L`
starts a path of (16.29) that stays within `δ` and converges to `Π_L`, and distinct `Π₀` give
distinct paths (a continuum of locally bounded equilibria). -/
theorem lower_locally_indeterminate {Φ : ℝ → ℝ} {PL d : ℝ} (hfix : Φ PL = PL)
    (hd : HasDerivAt Φ d PL) (hd1 : |d| < 1) :
    ∃ δ > 0, Set.InjOn (fun Pi0 t => Φ^[t] Pi0) (Set.Ioo (PL - δ) (PL + δ)) ∧
      ∀ Pi0 ∈ Set.Ioo (PL - δ) (PL + δ),
        (∀ t, |Φ^[t] Pi0 - PL| < δ) ∧ Tendsto (fun t => Φ^[t] Pi0) atTop (𝓝 PL) := by
  obtain ⟨δ, hδ, hatt⟩ := attracting_of_abs_deriv_lt_one hfix hd hd1
  refine ⟨δ, hδ, fun a _ b _ hab => by simpa using congrFun hab 0, fun Pi0 hP => ?_⟩
  exact hatt (fun t => Φ^[t] Pi0) (fun t => orbit_succ Φ Pi0 t)
    (by rw [Function.iterate_zero_apply, abs_lt]; constructor <;> linarith [hP.1, hP.2])

/-! ## p. 379: fiscal policy, (16.26) and (16.30) -/

/-- Cochrane (2023), (16.30) ⇒ (16.26), p. 379, "with … the flow condition (16.30) the
transversality condition holds, and (16.30) implies (16.26)": given the real flow, absolute
summability of discounted surpluses and the transversality condition `βᵀ b_{t+T} → 0`, the
valuation equation (16.26) `b_t = Σ βʲ s_{t+j}` holds as a genuine sum. -/
theorem valuation_of_tvc {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (hsum : Summable fun j => (1 + r)⁻¹ ^ j * s (t + j))
    (htvc : Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0)) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t) := by
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun T => ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j)) atTop
      (𝓝 (b t)) := by
    have : (fun T => ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j)) =
        fun T => b t - (1 + r)⁻¹ ^ T * b (t + T) := by
      funext T; rw [Hyperinflation.pv_partial hr hflow t T]; ring
    rw [this]
    simpa using (tendsto_const_nhds (x := b t)).sub htvc
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

/-- Cochrane (2023), (16.26), p. 379: conversely, the valuation equation (as a genuine sum)
together with the flow implies the transversality condition. -/
theorem tvc_of_valuation {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (h : HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0) := by
  have h1 := h.tendsto_sum_nat
  have : (fun T => (1 + r)⁻¹ ^ T * b (t + T)) =
      fun T => b t - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j) := by
    funext T; rw [Hyperinflation.pv_partial hr hflow t T]; ring
  rw [this]
  simpa using (tendsto_const_nhds (x := b t)).sub h1

/-- Cochrane (2023), (16.26) ⇔ transversality, p. 379: given the flow (16.30) and absolute
summability of the discounted surpluses, the valuation equation holds at `t` if and only if the
transversality condition holds at `t`. -/
theorem valuation_iff_tvc {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (hsum : Summable fun j => (1 + r)⁻¹ ^ j * s (t + j)) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0) :=
  ⟨tvc_of_valuation hr hflow t, valuation_of_tvc hr hflow t hsum⟩

/-- Cochrane (2023), p. 379, "(This is a specific version of the specification
`s_t = γ(B_{t−1}/P_t)` that produces passive fiscal policy.)": with `r > −1`, under
`s_t = γ b_t` real debt follows `b_{t+1} = (1 + r)(1 − γ)b_t`, and the transversality condition
`βᵗb_t → 0` holds for every initial real debt iff `0 < γ < 2`; `γ = r/(1+r)` lies in this range
for `r > 0`. -/
theorem passive_gamma_tvc_iff {r γ : ℝ} (hr : 0 < 1 + r) :
    (∀ b : ℕ → ℝ, (∀ t, b (t + 1) = (1 + r) * (b t - γ * b t)) →
      Tendsto (fun t => (1 + r)⁻¹ ^ t * b t) atTop (𝓝 0)) ↔ 0 < γ ∧ γ < 2 := by
  have hsol : ∀ b : ℕ → ℝ, (∀ t, b (t + 1) = (1 + r) * (b t - γ * b t)) →
      ∀ t, (1 + r)⁻¹ ^ t * b t = (1 - γ) ^ t * b 0 := by
    intro b hb t
    induction t with
    | zero => simp
    | succ n ih =>
      have e : (1 + r)⁻¹ ^ (n + 1) * b (n + 1) = ((1 + r)⁻¹ ^ n * b n) * (1 - γ) := by
        rw [hb, pow_succ]
        field_simp
      rw [e, ih, pow_succ]
      ring
  have habs : |1 - γ| < 1 ↔ 0 < γ ∧ γ < 2 := by
    rw [abs_lt]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← habs]
  constructor
  · intro h
    set b : ℕ → ℝ := fun t => ((1 + r) * (1 - γ)) ^ t with hbdef
    have hb : ∀ t, b (t + 1) = (1 + r) * (b t - γ * b t) := fun t => by
      simp only [hbdef, pow_succ]; ring
    have h1 := h b hb
    rw [show (fun t => (1 + r)⁻¹ ^ t * b t) = fun t => (1 - γ) ^ t * b 0 from
      funext (hsol b hb)] at h1
    simp only [hbdef, pow_zero, mul_one] at h1
    by_contra hcon
    push Not at hcon
    have hge : ∀ t : ℕ, 1 ≤ |(1 - γ) ^ t| := fun t => by rw [abs_pow]; exact one_le_pow₀ hcon
    have h2 := h1.abs
    rw [abs_zero] at h2
    have := ge_of_tendsto' h2 hge
    linarith
  · intro h b hb
    simp only [hsol b hb]
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const (b 0)

/-- Cochrane (2023), p. 379: for `r > 0` the passive coefficient `γ = r/(1 + r)` satisfies
`0 < γ < 2`. -/
theorem passive_coefficient_mem {r : ℝ} (hr : 0 < r) : 0 < r / (1 + r) ∧ r / (1 + r) < 2 := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-! ## The perfect-foresight equilibrium of §16.8 -/

/-- Cochrane (2023), eq. (16.27), p. 378: the previous price level, `P_{t−1}` (with the
predetermined initial `P_{−1}` at `t = 0`). -/
def prevP (Pm1 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => Pm1
  | t + 1 => P t

/-- Cochrane (2023), eq. (16.27), p. 378: gross inflation `Π_t = P_t/P_{t−1}`. -/
noncomputable def infl (Pm1 : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := P t / prevP Pm1 P t

/-- Cochrane (2023), §16.8, pp. 377–379: a perfect-foresight equilibrium of the full model with
interest-rate rule `Φ`, real rate `r`, initial price `P_{−1} = Pm1`: positive prices, the zero
bound `i_t ≥ 0`, the Fisher equation (16.25), the rule (16.27), the flow condition
`B_t/(1 + i_t) + P_t s_t = B_{t−1}` (with `D t = B_{t−1}`), and the valuation equation (16.26)
`B_{t−1}/P_t = Σ βʲ s_{t+j}` at every date, as a genuine sum. -/
def IsEquilibrium (r : ℝ) (Φ : ℝ → ℝ) (Pm1 : ℝ) (P i s D : ℕ → ℝ) : Prop :=
  0 < Pm1 ∧ (∀ t, 0 < P t) ∧ (∀ t, 0 ≤ i t) ∧
    (∀ t, 1 / (1 + i t) = (1 + r)⁻¹ * (P t / P (t + 1))) ∧
    (∀ t, 1 + i t = (1 + r) * Φ (infl Pm1 P t)) ∧
    (∀ t, D (t + 1) / (1 + i t) + P t * s t = D t) ∧
    ∀ t, HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (D t / P t)

/-- Cochrane (2023), eqs. (16.28)–(16.30), pp. 378–379: in any equilibrium inflation follows
(16.29) `Π_{t+1} = Φ(Π_t)`, respects the zero bound `Π_{t+1} ≥ β`, real debt follows (16.30), and
the transversality condition holds at every date. -/
theorem equilibrium_dynamics {r : ℝ} {Φ : ℝ → ℝ} {Pm1 : ℝ} {P i s D : ℕ → ℝ} (hr : 0 < 1 + r)
    (h : IsEquilibrium r Φ Pm1 P i s D) :
    (∀ t, infl Pm1 P (t + 1) = Φ (infl Pm1 P t)) ∧ (∀ t, (1 + r)⁻¹ ≤ infl Pm1 P (t + 1)) ∧
      (∀ t, D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t)) ∧
      ∀ t, Tendsto (fun T => (1 + r)⁻¹ ^ T * (D (t + T) / P (t + T))) atTop (𝓝 0) := by
  obtain ⟨-, hP, hi, hfis, hrule, hflow, hval⟩ := h
  have hfis' : ∀ t, infl Pm1 P (t + 1) = (1 + r)⁻¹ * (1 + i t) := fun t => by
    have := (fisher_pf_iff hr (by linarith [hi t]) (hP t) (hP (t + 1))).mp (hfis t)
    simpa [infl, prevP] using this
  have hrate : ∀ t, 1 + i t = (1 + r) * (P (t + 1) / P t) := fun t => by
    have := hfis' t
    simp only [infl, prevP] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hreal : ∀ t, D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t) := fun t =>
    Hyperinflation.real_debt_flow_scalar hr (hP t) (hP (t + 1)) (hrate t) (hflow t)
  refine ⟨fun t => ?_, fun t => (Hyperinflation.zero_bound_iff_scalar hr (hfis' t)).mp (hi t),
    hreal,
    fun t => tvc_of_valuation (b := fun t => D t / P t) hr hreal t (hval t)⟩
  rw [hfis', hrule, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Cochrane (2023), p. 379, "all of the paths graphed in Figure 16.2 are perfect-foresight
equilibria … we only need to exhibit one [fiscal policy]: `s_t = (r/(1+r))B_{t−1}/P_t`": for
`r > 0`, any `P_{−1} > 0`, initial nominal debt `B_{−1}`, and any initial inflation `Π₀ > 0`
whose orbit under `Φ` respects the zero bound, there is an equilibrium with `Π_t = Φ^[t](Π₀)`,
the passive surplus rule, and constant real debt. -/
theorem equilibrium_exists {r : ℝ} {Φ : ℝ → ℝ} {Pm1 Pi0 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hPi0 : 0 < Pi0) (hbound : ∀ t, (1 + r)⁻¹ ≤ Φ (Φ^[t] Pi0)) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ D 0 = D0 ∧
      (∀ t, infl Pm1 P t = Φ^[t] Pi0) ∧ (∀ t, s t = r / (1 + r) * (D t / P t)) ∧
      ∀ t, D t / P t = D0 / (Pm1 * Pi0) := by
  have hr1 : 0 < 1 + r := by linarith
  set π : ℕ → ℝ := fun t => Φ^[t] Pi0 with hπ
  have hπpos : ∀ t, 0 < π t := by
    intro t
    cases t with
    | zero => simpa [hπ] using hPi0
    | succ n =>
      simp only [hπ, orbit_succ]
      exact lt_of_lt_of_le (inv_pos.mpr hr1) (hbound n)
  have hπsucc : ∀ t, π (t + 1) = Φ (π t) := fun t => orbit_succ Φ Pi0 t
  set P : ℕ → ℝ := fun t => Pm1 * ∏ k ∈ Finset.range (t + 1), π k with hPdef
  set D : ℕ → ℝ := fun t => D0 * ∏ k ∈ Finset.range t, π (k + 1) with hDdef
  set c : ℝ := D0 / (Pm1 * Pi0) with hc
  have hPpos : ∀ t, 0 < P t := fun t =>
    mul_pos hPm1 (Finset.prod_pos fun k _ => hπpos k)
  have hPsucc : ∀ t, P (t + 1) = P t * π (t + 1) := fun t => by
    simp only [hPdef, Finset.prod_range_succ _ (t + 1)]; ring
  have hDsucc : ∀ t, D (t + 1) = D t * π (t + 1) := fun t => by
    simp only [hDdef, Finset.prod_range_succ]; ring
  have hreal : ∀ t, D t / P t = c := by
    intro t
    induction t with
    | zero =>
      simp only [hDdef, hPdef, hc, Finset.range_zero, Finset.prod_empty, mul_one, zero_add,
        Finset.prod_range_one]
      simp [hπ]
    | succ n ih =>
      rw [hDsucc, hPsucc, mul_div_mul_right _ _ (hπpos (n + 1)).ne', ih]
  have hinfl : ∀ t, infl Pm1 P t = π t := by
    intro t
    cases t with
    | zero =>
      simp only [infl, prevP, hPdef, zero_add, Finset.prod_range_one]
      field_simp
    | succ n =>
      simp only [infl, prevP]
      rw [hPsucc n]
      field_simp [(hPpos n).ne']
  set i : ℕ → ℝ := fun t => (1 + r) * Φ (π t) - 1 with hidef
  set s : ℕ → ℝ := fun _ => r / (1 + r) * c with hsdef
  have hone : ∀ t, 1 + i t = (1 + r) * π (t + 1) := fun t => by
    simp only [hidef, hπsucc]; ring
  refine ⟨P, i, s, D, ⟨hPm1, hPpos, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩, by simp [hDdef], fun t => hinfl t, fun t => by rw [hreal t],
    hreal⟩
  · have := (rule_respects_bound_iff (x := π t) (Φ := Φ) hr1).mpr (hbound t)
    simpa [hidef] using this
  · rw [hone, hPsucc]
    have := hπpos (t + 1)
    have := hPpos t
    field_simp
  · rw [hinfl, hone, hπsucc]
  · rw [hone, hDsucc]
    have h1 : P t * s t = r / (1 + r) * D t := by
      simp only [hsdef, ← hreal t]
      field_simp [(hPpos t).ne']
    rw [h1]
    have := hπpos (t + 1)
    field_simp
  · rw [hreal t]
    have hq0 : 0 ≤ (1 + r)⁻¹ := (inv_pos.mpr hr1).le
    have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right (r / (1 + r) * c)
    convert hg using 1
    field_simp
    rw [show 1 + r - 1 = r by ring, mul_div_assoc, div_self hr.ne', mul_one]

/-- Cochrane (2023), p. 379, "all of the paths … are perfect-foresight equilibria": if the rule
respects the zero bound everywhere (`Φ ≥ β` on `(0, ∞)`), then for every `Π₀ > 0` there is an
equilibrium with initial inflation `Π₀` — a continuum of equilibria, one for each `Π₀`. -/
theorem continuum_of_equilibria {r : ℝ} {Φ : ℝ → ℝ} {Pm1 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hbound : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (Pi0 : ℝ) (hPi0 : 0 < Pi0) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ infl Pm1 P 0 = Pi0 := by
  have hr1 : 0 < 1 + r := by linarith
  have hpos : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih => rw [orbit_succ]; exact lt_of_lt_of_le (inv_pos.mpr hr1) (hbound _ ih)
  obtain ⟨P, i, s, D, h, -, hinfl, -⟩ := equilibrium_exists D0 hr hPm1 hPi0 fun t =>
    hbound _ (hpos t)
  exact ⟨P, i, s, D, h, by simpa using hinfl 0⟩

/-- Cochrane (2023), p. 379, "deflationary equilibria that start anywhere below `Π*` and approach
`Π_L` are also valid equilibria, as is `Π_L` itself": under the hypotheses of
`deflation_tendsto_lower` with `Π_L ≥ β`, every `Π₀ ∈ [Π_L, Π*)` is the initial inflation of an
equilibrium (passive fiscal policy) whose inflation converges to `Π_L`. -/
theorem deflationary_equilibria {r : ℝ} {Φ : ℝ → ℝ} {Pm1 PL Pis Pi0 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hβPL : (1 + r)⁻¹ ≤ PL) (hcont : ContinuousOn Φ (Set.Icc PL Pis))
    (hfix : Φ PL = PL) (hbelow : ∀ x, PL < x → x < Pis → Φ x < x)
    (hge : ∀ x, PL < x → x < Pis → PL ≤ Φ x) (h0 : Pi0 ∈ Set.Ico PL Pis) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ infl Pm1 P 0 = Pi0 ∧
      Tendsto (fun t => infl Pm1 P t) atTop (𝓝 PL) := by
  have hr1 : 0 < 1 + r := by linarith
  have hPL0 : 0 < PL := lt_of_lt_of_le (inv_pos.mpr hr1) hβPL
  -- the orbit stays in `[Π_L, Π₀]` and converges to `Π_L`
  have horb : (∀ t, PL ≤ Φ^[t] Pi0) ∧ Tendsto (fun t => Φ^[t] Pi0) atTop (𝓝 PL) := by
    rcases h0.1.lt_or_eq with hlt | heq
    · have := deflation_tendsto_lower (infl := fun t => Φ^[t] Pi0) hcont hfix hbelow hge
        (fun t => orbit_succ Φ Pi0 t) (by simpa using (⟨hlt, h0.2⟩ : Pi0 ∈ Set.Ioo PL Pis))
      exact ⟨fun t => (this.2.1 t).1, this.2.2⟩
    · have hc : ∀ t, Φ^[t] Pi0 = PL := by
        intro t
        induction t with
        | zero => simp [heq]
        | succ n ih => rw [orbit_succ, ih, hfix]
      refine ⟨fun t => (hc t).ge, ?_⟩
      simp only [hc]
      exact tendsto_const_nhds
  obtain ⟨P, i, s, D, h, -, hinfl, -⟩ := equilibrium_exists (Φ := Φ) (Pi0 := Pi0) D0 hr hPm1
    (by linarith [h0.1]) fun t => by rw [← orbit_succ Φ Pi0 t]; exact hβPL.trans (horb.1 (t + 1))
  refine ⟨P, i, s, D, h, by simpa using hinfl 0, ?_⟩
  simp only [hinfl]
  exact horb.2

/-! ## p. 379: the 2%/1% example -/

/-- Cochrane (2023), p. 379: a linear Taylor rule `Φ(Π) = Π* + φ(Π − Π*)` truncated at the zero
bound, `Φ(Π) = max(β, Π* + φ(Π − Π*))`. -/
noncomputable def truncRule (β Pis φ : ℝ) (x : ℝ) : ℝ := max β (Pis + φ * (x - Pis))

/-- Cochrane (2023), p. 379: for `β < Π*` and `φ > 1`, the truncated rule has the active steady
state `Π*` with slope `φ`, the zero-bound steady state `Π_L = β`, and respects the bound. -/
theorem truncRule_props {β Pis φ : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) :
    truncRule β Pis φ Pis = Pis ∧ truncRule β Pis φ β = β ∧ (∀ x, β ≤ truncRule β Pis φ x) ∧
      HasDerivAt (truncRule β Pis φ) φ Pis ∧ Continuous (truncRule β Pis φ) := by
  refine ⟨by simp [truncRule, hβPis.le], ?_, fun x => le_max_left _ _, ?_, by
    unfold truncRule; fun_prop⟩
  · unfold truncRule
    apply max_eq_left
    nlinarith
  · have h : HasDerivAt (fun x => Pis + φ * (x - Pis)) φ Pis := by
      simpa using (((hasDerivAt_id Pis).sub_const Pis).const_mul φ).const_add Pis
    refine h.congr_of_eventuallyEq ?_
    have hlt : Pis - (Pis - β) / φ < Pis := by
      have : 0 < (Pis - β) / φ := div_pos (by linarith) (by linarith)
      linarith
    filter_upwards [Ioi_mem_nhds hlt] with x hx
    unfold truncRule
    apply max_eq_right
    have hx' : Pis - x < (Pis - β) / φ := by simp only [Set.mem_Ioi] at hx; linarith
    rw [lt_div_iff₀ (by linarith)] at hx'
    nlinarith

/-- Cochrane (2023), p. 379: along a path of the truncated rule starting at `Π₀ ≥ β`, the gap
below target is `Π* − Π_t = min(Π* − β, φᵗ(Π* − Π₀))`. -/
theorem truncRule_orbit_gap {β Pis φ x0 : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) (hx0 : β ≤ x0)
    (t : ℕ) :
    Pis - (truncRule β Pis φ)^[t] x0 = min (Pis - β) (φ ^ t * (Pis - x0)) := by
  induction t with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    exact (min_eq_right (by linarith)).symm
  | succ n ih =>
    rw [orbit_succ]
    have hstep : Pis - truncRule β Pis φ ((truncRule β Pis φ)^[n] x0) =
        min (Pis - β) (φ * (Pis - (truncRule β Pis φ)^[n] x0)) := by
      unfold truncRule
      rw [← min_sub_sub_left]
      congr 1
      ring
    rw [hstep, ih, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ φ), pow_succ]
    have hA : Pis - β ≤ φ * (Pis - β) := by nlinarith
    rw [← min_assoc, min_eq_left hA]
    congr 1
    ring

/-- Cochrane (2023), p. 379, "paths that start at `Π_t = 1.99%` and drift down to … `i_t = 0%`,
and stay there": with the truncated rule, every path starting in `[β, Π*)` reaches the zero
bound `Π = β` (`i = 0`) in finite time and stays there. -/
theorem truncRule_hits_bound {β Pis φ x0 : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) (hx0 : β ≤ x0)
    (hx0P : x0 < Pis) : ∃ T, ∀ t, T ≤ t → (truncRule β Pis φ)^[t] x0 = β := by
  have hg : 0 < Pis - x0 := by linarith
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((Pis - β) / (Pis - x0)) hφ
  refine ⟨T, fun t ht => ?_⟩
  have h1 : Pis - β ≤ φ ^ t * (Pis - x0) := by
    rw [div_lt_iff₀ hg] at hT
    have := pow_le_pow_right₀ hφ.le ht
    nlinarith
  have := truncRule_orbit_gap hβPis hφ hx0 t
  rw [min_eq_left h1] at this
  linarith

/-- Cochrane (2023), p. 379, the example: "if `Π* = 2%` … and the real interest rate is `r = 1%`,
then we have to rule out paths that start at `Π_t = 1.99%` and drift down to `Π_t = −1%`,
`i_t = 0%`, and stay there". With `β = 1/1.01`, `Π* = 1.02` and the truncated rule with `φ = 3/2`,
the path from `Π₀ = 1.0199` is an equilibrium path that reaches `Π = β` in finite time and stays
there, with `i = 0` and net inflation `β − 1 = −1/101 ∈ (−1%, −0.99%)`. -/
theorem example_two_one :
    (∃ T, ∀ t, T ≤ t →
      (truncRule (1 + 1 / 100)⁻¹ (102 / 100) (3 / 2))^[t] (10199 / 10000) = (1 + 1 / 100)⁻¹) ∧
      (1 + 1 / 100 : ℝ) * (1 + 1 / 100)⁻¹ - 1 = 0 ∧
      (1 + 1 / 100 : ℝ)⁻¹ - 1 = -1 / 101 ∧ (-1 / 100 : ℝ) < -1 / 101 ∧
      (-1 / 101 : ℝ) < -99 / 10000 := by
  refine ⟨truncRule_hits_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Cochrane (2023), p. 380, "if negative real interest rates endure, `Π_L` may occur at, say, 1%
inflation, only one percentage point below the 2% target, corresponding to a −1% real rate": with
`r = −1%` the zero-bound inflation rate is `β − 1 = 1/99 ≈ 1.01%`, about one percentage point
below `2%`. -/
theorem negative_real_rate_example :
    (1 + (-1 / 100) : ℝ)⁻¹ - 1 = 1 / 99 ∧ (101 / 10000 : ℝ) < 1 / 99 ∧ (1 / 99 : ℝ) < 102 / 10000 ∧
      (98 / 10000 : ℝ) < 2 / 100 - 1 / 99 ∧ (2 / 100 : ℝ) - 1 / 99 < 99 / 10000 := by
  norm_num

end Cochrane.NewKeynesianSelection.LowerBound

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium-selection patches

Cochrane (2023), Chapter 16, §16.10.1–16.10.6, pp. 383–394, with the Online Appendix A3,
§3.1.1–3.1.2, pp. 613–616. Perfect foresight throughout, except the minimum-state-variable
results, which hold for an arbitrary `ExpectationSystem`.

## Main results

* §16.10.1 (MSV), with (16.4) the canonical `SimplestModel.Eq164` and the MSV solution
  `SimplestModel.ar1Pi` (`SimplestModel.ar1Pi_eq164`): `msv_unique`, `msv_iff` (among
  `π_t = c u_t`, the unique
  solution of (16.4) is `−u_t/(φ − η)`, for every `φ ≠ η`, including passive `|φ| < 1`);
  `msv_none_of_eq`; `pf_explosive_not_msv`, `pf_passive_bounded_not_msv` (other solutions are not
  of MSV form, bounded ones included when `|φ| ≤ 1`); `msv_nonlinear_counterexample` (with a
  nonlinear `f`, `π_t = f(u_t)` admits explosive solutions under perfect foresight).
* §16.10.2 (stabilisations and ACK): `quantity_theory_growth`; the overlap regime `ACKEq`,
  `ack_inconsistent`, `ack_bounded`, `ack_iff`, `ack_prunes_inflation`, `ack_keeps_deflation`,
  `woodford_backstop_prunes`; the separated regime `StabEq`, `stabPath`, `stab_exists`,
  `stab_unique`, `stop_not_rule_out` ("stopping an inflation does not rule it out").
* §16.10.3 (fiscal trimming): BSGU `bsgu_real_debt`, `bsgu_tvc_violated`,
  `bsgu_no_equilibrium_to_lower`, `bsgu_target_survives`; Woodford's `μ̄` rule in Cochrane's
  notation `mubar_tvc_step`, `mubar_tvc_violated`, `mubar_deflation_violates`,
  `mubar_target_tvc_iff`; and the Woodford Chapter 2 versions restated in `WoodfordMuBar`.
* §16.10.4 (Bassetto): `bassetto_exit`, `bassetto_no_equilibrium`, `linear_rule_exit`.
* §16.10.5 (weird rules): `vertical_rule_exit`, `v_rule_unbounded`, `v_rule_unique_bounded`,
  `vRule`, `vRule_props`, `ahJump`, `ahJump_props`; tangency counterexample `tangentRule`,
  `tangent_rule_converges`.
* (16.31)–(16.32) (Schmitt-Grohé–Uribe): `eq1632_iff`, `eq1632_iff_path45`; the
  Schmitt-Grohé–Uribe example restated from Woodford Chapter 2 in `SGU`; and the correction
  `successor_exists_of_bounded_rule` (with a bounded continuous rule and `u_c ∘ L` continuous and
  positive on the range of rates, (16.32) always has a finite successor;
  `path_exists_of_bounded_rule`); and the converse example `bounded_rule_explosion` (bounded
  rule, `L(i) = 5 − i`, `u_c = 1/m`: no successor for `Π_t ∈ (1, 3/2)`).
* §16.10.6 (Sims 1994): `sims_tvc_violated`, `sims_tvc_violated_of_eventually_beta`,
  `sims_no_bite_above_beta`, `sims_slow_counterexample`.
* A3 §3.1.1–3.1.2: `a3_helicopter_pv`, `a3_helicopter_tvc_violated`, `a3_omo_real_const`,
  `a3_omo_nominal`, `a3_omo_debt_negative`, `a3_omo_tvc`.
-/

namespace Cochrane.NewKeynesianSelection.SelectionPatches

open Filter Topology
open Cochrane.NewKeynesianSelection.GlobalDynamics
open Cochrane.NewKeynesianSelection.LowerBound

/-! ## §16.10.1 Minimum state variables -/

/-- Cochrane (2023), §16.10.1, p. 385, "the only such solution is the 'locally bounded' choice
(16.6) `π_t = −u_t/(φ − η)`": if `u` is AR(1) and not identically zero, and `π_t = c u_t` solves
(16.4), then `φ ≠ η` and `c = −1/(φ − η)`. No restriction on `φ` is needed. -/
theorem msv_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {φ η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0)
    (h : SimplestModel.Eq164 𝔼 φ u (fun t => c • u t)) : φ ≠ η ∧ c = -(φ - η)⁻¹ := by
  obtain ⟨t, ω, hω⟩ := hne
  have ht := congrFun (h t) ω
  rw [ExpectationSystem.E_smul, hu.2 t] at ht
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at ht
  have hkey : (c * (η - φ) - 1) * u t ω = 0 := by linarith
  have hc : c * (η - φ) = 1 := by
    have := (mul_eq_zero.mp hkey).resolve_right hω
    linarith
  have hφη : φ ≠ η := by
    intro he; rw [he, sub_self, mul_zero] at hc; exact zero_ne_one hc
  refine ⟨hφη, ?_⟩
  have : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  field_simp
  linarith

/-- Cochrane (2023), §16.10.1, p. 385: for AR(1) `u` not identically zero, `π_t = c u_t` solves
(16.4) if and only if `φ ≠ η` and `c = −1/(φ − η)`. The MSV criterion selects this solution for
every `φ ≠ η` — also in the passive case `|φ| < 1`, where it is not needed to rule out
explosions (so it is a selection device independent of the Taylor principle). -/
theorem msv_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) {φ η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0) :
    SimplestModel.Eq164 𝔼 φ u (fun t => c • u t) ↔ φ ≠ η ∧ c = -(φ - η)⁻¹ := by
  refine ⟨msv_unique 𝔼 hu hne, ?_⟩
  rintro ⟨hφη, rfl⟩
  exact SimplestModel.ar1Pi_eq164 𝔼 hφη hu

/-- Cochrane (2023), §16.10.1, p. 385: if `φ = η` (and `u` is not identically zero), (16.4) has
no MSV solution at all. -/
theorem msv_none_of_eq {Ω : Type*} (𝔼 : ExpectationSystem Ω) {η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0) :
    ¬ SimplestModel.Eq164 𝔼 η u (fun t => c • u t) :=
  fun h => (msv_unique 𝔼 hu hne h).1 rfl

/-- Cochrane (2023), eq. (16.4), p. 364: under perfect foresight (16.4) is the deterministic
recursion `π_{t+1} = φπ_t + u_t`. -/
theorem simpleModel_pf_iff {φ : ℝ} {u infl : ℕ → Unit → ℝ} :
    SimplestModel.Eq164 perfectForesight φ u infl ↔
      ∀ t, infl (t + 1) () = φ * infl t () + u t () := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · simpa [perfectForesight] using congrFun h ()
  · funext ω
    simpa [perfectForesight] using h

/-- Cochrane (2023), §16.10.1, p. 385, "the minimum state variable criterion rules out the
explosive and sunspot solutions": under perfect foresight with `u_t = ηᵗu₀`, `φ ≠ η`, each
`π_t = −u_t/(φ − η) + φᵗδ₀` solves (16.4), and for `δ₀ ≠ 0` it is not of the form `c u_t`. -/
theorem pf_explosive_not_msv {φ η u0 δ0 : ℝ} (hφη : φ ≠ η) (hδ : δ0 ≠ 0) :
    (∀ t : ℕ, (-(φ - η)⁻¹ * (η ^ (t + 1) * u0) + φ ^ (t + 1) * δ0) =
      φ * (-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0) + η ^ t * u0) ∧
      ¬ ∃ c : ℝ, ∀ t : ℕ, -(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0 = c * (η ^ t * u0) := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  refine ⟨fun t => ?_, ?_⟩
  · field_simp
    ring
  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h0 h1
    have : (φ - η) * δ0 = 0 := by linear_combination h1 - η * h0
    rcases mul_eq_zero.mp this with h | h
    · exact hne h
    · exact hδ h

/-- Cochrane (2023), §16.10.1, p. 385, and §16.1, p. 364 ("if `‖φ‖ < 1`, this economy is stable
… but it remains indeterminate"): with `|φ| ≤ 1`, `|η| ≤ 1`, the non-MSV perfect-foresight
solutions `π_t = −u_t/(φ − η) + φᵗδ₀` are bounded, so the MSV criterion, not boundedness, is what
selects `−u_t/(φ − η)` in the passive case. -/
theorem pf_passive_bounded_not_msv {φ η u0 δ0 : ℝ} (hφ : |φ| ≤ 1) (hη : |η| ≤ 1) (t : ℕ) :
    |-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0| ≤ |(φ - η)⁻¹| * |u0| + |δ0| := by
  have h1 : |η ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hη
  have h2 : |φ ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hφ
  calc |-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0|
      ≤ |-(φ - η)⁻¹ * (η ^ t * u0)| + |φ ^ t * δ0| := abs_add_le _ _
    _ = |(φ - η)⁻¹| * (|η ^ t| * |u0|) + |φ ^ t| * |δ0| := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul]
    _ ≤ |(φ - η)⁻¹| * (1 * |u0|) + 1 * |δ0| := by
        gcongr
    _ = |(φ - η)⁻¹| * |u0| + |δ0| := by ring

/-- Cochrane (2023), §16.10.1, p. 385: the power identity behind the nonlinear MSV counterexample:
for `0 < η ≠ 1`, `φ > 0`, `u₀ > 0` and `κ = log φ/log η`, `(ηᵗu₀)^κ = φᵗ u₀^κ`. -/
theorem rpow_orbit {φ η u0 : ℝ} (hη0 : 0 < η) (hη1 : η ≠ 1) (hφ : 0 < φ) (hu0 : 0 < u0)
    (t : ℕ) :
    (η ^ t * u0) ^ (Real.log φ / Real.log η) = φ ^ t * u0 ^ (Real.log φ / Real.log η) := by
  have hlog : Real.log η ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h' | h' | h'
    · linarith
    · exact hη1 h'
    · linarith
  have hκ : η ^ (Real.log φ / Real.log η) = φ := by
    rw [Real.rpow_def_of_pos hη0, mul_div_cancel₀ _ hlog, Real.exp_log hφ]
  rw [Real.mul_rpow (pow_nonneg hη0.le t) hu0.le, ← Real.rpow_natCast η t, ← Real.rpow_mul hη0.le,
    mul_comm (t : ℝ), Real.rpow_mul hη0.le, hκ, Real.rpow_natCast]

/-- Cochrane (2023), §16.10.1, p. 385, imprecision: "the minimum state variable criterion says to
pick `π_t = f(u_t)`. The only such solution is … (16.6)" holds for linear `f` (`msv_iff`) but not
for arbitrary `f` under perfect foresight. With `u_t = ηᵗu₀`, `0 < η ≠ 1`, `u₀ > 0`, `φ > 0`,
`φ ≠ η`, the function `f(x) = −x/(φ − η) + x^κ`, `κ = log φ/log η`, gives a solution
`π_t = f(u_t)` of (16.4) that differs from (16.6) by `φᵗu₀^κ`, which explodes when `φ > 1`. -/
theorem msv_nonlinear_counterexample {φ η u0 : ℝ} (hη0 : 0 < η) (hη1 : η ≠ 1) (hφ : 0 < φ)
    (hφη : φ ≠ η) (hu0 : 0 < u0) :
    let f : ℝ → ℝ := fun x => -(φ - η)⁻¹ * x + x ^ (Real.log φ / Real.log η)
    (∀ t : ℕ, f (η ^ (t + 1) * u0) = φ * f (η ^ t * u0) + η ^ t * u0) ∧
      (∀ t : ℕ, f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0)) =
        φ ^ t * u0 ^ (Real.log φ / Real.log η)) ∧
      (1 < φ → Tendsto (fun t : ℕ => f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0))) atTop
        atTop) := by
  intro f
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  have hdev : ∀ t : ℕ, f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0)) =
      φ ^ t * u0 ^ (Real.log φ / Real.log η) := fun t => by
    simp only [f, rpow_orbit hη0 hη1 hφ hu0 t]
    ring
  refine ⟨fun t => ?_, hdev, fun hφ1 => ?_⟩
  · simp only [f, rpow_orbit hη0 hη1 hφ hu0 t, rpow_orbit hη0 hη1 hφ hu0 (t + 1)]
    field_simp
    ring
  · simp only [hdev]
    exact (tendsto_pow_atTop_atTop_of_one_lt hφ1).atTop_mul_const
      (Real.rpow_pos_of_pos hu0 _)

/-! ## §16.10.2 Stabilisations and threats -/

/-- Cochrane (2023), §16.10.2, p. 389, "an economy with constant velocity and hence money demand
`M_t V = P_t y`": money growth equals inflation, `M_{t+1}/M_t = P_{t+1}/P_t`; so the money-growth
rule `M_{T+1}/M_T = μ` is the inflation target `Π_{T+1} = μ`. -/
theorem quantity_theory_growth {V y : ℝ} {M P : ℕ → ℝ} (hV : 0 < V) (hy : 0 < y)
    (hP : ∀ t, 0 < P t) (hqt : ∀ t, M t * V = P t * y) (t : ℕ) :
    M (t + 1) / M t = P (t + 1) / P t := by
  have hM : ∀ t, M t = P t * y / V := fun t => by rw [← hqt t]; field_simp
  rw [hM, hM]
  have := hP t
  field_simp

/-- Cochrane (2023), §16.10.2, p. 389 (Atkeson, Chari and Kehoe 2010; Christiano and Takahashi
2018): perfect-foresight equilibrium of the regime "Taylor rule `1 + i_t = (1 + r)Φ(Π_t)` until
and including the first period `T` with `Π_T > Π_U`; money-growth rule `Π_{t+1} = μ` from `T`
on": the two rules overlap at `T`. -/
def ACKEq (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < infl t) ∧ (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, (∀ s < t, infl s ≤ PiU) → 1 + i t = (1 + r) * Φ (infl t)) ∧
    ∀ t, (∃ s ≤ t, PiU < infl s) → infl (t + 1) = μ

/-- Cochrane (2023), §16.10.2, p. 389, "an equilibrium cannot form at period `T`": at the first
period with `Π_T > Π_U`, an ACK equilibrium needs `Φ(Π_T) = μ` (a very high rate `i_T` and low
inflation `Π_{T+1} = μ` cannot both satisfy the Fisher equation). -/
theorem ack_inconsistent {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (h : ACKEq r Φ PiU μ infl i) {T : ℕ} (hT : PiU < infl T) (hbefore : ∀ s < T, infl s ≤ PiU) :
    Φ (infl T) = μ := by
  obtain ⟨-, -, hfis, htay, hmon⟩ := h
  have h1 := hmon T ⟨T, le_rfl, hT⟩
  rw [hfis, htay T hbefore, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] at h1
  exact h1

/-- Cochrane (2023), §16.10.2, p. 389, "the inflationary path leading to `T` is not an
equilibrium": if `Φ(Π) ≠ μ` whenever `Π > Π_U`, no ACK equilibrium ever exceeds `Π_U`. -/
theorem ack_bounded {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) (h : ACKEq r Φ PiU μ infl i) : ∀ t, infl t ≤ PiU := by
  by_contra hcon
  push Not at hcon
  classical
  let T := Nat.find hcon
  have hT : PiU < infl T := Nat.find_spec hcon
  have hbefore : ∀ s < T, infl s ≤ PiU := fun s hs => not_lt.mp (Nat.find_min hcon hs)
  exact hΦμ _ hT (ack_inconsistent hr h hT hbefore)

/-- Cochrane (2023), §16.10.2, p. 389: when `Φ(Π) ≠ μ` above `Π_U`, the ACK equilibria are
exactly the Taylor-rule equilibria (16.29) that never exceed `Π_U`. -/
theorem ack_iff {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) :
    ACKEq r Φ PiU μ infl i ↔
      (∀ t, 0 < infl t ∧ infl t ≤ PiU) ∧ (∀ t, infl (t + 1) = Φ (infl t)) ∧
        (∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, (1 + r)⁻¹ ≤ Φ (infl t) := by
  constructor
  · intro h
    have hb := ack_bounded hr hΦμ h
    obtain ⟨hpos, hi, hfis, htay, -⟩ := h
    have htay' : ∀ t, 1 + i t = (1 + r) * Φ (infl t) := fun t => htay t fun s _ => hb s
    have hdyn : ∀ t, infl (t + 1) = Φ (infl t) := fun t => by
      rw [hfis, htay', ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    refine ⟨fun t => ⟨hpos t, hb t⟩, hdyn, htay', fun t => ?_⟩
    rw [← hdyn]
    exact (Hyperinflation.zero_bound_iff_scalar hr (hfis t)).mp (hi t)
  · rintro ⟨hb, hdyn, htay, hbd⟩
    refine ⟨fun t => (hb t).1, fun t => ?_, fun t => ?_, fun t _ => htay t, ?_⟩
    · have := (rule_respects_bound_iff (x := infl t) (Φ := Φ) hr).mpr (hbd t)
      rw [← htay] at this; linarith
    · rw [htay, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, hdyn]
    · rintro t ⟨s, -, hs⟩
      exact absurd (hb s).2 (not_le.mpr hs)

/-- Cochrane (2023), §16.10.2, p. 389: the ACK regime prunes the inflationary equilibria of
Figure 16.2. If `Φ(Π) > Π` above `Π*` with `Φ` continuous there, `Π* ≤ Π_U`, and `Φ(Π) ≠ μ` above
`Π_U`, then no ACK equilibrium starts above `Π*`. -/
theorem ack_prunes_inflation {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU μ : ℝ} {infl i : ℕ → ℝ}
    (hr : 0 < 1 + r) (habove : ∀ x, Pis < x → x < Φ x) (hcont : ContinuousOn Φ (Set.Ioi Pis))
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) (h : ACKEq r Φ PiU μ infl i) : infl 0 ≤ Pis := by
  by_contra h0
  push Not at h0
  have hdyn := ((ack_iff hr hΦμ).mp h).2.1
  have hbd := ((ack_iff hr hΦμ).mp h).1
  have hup : ∀ t, Pis < infl t ∧ infl t < infl (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hdyn]; exact habove _ h0⟩
    | succ n ih =>
      have h1 : Pis < infl (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hdyn (n + 1)]; exact habove _ h1⟩
  have hmono : Monotone infl := monotone_nat_of_le_succ fun t => (hup t).2.le
  rcases monotone_orbit_atTop_or_fixed hdyn hmono with htop | ⟨L, -, hLb, hfix⟩
  · obtain ⟨t, ht⟩ := (htop.eventually (eventually_gt_atTop PiU)).exists
    linarith [(hbd t).2]
  · have hL : Pis < L := lt_of_lt_of_le h0 (hLb 0)
    have := hfix (hcont.continuousAt (Ioi_mem_nhds hL))
    linarith [habove L hL]

/-- Cochrane (2023), §16.10.2, p. 389: the ACK regime does not prune the deflationary paths: if
`Φ` is monotone on `(0, Π*]`, `Φ(Π*) = Π*`, `Φ ≥ β` there and `Π* ≤ Π_U`, every `Π₀ ∈ (0, Π*]`
starts an ACK equilibrium (the plain Taylor-rule path). -/
theorem ack_keeps_deflation {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hmono : MonotoneOn Φ (Set.Ioc 0 Pis)) (hfix : Φ Pis = Pis)
    (hbd : ∀ x ∈ Set.Ioc 0 Pis, (1 + r)⁻¹ ≤ Φ x) (hPiU : Pis ≤ PiU) (h0 : Pi0 ∈ Set.Ioc 0 Pis) :
    ACKEq r Φ PiU μ (fun t => Φ^[t] Pi0) (fun t => (1 + r) * Φ (Φ^[t] Pi0) - 1) := by
  have hmem : ∀ t, Φ^[t] Pi0 ∈ Set.Ioc 0 Pis := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ n ih =>
      rw [orbit_succ]
      exact ⟨lt_of_lt_of_le (inv_pos.mpr hr) (hbd _ ih),
        hfix ▸ hmono ih ⟨by linarith [ih.2, ih.1], le_rfl⟩ ih.2⟩
  refine ⟨fun t => (hmem t).1, fun t => ?_, fun t => ?_, fun t _ => by ring, ?_⟩
  · have := (rule_respects_bound_iff (x := Φ^[t] Pi0) (Φ := Φ) hr).mpr (hbd _ (hmem t))
    exact this
  · dsimp only
    rw [orbit_succ]; field_simp; ring
  · rintro t ⟨s, -, hs⟩
    exact absurd ((hmem s).2.trans hPiU) (not_le.mpr hs)

/-- Cochrane (2023), §16.10.2, pp. 388–389, Woodford's commodity backstop under a Taylor rule:
"if a government continues to follow the Taylor rule … even after it has switched to a commodity
standard that requires low nominal interest rates, then, yes, no equilibrium can form". A
commodity peg fixes the price level, `Π_{T+1} = 1`: the ACK structure with `μ = 1`; with
`1 ≤ Π* ≤ Π_U` and `Φ(Π) > Π` above `Π*` (continuous), no equilibrium starts above `Π*`. -/
theorem woodford_backstop_prunes {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU : ℝ} {infl i : ℕ → ℝ}
    (hr : 0 < 1 + r) (hPis1 : 1 ≤ Pis) (hPiU : Pis ≤ PiU) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (h : ACKEq r Φ PiU 1 infl i) : infl 0 ≤ Pis :=
  ack_prunes_inflation hr habove hcont
    (fun x hx => ne_of_gt (lt_trans (by linarith) (habove x (by linarith)))) h

/-- Cochrane (2023), §16.10.2, p. 387, "if the government separates by one period the inflation
and its stabilization": the Taylor rule applies at `t` while `Π_s ≤ Π_U` for all `s ≤ t`; from
the first period `T` with `Π_T > Π_U` on, only the money-growth rule `Π_{t+1} = μ` applies. -/
def StabEq (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < infl t) ∧ (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, (∀ s ≤ t, infl s ≤ PiU) → 1 + i t = (1 + r) * Φ (infl t)) ∧
    ∀ t, (∃ s ≤ t, PiU < infl s) → infl (t + 1) = μ

/-- Cochrane (2023), §16.10.2, p. 387: the stabilised path — the Taylor orbit `Φ^[t](Π₀)` until
it first exceeds `Π_U`, and `μ` from the next period on. -/
noncomputable def stabPath (Φ : ℝ → ℝ) (PiU μ Pi0 : ℝ) (t : ℕ) : ℝ :=
  if ∃ s < t, PiU < Φ^[s] Pi0 then μ else Φ^[t] Pi0

/-- Cochrane (2023), §16.10.2, p. 387: while the stabilised path has stayed at or below `Π_U`, it
coincides with the Taylor orbit, and so has the orbit. -/
theorem stabPath_taylor {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} {t : ℕ}
    (h : ∀ s ≤ t, stabPath Φ PiU μ Pi0 s ≤ PiU) :
    (∀ s ≤ t, Φ^[s] Pi0 ≤ PiU) ∧ ∀ s ≤ t, stabPath Φ PiU μ Pi0 s = Φ^[s] Pi0 := by
  have hno : ∀ s ≤ t, Φ^[s] Pi0 ≤ PiU := by
    by_contra hcon
    push Not at hcon
    classical
    have hex : ∃ s, s ≤ t ∧ PiU < Φ^[s] Pi0 := hcon
    let s0 := Nat.find hex
    have hs0 := Nat.find_spec hex
    have hmin : ∀ s < s0, Φ^[s] Pi0 ≤ PiU := fun s hs => by
      by_contra hc
      exact Nat.find_min hex hs ⟨by have := hs0.1; omega, not_le.mp hc⟩
    have heq : stabPath Φ PiU μ Pi0 s0 = Φ^[s0] Pi0 := by
      unfold stabPath
      rw [ite_eq_right_iff]
      rintro ⟨s, hs, hlt⟩
      exact absurd (hmin s hs) (not_le.mpr hlt)
    have := h s0 hs0.1
    rw [heq] at this
    exact absurd this (not_le.mpr hs0.2)
  refine ⟨hno, fun s hs => ?_⟩
  unfold stabPath
  rw [ite_eq_right_iff]
  rintro ⟨s', hs', hlt⟩
  exact absurd (hno s' (by omega)) (not_le.mpr hlt)

/-- Cochrane (2023), §16.10.2, p. 387: once the stabilised path has exceeded `Π_U`, it equals
`μ` from the next period on. -/
theorem stabPath_money {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} {t : ℕ}
    (h : ∃ s ≤ t, PiU < stabPath Φ PiU μ Pi0 s) : stabPath Φ PiU μ Pi0 (t + 1) = μ := by
  obtain ⟨s, hs, hlt⟩ := h
  unfold stabPath
  rw [ite_eq_left_iff]
  intro hc
  exfalso
  apply hc
  by_cases hex : ∃ s' < s, PiU < Φ^[s'] Pi0
  · obtain ⟨s', hs', h'⟩ := hex
    exact ⟨s', by omega, h'⟩
  · unfold stabPath at hlt
    simp only [hex, ↓reduceIte] at hlt
    exact ⟨s, by omega, hlt⟩

/-- Cochrane (2023), §16.10.2, p. 387: the stabilised path is an equilibrium of the separated
regime for every `Π₀ > 0`, provided the Taylor rule respects the zero bound (`Φ ≥ β` on `(0, ∞)`)
and the money-growth target does (`μ ≥ β`). -/
theorem stab_exists {r : ℝ} {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hΦ : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (hμ : (1 + r)⁻¹ ≤ μ) (hPi0 : 0 < Pi0) :
    StabEq r Φ PiU μ (stabPath Φ PiU μ Pi0)
      (fun t => (1 + r) * stabPath Φ PiU μ Pi0 (t + 1) - 1) ∧
      stabPath Φ PiU μ Pi0 0 = Pi0 := by
  have hβ : 0 < (1 + r)⁻¹ := inv_pos.mpr hr
  have horb : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih => rw [orbit_succ]; exact lt_of_lt_of_le hβ (hΦ _ ih)
  have hge : ∀ t, (1 + r)⁻¹ ≤ stabPath Φ PiU μ Pi0 (t + 1) := by
    intro t
    unfold stabPath
    split_ifs
    · exact hμ
    · rw [orbit_succ]; exact hΦ _ (horb t)
  have hpos : ∀ t, 0 < stabPath Φ PiU μ Pi0 t := by
    intro t
    cases t with
    | zero => simp [stabPath, hPi0]
    | succ n => exact lt_of_lt_of_le hβ (hge n)
  refine ⟨⟨hpos, fun t => ?_, fun t => ?_, fun t ht => ?_, fun t ht => stabPath_money ht⟩,
    by simp [stabPath]⟩
  · have := (rule_respects_bound_iff (x := 0) (Φ := fun _ => stabPath Φ PiU μ Pi0 (t + 1))
      hr).mpr (hge t)
    exact this
  · field_simp; ring
  · obtain ⟨hno, heq⟩ := stabPath_taylor ht
    have h1 : stabPath Φ PiU μ Pi0 (t + 1) = Φ^[t + 1] Pi0 := by
      unfold stabPath
      rw [ite_eq_right_iff]
      rintro ⟨s, hs, hlt⟩
      exact absurd (hno s (by omega)) (not_le.mpr hlt)
    dsimp only
    rw [h1, heq t le_rfl, orbit_succ]
    ring

/-- Cochrane (2023), §16.10.2, p. 387: the separated regime determines the path given `Π₀`: two
equilibria with the same initial inflation coincide. -/
theorem stab_unique {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {a b ia ib : ℕ → ℝ} (hr : 0 < 1 + r)
    (ha : StabEq r Φ PiU μ a ia) (hb : StabEq r Φ PiU μ b ib) (h0 : a 0 = b 0) :
    a = b ∧ ia = ib := by
  obtain ⟨-, -, hfa, hta, hma⟩ := ha
  obtain ⟨-, -, hfb, htb, hmb⟩ := hb
  have hdyn_a : ∀ t, (∀ s ≤ t, a s ≤ PiU) → a (t + 1) = Φ (a t) := fun t h => by
    rw [hfa, hta t h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hdyn_b : ∀ t, (∀ s ≤ t, b s ≤ PiU) → b (t + 1) = Φ (b t) := fun t h => by
    rw [hfb, htb t h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hall : ∀ t, ∀ s ≤ t, a s = b s := by
    intro t
    induction t with
    | zero => intro s hs; rw [Nat.le_zero.mp hs]; exact h0
    | succ n ih =>
      intro s hs
      rcases Nat.lt_or_ge s (n + 1) with hlt | hge
      · exact ih s (by omega)
      · have hs' : s = n + 1 := by omega
        subst hs'
        by_cases hc : ∀ s ≤ n, a s ≤ PiU
        · have hc' : ∀ s ≤ n, b s ≤ PiU := fun s hs => (ih s hs) ▸ hc s hs
          rw [hdyn_a n hc, hdyn_b n hc', ih n le_rfl]
        · push Not at hc
          obtain ⟨s, hs, hlt⟩ := hc
          rw [hma n ⟨s, hs, hlt⟩, hmb n ⟨s, hs, (ih s hs) ▸ hlt⟩]
  have hab : a = b := funext fun t => hall t t le_rfl
  refine ⟨hab, funext fun t => ?_⟩
  have h1 := hfa t
  have h2 := hfb t
  rw [hab] at h1
  rw [h1] at h2
  have := mul_left_cancel₀ (inv_ne_zero hr.ne') h2
  linarith

/-- Cochrane (2023), §16.10.2, p. 386, "if a multiple-equilibrium inflation or deflation breaks
out, and if the government successfully stops the inflation … then the inflation and its end
remain an equilibrium path": in the separated regime every `Π₀ > 0` starts exactly one
equilibrium; it follows the Taylor orbit up to the first period `T` at which the orbit exceeds
`Π_U`, and is stabilised at `μ` afterwards. Stopping an inflation does not rule it out. -/
theorem stop_not_rule_out {r : ℝ} {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hΦ : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (hμ : (1 + r)⁻¹ ≤ μ) (hPi0 : 0 < Pi0) :
    (∃ infl i : ℕ → ℝ, StabEq r Φ PiU μ infl i ∧ infl 0 = Pi0) ∧
      (∀ infl i infl' i' : ℕ → ℝ, StabEq r Φ PiU μ infl i → StabEq r Φ PiU μ infl' i' →
        infl 0 = Pi0 → infl' 0 = Pi0 → infl = infl') ∧
      ∀ T, PiU < Φ^[T] Pi0 → (∀ s < T, Φ^[s] Pi0 ≤ PiU) →
        (∀ t ≤ T, stabPath Φ PiU μ Pi0 t = Φ^[t] Pi0) ∧
          ∀ t, T < t → stabPath Φ PiU μ Pi0 t = μ := by
  refine ⟨⟨_, _, stab_exists hr hΦ hμ hPi0⟩, fun a ia b ib ha hb h0 h0' =>
    (stab_unique hr ha hb (h0.trans h0'.symm)).1, fun T hT hbefore => ⟨fun t ht => ?_,
      fun t ht => ?_⟩⟩
  · unfold stabPath
    rw [ite_eq_right_iff]
    rintro ⟨s, hs, hlt⟩
    exact absurd (hbefore s (by omega)) (not_le.mpr hlt)
  · unfold stabPath
    rw [ite_eq_left_iff]
    intro hc
    exact absurd ⟨T, ht, hT⟩ hc

/-! ## §16.10.3 Fiscal equilibrium trimming -/

/-- Cochrane (2023), §16.10.3, p. 390, Benhabib, Schmitt-Grohé and Uribe (2002): with surpluses
`s_t = θ(Π_t) B_{t−1}/P_t`, (16.30) becomes `b_{t+1} = (1 + r)(1 − θ(Π_t)) b_t` for real debt
`b_t = B_{t−1}/P_t`. -/
theorem bsgu_real_debt {r θ bt st bt1 : ℝ} (hflow : bt1 = (1 + r) * (bt - st))
    (hs : st = θ * bt) : bt1 = (1 + r) * (1 - θ) * bt := by
  rw [hflow, hs]; ring

/-- Cochrane (2023), §16.10.3, p. 390, "the government lowers taxes, real debt grows explosively,
the consumer's transversality condition is violated": if `b₀ > 0`,
`b_{t+1} = (1 + r)(1 − θ_t)b_t` with `θ_t < 1`, and eventually `θ_t ≤ θ̄ < 0`, then the discounted
real debt `βᵗb_t` diverges to `+∞`. -/
theorem bsgu_tvc_violated {r : ℝ} {b θ : ℕ → ℝ} (hr : 0 < 1 + r) (hb0 : 0 < b 0)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (1 - θ t) * b t) (hθ1 : ∀ t, θ t < 1) {T0 : ℕ}
    {θbar : ℝ} (hθbar : θbar < 0) (hev : ∀ t, T0 ≤ t → θ t ≤ θbar) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop atTop := by
  set x : ℕ → ℝ := fun T => (1 + r)⁻¹ ^ T * b T with hx
  have hstep : ∀ T, x (T + 1) = (1 - θ T) * x T := fun T => by
    simp only [hx, hflow, pow_succ]
    field_simp
  have hpos : ∀ T, 0 < x T := by
    intro T
    induction T with
    | zero => simpa [hx] using hb0
    | succ n ih => rw [hstep]; exact mul_pos (by linarith [hθ1 n]) ih
  have hgrow : ∀ n, (1 - θbar) ^ n * x T0 ≤ x (T0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, hstep, pow_succ]
      have h1 : 1 - θbar ≤ 1 - θ (T0 + n) := by linarith [hev (T0 + n) (by omega)]
      calc (1 - θbar) ^ n * (1 - θbar) * x T0 = (1 - θbar) * ((1 - θbar) ^ n * x T0) := by ring
        _ ≤ (1 - θ (T0 + n)) * x (T0 + n) := by
          have := pow_pos (by linarith : (0 : ℝ) < 1 - θbar) n
          have := hpos T0
          exact mul_le_mul h1 ih (by positivity) (by linarith)
  have hlim : Tendsto (fun T => (1 - θbar) ^ (T - T0) * x T0) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp
      (tendsto_sub_atTop_nat T0)).atTop_mul_const (hpos T0)
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop T0] with T hT
  have := hgrow (T - T0)
  rwa [Nat.add_sub_cancel' hT] at this

/-- Cochrane (2023), §16.10.3, pp. 390–391, "a deflationary trap is not a possible rational
expectations equilibrium": with the BSGU surplus rule `s_t = θ(Π_t)B_{t−1}/P_t`, `θ < 1`,
`θ` continuous at `Π_L` with `θ(Π_L) < 0`, and positive initial debt, no equilibrium (in the sense
of `LowerBound.IsEquilibrium`) has inflation converging to `Π_L`. -/
theorem bsgu_no_equilibrium_to_lower {r : ℝ} {Φ θ : ℝ → ℝ} {Pm1 PL : ℝ} {P i s D : ℕ → ℝ}
    (hr : 0 < 1 + r) (h : IsEquilibrium r Φ Pm1 P i s D)
    (hrule : ∀ t, s t = θ (infl Pm1 P t) * (D t / P t)) (hD0 : 0 < D 0)
    (hθ1 : ∀ x, θ x < 1) (hθc : ContinuousAt θ PL) (hθL : θ PL < 0) :
    ¬ Tendsto (infl Pm1 P) atTop (𝓝 PL) := by
  intro hlim
  obtain ⟨-, -, hreal, htvc⟩ := equilibrium_dynamics hr h
  have hP := h.2.1
  have hflow : ∀ t, D (t + 1) / P (t + 1) = (1 + r) * (1 - θ (infl Pm1 P t)) * (D t / P t) :=
    fun t => bsgu_real_debt (hreal t) (hrule t)
  have hev : ∀ᶠ t in atTop, θ (infl Pm1 P t) < θ PL / 2 :=
    (hθc.tendsto.comp hlim).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hev
  have hdiv := bsgu_tvc_violated (b := fun t => D t / P t) hr (div_pos hD0 (hP 0)) hflow
    (fun t => hθ1 _) (θbar := θ PL / 2) (by linarith) (fun t ht => (hT0 t ht).le)
  have h0 := htvc 0
  simp only [zero_add] at h0
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 h0

/-- Cochrane (2023), §16.10.3, p. 390: with `θ(Π*) = r/(1+r)` (passive at the target) the target
`Π_t ≡ Π*` remains an equilibrium under the BSGU surplus rule. -/
theorem bsgu_target_survives {r : ℝ} {Φ θ : ℝ → ℝ} {Pm1 Pis : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hfix : Φ Pis = Pis) (hβ : (1 + r)⁻¹ ≤ Pis) (hθ : θ Pis = r / (1 + r)) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ (∀ t, infl Pm1 P t = Pis) ∧
      ∀ t, s t = θ (infl Pm1 P t) * (D t / P t) := by
  have hc : ∀ t, Φ^[t] Pis = Pis := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [orbit_succ, ih, hfix]
  have hPis : 0 < Pis := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hβ
  obtain ⟨P, i, s, D, h, -, hinfl, hs, -⟩ := equilibrium_exists (Φ := Φ) (Pi0 := Pis) D0 hr
    hPm1 hPis fun t => by rw [hc, hfix]; exact hβ
  refine ⟨P, i, s, D, h, fun t => by rw [hinfl, hc], fun t => ?_⟩
  rw [hs, hinfl, hc, hθ]

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's rule "let total nominal government liabilities
`D_t` … grow at a constant rate `μ̄`", in Cochrane's notation: with `P_{T+1} = Π_{T+1}P_T` and
`D_{T+1} = μ̄D_T`, the transversality term `βᵀD_T/P_T` is multiplied each period by
`βμ̄/Π_{T+1}`. -/
theorem mubar_tvc_step {r μ : ℝ} {infl P D : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    (1 + r)⁻¹ ^ (T + 1) * (D (T + 1) / P (T + 1)) =
      (1 + r)⁻¹ ^ T * (D T / P T) * ((1 + r)⁻¹ * μ / infl (T + 1)) := by
  rw [hD, hPrec, pow_succ]
  have := hP T
  have := hinfl (T + 1)
  field_simp

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's `μ̄` rule: if eventually `Π_{T+1} ≤ βμ̄` and
nominal liabilities are positive, the transversality term is eventually nondecreasing and
positive, so the transversality condition fails. -/
theorem mubar_tvc_violated {r μ : ℝ} {infl P D : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ t, 0 < P t)
    (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) {T0 : ℕ}
    (hev : ∀ T, T0 ≤ T → infl (T + 1) ≤ (1 + r)⁻¹ * μ) :
    ¬ Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) := by
  set v : ℕ → ℝ := fun T => (1 + r)⁻¹ ^ T * (D T / P T) with hv
  have hpos : ∀ T, 0 < v T := fun T => by
    have := hDpos T; have := hP T; have := inv_pos.mpr hr; positivity
  have hmono : ∀ n, v T0 ≤ v (T0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc]
      simp only [hv] at ih ⊢
      rw [mubar_tvc_step hP hinfl hPrec hD]
      have h1 : 1 ≤ (1 + r)⁻¹ * μ / infl (T0 + n + 1) :=
        (one_le_div (hinfl _)).mpr (hev _ (by omega))
      have := hpos (T0 + n)
      simp only [hv] at this
      nlinarith
  intro h
  have hev' : ∀ᶠ T in atTop, v T0 ≤ v T := by
    filter_upwards [eventually_ge_atTop T0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev'
  linarith [hpos T0]

/-- Cochrane (2023), §16.10.3, p. 390, "thus, in the case of an appropriate fiscal policy rule, a
deflationary trap is not a possible rational expectations equilibrium": with liabilities growing
at `μ̄`, every path converging to a point `Π_L < βμ̄` violates the transversality condition (for
`Π_L = β`, at the zero bound, this needs only `μ̄ > 1`). -/
theorem mubar_deflation_violates {r μ PL : ℝ} {infl P D : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ t, 0 < P t) (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) (hlim : Tendsto infl atTop (𝓝 PL))
    (hPL : PL < (1 + r)⁻¹ * μ) :
    ¬ Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPL))
  exact mubar_tvc_violated hr hP hinfl hPrec hD hDpos (T0 := T0) fun T hT =>
    (hT0 (T + 1) (by omega)).le

/-- Cochrane (2023), §16.10.3, p. 390: along the target path `Π_t ≡ Π*` the transversality term
is `(βμ̄/Π*)ᵀ` times its initial value, so the target satisfies the transversality condition iff
`βμ̄ < Π*`. With `Π_L < βμ̄ < Π*` the `μ̄` rule removes the deflations and keeps the target. -/
theorem mubar_target_tvc_iff {r μ Pis : ℝ} {P D : ℕ → ℝ} (hr : 0 < 1 + r) (hμ : 0 < μ)
    (hPis : 0 < Pis) (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) ↔ (1 + r)⁻¹ * μ < Pis := by
  have hval : ∀ T, (1 + r)⁻¹ ^ T * (D T / P T) = D 0 / P 0 * ((1 + r)⁻¹ * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [mubar_tvc_step (infl := fun _ => Pis) hP (fun _ => hPis) hPrec hD, ih, pow_succ]
      ring
  have h0 : 0 < D 0 / P 0 := div_pos (hDpos 0) (hP 0)
  have hr0 : 0 ≤ (1 + r)⁻¹ * μ / Pis := by have := inv_pos.mpr hr; positivity
  simp only [hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ (1 + r)⁻¹ * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, D 0 / P 0 ≤ D 0 / P 0 * ((1 + r)⁻¹ * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : (1 + r)⁻¹ * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (D 0 / P 0)

/-! ## Woodford's `μ̄` rule, restated from the Woodford Chapter 2 project -/

namespace WoodfordMuBar

/-! ## The Taylor-rule version: nominal liabilities growing at `μ̄` (pp. 132–133) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), (1.24), p. 72, along a perfect-foresight path: the transversality term
`β^T λ(i_T) D_T/P_T` with `i_T = φ(Π_T)`. -/
noncomputable def tvcValue (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ P D : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * lam (φ (Pi_ T)) * D T / P T

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, displayed identity: when `P_{t+1} = Π_{t+1}P_t`,
`D_{t+1} = μ̄D_t` and (4.5) holds,
`β^{T+1}λ_{T+1}D_{T+1}/P_{T+1} = β^Tλ_TD_T/P_T · μ̄/(1 + i_T)`. -/
theorem tvcValue_succ {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    tvcValue β lam φ Pi_ P D (T + 1) = tvcValue β lam φ Pi_ P D T * (μ / (1 + φ (Pi_ T))) := by
  have h45 := hpath.2 T
  have hl1 := hlam (T + 1)
  have hl := hlam T
  have hPi := hpath.1 (T + 1)
  have hφT := hφ T
  have hPT := hP T
  have hlam1 : lam (φ (Pi_ (T + 1))) = Pi_ (T + 1) * lam (φ (Pi_ T)) / (β * (1 + φ (Pi_ T))) := by
    rw [div_eq_div_iff hl1.ne' hl.ne'] at h45
    rw [eq_div_iff (by positivity)]
    linarith
  unfold tvcValue
  rw [hlam1, hPrec, hD, pow_succ]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), pp. 132–133 (error E4 corrected): if from some date on `1 + i_T ≤ μ̄`, the
transversality term is nondecreasing and positive from that date, so the transversality
condition (1.24) is violated. -/
theorem taylor_tvc_violated_of_eventually_le {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hev : ∃ t0, ∀ T, t0 ≤ T → 1 + φ (Pi_ T) ≤ μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t0, ht0⟩ := hev
  have hpos : ∀ T, 0 < tvcValue β lam φ Pi_ P D T := fun T => by
    unfold tvcValue; have := hlam T; have := hDpos T; have := hP T; positivity
  have hmono : ∀ n, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D (t0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, tvcValue_succ hβ hpath hlam hφ hP hPrec hD]
      have h1 : 1 ≤ μ / (1 + φ (Pi_ (t0 + n))) :=
        (one_le_div (hφ _)).mpr (ht0 _ (Nat.le_add_right _ _))
      nlinarith [hpos (t0 + n)]
  intro h
  have hev : ∀ᶠ T in atTop, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev
  linarith [hpos t0]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, error E4: the printed claim "there must exist a date `t` such that
`1 + φ(Π_T) ≥ μ̄` for all `T ≥ t`" is false along any deflationary path converging to a point
`Π**` where `φ` is continuous with `1 + φ(Π**) < μ̄` (in Figure 2.4, `Π** = β`, `φ(β) = 0`,
`μ̄ > 1`). -/
theorem e4_printed_inequality_false {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ¬ ∃ t, ∀ T, t ≤ T → μ ≤ 1 + φ (Pi_ T) := by
  rintro ⟨t, ht⟩
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  have h2 : ∀ᶠ T in atTop, μ ≤ 1 + φ (Pi_ T) := by
    filter_upwards [eventually_ge_atTop t] with T hT using ht T hT
  have := ge_of_tendsto h1 h2
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, error E4 corrected: under the same hypotheses there is a date after
which `1 + φ(Π_T) ≤ μ̄` (indeed `<`). -/
theorem e4_corrected_inequality {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ∃ t, ∀ T, t ≤ T → 1 + φ (Pi_ T) ≤ μ := by
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  obtain ⟨t, ht⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds hμ))
  exact ⟨t, fun T hT => (ht T hT).le⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, "even if interest rates level off sooner, so that there exists a
lower steady-state inflation rate `Π** > β`, the same argument works as long as `μ̄ > β⁻¹Π**`":
a path of (4.5) converging to a steady state `Π**` (so `1 + φ(Π**) = β⁻¹Π**`) with `φ` continuous
there and `μ̄ > β⁻¹Π**` violates the transversality condition. -/
theorem deflation_tvc_violated {β μ Pss : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ0 : ∀ t, 0 ≤ φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss)
    (hss : 1 + φ Pss = Pss / β) (hμ : Pss / β < μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) :=
  taylor_tvc_violated_of_eventually_le hβ hpath hlam (fun t => by linarith [hφ0 t]) hP hPrec hD
    hDpos (e4_corrected_inequality hlim hcont (by rw [hss]; exact hμ))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 132: if `φ(Π) = 0` for all `Π ≤ Π̲` with `Π̲ > β`, a path of (4.5) that is
eventually below `Π̲` has `i_T = 0` and then `Π_{T+1} = β` from that date on. -/
theorem zero_bound_inflation_eq_beta {β Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hpath : IsPath45 β lam φ Pi_) (hlam0 : 0 < lam 0) (hzero : ∀ x, x ≤ Plow → φ x = 0)
    {t : ℕ} (ht : ∀ T, t ≤ T → Pi_ T ≤ Plow) : ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β := by
  intro T hT
  have h1 := hzero _ (ht T hT)
  have h2 := hzero _ (ht (T + 1) (by omega))
  have h45 := hpath.2 T
  rw [h1, h2, add_zero, mul_one] at h45
  exact ⟨h1, by rwa [div_left_inj' hlam0.ne'] at h45⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 132, "then any deflationary solution to (4.5) involves a zero nominal
interest rate in each period after some finite date `t`, which in turn implies that `Π_T = β`
for all `T ≥ t + 1`. It follows that … the transversality condition (1.24) is violated": with
`φ = 0` on `(−∞, Π̲]`, `Π̲ > β`, `D` growing at `μ̄ ≥ 1`, a path of (4.5) converging to `β`
eventually has `i = 0` and `Π = β`, and violates (1.24). -/
theorem zero_bound_tvc_violated {β μ Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hPlow : β < Plow) (hμ : 1 ≤ μ) (hpath : IsPath45 β lam φ Pi_)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) (hlam0 : 0 < lam 0) (hφ0 : ∀ t, 0 ≤ φ (Pi_ t))
    (hzero : ∀ x, x ≤ Plow → φ x = 0) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 β)) :
    (∃ t, ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β) ∧
      ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPlow))
  have hz := zero_bound_inflation_eq_beta hpath hlam0 hzero (fun T hT => (ht T hT).le)
  refine ⟨⟨t, hz⟩, taylor_tvc_violated_of_eventually_le hβ hpath hlam
    (fun s => by linarith [hφ0 s]) hP hPrec hD hDpos ⟨t, fun T hT => ?_⟩⟩
  rw [(hz T hT).1]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, "even if `φ(Π) > 0` for all `Π > β`, as long as
`φ(Π) < (Π − β)/β` for all `β < Π < Π*`, one can still exclude self-fulfilling deflations in the
case of any fiscal policy that ensures a growth rate `μ̄ > 1` for government liabilities": under
the hypotheses of Figure 2.4 (`GlobalDynamics.self_fulfilling_deflation45`), every solution of
(4.5) starting in `(β, Π*)` violates the transversality condition (1.24). -/
theorem fig24_deflations_violate_tvc {β Pis μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hμ : 1 < μ) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) : ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  have hlim := (self_fulfilling_deflation45 hβ hlam hanti hlamc hmono hφ0 hcont hφβ hbelow
    hpath h0).2.2
  exact deflation_tvc_violated hβ hpath (fun t => hlam _ (hφ0 _ (hpath.1 t)))
    (fun t => hφ0 _ (hpath.1 t)) hP hPrec hD hDpos hlim
    (hcont.continuousAt (Ioi_mem_nhds hβ)) (by rw [hφβ, div_self hβ.ne']; ring)
    (by rw [div_self hβ.ne']; exact hμ)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), pp. 132–133 (implicit): along the target path `Π_t ≡ Π*` (with
`1 + φ(Π*) = Π*/β`) the transversality term is `(βμ̄/Π*)^T` times its initial value, so the target
equilibrium satisfies (1.24) iff `βμ̄ < Π*` (given `μ̄ > 0`). -/
theorem target_tvc_iff {β μ Pis : ℝ} {lam φ : ℝ → ℝ} {P D : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hPis : 0 < Pis) (htarget : 1 + φ Pis = Pis / β) (hlam : 0 < lam (φ Pis))
    (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    Tendsto (tvcValue β lam φ (fun _ => Pis) P D) atTop (𝓝 0) ↔ β * μ < Pis := by
  have hpath : IsPath45 β lam φ (fun _ => Pis) := ⟨fun _ => hPis, fun _ => by
    simp only [htarget]; field_simp⟩
  have hval : ∀ T, tvcValue β lam φ (fun _ => Pis) P D T =
      tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [tvcValue_succ hβ hpath (fun _ => hlam) (fun _ => by rw [htarget]; positivity) hP hPrec
        hD, ih, htarget, pow_succ]
      field_simp
  have h0 : 0 < tvcValue β lam φ (fun _ => Pis) P D 0 := by
    unfold tvcValue; have := hDpos 0; have := hP 0; positivity
  have hr0 : 0 ≤ β * μ / Pis := by positivity
  rw [show tvcValue β lam φ (fun _ => Pis) P D =
    fun T => tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T from funext hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ β * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, tvcValue β lam φ (fun _ => Pis) P D 0 ≤
        tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : β * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (tvcValue β lam φ (fun _ => Pis) P D 0)

end WoodfordMuBar

/-! ## The Schmitt-Grohé–Uribe example, restated from the Woodford Chapter 2 project -/

namespace SGU

open Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar

/-! ## Preferences, (A.54) and (A.55) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the optimal cash-goods purchases `c₁ = min(m, C/(1 + θ))`. -/
noncomputable def c1opt (θ C m : ℝ) : ℝ := min m (C / (1 + θ))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.53), p. 654: the indirect utility
`u(C, m) = log c₁ + θ log(C − c₁)` at the optimal `c₁`. -/
noncomputable def uSGU (θ C m : ℝ) : ℝ :=
  Real.log (c1opt θ C m) + θ * Real.log (C - c1opt θ C m)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.53), p. 654, "the optimal level of cash goods purchases is equal to
`c₁ = min(m, C/(1 + θ))`": for `θ, C, m > 0`, every feasible `c₁ ∈ (0, m]` with `c₁ < C` gives
`log c₁ + θ log(C − c₁) ≤ u(C, m)`. -/
theorem c1opt_optimal {θ C m c1 : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hm : 0 < m) (h0 : 0 < c1)
    (hc1m : c1 ≤ m) (hc1C : c1 < C) :
    Real.log c1 + θ * Real.log (C - c1) ≤ uSGU θ C m := by
  unfold uSGU
  set cs := c1opt θ C m with hcs
  have hθ1 : 0 < 1 + θ := by linarith
  have hcsle : cs ≤ C / (1 + θ) := min_le_right _ _
  have hcspos : 0 < cs := lt_min hm (div_pos hC hθ1)
  have hCcs : 0 < C - cs := by
    have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
    linarith
  have h1 : Real.log c1 - Real.log cs ≤ c1 / cs - 1 := by
    rw [← Real.log_div h0.ne' hcspos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos h0 hcspos)
  have h2 : Real.log (C - c1) - Real.log (C - cs) ≤ (C - c1) / (C - cs) - 1 := by
    rw [← Real.log_div (by linarith) hCcs.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hCcs)
  have hkey : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) ≤ 0 := by
    have e : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) =
        (c1 - cs) * ((C - cs) - θ * cs) / (cs * (C - cs)) := by
      field_simp
      ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rcases le_total m (C / (1 + θ)) with hle | hle
    · have hcsm : cs = m := min_eq_left hle
      have hA : c1 - cs ≤ 0 := by rw [hcsm]; linarith
      have hB : 0 ≤ (C - cs) - θ * cs := by
        rw [hcsm]
        rw [le_div_iff₀ hθ1] at hle
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg hA hB
    · have hcsC : cs = C / (1 + θ) := min_eq_right hle
      have hB : (C - cs) - θ * cs = 0 := by rw [hcsC]; field_simp; ring
      rw [hB, mul_zero]
  nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.54), p. 654, region where the cash constraint binds
(`m < C/(1 + θ)`): `u_C = θ/(C − m)`, `u_m = 1/m − θ/(C − m)`, so
`λ = u_C + u_m = 1/m = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_binding {θ C m : ℝ} (hθ : 0 < θ) (hm : 0 < m) (hmC : m < C / (1 + θ)) :
    HasDerivAt (fun C' => uSGU θ C' m) (θ / (C - m)) C ∧
      HasDerivAt (fun m' => uSGU θ C m') (1 / m - θ / (C - m)) m ∧
      θ / (C - m) + (1 / m - θ / (C - m)) = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : m * (1 + θ) < C := by rwa [lt_div_iff₀ hθ1] at hmC
  have hCm : 0 < C - m := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id C).sub_const m).log hCm.ne'
    have h2 := (h.const_mul θ).const_add (Real.log m)
    simp only [id, one_div] at h2
    refine (h2.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC'] with C' hC'
    have : m ≤ C' / (1 + θ) := by rw [le_div_iff₀ hθ1]; exact (Set.mem_Ioi.mp hC').le
    simp only [uSGU, c1opt, min_eq_left this]
  · have h1 := (hasDerivAt_id m).log hm.ne'
    have h2 := (((hasDerivAt_id m).const_sub C).log hCm.ne').const_mul θ
    have h3 := h1.add h2
    simp only [id] at h3
    refine (h3.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_left (Set.mem_Iio.mp hm').le]
    rfl
  · simp only [c1opt, min_eq_left hmC.le]
    field_simp
    ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.54), p. 654, region beyond satiation (`m > C/(1 + θ)`):
`u_C = (1 + θ)/C`, `u_m = 0`, so `λ = (1 + θ)/C = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_satiated {θ C m : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hmC : C / (1 + θ) < m) :
    HasDerivAt (fun C' => uSGU θ C' m) ((1 + θ) / C) C ∧
      HasDerivAt (fun m' => uSGU θ C m') 0 m ∧ (1 + θ) / C + 0 = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : C < m * (1 + θ) := by rwa [div_lt_iff₀ hθ1] at hmC
  refine ⟨?_, ?_, ?_⟩
  · have ha : HasDerivAt (fun C' : ℝ => C' / (1 + θ)) (1 / (1 + θ)) C := by
      simpa using (hasDerivAt_id C).div_const (1 + θ)
    have hb : HasDerivAt (fun C' : ℝ => C' - C' / (1 + θ)) (1 - 1 / (1 + θ)) C :=
      (hasDerivAt_id C).sub ha
    have hpos1 : C / (1 + θ) ≠ 0 := (div_pos hC hθ1).ne'
    have hpos2 : C - C / (1 + θ) ≠ 0 := by
      have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
      linarith
    have h := (ha.log hpos1).add ((hb.log hpos2).const_mul θ)
    have hθ0 : θ ≠ 0 := hθ.ne'
    have hC0 : C ≠ 0 := hC.ne'
    have e1 : (1 : ℝ) - 1 / (1 + θ) = θ / (1 + θ) := by field_simp; ring
    have e2 : C - C / (1 + θ) = C * θ / (1 + θ) := by field_simp; ring
    refine (h.congr_deriv (by rw [e1, e2]; field_simp)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC'] with C' hC'
    have : C' / (1 + θ) ≤ m := by rw [div_le_iff₀ hθ1]; exact (Set.mem_Iio.mp hC').le
    simp only [uSGU, c1opt, min_eq_right this]
    rfl
  · refine (hasDerivAt_const m (uSGU θ C m)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_right (Set.mem_Ioi.mp hm').le, min_eq_right hmC.le]
  · simp only [c1opt, min_eq_right hmC.le]
    field_simp
    ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.55), p. 654: the liquidity-preference function
`L(Y, i) = Y/(1 + θ(1 + i))`. -/
noncomputable def LSGU (θ Y i : ℝ) : ℝ := Y / (1 + θ * (1 + i))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.41) ⇒ (A.55), p. 654: with `i^m = 0`, (A.41) reads `u_m/u_C = i`
(`Timing.oddsRatio_oppCost_zero`). For `i > 0` the real balances `m = L(Y, i)` lie in the region
where the cash constraint binds, and there `u_m/u_C = i` holds iff `m = Y/(1 + θ(1 + i))`. -/
theorem money_demand_A55 {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 < i) :
    0 < LSGU θ Y i ∧ LSGU θ Y i < Y / (1 + θ) ∧
      ∀ m, 0 < m → m < Y / (1 + θ) →
        ((1 / m - θ / (Y - m)) / (θ / (Y - m)) = i ↔ m = LSGU θ Y i) := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  refine ⟨div_pos hY hd, ?_, fun m hm hmY => ?_⟩
  · unfold LSGU
    exact div_lt_div_of_pos_left hY hθ1 (by nlinarith)
  · have hmY' : m * (1 + θ) < Y := by rwa [lt_div_iff₀ hθ1] at hmY
    have hYm : 0 < Y - m := by nlinarith
    have e : (1 / m - θ / (Y - m)) / (θ / (Y - m)) = (Y - m) / (θ * m) - 1 := by
      field_simp
    rw [e, LSGU, eq_div_iff hd.ne', sub_eq_iff_eq_add, div_eq_iff (by positivity)]
    constructor <;> intro h <;> linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ(i) = (1 + θ(1 + i))/Ȳ`. -/
noncomputable def lamSGU (θ Y i : ℝ) : ℝ := (1 + θ * (1 + i)) / Y

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, "substituting (A.55) into (A.54) … `λ(i) = (1 + θ(1 + i))/Ȳ` for all
`i ≥ 0`". -/
theorem lambda_of_i {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    1 / c1opt θ Y (LSGU θ Y i) = lamSGU θ Y i := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have hle : LSGU θ Y i ≤ Y / (1 + θ) := by
    unfold LSGU
    exact div_le_div_of_nonneg_left hY.le hθ1 (by nlinarith)
  rw [c1opt, min_eq_left hle, LSGU, lamSGU]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, "it can be made unboundedly large in the case of a high enough
interest rate". -/
theorem lamSGU_tendsto_atTop {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (lamSGU θ Y) atTop atTop := by
  unfold lamSGU
  refine Tendsto.atTop_div_const hY ?_
  exact tendsto_atTop_add_const_left _ 1
    (Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the elasticity of `λ(i)` with respect to `1 + i`,
`(1 + i)λ'(i)/λ(i)` with `λ' = θ/Ȳ`. -/
noncomputable def elasticity (θ Y i : ℝ) : ℝ := (1 + i) * (θ / Y) / lamSGU θ Y i

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ'(i) = θ/Ȳ`. -/
theorem hasDerivAt_lamSGU (θ Y i : ℝ) : HasDerivAt (lamSGU θ Y) (θ / Y) i := by
  have h := (((hasDerivAt_id i).const_add 1).const_mul θ).const_add 1
  exact (h.div_const Y).congr_deriv (by ring)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654 ("the elasticity of `λ(i)` with respect to `i` remains bounded below
1") and p. 137 (elasticity with respect to `1 + i` "positive, but bounded below one"): for
`i ≥ 0` the elasticity equals `θ(1 + i)/(1 + θ(1 + i)) ∈ (0, 1)`. -/
theorem elasticity_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) ∧ 0 < elasticity θ Y i ∧
      elasticity θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have e : elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) := by
    unfold elasticity lamSGU
    field_simp
  refine ⟨e, ?_, ?_⟩
  · rw [e]; have : 0 < 1 + i := by linarith
    positivity
  · rw [e, div_lt_one hd]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, precision: the elasticity tends to `1` as `i → ∞`, so it is below one
at every `i` but admits no uniform bound `k < 1`. -/
theorem elasticity_tendsto_one {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (elasticity θ Y) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℝ => θ * (1 + i)) atTop atTop :=
    Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun i : ℝ => 1 - 1 / (1 + θ * (1 + i))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 h1))
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
  rw [(elasticity_lt_one hθ hY hi).1]
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the elasticity with respect to `i`, `iλ'(i)/λ(i) = θi/(1 + θ(1 + i))`,
is also below one for `i ≥ 0`. -/
theorem elasticity_i_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    i * (θ / Y) / lamSGU θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  unfold lamSGU
  rw [div_lt_one (by positivity)]
  rw [mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  nlinarith

/-! ## The Taylor rule (A.56) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56), p. 654: `1 + φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)]` on its linear range. -/
noncomputable def ellSGU (β Pis φπ x : ℝ) : ℝ := (Pis + φπ * (x - Pis)) / β

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56) and fn. 8, p. 655: the rule
`φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)] − 1`, truncated at zero ("this form holds … only for inflation
rates for which it implies a nonnegative interest rate"). -/
noncomputable def phiSGU (β Pis φπ x : ℝ) : ℝ := max 0 (ellSGU β Pis φπ x - 1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): `1 + φ(Π) = max(1, ℓ(Π))`. -/
theorem one_add_phiSGU (β Pis φπ x : ℝ) :
    1 + phiSGU β Pis φπ x = max 1 (ellSGU β Pis φπ x) := by
  unfold phiSGU
  rw [← max_add_add_left]
  simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): `φ ≥ 0`. -/
theorem phiSGU_nonneg (β Pis φπ x : ℝ) : 0 ≤ phiSGU β Pis φπ x := le_max_left _ _

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): the rule is continuous. -/
theorem phiSGU_continuous (β Pis φπ : ℝ) : Continuous (phiSGU β Pis φπ) := by
  unfold phiSGU ellSGU
  fun_prop

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56), p. 655: the rule is "consistent with a steady-state inflation rate
`Π*`": `φ(Π*) = β⁻¹Π* − 1` when `Π* ≥ β`. -/
theorem phiSGU_target {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β ≤ Pis) :
    phiSGU β Pis φπ Pis = Pis / β - 1 := by
  unfold phiSGU ellSGU
  rw [sub_self, mul_zero, add_zero, max_eq_right]
  rw [sub_nonneg, le_div_iff₀ hβ]
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "such a rule satisfies the Taylor principle if and only if
`φ_π > 1`": for `Π* > β`, `φ'(Π*) = φ_π/β`, and the Taylor coefficient `Π*φ'(Π*)/(1 + φ(Π*))`
(= the slope `βφ'(Π*)` of the map (4.6), `GlobalDynamics.taylorCoeff_eq_slope`) equals `φ_π`. -/
theorem taylorCoeff_phiSGU {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β < Pis) :
    HasDerivAt (phiSGU β Pis φπ) (φπ / β) Pis ∧
      Pis * (φπ / β) / (1 + phiSGU β Pis φπ Pis) = φπ := by
  have hlin : HasDerivAt (fun x => ellSGU β Pis φπ x - 1) (φπ / β) Pis := by
    have h := ((((hasDerivAt_id Pis).sub_const Pis).const_mul φπ).const_add Pis).div_const β
    simpa [ellSGU] using h.sub_const 1
  have hval : 0 < ellSGU β Pis φπ Pis - 1 := by
    unfold ellSGU
    rw [sub_self, mul_zero, add_zero, sub_pos, one_lt_div hβ]
    exact hPis
  have hev : (phiSGU β Pis φπ) =ᶠ[𝓝 Pis] fun x => ellSGU β Pis φπ x - 1 := by
    have hc : ContinuousAt (fun x => ellSGU β Pis φπ x - 1) Pis := hlin.continuousAt
    filter_upwards [hc.eventually (lt_mem_nhds hval)] with x hx
    unfold phiSGU
    rw [max_eq_right hx.le]
  refine ⟨hlin.congr_of_eventuallyEq hev, ?_⟩
  rw [taylorCoeff_eq_slope hβ (by linarith) (phiSGU_target hβ hPis.le)]
  field_simp

/-! ## The functions `A` and `B` -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `A(Π) ≡ λ(φ(Π))/(1 + φ(Π))`. -/
noncomputable def sguA (θ Y β Pis φπ x : ℝ) : ℝ :=
  lamSGU θ Y (phiSGU β Pis φπ x) / (1 + phiSGU β Pis φπ x)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `B(Π) ≡ βλ(φ(Π))/Π`. -/
noncomputable def sguB (θ Y β Pis φπ x : ℝ) : ℝ := β * lamSGU θ Y (phiSGU β Pis φπ x) / x

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (error E5): the constant `β + θΠ*(1 − φ_π)`, whose sign decides the
direction of monotonicity of `B`. -/
def sguC (θ β Pis φπ : ℝ) : ℝ := β + θ * Pis * (1 - φπ)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ(φ(Π)) > 0`. -/
theorem lamSGU_phi_pos {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    0 < lamSGU θ Y (phiSGU β Pis φπ x) := by
  unfold lamSGU
  have := phiSGU_nonneg β Pis φπ x
  have : 0 < 1 + θ * (1 + phiSGU β Pis φπ x) := by nlinarith
  positivity

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (4.5) ⇔ p. 655: for positive inflation rates, (4.5) is
`B(Π_{t+1}) = A(Π_t)`. -/
theorem eq45_iff_AB {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hx' : 0 < x') :
    x' / lamSGU θ Y (phiSGU β Pis φπ x') =
        β * (1 + phiSGU β Pis φπ x) / lamSGU θ Y (phiSGU β Pis φπ x) ↔
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x := by
  have h1 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x) hθ hY
  have h2 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x') hθ hY
  have h3 : 0 < 1 + phiSGU β Pis φπ x := by linarith [phiSGU_nonneg β Pis φπ x]
  unfold sguA sguB
  rw [div_eq_div_iff h2.ne' h1.ne', div_eq_div_iff hx'.ne' h3.ne']
  constructor <;> intro h <;> nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: in terms of `M = 1 + φ(Π) = max(1, ℓ(Π))`,
`A = (1 + θM)/(ȲM)` and `B = β(1 + θM)/(ȲΠ)`. -/
theorem sguAB_formula (θ Y β Pis φπ x : ℝ) :
    sguA θ Y β Pis φπ x = (1 + θ * max 1 (ellSGU β Pis φπ x)) / Y / max 1 (ellSGU β Pis φπ x) ∧
      sguB θ Y β Pis φπ x = β * ((1 + θ * max 1 (ellSGU β Pis φπ x)) / Y) / x := by
  unfold sguA sguB lamSGU
  rw [one_add_phiSGU]
  exact ⟨rfl, rfl⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, with the factor `1/Ȳ` restored: on the linear range of the rule,
`B(Π) = [β + θΠ*(1 − φ_π)]/(ȲΠ) + θφ_π/Ȳ`. -/
theorem sguB_formula {θ Y β Pis φπ x : ℝ} (hβ : 0 < β) (hY : 0 < Y) (hx : 0 < x)
    (hl : 1 ≤ ellSGU β Pis φπ x) :
    sguB θ Y β Pis φπ x = sguC θ β Pis φπ / (Y * x) + θ * φπ / Y := by
  rw [(sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  unfold ellSGU sguC
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "`A(Π)` is a monotonically decreasing function of `Π`": for
`φ_π ≥ 0`. -/
theorem sguA_antitone {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 0 ≤ φπ) : Antitone (sguA θ Y β Pis φπ) := by
  intro a b hab
  have hM : max 1 (ellSGU β Pis φπ a) ≤ max 1 (ellSGU β Pis φπ b) := by
    refine max_le_max le_rfl ?_
    unfold ellSGU
    exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  have ha1 : 1 ≤ max 1 (ellSGU β Pis φπ a) := le_max_left _ _
  rw [(sguAB_formula θ Y β Pis φπ a).1, (sguAB_formula θ Y β Pis φπ b).1]
  set Ma := max 1 (ellSGU β Pis φπ a)
  set Mb := max 1 (ellSGU β Pis φπ b)
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hY (by linarith : (0 : ℝ) < Ma)]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "approaches the asymptotic value of `θ`" — with the factor `1/Ȳ`
the text omits: `A(Π) → θ/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguA_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguA θ Y β Pis φπ) atTop (𝓝 (θ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => 1 / (Y * ellSGU β Pis φπ x) + θ / Y) atTop (𝓝 (0 + θ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY hl)).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1)] with x hx
  rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_right hx]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, error E5: if `β + θΠ*(1 − φ_π) > 0`, `B` is strictly decreasing on
`(0, ∞)` (on both the linear and the truncated range of the rule). -/
theorem sguB_strictAntiOn {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hc : 0 < sguC θ β Pis φπ) : StrictAntiOn (sguB θ Y β Pis φπ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  rw [(sguAB_formula θ Y β Pis φπ a).2, (sguAB_formula θ Y β Pis φπ b).2]
  set Ma := max 1 (ellSGU β Pis φπ a) with hMa
  set Mb := max 1 (ellSGU β Pis φπ b) with hMb
  have hMa1 : 1 ≤ Ma := le_max_left _ _
  have hMal : ellSGU β Pis φπ a ≤ Ma := le_max_right _ _
  have hid : ∀ x, β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    intro x; unfold ellSGU sguC; field_simp; ring
  rw [div_lt_div_iff₀ hb' ha']
  suffices key : β * (1 + θ * Mb) * a < β * (1 + θ * Ma) * b by
    have e1 : β * ((1 + θ * Mb) / Y) * a = (1 / Y) * (β * (1 + θ * Mb) * a) := by ring
    have e2 : β * ((1 + θ * Ma) / Y) * b = (1 / Y) * (β * (1 + θ * Ma) * b) := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left key (by positivity)
  rcases le_total 1 (ellSGU β Pis φπ b) with hl | hl
  · have hMbe : Mb = ellSGU β Pis φπ b := max_eq_right hl
    rw [hMbe, hid b]
    have h1 : β * (1 + θ * ellSGU β Pis φπ a) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMal hθ.le; nlinarith
    rw [hid a] at h1
    nlinarith [mul_lt_mul_of_pos_left hab hc]
  · have hMbe : Mb = 1 := max_eq_left hl
    rw [hMbe]
    have h1 : β * (1 + θ * 1) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMa1 hθ.le; nlinarith
    have h2 : 0 < β * (1 + θ * 1) := by positivity
    nlinarith [mul_lt_mul_of_pos_left hab h2]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (error E5): if `β + θΠ*(1 − φ_π) > 0` then `B(Π) > θφ_π/Ȳ` for every
`Π > 0` ("approaches the asymptotic value `φ_πθ`" from above). -/
theorem sguB_gt {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hx : 0 < x)
    (hc : 0 < sguC θ β Pis φπ) : θ * φπ / Y < sguB θ Y β Pis φπ x := by
  rw [(sguAB_formula θ Y β Pis φπ x).2]
  have hle : ellSGU β Pis φπ x ≤ max 1 (ellSGU β Pis φπ x) := le_max_right _ _
  have hid : β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    unfold ellSGU sguC; field_simp; ring
  rw [lt_div_iff₀ hx, div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  have : β * (1 + θ * ellSGU β Pis φπ x) ≤ β * (1 + θ * max 1 (ellSGU β Pis φπ x)) := by
    have := mul_le_mul_of_nonneg_left hle hθ.le; nlinarith
  nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `B(Π) → θφ_π/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguB_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguB θ Y β Pis φπ) atTop (𝓝 (θ * φπ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => sguC θ β Pis φπ / (Y * x) + θ * φπ / Y) atTop
      (𝓝 (0 + θ * φπ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY tendsto_id)).add
      tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1), eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  rw [sguB_formula hβ hY hx0 hx]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (and the E6 condition of §4.1): if `φ_π > 1` and `Π* > β`, then
`A(Π) < B(Π)` for every `Π > Π*` — the curve (4.5) lies above the diagonal above the target. -/
theorem sguA_lt_B_above {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hx : Pis < x) :
    sguA θ Y β Pis φπ x < sguB θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ ellSGU β Pis φπ x := by
    unfold ellSGU; rw [le_div_iff₀ hβ]; nlinarith
  have hl0 : 0 < ellSGU β Pis φπ x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  have hkey : x < β * ellSGU β Pis φπ x := by
    unfold ellSGU; field_simp; nlinarith
  have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
  rw [div_lt_div_iff₀ hl0 hx0]
  nlinarith [mul_lt_mul_of_pos_left hkey hp]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: if `φ_π > 1` and `Π* > β`, then `B(Π) < A(Π)` for `β < Π < Π*`. -/
theorem sguB_lt_A_below {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hx1 : β < x) (hx2 : x < Pis) :
    sguB θ Y β Pis φπ x < sguA θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2]
  rcases le_total 1 (ellSGU β Pis φπ x) with hl | hl
  · rw [max_eq_right hl]
    have hl0 : 0 < ellSGU β Pis φπ x := by linarith
    have hkey : β * ellSGU β Pis φπ x < x := by
      unfold ellSGU; field_simp; nlinarith
    have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
    rw [div_lt_div_iff₀ hx0 hl0]
    nlinarith [mul_lt_mul_of_pos_left hkey hp]
  · rw [max_eq_left hl, div_one, div_lt_iff₀ hx0]
    have hp : 0 < (1 + θ * 1) / Y := by positivity
    nlinarith [mul_lt_mul_of_pos_left hx1 hp]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `ℓ(β) < 1` (so `φ(β) = 0` and `Π** = β`) when `φ_π > 1`, `Π* > β`;
hence `A(Π) = (1 + θ)/Ȳ = B(β)` for all `Π ≤ β`, and `A ≤ (1 + θ)/Ȳ` everywhere. -/
theorem sgu_at_beta {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ)
    (hPis : β < Pis) :
    ellSGU β Pis φπ β < 1 ∧ phiSGU β Pis φπ β = 0 ∧ sguB θ Y β Pis φπ β = (1 + θ) / Y ∧
      (∀ x, x ≤ β → sguA θ Y β Pis φπ x = (1 + θ) / Y) ∧
      ∀ x, sguA θ Y β Pis φπ x ≤ (1 + θ) / Y := by
  have hlβ : ellSGU β Pis φπ β < 1 := by
    unfold ellSGU; rw [div_lt_one hβ]; nlinarith
  have hmono : ∀ x, x ≤ β → ellSGU β Pis φπ x ≤ ellSGU β Pis φπ β := fun x hx => by
    unfold ellSGU; exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  refine ⟨hlβ, ?_, ?_, fun x hx => ?_, fun x => ?_⟩
  · unfold phiSGU; exact max_eq_left (by linarith)
  · rw [(sguAB_formula θ Y β Pis φπ β).2, max_eq_left hlβ.le]
    field_simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_left (le_trans (hmono x hx) hlβ.le)]
    simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1]
    have hM : 1 ≤ max 1 (ellSGU β Pis φπ x) := le_max_left _ _
    rw [div_div, div_le_div_iff₀ (by positivity) hY]
    nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: the bound `Π̄`, defined by `1 + φ(Π̄) = 1/(θ(φ_π − 1))`. -/
noncomputable def sguPibar (θ β Pis φπ : ℝ) : ℝ := Pis + (β / (θ * (φπ - 1)) - Pis) / φπ

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "there exists a finite `Π̄` such that `A(Π̄) = φ_πθ`" (with `1/Ȳ`):
under `φ_π > 1`, `Π* > β` and the E5 hypothesis `β + θΠ*(1 − φ_π) > 0`, `Π̄ > Π*`, and
`A(Π̄) = θφ_π/Ȳ`. -/
theorem sguPibar_spec {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) :
    Pis < sguPibar θ β Pis φπ ∧ ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) ∧
      sguA θ Y β Pis φπ (sguPibar θ β Pis φπ) = θ * φπ / Y := by
  have hk : 0 < θ * (φπ - 1) := by nlinarith
  have hφ0 : 0 < φπ := by linarith
  have hk1 : φπ - 1 ≠ 0 := by linarith
  have hkP : θ * (φπ - 1) * Pis < β := by unfold sguC at hc; nlinarith
  have hgt : Pis < β / (θ * (φπ - 1)) := by rw [lt_div_iff₀ hk]; linarith
  have hell : ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) := by
    unfold ellSGU sguPibar
    field_simp
    ring
  have hPi : Pis < sguPibar θ β Pis φπ := by
    unfold sguPibar
    have : 0 < (β / (θ * (φπ - 1)) - Pis) / φπ := div_pos (by linarith) hφ0
    linarith
  refine ⟨hPi, hell, ?_⟩
  have h1 : 1 ≤ 1 / (θ * (φπ - 1)) := by
    rw [le_div_iff₀ hk, one_mul]
    have : Pis / β > 1 := (one_lt_div hβ).mpr hPis
    have h2 : θ * (φπ - 1) * Pis < β := hkP
    nlinarith
  rw [(sguAB_formula θ Y β Pis φπ _).1, hell, max_eq_right h1]
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "in the case of any `Π_t ≥ Π̄`, there is no value for `Π_{t+1}` that
would satisfy (4.5)" — true under the E5 hypothesis. -/
theorem sgu_no_successor {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hx : sguPibar θ β Pis φπ ≤ x) (hx' : 0 < x') :
    sguB θ Y β Pis φπ x' ≠ sguA θ Y β Pis φπ x := by
  have h1 := sguA_antitone (θ := θ) (Pis := Pis) hY hβ (by linarith : (0 : ℝ) ≤ φπ) hx
  rw [(sguPibar_spec hθ hY hβ hφπ hPis hc).2.2] at h1
  have h2 := sguB_gt hθ hY hβ hx' hc (Pis := Pis) (φπ := φπ)
  intro h
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `A` and `B` are continuous at every `Π > 0`. -/
theorem sguAB_continuousAt {θ Y β Pis φπ x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    ContinuousAt (sguA θ Y β Pis φπ) x ∧ ContinuousAt (sguB θ Y β Pis φπ) x := by
  have hφ := (phiSGU_continuous β Pis φπ).continuousAt (x := x)
  have hl : ContinuousAt (fun z => lamSGU θ Y (phiSGU β Pis φπ z)) x := by
    unfold lamSGU
    exact ((continuousAt_const.add (continuousAt_const.mul (continuousAt_const.add hφ)))).div
      continuousAt_const hY.ne'
  refine ⟨hl.div (continuousAt_const.add hφ) (by linarith [phiSGU_nonneg β Pis φπ x]), ?_⟩
  exact (continuousAt_const.mul hl).div continuousAt_id hx.ne'

/-! ## Exclusion of self-fulfilling inflations and deflations -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "it is not possible to have a perfect-foresight equilibrium sequence
… in which `Π_t > Π*` in any period", under the added E5 hypothesis
`β + θΠ*(1 − φ_π) > 0` (with `φ_π > 1`, `Π* > β`): every solution of (4.5) satisfies `Π_t ≤ Π*`
at all dates. (Proof: above `Π*` the path must rise — `B > A` there and `B` is decreasing —
while `B > θφ_π/Ȳ` keeps it below `Π̄`; a bounded increasing path would converge to a steady
state above `Π*`, which does not exist.) -/
theorem sgu_no_hyperinflation {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) : ∀ t, Pi_ t ≤ Pis := by
  intro t0
  by_contra hcon
  push Not at hcon
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  set y : ℕ → ℝ := fun n => Pi_ (n + t0) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + t0 = n + t0 + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hstep : ∀ n, Pis < y n ∧ y n < y (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : Pis < y 0 := by simp only [hy, zero_add]; exact hcon
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos 1) (hypos 0) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB 0] at h1
      linarith
    | succ n ih =>
      have h0 : Pis < y (n + 1) := by linarith [ih.1, ih.2]
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos _) (hypos _) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB (n + 1)] at h1
      linarith
  have hmono : Monotone y := monotone_nat_of_le_succ fun n => (hstep n).2.le
  have hbdd : BddAbove (Set.range y) := by
    refine ⟨sguPibar θ β Pis φπ, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_contra hgt
    push Not at hgt
    exact sgu_no_successor hθ hY hβ hφπ hPis hc hgt.le (hypos (n + 1)) (hyAB n)
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, y n with hL
  have hL0 : y 0 ≤ L := le_ciSup hbdd 0
  have hLpos : 0 < L := by linarith [hypos 0]
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY hLpos
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have := sguA_lt_B_above hθ hY hβ hφπ hPis (by linarith [(hstep 0).1] : Pis < L) (Y := Y)
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 and §4.2: under the hypotheses of `sgu_no_hyperinflation`, a
perfect-foresight path that is ever below `Π*` converges to the Friedman rate `Π** = β`. -/
theorem sgu_deflation_tendsto {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) {t0 : ℕ} (ht0 : Pi_ t0 < Pis) :
    Tendsto Pi_ atTop (𝓝 β) := by
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  obtain ⟨-, -, hBβ, hAle, hAmax⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
  -- the successor of any `Π < Π*` lies in `[β, max(Π, β)]`, strictly below `Π` if `Π > β`
  have hsucc : ∀ x x', 0 < x → x < Pis → 0 < x' →
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x → β ≤ x' ∧ (x ≤ β → x' = β) ∧
        (β < x → x' < x) := by
    intro x x' hx hxP hx' hBA
    have hlow : β ≤ x' := by
      by_contra hlt
      push Not at hlt
      have := hsa hx' hβ hlt
      rw [hBA, hBβ] at this
      linarith [hAmax x]
    refine ⟨hlow, fun hxβ => ?_, fun hxβ => ?_⟩
    · rw [hAle x hxβ, ← hBβ] at hBA
      exact hsa.injOn hx' hβ hBA
    · by_contra hge
      push Not at hge
      have h1 := hsa.antitoneOn hx hx' hge
      have h2 := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hxβ hxP
      rw [hBA] at h1
      linarith
  set y : ℕ → ℝ := fun n => Pi_ (n + (t0 + 1)) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + (t0 + 1) = n + (t0 + 1) + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hy0 : β ≤ y 0 ∧ y 0 < Pis := by
    have h := hsucc _ _ (hpath.1 t0) ht0 (hpath.1 (t0 + 1)) (hAB t0)
    simp only [hy, zero_add]
    refine ⟨h.1, ?_⟩
    rcases le_or_gt (Pi_ t0) β with hle | hlt
    · rw [h.2.1 hle]; exact hPis
    · exact lt_trans (h.2.2 hlt) ht0
  have hstep : ∀ n, (β ≤ y n ∧ y n < Pis) ∧ y (n + 1) ≤ y n := by
    intro n
    induction n with
    | zero =>
      refine ⟨hy0, ?_⟩
      have h := hsucc _ _ (hypos 0) hy0.2 (hypos 1) (hyAB 0)
      rcases hy0.1.lt_or_eq with hlt | heq
      · exact (h.2.2 hlt).le
      · rw [h.2.1 heq.symm.le, heq]
    | succ n ih =>
      have h := hsucc _ _ (hypos n) ih.1.2 (hypos (n + 1)) (hyAB n)
      have hmem : β ≤ y (n + 1) ∧ y (n + 1) < Pis := ⟨h.1, lt_of_le_of_lt ih.2 ih.1.2⟩
      refine ⟨hmem, ?_⟩
      have h' := hsucc _ _ (hypos (n + 1)) hmem.2 (hypos (n + 2)) (hyAB (n + 1))
      rcases hmem.1.lt_or_eq with hlt | heq
      · exact (h'.2.2 hlt).le
      · rw [h'.2.1 heq.symm.le, heq]
  have hanti : Antitone y := antitone_nat_of_succ_le fun n => (hstep n).2
  have hbdd : BddBelow (Set.range y) := ⟨β, by rintro _ ⟨n, rfl⟩; exact (hstep n).1.1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, y n with hL
  have hLβ : β ≤ L := le_ciInf fun n => (hstep n).1.1
  have hLP : L < Pis := lt_of_le_of_lt (ciInf_le hbdd 0) (hstep 0).1.2
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY
    (by linarith : 0 < L) (Y := Y)
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have hLeq : L = β := by
    rcases hLβ.lt_or_eq with hlt | heq'
    · have := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hlt hLP
      linarith
    · exact heq'.symm
  rw [hLeq] at hlim
  exact (tendsto_add_atTop_iff_nat (t0 + 1)).mp hlim

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "Schmitt-Grohé and Uribe establish that in the case of an
interest-rate rule satisfying the Taylor principle and a balanced-budget fiscal rule, the unique
perfect-foresight equilibrium is the one in which `Π_t = Π*` at all times", under the added E5
hypothesis `β + θΠ*(1 − φ_π) > 0`: with nominal liabilities growing at `μ̄`, `1 < μ̄ < Π*/β`,
the constant path `Π*` solves (4.5) and satisfies the transversality condition (1.24), and a
solution of (4.5) satisfies (1.24) iff it is that constant path. -/
theorem sgu_unique_pf_equilibrium {θ Y β Pis φπ μ : ℝ} {Pi_ P D : ℕ → ℝ} (hθ : 0 < θ)
    (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hμ : 1 < μ) (hμPis : β * μ < Pis)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) ∧
      (Tendsto (tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_ P D) atTop (𝓝 0) ↔
        ∀ t, Pi_ t = Pis) := by
  have htarget : 1 + phiSGU β Pis φπ Pis = Pis / β := by
    rw [phiSGU_target hβ hPis.le]; ring
  have hconst : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) :=
    ⟨fun _ => by linarith, fun _ => by
      rw [htarget]; field_simp⟩
  refine ⟨hconst, ⟨fun htvc t => ?_, fun hall => ?_⟩⟩
  · have hle := sgu_no_hyperinflation hθ hY hβ hφπ hPis hc hpath t
    by_contra hne
    have hlt : Pi_ t < Pis := lt_of_le_of_ne hle hne
    have hlim := sgu_deflation_tendsto hθ hY hβ hφπ hPis hc hpath hlt
    obtain ⟨-, hφβ, -, -, -⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
    exact deflation_tvc_violated hβ hpath (fun s => lamSGU_phi_pos hθ hY)
      (fun s => phiSGU_nonneg _ _ _ _) hP hPrec hD hDpos hlim
      (phiSGU_continuous β Pis φπ).continuousAt (by rw [hφβ, div_self hβ.ne']; ring)
      (by rw [div_self hβ.ne']; exact hμ) htvc
  · have hPi : Pi_ = fun _ => Pis := funext hall
    subst hPi
    exact (target_tvc_iff hβ (by linarith) (by linarith) htarget (lamSGU_phi_pos hθ hY) hP
      hPrec hD hDpos).mpr hμPis

/-! ## Error E5: a counterexample when `β + θΠ*(1 − φ_π) < 0` -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the successor map on the upper branch of (4.5) in the
counterexample `β = 1/2, θ = 1, φ_π = 3/2, Π* = 3, Ȳ = 1`: `Π ↦ (6Π − 6)/(3Π − 5)`. -/
noncomputable def gE5 (x : ℝ) : ℝ := (6 * x - 6) / (3 * x - 5)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the price level `P_t = ∏_{s<t} Π_{s+1}` (with `P₀ = 1`). -/
def priceFrom (Pi_ : ℕ → ℝ) (t : ℕ) : ℝ := ∏ s ∈ Finset.range t, Pi_ (s + 1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: in the counterexample, `φ(Π) = 3Π − 4` for `Π ≥ 4/3`. -/
theorem phiE5 {x : ℝ} (hx : 4 / 3 ≤ x) : phiSGU (1 / 2) 3 (3 / 2) x = 3 * x - 4 := by
  unfold phiSGU ellSGU
  rw [max_eq_right (by linarith)]
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the interval `[32/13, 4]` is invariant under the upper
branch map. -/
theorem gE5_mem {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) : 32 / 13 ≤ gE5 x ∧ gE5 x ≤ 4 := by
  unfold gE5
  have hd : 0 < 3 * x - 5 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: on `[32/13, 4]` the upper branch map solves (4.5). -/
theorem gE5_eq45 {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) :
    gE5 x / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) (gE5 x)) =
      1 / 2 * (1 + phiSGU (1 / 2) 3 (3 / 2) x) / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) x) := by
  have hg := gE5_mem h1 h2
  rw [phiE5 (by linarith), phiE5 (by linarith [hg.1])]
  unfold lamSGU gE5
  have hd : 0 < 3 * x - 5 := by linarith
  have e1 : (1 + 1 * (1 + (3 * ((6 * x - 6) / (3 * x - 5)) - 4))) / 1 =
      (12 * x - 8) / (3 * x - 5) := by
    field_simp; ring
  have e2 : (1 + 1 * (1 + (3 * x - 4))) / 1 = 3 * x - 2 := by ring
  rw [e1, e2, div_div_div_cancel_right₀ hd.ne', div_eq_div_iff (by linarith) (by linarith)]
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, p. 655, error E5 — counterexample. Take `β = 1/2`, `θ = 1`,
`φ_π = 3/2 > 1` (Taylor principle), `Π* = 3`, `Ȳ = 1`; then `β + θΠ*(1 − φ_π) = −1 < 0`, and:
(i) the printed bound `Π̄` (`A(Π̄) = θφ_π/Ȳ`) is `5/3 < Π*`; (ii) `B` is not decreasing
(`B(3) < B(4)`); (iii) contrary to "in the case of any `Π_t ≥ Π̄` there is no value for `Π_{t+1}`
that would satisfy (4.5)", `Π_t = 4` has the successor `18/7`; (iv) with nominal liabilities
`D_t = 2^t` (`μ̄ = 2 ∈ (1, Π*/β)`) and `P_t = ∏_{s<t}Π_{s+1}`, both `Π_t ≡ 3` and the path
`Π_0 = 4`, `Π_{t+1} = (6Π_t − 6)/(3Π_t − 5)` solve (4.5), satisfy (4.4) (with
`L(i) = Ȳ/(1 + θ(1 + i))`) and satisfy the transversality condition (1.24): the
perfect-foresight equilibrium is not unique, and `Π_0 = 4 > Π*` refutes "`Π_t ≤ Π*` at all
times". -/
theorem e5_counterexample :
    sguC 1 (1 / 2) 3 (3 / 2) = -1 ∧
      (sguA 1 1 (1 / 2) 3 (3 / 2) (5 / 3) = 1 * (3 / 2) / 1 ∧ (5 / 3 : ℝ) < 3) ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) 3 < sguB 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) (18 / 7) = sguA 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      (IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3)
          (priceFrom fun _ => 3) (fun t => 2 ^ t)) atTop (𝓝 0)) ∧
      ∃ Pi_ : ℕ → ℝ, Pi_ 0 = 4 ∧ IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ ∧
        Summable (bound44Term (1 / 2) 1 (lamSGU 1 1) (LSGU 1 1)
          (fun t => phiSGU (1 / 2) 3 (3 / 2) (Pi_ t))) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
          (fun t => 2 ^ t)) atTop (𝓝 0) := by
  have hφ3 : phiSGU (1 / 2) 3 (3 / 2) 3 = 5 := by rw [phiE5 (by norm_num)]; norm_num
  have hφ4 : phiSGU (1 / 2) 3 (3 / 2) 4 = 8 := by rw [phiE5 (by norm_num)]; norm_num
  refine ⟨by unfold sguC; norm_num, ⟨?_, by norm_num⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold sguA lamSGU; rw [phiE5 (by norm_num)]; norm_num
  · unfold sguB lamSGU; rw [hφ3, hφ4]; norm_num
  · unfold sguA sguB lamSGU; rw [phiE5 (by norm_num), hφ4]; norm_num
  · exact ⟨fun _ => by norm_num, fun _ => by unfold lamSGU; rw [hφ3]; norm_num⟩
  · refine (target_tvc_iff (μ := 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hφ3]; norm_num)
      (by unfold lamSGU; rw [hφ3]; norm_num) (fun t => by unfold priceFrom; positivity)
      (fun t => by unfold priceFrom; rw [Finset.prod_range_succ, mul_comm])
      (fun t => by show (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t; ring) (fun t => by positivity)).mpr
      (by norm_num)
  · set Pi_ : ℕ → ℝ := fun t => gE5^[t] 4 with hPi
    have hsucc : ∀ t, Pi_ (t + 1) = gE5 (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
    have hmem : ∀ t, 32 / 13 ≤ Pi_ t ∧ Pi_ t ≤ 4 := by
      intro t
      induction t with
      | zero => simp only [hPi, Function.iterate_zero, id]; norm_num
      | succ n ih => rw [hsucc]; exact gE5_mem ih.1 ih.2
    have hpos : ∀ t, 0 < Pi_ t := fun t => by linarith [(hmem t).1]
    have hpath : IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ :=
      ⟨hpos, fun t => by rw [hsucc]; exact gE5_eq45 (hmem t).1 (hmem t).2⟩
    have hφ : ∀ t, phiSGU (1 / 2) 3 (3 / 2) (Pi_ t) = 3 * Pi_ t - 4 := fun t =>
      phiE5 (by linarith [(hmem t).1])
    refine ⟨Pi_, rfl, hpath, ?_, ?_⟩
    · refine (bound44_summable (β := 1 / 2) (ybar := 1) (Λ := 10) (K := 1) (by norm_num)
        (by norm_num) (by norm_num)
        (fun T => phiSGU_nonneg _ _ _ _) (fun T => lamSGU_phi_pos one_pos one_pos)
        (fun T => ?_) (fun j hj => ?_) (fun j hj => ?_)).2
      · unfold lamSGU; rw [hφ T]; linarith [(hmem T).2]
      · unfold LSGU; positivity
      · unfold LSGU
        rw [mul_div_assoc', div_le_one (by linarith)]
        linarith
    · have hP : ∀ t, 0 < priceFrom Pi_ t := fun t =>
        Finset.prod_pos fun s _ => hpos (s + 1)
      have hPrec : ∀ t, priceFrom Pi_ (t + 1) = Pi_ (t + 1) * priceFrom Pi_ t := fun t => by
        unfold priceFrom; rw [Finset.prod_range_succ, mul_comm]
      have hD : ∀ t, (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := fun t => by ring
      set V := tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
        (fun t => 2 ^ t) with hV
      have hVsucc : ∀ T, V (T + 1) = V T * (2 / (1 + phiSGU (1 / 2) 3 (3 / 2) (Pi_ T))) :=
        tvcValue_succ (by norm_num) hpath (fun t => lamSGU_phi_pos one_pos one_pos)
          (fun t => by linarith [phiSGU_nonneg (1 / 2) 3 (3 / 2) (Pi_ t)]) hP hPrec hD
      have hV0 : ∀ T, 0 ≤ V T := fun T => by
        simp only [hV, tvcValue]
        have := lamSGU_phi_pos (β := 1 / 2) (Pis := 3) (φπ := 3 / 2) (x := Pi_ T)
          one_pos one_pos
        have := hP T
        positivity
      have hVle : ∀ T, V T ≤ V 0 * (26 / 57) ^ T := by
        intro T
        induction T with
        | zero => simp
        | succ n ih =>
          rw [hVsucc, hφ n, pow_succ]
          have h1 : 2 / (1 + (3 * Pi_ n - 4)) ≤ 26 / 57 := by
            rw [div_le_div_iff₀ (by linarith [(hmem n).1]) (by norm_num)]
            linarith [(hmem n).1]
          have h2 : 0 ≤ 2 / (1 + (3 * Pi_ n - 4)) := div_nonneg (by norm_num)
            (by linarith [(hmem n).1])
          calc V n * (2 / (1 + (3 * Pi_ n - 4))) ≤ V 0 * (26 / 57) ^ n * (2 / (1 + (3 * Pi_ n - 4)))
                := mul_le_mul_of_nonneg_right ih h2
            _ ≤ V 0 * (26 / 57) ^ n * (26 / 57) :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg (hV0 0) (by positivity))
            _ = V 0 * ((26 / 57) ^ n * (26 / 57)) := by ring
      have hlim : Tendsto (fun T => V 0 * (26 / 57 : ℝ) ^ T) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 26 / 57)
          (by norm_num)).const_mul (V 0)
      exact squeeze_zero hV0 hVle hlim

end SGU

/-! ## (16.31)–(16.32): residual money demand -/

/-- Cochrane (2023), eqs. (16.31)–(16.32), p. 393: with the rule `1 + i_t = Φ(Π_t)/β` and money
demand `M_t/P_t = L(y, i_t)`, write `k(Π) = u_c[y, L(y, Φ(Π)/β − 1)]` for the marginal utility at
the rule's interest rate. Then the intertemporal condition (16.31)
`1 + i_t = Π_{t+1}u_c(t)/(βu_c(t+1))` is equivalent to (16.32)
`Π_{t+1} = Φ(Π_t) k(Π_{t+1})/k(Π_t)`. (The book writes `L(y, Φ(Π))`; the argument of `L` is the
interest rate, `Φ(Π)/β − 1`.) -/
theorem eq1632_iff {β x x' : ℝ} {Φ k : ℝ → ℝ} (hβ : 0 < β) (hk : 0 < k x) (hk' : 0 < k x') :
    Φ x / β = x' * k x / (β * k x') ↔ x' = Φ x * k x' / k x := by
  generalize k x = a at hk ⊢
  generalize k x' = b at hk' ⊢
  rw [div_eq_div_iff hβ.ne' (by positivity), eq_div_iff hk.ne']
  constructor
  · intro h
    have : β * (x' * a) = β * (Φ x * b) := by linarith
    have := mul_left_cancel₀ hβ.ne' this
    linarith
  · intro h
    linear_combination (-β) * h

/-- Cochrane (2023), eq. (16.32), p. 393, and Woodford (2003), eq. (4.5), p. 125: with
`λ(i) = u_c[y, L(y, i)]` and Woodford's rule `φ(Π) = Φ(Π)/β − 1`, a positive path satisfies
(16.32) at every date iff it is a solution of Woodford's (4.5) (`GlobalDynamics.IsPath45`); so the
Schmitt-Grohé–Uribe results of `SGU` apply to (16.32). -/
theorem eq1632_iff_path45 {β : ℝ} {Φ lam : ℝ → ℝ} {infl : ℕ → ℝ} (hβ : 0 < β)
    (hlam : ∀ t, 0 < lam (Φ (infl t) / β - 1)) (hpos : ∀ t, 0 < infl t) :
    IsPath45 β lam (fun x => Φ x / β - 1) infl ↔
      ∀ t, infl (t + 1) =
        Φ (infl t) * lam (Φ (infl (t + 1)) / β - 1) / lam (Φ (infl t) / β - 1) := by
  unfold IsPath45
  simp only [hpos, implies_true, true_and]
  refine forall_congr' fun t => ?_
  have h1 := hlam t
  have h2 := hlam (t + 1)
  have hb : β * (1 + (Φ (infl t) / β - 1)) = Φ (infl t) := by field_simp; ring
  rw [hb]
  generalize lam (Φ (infl t) / β - 1) = a at h1 ⊢
  generalize lam (Φ (infl (t + 1)) / β - 1) = b at h2 ⊢
  rw [div_eq_div_iff h2.ne' h1.ne', eq_div_iff h1.ne']

/-- Cochrane (2023), (16.32), p. 393, correction: "the difference equation (16.32) may rise to
require `Π_{t+1} = ∞` above some bound `Π_U`, even if the policy rule for nominal interest rates
… remains bounded" cannot happen when the rule is continuous and bounded and `k = u_c ∘ L` is
continuous and positive on the (compact) range of interest rates the rule sets: then every
`Π_t > 0` has a finite successor `Π_{t+1} > 0` solving (16.32). An explosion in finite time needs
an unbounded rule (as in Schmitt-Grohé–Uribe, `SGU.sgu_no_successor`) or `u_c ∘ L` vanishing or
exploding at a finite rate (money demand hitting zero). -/
theorem successor_exists_of_bounded_rule {β ilo ihi : ℝ} {Φ k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Icc ilo ihi)) (hkpos : ∀ j ∈ Set.Icc ilo ihi, 0 < k j)
    (hΦc : ContinuousOn Φ (Set.Ioi 0)) (hΦpos : ∀ x, 0 < x → 0 < Φ x)
    (hΦr : ∀ x, 0 < x → Φ x / β - 1 ∈ Set.Icc ilo ihi) {x : ℝ} (hx : 0 < x) :
    ∃ x', 0 < x' ∧ x' = Φ x * k (Φ x' / β - 1) / k (Φ x / β - 1) := by
  have hne : (Set.Icc ilo ihi).Nonempty := ⟨_, hΦr x hx⟩
  obtain ⟨jm, hjm, hmin⟩ := isCompact_Icc.exists_isMinOn hne hk
  obtain ⟨jM, hjM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hk
  set m := k jm with hm
  set M := k jM with hM
  have hm0 : 0 < m := hkpos jm hjm
  set H : ℝ → ℝ := fun z => k (Φ z / β - 1) with hH
  have hHb : ∀ z, 0 < z → m ≤ H z ∧ H z ≤ M := fun z hz =>
    ⟨hmin (hΦr z hz), hmax (hΦr z hz)⟩
  have hHc : ContinuousOn H (Set.Ioi 0) := by
    refine hk.comp (((hΦc.div_const β).sub continuousOn_const)) fun z hz => hΦr z hz
  set c := Φ x / H x with hc
  have hc0 : 0 < c := div_pos (hΦpos x hx) (lt_of_lt_of_le hm0 (hHb x hx).1)
  set a := c * m / 2 with ha
  set b := 2 * c * M with hb
  have ha0 : 0 < a := by positivity
  have hmM : m ≤ M := (hHb x hx).1.trans (hHb x hx).2
  have hab : a ≤ b := by
    rw [ha, hb]; nlinarith
  set G : ℝ → ℝ := fun z => z / H z with hG
  have hGc : ContinuousOn G (Set.Icc a b) := by
    have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha0 hz.1
    exact (continuousOn_id.mono hsub).div (hHc.mono hsub) fun z hz =>
      (lt_of_lt_of_le hm0 (hHb z (lt_of_lt_of_le ha0 hz.1)).1).ne'
  have hGa : G a ≤ c := by
    have h1 := (hHb a ha0).1
    simp only [hG]
    rw [div_le_iff₀ (lt_of_lt_of_le hm0 h1)]
    nlinarith
  have hGb : c ≤ G b := by
    have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
    have h1 := (hHb b hb0).2
    have h0 := lt_of_lt_of_le hm0 (hHb b hb0).1
    simp only [hG]
    rw [le_div_iff₀ h0]
    nlinarith
  obtain ⟨z, hz, hGz⟩ := intermediate_value_Icc hab hGc ⟨hGa, hGb⟩
  have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
  have hHz : 0 < H z := lt_of_lt_of_le hm0 (hHb z hz0).1
  refine ⟨z, hz0, ?_⟩
  simp only [hG] at hGz
  have : z = c * H z := by rw [← hGz]; field_simp
  conv_lhs => rw [this]
  simp only [hc, hH]
  ring

/-- Cochrane (2023), (16.32), p. 393, correction (continued): under the hypotheses of
`successor_exists_of_bounded_rule`, every `Π₀ > 0` starts a perfect-foresight path of (16.32)
defined at all dates: no explosion in finite time. -/
theorem path_exists_of_bounded_rule {β ilo ihi : ℝ} {Φ k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Icc ilo ihi)) (hkpos : ∀ j ∈ Set.Icc ilo ihi, 0 < k j)
    (hΦc : ContinuousOn Φ (Set.Ioi 0)) (hΦpos : ∀ x, 0 < x → 0 < Φ x)
    (hΦr : ∀ x, 0 < x → Φ x / β - 1 ∈ Set.Icc ilo ihi) {x0 : ℝ} (hx0 : 0 < x0) :
    ∃ infl : ℕ → ℝ, infl 0 = x0 ∧ (∀ t, 0 < infl t) ∧
      ∀ t, infl (t + 1) = Φ (infl t) * k (Φ (infl (t + 1)) / β - 1) / k (Φ (infl t) / β - 1) := by
  classical
  have hs := fun x (hx : 0 < x) =>
    successor_exists_of_bounded_rule hk hkpos hΦc hΦpos hΦr hx
  let next : ℝ → ℝ := fun x => if hx : 0 < x then Classical.choose (hs x hx) else 1
  have hnext : ∀ x, 0 < x → 0 < next x ∧
      next x = Φ x * k (Φ (next x) / β - 1) / k (Φ x / β - 1) := fun x hx => by
    simp only [next, hx, ↓reduceDIte]
    exact Classical.choose_spec (hs x hx)
  have hpos : ∀ t, 0 < next^[t] x0 := by
    intro t
    induction t with
    | zero => simpa using hx0
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hnext _ ih).1
  refine ⟨fun t => next^[t] x0, rfl, hpos, fun t => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact (hnext _ (hpos t)).2

/-- Cochrane (2023), (16.32), p. 393, explicit bounded-rule model (`β = 1/2`): the Taylor rule
`Φ(Π) = max(1/2, min(2Π − 1, 3))` (target `Π* = 1`, slope 2 there), truncated below at the zero
bound and capped above, so `1/2 ≤ Φ ≤ 3`. -/
noncomputable def boundedRule (x : ℝ) : ℝ := max (1 / 2) (min (2 * x - 1) 3)

/-- Cochrane (2023), (16.32), p. 393: the nominal rate set by `boundedRule` with `β = 1/2`,
`i = Φ(Π)/β − 1 = 2Φ(Π) − 1 ∈ [0, 5]`. -/
noncomputable def boundedRate (x : ℝ) : ℝ := 2 * boundedRule x - 1

/-- Cochrane (2023), (16.32), p. 393: money demand `M/P = L(i) = 5 − i`, positive for `i < 5`
and vanishing at the finite rate `i = 5` (the rate the capped rule reaches at `Π ≥ 2`). -/
def moneyDemand (i : ℝ) : ℝ := 5 - i

/-- Cochrane (2023), (16.31), p. 393: marginal utility of consumption as a function of real
money, `u_c(y, m) = 1/m` (e.g. a cash constraint `c ≤ m` with log utility), so `u_c ∘ L` blows
up as `i ↑ 5`. -/
noncomputable def ucMoney (m : ℝ) : ℝ := 1 / m

/-- Cochrane (2023), (16.32), p. 393: the rate set by the bounded rule is
`max(0, min(4Π − 3, 5))`, so it is at least `min(4Π − 3, 5)`. -/
theorem boundedRate_ge (x : ℝ) : min (4 * x - 3) 5 ≤ boundedRate x := by
  unfold boundedRate boundedRule
  rcases le_total (2 * x - 1) 3 with h1 | h1
  · rw [min_eq_left h1]
    have := le_max_right (1 / 2 : ℝ) (2 * x - 1)
    have := min_le_left (4 * x - 3) 5
    linarith
  · rw [min_eq_right h1]
    have := le_max_right (1 / 2 : ℝ) 3
    have := min_le_right (4 * x - 3) 5
    linarith

/-- Cochrane (2023), (16.32), p. 393, "the difference equation (16.32) may rise to require
`Π_{t+1} = ∞` above some bound `Π_U`, even if the policy rule for nominal interest rates … remains
bounded", made exact. With `β = 1/2`, the bounded rule `boundedRule` (`1/2 ≤ Φ ≤ 3`, rates in
`[0, 5]`, target `Π* = 1` with `Φ′(Π*) = 2`), money demand `L(i) = 5 − i` and `u_c = 1/m`, the
composite `u_c ∘ L` blows up at the finite rate `i = 5`, and for every `Π_t ∈ (1, 3/2)` there is
no `Π_{t+1} > 0` with positive money demand solving (16.32): inflation slightly above target
requires infinite inflation next period. Together with `successor_exists_of_bounded_rule`
(necessity of a singular `u_c ∘ L` on the range of rates) this settles the book's claim. -/
theorem bounded_rule_explosion :
    (∀ x, 1 / 2 ≤ boundedRule x ∧ boundedRule x ≤ 3) ∧
      (∀ x, 0 ≤ boundedRate x ∧ boundedRate x ≤ 5) ∧
      boundedRule 1 = 1 ∧ HasDerivAt boundedRule 2 1 ∧
      (∀ i, i < 5 → 0 < moneyDemand i) ∧
      Tendsto (fun i => ucMoney (moneyDemand i)) (𝓝[<] 5) atTop ∧
      ∀ x ∈ Set.Ioo (1 : ℝ) (3 / 2), ¬ ∃ x', 0 < x' ∧ 0 < moneyDemand (boundedRate x') ∧
        x' = boundedRule x * ucMoney (moneyDemand (boundedRate x')) /
          ucMoney (moneyDemand (boundedRate x)) := by
  have hbd : ∀ x, 1 / 2 ≤ boundedRule x ∧ boundedRule x ≤ 3 := fun x =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  refine ⟨hbd, fun x => ?_, ?_, ?_, fun i hi => by unfold moneyDemand; linarith, ?_, ?_⟩
  · unfold boundedRate; constructor <;> linarith [hbd x]
  · norm_num [boundedRule]
  · have h : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).sub_const 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)]
      with y hy
    unfold boundedRule
    rw [min_eq_left (by linarith [hy.2]), max_eq_right (by linarith [hy.1])]
  · have h1 : Tendsto (fun i : ℝ => moneyDemand i) (𝓝[<] 5) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun i : ℝ => 5 - i) (𝓝 5) (𝓝 (5 - 5)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with i hi
        simp only [Set.mem_Ioi, moneyDemand]
        linarith [Set.mem_Iio.mp hi]
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine h2.congr fun i => ?_
    simp [ucMoney]
  · rintro x hx ⟨x', hx'0, hL, heq⟩
    have hΦ : boundedRule x = 2 * x - 1 := by
      unfold boundedRule
      rw [min_eq_left (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
    have hr : boundedRate x = 4 * x - 3 := by unfold boundedRate; rw [hΦ]; ring
    have hLx : 0 < moneyDemand (boundedRate x) := by
      rw [hr]; unfold moneyDemand; linarith [hx.2]
    -- `x' · L(i(x')) = Φ(x) · L(i(x)) = (2x − 1)(8 − 4x) > 4`
    have hprod : x' * moneyDemand (boundedRate x') =
        (2 * x - 1) * moneyDemand (boundedRate x) := by
      rw [← hΦ]
      generalize moneyDemand (boundedRate x') = A at heq hL ⊢
      generalize moneyDemand (boundedRate x) = B at heq hLx ⊢
      rw [heq]
      unfold ucMoney
      field_simp
    have hbig : 4 < (2 * x - 1) * moneyDemand (boundedRate x) := by
      rw [hr]; unfold moneyDemand; nlinarith [hx.1, hx.2]
    -- but `x' · L(i(x')) ≤ 4` whenever money demand is positive
    have hge := boundedRate_ge x'
    have hsmall : x' * moneyDemand (boundedRate x') ≤ 4 := by
      rcases le_total (4 * x' - 3) 5 with h1 | h1
      · rw [min_eq_left h1] at hge
        unfold moneyDemand
        nlinarith [sq_nonneg (x' - 1)]
      · rw [min_eq_right h1] at hge
        unfold moneyDemand at hL
        linarith
    linarith

/-! ## §16.10.4 Threaten negative nominal rates (Bassetto) -/

/-- Cochrane (2023), §16.10.4, p. 391, Bassetto (2004): if the rule ignores the zero bound and
`Π*` is its only steady state on `[β, Π*]` — `Φ` continuous there with `Φ(Π) < Π` on `[β, Π*)` —
then every path of (16.29) starting in `[β, Π*)` reaches `Π_{t+1} < β`, i.e. `i_t < 0`, in finite
time ("the minute we pass the zero bound, no equilibrium can form"). -/
theorem bassetto_exit {Φ : ℝ → ℝ} {β Pis : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Icc β Pis)) (hbelow : ∀ x ∈ Set.Ico β Pis, Φ x < x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ico β Pis) :
    ∃ t, infl (t + 1) < β := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ t, infl t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      refine ⟨hcon n, ?_⟩
      rw [hpath]; exact lt_trans (hbelow _ ih) ih.2
  have hanti : Antitone infl := antitone_nat_of_succ_le fun t => by
    rw [hpath]; exact (hbelow _ (hmem t)).le
  have hbdd : BddBelow (Set.range infl) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, infl t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hmem t).1
  have hL0 : L ≤ infl 0 := ciInf_le hbdd 0
  have hLmem : L ∈ Set.Icc β Pis := ⟨hLβ, hL0.trans h0.2.le⟩
  have hwithin : Tendsto infl atTop (𝓝[Set.Icc β Pis] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun t => ⟨(hmem t).1, (hmem t).2.le⟩⟩
  have h1 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 (Φ L)) :=
    (hcont L hLmem).tendsto.comp hwithin
  have h2 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 L) := by
    have : (fun t => Φ (infl t)) = fun t => infl (t + 1) := funext fun t => (hpath t).symm
    rw [this]; exact (tendsto_add_atTop_iff_nat 1).mpr hlim
  have hfix := tendsto_nhds_unique h1 h2
  have := hbelow L ⟨hLβ, lt_of_le_of_lt hL0 h0.2⟩
  linarith

/-- Cochrane (2023), §16.10.4, pp. 391–392, "such a `Φ(Π)` function cleanly rules out
deflationary equilibria": under Bassetto's rule there is no equilibrium (with the zero bound,
`LowerBound.IsEquilibrium`) whose initial inflation lies in `[β, Π*)`. -/
theorem bassetto_no_equilibrium {r : ℝ} {Φ : ℝ → ℝ} {Pis Pm1 : ℝ} {P i s D : ℕ → ℝ}
    (hr : 0 < 1 + r) (hcont : ContinuousOn Φ (Set.Icc (1 + r)⁻¹ Pis))
    (hbelow : ∀ x ∈ Set.Ico (1 + r)⁻¹ Pis, Φ x < x) (h : IsEquilibrium r Φ Pm1 P i s D)
    (h0 : infl Pm1 P 0 ∈ Set.Ico (1 + r)⁻¹ Pis) : False := by
  obtain ⟨hdyn, hzb, -, -⟩ := equilibrium_dynamics hr h
  obtain ⟨t, ht⟩ := bassetto_exit hcont hbelow hdyn h0
  linarith [hzb t]

/-- Cochrane (2023), §16.10.4, p. 391: the linear rule `Φ(Π) = Π* + φ(Π − Π*)`, `φ > 1`, applied
without the zero bound. -/
def linRule (Pis φ : ℝ) (x : ℝ) : ℝ := Pis + φ * (x - Pis)

/-- Cochrane (2023), §16.10.4, pp. 391–392: the linear rule satisfies Bassetto's hypotheses
(continuous, `Φ(Π) < Π` below `Π*`), the gap below target grows as `φᵗ`, and above `Π*` the
inflationary paths stay above `Π*` — those equilibria are not removed. -/
theorem linear_rule_exit {Pis φ : ℝ} (hφ : 1 < φ) :
    Continuous (linRule Pis φ) ∧ (∀ x, x < Pis → linRule Pis φ x < x) ∧
      (∀ x0 t, Pis - (linRule Pis φ)^[t] x0 = φ ^ t * (Pis - x0)) ∧
      ∀ x0 t, Pis ≤ x0 → Pis ≤ (linRule Pis φ)^[t] x0 := by
  have hgap : ∀ x0 t, Pis - (linRule Pis φ)^[t] x0 = φ ^ t * (Pis - x0) := by
    intro x0 t
    induction t with
    | zero => simp
    | succ n ih =>
      rw [orbit_succ]
      simp only [linRule]
      rw [pow_succ]
      linear_combination φ * ih
  refine ⟨by unfold linRule; fun_prop, fun x hx => ?_, hgap, fun x0 t hx0 => ?_⟩
  · simp only [linRule]; nlinarith
  · have := hgap x0 t
    have : φ ^ t * (Pis - x0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith) t) (by linarith)
    linarith

/-! ## §16.10.5 Weird Taylor rules -/

/-- Cochrane (2023), §16.10.5, p. 392, Woodford (2003, p. 136): if the rule becomes vertical at
`Π_U > Π*` (`Φ(Π) → ∞` as `Π ↑ Π_U`), is continuous on `(Π*, Π_U)` with `Φ(Π) > Π` there, then
every path starting in `(Π*, Π_U)` reaches `Π_U` in finite time — infinite inflation, an
explosion "in finite time". -/
theorem vertical_rule_exit {Φ : ℝ → ℝ} {Pis PiU : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Ioo Pis PiU)) (habove : ∀ x ∈ Set.Ioo Pis PiU, x < Φ x)
    (hvert : Tendsto Φ (𝓝[<] PiU) atTop) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (h0 : infl 0 ∈ Set.Ioo Pis PiU) : ∃ t, PiU ≤ infl t := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ t, infl t ∈ Set.Ioo Pis PiU := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      refine ⟨?_, hcon (n + 1)⟩
      rw [hpath]; exact lt_trans ih.1 (habove _ ih)
  have hmono : Monotone infl := monotone_nat_of_le_succ fun t => by
    rw [hpath]; exact (habove _ (hmem t)).le
  have hbdd : BddAbove (Set.range infl) := ⟨PiU, by rintro _ ⟨t, rfl⟩; exact (hmem t).2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t, infl t with hL
  have hLU : L ≤ PiU := ciSup_le fun t => (hmem t).2.le
  have hL0 : infl 0 ≤ L := le_ciSup hbdd 0
  rcases hLU.lt_or_eq with hlt | heq
  · have hLmem : L ∈ Set.Ioo Pis PiU := ⟨lt_of_lt_of_le h0.1 hL0, hlt⟩
    have hfix := fixed_of_tendsto hpath hlim (hcont.continuousAt (Ioo_mem_nhds hLmem.1 hLmem.2))
    linarith [habove L hLmem]
  · have hw : Tendsto infl atTop (𝓝[<] PiU) :=
      tendsto_nhdsWithin_iff.mpr ⟨heq ▸ hlim, Eventually.of_forall fun t => (hmem t).2⟩
    have h1 : Tendsto (fun t => infl (t + 1)) atTop atTop := by
      have : (fun t => infl (t + 1)) = fun t => Φ (infl t) := funext hpath
      rw [this]; exact hvert.comp hw
    obtain ⟨t, ht⟩ := (h1.eventually (eventually_gt_atTop PiU)).exists
    linarith [(hmem (t + 1)).2]

/-- Cochrane (2023), §16.10.5, p. 392, Alstadheim and Henderson (2006): if the rule sends every
`Π ≠ Π*` above `Π*`, lies above the diagonal above `Π*` and is continuous there, every positive
path not starting at `Π*` explodes. -/
theorem v_rule_unbounded {Φ : ℝ → ℝ} {Pis : ℝ} {infl : ℕ → ℝ}
    (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (hpos : 0 < infl 0) (hne : infl 0 ≠ Pis) : Tendsto infl atTop atTop := by
  have h1 : Pis < infl 1 := by rw [hpath]; exact hjump _ hpos hne
  have hup : ∀ n, Pis < infl (n + 1) ∧ infl (n + 1) < infl (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h1, by rw [hpath 1]; exact habove _ h1⟩
    | succ n ih =>
      have h2 : Pis < infl (n + 2) := lt_trans ih.1 ih.2
      exact ⟨h2, by rw [hpath (n + 2)]; exact habove _ h2⟩
  set y : ℕ → ℝ := fun n => infl (n + 1) with hy
  have hypath : ∀ n, y (n + 1) = Φ (y n) := fun n => hpath (n + 1)
  have hymono : Monotone y := monotone_nat_of_le_succ fun n => (hup n).2.le
  rcases monotone_orbit_atTop_or_fixed hypath hymono with htop | ⟨L, -, hLb, hfix⟩
  · exact (tendsto_add_atTop_iff_nat 1).mp htop
  · exfalso
    have hL : Pis < L := lt_of_lt_of_le (hup 0).1 (hLb 0)
    have := hfix (hcont.continuousAt (Ioi_mem_nhds hL))
    linarith [habove L hL]

/-- Cochrane (2023), §16.10.5, p. 392: under the hypotheses of `v_rule_unbounded` with
`Φ(Π*) = Π*`, the target is the unique bounded positive equilibrium path. -/
theorem v_rule_unique_bounded {Φ : ℝ → ℝ} {Pis : ℝ} {infl : ℕ → ℝ}
    (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (hpos : ∀ t, 0 < infl t) (hbdd : BddAbove (Set.range infl)) : ∀ t, infl t = Pis := by
  intro t
  by_contra hne
  have := v_rule_unbounded (infl := fun s => infl (t + s)) hjump habove hcont
    (fun s => by rw [← add_assoc]; exact hpath _) (hpos t) (by simpa using hne)
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨s, hs⟩ := (this.eventually (eventually_gt_atTop M)).exists
  linarith [hM ⟨t + s, rfl⟩]

/-- Cochrane (2023), §16.10.5, p. 392: a V-shaped rule touching the 45° line only at `Π*`,
`Φ(Π) = Π* + 2|Π − Π*|`. -/
noncomputable def vRule (Pis : ℝ) (x : ℝ) : ℝ := Pis + 2 * |x - Pis|

/-- Cochrane (2023), §16.10.5, p. 392: the V-shaped rule satisfies the hypotheses of
`v_rule_unique_bounded` and never sets inflation below `Π*` (so it respects the zero bound when
`Π* ≥ β`). -/
theorem vRule_props (Pis : ℝ) :
    vRule Pis Pis = Pis ∧ (∀ x, x ≠ Pis → Pis < vRule Pis x) ∧
      (∀ x, Pis < x → x < vRule Pis x) ∧ Continuous (vRule Pis) ∧
      ∀ x, Pis ≤ vRule Pis x := by
  refine ⟨by simp [vRule], fun x hx => ?_, fun x hx => ?_, by unfold vRule; fun_prop,
    fun x => ?_⟩
  · have : 0 < |x - Pis| := abs_pos.mpr (sub_ne_zero.mpr hx)
    simp only [vRule]; linarith
  · simp only [vRule]; rw [abs_of_pos (by linarith)]; linarith
  · simp only [vRule]; linarith [abs_nonneg (x - Pis)]

/-- Cochrane (2023), §16.10.5, p. 392, Alstadheim and Henderson (2006): a discontinuous rule that
jumps from below `Π*` to above it, `Φ(Π) = Π* + 1` for `Π < Π*`, `Φ(Π) = Π* + 2(Π − Π*)` for
`Π ≥ Π*`. -/
noncomputable def ahJump (Pis : ℝ) (x : ℝ) : ℝ := if x < Pis then Pis + 1 else Pis + 2 * (x - Pis)

/-- Cochrane (2023), §16.10.5, p. 392: the discontinuous rule `ahJump` satisfies the hypotheses
of `v_rule_unique_bounded`. -/
theorem ahJump_props (Pis : ℝ) :
    ahJump Pis Pis = Pis ∧ (∀ x, x ≠ Pis → Pis < ahJump Pis x) ∧
      (∀ x, Pis < x → x < ahJump Pis x) ∧ ContinuousOn (ahJump Pis) (Set.Ioi Pis) := by
  refine ⟨by simp [ahJump], fun x hx => ?_, fun x hx => ?_, ?_⟩
  · unfold ahJump
    split_ifs with h
    · linarith
    · push Not at h; have := lt_of_le_of_ne h (Ne.symm hx); linarith
  · have hn : ¬ x < Pis := not_lt.mpr hx.le
    simp only [ahJump, hn, ↓reduceIte]
    linarith
  · have : Set.EqOn (ahJump Pis) (fun x => Pis + 2 * (x - Pis)) (Set.Ioi Pis) := fun x hx => by
      have hn : ¬ x < Pis := not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hx))
      simp only [ahJump, hn, ↓reduceIte]
    exact (ContinuousOn.congr (by fun_prop) this)

/-- Cochrane (2023), §16.10.5, p. 392: a rule tangent to the 45° line at `Π*`,
`Φ(Π) = Π + (Π − Π*)²`, which touches the line only at `Π*`. -/
def tangentRule (Pis : ℝ) (x : ℝ) : ℝ := x + (x - Pis) ^ 2

/-- Cochrane (2023), §16.10.5, p. 392: touching the 45° line only at `Π*` is not enough. The
tangent rule has `Π*` as its only steady state and respects the bound `Φ ≥ Π* − 1/4`, but every
path starting in `(Π* − 1, Π*)` is a bounded, nonconstant path converging to `Π*`: a continuum
of bounded equilibria. The V-shaped rules work because they jump *over* `Π*`. -/
theorem tangent_rule_converges {Pis : ℝ} {infl : ℕ → ℝ}
    (hpath : ∀ t, infl (t + 1) = tangentRule Pis (infl t)) (h0 : infl 0 ∈ Set.Ioo (Pis - 1) Pis) :
    (∀ x, tangentRule Pis x = x ↔ x = Pis) ∧ (∀ x, Pis - 1 / 4 ≤ tangentRule Pis x) ∧
      (∀ t, infl 0 ≤ infl t ∧ infl t < Pis) ∧ Tendsto infl atTop (𝓝 Pis) := by
  have hstep : ∀ x ∈ Set.Ioo (Pis - 1) Pis, x < tangentRule Pis x ∧ tangentRule Pis x < Pis :=
    fun x hx => by
      simp only [tangentRule]
      constructor
      · nlinarith [hx.2]
      · nlinarith [hx.1, hx.2]
  have hmem : ∀ t, infl t ∈ Set.Ioo (Pis - 1) Pis ∧ infl 0 ≤ infl t := by
    intro t
    induction t with
    | zero => exact ⟨h0, le_rfl⟩
    | succ n ih =>
      rw [hpath]
      have := hstep _ ih.1
      exact ⟨⟨by linarith [ih.1.1], this.2⟩, by linarith [ih.2]⟩
  refine ⟨fun x => ⟨fun h => ?_, fun h => by simp [tangentRule, h]⟩, fun x => ?_,
    fun t => ⟨(hmem t).2, (hmem t).1.2⟩, ?_⟩
  · simp only [tangentRule, add_eq_left] at h
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h
    linarith
  · simp only [tangentRule]; nlinarith [sq_nonneg (x - Pis + 1 / 2)]
  · have hmono : Monotone infl := monotone_nat_of_le_succ fun t => by
      rw [hpath]; exact (hstep _ (hmem t).1).1.le
    rcases monotone_orbit_atTop_or_fixed hpath hmono with htop | ⟨L, hL, hLb, hfix⟩
    · exfalso
      obtain ⟨t, ht⟩ := (htop.eventually (eventually_gt_atTop Pis)).exists
      linarith [(hmem t).1.2]
    · have hLP : L ≤ Pis := le_of_tendsto' hL fun t => (hmem t).1.2.le
      have hc : ContinuousAt (tangentRule Pis) L := by unfold tangentRule; fun_prop
      have hfx := hfix hc
      simp only [tangentRule, add_eq_left] at hfx
      have : L = Pis := by
        have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hfx
        linarith
      rw [this] at hL
      exact hL

/-! ## §16.10.6 Residual money demand: Sims (1994) -/

/-- Cochrane (2023), §16.10.6, pp. 393–394, Sims (1994): "perhaps there is a lower limit on
nominal money demand … then real money demand explodes in a deflation violating the
transversality condition". Precisely: if nominal money stays above `M̲ > 0`, prices follow
`P_{t+1} = Π_{t+1}P_t` with `Π_{t+1} ≥ β` (the zero bound), and the deflation approaches `β` fast
enough that `Σ (Π_{t+1} − β) < ∞`, then the discounted real money `βᵀM_T/P_T` does not tend to
zero: the transversality condition fails. -/
theorem sims_tvc_violated {β Mlow : ℝ} {infl P M : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hge : ∀ t, β ≤ infl (t + 1))
    (hsum : Summable fun t => infl (t + 1) - β) (hMlow : 0 < Mlow) (hM : ∀ t, Mlow ≤ M t) :
    ¬ Tendsto (fun T => β ^ T * M T / P T) atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun k => (infl (k + 1) - β) / β with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => div_nonneg (by linarith [hge k]) hβ.le
  have hasum : Summable a := hsum.div_const β
  set S := ∑' k, a k with hS
  have hinfl : ∀ t, 0 < infl (t + 1) := fun t => lt_of_lt_of_le hβ (hge t)
  have hP : ∀ t, 0 < P t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ n ih => rw [hPrec]; exact mul_pos (hinfl n) ih
  set q : ℕ → ℝ := fun T => β ^ T / P T with hq
  have hqstep : ∀ T, q (T + 1) = q T * (β / infl (T + 1)) := fun T => by
    simp only [hq, hPrec, pow_succ]
    have := hP T
    have := hinfl T
    field_simp
  -- `β/Π ≥ exp(−(Π/β − 1))`
  have hratio : ∀ T, Real.exp (-a T) ≤ β / infl (T + 1) := fun T => by
    have h1 : infl (T + 1) / β ≤ Real.exp (a T) := by
      have := Real.add_one_le_exp (a T)
      simp only [ha] at this ⊢
      have e : (infl (T + 1) - β) / β + 1 = infl (T + 1) / β := by field_simp; ring
      linarith
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (hinfl T)]
    rw [div_le_iff₀ hβ] at h1
    linarith
  have hqlow : ∀ T, q 0 * Real.exp (-∑ k ∈ Finset.range T, a k) ≤ q T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [hqstep, Finset.sum_range_succ, neg_add, Real.exp_add, ← mul_assoc]
      have hq0 : 0 ≤ q n := le_trans (by
        have : 0 < q 0 := by simp only [hq]; exact div_pos (pow_pos hβ 0) hP0
        positivity) ih
      exact mul_le_mul ih (hratio n) (Real.exp_pos _).le hq0
  have hq0 : 0 < q 0 := by simp only [hq]; exact div_pos (pow_pos hβ 0) hP0
  have hbound : ∀ T, q 0 * Real.exp (-S) ≤ q T := fun T => by
    refine le_trans ?_ (hqlow T)
    apply mul_le_mul_of_nonneg_left _ hq0.le
    apply Real.exp_le_exp.mpr
    have := hasum.sum_le_tsum (Finset.range T) (fun k _ => ha0 k)
    linarith
  have hc : 0 < Mlow * (q 0 * Real.exp (-S)) := by positivity
  intro hlim
  have hev : ∀ᶠ T in atTop, Mlow * (q 0 * Real.exp (-S)) ≤ β ^ T * M T / P T :=
    Eventually.of_forall fun T => by
      have h1 := hbound T
      have h2 : β ^ T * M T / P T = M T * q T := by simp only [hq]; ring
      rw [h2]
      exact mul_le_mul (hM T) h1 (by positivity) (by linarith [hM T])
  have := ge_of_tendsto hlim hev
  linarith

/-- Cochrane (2023), §16.10.6, p. 394: in particular, when the deflation reaches the zero bound
in finite time (`Π_t = β` from some date on, as with the truncated rule
`LowerBound.truncRule_hits_bound`), Sims's argument applies. -/
theorem sims_tvc_violated_of_eventually_beta {β Mlow : ℝ} {infl P M : ℕ → ℝ} (hβ : 0 < β)
    (hP0 : 0 < P 0) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hge : ∀ t, β ≤ infl (t + 1))
    {T0 : ℕ} (hT0 : ∀ t, T0 ≤ t → infl (t + 1) = β) (hMlow : 0 < Mlow) (hM : ∀ t, Mlow ≤ M t) :
    ¬ Tendsto (fun T => β ^ T * M T / P T) atTop (𝓝 0) := by
  refine sims_tvc_violated hβ hP0 hPrec hge ?_ hMlow hM
  refine summable_of_ne_finset_zero (s := Finset.range T0) fun t ht => ?_
  rw [Finset.mem_range, not_lt] at ht
  rw [hT0 t ht, sub_self]

/-- Cochrane (2023), §16.10.6, p. 394, imprecision: the penny in the sock drawer does not bite
when the deflation converges to a steady state `Π_L > β` (the zero bound not reached): with
constant money `M̲`, the discounted real money `βᵀM̲/P_T` tends to zero, so the transversality
condition holds. -/
theorem sims_no_bite_above_beta {β Mlow PL : ℝ} {infl P : ℕ → ℝ} (hβ : 0 < β) (hPL : β < PL)
    (hP0 : 0 < P 0) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hpos : ∀ t, 0 < infl t)
    (hlim : Tendsto infl atTop (𝓝 PL)) :
    Tendsto (fun T => β ^ T * Mlow / P T) atTop (𝓝 0) := by
  have hP : ∀ t, 0 < P t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ n ih => rw [hPrec]; exact mul_pos (hpos _) ih
  set c := (β + PL) / 2 with hc
  have hβc : β < c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds (by linarith : c < PL)))
  set q : ℕ → ℝ := fun T => β ^ T / P T with hq
  have hqpos : ∀ T, 0 < q T := fun T => div_pos (pow_pos hβ T) (hP T)
  have hqstep : ∀ T, q (T + 1) = q T * (β / infl (T + 1)) := fun T => by
    simp only [hq, hPrec, pow_succ]
    have := hP T
    have := hpos (T + 1)
    field_simp
  have hdecay : ∀ n, q (T0 + n) ≤ q T0 * (β / c) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, hqstep, pow_succ, ← mul_assoc]
      have h1 : β / infl (T0 + n + 1) ≤ β / c :=
        div_le_div_of_nonneg_left hβ.le hc0 (hT0 _ (by omega)).le
      exact mul_le_mul ih h1 (div_pos hβ (hpos _)).le (by have := hqpos T0; positivity)
  have hr0 : 0 ≤ β / c := (div_pos hβ hc0).le
  have hr1 : β / c < 1 := (div_lt_one hc0).mpr hβc
  have hlim0 : Tendsto (fun T => q T0 * (β / c) ^ (T - T0)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (tendsto_sub_atTop_nat T0)).const_mul (q T0)
    simpa using this
  have hq0 : Tendsto q atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun T => (hqpos T).le) ?_ hlim0
    filter_upwards [eventually_ge_atTop T0] with T hT
    have := hdecay (T - T0)
    rwa [Nat.add_sub_cancel' hT] at this
  have : (fun T => β ^ T * Mlow / P T) = fun T => Mlow * q T := by
    funext T; simp only [hq]; ring
  rw [this]
  simpa using hq0.const_mul Mlow

/-- Cochrane (2023), §16.10.6, p. 394, imprecision: summability cannot be dropped from
`sims_tvc_violated`. With `Π_{t+1} = β(t + 2)/(t + 1) ≥ β`, converging to the zero-bound rate
`β`, and `P_T = βᵀ(T + 1)`, constant money `M̲` gives `βᵀM̲/P_T = M̲/(T + 1) → 0`: a deflation
converging slowly to the zero bound satisfies the transversality condition despite the
penny. -/
theorem sims_slow_counterexample {β Mlow : ℝ} (hβ : 0 < β) :
    let infl : ℕ → ℝ := fun t => β * ((t : ℝ) + 1) / t
    let P : ℕ → ℝ := fun T => β ^ T * ((T : ℝ) + 1)
    (∀ t, P (t + 1) = infl (t + 1) * P t) ∧ (∀ t, β ≤ infl (t + 1)) ∧
      Tendsto infl atTop (𝓝 β) ∧ Tendsto (fun T => β ^ T * Mlow / P T) atTop (𝓝 0) := by
  intro infl P
  refine ⟨fun t => ?_, fun t => ?_, ?_, ?_⟩
  · simp only [infl, P]
    push_cast
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · simp only [infl]
    push_cast
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have h1 : Tendsto (fun t : ℕ => β * (1 + 1 / (t : ℝ))) atTop (𝓝 (β * (1 + 0))) :=
      (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).const_mul β
    rw [add_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp only [infl]
    have : (t : ℝ) ≠ 0 := by positivity
    field_simp
  · have h1 : Tendsto (fun T : ℕ => Mlow * (1 / ((T : ℝ) + 1))) atTop (𝓝 (Mlow * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul Mlow
    rw [mul_zero] at h1
    refine h1.congr fun T => ?_
    simp only [P]
    have : β ^ T ≠ 0 := (pow_pos hβ T).ne'
    field_simp

/-! ## Online Appendix A3, §3.1.1–3.1.2: helicopter money versus open-market operations -/

/-- Cochrane (2023), Online Appendix A3, eq. (3.1) and p. 614: with no debt, budget
`(M_t − M_{t−1})/P_t = −s_t` and `P_{t+1} = βP_t` (`i = 0`), the present-value relation
"final money equals initial money plus added money" holds:
`M_{t−1}/P_t = Σ_{j<T} βʲ s_{t+j} + βᵀM_{t+T−1}/P_{t+T}`, and the last term equals
`M_{t+T−1}/P_t`. Here `M t` is money held into period `t` (the book's `M_{t−1}`). -/
theorem a3_helicopter_pv {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, (M (t + 1) - M t) / P t = -s t) (hdefl : ∀ t, P (t + 1) = β * P t) (t T : ℕ) :
    M t / P t = ∑ j ∈ Finset.range T, β ^ j * s (t + j) + β ^ T * (M (t + T) / P (t + T)) ∧
      β ^ T * (M (t + T) / P (t + T)) = M (t + T) / P t := by
  have hPT : ∀ n, P (t + n) = β ^ n * P t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [← add_assoc, hdefl, ih, pow_succ]; ring
  have hflow : ∀ u, M (u + 1) / P (u + 1) = (1 + (β⁻¹ - 1)) * (M u / P u - s u) := fun u => by
    have h := hbud u
    have := hP u
    rw [hdefl]
    field_simp at h ⊢
    linarith
  have hr : 0 < 1 + (β⁻¹ - 1) := by simp [hβ]
  have hpv := Hyperinflation.pv_partial (b := fun u => M u / P u) hr hflow t T
  simp only [add_sub_cancel, inv_inv] at hpv
  refine ⟨hpv, ?_⟩
  rw [hPT T]
  have := hP t
  have := pow_pos hβ T
  field_simp

/-- Cochrane (2023), Online Appendix A3, p. 614, "the final term grows at rate `(1+µ)ᵀ`. The
final, transversality condition is violated": with perpetual money growth `M_{t+1} = (1 + µ)M_t`,
`µ > 0`, `M_0 > 0`, and `P_{t+1} = βP_t`, the discounted real money `βᵀM_T/P_T` diverges. -/
theorem a3_helicopter_tvc_violated {β μ : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hP0 : 0 < P 0) (hM0 : 0 < M 0) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t)
    (hdefl : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ T * (M T / P T)) atTop atTop := by
  have hPT : ∀ n, P n = β ^ n * P 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hdefl, ih, pow_succ]; ring
  have hMT : ∀ n, M n = (1 + μ) ^ n * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hgrow, ih, pow_succ]; ring
  have : (fun T => β ^ T * (M T / P T)) = fun T => (1 + μ) ^ T * (M 0 / P 0) := by
    funext T
    rw [hPT, hMT]
    have := pow_pos hβ T
    field_simp
  rw [this]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).atTop_mul_const (div_pos hM0 hP0)

/-- Cochrane (2023), Online Appendix A3, §3.1.2, p. 615: with debt and open-market operations,
total liabilities `W_t = B_{t−1} + M_{t−1}` satisfy `W_t/P_t = W_{t+1}/P_t + s_t`; the surplus
`s_t = (1 − β)W_t/P_t` with `P_{t+1} = βP_t` gives constant real total debt
`W_{t+1}/P_{t+1} = W_t/P_t` and nominal total debt `W_{t+1} = βW_t`. -/
theorem a3_omo_real_const {β : ℝ} {W P s : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, W t / P t = W (t + 1) / P t + s t) (hs : ∀ t, s t = (1 - β) * (W t / P t))
    (hdefl : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    W (t + 1) / P (t + 1) = W t / P t ∧ W (t + 1) = β * W t := by
  have h := hbud t
  rw [hs] at h
  have := hP t
  have hW : W (t + 1) = β * W t := by
    field_simp at h
    linarith
  refine ⟨?_, hW⟩
  rw [hW, hdefl]
  field_simp

/-- Cochrane (2023), Online Appendix A3, p. 616: under the OMO policy, `B_t + M_t = βᵗ(B_0 + M_0)`
and, with money growing at `1 + µ`, `B_t = βᵗ(B_0 + M_0) − (1 + µ)ᵗM_0`. -/
theorem a3_omo_nominal {β μ : ℝ} {B M W : ℕ → ℝ} (hW : ∀ t, W t = B t + M t)
    (hWstep : ∀ t, W (t + 1) = β * W t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ) :
    W t = β ^ t * (B 0 + M 0) ∧ B t = β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 := by
  have hWt : ∀ n, W n = β ^ n * (B 0 + M 0) := by
    intro n
    induction n with
    | zero => simp [hW]
    | succ n ih => rw [hWstep, ih, pow_succ]; ring
  have hMt : ∀ n, M n = (1 + μ) ^ n * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hgrow, ih, pow_succ]; ring
  refine ⟨hWt t, ?_⟩
  have := hW t
  rw [hWt t, hMt t] at this
  linarith

/-- Cochrane (2023), Online Appendix A3, p. 616, "the second term grows without bound, so
government debt becomes negative": with `0 < β < 1`, `µ ≥ 0` and `M_0 > 0`, eventually
`B_t < 0`. -/
theorem a3_omo_debt_negative {β μ B0 M0 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hμ : 0 ≤ μ)
    (hM0 : 0 < M0) :
    ∀ᶠ t in atTop, β ^ t * (B0 + M0) - (1 + μ) ^ t * M0 < 0 := by
  have h1 : Tendsto (fun t : ℕ => β ^ t * (B0 + M0)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (B0 + M0)
  filter_upwards [h1.eventually (gt_mem_nhds hM0)] with t ht
  have : M0 ≤ (1 + μ) ^ t * M0 := le_mul_of_one_le_left hM0.le (one_le_pow₀ (by linarith))
  linarith

/-- Cochrane (2023), Online Appendix A3, p. 615, "despite ever increasing money, the total value
of government debt is the same, and the transversality condition holds": under the OMO policy
the discounted real total debt `βᵀW_T/P_T = βᵀW_0/P_0` tends to zero. -/
theorem a3_omo_tvc {β : ℝ} {W P s : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, W t / P t = W (t + 1) / P t + s t) (hs : ∀ t, s t = (1 - β) * (W t / P t))
    (hdefl : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ T * (W T / P T)) atTop (𝓝 0) := by
  have hconst : ∀ T, W T / P T = W 0 / P 0 := by
    intro T
    induction T with
    | zero => rfl
    | succ n ih => rw [(a3_omo_real_const hβ hP hbud hs hdefl n).1, ih]
  simp only [hconst]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (W 0 / P 0)

end Cochrane.NewKeynesianSelection.SelectionPatches

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tiny bit of fiscal theory (Sims 2013)

Cochrane (2023), Chapter 16, §16.10.8, pp. 395–396. The simple environment `i_t = E_tπ_{t+1}`,
`i_t = φπ_t` under perfect foresight, so `π_t = φᵗπ₀`; real debt `b_t` with the surplus rule
(16.33) `s_t = γb_t + θπ_t` and accumulation (16.34) `b_{t+1} = Rb_t − s_t`.

## Main results

* `infl_path`: `π_t = φᵗπ₀`; `eq1634`: `b_{t+1} = (R − γ)b_t − θφᵗπ₀`.
* The closed form: `closed_form` (`φ ≠ R − γ`), `closed_form_book` (the printed form, `φ ≠ 0`),
  `closed_form_eq` (`φ = R − γ`).
* `debt_explodes`: for `|R − γ| < 1 < φ` and `θπ₀ ≠ 0`, `|b_t| → ∞` (as printed).
* Error E1: `tvc_iff` (`R^{−t}b_t → 0` iff `θπ₀ = 0` or `φ < R`), `e1_tvc_violated_iff`
  (TVC fails for every `π₀ ≠ 0` iff `φ ≥ R`), `e1_counterexample` (`φ = 1.02`, `R = 1.05`: debt
  explodes but the TVC holds), `active_iff` (determinacy `π₀ = 0` exactly when `φ ≥ R`).
* (16.26)-type valuation: `valuation_iff_tvc`, `valuation_fails`.
* Stationarity: `stationary_iff` (`(R − γ)ᵗb₀ → 0` for all `b₀` iff `R − 1 < γ < R + 1`),
  `stationary_counterexample` (`γ > R − 1` alone is not enough); `passive_of_bounded` (with a
  bounded external surplus component, debt is bounded and the TVC holds for every initial
  value: passive policy).
* `selected_path_indep_theta`: on the selected path `π ≡ 0`, the surplus is `γb_t` whatever `θ`
  ("its presence would have no effect … except for its elimination of the unstable solutions").
-/

namespace Cochrane.NewKeynesianSelection.SimsTinyFiscal

open Filter Topology
open Cochrane.NewKeynesianSelection.LowerBound

/-- Cochrane (2023), §16.10.8, p. 395: in the simple environment `i_t = E_tπ_{t+1}`,
`i_t = φπ_t` under perfect foresight, `π_{t+1} = φπ_t`, so `π_t = φᵗπ₀`. -/
theorem infl_path {φ : ℝ} {infl i : ℕ → ℝ} (hfis : ∀ t, i t = infl (t + 1))
    (hrule : ∀ t, i t = φ * infl t) (t : ℕ) : infl t = φ ^ t * infl 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [← hfis, hrule, ih, pow_succ]; ring

/-- Cochrane (2023), eqs. (16.33)–(16.34), p. 395: with `s_t = γb_t + θπ_t`,
`b_{t+1} = Rb_t − s_t` and `π_t = φᵗπ₀`, debt follows `b_{t+1} = (R − γ)b_t − θφᵗπ₀`. -/
theorem eq1634 {R γ θ φ π0 : ℝ} {b s infl : ℕ → ℝ} (hs : ∀ t, s t = γ * b t + θ * infl t)
    (hb : ∀ t, b (t + 1) = R * b t - s t) (hπ : ∀ t, infl t = φ ^ t * π0) (t : ℕ) :
    b (t + 1) = (R - γ) * b t - θ * (φ ^ t * π0) := by
  rw [hb, hs, hπ]; ring

/-- Cochrane (2023), p. 396, the solution of (16.34) for `φ ≠ R − γ`:
`b_t = (R − γ)ᵗb₀ − θπ₀(φᵗ − (R − γ)ᵗ)/(φ − (R − γ))`. -/
theorem closed_form {a θ φ π0 : ℝ} {b : ℕ → ℝ} (hφa : φ ≠ a)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * π0 * ((φ ^ t - a ^ t) / (φ - a)) := by
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb, ih]
    field_simp
    ring

/-- Cochrane (2023), p. 396, the printed form of the solution:
`b_t = (R − γ)ᵗb₀ − θ [1 − (R − γ)ᵗφ^{−t}]/[1 − (R − γ)φ^{−1}] φ^{t−1}π₀` (for `φ ≠ 0`,
`φ ≠ R − γ`; at `t = 0` read `φ^{−1}·(1 − 1) = 0`). -/
theorem closed_form_book {a θ φ π0 : ℝ} {b : ℕ → ℝ} (hφ : φ ≠ 0) (hφa : φ ≠ a)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * ((1 - a ^ t * (φ ^ t)⁻¹) / (1 - a * φ⁻¹)) * (φ ^ t * φ⁻¹) * π0 := by
  rw [closed_form hφa hb t]
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  have hne' : 1 - a * φ⁻¹ ≠ 0 := by
    rw [show 1 - a * φ⁻¹ = (φ - a) / φ by field_simp]
    exact div_ne_zero hne hφ
  have hpt : φ ^ t ≠ 0 := pow_ne_zero t hφ
  rw [show 1 - a * φ⁻¹ = (φ - a) / φ by field_simp]
  field_simp

/-- Cochrane (2023), p. 396, the borderline case `φ = R − γ`: `b_t = aᵗb₀ − θπ₀ t a^{t−1}`
(written `t·a^{t−1}` as `t * a^(t-1)` with natural subtraction). -/
theorem closed_form_eq {a θ π0 : ℝ} {b : ℕ → ℝ}
    (hb : ∀ t, b (t + 1) = a * b t - θ * (a ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * π0 * (t * a ^ (t - 1)) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb, ih]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- Cochrane (2023), p. 396, "for any `π₀ ≠ 0`, debt explodes": with `|R − γ| < 1 < φ` and
`θπ₀ ≠ 0`, `|b_t| → ∞`. -/
theorem debt_explodes {a θ φ π0 : ℝ} {b : ℕ → ℝ} (ha : |a| < 1) (hφ : 1 < φ) (hθπ : θ * π0 ≠ 0)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) :
    Tendsto (fun t => |b t|) atTop atTop := by
  have hφa : φ ≠ a := by
    intro h; rw [h] at hφ; linarith [le_abs_self a]
  have hpos : 0 < φ - a := by linarith [le_abs_self a]
  set c := θ * π0 / (φ - a) with hc
  have hc0 : 0 < |c| := abs_pos.mpr (div_ne_zero hθπ hpos.ne')
  have hlow : ∀ t, |c| * φ ^ t - (|b 0| + |c|) ≤ |b t| := by
    intro t
    have hform := closed_form hφa hb t
    have hat : |a ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha.le
    have e : b t = a ^ t * b 0 + c * a ^ t - c * φ ^ t := by rw [hform, hc]; field_simp; ring
    have h1 : |c * φ ^ t| ≤ |b t| + |a ^ t * b 0| + |c * a ^ t| := by
      have : c * φ ^ t = a ^ t * b 0 + c * a ^ t - b t := by linarith
      rw [this]
      calc |a ^ t * b 0 + c * a ^ t - b t| ≤ |a ^ t * b 0 + c * a ^ t| + |b t| := abs_sub _ _
        _ ≤ |a ^ t * b 0| + |c * a ^ t| + |b t| := by gcongr; exact abs_add_le _ _
        _ = |b t| + |a ^ t * b 0| + |c * a ^ t| := by ring
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < φ) t)] at h1
    have h2 : |a ^ t| * |b 0| ≤ |b 0| := by nlinarith [abs_nonneg (b 0)]
    have h3 : |c| * |a ^ t| ≤ |c| := by nlinarith [abs_nonneg c]
    linarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hφ).const_mul_atTop hc0)

/-- Cochrane (2023), p. 396, error E1: the transversality condition `R^{−t}b_t → 0` holds if and
only if `θπ₀ = 0` or `φ < R` (for `R > 0`, `|R − γ| < R`, `φ > 0`, `φ ≠ R − γ`). -/
theorem tvc_iff {R a θ φ π0 : ℝ} {b : ℕ → ℝ} (hR : 0 < R) (ha : |a| < R) (hφ : 0 < φ)
    (hφa : φ ≠ a) (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) :
    Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) ↔ θ * π0 = 0 ∨ φ < R := by
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  set c := θ * π0 / (φ - a) with hc
  have hform : ∀ t, R⁻¹ ^ t * b t = (a / R) ^ t * (b 0 + c) - c * (φ / R) ^ t := fun t => by
    rw [closed_form hφa hb t, hc, div_pow, div_pow, inv_pow]
    have : R ^ t ≠ 0 := pow_ne_zero t hR.ne'
    field_simp
    ring
  have haR : |a / R| < 1 := by rw [abs_div, abs_of_pos hR, div_lt_one hR]; exact ha
  have hA : Tendsto (fun t => (a / R) ^ t * (b 0 + c)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one haR).mul_const (b 0 + c)
  simp only [hform]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hθπ, hφR⟩ := hcon
    have hc0 : c ≠ 0 := div_ne_zero hθπ hne
    have h2 : Tendsto (fun t => c * (φ / R) ^ t) atTop (𝓝 0) := by
      have := hA.sub h
      simpa using this
    have h3 : Tendsto (fun t => (φ / R) ^ t) atTop (𝓝 0) := by
      have := h2.const_mul c⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hc0] using this
    have hge : ∀ t : ℕ, 1 ≤ (φ / R) ^ t := fun t => one_le_pow₀ ((one_le_div hR).mpr hφR)
    have := ge_of_tendsto' h3 hge
    linarith
  · rintro (h | h)
    · have hc0 : c = 0 := by rw [hc, h, zero_div]
      simpa [hc0] using hA
    · have h1 : Tendsto (fun t => (φ / R) ^ t) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hφ hR).le ((div_lt_one hR).mpr h)
      simpa using hA.sub (h1.const_mul c)

/-- Cochrane (2023), p. 396, error E1 (corrected statement): with `|R − γ| < 1 < R`, `φ > 1` and
`θ ≠ 0`, "for any `π₀ ≠ 0` debt … violat[es] the transversality condition" holds if and only if
`φ ≥ R`. For `1 < φ < R` every `π₀` satisfies the transversality condition and fiscal policy stays
passive. -/
theorem e1_tvc_violated_iff {R a θ φ : ℝ} (hR : 1 < R) (ha : |a| < 1) (hφ : 1 < φ)
    (hθ : θ ≠ 0) :
    (∀ π0 : ℝ, π0 ≠ 0 → ∀ b : ℕ → ℝ, (∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) →
      ¬ Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0)) ↔ R ≤ φ := by
  have hφa : φ ≠ a := by intro h; rw [h] at hφ; linarith [le_abs_self a]
  have haR : |a| < R := by linarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- the path from `π₀ = 1`, `b₀ = 0`
    set b : ℕ → ℝ := fun t => -θ * ((φ ^ t - a ^ t) / (φ - a)) with hbdef
    have hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * 1) := fun t => by
      have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
      simp only [hbdef]
      field_simp
      ring
    exact h 1 one_ne_zero b hb ((tvc_iff (by linarith) haR (by linarith) hφa hb).mpr
      (Or.inr hlt))
  · intro hRφ π0 hπ0 b hb htvc
    rcases (tvc_iff (by linarith) haR (by linarith) hφa hb).mp htvc with h | h
    · exact mul_ne_zero hθ hπ0 h
    · linarith

/-- Cochrane (2023), p. 396, error E1 counterexample: `R = 1.05`, `γ = 0.5` (so `R − γ = 0.55`),
`φ = 1.02`, `θ = 1`, `π₀ = 1`, `b₀ = 0`. Debt explodes, yet `R^{−t}b_t → 0`: the transversality
condition holds and the inflationary path is not ruled out. -/
theorem e1_counterexample :
    let b : ℕ → ℝ := fun t => -((102 / 100) ^ t - (55 / 100) ^ t) / (102 / 100 - 55 / 100)
    (∀ t, b (t + 1) = 55 / 100 * b t - 1 * ((102 / 100) ^ t * 1)) ∧
      Tendsto (fun t => |b t|) atTop atTop ∧
      Tendsto (fun t => (105 / 100 : ℝ)⁻¹ ^ t * b t) atTop (𝓝 0) := by
  intro b
  have hb : ∀ t, b (t + 1) = 55 / 100 * b t - 1 * ((102 / 100) ^ t * 1) := fun t => by
    simp only [b, pow_succ]
    ring
  refine ⟨hb, debt_explodes (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) hb, ?_⟩
  exact (tvc_iff (by norm_num) (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) hb).mpr
    (Or.inr (by norm_num))

/-- Cochrane (2023), p. 396, "we now have a real reason to rule out the nominally explosive
equilibria": with `|R − γ| < 1 < R`, `φ > 1`, `θ ≠ 0`, the transversality condition selects
`π₀ = 0` (fiscal policy active, a unique equilibrium) if and only if `φ ≥ R`. -/
theorem active_iff {R a θ φ : ℝ} (hR : 1 < R) (ha : |a| < 1) (hφ : 1 < φ) (hθ : θ ≠ 0)
    (b0 : ℝ) :
    (∀ π0 : ℝ, ∀ b : ℕ → ℝ, b 0 = b0 → (∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) →
      Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) → π0 = 0) ↔ R ≤ φ := by
  have hφa : φ ≠ a := by intro h; rw [h] at hφ; linarith [le_abs_self a]
  have haR : |a| < R := by linarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set b : ℕ → ℝ := fun t => a ^ t * b0 - θ * ((φ ^ t - a ^ t) / (φ - a)) with hbdef
    have hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * 1) := fun t => by
      have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
      simp only [hbdef]
      field_simp
      ring
    have := h 1 b (by simp [hbdef]) hb ((tvc_iff (by linarith) haR (by linarith) hφa hb).mpr
      (Or.inr hlt))
    exact one_ne_zero this
  · intro hRφ π0 b _ hb htvc
    by_contra hπ0
    exact (e1_tvc_violated_iff hR ha hφ hθ).mpr hRφ π0 hπ0 b hb htvc

/-- Cochrane (2023), p. 395, the valuation equation behind the transversality condition: with
`b_{t+1} = Rb_t − s_t`, `R > 0`, and absolutely summable discounted surpluses,
`b_t = Σ R^{−(j+1)} s_{t+j}` holds iff `R^{−T}b_{t+T} → 0`. -/
theorem valuation_iff_tvc {R : ℝ} {b s : ℕ → ℝ} (hR : 0 < R)
    (hb : ∀ t, b (t + 1) = R * b t - s t) (t : ℕ)
    (hsum : Summable fun j => R⁻¹ ^ (j + 1) * s (t + j)) :
    HasSum (fun j => R⁻¹ ^ (j + 1) * s (t + j)) (b t) ↔
      Tendsto (fun T => R⁻¹ ^ T * b (t + T)) atTop (𝓝 0) := by
  have hR1 : 0 < 1 + (R - 1) := by linarith
  have hflow : ∀ u, b (u + 1) = (1 + (R - 1)) * (b u - s u / R) := fun u => by
    rw [hb]; field_simp; ring
  have heq : (fun j => R⁻¹ ^ (j + 1) * s (t + j)) =
      fun j => (1 + (R - 1))⁻¹ ^ j * (s (t + j) / R) := by
    funext j; rw [pow_succ]; field_simp; ring
  rw [heq] at hsum ⊢
  have := LowerBound.valuation_iff_tvc (b := b) (s := fun u => s u / R) hR1 hflow t hsum
  simpa using this

/-- Cochrane (2023), p. 396: when the transversality condition fails, the valuation equation
`b₀ = Σ R^{−(j+1)}s_j` cannot hold (as a genuine sum). -/
theorem valuation_fails {R : ℝ} {b s : ℕ → ℝ} (hR : 0 < R) (hb : ∀ t, b (t + 1) = R * b t - s t)
    (htvc : ¬ Tendsto (fun T => R⁻¹ ^ T * b T) atTop (𝓝 0)) :
    ¬ HasSum (fun j => R⁻¹ ^ (j + 1) * s j) (b 0) := by
  intro h
  have hsum : Summable fun j => R⁻¹ ^ (j + 1) * s (0 + j) := by simpa using h.summable
  have := (valuation_iff_tvc hR hb 0 hsum).mp (by simpa using h)
  exact htvc (by simpa using this)

/-- Cochrane (2023), p. 395, "specialize to `γ > R − 1` so debt is stationary", corrected: with
no inflation term, `b_t = (R − γ)ᵗb₀` converges to zero for every `b₀` iff `|R − γ| < 1`, i.e.
`R − 1 < γ < R + 1`. -/
theorem stationary_iff {R γ : ℝ} :
    (∀ b0 : ℝ, Tendsto (fun t : ℕ => (R - γ) ^ t * b0) atTop (𝓝 0)) ↔
      R - 1 < γ ∧ γ < R + 1 := by
  have habs : |R - γ| < 1 ↔ R - 1 < γ ∧ γ < R + 1 := by
    rw [abs_lt]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← habs]
  constructor
  · intro h
    have h1 := h 1
    simp only [mul_one] at h1
    by_contra hcon
    push Not at hcon
    have hge : ∀ t : ℕ, 1 ≤ |(R - γ) ^ t| := fun t => by
      rw [abs_pow]; exact one_le_pow₀ hcon
    have h2 := h1.abs
    rw [abs_zero] at h2
    have := ge_of_tendsto' h2 hge
    linarith
  · intro h b0
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const b0

/-- Cochrane (2023), p. 395, error E1 (second part): `γ > R − 1` alone does not make debt
stationary. With `R = 1.05` and `γ = 3.05 > R − 1`, `R − γ = −2` and `b_t = (−2)ᵗ` does not
converge. -/
theorem stationary_counterexample :
    ((105 / 100 : ℝ) - 1 < 305 / 100) ∧
      ¬ Tendsto (fun t : ℕ => ((105 / 100 : ℝ) - 305 / 100) ^ t * 1) atTop (𝓝 0) := by
  refine ⟨by norm_num, fun h => ?_⟩
  have := (stationary_iff (R := 105 / 100) (γ := 305 / 100)).mp (fun b0 => by
    have := h.mul_const b0
    simpa [mul_comm, mul_assoc] using this)
  norm_num at this

/-- Cochrane (2023), p. 396, "the result that `γ > R − 1` leads to passive policy needs a bounded
external component of the surplus": if `b_{t+1} = (R − γ)b_t − x_t` with `|R − γ| < 1` and
`|x_t| ≤ X`, debt is bounded by `|b₀| + X/(1 − |R − γ|)`, and for `R > 1` the transversality
condition `R^{−t}b_t → 0` holds for every initial value: fiscal policy is passive. -/
theorem passive_of_bounded {R a X : ℝ} {b x : ℕ → ℝ} (ha : |a| < 1) (hR : 1 < R)
    (hx : ∀ t, |x t| ≤ X) (hb : ∀ t, b (t + 1) = a * b t - x t) :
    (∀ t, |b t| ≤ |b 0| + X / (1 - |a|)) ∧ Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) := by
  have h1a : 0 < 1 - |a| := by linarith
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hx 0)
  set B := |b 0| + X / (1 - |a|) with hB
  have hbd : ∀ t, |b t| ≤ B := by
    intro t
    induction t with
    | zero => rw [hB]; have : 0 ≤ X / (1 - |a|) := div_nonneg hX h1a.le; linarith
    | succ n ih =>
      rw [hb]
      have hkey : |a| * B + X ≤ B := by
        have : X = (1 - |a|) * (X / (1 - |a|)) := by field_simp
        rw [hB]
        nlinarith [abs_nonneg (b 0), abs_nonneg a, div_nonneg hX h1a.le]
      calc |a * b n - x n| ≤ |a * b n| + |x n| := abs_sub _ _
        _ = |a| * |b n| + |x n| := by rw [abs_mul]
        _ ≤ |a| * B + X := by gcongr; exact hx n
        _ ≤ B := hkey
  refine ⟨hbd, ?_⟩
  have hR0 : 0 ≤ R⁻¹ := (inv_pos.mpr (by linarith)).le
  have hR1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hlim : Tendsto (fun t => R⁻¹ ^ t * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1).mul_const B
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun t => abs_nonneg _) (fun t => ?_) hlim
  change |R⁻¹ ^ t * b t| ≤ R⁻¹ ^ t * B
  rw [abs_mul, abs_pow, abs_of_nonneg hR0]
  exact mul_le_mul_of_nonneg_left (hbd t) (pow_nonneg hR0 t)

/-- Cochrane (2023), p. 396, quoting Sims: "its [`θ`] presence would have no effect on the first
two equations of the system or on the equilibrium time path of prices and interest rates, except
for its elimination of the unstable solutions": on the selected path `π₀ = 0`, inflation is zero,
the surplus is `γb_t` and debt is `(R − γ)ᵗb₀`, whatever `θ`. -/
theorem selected_path_indep_theta {R γ θ φ : ℝ} {b s infl : ℕ → ℝ}
    (hs : ∀ t, s t = γ * b t + θ * infl t) (hb : ∀ t, b (t + 1) = R * b t - s t)
    (hπ : ∀ t, infl t = φ ^ t * 0) :
    (∀ t, infl t = 0) ∧ (∀ t, s t = γ * b t) ∧ ∀ t, b t = (R - γ) ^ t * b 0 := by
  have h0 : ∀ t, infl t = 0 := fun t => by rw [hπ, mul_zero]
  have hs' : ∀ t, s t = γ * b t := fun t => by rw [hs, h0, mul_zero, add_zero]
  refine ⟨h0, hs', fun t => ?_⟩
  induction t with
  | zero => simp
  | succ n ih => rw [hb, hs', ih, pow_succ]; ring

end Cochrane.NewKeynesianSelection.SimsTinyFiscal

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the Chapter 16 modules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, pp. 363–396, with §2.6
(p. 40). The chapter was formalised in three concurrent chains, and several book objects appear
in more than one of them with different (but equivalent) definitions. This module proves the
equivalences and the cross-chain connections. Two statements of Woodford (2003) are restated
here (not imported) to connect Cochrane's claims to them.

## Main results

* The §16.1 model (pp. 363–365): `nkEq_iff_nkModel` (`Identification.NKEq` is
  `SimplestModel.NKModel` plus adaptedness), `selected_iff_eq_fwdSol` (the new-Keynesian
  selection `Identification.Selected` is the forward solution (16.6) `SimplestModel.fwdSol`),
  `ar1_selected_eq_fwdSol` ((16.9) in both forms).
* NI-5 and the fiscal-theory rule equilibrium (pp. 40, 364, 372): `ftplEq_iff_ruleModel`,
  `ftplEq_eq_ruleSol`, `nk3Eq_iff_ruleModel` ((16.1)–(16.3) is the model (2.20)–(2.22) with
  `θ = φ`), `nk_is_ruleModel` (NI-5 in the `FTPLSimple` form); `ruleModel_eq164`,
  `rule_expected_path_of_eq164` (§16.4 and Chapter 12, P6, p. 327).
* NI-4 and the King form (pp. 366–367, 371): `king_disturbance_eq_toU`, `kingEq_iff_kingRule`,
  `king_bounded_eq_of_kingForm`.
* The Wicksellian rule (16.8), p. 365, and Woodford (2003) Ch. 2, eq. (1.36) and
  Proposition 2.3 (pp. 81–82): `WoodfordReduced`, `woodfordReduced_iff_eq164`,
  `wicksellModel_iff_woodford`, `woodford_prop_2_3_linear`, `woodford_determinate_iff`.
* E6 (p. 373) and Woodford (2003) Ch. 4, (4.5) and Proposition 4.11 (pp. 312–314):
  `WoodfordDebt45`, `fiscalBlock_debt45`, `e6_passive_iff_woodford45`, `woodford_ricardian_iff`,
  `passive_of_ricardian`, `passive_not_ricardian`.
* §16.3 and §16.8 (pp. 368, 377–379, (16.30)): `isEquilibrium_hyper` (an equilibrium of the full
  model of §16.8 satisfies the §16.3 fiscal block), `passive_tvc_of_gamma`.
* Transversality conditions: `tvc_pf_iff` (the expectation-system TVC of (16.20)–(16.22) under
  perfect foresight is the §16.3 TVC), `stoch_tvc_obs`.
-/

namespace Cochrane.NewKeynesianSelection.Links

open Filter Topology
open Innovation (innov IsShock)
open SimplestModel (Eq164 ar1Pi)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The §16.1 model and its selected solution -/

/-- Cochrane (2023), (16.1)–(16.2), p. 364: `Identification.NKEq` is `SimplestModel.NKModel`
together with adaptedness of inflation. -/
theorem nkEq_iff_nkModel (φ : ℝ) (u π i : ℕ → Ω → ℝ) :
    Identification.NKEq 𝔼 φ u π i ↔ 𝔼.Adapted π ∧ SimplestModel.NKModel 𝔼 φ u i π :=
  ⟨fun h => ⟨h.1, fun t => ⟨h.2.1 t, h.2.2 t⟩⟩,
    fun h => ⟨h.1, fun t => (h.2 t).1, fun t => (h.2 t).2⟩⟩

/-- Cochrane (2023), (16.6), p. 364: for `|φ| > 1` and a bounded adapted disturbance, the
new-Keynesian selection of the identification chain (`Identification.Selected`: the unique
bounded adapted solution of (16.4)) is exactly the forward solution `SimplestModel.fwdSol`. -/
theorem selected_iff_eq_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Identification.Selected 𝔼 φ u π ↔ π = SimplestModel.fwdSol 𝔼 φ u := by
  obtain ⟨hs, hb, ha, huniq⟩ := SimplestModel.fwdSol_existsUnique 𝔼 hφ hM hu
  constructor
  · intro h
    exact huniq π h.2.2.1 h.1
  · rintro rfl
    exact Identification.selected_of 𝔼 hφ hb ha hs

/-- Cochrane (2023), (16.9), p. 365: the two forms of the AR(1) result agree. For `|φ| > 1`,
`φ ≠ η` and a bounded AR(1) disturbance, the forward solution (16.6) is `π = −u/(φ − η)`, and it
is the selected equilibrium. -/
theorem ar1_selected_eq_fwdSol {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ}
    (h : Identification.AR1 𝔼 η u ε) (hM : ∀ t ω, |u t ω| ≤ M) :
    SimplestModel.fwdSol 𝔼 φ u = ar1Pi φ η u ∧
      Identification.Selected 𝔼 φ u (SimplestModel.fwdSol 𝔼 φ u) := by
  have e := SimplestModel.ar1_solution 𝔼 hφ hφη hM (h.isAR1 𝔼)
  refine ⟨e, ?_⟩
  rw [e]
  exact Identification.ar1_selected 𝔼 hφ hφη h ⟨M, hM⟩

/-! ### NI-5 and the fiscal-theory rule equilibrium -/

/-- Cochrane (2023), (2.20)–(2.22), p. 40: the fiscal-theory equilibrium of the identification
chain (`Identification.FTPLEq`) is the rule model `FTPLSimple.RuleModel` with adapted inflation. -/
theorem ftplEq_iff_ruleModel (θ : ℝ) (u εs π i : ℕ → Ω → ℝ) :
    Identification.FTPLEq 𝔼 θ u εs π i ↔ 𝔼.Adapted π ∧ FTPLSimple.RuleModel 𝔼 θ i u εs π :=
  ⟨fun h => ⟨h.1, fun t => ⟨h.2.1 t, h.2.2.1 t, h.2.2.2 t⟩⟩,
    fun h => ⟨h.1, fun t => (h.2 t).1, fun t => (h.2 t).2.1, fun t => (h.2 t).2.2⟩⟩

/-- Cochrane (2023), (2.25), p. 40: given the fiscal shock, every fiscal-theory equilibrium is the
path `FTPLSimple.ruleSol` from its own date-0 inflation (the solution of
`FTPLSimple.rule_existsUnique`). -/
theorem ftplEq_eq_ruleSol {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 εs) (h : Identification.FTPLEq 𝔼 θ u εs π i) :
    π = FTPLSimple.ruleSol θ u εs (π 0) := by
  obtain ⟨q, -, huniq⟩ := FTPLSimple.rule_existsUnique 𝔼 θ (h.1 0) hu hε
  have h1 := huniq (π, i) ⟨h.1, rfl, ((ftplEq_iff_ruleModel 𝔼 θ u εs π i).mp h).2⟩
  have hs := ObservationalEquivalence.ftpl_exists 𝔼 θ hu hε (h.1 0)
  have h2 := huniq (FTPLSimple.ruleSol θ u εs (π 0),
    Identification.fisherRate 𝔼 (FTPLSimple.ruleSol θ u εs (π 0)))
    ⟨hs.1, rfl, ((ftplEq_iff_ruleModel 𝔼 θ u εs _ _).mp hs).2⟩
  exact congrArg Prod.fst (h1.trans h2.symm)

/-- Cochrane (2023), (16.1)–(16.3), p. 364 ("the same set of equations as the simplest fiscal
theory of monetary policy model"): the full new-Keynesian model `Responses.NK3Eq` is the
fiscal-theory rule model (2.20)–(2.22) with `θ = φ`, for adapted inflation. -/
theorem nk3Eq_iff_ruleModel (φ : ℝ) (u εs π i : ℕ → Ω → ℝ) :
    Responses.NK3Eq 𝔼 φ u εs π i ↔ 𝔼.Adapted π ∧ FTPLSimple.RuleModel 𝔼 φ i u εs π := by
  constructor
  · rintro ⟨h, h3⟩
    exact ⟨h.1, fun t => ⟨h.2.1 t, h3 t, h.2.2 t⟩⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, fun t => (h t).1, fun t => (h t).2.2⟩, fun t => (h t).2.1⟩

/-- Cochrane (2023), p. 372 (NI-5) in the form of §2.6: the selected AR(1) new-Keynesian
equilibrium is the fiscal-theory rule equilibrium `FTPLSimple.RuleModel` with `θ = η`, no
monetary disturbance and fiscal shock `ε_Σs = ε_i/(φ − η)`, and it is the path
`FTPLSimple.ruleSol` (2.25). -/
theorem nk_is_ruleModel (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : Identification.AR1 𝔼 η u ε) :
    FTPLSimple.RuleModel 𝔼 η (Identification.fisherRate 𝔼 (ar1Pi φ η u)) 0
        (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u) ∧
      FTPLSimple.ruleSol η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u 0) = ar1Pi φ η u :=
  ⟨((ftplEq_iff_ruleModel 𝔼 _ _ _ _ _).mp (ObservationalEquivalence.nk_is_ftpl 𝔼 φ h)).2,
    ObservationalEquivalence.nk_eq_ftpl_path 𝔼 φ h⟩

/-- Cochrane (2023), (2.20)–(2.24), p. 40, and (16.4), p. 364: every solution of the
fiscal-theory rule model satisfies (16.4) with `φ = θ`, so the §16.4 results on `E_t π_{t+j}`
(`Hyperinflation.expected_path`, `stable_of_abs_lt_one`, `unstable_of_one_lt_abs`) apply to the
Chapter 12 rule equilibria of `FTPLSimple` (`rule_expected_path`, `rule_stable`,
`rule_determinate_unstable`). -/
theorem ruleModel_eq164 {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} (h : FTPLSimple.RuleModel 𝔼 θ i u ε π) :
    Eq164 𝔼 θ u π :=
  fun t => (h t).1.symm.trans (h t).2.2

/-- Cochrane (2023), p. 327 (Chapter 12, P6) and §16.4, p. 369: the expected-path result of the
fiscal-theory rule model, `E_t π_{t+j} = φʲ π_t`, re-derived from §16.4's
`Hyperinflation.expected_path` through `ruleModel_eq164`. -/
theorem rule_expected_path_of_eq164 {φ : ℝ} {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : FTPLSimple.RuleModel 𝔼 φ i 0 ε π) (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t :=
  Hyperinflation.expected_path 𝔼 hπ (ruleModel_eq164 𝔼 hm) t j

/-! ### NI-4 and the King form -/

/-- Cochrane (2023), (16.13), pp. 366–367: with consistent targets `i*_t = E_t π*_{t+1}`, the
disturbance `u = i* − φπ*` of `Responses.king_iff_nk` is King's translation `KingForm.toU`. -/
theorem king_disturbance_eq_toU (φ : ℝ) {istar pistar : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) :
    (fun t => istar t - φ • pistar t) = KingForm.toU 𝔼 φ pistar := by
  funext t
  rw [KingForm.toU, hc.2 t]

/-- Cochrane (2023), (16.12), p. 366, and (16.19), p. 371: with consistent targets, the
King-form equilibrium of the identification chain (`Identification.KingEq`) is adapted inflation
with the Fisher equation and King's rule `KingForm.KingRule`. -/
theorem kingEq_iff_kingRule (φ : ℝ) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) :
    Identification.KingEq 𝔼 φ istar pistar π i ↔
      𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ KingForm.KingRule 𝔼 φ pistar i π := by
  unfold Identification.KingEq KingForm.KingRule
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  rw [hc.2 t]

/-- Cochrane (2023), (16.14), p. 367, and NI-4 (16.19), p. 371: the identification chain's
`king_bounded_eq` follows from the King-form chain's `KingForm.eq_target_of_bounded`: for
`|φ| > 1` and bounded consistent targets every bounded King-form equilibrium is `π = π*`,
`i = i*`. -/
theorem king_bounded_eq_of_kingForm {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : Identification.KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) :
    π = pistar ∧ i = istar := by
  obtain ⟨-, hf, hk⟩ := (kingEq_iff_kingRule 𝔼 φ hc).mp h
  have hπ : π = pistar := KingForm.eq_target_of_bounded 𝔼 hφ hbs hc.1 hb fun t => by
    rw [map_sub, KingForm.expected_set_by_rate 𝔼 hf hk t]
    abel
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-! ### The Wicksellian rule (16.8) and Woodford's Proposition 2.3 -/

/-- Cochrane (2023), (16.8), p. 365, and Woodford (2003), eq. (1.36), p. 81 (restated from the
Woodford Chapter 2 project): Woodford's reduced price-level equation
`(1 + φ_p) P̂_t = E_t P̂_{t+1} + r̂_t + E_t π*_{t+1} − ν_t` for the log price gap `P̂`. -/
def WoodfordReduced (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + φp) • Ph t = 𝔼.E t (Ph (t + 1)) + r t + 𝔼.E t (pis (t + 1)) - ν t

/-- Cochrane (2023), (16.8) and (16.4), pp. 364–365: Woodford's (1.36) is Cochrane's equation
(16.4) for the price gap, `E_t P̂_{t+1} = (1 + φ_p) P̂_t + u_t`, with the disturbance
`u_t = ν_t − r̂_t − E_t π*_{t+1}`. -/
theorem woodfordReduced_iff_eq164 (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) :
    WoodfordReduced 𝔼 φp r pis ν Ph ↔
      Eq164 𝔼 (1 + φp) (fun t => ν t - r t - 𝔼.E t (pis (t + 1))) Ph := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.8), p. 365: Cochrane's Wicksellian model (constant target `p*`, no
real-rate variation) is Woodford's (1.36) with `r̂ = 0`, `π* = 0`, `ν = u` for the price gap
`p − p*`, together with the rule. -/
theorem wicksellModel_iff_woodford {φp pstar : ℝ} {u i p : ℕ → Ω → ℝ} :
    SimplestModel.WicksellModel 𝔼 φp pstar u i p ↔
      (∀ t, i t = φp • (p t - fun _ => pstar) + u t) ∧
        WoodfordReduced 𝔼 φp 0 0 u (fun t => p t - fun _ => pstar) := by
  rw [SimplestModel.wicksell_iff, woodfordReduced_iff_eq164]
  refine and_congr_right fun _ => ?_
  have e : (fun t => u t - (0 : ℕ → Ω → ℝ) t - 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1))) = u := by
    funext t
    simp
  rw [e]

/-- Woodford (2003), Proposition 2.3 (linear core), pp. 81–82, restated from the Woodford
Chapter 2 project and derived from Cochrane (2023), (16.6), p. 364 (`SimplestModel.fwdSol`): for
`φ_p > 0` and bounded `{r̂, π*, ν}` with `r̂`, `ν` adapted, (1.36) has exactly one bounded
adapted solution. Cochrane's (16.8) is the case `r̂ = π* = 0`. -/
theorem woodford_prop_2_3_linear {φp : ℝ} (hφ : 0 < φp) {r pis ν : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hpb : BoundedProc pis) (hνb : BoundedProc ν) (hra : 𝔼.Adapted r)
    (hνa : 𝔼.Adapted ν) :
    ∃! Ph, BoundedProc Ph ∧ 𝔼.Adapted Ph ∧ WoodfordReduced 𝔼 φp r pis ν Ph := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mp, hp⟩ := hpb
  obtain ⟨Mν, hν⟩ := hνb
  have h1 : 1 < |1 + φp| := by rw [abs_of_pos (by linarith)]; linarith
  set u : ℕ → Ω → ℝ := fun t => ν t - r t - 𝔼.E t (pis (t + 1)) with hu
  have huM : ∀ t ω, |u t ω| ≤ Mν + Mr + Mp := fun t ω => by
    simp only [hu, Pi.sub_apply]
    have := 𝔼.abs_E_le (hp (t + 1)) t ω
    calc |ν t ω - r t ω - 𝔼.E t (pis (t + 1)) ω|
        ≤ |ν t ω - r t ω| + |𝔼.E t (pis (t + 1)) ω| := abs_sub _ _
      _ ≤ |ν t ω| + |r t ω| + |𝔼.E t (pis (t + 1)) ω| := by gcongr; exact abs_sub _ _
      _ ≤ Mν + Mr + Mp := by linarith [hr t ω, hν t ω]
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu, map_sub, hra t, hνa t, 𝔼.E_E_self]
  obtain ⟨hs, hb, ha, huniq⟩ := SimplestModel.fwdSol_existsUnique 𝔼 h1 huM hua
  refine ⟨SimplestModel.fwdSol 𝔼 (1 + φp) u, ⟨hb, ha, (woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mpr
    hs⟩, fun Ph hP => huniq Ph ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hP.2.2) hP.1⟩

/-- Woodford (2003), Proposition 2.3, p. 82 (restated from the Woodford Chapter 2 project:
within `φ_p ≥ 0`, the log-linear system is determinate iff `φ_p > 0`), derived from Cochrane's
corrected determinacy condition for (16.8) (`SimplestModel.wicksell_determinate_iff`, survey E4:
`φ_p > 0` or `φ_p < −2`). -/
theorem woodford_determinate_iff [Nonempty Ω] {φp : ℝ} (hφ : 0 ≤ φp) :
    (∀ r pis ν : ℕ → Ω → ℝ, BoundedProc r → BoundedProc pis → BoundedProc ν → 𝔼.Adapted r →
      𝔼.Adapted ν → ∃! Ph, BoundedProc Ph ∧ WoodfordReduced 𝔼 φp r pis ν Ph) ↔ 0 < φp := by
  have hz : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun _ => map_zero _
  have e0 : ∀ u : ℕ → Ω → ℝ,
      (fun t => u t - (0 : ℕ → Ω → ℝ) t - 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1))) = u := fun u => by
    funext t
    simp
  constructor
  · intro h
    have hdet : ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
        ∃! x, BoundedProc x ∧ Eq164 𝔼 (1 + φp) u x := by
      intro u hub hua
      obtain ⟨x, hx, hxu⟩ := h 0 0 u hz hz hub hza hua
      refine ⟨x, ⟨hx.1, ?_⟩, fun y hy => hxu y ⟨hy.1, ?_⟩⟩
      · have := (woodfordReduced_iff_eq164 𝔼 φp 0 0 u x).mp hx.2
        rwa [e0] at this
      · rw [woodfordReduced_iff_eq164, e0]
        exact hy.2
    rcases (SimplestModel.wicksell_determinate_iff 𝔼 φp).mp hdet with h1 | h1
    · exact h1
    · linarith
  · intro hφ r pis ν hrb hpb hνb hra hνa
    obtain ⟨Ph, hP, huniq⟩ := woodford_prop_2_3_linear 𝔼 hφ hrb hpb hνb hra hνa
    refine ⟨Ph, ⟨hP.1, hP.2.2⟩, fun Q hQ => ?_⟩
    have h1 : 1 < |1 + φp| := by rw [abs_of_pos (by linarith)]; linarith
    exact SimplestModel.eq164_unique 𝔼 h1 ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hQ.2)
      ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hP.2.2) hQ.1 hP.1

/-! ### E6 and Woodford's Ricardian / non-Ricardian rules (Proposition 4.11) -/

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project), used for
Cochrane (2023), (16.20)–(16.22), p. 373: the law of motion of real debt under a linear tax rule,
`d_{t+1} = β⁻¹[(1 − τ_b) d_t − (b̄ + τ_π) π_t + (1 − τ_g) G_t − τ_y Y_t] + (b̄ − β⁻¹τ_i) i_t
− β⁻¹ v_t`. -/
def WoodfordDebt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Cochrane (2023), (16.20)–(16.22), p. 373, with `γ = α`: the debt of the unified model follows
Woodford's tax-rule debt dynamics (4.5) with `β = ρ`, `τ_b = α`, `b̄ = 0`, `τ_π = 1` applied to
unexpected inflation `ΔE_{t+1} π_{t+1}`, no other inputs, and the fiscal disturbance
`v_t = u_{s,t+1}`. -/
theorem fiscalBlock_debt45 {ρ α : ℝ} (hρ : ρ ≠ 0) {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : ObservationalEquivalence.FiscalBlock 𝔼 ρ α α us pistar π s v vs) :
    WoodfordDebt45 ρ 0 α 0 1 0 0 v (fun t => innov 𝔼 t (π (t + 1))) 0 0 0
      (fun t => us (t + 1)) := by
  intro t
  have e := ObservationalEquivalence.v_dyn 𝔼 h t
  rw [sub_self, zero_smul, sub_zero] at e
  funext ω
  have e' := congrFun e ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e' ⊢
  field_simp
  linarith

/-- Cochrane (2023), p. 373 (survey error E6, `ObservationalEquivalence.passive_iff`) in
Woodford's terms: on an expectation system with a nonzero innovation, fiscal policy
(16.20)–(16.22) is passive iff `γ = α`, and then real debt follows Woodford's (4.5) with
`τ_b = α`. -/
theorem e6_passive_iff_woodford45 {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us)
    (hnt : ∃ (x : ℕ → Ω → ℝ) (t : ℕ), innov 𝔼 t (x (t + 1)) ≠ 0) :
    (ObservationalEquivalence.FiscalPassive 𝔼 ρ α γ us ↔ γ = α) ∧
      ∀ pistar π s v vs : ℕ → Ω → ℝ,
        ObservationalEquivalence.FiscalBlock 𝔼 ρ α α us pistar π s v vs →
        WoodfordDebt45 ρ 0 α 0 1 0 0 v (fun t => innov 𝔼 t (π (t + 1))) 0 0 0
          (fun t => us (t + 1)) :=
  ⟨ObservationalEquivalence.passive_iff 𝔼 hρ0 hρ1 hα0 hα2 hus husa hnt,
    fun _ _ _ _ _ h => fiscalBlock_debt45 𝔼 hρ0.ne' h⟩

/-- Woodford (2003), p. 314 (restated from the Woodford Chapter 4 project), for Cochrane (2023),
p. 373: for `0 < β` and `τ_b ≤ 1`, Woodford's locally-Ricardian condition `|β⁻¹(1 − τ_b)| < 1`
(Proposition 4.11's dividing line) holds iff `τ_b > 1 − β`. -/
theorem woodford_ricardian_iff {β τb : ℝ} (hβ : 0 < β) (hτ : τb ≤ 1) :
    |β⁻¹ * (1 - τb)| < 1 ↔ 1 - β < τb := by
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ.le) (by linarith)), ← div_eq_inv_mul,
    div_lt_one hβ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 373, and Woodford (2003), Proposition 4.11, p. 314: a surplus rule that is
locally Ricardian in Woodford's sense (`|ρ⁻¹(1 − α)| < 1`, with `γ = α`) is passive in Cochrane's
transversality sense. -/
theorem passive_of_ricardian {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hR : |ρ⁻¹ * (1 - α)| < 1) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    ObservationalEquivalence.FiscalPassive 𝔼 ρ α α us := by
  have h1 : |1 - α| < ρ := by
    have e : |1 - α| = ρ * |ρ⁻¹ * (1 - α)| := by
      rw [abs_mul, abs_inv, abs_of_pos hρ0, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
    rw [e]
    calc ρ * |ρ⁻¹ * (1 - α)| < ρ * 1 := mul_lt_mul_of_pos_left hR hρ0
      _ = ρ := mul_one ρ
  have h2 := abs_lt.mp h1
  exact ObservationalEquivalence.passive_of_eq 𝔼 hρ0 hρ1 (by linarith) (by linarith) hus

/-- Cochrane (2023), p. 373, and Woodford (2003), Proposition 4.11, p. 314: the converse fails —
Cochrane's passivity (the transversality condition along every path) is weaker than Woodford's
local Ricardianness (bounded debt). With `ρ = 1/2` and `γ = α = 1/4` fiscal policy is passive,
yet `|ρ⁻¹(1 − α)| = 3/2 > 1`. -/
theorem passive_not_ricardian {M : ℝ} {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    ObservationalEquivalence.FiscalPassive 𝔼 (1 / 2) (1 / 4) (1 / 4) us ∧
      ¬ |(1 / 2 : ℝ)⁻¹ * (1 - 1 / 4)| < 1 := by
  refine ⟨ObservationalEquivalence.passive_of_eq 𝔼 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hus, ?_⟩
  norm_num [abs_of_pos]

/-! ### §16.3 and §16.8: the fiscal block -/

/-- Cochrane (2023), §16.8, pp. 377–379, and §16.3, p. 368: every perfect-foresight equilibrium
of the full model of §16.8 (`LowerBound.IsEquilibrium`) satisfies the fiscal block restated in
§16.3: the Fisher equation `FisherPF`, the flow condition `Flow`, the valuation equation
(16.26) `Valuation` and the transversality condition `TVC`. -/
theorem isEquilibrium_hyper {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {Pm1 : ℝ} {P i s D : ℕ → ℝ}
    (h : LowerBound.IsEquilibrium r Φ Pm1 P i s D) :
    Hyperinflation.FisherPF r P i ∧ Hyperinflation.Flow P D i s ∧
      Hyperinflation.Valuation r P D s ∧ Hyperinflation.TVC r P D := by
  have hdyn := LowerBound.equilibrium_dynamics hr h
  obtain ⟨-, hP, hi, hfis, -, hflow, hval⟩ := h
  refine ⟨fun t => ?_, hflow, hval, ?_⟩
  · have e := hfis t
    have h1 : 0 < 1 + i t := by linarith [hi t]
    have h2 := (hP t).ne'
    have h3 := (hP (t + 1)).ne'
    field_simp at e ⊢
    linarith
  · unfold Hyperinflation.TVC
    simpa using hdyn.2.2.2 0

/-- Cochrane (2023), p. 379 ("a specific version of the specification `s_t = γ(B_{t−1}/P_t)` that
produces passive fiscal policy") and §16.3, p. 368: the transversality condition of
`Hyperinflation.passive_tvc` also follows from the §16.8 criterion
`LowerBound.passive_gamma_tvc_iff` with `γ = r/(1 + r) ∈ (0, 2)`. -/
theorem passive_tvc_of_gamma {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : Hyperinflation.FisherPF r P i) (hflow : Hyperinflation.Flow P D i s)
    (hpas : Hyperinflation.PassiveRule r P D s) : Hyperinflation.TVC r P D := by
  have h1 : 0 < 1 + r := by linarith
  have hb : ∀ t, D (t + 1) / P (t + 1) =
      (1 + r) * (D t / P t - r / (1 + r) * (D t / P t)) := fun t => by
    rw [Hyperinflation.real_debt_flow h1 hP hF hflow t, hpas t]
  exact (LowerBound.passive_gamma_tvc_iff h1).mpr (LowerBound.passive_coefficient_mem hr) _ hb

/-! ### Transversality conditions -/

/-- Cochrane (2023), p. 137, p. 368 and p. 373: the expectation-system transversality condition
of the unified model (`ObservationalEquivalence.TVC`, `ρ^T E_t v_{t+T} → 0` at every date),
under perfect foresight with `ρ = 1/(1 + r)` and `v_t = B_{t−1}/P_t`, is the §16.3 condition
`Hyperinflation.TVC` (`(1 + r)^{−T} B_{T−1}/P_T → 0`): the date-0 limit implies the limit at
every date. -/
theorem tvc_pf_iff {r : ℝ} (hr : 0 < 1 + r) (P D : ℕ → ℝ) :
    ObservationalEquivalence.TVC perfectForesight (1 + r)⁻¹ (fun t _ => D t / P t) ↔
      Hyperinflation.TVC r P D := by
  constructor
  · intro h
    unfold Hyperinflation.TVC
    simpa [perfectForesight] using h 0 ()
  · intro h t ω
    have hshift := h.comp (tendsto_add_atTop_nat t)
    have hc := hshift.const_mul ((1 + r) ^ t)
    rw [mul_zero] at hc
    refine hc.congr fun T => ?_
    change (1 + r) ^ t * ((1 + r)⁻¹ ^ (T + t) * (D (T + t) / P (T + t))) =
      (1 + r)⁻¹ ^ T * (D (t + T) / P (t + T))
    rw [add_comm T t, pow_add, ← mul_assoc, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne',
      one_pow, one_mul]

/-- Cochrane (2023), §16.3, p. 368, under uncertainty: the passive-fiscal transversality result
`Hyperinflation.stoch_tvc` is the transversality condition `ObservationalEquivalence.TVC` of the
unified model (16.20)–(16.22) for real debt with `ρ = 1/(1 + r)`. -/
theorem stoch_tvc_obs (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r) {P D i s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (Hyperinflation.realDebt P D)) (hF : Hyperinflation.FisherE 𝔼 r P i)
    (hflow : Hyperinflation.FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) :
    ObservationalEquivalence.TVC 𝔼 (1 + r)⁻¹ (Hyperinflation.realDebt P D) :=
  fun t ω => Hyperinflation.stoch_tvc 𝔼 hPO hr hP hi hk hb hF hflow hpas t ω

end Cochrane.NewKeynesianSelection.Links

set_option linter.style.longLine false
#print axioms Cochrane.NewKeynesianSelection.SchurStable
#print axioms Cochrane.NewKeynesianSelection.discQ
#print axioms Cochrane.NewKeynesianSelection.root₁
#print axioms Cochrane.NewKeynesianSelection.root₂
#print axioms Cochrane.NewKeynesianSelection.root_sum
#print axioms Cochrane.NewKeynesianSelection.root_prod
#print axioms Cochrane.NewKeynesianSelection.root_eq
#print axioms Cochrane.NewKeynesianSelection.normSq_root_of_neg
#print axioms Cochrane.NewKeynesianSelection.norm_root_of_nonneg
#print axioms Cochrane.NewKeynesianSelection.schurStable_iff_roots
#print axioms Cochrane.NewKeynesianSelection.chSeq
#print axioms Cochrane.NewKeynesianSelection.convSeq
#print axioms Cochrane.NewKeynesianSelection.convSeq_rec
#print axioms Cochrane.NewKeynesianSelection.chSeq_eq_convSeq
#print axioms Cochrane.NewKeynesianSelection.norm_convSeq_le
#print axioms Cochrane.NewKeynesianSelection.abs_chSeq_le
#print axioms Cochrane.NewKeynesianSelection.tendsto_chSeq
#print axioms Cochrane.NewKeynesianSelection.tr2
#print axioms Cochrane.NewKeynesianSelection.det2
#print axioms Cochrane.NewKeynesianSelection.tr2_eq_trace
#print axioms Cochrane.NewKeynesianSelection.det2_eq_det
#print axioms Cochrane.NewKeynesianSelection.sq_eq_cayleyHamilton
#print axioms Cochrane.NewKeynesianSelection.pow_succ_eq
#print axioms Cochrane.NewKeynesianSelection.abs_pow_entry_le
#print axioms Cochrane.NewKeynesianSelection.tendsto_pow_entry
#print axioms Cochrane.NewKeynesianSelection.BoundedSeq
#print axioms Cochrane.NewKeynesianSelection.homogeneous_iterate
#print axioms Cochrane.NewKeynesianSelection.abs_mulVec_le
#print axioms Cochrane.NewKeynesianSelection.homogeneous_eq_zero
#print axioms Cochrane.NewKeynesianSelection.eq_root_of_eq
#print axioms Cochrane.NewKeynesianSelection.exists_eigenvector
#print axioms Cochrane.NewKeynesianSelection.exists_bounded_homogeneous
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.mk
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.E
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.const
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.mono
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.tower
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.known
#print axioms Cochrane.NewKeynesianSelection.perfectForesight
#print axioms Cochrane.NewKeynesianSelection.BoundedProc
#print axioms Cochrane.NewKeynesianSelection.BoundedVec
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.Adapted
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.IsAR1
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.E_neg
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.E_smul
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.E_E_self
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.abs_E_le
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.bounded_E
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.ar1_iterate
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forward_iterate
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forward_unique
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.E_tsum
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forwardSeries
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.PullOut
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.Solves
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.AdaptedVec
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.system_iterate
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.system_unique
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.system_not_unique
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.Determinate
#print axioms Cochrane.NewKeynesianSelection.ExpectationSystem.determinate_iff
#print axioms Cochrane.NewKeynesianSelection.perfectForesight_pullOut
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.NewKeynesianSelection.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.Solves
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.E_of_known
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.solves_adapted
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.iterate_A15
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.summable_A16
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.ScalarEq
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalarSol
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalarSol_apply
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalarEq_iff
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalar_homog
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sunspotFamily
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.homog_solves
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.solves_add_homog
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.existsUnique_iff
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.ar1_decay
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.predetermined_restriction
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.summable_geom_mul
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.abel_tsum
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.NewKeynesianSelection.ForwardSolution.E_tsum_dom
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_add
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_sub
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_smul
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_neg
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_const
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_of_known
#print axioms Cochrane.NewKeynesianSelection.Innovation.E_innov_zero
#print axioms Cochrane.NewKeynesianSelection.Innovation.E_innov_zero_of_le
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_eq_sub_E
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_known_next
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_E_succ
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_mul_known
#print axioms Cochrane.NewKeynesianSelection.Innovation.eq_E_add_innov
#print axioms Cochrane.NewKeynesianSelection.Innovation.decomposition_unique
#print axioms Cochrane.NewKeynesianSelection.Innovation.telescope_innov
#print axioms Cochrane.NewKeynesianSelection.Innovation.IsShock
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_shock
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_shock_later
#print axioms Cochrane.NewKeynesianSelection.Innovation.E_shock_of_le
#print axioms Cochrane.NewKeynesianSelection.Innovation.isShock_iff_innov
#print axioms Cochrane.NewKeynesianSelection.Innovation.innovProc
#print axioms Cochrane.NewKeynesianSelection.Innovation.innovProc_isShock
#print axioms Cochrane.NewKeynesianSelection.Innovation.eq_E_add_innovProc
#print axioms Cochrane.NewKeynesianSelection.Innovation.isShock_lin
#print axioms Cochrane.NewKeynesianSelection.Innovation.isShock_smul
#print axioms Cochrane.NewKeynesianSelection.Innovation.isShock_neg
#print axioms Cochrane.NewKeynesianSelection.Innovation.adapted_isShock_iff
#print axioms Cochrane.NewKeynesianSelection.Innovation.isShock_zero
#print axioms Cochrane.NewKeynesianSelection.Innovation.AR1Law
#print axioms Cochrane.NewKeynesianSelection.Innovation.ar1_of_shock
#print axioms Cochrane.NewKeynesianSelection.Innovation.shock_of_ar1
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_ar1
#print axioms Cochrane.NewKeynesianSelection.Innovation.E_ar1_shift
#print axioms Cochrane.NewKeynesianSelection.Innovation.innov_tsum
#print axioms Cochrane.NewKeynesianSelection.Innovation.coinShock_adapted
#print axioms Cochrane.NewKeynesianSelection.Innovation.coin_shock_ne_zero
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.summable_E_shift
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pvNews
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.E_forwardSeries_succ
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.innov_forwardSeries
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pvNews_isShock
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.PegModel
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegModel_iff
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegSol
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegSol_adapted
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.peg_existsUnique
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegSol_bounded
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.irf_peg_impact
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.irf_peg_later
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.expected_inflation_ahead
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.passiveShock
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.passiveShock_isShock
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.passive_valuation_holds
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.passive_any_innovation
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.RuleModel
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.Disturbance
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.Eq224
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.ruleModel_iff
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.eq224_iff
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.ruleSol
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.ruleSol_adapted
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.rule_existsUnique
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.rule_eq_peg
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.ruleSol_bounded
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.ruleSol_unbounded
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.peg_stable_determinate
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.peg_quiet
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.peg_unexpected_sq
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.fisher_alone_any_innovation
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.fisher_alone_not_countable
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.PegModelR
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegR_iff
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegR_existsUnique
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.pegR_expected
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.real_rate_passthrough
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.zero_peg_deflation
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.peg_steady_state_iff
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.rule_expected_path
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.rule_determinate_unstable
#print axioms Cochrane.NewKeynesianSelection.FTPLSimple.rule_stable
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.NKModel
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.Eq164
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nk_iff
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.passive_163
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nk_passive_iff
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nk_with_163_iff_ruleModel
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol_eq_ruleSol
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol_adapted
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol_solves
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.eq164_iff_165
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.eq_nkSol
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol_inj
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.equilibria_bijOn
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.expected_succ
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.sunspot_expected
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.expected_const_converges
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.expected_bounded
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.converges_needs_convergent_u
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.sunspot_fades
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.nkSol_bounded
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.indeterminate_of_abs_lt_one
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.coin_sunspot
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.eq164_unique
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.eq164_iff_scalar
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.fwdSol
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.fwdSol_apply
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.eq164_adapted
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.fwdSol_existsUnique
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.explodes_of_ne_fwdSol
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.determinate_iff
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1Pi
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1Pi_eq164
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1Pi_adapted
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1Pi_bounded
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1_solution
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1_rate
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1_law_1610
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.ar1_selection
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.irf_ar1
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.fig161_values
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.fig161_reverts
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.WicksellModel
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.wicksell_iff
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.wicksell_existsUnique
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.wicksell_apply
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.wicksell_determinate_iff
#print axioms Cochrane.NewKeynesianSelection.SimplestModel.printed_wicksell_false
#print axioms Cochrane.NewKeynesianSelection.KingForm.KingRule
#print axioms Cochrane.NewKeynesianSelection.KingForm.toU
#print axioms Cochrane.NewKeynesianSelection.KingForm.kingRule_iff
#print axioms Cochrane.NewKeynesianSelection.KingForm.kingModel_iff_nk
#print axioms Cochrane.NewKeynesianSelection.KingForm.toU_bounded
#print axioms Cochrane.NewKeynesianSelection.KingForm.toU_adapted
#print axioms Cochrane.NewKeynesianSelection.KingForm.eq1614_iff
#print axioms Cochrane.NewKeynesianSelection.KingForm.target_solves
#print axioms Cochrane.NewKeynesianSelection.KingForm.eq_target_of_bounded
#print axioms Cochrane.NewKeynesianSelection.KingForm.deviation_expected
#print axioms Cochrane.NewKeynesianSelection.KingForm.deviation_explodes
#print axioms Cochrane.NewKeynesianSelection.KingForm.fwdSol_toU
#print axioms Cochrane.NewKeynesianSelection.KingForm.toU_fwdSol
#print axioms Cochrane.NewKeynesianSelection.KingForm.translation_bijOn
#print axioms Cochrane.NewKeynesianSelection.KingForm.any_target_attainable
#print axioms Cochrane.NewKeynesianSelection.KingForm.eqm_rate_eq_target
#print axioms Cochrane.NewKeynesianSelection.KingForm.expected_set_by_rate
#print axioms Cochrane.NewKeynesianSelection.KingForm.unexpected_set_by_selection
#print axioms Cochrane.NewKeynesianSelection.KingForm.thetaRule_iff
#print axioms Cochrane.NewKeynesianSelection.KingForm.ftpl_same_inflation
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.FisherPF
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.Flow
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.PassiveRule
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.TVC
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.Valuation
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.real_debt_flow_scalar
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.real_debt_flow
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.passive_real_debt_const_real
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.passive_real_debt_const
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.passive_tvc
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.passive_valuation
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.any_price_path_eqm
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.zero_bound_iff_scalar
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.zero_bound_iff
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyperP
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyperP_pos
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyper_log_inflation
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyper_linear_eqm
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyper_rule
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyper_explodes
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.hyperinflation_satisfies_tvc
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.FisherE
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.FlowE
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.realDebt
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.stoch_real_debt_martingale
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.stoch_expected_real_debt
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.stoch_tvc
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.stoch_valuation
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.RealDebtFlow
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.pv_partial
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.ftpl_discounted_debt
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.ftpl_tvc_iff
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.ftpl_real_explosion
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.ftpl_price_level_iff
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.expected_path
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.stable_of_abs_lt_one
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.unstable_of_one_lt_abs
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.oscillating_of_lt_neg_one
#print axioms Cochrane.NewKeynesianSelection.Hyperinflation.determinate_of_lt_neg_one
#print axioms Cochrane.NewKeynesianSelection.Identification.fisherRate
#print axioms Cochrane.NewKeynesianSelection.Identification.NKEq
#print axioms Cochrane.NewKeynesianSelection.Identification.nkEq_iff
#print axioms Cochrane.NewKeynesianSelection.Identification.Selected
#print axioms Cochrane.NewKeynesianSelection.Identification.selected_of
#print axioms Cochrane.NewKeynesianSelection.Identification.selected_unique
#print axioms Cochrane.NewKeynesianSelection.Identification.reverseU
#print axioms Cochrane.NewKeynesianSelection.Identification.reverse_nkEq
#print axioms Cochrane.NewKeynesianSelection.Identification.reverse_selected
#print axioms Cochrane.NewKeynesianSelection.Identification.every_eq_selected
#print axioms Cochrane.NewKeynesianSelection.Identification.u_eq_of_nkEq
#print axioms Cochrane.NewKeynesianSelection.Identification.phi_eq_of_same_u
#print axioms Cochrane.NewKeynesianSelection.Identification.reverseU_sub
#print axioms Cochrane.NewKeynesianSelection.Identification.IdentifiedOn
#print axioms Cochrane.NewKeynesianSelection.Identification.identified_iff_learnable
#print axioms Cochrane.NewKeynesianSelection.Identification.nkClass
#print axioms Cochrane.NewKeynesianSelection.Identification.nkObs
#print axioms Cochrane.NewKeynesianSelection.Identification.nk_fiber_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.zero_selected
#print axioms Cochrane.NewKeynesianSelection.Identification.phi_not_identified
#print axioms Cochrane.NewKeynesianSelection.Identification.u_not_identified
#print axioms Cochrane.NewKeynesianSelection.Identification.phi_not_learnable
#print axioms Cochrane.NewKeynesianSelection.Identification.law_obs_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.AR1
#print axioms Cochrane.NewKeynesianSelection.Identification.AR1.E_succ
#print axioms Cochrane.NewKeynesianSelection.Identification.AR1.isAR1
#print axioms Cochrane.NewKeynesianSelection.Identification.ar1_selected
#print axioms Cochrane.NewKeynesianSelection.Identification.eq_16_10
#print axioms Cochrane.NewKeynesianSelection.Identification.eq_16_15
#print axioms Cochrane.NewKeynesianSelection.Identification.eq_16_16_innov
#print axioms Cochrane.NewKeynesianSelection.Identification.eq_16_18
#print axioms Cochrane.NewKeynesianSelection.Identification.ObsAR1
#print axioms Cochrane.NewKeynesianSelection.Identification.ar1_obs
#print axioms Cochrane.NewKeynesianSelection.Identification.obs_selected_every_phi
#print axioms Cochrane.NewKeynesianSelection.Identification.ni2_same_iff
#print axioms Cochrane.NewKeynesianSelection.Identification.ni2_rescaled
#print axioms Cochrane.NewKeynesianSelection.Identification.olsNoInt
#print axioms Cochrane.NewKeynesianSelection.Identification.sampleMean
#print axioms Cochrane.NewKeynesianSelection.Identification.olsSlope
#print axioms Cochrane.NewKeynesianSelection.Identification.olsIntercept
#print axioms Cochrane.NewKeynesianSelection.Identification.ivEst
#print axioms Cochrane.NewKeynesianSelection.Identification.olsNoInt_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.sampleMean_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.olsSlope_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.olsIntercept_eq_zero
#print axioms Cochrane.NewKeynesianSelection.Identification.ivEst_eq_add
#print axioms Cochrane.NewKeynesianSelection.Identification.ivEst_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.ni3_ols
#print axioms Cochrane.NewKeynesianSelection.Identification.ni3_ols_slope
#print axioms Cochrane.NewKeynesianSelection.Identification.ni3_ols_ne_phi
#print axioms Cochrane.NewKeynesianSelection.Identification.ni3_iv
#print axioms Cochrane.NewKeynesianSelection.Identification.ols_ar_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.KingEq
#print axioms Cochrane.NewKeynesianSelection.Identification.TargetsConsistent
#print axioms Cochrane.NewKeynesianSelection.Identification.king_target_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.king_bounded_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.king_selection_zero
#print axioms Cochrane.NewKeynesianSelection.Identification.king_eq_set
#print axioms Cochrane.NewKeynesianSelection.Identification.king_eq_set_indep
#print axioms Cochrane.NewKeynesianSelection.Identification.ThetaEq
#print axioms Cochrane.NewKeynesianSelection.Identification.ThetaConsistent
#print axioms Cochrane.NewKeynesianSelection.Identification.thetaEq_iff_king
#print axioms Cochrane.NewKeynesianSelection.Identification.thetaEq_target
#print axioms Cochrane.NewKeynesianSelection.Identification.thetaRule_eq_obs
#print axioms Cochrane.NewKeynesianSelection.Identification.iv_identifies_iff
#print axioms Cochrane.NewKeynesianSelection.Identification.theta_eq_phi_no_shock_zero
#print axioms Cochrane.NewKeynesianSelection.Identification.RREq
#print axioms Cochrane.NewKeynesianSelection.Identification.rr_iv_eq_phi_add
#print axioms Cochrane.NewKeynesianSelection.Identification.rr_iv_eq_phi_iff
#print axioms Cochrane.NewKeynesianSelection.Identification.rr_unique
#print axioms Cochrane.NewKeynesianSelection.Identification.rr_example
#print axioms Cochrane.NewKeynesianSelection.Identification.FTPLEq
#print axioms Cochrane.NewKeynesianSelection.Identification.ftplClass
#print axioms Cochrane.NewKeynesianSelection.Identification.ftpl_theta_eq
#print axioms Cochrane.NewKeynesianSelection.Identification.ftpl_theta_identified
#print axioms Cochrane.NewKeynesianSelection.Identification.ftpl_theta_learnable
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftpl_eq_225
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftpl_unique
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftpl_exists
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_is_ftpl
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_eq_ftpl_path
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.passive_surplus_eq_active
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.obs_irf
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_irf
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftpl_irf
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_irf_eq_ftpl_irf
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_to_ftpl
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nk_to_peg
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftpl_to_nk
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nkObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ftplObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.nkObsSet_eq_ftplObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.selectedObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.boundedFtplObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.selectedObsSet_eq_boundedFtplObsSet
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.MonetaryBlock
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.FiscalBlock
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.TVC
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.UnifiedEq
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.e_dyn
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.vs_dyn
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.v_dyn
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.E_gap
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.rec_limit
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.tendsto_tvc
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.tvc_iff
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.gap_zero_iff
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.FiscalPassive
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.passive_of_eq
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.fiscalPath
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.fiscalSurplus
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.fiscalPath_block
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.not_passive_of_ne
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.passive_iff
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.gap_succ
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.af_regime
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.af_regime_phi_zero
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.am_regime
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.ObsFiscal
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.unifiedEq_obs
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.obs_unifiedEq
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.eqObs
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.eqObs_eq
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.regimes_observationally_equivalent
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.gamma_phi_not_identified
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.eqObs_nonempty
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.unifiedClass
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.gamma_phi_not_learnable
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.coin_innov_ne_zero
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.coin_passive_iff
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.e6_printed_fails
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.coinSunspot
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.coinSunspot_monetary
#print axioms Cochrane.NewKeynesianSelection.ObservationalEquivalence.e6_counterexample
#print axioms Cochrane.NewKeynesianSelection.Responses.king_iff_nk
#print axioms Cochrane.NewKeynesianSelection.Responses.u_shock_eq_target
#print axioms Cochrane.NewKeynesianSelection.Responses.alt_paths
#print axioms Cochrane.NewKeynesianSelection.Responses.NonExplosive
#print axioms Cochrane.NewKeynesianSelection.Responses.alt_paths_explode
#print axioms Cochrane.NewKeynesianSelection.Responses.nonExplosive_iff
#print axioms Cochrane.NewKeynesianSelection.Responses.real_rate_zero
#print axioms Cochrane.NewKeynesianSelection.Responses.expected_follows_rate
#print axioms Cochrane.NewKeynesianSelection.Responses.fisherian_sign
#print axioms Cochrane.NewKeynesianSelection.Responses.impulse_path
#print axioms Cochrane.NewKeynesianSelection.Responses.impact_signs
#print axioms Cochrane.NewKeynesianSelection.Responses.super_fisherian
#print axioms Cochrane.NewKeynesianSelection.Responses.open_mouth
#print axioms Cochrane.NewKeynesianSelection.Responses.open_mouth_price_jump
#print axioms Cochrane.NewKeynesianSelection.Responses.dateOneShock
#print axioms Cochrane.NewKeynesianSelection.Responses.dateOneShock_isShock
#print axioms Cochrane.NewKeynesianSelection.Responses.superU
#print axioms Cochrane.NewKeynesianSelection.Responses.superU_ar1
#print axioms Cochrane.NewKeynesianSelection.Responses.super_fisherian_coin
#print axioms Cochrane.NewKeynesianSelection.Responses.open_mouth_coin
#print axioms Cochrane.NewKeynesianSelection.Responses.RuleExpEq
#print axioms Cochrane.NewKeynesianSelection.Responses.ruleExp_trivial
#print axioms Cochrane.NewKeynesianSelection.Responses.ruleExp_solutions
#print axioms Cochrane.NewKeynesianSelection.Responses.ruleExp_has_solution
#print axioms Cochrane.NewKeynesianSelection.Responses.ruleExp_disturbance
#print axioms Cochrane.NewKeynesianSelection.Responses.NK3Eq
#print axioms Cochrane.NewKeynesianSelection.Responses.no_fiscal_no_surprise
#print axioms Cochrane.NewKeynesianSelection.Responses.nk3_ar1_fiscal_iff
#print axioms Cochrane.NewKeynesianSelection.Responses.no_eq_without_fiscal
#print axioms Cochrane.NewKeynesianSelection.Responses.disinflation_iff_contraction
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.orbit_monotone_of_le
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.orbit_antitone_of_ge
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.fixed_of_tendsto
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.monotone_orbit_atTop_or_fixed
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.antitone_orbit_atBot_or_fixed
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.sign_near_of_deriv_pos
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.repelling_of_one_lt_abs_deriv
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.attracting_of_abs_deriv_lt_one
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.oppCost
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.oppCost_zero
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.discount
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.ricardian_step
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.ricardian_discounted
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.ricardian_tvc
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.ricardian_tvc_fails_of_alpha_zero
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.eq45_iff_fisher
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.IsPath45
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.IsPath46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.fisher_path_iff_eq45
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.isPath45_iff_isPath46_of_const
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.map46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.orbit46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.orbit46_succ
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.orbit46_isPath
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.isPath46_eq_orbit
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.bound44Term
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.bound44_summable
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.continuum_pf_equilibria
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.target_isFixed
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.hasDerivAt_map46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.taylorCoeff_eq_slope
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.second_steady_state
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.map46_step_down
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.self_fulfilling_deflation46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation46_strictAnti
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation46_eventually_deflation
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflationary_steady_state_indeterminate
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.inflation_unbounded46
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.inflation_unbounded_iff
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.phiCE
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.e6_counterexample
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.target_locally_repelling
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.target_locally_unique
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.ratio_strictMonoOn
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.steady_state45_iff
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.isPath45_unique
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.step45_down
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.self_fulfilling_deflation45
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation45_exists
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation45_bound44
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.step45_down_gen
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.self_fulfilling_deflation45_gen
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation45_exists_gen
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.antitone_lam_gives_gen
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.phiCE45
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation45_counterexample
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.bound44_summable_path
#print axioms Cochrane.NewKeynesianSelection.GlobalDynamics.deflation45_bound44_gen
#print axioms Cochrane.NewKeynesianSelection.LowerBound.BondPricing
#print axioms Cochrane.NewKeynesianSelection.LowerBound.bondPricing_perfectForesight_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.fisher_pf_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.log_fisher_pf
#print axioms Cochrane.NewKeynesianSelection.LowerBound.abs_exp_sub_le
#print axioms Cochrane.NewKeynesianSelection.LowerBound.hasDerivAt_E_exp
#print axioms Cochrane.NewKeynesianSelection.LowerBound.hasDerivAt_log_bondPricing
#print axioms Cochrane.NewKeynesianSelection.LowerBound.E_exp_pos
#print axioms Cochrane.NewKeynesianSelection.LowerBound.gateaux_log_bondPricing
#print axioms Cochrane.NewKeynesianSelection.LowerBound.hasDerivAt_log_rule
#print axioms Cochrane.NewKeynesianSelection.LowerBound.dynamics_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.eq_orbit
#print axioms Cochrane.NewKeynesianSelection.LowerBound.orbit_succ
#print axioms Cochrane.NewKeynesianSelection.LowerBound.target_repelling
#print axioms Cochrane.NewKeynesianSelection.LowerBound.target_unique_locally_bounded
#print axioms Cochrane.NewKeynesianSelection.LowerBound.zero_bound_eq_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.rule_respects_bound_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.lower_steady_state
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiTan
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiTan_poly_ge
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiTan_eq
#print axioms Cochrane.NewKeynesianSelection.LowerBound.hasDerivAt_tanPoly
#print axioms Cochrane.NewKeynesianSelection.LowerBound.hasDerivAt_phiTan
#print axioms Cochrane.NewKeynesianSelection.LowerBound.e2_tangency_counterexample
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiTan_left_unstable
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiJump
#print axioms Cochrane.NewKeynesianSelection.LowerBound.e2_discontinuous_counterexample
#print axioms Cochrane.NewKeynesianSelection.LowerBound.deflation_tendsto_lower
#print axioms Cochrane.NewKeynesianSelection.LowerBound.deflation_strictAnti
#print axioms Cochrane.NewKeynesianSelection.LowerBound.phiTan_deflation_tendsto
#print axioms Cochrane.NewKeynesianSelection.LowerBound.lower_locally_indeterminate
#print axioms Cochrane.NewKeynesianSelection.LowerBound.valuation_of_tvc
#print axioms Cochrane.NewKeynesianSelection.LowerBound.tvc_of_valuation
#print axioms Cochrane.NewKeynesianSelection.LowerBound.valuation_iff_tvc
#print axioms Cochrane.NewKeynesianSelection.LowerBound.passive_gamma_tvc_iff
#print axioms Cochrane.NewKeynesianSelection.LowerBound.passive_coefficient_mem
#print axioms Cochrane.NewKeynesianSelection.LowerBound.prevP
#print axioms Cochrane.NewKeynesianSelection.LowerBound.infl
#print axioms Cochrane.NewKeynesianSelection.LowerBound.IsEquilibrium
#print axioms Cochrane.NewKeynesianSelection.LowerBound.equilibrium_dynamics
#print axioms Cochrane.NewKeynesianSelection.LowerBound.equilibrium_exists
#print axioms Cochrane.NewKeynesianSelection.LowerBound.continuum_of_equilibria
#print axioms Cochrane.NewKeynesianSelection.LowerBound.deflationary_equilibria
#print axioms Cochrane.NewKeynesianSelection.LowerBound.truncRule
#print axioms Cochrane.NewKeynesianSelection.LowerBound.truncRule_props
#print axioms Cochrane.NewKeynesianSelection.LowerBound.truncRule_orbit_gap
#print axioms Cochrane.NewKeynesianSelection.LowerBound.truncRule_hits_bound
#print axioms Cochrane.NewKeynesianSelection.LowerBound.example_two_one
#print axioms Cochrane.NewKeynesianSelection.LowerBound.negative_real_rate_example
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.msv_unique
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.msv_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.msv_none_of_eq
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.simpleModel_pf_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.pf_explosive_not_msv
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.pf_passive_bounded_not_msv
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.rpow_orbit
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.msv_nonlinear_counterexample
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.quantity_theory_growth
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ACKEq
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ack_inconsistent
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ack_bounded
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ack_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ack_prunes_inflation
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ack_keeps_deflation
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.woodford_backstop_prunes
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.StabEq
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stabPath
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stabPath_taylor
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stabPath_money
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stab_exists
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stab_unique
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.stop_not_rule_out
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bsgu_real_debt
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bsgu_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bsgu_no_equilibrium_to_lower
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bsgu_target_survives
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.mubar_tvc_step
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.mubar_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.mubar_deflation_violates
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.mubar_target_tvc_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.tvcValue
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.tvcValue_succ
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.taylor_tvc_violated_of_eventually_le
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.e4_printed_inequality_false
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.e4_corrected_inequality
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.deflation_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.zero_bound_inflation_eq_beta
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.zero_bound_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.fig24_deflations_violate_tvc
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar.target_tvc_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.c1opt
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.uSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.c1opt_optimal
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lambda_A54_binding
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lambda_A54_satiated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.LSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.money_demand_A55
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lamSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lambda_of_i
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lamSGU_tendsto_atTop
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.elasticity
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.hasDerivAt_lamSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.elasticity_lt_one
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.elasticity_tendsto_one
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.elasticity_i_lt_one
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.ellSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.phiSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.one_add_phiSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.phiSGU_nonneg
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.phiSGU_continuous
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.phiSGU_target
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.taylorCoeff_phiSGU
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguA
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguC
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.lamSGU_phi_pos
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.eq45_iff_AB
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguAB_formula
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB_formula
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguA_antitone
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguA_tendsto
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB_strictAntiOn
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB_gt
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB_tendsto
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguA_lt_B_above
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguB_lt_A_below
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sgu_at_beta
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguPibar
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguPibar_spec
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sgu_no_successor
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sguAB_continuousAt
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sgu_no_hyperinflation
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sgu_deflation_tendsto
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.sgu_unique_pf_equilibrium
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.gE5
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.priceFrom
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.phiE5
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.gE5_mem
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.gE5_eq45
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.SGU.e5_counterexample
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.eq1632_iff
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.eq1632_iff_path45
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.successor_exists_of_bounded_rule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.path_exists_of_bounded_rule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.boundedRule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.boundedRate
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.moneyDemand
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ucMoney
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.boundedRate_ge
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bounded_rule_explosion
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bassetto_exit
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.bassetto_no_equilibrium
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.linRule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.linear_rule_exit
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.vertical_rule_exit
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.v_rule_unbounded
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.v_rule_unique_bounded
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.vRule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.vRule_props
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ahJump
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.ahJump_props
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.tangentRule
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.tangent_rule_converges
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.sims_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.sims_tvc_violated_of_eventually_beta
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.sims_no_bite_above_beta
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.sims_slow_counterexample
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_helicopter_pv
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_helicopter_tvc_violated
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_omo_real_const
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_omo_nominal
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_omo_debt_negative
#print axioms Cochrane.NewKeynesianSelection.SelectionPatches.a3_omo_tvc
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.infl_path
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.eq1634
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.closed_form
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.closed_form_book
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.closed_form_eq
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.debt_explodes
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.tvc_iff
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.e1_tvc_violated_iff
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.e1_counterexample
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.active_iff
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.valuation_iff_tvc
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.valuation_fails
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.stationary_iff
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.stationary_counterexample
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.passive_of_bounded
#print axioms Cochrane.NewKeynesianSelection.SimsTinyFiscal.selected_path_indep_theta
#print axioms Cochrane.NewKeynesianSelection.Links.nkEq_iff_nkModel
#print axioms Cochrane.NewKeynesianSelection.Links.selected_iff_eq_fwdSol
#print axioms Cochrane.NewKeynesianSelection.Links.ar1_selected_eq_fwdSol
#print axioms Cochrane.NewKeynesianSelection.Links.ftplEq_iff_ruleModel
#print axioms Cochrane.NewKeynesianSelection.Links.ftplEq_eq_ruleSol
#print axioms Cochrane.NewKeynesianSelection.Links.nk3Eq_iff_ruleModel
#print axioms Cochrane.NewKeynesianSelection.Links.nk_is_ruleModel
#print axioms Cochrane.NewKeynesianSelection.Links.ruleModel_eq164
#print axioms Cochrane.NewKeynesianSelection.Links.rule_expected_path_of_eq164
#print axioms Cochrane.NewKeynesianSelection.Links.king_disturbance_eq_toU
#print axioms Cochrane.NewKeynesianSelection.Links.kingEq_iff_kingRule
#print axioms Cochrane.NewKeynesianSelection.Links.king_bounded_eq_of_kingForm
#print axioms Cochrane.NewKeynesianSelection.Links.WoodfordReduced
#print axioms Cochrane.NewKeynesianSelection.Links.woodfordReduced_iff_eq164
#print axioms Cochrane.NewKeynesianSelection.Links.wicksellModel_iff_woodford
#print axioms Cochrane.NewKeynesianSelection.Links.woodford_prop_2_3_linear
#print axioms Cochrane.NewKeynesianSelection.Links.woodford_determinate_iff
#print axioms Cochrane.NewKeynesianSelection.Links.WoodfordDebt45
#print axioms Cochrane.NewKeynesianSelection.Links.fiscalBlock_debt45
#print axioms Cochrane.NewKeynesianSelection.Links.e6_passive_iff_woodford45
#print axioms Cochrane.NewKeynesianSelection.Links.woodford_ricardian_iff
#print axioms Cochrane.NewKeynesianSelection.Links.passive_of_ricardian
#print axioms Cochrane.NewKeynesianSelection.Links.passive_not_ricardian
#print axioms Cochrane.NewKeynesianSelection.Links.isEquilibrium_hyper
#print axioms Cochrane.NewKeynesianSelection.Links.passive_tvc_of_gamma
#print axioms Cochrane.NewKeynesianSelection.Links.tvc_pf_iff
#print axioms Cochrane.NewKeynesianSelection.Links.stoch_tvc_obs
