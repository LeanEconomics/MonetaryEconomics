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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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

Restated from the `Gali/ClassicalMonetaryModel` project (each project in this
repository is self-contained).
-/

namespace Gali.MonetaryPolicyDesign

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

end Gali.MonetaryPolicyDesign

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

Restated from the `Gali/ClassicalMonetaryModel` project (each project in this
repository is self-contained).
-/

namespace Gali.MonetaryPolicyDesign

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

end Gali.MonetaryPolicyDesign

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

Restated from the `Gali/ClassicalMonetaryModel` project (each project in this
repository is self-contained).
-/

namespace Gali.MonetaryPolicyDesign.ExpectationsFiniteTree

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

end Gali.MonetaryPolicyDesign.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The efficient allocation

Galí (2015), Chapter 4, §4.1, pp. 98–99, eqs. (1)–(3).

A benevolent planner maximises period utility
`U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z` (the book's utility of ch. 3, p. 54, with
`u(C) = (C^{1−σ} − 1)/(1 − σ)`, `log C` for `σ = 1`) where `C = (∫ C(i)^{(ε−1)/ε})^{ε/(ε−1)}`
is the CES consumption index, subject to the technologies `C(i) = A N(i)^{1−α}` and the labour
resource constraint `∫ N(i) = N`.

Goods are indexed by a probability space `(G, μ)`, which covers both the book's continuum
`[0, 1]` with Lebesgue measure (`planner_optimal_iff_unitInterval`) and finitely many goods with
weights `w i > 0`, `∑ w i = 1` (`planner_optimal_iff_finite`). An allocation is a measurable
`N(·) ≥ 0`, integrable, with `∫ N(i) > 0` (`Feasible`).

## Main results

* `aggConsumption_le`, `aggConsumption_eq_iff`: for a given total `N`, the CES index of
  `A N(i)^{1−α}` is at most `A N^{1−α}`, with equality **iff** `N(i) = N` for a.e. `i`
  (strict concavity of `x ↦ x^{(1−α)(ε−1)/ε}`, integrated Bernoulli/Jensen inequality).
* `welfare_le_symWelfare`, `welfare_eq_symWelfare_iff`: hence welfare is at most the welfare of
  the symmetric allocation with the same total employment, with equality iff symmetric.
* `marginal_utilities`, `hasDerivAt_output`: `−U_n/U_c = C^σ N^φ` (`mrs`) and
  `MPN = (1 − α) A N^{−α}` (`mpn`), as exact derivatives.
* `symWelfare_isMax_iff_foc`: along symmetric allocations, `N > 0` maximises welfare **iff**
  condition (3), `MRS = MPN`, holds (necessity and sufficiency).
* `mrs_sym_eq_mpn_iff`, `existsUnique_efficient`: (3) has exactly one solution,
  `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}` (`effEmployment`), which is the unique
  maximiser; `symWelfare_lt` is the strict welfare loss away from `N*`.
* `planner_optimal_iff`: a feasible allocation is optimal **iff** (1) `C(i) = C`, (2)
  `N(i) = N` a.e. and (3) `MRS = MPN`; `planner_optimal_iff_effEmployment`: iff `N(i) = N*`
  a.e.; `planner_existsUnique`: the optimum exists and is unique up to null sets.
* `welfare_lt_of_not_symmetric`: any non-symmetric allocation is strictly worse than the
  optimum.

Utility definitions and the tangent-line lemmas are restated from the Chapter 3 project
(`Household.lean`); `weightMeasure` from its `CES.lean`.
-/

namespace Gali.MonetaryPolicyDesign.Efficient

open MeasureTheory Filter Topology

/-! ### Period utility (restated from the Chapter 3 project) -/

/-- Galí (2015), p. 54 (ch. 3): utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1`
and `log C` for `σ = 1`. Restated from the Chapter 3 project. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 54 (ch. 3): disutility of labour `N^{1+φ}/(1+φ)`. Restated from the
Chapter 3 project. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 98 and p. 54: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`.
Restated from the Chapter 3 project. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), p. 99: marginal utility of consumption `u'(C) = C^{−σ}`. Restated from the
Chapter 3 project. -/
theorem hasDerivAt_utilC (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (utilC σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), p. 99: marginal disutility of labour `N^φ`. Restated from the Chapter 3
project. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 99 (concavity of utility): marginal utility `C^{−σ}` is nonincreasing
for `σ > 0`. Restated from the Chapter 3 project. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 99, concavity of utility). Restated from the Chapter 3
project. -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 99: the utility of consumption is concave for `σ > 0`, in tangent-line
form `u(y) ≤ u(x) + x^{−σ}(y − x)`. Restated from the Chapter 3 project. -/
theorem utilC_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilC σ y ≤ utilC σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun C => C ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilC σ hz)
    (antitoneOn_margUtil hσ)
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilC σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 99: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`v(x) + x^φ (y − x) ≤ v(y)`. Restated from the Chapter 3 project. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 99 (`U_c > 0`): the utility of consumption is strictly increasing on
`(0, ∞)`, in both the `σ ≠ 1` and the log case. -/
theorem utilC_lt_utilC {σ : ℝ} {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    utilC σ x < utilC σ y := by
  unfold utilC
  by_cases h1 : σ = 1
  · simp only [h1, ↓reduceIte]
    exact Real.log_lt_log hx hxy
  · simp only [h1, ↓reduceIte]
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hs : 0 < 1 - σ := by linarith
      have := Real.rpow_lt_rpow hx.le hxy hs
      exact div_lt_div_of_pos_right (by linarith) hs
    · have hs : 1 - σ < 0 := by linarith
      have := Real.rpow_lt_rpow_of_neg hx hxy hs
      exact (div_lt_div_right_of_neg hs).2 (by linarith)

/-- Galí (2015), p. 99: the marginal utilities `U_c = C^{−σ} Z`, `U_n = −N^φ Z` (exact
derivatives), whose ratio is the marginal rate of substitution `−U_n/U_c = C^σ N^φ`. -/
theorem marginal_utilities {σ φ C N Z : ℝ} (hφ : 0 ≤ φ) (hC : 0 < C) (hZ : 0 < Z) :
    HasDerivAt (fun c => periodUtility σ φ c N Z) (C ^ (-σ) * Z) C ∧
      HasDerivAt (fun n => periodUtility σ φ C n Z) (-(N ^ φ) * Z) N ∧
      -(-(N ^ φ) * Z) / (C ^ (-σ) * Z) = C ^ σ * N ^ φ := by
  refine ⟨((hasDerivAt_utilC σ hC).sub_const _).mul_const Z, ?_, ?_⟩
  · have h := ((hasDerivAt_disutilN hφ N).const_sub (utilC σ C)).mul_const Z
    simpa [periodUtility] using h
  · have hc : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
    rw [Real.rpow_neg hC.le] at hc ⊢
    field_simp

/-! ### MRS, MPN and a tangent bound for powers -/

/-- Galí (2015), eq. (3), p. 99: the marginal rate of substitution `−U_n/U_c = C^σ N^φ`
(`marginal_utilities`). -/
noncomputable def mrs (σ φ C N : ℝ) : ℝ := C ^ σ * N ^ φ

/-- Galí (2015), p. 99: the marginal product of labour `MPN = (1 − α) A N^{−α}`. -/
noncomputable def mpn (α A N : ℝ) : ℝ := (1 - α) * A * N ^ (-α)

/-- Galí (2015), p. 99: `MPN` is the derivative of the technology `A N^{1−α}`. -/
theorem hasDerivAt_output {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) (mpn α A N) N := by
  refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv ?_
  rw [mpn, show (1 : ℝ) - α - 1 = -α by ring]
  ring

/-- Galí (2015), p. 99: `MPN > 0` for `α < 1`, `A > 0`, `N > 0`. -/
theorem mpn_pos {α A N : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) : 0 < mpn α A N :=
  mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hN _)

/-- Concavity of `x ↦ x^q` for `0 ≤ q ≤ 1` (Bernoulli), in tangent form at `N > 0`:
`x^q ≤ N^q (1 + q (x/N − 1))` (used for Galí (2015), p. 99, concavity of technology). -/
theorem rpow_le_tangent {q x N : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hN : 0 < N) (hx : 0 ≤ x) :
    x ^ q ≤ N ^ q * (1 + q * (x / N - 1)) := by
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have h := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at h
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_le_iff₀ hNq] at h
  linarith

/-- Strict concavity of `x ↦ x^q` for `0 < q < 1`: equality in `rpow_le_tangent` forces
`x = N` (Galí (2015), p. 99, "concavity of utility and production functions"). -/
theorem eq_of_rpow_eq_tangent {q x N : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 0 < N)
    (hx : 0 ≤ x) (h : x ^ q = N ^ q * (1 + q * (x / N - 1))) : x = N := by
  by_contra hne
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have hs' : x / N - 1 ≠ 0 := by
    intro h0
    apply hne
    have : x / N = 1 := by linarith
    rwa [div_eq_one_iff_eq hN.ne'] at this
  have hlt := rpow_one_add_lt_one_add_mul_self hs hs' hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at hlt
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_lt_iff₀ hNq] at hlt
  linarith

/-! ### The symmetric problem: condition (3) -/

/-- Galí (2015), p. 99: welfare of the symmetric allocation with total employment `N`,
`U(A N^{1−α}, N; Z)`. -/
noncomputable def symWelfare (σ φ α A Z N : ℝ) : ℝ := periodUtility σ φ (A * N ^ (1 - α)) N Z

/-- Galí (2015), p. 99: the efficient level of employment, the solution of (3) with
`C = A N^{1−α}`: `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def effEmployment (σ φ α A : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ)) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 99: the derivative of symmetric welfare,
`(C^{−σ} MPN − N^φ) Z` with `C = A N^{1−α}`. -/
theorem hasDerivAt_symWelfare {σ φ α A Z N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hN : 0 < N) :
    HasDerivAt (symWelfare σ φ α A Z)
      (((A * N ^ (1 - α)) ^ (-σ) * mpn α A N - N ^ φ) * Z) N := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := (hasDerivAt_utilC σ hC).comp N (hasDerivAt_output (α := α) (A := A) hN)
  exact (HasDerivAt.sub h1 (hasDerivAt_disutilN hφ N)).mul_const Z

/-- Galí (2015), p. 99 (exponent bookkeeping): `MRS(A N^{1−α}, N) · (1 − α) A^{1−σ}
= MPN(N) · N^{φ + α + σ(1 − α)}`. -/
theorem mrs_mul_eq {σ φ α A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N * ((1 - α) * A ^ (1 - σ))
      = mpn α A N * N ^ (φ + α + σ * (1 - α)) := by
  have e1 : (A * N ^ (1 - α)) ^ σ = A ^ σ * N ^ ((1 - α) * σ) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
  calc mrs σ φ (A * N ^ (1 - α)) N * ((1 - α) * A ^ (1 - σ))
      = (1 - α) * (A ^ σ * A ^ (1 - σ)) * (N ^ ((1 - α) * σ) * N ^ φ) := by
        rw [mrs, e1]; ring
    _ = (1 - α) * A * N ^ ((1 - α) * σ + φ) := by
        rw [← Real.rpow_add hA, ← Real.rpow_add hN]
        norm_num
    _ = (1 - α) * A * (N ^ (-α) * N ^ (φ + α + σ * (1 - α))) := by
        rw [← Real.rpow_add hN, show -α + (φ + α + σ * (1 - α)) = (1 - α) * σ + φ by ring]
    _ = mpn α A N * N ^ (φ + α + σ * (1 - α)) := by rw [mpn]; ring

/-- Galí (2015), p. 99: the exponent `φ + α + σ(1 − α)` is positive. -/
theorem effExponent_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < φ + α + σ * (1 - α) := by
  have := mul_pos hσ (by linarith : (0 : ℝ) < 1 - α)
  linarith

/-- Galí (2015), p. 99: efficient employment is positive. -/
theorem effEmployment_pos {σ φ α A : ℝ} (hα1 : α < 1) (hA : 0 < A) :
    0 < effEmployment σ φ α A :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) _

/-- Galí (2015), eq. (3), p. 99, **existence and uniqueness**: along the symmetric allocation
`C = A N^{1−α}`, `MRS = MPN` holds for `N > 0` iff `N = N*`. -/
theorem mrs_sym_eq_mpn_iff {σ φ α A N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N = mpn α A N ↔ N = effEmployment σ φ α A := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  have hm := mpn_pos hα1 hA hN
  have key := mrs_mul_eq (σ := σ) (φ := φ) (α := α) hA hN
  constructor
  · intro h
    rw [h] at key
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) :=
      (mul_left_cancel₀ hm.ne' key).symm
    rw [effEmployment, ← hNk, Real.rpow_rpow_inv hN.le hk.ne']
  · intro h
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) := by
      rw [h, effEmployment, Real.rpow_inv_rpow hc.le hk.ne']
    rw [hNk] at key
    exact mul_right_cancel₀ hc.ne' key

/-- Galí (2015), eq. (3), p. 99, **sufficiency**: if `MRS = MPN` at `N₀ > 0` (symmetric
allocation), then `N₀` maximises welfare over all `N > 0`. -/
theorem symWelfare_le_of_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀)
    (hfoc : mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀ := by
  set x := A * N₀ ^ (1 - α) with hxdef
  set y := A * N ^ (1 - α) with hydef
  have hx : 0 < x := mul_pos hA (Real.rpow_pos_of_pos hN₀ _)
  have hy : 0 < y := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := utilC_le_tangent hσ hx hy
  have h3 := disutilN_tangent_le hφ hN₀ hN.le
  have h2 := rpow_le_tangent (q := 1 - α) (by linarith) (by linarith) hN₀ hN.le
  have hyx : y - x ≤ mpn α A N₀ * (N - N₀) := by
    have e : mpn α A N₀ * (N - N₀) = A * (N₀ ^ (1 - α) * ((1 - α) * (N / N₀ - 1))) := by
      rw [mpn, Real.rpow_neg hN₀.le, Real.rpow_sub hN₀, Real.rpow_one]
      field_simp
    rw [e, hydef, hxdef]
    nlinarith
  have hxs : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx _
  have hfoc' : x ^ (-σ) * mpn α A N₀ = N₀ ^ φ := by
    rw [← hfoc, mrs, ← mul_assoc, Real.rpow_neg hx.le, inv_mul_cancel₀
      (Real.rpow_pos_of_pos hx σ).ne', one_mul]
  have h4 : x ^ (-σ) * (y - x) ≤ N₀ ^ φ * (N - N₀) := by
    rw [← hfoc', mul_assoc]
    exact mul_le_mul_of_nonneg_left hyx hxs.le
  unfold symWelfare periodUtility
  rw [← hxdef, ← hydef]
  exact mul_le_mul_of_nonneg_right (by linarith) hZ.le

/-- Galí (2015), eq. (3), p. 99, **necessity**: if `N₀ > 0` maximises symmetric welfare over
`N > 0`, then `MRS = MPN` at `N₀`. -/
theorem foc_of_symWelfare_isMax {σ φ α A Z N₀ : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hZ : 0 < Z)
    (hN₀ : 0 < N₀) (hmax : ∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) :
    mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ := by
  have hloc : IsLocalMax (symWelfare σ φ α A Z) N₀ :=
    Filter.mem_of_superset (Ioi_mem_nhds hN₀) fun N hN => hmax N hN
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_symWelfare hφ hA hN₀)
  set x := A * N₀ ^ (1 - α) with hxdef
  have hx : 0 < x := mul_pos hA (Real.rpow_pos_of_pos hN₀ _)
  have h1 : x ^ (-σ) * mpn α A N₀ = N₀ ^ φ := by
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact absurd h hZ.ne'
  have hxs : x ^ σ ≠ 0 := (Real.rpow_pos_of_pos hx σ).ne'
  rw [mrs, ← h1, Real.rpow_neg hx.le]
  field_simp

/-- Galí (2015), eq. (3), p. 99: along symmetric allocations, `N₀ > 0` maximises welfare
**iff** `MRS = MPN` at `N₀` (necessary and sufficient). -/
theorem symWelfare_isMax_iff_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) ↔
      mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ :=
  ⟨foc_of_symWelfare_isMax hφ hA hZ hN₀,
    fun h _ hN => symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN₀ h hN⟩

/-- Galí (2015), p. 99: efficient employment `N*` maximises symmetric welfare. -/
theorem symWelfare_le_eff {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ (effEmployment_pos hα1 hA)
    ((mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA (effEmployment_pos hα1 hA)).2 rfl) hN

/-- Galí (2015), p. 99: **strict** welfare loss away from efficient employment: for `N > 0`,
`N ≠ N*`, welfare is strictly below its efficient level. -/
theorem symWelfare_lt {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N)
    (hne : N ≠ effEmployment σ φ α A) :
    symWelfare σ φ α A Z N < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  refine lt_of_le_of_ne (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN) fun heq => hne ?_
  refine (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN ?_)
  intro N' hN'
  rw [heq]
  exact symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'

/-- Galí (2015), p. 99, **existence and uniqueness** of efficient employment: exactly one
`N > 0` maximises symmetric welfare, namely `N*`. -/
theorem existsUnique_efficient {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
  refine ⟨effEmployment σ φ α A, ⟨effEmployment_pos hα1 hA,
    fun N' hN' => symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN hmax)

/-! ### Allocation across goods: conditions (1) and (2) -/

namespace Goods

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 99: the CES consumption index `C = (∫ C(i)^{(ε−1)/ε})^{ε/(ε−1)}`. -/
noncomputable def cesIndex (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), p. 99: the resource constraint for good `i`, `C(i) = A N(i)^{1−α}`. -/
noncomputable def goodsOutput (A α : ℝ) (n : G → ℝ) (i : G) : ℝ := A * n i ^ (1 - α)

/-- Galí (2015), p. 99: the consumption index of the allocation `N(·)`. -/
noncomputable def aggConsumption (μ : Measure G) (ε A α : ℝ) (n : G → ℝ) : ℝ :=
  cesIndex μ ε (goodsOutput A α n)

/-- Galí (2015), p. 99: a feasible labour allocation: measurable, `N(i) ≥ 0`, integrable,
with total employment `N = ∫ N(i) > 0`. -/
def Feasible (μ : Measure G) (n : G → ℝ) : Prop :=
  Measurable n ∧ (∀ i, 0 ≤ n i) ∧ Integrable n μ ∧ 0 < ∫ i, n i ∂μ

/-- Galí (2015), p. 98: the planner's objective, `U(C, N; Z)` with `C` the index of the
allocation and `N = ∫ N(i)`. -/
noncomputable def welfare (μ : Measure G) (σ φ ε A α Z : ℝ) (n : G → ℝ) : ℝ :=
  periodUtility σ φ (aggConsumption μ ε A α n) (∫ i, n i ∂μ) Z

variable {μ : Measure G}

/-- Galí (2015), p. 99: `(A x^{1−α})^r = A^r x^{(1−α) r}`. -/
theorem goodsOutput_rpow {A α r x : ℝ} (hA : 0 < A) (hx : 0 ≤ x) :
    (A * x ^ (1 - α)) ^ r = A ^ r * x ^ ((1 - α) * r) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]

/-- Galí (2015), p. 99: for `0 ≤ q ≤ 1`, `N(i)^q` is integrable when `N(·)` is feasible
(on a probability space). -/
theorem integrable_rpow [IsProbabilityMeasure μ] {n : G → ℝ} (hn : Feasible μ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Integrable (fun i => n i ^ q) μ := by
  obtain ⟨hm, h0, hi, -⟩ := hn
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
    (hm.pow_const q).aestronglyMeasurable (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 i) q)]
  have := rpow_le_tangent hq0 hq1 one_pos (h0 i)
  simp only [Real.one_rpow, div_one, one_mul] at this
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right hq1 (h0 i)]

/-- Galí (2015), p. 99 (Jensen): for `0 < q < 1`, `∫ N(i)^q ≤ (∫ N(i))^q`, with equality
**iff** `N(i) = ∫ N` for a.e. `i`. -/
theorem integral_rpow_le [IsProbabilityMeasure μ] {n : G → ℝ} (hn : Feasible μ n) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ i, n i ^ q ∂μ ≤ (∫ i, n i ∂μ) ^ q ∧
      (∫ i, n i ^ q ∂μ = (∫ i, n i ∂μ) ^ q ↔ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  have hf := integrable_rpow hn hq0.le hq1.le
  set g : G → ℝ := fun i => N ^ q * (1 - q) + N ^ q * q / N * n i with hg
  have hgi : Integrable g μ := (integrable_const _).add (hn.2.2.1.const_mul _)
  have hpt : ∀ i, n i ^ q ≤ g i := fun i => by
    have := rpow_le_tangent hq0.le hq1.le hN (hn.2.1 i)
    simp only [hg]
    have e : N ^ q * (1 + q * (n i / N - 1)) = N ^ q * (1 - q) + N ^ q * q / N * n i := by
      field_simp
      ring
    linarith
  have hgint : ∫ i, g i ∂μ = N ^ q := by
    simp only [hg]
    rw [integral_add (integrable_const _) (hn.2.2.1.const_mul _), integral_const,
      integral_const_mul, ← hNdef]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  have hle : ∫ i, n i ^ q ∂μ ≤ N ^ q := hgint ▸ integral_mono hf hgi hpt
  refine ⟨hle, ⟨fun heq => ?_, fun h => ?_⟩⟩
  · rw [← hgint] at heq
    have hae := (integral_eq_iff_of_ae_le hf hgi (Eventually.of_forall hpt)).1 heq
    filter_upwards [hae] with i hi
    refine eq_of_rpow_eq_tangent hq0 hq1 hN (hn.2.1 i) ?_
    rw [hi]
    simp only [hg]
    field_simp
    ring
  · rw [integral_congr_ae (g := fun _ => N ^ q) (by filter_upwards [h] with i hi; rw [hi])]
    simp

/-- Galí (2015), p. 99: the exponent `q = (1 − α)(ε − 1)/ε` lies in `(0, 1)`. -/
theorem q_mem {ε α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  have hr0 : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  have hr1 : (ε - 1) / ε < 1 := (div_lt_one (by linarith)).2 (by linarith)
  refine ⟨mul_pos (by linarith) hr0, ?_⟩
  calc (1 - α) * ((ε - 1) / ε) ≤ 1 * ((ε - 1) / ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
    _ < 1 := by linarith

/-- Galí (2015), p. 99: `∫ C(i)^r = A^r ∫ N(i)^{(1−α) r}`. -/
theorem integral_goodsOutput_rpow {A α r : ℝ} (hA : 0 < A) {n : G → ℝ} (hn : ∀ i, 0 ≤ n i) :
    ∫ i, goodsOutput A α n i ^ r ∂μ = A ^ r * ∫ i, n i ^ ((1 - α) * r) ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun i => goodsOutput_rpow hA (hn i))

/-- Galí (2015), p. 99: rewriting the index, `C = (A^r ∫ N(i)^q)^{1/r}`. -/
theorem aggConsumption_eq {ε A α : ℝ} (hA : 0 < A) {n : G → ℝ} (hn : ∀ i, 0 ≤ n i) :
    aggConsumption μ ε A α n
      = (A ^ ((ε - 1) / ε) * ∫ i, n i ^ ((1 - α) * ((ε - 1) / ε)) ∂μ) ^ ((ε - 1) / ε)⁻¹ := by
  rw [aggConsumption, cesIndex, integral_goodsOutput_rpow hA hn]

/-- Galí (2015), p. 99: `(A^r N^{(1−α) r})^{1/r} = A N^{1−α}`. -/
theorem symmetric_index {ε A α N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hN : 0 ≤ N) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ ((ε - 1) / ε)⁻¹
      = A * N ^ (1 - α) := by
  have hr : (ε - 1) / ε ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hN _),
    Real.rpow_rpow_inv hA.le hr, ← Real.rpow_mul hN, mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- Galí (2015), p. 99: the consumption index of a feasible allocation is positive. -/
theorem aggConsumption_pos [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    0 < aggConsumption μ ε A α n := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  rw [aggConsumption_eq hA hn.2.1]
  refine Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hA _) ?_) _
  have hnn : 0 ≤ fun i => n i ^ ((1 - α) * ((ε - 1) / ε)) :=
    fun i => Real.rpow_nonneg (hn.2.1 i) _
  rcases (integral_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg hnn (integrable_rpow hn hq0.le hq1.le)).1 h.symm
    have hn0 : (fun i => n i) =ᵐ[μ] 0 := by
      filter_upwards [hz] with i hi
      exact ((Real.rpow_eq_zero_iff_of_nonneg (hn.2.1 i)).1 hi).1
    have := hn.2.2.2
    rw [integral_congr_ae hn0] at this
    simp at this

/-- Galí (2015), eqs. (1)–(2), p. 99: for a feasible allocation with total employment
`N = ∫ N(i)`, the consumption index is at most `A N^{1−α}`. -/
theorem aggConsumption_le [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    aggConsumption μ ε A α n ≤ A * (∫ i, n i ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hε hA hn.2.2.2.le]
  refine Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA.le _)
    (integral_nonneg fun i => Real.rpow_nonneg (hn.2.1 i) _)) ?_ (inv_nonneg.2 hr.le)
  exact mul_le_mul_of_nonneg_left (integral_rpow_le hn hq0 hq1).1 (Real.rpow_nonneg hA.le _)

/-- Galí (2015), eqs. (1)–(2), p. 99: the bound `C ≤ A N^{1−α}` holds with equality **iff**
`N(i) = N` for a.e. `i` (strict concavity). -/
theorem aggConsumption_eq_iff [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    aggConsumption μ ε A α n = A * (∫ i, n i ∂μ) ^ (1 - α) ↔
      ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  obtain ⟨hle, hiff⟩ := integral_rpow_le hn hq0 hq1
  rw [← hiff, aggConsumption_eq hA hn.2.1, ← symmetric_index hε hA hn.2.2.2.le]
  have hAr : 0 < A ^ ((ε - 1) / ε) := Real.rpow_pos_of_pos hA _
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have := Real.rpow_lt_rpow (mul_nonneg hAr.le
      (integral_nonneg fun i => Real.rpow_nonneg (hn.2.1 i) _))
      (mul_lt_mul_of_pos_left hlt hAr) (inv_pos.2 hr)
    linarith
  · intro h
    rw [h]

/-- Galí (2015), p. 99: a constant allocation `N(i) = N > 0` is feasible. -/
theorem feasible_const [IsProbabilityMeasure μ] {N : ℝ} (hN : 0 < N) :
    Feasible μ (fun _ => N) :=
  ⟨measurable_const, fun _ => hN.le, integrable_const N, by simpa using hN⟩

/-- Galí (2015), p. 99: the welfare of the constant allocation `N(i) = N` is the symmetric
welfare `U(A N^{1−α}, N; Z)`. -/
theorem welfare_const [IsProbabilityMeasure μ] {σ φ ε A α Z N : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    welfare μ σ φ ε A α Z (fun _ => N) = symWelfare σ φ α A Z N := by
  have h := (aggConsumption_eq_iff hε hα0 hα1 hA (feasible_const (μ := μ) hN)).2
    (Eventually.of_forall fun _ => by simp)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  rw [welfare, h, symWelfare]
  simp

/-- Galí (2015), p. 99: welfare of a feasible allocation is at most the welfare of the
symmetric allocation with the same total employment. -/
theorem welfare_le_symWelfare [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n ≤ symWelfare σ φ α A Z (∫ i, n i ∂μ) := by
  unfold welfare symWelfare periodUtility
  refine mul_le_mul_of_nonneg_right (sub_le_sub_right ?_ _) hZ.le
  rcases (aggConsumption_le hε hα0 hα1 hA hn).lt_or_eq with h | h
  · exact (utilC_lt_utilC (aggConsumption_pos hε hα0 hα1 hA hn) h).le
  · rw [h]

/-- Galí (2015), eqs. (1)–(2), p. 99: equality in `welfare_le_symWelfare` holds **iff** the
allocation is symmetric, `N(i) = N` a.e. -/
theorem welfare_eq_symWelfare_iff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n = symWelfare σ φ α A Z (∫ i, n i ∂μ) ↔
      ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
  rw [← aggConsumption_eq_iff hε hα0 hα1 hA hn]
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne (aggConsumption_le hε hα0 hα1 hA hn) hne
    have h1 := utilC_lt_utilC (σ := σ) (aggConsumption_pos hε hα0 hα1 hA hn) hlt
    unfold welfare symWelfare periodUtility at h
    have h2 := mul_right_cancel₀ hZ.ne' h
    linarith
  · intro h
    rw [welfare, symWelfare, h]

/-- Galí (2015), p. 102: a **non-symmetric** allocation (`N(i) ≠ N` on a set of positive
measure) is strictly worse than the symmetric allocation with the same total employment. -/
theorem welfare_lt_symWelfare [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n)
    (hns : ¬ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) :
    welfare μ σ φ ε A α Z n < symWelfare σ φ α A Z (∫ i, n i ∂μ) :=
  lt_of_le_of_ne (welfare_le_symWelfare hε hα0 hα1 hA hZ hn)
    fun h => hns ((welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).1 h)

/-- Galí (2015), p. 99: every feasible allocation is (weakly) worse than the efficient
allocation `N(i) = N*`. -/
theorem welfare_le_eff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ}
    (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_le_symWelfare hε hα0 hα1 hA hZ hn).trans
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2)

/-- Galí (2015), p. 102: any non-symmetric feasible allocation is **strictly** worse than
the efficient allocation. -/
theorem welfare_lt_of_not_symmetric [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : G → ℝ} (hn : Feasible μ n) (hns : ¬ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) :
    welfare μ σ φ ε A α Z n < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_lt_symWelfare hε hα0 hα1 hA hZ hn hns).trans_le
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2)

/-- Galí (2015), eqs. (1)–(3), p. 99 (**necessary and sufficient**): a feasible allocation
maximises welfare over all feasible allocations iff (1) `C(i) = C` a.e., (2) `N(i) = N` a.e.
and (3) `MRS = MPN`, where `C` is the consumption index and `N = ∫ N(i)`. -/
theorem planner_optimal_iff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : G → ℝ} (hn : Feasible μ n) :
    (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) ↔
      (∀ᵐ i ∂μ, goodsOutput A α n i = aggConsumption μ ε A α n) ∧
      (∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) ∧
      mrs σ φ (aggConsumption μ ε A α n) (∫ i, n i ∂μ) = mpn α A (∫ i, n i ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  constructor
  · intro hopt
    have hsym : ∀ᵐ i ∂μ, n i = N := by
      refine (welfare_eq_symWelfare_iff (σ := σ) (φ := φ) hε hα0 hα1 hA hZ hn).1 (le_antisymm
        (welfare_le_symWelfare hε hα0 hα1 hA hZ hn) ?_)
      rw [← welfare_const (μ := μ) hε hα0 hα1 hA hN]
      exact hopt _ (feasible_const hN)
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    have hmax : ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
      intro N' hN'
      rw [← welfare_const (μ := μ) hε hα0 hα1 hA hN',
        ← (welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).2 hsym]
      exact hopt _ (feasible_const hN')
    refine ⟨?_, hsym, ?_⟩
    · filter_upwards [hsym] with i hi
      rw [goodsOutput, hi, hC]
    · rw [hC]
      exact foc_of_symWelfare_isMax hφ hA hZ hN hmax
  · rintro ⟨-, hsym, hfoc⟩ n' hn'
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    rw [hC] at hfoc
    rw [(welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).2 hsym]
    exact (welfare_le_symWelfare hε hα0 hα1 hA hZ hn').trans
      (symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN hfoc hn'.2.2.2)

/-- Galí (2015), §4.1, p. 99: a feasible allocation is optimal **iff** `N(i) = N*` for a.e.
`i`, where `N*` is efficient employment (`effEmployment`). -/
theorem planner_optimal_iff_effEmployment [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ}
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A)
    (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) ↔
      ∀ᵐ i ∂μ, n i = effEmployment σ φ α A := by
  rw [planner_optimal_iff hσ hφ hε hα0 hα1 hA hZ hn]
  have hN : 0 < ∫ i, n i ∂μ := hn.2.2.2
  constructor
  · rintro ⟨-, hsym, hfoc⟩
    rw [(aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym,
      mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN] at hfoc
    filter_upwards [hsym] with i hi
    rw [hi, hfoc]
  · intro h
    have hint : ∫ i, n i ∂μ = effEmployment σ φ α A := by
      rw [integral_congr_ae h]
      simp
    have hsym : ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
      filter_upwards [h] with i hi
      rw [hi, hint]
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    refine ⟨?_, hsym, ?_⟩
    · filter_upwards [hsym] with i hi
      rw [goodsOutput, hi, hC]
    · rw [hC, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN, hint]

/-- Galí (2015), §4.1, p. 99, **existence and uniqueness**: the efficient allocation
`N(i) = N*` is feasible and optimal, and every optimal allocation equals it a.e. -/
theorem planner_existsUnique [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    Feasible μ (fun _ => effEmployment σ φ α A) ∧
      (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n'
        ≤ welfare μ σ φ ε A α Z (fun _ => effEmployment σ φ α A)) ∧
      ∀ n, Feasible μ n →
        (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) →
        ∀ᵐ i ∂μ, n i = effEmployment σ φ α A := by
  have hf := feasible_const (μ := μ) (effEmployment_pos (σ := σ) (φ := φ) hα1 hA)
  refine ⟨hf, (planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hf).2
    (Eventually.of_forall fun _ => rfl), fun n hn hopt => ?_⟩
  exact (planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hn).1 hopt

/-! ### The continuum `[0, 1]` -/

/-- Galí (2015), p. 99: Lebesgue measure on the goods continuum `[0, 1]` is a probability
measure. -/
theorem isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

/-- Galí (2015), eqs. (1)–(3), p. 99, on the book's **continuum of goods `[0, 1]`**: a
feasible allocation is optimal iff (1), (2) and (3) hold, iff `N(i) = N*` for a.e. `i`. -/
theorem planner_optimal_iff_unitInterval {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : ℝ → ℝ}
    (hn : Feasible (volume.restrict (Set.Icc 0 1)) n) :
    ((∀ n' : ℝ → ℝ, Feasible (volume.restrict (Set.Icc 0 1)) n' →
        welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n) ↔
      (∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          goodsOutput A α n i = aggConsumption (volume.restrict (Set.Icc 0 1)) ε A α n) ∧
        (∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)), n i = ∫ j in Set.Icc 0 1, n j) ∧
        mrs σ φ (aggConsumption (volume.restrict (Set.Icc 0 1)) ε A α n)
          (∫ i in Set.Icc 0 1, n i) = mpn α A (∫ i in Set.Icc 0 1, n i)) ∧
    ((∀ n' : ℝ → ℝ, Feasible (volume.restrict (Set.Icc 0 1)) n' →
        welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n) ↔
      ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)), n i = effEmployment σ φ α A) := by
  have := isProbabilityMeasure_unitInterval
  exact ⟨planner_optimal_iff hσ hφ hε hα0 hα1 hA hZ hn,
    planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hn⟩

end Goods

/-! ### Finitely many goods -/

namespace Finite

open Goods

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), p. 99 (finitely many goods): the measure placing weight `w i` on good `i`.
Restated from the Chapter 3 project. -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Galí (2015), p. 99: the weighted measure gives good `x` mass `w x`. Restated from the
Chapter 3 project. -/
theorem weightMeasure_singleton {w : ι → ℝ} (x : ι) :
    weightMeasure w {x} = ENNReal.ofReal (w x) := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton x), hb]
  · simp

omit [MeasurableSingletonClass ι] in
/-- Galí (2015), p. 99: with `w ≥ 0` and `∑ w = 1` the weighted measure is a probability
measure. -/
theorem isProbabilityMeasure_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : IsProbabilityMeasure (weightMeasure w) := by
  constructor
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw i, h1, ENNReal.ofReal_one]

/-- Galí (2015), p. 99: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w i f i`. Restated from the Chapter 3 project. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (f : ι → ℝ) : ∫ i, f i ∂(weightMeasure w) = ∑ i, w i * f i := by
  have := isProbabilityMeasure_weightMeasure hw h1
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Galí (2015), p. 99: with positive weights, "almost every good" means every good. -/
theorem ae_weightMeasure_iff {w : ι → ℝ} (hw : ∀ i, 0 < w i) {p : ι → Prop} :
    (∀ᵐ i ∂(weightMeasure w), p i) ↔ ∀ i, p i := by
  refine ⟨fun h i => ?_, fun h => Eventually.of_forall h⟩
  by_contra hi
  have hpos : weightMeasure w {i} ≠ 0 := by
    rw [weightMeasure_singleton]
    exact (ENNReal.ofReal_pos.2 (hw i)).ne'
  exact hpos (measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hi)
    (ae_iff.1 h))

/-- Galí (2015), p. 99: for finitely many goods, an allocation `N(i) ≥ 0` with
`∑ w N(i) > 0` is feasible. -/
theorem feasible_of_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) {n : ι → ℝ}
    (hn : ∀ i, 0 ≤ n i) (hpos : 0 < ∑ i, w i * n i) : Feasible (weightMeasure w) n := by
  have := isProbabilityMeasure_weightMeasure hw h1
  exact ⟨Measurable.of_discrete, hn, Integrable.of_finite, by
    rwa [integral_weightMeasure hw h1]⟩

/-- Galí (2015), §4.1, p. 99, for **finitely many goods** with weights `w i > 0`,
`∑ w i = 1`: with `C = (∑ w (A N(i)^{1−α})^r)^{1/r}` and `N = ∑ w N(i)`, an allocation
`N(·) ≥ 0` with `N > 0` maximises `U(C, N; Z)` over all such allocations **iff**
`N(i) = N*` for **every** good `i`. -/
theorem planner_optimal_iff_finite {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (h1 : ∑ i, w i = 1) {n : ι → ℝ} (hn : ∀ i, 0 ≤ n i) (hpos : 0 < ∑ i, w i * n i) :
    (∀ n' : ι → ℝ, (∀ i, 0 ≤ n' i) → 0 < ∑ i, w i * n' i →
      periodUtility σ φ ((∑ i, w i * (A * n' i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * n' i) Z
        ≤ periodUtility σ φ ((∑ i, w i * (A * n i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * n i) Z) ↔
      ∀ i, n i = effEmployment σ φ α A := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have := isProbabilityMeasure_weightMeasure hw0 h1
  have hW : ∀ m : ι → ℝ, welfare (weightMeasure w) σ φ ε A α Z m
      = periodUtility σ φ ((∑ i, w i * (A * m i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * m i) Z := fun m => by
    rw [welfare, aggConsumption, cesIndex, integral_weightMeasure hw0 h1,
      integral_weightMeasure hw0 h1]
    rfl
  have h := planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ
    (feasible_of_nonneg hw0 h1 hn hpos)
  rw [ae_weightMeasure_iff hw] at h
  rw [← h, hW]
  constructor
  · intro hopt n' hn'
    rw [hW]
    have hf := hn'
    rw [Feasible, integral_weightMeasure hw0 h1] at hf
    exact hopt n' hf.2.1 hf.2.2.2
  · intro hopt n' hn' hpos'
    rw [← hW]
    exact hopt n' (feasible_of_nonneg hw0 h1 hn' hpos')

end Finite

end Gali.MonetaryPolicyDesign.Efficient

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sources of suboptimality in the basic New Keynesian model

Galí (2015), Chapter 4, §4.2, pp. 100–102.

## §4.2.1 Monopolistic competition (pp. 100–101)

A firm facing the isoelastic demand `Y(i) = (P(i)/P)^{−ε} Y` with technology
`Y(i) = A N(i)^{1−α}` and an employment subsidy at rate `τ < 1` (labour costs `(1 − τ) W`)
chooses employment (equivalently its price, `inverse_demand_iff`) to maximise profits.

* `firm_optimal_iff`: `N₀ > 0` is profit maximising **iff** the price-setting rule
  `P(i) = M (1 − τ) W / MPN(i)` holds, `M = ε/(ε − 1)`; `firm_existsUnique`: the optimum exists
  and is unique, hence identical across firms (`optimal_identical`); in a symmetric allocation
  this is `P = M (1 − τ) W/MPN` (`flex_price_rule`), and with the household's condition
  `W/P = MRS` gives `MRS = MPN/(M(1 − τ))` (`flex_mrs`), i.e. `MRS = MPN/M < MPN` for `τ = 0`.
* `mrs_eq_mpn_div_iff`, `existsUnique_flex`: for any wedge `w > 0` the condition
  `MRS = MPN/w` has exactly one solution `N(w)` (`flexEmployment`), with `N(1) = N*`.
* `flexEmployment_lt_eff`: a markup `w > 1` gives employment **strictly below** the efficient
  level; `lt_of_wedge` is the book's monotonicity argument (MRS increasing, MPN
  nonincreasing); `flex_welfare_lt`: the welfare loss is strict.
* `wedge_eq_one_iff_subsidy`, `flex_efficient_iff_subsidy`: the flexible-price allocation is
  efficient **iff** `M(1 − τ) = 1` **iff** `τ = 1/ε` (so the optimal subsidy is unique).

## §4.2.2 Sticky prices (pp. 101–102)

* `avgMarkup`, `mrs_eq_avgMarkup`: with the optimal subsidy, `MRS = MPN · M/M_t`;
  `foc_iff_avgMarkup`: (3) holds iff `M_t = M`; `employment_avgMarkup`: employment is
  `N(M_t/M)`, below/at/above `N*` iff `M_t >/=/< M`.
* `dispersion_violates_symmetry`, `dispersion_welfare_loss`: if relative prices are not all
  equal, the induced allocation violates (1) and (2) and is **strictly** worse than both the
  symmetric allocation with the same employment and the efficient allocation.
-/

namespace Gali.MonetaryPolicyDesign.Distortions

open MeasureTheory Filter Topology
open Gali.MonetaryPolicyDesign.Efficient

/-! ### The desired markup -/

/-- Galí (2015), p. 100: the desired (gross) markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 100: `M > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), p. 100: `M > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- Galí (2015), p. 100: `M · (ε − 1)/ε = 1`. -/
theorem markup_mul_r {ε : ℝ} (hε : 1 < ε) : markup ε * ((ε - 1) / ε) = 1 := by
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : ε ≠ 0 := by linarith
  rw [markup]
  field_simp

/-! ### The firm's problem under flexible prices -/

/-- Galí (2015), p. 100: the inverse of the isoelastic demand `y = (P(i)/P)^{−ε} Y`, the price
at which the firm sells `y`: `P(i) = P (y/Y)^{−1/ε}`. -/
noncomputable def invDemand (ε P Y y : ℝ) : ℝ := P * (y / Y) ^ (-ε⁻¹)

/-- Galí (2015), p. 100: choosing a price is equivalent to choosing a quantity: for `P(i)`,
`P`, `Y`, `y > 0`, `y = (P(i)/P)^{−ε} Y` iff `P(i) = P (y/Y)^{−1/ε}`. -/
theorem inverse_demand_iff {ε P Y y Pi : ℝ} (hε : 0 < ε) (hP : 0 < P) (hY : 0 < Y)
    (hy : 0 < y) (hPi : 0 < Pi) : y = (Pi / P) ^ (-ε) * Y ↔ Pi = invDemand ε P Y y := by
  have hne : -ε ≠ 0 := by linarith
  have hx : 0 < Pi / P := div_pos hPi hP
  rw [invDemand]
  constructor
  · intro h
    rw [h, mul_div_assoc, div_self hY.ne', mul_one, ← Real.rpow_neg_one ε, ← Real.rpow_mul hx.le]
    rw [show -ε * -ε ^ (-1 : ℝ) = 1 by rw [Real.rpow_neg_one]; field_simp, Real.rpow_one]
    field_simp
  · intro h
    have hyY : 0 < y / Y := div_pos hy hY
    have e : Pi / P = (y / Y) ^ (-ε⁻¹) := by rw [h]; field_simp
    rw [e, ← Real.rpow_mul hyY.le, show -ε⁻¹ * -ε = 1 by field_simp, Real.rpow_one]
    field_simp

/-- Galí (2015), p. 100: profits of a firm employing `N` (subsidy `τ`):
`P(i) Y(i) − (1 − τ) W N` with `Y(i) = A N^{1−α}` sold at the demand price. -/
noncomputable def firmProfit (ε α A W τ P Y N : ℝ) : ℝ :=
  invDemand ε P Y (A * N ^ (1 - α)) * (A * N ^ (1 - α)) - (1 - τ) * W * N

/-- Galí (2015), p. 100: the revenue constant `K = P Y^{1/ε} A^{(ε−1)/ε}`. -/
noncomputable def revConst (ε A P Y : ℝ) : ℝ := P * Y ^ ε⁻¹ * A ^ ((ε - 1) / ε)

/-- Galí (2015), p. 100: revenue is `P(i) Y(i) = K N^q`, `q = (1 − α)(ε − 1)/ε`. -/
theorem revenue_eq {ε α A P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y) (hN : 0 < N) :
    invDemand ε P Y (A * N ^ (1 - α)) * (A * N ^ (1 - α))
      = revConst ε A P Y * N ^ ((1 - α) * ((ε - 1) / ε)) := by
  have hy : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have hε0 : ε ≠ 0 := by linarith
  have e2 : A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))
      = (A * N ^ (1 - α)) ^ ((ε - 1) / ε) := (Goods.goodsOutput_rpow hA hN.le).symm
  have e : (A * N ^ (1 - α)) ^ ((ε - 1) / ε)
      = (A * N ^ (1 - α)) ^ (-ε⁻¹) * (A * N ^ (1 - α)) := by
    rw [show (ε - 1) / ε = -ε⁻¹ + 1 by field_simp; ring, Real.rpow_add hy, Real.rpow_one]
  rw [invDemand, revConst, mul_assoc (P * Y ^ ε⁻¹), e2, Real.div_rpow hy.le hY.le,
    Real.rpow_neg hY.le, div_inv_eq_mul, e]
  ring

/-- Galí (2015), p. 100: marginal revenue of labour, `K q N^q / N = r P(i) MPN(i)`
with `r = (ε − 1)/ε`. -/
theorem marginal_revenue_eq {ε α A P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y)
    (hN : 0 < N) :
    revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
      = (ε - 1) / ε * invDemand ε P Y (A * N ^ (1 - α)) * mpn α A N := by
  have h := revenue_eq (α := α) (P := P) hε hA hY hN
  have hN1 : N ^ (1 - α) / N = N ^ (-α) := by
    rw [← Real.rpow_sub_one hN.ne']
    ring_nf
  have e : revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
      = (1 - α) * ((ε - 1) / ε) * (revConst ε A P Y * N ^ ((1 - α) * ((ε - 1) / ε))) / N := by
    ring
  rw [e, ← h, mpn, ← hN1]
  ring

/-- Galí (2015), p. 100: the derivative of profits in `N`, `K q N^{q−1} − (1 − τ) W`. -/
theorem hasDerivAt_profit {ε α A W τ P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y)
    (hN : 0 < N) :
    HasDerivAt (firmProfit ε α A W τ P Y)
      (revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
        - (1 - τ) * W) N := by
  set q := (1 - α) * ((ε - 1) / ε)
  have hfun : ∀ᶠ M in 𝓝 N, firmProfit ε α A W τ P Y M
      = revConst ε A P Y * M ^ q - (1 - τ) * W * M := by
    filter_upwards [Ioi_mem_nhds hN] with M hM
    rw [firmProfit, revenue_eq hε hA hY hM]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  have h1 := ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hN.ne')).const_mul
    (revConst ε A P Y))
  have h2 := (hasDerivAt_id N).const_mul ((1 - τ) * W)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  rw [Real.rpow_sub_one hN.ne']
  simp only [mul_one]
  ring

/-- Galí (2015), p. 100: the first-order condition `K q N^q/N = (1 − τ) W` is equivalent to
the price-setting rule `P(i) = M (1 − τ) W / MPN(i)`. -/
theorem foc_iff_price_rule {ε α A W τ P Y N : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hY : 0 < Y) (hN : 0 < N) :
    revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
        = (1 - τ) * W ↔
      invDemand ε P Y (A * N ^ (1 - α)) = markup ε * ((1 - τ) * W / mpn α A N) := by
  rw [marginal_revenue_eq hε hA hY hN]
  have hm := mpn_pos hα1 hA hN
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [markup]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 100: the firm's problem is concave: if the first-order condition holds at
`N₀ > 0` then `N₀` maximises profits over `N > 0` (sufficiency). -/
theorem profit_le_of_foc {ε α A W τ P Y N₀ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hN₀ : 0 < N₀)
    (hfoc : revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N₀ ^ ((1 - α) * ((ε - 1) / ε)) / N₀
      = (1 - τ) * W) {N : ℝ} (hN : 0 < N) :
    firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₀ := by
  obtain ⟨hq0, hq1⟩ := Goods.q_mem hε hα0 hα1
  set q := (1 - α) * ((ε - 1) / ε) with hqdef
  have hK : 0 < revConst ε A P Y :=
    mul_pos (mul_pos hP (Real.rpow_pos_of_pos hY _)) (Real.rpow_pos_of_pos hA _)
  have ht := rpow_le_tangent hq0.le hq1.le hN₀ hN.le
  rw [firmProfit, firmProfit, revenue_eq hε hA hY hN, revenue_eq hε hA hY hN₀]
  have e : revConst ε A P Y * (N₀ ^ q * (1 + q * (N / N₀ - 1)))
      = revConst ε A P Y * N₀ ^ q + revConst ε A P Y * q * N₀ ^ q / N₀ * (N - N₀) := by
    field_simp
  have h1 := mul_le_mul_of_nonneg_left ht hK.le
  rw [e, hfoc] at h1
  nlinarith

/-- Galí (2015), p. 100: **the firm's optimum** (necessary and sufficient): `N₀ > 0` maximises
profits over `N > 0` iff the price-setting rule `P(i) = M (1 − τ) W / MPN(i)` holds. -/
theorem firm_optimal_iff {ε α A W τ P Y N₀ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₀) ↔
      invDemand ε P Y (A * N₀ ^ (1 - α)) = markup ε * ((1 - τ) * W / mpn α A N₀) := by
  rw [← foc_iff_price_rule hε hα1 hA hY hN₀]
  constructor
  · intro hmax
    have hloc : IsLocalMax (firmProfit ε α A W τ P Y) N₀ :=
      Filter.mem_of_superset (Ioi_mem_nhds hN₀) fun N hN => hmax N hN
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_profit (W := W) (τ := τ) hε hA hY hN₀)
    linarith
  · intro h N hN
    exact profit_le_of_foc hε hα0 hα1 hA hY hP hN₀ h hN

/-- Galí (2015), p. 100: the profit-maximising employment level,
`N° = ((1 − τ) W/(K q))^{1/(q − 1)}`. -/
noncomputable def firmEmployment (ε α A W τ P Y : ℝ) : ℝ :=
  ((1 - τ) * W / (revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)))) ^
    ((1 - α) * ((ε - 1) / ε) - 1)⁻¹

/-- Galí (2015), p. 100, **existence and uniqueness** of the firm's optimum (for `τ < 1`,
`W > 0`): exactly one `N > 0` maximises profits, `firmEmployment`. -/
theorem firm_existsUnique {ε α A W τ P Y : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hτ : τ < 1) (hW : 0 < W) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → firmProfit ε α A W τ P Y N' ≤ firmProfit ε α A W τ P Y N := by
  obtain ⟨hq0, hq1⟩ := Goods.q_mem hε hα0 hα1
  set q := (1 - α) * ((ε - 1) / ε) with hqdef
  have hK : 0 < revConst ε A P Y :=
    mul_pos (mul_pos hP (Real.rpow_pos_of_pos hY _)) (Real.rpow_pos_of_pos hA _)
  have hc : 0 < (1 - τ) * W / (revConst ε A P Y * q) :=
    div_pos (mul_pos (by linarith) hW) (mul_pos hK hq0)
  have hq1' : q - 1 ≠ 0 := by linarith
  -- the first-order condition is `N^{q−1} = (1 − τ) W/(K q)`
  have hfoc_iff : ∀ N, 0 < N →
      (revConst ε A P Y * q * N ^ q / N = (1 - τ) * W ↔
        N ^ (q - 1) = (1 - τ) * W / (revConst ε A P Y * q)) := by
    intro N hN
    rw [Real.rpow_sub_one hN.ne', eq_div_iff (mul_pos hK hq0).ne']
    constructor <;> intro h <;> rw [← h] <;> ring
  have hpos : 0 < firmEmployment ε α A W τ P Y := Real.rpow_pos_of_pos hc _
  refine ⟨firmEmployment ε α A W τ P Y, ⟨hpos, fun N' hN' => ?_⟩, ?_⟩
  · refine profit_le_of_foc hε hα0 hα1 hA hY hP hpos ?_ hN'
    rw [hfoc_iff _ hpos, firmEmployment, ← hqdef, Real.rpow_inv_rpow hc.le hq1']
  · rintro N ⟨hN, hmax⟩
    have h := (firm_optimal_iff hε hα0 hα1 hA hY hP hN).1 hmax
    rw [← foc_iff_price_rule hε hα1 hA hY hN, ← hqdef, hfoc_iff _ hN] at h
    rw [firmEmployment, ← hqdef, ← h, Real.rpow_rpow_inv hN.le hq1']

/-- Galí (2015), p. 100: "the profit maximising price is identical across firms": any two
profit-maximising employment levels (hence outputs and prices) coincide. -/
theorem optimal_identical {ε α A W τ P Y N₁ N₂ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hτ : τ < 1) (hW : 0 < W) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂)
    (h₁ : ∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₁)
    (h₂ : ∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₂) :
    N₁ = N₂ ∧ invDemand ε P Y (A * N₁ ^ (1 - α)) = invDemand ε P Y (A * N₂ ^ (1 - α)) := by
  have h := (firm_existsUnique hε hα0 hα1 hA hY hP hτ hW).unique ⟨hN₁, h₁⟩ ⟨hN₂, h₂⟩
  exact ⟨h, by rw [h]⟩

/-- Galí (2015), p. 100: in a symmetric allocation (`Y = A N^{1−α}`, so the firm's price is the
price level, `P(i) = P`), profit maximisation is the rule `P = M (1 − τ) W/MPN`. -/
theorem flex_price_rule {ε α A W τ P N : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hP : 0 < P) (hN : 0 < N) :
    (∀ N', 0 < N' → firmProfit ε α A W τ P (A * N ^ (1 - α)) N'
        ≤ firmProfit ε α A W τ P (A * N ^ (1 - α)) N) ↔
      P = markup ε * ((1 - τ) * W / mpn α A N) := by
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  rw [firm_optimal_iff hε hα0 hα1 hA hY hP hN, invDemand, div_self hY.ne', Real.one_rpow,
    mul_one]

/-- Galí (2015), p. 100 (τ = 0) and p. 101: with flexible prices `P = M (1 − τ) W/MPN` and the
household's condition `W/P = MRS`, `MRS = MPN/(M (1 − τ))`. For `τ = 0`, `MRS = MPN/M`. -/
theorem flex_mrs {ε α A W τ P C N σ φ : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hN : 0 < N) (hτ : τ < 1) (hW : 0 < W) (hP : P = markup ε * ((1 - τ) * W / mpn α A N))
    (hls : W / P = mrs σ φ C N) : mrs σ φ C N = mpn α A N / (markup ε * (1 - τ)) := by
  have hm := mpn_pos hα1 hA hN
  have hM := markup_pos hε
  have h1 : (0 : ℝ) < 1 - τ := by linarith
  rw [← hls, hP]
  field_simp

/-- Galí (2015), p. 100: with no subsidy the markup wedge violates (3): `MRS = MPN/M < MPN`. -/
theorem flex_mrs_lt_mpn {ε α A W P C N σ φ : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hN : 0 < N) (hW : 0 < W) (hP : P = markup ε * ((1 - 0) * W / mpn α A N))
    (hls : W / P = mrs σ φ C N) : mrs σ φ C N < mpn α A N := by
  rw [flex_mrs hε hα1 hA hN (by norm_num) hW hP hls, sub_zero, mul_one]
  exact div_lt_self (mpn_pos hα1 hA hN) (one_lt_markup hε)

/-! ### Equilibrium employment under a wedge -/

/-- Galí (2015), pp. 100–101: equilibrium employment when `MRS = MPN/w` along the symmetric
allocation, `N(w) = ((1 − α) A^{1−σ}/w)^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def flexEmployment (σ φ α A w : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ) / w) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 100: `N(w) > 0`. -/
theorem flexEmployment_pos {σ φ α A w : ℝ} (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    0 < flexEmployment σ φ α A w :=
  Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw) _

/-- Galí (2015), pp. 100–101: along the symmetric allocation, `MRS = MPN/w` holds for `N > 0`
**iff** `N = N(w)` (existence and uniqueness of the distorted equilibrium level). -/
theorem mrs_eq_mpn_div_iff {σ φ α A w N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w ↔ N = flexEmployment σ φ α A w := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) / w :=
    div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw
  have hm := mpn_pos hα1 hA hN
  have key := mrs_mul_eq (σ := σ) (φ := φ) (α := α) hA hN
  constructor
  · intro h
    rw [h] at key
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) / w := by
      field_simp at key ⊢
      nlinarith [key]
    rw [flexEmployment, ← hNk, Real.rpow_rpow_inv hN.le hk.ne']
  · intro h
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) / w := by
      rw [h, flexEmployment, Real.rpow_inv_rpow hc.le hk.ne']
    rw [hNk] at key
    have hc' : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
    field_simp at key ⊢
    nlinarith [key]

/-- Galí (2015), pp. 100–101: **existence and uniqueness** of the equilibrium employment level
under a wedge `w > 0`. -/
theorem existsUnique_flex {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    ∃! N, 0 < N ∧ mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w :=
  ⟨flexEmployment σ φ α A w, ⟨flexEmployment_pos hα1 hA hw,
    (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw (flexEmployment_pos hα1 hA hw)).2 rfl⟩,
    fun _ ⟨hN, h⟩ => (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h⟩

/-- Galí (2015), p. 101: with no wedge (`w = 1`) the equilibrium level is efficient. -/
theorem flexEmployment_one (σ φ α A : ℝ) :
    flexEmployment σ φ α A 1 = effEmployment σ φ α A := by
  rw [flexEmployment, effEmployment, div_one]

/-- Galí (2015), p. 100: a wedge `w > 1` (e.g. the markup `M`) gives employment **strictly
below** the efficient level, `N(w) < N*`. -/
theorem flexEmployment_lt_eff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 1 < w) :
    flexEmployment σ φ α A w < effEmployment σ φ α A := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  exact Real.rpow_lt_rpow (div_pos hc (by linarith)).le (div_lt_self hc hw) (inv_pos.2 hk)

/-- Galí (2015), §4.2.2, p. 101: a wedge `0 < w < 1` gives employment strictly **above** the
efficient level. -/
theorem eff_lt_flexEmployment {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw0 : 0 < w) (hw : w < 1) :
    effEmployment σ φ α A < flexEmployment σ φ α A w := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  exact Real.rpow_lt_rpow hc.le ((lt_div_iff₀ hw0).2 (by nlinarith)) (inv_pos.2 hk)

/-- Galí (2015), pp. 100–101: the equilibrium level is efficient **iff** there is no wedge. -/
theorem flexEmployment_eq_eff_iff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    flexEmployment σ φ α A w = effEmployment σ φ α A ↔ w = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, flexEmployment_one]⟩
  rcases lt_trichotomy w 1 with hlt | heq | hgt
  · exact absurd h (eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw hlt).ne'
  · exact heq
  · exact absurd h (flexEmployment_lt_eff hσ hφ hα0 hα1 hA hgt).ne

/-- Galí (2015), p. 100: along the symmetric allocation the MRS `A^σ N^{σ(1−α)+φ}` is strictly
increasing in `N`. -/
theorem mrs_sym_strictMonoOn {σ φ α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα1 : α < 1)
    (hA : 0 < A) : StrictMonoOn (fun N => mrs σ φ (A * N ^ (1 - α)) N) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha : (0 : ℝ) < a := ha
  have hb : 0 < b := ha.trans hab
  simp only [mrs]
  have h1 : (A * a ^ (1 - α)) ^ σ < (A * b ^ (1 - α)) ^ σ :=
    Real.rpow_lt_rpow (mul_pos hA (Real.rpow_pos_of_pos ha _)).le
      (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.le hab (by linarith)) hA) hσ
  have h2 : a ^ φ ≤ b ^ φ := Real.rpow_le_rpow ha.le hab.le hφ
  have h3 : 0 < a ^ φ := Real.rpow_pos_of_pos ha _
  have h4 : 0 < (A * b ^ (1 - α)) ^ σ := Real.rpow_pos_of_pos (mul_pos hA
    (Real.rpow_pos_of_pos hb _)) _
  calc (A * a ^ (1 - α)) ^ σ * a ^ φ < (A * b ^ (1 - α)) ^ σ * a ^ φ :=
        mul_lt_mul_of_pos_right h1 h3
    _ ≤ (A * b ^ (1 - α)) ^ σ * b ^ φ := mul_le_mul_of_nonneg_left h2 h4.le

/-- Galí (2015), p. 100: the marginal product of labour is nonincreasing in `N`
(`α ≥ 0`). -/
theorem mpn_antitoneOn {α A : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    AntitoneOn (mpn α A) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (by linarith))
    (mul_pos (by linarith) hA).le

/-- Galí (2015), p. 100, **the book's monotonicity argument**: if `f` (the MRS) is strictly
increasing, `g` (the MPN) nonincreasing and positive, `f a = g a` (efficiency) and
`f b = g b / w` with `w > 1` (markup), then `b < a`. -/
theorem lt_of_wedge {f g : ℝ → ℝ} {a b w : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : StrictMonoOn f (Set.Ioi 0)) (hg : AntitoneOn g (Set.Ioi 0)) (hgb : 0 < g b)
    (hw : 1 < w) (hfa : f a = g a) (hfb : f b = g b / w) : b < a := by
  by_contra hab
  push Not at hab
  have h1 : f a ≤ f b := hf.monotoneOn ha hb hab
  have h2 : g b ≤ g a := hg ha hb hab
  have h3 : g b / w < g b := div_lt_self hgb hw
  linarith

/-- Galí (2015), p. 100: the markup distortion leads to inefficiently low employment **and
output**: `N(M) < N*` and `A N(M)^{1−α} < A N*^{1−α}`. -/
theorem markup_inefficiently_low {σ φ ε α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    flexEmployment σ φ α A (markup ε) < effEmployment σ φ α A ∧
      A * flexEmployment σ φ α A (markup ε) ^ (1 - α)
        < A * effEmployment σ φ α A ^ (1 - α) := by
  have h := flexEmployment_lt_eff (σ := σ) (φ := φ) hσ hφ hα0 hα1 hA (one_lt_markup hε)
  refine ⟨h, mul_lt_mul_of_pos_left (Real.rpow_lt_rpow
    (flexEmployment_pos hα1 hA (markup_pos hε)).le h (by linarith)) hA⟩

/-- Galí (2015), p. 100: the welfare loss of any wedge `w ≠ 1` is **strict**. -/
theorem flex_welfare_lt {σ φ α A Z w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hw : 0 < w) (hw1 : w ≠ 1) :
    symWelfare σ φ α A Z (flexEmployment σ φ α A w)
      < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_lt hσ hφ hα0 hα1 hA hZ (flexEmployment_pos hα1 hA hw)
    fun h => hw1 ((flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw).1 h)

/-! ### The optimal subsidy -/

/-- Galí (2015), p. 101: `M (1 − τ) = 1` **iff** `τ = 1/ε`. -/
theorem wedge_eq_one_iff_subsidy {ε τ : ℝ} (hε : 1 < ε) :
    markup ε * (1 - τ) = 1 ↔ τ = 1 / ε := by
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : ε ≠ 0 := by linarith
  rw [markup]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 101: the subsidy `τ = 1/ε` delivers `M (1 − τ) = 1`. -/
theorem optimal_subsidy {ε : ℝ} (hε : 1 < ε) : markup ε * (1 - 1 / ε) = 1 :=
  (wedge_eq_one_iff_subsidy hε).2 rfl

/-- Galí (2015), p. 101: the flexible-price equilibrium under subsidy `τ < 1` is efficient
**iff** `τ = 1/ε`: the optimal subsidy exists and is unique. -/
theorem flex_efficient_iff_subsidy {σ φ ε α A τ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) :
    flexEmployment σ φ α A (markup ε * (1 - τ)) = effEmployment σ φ α A ↔ τ = 1 / ε := by
  rw [flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA (mul_pos (markup_pos hε) (by linarith)),
    wedge_eq_one_iff_subsidy hε]

/-- Galí (2015), p. 101: the flexible-price equilibrium with subsidy `τ`, i.e. the profit
maximisation of `flex_price_rule` and the household's `W/P = MRS` along the symmetric
allocation, has employment `N(M (1 − τ))`; it is efficient (`N = N*`) **iff** `τ = 1/ε`. -/
theorem flex_equilibrium {σ φ ε α A W τ P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) (hW : 0 < W) (hP : 0 < P)
    (hN : 0 < N)
    (hfirm : ∀ N', 0 < N' → firmProfit ε α A W τ P (A * N ^ (1 - α)) N'
        ≤ firmProfit ε α A W τ P (A * N ^ (1 - α)) N)
    (hls : W / P = mrs σ φ (A * N ^ (1 - α)) N) :
    N = flexEmployment σ φ α A (markup ε * (1 - τ)) ∧
      (N = effEmployment σ φ α A ↔ τ = 1 / ε) := by
  have hrule := (flex_price_rule hε hα0 hα1 hA hP hN).1 hfirm
  have h := flex_mrs hε hα1 hA hN hτ hW hrule hls
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA
    (mul_pos (markup_pos hε) (by linarith)) hN).1 h
  refine ⟨hN', ?_⟩
  rw [hN']
  exact flex_efficient_iff_subsidy hσ hφ hε hα0 hα1 hA hτ

/-! ### Sticky prices: the average markup -/

/-- Galí (2015), p. 101: the economy's average markup
`M_t = P_t / ((1 − τ)(W_t/MPN_t))`. -/
noncomputable def avgMarkup (τ P W mpnv : ℝ) : ℝ := P / ((1 - τ) * (W / mpnv))

/-- Galí (2015), p. 101: with the optimal subsidy `τ = 1/ε`, `M_t = P M/(W/MPN)`. -/
theorem avgMarkup_subsidy {ε P W m : ℝ} (hε : 1 < ε) (hW : 0 < W) (hm : 0 < m) :
    avgMarkup (1 / ε) P W m = P * markup ε / (W / m) := by
  have h1 : (1 : ℝ) - 1 / ε ≠ 0 := by
    have : 1 / ε < 1 := (div_lt_one (by linarith)).2 hε
    linarith
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [avgMarkup, markup]
  field_simp

/-- Galí (2015), p. 101: with the optimal subsidy and `W/P = MRS`,
`MRS = MPN · M/M_t`. -/
theorem mrs_eq_avgMarkup {ε P W m σ φ C N : ℝ} (hε : 1 < ε) (hP : 0 < P) (hW : 0 < W)
    (hm : 0 < m) (hls : W / P = mrs σ φ C N) :
    mrs σ φ C N = m * markup ε / avgMarkup (1 / ε) P W m := by
  have hM := markup_pos hε
  rw [avgMarkup_subsidy hε hW hm, ← hls]
  field_simp

/-- Galí (2015), p. 101: under the optimal subsidy, the efficiency condition (3) `MRS = MPN`
holds **iff** the average markup equals the frictionless markup, `M_t = M`. -/
theorem foc_iff_avgMarkup {ε P W m σ φ C N : ℝ} (hε : 1 < ε) (hP : 0 < P) (hW : 0 < W)
    (hm : 0 < m) (hls : W / P = mrs σ φ C N) :
    mrs σ φ C N = m ↔ avgMarkup (1 / ε) P W m = markup ε := by
  have hM := markup_pos hε
  have hMt : 0 < avgMarkup (1 / ε) P W m := by
    rw [avgMarkup_subsidy hε hW hm]
    exact div_pos (mul_pos hP hM) (div_pos hW hm)
  rw [mrs_eq_avgMarkup hε hP hW hm hls, div_eq_iff hMt.ne']
  constructor
  · intro h
    exact (mul_left_cancel₀ hm.ne' h).symm
  · intro h
    rw [h]

/-- Galí (2015), p. 101: under the optimal subsidy, along the symmetric allocation, employment
is `N(M_t/M)`; it is strictly below `N*` iff `M_t > M`, equal iff `M_t = M`, and strictly above
iff `M_t < M`. -/
theorem employment_avgMarkup {σ φ ε α A P W N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hP : 0 < P) (hW : 0 < W) (hN : 0 < N)
    (hls : W / P = mrs σ φ (A * N ^ (1 - α)) N) :
    N = flexEmployment σ φ α A (avgMarkup (1 / ε) P W (mpn α A N) / markup ε) ∧
      (N < effEmployment σ φ α A ↔ markup ε < avgMarkup (1 / ε) P W (mpn α A N)) ∧
      (N = effEmployment σ φ α A ↔ avgMarkup (1 / ε) P W (mpn α A N) = markup ε) ∧
      (effEmployment σ φ α A < N ↔ avgMarkup (1 / ε) P W (mpn α A N) < markup ε) := by
  have hm := mpn_pos hα1 hA hN
  have hM := markup_pos hε
  set Mt := avgMarkup (1 / ε) P W (mpn α A N) with hMtdef
  have hMt : 0 < Mt := by
    rw [hMtdef, avgMarkup_subsidy hε hW hm]
    exact div_pos (mul_pos hP hM) (div_pos hW hm)
  have hw : 0 < Mt / markup ε := div_pos hMt hM
  have h := mrs_eq_avgMarkup hε hP hW hm hls
  rw [← hMtdef] at h
  have h' : mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / (Mt / markup ε) := by
    rw [h]
    field_simp
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h'
  have e1 : Mt / markup ε = 1 ↔ Mt = markup ε := div_eq_one_iff_eq hM.ne'
  have e2 : 1 < Mt / markup ε ↔ markup ε < Mt := one_lt_div hM
  have e3 : Mt / markup ε < 1 ↔ Mt < markup ε := div_lt_one hM
  refine ⟨hN', ?_, ?_, ?_⟩
  · rw [← e2, hN']
    constructor
    · intro hlt
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hl | he
      · exact absurd hlt (eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw hl).not_gt
      · rw [he, flexEmployment_one] at hlt
        exact lt_irrefl _ hlt
    · exact flexEmployment_lt_eff hσ hφ hα0 hα1 hA
  · rw [← e1, hN', flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw]
  · rw [← e3, hN']
    constructor
    · intro hlt
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hl | he
      · exact absurd hlt (flexEmployment_lt_eff hσ hφ hα0 hα1 hA hl).not_gt
      · rw [← he, flexEmployment_one] at hlt
        exact lt_irrefl _ hlt
    · exact eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw

/-! ### Sticky prices: relative-price distortions -/

namespace Dispersion

open Gali.MonetaryPolicyDesign.Efficient.Goods

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

/-- Galí (2015), p. 102: labour employed by firm `i` when it charges `P(i)`: demand
`C(i) = (P(i)/P)^{−ε} C` produced with `C(i) = A N(i)^{1−α}`, so
`N(i) = ((P(i)/P)^{−ε} C/A)^{1/(1−α)}`. -/
noncomputable def labourDemand (ε α A Pbar C : ℝ) (P : G → ℝ) (i : G) : ℝ :=
  ((P i / Pbar) ^ (-ε) * C / A) ^ (1 - α)⁻¹

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: firm `i`'s output is its demand, `A N(i)^{1−α} = (P(i)/P)^{−ε} C`. -/
theorem goodsOutput_labourDemand {ε α A Pbar C : ℝ} (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) (i : G) :
    goodsOutput A α (labourDemand ε α A Pbar C P) i = (P i / Pbar) ^ (-ε) * C := by
  have hx : 0 ≤ (P i / Pbar) ^ (-ε) * C / A :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (div_pos (hP i) hPbar).le _) hC.le) hA.le
  rw [goodsOutput, labourDemand, Real.rpow_inv_rpow hx (by linarith)]
  field_simp

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: different prices mean different quantities: if two firms produce the
same output then they charge the same price. -/
theorem price_eq_of_output_eq {ε α A Pbar C : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) {i j : G}
    (h : goodsOutput A α (labourDemand ε α A Pbar C P) i
      = goodsOutput A α (labourDemand ε α A Pbar C P) j) : P i = P j := by
  rw [goodsOutput_labourDemand hα1 hA hPbar hC hP, goodsOutput_labourDemand hα1 hA hPbar hC hP]
    at h
  have h1 : (P i / Pbar) ^ (-ε) = (P j / Pbar) ^ (-ε) := mul_right_cancel₀ hC.ne' h
  have hne : -ε ≠ 0 := by linarith
  have h2 : P i / Pbar = P j / Pbar := by
    rw [← Real.rpow_rpow_inv (div_pos (hP i) hPbar).le hne,
      ← Real.rpow_rpow_inv (div_pos (hP j) hPbar).le hne, h1]
  field_simp at h2
  exact h2

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: different prices mean different employment: if two firms employ the
same labour then they charge the same price. -/
theorem price_eq_of_labour_eq {ε α A Pbar C : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) {i j : G}
    (h : labourDemand ε α A Pbar C P i = labourDemand ε α A Pbar C P j) : P i = P j :=
  price_eq_of_output_eq hε hα1 hA hPbar hC hP (by rw [goodsOutput, goodsOutput, h])

/-- Galí (2015), p. 102: if relative prices are **not** all equal (no constant `c` with
`P(i) = c` a.e.) then the induced allocation violates both efficiency conditions (1) and (2):
neither `C(i)` nor `N(i)` is a.e. constant. -/
theorem dispersion_violates_symmetry [IsProbabilityMeasure μ] {ε α A Pbar C : ℝ} (hε : 1 < ε)
    (hα1 : α < 1) (hA : 0 < A) (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ}
    (hP : ∀ i, 0 < P i) (hdisp : ¬ ∃ c, ∀ᵐ i ∂μ, P i = c) :
    (¬ ∃ c, ∀ᵐ i ∂μ, goodsOutput A α (labourDemand ε α A Pbar C P) i = c) ∧
      ¬ ∃ c, ∀ᵐ i ∂μ, labourDemand ε α A Pbar C P i = c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨i₀, hi₀⟩ := hc.exists
    refine hdisp ⟨P i₀, ?_⟩
    filter_upwards [hc] with i hi
    exact price_eq_of_output_eq hε hα1 hA hPbar hC hP (hi.trans hi₀.symm)
  · rintro ⟨c, hc⟩
    obtain ⟨i₀, hi₀⟩ := hc.exists
    refine hdisp ⟨P i₀, ?_⟩
    filter_upwards [hc] with i hi
    exact price_eq_of_labour_eq hε hα1 hA hPbar hC hP (hi.trans hi₀.symm)

/-- Galí (2015), p. 102, **strict welfare loss from price dispersion**: if relative prices are
not all equal, the induced (feasible) allocation is strictly worse than the symmetric allocation
with the same total employment, and strictly worse than the efficient allocation. -/
theorem dispersion_welfare_loss [IsProbabilityMeasure μ] {σ φ ε α A Z Pbar C : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i)
    (hfeas : Feasible μ (labourDemand ε α A Pbar C P)) (hdisp : ¬ ∃ c, ∀ᵐ i ∂μ, P i = c) :
    welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)
        < symWelfare σ φ α A Z (∫ i, labourDemand ε α A Pbar C P i ∂μ) ∧
      welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)
        < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  have hns : ¬ ∀ᵐ i ∂μ, labourDemand ε α A Pbar C P i = ∫ j, labourDemand ε α A Pbar C P j ∂μ :=
    fun h => (dispersion_violates_symmetry hε hα1 hA hPbar hC hP hdisp).2 ⟨_, h⟩
  exact ⟨welfare_lt_symWelfare hε hα0 hα1 hA hZ hfeas hns,
    welfare_lt_of_not_symmetric hσ hφ hε hα0 hα1 hA hZ hfeas hns⟩

/-- Galí (2015), p. 102: attaining the efficient allocation **requires** equal prices: if the
allocation induced by prices `P(·)` is optimal, then `P(i)` is a.e. constant. -/
theorem prices_equal_of_optimal [IsProbabilityMeasure μ] {σ φ ε α A Z Pbar C : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i)
    (hfeas : Feasible μ (labourDemand ε α A Pbar C P))
    (hopt : ∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n'
      ≤ welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)) :
    ∃ c, ∀ᵐ i ∂μ, P i = c := by
  by_contra hdisp
  have h1 := (dispersion_welfare_loss hσ hφ hε hα0 hα1 hA hZ hPbar hC hP hfeas hdisp).2
  have h2 := hopt _ (feasible_const (μ := μ) (effEmployment_pos (σ := σ) (φ := φ) hα1 hA))
  rw [welfare_const hε hα0 hα1 hA (effEmployment_pos hα1 hA)] at h2
  linarith

end Dispersion

end Gali.MonetaryPolicyDesign.Distortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal monetary policy with an efficient natural allocation

Galí (2015), Chapter 4, §4.3, pp. 102–104, eqs. (4)–(5) and `i_t = r^n_t`.

The non-policy block is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (7), p. 104, `κ > 0`) and
the DIS `ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eq. (6), p. 104), stated for an
arbitrary `ExpectationSystem`, so all results hold under perfect foresight and under
uncertainty. The natural rate `r^n` is an arbitrary process.

## Main results

* `zero_equilibrium_iff`: `(ỹ, π) ≡ (0, 0)` is an equilibrium **iff** `i_t = r^n_t` for all
  `t` (eqs. (4), (5) and `i = r^n`, p. 103).
* `infl_zero_of_gap_zero`: (4) ⇒ (5): along an equilibrium with bounded inflation, a closed gap
  implies zero inflation (forward uniqueness, `0 < β < 1`); `gap_zero_of_infl_zero`: (5) ⇒ (4)
  for `κ ≠ 0` (no boundedness needed).
* `divine_coincidence`: along any equilibrium with bounded inflation, `ỹ ≡ 0 ⟺ π ≡ 0`, and
  then `i = r^n`.
* `unbounded_counterexample`: the boundedness requirement cannot be dropped: under perfect
  foresight `ỹ ≡ 0`, `π_t = β^{−t}`, `i_t = r^n_t + β^{−(t+1)}` is an (unbounded) equilibrium.
* `pathLoss_nonneg`, `pathLoss_eq_zero_iff`, `optimal_policy`: for any discounted quadratic
  loss `∑ βᵗ (a ỹ_t² + b π_t²)` with `a, b > 0` (the form of §4.4), the policy `i = r^n`
  attains the minimum (zero) loss, state by state and in expectation, and any equilibrium
  attaining zero loss has `ỹ ≡ π ≡ 0` and `i = r^n`.
* `gap_zero_iff_efficient`: with the optimal subsidy `τ = 1/ε`, natural output is efficient
  output, so `ỹ = log Y − log Yⁿ = 0` iff `Y = A N*^{1−α}` (the link to §§4.1–4.2).
* `no_dispersion_of_price_stability`: in levels, with Calvo pricing and no inherited
  dispersion (`P_{−1}(i) = P_{−1}`, p. 102), a constant price level implies every reset price
  equals the old price level and **all prices stay equal forever** (no relative-price
  distortions).
-/

namespace Gali.MonetaryPolicyDesign.OptimalPolicy

open Filter Topology
open Gali.MonetaryPolicyDesign.Efficient Gali.MonetaryPolicyDesign.Distortions

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), p. 103: an equilibrium of the non-policy block given the interest-rate path
`i`: the NKPC (7) and the DIS (6). -/
def Equilibrium (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn

/-- Galí (2015), eqs. (4)–(5) and `i_t = r^n_t`, p. 103: the optimal outcome `ỹ ≡ 0`,
`π ≡ 0` is an equilibrium **iff** the nominal rate tracks the natural rate, `i_t = r^n_t` for
all `t` (`σ ≠ 0`). -/
theorem zero_equilibrium_iff {β σ κ : ℝ} (hσ : σ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn 0 0 i ↔ ∀ t, i t = rn t := by
  constructor
  · rintro ⟨-, hd⟩ t
    have h := hd t
    simp only [Pi.zero_apply, map_zero, zero_sub, sub_zero] at h
    have h2 : σ⁻¹ • (i t - rn t) = 0 := by
      have := congrArg Neg.neg h
      simp only [neg_zero, neg_neg] at this
      exact this.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (inv_eq_zero.1 h3) hσ
    · exact sub_eq_zero.1 h3
  · intro h
    refine ⟨fun t => by simp, fun t => ?_⟩
    simp [h t]

/-- Galí (2015), eqs. (4) ⇒ (5), p. 103: if the output gap is closed at all times and
inflation is bounded, the NKPC (with `|β| < 1`) forces zero inflation at all times. -/
theorem infl_zero_of_gap_zero {β κ : ℝ} (hβ : |β| < 1) {infl : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ 0 infl) (hb : BoundedProc infl) : infl = 0 := by
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  refine 𝔼.forward_unique hβ (u := 0) (fun t => ?_) h0 hb ⟨0, fun _ _ => by simp⟩
  rw [hp t]
  simp

/-- Galí (2015), eqs. (5) ⇒ (4), p. 103: if inflation is zero at all times, the NKPC (with
`κ ≠ 0`) forces a closed output gap (no boundedness needed). -/
theorem gap_zero_of_infl_zero {β κ : ℝ} (hκ : κ ≠ 0) {ygap : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap 0) : ygap = 0 := by
  funext t
  have h := hp t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at h
  rcases smul_eq_zero.1 h.symm with h1 | h1
  · exact absurd h1 hκ
  · exact h1

/-- Galí (2015), p. 103, **the divine coincidence**: along any equilibrium with bounded
inflation (`|β| < 1`, `κ ≠ 0`, `σ ≠ 0`), the output gap is closed at all times **iff**
inflation is zero at all times; and in that case `i_t = r^n_t` for all `t`. -/
theorem divine_coincidence {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : BoundedProc infl) :
    (ygap = 0 ↔ infl = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) := by
  have hiff : ygap = 0 ↔ infl = 0 := by
    constructor
    · intro hy
      subst hy
      exact infl_zero_of_gap_zero 𝔼 hβ heq.1 hb
    · intro hπ
      subst hπ
      exact gap_zero_of_infl_zero 𝔼 hκ heq.1
  refine ⟨hiff, fun hy => ?_⟩
  have hπ := hiff.1 hy
  subst hy
  subst hπ
  exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-- Galí (2015), p. 103: the optimal policy (4)–(5) in the form "price stability implies an
efficient level of output and vice versa": for a bounded equilibrium, `ỹ ≡ 0`, `π ≡ 0` and
`(ỹ, π) ≡ 0` are equivalent, and each forces `i = r^n`; conversely `i = r^n` makes
`(ỹ, π) ≡ 0` an equilibrium. -/
theorem optimal_policy_characterisation {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : BoundedProc infl) :
    (ygap = 0 ↔ ygap = 0 ∧ infl = 0) ∧ (infl = 0 ↔ ygap = 0 ∧ infl = 0) ∧
      (ygap = 0 ∧ infl = 0 → ∀ t, i t = rn t) ∧
      ((∀ t, i t = rn t) → Equilibrium 𝔼 β σ κ rn 0 0 i) := by
  obtain ⟨hiff, hi⟩ := divine_coincidence 𝔼 hβ hσ hκ heq hb
  exact ⟨⟨fun h => ⟨h, hiff.1 h⟩, fun h => h.1⟩, ⟨fun h => ⟨hiff.2 h, h⟩, fun h => h.2⟩,
    fun h => hi h.1, (zero_equilibrium_iff 𝔼 hσ rn i).2⟩

/-- Galí (2015), p. 103 (precision): boundedness cannot be dropped from (4) ⇒ (5). Under
perfect foresight with `0 < β < 1`, `ỹ ≡ 0`, `π_t = β^{−t}` and `i_t = r^n_t + β^{−(t+1)}`
solve the NKPC and the DIS, yet inflation is never zero (and is unbounded). -/
theorem unbounded_counterexample {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (rn : ℕ → Unit → ℝ) :
    Equilibrium perfectForesight β σ κ rn 0 (fun t _ => (β ^ t)⁻¹)
        (fun t u => rn t u + (β ^ (t + 1))⁻¹) ∧
      (∀ t u, (fun t (_ : Unit) => (β ^ t)⁻¹) t u ≠ 0) ∧
      ¬ BoundedProc (fun t (_ : Unit) => (β ^ t)⁻¹) := by
  refine ⟨⟨fun t => funext fun u => ?_, fun t => funext fun u => ?_⟩, fun t u => ?_, ?_⟩
  · simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, mul_zero, add_zero, pow_succ, mul_inv]
    field_simp
  · simp only [perfectForesight, LinearMap.id_apply, Pi.zero_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · exact inv_ne_zero (pow_ne_zero _ hβ0.ne')
  · rintro ⟨M, hM⟩
    have hlim : Tendsto (fun t : ℕ => (β ^ t)⁻¹) atTop atTop := by
      have h := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.2 hβ1)
      simpa [inv_pow] using h
    obtain ⟨t, ht⟩ := (hlim.eventually_gt_atTop M).exists
    have := hM t ()
    rw [abs_of_pos (inv_pos.2 (pow_pos hβ0 t))] at this
    linarith

/-! ### The loss function is minimised by the optimal policy -/

/-- Galí (2015), §4.3 and §4.4 (p. 111): the discounted quadratic loss along a state `ω`,
`∑ₜ βᵗ (a ỹ_t² + b π_t²)`. -/
noncomputable def pathLoss (a b β : ℝ) (ygap infl : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2)

omit 𝔼 in
/-- Galí (2015), p. 111: for bounded processes and `0 ≤ β < 1`, the loss series converges. -/
theorem pathLoss_summable {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ygap infl : ℕ → Ω → ℝ} (hy : BoundedProc ygap) (hπ : BoundedProc infl) (ω : Ω) :
    Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2) := by
  obtain ⟨M₁, hM₁⟩ := hy
  obtain ⟨M₂, hM₂⟩ := hπ
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _))))
    (fun t => mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₁ t ω)).1 (abs_le.1 (hM₁ t ω)).2) ha)
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₂ t ω)).1 (abs_le.1 (hM₂ t ω)).2) hb))
      (pow_nonneg hβ0 t))
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (a * M₁ ^ 2 + b * M₂ ^ 2))

omit 𝔼 in
/-- Galí (2015), p. 111: the loss is nonnegative (`a, b, β ≥ 0`). -/
theorem pathLoss_nonneg {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β)
    (ygap infl : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ pathLoss a b β ygap infl ω :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _)))

omit 𝔼 in
/-- Galí (2015), p. 103: the outcome `ỹ ≡ π ≡ 0` has zero loss. -/
theorem pathLoss_zero (a b β : ℝ) (ω : Ω) : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 ω = 0 := by
  simp [pathLoss]

omit 𝔼 in
/-- Galí (2015), p. 103: with `a, b, β > 0` and a summable loss, the loss is zero **iff**
`ỹ_t(ω) = π_t(ω) = 0` for all `t`. -/
theorem pathLoss_eq_zero_iff {a b β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    {ygap infl : ℕ → Ω → ℝ} {ω : Ω}
    (hs : Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2)) :
    pathLoss a b β ygap infl ω = 0 ↔ ∀ t, ygap t ω = 0 ∧ infl t ω = 0 := by
  have hnn : ∀ t, 0 ≤ β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2) := fun t =>
    mul_nonneg (pow_nonneg hβ0.le t)
      (add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg hb.le (sq_nonneg _)))
  rw [pathLoss, ← hs.hasSum_iff, hasSum_zero_iff_of_nonneg hnn]
  constructor
  · intro h t
    have h1 := congrFun h t
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero _ hβ0.ne')
    · have hy := mul_nonneg ha.le (sq_nonneg (ygap t ω))
      have hπ := mul_nonneg hb.le (sq_nonneg (infl t ω))
      have e1 : a * ygap t ω ^ 2 = 0 := by linarith
      have e2 : b * infl t ω ^ 2 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.1
          ((mul_eq_zero.1 e1).resolve_left ha.ne'),
        pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 e2).resolve_left hb.ne')⟩
  · intro h
    funext t
    simp [(h t).1, (h t).2]

/-- Galí (2015), §4.3, pp. 102–103, **the optimal policy**: for any loss `∑ βᵗ (a ỹ² + b π²)`
with `a, b > 0`, `0 < β < 1`: (i) every outcome has nonnegative loss in every state and in
expectation `E_0`; (ii) the rule `i = r^n` supports `ỹ ≡ π ≡ 0`, with zero loss; (iii) any
bounded equilibrium with zero loss in every state has `ỹ ≡ π ≡ 0` and `i = r^n`. -/
theorem optimal_policy {a b β σ κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (rn : ℕ → Ω → ℝ) :
    (∀ ygap infl : ℕ → Ω → ℝ, (∀ ω, 0 ≤ pathLoss a b β ygap infl ω) ∧
        ∀ ω, 𝔼.E 0 (pathLoss a b β (0 : ℕ → Ω → ℝ) 0) ω
          ≤ 𝔼.E 0 (pathLoss a b β ygap infl) ω) ∧
      Equilibrium 𝔼 β σ κ rn 0 0 rn ∧
      ∀ ygap infl i : ℕ → Ω → ℝ, Equilibrium 𝔼 β σ κ rn ygap infl i →
        BoundedProc ygap → BoundedProc infl → (∀ ω, pathLoss a b β ygap infl ω = 0) →
        ygap = 0 ∧ infl = 0 ∧ ∀ t, i t = rn t := by
  refine ⟨fun ygap infl => ⟨pathLoss_nonneg ha.le hb.le hβ0.le ygap infl, fun ω => ?_⟩,
    (zero_equilibrium_iff 𝔼 hσ rn rn).2 fun _ => rfl, ?_⟩
  · have h0 : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 = fun _ => (0 : ℝ) :=
      funext fun ω => pathLoss_zero a b β ω
    have := 𝔼.mono 0 (pathLoss_nonneg ha.le hb.le hβ0.le ygap infl) ω
    rw [h0]
    simpa [𝔼.const] using this
  · intro ygap infl i heq hy hπ hzero
    have hall : ∀ t ω, ygap t ω = 0 ∧ infl t ω = 0 := fun t ω =>
      ((pathLoss_eq_zero_iff ha hb hβ0
        (pathLoss_summable ha.le hb.le hβ0.le hβ1 hy hπ ω)).1 (hzero ω)) t
    have hy0 : ygap = 0 := funext fun t => funext fun ω => (hall t ω).1
    have hπ0 : infl = 0 := funext fun t => funext fun ω => (hall t ω).2
    refine ⟨hy0, hπ0, ?_⟩
    subst hy0
    subst hπ0
    exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-! ### Links to the efficient allocation and to price stability in levels -/

/-- Galí (2015), §4.3, p. 102: with the optimal subsidy `τ = 1/ε` the natural (flexible-price)
level of output `Yⁿ = A N(M(1 − τ))^{1−α}` is the efficient level, so the output gap
`ỹ = log Y − log Yⁿ` is zero **iff** `Y = A N*^{1−α}` (efficient output). -/
theorem gap_zero_iff_efficient {σ φ ε α A Y : ℝ} (hε : 1 < ε) (hA : 0 < A) (hα1 : α < 1)
    (hY : 0 < Y) :
    Real.log Y - Real.log (A * flexEmployment σ φ α A (markup ε * (1 - 1 / ε)) ^ (1 - α)) = 0 ↔
      Y = A * effEmployment σ φ α A ^ (1 - α) := by
  rw [optimal_subsidy hε, flexEmployment_one, sub_eq_zero]
  have hYe : 0 < A * effEmployment σ φ α A ^ (1 - α) :=
    mul_pos hA (Real.rpow_pos_of_pos (effEmployment_pos hα1 hA) _)
  exact ⟨fun h => Real.log_injOn_pos hY hYe h, fun h => by rw [h]⟩

omit 𝔼 in
/-- Galí (2015), p. 102, **price stability in levels**: Calvo pricing, where each firm either
keeps its price or resets it to the common `P*_t`, with the price index law
`P_t^{1−ε} = θ P_{t−1}^{1−ε} + (1 − θ) P*_t^{1−ε}` (`0 ≤ θ < 1`, `ε ≠ 1`) and no inherited
dispersion (`P_{−1}(i) = P_{−1}`; date `0` here is the book's `−1`). If the price level is
constant, then every reset price equals the old price level, `P*_t = P_{t−1}`, and all
prices stay equal to `P_{−1}` forever: no relative-price distortions emerge. -/
theorem no_dispersion_of_price_stability {G : Type*} {ε θ : ℝ} (hε : ε ≠ 1) (hθ : θ < 1)
    {Pl Pstar : ℕ → ℝ} {Pi : ℕ → G → ℝ} (hPl : ∀ t, 0 < Pl t) (hPs : ∀ t, 0 < Pstar t)
    (hlaw : ∀ t, Pl (t + 1) ^ (1 - ε) = θ * Pl t ^ (1 - ε) + (1 - θ) * Pstar (t + 1) ^ (1 - ε))
    (hfirm : ∀ t i, Pi (t + 1) i = Pi t i ∨ Pi (t + 1) i = Pstar (t + 1))
    (hinit : ∀ i, Pi 0 i = Pl 0) (hstab : ∀ t, Pl (t + 1) = Pl t) :
    (∀ t, Pl t = Pl 0) ∧ (∀ t, Pstar (t + 1) = Pl t) ∧ ∀ t i, Pi t i = Pl 0 := by
  have hconst : ∀ t, Pl t = Pl 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hstab t, ih]
  have hne : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hreset : ∀ t, Pstar (t + 1) = Pl t := by
    intro t
    have h := hlaw t
    rw [hstab t] at h
    have h1 : Pstar (t + 1) ^ (1 - ε) = Pl t ^ (1 - ε) := by
      have h2 : (1 - θ) * Pstar (t + 1) ^ (1 - ε) = (1 - θ) * Pl t ^ (1 - ε) := by linarith
      exact mul_left_cancel₀ (by linarith) h2
    rw [← Real.rpow_rpow_inv (hPs (t + 1)).le hne, h1, Real.rpow_rpow_inv (hPl t).le hne]
  refine ⟨hconst, hreset, fun t => ?_⟩
  induction t with
  | zero => exact hinit
  | succ t ih =>
    intro i
    rcases hfirm t i with h | h
    · rw [h, ih i]
    · rw [h, hreset t, hconst t]

end Gali.MonetaryPolicyDesign.OptimalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An exogenous interest-rate rule

Galí (2015), Chapter 4, §4.3.1.1, pp. 104–105. The non-policy block of the basic
New Keynesian model is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (7)) and the
DIS `ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eq. (6)). Under the
candidate rule (8), `i_t = r^n_t`, the equilibrium conditions are the system (9),
`x_t = A_O E_t x_{t+1}` with `x_t = (ỹ_t, π_t)` and (10)
`A_O = [[1, 1/σ], [κ, β + κ/σ]]`.

## Main results

* `equilibrium_iff_solves`: the NKPC, the DIS and the rule (8) hold iff `(ỹ, π)`
  solves (9) and `i = r^n`.
* `zero_equilibrium`: `ỹ = π = 0`, `i = r^n` is an equilibrium (p. 105).
* `det_sub_AO`, `charPolyO`: the characteristic polynomial
  `p(λ) = λ² − (1 + β + κ/σ) λ + β` of `A_O`.
* `eigenvalues_AO`: `A_O` has two real eigenvalues `0 < λ₁ < 1 < λ₂` and no
  other (complex) ones; found by the intermediate value theorem from
  `p(0) = β > 0`, `p(1) = −κ/σ < 0`, `p(1 + β + κ/σ) = β > 0`.
* `not_determinate_AO`: hence the system is indeterminate (Blanchard–Kahn,
  via `determinate_iff`).
* `sunspot_equilibrium`, `exists_second_equilibrium`: an explicit second bounded
  equilibrium, `ỹ_t = λ₂^{−t}`, `π_t = σ (λ₂ − 1) λ₂^{−t}`, `i_t = r^n_t`.
* `equilibrium_not_unique`: next to every bounded equilibrium there is another.
-/

namespace Gali.MonetaryPolicyDesign.RuleExogenous

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), eq. (8), p. 104: the exogenous rule `i_t = r^n_t`. -/
def ExogRule (i rn : ℕ → Ω → ℝ) : Prop := ∀ t, i t = rn t

/-- Galí (2015), §4.3.1.1, p. 104: an equilibrium under rule (8): the DIS (6),
the NKPC (7) and the rule (8). -/
def Equilibrium (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ExogRule i rn

/-- Galí (2015), eq. (10), p. 105: `A_O = [[1, 1/σ], [κ, β + κ/σ]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), eq. (9), p. 104: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the
Chapter 3 project). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the
Chapter 3 project). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), eq. (9), p. 104: given the rule (8), the NKPC and the DIS hold
iff `(ỹ, π)` solves `x_t = A_O E_t x_{t+1}`. -/
theorem nk_iff_solves {β σ κ : ℝ} {rn ygap infl i : ℕ → Ω → ℝ}
    (hrule : ExogRule i rn) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO]
      linear_combination e
    · simp [stack, AO]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [hrule t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- Galí (2015), eqs. (8)–(10), pp. 104–105: `(ỹ, π, i)` is an equilibrium under
rule (8) iff `x_t = (ỹ_t, π_t)` solves `x_t = A_O E_t x_{t+1}` and `i = r^n`. -/
theorem equilibrium_iff_solves {β σ κ : ℝ} {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ rn ygap infl i ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) ∧ i = rn := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hr).mp ⟨hp, hd⟩, funext hr⟩
  · rintro ⟨hs, rfl⟩
    have hr : ExogRule i i := fun _ => rfl
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 105: `ỹ_t = π_t = 0` for all `t`, with `i_t = r^n_t`, is an
equilibrium under rule (8). -/
theorem zero_equilibrium (β σ κ : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun _ => rfl⟩ <;> simp

/-- The trace of `A_O`: `tr A_O = 1 + β + κ/σ` (Galí 2015, eq. (10), p. 105). -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ / σ := by
  simp [tr2, AO]
  ring

/-- The determinant of `A_O`: `det A_O = β` (Galí 2015, eq. (10), p. 105). -/
theorem det2_AO {β σ κ : ℝ} (hσ : σ ≠ 0) : det2 (AO β σ κ) = β := by
  simp [det2, AO]
  field_simp
  ring

/-- Galí (2015), p. 105: the characteristic polynomial of `A_O`,
`p(λ) = λ² − (1 + β + κ/σ) λ + β`. -/
noncomputable def charPolyO (β σ κ x : ℝ) : ℝ := x ^ 2 - (1 + β + κ / σ) * x + β

/-- Galí (2015), p. 105: `det (λ I − A_O) = p(λ)`, so the eigenvalues of `A_O`
are the roots of `charPolyO`. -/
theorem det_sub_AO {β σ κ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    Matrix.det (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = charPolyO β σ κ x := by
  rw [Matrix.det_fin_two]
  simp [AO, charPolyO]
  field_simp
  ring

/-- Galí (2015), p. 105: `p(0) = β`. -/
theorem charPolyO_zero (β σ κ : ℝ) : charPolyO β σ κ 0 = β := by
  simp [charPolyO]

/-- Galí (2015), p. 105: `p(1) = −κ/σ`. -/
theorem charPolyO_one (β σ κ : ℝ) : charPolyO β σ κ 1 = -(κ / σ) := by
  simp [charPolyO]
  ring

/-- Galí (2015), p. 105: `p(1 + β + κ/σ) = β`. -/
theorem charPolyO_trace (β σ κ : ℝ) : charPolyO β σ κ (1 + β + κ / σ) = β := by
  simp [charPolyO]
  ring

/-- The characteristic polynomial is continuous. -/
theorem continuous_charPolyO (β σ κ : ℝ) : Continuous (charPolyO β σ κ) := by
  unfold charPolyO
  fun_prop

/-- Galí (2015), p. 105 (Exercise 4.1(a)): for `σ, κ, β > 0`, `p` has a root in
`(0, 1)` (intermediate value theorem: `p(0) > 0 > p(1)`). -/
theorem exists_root_Ioo_zero_one {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ x, 0 < x ∧ x < 1 ∧ charPolyO β σ κ x = 0 := by
  have h : (0 : ℝ) ∈ Set.Ioo (charPolyO β σ κ 1) (charPolyO β σ κ 0) := by
    rw [charPolyO_zero, charPolyO_one]
    exact ⟨by have := div_pos hκ hσ; linarith, hβ⟩
  obtain ⟨x, ⟨hx0, hx1⟩, hx⟩ :=
    intermediate_value_Ioo' zero_le_one (continuous_charPolyO β σ κ).continuousOn h
  exact ⟨x, hx0, hx1, hx⟩

/-- Galí (2015), p. 105 (Exercise 4.1(a)): for `σ, κ, β > 0`, `p` has a root
strictly greater than one (intermediate value theorem on `[1, 1 + β + κ/σ]`). -/
theorem exists_root_gt_one {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ x, 1 < x ∧ charPolyO β σ κ x = 0 := by
  have hT : 1 ≤ 1 + β + κ / σ := by have := div_pos hκ hσ; linarith
  have h : (0 : ℝ) ∈ Set.Ioo (charPolyO β σ κ 1) (charPolyO β σ κ (1 + β + κ / σ)) := by
    rw [charPolyO_trace, charPolyO_one]
    exact ⟨by have := div_pos hκ hσ; linarith, hβ⟩
  obtain ⟨x, ⟨hx1, -⟩, hx⟩ :=
    intermediate_value_Ioo hT (continuous_charPolyO β σ κ).continuousOn h
  exact ⟨x, hx1, hx⟩

/-- **The eigenvalues of `A_O`** (Galí 2015, p. 105; Exercise 4.1(a)): for
`σ, κ, β > 0`, `A_O` has two real eigenvalues `λ₁ ∈ (0, 1)` and `λ₂ > 1`, and
every complex root of its characteristic polynomial `z² − tr A_O z + det A_O`
is one of them. -/
theorem eigenvalues_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 < l₂ ∧
      Matrix.det (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = 0 ∧
      Matrix.det (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = 0 ∧
      ∀ z : ℂ, z ^ 2 - (tr2 (AO β σ κ) : ℂ) * z + (det2 (AO β σ κ) : ℂ) = 0 →
        z = l₁ ∨ z = l₂ := by
  obtain ⟨l₁, h0, h1, hp1⟩ := exists_root_Ioo_zero_one hσ hκ hβ
  obtain ⟨l₂, h2, hp2⟩ := exists_root_gt_one hσ hκ hβ
  refine ⟨l₁, l₂, h0, h1, h2, by rw [det_sub_AO hσ.ne', hp1],
    by rw [det_sub_AO hσ.ne', hp2], fun z hz => ?_⟩
  rw [tr2_AO, det2_AO hσ.ne'] at hz
  unfold charPolyO at hp1 hp2
  set T := 1 + β + κ / σ
  -- Vieta: `l₁ + l₂ = T` and `l₁ l₂ = β`, since `l₁ ≠ l₂`
  have hne : l₁ - l₂ ≠ 0 := by intro h; linarith
  have hsum : l₁ + l₂ = T := by
    have : (l₁ - l₂) * (l₁ + l₂ - T) = 0 := by linear_combination hp1 - hp2
    linarith [(mul_eq_zero.mp this).resolve_left hne]
  have hprod : l₁ * l₂ = β := by linear_combination -hp1 + l₁ * hsum
  have hsumC : ((l₁ : ℂ) + l₂) = (T : ℂ) := by exact_mod_cast hsum
  have hprodC : ((l₁ : ℂ) * l₂) = (β : ℂ) := by exact_mod_cast hprod
  have hf : (z - l₁) * (z - l₂) = 0 := by
    linear_combination hz - z * hsumC + hprodC
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Galí (2015), p. 105: `A_O` fails the Schur–Cohn condition, because
`tr A_O = 1 + det A_O + κ/σ > 1 + det A_O`. -/
theorem not_schurStable_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rintro ⟨-, hT⟩
  rw [tr2_AO, det2_AO hσ.ne'] at hT
  have := div_pos hκ hσ
  have := le_abs_self (1 + β + κ / σ)
  linarith

/-- **Indeterminacy under rule (8)** (Galí 2015, p. 105): for `σ, κ > 0` the
system (9) is not determinate: it has two distinct bounded adapted solutions
for some forcing process (Blanchard–Kahn, via `determinate_iff`). -/
theorem not_determinate_AO [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ 𝔼.Determinate (AO β σ κ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- Galí (2015), p. 105: the self-fulfilling output-gap path `ỹ_t = λ^{−t}`
attached to an eigenvalue `λ` of `A_O` (a deterministic process). -/
noncomputable def sunspotY (l : ℝ) : ℕ → Ω → ℝ := fun t _ => l⁻¹ ^ t

/-- Galí (2015), p. 105: the matching inflation path `π_t = σ (λ − 1) λ^{−t}`
(the eigenvector of `A_O` for `λ` is `(1, σ (λ − 1))`). -/
noncomputable def sunspotPi (σ l : ℝ) : ℕ → Ω → ℝ := fun t _ => σ * (l - 1) * l⁻¹ ^ t

/-- Galí (2015), p. 105: for every nonzero root `λ` of the characteristic
polynomial, `ỹ_t = λ^{−t}`, `π_t = σ (λ − 1) λ^{−t}`, `i_t = r^n_t` is an
equilibrium under rule (8). -/
theorem sunspot_equilibrium {β σ κ l : ℝ} (hσ : σ ≠ 0) (hl : l ≠ 0)
    (hp : charPolyO β σ κ l = 0) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn (sunspotY l) (sunspotPi σ l) rn := by
  have hp' : σ * l ^ 2 - (σ + β * σ + κ) * l + β * σ = 0 := by
    unfold charPolyO at hp
    field_simp at hp
    linear_combination hp
  have h1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  have hs : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  refine ⟨fun t => ?_, fun t => ?_, fun _ => rfl⟩
  · change (fun _ => σ * (l - 1) * l⁻¹ ^ t : Ω → ℝ) =
      β • 𝔼.E t (fun _ => σ * (l - 1) * l⁻¹ ^ (t + 1)) + κ • (fun _ => l⁻¹ ^ t)
    rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    linear_combination l⁻¹ ^ t * l⁻¹ * hp' - l⁻¹ ^ t * (σ * l - σ - κ) * h1
  · change (fun _ => l⁻¹ ^ t : Ω → ℝ) = 𝔼.E t (fun _ => l⁻¹ ^ (t + 1))
      - σ⁻¹ • (rn t - 𝔼.E t (fun _ => σ * (l - 1) * l⁻¹ ^ (t + 1)) - rn t)
    rw [𝔼.const, 𝔼.const]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    linear_combination (-(l⁻¹ ^ t)) * h1 - l⁻¹ ^ t * l⁻¹ * (l - 1) * hs

/-- **A second bounded equilibrium** (Galí 2015, p. 105): for `σ, κ, β > 0`
there is an equilibrium under rule (8) with bounded adapted output gap and
inflation that is not `ỹ = π = 0`, namely the sunspot path of the eigenvalue
`λ₂ > 1`: `ỹ_t = λ₂^{−t}`, `π_t = σ (λ₂ − 1) λ₂^{−t}`, `i_t = r^n_t`. -/
theorem exists_second_equilibrium [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, Equilibrium 𝔼 β σ κ rn ygap infl rn ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      ygap ≠ 0 ∧ infl ≠ 0 := by
  obtain ⟨l, hl1, hp⟩ := exists_root_gt_one hσ hκ hβ
  have hl0 : 0 < l := by linarith
  have hpow : ∀ t : ℕ, 0 < l⁻¹ ^ t ∧ l⁻¹ ^ t ≤ 1 := fun t =>
    ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)⟩
  have hc : 0 < σ * (l - 1) := mul_pos hσ (by linarith)
  refine ⟨sunspotY l, sunspotPi σ l, sunspot_equilibrium 𝔼 hσ.ne' hl0.ne' hp rn,
    fun t => 𝔼.const t _, fun t => 𝔼.const t _, ⟨1, fun t _ => ?_⟩,
    ⟨σ * (l - 1), fun t _ => ?_⟩, fun h => ?_, fun h => ?_⟩
  · simp only [sunspotY]
    rw [abs_of_pos (hpow t).1]
    exact (hpow t).2
  · simp only [sunspotPi]
    rw [abs_of_pos (mul_pos hc (hpow t).1)]
    exact mul_le_of_le_one_right hc.le (hpow t).2
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [sunspotY] at this
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp only [sunspotPi, pow_zero, mul_one, Pi.zero_apply] at this
    linarith

/-- **Multiplicity around every equilibrium** (Galí 2015, p. 105): for `σ, κ > 0`,
next to any equilibrium under rule (8) with bounded adapted output gap and
inflation there is another one with a different output gap or inflation path. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {rn ygap infl i : ℕ → Ω → ℝ} (he : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl', Equilibrium 𝔼 β σ κ rn ygap' infl' i ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  obtain ⟨hx, hi⟩ := (equilibrium_iff_solves 𝔼).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    (equilibrium_iff_solves 𝔼).mpr ⟨hst ▸ hy, hi⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

end Gali.MonetaryPolicyDesign.RuleExogenous

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An interest-rate rule with an endogenous component: the Taylor principle

Galí (2015), Chapter 4, §4.3.1.2, pp. 105–107. With the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eqs. (6)–(7), stated in
`RuleExogenous`), the rule (11) `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` gives the system
(12) `x_t = A_T E_t x_{t+1}` with (13)
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`, `Ω = 1/(σ + φ_y + κφ_π)`.

## Main results

* `equilibrium_iff_solves`: the NKPC, DIS and rule (11) hold iff `(ỹ, π)` solves (12).
* `schurStable_AT_iff`, `determinate_iff_14` (Bullard–Mitra): for `φ_π, φ_y ≥ 0`
  the system is determinate iff (14) `κ (φ_π − 1) + (1 − β) φ_y > 0`.
* `equilibrium_iff_zero`: under (14), `ỹ = π = 0`, `i = r^n` is THE unique
  equilibrium with bounded adapted output gap and inflation.
* `exists_nonzero_equilibrium`: without (14) there is a bounded equilibrium
  other than `ỹ = π = 0`.
* `tendsto_gap_of_tendsto_infl`, `tendsto_rate_of_tendsto_infl`: eq. (15): after
  a permanent change of inflation to `π̄` the NKPC forces `ỹ → (1 − β) π̄/κ`
  and the rule gives `i_t − r^n_t → (φ_π + φ_y (1 − β)/κ) π̄`.
* `taylorPrinciple_iff`: (14) holds iff the long-run response (15) exceeds one;
  `tendsto_realRate_of_tendsto_infl`: then the real rate eventually rises.
-/

namespace Gali.MonetaryPolicyDesign.RuleTaylorPrinciple

open Filter Topology Gali.MonetaryPolicyDesign.RuleExogenous

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (11), p. 105: the rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`. -/
def TaylorRule (φπ φy : ℝ) (i rn infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • infl t + φy • ygap t

/-- Galí (2015), §4.3.1.2, p. 105: an equilibrium under rule (11): the DIS (6),
the NKPC (7) and the rule (11). -/
def Equilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ TaylorRule φπ φy i rn infl ygap

/-- Galí (2015), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105:
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eqs. (12)–(13), p. 105: given rule (11), the NKPC and the DIS
hold iff `x_t = (ỹ_t, π_t)` solves `x_t = A_T E_t x_{t+1}` (for `σ ≠ 0` and
`σ + φ_y + κ φ_π ≠ 0`). Adapted from the Chapter 3 project. -/
theorem nk_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : TaylorRule φπ φy i rn infl ygap) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    -- the structural form `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1}`
    have s : (σ + φy) * ygap t ω + φπ * infl t ω
        = σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
      linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AT, omega]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AT, omega]
      field_simp
      linear_combination κ * s + (σ + φy) * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, omega] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      have r := congrFun (hrule t) ω
      simp [stack, AT, omega] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      have s : (σ + φy) * ygap t ω + φπ * infl t ω
          = σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
        apply mul_left_cancel₀ hS
        linear_combination (σ + φy) * e0 + φπ * e1
      rw [r]
      linear_combination σ⁻¹ * s - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eqs. (11)–(13), p. 105: `(ỹ, π, i)` is an equilibrium under
rule (11) iff `(ỹ, π)` solves (12) and `i` is given by the rule. -/
theorem equilibrium_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) ∧ TaylorRule φπ φy i rn infl ygap := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hσ hS hr).mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hσ hS hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 106: `ỹ = π = 0`, `i = r^n` is always an equilibrium under
rule (11). -/
theorem zero_equilibrium (β σ κ φπ φy : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ φπ φy rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> simp

/-- The trace of `A_T`: `(σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)` (Galí 2015,
eq. (13), p. 105). Restated from the Chapter 3 project. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The determinant of `A_T`: `σ β/(σ + φ_y + κ φ_π)` (Galí 2015, eq. (13),
p. 105). Restated from the Chapter 3 project. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Bullard–Mitra** (Galí 2015, eq. (14), p. 106): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle iff `κ (φ_π − 1) + (1 − β) φ_y > 0`. Restated from the Chapter 3 project. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), eq. (14), p. 106: under rule (11) with `φ_π, φ_y ≥ 0` the system
(12) is determinate (at most one bounded adapted solution for every forcing)
iff `κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
theorem determinate_iff_14 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- **Implementation of the optimal policy** (Galí 2015, p. 106): under (14),
`ỹ = π = 0` and `i = r^n` is the unique equilibrium under rule (11) with bounded
adapted output gap and inflation. -/
theorem equilibrium_iff_zero {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔ ygap = 0 ∧ infl = 0 ∧ i = rn := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  constructor
  · intro he
    obtain ⟨hx, hr⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp he
    obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
    have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14) hx h0
      (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
      (boundedVec_stack hba hbb) (boundedVec_stack ⟨0, fun t ω => by simp⟩
        ⟨0, fun t ω => by simp⟩)
    have h1 : ygap = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [hr t, h1, h2]
    simp
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact zero_equilibrium 𝔼 β σ κ φπ φy rn

/-- **Indeterminacy without (14)** (Galí 2015, p. 106): if `φ_π, φ_y ≥ 0` and
`κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, there is an equilibrium under rule (11) with
bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem exists_nonzero_equilibrium [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ 0 ∨ infl ≠ 0) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    fun t => rn t + φπ • y t 1 + φy • y t 0,
    (equilibrium_iff_solves 𝔼 hσ.ne' hS).mpr ⟨hst ▸ hy, fun t => rfl⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The long-run response (15) and the Taylor principle -/

/-- Galí (2015), eq. (15), p. 106: the long-run response of the nominal rate to a
permanent change in inflation, `φ_π + φ_y (1 − β)/κ`. -/
noncomputable def longRunResponse (β κ φπ φy : ℝ) : ℝ := φπ + φy * (1 - β) / κ

/-- Galí (2015), p. 106: the long-run relation implied by (7). If inflation
converges to `π̄` (both `π_t` and `E_t π_{t+1}`, as after a permanent change in
inflation), the NKPC forces the output gap to converge to `(1 − β) π̄/κ`. -/
theorem tendsto_gap_of_tendsto_infl {β κ : ℝ} (hκ : κ ≠ 0) {ygap infl : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap infl) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => ygap t ω) atTop (𝓝 ((1 - β) * pibar / κ)) := by
  have he : (fun t => ygap t ω) = fun t => κ⁻¹ * (infl t ω - β * 𝔼.E t (infl (t + 1)) ω) := by
    funext t
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p
    field_simp
    linear_combination -p
  rw [he]
  have hl := (h1.sub (h2.const_mul β)).const_mul κ⁻¹
  convert hl using 2
  field_simp

/-- **Eq. (15)** (Galí 2015, p. 106): after a permanent change of inflation to `π̄`
(with `r^n` held fixed by measuring `i_t − r^n_t`), rule (11) and the NKPC give
`i_t − r^n_t → (φ_π + φ_y (1 − β)/κ) π̄`. -/
theorem tendsto_rate_of_tendsto_infl {β κ φπ φy : ℝ} (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ ygap infl)
    (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => i t ω - rn t ω) atTop (𝓝 (longRunResponse β κ φπ φy * pibar)) := by
  have he : (fun t => i t ω - rn t ω) = fun t => φπ * infl t ω + φy * ygap t ω := by
    funext t
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at r
    linear_combination r
  rw [he]
  have hl := (h1.const_mul φπ).add ((tendsto_gap_of_tendsto_infl 𝔼 hκ hp ω h1 h2).const_mul φy)
  convert hl using 2
  unfold longRunResponse
  field_simp

/-- **The Taylor principle** (Galí 2015, p. 107): for `κ > 0`, condition (14)
holds iff the long-run response (15) of the nominal rate to inflation is
greater than one. -/
theorem taylorPrinciple_iff {β κ φπ φy : ℝ} (hκ : 0 < κ) :
    0 < κ * (φπ - 1) + (1 - β) * φy ↔ 1 < longRunResponse β κ φπ φy := by
  have h : longRunResponse β κ φπ φy - 1 = (κ * (φπ - 1) + (1 - β) * φy) / κ := by
    unfold longRunResponse
    field_simp
    ring
  rw [← sub_pos (a := longRunResponse β κ φπ φy) (b := 1), h, div_pos_iff_of_pos_right hκ]

/-- Galí (2015), p. 107: the long-run response of the real rate `i_t − E_t π_{t+1}`
(net of `r^n_t`) to a permanent change of inflation to `π̄` is
`(φ_π + φ_y (1 − β)/κ − 1) π̄`. -/
theorem tendsto_realRate_of_tendsto_infl {β κ φπ φy : ℝ} (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ ygap infl)
    (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) atTop
      (𝓝 ((longRunResponse β κ φπ φy - 1) * pibar)) := by
  have hl := (tendsto_rate_of_tendsto_infl 𝔼 hκ hp hr ω h1 h2).sub h2
  convert hl using 2 <;> ring

/-- **The real rate eventually rises** (Galí 2015, p. 107): under (14), after a
permanent increase of inflation to `π̄ > 0` the real rate (net of `r^n_t`) is
eventually positive. -/
theorem realRate_eventually_pos {β κ φπ φy : ℝ} (hκ : 0 < κ)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn ygap infl i : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap infl) (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ}
    (hpi : 0 < pibar) (ω : Ω) (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    ∀ᶠ t in atTop, 0 < i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω := by
  have hpos : 0 < (longRunResponse β κ φπ φy - 1) * pibar :=
    mul_pos (sub_pos.mpr ((taylorPrinciple_iff hκ).mp h14)) hpi
  exact (tendsto_realRate_of_tendsto_infl 𝔼 hκ.ne' hp hr ω h1 h2).eventually
    (lt_mem_nhds hpos)

end Gali.MonetaryPolicyDesign.RuleTaylorPrinciple

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A forward-looking interest-rate rule

Galí (2015), Chapter 4, §4.3.1.3 and §4.3.2, pp. 107–110. With the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (stated in `RuleExogenous`),
the forward-looking rule (16) `i_t = r^n_t + φ_π E_t π_{t+1} + φ_y E_t ỹ_{t+1}`
gives `x_t = A_F E_t x_{t+1}` with

  `A_F = [[1 − φ_y/σ, (1 − φ_π)/σ], [κ (1 − φ_y/σ), β + κ (1 − φ_π)/σ]]`.

**Correction (C4-1).** The book (p. 108) prints the `(2,2)` entry as
`β − κ φ_π/σ`; the correct entry is `β + κ (1 − φ_π)/σ` (`AF_ne_AFprinted`). Conditions
(17)–(18) characterise determinacy for the corrected matrix (`determinate_iff_17_18`),
and the printed matrix gives a different verdict at `σ = κ = 1`, `β = 1/2`,
`φ_π = 3`, `φ_y = 0` (`printed_verdict_differs`).

## Main results

* `equilibrium_iff_solves`: the NKPC, DIS and rule (16) hold iff `(ỹ, π)` solves
  `x_t = A_F E_t x_{t+1}`.
* `schurStable_AF_iff`, `determinate_iff_17_18`: for `σ > 0`, `0 < β < 1`,
  `φ_y ≥ 0`, determinacy holds iff (17) `κ (φ_π − 1) + (1 − β) φ_y > 0` and
  (18) `κ (φ_π − 1) + (1 + β) φ_y < 2σ (1 + β)`.
* `equilibrium_iff_zero`, `exists_nonzero_equilibrium`: under (17)–(18),
  `ỹ = π = 0`, `i = r^n` is the unique bounded equilibrium; otherwise not.
* `fn7_implied`, `abs_det2_AF_lt_one_iff`: footnote 7, the Bullard–Mitra condition
  `φ_y < σ (1 + β⁻¹)` is `|det A_F| < 1` and is implied by (17)–(18).
* `determinate_contemporaneous_phiy_zero`, `determinate_forward_phiy_zero`: p. 110, with
  `φ_y = 0`: `φ_π > 1` for rule (11), `1 < φ_π < 1 + 2σ(1 + β)/κ` for rule (16).
* `boundary_eigenvalue_neg_one`, `not_determinate_at_boundary`: at
  `φ_π = 1 + 2σ(1 + β)/κ` the matrix `A_F` has the eigenvalue `−1` and the
  system is indeterminate, so the book's "no greater than" must be strict (C4-4).
-/

namespace Gali.MonetaryPolicyDesign.RuleForward

open Gali.MonetaryPolicyDesign.RuleExogenous

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (16), p. 108: the forward-looking rule
`i_t = r^n_t + φ_π E_t π_{t+1} + φ_y E_t ỹ_{t+1}`. -/
def ForwardRule (φπ φy : ℝ) (i rn infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • 𝔼.E t (infl (t + 1)) + φy • 𝔼.E t (ygap (t + 1))

/-- Galí (2015), §4.3.1.3, p. 108: an equilibrium under rule (16): the DIS (6),
the NKPC (7) and the rule (16). -/
def Equilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ForwardRule 𝔼 φπ φy i rn infl ygap

/-- Galí (2015), p. 108, **corrected** (C4-1): the system matrix under rule (16),
`A_F = [[1 − φ_y/σ, (1 − φ_π)/σ], [κ (1 − φ_y/σ), β + κ (1 − φ_π)/σ]]`. -/
noncomputable def AF (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - φy / σ, (1 - φπ) / σ; κ * (1 - φy / σ), β + κ * (1 - φπ) / σ]

/-- Galí (2015), p. 108, **as printed**: the `(2,2)` entry is `β − κ φ_π/σ`. -/
noncomputable def AFprinted (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - φy / σ, (1 - φπ) / σ; κ * (1 - φy / σ), β - κ * φπ / σ]

/-- Galí (2015), p. 108: given rule (16), the NKPC and the DIS hold iff
`x_t = (ỹ_t, π_t)` solves `x_t = A_F E_t x_{t+1}`, with the corrected `A_F`. -/
theorem nk_iff_solves {β σ κ φπ φy : ℝ} {rn ygap infl i : ℕ → Ω → ℝ}
    (hrule : ForwardRule 𝔼 φπ φy i rn infl ygap) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AF β σ κ φπ φy) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    rw [r] at e
    fin_cases j
    · simp [stack, AF]
      linear_combination e
    · simp [stack, AF]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AF] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have r := congrFun (hrule t) ω
      simp [stack, AF] at e0
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      rw [r]
      linear_combination e0

/-- Galí (2015), p. 108: `(ỹ, π, i)` is an equilibrium under rule (16) iff
`(ỹ, π)` solves `x_t = A_F E_t x_{t+1}` and `i` is given by the rule. -/
theorem equilibrium_iff_solves {β σ κ φπ φy : ℝ} {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔
      𝔼.Solves (AF β σ κ φπ φy) 0 (stack ygap infl) ∧ ForwardRule 𝔼 φπ φy i rn infl ygap := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hr).mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 108: `ỹ = π = 0`, `i = r^n` is an equilibrium under rule (16). -/
theorem zero_equilibrium (β σ κ φπ φy : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ φπ φy rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> simp

/-- **C4-1** (Galí 2015, p. 108): the printed matrix differs from the system's
matrix whenever `κ ≠ 0` and `σ ≠ 0`; the `(2,2)` entries differ by `κ/σ`. -/
theorem AF_ne_AFprinted {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    AF β σ κ φπ φy ≠ AFprinted β σ κ φπ φy := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp only [AF, AFprinted, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h11
  have : κ / σ = 0 := by linear_combination h11
  exact div_ne_zero hκ hσ this

/-- The `(2,2)` entry of `A_F`: `β + κ (1 − φ_π)/σ` (Galí 2015, p. 108, corrected). -/
theorem AF_one_one (β σ κ φπ φy : ℝ) : AF β σ κ φπ φy 1 1 = β + κ * (1 - φπ) / σ := by
  simp [AF]

/-- The trace of `A_F`: `1 − φ_y/σ + β + κ (1 − φ_π)/σ` (Galí 2015, p. 108). -/
theorem tr2_AF (β σ κ φπ φy : ℝ) :
    tr2 (AF β σ κ φπ φy) = 1 - φy / σ + β + κ * (1 - φπ) / σ := by
  simp [tr2, AF]
  ring

/-- The determinant of `A_F`: `β (1 − φ_y/σ)` (Galí 2015, p. 108). -/
theorem det2_AF (β σ κ φπ φy : ℝ) : det2 (AF β σ κ φπ φy) = β * (1 - φy / σ) := by
  simp [det2, AF]
  ring

/-- Galí (2015), fn. 7, p. 108: for `σ > 0`, `0 < β < 1` and `φ_y ≥ 0`, the
Bullard–Mitra condition `φ_y < σ (1 + β⁻¹)` is exactly `|det A_F| < 1`. -/
theorem abs_det2_AF_lt_one_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) : |det2 (AF β σ κ φπ φy)| < 1 ↔ φy < σ * (1 + β⁻¹) := by
  rw [det2_AF, abs_lt]
  have hD1 : β * (1 - φy / σ) < 1 := by
    have : 0 ≤ φy / σ := div_nonneg hφy hσ.le
    nlinarith
  have key : -1 < β * (1 - φy / σ) ↔ φy < σ * (1 + β⁻¹) := by
    have e : β * (1 - φy / σ) + 1 = β * (σ * (1 + β⁻¹) - φy) / σ := by
      field_simp
      ring
    rw [← sub_pos (a := β * (1 - φy / σ)), sub_neg_eq_add, e,
      div_pos_iff_of_pos_right hσ, mul_pos_iff_of_pos_left hβ0, sub_pos]
  rw [key]
  exact ⟨fun h => h.1, fun h => ⟨h, hD1⟩⟩

/-- **Galí (2015), fn. 7, p. 108**: conditions (17) and (18) imply the third
Bullard–Mitra condition `φ_y < σ (1 + β⁻¹)` (adding them gives
`2β φ_y < 2σ (1 + β)`). -/
theorem fn7_implied {β σ κ φπ φy : ℝ} (hβ0 : 0 < β)
    (h17 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (h18 : κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β)) : φy < σ * (1 + β⁻¹) := by
  have h : β * φy < β * (σ * (1 + β⁻¹)) := by
    have e : β * (σ * (1 + β⁻¹)) = σ * (1 + β) := by field_simp; ring
    rw [e]; linarith
  exact lt_of_mul_lt_mul_left h hβ0.le

/-- **Determinacy conditions (17)–(18)** (Galí 2015, p. 108, for the corrected
`A_F`): for `σ > 0`, `0 < β < 1` and `φ_y ≥ 0`, both eigenvalues of `A_F` lie
inside the unit circle iff `κ (φ_π − 1) + (1 − β) φ_y > 0` and
`κ (φ_π − 1) + (1 + β) φ_y < 2σ (1 + β)`. -/
theorem schurStable_AF_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AF β σ κ φπ φy)) (det2 (AF β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) := by
  have e1 : 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy)
      = (κ * (φπ - 1) + (1 - β) * φy) / σ := by
    rw [tr2_AF, det2_AF]; field_simp; ring
  have e2 : 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy)
      = (2 * σ * (1 + β) - (κ * (φπ - 1) + (1 + β) * φy)) / σ := by
    rw [tr2_AF, det2_AF]; field_simp; ring
  have hT : |tr2 (AF β σ κ φπ φy)| < 1 + det2 (AF β σ κ φπ φy) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) := by
    rw [abs_lt]
    constructor
    · rintro ⟨h1, h2⟩
      have a : 0 < 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy) := by linarith
      have b : 0 < 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy) := by linarith
      rw [e1, div_pos_iff_of_pos_right hσ] at a
      rw [e2, div_pos_iff_of_pos_right hσ] at b
      exact ⟨a, by linarith⟩
    · rintro ⟨h1, h2⟩
      have a : 0 < 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy) := by
        rw [e1]; exact div_pos h1 hσ
      have b : 0 < 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy) := by
        rw [e2]; exact div_pos (by linarith) hσ
      constructor <;> linarith
  unfold SchurStable
  rw [hT, abs_det2_AF_lt_one_iff hσ hβ0 hβ1 hφy]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fn7_implied hβ0 h.1 h.2, h⟩

/-- Galí (2015), eqs. (17)–(18), p. 108: under rule (16) (for `σ > 0`,
`0 < β < 1`, `φ_y ≥ 0`) the system is determinate iff (17) and (18) hold. -/
theorem determinate_iff_17_18 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AF β σ κ φπ φy) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) :=
  (𝔼.determinate_iff _).trans (schurStable_AF_iff hσ hβ0 hβ1 hφy)

/-- **Implementation under rule (16)** (Galí 2015, pp. 108–109): under (17) and
(18), `ỹ = π = 0` and `i = r^n` is the unique equilibrium with bounded adapted
output gap and inflation. -/
theorem equilibrium_iff_zero {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) (h17 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (h18 : κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β))
    {rn ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔ ygap = 0 ∧ infl = 0 ∧ i = rn := by
  constructor
  · intro he
    obtain ⟨hx, hr⟩ := (equilibrium_iff_solves 𝔼).mp he
    obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
    have heq := 𝔼.system_unique ((schurStable_AF_iff hσ hβ0 hβ1 hφy).mpr ⟨h17, h18⟩) hx h0
      (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
      (boundedVec_stack hba hbb) (boundedVec_stack ⟨0, fun t ω => by simp⟩
        ⟨0, fun t ω => by simp⟩)
    have h1 : ygap = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [hr t, h1, h2]
    simp
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact zero_equilibrium 𝔼 β σ κ φπ φy rn

/-- **Indeterminacy without (17)–(18)** (Galí 2015, p. 108): if (17) or (18)
fails (with `σ > 0`, `0 < β < 1`, `φ_y ≥ 0`), there is an equilibrium under rule
(16) with bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem exists_nonzero_equilibrium [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy)
    (hfail : ¬ (0 < κ * (φπ - 1) + (1 - β) * φy ∧
      κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β))) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ 0 ∨ infl ≠ 0) := by
  have hns : ¬ SchurStable (tr2 (AF β σ κ φπ φy)) (det2 (AF β σ κ φπ φy)) := by
    rw [schurStable_AF_iff hσ hβ0 hβ1 hφy]; exact hfail
  obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    fun t => rn t + φπ • 𝔼.E t (y (t + 1) 1) + φy • 𝔼.E t (y (t + 1) 0),
    (equilibrium_iff_solves 𝔼).mpr ⟨hst ▸ hy, fun t => rfl⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The printed matrix gives the wrong verdict (C4-1) -/

/-- **C4-1** (Galí 2015, p. 108): at `σ = κ = 1`, `β = 1/2`, `φ_π = 3`,
`φ_y = 0`, conditions (17)–(18) hold and the corrected `A_F` satisfies the
Schur–Cohn condition, but the printed matrix does not (its trace is `−3/2` and its
determinant `−1/2`). -/
theorem printed_verdict_differs :
    (0 < (1 : ℝ) * (3 - 1) + (1 - 1 / 2) * 0 ∧
      (1 : ℝ) * (3 - 1) + (1 + 1 / 2) * 0 < 2 * 1 * (1 + 1 / 2)) ∧
    SchurStable (tr2 (AF (1 / 2) 1 1 3 0)) (det2 (AF (1 / 2) 1 1 3 0)) ∧
    ¬ SchurStable (tr2 (AFprinted (1 / 2) 1 1 3 0)) (det2 (AFprinted (1 / 2) 1 1 3 0)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [schurStable_AF_iff (by norm_num) (by norm_num) (by norm_num) le_rfl]
    norm_num
  · simp only [SchurStable, tr2, det2, AFprinted, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num [abs_of_neg]

/-- **C4-1, in terms of equilibria** (Galí 2015, p. 108): at `σ = κ = 1`,
`β = 1/2`, `φ_π = 3`, `φ_y = 0`, the system under rule (16) is determinate, but the
printed system is not; so the printed matrix does not describe the equilibrium
conditions. -/
theorem printed_determinacy_differs [Nonempty Ω] :
    𝔼.Determinate (AF (1 / 2) 1 1 3 0) ∧ ¬ 𝔼.Determinate (AFprinted (1 / 2) 1 1 3 0) := by
  rw [𝔼.determinate_iff, 𝔼.determinate_iff]
  exact ⟨printed_verdict_differs.2.1, printed_verdict_differs.2.2⟩

/-- **C4-1, a solution of the printed system that is not an equilibrium**
(Galí 2015, p. 108): at `σ = κ = 1`, `β = 1/2`, `φ_π = 3`, `φ_y = 0` there is a
bounded adapted `(ỹ, π) ≠ (0, 0)` solving `x_t = A_F^{printed} E_t x_{t+1}` that is
not an equilibrium under rule (16) for any nominal-rate path. -/
theorem printed_solution_not_equilibrium [Nonempty Ω] (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, 𝔼.Solves (AFprinted (1 / 2) 1 1 3 0) 0 (stack ygap infl) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      ∀ i, ¬ Equilibrium 𝔼 (1 / 2) 1 1 3 0 rn ygap infl i := by
  have hz : 𝔼.Solves (AFprinted (1 / 2) 1 1 3 0) 0 0 := fun t j => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique printed_verdict_differs.2.2 hz
    (fun t j => by simp) ⟨0, fun t j ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, hst ▸ hy, fun t => hay t 0, fun t => hay t 1,
    ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, fun i he => ?_⟩
  obtain ⟨hx, -⟩ := (equilibrium_iff_solves 𝔼).mp he
  have hz' : 𝔼.Solves (AF (1 / 2) 1 1 3 0) 0 0 := fun t j => by simp
  have hax : 𝔼.AdaptedVec (stack (fun t => y t 0) (fun t => y t 1)) := by
    rw [hst]; exact hay
  have hbx : BoundedVec (stack (fun t => y t 0) (fun t => y t 1)) := by
    rw [hst]; exact ⟨M, hM⟩
  have heq := 𝔼.system_unique printed_verdict_differs.2.1 hx hz'
    hax (fun t j => by simp) hbx ⟨0, fun t j ω => by simp⟩
  rw [hst] at heq
  exact hne heq

/-! ### Rules without an output-gap response (p. 110) -/

/-- Galí (2015), p. 110: with `φ_y = 0` the contemporaneous rule (11) (with
`φ_π ≥ 0`) is determinate iff `φ_π > 1`. -/
theorem determinate_contemporaneous_phiy_zero [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    𝔼.Determinate (RuleTaylorPrinciple.AT β σ κ φπ 0) ↔ 1 < φπ := by
  rw [RuleTaylorPrinciple.determinate_iff_14 𝔼 hσ hκ hβ0 hβ1 hφπ le_rfl, mul_zero, add_zero,
    mul_pos_iff_of_pos_left hκ, sub_pos]

/-- **Galí (2015), p. 110 (with C4-4)**: with `φ_y = 0` the forward-looking rule
(16) is determinate iff `1 < φ_π < 1 + 2σ (1 + β)/κ`, both inequalities strict. -/
theorem determinate_forward_phiy_zero [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    𝔼.Determinate (AF β σ κ φπ 0) ↔ 1 < φπ ∧ φπ < 1 + 2 * σ * (1 + β) / κ := by
  rw [determinate_iff_17_18 𝔼 hσ hβ0 hβ1 le_rfl]
  simp only [mul_zero, add_zero]
  rw [mul_pos_iff_of_pos_left hκ, sub_pos]
  have e : κ * (φπ - 1) < 2 * σ * (1 + β) ↔ φπ < 1 + 2 * σ * (1 + β) / κ := by
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hκ, mul_comm]
  rw [e]

/-- **C4-4** (Galí 2015, p. 110): at the boundary `φ_π = 1 + 2σ (1 + β)/κ`,
`φ_y = 0`, the matrix `A_F` has the eigenvalue `−1`:
`det (−I − A_F) = 1 + tr A_F + det A_F = 0`. -/
theorem boundary_eigenvalue_neg_one {β σ κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    Matrix.det ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      - AF β σ κ (1 + 2 * σ * (1 + β) / κ) 0) = 0 := by
  rw [Matrix.det_fin_two]
  simp [AF]
  field_simp
  ring

/-- **C4-4** (Galí 2015, p. 110): the book's "no greater than `1 + 2σ(1 + β)/κ`"
is not sufficient: at `φ_π = 1 + 2σ (1 + β)/κ` (which satisfies `1 < φ_π`),
`φ_y = 0`, the system under rule (16) is indeterminate. -/
theorem not_determinate_at_boundary [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 < 1 + 2 * σ * (1 + β) / κ ∧
      ¬ 𝔼.Determinate (AF β σ κ (1 + 2 * σ * (1 + β) / κ) 0) := by
  refine ⟨by have : 0 < 2 * σ * (1 + β) / κ := by positivity
             linarith, ?_⟩
  rw [determinate_forward_phiy_zero 𝔼 hσ hκ hβ0 hβ1]
  exact fun h => lt_irrefl _ h.2

end Gali.MonetaryPolicyDesign.RuleForward

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The welfare loss function

Galí (2015), Chapter 4, §4.4 (pp. 110–111) and Appendix 4.1 (pp. 117–119): the
second-order approximation to the representative household's welfare around an efficient
steady state, Lemmas 1 and 2, the loss function `W`, the average loss `L`, and the comparative
statics of the loss weights.

## Two layers

* **(A) exact algebra.** `secondOrderUtility_eq`: given an efficient steady state
  (`U_n N = −(1 − α) U_c C`, `efficiency_iff`), the exact employment identity
  `(1 − α) n = y − a + d` and `ŷ^n = ψ_ya a`, the book's second-order polynomial in log
  deviations equals
  `−(U_c C/2)[(σ + (φ+α)/(1−α))(y − ŷ^n)² + (ε/Θ) var_i p(i)] + t.i.p.` plus the explicit
  higher-order terms `K((ε/2Θ) var − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`; the terms
  independent of policy `tip` are an explicit function of the shocks `a`, `z` only.
* **(B) the analytic bridge.** `period_utility_second_order`: for `U(C, N; Z) = (u(C) + w(N))Z`
  with `u`, `w` of class `C³` near the steady state, along any one-parameter family of
  allocations of size `s` (log deviations `O(s)`, cross-sectional price variance `O(s²)`,
  Lemma 1), period utility equals the quadratic form plus t.i.p. up to `O(s³)`
  (`Asymptotics.IsBigO`), via Mathlib's one-dimensional Taylor theorem (`taylor_two`,
  `logdev_taylor`, `exp_taylor_two`). `period_utility_second_order_dispersion` discharges the
  Lemma 1 hypotheses for an actual family of price distributions;
  `period_utility_normalised` is the book's display divided by `U_c C`.

## Lemma 1 and Lemma 2

* Lemma 1 (`dispersion_second_order`, restated from the Chapter 3 project):
  `d = (ε/(2Θ)) var_i p(i) + O(s³)`.
* Lemma 2 is proved **exactly** for the Calvo cross-section
  `ν_t = θ ν_{t−1} + (1 − θ) δ_{p*_t}` of log prices with mean `m_t`: `calvoMix_mean`,
  `calvoMix_var` give `Δm_t = (1 − θ)(p*_t − m_{t−1})` and
  `var_t = θ var_{t−1} + θ(1 − θ)(p*_t − m_{t−1})²`, hence `var_t = θ var_{t−1} + (θ/(1−θ))(Δm_t)²`
  (`calvoMix_var_meanChange`, `calvo_var_recursion`). Then `lemma2_hasSum` (any inherited
  dispersion, Yun 2005), `lemma2`, `lemma2_calvo`:
  `∑ βᵗ var_t = θ/((1 − βθ)(1 − θ)) ∑ βᵗ (Δm_t)²`, with convergence proved. The link to
  inflation is second order: `inflation_sub_meanChange` (`π_t − Δm_t = O(s²)`) and
  `inflation_sq_sub_meanChange_sq` (`π_t² − (Δm_t)² = O(s³)`).

## `W`, `L` and the weights

* `welfare_eq_loss`, `welfare_eq_loss_calvo`: `W = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε/λ) π²]`
  (with `π = Δm`), exact given the Calvo recursion; `welfare_stationary`: `W = L/(1 − β)`.
* `gapCoeff_strictMono_sigma`, `gapCoeff_strictMono_phi`, `gapCoeff_strictMonoOn_alpha`: the
  gap coefficient increases in `σ`, `φ`, `α`. `inflWeight_strictMonoOn_eps`,
  `inflWeight_strictMonoOn_theta`: `ε/λ` increases in `ε` and `θ`.
* **C4-3.** The weight of the gap *relative* to inflation is `κ/ε` (`relWeight_eq_ratio`); its
  slope in `α` has the constant sign of `(1 − σ) − (σ + φ)(ε − 1)` (`relWeight_sub`), so it
  is strictly decreasing when `(σ + φ)(ε − 1) > 1 − σ` (`relWeight_strictAntiOn_alpha`, the
  baseline: `relWeight_baseline_strictAnti`, values `relWeight_baseline`) and increasing
  otherwise (`relWeight_strictMonoOn_alpha`). `relWeight_not_increasing_alpha` refutes the
  printed "relative weight … increasing in α" at the baseline.

-/

namespace Gali.MonetaryPolicyDesign.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology

variable {G : Type*} [MeasurableSpace G]

/-! ### Lemma 1: price dispersion to second order (restated from the Chapter 3 project) -/

/-- Galí (2015), p. 53 (restated from the Chapter 3 project): the CES price index
`P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), App. 4.1, p. 118 (restated from the Chapter 3 project): the dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Galí (2015), App. 4.1, p. 118: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), App. 4.1, p. 118 (restated from the Chapter 3 project): the cross-sectional
variance `var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ}

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: for a bounded measurable `z` on a probability space, every
`exp(t z)` is integrable (so the moment-generating function is finite everywhere). -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (t : ℝ) : Integrable (fun i => Real.exp (t * z i)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z i ≤ |t * z i| := le_abs_self _
    _ = |t| * |z i| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB i) (abs_nonneg t)

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86: **second-order Taylor expansion of the cumulant
generating function** of a bounded `z`:
`K(u) = (E z) u + (var z/2) u² + O(u³)` as `u → 0`. -/
theorem cgf_taylor [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) :
    (fun u => cgf z μ u - (∫ i, z i ∂μ) * u - (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      =O[nhds 0] fun u => u ^ 3 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have hAn : AnalyticOnNhd ℝ (cgf z μ) Set.univ := by
    have := analyticOnNhd_cgf (X := z) (μ := μ)
    rwa [hint] at this
  have hCD : ContDiff ℝ 3 (cgf z μ) := hAn.contDiff
  have hT := taylor_isLittleO_univ (x₀ := 0) hCD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd1 : deriv (cgf z μ) 0 = ∫ i, z i ∂μ := by
    rw [deriv_cgf_zero h0]
    simp
  have hd2 : iteratedDeriv 2 (cgf z μ) 0 = ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
    rw [iteratedDeriv_two_cgf_eq_integral h0, hd1, mgf_zero]
    simp
  have heq : (fun u => cgf z μ u - (∫ i, z i ∂μ) * u -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      = fun u => (cgf z μ u - taylorWithinEval (cgf z μ) 3 Set.univ 0 u) +
        iteratedDeriv 3 (cgf z μ) 0 / 6 * u ^ 3 := by
    funext u
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_univ,
      iteratedDeriv_zero, iteratedDeriv_one, hd1, hd2, cgf_zero, smul_eq_mul, sub_zero]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  simp only [sub_zero] at hT
  exact hT.isBigO.add ((Asymptotics.isBigO_refl _ _).const_mul_left _)

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86: the Taylor remainder of `K` along a ray,
`K(a s) − (E z)(a s) − (var z/2)(a s)² = O(s³)` as `s → 0`, for every slope `a`. -/
theorem cgf_taylor_comp [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (a : ℝ) :
    (fun s => cgf z μ (a * s) - (∫ i, z i ∂μ) * (a * s) -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (a * s) ^ 2) =O[nhds 0] fun s => s ^ 3 := by
  have hR := cgf_taylor (μ := μ) hz hB
  have ht : Filter.Tendsto (fun s : ℝ => a * s) (nhds 0) (nhds 0) := by
    have := (Filter.tendsto_id (x := nhds (0 : ℝ))).const_mul a
    simpa using this
  refine (hR.comp_tendsto ht).trans ?_
  have : ((fun u : ℝ => u ^ 3) ∘ fun s => a * s) = fun s => a ^ 3 * s ^ 3 := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [this]
  exact (Asymptotics.isBigO_refl _ _).const_mul_left _

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))` the log price
index is `p = p̄ + K((1 − ε)s)/(1 − ε)`, i.e. `P = exp(p̄ + K((1−ε)s)/(1−ε))`. -/
theorem priceIndex_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar s : ℝ) :
    priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + cgf z μ ((1 - ε) * s) / (1 - ε)) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ i, Real.exp (pbar + s * z i) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * pbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ i, Real.exp (pbar + s * z i) ^ (1 - ε)
        = Real.exp ((1 - ε) * pbar) * Real.exp ((1 - ε) * s * z i) := by
      intro i
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  unfold priceIndex
  rw [hsum, Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) (hM _)),
    Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  congr 1
  field_simp

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))`, the dispersion
term is exactly `d(s) = (1 − α) K(−εs/(1−α)) + (ε/(1−ε)) K((1−ε)s)`, with `K` the cumulant
generating function of `z`. -/
theorem dispersion_family_eq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (hα : α ≠ 1) (pbar s : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + s * z i))
      = (1 - α) * cgf z μ (-ε / (1 - α) * s) + ε / (1 - ε) * cgf z μ ((1 - ε) * s) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsubα : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hidx : priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)) :=
    priceIndex_family hz hB hε pbar s
  have hrel : ∀ i, (Real.exp (pbar + s * z i) /
      Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) ^ (-ε / (1 - α))
      = Real.exp (ε / (1 - α) * (Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) *
        Real.exp (-ε / (1 - α) * s * z i) := by
    intro i
    rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [dispersion, hidx]
  simp_rw [hrel]
  rw [integral_const_mul]
  have hm2 : ∫ i, Real.exp (-ε / (1 - α) * s * z i) ∂μ = mgf z μ (-ε / (1 - α) * s) := rfl
  rw [hm2, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf, cgf]
  field_simp
  ring

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 86: the cross-sectional variance of `p(i) = p̄ + s z(i)` is
`s² var z`. -/
theorem crossVar_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (pbar s : ℝ) :
    crossVar μ (fun i => pbar + s * z i) = s ^ 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hB i)
  have hmean : ∫ i, (pbar + s * z i) ∂μ = pbar + s * ∫ i, z i ∂μ := by
    rw [integral_add (integrable_const _) (hzI.const_mul s), integral_const, integral_const_mul]
    simp
  unfold crossVar
  beta_reduce
  rw [hmean]
  have hpt : ∀ i, (pbar + s * z i - (pbar + s * ∫ j, z j ∂μ)) ^ 2
      = s ^ 2 * (z i - ∫ j, z j ∂μ) ^ 2 := fun i => by ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86 (**second-order approximation of price dispersion**):
for any probability space of goods, any bounded measurable `z` and any level `p̄`, the family
of price distributions `p(i) = p̄ + s z(i)` (with `P` its CES index, so the index condition
holds) satisfies `d(s) = (ε/(2Θ)) var_i p(i) + O(s³)` as `s → 0`,
`Θ = (1 − α)/(1 − α + αε)`. -/
theorem dispersion_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 3 := by
  have hcomp := cgf_taylor_comp (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hsubα : (1 : ℝ) - α ≠ 0 := by linarith
  have hden : 1 - α + α * ε ≠ 0 := by nlinarith
  have heq : (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - α) * (cgf z μ (-ε / (1 - α) * s) - (∫ i, z i ∂μ) * (-ε / (1 - α) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (-ε / (1 - α) * s) ^ 2) +
        ε / (1 - ε) * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [dispersion_family_eq hz hB (by linarith) (by linarith), crossVar_family hz hB, bigTheta]
    field_simp
    ring
  rw [heq]
  exact ((hcomp _).const_mul_left _).add ((hcomp _).const_mul_left _)

/-- Restated from the Chapter 3 project.
Galí (2015), p. 59 and App. 3.4: along the family `p(i) = p̄ + s z(i)`, `d(s) = O(s²)`. -/
theorem dispersion_family_isBigO_sq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) =O[nhds 0]
      fun s => s ^ 2 := by
  have h3 := dispersion_second_order (μ := μ) hz hB hε hα0 hα1 pbar
  have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have hq : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 2 := by
    have : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
        = fun s => (ε / (2 * bigTheta α ε) * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (Asymptotics.isBigO_refl _ _).const_mul_left _
  have := (h3.trans h32).add hq
  simpa using this


/-- Galí (2015), App. 4.1, p. 119 (Lemma 2's first-order link, the log index versus the mean):
along `p(i) = p̄ + s z(i)` the log CES price index satisfies
`log P(s) = E_i p(i) + ((1 − ε)/2) var_i p(i) + O(s³)`; in particular `log P − E_i p = O(s²)`. -/
theorem logPriceIndex_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - ε)⁻¹ * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [priceIndex_family hz hB hε, Real.log_exp, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (cgf_taylor_comp hz hB _).const_mul_left _

/-! ### Bookkeeping for orders of magnitude -/

/-- Orders of magnitude multiply: `f = O(sᵃ)` and `g = O(sᵇ)` give `f g = O(sᵃ⁺ᵇ)`
(used throughout App. 4.1, Galí 2015, pp. 117–119). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Higher orders are smaller near `0`: `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b` (Galí 2015, App. 4.1,
"ignoring terms of third or higher order", p. 118). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- A process that is `O(s)` tends to `0` (Galí 2015, App. 4.1: the economy stays in a
neighbourhood of the steady state). -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-! ### One-dimensional Taylor expansions -/

/-- Galí (2015), App. 4.1, p. 117 (**second-order Taylor expansion with a cubic remainder**):
if `f` is `C³` near `x₀`, then
`f x = f x₀ + f'(x₀)(x − x₀) + f''(x₀)/2 (x − x₀)² + O((x − x₀)³)`.
This is Mathlib's one-dimensional Taylor theorem (`taylor_isLittleO`) at order three on an open
ball, with the cubic Taylor term absorbed into the `O`. -/
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

/-- Galí (2015), App. 4.1, p. 117: `e^x = 1 + x + x²/2 + O(x³)`, the expansion behind
`(X_t − X)/X ≃ x_t + x_t²/2`. -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 4.1, p. 117: `e^x − 1 = O(x)`. -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 4.1, p. 117 (**second-order expansion in log deviations**): if `f` is
`C³` near the steady state `X`, then with `X_t = X e^{x}`,
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

/-! ### Layer (A): the exact algebra of App. 4.1 -/

/-- Galí (2015), p. 111 and App. 4.1, p. 118: the output-gap coefficient of the loss,
`σ + (φ + α)/(1 − α)`. -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), App. 4.1, p. 119 (and ch. 3, p. 62): `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`,
so that natural output is `ŷ^n_t = ψ_ya a_t`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), App. 4.1, p. 117 (the second-order polynomial in log deviations): with
`Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y` (output = consumption), `n` (hours) and
`z` (preference shifter, `Z = e^z`),
`Ū(z + z²/2) + K(y + (1−σ)/2 y²) + U_n N(n + (1+φ)/2 n²) + K y z + U_n N n z`. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 4.1, pp. 118–119: the terms independent of policy ("t.i.p."), an
explicit function of the shocks `a` (technology) and `z` (preferences) only:
`Ū(z + z²/2) + K(a + a z + (Γψ_ya² − (1 + φ)/(1 − α)) a²/2)`, `Γ = σ + (φ+α)/(1−α)`. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 4.1, p. 118, last display: the policy-relevant quadratic form
`−(K/2)[(σ + (φ+α)/(1−α))(y − ŷ^n)² + (ε/Θ) var_i p(i)]`, with `ŷ^n = ψ_ya a`. -/
noncomputable def welfareQuadratic (K σ φ α ε y a v : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + ε / bigTheta α ε * v)

/-- Galí (2015), App. 4.1, p. 119: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)`, the identity
behind `(σ + (φ+α)/(1−α)) ŷ^n_t = ((1+φ)/(1−α)) a_t`. -/
theorem gapCoeff_mul_psiYA {σ φ : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), App. 4.1, p. 118: efficiency of the steady state, `−U_n/U_c = MPN` with
`MPN = (1 − α) Y/N` and `Y = C`, is equivalent to `U_n N = −(1 − α) U_c C`. -/
theorem efficiency_iff {Uc Un C N : ℝ} (hUc : Uc ≠ 0) (hN : N ≠ 0) :
    -Un / Uc = (1 - α) * C / N ↔ Un * N = -(1 - α) * (Uc * C) := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Galí (2015), App. 4.1, pp. 117–119 (**completing the square, exact**). Suppose the steady
state is efficient, `U_n N = −(1 − α) U_c C`, and hours satisfy the exact employment identity
`(1 − α) n = y − a + d` (Ch. 3, eq. (14) before approximation). Then for every `v` (to be the
cross-sectional price variance) the second-order polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + K((ε/2Θ) v − d)`
`− K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`.
The last two terms are of third order once `d − (ε/2Θ) v = O(s³)` (Lemma 1) and `d = O(s²)`. -/
theorem secondOrderUtility_eq {Ubar K UnN σ φ y n z a d v : ℝ} (hα : α ≠ 1)
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

/-! ### Layer (B): the analytic bridge -/

/-- Galí (2015), App. 4.1, pp. 117–119 (**second-order approximation of period utility,
rigorous form**). Period utility is `U(C, N; Z) = (u(C) + w(N)) Z` (separable, `U_cn = 0`,
`Z = e^z`), with `u`, `w` of class `C³` near the steady state `(C, N)`; `σ = −U_cc C/U_c`,
`φ = U_nn N/U_n`; the steady state is efficient, `U_n N = −(1 − α) U_c C`. Consider a
one-parameter family of allocations of size `s`: log deviations `y(s)` of output, `n(s)` of
hours, shocks `a(s)`, `z(s)`, all `O(s)`, with the exact employment identity
`(1 − α) n = y − a + d`, a price-dispersion term `d(s)` and cross-sectional price variance
`v(s) = O(s²)` related by Lemma 1, `d − (ε/2Θ) v = O(s³)`. Then
`U_t − U = −(U_c C/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) v] + t.i.p.(a, z) + O(s³)`. -/
theorem period_utility_second_order {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n a z d v : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s) (v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  set c := ε / (2 * bigTheta α ε) with hc
  -- orders of the building blocks
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
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
  -- the exact decomposition
  have hA : ∀ s, secondOrderUtility Ubar K UnN σ φ (y s) (n s) (z s)
      = welfareQuadratic K σ φ α ε (y s) (a s) (v s) + tip Ubar K σ φ α (a s) (z s) +
        K * (c * v s - d s) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) + d s * z s) :=
    fun s => secondOrderUtility_eq hα hden hEff (hn s)
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
  refine (((((((T1.add T2).add T3).add T4).add T5).add T6).sub T7)).congr_left fun s => ?_
  have hs := hA s
  unfold secondOrderUtility at hs
  linear_combination (-1 : ℝ) * hs

/-- Galí (2015), App. 4.1, p. 118 (**the bridge with Lemma 1 discharged**): the same
second-order statement when `d(s)` and `v(s)` are the dispersion term and the
cross-sectional variance of an actual family of price distributions `p(i) = p̄ + s ζ(i)` over
any probability space of goods (`ζ` bounded and measurable, `P` the CES index). -/
theorem period_utility_second_order_dispersion [IsProbabilityMeasure μ] {u w : ℝ → ℝ}
    {C N σ φ pbar B : ℝ} {ζ : G → ℝ} {y n a z : ℝ → ℝ} (hζ : Measurable ζ)
    (hB : ∀ i, |ζ i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hσ0 : 0 < σ) (hφ0 : 0 ≤ φ)
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C))
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1)
    (hn : ∀ s, (1 - α) * n s = y s - a s +
      dispersion μ α ε (fun i => Real.exp (pbar + s * ζ i))) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s)
            (crossVar μ (fun i => pbar + s * ζ i)) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hden : σ * (1 - α) + φ + α ≠ 0 := by
    have : 0 < σ * (1 - α) := mul_pos hσ0 (by linarith)
    linarith
  have hv : (fun s => crossVar μ (fun i => pbar + s * ζ i)) =O[𝓝 0] fun s => s ^ 2 := by
    have : (fun s => crossVar μ (fun i => pbar + s * ζ i))
        = fun s => (∫ i, (ζ i - ∫ j, ζ j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hζ hB]
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  exact period_utility_second_order hu hw hσ hφ hEff hα1.ne hden hy ha hz hv
    (dispersion_second_order hζ hB hε hα0 hα1 pbar) hn

/-- Galí (2015), App. 4.1, p. 118, normalised as in the book: with `U_c C ≠ 0`,
`(U_t − U)/(U_c C) = −½[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + O(s³)`. -/
theorem period_utility_normalised {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n a z d v : ℝ → ℝ}
    (hK : deriv u C * C ≠ 0) (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => ((u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) -
        (u C + w N)) / (deriv u C * C)
        - (-(1 / 2) * (gapCoeff σ φ α * (y s - psiYA σ φ α * a s) ^ 2 +
            ε / bigTheta α ε * v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s) / (deriv u C * C)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h := (period_utility_second_order hu hw hσ hφ hEff hα hden hy ha hz hv hd
    hn).const_mul_left (deriv u C * C)⁻¹
  refine h.congr_left fun s => ?_
  unfold welfareQuadratic
  generalize deriv u C * C = K at hK ⊢
  field_simp

/-! ### Lemma 2: the exact Calvo cross-section -/

/-- Galí (2015), p. 119 (Lemma 2 setting): a cross-sectional distribution of log prices is
admissible when it is a probability measure with finite first and second moments. -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν

/-- Galí (2015), p. 119: the cross-sectional mean of log prices `m = ∫ p ν(dp)`. -/
noncomputable def crossMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

/-- Galí (2015), p. 119: the cross-sectional variance of log prices `var_i p(i)`. -/
noncomputable def crossVarDist (ν : Measure ℝ) : ℝ := ∫ x, (x - crossMean ν) ^ 2 ∂ν

/-- Galí (2015), App. 3.2–3.3 and p. 119: the Calvo law of motion of the cross-section of log
prices, `ν_t = θ ν_{t−1} + (1 − θ) δ_{p*_t}` (derived from the firm-level model in the
Chapter 3 project, `dist_law_of_motion`). -/
noncomputable def calvoMix (θ : ℝ) (ν : Measure ℝ) (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac p

/-- Restated from the Chapter 3 project (`integral_calvo_mix`). Galí (2015), App. 3.2:
integrating against `θ ν + (1 − θ) δ_p` gives `θ ∫ f dν + (1 − θ) f(p)`. -/
theorem integral_calvoMix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(calvoMix θ ν p) = θ * ∫ x, f x ∂ν + (1 - θ) * f p := by
  have hd : Integrable f (Measure.dirac p) := integrable_dirac (by simp)
  rw [calvoMix, integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), p. 119: `var = E p² − (E p)²` for an admissible cross-section. -/
theorem crossVarDist_eq {ν : Measure ℝ} (hg : GoodDist ν) :
    crossVarDist ν = ∫ x, x ^ 2 ∂ν - crossMean ν ^ 2 := by
  obtain ⟨hp, h1, h2⟩ := hg
  have hpt : ∀ x, (x - crossMean ν) ^ 2 = x ^ 2 + (-2 * crossMean ν) * x + crossMean ν ^ 2 :=
    fun x => by ring
  unfold crossVarDist
  simp_rw [hpt]
  have e1 := integral_add (μ := ν) (f := fun x => x ^ 2 + (-2 * crossMean ν) * x)
    (g := fun _ => crossMean ν ^ 2) (h2.add (h1.const_mul _)) (integrable_const _)
  have e2 := integral_add (μ := ν) (f := fun x => x ^ 2) (g := fun x => (-2 * crossMean ν) * x)
    h2 (h1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold crossMean
  ring

/-- Galí (2015), p. 119: the Calvo law of motion preserves admissibility. -/
theorem calvoMix_good {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : GoodDist (calvoMix θ ν p) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [calvoMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (hi2.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Galí (2015), p. 119 (exact): the cross-sectional mean moves as
`m_t = θ m_{t−1} + (1 − θ) p*_t`, i.e. `Δm_t = (1 − θ)(p*_t − m_{t−1})`. -/
theorem calvoMix_mean {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : crossMean (calvoMix θ ν p) = θ * crossMean ν + (1 - θ) * p := by
  unfold crossMean
  exact integral_calvoMix h0 h1 p hg.2.1

/-- Galí (2015), p. 119 (**exact variance recursion**):
`var_t = θ var_{t−1} + θ(1 − θ)(p*_t − m_{t−1})²`. -/
theorem calvoMix_var {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ * (1 - θ) * (p - crossMean ν) ^ 2 := by
  rw [crossVarDist_eq (calvoMix_good h0 h1 p hg), crossVarDist_eq hg, calvoMix_mean h0 h1 p hg]
  have h2 : ∫ x, x ^ 2 ∂(calvoMix θ ν p) = θ * ∫ x, x ^ 2 ∂ν + (1 - θ) * p ^ 2 :=
    integral_calvoMix h0 h1 p hg.2.2
  rw [h2]
  ring

/-- Galí (2015), p. 119 (**exact, in terms of the change in the mean**): for `θ < 1`,
`var_t = θ var_{t−1} + (θ/(1 − θ)) (Δm_t)²` with `Δm_t = m_t − m_{t−1}`. -/
theorem calvoMix_var_meanChange {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ / (1 - θ) * (crossMean (calvoMix θ ν p) - crossMean ν) ^ 2 := by
  rw [calvoMix_var h0 h1.le p hg, calvoMix_mean h0 h1.le p hg]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), p. 119: along a Calvo sequence `ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` started
from an admissible `ν_0`, every cross-section is admissible. -/
theorem calvo_good {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0)) :
    ∀ t, GoodDist (ν t) := by
  intro t
  induction t with
  | zero => exact hg
  | succ t ih =>
    rw [hν t]
    exact calvoMix_good h0 h1 _ ih

/-- Galí (2015), p. 119 (**exact recursion along the Calvo sequence**; index `t + 1` is the
book's `t`, so `ν_0` is the inherited cross-section `ν_{−1}`):
`var_{t+1} = θ var_t + (θ/(1−θ))(m_{t+1} − m_t)²`. -/
theorem calvo_var_recursion {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ν : ℕ → Measure ℝ}
    {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (t : ℕ) :
    crossVarDist (ν (t + 1))
      = θ * crossVarDist (ν t) + θ / (1 - θ) * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2 := by
  rw [hν t]
  exact calvoMix_var_meanChange h0 h1 _ (calvo_good h0 h1.le hν hg t)

/-- Galí (2015), p. 119 (Lemma 2, partial sums): if `V_{t+1} = θ V_t + c q_t`, then
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

/-- Galí (2015), p. 119: a variance recursion `V_{t+1} = θ V_t + c q_t` with nonnegative data
stays nonnegative. -/
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

/-- Galí (2015), p. 119 (**Lemma 2, general form, exact**): if `V_{t+1} = θ V_t + c q_t`
with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`, `q ≥ 0` and `∑ βᵗ q_t` summable, then
`∑ βᵗ V_{t+1}` converges and equals `(θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. The term `θ V_0` is the
inherited dispersion of Yun (2005), cited p. 116. -/
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

/-- Galí (2015), p. 119 (**Lemma 2 as printed, exact**): with no inherited dispersion
(`V_0 = 0`, p. 102) and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
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

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, exact in `Δm`**): along
`ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` from an admissible `ν_0` with inherited dispersion
`var ν_0`, `∑ βᵗ var_i p_{t+1}(i) = (θ var ν_0 + (θ/(1−θ)) ∑ βᵗ (Δm_t)²)/(1 − βθ)`. -/
theorem lemma2_calvo_inherited {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      ((θ * crossVarDist (ν 0) + θ / (1 - θ) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) / (1 - β * θ)) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hV0 : 0 ≤ crossVarDist (ν 0) := integral_nonneg fun x => sq_nonneg _
  have hc : (0 : ℝ) ≤ θ / (1 - θ) := div_nonneg hθ0 (by linarith)
  exact lemma2_hasSum (c := θ / (1 - θ)) (V := fun t => crossVarDist (ν t)) hθ0 hβ0 hβθ hc hV0
    (fun t => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, as printed**): with no
inherited dispersion, `∑ βᵗ var_i p_t(i) = θ/((1−βθ)(1−θ)) ∑ βᵗ (Δm_t)²` exactly. -/
theorem lemma2_calvo {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      (θ / ((1 - β * θ) * (1 - θ)) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :=
  lemma2 (V := fun t => crossVarDist (ν t))
    (q := fun t => (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) hθ0 hθ1 hβ0 hβ1 hV0
    (fun _ => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**`Δm_t = π_t` to first order**): for log-price families
`p_k(i) = p̄ + s z_k(i)` at two consecutive dates, inflation `π = log P_1 − log P_0` (CES
indices) and the change in the cross-sectional mean `Δm = E p_1 − E p_0` differ by `O(s²)`. -/
theorem inflation_sub_meanChange [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ} (hz₀ : Measurable z₀)
    (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀) (hB₁ : ∀ i, |z₁ i| ≤ B₁)
    (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))) =O[𝓝 0] fun s => s ^ 2 := by
  have hvar : ∀ {z : G → ℝ} {B : ℝ}, Measurable z → (∀ i, |z i| ≤ B) →
      (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i)) =O[𝓝 0]
        fun s => s ^ 2 := fun {z} {B} hz hB => by
    have : (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
        = fun s => ((1 - ε) / 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have e₁ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₁ hB₁ hε pbar)).add
    (hvar hz₁ hB₁)
  have e₀ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₀ hB₀ hε pbar)).add
    (hvar hz₀ hB₀)
  refine (e₁.sub e₀).congr_left fun s => ?_
  ring

/-- Galí (2015), p. 119 (**`π_t² = (Δm_t)² + O(s³)`**): in the setting of
`inflation_sub_meanChange`, the squares of inflation and of the change in the cross-sectional
mean agree to second order, so Lemma 2 (exact in `Δm`) holds with `π` to second order. -/
theorem inflation_sq_sub_meanChange_sq [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀)
    (hB₁ : ∀ i, |z₁ i| ≤ B₁) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) ^ 2 -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) ^ 2) =O[𝓝 0]
      fun s => s ^ 3 := by
  have hD := inflation_sub_meanChange (μ := μ) hz₀ hz₁ hB₀ hB₁ hε pbar
  have hm : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) =O[𝓝 0]
      fun s => s ^ 1 := by
    have : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))
        = fun s => ((∫ i, z₁ i ∂μ) - ∫ i, z₀ i ∂μ) * s ^ 1 := by
      funext s
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have hsum := (bigO_weaken (by norm_num : 1 ≤ 2) hD).add (hm.const_mul_left 2)
  refine (bigO_mul hD hsum).congr_left fun s => ?_
  ring

/-! ### The welfare loss `W` and the average loss `L` (p. 111) -/

/-- Galí (2015), ch. 3, p. 61 (used on pp. 111 and 119):
`λ = (1 − θ)(1 − βθ)Θ/θ`. -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), ch. 3, p. 63: `κ = λ(σ + (φ + α)/(1 − α))`. -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * gapCoeff σ φ α

/-- Galí (2015), p. 111: the period loss `½[(σ + (φ+α)/(1−α)) ỹ² + (ε/λ) π²]`. -/
noncomputable def periodLoss (β θ σ φ α ε ygap infl : ℝ) : ℝ :=
  (gapCoeff σ φ α * ygap ^ 2 + ε / lambdaNK β θ α ε * infl ^ 2) / 2

/-- Galí (2015), p. 111 (**the welfare loss `W`**, for a given path):
`W = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/λ) π_t²]`. -/
noncomputable def welfareLoss (β θ σ φ α ε : ℝ) (ygap infl : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss β θ σ φ α ε (ygap t) (infl t)

/-- Galí (2015), p. 111 (**the average loss per period `L`**), as a function of the
variances: `L = ½[(σ + (φ+α)/(1−α)) var(ỹ) + (ε/λ) var(π)]`. -/
noncomputable def avgLoss (β θ σ φ α ε varY varPi : ℝ) : ℝ :=
  (gapCoeff σ φ α * varY + ε / lambdaNK β θ α ε * varPi) / 2

/-- Galí (2015), p. 119: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`. -/
theorem inflWeight_of_dispersion {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaNK β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 119, last display (**`W` in terms of the output gap and the price-level
drift, exact**): if the cross-sectional variance follows the exact Calvo recursion
`V_{t+1} = θ V_t + (θ/(1−θ)) (Δm_t)²` with no inherited dispersion, then
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/Θ) var_t] = W(ỹ, Δm)`, where `W` has inflation weight
`ε/λ`. -/
theorem welfare_eq_loss {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα : α < 1) {ygap Dm V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * Dm t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hD : Summable fun t => β ^ t * Dm t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + ε / bigTheta α ε * V (t + 1)) / 2))
      (welfareLoss β θ σ φ α ε ygap Dm) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => Dm t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hA := ((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hL.mul_left (ε / bigTheta α ε))).div_const 2
  have hB := ((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hD.hasSum.mul_left (ε / lambdaNK β θ α ε))).div_const 2
  have hW : welfareLoss β θ σ φ α ε ygap Dm = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
      ε / lambdaNK β θ α ε * ∑' t, β ^ t * Dm t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), pp. 111 and 119 (**`W` for the Calvo economy, exact in `Δm`**): along the
Calvo sequence of cross-sections with no inherited dispersion,
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/Θ) var_i p_t(i)] = W(ỹ, Δm)`. -/
theorem welfare_eq_loss_calvo {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα : α < 1) {ygap : ℕ → ℝ}
    {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hY : Summable fun t => β ^ t * ygap t ^ 2)
    (hD : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 +
        ε / bigTheta α ε * crossVarDist (ν (t + 1))) / 2))
      (welfareLoss β θ σ φ α ε ygap fun t => crossMean (ν (t + 1)) - crossMean (ν t)) :=
  welfare_eq_loss (V := fun t => crossVarDist (ν t)) hθ0 hθ1 hβ0 hβ1 hα hV0
    (calvo_var_recursion hθ0.le hθ1 hν hg) hY hD

/-- Galí (2015), p. 111 (**from `W` to `L`**): if the expected period-`t` squared gap and
squared inflation equal stationary variances `var(ỹ)`, `var(π)` at every date, then the
discounted expected loss is `L/(1 − β)`, i.e. `L` is the average loss per period. -/
theorem welfare_stationary {β θ σ φ varY varPi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {eY eP : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varPi) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * eY t + ε / lambdaNK β θ α ε * eP t) / 2))
      (avgLoss β θ σ φ α ε varY varPi / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (avgLoss β θ σ φ α ε varY varPi)
  convert h using 1
  · funext t
    rw [heY, heP, avgLoss]
  · rw [div_eq_inv_mul]

/-! ### Comparative statics of the weights (p. 111) -/

/-- Galí (2015), p. 111: the output-gap coefficient `σ + (φ+α)/(1−α)` is strictly increasing
in `σ`. -/
theorem gapCoeff_strictMono_sigma (φ α : ℝ) : StrictMono fun σ => gapCoeff σ φ α := by
  intro a b h
  simp only [gapCoeff]
  linarith

/-- Galí (2015), p. 111: the output-gap coefficient is strictly increasing in `φ` (`α < 1`). -/
theorem gapCoeff_strictMono_phi (σ : ℝ) (hα : α < 1) : StrictMono fun φ => gapCoeff σ φ α := by
  intro a b h
  simp only [gapCoeff]
  have h1 : (a + α) / (1 - α) < (b + α) / (1 - α) :=
    div_lt_div_of_pos_right (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 111: the output-gap coefficient is strictly increasing in `α` on
`α < 1` (for `φ > −1`, in particular for `φ ≥ 0`). -/
theorem gapCoeff_strictMonoOn_alpha (σ : ℝ) {φ : ℝ} (hφ : -1 < φ) :
    StrictMonoOn (fun α => gapCoeff σ φ α) (Set.Iio 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  simp only [gapCoeff]
  have h : (φ + a) / (1 - a) < (φ + b) / (1 - b) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-- Galí (2015), p. 111: the inflation weight in closed form,
`ε/λ = εθ(1 − α + αε)/((1 − θ)(1 − βθ)(1 − α))`. -/
theorem inflWeight_eq {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1) (hα : α < 1) :
    ε / lambdaNK β θ α ε
      = ε * θ * (1 - α + α * ε) / ((1 - θ) * (1 - β * θ) * (1 - α)) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 111: the inflation weight `ε/λ` is strictly increasing in the elasticity
of substitution `ε` (on `ε > 0`, for `0 ≤ α < 1`). -/
theorem inflWeight_strictMonoOn_eps {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    StrictMonoOn (fun ε => ε / lambdaNK β θ α ε) (Set.Ioi 0) := by
  have hβθ : β * θ < 1 := by nlinarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hΘa : 0 < 1 - α + α * a := by nlinarith
  have hΘb : 0 < 1 - α + α * b := by nlinarith
  simp only
  rw [inflWeight_eq hθ0 hθ1 hβθ hα1, inflWeight_eq hθ0 hθ1 hβθ hα1]
  have hD : 0 < (1 - θ) * (1 - β * θ) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hk : 0 < (b - a) * (1 - α + α * (a + b)) := mul_pos (by linarith) (by nlinarith)
  have : a * (1 - α + α * a) < b * (1 - α + α * b) := by nlinarith
  have hθ' : 0 < θ := hθ0
  nlinarith

/-- Galí (2015), p. 111: the inflation weight `ε/λ` is strictly increasing in the degree of
price stickiness `θ ∈ (0, 1)` (for `β ≤ 1`). -/
theorem inflWeight_strictMonoOn_theta {β : ℝ} (hβ1 : β ≤ 1) (hα : α < 1)
    (hε : 0 < ε) (hΘ : 0 < 1 - α + α * ε) :
    StrictMonoOn (fun θ => ε / lambdaNK β θ α ε) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hβa : β * a < 1 := by nlinarith
  have hβb : β * b < 1 := by nlinarith
  simp only
  rw [inflWeight_eq ha0 ha1 hβa hα, inflWeight_eq hb0 hb1 hβb hα]
  have hDa : 0 < (1 - a) * (1 - β * a) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hDb : 0 < (1 - b) * (1 - β * b) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < ε * (1 - α + α * ε) * (1 - α) := mul_pos (mul_pos hε hΘ) (by linarith)
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  nlinarith

/-- Galí (2015), p. 111 and ch. 5 (`ϑ = κ/ε`): the weight of the output gap **relative** to
inflation, `(σ + (φ+α)/(1−α)) / (ε/λ) = κ/ε`. -/
noncomputable def relWeight (β θ σ φ α ε : ℝ) : ℝ := kappaNK β θ σ φ α ε / ε

/-- Galí (2015), p. 111: `κ/ε` is the ratio of the two loss coefficients. -/
theorem relWeight_eq_ratio {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) (hε : 0 < ε) (hΘ : 0 < 1 - α + α * ε) :
    relWeight β θ σ φ α ε = gapCoeff σ φ α / (ε / lambdaNK β θ α ε) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold relWeight kappaNK lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 111 (C4-3): in closed form,
`κ/ε = ((1 − θ)(1 − βθ)/(θε)) · (σ(1 − α) + φ + α)/(1 − α + αε)`. -/
theorem relWeight_eq {β θ σ φ : ℝ} (hα : α < 1) :
    relWeight β θ σ φ α ε
      = (1 - θ) * (1 - β * θ) / (θ * ε) * ((σ * (1 - α) + φ + α) / (1 - α + α * ε)) := by
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold relWeight kappaNK lambdaNK bigTheta gapCoeff
  by_cases hε : ε = 0
  · simp [hε]
  by_cases hθ : θ = 0
  · simp [hθ]
  by_cases hΘ : 1 - α + α * ε = 0
  · simp [hΘ]
  field_simp
  ring

/-- Galí (2015), p. 111 (C4-3, exact difference): for `α₁, α₂` with `1 − αᵢ + αᵢε ≠ 0`,
`κ/ε(α₁) − κ/ε(α₂) = c (α₂ − α₁)((σ + φ)(ε − 1) − (1 − σ))/((1−α₁+α₁ε)(1−α₂+α₂ε))`,
`c = (1 − θ)(1 − βθ)/(θε)`: the sign of the slope in `α` does not depend on `α`. -/
theorem relWeight_sub {β θ σ φ α₁ α₂ : ℝ} (h₁ : α₁ < 1) (h₂ : α₂ < 1)
    (hΘ₁ : 1 - α₁ + α₁ * ε ≠ 0) (hΘ₂ : 1 - α₂ + α₂ * ε ≠ 0) :
    relWeight β θ σ φ α₁ ε - relWeight β θ σ φ α₂ ε
      = (1 - θ) * (1 - β * θ) / (θ * ε) * ((α₂ - α₁) * ((σ + φ) * (ε - 1) - (1 - σ)) /
          ((1 - α₁ + α₁ * ε) * (1 - α₂ + α₂ * ε))) := by
  rw [relWeight_eq h₁, relWeight_eq h₂, ← mul_sub, div_sub_div _ _ hΘ₁ hΘ₂]
  congr 2
  ring

/-- Galí (2015), p. 111 (**C4-3, corrected statement**): if `(σ + φ)(ε − 1) > 1 − σ` (true at
the baseline, and whenever `σ ≥ 1`), the relative weight `κ/ε` of the output gap is strictly
**decreasing** in `α` on `[0, 1)`. -/
theorem relWeight_strictAntiOn_alpha {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hε : 1 < ε) (hcond : 1 - σ < (σ + φ) * (ε - 1)) :
    StrictAntiOn (fun α => relWeight β θ σ φ α ε) (Set.Ico 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hΘa : 0 < 1 - a + a * ε := by nlinarith
  have hΘb : 0 < 1 - b + b * ε := by nlinarith
  have hβθ : β * θ < 1 := by nlinarith
  have hc : 0 < (1 - θ) * (1 - β * θ) / (θ * ε) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hθ0 (by linarith))
  have h := relWeight_sub (β := β) (θ := θ) (σ := σ) (φ := φ) hb1 ha1 hΘb.ne' hΘa.ne'
  have hpos : 0 < (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) / ((1 - b + b * ε) * (1 - a + a * ε))
      ∨ (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) / ((1 - b + b * ε) * (1 - a + a * ε)) < 0 := by
    right
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
      (mul_pos hΘb hΘa)
  simp only
  rcases hpos with hp | hn
  · exact absurd hp (by
      have : (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      exact not_lt.2 (div_nonpos_of_nonpos_of_nonneg this.le (mul_pos hΘb hΘa).le))
  · have := mul_neg_of_pos_of_neg hc hn
    linarith

/-- Galí (2015), p. 111 (C4-3, the other case): if `(σ + φ)(ε − 1) < 1 − σ`, the relative
weight `κ/ε` is strictly increasing in `α` on `[0, 1)`. -/
theorem relWeight_strictMonoOn_alpha {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hε : 1 < ε) (hcond : (σ + φ) * (ε - 1) < 1 - σ) :
    StrictMonoOn (fun α => relWeight β θ σ φ α ε) (Set.Ico 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hΘa : 0 < 1 - a + a * ε := by nlinarith
  have hΘb : 0 < 1 - b + b * ε := by nlinarith
  have hβθ : β * θ < 1 := by nlinarith
  have hc : 0 < (1 - θ) * (1 - β * θ) / (θ * ε) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hθ0 (by linarith))
  have h := relWeight_sub (β := β) (θ := θ) (σ := σ) (φ := φ) hb1 ha1 hΘb.ne' hΘa.ne'
  have hn : 0 < (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) /
      ((1 - b + b * ε) * (1 - a + a * ε)) :=
    div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (mul_pos hΘb hΘa)
  simp only
  have := mul_pos hc hn
  linarith

/-- Galí (2015), p. 111 (C4-3, the baseline numbers): at `β = 0.99`, `θ = 3/4`, `σ = 1`,
`φ = 5`, `ε = 9`, the relative weight `κ/ε` equals `103/1800 ≈ 0.0572` at `α = 0`,
`103/3240 ≈ 0.0318` at `α = 0.1`, `103/5400 ≈ 0.0191` at `α = 1/4` and
`103/7560 ≈ 0.0136` at `α = 0.4`. -/
theorem relWeight_baseline :
    relWeight 0.99 0.75 1 5 0 9 = 103 / 1800 ∧ relWeight 0.99 0.75 1 5 0.1 9 = 103 / 3240 ∧
      relWeight 0.99 0.75 1 5 0.25 9 = 103 / 5400 ∧ relWeight 0.99 0.75 1 5 0.4 9 = 103 / 7560 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [relWeight_eq (by norm_num)] <;> norm_num

/-- Galí (2015), p. 111 (**C4-3, counterexample to the printed claim**): "the relative weight of
output gap fluctuations in the loss function is increasing in … α" is false at the baseline:
the relative weight `κ/ε` is not monotone increasing in `α` (it falls from `≈ 0.0572` at
`α = 0` to `≈ 0.0191` at `α = 1/4`). The *absolute* coefficient is increasing in `α`
(`gapCoeff_strictMonoOn_alpha`). -/
theorem relWeight_not_increasing_alpha :
    ¬ MonotoneOn (fun α => relWeight 0.99 0.75 1 5 α 9) (Set.Ico 0 1) := by
  intro h
  have := h (a := 0) (b := 0.25) (by norm_num) (by norm_num) (by norm_num)
  simp only at this
  rw [relWeight_baseline.1, relWeight_baseline.2.2.1] at this
  norm_num at this

/-- Galí (2015), p. 111 (C4-3): at the baseline (`σ = 1`, `φ = 5`, `ε = 9`, `β = 0.99`,
`θ = 3/4`) the relative weight `κ/ε` is strictly decreasing in `α` on all of `[0, 1)`. -/
theorem relWeight_baseline_strictAnti :
    StrictAntiOn (fun α => relWeight 0.99 0.75 1 5 α 9) (Set.Ico 0 1) :=
  relWeight_strictAntiOn_alpha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Gali.MonetaryPolicyDesign.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two simple monetary policy rules

Galí (2015), Chapter 4, §4.4.1–4.4.2, pp. 111–116: a Taylor rule on output and a
constant money growth rule, evaluated with the loss function of `Welfare`.

## The Taylor rule (19)

* `rule19_iff_rule20`: `i_t = ρ + φ_π π_t + φ_y ŷ_t` is the gap rule (20) with the
  pseudo-shock `v_t = φ_y ŷ^n_t`.
* `equilibrium_iff_solves`: the equilibrium is `x_t = A_T E_t x_{t+1} + B_T(r̂^n_t − v_t)`
  (ch. 3's system with `v` reinterpreted); `schurStable_AT_iff`, `determinate_iff`: it is
  determinate iff (14) holds.
* `natRate_eq`, `drivingForce_eq`: with AR(1) technology,
  `r̂^n_t − v_t = −ψ_ya(σ(1 − ρ_a) + φ_y) a_t + (1 − ρ_z) z_t`.
* `equilibrium_iff_msv` (both shocks), `equilibrium_iff_msv_single`: under (14) the MSV
  solution `ỹ = ∑ ψ_y(ρ_k) c_k s_k`, `π = ∑ ψ_π(ρ_k) c_k s_k` exists and is the unique
  bounded equilibrium (uniqueness from the core's `system_unique`).
* `msvLoss`, `msvLoss_eq`, `msv_moments`, `equilibrium_loss`: the loss is
  `½[(σ + (φ+α)/(1−α)) ψ_y² + (ε/λ) ψ_π²] c² var(s)`, for any second-moment functional
  homogeneous of degree two (`variance_isSecondMoment`: Mathlib's variance is one);
  `ar1Var`, `ar1Var_fixed_point`, `ar1Var_hasSum`: the stationary AR(1) variance
  `σ_e²/(1 − ρ²)`.
* `msvLoss_tendsto_zero` (fn. 10): the variances of the gap and of inflation and the loss
  tend to `0` as `φ_π → ∞`.

## The constant money growth rule

`moneyDemand_iff_plus`, `constantMoney_iff_plus`, `predetermined_plus`,
`constantMoney_iff_system34`: with `l^+_t = l_t + ζ_t`, the model under `Δm_t = 0` is exactly
ch. 3's system (34) with shock vector `(r̂^n_t, ŷ^n_t, Δζ_t)`.

## Table 4.1

`table41_tech_1` … `table41_tech_4`, `table41_demand_1` … `table41_demand_4`: all 32 printed
entries follow from the closed forms at the baseline (`kappa_base`, `lambda_base`,
`gapCoeff_base`, `psiYA_base`), proved by `norm_num`. The book **truncates** to the printed
digits (`table41_truncated`: eight entries would differ under rounding).
-/

namespace Gali.MonetaryPolicyDesign.SimpleRules

open Filter Topology Welfare

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model under the Taylor rule (19) -/

/-- Galí (2015), eq. (7), p. 103 (ch. 3, eq. (22)): the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 103 (ch. 3, eq. (23)): the dynamic IS equation
`ỹ_t = −σ⁻¹(i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

omit 𝔼 in
/-- Galí (2015), eq. (19), p. 111: the Taylor rule `i_t = ρ + φ_π π_t + φ_y ŷ_t`, with
`ŷ_t = log(Y_t/Y)` the deviation of output from steady state. -/
def TaylorRule (ρ φπ φy : ℝ) (i infl yhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • yhat t

omit 𝔼 in
/-- Galí (2015), p. 112: the pseudo-shock `v_t = φ_y ŷ^n_t`. -/
def pseudoShock (φy : ℝ) (yhatn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => φy • yhatn t

omit 𝔼 in
/-- Galí (2015), eq. (20), p. 112: the rule in terms of the output gap,
`i_t = ρ + φ_π π_t + φ_y ỹ_t + v_t`. -/
def TaylorRuleGap (ρ φπ φy : ℝ) (i infl ygap v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + v t

omit 𝔼 in
/-- Galí (2015), eqs. (19)–(20), p. 112: since `ŷ_t = ỹ_t + ŷ^n_t`, the Taylor rule (19) on
output is the gap rule (20) with the pseudo-shock `v_t = φ_y ŷ^n_t`. -/
theorem rule19_iff_rule20 {ρ φπ φy : ℝ} {i infl yhat ygap yhatn : ℕ → Ω → ℝ}
    (hyhat : ∀ t, yhat t = ygap t + yhatn t) :
    TaylorRule ρ φπ φy i infl yhat ↔
      TaylorRuleGap ρ φπ φy i infl ygap (pseudoShock φy yhatn) := by
  simp only [TaylorRule, TaylorRuleGap, pseudoShock, hyhat, smul_add, add_assoc]

omit 𝔼 in
/-- Galí (2015), p. 112: the driving force of the system, `r̂^n_t − v_t = r^n_t − ρ − v_t`. -/
def drivingForce (ρ : ℝ) (rn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - v t

/-- Galí (2015), §4.4.1, pp. 111–112: an equilibrium under the Taylor rule (19): the NKPC,
the DIS and rule (19) with output `ŷ_t = ỹ_t + ŷ^n_t`. -/
def Equilibrium (β σ κ ρ φπ φy : ℝ) (rn yhatn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧
    TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t)

/-- Galí (2015), p. 112 (ch. 3, p. 65): the equilibrium conditions with the interest rate
substituted out, `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t` and the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), p. 112: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the matrix
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), p. 112: the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

omit 𝔼 in
/-- Galí (2015), p. 112: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

omit 𝔼 in
/-- Galí (2015), p. 112: the forcing term `B_T (r^n_t − v_t)`. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): with the gap rule (20), the
NKPC and the DIS hold iff the structural equations hold with `u = r̂^n − v`. -/
theorem nk_iff_structural {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0) {rn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRuleGap ρ φπ φy i infl ygap v) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy (drivingForce ρ rn v) ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [drivingForce, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [drivingForce, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the structural equations are
equivalent to `x_t = A_T E_t x_{t+1} + B_T u_t`, provided `σ + φ_y + κ φ_π ≠ 0`. -/
theorem structural_iff_solves {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β σ κ φπ φy u ygap infl ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination κ * e1 + (σ + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BT] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (σ + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0

/-- Galí (2015), p. 112 (**the system under rule (19)**): `(ỹ, π, i)` is an equilibrium under
the Taylor rule (19) iff `i` is given by the rule and `x_t = (ỹ_t, π_t)` solves
`x_t = A_T E_t x_{t+1} + B_T (r̂^n_t − v_t)` with the pseudo-shock `v_t = φ_y ŷ^n_t`: the
dynamics of ch. 3's rule, with `v` reinterpreted. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    (hS : σ + φy + κ * φπ ≠ 0) {rn yhatn ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t)) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy)
        (forcing (BT σ κ φπ φy) (drivingForce ρ rn (pseudoShock φy yhatn))) (stack ygap infl) := by
  have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp hrule
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hgap]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the trace of `A_T`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the determinant of `A_T`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (14), p. 106, as required on p. 111 (restated from the Chapter 3
project, Bullard–Mitra): for `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T`
lie inside the unit circle iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), p. 111: under rule (19) the system is determinate iff (14) holds (the
pseudo-shock is exogenous, so determinacy is that of ch. 3's rule). -/
theorem determinate_iff [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

omit 𝔼 in
/-- Restated from the Chapter 3 project: two bounded processes stack to a bounded vector. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Restated from the Chapter 3 project: two adapted processes stack to an adapted vector. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-! ### The driving force (20) -/

/-- Galí (2015), p. 112 (with ch. 3, p. 62): with AR(1) technology `E_t a_{t+1} = ρ_a a_t`,
natural output `ŷ^n_t = ψ_ya a_t` and the natural rate
`r^n_t = ρ + σ E_t Δŷ^n_{t+1} + (1 − ρ_z) z_t`, one has
`r^n_t − ρ = −σψ_ya(1 − ρ_a) a_t + (1 − ρ_z) z_t`. -/
theorem natRate_eq {σ ρ ρa ρz ψya : ℝ} {a z rn yhatn : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hyn : ∀ t, yhatn t = ψya • a t)
    (hrn : ∀ t, rn t = (fun _ => ρ) + σ • (𝔼.E t (yhatn (t + 1)) - yhatn t) + (1 - ρz) • z t)
    (t : ℕ) : rn t - (fun _ => ρ) = (-(σ * ψya * (1 - ρa))) • a t + (1 - ρz) • z t := by
  rw [hrn t, hyn t, hyn (t + 1), map_smul, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 112 (**the driving force under rule (19)**):
`r̂^n_t − v_t = −σψ_ya(1 − ρ_a)a_t − φ_yψ_ya a_t + (1 − ρ_z)z_t
= −ψ_ya(σ(1 − ρ_a) + φ_y) a_t + (1 − ρ_z) z_t`. -/
theorem drivingForce_eq {σ ρ ρa ρz ψya φy : ℝ} {a z rn yhatn : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hyn : ∀ t, yhatn t = ψya • a t)
    (hrn : ∀ t, rn t = (fun _ => ρ) + σ • (𝔼.E t (yhatn (t + 1)) - yhatn t) + (1 - ρz) • z t)
    (t : ℕ) :
    drivingForce ρ rn (pseudoShock φy yhatn) t
      = (-(ψya * (σ * (1 - ρa) + φy))) • a t + (1 - ρz) • z t := by
  have h := natRate_eq 𝔼 ha hyn hrn t
  unfold drivingForce pseudoShock
  rw [h, hyn t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Minimum-state-variable solutions -/

/-- Galí (2015), p. 66 (used on p. 113): the denominator
`(1 − βρ)(σ(1 − ρ) + φ_y) + κ(φ_π − ρ)` of `Λ`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 66: `Λ = 1/msvDen`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), p. 66: the MSV output-gap coefficient `ψ_y = (1 − βρ) Λ`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 66: the MSV inflation coefficient `ψ_π = κ Λ`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): `msvDen = (1 − ρ)((1 − βρ)σ + κ
+ βφ_y) + [κ(φ_π − 1) + (1 − β)φ_y]`. -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): under (14) and `ρ < 1`,
`msvDen > 0`. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρu) * σ := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Restated from the Chapter 3 project: a scalar multiple of an AR(1) process is AR(1). -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): for an AR(1) driving force with
persistence `ρ` and `msvDen ≠ 0`, `ỹ_t = ψ_y u_t`, `π_t = ψ_π u_t` satisfy the structural
equations. -/
theorem msv_structural {β σ κ φπ φy ρu : ℝ} (hD : msvDen β σ κ φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β σ κ φπ φy u (fun t => msvPsiY β σ κ φπ φy ρu • u t)
      (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have c1 : (σ + φy) * msvPsiY β σ κ φπ φy ρu + φπ * msvPsiPi β σ κ φπ φy ρu
      = σ * (msvPsiY β σ κ φπ φy ρu * ρu) + msvPsiPi β σ κ φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β σ κ φπ φy ρu
      = β * (msvPsiPi β σ κ φπ φy ρu * ρu) + κ * msvPsiY β σ κ φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 112: the structural equations are linear, so solutions for two driving
forces add up to a solution for their sum. -/
theorem structural_add {β σ κ φπ φy : ℝ} {u₁ u₂ y₁ y₂ p₁ p₂ : ℕ → Ω → ℝ}
    (h₁ : Structural 𝔼 β σ κ φπ φy u₁ y₁ p₁) (h₂ : Structural 𝔼 β σ κ φπ φy u₂ y₂ p₂) :
    Structural 𝔼 β σ κ φπ φy (fun t => u₁ t + u₂ t) (fun t => y₁ t + y₂ t)
      (fun t => p₁ t + p₂ t) := by
  intro t
  obtain ⟨a₁, b₁⟩ := h₁ t
  obtain ⟨a₂, b₂⟩ := h₂ t
  simp only [map_add]
  refine ⟨?_, ?_⟩
  · rw [smul_add, smul_add, smul_add]
    calc (σ + φy) • y₁ t + (σ + φy) • y₂ t + (φπ • p₁ t + φπ • p₂ t)
        = ((σ + φy) • y₁ t + φπ • p₁ t) + ((σ + φy) • y₂ t + φπ • p₂ t) := by abel
      _ = _ := by rw [a₁, a₂]; abel
  · rw [smul_add, smul_add, b₁, b₂]
    abel

omit 𝔼 in
/-- Galí (2015), p. 112: a linear combination of bounded processes is bounded. -/
theorem boundedProc_lin {a z : ℕ → Ω → ℝ} (ha : BoundedProc a) (hz : BoundedProc z)
    (c₁ c₂ : ℝ) : BoundedProc (fun t => c₁ • a t + c₂ • z t) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hz
  refine ⟨|c₁| * M₁ + |c₂| * M₂, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (h₁ t ω) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (h₂ t ω) (abs_nonneg _))

/-- Galí (2015), p. 112: a linear combination of adapted processes is adapted. -/
theorem adapted_lin {a z : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hz : 𝔼.Adapted z) (c₁ c₂ : ℝ) :
    𝔼.Adapted (fun t => c₁ • a t + c₂ • z t) := fun t => by
  simp only [map_add, map_smul, ha t, hz t]

/-- Galí (2015), pp. 112–113 (**the MSV solution under rule (19), existence and uniqueness**).
Let technology `a` and preferences `z` be bounded AR(1) processes with persistences
`ρ_a, ρ_z < 1`, and let the driving force be `r̂^n_t − v_t = c_a a_t + c_z z_t` (by
`drivingForce_eq`, `c_a = −ψ_ya(σ(1−ρ_a) + φ_y)`, `c_z = 1 − ρ_z`). Under (14), a triple with
bounded adapted `ỹ`, `π` is an equilibrium iff
`ỹ_t = ψ_y(ρ_a) c_a a_t + ψ_y(ρ_z) c_z z_t`, `π_t = ψ_π(ρ_a) c_a a_t + ψ_π(ρ_z) c_z z_t` and
`i_t` is given by (19); this triple is bounded and adapted, so it is the unique bounded
equilibrium. -/
theorem equilibrium_iff_msv {β σ κ ρ φπ φy ρa ρz ca cz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρa : ρa < 1) (hρz : ρz < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn a z : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hz : 𝔼.IsAR1 ρz z) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = ca • a t + cz • z t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      ygap = (fun t => (msvPsiY β σ κ φπ φy ρa * ca) • a t +
        (msvPsiY β σ κ φπ φy ρz * cz) • z t) ∧
      infl = (fun t => (msvPsiPi β σ κ φπ φy ρa * ca) • a t +
        (msvPsiPi β σ κ φπ φy ρz * cz) • z t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • (ygap t + yhatn t) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hDa := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρa h14).ne'
  have hDz := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρz h14).ne'
  have hU : drivingForce ρ rn (pseudoShock φy yhatn) = fun t => ca • a t + cz • z t :=
    funext hu
  have hmsv := structural_add 𝔼 (msv_structural 𝔼 hDa (isAR1_smul 𝔼 ha ca))
    (msv_structural 𝔼 hDz (isAR1_smul 𝔼 hz cz))
  have hY : (fun t => msvPsiY β σ κ φπ φy ρa • (ca • a t) + msvPsiY β σ κ φπ φy ρz • (cz • z t))
      = fun t => (msvPsiY β σ κ φπ φy ρa * ca) • a t + (msvPsiY β σ κ φπ φy ρz * cz) • z t := by
    simp only [smul_smul]
  have hP : (fun t => msvPsiPi β σ κ φπ φy ρa • (ca • a t) +
      msvPsiPi β σ κ φπ φy ρz • (cz • z t))
      = fun t => (msvPsiPi β σ κ φπ φy ρa * ca) • a t +
        (msvPsiPi β σ κ φπ φy ρz * cz) • z t := by
    simp only [smul_smul]
  rw [hY, hP] at hmsv
  constructor
  · intro he
    have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp he.2.2
    have hs := (nk_iff_structural 𝔼 hσ.ne' hgap).mp ⟨he.1, he.2.1⟩
    rw [hU] at hs
    have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14)
      ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
      ((structural_iff_solves 𝔼 hS _ _ _).mp hmsv)
      (adaptedVec_stack 𝔼 hya hpa)
      (adaptedVec_stack 𝔼 (adapted_lin 𝔼 ha.1 hz.1 _ _) (adapted_lin 𝔼 ha.1 hz.1 _ _))
      (boundedVec_stack hyb hpb)
      (boundedVec_stack (boundedProc_lin hab hzb _ _) (boundedProc_lin hab hzb _ _))
    refine ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t) := fun t => by rw [h3]
    have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp hrule
    have hs : Structural 𝔼 β σ κ φπ φy (drivingForce ρ rn (pseudoShock φy yhatn)) ygap infl := by
      rw [hU, h1, h2]
      exact hmsv
    have hnk := (nk_iff_structural 𝔼 hσ.ne' hgap).mpr hs
    exact ⟨hnk.1, hnk.2, hrule⟩

/-- Galí (2015), p. 113 (**single-shock version**, as used for each half of Table 4.1): with
one bounded AR(1) shock `s` and driving force `r̂^n_t − v_t = c s_t`, under (14) the unique
bounded equilibrium is `ỹ_t = ψ_y c s_t`, `π_t = ψ_π c s_t`. -/
theorem equilibrium_iff_msv_single {β σ κ ρ φπ φy ρs c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρs : ρs < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρs s) (hsb : BoundedProc s)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = c • s t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      ygap = (fun t => (msvPsiY β σ κ φπ φy ρs * c) • s t) ∧
      infl = (fun t => (msvPsiPi β σ κ φπ φy ρs * c) • s t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • (ygap t + yhatn t) := by
  have h0 : 𝔼.IsAR1 0 (fun _ => (0 : Ω → ℝ)) :=
    ⟨fun t => by simp, fun t => by simp⟩
  have h0b : BoundedProc (fun _ => (0 : Ω → ℝ)) := ⟨0, fun _ _ => by simp⟩
  have h := equilibrium_iff_msv 𝔼 (ca := c) (cz := 0) (i := i) hσ hκ hβ0 hβ1 hφπ hφy hρs
    (by norm_num) h14 hs h0 hsb h0b (fun t => by rw [hu t]; simp) hya hpa hyb hpb
  simpa using h

/-! ### Losses as quadratic forms in the MSV coefficients -/

/-- Galí (2015), p. 111 and Table 4.1, p. 113: the average loss `L` implied by a single AR(1)
shock with stationary variance `va` and loading `c` on the driving force, under rule (19):
`var(ỹ) = (ψ_y c)² va`, `var(π) = (ψ_π c)² va`, with `κ = λ(σ + (φ+α)/(1−α))`. -/
noncomputable def msvLoss (β θ σ φ α ε φπ φy ρu c va : ℝ) : ℝ :=
  avgLoss β θ σ φ α ε ((msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va)
    ((msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va)

/-- Galí (2015), p. 111 (**the loss as a quadratic form in the MSV coefficients times the
shock variance**): `L = ½[(σ + (φ+α)/(1−α)) ψ_y² + (ε/λ) ψ_π²] c² var(s)`. -/
theorem msvLoss_eq (β θ σ φ α ε φπ φy ρu c va : ℝ) :
    msvLoss β θ σ φ α ε φπ φy ρu c va
      = (gapCoeff σ φ α * msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu ^ 2 +
          ε / lambdaNK β θ α ε * msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu ^ 2) / 2 *
        c ^ 2 * va := by
  unfold msvLoss avgLoss
  ring

omit 𝔼 in
/-- Galí (2015), p. 113: an abstract second-moment functional `Var` (homogeneous of degree
two, `Var(k X) = k² Var X`) applied to the MSV solution gives
`Var(ỹ_t) = (ψ_y c)² Var(s_t)`, `Var(π_t) = (ψ_π c)² Var(s_t)`, and the period loss
`L = msvLoss(…, Var(s_t))`. -/
theorem msv_moments (Var : (Ω → ℝ) → ℝ) (hVar : ∀ (k : ℝ) (X : Ω → ℝ), Var (k • X) = k ^ 2 * Var X)
    {β θ σ φ α ε φπ φy ρs c : ℝ} {s ygap infl : ℕ → Ω → ℝ}
    (hy : ygap = fun t => (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) • s t)
    (hp : infl = fun t => (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) • s t) (t : ℕ) :
    Var (ygap t) = (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) ^ 2 * Var (s t) ∧
      Var (infl t) = (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) ^ 2 * Var (s t) ∧
      avgLoss β θ σ φ α ε (Var (ygap t)) (Var (infl t))
        = msvLoss β θ σ φ α ε φπ φy ρs c (Var (s t)) := by
  subst hy hp
  refine ⟨hVar _ _, hVar _ _, ?_⟩
  simp only [hVar]
  rfl

/-- Galí (2015), pp. 111–113 (**the loss of the unique equilibrium**): under (14), with one
bounded AR(1) shock `s` loading `c` on the driving force and `κ = λ(σ + (φ+α)/(1−α))`, every
bounded equilibrium has, for any second-moment functional `Var`,
`L_t = ½[(σ + (φ+α)/(1−α)) Var(ỹ_t) + (ε/λ) Var(π_t)] = msvLoss(…, Var(s_t))`. -/
theorem equilibrium_loss (Var : (Ω → ℝ) → ℝ)
    (hVar : ∀ (k : ℝ) (X : Ω → ℝ), Var (k • X) = k ^ 2 * Var X)
    {β θ σ φ α ε ρ φπ φy ρs c : ℝ} (hσ : 0 < σ) (hκ : 0 < kappaNK β θ σ φ α ε)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρs : ρs < 1)
    (h14 : 0 < kappaNK β θ σ φ α ε * (φπ - 1) + (1 - β) * φy) {rn yhatn s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρs s) (hsb : BoundedProc s)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = c • s t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl)
    (he : Equilibrium 𝔼 β σ (kappaNK β θ σ φ α ε) ρ φπ φy rn yhatn ygap infl i) (t : ℕ) :
    avgLoss β θ σ φ α ε (Var (ygap t)) (Var (infl t))
      = msvLoss β θ σ φ α ε φπ φy ρs c (Var (s t)) := by
  obtain ⟨h1, h2, -⟩ := (equilibrium_iff_msv_single 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρs h14 hs hsb hu
    hya hpa hyb hpb).mp he
  exact (msv_moments Var hVar h1 h2 t).2.2

omit 𝔼 in
/-- Galí (2015), p. 113: Mathlib's variance on any probability space is such a second-moment
functional, `var(k X) = k² var X`. -/
theorem variance_isSecondMoment [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (k : ℝ)
    (X : Ω → ℝ) : ProbabilityTheory.variance (k • X) μ = k ^ 2 * ProbabilityTheory.variance X μ :=
  ProbabilityTheory.variance_smul k X μ

/-- Galí (2015), p. 113 (innovations with standard deviation `σ_e`): the stationary variance of
an AR(1) process, `σ_e²/(1 − ρ²)`. -/
noncomputable def ar1Var (σe ρ : ℝ) : ℝ := σe ^ 2 / (1 - ρ ^ 2)

/-- Galí (2015), p. 113: the stationary AR(1) variance is the unique fixed point of
`V = ρ² V + σ_e²` (for `|ρ| < 1`). -/
theorem ar1Var_fixed_point {σe ρ V : ℝ} (hρ : |ρ| < 1) :
    V = ρ ^ 2 * V + σe ^ 2 ↔ V = ar1Var σe ρ := by
  have h : ρ ^ 2 < 1 := by
    have := sq_abs ρ
    nlinarith [abs_nonneg ρ]
  have h1 : 1 - ρ ^ 2 ≠ 0 := by linarith
  unfold ar1Var
  constructor
  · intro hV
    field_simp
    linarith
  · intro hV
    rw [hV]
    field_simp
    ring

/-- Galí (2015), p. 113: the MA(∞) form `s_t = ∑ ρᵏ e_{t−k}` with uncorrelated innovations of
variance `σ_e²` has variance `∑ ρ²ᵏ σ_e² = σ_e²/(1 − ρ²)`. -/
theorem ar1Var_hasSum {σe ρ : ℝ} (hρ : |ρ| < 1) :
    HasSum (fun k : ℕ => (ρ ^ k) ^ 2 * σe ^ 2) (ar1Var σe ρ) := by
  have h0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have h : ρ ^ 2 < 1 := by
    have := sq_abs ρ
    nlinarith [abs_nonneg ρ]
  have hg := (hasSum_geometric_of_lt_one h0 h).mul_right (σe ^ 2)
  unfold ar1Var
  convert hg using 1
  · funext k
    ring
  · rw [div_eq_inv_mul]

/-- Galí (2015), fn. 10, p. 114 (**losses vanish as `φ_π → ∞`**): with `κ > 0`, `βρ ≠ 1` held
fixed, the variances `(ψ_y c)² va`, `(ψ_π c)² va` of the output gap and of inflation, and
hence the loss `L`, tend to `0` as `φ_π → +∞`. -/
theorem msvLoss_tendsto_zero {β θ σ φ α ε φy ρu c va : ℝ} (hκ : 0 < kappaNK β θ σ φ α ε) :
    Tendsto (fun φπ => (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va) atTop
        (𝓝 0) ∧
      Tendsto (fun φπ => (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va) atTop
        (𝓝 0) ∧
      Tendsto (fun φπ => msvLoss β θ σ φ α ε φπ φy ρu c va) atTop (𝓝 0) := by
  set κ := kappaNK β θ σ φ α ε
  have hD : Tendsto (fun φπ => msvDen β σ κ φπ φy ρu) atTop atTop := by
    have : (fun φπ => msvDen β σ κ φπ φy ρu)
        = fun φπ => κ * φπ + ((1 - β * ρu) * (σ * (1 - ρu) + φy) - κ * ρu) := by
      funext φπ
      unfold msvDen
      ring
    rw [this]
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hκ)
  have hL : Tendsto (fun φπ => msvLambda β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hD
    simpa [msvLambda, one_div, Function.comp_def] using this
  have hY : Tendsto (fun φπ => msvPsiY β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := hL.const_mul (1 - β * ρu)
    simpa [msvPsiY] using this
  have hP : Tendsto (fun φπ => msvPsiPi β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := hL.const_mul κ
    simpa [msvPsiPi] using this
  have hY2 : Tendsto (fun φπ => (msvPsiY β σ κ φπ φy ρu * c) ^ 2 * va) atTop (𝓝 0) := by
    have := ((hY.mul_const c).pow 2).mul_const va
    simpa using this
  have hP2 : Tendsto (fun φπ => (msvPsiPi β σ κ φπ φy ρu * c) ^ 2 * va) atTop (𝓝 0) := by
    have := ((hP.mul_const c).pow 2).mul_const va
    simpa using this
  refine ⟨hY2, hP2, ?_⟩
  have := ((hY2.const_mul (gapCoeff σ φ α)).add
    (hP2.const_mul (ε / lambdaNK β θ α ε))).div_const 2
  simpa [msvLoss, avgLoss] using this

/-! ### §4.4.2: a constant money growth rule with money-demand shocks -/

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (31), p. 74 (restated from the Chapter 3 project), here with
real balances `l̂_t = L (t + 1)`: `l̂_t = ỹ_t − η î_t + ŷ^n_t`. -/
def MoneyDemandGap (η : ℝ) (ygap i yn L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t - η • i t + yn t

/-- Galí (2015), ch. 3, eq. (32), p. 74 (restated from the Chapter 3 project): the DIS with
the interest rate eliminated. -/
def Eq32 (σ η : ℝ) (ygap infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + σ * η) • ygap t = (σ * η) • 𝔼.E t (ygap (t + 1)) + L (t + 1) +
    η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (33), p. 74 (restated from the Chapter 3 project):
`l̂_{t−1} = l̂_t + π_t − Δm_t`. -/
def RealBalanceId (infl L dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L t = L (t + 1) + infl t - dm t

/-- Galí (2015), ch. 3, p. 75 (restated from the Chapter 3 project): `l̂_{t−1}` is
predetermined. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

/-- Galí (2015), ch. 3, eq. (32), p. 74 (restated from the Chapter 3 project): given money
demand (31), the DIS is equivalent to (32) (for `σ ≠ 0`, `η ≠ 0`). -/
theorem dis_iff_eq32 {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) {ygap infl i rn yn L : ℕ → Ω → ℝ}
    (hMD : MoneyDemandGap η ygap i yn L) :
    DIS 𝔼 σ ygap i infl rn ↔ Eq32 𝔼 σ η ygap infl L rn yn := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2]
    have h1' : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      rw [h1]; field_simp
    linear_combination η * h1'
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    have h3 : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      have h4 : η * (σ * ygap t ω - (-(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
          σ * 𝔼.E t (ygap (t + 1)) ω)) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hη
      · linarith
    field_simp
    linear_combination h3

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (34), p. 75: the state `(ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the forecast `(E_t ỹ_{t+1}, E_t π_{t+1}, E_t l̂_t)`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (34), p. 75: the shock vector `(r̂^n_t, ŷ^n_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), ch. 3, eq. (34), p. 75: `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-- Galí (2015), ch. 3, eq. (34), p. 75 (restated from the Chapter 3 project): with `l̂`
predetermined, (34) is equivalent to (32), the NKPC and (33). -/
theorem system34_iff {σ η β κ : ℝ} {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ ygap infl L rn yn dm ↔
      Eq32 𝔼 σ η ygap infl L rn yn ∧ NKPC 𝔼 β κ ygap infl ∧ RealBalanceId infl L dm := by
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (h t ω) 0
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 ⊢
      linarith
    · have h1 := congrFun (h t ω) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h1 ⊢
      linarith
    · have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h2 ⊢
      linarith
  · rintro ⟨h32, h22, h33⟩ t ω
    have a := congrFun (h32 t) ω
    have b := congrFun (h22 t) ω
    have c := congrFun (h33 t) ω
    have hLω := congrFun (hL t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] <;> linarith

omit 𝔼 in
/-- Galí (2015), p. 114: money demand with a money-demand shock, in deviations,
`l̂_t = ỹ_t + ŷ^n_t − η î_t − ζ_t`, with `l̂_t = L (t + 1)` and `ζ_t = ζ (t + 1)` (so `ζ 0` is
`ζ_{−1}`). -/
def MoneyDemandShock (η : ℝ) (ygap yn i zeta L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t + yn t - η • i t - zeta (t + 1)

omit 𝔼 in
/-- Galí (2015), p. 114: the constant money growth rule `Δm_t = 0` together with
`l̂_{t−1} = l̂_t + π_t − Δm_t`: `l̂_{t−1} = l̂_t + π_t`. -/
def ConstantMoney (infl L : ℕ → Ω → ℝ) : Prop := ∀ t, L t = L (t + 1) + infl t

omit 𝔼 in
/-- Galí (2015), p. 114: with `l_t = m_t − p_t`, `π_t = p_t − p_{t−1}` and a constant money
stock `m_t = m̄` (the rule `m_t = 0`), real balances satisfy `l̂_{t−1} = l̂_t + π_t` at every
date `t ≥ 1`. -/
theorem constantMoney_of_levels {mbar : ℝ} {p L infl : ℕ → Ω → ℝ}
    (hL : ∀ t, L (t + 1) = (fun _ => mbar) - p t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (t : ℕ) : L (t + 1) = L (t + 1 + 1) + infl (t + 1) := by
  rw [hL, hL, hp]
  abel

omit 𝔼 in
/-- Galí (2015), p. 115: `l^+_t = l_t + ζ_t`, i.e. `L⁺ t = L t + ζ t` (both shifted). -/
def Lplus (L zeta : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => L t + zeta t

omit 𝔼 in
/-- Galí (2015), p. 115: `Δζ_t = ζ_t − ζ_{t−1}`, i.e. `ζ (t + 1) − ζ t`. -/
def dZeta (zeta : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => zeta (t + 1) - zeta t

omit 𝔼 in
/-- Galí (2015), p. 115: money demand with the shock is ch. 3's (31) for adjusted real
balances, `l̂^+_t = ỹ_t − η î_t + ŷ^n_t` (equivalently `î_t = (ỹ_t + ŷ^n_t − l̂^+_t)/η`). -/
theorem moneyDemand_iff_plus {η : ℝ} {ygap yn i zeta L : ℕ → Ω → ℝ} :
    MoneyDemandShock η ygap yn i zeta L ↔ MoneyDemandGap η ygap i yn (Lplus L zeta) := by
  constructor
  · intro h t
    simp only [Lplus]
    rw [h t]
    abel
  · intro h t
    have := h t
    simp only [Lplus] at this
    rw [eq_sub_of_add_eq this]
    abel

omit 𝔼 in
/-- Galí (2015), p. 115: under the constant-money rule, adjusted real balances obey
`l̂^+_{t−1} = l̂^+_t + π_t − Δζ_t`, ch. 3's (33) with `Δm` replaced by `Δζ`. -/
theorem constantMoney_iff_plus {infl L zeta : ℕ → Ω → ℝ} :
    ConstantMoney infl L ↔ RealBalanceId infl (Lplus L zeta) (dZeta zeta) := by
  constructor
  · intro h t
    simp only [Lplus, dZeta]
    rw [h t]
    abel
  · intro h t
    have := h t
    simp only [Lplus, dZeta] at this
    have h2 := congrArg (fun x => x - zeta t) this
    simp only [add_sub_cancel_right] at h2
    rw [h2]
    abel

/-- Galí (2015), p. 115: if `l̂_{t−1}` is predetermined and the money-demand shock is known
when it occurs, adjusted real balances `l̂^+_{t−1}` are predetermined. -/
theorem predetermined_plus {L zeta : ℕ → Ω → ℝ} (hL : Predetermined 𝔼 L)
    (hz : ∀ t, 𝔼.E t (zeta (t + 1)) = zeta (t + 1)) : Predetermined 𝔼 (Lplus L zeta) := by
  intro t
  simp only [Lplus, map_add, hL t, hz t]

/-- Galí (2015), §4.4.2, p. 115 (**the constant money growth rule is ch. 3's system (34)**):
with money demand `l̂_t = ỹ_t + ŷ^n_t − η î_t − ζ_t`, the rule `Δm_t = 0` and predetermined
adjusted real balances, the NKPC, the DIS and the money-market condition hold iff
`A_{M,0}(ỹ_t, π_t, l̂^+_{t−1}) = A_{M,1}(E_t ỹ_{t+1}, E_t π_{t+1}, l̂^+_t)`
`+ B_M(r̂^n_t, ŷ^n_t, Δζ_t)` with the same matrices as (34): money-demand shocks enter exactly
as money-supply shocks. -/
theorem constantMoney_iff_system34 {σ η β κ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    {ygap infl i L zeta rn yn : ℕ → Ω → ℝ} (hMD : MoneyDemandShock η ygap yn i zeta L)
    (hL : Predetermined 𝔼 (Lplus L zeta)) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ConstantMoney infl L) ↔
      System34 𝔼 σ η β κ ygap infl (Lplus L zeta) rn yn (dZeta zeta) := by
  rw [system34_iff 𝔼 hL, ← dis_iff_eq32 𝔼 hσ hη (moneyDemand_iff_plus.mp hMD),
    ← constantMoney_iff_plus]
  tauto

/-! ### Table 4.1 from the closed forms -/

/-- Galí (2015), p. 112: the loading of technology in the driving force,
`c_a = −ψ_ya(σ(1 − ρ_a) + φ_y)`. -/
noncomputable def techLoad (σ φy ρa ψya : ℝ) : ℝ := -(ψya * (σ * (1 - ρa) + φy))

/-- Galí (2015), p. 112: the loading of the preference shock in the driving force,
`c_z = 1 − ρ_z`. -/
def demandLoad (ρz : ℝ) : ℝ := 1 - ρz

/-- Galí (2015), Table 4.1, p. 113: the baseline calibration of ch. 3 (`β = 0.99`, `σ = 1`,
`φ = 5`, `α = 1/4`, `ε = 9`, `θ = 3/4`), innovations with a standard deviation of one
percent: the standard deviation (in percent) of the output gap for a shock of persistence
`ρ` with loading `c`, `|ψ_y c|/√(1 − ρ²)`. -/
noncomputable def baseSdGap (φπ φy ρ c : ℝ) : ℝ :=
  Real.sqrt ((msvPsiY 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy ρ * c) ^ 2 * ar1Var 1 ρ)

/-- Galí (2015), Table 4.1, p. 113: the standard deviation (in percent) of quarterly
inflation, `|ψ_π c|/√(1 − ρ²)`, at the baseline. -/
noncomputable def baseSdInfl (φπ φy ρ c : ℝ) : ℝ :=
  Real.sqrt ((msvPsiPi 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy ρ * c) ^ 2 * ar1Var 1 ρ)

/-- Galí (2015), Table 4.1, p. 113: the standard deviation (in percent) of output under a
technology shock, `ŷ_t = ỹ_t + ψ_ya a_t = (ψ_y c_a + ψ_ya) a_t`, at the baseline. (Under the
preference shock `ŷ^n = 0`, so `σ(y) = σ(ỹ)`.) -/
noncomputable def baseSdOutputTech (φπ φy : ℝ) : ℝ :=
  Real.sqrt ((msvPsiY 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy 0.9 *
    techLoad 1 φy 0.9 (psiYA 1 5 0.25) + psiYA 1 5 0.25) ^ 2 * ar1Var 1 0.9)

/-- Galí (2015), Table 4.1, p. 113: the welfare loss `L` in percent of steady-state
consumption at the baseline (variances in squared percentage points, hence the `1/100`). -/
noncomputable def baseLoss (φπ φy ρ c : ℝ) : ℝ :=
  msvLoss 0.99 0.75 1 5 0.25 9 φπ φy ρ c (ar1Var 1 ρ) / 100

/-- Galí (2015), p. 67 (used for Table 4.1): `κ = 103/600` at the baseline. -/
theorem kappa_base : kappaNK 0.99 0.75 1 5 0.25 9 = 103 / 600 := by
  unfold kappaNK lambdaNK bigTheta gapCoeff
  norm_num

/-- Galí (2015), p. 67: `λ = 103/4800` at the baseline. -/
theorem lambda_base : lambdaNK 0.99 0.75 0.25 9 = 103 / 4800 := by
  unfold lambdaNK bigTheta
  norm_num

/-- Galí (2015), p. 111: the gap coefficient `σ + (φ+α)/(1−α) = 8` at the baseline. -/
theorem gapCoeff_base : gapCoeff 1 5 0.25 = 8 := by
  unfold gapCoeff
  norm_num

/-- Galí (2015), p. 113 (ch. 3 fn. 12): `ψ_ya = 1` at the baseline. -/
theorem psiYA_base : psiYA 1 5 0.25 = 1 := by
  unfold psiYA
  norm_num

/-- Bounds on a square root from bounds on its argument (for the printed standard
deviations of Galí 2015, Tables 4.1). -/
theorem sqrt_bounds {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h1 : a ^ 2 ≤ x) (h2 : x < b ^ 2) :
    a ≤ Real.sqrt x ∧ Real.sqrt x < b :=
  ⟨(Real.le_sqrt ha ((sq_nonneg a).trans h1)).2 h1, (Real.sqrt_lt' hb).2 h2⟩

/-- Galí (2015), Table 4.1, p. 113, technology, Taylor's rule `φ_π = 1.5`, `φ_y = 0.125`
(the book truncates to two decimals): `σ(y) ∈ [1.85, 1.86)`, `σ(ỹ) ∈ [0.44, 0.45)`,
`σ(π) ∈ [0.69, 0.70)`, `L ∈ [1.02, 1.03)`. -/
theorem table41_tech_1 :
    (1.85 ≤ baseSdOutputTech 1.5 0.125 ∧ baseSdOutputTech 1.5 0.125 < 1.86) ∧
    (0.44 ≤ baseSdGap 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 0.45) ∧
    (0.69 ≤ baseSdInfl 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 0.70) ∧
    (1.02 ≤ baseLoss 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 1.03) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 1.5`, `φ_y = 0` (truncated to the
printed digits): `σ(y) ∈ [2.07, 2.08)`, `σ(ỹ) ∈ [0.21, 0.22)`, `σ(π) ∈ [0.34, 0.35)`,
`L ∈ [0.25, 0.26)`. -/
theorem table41_tech_2 :
    (2.07 ≤ baseSdOutputTech 1.5 0 ∧ baseSdOutputTech 1.5 0 < 2.08) ∧
    (0.21 ≤ baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.22) ∧
    (0.34 ≤ baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.35) ∧
    (0.25 ≤ baseLoss 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.26) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 5`, `φ_y = 0` (truncated to the
printed digits): `σ(y) ∈ [2.25, 2.26)`, `σ(ỹ) ∈ [0.03, 0.04)`, `σ(π) ∈ [0.05, 0.06)`,
`L ∈ [0.006, 0.007)`. -/
theorem table41_tech_3 :
    (2.25 ≤ baseSdOutputTech 5 0 ∧ baseSdOutputTech 5 0 < 2.26) ∧
    (0.03 ≤ baseSdGap 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.04) ∧
    (0.05 ≤ baseSdInfl 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.06) ∧
    (0.006 ≤ baseLoss 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.007) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 1.5`, `φ_y = 1` (truncated to the
printed digits): `σ(y) ∈ [1.06, 1.07)`, `σ(ỹ) ∈ [1.23, 1.24)`, `σ(π) ∈ [1.94, 1.95)`,
`L ∈ [7.98, 7.99)`. -/
theorem table41_tech_4 :
    (1.06 ≤ baseSdOutputTech 1.5 1 ∧ baseSdOutputTech 1.5 1 < 1.07) ∧
    (1.23 ≤ baseSdGap 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 1.24) ∧
    (1.94 ≤ baseSdInfl 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 1.95) ∧
    (7.98 ≤ baseLoss 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 7.99) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 0.125`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.59, 0.60)`, `σ(π) ∈ [0.20, 0.21)`, `L ∈ [0.10, 0.11)`. -/
theorem table41_demand_1 :
    (0.59 ≤ baseSdGap 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseSdGap 1.5 0.125 0.5 (demandLoad 0.5) < 0.60) ∧
    (0.20 ≤ baseSdInfl 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseSdInfl 1.5 0.125 0.5 (demandLoad 0.5) < 0.21) ∧
    (0.10 ≤ baseLoss 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseLoss 1.5 0.125 0.5 (demandLoad 0.5) < 0.11) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 0`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.68, 0.69)`, `σ(π) ∈ [0.23, 0.24)`, `L ∈ [0.13, 0.14)`. -/
theorem table41_demand_2 :
    (0.68 ≤ baseSdGap 1.5 0 0.5 (demandLoad 0.5) ∧ baseSdGap 1.5 0 0.5 (demandLoad 0.5) < 0.69) ∧
    (0.23 ≤ baseSdInfl 1.5 0 0.5 (demandLoad 0.5) ∧ baseSdInfl 1.5 0 0.5 (demandLoad 0.5) < 0.24) ∧
    (0.13 ≤ baseLoss 1.5 0 0.5 (demandLoad 0.5) ∧ baseLoss 1.5 0 0.5 (demandLoad 0.5) < 0.14) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 5`, `φ_y = 0`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.28, 0.29)`, `σ(π) ∈ [0.09, 0.10)`, `L ∈ [0.02, 0.03)`. -/
theorem table41_demand_3 :
    (0.28 ≤ baseSdGap 5 0 0.5 (demandLoad 0.5) ∧ baseSdGap 5 0 0.5 (demandLoad 0.5) < 0.29) ∧
    (0.09 ≤ baseSdInfl 5 0 0.5 (demandLoad 0.5) ∧ baseSdInfl 5 0 0.5 (demandLoad 0.5) < 0.10) ∧
    (0.02 ≤ baseLoss 5 0 0.5 (demandLoad 0.5) ∧ baseLoss 5 0 0.5 (demandLoad 0.5) < 0.03) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 1`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.31, 0.32)`, `σ(π) ∈ [0.10, 0.11)`, `L ∈ [0.02, 0.03)`. -/
theorem table41_demand_4 :
    (0.31 ≤ baseSdGap 1.5 1 0.5 (demandLoad 0.5) ∧ baseSdGap 1.5 1 0.5 (demandLoad 0.5) < 0.32) ∧
    (0.10 ≤ baseSdInfl 1.5 1 0.5 (demandLoad 0.5) ∧ baseSdInfl 1.5 1 0.5 (demandLoad 0.5) < 0.11) ∧
    (0.02 ≤ baseLoss 1.5 1 0.5 (demandLoad 0.5) ∧ baseLoss 1.5 1 0.5 (demandLoad 0.5) < 0.03) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113 (**the printed entries are truncated, not rounded**): e.g.
for technology with `φ_π = 1.5`, `φ_y = 0`, `σ(π) ≈ 0.3458` (printed `0.34`) and
`σ(ỹ) ≈ 0.2196` (printed `0.21`); for demand with `φ_π = 1.5`, `φ_y = 1`, `L ≈ 0.0278`
(printed `0.02`). All 32 entries agree with the closed forms after truncation. -/
theorem table41_truncated :
    0.345 < baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      0.215 < baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      0.025 < baseLoss 1.5 1 0.5 (demandLoad 0.5) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, techLoad,
    demandLoad]
  refine ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num),
    (Real.lt_sqrt (by norm_num)).2 (by norm_num), by norm_num⟩

end Gali.MonetaryPolicyDesign.SimpleRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.1: some indeterminacy proofs

Galí (2015), Chapter 4, Exercise 4.1, p. 121, on the systems (9)–(10) (p. 104–105)
and (12)–(13) (p. 105) of §4.3.1.

The non-policy block is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eqs. (6), (7), p. 104).

## Main results

* `isEigenvalue_iff_root`: a complex number is an eigenvalue of a real `2 × 2`
  matrix iff it is a root of `z² − tr A z + det A`.
* `equilibrium_AO_iff`: under the rule `i_t = r^n_t` (8) the model is
  `x_t = A_O E_t x_{t+1}` with `A_O = [[1, σ⁻¹], [κ, β + κ/σ]]` (10).
* **Exercise 4.1(a)** `AO_eigenvalues`: `A_O` has two real eigenvalues
  `0 < λ₁ < 1 < λ₂`, and no others. Hence (`AO_not_unique`) the efficient outcome
  `ỹ = π = 0` is not the only bounded equilibrium.
* `equilibrium_iff_structural`, `structural_iff_solves`: under the rule
  `i_t = r^n_t + φ_π π_t + φ_y ỹ_t − u_t` the model is `x_t = A_T E_t x_{t+1} + B_T u_t`
  with `A_T` of (13).
* **Exercise 4.1(b)** `AT_eigenvalues_inside_iff`: for `φ_π, φ_y ≥ 0` both eigenvalues
  of `A_T` lie strictly **inside** the unit circle iff condition (14),
  `κ (φ_π − 1) + (1 − β) φ_y > 0`.
* **Correction C4-2**: the exercise as printed says "outside". `AT_not_both_outside`:
  the two eigenvalues of `A_T` are never both on or outside the unit circle, so
  `printed_iff_iff_not14` (the printed equivalence holds exactly when (14) fails) and
  `printed_ex4_1b_false` (the printed claim is false).
* General infrastructure used by Exercises 4.2 and 4.3: the MSV solution of the
  structural system for an AR(1) forcing (`msv_structural`), linearity
  (`structural_add`, `structural_smul`), uniqueness under (14) (`structural_unique`) and
  multiplicity without it (`structural_not_unique`).

The `A_T` algebra, the Bullard–Mitra lemma and the MSV formulas are restated from the
Chapter 3 project (`TaylorRuleSystem.lean`).
-/

namespace Gali.MonetaryPolicyDesign.Ex4_1

open Filter Topology

/-! ### Eigenvalues of real `2 × 2` matrices -/

/-- Galí (2015), p. 105: `z ∈ ℂ` is an eigenvalue of the real matrix `A`, i.e. there is a
nonzero complex vector `v` with `A v = z v`. -/
def IsEigenvalue (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ Matrix.mulVec (A.map (fun a : ℝ => (a : ℂ))) v = z • v

/-- Galí (2015), p. 105: the characteristic determinant of a real `2 × 2` matrix,
`det (z I − A) = z² − tr A z + det A`. -/
theorem det_charMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A.map (fun a : ℝ => (a : ℂ))).det
      = z ^ 2 - (tr2 A : ℂ) * z + (det2 A : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [tr2, det2]
  ring

/-- Galí (2015), p. 105: `z` is an eigenvalue of `A` iff `z² − tr A z + det A = 0`. -/
theorem isEigenvalue_iff_charpoly (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    IsEigenvalue A z ↔ z ^ 2 - (tr2 A : ℂ) * z + (det2 A : ℂ) = 0 := by
  rw [← det_charMatrix, ← Matrix.exists_mulVec_eq_zero_iff]
  unfold IsEigenvalue
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

/-- Galí (2015), p. 105: the eigenvalues of a real `2 × 2` matrix are exactly the two roots
`root₁`, `root₂` of its characteristic polynomial. -/
theorem isEigenvalue_iff_root (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    IsEigenvalue A z ↔ z = root₁ (tr2 A) (det2 A) ∨ z = root₂ (tr2 A) (det2 A) := by
  rw [isEigenvalue_iff_charpoly]
  exact ⟨eq_root_of_eq, root_eq _ _ z⟩

/-- Galí (2015), p. 105: both eigenvalues lie strictly inside the unit circle iff the
Schur–Cohn condition holds. -/
theorem eigenvalues_inside_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ z, IsEigenvalue A z → ‖z‖ < 1) ↔ SchurStable (tr2 A) (det2 A) := by
  rw [schurStable_iff_roots]
  simp only [isEigenvalue_iff_root]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ z (rfl | rfl)
    exacts [h1, h2]

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the DIS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), eq. (9), p. 104: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (12), p. 105: two bounded processes stack to a bounded vector. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Galí (2015), eq. (12), p. 105: two adapted processes stack to an adapted vector. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-! ### Exercise 4.1(a): the exogenous rule `i_t = r^n_t` -/

/-- Galí (2015), eq. (10), p. 105: `A_O = [[1, 1/σ], [κ, β + κ/σ]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), eq. (10), p. 105: `tr A_O = 1 + β + κ/σ`. -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ / σ := by
  simp [tr2, AO]
  ring

/-- Galí (2015), eq. (10), p. 105: `det A_O = β`. -/
theorem det2_AO {β σ κ : ℝ} (hσ : σ ≠ 0) : det2 (AO β σ κ) = β := by
  simp [det2, AO]
  field_simp
  ring

/-- Galí (2015), eqs. (8)–(10), pp. 104–105: under the rule `i_t = r^n_t` the NKPC and the
DIS equation hold iff `x_t = A_O E_t x_{t+1}`. -/
theorem equilibrium_AO_iff (β σ κ : ℝ) (rn ygap infl : ℕ → Ω → ℝ) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap rn infl rn) ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, AO]
      linear_combination e1
    · simp [stack, AO]
      linear_combination e2 + κ * e1
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- **Exercise 4.1(a)** (Galí 2015, p. 121; claim on p. 105): for `σ, κ > 0` and
`0 < β < 1`, the matrix `A_O` has two real eigenvalues `λ₁, λ₂` with
`0 < λ₁ < 1 < λ₂`, and every complex eigenvalue is one of them. -/
theorem AO_eigenvalues {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 < l₂ ∧
      ∀ z : ℂ, IsEigenvalue (AO β σ κ) z ↔ z = l₁ ∨ z = l₂ := by
  obtain ⟨T, hT⟩ : ∃ T, T = 1 + β + κ / σ := ⟨_, rfl⟩
  have hk : 0 < κ / σ := div_pos hκ hσ
  have hd : 0 ≤ T ^ 2 - 4 * β := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (T ^ 2 - 4 * β) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = T ^ 2 - 4 * β := hs ▸ Real.sq_sqrt hd
  have hT0 : 0 < T := by linarith
  refine ⟨(T - s) / 2, (T + s) / 2, ?_, ?_, ?_, fun z => ?_⟩
  · have : s < T := by nlinarith
    linarith
  · have : T - 2 < s := by nlinarith
    linarith
  · have : 2 - T < s := by nlinarith
    linarith
  · rw [isEigenvalue_iff_charpoly, tr2_AO, det2_AO hσ.ne', ← hT]
    have hs2c : (s : ℂ) ^ 2 = (T : ℂ) ^ 2 - 4 * β := by exact_mod_cast hs2
    constructor
    · intro h
      have hm : (z - (((T - s) / 2 : ℝ) : ℂ)) * (z - (((T + s) / 2 : ℝ) : ℂ)) = 0 := by
        push_cast
        linear_combination h - (1 / 4 : ℂ) * hs2c
      rcases mul_eq_zero.mp hm with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (sub_eq_zero.mp h')
    · rintro (rfl | rfl)
      · push_cast
        linear_combination (1 / 4 : ℂ) * hs2c
      · push_cast
        linear_combination (1 / 4 : ℂ) * hs2c

/-- Galí (2015), p. 105: `A_O` violates the Schur–Cohn condition (one eigenvalue is
outside the unit circle). -/
theorem not_schurStable_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rw [tr2_AO, det2_AO hσ.ne']
  rintro ⟨-, h⟩
  rw [abs_lt] at h
  have := div_pos hκ hσ
  linarith

/-- Galí (2015), p. 105: the efficient outcome `ỹ = π = 0` is an equilibrium under the
rule `i_t = r^n_t`. -/
theorem AO_zero_equilibrium (β σ κ : ℝ) (rn : ℕ → Ω → ℝ) :
    NKPC 𝔼 β κ (fun _ => 0) (fun _ => 0) ∧ DIS 𝔼 σ (fun _ => 0) rn (fun _ => 0) rn := by
  refine ⟨fun t => ?_, fun t => ?_⟩ <;> simp

/-- Galí (2015), p. 105: the system under `i_t = r^n_t` is not determinate. -/
theorem AO_not_determinate [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ 𝔼.Determinate (AO β σ κ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- **Indeterminacy under `i_t = r^n_t`** (Galí 2015, p. 105): besides `ỹ = π = 0` there is
an equilibrium with bounded adapted output gap and inflation that is not identically
zero. -/
theorem AO_not_unique [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap rn infl rn) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hz : 𝔼.Solves (AO β σ κ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hz
    (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (equilibrium_AO_iff 𝔼 β σ κ rn _ _).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  funext t j
  fin_cases j
  · exact congrFun hcon.1 t
  · exact congrFun hcon.2 t

/-! ### Exercise 4.1(b): the rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` -/

/-- Galí (2015), p. 105, with a forcing term `u`: the equilibrium conditions with the
interest rate substituted out,
`(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t`, together with the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eqs. (6), (7), (11), pp. 104–105: if the rule is
`i_t = r^n_t + φ_π π_t + φ_y ỹ_t − u_t` (rule (11) is `u = 0`), the NKPC and the DIS hold
iff the structural equations hold with forcing `u`. -/
theorem equilibrium_iff_structural {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0)
    {rn u ygap infl i : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = rn t + φπ • infl t + φy • ygap t - u t) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy u ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ * e - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv - r
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105: `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), p. 105 (Chapter 3, eq. (27)): the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

/-- Galí (2015), eq. (12), p. 105: the forcing term `B u_t` of the system. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), eq. (12), p. 105: the structural equations are equivalent to
`x_t = A_T E_t x_{t+1} + B_T u_t`, provided `σ + φ_y + κ φ_π ≠ 0`. Restated from the
Chapter 3 project. -/
theorem structural_iff_solves {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β σ κ φπ φy u ygap infl ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination κ * e1 + (σ + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BT] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (σ + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0

/-- Galí (2015), eq. (13), p. 105: `tr A_T = (σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (13), p. 105: `det A_T = σ β/(σ + φ_y + κ φ_π)`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 105: `0 < det A_T < 1` for `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`. -/
theorem det2_AT_mem {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    0 < det2 (AT β σ κ φπ φy) ∧ det2 (AT β σ κ φπ φy) < 1 := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [det2_AT hS.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hS]
  nlinarith

/-- **Bullard–Mitra** (Galí 2015, eq. (14), p. 106): for `σ, κ > 0`, `0 < β < 1` and
`φ_π, φ_y ≥ 0`, `A_T` satisfies the Schur–Cohn condition iff
`κ (φ_π − 1) + (1 − β) φ_y > 0`. Restated from the Chapter 3 project. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  obtain ⟨hD0, hD1⟩ := det2_AT_mem hσ hκ hβ0 hβ1 hφπ hφy
  rw [det2_AT hS.ne'] at hD0 hD1
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    exact ⟨hD1, by linarith⟩

/-- **Exercise 4.1(b), corrected** (Galí 2015, p. 121; text p. 106): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie strictly inside the unit
circle iff condition (14), `κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
theorem AT_eigenvalues_inside_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    (∀ z, IsEigenvalue (AT β σ κ φπ φy) z → ‖z‖ < 1) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  rw [eigenvalues_inside_iff]
  exact schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy

/-- Galí (2015), Exercise 4.1(b), p. 121 (correction C4-2): the two eigenvalues of `A_T`
are never both on or outside the unit circle, since their product is
`det A_T ∈ (0, 1)`. -/
theorem AT_not_both_outside {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    ¬ ∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 ≤ ‖z‖ := by
  intro h
  simp only [isEigenvalue_iff_root] at h
  have h1 := h _ (Or.inl rfl)
  have h2 := h _ (Or.inr rfl)
  obtain ⟨hD0, hD1⟩ := det2_AT_mem hσ hκ hβ0 hβ1 hφπ hφy
  have hp : ‖root₁ (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy))‖ *
      ‖root₂ (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy))‖
        = det2 (AT β σ κ φπ φy) := by
    rw [← norm_mul, root_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
  nlinarith

/-- Galí (2015), Exercise 4.1(b), p. 121 (correction C4-2): the printed equivalence
"both eigenvalues outside the unit circle iff (14)" holds exactly when (14) fails. -/
theorem printed_iff_iff_not14 {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    ((∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy) ↔ ¬ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hno : ¬ ∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖ := fun h =>
    AT_not_both_outside hσ hκ hβ0 hβ1 hφπ hφy fun z hz => (h z hz).le
  constructor
  · intro h h14
    exact hno (h.mpr h14)
  · intro h
    exact ⟨fun h' => absurd h' hno, fun h' => absurd h' h⟩

/-- **The printed Exercise 4.1(b) is false** (Galí 2015, p. 121, correction C4-2): at
`β = 1/2`, `σ = κ = 1`, `φ_π = 2`, `φ_y = 0` condition (14) holds but the eigenvalues
of `A_T` are not outside the unit circle. -/
theorem printed_ex4_1b_false :
    ¬ ∀ β σ κ φπ φy : ℝ, 0 < σ → 0 < κ → 0 < β → β < 1 → 0 ≤ φπ → 0 ≤ φy →
      ((∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖) ↔
        0 < κ * (φπ - 1) + (1 - β) * φy) := by
  intro h
  have h' := h (1 / 2) 1 1 2 0 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    le_rfl
  rw [printed_iff_iff_not14 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    le_rfl] at h'
  exact h' (by norm_num)

/-- Galí (2015), p. 106: the system under rule (11) is determinate (at most one bounded
adapted solution for every forcing) iff (14) holds. -/
theorem determinate_iff_14 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Galí (2015), p. 106: under (14), two bounded adapted solutions of the structural
equations with the same forcing coincide. -/
theorem structural_unique {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {u ygap infl ygap' infl' : ℕ → Ω → ℝ}
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (hs' : Structural 𝔼 β σ κ φπ φy u ygap' infl')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs) ((structural_iff_solves 𝔼 hS _ _ _).mp hs')
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- Galí (2015), p. 106: without (14), next to any bounded adapted solution of the
structural equations there is a second one. -/
theorem structural_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) {u ygap infl : ℕ → Ω → ℝ}
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl', Structural 𝔼 β σ κ φπ φy u ygap' infl' ∧ 𝔼.Adapted ygap' ∧
      𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]
    linarith
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs) (adaptedVec_stack 𝔼 ha hb)
    (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (structural_iff_solves 𝔼 hS _ _ _).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- **Rule (11) under (14)** (Galí 2015, p. 106): with `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`
and (14), the only equilibrium with bounded adapted output gap and inflation is
`ỹ = π = 0`. -/
theorem rule11_unique {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = rn t + φπ • infl t + φy • ygap t)
    (he : NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) := by
  have hr0 : ∀ t, i t = rn t + φπ • infl t + φy • ygap t - (fun _ => (0 : Ω → ℝ)) t :=
    fun t => by rw [hrule t, sub_zero]
  have hs := (equilibrium_iff_structural 𝔼 hσ.ne' hr0).mp he
  have hz : Structural 𝔼 β σ κ φπ φy (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    fun t => ⟨by simp, by simp⟩
  exact structural_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy h14 hs hz ha hb (fun t => by simp)
    (fun t => by simp) hba hbb ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩

/-- **Rule (11) without (14)** (Galí 2015, p. 106): if (14) fails, rule (11) admits an
equilibrium with bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem rule11_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ,
      (NKPC 𝔼 β κ ygap infl ∧
        DIS 𝔼 σ ygap (fun t => rn t + φπ • infl t + φy • ygap t) infl rn) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hz : Structural 𝔼 β σ κ φπ φy (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    fun t => ⟨by simp, by simp⟩
  obtain ⟨y', p', hs, ha, hb, hba, hbb, hne⟩ := structural_not_unique 𝔼 hσ hκ hβ0 hβ1 hφπ
    hφy h14 hz (fun t => by simp) (fun t => by simp) ⟨0, fun t ω => by simp⟩
    ⟨0, fun t ω => by simp⟩
  have hr0 : ∀ t, (fun t => rn t + φπ • p' t + φy • y' t) t
      = rn t + φπ • p' t + φy • y' t - (fun _ => (0 : Ω → ℝ)) t := fun t => by simp
  exact ⟨y', p', (equilibrium_iff_structural 𝔼 hσ.ne' hr0).mpr hs, ha, hb, hba, hbb, hne⟩

/-! ### MSV solutions for AR(1) forcing (used in Exercises 4.2 and 4.3) -/

/-- Galí (2015), p. 112 (Chapter 3, p. 66): the denominator
`(1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u)` of `Λ_u`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 112: `Λ_u = 1/((1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u))`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the output-gap coefficient `(1 − βρ_u) Λ_u`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the inflation coefficient `κ Λ_u`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the denominator of `Λ_u` is
`(1 − ρ_u)((1 − βρ_u) σ + κ + β φ_y) + [κ (φ_π − 1) + (1 − β) φ_y]`. -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen
  ring

/-- Galí (2015), p. 112: under (14) and `ρ_u < 1` the denominator of `Λ_u` is positive. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 112: a scalar multiple of an AR(1) process is AR(1) with the same
persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), p. 112: a scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (c : ℝ) :
    BoundedProc (fun t => c • u t) := by
  obtain ⟨M, hM⟩ := hu
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 112: the sum of two bounded processes is bounded. -/
theorem boundedProc_add {u v : ℕ → Ω → ℝ} (hu : BoundedProc u) (hv : BoundedProc v) :
    BoundedProc (fun t => u t + v t) := by
  obtain ⟨M, hM⟩ := hu
  obtain ⟨N, hN⟩ := hv
  exact ⟨M + N, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hN t ω))⟩

/-- Galí (2015), p. 112: for an AR(1) forcing with persistence `ρ_u` (and a nonzero
denominator), `ỹ_t = (1 − βρ_u) Λ_u u_t`, `π_t = κ Λ_u u_t` solve the structural
equations. Restated from the Chapter 3 project. -/
theorem msv_structural {β σ κ φπ φy ρu : ℝ} (hD : msvDen β σ κ φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β σ κ φπ φy u (fun t => msvPsiY β σ κ φπ φy ρu • u t)
      (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have c1 : (σ + φy) * msvPsiY β σ κ φπ φy ρu + φπ * msvPsiPi β σ κ φπ φy ρu
      = σ * (msvPsiY β σ κ φπ φy ρu * ρu) + msvPsiPi β σ κ φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β σ κ φπ φy ρu
      = β * (msvPsiPi β σ κ φπ φy ρu * ρu) + κ * msvPsiY β σ κ φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 112: the structural equations are linear, so solutions for two
forcing processes add up to a solution for their sum. -/
theorem structural_add {β σ κ φπ φy : ℝ} {u₁ u₂ y₁ y₂ p₁ p₂ : ℕ → Ω → ℝ}
    (h₁ : Structural 𝔼 β σ κ φπ φy u₁ y₁ p₁) (h₂ : Structural 𝔼 β σ κ φπ φy u₂ y₂ p₂) :
    Structural 𝔼 β σ κ φπ φy (fun t => u₁ t + u₂ t) (fun t => y₁ t + y₂ t)
      (fun t => p₁ t + p₂ t) := by
  intro t
  obtain ⟨a₁, b₁⟩ := h₁ t
  obtain ⟨a₂, b₂⟩ := h₂ t
  simp only [map_add, smul_add]
  constructor
  · rw [add_add_add_comm, a₁, a₂]
    abel
  · rw [b₁, b₂]
    abel

/-- Galí (2015), p. 112: scaling the forcing scales the solution. -/
theorem structural_smul {β σ κ φπ φy : ℝ} {u y p : ℕ → Ω → ℝ}
    (h : Structural 𝔼 β σ κ φπ φy u y p) (c : ℝ) :
    Structural 𝔼 β σ κ φπ φy (fun t => c • u t) (fun t => c • y t) (fun t => c • p t) := by
  intro t
  obtain ⟨a, b⟩ := h t
  simp only [map_smul]
  constructor
  · rw [smul_comm (σ + φy) c, smul_comm φπ c, ← smul_add, a, smul_comm σ c, smul_add,
      smul_add]
  · rw [b, smul_add, smul_comm β c, smul_comm κ c]

end Gali.MonetaryPolicyDesign.Ex4_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.2: inflation targeting with noisy data

Galí (2015), Chapter 4, Exercise 4.2, p. 121. The economy is
`π_t = β E_t π_{t+1} + κ ỹ_t` and `ỹ_t = −σ⁻¹ (i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`,
with natural rate `r^n_t = ρ + r̂_t`, `r̂_t` an AR(1) with persistence `ρ_r ∈ [0, 1)`.
Inflation is measured with an i.i.d. error, `π^o_t = π_t + ξ_t` (`E_t ξ_{t+1} = 0`), and the
central bank sets `i_t = ρ + φ_π π^o_t`.

## Main results

* **(a)** `ex4_2a_equilibrium_iff`: for `φ_π > 1` the unique equilibrium with bounded adapted
  output gap and inflation is the MSV solution
  `π_t = a_r r̂_t + a_ξ ξ_t`, `ỹ_t = b_r r̂_t + b_ξ ξ_t` with
  `a_r = κ/D_r`, `b_r = (1 − βρ_r)/D_r`, `D_r = (1 − βρ_r) σ (1 − ρ_r) + κ (φ_π − ρ_r)`,
  `a_ξ = −φ_π κ/(σ + κ φ_π)`, `b_ξ = −φ_π/(σ + κ φ_π)`. `ex4_2a_exists` gives existence
  whenever the denominators are nonzero, and `ex4_2a_not_unique` gives multiplicity for
  `φ_π ≤ 1`. `ex4_2a_rate` gives the nominal rate.
* **(b)** `ex4_2b_coefficients`, `ex4_2b_limits`: as `φ_π → ∞`, `π_t → −ξ_t`, measured
  inflation `π^o_t → 0`, `ỹ_t → −ξ_t/κ` and `i_t → r^n_t + (σ/κ) ξ_t`.
* **(c)** With a covariance form `B` (`bilin_quad`, `stationary_var_ar1`,
  `ex4_2c_variance`), `var π_t = a_r² var r̂ + a_ξ² var ξ =: V(φ_π)`. Over the determinacy
  region `φ_π > 1`, `V` is minimised as follows (with `h(φ) = φ (D_r(φ)/(σ + κφ))³`):
  `ex4_2c_interior`: if `σ var ξ · h(1) < κ var r̂`, there is a unique `φ* > 1` with
  `σ var ξ · h(φ*) = κ var r̂`, and it is the unique minimiser;
  `ex4_2c_corner`: otherwise `V` is strictly increasing on `[1, ∞)` and has no minimiser on
  `φ_π > 1`; `ex4_2c_no_noise`: without noise `V` is strictly decreasing and tends to `0`;
  `ex4_2c_iid`: for `ρ_r = 0`, `φ* = κ var r̂/(σ var ξ)` in closed form.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_2

open Filter Topology Gali.MonetaryPolicyDesign.Ex4_1

/-! ### The MSV coefficients -/

/-- Galí (2015), Exercise 4.2(a), p. 121: the denominator
`D_r(φ_π) = (1 − βρ_r) σ (1 − ρ_r) + κ (φ_π − ρ_r)`. -/
def Dr (β σ κ ρr φ : ℝ) : ℝ := (1 - β * ρr) * σ * (1 - ρr) + κ * (φ - ρr)

/-- Galí (2015), Exercise 4.2(a): the inflation response to the natural rate, `κ/D_r`. -/
noncomputable def aR (β σ κ ρr φ : ℝ) : ℝ := κ / Dr β σ κ ρr φ

/-- Galí (2015), Exercise 4.2(a): the output-gap response to the natural rate,
`(1 − βρ_r)/D_r`. -/
noncomputable def bR (β σ κ ρr φ : ℝ) : ℝ := (1 - β * ρr) / Dr β σ κ ρr φ

/-- Galí (2015), Exercise 4.2(a): the inflation response to the measurement error,
`−φ_π κ/(σ + κ φ_π)`. -/
noncomputable def aXi (σ κ φ : ℝ) : ℝ := -(φ * κ) / (σ + κ * φ)

/-- Galí (2015), Exercise 4.2(a): the output-gap response to the measurement error,
`−φ_π/(σ + κ φ_π)`. -/
noncomputable def bXi (σ κ φ : ℝ) : ℝ := -φ / (σ + κ * φ)

/-- Galí (2015), Exercise 4.2: `D_r(φ) = c + κ φ` with `c = (1 − βρ_r) σ (1 − ρ_r) − κ ρ_r`. -/
theorem Dr_eq (β σ κ ρr φ : ℝ) :
    Dr β σ κ ρr φ = ((1 - β * ρr) * σ * (1 - ρr) - κ * ρr) + κ * φ := by
  unfold Dr
  ring

/-- Galí (2015), Exercise 4.2: `D_r(φ) > 0` for `φ ≥ 1`. -/
theorem Dr_pos {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρr < 1) (hφ : 1 ≤ φ) : 0 < Dr β σ κ ρr φ := by
  unfold Dr
  have h1 : 0 < 1 - β * ρr := by nlinarith
  have h2 : 0 < (1 - β * ρr) * σ * (1 - ρr) := by
    have := mul_pos h1 hσ
    exact mul_pos this (by linarith)
  nlinarith

/-- Galí (2015), Exercise 4.2: `D_r(φ) ≤ σ + κ φ`. -/
theorem Dr_le {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) : Dr β σ κ ρr φ ≤ σ + κ * φ := by
  unfold Dr
  have h0 : 0 ≤ ρr * (1 + β - β * ρr) := mul_nonneg hρ0 (by nlinarith)
  have h1 : (1 - β * ρr) * (1 - ρr) ≤ 1 := by nlinarith
  nlinarith

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 4.2, p. 121: the natural rate `r^n_t = ρ + r̂_t`. -/
def natRate (ρ : ℝ) (rhat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + rhat t

/-- Galí (2015), Exercise 4.2, p. 121: the rule `i_t = ρ + φ_π π^o_t`,
with measured inflation `π^o_t = π_t + ξ_t`. -/
def Rule (ρ φ : ℝ) (i infl ξ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φ • (infl t + ξ t)

/-- Galí (2015), Exercise 4.2, p. 121: an equilibrium: the NKPC, the DIS equation and the
rule. -/
def Equilibrium (β σ κ ρ φ : ℝ) (rhat ξ ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl (natRate ρ rhat) ∧ Rule ρ φ i infl ξ

/-- Galí (2015), Exercise 4.2: the composite forcing `u_t = r̂_t − φ_π ξ_t`. -/
def forcingU (φ : ℝ) (rhat ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => rhat t - φ • ξ t

/-- Galí (2015), Exercise 4.2, p. 121: an equilibrium is a solution of the structural
system with `φ_y = 0` and forcing `r̂_t − φ_π ξ_t`, together with the rule. -/
theorem equilibrium_iff {β σ κ ρ φ : ℝ} (hσ : σ ≠ 0) {rhat ξ ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i ↔
      Structural 𝔼 β σ κ φ 0 (forcingU φ rhat ξ) ygap infl ∧ Rule ρ φ i infl ξ := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    have hr' : ∀ t, i t = natRate ρ rhat t + φ • infl t + (0 : ℝ) • ygap t
        - forcingU φ rhat ξ t := fun t => by
      rw [hr t]
      funext ω
      simp only [natRate, forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨(equilibrium_iff_structural 𝔼 hσ hr').mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    have hr' : ∀ t, i t = natRate ρ rhat t + φ • infl t + (0 : ℝ) • ygap t
        - forcingU φ rhat ξ t := fun t => by
      rw [hr t]
      funext ω
      simp only [natRate, forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨hp, hd⟩ := (equilibrium_iff_structural 𝔼 hσ hr').mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), Exercise 4.2(a): the MSV processes solve the structural system, for an
AR(1) natural rate and a serially uncorrelated measurement error. -/
theorem msv_structural {β σ κ ρr φ : ℝ} (hD : Dr β σ κ ρr φ ≠ 0) (hS : σ + κ * φ ≠ 0)
    {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ) :
    Structural 𝔼 β σ κ φ 0 (forcingU φ rhat ξ)
      (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t)
      (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) := by
  have c1 : (σ + 0) * bR β σ κ ρr φ + φ * aR β σ κ ρr φ
      = σ * (bR β σ κ ρr φ * ρr) + aR β σ κ ρr φ * ρr + 1 := by
    unfold bR aR
    field_simp
    unfold Dr
    ring
  have hinv : (σ + κ * φ) * (σ + κ * φ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have c2 : (σ + 0) * bXi σ κ φ + φ * aXi σ κ φ = -φ := by
    unfold bXi aXi
    linear_combination (-φ) * hinv
  have c3 : aR β σ κ ρr φ = β * (aR β σ κ ρr φ * ρr) + κ * bR β σ κ ρr φ := by
    unfold aR bR
    field_simp
    ring
  have c4 : aXi σ κ φ = κ * bXi σ κ φ := by
    unfold aXi bXi
    ring
  intro t
  simp only [map_add, map_smul, hr.2 t, hξ.2 t, smul_smul, zero_smul, smul_zero, add_zero]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination rhat t ω * c1 + ξ t ω * c2
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination rhat t ω * c3 + ξ t ω * c4

/-- Galí (2015), Exercise 4.2(a): `a • x + b • z` built from adapted processes is
adapted. -/
theorem adapted_comb {x z : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hz : 𝔼.Adapted z) (a b : ℝ) :
    𝔼.Adapted (fun t => a • x t + b • z t) := fun t => by
  simp only [map_add, map_smul, hx t, hz t]

/-- Galí (2015), Exercise 4.2(a): `a • x + b • z` built from bounded processes is
bounded. -/
theorem bounded_comb {x z : ℕ → Ω → ℝ} (hx : BoundedProc x) (hz : BoundedProc z) (a b : ℝ) :
    BoundedProc (fun t => a • x t + b • z t) :=
  boundedProc_add (boundedProc_smul hx a) (boundedProc_smul hz b)

/-- **Exercise 4.2(a), existence** (Galí 2015, p. 121): whenever `D_r ≠ 0` and
`σ + κ φ_π ≠ 0`, the MSV processes together with the rule form an equilibrium with bounded
adapted output gap and inflation. -/
theorem ex4_2a_exists {β σ κ ρ ρr φ : ℝ} (hσ : σ ≠ 0) (hD : Dr β σ κ ρr φ ≠ 0)
    (hS : σ + κ * φ ≠ 0) {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ)
    (hrb : BoundedProc rhat) (hξb : BoundedProc ξ) :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t)
      (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t)
      (fun t => (fun _ => ρ) + φ • ((aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) + ξ t)) ∧
    𝔼.Adapted (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
    𝔼.Adapted (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) ∧
    BoundedProc (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
    BoundedProc (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) :=
  ⟨(equilibrium_iff 𝔼 hσ).mpr ⟨msv_structural 𝔼 hD hS hr hξ, fun _ => rfl⟩,
    adapted_comb 𝔼 hr.1 hξ.1 _ _, adapted_comb 𝔼 hr.1 hξ.1 _ _,
    bounded_comb hrb hξb _ _, bounded_comb hrb hξb _ _⟩

/-- **Exercise 4.2(a), the unique equilibrium** (Galí 2015, p. 121): for `σ, κ > 0`,
`0 < β < 1`, `ρ_r < 1` (the book has `ρ_r ∈ [0, 1)`) and `φ_π > 1`, with bounded AR(1)
`r̂` and bounded serially uncorrelated `ξ`, a triple `(ỹ, π, i)` with bounded adapted
`ỹ, π` is an equilibrium iff it is the MSV solution `ỹ_t = b_r r̂_t + b_ξ ξ_t`,
`π_t = a_r r̂_t + a_ξ ξ_t`, with `i` given by the rule. -/
theorem ex4_2a_equilibrium_iff {β σ κ ρ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hφ : 1 < φ) {rhat ξ : ℕ → Ω → ℝ}
    (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ) (hrb : BoundedProc rhat) (hξb : BoundedProc ξ)
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i ↔
      ygap = (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
      infl = (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) ∧
      i = fun t => (fun _ => ρ) + φ • (infl t + ξ t) := by
  have hD := (Dr_pos hσ hκ hβ0 hβ1 hρ1 hφ.le).ne'
  have hS : σ + κ * φ ≠ 0 := by positivity
  rw [equilibrium_iff 𝔼 hσ.ne']
  constructor
  · rintro ⟨hs, hrule⟩
    obtain ⟨h1, h2⟩ := structural_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
      (by nlinarith) hs (msv_structural 𝔼 hD hS hr hξ) ha hb (adapted_comb 𝔼 hr.1 hξ.1 _ _)
      (adapted_comb 𝔼 hr.1 hξ.1 _ _) hba hbb (bounded_comb hrb hξb _ _)
      (bounded_comb hrb hξb _ _)
    exact ⟨h1, h2, funext hrule⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2]
    refine ⟨msv_structural 𝔼 hD hS hr hξ, fun t => ?_⟩
    rw [h3, h2]

/-- **Exercise 4.2(a), the nominal rate** (Galí 2015, p. 121): in the MSV equilibrium
`i_t = ρ + φ_π a_r r̂_t + (φ_π σ/(σ + κ φ_π)) ξ_t`. -/
theorem ex4_2a_rate {β σ κ ρ ρr φ : ℝ} (hS : σ + κ * φ ≠ 0) (rhat ξ : ℕ → Ω → ℝ) (t : ℕ) :
    (fun _ => ρ) + φ • ((aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) + ξ t)
      = (fun _ => ρ) + (φ * aR β σ κ ρr φ) • rhat t + (φ * σ / (σ + κ * φ)) • ξ t := by
  have hinv : (σ + κ * φ) * (σ + κ * φ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have hc : φ * (aXi σ κ φ + 1) = φ * σ / (σ + κ * φ) := by
    unfold aXi
    linear_combination (-φ) * hinv
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ξ t ω * hc

/-- **Exercise 4.2(a), multiplicity for `φ_π ≤ 1`** (Galí 2015, pp. 106, 121): if
`0 ≤ φ_π ≤ 1`, next to any equilibrium with bounded adapted output gap and inflation there
is a second one. -/
theorem ex4_2a_not_unique [Nonempty Ω] {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {rhat ξ ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap' infl' i' ∧ 𝔼.Adapted ygap' ∧
      𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  obtain ⟨hs, -⟩ := (equilibrium_iff 𝔼 hσ.ne').mp he
  obtain ⟨y', p', hs', ha', hb', hba', hbb', hne⟩ := structural_not_unique 𝔼 hσ hκ hβ0 hβ1
    hφ0 le_rfl (by nlinarith) hs ha hb hba hbb
  exact ⟨y', p', fun t => (fun _ => ρ) + φ • (p' t + ξ t),
    (equilibrium_iff 𝔼 hσ.ne').mpr ⟨hs', fun _ => rfl⟩, ha', hb', hba', hbb', hne⟩

/-! ### Exercise 4.2(b): `φ_π → ∞` -/

/-- Galí (2015), Exercise 4.2(b): `d/(c + κ φ) → 0` as `φ → ∞`, for `κ > 0`. -/
theorem tendsto_div_affine (d c : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun φ : ℝ => d / (c + κ * φ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ c (Tendsto.const_mul_atTop hκ tendsto_id))

/-- **Exercise 4.2(b), coefficients** (Galí 2015, p. 121): as `φ_π → ∞`,
`a_r → 0`, `b_r → 0`, `a_ξ → −1`, `b_ξ → −1/κ`, `1 + a_ξ → 0` (measured inflation),
`φ_π a_r → 1` and `φ_π (1 + a_ξ) → σ/κ` (the nominal rate). -/
theorem ex4_2b_coefficients (β : ℝ) {σ κ : ℝ} (ρr : ℝ) (hκ : 0 < κ) :
    Tendsto (aR β σ κ ρr) atTop (𝓝 0) ∧ Tendsto (bR β σ κ ρr) atTop (𝓝 0) ∧
    Tendsto (aXi σ κ) atTop (𝓝 (-1)) ∧ Tendsto (bXi σ κ) atTop (𝓝 (-1 / κ)) ∧
    Tendsto (fun φ => 1 + aXi σ κ φ) atTop (𝓝 0) ∧
    Tendsto (fun φ => φ * aR β σ κ ρr φ) atTop (𝓝 1) ∧
    Tendsto (fun φ => φ * (1 + aXi σ κ φ)) atTop (𝓝 (σ / κ)) := by
  set c := (1 - β * ρr) * σ * (1 - ρr) - κ * ρr
  have hDr : ∀ φ, Dr β σ κ ρr φ = c + κ * φ := Dr_eq β σ κ ρr
  -- eventually both denominators are positive
  have hev : ∀ᶠ φ in atTop, 0 < c + κ * φ ∧ 0 < σ + κ * φ := by
    have h1 := (tendsto_atTop_add_const_left _ c
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
    have h2 := (tendsto_atTop_add_const_left _ σ
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
    exact h1.and h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := tendsto_div_affine κ c hκ
    refine this.congr fun φ => ?_
    simp only [aR, hDr]
  · have := tendsto_div_affine (1 - β * ρr) c hκ
    refine this.congr fun φ => ?_
    simp only [bR, hDr]
  · have := (tendsto_div_affine σ σ hκ).const_add (-1)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    simp only [aXi]
    linear_combination hS
  · have := (tendsto_div_affine (σ / κ) σ hκ).const_add (-1 / κ)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    have hk := mul_inv_cancel₀ hκ.ne'
    simp only [bXi]
    linear_combination κ⁻¹ * hS - φ * (σ + κ * φ)⁻¹ * hk
  · have := tendsto_div_affine σ σ hκ
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    simp only [aXi]
    linear_combination hS
  · have := (tendsto_div_affine (-c) c hκ).const_add 1
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hD := mul_inv_cancel₀ hφ.1.ne'
    simp only [aR, hDr]
    linear_combination -hD
  · have := (tendsto_div_affine (-(σ ^ 2 / κ)) σ hκ).const_add (σ / κ)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    have hk := mul_inv_cancel₀ hκ.ne'
    simp only [aXi]
    linear_combination σ * φ * (σ + κ * φ)⁻¹ * hk - (σ * κ⁻¹ - φ) * hS

/-- **Exercise 4.2(b)** (Galí 2015, p. 121): along the MSV equilibria, as `φ_π → ∞`,
inflation tends to `−ξ_t`, measured inflation `π^o_t` to `0`, the output gap to `−ξ_t/κ`, and
the nominal rate to `r^n_t + (σ/κ) ξ_t`, at every date and state. -/
theorem ex4_2b_limits (β : ℝ) {σ κ : ℝ} (ρ ρr : ℝ) (hκ : 0 < κ) (rhat ξ : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    Tendsto (fun φ => aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω) atTop
        (𝓝 (-ξ t ω)) ∧
    Tendsto (fun φ => aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω + ξ t ω) atTop (𝓝 0) ∧
    Tendsto (fun φ => bR β σ κ ρr φ * rhat t ω + bXi σ κ φ * ξ t ω) atTop
        (𝓝 (-ξ t ω / κ)) ∧
    Tendsto (fun φ => ρ + φ * (aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω + ξ t ω))
        atTop (𝓝 ((ρ + rhat t ω) + σ / κ * ξ t ω)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ex4_2b_coefficients β ρr hκ (σ := σ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (h1.mul_const (rhat t ω)).add (h3.mul_const (ξ t ω))
    convert this using 2
    ring
  · have := (h1.mul_const (rhat t ω)).add (h5.mul_const (ξ t ω))
    convert this using 2
    · ring
    · ring
  · have := (h2.mul_const (rhat t ω)).add (h4.mul_const (ξ t ω))
    convert this using 2
    ring
  · have := ((h6.mul_const (rhat t ω)).add (h7.mul_const (ξ t ω))).const_add ρ
    convert this using 2
    · ring
    · ring

/-! ### Exercise 4.2(c): the variance of inflation -/

/-- Galí (2015), Exercise 4.2(c): for a bilinear covariance form `B` and uncorrelated
`x, z`, `var (a x + b z) = a² var x + b² var z`. -/
theorem bilin_quad (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (a b : ℝ) (x z : Ω → ℝ)
    (h1 : B x z = 0) (h2 : B z x = 0) :
    B (a • x + b • z) (a • x + b • z) = a ^ 2 * B x x + b ^ 2 * B z z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Galí (2015), Exercise 4.2(c): the stationary variance of an AR(1),
`r̂_{t+1} = ρ_r r̂_t + ε_{t+1}` with `ε_{t+1}` uncorrelated with `r̂_t`: if
`var r̂_{t+1} = var r̂_t` then `var r̂_t = var ε/(1 − ρ_r²)`. -/
theorem stationary_var_ar1 (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {ρr sε : ℝ}
    (hρ : ρr ^ 2 < 1) {rhat ε : ℕ → Ω → ℝ} {t : ℕ}
    (hlaw : rhat (t + 1) = ρr • rhat t + ε (t + 1)) (h1 : B (rhat t) (ε (t + 1)) = 0)
    (h2 : B (ε (t + 1)) (rhat t) = 0) (hε : B (ε (t + 1)) (ε (t + 1)) = sε)
    (hstat : B (rhat (t + 1)) (rhat (t + 1)) = B (rhat t) (rhat t)) :
    B (rhat t) (rhat t) = sε / (1 - ρr ^ 2) := by
  have h := bilin_quad B ρr 1 (rhat t) (ε (t + 1)) h1 h2
  rw [one_smul, ← hlaw, hstat, hε] at h
  have hne : 1 - ρr ^ 2 ≠ 0 := by linarith
  field_simp
  linarith

/-- Galí (2015), Exercise 4.2(c): the variance of inflation in the MSV equilibrium as a
function of `φ_π`, `V(φ_π) = a_r² var r̂ + a_ξ² var ξ`. -/
noncomputable def varInfl (β σ κ ρr sr sξ φ : ℝ) : ℝ :=
  aR β σ κ ρr φ ^ 2 * sr + aXi σ κ φ ^ 2 * sξ

/-- Galí (2015), Exercise 4.2(c): the variance of the output gap in the MSV equilibrium,
`b_r² var r̂ + b_ξ² var ξ`. -/
noncomputable def varGap (β σ κ ρr sr sξ φ : ℝ) : ℝ :=
  bR β σ κ ρr φ ^ 2 * sr + bXi σ κ φ ^ 2 * sξ

/-- **Exercise 4.2(c), variances** (Galí 2015, p. 121): in the unique equilibrium
(`φ_π > 1`), if `r̂_t` and `ξ_t` are uncorrelated under the covariance form `B`, then
`var π_t = V(φ_π)` and `var ỹ_t = b_r² var r̂_t + b_ξ² var ξ_t`. -/
theorem ex4_2c_variance (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρ ρr φ : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρr < 1)
    (hφ : 1 < φ) {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ)
    (hrb : BoundedProc rhat) (hξb : BoundedProc ξ) {ygap infl i : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) (he : Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i) (t : ℕ)
    (h1 : B (rhat t) (ξ t) = 0) (h2 : B (ξ t) (rhat t) = 0) :
    B (infl t) (infl t) = varInfl β σ κ ρr (B (rhat t) (rhat t)) (B (ξ t) (ξ t)) φ ∧
      B (ygap t) (ygap t) = varGap β σ κ ρr (B (rhat t) (rhat t)) (B (ξ t) (ξ t)) φ := by
  obtain ⟨hy, hp, -⟩ := (ex4_2a_equilibrium_iff 𝔼 hσ hκ hβ0 hβ1 hρ1 hφ hr hξ hrb hξb ha hb
    hba hbb).mp he
  rw [hy, hp]
  exact ⟨bilin_quad B _ _ _ _ h1 h2, bilin_quad B _ _ _ _ h1 h2⟩

/-- Galí (2015), Exercise 4.2(c): the function `h(φ) = φ (D_r(φ)/(σ + κ φ))³` whose level
set `σ var ξ · h(φ) = κ var r̂` is the first-order condition. -/
noncomputable def hcrit (β σ κ ρr φ : ℝ) : ℝ := φ * (Dr β σ κ ρr φ / (σ + κ * φ)) ^ 3

/-- Galí (2015), Exercise 4.2(c): the ratio `D_r(φ)/(σ + κ φ)` is positive and nondecreasing
on `φ ≥ 1`. -/
theorem ratio_mono {β σ κ ρr x y : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 < Dr β σ κ ρr x / (σ + κ * x) ∧
      Dr β σ κ ρr x / (σ + κ * x) ≤ Dr β σ κ ρr y / (σ + κ * y) := by
  have hDx := Dr_pos hσ hκ hβ0 hβ1 hρ1 hx
  have hSx : 0 < σ + κ * x := by nlinarith
  have hSy : 0 < σ + κ * y := by nlinarith
  have hle := Dr_le (φ := x) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hDy : Dr β σ κ ρr y = Dr β σ κ ρr x + κ * (y - x) := by
    unfold Dr
    ring
  refine ⟨div_pos hDx hSx, ?_⟩
  rw [div_le_div_iff₀ hSx hSy, hDy]
  have : 0 ≤ κ * (y - x) := mul_nonneg hκ.le (by linarith)
  nlinarith

/-- Galí (2015), Exercise 4.2(c): `h` is strictly increasing on `[1, ∞)`. -/
theorem hcrit_strictMonoOn {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) :
    StrictMonoOn (hcrit β σ κ ρr) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx' : (1 : ℝ) ≤ x := hx
  have hy' : (1 : ℝ) ≤ y := hy
  obtain ⟨hq0, hq⟩ := ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 hx' hxy.le
  have hqy : 0 < Dr β σ κ ρr y / (σ + κ * y) := (ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0
    hβ1 hρ0 hρ1 hy' le_rfl).1
  have h3 : (Dr β σ κ ρr x / (σ + κ * x)) ^ 3 ≤ (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 :=
    pow_le_pow_left₀ hq0.le hq 3
  have h3y : 0 < (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 := pow_pos hqy 3
  unfold hcrit
  calc x * (Dr β σ κ ρr x / (σ + κ * x)) ^ 3 ≤ x * (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ < y * (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 := mul_lt_mul_of_pos_right hxy h3y

/-- Galí (2015), Exercise 4.2(c): `h(φ) ≥ φ h(1)` for `φ ≥ 1`, so `h` is unbounded. -/
theorem hcrit_ge {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hφ : 1 ≤ φ) :
    φ * hcrit β σ κ ρr 1 ≤ hcrit β σ κ ρr φ := by
  obtain ⟨hq0, hq⟩ := ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 le_rfl hφ
  unfold hcrit
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0.le hq 3) (by linarith)

/-- Galí (2015), Exercise 4.2(c): `h(1) > 0`. -/
theorem hcrit_one_pos {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) : 0 < hcrit β σ κ ρr 1 := by
  unfold hcrit
  rw [one_mul]
  exact pow_pos (ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 le_rfl le_rfl).1 3

/-- Galí (2015), Exercise 4.2(c): `h` is continuous on `[1, ∞)`. -/
theorem hcrit_continuousOn {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ContinuousOn (hcrit β σ κ ρr) (Set.Ici 1) := by
  unfold hcrit Dr
  apply ContinuousOn.mul continuousOn_id
  apply ContinuousOn.pow
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : (1 : ℝ) ≤ x := hx
  have : 0 < σ + κ * x := by nlinarith
  exact this.ne'

/-- **The derivative of the inflation variance** (Galí 2015, Exercise 4.2(c)):
`V'(φ) = 2κ² (σ var ξ · h(φ) − κ var r̂)/D_r(φ)³` wherever `D_r(φ) ≠ 0 ≠ σ + κ φ`. -/
theorem hasDerivAt_varInfl {β σ κ ρr sr sξ x : ℝ} (hD : Dr β σ κ ρr x ≠ 0)
    (hS : σ + κ * x ≠ 0) :
    HasDerivAt (varInfl β σ κ ρr sr sξ)
      (2 * κ ^ 2 * (σ * sξ * hcrit β σ κ ρr x - κ * sr) / Dr β σ κ ρr x ^ 3) x := by
  have hDr : HasDerivAt (fun y => Dr β σ κ ρr y) κ x := by
    have := (((hasDerivAt_id' x).sub_const ρr).const_mul κ).const_add
      ((1 - β * ρr) * σ * (1 - ρr))
    simpa [Dr] using this
  have hS' : HasDerivAt (fun y => σ + κ * y) κ x := by
    simpa using ((hasDerivAt_id' x).const_mul κ).const_add σ
  have hN : HasDerivAt (fun y => -κ * y) (-κ) x := by
    simpa using (hasDerivAt_id' x).const_mul (-κ)
  have hA := (hasDerivAt_const x κ).fun_div hDr hD
  have hX := hN.fun_div hS' hS
  have hV := ((hA.mul hA).mul_const sr).add ((hX.mul hX).mul_const sξ)
  have hfun : varInfl β σ κ ρr sr sξ = fun y => κ / Dr β σ κ ρr y * (κ / Dr β σ κ ρr y) * sr
      + -κ * y / (σ + κ * y) * (-κ * y / (σ + κ * y)) * sξ := by
    funext y
    unfold varInfl aR aXi
    ring
  rw [hfun]
  refine hV.congr_deriv ?_
  unfold hcrit
  field_simp
  ring

/-- Galí (2015), Exercise 4.2(c): `V` is continuous on `[1, ∞)`. -/
theorem varInfl_continuousOn {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (s : Set ℝ) (hs : s ⊆ Set.Ici 1) :
    ContinuousOn (varInfl β σ κ ρr sr sξ) s := by
  intro x hx
  have hx' : (1 : ℝ) ≤ x := hs hx
  have hD := (Dr_pos hσ hκ hβ0 hβ1 hρ1 hx').ne'
  have hS : σ + κ * x ≠ 0 := by nlinarith
  exact (hasDerivAt_varInfl (sr := sr) (sξ := sξ) hD hS).continuousAt.continuousWithinAt

/-- Galí (2015), Exercise 4.2(c): the sign of `V'` on `(1, ∞)` is the sign of
`σ var ξ · h(φ) − κ var r̂`. -/
theorem deriv_varInfl_eq {β σ κ ρr sr sξ x : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hx : 1 ≤ x) :
    deriv (varInfl β σ κ ρr sr sξ) x
      = 2 * κ ^ 2 * (σ * sξ * hcrit β σ κ ρr x - κ * sr) / Dr β σ κ ρr x ^ 3 ∧
      0 < 2 * κ ^ 2 / Dr β σ κ ρr x ^ 3 := by
  have hDp := Dr_pos hσ hκ hβ0 hβ1 hρ1 hx
  have hS : σ + κ * x ≠ 0 := by nlinarith
  exact ⟨(hasDerivAt_varInfl hDp.ne' hS).deriv, by positivity⟩

/-- **Exercise 4.2(c), interior optimum** (Galí 2015, p. 121): let `var ξ > 0` and
`σ var ξ · h(1) < κ var r̂`. Then there is a unique `φ* > 1` with
`σ var ξ · h(φ*) = κ var r̂`, and `φ*` is the unique minimiser of `var π` over the
determinacy region `φ_π > 1`. -/
theorem ex4_2c_interior {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hsξ : 0 < sξ)
    (hlt : σ * sξ * hcrit β σ κ ρr 1 < κ * sr) :
    ∃ φs, 1 < φs ∧ σ * sξ * hcrit β σ κ ρr φs = κ * sr ∧
      (∀ φ, 1 < φ → σ * sξ * hcrit β σ κ ρr φ = κ * sr → φ = φs) ∧
      ∀ φ, 1 < φ → φ ≠ φs → varInfl β σ κ ρr sr sξ φs < varInfl β σ κ ρr sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have h1pos := hcrit_one_pos (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hmono := hcrit_strictMonoOn (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hg : StrictMonoOn (fun φ => σ * sξ * hcrit β σ κ ρr φ) (Set.Ici 1) :=
    fun x hx y hy hxy => mul_lt_mul_of_pos_left (hmono hx hy hxy) hss
  -- a point where `σ var ξ · h ≥ κ var r̂`
  set M := max 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1)) + 1 with hM
  have hM1 : 1 ≤ M := by
    have := le_max_left 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1))
    linarith
  have hMge : κ * sr ≤ σ * sξ * hcrit β σ κ ρr M := by
    have hge := hcrit_ge (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 hM1
    have hpos : 0 < σ * sξ * hcrit β σ κ ρr 1 := mul_pos hss h1pos
    have hM2 : κ * sr / (σ * sξ * hcrit β σ κ ρr 1) ≤ M := by
      have := le_max_right 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1))
      linarith
    rw [div_le_iff₀ hpos] at hM2
    nlinarith
  have hcont : ContinuousOn (fun φ => σ * sξ * hcrit β σ κ ρr φ) (Set.Icc 1 M) :=
    ((hcrit_continuousOn hσ hκ).mono Set.Icc_subset_Ici_self).const_smul (σ * sξ)
  obtain ⟨φs, ⟨hφs1, -⟩, hφs⟩ := intermediate_value_Icc hM1 hcont ⟨hlt.le, hMge⟩
  have hφs1' : 1 < φs := by
    rcases hφs1.lt_or_eq with h | h
    · exact h
    · subst h
      simp only at hφs
      linarith
  refine ⟨φs, hφs1', hφs, fun φ hφ hφeq => ?_, fun φ hφ hne => ?_⟩
  · exact hg.injOn (Set.mem_Ici.mpr hφ.le) (Set.mem_Ici.mpr hφs1) (hφeq.trans hφs.symm)
  · -- `V` decreases on `[1, φ*]` and increases on `[φ*, ∞)`
    have hanti : StrictAntiOn (varInfl β σ κ ρr sr sξ) (Set.Icc 1 φs) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 1 φs)
        (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ Set.Icc_subset_Ici_self) fun x hx => ?_
      rw [interior_Icc] at hx
      obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1
        hx.1.le
      have hlt' : σ * sξ * hcrit β σ κ ρr x < κ * sr := by
        rw [← hφs]
        exact hg (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hφs1) hx.2
      rw [hd, mul_div_right_comm]
      exact mul_neg_of_pos_of_neg hp (by linarith)
    have hmono' : StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici φs) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici φs)
        (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ (Set.Ici_subset_Ici.mpr hφs1)) fun x hx => ?_
      rw [interior_Ici] at hx
      have hx' : φs < x := hx
      obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1
        (hφs1.trans hx'.le)
      have hgt : κ * sr < σ * sξ * hcrit β σ κ ρr x := by
        rw [← hφs]
        exact hg (Set.mem_Ici.mpr hφs1) (Set.mem_Ici.mpr (hφs1.trans hx'.le)) hx'
      rw [hd, mul_div_right_comm]
      exact mul_pos hp (by linarith)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hanti ⟨hφ.le, h.le⟩ ⟨hφs1, le_rfl⟩ h
    · exact hmono' ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr h.le) h

/-- **Exercise 4.2(c), corner case** (Galí 2015, p. 121): if `var ξ > 0` and
`κ var r̂ ≤ σ var ξ · h(1)`, then `var π` is strictly increasing on `[1, ∞)`, so it has no
minimiser on the determinacy region `φ_π > 1`: every `φ_π > 1` is beaten by a smaller one. -/
theorem ex4_2c_corner {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hsξ : 0 < sξ)
    (hge : κ * sr ≤ σ * sξ * hcrit β σ κ ρr 1) :
    StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici 1) ∧
      ∀ φ, 1 < φ → ∃ φ', 1 < φ' ∧ φ' < φ ∧
        varInfl β σ κ ρr sr sξ φ' < varInfl β σ κ ρr sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have hmono := hcrit_strictMonoOn (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hV : StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1)
      (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ le_rfl) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx' : 1 < x := hx
    obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1 hx'.le
    have hgt : σ * sξ * hcrit β σ κ ρr 1 < σ * sξ * hcrit β σ κ ρr x :=
      mul_lt_mul_of_pos_left (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx'.le) hx') hss
    rw [hd, mul_div_right_comm]
    exact mul_pos hp (by linarith)
  refine ⟨hV, fun φ hφ => ⟨(1 + φ) / 2, by linarith, by linarith, ?_⟩⟩
  exact hV (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hφ.le) (by linarith)

/-- **Exercise 4.2(c), no measurement error** (Galí 2015, p. 121 and fn. 10, p. 114): if
`var ξ = 0`, `var r̂ > 0` and `ρ_r < 1`, then `var π` is strictly decreasing on `[1, ∞)`
and tends to `0` as `φ_π → ∞`; there is no minimiser. -/
theorem ex4_2c_no_noise {β σ κ ρr sr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hsr : 0 < sr) :
    StrictAntiOn (varInfl β σ κ ρr sr 0) (Set.Ici 1) ∧
      Tendsto (varInfl β σ κ ρr sr 0) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · refine strictAntiOn_of_deriv_neg (convex_Ici 1)
      (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ le_rfl) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx' : 1 < x := hx
    obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := 0) hσ hκ hβ0 hβ1 hρ1 hx'.le
    rw [hd, mul_div_right_comm]
    exact mul_neg_of_pos_of_neg hp (by nlinarith)
  · have h := (ex4_2b_coefficients β ρr hκ (σ := σ)).1
    have := (h.pow 2).mul_const sr
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    refine this.congr fun φ => ?_
    simp [varInfl]

/-- Galí (2015), Exercise 4.2(c), hint (`ρ_r = 0`): then `h(φ) = φ`. -/
theorem hcrit_iid {β σ κ φ : ℝ} (hS : σ + κ * φ ≠ 0) : hcrit β σ κ 0 φ = φ := by
  unfold hcrit Dr
  have : (1 - β * 0) * σ * (1 - 0) + κ * (φ - 0) = σ + κ * φ := by ring
  rw [this, div_self hS, one_pow, mul_one]

/-- **Exercise 4.2(c), i.i.d. natural rate** (Galí 2015, p. 121, hint `ρ_r = 0`): with
`var ξ > 0` and `φ* = κ var r̂/(σ var ξ) > 1`, `φ*` is the unique minimiser of `var π` over
`φ_π > 1`. -/
theorem ex4_2c_iid {β σ κ sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsξ : 0 < sξ) (h1 : 1 < κ * sr / (σ * sξ)) :
    ∀ φ, 1 < φ → φ ≠ κ * sr / (σ * sξ) →
      varInfl β σ κ 0 sr sξ (κ * sr / (σ * sξ)) < varInfl β σ κ 0 sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have hlt : σ * sξ * hcrit β σ κ 0 1 < κ * sr := by
    rw [hcrit_iid (by positivity), mul_one]
    rwa [one_lt_div hss] at h1
  obtain ⟨φs, hφs1, hφs, huniq, hmin⟩ := ex4_2c_interior hσ hκ hβ0 hβ1 le_rfl one_pos hsξ hlt
  have hK : σ * sξ * hcrit β σ κ 0 (κ * sr / (σ * sξ)) = κ * sr := by
    rw [hcrit_iid (by positivity)]
    field_simp
  have heq : κ * sr / (σ * sξ) = φs := huniq _ h1 hK
  rw [heq]
  intro φ hφ hne
  exact hmin φ hφ hne

end Gali.MonetaryPolicyDesign.Ex4_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.3: monetary policy and the effects of technology shocks

Galí (2015), Chapter 4, Exercise 4.3, pp. 121–122. The economy is
`y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ)`, `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`,
with the rule `i_t = ρ + φ_π π_t` (`φ_π > 1`), labour productivity `y_t − n_t = a_t`, technology
an AR(1) with persistence `ρ_a ∈ [0, 1)`, and natural output `y^n_t = ψ_y a_t` with `ψ_y > 1`.

Write `c = (1 − βρ_a) σ (1 − ρ_a) > 0` and `D = c + κ (φ_π − ρ_a)`.

## Main results

* **(a)** `ex4_3a_equilibrium_iff`: the unique equilibrium with bounded adapted output,
  inflation and employment is `y_t = γ_y a_t`, `π_t = γ_π a_t`, `n_t = γ_n a_t` with
  `γ_y = ψ_y κ (φ_π − ρ_a)/D`, `γ_π = −σ ψ_y (1 − ρ_a) κ/D`, `γ_n = γ_y − 1`
  (`gammaN_eq`: `γ_n = ((ψ_y − 1) κ (φ_π − ρ_a) − c)/D`).
* **(b)** `gammaY_mem`, `gammaPi_neg`: `0 < γ_y < ψ_y`, `γ_π < 0`. `ex4_3b_mono_phi`,
  `ex4_3b_mono_kappa`: `γ_y`, `γ_n` increase and `γ_π` rises towards `0` as `φ_π` increases;
  `γ_y`, `γ_n` increase and `γ_π` falls as `κ` increases (less price rigidity).
  `ex4_3b_phi_infty`: as `φ_π → ∞`, `γ_y → ψ_y`, `γ_π → 0`, `γ_n → ψ_y − 1` (the natural
  allocation). `ex4_3b_kappa_infty`: as `κ → ∞` (flexible prices), `γ_y → ψ_y`,
  `γ_n → ψ_y − 1`, `γ_π → −σ ψ_y (1 − ρ_a)/(φ_π − ρ_a)`. `ex4_3b_kappa_zero`: as `κ → 0`
  (fully rigid prices), `γ_y → 0`, `γ_π → 0`, `γ_n → −1`.
* **(c)** `ex4_3c_sign`: employment rises after a positive technology shock iff
  `(ψ_y − 1) κ (φ_π − ρ_a) > c`, and falls iff `<`. `ex4_3c_both_signs`: both occur
  (small `κ` gives a fall, large `φ_π` a rise). `ex4_3c_covariance`: the conditional
  covariance of output and employment is `γ_y γ_n var a`, so it has the sign of `γ_n`.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_3

open Filter Topology Gali.MonetaryPolicyDesign.Ex4_1

/-! ### The MSV coefficients -/

/-- Galí (2015), Exercise 4.3(a): `c = (1 − βρ_a) σ (1 − ρ_a)`. -/
def cA (β σ ρa : ℝ) : ℝ := (1 - β * ρa) * σ * (1 - ρa)

/-- Galí (2015), Exercise 4.3(a): the denominator `D = (1 − βρ_a) σ (1 − ρ_a) + κ (φ_π − ρ_a)`. -/
def Da (β σ κ ρa φ : ℝ) : ℝ := cA β σ ρa + κ * (φ - ρa)

/-- Galí (2015), Exercise 4.3(a): the output response `γ_y = ψ_y κ (φ_π − ρ_a)/D`. -/
noncomputable def gammaY (β σ κ ρa ψy φ : ℝ) : ℝ := ψy * (κ * (φ - ρa)) / Da β σ κ ρa φ

/-- Galí (2015), Exercise 4.3(a): the inflation response `γ_π = −σ ψ_y (1 − ρ_a) κ/D`. -/
noncomputable def gammaPi (β σ κ ρa ψy φ : ℝ) : ℝ := -(σ * ψy * (1 - ρa)) * κ / Da β σ κ ρa φ

/-- Galí (2015), Exercise 4.3(a): the employment response `γ_n = γ_y − 1`. -/
noncomputable def gammaN (β σ κ ρa ψy φ : ℝ) : ℝ := gammaY β σ κ ρa ψy φ - 1

/-- Galí (2015), Exercise 4.3: `c > 0`. -/
theorem cA_pos {β σ ρa : ℝ} (hσ : 0 < σ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa)
    (hρ1 : ρa < 1) : 0 < cA β σ ρa := by
  unfold cA
  have h1 : 0 < 1 - β * ρa := by nlinarith
  exact mul_pos (mul_pos h1 hσ) (by linarith)

/-- Galí (2015), Exercise 4.3: `D > 0` whenever `κ ≥ 0` and `φ_π ≥ ρ_a`. -/
theorem Da_pos {β σ κ ρa φ : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : ρa ≤ φ) : 0 < Da β σ κ ρa φ := by
  unfold Da
  have := cA_pos hσ hβ1 hρ0 hρ1
  have : 0 ≤ κ * (φ - ρa) := mul_nonneg hκ (by linarith)
  linarith

/-- Galí (2015), Exercise 4.3(c): `γ_n = ((ψ_y − 1) κ (φ_π − ρ_a) − c)/D`. -/
theorem gammaN_eq {β σ κ ρa ψy φ : ℝ} (hD : Da β σ κ ρa φ ≠ 0) :
    gammaN β σ κ ρa ψy φ = ((ψy - 1) * (κ * (φ - ρa)) - cA β σ ρa) / Da β σ κ ρa φ := by
  unfold gammaN gammaY
  field_simp
  unfold Da
  ring

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 4.3, pp. 121–122: an equilibrium: the DIS equation in output, the
NKPC with `y^n_t = ψ_y a_t`, the rule `i_t = ρ + φ_π π_t`, and `y_t − n_t = a_t`. -/
def Equilibrium (β σ κ ρ ψy φ : ℝ) (a y infl n i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)) ∧
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - ψy • a t)) ∧
  (∀ t, i t = (fun _ => ρ) + φ • infl t) ∧
  (∀ t, y t - n t = a t)

/-- Galí (2015), Exercise 4.3: the equilibrium conditions are the structural system of the
output gap `ỹ = y − ψ_y a` (with `φ_y = 0` and forcing `u_t = −σ ψ_y (1 − ρ_a) a_t`), the
rule, and `n_t = y_t − a_t`. -/
theorem equilibrium_iff {β σ κ ρ ρa ψy φ : ℝ} (hσ : σ ≠ 0) {a y infl n i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a y infl n i ↔
      Structural 𝔼 β σ κ φ 0 (fun t => (-(σ * ψy * (1 - ρa))) • a t)
        (fun t => y t - ψy • a t) infl ∧
      (∀ t, i t = (fun _ => ρ) + φ • infl t) ∧ (∀ t, n t = y t - a t) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hd, hp, hr, hn⟩
    refine ⟨fun t => ⟨?_, ?_⟩, hr, fun t => by rw [← hn t]; abel⟩
    · funext ω
      have e := congrFun (hd t) ω
      have r := congrFun (hr t) ω
      have ea := congrFun (ha.2 t) ω
      simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at e r ea ⊢
      rw [ea]
      linear_combination σ * e - (i t ω - 𝔼.E t (infl (t + 1)) ω - ρ) * hinv - r
    · rw [hp t]
  · rintro ⟨hs, hr, hn⟩
    refine ⟨fun t => ?_, fun t => (hs t).2, hr, fun t => by rw [hn t]; abel⟩
    funext ω
    have e := congrFun (hs t).1 ω
    have r := congrFun (hr t) ω
    have ea := congrFun (ha.2 t) ω
    simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ea ⊢
    rw [ea] at e
    linear_combination σ⁻¹ * e + σ⁻¹ * r - (y t ω - 𝔼.E t (y (t + 1)) ω) * hinv

/-- Galí (2015), Exercise 4.3(a): the MSV processes solve the structural system. -/
theorem msv_structural {β σ κ ρa ψy φ : ℝ} (hD : Da β σ κ ρa φ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    Structural 𝔼 β σ κ φ 0 (fun t => (-(σ * ψy * (1 - ρa))) • a t)
      (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t)
      (fun t => gammaPi β σ κ ρa ψy φ • a t) := by
  have c1 : (σ + 0) * (gammaY β σ κ ρa ψy φ - ψy) + φ * gammaPi β σ κ ρa ψy φ
      = σ * ((gammaY β σ κ ρa ψy φ - ψy) * ρa) + gammaPi β σ κ ρa ψy φ * ρa
        - σ * ψy * (1 - ρa) := by
    unfold gammaY gammaPi
    field_simp
    unfold Da cA
    ring
  have c2 : gammaPi β σ κ ρa ψy φ
      = β * (gammaPi β σ κ ρa ψy φ * ρa) + κ * (gammaY β σ κ ρa ψy φ - ψy) := by
    unfold gammaY gammaPi
    field_simp
    unfold Da cA
    ring
  intro t
  simp only [map_sub, map_smul, ha.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a t ω * c1
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a t ω * c2

/-- **Exercise 4.3(a)** (Galí 2015, p. 122): for `σ, κ > 0`, `0 < β < 1`, `0 ≤ ρ_a < 1` and
`φ_π > 1`, with bounded AR(1) technology, a tuple `(y, π, n, i)` with bounded adapted
`y, π, n` is an equilibrium iff `y_t = γ_y a_t`, `π_t = γ_π a_t`, `n_t = γ_n a_t` and
`i_t = ρ + φ_π π_t`. The MSV tuple is bounded and adapted, so it is the unique such
equilibrium (`ex4_3a_exists`). -/
theorem ex4_3a_equilibrium_iff {β σ κ ρ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : 1 < φ) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {y infl n i : ℕ → Ω → ℝ}
    (hay : 𝔼.Adapted y) (hai : 𝔼.Adapted infl) (hby : BoundedProc y)
    (hbi : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a y infl n i ↔
      y = (fun t => gammaY β σ κ ρa ψy φ • a t) ∧
      infl = (fun t => gammaPi β σ κ ρa ψy φ • a t) ∧
      n = (fun t => gammaN β σ κ ρa ψy φ • a t) ∧
      i = fun t => (fun _ => ρ) + φ • infl t := by
  have hD := (Da_pos hσ hκ.le hβ1 hρ0 hρ1 (by linarith) (φ := φ)).ne'
  rw [equilibrium_iff 𝔼 hσ.ne' ha]
  have hgapA : 𝔼.Adapted (fun t => y t - ψy • a t) :=
    fun t => by simp only [map_sub, map_smul, hay t, ha.1 t]
  have hgapB : BoundedProc (fun t => y t - ψy • a t) := by
    have := Ex4_2.bounded_comb hby hab 1 (-ψy)
    simpa [sub_eq_add_neg, neg_smul] using this
  have hmA : 𝔼.Adapted (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t) :=
    fun t => by simp only [map_sub, map_smul, ha.1 t]
  have hmB : BoundedProc (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t) := by
    have := Ex4_2.bounded_comb hab hab (gammaY β σ κ ρa ψy φ) (-ψy)
    simpa [sub_eq_add_neg, neg_smul] using this
  constructor
  · rintro ⟨hs, hr, hn⟩
    obtain ⟨h1, h2⟩ := structural_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
      (by nlinarith) hs (msv_structural 𝔼 hD ha) hgapA hai hmA (isAR1_smul 𝔼 ha _).1 hgapB
      hbi hmB (boundedProc_smul hab _)
    have hy : y = fun t => gammaY β σ κ ρa ψy φ • a t := by
      funext t
      have := congrFun h1 t
      simpa using this
    refine ⟨hy, h2, ?_, funext hr⟩
    funext t
    rw [hn t, hy]
    simp only [gammaN, sub_smul, one_smul]
  · rintro ⟨hy, hp, hn, hi⟩
    refine ⟨?_, fun t => by rw [hi], fun t => ?_⟩
    · rw [hy, hp]
      exact msv_structural 𝔼 hD ha
    · rw [hn, hy]
      simp only [gammaN, sub_smul, one_smul]

/-- **Exercise 4.3(a), existence** (Galí 2015, p. 122): whenever `D ≠ 0` the MSV tuple is an
equilibrium. -/
theorem ex4_3a_exists {β σ κ ρ ρa ψy φ : ℝ} (hσ : σ ≠ 0) (hD : Da β σ κ ρa φ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a (fun t => gammaY β σ κ ρa ψy φ • a t)
      (fun t => gammaPi β σ κ ρa ψy φ • a t) (fun t => gammaN β σ κ ρa ψy φ • a t)
      (fun t => (fun _ => ρ) + φ • (gammaPi β σ κ ρa ψy φ • a t)) := by
  rw [equilibrium_iff 𝔼 hσ ha]
  refine ⟨msv_structural 𝔼 hD ha, fun _ => rfl, fun t => ?_⟩
  simp only [gammaN, sub_smul, one_smul]

/-! ### Exercise 4.3(b): dependence on `φ_π` and `κ` -/

/-- Galí (2015), Exercise 4.3(b): `0 < γ_y < ψ_y` for `κ > 0`, `φ_π > ρ_a`. -/
theorem gammaY_mem {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa < φ) :
    0 < gammaY β σ κ ρa ψy φ ∧ gammaY β σ κ ρa ψy φ < ψy := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hx : 0 < κ * (φ - ρa) := mul_pos hκ (by linarith)
  have hD : 0 < Da β σ κ ρa φ := by unfold Da; linarith
  unfold gammaY
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hD]
  unfold Da
  nlinarith

/-- Galí (2015), Exercise 4.3(b): `γ_π < 0`: a positive technology shock lowers inflation. -/
theorem gammaPi_neg {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa ≤ φ) :
    gammaPi β σ κ ρa ψy φ < 0 := by
  have hD := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hφ
  unfold gammaPi
  apply div_neg_of_neg_of_pos _ hD
  have : 0 < σ * ψy * (1 - ρa) := mul_pos (mul_pos hσ hψ) (by linarith)
  nlinarith

/-- **Exercise 4.3(b), dependence on `φ_π`** (Galí 2015, p. 122): on `φ_π > ρ_a`, the output
and employment responses are strictly increasing in `φ_π` and the inflation response is
strictly increasing (towards zero). -/
theorem ex4_3b_mono_phi {β σ κ ρa ψy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) :
    StrictMonoOn (gammaY β σ κ ρa ψy) (Set.Ioi ρa) ∧
      StrictMonoOn (gammaN β σ κ ρa ψy) (Set.Ioi ρa) ∧
      StrictMonoOn (gammaPi β σ κ ρa ψy) (Set.Ioi ρa) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hY : StrictMonoOn (gammaY β σ κ ρa ψy) (Set.Ioi ρa) := by
    intro x hx z hz hxz
    have hx' : ρa < x := hx
    have hz' : ρa < z := hz
    have hDx := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hx'.le (φ := x)
    have hDz := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hz'.le (φ := z)
    unfold gammaY
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < κ * (z - x) := mul_pos hκ (by linarith)
    have : 0 < ψy * cA β σ ρa * (κ * (z - x)) := by positivity
    nlinarith
  refine ⟨hY, fun x hx z hz hxz => ?_, fun x hx z hz hxz => ?_⟩
  · unfold gammaN
    linarith [hY hx hz hxz]
  · have hx' : ρa < x := hx
    have hz' : ρa < z := hz
    have hDx := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hx'.le (φ := x)
    have hDz := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hz'.le (φ := z)
    unfold gammaPi
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < σ * ψy * (1 - ρa) * κ := mul_pos (mul_pos (mul_pos hσ hψ) (by linarith)) hκ
    have : 0 < σ * ψy * (1 - ρa) * κ * (κ * (z - x)) := mul_pos this (mul_pos hκ (by linarith))
    nlinarith

/-- **Exercise 4.3(b), dependence on `κ`** (Galí 2015, p. 122): for `φ_π > ρ_a`, on `κ > 0`
the output and employment responses are strictly increasing in `κ` (less rigid prices) and
the inflation response is strictly decreasing (more negative). -/
theorem ex4_3b_mono_kappa {β σ ρa ψy φ : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa < φ) :
    StrictMonoOn (fun κ => gammaY β σ κ ρa ψy φ) (Set.Ioi 0) ∧
      StrictMonoOn (fun κ => gammaN β σ κ ρa ψy φ) (Set.Ioi 0) ∧
      StrictAntiOn (fun κ => gammaPi β σ κ ρa ψy φ) (Set.Ioi 0) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hm : 0 < φ - ρa := by linarith
  have hY : StrictMonoOn (fun κ => gammaY β σ κ ρa ψy φ) (Set.Ioi 0) := by
    intro x hx z hz hxz
    have hx' : (0 : ℝ) < x := hx
    have hz' : (0 : ℝ) < z := hz
    have hDx := Da_pos hσ hx'.le hβ1 hρ0 hρ1 hφ.le
    have hDz := Da_pos hσ hz'.le hβ1 hρ0 hρ1 hφ.le
    simp only [gammaY]
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < ψy * cA β σ ρa * ((z - x) * (φ - ρa)) := by
      have : 0 < (z - x) * (φ - ρa) := mul_pos (by linarith) hm
      positivity
    nlinarith
  refine ⟨hY, fun x hx z hz hxz => ?_, fun x hx z hz hxz => ?_⟩
  · simp only [gammaN]
    linarith [hY hx hz hxz]
  · have hx' : (0 : ℝ) < x := hx
    have hz' : (0 : ℝ) < z := hz
    have hDx := Da_pos hσ hx'.le hβ1 hρ0 hρ1 hφ.le
    have hDz := Da_pos hσ hz'.le hβ1 hρ0 hρ1 hφ.le
    simp only [gammaPi]
    rw [div_lt_div_iff₀ hDz hDx]
    unfold Da
    have : 0 < σ * ψy * (1 - ρa) * cA β σ ρa * (z - x) :=
      mul_pos (mul_pos (mul_pos (mul_pos hσ hψ) (by linarith)) hc) (by linarith)
    nlinarith

/-- **Exercise 4.3(b), strict inflation targeting** (Galí 2015, p. 122): as `φ_π → ∞`,
`γ_y → ψ_y`, `γ_π → 0` and `γ_n → ψ_y − 1`: the natural (flexible-price) allocation. -/
theorem ex4_3b_phi_infty (β σ ρa ψy : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (gammaY β σ κ ρa ψy) atTop (𝓝 ψy) ∧
      Tendsto (gammaPi β σ κ ρa ψy) atTop (𝓝 0) ∧
      Tendsto (gammaN β σ κ ρa ψy) atTop (𝓝 (ψy - 1)) := by
  set c := cA β σ ρa
  have hDa : ∀ φ, Da β σ κ ρa φ = (c - κ * ρa) + κ * φ := fun φ => by
    unfold Da
    ring
  have hev : ∀ᶠ φ in atTop, 0 < (c - κ * ρa) + κ * φ :=
    (tendsto_atTop_add_const_left _ (c - κ * ρa)
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
  have hY : Tendsto (gammaY β σ κ ρa ψy) atTop (𝓝 ψy) := by
    have := (Ex4_2.tendsto_div_affine (-(ψy * c)) (c - κ * ρa) hκ).const_add ψy
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hD := mul_inv_cancel₀ hφ.ne'
    simp only [gammaY, hDa]
    linear_combination -ψy * hD
  refine ⟨hY, ?_, ?_⟩
  · have := Ex4_2.tendsto_div_affine (-(σ * ψy * (1 - ρa)) * κ) (c - κ * ρa) hκ
    refine this.congr fun φ => ?_
    simp only [gammaPi, hDa]
  · exact hY.sub_const 1

/-- **Exercise 4.3(b), flexible prices** (Galí 2015, p. 122): for `φ_π > ρ_a`, as `κ → ∞`,
`γ_y → ψ_y`, `γ_n → ψ_y − 1` and `γ_π → −σ ψ_y (1 − ρ_a)/(φ_π − ρ_a)`. -/
theorem ex4_3b_kappa_infty (β σ ρa ψy : ℝ) {φ : ℝ} (hφ : ρa < φ) :
    Tendsto (fun κ => gammaY β σ κ ρa ψy φ) atTop (𝓝 ψy) ∧
      Tendsto (fun κ => gammaN β σ κ ρa ψy φ) atTop (𝓝 (ψy - 1)) ∧
      Tendsto (fun κ => gammaPi β σ κ ρa ψy φ) atTop
        (𝓝 (-(σ * ψy * (1 - ρa)) / (φ - ρa))) := by
  set c := cA β σ ρa
  have hm : 0 < φ - ρa := by linarith
  have hDa : ∀ κ, Da β σ κ ρa φ = c + (φ - ρa) * κ := fun κ => by
    unfold Da
    ring
  have hev : ∀ᶠ κ in atTop, 0 < c + (φ - ρa) * κ :=
    (tendsto_atTop_add_const_left _ c
      (Tendsto.const_mul_atTop hm tendsto_id)).eventually_gt_atTop 0
  have hY : Tendsto (fun κ => gammaY β σ κ ρa ψy φ) atTop (𝓝 ψy) := by
    have := (Ex4_2.tendsto_div_affine (-(ψy * c)) c hm).const_add ψy
    rw [add_zero] at this
    refine this.congr' (hev.mono fun κ hκ => ?_)
    have hD := mul_inv_cancel₀ hκ.ne'
    simp only [gammaY, hDa]
    linear_combination -ψy * hD
  refine ⟨hY, hY.sub_const 1, ?_⟩
  have := (Ex4_2.tendsto_div_affine (σ * ψy * (1 - ρa) * c / (φ - ρa)) c hm).const_add
    (-(σ * ψy * (1 - ρa)) / (φ - ρa))
  rw [add_zero] at this
  refine this.congr' (hev.mono fun κ hκ => ?_)
  have hD := mul_inv_cancel₀ hκ.ne'
  have hM := mul_inv_cancel₀ hm.ne'
  simp only [gammaPi, hDa]
  linear_combination σ * ψy * (1 - ρa) * (φ - ρa)⁻¹ * hD
    - σ * ψy * (1 - ρa) * κ * (c + (φ - ρa) * κ)⁻¹ * hM

/-- **Exercise 4.3(b), fully rigid prices** (Galí 2015, p. 122): as `κ → 0`, `γ_y → 0`,
`γ_π → 0` and `γ_n → −1`: output does not respond and employment falls one for one. -/
theorem ex4_3b_kappa_zero {β σ ρa ψy φ : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) :
    Tendsto (fun κ => gammaY β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun κ => gammaPi β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun κ => gammaN β σ κ ρa ψy φ) (𝓝 0) (𝓝 (-1)) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hden : Tendsto (fun κ : ℝ => Da β σ κ ρa φ) (𝓝 0) (𝓝 (cA β σ ρa)) := by
    have := (tendsto_const_nhds (x := cA β σ ρa)).add
      ((tendsto_id (x := (𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := φ - ρa)))
    simp only [id, zero_mul, add_zero] at this
    exact this
  have hY : Tendsto (fun κ => gammaY β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) := by
    have hnum : Tendsto (fun κ : ℝ => ψy * (κ * (φ - ρa))) (𝓝 0) (𝓝 0) := by
      have := (tendsto_const_nhds (x := ψy)).mul
        ((tendsto_id (x := (𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := φ - ρa)))
      simpa using this
    have h := hnum.div hden hc.ne'
    rw [zero_div] at h
    exact h
  have hN := hY.sub_const 1
  rw [zero_sub] at hN
  refine ⟨hY, ?_, hN⟩
  have hnum : Tendsto (fun κ : ℝ => -(σ * ψy * (1 - ρa)) * κ) (𝓝 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := -(σ * ψy * (1 - ρa)))).mul
      (tendsto_id (x := (𝓝 (0 : ℝ))))
    simpa using this
  have h := hnum.div hden hc.ne'
  rw [zero_div] at h
  exact h

/-! ### Exercise 4.3(c): the employment response -/

/-- **Exercise 4.3(c)** (Galí 2015, p. 122): for `κ > 0` and `φ_π > ρ_a`, employment rises
after a positive technology shock iff `(ψ_y − 1) κ (φ_π − ρ_a) > (1 − βρ_a) σ (1 − ρ_a)`,
falls iff `<`, and is unchanged iff `=`. -/
theorem ex4_3c_sign {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : ρa ≤ φ) :
    (0 < gammaN β σ κ ρa ψy φ ↔ cA β σ ρa < (ψy - 1) * (κ * (φ - ρa))) ∧
      (gammaN β σ κ ρa ψy φ < 0 ↔ (ψy - 1) * (κ * (φ - ρa)) < cA β σ ρa) ∧
      (gammaN β σ κ ρa ψy φ = 0 ↔ (ψy - 1) * (κ * (φ - ρa)) = cA β σ ρa) := by
  have hD := Da_pos hσ hκ hβ1 hρ0 hρ1 hφ
  rw [gammaN_eq hD.ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pos_iff_of_pos_right hD, sub_pos]
  · rw [div_neg_iff, sub_neg]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · exact h
    · intro h
      exact Or.inr ⟨h, hD⟩
  · rw [div_eq_zero_iff, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · exact Or.inl

/-- **Exercise 4.3(c), both signs occur** (Galí 2015, p. 122): with `ψ_y > 1` and
`φ_π > ρ_a`, employment falls after a positive technology shock when prices are rigid
enough (small `κ > 0`) and rises when policy is aggressive enough (large `φ_π`). -/
theorem ex4_3c_both_signs {β σ ρa ψy : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 1 < ψy) :
    (∀ φ, ρa < φ → ∃ κ, 0 < κ ∧ gammaN β σ κ ρa ψy φ < 0) ∧
      (∀ κ, 0 < κ → ∃ φ, 1 < φ ∧ 0 < gammaN β σ κ ρa ψy φ) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  refine ⟨fun φ hφ => ?_, fun κ hκ => ?_⟩
  · have hm : 0 < (ψy - 1) * (φ - ρa) := mul_pos (by linarith) (by linarith)
    refine ⟨cA β σ ρa / ((ψy - 1) * (φ - ρa)) / 2, by positivity, ?_⟩
    refine ((ex4_3c_sign hσ (by positivity) hβ1 hρ0 hρ1 hφ.le).2.1).mpr ?_
    have : (ψy - 1) * (cA β σ ρa / ((ψy - 1) * (φ - ρa)) / 2 * (φ - ρa))
        = cA β σ ρa / 2 * (((ψy - 1) * (φ - ρa)) / ((ψy - 1) * (φ - ρa))) := by
      ring
    rw [this, div_self hm.ne', mul_one]
    linarith
  · have hk : 0 < (ψy - 1) * κ := mul_pos (by linarith) hκ
    set φ := ρa + 1 + cA β σ ρa / ((ψy - 1) * κ) with hφdef
    have hφ1 : 1 < φ := by
      have : 0 < cA β σ ρa / ((ψy - 1) * κ) := by positivity
      linarith
    refine ⟨φ, hφ1, ((ex4_3c_sign hσ hκ.le hβ1 hρ0 hρ1 (by linarith)).1).mpr ?_⟩
    have : (ψy - 1) * (κ * (φ - ρa))
        = (ψy - 1) * κ + cA β σ ρa * (((ψy - 1) * κ) / ((ψy - 1) * κ)) := by
      rw [hφdef]
      ring
    rw [this, div_self hk.ne', mul_one]
    linarith

/-- **Exercise 4.3(c), comovement** (Galí 2015, p. 122): for a covariance form `B`, in the
MSV equilibrium `cov(y_t, n_t) = γ_y γ_n var a_t`; with `0 < γ_y` (`gammaY_mem`) and
`var a_t > 0` its sign is the sign of `γ_n`, so output and employment move in opposite
directions conditional on technology exactly when `γ_n < 0`. -/
theorem ex4_3c_covariance (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρa ψy φ : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1)
    (hψ : 0 < ψy) (hφ : ρa < φ) (x : Ω → ℝ) (hx : 0 < B x x) :
    B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x)
        = gammaY β σ κ ρa ψy φ * gammaN β σ κ ρa ψy φ * B x x ∧
      (B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x) < 0 ↔
        gammaN β σ κ ρa ψy φ < 0) := by
  have hcov : B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x)
      = gammaY β σ κ ρa ψy φ * gammaN β σ κ ρa ψy φ * B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hY := (gammaY_mem hσ hκ hβ1 hρ0 hρ1 hψ hφ).1
  refine ⟨hcov, ?_⟩
  rw [hcov, mul_comm (gammaY β σ κ ρa ψy φ), mul_assoc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : 0 ≤ gammaN β σ κ ρa ψy φ * (gammaY β σ κ ρa ψy φ * B x x) :=
      mul_nonneg hn (mul_pos hY hx).le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos h (mul_pos hY hx)

end Gali.MonetaryPolicyDesign.Ex4_3

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.4: interest rate versus money supply rules

Galí (2015), Chapter 4, Exercise 4.4, pp. 122–123. The economy is the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`, the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t` and the money demand `m_t − p_t = y_t − η i_t`, with
`y_t = ỹ_t + y^n_t`. The natural rate `r^n` and natural output `y^n` are exogenous; the central
bank minimises `ϑ var(ỹ_t) + var(π_t)`.

## (a) An interest rate rule

* `loss_nonneg`, `loss_zero`, `zero_minimises_loss`: the outcome `ỹ = π = 0` attains the lowest
  possible loss, zero (for every probability law of the outcomes and every `ϑ ≥ 0`).
* `zero_equilibrium_iff`: `ỹ = π = 0` satisfies the IS equation and the Phillips curve iff
  `i_t = r^n_t` (eqs. (4)–(5) and p. 103).
* The rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` (eq. (11)): `rule_iff_solves` writes the equilibrium
  as `x_t = A_T E_t x_{t+1}` with `A_T` of eq. (13); `schurStable_AT_iff`: for `φ_π, φ_y ≥ 0`
  both eigenvalues of `A_T` lie inside the unit circle iff condition (14),
  `κ (φ_π − 1) + (1 − β) φ_y > 0` (restated from the Chapter 3 project).
* `rule_implements`: under (14) the outcome `ỹ = π = 0, i = r^n` is an equilibrium and it is the
  only bounded one; `rule_not_unique`: without (14) there is a second bounded equilibrium;
  `implements_uniquely_iff`: the rule implements the optimum uniquely iff (14) holds.

## (b) The money supply under the optimal policy

* `price_level_const`: with `π = 0` the price level stays at its initial value `p*`.
* `money_path_optimal`: in every equilibrium with `ỹ = π = 0`, `m_t = p* + y^n_t − η r^n_t`.
* `constant_money_suboptimal`: a constant money supply is consistent with the optimum only if
  `y^n_t − η r^n_t` is constant; `constant_money_not_optimal`: when `y^n − η r^n` moves, no
  equilibrium under a constant money supply attains `ỹ = π = 0`.
* `constant_money_optimal_of_const`: conversely, when `y^n − η r^n` is constant, a constant
  money supply supports the optimal outcome.

## (c) A money supply rule that implements the optimum

* `moneyRule_equilibrium`: under the rule `m_t = p* + y^n_t − η r^n_t` the optimal outcome
  (`ỹ = π = 0`, `p = p*`, `i = r^n`) is an equilibrium.
* `moneyRule_iff_interestRule`: given money demand and `η > 0`, the money rule is equivalent to
  the implicit interest rate rule `i_t = r^n_t + η⁻¹ (ỹ_t + p_t − p*)`, a rule responding to the
  output gap and to the price level.
* `MoneyRuleUniqueness`: whether the optimum is the *unique* bounded equilibrium under the money
  rule is a three-variable determinacy question (the price level is predetermined), the one of
  Galí Chapter 3 footnote 14. It is recorded here as a claim and is **not yet claimed**: the
  project defers it.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_4

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Ex. 4.4, p. 122 (eq. (6), p. 104): the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), Ex. 4.4, p. 122 (eq. (7), p. 104): the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), Ex. 4.4, p. 122: the non-policy block, the IS equation and the Phillips curve. -/
def Block (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ rn ygap infl i ∧ NKPC 𝔼 β κ ygap infl

/-! ### (a) The optimal policy and an interest rate rule -/

/-- Galí (2015), Ex. 4.4, p. 122: the central bank's loss `ϑ var(ỹ_t) + var(π_t)` at date `t`,
for a probability law `μ` of the outcomes. -/
noncomputable def loss [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : ℝ) (ygap infl : ℕ → Ω → ℝ)
    (t : ℕ) : ℝ :=
  ϑ * variance (ygap t) μ + variance (infl t) μ

/-- Galí (2015), Ex. 4.4, p. 122: the loss is nonnegative for `ϑ ≥ 0`. -/
theorem loss_nonneg [MeasurableSpace Ω] (μ : Measure Ω) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (ygap infl : ℕ → Ω → ℝ) (t : ℕ) : 0 ≤ loss μ ϑ ygap infl t :=
  add_nonneg (mul_nonneg hϑ (variance_nonneg _ _)) (variance_nonneg _ _)

/-- Galí (2015), Ex. 4.4, p. 122: the outcome `ỹ = π = 0` has zero loss. -/
theorem loss_zero [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : ℝ) (t : ℕ) :
    loss μ ϑ (fun _ => 0) (fun _ => 0) t = 0 := by
  simp [loss, variance_zero]

/-- Galí (2015), Ex. 4.4(a), p. 122, with eqs. (4)–(5), p. 103: the outcome `ỹ = π = 0`
minimises the loss at every date against every other outcome. -/
theorem zero_minimises_loss [MeasurableSpace Ω] (μ : Measure Ω) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (ygap infl : ℕ → Ω → ℝ) (t : ℕ) :
    loss μ ϑ (fun _ => 0) (fun _ => 0) t ≤ loss μ ϑ ygap infl t := by
  rw [loss_zero]; exact loss_nonneg μ hϑ ygap infl t

/-- Galí (2015), eqs. (4)–(5) and p. 103 (Ex. 4.4(a)): the optimal outcome `ỹ = π = 0` satisfies
the IS equation and the Phillips curve if and only if `i_t = r^n_t` for all `t`. -/
theorem zero_equilibrium_iff {β σ κ : ℝ} (hσ : σ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Block 𝔼 β σ κ rn (fun _ => 0) (fun _ => 0) i ↔ i = rn := by
  constructor
  · rintro ⟨hd, -⟩
    funext t ω
    have e := congrFun (hd t) ω
    simp only [map_zero, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e
    have : σ⁻¹ * (i t ω - rn t ω) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (inv_ne_zero hσ)
    linarith
  · rintro rfl
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω; simp
    · funext ω; simp

/-- Galí (2015), eq. (11), p. 105: the interest rate rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`. -/
def Rule (φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • infl t + φy • ygap t

/-- Galí (2015), eq. (13), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105: `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eq. (12): the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (12), p. 105: under rule (11) the IS equation and the Phillips curve hold
iff `x_t = A_T E_t x_{t+1}`, provided `σ ≠ 0` and `σ + φ_y + κ φ_π ≠ 0` (the natural rate drops
out). -/
theorem rule_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hr : Rule φπ φy rn ygap infl i) :
    Block 𝔼 β σ κ rn ygap infl i ↔ 𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hd, hp⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 r
    have e1' : (σ + φy) * ygap t ω + φπ * infl t ω =
        σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
      linear_combination σ * e1 - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AT, omega]
      field_simp
      linear_combination e1' - φπ * e2
    · simp [stack, AT, omega]
      field_simp
      linear_combination κ * e1' + (σ + φy) * e2
  · intro h
    have key : ∀ t ω, (σ + φy) * ygap t ω + φπ * infl t ω =
          σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω ∧
        infl t ω = β * 𝔼.E t (infl (t + 1)) ω + κ * ygap t ω := by
      intro t ω
      have h0 := congrFun (h t 0) ω
      have h1 := congrFun (h t 1) ω
      simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at h0 h1
      field_simp at h0 h1
      constructor
      · apply mul_left_cancel₀ hS
        linear_combination (σ + φy) * h0 + φπ * h1
      · apply mul_left_cancel₀ hS
        linear_combination h1 - κ * h0
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e := (key t ω).1
      have r := congrFun (hr t) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      rw [r]
      field_simp
      linear_combination e
    · have e := (key t ω).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact e

/-- Galí (2015), p. 105: the trace of `A_T` is `(σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 105: the determinant of `A_T` is `σ β/(σ + φ_y + κ φ_π)`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Condition (14)** (Galí 2015, p. 106; Bullard–Mitra): for `σ, κ > 0`, `0 < β < 1` and
`φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit circle iff
`κ (φ_π − 1) + (1 − β) φ_y > 0` (restated from the Chapter 3 project). -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Ex. 4.4(a), pp. 105–106: a bounded adapted equilibrium under rule (11), with
`ỹ`, `π` and `i` all determined. -/
def RuleEquilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σ κ rn ygap infl i ∧ Rule φπ φy rn ygap infl i ∧ 𝔼.Adapted ygap ∧
    𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl

/-- **Ex. 4.4(a)** (Galí 2015, pp. 105–106): under condition (14) the rule
`i_t = r^n_t + φ_π π_t + φ_y ỹ_t` implements the optimal policy: `ỹ = π = 0, i = r^n` is an
equilibrium, and every bounded adapted equilibrium is this one. -/
theorem rule_implements {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (rn : ℕ → Ω → ℝ) :
    RuleEquilibrium 𝔼 β σ κ φπ φy rn (fun _ => 0) (fun _ => 0) rn ∧
      ∀ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i →
        ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ i = rn := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hr0 : Rule φπ φy rn (fun _ => 0) (fun _ => 0) rn := fun t => by simp
  refine ⟨⟨(zero_equilibrium_iff 𝔼 hσ.ne' rn rn).2 rfl, hr0, fun t => map_zero _,
    fun t => map_zero _, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩⟩, ?_⟩
  rintro ygap infl i ⟨hb, hr, ha, hai, hby, hbi⟩
  have hx := (rule_iff_solves 𝔼 hσ.ne' hS hr).1 hb
  have h0 := (rule_iff_solves 𝔼 hσ.ne' hS hr0).1
    ((zero_equilibrium_iff 𝔼 (β := β) (κ := κ) hσ.ne' rn rn).2 rfl)
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).2 h14) hx h0
    (adaptedVec_stack 𝔼 ha hai) (adaptedVec_stack 𝔼 (fun t => map_zero _) fun t => map_zero _)
    (boundedVec_stack hby hbi)
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have h1 : ygap = fun _ => 0 := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = fun _ => 0 := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [hr t, h1, h2]
  simp

/-- Galí (2015), p. 106 (necessity of (14)): if `κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, the rule
has a bounded equilibrium other than `ỹ = π = 0`. -/
theorem rule_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hr0 : Rule φπ φy rn (fun _ => 0) (fun _ => 0) rn := fun t => by simp
  have h0 := (rule_iff_solves 𝔼 hσ.ne' hS hr0).1
    ((zero_equilibrium_iff 𝔼 (β := β) (κ := κ) hσ.ne' rn rn).2 rfl)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => map_zero _) fun t => map_zero _)
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hr' : Rule φπ φy rn ygap' infl' (fun t => rn t + φπ • infl' t + φy • ygap' t) :=
    fun t => rfl
  refine ⟨ygap', infl', _, ⟨(rule_iff_solves 𝔼 hσ.ne' hS hr').2 (hst ▸ hy), hr',
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- **Ex. 4.4(a)** (Galí 2015, p. 106): for `φ_π, φ_y ≥ 0` the rule (11) implements
`ỹ = π = 0` as the unique bounded equilibrium if and only if condition (14) holds. -/
theorem implements_uniquely_iff [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (rn : ℕ → Ω → ℝ) :
    (∀ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i →
      ygap = (fun _ => 0) ∧ infl = (fun _ => 0)) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  constructor
  · intro h
    by_contra h14
    obtain ⟨ygap, infl, i, he, hne⟩ :=
      rule_not_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy (not_lt.1 h14) rn
    have := h ygap infl i he
    rcases hne with hne | hne
    · exact hne this.1
    · exact hne this.2
  · intro h14 ygap infl i he
    have := (rule_implements 𝔼 hσ hκ hβ0 hβ1 hφπ hφy h14 rn).2 ygap infl i he
    exact ⟨this.1, this.2.1⟩

/-! ### (b) The money supply under the optimal policy -/

/-- Galí (2015), Ex. 4.4(b): the lagged price level `p_{t−1}`, with `p_{−1} = p*` given. -/
def lagP (pstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => pstar
  | t + 1 => p t

/-- Galí (2015), Ex. 4.4: inflation is the change in the (log) price level,
`π_t = p_t − p_{t−1}`, with initial price level `p_{−1} = p*`. -/
def PriceLevel (pstar : ℝ) (p infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = p t - lagP pstar p t

/-- Galí (2015), Ex. 4.4, p. 122: money demand `m_t − p_t = y_t − η i_t` with output
`y_t = ỹ_t + y^n_t`. -/
def MoneyDemand (η : ℝ) (yn ygap p m i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t - p t = (ygap t + yn t) - η • i t

/-- Galí (2015), Ex. 4.4: an equilibrium of the full model: the IS equation, the Phillips curve,
the price-level identity and money demand. -/
def FullEquilibrium (β σ κ η pstar : ℝ) (rn yn ygap infl p m i : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σ κ rn ygap infl i ∧ PriceLevel pstar p infl ∧ MoneyDemand η yn ygap p m i

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(b): with zero inflation the price level never moves from `p*`. -/
theorem price_level_const {pstar : ℝ} {p : ℕ → Ω → ℝ}
    (h : PriceLevel pstar p (fun _ => 0)) (t : ℕ) : p t = fun _ => pstar := by
  induction t with
  | zero => have := h 0; simp only [lagP] at this; exact (sub_eq_zero.1 this.symm)
  | succ t ih =>
    have := h (t + 1)
    simp only [lagP] at this
    rw [← ih]
    exact sub_eq_zero.1 this.symm

/-- **Ex. 4.4(b)** (Galí 2015, p. 122): in every equilibrium attaining the optimal outcome
`ỹ = π = 0`, the money supply is `m_t = p* + y^n_t − η r^n_t`. -/
theorem money_path_optimal {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) {rn yn p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p m i) (t : ℕ) :
    m t = (fun _ => pstar) + yn t - η • rn t := by
  have hi := (zero_equilibrium_iff 𝔼 hσ rn i).1 h.1
  have hp := price_level_const h.2.1 t
  have hm := h.2.2 t
  rw [hp, hi] at hm
  funext ω
  have e := congrFun hm ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
  linarith

/-- **Ex. 4.4(b)** (Galí 2015, p. 122): if the money supply is held constant at `m̄` and an
equilibrium attains `ỹ = π = 0`, then `y^n_t − η r^n_t = m̄ − p*` at every date and state. -/
theorem constant_money_suboptimal {β σ κ η pstar mbar : ℝ} (hσ : σ ≠ 0)
    {rn yn p i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p (fun _ _ => mbar) i)
    (t : ℕ) (ω : Ω) : yn t ω - η * rn t ω = mbar - pstar := by
  have e := congrFun (money_path_optimal 𝔼 hσ h t) ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  linarith

/-- **Ex. 4.4(b)** (Galí 2015, p. 122: a constant money supply is generally suboptimal): if
`y^n − η r^n` is not constant, no equilibrium under a constant money supply attains the
optimal outcome `ỹ = π = 0`. -/
theorem constant_money_not_optimal {β σ κ η pstar mbar : ℝ} (hσ : σ ≠ 0)
    {rn yn : ℕ → Ω → ℝ}
    (hvar : ∃ s t ω ω', yn s ω - η * rn s ω ≠ yn t ω' - η * rn t ω') :
    ¬ ∃ p i, FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p
      (fun _ _ => mbar) i := by
  rintro ⟨p, i, h⟩
  obtain ⟨s, t, ω, ω', hne⟩ := hvar
  exact hne ((constant_money_suboptimal 𝔼 hσ h s ω).trans
    (constant_money_suboptimal 𝔼 hσ h t ω').symm)

/-- Galí (2015), Ex. 4.4(b)–(c): the optimal outcome `ỹ = π = 0`, `p = p*`, `i = r^n` is an
equilibrium whenever money follows `m_t = p* + y^n_t − η r^n_t`. -/
theorem optimal_equilibrium {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
      (fun t => (fun _ => pstar) + yn t - η • rn t) rn := by
  refine ⟨(zero_equilibrium_iff 𝔼 hσ rn rn).2 rfl, fun t => ?_, fun t => ?_⟩
  · cases t <;> simp [lagP]
  · funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-- Galí (2015), Ex. 4.4(b): conversely, if `y^n_t − η r^n_t = c` is constant, the constant money
supply `m̄ = p* + c` supports the optimal outcome. -/
theorem constant_money_optimal_of_const {β σ κ η pstar c : ℝ} (hσ : σ ≠ 0)
    {rn yn : ℕ → Ω → ℝ} (hc : ∀ t ω, yn t ω - η * rn t ω = c) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
      (fun _ _ => pstar + c) rn := by
  have h := optimal_equilibrium 𝔼 (β := β) (κ := κ) (η := η) (pstar := pstar) hσ rn yn
  have hm : (fun t => (fun _ => pstar) + yn t - η • rn t) = fun (_ : ℕ) (_ : Ω) => pstar + c := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hc t ω]
  rwa [hm] at h

/-! ### (c) A money supply rule implementing the optimum -/

/-- Galí (2015), Ex. 4.4(c), p. 123: the money supply rule `m_t = p* + y^n_t − η r^n_t`. -/
def MoneyRule (η pstar : ℝ) (rn yn m : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t = (fun _ => pstar) + yn t - η • rn t

/-- **Ex. 4.4(c)** (Galí 2015, p. 123, existence): under the money rule
`m_t = p* + y^n_t − η r^n_t` the optimal outcome `ỹ = π = 0`, `p_t = p*`, `i_t = r^n_t` is an
equilibrium. -/
theorem moneyRule_equilibrium {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
        (fun t => (fun _ => pstar) + yn t - η • rn t) rn ∧
      MoneyRule η pstar rn yn (fun t => (fun _ => pstar) + yn t - η • rn t) :=
  ⟨optimal_equilibrium 𝔼 hσ rn yn, fun _ => rfl⟩

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): given money demand and `η > 0`, the money rule
`m_t = p* + y^n_t − η r^n_t` holds iff the nominal rate follows the implicit interest rate rule
`i_t = r^n_t + η⁻¹ (ỹ_t + (p_t − p*))`. -/
theorem moneyRule_iff_interestRule {η pstar : ℝ} (hη : 0 < η) {rn yn ygap p m i : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η yn ygap p m i) :
    MoneyRule η pstar rn yn m ↔
      ∀ t, i t = rn t + η⁻¹ • (ygap t + (p t - fun _ => pstar)) := by
  have hinv : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  constructor
  · intro h t
    funext ω
    have e := congrFun (hmd t) ω
    have r := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination η⁻¹ * e - η⁻¹ * r - i t ω * hinv + rn t ω * hinv
  · intro h t
    funext ω
    have e := congrFun (hmd t) ω
    have r := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination e - η * r - (ygap t ω + (p t ω - pstar)) * hinv

/-- Galí (2015), Ex. 4.4(c) (**not yet claimed**): the statement that under the money rule
`m_t = p* + y^n_t − η r^n_t` the optimal outcome is the *unique* bounded equilibrium for every
bounded adapted `r^n`, `y^n`. With the price level predetermined this is a three-variable
determinacy question (the open question of Galí Chapter 3, footnote 14), which this project
leaves open; the definition records the claim without asserting it. -/
def MoneyRuleUniqueness (β σ κ η pstar : ℝ) : Prop :=
  ∀ rn yn ygap infl p m i : ℕ → Ω → ℝ,
    BoundedProc rn → 𝔼.Adapted rn → BoundedProc yn → 𝔼.Adapted yn →
    FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i → MoneyRule η pstar rn yn m →
    𝔼.Adapted ygap → 𝔼.Adapted p → BoundedProc ygap → BoundedProc p →
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0)

end Gali.MonetaryPolicyDesign.Ex4_4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.5: optimal monetary policy with price setting in advance

Galí (2015), Chapter 4, Exercise 4.5, pp. 123–125. Money in the utility function with period
utility `log C + log (M/P) − N^{1+φ}/(1+φ)` (eq. (21)), monopolistically competitive firms
with `Y(i) = A N(i)` (eq. (22)), technology `A_t/A_{t−1} = (1 + γ_a) e^{ε^a_t}` and money
`M_t/M_{t−1} = (1 + γ_m) e^{ε^m_t}` (eq. (23)) with Gaussian innovations. The money rules of
part (g) are `ε^m_t = φ_a ε^a_t + φ_v ν_t`, `ν_t ~ N(0, 1)` independent of `ε^a`; the
exogenous rule (23) with `ε^m` independent of `ε^a` is the case `φ_a = 0`.

The shocks live on a genuine probability space with a filtration (`ShockPair`: the pair
`(ε^a_t, ν_t)` is adapted, has law `N(0, σ_a²) ⊗ N(0, 1)`, and the date-`t+1` pair is independent
of `ℱ_t`); `concreteShocks` builds one on `Measure.infinitePi`, so nothing is vacuous.

## (a) Household
`hasDerivAt_utility_C/_m/_N`, `labour_optimum_iff` (`W/P = C N^φ`), `money_optimum_iff`
(`C = (1 − Q) M/P`), and the Euler equation with a genuine conditional expectation (`eulerRHS`);
restated from the Chapter 2 project.

## (b)–(c) Flexible prices
* `price_optimum_iff`: the firm maximises `Y(i)(P(i) − W/A)` iff `P(i) = 𝓜 W/A`,
  `𝓜 = ε/(ε − 1)` (Bernoulli's inequality, `markup_pricing_le/_lt`).
* `flex_employment`: `N_t = 𝓜^{−1/(1+φ)}` in every equilibrium, state by state; `flex_output`;
  `flex_velocity`: `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`, `σ_m² = φ_a² σ_a² + φ_v²`
  (`condExp_money_ratio`, Gaussian MGF); `flex_candidate`: the exact equilibrium exists;
  `flex_inflation`: `P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`.

## (d) Welfare and the Friedman rule
`hasSum_flex_welfare`: `∑ βᵗ E[U_t] = welfareFlex`, which depends on policy only through
`−log V/(1 − β)`; welfare falls with `γ_m`, rises with `σ_m²`, and as a function of the nominal
rate `i > 0` is strictly decreasing and unbounded as `i → 0⁺` (`welfare_rate_strictAnti`,
`tendsto_welfare_rate`); `not_optimal_of_equilibrium`: every policy with `i > 0` is strictly
improved upon, so the optimum must satisfy the Friedman rule `1 + γ_m = β e^{σ_m²/2}`
(`friedman_iff`) — any `(γ_m, σ_m²)` on that locus supports it. **Imprecision**: at the Friedman
rule there is no equilibrium (`not_equilibrium_at_friedman`); it is a supremum, not a maximum.

## (e) Prices set one period in advance
* `sticky_objective_eq`: the book's objective with `Λ_{t−1,t} = β C_{t−1}/C_t` (deflated by
  `P_t`; the printed `P_{t+1}` is a typo) is `β C_{t−1} P_t^{ε−1} P_t(i)^{−ε}(P_t(i) − W_t/A_t)`.
* `sticky_price_optimal`, `sticky_price_unique`: with genuine conditional expectations, the
  optimal preset price is `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]` (sufficiency and necessity);
  `pricing_iff`: in equilibrium this is `E_{t−1}[N_t^{1+φ}] = 1/𝓜`.
* `sticky_employment`: in every sticky-price equilibrium with constant velocity,
  `N_{t+1} = 𝓜^{−1/(1+φ)} e^{(ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2}` a.s.,
  `s² = (φ_a − 1)² σ_a² + φ_v²`; `sticky_employment_zero`, `sticky_velocity`,
  `sticky_output_balances` (`Y = A N`, `M/P = A N/V`); `sticky_candidate`: existence.

## (f) Expected utility
`sticky_expected_utility_succ`, `hasSum_sticky_welfare`, `integral_tsum_sticky_welfare`:
`E[∑ βᵗ U_t] = ∑ βᵗ E[U_t] = welfareFlex(V) − (1 + φ) s² β/(1 − β)` (`stickyWelfare`).

## (g) The optimal money rule
`stabilization_optimal`, `stabilization_improves`: for every nominal rate the rule
`φ_a = 1, φ_v = 0` is at least as good as any `(φ_a, φ_v)` and strictly better unless
`(φ_a, φ_v) = (1, 0)` (for `σ_a² > 0`, `varX_eq_zero_iff`); `policy_not_optimal`
(**correction**): no rule is optimal, since lowering `γ_m` towards the Friedman level always
helps; `tendsto_policyWelfare_friedman`: with `φ_a = 1, φ_v = 0` welfare tends to `+∞` as
`1 + γ_m ↓ β e^{σ_a²/2}`, so the book's answer (`γ_m` at the Friedman level, `φ_a = 1`,
`φ_v = 0`) is the supremum; `stickyN_replicates`, `sticky_replicates_flex`,
`sticky_employment_replicates`, `policyWelfare_replicates`: under `φ_a = 1, φ_v = 0` the
sticky-price equilibrium replicates the flexible-price allocation and welfare.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### (a) Optimality conditions -/

/-- Galí (2015), Ex. 4.5, eq. (21), p. 123: period utility `log C + log m − N^{1+φ}/(1+φ)`,
with real balances `m = M/P`. -/
noncomputable def utility (φ C m N : ℝ) : ℝ :=
  Real.log C + Real.log m - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal utility of consumption is `U_c = 1/C`. -/
theorem hasDerivAt_utility_C (φ m N : ℝ) {C : ℝ} (hC : C ≠ 0) :
    HasDerivAt (fun C' => utility φ C' m N) C⁻¹ C := by
  have := ((Real.hasDerivAt_log hC).add_const (Real.log m)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal utility of real balances is `U_m = 1/m`. -/
theorem hasDerivAt_utility_m (φ C N : ℝ) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun m' => utility φ C m' N) m⁻¹ m := by
  have := ((Real.hasDerivAt_log hm).const_add (Real.log C)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal disutility of labour is `−U_n = N^φ`. -/
theorem hasDerivAt_utility_N {φ : ℝ} (hφ : 0 ≤ φ) (C m N : ℝ) :
    HasDerivAt (fun N' => utility φ C m N') (-N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have := hd.const_sub (Real.log C + Real.log m)
  simpa [utility] using this

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (restated from the Chapter 2 project; used for the concavity of (21)). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`x^{1+φ}/(1+φ) + x^φ (y − x) ≤ y^{1+φ}/(1+φ)` (restated from the Chapter 2 project). -/
theorem disutil_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ (1 + φ) / (1 + φ) + x ^ φ * (y - x) ≤ y ^ (1 + φ) / (1 + φ) := by
  have hd : ∀ z : ℝ, HasDerivAt (fun N : ℝ => N ^ (1 + φ) / (1 + φ)) (z ^ φ) z := by
    intro z
    refine ((Real.hasDerivAt_rpow_const (x := z) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have h := le_tangent (f := fun N => -(N ^ (1 + φ) / (1 + φ))) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hd z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 21: the marginal disutility of labour, `d/dN [N^{1+φ}/(1+φ)] = N^φ`. -/
theorem hasDerivAt_disutil {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), Ex. 4.5(a) (concavity of (21)): the tangent-line inequality for `log`,
`log y ≤ log x + (y − x)/x` for `x, y > 0`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- Galí (2015), Ex. 4.5(a), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` (real balances `m` fixed) with `C > 0`, then
`W/P = C N^φ`. -/
theorem labour_foc_necessary {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => utility φ ((W * N' + X) / P) m N') N) :
    W / P = C * N ^ φ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hg : HasDerivAt (fun N' => utility φ ((W * N' + X) / P) m N') (C⁻¹ * (W / P) - N ^ φ)
      N := by
    have h1 : HasDerivAt (fun N' => Real.log ((W * N' + X) / P)) (C⁻¹ * (W / P)) N := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp N hin
      rw [hCeq] at this
      exact this
    have h2 : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N :=
      hasDerivAt_disutil hφ N
    exact HasDerivAt.sub (h1.add_const (Real.log m)) h2
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  field_simp
  linarith

/-- Galí (2015), Ex. 4.5(a), p. 19 (**sufficiency**, by concavity): if `W/P = C N^φ` at a
point with `C, N > 0` on the budget line `P C = W N + X`, it maximises (21) among all feasible
`N' ≥ 0` with `C' = (W N' + X)/P > 0`. -/
theorem labour_foc_sufficient {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) (hfoc : W / P = C * N ^ φ) {N' : ℝ}
    (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N := by
  have hu := log_le_tangent hC hC'
  have hv := disutil_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have h3 : ((W * N' + X) / P - C) / C = N ^ φ * (N' - N) := by
    rw [hdiff, hfoc]; field_simp
  unfold utility
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (4), p. 19: a point with `C, N > 0` on the budget line solves
the labour-supply problem iff `W/P = C N^φ`. -/
theorem labour_optimum_iff {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N) ↔ W / P = C * N ^ φ := by
  constructor
  · intro h
    refine labour_foc_necessary (m := m) hφ hP hC hbud ?_
    have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
    have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
    have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
      (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
    rw [hCeq]
    exact h N' h2'.le h1'
  · intro h N' hN' hC'
    exact labour_foc_sufficient hφ hP hN hC hbud h hN' hC'

/-- Galí (2015), Ex. 4.5(a), with eq. (33), p. 32 (**necessity**): holding total financial
wealth fixed, the budget (32) reads `P C + (1 − Q) P m = X`. If real balances `m > 0` are a
local optimum along it with `C > 0`, then `C = (1 − Q) m`: velocity `P C/M` equals `1 − Q`. -/
theorem money_foc_necessary {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X)
    (hloc : IsLocalMax (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N) m) :
    C = (1 - Q) * m := by
  have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
  have hin : HasDerivAt (fun m' : ℝ => (X - (1 - Q) * P * m') / P) (-(1 - Q)) m := by
    have := (((hasDerivAt_id' m).const_mul ((1 - Q) * P)).const_sub X).div_const P
    convert this using 1
    field_simp
  have hg : HasDerivAt (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N)
      (C⁻¹ * (-(1 - Q)) + m⁻¹) m := by
    have h1 : HasDerivAt (fun m' => Real.log ((X - (1 - Q) * P * m') / P)) (C⁻¹ * (-(1 - Q)))
        m := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp m hin
      rw [hCeq] at this
      exact this
    have := (h1.add (Real.hasDerivAt_log hm.ne')).sub_const (N ^ (1 + φ) / (1 + φ))
    simpa [utility] using this
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (33), p. 32 (**sufficiency**, by concavity of `log`): if
`C = (1 − Q) m` at a point with `C, m > 0` on the budget line `P C + (1 − Q) P m = X`, it
maximises (21) among all `m' > 0` with `C' > 0`. -/
theorem money_foc_sufficient {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) (hfoc : C = (1 - Q) * m) {m' : ℝ} (hm' : 0 < m')
    (hC' : 0 < (X - (1 - Q) * P * m') / P) :
    utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N := by
  have h1 := log_le_tangent hC hC'
  have h2 := log_le_tangent hm hm'
  have hdiff : (X - (1 - Q) * P * m') / P - C = -(1 - Q) * (m' - m) := by
    rw [← hbud]; field_simp; ring
  have hsum : ((X - (1 - Q) * P * m') / P - C) / C + (m' - m) / m = 0 := by
    rw [hdiff, hfoc]
    have hm0 : m ≠ 0 := hm.ne'
    by_cases hQ : 1 - Q = 0
    · rw [hQ] at hfoc; linarith
    · field_simp; ring
  unfold utility
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (33), p. 32: on the budget line, `(C, m)` with `C, m > 0`
solves the portfolio problem iff `C = (1 − Q) m`. -/
theorem money_optimum_iff {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) :
    (∀ m', 0 < m' → 0 < (X - (1 - Q) * P * m') / P →
      utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N) ↔ C = (1 - Q) * m := by
  constructor
  · intro h
    refine money_foc_necessary (φ := φ) (N := N) hP hC hm hbud ?_
    have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
    have hcont : Continuous fun m' : ℝ => (X - (1 - Q) * P * m') / P := by fun_prop
    have h1 : ∀ᶠ m' in 𝓝 m, 0 < (X - (1 - Q) * P * m') / P :=
      (hcont.tendsto m).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hm] with m' h1' h2'
    rw [hCeq]
    exact h m' h2' h1'
  · intro h m' hm' hC'
    exact money_foc_sufficient hP hC hm hbud h hm' hC'


/-! ### (b) Monopolistic price setting -/

/-- Galí (2015), Ex. 4.5(b), p. 124: the gross markup `𝓜 = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), Ex. 4.5(b): `𝓜 > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  div_pos (by linarith) (by linarith)

/-- Galí (2015), Ex. 4.5(b): `𝓜 > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]; linarith

/-- Galí (2015), Ex. 4.5(b): the real profit `x^{−ε} (x − c)` of a price `x` per unit of
`P^ε Y`, for marginal cost `c` (Bernoulli's inequality): it is maximised at `x = 𝓜 c`,
`x^{−ε}(x − c) ≤ (𝓜c)^{−ε}(𝓜c − c)` for every `x > 0`. -/
theorem markup_pricing_le {ε c x : ℝ} (hε : 1 < ε) (hc : 0 < c) (hx : 0 < x) :
    x ^ (-ε) * (x - c) ≤ (markup ε * c) ^ (-ε) * (markup ε * c - c) := by
  set a := markup ε * c with ha
  have hapos : 0 < a := mul_pos (markup_pos hε) hc
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hε0 : ε ≠ 0 := by linarith
  have hac : a - c = a / ε := by
    rw [ha, markup]; field_simp; ring
  have hB := one_add_mul_self_le_rpow_one_add (s := x / a - 1) (by
    have := div_pos hx hapos; linarith) hε.le
  rw [show 1 + (x / a - 1) = x / a by ring, Real.div_rpow hx.le hapos.le] at hB
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx ε
  have hae : 0 < a ^ ε := Real.rpow_pos_of_pos hapos ε
  rw [Real.rpow_neg hx.le, Real.rpow_neg hapos.le, hac]
  have key : ε * (x - c) * a ^ ε ≤ a * x ^ ε := by
    have h1 : (1 + ε * (x / a - 1)) * a ^ ε ≤ x ^ ε := by
      rwa [le_div_iff₀ hae] at hB
    have h2 : (1 + ε * (x / a - 1)) * a = ε * (x - c) := by
      have : ε * c = (ε - 1) * a := by rw [ha, markup]; field_simp
      field_simp
      linear_combination this
    nlinarith
  rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hxe hae, div_mul_eq_mul_div,
    le_div_iff₀ (by linarith)]
  nlinarith

/-- Galí (2015), Ex. 4.5(b): the maximiser is unique: for `x > 0`, `x ≠ 𝓜 c`,
`x^{−ε}(x − c) < (𝓜c)^{−ε}(𝓜c − c)`. -/
theorem markup_pricing_lt {ε c x : ℝ} (hε : 1 < ε) (hc : 0 < c) (hx : 0 < x)
    (hne : x ≠ markup ε * c) :
    x ^ (-ε) * (x - c) < (markup ε * c) ^ (-ε) * (markup ε * c - c) := by
  set a := markup ε * c with ha
  have hapos : 0 < a := mul_pos (markup_pos hε) hc
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hε0 : ε ≠ 0 := by linarith
  have hac : a - c = a / ε := by
    rw [ha, markup]; field_simp; ring
  have hs : x / a - 1 ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero, div_eq_one_iff_eq hapos.ne'] at h
    exact h
  have hB := one_add_mul_self_lt_rpow_one_add (s := x / a - 1) (by
    have := div_pos hx hapos; linarith) hs hε
  rw [show 1 + (x / a - 1) = x / a by ring, Real.div_rpow hx.le hapos.le] at hB
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx ε
  have hae : 0 < a ^ ε := Real.rpow_pos_of_pos hapos ε
  rw [Real.rpow_neg hx.le, Real.rpow_neg hapos.le, hac]
  have key : ε * (x - c) * a ^ ε < a * x ^ ε := by
    have h1 : (1 + ε * (x / a - 1)) * a ^ ε < x ^ ε := by
      rwa [lt_div_iff₀ hae] at hB
    have h2 : (1 + ε * (x / a - 1)) * a = ε * (x - c) := by
      have : ε * c = (ε - 1) * a := by rw [ha, markup]; field_simp
      field_simp
      linear_combination this
    nlinarith
  rw [inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀ hxe hae, div_mul_eq_mul_div,
    lt_div_iff₀ (by linarith)]
  nlinarith

/-- Galí (2015), Ex. 4.5(b), p. 124: the profit `Y(i)(P(i) − W/A)` with demand
`Y(i) = (P(i)/P)^{−ε} Y` equals `P^ε Y · P(i)^{−ε}(P(i) − W/A)`. -/
theorem profit_eq {ε P Y x c : ℝ} (hP : 0 < P) (hx : 0 < x) :
    (x / P) ^ (-ε) * Y * (x - c) = P ^ ε * Y * (x ^ (-ε) * (x - c)) := by
  rw [Real.div_rpow hx.le hP.le, Real.rpow_neg hP.le, div_inv_eq_mul]
  ring

/-- **Ex. 4.5(b)** (Galí 2015, p. 124): the monopolistically competitive firm, setting its price
after observing the shocks, maximises current profit `Y(i)(P(i) − W/A)` subject to
`Y(i) = (P(i)/P)^{−ε} Y` at a price `x > 0` if and only if `x = 𝓜 W/A`, `𝓜 = ε/(ε − 1)`. -/
theorem price_optimum_iff {ε P Y c x : ℝ} (hε : 1 < ε) (hP : 0 < P) (hY : 0 < Y) (hc : 0 < c)
    (hx : 0 < x) :
    (∀ x', 0 < x' → (x' / P) ^ (-ε) * Y * (x' - c) ≤ (x / P) ^ (-ε) * Y * (x - c)) ↔
      x = markup ε * c := by
  have hK : 0 < P ^ ε * Y := mul_pos (Real.rpow_pos_of_pos hP ε) hY
  constructor
  · intro h
    by_contra hne
    have h1 := h (markup ε * c) (mul_pos (markup_pos hε) hc)
    rw [profit_eq hP (mul_pos (markup_pos hε) hc), profit_eq hP hx] at h1
    have h2 := markup_pricing_lt hε hc hx hne
    nlinarith
  · rintro rfl x' hx'
    rw [profit_eq hP hx', profit_eq hP (mul_pos (markup_pos hε) hc)]
    exact mul_le_mul_of_nonneg_left (markup_pricing_le hε hc hx') hK.le

/-- Galí (2015), Ex. 4.5(b): in a symmetric equilibrium `P = 𝓜 W/A`, the real wage is
`W/P = A/𝓜`. -/
theorem real_wage_of_pricing {ε P W A : ℝ} (hε : 1 < ε) (hP : 0 < P) (hA : 0 < A)
    (h : P = markup ε * (W / A)) : W / P = A / markup ε := by
  have hM := markup_pos hε
  have hW : W ≠ 0 := by
    rintro rfl
    rw [zero_div, mul_zero] at h
    exact hP.ne' h
  rw [h]; field_simp

/-! ### (c) The flexible-price equilibrium: employment -/

/-- Galí (2015), Ex. 4.5(c): flexible-price employment `N = 𝓜^{−1/(1+φ)}`. -/
noncomputable def Nflex (φ ε : ℝ) : ℝ := (markup ε)⁻¹ ^ (1 + φ)⁻¹

/-- Galí (2015), Ex. 4.5(c): `N > 0`. -/
theorem Nflex_pos {φ ε : ℝ} (hε : 1 < ε) : 0 < Nflex φ ε :=
  Real.rpow_pos_of_pos (inv_pos.2 (markup_pos hε)) _

/-- Galí (2015), Ex. 4.5(c): `N^{1+φ} = 1/𝓜`. -/
theorem Nflex_rpow {φ ε : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) : Nflex φ ε ^ (1 + φ) = (markup ε)⁻¹ :=
  Real.rpow_inv_rpow (inv_pos.2 (markup_pos hε)).le (by linarith)

/-- Galí (2015), Ex. 4.5(c), p. 124: given labour supply `W/P = C N^φ`, markup pricing
`P = 𝓜 W/A`, technology `Y = A N` and `C = Y`, employment is `N = 𝓜^{−1/(1+φ)}`, state by
state. -/
theorem employment_flex {φ ε P W A C N : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hP : 0 < P) (hA : 0 < A)
    (hN : 0 < N) (hlab : W / P = C * N ^ φ) (hpr : P = markup ε * (W / A)) (hC : C = A * N) :
    N = Nflex φ ε := by
  have hw := real_wage_of_pricing hε hP hA hpr
  rw [hw, hC] at hlab
  have hM := markup_pos hε
  have h1 : N ^ (1 + φ) = (markup ε)⁻¹ := by
    rw [Real.rpow_add hN, Real.rpow_one]
    field_simp at hlab ⊢
    nlinarith [hlab]
  rw [Nflex, ← h1, Real.rpow_rpow_inv hN.le (by linarith)]

/-! ### The stochastic environment -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 4.5, p. 123, and eq. (23): the level `X_t = X₀ (1 + γ)ᵗ e^{ε_1 + ⋯ + ε_t}`
of technology (`X = A`) or of the money supply (`X = M`). -/
noncomputable def level (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  X₀ * (1 + γ) ^ t * Real.exp (∑ s ∈ Finset.range t, ε (s + 1) ω)

/-- Galí (2015), Ex. 4.5, p. 123, and eq. (23): `X_{t+1}/X_t = (1 + γ) e^{ε_{t+1}}`. -/
theorem level_succ (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    level X₀ γ ε (t + 1) ω = level X₀ γ ε t ω * ((1 + γ) * Real.exp (ε (t + 1) ω)) := by
  simp only [level, Finset.sum_range_succ, Real.exp_add, pow_succ]
  ring

/-- Galí (2015), Ex. 4.5: levels are positive when `X₀ > 0` and `1 + γ > 0`. -/
theorem level_pos {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : 0 < level X₀ γ ε t ω := by
  unfold level
  positivity

/-- Galí (2015), Ex. 4.5: the date-0 level is `X₀`. -/
theorem level_zero (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (ω : Ω) : level X₀ γ ε 0 ω = X₀ := by
  simp [level]

/-- Galí (2015), Ex. 4.5: `log X_t = log X₀ + t log(1 + γ) + ε_1 + ⋯ + ε_t`. -/
theorem log_level_eq {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Real.log (level X₀ γ ε t ω) =
      (Real.log X₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, ε (s + 1) ω := by
  rw [level, Real.log_mul (mul_pos hX (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
    Real.log_mul hX.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]

/-- Galí (2015), Ex. 4.5, p. 124: the law of one period's innovations `(ε^a_t, ν_t)`,
independent `N(0, σ_a²)` and `N(0, 1)`. -/
noncomputable abbrev pairLaw (va : ℝ≥0) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 va).prod (gaussianReal 0 1)

/-- Galí (2015), Ex. 4.5 (Gaussian moment generating function): for independent
`ε^a ~ N(0, σ_a²)` and `ν ~ N(0, 1)`, `E e^{a ε^a + b ν} = e^{(a² σ_a² + b²)/2}`. -/
theorem integral_exp_pair (va : ℝ≥0) (a b : ℝ) :
    ∫ q, Real.exp (a * q.1 + b * q.2) ∂(pairLaw va) = Real.exp ((a ^ 2 * va + b ^ 2) / 2) := by
  have h1 : ∫ x, Real.exp (a * x) ∂(gaussianReal 0 va) = Real.exp (va * a ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := va)) a
    simpa [mgf] using this
  have h2 : ∫ x, Real.exp (b * x) ∂(gaussianReal 0 1) = Real.exp (b ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) b
    simpa [mgf] using this
  have hfun : (fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)) =
      fun q => Real.exp (a * q.1) * Real.exp (b * q.2) := by
    funext q; rw [Real.exp_add]
  rw [hfun, integral_prod_mul (fun x => Real.exp (a * x)) (fun y => Real.exp (b * y)), h1, h2,
    ← Real.exp_add]
  congr 1; ring

/-- Galí (2015), Ex. 4.5: `e^{a ε^a + b ν}` is integrable under the law of the innovations. -/
theorem integrable_exp_pair (va : ℝ≥0) (a b : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)) (pairLaw va) := by
  have := (integrable_exp_mul_gaussianReal (μ := 0) (v := va) a).mul_prod
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) b)
  refine this.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Real.exp_add]

variable [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)

/-- Galí (2015), Ex. 4.5, pp. 123–124: the shocks. At each date the pair `(ε^a_t, ν_t)` is
`ℱ_t`-measurable with law `N(0, σ_a²) ⊗ N(0, 1)`, and the date-`t+1` pair is independent of
`ℱ_t` (so the pairs are i.i.d. and `ν` is independent of `ε^a` at all leads and lags). -/
structure ShockPair where
  /-- The innovation pair `(ε^a_t, ν_t)`. -/
  Z : ℕ → Ω → ℝ × ℝ
  /-- The technology variance `σ_a²`. -/
  va : ℝ≥0
  /-- The pair is known at date `t`. -/
  adapted : ∀ t, Measurable[ℱ t] (Z t)
  /-- The law of each pair. -/
  hasLaw : ∀ t, HasLaw (Z t) (pairLaw va) μ
  /-- The date-`t+1` pair is independent of the date-`t` information. -/
  indep : ∀ t, Indep (MeasurableSpace.comap (Z (t + 1)) inferInstance) (ℱ t) μ

variable {μ ℱ}

/-- Galí (2015), Ex. 4.5, p. 123: the technology innovation `ε^a_t`. -/
def techShock (S : ShockPair μ ℱ) : ℕ → Ω → ℝ := fun t ω => (S.Z t ω).1

/-- Galí (2015), Ex. 4.5(g), p. 124: the money-growth innovation of the rule class,
`ε^m_t = φ_a ε^a_t + φ_v ν_t`. -/
def moneyShock (φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ :=
  fun t ω => φa * (S.Z t ω).1 + φv * (S.Z t ω).2

/-- Galí (2015), Ex. 4.5(g): the variance `σ_m² = φ_a² σ_a² + φ_v²` of money growth. -/
def varM (va φa φv : ℝ) : ℝ := φa ^ 2 * va + φv ^ 2

/-- Galí (2015), Ex. 4.5(e)–(g): the variance `s² = (φ_a − 1)² σ_a² + φ_v²` of
`ε^m_t − ε^a_t`, the innovation that moves employment when prices are set in advance. -/
def varX (va φa φv : ℝ) : ℝ := (φa - 1) ^ 2 * va + φv ^ 2

/-- Galí (2015), Ex. 4.5: `σ_m² ≥ 0`. -/
theorem varM_nonneg {va : ℝ} (hva : 0 ≤ va) (φa φv : ℝ) : 0 ≤ varM va φa φv := by
  unfold varM; positivity

/-- Galí (2015), Ex. 4.5: `s² ≥ 0`. -/
theorem varX_nonneg {va : ℝ} (hva : 0 ≤ va) (φa φv : ℝ) : 0 ≤ varX va φa φv := by
  unfold varX; positivity

/-- Galí (2015), Ex. 4.5: `E_t g(ε^a_{t+1}, ν_{t+1}) = ∫ g dN(0, σ_a²) ⊗ N(0, 1)` (the
innovation is independent of `ℱ_t`). -/
theorem condExp_shock [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) (t : ℕ) :
    μ[fun ω => g (S.Z (t + 1) ω) | ℱ t] =ᵐ[μ] fun _ => ∫ q, g q ∂(pairLaw S.va) := by
  have hmeas : Measurable (S.Z (t + 1)) := (S.adapted (t + 1)).mono (ℱ.le (t + 1)) le_rfl
  have hsm : StronglyMeasurable[MeasurableSpace.comap (S.Z (t + 1)) inferInstance]
      (fun ω => g (S.Z (t + 1) ω)) := (hg.comp (comap_measurable _)).stronglyMeasurable
  refine (condExp_indep_eq hmeas.comap_le (ℱ.le t) hsm (S.indep t)).trans ?_
  exact Filter.Eventually.of_forall fun _ =>
    (S.hasLaw (t + 1)).integral_comp hg.aestronglyMeasurable

/-- Galí (2015), Ex. 4.5: `E e^{a ε^a_t + b ν_t} = e^{(a² σ_a² + b²)/2}`. -/
theorem integral_exp_shock (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, Real.exp (a * (S.Z t ω).1 + b * (S.Z t ω).2) ∂μ =
      Real.exp ((a ^ 2 * S.va + b ^ 2) / 2) := by
  rw [← integral_exp_pair]
  exact (S.hasLaw t).integral_comp (f := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (by fun_prop : Continuous fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)).aestronglyMeasurable

/-- Galí (2015), Ex. 4.5: `e^{a ε^a_t + b ν_t}` is integrable. -/
theorem integrable_exp_shock (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    Integrable (fun ω => Real.exp (a * (S.Z t ω).1 + b * (S.Z t ω).2)) μ :=
  (S.hasLaw t).integrable_comp (f := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (integrable_exp_pair S.va a b)

/-- Galí (2015), Ex. 4.5: `ε^a_t ~ N(0, σ_a²)`. -/
theorem hasLaw_fst (S : ShockPair μ ℱ) (t : ℕ) :
    HasLaw (fun ω => (S.Z t ω).1) (gaussianReal 0 S.va) μ :=
  HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (S.hasLaw t)

/-- Galí (2015), Ex. 4.5: `ν_t ~ N(0, 1)`. -/
theorem hasLaw_snd (S : ShockPair μ ℱ) (t : ℕ) :
    HasLaw (fun ω => (S.Z t ω).2) (gaussianReal 0 1) μ :=
  HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (S.hasLaw t)

/-- Galí (2015), Ex. 4.5: linear combinations `a ε^a_t + b ν_t` are integrable. -/
theorem integrable_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    Integrable (fun ω => a * (S.Z t ω).1 + b * (S.Z t ω).2) μ :=
  (((hasLaw_fst S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))).const_mul
    a).add (((hasLaw_snd S t).integrable
      (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))).const_mul b)

/-- Galí (2015), Ex. 4.5: `E (a ε^a_t + b ν_t) = 0`. -/
theorem integral_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, (a * (S.Z t ω).1 + b * (S.Z t ω).2) ∂μ = 0 := by
  have h1 := (hasLaw_fst S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  have h2 := (hasLaw_snd S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  rw [integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul, integral_const_mul,
    (hasLaw_fst S t).integral_eq, (hasLaw_snd S t).integral_eq, integral_id_gaussianReal,
    integral_id_gaussianReal]
  ring

/-- Galí (2015), Ex. 4.5: expected log technology, `E[log A_t] = log A₀ + t log(1 + γ_a)`. -/
theorem integral_log_tech [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {A₀ γ : ℝ}
    (hA : 0 < A₀) (hγ : 0 < 1 + γ) (t : ℕ) :
    ∫ ω, Real.log (level A₀ γ (techShock S) t ω) ∂μ = Real.log A₀ + t * Real.log (1 + γ) := by
  have hfun : (fun ω => Real.log (level A₀ γ (techShock S) t ω)) = fun ω =>
      (Real.log A₀ + t * Real.log (1 + γ)) +
        ∑ s ∈ Finset.range t, (1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2) := by
    funext ω
    rw [log_level_eq hA hγ]
    simp [techShock]
  rw [hfun, integral_add (integrable_const _) (integrable_finsetSum _ fun s _ =>
    integrable_lin S 1 0 (s + 1)), integral_finsetSum _ fun s _ => integrable_lin S 1 0 (s + 1)]
  simp only [integral_lin, Finset.sum_const_zero, add_zero, integral_const, probReal_univ,
    one_smul]

/-- Galí (2015), Ex. 4.5: `log A_t` is integrable. -/
theorem integrable_log_tech (S : ShockPair μ ℱ) {A₀ γ : ℝ} (hA : 0 < A₀) (hγ : 0 < 1 + γ)
    [IsFiniteMeasure μ] (t : ℕ) :
    Integrable (fun ω => Real.log (level A₀ γ (techShock S) t ω)) μ := by
  have hfun : (fun ω => Real.log (level A₀ γ (techShock S) t ω)) = fun ω =>
      (Real.log A₀ + t * Real.log (1 + γ)) +
        ∑ s ∈ Finset.range t, (1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2) := by
    funext ω
    rw [log_level_eq hA hγ]
    simp [techShock]
  rw [hfun]
  exact (integrable_const _).add (integrable_finsetSum _ fun s _ => integrable_lin S 1 0 (s + 1))

/-- Galí (2015), Ex. 4.5, eq. (23) with Ex. 4.5(g): `E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)`
for the money supply `M_{t+1}/M_t = (1 + γ_m) e^{φ_a ε^a_{t+1} + φ_v ν_{t+1}}` (Gaussian MGF,
independence). -/
theorem condExp_money_ratio [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {M₀ γ : ℝ}
    (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (φa φv : ℝ) (t : ℕ) :
    μ[fun ω => level M₀ γ (moneyShock φa φv S) t ω / level M₀ γ (moneyShock φa φv S) (t + 1) ω
      | ℱ t] =ᵐ[μ] fun _ => Real.exp (varM S.va φa φv / 2) / (1 + γ) := by
  have hfun : (fun ω => level M₀ γ (moneyShock φa φv S) t ω /
      level M₀ γ (moneyShock φa φv S) (t + 1) ω) = fun ω =>
        (fun q : ℝ × ℝ => (1 + γ)⁻¹ * Real.exp (-φa * q.1 + -φv * q.2)) (S.Z (t + 1) ω) := by
    funext ω
    have h1 : level M₀ γ (moneyShock φa φv S) t ω ≠ 0 :=
      mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ hγ.ne')) (Real.exp_pos _).ne'
    rw [level_succ]
    simp only [moneyShock]
    rw [show -φa * (S.Z (t + 1) ω).1 + -φv * (S.Z (t + 1) ω).2 =
      -(φa * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) by ring, Real.exp_neg]
    field_simp
  rw [hfun]
  refine (condExp_shock S (g := fun q : ℝ × ℝ => (1 + γ)⁻¹ * Real.exp (-φa * q.1 + -φv * q.2))
    (by fun_prop) t).trans (Filter.Eventually.of_forall fun _ => ?_)
  simp only
  rw [integral_const_mul, integral_exp_pair, varM]
  ring_nf

/-! ### (a)–(c) Equilibrium -/

variable (μ ℱ)

/-- Galí (2015), eq. (5) with `U_c = 1/C` (Ex. 4.5(a)): the right side
`β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]` of the Euler equation, with a genuine conditional
expectation given `ℱ_t`. -/
noncomputable def eulerRHS (β : ℝ) (C P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * μ[fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω') | ℱ t] ω

variable {μ ℱ}

/-- Galí (2015), Ex. 4.5: the steady bond price `Q* = β e^{σ_m²/2}/(1 + γ_m)`. -/
noncomputable def Qstar (β γ v : ℝ) : ℝ := β * Real.exp (v / 2) / (1 + γ)

/-- Galí (2015), Ex. 4.5: the constant velocity `V = 1 − Q*`. -/
noncomputable def velocity (β γ v : ℝ) : ℝ := 1 - Qstar β γ v

/-- Galí (2015), Ex. 4.5(c): with constant velocity, `C_t P_t = V M_t`, the Euler equation's
right side is the constant `Q* = β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem eulerRHS_of_const_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) (β : ℝ)
    {M₀ γ V φa φv : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (hV : V ≠ 0) {C P : ℕ → Ω → ℝ}
    (hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ (moneyShock φa φv S) t ω) (t : ℕ) :
    eulerRHS μ ℱ β C P t =ᵐ[μ] fun _ => Qstar β γ (varM S.va φa φv) := by
  have hfun : (fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω'))
      = fun ω' => level M₀ γ (moneyShock φa φv S) t ω' /
        level M₀ γ (moneyShock φa φv S) (t + 1) ω' := by
    funext ω'
    rw [hCP, hCP, mul_div_mul_left _ _ hV]
  filter_upwards [condExp_money_ratio S hM hγ φa φv t] with ω hω
  simp only [eulerRHS]
  rw [hfun, hω, Qstar]
  ring

/-- Galí (2015), Ex. 4.5(c) (the constant-velocity solution): if money demand
`C = (1 − Q) M/P` and the Euler equation hold and velocity `P_t C_t/M_t = V` is constant, then
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem velocity_of_euler [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) (β : ℝ)
    {M₀ γ V φa φv : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ) {C P Q : ℕ → Ω → ℝ}
    (hC : ∀ t ω, 0 < C t ω) (hP : ∀ t ω, 0 < P t ω)
    (hmoney : ∀ t ω, C t ω = (1 - Q t ω) * (level M₀ γ (moneyShock φa φv S) t ω / P t ω))
    (heuler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t)
    (hV : ∀ t ω, P t ω * C t ω / level M₀ γ (moneyShock φa φv S) t ω = V) :
    V = velocity β γ (varM S.va φa φv) := by
  have hMp := level_pos hM hγ (moneyShock φa φv S)
  obtain ⟨ω₀, -⟩ := (heuler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀]
    exact div_pos (mul_pos (hP 0 ω₀) (hC 0 ω₀)) (hMp 0 ω₀)
  have hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ (moneyShock φa φv S) t ω := fun t ω => by
    rw [← hV t ω]
    field_simp [(hMp t ω).ne']
  have hQ : ∀ ω, Q 0 ω = 1 - V := fun ω => by
    rw [← hV 0 ω, hmoney 0 ω]
    field_simp [(hMp 0 ω).ne', (hP 0 ω).ne']
    ring
  have hae := (heuler 0).trans (eulerRHS_of_const_velocity S β hM.ne' hγ hVpos.ne' hCP 0)
  obtain ⟨ω, hω⟩ := hae.exists
  rw [hQ ω] at hω
  simp only at hω
  rw [velocity]
  linarith

variable (μ ℱ) (β φ ε : ℝ) (A M C N Y P W Q : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 4.5(a)–(c), pp. 123–124: an equilibrium with flexible prices. The household
conditions are labour supply `W/P = C N^φ`, money demand `C = (1 − Q)(M/P)` and the Euler
equation; firms set `P = 𝓜 W/A` (part (b)); `Y = A N` and `C = Y`. -/
structure IsFlexEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply: `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand: `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation. -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Markup pricing (part (b)): `P = 𝓜 W/A`. -/
  pricing : ∀ t ω, P t ω = markup ε * (W t ω / A t ω)
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ ε A M C N Y P W Q}

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): in every flexible-price equilibrium employment is
constant, `N_t = 𝓜^{−1/(1+φ)}`, state by state. -/
theorem flex_employment {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : N t ω = Nflex φ ε :=
  employment_flex hφ hε (h.pos_P t ω) (hA t ω) (h.pos_N t ω) (h.labour t ω) (h.pricing t ω)
    ((h.clearing t ω).trans (h.technology t ω))

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): flexible-price output and consumption are
`Y_t = C_t = 𝓜^{−1/(1+φ)} A_t`. -/
theorem flex_output {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) :
    Y t ω = A t ω * Nflex φ ε ∧ C t ω = A t ω * Nflex φ ε := by
  have hY : Y t ω = A t ω * Nflex φ ε := by
    rw [h.technology t ω, flex_employment h hφ hε hA t ω]
  exact ⟨hY, (h.clearing t ω).trans hY⟩

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): with constant velocity the flexible-price equilibrium has
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem flex_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    V = velocity β γm (varM S.va φa φv) :=
  velocity_of_euler S β hM hγm h.pos_C h.pos_P h.money h.euler fun t ω => by
    rw [h.clearing t ω]; exact hV t ω

/-- **Ex. 4.5(c)** (Galí 2015, p. 124, existence): if `β e^{σ_m²/2} < 1 + γ_m`, the allocation
`N = 𝓜^{−1/(1+φ)}`, `C = Y = N A`, `P = V M/(N A)`, `W = P A/𝓜`, `Q = Q*` is an exact
flexible-price equilibrium. -/
theorem flex_candidate [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm φa φv : ℝ}
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀)
    (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM S.va φa φv) < 1) :
    IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) (level M₀ γm (moneyShock φa φv S))
      (fun t ω => level A₀ γa (techShock S) t ω * Nflex φ ε) (fun _ _ => Nflex φ ε)
      (fun t ω => level A₀ γa (techShock S) t ω * Nflex φ ε)
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * Nflex φ ε))
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (Nflex φ ε * markup ε))
      (fun _ _ => Qstar β γm (varM S.va φa φv)) := by
  have hV : 0 < velocity β γm (varM S.va φa φv) := by rw [velocity]; linarith
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hN := Nflex_pos (φ := φ) hε
  have hN1 := Nflex_rpow hφ hε
  have hmk := markup_pos hε
  refine ⟨fun t ω => mul_pos (hAp t ω) hN, fun _ _ => hN, fun t ω => div_pos (mul_pos hV
    (hMp t ω)) (mul_pos (hAp t ω) hN), fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t ω => ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · have key : Nflex φ ε * Nflex φ ε ^ φ = (markup ε)⁻¹ := by
      rw [← hN1, Real.rpow_add hN, Real.rpow_one]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne', hmk.ne']
    rw [show Nflex φ ε * markup ε * Nflex φ ε ^ φ = markup ε * (Nflex φ ε * Nflex φ ε ^ φ) by
      ring, key]
    field_simp
  · rw [show 1 - Qstar β γm (varM S.va φa φv) = velocity β γm (varM S.va φa φv) from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne']
  · refine (eulerRHS_of_const_velocity S β hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne']
  · field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne', hmk.ne']

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): flexible-price inflation is
`P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`, in every equilibrium with
constant velocity. -/
theorem flex_inflation (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) (ω : Ω) :
    P (t + 1) ω / P t ω = (1 + γm) / (1 + γa) *
      Real.exp (moneyShock φa φv S (t + 1) ω - techShock S (t + 1) ω) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hN := Nflex_pos (φ := φ) hε
  have hPeq : ∀ s, P s ω = V * level M₀ γm (moneyShock φa φv S) s ω /
      (level A₀ γa (techShock S) s ω * Nflex φ ε) := fun s => by
    have h1 := hV s ω
    rw [(flex_output h hφ hε hAp s ω).1] at h1
    rw [← h1]
    field_simp [(hAp s ω).ne', (hMp s ω).ne']
  have hVpos : 0 < V := by
    rw [← hV 0 ω, ← h.clearing 0 ω]
    exact div_pos (mul_pos (h.pos_P 0 ω) (h.pos_C 0 ω)) (hMp 0 ω)
  rw [hPeq, hPeq, level_succ, level_succ, Real.exp_sub]
  field_simp [(hAp t ω).ne', (hMp t ω).ne', hVpos.ne', hγa.ne', hN.ne',
    (Real.exp_pos (techShock S (t + 1) ω)).ne']

/-! ### (d) Welfare under flexible prices and the Friedman rule -/

/-- Galí (2015), Ex. 4.5(d), p. 124: in a flexible-price equilibrium with constant velocity `V`,
period utility is `2 log A_t + 2 log N − log V − 𝓜⁻¹/(1+φ)`, `N = 𝓜^{−1/(1+φ)}`. -/
theorem flex_period_utility {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (hM : ∀ t ω, 0 < M t ω) {V : ℝ}
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) = 2 * Real.log (A t ω) +
      2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hY := flex_output h hφ hε hA t ω
  have hN := flex_employment h hφ hε hA t ω
  have hP := h.pos_P t ω
  have hNf := Nflex_pos (φ := φ) hε
  have hVpos : 0 < V := by
    rw [← hV t ω, hY.1]; exact div_pos (mul_pos hP (mul_pos (hA t ω) hNf)) (hM t ω)
  have hmp : M t ω / P t ω = A t ω * Nflex φ ε / V := by
    rw [← hV t ω, hY.1]
    field_simp [(hA t ω).ne', (hM t ω).ne', hP.ne', hNf.ne']
  rw [utility, hY.2, hmp, hN, Nflex_rpow hφ hε,
    Real.log_div (mul_pos (hA t ω) hNf).ne' hVpos.ne',
    Real.log_mul (hA t ω).ne' hNf.ne']
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124: closed-form expected lifetime utility of the flexible-price
equilibrium, `(2 log A₀ + 2 log N − log V − 𝓜⁻¹/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. -/
noncomputable def welfareFlex (β φ ε A₀ γa V : ℝ) : ℝ :=
  (2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ)) / (1 - β) +
    2 * Real.log (1 + γa) * β / (1 - β) ^ 2

/-- Galí (2015), Ex. 4.5(d): if `E[U_t] = K + c t`, then `∑ βᵗ E[U_t]` converges to
`K/(1 − β) + c β/(1 − β)²` (for `0 ≤ β < 1`). -/
theorem hasSum_affine {β K c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * (K + c * t)) (K / (1 - β) + c * β / (1 - β) ^ 2) := by
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left K
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).mul_left c
  have hne : (1 - β) ≠ 0 := by linarith
  convert hg.add hn using 1
  · funext t; ring
  · field_simp

/-- **Ex. 4.5(d)** (Galí 2015, p. 124, infinite horizon): in a flexible-price equilibrium with
constant velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to `welfareFlex`. -/
theorem hasSum_flex_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hε : 1 < ε) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) M C N Y P W Q)
    (hM : ∀ t ω, 0 < M t ω) (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ)
      (welfareFlex β φ ε A₀ γa V) := by
  have hAp := level_pos hA hγa (techShock S)
  set K := 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) with hK
  have hE : ∀ t : ℕ, ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ
      = (2 * Real.log A₀ + K) + 2 * Real.log (1 + γa) * t := by
    intro t
    have hfun : (fun ω => utility φ (C t ω) (M t ω / P t ω) (N t ω))
        = fun ω => 2 * Real.log (level A₀ γa (techShock S) t ω) + K := by
      funext ω
      rw [flex_period_utility h hφ hε hAp hM hV t ω, hK]
      ring
    rw [hfun, integral_add ((integrable_log_tech S hA hγa t).const_mul 2) (integrable_const _),
      integral_const_mul, integral_log_tech S hA hγa t]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  have hs := hasSum_affine (K := 2 * Real.log A₀ + K) (c := 2 * Real.log (1 + γa)) hβ0 hβ1
  convert hs using 1
  · funext t; rw [hE t]
  · rw [welfareFlex, hK]; ring

/-- Galí (2015), Ex. 4.5(c): an equilibrium with constant velocity exists only if
`Q* = β e^{σ_m²/2}/(1 + γ_m) < 1`, i.e. only if the nominal rate is strictly positive. -/
theorem flex_qstar_lt_one [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    Qstar β γm (varM S.va φa φv) < 1 := by
  have hVeq := flex_velocity S hM hγm h hV
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγm _ 0 ω₀)
  rw [hVeq, velocity] at hVpos
  linarith
/-- Galí (2015), Ex. 4.5(c)–(d), p. 124, and Galí p. 32 (`Q = e^{−i}`): the constant nominal rate
`i = −log Q* = log(1 + γ_m) − log β − σ_m²/2`. -/
theorem nominalRate_eq {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = Real.log (1 + γ) - Real.log β - v / 2 := by
  rw [Qstar, Real.log_div (mul_pos hβ (Real.exp_pos _)).ne' hγ.ne',
    Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124: the constraint `Q_t ≤ 1` (a nonnegative nominal rate)
reads `β e^{σ_m²/2} ≤ 1 + γ_m`. -/
theorem qstar_le_one_iff {β γ v : ℝ} (hγ : 0 < 1 + γ) :
    Qstar β γ v ≤ 1 ↔ β * Real.exp (v / 2) ≤ 1 + γ := by
  rw [Qstar, div_le_one hγ]

/-- Galí (2015), Ex. 4.5(d), p. 124: the Friedman rule `i = −log Q* = 0` holds iff `Q* = 1`,
i.e. iff `1 + γ_m = β e^{σ_m²/2}`. -/
theorem friedman_iff {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = 0 ↔ 1 + γ = β * Real.exp (v / 2) := by
  have hQ : 0 < Qstar β γ v := div_pos (mul_pos hβ (Real.exp_pos _)) hγ
  rw [neg_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h hQ.ne'
    · rw [Qstar, div_eq_one_iff_eq hγ.ne'] at h; exact h.symm
    · linarith
  · intro h
    right; left
    rw [Qstar, h, div_self (mul_pos hβ (Real.exp_pos _)).ne']

/-- Galí (2015), Ex. 4.5(d), p. 124 (**imprecision**): at the Friedman rule `Q* = 1` there is no
equilibrium with constant velocity (velocity would be `0`, real balances infinite). -/
theorem not_equilibrium_at_friedman [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε M₀ γm φa φv V : ℝ} (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hF : Qstar β γm (varM S.va φa φv) = 1) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q) :
    ¬ ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V := fun hV => by
  have := flex_qstar_lt_one S hM hγm h hV
  linarith


/-- Galí (2015), Ex. 4.5(d): `welfareFlex = K − log V/(1 − β)` with `K` independent of
monetary policy. -/
theorem welfareFlex_eq (β φ ε A₀ γa V : ℝ) :
    welfareFlex β φ ε A₀ γa V = welfareFlex β φ ε A₀ γa 1 - Real.log V / (1 - β) := by
  simp only [welfareFlex, Real.log_one, sub_zero]
  ring

/-- Galí (2015), Ex. 4.5(d): welfare is strictly decreasing in velocity: for `V₁, V₂ > 0`,
`welfare(V₂) < welfare(V₁)` iff `V₁ < V₂`. -/
theorem welfareFlex_lt_iff {β φ ε A₀ γa V₁ V₂ : ℝ} (hβ : β < 1) (h1 : 0 < V₁)
    (h2 : 0 < V₂) :
    welfareFlex β φ ε A₀ γa V₂ < welfareFlex β φ ε A₀ γa V₁ ↔ V₁ < V₂ := by
  rw [welfareFlex_eq β φ ε A₀ γa V₂, welfareFlex_eq β φ ε A₀ γa V₁, sub_lt_sub_iff_left,
    div_lt_div_iff_of_pos_right (by linarith), Real.log_lt_log_iff h1 h2]

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is strictly decreasing in money growth `γ_m`
(among policies with an equilibrium, `Q* < 1`). -/
theorem welfare_strictAnti_gamma {β φ ε A₀ γa v γ₁ γ₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ₁ : 0 < 1 + γ₁) (h12 : γ₁ < γ₂) (hQ : Qstar β γ₁ v < 1) :
    welfareFlex β φ ε A₀ γa (velocity β γ₂ v) < welfareFlex β φ ε A₀ γa (velocity β γ₁ v) := by
  have hγ₂ : 0 < 1 + γ₂ := by linarith
  have hlt : Qstar β γ₂ v < Qstar β γ₁ v :=
    div_lt_div_of_pos_left (mul_pos hβ0 (Real.exp_pos _)) hγ₁ (by linarith)
  have hpos : 0 < Qstar β γ₂ v := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ₂
  rw [welfareFlex_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is strictly increasing in the variance `σ_m²` of
money growth (among policies with an equilibrium, `Q* < 1`): a higher variance raises
`E_t[M_t/M_{t+1}]`, the bond price and real balances. -/
theorem welfare_strictMono_var {β φ ε A₀ γa γ v₁ v₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (h12 : v₁ < v₂) (hQ : Qstar β γ v₂ < 1) :
    welfareFlex β φ ε A₀ γa (velocity β γ v₁) < welfareFlex β φ ε A₀ γa (velocity β γ v₂) := by
  have hlt : Qstar β γ v₁ < Qstar β γ v₂ := by
    unfold Qstar
    gcongr
  rw [welfareFlex_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: as a function of the constant nominal rate `i > 0`
(`Q* = e^{−i}`, `V = 1 − e^{−i}`), welfare is strictly decreasing. -/
theorem welfare_rate_strictAnti {β φ ε A₀ γa : ℝ} (hβ : β < 1) :
    StrictAntiOn (fun i => welfareFlex β φ ε A₀ γa (1 - Real.exp (-i))) (Set.Ioi 0) := by
  intro i hi j hj hij
  have hpos : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-x) := fun x hx => by
    have := Real.exp_lt_exp.2 (show -x < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  simp only
  rw [welfareFlex_lt_iff hβ (hpos i hi) (hpos j hj)]
  have := Real.exp_lt_exp.2 (show -j < -i by linarith)
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is unbounded as the nominal rate falls to zero:
`welfare(1 − e^{−i}) → ∞` as `i → 0⁺`. The Friedman rule is a supremum, not attained. -/
theorem tendsto_welfare_rate {β φ ε A₀ γa : ℝ} (hβ : β < 1) :
    Tendsto (fun i => welfareFlex β φ ε A₀ γa (1 - Real.exp (-i))) (𝓝[>] 0) atTop := by
  have hV : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝 0) (𝓝 (1 - Real.exp (-0))) :=
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).tendsto 0
      simp only [neg_zero, Real.exp_zero, sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with i hi
      have := Real.exp_lt_exp.2 (show -i < 0 by simp only [Set.mem_Ioi] at hi; linarith)
      rw [Real.exp_zero] at this
      simp only [Set.mem_Ioi]
      linarith
  have hlog : Tendsto (fun i : ℝ => -Real.log (1 - Real.exp (-i)) * (1 - β)⁻¹) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hV)).atTop_mul_const
      (inv_pos.2 (by linarith))
  refine (tendsto_atTop_add_const_left _ (welfareFlex β φ ε A₀ γa 1) hlog).congr fun i => ?_
  rw [welfareFlex_eq β φ ε A₀ γa (1 - Real.exp (-i))]
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124 (**the optimal policy must satisfy the Friedman rule**):
every policy `(γ_m, σ_m²)` with an equilibrium (`Q* < 1`, i.e. `i > 0`) is strictly improved
upon by another admissible policy with an equilibrium; so no policy with `i > 0` is optimal. -/
theorem not_optimal_of_equilibrium {β φ ε A₀ γa γ v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (hQ : Qstar β γ v < 1) :
    ∃ γ', 0 < 1 + γ' ∧ Qstar β γ' v < 1 ∧
      welfareFlex β φ ε A₀ γa (velocity β γ v) < welfareFlex β φ ε A₀ γa (velocity β γ' v) := by
  set q := Qstar β γ v with hq
  have hqpos : 0 < q := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ
  set q' := (q + 1) / 2 with hq'
  have hq'pos : 0 < q' := by rw [hq']; linarith
  have hb : 0 < β * Real.exp (v / 2) := mul_pos hβ0 (Real.exp_pos _)
  refine ⟨β * Real.exp (v / 2) / q' - 1, by simp only [add_sub_cancel]; positivity, ?_, ?_⟩
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [this, hq']; linarith
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [welfareFlex_lt_iff hβ1 (by rw [velocity, this, hq']; linarith)
      (by rw [velocity, ← hq]; linarith), velocity, velocity, this, ← hq, hq']
    linarith

/-! ### (e) Prices set one period in advance: the firm's problem -/

/-- Galí (2015), Ex. 4.5(e), p. 124: the firm's discounted real profit
`Λ_{t−1,t} (Y_t(i)/P_t)(P_t(i) − W_t/A_t)` with `Λ_{t−1,t} = β C_{t−1}/C_t`, demand
`Y_t(i) = (P_t(i)/P_t)^{−ε} Y_t` and `Y_t = C_t` equals
`β C_{t−1} P_t^{ε−1} · P_t(i)^{−ε}(P_t(i) − W_t/A_t)`. (The book prints the deflator `P_{t+1}`;
real profit at `t` is deflated by `P_t`.) -/
theorem sticky_objective_eq {β ε Cm Ct Pt x w : ℝ} (hCt : 0 < Ct) (hPt : 0 < Pt) (hx : 0 < x) :
    β * Cm / Ct * ((x / Pt) ^ (-ε) * Ct / Pt) * (x - w) =
      β * Cm * Pt ^ (ε - 1) * (x ^ (-ε) * (x - w)) := by
  rw [Real.div_rpow hx.le hPt.le, Real.rpow_neg hPt.le, Real.rpow_sub_one hPt.ne']
  field_simp

/-- Galí (2015), Ex. 4.5(e) (pull-out): for a price `x` and a factor `K` known at `t − 1`
(measurable for `G = ℱ_{t−1}`), the conditional expected profit is
`E[K x^{−ε}(x − w) | G] = K x^{−ε}(x − E[w | G])`. -/
theorem condExp_objective [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hx : StronglyMeasurable[G] x)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ) (hw : Integrable w μ) :
    μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] =ᵐ[μ]
      fun ω => K ω * (x ω ^ (-ε) * (x ω - μ[w | G] ω)) := by
  have hb : StronglyMeasurable[G] (fun ω => x ω ^ (-ε)) :=
    (hx.measurable.pow_const (-ε)).stronglyMeasurable
  have ha : StronglyMeasurable[G] (fun ω => x ω ^ (-ε) * x ω) := hb.mul hx
  have hsplit : (fun ω => x ω ^ (-ε) * (x ω - w ω)) =
      (fun ω => x ω ^ (-ε) * x ω) - fun ω => x ω ^ (-ε) * w ω := by
    funext ω; simp only [Pi.sub_apply]; ring
  have hg : Integrable (fun ω => x ω ^ (-ε) * (x ω - w ω)) μ := by
    rw [hsplit]; exact h1.sub h2
  have e1 : μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] =ᵐ[μ]
      fun ω => K ω * μ[fun ω => x ω ^ (-ε) * (x ω - w ω) | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hK hobj hg
  have e2 := condExp_sub h1 h2 G
  have e3 : μ[fun ω => x ω ^ (-ε) * w ω | G] =ᵐ[μ] fun ω => x ω ^ (-ε) * μ[w | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hb h2 hw
  rw [condExp_of_stronglyMeasurable hG ha h1, ← hsplit] at e2
  filter_upwards [e1, e2, e3] with ω h1' h2' h3'
  rw [h1', h2', Pi.sub_apply, h3']
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, optimality): with the price level and `C_{t−1}` known at
`t − 1`, the price `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]` maximises the conditional expected discounted
profit `E_{t−1}[K P_t(i)^{−ε}(P_t(i) − W_t/A_t)]` (`K = β C_{t−1} P_t^{ε−1} > 0`, see
`sticky_objective_eq`) against every admissible price set at `t − 1`. -/
theorem sticky_price_optimal [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    (hε : 1 < ε) {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hKpos : ∀ ω, 0 < K ω)
    (hw : Integrable w μ) (hwpos : ∀ᵐ ω ∂μ, 0 < μ[w | G] ω)
    (hx : StronglyMeasurable[G] x) (hxpos : ∀ ω, 0 < x ω)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ)
    (hobj' : Integrable (fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) *
      (markup ε * μ[w | G] ω - w ω))) μ)
    (h1' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω)) μ)
    (h2' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * w ω) μ) :
    ∀ᵐ ω ∂μ, μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] ω ≤
      μ[fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω - w ω)) | G] ω := by
  have hxs : StronglyMeasurable[G] (fun ω => markup ε * μ[w | G] ω) :=
    stronglyMeasurable_condExp.const_mul _
  filter_upwards [condExp_objective (mΩ := mΩ) hG hK hx hobj h1 h2 hw,
    condExp_objective (mΩ := mΩ) hG hK hxs hobj' h1' h2' hw, hwpos] with ω e1 e2 hpos
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (markup_pricing_le hε hpos (hxpos ω)) (hKpos ω).le

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, the first-order condition is necessary): a price set at
`t − 1` that does at least as well as `𝓜 E_{t−1}[W_t/A_t]` equals it almost surely; the optimal
preset price is `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]`. -/
theorem sticky_price_unique [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    (hε : 1 < ε) {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hKpos : ∀ ω, 0 < K ω)
    (hw : Integrable w μ) (hwpos : ∀ᵐ ω ∂μ, 0 < μ[w | G] ω)
    (hx : StronglyMeasurable[G] x) (hxpos : ∀ ω, 0 < x ω)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ)
    (hobj' : Integrable (fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) *
      (markup ε * μ[w | G] ω - w ω))) μ)
    (h1' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω)) μ)
    (h2' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * w ω) μ)
    (hopt : ∀ᵐ ω ∂μ,
      μ[fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω - w ω)) | G] ω ≤
        μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] ω) :
    x =ᵐ[μ] fun ω => markup ε * μ[w | G] ω := by
  have hxs : StronglyMeasurable[G] (fun ω => markup ε * μ[w | G] ω) :=
    stronglyMeasurable_condExp.const_mul _
  filter_upwards [condExp_objective (mΩ := mΩ) hG hK hx hobj h1 h2 hw,
    condExp_objective (mΩ := mΩ) hG hK hxs hobj' h1' h2' hw, hwpos, hopt] with ω e1 e2 hpos ho
  rw [e1, e2] at ho
  by_contra hne
  have := mul_lt_mul_of_pos_left (markup_pricing_lt hε hpos (hxpos ω) hne) (hKpos ω)
  linarith

/-- Galí (2015), Ex. 4.5(e): with labour supply `W/P = C N^φ` and `C = A N`, real marginal cost
in nominal terms is `W/A = P N^{1+φ}`. -/
theorem wage_over_tech {φ P W A C N : ℝ} (hP : 0 < P) (hA : 0 < A) (hN : 0 < N)
    (hlab : W / P = C * N ^ φ) (hC : C = A * N) : W / A = P * N ^ (1 + φ) := by
  rw [Real.rpow_add hN, Real.rpow_one]
  rw [div_eq_iff hP.ne'] at hlab
  rw [hlab, hC]
  field_simp

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): in a symmetric equilibrium with the price level `P_t`
known at `t − 1`, the pricing condition `P_t = 𝓜 E_{t−1}[W_t/A_t] = 𝓜 E_{t−1}[P_t N_t^{1+φ}]`
holds iff `E_{t−1}[N_t^{1+φ}] = 1/𝓜`: expected hours are at their flexible-price level. -/
theorem pricing_iff [IsFiniteMeasure μ] {G : MeasurableSpace Ω} {ε : ℝ} (hε : 1 < ε)
    {Pn X : Ω → ℝ} (hPn : StronglyMeasurable[G] Pn) (hPpos : ∀ ω, 0 < Pn ω)
    (hX : Integrable X μ) (hPX : Integrable (fun ω => Pn ω * X ω) μ) :
    (Pn =ᵐ[μ] fun ω => markup ε * μ[fun ω => Pn ω * X ω | G] ω) ↔
      μ[X | G] =ᵐ[μ] fun _ => (markup ε)⁻¹ := by
  have e : μ[fun ω => Pn ω * X ω | G] =ᵐ[μ] fun ω => Pn ω * μ[X | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hPn hPX hX
  have hM := markup_pos hε
  constructor
  · intro h
    filter_upwards [h, e] with ω h1 h2
    rw [h2] at h1
    have hp := hPpos ω
    field_simp
    nlinarith [h1]
  · intro h
    filter_upwards [h, e] with ω h1 h2
    rw [h2, h1]
    field_simp

/-! ### (e) The sticky-price equilibrium -/

omit mΩ in
/-- Galí (2015), Ex. 4.5: levels built from adapted innovations are adapted. -/
theorem measurable_level {m : MeasurableSpace Ω} (ℱ' : Filtration ℕ m) {X₀ γ : ℝ}
    {ε : ℕ → Ω → ℝ} (hε : ∀ s, Measurable[ℱ' s] (ε s)) (t : ℕ) :
    Measurable[ℱ' t] (level X₀ γ ε t) := by
  have hs : Measurable[ℱ' t] fun ω => ∑ s ∈ Finset.range t, ε (s + 1) ω :=
    Finset.measurable_sum _ fun s hs =>
      (hε (s + 1)).mono (ℱ'.mono (by simp only [Finset.mem_range] at hs; omega)) le_rfl
  exact (Real.measurable_exp.comp hs).const_mul _

/-- Galí (2015), Ex. 4.5: technology innovations are adapted. -/
theorem techShock_measurable (S : ShockPair μ ℱ) (s : ℕ) : Measurable[ℱ s] (techShock S s) :=
  measurable_fst.comp (S.adapted s)

/-- Galí (2015), Ex. 4.5: money innovations are adapted. -/
theorem moneyShock_measurable (S : ShockPair μ ℱ) (φa φv : ℝ) (s : ℕ) :
    Measurable[ℱ s] (moneyShock φa φv S s) :=
  ((measurable_fst.comp (S.adapted s)).const_mul φa).add
    ((measurable_snd.comp (S.adapted s)).const_mul φv)

/-- Galí (2015), Ex. 4.5(e): the innovation `ε^m_t − ε^a_t = (φ_a − 1) ε^a_t + φ_v ν_t` that
moves employment when prices are preset. -/
def gapShock (φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ :=
  fun t ω => (φa - 1) * (S.Z t ω).1 + φv * (S.Z t ω).2

/-- Galí (2015), Ex. 4.5(e): `ε^m_t − ε^a_t` is the gap innovation. -/
theorem moneyShock_sub_techShock (S : ShockPair μ ℱ) (φa φv : ℝ) (t : ℕ) (ω : Ω) :
    moneyShock φa φv S t ω - techShock S t ω = gapShock φa φv S t ω := by
  simp only [moneyShock, techShock, gapShock]; ring

variable (μ ℱ β φ ε A M C N Y P W Q)

/-- Galí (2015), Ex. 4.5(e), p. 124: an equilibrium when prices are set one period in advance.
Household conditions as in (a); `C = Y = A N`; the price level `P_{t+1}` is known at `t`
(`P_0` is set before the economy starts); hours are integrable; and the firms' first-order
condition, in the form `E_t[N_{t+1}^{1+φ}] = 1/𝓜` (`pricing_iff`), holds. -/
structure IsStickyEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply: `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand: `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation. -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Prices are set one period in advance: `P_{t+1}` is known at `t`. -/
  preset : ∀ t, Measurable[ℱ t] (P (t + 1))
  /-- The initial price level is set before the shocks: it is deterministic. -/
  preset0 : ∀ ω ω', P 0 ω = P 0 ω'
  /-- Hours to the power `1 + φ` are integrable. -/
  integrable_hours : ∀ t, Integrable (fun ω => N t ω ^ (1 + φ)) μ
  /-- The firms' first-order condition: `E_t[N_{t+1}^{1+φ}] = 1/𝓜`. -/
  pricing : ∀ t, μ[fun ω => N (t + 1) ω ^ (1 + φ) | ℱ t] =ᵐ[μ] fun _ => (markup ε)⁻¹
  /-- The first-order condition at date 0, with no information: `E[N_0^{1+φ}] = 1/𝓜`. -/
  pricing0 : ∫ ω, N 0 ω ^ (1 + φ) ∂μ = (markup ε)⁻¹
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ ε A M C N Y P W Q}

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, solving exactly): in a sticky-price equilibrium with
constant velocity `V`, employment is
`N_{t+1} = 𝓜^{−1/(1+φ)} exp((ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2)`, `s² = var(ε^m − ε^a)`,
almost surely. -/
theorem sticky_employment [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) :
    N (t + 1) =ᵐ[μ] fun ω => Nflex φ ε *
      Real.exp (gapShock φa φv S (t + 1) ω - (1 + φ) * varX S.va φa φv / 2) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have h1φ : 0 < 1 + φ := by linarith
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (by rw [← h.clearing]; exact h.pos_C 0 ω₀))
      (hMp 0 ω₀)
  have hNeq : ∀ s ω, N s ω = V * level M₀ γm (moneyShock φa φv S) s ω /
      (P s ω * level A₀ γa (techShock S) s ω) := fun s ω => by
    have e := hV s ω
    rw [h.technology s ω] at e
    rw [← e]
    field_simp [(hMp s ω).ne', (h.pos_P s ω).ne', (hAp s ω).ne']
  set R : Ω → ℝ := fun ω => V * level M₀ γm (moneyShock φa φv S) t ω * (1 + γm) /
      (P (t + 1) ω * (level A₀ γa (techShock S) t ω * (1 + γa)))
    with hR
  have hRpos : ∀ ω, 0 < R ω := fun ω => div_pos (mul_pos (mul_pos hVpos (hMp t ω)) hγm)
    (mul_pos (h.pos_P (t + 1) ω) (mul_pos (hAp t ω) hγa))
  have hNR : ∀ ω, N (t + 1) ω = R ω * Real.exp (gapShock φa φv S (t + 1) ω) := fun ω => by
    rw [hNeq, level_succ, level_succ, ← moneyShock_sub_techShock, Real.exp_sub]
    simp only [hR]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', (h.pos_P (t + 1) ω).ne']
  have hRmeas : Measurable[ℱ t] R :=
    (((measurable_const.mul (measurable_level ℱ (moneyShock_measurable S φa φv) t)).mul_const
      _).div ((h.preset t).mul ((measurable_level ℱ (techShock_measurable S) t).mul_const _)))
  set a := (1 + φ) * (φa - 1) with ha
  set b := (1 + φ) * φv with hb
  have hpow : ∀ ω, N (t + 1) ω ^ (1 + φ) =
      R ω ^ (1 + φ) * Real.exp (a * (S.Z (t + 1) ω).1 + b * (S.Z (t + 1) ω).2) := fun ω => by
    rw [hNR, Real.mul_rpow (hRpos ω).le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    simp only [gapShock, ha, hb]; ring
  have hE := condExp_shock S (g := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (by fun_prop) t
  have hint := h.integrable_hours (t + 1)
  have hfun : (fun ω => N (t + 1) ω ^ (1 + φ)) =
      (fun ω => R ω ^ (1 + φ)) * fun ω => Real.exp (a * (S.Z (t + 1) ω).1 +
        b * (S.Z (t + 1) ω).2) := by
    funext ω; rw [hpow]; rfl
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) (μ := μ)
    (hRmeas.pow_const (1 + φ)).stronglyMeasurable (hfun ▸ hint) (integrable_exp_shock S a b (t + 1))
  have hpr := h.pricing t
  rw [hfun] at hpr
  filter_upwards [hpull, hE, hpr] with ω e1 e2 e3
  rw [e3, Pi.mul_apply, e2, integral_exp_pair] at e1
  -- e1 : 𝓜⁻¹ = R ω ^ (1+φ) * exp((a² va + b²)/2)
  have hkey : (a ^ 2 * S.va + b ^ 2) / 2 = (1 + φ) ^ 2 * varX S.va φa φv / 2 := by
    simp only [ha, hb, varX]; ring
  rw [hkey] at e1
  have hR1 : R ω ^ (1 + φ) = (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) := by
    rw [Real.exp_neg, e1]
    field_simp
  have hRval : R ω = Nflex φ ε * Real.exp (-((1 + φ) * varX S.va φa φv / 2)) := by
    rw [← Real.rpow_rpow_inv (hRpos ω).le h1φ.ne', hR1,
      Real.mul_rpow (inv_pos.2 (markup_pos hε)).le (Real.exp_pos _).le, ← Real.exp_mul, Nflex]
    congr 2
    field_simp
  rw [hNR, hRval, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): at date 0 (price set with no information and
deterministic initial conditions) employment is at its flexible-price level. -/
theorem sticky_employment_zero [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (ω : Ω) :
    N 0 ω = Nflex φ ε := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNeq : ∀ ω, N 0 ω = V * M₀ / (P 0 ω * A₀) := fun ω => by
    have e := hV 0 ω
    rw [h.technology 0 ω, level_zero, level_zero] at e
    rw [← e]
    field_simp [hM.ne', (h.pos_P 0 ω).ne', hA.ne']
  have hconst : ∀ ω', N 0 ω' = N 0 ω := fun ω' => by rw [hNeq, hNeq, h.preset0 ω' ω]
  have h0 := h.pricing0
  rw [show (fun ω' => N 0 ω' ^ (1 + φ)) = fun _ => N 0 ω ^ (1 + φ) by
    funext ω'; rw [hconst], integral_const, probReal_univ, one_smul] at h0
  rw [Nflex, ← h0, Real.rpow_rpow_inv (h.pos_N 0 ω).le (by linarith)]

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): in a sticky-price equilibrium with constant velocity,
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`, as under flexible prices. -/
theorem sticky_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    V = velocity β γm (varM S.va φa φv) :=
  velocity_of_euler S β hM hγm h.pos_C h.pos_P h.money h.euler fun t ω => by
    rw [h.clearing t ω]; exact hV t ω

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): output is `Y_t = A_t N_t` and real balances are
`M_t/P_t = A_t N_t / V`. -/
theorem sticky_output_balances {β φ ε V : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    Y t ω = A t ω * N t ω ∧ M t ω / P t ω = A t ω * N t ω / V := by
  refine ⟨h.technology t ω, ?_⟩
  rw [← h.technology t ω, ← hV t ω]
  field_simp [(hM t ω).ne', (h.pos_P t ω).ne']
  have := (h.clearing t ω).symm ▸ h.pos_C t ω
  field_simp [this.ne']

/-- Galí (2015), Ex. 4.5(e): the closed-form sticky-price employment
`N_0 = 𝓜^{−1/(1+φ)}`, `N_{t+1} = 𝓜^{−1/(1+φ)} exp((ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2)`. -/
noncomputable def stickyN (φ ε φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ
  | 0 => fun _ => Nflex φ ε
  | t + 1 => fun ω => Nflex φ ε *
      Real.exp (gapShock φa φv S (t + 1) ω - (1 + φ) * varX S.va φa φv / 2)

/-- Galí (2015), Ex. 4.5(e): sticky-price employment is positive. -/
theorem stickyN_pos {φ ε φa φv : ℝ} (hε : 1 < ε) (S : ShockPair μ ℱ) (t : ℕ) (ω : Ω) :
    0 < stickyN φ ε φa φv S t ω := by
  cases t with
  | zero => exact Nflex_pos hε
  | succ t => exact mul_pos (Nflex_pos hε) (Real.exp_pos _)

/-- Galí (2015), Ex. 4.5(e):
`N_{t+1}^{1+φ} = 𝓜⁻¹ e^{−(1+φ)² s²/2} e^{(1+φ)(φ_a − 1) ε^a_{t+1} + (1+φ) φ_v ν_{t+1}}`. -/
theorem stickyN_rpow_succ {φ ε φa φv : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (S : ShockPair μ ℱ)
    (t : ℕ) (ω : Ω) :
    stickyN φ ε φa φv S (t + 1) ω ^ (1 + φ) =
      (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) *
        Real.exp ((1 + φ) * (φa - 1) * (S.Z (t + 1) ω).1 + (1 + φ) * φv * (S.Z (t + 1) ω).2) := by
  simp only [stickyN]
  rw [Real.mul_rpow (Nflex_pos hε).le (Real.exp_pos _).le, Nflex_rpow hφ hε, ← Real.exp_mul,
    mul_assoc, ← Real.exp_add]
  congr 2
  simp only [gapShock]
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, existence): if `β e^{σ_m²/2} < 1 + γ_m`, the allocation
`N = stickyN`, `C = Y = A N`, `P = V M/(A N)`, `W = P C N^φ`, `Q = Q*`, `V = 1 − Q*`, is an
exact equilibrium with prices set one period in advance. -/
theorem sticky_candidate [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa)
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM S.va φa φv) < 1) :
    IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) (level M₀ γm (moneyShock φa φv S))
      (fun t ω => level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω)
      (stickyN φ ε φa φv S)
      (fun t ω => level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω)
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω))
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω) *
          (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω) *
          stickyN φ ε φa φv S t ω ^ φ)
      (fun _ _ => Qstar β γm (varM S.va φa φv)) := by
  set V := velocity β γm (varM S.va φa φv) with hVdef
  have hV : 0 < V := by rw [hVdef, velocity]; linarith
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNp := stickyN_pos (φ := φ) (φa := φa) (φv := φv) hε S
  set a := (1 + φ) * (φa - 1) with ha
  set b := (1 + φ) * φv with hb
  set k := (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) with hk
  have hkey : k * Real.exp ((a ^ 2 * S.va + b ^ 2) / 2) = (markup ε)⁻¹ := by
    rw [hk, mul_assoc, ← Real.exp_add]
    rw [show -((1 + φ) ^ 2 * varX S.va φa φv / 2) + (a ^ 2 * S.va + b ^ 2) / 2 = 0 by
      simp only [ha, hb, varX]; ring, Real.exp_zero, mul_one]
  have hpowfun : ∀ t, (fun ω => stickyN φ ε φa φv S (t + 1) ω ^ (1 + φ)) =
      fun ω => (fun q : ℝ × ℝ => k * Real.exp (a * q.1 + b * q.2)) (S.Z (t + 1) ω) := by
    intro t; funext ω; rw [stickyN_rpow_succ hφ hε S t ω]
  refine ⟨fun t ω => mul_pos (hAp t ω) (hNp t ω), hNp, fun t ω => div_pos (mul_pos hV (hMp t ω))
    (mul_pos (hAp t ω) (hNp t ω)), fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_,
    fun ω ω' => ?_, fun t => ?_, fun t => ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · field_simp [(hAp t ω).ne', (hMp t ω).ne', (hNp t ω).ne', hV.ne']
  · rw [show 1 - Qstar β γm (varM S.va φa φv) = V from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', (hNp t ω).ne', hV.ne']
  · refine (eulerRHS_of_const_velocity S β hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne', (hNp t ω).ne']
  · have hfun : (fun ω => V * level M₀ γm (moneyShock φa φv S) (t + 1) ω /
        (level A₀ γa (techShock S) (t + 1) ω * stickyN φ ε φa φv S (t + 1) ω)) =
        fun ω => V * level M₀ γm (moneyShock φa φv S) t ω * (1 + γm) *
          Real.exp ((1 + φ) * varX S.va φa φv / 2) /
          (level A₀ γa (techShock S) t ω * (1 + γa) * Nflex φ ε) := by
      funext ω
      have hsplit : moneyShock φa φv S (t + 1) ω =
          techShock S (t + 1) ω + gapShock φa φv S (t + 1) ω := by
        rw [← moneyShock_sub_techShock]; ring
      simp only [stickyN]
      rw [level_succ, level_succ, hsplit, Real.exp_add, Real.exp_sub]
      field_simp [(hAp t ω).ne', (hMp t ω).ne', (Nflex_pos (φ := φ) hε).ne']
    change Measurable[ℱ t] (fun ω => V * level M₀ γm (moneyShock φa φv S) (t + 1) ω /
        (level A₀ γa (techShock S) (t + 1) ω * stickyN φ ε φa φv S (t + 1) ω))
    rw [hfun]
    exact ((((measurable_level ℱ (moneyShock_measurable S φa φv) t).const_mul V).mul_const
      _).mul_const _).div (((measurable_level ℱ (techShock_measurable S) t).mul_const
        _).mul_const _)
  · simp only [stickyN, level_zero]
  · cases t with
    | zero => exact integrable_const (Nflex φ ε ^ (1 + φ))
    | succ t =>
      rw [hpowfun t]
      exact (integrable_exp_shock S a b (t + 1)).const_mul k
  · rw [hpowfun t]
    refine (condExp_shock S (g := fun q : ℝ × ℝ => k * Real.exp (a * q.1 + b * q.2))
      (by fun_prop) t).trans (Filter.Eventually.of_forall fun _ => ?_)
    simp only
    rw [integral_const_mul, integral_exp_pair, hkey]
  · simp only [stickyN]
    rw [integral_const, probReal_univ, one_smul, Nflex_rpow hφ hε]

/-! ### (f) Expected utility with prices set in advance -/

/-- Galí (2015), Ex. 4.5(f), p. 124: in a sticky-price equilibrium with constant velocity `V`,
period utility is `2 log A_t + 2 log N_t − log V − N_t^{1+φ}/(1+φ)`. -/
theorem sticky_period_utility {β φ ε V : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hA : ∀ t ω, 0 < A t ω)
    (hM : ∀ t ω, 0 < M t ω) (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (hVpos : 0 < V)
    (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) = 2 * Real.log (A t ω) +
      2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ) := by
  have hb := (sticky_output_balances h hM hV t ω).2
  have hC : C t ω = A t ω * N t ω := (h.clearing t ω).trans (h.technology t ω)
  have hAN := mul_pos (hA t ω) (h.pos_N t ω)
  rw [utility, hC, hb, Real.log_div hAN.ne' hVpos.ne',
    Real.log_mul (hA t ω).ne' (h.pos_N t ω).ne']
  ring

/-- Galí (2015), Ex. 4.5(f): expected lifetime utility with prices set in advance,
`welfareFlex − (1 + φ) s² β/(1 − β)`: the flexible-price value minus the cost
`(1 + φ) s²` per period of employment fluctuations. -/
noncomputable def stickyWelfare (β φ ε A₀ γa V s2 : ℝ) : ℝ :=
  welfareFlex β φ ε A₀ γa V - (1 + φ) * s2 * β / (1 - β)

/-- **Ex. 4.5(f)** (Galí 2015, p. 124): in a sticky-price equilibrium with constant velocity,
expected utility at date `t + 1` is
`2 E log A_{t+1} + 2 log N − (1+φ) s² − log V − 𝓜⁻¹/(1+φ)` (Gaussian moments). -/
theorem sticky_expected_utility_succ [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (hVpos : 0 < V)
    (t : ℕ) :
    ∫ ω, utility φ (C (t + 1) ω) (level M₀ γm (moneyShock φa φv S) (t + 1) ω / P (t + 1) ω)
        (N (t + 1) ω) ∂μ =
      2 * (Real.log A₀ + (t + 1 : ℕ) * Real.log (1 + γa)) + 2 * Real.log (Nflex φ ε) -
        (1 + φ) * varX S.va φa φv - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNae := sticky_employment S hφ hε hA hγa hM hγm h hV t
  have hlogN : (fun ω => Real.log (N (t + 1) ω)) =ᵐ[μ] fun ω =>
      (Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2) +
        ((φa - 1) * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) := by
    filter_upwards [hNae] with ω hω
    rw [hω, Real.log_mul (Nflex_pos hε).ne' (Real.exp_pos _).ne', Real.log_exp]
    simp only [gapShock]; ring
  have hlogNint : Integrable (fun ω => Real.log (N (t + 1) ω)) μ :=
    ((integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1))).congr hlogN.symm
  have hlogNE : ∫ ω, Real.log (N (t + 1) ω) ∂μ =
      Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2 := by
    rw [integral_congr_ae hlogN, integral_add (integrable_const _)
      (integrable_lin S (φa - 1) φv (t + 1)), integral_lin, integral_const, probReal_univ,
      one_smul, add_zero]
  have hpowE : ∫ ω, N (t + 1) ω ^ (1 + φ) ∂μ = (markup ε)⁻¹ := by
    rw [← integral_condExp (ℱ.le t), integral_congr_ae (h.pricing t), integral_const,
      probReal_univ, one_smul]
  have hfun : (fun ω => utility φ (C (t + 1) ω)
      (level M₀ γm (moneyShock φa φv S) (t + 1) ω / P (t + 1) ω) (N (t + 1) ω)) =
      fun ω => (2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
        2 * Real.log (N (t + 1) ω) - Real.log V) - N (t + 1) ω ^ (1 + φ) / (1 + φ) := by
    funext ω
    rw [sticky_period_utility h hAp hMp hV hVpos]
  have i1 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω)) μ :=
    (integrable_log_tech S hA hγa (t + 1)).const_mul 2
  have i2 : Integrable (fun ω => 2 * Real.log (N (t + 1) ω)) μ := hlogNint.const_mul 2
  have i12 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
      2 * Real.log (N (t + 1) ω)) μ := i1.add i2
  have i123 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
      2 * Real.log (N (t + 1) ω) - Real.log V) μ := i12.sub (integrable_const _)
  have i4 : Integrable (fun ω => N (t + 1) ω ^ (1 + φ) / (1 + φ)) μ :=
    (h.integrable_hours (t + 1)).div_const _
  rw [hfun, integral_sub i123 i4, integral_sub i12 (integrable_const _), integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_div, integral_log_tech S hA hγa (t + 1),
    hlogNE, hpowE, integral_const, probReal_univ, one_smul]
  ring

/-- **Ex. 4.5(f)** (Galí 2015, p. 124): at date 0 expected utility is
`2 log A₀ + 2 log N − log V − 𝓜⁻¹/(1+φ)` (employment is at its flexible-price level). -/
theorem sticky_expected_utility_zero [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (hVpos : 0 < V) :
    ∫ ω, utility φ (C 0 ω) (level M₀ γm (moneyShock φa φv S) 0 ω / P 0 ω) (N 0 ω) ∂μ =
      2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hfun : (fun ω => utility φ (C 0 ω) (level M₀ γm (moneyShock φa φv S) 0 ω / P 0 ω)
      (N 0 ω)) = fun _ => 2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V -
        (markup ε)⁻¹ / (1 + φ) := by
    funext ω
    have hN := sticky_employment_zero S hφ hA hγa hM hγm h hV ω
    rw [sticky_period_utility h hAp hMp hV hVpos, hN, level_zero]
    rw [Nflex_rpow hφ hε]
  rw [hfun, integral_const, probReal_univ, one_smul]

/-- **Ex. 4.5(f)** (Galí 2015, p. 124, infinite horizon): in a sticky-price equilibrium with
constant velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to
`stickyWelfare = welfareFlex − (1 + φ) s² β/(1 − β)`, `s² = (φ_a − 1)² σ_a² + φ_v²`. -/
theorem hasSum_sticky_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω)
        (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ)
      (stickyWelfare β φ ε A₀ γa V (varX S.va φa φv)) := by
  have hVpos : 0 < V := by
    obtain ⟨ω₀, -⟩ := (h.euler 0).exists
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγm _ 0 ω₀)
  set K := 2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ)
    with hK
  set c := 2 * Real.log (1 + γa) with hc
  set d := (1 + φ) * varX S.va φa φv with hd
  have hterm : ∀ t : ℕ, β ^ t * ∫ ω, utility φ (C t ω)
      (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ =
      β ^ t * (K + c * t) - d * β ^ t + d * (if t = 0 then 1 else 0) := by
    intro t
    cases t with
    | zero =>
      rw [sticky_expected_utility_zero S hφ hε hA hγa hM hγm h hV hVpos]
      simp only [pow_zero, one_mul, ↓reduceIte, CharP.cast_eq_zero, mul_zero, add_zero, hK]
      ring
    | succ t =>
      rw [sticky_expected_utility_succ S hφ hε hA hγa hM hγm h hV hVpos t]
      simp only [Nat.succ_ne_zero, ↓reduceIte, mul_zero, add_zero, hK, hc, hd]
      ring
  have h1 := hasSum_affine (K := K) (c := c) hβ0 hβ1
  have h2 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left d
  have h3 := (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).mul_left d
  have hne : (1 - β) ≠ 0 := by linarith
  convert (h1.sub h2).add h3 using 1
  · funext t
    rw [hterm t]
  · rw [stickyWelfare, welfareFlex, hK, hc, hd]
    field_simp
    ring

/-! ### (g) Optimal monetary policy within the class of money supply rules -/

/-- Galí (2015), Ex. 4.5(g), p. 124: expected lifetime utility under the rule
`(γ_m, φ_a, φ_v)`: velocity `V = 1 − β e^{σ_m²/2}/(1 + γ_m)` with `σ_m² = φ_a² σ_a² + φ_v²`,
and employment variance `s² = (φ_a − 1)² σ_a² + φ_v²`. -/
noncomputable def policyWelfare (β φ ε A₀ γa va γm φa φv : ℝ) : ℝ :=
  stickyWelfare β φ ε A₀ γa (velocity β γm (varM va φa φv)) (varX va φa φv)

/-- Galí (2015), Ex. 4.5(f)–(g): prices set in advance never do better than flexible prices with
the same velocity: `stickyWelfare ≤ welfareFlex`. -/
theorem stickyWelfare_le_flex {β φ ε A₀ γa V s2 : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hs : 0 ≤ s2) : stickyWelfare β φ ε A₀ γa V s2 ≤ welfareFlex β φ ε A₀ γa V := by
  unfold stickyWelfare
  have : 0 ≤ (1 + φ) * s2 * β / (1 - β) := by
    apply div_nonneg _ (by linarith); positivity
  linarith

/-- Galí (2015), Ex. 4.5(f)–(g): for `0 < β < 1` the sticky-price welfare equals the
flexible-price welfare iff `s² = 0`. -/
theorem stickyWelfare_eq_flex_iff {β φ ε A₀ γa V s2 : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    stickyWelfare β φ ε A₀ γa V s2 = welfareFlex β φ ε A₀ γa V ↔ s2 = 0 := by
  unfold stickyWelfare
  have hpos : 0 < (1 + φ) * β / (1 - β) := div_pos (by positivity) (by linarith)
  constructor
  · intro h
    have : (1 + φ) * s2 * β / (1 - β) = 0 := by linarith
    rw [show (1 + φ) * s2 * β / (1 - β) = s2 * ((1 + φ) * β / (1 - β)) by ring] at this
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  · rintro rfl; simp

/-- Galí (2015), Ex. 4.5(g): with `σ_a² > 0`, the employment variance vanishes,
`(φ_a − 1)² σ_a² + φ_v² = 0`, iff `φ_a = 1` and `φ_v = 0`. -/
theorem varX_eq_zero_iff {va φa φv : ℝ} (hva : 0 < va) :
    varX va φa φv = 0 ↔ φa = 1 ∧ φv = 0 := by
  unfold varX
  constructor
  · intro h
    have h1 : (φa - 1) ^ 2 * va = 0 := by nlinarith [sq_nonneg (φa - 1), sq_nonneg φv]
    have h2 : φv ^ 2 = 0 := by nlinarith [sq_nonneg (φa - 1), sq_nonneg φv]
    refine ⟨?_, pow_eq_zero_iff (two_ne_zero) |>.1 h2⟩
    have := (mul_eq_zero.1 h1).resolve_right hva.ne'
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro ⟨rfl, rfl⟩; ring

/-- Galí (2015), Ex. 4.5(g): for every money growth rate the welfare of the rule is
`welfareFlex(V) − (1 + φ) s² β/(1 − β)`; with the same bond price `Q*` (hence the same nominal
rate and velocity) the rule `φ_a = 1, φ_v = 0` is at least as good as any `(φ_a, φ_v)`, and
strictly better unless `φ_a = 1, φ_v = 0` (for `σ_a² > 0`). -/
theorem stabilization_optimal {β φ ε A₀ γa va γm φa φv γm' : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hva : 0 < va)
    (hQ : Qstar β γm' (varM va 1 0) = Qstar β γm (varM va φa φv)) :
    policyWelfare β φ ε A₀ γa va γm φa φv ≤ policyWelfare β φ ε A₀ γa va γm' 1 0 ∧
      (¬ (φa = 1 ∧ φv = 0) →
        policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' 1 0) := by
  have hv : velocity β γm' (varM va 1 0) = velocity β γm (varM va φa φv) := by
    rw [velocity, velocity, hQ]
  have h10 : varX va 1 0 = 0 := by unfold varX; ring
  have hflex : policyWelfare β φ ε A₀ γa va γm' 1 0 =
      welfareFlex β φ ε A₀ γa (velocity β γm (varM va φa φv)) := by
    rw [policyWelfare, hv, h10, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 rfl]
  rw [hflex]
  refine ⟨stickyWelfare_le_flex hφ hβ0.le hβ1 (varX_nonneg hva.le _ _), fun hne => ?_⟩
  refine lt_of_le_of_ne (stickyWelfare_le_flex hφ hβ0.le hβ1 (varX_nonneg hva.le _ _))
    fun heq => hne ?_
  exact (varX_eq_zero_iff hva).1 ((stickyWelfare_eq_flex_iff hφ hβ0 hβ1).1 heq)

/-- Galí (2015), Ex. 4.5(g): any bond price `Q* > 0` can be attained by the rule with
`φ_a = 1, φ_v = 0` (choosing `1 + γ_m = β e^{σ_a²/2}/Q*`). -/
theorem exists_gamma_for_qstar {β va q : ℝ} (hβ0 : 0 < β) (hq : 0 < q) :
    ∃ γm, 0 < 1 + γm ∧ Qstar β γm (varM va 1 0) = q := by
  refine ⟨β * Real.exp (varM va 1 0 / 2) / q - 1, by
    simp only [add_sub_cancel]; positivity, ?_⟩
  rw [Qstar, add_sub_cancel]
  field_simp

/-- **Ex. 4.5(g)** (Galí 2015, p. 124): every rule `(γ_m, φ_a, φ_v)` with `(φ_a, φ_v) ≠ (1, 0)`
and an equilibrium is strictly improved upon by the rule with `φ_a = 1` (money accommodates
technology one for one), `φ_v = 0` (no noise) and the same nominal interest rate. -/
theorem stabilization_improves {β φ ε A₀ γa va γm φa φv : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hva : 0 < va) (hγm : 0 < 1 + γm) (hne : ¬ (φa = 1 ∧ φv = 0)) :
    ∃ γm', 0 < 1 + γm' ∧ Qstar β γm' (varM va 1 0) = Qstar β γm (varM va φa φv) ∧
      policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' 1 0 := by
  have hq : 0 < Qstar β γm (varM va φa φv) := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγm
  obtain ⟨γm', hγ', hQ'⟩ := exists_gamma_for_qstar (va := va) hβ0 hq
  exact ⟨γm', hγ', hQ', (stabilization_optimal hφ hβ0 hβ1 hva hQ').2 hne⟩

/-- **Ex. 4.5(g)** (Galí 2015, pp. 124–125; **correction**): no rule is optimal. Every rule with an
equilibrium (`Q* < 1`, i.e. a positive nominal rate) is strictly improved upon by another rule
with an equilibrium: lowering money growth towards the Friedman-rule level raises welfare
without bound. -/
theorem policy_not_optimal {β φ ε A₀ γa va γm φa φv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ γm', 0 < 1 + γm' ∧ Qstar β γm' (varM va φa φv) < 1 ∧
      policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' φa φv := by
  obtain ⟨γ', h1, h2, h3⟩ := not_optimal_of_equilibrium (φ := φ) (ε := ε) (A₀ := A₀) (γa := γa)
    hβ0 hβ1 hγm hQ
  refine ⟨γ', h1, h2, ?_⟩
  unfold policyWelfare stickyWelfare
  linarith

/-- Galí (2015), Ex. 4.5(g): along the rules with `φ_a = 1, φ_v = 0`, welfare equals the
flexible-price welfare and is unbounded as money growth falls to the Friedman-rule level
`1 + γ_m = β e^{σ_a²/2}` (`Q* ↑ 1`, nominal rate `↓ 0`): the Friedman rule with
`φ_a = 1, φ_v = 0` is the supremum. -/
theorem tendsto_policyWelfare_friedman {β φ ε A₀ γa va : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    Tendsto (fun γm => policyWelfare β φ ε A₀ γa va γm 1 0)
      (𝓝[>] (β * Real.exp (varM va 1 0 / 2) - 1)) atTop := by
  set γF := β * Real.exp (varM va 1 0 / 2) - 1 with hγF
  have hF : 0 < 1 + γF := by rw [hγF]; simp only [add_sub_cancel]; positivity
  have hV : ∀ γm, γF < γm → velocity β γm (varM va 1 0) = (γm - γF) / (1 + γm) := by
    intro γm hγ
    have : 0 < 1 + γm := by linarith
    rw [velocity, Qstar, show β * Real.exp (varM va 1 0 / 2) = 1 + γF by rw [hγF]; ring]
    field_simp
    ring
  have h10 : varX va 1 0 = 0 := by unfold varX; ring
  have hlim : Tendsto (fun γm : ℝ => (γm - γF) / (1 + γm)) (𝓝[>] γF) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun γm : ℝ => (γm - γF) / (1 + γm)) (𝓝 γF) (𝓝 ((γF - γF) / (1 + γF))) :=
        ((continuous_id.sub continuous_const).tendsto γF).div
          ((continuous_const.add continuous_id).tendsto γF) hF.ne'
      rw [sub_self, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γm hγ
      simp only [Set.mem_Ioi] at hγ ⊢
      exact div_pos (by linarith) (by linarith)
  have hlog : Tendsto (fun γm : ℝ => -Real.log ((γm - γF) / (1 + γm)) * (1 - β)⁻¹) (𝓝[>] γF)
      atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hlim)).atTop_mul_const
      (inv_pos.2 (by linarith))
  refine (tendsto_atTop_add_const_left _ (welfareFlex β φ ε A₀ γa 1) hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γm hγ
  simp only [Set.mem_Ioi] at hγ
  rw [policyWelfare, h10, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 rfl, hV γm hγ,
    welfareFlex_eq β φ ε A₀ γa ((γm - γF) / (1 + γm))]
  ring

/-- **Ex. 4.5(g)** (Galí 2015, p. 125: the optimal rule replicates the flexible-price
equilibrium): with `φ_a = 1` and `φ_v = 0` (`ε^m = ε^a`), sticky-price employment is
`N_t = 𝓜^{−1/(1+φ)}` at every date and state, the flexible-price level. -/
theorem stickyN_replicates (S : ShockPair μ ℱ) (φ ε : ℝ) (t : ℕ) (ω : Ω) :
    stickyN φ ε 1 0 S t ω = Nflex φ ε := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [stickyN, gapShock, varX]
    ring_nf
    simp

/-- **Ex. 4.5(g)** (Galí 2015, p. 125): under the rule `φ_a = 1, φ_v = 0` the sticky-price
equilibrium allocation (employment, output, consumption, price level, real balances) coincides
with the flexible-price equilibrium allocation, state by state. -/
theorem sticky_replicates_flex (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm : ℝ} (t : ℕ) (ω : Ω) :
    stickyN φ ε 1 0 S t ω = Nflex φ ε ∧
      level A₀ γa (techShock S) t ω * stickyN φ ε 1 0 S t ω =
        level A₀ γa (techShock S) t ω * Nflex φ ε ∧
      velocity β γm (varM S.va 1 0) * level M₀ γm (moneyShock 1 0 S) t ω /
          (level A₀ γa (techShock S) t ω * stickyN φ ε 1 0 S t ω) =
        velocity β γm (varM S.va 1 0) * level M₀ γm (moneyShock 1 0 S) t ω /
          (level A₀ γa (techShock S) t ω * Nflex φ ε) := by
  rw [stickyN_replicates]
  exact ⟨rfl, rfl, rfl⟩

/-- **Ex. 4.5(g)** (Galí 2015, p. 125): in *every* sticky-price equilibrium with constant
velocity under the rule `φ_a = 1, φ_v = 0`, employment is at its flexible-price level almost
surely. -/
theorem sticky_employment_replicates [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock 1 0 S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock 1 0 S) t ω = V) (t : ℕ) :
    N t =ᵐ[μ] fun _ => Nflex φ ε := by
  cases t with
  | zero => exact Filter.Eventually.of_forall fun ω =>
      sticky_employment_zero S hφ hA hγa hM hγm h hV ω
  | succ t =>
    filter_upwards [sticky_employment S hφ hε hA hγa hM hγm h hV t] with ω hω
    rw [hω]
    simp only [gapShock, varX]
    ring_nf
    simp

/-- Galí (2015), Ex. 4.5(g): the rule `φ_a = 1, φ_v = 0` attains the flexible-price welfare. -/
theorem policyWelfare_replicates {β φ ε A₀ γa va γm : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    policyWelfare β φ ε A₀ γa va γm 1 0 =
      welfareFlex β φ ε A₀ γa (velocity β γm (varM va 1 0)) := by
  rw [policyWelfare, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 (by unfold varX; ring)]

/-- Galí (2015), Ex. 4.5(g), p. 125: the non-negativity constraint on the nominal rate,
`Q* ≤ 1`, with `φ_a = 1, φ_v = 0` reads `β e^{σ_a²/2} ≤ 1 + γ_m`; the Friedman-rule level is
`1 + γ_m = β e^{σ_a²/2}`. -/
theorem friedman_level_of_replicating {β γm va : ℝ} (hγm : 0 < 1 + γm) :
    Qstar β γm (varM va 1 0) ≤ 1 ↔ β * Real.exp (va / 2) ≤ 1 + γm := by
  rw [qstar_le_one_iff hγm]
  unfold varM
  ring_nf

/-! ### A concrete probability space carrying the shocks (non-vacuity) -/

/-- Galí (2015), Ex. 4.5: the sample space `ℕ → ℝ × ℝ` of innovation sequences with the i.i.d.
product law `⊗ₜ N(0, σ_a²) ⊗ N(0, 1)` (`Measure.infinitePi`). -/
noncomputable abbrev shockMeasure (va : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => pairLaw va

/-- Galí (2015), Ex. 4.5: the natural filtration `ℱ_t = σ((ε^a_s, ν_s), s ≤ t)`. -/
noncomputable def shockFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) :=
  Filtration.natural (fun (i : ℕ) (ω : ℕ → ℝ × ℝ) => ω i)
    fun i => (measurable_pi_apply i).stronglyMeasurable

/-- Galí (2015), Ex. 4.5: the date-`t+1` innovation pair is independent of `ℱ_t` under the
product law (restated from the Chapter 2 project). -/
theorem coord_indep (va : ℝ≥0) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω (t + 1)) inferInstance)
      (shockFiltration t) (shockMeasure va) := by
  have hI : iIndep (fun i => MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance)
      (shockMeasure va) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ (x : ℝ × ℝ) => x)
      (P := fun _ : ℕ => pairLaw va) (fun _ => measurable_id))
  have h := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hI
    (S := {t + 1}) (T := Set.Iic t) (Set.disjoint_singleton_left.2 (by simp))
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iic] at h
  exact h

/-- Galí (2015), Ex. 4.5: `ℱ_t` contains the date-`t` innovations. -/
theorem comap_le_shockFiltration (t : ℕ) :
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω t) inferInstance ≤ shockFiltration t :=
  le_iSup₂ (f := fun j (_ : j ≤ t) =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω j) inferInstance) t le_rfl

/-- Galí (2015), Ex. 4.5: the coordinate process is a `ShockPair` on the concrete space. -/
noncomputable def concreteShocks (va : ℝ≥0) : ShockPair (shockMeasure va) shockFiltration where
  Z := fun t ω => ω t
  va := va
  adapted := fun t => (comap_measurable _).mono (comap_le_shockFiltration t) le_rfl
  hasLaw := fun t => (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va) t).hasLaw
  indep := fun t => coord_indep va t

/-- Galí (2015), Ex. 4.5(c), p. 124 (**non-vacuity**): on the concrete space the exact
flexible-price equilibrium exists whenever `β e^{σ_m²/2} < 1 + γ_m`. -/
theorem exists_flex_equilibrium (va : ℝ≥0) {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ C N Y P W Q, IsFlexEquilibrium (shockMeasure va) shockFiltration β φ ε
      (level A₀ γa (techShock (concreteShocks va)))
      (level M₀ γm (moneyShock φa φv (concreteShocks va))) C N Y P W Q :=
  ⟨_, _, _, _, _, _, flex_candidate (concreteShocks va) hφ hε hA hγa hM hγm hQ⟩

/-- Galí (2015), Ex. 4.5(e), p. 124 (**non-vacuity**): on the concrete space the exact
equilibrium with prices set in advance exists whenever `β e^{σ_m²/2} < 1 + γ_m`. -/
theorem exists_sticky_equilibrium (va : ℝ≥0) {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ C N Y P W Q, IsStickyEquilibrium (shockMeasure va) shockFiltration β φ ε
      (level A₀ γa (techShock (concreteShocks va)))
      (level M₀ γm (moneyShock φa φv (concreteShocks va))) C N Y P W Q :=
  ⟨_, _, _, _, _, _, sticky_candidate (concreteShocks va) hφ hε hA hγa hM hγm hQ⟩

/-! ### (f) Expected lifetime utility as the expectation of the infinite sum -/

/-- Galí (2015), Ex. 4.5(f): `log N_{t+1} = log N − (1+φ) s²/2 + (ε^m_{t+1} − ε^a_{t+1})`
almost surely in a sticky-price equilibrium with constant velocity. -/
theorem sticky_logN_succ [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) :
    (fun ω => Real.log (N (t + 1) ω)) =ᵐ[μ] fun ω =>
      (Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2) +
        ((φa - 1) * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) := by
  filter_upwards [sticky_employment S hφ hε hA hγa hM hγm h hV t] with ω hω
  rw [hω, Real.log_mul (Nflex_pos hε).ne' (Real.exp_pos _).ne', Real.log_exp]
  simp only [gapShock]; ring

/-- Galí (2015), Ex. 4.5(f): `E|a ε^a_t + b ν_t| = ∫ |a x + b y| dN(0, σ_a²) ⊗ N(0, 1)`, the
same at every date. -/
theorem integral_abs_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, |a * (S.Z t ω).1 + b * (S.Z t ω).2| ∂μ = ∫ q, |a * q.1 + b * q.2| ∂(pairLaw S.va) :=
  (S.hasLaw t).integral_comp (f := fun q : ℝ × ℝ => |a * q.1 + b * q.2|)
    (by fun_prop : Continuous fun q : ℝ × ℝ => |a * q.1 + b * q.2|).aestronglyMeasurable

/-- Galí (2015), Ex. 4.5(f): the bound
`|log A_t| ≤ |log A₀| + t |log(1 + γ_a)| + |ε^a_1| + ⋯ + |ε^a_t|`. -/
theorem abs_log_tech_le (S : ShockPair μ ℱ) {A₀ γa : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa)
    (t : ℕ) (ω : Ω) : |Real.log (level A₀ γa (techShock S) t ω)| ≤
      |Real.log A₀| + t * |Real.log (1 + γa)| +
        ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| := by
  rw [log_level_eq hA hγa]
  have h1 := Finset.abs_sum_le_sum_abs (fun s => techShock S (s + 1) ω) (Finset.range t)
  have h2 : |(t : ℝ) * Real.log (1 + γa)| = t * |Real.log (1 + γa)| := by
    rw [abs_mul, Nat.abs_cast]
  have h3 := abs_add_le (Real.log A₀ + t * Real.log (1 + γa))
    (∑ s ∈ Finset.range t, techShock S (s + 1) ω)
  have h4 := abs_add_le (Real.log A₀) (t * Real.log (1 + γa))
  simp only [techShock, one_mul, zero_mul, add_zero] at h1 h3 ⊢
  linarith

/-- **Ex. 4.5(f)** (Galí 2015, p. 124, expected lifetime utility): in a sticky-price
equilibrium with constant velocity, `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t] = stickyWelfare`. The
interchange is justified by the bound `E|βᵗ U_t| ≤ βᵗ (K₀ + K₁ t)`. -/
theorem integral_tsum_sticky_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    ∫ ω, ∑' t : ℕ, β ^ t * utility φ (C t ω)
        (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ =
      stickyWelfare β φ ε A₀ γa V (varX S.va φa φv) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hVpos : 0 < V := by
    obtain ⟨ω₀, -⟩ := (h.euler 0).exists
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (hMp 0 ω₀)
  have h1φ : 0 < 1 + φ := by linarith
  set m₁ := ∫ q, |1 * q.1 + 0 * q.2| ∂(pairLaw S.va) with hm₁
  set m₂ := ∫ q, |(φa - 1) * q.1 + φv * q.2| ∂(pairLaw S.va) with hm₂
  have hm₁0 : 0 ≤ m₁ := integral_nonneg fun q => abs_nonneg _
  have hm₂0 : 0 ≤ m₂ := integral_nonneg fun q => abs_nonneg _
  set L := |Real.log (Nflex φ ε)| + (1 + φ) * varX S.va φa φv / 2 + m₂ with hL
  have hs0 : 0 ≤ (1 + φ) * varX S.va φa φv / 2 := by
    have := varX_nonneg S.va.2 φa φv; positivity
  -- integrability and the bound for `log N_t`
  have hlogN : ∀ t, Integrable (fun ω => Real.log (N t ω)) μ ∧
      ∫ ω, |Real.log (N t ω)| ∂μ ≤ L := by
    intro t
    cases t with
    | zero =>
      have hc : (fun ω => Real.log (N 0 ω)) = fun _ => Real.log (Nflex φ ε) := by
        funext ω; rw [sticky_employment_zero S hφ hA hγa hM hγm h hV ω]
      refine ⟨by rw [hc]; exact integrable_const _, ?_⟩
      rw [show (fun ω => |Real.log (N 0 ω)|) = fun _ => |Real.log (Nflex φ ε)| by
        funext ω; rw [congrFun hc ω], integral_const, probReal_univ, one_smul, hL]
      linarith
    | succ t =>
      have hae := sticky_logN_succ S hφ hε hA hγa hM hγm h hV t
      have hint : Integrable (fun ω => Real.log (N (t + 1) ω)) μ :=
        ((integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1))).congr hae.symm
      refine ⟨hint, ?_⟩
      have hbd : ∀ᵐ ω ∂μ, |Real.log (N (t + 1) ω)| ≤ (|Real.log (Nflex φ ε)| +
          (1 + φ) * varX S.va φa φv / 2) + |(φa - 1) * (S.Z (t + 1) ω).1 +
            φv * (S.Z (t + 1) ω).2| := by
        filter_upwards [hae] with ω hω
        rw [hω]
        refine (abs_add_le _ _).trans ?_
        have := abs_sub (Real.log (Nflex φ ε)) ((1 + φ) * varX S.va φa φv / 2)
        rw [abs_of_nonneg hs0] at this
        linarith
      have hmaj : Integrable (fun ω => (|Real.log (Nflex φ ε)| +
          (1 + φ) * varX S.va φa φv / 2) + |(φa - 1) * (S.Z (t + 1) ω).1 +
            φv * (S.Z (t + 1) ω).2|) μ :=
        (integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1)).abs
      refine (integral_mono_ae hint.abs hmaj hbd).trans (le_of_eq ?_)
      rw [integral_add (integrable_const _) (integrable_lin S (φa - 1) φv (t + 1)).abs,
        integral_const, probReal_univ, one_smul, integral_abs_lin, ← hm₂, hL]
  -- `E N_t^{1+φ} = 𝓜⁻¹`
  have hpowE : ∀ t, ∫ ω, N t ω ^ (1 + φ) ∂μ = (markup ε)⁻¹ := by
    intro t
    cases t with
    | zero => exact h.pricing0
    | succ t =>
      rw [← integral_condExp (ℱ.le t), integral_congr_ae (h.pricing t), integral_const,
        probReal_univ, one_smul]
  set U : ℕ → Ω → ℝ := fun t ω => utility φ (C t ω)
    (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) with hU
  have hUeq : ∀ t ω, U t ω = 2 * Real.log (level A₀ γa (techShock S) t ω) +
      2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ) := fun t ω =>
    sticky_period_utility h hAp hMp hV hVpos t ω
  have hint : ∀ t : ℕ, Integrable (fun ω => β ^ t * U t ω) μ := by
    intro t
    have : (fun ω => β ^ t * U t ω) = fun ω => β ^ t * (2 * Real.log (level A₀ γa (techShock S)
        t ω) + 2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ)) := by
      funext ω; rw [hUeq]
    rw [this]
    exact (((((integrable_log_tech S hA hγa t).const_mul 2).add ((hlogN t).1.const_mul 2)).sub
      (integrable_const _)).sub ((h.integrable_hours t).div_const _)).const_mul _
  set K₀ := 2 * |Real.log A₀| + 2 * L + |Real.log V| + (markup ε)⁻¹ / (1 + φ) with hK₀
  set K₁ := 2 * |Real.log (1 + γa)| + 2 * m₁ with hK₁
  set g : ℕ → ℝ := fun t => β ^ t * (K₀ + K₁ * t) with hg
  have hgs : Summable g := (hasSum_affine (K := K₀) (c := K₁) hβ0 hβ1).summable
  have hbound : ∀ t : ℕ, ∫ ω, ‖β ^ t * U t ω‖ ∂μ ≤ g t := by
    intro t
    have hpt : ∀ ω, ‖β ^ t * U t ω‖ ≤ β ^ t * ((2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| +
        2 * ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| +
        2 * |Real.log (N t ω)| + N t ω ^ (1 + φ) / (1 + φ)) := by
      intro ω
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0, hUeq]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
      have h1 := abs_log_tech_le S hA hγa t ω
      have h2 : 0 ≤ N t ω ^ (1 + φ) / (1 + φ) :=
        div_nonneg (Real.rpow_nonneg (h.pos_N t ω).le _) h1φ.le
      have h3 := abs_sub (2 * Real.log (level A₀ γa (techShock S) t ω) +
        2 * Real.log (N t ω) - Real.log V) (N t ω ^ (1 + φ) / (1 + φ))
      have h4 := abs_sub (2 * Real.log (level A₀ γa (techShock S) t ω) +
        2 * Real.log (N t ω)) (Real.log V)
      have h5 := abs_add_le (2 * Real.log (level A₀ γa (techShock S) t ω))
        (2 * Real.log (N t ω))
      rw [abs_of_nonneg h2] at h3
      rw [abs_mul, abs_two] at h5
      rw [abs_mul (2 : ℝ), abs_two] at h5
      linarith
    have hsumint : Integrable (fun ω => ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ :=
      integrable_finsetSum _ fun s _ => (integrable_lin S 1 0 (s + 1)).abs
    have j1 : Integrable (fun _ : Ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)|) μ := integrable_const _
    have j2 : Integrable (fun ω => 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ := hsumint.const_mul 2
    have j3 : Integrable (fun ω => 2 * |Real.log (N t ω)|) μ := (hlogN t).1.abs.const_mul 2
    have j4 : Integrable (fun ω => N t ω ^ (1 + φ) / (1 + φ)) μ :=
      (h.integrable_hours t).div_const _
    have j12 : Integrable (fun ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ := j1.add j2
    have j123 : Integrable (fun ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| + 2 * |Real.log (N t ω)|) μ := j12.add j3
    have hrint : Integrable (fun ω => β ^ t * ((2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| +
        2 * ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| +
        2 * |Real.log (N t ω)| + N t ω ^ (1 + φ) / (1 + φ))) μ :=
      (j123.add j4).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hrint
      (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
    rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_div, hpowE t, integral_finsetSum _ fun s _ =>
      (integrable_lin S 1 0 (s + 1)).abs]
    simp only [integral_abs_lin S 1 0, ← hm₁]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    have := (hlogN t).2
    rw [hK₀, hK₁]
    nlinarith
  have hsum : Summable fun t : ℕ => ∫ ω, ‖β ^ t * U t ω‖ ∂μ :=
    hgs.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _) hbound
  change ∫ ω, ∑' t : ℕ, β ^ t * U t ω ∂μ = _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_const_mul]
  exact (hasSum_sticky_welfare S hφ hε hA hγa hM hγm hβ0 hβ1 h hV).tsum_eq

end Gali.MonetaryPolicyDesign.Ex4_5

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.6: a price-level based interest rate rule

Galí (2015), Chapter 4, Exercise 4.6, p. 125. The economy is the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` and the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`, with `π_t = p̂_t − p̂_{t−1}`. Policy follows the price-level rule
`i_t = r^n_t + φ_p p̂_t`, `p̂_t = p_t − p*`. The book asks to show that the rule generates a
unique stationary equilibrium if and only if `φ_p > 0`.

The lagged price level `p̂_{t−1}` is predetermined (`p̂_{−1}` is given), so the equilibrium is a
system in `(p̂_{t−1}, p̂_t, ỹ_t)` with one predetermined and two jump variables. A bounded
equilibrium exists and is unique for every initial price level iff exactly one root of the
characteristic polynomial (`charPoly`)

  `P(λ) = σ (λ − 1)² (1 − βλ) − κ λ (1 + φ_p − λ)`

lies inside the unit circle (`λ` is the ratio `p̂_t / p̂_{t−1}` of a perfect-foresight mode).

## The factorisation

For a real root `λ` of `P`, put `w_t = p̂_t − λ p̂_{t−1}` and `v_t = ỹ_t − c(λ) p̂_{t−1}` with
`c(λ) = −(1 − λ)(1 − βλ)/κ` (`loadY`). The predetermined variable drops out and `(w, v)` solves
a *homogeneous* two-dimensional forward system `x_t = A(λ) E_t x_{t+1}` (`reduce_solves`), whose
matrix (`fwdA`) has `det A = βλ` (`det2_fwdA`) and
`σ (1 − λ)(1 − tr A + det A) = κ φ_p λ`, `σ (1 + λ)(1 + tr A + det A) = λ P(−1)` (`key_one`,
`key_neg_one`). The natural rate drops out of the system entirely.

## Main results

* `determinate_of_root`: if `P(λ) = 0`, `|λ| < 1` and `A(λ)` is Schur stable, then for every
  initial price level there is exactly one bounded equilibrium, `p̂_t = λ^{t+1} p̂_{−1}`,
  `ỹ_t = c(λ) λᵗ p̂_{−1}`, `i_t = r^n_t + φ_p p̂_t` (`bounded_eq_explicit`).
* `determinate_of_pos`: **`φ_p > 0` ⇒ determinacy** (a root in `(0, 1)`).
* `not_determinate_of_two_roots`, `not_determinate_of_neg`: for
  `φ* ≤ φ_p ≤ 0`, `φ* = −2 − 4σ(1 + β)/κ` (`phiStar`), there are two bounded equilibria with the
  same initial price level (two roots in the closed unit disc; for `φ* < φ_p < 0` the stable
  roots may be complex and the second equilibrium is built from the backward matrix `bwdB`).
* `determinate_of_lt_phiStar` (**correction**): for `φ_p < φ*` the equilibrium is again
  determinate (an oscillating stable root in `(−1, 0)`).
* `determinate_iff`: determinacy `⟺ φ_p > 0 ∨ φ_p < φ*`; `determinate_iff_pos_of_ge`: the book's
  claim holds for `φ_p ≥ φ*`, in particular for all `φ_p ≥ 0`; `book_claim_false`: the printed
  "if and only if `φ_p > 0`" fails over all real `φ_p`.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_6

open Filter Topology

/-! ### The characteristic polynomial and the reduced matrices -/

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

/-- Galí (2015), Ex. 4.6: the backward matrix `B(λ) = A(λ)⁻¹` of the reduced system
(perfect foresight: `(w_{t+1}, v_{t+1}) = B(λ) (w_t, v_t)`). -/
noncomputable def bwdB (σ κ β φ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mCoef β r / β, -κ / β;
    -(mCoef β r + β * eCoef σ κ β φ r) / (β * σ), (κ + β * σ) / (β * σ)]

/-- Galí (2015), Ex. 4.6: the lower determinacy threshold `φ* = −2 − 4σ(1 + β)/κ`, at which
`P(−1) = 0`. -/
noncomputable def phiStar (σ κ β : ℝ) : ℝ := -2 - 4 * σ * (1 + β) / κ

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

/-- Galí (2015), Ex. 4.6: for `κ > 0`, `P(−1) > 0` iff `φ_p > φ*`, and `P(−1) < 0` iff
`φ_p < φ*`. -/
theorem charPoly_neg_one_pos_iff {σ κ β φ : ℝ} (hκ : 0 < κ) :
    0 < charPoly σ κ β φ (-1) ↔ phiStar σ κ β < φ := by
  rw [charPoly_neg_one, phiStar,
    show -2 - 4 * σ * (1 + β) / κ = (-(2 * κ) - 4 * σ * (1 + β)) / κ by field_simp,
    div_lt_iff₀ hκ]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Ex. 4.6: `P(−1) < 0` iff `φ_p < φ*` (for `κ > 0`). -/
theorem charPoly_neg_one_neg_iff {σ κ β φ : ℝ} (hκ : 0 < κ) :
    charPoly σ κ β φ (-1) < 0 ↔ φ < phiStar σ κ β := by
  rw [charPoly_neg_one, phiStar,
    show -2 - 4 * σ * (1 + β) / κ = (-(2 * κ) - 4 * σ * (1 + β)) / κ by field_simp,
    lt_div_iff₀ hκ]
  constructor <;> intro h <;> linarith

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

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the backward recursion
`(w', v') = B(λ) (w, v)` gives the reduced Phillips curve and IS equation. -/
theorem bwd_step {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (x : Fin 2 → ℝ) :
    mCoef β r * x 0 - κ * x 1 = β * (bwdB σ κ β φ r).mulVec x 0 ∧
      σ * x 1 = σ * (bwdB σ κ β φ r).mulVec x 1 + eCoef σ κ β φ r * x 0 +
        (bwdB σ κ β φ r).mulVec x 0 := by
  simp only [bwdB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · field_simp
    ring
  · field_simp
    ring

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

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 4.6: the lagged price level `p̂_{t−1}`, with `p̂_{−1}` given. -/
def lagP (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pm1
  | t + 1 => p t

/-- Galí (2015), Ex. 4.6: inflation `π_t = p̂_t − p̂_{t−1}`. -/
def infl (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - lagP pm1 p t

/-- Galí (2015), Ex. 4.6, p. 125: an equilibrium given the initial price level `p̂_{−1}`: the IS
equation, the Phillips curve and the price-level rule `i_t = r^n_t + φ_p p̂_t`. -/
def IsEquilibrium (β σ κ φ : ℝ) (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl pm1 p (t + 1)) - rn t) ∧
    infl pm1 p t = β • 𝔼.E t (infl pm1 p (t + 1)) + κ • y t ∧
    i t = rn t + φ • p t

/-- Galí (2015), Ex. 4.6: a stationary (bounded, adapted) equilibrium. -/
def BoundedEq (β σ κ φ : ℝ) (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i ∧ 𝔼.Adapted y ∧ 𝔼.Adapted p ∧ BoundedProc y ∧
    BoundedProc p

/-- Galí (2015), Ex. 4.6: the rule generates a unique stationary equilibrium: for every natural
rate and every bounded initial price level known at date 0, a bounded equilibrium exists and any
two coincide. -/
def Determinate (β σ κ φ : ℝ) : Prop :=
  ∀ (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ), 𝔼.E 0 pm1 = pm1 → (∃ M, ∀ ω, |pm1 ω| ≤ M) →
    (∃ y p i, BoundedEq 𝔼 β σ κ φ rn pm1 y p i) ∧
    ∀ y p i y' p' i', BoundedEq 𝔼 β σ κ φ rn pm1 y p i → BoundedEq 𝔼 β σ κ φ rn pm1 y' p' i' →
      y = y' ∧ p = p' ∧ i = i'

/-- Galí (2015), Ex. 4.6: the initial price level is known at every date. -/
theorem known_pm1 {pm1 : Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (t : ℕ) : 𝔼.E t pm1 = pm1 := by
  have := 𝔼.known (Nat.zero_le t) pm1
  rwa [h] at this

/-- Galí (2015), Ex. 4.6: the lagged price level is adapted. -/
theorem lagP_adapted {pm1 : Ω → ℝ} {p : ℕ → Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (hp : 𝔼.Adapted p) :
    𝔼.Adapted (lagP pm1 p) := by
  intro t
  cases t with
  | zero => exact h
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    have := 𝔼.known (Nat.le_succ t) (p t)
    rwa [hp t] at this

/-- Galí (2015), Ex. 4.6: for an adapted price level, the equilibrium conditions hold iff,
pointwise, `σ ỹ_t = σ E_t ỹ_{t+1} − ((φ_p + 1) p̂_t − E_t p̂_{t+1})`,
`(1 + β) p̂_t − p̂_{t−1} = β E_t p̂_{t+1} + κ ỹ_t` and the rule holds. -/
theorem eq_iff_pointwise {β σ κ φ : ℝ} (hσ : σ ≠ 0) {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ}
    {y p i : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i ↔ ∀ t ω,
      σ * y t ω = σ * 𝔼.E t (y (t + 1)) ω - ((φ + 1) * p t ω - 𝔼.E t (p (t + 1)) ω) ∧
      (1 + β) * p t ω - lagP pm1 p t ω = β * 𝔼.E t (p (t + 1)) ω + κ * y t ω ∧
      i t ω = rn t ω + φ * p t ω := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hE : ∀ t, 𝔼.E t (infl pm1 p (t + 1)) = 𝔼.E t (p (t + 1)) - p t := fun t => by
    change 𝔼.E t (p (t + 1) - p t) = _
    rw [map_sub, hp t]
  constructor
  · intro h t ω
    obtain ⟨h1, h2, h3⟩ := h t
    rw [hE] at h1 h2
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    simp only [infl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3
    refine ⟨?_, by linarith, e3⟩
    linear_combination σ * e1 - e3 -
      (i t ω - (𝔼.E t (p (t + 1)) ω - p t ω) - rn t ω) * hinv
  · intro h t
    refine ⟨funext fun ω => ?_, funext fun ω => ?_, funext fun ω => (h t ω).2.2⟩
    · obtain ⟨e1, -, e3⟩ := h t ω
      rw [hE]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination σ⁻¹ * e1 - (y t ω - 𝔼.E t (y (t + 1)) ω) * hinv + σ⁻¹ * e3
    · obtain ⟨-, e2, -⟩ := h t ω
      rw [hE]
      simp only [infl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith

/-- Galí (2015), Ex. 4.6: the transformed variable `w_t = p̂_t − λ p̂_{t−1}`. -/
def wseq (r : ℝ) (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - r • lagP pm1 p t

/-- Galí (2015), Ex. 4.6: the transformed variable `v_t = ỹ_t − c(λ) p̂_{t−1}`. -/
noncomputable def vseq (κ β r : ℝ) (pm1 : Ω → ℝ) (p y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  y t - loadY κ β r • lagP pm1 p t

/-- Galí (2015), Ex. 4.6: the stacked vector `(w_t, v_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- **The factorisation** (Galí 2015, Ex. 4.6): at a root `λ` of `P`, in every equilibrium with
an adapted price level, `(w, v)` solves the homogeneous forward system
`(w_t, v_t) = A(λ) E_t (w_{t+1}, v_{t+1})`; the predetermined price level and the natural rate
drop out. -/
theorem reduce_solves {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0)
    {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ} {y p i : ℕ → Ω → ℝ}
    (he : IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i) (hp : 𝔼.Adapted p) :
    𝔼.Solves (fwdA σ κ β φ r) 0 (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
  have hpt := (eq_iff_pointwise 𝔼 hσ hp).1 he
  intro t j
  funext ω
  obtain ⟨e1, e2, -⟩ := hpt t ω
  have h1 := (pc_iff (r := r) hκ _ _ _ _).1 e2
  have h2 := (is_iff (k := lagP pm1 p t ω) hκ hP _ _ _ _).1 e1
  have hfw := fwd_of hσ hκ hP h1 h2
  have hEw : 𝔼.E t (wseq r pm1 p (t + 1)) ω = 𝔼.E t (p (t + 1)) ω - r * p t ω := by
    change 𝔼.E t (p (t + 1) - r • p t) ω = _
    rw [map_sub, map_smul, hp t]; rfl
  have hEv : 𝔼.E t (vseq κ β r pm1 p y (t + 1)) ω =
      𝔼.E t (y (t + 1)) ω - loadY κ β r * p t ω := by
    change 𝔼.E t (y (t + 1) - loadY κ β r • p t) ω = _
    rw [map_sub, map_smul, hp t]; rfl
  fin_cases j
  · simp only [stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [hEw, hEv]
    simp only [fwdA, wseq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hfw.1
  · simp only [stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.zero_apply, add_zero]
    rw [hEw, hEv]
    simp only [fwdA, vseq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hfw.2

/-! ### Determinacy -/

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, the `λ`-mode `p̂_t = λ^{t+1} p̂_{−1}`,
`ỹ_t = c(λ) λᵗ p̂_{−1}`, `i_t = r^n_t + φ_p p̂_t` is an equilibrium for every initial price level
known at date 0. -/
theorem mode_isEquilibrium {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (rn : ℕ → Ω → ℝ) {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1) :
    IsEquilibrium 𝔼 β σ κ φ rn pm1 (fun t => (loadY κ β r * r ^ t) • pm1)
      (fun t => r ^ (t + 1) • pm1) (fun t => rn t + φ • (r ^ (t + 1) • pm1)) := by
  have hpa : 𝔼.Adapted (fun t => r ^ (t + 1) • pm1) := fun t => by
    simp only [map_smul, known_pm1 𝔼 hpm t]
  have hlag : ∀ t, lagP pm1 (fun t => r ^ (t + 1) • pm1) t = r ^ t • pm1 := fun t => by
    cases t with
    | zero => simp [lagP]
    | succ t => rfl
  refine (eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_
  simp only [map_smul, known_pm1 𝔼 hpm t, hlag t, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  refine ⟨(is_iff (k := r ^ t * pm1 ω) hκ hP _ _ _ _).2 (by ring),
    (pc_iff (r := r) hκ _ _ _ _).2 (by ring), trivial⟩

/-- Galí (2015), Ex. 4.6: if `P(λ) = 0` and `A(λ)` is Schur stable, every stationary equilibrium
is the `λ`-mode: `p̂_t = λ^{t+1} p̂_{−1}` and `ỹ_t = c(λ) λᵗ p̂_{−1}`. -/
theorem bounded_eq_explicit {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (hA : SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r)))
    {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1) (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M)
    {y p i : ℕ → Ω → ℝ} (he : BoundedEq 𝔼 β σ κ φ rn pm1 y p i) :
    p = (fun t => r ^ (t + 1) • pm1) ∧ y = (fun t => (loadY κ β r * r ^ t) • pm1) := by
  obtain ⟨he, hya, hpa, ⟨My, hMy⟩, ⟨Mp, hMp⟩⟩ := he
  obtain ⟨M0, hM0⟩ := hpmb
  have hs := reduce_solves 𝔼 hσ hκ hP he hpa
  have hlb : ∀ t ω, |lagP pm1 p t ω| ≤ M0 + Mp := by
    intro t ω
    cases t with
    | zero =>
      change |pm1 ω| ≤ _
      have := abs_nonneg (p 0 ω); linarith [hM0 ω, hMp 0 ω]
    | succ t =>
      change |p t ω| ≤ _
      have := abs_nonneg (pm1 ω); linarith [hM0 ω, hMp t ω]
  have hla := lagP_adapted 𝔼 hpm hpa
  have hav : 𝔼.AdaptedVec (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
    intro t j
    fin_cases j
    · change 𝔼.E t (p t - r • lagP pm1 p t) = p t - r • lagP pm1 p t
      rw [map_sub, map_smul, hpa t, hla t]
    · change 𝔼.E t (y t - loadY κ β r • lagP pm1 p t) = y t - loadY κ β r • lagP pm1 p t
      rw [map_sub, map_smul, hya t, hla t]
  have hbv : BoundedVec (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
    refine ⟨Mp + |r| * (M0 + Mp) + My + |loadY κ β r| * (M0 + Mp), fun t j ω => ?_⟩
    have h1 := abs_nonneg (p t ω)
    have h2 := abs_nonneg (y t ω)
    have h3 : |r * lagP pm1 p t ω| ≤ |r| * (M0 + Mp) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hlb t ω) (abs_nonneg r)
    have h4 : |loadY κ β r * lagP pm1 p t ω| ≤ |loadY κ β r| * (M0 + Mp) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hlb t ω) (abs_nonneg _)
    have h5 := abs_nonneg (r * lagP pm1 p t ω)
    have h6 := abs_nonneg (loadY κ β r * lagP pm1 p t ω)
    fin_cases j
    · change |p t ω - r * lagP pm1 p t ω| ≤ _
      linarith [abs_sub (p t ω) (r * lagP pm1 p t ω), hMp t ω, hMy t ω]
    · change |y t ω - loadY κ β r * lagP pm1 p t ω| ≤ _
      linarith [abs_sub (y t ω) (loadY κ β r * lagP pm1 p t ω), hMp t ω, hMy t ω]
  have h0 : 𝔼.Solves (fwdA σ κ β φ r) 0 0 := fun t j => by simp
  have heq := 𝔼.system_unique hA hs h0 hav (fun t j => map_zero _) hbv
    ⟨0, fun t j ω => by simp⟩
  have hw : ∀ t, p t = r • lagP pm1 p t := fun t => by
    have := congrFun (congrFun heq t) 0
    simp only [stack, Matrix.cons_val_zero, wseq] at this
    exact sub_eq_zero.1 this
  have hv : ∀ t, y t = loadY κ β r • lagP pm1 p t := fun t => by
    have := congrFun (congrFun heq t) 1
    simp only [stack, Matrix.cons_val_one, Matrix.cons_val_fin_one, vseq] at this
    exact sub_eq_zero.1 this
  have hpexp : ∀ t, p t = r ^ (t + 1) • pm1 := by
    intro t
    induction t with
    | zero => rw [hw 0]; simp [lagP]
    | succ t ih =>
      rw [hw (t + 1)]
      change r • p t = _
      rw [ih, smul_smul]
      congr 1
      ring
  refine ⟨funext hpexp, funext fun t => ?_⟩
  rw [hv t]
  cases t with
  | zero => simp [lagP]
  | succ t =>
    change loadY κ β r • p t = _
    rw [hpexp t, smul_smul]

/-- Galí (2015), Ex. 4.6: if `P(λ) = 0`, `|λ| < 1` and `A(λ)` is Schur stable, the rule
generates a unique stationary equilibrium for every initial price level. -/
theorem determinate_of_root {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (hr : |r| < 1)
    (hA : SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r))) :
    Determinate 𝔼 β σ κ φ := by
  intro rn pm1 hpm hpmb
  refine ⟨⟨_, _, _, mode_isEquilibrium 𝔼 hσ hκ hP rn hpm, fun t => ?_, fun t => ?_, ?_, ?_⟩, ?_⟩
  · simp only [map_smul, known_pm1 𝔼 hpm t]
  · simp only [map_smul, known_pm1 𝔼 hpm t]
  · obtain ⟨M, hM⟩ := hpmb
    refine ⟨|loadY κ β r| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
    have h2 := abs_nonneg (pm1 ω)
    have h3 := mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg (loadY κ β r))
    calc |loadY κ β r| * |r| ^ t * |pm1 ω| ≤ |loadY κ β r| * 1 * |pm1 ω| := by gcongr
      _ ≤ |loadY κ β r| * M := by rw [mul_one]; exact h3
  · obtain ⟨M, hM⟩ := hpmb
    refine ⟨M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have h1 : |r| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
    have h2 := abs_nonneg (pm1 ω)
    nlinarith [hM ω]
  · intro y p i y' p' i' he he'
    obtain ⟨hp1, hy1⟩ := bounded_eq_explicit 𝔼 hσ hκ hP hA hpm hpmb he
    obtain ⟨hp2, hy2⟩ := bounded_eq_explicit 𝔼 hσ hκ hP hA hpm hpmb he'
    refine ⟨hy1.trans hy2.symm, hp1.trans hp2.symm, funext fun t => ?_⟩
    rw [(he.1 t).2.2, (he'.1 t).2.2, hp1, hp2]

/-! ### Roots of the characteristic polynomial -/

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

/-- Galí (2015), Ex. 4.6: for `φ_p < φ*` the polynomial has a root in `(−1, 0)`
(`P(−1) < 0 < σ = P(0)`). -/
theorem exists_root_neg {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : φ < phiStar σ κ β) :
    ∃ r, -1 < r ∧ r < 0 ∧ charPoly σ κ β φ r = 0 := by
  have h := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ (-1)) (charPoly σ κ β φ 0) by
      rw [charPoly_zero]; exact ⟨(charPoly_neg_one_neg_iff hκ).2 hφ, hσ⟩)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), Ex. 4.6: for `φ_p < 1/β − 1` (in particular `φ_p ≤ 0`) the polynomial has a
root `λ > 1/β` (`P(1/β) > 0` and `P(λ) → −∞`). -/
theorem exists_root_large {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : φ ≤ 0) : ∃ r, 1 / β < r ∧ charPoly σ κ β φ r = 0 := by
  set a := σ + 2 * σ * β + κ with ha
  set b := 2 * σ + σ * β + κ * (1 + φ) with hb
  set K := a + |b| + σ with hK
  have hKpos : 0 < K := by have := abs_nonneg b; rw [hK, ha]; positivity
  set X := K / (σ * β) + 1 / β + 1 with hX
  have hσβ : 0 < σ * β := mul_pos hσ hβ0
  have hX1 : 1 / β < X := by rw [hX]; have := div_pos hKpos hσβ; linarith
  have hb1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hXge : 1 ≤ X := by linarith
  have hXeq : σ * β * X = K + σ + σ * β := by rw [hX]; field_simp
  have hexp : charPoly σ κ β φ X = -(σ * β * X) * X ^ 2 + a * X ^ 2 - b * X + σ := by
    rw [ha, hb]; unfold charPoly; ring
  have hPX : charPoly σ κ β φ X < 0 := by
    rw [hexp, hXeq]
    have h1 : -b * X ≤ |b| * X ^ 2 := by
      have := neg_abs_le b
      have hX2 : X ≤ X ^ 2 := by nlinarith
      nlinarith [abs_nonneg b]
    have h2 : σ ≤ σ * X ^ 2 := by nlinarith
    have h3 : 0 < X ^ 2 := by positivity
    nlinarith
  have hP1 : 0 < charPoly σ κ β φ (1 / β) := by
    unfold charPoly
    have : 1 - β * (1 / β) = 0 := by field_simp; ring
    rw [this, mul_zero, zero_sub, neg_pos]
    have h1 : 1 + φ - 1 / β < 0 := by linarith
    have h2 : 0 < κ * (1 / β) := by positivity
    nlinarith
  have h := intermediate_value_Ioo' hX1.le (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ X) (charPoly σ κ β φ (1 / β)) from ⟨hPX, hP1⟩)
  obtain ⟨r, ⟨h0, -⟩, hr⟩ := h
  exact ⟨r, h0, hr⟩

/-! ### The determinacy region -/

/-- **Ex. 4.6, sufficiency** (Galí 2015, p. 125): for `φ_p > 0` the price-level rule generates a
unique stationary equilibrium for every initial price level. -/
theorem determinate_of_pos {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 0 < φ) : Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_pos (β := β) hσ hκ hφ
  have hP1 : 0 < charPoly σ κ β φ (-1) := by rw [charPoly_neg_one]; positivity
  exact determinate_of_root 𝔼 hσ.ne' hκ.ne' hP (abs_lt.2 ⟨by linarith, hr1⟩)
    (schur_fwdA hσ hκ hβ0 hβ1 hP (abs_lt.2 ⟨by linarith, hr1⟩) (mul_pos hφ hr0)
      (mul_pos hr0 hP1))

/-- **Ex. 4.6, correction** (Galí 2015, p. 125): for `φ_p < φ* = −2 − 4σ(1 + β)/κ` the rule
*also* generates a unique stationary equilibrium (the stable root lies in `(−1, 0)`). -/
theorem determinate_of_lt_phiStar {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : φ < phiStar σ κ β) : Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_neg (β := β) hσ hκ hφ
  have hP1 := (charPoly_neg_one_neg_iff hκ).2 hφ
  have hφneg : φ < 0 := by
    have : phiStar σ κ β < 0 := by
      unfold phiStar
      have : 0 < 4 * σ * (1 + β) / κ := by positivity
      linarith
    linarith
  exact determinate_of_root 𝔼 hσ.ne' hκ.ne' hP (abs_lt.2 ⟨hr0, by linarith⟩)
    (schur_fwdA hσ hκ hβ0 hβ1 hP (abs_lt.2 ⟨hr0, by linarith⟩) (mul_pos_of_neg_of_neg hφneg hr1)
      (mul_pos_of_neg_of_neg hr1 hP1))

/-- Galí (2015), Ex. 4.6: the zero outcome (`ỹ = p̂ = 0`, `i = r^n`) is a stationary equilibrium
when `p̂_{−1} = 0`. -/
theorem zero_boundedEq {β σ κ φ : ℝ} (hσ : σ ≠ 0) (rn : ℕ → Ω → ℝ) :
    BoundedEq 𝔼 β σ κ φ rn (fun _ => 0) (fun _ => 0) (fun _ => 0) rn := by
  have hpa : 𝔼.Adapted (fun _ => (0 : Ω → ℝ)) := fun t => map_zero _
  refine ⟨(eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_, hpa, hpa, ⟨0, fun t ω => by simp⟩,
    ⟨0, fun t ω => by simp⟩⟩
  cases t <;> simp [lagP]

/-- Galí (2015), Ex. 4.6 (**multiplicity**): if `P` has two distinct real roots `λ, μ` in the
closed unit disc, the rule does not generate a unique stationary equilibrium: with
`p̂_{−1} = 0`, both `0` and the deterministic path `p̂_t = λ^{t+1} − μ^{t+1}` are stationary
equilibria. -/
theorem not_determinate_of_two_roots [Nonempty Ω] {β σ κ φ r s : ℝ} (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hPr : charPoly σ κ β φ r = 0) (hPs : charPoly σ κ β φ s = 0) (hrs : r ≠ s)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) : ¬ Determinate 𝔼 β σ κ φ := by
  intro hD
  obtain ⟨-, huniq⟩ := hD (fun _ => 0) (fun _ => 0) (map_zero _) ⟨0, fun _ => by simp⟩
  set p : ℕ → Ω → ℝ := fun t _ => r ^ (t + 1) - s ^ (t + 1) with hp
  set y : ℕ → Ω → ℝ := fun t _ => loadY κ β r * r ^ t - loadY κ β s * s ^ t with hy
  have hpa : 𝔼.Adapted p := fun t => 𝔼.const t _
  have hya : 𝔼.Adapted y := fun t => 𝔼.const t _
  have hlag : ∀ t ω, lagP (fun _ => 0) p t ω = r ^ t - s ^ t := by
    intro t ω
    cases t with
    | zero => simp [lagP]
    | succ t => rfl
  have he : IsEquilibrium 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine (eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_
    rw [hlag t ω, hp, hy, 𝔼.const, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
    have i1 := (is_iff (k := r ^ t) hκ hPr (r ^ (t + 1)) (loadY κ β r * r ^ t) (r ^ (t + 2))
      (loadY κ β r * r ^ (t + 1))).2 (by ring)
    have i2 := (is_iff (k := s ^ t) hκ hPs (s ^ (t + 1)) (loadY κ β s * s ^ t) (s ^ (t + 2))
      (loadY κ β s * s ^ (t + 1))).2 (by ring)
    have p1 := (pc_iff (r := r) (β := β) hκ (r ^ t) (r ^ (t + 1)) (loadY κ β r * r ^ t)
      (r ^ (t + 2))).2 (by ring)
    have p2 := (pc_iff (r := s) (β := β) hκ (s ^ t) (s ^ (t + 1)) (loadY κ β s * s ^ t)
      (s ^ (t + 2))).2 (by ring)
    refine ⟨by linear_combination i1 - i2, by linear_combination p1 - p2, by simp⟩
  have hb : BoundedEq 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine ⟨he, hya, hpa, ⟨|loadY κ β r| + |loadY κ β s|, fun t ω => ?_⟩,
      ⟨2, fun t ω => ?_⟩⟩
    · have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
      have h2 : |s| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      calc |loadY κ β r * r ^ t - loadY κ β s * s ^ t|
          ≤ |loadY κ β r * r ^ t| + |loadY κ β s * s ^ t| := abs_sub _ _
        _ = |loadY κ β r| * |r| ^ t + |loadY κ β s| * |s| ^ t := by rw [abs_mul, abs_mul,
            abs_pow, abs_pow]
        _ ≤ |loadY κ β r| * 1 + |loadY κ β s| * 1 := by gcongr
        _ = _ := by ring
    · have h1 : |r| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
      have h2 : |s| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      calc |r ^ (t + 1) - s ^ (t + 1)| ≤ |r ^ (t + 1)| + |s ^ (t + 1)| := abs_sub _ _
        _ ≤ 2 := by rw [abs_pow, abs_pow]; linarith
  obtain ⟨-, hp0, -⟩ := huniq _ _ _ _ _ _ hb (zero_boundedEq 𝔼 hσ _)
  have := congrFun (congrFun hp0 0) (Classical.arbitrary Ω)
  simp only [hp, zero_add, pow_one] at this
  exact hrs (sub_eq_zero.1 this)

/-- Galí (2015), Ex. 4.6: for `φ_p = 0` the rule does not pin down a unique stationary
equilibrium (roots `1` and a root in `(0, 1)`). -/
theorem not_determinate_zero [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ Determinate 𝔼 β σ κ 0 := by
  set g : ℝ → ℝ := fun x => σ * (x - 1) * (1 - β * x) + κ * x with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  obtain ⟨r, ⟨hr0, hr1⟩, hgr⟩ := intermediate_value_Ioo (zero_le_one' ℝ) hgc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g 0) (g 1) by simp only [hg]; constructor <;> nlinarith)
  have hPr : charPoly σ κ β 0 r = 0 := by
    have : charPoly σ κ β 0 r = (r - 1) * g r := by simp only [hg]; unfold charPoly; ring
    rw [this, hgr, mul_zero]
  have hP1 : charPoly σ κ β 0 1 = 0 := by rw [charPoly_one]; ring
  exact not_determinate_of_two_roots 𝔼 hσ.ne' hκ.ne' hPr hP1 hr1.ne
    (by rw [abs_of_pos hr0]; exact hr1.le) (by norm_num)

/-- Galí (2015), Ex. 4.6: at `φ_p = φ*` the rule does not pin down a unique stationary
equilibrium (roots `−1` and a root in `(−1, 0)`). -/
theorem not_determinate_phiStar [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) : ¬ Determinate 𝔼 β σ κ (phiStar σ κ β) := by
  set g : ℝ → ℝ := fun x => -(σ * β) * x ^ 2 + (σ + 3 * σ * β + κ) * x + σ with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  obtain ⟨r, ⟨hr0, hr1⟩, hgr⟩ := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    hgc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g (-1)) (g 0) by simp only [hg]; constructor <;> nlinarith)
  have hfac : ∀ x, charPoly σ κ β (phiStar σ κ β) x = (x + 1) * g x := by
    intro x; simp only [hg]; unfold charPoly phiStar; field_simp; ring
  have hPr : charPoly σ κ β (phiStar σ κ β) r = 0 := by rw [hfac, hgr, mul_zero]
  have hP1 : charPoly σ κ β (phiStar σ κ β) (-1) = 0 := by rw [hfac]; ring
  exact not_determinate_of_two_roots 𝔼 hσ.ne' hκ.ne' hPr hP1 (by linarith)
    (abs_le.2 ⟨by linarith, by linarith⟩) (by norm_num)

/-! ### The region `φ* < φ_p < 0`: complex stable roots -/

/-- Galí (2015), Ex. 4.6: the determinant of the backward matrix, `det B(λ) = (σ(1 + β − βλ) −
κ e(λ))/(βσ)`. -/
theorem det2_bwdB {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    det2 (bwdB σ κ β φ r) = (σ * mCoef β r - κ * eCoef σ κ β φ r) / (β * σ) := by
  simp only [det2, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: the trace of the backward matrix. -/
theorem tr2_bwdB (σ κ β φ r : ℝ) :
    tr2 (bwdB σ κ β φ r) = mCoef β r / β + (κ + β * σ) / (β * σ) := by
  simp only [tr2, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Galí (2015), Ex. 4.6: `βσ (1 − tr B + det B) = −κ (1 + e(λ))`. -/
theorem bwdB_one (σ κ β φ r : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    β * σ * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      -(κ * (1 + eCoef σ κ β φ r)) := by
  rw [det2_bwdB hσ hβ, tr2_bwdB]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: `βσ (1 + tr B + det B) = 2βσ + 2σ(1 + β − βλ) + κ − κ e(λ)`. -/
theorem bwdB_neg_one (σ κ β φ r : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    β * σ * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      2 * β * σ + 2 * σ * mCoef β r + κ - κ * eCoef σ κ β φ r := by
  rw [det2_bwdB hσ hβ, tr2_bwdB]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`,
`βσ (1 − λ)(1 − tr B + det B) = κ φ_p`. -/
theorem keyB_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) :
    β * σ * (1 - r) * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) = κ * φ := by
  have h := loadY_mul hκ β r
  rw [show β * σ * (1 - r) * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
    (1 - r) * (β * σ * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r))) by ring,
    bwdB_one σ κ β φ r hσ hβ]
  unfold eCoef
  unfold charPoly at hP
  linear_combination (-(σ * (1 - r))) * h + hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`,
`βσ (1 + λ)(1 + tr B + det B) = P(−1)`. -/
theorem keyB_neg_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) :
    β * σ * (1 + r) * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      charPoly σ κ β φ (-1) := by
  have h := loadY_mul hκ β r
  rw [show β * σ * (1 + r) * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
    (1 + r) * (β * σ * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r))) by ring,
    bwdB_neg_one σ κ β φ r hσ hβ]
  unfold eCoef mCoef
  unfold charPoly at hP ⊢
  linear_combination (-(σ * (1 + r))) * h - hP

/-- Galí (2015), Ex. 4.6: a real sequence tending to zero is bounded. -/
theorem bounded_of_tendsto_zero {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    ∃ M, ∀ t, |u t| ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨M, fun t => by simpa [Real.norm_eq_abs] using hM (u t) ⟨t, rfl⟩⟩

/-- Galí (2015), Ex. 4.6 (**multiplicity for `φ* < φ_p < 0`**): the polynomial has a root
`λ > 1/β`, the backward matrix `B(λ)` (whose eigenvalues are the two other roots, possibly
complex) is Schur stable, and its decaying solutions give a second stationary equilibrium with
`p̂_{−1} = 0` next to the zero one. -/
theorem not_determinate_of_neg [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : φ < 0) (hφs : phiStar σ κ β < φ) :
    ¬ Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr, hP⟩ := exists_root_large (β := β) hσ hκ hβ0 hβ1 hφ.le
  have hb1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hr1 : 1 < r := hb1.trans hr
  have hβr : 1 < β * r := by rw [div_lt_iff₀ hβ0] at hr; linarith
  set B := bwdB σ κ β φ r with hBdef
  -- Schur stability of `B`
  have hΔ := delta_eq hκ.ne' hP
  have hD : det2 B = 1 / (β * r) := by
    have hr0 : r ≠ 0 := by linarith
    have hm : σ * mCoef β r - κ * eCoef σ κ β φ r = σ / r := by
      rw [eq_div_iff hr0]; linarith
    rw [hBdef, det2_bwdB hσ.ne' hβ0.ne', hm]
    field_simp
  have hD0 : 0 < det2 B := by rw [hD]; exact div_pos one_pos (by linarith)
  have hD1 : det2 B < 1 := by rw [hD, div_lt_one (by linarith)]; exact hβr
  have k1 := keyB_one hσ.ne' hβ0.ne' hκ.ne' hP
  have k2 := keyB_neg_one hσ.ne' hβ0.ne' hκ.ne' hP
  rw [← hBdef] at k1 k2
  have hP1 := (charPoly_neg_one_pos_iff hκ).2 hφs
  have e1 : 0 < 1 - tr2 B + det2 B := by
    have hneg : β * σ * (1 - r) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have : β * σ * (1 - r) * (1 - tr2 B + det2 B) < 0 := by rw [k1]; nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  have e2 : 0 < 1 + tr2 B + det2 B := by
    have hpos : 0 < β * σ * (1 + r) := by positivity
    have : 0 < β * σ * (1 + r) * (1 + tr2 B + det2 B) := by rw [k2]; exact hP1
    exact pos_of_mul_pos_right this hpos.le
  have hB : SchurStable (tr2 B) (det2 B) :=
    ⟨by rw [abs_of_pos hD0]; exact hD1, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  -- the construction
  set dd := r ^ 2 - tr2 B * r + det2 B with hdd
  have hdd0 : 0 < dd := by rw [hdd]; nlinarith
  set s0 : Fin 2 → ℝ := ![B 0 1, B 1 1 - r] with hs0
  set sseq : ℕ → Fin 2 → ℝ := fun t => (B ^ t).mulVec s0 with hsseq
  set hf : (Fin 2 → ℝ) → ℝ := fun x => (r - B 1 1) * x 0 + B 0 1 * x 1 with hhf
  set kseq : ℕ → ℝ := fun t => -hf (sseq t) / dd with hkseq
  have hstep : ∀ t, sseq (t + 1) = B.mulVec (sseq t) := fun t => by
    simp only [hsseq, pow_succ', Matrix.mulVec_mulVec]
  have hk0 : kseq 0 = 0 := by
    simp only [hkseq, hsseq, pow_zero, Matrix.one_mulVec, hhf, hs0, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hk : ∀ t, kseq (t + 1) = r * kseq t + sseq t 0 := fun t => by
    have hid : r * hf (sseq t) - hf (B.mulVec (sseq t)) = dd * sseq t 0 := by
      simp only [hhf, hdd, tr2, det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    simp only [hkseq, hstep t]
    field_simp
    linear_combination hid
  have hbw := fun t => bwd_step (κ := κ) (φ := φ) (r := r) hσ.ne' hβ0.ne' (sseq t)
  -- convergence to zero
  have hs_lim : ∀ j, Tendsto (fun t => sseq t j) atTop (𝓝 0) := fun j => by
    have := ((tendsto_pow_entry hB j 0).mul_const (s0 0)).add
      ((tendsto_pow_entry hB j 1).mul_const (s0 1))
    simpa [hsseq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hk_lim : Tendsto kseq atTop (𝓝 0) := by
    have := ((((hs_lim 0).const_mul (r - B 1 1)).add ((hs_lim 1).const_mul (B 0 1))).neg).div_const
      dd
    simpa [hkseq, hhf] using this
  obtain ⟨Mk, hMk⟩ := bounded_of_tendsto_zero hk_lim
  obtain ⟨Ms, hMs⟩ := bounded_of_tendsto_zero (hs_lim 1)
  -- the second equilibrium
  set p : ℕ → Ω → ℝ := fun t _ => kseq (t + 1) with hp
  set y : ℕ → Ω → ℝ := fun t _ => sseq t 1 + loadY κ β r * kseq t with hy
  have hpa : 𝔼.Adapted p := fun t => 𝔼.const t _
  have hya : 𝔼.Adapted y := fun t => 𝔼.const t _
  have hlag : ∀ t ω, lagP (fun _ => 0) p t ω = kseq t := by
    intro t ω
    cases t with
    | zero => simp [lagP, hk0]
    | succ t => rfl
  have he : IsEquilibrium 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine (eq_iff_pointwise 𝔼 hσ.ne' hpa).2 fun t ω => ?_
    rw [hlag t ω, hp, hy, 𝔼.const, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have b1 := (hbw t).1
    have b2 := (hbw t).2
    rw [← hstep t] at b1 b2
    refine ⟨(is_iff (k := kseq t) hκ.ne' hP _ _ _ _).2 ?_, (pc_iff (r := r) hκ.ne' _ _ _ _).2 ?_,
      by simp⟩
    · rw [hk (t + 1), hk t]
      linear_combination b2
    · rw [hk (t + 1), hk t]
      linear_combination b1
  have hb : BoundedEq 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine ⟨he, hya, hpa, ⟨Ms + |loadY κ β r| * Mk, fun t ω => ?_⟩, ⟨Mk, fun t ω => hMk (t + 1)⟩⟩
    have h1 := mul_le_mul_of_nonneg_left (hMk t) (abs_nonneg (loadY κ β r))
    calc |sseq t 1 + loadY κ β r * kseq t| ≤ |sseq t 1| + |loadY κ β r * kseq t| :=
          abs_add_le _ _
      _ ≤ Ms + |loadY κ β r| * Mk := by rw [abs_mul]; linarith [hMs t]
  intro hD
  obtain ⟨-, huniq⟩ := hD (fun _ => 0) (fun _ => 0) (map_zero _) ⟨0, fun _ => by simp⟩
  obtain ⟨-, hp0, -⟩ := huniq _ _ _ _ _ _ hb (zero_boundedEq 𝔼 hσ.ne' _)
  have h0 := congrFun (congrFun hp0 0) (Classical.arbitrary Ω)
  simp only [hp, hk 0, hk0, mul_zero, zero_add, hsseq, pow_zero, Matrix.one_mulVec, hs0,
    Matrix.cons_val_zero] at h0
  simp only [hBdef, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0
  have : -κ / β ≠ 0 := div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  exact this h0

/-! ### The determinacy region: the corrected statement -/

/-- Galí (2015), Ex. 4.6 (**necessity on `[φ*, 0]`**): for `φ* ≤ φ_p ≤ 0` the price-level rule
does not generate a unique stationary equilibrium. -/
theorem not_determinate_of_le [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : φ ≤ 0) (hφs : phiStar σ κ β ≤ φ) :
    ¬ Determinate 𝔼 β σ κ φ := by
  rcases hφ0.lt_or_eq with hφ | rfl
  · rcases hφs.lt_or_eq with hφs | rfl
    · exact not_determinate_of_neg 𝔼 hσ hκ hβ0 hβ1 hφ hφs
    · exact not_determinate_phiStar 𝔼 hσ hκ hβ0
  · exact not_determinate_zero 𝔼 hσ hκ

/-- **Ex. 4.6, corrected** (Galí 2015, p. 125): for `σ, κ > 0` and `0 < β < 1`, the price-level
rule `i_t = r^n_t + φ_p p̂_t` generates a unique stationary equilibrium (for every initial price
level) if and only if `φ_p > 0` or `φ_p < φ* = −2 − 4σ(1 + β)/κ`. -/
theorem determinate_iff [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) : Determinate 𝔼 β σ κ φ ↔ 0 < φ ∨ φ < phiStar σ κ β := by
  constructor
  · intro hD
    by_contra hc
    push Not at hc
    exact not_determinate_of_le 𝔼 hσ hκ hβ0 hβ1 hc.1 hc.2 hD
  · rintro (h | h)
    · exact determinate_of_pos 𝔼 hσ hκ hβ0 hβ1 h
    · exact determinate_of_lt_phiStar 𝔼 hσ hκ hβ0 hβ1 h

/-- **Ex. 4.6** (Galí 2015, p. 125, the book's claim where it is true): for `φ_p ≥ φ*`, in
particular for every `φ_p ≥ 0`, the rule generates a unique stationary equilibrium iff
`φ_p > 0`. -/
theorem determinate_iff_pos_of_ge [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφs : phiStar σ κ β ≤ φ) :
    Determinate 𝔼 β σ κ φ ↔ 0 < φ := by
  rw [determinate_iff 𝔼 hσ hκ hβ0 hβ1]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd hφs (not_le.2 h)
  · exact Or.inl

/-- **Ex. 4.6, counterexample** (Galí 2015, p. 125): the printed claim "unique stationary
equilibrium if and only if `φ_p > 0`" fails over all real `φ_p`: `φ_p = φ* − 1 < 0` is
determinate. -/
theorem book_claim_false [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) : ¬ ∀ φ, Determinate 𝔼 β σ κ φ ↔ 0 < φ := by
  intro h
  have hD := determinate_of_lt_phiStar 𝔼 (φ := phiStar σ κ β - 1) hσ hκ hβ0 hβ1 (by linarith)
  have hneg : phiStar σ κ β - 1 < 0 := by
    unfold phiStar
    have : 0 < 4 * σ * (1 + β) / κ := by positivity
    linarith
  exact absurd ((h _).1 hD) (not_lt.2 hneg.le)

end Gali.MonetaryPolicyDesign.Ex4_6

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stable invariant subspace of a real matrix

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 and footnotes 1–2; Blanchard and
Kahn (1980). Linear algebra behind the general Blanchard–Kahn theorem (`GeneralBK`).

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.InvariantSplit`, namespace
renamed; this project does not import across projects). Used here for Galí (2015), Ex. 4.4(c),
p. 123: uniqueness of the equilibrium under the money supply rule (`Ex4_4Determinacy`).

For a real square matrix `A` (any finite index type):

* `eigs A`: the complex eigenvalues of `A` with algebraic multiplicity (the roots of the
  characteristic polynomial over `ℂ`), `stableCount A` the number of them in the open unit disc,
  `NoUnit A`: no eigenvalue on the unit circle.
* `boundedOrbits A`: the real subspace of vectors `v` whose orbit `Aᵗ v` is bounded — the real
  stable invariant subspace when `NoUnit A` holds.
* `pow_entry_bound`: eigenvalues in the open disc give geometric decay of the powers (Gelfand's
  formula); `norm_le_one_of_pow_bounded`: bounded powers force eigenvalues in the closed disc.
* `stableCount_le_finrank`: the number of stable eigenvalues (with multiplicity) is at most the
  dimension of `boundedOrbits A` (complex generalised eigenspaces of stable eigenvalues have
  bounded orbits; their real and imaginary parts lie in `boundedOrbits A`).
* `finrank_le_stableCount`, `finrank_eq_stableCount`: with no eigenvalue on the unit circle the
  dimension of `boundedOrbits A` *equals* the number of eigenvalues in the open disc (the
  restriction of `A` to it, `restrict_block`, has a characteristic polynomial dividing that of
  `A` and bounded powers, `exists_restrict_stable`); `boundedOrbits_eq_bot_of_unstable`.
* `tendsto_of_mem_boundedOrbits`: with no eigenvalue on the unit circle every bounded orbit tends
  to `0` — `boundedOrbits A` is the real stable invariant subspace `{v : Aᵗ v → 0}`.

For a split state `Z ⊕ X` (`X` the predetermined coordinates):

* `GenericX A`: `boundedOrbits A` meets `{x = 0}` only in `0` (the genericity condition).
* `exists_graph`: if moreover `dim boundedOrbits A = |X|`, the subspace is the graph of a matrix
  `G : Z × X` (`IsGraph`), so `A [G; I] = [G; I] Λ` with `Λ = A_xz G + A_xx` (`lam`), and with
  `C = A_zz − G A_xz` (`cmat`) the change of variables `ẑ = z − G x` makes `A` block triangular:
  `charpoly A = charpoly C · charpoly Λ` (`charpoly_split`, `eigs_split`).
* `lam_stable`: under `NoUnit`, every eigenvalue of `Λ` lies in the open disc;
  `cmat_unstable`: every eigenvalue of `C` lies outside the closed disc;
  `stableCount_eq_card`: hence exactly `|X|` eigenvalues of `A` lie in the open disc.

The proof of `pow_entry_bound` is restated from `BlanchardKahn.pow_entry_bound` (from the Galí
Chapter 6 project), generalised from `Fin n` to any finite index type.
-/

namespace Gali.MonetaryPolicyDesign.InvariantSplit

open Polynomial Filter Topology
open scoped Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Complex eigenvalues of a real matrix -/

/-- Woodford (2003), App. C.1, p. 670: the complex eigenvalues of a real square matrix, with
algebraic multiplicity (the roots of its characteristic polynomial over `ℂ`). -/
noncomputable def eigs (K : Matrix κ κ ℝ) : Multiset ℂ := (K.map Complex.ofReal).charpoly.roots

/-- Woodford (2003), App. C.1, p. 670: the number of eigenvalues (with multiplicity) in the open
unit disc. -/
noncomputable def stableCount (K : Matrix κ κ ℝ) : ℕ :=
  Multiset.card ((eigs K).filter (fun μ => ‖μ‖ < 1))

/-- Woodford (2003), App. C.1, p. 670, fn. 1: no eigenvalue lies on the unit circle. -/
def NoUnit (K : Matrix κ κ ℝ) : Prop := ∀ μ ∈ eigs K, ‖μ‖ ≠ 1

/-- Woodford (2003), App. C.1, p. 670 (tool): `μ` is an eigenvalue iff `det (μ I − K) = 0`. -/
theorem mem_eigs_iff (K : Matrix κ κ ℝ) (μ : ℂ) :
    μ ∈ eigs K ↔ (Matrix.scalar κ μ - K.map Complex.ofReal).det = 0 := by
  rw [eigs, mem_roots (Matrix.charpoly_monic _).ne_zero, IsRoot, Matrix.eval_charpoly]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue has a complex eigenvector. -/
theorem exists_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} (h : μ ∈ eigs K) :
    ∃ c : κ → ℂ, c ≠ 0 ∧ K.map Complex.ofReal *ᵥ c = μ • c := by
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ((mem_eigs_iff K μ).mp h)
  refine ⟨c, hc0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hc
  rw [← hc]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue has a complex left eigenvector. -/
theorem exists_left_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} (h : μ ∈ eigs K) :
    ∃ q : κ → ℂ, q ≠ 0 ∧ q ᵥ* K.map Complex.ofReal = μ • q := by
  obtain ⟨q, hq0, hq⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr ((mem_eigs_iff K μ).mp h)
  refine ⟨q, hq0, ?_⟩
  rw [Matrix.vecMul_sub, sub_eq_zero] at hq
  rw [← hq]
  funext i
  simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]

/-- Woodford (2003), App. C.1, p. 670 (tool): a complex eigenvector gives an eigenvalue. -/
theorem mem_eigs_of_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} {c : κ → ℂ} (hc0 : c ≠ 0)
    (hc : K.map Complex.ofReal *ᵥ c = μ • c) : μ ∈ eigs K := by
  rw [mem_eigs_iff, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, hc0, ?_⟩
  rw [Matrix.sub_mulVec, hc]
  funext i
  simp [Matrix.scalar_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvector of `M` is one of every power,
`Mᵗ c = μᵗ c`. -/
theorem pow_mulVec_eigvec {R : Type*} [CommRing R] {M : Matrix κ κ R} {μ : R} {c : κ → R}
    (hc : M *ᵥ c = μ • c) (t : ℕ) : M ^ t *ᵥ c = μ ^ t • c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- Woodford (2003), App. C.1, p. 670 (tool): powers of the complexified matrix are the
complexified powers. -/
theorem map_ofReal_pow (K : Matrix κ κ ℝ) (t : ℕ) :
    (K ^ t).map Complex.ofReal = K.map Complex.ofReal ^ t :=
  Matrix.map_pow K Complex.ofRealHom t

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues equals the dimension. -/
theorem card_eigs (K : Matrix κ κ ℝ) : Multiset.card (eigs K) = Fintype.card κ := by
  rw [eigs, IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]

/-! ### Geometric decay and bounded powers -/

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn, the tool; restated from
`BlanchardKahn.pow_entry_bound` for any finite index type): if every complex eigenvalue of a
real square matrix `K` lies in the open unit disc, the entries of `Kᵏ` decay geometrically
(Gelfand's spectral radius formula). -/
theorem pow_entry_bound (K : Matrix κ κ ℝ) (h : ∀ μ ∈ eigs K, ‖μ‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix κ κ ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    have hm : w ∈ A.charpoly.roots := by
      rw [mem_roots (Matrix.charpoly_monic A).ne_zero]; exact hw
    exact ⟨Multiset.mem_toFinset.mpr hm, h w hm⟩
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have := h w (Multiset.mem_toFinset.mp hw)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using this
  have hsr : spectralRadius ℂ A ≤ (ρ0 : ENNReal) := by
    refine iSup₂_le fun w hw => ?_
    rw [quasispectrum_eq_spectrum_union_zero] at hw
    rcases hw with hw | hw
    · exact ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun w => ‖w‖₊) (hspec w hw).1)
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      simp
  set r : ℝ := ((ρ0 : ℝ) + 1) / 2 with hr
  have hρ0' : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
  have hρ0r : (ρ0 : ℝ) < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hbig : ∀ k ≥ N + 1, ‖A ^ k‖ ≤ r ^ k := by
    intro k hk
    have h1 := hN k (by omega)
    rw [ENNReal.ofReal_lt_ofReal_iff hr0] at h1
    have hk0 : k ≠ 0 := by omega
    have h2 : (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖A ^ k‖ := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow (norm_nonneg _) hk0
    rw [← h2]
    exact (pow_lt_pow_left₀ h1 (Real.rpow_nonneg (norm_nonneg _) _) hk0).le
  set Cb : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k with hCb
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
    Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
  have hCb0 : 0 ≤ Cb := by linarith
  have hall : ∀ k, ‖A ^ k‖ ≤ Cb * r ^ k := by
    intro k
    by_cases hk : k ≤ N
    · have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hle : ‖A ^ k‖ / r ^ k ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
        Finset.single_le_sum (f := fun k => ‖A ^ k‖ / r ^ k)
          (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) hmem
      have hrk : 0 < r ^ k := pow_pos hr0 k
      have : ‖A ^ k‖ = ‖A ^ k‖ / r ^ k * r ^ k := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hrk.le
    · have := hbig k (by omega)
      have hrk : 0 ≤ r ^ k := pow_nonneg hr0.le k
      nlinarith
  refine ⟨Cb, r, hCb0, hr0, hr1, fun k i j => ?_⟩
  have hentry : |(K ^ k) i j| = ‖(A ^ k) i j‖ := by
    have e : (A ^ k) i j = ((K ^ k) i j : ℂ) := by
      rw [hA, ← map_ofReal_pow]; rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [hentry]
  refine le_trans ?_ (hall k)
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖(A ^ k) i j‖₊ ≤ ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖(A ^ k) i j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j, ‖(A ^ k) i j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖(A ^ k) i j‖₊) (Finset.mem_univ i)
  have := h1.trans h2
  rw [← coe_nnnorm]
  exact_mod_cast this

/-- Woodford (2003), App. C.1, p. 670 (tool): if the entries of all powers of a real matrix are
bounded, every complex eigenvalue lies in the closed unit disc. -/
theorem norm_le_one_of_pow_bounded {K : Matrix κ κ ℝ} {Cb : ℝ}
    (hb : ∀ t i j, |(K ^ t) i j| ≤ Cb) : ∀ μ ∈ eigs K, ‖μ‖ ≤ 1 := by
  intro μ hμ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hc0 (funext hne)
  by_contra hgt
  push Not at hgt
  set D : ℝ := ∑ j, Cb * ‖c j‖ with hD
  have hle : ∀ t : ℕ, ‖μ‖ ^ t * ‖c i‖ ≤ D := by
    intro t
    have e := congrFun (pow_mulVec_eigvec hc t) i
    rw [← map_ofReal_pow] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [← norm_pow, ← norm_mul, ← e, Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb t i j) (norm_nonneg _)
  have hci : 0 < ‖c i‖ := norm_pos_iff.mpr hi
  have htend : Tendsto (fun t : ℕ => ‖μ‖ ^ t * ‖c i‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hci
  obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop D).exists
  exact absurd (hle t) (not_le.mpr ht)

/-! ### The bounded-orbit (stable) subspace -/

/-- Woodford (2003), App. C.1, p. 670, fn. 2: the real vectors whose orbit `Aᵗ v` under
`y_{t+1} = A y_t` is bounded — the real stable invariant subspace of `A` when no eigenvalue lies on
the unit circle. -/
def boundedOrbits (A : Matrix κ κ ℝ) : Submodule ℝ (κ → ℝ) where
  carrier := {v | ∃ C, ∀ t i, |(A ^ t *ᵥ v) i| ≤ C}
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun t i => ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hC t i) (hD t i))
  zero_mem' := ⟨0, fun t i => by simp⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨|c| * C, fun t i => ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC t i) (abs_nonneg c)

/-- Woodford (2003), App. C.1, p. 670 (tool): membership in the bounded-orbit subspace. -/
theorem mem_boundedOrbits {A : Matrix κ κ ℝ} {v : κ → ℝ} :
    v ∈ boundedOrbits A ↔ ∃ C, ∀ t i, |(A ^ t *ᵥ v) i| ≤ C := Iff.rfl

/-- Woodford (2003), App. C.1, p. 670 (tool): the bounded-orbit subspace is `A`-invariant. -/
theorem mulVec_mem_boundedOrbits {A : Matrix κ κ ℝ} {v : κ → ℝ} (hv : v ∈ boundedOrbits A) :
    A *ᵥ v ∈ boundedOrbits A := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨C, fun t i => ?_⟩
  rw [Matrix.mulVec_mulVec, ← pow_succ]
  exact hC (t + 1) i

/-- Woodford (2003), App. C.1, p. 670 (tool): a vector whose orbit is a bounded sequence `y`
lies in the bounded-orbit subspace. -/
theorem mem_boundedOrbits_of_orbit {A : Matrix κ κ ℝ} {y : ℕ → κ → ℝ}
    (hy : ∀ t, y (t + 1) = A *ᵥ y t) {C : ℝ} (hC : ∀ t i, |y t i| ≤ C) :
    y 0 ∈ boundedOrbits A := by
  have horb : ∀ t, A ^ t *ᵥ y 0 = y t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hy t]
  exact ⟨C, fun t i => by rw [horb t]; exact hC t i⟩

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the real part of a complexified matrix–vector
product. -/
theorem re_mulVec (K : Matrix κ κ ℝ) (v : κ → ℂ) (i : κ) :
    ((K.map Complex.ofReal *ᵥ v) i).re = (K *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the imaginary part of a complexified matrix–vector
product. -/
theorem im_mulVec (K : Matrix κ κ ℝ) (v : κ → ℂ) (i : κ) :
    ((K.map Complex.ofReal *ᵥ v) i).im = (K *ᵥ fun j => (v j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- Woodford (2003), App. C.1, p. 670 (tool): the complex vectors with bounded orbits. -/
def boundedOrbitsC (A : Matrix κ κ ℝ) : Submodule ℂ (κ → ℂ) where
  carrier := {v | ∃ C, ∀ t i, ‖(A.map Complex.ofReal ^ t *ᵥ v) i‖ ≤ C}
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun t i => ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hC t i) (hD t i))
  zero_mem' := ⟨0, fun t i => by simp⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun t i => ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC t i) (norm_nonneg c)

/-- Woodford (2003), App. C.1, p. 670 (tool): generalised eigenvectors of an eigenvalue in the
open unit disc have bounded orbits. Induction on the nilpotency order: with
`u = (A − μ) v` of bounded orbit, `Aᵗ⁺¹ v = μ Aᵗ v + Aᵗ u` stays bounded. -/
theorem maxGenEigenspace_le_boundedOrbitsC (A : Matrix κ κ ℝ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    Module.End.maxGenEigenspace (Matrix.toLin' (A.map Complex.ofReal)) μ ≤ boundedOrbitsC A := by
  set M : Matrix κ κ ℂ := A.map Complex.ofReal with hM
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply] at hk; rw [hk]; exact Submodule.zero_mem _
  | succ k ih =>
    set u : κ → ℂ := M *ᵥ v - μ • v with hu
    have hu' : (Matrix.toLin' M - μ • 1) v = u := by
      simp [hu, Matrix.toLin'_apply]
    have hub : u ∈ boundedOrbitsC A := by
      apply ih
      rw [← hu', ← Module.End.mul_apply, ← pow_succ]
      exact hk
    obtain ⟨Cu, hCu⟩ := hub
    set V : ℝ := ∑ i, ‖v i‖ with hV
    set Mb : ℝ := max V (max Cu 0 / (1 - ‖μ‖)) with hMb
    have h1 : 0 < 1 - ‖μ‖ := by linarith
    have hCM : max Cu 0 ≤ (1 - ‖μ‖) * Mb := by
      have : max Cu 0 / (1 - ‖μ‖) ≤ Mb := le_max_right _ _
      rw [div_le_iff₀ h1] at this
      linarith
    refine ⟨Mb, fun t => ?_⟩
    induction t with
    | zero =>
      intro i
      simp only [pow_zero, Matrix.one_mulVec]
      exact le_trans (Finset.single_le_sum (f := fun i => ‖v i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ i)) (le_max_left _ _)
    | succ t ih2 =>
      intro i
      have e : M ^ (t + 1) *ᵥ v = μ • (M ^ t *ᵥ v) + M ^ t *ᵥ u := by
        rw [pow_succ, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_sub, Matrix.mulVec_smul]
        abel
      rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have hu2 := hCu t i
      have := mul_le_mul_of_nonneg_left (ih2 i) (norm_nonneg μ)
      have : Cu ≤ max Cu 0 := le_max_left _ _
      nlinarith

/-- Woodford (2003), App. C.1, p. 670 (tool): the complex bounded-orbit subspace is spanned by
(the images of) real vectors with bounded orbits, so its complex dimension is at most the real
dimension of `boundedOrbits A`. -/
theorem finrank_boundedOrbitsC_le (A : Matrix κ κ ℝ) :
    Module.finrank ℂ (boundedOrbitsC A) ≤ Module.finrank ℝ (boundedOrbits A) := by
  set b := Module.finBasis ℝ (boundedOrbits A) with hb
  set f : Fin (Module.finrank ℝ (boundedOrbits A)) → (κ → ℂ) :=
    fun k i => (((b k : boundedOrbits A) : κ → ℝ) i : ℂ) with hf
  have hreal : ∀ w ∈ boundedOrbits A,
      (fun i => (w i : ℂ)) ∈ Submodule.span ℂ (Set.range f) := by
    intro w hw
    have hsum := b.sum_repr ⟨w, hw⟩
    have e : (fun i => (w i : ℂ)) = ∑ k, ((b.repr ⟨w, hw⟩ k : ℝ) : ℂ) • f k := by
      funext i
      have := congrArg (fun z : boundedOrbits A => (z : κ → ℝ) i) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, ← this, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  have hle : boundedOrbitsC A ≤ Submodule.span ℂ (Set.range f) := by
    rintro v ⟨C, hC⟩
    have hre : (fun i => (v i).re) ∈ boundedOrbits A := by
      refine ⟨C, fun t i => ?_⟩
      rw [← re_mulVec, map_ofReal_pow]
      exact (Complex.abs_re_le_norm _).trans (hC t i)
    have him : (fun i => (v i).im) ∈ boundedOrbits A := by
      refine ⟨C, fun t i => ?_⟩
      rw [← im_mulVec, map_ofReal_pow]
      exact (Complex.abs_im_le_norm _).trans (hC t i)
    have e : v = (fun i => ((v i).re : ℂ)) + Complex.I • fun i => ((v i).im : ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im (v i)).symm
    rw [e]
    exact Submodule.add_mem _ (hreal _ hre) (Submodule.smul_mem _ _ (hreal _ him))
  calc Module.finrank ℂ (boundedOrbitsC A) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range f)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℝ (boundedOrbits A))) := finrank_range_le_card f
    _ = Module.finrank ℝ (boundedOrbits A) := Fintype.card_fin _

/-- Woodford (2003), App. C.1, p. 670 (tool): the dimension of the span of finitely many
independent subspaces is the sum of their dimensions. -/
theorem finrank_finset_sup {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : ℂ → Submodule ℂ V} (hW : iSupIndep W) (s : Finset ℂ) :
    Module.finrank ℂ (s.sup W : Submodule ℂ V) = ∑ μ ∈ s, Module.finrank ℂ (W μ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (W a) (s.sup W) := by
      rw [Finset.sup_eq_iSup]
      have := hW.disjoint_biSup (x := a) (y := (s : Set ℂ)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (s.sup W)
    rw [disjoint_iff.mp hd, finrank_bot, add_zero] at h
    exact h

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues in a set, counted with
multiplicity, is the sum of their root multiplicities. -/
theorem card_filter_eq_sum (p : ℂ[X]) (P : ℂ → Prop) [DecidablePred P] :
    Multiset.card (p.roots.filter P) =
      ∑ μ ∈ p.roots.toFinset.filter P, p.rootMultiplicity μ := by
  rw [← Multiset.toFinset_sum_count_eq, Multiset.toFinset_filter]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.mem_filter] at hμ
  rw [Multiset.count_filter, count_roots]
  simp only [hμ.2, ↓reduceIte]

/-- **Stable eigenvalues span bounded orbits** (Woodford (2003), App. C.1, p. 670; Blanchard and
Kahn (1980)): the number of eigenvalues of `A` in the open unit disc, counted with algebraic
multiplicity, is at most the dimension of the real bounded-orbit subspace. -/
theorem stableCount_le_finrank (A : Matrix κ κ ℝ) :
    stableCount A ≤ Module.finrank ℝ (boundedOrbits A) := by
  set φ := Matrix.toLin' (A.map Complex.ofReal) with hφ
  set p := (A.map Complex.ofReal).charpoly with hp
  set s := p.roots.toFinset.filter (fun μ => ‖μ‖ < 1) with hs
  have hcount : stableCount A = ∑ μ ∈ s, Module.finrank ℂ (Module.End.maxGenEigenspace φ μ) := by
    rw [stableCount, eigs, card_filter_eq_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [LinearMap.finrank_maxGenEigenspace_eq, hφ, Matrix.charpoly_toLin']
  have hsup : s.sup (Module.End.maxGenEigenspace φ) ≤ boundedOrbitsC A := by
    refine Finset.sup_le fun μ hμ => ?_
    rw [hs, Finset.mem_filter] at hμ
    exact maxGenEigenspace_le_boundedOrbitsC A hμ.2
  rw [hcount, ← finrank_finset_sup (Module.End.independent_maxGenEigenspace φ) s]
  exact (Submodule.finrank_mono hsup).trans (finrank_boundedOrbitsC_le A)

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues outside the closed unit
disc. -/
noncomputable def unstableCount (K : Matrix κ κ ℝ) : ℕ :=
  Multiset.card ((eigs K).filter (fun μ => 1 < ‖μ‖))

/-- Woodford (2003), App. C.1, p. 670: with no eigenvalue on the unit circle, the stable and the
unstable eigenvalues together are all `n` of them. -/
theorem stableCount_add_unstableCount {K : Matrix κ κ ℝ} (h : NoUnit K) :
    stableCount K + unstableCount K = Fintype.card κ := by
  rw [stableCount, unstableCount, ← card_eigs K, ← Multiset.card_add]
  congr 1
  conv_rhs => rw [← Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ < 1) (eigs K)]
  congr 1
  refine Multiset.filter_congr fun μ hμ => ?_
  have := h μ hμ
  constructor
  · intro h1; exact not_lt.mpr h1.le
  · intro h1; exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm this)

/-! ### The bounded-orbit subspace has exactly `stableCount` dimensions (no unit eigenvalue) -/

/-- Woodford (2003), App. C.1, p. 670 (tool): an `A`-invariant subspace `V` carries a matrix `T`
of the restriction of `A` (in the basis `Module.finBasis`), and `charpoly T` divides
`charpoly A` (block triangular form in a basis adapted to `V ⊕ W`, `W` a complement). -/
theorem restrict_block (A : Matrix κ κ ℝ) (V : Submodule ℝ (κ → ℝ))
    (hV : ∀ v ∈ V, A *ᵥ v ∈ V) :
    ∃ T : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ,
      T.charpoly ∣ A.charpoly ∧ ∀ j, A *ᵥ (Module.finBasis ℝ V j : κ → ℝ) =
        ∑ i, T i j • (Module.finBasis ℝ V i : κ → ℝ) := by
  set bV := Module.finBasis ℝ V with hbV
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  set bW := Module.finBasis ℝ W with hbW
  set e := Submodule.prodEquivOfIsCompl V W hW with he
  set φ : Module.End ℝ (κ → ℝ) := Matrix.toLin' A with hφ
  set ψ := e.symm.conj φ with hψdef
  set bb := bV.prod bW with hbb
  set T' := LinearMap.toMatrix bb bb ψ with hT'
  have hψ : ∀ j, ψ (bb (Sum.inl j)) = (⟨A *ᵥ bV j, hV _ (bV j).2⟩, 0) := by
    intro j
    rw [hψdef, LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    have h1 : e (bb (Sum.inl j)) = bV j := by
      rw [he, Submodule.coe_prodEquivOfIsCompl', hbb, Module.Basis.prod_apply_inl_fst,
        Module.Basis.prod_apply_inl_snd]
      simp
    rw [h1, hφ, Matrix.toLin'_apply]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left V W hW ⟨_, _⟩
  have h21 : T'.toBlocks₂₁ = 0 := by
    ext k j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, hT',
      LinearMap.toMatrix_apply]
    rw [hψ, hbb, Module.Basis.prod_repr_inr]
    simp
  have h11 : ∀ i j, T'.toBlocks₁₁ i j = bV.repr ⟨A *ᵥ bV j, hV _ (bV j).2⟩ i := by
    intro i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hT', LinearMap.toMatrix_apply]
    rw [hψ, hbb, Module.Basis.prod_repr_inl]
  refine ⟨T'.toBlocks₁₁, ?_, fun j => ?_⟩
  · have hc : A.charpoly = T'.charpoly := by
      rw [hT', LinearMap.charpoly_toMatrix, hψdef, LinearEquiv.charpoly_conj, hφ,
        Matrix.charpoly_toLin']
    rw [hc, ← Matrix.fromBlocks_toBlocks T', h21, Matrix.charpoly_fromBlocks_zero₂₁]
    exact dvd_mul_right _ _
  · have hsum := bV.sum_repr ⟨A *ᵥ bV j, hV _ (bV j).2⟩
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [h11]

/-- Woodford (2003), App. C.1, p. 670 (tool): `|μ| ≤ 1` when `μᵗ z` stays bounded, `z ≠ 0`. -/
theorem norm_le_one_of_bounded_pow_mul {μ z : ℂ} (hz : z ≠ 0) {C : ℝ}
    (h : ∀ t : ℕ, ‖μ ^ t * z‖ ≤ C) : ‖μ‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have htend : Tendsto (fun t : ℕ => ‖μ‖ ^ t * ‖z‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hz0
  obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop C).exists
  have := h t
  rw [norm_mul, norm_pow] at this
  linarith

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn (1980)): if no eigenvalue lies on the
unit circle, the matrix `T` of `A` restricted to the bounded-orbit subspace has all its
eigenvalues in the open unit disc, and they are eigenvalues of `A` with multiplicity. The
restriction has bounded powers, so its eigenvalues lie in the closed disc (`restrict_block`
gives `charpoly T ∣ charpoly A`). -/
theorem exists_restrict_stable {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    ∃ T : Matrix (Fin (Module.finrank ℝ (boundedOrbits A)))
        (Fin (Module.finrank ℝ (boundedOrbits A))) ℝ,
      eigs T ≤ eigs A ∧ (∀ μ ∈ eigs T, ‖μ‖ < 1) ∧
      ∀ j, A *ᵥ (Module.finBasis ℝ (boundedOrbits A) j : κ → ℝ) =
        ∑ i, T i j • (Module.finBasis ℝ (boundedOrbits A) i : κ → ℝ) := by
  set B := boundedOrbits A with hB
  set bV := Module.finBasis ℝ B with hbV
  obtain ⟨T, hdvd, hexp⟩ := restrict_block A B (fun v hv => mulVec_mem_boundedOrbits hv)
  have hle : eigs T ≤ eigs A := by
    have e1 : (T.map Complex.ofReal).charpoly = T.charpoly.map Complex.ofRealHom :=
      Matrix.charpoly_map T Complex.ofRealHom
    have e2 : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
      Matrix.charpoly_map A Complex.ofRealHom
    rw [eigs, eigs, e1, e2]
    exact Polynomial.roots.le_of_dvd ((Matrix.charpoly_monic A).map _).ne_zero
      (Polynomial.map_dvd _ hdvd)
  set bv : Fin (Module.finrank ℝ B) → κ → ℝ := fun j => (bV j : κ → ℝ) with hbv
  have hli : LinearIndependent ℝ bv := bV.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hst : ∀ μ ∈ eigs T, ‖μ‖ < 1 := by
    intro μ hμ
    obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
    have hcT : ∀ i, ∑ j, (T i j : ℂ) * c j = μ * c i := fun i => by
      have := congrFun hc i
      simpa [Matrix.mulVec, dotProduct] using this
    set u : κ → ℂ := fun k => ∑ j, c j * (bv j k : ℂ) with hu
    have hAu : A.map Complex.ofReal *ᵥ u = μ • u := by
      funext k
      have hb : ∀ j, ∑ l, (A k l : ℂ) * (bv j l : ℂ) = ∑ i, (T i j : ℂ) * (bv i k : ℂ) := by
        intro j
        have := congrFun (hexp j) k
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at this
        exact_mod_cast this
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hu, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      have e1 : ∀ j, ∑ l, (A k l : ℂ) * (c j * (bv j l : ℂ)) =
          c j * ∑ i, (T i j : ℂ) * (bv i k : ℂ) := by
        intro j
        rw [← hb j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      simp only [e1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show μ * (c i * (bv i k : ℂ)) = (∑ j, (T i j : ℂ) * c j) * (bv i k : ℂ) by
        rw [hcT i]; ring, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hre : (fun k => (u k).re) = ∑ j, (c j).re • bv j := by
      funext k
      simp [hu, Finset.sum_apply, Complex.re_sum]
    have him : (fun k => (u k).im) = ∑ j, (c j).im • bv j := by
      funext k
      simp [hu, Finset.sum_apply, Complex.im_sum]
    have hreB : (fun k => (u k).re) ∈ B := by
      rw [hre]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bV j).2
    have himB : (fun k => (u k).im) ∈ B := by
      rw [him]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bV j).2
    have hu0 : u ≠ 0 := by
      intro h0
      have h1 : ∑ j, (c j).re • bv j = 0 := by
        rw [← hre, h0]; funext k; simp
      have h2 : ∑ j, (c j).im • bv j = 0 := by
        rw [← him, h0]; funext k; simp
      apply hc0
      funext j
      exact Complex.ext (Fintype.linearIndependent_iff.mp hli _ h1 j)
        (Fintype.linearIndependent_iff.mp hli _ h2 j)
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hu0 (funext hne)
    obtain ⟨C1, hC1⟩ := hreB
    obtain ⟨C2, hC2⟩ := himB
    have hbd : ∀ t : ℕ, ‖μ ^ t * u k‖ ≤ C1 + C2 := by
      intro t
      have e := congrFun (pow_mulVec_eigvec hAu t) k
      rw [← map_ofReal_pow] at e
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [← e]
      have hr := hC1 t k
      have hi := hC2 t k
      rw [← re_mulVec] at hr
      rw [← im_mulVec] at hi
      refine (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hr hi)
    have h1 := norm_le_one_of_bounded_pow_mul hk hbd
    exact lt_of_le_of_ne h1 (hnu μ (Multiset.mem_of_le hle hμ))
  exact ⟨T, hle, hst, hexp⟩

/-- **The stable dimension equals the stable count** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn (1980)), upper bound: if no eigenvalue lies on the unit circle, the dimension
of the bounded-orbit subspace is at most the number of eigenvalues in the open unit disc. -/
theorem finrank_le_stableCount {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    Module.finrank ℝ (boundedOrbits A) ≤ stableCount A := by
  obtain ⟨T, hle, hst, -⟩ := exists_restrict_stable hnu
  calc Module.finrank ℝ (boundedOrbits A) = Multiset.card (eigs T) := by
        rw [card_eigs, Fintype.card_fin]
    _ = Multiset.card ((eigs T).filter (fun μ => ‖μ‖ < 1)) := by
        rw [Multiset.filter_eq_self.mpr hst]
    _ ≤ stableCount A := Multiset.card_le_card (Multiset.filter_le_filter _ hle)

/-- **Bounded orbits decay** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn (1980)): if
no eigenvalue lies on the unit circle, every bounded orbit tends to `0`, so the bounded-orbit
subspace is the stable subspace `{v : Aᵗ v → 0}`. On the subspace, `A` acts through the matrix
`T` of `exists_restrict_stable`, whose powers decay geometrically. -/
theorem tendsto_of_mem_boundedOrbits {A : Matrix κ κ ℝ} (hnu : NoUnit A) {v : κ → ℝ}
    (hv : v ∈ boundedOrbits A) : Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) := by
  obtain ⟨T, -, hst, hexp⟩ := exists_restrict_stable hnu
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hT⟩ := pow_entry_bound T hst
  set bV := Module.finBasis ℝ (boundedOrbits A) with hbV
  set b : Fin (Module.finrank ℝ (boundedOrbits A)) → κ → ℝ := fun j => (bV j : κ → ℝ) with hb
  have hpow : ∀ t j, A ^ t *ᵥ b j = ∑ i, (T ^ t) i j • b i := by
    intro t
    induction t with
    | zero =>
      intro j
      simp only [pow_zero, Matrix.one_mulVec, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    | succ t ih =>
      intro j
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih j, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hb, hexp, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul, pow_succ', Matrix.mul_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hv' : v = ∑ j, bV.repr ⟨v, hv⟩ j • b j := by
    have := congrArg Subtype.val (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hentry : ∀ i j, Tendsto (fun t => (T ^ t) i j) atTop (𝓝 0) := by
    intro i j
    refine squeeze_zero_norm (a := fun t : ℕ => Cb * ρ ^ t) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hT t i j
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul Cb
  have e : (fun t => A ^ t *ᵥ v) =
      fun t => ∑ j, ∑ i, (bV.repr ⟨v, hv⟩ j * (T ^ t) i j) • b i := by
    funext t
    conv_lhs => rw [hv']
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, hpow, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [e]
  have : (0 : κ → ℝ) = ∑ j : Fin (Module.finrank ℝ (boundedOrbits A)),
      ∑ i : Fin (Module.finrank ℝ (boundedOrbits A)), (bV.repr ⟨v, hv⟩ j * 0) • b i := by
    simp
  rw [this]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => ?_
  exact ((hentry i j).const_mul _).smul_const _

/-- **The stable dimension equals the stable count** (Woodford (2003), App. C.1, p. 670, the
"equivalently" of the counting rule; Blanchard and Kahn (1980)): with no eigenvalue on the unit
circle, the real bounded-orbit (stable) subspace has dimension equal to the number of eigenvalues
in the open unit disc, counted with algebraic multiplicity. -/
theorem finrank_eq_stableCount {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    Module.finrank ℝ (boundedOrbits A) = stableCount A :=
  le_antisymm (finrank_le_stableCount hnu) (stableCount_le_finrank A)

/-- Woodford (2003), App. C.1, p. 670 (Prop. C.1's mechanism): if every eigenvalue lies outside
the closed unit disc, the only bounded orbit is `0`. -/
theorem boundedOrbits_eq_bot_of_unstable {A : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs A, 1 < ‖μ‖) :
    boundedOrbits A = ⊥ := by
  have hnu : NoUnit A := fun μ hμ h1 => by have := h μ hμ; rw [h1] at this; exact lt_irrefl _ this
  have hc : stableCount A = 0 := by
    rw [stableCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    exact fun μ hμ => not_lt.mpr (h μ hμ).le
  rw [← Submodule.finrank_eq_zero, finrank_eq_stableCount hnu, hc]

/-! ### Bounded linear recursions -/

/-- Woodford (2003), App. C.1, p. 670 (tool): an entry of a matrix is bounded by the sum of the
absolute values of all entries. -/
theorem abs_entry_le_sum {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) (i : m)
    (j : n) : |M i j| ≤ ∑ i, ∑ j, |M i j| :=
  (Finset.single_le_sum (f := fun j => |M i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- Woodford (2003), App. C.1, p. 670 (tool): `|(M v)_i| ≤ n a b` when the entries of `M` are
bounded by `a` and those of `v` by `b`. -/
theorem abs_mulVec_le {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) {a b : ℝ}
    (hM : ∀ i j, |M i j| ≤ a) (hv : ∀ j, |v j| ≤ b) (i : m) :
    |(M *ᵥ v) i| ≤ Fintype.card n * (a * b) := by
  rw [Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : n, a * b := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hM i j) (hv j) (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
    _ = Fintype.card n * (a * b) := by simp

/-- Woodford (2003), App. C.1, p. 670 (tool): the solution of `x_{t+1} = L x_t + f_t`,
`x_t = Lᵗ x_0 + ∑_{k<t} Lᵏ f_{t−1−k}`. -/
theorem rec_closed {L : Matrix κ κ ℝ} {f x : ℕ → κ → ℝ} (hx : ∀ t, x (t + 1) = L *ᵥ x t + f t)
    (t : ℕ) : x t = L ^ t *ᵥ x 0 + ∑ k ∈ Finset.range t, L ^ k *ᵥ f (t - 1 - k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx t, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_mulVec, ← pow_succ',
      Finset.sum_range_succ' _ t, add_assoc]
    congr 1
    simp only [pow_zero, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← pow_succ']
    rw [show t + 1 - 1 - 0 = t by omega]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show t + 1 - 1 - (k + 1) = t - 1 - k by omega]

/-- Woodford (2003), App. C.1, p. 670 (tool): if the powers of `L` decay geometrically, the
backward recursion `x_{t+1} = L x_t + f_t` with bounded `f` has a bounded solution. -/
theorem rec_bounded {L : Matrix κ κ ℝ} {Cb ρ : ℝ} (hCb : 0 ≤ Cb) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hL : ∀ k i j, |(L ^ k) i j| ≤ Cb * ρ ^ k) {f x : ℕ → κ → ℝ}
    (hx : ∀ t, x (t + 1) = L *ᵥ x t + f t) {F X0 : ℝ} (hF0 : 0 ≤ F) (hX0 : 0 ≤ X0)
    (hf : ∀ t j, |f t j| ≤ F) (hx0 : ∀ j, |x 0 j| ≤ X0) :
    ∀ t j, |x t j| ≤ Fintype.card κ * Cb * (X0 + F / (1 - ρ)) := by
  intro t j
  set c : ℝ := (Fintype.card κ : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have h1 : 0 < 1 - ρ := by linarith
  rw [rec_closed hx t, Pi.add_apply, Finset.sum_apply]
  have hA : |(L ^ t *ᵥ x 0) j| ≤ c * (Cb * ρ ^ t * X0) :=
    abs_mulVec_le _ _ (hL t) hx0 j
  have hB : ∀ k ∈ Finset.range t, |(L ^ k *ᵥ f (t - 1 - k)) j| ≤ c * Cb * F * ρ ^ k := by
    intro k _
    have := abs_mulVec_le _ _ (hL k) (hf (t - 1 - k)) j
    calc _ ≤ c * (Cb * ρ ^ k * F) := this
      _ = c * Cb * F * ρ ^ k := by ring
  have hgeo : ∑ k ∈ Finset.range t, ρ ^ k ≤ 1 / (1 - ρ) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := t) hρ0 hρ1
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have hρt : ρ ^ t ≤ 1 := pow_le_one₀ hρ0 hρ1.le
  have hsum : |∑ k ∈ Finset.range t, (L ^ k *ᵥ f (t - 1 - k)) j| ≤ c * Cb * F * (1 / (1 - ρ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hB).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  have hcCb : 0 ≤ c * Cb := mul_nonneg hc0 hCb
  calc _ ≤ |(L ^ t *ᵥ x 0) j| + |∑ k ∈ Finset.range t, (L ^ k *ᵥ f (t - 1 - k)) j| :=
        abs_add_le _ _
    _ ≤ c * (Cb * ρ ^ t * X0) + c * Cb * F * (1 / (1 - ρ)) := add_le_add hA hsum
    _ ≤ c * Cb * X0 + c * Cb * F * (1 / (1 - ρ)) := by
        have : c * (Cb * ρ ^ t * X0) = c * Cb * X0 * ρ ^ t := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left hρt (mul_nonneg hcCb hX0)
        linarith
    _ = c * Cb * (X0 + F / (1 - ρ)) := by ring

/-- Woodford (2003), App. C.1, p. 670 (tool): the backward recursion `x_{t+1} = L x_t + f_t`,
`x_0` given. -/
def xrecV {ι : Type*} [Fintype ι] (L : Matrix ι ι ℝ) (f : ℕ → ι → ℝ) (x0 : ι → ℝ) :
    ℕ → ι → ℝ
  | 0 => x0
  | t + 1 => L *ᵥ xrecV L f x0 t + f t

/-! ### Predetermined coordinates: the genericity condition and the graph -/

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 672, fn. 2 (the genericity condition the book leaves
implicit; Blanchard and Kahn (1980)): with the state split into non-predetermined coordinates
`Z` and predetermined coordinates `X`, no nonzero bounded orbit starts with `x = 0`. -/
def GenericX (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ v ∈ boundedOrbits A, (∀ j, v (Sum.inr j) = 0) → v = 0

/-- Woodford (2003), App. C.1, p. 672: the projection onto the predetermined coordinates. -/
def projX : (Z ⊕ X → ℝ) →ₗ[ℝ] (X → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr

/-- Woodford (2003), App. C.1, p. 672: the vector `(G x, x)` of the graph of `G : X → Z`. -/
def graphV (G : Matrix Z X ℝ) (x : X → ℝ) : Z ⊕ X → ℝ := Sum.elim (G *ᵥ x) x

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): the bounded-orbit subspace is the graph
of `G`: it contains every `(G x, x)`, and each of its vectors has `z = G x`. -/
def IsGraph (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Prop :=
  (∀ x, graphV G x ∈ boundedOrbits A) ∧
    ∀ v ∈ boundedOrbits A, ∀ i, v (Sum.inl i) = (G *ᵥ fun j => v (Sum.inr j)) i

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): two matrices acting identically on all vectors
are equal. -/
theorem matrix_eq_of_mulVec {m n : Type*} [Fintype n] {M N : Matrix m n ℝ}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  classical
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): a block matrix acting on `(z, x)`. -/
theorem mulVec_sumElim (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (z : Z → ℝ) (x : X → ℝ) :
    A *ᵥ Sum.elim z x = Sum.elim (A.toBlocks₁₁ *ᵥ z + A.toBlocks₁₂ *ᵥ x)
      (A.toBlocks₂₁ *ᵥ z + A.toBlocks₂₂ *ᵥ x) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  rw [Matrix.fromBlocks_mulVec]
  rfl

/-- **The graph** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)): if the
bounded-orbit subspace has dimension `|X|` and meets `{x = 0}` only in `0`, it projects
isomorphically onto the predetermined coordinates, so it is the graph of a matrix `G`. -/
theorem exists_graph {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A) :
    ∃ G : Matrix Z X ℝ, IsGraph A G := by
  set B := boundedOrbits A with hB
  set f : B →ₗ[ℝ] (X → ℝ) := (projX (Z := Z) (X := X)).domRestrict B with hf
  have hfv : ∀ v : B, ∀ j, f v j = (v : Z ⊕ X → ℝ) (Sum.inr j) := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    exact hg v v.2 (fun j => by rw [← hfv]; exact congrFun hv j)
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hd, Module.finrank_fintype_fun_eq_card])).mp hinj
  choose b hb using fun j : X => hsurj (Pi.single j 1)
  set G : Matrix Z X ℝ := fun i j => (b j : Z ⊕ X → ℝ) (Sum.inl i) with hG
  have h1 : ∀ x : X → ℝ, graphV G x = ∑ j, x j • (b j : Z ⊕ X → ℝ) := by
    intro x
    funext k
    rcases k with i | k
    · simp [graphV, hG, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · have e : ∀ j, (b j : Z ⊕ X → ℝ) (Sum.inr k) = (Pi.single j (1 : ℝ) : X → ℝ) k := fun j => by
        rw [← hfv, hb j]
      simp only [graphV, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [e]
      simp [Pi.single_apply]
  have hmem : ∀ x : X → ℝ, graphV G x ∈ B := by
    intro x
    rw [h1 x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
  refine ⟨G, hmem, fun v hv i => ?_⟩
  set w := v - graphV G (fun j => v (Sum.inr j)) with hw
  have hwB : w ∈ B := Submodule.sub_mem _ hv (hmem _)
  have hw0 : w = 0 := hg w hwB (fun j => by simp [hw, graphV])
  have := congrFun hw0 (Sum.inl i)
  simp only [hw, Pi.sub_apply, graphV, Sum.elim_inl, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Woodford (2003), App. C.1, p. 672: `Λ = A_xz G + A_xx`, the matrix of `A` restricted to the
graph, in the predetermined coordinates. -/
def lam (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Matrix X X ℝ :=
  A.toBlocks₂₁ * G + A.toBlocks₂₂

/-- Woodford (2003), App. C.1, p. 672: `C = A_zz − G A_xz`, the matrix governing
`ẑ_t = z_t − G x_t`. -/
def cmat (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Matrix Z Z ℝ :=
  A.toBlocks₁₁ - G * A.toBlocks₂₁

/-- Woodford (2003), App. C.1, p. 672: invariance of the graph,
`A_zz G + A_zx = G Λ`, i.e. `A [G; I] = [G; I] Λ`. -/
theorem graph_invariant {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G) :
    A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G := by
  refine matrix_eq_of_mulVec fun x => ?_
  have hv := mulVec_mem_boundedOrbits (hG.1 x)
  funext i
  have e := hG.2 _ hv i
  rw [graphV, mulVec_sumElim] at e
  simp only [Sum.elim_inl, Sum.elim_inr] at e
  have e2 : (A.toBlocks₁₁ * G + A.toBlocks₁₂) *ᵥ x =
      A.toBlocks₁₁ *ᵥ (G *ᵥ x) + A.toBlocks₁₂ *ᵥ x := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have e3 : (G * lam A G) *ᵥ x = G *ᵥ (A.toBlocks₂₁ *ᵥ (G *ᵥ x) + A.toBlocks₂₂ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, lam, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [e2, e3]
  exact e

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the invariance identity on vectors,
`A_zz G x + A_zx x = G Λ x`. -/
theorem graph_invariant_vec {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) :
    A.toBlocks₁₁ *ᵥ (G *ᵥ x) + A.toBlocks₁₂ *ᵥ x = G *ᵥ (lam A G *ᵥ x) := by
  have := congrArg (fun M => M *ᵥ x) hinv
  simpa only [Matrix.add_mulVec, Matrix.mulVec_mulVec] using this

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): `Λ x = A_xz G x + A_xx x`. -/
theorem lam_mulVec (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (x : X → ℝ) :
    lam A G *ᵥ x = A.toBlocks₂₁ *ᵥ (G *ᵥ x) + A.toBlocks₂₂ *ᵥ x := by
  rw [lam, Matrix.add_mulVec, Matrix.mulVec_mulVec]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: `A (G x, x) = (G Λ x, Λ x)`. -/
theorem mulVec_graphV {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) :
    A *ᵥ graphV G x = graphV G (lam A G *ᵥ x) := by
  rw [graphV, mulVec_sumElim, graphV, graph_invariant_vec hinv, lam_mulVec]

/-- Woodford (2003), App. C.1, p. 672: `Aᵗ (G x, x) = (G Λᵗ x, Λᵗ x)`. -/
theorem pow_mulVec_graphV {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) (t : ℕ) :
    A ^ t *ᵥ graphV G x = graphV G (lam A G ^ t *ᵥ x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, mulVec_graphV hinv, Matrix.mulVec_mulVec,
      ← pow_succ']

/-- Woodford (2003), App. C.1, p. 672: the powers of `Λ` are bounded (`Λᵗ` is `Aᵗ` on bounded
orbits). -/
theorem lam_pow_bounded {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G) :
    ∃ Cb, ∀ t j k, |(lam A G ^ t) j k| ≤ Cb := by
  have hinv := graph_invariant hG
  choose C hC using fun k : X => hG.1 (Pi.single k (1 : ℝ))
  refine ⟨∑ k, |C k|, fun t j k => ?_⟩
  have e : (lam A G ^ t) j k = (A ^ t *ᵥ graphV G (Pi.single k (1 : ℝ))) (Sum.inr j) := by
    rw [pow_mulVec_graphV hinv, graphV, Sum.elim_inr]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e]
  exact ((hC k t _).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))

/-- Woodford (2003), App. C.1, p. 672 (tool): the change of variables `ẑ = z − G x` and its
inverse. -/
theorem fromBlocks_shear_mul (G : Matrix Z X ℝ) :
    Matrix.fromBlocks (1 : Matrix Z Z ℝ) G 0 (1 : Matrix X X ℝ) *
      Matrix.fromBlocks (1 : Matrix Z Z ℝ) (-G) 0 (1 : Matrix X X ℝ) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-- **Block triangularisation** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)):
in the coordinates `(ẑ, x)`, `ẑ = z − G x`, the matrix `A` is block lower triangular with
diagonal blocks `C` and `Λ`, so `charpoly A = charpoly C · charpoly Λ`. -/
theorem charpoly_split {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    A.charpoly = (cmat A G).charpoly * (lam A G).charpoly := by
  set T := Matrix.fromBlocks (1 : Matrix Z Z ℝ) G 0 (1 : Matrix X X ℝ) with hT
  set T' := Matrix.fromBlocks (1 : Matrix Z Z ℝ) (-G) 0 (1 : Matrix X X ℝ) with hT'
  have hconj : T' * A * T = Matrix.fromBlocks (cmat A G) 0 A.toBlocks₂₁ (lam A G) := by
    rw [hT, hT']
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have h12 : (A.toBlocks₁₁ - G * A.toBlocks₂₁) * G + (A.toBlocks₁₂ - G * A.toBlocks₂₂) = 0 := by
      have e : (A.toBlocks₁₁ - G * A.toBlocks₂₁) * G + (A.toBlocks₁₂ - G * A.toBlocks₂₂) =
          (A.toBlocks₁₁ * G + A.toBlocks₁₂) - G * lam A G := by
        rw [lam, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
      rw [e, hinv, sub_self]
    congr 1
    · simp [cmat, sub_eq_add_neg, Matrix.neg_mul]
    · simpa [sub_eq_add_neg, Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc] using h12
    · simp
    · simp [lam]
  calc A.charpoly = ((T * T') * A).charpoly := by rw [fromBlocks_shear_mul, Matrix.one_mul]
    _ = ((T' * A) * T).charpoly := by rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm]
    _ = _ := by rw [hconj, Matrix.charpoly_fromBlocks_zero₁₂]

/-- Woodford (2003), App. C.1, p. 670 (tool): the characteristic polynomial of the
complexification. -/
theorem charpoly_map_ofReal (K : Matrix κ κ ℝ) :
    (K.map Complex.ofReal).charpoly = K.charpoly.map Complex.ofRealHom :=
  Matrix.charpoly_map K Complex.ofRealHom

/-- Woodford (2003), App. C.1, p. 672: the eigenvalues of `A` are those of `C` together with those
of `Λ`, with multiplicity. -/
theorem eigs_split {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    eigs A = eigs (cmat A G) + eigs (lam A G) := by
  rw [eigs, eigs, eigs, charpoly_map_ofReal, charpoly_map_ofReal, charpoly_map_ofReal,
    charpoly_split hinv, Polynomial.map_mul]
  refine roots_mul ?_
  exact mul_ne_zero ((Matrix.charpoly_monic _).map _).ne_zero
    ((Matrix.charpoly_monic _).map _).ne_zero

/-- Woodford (2003), App. C.1, p. 672: with no eigenvalue on the unit circle, every eigenvalue of
`Λ` lies in the open unit disc. -/
theorem lam_stable {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (hnu : NoUnit A) : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1 := by
  intro μ hμ
  obtain ⟨Cb, hCb⟩ := lam_pow_bounded hG
  have h1 := norm_le_one_of_pow_bounded hCb μ hμ
  have h2 : μ ∈ eigs A := by
    rw [eigs_split (graph_invariant hG)]
    exact Multiset.mem_add.mpr (Or.inr hμ)
  exact lt_of_le_of_ne h1 (hnu μ h2)

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): a bounded solution `ẑ` of
`ẑ_{t+1} = C ẑ_t` starts at `0` — otherwise `(ẑ_0, 0)` would be a nonzero bounded orbit of `A`
with `x = 0` (the orbit is completed by `x_{t+1} = Λ x_t + A_xz ẑ_t`, `x_0 = 0`). -/
theorem zero_of_cmat_orbit {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hG : IsGraph A G) (hg : GenericX A) {Cb ρ : ℝ} (hCb : 0 ≤ Cb) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hL : ∀ k i j, |(lam A G ^ k) i j| ≤ Cb * ρ ^ k) {zh : ℕ → Z → ℝ}
    (hrec : ∀ t, zh (t + 1) = cmat A G *ᵥ zh t) {Kz : ℝ} (hKz : 0 ≤ Kz)
    (hzb : ∀ t i, |zh t i| ≤ Kz) : zh 0 = 0 := by
  have hinv := graph_invariant hG
  set R := A.toBlocks₂₁ with hR
  set x : ℕ → X → ℝ := xrecV (lam A G) (fun t => R *ᵥ zh t) 0 with hx
  have hxrec : ∀ t, x (t + 1) = lam A G *ᵥ x t + R *ᵥ zh t := fun t => rfl
  set aR : ℝ := ∑ i, ∑ j, |R i j| with haR
  set aG : ℝ := ∑ i, ∑ j, |G i j| with haG
  have haR0 : 0 ≤ aR := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have haG0 : 0 ≤ aG := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set F : ℝ := Fintype.card Z * (aR * Kz) with hF
  have hF0 : 0 ≤ F := by positivity
  have hfb : ∀ t j, |(R *ᵥ zh t) j| ≤ F := fun t j =>
    abs_mulVec_le R (zh t) (abs_entry_le_sum R) (hzb t) j
  set Xb : ℝ := Fintype.card X * Cb * (0 + F / (1 - ρ)) with hXb
  have hxb : ∀ t j, |x t j| ≤ Xb :=
    rec_bounded hCb hρ0 hρ1 hL hxrec hF0 le_rfl hfb (fun j => by simp [hx, xrecV])
  have hXb0 : 0 ≤ Xb := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set y : ℕ → Z ⊕ X → ℝ := fun t => Sum.elim (zh t + G *ᵥ x t) (x t) with hy
  have hystep : ∀ t, y (t + 1) = A *ᵥ y t := by
    intro t
    rw [hy, mulVec_sumElim]
    simp only
    rw [hrec t, hxrec t]
    congr 1
    · rw [cmat]
      simp only [Matrix.mulVec_add, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      rw [← graph_invariant_vec hinv]
      abel
    · simp only [Matrix.mulVec_add, lam_mulVec]
      abel
  have hyb : ∀ t k, |y t k| ≤ Kz + Fintype.card X * (aG * Xb) + Xb := by
    intro t k
    have hGx : ∀ i, |(G *ᵥ x t) i| ≤ Fintype.card X * (aG * Xb) := fun i =>
      abs_mulVec_le G (x t) (abs_entry_le_sum G) (hxb t) i
    rcases k with i | j
    · simp only [hy, Sum.elim_inl, Pi.add_apply]
      have := (abs_add_le _ _).trans (add_le_add (hzb t i) (hGx i))
      linarith
    · simp only [hy, Sum.elim_inr]
      have : 0 ≤ Kz + Fintype.card X * (aG * Xb) := by positivity
      linarith [hxb t j]
  have hmem := mem_boundedOrbits_of_orbit hystep hyb
  have h0 : y 0 = 0 := hg _ hmem (fun j => by simp [hy, hx, xrecV])
  funext i
  have := congrFun h0 (Sum.inl i)
  simpa [hy, hx, xrecV] using this

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): under genericity, every eigenvalue of
`C = A_zz − G A_xz` lies outside the closed unit disc (given that `Λ` is stable). For an
eigenvalue `|μ| ≤ 1` with eigenvector `c`, the real and imaginary parts of `μᵗ c` are bounded
solutions of `ẑ_{t+1} = C ẑ_t`, so `c = 0` by `zero_of_cmat_orbit`. -/
theorem cmat_unstable {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (hg : GenericX A) (hΛ : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1) :
    ∀ μ ∈ eigs (cmat A G), 1 < ‖μ‖ := by
  intro μ hμ
  by_contra hle
  push Not at hle
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hL⟩ := pow_entry_bound (lam A G) hΛ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  set K : ℝ := ∑ i, ‖c i‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hstep : ∀ t i, μ ^ (t + 1) * c i =
      ((cmat A G).map Complex.ofReal *ᵥ fun j => μ ^ t * c j) i := by
    intro t i
    have : (cmat A G).map Complex.ofReal *ᵥ (fun j => μ ^ t * c j) = μ ^ (t + 1) • c := by
      have e : (fun j => μ ^ t * c j) = μ ^ t • c := rfl
      rw [e, Matrix.mulVec_smul, hc, smul_smul, pow_succ]
    rw [this]
    rfl
  have hbd : ∀ t i, ‖μ ^ t * c i‖ ≤ K := by
    intro t i
    rw [norm_mul, norm_pow]
    calc ‖μ‖ ^ t * ‖c i‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hle) (norm_nonneg _)
      _ ≤ K := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun i => ‖c i‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
  have hre := zero_of_cmat_orbit hG hg hCb hρ0.le hρ1 hL
    (zh := fun t i => (μ ^ t * c i).re)
    (fun t => by
      funext i
      rw [hstep t i]
      exact re_mulVec _ _ i) hK0
    (fun t i => (Complex.abs_re_le_norm _).trans (hbd t i))
  have him := zero_of_cmat_orbit hG hg hCb hρ0.le hρ1 hL
    (zh := fun t i => (μ ^ t * c i).im)
    (fun t => by
      funext i
      rw [hstep t i]
      exact im_mulVec _ _ i) hK0
    (fun t i => (Complex.abs_im_le_norm _).trans (hbd t i))
  apply hc0
  funext i
  have h1 := congrFun hre i
  have h2 := congrFun him i
  simp only [pow_zero, one_mul, Pi.zero_apply] at h1 h2
  exact Complex.ext h1 h2

/-- **The eigenvalue count** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)): if
the graph's `Λ` is stable and `C` is unstable, exactly `|X|` eigenvalues of `A` (with
multiplicity) lie in the open unit disc. -/
theorem stableCount_eq_card {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G)
    (hΛ : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1) (hC : ∀ μ ∈ eigs (cmat A G), 1 < ‖μ‖) :
    stableCount A = Fintype.card X := by
  rw [stableCount, eigs_split hinv, Multiset.filter_add, Multiset.card_add,
    Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hC μ hμ).le),
    Multiset.filter_eq_self.mpr hΛ, Multiset.card_zero, zero_add, card_eigs]

/-- Woodford (2003), App. C.1, p. 672: genericity bounds the dimension of the bounded-orbit
subspace by the number of predetermined variables. -/
theorem finrank_le_of_genericX {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hg : GenericX A) :
    Module.finrank ℝ (boundedOrbits A) ≤ Fintype.card X := by
  set f := (projX (Z := Z) (X := X)).domRestrict (boundedOrbits A) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hg v v.2 (fun j => congrFun hv j))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at this

/-- Woodford (2003), App. C.1, p. 672, fn. 2: more bounded directions than predetermined
variables violate genericity. -/
theorem not_genericX_of_lt {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Fintype.card X < Module.finrank ℝ (boundedOrbits A)) : ¬ GenericX A :=
  fun hg => absurd (finrank_le_of_genericX hg) (not_le.mpr h)

/-- Woodford (2003), App. C.1, p. 672: fewer bounded directions than predetermined variables
leave some initial condition `x₀` not reached by any bounded orbit. -/
theorem exists_unreached_of_lt {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ∃ x0 : X → ℝ, ∀ v ∈ boundedOrbits A, (fun j => v (Sum.inr j)) ≠ x0 := by
  set f := (projX (Z := Z) (X := X)).domRestrict (boundedOrbits A) with hf
  have hr : LinearMap.range f ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_le f
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    exact absurd h1 (not_le.mpr h)
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∉ LinearMap.range f := by
    by_contra hall
    push Not at hall
    exact hr (eq_top_iff.mpr fun x _ => hall x)
  refine ⟨x0, fun v hv he => hx0 ⟨⟨v, hv⟩, ?_⟩⟩
  rw [← he]
  rfl

/-- **The two forms of the counting condition** (Woodford (2003), App. C.1, p. 672; Blanchard and
Kahn (1980)): with no eigenvalue on the unit circle and genericity, the stable subspace has
dimension `|X|` iff exactly `|X|` eigenvalues (with multiplicity) lie in the open unit disc. -/
theorem finrank_eq_iff_stableCount_eq {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hg : GenericX A) :
    Module.finrank ℝ (boundedOrbits A) = Fintype.card X ↔ stableCount A = Fintype.card X := by
  constructor
  · intro hd
    obtain ⟨G, hG⟩ := exists_graph hd hg
    have hΛ := lam_stable hG hnu
    exact stableCount_eq_card (graph_invariant hG) hΛ (cmat_unstable hG hg hΛ)
  · intro hc
    exact le_antisymm (finrank_le_of_genericX hg) (hc ▸ stableCount_le_finrank A)

end Gali.MonetaryPolicyDesign.InvariantSplit

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Forward systems over an arbitrary finite index type

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670, fn. 1 (Blanchard and Kahn 1980).
Vector processes of random variables indexed by any finite type, and the forward system
`s_t = K E_t s_{t+1} + w_t`: if the powers of `K` decay geometrically it has exactly one bounded
adapted solution for every bounded adapted forcing, the forward series
`s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` (`fsolves_exists`, `fsolves_unique`).

Restated from `BlanchardKahn` (`rvMul`, `FSolves`, `fsolves_iterate`, `fsolves_unique`,
`fsolves_exists`, which restated them from the Galí Chapter 6 project), generalised from `Fin n`
to any finite index type.

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.GeneralBKForward`,
namespace renamed; this project does not import across projects). Used here for Galí (2015),
Ex. 4.4(c), p. 123 (`Ex4_4Determinacy`).
-/

namespace Gali.MonetaryPolicyDesign.GeneralBKForward

open Filter Topology
open scoped Matrix

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix acting on a vector of random variables,
`(M a)_i = ∑_j M_{ij} a_j`. -/
def mv {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) : m → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise. -/
theorem mv_apply {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = (M *ᵥ fun j => a j ω) i := by
  simp [mv, Finset.sum_apply, Matrix.mulVec, dotProduct]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise, as a sum. -/
theorem mv_apply_sum {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = ∑ j, M i j * a j ω := by
  simp [mv, Finset.sum_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): compatibility with matrix multiplication. -/
theorem mv_mv {Ω m n l : Type*} [Fintype n] [Fintype l] (M : Matrix m n ℝ) (N : Matrix n l ℝ)
    (a : l → Ω → ℝ) : mv M (mv N a) = mv (M * N) a := by
  funext i
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford (2003), App. C.1, p. 670 (tool): additivity of the action. -/
theorem mv_add {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a + b) = mv M a + mv M b := by
  funext i
  simp only [mv, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects subtraction. -/
theorem mv_sub {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a - b) = mv M a - mv M b := by
  funext i
  simp only [mv, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a sum of matrices. -/
theorem add_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M + N) a = mv M a + mv N a := by
  funext i
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a difference of matrices. -/
theorem sub_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M - N) a = mv M a - mv N a := by
  funext i
  simp only [mv, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.sub_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the identity matrix acts trivially. -/
theorem mv_one {Ω n : Type*} [Fintype n] [DecidableEq n] (a : n → Ω → ℝ) :
    mv (1 : Matrix n n ℝ) a = a := by
  funext i
  simp [mv, Matrix.one_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action on the zero vector. -/
theorem mv_zero {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) :
    mv M (0 : n → Ω → ℝ) = 0 := by
  funext i
  simp [mv]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects negation. -/
theorem mv_neg {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv M (-a) = -mv M a := by
  funext i
  simp [mv, Finset.sum_neg_distrib]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. C.1, p. 670 (tool): `E_t` commutes with constant matrices. -/
theorem E_mv {m n : Type*} [Fintype n] (t : ℕ) (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m) :
    𝔼.E t (mv M a i) = mv M (fun j => 𝔼.E t (a j)) i := by
  simp only [mv, map_sum, map_smul]

/-- Woodford (2003), App. C.1, p. 670: a vector process is adapted. -/
def AdaptedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford (2003), App. C.1, p. 670: a vector process is bounded. -/
def BoundedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford (2003), App. C.1, p. 670: `s` solves the forward system
`s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (w s : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t, s t = mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps a bounded vector process to
a bounded one. -/
theorem boundedV_mv {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n ℝ)
    {a : ℕ → n → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => mv M (a t)) := by
  have := Fintype.ofFinite m
  obtain ⟨B, hB⟩ := ha
  refine ⟨Fintype.card n * ((∑ i, ∑ j, |M i j|) * max B 0), fun t i ω => ?_⟩
  change |mv M (a t) i ω| ≤ _
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ (InvariantSplit.abs_entry_le_sum M)
    (fun j => (hB t j ω).trans (le_max_left _ _)) i |>.trans (le_of_eq (by ring))

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps an adapted vector process
to an adapted one. -/
theorem adaptedV_mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {a : ℕ → n → Ω → ℝ}
    (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => mv M (a t)) := by
  intro t i
  change 𝔼.E t (mv M (a t) i) = mv M (a t) i
  rw [E_mv 𝔼]
  congr 1
  funext j
  exact ha t j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. C.1, p. 670: iterating a homogeneous forward system,
`d_t = Kᵏ E_t d_{t+k}`. -/
theorem fsolves_iterate {K : Matrix ι ι ℝ} {d : ℕ → ι → Ω → ℝ} (hd : FSolves 𝔼 K 0 d)
    (had : AdaptedV 𝔼 d) (t k : ℕ) : d t = mv (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, mv_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) = mv K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_mv 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, mv_mv, ← pow_succ]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_mv_le {M : Matrix ι ι ℝ} {c : ℝ} (hM : ∀ i j, |M i j| ≤ c) {a : ι → Ω → ℝ}
    {B : ℝ} (ha : ∀ j ω, |a j ω| ≤ B) (i : ι) (ω : Ω) :
    |mv M a i ω| ≤ Fintype.card ι * (c * B) := by
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ hM (fun j => ha j ω) i

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted solution. -/
theorem fsolves_unique {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → ι → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : AdaptedV 𝔼 x) (hay : AdaptedV 𝔼 y)
    (hbx : BoundedV x) (hby : BoundedV y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → ι → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, mv, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : AdaptedV 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ Fintype.card ι * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (Fintype.card ι : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop
        (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (Fintype.card ι : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, the forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution
of `s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w : ℕ → ι → Ω → ℝ} {Mw : ℝ}
    (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : AdaptedV 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ AdaptedV 𝔼 s ∧ BoundedV s := by
  set Mb : ℝ := Fintype.card ι * Cb * Mw with hMb
  set B : ℕ → ℕ → ι → Ω → ℝ := fun k t => mv (K ^ k) (fun j => 𝔼.E t (w (t + k) j)) with hB
  have hT : ∀ k t t' i ω, |mv (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ Fintype.card ι * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => mv (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → ι → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_mv 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, mv_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← mv_apply_sum, mv_mv, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, mv_apply_sum]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ =>
        (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_mv 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

end Gali.MonetaryPolicyDesign.GeneralBKForward

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The general Blanchard–Kahn theorem

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (Props. C.1, C.2 and footnotes
1–2), which *assumes* the counting rule of Blanchard and Kahn (1980). This module proves the
general rule, for any number of predetermined and non-predetermined variables and any
`ExpectationSystem` (perfect foresight and genuine uncertainty alike), with existence and
uniqueness among bounded adapted processes.

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.GeneralBK`, namespace
renamed; this project does not import across projects). Used here for Galí (2015), Ex. 4.4(c),
p. 123 (`Ex4_4Determinacy`).

## Setting

The state is `y_t = (z_t, x_t)` with index type `Z ⊕ X`: `z_t` non-predetermined, `x_t`
predetermined. `E_t y_{t+1} = A y_t + w_t` (`Solves`) for a real matrix `A`; an equilibrium
(`Equil`) is a bounded adapted solution whose predetermined block `x_{t+1}` is known at date `t`
and starts at the given `x_0`. `Determinate`: for every bounded adapted forcing `w` and every
`x_0` there is exactly one equilibrium.

## Main results

* `determinate_of` (**sufficiency**, any `ExpectationSystem`): no eigenvalue of `A` on the unit
  circle (`NoUnit`), the bounded-orbit (stable) subspace of dimension `|X|`, and genericity
  (`GenericX`: the stable subspace meets `{x = 0}` only in `0`) imply determinacy. Proof: the
  stable subspace is the graph of `G` (`InvariantSplit.exists_graph`); `ẑ_t = z_t − G x_t` solves
  `E_t ẑ_{t+1} = C ẑ_t + ŵ_t` with all eigenvalues of `C` outside the closed disc, so it is the
  forward solution through `C⁻¹`; then `x_{t+1} = Λ x_t + A_xz ẑ_t + w^x_t` with `Λ` stable is
  solved backward from `x_0`.
* Necessity, for every `ExpectationSystem` on a nonempty state space, failure by failure:
  - an eigenvalue on the unit circle gives **non-existence** by resonance: a bounded
    deterministic forcing `w_t = Re(μ^{t+1} b)` admits no bounded solution at all
    (`nonexist_of_unit`);
  - a failure of genericity gives **non-uniqueness**: next to every equilibrium there is another
    one, obtained by adding a bounded orbit with `x_0 = 0` (`mult_of_not_genericX`); this
    covers a stable subspace of dimension larger than `|X|` (`InvariantSplit.not_genericX_of_lt`);
  - a stable subspace of dimension smaller than `|X|` gives **non-existence** for some `x_0`
    already with `w = 0` (`nonexist_of_lt`).
* `determinate_iff` (**the Blanchard–Kahn theorem**): `Determinate ↔ NoUnit ∧ dim = |X| ∧ GenericX`;
  `determinate_iff_count`: the same with the dimension replaced by the number of eigenvalues in
  the open unit disc counted with algebraic multiplicity (`stableCount A = |X|`);
  `determinate_iff_unstableCount`: equivalently `|Z|` eigenvalues outside the closed disc.
* `determinate_iff_perfectForesight`: determinacy does not depend on the expectation system.
* `mem_boundedOrbits_iff_tendsto_of_noUnit`: with no eigenvalue on the unit circle the
  bounded-orbit subspace is the stable invariant subspace `{v : Aᵗ v → 0}`, and its dimension is
  the number of stable eigenvalues (`InvariantSplit.finrank_eq_stableCount`), so (ii) can be read
  either way.
-/

namespace Gali.MonetaryPolicyDesign.GeneralBK

open Filter Topology InvariantSplit GeneralBKForward
open scoped Matrix

/-! ### Small tools -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a complexified real vector under a complexified
real matrix. -/
theorem map_ofReal_mulVec {m n : Type*} [Fintype n] (K : Matrix m n ℝ) (v : n → ℝ) :
    K.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((K *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Complex.ofReal_sum]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix with all eigenvalues outside the closed
unit disc is invertible. -/
theorem det_ne_zero_of_unstable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : K.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have h0 : (0 : ℂ) ∈ eigs K := by
    refine mem_eigs_of_eigvec (c := fun i => (v i : ℂ)) ?_ ?_
    · intro hc
      apply hv0
      funext i
      have := congrFun hc i
      simpa using this
    · rw [map_ofReal_mulVec, hv]
      funext i
      simp
  have := h 0 h0
  norm_num at this

/-- Woodford (2003), App. C.1, p. 670 (tool): if every eigenvalue of `K` lies outside the closed
unit disc, every eigenvalue of `K⁻¹` lies in the open disc. -/
theorem inv_stable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : ∀ μ ∈ eigs K⁻¹, ‖μ‖ < 1 := by
  have hdet := det_ne_zero_of_unstable h
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet)
  intro μ hμ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  have hmap : K.map Complex.ofReal * K⁻¹.map Complex.ofReal = 1 := by
    have e : (K * K⁻¹).map Complex.ofReal = K.map Complex.ofReal * K⁻¹.map Complex.ofReal :=
      Matrix.map_mul (f := Complex.ofRealHom)
    rw [← e, hKK]
    exact Matrix.map_one _ (by simp) (by simp)
  have hc' : μ • (K.map Complex.ofReal *ᵥ c) = c := by
    calc μ • (K.map Complex.ofReal *ᵥ c) = K.map Complex.ofReal *ᵥ (μ • c) :=
          (Matrix.mulVec_smul _ _ _).symm
      _ = (K.map Complex.ofReal * K⁻¹.map Complex.ofReal) *ᵥ c := by
          rw [← hc, Matrix.mulVec_mulVec]
      _ = c := by rw [hmap, Matrix.one_mulVec]
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hc', h0, zero_smul]
  have hev : K.map Complex.ofReal *ᵥ c = μ⁻¹ • c := (eq_inv_smul_iff₀ hμ0).mpr hc'
  have h1 := h μ⁻¹ (mem_eigs_of_eigvec hc0 hev)
  rw [norm_inv] at h1
  exact (one_lt_inv₀ (norm_pos_iff.mpr hμ0)).mp h1

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of bounded vector processes are bounded. -/
theorem boundedV_add {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t + b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_add_le _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of bounded vector processes are
bounded. -/
theorem boundedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t - b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_sub _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of bounded vector processes are
bounded. -/
theorem boundedV_neg {a : ℕ → κ → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => -a t) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun t i ω => by simpa using hA t i ω⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of adapted vector processes are adapted. -/
theorem adaptedV_add {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t + b t) := fun t i => by
  simp only [Pi.add_apply, map_add, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of adapted vector processes are
adapted. -/
theorem adaptedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t - b t) := fun t i => by
  simp only [Pi.sub_apply, map_sub, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of adapted vector processes are
adapted. -/
theorem adaptedV_neg {a : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => -a t) :=
  fun t i => by simp only [Pi.neg_apply, map_neg, ha t i]

/-! ### The system -/

/-- Woodford (2003), (C.19) and App. C.1, p. 670: `y` solves `E_t y_{t+1} = A y_t + w_t`. -/
def Solves {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w y : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (y (t + 1) i) = mv A (y t) i + w t i

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, pp. 670–672 (Blanchard and Kahn 1980): a (bounded) rational
expectations equilibrium of `E_t y_{t+1} = A y_t + w_t` with state `y = (z, x)`: `y` solves the
system, is adapted and bounded, the predetermined block `x_{t+1}` is known at date `t`, and
`x_0` is the given vector. -/
def Equil (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  Solves 𝔼 A w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = fun _ => x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670 (determinacy, Blanchard and Kahn 1980): for every bounded
adapted forcing and every initial value of the predetermined variables there is exactly one
bounded equilibrium. -/
def Determinate (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → ℝ, ∃! y, Equil 𝔼 A w x0 y

omit [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670 (tool): a random state vector at a fixed outcome, split
into its blocks. -/
theorem eval_split (y : Z ⊕ X → Ω → ℝ) (ω : Ω) :
    (fun k => y k ω) = Sum.elim (fun i => y (Sum.inl i) ω) (fun j => y (Sum.inr j) ω) := by
  funext k
  rcases k with i | j <;> rfl

/-! ### Identities behind the change of variables `ẑ = z − G x` -/

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the non-predetermined block,
`(A y)_z = A_zz z + A_zx x`. -/
theorem mv_inl (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun i => mv A y (Sum.inl i)) =
      mv A.toBlocks₁₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₁₂ (fun j => y (Sum.inr j)) := by
  funext i
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the predetermined block,
`(A y)_x = A_xz z + A_xx x`. -/
theorem mv_inr (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun j => mv A y (Sum.inr j)) =
      mv A.toBlocks₂₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₂₂ (fun j => y (Sum.inr j)) := by
  funext j
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the invariance of the graph solved for `A_zx`:
`A_zx = G A_xz G + G A_xx − A_zz G`. -/
theorem zx_block_eq {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    A.toBlocks₁₂ = G * A.toBlocks₂₁ * G + G * A.toBlocks₂₂ - A.toBlocks₁₁ * G := by
  rw [eq_sub_iff_add_eq, add_comm, hinv, lam, Matrix.mul_add, Matrix.mul_assoc]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (uniqueness step): for random `(z, x)`,
`A_zz z + A_zx x + w^z − G (A_xz z + A_xx x + w^x) = C (z − G x) + (w^z − G w^x)`. -/
theorem identity_zhat {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (z wz : Z → Ω → ℝ)
    (x wx : X → Ω → ℝ) :
    mv A.toBlocks₁₁ z + mv A.toBlocks₁₂ x + wz -
        mv G (mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x + wx) =
      mv (cmat A G) (z - mv G x) + (wz - mv G wx) := by
  rw [zx_block_eq hinv, cmat]
  simp only [add_mv, sub_mv, mv_add, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (the predetermined block):
`A_xz z + A_xx x = A_xz (z − G x) + Λ x`. -/
theorem identity_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (z : Z → Ω → ℝ)
    (x : X → Ω → ℝ) :
    mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x = mv A.toBlocks₂₁ (z - mv G x) + mv (lam A G) x := by
  rw [lam]
  simp only [add_mv, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step): with `z = ẑ + G x`,
`C ẑ + (w^z − G w^x) + G (Λ x + (A_xz ẑ + w^x)) = A_zz z + A_zx x + w^z`. -/
theorem identity_exist {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (a wz : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (cmat A G) a + (wz - mv G c) + mv G (mv (lam A G) b + (mv A.toBlocks₂₁ a + c)) =
      mv A.toBlocks₁₁ (a + mv G b) + mv A.toBlocks₁₂ b + wz := by
  rw [zx_block_eq hinv, cmat, lam]
  simp only [add_mv, sub_mv, mv_add, ← mv_mv]
  abel_nf

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step, predetermined block):
`Λ x + (A_xz ẑ + w^x) = A_xz (ẑ + G x) + A_xx x + w^x`. -/
theorem identity_exist_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (a : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (lam A G) b + (mv A.toBlocks₂₁ a + c) =
      mv A.toBlocks₂₁ (a + mv G b) + mv A.toBlocks₂₂ b + c := by
  rw [lam]
  simp only [add_mv, mv_add, ← mv_mv]
  abel

/-! ### The backward recursion for the predetermined block -/

/-- Woodford (2003), App. C.1, p. 672: the predetermined block `x_{t+1} = Λ x_t + g_t`,
`x_0` given, as a process of random variables. -/
def xrecR (L : Matrix X X ℝ) (g : ℕ → X → Ω → ℝ) (x0 : X → ℝ) : ℕ → X → Ω → ℝ
  | 0 => fun j _ => x0 j
  | t + 1 => mv L (xrecR L g x0 t) + g t

omit [DecidableEq Z] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is bounded when `Λ` is stable and
`g` is bounded. -/
theorem xrecR_bounded {L : Matrix X X ℝ} (hL : ∀ μ ∈ eigs L, ‖μ‖ < 1) {g : ℕ → X → Ω → ℝ}
    (hg : BoundedV g) (x0 : X → ℝ) : BoundedV (xrecR L g x0) := by
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hLp⟩ := pow_entry_bound L hL
  obtain ⟨F, hF⟩ := hg
  refine ⟨Fintype.card X * Cb * (∑ j, |x0 j| + max F 0 / (1 - ρ)), fun t j ω => ?_⟩
  have hrec : ∀ t, (fun j => xrecR L g x0 (t + 1) j ω) =
      L *ᵥ (fun j => xrecR L g x0 t j ω) + fun j => g t j ω := by
    intro t
    funext j
    simp only [xrecR, Pi.add_apply, mv_apply]
  exact rec_bounded (x := fun t j => xrecR L g x0 t j ω) (f := fun t j => g t j ω) hCb hρ0.le
    hρ1 hLp hrec (le_max_right _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun t j => (hF t j ω).trans (le_max_left _ _))
    (fun j => Finset.single_le_sum (f := fun j => |x0 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)) t j

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is known one period ahead:
`x_t` is known at `t` and so is `x_{t+1}` (when `g` is adapted). -/
theorem xrecR_known {L : Matrix X X ℝ} {g : ℕ → X → Ω → ℝ} (hg : AdaptedV 𝔼 g) (x0 : X → ℝ) :
    ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j ∧
      𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
  have hnext : ∀ t, (∀ j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j) →
      ∀ j, 𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
    intro t ht j
    simp only [xrecR, Pi.add_apply, map_add, E_mv 𝔼, hg t j]
    congr 2
    funext k
    exact ht k
  have hcur : ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j := by
    intro t
    induction t with
    | zero => intro j; exact 𝔼.const 0 (x0 j)
    | succ t ih =>
      intro j
      rw [← hnext t ih j, 𝔼.known (Nat.le_succ t)]
  exact fun t j => ⟨hcur t j, hnext t (hcur t) j⟩

/-! ### Sufficiency -/

/-- Woodford (2003), App. C.1, p. 672 (tool): with `K C = C K = 1`, the forward form
`ẑ_t = K E_t ẑ_{t+1} − K ŵ_t` is the system `E_t ẑ_{t+1} = C ẑ_t + ŵ_t`. -/
theorem fsolves_iff_cform {C K : Matrix Z Z ℝ} (hKC : K * C = 1) (hCK : C * K = 1)
    (wh zh : ℕ → Z → Ω → ℝ) :
    FSolves 𝔼 K (fun t => -mv K (wh t)) zh ↔
      ∀ t, (fun i => 𝔼.E t (zh (t + 1) i)) = mv C (zh t) + wh t := by
  constructor
  · intro h t
    have e := congrArg (mv C) (h t)
    rw [mv_add, mv_neg, mv_mv, mv_mv, hCK, mv_one, mv_one] at e
    rw [e]
    abel
  · intro h t
    simp only [h t, mv_add, mv_mv, hKC, mv_one, add_neg_cancel_right]

/-- **Blanchard–Kahn, sufficiency** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn 1980):
for any expectation system, if no eigenvalue of `A` lies on the unit circle, the stable
(bounded-orbit) subspace has dimension equal to the number of predetermined variables, and it
meets `{x = 0}` only in `0`, then for every bounded adapted forcing and every `x_0` there is
exactly one bounded equilibrium. -/
theorem determinate_of {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A) :
    Determinate 𝔼 A := by
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  have hΛ := lam_stable hG hnu
  have hC := cmat_unstable hG hg hΛ
  have hdet : IsUnit (cmat A G).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_unstable hC)
  have hKC : (cmat A G)⁻¹ * cmat A G = 1 := Matrix.nonsing_inv_mul _ hdet
  have hCK : cmat A G * (cmat A G)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  obtain ⟨CbK, ρK, -, hρK0, hρK1, hKpow⟩ := pow_entry_bound _ (inv_stable hC)
  intro w hwb hwa x0
  set wz : ℕ → Z → Ω → ℝ := fun t i => w t (Sum.inl i) with hwz
  set wx : ℕ → X → Ω → ℝ := fun t j => w t (Sum.inr j) with hwx
  have hwzb : BoundedV wz := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t i ω => hM t _ ω⟩
  have hwxb : BoundedV wx := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t j ω => hM t _ ω⟩
  have hwzA : AdaptedV 𝔼 wz := fun t i => hwa t (Sum.inl i)
  have hwxA : AdaptedV 𝔼 wx := fun t j => hwa t (Sum.inr j)
  set wh : ℕ → Z → Ω → ℝ := fun t => wz t - mv G (wx t) with hwh
  have hwhb : BoundedV wh := boundedV_sub hwzb (boundedV_mv G hwxb)
  have hwhA : AdaptedV 𝔼 wh := adaptedV_sub 𝔼 hwzA (adaptedV_mv 𝔼 G hwxA)
  have hfb : BoundedV (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    boundedV_neg (boundedV_mv _ hwhb)
  have hfA : AdaptedV 𝔼 (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    adaptedV_neg 𝔼 (adaptedV_mv 𝔼 _ hwhA)
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨zh, hzh, hzhA, hzhb⟩ := fsolves_exists 𝔼 hρK0.le hρK1 hKpow hMf hfA
  have hzhE := (fsolves_iff_cform 𝔼 hKC hCK wh zh).mp hzh
  set g : ℕ → X → Ω → ℝ := fun t => mv A.toBlocks₂₁ (zh t) + wx t with hgdef
  have hgA : AdaptedV 𝔼 g := adaptedV_add 𝔼 (adaptedV_mv 𝔼 _ hzhA) hwxA
  have hgb : BoundedV g := boundedV_add (boundedV_mv _ hzhb) hwxb
  set xr := xrecR (lam A G) g x0 with hxr
  have hxrb : BoundedV xr := xrecR_bounded hΛ hgb x0
  have hxrK := xrecR_known 𝔼 (L := lam A G) hgA x0
  have hxr1 : ∀ t, xr (t + 1) = mv (lam A G) (xr t) + g t := fun t => rfl
  set y : ℕ → Z ⊕ X → Ω → ℝ := fun t => Sum.elim (zh t + mv G (xr t)) (xr t) with hy
  have hyz : ∀ t, (fun i => y t (Sum.inl i)) = zh t + mv G (xr t) := fun t => rfl
  have hyx : ∀ t, (fun j => y t (Sum.inr j)) = xr t := fun t => rfl
  -- every equilibrium is `y`
  have huniq : ∀ y', Equil 𝔼 A w x0 y' → y' = y := by
    rintro y' ⟨hs, ha, hk, h0, hb⟩
    set zh' : ℕ → Z → Ω → ℝ :=
      fun t => (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) with hzh'
    have hzh'A : AdaptedV 𝔼 zh' :=
      adaptedV_sub 𝔼 (fun t i => ha t (Sum.inl i))
        (adaptedV_mv 𝔼 G (fun t j => ha t (Sum.inr j)))
    have hb1 : BoundedV (fun t i => y' t (Sum.inl i)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t i ω => hM t _ ω⟩
    have hb2 : BoundedV (fun t j => y' t (Sum.inr j)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t j ω => hM t _ ω⟩
    have hzh'b : BoundedV zh' := boundedV_sub hb1 (boundedV_mv G hb2)
    have hEz : ∀ t, (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) =
        (fun i => mv A (y' t) (Sum.inl i)) + wz t := fun t => by
      funext i; rw [hs t]; rfl
    have hEx : ∀ t, (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) =
        (fun j => mv A (y' t) (Sum.inr j)) + wx t := fun t => by
      funext j; rw [hs t]; rfl
    have hcf : ∀ t, (fun i => 𝔼.E t (zh' (t + 1) i)) = mv (cmat A G) (zh' t) + wh t := by
      intro t
      have hE : (fun i => 𝔼.E t (zh' (t + 1) i)) =
          (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) -
            mv G (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
        funext i
        simp only [hzh', Pi.sub_apply, map_sub, E_mv 𝔼]
      rw [hE, hEz, hEx, mv_inl, mv_inr, identity_zhat hinv]
    have hzz : zh' = zh :=
      fsolves_unique 𝔼 hρK0.le hρK1 hKpow ((fsolves_iff_cform 𝔼 hKC hCK wh zh').mpr hcf) hzh
        hzh'A hzhA hzh'b ⟨_, hzhb.choose_spec⟩
    have hxx : ∀ t, (fun j => y' t (Sum.inr j)) = xr t := by
      intro t
      induction t with
      | zero => funext j; exact h0 j
      | succ t ih =>
        have e1 : (fun j => y' (t + 1) (Sum.inr j)) =
            (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
          funext j; exact (hk t j).symm
        have hz't : (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) = zh' t := rfl
        rw [e1, hEx, mv_inr, identity_x A G, hz't, hzz, ih, hxr1]
        simp only [hgdef]
        abel
    funext t k
    rcases k with i | j
    · have e := congrFun (congrArg (fun f => f t) hzz) i
      simp only [hzh', Pi.sub_apply, hxx t] at e
      have e2 : y' t (Sum.inl i) = zh t i + mv G (xr t) i := by
        rw [← e]; abel
      rw [e2]
      rfl
    · exact congrFun (hxx t) j
  refine ⟨y, ⟨?_, ?_, ?_, ?_, ?_⟩, huniq⟩
  · -- the system
    intro t k
    rcases k with i | j
    · have hv : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
          (fun i => mv A (y t) (Sum.inl i)) + wz t := by
        have e1 : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
            (fun i => 𝔼.E t (zh (t + 1) i)) + mv G (fun j => 𝔼.E t (xr (t + 1) j)) := by
          funext i
          simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼]
        have e2 : (fun j => 𝔼.E t (xr (t + 1) j)) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, e2, hzhE t, hxr1, mv_inl, hyz, hyx, hwh, hgdef]
        exact identity_exist hinv _ _ _ _
      exact congrFun hv i
    · have hv : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) =
          (fun j => mv A (y t) (Sum.inr j)) + wx t := by
        have e1 : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, hxr1, mv_inr, hyz, hyx, hgdef]
        exact identity_exist_x A G _ _ _
      exact congrFun hv j
  · -- adapted
    intro t k
    rcases k with i | j
    · simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼, hzhA t i]
      congr 2
      funext j
      exact (hxrK t j).1
    · exact (hxrK t j).1
  · -- the predetermined block is known one period ahead
    intro t j
    exact (hxrK t j).2
  · -- the initial condition
    intro j
    rfl
  · -- boundedness
    obtain ⟨Mz, hMz⟩ := hzhb
    obtain ⟨Mx, hMx⟩ := hxrb
    obtain ⟨Mg, hMg⟩ := boundedV_mv G ⟨Mx, hMx⟩
    refine ⟨max (Mz + Mg) Mx, fun t k ω => ?_⟩
    rcases k with i | j
    · change |zh t i ω + mv G (xr t) i ω| ≤ _
      exact ((abs_add_le _ _).trans (add_le_add (hMz t i ω) (hMg t i ω))).trans
        (le_max_left _ _)
    · exact (hMx t j ω).trans (le_max_right _ _)

/-! ### Necessity (i): an eigenvalue on the unit circle gives non-existence by resonance -/

open ComplexConjugate

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): for a left eigenvector `q A = μ q`,
`q · (A e) = μ (q · e)`. -/
theorem sum_q_mulVec {A : Matrix κ κ ℝ} {μ : ℂ} {q : κ → ℂ}
    (hq : q ᵥ* A.map Complex.ofReal = μ • q) (e : κ → ℝ) :
    ∑ i, q i * ((A *ᵥ e) i : ℂ) = μ * ∑ j, q j * (e j : ℂ) := by
  have hcol : ∀ j, ∑ i, q i * (A i j : ℂ) = μ * q j := fun j => by
    have := congrFun hq j
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hcol j, mul_assoc]

/-- Woodford (2003), App. C.1, p. 670 (tool): a linear lower bound `a + T c − K` with `c > 0`
cannot stay below a constant. -/
theorem false_of_linear_growth {a c K Q : ℝ} (hc : 0 < c) (h : ∀ T : ℕ, a + T * c - K ≤ Q) :
    False := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((Q + K - a) / c)
  have := h T
  rw [div_lt_iff₀ hc] at hT
  linarith

omit [DecidableEq κ] in
/-- **Resonance** (Woodford (2003), App. C.1, p. 670, fn. 1: the boundary case): let `‖μ‖ = 1`
and `q A = μ q`, `q ≠ 0` (with `q` real when `μ = ±1`). Then the deterministic system
`e_{t+1} = A e_t + w_t` with the bounded forcing `w_{t,i} = Re(μ^{t+1} q̄_i)` has no bounded
solution: `d_t = (q · e_t) μ̄ᵗ` grows like `t ∑|q_i|²/2`. -/
theorem no_bounded_resonance {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1) {q : κ → ℂ}
    (hq0 : q ≠ 0) (hq : q ᵥ* A.map Complex.ofReal = μ • q)
    (hre : μ ^ 2 = 1 → ∀ i, (q i).im = 0) {e : ℕ → κ → ℝ}
    (he : ∀ t, e (t + 1) = A *ᵥ e t + fun i => (μ ^ (t + 1) * conj (q i)).re)
    {B : ℝ} (hB : ∀ t i, |e t i| ≤ B) : False := by
  set m : ℕ → ℂ := fun t => ∑ i, q i * (e t i : ℂ) with hm
  set N : ℝ := ∑ i, ‖q i‖ ^ 2 with hN
  set σ : ℂ := ∑ i, q i ^ 2 with hσ
  set ζ : ℂ := conj μ ^ 2 with hζ
  have hμc : μ * conj μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
    norm_num
  have hN0 : 0 < N := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hq0 (funext hne)
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨i, Finset.mem_univ i, by have := norm_pos_iff.mpr hi; positivity⟩
  have hNc : (N : ℂ) = ∑ i, q i * conj (q i) := by
    rw [hN]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hqw : ∀ t, ∑ i, q i * (((μ ^ (t + 1) * conj (q i)).re : ℝ) : ℂ) =
      (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    rw [hNc, hσ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_eq_add_conj, map_mul, map_pow, Complex.conj_conj]
    ring
  have hm_succ : ∀ t, m (t + 1) = μ * m t + (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    simp only [hm, he t, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
    rw [sum_q_mulVec hq, hqw]
  set d : ℕ → ℂ := fun t => m t * conj μ ^ t with hd
  have hd_succ : ∀ t, d (t + 1) = d t + ((N : ℂ) + σ * ζ ^ (t + 1)) / 2 := by
    intro t
    have h1 : μ ^ (t + 1) * conj μ ^ (t + 1) = 1 := by rw [← mul_pow, hμc, one_pow]
    have h2 : μ * conj μ ^ (t + 1) = conj μ ^ t := by
      rw [pow_succ]
      linear_combination (conj μ ^ t) * hμc
    have h3 : conj μ ^ (t + 1) * conj μ ^ (t + 1) = ζ ^ (t + 1) := by
      rw [hζ, ← pow_mul, ← pow_add]
      ring_nf
    simp only [hd]
    rw [hm_succ t]
    linear_combination (m t) * h2 + ((N : ℂ) / 2) * h1 + (σ / 2) * h3
  set S : ℕ → ℂ := fun T => ∑ s ∈ Finset.range T, ζ ^ (s + 1) with hS
  have hd_closed : ∀ T : ℕ, d T = d 0 + ((T * N / 2 : ℝ) : ℂ) + σ / 2 * S T := by
    intro T
    induction T with
    | zero => simp [hS]
    | succ T ih =>
      rw [hd_succ T, ih]
      simp only [hS, Finset.sum_range_succ]
      push_cast
      ring
  set Q : ℝ := ∑ i, ‖q i‖ * B with hQ
  have hdQ : ∀ T, ‖d T‖ ≤ Q := by
    intro T
    simp only [hd, hm, norm_mul, norm_pow, Complex.norm_conj, hμ, one_pow, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB T i) (norm_nonneg _)
  -- the oscillating part is bounded below
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ T, -K ≤ (σ / 2 * S T).re := by
    by_cases hζ1 : ζ = 1
    · have hμ2 : μ ^ 2 = 1 := by
        have := congrArg conj hζ1
        rw [hζ, map_pow, Complex.conj_conj, map_one] at this
        exact this
      have hreal := hre hμ2
      have hσN : σ = (N : ℂ) := by
        rw [hσ, hNc]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hqi : q i = ((q i).re : ℂ) := Complex.ext rfl (by simp [hreal i])
        rw [hqi, Complex.conj_ofReal]
        ring
      refine ⟨0, fun T => ?_⟩
      have hST : S T = (T : ℂ) := by simp [hS, hζ1]
      rw [hσN, hST]
      have : ((N : ℂ) / 2 * (T : ℂ)).re = N / 2 * T := by
        rw [show ((N : ℂ) / 2 * (T : ℂ)) = ((N / 2 * T : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      rw [this]
      have : 0 ≤ N / 2 * T := by positivity
      linarith
    · have hζn : ‖ζ‖ = 1 := by rw [hζ, norm_pow, Complex.norm_conj, hμ, one_pow]
      have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
      refine ⟨‖σ‖ / ‖ζ - 1‖, fun T => ?_⟩
      have hSb : ‖S T‖ ≤ 2 / ‖ζ - 1‖ := by
        have e : S T = ζ * ((ζ ^ T - 1) / (ζ - 1)) := by
          rw [hS, ← geom_sum_eq hζ1 T, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        rw [e, norm_mul, hζn, one_mul, norm_div]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖ζ ^ T - 1‖ ≤ ‖ζ ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
      have hb : ‖σ / 2 * S T‖ ≤ ‖σ‖ / ‖ζ - 1‖ := by
        rw [norm_mul, norm_div, Complex.norm_two]
        calc ‖σ‖ / 2 * ‖S T‖ ≤ ‖σ‖ / 2 * (2 / ‖ζ - 1‖) :=
              mul_le_mul_of_nonneg_left hSb (by positivity)
          _ = ‖σ‖ / ‖ζ - 1‖ := by ring
      have := Complex.abs_re_le_norm (σ / 2 * S T)
      have := neg_abs_le (σ / 2 * S T).re
      linarith
  refine false_of_linear_growth (a := (d 0).re) (c := N / 2) (K := K) (Q := Q)
    (by positivity) fun T => ?_
  have h1 : (d T).re = (d 0).re + T * N / 2 + (σ / 2 * S T).re := by
    rw [hd_closed T, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have h2 : (d T).re ≤ Q := (Complex.re_le_norm _).trans (hdQ T)
  have h3 := hK T
  have : (T : ℝ) * (N / 2) = T * N / 2 := by ring
  linarith

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue on the unit circle has a left
eigenvector, which can be chosen real when the eigenvalue is `±1`. -/
theorem exists_left_eigvec_unit {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A) :
    ∃ q : κ → ℂ, q ≠ 0 ∧ q ᵥ* A.map Complex.ofReal = μ • q ∧
      (μ ^ 2 = 1 → ∀ i, (q i).im = 0) := by
  by_cases h2 : μ ^ 2 = 1
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, μ = (r : ℂ) := by
      have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with e | e
      · exact ⟨1, by push_cast; linear_combination e⟩
      · exact ⟨-1, by push_cast; linear_combination e⟩
    have hdetC := (mem_eigs_iff A μ).mp hμ
    have hmap : Matrix.scalar κ μ - A.map Complex.ofReal =
        (Matrix.scalar κ r - A).map Complex.ofReal := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hr]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    have hdetR : (Matrix.scalar κ r - A).det = 0 := by
      have e := RingHom.map_det Complex.ofRealHom (Matrix.scalar κ r - A)
      rw [hmap] at hdetC
      have e2 : (Complex.ofRealHom.mapMatrix (Matrix.scalar κ r - A)) =
          (Matrix.scalar κ r - A).map Complex.ofReal := rfl
      rw [e2, hdetC] at e
      exact Complex.ofReal_eq_zero.mp e
    obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetR
    refine ⟨fun i => (p i : ℂ), ?_, ?_, fun _ i => by simp⟩
    · intro h
      apply hp0
      funext i
      have := congrFun h i
      simpa using this
    · rw [Matrix.vecMul_sub, sub_eq_zero] at hp
      funext j
      have hj := congrFun hp j
      have h1 : (p ᵥ* Matrix.scalar κ r) j = r * p j := by
        simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
      have e : ∑ i, p i * A i j = r * p j := by
        calc ∑ i, p i * A i j = (p ᵥ* A) j := rfl
          _ = r * p j := hj.symm.trans h1
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hr]
      exact_mod_cast e
  · obtain ⟨q, hq0, hq⟩ := exists_left_eigvec hμ
    exact ⟨q, hq0, hq, fun h => absurd h h2⟩

/-- **Non-existence at a unit-circle eigenvalue** (Woodford (2003), App. C.1, p. 670, fn. 1;
Blanchard and Kahn 1980): if `A` has an eigenvalue `μ` with `|μ| = 1`, there is a bounded
adapted (indeed deterministic) forcing, `w_{t,i} = Re(μ^{t+1} q̄_i)` for a left eigenvector `q`,
for which `E_t y_{t+1} = A y_t + w_t` has no bounded solution at all, adapted or not, whatever the
predetermined restrictions. Taking `E_0` of a solution reduces to `no_bounded_resonance`. -/
theorem nonexist_of_unit [Nonempty Ω] {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A)
    (h1 : ‖μ‖ = 1) :
    ∃ w : ℕ → κ → Ω → ℝ, BoundedV w ∧ AdaptedV 𝔼 w ∧
      ∀ y, Solves 𝔼 A w y → BoundedV y → False := by
  obtain ⟨q, hq0, hq, hre⟩ := exists_left_eigvec_unit hμ
  refine ⟨fun t i _ => (μ ^ (t + 1) * conj (q i)).re, ⟨∑ i, ‖q i‖, fun t i _ => ?_⟩,
    fun t i => 𝔼.const t _, ?_⟩
  · refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, h1, one_pow, one_mul, Complex.norm_conj]
    exact Finset.single_le_sum (f := fun i => ‖q i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  · rintro y hy ⟨B, hB⟩
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    refine no_bounded_resonance h1 hq0 hq hre (e := fun t i => 𝔼.E 0 (y t i) ω₀) (fun t => ?_)
      (B := B) (fun t i => 𝔼.abs_E_le (hB t i) 0 ω₀)
    funext i
    have e1 : 𝔼.E 0 (y (t + 1) i) = 𝔼.E 0 (𝔼.E t (y (t + 1) i)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    rw [e1, hy t i, map_add, E_mv 𝔼, 𝔼.const, Pi.add_apply, Pi.add_apply, mv_apply]

/-- Woodford (2003), App. C.1, p. 670, fn. 1: with an eigenvalue on the unit circle the system is
not determinate (equilibrium fails to exist for some bounded forcing). -/
theorem not_determinate_of_unit [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {μ : ℂ}
    (hμ : μ ∈ eigs A) (h1 : ‖μ‖ = 1) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨w, hwb, hwa, hno⟩ := nonexist_of_unit 𝔼 hμ h1
  obtain ⟨y, ⟨hs, -, -, -, hb⟩, -⟩ := hdet w hwb hwa 0
  exact hno y hs hb

/-! ### Necessity (ii): genericity and the dimension of the stable subspace -/

/-- **Non-uniqueness without genericity** (Woodford (2003), App. C.1, p. 672, fn. 2; Blanchard
and Kahn 1980): if a nonzero bounded orbit `Aᵗ v` starts with `x = 0`, then next to every
equilibrium there is another one (add the deterministic path `Aᵗ v`). -/
theorem mult_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : ¬ GenericX A)
    {w : ℕ → Z ⊕ X → Ω → ℝ} {x0 : X → ℝ} {y : ℕ → Z ⊕ X → Ω → ℝ} (hy : Equil 𝔼 A w x0 y) :
    ∃ y', Equil 𝔼 A w x0 y' ∧ y' ≠ y := by
  unfold GenericX at h
  push Not at h
  obtain ⟨v, ⟨C, hC⟩, hvx, hv0⟩ := h
  obtain ⟨hs, ha, hk, h0, ⟨M, hM⟩⟩ := hy
  set y' : ℕ → Z ⊕ X → Ω → ℝ := fun t k => y t k + fun _ => (A ^ t *ᵥ v) k with hy'
  refine ⟨y', ⟨fun t k => ?_, fun t k => ?_, fun t j => ?_, fun j => ?_, ⟨M + C, ?_⟩⟩, ?_⟩
  · simp only [hy', map_add, 𝔼.const, hs t k]
    funext ω
    simp only [Pi.add_apply, mv_apply]
    rw [show (fun j => y t j ω + (A ^ t *ᵥ v) j) = (fun j => y t j ω) + A ^ t *ᵥ v from rfl,
      Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_mulVec, ← pow_succ']
    ring
  · simp only [hy', map_add, 𝔼.const, ha t k]
  · simp only [hy', map_add, 𝔼.const, hk t j]
  · simp only [hy', pow_zero, Matrix.one_mulVec, hvx j, h0 j]
    funext ω
    simp
  · intro t k ω
    exact (abs_add_le _ _).trans (add_le_add (hM t k ω) (hC t k))
  · intro he
    apply hv0
    funext k
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun he 0) k) ω
    simpa [hy'] using this

/-- Woodford (2003), App. C.1, p. 672, fn. 2: without genericity the system is not
determinate (already for `w = 0`, `x_0 = 0` there are two equilibria). -/
theorem not_determinate_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : ¬ GenericX A) : ¬ Determinate 𝔼 A := by
  intro hdet
  have hb0 : BoundedV (0 : ℕ → Z ⊕ X → Ω → ℝ) := ⟨0, fun _ _ _ => by simp⟩
  have ha0 : AdaptedV 𝔼 (0 : ℕ → Z ⊕ X → Ω → ℝ) := fun t k => by simp
  obtain ⟨y, hy, huniq⟩ := hdet 0 hb0 ha0 0
  obtain ⟨y', hy', hne⟩ := mult_of_not_genericX 𝔼 h hy
  exact hne (huniq y' hy')

/-- **Non-existence with too few stable directions** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): if the bounded-orbit subspace has dimension below the number of
predetermined variables, some initial `x_0` admits no equilibrium even with `w = 0`. Taking
`E_0` of an equilibrium gives, outcome by outcome, a bounded orbit starting at `(z_0, x_0)`. -/
theorem nonexist_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ∃ x0 : X → ℝ, ∀ y, ¬ Equil 𝔼 A 0 x0 y := by
  obtain ⟨x0, hx0⟩ := exists_unreached_of_lt h
  refine ⟨x0, fun y hy => ?_⟩
  obtain ⟨hs, -, -, h0, ⟨M, hM⟩⟩ := hy
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  set e : ℕ → Z ⊕ X → ℝ := fun t k => 𝔼.E 0 (y t k) ω₀ with he
  have hstep : ∀ t, e (t + 1) = A *ᵥ e t := by
    intro t
    funext k
    have e1 : 𝔼.E 0 (y (t + 1) k) = 𝔼.E 0 (𝔼.E t (y (t + 1) k)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    simp only [he]
    rw [e1, hs t k, Pi.zero_apply, Pi.zero_apply, add_zero, E_mv 𝔼, mv_apply]
  have hmem := mem_boundedOrbits_of_orbit hstep (fun t k => 𝔼.abs_E_le (hM t k) 0 ω₀)
  apply hx0 _ hmem
  funext j
  simp only [he, h0 j, 𝔼.const]

/-- Woodford (2003), App. C.1, p. 670: too few stable directions — not determinate. -/
theorem not_determinate_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨x0, hx0⟩ := nonexist_of_lt 𝔼 h
  obtain ⟨y, hy, -⟩ := hdet 0 ⟨0, fun _ _ _ => by simp⟩ (fun t k => by simp) x0
  exact hx0 y hy

/-- Woodford (2003), App. C.1, p. 672, fn. 2: too many stable directions — not determinate
(genericity must fail, so equilibria are not unique). -/
theorem not_determinate_of_gt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Fintype.card X < Module.finrank ℝ (boundedOrbits A)) : ¬ Determinate 𝔼 A :=
  not_determinate_of_not_genericX 𝔼 (not_genericX_of_lt h)

/-! ### The Blanchard–Kahn theorem -/

/-- **The Blanchard–Kahn theorem** (Woodford (2003), App. C.1, p. 670 and fn. 1–2, which the book
takes from Blanchard and Kahn (1980)): for any expectation system on a nonempty state space, the
system `E_t y_{t+1} = A y_t + w_t` with `|X|` predetermined variables is determinate iff
(i) no eigenvalue of `A` lies on the unit circle, (ii) the stable (bounded-orbit) subspace has
dimension `|X|`, and (iii) the stable subspace meets `{x = 0}` only in `0`. -/
theorem determinate_iff [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ Module.finrank ℝ (boundedOrbits A) = Fintype.card X ∧
      GenericX A := by
  constructor
  · intro hdet
    have hnu : NoUnit A := fun μ hμ h1 => not_determinate_of_unit 𝔼 hμ h1 hdet
    have hg : GenericX A := by
      by_contra hg
      exact not_determinate_of_not_genericX 𝔼 hg hdet
    refine ⟨hnu, ?_, hg⟩
    rcases lt_trichotomy (Module.finrank ℝ (boundedOrbits A)) (Fintype.card X) with h | h | h
    · exact absurd hdet (not_determinate_of_lt 𝔼 h)
    · exact h
    · exact absurd hdet (not_determinate_of_gt 𝔼 h)
  · rintro ⟨hnu, hd, hg⟩
    exact determinate_of 𝔼 hnu hd hg

/-- **The Blanchard–Kahn counting rule** (Woodford (2003), App. C.1, p. 670 and fn. 1–2; Blanchard
and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly `|X|` eigenvalues in the
open unit disc counted with algebraic multiplicity, and genericity. -/
theorem determinate_iff_count [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ stableCount A = Fintype.card X ∧ GenericX A := by
  rw [determinate_iff]
  constructor
  · rintro ⟨hnu, hd, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mp hd, hg⟩
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mpr hc, hg⟩

/-- **The Blanchard–Kahn counting rule, unstable form** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly as many
eigenvalues outside the unit circle (with multiplicity) as non-predetermined variables, and
genericity. -/
theorem determinate_iff_unstableCount [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ unstableCount A = Fintype.card Z ∧ GenericX A := by
  rw [determinate_iff_count]
  constructor
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670: determinacy does not depend on the expectation system —
it holds under any expectation system on a nonempty state space iff it holds under perfect
foresight. -/
theorem determinate_iff_perfectForesight [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ Determinate perfectForesight A := by
  classical
  rw [determinate_iff, determinate_iff]

/-! ### The bounded-orbit subspace is the stable subspace -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a vector whose orbit tends to `0` has a bounded
orbit. -/
theorem mem_boundedOrbits_of_tendsto {A : Matrix κ κ ℝ} {v : κ → ℝ}
    (h : Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0)) : v ∈ boundedOrbits A := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun t => A ^ t *ᵥ v) h)
  exact ⟨C, fun t i => (norm_le_pi_norm (A ^ t *ᵥ v) i).trans (hC _ ⟨t, rfl⟩) |>.trans' le_rfl⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): with no eigenvalue on the unit
circle, the bounded-orbit subspace is exactly the stable subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto_of_noUnit {A : Matrix κ κ ℝ} (hnu : NoUnit A)
    (v : κ → ℝ) : v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) :=
  ⟨tendsto_of_mem_boundedOrbits hnu, mem_boundedOrbits_of_tendsto⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): under the Blanchard–Kahn
conditions every bounded orbit tends to `0` — the bounded-orbit subspace is exactly the stable
subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A)
    (v : Z ⊕ X → ℝ) :
    v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) := by
  refine ⟨fun hv => ?_, mem_boundedOrbits_of_tendsto⟩
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hL⟩ := pow_entry_bound _ (lam_stable hG hnu)
  set x : X → ℝ := fun j => v (Sum.inr j) with hx
  have hvg : v = graphV G x := by
    funext k
    rcases k with i | j
    · exact hG.2 v hv i
    · rfl
  set Xb : ℝ := ∑ j, |x j| with hXb
  have hXb0 : 0 ≤ Xb := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hxj : ∀ j, |x j| ≤ Xb := fun j =>
    Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  set aG : ℝ := ∑ i, ∑ j, |G i j| with haG
  have hLx : ∀ t j, |(lam A G ^ t *ᵥ x) j| ≤ Fintype.card X * (Cb * ρ ^ t * Xb) :=
    fun t j => InvariantSplit.abs_mulVec_le _ _ (hL t) hxj j
  have hlim : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul Cb).mul_const Xb
    simpa using this.const_mul (Fintype.card X : ℝ)
  have hlim2 : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) *
      (aG * ((Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)))) atTop (𝓝 0) := by
    simpa using (hlim.const_mul aG).const_mul (Fintype.card X : ℝ)
  rw [hvg, tendsto_pi_nhds]
  intro k
  simp only [pow_mulVec_graphV hinv]
  rcases k with i | j
  · refine squeeze_zero_norm (fun t => ?_) hlim2
    rw [Real.norm_eq_abs]
    exact InvariantSplit.abs_mulVec_le G _ (abs_entry_le_sum G) (hLx t) i
  · refine squeeze_zero_norm (fun t => ?_) hlim
    rw [Real.norm_eq_abs]
    exact hLx t j

end Gali.MonetaryPolicyDesign.GeneralBK

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The money-supply system (34) of Chapter 3

Galí (2015), Chapter 3, §3.4.2, pp. 74–75, used in Chapter 4, Ex. 4.4(c), p. 123 (a money supply
rule). Restated from the Chapter 3 project (`BasicNewKeynesianModel.MoneyRule`, namespace renamed;
this project does not import across projects): the matrices `A_{M,0}`, `A_{M,1}`, `B_M` of (34),
the system itself with real balances `l̂_{t−1}` predetermined, the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0})` and its basic properties, and the statement of the book's
determinacy claim (fn. 14), proved in `MoneyRuleRoots.bookDeterminacyClaim_holds`.
-/

namespace Gali.MonetaryPolicyDesign.MoneyRuleSystem

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 75: real balances `l̂_{t−1}` are predetermined, so `l̂_t` is known at `t`. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

/-! ### The matrix form (34) -/

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), eq. (34), p. 75: the forecast
`E_t x_{t+1} = (E_t ỹ_{t+1}, E_t π_{t+1}, E_t l̂_t)`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), eq. (34), p. 75: the shocks `(r̂^n_t, ŷ^n_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), eq. (34), p. 75: `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t` in every
state. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-! ### Eigenvalues of `A_M` -/

/-- Galí (2015), p. 75 (survey §3.1): the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`. -/
def charCubic (σ η β κ z : ℝ) : ℝ :=
  (σ * η - z * (1 + σ * η)) * (β - z) * (1 - z) - η * κ * z * (1 - z) + κ * z ^ 2

/-- Galí (2015), p. 75: `det(A_{M,1} − z A_{M,0})` is the characteristic cubic (exact). -/
theorem det_AM1_sub_smul_AM0 (σ η β κ z : ℝ) :
    (AM1 σ η β - z • AM0 σ η κ).det = charCubic σ η β κ z := by
  simp [Matrix.det_fin_three, AM0, AM1, charCubic]
  ring

/-- Galí (2015), p. 75: `det A_{M,0} = 1 + ση`. -/
theorem det_AM0 (σ η κ : ℝ) : (AM0 σ η κ).det = 1 + σ * η := by
  simp [Matrix.det_fin_three, AM0]

/-- Galí (2015), p. 75: `det A_{M,1} = σηβ`. -/
theorem det_AM1 (σ η β : ℝ) : (AM1 σ η β).det = σ * η * β := by
  simp [Matrix.det_fin_three, AM1]

/-- Galí (2015), p. 75: the matrix `A_M ≡ A_{M,0}⁻¹ A_{M,1}`. -/
noncomputable def AM (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM0 σ η κ)⁻¹ * AM1 σ η β

/-- Galí (2015), p. 75: `det(A_M − z I) = (1+ση)⁻¹ f(z)` when `1 + ση ≠ 0`. -/
theorem det_AM_sub_smul {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      (1 + σ * η)⁻¹ * charCubic σ η β κ z := by
  have hu : IsUnit (AM0 σ η κ).det := by rw [det_AM0]; exact h.isUnit
  have hfac : AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      (AM0 σ η κ)⁻¹ * (AM1 σ η β - z • AM0 σ η κ) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu, AM]
  rw [hfac, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv',
    det_AM1_sub_smul_AM0]

/-- Galí (2015), p. 75: the characteristic polynomial of `A_M` evaluated at `z` is
`−(1+ση)⁻¹ f(z)`, so the eigenvalues of `A_M` are exactly the roots of `f`. -/
theorem charpoly_AM_eval {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.eval z = -((1 + σ * η)⁻¹ * charCubic σ η β κ z) := by
  rw [Matrix.eval_charpoly, ← det_AM_sub_smul h]
  have : Matrix.scalar (Fin 3) z - AM σ η β κ =
      -(AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    rw [neg_sub, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [this, Matrix.det_neg]
  simp only [Fintype.card_fin]
  ring

/-- Galí (2015), p. 75: a real `z` is an eigenvalue of `A_M` iff `f(z) = 0`. -/
theorem isRoot_charpoly_AM_iff {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.IsRoot z ↔ charCubic σ η β κ z = 0 := by
  rw [Polynomial.IsRoot.def, charpoly_AM_eval h, neg_eq_zero, mul_eq_zero]
  simp [inv_eq_zero, h]

/-- Galí (2015), p. 75: the cubic expanded; its leading coefficient is `−(1+ση)`. -/
theorem charCubic_expand (σ η β κ z : ℝ) :
    charCubic σ η β κ z = -(1 + σ * η) * z ^ 3 +
      (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * z ^ 2 +
      (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * z + σ * η * β := by
  unfold charCubic
  ring

/-- Galí (2015), p. 75: `f(0) = σηβ`. -/
theorem charCubic_zero (σ η β κ : ℝ) : charCubic σ η β κ 0 = σ * η * β := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(1) = κ`. -/
theorem charCubic_one (σ η β κ : ℝ) : charCubic σ η β κ 1 = κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(0) > 0` and `f(1) > 0` for `σ, η, β, κ > 0`, and the leading
coefficient `−(1+ση)` is negative. -/
theorem charCubic_signs {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β) (hκ : 0 < κ) :
    0 < charCubic σ η β κ 0 ∧ 0 < charCubic σ η β κ 1 ∧ -(1 + σ * η) < 0 := by
  rw [charCubic_zero, charCubic_one]
  refine ⟨by positivity, hκ, ?_⟩
  have : 0 < σ * η := mul_pos hσ hη
  linarith

/-- Galí (2015), p. 75: the cubic has a real root strictly greater than one (IVT between
`f(1) = κ > 0` and a point where `f < 0`). -/
theorem charCubic_root_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ charCubic σ η β κ z = 0 := by
  set b := 1 + σ * η with hb
  set c₂ := σ * η + b * (1 + β) + η * κ + κ with hc₂
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb0 : 0 < b := by linarith
  have hc₂0 : 0 < c₂ := by
    have : 0 < η * κ := mul_pos hη hκ
    nlinarith
  set R := 1 + c₂ / b with hR
  have hR1 : 1 < R := by have := div_pos hc₂0 hb0; linarith
  have hbR : b * R = b + c₂ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_expand]
    have hηκ : 0 < η * κ := mul_pos hη hκ
    have hsηβ : 0 < σ * η * β := by positivity
    have hlead : -b * R ^ 3 + c₂ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + c₂ * R ^ 2 = R ^ 2 * (c₂ - b * R) := by ring
      rw [this, hbR]; ring
    have hc1 : (-(σ * η) * (1 + β) - b * β - η * κ) * R ≤
        -(σ * η) * (1 + β) - b * β - η * κ := by
      have hneg : -(σ * η) * (1 + β) - b * β - η * κ < 0 := by nlinarith
      nlinarith
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hsum : -(σ * η) * (1 + β) - b * β - η * κ + σ * η * β < 0 := by nlinarith
    have hfin : -b * R ^ 2 < 0 := by nlinarith
    calc -(1 + σ * η) * R ^ 3 + (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * R ^ 2 +
          (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * R + σ * η * β
        = (-b * R ^ 3 + c₂ * R ^ 2) +
          (-(σ * η) * (1 + β) - b * β - η * κ) * R + σ * η * β := by
          rw [hb, hc₂]
      _ < 0 := by rw [hlead]; linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: for `σ, η, β, κ > 0`, `A_M` has a real eigenvalue strictly
greater than one (so at least one eigenvalue lies outside the unit circle). -/
theorem AM_has_eigenvalue_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ (AM σ η β κ).charpoly.IsRoot z := by
  obtain ⟨z, hz1, hz⟩ := charCubic_root_gt_one hσ hη hβ hκ
  have h : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  exact ⟨z, hz1, (isRoot_charpoly_AM_iff h z).mpr hz⟩

/-- Galí (2015), p. 75: `det A_M = σηβ/(1+ση)`, the product of the three eigenvalues. -/
theorem det_AM {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) :
    (AM σ η β κ).det = σ * η * β / (1 + σ * η) := by
  rw [AM, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv', det_AM1]
  field_simp

/-- Galí (2015), p. 75: for `σ, η > 0` and `0 < β < 1`, the product of the eigenvalues of
`A_M` lies in `(0, 1)`. -/
theorem det_AM_pos_lt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hβ1 : β < 1) : 0 < (AM σ η β κ).det ∧ (AM σ η β κ).det < 1 := by
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb : 0 < 1 + σ * η := by linarith
  rw [det_AM hb.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hb]
  nlinarith

/-- Galí (2015), p. 75 and fn. 14: the book's determinacy claim: the cubic factors as
`−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and both roots of the quadratic factor inside the
unit circle (Schur–Cohn). The book supports it numerically only; it is proved in
`MoneyRuleRoots.bookDeterminacyClaim_holds`. -/
def BookDeterminacyClaim (σ η β κ : ℝ) : Prop :=
  ∃ r q₁ q₀ : ℝ, 1 < r ∧
    (∀ z, charCubic σ η β κ z = -(1 + σ * η) * (z - r) * (z ^ 2 + q₁ * z + q₀)) ∧
    SchurStable (-q₁) q₀

end Gali.MonetaryPolicyDesign.MoneyRuleSystem

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Root location for the money-supply system (34): Galí's footnote 14 proved

Galí (2015), Chapter 3, §3.4.2, p. 75 and fn. 14. Under an exogenous money supply the
equilibrium solves (34), `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`, and the book states,
supported only by a numerical exploration (fn. 14), that `A_M = A_{M,0}⁻¹ A_{M,1}` always has two
eigenvalues inside and one outside the unit circle. Here this is proved for all parameters.

With `b = 1 + ση` the eigenvalues of `A_M` are the roots of the characteristic cubic
`f(z) = (ση − z b)(β − z)(1 − z) − ηκ z(1 − z) + κ z²` (`MoneyRuleSystem.isRoot_charpoly_AM_iff`):
`f(0) = σηβ`, `f(1) = κ > 0`, `f(−1) = 2(1 + 2ση)(1 + β) + 2ηκ + κ > 0`, leading coefficient
`−b < 0`. So `f` has a real root `r > 1` and factors as `f(z) = −b (z − r)(z² + q₁ z + q₀)`;
evaluating at `0`, `1`, `−1` gives `b r q₀ = σηβ`, `b (r − 1)(1 + q₁ + q₀) = κ` and
`b (1 + r)(1 − q₁ + q₀) = f(−1)`, which are exactly the Schur–Cohn conditions
`|q₀| < 1`, `|q₁| < 1 + q₀` for the quadratic factor.

## Parameter domain

Everything holds for `σ ≥ 0`, `η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1`, which contains Galí's domain
(`σ > 0`, `κ > 0`, `0 < β < 1`, and `η ≥ 0`: Galí (2015), Ch. 2, eq. (4), p. 21 allows a zero
interest semi-elasticity of money demand). At `η = 0` one eigenvalue is `0` (still inside).

## Main results

* `exists_root_gt_one`, `charCubic_factor`: the real root `r > 1` and the factorisation.
* `quad_schurStable`: the quadratic factor satisfies the Schur–Cohn conditions.
* `bookDeterminacyClaim_holds`, `bookDeterminacyClaim_gali`: the book's claim
  `MoneyRuleSystem.BookDeterminacyClaim` is TRUE (stated before without proof).
* `norm_lt_one_of_quadratic`: a complex root of a real monic quadratic satisfying the Schur–Cohn
  conditions lies in the open unit disc.
* `AM_root_location`: counted with algebraic multiplicity over `ℂ`, `A_M` has exactly one
  eigenvalue outside the closed unit disc (`unstableCount = 1`), two in the open disc
  (`stableCount = 2`) and none on the unit circle (`NoUnit`).
* `real_eigenvalue_unique`: every real eigenvalue of modulus `≥ 1` is the root `r > 1`.

The analogous result for a more general model was proved analytically by Schabert and
Stoltenberg (2005), ECB Working Paper 458, Prop. 12 and App. 6.12.

Restated from the Chapter 3 project (`BasicNewKeynesianModel.MoneyRuleRoots`, namespace renamed;
this project does not import across projects). Used for Galí (2015), Ex. 4.4(c), p. 123.
-/

namespace Gali.MonetaryPolicyDesign.MoneyRuleRoots

open Polynomial MoneyRuleSystem InvariantSplit

/-! ### The real factorisation -/

/-- Galí (2015), p. 75: the coefficient of `z²` in the characteristic cubic. -/
def coef2 (σ η β κ : ℝ) : ℝ := σ * η + (1 + σ * η) * (1 + β) + η * κ + κ

/-- Galí (2015), p. 75: the coefficient of `z` in the characteristic cubic. -/
def coef1 (σ η β κ : ℝ) : ℝ := -(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ

/-- Galí (2015), p. 75: `f(z) = −(1+ση) z³ + c₂ z² + c₁ z + σηβ`. -/
theorem charCubic_eq_coef (σ η β κ z : ℝ) :
    charCubic σ η β κ z =
      -(1 + σ * η) * z ^ 3 + coef2 σ η β κ * z ^ 2 + coef1 σ η β κ * z + σ * η * β := by
  rw [charCubic_expand, coef2, coef1]

/-- Galí (2015), p. 75: the linear coefficient `q₁ = r − c₂/(1+ση)` of the quadratic factor of
the cubic after the root `r` is divided out. -/
noncomputable def quadQ1 (σ η β κ r : ℝ) : ℝ := r - coef2 σ η β κ / (1 + σ * η)

/-- Galí (2015), p. 75: the constant `q₀ = r q₁ − c₁/(1+ση)` of the quadratic factor. -/
noncomputable def quadQ0 (σ η β κ r : ℝ) : ℝ := r * quadQ1 σ η β κ r - coef1 σ η β κ / (1 + σ * η)

/-- Galí (2015), p. 75: `(1+ση) q₁ = (1+ση) r − c₂`. -/
theorem quadQ1_mul {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) (r : ℝ) :
    (1 + σ * η) * quadQ1 σ η β κ r = (1 + σ * η) * r - coef2 σ η β κ := by
  rw [quadQ1, mul_sub, mul_div_cancel₀ _ hb]

/-- Galí (2015), p. 75: `(1+ση) q₀ = (1+ση) r q₁ − c₁`. -/
theorem quadQ0_mul {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) (r : ℝ) :
    (1 + σ * η) * quadQ0 σ η β κ r = (1 + σ * η) * r * quadQ1 σ η β κ r - coef1 σ η β κ := by
  rw [quadQ0, mul_sub, mul_div_cancel₀ _ hb, mul_assoc]

/-- Galí (2015), p. 75: if `f(r) = 0` the cubic factors as
`f(z) = −(1+ση)(z − r)(z² + q₁ z + q₀)`. -/
theorem charCubic_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0)
    (z : ℝ) : charCubic σ η β κ z =
      -(1 + σ * η) * (z - r) * (z ^ 2 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r) := by
  have h1 := quadQ1_mul (κ := κ) (β := β) hb r
  have h0 := quadQ0_mul (κ := κ) (β := β) hb r
  rw [charCubic_eq_coef] at hr ⊢
  linear_combination (z ^ 2 - r ^ 2) * h1 + (z - r) * h0 + hr

/-- Galí (2015), p. 75: `f(−1) = 2(1 + 2ση)(1 + β) + 2ηκ + κ`. -/
theorem charCubic_neg_one (σ η β κ : ℝ) :
    charCubic σ η β κ (-1) = 2 * (1 + 2 * (σ * η)) * (1 + β) + 2 * (η * κ) + κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` the cubic has a real root strictly
greater than one (IVT between `f(1) = κ > 0` and `f(1 + c₂/(1+ση)) < 0`). -/
theorem exists_root_gt_one {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : ∃ r, 1 < r ∧ charCubic σ η β κ r = 0 := by
  have hsη : 0 ≤ σ * η := mul_nonneg hσ hη
  have hηκ : 0 ≤ η * κ := mul_nonneg hη hκ.le
  set b := 1 + σ * η with hb
  have hb0 : 0 < b := by linarith
  have hc2 : 0 < coef2 σ η β κ := by
    unfold coef2; nlinarith
  have hc1 : coef1 σ η β κ ≤ 0 := by
    unfold coef1; nlinarith
  set R := 1 + coef2 σ η β κ / b with hR
  have hR1 : 1 < R := by have := div_pos hc2 hb0; linarith
  have hbR : b * R = b + coef2 σ η β κ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_eq_coef]
    have hlead : -b * R ^ 3 + coef2 σ η β κ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + coef2 σ η β κ * R ^ 2 = R ^ 2 * (coef2 σ η β κ - b * R) := by ring
      rw [this, hbR]; ring
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hc1R : coef1 σ η β κ * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc1 (by linarith)
    have hsηβ : σ * η * β ≤ σ * η := by nlinarith
    have hbR2 : b < b * R ^ 2 := by nlinarith
    rw [← hb]
    linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: the values of the quadratic factor at `0`, `1`, `−1` (given a root
`r > 1`): `(1+ση) r q₀ = σηβ`, `(1+ση)(r − 1)(1 + q₁ + q₀) = κ`,
`(1+ση)(1 + r)(1 − q₁ + q₀) = f(−1)`. -/
theorem quad_values {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (1 + σ * η) * r * quadQ0 σ η β κ r = σ * η * β ∧
      (1 + σ * η) * (r - 1) * (1 + quadQ1 σ η β κ r + quadQ0 σ η β κ r) = κ ∧
      (1 + σ * η) * (1 + r) * (1 - quadQ1 σ η β κ r + quadQ0 σ η β κ r) =
        charCubic σ η β κ (-1) := by
  have h0 := charCubic_factor hb hr 0
  have h1 := charCubic_factor hb hr 1
  have hm := charCubic_factor hb hr (-1)
  rw [charCubic_zero] at h0
  rw [charCubic_one] at h1
  refine ⟨by linear_combination -h0, by linear_combination -h1, by linear_combination -hm⟩

/-- Galí (2015), p. 75: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` and a root `r > 1`, the quadratic
factor `z² + q₁ z + q₀` satisfies the Schur–Cohn conditions `|q₀| < 1`, `|q₁| < 1 + q₀`, and
`q₀ ≥ 0` (with `q₀ > 0` iff `σηβ > 0`). -/
theorem quad_schurStable {σ η β κ r : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hr1 : 1 < r) (hr : charCubic σ η β κ r = 0) :
    SchurStable (-quadQ1 σ η β κ r) (quadQ0 σ η β κ r) ∧ 0 ≤ quadQ0 σ η β κ r := by
  have hsη : 0 ≤ σ * η := mul_nonneg hσ hη
  have hηκ : 0 ≤ η * κ := mul_nonneg hη hκ.le
  have hb0 : 0 < 1 + σ * η := by linarith
  obtain ⟨h0, h1, hm⟩ := quad_values hb0.ne' hr
  rw [charCubic_neg_one] at hm
  have hbr : 0 < (1 + σ * η) * r := by positivity
  have hq0 : 0 ≤ quadQ0 σ η β κ r := by
    by_contra hneg
    push Not at hneg
    have : (1 + σ * η) * r * quadQ0 σ η β κ r < 0 := mul_neg_of_pos_of_neg hbr hneg
    have : 0 ≤ σ * η * β := mul_nonneg hsη hβ0
    linarith
  have hq0' : quadQ0 σ η β κ r < 1 := by
    by_contra hge
    push Not at hge
    have hsηβ : σ * η * β ≤ σ * η := by nlinarith
    have : (1 + σ * η) * r * 1 ≤ (1 + σ * η) * r * quadQ0 σ η β κ r :=
      mul_le_mul_of_nonneg_left hge hbr.le
    nlinarith
  have hp1 : 0 < 1 + quadQ1 σ η β κ r + quadQ0 σ η β κ r := by
    have hpos : 0 < (1 + σ * η) * (r - 1) := mul_pos hb0 (by linarith)
    refine pos_of_mul_pos_right (a := (1 + σ * η) * (r - 1)) ?_ hpos.le
    rw [h1]; exact hκ
  have hm1 : 0 < 1 - quadQ1 σ η β κ r + quadQ0 σ η β κ r := by
    have hpos : 0 < (1 + σ * η) * (1 + r) := mul_pos hb0 (by linarith)
    refine pos_of_mul_pos_right (a := (1 + σ * η) * (1 + r)) ?_ hpos.le
    rw [hm]; positivity
  refine ⟨⟨?_, ?_⟩, hq0⟩
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

/-- **Galí (2015), p. 75, fn. 14, PROVED**: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` the
characteristic cubic factors as `−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and the quadratic
factor Schur stable: the book's (numerically supported) determinacy claim holds. -/
theorem bookDeterminacyClaim_holds {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : BookDeterminacyClaim σ η β κ := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ hη hκ hβ0 hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  exact ⟨r, quadQ1 σ η β κ r, quadQ0 σ η β κ r, hr1, charCubic_factor hb hr,
    (quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr).1⟩

/-- **Galí (2015), p. 75, fn. 14, PROVED** on the book's parameter domain `σ > 0`, `η ≥ 0`,
`κ > 0`, `0 < β < 1`. -/
theorem bookDeterminacyClaim_gali {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) : BookDeterminacyClaim σ η β κ :=
  bookDeterminacyClaim_holds hσ.le hη hκ hβ0.le hβ1.le

/-! ### Complex roots -/

/-- Galí (2015), p. 75 (Schur–Cohn for a real quadratic): if `|b| < 1` and `|a| < 1 + b`, every
complex root of `ν² + a ν + b` lies in the open unit disc. -/
theorem norm_lt_one_of_quadratic {a b : ℝ} (hb : |b| < 1) (ha : |a| < 1 + b) {ν : ℂ}
    (hν : ν ^ 2 + a * ν + b = 0) : ‖ν‖ < 1 := by
  have hre := congrArg Complex.re hν
  have him := congrArg Complex.im hν
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  set x := ν.re
  set y := ν.im
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have hn : ‖ν‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : x ^ 2 + y ^ 2 < 1 := by
    by_cases hy : y = 0
    · rw [hy] at hre ⊢
      have hx : x * x + a * x + b = 0 := by linarith
      have hlt : x < 1 := by
        by_contra hx1
        push Not at hx1
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (hb2.le.trans hx1))]
      have hgt : -1 < x := by
        by_contra hx1
        push Not at hx1
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : (0 : ℝ) ≤ -x - b)]
      nlinarith
    · have h2 : 2 * x + a = 0 := by
        have : y * (2 * x + a) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hy
        · exact h
      nlinarith
  rw [← hn] at key
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp key

/-- Galí (2015), p. 75: the real monic quadratic `z² + q₁ z + q₀`. -/
noncomputable def quadPoly (q₁ q₀ : ℝ) : ℝ[X] := X ^ 2 + C q₁ * X + C q₀

/-- Galí (2015), p. 75: a complex root `μ` of the quadratic satisfies `μ² + q₁ μ + q₀ = 0`. -/
theorem quadPoly_root {q₁ q₀ : ℝ} {μ : ℂ}
    (h : μ ∈ ((quadPoly q₁ q₀).map Complex.ofRealHom).roots) : μ ^ 2 + q₁ * μ + q₀ = 0 := by
  have h' := (mem_roots'.mp h).2
  simpa [quadPoly, IsRoot] using h'

/-- Galí (2015), p. 75: with `1 + ση ≠ 0` and `f(r) = 0`, the characteristic polynomial of `A_M`
is `(X − r)(X² + q₁ X + q₀)`. -/
theorem charpoly_AM_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (AM σ η β κ).charpoly = (X - C r) * quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r) := by
  refine Polynomial.funext fun z => ?_
  rw [charpoly_AM_eval hb, charCubic_factor hb hr]
  simp only [quadPoly, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  field_simp

/-- Galí (2015), p. 75: the eigenvalues of `A_M` (with multiplicity) are `r` and the two complex
roots of the quadratic factor. -/
theorem eigs_AM {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    eigs (AM σ η β κ) = {(r : ℂ)} +
      ((quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r)).map Complex.ofRealHom).roots := by
  have hne : ((AM σ η β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
    ((Matrix.charpoly_monic _).map _).ne_zero
  rw [eigs, charpoly_map_ofReal]
  rw [charpoly_AM_factor hb hr, Polynomial.map_mul] at hne ⊢
  rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
  rfl

/-- **Galí (2015), p. 75, fn. 14 — root location, PROVED**: for `σ, η ≥ 0`, `κ > 0`,
`0 ≤ β ≤ 1`, counted with algebraic multiplicity over `ℂ`, `A_M = A_{M,0}⁻¹ A_{M,1}` has no
eigenvalue on the unit circle, exactly one outside the closed unit disc and exactly two in the
open unit disc. -/
theorem AM_root_location {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    NoUnit (AM σ η β κ) ∧ unstableCount (AM σ η β κ) = 1 ∧ stableCount (AM σ η β κ) = 2 := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ hη hκ hβ0 hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr
  set R := ((quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r)).map Complex.ofRealHom).roots
    with hRdef
  have hRin : ∀ μ ∈ R, ‖μ‖ < 1 := by
    intro μ hμ
    refine norm_lt_one_of_quadratic hS.1 ?_ (quadPoly_root hμ)
    have := hS.2
    rwa [abs_neg] at this
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have he : eigs (AM σ η β κ) = {(r : ℂ)} + R := eigs_AM hb hr
  have hcard : Multiset.card R = 2 := by
    have h3 := card_eigs (AM σ η β κ)
    rw [he, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at h3
    omega
  have hra : |r| = r := abs_of_pos (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · rw [hrn]; exact hr1.ne'
    · exact (hRin μ hμ).ne
  · rw [unstableCount, he, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hRin μ hμ).le), add_zero,
      Multiset.filter_singleton]
    simp [hra, hr1]
  · rw [stableCount, he, Multiset.filter_add, Multiset.filter_eq_self.mpr hRin,
      Multiset.filter_singleton]
    simp [hra, hr1.le, hcard]

/-- **Galí (2015), p. 75 — root location on the book's domain** (`σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β < 1`): one eigenvalue of `A_M` outside the closed unit disc, two inside the open disc,
none on the circle. -/
theorem AM_root_location_gali {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    NoUnit (AM σ η β κ) ∧ unstableCount (AM σ η β κ) = 1 ∧ stableCount (AM σ η β κ) = 2 :=
  AM_root_location hσ.le hη hκ hβ0.le hβ1.le

/-- Galí (2015), p. 75: the real eigenvalue outside the unit circle is unique: every real root of
the cubic with `|z| ≥ 1` equals the root `r > 1`. -/
theorem real_eigenvalue_unique {σ η β κ r z : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hr1 : 1 < r) (hr : charCubic σ η β κ r = 0)
    (hz : charCubic σ η β κ z = 0) (hz1 : 1 ≤ |z|) : z = r := by
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr
  rw [charCubic_factor hb hr, mul_eq_zero, mul_eq_zero] at hz
  rcases hz with (h | h) | h
  · exact absurd (neg_eq_zero.mp h) hb
  · linarith
  · have hn := norm_lt_one_of_quadratic hS.1 (by have := hS.2; rwa [abs_neg] at this)
      (ν := (z : ℂ)) (by exact_mod_cast h)
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    linarith

end Gali.MonetaryPolicyDesign.MoneyRuleRoots

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Determinacy under an exogenous money supply

Galí (2015), Chapter 3, §3.4.2, p. 75 and fn. 14: "the equilibrium is always determined under an
exogenous path for the money supply". This module proves it in the strong sense of the general
Blanchard–Kahn theorem (`GeneralBK`, restated from the Woodford Chapter 4 project): for every
bounded adapted path of the shocks `s_t = (r̂ⁿ_t, ŷⁿ_t, Δm_t)`, every initial real balance
`l̂_{−1}` and any `ExpectationSystem`, system (34),
`A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t` with `l̂_{t−1}` predetermined, has exactly one
bounded adapted solution.

## The state-space form

The state is `x_t = (ỹ_t, π_t; l̂_{t−1})`, indexed by `Fin 2 ⊕ Fin 1` (two non-predetermined
variables, one predetermined).

* `η > 0`: `A_{M,1}` is invertible (`det A_{M,1} = σηβ`), and (34) is
  `E_t x_{t+1} = A_b x_t − A_{M,1}⁻¹ B_M s_t` with `A_b = A_{M,1}⁻¹ A_{M,0} = A_M⁻¹`
  (`Ab3_eq_inv_AM`). Its characteristic polynomial is `(X − r⁻¹)(X² + (q₁/q₀) X + 1/q₀)`
  (`charpoly_Ab3_factor`): one eigenvalue `1/r ∈ (0, 1)` and two outside the closed unit disc
  (`Ab3_root_location`). Genericity holds because the stable eigenvector has a non-zero
  real-balance component (`Abk_genericX`).
* `η = 0` (allowed by Galí, Ch. 2, p. 21): `A_{M,1}` is singular (one infinite generalised
  eigenvalue). The first row of (34) is then static, `ỹ_t = l̂_t − ŷⁿ_t`, and the system reduces
  exactly to `(π_t; l̂_{t−1})` with `E_t (π_{t+1}, l̂_t) = B (π_t, l̂_{t−1}) + w_t`,
  `B = [[(1+κ)/β, −κ/β], [−1, 1]]`, whose eigenvalues are `ρ₁ ∈ (0,1)` and `1/(βρ₁) > 1`.

## Main results

* `Abk_determinate`, `B2_determinate`: the Blanchard–Kahn conditions hold, so the state-space
  systems are determinate for EVERY bounded adapted forcing vector.
* `system34_existsUnique`: for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1` and bounded adapted shocks,
  (34) has exactly one bounded adapted equilibrium with predetermined real balances starting at
  any given `l̂_{−1}` — for every `ExpectationSystem`.

Restated from the Chapter 3 project (`BasicNewKeynesianModel.MoneyRuleDeterminacy`, namespace
renamed, without the Chapter 3 model-equation corollary; this project does not import across
projects). Used for Galí (2015), Ex. 4.4(c), p. 123 (`Ex4_4Determinacy`).
-/

namespace Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy

open Polynomial MoneyRuleSystem MoneyRuleRoots InvariantSplit GeneralBKForward GeneralBK
open scoped Matrix

/-! ### Tools -/

/-- Galí (2015), p. 75 (tool): the eigenvalues are invariant under a relabelling of the state. -/
theorem eigs_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (M : Matrix κ κ ℝ) : eigs (M.submatrix e e) = eigs M := by
  unfold eigs
  rw [show (M.submatrix e e).map Complex.ofReal = Matrix.reindex e.symm e.symm
    (M.map Complex.ofReal) from rfl, Matrix.charpoly_reindex]

/-- Galí (2015), p. 75 (tool): if the stable count is one and a real eigenvector of a stable
eigenvalue has a non-zero predetermined component, the genericity condition holds (the stable
subspace is the line through that eigenvector). -/
theorem genericX_of_eigvec {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z]
    [DecidableEq X] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A) (hs : stableCount A = 1)
    {ρ : ℝ} (hρ : |ρ| < 1) {e : Z ⊕ X → ℝ} (he : A *ᵥ e = ρ • e) {j : X}
    (hej : e (Sum.inr j) ≠ 0) : GenericX A := by
  have he0 : e ≠ 0 := fun h => hej (by rw [h]; rfl)
  have hmem : e ∈ boundedOrbits A := by
    refine ⟨∑ k, |e k|, fun t i => ?_⟩
    rw [pow_mulVec_eigvec he t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |ρ| ^ t * |e i| ≤ 1 * |e i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hρ.le) (abs_nonneg _)
      _ = |e i| := one_mul _
      _ ≤ ∑ k, |e k| :=
          Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg _)
            (Finset.mem_univ i)
  have hspan : Submodule.span ℝ {e} = boundedOrbits A := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
    · rw [finrank_span_singleton he0, finrank_eq_stableCount hnu, hs]
  intro v hv hvx
  rw [← hspan, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  have h := hvx j
  rw [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · rw [h, zero_smul]
  · exact absurd h hej

/-- Galí (2015), p. 75 (tool): the roots of `X² + (q₁/q₀) X + 1/q₀` are the reciprocals of the
roots of `X² + q₁ X + q₀`, so they lie OUTSIDE the closed unit disc when the latter satisfies the
Schur–Cohn conditions. -/
theorem norm_gt_one_of_recip {q₁ q₀ : ℝ} (hS : SchurStable (-q₁) q₀) (hq0 : q₀ ≠ 0) {μ : ℂ}
    (h : μ ∈ ((quadPoly (q₁ / q₀) q₀⁻¹).map Complex.ofRealHom).roots) : 1 < ‖μ‖ := by
  have h1 := quadPoly_root h
  have hq0c : (q₀ : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hμ : μ ≠ 0 := by
    rintro rfl
    have : ((q₀⁻¹ : ℝ) : ℂ) = 0 := by simpa using h1
    exact hq0 (by exact_mod_cast inv_eq_zero.mp (by exact_mod_cast this))
  have h2 : (q₀ : ℂ) * μ ^ 2 + q₁ * μ + 1 = 0 := by
    have e : (q₀ : ℂ) * (μ ^ 2 + ((q₁ / q₀ : ℝ) : ℂ) * μ + ((q₀⁻¹ : ℝ) : ℂ)) =
        q₀ * μ ^ 2 + q₁ * μ + 1 := by
      push_cast
      field_simp
    rw [← e, h1, mul_zero]
  set ν := μ⁻¹ with hν
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have h3 : ν ^ 2 + q₁ * ν + q₀ = 0 := by
    linear_combination ν ^ 2 * h2 - ((q₁ : ℂ) * ν + q₀ * (1 + ν * μ)) * hνμ
  have hn := norm_lt_one_of_quadratic hS.1 (by have := hS.2; rwa [abs_neg] at this) h3
  have hν0 : ν ≠ 0 := inv_ne_zero hμ
  have hμν : μ = ν⁻¹ := by rw [hν, inv_inv]
  rw [hμν, norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hν0)).mpr hn

/-! ### `η > 0`: the backward matrix `A_b = A_{M,1}⁻¹ A_{M,0}` -/

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible, (34) reads
`E_t x_{t+1} = A_b x_t − A_{M,1}⁻¹ B_M s_t` with `A_b = A_{M,1}⁻¹ A_{M,0}`. -/
noncomputable def Ab3 (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM1 σ η β)⁻¹ * AM0 σ η κ

/-- Galí (2015), p. 75: `A_{M,1}` is invertible iff `σηβ ≠ 0`; in particular for `η > 0`. -/
theorem isUnit_det_AM1 {σ η β : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0) :
    IsUnit (AM1 σ η β).det := by
  rw [det_AM1]
  exact (mul_ne_zero (mul_ne_zero hσ hη) hβ).isUnit

/-- Galí (2015), p. 75: `A_{M,0}` is invertible whenever `1 + ση ≠ 0`. -/
theorem isUnit_det_AM0 {σ η κ : ℝ} (hb : 1 + σ * η ≠ 0) : IsUnit (AM0 σ η κ).det := by
  rw [det_AM0]
  exact hb.isUnit

/-- Galí (2015), p. 75: the backward matrix is the inverse of `A_M = A_{M,0}⁻¹ A_{M,1}`, so its
eigenvalues are the reciprocals of those of `A_M`. -/
theorem Ab3_eq_inv_AM {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) :
    Ab3 σ η β κ = (AM σ η β κ)⁻¹ := by
  rw [AM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_AM0 hb), Ab3]

/-- Galí (2015), p. 75: `det(z A_{M,1} − A_{M,0}) = σηβ z³ + c₁ z² + c₂ z − (1+ση)`, the
reversed characteristic cubic `z³ f(1/z)`. -/
theorem det_pencil (σ η β κ z : ℝ) :
    (z • AM1 σ η β - AM0 σ η κ).det =
      σ * η * β * z ^ 3 + coef1 σ η β κ * z ^ 2 + coef2 σ η β κ * z - (1 + σ * η) := by
  simp [Matrix.det_fin_three, AM0, AM1, coef1, coef2]
  ring

/-- Galí (2015), p. 75: with `f(r) = 0`,
`det(z A_{M,1} − A_{M,0}) = −(1+ση)(1 − r z)(1 + q₁ z + q₀ z²)`. -/
theorem det_pencil_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0)
    (z : ℝ) : (z • AM1 σ η β - AM0 σ η κ).det =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
  have h1 := quadQ1_mul (κ := κ) (β := β) hb r
  have h0 := quadQ0_mul (κ := κ) (β := β) hb r
  rw [det_pencil]
  rw [charCubic_eq_coef] at hr
  linear_combination (z - r ^ 2 * z ^ 3) * h1 + (z ^ 2 - r * z ^ 3) * h0 + z ^ 3 * hr

/-- Galí (2015), p. 75: `det A_{M,1} · det(z − A_b) = det(z A_{M,1} − A_{M,0})`. -/
theorem det_AM1_mul_charpoly_Ab3 {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (z : ℝ) :
    (AM1 σ η β).det * (Ab3 σ η β κ).charpoly.eval z = (z • AM1 σ η β - AM0 σ η κ).det := by
  rw [Matrix.eval_charpoly, ← Matrix.det_mul]
  congr 1
  rw [Matrix.mul_sub, Ab3, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

/-- Galí (2015), p. 75: for `σ, η, β ≠ 0`, `1 + ση ≠ 0` and a root `r` of the cubic, the
characteristic polynomial of `A_b` is `(X − r⁻¹)(X² + (q₁/q₀) X + q₀⁻¹)`. -/
theorem charpoly_Ab3_factor {σ η β κ r : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0)
    (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (Ab3 σ η β κ).charpoly = (X - C r⁻¹) *
      quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r) (quadQ0 σ η β κ r)⁻¹ := by
  have hu := isUnit_det_AM1 hσ hη hβ
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hsηβ : σ * η * β ≠ 0 := mul_ne_zero (mul_ne_zero hσ hη) hβ
  have hr0 : r ≠ 0 := by rintro rfl; apply hsηβ; rw [← hv0]; ring
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by rintro h; apply hsηβ; rw [← hv0, h]; ring
  refine Polynomial.funext fun z => ?_
  have e := det_AM1_mul_charpoly_Ab3 (κ := κ) hu z
  rw [det_pencil_factor hb hr, det_AM1, ← hv0] at e
  have hden : (1 + σ * η) * r * quadQ0 σ η β κ r ≠ 0 := by rw [hv0]; exact hsηβ
  simp only [quadPoly, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  have key : (1 + σ * η) * r * quadQ0 σ η β κ r * ((z - r⁻¹) * (z ^ 2 +
      quadQ1 σ η β κ r / quadQ0 σ η β κ r * z + (quadQ0 σ η β κ r)⁻¹)) =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
    field_simp
    ring
  exact mul_left_cancel₀ hden (e.trans key.symm)

/-- Galí (2015), p. 75, fn. 14 (backward form, `η > 0`): for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`,
`A_b = A_M⁻¹` has exactly one eigenvalue in the open unit disc (namely `1/r`), two outside the
closed disc and none on the unit circle (with algebraic multiplicity over `ℂ`). -/
theorem Ab3_root_location {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Ab3 σ η β κ) ∧ stableCount (Ab3 σ η β κ) = 1 ∧ unstableCount (Ab3 σ η β κ) = 2 := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ.le hη.le hκ hβ0.le hβ1 hr1 hr
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hv0
    have := mul_pos (mul_pos hσ hη) hβ0
    linarith
  set R := ((quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r)
    (quadQ0 σ η β κ r)⁻¹).map Complex.ofRealHom).roots with hRdef
  have hRout : ∀ μ ∈ R, 1 < ‖μ‖ := fun μ hμ => norm_gt_one_of_recip hS hq0 hμ
  have he : eigs (Ab3 σ η β κ) = {((r⁻¹ : ℝ) : ℂ)} + R := by
    have hne : ((Ab3 σ η β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_Ab3_factor hσ.ne' hη.ne' hβ0.ne' hb hr, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hr0 : 0 < r := by linarith
  have hrlt : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hra : |r⁻¹| = r⁻¹ := abs_of_pos (inv_pos.mpr hr0)
  have hcard : Multiset.card R = 2 := by
    have h3 := card_eigs (Ab3 σ η β κ)
    rw [he, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at h3
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · rw [Complex.norm_real, Real.norm_eq_abs, hra]; exact hrlt.ne
    · exact (hRout μ hμ).ne'
  · rw [stableCount, he, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hRout μ hμ).le), add_zero,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt]
  · rw [unstableCount, he, Multiset.filter_add, Multiset.filter_eq_self.mpr hRout,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt.le, hcard]

/-- Galí (2015), p. 75: the relabelling of `Fin 3` as `Fin 2 ⊕ Fin 1`: `ỹ_t, π_t`
non-predetermined (`Sum.inl 0`, `Sum.inl 1`), `l̂_{t−1}` predetermined (`Sum.inr 0`). -/
abbrev eS : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75: the backward matrix on the split state `Fin 2 ⊕ Fin 1`. -/
noncomputable def Abk (σ η β κ : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  (Ab3 σ η β κ).submatrix eS eS

/-- Galí (2015), p. 75: a real eigenvector of the pencil for the root `r`:
`A_{M,1} v = r A_{M,0} v` with `v = ((r − β)(r − 1), rκ(r − 1), r²κ)`. -/
def eigv3 (β κ r : ℝ) : Fin 3 → ℝ := ![(r - β) * (r - 1), r * κ * (r - 1), r ^ 2 * κ]

/-- Galí (2015), p. 75: `A_{M,1} v = r A_{M,0} v` when `f(r) = 0`. -/
theorem pencil_eigvec {σ η β κ r : ℝ} (hr : charCubic σ η β κ r = 0) :
    AM1 σ η β *ᵥ eigv3 β κ r = r • (AM0 σ η κ *ᵥ eigv3 β κ r) := by
  unfold charCubic at hr
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    linear_combination hr
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring

/-- Galí (2015), p. 75: `A_b v = r⁻¹ v` (the stable eigenvector of the backward matrix). -/
theorem Ab3_eigvec {σ η β κ r : ℝ} (hu : IsUnit (AM1 σ η β).det) (hr0 : r ≠ 0)
    (hr : charCubic σ η β κ r = 0) : Ab3 σ η β κ *ᵥ eigv3 β κ r = r⁻¹ • eigv3 β κ r := by
  have h := pencil_eigvec (σ := σ) (η := η) hr
  have h0 : AM0 σ η κ *ᵥ eigv3 β κ r = r⁻¹ • (AM1 σ η β *ᵥ eigv3 β κ r) := by
    rw [h, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [Ab3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- Galí (2015), p. 75: the eigenvalues of the split backward matrix are those of `A_b`. -/
theorem eigs_Abk (σ η β κ : ℝ) : eigs (Abk σ η β κ) = eigs (Ab3 σ η β κ) :=
  eigs_submatrix_equiv eS _

/-- Galí (2015), p. 75, fn. 14 (`η > 0`): the Blanchard–Kahn conditions for (34): no eigenvalue
of the backward matrix on the unit circle, exactly one (= the number of predetermined variables)
in the open unit disc, and genericity (the stable eigenvector moves real balances). -/
theorem Abk_bk_conditions {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Abk σ η β κ) ∧ stableCount (Abk σ η β κ) = Fintype.card (Fin 1) ∧
      GenericX (Abk σ η β κ) := by
  obtain ⟨hnu, hs, -⟩ := Ab3_root_location hσ hη hκ hβ0 hβ1
  have hnu' : NoUnit (Abk σ η β κ) := by unfold NoUnit; rw [eigs_Abk]; exact hnu
  have hs' : stableCount (Abk σ η β κ) = 1 := by unfold stableCount; rw [eigs_Abk]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hr0 : 0 < r := by linarith
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hev : Abk σ η β κ *ᵥ (eigv3 β κ r ∘ eS) = r⁻¹ • (eigv3 β κ r ∘ eS) := by
    rw [Abk, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, Ab3_eigvec hu hr0.ne' hr]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := r⁻¹) ?_ hev (j := 0) ?_
  · rw [abs_of_pos (inv_pos.mpr hr0)]; exact inv_lt_one_of_one_lt₀ hr1
  · change r ^ 2 * κ ≠ 0
    positivity

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`)**: the backward form of (34) is determinate, in the
strong Blanchard–Kahn sense: for EVERY bounded adapted forcing vector and every initial real
balance there is exactly one bounded equilibrium, for any expectation system. -/
theorem Abk_determinate {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : Determinate 𝔼 (Abk σ η β κ) := by
  obtain ⟨hnu, hs, hg⟩ := Abk_bk_conditions hσ hη hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-! ### `η > 0`: from the state-space form back to (34) -/

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t; l̂_{t−1})` as a vector process on
the split index `Fin 2 ⊕ Fin 1`. -/
def yvec (ygap infl L : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![ygap t, infl t, L t] (eS k)

/-- Galí (2015), eq. (34), p. 75: the shock vector `s_t = (r̂ⁿ_t, ŷⁿ_t, Δm_t)` as a vector
process. -/
def svec (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ := fun t => ![rn t, yn t, dm t]

/-- Galí (2015), eq. (34), p. 75: the forcing `−A_{M,1}⁻¹ B_M s_t` of the backward form. -/
noncomputable def wvec (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => mv (-((AM1 σ η β)⁻¹ * BM η)) (svec rn yn dm t) (eS k)

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the state vector at an outcome, relabelled. -/
theorem yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => yvec ygap infl L t k ω) = stateVec ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, stateVec]
  generalize eS k = i
  fin_cases i <;> rfl

/-- Galí (2015), p. 75 (tool): the forecast vector at an outcome, relabelled. -/
theorem E_yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) = expVec 𝔼 ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, expVec]
  generalize eS k = i
  fin_cases i <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the forcing at an outcome, relabelled. -/
theorem wvec_apply (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => wvec σ η β rn yn dm t k ω) =
      ((-((AM1 σ η β)⁻¹ * BM η)) *ᵥ shockVec rn yn dm t ω) ∘ eS := by
  funext k
  simp only [Function.comp, wvec, mv_apply]
  congr 2
  funext j
  fin_cases j <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the split backward matrix acting on a state, relabelled. -/
theorem mv_Abk_apply (σ η β κ : ℝ) (a : Fin 2 ⊕ Fin 1 → Ω → ℝ) (ω : Ω) :
    (fun k => mv (Abk σ η β κ) a k ω) = (Ab3 σ η β κ *ᵥ ((fun k => a k ω) ∘ eS.symm)) ∘ eS := by
  funext k
  rw [mv_apply, Abk, Matrix.submatrix_mulVec_equiv]

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible,
`E = A_b x − A_{M,1}⁻¹ B_M s` iff `A_{M,0} x = A_{M,1} E + B_M s`. -/
theorem backward_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (x Ex s : Fin 3 → ℝ) :
    Ex = Ab3 σ η β κ *ᵥ x + (-((AM1 σ η β)⁻¹ * BM η)) *ᵥ s ↔
      AM0 σ η κ *ᵥ x = AM1 σ η β *ᵥ Ex + BM η *ᵥ s := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_neg,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.neg_mulVec]
    abel
  · intro h
    have hE : Ex = (AM1 σ η β)⁻¹ *ᵥ (AM1 σ η β *ᵥ Ex) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have h1 : AM1 σ η β *ᵥ Ex = AM0 σ η κ *ᵥ x - BM η *ᵥ s := by rw [h]; abel
    rw [hE, h1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.neg_mulVec, sub_eq_add_neg]

/-- Galí (2015), eq. (34), p. 75 (`η > 0`): the backward state-space system holds iff (34) holds. -/
theorem solves_Abk_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (yvec ygap infl L) ↔
      System34 𝔼 σ η β κ ygap infl L rn yn dm := by
  have key : ∀ t ω, (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
      mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
      (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
        (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω) := by
    intro t ω
    rw [← backward_iff hu]
    have hfun : (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
        mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
        (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) =
          (fun k => mv (Abk σ η β κ) (yvec ygap infl L t) k ω) +
            (fun k => wvec σ η β rn yn dm t k ω) :=
      ⟨fun h => funext h, fun h k => congrFun h k⟩
    rw [hfun, E_yvec_apply, mv_Abk_apply, wvec_apply, yvec_apply, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id, ← Pi.add_comp]
    exact eS.surjective.injective_comp_right.eq_iff
  constructor
  · intro h t ω
    exact (key t ω).mp fun k => congrFun (h t k) ω
  · intro h t k
    funext ω
    exact (key t ω).mpr (h t ω) k

/-- Galí (2015), eq. (34), p. 75: a bounded equilibrium of (34) with predetermined real balances
starting at `l̂_{−1} = L0`: (34) holds, `l̂_t` is known at `t`, all three variables are adapted
and bounded. -/
def Equil34 (σ η β κ L0 : ℝ) (rn yn dm ygap infl L : ℕ → Ω → ℝ) : Prop :=
  System34 𝔼 σ η β κ ygap infl L rn yn dm ∧ Predetermined 𝔼 L ∧ L 0 = (fun _ => L0) ∧
    𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L ∧
    BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L

/-- Galí (2015), p. 75 (`η > 0`): equilibria of the backward state-space form are exactly the
bounded equilibria of (34). -/
theorem equil_Abk_iff {σ η β κ L0 : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Equil 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (fun _ => L0) (yvec ygap infl L) ↔
      Equil34 𝔼 σ η β κ L0 rn yn dm ygap infl L := by
  have hA : AdaptedV 𝔼 (yvec ygap infl L) ↔
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L := by
    constructor
    · intro h
      exact ⟨fun t => h t (Sum.inl 0), fun t => h t (Sum.inl 1), fun t => h t (Sum.inr 0)⟩
    · rintro ⟨h1, h2, h3⟩ t k
      rcases k with i | j
      · fin_cases i
        · exact h1 t
        · exact h2 t
      · fin_cases j
        exact h3 t
  have hK : (∀ t (j : Fin 1), 𝔼.E t (yvec ygap infl L (t + 1) (Sum.inr j)) =
      yvec ygap infl L (t + 1) (Sum.inr j)) ↔ Predetermined 𝔼 L := by
    constructor
    · intro h t
      exact h t 0
    · intro h t j
      fin_cases j
      exact h t
  have hI : (∀ j : Fin 1, yvec ygap infl L 0 (Sum.inr j) = fun _ => (fun _ => L0) j) ↔
      L 0 = fun _ => L0 := by
    constructor
    · intro h
      exact h 0
    · intro h j
      fin_cases j
      exact h
  have hB : BoundedV (yvec ygap infl L) ↔
      BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L := by
    constructor
    · rintro ⟨M, hM⟩
      exact ⟨⟨M, fun t ω => hM t (Sum.inl 0) ω⟩, ⟨M, fun t ω => hM t (Sum.inl 1) ω⟩,
        ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩⟩
    · rintro ⟨⟨M1, h1⟩, ⟨M2, h2⟩, ⟨M3, h3⟩⟩
      refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
      rcases k with i | j
      · fin_cases i
        · exact (h1 t ω).trans (le_max_left _ _)
        · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
      · fin_cases j
        exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold Equil Equil34
  rw [solves_Abk_iff 𝔼 hu, hA, hK, hI, hB]
  tauto

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): bounded shocks give a bounded shock vector. -/
theorem svec_boundedV {rn yn dm : ℕ → Ω → ℝ} (h1 : BoundedProc rn) (h2 : BoundedProc yn)
    (h3 : BoundedProc dm) : BoundedV (svec rn yn dm) := by
  obtain ⟨M1, h1⟩ := h1
  obtain ⟨M2, h2⟩ := h2
  obtain ⟨M3, h3⟩ := h3
  refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
  fin_cases k
  · exact (h1 t ω).trans (le_max_left _ _)
  · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Galí (2015), p. 75 (tool): adapted shocks give an adapted shock vector. -/
theorem svec_adaptedV {rn yn dm : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted rn) (h2 : 𝔼.Adapted yn)
    (h3 : 𝔼.Adapted dm) : AdaptedV 𝔼 (svec rn yn dm) := by
  intro t k
  fin_cases k
  · exact h1 t
  · exact h2 t
  · exact h3 t

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`), PROVED**: for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium with predetermined real
balances. -/
theorem system34_existsUnique_pos {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hwb : BoundedV (wvec σ η β rn yn dm) := by
    obtain ⟨B, hB⟩ := boundedV_mv (-((AM1 σ η β)⁻¹ * BM η)) (svec_boundedV hrnb hynb hdmb)
    exact ⟨B, fun t k ω => hB t (eS k) ω⟩
  have hwa : AdaptedV 𝔼 (wvec σ η β rn yn dm) := fun t k =>
    adaptedV_mv 𝔼 (-((AM1 σ η β)⁻¹ * BM η)) (svec_adaptedV 𝔼 hrna hyna hdma) t (eS k)
  obtain ⟨y, hy, huniq⟩ := Abk_determinate 𝔼 hσ hη hκ hβ0 hβ1 _ hwb hwa (fun _ => L0)
  have hyv : yvec (fun t => y t (Sum.inl 0)) (fun t => y t (Sum.inl 1))
      (fun t => y t (Sum.inr 0)) = y := by
    funext t k
    rcases k with i | j
    · fin_cases i <;> rfl
    · fin_cases j; rfl
  refine ⟨(fun t => y t (Sum.inl 0), fun t => y t (Sum.inl 1), fun t => y t (Sum.inr 0)),
    ?_, ?_⟩
  · exact (equil_Abk_iff 𝔼 hu).mp (by rw [hyv]; exact hy)
  · rintro ⟨a, b, c⟩ hv
    have h := huniq _ ((equil_Abk_iff 𝔼 hu).mpr hv)
    rw [← h]
    rfl

/-! ### `η = 0`: the reduced two-variable system -/

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the backward matrix of the reduced system in
`(π_t; l̂_{t−1})`, `[[(1+κ)/β, −κ/β], [−1, 1]]`. -/
noncomputable def B2f (β κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(1 + κ) / β, -κ / β; -1, 1]

/-- Galí (2015), p. 75: the relabelling of `Fin 2` as `Fin 1 ⊕ Fin 1` (`π_t` non-predetermined,
`l̂_{t−1}` predetermined). -/
abbrev eS2 : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the reduced backward matrix on `Fin 1 ⊕ Fin 1`. -/
noncomputable def B2 (β κ : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  (B2f β κ).submatrix eS2 eS2

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the stable root `ρ₁ ∈ (0, 1)` of
`β ρ² − (1 + β + κ) ρ + 1 = 0` (IVT: the left side is `1` at `0` and `−κ` at `1`). -/
theorem exists_rho1 {β κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0 := by
  have hcont : ContinuousOn (fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) (Set.Icc 0 1) := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 1)
      ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 0) := by
    simp only [Set.mem_Ioo]
    constructor <;> nlinarith
  obtain ⟨z, ⟨hz0, hz1⟩, hz⟩ := intermediate_value_Ioo' zero_le_one hcont hmem
  exact ⟨z, hz0, hz1, hz⟩

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the characteristic polynomial of the reduced matrix is
`(X − ρ₁)(X − 1/(βρ₁))`. -/
theorem charpoly_B2f {β κ ρ : ℝ} (hβ : β ≠ 0) (hρ0 : ρ ≠ 0)
    (hρ : β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0) :
    (B2f β κ).charpoly = (X - C ρ) * (X - C (1 / (β * ρ))) := by
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.det_fin_two]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  simp [B2f, Matrix.scalar_apply]
  field_simp
  linear_combination z * hρ

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the reduced matrix has one eigenvalue `ρ₁ ∈ (0, 1)`, one
eigenvalue `1/(βρ₁) > 1`, none on the unit circle. -/
theorem B2f_root_location {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2f β κ) ∧ stableCount (B2f β κ) = 1 := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hβρ : β * ρ < 1 := by nlinarith
  have hρ2 : 1 < 1 / (β * ρ) := one_lt_one_div (by positivity) hβρ
  have he : eigs (B2f β κ) = {(ρ : ℂ)} + {((1 / (β * ρ) : ℝ) : ℂ)} := by
    have hne : ((B2f β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_B2f hβ0.ne' hρ0.ne' hρ, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hn1 : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hn2 : ‖((1 / (β * ρ) : ℝ) : ℂ)‖ = 1 / (β * ρ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | rfl
    · rw [hn1]; exact hρ1.ne
    · rw [hn2]; exact hρ2.ne'
  · have hlt2 : ¬ 1 / (β * ρ) < 1 := not_lt.mpr hρ2.le
    rw [stableCount, he, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton]
    simp only [hn1, hn2, hρ1, hlt2, ↓reduceIte, Multiset.card_add, Multiset.card_singleton,
      Multiset.empty_eq_zero, Multiset.card_zero]

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the Blanchard–Kahn conditions for the reduced system: no
eigenvalue on the unit circle, exactly one in the open disc, genericity (the stable eigenvector
`(1 − ρ₁, 1)` moves real balances). -/
theorem B2_bk_conditions {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2 β κ) ∧ stableCount (B2 β κ) = Fintype.card (Fin 1) ∧ GenericX (B2 β κ) := by
  obtain ⟨hnu, hs⟩ := B2f_root_location hκ hβ0 hβ1
  have heq : eigs (B2 β κ) = eigs (B2f β κ) := eigs_submatrix_equiv eS2 _
  have hnu' : NoUnit (B2 β κ) := by unfold NoUnit; rw [heq]; exact hnu
  have hs' : stableCount (B2 β κ) = 1 := by unfold stableCount; rw [heq]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hv : B2f β κ *ᵥ ![1 - ρ, 1] = ρ • ![1 - ρ, 1] := by
    funext i
    fin_cases i
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      linear_combination hρ
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hev : B2 β κ *ᵥ (![1 - ρ, 1] ∘ eS2) = ρ • (![1 - ρ, 1] ∘ eS2) := by
    rw [B2, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, hv]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := ρ) ?_ hev (j := 0) ?_
  · rw [abs_of_pos hρ0]; exact hρ1
  · change (1 : ℝ) ≠ 0
    exact one_ne_zero

/-- **Galí (2015), p. 75 (`η = 0`)**: the reduced backward system is determinate for every
bounded adapted forcing vector, for any expectation system. -/
theorem B2_determinate {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Determinate 𝔼 (B2 β κ) := by
  obtain ⟨hnu, hs, hg⟩ := B2_bk_conditions hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced state `(π_t; l̂_{t−1})`. -/
def y2 (infl L : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ := fun t k => ![infl t, L t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced forcing
`((κ/β)(ŷⁿ_t − Δm_t); Δm_t)`. -/
noncomputable def w2 (β κ : ℝ) (yn dm : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![(κ / β) • (yn t - dm t), dm t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced system, written out:
`E_t π_{t+1} = ((1+κ)/β) π_t − (κ/β) l̂_{t−1} + (κ/β)(ŷⁿ_t − Δm_t)` and
`E_t l̂_t = −π_t + l̂_{t−1} + Δm_t`. -/
theorem solves_B2_iff {β κ : ℝ} {infl L yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (B2 β κ) (w2 β κ yn dm) (y2 infl L) ↔
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have h0 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inl 0) ω =
      (1 + κ) / β * infl t ω + -κ / β * L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  have h1 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inr 0) ω = -infl t ω + L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  constructor
  · intro h
    refine ⟨fun t ω => ?_, fun t ω => ?_⟩
    · have := congrFun (h t (Sum.inl 0)) ω
      rw [Pi.add_apply, h0] at this
      exact this
    · have := congrFun (h t (Sum.inr 0)) ω
      rw [Pi.add_apply, h1] at this
      exact this
  · rintro ⟨ha, hb⟩ t k
    funext ω
    rcases k with i | j
    · fin_cases i
      rw [Pi.add_apply]
      have := h0 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact ha t ω
    · fin_cases j
      rw [Pi.add_apply]
      have := h1 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact hb t ω

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): with predetermined real balances, (34) is the static
equation `ỹ_t = l̂_t − ŷⁿ_t` together with the reduced two-variable system. -/
theorem system34_zero_iff {σ β κ : ℝ} (hβ : β ≠ 0) {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ 0 β κ ygap infl L rn yn dm ↔
      (∀ t, ygap t = L (t + 1) - yn t) ∧
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have e1 : ∀ x l s : ℝ, β * ((1 + κ) / β * x + -κ / β * l + κ / β * s) =
      (1 + κ) * x - κ * l + κ * s := by
    intro x l s
    field_simp
    ring
  constructor
  · intro h
    have hrow : ∀ t ω, ygap t ω = L (t + 1) ω - yn t ω ∧
        -κ * ygap t ω + infl t ω = β * 𝔼.E t (infl (t + 1)) ω ∧
        -infl t ω + L t ω = L (t + 1) ω - dm t ω := by
      intro t ω
      have h0 := congrFun (h t ω) 0
      have h1 := congrFun (h t ω) 1
      have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 h1 h2
      refine ⟨by linarith, by linarith, by linarith⟩
    refine ⟨fun t => funext fun ω => (hrow t ω).1, fun t ω => ?_, fun t ω => ?_⟩
    · obtain ⟨a, b, c⟩ := hrow t ω
      apply mul_left_cancel₀ hβ
      rw [e1]
      linear_combination -b - κ * a + κ * c
    · have hLω := congrFun (hL t) ω
      obtain ⟨-, -, c⟩ := hrow t ω
      linarith
  · rintro ⟨ha, hb, hc⟩ t ω
    have a := congrFun (ha t) ω
    have b := hb t ω
    have c := hc t ω
    have hLω := congrFun (hL t) ω
    have b' : β * 𝔼.E t (infl (t + 1)) ω =
        (1 + κ) * infl t ω - κ * L t ω + κ * (yn t ω - dm t ω) := by rw [b, e1]
    simp only [Pi.sub_apply] at a
    funext j
    fin_cases j
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linear_combination (-κ) * a - b' + κ * hLω - κ * c
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith

/-- **Galí (2015), p. 75, fn. 14 (`η = 0`), PROVED**: with an interest-inelastic money demand
(`η = 0`, allowed in Galí, Ch. 2, p. 21), `κ > 0`, `0 < β ≤ 1`, any `σ`, any expectation system,
bounded adapted shocks and any initial real balance, (34) has exactly one bounded adapted
equilibrium with predetermined real balances (the natural rate `r̂ⁿ` does not enter). -/
theorem system34_existsUnique_zero {σ β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {rn yn dm : ℕ → Ω → ℝ} (hynb : BoundedProc yn) (hdmb : BoundedProc dm)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ 0 β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  obtain ⟨My, hMy⟩ := hynb
  obtain ⟨Md, hMd⟩ := hdmb
  have hwb : BoundedV (w2 β κ yn dm) := by
    refine ⟨|κ / β| * (My + Md) + Md, fun t k ω => ?_⟩
    have hd0 : 0 ≤ Md := (abs_nonneg _).trans (hMd 0 ω)
    have hk : 0 ≤ |κ / β| * (My + Md) := by
      have : 0 ≤ My := (abs_nonneg _).trans (hMy 0 ω)
      positivity
    rcases k with i | j
    · fin_cases i
      change |(κ / β) * (yn t ω - dm t ω)| ≤ _
      rw [abs_mul]
      have : |yn t ω - dm t ω| ≤ My + Md :=
        (abs_sub _ _).trans (add_le_add (hMy t ω) (hMd t ω))
      nlinarith [abs_nonneg (κ / β)]
    · fin_cases j
      change |dm t ω| ≤ _
      linarith [hMd t ω]
  have hwa : AdaptedV 𝔼 (w2 β κ yn dm) := by
    intro t k
    rcases k with i | j
    · fin_cases i
      change 𝔼.E t ((κ / β) • (yn t - dm t)) = (κ / β) • (yn t - dm t)
      rw [map_smul, map_sub, hyna t, hdma t]
    · fin_cases j
      exact hdma t
  obtain ⟨y, ⟨hs, ha, hk, hi, hb⟩, huniq⟩ :=
    B2_determinate 𝔼 hκ hβ0 hβ1 (w2 β κ yn dm) hwb hwa (fun _ => L0)
  set infl : ℕ → Ω → ℝ := fun t => y t (Sum.inl 0) with hinfl
  set L : ℕ → Ω → ℝ := fun t => y t (Sum.inr 0) with hLdef
  have hyv : y2 infl L = y := by
    funext t k
    rcases k with i | j
    · fin_cases i; rfl
    · fin_cases j; rfl
  have hpred : Predetermined 𝔼 L := fun t => hk t 0
  rw [← hyv, solves_B2_iff] at hs
  refine ⟨(fun t => L (t + 1) - yn t, infl, L), ⟨?_, hpred, hi 0, ?_, fun t => ha t (Sum.inl 0),
    fun t => ha t (Sum.inr 0), ?_, ?_, ?_⟩, ?_⟩
  · exact (system34_zero_iff 𝔼 hβ0.ne' hpred).mpr ⟨fun t => rfl, hs.1, hs.2⟩
  · intro t
    change 𝔼.E t (L (t + 1) - yn t) = L (t + 1) - yn t
    rw [map_sub, hpred t, hyna t]
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + My, fun t ω => ?_⟩
    change |L (t + 1) ω - yn t ω| ≤ _
    exact (abs_sub _ _).trans (add_le_add (hM (t + 1) (Sum.inr 0) ω) (hMy t ω))
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inl 0) ω⟩
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩
  · rintro ⟨g', i', L'⟩ ⟨hsys, hpred', hL0, -, hai, haL, -, hbi, hbL⟩
    obtain ⟨hg, ha', hb'⟩ := (system34_zero_iff 𝔼 hβ0.ne' hpred').mp hsys
    have heq : y2 i' L' = y := by
      refine huniq _ ⟨(solves_B2_iff 𝔼).mpr ⟨ha', hb'⟩, ?_, ?_, ?_, ?_⟩
      · intro t k
        rcases k with i | j
        · fin_cases i; exact hai t
        · fin_cases j; exact haL t
      · intro t j
        fin_cases j
        exact hpred' t
      · intro j
        fin_cases j
        exact hL0
      · obtain ⟨M1, h1⟩ := hbi
        obtain ⟨M2, h2⟩ := hbL
        refine ⟨max M1 M2, fun t k ω => ?_⟩
        rcases k with i | j
        · fin_cases i; exact (h1 t ω).trans (le_max_left _ _)
        · fin_cases j; exact (h2 t ω).trans (le_max_right _ _)
    have hi' : i' = infl := funext fun t => congrFun (congrFun heq t) (Sum.inl 0)
    have hL' : L' = L := funext fun t => congrFun (congrFun heq t) (Sum.inr 0)
    subst hi' hL'
    have hg' : g' = fun t => L (t + 1) - yn t := funext hg
    rw [hg']

/-- **Galí (2015), p. 75 and fn. 14, PROVED** ("the equilibrium is always determined under an
exogenous path for the money supply"): for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium `(ỹ, π, l̂)` with real
balances predetermined. -/
theorem system34_existsUnique {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  rcases hη.lt_or_eq with h | h
  · exact system34_existsUnique_pos 𝔼 hσ h hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
  · subst h
    exact system34_existsUnique_zero 𝔼 hκ hβ0 hβ1 hynb hdmb hyna hdma L0

end Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 4.4(c): the money supply rule implements the optimum uniquely

Galí (2015), Chapter 4, Exercise 4.4(c), p. 123. Under the money supply rule
`m_t = p* + yⁿ_t − η rⁿ_t`, the optimal outcome `ỹ = π = 0`, `p = p*`, `i = rⁿ` is an equilibrium
(`Ex4_4.moneyRule_equilibrium`). This module proves that it is the ONLY bounded equilibrium,
the claim recorded (and deferred) as `Ex4_4.MoneyRuleUniqueness`.

## The reduction to (34)

With real balances measured from target, `l̂_{t−1} = p* − p_{t−1}` (`realBal`, so `l̂_{−1} = 0`),
money demand and the rule give `η (i_t − rⁿ_t) = ỹ_t − l̂_t`, and the IS equation, the Phillips
curve and the price-level identity become EXACTLY the Chapter 3 system (34) with all shocks set
to zero (`system34_of_moneyRule`): the natural-rate and natural-output terms cancel. The
Chapter 3 determinacy theorem (`MoneyRuleDeterminacy.system34_existsUnique`, restated in this
project) then says the bounded equilibrium of (34) with `l̂_{−1} = 0` is unique; the zero path is
one, so `ỹ = π = 0`.

## Main results

* `system34_of_moneyRule`: every equilibrium under the money rule solves (34) with zero shocks.
* `moneyRule_gap_infl_zero`, `moneyRuleUniqueness_holds`: **`Ex4_4.MoneyRuleUniqueness`
  holds** for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, for any expectation system (the boundedness
  of `rⁿ`, `yⁿ` is not even needed).
* `moneyRule_unique_outcome`, `moneyRule_implements_uniquely`: every bounded equilibrium under the
  rule has `ỹ = π = 0`, `p_t = p*`, `i_t = rⁿ_t`, and this outcome is an equilibrium.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_4Determinacy

open Ex4_4 MoneyRuleSystem MoneyRuleDeterminacy

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 4.4(c), p. 123: real balances measured from target,
`l̂_{t−1} = p* − p_{t−1}` (so `l̂_{−1} = 0` and `l̂_t = p* − p_t`). -/
def realBal (pstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => pstar) - lagP pstar p t

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): `l̂_{−1} = 0`. -/
theorem realBal_zero (pstar : ℝ) (p : ℕ → Ω → ℝ) : realBal pstar p 0 = fun _ => 0 := by
  funext ω
  simp [realBal, lagP]

/-- Galí (2015), Ex. 4.4: the lagged price level `p_{t−1}` is adapted when `p` is. -/
theorem lagP_adapted {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    𝔼.Adapted (lagP pstar p) := by
  intro t
  cases t with
  | zero => exact 𝔼.const 0 pstar
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    calc 𝔼.E (t + 1) (p t) = 𝔼.E (t + 1) (𝔼.E t (p t)) := by rw [hp t]
      _ = 𝔼.E t (p t) := 𝔼.known (Nat.le_succ t) _
      _ = p t := hp t

omit 𝔼 in
/-- Galí (2015), Ex. 4.4: the lagged price level is bounded when `p` is. -/
theorem lagP_bounded {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : BoundedProc p) :
    BoundedProc (lagP pstar p) := by
  obtain ⟨M, hM⟩ := hp
  refine ⟨max M |pstar|, fun t ω => ?_⟩
  cases t with
  | zero => exact le_max_right _ _
  | succ t => exact (hM t ω).trans (le_max_left _ _)

/-- Galí (2015), Ex. 4.4(c): real balances `l̂_t = p* − p_t` are known at `t` (predetermined). -/
theorem realBal_pred {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    Predetermined 𝔼 (realBal pstar p) := by
  intro t
  change 𝔼.E t ((fun _ => pstar) - p t) = (fun _ => pstar) - p t
  rw [map_sub, 𝔼.const, hp t]

/-- Galí (2015), Ex. 4.4(c): real balances are adapted. -/
theorem realBal_adapted {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    𝔼.Adapted (realBal pstar p) := by
  intro t
  change 𝔼.E t ((fun _ => pstar) - lagP pstar p t) = (fun _ => pstar) - lagP pstar p t
  rw [map_sub, 𝔼.const, lagP_adapted 𝔼 hp t]

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): real balances are bounded. -/
theorem realBal_bounded {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : BoundedProc p) :
    BoundedProc (realBal pstar p) := by
  obtain ⟨M, hM⟩ := lagP_bounded (pstar := pstar) hp
  refine ⟨|pstar| + M, fun t ω => ?_⟩
  change |pstar - lagP pstar p t ω| ≤ _
  exact (abs_sub _ _).trans (add_le_add le_rfl (hM t ω))

/-- Galí (2015), Ex. 4.4: inflation `π_t = p_t − p_{t−1}` is adapted when `p` is. -/
theorem infl_adapted {pstar : ℝ} {p infl : ℕ → Ω → ℝ} (hpl : PriceLevel pstar p infl)
    (hp : 𝔼.Adapted p) : 𝔼.Adapted infl := by
  intro t
  rw [hpl t, map_sub, hp t, lagP_adapted 𝔼 hp t]

omit 𝔼 in
/-- Galí (2015), Ex. 4.4: inflation is bounded when `p` is. -/
theorem infl_bounded {pstar : ℝ} {p infl : ℕ → Ω → ℝ} (hpl : PriceLevel pstar p infl)
    (hp : BoundedProc p) : BoundedProc infl := by
  obtain ⟨M, hM⟩ := hp
  obtain ⟨M', hM'⟩ := lagP_bounded (pstar := pstar) ⟨M, hM⟩
  refine ⟨M + M', fun t ω => ?_⟩
  rw [hpl t, Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))

/-- **Galí (2015), Ex. 4.4(c), p. 123 (reduction)**: every equilibrium under the money rule
`m_t = p* + yⁿ_t − η rⁿ_t` (with an adapted price level and `σ ≠ 0`) solves the Chapter 3 system
(34) for `(ỹ_t, π_t, l̂_{t−1} = p* − p_{t−1})` with ALL shocks equal to zero. -/
theorem system34_of_moneyRule {β σ κ η pstar : ℝ} (hσ : σ ≠ 0)
    {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hp : 𝔼.Adapted p) :
    System34 𝔼 σ η β κ ygap infl (realBal pstar p) 0 0 0 := by
  obtain ⟨⟨hD, hN⟩, hPL, hMD⟩ := h
  intro t ω
  have hd := congrFun (hD t) ω
  have hn := congrFun (hN t) ω
  have hpl := congrFun (hPL t) ω
  have hmd := congrFun (hMD t) ω
  have hr := congrFun (hm t) ω
  have hEL : 𝔼.E t (realBal pstar p (t + 1)) ω = pstar - p t ω := by
    rw [realBal_pred 𝔼 hp t]
    rfl
  have hRt : realBal pstar p t ω = pstar - lagP pstar p t ω := rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hd hn hpl hmd hr
  have hd' : σ * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω -
      (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
    rw [hd, mul_sub, ← mul_assoc, mul_inv_cancel₀ hσ, one_mul]
  funext j
  fin_cases j
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linear_combination η * hd' - hmd + hr - hEL
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linarith
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linarith

/-- Galí (2015), Ex. 4.4(c): the zero path solves (34) with zero shocks and `l̂_{−1} = 0`. -/
theorem equil34_zero (σ η β κ : ℝ) :
    Equil34 𝔼 σ η β κ 0 0 0 0 (0 : ℕ → Ω → ℝ) 0 0 := by
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero (𝔼.E t)
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  refine ⟨?_, fun t => map_zero (𝔼.E t), rfl, hza, hza, hza, hzb, hzb, hzb⟩
  intro t ω
  funext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, stateVec, expVec, shockVec]

/-- **Galí (2015), Ex. 4.4(c), p. 123 — uniqueness**: for `σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β ≤ 1` and any expectation system, under the money rule `m_t = p* + yⁿ_t − η rⁿ_t` every
equilibrium with bounded adapted output gap and price level has `ỹ = π = 0` (for ANY shocks
`rⁿ`, `yⁿ`: they cancel from the reduced system). -/
theorem moneyRule_gap_infl_zero {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hag : 𝔼.Adapted ygap) (hap : 𝔼.Adapted p)
    (hbg : BoundedProc ygap) (hbp : BoundedProc p) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) := by
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero (𝔼.E t)
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨v, -, huniq⟩ := system34_existsUnique 𝔼 hσ hη hκ hβ0 hβ1 hzb hzb hzb hza hza hza 0
  have hpl := h.2.1
  have e1 := huniq (ygap, infl, realBal pstar p)
    ⟨system34_of_moneyRule 𝔼 hσ.ne' h hm hap, realBal_pred 𝔼 hap, realBal_zero pstar p, hag,
      infl_adapted 𝔼 hpl hap, realBal_adapted 𝔼 hap, hbg, infl_bounded hpl hbp,
      realBal_bounded hbp⟩
  have e0 := huniq (0, 0, 0) (equil34_zero 𝔼 σ η β κ)
  have e := e1.trans e0.symm
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1, e.2.1⟩

/-- **Galí (2015), Ex. 4.4(c), p. 123 — uniqueness, PROVED**: for `σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β ≤ 1` and any expectation system, the claim `Ex4_4.MoneyRuleUniqueness` (recorded without
proof in `Ex4_4`) holds. -/
theorem moneyRuleUniqueness_holds {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) : MoneyRuleUniqueness 𝔼 β σ κ η pstar :=
  fun _ _ _ _ _ _ _ _ _ _ _ h hm hag hap hbg hbp =>
    moneyRule_gap_infl_zero 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp

/-- **Galí (2015), Ex. 4.4(c), p. 123**: every bounded equilibrium under the money rule attains
the optimum: `ỹ = π = 0`, the price level stays at `p*`, and `i_t = rⁿ_t`. -/
theorem moneyRule_unique_outcome {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hag : 𝔼.Adapted ygap) (hap : 𝔼.Adapted p)
    (hbg : BoundedProc ygap) (hbp : BoundedProc p) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ (∀ t, p t = fun _ => pstar) ∧ i = rn := by
  obtain ⟨hg, hi⟩ := moneyRule_gap_infl_zero 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp
  subst hg hi
  exact ⟨rfl, rfl, price_level_const h.2.1, (zero_equilibrium_iff 𝔼 hσ.ne' rn i).mp h.1⟩

/-- **Galí (2015), Ex. 4.4(c), p. 123: the money rule implements the optimum UNIQUELY**: for
`σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, under `m_t = p* + yⁿ_t − η rⁿ_t` the optimal outcome
(`ỹ = π = 0`, `p = p*`, `i = rⁿ`) is an equilibrium, and every equilibrium with bounded adapted
output gap and price level is that outcome. -/
theorem moneyRule_implements_uniquely {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
        (fun t => (fun _ => pstar) + yn t - η • rn t) rn ∧
      ∀ ygap infl p m i : ℕ → Ω → ℝ,
        FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i →
        Ex4_4.MoneyRule η pstar rn yn m → 𝔼.Adapted ygap → 𝔼.Adapted p →
        BoundedProc ygap → BoundedProc p →
        ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ (∀ t, p t = fun _ => pstar) ∧ i = rn :=
  ⟨(moneyRule_equilibrium 𝔼 hσ.ne' rn yn).1, fun _ _ _ _ _ h hm hag hap hbg hbp =>
    moneyRule_unique_outcome 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp⟩

end Gali.MonetaryPolicyDesign.Ex4_4Determinacy

set_option linter.style.longLine false
#print axioms Gali.MonetaryPolicyDesign.SchurStable
#print axioms Gali.MonetaryPolicyDesign.disc
#print axioms Gali.MonetaryPolicyDesign.root₁
#print axioms Gali.MonetaryPolicyDesign.root₂
#print axioms Gali.MonetaryPolicyDesign.root_sum
#print axioms Gali.MonetaryPolicyDesign.root_prod
#print axioms Gali.MonetaryPolicyDesign.root_eq
#print axioms Gali.MonetaryPolicyDesign.normSq_root_of_neg
#print axioms Gali.MonetaryPolicyDesign.norm_root_of_nonneg
#print axioms Gali.MonetaryPolicyDesign.schurStable_iff_roots
#print axioms Gali.MonetaryPolicyDesign.chSeq
#print axioms Gali.MonetaryPolicyDesign.convSeq
#print axioms Gali.MonetaryPolicyDesign.convSeq_rec
#print axioms Gali.MonetaryPolicyDesign.chSeq_eq_convSeq
#print axioms Gali.MonetaryPolicyDesign.norm_convSeq_le
#print axioms Gali.MonetaryPolicyDesign.abs_chSeq_le
#print axioms Gali.MonetaryPolicyDesign.tendsto_chSeq
#print axioms Gali.MonetaryPolicyDesign.tr2
#print axioms Gali.MonetaryPolicyDesign.det2
#print axioms Gali.MonetaryPolicyDesign.tr2_eq_trace
#print axioms Gali.MonetaryPolicyDesign.det2_eq_det
#print axioms Gali.MonetaryPolicyDesign.sq_eq_cayleyHamilton
#print axioms Gali.MonetaryPolicyDesign.pow_succ_eq
#print axioms Gali.MonetaryPolicyDesign.abs_pow_entry_le
#print axioms Gali.MonetaryPolicyDesign.tendsto_pow_entry
#print axioms Gali.MonetaryPolicyDesign.BoundedSeq
#print axioms Gali.MonetaryPolicyDesign.homogeneous_iterate
#print axioms Gali.MonetaryPolicyDesign.abs_mulVec_le
#print axioms Gali.MonetaryPolicyDesign.homogeneous_eq_zero
#print axioms Gali.MonetaryPolicyDesign.eq_root_of_eq
#print axioms Gali.MonetaryPolicyDesign.exists_eigenvector
#print axioms Gali.MonetaryPolicyDesign.exists_bounded_homogeneous
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.mk
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.E
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.const
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.mono
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.tower
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.known
#print axioms Gali.MonetaryPolicyDesign.perfectForesight
#print axioms Gali.MonetaryPolicyDesign.BoundedProc
#print axioms Gali.MonetaryPolicyDesign.BoundedVec
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.Adapted
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.IsAR1
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.E_neg
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.E_smul
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.E_E_self
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.abs_E_le
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.bounded_E
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.ar1_iterate
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forward_iterate
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forward_unique
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forward_ar1_solves
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.E_tsum
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forwardSeries
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forwardSeries_summable
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forwardSeries_solves
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.eq_forwardSeries
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.Solves
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.AdaptedVec
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.system_iterate
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.system_unique
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.system_not_unique
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.Determinate
#print axioms Gali.MonetaryPolicyDesign.ExpectationSystem.determinate_iff
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinObs
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinTree
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinSystem
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.firstHeads
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinShock
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinAR1
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.MonetaryPolicyDesign.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.MonetaryPolicyDesign.Efficient.utilC
#print axioms Gali.MonetaryPolicyDesign.Efficient.disutilN
#print axioms Gali.MonetaryPolicyDesign.Efficient.periodUtility
#print axioms Gali.MonetaryPolicyDesign.Efficient.hasDerivAt_utilC
#print axioms Gali.MonetaryPolicyDesign.Efficient.hasDerivAt_disutilN
#print axioms Gali.MonetaryPolicyDesign.Efficient.antitoneOn_margUtil
#print axioms Gali.MonetaryPolicyDesign.Efficient.le_tangent
#print axioms Gali.MonetaryPolicyDesign.Efficient.utilC_le_tangent
#print axioms Gali.MonetaryPolicyDesign.Efficient.disutilN_tangent_le
#print axioms Gali.MonetaryPolicyDesign.Efficient.utilC_lt_utilC
#print axioms Gali.MonetaryPolicyDesign.Efficient.marginal_utilities
#print axioms Gali.MonetaryPolicyDesign.Efficient.mrs
#print axioms Gali.MonetaryPolicyDesign.Efficient.mpn
#print axioms Gali.MonetaryPolicyDesign.Efficient.hasDerivAt_output
#print axioms Gali.MonetaryPolicyDesign.Efficient.mpn_pos
#print axioms Gali.MonetaryPolicyDesign.Efficient.rpow_le_tangent
#print axioms Gali.MonetaryPolicyDesign.Efficient.eq_of_rpow_eq_tangent
#print axioms Gali.MonetaryPolicyDesign.Efficient.symWelfare
#print axioms Gali.MonetaryPolicyDesign.Efficient.effEmployment
#print axioms Gali.MonetaryPolicyDesign.Efficient.hasDerivAt_symWelfare
#print axioms Gali.MonetaryPolicyDesign.Efficient.mrs_mul_eq
#print axioms Gali.MonetaryPolicyDesign.Efficient.effExponent_pos
#print axioms Gali.MonetaryPolicyDesign.Efficient.effEmployment_pos
#print axioms Gali.MonetaryPolicyDesign.Efficient.mrs_sym_eq_mpn_iff
#print axioms Gali.MonetaryPolicyDesign.Efficient.symWelfare_le_of_foc
#print axioms Gali.MonetaryPolicyDesign.Efficient.foc_of_symWelfare_isMax
#print axioms Gali.MonetaryPolicyDesign.Efficient.symWelfare_isMax_iff_foc
#print axioms Gali.MonetaryPolicyDesign.Efficient.symWelfare_le_eff
#print axioms Gali.MonetaryPolicyDesign.Efficient.symWelfare_lt
#print axioms Gali.MonetaryPolicyDesign.Efficient.existsUnique_efficient
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.cesIndex
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.goodsOutput
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.aggConsumption
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.Feasible
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.goodsOutput_rpow
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.integrable_rpow
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.integral_rpow_le
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.q_mem
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.integral_goodsOutput_rpow
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.aggConsumption_eq
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.symmetric_index
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.aggConsumption_pos
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.aggConsumption_le
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.aggConsumption_eq_iff
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.feasible_const
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_const
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_le_symWelfare
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_eq_symWelfare_iff
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_lt_symWelfare
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_le_eff
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.welfare_lt_of_not_symmetric
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.planner_optimal_iff
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.planner_optimal_iff_effEmployment
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.planner_existsUnique
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.isProbabilityMeasure_unitInterval
#print axioms Gali.MonetaryPolicyDesign.Efficient.Goods.planner_optimal_iff_unitInterval
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.weightMeasure
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.weightMeasure_singleton
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.isProbabilityMeasure_weightMeasure
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.integral_weightMeasure
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.ae_weightMeasure_iff
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.feasible_of_nonneg
#print axioms Gali.MonetaryPolicyDesign.Efficient.Finite.planner_optimal_iff_finite
#print axioms Gali.MonetaryPolicyDesign.Distortions.markup
#print axioms Gali.MonetaryPolicyDesign.Distortions.one_lt_markup
#print axioms Gali.MonetaryPolicyDesign.Distortions.markup_pos
#print axioms Gali.MonetaryPolicyDesign.Distortions.markup_mul_r
#print axioms Gali.MonetaryPolicyDesign.Distortions.invDemand
#print axioms Gali.MonetaryPolicyDesign.Distortions.inverse_demand_iff
#print axioms Gali.MonetaryPolicyDesign.Distortions.firmProfit
#print axioms Gali.MonetaryPolicyDesign.Distortions.revConst
#print axioms Gali.MonetaryPolicyDesign.Distortions.revenue_eq
#print axioms Gali.MonetaryPolicyDesign.Distortions.marginal_revenue_eq
#print axioms Gali.MonetaryPolicyDesign.Distortions.hasDerivAt_profit
#print axioms Gali.MonetaryPolicyDesign.Distortions.foc_iff_price_rule
#print axioms Gali.MonetaryPolicyDesign.Distortions.profit_le_of_foc
#print axioms Gali.MonetaryPolicyDesign.Distortions.firm_optimal_iff
#print axioms Gali.MonetaryPolicyDesign.Distortions.firmEmployment
#print axioms Gali.MonetaryPolicyDesign.Distortions.firm_existsUnique
#print axioms Gali.MonetaryPolicyDesign.Distortions.optimal_identical
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_price_rule
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_mrs
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_mrs_lt_mpn
#print axioms Gali.MonetaryPolicyDesign.Distortions.flexEmployment
#print axioms Gali.MonetaryPolicyDesign.Distortions.flexEmployment_pos
#print axioms Gali.MonetaryPolicyDesign.Distortions.mrs_eq_mpn_div_iff
#print axioms Gali.MonetaryPolicyDesign.Distortions.existsUnique_flex
#print axioms Gali.MonetaryPolicyDesign.Distortions.flexEmployment_one
#print axioms Gali.MonetaryPolicyDesign.Distortions.flexEmployment_lt_eff
#print axioms Gali.MonetaryPolicyDesign.Distortions.eff_lt_flexEmployment
#print axioms Gali.MonetaryPolicyDesign.Distortions.flexEmployment_eq_eff_iff
#print axioms Gali.MonetaryPolicyDesign.Distortions.mrs_sym_strictMonoOn
#print axioms Gali.MonetaryPolicyDesign.Distortions.mpn_antitoneOn
#print axioms Gali.MonetaryPolicyDesign.Distortions.lt_of_wedge
#print axioms Gali.MonetaryPolicyDesign.Distortions.markup_inefficiently_low
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_welfare_lt
#print axioms Gali.MonetaryPolicyDesign.Distortions.wedge_eq_one_iff_subsidy
#print axioms Gali.MonetaryPolicyDesign.Distortions.optimal_subsidy
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_efficient_iff_subsidy
#print axioms Gali.MonetaryPolicyDesign.Distortions.flex_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Distortions.avgMarkup
#print axioms Gali.MonetaryPolicyDesign.Distortions.avgMarkup_subsidy
#print axioms Gali.MonetaryPolicyDesign.Distortions.mrs_eq_avgMarkup
#print axioms Gali.MonetaryPolicyDesign.Distortions.foc_iff_avgMarkup
#print axioms Gali.MonetaryPolicyDesign.Distortions.employment_avgMarkup
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.labourDemand
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.goodsOutput_labourDemand
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.price_eq_of_output_eq
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.price_eq_of_labour_eq
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.dispersion_violates_symmetry
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.dispersion_welfare_loss
#print axioms Gali.MonetaryPolicyDesign.Distortions.Dispersion.prices_equal_of_optimal
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.NKPC
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.DIS
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.zero_equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.infl_zero_of_gap_zero
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.gap_zero_of_infl_zero
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.divine_coincidence
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.optimal_policy_characterisation
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.unbounded_counterexample
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.pathLoss
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.pathLoss_summable
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.pathLoss_nonneg
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.pathLoss_zero
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.pathLoss_eq_zero_iff
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.optimal_policy
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.gap_zero_iff_efficient
#print axioms Gali.MonetaryPolicyDesign.OptimalPolicy.no_dispersion_of_price_stability
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.NKPC
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.DIS
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.ExogRule
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.stack
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.boundedVec_stack
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.adaptedVec_stack
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.nk_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.equilibrium_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.zero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.tr2_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.det2_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.charPolyO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.det_sub_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.charPolyO_zero
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.charPolyO_one
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.charPolyO_trace
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.continuous_charPolyO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.exists_root_Ioo_zero_one
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.exists_root_gt_one
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.eigenvalues_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.not_schurStable_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.not_determinate_AO
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.sunspotY
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.sunspotPi
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.sunspot_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.exists_second_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleExogenous.equilibrium_not_unique
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.TaylorRule
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.omega
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.AT
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.nk_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.equilibrium_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.zero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.tr2_AT
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.det2_AT
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.schurStable_AT_iff
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.determinate_iff_14
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.equilibrium_iff_zero
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.exists_nonzero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.longRunResponse
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.tendsto_gap_of_tendsto_infl
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.tendsto_rate_of_tendsto_infl
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.taylorPrinciple_iff
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.tendsto_realRate_of_tendsto_infl
#print axioms Gali.MonetaryPolicyDesign.RuleTaylorPrinciple.realRate_eventually_pos
#print axioms Gali.MonetaryPolicyDesign.RuleForward.ForwardRule
#print axioms Gali.MonetaryPolicyDesign.RuleForward.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleForward.AF
#print axioms Gali.MonetaryPolicyDesign.RuleForward.AFprinted
#print axioms Gali.MonetaryPolicyDesign.RuleForward.nk_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleForward.equilibrium_iff_solves
#print axioms Gali.MonetaryPolicyDesign.RuleForward.zero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleForward.AF_ne_AFprinted
#print axioms Gali.MonetaryPolicyDesign.RuleForward.AF_one_one
#print axioms Gali.MonetaryPolicyDesign.RuleForward.tr2_AF
#print axioms Gali.MonetaryPolicyDesign.RuleForward.det2_AF
#print axioms Gali.MonetaryPolicyDesign.RuleForward.abs_det2_AF_lt_one_iff
#print axioms Gali.MonetaryPolicyDesign.RuleForward.fn7_implied
#print axioms Gali.MonetaryPolicyDesign.RuleForward.schurStable_AF_iff
#print axioms Gali.MonetaryPolicyDesign.RuleForward.determinate_iff_17_18
#print axioms Gali.MonetaryPolicyDesign.RuleForward.equilibrium_iff_zero
#print axioms Gali.MonetaryPolicyDesign.RuleForward.exists_nonzero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleForward.printed_verdict_differs
#print axioms Gali.MonetaryPolicyDesign.RuleForward.printed_determinacy_differs
#print axioms Gali.MonetaryPolicyDesign.RuleForward.printed_solution_not_equilibrium
#print axioms Gali.MonetaryPolicyDesign.RuleForward.determinate_contemporaneous_phiy_zero
#print axioms Gali.MonetaryPolicyDesign.RuleForward.determinate_forward_phiy_zero
#print axioms Gali.MonetaryPolicyDesign.RuleForward.boundary_eigenvalue_neg_one
#print axioms Gali.MonetaryPolicyDesign.RuleForward.not_determinate_at_boundary
#print axioms Gali.MonetaryPolicyDesign.Welfare.priceIndex
#print axioms Gali.MonetaryPolicyDesign.Welfare.dispersion
#print axioms Gali.MonetaryPolicyDesign.Welfare.bigTheta
#print axioms Gali.MonetaryPolicyDesign.Welfare.crossVar
#print axioms Gali.MonetaryPolicyDesign.Welfare.integrable_exp_mul
#print axioms Gali.MonetaryPolicyDesign.Welfare.interior_integrableExpSet
#print axioms Gali.MonetaryPolicyDesign.Welfare.cgf_taylor
#print axioms Gali.MonetaryPolicyDesign.Welfare.cgf_taylor_comp
#print axioms Gali.MonetaryPolicyDesign.Welfare.priceIndex_family
#print axioms Gali.MonetaryPolicyDesign.Welfare.dispersion_family_eq
#print axioms Gali.MonetaryPolicyDesign.Welfare.crossVar_family
#print axioms Gali.MonetaryPolicyDesign.Welfare.dispersion_second_order
#print axioms Gali.MonetaryPolicyDesign.Welfare.dispersion_family_isBigO_sq
#print axioms Gali.MonetaryPolicyDesign.Welfare.logPriceIndex_second_order
#print axioms Gali.MonetaryPolicyDesign.Welfare.bigO_mul
#print axioms Gali.MonetaryPolicyDesign.Welfare.bigO_weaken
#print axioms Gali.MonetaryPolicyDesign.Welfare.tendsto_zero_of_bigO
#print axioms Gali.MonetaryPolicyDesign.Welfare.taylor_two
#print axioms Gali.MonetaryPolicyDesign.Welfare.exp_taylor_two
#print axioms Gali.MonetaryPolicyDesign.Welfare.exp_sub_one_bigO
#print axioms Gali.MonetaryPolicyDesign.Welfare.logdev_taylor
#print axioms Gali.MonetaryPolicyDesign.Welfare.gapCoeff
#print axioms Gali.MonetaryPolicyDesign.Welfare.psiYA
#print axioms Gali.MonetaryPolicyDesign.Welfare.secondOrderUtility
#print axioms Gali.MonetaryPolicyDesign.Welfare.tip
#print axioms Gali.MonetaryPolicyDesign.Welfare.welfareQuadratic
#print axioms Gali.MonetaryPolicyDesign.Welfare.gapCoeff_mul_psiYA
#print axioms Gali.MonetaryPolicyDesign.Welfare.efficiency_iff
#print axioms Gali.MonetaryPolicyDesign.Welfare.secondOrderUtility_eq
#print axioms Gali.MonetaryPolicyDesign.Welfare.period_utility_second_order
#print axioms Gali.MonetaryPolicyDesign.Welfare.period_utility_second_order_dispersion
#print axioms Gali.MonetaryPolicyDesign.Welfare.period_utility_normalised
#print axioms Gali.MonetaryPolicyDesign.Welfare.GoodDist
#print axioms Gali.MonetaryPolicyDesign.Welfare.crossMean
#print axioms Gali.MonetaryPolicyDesign.Welfare.crossVarDist
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvoMix
#print axioms Gali.MonetaryPolicyDesign.Welfare.integral_calvoMix
#print axioms Gali.MonetaryPolicyDesign.Welfare.crossVarDist_eq
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvoMix_good
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvoMix_mean
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvoMix_var
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvoMix_var_meanChange
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvo_good
#print axioms Gali.MonetaryPolicyDesign.Welfare.calvo_var_recursion
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2_partial
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2_nonneg
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2_hasSum
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2_calvo_inherited
#print axioms Gali.MonetaryPolicyDesign.Welfare.lemma2_calvo
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflation_sub_meanChange
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflation_sq_sub_meanChange_sq
#print axioms Gali.MonetaryPolicyDesign.Welfare.lambdaNK
#print axioms Gali.MonetaryPolicyDesign.Welfare.kappaNK
#print axioms Gali.MonetaryPolicyDesign.Welfare.periodLoss
#print axioms Gali.MonetaryPolicyDesign.Welfare.welfareLoss
#print axioms Gali.MonetaryPolicyDesign.Welfare.avgLoss
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflWeight_of_dispersion
#print axioms Gali.MonetaryPolicyDesign.Welfare.welfare_eq_loss
#print axioms Gali.MonetaryPolicyDesign.Welfare.welfare_eq_loss_calvo
#print axioms Gali.MonetaryPolicyDesign.Welfare.welfare_stationary
#print axioms Gali.MonetaryPolicyDesign.Welfare.gapCoeff_strictMono_sigma
#print axioms Gali.MonetaryPolicyDesign.Welfare.gapCoeff_strictMono_phi
#print axioms Gali.MonetaryPolicyDesign.Welfare.gapCoeff_strictMonoOn_alpha
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflWeight_eq
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflWeight_strictMonoOn_eps
#print axioms Gali.MonetaryPolicyDesign.Welfare.inflWeight_strictMonoOn_theta
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_eq_ratio
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_eq
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_sub
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_strictAntiOn_alpha
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_strictMonoOn_alpha
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_baseline
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_not_increasing_alpha
#print axioms Gali.MonetaryPolicyDesign.Welfare.relWeight_baseline_strictAnti
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.NKPC
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.DIS
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.TaylorRule
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.pseudoShock
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.TaylorRuleGap
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.rule19_iff_rule20
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.drivingForce
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.Structural
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.omega
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.AT
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.BT
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.stack
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.forcing
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.nk_iff_structural
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.structural_iff_solves
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.equilibrium_iff_solves
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.tr2_AT
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.det2_AT
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.schurStable_AT_iff
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.determinate_iff
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.boundedVec_stack
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.adaptedVec_stack
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.natRate_eq
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.drivingForce_eq
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvDen
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvLambda
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvPsiY
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvPsiPi
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvDen_eq
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvDen_pos
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.isAR1_smul
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msv_structural
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.structural_add
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.boundedProc_lin
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.adapted_lin
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.equilibrium_iff_msv
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.equilibrium_iff_msv_single
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvLoss
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvLoss_eq
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msv_moments
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.equilibrium_loss
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.variance_isSecondMoment
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.ar1Var
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.ar1Var_fixed_point
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.ar1Var_hasSum
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.msvLoss_tendsto_zero
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.MoneyDemandGap
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.Eq32
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.RealBalanceId
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.Predetermined
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.dis_iff_eq32
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.AM0
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.AM1
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.BM
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.stateVec
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.expVec
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.shockVec
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.System34
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.system34_iff
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.MoneyDemandShock
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.ConstantMoney
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.constantMoney_of_levels
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.Lplus
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.dZeta
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.moneyDemand_iff_plus
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.constantMoney_iff_plus
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.predetermined_plus
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.constantMoney_iff_system34
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.techLoad
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.demandLoad
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.baseSdGap
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.baseSdInfl
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.baseSdOutputTech
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.baseLoss
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.kappa_base
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.lambda_base
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.gapCoeff_base
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.psiYA_base
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.sqrt_bounds
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_tech_1
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_tech_2
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_tech_3
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_tech_4
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_demand_1
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_demand_2
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_demand_3
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_demand_4
#print axioms Gali.MonetaryPolicyDesign.SimpleRules.table41_truncated
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.IsEigenvalue
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.det_charMatrix
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.isEigenvalue_iff_charpoly
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.isEigenvalue_iff_root
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.eigenvalues_inside_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.NKPC
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.DIS
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.boundedVec_stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.adaptedVec_stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AO
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.tr2_AO
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.det2_AO
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.equilibrium_AO_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AO_eigenvalues
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.not_schurStable_AO
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AO_zero_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AO_not_determinate
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AO_not_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.Structural
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.equilibrium_iff_structural
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.omega
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.BT
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.forcing
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.structural_iff_solves
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.tr2_AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.det2_AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.det2_AT_mem
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.schurStable_AT_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AT_eigenvalues_inside_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.AT_not_both_outside
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.printed_iff_iff_not14
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.printed_ex4_1b_false
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.determinate_iff_14
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.structural_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.structural_not_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.rule11_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.rule11_not_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvDen
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvLambda
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvPsiY
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvPsiPi
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvDen_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msvDen_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.isAR1_smul
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.boundedProc_smul
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.boundedProc_add
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.msv_structural
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.structural_add
#print axioms Gali.MonetaryPolicyDesign.Ex4_1.structural_smul
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Dr
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.aR
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.bR
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.aXi
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.bXi
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Dr_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Dr_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Dr_le
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.natRate
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Rule
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.forcingU
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.msv_structural
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.adapted_comb
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.bounded_comb
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2a_exists
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2a_equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2a_rate
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2a_not_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.tendsto_div_affine
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2b_coefficients
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2b_limits
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.bilin_quad
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.stationary_var_ar1
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.varInfl
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.varGap
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2c_variance
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ratio_mono
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit_strictMonoOn
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit_ge
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit_one_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit_continuousOn
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hasDerivAt_varInfl
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.varInfl_continuousOn
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.deriv_varInfl_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2c_interior
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2c_corner
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2c_no_noise
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.hcrit_iid
#print axioms Gali.MonetaryPolicyDesign.Ex4_2.ex4_2c_iid
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.cA
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.Da
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaY
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaPi
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaN
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.cA_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.Da_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaN_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.Equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.msv_structural
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3a_equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3a_exists
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaY_mem
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.gammaPi_neg
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3b_mono_phi
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3b_mono_kappa
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3b_phi_infty
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3b_kappa_infty
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3b_kappa_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3c_sign
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3c_both_signs
#print axioms Gali.MonetaryPolicyDesign.Ex4_3.ex4_3c_covariance
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.DIS
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.NKPC
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.Block
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.loss
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.loss_nonneg
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.loss_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.zero_minimises_loss
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.zero_equilibrium_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.Rule
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.omega
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.rule_iff_solves
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.tr2_AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.det2_AT
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.schurStable_AT_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.boundedVec_stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.adaptedVec_stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.RuleEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.rule_implements
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.rule_not_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.implements_uniquely_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.lagP
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.PriceLevel
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.MoneyDemand
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.FullEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.price_level_const
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.money_path_optimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.constant_money_suboptimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.constant_money_not_optimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.optimal_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.constant_money_optimal_of_const
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.MoneyRule
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.moneyRule_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.moneyRule_iff_interestRule
#print axioms Gali.MonetaryPolicyDesign.Ex4_4.MoneyRuleUniqueness
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.utility
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasDerivAt_utility_C
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasDerivAt_utility_m
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasDerivAt_utility_N
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.le_tangent
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.disutil_tangent_le
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasDerivAt_disutil
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.log_le_tangent
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.labour_foc_necessary
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.labour_foc_sufficient
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.labour_optimum_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.money_foc_necessary
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.money_foc_sufficient
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.money_optimum_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.markup
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.markup_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.one_lt_markup
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.markup_pricing_le
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.markup_pricing_lt
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.profit_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.price_optimum_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.real_wage_of_pricing
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.Nflex
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.Nflex_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.Nflex_rpow
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.employment_flex
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.level
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.level_succ
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.level_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.level_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.log_level_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.pairLaw
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_exp_pair
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integrable_exp_pair
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.mk
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.Z
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.va
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.adapted
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.hasLaw
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.ShockPair.indep
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.techShock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.moneyShock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.varM
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.varX
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.varM_nonneg
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.varX_nonneg
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.condExp_shock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_exp_shock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integrable_exp_shock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasLaw_fst
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasLaw_snd
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integrable_lin
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_lin
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_log_tech
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integrable_log_tech
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.condExp_money_ratio
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.eulerRHS
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.Qstar
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.velocity
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.eulerRHS_of_const_velocity
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.velocity_of_euler
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.mk
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.pos_C
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.pos_N
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.pos_P
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.labour
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.money
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.euler
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.pricing
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.technology
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsFlexEquilibrium.clearing
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_employment
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_output
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_velocity
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_candidate
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_inflation
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_period_utility
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfareFlex
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasSum_affine
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasSum_flex_welfare
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.flex_qstar_lt_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.nominalRate_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.qstar_le_one_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.friedman_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.not_equilibrium_at_friedman
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfareFlex_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfareFlex_lt_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfare_strictAnti_gamma
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfare_strictMono_var
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.welfare_rate_strictAnti
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.tendsto_welfare_rate
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.not_optimal_of_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_objective_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.condExp_objective
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_price_optimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_price_unique
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.wage_over_tech
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.pricing_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.measurable_level
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.techShock_measurable
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.moneyShock_measurable
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.gapShock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.moneyShock_sub_techShock
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.mk
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.pos_C
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.pos_N
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.pos_P
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.labour
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.money
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.euler
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.preset
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.preset0
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.integrable_hours
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.pricing
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.pricing0
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.technology
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.IsStickyEquilibrium.clearing
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_employment
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_employment_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_velocity
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_output_balances
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyN
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyN_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyN_rpow_succ
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_candidate
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_period_utility
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyWelfare
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_expected_utility_succ
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_expected_utility_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.hasSum_sticky_welfare
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.policyWelfare
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyWelfare_le_flex
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyWelfare_eq_flex_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.varX_eq_zero_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stabilization_optimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.exists_gamma_for_qstar
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stabilization_improves
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.policy_not_optimal
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.tendsto_policyWelfare_friedman
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.stickyN_replicates
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_replicates_flex
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_employment_replicates
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.policyWelfare_replicates
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.friedman_level_of_replicating
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.shockMeasure
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.shockFiltration
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.coord_indep
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.comap_le_shockFiltration
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.concreteShocks
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.exists_flex_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.exists_sticky_equilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.sticky_logN_succ
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_abs_lin
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.abs_log_tech_le
#print axioms Gali.MonetaryPolicyDesign.Ex4_5.integral_tsum_sticky_welfare
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.loadY
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.eCoef
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.mCoef
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.fwdA
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bwdB
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.phiStar
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.loadY_mul
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly_neg_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly_neg_one_pos_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.charPoly_neg_one_neg_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.continuous_charPoly
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.is_coef_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.delta_eq
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.pc_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.is_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.fwd_of
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bwd_step
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.det2_fwdA
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.tr2_fwdA
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.key_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.key_neg_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.schur_fwdA
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.lagP
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.infl
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.IsEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.BoundedEq
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.Determinate
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.known_pm1
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.lagP_adapted
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.eq_iff_pointwise
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.wseq
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.vseq
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.stack
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.reduce_solves
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.mode_isEquilibrium
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bounded_eq_explicit
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.determinate_of_root
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.exists_root_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.exists_root_neg
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.exists_root_large
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.determinate_of_pos
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.determinate_of_lt_phiStar
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.zero_boundedEq
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.not_determinate_of_two_roots
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.not_determinate_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.not_determinate_phiStar
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.det2_bwdB
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.tr2_bwdB
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bwdB_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bwdB_neg_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.keyB_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.keyB_neg_one
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.bounded_of_tendsto_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.not_determinate_of_neg
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.not_determinate_of_le
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.determinate_iff
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.determinate_iff_pos_of_ge
#print axioms Gali.MonetaryPolicyDesign.Ex4_6.book_claim_false
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.eigs
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.stableCount
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.NoUnit
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mem_eigs_iff
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.exists_eigvec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.exists_left_eigvec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mem_eigs_of_eigvec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.pow_mulVec_eigvec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.map_ofReal_pow
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.card_eigs
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.pow_entry_bound
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.norm_le_one_of_pow_bounded
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.boundedOrbits
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mem_boundedOrbits
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mulVec_mem_boundedOrbits
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mem_boundedOrbits_of_orbit
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.re_mulVec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.im_mulVec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.boundedOrbitsC
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.maxGenEigenspace_le_boundedOrbitsC
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_boundedOrbitsC_le
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_finset_sup
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.card_filter_eq_sum
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.stableCount_le_finrank
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.unstableCount
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.stableCount_add_unstableCount
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.restrict_block
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.norm_le_one_of_bounded_pow_mul
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.exists_restrict_stable
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_le_stableCount
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.tendsto_of_mem_boundedOrbits
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_eq_stableCount
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.boundedOrbits_eq_bot_of_unstable
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.abs_entry_le_sum
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.abs_mulVec_le
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.rec_closed
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.rec_bounded
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.xrecV
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.GenericX
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.projX
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.graphV
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.IsGraph
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.matrix_eq_of_mulVec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mulVec_sumElim
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.exists_graph
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.lam
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.cmat
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.graph_invariant
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.graph_invariant_vec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.lam_mulVec
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.mulVec_graphV
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.pow_mulVec_graphV
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.lam_pow_bounded
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.fromBlocks_shear_mul
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.charpoly_split
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.charpoly_map_ofReal
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.eigs_split
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.lam_stable
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.zero_of_cmat_orbit
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.cmat_unstable
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.stableCount_eq_card
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_le_of_genericX
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.not_genericX_of_lt
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.exists_unreached_of_lt
#print axioms Gali.MonetaryPolicyDesign.InvariantSplit.finrank_eq_iff_stableCount_eq
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_apply
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_apply_sum
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_add
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_sub
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.add_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.sub_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_one
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_zero
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.mv_neg
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.E_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.AdaptedV
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.BoundedV
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.FSolves
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.boundedV_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.adaptedV_mv
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.fsolves_iterate
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.abs_mv_le
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.fsolves_unique
#print axioms Gali.MonetaryPolicyDesign.GeneralBKForward.fsolves_exists
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.map_ofReal_mulVec
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.det_ne_zero_of_unstable
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.inv_stable
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.boundedV_add
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.boundedV_sub
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.boundedV_neg
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.adaptedV_add
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.adaptedV_sub
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.adaptedV_neg
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.Solves
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.Equil
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.Determinate
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.eval_split
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mv_inl
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mv_inr
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.zx_block_eq
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.identity_zhat
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.identity_x
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.identity_exist
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.identity_exist_x
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.xrecR
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.xrecR_bounded
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.xrecR_known
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.fsolves_iff_cform
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.determinate_of
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.sum_q_mulVec
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.false_of_linear_growth
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.no_bounded_resonance
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.exists_left_eigvec_unit
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.nonexist_of_unit
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.not_determinate_of_unit
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mult_of_not_genericX
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.not_determinate_of_not_genericX
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.nonexist_of_lt
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.not_determinate_of_lt
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.not_determinate_of_gt
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.determinate_iff
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.determinate_iff_count
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.determinate_iff_unstableCount
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.determinate_iff_perfectForesight
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mem_boundedOrbits_of_tendsto
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mem_boundedOrbits_iff_tendsto_of_noUnit
#print axioms Gali.MonetaryPolicyDesign.GeneralBK.mem_boundedOrbits_iff_tendsto
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.Predetermined
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.AM0
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.AM1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.BM
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.stateVec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.expVec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.shockVec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.System34
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM1_sub_smul_AM0
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM0
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.AM
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM_sub_smul
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charpoly_AM_eval
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.isRoot_charpoly_AM_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic_expand
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic_zero
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic_signs
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.charCubic_root_gt_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.AM_has_eigenvalue_gt_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.det_AM_pos_lt_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleSystem.BookDeterminacyClaim
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.coef2
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.coef1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.charCubic_eq_coef
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadQ1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadQ0
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadQ1_mul
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadQ0_mul
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.charCubic_factor
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.charCubic_neg_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.exists_root_gt_one
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quad_values
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quad_schurStable
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.bookDeterminacyClaim_holds
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.bookDeterminacyClaim_gali
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.norm_lt_one_of_quadratic
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadPoly
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.quadPoly_root
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.charpoly_AM_factor
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.eigs_AM
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.AM_root_location
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.AM_root_location_gali
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleRoots.real_eigenvalue_unique
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.eigs_submatrix_equiv
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.genericX_of_eigvec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.norm_gt_one_of_recip
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Ab3
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.isUnit_det_AM1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.isUnit_det_AM0
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Ab3_eq_inv_AM
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.det_pencil
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.det_pencil_factor
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.det_AM1_mul_charpoly_Ab3
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.charpoly_Ab3_factor
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Ab3_root_location
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.eS
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Abk
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.eigv3
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.pencil_eigvec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Ab3_eigvec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.eigs_Abk
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Abk_bk_conditions
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Abk_determinate
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.yvec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.svec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.wvec
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.yvec_apply
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.E_yvec_apply
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.wvec_apply
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.mv_Abk_apply
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.backward_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.solves_Abk_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.Equil34
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.equil_Abk_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.svec_boundedV
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.svec_adaptedV
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.system34_existsUnique_pos
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.B2f
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.eS2
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.B2
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.exists_rho1
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.charpoly_B2f
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.B2f_root_location
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.B2_bk_conditions
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.B2_determinate
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.y2
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.w2
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.solves_B2_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.system34_zero_iff
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.system34_existsUnique_zero
#print axioms Gali.MonetaryPolicyDesign.MoneyRuleDeterminacy.system34_existsUnique
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.realBal
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.realBal_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.lagP_adapted
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.lagP_bounded
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.realBal_pred
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.realBal_adapted
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.realBal_bounded
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.infl_adapted
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.infl_bounded
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.system34_of_moneyRule
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.equil34_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.moneyRule_gap_infl_zero
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.moneyRuleUniqueness_holds
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.moneyRule_unique_outcome
#print axioms Gali.MonetaryPolicyDesign.Ex4_4Determinacy.moneyRule_implements_uniquely
