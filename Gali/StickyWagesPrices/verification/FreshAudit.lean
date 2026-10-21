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
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
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

Restated from the `Gali/DiscretionCommitment` project (each project in this
repository is self-contained).
-/

namespace Gali.StickyWagesPrices

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

end Gali.StickyWagesPrices

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

Restated from the `Gali/DiscretionCommitment` project (each project in this
repository is self-contained).
-/

namespace Gali.StickyWagesPrices

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

end Gali.StickyWagesPrices

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

Restated from the `Gali/DiscretionCommitment` project (each project in this
repository is self-contained).
-/

namespace Gali.StickyWagesPrices.ExpectationsFiniteTree

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

end Gali.StickyWagesPrices.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The determinacy theorem of Galí (2015), p. 174

Galí (2015), Chapter 6, Section 6.2, pp. 172–175. Under the interest rate rule (23) the
sticky-wage-and-price economy is the system (24),

  `A₀ʷ x_t = A₁ʷ E_t x_{t+1} + B₀ʷ u_t`,  `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})`,

with three non-predetermined variables and one predetermined variable (the lagged real wage
gap). The book states without proof (fn. 2, citing Flaschel–Franke–Proaño 2008 and
Blasselle–Poissonnier 2013) that, for nonnegative rule coefficients, the equilibrium is
determinate if and only if

  `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`,  `Θ_y = σ + (α + φ)/(1 − α)`,

equivalently three eigenvalues of `(A₀ʷ)⁻¹ A₁ʷ` lie inside and one outside the unit circle.
This module proves both statements in full.

## Method

* `q(z) = −det(A₀ʷ − z A₁ʷ)` is an explicit quartic with `q(1) = λ_p λ_w Θ_y (LHS − 1)`.
* **No root on the unit circle when `q(1) > 0`** (`Par.qC_ne_zero_of_norm_eq_one`): writing
  `z = x + i y`, `Re(q(z) · i z̄ ē)` with `e = (1 − βz)(1 − z̄)` equals
  `(1 − β) y q(1)` plus a sum of nonnegative terms (`circle_cert`, an exact polynomial identity
  modulo `x² + y² = 1`).
* **Counting by the argument principle** (`argument_principle`, `inCount_path`): along a path
  of quartics without roots on the circle the number of roots in the unit disc is constant.
  A two-stage homotopy (policy coefficients, then structural parameters) inside the region
  `q(1) > 0` connects any parameter vector to a reference vector whose quartic factors with
  roots `1/2, 1/3, 4, 1/8` (`Par.inCount_QC`).
* **Blanchard–Kahn with one predetermined variable**: the unique stable root `μ ∈ (0, 1)` of
  `q` and its eigenvector `(g, 1)` quasi-difference the system into a forward system
  `s_t = K E_t s_{t+1} + F u_t` whose matrix `K` has all eigenvalues in the open unit disc
  (`Par.Km_eigen`, via `det(C − z D) = −q(z)/(z − μ)`); Gelfand's formula gives geometric decay
  of `Kᵏ` (`pow_entry_bound`), whence existence and uniqueness (`Fwd.fsolves_exists`,
  `Fwd.fsolves_unique`, `Dyn.determinate_of_pos`).
* **Failure when the condition fails**: at `q(1) = 0` a unit root makes a constant forcing
  produce no bounded solution (`Dyn.not_determinate_of_eq`); when `q(1) < 0` the number of
  roots of `q` in the closed disc is never one (`Dyn.closedRoots_card_ne_one`); with none, no
  bounded solution exists for `ω̃_{−1} = 1` (`Dyn.not_determinate_of_no_root`); with two or
  more, an explicit nonzero bounded solution with `ω̃_{−1} = 0` exists (complex pair, two real
  roots, or a Jordan chain for a double root).

## Main results

* `determinacy_iff`: the p. 174 theorem, in the book's parameters.
* `eigenvalues_iff`: the eigenvalue form (three inside, one outside, with multiplicity).
* `determinacy_iff_phiY_zero`: with `φ_y = 0` the condition is `φ_p + φ_w > 1`.
* `exNE_no_bounded_solution`, `exBase_multiplicity`: both failure modes occur.

## Remark on the book (Lean-checked)

Figure 6.1 labels the region where the condition fails "Indeterminacy". At the book's baseline
calibration that is what happens (`exBase_multiplicity`: two stable roots, two bounded
solutions), but not in general: at the admissible point `exNE` (`β = 9/10, σ = 3/4, α = 3/4,
φ = 3, λ_p = 1/40, λ_w = 6/5, φ_p = 2/25, φ_w = 31/50, φ_y = 7/100`, `LHS = 1939/2700 < 1`)
all four eigenvalues of `Aʷ` lie inside the unit circle (`exNE_no_root`) and there is no bounded
solution for zero forcing and `ω̃_{−1} = 1` (`exNE_no_bounded_solution`): non-existence, not
multiplicity. The theorem `determinacy_iff` covers both cases.
-/

namespace Gali.StickyWagesPrices.Determinacy4

open Polynomial Complex Real Filter Topology

/-- Galí (2015), p. 174: The number of roots (with multiplicity) of `p` in the open unit disc. -/
noncomputable def inCount (p : ℂ[X]) : ℕ := (p.roots.filter (fun z => ‖z‖ < 1)).card

/-- Galí (2015), p. 174: `∮ (z − α)⁻¹` over the unit circle: `2πi` inside, `0` outside. -/
theorem circleIntegral_sub_inv (α : ℂ) (hα : ‖α‖ ≠ 1) :
    (∮ z in C(0, 1), (z - α)⁻¹) = if ‖α‖ < 1 then 2 * π * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h)
  · have hgt : 1 < ‖α‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hα)
    refine DiffContOnCl.circleIntegral_eq_zero zero_le_one ?_
    refine DifferentiableOn.diffContOnCl_ball (U := {z | z ≠ α}) ?_ ?_
    · intro z hz
      exact ((differentiableAt_id.sub_const α).inv (sub_ne_zero.mpr hz)).differentiableWithinAt
    · intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz
      intro h'
      rw [h'] at hz
      linarith

/-- Galí (2015), p. 174 (tool): the argument principle for polynomials on the unit circle. -/
theorem argument_principle (p : ℂ[X]) (hp : p ≠ 0) (hc : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    (∮ z in C(0, 1), p.derivative.eval z / p.eval z) = 2 * π * I * inCount p := by
  induction h : p.natDegree generalizing p with
  | zero =>
    obtain ⟨a, rfl⟩ : ∃ a, p = C a := ⟨_, eq_C_of_natDegree_eq_zero h⟩
    simp [inCount, circleIntegral]
  | succ n ih =>
    obtain ⟨α, hα⟩ : ∃ α, IsRoot p α :=
      Complex.exists_root (by rw [degree_eq_natDegree hp, h]; exact_mod_cast Nat.succ_pos n)
    set p₁ := p /ₘ (X - C α) with hp₁
    have hfac : (X - C α) * p₁ = p := mul_divByMonic_eq_iff_isRoot.mpr hα
    have hp₁0 : p₁ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfac; exact hp hfac.symm
    have hdeg : p₁.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero α) hp₁0, natDegree_X_sub_C, h] at this
      omega
    have hc₁ : ∀ z : ℂ, ‖z‖ = 1 → p₁.eval z ≠ 0 := by
      intro z hz h0
      apply hc z hz
      rw [← hfac, eval_mul, h0, mul_zero]
    have hαn : ‖α‖ ≠ 1 := fun h1 => hc α h1 hα
    have hne : ∀ z : ℂ, ‖z‖ = 1 → z - α ≠ 0 := fun z hz h0 => by
      rw [sub_eq_zero] at h0; rw [h0] at hz; exact hαn hz
    have heq : Set.EqOn (fun z => p.derivative.eval z / p.eval z)
        (fun z => (z - α)⁻¹ + p₁.derivative.eval z / p₁.eval z) (Metric.sphere 0 1) := by
      intro z hz
      have hz' : ‖z‖ = 1 := by simpa using hz
      have h1 := hne z hz'
      have h2 := hc₁ z hz'
      simp only
      rw [← hfac, derivative_mul]
      simp only [eval_mul, eval_add, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
        derivative_C, sub_zero, one_mul]
      field_simp
    have hint1 : CircleIntegrable (fun z : ℂ => (z - α)⁻¹) 0 1 := by
      refine ContinuousOn.circleIntegrable zero_le_one ?_
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro z hz
      exact hne z (by simpa using hz)
    have hint2 : CircleIntegrable (fun z : ℂ => p₁.derivative.eval z / p₁.eval z) 0 1 := by
      refine ContinuousOn.circleIntegrable zero_le_one ?_
      refine ContinuousOn.div (Polynomial.continuousOn _) (Polynomial.continuousOn _) ?_
      intro z hz
      exact hc₁ z (by simpa using hz)
    rw [circleIntegral.integral_congr zero_le_one heq, circleIntegral.integral_add hint1 hint2,
      circleIntegral_sub_inv α hαn, ih p₁ hp₁0 hc₁ hdeg]
    have hroots : p.roots = α ::ₘ p₁.roots := by
      rw [← hfac, roots_mul (by rw [hfac]; exact hp), roots_X_sub_C]
      rfl
    unfold inCount
    rw [hroots, Multiset.filter_cons]
    split_ifs with hlt
    · simp only [Multiset.singleton_add, Multiset.card_cons]
      push_cast
      ring
    · simp

/-- Galí (2015), p. 174: A quartic polynomial from its five coefficients. -/
noncomputable def quart (a : Fin 5 → ℂ) : ℂ[X] :=
  C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 + C (a 3) * X ^ 3 + C (a 4) * X ^ 4

/-- Galí (2015), p. 174 (tool): evaluating a quartic. -/
theorem eval_quart (a : Fin 5 → ℂ) (z : ℂ) :
    (quart a).eval z = a 0 + a 1 * z + a 2 * z ^ 2 + a 3 * z ^ 3 + a 4 * z ^ 4 := by
  simp [quart]

/-- Galí (2015), p. 174 (tool): evaluating the derivative of a quartic. -/
theorem eval_derivative_quart (a : Fin 5 → ℂ) (z : ℂ) :
    (quart a).derivative.eval z = a 1 + 2 * a 2 * z + 3 * a 3 * z ^ 2 + 4 * a 4 * z ^ 3 := by
  simp only [quart, derivative_add, derivative_C, derivative_mul, derivative_X, derivative_X_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one]
  push_cast
  ring

/-- Galí (2015), p. 174 (tool): along a continuous path of quartics with no root on the unit
circle, the number of roots inside the unit disc is constant. -/
theorem inCount_path (a : ℝ → Fin 5 → ℂ) (ha : ∀ i, Continuous fun s => a s i)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, quart (a s) ≠ 0)
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 → (quart (a s)).eval z ≠ 0) :
    inCount (quart (a 0)) = inCount (quart (a 1)) := by
  set pr : ℝ → ℝ := fun s => (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ) with hpr
  have hprc : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hprm : ∀ s, pr s ∈ Set.Icc (0 : ℝ) 1 := fun s => Subtype.prop _
  set b : ℝ → Fin 5 → ℂ := fun s => a (pr s) with hb
  have hbc : ∀ i, Continuous fun s => b s i := fun i => (ha i).comp hprc
  have hI : ∀ s, (∮ z in C(0, 1), (quart (b s)).derivative.eval z / (quart (b s)).eval z)
      = 2 * π * I * inCount (quart (b s)) := fun s =>
    argument_principle _ (hne _ (hprm s)) (hc _ (hprm s))
  set n : ℝ → ℝ := fun s => (inCount (quart (b s)) : ℝ) with hn
  have hn_eq : ∀ s, n s = ((∮ z in C(0, 1), (quart (b s)).derivative.eval z /
      (quart (b s)).eval z) / (2 * π * I)).re := by
    intro s
    rw [hI s]
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [mul_div_cancel_left₀ _ h2]
    simp [hn]
  have hcont : Continuous n := by
    have hF : Continuous fun s => (∮ z in C(0, 1), (quart (b s)).derivative.eval z /
        (quart (b s)).eval z) := by
      unfold circleIntegral
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun s θ => deriv (circleMap 0 1) θ • ((quart (b s)).derivative.eval
          (circleMap 0 1 θ) / (quart (b s)).eval (circleMap 0 1 θ))) ?_ 0 (2 * π)
      simp only [deriv_circleMap, eval_quart, eval_derivative_quart, smul_eq_mul]
      have hm : Continuous fun x : ℝ × ℝ => circleMap 0 1 x.2 :=
        (continuous_circleMap 0 1).comp continuous_snd
      have hbi : ∀ i, Continuous fun x : ℝ × ℝ => b x.1 i := fun i => (hbc i).comp continuous_fst
      refine Continuous.mul (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) ?_)
      intro x
      have := hc _ (hprm x.1) (circleMap 0 1 x.2) (by simp)
      rw [eval_quart] at this
      exact this
    have : n = fun s => ((∮ z in C(0, 1), (quart (b s)).derivative.eval z /
        (quart (b s)).eval z) / (2 * π * I)).re := funext hn_eq
    rw [this]
    exact Complex.continuous_re.comp (hF.div_const _)
  have hb0 : b 0 = a 0 := by simp [hb, hpr]
  have hb1 : b 1 = a 1 := by simp [hb, hpr]
  rw [← hb0, ← hb1]
  by_contra hneq
  -- an integer-valued continuous function on `[0,1]` is constant
  have hmid : ∀ m₀ m₁ : ℕ, m₀ < m₁ → ∀ s, n s ≠ m₀ + 1 / 2 := by
    intro m₀ m₁ _ s hs
    have : (2 * inCount (quart (b s)) : ℝ) = 2 * m₀ + 1 := by
      have := hs; simp only [hn] at this; linarith
    have h' : 2 * inCount (quart (b s)) = 2 * m₀ + 1 := by exact_mod_cast this
    omega
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (inCount (quart (b 0)) : ℝ) + 1 / 2 ∈ Set.Icc (n 0) (n 1) by
        simp only [hn, Set.mem_Icc]
        have : (inCount (quart (b 0)) + 1 : ℝ) ≤ inCount (quart (b 1)) := by exact_mod_cast hlt
        constructor <;> linarith)
    exact hmid _ _ hlt s hs
  · obtain ⟨s, -, hs⟩ := intermediate_value_Icc' (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (inCount (quart (b 1)) : ℝ) + 1 / 2 ∈ Set.Icc (n 1) (n 0) by
        simp only [hn, Set.mem_Icc]
        have : (inCount (quart (b 1)) + 1 : ℝ) ≤ inCount (quart (b 0)) := by exact_mod_cast hgt
        constructor <;> linarith)
    exact hmid _ _ hgt s hs

/-- Galí (2015), eq. (24), p. 173: Parameters of system (24). -/
structure Par where
  β : ℝ
  σ : ℝ
  κp : ℝ
  κw : ℝ
  lamP : ℝ
  lamW : ℝ
  φp : ℝ
  φw : ℝ
  φy : ℝ

namespace Par

/-- Galí (2015), p. 174: `Ψ = λ_w κ_p + λ_p κ_w` \(= λ_p λ_w Θ_y\). -/
def Ψ (P : Par) : ℝ := P.lamW * P.κp + P.lamP * P.κw

/-- Galí (2015), p. 174: Constant coefficient of `q`. -/
def c0 (P : Par) : ℝ := -P.σ - P.κp * P.φp - P.κw * P.φw - P.φy

/-- Galí (2015), p. 174: Linear coefficient of `q`. -/
def c1 (P : Par) : ℝ :=
  2 * P.β * P.σ + P.β * P.κp * P.φp + P.β * P.κw * P.φw + 2 * P.β * P.φy + P.σ * P.lamP
    + P.σ * P.lamW + 2 * P.σ + P.κp * P.lamW * P.φp + P.κp * P.lamW * P.φw + P.κp * P.φp
    + P.κp + P.κw * P.lamP * P.φp + P.κw * P.lamP * P.φw + P.κw * P.φw + P.lamP * P.φy
    + P.lamW * P.φy + P.φy

/-- Galí (2015), p. 174: Quadratic coefficient of `q`. -/
def c2 (P : Par) : ℝ :=
  -P.β ^ 2 * P.σ - P.β ^ 2 * P.φy - P.β * P.σ * P.lamP - P.β * P.σ * P.lamW
    - 4 * P.β * P.σ - P.β * P.κp * P.φp - P.β * P.κp - P.β * P.κw * P.φw
    - P.β * P.lamP * P.φy - P.β * P.lamW * P.φy - 2 * P.β * P.φy - P.σ * P.lamP
    - P.σ * P.lamW - P.σ - P.κp * P.lamW - P.κp - P.κw * P.lamP

/-- Galí (2015), p. 174: Cubic coefficient of `q`. -/
def c3 (P : Par) : ℝ :=
  2 * P.β ^ 2 * P.σ + P.β ^ 2 * P.φy + P.β * P.σ * P.lamP + P.β * P.σ * P.lamW
    + 2 * P.β * P.σ + P.β * P.κp

/-- Galí (2015), p. 174: Leading coefficient of `q`. -/
def c4 (P : Par) : ℝ := -P.β ^ 2 * P.σ

/-- Galí (2015), p. 174: `q` evaluated at a real point. -/
def qr (P : Par) (r : ℝ) : ℝ :=
  P.c0 + P.c1 * r + P.c2 * r ^ 2 + P.c3 * r ^ 3 + P.c4 * r ^ 4

/-- Galí (2015), p. 174: `q(1) = Ψ (L − 1)` in polynomial form. -/
theorem qr_one (P : Par) :
    P.qr 1 = -P.Ψ + P.φy * (1 - P.β) * (P.lamP + P.lamW) + (P.φp + P.φw) * P.Ψ := by
  simp only [qr, c0, c1, c2, c3, c4, Ψ]; ring

end Par

set_option maxRecDepth 20000 in
/-- Galí (2015), p. 174 (the key inequality): writing `z = x + i y` on the unit circle, the real
combination `Re(q(z) · i z̄ ē)` with `e = (1 − βz)(1 − z̄)` equals
`(1 − β) y q(1) + y · (nonnegative terms)`. Here it is stated through the real and imaginary
parts of `q(z)`. -/
theorem circle_cert (P : Par) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1)
    (hre : P.c0 + P.c1 * x + P.c2 * (x ^ 2 - y ^ 2) + P.c3 * (x ^ 3 - 3 * x * y ^ 2)
      + P.c4 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4) = 0)
    (him : P.c1 * y + P.c2 * (2 * x * y) + P.c3 * (3 * x ^ 2 * y - y ^ 3)
      + P.c4 * (4 * x ^ 3 * y - 4 * x * y ^ 3) = 0) :
    (1 - P.β) * y * P.qr 1 + y * (2 * P.Ψ * (1 - x)
        + (((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
          * (P.κp + P.σ * (1 + P.β - 2 * P.β * x + (P.lamP + P.lamW)))
        + P.φy * P.β * ((((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
          + 2 * (P.lamP + P.lamW) * (1 - x))) = 0 := by
  simp only [Par.c0, Par.c1, Par.c2, Par.c3, Par.c4, Par.qr, Par.Ψ] at hre him ⊢
  linear_combination (x ^ 2 * y * P.β - 2 * x * y * P.β + y ^ 3 * P.β + y) * hre
    - (x ^ 3 * P.β - x ^ 2 * P.β - x ^ 2 + x * y ^ 2 * P.β + x + y ^ 2 * P.β - y ^ 2) * him
    - (3 * x ^ 4 * y * P.β ^ 3 * P.σ - 4 * x ^ 3 * y * P.β ^ 3 * P.σ
      - 2 * x ^ 3 * y * P.β ^ 3 * P.φy - 2 * x ^ 3 * y * P.β ^ 2 * P.σ * P.lamP
      - 2 * x ^ 3 * y * P.β ^ 2 * P.σ * P.lamW - 8 * x ^ 3 * y * P.β ^ 2 * P.σ
      - 2 * x ^ 3 * y * P.β ^ 2 * P.κp + 2 * x ^ 2 * y ^ 3 * P.β ^ 3 * P.σ
      + x ^ 2 * y * P.β ^ 3 * P.σ + x ^ 2 * y * P.β ^ 3 * P.φy
      + x ^ 2 * y * P.β ^ 2 * P.σ * P.lamP + x ^ 2 * y * P.β ^ 2 * P.σ * P.lamW
      + 10 * x ^ 2 * y * P.β ^ 2 * P.σ + x ^ 2 * y * P.β ^ 2 * P.κp * P.φp
      + x ^ 2 * y * P.β ^ 2 * P.κp + x ^ 2 * y * P.β ^ 2 * P.κw * P.φw
      + x ^ 2 * y * P.β ^ 2 * P.lamP * P.φy + x ^ 2 * y * P.β ^ 2 * P.lamW * P.φy
      + 5 * x ^ 2 * y * P.β ^ 2 * P.φy + 4 * x ^ 2 * y * P.β * P.σ * P.lamP
      + 4 * x ^ 2 * y * P.β * P.σ * P.lamW + 7 * x ^ 2 * y * P.β * P.σ
      + x ^ 2 * y * P.β * P.κp * P.lamW + 4 * x ^ 2 * y * P.β * P.κp
      + x ^ 2 * y * P.β * P.κw * P.lamP - 4 * x * y ^ 3 * P.β ^ 3 * P.σ
      - 2 * x * y ^ 3 * P.β ^ 3 * P.φy - 2 * x * y ^ 3 * P.β ^ 2 * P.σ * P.lamP
      - 2 * x * y ^ 3 * P.β ^ 2 * P.σ * P.lamW - 2 * x * y ^ 3 * P.β ^ 2 * P.κp
      - 2 * x * y * P.β ^ 2 * P.σ - 2 * x * y * P.β ^ 2 * P.φy - 2 * x * y * P.β * P.σ * P.lamP
      - 2 * x * y * P.β * P.σ * P.lamW - 8 * x * y * P.β * P.σ - 2 * x * y * P.β * P.κp * P.φp
      - 2 * x * y * P.β * P.κp - 2 * x * y * P.β * P.κw * P.φw - 2 * x * y * P.β * P.lamP * P.φy
      - 2 * x * y * P.β * P.lamW * P.φy - 4 * x * y * P.β * P.φy - 2 * x * y * P.σ * P.lamP
      - 2 * x * y * P.σ * P.lamW - 2 * x * y * P.σ - 2 * x * y * P.κp * P.lamW
      - 2 * x * y * P.κp - 2 * x * y * P.κw * P.lamP - y ^ 5 * P.β ^ 3 * P.σ
      + y ^ 3 * P.β ^ 3 * P.σ + y ^ 3 * P.β ^ 3 * P.φy + y ^ 3 * P.β ^ 2 * P.σ * P.lamP
      + y ^ 3 * P.β ^ 2 * P.σ * P.lamW + 2 * y ^ 3 * P.β ^ 2 * P.σ
      + y ^ 3 * P.β ^ 2 * P.κp * P.φp + y ^ 3 * P.β ^ 2 * P.κp + y ^ 3 * P.β ^ 2 * P.κw * P.φw
      + y ^ 3 * P.β ^ 2 * P.lamP * P.φy + y ^ 3 * P.β ^ 2 * P.lamW * P.φy
      + y ^ 3 * P.β ^ 2 * P.φy - y ^ 3 * P.β * P.σ + y ^ 3 * P.β * P.κp * P.lamW
      + y ^ 3 * P.β * P.κw * P.lamP + y * P.β ^ 2 * P.lamP * P.φy + y * P.β ^ 2 * P.lamW * P.φy
      + y * P.β * P.σ - y * P.β * P.κp * P.lamW * P.φp - y * P.β * P.κp * P.lamW * P.φw
      + y * P.β * P.κp * P.lamW - y * P.β * P.κw * P.lamP * P.φp
      - y * P.β * P.κw * P.lamP * P.φw + y * P.β * P.κw * P.lamP + y * P.β * P.φy
      + y * P.σ * P.lamP + y * P.σ * P.lamW + 2 * y * P.σ + y * P.κp * P.lamW * P.φp
      + y * P.κp * P.lamW * P.φw + y * P.κp * P.lamW + y * P.κp * P.φp + y * P.κp
      + y * P.κw * P.lamP * P.φp + y * P.κw * P.lamP * P.φw + y * P.κw * P.lamP
      + y * P.κw * P.φw + y * P.lamP * P.φy + y * P.lamW * P.φy + y * P.φy) * hxy

namespace Par

/-- Galí (2015), p. 174: The complex coefficient vector of `q`. -/
noncomputable def qv (P : Par) : Fin 5 → ℂ := ![(P.c0 : ℂ), P.c1, P.c2, P.c3, P.c4]

/-- Galí (2015), p. 174: The quartic `q(z)`, with `det(A₀ʷ − z A₁ʷ) = −q(z)`. -/
noncomputable def qC (P : Par) : ℂ[X] := quart P.qv

/-- Galí (2015), p. 174: The reversed coefficient vector. -/
noncomputable def Qv (P : Par) : Fin 5 → ℂ := ![(P.c4 : ℂ), P.c3, P.c2, P.c1, P.c0]

/-- Galí (2015), p. 174: The reversed quartic `Q(w) = w⁴ q(1/w)`, whose roots are the eigenvalues of
`(A₀ʷ)⁻¹ A₁ʷ`. -/
noncomputable def QC (P : Par) : ℂ[X] := quart P.Qv

/-- Galí (2015), p. 174: `q(z)` in coefficient form. -/
theorem eval_qC (P : Par) (z : ℂ) :
    P.qC.eval z = P.c0 + P.c1 * z + P.c2 * z ^ 2 + P.c3 * z ^ 3 + P.c4 * z ^ 4 := by
  simp [qC, qv, eval_quart]

/-- Galí (2015), p. 174: the reversed quartic `Q(w)` in coefficient form. -/
theorem eval_QC (P : Par) (z : ℂ) :
    P.QC.eval z = P.c4 + P.c3 * z + P.c2 * z ^ 2 + P.c1 * z ^ 3 + P.c0 * z ^ 4 := by
  simp [QC, Qv, eval_quart]

/-- Galí (2015), p. 174: `Q(w) = w⁴ q(1/w)`, so the roots of `Q` (eigenvalues of `Aʷ`) are
the reciprocals of the roots of `q`. -/
theorem eval_QC_eq (P : Par) {w : ℂ} (hw : w ≠ 0) : P.QC.eval w = w ^ 4 * P.qC.eval w⁻¹ := by
  rw [eval_QC, eval_qC]
  field_simp
  ring

/-- Galí (2015), p. 174: `q` at a real point is real. -/
theorem eval_qC_ofReal (P : Par) (r : ℝ) : P.qC.eval (r : ℂ) = (P.qr r : ℂ) := by
  rw [eval_qC]; simp [qr]

/-- Galí (2015), p. 174: `q` has real coefficients, `q(z̄) = conj (q z)`. -/
theorem eval_qC_conj (P : Par) (z : ℂ) :
    P.qC.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.qC.eval z) := by
  simp [eval_qC, map_add, map_mul, map_pow]

/-- Galí (2015), p. 174: real and imaginary parts of `q(x + i y)`. -/
theorem eval_qC_mk (P : Par) (x y : ℝ) : P.qC.eval ⟨x, y⟩ =
    ⟨P.c0 + P.c1 * x + P.c2 * (x ^ 2 - y ^ 2) + P.c3 * (x ^ 3 - 3 * x * y ^ 2)
      + P.c4 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4),
     P.c1 * y + P.c2 * (2 * x * y) + P.c3 * (3 * x ^ 2 * y - y ^ 3)
      + P.c4 * (4 * x ^ 3 * y - 4 * x * y ^ 3)⟩ := by
  rw [eval_qC]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/-- Galí (2015), p. 174: The sign conditions of the book (all coefficients nonnegative, `0 < β <
1`, `σ > 0`,
`λ_p, λ_w > 0`), with `κ_p, κ_w ≥ 0`. -/
def Adm (P : Par) : Prop :=
  0 < P.β ∧ P.β < 1 ∧ 0 < P.σ ∧ 0 ≤ P.κp ∧ 0 ≤ P.κw ∧ 0 < P.lamP ∧ 0 < P.lamW ∧
    0 ≤ P.φp ∧ 0 ≤ P.φw ∧ 0 ≤ P.φy

/-- Galí (2015), p. 174: `q(−1)` as minus a sum of terms that are nonnegative under the sign
conditions. -/
theorem qr_neg_one (P : Par) : P.qr (-1) =
    -(2 * P.σ * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) + P.κp * (2 + 2 * P.β) + P.Ψ)
    - P.φy * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW))
    - P.φp * (P.κp * (2 + 2 * P.β) + P.Ψ) - P.φw * (P.κw * (2 + 2 * P.β) + P.Ψ) := by
  simp only [qr, c0, c1, c2, c3, c4, Ψ]; ring

/-- Galí (2015), p. 174: `Ψ = λ_w κ_p + λ_p κ_w ≥ 0` under the sign conditions. -/
theorem Ψ_nonneg {P : Par} (hP : P.Adm) : 0 ≤ P.Ψ := by
  obtain ⟨-, -, -, hkp, hkw, hlp, hlw, -⟩ := hP
  unfold Ψ
  exact add_nonneg (mul_nonneg hlw.le hkp) (mul_nonneg hlp.le hkw)

/-- Galí (2015), p. 174: `q(−1) < 0`, so `−1` is never an eigenvalue. -/
theorem qr_neg_one_neg {P : Par} (hP : P.Adm) : P.qr (-1) < 0 := by
  have hΨ := Ψ_nonneg hP
  obtain ⟨hb0, -, hs, hkp, hkw, hlp, hlw, hfp, hfw, hfy⟩ := hP
  rw [qr_neg_one]
  have h1 : 0 < 2 * P.σ * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) := by positivity
  have h2 : 0 ≤ P.φy * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) := by positivity
  have h3 : 0 ≤ P.φp * (P.κp * (2 + 2 * P.β) + P.Ψ) := by positivity
  have h4 : 0 ≤ P.φw * (P.κw * (2 + 2 * P.β) + P.Ψ) := by positivity
  have h5 : 0 ≤ P.κp * (2 + 2 * P.β) := by positivity
  linarith

/-- Galí (2015), p. 174: `q(0) = −det A₀ʷ < 0`. -/
theorem c0_neg {P : Par} (hP : P.Adm) : P.c0 < 0 := by
  obtain ⟨-, -, hs, hkp, hkw, -, -, hfp, hfw, hfy⟩ := hP
  unfold c0
  nlinarith [mul_nonneg hkp hfp, mul_nonneg hkw hfw]

/-- Galí (2015), p. 174: the leading coefficient `−β² σ` of `q` is negative. -/
theorem c4_neg {P : Par} (hP : P.Adm) : P.c4 < 0 := by
  obtain ⟨hb, -, hs, -⟩ := hP
  unfold c4
  nlinarith [mul_pos (pow_pos hb 2) hs]

/-- Galí (2015), p. 174: the circle certificate forces `q(1) < 0` at any root `x + i y`,
`y > 0`, on the unit circle. -/
theorem qr_one_neg_of_root {P : Par} (hP : P.Adm) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1)
    (hy : 0 < y) (h0 : P.qC.eval ⟨x, y⟩ = 0) : P.qr 1 < 0 := by
  have hΨ := Ψ_nonneg hP
  obtain ⟨hb0, hb1, hs, hkp, -, hlp, hlw, -, -, hfy⟩ := hP
  rw [eval_qC_mk] at h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hc := circle_cert P hxy hre him
  have hx1 : x ≤ 1 := by nlinarith
  have he2p : 0 < ((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (mul_pos (by linarith) hy) 2)
  have hA : 0 ≤ 2 * P.Ψ * (1 - x) := mul_nonneg (by linarith) (by linarith)
  have hbx : P.β * x ≤ P.β := by
    have := mul_le_mul_of_nonneg_left hx1 hb0.le
    linarith
  have hB : 0 < (((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
      * (P.κp + P.σ * (1 + P.β - 2 * P.β * x + (P.lamP + P.lamW))) :=
    mul_pos he2p (add_pos_of_nonneg_of_pos hkp (mul_pos hs (by linarith)))
  have hC : 0 ≤ P.φy * P.β * ((((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2
      + ((1 - P.β) * y) ^ 2) + 2 * (P.lamP + P.lamW) * (1 - x)) :=
    mul_nonneg (mul_nonneg hfy hb0.le)
      (add_nonneg he2p.le (mul_nonneg (by linarith) (by linarith)))
  have hsum := mul_pos hy (add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hA hB) hC)
  by_contra hq
  have hq' : 0 ≤ (1 - P.β) * y * P.qr 1 :=
    mul_nonneg (mul_nonneg (by linarith) hy.le) (not_lt.mp hq)
  linarith

/-- Galí (2015), p. 174: when `q(1) > 0`, i.e. the condition of p. 174 holds, `q` has no root on
the unit circle. -/
theorem qC_ne_zero_of_norm_eq_one {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {z : ℂ}
    (hz : ‖z‖ = 1) : P.qC.eval z ≠ 0 := by
  obtain ⟨x, y⟩ := z
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have h := Complex.sq_norm (⟨x, y⟩ : ℂ)
    rw [hz, Complex.normSq_mk] at h
    nlinarith
  rcases lt_trichotomy y 0 with hy | hy | hy
  · intro h0
    have hconj : P.qC.eval ⟨x, -y⟩ = 0 := by
      have := eval_qC_conj P ⟨x, y⟩
      rw [h0, map_zero] at this
      exact this
    exact absurd (qr_one_neg_of_root hP (by nlinarith) (by linarith) hconj) (not_lt.mpr h1.le)
  · subst hy
    have hx : x = 1 ∨ x = -1 := by
      have : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    have hz' : (⟨x, 0⟩ : ℂ) = (x : ℂ) := Complex.ext (by simp) (by simp)
    rw [hz', eval_qC_ofReal]
    intro h0
    have h0' : P.qr x = 0 := by exact_mod_cast h0
    rcases hx with rfl | rfl
    · linarith
    · linarith [qr_neg_one_neg hP]
  · exact fun h0 => absurd (qr_one_neg_of_root hP hxy hy h0) (not_lt.mpr h1.le)

/-- Galí (2015), p. 174: The reversed quartic has no root on the unit circle when `q(1) > 0`. -/
theorem QC_ne_zero_of_norm_eq_one {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {w : ℂ}
    (hw : ‖w‖ = 1) : P.QC.eval w ≠ 0 := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  rw [eval_QC_eq P hw0]
  refine mul_ne_zero (pow_ne_zero _ hw0) (qC_ne_zero_of_norm_eq_one hP h1 ?_)
  rw [norm_inv, hw, inv_one]

end Par

/-- Galí (2015), p. 174 (tool): the leading coefficient of a quartic. -/
theorem coeff_quart_four (a : Fin 5 → ℂ) : (quart a).coeff 4 = a 4 := by
  simp [quart, coeff_X_pow, coeff_C_mul]

/-- Galí (2015), p. 174 (tool): a quartic with nonzero leading coefficient is nonzero. -/
theorem quart_ne_zero {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : quart a ≠ 0 := by
  intro h0
  apply h
  rw [← coeff_quart_four a, h0, coeff_zero]

namespace Par

/-- Galí (2015), p. 174: Linear interpolation between two parameter vectors (the homotopy of the
proof). -/
def mix (P Q : Par) (s : ℝ) : Par :=
  ⟨(1 - s) * P.β + s * Q.β, (1 - s) * P.σ + s * Q.σ, (1 - s) * P.κp + s * Q.κp,
    (1 - s) * P.κw + s * Q.κw, (1 - s) * P.lamP + s * Q.lamP, (1 - s) * P.lamW + s * Q.lamW,
    (1 - s) * P.φp + s * Q.φp, (1 - s) * P.φw + s * Q.φw, (1 - s) * P.φy + s * Q.φy⟩

/-- Galí (2015), p. 174 (homotopy): the path starts at `P`. -/
theorem mix_zero (P Q : Par) : P.mix Q 0 = P := by
  cases P; simp [mix]

/-- Galí (2015), p. 174 (homotopy): the path ends at `Q`. -/
theorem mix_one (P Q : Par) : P.mix Q 1 = Q := by
  cases Q; simp [mix]

/-- Galí (2015), p. 174 (homotopy): the sign conditions are convex. -/
theorem adm_mix {P Q : Par} (hP : P.Adm) (hQ : Q.Adm) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (P.mix Q s).Adm := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hP
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hQ
  have h1s : 0 ≤ 1 - s := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mix]
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a1
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a2
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a3
    · nlinarith
  · positivity
  · positivity
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a6
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a7
    · nlinarith
  · positivity
  · positivity
  · positivity

/-- Galí (2015), p. 174 (homotopy): the coefficients move continuously along the path. -/
theorem continuous_Qv_mix (P Q : Par) (i : Fin 5) : Continuous fun s => (P.mix Q s).Qv i := by
  fin_cases i <;> simp only [Qv, c0, c1, c2, c3, c4, mix] <;> fun_prop

/-- Galí (2015), p. 174 (homotopy step): along a segment of admissible parameters on which
`q(1) > 0`, the number of eigenvalues inside the unit circle does not change. -/
theorem inCount_QC_mix {P Q : Par} (hP : P.Adm) (hQ : Q.Adm)
    (h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < (P.mix Q s).qr 1) : inCount P.QC = inCount Q.QC := by
  have h := inCount_path (fun s => (P.mix Q s).Qv) (continuous_Qv_mix P Q) ?_ ?_
  · simpa [QC, mix_zero, mix_one] using h
  · intro s hs
    refine quart_ne_zero ?_
    simp only [Qv, Matrix.cons_val]
    exact_mod_cast (c0_neg (adm_mix hP hQ hs)).ne
  · intro s hs z hz
    exact QC_ne_zero_of_norm_eq_one (adm_mix hP hQ hs) (h1 s hs) hz

/-- Galí (2015), p. 174: The reference parameters: `β = 1/2`, `σ = 1`, `κ_p = κ_w = 1`, `λ_p = λ_w
= 21/16`,
`φ_p = 2`, `φ_w = φ_y = 0`. -/
noncomputable def Pref : Par := ⟨1 / 2, 1, 1, 1, 21 / 16, 21 / 16, 2, 0, 0⟩

/-- Galí (2015), p. 174 (reference point): at `Pref`, `Q` factors with roots
`1/2, 1/3, 4, 1/8`. -/
theorem QC_ref : Pref.QC = C (-3) * ((X - C (1 / 2)) * (X - C (1 / 3)) * (X - C 4)
    * (X - C (1 / 8))) := by
  apply Polynomial.funext
  intro z
  rw [eval_QC]
  simp only [Pref, c0, c1, c2, c3, c4, eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  ring

/-- Galí (2015), p. 174 (reference point): three eigenvalues inside the unit circle. -/
theorem inCount_ref : inCount Pref.QC = 3 := by
  rw [QC_ref, inCount, roots_C_mul _ (by norm_num)]
  have h1 : ∀ a : ℂ, X - C a ≠ 0 := X_sub_C_ne_zero
  rw [roots_mul (by simp [h1]), roots_mul (by simp [h1]), roots_mul (by simp [h1])]
  simp only [roots_X_sub_C]
  norm_num [Multiset.filter_cons, Multiset.filter_singleton]

/-- Galí (2015), p. 174 (reference point): `Pref` satisfies the sign conditions. -/
theorem adm_ref : Pref.Adm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Pref] <;> norm_num

/-- Galí (2015), p. 174: The policy endpoint: `φ_p = 2`, `φ_w = φ_y = 0` with the structural
parameters of `P`. -/
def endpt (P : Par) : Par := ⟨P.β, P.σ, P.κp, P.κw, P.lamP, P.lamW, 2, 0, 0⟩

/-- Galí (2015), p. 174 (eigenvalue count): under the sign conditions and `q(1) > 0`, exactly
three roots of `Q` (eigenvalues of `(A₀ʷ)⁻¹ A₁ʷ`) lie in the open unit disc. -/
theorem inCount_QC {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    inCount P.QC = 3 := by
  have hE : P.endpt.Adm := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hP
    exact ⟨a1, a2, a3, a4, a5, a6, a7, by simp [endpt], by simp [endpt], by simp [endpt]⟩
  have step1 : inCount P.QC = inCount P.endpt.QC := by
    refine inCount_QC_mix hP hE fun s hs => ?_
    have : (P.mix P.endpt s).qr 1 = (1 - s) * P.qr 1 + s * P.Ψ := by
      simp only [qr_one, mix, endpt, Ψ]; ring
    rw [this]
    obtain ⟨hs0, hs1⟩ := hs
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using h1
    · have : 0 ≤ (1 - s) * P.qr 1 := mul_nonneg (by linarith) h1.le
      nlinarith
  have step2 : inCount P.endpt.QC = inCount Pref.QC := by
    refine inCount_QC_mix hE adm_ref fun s hs => ?_
    have hm := adm_mix hE adm_ref hs
    have : (P.endpt.mix Pref s).qr 1 = (P.endpt.mix Pref s).Ψ := by
      simp only [qr_one, mix, endpt, Pref, Ψ]; ring
    rw [this]
    obtain ⟨hs0, hs1⟩ := hs
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa [mix_zero, endpt, Ψ] using hΨ
    · obtain ⟨-, -, -, hkp, hkw, hlp, hlw, -⟩ := hm
      have hk : 0 < (P.endpt.mix Pref s).κp := by
        simp only [mix, endpt, Pref] at hkp ⊢
        nlinarith [hP.2.2.2.1]
      unfold Ψ
      nlinarith [mul_pos hlw hk, mul_nonneg hlp.le hkw]
  rw [step1, step2, inCount_ref]

end Par

/-- Galí (2015), p. 174 (tool): a quartic with nonzero leading coefficient has degree four. -/
theorem natDegree_quart {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : (quart a).natDegree = 4 := by
  unfold quart
  compute_degree!

/-- Galí (2015), p. 174 (tool): such a quartic has four complex roots with multiplicity. -/
theorem card_roots_quart {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : (quart a).roots.card = 4 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_quart h]

/-- Galí (2015), p. 174: The number of roots (with multiplicity) of `p` strictly outside the unit
circle. -/
noncomputable def outCount (p : ℂ[X]) : ℕ := (p.roots.filter (fun z => 1 < ‖z‖)).card

/-- Galí (2015), p. 174 (tool): without roots on the unit circle, roots split into those
inside and those outside. -/
theorem inCount_add_outCount {p : ℂ[X]} (hc : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    inCount p + outCount p = p.roots.card := by
  unfold inCount outCount
  have h : p.roots.filter (fun z => 1 < ‖z‖) = p.roots.filter (fun z => ¬ ‖z‖ < 1) := by
    refine Multiset.filter_congr fun z hz => ?_
    have hz1 : ‖z‖ ≠ 1 := fun h1 => hc z h1 (Polynomial.isRoot_of_mem_roots hz)
    constructor
    · intro h; exact not_lt.mpr h.le
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz1)
  rw [h, ← Multiset.card_add, Multiset.filter_add_not]

namespace Par

/-- Galí (2015), p. 174: `Q ≠ 0`. -/
theorem QC_ne_zero {P : Par} (hP : P.Adm) : P.QC ≠ 0 :=
  quart_ne_zero (by simp only [Qv, Matrix.cons_val]; exact_mod_cast (c0_neg hP).ne)

/-- Galí (2015), p. 174: `Aʷ` has four eigenvalues with multiplicity. -/
theorem card_roots_QC {P : Par} (hP : P.Adm) : P.QC.roots.card = 4 :=
  card_roots_quart (by simp only [Qv, Matrix.cons_val]; exact_mod_cast (c0_neg hP).ne)

/-- Galí (2015), p. 174: under the condition, exactly one eigenvalue lies outside the unit
circle. -/
theorem outCount_QC {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    outCount P.QC = 1 := by
  have h := inCount_add_outCount (p := P.QC) fun z hz => QC_ne_zero_of_norm_eq_one hP h1 hz
  rw [inCount_QC hP hΨ h1, card_roots_QC hP] at h
  omega

/-- Galí (2015), p. 174: The derivative `q'(r)`. -/
def dqr (P : Par) (r : ℝ) : ℝ := P.c1 + 2 * P.c2 * r + 3 * P.c3 * r ^ 2 + 4 * P.c4 * r ^ 3

/-- Galí (2015), p. 174: the derivative of `Q` in coefficient form. -/
theorem eval_derivative_QC (P : Par) (w : ℂ) :
    P.QC.derivative.eval w = P.c3 + 2 * P.c2 * w + 3 * P.c1 * w ^ 2 + 4 * P.c0 * w ^ 3 := by
  simp [QC, Qv, eval_derivative_quart]

/-- Galí (2015), p. 174: `q` is continuous on the reals. -/
theorem continuous_qr (P : Par) : Continuous P.qr := by
  unfold qr; fun_prop

/-- Galí (2015), p. 174: `q(0)` is the constant coefficient. -/
theorem qr_zero (P : Par) : P.qr 0 = P.c0 := by simp [qr]

/-- Galí (2015), p. 174: `q(0)` is the constant coefficient (complex form). -/
theorem qC_eval_zero (P : Par) : P.qC.eval 0 = P.c0 := by simp [eval_qC]

/-- Galí (2015), p. 174: A root `ζ` of `q` in the closed unit disc gives the root `ζ⁻¹` of `Q`
strictly outside the
unit circle (when `q(1) > 0`). -/
theorem inv_mem_out {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (h0 : P.qC.eval ζ = 0) : ζ⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [qC_eval_zero] at h0
    exact (c0_neg hP).ne (by exact_mod_cast h0)
  have hroot : P.QC.eval ζ⁻¹ = 0 := by
    rw [eval_QC_eq P (inv_ne_zero hζ0), inv_inv, h0, mul_zero]
  rw [Multiset.mem_filter, mem_roots (QC_ne_zero hP)]
  refine ⟨hroot, ?_⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  rw [norm_inv]
  have hge : 1 ≤ ‖ζ‖⁻¹ := one_le_inv_iff₀.mpr ⟨hn, hζ⟩
  refine lt_of_le_of_ne hge fun he => ?_
  exact QC_ne_zero_of_norm_eq_one hP h1 (w := ζ⁻¹) (by rw [norm_inv, ← he]) hroot

/-- Galí (2015), p. 174: under the condition, `q` has exactly one root in the closed unit disc;
it is real, lies in `(0, 1)` and is simple. -/
theorem stable_root {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ P.qr μ = 0 ∧ P.dqr μ ≠ 0 ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ := by
  have hq0 : P.qr 0 < 0 := by rw [qr_zero]; exact c0_neg hP
  obtain ⟨μ, ⟨hμ0, hμ1⟩, hμ⟩ := intermediate_value_Ioo (zero_le_one (α := ℝ))
    (continuous_qr P).continuousOn (show (0 : ℝ) ∈ Set.Ioo (P.qr 0) (P.qr 1) from ⟨hq0, h1⟩)
  obtain ⟨w0, hw0⟩ := Multiset.card_eq_one.mp (outCount_QC hP hΨ h1)
  have hμC : P.qC.eval (μ : ℂ) = 0 := by rw [eval_qC_ofReal, hμ, Complex.ofReal_zero]
  have hμn : ‖(μ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ0]; exact hμ1.le
  have hmem := inv_mem_out hP h1 hμn hμC
  rw [hw0, Multiset.mem_singleton] at hmem
  refine ⟨μ, hμ0, hμ1, hμ, ?_, ?_⟩
  · intro hd
    have hw : ((μ : ℂ))⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := inv_mem_out hP h1 hμn hμC
    have hroot : P.QC.IsRoot ((μ : ℂ))⁻¹ := by
      have := (Multiset.mem_filter.mp hw).1
      exact (mem_roots (QC_ne_zero hP)).mp this
    have hder : P.QC.derivative.IsRoot ((μ : ℂ))⁻¹ := by
      have hμ0' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
      have e1 : (P.qr μ : ℂ) = 0 := by rw [hμ]; simp
      have e2 : (P.dqr μ : ℂ) = 0 := by rw [hd]; simp
      simp only [qr, dqr] at e1 e2
      push_cast at e1 e2
      rw [IsRoot, eval_derivative_QC]
      field_simp
      linear_combination 4 * e1 - (μ : ℂ) * e2
    have hmult := (one_lt_rootMultiplicity_iff_isRoot (QC_ne_zero hP)).mpr ⟨hroot, hder⟩
    have hcnt : 2 ≤ (P.QC.roots.filter (fun z => 1 < ‖z‖)).count ((μ : ℂ))⁻¹ := by
      rw [Multiset.count_filter_of_pos (p := fun z : ℂ => 1 < ‖z‖) (Multiset.mem_filter.mp hw).2,
        count_roots]
      omega
    have hle := Multiset.count_le_card ((μ : ℂ))⁻¹ (P.QC.roots.filter (fun z => 1 < ‖z‖))
    have hc1 : (P.QC.roots.filter (fun z => 1 < ‖z‖)).card = 1 := outCount_QC hP hΨ h1
    omega
  · intro ζ hζ h0
    have hm := inv_mem_out hP h1 hζ h0
    rw [hw0, Multiset.mem_singleton, ← hmem] at hm
    exact inv_injective hm

end Par

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn, the tool): if every complex eigenvalue of a
real square matrix `K` lies in the open unit disc, the entries of `Kᵏ` decay geometrically
(Gelfand's spectral radius formula). -/
theorem pow_entry_bound {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ w : ℂ, (Matrix.scalar (Fin n) w - K.map Complex.ofReal).det = 0 → ‖w‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  have hpow : ∀ k, ((K ^ k).map Complex.ofReal) = (K.map Complex.ofReal) ^ k := fun k =>
    (Complex.ofRealHom.mapMatrix.map_pow K k)
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix (Fin n) (Fin n) ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    refine ⟨?_, h w ?_⟩
    · rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero]
      exact hw
    · rw [← Matrix.eval_charpoly]; exact hw
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have hw' : w ∈ spectrum ℂ A := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero] at hw
      exact hw
    have := (hspec w hw').2
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
  have hρ0r : (ρ0 : ℝ) < r := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr1 : r < 1 := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- norm bound for large powers
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
  have hCb0 : 0 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
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
      have := congrFun (congrFun (hpow k) i) j
      exact this.symm
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

/-- Galí (2015), p. 174: A matrix acting on a vector of random variables: `(M a)_i = ∑_j M_{ij}
a_j`. -/
def rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Galí (2015), p. 174 (tool): matrices act on vectors of random variables compatibly with
multiplication. -/
theorem rvMul_rvMul {Ω : Type*} {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Galí (2015), p. 174 (tool): additivity of the action. -/
theorem rvMul_add {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Galí (2015), p. 174 (tool): the action respects subtraction. -/
theorem rvMul_sub {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Galí (2015), p. 174 (tool): the identity matrix acts trivially. -/
theorem rvMul_one {Ω : Type*} {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]

/-- Galí (2015), p. 174 (tool): the action on the zero vector. -/
theorem rvMul_zero {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    rvMul M (0 : Fin m → Ω → ℝ) = 0 := by
  funext i
  simp [rvMul]

/-- Galí (2015), p. 174 (tool): the action, pointwise. -/
theorem rvMul_apply {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]

namespace Fwd

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 174 (tool): `E_t` commutes with constant matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Galí (2015), p. 174: A vector process solves the forward system `s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Galí (2015), p. 174: A vector process is adapted. -/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Galí (2015), p. 174: A vector process is bounded. -/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Galí (2015), p. 174: Iterating a homogeneous forward system: `d_t = Kᵏ E_t d_{t+k}`. -/
theorem fsolves_iterate {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {d : ℕ → Fin n → Ω → ℝ}
    (hd : FSolves 𝔼 K 0 d) (had : VAdapted 𝔼 d) (t k : ℕ) :
    d t = rvMul (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, rvMul_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) =
        rvMul K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_rvMul 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, rvMul_rvMul, ← pow_succ]

/-- Galí (2015), p. 174: Bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_rvMul_pow_le {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) (k : ℕ) {a : Fin n → Ω → ℝ} {M : ℝ}
    (ha : ∀ j ω, |a j ω| ≤ M) (i : Fin n) (ω : Ω) :
    |rvMul (K ^ k) a i ω| ≤ n * (Cb * ρ ^ k * M) := by
  rw [rvMul_apply]
  have hM : 0 ≤ M := (abs_nonneg _).trans (ha i ω)
  calc |∑ j, (K ^ k) i j * a j ω| ≤ ∑ j, |(K ^ k) i j * a j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, Cb * ρ ^ k * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hK k i j) (ha j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (hK k i j))
    _ = n * (Cb * ρ ^ k * M) := by simp

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn): if the powers of `K` decay geometrically, the
forward system `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted solution. -/
theorem fsolves_unique {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → Fin n → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : VAdapted 𝔼 x)
    (hay : VAdapted 𝔼 y) (hbx : VBounded x) (hby : VBounded y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → Fin n → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, rvMul, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : VAdapted 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ n * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (n : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (n : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn): if the powers of `K` decay geometrically, the
forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution of
`s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k)
    {w : ℕ → Fin n → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : VAdapted 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ VAdapted 𝔼 s ∧ VBounded s := by
  set Mb : ℝ := n * Cb * Mw with hMb
  set B : ℕ → ℕ → Fin n → Ω → ℝ := fun k t => rvMul (K ^ k) (fun j => 𝔼.E t (w (t + k) j))
    with hB
  have hT : ∀ k t t' i ω, |rvMul (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ n * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => rvMul (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → Fin n → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_rvMul 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, rvMul_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← rvMul_apply, rvMul_rvMul, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, rvMul_apply]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ => (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left
        (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_rvMul 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

end Fwd

namespace Par

/-- Galí (2015), eq. (24), p. 173: the matrix `A₀ʷ`. -/
def A0 (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ + P.φy, P.φp, P.φw, 0; -P.κp, 1, 0, 0; -P.κw, 0, 1, 0; 0, -1, 1, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `A₁ʷ`. -/
def A1 (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ, 1, 0, 0; 0, P.β, 0, P.lamP; 0, 0, P.β, -P.lamW; 0, 0, 0, 1]

/-- Galí (2015), p. 174: `det(A₀ʷ − z A₁ʷ) = −q(z)` for complex `z`. -/
theorem det_A0_sub_A1 (P : Par) (z : ℂ) :
    (P.A0.map Complex.ofReal - z • P.A1.map Complex.ofReal).det = -(P.qC.eval z) := by
  rw [eval_qC]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A0, A1, c0, c1, c2, c3, c4]
  ring

/-- Galí (2015), p. 174: `det(A₀ʷ − r A₁ʷ) = −q(r)` for real `r`. -/
theorem det_A0_sub_A1_real (P : Par) (r : ℝ) : (P.A0 - r • P.A1).det = -(P.qr r) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A0, A1, qr, c0, c1, c2, c3,
    c4]
  ring

end Par

/-- Galí (2015), eq. (24), p. 173: the matrix `B₀ʷ`. -/
def B0 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0; 0, 1]

namespace Par

/-- Galí (2015), p. 174: `D(r) = (r − 1)(1 − β r) + (λ_p + λ_w) r`. -/
def Dr (P : Par) (r : ℝ) : ℝ := -P.β * r ^ 2 + (1 + P.β + (P.lamP + P.lamW)) * r - 1

/-- Galí (2015), p. 174: `Br(r) = (σ + φ_y − σ r)(1 − β r) + (φ_p − r) κ_p + φ_w κ_w`. -/
def Brr (P : Par) (r : ℝ) : ℝ :=
  P.σ * P.β * r ^ 2 - (P.σ + P.β * (P.σ + P.φy) + P.κp) * r
    + (P.σ + P.φy + P.φp * P.κp + P.φw * P.κw)

/-- Galí (2015), p. 174: `H(r) = (φ_p − r) λ_p − φ_w λ_w`. -/
def Hr (P : Par) (r : ℝ) : ℝ := -P.lamP * r + (P.φp * P.lamP - P.φw * P.lamW)

/-- Galí (2015), p. 174: The factorisation `q(r) = Br(r) D(r) + r (κ_w − κ_p) H(r)`. -/
theorem qr_factor (P : Par) (r : ℝ) :
    P.qr r = P.Brr r * P.Dr r + r * (P.κw - P.κp) * P.Hr r := by
  simp only [qr, Brr, Dr, Hr, c0, c1, c2, c3, c4]; ring

/-- Galí (2015), p. 174: the derivative of the factorisation `q = Br D + r (κ_w − κ_p) H`. -/
theorem dqr_factor (P : Par) (r : ℝ) :
    P.dqr r = (2 * P.σ * P.β * r - (P.σ + P.β * (P.σ + P.φy) + P.κp)) * P.Dr r
      + P.Brr r * (-2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)))
      + (P.κw - P.κp) * (P.Hr r - P.lamP * r) := by
  simp only [dqr, Brr, Dr, Hr, c1, c2, c3, c4]; ring

/-- Galí (2015), p. 174: The eigen-equations `(A₀ʷ − μ A₁ʷ) (g₀, g₁, g₂, 1)ᵀ = 0`: the stable
mode, normalised on
the predetermined real wage gap. -/
def StableVec (P : Par) (μ : ℝ) (g : Fin 3 → ℝ) : Prop :=
  (P.σ + P.φy) * g 0 + P.φp * g 1 + P.φw * g 2 - μ * (P.σ * g 0 + g 1) = 0 ∧
  -P.κp * g 0 + g 1 - μ * (P.β * g 1 + P.lamP) = 0 ∧
  -P.κw * g 0 + g 2 - μ * (P.β * g 2 - P.lamW) = 0 ∧
  -g 1 + g 2 + 1 - μ = 0

/-- Galí (2015), p. 174: Normalising an eigenvector `v` of `A₀ʷ − μ A₁ʷ` with `v₃ ≠ 0`. -/
theorem stableVec_of_hom (P : Par) {μ v0 v1 v2 v3 : ℝ} (hv3 : v3 ≠ 0)
    (h1 : (P.σ + P.φy) * v0 + P.φp * v1 + P.φw * v2 - μ * (P.σ * v0 + v1) = 0)
    (h2 : -P.κp * v0 + v1 - μ * (P.β * v1 + P.lamP * v3) = 0)
    (h3 : -P.κw * v0 + v2 - μ * (P.β * v2 - P.lamW * v3) = 0)
    (h4 : -v1 + v2 + v3 - μ * v3 = 0) : P.StableVec μ ![v0 / v3, v1 / v3, v2 / v3] := by
  have hinv : v3 * v3⁻¹ = 1 := mul_inv_cancel₀ hv3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv]
  · linear_combination v3⁻¹ * h1
  · linear_combination v3⁻¹ * h2 + μ * P.lamP * hinv
  · linear_combination v3⁻¹ * h3 - μ * P.lamW * hinv
  · linear_combination v3⁻¹ * h4 - (1 - μ) * hinv

/-- Galí (2015), p. 174: the stable root `μ` has an eigenvector whose real-wage-gap component
is nonzero. -/
theorem exists_stableVec {P : Par} (hP : P.Adm) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) : ∃ g, P.StableVec μ g := by
  obtain ⟨hb0, hb1, -, -, -, hlp, hlw, -⟩ := hP
  have hb : 0 < 1 - P.β * μ := by nlinarith
  have hb' : (1 - P.β * μ) ≠ 0 := hb.ne'
  rw [qr_factor] at hq
  by_cases hBr : P.Brr μ = 0
  · -- then `κ_w ≠ κ_p`, and the first eigenvector field works
    have hk : P.κw - P.κp ≠ 0 := by
      intro hk
      obtain ⟨μD, ⟨hD0, hD1⟩, hDμ⟩ := intermediate_value_Ioo (zero_le_one (α := ℝ))
        (show Continuous P.Dr by unfold Dr; fun_prop).continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.Dr 0) (P.Dr 1) by
          simp only [Dr, Set.mem_Ioo]; constructor <;> nlinarith)
      have hqD : P.qr μD = 0 := by rw [qr_factor, hDμ, hk]; ring
      have hμD : (μD : ℂ) = μ := huniq μD (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]; exact hD1.le)
        (by rw [eval_qC_ofReal, hqD, Complex.ofReal_zero])
      have hμD' : μD = μ := by exact_mod_cast hμD
      subst hμD'
      exact hd (by rw [dqr_factor, hDμ, hBr, hk]; ring)
    refine ⟨_, P.stableVec_of_hom (v0 := P.Dr μ * (1 - P.β * μ))
      (v1 := P.κp * P.Dr μ + P.lamP * μ * (P.κw - P.κp))
      (v2 := P.κw * P.Dr μ - P.lamW * μ * (P.κw - P.κp)) (mul_ne_zero hk hb') ?_ ?_ ?_ ?_⟩
    · simp only [Brr, Dr, Hr] at hq ⊢
      linear_combination hq
    · ring
    · ring
    · simp only [Dr]; ring
  · refine ⟨_, P.stableVec_of_hom (v0 := -μ * P.Hr μ * (1 - P.β * μ))
      (v1 := -P.κp * μ * P.Hr μ + P.lamP * μ * P.Brr μ)
      (v2 := -P.κw * μ * P.Hr μ - P.lamW * μ * P.Brr μ) (mul_ne_zero hBr hb') ?_ ?_ ?_ ?_⟩
    · simp only [Brr, Hr]; ring
    · ring
    · ring
    · simp only [Dr, Hr, Brr] at hq ⊢
      linear_combination -hq

end Par

namespace Par

/-- Galí (2015), p. 174: The matrix acting on `(ẑ_t, n_t)` after quasi-differencing by the stable
mode:
the first three columns of `A₀ʷ` and `−A₁ʷ v`, `v = (g, 1)`. -/
def Cm (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ + P.φy, P.φp, P.φw, -(P.σ * g 0 + g 1); -P.κp, 1, 0, -(P.β * g 1 + P.lamP);
    -P.κw, 0, 1, -(P.β * g 2 - P.lamW); 0, -1, 1, -1]

/-- Galí (2015), p. 174: The first three columns of `A₁ʷ` (and a zero column). -/
def Dm (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ, 1, 0, 0; 0, P.β, 0, 0; 0, 0, P.β, 0; 0, 0, 0, 0]

/-- Galí (2015), p. 174: The change of basis `[e₀ e₁ e₂ v]`. -/
def Vm (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, g 0; 0, 1, 0, g 1; 0, 0, 1, g 2; 0, 0, 0, 1]

/-- Galí (2015), p. 174: `(A₀ʷ − z A₁ʷ) V = (C − z D) diag(1, 1, 1, z − μ)`, whence
`det(C − z D) (z − μ) = −q(z)`. -/
theorem det_Cm_sub_mul {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g) (z : ℂ) :
    ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det * (z - μ) =
      -(P.qC.eval z) := by
  obtain ⟨e1, e2, e3, e4⟩ := hg
  have c1 : ((P.σ : ℂ) + P.φy) * g 0 + P.φp * g 1 + P.φw * g 2 - μ * (P.σ * g 0 + g 1) = 0 := by
    exact_mod_cast e1
  have c2 : -(P.κp : ℂ) * g 0 + g 1 - μ * (P.β * g 1 + P.lamP) = 0 := by exact_mod_cast e2
  have c3 : -(P.κw : ℂ) * g 0 + g 2 - μ * (P.β * g 2 - P.lamW) = 0 := by exact_mod_cast e3
  have c4 : -(g 1 : ℂ) + g 2 + 1 - μ = 0 := by exact_mod_cast e4
  have hmat : (P.A0.map Complex.ofReal - z • P.A1.map Complex.ofReal) * (Vm g).map Complex.ofReal =
      ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal) *
        Matrix.diagonal ![1, 1, 1, z - μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, A0, A1, Cm, Dm, Vm, Matrix.diagonal]
    · linear_combination c1
    · linear_combination c2
    · linear_combination c3
    · linear_combination c4
  have hV : ((Vm g).map Complex.ofReal).det = 1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Vm]
  have hd := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, hV, mul_one, det_A0_sub_A1, Matrix.det_diagonal,
    Fin.prod_univ_four] at hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_mul] at hd
  exact hd.symm

/-- Galí (2015), p. 174: The cubic `r(z) = q(z)/(z − μ)` (synthetic division). -/
noncomputable def rr (P : Par) (μ : ℝ) (z : ℂ) : ℂ :=
  P.c4 * z ^ 3 + (P.c3 + μ * P.c4) * z ^ 2 + (P.c2 + μ * (P.c3 + μ * P.c4)) * z
    + (P.c1 + μ * (P.c2 + μ * (P.c3 + μ * P.c4)))

/-- Galí (2015), p. 174: `q(z) = (z − μ) r(z)` when `q(μ) = 0`. -/
theorem qC_eq_mul_rr (P : Par) {μ : ℝ} (hq : P.qr μ = 0) (z : ℂ) :
    P.qC.eval z = (z - μ) * P.rr μ z := by
  have hq' : (P.qr μ : ℂ) = 0 := by rw [hq, Complex.ofReal_zero]
  simp only [qr] at hq'
  push_cast at hq'
  rw [eval_qC, rr]
  linear_combination hq'

/-- Galí (2015), p. 174: `r(μ) = q′(μ)`. -/
theorem rr_self (P : Par) (μ : ℝ) : P.rr μ μ = P.dqr μ := by
  simp only [rr, dqr]; push_cast; ring

/-- Galí (2015), p. 174: `r` is continuous. -/
theorem continuous_rr (P : Par) (μ : ℝ) : Continuous (P.rr μ) := by
  unfold rr; fun_prop

/-- Galí (2015), p. 174: `det(C − z D) = −r(z)` for every complex `z`. -/
theorem det_Cm_sub {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g) (hq : P.qr μ = 0)
    (z : ℂ) : ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det = -P.rr μ z := by
  have hcont : Continuous fun z : ℂ =>
      ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det :=
    Continuous.matrix_det (continuous_const.sub (continuous_id.smul continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (μ : ℂ)) hcont
    (continuous_rr P μ).neg (fun z hz => by
      have hz' : z - μ ≠ 0 := sub_ne_zero.mpr hz
      have h := det_Cm_sub_mul hg z
      rw [qC_eq_mul_rr P hq] at h
      apply mul_right_cancel₀ hz'
      rw [h, Pi.neg_apply]; ring)
  exact congrFun heq z

/-- Galí (2015), p. 174: `r` has no root in the closed unit disc. -/
theorem rr_ne_zero {P : Par} {μ : ℝ} (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    P.rr μ z ≠ 0 := by
  intro h0
  have hzμ : z = μ := huniq z hz (by rw [qC_eq_mul_rr P hq, h0, mul_zero])
  rw [hzμ, rr_self] at h0
  exact hd (by exact_mod_cast h0)

/-- Galí (2015), p. 174: The forward matrix `K = C⁻¹ D` of the quasi-differenced system. -/
noncomputable def Km (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := (P.Cm g)⁻¹ * P.Dm

/-- Galí (2015), p. 174: The forcing matrix `F = C⁻¹ B₀ʷ`. -/
noncomputable def Fm (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ := (P.Cm g)⁻¹ * B0

/-- Galí (2015), p. 174: the quasi-differenced system is well defined, `det C ≠ 0`. -/
theorem det_Cm_ne_zero {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) : (P.Cm g).det ≠ 0 := by
  intro h0
  have h := det_Cm_sub hg hq 0
  rw [zero_smul, sub_zero] at h
  have hc : ((P.Cm g).map Complex.ofReal).det = ((P.Cm g).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom (P.Cm g)).symm
  rw [hc, h0, Complex.ofReal_zero] at h
  exact rr_ne_zero hq hd huniq (z := 0) (by simp) (neg_eq_zero.mp h.symm)

/-- Galí (2015), p. 174: every eigenvalue of `K = C⁻¹ D` lies in the open unit disc. -/
theorem Km_eigen {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) (w : ℂ)
    (hw : (Matrix.scalar (Fin 4) w - (P.Km g).map Complex.ofReal).det = 0) : ‖w‖ < 1 := by
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; exact zero_lt_one
  have hCu : IsUnit (P.Cm g).det := isUnit_iff_ne_zero.mpr (det_Cm_ne_zero hg hq hd huniq)
  have hCK : (P.Cm g).map Complex.ofReal * (P.Km g).map Complex.ofReal =
      P.Dm.map Complex.ofReal := by
    have e : ∀ M : Matrix (Fin 4) (Fin 4) ℝ, M.map Complex.ofReal = Complex.ofRealHom.mapMatrix M :=
      fun M => rfl
    rw [e, e, e, ← map_mul, Km, Matrix.mul_nonsing_inv_cancel_left _ _ hCu]
  have hprod : (P.Cm g).map Complex.ofReal * (Matrix.scalar (Fin 4) w - (P.Km g).map
      Complex.ofReal) = w • ((P.Cm g).map Complex.ofReal - w⁻¹ • P.Dm.map Complex.ofReal) := by
    rw [Matrix.mul_sub, hCK, smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul,
      Matrix.scalar_apply]
    congr 1
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hw, mul_zero, Matrix.det_smul, det_Cm_sub hg hq] at hdet
  have hr : P.rr μ w⁻¹ = 0 := by
    have : (w ^ Fintype.card (Fin 4)) * (-P.rr μ w⁻¹) = 0 := hdet.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by simp) |>.mp h) hw0
    · exact neg_eq_zero.mp h
  by_contra hge
  have hle : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.mp hge)
  exact rr_ne_zero hq hd huniq hle hr

end Par

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (24), p. 173: `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` solves
`A₀ʷ x_t = A₁ʷ E_t x_{t+1} + B₀ʷ u_t` with initial real wage gap `ω̃_{−1}`; all variables are
adapted and `ω̃_t` (the last entry of `x_{t+1}`) is predetermined, i.e. known at `t`. -/
def IsSol (P : Par) (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : Prop :=
  (∀ t, rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t)) ∧
    x 0 3 = ω0 ∧ Fwd.VAdapted 𝔼 x ∧ ∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3

/-- Galí (2015), p. 174: the equilibrium is determinate when, for every bounded adapted forcing
`u` and every bounded initial real wage gap `ω̃_{−1}` known at date `0`, system (24) has exactly
one bounded solution. -/
def Determinate (P : Par) : Prop :=
  ∀ (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ), Fwd.VBounded u → Fwd.VAdapted 𝔼 u →
    (∃ M, ∀ ω, |ω0 ω| ≤ M) → 𝔼.E 0 ω0 = ω0 → ∃! x, IsSol 𝔼 P u ω0 x ∧ Fwd.VBounded x

/-- Galí (2015), p. 174: Quasi-differencing by the stable mode: `ẑ_t = (ỹ, π^p, π^w)_t − g
ω̃_{t−1}` and
`n_t = ω̃_t − μ ω̃_{t−1}`. -/
def toS (μ : ℝ) (g : Fin 3 → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![x t 0 - g 0 • x t 3, x t 1 - g 1 • x t 3, x t 2 - g 2 • x t 3,
    x (t + 1) 3 - μ • x t 3]

/-- Galí (2015), p. 174: The key identity: `C s_t − D E_t s_{t+1} = A₀ʷ x_t − A₁ʷ E_t x_{t+1}`. -/
theorem transform {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (x : ℕ → Fin 4 → Ω → ℝ) (t : ℕ) (hpre : 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) :
    rvMul (P.Cm g) (toS μ g x t) - rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) =
      rvMul P.A0 (x t) - rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) := by
  obtain ⟨e1, e2, e3, e4⟩ := hg
  funext i ω
  fin_cases i <;>
    simp [rvMul_apply, Fin.sum_univ_four, Par.Cm, Par.Dm, Par.A0, Par.A1, toS, map_sub,
      map_smul, hpre]
  · linear_combination (-x t 3 ω) * e1
  · linear_combination (-x t 3 ω) * e2
  · linear_combination (-x t 3 ω) * e3
  · linear_combination (-x t 3 ω) * e4

/-- Galí (2015), p. 174: Equation (24) at date `t` is equivalent to the quasi-differenced forward
system
`s_t = K E_t s_{t+1} + F u_t`. -/
theorem eq_iff_fwd {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hCu : IsUnit (P.Cm g).det) (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (t : ℕ)
    (hpre : 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) :
    rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t) ↔
      toS μ g x t = rvMul (P.Km g) (fun j => 𝔼.E t (toS μ g x (t + 1) j))
        + rvMul (P.Fm g) (u t) := by
  have htr := transform 𝔼 hg x t hpre
  constructor
  · intro h
    have hC : rvMul (P.Cm g) (toS μ g x t) =
        rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) + rvMul B0 (u t) := by
      rw [← sub_eq_iff_eq_add', htr, h]; abel
    calc toS μ g x t = rvMul ((P.Cm g)⁻¹ * P.Cm g) (toS μ g x t) := by
          rw [Matrix.nonsing_inv_mul _ hCu, rvMul_one]
      _ = _ := by
          rw [← rvMul_rvMul, hC, rvMul_add, rvMul_rvMul, rvMul_rvMul]; rfl
  · intro h
    have hC : rvMul (P.Cm g) (toS μ g x t) =
        rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) + rvMul B0 (u t) := by
      rw [h, rvMul_add, rvMul_rvMul, rvMul_rvMul, Par.Km, Par.Fm,
        Matrix.mul_nonsing_inv_cancel_left _ _ hCu, Matrix.mul_nonsing_inv_cancel_left _ _ hCu]
    rw [← sub_eq_iff_eq_add', ← htr, hC]; abel

/-- Galí (2015), p. 174: The quasi-differenced process of a solution is adapted. -/
theorem toS_adapted {μ : ℝ} {g : Fin 3 → ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hax : Fwd.VAdapted 𝔼 x)
    (hpre : ∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) : Fwd.VAdapted 𝔼 (toS μ g x) := by
  intro t i
  fin_cases i <;> simp [toS, map_sub, map_smul, hax t, hpre t]

/-- Galí (2015), p. 174: The quasi-differenced process of a bounded process is bounded. -/
theorem toS_bounded {μ : ℝ} {g : Fin 3 → ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hbx : Fwd.VBounded x) :
    Fwd.VBounded (toS μ g x) := by
  obtain ⟨M, hM⟩ := hbx
  refine ⟨M * (1 + |g 0| + |g 1| + |g 2| + |μ|), fun t i ω => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t 0 ω)
  have hb : ∀ (a : ℝ) (j : Fin 4) (s : ℕ), |x s j ω - a * x t 3 ω| ≤ M * (1 + |a|) := by
    intro a j s
    calc |x s j ω - a * x t 3 ω| ≤ |x s j ω| + |a| * |x t 3 ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ M + |a| * M := add_le_add (hM s j ω) (mul_le_mul_of_nonneg_left (hM t 3 ω)
          (abs_nonneg a))
      _ = M * (1 + |a|) := by ring
  have hg0 := abs_nonneg (g 0)
  have hg1 := abs_nonneg (g 1)
  have hg2 := abs_nonneg (g 2)
  have hμ := abs_nonneg μ
  fin_cases i <;> simp only [toS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · exact (hb (g 0) 0 t).trans (by nlinarith)
  · exact (hb (g 1) 1 t).trans (by nlinarith)
  · exact (hb (g 2) 2 t).trans (by nlinarith)
  · exact (hb μ 3 (t + 1)).trans (by nlinarith)

/-- Galí (2015), p. 174: The predetermined real wage gap rebuilt from `ω̃_{−1}` and the
innovations `n_t`:
`ω̃_t = μ ω̃_{t−1} + n_t`. -/
def mseq (μ : ℝ) (ω0 : Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ω0
  | t + 1 => μ • mseq μ ω0 s t + s t 3

/-- Galí (2015), p. 174: The solution rebuilt from the quasi-differenced variables. -/
def ofS (g : Fin 3 → ℝ) (m : ℕ → Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![s t 0 + g 0 • m t, s t 1 + g 1 • m t, s t 2 + g 2 • m t, m t]

/-- Galí (2015), p. 174 (existence): quasi-differencing the rebuilt solution returns `s`. -/
theorem toS_ofS (μ : ℝ) (g : Fin 3 → ℝ) (ω0 : Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) :
    toS μ g (ofS g (mseq μ ω0 s) s) = s := by
  funext t i
  fin_cases i <;> simp [toS, ofS, mseq]

/-- Galí (2015), p. 174 (existence): the rebuilt real wage gap is adapted. -/
theorem mseq_adapted {μ : ℝ} {ω0 : Ω → ℝ} {s : ℕ → Fin 4 → Ω → ℝ} (hω0 : 𝔼.E 0 ω0 = ω0)
    (has : Fwd.VAdapted 𝔼 s) (t : ℕ) : 𝔼.E t (mseq μ ω0 s t) = mseq μ ω0 s t := by
  induction t with
  | zero => exact hω0
  | succ t ih =>
    have h1 : 𝔼.E t (mseq μ ω0 s (t + 1)) = mseq μ ω0 s (t + 1) := by
      simp only [mseq, map_add, map_smul, ih, has t 3]
    rw [← h1, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), p. 174 (existence): the rebuilt real wage gap is bounded (`0 ≤ μ < 1`). -/
theorem mseq_bounded {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {ω0 : Ω → ℝ} {M0 : ℝ}
    (hω : ∀ ω, |ω0 ω| ≤ M0) {s : ℕ → Fin 4 → Ω → ℝ} {Ms : ℝ}
    (hs : ∀ t i ω, |s t i ω| ≤ Ms) (t : ℕ) (ω : Ω) :
    |mseq μ ω0 s t ω| ≤ max M0 (Ms / (1 - μ)) := by
  induction t with
  | zero => exact (hω ω).trans (le_max_left _ _)
  | succ t ih =>
    simp only [mseq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1μ : 0 < 1 - μ := by linarith
    have hMs : Ms ≤ (1 - μ) * max M0 (Ms / (1 - μ)) := by
      have := le_max_right M0 (Ms / (1 - μ))
      rw [div_le_iff₀ h1μ] at this
      linarith
    calc |μ * mseq μ ω0 s t ω + s t 3 ω| ≤ μ * |mseq μ ω0 s t ω| + |s t 3 ω| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hμ0]
      _ ≤ μ * max M0 (Ms / (1 - μ)) + Ms :=
          add_le_add (mul_le_mul_of_nonneg_left ih hμ0) (hs t 3 ω)
      _ ≤ max M0 (Ms / (1 - μ)) := by linarith

/-- **Galí (2015), p. 174, sufficiency**: under the sign conditions, if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1` (equivalently `q(1) > 0`), system (24) has
exactly one bounded solution for every bounded adapted forcing and every bounded initial real
wage gap. -/
theorem determinate_of_pos {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    Determinate 𝔼 P := by
  obtain ⟨μ, hμ0, hμ1, hq, hd, huniq⟩ := P.stable_root hP hΨ h1
  obtain ⟨g, hg⟩ := P.exists_stableVec hP hμ0 hμ1 hq hd huniq
  have hCu : IsUnit (P.Cm g).det := isUnit_iff_ne_zero.mpr (P.det_Cm_ne_zero hg hq hd huniq)
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound (P.Km g) (P.Km_eigen hg hq hd huniq)
  intro u ω0 hbu hau hbω hω0
  obtain ⟨Mu, hMu⟩ := hbu
  obtain ⟨M0, hM0⟩ := hbω
  set w : ℕ → Fin 4 → Ω → ℝ := fun t => rvMul (P.Fm g) (u t) with hw_def
  have hwb : ∀ t i ω, |w t i ω| ≤ ∑ k, |P.Fm g i k| * Mu := by
    intro t i ω
    simp only [hw_def]
    rw [rvMul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMu t k ω) (abs_nonneg _)
  set Mw : ℝ := ∑ i, ∑ k, |P.Fm g i k| * Mu with hMw
  have hwb' : ∀ t i ω, |w t i ω| ≤ Mw := by
    intro t i ω
    refine (hwb t i ω).trans ?_
    have hMu0 : 0 ≤ Mu := (abs_nonneg _).trans (hMu t 0 ω)
    exact Finset.single_le_sum (f := fun i => ∑ k, |P.Fm g i k| * Mu)
      (fun i _ => Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) hMu0)
      (Finset.mem_univ i)
  have haw : Fwd.VAdapted 𝔼 w := by
    intro t i
    rw [hw_def]
    simp only [Fwd.E_rvMul 𝔼, hau t]
  obtain ⟨s, hs, has, ⟨Ms, hMs⟩⟩ := Fwd.fsolves_exists 𝔼 hρ0.le hρ1 hK hwb' haw
  set m := mseq μ ω0 s with hm
  have ham : ∀ t, 𝔼.E t (m t) = m t := mseq_adapted 𝔼 hω0 has
  have hpre : ∀ t, 𝔼.E t (ofS g m s (t + 1) 3) = ofS g m s (t + 1) 3 := by
    intro t
    simp only [ofS, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, hm, mseq,
      map_add, map_smul, mseq_adapted 𝔼 hω0 has t, has t 3]
  refine ⟨ofS g m s, ⟨⟨fun t => ?_, ?_, ?_, hpre⟩, ?_⟩, ?_⟩
  · rw [eq_iff_fwd 𝔼 hg hCu _ u t (hpre t), toS_ofS]
    exact hs t
  · simp [ofS, hm, mseq]
  · intro t i
    fin_cases i <;> simp [ofS, map_add, map_smul, has t, ham t]
  · have hmb := mseq_bounded hμ0.le hμ1 hM0 hMs
    set Mm := max M0 (Ms / (1 - μ))
    refine ⟨Ms + (|g 0| + |g 1| + |g 2| + 1) * Mm, fun t i ω => ?_⟩
    have hmt := hmb t ω
    have hMm : 0 ≤ Mm := (abs_nonneg _).trans hmt
    have hg0 := abs_nonneg (g 0)
    have hg1 := abs_nonneg (g 1)
    have hg2 := abs_nonneg (g 2)
    have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs t 0 ω)
    have hb : ∀ (a : ℝ) (j : Fin 4), |s t j ω + a * m t ω| ≤ Ms + |a| * Mm := by
      intro a j
      refine (abs_add_le _ _).trans (add_le_add (hMs t j ω) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hmt (abs_nonneg a)
    fin_cases i <;> simp only [ofS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · exact (hb (g 0) 0).trans (by nlinarith)
    · exact (hb (g 1) 1).trans (by nlinarith)
    · exact (hb (g 2) 2).trans (by nlinarith)
    · exact hmt.trans (by nlinarith)
  · rintro y ⟨⟨hy, hy0, hay, hpy⟩, hby⟩
    have hsy : Fwd.FSolves 𝔼 (P.Km g) w (toS μ g y) := fun t =>
      (eq_iff_fwd 𝔼 hg hCu y u t (hpy t)).mp (hy t)
    have heq : toS μ g y = s := Fwd.fsolves_unique 𝔼 hρ0.le hρ1 hK hsy hs
      (toS_adapted 𝔼 hay hpy) has (toS_bounded hby) ⟨Ms, hMs⟩
    have h3 : ∀ t, y t 3 = m t := by
      intro t
      induction t with
      | zero => rw [hy0, hm, mseq]
      | succ t ih =>
        have := congrFun (congrFun heq t) 3
        simp only [toS, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
        rw [hm, mseq, ← hm, ← this, ih]
        abel
    funext t i
    have hc := congrFun (congrFun heq t) i
    fin_cases i <;> simp only [toS, ofS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val] at hc ⊢
    · rw [← hc, h3 t]; abel
    · rw [← hc, h3 t]; abel
    · rw [← hc, h3 t]; abel
    · exact h3 t

end Dyn

namespace Par

/-- Galí (2015), eq. (24): `det A₀ʷ = −q(0) > 0`. -/
theorem det_A0 (P : Par) : P.A0.det = -P.c0 := by
  have h := P.det_A0_sub_A1_real 0
  rw [zero_smul, sub_zero, qr_zero] at h
  exact h

/-- Galí (2015), eq. (24): `det A₁ʷ = σ β²`. -/
theorem det_A1 (P : Par) : P.A1.det = P.σ * P.β ^ 2 := by
  rw [show P.σ * P.β ^ 2 = P.σ * (P.β * (P.β * 1)) by ring]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A1]

/-- Galí (2015), p. 174: the derivative of `q` in coefficient form. -/
theorem eval_derivative_qC (P : Par) (z : ℂ) :
    P.qC.derivative.eval z = P.c1 + 2 * P.c2 * z + 3 * P.c3 * z ^ 2 + 4 * P.c4 * z ^ 3 := by
  simp [qC, qv, eval_derivative_quart]

end Par

namespace Dyn

open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 174 (tool): a row combination `ℓᵀ M a = (ℓᵀ M) a`. -/
theorem sum_smul_rvMul {n m : ℕ} (ℓ : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin m → Ω → ℝ) : ∑ i, ℓ i • rvMul M a i = ∑ j, (ℓ ᵥ* M) j • a j := by
  simp only [rvMul, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Galí (2015), p. 174 (tool): the action on deterministic vectors. -/
theorem rvMul_const {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → ℝ) :
    rvMul M (fun j (_ : Ω) => a j) = fun i _ => (M *ᵥ a) i := by
  funext i ω
  simp [rvMul_apply, Matrix.mulVec, dotProduct]

/-- Galí (2015), p. 174 (multiplicity): a nonzero bounded deterministic solution of the
homogeneous system with `ω̃_{−1} = 0` gives two different bounded solutions of (24) for
`u = 0`, `ω̃_{−1} = 0`. -/
theorem multiple_solutions_of_mode [Nonempty Ω] {P : Par} {X : ℕ → Fin 4 → ℝ}
    (hX : ∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) (h0 : X 0 3 = 0)
    (hb : ∃ M, ∀ t j, |X t j| ≤ M) (hne : X ≠ 0) :
    IsSol 𝔼 P 0 0 0 ∧ Fwd.VBounded (0 : ℕ → Fin 4 → Ω → ℝ) ∧
      IsSol 𝔼 P 0 0 (fun t j _ => X t j) ∧ Fwd.VBounded (fun t j (_ : Ω) => X t j) ∧
      (fun t j (_ : Ω) => X t j) ≠ 0 := by
  have hz : IsSol 𝔼 P 0 0 0 := by
    refine ⟨fun t => ?_, rfl, fun t i => by simp, fun t => by simp⟩
    funext i ω
    simp [rvMul_apply]
  have hc : IsSol 𝔼 P 0 0 (fun t j _ => X t j) := by
    refine ⟨fun t => ?_, ?_, fun t i => 𝔼.const t _, fun t => 𝔼.const t _⟩
    · have hE : (fun j => 𝔼.E t (fun _ : Ω => X (t + 1) j)) = fun j _ => X (t + 1) j :=
        funext fun j => 𝔼.const t _
      rw [hE, Pi.zero_apply, rvMul_zero, add_zero, rvMul_const, rvMul_const, hX t]
    · funext ω; simp [h0]
  obtain ⟨M, hM⟩ := hb
  refine ⟨hz, ⟨0, by simp⟩, hc, ⟨M, fun t j _ => hM t j⟩, fun h => hne ?_⟩
  funext t j
  have := congrFun (congrFun (congrFun h t) j) (Classical.arbitrary Ω)
  simpa using this

/-- Galí (2015), p. 174 (indeterminacy): such a mode rules out determinacy. -/
theorem not_determinate_of_mode [Nonempty Ω] {P : Par} {X : ℕ → Fin 4 → ℝ}
    (hX : ∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) (h0 : X 0 3 = 0)
    (hb : ∃ M, ∀ t j, |X t j| ≤ M) (hne : X ≠ 0) : ¬ Determinate 𝔼 P := by
  intro hdet
  obtain ⟨x, -, huniq⟩ := hdet 0 0 ⟨0, by simp⟩ (by intro t i; simp) ⟨0, by simp⟩ (by simp)
  obtain ⟨hz, hzb, hc, hcb, hne'⟩ := multiple_solutions_of_mode 𝔼 hX h0 hb hne
  exact hne' ((huniq _ ⟨hc, hcb⟩).trans (huniq 0 ⟨hz, hzb⟩).symm)

/-- **Galí (2015), p. 174, the boundary**: if `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) = 1`
(`q(1) = 0`, a unit eigenvalue) the equilibrium is not determinate: for a suitable constant
forcing there is no bounded solution. -/
theorem not_determinate_of_eq [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 = 0) :
    ¬ Determinate 𝔼 P := by
  obtain ⟨hb0, hb1, -⟩ := hP
  have hdet : (P.A0 - (1 : ℝ) • P.A1).det = 0 := by rw [P.det_A0_sub_A1_real, h1, neg_zero]
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hℓA : ℓ ᵥ* P.A0 = ℓ ᵥ* P.A1 := by
    rw [one_smul, Matrix.vecMul_sub, sub_eq_zero] at hℓ; exact hℓ
  have hcol : ∀ j, (ℓ ᵥ* P.A0) j = (ℓ ᵥ* P.A1) j := fun j => congrFun hℓA j
  have h03 : ℓ 0 ^ 2 + ℓ 3 ^ 2 ≠ 0 := by
    intro hN
    have h0 : ℓ 0 = 0 := by nlinarith [sq_nonneg (ℓ 0), sq_nonneg (ℓ 3)]
    have h3 : ℓ 3 = 0 := by nlinarith [sq_nonneg (ℓ 0), sq_nonneg (ℓ 3)]
    have c1 := hcol 1
    have c2 := hcol 2
    simp only [Matrix.vecMul, dotProduct, Par.A0, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.sum_univ_four, h0,
      zero_mul, mul_one, zero_add, Matrix.cons_val, mul_zero, add_zero, h3, mul_neg, neg_zero,
      Par.A1] at c1 c2
    have h1' : ℓ 1 = 0 := by
      have : ℓ 1 * (1 - P.β) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    have h2' : ℓ 2 = 0 := by
      have : ℓ 2 * (1 - P.β) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    apply hℓ0
    funext j
    fin_cases j <;> simp [h0, h3, h1', h2']
  set N := ℓ 0 ^ 2 + ℓ 3 ^ 2 with hN
  set u : ℕ → Fin 2 → Ω → ℝ := fun _ => ![fun _ => ℓ 0 / N, fun _ => ℓ 3 / N] with hu
  intro hdetm
  obtain ⟨x, ⟨⟨hx, -, hax, -⟩, ⟨Mx, hMx⟩⟩, -⟩ := hdetm u 0
    ⟨|ℓ 0 / N| + |ℓ 3 / N|, fun t i ω => by
      fin_cases i <;> simp [hu]⟩
    (fun t i => by fin_cases i <;> simp [hu, 𝔼.const]) ⟨0, by simp⟩ (by simp)
  set S : ℕ → Ω → ℝ := fun t => ∑ i, ℓ i • rvMul P.A1 (x t) i with hS
  have hSrec : ∀ t, S t = 𝔼.E t (S (t + 1)) + fun _ => 1 := by
    intro t
    have h := congrArg (fun v => ∑ i, ℓ i • v i) (hx t)
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib] at h
    rw [sum_smul_rvMul, hℓA, ← sum_smul_rvMul] at h
    have hB : ∑ i, ℓ i • rvMul B0 (u t) i = fun _ => 1 := by
      funext ω
      simp [rvMul_apply, Fin.sum_univ_four, Fin.sum_univ_two, B0, hu, Finset.sum_apply]
      field_simp
      linear_combination -hN
    rw [hB] at h
    change ∑ i, ℓ i • rvMul P.A1 (x t) i =
      𝔼.E t (∑ i, ℓ i • rvMul P.A1 (x (t + 1)) i) + fun _ => 1
    rw [h]
    congr 1
    simp only [map_sum, map_smul, Fwd.E_rvMul 𝔼]
  have hS0 : 𝔼.E 0 (S 0) = S 0 := by
    simp only [hS, map_sum, map_smul, Fwd.E_rvMul 𝔼, hax 0]
  have hE0 : ∀ t, 𝔼.E 0 (S t) = S 0 - fun _ => (t : ℝ) := by
    intro t
    induction t with
    | zero => rw [hS0]; funext ω; simp
    | succ t ih =>
      have h := congrArg (𝔼.E 0) (hSrec t)
      rw [map_add, 𝔼.tower (Nat.zero_le t), 𝔼.const] at h
      rw [ih] at h
      funext ω
      have := congrFun h ω
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      push_cast
      linarith
  set MS : ℝ := ∑ i, |ℓ i| * ∑ j, |P.A1 i j| * Mx with hMS
  have hSb : ∀ t ω, |S t ω| ≤ MS := by
    intro t ω
    simp only [hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rvMul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMx t j ω) (abs_nonneg _)
  obtain ⟨T, hT⟩ := exists_nat_gt (|S 0 (Classical.arbitrary Ω)| + MS)
  have h1' := 𝔼.abs_E_le (hSb T) 0 (Classical.arbitrary Ω)
  rw [hE0 T] at h1'
  simp only [Pi.sub_apply] at h1'
  have := abs_sub_abs_le_abs_sub (T : ℝ) (S 0 (Classical.arbitrary Ω))
  rw [abs_sub_comm] at h1'
  rw [abs_of_nonneg (Nat.cast_nonneg T)] at this
  linarith

/-- Galí (2015), p. 174 (tool): complexification of a real matrix as a ring map. -/
theorem map_ofReal_eq (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.map Complex.ofReal = Complex.ofRealHom.mapMatrix M := rfl

/-- Galí (2015), p. 174: if `q` has no root in the closed unit disc (all four eigenvalues of
`(A₀ʷ)⁻¹ A₁ʷ` inside the unit circle) there is no bounded solution with `u = 0` and
`ω̃_{−1} = 1` (non-existence). -/
theorem no_bounded_solution_of_no_root [Nonempty Ω] {P : Par} (hP : P.Adm)
    (hno : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0) (x : ℕ → Fin 4 → Ω → ℝ)
    (hsol : IsSol 𝔼 P 0 (fun _ => 1) x) (hbx : Fwd.VBounded x) : False := by
  obtain ⟨hx, hx0, hax, -⟩ := hsol
  have hA0u : IsUnit P.A0.det := by
    rw [P.det_A0]; exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (P.c0_neg hP).ne)
  have hfs : Fwd.FSolves 𝔼 (P.A0⁻¹ * P.A1) 0 x := by
    intro t
    have h := hx t
    rw [Pi.zero_apply, rvMul_zero, add_zero] at h
    rw [Pi.zero_apply, add_zero, ← rvMul_rvMul, ← h, rvMul_rvMul,
      Matrix.nonsing_inv_mul _ hA0u, rvMul_one]
  have heig : ∀ w : ℂ, (Matrix.scalar (Fin 4) w - (P.A0⁻¹ * P.A1).map Complex.ofReal).det = 0 →
      ‖w‖ < 1 := by
    intro w hw
    have hAA : P.A0.map Complex.ofReal * (P.A0⁻¹ * P.A1).map Complex.ofReal =
        P.A1.map Complex.ofReal := by
      rw [map_ofReal_eq, map_ofReal_eq, map_ofReal_eq, ← map_mul,
        Matrix.mul_nonsing_inv_cancel_left _ _ hA0u]
    have hprod : P.A0.map Complex.ofReal * (Matrix.scalar (Fin 4) w -
        (P.A0⁻¹ * P.A1).map Complex.ofReal) =
        w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal := by
      rw [Matrix.mul_sub, hAA, Matrix.scalar_apply]
      congr 1
      ext i j
      simp [Matrix.mul_diagonal, mul_comm]
    have hdet0 := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hw, mul_zero] at hdet0
    have hA1c : (P.A1.map Complex.ofReal).det = ((P.σ * P.β ^ 2 : ℝ) : ℂ) := by
      rw [map_ofReal_eq, ← RingHom.map_det, P.det_A1]; rfl
    by_cases hw0 : w = 0
    · exfalso
      rw [hw0, zero_smul, zero_sub, Matrix.det_neg, hA1c] at hdet0
      obtain ⟨hb0, -, hs, -⟩ := hP
      simp only [Fintype.card_fin, ofReal_mul, ofReal_pow, zero_eq_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, neg_eq_zero, one_ne_zero,
        mul_eq_zero, ofReal_eq_zero, false_or] at hdet0
      rcases hdet0 with h | h
      · exact hs.ne' h
      · exact hb0.ne' h
    have hsplit : w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal =
        w • (P.A0.map Complex.ofReal - w⁻¹ • P.A1.map Complex.ofReal) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul]
    rw [hsplit, Matrix.det_smul, P.det_A0_sub_A1] at hdet0
    have hq : P.qC.eval w⁻¹ = 0 := by
      rcases mul_eq_zero.mp hdet0.symm with h | h
      · exact absurd (pow_eq_zero_iff (by simp) |>.mp h) hw0
      · exact neg_eq_zero.mp h
    by_contra hge
    exact hno w⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.mp hge)) hq
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound _ heig
  have hz : Fwd.FSolves 𝔼 (P.A0⁻¹ * P.A1) 0 0 := by
    intro t; funext i ω; simp [rvMul_apply]
  have h := Fwd.fsolves_unique 𝔼 hρ0.le hρ1 hK hfs hz hax (by intro t i; simp) hbx ⟨0, by simp⟩
  have h03 := congrFun (congrFun (congrFun h 0) 3) (Classical.arbitrary Ω)
  rw [hx0] at h03
  simp at h03

/-- Galí (2015), p. 174: no root of `q` in the closed unit disc rules out determinacy. -/
theorem not_determinate_of_no_root [Nonempty Ω] {P : Par} (hP : P.Adm)
    (hno : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0) : ¬ Determinate 𝔼 P := by
  intro hdet
  obtain ⟨x, ⟨hsol, hbx⟩, -⟩ := hdet 0 (fun _ => 1) ⟨0, by simp⟩
    (by intro t i; simp) ⟨1, by simp⟩ (𝔼.const 0 1)
  exact no_bounded_solution_of_no_root 𝔼 hP hno x hsol hbx

/-- Galí (2015), p. 174: The roots of `q` in the closed unit disc, with multiplicity. -/
noncomputable def closedRoots (P : Par) : Multiset ℂ := P.qC.roots.filter (fun z => ‖z‖ ≤ 1)

/-- Galí (2015), p. 174: `q ≠ 0`. -/
theorem qC_ne_zero {P : Par} (hP : P.Adm) : P.qC ≠ 0 :=
  quart_ne_zero (by simp only [Par.qv, Matrix.cons_val]; exact_mod_cast (P.c4_neg hP).ne)

/-- Galí (2015), p. 174: membership in the roots of `q` in the closed unit disc. -/
theorem mem_closedRoots {P : Par} (hP : P.Adm) {ζ : ℂ} :
    ζ ∈ closedRoots P ↔ ‖ζ‖ ≤ 1 ∧ P.qC.eval ζ = 0 := by
  rw [closedRoots, Multiset.mem_filter, mem_roots (qC_ne_zero hP), IsRoot]
  exact and_comm

/-- Galí (2015), p. 174: The real synthetic-division cubic `s(t) = q(t)/(t − r)`. -/
def sr (P : Par) (r t : ℝ) : ℝ :=
  P.c4 * t ^ 3 + (P.c3 + r * P.c4) * t ^ 2 + (P.c2 + r * (P.c3 + r * P.c4)) * t
    + (P.c1 + r * (P.c2 + r * (P.c3 + r * P.c4)))

/-- Galí (2015), p. 174: synthetic division `q(t) = (t − r) s(t) + q(r)`. -/
theorem qr_eq_sr (P : Par) (r t : ℝ) : P.qr t = (t - r) * sr P r t + P.qr r := by
  simp only [Par.qr, sr]; ring

/-- Galí (2015), p. 174: `s(r) = q′(r)`. -/
theorem sr_self (P : Par) (r : ℝ) : sr P r r = P.dqr r := by
  simp only [sr, Par.dqr]; ring

/-- Galí (2015), p. 174: when `q(1) < 0`, the number of roots of `q` in the closed unit disc
cannot be one (it is even: complex roots pair up, and `q(−1) < 0`, `q(1) < 0` force an even
number of real roots in `(−1, 1)`). -/
theorem closedRoots_card_ne_one {P : Par} (hP : P.Adm) (h1 : P.qr 1 < 0) :
    (closedRoots P).card ≠ 1 := by
  intro hc
  obtain ⟨ζ0, hζ0⟩ := Multiset.card_eq_one.mp hc
  have huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = ζ0 := by
    intro ζ hζ h0
    have := (mem_closedRoots hP).mpr ⟨hζ, h0⟩
    rwa [hζ0, Multiset.mem_singleton] at this
  have hmem : ζ0 ∈ closedRoots P := by rw [hζ0]; exact Multiset.mem_singleton_self _
  obtain ⟨hn0, hq0⟩ := (mem_closedRoots hP).mp hmem
  -- `ζ0` is real
  have hconj : (starRingEnd ℂ) ζ0 = ζ0 := huniq _ (by rwa [Complex.norm_conj])
    (by rw [Par.eval_qC_conj, hq0, map_zero])
  set r := ζ0.re with hr
  have hζr : ζ0 = (r : ℂ) := (Complex.conj_eq_iff_re.mp hconj).symm
  have hqr : P.qr r = 0 := by
    have := hq0; rw [hζr, Par.eval_qC_ofReal] at this; exact_mod_cast this
  have hrn : |r| ≤ 1 := by
    have := hn0; rwa [hζr, Complex.norm_real, Real.norm_eq_abs] at this
  -- `r` is a simple root
  have hdr : P.dqr r ≠ 0 := by
    intro hd
    have hroot : P.qC.IsRoot ζ0 := hq0
    have hder : P.qC.derivative.IsRoot ζ0 := by
      rw [IsRoot, P.eval_derivative_qC, hζr]
      have : (P.dqr r : ℂ) = 0 := by rw [hd, Complex.ofReal_zero]
      simp only [Par.dqr] at this
      push_cast at this
      exact this
    have hm := (one_lt_rootMultiplicity_iff_isRoot (qC_ne_zero hP)).mpr ⟨hroot, hder⟩
    have hcnt : 2 ≤ (closedRoots P).count ζ0 := by
      rw [closedRoots, Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ ≤ 1) hn0,
        count_roots]
      omega
    have := Multiset.count_le_card ζ0 (closedRoots P)
    omega
  have hr1 : r ≠ 1 := fun h => by rw [h] at hqr; linarith
  have hrm1 : r ≠ -1 := fun h => by rw [h] at hqr; linarith [P.qr_neg_one_neg hP]
  have hrlt : -1 < r ∧ r < 1 := by
    rw [abs_le] at hrn
    exact ⟨lt_of_le_of_ne hrn.1 (Ne.symm hrm1), lt_of_le_of_ne hrn.2 hr1⟩
  -- the cofactor `s` has no zero on `[−1, 1]`
  have hs : ∀ t ∈ Set.Icc (-1 : ℝ) 1, sr P r t ≠ 0 := by
    intro t ht h0
    by_cases htr : t = r
    · rw [htr, sr_self] at h0; exact hdr h0
    · have hqt : P.qr t = 0 := by rw [qr_eq_sr P r t, h0, hqr]; ring
      have := huniq t (by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ht)
        (by rw [Par.eval_qC_ofReal, hqt, Complex.ofReal_zero])
      rw [hζr] at this
      exact htr (by exact_mod_cast this)
  have hscont : Continuous (sr P r) := by unfold sr; fun_prop
  have hsgn : 0 < sr P r (-1) * sr P r 1 := by
    by_contra hle
    rw [not_lt] at hle
    rcases le_total (sr P r (-1)) 0 with ha | ha
    · have hb : 0 ≤ sr P r 1 := by
        by_contra hb; rw [not_le] at hb
        have := mul_pos_of_neg_of_neg (lt_of_le_of_ne ha (hs (-1) ⟨le_rfl, by norm_num⟩)) hb
        linarith
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
        hscont.continuousOn (show (0 : ℝ) ∈ Set.Icc (sr P r (-1)) (sr P r 1) from ⟨ha, hb⟩)
      exact hs t ht ht0
    · have hb : sr P r 1 ≤ 0 := by
        by_contra hb; rw [not_le] at hb
        have := mul_pos (lt_of_le_of_ne ha (Ne.symm (hs (-1) ⟨le_rfl, by norm_num⟩))) hb
        linarith
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' (show (-1 : ℝ) ≤ 1 by norm_num)
        hscont.continuousOn (show (0 : ℝ) ∈ Set.Icc (sr P r 1) (sr P r (-1)) from ⟨hb, ha⟩)
      exact hs t ht ht0
  have hprod : P.qr 1 * P.qr (-1) = -((1 - r) * (1 + r)) * (sr P r (-1) * sr P r 1) := by
    rw [qr_eq_sr P r 1, qr_eq_sr P r (-1), hqr]; ring
  have hpos : 0 < (1 - r) * (1 + r) := mul_pos (by linarith) (by linarith)
  have hneg := mul_pos_of_neg_of_neg h1 (P.qr_neg_one_neg hP)
  nlinarith

/-- Galí (2015), p. 174: A real root of `q` gives a real eigenvector: `A₀ʷ V = r A₁ʷ V`. -/
theorem exists_real_eigvec {P : Par} {r : ℝ} (hq : P.qr r = 0) :
    ∃ V : Fin 4 → ℝ, V ≠ 0 ∧ P.A0 *ᵥ V = r • (P.A1 *ᵥ V) := by
  have hdet : (P.A0 - r • P.A1).det = 0 := by rw [P.det_A0_sub_A1_real, hq, neg_zero]
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨V, hV0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hV
  exact hV

/-- Galí (2015), p. 174: The geometric mode `X_t = rᵗ V`. -/
theorem geom_mode {P : Par} {r : ℝ} {V : Fin 4 → ℝ} (hV : P.A0 *ᵥ V = r • (P.A1 *ᵥ V))
    (t : ℕ) : P.A0 *ᵥ (r ^ t • V) = P.A1 *ᵥ (r ^ (t + 1) • V) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hV, smul_smul, pow_succ]

/-- Galí (2015), p. 174 (tool): powers of a number in `[−1, 1]` stay in `[−1, 1]`. -/
theorem abs_pow_le_one {r : ℝ} (hr : |r| ≤ 1) (t : ℕ) : |r ^ t| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg r) hr

/-- Galí (2015), p. 174 (indeterminacy, complex roots): a non-real root of `q` in the closed
unit disc gives a nonzero bounded oscillating solution with `ω̃_{−1} = 0`. -/
theorem not_determinate_of_complex_root [Nonempty Ω] {P : Par} {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (hq : P.qC.eval ζ = 0) (him : ζ.im ≠ 0) : ¬ Determinate 𝔼 P := by
  have hdet : (P.A0.map Complex.ofReal - ζ • P.A1.map Complex.ofReal).det = 0 := by
    rw [P.det_A0_sub_A1, hq, neg_zero]
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hV
  set c : ℂ := if V 3 = 0 then 1 else Complex.I * (starRingEnd ℂ) (V 3) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; split_ifs with h
    · exact one_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero ((_root_.map_ne_zero _).mpr h)
  have hc3 : (c * V 3).re = 0 := by
    rw [hc]; split_ifs with h
    · simp [h]
    · rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
      ring
  have key : ∀ (M : Matrix (Fin 4) (Fin 4) ℝ) (a : ℂ) (i : Fin 4),
      (M *ᵥ fun j => (a * V j).re) i = (a * ((M.map Complex.ofReal) *ᵥ V) i).re := by
    intro M a i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a * (↑(M i j) * V j) = ↑(M i j) * (a * V j) by ring, Complex.re_ofReal_mul]
  refine not_determinate_of_mode 𝔼 (X := fun t j => (c * ζ ^ t * V j).re) (fun t => ?_) ?_ ?_ ?_
  · funext i
    rw [key, key, hV, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · simpa using hc3
  · refine ⟨‖c‖ * ∑ j, ‖V j‖, fun t j => ?_⟩
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖ζ‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg _) hζ
    have h2 : ‖V j‖ ≤ ∑ j, ‖V j‖ :=
      Finset.single_le_sum (f := fun j => ‖V j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    calc ‖c‖ * ‖ζ‖ ^ t * ‖V j‖ ≤ ‖c‖ * 1 * ∑ j, ‖V j‖ := by gcongr
      _ = _ := by ring
  · intro hX
    obtain ⟨j, hj⟩ : ∃ j, V j ≠ 0 := by
      by_contra h; push Not at h; exact hV0 (funext h)
    have e0 := congrFun (congrFun hX 0) j
    have e1 := congrFun (congrFun hX 1) j
    simp only [pow_zero, mul_one, pow_one, Pi.zero_apply] at e0 e1
    set a := c * V j with ha
    have ha0 : a ≠ 0 := mul_ne_zero hc0 hj
    have e1' : (ζ * a).re = 0 := by rw [ha, ← e1]; ring_nf
    rw [Complex.mul_re, e0, mul_zero, zero_sub, neg_eq_zero] at e1'
    rcases mul_eq_zero.mp e1' with h | h
    · exact him h
    · exact ha0 (Complex.ext e0 h)

/-- Galí (2015), p. 174 (indeterminacy, two real roots): two distinct real roots of `q` in
`[−1, 1]` give a nonzero bounded mode with `ω̃_{−1} = 0`. -/
theorem exists_mode_of_two_real_roots {P : Par} {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂)
    (h₁ : |r₁| ≤ 1) (h₂ : |r₂| ≤ 1) (hq₁ : P.qr r₁ = 0) (hq₂ : P.qr r₂ = 0) :
    ∃ X : ℕ → Fin 4 → ℝ, (∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) ∧ X 0 3 = 0 ∧
      (∃ M, ∀ t j, |X t j| ≤ M) ∧ X ≠ 0 := by
  obtain ⟨V, hV0, hV⟩ := exists_real_eigvec hq₁
  obtain ⟨W, hW0, hW⟩ := exists_real_eigvec hq₂
  have hbd : ∀ (r : ℝ), |r| ≤ 1 → ∀ (U : Fin 4 → ℝ) t j, |(r ^ t • U) j| ≤ ∑ j, |U j| := by
    intro r hr U t j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |r ^ t| * |U j| ≤ 1 * |U j| :=
          mul_le_mul_of_nonneg_right (abs_pow_le_one hr t) (abs_nonneg _)
      _ ≤ ∑ j, |U j| := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun j => |U j|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
  by_cases hV3 : V 3 = 0
  · refine ⟨fun t => r₁ ^ t • V, geom_mode hV, by simp [hV3], ⟨_, hbd r₁ h₁ V⟩,
      fun h => hV0 ?_⟩
    have := congrFun h 0; simpa using this
  by_cases hW3 : W 3 = 0
  · refine ⟨fun t => r₂ ^ t • W, geom_mode hW, by simp [hW3], ⟨_, hbd r₂ h₂ W⟩,
      fun h => hW0 ?_⟩
    have := congrFun h 0; simpa using this
  refine ⟨fun t => W 3 • (r₁ ^ t • V) - V 3 • (r₂ ^ t • W), fun t => ?_, ?_,
    ⟨|W 3| * ∑ j, |V j| + |V 3| * ∑ j, |W j|, fun t j => ?_⟩, ?_⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hV, hW]
    module
  · simp; ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hbd r₁ h₁ V t j) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hbd r₂ h₂ W t j) (abs_nonneg _)
  · intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp only [pow_zero, one_smul, pow_one, Pi.zero_apply] at e0 e1
    apply hV0
    funext j
    have a0 := congrFun e0 j
    have a1 := congrFun e1 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a0 a1
    have : W 3 * (r₁ - r₂) * V j = 0 := by linear_combination a1 - r₂ * a0
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hW3
      · exact absurd (sub_eq_zero.mp h'') hne
    · exact h'

/-- Galí (2015), p. 174 (indeterminacy, two real roots): not determinate. -/
theorem not_determinate_of_two_real_roots [Nonempty Ω] {P : Par} {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂)
    (h₁ : |r₁| ≤ 1) (h₂ : |r₂| ≤ 1) (hq₁ : P.qr r₁ = 0) (hq₂ : P.qr r₂ = 0) :
    ¬ Determinate 𝔼 P := by
  obtain ⟨X, hX, h0, hb, hX0⟩ := exists_mode_of_two_real_roots hne h₁ h₂ hq₁ hq₂
  exact not_determinate_of_mode 𝔼 hX h0 hb hX0

/-- Galí (2015), p. 174 (indeterminacy, a double real root): a real root `r ∈ (−1, 1)` of
multiplicity at least two gives a nonzero bounded solution `rᵗ((t + c) V + r V′)` (or a pure
mode when `κ_w = κ_p`) with `ω̃_{−1} = 0`. -/
theorem not_determinate_of_double_root [Nonempty Ω] {P : Par} (hP : P.Adm) {r : ℝ}
    (hr : |r| < 1) (hq : P.qr r = 0) (hd : P.dqr r = 0) : ¬ Determinate 𝔼 P := by
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [Par.qr_zero] at hq; exact (P.c0_neg hP).ne hq
  obtain ⟨hb0, hb1, -, -, -, hlp, hlw, -⟩ := hP
  have hbr : 0 < 1 - P.β * r := by
    have := abs_lt.mp hr
    nlinarith [abs_lt.mp hr]
  rw [P.qr_factor] at hq
  rw [P.dqr_factor] at hd
  by_cases hk : P.κw - P.κp = 0
  · -- `κ_w = κ_p`: then `Br(r) = 0` and `(1 − βr, κ_p, κ_w, 0)` is an eigenvector
    have hBr : P.Brr r = 0 := by
      by_contra hB
      rw [hk] at hq hd
      have hD : P.Dr r = 0 := by
        have : P.Brr r * P.Dr r = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      have hD' : -2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)) = 0 := by
        rw [hD] at hd
        have : P.Brr r * (-2 * P.β * r + (1 + P.β + (P.lamP + P.lamW))) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      simp only [Par.Dr] at hD
      have hr2 : P.β * r ^ 2 = 1 := by nlinarith
      have : r ^ 2 < 1 := by nlinarith [abs_lt.mp hr]
      nlinarith
    set V : Fin 4 → ℝ := ![1 - P.β * r, P.κp, P.κw, 0] with hVdef
    have hV : P.A0 *ᵥ V = r • (P.A1 *ᵥ V) := by
      funext i
      fin_cases i <;> simp [hVdef, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Par.A0,
        Par.A1]
      · simp only [Par.Brr] at hBr; linear_combination hBr
      · ring
      · ring
      · linear_combination hk
    refine not_determinate_of_mode 𝔼 (X := fun t => r ^ t • V) (geom_mode hV) (by simp [hVdef])
      ⟨∑ j, |V j|, fun t j => ?_⟩ fun h => ?_
    · rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      calc |r ^ t| * |V j| ≤ 1 * |V j| :=
            mul_le_mul_of_nonneg_right (abs_pow_le_one hr.le t) (abs_nonneg _)
        _ ≤ ∑ j, |V j| := by
            rw [one_mul]
            exact Finset.single_le_sum (f := fun j => |V j|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)
    · have := congrFun (congrFun h 0) 0
      simp [hVdef] at this
      linarith
  · -- `κ_w ≠ κ_p`: the eigenvector field `v(r)` and its derivative give a Jordan chain
    set k := P.κw - P.κp with hkdef
    set V : Fin 4 → ℝ := ![P.Dr r * (1 - P.β * r), P.κp * P.Dr r + P.lamP * r * k,
      P.κw * P.Dr r - P.lamW * r * k, k * (1 - P.β * r)] with hVdef
    set D' := -2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)) with hD'
    set V' : Fin 4 → ℝ := ![D' * (1 - P.β * r) - P.β * P.Dr r, P.κp * D' + P.lamP * k,
      P.κw * D' - P.lamW * k, -(k * P.β)] with hV'def
    have hV : ∀ i, (P.A0 *ᵥ V) i = r * (P.A1 *ᵥ V) i := by
      intro i
      fin_cases i <;> simp [hVdef, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Par.A0,
        Par.A1]
      · simp only [Par.Brr, Par.Dr, Par.Hr] at hq ⊢; linear_combination hq
      · ring
      · ring
      · simp only [Par.Dr]; ring
    have hV' : ∀ i, (P.A0 *ᵥ V') i = r * (P.A1 *ᵥ V') i + (P.A1 *ᵥ V) i := by
      intro i
      fin_cases i <;> simp [hVdef, hV'def, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Par.A0, Par.A1]
      · simp only [Par.Brr, Par.Dr, Par.Hr, hD'] at hd ⊢; linear_combination hd
      · ring
      · ring
      · simp only [hD']; ring
    have hV3 : V 3 ≠ 0 := by rw [hVdef]; exact mul_ne_zero hk hbr.ne'
    set c : ℝ := -(r * V' 3) / V 3 with hc
    have hc3 : c * V 3 + r * V' 3 = 0 := by rw [hc]; field_simp; ring
    obtain ⟨B, hB⟩ := (tendsto_self_mul_const_pow_of_lt_one (abs_nonneg r) hr).bddAbove_range
    refine not_determinate_of_mode 𝔼 (X := fun t => r ^ t • (((t : ℝ) + c) • V + r • V'))
      (fun t => ?_) ?_ ⟨(B + |c|) * ∑ j, |V j| + ∑ j, |V' j|, fun t j => ?_⟩ ?_
    · funext i
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul, hV i, hV' i]
      push_cast
      ring
    · simp only [pow_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_zero, zero_add]
      linear_combination hc3
    · have hBt : |r| ^ t * t ≤ B := by
        have := hB ⟨t, rfl⟩; simp only at this; linarith [mul_comm (|r| ^ t) (t : ℝ)]
      have hpt : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
      have hVj : |V j| ≤ ∑ j, |V j| :=
        Finset.single_le_sum (f := fun j => |V j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hV'j : |V' j| ≤ ∑ j, |V' j| :=
        Finset.single_le_sum (f := fun j => |V' j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      have hB0 : 0 ≤ B := le_trans (by positivity) hBt
      calc |r ^ t * ((t + c) * V j + r * V' j)|
          ≤ (|r| ^ t * t + |r| ^ t * |c|) * |V j| + |r| ^ t * |r| * |V' j| := by
            rw [abs_mul, abs_pow]
            have h1 : |(t + c) * V j + r * V' j| ≤ (t + |c|) * |V j| + |r| * |V' j| := by
              refine (abs_add_le _ _).trans (add_le_add ?_ (by rw [abs_mul]))
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by
                rw [abs_of_nonneg (Nat.cast_nonneg t)])) (abs_nonneg _)
            calc |r| ^ t * |(t + c) * V j + r * V' j| ≤
                |r| ^ t * ((t + |c|) * |V j| + |r| * |V' j|) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = _ := by ring
        _ ≤ (B + |c|) * ∑ j, |V j| + ∑ j, |V' j| := by
            have hr1 : |r| ^ t * |r| ≤ 1 := by
              have := mul_le_mul hpt hr.le (abs_nonneg r) zero_le_one; linarith
            have hc1 : |r| ^ t * |c| ≤ |c| := by
              have := mul_le_mul_of_nonneg_right hpt (abs_nonneg c); linarith
            have e1 : (|r| ^ t * t + |r| ^ t * |c|) * |V j| ≤ (B + |c|) * ∑ j, |V j| :=
              mul_le_mul (by linarith) hVj (abs_nonneg _) (by positivity)
            have e2 : |r| ^ t * |r| * |V' j| ≤ ∑ j, |V' j| := by
              have := mul_le_mul hr1 hV'j (abs_nonneg _) zero_le_one; linarith
            linarith
    · intro h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      apply hV3
      have a0 : c • V + r • V' = 0 := by simpa using e0
      have a1 : r • ((1 + c) • V + r • V') = 0 := by simpa using e1
      have hVz : r • V = 0 := by
        have : r • ((1 + c) • V + r • V') = r • V + r • (c • V + r • V') := by module
        rw [this, a0, smul_zero, add_zero] at a1
        exact a1
      have := congrFun hVz 3
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left hr0

end Dyn

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), p. 174, necessity (strict case)**: if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) < 1` the equilibrium is not determinate: either no
bounded solution exists (no root of `q` in the closed unit disc) or there are many (two or more
roots in the closed disc; one is impossible). -/
theorem not_determinate_of_neg [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 < 0) :
    ¬ Determinate 𝔼 P := by
  rcases Nat.lt_or_ge (closedRoots P).card 2 with hlt | hge
  · have h0 : (closedRoots P).card = 0 := by
      have := closedRoots_card_ne_one hP h1
      omega
    refine not_determinate_of_no_root 𝔼 hP fun ζ hζ h0' => ?_
    have hm := (mem_closedRoots hP).mpr ⟨hζ, h0'⟩
    rw [Multiset.card_eq_zero.mp h0] at hm
    exact Multiset.notMem_zero _ hm
  · by_cases hcx : ∃ ζ ∈ closedRoots P, ζ.im ≠ 0
    · obtain ⟨ζ, hζ, him⟩ := hcx
      obtain ⟨hn, hq⟩ := (mem_closedRoots hP).mp hζ
      exact not_determinate_of_complex_root 𝔼 hn hq him
    · push Not at hcx
      obtain ⟨ζ₁, h₁⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (closedRoots P).card)
      have hcard : 0 < ((closedRoots P).erase ζ₁).card := by
        rw [Multiset.card_erase_of_mem h₁, Nat.pred_eq_sub_one]; omega
      obtain ⟨ζ₂, h₂e⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
      have h₂ := Multiset.mem_of_mem_erase h₂e
      have hreal : ∀ ζ ∈ closedRoots P, ζ = (ζ.re : ℂ) := fun ζ hζ =>
        Complex.ext (by simp) (by simp [hcx ζ hζ])
      obtain ⟨hn₁, hq₁⟩ := (mem_closedRoots hP).mp h₁
      obtain ⟨hn₂, hq₂⟩ := (mem_closedRoots hP).mp h₂
      have hr₁ : P.qr ζ₁.re = 0 := by
        have := hq₁; rw [hreal ζ₁ h₁, Par.eval_qC_ofReal] at this; exact_mod_cast this
      have hr₂ : P.qr ζ₂.re = 0 := by
        have := hq₂; rw [hreal ζ₂ h₂, Par.eval_qC_ofReal] at this; exact_mod_cast this
      have ha₁ : |ζ₁.re| ≤ 1 := by
        have := hn₁; rwa [hreal ζ₁ h₁, Complex.norm_real, Real.norm_eq_abs] at this
      have ha₂ : |ζ₂.re| ≤ 1 := by
        have := hn₂; rwa [hreal ζ₂ h₂, Complex.norm_real, Real.norm_eq_abs] at this
      by_cases h12 : ζ₁ = ζ₂
      · subst h12
        have hc1 : 1 ≤ ((closedRoots P).erase ζ₁).count ζ₁ := Multiset.one_le_count_iff_mem.mpr h₂e
        rw [Multiset.count_erase_self] at hc1
        have hcnt : 2 ≤ P.qC.rootMultiplicity ζ₁ := by
          rw [← count_roots]
          have := Multiset.count_le_of_le ζ₁ (Multiset.filter_le (fun z : ℂ => ‖z‖ ≤ 1) P.qC.roots)
          rw [closedRoots] at hc1
          omega
        obtain ⟨-, hder⟩ := (one_lt_rootMultiplicity_iff_isRoot (qC_ne_zero hP)).mp hcnt
        have hd : P.dqr ζ₁.re = 0 := by
          have := hder
          rw [IsRoot, P.eval_derivative_qC, hreal ζ₁ h₁] at this
          have e : ((P.dqr ζ₁.re : ℝ) : ℂ) = 0 := by
            simp only [Par.dqr]; push_cast; exact this
          exact_mod_cast e
        have hlt1 : |ζ₁.re| < 1 := by
          refine lt_of_le_of_ne ha₁ fun he => ?_
          rcases abs_eq (zero_le_one) |>.mp he with h | h
          · rw [h] at hr₁; linarith
          · rw [h] at hr₁; linarith [P.qr_neg_one_neg hP]
        exact not_determinate_of_double_root 𝔼 hP hlt1 hr₁ hd
      · have hne : ζ₁.re ≠ ζ₂.re := fun h => h12 (by rw [hreal ζ₁ h₁, hreal ζ₂ h₂, h])
        exact not_determinate_of_two_real_roots 𝔼 hne ha₁ ha₂ hr₁ hr₂

/-- Galí (2015), p. 174, necessity: if the condition fails, the equilibrium is not determinate. -/
theorem not_determinate_of_le [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 ≤ 0) :
    ¬ Determinate 𝔼 P := by
  rcases eq_or_lt_of_le h1 with h | h
  · exact not_determinate_of_eq 𝔼 hP h
  · exact not_determinate_of_neg 𝔼 hP h

/-- **Galí (2015), p. 174 (the determinacy theorem, in `q(1)` form)**: under the sign conditions,
system (24) is determinate if and only if `q(1) = λ_p λ_w Θ_y (LHS − 1) > 0`. -/
theorem determinate_iff [Nonempty Ω] {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) :
    Determinate 𝔼 P ↔ 0 < P.qr 1 := by
  constructor
  · intro h
    by_contra h1
    exact not_determinate_of_le 𝔼 hP (not_lt.mp h1) h
  · exact determinate_of_pos 𝔼 hP hΨ

end Dyn

namespace Par

/-- Galí (2015), p. 174: `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` (Galí 2015, p. 174). -/
noncomputable def Aw (P : Par) : Matrix (Fin 4) (Fin 4) ℝ := P.A0⁻¹ * P.A1

/-- Galí (2015), p. 174: `det(A₀ʷ) · det(w I − Aʷ) = det(w A₀ʷ − A₁ʷ)`. -/
theorem det_A0_mul_det_charmat {P : Par} (hP : P.Adm) (w : ℂ) :
    (P.A0.map Complex.ofReal).det * (Matrix.scalar (Fin 4) w - P.Aw.map Complex.ofReal).det =
      (w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal).det := by
  have hA0u : IsUnit P.A0.det := by
    rw [P.det_A0]; exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (P.c0_neg hP).ne)
  have hAA : P.A0.map Complex.ofReal * P.Aw.map Complex.ofReal = P.A1.map Complex.ofReal := by
    rw [Dyn.map_ofReal_eq, Dyn.map_ofReal_eq, Dyn.map_ofReal_eq, ← map_mul, Aw,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA0u]
  rw [← Matrix.det_mul, Matrix.mul_sub, hAA, Matrix.scalar_apply]
  congr 2
  ext i j
  simp [Matrix.mul_diagonal, mul_comm]

/-- Galí (2015), p. 174: the characteristic polynomial of `Aʷ` is a nonzero multiple of the
reversed quartic `Q(w) = w⁴ q(1/w)`. -/
theorem charpoly_Aw {P : Par} (hP : P.Adm) :
    (P.Aw.map Complex.ofReal).charpoly = C (-((P.A0.det : ℂ))⁻¹) * P.QC := by
  have hdA0 : ((P.A0.det : ℝ) : ℂ) ≠ 0 := by
    rw [P.det_A0]; exact_mod_cast neg_ne_zero.mpr (P.c0_neg hP).ne
  have hdc : (P.A0.map Complex.ofReal).det = ((P.A0.det : ℝ) : ℂ) := by
    rw [Dyn.map_ofReal_eq, ← RingHom.map_det]; rfl
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono
    fun w hw => ?_)
  have hw0 : w ≠ 0 := hw
  simp only [Set.mem_ofPred_eq, Matrix.eval_charpoly, eval_mul, eval_C]
  have h := det_A0_mul_det_charmat hP w
  have hsplit : w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal =
      w • (P.A0.map Complex.ofReal - w⁻¹ • P.A1.map Complex.ofReal) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul]
  rw [hsplit, Matrix.det_smul, P.det_A0_sub_A1, hdc] at h
  rw [P.eval_QC_eq hw0]
  simp only [Fintype.card_fin] at h
  have h' := congrArg (fun z => ((P.A0.det : ℝ) : ℂ)⁻¹ * z) h
  simp only [← mul_assoc, inv_mul_cancel₀ hdA0, one_mul] at h'
  rw [h']
  ring

/-- **Galí (2015), p. 174 (the eigenvalue form)**: under the sign conditions, exactly three
eigenvalues of `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` lie inside the unit circle and one outside (counted with
multiplicity) if and only if `q(1) > 0`. -/
theorem eigen_count_iff {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) :
    ((P.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => ‖z‖ < 1)).card = 3 ∧
      ((P.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => 1 < ‖z‖)).card = 1 ↔
      0 < P.qr 1 := by
  have hc : (-((P.A0.det : ℂ))⁻¹) ≠ 0 := by
    rw [P.det_A0]
    simp only [Complex.ofReal_neg, inv_neg, neg_neg, ne_eq, inv_eq_zero]
    exact_mod_cast (P.c0_neg hP).ne
  rw [charpoly_Aw hP, roots_C_mul _ hc]
  constructor
  · rintro ⟨hin, hout⟩
    by_contra hq
    have hq' := not_lt.mp hq
    have h4 := card_roots_QC hP
    -- no root of `Q` lies on the unit circle
    have hsplit := Multiset.filter_add_not (fun z : ℂ => ‖z‖ < 1) P.QC.roots
    have hnot : (P.QC.roots.filter (fun z => ¬ ‖z‖ < 1)).card = 1 := by
      have := congrArg Multiset.card hsplit
      rw [Multiset.card_add, hin, h4] at this
      omega
    have hsub : P.QC.roots.filter (fun z => 1 < ‖z‖) ≤
        P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
      Multiset.monotone_filter_right _ fun z h => not_lt.mpr h.le
    have heqf : P.QC.roots.filter (fun z => 1 < ‖z‖) =
        P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
      Multiset.eq_of_le_of_card_le hsub (by rw [hout, hnot])
    have hcirc : ∀ z ∈ P.QC.roots, ‖z‖ ≠ 1 := by
      intro z hz h1
      have hm : z ∈ P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
        Multiset.mem_filter.mpr ⟨hz, by rw [h1]; exact lt_irrefl 1⟩
      rw [← heqf, Multiset.mem_filter, h1] at hm
      exact lt_irrefl 1 hm.2
    rcases eq_or_lt_of_le hq' with h1 | h1
    · -- `Q(1) = q(1) = 0`: a unit eigenvalue
      apply hcirc 1 ((mem_roots (QC_ne_zero hP)).mpr ?_) (by simp)
      rw [IsRoot, eval_QC_eq P one_ne_zero, inv_one, one_pow, one_mul]
      have := P.eval_qC_ofReal 1
      rw [Complex.ofReal_one] at this
      rw [this, h1, Complex.ofReal_zero]
    · obtain ⟨w0, hw0⟩ := Multiset.card_eq_one.mp hout
      have hw0f : w0 ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := by
        rw [hw0]; exact Multiset.mem_singleton_self w0
      have hw0m : w0 ∈ P.QC.roots := Multiset.mem_of_mem_filter hw0f
      have hw0n : 1 < ‖w0‖ := (Multiset.mem_filter.mp hw0f).2
      have hw00 : w0 ≠ 0 := by intro h; rw [h, norm_zero] at hw0n; linarith
      -- every root of `q` in the closed disc is `w0⁻¹`
      have hall : ∀ ζ ∈ Dyn.closedRoots P, ζ = w0⁻¹ := by
        intro ζ hζ
        obtain ⟨hn, hq0⟩ := (Dyn.mem_closedRoots hP).mp hζ
        have hζ0 : ζ ≠ 0 := by
          rintro rfl; rw [qC_eval_zero] at hq0; exact (c0_neg hP).ne (by exact_mod_cast hq0)
        have hroot : ζ⁻¹ ∈ P.QC.roots := (mem_roots (QC_ne_zero hP)).mpr (by
          rw [IsRoot, eval_QC_eq P (inv_ne_zero hζ0), inv_inv, hq0, mul_zero])
        have hge : 1 ≤ ‖ζ⁻¹‖ := by
          rw [norm_inv]; exact one_le_inv_iff₀.mpr ⟨norm_pos_iff.mpr hζ0, hn⟩
        have hout' : ζ⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) :=
          Multiset.mem_filter.mpr ⟨hroot, lt_of_le_of_ne hge (Ne.symm (hcirc _ hroot))⟩
        rw [hw0, Multiset.mem_singleton] at hout'
        rw [← hout', inv_inv]
      -- `w0⁻¹` is a root of `q` in the open disc
      have hmem : w0⁻¹ ∈ Dyn.closedRoots P := by
        refine (Dyn.mem_closedRoots hP).mpr ⟨?_, ?_⟩
        · rw [norm_inv]; exact inv_le_one_of_one_le₀ hw0n.le
        · have := (mem_roots (QC_ne_zero hP)).mp hw0m
          rw [IsRoot, eval_QC_eq P hw00] at this
          exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hw00)
      -- and it is simple
      have hcount : (Dyn.closedRoots P).count w0⁻¹ ≤ 1 := by
        rw [Dyn.closedRoots, Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ ≤ 1)
          ((Dyn.mem_closedRoots hP).mp hmem).1, count_roots]
        by_contra hm
        obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot (t := w0⁻¹)
          (Dyn.qC_ne_zero hP)).mp (by omega)
        have hQd : P.QC.derivative.IsRoot w0 := by
          rw [IsRoot, eval_derivative_QC]
          rw [IsRoot, P.eval_derivative_qC] at hd
          rw [IsRoot, eval_qC] at hr
          have hw' : w0 * w0⁻¹ = 1 := mul_inv_cancel₀ hw00
          linear_combination (4 * w0 ^ 3) * hr - w0 ^ 2 * hd
            + (-4 * w0 ^ 2 * w0⁻¹ ^ 3 * P.c4 - 4 * w0 ^ 2 * w0⁻¹ ^ 2 * P.c3
              - 4 * w0 ^ 2 * w0⁻¹ * P.c2 - 4 * w0 ^ 2 * P.c1 - w0 * w0⁻¹ * P.c3
              - 2 * w0 * P.c2 - P.c3) * hw'
        have hm2 := (one_lt_rootMultiplicity_iff_isRoot (QC_ne_zero hP)).mpr
          ⟨(mem_roots (QC_ne_zero hP)).mp hw0m, hQd⟩
        have : 2 ≤ (P.QC.roots.filter (fun z => 1 < ‖z‖)).count w0 := by
          rw [Multiset.count_filter_of_pos (p := fun z : ℂ => 1 < ‖z‖) hw0n, count_roots]
          omega
        rw [hw0, Multiset.count_singleton_self] at this
        omega
      have hcard : (Dyn.closedRoots P).card = 1 := by
        rw [Multiset.eq_replicate_of_mem hall, Multiset.card_replicate]
        have := Multiset.count_pos.mpr hmem
        rw [Multiset.eq_replicate_of_mem hall, Multiset.count_replicate_self] at this hcount
        omega
      exact Dyn.closedRoots_card_ne_one hP h1 hcard
  · intro h1
    exact ⟨inCount_QC hP hΨ h1, outCount_QC hP hΨ h1⟩

end Par

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (24), p. 173, row by row: the matrix equation is the IS equation (22) with
rule (23) substituted, the price and wage Phillips curves (18) and (20), and the real-wage
identity (21), where `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` and
`u_t = (r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t)`. -/
theorem eq24_iff (P : Par) (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t) ↔
      ∀ ω, (P.σ + P.φy) * x t 0 ω + P.φp * x t 1 ω + P.φw * x t 2 ω =
          P.σ * 𝔼.E t (x (t + 1) 0) ω + 𝔼.E t (x (t + 1) 1) ω + u t 0 ω ∧
        x t 1 ω = P.β * 𝔼.E t (x (t + 1) 1) ω + P.κp * x t 0 ω
          + P.lamP * 𝔼.E t (x (t + 1) 3) ω ∧
        x t 2 ω = P.β * 𝔼.E t (x (t + 1) 2) ω + P.κw * x t 0 ω
          - P.lamW * 𝔼.E t (x (t + 1) 3) ω ∧
        𝔼.E t (x (t + 1) 3) ω = x t 3 ω + x t 2 ω - x t 1 ω - u t 1 ω := by
  constructor
  · intro h ω
    have h0 := congrFun (congrFun h 0) ω
    have h1 := congrFun (congrFun h 1) ω
    have h2 := congrFun (congrFun h 2) ω
    have h3 := congrFun (congrFun h 3) ω
    simp only [Par.A0, Fin.isValue, rvMul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_four, Matrix.cons_val_one,
      Matrix.cons_val, zero_mul, add_zero, Par.A1, B0, Pi.add_apply, one_mul, Fin.sum_univ_two,
      neg_mul, zero_add] at h0 h1 h2 h3
    refine ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2,
      by linear_combination -h3⟩
  · intro h
    funext i ω
    obtain ⟨h0, h1, h2, h3⟩ := h ω
    fin_cases i <;>
      simp [rvMul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Par.A0, Par.A1, B0]
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2
    · linear_combination -h3

end Dyn

namespace Par

/-- Galí (2015), p. 174: the left-hand side
`φ_p + φ_w + φ_y (1 − β)(λ_p + λ_w)/(λ_w κ_p + λ_p κ_w)` of the determinacy condition. -/
noncomputable def Lhs (P : Par) : ℝ := P.φp + P.φw + P.φy * (1 - P.β) * (P.lamP + P.lamW) / P.Ψ

/-- Galí (2015), p. 174: `q(1) = Ψ (LHS − 1)`, i.e. `det(A₀ʷ − A₁ʷ) = −Ψ (LHS − 1)`. -/
theorem qr_one_eq_mul {P : Par} (hΨ : P.Ψ ≠ 0) : P.qr 1 = P.Ψ * (P.Lhs - 1) := by
  rw [qr_one, Lhs]; field_simp; ring

/-- Galí (2015), p. 174: `q(1) > 0` is exactly the book's condition `LHS > 1`. -/
theorem qr_one_pos_iff {P : Par} (hΨ : 0 < P.Ψ) : 0 < P.qr 1 ↔ 1 < P.Lhs := by
  rw [qr_one_eq_mul hΨ.ne']
  constructor
  · intro h; by_contra h'; nlinarith
  · intro h; nlinarith

end Par

/-- Galí (2015), (18) and (20), p. 172: the system parameters from the primitives,
`κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def bookPar (β σ φ α lamP lamW φp φw φy : ℝ) : Par :=
  ⟨β, σ, α * lamP / (1 - α), lamW * (σ + φ / (1 - α)), lamP, lamW, φp, φw, φy⟩

/-- Galí (2015), p. 174: the book's hypotheses give the sign conditions. -/
theorem bookPar_adm {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) : (bookPar β σ φ α lamP lamW φp φw φy).Adm := by
  have h1α : 0 < 1 - α := by linarith
  exact ⟨hβ0, hβ1, hσ, by simp only [bookPar]; positivity, by simp only [bookPar]; positivity,
    hlp, hlw, hfp, hfw, hfy⟩

/-- Galí (2015), p. 174: `Ψ = λ_p λ_w Θ_y` with `Θ_y = σ + (φ + α)/(1 − α)`. -/
theorem bookPar_Ψ {β σ φ α lamP lamW φp φw φy : ℝ} (hα1 : α < 1) :
    (bookPar β σ φ α lamP lamW φp φw φy).Ψ = lamP * lamW * (σ + (φ + α) / (1 - α)) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  simp only [Par.Ψ, bookPar]
  field_simp
  ring

/-- Galí (2015), p. 174: the left-hand side in the book's form. -/
theorem bookPar_Lhs {β σ φ α lamP lamW φp φw φy : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    (bookPar β σ φ α lamP lamW φp φw φy).Lhs =
      φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have h1α : 0 < 1 - α := by linarith
  have hΘ : 0 < σ + (α + φ) / (1 - α) := by positivity
  rw [Par.Lhs, bookPar_Ψ hα1]
  simp only [bookPar]
  rw [show φ + α = α + φ by ring]
  field_simp
  ring

/-- **Galí (2015), p. 174 — the determinacy theorem.** Let `0 < β < 1`, `σ > 0`, `φ ≥ 0`,
`0 ≤ α < 1`, `λ_p, λ_w > 0` and `φ_p, φ_w, φ_y ≥ 0`. The equilibrium of system (24) under rule
(23) is determinate (for every bounded adapted forcing and every bounded initial real wage gap
`ω̃_{−1}` there is exactly one bounded solution) if and only if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
theorem determinacy_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    Dyn.Determinate 𝔼 (bookPar β σ φ α lamP lamW φp φw φy) ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have hP := bookPar_adm (φp := φp) (φw := φw) (φy := φy) (lamP := lamP) (lamW := lamW)
    hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw hfy
  have hΨ : 0 < (bookPar β σ φ α lamP lamW φp φw φy).Ψ := by
    rw [bookPar_Ψ hα1]
    have h1α : 0 < 1 - α := by linarith
    positivity
  rw [Dyn.determinate_iff 𝔼 hP hΨ, Par.qr_one_pos_iff hΨ, bookPar_Lhs hσ hφ hα0 hα1 hlp hlw]

/-- **Galí (2015), p. 174 — the eigenvalue form.** Under the same hypotheses, exactly three
eigenvalues of `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` lie inside and one outside the unit circle (counted with
multiplicity) if and only if `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`. -/
theorem eigenvalues_iff {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    (((bookPar β σ φ α lamP lamW φp φw φy).Aw.map Complex.ofReal).charpoly.roots.filter
        (fun z => ‖z‖ < 1)).card = 3 ∧
      (((bookPar β σ φ α lamP lamW φp φw φy).Aw.map Complex.ofReal).charpoly.roots.filter
        (fun z => 1 < ‖z‖)).card = 1 ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have hP := bookPar_adm (φp := φp) (φw := φw) (φy := φy) (lamP := lamP) (lamW := lamW)
    hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw hfy
  have hΨ : 0 < (bookPar β σ φ α lamP lamW φp φw φy).Ψ := by
    rw [bookPar_Ψ hα1]
    have h1α : 0 < 1 - α := by linarith
    positivity
  rw [Par.eigen_count_iff hP hΨ, Par.qr_one_pos_iff hΨ, bookPar_Lhs hσ hφ hα0 hα1 hlp hlw]

/-- Galí (2015), p. 174: with `φ_y = 0` the condition reads `φ_p + φ_w > 1`. -/
theorem determinacy_iff_phiY_zero {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {β σ φ α lamP lamW φp φw : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) :
    Dyn.Determinate 𝔼 (bookPar β σ φ α lamP lamW φp φw 0) ↔ 1 < φp + φw := by
  rw [determinacy_iff 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw le_rfl]
  simp

namespace Par

/-- Galí (2015), p. 174 (non-existence criterion): if on the unit circle `q(z)` is never a
nonnegative real number, all four roots of `Q` (eigenvalues of `Aʷ`) lie in the open unit disc.
The proof deforms `Q` to `q(0) w⁴` along `(1 − s) Q(w) + s q(0) w⁴`. -/
theorem inCount_QC_four {P : Par} (hP : P.Adm)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (P.qC.eval z).im = 0 → (P.qC.eval z).re < 0) :
    inCount P.QC = 4 := by
  have hc0 : (P.c0 : ℂ) ≠ 0 := by exact_mod_cast (c0_neg hP).ne
  set a : ℝ → Fin 5 → ℂ := fun s => ![(1 - s) * P.c4, (1 - s) * P.c3, (1 - s) * P.c2,
    (1 - s) * P.c1, P.c0] with ha
  have h := inCount_path a (fun i => by fin_cases i <;> simp only [ha] <;> fun_prop)
    (fun s _ => quart_ne_zero (by simpa [ha] using hc0)) ?_
  · have h0 : quart (a 0) = P.QC := by
      rw [QC]; congr 1; funext i; fin_cases i <;> simp [ha, Qv]
    have h1 : quart (a 1) = C (P.c0 : ℂ) * X ^ 4 := by
      simp [ha, quart]
    rw [h0, h1] at h
    rw [h, inCount, roots_C_mul _ hc0, roots_X_pow]
    simp [Multiset.filter_nsmul, Multiset.filter_singleton]
  · intro s ⟨hs0, hs1⟩ w hw h0
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
    set z := w⁻¹ with hz
    have hzn : ‖z‖ = 1 := by rw [hz, norm_inv, hw, inv_one]
    have hexp : (quart (a s)).eval w = w ^ 4 * ((1 - s) * P.qC.eval z + s * P.c0) := by
      rw [eval_quart, eval_qC, hz]
      simp only [ha, Matrix.cons_val]
      field_simp
      ring
    rw [hexp] at h0
    have key : ((1 - s : ℝ) : ℂ) * P.qC.eval z + ((s * P.c0 : ℝ) : ℂ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hw0)
      push_cast; linear_combination this
    have kre := congrArg Complex.re key
    have kim := congrArg Complex.im key
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im, add_zero] at kre kim
    have hc0' := c0_neg hP
    rcases eq_or_lt_of_le hs1 with h1 | h1
    · subst h1; exact hc0'.ne (by linear_combination kre)
    · have h1s : 0 < 1 - s := by linarith
      have him : (P.qC.eval z).im = 0 := by
        rcases mul_eq_zero.mp kim with h | h
        · linarith
        · exact h
      have hre := hcirc z hzn him
      nlinarith [mul_nonneg hs0 (neg_nonneg.mpr hc0'.le)]

/-- Galí (2015), p. 174 (non-existence criterion): if all roots of `Q` lie in the open unit disc,
`q` has no root in the closed unit disc. -/
theorem no_root_of_inCount_four {P : Par} (hP : P.Adm) (h4 : inCount P.QC = 4) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0 := by
  intro ζ hζ h0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [qC_eval_zero] at h0; exact (c0_neg hP).ne (by exact_mod_cast h0)
  have hroot : ζ⁻¹ ∈ P.QC.roots := (mem_roots (QC_ne_zero hP)).mpr (by
    rw [IsRoot, eval_QC_eq P (inv_ne_zero hζ0), inv_inv, h0, mul_zero])
  have hall : P.QC.roots.filter (fun z => ‖z‖ < 1) = P.QC.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by
      rw [card_roots_QC hP]; exact h4.ge)
  rw [← hall, Multiset.mem_filter, norm_inv] at hroot
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have : 1 ≤ ‖ζ‖⁻¹ := one_le_inv_iff₀.mpr ⟨hn, hζ⟩
  linarith [hroot.2]

end Par

/-- Galí (2015), Fig. 6.1, p. 175 (correction): an admissible parameter point violating the
p. 174 condition at which the failure is non-existence: `β = 9/10`, `σ = 3/4`, `φ = 3`,
`α = 3/4`, `λ_p = 1/40`, `λ_w = 6/5`, `φ_p = 2/25`, `φ_w = 31/50`, `φ_y = 7/100`. -/
noncomputable def exNE : Par :=
  bookPar (9 / 10) (3 / 4) 3 (3 / 4) (1 / 40) (6 / 5) (2 / 25) (31 / 50) (7 / 100)

/-- Galí (2015), Fig. 6.1 (correction): the coefficients of `q` at `exNE`. -/
theorem exNE_coeffs : exNE.c0 = -1289 / 125 ∧ exNE.c1 = 449821 / 20000 ∧
    exNE.c2 = -9513 / 625 ∧ exNE.c3 = 140643 / 40000 ∧ exNE.c4 = -243 / 400 := by
  simp only [exNE, bookPar, Par.c0, Par.c1, Par.c2, Par.c3, Par.c4]
  norm_num

/-- Galí (2015), Fig. 6.1 (correction): `exNE` satisfies the sign conditions. -/
theorem exNE_adm : exNE.Adm :=
  bookPar_adm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Galí (2015), Fig. 6.1 (correction): at `exNE` the p. 174 condition fails
(`LHS = 1939/2700 < 1`). -/
theorem exNE_lhs : (2 / 25 : ℝ) + 31 / 50 + 7 / 100 * (1 - 9 / 10) / (3 / 4 + (3 / 4 + 3)
    / (1 - 3 / 4)) * (1 / (1 / 40) + 1 / (6 / 5)) = 1939 / 2700 := by
  norm_num

/-- Galí (2015), Fig. 6.1 (correction): on the unit circle `q` is never a nonnegative real at
`exNE` (its imaginary part is `y · P(x)` with `P > 0` on `[−1, 1]`, and `q(±1) < 0`). -/
theorem exNE_circle : ∀ z : ℂ, ‖z‖ = 1 → (exNE.qC.eval z).im = 0 →
    (exNE.qC.eval z).re < 0 := by
  intro z hz him
  obtain ⟨x, y⟩ := z
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have h := Complex.sq_norm (⟨x, y⟩ : ℂ)
    rw [hz, Complex.normSq_mk] at h
    nlinarith
  obtain ⟨e0, e1, e2, e3, e4⟩ := exNE_coeffs
  rw [Par.eval_qC_mk] at him ⊢
  simp only [e0, e1, e2, e3, e4] at him ⊢
  have hx1 : x ≤ 1 := by nlinarith
  set Pc : ℝ := 449821 / 20000 + 2 * (-9513 / 625) * x + 140643 / 40000 * (4 * x ^ 2 - 1)
    + (-243 / 400) * (8 * x ^ 3 - 4 * x) with hPc
  have hG : 0 < 243 / 50 * x ^ 2 - 92043 / 10000 * x + 188073 / 10000 := by
    nlinarith [sq_nonneg (x - 1)]
  have hPpos : 0 < Pc := by
    have : Pc = 6707 / 40000 + (1 - x) * (243 / 50 * x ^ 2 - 92043 / 10000 * x
      + 188073 / 10000) := by rw [hPc]; ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hG.le]
  have himP : y * Pc = 0 := by
    rw [hPc]
    linear_combination him - (-(140643 / 40000) * y - 4 * (-243 / 400) * x * y) * hxy
  have hy : y = 0 := (mul_eq_zero.mp himP).resolve_right hPpos.ne'
  subst hy
  have hx : x = 1 ∨ x = -1 := by
    have : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hx with rfl | rfl <;> norm_num

/-- **Galí (2015), Fig. 6.1, p. 175 (correction): non-existence in the "Indeterminacy"
region.** At `exNE` (`LHS < 1`) `q` has no root in the closed unit disc and all four
eigenvalues of `Aʷ` lie inside the unit circle. -/
theorem exNE_no_root : (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → exNE.qC.eval ζ ≠ 0) ∧
    ((exNE.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => ‖z‖ < 1)).card = 4 := by
  have h4 := Par.inCount_QC_four exNE_adm exNE_circle
  refine ⟨Par.no_root_of_inCount_four exNE_adm h4, ?_⟩
  have hc : (-((exNE.A0.det : ℂ))⁻¹) ≠ 0 := by
    rw [exNE.det_A0]
    simp only [Complex.ofReal_neg, inv_neg, neg_neg, ne_eq, inv_eq_zero]
    exact_mod_cast (Par.c0_neg exNE_adm).ne
  rw [Par.charpoly_Aw exNE_adm, roots_C_mul _ hc]
  exact h4

/-- **Galí (2015), Fig. 6.1, p. 175 (correction).** At `exNE`, where the p. 174 condition
fails, system (24) with zero forcing and initial real wage gap `ω̃_{−1} = 1` has no bounded
solution, under any expectation system: the failure is non-existence, not multiplicity. -/
theorem exNE_no_bounded_solution {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (x : ℕ → Fin 4 → Ω → ℝ) : ¬ (Dyn.IsSol 𝔼 exNE 0 (fun _ => 1) x ∧ Fwd.VBounded x) :=
  fun h => Dyn.no_bounded_solution_of_no_root 𝔼 exNE_adm exNE_no_root.1 x h.1 h.2

/-- Galí (2015), §6.2.1 (baseline calibration): `λ_p` and `λ_w` for `β = 0.99`, `θ_p = θ_w = 3/4`,
`α = 1/4`, `ε_p = 9`, `ε_w = 4.5`, `φ = 5`. -/
theorem baseline_lambdas :
    (1 - 3 / 4 : ℝ) * (1 - 99 / 100 * (3 / 4)) / (3 / 4) * ((1 - 1 / 4) / (1 - 1 / 4 + 1 / 4 * 9))
      = 103 / 4800 ∧
    (1 - 3 / 4 : ℝ) * (1 - 99 / 100 * (3 / 4)) / (3 / 4 * (1 + 9 / 2 * 5)) = 103 / 28200 := by
  norm_num

/-- Galí (2015), Fig. 6.1, p. 175: the baseline calibration with `φ_p = 9/10`,
`φ_w = φ_y = 0` (so `LHS = 9/10 < 1`). -/
noncomputable def exBase : Par :=
  bookPar (99 / 100) 1 5 (1 / 4) (103 / 4800) (103 / 28200) (9 / 10) 0 0

/-- Galí (2015), Fig. 6.1 (baseline): `q(0) < 0 < q(9/10)` and `q(1) < 0`. -/
theorem exBase_signs : exBase.qr 0 < 0 ∧ 0 < exBase.qr (9 / 10) ∧ exBase.qr 1 < 0 := by
  simp only [exBase, bookPar, Par.qr, Par.c0, Par.c1, Par.c2, Par.c3, Par.c4]
  norm_num

/-- Galí (2015), Fig. 6.1 (baseline): `q` has two distinct real roots in `(0, 1)`, i.e. two
eigenvalues of `Aʷ` outside the unit circle (two stable roots for one predetermined
variable). -/
theorem exBase_two_roots : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < 9 / 10 ∧ 9 / 10 < r₂ ∧ r₂ < 1 ∧
    exBase.qr r₁ = 0 ∧ exBase.qr r₂ = 0 := by
  obtain ⟨h0, hm, h1⟩ := exBase_signs
  obtain ⟨r₁, ⟨a1, b1⟩, e1⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 9 / 10 by norm_num)
    (exBase.continuous_qr).continuousOn (show (0 : ℝ) ∈ Set.Ioo (exBase.qr 0)
      (exBase.qr (9 / 10)) from ⟨h0, hm⟩)
  obtain ⟨r₂, ⟨a2, b2⟩, e2⟩ := intermediate_value_Ioo' (show (9 / 10 : ℝ) ≤ 1 by norm_num)
    (exBase.continuous_qr).continuousOn (show (0 : ℝ) ∈ Set.Ioo (exBase.qr 1)
      (exBase.qr (9 / 10)) from ⟨h1, hm⟩)
  exact ⟨r₁, r₂, a1, b1, a2, b2, e1, e2⟩

/-- **Galí (2015), Fig. 6.1, p. 175 (baseline: multiplicity).** At the baseline calibration
with `φ_p = 9/10`, `φ_w = φ_y = 0` the failure of the p. 174 condition is genuine
indeterminacy: with zero forcing and `ω̃_{−1} = 0` there are two different bounded
solutions of (24). -/
theorem exBase_multiplicity {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) :
    ∃ x y : ℕ → Fin 4 → Ω → ℝ, x ≠ y ∧ Dyn.IsSol 𝔼 exBase 0 0 x ∧ Fwd.VBounded x ∧
      Dyn.IsSol 𝔼 exBase 0 0 y ∧ Fwd.VBounded y := by
  obtain ⟨r₁, r₂, a1, b1, a2, b2, e1, e2⟩ := exBase_two_roots
  obtain ⟨X, hX, h0, hb, hX0⟩ := Dyn.exists_mode_of_two_real_roots (P := exBase)
    (show r₁ ≠ r₂ by intro h; linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) e1 e2
  obtain ⟨hz, hzb, hc, hcb, hne⟩ := Dyn.multiple_solutions_of_mode 𝔼 hX h0 hb hX0
  exact ⟨_, _, hne, hc, hcb, hz, hzb⟩

end Gali.StickyWagesPrices.Determinacy4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Labour aggregation, labour demand and the employment–output relation

Galí (2015), Chapter 6, §6.1.1 (pp. 164–165), eqs. (2)–(4), and §6.2 (pp. 170–171); the same
relation is restated in Appendix 6.1 (pp. 189–190).

Labour types are indexed by a measure space `(J, μ)`: the book's continuum `[0, 1]` with
Lebesgue measure is `μ = volume.restrict (Set.Icc 0 1)`, and finitely many types with weights
`w j` is `μ = Finite.weightMeasure w`. For `ε_w > 1` the labour index of a firm is
`N = (∫ N(j)^{1−1/ε_w} dj)^{ε_w/(ε_w−1)}` (2) and the wage index is
`W = (∫ W(j)^{1−ε_w} dj)^{1/(1−ε_w)}` (4). The CES machinery is restated from the Chapter 3
project (`CES.lean`), with goods and prices replaced by labour types and wages.

## Main results

* `wageBill_ge`, `wageBill_eq_iff`: every labour bundle costs at least `W · N` (its own index
  `N`), with equality **iff** it is on the labour-demand schedule (3) almost everywhere.
* `cost_min_iff`: (3) is the **unique cost minimiser**: among bundles delivering the index `N`,
  a bundle minimises the wage bill iff it equals `(W(j)/W)^{−ε_w} N` a.e.
* `laborIndex_demand`, `wageBill_demand`: (3) delivers `N` and the wage-bill identity
  `∫ W(j) N(i,j) dj = W N(i)` (p. 165).
* `unitInterval_cost_minimisation`, `Finite.finite_cost_minimisation`: the continuum `[0, 1]`
  and finitely many types with positive weights.
* `aggregate_employment`, `employment_identity`: with labour demand (3), production (1) and
  goods demand, `N = ∫∫ N(i,j) dj di = Δ_w Δ_p (Y/A)^{1/(1−α)}` **exactly**, hence
  `(1 − α) n = y − a + d_w + d_p` (pp. 170–171).
* `dW_nonneg`, `dP_nonneg`, `dW_eq_zero_iff`, `dP_eq_zero_iff` (and `_const` forms):
  `d_w, d_p ≥ 0`, with equality iff there is no wage (price) dispersion.
* `dW_family_first_order`, `dP_family_first_order`, `employment_first_order`: along
  one-parameter families of wage and price distributions `d_w`, `d_p` vanish with zero
  derivative, so `(1 − α) n = y − a` to first order (p. 171).
-/

namespace Gali.StickyWagesPrices.LaborAggregation

open MeasureTheory ProbabilityTheory

variable {J : Type*} [MeasurableSpace J]


/-- Galí (2015), eq. (4), p. 165: the wage index `W = (∫ W(j)^{1−ε} dj)^{1/(1−ε)}`. -/
noncomputable def cesIndex (μ : Measure J) (ε : ℝ) (W : J → ℝ) : ℝ :=
  (∫ j, W j ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), eq. (2), p. 164: the CES labour index (2)
`N = (∫ N(j)^{(ε−1)/ε} dj)^{ε/(ε−1)}`. -/
noncomputable def laborIndex (μ : Measure J) (ε : ℝ) (n : J → ℝ) : ℝ :=
  (∫ j, n j ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N`. -/
noncomputable def laborDemand (μ : Measure J) (ε : ℝ) (W : J → ℝ) (N : ℝ) (j : J) : ℝ :=
  (W j / cesIndex μ ε W) ^ (-ε) * N

/-- Galí (2015), §6.1.1, p. 164: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), §6.1.1, p. 164: the factorisation behind `young_le`,
`n^r = (a n N^{−1/ε})^r (a^{1−ε} N^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    (a * n * N ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) ^ (1 / ε)
      = n ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hn,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le]
  have e1 : a ^ ((ε - 1) / ε) * n ^ ((ε - 1) / ε) * N ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * N ^ ((ε - 1) / ε * (1 / ε)))
      = n ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (N ^ (-1 / ε * ((ε - 1) / ε)) * N ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hN]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), §6.1.1, p. 164: the pointwise weighted AM–GM (Young) inequality behind
cost minimisation. For a relative wage `a > 0`, a quantity `n ≥ 0` and an aggregate
`N > 0`, `n^r ≤ r (a n N^{−1/ε}) + (1/ε) a^{1−ε} N^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    n ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * n * N ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hn hN]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), §6.1.1, p. 164: equality in `young_le` holds iff `n = a^{−ε} N`, i.e. iff
the quantity lies on the labour-demand schedule (3). -/
theorem young_eq_iff {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    n ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * n * N ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) ↔
      n = a ^ (-ε) * N := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hn hN, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * N ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * N ^ ((ε - 1) / ε) = a * N ^ (-1 / ε) * (a ^ (-ε) * N) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : N ^ ((ε - 1) / ε) = N ^ (-1 / ε) * N := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hN, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * n * N ^ (-1 / ε) = a * N ^ (-1 / ε) * n by ring]
  exact mul_right_inj' hk

variable {μ : Measure J} {ε : ℝ} {W : J → ℝ}

/-- Galí (2015), §6.1.1, pp. 164–165: the wage index is positive when `∫ W(j)^{1−ε} > 0`. -/
theorem cesIndex_pos (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) : 0 < cesIndex μ ε W :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), §6.1.1, pp. 164–165: `W^{1−ε} = ∫ W(j)^{1−ε} dj`, the defining property. -/
theorem cesIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    cesIndex μ ε W ^ (1 - ε) = ∫ j, W j ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), eq. (4), p. 165 (index condition): `∫ (W(j)/W)^{1−ε} di = 1`. -/
theorem integral_relWage_rpow (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    ∫ j, (W j / cesIndex μ ε W) ^ (1 - ε) ∂μ = 1 := by
  have hI := cesIndex_pos hpos
  simp_rw [Real.div_rpow (hW _).le hI.le]
  rw [integral_div, cesIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), eq. (4), p. 165: the relative-wage integrand `(W(j)/W)^{1−ε}` is integrable. -/
theorem integrable_relWage_rpow (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hW : ∀ j, 0 < W j)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    Integrable (fun j => (W j / cesIndex μ ε W) ^ (1 - ε)) μ := by
  have hI := cesIndex_pos hpos
  simp_rw [Real.div_rpow (hW _).le hI.le]
  exact hWi.div_const _

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N` delivers
exactly the aggregate `N`. -/
theorem laborIndex_demand (hε : 1 < ε) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) : laborIndex μ ε (laborDemand μ ε W N) = N := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ j, laborDemand μ ε W N j ^ ((ε - 1) / ε)
      = N ^ ((ε - 1) / ε) * (W j / cesIndex μ ε W) ^ (1 - ε) := by
    intro j
    have ha : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
    rw [laborDemand, Real.mul_rpow (by positivity) hN, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold laborIndex
  simp_rw [hpt]
  rw [integral_const_mul, integral_relWage_rpow hε hW hpos, mul_one, Real.rpow_rpow_inv hN hr]

/-- Galí (2015), §6.1.1, pp. 164–165: `W(j) (W(j)/W)^{−ε} N = W N (W(j)/W)^{1−ε}` pointwise. -/
theorem wage_mul_demand (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) (N : ℝ)
    (j : J) : W j * laborDemand μ ε W N j
      = cesIndex μ ε W * N * (W j / cesIndex μ ε W) ^ (1 - ε) := by
  have hI := cesIndex_pos hpos
  have ha : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
  have h1 : (W j / cesIndex μ ε W) ^ (1 - ε)
      = W j / cesIndex μ ε W * (W j / cesIndex μ ε W) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [laborDemand, h1]
  field_simp

/-- Galí (2015), §6.1.1, pp. 164–165: under the labour-demand schedule, the wage bill is
`∫ W(j) N(j) di = W N`. -/
theorem wageBill_demand (hε : 1 < ε) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    (N : ℝ) : ∫ j, W j * laborDemand μ ε W N j ∂μ = cesIndex μ ε W * N := by
  simp_rw [wage_mul_demand hW hpos N]
  rw [integral_const_mul, integral_relWage_rpow hε hW hpos, mul_one]

/-- Galí (2015), §6.1.1, p. 164: the CES aggregate is nonnegative. -/
theorem laborIndex_nonneg {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) : 0 ≤ laborIndex μ ε n :=
  Real.rpow_nonneg (integral_nonneg fun j => Real.rpow_nonneg (hn j) _) _

/-- Galí (2015), §6.1.1, p. 164: `N^r = ∫ N(j)^r` for the CES aggregate `N`. -/
theorem laborIndex_rpow (hε : 1 < ε) {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) :
    laborIndex μ ε n ^ ((ε - 1) / ε) = ∫ j, n j ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun j => Real.rpow_nonneg (hn j) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), §6.1.1, p. 164: the integrated Young bound. For a bundle with positive
aggregate `N`, `N^r ≤ r N^{−1/ε} (∫ W n)/W + (1/ε) N^r`. -/
theorem integrated_young (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ)
    (hN : 0 < laborIndex μ ε n) :
    Integrable (fun j => (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) μ ∧
      (∀ j, n j ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) ∧
      ∫ j, ((ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
          (∫ j, W j * n j ∂μ) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) := by
  have hI := cesIndex_pos hpos
  have hint1 := hWn.const_mul ((ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W))
  have hint2 := (integrable_relWage_rpow hWi hW hpos).const_mul
    (1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun j => ?_, ?_⟩
  · have h := young_le hε (div_pos (hW j) hI) (hn j) hN
    have e : (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) * (W j * n j)
        = (ε - 1) / ε * (W j / cesIndex μ ε W * n j * laborIndex μ ε n ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relWage_rpow hε hW hpos, mul_one]

/-- Galí (2015), §6.1.1, p. 164 (**cost minimisation**): any bundle
`N(·) ≥ 0` costs at least `W · N`, where `N` is its CES aggregate. -/
theorem wageBill_ge (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) :
    cesIndex μ ε W * laborIndex μ ε n ≤ ∫ j, W j * n j ∂μ := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ j, W j * n j ∂μ := integral_nonneg fun j => mul_nonneg (hW j).le (hn j)
  rcases (laborIndex_nonneg (μ := μ) (ε := ε) hn).eq_or_lt with h0 | hN
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hW hWi hpos hn hWn hN
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun j => Real.rpow_nonneg (hn j) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← laborIndex_rpow hε hn] at hmono
  set N := laborIndex μ ε n
  set S := ∫ j, W j * n j ∂μ
  have hK : 0 < N ^ (-1 / ε) := Real.rpow_pos_of_pos hN _
  have hCr : N ^ ((ε - 1) / ε) = N * N ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hN, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (N * N ^ (-1 / ε)) ≤
      (ε - 1) / ε * (N ^ (-1 / ε) * (S / cesIndex μ ε W)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (N ^ (-1 / ε) / cesIndex μ ε W) * S
        = (ε - 1) / ε * (N ^ (-1 / ε) * (S / cesIndex μ ε W)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm N] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (3), p. 164: a bundle costs exactly `W · N` (its
aggregate `N`) **if and only if** it is the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N`
almost everywhere. -/
theorem wageBill_eq_iff (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) :
    ∫ j, W j * n j ∂μ = cesIndex μ ε W * laborIndex μ ε n ↔
      n =ᵐ[μ] laborDemand μ ε W (laborIndex μ ε n) := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← wageBill_demand hε hW hpos (laborIndex μ ε n)]
    refine integral_congr_ae ?_
    filter_upwards [h] with j hi
    rw [hi]
  intro heq
  rcases (laborIndex_nonneg (μ := μ) (ε := ε) hn).eq_or_lt with h0 | hN
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun j => mul_nonneg (hW j).le (hn j)) hWn).1 heq
    filter_upwards [hz] with j hi
    rw [← h0, laborDemand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hW j).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hW hWi hpos hn hWn hN
  set N := laborIndex μ ε n
  have hcr : Integrable (fun j => n j ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← laborIndex_rpow hε hn]
    exact (Real.rpow_pos_of_pos hN _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun j => sub_nonneg.2 (hle j)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← laborIndex_rpow hε hn, heq]
      have hCr : N ^ ((ε - 1) / ε) = N * N ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hN, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with j hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hW j) hI) (hn j) hN).1 (by
    rw [← hi]
    ring)
  rw [this, laborDemand]

/-- Galí (2015), §6.1.1, p. 164 (dual form): for a bundle with wage bill
`∫ W(j) N(j) = X`, the attainable labour index is at most `X / W`. -/
theorem laborIndex_le_of_wageBill (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) {X : ℝ}
    (hX : ∫ j, W j * n j ∂μ = X) : laborIndex μ ε n ≤ X / cesIndex μ ε W := by
  rw [le_div_iff₀ (cesIndex_pos hpos), mul_comm, ← hX]
  exact wageBill_ge hε hW hWi hpos hn hWn

/-- Galí (2015), §6.1.1, p. 164 (dual form, equality): with wage bill `X`, the index
attains `X / W` iff `N(j) = (W(j)/W)^{−ε} X/W` almost everywhere. -/
theorem laborIndex_eq_iff_of_wageBill (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) {X : ℝ}
    (hX : ∫ j, W j * n j ∂μ = X) :
    laborIndex μ ε n = X / cesIndex μ ε W ↔
      n =ᵐ[μ] laborDemand μ ε W (X / cesIndex μ ε W) := by
  have hI := cesIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (wageBill_eq_iff hε hW hWi hpos hn hWn).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / cesIndex μ ε W := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun j => mul_nonneg (hW j).le (hn j)) hI.le
    have hagg : laborIndex μ ε n = laborIndex μ ε (laborDemand μ ε W (X / cesIndex μ ε W)) := by
      unfold laborIndex
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with j hi
      rw [hi]
    rw [hagg, laborIndex_demand hε hW hpos hX0]

/-- Galí (2015), §6.1.1, pp. 164–165: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ W(j)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : J → ℝ} (hμ : μ ≠ 0) (hf : ∀ j, 0 < f j)
    (hfi : Integrable f μ) : 0 < ∫ j, f j ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun j => (hf j).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun j => (hf j).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), §6.1.1, pp. 164–165: Lebesgue measure on `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), §6.1.1, pp. 164–165, on the book's **continuum of labour types
`[0, 1]` with Lebesgue measure**: (i) every bundle `N(·) ≥ 0` costs at least `W · N`;
(ii) it costs exactly `W · N` iff `N(j) = (W(j)/W)^{−ε} N` for a.e. `j ∈ [0, 1]`;
(iii) the labour-demand schedule attains any aggregate `N ≥ 0`; (iv) it costs `W N`. -/
theorem unitInterval_cost_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ j, 0 < Q j)
    (hQi : IntegrableOn (fun j => Q j ^ (1 - ε)) (Set.Icc 0 1)) {n : ℝ → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hQc : IntegrableOn (fun j => Q j * n j) (Set.Icc 0 1)) :
    cesIndex (volume.restrict (Set.Icc 0 1)) ε Q * laborIndex (volume.restrict (Set.Icc 0 1)) ε n
        ≤ ∫ j in Set.Icc 0 1, Q j * n j ∧
      (∫ j in Set.Icc 0 1, Q j * n j
          = cesIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            laborIndex (volume.restrict (Set.Icc 0 1)) ε n ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          n j = laborDemand (volume.restrict (Set.Icc 0 1)) ε Q
            (laborIndex (volume.restrict (Set.Icc 0 1)) ε n) j) ∧
      (∀ N : ℝ, 0 ≤ N → laborIndex (volume.restrict (Set.Icc 0 1)) ε
        (laborDemand (volume.restrict (Set.Icc 0 1)) ε Q N) = N) ∧
      ∀ N : ℝ, ∫ j in Set.Icc 0 1, Q j * laborDemand (volume.restrict (Set.Icc 0 1)) ε Q N j
        = cesIndex (volume.restrict (Set.Icc 0 1)) ε Q * N := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun j => Real.rpow_pos_of_pos (hQ j) _)
    hQi
  exact ⟨wageBill_ge hε hQ hQi hpos hn hQc, wageBill_eq_iff hε hQ hQi hpos hn hQc,
    fun N hN => laborIndex_demand hε hQ hpos hN, wageBill_demand hε hQ hpos⟩

namespace Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), §6.1.1, pp. 164–165 (finitely many types): the measure with weight `w j` on
type `j`, a discretisation of `[0, 1]` (e.g. `w j = 1/n`). -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ j, ENNReal.ofReal (w j) • Measure.dirac j

/-- Galí (2015), §6.1.1, pp. 164–165: the weighted measure gives type `x` mass `w x`. -/
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
/-- Galí (2015), §6.1.1, pp. 164–165: the weighted measure is finite. -/
theorem weightMeasure_univ_lt_top {w : ι → ℝ} : weightMeasure w Set.univ < ⊤ := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

/-- Galí (2015), §6.1.1, pp. 164–165: every function is integrable for the weighted measure. -/
theorem integrable_weightMeasure {w : ι → ℝ} (f : ι → ℝ) : Integrable f (weightMeasure w) := by
  have : IsFiniteMeasure (weightMeasure w) := ⟨weightMeasure_univ_lt_top⟩
  exact Integrable.of_finite

/-- Galí (2015), §6.1.1, pp. 164–165: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w j f j`. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (f : ι → ℝ) :
    ∫ j, f j ∂(weightMeasure w) = ∑ j, w j * f j := by
  rw [integral_fintype (integrable_weightMeasure f)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw j), smul_eq_mul]

/-- Galí (2015), §6.1.1, pp. 164–165, for **finitely many labour types** with weights
`w j > 0`. With `W = (∑ w W(j)^{1−ε})^{1/(1−ε)}` and `N = (∑ w N(j)^r)^{1/r}`:
(i) `∑ w W(j) N(j) ≥ W N`; (ii) equality iff `N(j) = (W(j)/W)^{−ε} N` for **every** `j`;
(iii) the labour-demand schedule attains any `N ≥ 0`; (iv) it costs exactly `W N`. -/
theorem finite_cost_minimisation [Nonempty ι] (hε : 1 < ε) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) {Q : ι → ℝ} (hQ : ∀ j, 0 < Q j) {n : ι → ℝ} (hn : ∀ j, 0 ≤ n j) :
    (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ * (∑ j, w j * n j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹
        ≤ ∑ j, w j * (Q j * n j) ∧
      (∑ j, w j * (Q j * n j) = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ *
          (∑ j, w j * n j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ ↔
        ∀ j, n j = (Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) *
          (∑ i, w i * n i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹) ∧
      (∀ N : ℝ, 0 ≤ N → (∑ j, w j *
        ((Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N) ^ ((ε - 1) / ε)) ^
          ((ε - 1) / ε)⁻¹ = N) ∧
      ∀ N : ℝ, ∑ j, w j * (Q j * ((Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N))
        = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ * N := by
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).le
  have hμ : weightMeasure w ≠ 0 := by
    intro h
    obtain ⟨x⟩ := ‹Nonempty ι›
    have := weightMeasure_singleton (w := w) x
    rw [h, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.ofReal_pos.2 (hw x)).ne' this.symm
  have hpos := integral_pos_of_pos hμ (fun j => Real.rpow_pos_of_pos (hQ j) (1 - ε))
    (integrable_weightMeasure _)
  have hPI : cesIndex (weightMeasure w) ε Q = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ := by
    rw [cesIndex, integral_weightMeasure hw0]
  have hCA : ∀ d : ι → ℝ, laborIndex (weightMeasure w) ε d
      = (∑ i, w i * d i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ := by
    intro d
    rw [laborIndex, integral_weightMeasure hw0]
  have hD : ∀ N j, laborDemand (weightMeasure w) ε Q N j
      = (Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N := by
    intro N j
    rw [laborDemand, hPI]
  have h1 := wageBill_ge hε hQ (integrable_weightMeasure _) hpos hn (integrable_weightMeasure _)
  have h2 := wageBill_eq_iff hε hQ (integrable_weightMeasure _) hpos hn (integrable_weightMeasure _)
  rw [hPI, hCA, integral_weightMeasure hw0] at h1 h2
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h2
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2]
    constructor
    · intro h j
      rw [← hD]
      exact h j (by rw [weightMeasure_singleton]; exact (ENNReal.ofReal_pos.2 (hw j)).ne')
    · intro h j _
      rw [hD]
      exact h j
  · intro N hN
    have := laborIndex_demand hε hQ hpos hN (μ := weightMeasure w)
    rw [hCA] at this
    simpa only [hD] using this
  · intro N
    have := wageBill_demand hε hQ hpos N (μ := weightMeasure w)
    rw [integral_weightMeasure hw0, hPI] at this
    simpa only [hD] using this

end Finite


/-! ### Labour demand (3) is the unique cost minimiser -/

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule is a feasible bundle: it is
nonnegative and its wage bill is integrable. -/
theorem laborDemand_feasible (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) {N : ℝ} (hN : 0 ≤ N) :
    (∀ j, 0 ≤ laborDemand μ ε W N j) ∧
      Integrable (fun j => W j * laborDemand μ ε W N j) μ := by
  have hI := cesIndex_pos hpos
  refine ⟨fun j => mul_nonneg (Real.rpow_nonneg (div_pos (hW j) hI).le _) hN, ?_⟩
  simp_rw [wage_mul_demand hW hpos N]
  exact (integrable_relWage_rpow hWi hW hpos).const_mul _

/-- Galí (2015), eq. (3), p. 164 (**labour demand is the unique cost minimiser**): a firm that
needs the labour index `N ≥ 0` and uses a bundle `n(·) ≥ 0` with `N(n) = N` minimises its wage
bill `∫ W(j) n(j) dj` over all such bundles **if and only if** `n(j) = (W(j)/W)^{−ε_w} N` for
almost every `j`. -/
theorem cost_min_iff (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) {n : J → ℝ} (hn : ∀ j, 0 ≤ n j)
    (hWn : Integrable (fun j => W j * n j) μ) (hnN : laborIndex μ ε n = N) :
    (∀ m : J → ℝ, (∀ j, 0 ≤ m j) → Integrable (fun j => W j * m j) μ →
        laborIndex μ ε m = N → ∫ j, W j * n j ∂μ ≤ ∫ j, W j * m j ∂μ) ↔
      n =ᵐ[μ] laborDemand μ ε W N := by
  obtain ⟨hd0, hdi⟩ := laborDemand_feasible hW hWi hpos hN
  constructor
  · intro hmin
    have h1 := hmin _ hd0 hdi (laborIndex_demand hε hW hpos hN)
    rw [wageBill_demand hε hW hpos N] at h1
    have h2 := wageBill_ge hε hW hWi hpos hn hWn
    rw [hnN] at h2
    have heq : ∫ j, W j * n j ∂μ = cesIndex μ ε W * laborIndex μ ε n := by
      rw [hnN]
      linarith
    have := (wageBill_eq_iff hε hW hWi hpos hn hWn).1 heq
    rwa [hnN] at this
  · intro hae m hm hWm hmN
    have hc : ∫ j, W j * n j ∂μ = cesIndex μ ε W * N := by
      rw [← wageBill_demand hε hW hpos N]
      refine integral_congr_ae ?_
      filter_upwards [hae] with j hj
      rw [hj]
    rw [hc, ← hmN]
    exact wageBill_ge hε hW hWi hpos hm hWm

/-! ### Dispersion terms and the employment–output relation (pp. 170–171) -/

/-- Galí (2015), p. 171: the dispersion integral `∫ (X(j)/X)^e dj` of a cross-section `X(·)`
with CES index `X = cesIndex μ ε X`. Wage dispersion is `Δ_w = ∫ (W(j)/W)^{−ε_w} dj`
(`e = −ε_w`); price dispersion is `Δ_p = ∫ (P(i)/P)^{−ε_p/(1−α)} di` (`e = −ε_p/(1−α)`). -/
noncomputable def dispIntegral (μ : Measure J) (ε e : ℝ) (X : J → ℝ) : ℝ :=
  ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ

/-- Galí (2015), p. 171: wage dispersion `Δ_w = ∫ (W(j)/W)^{−ε_w} dj`. -/
noncomputable def wageDisp (μ : Measure J) (εw : ℝ) (W : J → ℝ) : ℝ := dispIntegral μ εw (-εw) W

/-- Galí (2015), p. 171: price dispersion `Δ_p = ∫ (P(i)/P)^{−ε_p/(1−α)} di`. -/
noncomputable def priceDisp (μ : Measure J) (α εp : ℝ) (P : J → ℝ) : ℝ :=
  dispIntegral μ εp (-εp / (1 - α)) P

/-- Galí (2015), p. 171: `d_w = (1 − α) log ∫ (W(j)/W)^{−ε_w} dj`. -/
noncomputable def dW (μ : Measure J) (α εw : ℝ) (W : J → ℝ) : ℝ :=
  (1 - α) * Real.log (wageDisp μ εw W)

/-- Galí (2015), p. 171: `d_p = (1 − α) log ∫ (P(i)/P)^{−ε_p/(1−α)} di`. -/
noncomputable def dP (μ : Measure J) (α εp : ℝ) (P : J → ℝ) : ℝ :=
  (1 - α) * Real.log (priceDisp μ α εp P)

/-- Galí (2015), p. 170: with every firm on its labour-demand schedule (3),
`N(i,j) = (W(j)/W)^{−ε_w} N(i)`, firm `i` employs `∫ N(i,j) dj = Δ_w N(i)` hours. -/
theorem firm_hours {F : Type*} {N : F → J → ℝ} {Nf : F → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) (i : F) :
    ∫ j, N i j ∂μ = wageDisp μ ε W * Nf i := by
  simp_rw [hdem i, laborDemand]
  rw [integral_mul_const, wageDisp, dispIntegral]

/-- Galí (2015), pp. 170–171: with production `Y(i) = A N(i)^{1−α}` (1) and output on the
goods-demand schedule `Y(i) = (P(i)/P)^{−ε_p} Y`, `∫ N(i) di = Δ_p (Y/A)^{1/(1−α)}`
(restated from the Chapter 3 project, `employment_level`). -/
theorem firm_index_level {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) :
    ∫ i, Nf i ∂μF = (Y / A) ^ (1 - α)⁻¹ * priceDisp μF α εp P := by
  have hI := cesIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, Nf i = (Y / A) ^ (1 - α)⁻¹ * (P i / cesIndex μF εp P) ^ (-εp / (1 - α)) := by
    intro i
    have ha : 0 < P i / cesIndex μF εp P := div_pos (hP i) hI
    have h1 : Nf i ^ (1 - α) = (P i / cesIndex μF εp P) ^ (-εp) * (Y / A) := by
      have := hprod i
      rw [laborDemand] at this
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-εp), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul, priceDisp, dispIntegral]

/-- Galí (2015), pp. 170–171 (**exact aggregate employment**): with labour demand (3) for every
firm, production (1) and goods demand, aggregate employment
`N = ∫∫ N(i,j) dj di = Δ_w Δ_p (Y/A)^{1/(1−α)}`. -/
theorem aggregate_employment {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) {N : F → J → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) :
    ∫ i, ∫ j, N i j ∂μ ∂μF = wageDisp μ ε W * priceDisp μF α εp P * (Y / A) ^ (1 - α)⁻¹ := by
  simp_rw [firm_hours hdem]
  rw [integral_const_mul, firm_index_level hα1 hP hpos hA hY hN hprod]
  ring

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (**exact employment–output relation**):
`(1 − α) n = y − a + d_w + d_p`, with `n = log ∫∫ N(i,j) dj di`, `y = log Y`, `a = log A`. -/
theorem employment_identity {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) {N : F → J → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) (hDw : 0 < wageDisp μ ε W)
    (hDp : 0 < priceDisp μF α εp P) :
    (1 - α) * Real.log (∫ i, ∫ j, N i j ∂μ ∂μF)
      = Real.log Y - Real.log A + dW μ α ε W + dP μF α εp P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [aggregate_employment hα1 hP hpos hA hY.le hN hprod hdem,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hDw.ne' hDp.ne',
    Real.log_rpow (by positivity), Real.log_div hY.ne' hA.ne', dW, dP]
  field_simp
  ring

/-- Galí (2015), p. 171 (via ch. 3, App. 3.4): the pointwise Bernoulli bound behind
`Δ ≥ 1`. For `ε > 1` and an exponent `e < 1 − ε`, with `q = e/(1 − ε) > 1`,
`x^e ≥ 1 + q (x^{1−ε} − 1)` for `x > 0`, with equality only at `x = 1`. -/
theorem bernoulli_disp {e : ℝ} (hε : 1 < ε) (he : e < 1 - ε) {x : ℝ} (hx : 0 < x) :
    1 + e / (1 - ε) * (x ^ (1 - ε) - 1) ≤ x ^ e ∧
      (1 + e / (1 - ε) * (x ^ (1 - ε) - 1) = x ^ e → x = 1) := by
  have hsub : (1 : ℝ) - ε < 0 := by linarith
  have hq : 1 < e / (1 - ε) := by rw [one_lt_div_of_neg hsub]; exact he
  have hy : 0 < x ^ (1 - ε) := Real.rpow_pos_of_pos hx _
  have hs : -1 ≤ x ^ (1 - ε) - 1 := by linarith
  have hrw : x ^ e = (x ^ (1 - ε)) ^ (e / (1 - ε)) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    have h1 : (1 : ℝ) - ε ≠ 0 := hsub.ne
    field_simp
  rw [hrw]
  refine ⟨by simpa using one_add_mul_self_le_rpow_one_add hs hq.le, fun heq => ?_⟩
  by_contra hne
  have hy1 : x ^ (1 - ε) - 1 ≠ 0 := by
    intro h0
    have h1 : x ^ (1 - ε) = 1 := by linarith
    apply hne
    rw [← Real.rpow_rpow_inv hx.le hsub.ne, h1, Real.one_rpow]
  have := one_add_mul_self_lt_rpow_one_add hs hy1 hq
  simp only [add_sub_cancel] at this
  linarith

/-- Galí (2015), p. 171: the Bernoulli lower bound integrates to one by the index condition
`∫ (X(j)/X)^{1−ε} = 1`. -/
theorem integral_bernoulli_lower [IsProbabilityMeasure μ] (hε : 1 < ε) {X : J → ℝ}
    (hX : ∀ j, 0 < X j) (hXi : Integrable (fun j => X j ^ (1 - ε)) μ) (q : ℝ) :
    Integrable (fun j => 1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1)) μ ∧
      ∫ j, (1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1)) ∂μ = 1 := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hy := integrable_relWage_rpow hXi hX hpos
  have he : (fun j => 1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1))
      = fun j => (1 - q) + q * (X j / cesIndex μ ε X) ^ (1 - ε) := by
    funext j
    ring
  rw [he]
  refine ⟨(integrable_const _).add (hy.const_mul q), ?_⟩
  rw [integral_add (integrable_const _) (hy.const_mul q), integral_const, integral_const_mul,
    integral_relWage_rpow hε hX hpos]
  simp

/-- Galí (2015), p. 171 (Jensen): for `e < 1 − ε` the dispersion integral is at least one,
`∫ (X(j)/X)^e ≥ 1`. -/
theorem one_le_dispIntegral [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε) (he : e < 1 - ε)
    {X : J → ℝ} (hX : ∀ j, 0 < X j) (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) : 1 ≤ dispIntegral μ ε e X := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hI := cesIndex_pos hpos
  obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hX hXi (e / (1 - ε))
  have h := integral_mono hlow hD fun j => (bernoulli_disp hε he (div_pos (hX j) hI)).1
  rwa [hval] at h

/-- Galí (2015), p. 171: `log Δ ≥ 0` for `e < 1 − ε`. -/
theorem log_dispIntegral_nonneg [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε)
    (he : e < 1 - ε) {X : J → ℝ} (hX : ∀ j, 0 < X j)
    (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) :
    0 ≤ Real.log (dispIntegral μ ε e X) :=
  Real.log_nonneg (one_le_dispIntegral hε he hX hXi hD)

/-- Galí (2015), p. 171: `log Δ = 0` **iff** there is no dispersion, `X(j) = X` a.e. -/
theorem log_dispIntegral_eq_zero_iff [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε)
    (he : e < 1 - ε) {X : J → ℝ} (hX : ∀ j, 0 < X j)
    (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) :
    Real.log (dispIntegral μ ε e X) = 0 ↔ ∀ᵐ j ∂μ, X j = cesIndex μ ε X := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hI := cesIndex_pos hpos
  constructor
  · intro hlog
    have h1 := one_le_dispIntegral hε he hX hXi hD
    have hint1 : ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ = 1 := by
      rcases Real.log_eq_zero.1 hlog with h | h | h
      · rw [dispIntegral] at h h1; linarith
      · exact h
      · rw [dispIntegral] at h h1; linarith
    obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hX hXi (e / (1 - ε))
    have hz := (integral_eq_zero_iff_of_nonneg (fun j => sub_nonneg.2
      (bernoulli_disp hε he (div_pos (hX j) hI)).1) (hD.sub hlow)).1 (by
        rw [integral_sub hD hlow, hint1, hval, sub_self])
    filter_upwards [hz] with j hj
    simp only [Pi.zero_apply, sub_eq_zero] at hj
    have := (bernoulli_disp hε he (div_pos (hX j) hI)).2 hj.symm
    rwa [div_eq_one_iff_eq hI.ne'] at this
  · intro h
    have hint1 : ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ = 1 := by
      rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
        filter_upwards [h] with j hj
        rw [hj, div_self hI.ne', Real.one_rpow])]
      simp
    rw [dispIntegral, hint1, Real.log_one]

/-- Galí (2015), p. 171: the index of a cross-section that is a.e. equal to a constant `c` is
`c`, so "`X(j) = X` a.e." is the same as "all `X(j)` are a.e. equal". -/
theorem ae_eq_index_iff_const [IsProbabilityMeasure μ] {X : J → ℝ} (hε : ε ≠ 1)
    (hX : ∀ j, 0 < X j) :
    (∀ᵐ j ∂μ, X j = cesIndex μ ε X) ↔ ∃ c, ∀ᵐ j ∂μ, X j = c := by
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  obtain ⟨j₀, hj₀⟩ := hc.exists
  have hc0 : 0 < c := hj₀ ▸ hX j₀
  have hidx : cesIndex μ ε X = c := by
    unfold cesIndex
    rw [integral_congr_ae (g := fun _ => c ^ (1 - ε)) (by
      filter_upwards [hc] with j hj
      rw [hj])]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact Real.rpow_rpow_inv hc0.le (sub_ne_zero.2 (Ne.symm hε))
  rw [hidx]
  exact hc

/-- Galí (2015), p. 171: the wage exponent `−ε_w` satisfies `−ε_w < 1 − ε_w`. -/
theorem wage_exponent_lt (εw : ℝ) : -εw < 1 - εw := by linarith

/-- Galí (2015), p. 171: the price exponent satisfies `−ε_p/(1 − α) < 1 − ε_p` for
`ε_p > 1`, `0 ≤ α < 1`. -/
theorem price_exponent_lt {α εp : ℝ} (hε : 1 < εp) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -εp / (1 - α) < 1 - εp := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  rw [div_lt_iff₀ h1]
  nlinarith

/-- Galí (2015), p. 171: **wage dispersion is nonnegative**, `d_w ≥ 0` (`α < 1`). -/
theorem dW_nonneg [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) : 0 ≤ dW μ α ε W :=
  mul_nonneg (by linarith) (log_dispIntegral_nonneg hε (wage_exponent_lt ε) hW hWi hD)

/-- Galí (2015), p. 171: `d_w = 0` **iff** there is no wage dispersion, `W(j) = W` a.e. -/
theorem dW_eq_zero_iff [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) :
    dW μ α ε W = 0 ↔ ∀ᵐ j ∂μ, W j = cesIndex μ ε W := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [dW, mul_eq_zero, or_iff_right hsub, wageDisp]
  exact log_dispIntegral_eq_zero_iff hε (wage_exponent_lt ε) hW hWi hD

/-- Galí (2015), p. 171: `d_w = 0` iff all wages are (a.e.) equal. -/
theorem dW_eq_zero_iff_const [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) :
    dW μ α ε W = 0 ↔ ∃ c, ∀ᵐ j ∂μ, W j = c := by
  rw [dW_eq_zero_iff hα1 hε hW hWi hD]
  exact ae_eq_index_iff_const hε.ne' hW

/-- Galí (2015), p. 171: **price dispersion is nonnegative**, `d_p ≥ 0` (`0 ≤ α < 1`). -/
theorem dP_nonneg [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    0 ≤ dP μ α ε P :=
  mul_nonneg (by linarith) (log_dispIntegral_nonneg hε (price_exponent_lt hε hα0 hα1) hP hPi hD)

/-- Galí (2015), p. 171: `d_p = 0` **iff** there is no price dispersion, `P(i) = P` a.e. -/
theorem dP_eq_zero_iff [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dP μ α ε P = 0 ↔ ∀ᵐ i ∂μ, P i = cesIndex μ ε P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [dP, mul_eq_zero, or_iff_right hsub, priceDisp]
  exact log_dispIntegral_eq_zero_iff hε (price_exponent_lt hε hα0 hα1) hP hPi hD

/-- Galí (2015), p. 171: `d_p = 0` iff all prices are (a.e.) equal. -/
theorem dP_eq_zero_iff_const [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dP μ α ε P = 0 ↔ ∃ c, ∀ᵐ i ∂μ, P i = c := by
  rw [dP_eq_zero_iff hα0 hα1 hε hP hPi hD]
  exact ae_eq_index_iff_const hε.ne' hP

/-! ### First order: `d_w` and `d_p` vanish with zero derivative (p. 171) -/

/-- Galí (2015), p. 171 (via ch. 3, App. 3.4): for a bounded measurable `z` on a probability
space every `exp(t z)` is integrable. -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (t : ℝ) : Integrable (fun j => Real.exp (t * z j)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z j ≤ |t * z j| := le_abs_self _
    _ = |t| * |z j| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB j) (abs_nonneg t)

/-- Galí (2015), p. 171: for bounded `z` the cumulant-generating function is analytic on `ℝ`. -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Galí (2015), p. 171: along the family `X(j) = exp(x̄ + s z(j))` the CES index is
`exp(x̄ + K((1 − ε)s)/(1 − ε))`, with `K` the cumulant-generating function of `z`
(restated from the Chapter 3 project, `priceIndex_family`). -/
theorem cesIndex_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (xbar s : ℝ) :
    cesIndex μ ε (fun j => Real.exp (xbar + s * z j))
      = Real.exp (xbar + cgf z μ ((1 - ε) * s) / (1 - ε)) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ j, Real.exp (xbar + s * z j) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * xbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ j, Real.exp (xbar + s * z j) ^ (1 - ε)
        = Real.exp ((1 - ε) * xbar) * Real.exp ((1 - ε) * s * z j) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  unfold cesIndex
  rw [hsum, Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) (hM _)),
    Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  congr 1
  field_simp

/-- Galí (2015), p. 171: along `X(j) = exp(x̄ + s z(j))`, **exactly**
`log ∫ (X(j)/X)^e dj = K(e s) − (e/(1 − ε)) K((1 − ε) s)`. -/
theorem log_dispIntegral_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar s : ℝ) :
    Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j)))
      = cgf z μ (e * s) - e / (1 - ε) * cgf z μ ((1 - ε) * s) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hidx : cesIndex μ ε (fun j => Real.exp (xbar + s * z j))
      = Real.exp (xbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)) :=
    cesIndex_family hz hB hε xbar s
  have hrel : ∀ j, (Real.exp (xbar + s * z j) /
      Real.exp (xbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) ^ e
      = Real.exp (-(e * (Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)))) *
        Real.exp (e * s * z j) := by
    intro j
    rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [dispIntegral, hidx]
  simp_rw [hrel]
  rw [integral_const_mul]
  have hm2 : ∫ j, Real.exp (e * s * z j) ∂μ = mgf z μ (e * s) := rfl
  rw [hm2, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf, cgf]
  ring

/-- Galí (2015), p. 171: `s ↦ K(a s)` has derivative `a E z` at `0` (`K` the cumulant
generating function of a bounded `z`). -/
theorem hasDerivAt_cgf_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    HasDerivAt (fun s => cgf z μ (a * s)) (a * ∫ j, z j ∂μ) 0 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd : HasDerivAt (cgf z μ) (∫ j, z j ∂μ) (a * 0) := by
    have := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at this
    rw [mul_zero]
    simpa using this
  have hl : HasDerivAt (fun s : ℝ => a * s) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  exact (hd.comp 0 hl).congr_deriv (by ring)

/-- Galí (2015), p. 171 (**first order**): along `X(j) = exp(x̄ + s z(j))`, the log dispersion
integral is `0` at `s = 0` and has derivative `0` there. -/
theorem log_dispIntegral_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar : ℝ) :
    Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + 0 * z j))) = 0 ∧
      HasDerivAt (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))))
        0 0 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  refine ⟨by rw [log_dispIntegral_family hz hB hε]; simp [cgf_zero], ?_⟩
  have hfun : (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))))
      = fun s => cgf z μ (e * s) - e / (1 - ε) * cgf z μ ((1 - ε) * s) :=
    funext fun s => log_dispIntegral_family hz hB hε e xbar s
  rw [hfun]
  have h := HasDerivAt.sub (hasDerivAt_cgf_mul (μ := μ) hz hB e)
    ((hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).const_mul (e / (1 - ε)))
  refine h.congr_deriv ?_
  have : e / (1 - ε) * ((1 - ε) * ∫ j, z j ∂μ) = e * ∫ j, z j ∂μ := by field_simp
  rw [this, sub_self]

/-- Galí (2015), p. 171 (**`d_w` is zero to first order**): along the family of wage
distributions `w(j) = w̄ + s z(j)`, `d_w(0) = 0` and `d_w'(0) = 0`. -/
theorem dW_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    dW μ α ε (fun j => Real.exp (wbar + 0 * z j)) = 0 ∧
      HasDerivAt (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j))) 0 0 := by
  obtain ⟨h0, hd⟩ := log_dispIntegral_family_first_order (μ := μ) hz hB hε (-ε) wbar
  refine ⟨by rw [dW, wageDisp, h0, mul_zero], ?_⟩
  simpa [dW, wageDisp] using hd.const_mul (1 - α)

/-- Galí (2015), p. 171 (**`d_p` is zero to first order**): along the family of price
distributions `p(i) = p̄ + s z(i)`, `d_p(0) = 0` and `d_p'(0) = 0`. -/
theorem dP_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α pbar : ℝ) :
    dP μ α ε (fun j => Real.exp (pbar + 0 * z j)) = 0 ∧
      HasDerivAt (fun s => dP μ α ε (fun j => Real.exp (pbar + s * z j))) 0 0 := by
  obtain ⟨h0, hd⟩ := log_dispIntegral_family_first_order (μ := μ) hz hB hε (-ε / (1 - α)) pbar
  refine ⟨by rw [dP, priceDisp, h0, mul_zero], ?_⟩
  simpa [dP, priceDisp] using hd.const_mul (1 - α)

/-- Galí (2015), p. 171 (**`(1 − α) n = y − a` to first order**): if along a perturbation `s`
the exact relation `(1 − α) n(s) = y(s) − a(s) + d_w(s) + d_p(s)` holds, with wages
`w(j) = w̄ + s z_w(j)` and prices `p(i) = p̄ + s z_p(i)`, and `y`, `a` are differentiable at
`0`, then `(1 − α) n'(0) = y'(0) − a'(0)`: the dispersion terms drop out. -/
theorem employment_first_order {F : Type*} [MeasurableSpace F] {μF : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μF] {α εp : ℝ} (hεp : εp ≠ 1)
    (hε : ε ≠ 1) {zw : J → ℝ} (hzw : Measurable zw) {Bw : ℝ} (hBw : ∀ j, |zw j| ≤ Bw)
    {zp : F → ℝ} (hzp : Measurable zp) {Bp : ℝ} (hBp : ∀ i, |zp i| ≤ Bp) (wbar pbar : ℝ)
    {n y a : ℝ → ℝ} {y' a' : ℝ} (hy : HasDerivAt y y' 0) (ha : HasDerivAt a a' 0)
    (hn : ∀ s, (1 - α) * n s = y s - a s + dW μ α ε (fun j => Real.exp (wbar + s * zw j))
      + dP μF α εp (fun i => Real.exp (pbar + s * zp i))) :
    HasDerivAt (fun s => (1 - α) * n s) (y' - a') 0 := by
  have hw := (dW_family_first_order (μ := μ) hzw hBw hε α wbar).2
  have hp := (dP_family_first_order (μ := μF) hzp hBp hεp α pbar).2
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub hy ha) hw) hp
  have hfun : (fun s => (1 - α) * n s) = (y - a + fun s => dW μ α ε
      (fun j => Real.exp (wbar + s * zw j))) + fun s => dP μF α εp
      (fun i => Real.exp (pbar + s * zp i)) := by
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    exact hn s
  rw [hfun]
  exact h.congr_deriv (by ring)

end Gali.StickyWagesPrices.LaborAggregation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Wage dispersion to second order and the wage version of Lemma 2

Galí (2015), Chapter 6, p. 171 and Appendix 6.1 (pp. 189–192).

Labour types form a probability space `(J, μ)` (the book's `[0, 1]`, or finitely many types
with weights summing to one). Log wages follow one-parameter families `w(j) = w̄ + s z(j)`
with `z` bounded and measurable, and `W` is the CES wage index (4).

## Main results

* `log_dispIntegral_second_order`: `log ∫ (X(j)/X)^e = (e(e − 1 + ε)/2) var_j x(j) + O(s³)`.
* `dW_second_order` (**p. 171, p. 190**): `d_w = ((1 − α)ε_w/2) var_j w(j) + O(s³)`, and
  `dP_second_order`: `d_p = (ε_p/(2Θ)) var_i p(i) + O(s³)` with `Θ = (1−α)/(1−α+αε_p)`.
* `relLogWage_moments`, `relLogWage_mean_second_order`, `relLogWage_sq_second_order`: p. 189,
  `∫ ŵ(j) dj = ((ε_w − 1)/2) ∫ ŵ(j)² dj + O(s³)` and `∫ ŵ(j)² = var_j w + O(s⁴)`.
* `log_integral_exp_second_order` (p. 189): `n + n²/2 = ∫ n(j) + ½ ∫ n(j)² + O(s³)` when
  `N = ∫ N(j) dj`.
* `integral_sq_employment` (p. 189): with labour demand (3) at every type, **exactly**
  `∫ n(j)² = n² + ε_w² var_j w + (d² − n²)` with `d − n = O(s²)`, hence
  `∫ n(j)² = n² + ε_w² var_j w + O(s³)` whenever aggregate employment `n = O(s)`
  (`integral_sq_employment_second_order`).
* **Lemma 2 for wages** (App. 6.1, p. 192), exact in the change of the cross-sectional mean of
  log wages `m^w`: `wageMix_var_meanChange`
  (`var_t = θ_w var_{t−1} + (θ_w/(1−θ_w))(Δm^w_t)²`), `wage_lemma2_calvo_inherited`,
  `wage_lemma2_calvo`
  (`∑ βᵗ var_j w_t(j) = θ_w/((1−βθ_w)(1−θ_w)) ∑ βᵗ (Δm^w_t)²`, convergence proved).
* `wageInflation_sub_meanChange`, `wageInflation_sq_sub_meanChange_sq`: `π^w = Δm^w + O(s²)`
  and `(π^w)² = (Δm^w)² + O(s³)`.

The Calvo law of motion of the wage cross-section used here is derived from the type-level
Calvo lottery in `WageInflation` (`wage_dist_law_of_motion`). The proofs follow the
Chapter 3 project (`PriceDispersion.lean`) and the Chapter 4 project (`Welfare.lean`), with
prices replaced by wages.
-/

namespace Gali.StickyWagesPrices.WageDispersion

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.StickyWagesPrices.LaborAggregation

variable {J : Type*} [MeasurableSpace J]

/-- Galí (2015), App. 6.1, p. 189: the cross-sectional variance
`var_j w(j) = ∫ (w(j) − ∫ w)² dj`. -/
noncomputable def crossVar (μ : Measure J) (w : J → ℝ) : ℝ :=
  ∫ j, (w j - ∫ i, w i ∂μ) ^ 2 ∂μ

/-- Galí (2015), p. 171 (ch. 3, p. 60): `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

variable {μ : Measure J} {ε : ℝ}

/-! ### Orders of magnitude -/

/-- Galí (2015), App. 6.1, pp. 188–190 (bookkeeping of orders): `f = O(sᵃ)` and `g = O(sᵇ)`
give `f g = O(sᵃ⁺ᵇ)` (restated from the Chapter 4 project). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Galí (2015), App. 6.1, p. 189 ("third or higher order"): `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b`
(restated from the Chapter 4 project). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- Galí (2015), App. 6.1, p. 189: a monomial `c sᵃ` is `O(sᵃ)`. -/
theorem monomial_isBigO (c : ℝ) (a : ℕ) : (fun s : ℝ => c * s ^ a) =O[𝓝 0] fun s => s ^ a :=
  (isBigO_refl _ _).const_mul_left c

/-! ### Taylor expansion of the cumulant-generating function -/

/-- Galí (2015), App. 6.1, p. 189 (via ch. 3, App. 3.4): **second-order Taylor expansion of
the cumulant-generating function** of a bounded `z`, `K(u) = (E z)u + (var z/2)u² + O(u³)`
(restated from the Chapter 3 project). -/
theorem cgf_taylor [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) :
    (fun u => cgf z μ u - (∫ j, z j ∂μ) * u - (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      =O[𝓝 0] fun u => u ^ 3 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have hAn : AnalyticOnNhd ℝ (cgf z μ) Set.univ := by
    have := analyticOnNhd_cgf (X := z) (μ := μ)
    rwa [hint] at this
  have hCD : ContDiff ℝ 3 (cgf z μ) := hAn.contDiff
  have hT := taylor_isLittleO_univ (x₀ := 0) hCD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd1 : deriv (cgf z μ) 0 = ∫ j, z j ∂μ := by
    rw [deriv_cgf_zero h0]
    simp
  have hd2 : iteratedDeriv 2 (cgf z μ) 0 = ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
    rw [iteratedDeriv_two_cgf_eq_integral h0, hd1, mgf_zero]
    simp
  have heq : (fun u => cgf z μ u - (∫ j, z j ∂μ) * u -
      (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
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
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 6.1, p. 189: the Taylor remainder of `K` along a ray,
`K(a s) − (E z)(a s) − (var z/2)(a s)² = O(s³)` (restated from the Chapter 3 project). -/
theorem cgf_taylor_comp [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    (fun s => cgf z μ (a * s) - (∫ j, z j ∂μ) * (a * s) -
      (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * (a * s) ^ 2) =O[𝓝 0] fun s => s ^ 3 := by
  have hR := cgf_taylor (μ := μ) hz hB
  have ht : Tendsto (fun s : ℝ => a * s) (𝓝 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul a
    simpa using this
  refine (hR.comp_tendsto ht).trans ?_
  have : ((fun u : ℝ => u ^ 3) ∘ fun s => a * s) = fun s => a ^ 3 * s ^ 3 := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [this]
  exact (isBigO_refl _ _).const_mul_left _

/-- Galí (2015), App. 6.1, p. 189: a bounded measurable `z` is integrable, and so is
`(z − E z)²`. -/
theorem integrable_bounded [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) :
    Integrable z μ ∧ Integrable (fun j => (z j - ∫ i, z i ∂μ) ^ 2) μ := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)
  refine ⟨hzI, ?_⟩
  set m := ∫ i, z i ∂μ
  refine Integrable.of_bound ((hz.sub measurable_const).pow_const 2).aestronglyMeasurable
    ((B + |m|) ^ 2) (Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  have h1 : |z j - m| ≤ B + |m| := (abs_sub _ _).trans (by linarith [hB j])
  calc (z j - m) ^ 2 = |z j - m| ^ 2 := (sq_abs _).symm
    _ ≤ (B + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- Galí (2015), App. 6.1, p. 189: the cross-sectional variance of `w(j) = w̄ + s z(j)` is
`s² var z` (restated from the Chapter 3 project). -/
theorem crossVar_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (wbar s : ℝ) :
    crossVar μ (fun j => wbar + s * z j) = s ^ 2 * ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
  have hzI := (integrable_bounded (μ := μ) hz hB).1
  have hmean : ∫ j, (wbar + s * z j) ∂μ = wbar + s * ∫ j, z j ∂μ := by
    rw [integral_add (integrable_const _) (hzI.const_mul s), integral_const, integral_const_mul]
    simp
  unfold crossVar
  beta_reduce
  rw [hmean]
  have hpt : ∀ j, (wbar + s * z j - (wbar + s * ∫ i, z i ∂μ)) ^ 2
      = s ^ 2 * (z j - ∫ i, z i ∂μ) ^ 2 := fun j => by ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Galí (2015), App. 6.1, p. 189: along `w(j) = w̄ + s z(j)`, `var_j w = O(s²)`. -/
theorem crossVar_family_isBigO [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (wbar : ℝ) :
    (fun s => crossVar μ (fun j => wbar + s * z j)) =O[𝓝 0] fun s => s ^ 2 := by
  have : (fun s => crossVar μ (fun j => wbar + s * z j))
      = fun s => (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) * s ^ 2 := by
    funext s
    rw [crossVar_family hz hB, mul_comm]
  rw [this]
  exact monomial_isBigO _ 2

/-! ### Dispersion to second order (p. 171, App. 6.1 p. 190) -/

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (general form): along `x(j) = x̄ + s z(j)`,
`log ∫ (X(j)/X)^e dj = (e (e − 1 + ε)/2) var_j x(j) + O(s³)`. -/
theorem log_dispIntegral_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar : ℝ) :
    (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))) -
        e * (e - 1 + ε) / 2 * crossVar μ (fun j => xbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hcomp := cgf_taylor_comp (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))) -
        e * (e - 1 + ε) / 2 * crossVar μ (fun j => xbar + s * z j))
      = fun s => (cgf z μ (e * s) - (∫ j, z j ∂μ) * (e * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * (e * s) ^ 2) +
        (-(e / (1 - ε))) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [log_dispIntegral_family hz hB hε, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (hcomp e).add ((hcomp _).const_mul_left _)

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (**`d_w ≃ ((1 − α)ε_w/2) var_j w(j)`**): along
the family of wage distributions `w(j) = w̄ + s z(j)` (with `W` its CES index),
`d_w(s) = ((1 − α) ε_w/2) var_j w(j) + O(s³)`. -/
theorem dW_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j)) -
        (1 - α) * ε / 2 * crossVar μ (fun j => wbar + s * z j)) =O[𝓝 0] fun s => s ^ 3 := by
  have h := (log_dispIntegral_second_order (μ := μ) hz hB hε (-ε) wbar).const_mul_left (1 - α)
  refine h.congr_left fun s => ?_
  simp only [dW, wageDisp]
  ring

/-- Galí (2015), p. 171 (**`d_p ≃ (ε_p/(2Θ)) var_i p(i)`**, as in ch. 4, App. 4.1): along
`p(i) = p̄ + s z(i)`, `d_p(s) = (ε_p/(2Θ)) var_i p(i) + O(s³)`, `Θ = (1−α)/(1−α+αε_p)`. -/
theorem dP_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : 1 < ε) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dP μ α ε (fun j => Real.exp (pbar + s * z j)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun j => pbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubα : (1 : ℝ) - α ≠ 0 := by linarith
  have hden : 1 - α + α * ε ≠ 0 := by nlinarith
  have h := (log_dispIntegral_second_order (μ := μ) hz hB hε.ne' (-ε / (1 - α)) pbar
    ).const_mul_left (1 - α)
  refine h.congr_left fun s => ?_
  simp only [dP, priceDisp, bigTheta]
  field_simp
  ring

/-- Galí (2015), p. 171: along the wage family, `d_w = O(s²)`. -/
theorem dW_isBigO_sq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j))) =O[𝓝 0] fun s => s ^ 2 := by
  have h := (bigO_weaken (by norm_num : 2 ≤ 3) (dW_second_order (μ := μ) hz hB hε α wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz hB wbar).const_mul_left ((1 - α) * ε / 2))
  simpa using h

/-- Galí (2015), p. 171: along the wage family, `log Δ_w = O(s²)`. -/
theorem log_wageDisp_isBigO_sq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))))
      =O[𝓝 0] fun s => s ^ 2 := by
  have h := dW_isBigO_sq (μ := μ) hz hB hε 0 wbar
  simpa [dW] using h

/-! ### Relative log wages (App. 6.1, p. 189) -/

/-- Galí (2015), App. 6.1, p. 189: the relative log wage `ŵ(j) = w(j) − w` along the family
`w(j) = w̄ + s z(j)`, with `w` the log CES wage index. -/
noncomputable def relLogWage (μ : Measure J) (ε : ℝ) (z : J → ℝ) (wbar s : ℝ) (j : J) : ℝ :=
  wbar + s * z j - Real.log (cesIndex μ ε (fun i => Real.exp (wbar + s * z i)))

/-- Galí (2015), App. 6.1, p. 189: the mean of `ŵ`,
`E_j ŵ = s E z − K((1 − ε)s)/(1 − ε)`. -/
noncomputable def relLogWageMean (μ : Measure J) (ε : ℝ) (z : J → ℝ) (s : ℝ) : ℝ :=
  s * (∫ j, z j ∂μ) - cgf z μ ((1 - ε) * s) / (1 - ε)

/-- Galí (2015), App. 6.1, p. 189 (exact): `ŵ(j) = s (z(j) − E z) + E_j ŵ`. -/
theorem relLogWage_eq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) (j : J) :
    relLogWage μ ε z wbar s j = s * (z j - ∫ i, z i ∂μ) + relLogWageMean μ ε z s := by
  rw [relLogWage, cesIndex_family hz hB hε, Real.log_exp, relLogWageMean]
  ring

/-- Galí (2015), App. 6.1, p. 189: `∫ (d − a (z − E z))² = d² + a² var z` for bounded `z`. -/
theorem integral_sq_affine [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (d a : ℝ) :
    ∫ j, (d - a * (z j - ∫ i, z i ∂μ)) ^ 2 ∂μ
      = d ^ 2 + a ^ 2 * ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
  obtain ⟨hzI, hz2⟩ := integrable_bounded (μ := μ) hz hB
  set m := ∫ i, z i ∂μ
  have hzc : Integrable (fun j => z j - m) μ := hzI.sub (integrable_const m)
  have hzm : ∫ j, (z j - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  have hsq : ∀ j, (d - a * (z j - m)) ^ 2
      = d ^ 2 + (a ^ 2 * (z j - m) ^ 2 + (-2 * a * d) * (z j - m)) := fun j => by ring
  simp_rw [hsq]
  have e1 := integral_add (μ := μ) (f := fun _ => d ^ 2)
    (g := fun j => a ^ 2 * (z j - m) ^ 2 + -2 * a * d * (z j - m)) (integrable_const _)
    ((hz2.const_mul (a ^ 2)).add (hzc.const_mul (-2 * a * d)))
  have e2 := integral_add (μ := μ) (f := fun j => a ^ 2 * (z j - m) ^ 2)
    (g := fun j => -2 * a * d * (z j - m)) (hz2.const_mul (a ^ 2)) (hzc.const_mul (-2 * a * d))
  rw [e1, e2, integral_const_mul, integral_const_mul, hzm]
  simp

/-- Galí (2015), App. 6.1, p. 189 (exact moments of `ŵ`): `E_j ŵ = relLogWageMean` and
`E_j ŵ² = var_j w + (E_j ŵ)²`. -/
theorem relLogWage_moments [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) :
    ∫ j, relLogWage μ ε z wbar s j ∂μ = relLogWageMean μ ε z s ∧
      ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ
        = crossVar μ (fun j => wbar + s * z j) + relLogWageMean μ ε z s ^ 2 := by
  obtain ⟨hzI, -⟩ := integrable_bounded (μ := μ) hz hB
  simp_rw [relLogWage_eq hz hB hε wbar s]
  set m := ∫ i, z i ∂μ
  have hzm : ∫ j, (z j - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  refine ⟨?_, ?_⟩
  · have e1 := integral_add (μ := μ) (f := fun j => s * (z j - m))
      (g := fun _ => relLogWageMean μ ε z s) ((hzI.sub (integrable_const m)).const_mul s)
      (integrable_const _)
    rw [e1, integral_const_mul, hzm]
    simp
  · have := integral_sq_affine (μ := μ) hz hB (relLogWageMean μ ε z s) (-s)
    have e1 : ∀ j, (s * (z j - m) + relLogWageMean μ ε z s) ^ 2
        = (relLogWageMean μ ε z s - -s * (z j - m)) ^ 2 := fun j => by ring
    simp_rw [e1]
    rw [this, crossVar_family hz hB]
    ring

/-- Galí (2015), App. 6.1, p. 189: `E_j ŵ = O(s²)`. -/
theorem relLogWageMean_isBigO [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) :
    (fun s => relLogWageMean μ ε z s) =O[𝓝 0] fun s => s ^ 2 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have : (fun s => relLogWageMean μ ε z s)
      = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
        (-((1 - ε) * (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2)) * s ^ 2 := by
    funext s
    rw [relLogWageMean]
    field_simp
    ring
  rw [this]
  exact ((bigO_weaken (by norm_num : 2 ≤ 3) hR).const_mul_left _).add (monomial_isBigO _ 2)

/-- Galí (2015), App. 6.1, p. 189 (**`∫ ŵ(j) dj = ((ε_w − 1)/2) var_j w` is of second order**):
`E_j ŵ − ((ε − 1)/2) E_j ŵ² = O(s³)`. -/
theorem relLogWage_mean_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => ∫ j, relLogWage μ ε z wbar s j ∂μ -
        (ε - 1) / 2 * ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ) =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  have hE2 := bigO_weaken (by norm_num : 3 ≤ 2 + 2) (bigO_mul hE hE)
  have heq : (fun s => ∫ j, relLogWage μ ε z wbar s j ∂μ -
        (ε - 1) / 2 * ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ)
      = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
        (-((ε - 1) / 2)) * (relLogWageMean μ ε z s * relLogWageMean μ ε z s) := by
    funext s
    rw [(relLogWage_moments hz hB hε wbar s).1, (relLogWage_moments hz hB hε wbar s).2,
      crossVar_family hz hB, relLogWageMean]
    field_simp
    ring
  rw [heq]
  exact (hR.const_mul_left _).add (hE2.const_mul_left _)

/-- Galí (2015), App. 6.1, p. 189: `∫ ŵ(j)² dj = var_j w + O(s⁴)`. -/
theorem relLogWage_sq_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ - crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 4 := by
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  refine (bigO_mul hE hE).congr_left fun s => ?_
  rw [(relLogWage_moments hz hB hε wbar s).2]
  ring

/-! ### Aggregate employment and the square of individual employment (p. 189) -/

/-- Galí (2015), App. 6.1, p. 189: with `N = ∫ N(j) dj` and `n = log N`, `n(j) = log N(j)`
(log deviations from a steady state normalised to one), the family `n(j) = s ζ(j)` gives
`n = K_ζ(s)` and `n + n²/2 = ∫ n(j) + ½ ∫ n(j)² + O(s³)`. -/
theorem log_integral_exp_second_order [IsProbabilityMeasure μ] {ζ : J → ℝ}
    (hζ : Measurable ζ) {B : ℝ} (hB : ∀ j, |ζ j| ≤ B) :
    (fun s => (Real.log (∫ j, Real.exp (s * ζ j) ∂μ) +
        Real.log (∫ j, Real.exp (s * ζ j) ∂μ) ^ 2 / 2) -
        (∫ j, s * ζ j ∂μ + (∫ j, (s * ζ j) ^ 2 ∂μ) / 2)) =O[𝓝 0] fun s => s ^ 3 := by
  obtain ⟨hζI, hζ2⟩ := integrable_bounded (μ := μ) hζ hB
  set m := ∫ j, ζ j ∂μ
  set v := ∫ j, (ζ j - m) ^ 2 ∂μ
  have hR : (fun s => cgf ζ μ s - m * s - v / 2 * s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
    cgf_taylor (μ := μ) hζ hB
  have hK : ∀ s, Real.log (∫ j, Real.exp (s * ζ j) ∂μ) = cgf ζ μ s := fun s => rfl
  have hsq : ∀ s, ∫ j, (s * ζ j) ^ 2 ∂μ = s ^ 2 * (v + m ^ 2) := by
    intro s
    have h1 : ∀ j, (s * ζ j) ^ 2 = s ^ 2 * ((ζ j - m) ^ 2 + 2 * m * (ζ j - m) + m ^ 2) :=
      fun j => by ring
    have hzc : Integrable (fun j => ζ j - m) μ := hζI.sub (integrable_const m)
    have hzm : ∫ j, (ζ j - m) ∂μ = 0 := by
      rw [integral_sub hζI (integrable_const m)]
      simp [m]
    simp_rw [h1]
    have e1 := integral_add (μ := μ) (f := fun j => (ζ j - m) ^ 2 + 2 * m * (ζ j - m))
      (g := fun _ => m ^ 2) (hζ2.add (hzc.const_mul (2 * m))) (integrable_const _)
    have e2 := integral_add (μ := μ) (f := fun j => (ζ j - m) ^ 2)
      (g := fun j => 2 * m * (ζ j - m)) hζ2 (hzc.const_mul (2 * m))
    rw [integral_const_mul, e1, e2, integral_const_mul, hzm]
    simp [v]
  have hlin : ∀ s, ∫ j, s * ζ j ∂μ = s * m := fun s => integral_const_mul s ζ
  -- `K − m s = O(s²)` and `K + m s = O(s)`
  have hA : (fun s => cgf ζ μ s - m * s) =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hR).add (monomial_isBigO (v / 2) 2)).congr_left
      fun s => by ring
  have hB' : (fun s => cgf ζ μ s + m * s) =O[𝓝 0] fun s => s ^ 1 :=
    ((bigO_weaken (by norm_num : 1 ≤ 2) hA).add (monomial_isBigO (2 * m) 1)).congr_left
      fun s => by ring
  have hprod := bigO_mul hA hB'
  refine (hR.add (hprod.const_mul_left (1 / 2))).congr_left fun s => ?_
  rw [hK, hsq, hlin]
  ring

/-- Galí (2015), App. 6.1, p. 189 (log of labour demand (3), **exact**): with
`N(j) = (W(j)/W)^{−ε_w} N^d`, `log N(j) − log ∫ N(i) di = −ε_w ŵ(j) − log Δ_w`, where
`ŵ(j) = log W(j) − log W`. -/
theorem log_laborDemand_sub [IsProbabilityMeasure μ] {W : J → ℝ} (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) {Nd : ℝ} (hNd : 0 < Nd)
    (hDw : 0 < wageDisp μ ε W) (j : J) :
    Real.log (laborDemand μ ε W Nd j) - Real.log (∫ i, laborDemand μ ε W Nd i ∂μ)
      = -ε * (Real.log (W j) - Real.log (cesIndex μ ε W)) - Real.log (wageDisp μ ε W) := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hW j) (1 - ε)) hWi
  have hI := cesIndex_pos hpos
  have hint : ∫ i, laborDemand μ ε W Nd i ∂μ = wageDisp μ ε W * Nd := by
    simp only [laborDemand]
    rw [integral_mul_const, wageDisp, dispIntegral]
  have hr : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
  rw [hint, laborDemand, Real.log_mul (Real.rpow_pos_of_pos hr _).ne' hNd.ne',
    Real.log_rpow hr, Real.log_div (hW j).ne' hI.ne', Real.log_mul hDw.ne' hNd.ne']
  ring

/-- Galí (2015), App. 6.1, p. 189 (**exact form of `∫ n(j)² = n² + ε_w² var_j w`**). Along the
wage family `w(j) = w̄ + s z(j)`, let every type be on labour demand (3) with labour index
`N^d > 0`, let `n(j) = log N(j) − log N̄` and `n = log ∫ N(j) dj − log N̄` (deviations from a
steady state `N̄ > 0`). Then exactly `∫ n(j)² dj = (n − log Δ_w − ε_w E_j ŵ)² + ε_w² var_j w`. -/
theorem integral_sq_employment [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) {Nd Nbar : ℝ} (hNd : 0 < Nd)
    (hDw : 0 < wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) :
    ∫ j, (Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd j) -
        Real.log Nbar) ^ 2 ∂μ
      = (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd i ∂μ) -
          Real.log Nbar - Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) -
          ε * relLogWageMean μ ε z s) ^ 2 + ε ^ 2 * crossVar μ (fun j => wbar + s * z j) := by
  have hWi : Integrable (fun j => Real.exp (wbar + s * z j) ^ (1 - ε)) μ := by
    have : (fun j => Real.exp (wbar + s * z j) ^ (1 - ε))
        = fun j => Real.exp ((1 - ε) * wbar) * Real.exp ((1 - ε) * s * z j) := by
      funext j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact (integrable_exp_mul hz hB _).const_mul _
  set n := Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd i ∂μ) -
    Real.log Nbar
  set δ := Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j)))
  have hpt : ∀ j, Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd j) -
      Real.log Nbar = (n - δ - ε * relLogWageMean μ ε z s) - ε * s * (z j - ∫ i, z i ∂μ) := by
    intro j
    have h := log_laborDemand_sub (fun j => Real.exp_pos (wbar + s * z j)) hWi hNd hDw j
    have hw := relLogWage_eq (μ := μ) hz hB hε wbar s j
    rw [relLogWage] at hw
    rw [Real.log_exp] at h
    simp only [n, δ]
    linear_combination h + (-ε) * hw
  simp_rw [hpt]
  rw [integral_sq_affine hz hB, crossVar_family hz hB]
  ring

/-- Galí (2015), App. 6.1, p. 189 (**`∫ n(j)² = n² + ε_w² var_j w` up to third order**): in the
setting of `integral_sq_employment`, if aggregate employment is first order along the
perturbation (`n(s) = O(s)`) then `∫ n(j)² − n² − ε_w² var_j w = O(s³)`. -/
theorem integral_sq_employment_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ)
    {Nd : ℝ → ℝ} (hNd : ∀ s, 0 < Nd s) {Nbar : ℝ}
    (hDw : ∀ s, 0 < wageDisp μ ε (fun j => Real.exp (wbar + s * z j)))
    (hn : (fun s => Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i))
        (Nd s) i ∂μ) - Real.log Nbar) =O[𝓝 0] fun s => s ^ 1) :
    (fun s => ∫ j, (Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) (Nd s) j) -
        Real.log Nbar) ^ 2 ∂μ -
      (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) (Nd s) i ∂μ) -
        Real.log Nbar) ^ 2 - ε ^ 2 * crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hδ := log_wageDisp_isBigO_sq (μ := μ) hz hB hε wbar
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  have hD : (fun s => Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) +
      ε * relLogWageMean μ ε z s) =O[𝓝 0] fun s => s ^ 2 := hδ.add (hE.const_mul_left ε)
  have hS : (fun s => 2 * (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i))
        (Nd s) i ∂μ) - Real.log Nbar) - (Real.log (wageDisp μ ε (fun j => Real.exp
        (wbar + s * z j))) + ε * relLogWageMean μ ε z s)) =O[𝓝 0] fun s => s ^ 1 :=
    (hn.const_mul_left 2).sub (bigO_weaken (by norm_num : 1 ≤ 2) hD)
  refine ((bigO_mul hD hS).neg_left).congr_left fun s => ?_
  rw [integral_sq_employment hz hB hε wbar s (hNd s) (hDw s)]
  ring

/-! ### Lemma 2 for wages: the exact Calvo cross-section (App. 6.1, p. 192) -/

/-- Galí (2015), App. 6.1, p. 192 (setting of Lemma 2): an admissible cross-sectional
distribution of log wages is a probability measure with finite first and second moments. -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν

/-- Galí (2015), App. 6.1, p. 192: the cross-sectional mean of log wages `m^w = ∫ w ν(dw)`. -/
noncomputable def crossMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

/-- Galí (2015), App. 6.1, p. 192: the cross-sectional variance of log wages `var_j w(j)`. -/
noncomputable def crossVarDist (ν : Measure ℝ) : ℝ := ∫ x, (x - crossMean ν) ^ 2 ∂ν

/-- Galí (2015), §6.1.2.2, p. 169 and App. 6.1, p. 192: the Calvo law of motion of the
cross-section of log wages, `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{w*_t}` (derived from the
type-level Calvo lottery in `WageInflation`). -/
noncomputable def wageMix (θ : ℝ) (ν : Measure ℝ) (w : ℝ) : Measure ℝ :=
  ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac w

/-- Galí (2015), App. 6.1, p. 192 (restated from the Chapter 4 project): integrating against
`θ ν + (1 − θ) δ_w` gives `θ ∫ f dν + (1 − θ) f(w)`. -/
theorem integral_wageMix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(wageMix θ ν w) = θ * ∫ x, f x ∂ν + (1 - θ) * f w := by
  have hd : Integrable f (Measure.dirac w) := integrable_dirac (by simp)
  rw [wageMix, integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), App. 6.1, p. 192: `var = E w² − (E w)²` for an admissible cross-section. -/
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

/-- Galí (2015), App. 6.1, p. 192: the Calvo law of motion preserves admissibility. -/
theorem wageMix_good {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) : GoodDist (wageMix θ ν w) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [wageMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (hi2.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Galí (2015), App. 6.1, p. 192 (exact): the mean log wage moves as
`m^w_t = θ_w m^w_{t−1} + (1 − θ_w) w*_t`, i.e. `Δm^w_t = (1 − θ_w)(w*_t − m^w_{t−1})`. -/
theorem wageMix_mean {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) : crossMean (wageMix θ ν w) = θ * crossMean ν + (1 - θ) * w := by
  unfold crossMean
  exact integral_wageMix h0 h1 w hg.2.1

/-- Galí (2015), App. 6.1, p. 192 (**exact variance recursion**):
`var_t = θ_w var_{t−1} + θ_w(1 − θ_w)(w*_t − m^w_{t−1})²`. -/
theorem wageMix_var {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (wageMix θ ν w)
      = θ * crossVarDist ν + θ * (1 - θ) * (w - crossMean ν) ^ 2 := by
  rw [crossVarDist_eq (wageMix_good h0 h1 w hg), crossVarDist_eq hg, wageMix_mean h0 h1 w hg]
  have h2 : ∫ x, x ^ 2 ∂(wageMix θ ν w) = θ * ∫ x, x ^ 2 ∂ν + (1 - θ) * w ^ 2 :=
    integral_wageMix h0 h1 w hg.2.2
  rw [h2]
  ring

/-- Galí (2015), App. 6.1, p. 192 (**exact, in terms of the change in the mean**): for
`θ_w < 1`, `var_t = θ_w var_{t−1} + (θ_w/(1 − θ_w)) (Δm^w_t)²`. -/
theorem wageMix_var_meanChange {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (w : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (wageMix θ ν w)
      = θ * crossVarDist ν + θ / (1 - θ) * (crossMean (wageMix θ ν w) - crossMean ν) ^ 2 := by
  rw [wageMix_var h0 h1.le w hg, wageMix_mean h0 h1.le w hg]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 6.1, p. 192: along a Calvo sequence `ν_{t+1} = θ_w ν_t + (1−θ_w) δ_{w*_t}`
from an admissible `ν_0`, every cross-section is admissible. -/
theorem wage_good {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0)) :
    ∀ t, GoodDist (ν t) := by
  intro t
  induction t with
  | zero => exact hg
  | succ t ih =>
    rw [hν t]
    exact wageMix_good h0 h1 _ ih

/-- Galí (2015), App. 6.1, p. 192 (**exact recursion along the Calvo sequence**; `ν_0` is the
inherited cross-section): `var_{t+1} = θ_w var_t + (θ_w/(1−θ_w))(m^w_{t+1} − m^w_t)²`. -/
theorem wage_var_recursion {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ν : ℕ → Measure ℝ}
    {wstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0))
    (t : ℕ) :
    crossVarDist (ν (t + 1))
      = θ * crossVarDist (ν t) + θ / (1 - θ) * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2 := by
  rw [hν t]
  exact wageMix_var_meanChange h0 h1 _ (wage_good h0 h1.le hν hg t)

/-- Galí (2015), App. 6.1, p. 192 (Lemma 2, partial sums; restated from the Chapter 4 project):
if `V_{t+1} = θ V_t + c q_t`, then
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

/-- Galí (2015), App. 6.1, p. 192: a variance recursion `V_{t+1} = θ V_t + c q_t` with
nonnegative data stays nonnegative. -/
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

/-- Galí (2015), App. 6.1, p. 192 (**Lemma 2, general form, exact**; restated from the
Chapter 4 project): if `V_{t+1} = θ V_t + c q_t` with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`,
`q ≥ 0` and `∑ βᵗ q_t` summable, then `∑ βᵗ V_{t+1}` converges to
`(θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. -/
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

/-- Galí (2015), App. 6.1, p. 192 (**Lemma 2 as used there, exact**): with no inherited
dispersion (`V_0 = 0`) and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
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

/-- Galí (2015), App. 6.1, p. 192 (**wage Lemma 2 with inherited dispersion, exact in
`Δm^w`**): along `ν_{t+1} = θ_w ν_t + (1 − θ_w) δ_{w*_t}` from an admissible `ν_0`,
`∑ βᵗ var_j w_{t+1}(j) = (θ_w var ν_0 + (θ_w/(1−θ_w)) ∑ βᵗ (Δm^w_t)²)/(1 − βθ_w)`. -/
theorem wage_lemma2_calvo_inherited {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0))
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      ((θ * crossVarDist (ν 0) + θ / (1 - θ) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) / (1 - β * θ)) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hV0 : 0 ≤ crossVarDist (ν 0) := integral_nonneg fun x => sq_nonneg _
  have hc : (0 : ℝ) ≤ θ / (1 - θ) := div_nonneg hθ0 (by linarith)
  exact lemma2_hasSum (c := θ / (1 - θ)) (V := fun t => crossVarDist (ν t)) hθ0 hβ0 hβθ hc hV0
    (fun t => sq_nonneg _) (wage_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), App. 6.1, p. 192 (**wage Lemma 2, exact in `Δm^w`**): with no inherited
wage dispersion, `∑ βᵗ var_j w_t(j) = θ_w/((1 − βθ_w)(1 − θ_w)) ∑ βᵗ (Δm^w_t)²`. -/
theorem wage_lemma2_calvo {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      (θ / ((1 - β * θ) * (1 - θ)) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :=
  lemma2 (V := fun t => crossVarDist (ν t))
    (q := fun t => (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) hθ0 hθ1 hβ0 hβ1 hV0
    (fun _ => sq_nonneg _) (wage_var_recursion hθ0 hθ1 hν hg) hQ

/-! ### `Δm^w = π^w` to first order (App. 6.1, p. 192) -/

/-- Galí (2015), App. 6.1, p. 192 (the log wage index versus the mean): along
`w(j) = w̄ + s z(j)`, `log W(s) = E_j w(j) + ((1 − ε)/2) var_j w(j) + O(s³)`. -/
theorem logWageIndex_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) -
        (wbar + s * ∫ j, z j ∂μ) - (1 - ε) / 2 * crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) -
        (wbar + s * ∫ j, z j ∂μ) - (1 - ε) / 2 * crossVar μ (fun j => wbar + s * z j))
      = fun s => (1 - ε)⁻¹ * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [cesIndex_family hz hB hε, Real.log_exp, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (cgf_taylor_comp hz hB _).const_mul_left _

/-- Galí (2015), App. 6.1, p. 192 (**`Δm^w_t = π^w_t` to first order**): for log-wage families
`w_k(j) = w̄ + s z_k(j)` at two consecutive dates, wage inflation `π^w = log W_1 − log W_0`
(CES indices) and the change in the cross-sectional mean `Δm^w = E w_1 − E w_0` differ by
`O(s²)`. -/
theorem wageInflation_sub_meanChange [IsProbabilityMeasure μ] {z₀ z₁ : J → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ j, |z₀ j| ≤ B₀)
    (hB₁ : ∀ j, |z₁ j| ≤ B₁) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₁ j))) -
        Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₀ j)))) -
        ((wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ))) =O[𝓝 0] fun s => s ^ 2 := by
  have e₁ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logWageIndex_second_order (μ := μ) hz₁ hB₁ hε wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz₁ hB₁ wbar).const_mul_left ((1 - ε) / 2))
  have e₀ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logWageIndex_second_order (μ := μ) hz₀ hB₀ hε wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz₀ hB₀ wbar).const_mul_left ((1 - ε) / 2))
  refine (e₁.sub e₀).congr_left fun s => ?_
  ring

/-- Galí (2015), App. 6.1, p. 192 (**`(π^w_t)² = (Δm^w_t)² + O(s³)`**): the squares of wage
inflation and of the change in the mean log wage agree to second order, so the wage Lemma 2
(exact in `Δm^w`) holds with `π^w` to second order. -/
theorem wageInflation_sq_sub_meanChange_sq [IsProbabilityMeasure μ] {z₀ z₁ : J → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ j, |z₀ j| ≤ B₀)
    (hB₁ : ∀ j, |z₁ j| ≤ B₁) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₁ j))) -
        Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₀ j)))) ^ 2 -
        ((wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ)) ^ 2) =O[𝓝 0]
      fun s => s ^ 3 := by
  have hD := wageInflation_sub_meanChange (μ := μ) hz₀ hz₁ hB₀ hB₁ hε wbar
  have hm : (fun s => (wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ)) =O[𝓝 0]
      fun s => s ^ 1 :=
    (monomial_isBigO ((∫ j, z₁ j ∂μ) - ∫ j, z₀ j ∂μ) 1).congr_left fun s => by ring
  have hsum := (bigO_weaken (by norm_num : 1 ≤ 2) hD).add (hm.const_mul_left 2)
  refine (bigO_mul hD hsum).congr_left fun s => ?_
  ring

end Gali.StickyWagesPrices.WageDispersion

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Wage setting

Galí (2015), Chapter 6, §6.1.2.1 (pp. 167–169), eqs. (10)–(13).

A union resetting the wage of its labour type at `t` chooses `W*` to maximise the genuine
infinite discounted sum (10),
`∑ₖ (βθ_w)ᵏ E_t[(C_{t+k}^{−σ} (W*/P_{t+k}) N_{t+k|t} − N_{t+k|t}^{1+φ}/(1+φ)) Z_{t+k}]`,
subject to labour demand `N_{t+k|t} = (W*/W_{t+k})^{−ε_w} N^d_{t+k}` (p. 168). Expectations are
an arbitrary `ExpectationSystem`. Processes are indexed by the horizon `k` (date `t + k`).

## Structure

The union's problem is an instance of a generic Calvo reset problem
`∑ₖ θᵏ E_t[Q_k (x Y_k(x) − Ψ_k(Y_k(x)))]`, `Y_k(x) = (x/P_k)^{−ε} C_k`, with discount factor
`Q_k = βᵏ Z C^{−σ}/P`, "price index" `W`, "demand shifter" `N^d`, and nominal cost
`Ψ_k(y) = P C^σ y^{1+φ}/(1+φ)` (the money value of the disutility of work, so `Q Ψ = βᵏ Z
y^{1+φ}/(1+φ)`). The generic theory (differentiation under `E_t` and under the infinite sum,
necessity and — with convex `Ψ` — sufficiency and uniqueness, regularity from primitives, the
flexible limit, the steady state and the exact linearisation) is restated from the Chapter 3
project (`ResetPrice.lean`), with eq. numbers of Chapter 6.

## Main results

* `unionObjective_eq`, `E_tsum_unionObjective`: (10) as a generic reset objective, and with
  `E_t` outside the sum as printed.
* `union_hasDerivAt`, `union_foc_of_isLocalMax`: the derivative of (10) is
  `((1 − ε_w)/W*) × LHS of (11)`; **(11) is necessary**.
* `union_isMaxOn_iff_foc`: **(11) is necessary and sufficient**, and the maximiser is unique
  (strict), under `UnionPrimitives` alone: `φ ≥ 0` makes the disutility convex in hours, and
  the objective is then strictly increasing below and strictly decreasing above any root of
  (11) (it is unimodal; global concavity in `W*` is not needed and not claimed).
* `union_flexible`, `flexible_wage_index`: `θ_w = 0 ⇒ W*/P = M_w MRS_{t|t}`, `W* = W`,
  `MRS_{t|t} = MRS_t`.
* `union_steadyState_foc_iff`: zero-inflation steady state, `W/P = M_w MRS`.
* `foc11_eq_focLHS`, `hasDerivAt_focLHS_path`, `eq12_iff`: (12) is exactly the vanishing of the
  derivative of (11) at the steady state along any bounded perturbation.
* `log_mrsReset`, `mrs_correction_first_order`: `mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w* − w_{t+k})
  − φ log Δ_w` exactly, the last term vanishing to first order (p. 169).
* `eq13`: (12) and the `mrs` relation imply the recursive form (13); the wage `w*` is the
  forward series and the **unique bounded solution** of (13).
-/

namespace Gali.StickyWagesPrices.WageSetting

open Filter Topology MeasureTheory
open Gali.StickyWagesPrices.LaborAggregation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Conditional expectations of discounted sums -/

/-- A geometrically weighted series of uniformly bounded random variables
converges at every state (used throughout Galí (2015), §6.1.2.1, eqs. (10)–(12), pp. 167–168). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-! ### Differentiating under `E_t` -/

/-- **Differentiation under a conditional expectation.** If the second-order
remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the state, then
`z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. Needed to differentiate the
reset-wage objective of Galí (2015), pp. 167–168, under `E_t`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- A Lipschitz bound on the derivative bounds the second-order remainder:
`|f(x+h) − f(x) − h f'(x)| ≤ L h²` (mean value theorem; used to differentiate (10) under
`E_t`, Galí (2015), pp. 167–168). -/
theorem remainder_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {x r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ Metric.ball x r, HasDerivAt f (f' y) y)
    (hL : ∀ y ∈ Metric.ball x r, |f' y - f' x| ≤ L * |y - x|) {h : ℝ} (hh : |h| < r) :
    |f (x + h) - f x - h * f' x| ≤ L * h ^ 2 := by
  have hsub : Metric.closedBall x |h| ⊆ Metric.ball x r :=
    Metric.closedBall_subset_ball hh
  have hd : ∀ y ∈ Metric.closedBall x |h|,
      HasDerivWithinAt (fun z => f z - z * f' x) (f' y - f' x) (Metric.closedBall x |h|) y := by
    intro y hy
    have h1 := hf y (hsub hy)
    have h2 : HasDerivAt (fun z : ℝ => z * f' x) (f' x) y := by
      simpa using (hasDerivAt_id y).mul_const (f' x)
    exact (HasDerivAt.sub h1 h2).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall x |h|, ‖f' y - f' x‖ ≤ L * |h| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hL y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  have hx : x ∈ Metric.closedBall x |h| := Metric.mem_closedBall_self (abs_nonneg h)
  have hxh : x + h ∈ Metric.closedBall x |h| := by
    simp [Metric.mem_closedBall]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_closedBall x |h|) hx hxh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at this
  calc |f (x + h) - f x - h * f' x| = |f (x + h) - (x + h) * f' x - (f x - x * f' x)| := by
        ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Differentiation under `E_t`, Lipschitz form.** If `z ↦ g z ω` has derivative
`g' z ω` near `x` and the derivative is Lipschitz at `x` uniformly in the state,
then `z ↦ E_t[g z]` has derivative `E_t[g' x]` at `x` (Galí (2015), pp. 167–168). -/
theorem hasDerivAt_E {g g' : ℝ → Ω → ℝ} {x r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ Metric.ball x r, ∀ ω, HasDerivAt (fun z => g z ω) (g' y ω) y)
    (hL : ∀ y ∈ Metric.ball x r, ∀ ω, |g' y ω - g' x ω| ≤ L * |y - x|) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t (g' x) ω) x :=
  hasDerivAt_E_of_remainder 𝔼 hr (fun _ hh ω' => remainder_le_of_lipschitz_deriv hL0
    (fun y hy => hg y hy ω') (fun y hy => hL y hy ω') hh) t ω

/-- **Term-by-term differentiation of a discounted sum of conditional
expectations** (Galí (2015), eq. (11), p. 168): `z ↦ ∑ₖ θᵏ E_t[gₖ z]` has
derivative `∑ₖ θᵏ E_t[g'ₖ x]` on an open interval `U`, provided each `g'ₖ` is
locally Lipschitz uniformly in the state and dominated by `uₖ` with
`∑ |θ|ᵏ uₖ < ∞`, and the series converges at one point of `U`. -/
theorem hasDerivAt_tsum_E {θ : ℝ} {g g' : ℕ → ℝ → Ω → ℝ} {U : Set ℝ} {u : ℕ → ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hg : ∀ k, ∀ y ∈ U, ∀ ω, HasDerivAt (fun z => g k z ω) (g' k y ω) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0,
      ∀ z ∈ Metric.ball y r, ∀ ω, |g' k z ω - g' k y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |g' k y ω| ≤ u k) (hu : Summable fun k => |θ| ^ k * u k)
    {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (g k y₀) ω) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => ∑' k, θ ^ k * 𝔼.E t (g k z) ω)
      (∑' k, θ ^ k * 𝔼.E t (g' k x) ω) x := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |θ| ^ k * u k)
    (g := fun k z => θ ^ k * 𝔼.E t (g k z) ω) (g' := fun k z => θ ^ k * 𝔼.E t (g' k z) ω)
    hu hU hU' (fun k y hy => ?_) (fun k y hy => ?_) hy₀ hs hx
  · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨L, hL0, r, hr, hL⟩ := hLip k y hy
    have hsub : Metric.ball y (min r r₁) ⊆ Metric.ball y r₁ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hsub' : Metric.ball y (min r r₁) ⊆ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left _ _)
    exact (hasDerivAt_E 𝔼 (lt_min hr hr₁) hL0 (fun z hz ω' => hg k z (hball (hsub hz)) ω')
      (fun z hz ω' => hL z (hsub' hz) ω') t ω).const_mul (θ ^ k)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k y hy) t ω)
      (pow_nonneg (abs_nonneg θ) k)

/-! ### The reset-wage objective and the first-order condition (11) -/

/-- The desired (frictionless) gross markup `M = ε/(ε − 1)` (Galí (2015), p. 168). -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- The desired markup exceeds one: `M > 1` for `ε > 1` (Galí (2015), p. 168). -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  unfold markup
  rw [one_lt_div (by linarith)]
  linarith

/-- The desired markup is positive (Galí (2015), p. 168). -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- The labour-demand constraint, Galí (2015), pp. 167–168:
`Y_{t+k|t} = (P*_t / P_{t+k})^{−ε} C_{t+k}`, as a random variable. -/
noncomputable def demand (ε Pstar : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (Pstar / P ω) ^ (-ε) * C ω

/-- Demand factorises as `P*^{−ε} · P^ε C` (Galí (2015), the labour-demand constraint, p. 168). -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand ε x P C ω = x ^ (-ε) * (P ω ^ ε * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le ε, div_inv_eq_mul]
  ring

/-- Demand is positive (Galí (2015), the labour-demand constraint, p. 168). -/
theorem demand_pos {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) : 0 < demand ε x P C ω :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hx (hP ω)) _) (hC ω)

/-- The price elasticity of labour demand is `−ε`: `dY/dP* = −ε Y / P*`
(Galí (2015), pp. 167–168). -/
theorem hasDerivAt_demand {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    HasDerivAt (fun z => demand ε z P C ω) (-ε * demand ε x P C ω / x) x := by
  have hxP : x / P ω ≠ 0 := (div_pos hx (hP ω)).ne'
  have h1 : HasDerivAt (fun z => z / P ω) (1 / P ω) x := (hasDerivAt_id x).div_const (P ω)
  have h2 := (h1.rpow_const (p := -ε) (Or.inl hxP)).mul_const (C ω)
  refine h2.congr_deriv ?_
  unfold demand
  rw [Real.rpow_sub_one hxP]
  have := (hP ω).ne'
  field_simp

/-- Generic horizon-`k` payoff of an agent (here the union) that reset its wage (price) to
`P*` (Galí (2015), pp. 167–168):
`Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))`, where
`Q_{t,t+k} = Λ_{t,t+k}/P_{t+k}` converts nominal date-`t+k` income into date-`t`
utility and `Ψ_{t+k}` is the nominal cost (for the union: money disutility of work). -/
noncomputable def profit (ε : ℝ) (Q P C : Ω → ℝ) (Ψ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (Pstar * demand ε Pstar P C ω - Ψ ω (demand ε Pstar P C ω))

/-- **The reset-wage objective** (Galí (2015), pp. 167–168):
`∑ₖ θᵏ E_t[Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]`, a genuine infinite
discounted sum, evaluated at the state `ω`. -/
noncomputable def objective (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) Pstar) ω

/-- The summand of (11), Galí (2015), pp. 167–168:
`Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})`, with `Ψ'_{t+k|t} = Ψ'_{t+k}(Y_{t+k|t})`
the nominal marginal cost. -/
noncomputable def focTerm (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * demand ε Pstar P C ω * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The left-hand side of the optimality condition (11), Galí (2015), pp. 167–168:
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})]`. -/
noncomputable def focSum (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (focTerm ε (Q k) (P k) (C k) (dΨ k) Pstar) ω

/-- The derivative of horizon-`k` profits in `P*`:
`((1 − ε)/P*) Q Y (P* − M Ψ')` (Galí (2015), pp. 167–168). -/
noncomputable def profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) / Pstar * focTerm ε Q P C dΨ Pstar ω

/-- **Marginal profit at one horizon** (Galí (2015), pp. 167–168):
`d/dP* [Q (P* Y − Ψ(Y))] = ((1 − ε)/P*) Q Y (P* − M Ψ'(Y))`. -/
theorem hasDerivAt_profit {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    {Ψ dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ ω) (dΨ ω y) y) (ω : Ω) :
    HasDerivAt (fun z => profit ε Q P C Ψ z ω) (profitDeriv ε Q P C dΨ x ω) x := by
  have hY := hasDerivAt_demand (ε := ε) (C := C) hx hP ω
  have hΨY := (hΨ ω _ (demand_pos hx hP hC ω)).comp x hY
  have h := (((hasDerivAt_id x).mul hY).sub hΨY).const_mul (Q ω)
  refine h.congr_deriv ?_
  unfold profitDeriv focTerm markup
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- `E_t` of marginal profit: the constant `(1 − ε)/P*` comes out of `E_t`
(Galí (2015), pp. 167–168). -/
theorem E_profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (x : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (profitDeriv ε Q P C dΨ x) ω = (1 - ε) / x * 𝔼.E t (focTerm ε Q P C dΨ x) ω := by
  have : profitDeriv ε Q P C dΨ x = ((1 - ε) / x) • focTerm ε Q P C dΨ x := rfl
  rw [this, 𝔼.E_smul]
  rfl

/-- **The derivative of the reset-wage objective** (Galí (2015), eq. (11), p. 168):
under explicit domination and local-Lipschitz hypotheses on marginal profits and
convergence of the objective at one price, the objective has derivative
`((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]` at every `P*` in
an open interval `U ⊆ (0, ∞)`. -/
theorem hasDerivAt_objective {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U) (hUpos : U ⊆ Set.Ioi 0)
    {u : ℕ → ℝ}
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (hu : Summable fun k => |θ| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have h := hasDerivAt_tsum_E 𝔼 (θ := θ)
    (g := fun k z => profit ε (Q k) (P k) (C k) (Ψ k) z)
    (g' := fun k z => profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) hU hU'
    (fun k y hy ω' => hasDerivAt_profit hε (hUpos hy) (hP k) (hC k) (hΨ k) ω')
    hLip hdom hu hy₀ t ω hs hx
  refine h.congr_deriv ?_
  simp only [E_profitDeriv, focSum]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **The optimality condition (11) is necessary** (Galí (2015), eq. (11), p. 168):
if `P*` is a local maximum of the reset-wage objective, then
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})] = 0`. -/
theorem foc_of_isLocalMax {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} {t : ℕ} {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hder : HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero hder
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective is differentiable at every positive price when marginal profits
are dominated on every bounded interval `(a, b)` with `a > 0` (Galí (2015), pp. 167–168). -/
theorem hasDerivAt_objective_of_pos {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  obtain ⟨u, hu, hdom⟩ := hloc (x / 2) (x + 1) (by positivity)
  have hxU : x ∈ Set.Ioo (x / 2) (x + 1) := ⟨by linarith, by linarith⟩
  have hUpos : Set.Ioo (x / 2) (x + 1) ⊆ Set.Ioi 0 := fun y hy => by
    simp only [Set.mem_Ioi]; linarith [hy.1]
  exact hasDerivAt_objective 𝔼 hε hP hC hΨ isOpen_Ioo isPreconnected_Ioo hUpos
    (fun k y hy => hLip k y (hUpos hy)) hdom hu hxU t ω (hs x hx) hxU

/-! ### The first-order condition characterises the optimum (convex costs) -/

/-- The `P*`-dependent core of the summand of (11) once the factor `P*^{−ε}` of
demand is taken out: `Q P^ε C (P* − M Ψ'(Y))` (Galí (2015), pp. 167–168). -/
noncomputable def focCore (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (P ω ^ ε * C ω) * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The summand of (11) is `P*^{−ε}` times its core (Galí (2015), pp. 167–168). -/
theorem focTerm_eq {ε x : ℝ} (hx : 0 < x) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) : focTerm ε Q P C dΨ x = x ^ (-ε) • focCore ε Q P C dΨ x := by
  funext ω
  simp only [focTerm, focCore, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hP ω]
  ring

/-- With convex costs (nondecreasing marginal cost), the core of (11) increases in
`P*` at least at rate `Q P^ε C`: a higher price lowers demand and hence marginal
cost (Galí (2015), pp. 167–168). -/
theorem focCore_sub_ge {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (ω : Ω) :
    (y - x) * (Q ω * (P ω ^ ε * C ω)) ≤ focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hK : 0 < P ω ^ ε * C ω := mul_pos (Real.rpow_pos_of_pos (hP ω) ε) (hC ω)
  have hdem : demand ε y P C ω ≤ demand ε x P C ω := by
    rw [demand_eq hx hP ω, demand_eq hy hP ω]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
      hK.le
  have hd : dΨ ω (demand ε y P C ω) ≤ dΨ ω (demand ε x P C ω) :=
    hconv ω (demand_pos hy hP hC ω) (demand_pos hx hP hC ω) hdem
  have key : focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω
        - (y - x) * (Q ω * (P ω ^ ε * C ω))
      = Q ω * (P ω ^ ε * C ω) *
        (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) := by
    unfold focCore; ring
  have h0 : 0 ≤ Q ω * (P ω ^ ε * C ω) *
      (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) :=
    mul_nonneg (mul_pos (hQ ω) hK).le
      (mul_nonneg (markup_pos hε).le (sub_nonneg.mpr hd))
  linarith

/-- `E_t` version of `focCore_sub_ge` (Galí (2015), pp. 167–168). -/
theorem E_focCore_le {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (t : ℕ) (ω : Ω) :
    (y - x) * 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω + 𝔼.E t (focCore ε Q P C dΨ x) ω
      ≤ 𝔼.E t (focCore ε Q P C dΨ y) ω := by
  have hle : (y - x) • (fun ω' => Q ω' * (P ω' ^ ε * C ω')) + focCore ε Q P C dΨ x
      ≤ focCore ε Q P C dΨ y := fun ω' => by
    have := focCore_sub_ge hε hQ hP hC hconv hx hxy ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have := 𝔼.mono t hle ω
  simpa [map_add, map_smul] using this

/-- The expected-revenue weight `E_t[Q P^ε C]` is nonnegative (Galí (2015), pp. 167–168). -/
theorem E_weight_nonneg {ε : ℝ} {Q P C : Ω → ℝ} (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω := by
  have h0 : (0 : Ω → ℝ) ≤ fun ω' => Q ω' * (P ω' ^ ε * C ω') := fun ω' =>
    (mul_pos (hQ ω') (mul_pos (Real.rpow_pos_of_pos (hP ω') ε) (hC ω'))).le
  simpa using 𝔼.mono t h0 ω

/-- `E_t` of the summand of (11) in terms of marginal profit
(Galí (2015), pp. 167–168). -/
theorem E_focCore_eq {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    (dΨ : Ω → ℝ → ℝ) (hP : ∀ ω, 0 < P ω) (t : ℕ) (ω : Ω) :
    𝔼.E t (focCore ε Q P C dΨ x) ω
      = ((1 - ε) / x * x ^ (-ε))⁻¹ * 𝔼.E t (profitDeriv ε Q P C dΨ x) ω := by
  rw [E_profitDeriv, focTerm_eq hx dΨ hP, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h2 : x ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 : 1 - ε ≠ 0 := by linarith
  field_simp

/-- **The optimality condition (11) characterises the optimal reset wage**
(Galí (2015), eq. (11), p. 168). With convex costs (nondecreasing marginal cost),
positive discount factors, prices and demand, and a positive current-period
revenue weight, a positive price `P*` maximises the reset-wage objective over
all positive prices if and only if it satisfies (11); such a maximiser is then
the strict, hence unique, maximiser. -/
theorem isMaxOn_iff_foc {θ ε : ℝ} (hε : 1 < ε) (hθ : 0 ≤ θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ k ω, 0 < Q k ω) (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hconv : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0))
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω)
    {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  set V := fun z => objective 𝔼 θ ε Q P C Ψ t z ω with hV
  set H : ℝ → ℝ := fun z => ∑' k, θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω
    with hH
  have hder : ∀ z, 0 < z → HasDerivAt V ((1 - ε) / z * focSum 𝔼 θ ε Q P C dΨ t z ω) z :=
    fun z hz => hasDerivAt_objective_of_pos 𝔼 hε hP hC hΨ hLip hloc t ω hs hz
  -- summability of the core series
  have hsum : ∀ z, 0 < z →
      Summable fun k => θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω := by
    intro z hz
    obtain ⟨u, hu, hdom⟩ := hloc (z / 2) (z + 1) (by positivity)
    have hzU : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hs' : Summable fun k =>
        θ ^ k * 𝔼.E t (profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) ω := by
      refine Summable.of_norm_bounded hu fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k z hzU) t ω)
        (pow_nonneg (abs_nonneg θ) k)
    refine (hs'.mul_left ((1 - ε) / z * z ^ (-ε))⁻¹).congr fun k => ?_
    rw [E_focCore_eq 𝔼 hε hz _ (hP k)]
    ring
  -- (11) in terms of the core series
  have hfocH : ∀ z, 0 < z → focSum 𝔼 θ ε Q P C dΨ t z ω = z ^ (-ε) * H z := by
    intro z hz
    simp only [focSum, hH, focTerm_eq hz _ (hP _), 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  -- the core series is strictly increasing
  have hHmono : ∀ z y, 0 < z → z < y → H z < H y := by
    intro z y hz hzy
    refine Summable.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ (hsum z hz)
      (hsum y (hz.trans hzy))
    · have h1 := E_focCore_le 𝔼 hε (hQ k) (hP k) (hC k) (hconv k) hz hzy.le t ω
      have h2 := E_weight_nonneg 𝔼 (ε := ε) (hQ k) (hP k) (hC k) t ω
      have h3 : 0 ≤ (y - z) * 𝔼.E t (fun ω' => Q k ω' * (P k ω' ^ ε * C k ω')) ω :=
        mul_nonneg (by linarith) h2
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hθ k)
    · have h1 := E_focCore_le 𝔼 hε (hQ 0) (hP 0) (hC 0) (hconv 0) hz hzy.le t ω
      have h3 : 0 < (y - z) * 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω :=
        mul_pos (by linarith) hpos
      simp only [pow_zero, one_mul]
      linarith
  have hcoef : ∀ z, 0 < z → (1 - ε) / z < 0 := fun z hz => div_neg_of_neg_of_pos (by linarith) hz
  -- the strict-maximum part
  have hstrict : focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x → V y < V x := by
    intro hfoc
    have hHx : H x = 0 := by
      have := hfocH x hx
      rw [hfoc] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (Real.rpow_pos_of_pos hx _).ne'
    have hcont : ∀ z, 0 < z → ContinuousAt V z := fun z hz => (hder z hz).continuousAt
    have hinc : StrictMonoOn V (Set.Ioc 0 x) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 x)
        (fun z hz => (hcont z hz.1).continuousWithinAt) fun z hz => ?_
      rw [interior_Ioc] at hz
      rw [(hder z hz.1).deriv, hfocH z hz.1]
      have hHz : H z < 0 := hHx ▸ hHmono z x hz.1 hz.2
      have := mul_neg_of_neg_of_pos hHz (Real.rpow_pos_of_pos hz.1 (-ε))
      nlinarith [hcoef z hz.1]
    have hdec : StrictAntiOn V (Set.Ici x) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici x)
        (fun z hz => (hcont z (lt_of_lt_of_le hx hz)).continuousWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      have hz0 : 0 < z := hx.trans hz
      rw [(hder z hz0).deriv, hfocH z hz0]
      have hHz : 0 < H z := hHx ▸ hHmono x z hx hz
      have := mul_pos (Real.rpow_pos_of_pos hz0 (-ε)) hHz
      nlinarith [hcoef z hz0]
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with h | h
    · exact hinc ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ h
    · exact hdec (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
  refine ⟨⟨fun hmax => ?_, fun hfoc => ?_⟩, hstrict⟩
  · exact foc_of_isLocalMax 𝔼 hε hx (hder x hx) (hmax.isLocalMax (Ioi_mem_nhds hx))
  · intro y hy
    rcases eq_or_ne y x with h | h
    · rw [h]; exact le_refl (V x)
    · exact (hstrict hfoc y hy h).le

/-! ### Flexible prices and the zero-wage-inflation steady state -/

/-- With flexible wages (`θ = 0`) the objective reduces to current expected
profits (Galí (2015), p. 168). -/
theorem objective_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    objective 𝔼 0 ε Q P C Ψ t z ω = 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) ω := by
  unfold objective
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- With flexible wages (`θ = 0`) condition (11) involves only the current period
(Galí (2015), p. 168). -/
theorem focSum_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t z ω = 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) z) ω := by
  unfold focSum
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- **Flexible-wage wage-setting rule** (Galí (2015), p. 168): with `θ = 0` and the
current-period variables known at `t`, condition (11) holds if and only if
`P*_t = M Ψ'_{t|t}`, the frictionless markup over marginal cost. -/
theorem flexible_foc_iff {ε x : ℝ} (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    {t : ℕ} (hknown : 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x)
      = focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t x ω = 0 ↔ x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  rw [focSum_flexible, hknown]
  unfold focTerm
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  constructor
  · intro h0
    have := (mul_eq_zero.mp h0).resolve_left h.ne'
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero]

/-- **Flexible-wage optimum** (Galí (2015), p. 168): with `θ = 0`, if the
current-period profit function is known at `t` and `P*` is a local maximum of
the objective, then `P* = M Ψ'_{t|t}`. -/
theorem flexible_optimum {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ 0 ω) (dΨ 0 ω y) y) {t : ℕ}
    (hknown : ∀ z, 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z)
      = profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 0 ε Q P C Ψ t z ω) x) :
    x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  have hfun : (fun z => objective 𝔼 0 ε Q P C Ψ t z ω)
      = fun z => profit ε (Q 0) (P 0) (C 0) (Ψ 0) z ω := by
    funext z; rw [objective_flexible, hknown]
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero (hasDerivAt_profit hε hx hP hC hΨ ω)
  unfold profitDeriv focTerm at h0
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  have h1 := (mul_eq_zero.mp h0).resolve_left hc
  have := (mul_eq_zero.mp h1).resolve_left h.ne'
  linarith

/-- **The zero-wage-inflation steady state** (Galí (2015), p. 168): with constant price
level `P`, consumption `C`, discount factors `Λ_{t,t+k} = βᵏ` and marginal cost `Ψ`
at the steady-state output, condition (11) at `P* = P` holds if and only if
`P = M Ψ`: actual markups equal the frictionless markup. -/
theorem steadyState_foc_iff {β θ ε Pbar Cbar Ψbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hP : 0 < Pbar) (hC : 0 < Cbar) {dΨ : ℕ → Ω → ℝ → ℝ}
    (hdΨ : ∀ k ω, dΨ k ω Cbar = Ψbar) (t : ℕ) (ω : Ω) :
    focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t Pbar ω = 0
      ↔ Pbar = markup ε * Ψbar := by
  have hY : ∀ ω' : Ω, demand ε Pbar (fun _ => Pbar) (fun _ => Cbar) ω' = Cbar := by
    intro ω'; simp [demand, div_self hP.ne']
  have hterm : ∀ k, focTerm ε (fun _ => β ^ k / Pbar) (fun _ => Pbar) (fun _ => Cbar) (dΨ k) Pbar
      = fun _ => β ^ k / Pbar * Cbar * (Pbar - markup ε * Ψbar) := by
    intro k; funext ω'
    simp only [focTerm, hY, hdΨ]
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hsum : focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t
      Pbar ω = (1 - β * θ)⁻¹ * (Cbar / Pbar * (Pbar - markup ε * Ψbar)) := by
    simp only [focSum, hterm, 𝔼.const]
    rw [← tsum_geometric_of_lt_one hβθ0 hβθ1, ← tsum_mul_right]
    congr 1; funext k
    rw [mul_pow]; field_simp
  rw [hsum]
  have h1 : (1 - β * θ)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h2 : Cbar / Pbar ≠ 0 := (div_pos hC hP).ne'
  constructor
  · intro h0
    have := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h1)).resolve_left h2
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero, mul_zero]

/-! ### The log-linear wage-setting rule (12) as the exact linearisation of (11) -/

/-- The log desired markup `μ = log M` (Galí (2015), p. 168). -/
noncomputable def logMarkup (ε : ℝ) : ℝ := Real.log (markup ε)

/-- The left-hand side of (11) written in terms of the weights
`wₖ = Λ_{t,t+k} Y_{t+k|t} / P_{t+k}` and the nominal marginal costs
`Ψ_{t+k|t}` (Galí (2015), eq. (11), p. 168):
`∑ₖ θᵏ E_t[wₖ (P* − M Ψ_{t+k|t})]`. -/
noncomputable def focLHS (θ ε : ℝ) (w : ℕ → Ω → ℝ) (Pstar : ℝ) (Ψm : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (fun ω' => w k ω' * (Pstar - markup ε * Ψm k ω')) ω

/-- The reset-wage condition `focSum` is (11) with weights `Q_{t,t+k} Y_{t+k|t}`
and marginal costs `Ψ'_{t+k}(Y_{t+k|t})` (Galí (2015), pp. 167–168). -/
theorem focSum_eq_focLHS (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (x : ℝ) :
    focSum 𝔼 θ ε Q P C dΨ t x = focLHS 𝔼 θ ε (fun k ω => Q k ω * demand ε x (P k) (C k) ω) x
      (fun k ω => dΨ k ω (demand ε x (P k) (C k) ω)) t := rfl

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]` (used for (12), Galí (2015), p. 168). -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr hgB) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- **Exact linearisation of (11) at the zero-wage-inflation steady state**
(Galí (2015), p. 168). Perturb the steady state along an arbitrary bounded
direction: log weights `log wₖ = log(βᵏ w̄) + s ŵₖ` (stochastic discount factor,
demand and price level combined), log reset wage `p* = p̄ + s x̂`, and log
marginal costs `ψ_{t+k|t} = ψ̄ + s ψ̂ₖ`, where the steady state satisfies
`p̄ = μ + ψ̄` (`P = M Ψ`). Then the left-hand side of (11) has derivative
`w̄ e^{p̄} ∑ₖ (βθ)ᵏ (x̂ − E_t ψ̂ₖ)` at `s = 0`. The weight deviations `ŵ` drop out:
to first order only prices and marginal costs matter. -/
theorem hasDerivAt_focLHS_path {θ β ε wbar pbar xhat B : ℝ} (hε : 1 < ε) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {what ψhat : ℕ → Ω → ℝ}
    (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hxB : |xhat| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hxB
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  -- rewrite the path of (11) through exponentials of `s a` and `s b`
  have hfun : (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      = fun s => ∑' k, (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    congr 1; funext k
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup ε) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup ε) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hε)]
        have := (markup_pos hε).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    ring
  rw [hfun]
  -- term-by-term differentiation on `(-1, 1)`
  have hbd : ∀ (g : Ω → ℝ), (∀ ω', |g ω'| ≤ 2 * B) → ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      |𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω| ≤ 2 * B * Real.exp (2 * B) := by
    intro g hg s hs
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hg ω') ?_ (Real.exp_pos _).le (by linarith)
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ 1 * (2 * B) := mul_le_mul hs1 (hg ω') (abs_nonneg _) zero_le_one
      _ = 2 * B := one_mul _
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => (β * θ) ^ k * (|c| * (2 * (2 * B * Real.exp (2 * B)))))
    (g := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)))
    (g' := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => a k ω' * Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => b k ω' * Real.exp (s * b k ω')) ω)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hβθ0 hβθ1).mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => (((hasDerivAt_E_exp 𝔼 (haB k) t ω s).sub
      (hasDerivAt_E_exp 𝔼 (hbB k) t ω s)).const_mul c).const_mul _)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβθ0 k), abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c))
        (pow_nonneg hβθ0 k)
      refine (abs_sub _ _).trans ?_
      linarith [hbd _ (haB k) s hs, hbd _ (hbB k) s hs])
    ⟨by norm_num, by norm_num⟩
    (by simp)
    ⟨by norm_num, by norm_num⟩
  refine hD.congr_deriv ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- **The log-linear wage-setting rule (12)** (Galí (2015), eq. (12), p. 168). The
first-order term of (11) at the zero-wage-inflation steady state vanishes if and only if
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k|t}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k|t} = ψ̄ + ψ̂ₖ` with `ψ̄ = p̄ − μ`. -/
theorem eq12_iff {θ β ε wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hwbar : 0 < wbar) {ψhat : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + (1 - β * θ) *
        ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hβθ : |β * θ| < 1 := by rwa [abs_of_nonneg hβθ0]
  have hg := summable_geometric_of_lt_one hβθ0 hβθ1
  have hT := summable_geometric_bounded hβθ (fun k ω' => 𝔼.abs_E_le (hψ k) t ω') ω
  set T := ∑' k, (β * θ) ^ k * 𝔼.E t (ψhat k) ω with hTdef
  have h1 : ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = xhat * (1 - β * θ)⁻¹ - T := by
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hg.mul_right xhat) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1]
    ring
  have h2 : ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (pbar - logMarkup ε) * (1 - β * θ)⁻¹ + T := by
    have : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
        = (pbar - logMarkup ε) + 𝔼.E t (ψhat k) ω := by
      intro k
      have hf : (fun ω' => (pbar - logMarkup ε) + ψhat k ω')
          = (fun _ => pbar - logMarkup ε) + ψhat k := rfl
      rw [hf, map_add, 𝔼.const]; rfl
    simp_rw [this, mul_add]
    rw [Summable.tsum_add (hg.mul_right _) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1, mul_comm]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hd : 1 - β * θ ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp at h3 ⊢
    linarith
  · intro h
    have h3 : xhat * (1 - β * θ)⁻¹ - T = 0 := by
      field_simp at h ⊢
      linarith
    rw [h3, mul_zero]

/-! ### Regularity of the reset-wage problem from model primitives -/

/-- **Primitive assumptions on the reset-wage problem** (Galí (2015), pp. 167–168): Calvo
`θ ≥ 0` and a discount bound `β ≥ 0` with `θβ < 1`; `ε > 1`; nominal discount factors
`0 < Q_{t,t+k} ≤ Q̄ βᵏ`; price levels and consumption in `[m, M̄]` with `m > 0`; a
nominal cost function `Ψ` twice differentiable at positive output, with `Ψ`, `Ψ'`,
`Ψ''` bounded, uniformly in the horizon and the state, on every compact range of
positive output. -/
def Primitives (θ β ε Qb m Mx : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ) :
    Prop :=
  0 ≤ θ ∧ 0 ≤ β ∧ θ * β < 1 ∧ 1 < ε ∧ 0 < m ∧
  (∀ k ω, 0 < Q k ω ∧ Q k ω ≤ Qb * β ^ k) ∧
  (∀ k ω, m ≤ P k ω ∧ P k ω ≤ Mx) ∧ (∀ k ω, m ≤ C k ω ∧ C k ω ≤ Mx) ∧
  (∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y) ∧
  (∀ k ω y, 0 < y → HasDerivAt (dΨ k ω) (d2Ψ k ω y) y) ∧
  (∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
    |Ψ k ω y| ≤ K ∧ |dΨ k ω y| ≤ K ∧ |d2Ψ k ω y| ≤ K)

/-- Bounds on the demand shifter `P^ε C ∈ [m^ε m, M̄^ε M̄]` (Galí (2015),
pp. 167–168). -/
theorem weight_bounds {ε m Mx : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) {P C : Ω → ℝ}
    (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx) (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    m ^ ε * m ≤ P ω ^ ε * C ω ∧ P ω ^ ε * C ω ≤ Mx ^ ε * Mx := by
  have hP0 : 0 ≤ P ω := hm.le.trans (hP ω).1
  have hC0 : 0 ≤ C ω := hm.le.trans (hC ω).1
  refine ⟨mul_le_mul (Real.rpow_le_rpow hm.le (hP ω).1 hε) (hC ω).1 hm.le
    (Real.rpow_nonneg hP0 _), mul_le_mul (Real.rpow_le_rpow hP0 (hP ω).2 hε) (hC ω).2 hC0
    (Real.rpow_nonneg (hP0.trans (hP ω).2) _)⟩

/-- **Demand stays in a compact range of positive output** when the reset wage
ranges over `[lo, hi] ⊂ (0, ∞)` (Galí (2015), the labour-demand constraint, p. 168). -/
theorem demand_bounds {ε m Mx lo hi z : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) (hlo : 0 < lo)
    (hz1 : lo ≤ z) (hz2 : z ≤ hi) {P C : Ω → ℝ} (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx)
    (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    hi ^ (-ε) * (m ^ ε * m) ≤ demand ε z P C ω ∧
      demand ε z P C ω ≤ lo ^ (-ε) * (Mx ^ ε * Mx) := by
  have hz : 0 < z := hlo.trans_le hz1
  have hPpos : ∀ ω, 0 < P ω := fun ω => hm.trans_le (hP ω).1
  obtain ⟨hw1, hw2⟩ := weight_bounds hε hm hP hC ω
  rw [demand_eq hz hPpos ω]
  have hm0 : 0 ≤ m ^ ε * m := by positivity
  exact ⟨mul_le_mul (Real.rpow_le_rpow_of_nonpos hz hz2 (by linarith)) hw1 hm0
      (Real.rpow_nonneg hz.le _),
    mul_le_mul (Real.rpow_le_rpow_of_nonpos hlo hz1 (by linarith)) hw2 (hm0.trans hw1)
      (Real.rpow_nonneg hlo.le _)⟩

/-- Marginal profit in factored form:
`((1 − ε)/P*) Q Y (P* − M Ψ') = (1 − ε) Q P^ε C (P*^{−ε} − M P*^{−ε−1} Ψ')`
(Galí (2015), pp. 167–168). -/
theorem profitDeriv_eq {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    profitDeriv ε Q P C dΨ z ω = (1 - ε) * Q ω * (P ω ^ ε * C ω) *
      (z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))) := by
  unfold profitDeriv focTerm
  rw [demand_eq hz hP ω, Real.rpow_sub_one hz.ne']
  field_simp

/-- The derivative of marginal profit in the reset wage (Galí (2015), pp. 167–168). -/
noncomputable def profitDeriv2 (ε : ℝ) (Q P C : Ω → ℝ) (dΨ d2Ψ : Ω → ℝ → ℝ) (z : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) * Q ω * (P ω ^ ε * C ω) * (-ε * z ^ (-ε - 1) - markup ε *
    ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
      + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))))

/-- Marginal profit is differentiable in the reset wage, with derivative
`profitDeriv2` (Galí (2015), pp. 167–168). -/
theorem hasDerivAt_profitDeriv {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ}
    {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hdΨ : ∀ ω y, 0 < y → HasDerivAt (dΨ ω) (d2Ψ ω y) y) (ω : Ω) :
    HasDerivAt (fun x => profitDeriv ε Q P C dΨ x ω) (profitDeriv2 ε Q P C dΨ d2Ψ z ω) z := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-ε)) (-ε * z ^ (-ε - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h2 : HasDerivAt (fun x : ℝ => x ^ (-ε - 1)) ((-ε - 1) * z ^ (-ε - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h3 : HasDerivAt (fun x => dΨ ω (demand ε x P C ω))
      (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)) z :=
    (hdΨ ω _ (demand_pos hz hP hC ω)).comp z (hasDerivAt_demand hz hP ω)
  have hG := (HasDerivAt.sub h1 ((HasDerivAt.mul h2 h3).const_mul (markup ε))).const_mul
    ((1 - ε) * Q ω * (P ω ^ ε * C ω))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact profitDeriv_eq hx dΨ hP ω

/-- A bound on marginal profit on prices `≥ lo > 0` (Galí (2015), pp. 167–168). -/
theorem abs_profitDeriv_le {ε z lo Qm W K : ℝ} (hε : 1 < ε) (hlo : 0 < lo) (hz : lo ≤ z)
    {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) (hQ0 : 0 < Q ω)
    (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω) (hW : P ω ^ ε * C ω ≤ W)
    (hd : |dΨ ω (demand ε z P C ω)| ≤ K) :
    |profitDeriv ε Q P C dΨ z ω|
      ≤ (ε - 1) * Qm * W * (lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K)) := by
  have hz0 : 0 < z := hlo.trans_le hz
  rw [profitDeriv_eq hz0 dΨ hP ω]
  have hM := markup_pos hε
  have a0 : 0 ≤ z ^ (-ε) := Real.rpow_nonneg hz0.le _
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have b0 : z ^ (-ε) ≤ lo ^ (-ε) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have hi : |z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))|
      ≤ lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg a0, abs_mul, abs_of_pos hM, abs_mul, abs_of_nonneg a1]
    gcongr
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- A bound on the derivative of marginal profit on prices `≥ lo > 0`
(Galí (2015), pp. 167–168). -/
theorem abs_profitDeriv2_le {ε z lo Qm W K Yh : ℝ} (hε : 1 < ε) (hlo : 0 < lo)
    (hz : lo ≤ z) {Q P C : Ω → ℝ} {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) (hQ0 : 0 < Q ω) (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω)
    (hW : P ω ^ ε * C ω ≤ W) (hd : |dΨ ω (demand ε z P C ω)| ≤ K)
    (hd2 : |d2Ψ ω (demand ε z P C ω)| ≤ K) (hY : demand ε z P C ω ≤ Yh) :
    |profitDeriv2 ε Q P C dΨ d2Ψ z ω| ≤ (ε - 1) * Qm * W * (ε * lo ^ (-ε - 1)
      + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo))))) := by
  have hz0 : 0 < z := hlo.trans_le hz
  have hM := markup_pos hε
  have hε0 : 0 < ε := by linarith
  have hY0 := demand_pos (ε := ε) hz0 hP hC ω
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have a2 : 0 ≤ z ^ (-ε - 1 - 1) := Real.rpow_nonneg hz0.le _
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b2 : z ^ (-ε - 1 - 1) ≤ lo ^ (-ε - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have bY : demand ε z P C ω / z ≤ Yh / lo := div_le_div₀ (hY0.le.trans hY) hY hlo hz
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have e1 : |-ε * z ^ (-ε - 1)| = ε * z ^ (-ε - 1) := by
    rw [abs_mul, abs_neg, abs_of_pos hε0, abs_of_nonneg a1]
  have e2 : |(-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)|
      = (ε + 1) * z ^ (-ε - 1 - 1) * |dΨ ω (demand ε z P C ω)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg a2, abs_of_nonpos (by linarith : -ε - 1 ≤ 0)]
    ring
  have e3 : |z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))|
      = z ^ (-ε - 1) * (|d2Ψ ω (demand ε z P C ω)| * (ε * (demand ε z P C ω / z))) := by
    have hn : -ε * demand ε z P C ω / z ≤ 0 := by
      rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonpos hn]
    ring
  have hi : |-ε * z ^ (-ε - 1) - markup ε *
      ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
        + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)))|
      ≤ ε * lo ^ (-ε - 1)
        + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo)))) := by
    refine (abs_sub _ _).trans ?_
    rw [e1, abs_mul, abs_of_pos hM]
    refine add_le_add (by gcongr) (mul_le_mul_of_nonneg_left ?_ hM.le)
    refine (abs_add_le _ _).trans ?_
    rw [e2, e3]
    have hYz : 0 ≤ demand ε z P C ω / z := by positivity
    gcongr
  unfold profitDeriv2
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- **Local Lipschitz bounds on marginal profit from primitives** (Galí (2015),
pp. 167–168): under `Primitives`, marginal profit is Lipschitz in the reset wage near
every positive price, uniformly in the state. -/
theorem lipschitz_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y| := by
  obtain ⟨-, hβ, -, hε, hm, hQ, hP, hC, -, hdΨ, hΨb⟩ := hprim
  intro k y hy
  have hε0 : 0 ≤ ε := by linarith
  have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
  have hCpos : ∀ ω, 0 < C k ω := fun ω => hm.trans_le (hC k ω).1
  set lo := y / 2 with hlo_def
  set hi := 2 * y with hhi_def
  have hlo : 0 < lo := by positivity
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  set Yh := lo ^ (-ε) * Khi
  have hy1 : 0 < hi ^ (-ε) * Klo := by positivity
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) Yh hy1
  set L₀ := (ε - 1) * (|Qb| * β ^ k) * Khi * (ε * lo ^ (-ε - 1) + markup ε *
    ((ε + 1) * lo ^ (-ε - 1 - 1) * |K| + lo ^ (-ε - 1) * (|K| * (ε * (Yh / lo)))))
  refine ⟨max L₀ 0, le_max_right _ _, lo, hlo, fun z hz ω => ?_⟩
  have hball : ∀ x ∈ Metric.ball y lo, lo ≤ x ∧ x ≤ hi := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith
  have hd : ∀ x ∈ Metric.ball y lo, HasDerivWithinAt
      (fun x => profitDeriv ε (Q k) (P k) (C k) (dΨ k) x ω)
      (profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω) (Metric.ball y lo) x :=
    fun x hx => (hasDerivAt_profitDeriv (hlo.trans_le (hball x hx).1) hPpos hCpos (hdΨ k)
      ω).hasDerivWithinAt
  have hb : ∀ x ∈ Metric.ball y lo,
      ‖profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω‖ ≤ max L₀ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hball x hx
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hlo hx1 hx2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, hK2⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    rw [Real.norm_eq_abs]
    exact (abs_profitDeriv2_le hε hlo hx1 hPpos hCpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))
      (hK2.trans (le_abs_self _)) hY2).trans (le_max_left _ _)
  have hyb : y ∈ Metric.ball y lo := Metric.mem_ball_self hlo
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_ball y lo) hyb hz
  simpa only [Real.norm_eq_abs] using this

/-- **Domination of marginal profit from primitives** (Galí (2015), pp. 167–168): under
`Primitives`, on every interval `(a, b)` with `a > 0`, marginal profit at horizon `k`
is bounded by `uₖ = c βᵏ`, and `∑ θᵏ uₖ < ∞` since `θβ < 1`. -/
theorem dominated_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro a b ha
  have hε0 : 0 ≤ ε := by linarith
  set hi := max b a
  have hhi : 0 < hi := ha.trans_le (le_max_right _ _)
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) (a ^ (-ε) * Khi) (by positivity)
  set c := (ε - 1) * |Qb| * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|))
  refine ⟨fun k => (ε - 1) * (|Qb| * β ^ k) * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|)),
    ?_, fun k y hy ω => ?_⟩
  · refine ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c).congr
      fun k => ?_
    rw [abs_of_nonneg hθ, mul_pow]
    ring
  · have hy1 : a ≤ y := hy.1.le
    have hy2 : y ≤ hi := hy.2.le.trans (le_max_left _ _)
    have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm ha hy1 hy2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, -⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    exact abs_profitDeriv_le hε ha hy1 hPpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))

/-- **Convergence of the objective from primitives** (Galí (2015), pp. 167–168): under
`Primitives`, the reset-wage objective converges at every positive price. -/
theorem summable_profit_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) : ∀ y, 0 < y →
      Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro y hy
  have hε0 : 0 ≤ ε := by linarith
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (y ^ (-ε) * Klo) (y ^ (-ε) * Khi) (by positivity)
  set c := |Qb| * (y * |y ^ (-ε) * Khi| + |K|)
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hθ]
  have hb : ∀ ω', |profit ε (Q k) (P k) (C k) (Ψ k) y ω'| ≤ |Qb| * β ^ k *
      (y * |y ^ (-ε) * Khi| + |K|) := by
    intro ω'
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hy le_rfl le_rfl (hP k) (hC k) ω'
    obtain ⟨hK0, -, -⟩ := hK k ω' _ hY1 hY2
    have hY0 : 0 < demand ε y (P k) (C k) ω' :=
      demand_pos hy (fun ω => hm.trans_le (hP k ω).1) (fun ω => hm.trans_le (hC k ω).1) ω'
    have hQm : Q k ω' ≤ |Qb| * β ^ k :=
      (hQ k ω').2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    unfold profit
    rw [abs_mul, abs_of_pos (hQ k ω').1]
    refine mul_le_mul hQm ((abs_sub _ _).trans (add_le_add ?_
      (hK0.trans (le_abs_self _)))) (abs_nonneg _) ((hQ k ω').1.le.trans hQm)
    rw [abs_mul, abs_of_pos hy, abs_of_pos hY0]
    exact mul_le_mul_of_nonneg_left (hY2.trans (le_abs_self _)) hy.le
  calc θ ^ k * |𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω|
      ≤ θ ^ k * (|Qb| * β ^ k * (y * |y ^ (-ε) * Khi| + |K|)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le hb t ω) (pow_nonneg hθ k)
    _ = c * (θ * β) ^ k := by rw [mul_pow]; ring

/-- **The derivative of the reset-wage objective, from primitives only**
(Galí (2015), eq. (11), p. 168): under `Primitives`, at every positive price the
objective has derivative `((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]`. -/
theorem hasDerivAt_objective_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨-, -, -, hε, hm, -, hP, hC, hΨ, -, -⟩ := hprim
  exact hasDerivAt_objective_of_pos 𝔼 hε (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hLip hloc t ω hs hx

/-- **(11) is necessary, from primitives only** (Galí (2015), eq. (11), p. 168): under
`Primitives`, a local maximum `P* > 0` of the reset-wage objective satisfies (11). -/
theorem foc_of_isLocalMax_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) {t : ℕ}
    {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 :=
  foc_of_isLocalMax 𝔼 hprim.2.2.2.1 hx (hasDerivAt_objective_of_primitives 𝔼 hprim t ω hx) hmax

/-- **(11) characterises the optimal reset wage, from primitives only**
(Galí (2015), eq. (11), p. 168): under `Primitives`, convex costs (`Ψ'' ≥ 0`) and the
a current-period discount factor bounded away from zero, a positive wage
maximises the objective over all positive wages if and only if it satisfies (11), and it is
then the unique maximiser. -/
theorem isMaxOn_iff_foc_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ)
    (hconv : ∀ k ω y, 0 < y → 0 ≤ d2Ψ k ω y) (hQ0 : ∃ q, 0 < q ∧ ∀ ω, q ≤ Q 0 ω) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨hθ, -, -, hε, hm, hQ, hP, hC, hΨ, hdΨ, -⟩ := hprim
  have hε0 : 0 ≤ ε := by linarith
  have hmono : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0) := by
    intro k ω
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun y hy => (hdΨ k ω y hy).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun y hy => (hdΨ k ω y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro y hy
      rw [(hdΨ k ω y hy).deriv]
      exact hconv k ω y hy
  have hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω := by
    obtain ⟨q, hq, hqle⟩ := hQ0
    have hc : 0 < q * (m ^ ε * m) := by positivity
    have hle : (fun _ : Ω => q * (m ^ ε * m))
        ≤ fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω') := fun ω' =>
      mul_le_mul (hqle ω') (weight_bounds hε0 hm (hP 0) (hC 0) ω').1 (by positivity)
        (hQ 0 ω').1.le
    have := 𝔼.mono t hle ω
    rw [𝔼.const] at this
    exact hc.trans_le this
  exact isMaxOn_iff_foc 𝔼 hε hθ (fun k ω => (hQ k ω).1) (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hmono hLip hloc t ω hs hpos hx


/-! ### The union's problem (10) -/

/-- Galí (2015), eq. (10), p. 167: the date-`t+k` term of the union's objective when the wage
is reset to `W*`, `(C^{−σ} (W*/P) N_{t+k|t} − N_{t+k|t}^{1+φ}/(1+φ)) Z`, where
`N_{t+k|t} = (W*/W_{t+k})^{−ε_w} N^d_{t+k}` is labour demand for the type (p. 168). -/
noncomputable def unionSurplus (σ φ ε : ℝ) (Z C P W Nd : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => (C ω ^ (-σ) * (x / P ω) * demand ε x W Nd ω -
    demand ε x W Nd ω ^ (1 + φ) / (1 + φ)) * Z ω

/-- Galí (2015), eq. (10), p. 167 (**the union's objective**), a genuine infinite discounted
sum: `∑ₖ (βθ_w)ᵏ E_t[(C_{t+k}^{−σ} (W*/P_{t+k}) N_{t+k|t} − N_{t+k|t}^{1+φ}/(1+φ)) Z_{t+k}]`. -/
noncomputable def unionObjective (θ β σ φ ε : ℝ) (Z C P W Nd : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    Ω → ℝ :=
  fun ω => ∑' k, (β * θ) ^ k * 𝔼.E t (unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x) ω

/-- Galí (2015), eq. (10), p. 167, **with `E_t` outside the sum as printed**: when the
period terms are uniformly bounded and `0 ≤ βθ_w < 1`,
`E_t[∑ₖ (βθ_w)ᵏ (…)] = ∑ₖ (βθ_w)ᵏ E_t[…]`. -/
theorem E_tsum_unionObjective {θ β σ φ ε : ℝ} (hβθ0 : 0 ≤ β * θ) (hβθ1 : β * θ < 1)
    {Z C P W Nd : ℕ → Ω → ℝ} {x K : ℝ}
    (hK : ∀ k ω, |unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x ω| ≤ K) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (fun ω' => ∑' k, (β * θ) ^ k *
        unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x ω') ω
      = unionObjective 𝔼 θ β σ φ ε Z C P W Nd t x ω := by
  have hb : ∀ k ω', |(β * θ) ^ k * unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x ω'|
      ≤ (β * θ) ^ k * K := fun k ω' => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβθ0 k)]
    exact mul_le_mul_of_nonneg_left (hK k ω') (pow_nonneg hβθ0 k)
  rw [𝔼.E_tsum hβθ0 hβθ1 hb t ω]
  unfold unionObjective
  congr 1
  funext k
  change 𝔼.E t ((β * θ) ^ k • unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x) ω = _
  rw [map_smul]
  rfl

/-- Galí (2015), eq. (10), p. 167: the money value at `t + k` of the disutility of `y` hours,
`Ψ(y) = P C^σ y^{1+φ}/(1+φ)`, so that `Q_{t,t+k} Ψ = βᵏ Z y^{1+φ}/(1+φ)`. -/
noncomputable def disutil (σ φ : ℝ) (P C : Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω y => P ω * C ω ^ σ * (y ^ (1 + φ) / (1 + φ))

/-- Galí (2015), p. 168: the marginal money disutility `Ψ'(y) = P C^σ y^φ = P · MRS`. -/
noncomputable def dDisutil (σ φ : ℝ) (P C : Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω y => P ω * C ω ^ σ * y ^ φ

/-- Galí (2015), p. 168: `Ψ''(y) = P C^σ φ y^{φ−1}`. -/
noncomputable def d2Disutil (σ φ : ℝ) (P C : Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω y => P ω * C ω ^ σ * (φ * y ^ (φ - 1))

/-- Galí (2015), eq. (10), p. 167: the union's discount factor on nominal income at `t + k`,
`Q_{t,t+k} = βᵏ Z_{t+k} C_{t+k}^{−σ}/P_{t+k}`. -/
noncomputable def unionQ (β σ : ℝ) (Z C P : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => β ^ k * Z k ω * C k ω ^ (-σ) / P k ω

/-- Galí (2015), p. 168: `Ψ' = P C^σ y^φ` is the derivative of the money disutility. -/
theorem hasDerivAt_disutil {σ φ : ℝ} (hφ : 0 ≤ φ) (P C : Ω → ℝ) (ω : Ω) {y : ℝ}
    (hy : 0 < y) : HasDerivAt (disutil σ φ P C ω) (dDisutil σ φ P C ω y) y := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inl hy.ne')).div_const
    (1 + φ)).const_mul (P ω * C ω ^ σ)
  refine h.congr_deriv ?_
  have : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [dDisutil, show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 168: `Ψ'' = P C^σ φ y^{φ−1}` is the derivative of `Ψ'`. -/
theorem hasDerivAt_dDisutil (σ φ : ℝ) (P C : Ω → ℝ) (ω : Ω) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (dDisutil σ φ P C ω) (d2Disutil σ φ P C ω y) y :=
  (Real.hasDerivAt_rpow_const (p := φ) (Or.inl hy.ne')).const_mul (P ω * C ω ^ σ)

/-- Galí (2015), p. 168: with `φ ≥ 0` the disutility of work is convex in hours. -/
theorem d2Disutil_nonneg {σ φ : ℝ} (hφ : 0 ≤ φ) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) {y : ℝ} (hy : 0 < y) : 0 ≤ d2Disutil σ φ P C ω y :=
  mul_nonneg (mul_pos (hP ω) (Real.rpow_pos_of_pos (hC ω) σ)).le
    (mul_nonneg hφ (Real.rpow_nonneg hy.le _))

/-- Galí (2015), eq. (10), p. 167: the generic horizon-`k` "profit" with `Q = βᵏ Z C^{−σ}/P`
and `Ψ = P C^σ y^{1+φ}/(1+φ)` is `βᵏ` times the union's period term. -/
theorem profit_unionQ {β σ φ ε : ℝ} (hφ : 0 ≤ φ) {Z C P W Nd : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω) (k : ℕ) (x : ℝ) :
    profit ε (unionQ β σ Z C P k) (W k) (Nd k) (disutil σ φ (P k) (C k)) x
      = β ^ k • unionSurplus σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x := by
  funext ω
  simp only [profit, unionQ, disutil, unionSurplus, Pi.smul_apply, smul_eq_mul]
  have h1 := (hP k ω).ne'
  have h2 := (Real.rpow_pos_of_pos (hC k ω) σ).ne'
  have h3 : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [Real.rpow_neg (hC k ω).le]
  field_simp

/-- Galí (2015), eq. (10), p. 167: **the union's objective is the generic reset objective**
with `Q = βᵏ Z C^{−σ}/P`, price index `W`, demand shifter `N^d` and money disutility `Ψ`. -/
theorem unionObjective_eq {θ β σ φ ε : ℝ} (hφ : 0 ≤ φ) {Z C P W Nd : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω) (t : ℕ) (x : ℝ) :
    unionObjective 𝔼 θ β σ φ ε Z C P W Nd t x
      = objective 𝔼 θ ε (unionQ β σ Z C P) W Nd (fun k => disutil σ φ (P k) (C k)) t x := by
  funext ω
  unfold unionObjective objective
  congr 1
  funext k
  rw [profit_unionQ hφ hP hC k x, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-! ### The first-order condition (11) -/

/-- Galí (2015), p. 168: `MRS_{t+k|t} = C_{t+k}^σ N_{t+k|t}^φ`, the marginal rate of
substitution relevant to the workers who reset their wage at `t`. -/
noncomputable def mrsReset (σ φ ε : ℝ) (C W Nd : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => C ω ^ σ * demand ε x W Nd ω ^ φ

/-- Galí (2015), eq. (11), p. 168: the summand
`N_{t+k|t} Z_{t+k} C_{t+k}^{−σ} (W*/P_{t+k} − M_w MRS_{t+k|t})`. -/
noncomputable def foc11Term (σ φ ε : ℝ) (Z C P W Nd : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => demand ε x W Nd ω * Z ω * C ω ^ (-σ) *
    (x / P ω - markup ε * mrsReset σ φ ε C W Nd x ω)

/-- Galí (2015), eq. (11), p. 168: the left-hand side
`∑ₖ (βθ_w)ᵏ E_t[N_{t+k|t} Z_{t+k} C_{t+k}^{−σ}(W*/P_{t+k} − M_w MRS_{t+k|t})]`. -/
noncomputable def foc11 (θ β σ φ ε : ℝ) (Z C P W Nd : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, (β * θ) ^ k * 𝔼.E t (foc11Term σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x) ω

/-- Galí (2015), eq. (11), p. 168: the generic summand `Q Y (W* − M Ψ'(Y))` is `βᵏ` times the
summand of (11). -/
theorem focTerm_union {β σ φ ε : ℝ} {Z C P W Nd : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (k : ℕ) (x : ℝ) :
    focTerm ε (unionQ β σ Z C P k) (W k) (Nd k) (dDisutil σ φ (P k) (C k)) x
      = β ^ k • foc11Term σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x := by
  funext ω
  simp only [focTerm, unionQ, dDisutil, foc11Term, mrsReset, Pi.smul_apply, smul_eq_mul]
  have h1 := (hP k ω).ne'
  have h2 := (Real.rpow_pos_of_pos (hC k ω) σ).ne'
  rw [Real.rpow_neg (hC k ω).le]
  field_simp

/-- Galí (2015), eq. (11), p. 168: the generic first-order sum is the left-hand side of (11). -/
theorem focSum_union {θ β σ φ ε : ℝ} {Z C P W Nd : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (t : ℕ) (x : ℝ) :
    focSum 𝔼 θ ε (unionQ β σ Z C P) W Nd (fun k => dDisutil σ φ (P k) (C k)) t x
      = foc11 𝔼 θ β σ φ ε Z C P W Nd t x := by
  funext ω
  unfold focSum foc11
  congr 1
  funext k
  rw [focTerm_union hP hC k x, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), §6.1.2.1, pp. 167–168 (**primitive assumptions on the union's problem**):
Calvo `θ_w ≥ 0`, `0 < β`, `θ_wβ < 1`, `ε_w > 1`, `φ ≥ 0`, and preference shifters,
consumption, prices, wages and labour-demand shifters in `[m, M̄]` with `m > 0`. -/
def UnionPrimitives (θ β φ ε m Mx : ℝ) (Z C P W Nd : ℕ → Ω → ℝ) : Prop :=
  0 ≤ θ ∧ 0 < β ∧ θ * β < 1 ∧ 1 < ε ∧ 0 ≤ φ ∧ 0 < m ∧
  (∀ k ω, m ≤ Z k ω ∧ Z k ω ≤ Mx) ∧ (∀ k ω, m ≤ C k ω ∧ C k ω ≤ Mx) ∧
  (∀ k ω, m ≤ P k ω ∧ P k ω ≤ Mx) ∧ (∀ k ω, m ≤ W k ω ∧ W k ω ≤ Mx) ∧
  (∀ k ω, m ≤ Nd k ω ∧ Nd k ω ≤ Mx)

/-- Galí (2015), pp. 167–168: a power of a number in `[lo, hi] ⊂ (0, ∞)` is at most
`lo^a + hi^a`, whatever the sign of `a`. -/
theorem rpow_le_add {a y lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    y ^ a ≤ lo ^ a + hi ^ a := by
  rcases le_total 0 a with ha | ha
  · have := Real.rpow_le_rpow (hlo.le.trans h1) h2 ha
    linarith [Real.rpow_nonneg hlo.le a]
  · have := Real.rpow_le_rpow_of_nonpos hlo h1 ha
    linarith [Real.rpow_nonneg (hlo.le.trans (h1.trans h2)) a]

/-- Galí (2015), pp. 167–168: bounds on the money-disutility factor
`0 < P C^σ ≤ M̄ (m^σ + M̄^σ)`. -/
theorem disutil_factor_bounds {σ m Mx : ℝ} (hm : 0 < m) {P C : Ω → ℝ}
    (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx) (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    0 < P ω * C ω ^ σ ∧ P ω * C ω ^ σ ≤ Mx * (m ^ σ + Mx ^ σ) := by
  have hP0 : 0 < P ω := hm.trans_le (hP ω).1
  have hc0 : 0 < C ω ^ σ := Real.rpow_pos_of_pos (hm.trans_le (hC ω).1) σ
  refine ⟨mul_pos hP0 hc0, mul_le_mul (hP ω).2 (rpow_le_add hm (hC ω).1 (hC ω).2) hc0.le
    (hP0.le.trans (hP ω).2)⟩

/-- Galí (2015), pp. 167–168 (**regularity of the union's problem from primitives**):
`UnionPrimitives` imply the generic `Primitives` of the reset problem with
`Q = βᵏ Z C^{−σ}/P`, `Q̄ = M̄ (m^{−σ} + M̄^{−σ})/m` and the money disutility `Ψ`. -/
theorem primitives_of_union {θ β σ φ ε m Mx : ℝ} {Z C P W Nd : ℕ → Ω → ℝ}
    (h : UnionPrimitives θ β φ ε m Mx Z C P W Nd) :
    Primitives θ β ε (Mx * (m ^ (-σ) + Mx ^ (-σ)) / m) m Mx (unionQ β σ Z C P) W Nd
      (fun k => disutil σ φ (P k) (C k)) (fun k => dDisutil σ φ (P k) (C k))
      (fun k => d2Disutil σ φ (P k) (C k)) := by
  obtain ⟨hθ, hβ, hθβ, hε, hφ, hm, hZ, hC, hP, hW, hN⟩ := h
  refine ⟨hθ, hβ.le, hθβ, hε, hm, fun k ω => ?_, hW, hN,
    fun k ω y hy => hasDerivAt_disutil hφ _ _ ω hy,
    fun k ω y hy => hasDerivAt_dDisutil σ φ _ _ ω hy, fun y₁ y₂ hy₁ => ?_⟩
  · have hP0 : 0 < P k ω := hm.trans_le (hP k ω).1
    have hZ0 : 0 < Z k ω := hm.trans_le (hZ k ω).1
    have hMx : 0 < Mx := hm.trans_le ((hZ k ω).1.trans (hZ k ω).2)
    have hc0 : 0 < C k ω ^ (-σ) := Real.rpow_pos_of_pos (hm.trans_le (hC k ω).1) _
    have hc : C k ω ^ (-σ) ≤ m ^ (-σ) + Mx ^ (-σ) := rpow_le_add hm (hC k ω).1 (hC k ω).2
    have hb : 0 < β ^ k := pow_pos hβ k
    refine ⟨by unfold unionQ; positivity, ?_⟩
    have h1 : β ^ k * Z k ω * C k ω ^ (-σ) ≤ β ^ k * Mx * (m ^ (-σ) + Mx ^ (-σ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hZ k ω).2 hb.le) hc hc0.le (mul_pos hb hMx).le
    have h2 := div_le_div₀ (mul_nonneg (mul_pos hb hMx).le (hc0.le.trans hc)) h1 hm (hP k ω).1
    calc unionQ β σ Z C P k ω ≤ β ^ k * Mx * (m ^ (-σ) + Mx ^ (-σ)) / m := h2
      _ = Mx * (m ^ (-σ) + Mx ^ (-σ)) / m * β ^ k := by ring
  · refine ⟨Mx * (m ^ σ + Mx ^ σ) * ((y₁ ^ (1 + φ) + y₂ ^ (1 + φ)) + (y₁ ^ φ + y₂ ^ φ) +
      φ * (y₁ ^ (φ - 1) + y₂ ^ (φ - 1))), fun k ω y hy1 hy2 => ?_⟩
    obtain ⟨hf0, hf⟩ := disutil_factor_bounds (σ := σ) hm (hP k) (hC k) ω
    have hy : 0 < y := hy₁.trans_le hy1
    have hS0 : 0 ≤ Mx * (m ^ σ + Mx ^ σ) := hf0.le.trans hf
    have a1 : 0 ≤ y₁ ^ (1 + φ) := Real.rpow_nonneg hy₁.le _
    have a2 : 0 ≤ y₂ ^ (1 + φ) := Real.rpow_nonneg (hy.le.trans hy2) _
    have a3 : 0 ≤ y₁ ^ φ := Real.rpow_nonneg hy₁.le _
    have a4 : 0 ≤ y₂ ^ φ := Real.rpow_nonneg (hy.le.trans hy2) _
    have a5 : 0 ≤ φ * (y₁ ^ (φ - 1) + y₂ ^ (φ - 1)) :=
      mul_nonneg hφ (add_nonneg (Real.rpow_nonneg hy₁.le _)
        (Real.rpow_nonneg (hy.le.trans hy2) _))
    have b1 : y ^ (1 + φ) / (1 + φ) ≤ y₁ ^ (1 + φ) + y₂ ^ (1 + φ) := by
      have hpow := rpow_le_add (a := 1 + φ) hy₁ hy1 hy2
      have hy0 : 0 ≤ y ^ (1 + φ) := Real.rpow_nonneg hy.le _
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have b2 : y ^ φ ≤ y₁ ^ φ + y₂ ^ φ := rpow_le_add hy₁ hy1 hy2
    have b3 : φ * y ^ (φ - 1) ≤ φ * (y₁ ^ (φ - 1) + y₂ ^ (φ - 1)) :=
      mul_le_mul_of_nonneg_left (rpow_le_add hy₁ hy1 hy2) hφ
    have c1 : 0 ≤ y ^ (1 + φ) / (1 + φ) :=
      div_nonneg (Real.rpow_nonneg hy.le _) (by linarith)
    have c2 : 0 ≤ y ^ φ := Real.rpow_nonneg hy.le _
    have c3 : 0 ≤ φ * y ^ (φ - 1) := mul_nonneg hφ (Real.rpow_nonneg hy.le _)
    have key : ∀ T B : ℝ, 0 ≤ T → T ≤ B → B ≤ (y₁ ^ (1 + φ) + y₂ ^ (1 + φ)) +
        (y₁ ^ φ + y₂ ^ φ) + φ * (y₁ ^ (φ - 1) + y₂ ^ (φ - 1)) →
        |P k ω * C k ω ^ σ * T| ≤ Mx * (m ^ σ + Mx ^ σ) * ((y₁ ^ (1 + φ) + y₂ ^ (1 + φ)) +
          (y₁ ^ φ + y₂ ^ φ) + φ * (y₁ ^ (φ - 1) + y₂ ^ (φ - 1))) := by
      intro T B hT hTB hB
      rw [abs_of_nonneg (mul_nonneg hf0.le hT)]
      exact mul_le_mul hf (hTB.trans hB) hT hS0
    exact ⟨key _ _ c1 b1 (by linarith), key _ _ c2 b2 (by linarith),
      key _ _ c3 b3 (by linarith)⟩

/-- Galí (2015), eq. (10)–(11), pp. 167–168 (**the derivative of the union's objective**):
under `UnionPrimitives`, at every `W* > 0` the objective (10) has derivative
`((1 − ε_w)/W*) × ∑ₖ (βθ_w)ᵏ E_t[N_{t+k|t} Z C^{−σ}(W*/P − M_w MRS_{t+k|t})]`. -/
theorem union_hasDerivAt {θ β σ φ ε m Mx : ℝ} {Z C P W Nd : ℕ → Ω → ℝ}
    (h : UnionPrimitives θ β φ ε m Mx Z C P W Nd) (t : ℕ) (ω : Ω) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => unionObjective 𝔼 θ β σ φ ε Z C P W Nd t z ω)
      ((1 - ε) / x * foc11 𝔼 θ β σ φ ε Z C P W Nd t x ω) x := by
  have hprim := primitives_of_union (σ := σ) h
  obtain ⟨-, -, -, -, hφ, hm, -, hC, hP, -, -⟩ := h
  have hP0 : ∀ k ω, 0 < P k ω := fun k ω => hm.trans_le (hP k ω).1
  have hC0 : ∀ k ω, 0 < C k ω := fun k ω => hm.trans_le (hC k ω).1
  have hd := hasDerivAt_objective_of_primitives 𝔼 hprim t ω hx
  have e1 : (fun z => unionObjective 𝔼 θ β σ φ ε Z C P W Nd t z ω)
      = fun z => objective 𝔼 θ ε (unionQ β σ Z C P) W Nd
          (fun k => disutil σ φ (P k) (C k)) t z ω :=
    funext fun z => by rw [unionObjective_eq 𝔼 hφ hP0 hC0]
  rw [e1, ← focSum_union 𝔼 hP0 hC0]
  exact hd

/-- Galí (2015), eq. (11), p. 168 (**(11) is necessary**): under `UnionPrimitives`, a local
maximum `W* > 0` of the union's objective (10) satisfies (11). -/
theorem union_foc_of_isLocalMax {θ β σ φ ε m Mx : ℝ} {Z C P W Nd : ℕ → Ω → ℝ}
    (h : UnionPrimitives θ β φ ε m Mx Z C P W Nd) {t : ℕ} {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => unionObjective 𝔼 θ β σ φ ε Z C P W Nd t z ω) x) :
    foc11 𝔼 θ β σ φ ε Z C P W Nd t x ω = 0 := by
  have hε := h.2.2.2.1
  have h0 := hmax.hasDerivAt_eq_zero (union_hasDerivAt 𝔼 h t ω hx)
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h0).resolve_left hc

/-- Galí (2015), eq. (11), p. 168 (**(11) is necessary and sufficient, with a unique
optimum**): under `UnionPrimitives` (so the disutility of work is convex, `φ ≥ 0`), a wage
`W* > 0` maximises the union's objective (10) over all positive wages if and only if it
satisfies (11); it is then the strict, hence unique, maximiser. -/
theorem union_isMaxOn_iff_foc {θ β σ φ ε m Mx : ℝ} {Z C P W Nd : ℕ → Ω → ℝ}
    (h : UnionPrimitives θ β φ ε m Mx Z C P W Nd) (t : ℕ) (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => unionObjective 𝔼 θ β σ φ ε Z C P W Nd t z ω) (Set.Ioi 0) x ↔
        foc11 𝔼 θ β σ φ ε Z C P W Nd t x ω = 0) ∧
      (foc11 𝔼 θ β σ φ ε Z C P W Nd t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        unionObjective 𝔼 θ β σ φ ε Z C P W Nd t y ω <
          unionObjective 𝔼 θ β σ φ ε Z C P W Nd t x ω) := by
  have hprim := primitives_of_union (σ := σ) h
  obtain ⟨-, -, -, -, hφ, hm, hZ, hC, hP, -, -⟩ := h
  have hP0 : ∀ k ω, 0 < P k ω := fun k ω => hm.trans_le (hP k ω).1
  have hC0 : ∀ k ω, 0 < C k ω := fun k ω => hm.trans_le (hC k ω).1
  have hMx : 0 < Mx := hm.trans_le ((hZ 0 ω).1.trans (hZ 0 ω).2)
  have hS : 0 < m ^ σ + Mx ^ σ := add_pos (Real.rpow_pos_of_pos hm σ) (Real.rpow_pos_of_pos hMx σ)
  have hQ0 : ∃ q, 0 < q ∧ ∀ ω', q ≤ unionQ β σ Z C P 0 ω' := by
    refine ⟨m * (m ^ σ + Mx ^ σ)⁻¹ / Mx, by positivity, fun ω' => ?_⟩
    have hc0 : 0 < C 0 ω' ^ σ := Real.rpow_pos_of_pos (hC0 0 ω') σ
    have hcinv : (m ^ σ + Mx ^ σ)⁻¹ ≤ C 0 ω' ^ (-σ) := by
      rw [Real.rpow_neg (hC0 0 ω').le]
      exact inv_anti₀ hc0 (rpow_le_add hm (hC 0 ω').1 (hC 0 ω').2)
    have h1 : m * (m ^ σ + Mx ^ σ)⁻¹ ≤ Z 0 ω' * C 0 ω' ^ (-σ) :=
      mul_le_mul (hZ 0 ω').1 hcinv (by positivity) (hm.le.trans (hZ 0 ω').1)
    have h2 := div_le_div₀ (mul_nonneg (hm.le.trans (hZ 0 ω').1)
      (Real.rpow_nonneg (hC0 0 ω').le _)) h1 (hP0 0 ω') (hP 0 ω').2
    simp only [unionQ, pow_zero, one_mul]
    exact h2
  have hconv : ∀ k ω' y, 0 < y → 0 ≤ (fun k => d2Disutil σ φ (P k) (C k)) k ω' y :=
    fun k ω' y hy => d2Disutil_nonneg hφ (hP0 k) (hC0 k) ω' hy
  have key := isMaxOn_iff_foc_of_primitives 𝔼 hprim hconv hQ0 t ω hx
  have e : ∀ z, objective 𝔼 θ ε (unionQ β σ Z C P) W Nd (fun k => disutil σ φ (P k) (C k)) t z ω
      = unionObjective 𝔼 θ β σ φ ε Z C P W Nd t z ω := fun z => by
    rw [unionObjective_eq 𝔼 hφ hP0 hC0]
  simp only [e, focSum_union 𝔼 hP0 hC0] at key
  exact key

/-! ### Flexible wages and the zero-inflation steady state (p. 168) -/

/-- Galí (2015), p. 168: on a probability space of labour types the CES index of a constant
cross-section `W(j) = c` is `c`; with flexible wages (`θ_w = 0`) every type resets, so
`W_t = W*_t`. -/
theorem cesIndex_const {J : Type*} [MeasurableSpace J] (μ : Measure J) [IsProbabilityMeasure μ]
    {ε c : ℝ} (hε : ε ≠ 1) (hc : 0 < c) : cesIndex μ ε (fun _ => c) = c := by
  unfold cesIndex
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact Real.rpow_rpow_inv hc.le (sub_ne_zero.2 (Ne.symm hε))

/-- Galí (2015), p. 168: when the reset wage equals the wage index, `N_{t|t} = N^d_t`, so
`MRS_{t|t} = C^σ (N^d)^φ`. -/
theorem flexible_wage_index {σ φ ε x : ℝ} (hx : 0 < x) (C Nd : Ω → ℝ) (ω : Ω) :
    demand ε x (fun _ => x) Nd ω = Nd ω ∧
      mrsReset σ φ ε C (fun _ => x) Nd x ω = C ω ^ σ * Nd ω ^ φ := by
  have h : demand ε x (fun _ => x) Nd ω = Nd ω := by
    simp [demand, div_self hx.ne']
  exact ⟨h, by rw [mrsReset, h]⟩

/-- Galí (2015), p. 168 (**flexible wages**): with `θ_w = 0`, if the current-period terms are
known at `t` and `W* > 0` is a local maximum of (10), then `W*/P_t = M_w MRS_{t|t}`: the
real wage is the frictionless markup `M_w` over the marginal rate of substitution. -/
theorem union_flexible {β σ φ ε : ℝ} (hε : 1 < ε) (hφ : 0 ≤ φ) {Z C P W Nd : ℕ → Ω → ℝ}
    (hZ : ∀ ω, 0 < Z 0 ω) (hC : ∀ k ω, 0 < C k ω) (hP : ∀ k ω, 0 < P k ω)
    (hW : ∀ ω, 0 < W 0 ω) (hN : ∀ ω, 0 < Nd 0 ω) {t : ℕ}
    (hknown : ∀ z, 𝔼.E t (unionSurplus σ φ ε (Z 0) (C 0) (P 0) (W 0) (Nd 0) z)
      = unionSurplus σ φ ε (Z 0) (C 0) (P 0) (W 0) (Nd 0) z) {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => unionObjective 𝔼 0 β σ φ ε Z C P W Nd t z ω) x) :
    x / P 0 ω = markup ε * mrsReset σ φ ε (C 0) (W 0) (Nd 0) x ω := by
  have hQ : ∀ ω, 0 < unionQ β σ Z C P 0 ω := fun ω => by
    simp only [unionQ, pow_zero, one_mul]
    exact div_pos (mul_pos (hZ ω) (Real.rpow_pos_of_pos (hC 0 ω) _)) (hP 0 ω)
  have hknown' : ∀ z, 𝔼.E t (profit ε (unionQ β σ Z C P 0) (W 0) (Nd 0)
      (disutil σ φ (P 0) (C 0)) z) = profit ε (unionQ β σ Z C P 0) (W 0) (Nd 0)
      (disutil σ φ (P 0) (C 0)) z := fun z => by
    rw [profit_unionQ hφ hP hC 0 z, pow_zero, one_smul, hknown]
  have hfun : (fun z => unionObjective 𝔼 0 β σ φ ε Z C P W Nd t z ω)
      = fun z => objective 𝔼 0 ε (unionQ β σ Z C P) W Nd
          (fun k => disutil σ φ (P k) (C k)) t z ω :=
    funext fun z => by rw [unionObjective_eq 𝔼 hφ hP hC]
  rw [hfun] at hmax
  have h := flexible_optimum 𝔼 (Ψ := fun k => disutil σ φ (P k) (C k))
    (dΨ := fun k => dDisutil σ φ (P k) (C k)) hε hx hQ hW hN
    (fun ω y hy => hasDerivAt_disutil hφ _ _ ω hy) hknown' hmax
  simp only [dDisutil] at h
  have hP0 := (hP 0 ω).ne'
  rw [mrsReset]
  conv_lhs => rw [h]
  field_simp

/-- Galí (2015), p. 168 (**the zero-inflation steady state**): with constant preference
shifter, consumption, prices, wages and labour-demand shifter, and the reset wage equal to
the wage index, (11) holds iff `W/P = M_w MRS` with `MRS = C^σ N^φ`. -/
theorem union_steadyState_foc_iff {β θ σ φ ε Zb Cb Pb Wb Nb : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hZ : 0 < Zb) (hC : 0 < Cb) (hW : 0 < Wb) (hN : 0 < Nb)
    (t : ℕ) (ω : Ω) :
    foc11 𝔼 θ β σ φ ε (fun _ _ => Zb) (fun _ _ => Cb) (fun _ _ => Pb) (fun _ _ => Wb)
        (fun _ _ => Nb) t Wb ω = 0 ↔ Wb / Pb = markup ε * (Cb ^ σ * Nb ^ φ) := by
  have hY : ∀ ω' : Ω, demand ε Wb (fun _ => Wb) (fun _ => Nb) ω' = Nb := fun ω' =>
    (flexible_wage_index (σ := σ) (φ := φ) hW (fun _ => Cb) (fun _ => Nb) ω').1
  have hterm : foc11Term σ φ ε (fun _ => Zb) (fun _ => Cb) (fun _ => Pb) (fun _ => Wb)
      (fun _ => Nb) Wb = fun (_ : Ω) => Nb * Zb * Cb ^ (-σ) *
        (Wb / Pb - markup ε * (Cb ^ σ * Nb ^ φ)) := by
    funext ω'
    simp only [foc11Term, mrsReset, hY]
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hsum : foc11 𝔼 θ β σ φ ε (fun _ _ => Zb) (fun _ _ => Cb) (fun _ _ => Pb)
      (fun _ _ => Wb) (fun _ _ => Nb) t Wb ω
      = (1 - β * θ)⁻¹ * (Nb * Zb * Cb ^ (-σ) * (Wb / Pb - markup ε * (Cb ^ σ * Nb ^ φ))) := by
    simp only [foc11, hterm, 𝔼.const]
    rw [← tsum_geometric_of_lt_one hβθ0 hβθ1, ← tsum_mul_right]
  rw [hsum]
  have h1 : (1 - β * θ)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h2 : Nb * Zb * Cb ^ (-σ) ≠ 0 := (mul_pos (mul_pos hN hZ) (Real.rpow_pos_of_pos hC _)).ne'
  constructor
  · intro h0
    have := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h1)).resolve_left h2
    linarith
  · intro h0
    rw [h0, sub_self, mul_zero, mul_zero]

/-! ### The log-linear wage-setting rule (12) -/

/-- Galí (2015), eqs. (11)–(12), p. 168: the left-hand side of (11) is the generic `focLHS`
with weights `βᵏ N_{t+k|t} Z C^{−σ}/P` and nominal marginal rates of substitution
`P_{t+k} MRS_{t+k|t}`; its log is `ψ_{t+k|t} = p_{t+k} + mrs_{t+k|t}`, so `eq12_iff` reads
`w*_t = μ^w + (1 − βθ_w) ∑ₖ (βθ_w)ᵏ E_t[mrs_{t+k|t} + p_{t+k}]`, eq. (12). -/
theorem foc11_eq_focLHS {θ β σ φ ε : ℝ} {Z C P W Nd : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω)
    (t : ℕ) (x : ℝ) :
    foc11 𝔼 θ β σ φ ε Z C P W Nd t x
      = focLHS 𝔼 θ ε (fun k ω => β ^ k * (demand ε x (W k) (Nd k) ω * Z k ω * C k ω ^ (-σ) /
          P k ω)) x (fun k ω => P k ω * mrsReset σ φ ε (C k) (W k) (Nd k) x ω) t := by
  funext ω
  unfold foc11 focLHS
  congr 1
  funext k
  have hpt : (fun ω' => β ^ k * (demand ε x (W k) (Nd k) ω' * Z k ω' * C k ω' ^ (-σ) /
      P k ω') * (x - markup ε * (P k ω' * mrsReset σ φ ε (C k) (W k) (Nd k) x ω')))
      = β ^ k • foc11Term σ φ ε (Z k) (C k) (P k) (W k) (Nd k) x := by
    funext ω'
    simp only [foc11Term, Pi.smul_apply, smul_eq_mul]
    have := (hP k ω').ne'
    field_simp
  rw [hpt, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), p. 169 (**`mrs_{t+k|t}` versus the economy's `mrs_{t+k}`, exact**): with
labour demand (3) for the type, `N_{t+k|t} = (W*/W)^{−ε_w} N^d`, and aggregate employment
`N = Δ_w N^d` (p. 170), the log of `MRS_{t+k|t}` is
`mrs_{t+k} − ε_w φ (w* − w_{t+k}) − φ log Δ_w`, where `mrs_{t+k} = σ c + φ n`. -/
theorem log_mrsReset {σ φ ε x : ℝ} (hx : 0 < x) {C W Nd : Ω → ℝ} (hC : ∀ ω, 0 < C ω)
    (hW : ∀ ω, 0 < W ω) (hN : ∀ ω, 0 < Nd ω) {Δ : ℝ} (hΔ : 0 < Δ) (ω : Ω) :
    Real.log (mrsReset σ φ ε C W Nd x ω)
      = (σ * Real.log (C ω) + φ * Real.log (Δ * Nd ω)) -
        ε * φ * (Real.log x - Real.log (W ω)) - φ * Real.log Δ := by
  have hr : 0 < x / W ω := div_pos hx (hW ω)
  have hd : 0 < demand ε x W Nd ω := demand_pos hx hW hN ω
  have hld : Real.log (demand ε x W Nd ω) = -ε * (Real.log x - Real.log (W ω)) +
      Real.log (Nd ω) := by
    rw [demand, Real.log_mul (Real.rpow_pos_of_pos hr _).ne' (hN ω).ne', Real.log_rpow hr,
      Real.log_div hx.ne' (hW ω).ne']
  rw [mrsReset, Real.log_mul (Real.rpow_pos_of_pos (hC ω) _).ne'
    (Real.rpow_pos_of_pos hd _).ne', Real.log_rpow (hC ω), Real.log_rpow hd, hld,
    Real.log_mul hΔ.ne' (hN ω).ne']
  ring

/-- Galí (2015), p. 169 (**the `mrs` relation holds to first order**): along a family of
wage distributions `w(j) = w̄ + s z(j)`, the correction term `φ log Δ_w` of `log_mrsReset`
vanishes at `s = 0` and has zero derivative there. -/
theorem mrs_correction_first_order {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B)
    {ε : ℝ} (hε : ε ≠ 1) (φ wbar : ℝ) :
    φ * Real.log (wageDisp μ ε (fun j => Real.exp (wbar + 0 * z j))) = 0 ∧
      HasDerivAt (fun s => φ * Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))))
        0 0 := by
  obtain ⟨h0, hd⟩ := log_dispIntegral_family_first_order (μ := μ) hz hB hε (-ε) wbar
  refine ⟨by rw [wageDisp, h0, mul_zero], ?_⟩
  simpa [wageDisp] using hd.const_mul φ

/-! ### The recursive form (13) -/

/-- Galí (2015), p. 169: the gap of the economy's average log wage markup from its
steady-state value, `μ̂^w_t = (w_t − p_t − mrs_t) − μ^w`. -/
noncomputable def markupGap (μw : ℝ) (w p mrs : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (w t ω - p t ω - mrs t ω) - μw

/-- Galí (2015), eqs. (12)–(13), p. 169 (**the recursive wage-setting rule**). Let the reset
wage satisfy (12), `w*_t = μ^w + (1 − βθ_w) ∑ₖ (βθ_w)ᵏ E_t[mrs_{t+k|t} + p_{t+k}]`, with
`mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w*_t − w_{t+k})` (p. 169), for bounded adapted `w`, `p`, `mrs`
and adapted `w*`. Then (i) (13) holds,
`w*_t = βθ_w E_t w*_{t+1} + (1 − βθ_w)(w_t − (1 + ε_wφ)⁻¹ μ̂^w_t)`; (ii) `w*` is the forward
series; (iii) it is the **unique bounded solution** of (13). -/
theorem eq13 {β θ ε φ μw M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hεφ : 0 ≤ ε * φ) {wstar w p mrs : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = μw + (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + p (t + k) ω') ω)
    (hmrs : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω)) :
    (∀ t, wstar t = (β * θ) • 𝔼.E t (wstar (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) ∧
    wstar = 𝔼.forwardSeries (β * θ)
      (fun t => (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) ∧
    ∀ z : ℕ → Ω → ℝ, BoundedProc z → (∀ t, z t = (β * θ) • 𝔼.E t (z (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) → z = wstar := by
  set a := β * θ with ha
  have ha0 : 0 ≤ a := mul_nonneg hβ0 hθ0
  have ha1 : a < 1 := by nlinarith
  have hd : 1 + ε * φ ≠ 0 := by linarith
  set c := (1 + ε * φ)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.mpr (by linarith)
  set u : ℕ → Ω → ℝ := fun t => (1 - a) • (w t - c • markupGap μw w p mrs t) with hu
  set y : ℕ → Ω → ℝ := fun s ω => mrs s ω + ε * φ * w s ω + p s ω with hy
  -- bounds and adaptedness
  have hyb : ∀ t ω, |y t ω| ≤ M + ε * φ * M + M := fun t ω => by
    have h1 := abs_add_le (mrs t ω + ε * φ * w t ω) (p t ω)
    have h2 := abs_add_le (mrs t ω) (ε * φ * w t ω)
    have h3 : |ε * φ * w t ω| ≤ ε * φ * M := by
      rw [abs_mul, abs_of_nonneg hεφ]
      exact mul_le_mul_of_nonneg_left (hw t ω) hεφ
    simp only [hy]
    linarith [hm t ω, hp t ω]
  have hgap : ∀ t, markupGap μw w p mrs t = w t - p t - mrs t - fun _ => μw := fun t => rfl
  have hub : ∀ t ω, |u t ω| ≤ (1 - a) * (M + c * (3 * M + |μw|)) := fun t ω => by
    have hg : |markupGap μw w p mrs t ω| ≤ 3 * M + |μw| := by
      simp only [markupGap]
      have := abs_sub (w t ω - p t ω - mrs t ω) μw
      have := abs_sub (w t ω - p t ω) (mrs t ω)
      have := abs_sub (w t ω) (p t ω)
      linarith [hw t ω, hp t ω, hm t ω]
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hc0]
    exact add_le_add (hw t ω) (mul_le_mul_of_nonneg_left hg hc0)
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu, hgap, map_smul, map_sub, 𝔼.const, hwa t, hpa t, hma t]
  -- `w*` is the forward series of `u`
  have hS : ∀ t ω, Summable fun k => a ^ k * 𝔼.E t (y (t + k)) ω :=
    fun t ω => 𝔼.forwardSeries_summable ha0 ha1 hyb t ω
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  have hkey : ∀ t ω, wstar t ω = c * (μw + (1 - a) * ∑' k, a ^ k * 𝔼.E t (y (t + k)) ω) := by
    intro t ω
    have hin : ∀ k, 𝔼.E t (fun ω' => mrsR t k ω' + p (t + k) ω') ω
        = 𝔼.E t (y (t + k)) ω - ε * φ * wstar t ω := by
      intro k
      have hf : (fun ω' => mrsR t k ω' + p (t + k) ω') = y (t + k) - (ε * φ) • wstar t := by
        funext ω'
        simp only [hy, hmrs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hf, map_sub, map_smul, hsa t]
      rfl
    have h := h12 t ω
    simp_rw [hin, mul_sub] at h
    rw [Summable.tsum_sub (hS t ω) (hgeo.mul_right _), tsum_mul_right,
      tsum_geometric_of_lt_one ha0 ha1] at h
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    rw [hc, eq_inv_mul_iff_mul_eq₀ hd]
    field_simp at h
    linear_combination h
  have hfs : ∀ t, wstar t = 𝔼.forwardSeries a u t := by
    intro t
    funext ω
    have hEu : ∀ k, 𝔼.E t (u (t + k)) ω = (1 - a) * c * (𝔼.E t (y (t + k)) ω + μw) := by
      intro k
      have hf : u (t + k) = ((1 - a) * c) • (y (t + k) + fun _ => μw) := by
        funext ω'
        simp only [hu, hy, markupGap, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
        rw [hc]
        field_simp
        ring
      rw [hf, map_smul, map_add, 𝔼.const]
      rfl
    change wstar t ω = ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
    simp_rw [hEu]
    have e : ∀ k, a ^ k * ((1 - a) * c * (𝔼.E t (y (t + k)) ω + μw))
        = (1 - a) * c * (a ^ k * 𝔼.E t (y (t + k)) ω) + (1 - a) * c * μw * a ^ k :=
      fun k => by ring
    simp_rw [e]
    rw [Summable.tsum_add ((hS t ω).mul_left _) (hgeo.mul_left _), tsum_mul_left,
      tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, hkey t ω]
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    field_simp
    ring
  have hfs' : wstar = 𝔼.forwardSeries a u := funext hfs
  refine ⟨fun t => ?_, hfs', fun z hz hzrec => ?_⟩
  · rw [hfs', 𝔼.forwardSeries_solves ha0 ha1 hub hua t]
  · rw [hfs']
    exact 𝔼.eq_forwardSeries ha0 ha1 hub hua hzrec hz

end Gali.StickyWagesPrices.WageSetting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Wage inflation dynamics

Galí (2015), Chapter 6, §6.1.2.2 (pp. 169–170), eqs. (14)–(15).

## The cross-section of wages

Labour types form a measure space `(F, m)`. In period `t` the types in a measurable set `S`
(mass `1 − θ_w`) reset their wage to the common `W*_t`; the others keep last period's wage, and
the non-resetters are a representative subsample. `wage_dist_law_of_motion` derives the law of
motion of the wage distribution `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{W*_t}`, `wage_recursion` and
`wage_index_recursion` the CES wage-index recursion of p. 169,
`W_t^{1−ε_w} = θ_w W_{t−1}^{1−ε_w} + (1 − θ_w)(W*_t)^{1−ε_w}`, and `lottery_model` /
`wage_recursion_lottery` show the hypotheses hold for an explicit Calvo lottery. The
cross-section of **log** wages obeys the same law (`log_wage_law_of_motion`), which is the
`wageMix` recursion behind the wage Lemma 2 of `WageDispersion`. All of this is restated from
the Chapter 3 project (`CalvoIndex.lean`), with prices replaced by wages.

## Main results

* `log_wageIndex_eq`, `hasDerivAt_inflFn`, `eq14_tangent`: (14) is the exact first-order
  approximation of the wage-index recursion: `log W_t = w_{t−1} + f(w*_t − w_{t−1})` with
  `f(0) = 0`, `f'(0) = 1 − θ_w`, and the tangent line is `θ_w w_{t−1} + (1 − θ_w) w*_t`.
* `eq15_iff`: given (14), the recursive wage-setting rule (13) holds at every date iff the
  **wage-inflation equation (15)** `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t` does, with
  `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`.
* `lambdaW_pos`, `lambdaW_strictAntiOn_theta`, `lambdaW_strictAntiOn_eps`,
  `lambdaW_strictAntiOn_phi`: `λ_w > 0`, strictly decreasing in `θ_w`, `ε_w` and `φ` (p. 170).
-/

namespace Gali.StickyWagesPrices.WageInflation

open MeasureTheory
open Gali.StickyWagesPrices.LaborAggregation Gali.StickyWagesPrices.WageDispersion

/-- Galí (2015), §6.1.2.2, p. 169: integrating against the Calvo mixture
`θ ν + (1 − θ) δ_{W*}` gives `θ ∫ f dν + (1 − θ) f(W*)`. -/
theorem integral_wage_mix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (Wstar : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar)
      = θ * ∫ x, f x ∂ν + (1 - θ) * f Wstar := by
  have hd : Integrable f (Measure.dirac Wstar) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), eq. (4), p. 165, at the level of wage distributions: if
`ν_t = θ ν_{t−1} + (1 − θ) δ_{W*}`, where `ν_{t−1}` has a positive, integrable
`∫ p^{1−ε}`, then with `W_s = (∫ p^{1−ε} dν_s)^{1/(1−ε)}`,
`(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`. -/
theorem wage_recursion_of_dist {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1)
    {νprev : Measure ℝ} {Wstar : ℝ} (hWstar : 0 < Wstar)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar) ε
        (fun x => x) / cesIndex νprev ε (fun x => x)) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex νprev ε (fun x => x)) ^ (1 - ε) := by
  have hmix := integral_wage_mix h0 h1.le Wstar hint
  have hnew : 0 < θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Wstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Wstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hWstar _)
    have : 0 ≤ θ * ∫ x, x ^ (1 - ε) ∂νprev := mul_nonneg h0 hpos.le
    linarith
  have hI := cesIndex_pos (W := fun x : ℝ => x) hpos
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hPt : cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar)
      ε (fun x => x) ^ (1 - ε) = θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Wstar ^ (1 - ε) := by
    unfold cesIndex
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) •
      Measure.dirac Wstar) ε (fun x => x) := by
    unfold cesIndex
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hI.le, Real.div_rpow hWstar.le hI.le, hPt,
    cesIndex_rpow (W := fun x : ℝ => x) hε hpos]
  field_simp

/-- Galí (2015), §6.1.2.2, p. 169 (**law of motion of the wage distribution**). Labour types
`(F, m)`; those in `S` (mass `1 − θ`) reset to `W*`, the rest keep `w_{t−1}`, and the
non-resetters are a representative subsample (their wage distribution is `θ` times that of
all labour types). Then `ν_t = θ ν_{t−1} + (1 − θ) δ_{W*}` where `ν_s = m.map p_s`. -/
theorem wage_dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hnow : Measurable pnow)
    {Wstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Wstar) (hkeep : ∀ i ∉ S, pnow i = pprev i)
    (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • m.map pprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Wstar := by
    rw [Measure.map_congr (g := fun _ => Wstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = (m.restrict Sᶜ).map pprev :=
    Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, add_comm]

/-- Galí (2015), the wage-index recursion, p. 169 (**Calvo wage-index recursion**),
derived from the type-level model of `wage_dist_law_of_motion`: with `W_s` the CES wage index of
the cross-section `p_s`, `(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*_t/W_{t−1})^{1−ε}`. -/
theorem wage_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, pnow i = Wstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - ε) ∂m) :
    (cesIndex m ε pnow / cesIndex m ε pprev) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex m ε pprev) ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - ε) ∂m = ∫ x, x ^ (1 - ε) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hidx : ∀ p : F → ℝ, Measurable p →
      cesIndex m ε p = cesIndex (m.map p) ε (fun x => x) := fun p hp => by
    unfold cesIndex
    rw [hmap p hp]
  have hint' : Integrable (fun x : ℝ => x ^ (1 - ε)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hidx pnow hnow, hidx pprev hprev, wage_dist_law_of_motion m hS hnow hreset hkeep hmass hind]
  rw [hmap pprev hprev] at hpos
  exact wage_recursion_of_dist hε h0 h1 hWstar hint' hpos

/-- Galí (2015), §6.1.2.1, p. 167 (**the Calvo lottery is a representative subsample**): for any
probability space of labour types `(Ω, μ₀)` with wages `p`, give each type an independent uniform
draw `u ∈ [0, 1]` and let it reset iff `u > θ`. On `Ω × [0, 1]` with the product measure the
resetters have mass `1 − θ`, the non-resetters' wage distribution is `θ` times the full one,
and the full distribution is that of `p` under `μ₀`. -/
theorem lottery_model {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {p : Ω → ℝ} (hp : Measurable p) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.univ ×ˢ Set.Ioi θ)
        = ENNReal.ofReal (1 - θ) ∧
      ((μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).restrict (Set.univ ×ˢ Set.Ioi θ)ᶜ).map
          (fun x => p x.1)
        = ENNReal.ofReal θ •
          (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) ∧
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) = μ₀.map p := by
  have hfst : ∀ ν : Measure ℝ, SFinite ν →
      (μ₀.prod ν).map (fun x => p x.1) = ν Set.univ • μ₀.map p := by
    intro ν _
    have : (fun x : Ω × ℝ => p x.1) = p ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map hp measurable_fst, Measure.map_fst_prod, Measure.map_smul]
    exact hp.aemeasurable
  have hall : (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1)
      = μ₀.map p := by
    rw [hfst _ inferInstance, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  refine ⟨?_, ?_, hall⟩
  · rw [Measure.prod_prod, measure_univ, one_mul,
      Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi θ ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc θ 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
    rw [this, Real.volume_Ioc]
  · have hc : (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ))ᶜ = Set.univ ×ˢ Set.Iic θ := by
      ext x
      simp
    rw [hc, ← Measure.prod_restrict, Measure.restrict_univ, hfst _ inferInstance, hall,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic θ ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 θ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]

/-- Galí (2015), the wage-index recursion, p. 169, for the **explicit Calvo-lottery
economy** of `lottery_model`: labour types `(ω, u) ∈ Ω × [0, 1]`, last period's wage `w ω`, and
this period's wage `W*` if `u > θ` and `w ω` otherwise. With `W_{t−1}` the index of `w`
under `μ₀`, `(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`. -/
theorem wage_recursion_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - ε)) μ₀)
    {Wstar : ℝ} (hWstar : 0 < Wstar) :
    (cesIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε
        (fun x => if θ < x.2 then Wstar else p x.1) / cesIndex μ₀ ε p) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex μ₀ ε p) ^ (1 - ε) := by
  obtain ⟨hmass, hind, hall⟩ := lottery_model μ₀ hp h0 h1.le
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hpp : Measurable fun x : Ω × ℝ => p x.1 := hp.comp measurable_fst
  have hI : ∫ x, p x.1 ^ (1 - ε) ∂(μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ ω, p ω ^ (1 - ε) ∂μ₀ := by
    rw [← integral_map hpp.aemeasurable hmeas.aestronglyMeasurable, hall,
      integral_map hp.aemeasurable hmeas.aestronglyMeasurable]
  have hidx : cesIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε (fun x => p x.1)
      = cesIndex μ₀ ε p := by
    unfold cesIndex
    rw [hI]
  have hint' : Integrable (fun x => p x.1 ^ (1 - ε))
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hp.aemeasurable).2 hint
    rw [← hall] at this
    exact (integrable_map_measure hmeas.aestronglyMeasurable hpp.aemeasurable).1 this
  have hpos : 0 < ∫ ω, p ω ^ (1 - ε) ∂μ₀ :=
    integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ₀)
      (fun ω => Real.rpow_pos_of_pos (hp0 ω) _) hint
  have hS : MeasurableSet (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hnow : Measurable fun x : Ω × ℝ => if θ < x.2 then Wstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine wage_recursion _ hε h0 h1 hS hpp hnow hWstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Galí (2015), §6.1.2.1, p. 167 (**decomposition by date of last reset**): if the wage
distribution follows `ν_{s+1} = θ ν_s + (1 − θ) δ_{W*_{s+1}}`, then
`ν_{t+k} = θᵏ ν_t + ∑_{h=1}^{k} (1 − θ) θ^{k−h} δ_{W*_{t+h}}` (written with `h ↦ h + 1`): a
mass `θᵏ` still charges the wages of date `t`, and a mass `(1 − θ)θ^{k−h}` last reset at
`t + h`. -/
theorem dist_k_step {θ : ℝ} (h0 : 0 ≤ θ) {ν : ℕ → Measure ℝ} {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) :
    ν (t + k) = ENNReal.ofReal (θ ^ k) • ν t + ∑ h ∈ Finset.range k,
      ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h)) • Measure.dirac (Wstar (t + h + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hlaw, ih, smul_add, Finset.smul_sum, smul_smul, Finset.sum_range_succ]
    simp_rw [smul_smul]
    have hc : ∀ h ∈ Finset.range k, ENNReal.ofReal θ * ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h))
        = ENNReal.ofReal ((1 - θ) * θ ^ (k + 1 - 1 - h)) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [← ENNReal.ofReal_mul h0]
      congr 1
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl fun h hh => by rw [hc h hh], ← ENNReal.ofReal_mul h0, ← pow_succ',
      show k + 1 - 1 - k = 0 by omega, pow_zero, mul_one, add_assoc]

/-- Galí (2015), §6.1.2.1, p. 167: the probabilities in (10) sum to one,
`θᵏ + (1 − θ) ∑_{h=1}^{k} θ^{k−h} = 1`. -/
theorem prob_identity (θ : ℝ) (k : ℕ) :
    θ ^ k + (1 - θ) * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have hs : ∑ h ∈ Finset.Icc 1 k, θ ^ (k + 1 - h) = θ * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_Icc] at hh
      rw [show k + 1 - h = (k - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), §6.1.2.1, p. 167: the identity of `prob_identity` in the indexing of
`dist_k_step`, `θᵏ + ∑_{h<k} (1 − θ) θ^{k−1−h} = 1`. -/
theorem prob_identity_range (θ : ℝ) (k : ℕ) :
    θ ^ k + ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 - 1 - k = 0 by omega, pow_zero]
    have hs : ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k + 1 - 1 - h)
        = θ * ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), §6.1.2.1, p. 167: if `ν_t` is a probability distribution, so is `ν_{t+k}`;
the masses of `dist_k_step` add up to one. -/
theorem dist_k_step_mass {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ}
    {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) (hν : ν t Set.univ = 1) : ν (t + k) Set.univ = 1 := by
  have hnn : ∀ h ∈ Finset.range k, 0 ≤ (1 - θ) * θ ^ (k - 1 - h) :=
    fun h _ => mul_nonneg (by linarith) (pow_nonneg h0 _)
  rw [dist_k_step h0 hlaw t k]
  simp only [Measure.coe_add, Measure.coe_smul, Measure.coe_finsetSum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, measure_univ, hν, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (pow_nonneg h0 _)
    (Finset.sum_nonneg hnn), prob_identity_range, ENNReal.ofReal_one]

/-- Galí (2015), p. 169: a positive number `y` satisfies `y^{1−ε} = 1` iff `y = 1` (`ε ≠ 1`). -/
theorem rpow_eq_one_iff {ε y : ℝ} (hε : ε ≠ 1) (hy : 0 < y) : y ^ (1 - ε) = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
    rw [← Real.rpow_rpow_inv hy.le hsub, h, Real.one_rpow]
  · rintro rfl
    exact Real.one_rpow _

/-- Galí (2015), p. 169 (**zero-wage-inflation steady state**): under the wage-index recursion,
gross wage inflation is one
iff the reset wage equals last period's wage index, `Π = 1 ⟺ W*/W_{t−1} = 1`
(`0 ≤ θ < 1`, `ε ≠ 1`). -/
theorem zero_wage_inflation_iff {θ ε Pi x : ℝ} (h1 : θ < 1) (hε : ε ≠ 1) (hPi : 0 < Pi)
    (hx : 0 < x) (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) : Pi = 1 ↔ x = 1 := by
  rw [← rpow_eq_one_iff hε hPi, ← rpow_eq_one_iff hε hx, hrec]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  constructor
  · intro h
    have h' : (1 - θ) * x ^ (1 - ε) = (1 - θ) * 1 := by linarith
    exact mul_left_cancel₀ this h'
  · intro h
    rw [h]
    ring

/-- Galí (2015), p. 169, in levels: under the wage-index recursion, `W_t = W_{t−1}` iff
`W*_t = W_{t−1}`, and then
`W*_t = W_{t−1} = W_t`. -/
theorem zero_wage_inflation_levels {θ ε Pt Pprev Wstar : ℝ} (h1 : θ < 1) (hε : ε ≠ 1)
    (hPt : 0 < Pt) (hPprev : 0 < Pprev) (hWstar : 0 < Wstar)
    (hrec : (Pt / Pprev) ^ (1 - ε) = θ + (1 - θ) * (Wstar / Pprev) ^ (1 - ε)) :
    (Pt = Pprev ↔ Wstar = Pprev) ∧ (Pt = Pprev → Wstar = Pprev ∧ Wstar = Pt) := by
  have h := zero_wage_inflation_iff h1 hε (div_pos hPt hPprev) (div_pos hWstar hPprev) hrec
  rw [div_eq_one_iff_eq hPprev.ne', div_eq_one_iff_eq hPprev.ne'] at h
  exact ⟨h, fun he => ⟨h.1 he, (h.1 he).trans he.symm⟩⟩

/-- Galí (2015), eq. (14), p. 169: log gross wage inflation as a function of the log relative reset
wage `y = log(W*_t/W_{t−1})`, as implied by (7):
`π(y) = (1 − ε)⁻¹ log(θ + (1 − θ) e^{(1−ε) y})`. -/
noncomputable def inflFn (θ ε y : ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ + (1 - θ) * Real.exp ((1 - ε) * y))

/-- Galí (2015), eq. (14), p. 169: the exact (nonlinear) wage-index recursion says
`log Π_t = inflFn θ ε (log(W*_t/W_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε Pi x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε (Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hx, mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), p. 169: at the zero-wage-inflation steady state (`W* = W_{t−1}`, i.e. `y = 0`),
`π = 0`. -/
theorem inflFn_zero (θ ε : ℝ) : inflFn θ ε 0 = 0 := by
  simp [inflFn]

/-- Galí (2015), eq. (14), p. 169 (**exact derivative**): `d log Π_t / d log(W*_t/W_{t−1}) = 1 − θ`
at the zero-wage-inflation steady state; i.e. `π_t = (1 − θ)(p*_t − p_{t−1})` is the first-order
approximation of (7). -/
theorem hasDerivAt_inflFn (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) : HasDerivAt (inflFn θ ε) (1 - θ) 0 := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h1 : HasDerivAt (fun y : ℝ => (1 - ε) * y) (1 - ε) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - ε)
  have h2 := HasDerivAt.exp h1
  have h3 := HasDerivAt.const_add θ (HasDerivAt.const_mul (1 - θ) h2)
  have hne : θ + (1 - θ) * Real.exp ((1 - ε) * 0) ≠ 0 := by simp
  have h4 := HasDerivAt.const_mul (1 - ε)⁻¹ (HasDerivAt.log h3 hne)
  unfold inflFn
  convert h4 using 1
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Galí (2015), eq. (14), p. 169: the remainder of the log-linear approximation is
`o(y)`, `inflFn θ ε y − (1 − θ) y = o(y)` as `y → 0`. -/
theorem inflFn_isLittleO (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) :
    (fun y => inflFn θ ε y - (1 - θ) * y) =o[nhds 0] fun y => y := by
  have h := (hasDerivAt_iff_isLittleO.1 (hasDerivAt_inflFn θ hε))
  simpa [inflFn_zero, mul_comm] using h


/-! ### The wage-index recursion in levels and the log-wage cross-section -/

/-- Galí (2015), p. 169: the wage-index recursion in relative form,
`(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`, is the book's level form
`W_t^{1−ε} = θ W_{t−1}^{1−ε} + (1 − θ)(W*)^{1−ε}`. -/
theorem recursion_levels_iff {θ ε Wt Wp Ws : ℝ} (hWt : 0 < Wt) (hWp : 0 < Wp) (hWs : 0 < Ws) :
    (Wt / Wp) ^ (1 - ε) = θ + (1 - θ) * (Ws / Wp) ^ (1 - ε) ↔
      Wt ^ (1 - ε) = θ * Wp ^ (1 - ε) + (1 - θ) * Ws ^ (1 - ε) := by
  have hp : 0 < Wp ^ (1 - ε) := Real.rpow_pos_of_pos hWp _
  rw [Real.div_rpow hWt.le hWp.le, Real.div_rpow hWs.le hWp.le]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 169 (**the CES wage-index recursion, level form**), derived from the
type-level Calvo model of `wage_recursion`: `W_t^{1−ε_w} = θ_w W_{t−1}^{1−ε_w} +
(1 − θ_w)(W*_t)^{1−ε_w}`. -/
theorem wage_index_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {wprev wnow : F → ℝ} (hprev : Measurable wprev) (hnow : Measurable wnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, wnow i = Wstar)
    (hkeep : ∀ i ∉ S, wnow i = wprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map wprev = ENNReal.ofReal θ • m.map wprev)
    (hint : Integrable (fun i => wprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, wprev i ^ (1 - ε) ∂m) (hnowpos : 0 < cesIndex m ε wnow) :
    cesIndex m ε wnow ^ (1 - ε)
      = θ * cesIndex m ε wprev ^ (1 - ε) + (1 - θ) * Wstar ^ (1 - ε) :=
  (recursion_levels_iff hnowpos (cesIndex_pos hpos) hWstar).1
    (wage_recursion m hε h0 h1 hS hprev hnow hWstar hreset hkeep hmass hind hint hpos)

/-- Galí (2015), p. 169 and App. 6.1, p. 192 (**law of motion of the cross-section of log
wages**): under the type-level Calvo model, the distribution of log wages follows the
`wageMix` recursion `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{w*_t}` used in the wage Lemma 2. The
representative-subsample hypothesis on wages implies it for log wages. -/
theorem log_wage_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {wprev wnow : F → ℝ} (hprev : Measurable wprev)
    (hnow : Measurable wnow) {Wstar : ℝ} (hreset : ∀ i ∈ S, wnow i = Wstar)
    (hkeep : ∀ i ∉ S, wnow i = wprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map wprev = ENNReal.ofReal θ • m.map wprev) :
    m.map (fun i => Real.log (wnow i))
      = wageMix θ (m.map (fun i => Real.log (wprev i))) (Real.log Wstar) := by
  have hlog : Measurable Real.log := Real.measurable_log
  have hind' : (m.restrict Sᶜ).map (fun i => Real.log (wprev i))
      = ENNReal.ofReal θ • m.map (fun i => Real.log (wprev i)) := by
    have e1 : (fun i => Real.log (wprev i)) = Real.log ∘ wprev := rfl
    rw [e1, ← Measure.map_map hlog hprev, ← Measure.map_map hlog hprev, hind,
      Measure.map_smul _ hlog.aemeasurable]
  exact wage_dist_law_of_motion m hS (hlog.comp hnow)
    (fun i hi => by simp only [Function.comp_apply, hreset i hi])
    (fun i hi => by simp only [Function.comp_apply, hkeep i hi]) hmass hind'

/-! ### Eq. (14) as the exact first-order approximation -/

/-- Galí (2015), p. 169: the wage-index recursion gives, exactly,
`log W_t = log W_{t−1} + f(log W*_t − log W_{t−1})` with `f = inflFn θ_w ε_w`. -/
theorem log_wageIndex_eq {θ ε Wt Wp Ws : ℝ} (hε : ε ≠ 1) (hWt : 0 < Wt) (hWp : 0 < Wp)
    (hWs : 0 < Ws) (hrec : Wt ^ (1 - ε) = θ * Wp ^ (1 - ε) + (1 - θ) * Ws ^ (1 - ε)) :
    Real.log Wt = Real.log Wp + inflFn θ ε (Real.log Ws - Real.log Wp) := by
  have h := log_infl_eq_inflFn hε (div_pos hWt hWp) (div_pos hWs hWp)
    ((recursion_levels_iff hWt hWp hWs).2 hrec)
  rw [Real.log_div hWt.ne' hWp.ne', Real.log_div hWs.ne' hWp.ne'] at h
  linarith

/-- Galí (2015), eq. (14), p. 169 (**exact linearisation**): `w*_t ↦ log W_t` has value `w_{t−1}`
and derivative `1 − θ_w` at the zero-wage-inflation point `w*_t = w_{t−1}`, and its tangent
line there is `w_t = θ_w w_{t−1} + (1 − θ_w) w*_t`, eq. (14). -/
theorem eq14_tangent (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (wp : ℝ) :
    wp + inflFn θ ε (wp - wp) = wp ∧
      HasDerivAt (fun ws => wp + inflFn θ ε (ws - wp)) (1 - θ) wp ∧
      ∀ ws, wp + (1 - θ) * (ws - wp) = θ * wp + (1 - θ) * ws := by
  refine ⟨by rw [sub_self, inflFn_zero, add_zero], ?_, fun ws => by ring⟩
  have h1 : HasDerivAt (fun ws : ℝ => ws - wp) 1 wp := (hasDerivAt_id wp).sub_const wp
  have h2 : HasDerivAt (inflFn θ ε) (1 - θ) ((fun ws : ℝ => ws - wp) wp) := by
    simp only [sub_self]
    exact hasDerivAt_inflFn θ hε
  have h3 := (HasDerivAt.comp (h := fun ws : ℝ => ws - wp) wp h2 h1).const_add wp
  simpa using h3

/-- Galí (2015), eq. (14), p. 169: `w_t = θ_w w_{t−1} + (1 − θ_w) w*_t` iff
`π^w_t = (1 − θ_w)(w*_t − w_{t−1})`. -/
theorem eq14_iff (θ w wp ws : ℝ) :
    w = θ * wp + (1 - θ) * ws ↔ w - wp = (1 - θ) * (ws - wp) := by
  constructor <;> intro h <;> linarith

/-! ### The wage-inflation equation (15) -/

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`. -/
noncomputable def lambdaW (β θ ε φ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))

/-- Galí (2015), p. 169: wage inflation `π^w_{t+1} = w_{t+1} − w_t` (dated `t + 1`). -/
noncomputable def wageInfl {Ω : Type*} (w : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := w (t + 1) - w t

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eqs. (13)–(15), pp. 169–170 (**(13) + (14) ⟺ (15)**): with
`0 < θ_w < 1`, `1 + ε_wφ ≠ 0`, an adapted (log) wage index `w` and the index recursion (14),
`w_{t+1} = θ_w w_t + (1 − θ_w) w*_{t+1}` at every date, the recursive wage-setting rule (13)
holds at every date `t + 1` **if and only if** the wage-inflation equation (15),
`π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w μ̂^w_{t+1}`, does. -/
theorem eq15_iff {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w μhat : ℕ → Ω → ℝ} (hwa : 𝔼.Adapted w)
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1)) :
    (∀ t, wstar (t + 1) = (β * θ) • 𝔼.E (t + 1) (wstar (t + 2)) +
        (1 - β * θ) • (w (t + 1) - (1 + ε * φ)⁻¹ • μhat (t + 1))) ↔
      ∀ t, wageInfl w t = β • 𝔼.E (t + 1) (wageInfl w (t + 1)) -
        lambdaW β θ ε φ • μhat (t + 1) := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have hθ : θ ≠ 0 := hθ0.ne'
  have hL : θ * lambdaW β θ ε φ = (1 - θ) * (1 - β * θ) * (1 + ε * φ)⁻¹ := by
    unfold lambdaW
    field_simp
  have hA : ∀ t ω, w (t + 1) ω = θ * w t ω + (1 - θ) * wstar (t + 1) ω := fun t ω => by
    have := congrFun (h14 t) ω
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hB : ∀ t ω, 𝔼.E (t + 1) (w (t + 2)) ω
      = θ * w (t + 1) ω + (1 - θ) * 𝔼.E (t + 1) (wstar (t + 2)) ω := fun t ω => by
    have h' : w (t + 2) = θ • w (t + 1) + (1 - θ) • wstar (t + 2) := h14 (t + 1)
    rw [h', map_add, map_smul, map_smul, hwa (t + 1)]
    rfl
  have hEπ : ∀ t ω, 𝔼.E (t + 1) (wageInfl w (t + 1)) ω = 𝔼.E (t + 1) (w (t + 2)) ω -
      w (t + 1) ω := by
    intro t ω
    simp only [wageInfl, map_sub, hwa (t + 1), Pi.sub_apply]
  constructor
  · intro h13 t
    funext ω
    have E13 : wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω) := by
      have := congrFun (h13 t) ω
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using this
    have hgoal : θ * (w (t + 1) ω - w t ω - (β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω)) = 0 := by
      linear_combination (1 - θ) * E13 + hA t ω - β * θ * hB t ω + μhat (t + 1) ω * hL
    have hq := (mul_eq_zero.mp hgoal).resolve_left hθ
    change wageInfl w t ω = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω -
      lambdaW β θ ε φ * μhat (t + 1) ω
    rw [hEπ t ω]
    simp only [wageInfl, Pi.sub_apply]
    linarith
  · intro h15 t
    funext ω
    have F15 : w (t + 1) ω - w t ω = β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω := by
      have h := congrFun (h15 t) ω
      have e : (β • 𝔼.E (t + 1) (wageInfl w (t + 1)) - lambdaW β θ ε φ • μhat (t + 1)) ω
          = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω - lambdaW β θ ε φ * μhat (t + 1) ω := rfl
      rw [e, hEπ t ω] at h
      simpa only [wageInfl, Pi.sub_apply] using h
    have hgoal : (1 - θ) * (wstar (t + 1) ω - (β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω))) = 0 := by
      linear_combination θ * F15 - μhat (t + 1) ω * hL - hA t ω + β * θ * hB t ω
    have hq := (mul_eq_zero.mp hgoal).resolve_left h1θ
    change wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
      (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω)
    linarith

/-- Galí (2015), p. 170 (**`λ_w > 0`**): for `0 < θ_w < 1`, `βθ_w < 1` and `1 + ε_wφ > 0`. -/
theorem lambdaW_pos {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hεφ : 0 < 1 + ε * φ) : 0 < lambdaW β θ ε φ := by
  unfold lambdaW
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 1 - β * θ := by linarith
  positivity

/-- Galí (2015), p. 170 (`λ_w` and wage stickiness): for `0 ≤ β ≤ 1` and `1 + ε_wφ > 0`,
`λ_w` is strictly decreasing in `θ_w` on `(0, 1)`. -/
theorem lambdaW_strictAntiOn_theta {β ε φ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hεφ : 0 < 1 + ε * φ) : StrictAntiOn (fun θ => lambdaW β θ ε φ) (Set.Ioo 0 1) := by
  intro θ₁ h₁ θ₂ h₂ hlt
  simp only [lambdaW]
  have a1 : 0 < θ₁ := h₁.1
  have a2 : 0 < θ₂ := h₂.1
  have b2 : 0 < 1 - β * θ₂ := by nlinarith [h₂.2]
  have hB : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
  have hA : (1 - θ₂) / θ₂ < (1 - θ₁) / θ₁ := by
    rw [div_lt_div_iff₀ a2 a1]
    nlinarith
  have hA1 : 0 ≤ (1 - θ₁) / θ₁ := div_nonneg (by linarith [h₁.2]) a1.le
  have key : (1 - θ₂) / θ₂ * (1 - β * θ₂) < (1 - θ₁) / θ₁ * (1 - β * θ₁) :=
    calc (1 - θ₂) / θ₂ * (1 - β * θ₂) < (1 - θ₁) / θ₁ * (1 - β * θ₂) :=
          mul_lt_mul_of_pos_right hA b2
      _ ≤ (1 - θ₁) / θ₁ * (1 - β * θ₁) := mul_le_mul_of_nonneg_left hB hA1
  have e : ∀ θ : ℝ, θ ≠ 0 → (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))
      = (1 - θ) / θ * (1 - β * θ) / (1 + ε * φ) := fun θ hθ => by
    field_simp
  rw [e θ₁ a1.ne', e θ₂ a2.ne']
  exact div_lt_div_of_pos_right key hεφ

/-- Galí (2015), p. 170: for `0 < θ_w < 1`, `βθ_w < 1` and `φ > 0`, `λ_w` is strictly
decreasing in the elasticity of substitution `ε_w ≥ 0`. -/
theorem lambdaW_strictAntiOn_eps {β θ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hφ : 0 < φ) : StrictAntiOn (fun ε => lambdaW β θ ε φ) (Set.Ici 0) := by
  intro ε₁ h₁ ε₂ h₂ hlt
  simp only [lambdaW]
  have hK : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  have hd1 : 0 < θ * (1 + ε₁ * φ) := mul_pos hθ0 (by nlinarith [Set.mem_Ici.mp h₁])
  have hlt' : θ * (1 + ε₁ * φ) < θ * (1 + ε₂ * φ) :=
    mul_lt_mul_of_pos_left (by nlinarith) hθ0
  exact div_lt_div_of_pos_left hK hd1 hlt'

/-- Galí (2015), p. 170: for `0 < θ_w < 1`, `βθ_w < 1` and `ε_w > 0`, `λ_w` is strictly
decreasing in the inverse Frisch elasticity `φ ≥ 0`. -/
theorem lambdaW_strictAntiOn_phi {β θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hε : 0 < ε) : StrictAntiOn (fun φ => lambdaW β θ ε φ) (Set.Ici 0) := by
  intro φ₁ h₁ φ₂ h₂ hlt
  simp only [lambdaW]
  have hK : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  have hd1 : 0 < θ * (1 + ε * φ₁) := mul_pos hθ0 (by nlinarith [Set.mem_Ici.mp h₁])
  have hlt' : θ * (1 + ε * φ₁) < θ * (1 + ε * φ₂) :=
    mul_lt_mul_of_pos_left (by nlinarith) hθ0
  exact div_lt_div_of_pos_left hK hd1 hlt'

end Gali.StickyWagesPrices.WageInflation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The sticky wage and price model in gap form

Galí (2015), Chapter 6, §6.2, pp. 170–173 and §6.4.3, pp. 183–184. The price
inflation equation (6) and the wage inflation equation (15) are rewritten in
terms of the output gap `ỹ = y − yⁿ` and the real wage gap `ω̃ = ω − ωⁿ`, where
natural levels refer to the equilibrium with flexible prices AND flexible wages.

The price NKPC (6), `π^p_t = β E_t π^p_{t+1} − λ_p μ̂^p_t`, and the wage NKPC
(15), `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`, are taken as model equations with
parameters `λ_p, λ_w`. All equations hold for an arbitrary `ExpectationSystem`,
so every result holds under perfect foresight and under uncertainty.

## Main results

* `psiWA_eq`, `psiWA_pos`: `ψ_wa = (1 − α ψ_ya)/(1 − α) = (σ + φ)/(σ (1 − α) + φ + α) > 0`
  for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1` (p. 171).
* `natural_allocation_iff`: the flexible price and wage allocation, solved exactly;
  the natural real wage is (16) up to the additive constant `−α ψ_y/(1 − α)`
  (`natWage_constant_ne_zero`: the constant printed in (16) is incomplete).
* `priceMarkup_gap`, `wageMarkup_gap`: eqs. (17) and (19).
* `priceNKPC_iff_gap`, `wageNKPC_iff_gap`: (6) ⇔ (18) and (15) ⇔ (20), with
  `κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`.
* `wageGap_identity`: the identity (21).
* `euler_iff_disGap_ar1`: the Euler equation (9) is equivalent to the DIS in
  gaps (22) with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`.
* `composite_nkpc`, `kappaBar_eq`: the composite NKPC (36) holds for ALL parameter
  values with slope `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w) = λ_p λ_w Θ_y/(λ_p + λ_w)`,
  `Θ_y = σ + (φ + α)/(1 − α)`; `kappaBar_strictly_between`: when `κ_p ≠ κ_w` the
  slope lies strictly between them, so the book's `κ` (defined only for
  `κ_p = κ_w`) is not the general slope.
* `kappa_common`: footnote 6, `κ_p = κ_w = κ ⇒ κ = λ_p λ_w Θ_y/(λ_p + λ_w)`.
-/

namespace Gali.StickyWagesPrices.GapForm

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Parameters -/

/-- Galí (2015), p. 171 (ch. 3, eq. (20)): the elasticity of natural output with
respect to technology, `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), eq. (16), p. 171: the elasticity of the natural real wage with
respect to technology, `ψ_wa = (1 − α ψ_ya)/(1 − α)`. -/
noncomputable def psiWA (σ φ α : ℝ) : ℝ := (1 - α * psiYA σ φ α) / (1 - α)

/-- Galí (2015), p. 171: the constant of natural output with flexible prices and
wages, `ψ_y = (1 − α)(log(1 − α) − μ^p − μ^w)/(σ (1 − α) + φ + α)`
(ch. 3's constant with the total markup `μ^p + μ^w`). -/
noncomputable def psiY (σ φ α μp μw : ℝ) : ℝ :=
  (1 - α) * (Real.log (1 - α) - μp - μw) / (σ * (1 - α) + φ + α)

/-- Galí (2015), p. 174 and fn. 6, p. 183: `Θ_y = σ + (φ + α)/(1 − α)`. -/
noncomputable def thetaY (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), eq. (18), p. 172: `κ_p = α λ_p/(1 − α)`. -/
noncomputable def kappaP (α lamP : ℝ) : ℝ := α * lamP / (1 - α)

/-- Galí (2015), eq. (20), p. 172: `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def kappaW (σ φ α lamW : ℝ) : ℝ := lamW * (σ + φ / (1 - α))

/-- Galí (2015), p. 171: the denominator `σ (1 − α) + φ + α` is positive under
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem denom_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < σ * (1 - α) + φ + α := by
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- Galí (2015), eq. (16), p. 171: `ψ_wa = (σ + φ)/(σ (1 − α) + φ + α)`. -/
theorem psiWA_eq {σ φ α : ℝ} (hD : σ * (1 - α) + φ + α ≠ 0) (hα1 : α ≠ 1) :
    psiWA σ φ α = (σ + φ) / (σ * (1 - α) + φ + α) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  unfold psiWA psiYA
  field_simp
  ring

/-- Galí (2015), eq. (16), p. 171: `ψ_wa > 0` for `σ > 0`, `φ ≥ 0`,
`0 ≤ α < 1` (equivalently `α ψ_ya < 1`). -/
theorem psiWA_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < psiWA σ φ α := by
  rw [psiWA_eq (denom_pos hσ hφ hα0 hα1).ne' hα1.ne]
  exact div_pos (by linarith) (denom_pos hσ hφ hα0 hα1)

/-- Galí (2015), p. 171: `α ψ_ya < 1` under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem alpha_psiYA_lt_one {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) : α * psiYA σ φ α < 1 := by
  have h := psiWA_pos hσ hφ hα0 hα1
  unfold psiWA at h
  have h1 : 0 < 1 - α := by linarith
  have := (div_pos_iff_of_pos_right h1).mp h
  linarith

/-- Galí (2015), p. 174: `Θ_y = σ + (φ + α)/(1 − α) > 0`. -/
theorem thetaY_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < thetaY σ φ α := by
  unfold thetaY
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Galí (2015), eq. (18), p. 172: `κ_p ≥ 0` for `λ_p ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaP_nonneg {α lamP : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 ≤ lamP) :
    0 ≤ kappaP α lamP :=
  div_nonneg (mul_nonneg hα0 hlamP) (by linarith)

/-- Galí (2015), eq. (20), p. 172: `κ_w > 0` for `λ_w > 0`, `σ > 0`, `φ ≥ 0`,
`α < 1`. -/
theorem kappaW_pos {σ φ α lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα1 : α < 1) (hlamW : 0 < lamW) :
    0 < kappaW σ φ α lamW := by
  unfold kappaW
  have : 0 ≤ φ / (1 - α) := div_nonneg hφ (by linarith)
  exact mul_pos hlamW (by linarith)

/-! ### The natural allocation and the natural real wage (16) -/

/-- Galí (2015), eq. (16), p. 171: the allocation with flexible prices and
wages. With labour demand `(1 − α) n = y − a`, the price-setting condition
`ω = mpn − μ^p = log(1 − α) + (a − α n) − μ^p` and the wage-setting condition
`ω = mrs + μ^w = σ y + φ n + μ^w`, the natural allocation is unique:
`yⁿ = ψ_ya a + ψ_y`, `nⁿ = (yⁿ − a)/(1 − α)` and
`ωⁿ = log(1 − α) + ψ_wa a − μ^p − α ψ_y/(1 − α)`. -/
theorem natural_allocation_iff {σ φ α μp μw : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (a y n w : ℝ) :
    ((1 - α) * n = y - a ∧ w = Real.log (1 - α) + (a - α * n) - μp ∧
        w = σ * y + φ * n + μw) ↔
      (y = psiYA σ φ α * a + psiY σ φ α μp μw ∧ n = (y - a) / (1 - α) ∧
        w = Real.log (1 - α) + psiWA σ φ α * a - μp - α / (1 - α) * psiY σ φ α μp μw) := by
  have hD := denom_pos hσ hφ hα0 hα1
  have h1 : 1 - α ≠ 0 := by linarith
  set L := Real.log (1 - α)
  constructor
  · rintro ⟨hn, hp, hw⟩
    have hy : y * (σ * (1 - α) + φ + α) = (1 + φ) * a + (1 - α) * (L - μp - μw) := by
      linear_combination (1 - α) * (hp - hw) - (φ + α) * hn
    have hy' : y = psiYA σ φ α * a + psiY σ φ α μp μw := by
      unfold psiYA psiY
      field_simp
      linear_combination hy
    have hn' : n = (y - a) / (1 - α) := by
      field_simp
      linear_combination hn
    refine ⟨hy', hn', ?_⟩
    rw [hp, hn']
    rw [hy']
    unfold psiWA psiYA
    field_simp
    ring
  · rintro ⟨hy, hn, hw⟩
    have hn' : (1 - α) * n = y - a := by
      rw [hn]
      field_simp
    refine ⟨hn', ?_, ?_⟩
    · rw [hw, hn, hy]
      unfold psiWA psiYA
      field_simp
      ring
    · rw [hw, hn, hy]
      unfold psiWA psiYA psiY
      field_simp
      ring

/-- Galí (2015), eq. (16), p. 171 (correction): the printed second line
`ωⁿ = log(1 − α) + ψ_wa a − μ^p` omits the constant `−α ψ_y/(1 − α)`. It is
nonzero in general: at `α = 1/2`, `σ = φ = 1`, `μ^p = μ^w = 0` it equals
`−log(1/2)/4 ≠ 0`. (The omission is harmless for the dynamics: only `Δωⁿ` and
deviations enter (21)–(24).) -/
theorem natWage_constant_ne_zero :
    (1 / 2 : ℝ) / (1 - 1 / 2) * psiY 1 1 (1 / 2) 0 0 ≠ 0 := by
  unfold psiY
  have hlog : Real.log (1 - 1 / 2 : ℝ) ≠ 0 := by
    have : Real.log (1 - 1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    exact this.ne
  have : (1 - 1 / 2 : ℝ) * (Real.log (1 - 1 / 2) - 0 - 0) / (1 * (1 - 1 / 2) + 1 + 1 / 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (by simpa using hlog)) (by norm_num)
  exact mul_ne_zero (by norm_num) this

/-! ### Markups in gap form: (17) and (19) -/

/-- Galí (2015), eq. (17), p. 172: with labour demand `(1 − α) n = y − a` (also at
the natural allocation) and the natural real wage (16) in its first form
`ωⁿ = log(1 − α) + (a − α nⁿ) − μ^p`, the price markup gap
`μ̂^p = (mpn − ω) − μ^p` equals `−α/(1 − α) ỹ − ω̃`. -/
theorem priceMarkup_gap {α L a y yn n nn w wn μp : ℝ} (hα1 : α ≠ 1)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = L + (a - α * nn) - μp) :
    (L + (a - α * n) - w) - μp = -(α / (1 - α)) * (y - yn) - (w - wn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
  have hq : α / (1 - α) * (y - yn) = α * (n - nn) := by
    rw [hy]
    field_simp
  rw [neg_mul, hq, hwn]
  ring

/-- Galí (2015), eq. (19), p. 172: with `mrs = σ y + φ n`, labour demand
`(1 − α) n = y − a` (also at the natural allocation) and the natural real wage
`ωⁿ = σ yⁿ + φ nⁿ + μ^w`, the wage markup gap `μ̂^w = (ω − mrs) − μ^w` equals
`ω̃ − (σ + φ/(1 − α)) ỹ`. -/
theorem wageMarkup_gap {σ φ α a y yn n nn w wn μw : ℝ} (hα1 : α ≠ 1)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = σ * yn + φ * nn + μw) :
    (w - (σ * y + φ * n)) - μw = (w - wn) - (σ + φ / (1 - α)) * (y - yn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
  have hq : φ / (1 - α) * (y - yn) = φ * (n - nn) := by
    rw [hy]
    field_simp
  rw [add_mul, hq, hwn]
  ring

/-! ### Inflation equations in gap form: (18) and (20) -/

/-- Galí (2015), eq. (6), p. 165: the price NKPC
`π^p_t = β E_t π^p_{t+1} − λ_p μ̂^p_t`. -/
def PriceNKPC (β lamP : ℝ) (pp muP : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) - lamP • muP t

/-- Galí (2015), eq. (15), p. 170: the wage NKPC
`π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`. -/
def WageNKPC (β lamW : ℝ) (pw muW : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - lamW • muW t

/-- Galí (2015), eq. (18), p. 172: price inflation in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PriceGapNKPC (β κp lamP : ℝ) (pp ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • ygap t + lamP • wgap t

/-- Galí (2015), eq. (20), p. 172: wage inflation in gaps,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WageGapNKPC (β κw lamW : ℝ) (pw ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • ygap t - lamW • wgap t

/-- Galí (2015), eqs. (6), (17), (18), p. 172: given the markup relation (17)
`μ̂^p_t = −α/(1 − α) ỹ_t − ω̃_t` at every date, the price NKPC (6) is equivalent
to (18) with `κ_p = α λ_p/(1 − α)`. -/
theorem priceNKPC_iff_gap {α β lamP : ℝ} {pp muP ygap wgap : ℕ → Ω → ℝ}
    (hmu : ∀ t, muP t = -(α / (1 - α)) • ygap t - wgap t) :
    PriceNKPC 𝔼 β lamP pp muP ↔ PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp ygap wgap := by
  unfold PriceNKPC PriceGapNKPC kappaP
  constructor
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), eqs. (15), (19), (20), p. 172: given the markup relation (19)
`μ̂^w_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t` at every date, the wage NKPC (15) is
equivalent to (20) with `κ_w = λ_w (σ + φ/(1 − α))`. -/
theorem wageNKPC_iff_gap {σ φ α β lamW : ℝ} {pw muW ygap wgap : ℕ → Ω → ℝ}
    (hmu : ∀ t, muW t = wgap t - (σ + φ / (1 - α)) • ygap t) :
    WageNKPC 𝔼 β lamW pw muW ↔ WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw ygap wgap := by
  unfold WageNKPC WageGapNKPC kappaW
  constructor
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), eqs. (6), (17), (18), p. 172, from the levels: if at every date
labour demand holds (`(1 − α) n = y − a`, also at the natural allocation), the
natural real wage is (16) in its first form and the price markup gap is
`μ̂^p = (mpn − ω) − μ^p` with `mpn = log(1 − α) + a − α n`, then (6) is equivalent
to (18). -/
theorem priceNKPC_iff_gap_of_levels {α β lamP μp : ℝ} (hα1 : α ≠ 1)
    {pp muP a y yn n nn w wn : ℕ → Ω → ℝ}
    (hn : ∀ t, (1 - α) • n t = y t - a t) (hnn : ∀ t, (1 - α) • nn t = yn t - a t)
    (hwn : ∀ t, wn t = (fun _ => Real.log (1 - α)) + (a t - α • nn t) - fun _ => μp)
    (hmu : ∀ t, muP t = ((fun _ => Real.log (1 - α)) + (a t - α • n t) - w t) - fun _ => μp) :
    PriceNKPC 𝔼 β lamP pp muP ↔
      PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp (fun t => y t - yn t) (fun t => w t - wn t) := by
  apply priceNKPC_iff_gap
  intro t
  rw [hmu t]
  funext x
  have e1 := congrFun (hn t) x
  have e2 := congrFun (hnn t) x
  have e3 := congrFun (hwn t) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact priceMarkup_gap hα1 e1 e2 e3

/-- Galí (2015), eqs. (15), (19), (20), p. 172, from the levels: if at every date
labour demand holds (also at the natural allocation), the natural real wage is
`ωⁿ = σ yⁿ + φ nⁿ + μ^w` and the wage markup gap is `μ̂^w = (ω − mrs) − μ^w` with
`mrs = σ y + φ n`, then (15) is equivalent to (20). -/
theorem wageNKPC_iff_gap_of_levels {σ φ α β lamW μw : ℝ} (hα1 : α ≠ 1)
    {pw muW a y yn n nn w wn : ℕ → Ω → ℝ}
    (hn : ∀ t, (1 - α) • n t = y t - a t) (hnn : ∀ t, (1 - α) • nn t = yn t - a t)
    (hwn : ∀ t, wn t = σ • yn t + φ • nn t + fun _ => μw)
    (hmu : ∀ t, muW t = (w t - (σ • y t + φ • n t)) - fun _ => μw) :
    WageNKPC 𝔼 β lamW pw muW ↔
      WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw (fun t => y t - yn t) (fun t => w t - wn t) := by
  apply wageNKPC_iff_gap
  intro t
  rw [hmu t]
  funext x
  have e1 := congrFun (hn t) x
  have e2 := congrFun (hnn t) x
  have e3 := congrFun (hwn t) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact wageMarkup_gap hα1 e1 e2 e3

/-! ### The real wage gap identity (21) -/

/-- Galí (2015), eq. (21), p. 172: with `ω_t = w_t − p_t`, `π^w_t = w_t − w_{t−1}`,
`π^p_t = p_t − p_{t−1}`, `ω̃_t = ω_t − ωⁿ_t` and `Δωⁿ_t = ωⁿ_t − ωⁿ_{t−1}`, the
real wage gap satisfies `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
theorem wageGap_identity (wlev plev wn : ℕ → Ω → ℝ) (t : ℕ) :
    (wlev (t + 1) - plev (t + 1)) - wn (t + 1)
      = ((wlev t - plev t) - wn t) + (wlev (t + 1) - wlev t) - (plev (t + 1) - plev t)
        - (wn (t + 1) - wn t) := by
  abel

/-! ### The dynamic IS equation in gaps (22)

Restated from the Chapter 3 project (`DIS.lean`): the Euler equation (9) with
the preference shock, natural output, the natural rate and the DIS in gaps. -/

/-- Galí (2015), eq. (9), p. 167, with `y = c` (p. 170): the Euler equation in
output, `y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π^p_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerOutput (σ ρ ρz : ℝ) (y i pp z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), p. 171 (ch. 3, eq. (20)): natural output `yⁿ_t = ψ_ya a_t + ψ_y`. -/
def natOutput (ψya ψy : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψya • a t + fun _ => ψy

/-- Galí (2015), p. 173: the natural rate of interest, the real rate supporting
natural output in the Euler equation,
`rⁿ_t = ρ + σ (E_t yⁿ_{t+1} − yⁿ_t) + (1 − ρ_z) z_t`. -/
def natRate (σ ρ ρz : ℝ) (yn z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + σ • (𝔼.E t (yn (t + 1)) - yn t) + (1 - ρz) • z t

/-- Galí (2015), eq. (22), p. 173: the dynamic IS equation in gaps,
`ỹ_t = −σ⁻¹ (i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i pp rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), p. 173: for AR(1) technology with persistence `ρ_a` and natural
output `yⁿ_t = ψ_ya a_t + ψ_y`, the natural rate is
`rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem natRate_ar1 {σ ρ ρz ρa ψya ψy : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (z : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z t
      = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t := by
  unfold natRate natOutput
  rw [map_add, map_smul, 𝔼.const, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (22), p. 173: with `ỹ_t = y_t − yⁿ_t`, the Euler equation (9)
is equivalent to the DIS in gaps with the natural rate `rⁿ`. -/
theorem euler_iff_disGap {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y yn ygap i pp z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - yn t) :
    EulerOutput 𝔼 σ ρ ρz y i pp z ↔ DISGap 𝔼 σ ygap i pp (natRate 𝔼 σ ρ ρz yn z) := by
  unfold EulerOutput DISGap natRate
  simp only [hgap, map_sub]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e

/-- Galí (2015), eq. (22), p. 173: for AR(1) technology and natural output
`yⁿ = ψ_ya a + ψ_y`, the Euler equation (9) is equivalent to the DIS in gaps
with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem euler_iff_disGap_ar1 {σ ρ ρz ρa ψya ψy : ℝ} (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) {y ygap i pp z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - natOutput ψya ψy a t) :
    EulerOutput 𝔼 σ ρ ρz y i pp z ↔ DISGap 𝔼 σ ygap i pp
      (fun t => (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t) := by
  have hrn : natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z
      = fun t => (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t :=
    funext (natRate_ar1 𝔼 ha z)
  rw [← hrn]
  exact euler_iff_disGap 𝔼 hσ hgap

/-! ### Composite inflation and the composite NKPC (36) -/

/-- Galí (2015), p. 184: composite inflation
`π̄_t = λ_w/(λ_p + λ_w) π^p_t + λ_p/(λ_p + λ_w) π^w_t`. -/
noncomputable def compositeInfl (lamP lamW : ℝ) (pp pw : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (lamW / (lamP + lamW)) • pp t + (lamP / (lamP + lamW)) • pw t

/-- Galí (2015), eq. (36), p. 184 (corrected): the slope of the composite NKPC,
`κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)`. -/
noncomputable def kappaBar (lamP lamW κp κw : ℝ) : ℝ := (lamW * κp + lamP * κw) / (lamP + lamW)

/-- Galí (2015), eq. (36), p. 184: for ANY parameter values (only `λ_p + λ_w ≠ 0`
is needed), (18) and (20) imply the composite NKPC
`π̄_t = β E_t π̄_{t+1} + κ̄ ỹ_t` with `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)`. -/
theorem composite_nkpc {β κp κw lamP lamW : ℝ} (hsum : lamP + lamW ≠ 0)
    {pp pw ygap wgap : ℕ → Ω → ℝ} (h18 : PriceGapNKPC 𝔼 β κp lamP pp ygap wgap)
    (h20 : WageGapNKPC 𝔼 β κw lamW pw ygap wgap) (t : ℕ) :
    compositeInfl lamP lamW pp pw t
      = β • 𝔼.E t (compositeInfl lamP lamW pp pw (t + 1)) + kappaBar lamP lamW κp κw • ygap t := by
  unfold compositeInfl kappaBar
  rw [map_add, map_smul, map_smul, h18 t, h20 t]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), eq. (36) and fn. 6, pp. 183–184: with `κ_p = α λ_p/(1 − α)` and
`κ_w = λ_w (σ + φ/(1 − α))`, the composite slope is
`κ̄ = λ_p λ_w Θ_y/(λ_p + λ_w)`, `Θ_y = σ + (φ + α)/(1 − α)`, for all parameters. -/
theorem kappaBar_eq (σ φ α lamP lamW : ℝ) :
    kappaBar lamP lamW (kappaP α lamP) (kappaW σ φ α lamW)
      = lamP * lamW * thetaY σ φ α / (lamP + lamW) := by
  unfold kappaBar kappaP kappaW thetaY
  ring

/-- Galí (2015), eq. (36), p. 184: the composite NKPC in the model's parameters,
`π̄_t = β E_t π̄_{t+1} + λ_p λ_w Θ_y/(λ_p + λ_w) ỹ_t`, for all parameter values
with `λ_p + λ_w ≠ 0`. -/
theorem composite_nkpc_explicit {σ φ α β lamP lamW : ℝ} (hsum : lamP + lamW ≠ 0)
    {pp pw ygap wgap : ℕ → Ω → ℝ} (h18 : PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp ygap wgap)
    (h20 : WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw ygap wgap) (t : ℕ) :
    compositeInfl lamP lamW pp pw t = β • 𝔼.E t (compositeInfl lamP lamW pp pw (t + 1))
      + (lamP * lamW * thetaY σ φ α / (lamP + lamW)) • ygap t := by
  rw [← kappaBar_eq]
  exact composite_nkpc 𝔼 hsum h18 h20 t

/-- Galí (2015), eq. (36), p. 184: `κ̄ > 0` for `λ_p, λ_w > 0` and the standard
restrictions `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaBar_pos {σ φ α lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    0 < kappaBar lamP lamW (kappaP α lamP) (kappaW σ φ α lamW) := by
  rw [kappaBar_eq]
  exact div_pos (mul_pos (mul_pos hlamP hlamW) (thetaY_pos hσ hφ hα0 hα1)) (by linarith)

/-- Galí (2015), eq. (36), p. 184 (correction): the book writes the slope of (36)
as `κ`, which is defined (fn. 6) only when `κ_p = κ_w`. In general `κ̄` is a
weighted average of `κ_p` and `κ_w`; when `κ_p < κ_w` it lies strictly between
them, so it coincides with neither. -/
theorem kappaBar_strictly_between {lamP lamW κp κw : ℝ} (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hκ : κp < κw) : κp < kappaBar lamP lamW κp κw ∧ kappaBar lamP lamW κp κw < κw := by
  unfold kappaBar
  have hs : 0 < lamP + lamW := by linarith
  constructor
  · rw [lt_div_iff₀ hs]
    nlinarith
  · rw [div_lt_iff₀ hs]
    nlinarith

/-- Galí (2015), fn. 6, p. 183: when `κ_p = κ_w = κ`, the common slope is
`κ = λ_p λ_w/(λ_p + λ_w) · (σ + (φ + α)/(1 − α))`; it is then also the
composite slope `κ̄` of (36). -/
theorem kappa_common {σ φ α lamP lamW κ : ℝ} (hsum : lamP + lamW ≠ 0)
    (hp : kappaP α lamP = κ) (hw : kappaW σ φ α lamW = κ) :
    κ = lamP * lamW / (lamP + lamW) * thetaY σ φ α ∧ kappaBar lamP lamW κ κ = κ := by
  have hbar : kappaBar lamP lamW κ κ = κ := by
    unfold kappaBar
    field_simp
    ring
  refine ⟨?_, hbar⟩
  have h := kappaBar_eq σ φ α lamP lamW
  rw [hp, hw, hbar] at h
  rw [h]
  ring

end Gali.StickyWagesPrices.GapForm

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The equilibrium system under a simple interest rate rule

Galí (2015), Chapter 6, §6.2, pp. 173–175. Closing the gap form (18), (20), (21),
(22) with the rule (23) `i_t = ρ + φ_p π^p_t + φ_w π^w_t + φ_y ŷ_t + v_t` gives the
four-variable system (24) `A₀ x_t = A₁ E_t x_{t+1} + B₀ u_t` with
`x_t = [ỹ_t, π^p_t, π^w_t, ω̃_{t−1}]` and `u_t = [r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t]`.

Convention: the fourth state is the LAGGED real wage gap; the process `wl` has
`wl t = ω̃_{t−1}`, so `ω̃_t = wl (t + 1)` and `wl 0 = ω̃_{−1}` is the initial
condition. `r̂ⁿ = rⁿ − ρ` is the natural rate in deviation from `ρ`.

## Main results

* `equilibrium_iff_matrixEq`: the model equations (18), (20), (21), (22), (23)
  are equivalent to the matrix equation (24) (given that `ω̃_t` is known at `t`).
* `zeroPath_iff`, `zeroPath_exists_iff`: the path `ỹ = π^p = π^w = 0` solves (24),
  with `ω̃_{−1} = 0`, iff `u_{1} ≡ 0` and `Δωⁿ ≡ 0`.
* `zeroPath_iff_primitives` (corrected p. 174 statement): with AR(1) technology
  (`ρ_a ≠ 1`), the zero path solves (24) iff the natural wage is constant at its
  steady state AND `v = r̂ⁿ`, for every `φ_y`. `zeroPath_solves_any_phiY`: the
  printed hypothesis `φ_y = 0` is redundant; `zeroPath_fails_v_eq_rn`: the printed
  `v = rⁿ` (without hat) does not work when `ρ ≠ 0`.
* `det_A0_sub_A1_eq`: `det(A₀ − A₁) = −λ_p λ_w Θ_y (LHS − 1)` with
  `LHS = φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)` (the p. 174 condition).
* `one_eigenvalue_iff`: `1` is an eigenvalue of `A₀⁻¹ A₁` iff `LHS = 1`, i.e.
  exactly on the determinacy boundary.
* `detCondition_phiY_zero`, `detCondition_iff_threshold`, `threshold_strictAnti`:
  for `φ_y = 0` the condition reads `φ_p + φ_w > 1`; the threshold on
  `φ_p + φ_w` strictly decreases in `φ_y` (Figure 6.1).

The determinacy theorem itself (eigenvalue location) is in another module.
-/

namespace Gali.StickyWagesPrices.System

open GapForm
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The rule (23) and the matrix form (24) -/

/-- Galí (2015), eq. (23), p. 173: the interest rate rule
`i_t = ρ + φ_p π^p_t + φ_w π^w_t + φ_y ŷ_t + v_t`. -/
def Rule (ρ φp φw φy : ℝ) (i pp pw yhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φp • pp t + φw • pw t + φy • yhat t + v t

/-- Galí (2015), eq. (21), p. 172, in the lagged convention `wl t = ω̃_{t−1}`:
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
def WageGapLaw (wl pp pw dwn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wl (t + 1) = wl t + pw t - pp t - dwn t

/-- Galí (2015), eqs. (18), (20), (21), (22), pp. 172–173: the non-policy block in
gaps, with `ω̃_t = wl (t + 1)`. -/
def Equilibrium (σ β κp κw lamP lamW : ℝ) (ygap pp pw wl i rn dwn : ℕ → Ω → ℝ) : Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageGapNKPC 𝔼 β κw lamW pw ygap (fun t => wl (t + 1)) ∧ WageGapLaw wl pp pw dwn

/-- Galí (2015), eq. (24), p. 173: the matrix `A₀ʷ`. -/
def A0 (σ φp φw φy κp κw : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![σ + φy, φp, φw, 0; -κp, 1, 0, 0; -κw, 0, 1, 0; 0, -1, 1, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `A₁ʷ`. -/
def A1 (σ β lamP lamW : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![σ, 1, 0, 0; 0, β, 0, lamP; 0, 0, β, -lamW; 0, 0, 0, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `B₀ʷ`. -/
def B0 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0; 0, 1]

/-- Galí (2015), eq. (24), p. 173: the state `x_t = [ỹ_t, π^p_t, π^w_t, ω̃_{t−1}]`. -/
def stateVec (ygap pp pw wl : ℕ → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![ygap t, pp t, pw t, wl t]

/-- Galí (2015), eq. (24), p. 173: the forcing vector `u_t = [u₁_t, Δωⁿ_t]`. -/
def shockVec (u1 dwn : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![u1 t, dwn t]

/-- Galí (2015), eq. (24), p. 173: `A₀ x_t = A₁ E_t x_{t+1} + B₀ u_t` at every date. -/
def MatrixEq (A₀ A₁ : Matrix (Fin 4) (Fin 4) ℝ) (B₀ : Matrix (Fin 4) (Fin 2) ℝ)
    (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, ∑ j, A₀ i j • x t j = ∑ j, A₁ i j • 𝔼.E t (x (t + 1) j) + ∑ k, B₀ i k • u t k

/-- Galí (2015), eq. (24), p. 173: the matrix equation written row by row. -/
theorem matrixEq_iff_rows {σ β φp φw φy κp κw lamP lamW : ℝ} (ygap pp pw wl u1 dwn : ℕ → Ω → ℝ) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0 (stateVec ygap pp pw wl)
        (shockVec u1 dwn) ↔
      ∀ t, ((σ + φy) • ygap t + φp • pp t + φw • pw t
          = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (pp (t + 1)) + u1 t) ∧
        (-(κp • ygap t) + pp t = β • 𝔼.E t (pp (t + 1)) + lamP • 𝔼.E t (wl (t + 1))) ∧
        (-(κw • ygap t) + pw t = β • 𝔼.E t (pw (t + 1)) - lamW • 𝔼.E t (wl (t + 1))) ∧
        (-pp t + pw t + wl t = 𝔼.E t (wl (t + 1)) + dwn t) := by
  unfold MatrixEq
  constructor
  · intro h t
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 0
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 1
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 2
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 3
  · rintro h t i
    obtain ⟨h0, h1, h2, h3⟩ := h t
    fin_cases i
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h0
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h1
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h2
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h3

/-- Galí (2015), eq. (24), p. 173: given the rule (23) with `ŷ = ỹ + ŷⁿ` and a real
wage gap known at each date (`E_t ω̃_t = ω̃_t`), the model equations (18), (20),
(21), (22) are equivalent to the matrix equation (24) with
`u_t = [r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t]`, `r̂ⁿ_t = rⁿ_t − ρ`. -/
theorem equilibrium_iff_matrixEq {σ β ρ φp φw φy κp κw lamP lamW : ℝ} (hσ : σ ≠ 0)
    {ygap pp pw wl i rn dwn v yhat ynhat : ℕ → Ω → ℝ}
    (hrule : Rule ρ φp φw φy i pp pw yhat v) (hyhat : ∀ t, yhat t = ygap t + ynhat t)
    (hadapt : ∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) :
    Equilibrium 𝔼 σ β κp κw lamP lamW ygap pp pw wl i rn dwn ↔
      MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0 (stateVec ygap pp pw wl)
        (shockVec (fun t => rn t - (fun _ => ρ) - v t - φy • ynhat t) dwn) := by
  rw [matrixEq_iff_rows]
  unfold Equilibrium DISGap PriceGapNKPC WageGapNKPC WageGapLaw
  simp only [hadapt]
  constructor
  · rintro ⟨hd, h18, h20, h21⟩ t
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext x
      have e1 := congrFun (hd t) x
      have e2 := congrFun (hrule t) x
      have e3 := congrFun (hyhat t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      rw [e3] at e2
      rw [e2] at e1
      field_simp at e1
      linear_combination e1
    · funext x
      have e := congrFun (h18 t) x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h20 t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h21 t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at e ⊢
      linear_combination -e
  · intro h
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · funext x
      have e1 := congrFun (h t).1 x
      have e2 := congrFun (hrule t) x
      have e3 := congrFun (hyhat t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      rw [e3] at e2
      rw [e2]
      field_simp
      linear_combination e1
    · funext x
      have e := congrFun (h t).2.1 x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h t).2.2.1 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h t).2.2.2 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at e ⊢
      linear_combination -e

/-- Galí (2015), p. 173: `{u_t}` is a linear transformation of the shifters
`{a_t, z_t, v_t}`: with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t` and
`ŷⁿ_t = ψ_ya a_t`, `u₁_t = −(σ (1 − ρ_a) + φ_y) ψ_ya a_t + (1 − ρ_z) z_t − v_t`. -/
theorem u1_linear (σ ρ ρa ρz ψya φy : ℝ) (a z v : ℕ → Ω → ℝ) (t : ℕ) :
    ((fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t) - (fun _ => ρ) - v t
        - φy • (ψya • a t)
      = -((σ * (1 - ρa) + φy) * ψya) • a t + (1 - ρz) • z t - v t := by
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### When is `ỹ = π^p = π^w = 0` an equilibrium? (p. 174) -/

/-- Galí (2015), p. 174: with `λ_p ≠ 0` and a real wage gap known at each date,
the path `ỹ = π^p = π^w = 0` (with lagged gap `wl`) solves (24) iff
`u₁ ≡ 0`, `ω̃_t = 0` for all `t ≥ 0`, `Δωⁿ_0 = ω̃_{−1}` and `Δωⁿ_t = 0` for `t ≥ 1`. -/
theorem zeroPath_iff {σ β φp φw φy κp κw lamP lamW : ℝ} (hlamP : lamP ≠ 0)
    {wl u1 dwn : ℕ → Ω → ℝ} (hadapt : ∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
        (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl) (shockVec u1 dwn) ↔
      (∀ t, u1 t = 0) ∧ (∀ t, wl (t + 1) = 0) ∧ dwn 0 = wl 0 ∧ ∀ t, dwn (t + 1) = 0 := by
  rw [matrixEq_iff_rows]
  simp only [hadapt, map_zero, smul_zero, add_zero, zero_add, neg_zero]
  have hw : (∀ t, (0 : Ω → ℝ) = lamP • wl (t + 1)) ↔ ∀ t, wl (t + 1) = 0 := by
    refine forall_congr' fun t => ?_
    rw [eq_comm, smul_eq_zero]
    simp [hlamP]
  constructor
  · intro h
    have hw1 : ∀ t, wl (t + 1) = 0 := hw.mp fun t => (h t).2.1
    refine ⟨fun t => ((h t).1).symm, hw1, ?_, fun t => ?_⟩
    · have e := (h 0).2.2.2
      rw [hw1 0, zero_add] at e
      exact e.symm
    · have e := (h (t + 1)).2.2.2
      rw [hw1 t, hw1 (t + 1), zero_add] at e
      exact e.symm
  · rintro ⟨hu, hw1, hd0, hd⟩ t
    refine ⟨(hu t).symm, hw.mpr hw1 t, ?_, ?_⟩
    · rw [hw1 t, smul_zero, sub_zero]
    · rw [hw1 t]
      cases t with
      | zero => rw [hd0, zero_add]
      | succ s => rw [hd s, hw1 s, add_zero]

/-- Galí (2015), p. 174 (corrected): with `λ_p ≠ 0`, there is a solution of (24)
with `ỹ = π^p = π^w = 0` for all `t`, initial condition `ω̃_{−1} = 0` and a real
wage gap known at each date, iff `u₁_t = r̂ⁿ_t − v_t − φ_y ŷⁿ_t ≡ 0` and
`Δωⁿ ≡ 0`. -/
theorem zeroPath_exists_iff {σ β φp φw φy κp κw lamP lamW : ℝ} (hlamP : lamP ≠ 0)
    {u1 dwn : ℕ → Ω → ℝ} :
    (∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl) (shockVec u1 dwn)) ↔
      (∀ t, u1 t = 0) ∧ ∀ t, dwn t = 0 := by
  constructor
  · rintro ⟨wl, h0, hadapt, h⟩
    obtain ⟨hu, -, hd0, hd⟩ := (zeroPath_iff 𝔼 hlamP hadapt).mp h
    refine ⟨hu, fun t => ?_⟩
    cases t with
    | zero => rw [hd0, h0]
    | succ s => exact hd s
  · rintro ⟨hu, hd⟩
    have hadapt : ∀ t, 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) = (fun _ => 0) (t + 1) :=
      fun t => map_zero _
    refine ⟨fun _ => 0, rfl, hadapt, (zeroPath_iff 𝔼 hlamP hadapt).mpr ⟨hu, fun _ => rfl, ?_,
      fun t => hd (t + 1)⟩⟩
    exact hd 0

/-- Galí (2015), p. 174 (corrected statement; survey error 1). Technology `a` is
AR(1) with `ρ_a ≠ 1` (in deviations from steady state), `ŷⁿ_t = ψ_ya a_t`, the
natural real wage in deviations is `ω̂ⁿ_t = ψ_wa a_t` with `ψ_wa ≠ 0` (lagged
convention: `wnl (t + 1) = ω̂ⁿ_t`, `wnl 0 = ω̂ⁿ_{−1}`), `Δωⁿ_t = ω̂ⁿ_t − ω̂ⁿ_{t−1}`.
Then, for EVERY `φ_y`, the path `ỹ = π^p = π^w = 0` with `ω̃_{−1} = 0` solves (24)
iff the natural wage is constant at its steady state (`ω̂ⁿ ≡ 0`, at all dates
from `−1`) and `v = r̂ⁿ`. -/
theorem zeroPath_iff_primitives {σ β φp φw φy κp κw lamP lamW ρa ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) (hρa : ρa ≠ 1) {a wnl rnhat v : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hwn : ∀ t, wnl (t + 1) = ψwa • a t) :
    (∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl)
          (shockVec (fun t => rnhat t - v t - φy • (ψya • a t))
            (fun t => wnl (t + 1) - wnl t))) ↔
      (∀ t, wnl t = 0) ∧ ∀ t, v t = rnhat t := by
  rw [zeroPath_exists_iff 𝔼 hlamP]
  have ha0 : ∀ t, ψwa • a t = 0 → a t = 0 := fun t h => by
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' hψ
    · exact h'
  constructor
  · rintro ⟨hu, hd⟩
    -- the natural wage is constant over time
    have hconst : ∀ t, wnl t = wnl 0 := by
      intro t
      induction t with
      | zero => rfl
      | succ s ih => rw [← ih]; exact sub_eq_zero.mp (hd s)
    -- hence technology is constant, and AR(1) with ρ_a ≠ 1 forces it to be zero
    have hac : a 1 = a 0 := by
      have h1 : ψwa • a 1 = ψwa • a 0 := by rw [← hwn, ← hwn, hconst 2, hconst 1]
      exact smul_right_injective _ hψ h1
    have hz : a 0 = 0 := by
      have e := ha.2 0
      rw [hac, ha.1 0] at e
      funext x
      have ex := congrFun e x
      simp only [Pi.smul_apply, smul_eq_mul] at ex
      have : (1 - ρa) * a 0 x = 0 := by linear_combination ex
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by linarith : ρa = 1) hρa
      · exact h'
    have hw0 : ∀ t, wnl t = 0 := by
      intro t
      rw [hconst t, ← hconst 1, hwn 0, hz, smul_zero]
    have hat : ∀ t, a t = 0 := fun t => by
      have h := hwn t
      rw [hw0 (t + 1)] at h
      exact ha0 t h.symm
    refine ⟨hw0, fun t => ?_⟩
    have e := hu t
    rw [hat t, smul_zero, smul_zero, sub_zero] at e
    exact (sub_eq_zero.mp e).symm
  · rintro ⟨hw0, hv⟩
    have hat : ∀ t, a t = 0 := fun t => by
      have h := hwn t
      rw [hw0 (t + 1)] at h
      exact ha0 t h.symm
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hat t, hv t, smul_zero, smul_zero, sub_self, sub_zero]
    · rw [hw0 (t + 1), hw0 t, sub_zero]

/-- Galí (2015), p. 174 (the printed hypothesis `φ_y = 0` is redundant): if the
natural wage is at its steady state at all dates (`ω̂ⁿ ≡ 0`, so `a ≡ 0` and
`ŷⁿ ≡ 0`) and `v = r̂ⁿ`, then `ỹ = π^p = π^w = 0` (with `ω̃ ≡ 0`) solves (24) for
ANY `φ_y`, in particular `φ_y ≠ 0`. -/
theorem zeroPath_solves_any_phiY {σ β φp φw φy κp κw lamP lamW ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) {a wnl rnhat v : ℕ → Ω → ℝ}
    (hwn : ∀ t, wnl (t + 1) = ψwa • a t) (hw0 : ∀ t, wnl t = 0) (hv : ∀ t, v t = rnhat t) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
      (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0))
      (shockVec (fun t => rnhat t - v t - φy • (ψya • a t)) (fun t => wnl (t + 1) - wnl t)) := by
  have hat : ∀ t, a t = 0 := fun t => by
    have h := hwn t
    rw [hw0 (t + 1)] at h
    rcases smul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hψ
    · exact h'
  have hadapt : ∀ t, 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) = (fun _ => 0) (t + 1) :=
    fun t => map_zero _
  refine (zeroPath_iff 𝔼 hlamP hadapt).mpr ⟨fun t => ?_, fun _ => rfl, ?_, fun t => ?_⟩
  · rw [hat t, hv t, smul_zero, smul_zero, sub_self, sub_zero]
  · rw [hw0 1, hw0 0, sub_zero]
  · rw [hw0 (t + 2), hw0 (t + 1), sub_zero]

/-- Galí (2015), p. 174 (the printed `v_t = rⁿ_t` must be `v_t = r̂ⁿ_t = rⁿ_t − ρ`):
if `v = rⁿ = ρ + r̂ⁿ` with `ρ ≠ 0`, then even with a constant natural wage
(`ω̂ⁿ ≡ 0`) the path `ỹ = π^p = π^w = 0` (with `ω̃_{−1} = 0`) does NOT solve (24). -/
theorem zeroPath_fails_v_eq_rn [Nonempty Ω] {σ β φp φw φy κp κw lamP lamW ρ ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) (hρ : ρ ≠ 0) {a wnl rnhat v : ℕ → Ω → ℝ}
    (hwn : ∀ t, wnl (t + 1) = ψwa • a t) (hw0 : ∀ t, wnl t = 0)
    (hv : ∀ t, v t = (fun _ => ρ) + rnhat t) :
    ¬ ∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl)
          (shockVec (fun t => rnhat t - v t - φy • (ψya • a t))
            (fun t => wnl (t + 1) - wnl t)) := by
  rw [zeroPath_exists_iff 𝔼 hlamP]
  rintro ⟨hu, -⟩
  have ha : a 0 = 0 := by
    have h := hwn 0
    rw [hw0 1] at h
    rcases smul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hψ
    · exact h'
  have e := hu 0
  rw [ha, hv 0, smul_zero, smul_zero, sub_zero] at e
  obtain ⟨x⟩ := ‹Nonempty Ω›
  have ex := congrFun e x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at ex
  exact hρ (by linarith)

/-! ### The determinant identity and the determinacy boundary (p. 174) -/

/-- Galí (2015), p. 174: the left-hand side of the determinacy condition,
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
noncomputable def detLHS (σ φ α β lamP lamW φp φw φy : ℝ) : ℝ :=
  φp + φw + φy * (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)

/-- Galí (2015), eq. (24), p. 173: `det(A₀ − A₁)` for general slopes `κ_p, κ_w`:
`−φ_y (1 − β)(λ_p + λ_w) − (φ_p + φ_w − 1)(λ_w κ_p + λ_p κ_w)`. -/
theorem det_A0_sub_A1 (σ β φp φw φy κp κw lamP lamW : ℝ) :
    (A0 σ φp φw φy κp κw - A1 σ β lamP lamW).det
      = -(φy * (1 - β) * (lamP + lamW)) - (φp + φw - 1) * (lamW * κp + lamP * κw) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, A0, A1]
  ring

/-- Galí (2015), p. 174: with `κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`,
`det(A₀ − A₁) = −λ_p λ_w Θ_y (LHS − 1)`, where `LHS` is the left side of the
determinacy condition. -/
theorem det_A0_sub_A1_eq {σ φ α β φp φw φy lamP lamW : ℝ} (hlamP : lamP ≠ 0) (hlamW : lamW ≠ 0)
    (hΘ : thetaY σ φ α ≠ 0) :
    (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW) - A1 σ β lamP lamW).det
      = -(lamP * lamW * thetaY σ φ α) * (detLHS σ φ α β lamP lamW φp φw φy - 1) := by
  rw [det_A0_sub_A1]
  have hk : lamW * kappaP α lamP + lamP * kappaW σ φ α lamW = lamP * lamW * thetaY σ φ α := by
    unfold kappaP kappaW thetaY
    ring
  rw [hk]
  unfold detLHS
  field_simp
  ring

/-- Galí (2015), eq. (24), p. 173: `det A₀ = σ + φ_y + φ_p κ_p + φ_w κ_w`. -/
theorem det_A0 (σ φp φw φy κp κw : ℝ) :
    (A0 σ φp φw φy κp κw).det = σ + φy + φp * κp + φw * κw := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, A0]
  ring

/-- Galí (2015), p. 174: under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0` and
nonnegative policy coefficients, `A₀` is invertible (`det A₀ > 0`). -/
theorem det_A0_pos {σ φ α φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hp : 0 ≤ φp) (hw : 0 ≤ φw)
    (hy : 0 ≤ φy) : 0 < (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW)).det := by
  rw [det_A0]
  have h1 := mul_nonneg hp (kappaP_nonneg hα0 hα1 hlamP.le)
  have h2 := mul_nonneg hw (kappaW_pos hσ hφ hα1 hlamW).le
  linarith

/-- Galí (2015), p. 174: `1` is an eigenvalue of `A ≡ A₀⁻¹ A₁` exactly on the
boundary of the determinacy region: there is `v ≠ 0` with `A v = v` iff
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) = 1`. -/
theorem one_eigenvalue_iff {σ φ α β φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hp : 0 ≤ φp)
    (hw : 0 ≤ φw) (hy : 0 ≤ φy) :
    (∃ x : Fin 4 → ℝ, x ≠ 0 ∧
        ((A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW))⁻¹ * A1 σ β lamP lamW) *ᵥ x = x) ↔
      detLHS σ φ α β lamP lamW φp φw φy = 1 := by
  set M := A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW)
  set N := A1 σ β lamP lamW
  have hdet : IsUnit M.det := (det_A0_pos hσ hφ hα0 hα1 hlamP hlamW hp hw hy).ne'.isUnit
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have key : ∀ x : Fin 4 → ℝ, (M⁻¹ * N) *ᵥ x = x ↔ (M - N) *ᵥ x = 0 := by
    intro x
    constructor
    · intro h
      have h2 : N *ᵥ x = M *ᵥ x := by
        calc N *ᵥ x = (M * (M⁻¹ * N)) *ᵥ x := by
                rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
          _ = M *ᵥ x := by rw [← Matrix.mulVec_mulVec, h]
      rw [Matrix.sub_mulVec, h2, sub_self]
    · intro h
      rw [Matrix.sub_mulVec, sub_eq_zero] at h
      rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
  have hex : (∃ x : Fin 4 → ℝ, x ≠ 0 ∧ (M⁻¹ * N) *ᵥ x = x) ↔ (M - N).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact exists_congr fun x => and_congr_right fun _ => key x
  rw [hex, det_A0_sub_A1_eq hlamP.ne' hlamW.ne' hΘ.ne']
  have hc : lamP * lamW * thetaY σ φ α ≠ 0 := (mul_pos (mul_pos hlamP hlamW) hΘ).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (neg_eq_zero.mp h') hc
    · linarith
  · intro h
    rw [h, sub_self, mul_zero]

/-- Galí (2015), p. 174: the sign of `det(A₀ − A₁)` tells on which side of the
boundary the coefficients lie: `det(A₀ − A₁) < 0` iff `LHS > 1`. -/
theorem det_neg_iff {σ φ α β φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW) - A1 σ β lamP lamW).det < 0 ↔
      1 < detLHS σ φ α β lamP lamW φp φw φy := by
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have hc : 0 < lamP * lamW * thetaY σ φ α := mul_pos (mul_pos hlamP hlamW) hΘ
  rw [det_A0_sub_A1_eq hlamP.ne' hlamW.ne' hΘ.ne', neg_mul, neg_lt_zero]
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp hc
    linarith
  · intro h
    exact mul_pos hc (by linarith)

/-- Galí (2015), p. 174: in the special case `φ_y = 0` the determinacy condition
reads `φ_p + φ_w > 1`. -/
theorem detCondition_phiY_zero (σ φ α β lamP lamW φp φw : ℝ) :
    1 < detLHS σ φ α β lamP lamW φp φw 0 ↔ 1 < φp + φw := by
  unfold detLHS
  simp

/-- Galí (2015), p. 175, Figure 6.1: the lower bound on `φ_p + φ_w` implied by the
determinacy condition, `1 − φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)`. -/
noncomputable def threshold (σ φ α β lamP lamW φy : ℝ) : ℝ :=
  1 - φy * (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)

/-- Galí (2015), pp. 174–175: the determinacy condition is `φ_p + φ_w > threshold(φ_y)`. -/
theorem detCondition_iff_threshold (σ φ α β lamP lamW φp φw φy : ℝ) :
    1 < detLHS σ φ α β lamP lamW φp φw φy ↔ threshold σ φ α β lamP lamW φy < φp + φw := by
  unfold detLHS threshold
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 174: at `φ_y = 0` the threshold is `1`. -/
theorem threshold_zero (σ φ α β lamP lamW : ℝ) : threshold σ φ α β lamP lamW 0 = 1 := by
  simp [threshold]

/-- Galí (2015), p. 175 and Figure 6.1: "as `φ_y` increases, the lower bound on
`φ_p + φ_w` consistent with a unique equilibrium declines" — the threshold is
strictly decreasing in `φ_y` for `β < 1`. -/
theorem threshold_strictAnti {σ φ α β lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : β < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    StrictAnti (threshold σ φ α β lamP lamW) := by
  intro a b hab
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have hs : 0 < 1 / lamP + 1 / lamW := by positivity
  have hc : 0 < (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW) :=
    mul_pos (div_pos (by linarith) hΘ) hs
  have e : ∀ y, threshold σ φ α β lamP lamW y
      = 1 - y * ((1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)) := by
    intro y
    unfold threshold
    ring
  rw [e, e]
  have := mul_lt_mul_of_pos_right hab hc
  linarith

end Gali.StickyWagesPrices.System

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The efficient allocation with goods and labour types

Galí (2015), Chapter 6, §6.3, pp. 178–179, eqs. (25)–(27).

The planner maximises period utility `U(C, {N(j)}; Z) = (u(C) − ∫ N(j)^{1+φ}/(1+φ) dj) Z`
(the book's utility of p. 167, `u(C) = (C^{1−σ} − 1)/(1 − σ)` or `log C`) where
`C = (∫ C(i)^{(ε_p−1)/ε_p} di)^{ε_p/(ε_p−1)}` is the CES consumption index, each good is produced
with `C(i) = A N(i)^{1−α}` (eq. (1)), the labour input of firm `i` is the CES index
`N(i) = (∫ N(i,j)^{(ε_w−1)/ε_w} dj)^{ε_w/(ε_w−1)}` of the labour types (eq. (2)), and the
supply of type `j` is `N(j) = ∫ N(i,j) di` (market clearing).

Goods are indexed by a probability space `(G, μ)` and labour types by a probability space
`(J, ν)`; an allocation is a jointly measurable `N(·,·) ≥ 0` on `G × J`, integrable for the
product measure, with integrable disutility and positive total hours `∫∫ N(i,j)`
(`Planner.Feasible`). The book's continuum `[0, 1] × [0, 1]` is
`Planner.planner_optimal_iff_unitInterval`.

## Main results

* `Planner.labourIndex_le_firmHours`: the labour index of each firm is at most its total hours
  (power-mean inequality in the labour-type dimension), with equality iff hours are equal
  across types (`cesIndex_eq_integral_iff`).
* `Planner.aggConsumption_le`, `Planner.aggConsumption_eq_iff`: for total hours `L`, the
  consumption index is at most `A L^{1−α}`, with equality **iff** `N(i,j) = L` for a.e.
  `(i, j)` (both CES dimensions at once).
* `Planner.disutility_ge`: `∫ N(j)^{1+φ}/(1+φ) ≥ L^{1+φ}/(1+φ)` (Jensen).
* `Planner.welfare_le_symWelfare`, `Planner.welfare_eq_symWelfare_iff`: welfare is at most the
  welfare of the symmetric allocation with the same total hours, with equality iff symmetric.
* `symWelfare_isMax_iff_foc`: along symmetric allocations `MRS = MPN` (27) is **necessary and
  sufficient**; `existsUnique_efficient`: it has exactly one solution `N*` (`effEmployment`).
* `Planner.planner_optimal_iff`: a feasible allocation is optimal **iff** (25) `C(i) = C`,
  (26) `N(i,j) = N(j) = N(i) = N` and (27) `MRS = MPN`, a.e.;
  `Planner.planner_optimal_iff_effEmployment`, `Planner.planner_existsUnique`: iff
  `N(i,j) = N*` a.e., and the optimum exists and is unique up to null sets.
* `flex_mrs_eq`, `flex_equilibrium`: in the flexible-price-and-wage equilibrium
  (`W/P = M_w MRS`, `P = M_p (1 − τ) W/MPN`), `MRS = MPN/((1 − τ) M_p M_w)` and employment is
  `N((1 − τ) M_p M_w)`; `flex_equilibrium_efficient_iff`: it is efficient **iff**
  `τ = 1 − 1/(M_p M_w)`; `existsUnique_subsidy`: this subsidy exists, is unique, and lies in
  `(0, 1)`; `optimalSubsidy_flexWages` recovers Chapter 4's `τ = 1/ε_p` when `M_w = 1`.

Utility definitions, tangent-line lemmas, the symmetric problem and `flexEmployment` are restated
from the Chapter 4 project (`Efficient.lean`, `Distortions.lean`). The CES aggregator is
`LaborAggregation.laborIndex` (used both for goods, `ε = ε_p`, and labour types, `ε = ε_w`).
-/

namespace Gali.StickyWagesPrices.Efficiency

open MeasureTheory Filter Topology

/-! ### Period utility (restated from the Chapter 4 project) -/

/-- Galí (2015), p. 167: utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1` and
`log C` for `σ = 1`. Restated from the Chapter 4 project. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 167: disutility of labour of one type, `N^{1+φ}/(1+φ)`. Restated from the
Chapter 4 project. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 167, evaluated at a symmetric allocation `N(j) = N`: period utility
`U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. Restated from the Chapter 4 project. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), p. 178: marginal utility of consumption `u'(C) = C^{−σ}`. Restated from the
Chapter 4 project. -/
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

/-- Galí (2015), p. 178: marginal disutility of labour `N^φ`. Restated from the Chapter 4
project. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 178 (concavity of utility): marginal utility `C^{−σ}` is nonincreasing for
`σ > 0`. Restated from the Chapter 4 project. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its tangent
lines (Galí (2015), p. 178, concavity of utility). Restated from the Chapter 4 project. -/
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

/-- Galí (2015), p. 178: the utility of consumption is concave for `σ > 0`, in tangent-line
form `u(y) ≤ u(x) + x^{−σ}(y − x)`. Restated from the Chapter 4 project. -/
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

/-- Galí (2015), p. 178: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`v(x) + x^φ (y − x) ≤ v(y)`. Restated from the Chapter 4 project. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 178 (`U_c > 0`): the utility of consumption is strictly increasing on
`(0, ∞)`. Restated from the Chapter 4 project. -/
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

/-- Galí (2015), eq. (27), p. 178: the marginal utilities `U_c = C^{−σ} Z`, `U_n = −N^φ Z`
(exact derivatives along a symmetric allocation), whose ratio is the marginal rate of
substitution `−U_n/U_c = C^σ N^φ`. -/
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

/-- Galí (2015), eq. (27), p. 178: the marginal rate of substitution `−U_n/U_c = C^σ N^φ`
(`marginal_utilities`). -/
noncomputable def mrs (σ φ C N : ℝ) : ℝ := C ^ σ * N ^ φ

/-- Galí (2015), p. 178: the marginal product of labour `MPN = (1 − α) A N^{−α}`. -/
noncomputable def mpn (α A N : ℝ) : ℝ := (1 - α) * A * N ^ (-α)

/-- Galí (2015), p. 178: `MPN` is the derivative of the technology `A N^{1−α}`. -/
theorem hasDerivAt_output {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) (mpn α A N) N := by
  refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv ?_
  rw [mpn, show (1 : ℝ) - α - 1 = -α by ring]
  ring

/-- Galí (2015), p. 178: `MPN > 0` for `α < 1`, `A > 0`, `N > 0`. -/
theorem mpn_pos {α A N : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) : 0 < mpn α A N :=
  mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hN _)

/-- Concavity of `x ↦ x^q` for `0 ≤ q ≤ 1` (Bernoulli), in tangent form at `N > 0`:
`x^q ≤ N^q (1 + q (x/N − 1))` (Galí (2015), p. 178, concavity of the aggregators and of
technology). Restated from the Chapter 4 project. -/
theorem rpow_le_tangent {q x N : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hN : 0 < N) (hx : 0 ≤ x) :
    x ^ q ≤ N ^ q * (1 + q * (x / N - 1)) := by
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have h := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at h
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_le_iff₀ hNq] at h
  linarith

/-- Strict concavity of `x ↦ x^q` for `0 < q < 1`: equality in `rpow_le_tangent` forces
`x = N` (Galí (2015), p. 178). Restated from the Chapter 4 project. -/
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

/-! ### The symmetric problem: condition (27) -/

/-- Galí (2015), p. 178: welfare of the symmetric allocation `N(i,j) = N` (so `C = A N^{1−α}`
and `N(j) = N`), `U(A N^{1−α}, N; Z)`. -/
noncomputable def symWelfare (σ φ α A Z N : ℝ) : ℝ := periodUtility σ φ (A * N ^ (1 - α)) N Z

/-- Galí (2015), p. 178: the efficient level of employment, the solution of (27) with
`C = A N^{1−α}`: `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def effEmployment (σ φ α A : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ)) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 178: the derivative of symmetric welfare, `(C^{−σ} MPN − N^φ) Z` with
`C = A N^{1−α}`. -/
theorem hasDerivAt_symWelfare {σ φ α A Z N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hN : 0 < N) :
    HasDerivAt (symWelfare σ φ α A Z)
      (((A * N ^ (1 - α)) ^ (-σ) * mpn α A N - N ^ φ) * Z) N := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := (hasDerivAt_utilC σ hC).comp N (hasDerivAt_output (α := α) (A := A) hN)
  exact (HasDerivAt.sub h1 (hasDerivAt_disutilN hφ N)).mul_const Z

/-- Galí (2015), p. 178 (exponent bookkeeping): `MRS(A N^{1−α}, N) · (1 − α) A^{1−σ}
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

/-- Galí (2015), p. 178: the exponent `φ + α + σ(1 − α)` is positive. -/
theorem effExponent_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < φ + α + σ * (1 - α) := by
  have := mul_pos hσ (by linarith : (0 : ℝ) < 1 - α)
  linarith

/-- Galí (2015), p. 178: efficient employment is positive. -/
theorem effEmployment_pos {σ φ α A : ℝ} (hα1 : α < 1) (hA : 0 < A) :
    0 < effEmployment σ φ α A :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) _

/-- Galí (2015), eq. (27), p. 178, **existence and uniqueness**: along the symmetric allocation
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

/-- Galí (2015), eq. (27), p. 178, **sufficiency**: if `MRS = MPN` at `N₀ > 0` (symmetric
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

/-- Galí (2015), eq. (27), p. 178, **necessity**: if `N₀ > 0` maximises symmetric welfare over
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

/-- Galí (2015), eq. (27), p. 178: along symmetric allocations, `N₀ > 0` maximises welfare
**iff** `MRS = MPN` at `N₀` (necessary and sufficient). -/
theorem symWelfare_isMax_iff_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) ↔
      mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ :=
  ⟨foc_of_symWelfare_isMax hφ hA hZ hN₀,
    fun h _ hN => symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN₀ h hN⟩

/-- Galí (2015), p. 178: efficient employment `N*` maximises symmetric welfare. -/
theorem symWelfare_le_eff {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ (effEmployment_pos hα1 hA)
    ((mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA (effEmployment_pos hα1 hA)).2 rfl) hN

/-- Galí (2015), p. 178: **strict** welfare loss away from efficient employment. -/
theorem symWelfare_lt {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N)
    (hne : N ≠ effEmployment σ φ α A) :
    symWelfare σ φ α A Z N < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  refine lt_of_le_of_ne (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN) fun heq => hne ?_
  refine (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN ?_)
  intro N' hN'
  rw [heq]
  exact symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'

/-- Galí (2015), p. 178, **existence and uniqueness** of efficient employment: exactly one
`N > 0` maximises symmetric welfare, namely `N*`. -/
theorem existsUnique_efficient {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
  refine ⟨effEmployment σ φ α A, ⟨effEmployment_pos hα1 hA,
    fun N' hN' => symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN hmax)

/-! ### CES aggregators on a probability space -/

namespace CES

open Gali.StickyWagesPrices.LaborAggregation

variable {X : Type*} [MeasurableSpace X]

/-- Galí (2015), p. 178: a one-dimensional allocation of hours: measurable, nonnegative,
integrable, with positive total `∫ N > 0`. -/
def PosAlloc (μ : Measure X) (n : X → ℝ) : Prop :=
  Measurable n ∧ (∀ i, 0 ≤ n i) ∧ Integrable n μ ∧ 0 < ∫ i, n i ∂μ

variable {μ : Measure X}

/-- Galí (2015), p. 178: for `ε > 1` the CES exponent `r = (ε − 1)/ε` lies in `(0, 1)`. -/
theorem r_mem {ε : ℝ} (hε : 1 < ε) : 0 < (ε - 1) / ε ∧ (ε - 1) / ε < 1 :=
  ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- Galí (2015), p. 178: the exponent `q = (1 − α)(ε − 1)/ε` lies in `(0, 1)`. Restated from
the Chapter 4 project. -/
theorem q_mem {ε α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  refine ⟨mul_pos (by linarith) hr0, ?_⟩
  calc (1 - α) * ((ε - 1) / ε) ≤ 1 * ((ε - 1) / ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
    _ < 1 := by linarith

/-- Galí (2015), p. 178: for `0 ≤ q ≤ 1`, `n^q` is integrable when `n ≥ 0` is measurable and
integrable (on a probability space). Restated from the Chapter 4 project. -/
theorem integrable_rpow [IsProbabilityMeasure μ] {n : X → ℝ} (hm : Measurable n)
    (h0 : ∀ i, 0 ≤ n i) (hi : Integrable n μ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun i => n i ^ q) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
    (hm.pow_const q).aestronglyMeasurable (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 i) q)]
  have := rpow_le_tangent hq0 hq1 one_pos (h0 i)
  simp only [Real.one_rpow, div_one, one_mul] at this
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right hq1 (h0 i)]

/-- Galí (2015), p. 178 (Jensen): for `0 < q < 1`, `∫ n^q ≤ (∫ n)^q`, with equality **iff**
`n = ∫ n` a.e. Restated from the Chapter 4 project. -/
theorem integral_rpow_le [IsProbabilityMeasure μ] {n : X → ℝ} (hn : PosAlloc μ n) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ i, n i ^ q ∂μ ≤ (∫ i, n i ∂μ) ^ q ∧
      (∫ i, n i ^ q ∂μ = (∫ i, n i ∂μ) ^ q ↔ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  have hf := integrable_rpow hn.1 hn.2.1 hn.2.2.1 hq0.le hq1.le
  set g : X → ℝ := fun i => N ^ q * (1 - q) + N ^ q * q / N * n i with hg
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

/-- Galí (2015), p. 178: a CES index of an a.e. constant `c ≥ 0` is `c`. -/
theorem cesIndex_of_ae_eq [IsProbabilityMeasure μ] {ε c : ℝ} (hε : 1 < ε) (hc : 0 ≤ c)
    {f : X → ℝ} (hf : ∀ᵐ i ∂μ, f i = c) : laborIndex μ ε f = c := by
  obtain ⟨hr0, -⟩ := r_mem hε
  rw [laborIndex, integral_congr_ae (g := fun _ => c ^ ((ε - 1) / ε))
    (by filter_upwards [hf] with i hi; rw [hi])]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact Real.rpow_rpow_inv hc hr0.ne'

/-- Galí (2015), p. 189 (power-mean inequality, labour-type dimension): the CES index is at
most the arithmetic total, `(∫ f^r)^{1/r} ≤ ∫ f` for `r = (ε − 1)/ε ∈ (0, 1)`. -/
theorem cesIndex_le_integral [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {f : X → ℝ}
    (hm : Measurable f) (h0 : ∀ i, 0 ≤ f i) (hi : Integrable f μ) :
    laborIndex μ ε f ≤ ∫ i, f i ∂μ := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  have hnn : 0 ≤ fun i => f i := fun i => h0 i
  rcases (integral_nonneg hnn).lt_or_eq with hpos | hzero
  · have h := (integral_rpow_le ⟨hm, h0, hi, hpos⟩ hr0 hr1).1
    calc laborIndex μ ε f ≤ ((∫ i, f i ∂μ) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ :=
          Real.rpow_le_rpow (integral_nonneg fun i => Real.rpow_nonneg (h0 i) _) h
            (inv_nonneg.2 hr0.le)
      _ = ∫ i, f i ∂μ := Real.rpow_rpow_inv hpos.le hr0.ne'
  · have hz := (integral_eq_zero_iff_of_nonneg hnn hi).1 hzero.symm
    have hzr : (fun i => f i ^ ((ε - 1) / ε)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hz] with i hi
      simp only [Pi.zero_apply] at hi
      rw [hi, Real.zero_rpow hr0.ne']
    rw [laborIndex, integral_congr_ae hzr, integral_zero, Real.zero_rpow (inv_pos.2 hr0).ne',
      ← hzero]

/-- Galí (2015), p. 189: for a positive allocation, the CES index equals the arithmetic total
**iff** the allocation is a.e. constant. -/
theorem cesIndex_eq_integral_iff [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {f : X → ℝ}
    (hf : PosAlloc μ f) : laborIndex μ ε f = ∫ i, f i ∂μ ↔ ∀ᵐ i ∂μ, f i = ∫ j, f j ∂μ := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  rw [← (integral_rpow_le hf hr0 hr1).2]
  have hI : 0 ≤ ∫ i, f i ^ ((ε - 1) / ε) ∂μ :=
    integral_nonneg fun i => Real.rpow_nonneg (hf.2.1 i) _
  constructor
  · intro h
    rw [← h, laborIndex, Real.rpow_inv_rpow hI hr0.ne']
  · intro h
    rw [laborIndex, h, Real.rpow_rpow_inv hf.2.2.2.le hr0.ne']

/-- Galí (2015), p. 178: `(A x^{1−α})^r = A^r x^{(1−α) r}`. Restated from the Chapter 4
project. -/
theorem output_rpow {A α r x : ℝ} (hA : 0 < A) (hx : 0 ≤ x) :
    (A * x ^ (1 - α)) ^ r = A ^ r * x ^ ((1 - α) * r) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]

/-- Galí (2015), p. 178: `(A^r N^{(1−α) r})^{1/r} = A N^{1−α}`. Restated from the Chapter 4
project. -/
theorem symmetric_index {ε A α N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hN : 0 ≤ N) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ ((ε - 1) / ε)⁻¹
      = A * N ^ (1 - α) := by
  have hr : (ε - 1) / ε ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hN _),
    Real.rpow_rpow_inv hA.le hr, ← Real.rpow_mul hN, mul_assoc, mul_inv_cancel₀ hr, mul_one]

end CES

/-! ### The planner with goods and labour types: conditions (25) and (26) -/

namespace Planner

open CES Gali.StickyWagesPrices.LaborAggregation

variable {G J : Type*} [MeasurableSpace G] [MeasurableSpace J]

/-- Galí (2015), eq. (2), p. 164: the labour index of firm `i`,
`N(i) = (∫ N(i,j)^{(ε_w−1)/ε_w} dj)^{ε_w/(ε_w−1)}`. -/
noncomputable def labourIndex (ν : Measure J) (εw : ℝ) (n : G × J → ℝ) (i : G) : ℝ :=
  laborIndex ν εw fun j => n (i, j)

/-- Galí (2015), p. 189: the total hours of all types worked at firm `i`, `∫ N(i,j) dj`. -/
noncomputable def firmHours (ν : Measure J) (n : G × J → ℝ) (i : G) : ℝ := ∫ j, n (i, j) ∂ν

/-- Galí (2015), pp. 166 and 189 (market clearing): the hours supplied by type `j`,
`N(j) = ∫ N(i,j) di`. -/
noncomputable def labourSupply (μ : Measure G) (n : G × J → ℝ) (j : J) : ℝ := ∫ i, n (i, j) ∂μ

/-- Galí (2015), p. 189: total hours `∫∫ N(i,j) di dj`. -/
noncomputable def totalHours (μ : Measure G) (ν : Measure J) (n : G × J → ℝ) : ℝ :=
  ∫ p, n p ∂(μ.prod ν)

/-- Galí (2015), eq. (1), p. 164: output of good `i`, `C(i) = Y(i) = A N(i)^{1−α}`. -/
noncomputable def goodsOutput (ν : Measure J) (εw A α : ℝ) (n : G × J → ℝ) (i : G) : ℝ :=
  A * labourIndex ν εw n i ^ (1 - α)

/-- Galí (2015), p. 178: the consumption index of the allocation `N(·,·)`. -/
noncomputable def aggConsumption (μ : Measure G) (ν : Measure J) (εp εw A α : ℝ)
    (n : G × J → ℝ) : ℝ :=
  laborIndex μ εp (goodsOutput ν εw A α n)

/-- Galí (2015), pp. 167 and 178: the planner's objective
`U(C, {N(j)}; Z) = (u(C) − ∫ N(j)^{1+φ}/(1+φ) dj) Z`. -/
noncomputable def welfare (μ : Measure G) (ν : Measure J) (σ φ εp εw A α Z : ℝ)
    (n : G × J → ℝ) : ℝ :=
  (utilC σ (aggConsumption μ ν εp εw A α n) - ∫ j, disutilN φ (labourSupply μ n j) ∂ν) * Z

/-- Galí (2015), p. 178: a feasible allocation of hours `N(i,j)`: jointly measurable,
nonnegative, integrable, with integrable disutility and positive total hours. -/
def Feasible (μ : Measure G) (ν : Measure J) (φ : ℝ) (n : G × J → ℝ) : Prop :=
  Measurable n ∧ (∀ p, 0 ≤ n p) ∧ Integrable n (μ.prod ν) ∧
    Integrable (fun j => disutilN φ (labourSupply μ n j)) ν ∧ 0 < totalHours μ ν n

variable {μ : Measure G} {ν : Measure J}

/-- Galí (2015), p. 189: firm hours `i ↦ ∫ N(i,j) dj` form a positive one-dimensional
allocation whose total is total hours (Fubini). -/
theorem firmHours_posAlloc [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : ℝ}
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    PosAlloc μ (firmHours ν n) ∧ ∫ i, firmHours ν n i ∂μ = totalHours μ ν n := by
  obtain ⟨hm, h0, hi, -, hpos⟩ := hn
  have htot : ∫ i, firmHours ν n i ∂μ = totalHours μ ν n := (integral_prod n hi).symm
  exact ⟨⟨hm.stronglyMeasurable.integral_prod_right'.measurable,
    fun i => integral_nonneg fun j => h0 _, hi.integral_prod_left, htot ▸ hpos⟩, htot⟩

/-- Galí (2015), p. 189: the supplies `j ↦ N(j)` are integrable and sum to total hours. -/
theorem labourSupply_integral [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {n : G × J → ℝ}
    (hi : Integrable n (μ.prod ν)) :
    Integrable (labourSupply μ n) ν ∧ ∫ j, labourSupply μ n j ∂ν = totalHours μ ν n :=
  ⟨hi.integral_prod_right, (integral_prod_symm n hi).symm⟩

omit [MeasurableSpace G] in
/-- Galí (2015), p. 164: the labour index of every firm is nonnegative. -/
theorem labourIndex_nonneg {εw : ℝ} {n : G × J → ℝ} (h0 : ∀ p, 0 ≤ n p) (i : G) :
    0 ≤ labourIndex ν εw n i :=
  laborIndex_nonneg fun j => h0 (i, j)

/-- Galí (2015), p. 164: the labour index `i ↦ N(i)` is measurable. -/
theorem labourIndex_measurable [IsProbabilityMeasure ν] {εw : ℝ} {n : G × J → ℝ}
    (hm : Measurable n) : Measurable (labourIndex ν εw n) :=
  ((hm.pow_const ((εw - 1) / εw)).stronglyMeasurable.integral_prod_right').measurable.pow_const _

/-- Galí (2015), p. 189 (**power mean, labour types**): for a.e. firm, its labour index is at
most its total hours, `N(i) ≤ ∫ N(i,j) dj`. -/
theorem labourIndex_le_firmHours [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {εw : ℝ}
    (hε : 1 < εw) {n : G × J → ℝ} (hm : Measurable n) (h0 : ∀ p, 0 ≤ n p)
    (hi : Integrable n (μ.prod ν)) :
    ∀ᵐ i ∂μ, labourIndex ν εw n i ≤ firmHours ν n i := by
  filter_upwards [hi.prod_right_ae] with i hii
  exact cesIndex_le_integral hε (hm.comp measurable_prodMk_left) (fun j => h0 _) hii

/-- Galí (2015), p. 178: the consumption index is `C = (A^r ∫ N(i)^q)^{1/r}`,
`r = (ε_p − 1)/ε_p`, `q = (1 − α) r`. -/
theorem aggConsumption_eq {εp εw A α : ℝ} (hA : 0 < A) {n : G × J → ℝ} (h0 : ∀ p, 0 ≤ n p) :
    aggConsumption μ ν εp εw A α n
      = (A ^ ((εp - 1) / εp) *
          ∫ i, labourIndex ν εw n i ^ ((1 - α) * ((εp - 1) / εp)) ∂μ) ^ ((εp - 1) / εp)⁻¹ := by
  rw [aggConsumption, laborIndex, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun i => output_rpow hA
    (labourIndex_nonneg h0 i))

/-- Galí (2015), p. 178: the integrand `N(i)^q` is integrable and bounded by
`(∫ N(i,j) dj)^q`, whose integral is at most `L^q`, `L` total hours. -/
theorem integral_labourIndex_rpow [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ εw q : ℝ} (hε : 1 < εw) (hq0 : 0 < q) (hq1 : q < 1) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    Integrable (fun i => labourIndex ν εw n i ^ q) μ ∧
      Integrable (fun i => firmHours ν n i ^ q) μ ∧
      (∀ᵐ i ∂μ, labourIndex ν εw n i ^ q ≤ firmHours ν n i ^ q) ∧
      ∫ i, labourIndex ν εw n i ^ q ∂μ ≤ ∫ i, firmHours ν n i ^ q ∂μ ∧
      ∫ i, firmHours ν n i ^ q ∂μ ≤ totalHours μ ν n ^ q := by
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  have hmi := integrable_rpow hP.1 hP.2.1 hP.2.2.1 hq0.le hq1.le
  have hle : ∀ᵐ i ∂μ, labourIndex ν εw n i ^ q ≤ firmHours ν n i ^ q := by
    filter_upwards [labourIndex_le_firmHours hε hn.1 hn.2.1 hn.2.2.1] with i hi
    exact Real.rpow_le_rpow (labourIndex_nonneg hn.2.1 i) hi hq0.le
  have hxi : Integrable (fun i => labourIndex ν εw n i ^ q) μ := by
    refine Integrable.mono' hmi ((labourIndex_measurable hn.1).pow_const q).aestronglyMeasurable ?_
    filter_upwards [hle] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) q)]
    exact hi
  refine ⟨hxi, hmi, hle, integral_mono_of_nonneg (Eventually.of_forall fun i =>
    Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) q) hmi hle, ?_⟩
  rw [← htot]
  exact (integral_rpow_le hP hq0 hq1).1

/-- Galí (2015), eqs. (1)–(2), p. 178: for a feasible allocation with total hours `L`, the
consumption index is at most `A L^{1−α}`. -/
theorem aggConsumption_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ εp εw A α : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    aggConsumption μ ν εp εw A α n ≤ A * totalHours μ ν n ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεp
  obtain ⟨-, -, -, h1, h2⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hεp hA hn.2.2.2.2.le]
  refine Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA.le _)
    (integral_nonneg fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _)) ?_
    (inv_nonneg.2 hr0.le)
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hA.le _)

/-- Galí (2015), p. 178: if `N(i,j) = c` a.e., then `N(i) = c` for a.e. firm, `N(j) = c` for
a.e. type, `C(i) = A c^{1−α}` for a.e. good and `C = A c^{1−α}`. -/
theorem symmetric_consequences [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {εp εw A α c : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) (hA : 0 < A) (hc : 0 ≤ c)
    {n : G × J → ℝ} (hm : Measurable n) (h : ∀ᵐ p ∂(μ.prod ν), n p = c) :
    (∀ᵐ i ∂μ, labourIndex ν εw n i = c) ∧ (∀ᵐ j ∂ν, labourSupply μ n j = c) ∧
      (∀ᵐ i ∂μ, goodsOutput ν εw A α n i = A * c ^ (1 - α)) ∧
      aggConsumption μ ν εp εw A α n = A * c ^ (1 - α) := by
  have hms : MeasurableSet {p : G × J | n p = c} := measurableSet_eq_fun hm measurable_const
  have hii : ∀ᵐ i ∂μ, ∀ᵐ j ∂ν, n (i, j) = c := (Measure.ae_prod_iff_ae_ae hms).1 h
  have hjj : ∀ᵐ j ∂ν, ∀ᵐ i ∂μ, n (i, j) = c := (Measure.ae_ae_comm (p := fun i j => n (i, j) = c)
    hms).1 hii
  have hL : ∀ᵐ i ∂μ, labourIndex ν εw n i = c := by
    filter_upwards [hii] with i hi
    exact cesIndex_of_ae_eq hεw hc hi
  have hY : ∀ᵐ i ∂μ, goodsOutput ν εw A α n i = A * c ^ (1 - α) := by
    filter_upwards [hL] with i hi
    rw [goodsOutput, hi]
  refine ⟨hL, ?_, hY, cesIndex_of_ae_eq hεp (mul_nonneg hA.le (Real.rpow_nonneg hc _)) hY⟩
  filter_upwards [hjj] with j hj
  rw [labourSupply, integral_congr_ae hj]
  simp

/-- Galí (2015), p. 178: the consumption index of a feasible allocation is positive. -/
theorem aggConsumption_pos [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ εp εw A α : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) : 0 < aggConsumption μ ν εp εw A α n := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεw
  obtain ⟨hxi, -, -, -, -⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  rw [aggConsumption_eq hA hn.2.1]
  refine Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hA _) ?_) _
  have hnn : 0 ≤ fun i => labourIndex ν εw n i ^ ((1 - α) * ((εp - 1) / εp)) :=
    fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _
  rcases (integral_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg hnn hxi).1 h.symm
    have hm0 : ∀ᵐ i ∂μ, firmHours ν n i = 0 := by
      filter_upwards [hz, hn.2.2.1.prod_right_ae] with i hi hii
      have hx0 : labourIndex ν εw n i = 0 :=
        ((Real.rpow_eq_zero_iff_of_nonneg (labourIndex_nonneg hn.2.1 i)).1 hi).1
      have hI0 : ∫ j, n (i, j) ^ ((εw - 1) / εw) ∂ν = 0 :=
        ((Real.rpow_eq_zero_iff_of_nonneg (integral_nonneg fun j =>
          Real.rpow_nonneg (hn.2.1 _) _)).1 hx0).1
      have hpow := (integral_eq_zero_iff_of_nonneg (fun j => Real.rpow_nonneg (hn.2.1 (i, j)) _)
        (integrable_rpow (hn.1.comp measurable_prodMk_left) (fun j => hn.2.1 _) hii hr0.le
          (r_mem hεw).2.le)).1 hI0
      have hsec : (fun j => n (i, j)) =ᵐ[ν] 0 := by
        filter_upwards [hpow] with j hj
        exact ((Real.rpow_eq_zero_iff_of_nonneg (hn.2.1 (i, j))).1 hj).1
      rw [firmHours, integral_congr_ae hsec]
      simp
    have := hn.2.2.2.2
    rw [← htot, integral_congr_ae hm0] at this
    simp at this

/-- Galí (2015), eqs. (25)–(26), p. 178 (**both CES dimensions**): the bound
`C ≤ A L^{1−α}` holds with equality **iff** `N(i,j) = L` for a.e. `(i, j)`. -/
theorem aggConsumption_eq_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ εp εw A α : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A)
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    aggConsumption μ ν εp εw A α n = A * totalHours μ ν n ^ (1 - α) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεp
  set q := (1 - α) * ((εp - 1) / εp) with hqdef
  set L := totalHours μ ν n with hLdef
  have hL : 0 < L := hn.2.2.2.2
  obtain ⟨hxi, hmi, hle, h1, h2⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  constructor
  · intro hC
    rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hεp hA hL.le] at hC
    have hAr : 0 < A ^ ((εp - 1) / εp) := Real.rpow_pos_of_pos hA _
    have hIx : ∫ i, labourIndex ν εw n i ^ q ∂μ = L ^ q := by
      by_contra hne
      have hlt := lt_of_le_of_ne (h1.trans h2) hne
      have := Real.rpow_lt_rpow (mul_nonneg hAr.le
        (integral_nonneg fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _))
        (mul_lt_mul_of_pos_left hlt hAr) (inv_pos.2 hr0)
      rw [hC] at this
      exact lt_irrefl _ this
    have hIm : ∫ i, firmHours ν n i ^ q ∂μ = L ^ q := le_antisymm h2 (hIx ▸ h1)
    have hmL : ∀ᵐ i ∂μ, firmHours ν n i = L := by
      have := (integral_rpow_le hP hq0 hq1).2.1 (by rw [htot]; exact hIm)
      rwa [htot] at this
    have hdiff : (fun i => firmHours ν n i ^ q - labourIndex ν εw n i ^ q) =ᵐ[μ] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae
        (f := fun i => firmHours ν n i ^ q - labourIndex ν εw n i ^ q) ?_ (hmi.sub hxi)).1 ?_
      · filter_upwards [hle] with i hi
        exact sub_nonneg.2 hi
      · rw [integral_sub hmi hxi, hIm, hIx, sub_self]
    have hxm : ∀ᵐ i ∂μ, labourIndex ν εw n i = firmHours ν n i := by
      filter_upwards [hdiff] with i hi
      simp only [Pi.zero_apply, sub_eq_zero] at hi
      rw [← Real.rpow_rpow_inv (labourIndex_nonneg hn.2.1 i) hq0.ne', ← hi,
        Real.rpow_rpow_inv (hP.2.1 i) hq0.ne']
    have hii : ∀ᵐ i ∂μ, ∀ᵐ j ∂ν, n (i, j) = L := by
      filter_upwards [hmL, hxm, hn.2.2.1.prod_right_ae] with i hmi' hxi' hint
      have hPi : PosAlloc ν fun j => n (i, j) :=
        ⟨hn.1.comp measurable_prodMk_left, fun j => hn.2.1 _, hint, by
          change 0 < firmHours ν n i
          rw [hmi']
          exact hL⟩
      have := (cesIndex_eq_integral_iff hεw hPi).1 (by
        change labourIndex ν εw n i = firmHours ν n i
        exact hxi')
      filter_upwards [this] with j hj
      rw [hj]
      exact hmi'
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hn.1 measurable_const)).2 hii
  · intro h
    exact (symmetric_consequences (α := α) hεp hεw hA hL.le hn.1 h).2.2.2

/-- Galí (2015), p. 178 (Jensen, labour types): the disutility of a feasible allocation is at
least the disutility of total hours, `∫ N(j)^{1+φ}/(1+φ) ≥ L^{1+φ}/(1+φ)`. -/
theorem disutility_ge [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : ℝ} (hφ : 0 ≤ φ)
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    disutilN φ (totalHours μ ν n) ≤ ∫ j, disutilN φ (labourSupply μ n j) ∂ν := by
  set L := totalHours μ ν n with hLdef
  have hL : 0 < L := hn.2.2.2.2
  obtain ⟨hsi, hsum⟩ := labourSupply_integral (μ := μ) (ν := ν) hn.2.2.1
  have hpt : ∀ j, (disutilN φ L - L ^ φ * L) + L ^ φ * labourSupply μ n j
      ≤ disutilN φ (labourSupply μ n j) := fun j => by
    have := disutilN_tangent_le hφ hL (integral_nonneg (μ := μ) fun i => hn.2.1 (i, j))
    unfold labourSupply at this ⊢
    linarith
  have hint := integral_mono (f := fun j => (disutilN φ L - L ^ φ * L) +
    L ^ φ * labourSupply μ n j) ((integrable_const _).add (hsi.const_mul _)) hn.2.2.2.1 hpt
  rw [integral_add (integrable_const _) (hsi.const_mul _), integral_const_mul, hsum,
    integral_const] at hint
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint
  linarith

/-- Galí (2015), p. 178: welfare of a feasible allocation is at most the welfare of the
symmetric allocation with the same total hours. -/
theorem welfare_le_symWelfare [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n ≤ symWelfare σ φ α A Z (totalHours μ ν n) := by
  unfold welfare symWelfare periodUtility
  refine mul_le_mul_of_nonneg_right (sub_le_sub ?_ (disutility_ge hφ hn)) hZ.le
  rcases (aggConsumption_le hεp hεw hα0 hα1 hA hn).lt_or_eq with h | h
  · exact (utilC_lt_utilC (aggConsumption_pos hεp hεw hα0 hα1 hA hn) h).le
  · rw [h]

/-- Galí (2015), eqs. (25)–(26), p. 178: equality in `welfare_le_symWelfare` holds **iff** the
allocation is symmetric, `N(i,j) = L` for a.e. `(i, j)`. -/
theorem welfare_eq_symWelfare_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n = symWelfare σ φ α A Z (totalHours μ ν n) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
  rw [← aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn]
  have hD := disutility_ge hφ hn
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne (aggConsumption_le hεp hεw hα0 hα1 hA hn) hne
    have h1 := utilC_lt_utilC (σ := σ) (aggConsumption_pos hεp hεw hα0 hα1 hA hn) hlt
    unfold welfare symWelfare periodUtility at h
    have h2 := mul_right_cancel₀ hZ.ne' h
    linarith
  · intro h
    have hsym := (aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn).1 h
    obtain ⟨-, hS, -, -⟩ := symmetric_consequences (α := α) hεp hεw hA hn.2.2.2.2.le hn.1 hsym
    have hDeq : ∫ j, disutilN φ (labourSupply μ n j) ∂ν = disutilN φ (totalHours μ ν n) := by
      rw [integral_congr_ae (g := fun _ => disutilN φ (totalHours μ ν n))
        (by filter_upwards [hS] with j hj; rw [hj])]
      simp
    rw [welfare, symWelfare, periodUtility, h, hDeq]

/-- Galí (2015), p. 178: a **non-symmetric** feasible allocation is strictly worse than the
symmetric allocation with the same total hours. -/
theorem welfare_lt_symWelfare [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n)
    (hns : ¬ ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) :
    welfare μ ν σ φ εp εw A α Z n < symWelfare σ φ α A Z (totalHours μ ν n) :=
  lt_of_le_of_ne (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn)
    fun h => hns ((welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).1 h)

/-- Galí (2015), p. 178: a constant allocation `N(i,j) = N > 0` is feasible. -/
theorem feasible_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ N : ℝ}
    (hN : 0 < N) : Feasible μ ν φ (fun _ => N) :=
  ⟨measurable_const, fun _ => hN.le, integrable_const N, by
    simp only [labourSupply, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact integrable_const _, by simpa [totalHours] using hN⟩

/-- Galí (2015), p. 178: the welfare of the constant allocation `N(i,j) = N` is the symmetric
welfare `U(A N^{1−α}, N; Z)`. -/
theorem welfare_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {σ φ εp εw A α Z N : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hA : 0 < A) (hN : 0 < N) :
    welfare μ ν σ φ εp εw A α Z (fun _ => N) = symWelfare σ φ α A Z N := by
  obtain ⟨-, -, -, hC⟩ := symmetric_consequences (μ := μ) (ν := ν) (α := α) hεp hεw hA hN.le
    measurable_const (Eventually.of_forall fun _ => rfl)
  rw [welfare, hC, symWelfare, periodUtility]
  simp [labourSupply]

/-- Galí (2015), p. 178: every feasible allocation is (weakly) worse than the efficient
allocation `N(i,j) = N*`. -/
theorem welfare_le_eff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {σ φ εp εw A α Z : ℝ}
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn).trans
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2.2)

/-- Galí (2015), p. 178: any non-symmetric feasible allocation is **strictly** worse than the
efficient allocation. -/
theorem welfare_lt_of_not_symmetric [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) (hns : ¬ ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) :
    welfare μ ν σ φ εp εw A α Z n < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_lt_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn hns).trans_le
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2.2)

/-- Galí (2015), eqs. (25)–(27), p. 178 (**necessary and sufficient**): a feasible allocation
maximises welfare over all feasible allocations iff
(25) `C(i) = C` for a.e. good;
(26) `N(i,j) = N` for a.e. `(i, j)`, `N(i) = N` for a.e. firm and `N(j) = N` for a.e. type;
(27) `MRS = MPN`;
where `C` is the consumption index and `N` total hours. -/
theorem planner_optimal_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    (∀ n', Feasible μ ν φ n' →
        welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) ↔
      (∀ᵐ i ∂μ, goodsOutput ν εw A α n i = aggConsumption μ ν εp εw A α n) ∧
      ((∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) ∧
        (∀ᵐ i ∂μ, labourIndex ν εw n i = totalHours μ ν n) ∧
        (∀ᵐ j ∂ν, labourSupply μ n j = totalHours μ ν n)) ∧
      mrs σ φ (aggConsumption μ ν εp εw A α n) (totalHours μ ν n)
        = mpn α A (totalHours μ ν n) := by
  set N := totalHours μ ν n with hNdef
  have hN : 0 < N := hn.2.2.2.2
  constructor
  · intro hopt
    have hsym : ∀ᵐ p ∂(μ.prod ν), n p = N := by
      refine (welfare_eq_symWelfare_iff (σ := σ) hφ hεp hεw hα0 hα1 hA hZ hn).1 (le_antisymm
        (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn) ?_)
      rw [← welfare_const (μ := μ) (ν := ν) (εp := εp) (εw := εw) hεp hεw hA hN]
      exact hopt _ (feasible_const hN)
    obtain ⟨hL, hS, hY, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    have hmax : ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
      intro N' hN'
      rw [← welfare_const (μ := μ) (ν := ν) (εp := εp) (εw := εw) hεp hεw hA hN',
        ← (welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).2 hsym]
      exact hopt _ (feasible_const hN')
    refine ⟨?_, ⟨hsym, hL, hS⟩, ?_⟩
    · filter_upwards [hY] with i hi
      rw [hi, hC]
    · rw [hC]
      exact foc_of_symWelfare_isMax hφ hA hZ hN hmax
  · rintro ⟨-, ⟨hsym, -, -⟩, hfoc⟩ n' hn'
    obtain ⟨-, -, -, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    rw [hC] at hfoc
    rw [(welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).2 hsym]
    exact (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn').trans
      (symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN hfoc hn'.2.2.2.2)

/-- Galí (2015), §6.3, p. 178: a feasible allocation is optimal **iff** `N(i,j) = N*` for
a.e. `(i, j)`, where `N*` is efficient employment (`effEmployment`). -/
theorem planner_optimal_iff_effEmployment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    (∀ n', Feasible μ ν φ n' →
        welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = effEmployment σ φ α A := by
  rw [planner_optimal_iff hσ hφ hεp hεw hα0 hα1 hA hZ hn]
  have hN : 0 < totalHours μ ν n := hn.2.2.2.2
  constructor
  · rintro ⟨-, ⟨hsym, -, -⟩, hfoc⟩
    rw [(aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn).2 hsym,
      mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN] at hfoc
    filter_upwards [hsym] with p hp
    rw [hp, hfoc]
  · intro h
    have hint : totalHours μ ν n = effEmployment σ φ α A := by
      rw [totalHours, integral_congr_ae h]
      simp
    have hsym : ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
      filter_upwards [h] with p hp
      rw [hp, hint]
    obtain ⟨hL, hS, hY, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    refine ⟨?_, ⟨hsym, hL, hS⟩, ?_⟩
    · filter_upwards [hY] with i hi
      rw [hi, hC]
    · rw [hC, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN, hint]

/-- Galí (2015), §6.3, p. 178, **existence and uniqueness**: the efficient allocation
`N(i,j) = N*` is feasible and optimal, and every optimal allocation equals it a.e. -/
theorem planner_existsUnique [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    Feasible μ ν φ (fun _ => effEmployment σ φ α A) ∧
      (∀ n', Feasible μ ν φ n' → welfare μ ν σ φ εp εw A α Z n'
        ≤ welfare μ ν σ φ εp εw A α Z (fun _ => effEmployment σ φ α A)) ∧
      ∀ n, Feasible μ ν φ n →
        (∀ n', Feasible μ ν φ n' →
          welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) →
        ∀ᵐ p ∂(μ.prod ν), n p = effEmployment σ φ α A := by
  have hf := feasible_const (μ := μ) (ν := ν) (φ := φ) (effEmployment_pos (σ := σ) (φ := φ)
    hα1 hA)
  refine ⟨hf, (planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hf).2
    (Eventually.of_forall fun _ => rfl), fun n hn hopt => ?_⟩
  exact (planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hn).1 hopt

/-- Galí (2015), p. 178: Lebesgue measure on the continuum `[0, 1]` of goods (or of labour
types) is a probability measure. -/
theorem isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

/-- Galí (2015), §6.3, p. 178, on the book's **continua of goods and labour types
`[0, 1] × [0, 1]`**: a feasible allocation is optimal iff `N(i,j) = N*` for a.e. `(i, j)`,
iff (25)–(27) hold. -/
theorem planner_optimal_iff_unitInterval {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : ℝ × ℝ → ℝ}
    (hn : Feasible (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) φ n) :
    (∀ n' : ℝ × ℝ → ℝ,
        Feasible (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) φ n' →
        welfare (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) σ φ εp εw A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1))
            σ φ εp εw A α Z n) ↔
      ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
        n p = effEmployment σ φ α A := by
  have := isProbabilityMeasure_unitInterval
  exact planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hn

end Planner

/-! ### The decentralised flexible-price-and-wage equilibrium (pp. 178–179) -/

/-- Galí (2015), pp. 165 and 168: the desired gross markups `M_p = ε_p/(ε_p − 1)` and
`M_w = ε_w/(ε_w − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 168: `M > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), p. 168: `M > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- Galí (2015), p. 178: with flexible prices and wages, equal prices and equal wages give
`C(i) = (P(i)/P)^{−ε_p} C = C` (eq. (7)) and `N(i,j) = (W(j)/W)^{−ε_w} N(i) = N(i)` (eq. (3)):
conditions (25) and the first part of (26) hold. -/
theorem demand_at_equal_prices {ε P C : ℝ} (hP : 0 < P) : (P / P) ^ (-ε) * C = C := by
  rw [div_self hP.ne', Real.one_rpow, one_mul]

/-- Galí (2015), p. 178: equilibrium employment when `MRS = MPN/w` along the symmetric
allocation,
`N(w) = ((1 − α) A^{1−σ}/w)^{1/(φ + α + σ(1 − α))}`. Restated from the Chapter 4 project. -/
noncomputable def flexEmployment (σ φ α A w : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ) / w) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 178: `N(w) > 0`. Restated from the Chapter 4 project. -/
theorem flexEmployment_pos {σ φ α A w : ℝ} (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    0 < flexEmployment σ φ α A w :=
  Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw) _

/-- Galí (2015), p. 178: along the symmetric allocation, `MRS = MPN/w` holds for `N > 0`
**iff** `N = N(w)`. Restated from the Chapter 4 project. -/
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

/-- Galí (2015), p. 178: **existence and uniqueness** of the equilibrium employment level under
a wedge `w > 0`. Restated from the Chapter 4 project. -/
theorem existsUnique_flex {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    ∃! N, 0 < N ∧ mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w :=
  ⟨flexEmployment σ φ α A w, ⟨flexEmployment_pos hα1 hA hw,
    (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw (flexEmployment_pos hα1 hA hw)).2 rfl⟩,
    fun _ ⟨hN, h⟩ => (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h⟩

/-- Galí (2015), p. 178: the equilibrium level is efficient **iff** there is no wedge,
`N(w) = N* ↔ w = 1` (for `w > 0`). -/
theorem flexEmployment_eq_eff_iff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    flexEmployment σ φ α A w = effEmployment σ φ α A ↔ w = 1 := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  constructor
  · intro h
    rw [flexEmployment, effEmployment] at h
    have h2 := congrArg (fun x => x ^ (φ + α + σ * (1 - α))) h
    rw [Real.rpow_inv_rpow (div_pos hc hw).le hk.ne', Real.rpow_inv_rpow hc.le hk.ne'] at h2
    rw [div_eq_iff hw.ne'] at h2
    nlinarith
  · intro h
    rw [h, flexEmployment, effEmployment, div_one]

/-- Galí (2015), p. 178: the flexible-price-and-wage equilibrium conditions, the wage rule
`W/P = M_w MRS` and the price rule `P = M_p (1 − τ) W/MPN` (employment subsidy `τ < 1`), imply
`MRS = MPN/((1 − τ) M_p M_w)`. -/
theorem flex_mrs_eq {Mp Mw τ W P mrsv mpnv : ℝ} (hP : 0 < P) (hτ : τ < 1)
    (hMp : 0 < Mp) (hMw : 0 < Mw) (hwage : W / P = Mw * mrsv)
    (hprice : P = Mp * ((1 - τ) * W / mpnv)) :
    mrsv = mpnv / ((1 - τ) * Mp * Mw) := by
  have h1 : (0 : ℝ) < 1 - τ := by linarith
  rw [hprice] at hwage
  have hW : W ≠ 0 := by
    intro h0
    rw [h0] at hprice
    simp at hprice
    linarith
  field_simp at hwage ⊢
  linear_combination (-1 : ℝ) * hwage

/-- Galí (2015), p. 179: under the flexible-price-and-wage rules, (27) `MRS = MPN` holds
**iff** `(1 − τ) M_p M_w = 1`. -/
theorem flex_efficient_iff_wedge {Mp Mw τ W P mrsv mpnv : ℝ} (hP : 0 < P) (hm : 0 < mpnv)
    (hτ : τ < 1) (hMp : 0 < Mp) (hMw : 0 < Mw) (hwage : W / P = Mw * mrsv)
    (hprice : P = Mp * ((1 - τ) * W / mpnv)) :
    mrsv = mpnv ↔ (1 - τ) * Mp * Mw = 1 := by
  rw [flex_mrs_eq hP hτ hMp hMw hwage hprice]
  have hw : 0 < (1 - τ) * Mp * Mw := mul_pos (mul_pos (by linarith) hMp) hMw
  rw [div_eq_iff hw.ne']
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_one]

/-- Galí (2015), p. 179: `(1 − τ) M_p M_w = 1` **iff** `τ = 1 − 1/(M_p M_w)`. -/
theorem wedge_eq_one_iff_subsidy {Mp Mw τ : ℝ} (hM : Mp * Mw ≠ 0) :
    (1 - τ) * Mp * Mw = 1 ↔ τ = 1 - 1 / (Mp * Mw) := by
  constructor
  · intro h
    have h1 : 1 - τ = 1 / (Mp * Mw) := by
      rw [eq_div_iff hM, ← mul_assoc]
      exact h
    linarith
  · intro h
    rw [h, sub_sub_cancel, mul_assoc, one_div_mul_cancel hM]

/-- Galí (2015), p. 179: the optimal subsidy `τ* = 1 − 1/(M_p M_w)` lies in `(0, 1)`. -/
theorem optimalSubsidy_mem {εp εw : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) :
    0 < 1 - 1 / (markup εp * markup εw) ∧ 1 - 1 / (markup εp * markup εw) < 1 := by
  have h1 := one_lt_markup hεp
  have h2 := one_lt_markup hεw
  have hM : 1 < markup εp * markup εw := by nlinarith
  have hpos : 0 < 1 / (markup εp * markup εw) := by positivity
  refine ⟨?_, by linarith⟩
  have : 1 / (markup εp * markup εw) < 1 := (div_lt_one (by linarith)).2 hM
  linarith

/-- Galí (2015), p. 179 (consistency with ch. 4): with flexible wages (`M_w = 1`) the optimal
subsidy is Chapter 4's `τ = 1/ε_p`. -/
theorem optimalSubsidy_flexWages {εp : ℝ} (hεp : 1 < εp) :
    1 - 1 / (markup εp * 1) = 1 / εp := by
  have h1 : εp - 1 ≠ 0 := by linarith
  have h2 : εp ≠ 0 := by linarith
  rw [markup, mul_one]
  field_simp
  ring

/-- Galí (2015), pp. 178–179 (**the flexible-price-and-wage equilibrium**): along the
symmetric allocation with employment `N > 0`, if the wage rule `W/P = M_w MRS` and the price
rule `P = M_p (1 − τ) W/MPN` hold, then `N = N((1 − τ) M_p M_w)`, and the allocation is
efficient (`N = N*`) **iff** `τ = 1 − 1/(M_p M_w)`. -/
theorem flex_equilibrium {σ φ εp εw α A τ W P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp)
    (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) (hP : 0 < P)
    (hN : 0 < N) (hwage : W / P = markup εw * mrs σ φ (A * N ^ (1 - α)) N)
    (hprice : P = markup εp * ((1 - τ) * W / mpn α A N)) :
    N = flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw) ∧
      (N = effEmployment σ φ α A ↔ τ = 1 - 1 / (markup εp * markup εw)) := by
  have hMp := markup_pos hεp
  have hMw := markup_pos hεw
  have hw : 0 < (1 - τ) * markup εp * markup εw := mul_pos (mul_pos (by linarith) hMp) hMw
  have h := flex_mrs_eq hP hτ hMp hMw hwage hprice
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h
  refine ⟨hN', ?_⟩
  rw [hN', flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw,
    wedge_eq_one_iff_subsidy (mul_pos hMp hMw).ne']

/-- Galí (2015), pp. 178–179: the flexible-price-and-wage equilibrium allocation **maximises
welfare iff** `τ = 1 − 1/(M_p M_w)` (in the sense of the symmetric problem, which by
`Planner.planner_optimal_iff` is the planner's problem). -/
theorem flex_equilibrium_efficient_iff {σ φ εp εw α A Z τ W P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hτ : τ < 1) (hP : 0 < P) (hN : 0 < N)
    (hwage : W / P = markup εw * mrs σ φ (A * N ^ (1 - α)) N)
    (hprice : P = markup εp * ((1 - τ) * W / mpn α A N)) :
    (∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N) ↔
      τ = 1 - 1 / (markup εp * markup εw) := by
  rw [symWelfare_isMax_iff_foc hσ hφ hα0 hα1 hA hZ hN, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN]
  exact (flex_equilibrium hσ hφ hεp hεw hα0 hα1 hA hτ hP hN hwage hprice).2

/-- Galí (2015), p. 179 (**the optimal subsidy exists and is unique**): exactly one subsidy
`τ < 1` makes the flexible-price-and-wage equilibrium employment efficient, namely
`τ = 1 − 1/(M_p M_w)`. -/
theorem existsUnique_subsidy {σ φ εp εw α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp)
    (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    ∃! τ, τ < 1 ∧ flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw)
      = effEmployment σ φ α A := by
  have hMp := markup_pos hεp
  have hMw := markup_pos hεw
  have hM : markup εp * markup εw ≠ 0 := (mul_pos hMp hMw).ne'
  have key : ∀ τ, τ < 1 → (flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw)
      = effEmployment σ φ α A ↔ τ = 1 - 1 / (markup εp * markup εw)) := fun τ hτ => by
    rw [flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA
      (mul_pos (mul_pos (by linarith) hMp) hMw), wedge_eq_one_iff_subsidy hM]
  obtain ⟨-, h1⟩ := optimalSubsidy_mem hεp hεw
  exact ⟨1 - 1 / (markup εp * markup εw), ⟨h1, (key _ h1).2 rfl⟩,
    fun τ ⟨hτ, h⟩ => (key τ hτ).1 h⟩

end Gali.StickyWagesPrices.Efficiency

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The welfare loss function with sticky wages and prices

Galí (2015), Chapter 6, §6.3 (p. 179, eqs. (28)–(29)) and Appendix 6.1 (pp. 188–192): the
second-order approximation to the household's welfare around an efficient steady state, with
price **and** wage dispersion, the loss function `𝕎`, the average loss `L`, and the
comparative statics of the wage-inflation weight.

This module builds on `LaborAggregation` (CES indices, labour demand, `dispIntegral`, `d_w`,
`d_p`, the exact employment identity) and `WageDispersion` (cumulant expansions, `d_w`, `d_p`
to second order, the Calvo wage cross-section `wageMix` and the exact Lemma 2), and imports
them rather than restating them.

## Dispersion terms (pp. 189–190)

* `effWageDisp` `d_w^φ = ((1−α)/(1+φ)) log ∫ (W(j)/W)^{−ε_w(1+φ)}`: `d_w^φ = (Υ/2) var_j w + O(s³)`
  (`effWageDisp_second_order`), `Υ = ε_w(1−α)(1+ε_wφ)`; `effWageDisp_sub_wageDisp` is the book's
  `∫ n̂(j)² = n̂² + ε_w² var_j w` step (p. 189).
* With the book's power disutility the exact identity
  `∫ (N^d (W(j)/W)^{−ε_w})^{1+φ}/(1+φ) dj = (N^d e^{log Δ_w^φ/(1+φ)})^{1+φ}/(1+φ)`
  (`disutility_types_eq`) reduces the labour-type cross-section to **effective hours** `Ñ` with
  `(1 − α) log(Ñ/N) = y − a + d_p + d_w^φ` exactly (`effectiveHours_identity`).

## Two layers for (28)

* **(A) exact algebra.** `secondOrderUtility_eq`: given an efficient steady state and the
  exact identity `(1 − α) n = y − a + d`, the second-order polynomial in log deviations equals
  `−(K/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε_p/Θ) var_p + Υ var_w] + t.i.p.` plus explicit
  higher-order terms; `secondOrderUtility_distorted` is the inefficient case (`Φ ŷ` term).
* **(B) the analytic bridge.** `period_utility_second_order`: for `C³` utility, along any
  one-parameter family of size `s`, period utility equals that quadratic form plus t.i.p.
  up to `O(s³)`. `period_utility_second_order_families` discharges every hypothesis for the
  actual model: price and wage cross-sections `p̄ + s ζ(i)`, `w̄ + s ξ(j)`, firm labour demand
  from (1) and (7), type-`j` employment from (3), the book's disutility, and output,
  technology and preference deviations `O(s)`.

## Lemma 2 and the loss

* Lemma 2 is `WageDispersion.lemma2` / `wage_lemma2_calvo` (the Calvo mixture is the same for
  prices with `θ_p`). **Survey error 8:** the book's equality holds only up to the
  policy-independent term `θ V_0/(1 − βθ)` (`lemma2_inherited`,
  `lemma2_printed_fails_with_inherited`, `welfare_eq_loss_inherited`).
* `welfare_eq_loss`, `welfare_eq_loss_calvo`: (28),
  `𝕎 = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`;
  `welfare_stationary`: (29).
* `wageWeight_strictMonoOn_eps`, `wageWeight_strictAnti_alpha`, `wageWeight_strictMonoOn_theta`:
  the wage-inflation weight `ε_w(1−α)/λ_w` is increasing in `ε_w`, in `1 − α` and in `θ_w`
  (all three claims of p. 179 hold); `lambdaW_strictAntiOn_theta`: `λ_w` is decreasing in
  `θ_w`.

The one-dimensional Taylor tools of layer (B) are restated from the Chapter 4 project.
-/

namespace Gali.StickyWagesPrices.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.StickyWagesPrices.LaborAggregation Gali.StickyWagesPrices.WageDispersion

variable {G : Type*} [MeasurableSpace G]

variable {μ : Measure G}

/-! ### Dispersion of wages, effective hours (pp. 189–190) -/

/-- Galí (2015), App. 6.1, p. 190: `Υ = ε_w(1 − α)(1 + ε_w φ)`. -/
noncomputable def upsilon (α φ εw : ℝ) : ℝ := εw * (1 - α) * (1 + εw * φ)

/-- Galí (2015), App. 6.1, pp. 189–190: the **effective** wage dispersion
`d_w^φ = ((1 − α)/(1 + φ)) log ∫ (W(j)/W)^{−ε_w(1+φ)}`, which collects `d_w` and the extra
disutility of unequal hours across types. -/
noncomputable def effWageDisp (ν : Measure G) (α φ εw : ℝ) (W : G → ℝ) : ℝ :=
  (1 - α) / (1 + φ) * Real.log (dispIntegral ν εw (-(εw * (1 + φ))) W)

/-- Galí (2015), App. 6.1, p. 190: along `X(i) = exp(x̄ + s z(i))`, relative values raised to
`e` are `(X(i)/X)^e = e^{−e K((1−ε)s)/(1−ε)} e^{e s z(i)}`. -/
theorem ratio_rpow_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (e pbar s : ℝ) (i : G) :
    (Real.exp (pbar + s * z i) / cesIndex μ ε (fun i => Real.exp (pbar + s * z i))) ^ e
      = Real.exp (-(e * (cgf z μ ((1 - ε) * s) / (1 - ε)))) * Real.exp (e * s * z i) := by
  rw [cesIndex_family hz hB hε, ← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Galí (2015), App. 6.1, p. 190: along the family the dispersion integrand is integrable and
the dispersion integral `∫ (X(i)/X)^e` is positive. -/
theorem dispIntegral_family_pos [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (e pbar s : ℝ) :
    Integrable (fun i => (Real.exp (pbar + s * z i) /
        cesIndex μ ε (fun i => Real.exp (pbar + s * z i))) ^ e) μ ∧
      0 < dispIntegral μ ε e (fun i => Real.exp (pbar + s * z i)) := by
  have hrel := ratio_rpow_family (μ := μ) hz hB hε e pbar s
  refine ⟨?_, ?_⟩
  · simp_rw [hrel]
    exact (integrable_exp_mul hz hB (e * s)).const_mul _
  · rw [dispIntegral]
    simp_rw [hrel]
    rw [integral_const_mul]
    exact mul_pos (Real.exp_pos _) (mgf_pos (integrable_exp_mul hz hB (e * s)))

/-- Galí (2015), App. 6.1, pp. 189–190: the effective wage dispersion satisfies
`d_w^φ = (Υ/2) var_j w + O(s³)`, `Υ = ε_w(1 − α)(1 + ε_w φ)`. -/
theorem effWageDisp_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {α φ εw : ℝ} (hφ : 0 ≤ φ) (hεw : 1 < εw) (wbar : ℝ) :
    (fun s => effWageDisp μ α φ εw (fun i => Real.exp (wbar + s * z i)) -
        upsilon α φ εw / 2 * crossVar μ (fun i => wbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have h := (log_dispIntegral_second_order (μ := μ) hz hB (ε := εw) (by linarith)
    (-(εw * (1 + φ))) wbar).const_mul_left ((1 - α) / (1 + φ))
  refine h.congr_left fun s => ?_
  rw [effWageDisp, upsilon]
  field_simp
  ring

/-- Galí (2015), App. 6.1, p. 189 (**the `∫ n̂(j)² = n̂² + ε_w² var_j w` step**): the effective
wage dispersion exceeds `d_w` by `((1 − α) ε_w² φ/2) var_j w + O(s³)`, the extra disutility of
hours that differ across labour types. -/
theorem effWageDisp_sub_wageDisp [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {α φ εw : ℝ} (hφ : 0 ≤ φ) (hεw : 1 < εw) (wbar : ℝ) :
    (fun s => effWageDisp μ α φ εw (fun i => Real.exp (wbar + s * z i)) -
        dW μ α εw (fun i => Real.exp (wbar + s * z i)) -
        (1 - α) * εw ^ 2 * φ / 2 * crossVar μ (fun i => wbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  refine ((effWageDisp_second_order (μ := μ) (α := α) hz hB hφ hεw wbar).sub
    (dW_second_order (μ := μ) hz hB (ε := εw) (by linarith) α wbar)).congr_left fun s => ?_
  rw [upsilon]
  ring

/-! ### Exact employment and disutility identities (pp. 189–190) -/

/-- Galí (2015), pp. 189–190 (exact, pointwise): firm labour demand `N(i) = (Y(i)/A)^{1/(1−α)}`
with `Y(i) = (P(i)/P)^{−ε_p} Y` is `(Y/A)^{1/(1−α)} (P(i)/P)^{−ε_p/(1−α)}` (the integrated form
is `LaborAggregation.firm_index_level`). -/
theorem firmLabour_eq {α εp Y A x : ℝ} (hY : 0 ≤ Y) (hA : 0 < A) (hx : 0 ≤ x) :
    (Y * x ^ (-εp) / A) ^ (1 - α)⁻¹ = (Y / A) ^ (1 - α)⁻¹ * x ^ (-εp / (1 - α)) := by
  rw [mul_div_right_comm, Real.mul_rpow (div_nonneg hY hA.le) (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx]
  rfl

/-- Galí (2015), pp. 189–190 (**exact disutility identity**): with type employment
`𝒩(j) = (W(j)/W)^{−ε_w} N^d` and the book's disutility, if `Δ_w^φ = ∫ (W(j)/W)^{−ε_w(1+φ)}`
is positive, then `∫ 𝒩(j)^{1+φ}/(1+φ) dj = (N^d e^{log Δ_w^φ/(1+φ)})^{1+φ}/(1+φ)`: the
cross-section of hours acts exactly like **effective hours** `N^d (Δ_w^φ)^{1/(1+φ)}`. -/
theorem disutility_types_eq {φ εw Nd : ℝ} (hφ : 0 ≤ φ) (hNd : 0 ≤ Nd)
    {W : G → ℝ} (hW : ∀ j, 0 < W j) (hWbar : 0 < cesIndex μ εw W)
    (hpos : 0 < dispIntegral μ εw (-(εw * (1 + φ))) W) :
    ∫ j, ((W j / cesIndex μ εw W) ^ (-εw) * Nd) ^ (1 + φ) / (1 + φ) ∂μ
      = (Nd * Real.exp (Real.log (dispIntegral μ εw (-(εw * (1 + φ))) W) / (1 + φ))) ^ (1 + φ)
        / (1 + φ) := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have hx : ∀ j, 0 ≤ W j / cesIndex μ εw W := fun j => (div_pos (hW j) hWbar).le
  have hpt : ∀ j, ((W j / cesIndex μ εw W) ^ (-εw) * Nd) ^ (1 + φ) / (1 + φ)
      = Nd ^ (1 + φ) / (1 + φ) * (W j / cesIndex μ εw W) ^ (-(εw * (1 + φ))) := fun j => by
    rw [Real.mul_rpow (Real.rpow_nonneg (hx j) _) hNd, ← Real.rpow_mul (hx j)]
    rw [show -εw * (1 + φ) = -(εw * (1 + φ)) by ring]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Real.mul_rpow hNd (Real.exp_pos _).le, ← Real.exp_mul,
    div_mul_cancel₀ _ h1, Real.exp_log hpos, dispIntegral]
  ring

/-- Galí (2015), p. 190 (**exact employment identity in logs**): with steady state
`C = A N^{1−α}` (`N > 0`), output `Y = C e^{y}`, technology `A_t = A e^{a}`, aggregate firm
labour `N^d = (Y/A_t)^{1/(1−α)} Δ_p` with `Δ_p = e^{d_p/(1−α)}`, effective hours
`Ñ = N^d e^{log Δ_w^φ/(1+φ)}` with `log Δ_w^φ = (1+φ) d_w^φ/(1−α)`, one has `Ñ = N e^{n}` with
`(1 − α) n = y − a + d_p + d_w^φ`. -/
theorem effectiveHours_identity {α A N y a dp dw : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    (A * N ^ (1 - α) * Real.exp y / (A * Real.exp a)) ^ (1 - α)⁻¹ *
        Real.exp (dp / (1 - α)) * Real.exp (dw / (1 - α))
      = N * Real.exp ((y - a + dp + dw) / (1 - α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hY : A * N ^ (1 - α) * Real.exp y / (A * Real.exp a)
      = N ^ (1 - α) * Real.exp (y - a) := by
    rw [Real.exp_sub]
    field_simp
  rw [hY, Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.exp_pos _).le,
    Real.rpow_rpow_inv hN.le h1, ← Real.exp_mul, mul_assoc, mul_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- A process that is `O(s)` tends to `0` (Galí 2015, App. 6.1). Restated from the Chapter 4
project. -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-! ### One-dimensional Taylor expansions (restated from the Chapter 4 project) -/

/-- Galí (2015), App. 6.1, p. 188 (**second-order Taylor expansion with a cubic remainder**).
Restated from the Chapter 4 project. -/
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

/-- Galí (2015), App. 6.1, p. 188: `e^x = 1 + x + x²/2 + O(x³)`. Restated from the Chapter 4
project. -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 6.1, p. 188: `e^x − 1 = O(x)`. Restated from the Chapter 4 project. -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 6.1, p. 188 (**second-order expansion in log deviations**):
`f(X e^{x}) − f(X) = f'(X) X (x + x²/2) + f''(X) X² x²/2 + O(x³)`. Restated from the
Chapter 4 project. -/
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

/-! ### Layer (A): the exact algebra of App. 6.1 -/

/-- Galí (2015), eq. (28), p. 179: the output-gap coefficient `σ + (φ + α)/(1 − α)`. -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), p. 191: `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`, so that `ŷ^e_t = ψ_ya a_t`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), App. 6.1, p. 188 (the second-order polynomial in log deviations): with
`Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y` (output = consumption), `n` (hours)
and `z` (`Z = e^z`). Restated from the Chapter 4 project. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 6.1, p. 191: the terms independent of policy, an explicit function of the
shocks `a`, `z` only. Restated from the Chapter 4 project. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 6.1, p. 191, last display (with `Φ = 0`): the policy-relevant quadratic
form `−(K/2)[(σ + (φ+α)/(1−α))(y − ŷ^e)² + (ε_p/Θ) var_i p + Υ var_j w]`, `ŷ^e = ψ_ya a`. -/
noncomputable def welfareQuadratic (K σ φ α εp εw y a vp vw : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + εp / bigTheta α εp * vp +
    upsilon α φ εw * vw)

/-- Galí (2015), p. 191: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)`. -/
theorem gapCoeff_mul_psiYA {σ φ α : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), p. 191, the completing-the-square coefficient:
`−(1 − σ) + (1 + φ)/(1 − α) = σ + (φ + α)/(1 − α)`. -/
theorem gapCoeff_eq {σ φ α : ℝ} (hα : α ≠ 1) :
    -(1 - σ) + (1 + φ) / (1 - α) = gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff
  field_simp
  ring

/-- Galí (2015), p. 190: the bookkeeping `ε_w/2 + ε_w² φ/2 = Υ/(2(1 − α))`: `d_w` plus the
`∫ n̂(j)²` term (times `(1 − α)`) give `Υ/2`. -/
theorem upsilon_split {α φ εw : ℝ} :
    (1 - α) * εw / 2 + (1 - α) * εw ^ 2 * φ / 2 = upsilon α φ εw / 2 := by
  unfold upsilon
  ring

/-- Galí (2015), App. 6.1, pp. 188–191 (**completing the square, exact**). Suppose the steady
state is efficient, `U_n N = −(1 − α) U_c C`, and hours satisfy `(1 − α) n = y − a + d`. Then
for every `v_p`, `v_w` the second-order polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) v_p + Υ v_w] + t.i.p. + K((ε_p/2Θ) v_p + (Υ/2) v_w − d)`
`− K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`; the last two terms are of third order once
`d − (ε_p/2Θ) v_p − (Υ/2) v_w = O(s³)` and `d = O(s²)`. -/
theorem secondOrderUtility_eq {Ubar K UnN σ φ α εp εw y n z a d vp vw : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = welfareQuadratic K σ φ α εp εw y a vp vw + tip Ubar K σ φ α a z +
        K * (εp / (2 * bigTheta α εp) * vp + upsilon α φ εw / 2 * vw - d) -
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

/-- Galí (2015), App. 6.1, pp. 190–191 (**an inefficient steady state**): if
`U_n N = −(1 − Φ)(1 − α) U_c C` (steady-state distortion `Φ`) and `(1 − α) n = y − a + d`,
the polynomial equals its value at the efficient coefficient plus
`Φ K (y − a + d) + Φ (1 − α) K ((1+φ)/2 n² + n z)`: the book's `Φ ŷ` term (`−Φ K a` is
t.i.p.) plus `Φ` times second-order terms, dropped by the "small distortion" assumption. -/
theorem secondOrderUtility_distorted {Ubar K UnN σ φ α Φ y n z a d : ℝ}
    (hUn : UnN = -(1 - Φ) * (1 - α) * K) (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = secondOrderUtility Ubar K (-(1 - α) * K) σ φ y n z + Φ * K * (y - a + d) +
        Φ * (1 - α) * K * ((1 + φ) / 2 * n ^ 2 + n * z) := by
  subst hUn
  unfold secondOrderUtility
  linear_combination (Φ * K) * hn

/-! ### Layer (B): the analytic bridge -/

/-- Galí (2015), App. 6.1, pp. 188–191 (**second-order approximation of period utility,
rigorous form**). Period utility is `(u(C) + w(N)) Z` with `u`, `w` of class `C³` near the
steady state, `σ = −U_cc C/U_c`, `φ = U_nn N/U_n`, efficient steady state
`U_n N = −(1 − α) U_c C`. Along a one-parameter family of size `s` with `y, a, z = O(s)`,
variances `v_p, v_w = O(s²)`, the exact identity `(1 − α) n = y − a + d` and the dispersion
relation `d − (ε_p/2Θ) v_p − (Υ/2) v_w = O(s³)`:
`U_t − U = −(U_c C/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) v_p + Υ v_w] + t.i.p.(a, z) + O(s³)`. -/
theorem period_utility_second_order {u w : ℝ → ℝ} {C N σ φ α εp εw : ℝ}
    {y n a z d vp vw : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hvp : vp =O[𝓝 0] fun s => s ^ 2)
    (hvw : vw =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - εp / (2 * bigTheta α εp) * vp s - upsilon α φ εw / 2 * vw s)
      =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α εp εw (y s) (a s) (vp s) (vw s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  set cp := εp / (2 * bigTheta α εp) with hcp
  set cw := upsilon α φ εw / 2 with hcw
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    (((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hvp.const_mul_left cp)).add
      (hvw.const_mul_left cw)).congr_left fun s => by ring
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
  have hA : ∀ s, secondOrderUtility Ubar K UnN σ φ (y s) (n s) (z s)
      = welfareQuadratic K σ φ α εp εw (y s) (a s) (vp s) (vw s) + tip Ubar K σ φ α (a s) (z s) +
        K * (cp * vp s + cw * vw s - d s) -
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
  have T6 : (fun s => K * (cp * vp s + cw * vw s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
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

/-- Galí (2015), pp. 167 and 188: the book's disutility of hours, as a function of (effective)
hours, `w(N) = −N^{1+φ}/(1+φ)`, has derivative `−N^φ` everywhere (`φ ≥ 0`). -/
theorem deriv_negDisutil {φ : ℝ} (hφ : 0 ≤ φ) :
    deriv (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) = fun x => -x ^ φ := by
  funext x
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have h : HasDerivAt (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ)))
      (-((1 + φ) * x ^ (1 + φ - 1) / (1 + φ))) x :=
    ((Real.hasDerivAt_rpow_const (x := x) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).neg
  rw [h.deriv, show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 189: for the book's disutility, `φ = U_nn N/U_n` at every `N > 0`:
`w''(N) N = φ w'(N)`. -/
theorem negDisutil_phi {φ N : ℝ} (hφ : 0 ≤ φ) (hN : 0 < N) :
    iteratedDeriv 2 (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N * N
      = φ * deriv (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_negDisutil hφ]
  have h : HasDerivAt (fun x : ℝ => -x ^ φ) (-(φ * N ^ (φ - 1))) N :=
    (Real.hasDerivAt_rpow_const (x := N) (p := φ) (Or.inl hN.ne')).neg
  rw [h.deriv]
  have : N ^ (φ - 1) * N = N ^ φ := by
    rw [Real.rpow_sub_one hN.ne']
    field_simp
  linear_combination (-φ) * this

/-- Galí (2015), p. 188: the book's disutility is `C³` at every `N > 0`. -/
theorem negDisutil_contDiffAt {φ N : ℝ} (hN : 0 < N) :
    ContDiffAt ℝ 3 (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N :=
  ((Real.contDiffAt_rpow_const_of_ne (p := 1 + φ) hN.ne').div_const _).neg

/-- Galí (2015), App. 6.1, pp. 188–191 (**the second-order approximation for the actual
model**). Goods on a probability space `(G, μ)`, labour types on `(J, ν)`. Steady state
`N > 0`, `A > 0`, `C = A N^{1−α}`; `u` is `C³` at `C` with `σ = −u''C/u'`; the book's
disutility; efficient steady state `N^φ N = (1 − α) u'(C) C` (i.e. `MRS = MPN`). Families of
size `s`: prices `P(i) = e^{p̄ + s ζ(i)}`, wages `W(j) = e^{w̄ + s ξ(j)}` (`ζ, ξ` bounded and
measurable), output `Y = C e^{y}`, technology `A e^{a}`, preference shifter `e^{z}`
(`y, a, z = O(s)`). Firm labour is `N(i) = (Y(i)/A_t)^{1/(1−α)}` with `Y(i) = (P(i)/P)^{−ε_p} Y`
(eqs. (1), (7)), aggregate firm labour `N^d = ∫ N(i)`, and type employment
`𝒩(j) = (W(j)/W)^{−ε_w} N^d` (eq. (3)). Then period utility
`(u(Y) − ∫ 𝒩(j)^{1+φ}/(1+φ) dj) e^{z}` minus its steady-state value equals
`−(u'(C)C/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) var_i p + Υ var_j w] + t.i.p.(a, z)` up to `O(s³)`. -/
theorem period_utility_second_order_families {J : Type*} [MeasurableSpace J] {ν : Measure J}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {u : ℝ → ℝ}
    {N A σ φ α εp εw pbar wbar Bp Bw : ℝ} {ζ : G → ℝ} {ξ : J → ℝ} {y a z : ℝ → ℝ}
    (hζ : Measurable ζ) (hBp : ∀ i, |ζ i| ≤ Bp) (hξ : Measurable ξ) (hBw : ∀ j, |ξ j| ≤ Bw)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hσ0 : 0 < σ) (hφ0 : 0 ≤ φ)
    (hN : 0 < N) (hA : 0 < A) (hu : ContDiffAt ℝ 3 u (A * N ^ (1 - α)))
    (hσ : iteratedDeriv 2 u (A * N ^ (1 - α)) * (A * N ^ (1 - α))
      = -σ * deriv u (A * N ^ (1 - α)))
    (hEff : N ^ φ * N = (1 - α) * (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))))
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) :
    (fun s => (u (A * N ^ (1 - α) * Real.exp (y s)) -
          ∫ j, ((Real.exp (wbar + s * ξ j) / cesIndex ν εw (fun j => Real.exp (wbar + s * ξ j)))
              ^ (-εw) *
            ∫ i, ((A * N ^ (1 - α) * Real.exp (y s)) *
              (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
                ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ ∂μ) ^ (1 + φ) / (1 + φ) ∂ν) *
          Real.exp (z s) -
        (u (A * N ^ (1 - α)) - N ^ (1 + φ) / (1 + φ)) -
        (welfareQuadratic (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))) σ φ α εp εw (y s) (a s)
            (crossVar μ (fun i => pbar + s * ζ i)) (crossVar ν (fun j => wbar + s * ξ j)) +
          tip (u (A * N ^ (1 - α)) - N ^ (1 + φ) / (1 + φ))
            (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  set C := A * N ^ (1 - α) with hCdef
  set w : ℝ → ℝ := fun x => -(x ^ (1 + φ) / (1 + φ)) with hwdef
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1φ : (1 : ℝ) + φ ≠ 0 := by linarith
  have hden : σ * (1 - α) + φ + α ≠ 0 := by
    have : 0 < σ * (1 - α) := mul_pos hσ0 (by linarith)
    linarith
  set dp : ℝ → ℝ := fun s => dP μ α εp (fun i => Real.exp (pbar + s * ζ i)) with hdp
  set dw : ℝ → ℝ := fun s => effWageDisp ν α φ εw (fun j => Real.exp (wbar + s * ξ j))
    with hdw
  set n : ℝ → ℝ := fun s => (y s - a s + dp s + dw s) / (1 - α) with hndef
  have hn : ∀ s, (1 - α) * n s = y s - a s + (dp s + dw s) := fun s => by
    simp only [hndef]
    field_simp
    ring
  have hdd : (fun s => (dp s + dw s) - εp / (2 * bigTheta α εp) *
      crossVar μ (fun i => pbar + s * ζ i) - upsilon α φ εw / 2 *
      crossVar ν (fun j => wbar + s * ξ j)) =O[𝓝 0] fun s => s ^ 3 :=
    ((dP_second_order hζ hBp hεp hα0 hα1 pbar).add
      (effWageDisp_second_order (α := α) hξ hBw hφ0 hεw wbar)).congr_left fun s => by ring
  have hwd : deriv w N = -N ^ φ := by
    rw [hwdef, deriv_negDisutil hφ0]
  have hEff' : deriv w N * N = -(1 - α) * (deriv u C * C) := by
    rw [hwd]
    linarith
  have key := period_utility_second_order (u := u) (w := w) (C := C) (N := N) (εp := εp)
    (εw := εw) (d := fun s => dp s + dw s) hu (negDisutil_contDiffAt hN) hσ
    (negDisutil_phi hφ0 hN) hEff' hα1.ne hden hy ha hz
    (crossVar_family_isBigO hζ hBp pbar) (crossVar_family_isBigO hξ hBw wbar) hdd hn
  refine key.congr_left fun s => ?_
  -- the exact identities of the model
  have hPint := dispIntegral_family_pos (μ := μ) hζ hBp (ε := εp) (by linarith)
    (-εp / (1 - α)) pbar s
  have hWint := dispIntegral_family_pos (μ := ν) hξ hBw (ε := εw) (by linarith)
    (-(εw * (1 + φ))) wbar s
  have hPpos : 0 < cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)) := by
    rw [cesIndex_family hζ hBp (by linarith)]
    exact Real.exp_pos _
  have hWpos : 0 < cesIndex ν εw (fun j => Real.exp (wbar + s * ξ j)) := by
    rw [cesIndex_family hξ hBw (by linarith)]
    exact Real.exp_pos _
  have hYpos : 0 ≤ C * Real.exp (y s) :=
    (mul_pos (mul_pos hA (Real.rpow_pos_of_pos hN _)) (Real.exp_pos _)).le
  have hNd : ∫ i, ((C * Real.exp (y s)) *
        (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
          ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ ∂μ
      = (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
          Real.exp (dp s / (1 - α)) := by
    have hpt : ∀ i, ((C * Real.exp (y s)) *
        (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
          ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹
        = (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
          (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
            ^ (-εp / (1 - α)) := fun i =>
      firmLabour_eq hYpos (mul_pos hA (Real.exp_pos _))
        (div_pos (Real.exp_pos _) hPpos).le
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [hdp]
    simp only [dP, priceDisp]
    rw [mul_div_cancel_left₀ _ h1, Real.exp_log hPint.2, dispIntegral]
  have hNdpos : 0 ≤ (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
      Real.exp (dp s / (1 - α)) :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hYpos (mul_pos hA (Real.exp_pos _)).le) _)
      (Real.exp_pos _).le
  have hD := disutility_types_eq (μ := ν) (εw := εw) hφ0 hNdpos
    (W := fun j => Real.exp (wbar + s * ξ j)) (fun j => Real.exp_pos _) hWpos hWint.2
  have hdwexp : Real.exp (Real.log (dispIntegral ν εw (-(εw * (1 + φ)))
      (fun j => Real.exp (wbar + s * ξ j))) / (1 + φ)) = Real.exp (dw s / (1 - α)) := by
    rw [hdw]
    simp only [effWageDisp]
    congr 1
    field_simp
  have hEH := effectiveHours_identity (y := y s) (a := a s) (dp := dp s) (dw := dw s) hα1 hA hN
  rw [hNd, hD, hdwexp, hEH]
  have hnN : N * Real.exp ((y s - a s + dp s + dw s) / (1 - α)) = N * Real.exp (n s) := rfl
  rw [hnN]
  simp only [hwdef]
  ring_nf

/-- Galí (2015), p. 192 (**Lemma 2 with inherited dispersion**, survey error 8): with any
`V_0 ≥ 0`, `∑ βᵗ V_{t+1} = θ V_0/(1 − βθ) + θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`: the printed
equality holds only up to the policy-independent term `θ V_0/(1 − βθ)`. -/
theorem lemma2_inherited {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ * V 0 / (1 - β * θ) + θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0 hq hrec hQ
  convert h using 1
  field_simp

/-- Galí (2015), p. 192 (**survey error 8, counterexample**): with inherited dispersion
`V_0 = 1`, `θ ∈ (0, 1)` and no inflation (`q ≡ 0`), `V_t = θᵗ` satisfies the Calvo recursion and
`∑ βᵗ V_{t+1} = θ/(1 − βθ) > 0`, while the printed Lemma 2 gives `0`: the equality holds only
up to terms independent of policy. -/
theorem lemma2_printed_fails_with_inherited {θ β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ t, θ ^ (t + 1) = θ * θ ^ t + θ / (1 - θ) * 0) ∧
      HasSum (fun t => β ^ t * θ ^ (t + 1)) (θ / (1 - β * θ)) ∧
      θ / (1 - β * θ) ≠ θ / ((1 - β * θ) * (1 - θ)) * ∑' _ : ℕ, β ^ 0 * (0 : ℝ) := by
  have hβθ : β * θ < 1 := by nlinarith
  refine ⟨fun t => by ring, ?_, ?_⟩
  · have h := (hasSum_geometric_of_lt_one (mul_nonneg hβ0 hθ0.le) hβθ).mul_left θ
    have e : (fun t => β ^ t * θ ^ (t + 1)) = fun t => θ * (β * θ) ^ t := by
      funext t
      rw [mul_pow, pow_succ]
      ring
    rw [e, div_eq_mul_inv]
    exact h
  · simp only [mul_zero, tsum_zero]
    exact (div_pos hθ0 (by linarith)).ne'

/-! ### The welfare loss (28) and the average loss (29) -/

/-- Galí (2015), p. 166: `λ_p = (1 − θ_p)(1 − βθ_p)Θ/θ_p`. -/
noncomputable def lambdaP (β θp α εp : ℝ) : ℝ := (1 - θp) * (1 - β * θp) / θp * bigTheta α εp

/-- Galí (2015), eq. (15), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lambdaW (β θw φ εw : ℝ) : ℝ := (1 - θw) * (1 - β * θw) / (θw * (1 + εw * φ))

/-- Galí (2015), eq. (28), p. 179: the weight on price inflation `ε_p/λ_p`. -/
noncomputable def priceWeight (β θp α εp : ℝ) : ℝ := εp / lambdaP β θp α εp

/-- Galí (2015), eq. (28), p. 179: the weight on wage inflation `ε_w(1 − α)/λ_w`. -/
noncomputable def wageWeight (β θw α φ εw : ℝ) : ℝ := εw * (1 - α) / lambdaW β θw φ εw

/-- Galí (2015), eq. (28), p. 179: the period loss
`½[(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
noncomputable def periodLoss (β θp θw σ φ α εp εw ygap pp pw : ℝ) : ℝ :=
  (gapCoeff σ φ α * ygap ^ 2 + priceWeight β θp α εp * pp ^ 2 +
    wageWeight β θw α φ εw * pw ^ 2) / 2

/-- Galí (2015), eq. (28), p. 179 (**the welfare loss `𝕎`**, for a given path, up to t.i.p.). -/
noncomputable def welfareLoss (β θp θw σ φ α εp εw : ℝ) (ygap pp pw : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss β θp θw σ φ α εp εw (ygap t) (pp t) (pw t)

/-- Galí (2015), eq. (29), p. 179 (**the average period loss `L`**) as a function of the
variances. -/
noncomputable def avgLoss (β θp θw σ φ α εp εw varY varP varW : ℝ) : ℝ :=
  (gapCoeff σ φ α * varY + priceWeight β θp α εp * varP + wageWeight β θw α φ εw * varW) / 2

/-- Galí (2015), p. 192: `(ε_p/Θ) · θ_p/((1 − βθ_p)(1 − θ_p)) = ε_p/λ_p`. -/
theorem priceWeight_of_dispersion {β θ α εp : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβθ : β * θ < 1) (hα : α < 1) :
    εp / bigTheta α εp * (θ / ((1 - β * θ) * (1 - θ))) = priceWeight β θ α εp := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold priceWeight lambdaP bigTheta
  field_simp

/-- Galí (2015), p. 192: `Υ · θ_w/((1 − βθ_w)(1 − θ_w)) = ε_w(1 − α)/λ_w`, the step from the
wage dispersion term to the wage-inflation weight. -/
theorem wageWeight_of_dispersion {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβθ : β * θ < 1) (hφε : 1 + εw * φ ≠ 0) :
    upsilon α φ εw * (θ / ((1 - β * θ) * (1 - θ))) = wageWeight β θ α φ εw := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  unfold wageWeight lambdaW upsilon
  field_simp

/-- Galí (2015), p. 192 (**(28) from the dispersion form, exact**): if the price and wage
cross-sectional variances follow the exact Calvo recursions
`V_{t+1} = θ V_t + (θ/(1−θ)) (Δm_t)²` with no inherited dispersion, then
`½ ∑ βᵗ [Γ ỹ_t² + (ε_p/Θ) V^p_{t+1} + Υ V^w_{t+1}] = 𝕎(ỹ, Δm^p, Δm^w)`. -/
theorem welfare_eq_loss {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap Dp Dw Vp Vw : ℕ → ℝ} (hVp0 : Vp 0 = 0) (hVw0 : Vw 0 = 0)
    (hrecp : ∀ t, Vp (t + 1) = θp * Vp t + θp / (1 - θp) * Dp t ^ 2)
    (hrecw : ∀ t, Vw (t + 1) = θw * Vw t + θw / (1 - θw) * Dw t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hDp : Summable fun t => β ^ t * Dp t ^ 2)
    (hDw : Summable fun t => β ^ t * Dw t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + εp / bigTheta α εp * Vp (t + 1) +
        upsilon α φ εw * Vw (t + 1)) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap Dp Dw) := by
  have hβθp : β * θp < 1 := by nlinarith
  have hβθw : β * θw < 1 := by nlinarith
  have hLp := lemma2 (q := fun t => Dp t ^ 2) hθp0.le hθp1 hβ0 hβ1 hVp0 (fun _ => sq_nonneg _)
    hrecp hDp
  have hLw := lemma2 (q := fun t => Dw t ^ 2) hθw0.le hθw1 hβ0 hβ1 hVw0 (fun _ => sq_nonneg _)
    hrecw hDw
  have hA := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hLp.mul_left (εp / bigTheta α εp))).add (hLw.mul_left (upsilon α φ εw))).div_const 2
  have hB := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hDp.hasSum.mul_left (priceWeight β θp α εp))).add
    (hDw.hasSum.mul_left (wageWeight β θw α φ εw))).div_const 2
  have hW : welfareLoss β θp θw σ φ α εp εw ygap Dp Dw
      = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
        priceWeight β θp α εp * ∑' t, β ^ t * Dp t ^ 2 +
        wageWeight β θw α φ εw * ∑' t, β ^ t * Dw t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← priceWeight_of_dispersion hθp0 hθp1 hβθp hα,
    ← wageWeight_of_dispersion (α := α) hθw0 hθw1 hβθw hφε]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), p. 192 (**(28) with inherited dispersion**, survey error 8): with any
inherited `V^p_0, V^w_0 ≥ 0` the discounted dispersion form equals `𝕎` **plus** the
policy-independent constant `½[(ε_p/Θ) θ_p V^p_0/(1 − βθ_p) + Υ θ_w V^w_0/(1 − βθ_w)]`. -/
theorem welfare_eq_loss_inherited {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap Dp Dw Vp Vw : ℕ → ℝ} (hVp0 : 0 ≤ Vp 0) (hVw0 : 0 ≤ Vw 0)
    (hrecp : ∀ t, Vp (t + 1) = θp * Vp t + θp / (1 - θp) * Dp t ^ 2)
    (hrecw : ∀ t, Vw (t + 1) = θw * Vw t + θw / (1 - θw) * Dw t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hDp : Summable fun t => β ^ t * Dp t ^ 2)
    (hDw : Summable fun t => β ^ t * Dw t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + εp / bigTheta α εp * Vp (t + 1) +
        upsilon α φ εw * Vw (t + 1)) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap Dp Dw +
        (εp / bigTheta α εp * (θp * Vp 0 / (1 - β * θp)) +
          upsilon α φ εw * (θw * Vw 0 / (1 - β * θw))) / 2) := by
  have hβθp : β * θp < 1 := by nlinarith
  have hβθw : β * θw < 1 := by nlinarith
  have hLp := lemma2_inherited (q := fun t => Dp t ^ 2) hθp0.le hθp1 hβ0 hβ1 hVp0
    (fun _ => sq_nonneg _) hrecp hDp
  have hLw := lemma2_inherited (q := fun t => Dw t ^ 2) hθw0.le hθw1 hβ0 hβ1 hVw0
    (fun _ => sq_nonneg _) hrecw hDw
  have hA := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hLp.mul_left (εp / bigTheta α εp))).add (hLw.mul_left (upsilon α φ εw))).div_const 2
  have hB := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hDp.hasSum.mul_left (priceWeight β θp α εp))).add
    (hDw.hasSum.mul_left (wageWeight β θw α φ εw))).div_const 2
  have hW : welfareLoss β θp θw σ φ α εp εw ygap Dp Dw
      = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
        priceWeight β θp α εp * ∑' t, β ^ t * Dp t ^ 2 +
        wageWeight β θw α φ εw * ∑' t, β ^ t * Dw t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← priceWeight_of_dispersion hθp0 hθp1 hβθp hα,
    ← wageWeight_of_dispersion (α := α) hθw0 hθw1 hβθw hφε]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), pp. 179 and 192 (**(28) for the Calvo economy, exact in `Δm`**): along the
Calvo sequences of price and wage cross-sections (both following the Calvo mixture `wageMix`,
with `θ_p` and `θ_w`) with no inherited dispersion,
`½ ∑ βᵗ [Γ ỹ_t² + (ε_p/Θ) var_i p_t + Υ var_j w_t] = 𝕎(ỹ, Δm^p, Δm^w)`. -/
theorem welfare_eq_loss_calvo {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap : ℕ → ℝ} {νp νw : ℕ → Measure ℝ} {pstar wstar : ℕ → ℝ}
    (hνp : ∀ t, νp (t + 1) = wageMix θp (νp t) (pstar t))
    (hνw : ∀ t, νw (t + 1) = wageMix θw (νw t) (wstar t))
    (hgp : GoodDist (νp 0)) (hgw : GoodDist (νw 0))
    (hVp0 : crossVarDist (νp 0) = 0) (hVw0 : crossVarDist (νw 0) = 0)
    (hY : Summable fun t => β ^ t * ygap t ^ 2)
    (hDp : Summable fun t => β ^ t * (crossMean (νp (t + 1)) - crossMean (νp t)) ^ 2)
    (hDw : Summable fun t => β ^ t * (crossMean (νw (t + 1)) - crossMean (νw t)) ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 +
        εp / bigTheta α εp * crossVarDist (νp (t + 1)) +
        upsilon α φ εw * crossVarDist (νw (t + 1))) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap (fun t => crossMean (νp (t + 1)) - crossMean (νp t))
        fun t => crossMean (νw (t + 1)) - crossMean (νw t)) :=
  welfare_eq_loss (Vp := fun t => crossVarDist (νp t)) (Vw := fun t => crossVarDist (νw t))
    hθp0 hθp1 hθw0 hθw1 hβ0 hβ1 hα hφε hVp0 hVw0 (wage_var_recursion hθp0.le hθp1 hνp hgp)
    (wage_var_recursion hθw0.le hθw1 hνw hgw) hY hDp hDw

/-- Galí (2015), eq. (29), p. 179 (**from `𝕎` to `L`**): if the expected squared gap and
squared price and wage inflation equal stationary variances at every date, the discounted
expected loss is `L/(1 − β)`. -/
theorem welfare_stationary {β θp θw σ φ α εp εw varY varP varW : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {eY eP eW : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varP)
    (heW : ∀ t, eW t = varW) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * eY t + priceWeight β θp α εp * eP t +
        wageWeight β θw α φ εw * eW t) / 2))
      (avgLoss β θp θw σ φ α εp εw varY varP varW / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right
    (avgLoss β θp θw σ φ α εp εw varY varP varW)
  convert h using 1
  · funext t
    rw [heY, heP, heW, avgLoss]
  · rw [div_eq_inv_mul]

/-! ### Comparative statics of the wage-inflation weight (p. 179) -/

/-- Galí (2015), p. 179: the wage-inflation weight in closed form,
`ε_w(1 − α)/λ_w = ε_w(1 − α) θ_w (1 + ε_w φ)/((1 − θ_w)(1 − βθ_w))`. -/
theorem wageWeight_eq {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hφε : 1 + εw * φ ≠ 0) :
    wageWeight β θ α φ εw = εw * (1 - α) * θ * (1 + εw * φ) / ((1 - θ) * (1 - β * θ)) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  unfold wageWeight lambdaW
  field_simp

/-- Galí (2015), p. 179, claim (i): the wage-inflation weight is strictly **increasing in the
elasticity of substitution among labour types** `ε_w` (on `ε_w > 0`, for `φ ≥ 0`, `α < 1`). -/
theorem wageWeight_strictMonoOn_eps {β θ α φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hα1 : α < 1) (hφ : 0 ≤ φ) :
    StrictMonoOn (fun εw => wageWeight β θ α φ εw) (Set.Ioi 0) := by
  have hβθ : β * θ < 1 := by nlinarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hφa : 1 + a * φ ≠ 0 := by nlinarith
  have hφb : 1 + b * φ ≠ 0 := by nlinarith
  simp only
  rw [wageWeight_eq hθ0 hθ1 hβθ hφa, wageWeight_eq hθ0 hθ1 hβθ hφb]
  have hD : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hk : a * (1 + a * φ) < b * (1 + b * φ) := by
    have h0 : 0 < (b - a) * (1 + (a + b) * φ) := mul_pos (by linarith) (by nlinarith)
    nlinarith [h0]
  have hc : 0 < (1 - α) * θ := mul_pos (by linarith) hθ0
  nlinarith

/-- Galí (2015), p. 179, claim (ii): the wage-inflation weight is strictly **increasing in the
labour elasticity `1 − α`**, i.e. strictly decreasing in `α` (for `ε_w > 0`, `φ ≥ 0`). -/
theorem wageWeight_strictAnti_alpha {β θ φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hεw : 0 < εw) (hφ : 0 ≤ φ) :
    StrictAnti fun α => wageWeight β θ α φ εw := by
  have hβθ : β * θ < 1 := by nlinarith
  have hφε : 1 + εw * φ ≠ 0 := by nlinarith
  intro a b hab
  simp only
  rw [wageWeight_eq hθ0 hθ1 hβθ hφε, wageWeight_eq hθ0 hθ1 hβθ hφε]
  have hD : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hc : 0 < εw * θ * (1 + εw * φ) := mul_pos (mul_pos hεw hθ0) (by nlinarith)
  nlinarith

/-- Galí (2015), p. 179, claim (iii): the wage-inflation weight is strictly **increasing in
the degree of wage stickiness** `θ_w ∈ (0, 1)` (for `β ≤ 1`, `ε_w > 0`, `φ ≥ 0`, `α < 1`). -/
theorem wageWeight_strictMonoOn_theta {β α φ εw : ℝ} (hβ1 : β ≤ 1) (hα1 : α < 1)
    (hεw : 0 < εw) (hφ : 0 ≤ φ) :
    StrictMonoOn (fun θ => wageWeight β θ α φ εw) (Set.Ioo 0 1) := by
  have hφε : 1 + εw * φ ≠ 0 := by nlinarith
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hβa : β * a < 1 := by nlinarith
  have hβb : β * b < 1 := by nlinarith
  simp only
  rw [wageWeight_eq ha0 ha1 hβa hφε, wageWeight_eq hb0 hb1 hβb hφε]
  have hDa : 0 < (1 - a) * (1 - β * a) := mul_pos (by linarith) (by linarith)
  have hDb : 0 < (1 - b) * (1 - β * b) := mul_pos (by linarith) (by linarith)
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < εw * (1 - α) * (1 + εw * φ) :=
    mul_pos (mul_pos hεw (by linarith)) (by nlinarith)
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  have e1 : εw * (1 - α) * a * (1 + εw * φ) * ((1 - b) * (1 - β * b))
      = εw * (1 - α) * (1 + εw * φ) * (a * ((1 - b) * (1 - β * b))) := by ring
  have e2 : εw * (1 - α) * b * (1 + εw * φ) * ((1 - a) * (1 - β * a))
      = εw * (1 - α) * (1 + εw * φ) * (b * ((1 - a) * (1 - β * a))) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hkey hk

/-- Galí (2015), p. 179 ("θ_w … inversely related to λ_w"): `λ_w` is strictly decreasing in
`θ_w ∈ (0, 1)` (for `β ≤ 1`, `ε_w φ > −1`). -/
theorem lambdaW_strictAntiOn_theta {β φ εw : ℝ} (hβ1 : β ≤ 1) (hφε : 0 < 1 + εw * φ) :
    StrictAntiOn (fun θ => lambdaW β θ φ εw) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  simp only [lambdaW]
  rw [div_lt_div_iff₀ (mul_pos hb0 hφε) (mul_pos ha0 hφε)]
  have hab1 : a * b < 1 := by nlinarith
  have hβab : β * (a * b) ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.2 hβ1) (mul_pos ha0 hb0).le]
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  have e1 : (1 - b) * (1 - β * b) * (a * (1 + εw * φ))
      = (1 + εw * φ) * (a * ((1 - b) * (1 - β * b))) := by ring
  have e2 : (1 - a) * (1 - β * a) * (b * (1 + εw * φ))
      = (1 + εw * φ) * (b * ((1 - a) * (1 - β * a))) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hkey hφε

/-- Galí (2015), p. 179: the wage-inflation weight is positive for `θ_w ∈ (0, 1)`, `β ≤ 1`,
`ε_w > 0`, `φ ≥ 0`, `α < 1`. -/
theorem wageWeight_pos {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hα1 : α < 1) (hεw : 0 < εw) (hφ : 0 ≤ φ) : 0 < wageWeight β θ α φ εw := by
  have hβθ : β * θ < 1 := by nlinarith
  have hφε : 0 < 1 + εw * φ := by nlinarith
  rw [wageWeight_eq hθ0 hθ1 hβθ hφε.ne']
  exact div_pos (mul_pos (mul_pos (mul_pos hεw (by linarith)) hθ0) hφε)
    (mul_pos (by linarith) (by linarith))

end Gali.StickyWagesPrices.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Limiting cases: flexible wages, flexible prices, and strict targeting

Galí (2015), Chapter 6, §6.3, p. 180.

## Flexible wages (the limiting model, survey error 7)

With flexible wages the wage markup is constant, so the real-wage gap equals the MRS gap,
`ω̃ = σ ỹ + φ ñ = (σ + φ/(1−α)) ỹ` (`flexWage_realWageGap`), and (18) becomes the Chapter 3
NKPC `π^p = β E π^p' + κ_p ỹ` with `κ_p = λ_p (σ + (φ+α)/(1−α))` (`flexWage_nkpc`). This is
stated for the **limiting model** (constant wage markup), not as a limit of (28): with
`θ_w = 0` the Calvo wage recursion leaves no wage dispersion at all
(`flexWage_no_wage_dispersion`), so the wage term of the welfare loss is absent; separately
`lambdaW_tendsto_atTop` (`λ_w → ∞` as `θ_w → 0⁺`) and `wageWeight_tendsto_zero` (the weight
`ε_w(1−α)/λ_w → 0`) give the book's limit statement. In that model `π^p = ỹ = 0` is feasible
and optimal (`flexWage_optimal`), strict price-inflation targeting forces `ỹ = 0`
(`flexWage_strictPrice_forces_zero_gap`), and under perfect foresight the optimum is unique
(`nk_zero_unique_pf`).

## Flexible prices

Symmetrically `ω̃ = −(α/(1−α)) ỹ` (`flexPrice_realWageGap`), (20) becomes
`π^w = β E π^w' + λ_w (σ + (φ+α)/(1−α)) ỹ` (`flexPrice_nkpc`), and `π^w = ỹ = 0` is optimal
(`flexPrice_optimal`); `lambdaP_tendsto_atTop`, `priceWeight_tendsto_zero`.

## Strict targeting is suboptimal with both rigidities

In the perfect-foresight model (18), (20), (21) with `ω̃_{−1} = 0` and loss (28):
* `strict_price_targeting_suboptimal`: there is a technology-shock path `Δωⁿ` (nonzero only
  at `t = 0, 1`) for which a path with `π^p ≡ 0` exists, it is **unique** among paths with
  `∑ βᵗ ỹ_t² < ∞`, and it has **strictly higher loss** than another feasible path.
* `strict_wage_targeting_suboptimal`: the same for `π^w ≡ 0`.
* `strict_price_targeting_suboptimal_model`, `strict_wage_targeting_suboptimal_model`: the
  same with the model's coefficients `κ_p = αλ_p/(1−α)`, `κ_w = λ_w(σ + φ/(1−α))` and weights
  `σ + (φ+α)/(1−α)`, `ε_p/λ_p`, `ε_w(1−α)/λ_w`, for all `θ_p, θ_w ∈ (0, 1)`.

The improving direction is an explicit two-period feasible perturbation (`dirY`, `dirP`, `dirW`,
`dirOm`); uniqueness of the strict-targeting path uses the exponential growth of the homogeneous
real-wage-gap dynamics (`growth`).
-/

namespace Gali.StickyWagesPrices.LimitingCases

open Filter Topology
open Gali.StickyWagesPrices.Welfare Gali.StickyWagesPrices.WageDispersion

/-! ### The gap equations under a general expectation system -/

/-- Galí (2015), eq. (18), p. 172: the price NKPC in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PricePC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κp lamP : ℝ) (y pp om : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • y t + lamP • om t

/-- Galí (2015), eq. (20), p. 172: the wage NKPC in gaps,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WagePC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κw lamW : ℝ) (y pw om : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • y t - lamW • om t

/-- Galí (2015), p. 180 (and ch. 3): a New Keynesian Phillips curve
`x_t = β E_t x_{t+1} + κ ỹ_t`. -/
def NKPC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ : ℝ) (y x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = β • 𝔼.E t (x (t + 1)) + κ • y t

/-- Galí (2015), eq. (18), p. 172: `κ_p = α λ_p/(1 − α)`. -/
noncomputable def kappaP (α lamP : ℝ) : ℝ := α * lamP / (1 - α)

/-- Galí (2015), eq. (20), p. 172: `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def kappaW (σ φ α lamW : ℝ) : ℝ := lamW * (σ + φ / (1 - α))

/-- Galí (2015), p. 180: `κ_p + λ_p (σ + φ/(1−α)) = λ_p (σ + (φ+α)/(1−α))`. -/
theorem kappaP_add {σ φ α lamP : ℝ} (hα : α ≠ 1) :
    kappaP α lamP + lamP * (σ + φ / (1 - α)) = lamP * gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold kappaP gapCoeff
  field_simp
  ring

/-- Galí (2015), p. 180: `κ_w + λ_w α/(1−α) = λ_w (σ + (φ+α)/(1−α))`. -/
theorem kappaW_add {σ φ α lamW : ℝ} (hα : α ≠ 1) :
    kappaW σ φ α lamW + lamW * (α / (1 - α)) = lamW * gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold kappaW gapCoeff
  field_simp
  ring

/-! ### Flexible wages (pp. 180) -/

/-- Galí (2015), p. 180: with a constant wage markup the real-wage gap equals the MRS gap,
`ω̃ = σ ỹ + φ ñ`; with `(1 − α) ñ = ỹ` (first-order employment gap) this is
`ω̃ = (σ + φ/(1−α)) ỹ`. -/
theorem flexWage_realWageGap {σ φ α y n om : ℝ} (hα : α ≠ 1) (hom : om = σ * y + φ * n)
    (hn : (1 - α) * n = y) : om = (σ + φ / (1 - α)) * y := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = y / (1 - α) := by
    field_simp
    linarith
  rw [hom, hn']
  ring

/-- Galí (2015), p. 180 (**flexible wages**): if (18) holds and the wage markup is constant,
`ω̃_t = (σ + φ/(1−α)) ỹ_t`, then price inflation follows the Chapter 3 NKPC
`π^p_t = β E_t π^p_{t+1} + λ_p (σ + (φ+α)/(1−α)) ỹ_t`, for any expectation system. -/
theorem flexWage_nkpc {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamP : ℝ} (hα : α ≠ 1)
    {y pp om : ℕ → Ω → ℝ} (hP : PricePC 𝔼 β (kappaP α lamP) lamP y pp om)
    (hom : ∀ t, om t = (σ + φ / (1 - α)) • y t) :
    NKPC 𝔼 β (lamP * gapCoeff σ φ α) y pp := by
  intro t
  rw [hP t, hom t, smul_smul, ← kappaP_add (σ := σ) (φ := φ) (lamP := lamP) hα]
  ext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 180 (survey error 7): in the limiting flexible-wage model (`θ_w = 0`) the
Calvo wage cross-section has no dispersion: the recursion
`V_{t+1} = θ_w V_t + (θ_w/(1−θ_w)) (π^w_t)²` gives `V_{t+1} = 0`, so the wage term of the
welfare loss is exactly absent (rather than being the `λ_w → ∞` limit of (28)). -/
theorem flexWage_no_wage_dispersion {V q : ℕ → ℝ}
    (hrec : ∀ t, V (t + 1) = 0 * V t + 0 / (1 - 0) * q t) : ∀ t, V (t + 1) = 0 := by
  intro t
  rw [hrec t]
  ring

/-- Galí (2015), p. 180: **`λ_w → +∞` as `θ_w → 0⁺`** (for `1 + ε_w φ > 0`). -/
theorem lambdaW_tendsto_atTop {β φ εw : ℝ} (hφε : 0 < 1 + εw * φ) :
    Tendsto (fun θ => lambdaW β θ φ εw) (𝓝[>] 0) atTop := by
  have heq : (fun θ => lambdaW β θ φ εw)
      = fun θ => (1 - θ) * (1 - β * θ) / (1 + εw * φ) * θ⁻¹ := by
    funext θ
    simp only [lambdaW, div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  have hc : Continuous fun θ : ℝ => (1 - θ) * (1 - β * θ) / (1 + εw * φ) := by fun_prop
  have hf : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ) / (1 + εw * φ)) (𝓝[>] 0)
      (𝓝 (1 / (1 + εw * φ))) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact hf.pos_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero

/-- Galí (2015), p. 180: **`λ_p → +∞` as `θ_p → 0⁺`** (for `0 ≤ α < 1`, `ε_p > 0`). -/
theorem lambdaP_tendsto_atTop {β α εp : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) :
    Tendsto (fun θ => lambdaP β θ α εp) (𝓝[>] 0) atTop := by
  have hΘ : 0 < bigTheta α εp := div_pos (by linarith) (by nlinarith)
  have heq : (fun θ => lambdaP β θ α εp)
      = fun θ => (1 - θ) * (1 - β * θ) * bigTheta α εp * θ⁻¹ := by
    funext θ
    simp only [lambdaP, div_eq_mul_inv]
    ring
  rw [heq]
  have hc : Continuous fun θ : ℝ => (1 - θ) * (1 - β * θ) * bigTheta α εp := by fun_prop
  have hf : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ) * bigTheta α εp) (𝓝[>] 0)
      (𝓝 (bigTheta α εp)) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact hf.pos_mul_atTop hΘ tendsto_inv_nhdsGT_zero

/-- Galí (2015), p. 180: as `θ_w → 0⁺` the wage-inflation weight `ε_w(1−α)/λ_w → 0` ("wage
inflation is no longer costly"). -/
theorem wageWeight_tendsto_zero {β α φ εw : ℝ} (hφε : 0 < 1 + εw * φ) :
    Tendsto (fun θ => wageWeight β θ α φ εw) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.div_atTop (lambdaW_tendsto_atTop hφε)

/-- Galí (2015), p. 180: as `θ_p → 0⁺` the price-inflation weight `ε_p/λ_p → 0`. -/
theorem priceWeight_tendsto_zero {β α εp : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) :
    Tendsto (fun θ => priceWeight β θ α εp) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.div_atTop (lambdaP_tendsto_atTop hα0 hα1 hεp)

/-! ### Flexible prices (p. 180) -/

/-- Galí (2015), p. 180: with a constant price markup the real-wage gap equals the gap in the
marginal product of labour, `ω̃ = ỹ − ñ`; with `(1 − α) ñ = ỹ` this is `ω̃ = −(α/(1−α)) ỹ`. -/
theorem flexPrice_realWageGap {α y n om : ℝ} (hα : α ≠ 1) (hom : om = y - n)
    (hn : (1 - α) * n = y) : om = -(α / (1 - α)) * y := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = y / (1 - α) := by
    field_simp
    linarith
  rw [hom, hn']
  field_simp
  ring

/-- Galí (2015), p. 180 (**flexible prices**): if (20) holds and the price markup is constant,
`ω̃_t = −(α/(1−α)) ỹ_t`, then `π^w_t = β E_t π^w_{t+1} + λ_w (σ + (φ+α)/(1−α)) ỹ_t`. (The book
calls this slope `κ_w`, which clashes with the `κ_w = λ_w(σ + φ/(1−α))` of (20).) -/
theorem flexPrice_nkpc {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamW : ℝ} (hα : α ≠ 1)
    {y pw om : ℕ → Ω → ℝ} (hW : WagePC 𝔼 β (kappaW σ φ α lamW) lamW y pw om)
    (hom : ∀ t, om t = (-(α / (1 - α))) • y t) :
    NKPC 𝔼 β (lamW * gapCoeff σ φ α) y pw := by
  intro t
  rw [hW t, hom t, smul_smul, ← kappaW_add (σ := σ) (φ := φ) (lamW := lamW) hα]
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The optimum in the one-rigidity models -/

/-- Galí (2015), pp. 179–180: the welfare loss of a one-rigidity model,
`E_0 ½ ∑ βᵗ [Θ_y ỹ_t² + c x_t²]` (`x = π^p`, `c = ε_p/λ_p` with flexible wages;
`x = π^w`, `c = ε_w(1−α)/λ_w` with flexible prices). -/
noncomputable def nkLoss {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β Θy c : ℝ)
    (y x : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => (Θy * y t ω' ^ 2 + c * x t ω' ^ 2) / 2) ω

/-- Galí (2015), p. 180: the loss is nonnegative (`β, Θ_y, c ≥ 0`). -/
theorem nkLoss_nonneg {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Θy c : ℝ} (hβ : 0 ≤ β)
    (hΘ : 0 ≤ Θy) (hc : 0 ≤ c) (y x : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ nkLoss 𝔼 β Θy c y x ω := by
  refine tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ t) ?_
  have hle : (0 : Ω → ℝ) ≤ fun ω' => (Θy * y t ω' ^ 2 + c * x t ω' ^ 2) / 2 := fun ω' => by
    have := mul_nonneg hΘ (sq_nonneg (y t ω'))
    have := mul_nonneg hc (sq_nonneg (x t ω'))
    simp only [Pi.zero_apply]
    linarith
  have := 𝔼.mono 0 hle ω
  rwa [map_zero] at this

/-- Galí (2015), p. 180: the zero path `ỹ = x = 0` has zero loss. -/
theorem nkLoss_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β Θy c : ℝ) (ω : Ω) :
    nkLoss 𝔼 β Θy c (fun _ _ => 0) (fun _ _ => 0) ω = 0 := by
  have h : (fun _ : Ω => (Θy * (0 : ℝ) ^ 2 + c * (0 : ℝ) ^ 2) / 2) = 0 := by
    funext ω'
    simp
  simp only [nkLoss, h, map_zero, Pi.zero_apply, mul_zero, tsum_zero]

/-- Galí (2015), p. 180: the zero path satisfies any NKPC. -/
theorem nkpc_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ : ℝ) :
    NKPC 𝔼 β κ (fun _ _ => 0) (fun _ _ => 0) := by
  intro t
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-- Galí (2015), p. 180 (**the optimum with one rigidity**): `x = ỹ = 0` satisfies the NKPC
and attains the lower bound zero of the loss, so it is optimal among all paths. -/
theorem nk_zero_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Θy c : ℝ} (hβ : 0 ≤ β)
    (hΘ : 0 ≤ Θy) (hc : 0 ≤ c) (κ : ℝ) :
    NKPC 𝔼 β κ (fun _ _ => 0) (fun _ _ => 0) ∧
      ∀ (y x : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β Θy c (fun _ _ => 0) (fun _ _ => 0) ω ≤ nkLoss 𝔼 β Θy c y x ω :=
  ⟨nkpc_zero 𝔼 β κ, fun y x ω => by
    rw [nkLoss_zero]
    exact nkLoss_nonneg 𝔼 hβ hΘ hc y x ω⟩

/-- Galí (2015), p. 180 (**uniqueness of the optimum, perfect foresight**): with `β, Θ_y, c > 0`
and a summable loss, zero loss forces `ỹ_t = x_t = 0` at every date. -/
theorem nk_zero_unique_pf {β Θy c : ℝ} (hβ : 0 < β) (hΘ : 0 < Θy) (hc : 0 < c)
    {y x : ℕ → Unit → ℝ}
    (hs : Summable fun t => β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2))
    (h0 : nkLoss perfectForesight β Θy c y x () = 0) : ∀ t, y t () = 0 ∧ x t () = 0 := by
  have hpf : nkLoss perfectForesight β Θy c y x ()
      = ∑' t, β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) := rfl
  rw [hpf] at h0
  have hnn : ∀ t, 0 ≤ β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) := fun t =>
    mul_nonneg (pow_nonneg hβ.le t) (by positivity)
  intro t
  have hle := hs.le_tsum t (fun j _ => hnn j)
  rw [h0] at hle
  have ht : β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) = 0 := le_antisymm hle (hnn t)
  have hβt : 0 < β ^ t := pow_pos hβ t
  have hq : Θy * y t () ^ 2 + c * x t () ^ 2 = 0 := by
    rcases mul_eq_zero.1 ht with h | h
    · exact absurd h hβt.ne'
    · linarith
  have h1 : Θy * y t () ^ 2 = 0 := by
    have := mul_nonneg hΘ.le (sq_nonneg (y t ()))
    have := mul_nonneg hc.le (sq_nonneg (x t ()))
    linarith
  have h2 : c * x t () ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h1).resolve_left hΘ.ne'),
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h2).resolve_left hc.ne')⟩

/-- Galí (2015), p. 180 (**flexible wages: the optimum**): in the limiting flexible-wage model,
the path `π^p = ỹ = ω̃ = 0` satisfies (18) and the constant-wage-markup condition, and attains
zero loss `E_0 ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)²]`, the lower bound for every
path. -/
theorem flexWage_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamP εp : ℝ}
    (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 < lamP)
    (hεp : 0 ≤ εp) :
    PricePC 𝔼 β (kappaP α lamP) lamP (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ t, (fun _ _ => 0 : ℕ → Ω → ℝ) t = (σ + φ / (1 - α)) • (fun _ _ => 0 : ℕ → Ω → ℝ) t) ∧
      ∀ (y pp : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β (gapCoeff σ φ α) (εp / lamP) (fun _ _ => 0) (fun _ _ => 0) ω
          ≤ nkLoss 𝔼 β (gapCoeff σ φ α) (εp / lamP) y pp ω := by
  have hΘ : 0 ≤ gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) (by linarith : (0 : ℝ) ≤ 1 - α)
    linarith
  refine ⟨fun t => ?_, fun t => by ext; simp, (nk_zero_optimal 𝔼 hβ hΘ
    (div_nonneg hεp hlamP.le) 0).2⟩
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-- Galí (2015), p. 180: in the flexible-wage model, **strict price-inflation targeting forces a
zero output gap**: if `π^p ≡ 0` satisfies the NKPC with slope `κ ≠ 0` then `ỹ ≡ 0`; together
with `flexWage_optimal`, strict price-inflation targeting is optimal when wages are flexible. -/
theorem flexWage_strictPrice_forces_zero_gap {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ : ℝ}
    (hκ : κ ≠ 0) {y : ℕ → Ω → ℝ} (h : NKPC 𝔼 β κ y (fun _ _ => 0)) : ∀ t, y t = 0 := by
  intro t
  have ht := h t
  have h0 : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h0, map_zero, smul_zero, zero_add] at ht
  have := congrArg (fun f => κ⁻¹ • f) ht
  simp only [smul_zero, smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  exact this.symm

/-- Galí (2015), p. 180 (**flexible prices: the optimum**): in the limiting flexible-price model
the path `π^w = ỹ = ω̃ = 0` satisfies (20) and the constant-price-markup condition and attains
zero loss `E_0 ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
theorem flexPrice_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamW εw : ℝ}
    (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamW : 0 < lamW)
    (hεw : 0 ≤ εw) :
    WagePC 𝔼 β (kappaW σ φ α lamW) lamW (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ t, (fun _ _ => 0 : ℕ → Ω → ℝ) t = (-(α / (1 - α))) • (fun _ _ => 0 : ℕ → Ω → ℝ) t) ∧
      ∀ (y pw : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β (gapCoeff σ φ α) (εw * (1 - α) / lamW) (fun _ _ => 0) (fun _ _ => 0) ω
          ≤ nkLoss 𝔼 β (gapCoeff σ φ α) (εw * (1 - α) / lamW) y pw ω := by
  have hΘ : 0 ≤ gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) (by linarith : (0 : ℝ) ≤ 1 - α)
    linarith
  refine ⟨fun t => ?_, fun t => by ext; simp, (nk_zero_optimal 𝔼 hβ hΘ
    (div_nonneg (mul_nonneg hεw (by linarith)) hlamW.le) 0).2⟩
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-! ### Strict targeting with sticky wages and prices (perfect foresight) -/

/-- Galí (2015), eqs. (18), (20), (21), pp. 172–173, under perfect foresight with
`ω̃_{−1} = 0`: a path `(ỹ, π^p, π^w, ω̃)` is feasible given the natural-real-wage changes
`Δωⁿ` (`dn`). -/
def Feasible (β κp κw lamP lamW : ℝ) (dn y pp pw om : ℕ → ℝ) : Prop :=
  (∀ t, pp t = β * pp (t + 1) + κp * y t + lamP * om t) ∧
    (∀ t, pw t = β * pw (t + 1) + κw * y t - lamW * om t) ∧
    om 0 = pw 0 - pp 0 - dn 0 ∧ ∀ t, om (t + 1) = om t + pw (t + 1) - pp (t + 1) - dn (t + 1)

/-- Galí (2015), eq. (28), p. 179, perfect foresight: the welfare loss
`½ ∑ βᵗ [Θ_y ỹ_t² + c_p (π^p_t)² + c_w (π^w_t)²]`. -/
noncomputable def loss (β Θy cp cw : ℝ) (y pp pw : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * ((Θy * y t ^ 2 + cp * pp t ^ 2 + cw * pw t ^ 2) / 2)

/-- Galí (2015), p. 180: the improving direction, output-gap component
`(1 + β + λ_p + λ_w, −1, 0, 0, …)`. -/
def dirY (β lamP lamW : ℝ) : ℕ → ℝ
  | 0 => 1 + β + (lamP + lamW)
  | 1 => -1
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, price-inflation component
`(κ_p + M, −κ_p, 0, …)`, `M = κ_p λ_w + λ_p κ_w`. -/
def dirP (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => κp + (κp * lamW + lamP * κw)
  | 1 => -κp
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, wage-inflation component
`(κ_w + M, −κ_w, 0, …)`. -/
def dirW (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => κw + (κp * lamW + lamP * κw)
  | 1 => -κw
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, real-wage-gap component
`(κ_w − κ_p, 0, 0, …)`. -/
def dirOm (κp κw : ℝ) : ℕ → ℝ
  | 0 => κw - κp
  | _ + 1 => 0

/-- Galí (2015), p. 180: the two-period direction is feasible for the homogeneous system
(`Δωⁿ ≡ 0`, `ω̃_{−1} = 0`). -/
theorem feasible_dir (β κp κw lamP lamW : ℝ) :
    Feasible β κp κw lamP lamW (fun _ => 0) (dirY β lamP lamW) (dirP κp κw lamP lamW)
      (dirW κp κw lamP lamW)
      (dirOm κp κw) := by
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [dirP, dirY, dirOm]; ring
    | 1 => simp only [dirP, dirY, dirOm]; ring
    | n + 2 => simp only [dirP, dirY, dirOm]; ring
  · match t with
    | 0 => simp only [dirW, dirY, dirOm]; ring
    | 1 => simp only [dirW, dirY, dirOm]; ring
    | n + 2 => simp only [dirW, dirY, dirOm]; ring
  · simp only [dirW, dirP, dirOm]
    ring
  · match t with
    | 0 => simp only [dirW, dirP, dirOm]; ring
    | n + 1 => simp only [dirW, dirP, dirOm]; ring

/-- Galí (2015), p. 180: feasibility is preserved by adding a multiple of a homogeneous
feasible direction. -/
theorem feasible_add {β κp κw lamP lamW : ℝ} {dn y pp pw om hy hp hw ho : ℕ → ℝ} (τ : ℝ)
    (hx : Feasible β κp κw lamP lamW dn y pp pw om)
    (hh : Feasible β κp κw lamP lamW (fun _ => 0) hy hp hw ho) :
    Feasible β κp κw lamP lamW dn (fun t => y t + τ * hy t) (fun t => pp t + τ * hp t)
      (fun t => pw t + τ * hw t) (fun t => om t + τ * ho t) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨g1, g2, g3, g4⟩ := hh
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · linear_combination h1 t + τ * g1 t
  · linear_combination h2 t + τ * g2 t
  · beta_reduce at g3
    linear_combination h3 + τ * g3
  · beta_reduce at g4
    linear_combination h4 t + τ * g4 t

/-- Galí (2015), p. 180: the loss of a path that vanishes from `t = 2` on is a finite sum. -/
theorem loss_two {β Θy cp cw : ℝ} {y pp pw : ℕ → ℝ} (hy : ∀ t, y (t + 2) = 0)
    (hp : ∀ t, pp (t + 2) = 0) (hw : ∀ t, pw (t + 2) = 0) :
    loss β Θy cp cw y pp pw = (Θy * y 0 ^ 2 + cp * pp 0 ^ 2 + cw * pw 0 ^ 2) / 2 +
      β * ((Θy * y 1 ^ 2 + cp * pp 1 ^ 2 + cw * pw 1 ^ 2) / 2) := by
  rw [loss, tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro t ht
    have h2 : 2 ≤ t := by
      simp only [Finset.mem_range, not_lt] at ht
      exact ht
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h2
    simp [hy n, hp n, hw n]

/-- Galí (2015), p. 180 (elementary): for `B ≠ 0`, `Q ≥ 0` and `τ = −B/(Q + 1)`,
`τ B + τ² Q < 0`, so a quadratic loss can be lowered along any direction with nonzero slope. -/
theorem quad_improve {B Q : ℝ} (hB : B ≠ 0) (hQ : 0 ≤ Q) :
    (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q < 0 := by
  have hQ1 : 0 < Q + 1 := by linarith
  have hB2 : 0 < B ^ 2 := by positivity
  have e : (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q = -(B ^ 2 / (Q + 1) ^ 2) := by
    field_simp
    ring
  rw [e]
  exact neg_lt_zero.2 (by positivity)

/-- Galí (2015), p. 180 (the growth argument behind uniqueness): if `δ_0 = D_0 > 0`,
`D_{t+1} = D_t + δ_{t+1}` and `β δ_{t+1} = δ_t + m D_t` with `0 < β ≤ 1`, `m ≥ 0`, then
`δ_t ≥ 0`, `D_0 ≤ βᵗ δ_t` and `δ_t ≤ D_t` for all `t` (the real-wage gap explodes
geometrically). -/
theorem growth {β m : ℝ} (hβ0 : 0 < β) (hm : 0 ≤ m) {D δ : ℕ → ℝ} (h0 : δ 0 = D 0)
    (hD : ∀ t, D (t + 1) = D t + δ (t + 1)) (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t)
    (hc : 0 < D 0) : ∀ t, 0 ≤ δ t ∧ D 0 ≤ β ^ t * δ t ∧ δ t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨by linarith, by simp [h0], by linarith⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have hDt : 0 ≤ D t := le_trans i1 i3
    have hstep : δ t ≤ β * δ (t + 1) := by rw [hδ t]; nlinarith
    have hpos : 0 ≤ δ (t + 1) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    refine ⟨hpos, ?_, ?_⟩
    · calc D 0 ≤ β ^ t * δ t := i2
        _ ≤ β ^ t * (β * δ (t + 1)) := mul_le_mul_of_nonneg_left hstep (pow_nonneg hβ0.le t)
        _ = β ^ (t + 1) * δ (t + 1) := by ring
    · rw [hD t]
      linarith

/-- Galí (2015), p. 180: in the setting of `growth`, `D_0 = 0` forces `D ≡ δ ≡ 0`. -/
theorem zero_of_growth {β m : ℝ} (hβ0 : 0 < β) {D δ : ℕ → ℝ} (h0 : δ 0 = D 0)
    (hD : ∀ t, D (t + 1) = D t + δ (t + 1)) (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t)
    (hc : D 0 = 0) : ∀ t, D t = 0 ∧ δ t = 0 := by
  intro t
  induction t with
  | zero => exact ⟨hc, by rw [h0, hc]⟩
  | succ t ih =>
    have h1 : β * δ (t + 1) = 0 := by rw [hδ t, ih.1, ih.2]; ring
    have h2 : δ (t + 1) = 0 := (mul_eq_zero.1 h1).resolve_left hβ0.ne'
    exact ⟨by rw [hD t, ih.1, h2]; ring, h2⟩

/-- Galí (2015), p. 180: in the setting of `growth` with `β ≤ 1` and any `D_0`,
`D_0² ≤ βᵗ D_t²` for every `t`. -/
theorem sq_le_of_growth {β m : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hm : 0 ≤ m) {D δ : ℕ → ℝ}
    (h0 : δ 0 = D 0) (hD : ∀ t, D (t + 1) = D t + δ (t + 1))
    (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t) : ∀ t, D 0 ^ 2 ≤ β ^ t * D t ^ 2 := by
  have key : ∀ {D δ : ℕ → ℝ}, δ 0 = D 0 → (∀ t, D (t + 1) = D t + δ (t + 1)) →
      (∀ t, β * δ (t + 1) = δ t + m * D t) → 0 < D 0 → ∀ t, D 0 ^ 2 ≤ β ^ t * D t ^ 2 := by
    intro D δ h0 hD hδ hc t
    obtain ⟨i1, i2, i3⟩ := growth hβ0 hm h0 hD hδ hc t
    have hbt : 0 < β ^ t := pow_pos hβ0 t
    have hbt1 : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have hDt : 0 ≤ D t := le_trans i1 i3
    have h1 : D 0 ≤ β ^ t * D t := le_trans i2 (mul_le_mul_of_nonneg_left i3 hbt.le)
    have h2 : β ^ t * D t ≤ D t := by nlinarith
    nlinarith
  intro t
  rcases lt_trichotomy (D 0) 0 with hneg | hzero | hpos
  · have := key (D := fun t => -D t) (δ := fun t => -δ t) (by rw [h0])
      (fun t => by rw [hD t]; ring)
      (fun t => by linear_combination (-1 : ℝ) * hδ t)
      (by linarith) t
    simpa using this
  · calc D 0 ^ 2 = 0 := by rw [hzero]; ring
      _ ≤ β ^ t * D t ^ 2 := by positivity
  · exact key h0 hD hδ hpos t

/-- Galí (2015), p. 180: a sequence whose discounted squares are summable cannot stay above a
positive bound from `t = 1` on. -/
theorem not_summable_of_ge {f : ℕ → ℝ} {k : ℝ} (hk : 0 < k) (hf : ∀ t, k ≤ f (t + 1))
    (hs : Summable f) : False := by
  have h := ((summable_nat_add_iff 1).2 hs).tendsto_atTop_zero
  obtain ⟨t, ht⟩ := (h.eventually (gt_mem_nhds hk)).exists
  linarith [hf t]

/-- Galí (2015), p. 180: `M = κ_p λ_w + λ_p κ_w`, the coefficient of the strict-targeting paths. -/
noncomputable def bigM (κp κw lamP lamW : ℝ) : ℝ := κp * lamW + lamP * κw

/-- Galí (2015), p. 180: the technology-shock path (changes in the natural real wage) used for
strict price-inflation targeting: `Δωⁿ = ((M + κ_p)/λ_p, −κ_p/λ_p, 0, …)`. -/
noncomputable def priceShock (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => (bigM κp κw lamP lamW + κp) / lamP
  | 1 => -κp / lamP
  | _ + 2 => 0

/-- Galí (2015), p. 180: the strict price-inflation-targeting path for `priceShock`: output gap
`(1, 0, …)`. -/
def spY : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict price-targeting path, wage inflation `(M/λ_p, 0, …)`. -/
noncomputable def spW (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => bigM κp κw lamP lamW / lamP
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict price-targeting path, real-wage gap `(−κ_p/λ_p, 0, …)`. -/
noncomputable def spOm (κp lamP : ℝ) : ℕ → ℝ
  | 0 => -κp / lamP
  | _ + 1 => 0

/-- Galí (2015), p. 180: `π^p ≡ 0`, `ỹ = spY`, `π^w = spW`, `ω̃ = spOm` is feasible for the
technology shock `priceShock`. -/
theorem feasible_sp {β κp κw lamP lamW : ℝ} (hlamP : 0 < lamP) :
    Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) spY (fun _ => 0) (spW κp κw lamP lamW)
      (spOm κp lamP) := by
  have hl : lamP ≠ 0 := hlamP.ne'
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [spY, spOm]; field_simp; ring
    | n + 1 => simp only [spY, spOm]; ring
  · match t with
    | 0 => simp only [spY, spOm, spW, bigM]; field_simp; ring
    | n + 1 => simp only [spY, spOm, spW]; ring
  · simp only [spOm, spW, priceShock, bigM]
    field_simp
    ring
  · match t with
    | 0 => simp only [spOm, spW, priceShock]; ring
    | n + 1 => simp only [spOm, spW, priceShock]; ring

/-- Galí (2015), p. 180 (**uniqueness of the strict price-targeting path**): with
`0 < β ≤ 1`, `κ_p ≥ 0`, `λ_p, λ_w > 0`, every feasible path for `priceShock` with `π^p ≡ 0` and
`∑ βᵗ ỹ_t² < ∞` is the explicit path `(spY, 0, spW, spOm)` (`κ_w > 0`). -/
theorem sp_unique {β κp κw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hκp : 0 ≤ κp)
    (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hκw : 0 < κw) {y pw om : ℕ → ℝ}
    (hF : Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y (fun _ => 0) pw om)
    (hs : Summable fun t => β ^ t * y t ^ 2) :
    y = spY ∧ pw = spW κp κw lamP lamW ∧ om = spOm κp lamP := by
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := feasible_sp (β := β) (κp := κp) (κw := κw) (lamW := lamW) hlamP
  set D : ℕ → ℝ := fun t => om t - spOm κp lamP t with hDdef
  set δ : ℕ → ℝ := fun t => pw t - spW κp κw lamP lamW t with hδdef
  set dY : ℕ → ℝ := fun t => y t - spY t with hdYdef
  have e18 : ∀ t, κp * dY t + lamP * D t = 0 := fun t => by
    have a := f1 t
    have b := g1 t
    simp only [hDdef, hdYdef]
    linarith
  have e0 : δ 0 = D 0 := by
    simp only [hDdef, hδdef]
    linarith
  have eD : ∀ t, D (t + 1) = D t + δ (t + 1) := fun t => by
    have a := f4 t
    have b := g4 t
    simp only [hDdef, hδdef]
    linarith
  have e20 : ∀ t, δ t = β * δ (t + 1) + κw * dY t - lamW * D t := fun t => by
    have a := f2 t
    have b := g2 t
    simp only [hDdef, hδdef, hdYdef]
    linarith
  -- the output-gap difference is summable in the discounted-square sense from `t = 1` on
  have hsY : ∀ t, β ^ (t + 1) * dY (t + 1) ^ 2 = β ^ (t + 1) * y (t + 1) ^ 2 := fun t => by
    simp [hdYdef, spY]
  have hzero : D = 0 ∧ δ = 0 ∧ dY = 0 := by
    rcases hκp.lt_or_eq with hκpos | hκ0
    · -- `κ_p > 0`: `ỹ` is proportional to `ω̃`, and the homogeneous dynamics explode
      set m := κw * lamP / κp + lamW with hm
      have hm0 : 0 ≤ m := by positivity
      have hdY : ∀ t, dY t = -(lamP / κp) * D t := fun t => by
        have := e18 t
        field_simp
        linarith
      have eδ : ∀ t, β * δ (t + 1) = δ t + m * D t := fun t => by
        have := e20 t
        rw [hdY t] at this
        rw [hm]
        field_simp at this ⊢
        linarith
      rcases eq_or_ne (D 0) 0 with hD0 | hD0
      · have hz := zero_of_growth hβ0 e0 eD eδ hD0
        refine ⟨funext fun t => (hz t).1, funext fun t => (hz t).2, funext fun t => ?_⟩
        rw [hdY t, (hz t).1]
        simp
      · exfalso
        have hsq := sq_le_of_growth hβ0 hβ1 hm0 e0 eD eδ
        have hk : 0 < (lamP / κp) ^ 2 * D 0 ^ 2 := by positivity
        refine not_summable_of_ge hk (fun t => ?_) hs
        have h1 := hsq (t + 1)
        have h2 : β ^ (t + 1) * y (t + 1) ^ 2
            = (lamP / κp) ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2) := by
          rw [← hsY t, hdY (t + 1)]
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · -- `κ_p = 0`: `ω̃` is pinned at its strict-targeting value
      have hD : ∀ t, D t = 0 := fun t => by
        have := e18 t
        rw [← hκ0, zero_mul, zero_add] at this
        exact (mul_eq_zero.1 this).resolve_left hlamP.ne'
      have hδ : ∀ t, δ t = 0 := fun t => by
        cases t with
        | zero => rw [e0, hD 0]
        | succ t => have := eD t; rw [hD (t + 1), hD t] at this; linarith
      refine ⟨funext hD, funext hδ, funext fun t => ?_⟩
      have := e20 t
      rw [hδ t, hδ (t + 1), hD t] at this
      have h : κw * dY t = 0 := by linarith
      exact (mul_eq_zero.1 h).resolve_left hκw.ne'
  obtain ⟨hD, hδ, hdY⟩ := hzero
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · have := congrFun hdY t
    simp only [hdYdef, Pi.zero_apply] at this
    linarith
  · have := congrFun hδ t
    simp only [hδdef, Pi.zero_apply] at this
    linarith
  · have := congrFun hD t
    simp only [hDdef, Pi.zero_apply] at this
    linarith

/-- Galí (2015), p. 180 (**strict price-inflation targeting is suboptimal with sticky wages**):
for `0 < β ≤ 1`, `κ_p ≥ 0`, `κ_w, λ_p, λ_w, Θ_y > 0` and weights `c_p, c_w ≥ 0`, there is a
technology-shock path `Δωⁿ` (`priceShock`, zero from `t = 2` on) for which a path with
`π^p ≡ 0` exists; every such path with `∑ βᵗ ỹ_t² < ∞` has **strictly higher loss** (28) than
some other feasible path. -/
theorem strict_price_targeting_suboptimal {β κp κw lamP lamW Θy cp cw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hκp : 0 ≤ κp) (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hΘ : 0 < Θy) (hcp : 0 ≤ cp) (hcw : 0 ≤ cw) :
    (∀ t, priceShock κp κw lamP lamW (t + 2) = 0) ∧
      Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) spY (fun _ => 0)
        (spW κp κw lamP lamW) (spOm κp lamP) ∧
      ∀ y pw om : ℕ → ℝ,
        Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y (fun _ => 0) pw om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ,
          Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y' pp' pw' om' ∧
            loss β Θy cp cw y' pp' pw' < loss β Θy cp cw y (fun _ => 0) pw := by
  refine ⟨fun t => rfl, feasible_sp hlamP, fun y pw om hF hs => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := sp_unique hβ0 hβ1 hκp hlamP hlamW hκw hF hs
  have hM : 0 ≤ bigM κp κw lamP lamW := by unfold bigM; positivity
  have hB : 0 < Θy * (1 + β + (lamP + lamW)) +
      cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW) := by
    have h1 : 0 < Θy * (1 + β + (lamP + lamW)) := mul_pos hΘ (by linarith)
    have h2 : 0 ≤ cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW) := by
      positivity
    linarith
  have hQ : 0 ≤ (Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) := by
    positivity
  have himp := quad_improve hB.ne' hQ
  set τ := -(Θy * (1 + β + (lamP + lamW)) +
      cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW)) /
    ((Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) + 1)
    with hτ
  refine ⟨_, _, _, _, feasible_add τ (feasible_sp (β := β) (κw := κw) (lamW := lamW) hlamP)
    (feasible_dir β κp κw lamP lamW), ?_⟩
  rw [loss_two (fun t => by simp [spY, dirY]) (fun t => by simp [dirP])
      (fun t => by simp [spW, dirW]),
    loss_two (fun t => by simp [spY]) (fun _ => rfl) (fun t => by simp [spW])]
  simp only [spY, spW, dirY, dirP, dirW]
  simp only [bigM] at himp ⊢
  linear_combination himp

/-- Galí (2015), p. 180: the technology-shock path used for strict wage-inflation targeting,
`Δωⁿ = (−(M + κ_w)/λ_w, κ_w/λ_w, 0, …)`. -/
noncomputable def wageShock (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => -(bigM κp κw lamP lamW + κw) / lamW
  | 1 => κw / lamW
  | _ + 2 => 0

/-- Galí (2015), p. 180: the strict wage-targeting path, price inflation `(M/λ_w, 0, …)`. -/
noncomputable def swP (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => bigM κp κw lamP lamW / lamW
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict wage-targeting path, real-wage gap `(κ_w/λ_w, 0, …)`. -/
noncomputable def swOm (κw lamW : ℝ) : ℕ → ℝ
  | 0 => κw / lamW
  | _ + 1 => 0

/-- Galí (2015), p. 180: `π^w ≡ 0`, `ỹ = spY`, `π^p = swP`, `ω̃ = swOm` is feasible for the
technology shock `wageShock`. -/
theorem feasible_sw {β κp κw lamP lamW : ℝ} (hlamW : 0 < lamW) :
    Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) spY (swP κp κw lamP lamW)
      (fun _ => 0) (swOm κw lamW) := by
  have hl : lamW ≠ 0 := hlamW.ne'
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [spY, swOm, swP, bigM]; field_simp; ring
    | n + 1 => simp only [spY, swOm, swP]; ring
  · match t with
    | 0 => simp only [spY, swOm]; field_simp; ring
    | n + 1 => simp only [spY, swOm]; ring
  · simp only [swOm, swP, wageShock, bigM]
    field_simp
    ring
  · match t with
    | 0 => simp only [swOm, swP, wageShock]; ring
    | n + 1 => simp only [swOm, swP, wageShock]; ring

/-- Galí (2015), p. 180 (**uniqueness of the strict wage-targeting path**): with `0 < β ≤ 1`,
`κ_p ≥ 0`, `κ_w, λ_p, λ_w > 0`, every feasible path for `wageShock` with `π^w ≡ 0` and
`∑ βᵗ ỹ_t² < ∞` is the explicit path `(spY, swP, 0, swOm)`. -/
theorem sw_unique {β κp κw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hκp : 0 ≤ κp)
    (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW) {y pp om : ℕ → ℝ}
    (hF : Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y pp (fun _ => 0) om)
    (hs : Summable fun t => β ^ t * y t ^ 2) :
    y = spY ∧ pp = swP κp κw lamP lamW ∧ om = swOm κw lamW := by
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := feasible_sw (β := β) (κp := κp) (κw := κw) (lamP := lamP) hlamW
  set D : ℕ → ℝ := fun t => om t - swOm κw lamW t with hDdef
  set δ : ℕ → ℝ := fun t => swP κp κw lamP lamW t - pp t with hδdef
  set dY : ℕ → ℝ := fun t => y t - spY t with hdYdef
  set m := κp * lamW / κw + lamP with hm
  have hm0 : 0 ≤ m := by positivity
  have hdY : ∀ t, dY t = lamW / κw * D t := fun t => by
    have a := f2 t
    have b := g2 t
    simp only [hDdef, hdYdef]
    field_simp
    linarith
  have e0 : δ 0 = D 0 := by
    simp only [hDdef, hδdef]
    linarith
  have eD : ∀ t, D (t + 1) = D t + δ (t + 1) := fun t => by
    have a := f4 t
    have b := g4 t
    simp only [hDdef, hδdef]
    linarith
  have eδ : ∀ t, β * δ (t + 1) = δ t + m * D t := fun t => by
    have a := f1 t
    have b := g1 t
    have c := hdY t
    simp only [hDdef, hδdef, hdYdef] at c ⊢
    rw [hm]
    field_simp at c ⊢
    nlinarith
  have hsY : ∀ t, β ^ (t + 1) * dY (t + 1) ^ 2 = β ^ (t + 1) * y (t + 1) ^ 2 := fun t => by
    simp [hdYdef, spY]
  have hzero : ∀ t, D t = 0 ∧ δ t = 0 := by
    rcases eq_or_ne (D 0) 0 with hD0 | hD0
    · exact zero_of_growth hβ0 e0 eD eδ hD0
    · exfalso
      have hsq := sq_le_of_growth hβ0 hβ1 hm0 e0 eD eδ
      have hk : 0 < (lamW / κw) ^ 2 * D 0 ^ 2 := by positivity
      refine not_summable_of_ge hk (fun t => ?_) hs
      have h1 := hsq (t + 1)
      have h2 : β ^ (t + 1) * y (t + 1) ^ 2
          = (lamW / κw) ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2) := by
        rw [← hsY t, hdY (t + 1)]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · have h := hdY t
    rw [(hzero t).1, mul_zero] at h
    simp only [hdYdef] at h
    linarith
  · have h := (hzero t).2
    simp only [hδdef] at h
    linarith
  · have h := (hzero t).1
    simp only [hDdef] at h
    linarith

/-- Galí (2015), p. 180 (**strict wage-inflation targeting is suboptimal with sticky prices**):
for `0 < β ≤ 1`, `κ_p ≥ 0`, `κ_w, λ_p, λ_w, Θ_y > 0` and weights `c_p, c_w ≥ 0`, there is a
technology-shock path `Δωⁿ` (`wageShock`) for which a path with `π^w ≡ 0` exists; every such
path with `∑ βᵗ ỹ_t² < ∞` has **strictly higher loss** (28) than some other feasible path. -/
theorem strict_wage_targeting_suboptimal {β κp κw lamP lamW Θy cp cw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hκp : 0 ≤ κp) (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hΘ : 0 < Θy) (hcp : 0 ≤ cp) (hcw : 0 ≤ cw) :
    (∀ t, wageShock κp κw lamP lamW (t + 2) = 0) ∧
      Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) spY (swP κp κw lamP lamW)
        (fun _ => 0) (swOm κw lamW) ∧
      ∀ y pp om : ℕ → ℝ,
        Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y pp (fun _ => 0) om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ,
          Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y' pp' pw' om' ∧
            loss β Θy cp cw y' pp' pw' < loss β Θy cp cw y pp (fun _ => 0) := by
  refine ⟨fun t => rfl, feasible_sw hlamW, fun y pp om hF hs => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := sw_unique hβ0 hβ1 hκp hκw hlamP hlamW hF hs
  have hM : 0 ≤ bigM κp κw lamP lamW := by unfold bigM; positivity
  have hB : 0 < Θy * (1 + β + (lamP + lamW)) +
      cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW) := by
    have h1 : 0 < Θy * (1 + β + (lamP + lamW)) := mul_pos hΘ (by linarith)
    have h2 : 0 ≤ cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW) := by
      positivity
    linarith
  have hQ : 0 ≤ (Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) := by
    positivity
  have himp := quad_improve hB.ne' hQ
  set τ := -(Θy * (1 + β + (lamP + lamW)) +
      cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW)) /
    ((Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) + 1)
    with hτ
  refine ⟨_, _, _, _, feasible_add τ (feasible_sw (β := β) (κp := κp) (lamP := lamP) hlamW)
    (feasible_dir β κp κw lamP lamW), ?_⟩
  rw [loss_two (fun t => by simp [spY, dirY]) (fun t => by simp [swP, dirP])
      (fun t => by simp [dirW]),
    loss_two (fun t => by simp [spY]) (fun t => by simp [swP]) (fun _ => rfl)]
  simp only [spY, swP, dirY, dirP, dirW]
  simp only [bigM] at himp ⊢
  linear_combination himp

/-- Galí (2015), p. 180: the model's coefficients are admissible: for `0 < β < 1`, `σ > 0`,
`φ ≥ 0`, `0 ≤ α < 1`, `ε_p, ε_w > 0`, `θ_p, θ_w ∈ (0, 1)`: `λ_p, λ_w > 0`, `κ_p ≥ 0`, `κ_w > 0`,
`σ + (φ+α)/(1−α) > 0` and the inflation weights are nonnegative. -/
theorem model_coefficients {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hθp0 : 0 < θp)
    (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    0 < lambdaP β θp α εp ∧ 0 < lambdaW β θw φ εw ∧ 0 ≤ kappaP α (lambdaP β θp α εp) ∧
      0 < kappaW σ φ α (lambdaW β θw φ εw) ∧ 0 < gapCoeff σ φ α ∧
      0 ≤ priceWeight β θp α εp ∧ 0 ≤ wageWeight β θw α φ εw := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hΘ : 0 < bigTheta α εp := div_pos h1 (by nlinarith)
  have hβθp : 0 < 1 - β * θp := by nlinarith
  have hβθw : 0 < 1 - β * θw := by nlinarith
  have hlp : 0 < lambdaP β θp α εp :=
    mul_pos (div_pos (mul_pos (by linarith) hβθp) hθp0) hΘ
  have hlw : 0 < lambdaW β θw φ εw :=
    div_pos (mul_pos (by linarith) hβθw) (mul_pos hθw0 (by nlinarith))
  have hg : 0 < gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) h1.le
    linarith
  refine ⟨hlp, hlw, div_nonneg (mul_nonneg hα0 hlp.le) h1.le,
    mul_pos hlw (by have := div_nonneg hφ h1.le; linarith), hg,
    div_nonneg hεp.le hlp.le, div_nonneg (mul_nonneg hεw.le h1.le) hlw.le⟩

/-- Galí (2015), p. 180 (**strict price-inflation targeting is suboptimal, model form**): with
the model's `κ_p = αλ_p/(1−α)`, `κ_w = λ_w(σ + φ/(1−α))`, `λ_p`, `λ_w` and the weights of (28),
for every `θ_p, θ_w ∈ (0, 1)` there is a technology-shock path for which the (unique) strict
price-inflation-targeting path is strictly beaten by another feasible path. -/
theorem strict_price_targeting_suboptimal_model {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp)
    (hεw : 0 < εw) (hθp0 : 0 < θp) (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    ∃ dn : ℕ → ℝ, (∀ t, dn (t + 2) = 0) ∧
      (∃ y pw om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
        (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y
          (fun _ => 0) pw om) ∧
      ∀ y pw om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
          (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y
            (fun _ => 0) pw om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
            (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn
              y' pp' pw' om' ∧
          loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y' pp' pw'
            < loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y
              (fun _ => 0) pw := by
  obtain ⟨hlp, hlw, hkp, hkw, hg, hcp, hcw⟩ := model_coefficients hβ0 hβ1 hσ hφ hα0 hα1 hεp
    hεw hθp0 hθp1 hθw0 hθw1
  obtain ⟨h1, h2, h3⟩ := strict_price_targeting_suboptimal (Θy := gapCoeff σ φ α)
    (cp := priceWeight β θp α εp) (cw := wageWeight β θw α φ εw) hβ0 hβ1.le hkp hkw hlp hlw hg
    hcp hcw
  exact ⟨_, h1, ⟨_, _, _, h2⟩, h3⟩

/-- Galí (2015), p. 180 (**strict wage-inflation targeting is suboptimal, model form**): for
every `θ_p, θ_w ∈ (0, 1)` there is a technology-shock path for which the (unique) strict
wage-inflation-targeting path is strictly beaten by another feasible path. -/
theorem strict_wage_targeting_suboptimal_model {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp)
    (hεw : 0 < εw) (hθp0 : 0 < θp) (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    ∃ dn : ℕ → ℝ, (∀ t, dn (t + 2) = 0) ∧
      (∃ y pp om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
        (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y pp
          (fun _ => 0) om) ∧
      ∀ y pp om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
          (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y pp
            (fun _ => 0) om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
            (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn
              y' pp' pw' om' ∧
          loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y' pp' pw'
            < loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y pp
              (fun _ => 0) := by
  obtain ⟨hlp, hlw, hkp, hkw, hg, hcp, hcw⟩ := model_coefficients hβ0 hβ1 hσ hφ hα0 hα1 hεp
    hεw hθp0 hθp1 hθw0 hθw1
  obtain ⟨h1, h2, h3⟩ := strict_wage_targeting_suboptimal (Θy := gapCoeff σ φ α)
    (cp := priceWeight β θp α εp) (cw := wageWeight β θw α φ εw) hβ0 hβ1.le hkp hkw hlp hlw hg
    hcp hcw
  exact ⟨_, h1, ⟨_, _, _, h2⟩, h3⟩

end Gali.StickyWagesPrices.LimitingCases

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Baseline calibration

Galí (2015), Chapter 6, §6.2.1 (pp. 176–177) and §6.5 (pp. 185–187).

The baseline is the Chapter 3 calibration `β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`, `ε_p = 9`,
`θ_p = 3/4`, together with `θ_w = 3/4` (p. 176) and `ε_w = 4.5` (p. 177). Exact values:

* `lambdaP_baseline`: `λ_p = 103/4800 ≈ 0.02146`; `lambdaW_baseline`: `λ_w = 103/28200 ≈ 0.00365`.
* `kappaP_baseline`, `kappaW_baseline`: `κ_p = 103/14400`, `κ_w = 2369/84600`.
* `compositeWeight_baseline`: the weight of wage inflation in composite inflation
  `π̄ = (λ_w π^p + λ_p π^w)/(λ_p + λ_w)` is `λ_p/(λ_p + λ_w) = 47/55 ≈ 0.8545` ("0.85", p. 186).
* `gapCoeff_baseline`, `priceWeight_baseline`, `wageWeight_baseline`: the loss weights of (28)
  and (29) are `8`, `43200/103 ≈ 419.4` and `95175/103 ≈ 924.0`.

Table 6.1 (p. 186) reports **simulated** volatilities and losses; the simulation itself is
computational and not formalised. `table61_losses` recomputes the average loss (29) from the
printed standard deviations (in percent; `L` in percent of steady-state consumption) for the
seven technology-shock columns: every recomputed value lies 2–7% **below** the printed one
(e.g. `0.0296` vs `0.0330` for the optimal policy), consistent with truncated standard
deviations (survey item 11, informational, not an error). The recomputed ranking
(`table61_ranking`) agrees with the printed one except that flexible composite and flexible
wage targeting swap places (`table61_flexible_swap`: printed `0.307 > 0.305`, recomputed
`0.288 < 0.295`); the book's text does not rank these two.
-/

namespace Gali.StickyWagesPrices.Calibration

open Gali.StickyWagesPrices.Welfare Gali.StickyWagesPrices.LimitingCases
open Gali.StickyWagesPrices.WageDispersion

/-- Galí (2015), pp. 166 and 176: at the baseline, `λ_p = 103/4800`. -/
theorem lambdaP_baseline : lambdaP 0.99 0.75 0.25 9 = 103 / 4800 := by
  unfold lambdaP bigTheta
  norm_num

/-- Galí (2015), pp. 170 and 177: at the baseline, `λ_w = 103/28200`. -/
theorem lambdaW_baseline : lambdaW 0.99 0.75 5 4.5 = 103 / 28200 := by
  unfold lambdaW
  norm_num

/-- Galí (2015), p. 172: at the baseline, `κ_p = α λ_p/(1 − α) = 103/14400`. -/
theorem kappaP_baseline : kappaP 0.25 (lambdaP 0.99 0.75 0.25 9) = 103 / 14400 := by
  rw [lambdaP_baseline]
  unfold kappaP
  norm_num

/-- Galí (2015), p. 172: at the baseline, `κ_w = λ_w (σ + φ/(1 − α)) = 2369/84600`. -/
theorem kappaW_baseline : kappaW 1 5 0.25 (lambdaW 0.99 0.75 5 4.5) = 2369 / 84600 := by
  rw [lambdaW_baseline]
  unfold kappaW
  norm_num

/-- Galí (2015), p. 186 (**"wage inflation has a weight of 0.85 in composite inflation"**): at
the baseline, `λ_p/(λ_p + λ_w) = 47/55`, which lies in `(0.8545, 0.8546)` and rounds to
`0.85`. -/
theorem compositeWeight_baseline :
    lambdaP 0.99 0.75 0.25 9 / (lambdaP 0.99 0.75 0.25 9 + lambdaW 0.99 0.75 5 4.5) = 47 / 55 ∧
      (0.8545 : ℝ) < 47 / 55 ∧ (47 / 55 : ℝ) < 0.8546 ∧ |(47 / 55 : ℝ) - 0.85| < 0.005 := by
  rw [lambdaP_baseline, lambdaW_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [abs_lt]
  constructor <;> norm_num

/-- Galí (2015), p. 186: the weight of price inflation in composite inflation,
`λ_w/(λ_p + λ_w) = 8/55 ≈ 0.145`. -/
theorem compositePriceWeight_baseline :
    lambdaW 0.99 0.75 5 4.5 / (lambdaP 0.99 0.75 0.25 9 + lambdaW 0.99 0.75 5 4.5) = 8 / 55 := by
  rw [lambdaP_baseline, lambdaW_baseline]
  norm_num

/-- Galí (2015), eq. (28), p. 179: at the baseline the output-gap weight is
`σ + (φ + α)/(1 − α) = 8`. -/
theorem gapCoeff_baseline : gapCoeff 1 5 0.25 = 8 := by
  unfold gapCoeff
  norm_num

/-- Galí (2015), eq. (28), p. 179: at the baseline the price-inflation weight is
`ε_p/λ_p = 43200/103 ≈ 419.4`. -/
theorem priceWeight_baseline :
    priceWeight 0.99 0.75 0.25 9 = 43200 / 103 ∧ (419.4 : ℝ) < 43200 / 103 ∧
      (43200 / 103 : ℝ) < 419.5 := by
  unfold priceWeight
  rw [lambdaP_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Galí (2015), eq. (28), p. 179: at the baseline the wage-inflation weight is
`ε_w(1 − α)/λ_w = 95175/103 ≈ 924.0`. -/
theorem wageWeight_baseline :
    wageWeight 0.99 0.75 0.25 5 4.5 = 95175 / 103 ∧ (924 : ℝ) < 95175 / 103 ∧
      (95175 / 103 : ℝ) < 924.1 := by
  unfold wageWeight
  rw [lambdaW_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Galí (2015), p. 179: at the baseline the wage-inflation weight is more than twice the
price-inflation weight (`924.0` vs `419.4`), even though the composite-inflation weights favour
wage inflation by `47 : 8`. -/
theorem wageWeight_gt_priceWeight_baseline :
    2 * priceWeight 0.99 0.75 0.25 9 < wageWeight 0.99 0.75 0.25 5 4.5 := by
  rw [priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), eq. (29), p. 179, in the units of Table 6.1: standard deviations in percent,
loss in percent of steady-state consumption, `L = ½[8 σ(ỹ)² + 419.4 σ(π^p)² + 924.0 σ(π^w)²]/100`
with the exact baseline weights. -/
noncomputable def tableLoss (sdY sdP sdW : ℝ) : ℝ :=
  (gapCoeff 1 5 0.25 * sdY ^ 2 + priceWeight 0.99 0.75 0.25 9 * sdP ^ 2 +
    wageWeight 0.99 0.75 0.25 5 4.5 * sdW ^ 2) / 200

/-- Galí (2015), Table 6.1, p. 186 (technology shocks), **computational record**: the average
loss (29) recomputed from the printed standard deviations, against the printed `L`:
optimal `0.0296` (printed `0.0330`), strict price `0.769` (`0.78`), strict wage `0.0370`
(`0.039`), strict composite `0.0320` (`0.0337`), flexible price `0.449` (`0.47`), flexible wage
`0.295` (`0.305`), flexible composite `0.288` (`0.307`). Every recomputed value is below the
printed one. -/
theorem table61_losses :
    (0.0295 < tableLoss 0.04 0.11 0.03 ∧ tableLoss 0.04 0.11 0.03 < 0.0297) ∧
      (0.769 < tableLoss 3.38 0 0.26 ∧ tableLoss 3.38 0 0.26 < 0.770) ∧
      (0.0370 < tableLoss 0.20 0.13 0 ∧ tableLoss 0.20 0.13 0 < 0.0371) ∧
      (0.0320 < tableLoss 0 0.12 0.02 ∧ tableLoss 0 0.12 0.02 < 0.0321) ∧
      (0.448 < tableLoss 0.84 0.29 0.23 ∧ tableLoss 0.84 0.29 0.23 < 0.450) ∧
      (0.294 < tableLoss 1.18 0.24 0.16 ∧ tableLoss 1.18 0.24 0.16 < 0.295) ∧
      (0.288 < tableLoss 1.11 0.24 0.16 ∧ tableLoss 1.11 0.24 0.16 < 0.289) := by
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), Table 6.1 and p. 186 (**ranking from the recomputed losses**): optimal <
strict composite < strict wage < flexible composite < flexible wage < flexible price < strict
price. This is the printed order except for the flexible composite/wage pair. -/
theorem table61_ranking :
    tableLoss 0.04 0.11 0.03 < tableLoss 0 0.12 0.02 ∧
      tableLoss 0 0.12 0.02 < tableLoss 0.20 0.13 0 ∧
      tableLoss 0.20 0.13 0 < tableLoss 1.11 0.24 0.16 ∧
      tableLoss 1.11 0.24 0.16 < tableLoss 1.18 0.24 0.16 ∧
      tableLoss 1.18 0.24 0.16 < tableLoss 0.84 0.29 0.23 ∧
      tableLoss 0.84 0.29 0.23 < tableLoss 3.38 0 0.26 := by
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), Table 6.1, p. 186 (informational): the printed losses rank flexible wage
targeting (`0.305`) above flexible composite targeting (`0.307`), but the losses recomputed
from the printed standard deviations reverse the pair. -/
theorem table61_flexible_swap :
    (0.305 : ℝ) < 0.307 ∧ tableLoss 1.11 0.24 0.16 < tableLoss 1.18 0.24 0.16 := by
  refine ⟨by norm_num, ?_⟩
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

end Gali.StickyWagesPrices.Calibration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal monetary policy with sticky wages and prices

Galí (2015), Section 6.4, pp. 181–185, and Appendix 6.2, p. 192.

The central bank minimises the welfare loss (28),
`𝕎 = ½ E_0 ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)` with `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w`, subject to (18), (20), (21) for `t ≥ 0`, given
`ω̃_{−1}`. The model equations and the loss are stated here directly (no other chain imported);
the coefficients are bundled in `Coef`, the book's values in `bookCoef`. Equations hold for an
arbitrary `ExpectationSystem`, so results cover perfect foresight and genuine uncertainty.

## Main results

* **Commitment, deterministic** (`Det`, all feasible paths with finite loss): the Lagrangian
  identity `lagrangian_alg`; transversality for the predetermined real wage gap
  (`tendsto_disc_partial`, Cauchy–Schwarz); `Det.loss_sub_hasSum` (the excess loss is the
  discounted quadratic form of the deviations); SUFFICIENCY `Det.isOptimal_of_foc`, UNIQUENESS
  `Det.eq_of_loss_eq`, NECESSITY (whenever (30)–(33) have a bounded-multiplier solution)
  `Det.isOptimal_iff_foc`, `Det.existsUnique_optimal`.
* **Commitment, stochastic** (`Stoch`, bounded adapted plans, pull-out property):
  `Stoch.period_identity`, `Stoch.E0_identity`, `Stoch.expLoss_sub_hasSum`,
  `Stoch.commitment_optimal` (optimal state by state; unique in conditional mean square).
* **Appendix 6.2**: `Stoch.matrix_form_iff` — (18), (20), (21), (30)–(33) ⇔
  `A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t` for the printed 7 × 7 matrices.
* **§6.4.1**: `Det.demand_zero_optimal`, `Stoch.demand_zero_optimal` (zero path optimal and
  unique); `Stoch.rule_implements` (the rule `i_t = rⁿ_t + φ_p π^p_t` supports it, uniquely under
  `RuleDeterminate`); determinacy for `φ_p > 1` and general parameters from the p. 174 theorem
  (`Determinacy4`): `Stoch.rule_isSol`, `Stoch.ruleDeterminate_of_phiP`,
  `Stoch.ruleDeterminate_book`, and the unconditional `Stoch.rule_implements_book`; for
  `κ_p = κ_w` an elementary proof and the converse: `Stoch.ruleDeterminate_of_kap_eq`,
  `Stoch.not_ruleDeterminate`, `Stoch.ruleDeterminate_iff` (determinate iff `φ_p > 1`), via the
  relative-inflation block `Stoch.block_zero` and the Chapter 3 system `schur_ruleA_iff`.
* **fn. 6, (34)–(36)**: `book_fn6`, `book_composite_slope`, `Stoch.composite_nkpc` (36) with the
  general slope `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)` (survey error 3), `Det.composite_foc`,
  `Stoch.composite_foc` (34)–(35).
* **p. 184, special case optimality** (survey Note N6.1 separation, replacing the book's argument,
  which checks only the necessary conditions (34)–(35): survey error 2,
  `composite_path_satisfies_34_35`): `separation`, `Stoch.proj_plan`,
  `Stoch.periodLoss_sub_proj` (pathwise), `Stoch.composite_targeting_optimal`,
  `Stoch.exists_composite_plan`, `Stoch.composite_targeting_solves` (under `E_0`, by
  monotonicity); `Det.block_zero_finite`, `Det.composite_targeting_optimal`,
  `Det.composite_targeting_existsUnique` (among all finite-loss paths).
* **Composite weights and targeting**: `wage_weight_strictMonoOn`, `price_weight_strictMonoOn`;
  `Stoch.composite_zero_iff` (strict composite targeting ⇔ `ỹ ≡ 0`, all parameters).
-/

namespace Gali.StickyWagesPrices.OptimalPolicy

open Filter Topology

/-! ### Coefficients and lags -/

/-- Galí (2015), (18), (20), (28), pp. 172, 179: the coefficients of the optimal-policy problem:
the discount factor, the slopes `κ_p, κ_w, λ_p, λ_w` of the price and wage Phillips curves, and the
loss weights `a_y, a_p, a_w` on `ỹ², (π^p)², (π^w)²` (in the book `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w`, see `bookCoef`). -/
structure Coef where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The output-gap slope `κ_p` of the price Phillips curve (18). -/
  kapP : ℝ
  /-- The output-gap slope `κ_w` of the wage Phillips curve (20). -/
  kapW : ℝ
  /-- The real-wage-gap slope `λ_p` of (18). -/
  lamP : ℝ
  /-- The real-wage-gap slope `λ_w` of (20). -/
  lamW : ℝ
  /-- The loss weight on `ỹ²`. -/
  ay : ℝ
  /-- The loss weight on `(π^p)²`. -/
  ap : ℝ
  /-- The loss weight on `(π^w)²`. -/
  aw : ℝ

/-- Galí (2015), (18), (20), (28), pp. 172, 179: the book's coefficients, with
`κ_p = αλ_p/(1 − α)`, `κ_w = λ_w(σ + φ/(1 − α))`, `a_y = σ + (φ + α)/(1 − α)`, `a_p = ε_p/λ_p`,
`a_w = ε_w(1 − α)/λ_w`. -/
noncomputable def bookCoef (β σ φ α εp εw lamP lamW : ℝ) : Coef where
  β := β
  kapP := α * lamP / (1 - α)
  kapW := lamW * (σ + φ / (1 - α))
  lamP := lamP
  lamW := lamW
  ay := σ + (φ + α) / (1 - α)
  ap := εp / lamP
  aw := εw * (1 - α) / lamW

/-- Galí (2015), (21), p. 172: the lag `x_{t−1}` of a sequence with initial value `x_{−1} = x0`
(used for `ω̃_{t−1}` with `ω̃_{−1}` given, and for the multipliers with `ζ_{−1} = 0`). -/
def prev {α : Type*} (x0 : α) (x : ℕ → α) : ℕ → α
  | 0 => x0
  | t + 1 => x t

/-- Galí (2015), p. 181: `x_{−1} = x0`. -/
@[simp] theorem prev_zero {α : Type*} (x0 : α) (x : ℕ → α) : prev x0 x 0 = x0 := rfl

/-- Galí (2015), p. 181: the lag at date `t + 1` is the date-`t` value. -/
@[simp] theorem prev_succ {α : Type*} (x0 : α) (x : ℕ → α) (t : ℕ) : prev x0 x (t + 1) = x t :=
  rfl

/-- Galí (2015), p. 181: the lag of a difference with common initial value starts at zero. -/
theorem prev_sub {α : Type*} [AddGroup α] (x0 : α) (x x' : ℕ → α) (t : ℕ) :
    prev x0 x t - prev x0 x' t = prev 0 (fun s => x s - x' s) t := by
  cases t <;> simp

/-! ### The Lagrangian identity -/

/-- **Galí (2015), (30)–(33), p. 181 (the Lagrangian identity, one period)**: if `(ỹ*, π^p*, π^w*,
ω̃*)` satisfies the constraints (18), (20), (21) and the first-order conditions (30)–(33) with
multipliers `ζ₁, ζ₂, ζ₃`, and `(ỹ, π^p, π^w, ω̃)` satisfies the same constraints, then the excess
period loss is the quadratic form in the deviations plus a telescoping term. Here `Ep` stands for
(the conditional expectation of) next period's price inflation, etc. -/
theorem lagrangian_alg (c : Coef) {y p q w wl ys ps qs ws wsl Ep Eq Eps Eqs dn z1 z1l z2 z2l z3
    Ez3 : ℝ}
    (c1 : p = c.β * Ep + c.kapP * y + c.lamP * w) (c2 : q = c.β * Eq + c.kapW * y - c.lamW * w)
    (c3 : w = wl + q - p - dn) (c1s : ps = c.β * Eps + c.kapP * ys + c.lamP * ws)
    (c2s : qs = c.β * Eqs + c.kapW * ys - c.lamW * ws) (c3s : ws = wsl + qs - ps - dn)
    (f1 : c.ay * ys + c.kapP * z1 + c.kapW * z2 = 0) (f2 : c.ap * ps - (z1 - z1l) + z3 = 0)
    (f3 : c.aw * qs - (z2 - z2l) - z3 = 0)
    (f4 : c.lamP * z1 - c.lamW * z2 + z3 - c.β * Ez3 = 0) :
    (c.ay * y ^ 2 + c.ap * p ^ 2 + c.aw * q ^ 2) / 2 -
        (c.ay * ys ^ 2 + c.ap * ps ^ 2 + c.aw * qs ^ 2) / 2 =
      (c.ay * (y - ys) ^ 2 + c.ap * (p - ps) ^ 2 + c.aw * (q - qs) ^ 2) / 2 +
        c.β * (z1 * (Ep - Eps) + z2 * (Eq - Eqs) + (w - ws) * Ez3) -
          (z1l * (p - ps) + z2l * (q - qs) + (wl - wsl) * z3) := by
  linear_combination (y - ys) * f1 + (p - ps) * f2 + (q - qs) * f3 + z1 * (c1 - c1s) +
    z2 * (c2 - c2s) - z3 * (c3 - c3s) + (w - ws) * f4

/-- Galí (2015), p. 181 (the Lagrangian argument, abstract form): if `g_t = D_t + (h_{t+1} − h_t)`
with `D_t ≥ 0`, `h_0 = 0` (`ζ_{1,−1} = ζ_{2,−1} = 0`, common `ω̃_{−1}`) and `h_t → 0`
(transversality), and `∑ g_t = G`, then `∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + (h (t + 1) - h t)) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t - h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.sub hh

/-! ### Weighted square summability -/

/-- Galí (2015), p. 181 (transversality): if `∑ βᵗ x_t²` converges, `0 ≤ β < 1`, then
`βᵗ |x_t| → 0`. -/
theorem tendsto_disc_abs {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * x t ^ 2)) :
    Tendsto (fun t => β ^ t * |x t|) atTop (𝓝 0) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  have h2 := hs.tendsto_atTop_zero
  have hup := (h1.add h2).div_const 2
  rw [add_zero, zero_div] at hup
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
  have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have hx : |x t| ≤ (1 + x t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|x t| - 1), sq_abs (x t)]
  have := mul_le_mul_of_nonneg_left hx hb
  linarith

/-- Galí (2015), p. 181 (transversality for the predetermined real wage gap): if
`∑ βᵗ e_t²` converges, `0 < β < 1`, then `βᵗ ∑_{s<t} |e_s| → 0` (Cauchy–Schwarz:
`(∑_{s<t} |e_s|)² ≤ (∑ βˢ e_s²)(∑_{s<t} β⁻ˢ)`). -/
theorem tendsto_disc_partial {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {e : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * e t ^ 2)) :
    Tendsto (fun t => β ^ t * ∑ s ∈ Finset.range t, |e s|) atTop (𝓝 0) := by
  set S := ∑' t, β ^ t * e t ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun t => by positivity
  have hbi : 1 < β⁻¹ := one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩
  set K := S / (β⁻¹ - 1) with hK
  have hK0 : 0 ≤ K := div_nonneg hS0 (by linarith)
  have hbound : ∀ t, (β ^ t * ∑ s ∈ Finset.range t, |e s|) ^ 2 ≤ K * β ^ t := by
    intro t
    have hcs : (∑ s ∈ Finset.range t, |e s|) ^ 2 ≤
        (∑ s ∈ Finset.range t, β ^ s * e s ^ 2) * ∑ s ∈ Finset.range t, β⁻¹ ^ s :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => by positivity)
        (fun s _ => by positivity) (fun s _ => by
          rw [sq_abs, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hβ0.ne', one_pow, one_mul])
    have h1 : ∑ s ∈ Finset.range t, β ^ s * e s ^ 2 ≤ S :=
      hs.sum_le_tsum _ (fun s _ => by positivity)
    have h2 : ∑ s ∈ Finset.range t, β⁻¹ ^ s ≤ β⁻¹ ^ t / (β⁻¹ - 1) := by
      rw [geom_sum_eq hbi.ne']
      gcongr
      linarith
    have h3 : (∑ s ∈ Finset.range t, |e s|) ^ 2 ≤ S * (β⁻¹ ^ t / (β⁻¹ - 1)) :=
      hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun s _ => by positivity) hS0)
    have hpow : (β ^ t) ^ 2 * β⁻¹ ^ t = β ^ t := by
      rw [inv_pow, sq]; field_simp
    calc (β ^ t * ∑ s ∈ Finset.range t, |e s|) ^ 2
        = (β ^ t) ^ 2 * (∑ s ∈ Finset.range t, |e s|) ^ 2 := by ring
      _ ≤ (β ^ t) ^ 2 * (S * (β⁻¹ ^ t / (β⁻¹ - 1))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K * ((β ^ t) ^ 2 * β⁻¹ ^ t) := by rw [hK]; ring
      _ = K * β ^ t := by rw [hpow]
  have hlim : Tendsto (fun t => Real.sqrt (K * β ^ t)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul K).sqrt
    simpa using this
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hlim
  have hnn : 0 ≤ β ^ t * ∑ s ∈ Finset.range t, |e s| := by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt (hbound t)

/-- Galí (2015), p. 181: `∑ βᵗ (a_t − b_t)²` converges when `∑ βᵗ a_t²` and `∑ βᵗ b_t²` do. -/
theorem summable_sub_sq {β : ℝ} (hβ0 : 0 ≤ β) {a b : ℕ → ℝ}
    (ha : Summable (fun t => β ^ t * a t ^ 2)) (hb : Summable (fun t => β ^ t * b t ^ 2)) :
    Summable (fun t => β ^ t * (a t - b t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
    ((ha.mul_left 2).add (hb.mul_left 2))
  have hp : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have : (a t - b t) ^ 2 ≤ 2 * a t ^ 2 + 2 * b t ^ 2 := by nlinarith [sq_nonneg (a t + b t)]
  have := mul_le_mul_of_nonneg_left this hp
  linarith

/-! ### The deterministic commitment problem -/

namespace Det

/-- Galí (2015), (18), (20), (21), p. 172 (perfect foresight): the constraints
`π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, `π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`,
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, `t ≥ 0`, with `ω̃_{−1} = w0` given. -/
def Feasible (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) + c.kapW * y t - c.lamW * w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Galí (2015), (30)–(33), p. 181 (perfect foresight): the first-order conditions with
multipliers `ζ₁, ζ₂, ζ₃` and `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOC (c : Coef) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, c.ay * y t + c.kapP * z1 t + c.kapW * z2 t = 0 ∧
    c.ap * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP * z1 t - c.lamW * z2 t + z3 t - c.β * z3 (t + 1) = 0

/-- Galí (2015), p. 181: the multipliers are bounded. -/
def BoundedMult (z1 z2 z3 : ℕ → ℝ) : Prop := ∃ Z, ∀ t, |z1 t| ≤ Z ∧ |z2 t| ≤ Z ∧ |z3 t| ≤ Z

/-- Galí (2015), (28), p. 179: the discounted period loss
`βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def lossTerm (c : Coef) (y pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.β ^ t * ((c.ay * y t ^ 2 + c.ap * pp t ^ 2 + c.aw * pw t ^ 2) / 2)

/-- Galí (2015), (28), p. 179: the loss is finite. -/
def FiniteLoss (c : Coef) (y pp pw : ℕ → ℝ) : Prop := Summable (lossTerm c y pp pw)

/-- Galí (2015), (28), p. 179: the loss `½ ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`
(used on finite-loss paths). -/
noncomputable def loss (c : Coef) (y pp pw : ℕ → ℝ) : ℝ := ∑' t, lossTerm c y pp pw t

/-- Galí (2015), §6.4, p. 181: `(ỹ, π^p, π^w, ω̃)` solves the commitment problem: it is feasible,
has finite loss, and no feasible finite-loss path has a smaller loss. -/
def IsOptimal (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  Feasible c dn w0 y pp pw w ∧ FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w', Feasible c dn w0 y' pp' pw' w' → FiniteLoss c y' pp' pw' →
      loss c y pp pw ≤ loss c y' pp' pw'

/-- Galí (2015), (28), p. 179: on a finite-loss path `∑ βᵗ ỹ_t²`, `∑ βᵗ (π^p_t)²` and
`∑ βᵗ (π^w_t)²` converge (positive weights). -/
theorem summable_sq {c : Coef} (hβ0 : 0 ≤ c.β) (hay : 0 < c.ay) (hap : 0 < c.ap)
    (haw : 0 < c.aw) {y pp pw : ℕ → ℝ} (hl : FiniteLoss c y pp pw) :
    Summable (fun t => c.β ^ t * y t ^ 2) ∧ Summable (fun t => c.β ^ t * pp t ^ 2) ∧
      Summable (fun t => c.β ^ t * pw t ^ 2) := by
  have key : ∀ t, 0 ≤ c.β ^ t * (c.ay * y t ^ 2) ∧ 0 ≤ c.β ^ t * (c.ap * pp t ^ 2) ∧
      0 ≤ c.β ^ t * (c.aw * pw t ^ 2) := fun t => ⟨by positivity, by positivity, by positivity⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.ay))
    rw [div_mul_eq_mul_div, le_div_iff₀ hay]
    unfold lossTerm
    nlinarith [key t]
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.ap))
    rw [div_mul_eq_mul_div, le_div_iff₀ hap]
    unfold lossTerm
    nlinarith [key t]
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.aw))
    rw [div_mul_eq_mul_div, le_div_iff₀ haw]
    unfold lossTerm
    nlinarith [key t]

/-- Galí (2015), (21), p. 172: two feasible paths with the same `ω̃_{−1}` and the same shocks
have lagged real wage gaps differing by the accumulated relative wage-price inflation:
`ω̃_{t−1} − ω̃*_{t−1} = ∑_{s<t} ((π^w_s − π^w*_s) − (π^p_s − π^p*_s))`. -/
theorem prev_sub_eq_sum {c : Coef} {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w ys pps pws ws : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hfs : Feasible c dn w0 ys pps pws ws) (t : ℕ) :
    prev w0 w t - prev w0 ws t =
      ∑ s ∈ Finset.range t, ((pw s - pws s) - (pp s - pps s)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, prev_succ, prev_succ]
    have h1 := (hf t).2.2
    have h2 := (hfs t).2.2
    linarith

/-- **Galí (2015), (30)–(33), p. 181 (sufficiency of the first-order conditions,
deterministic)**: if a feasible finite-loss path `(ỹ*, π^p*, π^w*, ω̃*)` satisfies (30)–(33) with
bounded multipliers (`ζ_{1,−1} = ζ_{2,−1} = 0`), then for every feasible finite-loss path
`L − L* = ½ ∑ βᵗ (a_y (ỹ_t − ỹ*_t)² + a_p (π^p_t − π^p*_t)² + a_w (π^w_t − π^w*_t)²)`: the
Lagrangian cross terms telescope, and the transversality term vanishes. -/
theorem loss_sub_hasSum {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw)
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    HasSum (fun t => c.β ^ t * ((c.ay * (y t - ys t) ^ 2 + c.ap * (pp t - pps t) ^ 2 +
        c.aw * (pw t - pws t) ^ 2) / 2)) (loss c y pp pw - loss c ys pps pws) := by
  obtain ⟨Z, hZ⟩ := hZ
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0).1
  obtain ⟨-, sp, sq⟩ := summable_sq hβ0.le hay hap haw hl
  obtain ⟨-, sps, sqs⟩ := summable_sq hβ0.le hay hap haw hls
  have sdp := summable_sub_sq hβ0.le sp sps
  have sdq := summable_sub_sq hβ0.le sq sqs
  have sde := summable_sub_sq hβ0.le sdq sdp
  have a1 := tendsto_disc_abs hβ0.le hβ1 sdp
  have a2 := tendsto_disc_abs hβ0.le hβ1 sdq
  have a3 := tendsto_disc_partial hβ0 hβ1 sde
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum) (fun t => by positivity)
    (h := fun t => c.β ^ t * (prev 0 z1 t * (pp t - pps t) + prev 0 z2 t * (pw t - pws t) +
      (prev w0 w t - prev w0 ws t) * z3 t)) (fun t => ?_) (by simp) ?_
  · have key := lagrangian_alg c (hf t).1 (hf t).2.1 (hf t).2.2 (hfs t).1 (hfs t).2.1
      (hfs t).2.2 (hξ t).1 (hξ t).2.1 (hξ t).2.2.1 (hξ t).2.2.2
    simp only [lossTerm, prev_succ, pow_succ]
    linear_combination c.β ^ t * key
  · have hup := ((a1.add a2).add a3).const_mul Z
    rw [add_zero, add_zero, mul_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ c.β ^ t := pow_nonneg hβ0.le t
    have hz1 : |prev 0 z1 t| ≤ Z := by cases t <;> simp [hZ0, (hZ _).1]
    have hz2 : |prev 0 z2 t| ≤ Z := by cases t <;> simp [hZ0, (hZ _).2.1]
    have hz3 : |z3 t| ≤ Z := (hZ t).2.2
    have hW : |prev w0 w t - prev w0 ws t| ≤
        ∑ s ∈ Finset.range t, |(pw s - pws s) - (pp s - pps s)| := by
      rw [prev_sub_eq_sum hf hfs t]
      exact Finset.abs_sum_le_sum_abs _ _
    have e1 : |prev 0 z1 t * (pp t - pps t)| ≤ Z * |pp t - pps t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hz1 (abs_nonneg _)
    have e2 : |prev 0 z2 t * (pw t - pws t)| ≤ Z * |pw t - pws t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hz2 (abs_nonneg _)
    have e3 : |(prev w0 w t - prev w0 ws t) * z3 t| ≤
        Z * ∑ s ∈ Finset.range t, |(pw s - pws s) - (pp s - pps s)| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hz3 hW (abs_nonneg _) hZ0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
    have htri := abs_add_three (prev 0 z1 t * (pp t - pps t)) (prev 0 z2 t * (pw t - pws t))
      ((prev w0 w t - prev w0 ws t) * z3 t)
    have hle := mul_le_mul_of_nonneg_left (htri.trans (add_le_add (add_le_add e1 e2) e3)) hb
    linarith

/-- **Galí (2015), §6.4, p. 181 (optimality, deterministic)**: a feasible finite-loss path
satisfying the first-order conditions (30)–(33) with bounded multipliers solves the commitment
problem. -/
theorem isOptimal_of_foc {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    IsOptimal c dn w0 ys pps pws ws :=
  ⟨hfs, hls, fun _ _ _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ).nonneg
      (fun t => by positivity))⟩

/-- **Galí (2015), §6.4, p. 181 (uniqueness, deterministic)**: a feasible finite-loss path with
the same loss as a path satisfying (30)–(33) with bounded multipliers coincides with it (all four
variables; the real wage gap by (21)). -/
theorem eq_of_loss_eq {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw)
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3)
    (heq : loss c y pp pw = loss c ys pps pws) : y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws := by
  have hs := loss_sub_hasSum hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, y t = ys t ∧ pp t = pps t ∧ pw t = pws t := fun t => by
    have h := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at h
    have k1 := mul_nonneg hay.le (sq_nonneg (y t - ys t))
    have k2 := mul_nonneg hap.le (sq_nonneg (pp t - pps t))
    have k3 := mul_nonneg haw.le (sq_nonneg (pw t - pws t))
    have e1 : c.ay * (y t - ys t) ^ 2 = 0 := by linarith
    have e2 : c.ap * (pp t - pps t) ^ 2 = 0 := by linarith
    have e3 : c.aw * (pw t - pws t) ^ 2 = 0 := by linarith
    simp only [mul_eq_zero, hay.ne', hap.ne', haw.ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, sub_eq_zero] at e1 e2 e3
    exact ⟨e1, e2, e3⟩
  have hw : ∀ t, prev w0 w t = prev w0 ws t := fun t => by
    have := prev_sub_eq_sum hf hfs t
    rw [Finset.sum_eq_zero (fun s _ => by rw [(ht s).2.1, (ht s).2.2]; ring)] at this
    linarith
  refine ⟨funext fun t => (ht t).1, funext fun t => (ht t).2.1, funext fun t => (ht t).2.2,
    funext fun t => ?_⟩
  have := hw (t + 1)
  simpa using this

/-- **Galí (2015), §6.4, p. 181 (necessity and sufficiency of the first-order conditions,
deterministic)**: if some feasible finite-loss path satisfies (30)–(33) with bounded multipliers
(the problem has a Lagrangian solution), then a feasible finite-loss path is optimal iff it
satisfies (30)–(33) with bounded multipliers, and the optimum is unique. -/
theorem isOptimal_iff_foc {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) {y pp pw w : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw) :
    (IsOptimal c dn w0 y pp pw w ↔
      ∃ z1' z2' z3', FOC c y pp pw z1' z2' z3' ∧ BoundedMult z1' z2' z3') ∧
    (IsOptimal c dn w0 y pp pw w ↔ y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws) := by
  have hopt := isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ
  have h2 : IsOptimal c dn w0 y pp pw w ↔ y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws := by
    constructor
    · rintro ⟨-, -, hmin⟩
      exact eq_of_loss_eq hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ
        (le_antisymm (hmin _ _ _ _ hfs hls) (hopt.2.2 _ _ _ _ hf hl))
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact hopt
  refine ⟨⟨fun h => ?_, fun ⟨z1', z2', z3', h1, h2⟩ =>
    isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl h1 h2⟩, h2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h2.1 h
  exact ⟨z1, z2, z3, hξ, hZ⟩

/-- **Galí (2015), §6.4, p. 181 (existence and uniqueness, deterministic)**: if the first-order
conditions have a feasible finite-loss solution with bounded multipliers, the commitment problem
has exactly one solution. -/
theorem existsUnique_optimal {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ), IsOptimal c dn w0 p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine ⟨(ys, pps, pws, ws), isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ, ?_⟩
  rintro ⟨y, pp, pw, w⟩ h
  obtain ⟨h1, h2, h3, h4⟩ := (isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ h.1 h.2.1).2.1 h
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end Det

/-! ### The commitment problem under uncertainty -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (18), (20), (21), p. 172: the constraints of the policy problem, for an arbitrary
expectation system: `π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, with
`ω̃_{−1} = w0` given. -/
def Constr (c : Coef) (dn : ℕ → Ω → ℝ) (w0 : Ω → ℝ) (y pp pw w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = c.β • 𝔼.E t (pp (t + 1)) + c.kapP • y t + c.lamP • w t ∧
    pw t = c.β • 𝔼.E t (pw (t + 1)) + c.kapW • y t - c.lamW • w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Galí (2015), §6.4, p. 181: an admissible plan: bounded adapted output gap, price and wage
inflation and real wage gap satisfying the constraints (18), (20), (21). -/
def Plan (c : Coef) (dn : ℕ → Ω → ℝ) (w0 : Ω → ℝ) (y pp pw w : ℕ → Ω → ℝ) : Prop :=
  Constr 𝔼 c dn w0 y pp pw w ∧ 𝔼.Adapted y ∧ 𝔼.Adapted pp ∧ 𝔼.Adapted pw ∧ 𝔼.Adapted w ∧
    BoundedProc y ∧ BoundedProc pp ∧ BoundedProc pw ∧ BoundedProc w

/-- Galí (2015), (30)–(33), p. 181: the first-order conditions of the commitment problem,
`a_y ỹ_t + κ_p ζ_{1,t} + κ_w ζ_{2,t} = 0`, `a_p π^p_t − Δζ_{1,t} + ζ_{3,t} = 0`,
`a_w π^w_t − Δζ_{2,t} − ζ_{3,t} = 0`, `λ_p ζ_{1,t} − λ_w ζ_{2,t} + ζ_{3,t} − β E_t ζ_{3,t+1} = 0`,
with `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOCs (c : Coef) (y pp pw z1 z2 z3 : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c.ay • y t + c.kapP • z1 t + c.kapW • z2 t = 0 ∧
    c.ap • pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw • pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP • z1 t - c.lamW • z2 t + z3 t - c.β • 𝔼.E t (z3 (t + 1)) = 0

/-- Galí (2015), (28), p. 179: the period loss `½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def periodLoss (c : Coef) (y pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (c.ay * y t ω ^ 2 + c.ap * pp t ω ^ 2 + c.aw * pw t ω ^ 2) / 2

/-- Galí (2015), (28), p. 179: the welfare loss `𝕎 = E_0 ∑ βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² +
a_w (π^w_t)²)` (a date-0 random variable). -/
noncomputable def expLoss (c : Coef) (y pp pw : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, c.β ^ t * periodLoss c y pp pw t ω)

/-- Galí (2015), (28), p. 179: the period loss of the deviations of one plan from another. -/
noncomputable def devLoss (c : Coef) (y pp pw ys pps pws : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (c.ay * (y t ω - ys t ω) ^ 2 + c.ap * (pp t ω - pps t ω) ^ 2 +
    c.aw * (pw t ω - pws t ω) ^ 2) / 2

/-- Galí (2015), p. 181: the date-`t` Lagrangian cross term
`ζ_{1,t−1} dπ^p_t + ζ_{2,t−1} dπ^w_t + dω̃_{t−1} ζ_{3,t}`. -/
def cross (y0 : Ω → ℝ) (pp pw w pps pws ws z1 z2 z3 : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  prev 0 z1 t * (pp t - pps t) + prev 0 z2 t * (pw t - pws t) +
    (prev y0 w t - prev y0 ws t) * z3 t

/-- Galí (2015), p. 181: `E_t` of a nonnegative random variable is nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

/-- Galí (2015), (28), p. 179: for a bounded plan the welfare loss is the genuine infinite sum
`∑ βᵗ E_0 ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)` (`E_0` commutes with the geometrically
dominated series). -/
theorem expLoss_hasSum {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1) (hay : 0 ≤ c.ay)
    (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {y pp pw : ℕ → Ω → ℝ} (hy : BoundedProc y)
    (hpp : BoundedProc pp) (hpw : BoundedProc pw) (ω : Ω) :
    HasSum (fun t => c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω) (expLoss 𝔼 c y pp pw ω) := by
  obtain ⟨A, hA⟩ := hy
  obtain ⟨B, hB⟩ := hpp
  obtain ⟨C, hC⟩ := hpw
  set K := (c.ay * A ^ 2 + c.ap * B ^ 2 + c.aw * C ^ 2) / 2 with hK
  have hpl : ∀ t ω, |periodLoss c y pp pw t ω| ≤ K := by
    intro t ω
    have h1 : y t ω ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t ω) 2
    have h2 : pp t ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t ω) 2
    have h3 : pw t ω ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC t ω) 2
    unfold periodLoss
    rw [abs_of_nonneg (by positivity), hK]
    have := mul_le_mul_of_nonneg_left h1 hay
    have := mul_le_mul_of_nonneg_left h2 hap
    have := mul_le_mul_of_nonneg_left h3 haw
    linarith
  have hf : ∀ k ω, |c.β ^ k * periodLoss c y pp pw k ω| ≤ c.β ^ k * K := by
    intro k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hpl k ω) (pow_nonneg hβ0 k)
  have hE : 𝔼.E 0 (fun ω' => ∑' k, c.β ^ k * periodLoss c y pp pw k ω') ω =
      ∑' k, 𝔼.E 0 (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') ω := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') ω =
      c.β ^ k * 𝔼.E 0 (periodLoss c y pp pw k) ω := fun k => by
    have : (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') = c.β ^ k • periodLoss c y pp pw k :=
      rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hpl k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, c.β ^ k * periodLoss c y pp pw k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-- **Galí (2015), (30)–(33), p. 181 (the Lagrangian identity, one period, state by state)**: for
a plan satisfying the first-order conditions and any other solution of the constraints,
`ℓ_t − ℓ*_t = ½ Q(d_t) + β (ζ_{1,t} E_t dπ^p_{t+1} + ζ_{2,t} E_t dπ^w_{t+1} +
dω̃_t E_t ζ_{3,t+1}) − (cross term at t)`. -/
theorem period_identity {c : Coef} {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hc : Constr 𝔼 c dn w0 y pp pw w) (hcs : Constr 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (t : ℕ) :
    periodLoss c y pp pw t - periodLoss c ys pps pws t =
      devLoss c y pp pw ys pps pws t +
        c.β • (z1 t * (𝔼.E t (pp (t + 1)) - 𝔼.E t (pps (t + 1))) +
          z2 t * (𝔼.E t (pw (t + 1)) - 𝔼.E t (pws (t + 1))) +
            (w t - ws t) * 𝔼.E t (z3 (t + 1))) -
        cross w0 pp pw w pps pws ws z1 z2 z3 t := by
  funext ω
  have c1 := congrFun (hc t).1 ω
  have c2 := congrFun (hc t).2.1 ω
  have c3 := congrFun (hc t).2.2 ω
  have c1s := congrFun (hcs t).1 ω
  have c2s := congrFun (hcs t).2.1 ω
  have c3s := congrFun (hcs t).2.2 ω
  have f1 := congrFun (hfoc t).1 ω
  have f2 := congrFun (hfoc t).2.1 ω
  have f3 := congrFun (hfoc t).2.2.1 ω
  have f4 := congrFun (hfoc t).2.2.2 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at c1 c2 c3 c1s c2s c3s f1 f2 f3 f4
  simp only [periodLoss, devLoss, cross, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.mul_apply]
  exact lagrangian_alg c c1 c2 c3 c1s c2s c3s f1 f2 f3 f4

/-- **Galí (2015), p. 181 (the Lagrangian identity under `E_0`)**: with the law of iterated
expectations and the pull-out property, the expected excess period loss is
`E_0 ½ Q(d_t) + β E_0 (cross term at t + 1) − E_0 (cross term at t)`. -/
theorem E0_identity (hpo : 𝔼.PullOut) {c : Coef} {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hc : Constr 𝔼 c dn w0 y pp pw w) (hcs : Constr 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hwa : 𝔼.Adapted w) (hwsa : 𝔼.Adapted ws)
    (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (periodLoss c y pp pw t) ω - 𝔼.E 0 (periodLoss c ys pps pws t) ω =
      𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω +
        c.β * 𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 (t + 1)) ω -
          𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 t) ω := by
  have hdw : 𝔼.E t (w t - ws t) = w t - ws t := by rw [map_sub, hwa t, hwsa t]
  have hpull : z1 t * (𝔼.E t (pp (t + 1)) - 𝔼.E t (pps (t + 1))) +
      z2 t * (𝔼.E t (pw (t + 1)) - 𝔼.E t (pws (t + 1))) + (w t - ws t) * 𝔼.E t (z3 (t + 1)) =
      𝔼.E t (cross w0 pp pw w pps pws ws z1 z2 z3 (t + 1)) := by
    rw [← map_sub, ← map_sub, ← hpo t _ _ (hz1 t), ← hpo t _ _ (hz2 t), ← hpo t _ _ hdw,
      ← map_add, ← map_add]
    rfl
  have h := congrArg (fun f => 𝔼.E 0 f ω) (period_identity 𝔼 hc hcs hfoc t)
  simp only [map_sub, map_add, map_smul, hpull, 𝔼.tower (Nat.zero_le t), Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- Galí (2015), p. 181: `E_0` of the deviation loss is nonnegative (nonnegative weights). -/
theorem E0_devLoss_nonneg {c : Coef} (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw)
    (y pp pw ys pps pws : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω :=
  E_nonneg 𝔼 (fun ω => by unfold devLoss; positivity) 0 ω

/-- **Galí (2015), §6.4, p. 181 (sufficiency of the first-order conditions, stochastic)**: if a
plan satisfies (30)–(33) with bounded multipliers, `ζ₁, ζ₂` adapted, then for every other plan the
excess welfare loss is the genuine infinite sum
`𝕎 − 𝕎* = ∑ βᵗ E_0 ½ (a_y (ỹ_t − ỹ*_t)² + a_p (π^p_t − π^p*_t)² + a_w (π^w_t − π^w*_t)²)`. -/
theorem expLoss_sub_hasSum (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1)
    (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω) :
    HasSum (fun t => c.β ^ t * 𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω)
      (expLoss 𝔼 c y pp pw ω - expLoss 𝔼 c ys pps pws ω) := by
  obtain ⟨hc, -, -, -, hwa, hyb, hppb, hpwb, ⟨Mw, hMw⟩⟩ := hp
  obtain ⟨hcs, -, -, -, hwsa, hysb, hppsb, hpwsb, ⟨Mws, hMws⟩⟩ := hps
  obtain ⟨Bp, hBp⟩ := hppb
  obtain ⟨Bq, hBq⟩ := hpwb
  obtain ⟨Bps, hBps⟩ := hppsb
  obtain ⟨Bqs, hBqs⟩ := hpwsb
  obtain ⟨Z1, hZ1⟩ := hb1
  obtain ⟨Z2, hZ2⟩ := hb2
  obtain ⟨Z3, hZ3⟩ := hb3
  have hZ10 : 0 ≤ Z1 := (abs_nonneg _).trans (hZ1 0 ω)
  have hZ20 : 0 ≤ Z2 := (abs_nonneg _).trans (hZ2 0 ω)
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ω)
  have hMws0 : 0 ≤ Mws := (abs_nonneg _).trans (hMws 0 ω)
  set K := Z1 * (Bp + Bps) + Z2 * (Bq + Bqs) + (Mw + Mws) * Z3 with hK
  have hH : ∀ t ω, |cross w0 pp pw w pps pws ws z1 z2 z3 t ω| ≤ K := by
    intro t ω
    have hz1 : |prev 0 z1 t ω| ≤ Z1 := by cases t <;> simp [hZ10, hZ1 _ ω]
    have hz2 : |prev 0 z2 t ω| ≤ Z2 := by cases t <;> simp [hZ20, hZ2 _ ω]
    have hdw : |prev w0 w t ω - prev w0 ws t ω| ≤ Mw + Mws := by
      cases t with
      | zero => simpa using add_nonneg hMw0 hMws0
      | succ t => exact (abs_sub _ _).trans (add_le_add (hMw t ω) (hMws t ω))
    have e1 : |prev 0 z1 t ω * (pp t ω - pps t ω)| ≤ Z1 * (Bp + Bps) := by
      rw [abs_mul]
      exact mul_le_mul hz1 ((abs_sub _ _).trans (add_le_add (hBp t ω) (hBps t ω)))
        (abs_nonneg _) hZ10
    have e2 : |prev 0 z2 t ω * (pw t ω - pws t ω)| ≤ Z2 * (Bq + Bqs) := by
      rw [abs_mul]
      exact mul_le_mul hz2 ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBqs t ω)))
        (abs_nonneg _) hZ20
    have e3 : |(prev w0 w t ω - prev w0 ws t ω) * z3 t ω| ≤ (Mw + Mws) * Z3 := by
      rw [abs_mul]
      exact mul_le_mul hdw (hZ3 t ω) (abs_nonneg _) (by positivity)
    simp only [cross, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    exact (abs_add_three _ _ _).trans (by rw [hK]; linarith)
  refine hasSum_of_telescope
    ((expLoss_hasSum 𝔼 hβ0 hβ1 hay hap haw hyb ⟨Bp, hBp⟩ ⟨Bq, hBq⟩ ω).sub
      (expLoss_hasSum 𝔼 hβ0 hβ1 hay hap haw hysb ⟨Bps, hBps⟩ ⟨Bqs, hBqs⟩ ω))
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_devLoss_nonneg 𝔼 hay hap haw _ _ _ _ _ _ t ω))
    (h := fun t => c.β ^ t * 𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 t) ω)
    (fun t => ?_) ?_ ?_
  · rw [← mul_sub, E0_identity 𝔼 hpo hc hcs hfoc hwa hwsa hz1 hz2 t ω, pow_succ]
    ring
  · have : cross w0 pp pw w pps pws ws z1 z2 z3 0 = 0 := by
      funext ω; simp [cross]
    simp [this]
  · refine squeeze_zero_norm (a := fun t => c.β ^ t * K) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hH t) 0 ω) (pow_nonneg hβ0 t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K

/-- **Galí (2015), §6.4, p. 181 (optimality, stochastic)**: a plan satisfying the first-order
conditions (30)–(33) with bounded multipliers (`ζ₁, ζ₂` adapted) has the smallest welfare loss
among all plans, state by state. -/
theorem expLoss_le_of_foc (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1)
    (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω) :
    expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω :=
  sub_nonneg.1 ((expLoss_sub_hasSum 𝔼 hpo hβ0 hβ1 hay hap haw hp hps hfoc hz1 hz2 hb1 hb2 hb3
    ω).nonneg (fun t => mul_nonneg (pow_nonneg hβ0 t)
      (E0_devLoss_nonneg 𝔼 hay hap haw _ _ _ _ _ _ t ω)))

/-- **Galí (2015), §6.4, p. 181 (uniqueness of the optimum, stochastic)**: a plan attaining at
`ω` the same welfare loss as a plan satisfying (30)–(33) with bounded multipliers coincides with
it in conditional mean square: `E_0 (ỹ_t − ỹ*_t)² = E_0 (π^p_t − π^p*_t)² =
E_0 (π^w_t − π^w*_t)² = 0` at `ω` for every `t` (under perfect foresight: equal paths). -/
theorem eq_of_expLoss_eq (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω)
    (heq : expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 ∧
        𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0 := by
  have hs := expLoss_sub_hasSum 𝔼 hpo hβ0.le hβ1 hay.le hap.le haw.le hp hps hfoc hz1 hz2 hb1
    hb2 hb3 ω
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E0_devLoss_nonneg 𝔼 hay.le hap.le haw.le _ _ _ _ _ _ t ω))).1 hs
  have ht := congrFun hz t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  have hsplit : devLoss c y pp pw ys pps pws t =
      (1 / 2 : ℝ) • (c.ay • (fun ω => (y t ω - ys t ω) ^ 2) +
        c.ap • (fun ω => (pp t ω - pps t ω) ^ 2) + c.aw • (fun ω => (pw t ω - pws t ω) ^ 2)) := by
    funext ω; simp only [devLoss, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  rw [hsplit, map_smul, map_add, map_add, map_smul, map_smul, map_smul] at ht
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
  have h1 := E_nonneg 𝔼 (f := fun ω => (y t ω - ys t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E_nonneg 𝔼 (f := fun ω => (pp t ω - pps t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h3 := E_nonneg 𝔼 (f := fun ω => (pw t ω - pws t ω) ^ 2) (fun ω => by positivity) 0 ω
  have k1 := mul_nonneg hay.le h1
  have k2 := mul_nonneg hap.le h2
  have k3 := mul_nonneg haw.le h3
  refine ⟨?_, ?_, ?_⟩
  · have : c.ay * 𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hay.ne'
  · have : c.ap * 𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hap.ne'
  · have : c.aw * 𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left haw.ne'

/-- **Galí (2015), §6.4, p. 181 (THE OPTIMAL POLICY UNDER COMMITMENT, stochastic)**: a plan
satisfying the first-order conditions (30)–(33) with `ζ_{1,−1} = ζ_{2,−1} = 0` and bounded
multipliers (`ζ₁, ζ₂` adapted) minimises the welfare loss (28) among all bounded adapted plans,
state by state; any plan with the same loss at `ω` coincides with it in conditional mean square.
Requires the pull-out property (true for perfect foresight and every finite event tree). -/
theorem commitment_optimal (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ} (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) :
    ∀ y pp pw w, Plan 𝔼 c dn w0 y pp pw w → ∀ ω,
      expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω → ∀ t,
          𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 ∧
            𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 ∧
              𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0) :=
  fun _ _ _ _ hp ω => ⟨expLoss_le_of_foc 𝔼 hpo hβ0.le hβ1 hay.le hap.le haw.le hp hps hfoc hz1
    hz2 hb1 hb2 hb3 ω, fun heq t => eq_of_expLoss_eq 𝔼 hpo hβ0 hβ1 hay hap haw hp hps hfoc hz1
      hz2 hb1 hb2 hb3 ω heq t⟩

end Stoch

/-! ### The matrix form (Appendix 6.2) -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Appendix 6.2, p. 192: the matrix `A₀*`. -/
def A0 (c : Coef) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![-c.kapP, 1, 0, 0, 0, 0, 0;
     -c.kapW, 0, 1, 0, 0, 0, 0;
     0, -1, 1, 1, 0, 0, 0;
     c.ay, 0, 0, 0, 0, 0, 0;
     0, c.ap, 0, 0, 1, 0, 1;
     0, 0, c.aw, 0, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1]

/-- Galí (2015), Appendix 6.2, p. 192: the matrix `A₁*`. -/
def A1 (c : Coef) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, c.β, 0, c.lamP, 0, 0, 0;
     0, 0, c.β, -c.lamW, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, -c.kapP, -c.kapW, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, -c.lamP, c.lamW, c.β]

/-- Galí (2015), Appendix 6.2, p. 192: the vector `B₀* = (0, 0, ψ_wa, 0, 0, 0, 0)'`. -/
def B0 (ψ : ℝ) : Fin 7 → ℝ := ![0, 0, ψ, 0, 0, 0, 0]

/-- Galí (2015), p. 181: the state vector
`x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1}, ζ_{1,t−1}, ζ_{2,t−1}, ζ_{3,t})`. -/
def stateVec (w0 : Ω → ℝ) (y pp pw w z1 z2 z3 : ℕ → Ω → ℝ) (t : ℕ) : Fin 7 → Ω → ℝ :=
  ![y t, pp t, pw t, prev w0 w t, prev 0 z1 t, prev 0 z2 t, z3 t]

/-- Galí (2015), p. 181: the dynamical system `A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t`. -/
def MatrixSystem (c : Coef) (ψ : ℝ) (da : ℕ → Ω → ℝ) (x : ℕ → Fin 7 → Ω → ℝ) : Prop :=
  ∀ t i, ∑ j, A0 c i j • x t j = ∑ j, A1 c i j • 𝔼.E t (x (t + 1) j) + B0 ψ i • da t

/-- **Galí (2015), p. 181 and Appendix 6.2, p. 192 (the matrix form)**: with `Δωⁿ_t = ψ_wa Δa_t`
and `ω̃, ζ₁, ζ₂` adapted, the constraints (18), (20), (21) together with the first-order conditions
(30)–(33) hold at every date iff the state vector `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1},
ζ_{1,t−1}, ζ_{2,t−1}, ζ_{3,t})` (with `ζ_{1,−1} = ζ_{2,−1} = 0`) solves
`A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t` with the matrices printed in Appendix 6.2 (all seven rows
check). -/
theorem matrix_form_iff (c : Coef) (ψ : ℝ) (da : ℕ → Ω → ℝ) (w0 : Ω → ℝ)
    {y pp pw w z1 z2 z3 : ℕ → Ω → ℝ}
    (hwa : 𝔼.Adapted w) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2) :
    (Constr 𝔼 c (fun t => ψ • da t) w0 y pp pw w ∧ FOCs 𝔼 c y pp pw z1 z2 z3) ↔
      MatrixSystem 𝔼 c ψ da (stateVec w0 y pp pw w z1 z2 z3) := by
  simp only [MatrixSystem, stateVec, Constr, FOCs, ← forall_and]
  refine forall_congr' fun t => ?_
  simp only [funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply,
    A0, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_seven,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, A1, prev_succ,
    hwa t, hz1 t, hz2 t, B0, Fin.forall_fin_succ, neg_mul, one_mul, zero_mul, add_zero, zero_add,
    Matrix.cons_val_succ, forall_const]
  constructor
  · rintro ⟨⟨e1, e2, e3⟩, f1, f2, f3, f4⟩
    exact ⟨fun x => by linarith [e1 x], fun x => by linarith [e2 x], fun x => by linarith [e3 x],
      fun x => by linarith [f1 x], fun x => by linarith [f2 x], fun x => by linarith [f3 x],
      fun x => by linarith [f4 x]⟩
  · rintro ⟨r1, r2, r3, r4, r5, r6, r7⟩
    exact ⟨⟨fun x => by linarith [r1 x], fun x => by linarith [r2 x], fun x => by linarith [r3 x]⟩,
      fun x => by linarith [r4 x], fun x => by linarith [r5 x], fun x => by linarith [r6 x],
      fun x => by linarith [r7 x]⟩

end Stoch

/-! ### §6.4.1: demand shocks -/

namespace Det

/-- **Galí (2015), §6.4.1, p. 181 (demand shocks, deterministic)**: with demand shocks only the
natural real wage does not move (`Δωⁿ ≡ 0`, since `ωⁿ` depends on technology only, (16)); then,
starting from `ω̃_{−1} = 0`, the zero path (`x_t = 0` for all `t`) is the unique solution of the
commitment problem: it is feasible with zero loss, every loss is nonnegative, and it satisfies
(30)–(33) with zero multipliers. -/
theorem demand_zero_optimal {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) :
    IsOptimal c 0 0 0 0 0 0 ∧ loss c 0 0 0 = 0 ∧
      ∀ y pp pw w, IsOptimal c 0 0 y pp pw w ↔ y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 := by
  have hf : Feasible c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hl : FiniteLoss c 0 0 0 := by
    have : lossTerm c 0 0 0 = 0 := by funext t; simp [lossTerm]
    rw [FiniteLoss, this]; exact summable_zero
  have hξ : FOC c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hZ : BoundedMult (0 : ℕ → ℝ) 0 0 := ⟨0, fun t => by simp⟩
  refine ⟨isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl hξ hZ, by simp [loss, lossTerm],
    fun y pp pw w => ⟨fun h => ?_, ?_⟩⟩
  · exact (isOptimal_iff_foc hβ0 hβ1 hay hap haw hf hl hξ hZ h.1 h.2.1).2.1 h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl hξ hZ

end Det

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (28), p. 179: the welfare loss is nonnegative (nonnegative weights). -/
theorem expLoss_nonneg {c : Coef} (hβ0 : 0 ≤ c.β) (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap)
    (haw : 0 ≤ c.aw) (y pp pw : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ expLoss 𝔼 c y pp pw ω :=
  E_nonneg 𝔼 (fun ω => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (by unfold periodLoss; positivity)) 0 ω

/-- Galí (2015), §6.4.1, p. 181: the zero allocation has zero welfare loss. -/
theorem expLoss_zero (c : Coef) : expLoss 𝔼 c 0 0 0 = 0 := by
  have : (fun ω => ∑' t, c.β ^ t * periodLoss c (0 : ℕ → Ω → ℝ) 0 0 t ω) = 0 := by
    funext ω; simp [periodLoss]
  rw [expLoss, this, map_zero]

/-- Galí (2015), §6.4.1, p. 181: with `Δωⁿ ≡ 0` and `ω̃_{−1} = 0` the zero allocation is a plan. -/
theorem zero_plan (c : Coef) : Plan 𝔼 c 0 0 0 0 0 0 := by
  refine ⟨fun t => ?_, fun t => map_zero _, fun t => map_zero _, fun t => map_zero _,
    fun t => map_zero _, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩,
    ⟨0, fun t ω => by simp⟩⟩
  cases t <;> simp

/-- **Galí (2015), §6.4.1, p. 181 (demand shocks, stochastic)**: when demand shocks are the only
source of fluctuations (`Δωⁿ ≡ 0`) and `ω̃_{−1} = 0`, the zero allocation is optimal: it is a plan
with zero loss and every plan has a nonnegative loss; it satisfies (30)–(33) with zero multipliers,
and any plan with the same loss at `ω` has `E_0 ỹ_t² = E_0 (π^p_t)² = E_0 (π^w_t)² = 0` there. -/
theorem demand_zero_optimal (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) :
    Plan 𝔼 c 0 0 0 0 0 0 ∧ FOCs 𝔼 c 0 0 0 0 0 0 ∧ expLoss 𝔼 c 0 0 0 = 0 ∧
      ∀ y pp pw w, Plan 𝔼 c 0 0 y pp pw w → ∀ ω, 0 ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = 0 → ∀ t, 𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 ∧
          𝔼.E 0 (fun ω => pp t ω ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => pw t ω ^ 2) ω = 0) := by
  have hfoc : FOCs 𝔼 c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun t ω => by simp⟩
  have ha : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
  refine ⟨zero_plan 𝔼 c, hfoc, expLoss_zero 𝔼 c, fun y pp pw w hp ω =>
    ⟨expLoss_nonneg 𝔼 hβ0.le hay.le hap.le haw.le y pp pw ω, fun h0 t => ?_⟩⟩
  have h := (commitment_optimal 𝔼 hpo hβ0 hβ1 hay hap haw (zero_plan 𝔼 c) hfoc ha ha hb hb hb
    y pp pw w hp ω).2 (by rw [h0, expLoss_zero]; rfl) t
  simpa using h

/-! ### §6.4.1: implementation by an interest-rate rule -/

/-- Galí (2015), (22), p. 173: the dynamic IS equation in gaps,
`ỹ_t = −(1/σ)(i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (rn i y pp : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = -(1 / σ) • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (y (t + 1))

/-- Galí (2015), §6.4.1, p. 182: an equilibrium under the rule `i_t = rⁿ_t + φ_p π^p_t` with demand
shocks only (`Δωⁿ ≡ 0`) and `ω̃_{−1} = 0`: the DIS (22), the rule, and a plan (bounded adapted
solution of (18), (20), (21)). -/
def RuleEqm (c : Coef) (σ φp : ℝ) (rn y pp pw w i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ rn i y pp ∧ (∀ t, i t = rn t + φp • pp t) ∧ Plan 𝔼 c 0 0 y pp pw w

/-- Galí (2015), §6.4.1, p. 182 (and p. 174 with `φ_w = φ_y = 0`): the rule is determinate: the
only bounded adapted solution of `σ ỹ_t = σ E_t ỹ_{t+1} − φ_p π^p_t + E_t π^p_{t+1}`, (18), (20),
(21) with `Δωⁿ ≡ 0` and `ω̃_{−1} = 0` is zero. -/
def RuleDeterminate (c : Coef) (σ φp : ℝ) : Prop :=
  ∀ y pp pw w : ℕ → Ω → ℝ,
    (∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1))) →
      Plan 𝔼 c 0 0 y pp pw w → y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0

/-- **Galí (2015), §6.4.1, p. 182 (implementation)**: under demand shocks the rule
`i_t = rⁿ_t + φ_p π^p_t` supports the optimal (zero) allocation with `i_t = rⁿ_t`; if the rule is
determinate, this is the only equilibrium. (Determinacy holds for `φ_p > 1` when `κ_p = κ_w`,
`ruleDeterminate_of_kap_eq`, and for general parameters with `φ_p > 1` by
`ruleDeterminate_of_phiP` / `ruleDeterminate_book`; the unconditional statement is
`rule_implements_book`.) -/
theorem rule_implements {c : Coef} {σ φp : ℝ} (hσ : 0 < σ) (rn : ℕ → Ω → ℝ) :
    RuleEqm 𝔼 c σ φp rn 0 0 0 0 rn ∧
      (RuleDeterminate 𝔼 c σ φp → ∀ y pp pw w i, RuleEqm 𝔼 c σ φp rn y pp pw w i →
        y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ i = rn) := by
  refine ⟨⟨fun t => ?_, fun t => by simp, zero_plan 𝔼 c⟩, fun hdet y pp pw w i h => ?_⟩
  · simp
  obtain ⟨hdis, hrule, hp⟩ := h
  have hs : ∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1)) := by
    intro t
    funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    field_simp at h1
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := hdet y pp pw w hs hp
  refine ⟨h1, h2, h3, h4, funext fun t => ?_⟩
  rw [hrule t, h2]
  simp

end Stoch

/-! ### The relative-inflation block and determinacy when `κ_p = κ_w` -/

/-- Galí (2015), Note N6.1 (survey): the characteristic polynomial
`β r² − (1 + β + k) r + 1` of the relative-inflation block has a root in `(0, 1)` for `k > 0`
(it is `1` at `r = 0` and `−k` at `r = 1`). -/
theorem exists_block_root {β k : ℝ} (hk : 0 < k) :
    ∃ r, 0 < r ∧ r < 1 ∧ β * r ^ 2 - (1 + β + k) * r + 1 = 0 := by
  have hcont : Continuous (fun r : ℝ => β * r ^ 2 - (1 + β + k) * r + 1) := by fun_prop
  have h := intermediate_value_Ioo' (zero_le_one' ℝ) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (β * 1 ^ 2 - (1 + β + k) * 1 + 1) (β * 0 ^ 2 - (1 + β + k) * 0 + 1) by
      constructor <;> nlinarith)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), Note N6.1 (survey) (the relative-inflation block is determinate)**: with
`0 < β < 1` and `k > 0`, the only bounded adapted solution of `D_t = β E_t D_{t+1} − k ω̃_t`,
`ω̃_t = ω̃_{t−1} + D_t`, `ω̃_{−1} = 0` is zero. Proof: for the root `r ∈ (0, 1)` of
`β r² − (1 + β + k) r + 1`, `v_t = ω̃_t − r ω̃_{t−1}` solves `v_t = β r E_t v_{t+1}`, so `v = 0`,
and then `ω̃_t = r ω̃_{t−1}` with `ω̃_{−1} = 0`. -/
theorem block_zero {β k : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hk : 0 < k) {D w : ℕ → Ω → ℝ}
    (hwa : 𝔼.Adapted w) (hwb : BoundedProc w)
    (h1 : ∀ t, D t = β • 𝔼.E t (D (t + 1)) - k • w t) (h2 : ∀ t, w t = prev 0 w t + D t) :
    D = 0 ∧ w = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := β) hk
  set v : ℕ → Ω → ℝ := fun t => w t - r • prev 0 w t with hv_def
  have hv : ∀ t, v t = (β * r) • 𝔼.E t (v (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t
    have hED : 𝔼.E t (D (t + 1)) = 𝔼.E t (w (t + 1)) - w t := by
      have := congrArg (𝔼.E t) (h2 (t + 1))
      rw [map_add, prev_succ, hwa t] at this
      rw [this]; abel
    have hEv : 𝔼.E t (v (t + 1)) = 𝔼.E t (w (t + 1)) - r • w t := by
      simp only [hv_def, prev_succ, map_sub, map_smul, hwa t]
    funext ω
    have a := congrFun (h1 t) ω
    have b := congrFun (h2 t) ω
    have c := congrFun hED ω
    have d := congrFun hEv ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c d
    simp only [hv_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      add_zero]
    rw [d]
    rw [c] at a
    linear_combination r * a + r * b + (w t ω) * hr
  obtain ⟨Mw, hMw⟩ := hwb
  have hvb : BoundedProc v := ⟨Mw + |r| * Mw, fun t ω => by
    have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ω)
    have hp : |prev 0 w t ω| ≤ Mw := by cases t <;> simp [hMw0, hMw _ ω]
    simp only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hMw t ω) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg r)⟩
  have hβr : |β * r| < 1 := by
    rw [abs_of_pos (mul_pos hβ0 hr0)]; nlinarith
  have hzero : ∀ t, (0 : ℕ → Ω → ℝ) t = (β * r) • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) +
      (0 : ℕ → Ω → ℝ) t := fun t => by simp
  have hv0 := 𝔼.forward_unique hβr hv hzero hvb ⟨0, fun t ω => by simp⟩
  have hw : ∀ t, w t = 0 := by
    intro t
    induction t with
    | zero =>
      have := congrFun hv0 0
      simpa [hv_def] using this
    | succ t ih =>
      have := congrFun hv0 (t + 1)
      simp only [hv_def, prev_succ, ih, smul_zero, sub_zero, Pi.zero_apply] at this
      exact this
  refine ⟨funext fun t => ?_, funext hw⟩
  have := h2 t
  rw [hw t] at this
  cases t with
  | zero => simpa using this.symm
  | succ t => simpa [hw t] using this.symm

end Stoch

/-- Galí (2015), §6.4.1, p. 182 (with `κ_p = κ_w = κ`, once `ω̃ ≡ 0` and `π^w = π^p`): the
coefficient matrix of `(ỹ_t, π^p_t) = A E_t (ỹ_{t+1}, π^p_{t+1})` under the rule
`i_t = rⁿ_t + φ_p π^p_t`, `A = (σ + κφ_p)⁻¹ [[σ, 1 − βφ_p], [κσ, κ + βσ]]` (as in Chapter 3). -/
noncomputable def ruleA (σ κ β φp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φp), (1 - β * φp) / (σ + κ * φp);
     κ * σ / (σ + κ * φp), (κ + β * σ) / (σ + κ * φp)]

/-- Galí (2015), p. 182 (as in Chapter 3): `det A = βσ/(σ + κφ_p)`. -/
theorem det2_ruleA {σ κ β φp : ℝ} (hΩ : 0 < σ + κ * φp) :
    det2 (ruleA σ κ β φp) = β * σ / (σ + κ * φp) := by
  simp only [det2, ruleA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
  field_simp
  ring

/-- Galí (2015), p. 182 (as in Chapter 3): `tr A = (σ + κ + βσ)/(σ + κφ_p)`. -/
theorem tr2_ruleA (σ κ β φp : ℝ) :
    tr2 (ruleA σ κ β φp) = (σ + κ + β * σ) / (σ + κ * φp) := by
  simp only [tr2, ruleA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
  ring

/-- **Galí (2015), p. 182 (the Taylor principle for the composite system)**: for `σ, κ > 0`,
`0 < β < 1`, `φ_p ≥ 0`, both eigenvalues of `A` lie inside the unit circle iff `φ_p > 1`. -/
theorem schur_ruleA_iff {σ κ β φp : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 ≤ φp) : SchurStable (tr2 (ruleA σ κ β φp)) (det2 (ruleA σ κ β φp)) ↔ 1 < φp := by
  have hΩ : 0 < σ + κ * φp := by positivity
  rw [tr2_ruleA, det2_ruleA hΩ, SchurStable]
  have hd : 0 < β * σ / (σ + κ * φp) := by positivity
  have hd1 : β * σ / (σ + κ * φp) < 1 := by
    rw [div_lt_one hΩ]; nlinarith [mul_nonneg hκ.le hφ]
  have ht : 0 < (σ + κ + β * σ) / (σ + κ * φp) := by positivity
  rw [abs_of_pos hd, abs_of_pos ht, one_add_div hΩ.ne', div_lt_div_iff_of_pos_right hΩ]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact ⟨hd1, by nlinarith⟩

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 182: the stacked vector `(ỹ_t, π^p_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- Galí (2015), p. 182: with `κ_p = κ_w = κ`, `ω̃ ≡ 0`, `π^w = π^p`, the DIS under the rule and
(18) are equivalent to `(ỹ_t, π^p_t) = A E_t (ỹ_{t+1}, π^p_{t+1})`. -/
theorem solves_ruleA_iff {σ κ β φp : ℝ} (hΩ : 0 < σ + κ * φp) (y pp : ℕ → Ω → ℝ) :
    ((∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1))) ∧
      ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κ • y t) ↔
      𝔼.Solves (ruleA σ κ β φp) 0 (stack y pp) := by
  have hΩ' := hΩ.ne'
  constructor
  · rintro ⟨h1, h2⟩ t i
    funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (h2 t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases i
    · simp only [stack, ruleA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      field_simp
      linear_combination e1 - φp * e2
    · simp only [stack, ruleA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      field_simp
      linear_combination (σ + κ * φp) * e2 + κ * (e1 - φp * e2)
  · intro h
    have r : ∀ t ω, (σ + κ * φp) * y t ω =
          σ * 𝔼.E t (y (t + 1)) ω + (1 - β * φp) * 𝔼.E t (pp (t + 1)) ω ∧
        (σ + κ * φp) * pp t ω =
          κ * σ * 𝔼.E t (y (t + 1)) ω + (κ + β * σ) * 𝔼.E t (pp (t + 1)) ω := by
      intro t ω
      have r0 := congrFun (h t 0) ω
      have r1 := congrFun (h t 1) ω
      simp only [stack, ruleA, Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at r0 r1
      rw [r0, r1]
      constructor <;> field_simp
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · obtain ⟨r0, r1⟩ := r t ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine mul_left_cancel₀ hΩ' ?_
      linear_combination σ * r0 + φp * r1
    · obtain ⟨r0, r1⟩ := r t ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine mul_left_cancel₀ hΩ' ?_
      linear_combination r1 - κ * r0

/-- **Galí (2015), §6.4.1, p. 182 (determinacy of the implementing rule when `κ_p = κ_w`)**: with
`κ_p = κ_w = κ > 0`, `λ_p + λ_w > 0`, `σ > 0`, `0 < β < 1` and `φ_p > 1`, the rule
`i_t = rⁿ_t + φ_p π^p_t` is determinate. The system factors: `D = π^w − π^p` and `ω̃` form the
block `D_t = β E_t D_{t+1} − (λ_p + λ_w) ω̃_t`, `ω̃_t = ω̃_{t−1} + D_t` (`block_zero`), and then
`(ỹ, π^p)` solves the Chapter 3 system with the Taylor principle. -/
theorem ruleDeterminate_of_kap_eq {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hl : 0 < c.lamP + c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ)
    (hφ : 1 < φp) : RuleDeterminate 𝔼 c σ φp := by
  intro y pp pw w hs hp
  obtain ⟨hc, hya, hppa, -, hwa, ⟨My, hMy⟩, ⟨Mp, hMp⟩, -, hwb⟩ := hp
  set D : ℕ → Ω → ℝ := fun t => pw t - pp t with hD_def
  have h1 : ∀ t, D t = c.β • 𝔼.E t (D (t + 1)) - (c.lamP + c.lamW) • w t := by
    intro t
    funext ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    simp only [hD_def, map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk] at e1
    linarith
  have h2 : ∀ t, w t = prev 0 w t + D t := by
    intro t
    funext ω
    have e3 := congrFun (hc t).2.2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, sub_zero] at e3
    simp only [hD_def, Pi.add_apply, Pi.sub_apply]
    linarith
  obtain ⟨hD, hw⟩ := block_zero 𝔼 hβ0 hβ1 hl hwa hwb h1 h2
  have hpw : pw = pp := funext fun t => funext fun ω => by
    have := congrFun (congrFun hD t) ω
    simp only [hD_def, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  have h18 : ∀ t, pp t = c.β • 𝔼.E t (pp (t + 1)) + c.kapP • y t := by
    intro t
    have := (hc t).1
    rw [hw] at this
    simpa using this
  have hΩ : 0 < σ + c.kapP * φp := by positivity
  have hsol := (solves_ruleA_iff 𝔼 hΩ y pp).1 ⟨hs, h18⟩
  have hA := (schur_ruleA_iff hσ hκ hβ0 hβ1 (by linarith)).2 hφ
  have hzero : 𝔼.Solves (ruleA σ c.kapP c.β φp) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hA hsol hzero
    (fun t i => by fin_cases i <;> simp [stack, hya t, hppa t]) (fun t i => by simp)
    ⟨My + Mp, fun t i ω => by
      have := abs_nonneg (y t ω)
      have := abs_nonneg (pp t ω)
      fin_cases i
      · simp only [stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linarith [hMy t ω, hMp t ω]
      · simp only [stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith [hMy t ω, hMp t ω]⟩ ⟨0, fun t i ω => by simp⟩
  have hy : y = 0 := funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0
  have hpp : pp = 0 := funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1
  exact ⟨hy, hpp, hpw.trans hpp, hw⟩

/-- **Galí (2015), §6.4.1, p. 182 (indeterminacy for `φ_p ≤ 1` when `κ_p = κ_w`)**: with
`0 ≤ φ_p ≤ 1` the rule admits a nonzero bounded adapted equilibrium (with `ω̃ ≡ 0`,
`π^w = π^p`), built from a self-fulfilling solution of the Chapter 3 system. -/
theorem not_ruleDeterminate [Nonempty Ω] {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ) (hφ0 : 0 ≤ φp)
    (hφ1 : φp ≤ 1) : ¬ RuleDeterminate 𝔼 c σ φp := by
  intro hdet
  have hΩ : 0 < σ + c.kapP * φp := by positivity
  have hA : ¬ SchurStable (tr2 (ruleA σ c.kapP c.β φp)) (det2 (ruleA σ c.kapP c.β φp)) :=
    fun h => by linarith [(schur_ruleA_iff hσ hκ hβ0 hβ1 hφ0).1 h]
  obtain ⟨Y, hY, hYa, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hA (w := 0) (x := 0)
    (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  set y : ℕ → Ω → ℝ := fun t => Y t 0 with hy_def
  set pp : ℕ → Ω → ℝ := fun t => Y t 1 with hpp_def
  have hst : stack y pp = Y := by
    funext t i
    fin_cases i <;> rfl
  rw [← hst] at hY
  obtain ⟨h1, h2⟩ := (solves_ruleA_iff 𝔼 hΩ y pp).2 hY
  have hplan : Plan 𝔼 c 0 0 y pp pp 0 := by
    refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => hYa t 0, fun t => hYa t 1, fun t => hYa t 1,
      fun t => map_zero _, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩,
      ⟨M, fun t ω => hM t 1 ω⟩, ⟨0, fun t ω => by simp⟩⟩
    · simpa using h2 t
    · rw [← hk]; simpa using h2 t
    · cases t <;> simp
  obtain ⟨hy0, hpp0, -, -⟩ := hdet y pp pp 0 h1 hplan
  apply hne
  funext t i
  fin_cases i
  · exact congrFun hy0 t
  · exact congrFun hpp0 t

/-- **Galí (2015), §6.4.1, p. 182 (the implementing rule, `κ_p = κ_w`)**: the rule
`i_t = rⁿ_t + φ_p π^p_t` (`φ_p ≥ 0`) is determinate iff `φ_p > 1`. -/
theorem ruleDeterminate_iff [Nonempty Ω] {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hl : 0 < c.lamP + c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ)
    (hφ0 : 0 ≤ φp) : RuleDeterminate 𝔼 c σ φp ↔ 1 < φp := by
  constructor
  · intro h
    by_contra hc
    exact not_ruleDeterminate 𝔼 hk hκ hβ0 hβ1 hσ hφ0 (not_lt.1 hc) h
  · exact ruleDeterminate_of_kap_eq 𝔼 hk hκ hl hβ0 hβ1 hσ

end Stoch

/-! ### The implementing rule for general parameters (via `Determinacy4`) -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (24), p. 173, with `φ_w = φ_y = 0`: the parameters of system (24) under the rule
`i_t = rⁿ_t + φ_p π^p_t`, read off the policy-problem coefficients. -/
def rulePar (c : Coef) (σ φp : ℝ) : Determinacy4.Par :=
  ⟨c.β, σ, c.kapP, c.kapW, c.lamP, c.lamW, φp, 0, 0⟩

/-- Galí (2015), §6.4.1, p. 182: the rule system as system (24): a bounded adapted solution of
`σ ỹ_t = σ E_t ỹ_{t+1} − φ_p π^p_t + E_t π^p_{t+1}` (the DIS (22) after the `rⁿ` cancellation),
(18), (20), (21) with `Δωⁿ ≡ 0`, `ω̃_{−1} = 0` gives the solution
`x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` of (24) with zero forcing and zero initial condition. -/
theorem rule_isSol {c : Coef} {σ φp : ℝ} {y pp pw w : ℕ → Ω → ℝ}
    (hs : ∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1)))
    (hp : Plan 𝔼 c 0 0 y pp pw w) :
    Determinacy4.Dyn.IsSol 𝔼 (rulePar c σ φp) 0 0 (fun t => ![y t, pp t, pw t, prev 0 w t]) ∧
      Determinacy4.Fwd.VBounded (fun t => ![y t, pp t, pw t, prev 0 w t]) := by
  obtain ⟨hc, hya, hppa, hpwa, hwa, ⟨My, hMy⟩, ⟨Mp, hMp⟩, ⟨Mq, hMq⟩, ⟨Mw, hMw⟩⟩ := hp
  have hpa : ∀ t, 𝔼.E t (prev 0 w t) = prev 0 w t := by
    intro t
    cases t with
    | zero => exact map_zero _
    | succ t => simp only [prev_succ]; rw [← hwa t, 𝔼.known (Nat.le_succ t)]
  refine ⟨⟨fun t => ?_, rfl, fun t i => ?_, fun t => ?_⟩, ⟨My + Mp + Mq + Mw, fun t i ω => ?_⟩⟩
  · refine (Determinacy4.Dyn.eq24_iff 𝔼 (rulePar c σ φp)
      (fun t => ![y t, pp t, pw t, prev 0 w t]) 0 t).2 fun ω => ?_
    have e0 := congrFun (hs t) ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    have e3 := congrFun (hc t).2.2 ω
    have hw := congrFun (hwa t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      at e0 e1 e2 e3
    simp only [rulePar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue, prev_succ, hw, Pi.zero_apply]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · fin_cases i
    · exact hya t
    · exact hppa t
    · exact hpwa t
    · exact hpa t
  · simp only [Matrix.cons_val, Fin.isValue, prev_succ]
    exact hwa t
  · have h0 := (abs_nonneg (y t ω)).trans (hMy t ω)
    have h1 := (abs_nonneg (pp t ω)).trans (hMp t ω)
    have h2 := (abs_nonneg (pw t ω)).trans (hMq t ω)
    have h3 := (abs_nonneg (w t ω)).trans (hMw t ω)
    have hpw : |prev 0 w t ω| ≤ Mw := by cases t <;> simp [h3, hMw _ ω]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val]; linarith [hMy t ω]
    · simp only [Fin.mk_one, Matrix.cons_val]; linarith [hMp t ω]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]; linarith [hMq t ω]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]; linarith

/-- **Galí (2015), §6.4.1, p. 182 (determinacy of the implementing rule, general parameters)**:
with `0 < β < 1`, `σ > 0`, `κ_p, κ_w ≥ 0`, `λ_p, λ_w > 0`, `λ_w κ_p + λ_p κ_w > 0` and
`φ_p > 1`, the rule `i_t = rⁿ_t + φ_p π^p_t` is determinate. This is the `φ_w = φ_y = 0` case of
the p. 174 determinacy theorem (`Determinacy4.Dyn.determinate_of_pos`, whose condition reads
`φ_p > 1` here): the rule system is system (24) with zero forcing (`rule_isSol`), and zero is
its unique bounded solution. -/
theorem ruleDeterminate_of_phiP {c : Coef} {σ φp : ℝ} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hσ : 0 < σ) (hkp : 0 ≤ c.kapP) (hkw : 0 ≤ c.kapW) (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hΨ : 0 < c.lamW * c.kapP + c.lamP * c.kapW) (hφ : 1 < φp) : RuleDeterminate 𝔼 c σ φp := by
  intro y pp pw w hs hp
  have hP : (rulePar c σ φp).Adm :=
    ⟨hβ0, hβ1, hσ, hkp, hkw, hlp, hlw, show (0 : ℝ) ≤ φp by linarith, le_rfl, le_rfl⟩
  have hΨ' : 0 < (rulePar c σ φp).Ψ := hΨ
  have h1 : 0 < (rulePar c σ φp).qr 1 := by
    rw [Determinacy4.Par.qr_one_pos_iff hΨ']
    simpa [Determinacy4.Par.Lhs, rulePar] using hφ
  have hdet := Determinacy4.Dyn.determinate_of_pos 𝔼 hP hΨ' h1
  obtain ⟨x, -, huniq⟩ := hdet 0 0 ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
    ⟨0, fun ω => by simp⟩ (map_zero _)
  obtain ⟨hsol, hbd⟩ := rule_isSol 𝔼 hs hp
  have hz : Determinacy4.Dyn.IsSol 𝔼 (rulePar c σ φp) 0 0 (fun _ => ![0, 0, 0, 0]) ∧
      Determinacy4.Fwd.VBounded (fun (_ : ℕ) => (![0, 0, 0, 0] : Fin 4 → Ω → ℝ)) := by
    have := rule_isSol 𝔼 (y := 0) (pp := 0) (pw := 0) (w := 0) (c := c) (σ := σ) (φp := φp)
      (fun t => by simp) (zero_plan 𝔼 c)
    have hpz : ∀ t, prev (0 : Ω → ℝ) (0 : ℕ → Ω → ℝ) t = 0 := fun t => by cases t <;> rfl
    simpa [hpz] using this
  have heq := (huniq _ ⟨hsol, hbd⟩).trans (huniq _ hz).symm
  have hcomp : ∀ t (i : Fin 4), ![y t, pp t, pw t, prev 0 w t] i = (0 : Ω → ℝ) := fun t i => by
    have := congrFun (congrFun heq t) i
    fin_cases i <;> simpa using this
  refine ⟨funext fun t => hcomp t 0, funext fun t => hcomp t 1, funext fun t => hcomp t 2,
    funext fun t => ?_⟩
  simpa using hcomp (t + 1) 3

/-- **Galí (2015), §6.4.1, p. 182 (determinacy for the book's coefficients)**: with `0 < β < 1`,
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`, the rule `i_t = rⁿ_t + φ_p π^p_t` with `φ_p > 1`
is determinate for any `ε_p, ε_w` (the loss weights do not enter). -/
theorem ruleDeterminate_book {β σ φ α εp εw lamP lamW φp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hφp : 1 < φp) : RuleDeterminate 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp := by
  have h1α : 0 < 1 - α := by linarith
  have hkp : 0 ≤ (bookCoef β σ φ α εp εw lamP lamW).kapP := by
    simp only [bookCoef]; positivity
  have hkw : 0 < (bookCoef β σ φ α εp εw lamP lamW).kapW := by
    simp only [bookCoef]; positivity
  refine ruleDeterminate_of_phiP 𝔼 hβ0 hβ1 hσ hkp hkw.le hlp hlw ?_ hφp
  have : 0 ≤ (bookCoef β σ φ α εp εw lamP lamW).lamW *
      (bookCoef β σ φ α εp εw lamP lamW).kapP := mul_nonneg hlw.le hkp
  have : 0 < (bookCoef β σ φ α εp εw lamP lamW).lamP *
      (bookCoef β σ φ α εp εw lamP lamW).kapW := mul_pos hlp hkw
  linarith

/-- **Galí (2015), §6.4.1, p. 182 (implementation, unconditional)**: for the book's coefficients
(`0 < β < 1`, `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`) and `φ_p > 1`, under demand shocks
(`Δωⁿ ≡ 0`, `ω̃_{−1} = 0`) the rule `i_t = rⁿ_t + φ_p π^p_t` has the optimal zero allocation with
`i_t = rⁿ_t` as an equilibrium, and it is the only bounded adapted equilibrium. -/
theorem rule_implements_book {β σ φ α εp εw lamP lamW φp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hφp : 1 < φp) (rn : ℕ → Ω → ℝ) :
    RuleEqm 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp rn 0 0 0 0 rn ∧
      ∀ y pp pw w i, RuleEqm 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp rn y pp pw w i →
        y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ i = rn := by
  obtain ⟨h1, h2⟩ := rule_implements 𝔼 (c := bookCoef β σ φ α εp εw lamP lamW) (φp := φp) hσ rn
  exact ⟨h1, h2 (ruleDeterminate_book 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hφp)⟩

end Stoch

/-! ### Composite inflation, footnote 6 and (34)–(36) -/

/-- Galí (2015), fn. 6, p. 183, and (36), p. 184 (survey error 3): for the book's coefficients,
`λ_w κ_p + λ_p κ_w = λ_p λ_w (σ + (φ + α)/(1 − α))`. -/
theorem book_composite_slope {β σ φ α εp εw lamP lamW : ℝ} (hα : α ≠ 1) :
    (bookCoef β σ φ α εp εw lamP lamW).lamW * (bookCoef β σ φ α εp εw lamP lamW).kapP +
        (bookCoef β σ φ α εp εw lamP lamW).lamP * (bookCoef β σ φ α εp εw lamP lamW).kapW =
      lamP * lamW * (σ + (φ + α) / (1 - α)) := by
  have h : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  simp only [bookCoef]
  field_simp
  ring

/-- **Galí (2015), fn. 6, p. 183**: if `κ_p = κ_w ≡ κ` then
`κ = λ_p λ_w/(λ_p + λ_w) · (σ + (φ + α)/(1 − α))`. -/
theorem book_fn6 {β σ φ α εp εw lamP lamW : ℝ} (hα : α ≠ 1) (hl : lamP + lamW ≠ 0)
    (hk : (bookCoef β σ φ α εp εw lamP lamW).kapP = (bookCoef β σ φ α εp εw lamP lamW).kapW) :
    (bookCoef β σ φ α εp εw lamP lamW).kapP =
      lamP * lamW / (lamP + lamW) * (σ + (φ + α) / (1 - α)) := by
  have h := book_composite_slope (β := β) (σ := σ) (φ := φ) (εp := εp) (εw := εw)
    (lamP := lamP) (lamW := lamW) hα
  rw [← hk] at h
  simp only [bookCoef] at h ⊢
  rw [div_mul_eq_mul_div, eq_div_iff hl]
  linear_combination h

/-- Galí (2015), (28), p. 179: under `0 ≤ α < 1`, `σ > 0`, `φ ≥ 0`, `ε_p, ε_w > 0`,
`λ_p, λ_w > 0`, the book's loss weights are positive and `κ_p ≥ 0`, `κ_w > 0`. -/
theorem bookCoef_pos {β σ φ α εp εw lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    0 < (bookCoef β σ φ α εp εw lamP lamW).ay ∧ 0 < (bookCoef β σ φ α εp εw lamP lamW).ap ∧
      0 < (bookCoef β σ φ α εp εw lamP lamW).aw ∧
        0 ≤ (bookCoef β σ φ α εp εw lamP lamW).kapP ∧
          0 < (bookCoef β σ φ α εp εw lamP lamW).kapW := by
  have h1 : 0 < 1 - α := by linarith
  simp only [bookCoef]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩

/-- Galí (2015), (34)–(35), pp. 183–184 (the algebra): from (30) at `t` and `t − 1`, (31) and
(32) with `a_p = ε/λ_p`, `a_w = ε/λ_w`, `κ_p = κ_w = κ` and `κ (λ_p + λ_w) = λ_p λ_w a_y`
(fn. 6), composite inflation is `π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})`. -/
theorem composite_alg {ay κ lp lw ε y yl p q z1 z1l z2 z2l z3 : ℝ} (hlp : 0 < lp)
    (hlw : 0 < lw) (hε : ε ≠ 0) (hκ : κ ≠ 0) (hkey : κ * (lp + lw) = lp * lw * ay)
    (f1 : ay * y + κ * z1 + κ * z2 = 0) (f1l : ay * yl + κ * z1l + κ * z2l = 0)
    (f2 : ε / lp * p - (z1 - z1l) + z3 = 0) (f3 : ε / lw * q - (z2 - z2l) - z3 = 0) :
    lw / (lp + lw) * p + lp / (lp + lw) * q = -(1 / ε) * (y - yl) := by
  have g2 : ε * p = lp * (z1 - z1l - z3) := by
    have : ε / lp * p = z1 - z1l - z3 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff hlp.ne'] at this
    linarith
  have g3 : ε * q = lw * (z2 - z2l + z3) := by
    have : ε / lw * q = z2 - z2l + z3 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff hlw.ne'] at this
    linarith
  have h : κ * (ε * (lw * p + lp * q)) = κ * (-(lp + lw) * (y - yl)) := by
    linear_combination (κ * lw) * g2 + (κ * lp) * g3 + (lp * lw) * (f1 - f1l) + (y - yl) * hkey
  have h' := mul_left_cancel₀ hκ h
  have hs : 0 < lp + lw := by linarith
  field_simp
  linear_combination h'

/-- Galí (2015), (34)–(35): `κ (λ_p + λ_w) = λ_p λ_w a_y` with `a_y > 0`, `λ_p, λ_w > 0` forces
`κ ≠ 0`. -/
theorem kap_ne_zero {ay κ lp lw : ℝ} (hay : 0 < ay) (hlp : 0 < lp) (hlw : 0 < lw)
    (hkey : κ * (lp + lw) = lp * lw * ay) : κ ≠ 0 := by
  rintro rfl
  have : 0 < lp * lw * ay := by positivity
  linarith

/-- Galí (2015), N6.1 (survey) (the separation identity): with
`π̄ = (λ_w π^p + λ_p π^w)/(λ_p + λ_w)` and `D = π^w − π^p`,
`(ε/λ_p)(π^p)² + (ε/λ_w)(π^w)² = ε(λ_p + λ_w)/(λ_p λ_w) π̄² + ε/(λ_p + λ_w) D²`. -/
theorem separation {lp lw : ℝ} (hlp : 0 < lp) (hlw : 0 < lw) (ε p q : ℝ) :
    ε / lp * p ^ 2 + ε / lw * q ^ 2 =
      ε * (lp + lw) / (lp * lw) * (lw / (lp + lw) * p + lp / (lp + lw) * q) ^ 2 +
        ε / (lp + lw) * (q - p) ^ 2 := by
  have hs : 0 < lp + lw := by linarith
  field_simp
  ring

namespace Det

/-- **Galí (2015), (34)–(35), pp. 183–184 (deterministic)**: in the special case `κ_p = κ_w`,
`ε_p = ε_w(1 − α) = ε` (so `a_p = ε/λ_p`, `a_w = ε/λ_w`) with `κ(λ_p + λ_w) = λ_p λ_w a_y`
(fn. 6), the first-order conditions (30)–(32) imply `π̄_t = −(1/ε) Δỹ_t` for `t ≥ 1` (34) and
`π̄_0 = −(1/ε) ỹ_0` (35) (`ỹ_{−1} := 0`). -/
theorem composite_foc {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hkey : c.kapP * (c.lamP + c.lamW) = c.lamP * c.lamW * c.ay) (hay : 0 < c.ay)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hε : ε ≠ 0) (hap : c.ap = ε / c.lamP)
    (haw : c.aw = ε / c.lamW) {y pp pw z1 z2 z3 : ℕ → ℝ} (hfoc : FOC c y pp pw z1 z2 z3)
    (t : ℕ) :
    c.lamW / (c.lamP + c.lamW) * pp t + c.lamP / (c.lamP + c.lamW) * pw t =
      -(1 / ε) * (y t - prev 0 y t) := by
  have hκ := kap_ne_zero hay hlp hlw hkey
  have f1l : c.ay * prev 0 y t + c.kapP * prev 0 z1 t + c.kapP * prev 0 z2 t = 0 := by
    cases t with
    | zero => simp
    | succ s => have := (hfoc s).1; rw [← hk] at this; simpa using this
  have f1 := (hfoc t).1
  rw [← hk] at f1
  have f2 := (hfoc t).2.1
  have f3 := (hfoc t).2.2.1
  rw [hap] at f2
  rw [haw] at f3
  exact composite_alg hlp hlw hε hκ hkey f1 f1l f2 f3

end Det

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 184: composite inflation `π̄_t = (λ_w π^p_t + λ_p π^w_t)/(λ_p + λ_w)`. -/
noncomputable def pibar (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (c.lamW / (c.lamP + c.lamW)) • pp t + (c.lamP / (c.lamP + c.lamW)) • pw t

/-- **Galí (2015), (36), p. 184 (composite Phillips curve, all parameters)**: combining (18) and
(20), `π̄_t = β E_t π̄_{t+1} + κ̄ ỹ_t` with `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)` (the book writes
`κ`, defined only when `κ_p = κ_w`; survey error 3; for the book's coefficients
`κ̄ = λ_p λ_w (σ + (φ + α)/(1 − α))/(λ_p + λ_w)`, `book_composite_slope`). -/
theorem composite_nkpc {c : Coef} (hl : c.lamP + c.lamW ≠ 0) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w : ℕ → Ω → ℝ} (hc : Constr 𝔼 c dn w0 y pp pw w) (t : ℕ) :
    pibar c pp pw t = c.β • 𝔼.E t (pibar c pp pw (t + 1)) +
      ((c.lamW * c.kapP + c.lamP * c.kapW) / (c.lamP + c.lamW)) • y t := by
  funext ω
  have e1 := congrFun (hc t).1 ω
  have e2 := congrFun (hc t).2.1 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  simp only [pibar, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination c.lamW * e1 + c.lamP * e2

/-- **Galí (2015), (34)–(35), pp. 183–184**: in the special case `κ_p = κ_w`, `ε_p = ε_w(1 − α) =
ε` (`a_p = ε/λ_p`, `a_w = ε/λ_w`, and fn. 6: `κ(λ_p + λ_w) = λ_p λ_w a_y`), the first-order
conditions (30)–(32) imply `π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})` for `t ≥ 1` (34) and
`π̄_0 = −(1/ε) ỹ_0` (35). -/
theorem composite_foc {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hkey : c.kapP * (c.lamP + c.lamW) = c.lamP * c.lamW * c.ay) (hay : 0 < c.ay)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hε : ε ≠ 0) (hap : c.ap = ε / c.lamP)
    (haw : c.aw = ε / c.lamW) {y pp pw z1 z2 z3 : ℕ → Ω → ℝ}
    (hfoc : FOCs 𝔼 c y pp pw z1 z2 z3) (t : ℕ) :
    pibar c pp pw t = -(1 / ε) • (y t - prev 0 y t) := by
  have hκ := kap_ne_zero hay hlp hlw hkey
  funext ω
  have f1l : c.ay * prev 0 y t ω + c.kapP * prev 0 z1 t ω + c.kapP * prev 0 z2 t ω = 0 := by
    cases t with
    | zero => simp
    | succ s =>
      have := congrFun (hfoc s).1 ω
      rw [← hk] at this
      simpa using this
  have f1 := congrFun (hfoc t).1 ω
  have f2 := congrFun (hfoc t).2.1 ω
  have f3 := congrFun (hfoc t).2.2.1 ω
  rw [← hk] at f1
  rw [hap] at f2
  rw [haw] at f3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at f1 f2 f3
  simp only [pibar, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact composite_alg hlp hlw hε hκ hkey f1 f1l f2 f3

/-! ### The special case: strict composite inflation targeting is optimal (p. 184) -/

/-- Galí (2015), N6.1 (survey): the price inflation of the projected plan,
`−λ_p/(λ_p + λ_w) · (π^w_t − π^p_t)` (composite inflation zero, same `D = π^w − π^p`). -/
noncomputable def projP (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (-(c.lamP / (c.lamP + c.lamW))) • (pw t - pp t)

/-- Galí (2015), N6.1 (survey): the wage inflation of the projected plan,
`λ_w/(λ_p + λ_w) · (π^w_t − π^p_t)`. -/
noncomputable def projW (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (c.lamW / (c.lamP + c.lamW)) • (pw t - pp t)

/-- Galí (2015), N6.1 (survey): with `κ_p = κ_w`, (18) − (20) and (21) give the
relative-inflation block `D_t = β E_t D_{t+1} − (λ_p + λ_w) ω̃_t`,
`ω̃_t = ω̃_{t−1} + D_t − Δωⁿ_t`, which does not involve `ỹ` or `π̄`. -/
theorem block_of_constr {c : Coef} (hk : c.kapP = c.kapW) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w : ℕ → Ω → ℝ} (hc : Constr 𝔼 c dn w0 y pp pw w) (t : ℕ) :
    pw t - pp t = c.β • 𝔼.E t (pw (t + 1) - pp (t + 1)) - (c.lamP + c.lamW) • w t ∧
      w t = prev w0 w t + (pw t - pp t) - dn t := by
  constructor
  · funext ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk] at e1
    linarith
  · rw [(hc t).2.2]; abel

/-- **Galí (2015), N6.1 (survey) (feasibility of the projection)**: with `κ_p = κ_w`, replacing
`(ỹ, π̄)` by `(0, 0)` and keeping `D = π^w − π^p` and `ω̃` maps plans to plans. -/
theorem proj_plan {c : Coef} (hk : c.kapP = c.kapW) (hl : 0 < c.lamP + c.lamW)
    {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ} {y pp pw w : ℕ → Ω → ℝ} (hp : Plan 𝔼 c dn w0 y pp pw w) :
    Plan 𝔼 c dn w0 0 (projP c pp pw) (projW c pp pw) w := by
  obtain ⟨hc, -, hppa, hpwa, hwa, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, hwb⟩ := hp
  have hl' := hl.ne'
  refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => map_zero _, fun t => ?_, fun t => ?_, hwa,
    ⟨0, fun t ω => by simp⟩, ⟨|c.lamP / (c.lamP + c.lamW)| * (Bq + Bp), fun t ω => ?_⟩,
    ⟨|c.lamW / (c.lamP + c.lamW)| * (Bq + Bp), fun t ω => ?_⟩, hwb⟩
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [projP, map_smul, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination (-c.lamP) * e
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [projW, map_smul, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination c.lamW * e
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).2 ω
    simp only [Pi.add_apply, Pi.sub_apply] at e
    simp only [projP, projW, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    field_simp
    ring
  · simp only [projP, map_smul, map_sub, hppa t, hpwa t]
  · simp only [projW, map_smul, map_sub, hppa t, hpwa t]
  · simp only [projP, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBp t ω)))
      (abs_nonneg _)
  · simp only [projW, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBp t ω)))
      (abs_nonneg _)

/-- **Galí (2015), N6.1 (survey) (the projection lowers the loss pathwise)**: with
`a_p = ε/λ_p`, `a_w = ε/λ_w`, the period loss of a plan exceeds that of its projection by
`½ (a_y ỹ_t² + ε(λ_p + λ_w)/(λ_p λ_w) π̄_t²) ≥ 0`, state by state. -/
theorem periodLoss_sub_proj {c : Coef} {ε : ℝ} (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) (y pp pw : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    periodLoss c y pp pw t ω - periodLoss c 0 (projP c pp pw) (projW c pp pw) t ω =
      (c.ay * y t ω ^ 2 + ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) * pibar c pp pw t ω ^ 2) /
        2 := by
  have hs := separation hlp hlw ε (pp t ω) (pw t ω)
  have hl : 0 < c.lamP + c.lamW := by linarith
  simp only [periodLoss, projP, projW, pibar, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Pi.zero_apply, hap, haw]
  field_simp
  field_simp at hs
  linear_combination hs

/-- Galí (2015), p. 184: with composite inflation zero, price and wage inflation are the
projections of `D = π^w − π^p`. -/
theorem eq_proj_of_pibar {c : Coef} (hl : 0 < c.lamP + c.lamW) {pp pw : ℕ → Ω → ℝ} (t : ℕ)
    (h : pibar c pp pw t = 0) : pp t = projP c pp pw t ∧ pw t = projW c pp pw t := by
  constructor <;> funext ω <;> have e := congrFun h ω <;>
    simp only [pibar, projP, projW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢ <;> field_simp at e ⊢ <;> linarith

/-- **Galí (2015), p. 184 (strict composite inflation targeting is OPTIMAL)**: in the special case
`κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε` (`a_p = ε/λ_p`, `a_w = ε/λ_w`), any plan with `ỹ ≡ 0` and
`π̄ ≡ 0` minimises the welfare loss among all plans, state by state; and any plan with the same
loss at `ω` has `E_0 ỹ_t² = E_0 π̄_t² = 0` there. Proof (survey Note N6.1, replacing the book's
argument, which checks only the necessary conditions (34)–(35): survey error 2): every plan's
projection (same `D`, `ω̃`, with `ỹ = π̄ = 0`) is a plan with pathwise lower loss; by
determinacy of the relative-inflation block all projections coincide with the candidate. No
pull-out property is needed. -/
theorem composite_targeting_optimal {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → Ω → ℝ}
    {w0 : Ω → ℝ} {ys pps pws ws : ℕ → Ω → ℝ} (hC : Plan 𝔼 c dn w0 ys pps pws ws)
    (hy0 : ys = 0) (hpi : ∀ t, pibar c pps pws t = 0) :
    ∀ y pp pw w, Plan 𝔼 c dn w0 y pp pw w → ∀ ω,
      expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω → ∀ t,
          𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω = 0) := by
  intro y pp pw w hp ω
  have hl : 0 < c.lamP + c.lamW := by linarith
  have hapos : 0 ≤ c.ap := by rw [hap]; positivity
  have hawpos : 0 ≤ c.aw := by rw [haw]; positivity
  have hP := proj_plan 𝔼 hk hl hp
  have hyb := hp.2.2.2.2.2.1
  have hppb := hp.2.2.2.2.2.2.1
  have hpwb := hp.2.2.2.2.2.2.2.1
  -- the projection coincides with the candidate
  obtain ⟨hc, -, -, -, hwa, -, -, -, ⟨Mw, hMw⟩⟩ := hp
  obtain ⟨hcs, -, -, -, hwsa, -, -, -, ⟨Mws, hMws⟩⟩ := hC
  set Dd : ℕ → Ω → ℝ := fun t => (pw t - pp t) - (pws t - pps t) with hDd
  set wd : ℕ → Ω → ℝ := fun t => w t - ws t with hwd
  have hb1 : ∀ t, Dd t = c.β • 𝔼.E t (Dd (t + 1)) - (c.lamP + c.lamW) • wd t := by
    intro t
    funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    have es := congrFun (block_of_constr 𝔼 hk hcs t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e es
    simp only [hDd, hwd, map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hb2 : ∀ t, wd t = prev 0 wd t + Dd t := by
    intro t
    have e := (block_of_constr 𝔼 hk hc t).2
    have es := (block_of_constr 𝔼 hk hcs t).2
    have hp' := prev_sub w0 w ws t
    simp only [hDd, hwd]
    rw [← hp']
    conv_lhs => rw [e, es]
    abel
  have hwda : 𝔼.Adapted wd := fun t => by simp only [hwd, map_sub, hwa t, hwsa t]
  obtain ⟨hD0, -⟩ := block_zero 𝔼 hβ0 hβ1 hl hwda
    ⟨Mw + Mws, fun t ω => (abs_sub _ _).trans (add_le_add (hMw t ω) (hMws t ω))⟩ hb1 hb2
  have hDeq : ∀ t, pw t - pp t = pws t - pps t := fun t => by
    have := congrFun hD0 t
    simp only [hDd, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hpp : projP c pp pw = pps := funext fun t => by
    rw [(eq_proj_of_pibar hl t (hpi t)).1]; simp only [projP, hDeq t]
  have hpw : projW c pp pw = pws := funext fun t => by
    rw [(eq_proj_of_pibar hl t (hpi t)).2]; simp only [projW, hDeq t]
  rw [hpp, hpw] at hP
  -- the excess loss as a series of nonnegative terms
  have hpl := hP
  obtain ⟨-, -, -, -, -, hysb, hppsb, hpwsb, -⟩ := hpl
  have hS := (expLoss_hasSum 𝔼 hβ0.le hβ1 hay.le hapos hawpos hyb hppb hpwb ω).sub
    (expLoss_hasSum 𝔼 hβ0.le hβ1 hay.le hapos hawpos hysb hppsb hpwsb ω)
  set K := ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) with hK
  have hK0 : 0 < K := by positivity
  have hterm : ∀ t, c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω -
      c.β ^ t * 𝔼.E 0 (periodLoss c 0 pps pws t) ω =
      c.β ^ t * ((c.ay / 2) * 𝔼.E 0 (fun ω => y t ω ^ 2) ω +
        (K / 2) * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω) := by
    intro t
    have hf : periodLoss c y pp pw t - periodLoss c 0 pps pws t =
        (c.ay / 2) • (fun ω => y t ω ^ 2) + (K / 2) • (fun ω => pibar c pp pw t ω ^ 2) := by
      funext ω'
      have := periodLoss_sub_proj hlp hlw hap haw y pp pw t ω'
      rw [hpp, hpw] at this
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [this, hK]
      ring
    rw [← mul_sub, ← Pi.sub_apply (𝔼.E 0 _), ← map_sub, hf, map_add, map_smul, map_smul]
    rfl
  rw [hy0]
  simp only [hterm] at hS
  have hnn : ∀ t, 0 ≤ c.β ^ t * ((c.ay / 2) * 𝔼.E 0 (fun ω => y t ω ^ 2) ω +
      (K / 2) * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω) := fun t => by
    have h1 := E_nonneg 𝔼 (f := fun ω => y t ω ^ 2) (fun ω => by positivity) 0 ω
    have h2 := E_nonneg 𝔼 (f := fun ω => pibar c pp pw t ω ^ 2) (fun ω => by positivity) 0 ω
    positivity
  refine ⟨sub_nonneg.1 (hS.nonneg hnn), fun heq t => ?_⟩
  rw [heq, sub_self] at hS
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).1 hS) t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at hz
  have h1 := E_nonneg 𝔼 (f := fun ω => y t ω ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E_nonneg 𝔼 (f := fun ω => pibar c pp pw t ω ^ 2) (fun ω => by positivity) 0 ω
  have k1 := mul_nonneg (half_pos hay).le h1
  have k2 := mul_nonneg (half_pos hK0).le h2
  constructor
  · have : c.ay / 2 * 𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (half_pos hay).ne'
  · have : K / 2 * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (half_pos hK0).ne'

/-- Galí (2015), N6.1 (survey): the real wage gap of the candidate plan,
`ω̃_t = r ω̃_{t−1} + v_t` with `ω̃_{−1} = w0`. -/
def wSeq (r : ℝ) (w0 : Ω → ℝ) (v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => r • w0 + v 0
  | t + 1 => r • wSeq r w0 v t + v (t + 1)

/-- Galí (2015), N6.1 (survey): `ω̃_t = r ω̃_{t−1} + v_t`. -/
theorem wSeq_eq (r : ℝ) (w0 : Ω → ℝ) (v : ℕ → Ω → ℝ) (t : ℕ) :
    wSeq r w0 v t = r • prev w0 (wSeq r w0 v) t + v t := by
  cases t <;> rfl

/-- Galí (2015), p. 181: the lag of an adapted process with a date-0-known initial value is
adapted. -/
theorem prev_adapted {w0 : Ω → ℝ} {w : ℕ → Ω → ℝ} (hw0 : 𝔼.E 0 w0 = w0) (hwa : 𝔼.Adapted w) :
    𝔼.Adapted (prev w0 w) := by
  intro t
  cases t with
  | zero => exact hw0
  | succ t => simp only [prev_succ]; rw [← hwa t, 𝔼.known (Nat.le_succ t)]

/-- **Galí (2015), p. 184 (existence of the strict composite-targeting plan)**: with
`λ_p, λ_w > 0`, `0 < β < 1`, a bounded adapted `Δωⁿ` and a bounded date-0-known `ω̃_{−1}`, there
is a plan with `ỹ ≡ 0` and `π̄ ≡ 0`: `ω̃_t = r ω̃_{t−1} + v_t` where `r ∈ (0, 1)` is the stable
root of the relative-inflation block and `v` the forward solution of
`v_t = β r E_t v_{t+1} + r (β E_t Δωⁿ_{t+1} − Δωⁿ_t)`, `D_t = ω̃_t − ω̃_{t−1} + Δωⁿ_t`,
`π^p = −λ_p D/(λ_p + λ_w)`, `π^w = λ_w D/(λ_p + λ_w)`. -/
theorem exists_composite_plan {c : Coef} (hlp : 0 < c.lamP)
    (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) {dn : ℕ → Ω → ℝ} {Md : ℝ}
    (hdb : ∀ t ω, |dn t ω| ≤ Md) (hda : 𝔼.Adapted dn) {w0 : Ω → ℝ} {M0 : ℝ}
    (hw0 : 𝔼.E 0 w0 = w0) (hw0b : ∀ ω, |w0 ω| ≤ M0) :
    ∃ pp pw w, Plan 𝔼 c dn w0 0 pp pw w ∧ ∀ t, pibar c pp pw t = 0 := by
  set k := c.lamP + c.lamW with hk_def
  have hkpos : 0 < k := by positivity
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := c.β) hkpos
  set f : ℕ → Ω → ℝ := fun t => c.β • 𝔼.E t (dn (t + 1)) - dn t with hf_def
  set u : ℕ → Ω → ℝ := fun t => r • f t with hu_def
  have hub : ∀ t ω, |u t ω| ≤ r * (c.β * Md + Md) := by
    intro t ω
    simp only [hu_def, hf_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_of_pos hr0]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ (hdb t ω))) hr0.le
    rw [abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdb (t + 1)) t ω) hβ0.le
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu_def, hf_def, map_smul, map_sub, 𝔼.E_E_self, hda t]
  have ha0 : 0 ≤ c.β * r := by positivity
  have ha1 : c.β * r < 1 := by nlinarith
  set v := 𝔼.forwardSeries (c.β * r) u with hv_def
  have hv : ∀ t, v t = (c.β * r) • 𝔼.E t (v (t + 1)) + u t :=
    𝔼.forwardSeries_solves ha0 ha1 hub hua
  have hva : 𝔼.Adapted v := 𝔼.forwardSeries_adapted ha0 ha1 hub
  obtain ⟨V, hV⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hub
  set w := wSeq r w0 v with hw_def
  have hwa : 𝔼.Adapted w := by
    intro t
    induction t with
    | zero =>
      change 𝔼.E 0 (r • w0 + v 0) = r • w0 + v 0
      rw [map_add, map_smul, hw0, hva 0]
    | succ t ih =>
      change 𝔼.E (t + 1) (r • w t + v (t + 1)) = r • w t + v (t + 1)
      rw [map_add, map_smul, hva (t + 1), ← ih, 𝔼.known (Nat.le_succ t)]
  have hpa := prev_adapted 𝔼 hw0 hwa
  set B := |M0| + |V| / (1 - r) with hB
  have hB1 : |V| ≤ (1 - r) * B := by
    rw [hB, mul_add, mul_div_cancel₀ _ (by linarith : (1 - r) ≠ 0)]
    nlinarith [abs_nonneg M0]
  have hwb : ∀ t ω, |w t ω| ≤ B := by
    have hstep : ∀ t ω, |prev w0 w t ω| ≤ B → |w t ω| ≤ B := by
      intro t ω h
      have := congrFun (wSeq_eq r w0 v t) ω
      rw [← hw_def] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hr0]
      have h1 := mul_le_mul_of_nonneg_left h hr0.le
      have h2 := (hV t ω).trans (le_abs_self V)
      linarith
    intro t
    induction t with
    | zero => exact fun ω => hstep 0 ω (by
        simp only [prev_zero]
        have := abs_nonneg V
        have : 0 ≤ |V| / (1 - r) := div_nonneg (abs_nonneg V) (by linarith)
        linarith [hw0b ω, le_abs_self M0])
    | succ t ih => exact fun ω => hstep (t + 1) ω (ih ω)
  have hpb : ∀ t ω, |prev w0 w t ω| ≤ B := by
    intro t ω
    cases t with
    | zero =>
      have : 0 ≤ |V| / (1 - r) := div_nonneg (abs_nonneg V) (by linarith)
      simp only [prev_zero]
      linarith [hw0b ω, le_abs_self M0]
    | succ t => exact hwb t ω
  set D : ℕ → Ω → ℝ := fun t => w t - prev w0 w t + dn t with hD_def
  have hblock : ∀ t, D t = c.β • 𝔼.E t (D (t + 1)) - k • w t := by
    intro t
    have hEw : 𝔼.E t (w (t + 1)) = r • w t + 𝔼.E t (v (t + 1)) := by
      change 𝔼.E t (r • w t + v (t + 1)) = _
      rw [map_add, map_smul, hwa t]
    have hED : 𝔼.E t (D (t + 1)) = 𝔼.E t (w (t + 1)) - w t + 𝔼.E t (dn (t + 1)) := by
      simp only [hD_def, prev_succ, map_add, map_sub, hwa t]
    funext ω
    have e1 := congrFun hEw ω
    have e2 := congrFun hED ω
    have e3 := congrFun (hv t) ω
    have e4 := congrFun (wSeq_eq r w0 v t) ω
    rw [← hw_def] at e4
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    simp only [hu_def, hf_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3
    simp only [hD_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hD_def] at e2
    simp only at e2
    rw [e2]
    refine mul_left_cancel₀ hr0.ne' ?_
    linear_combination e4 + (-r * c.β) * e1 + e3 - (w t ω) * hr
  have hl' := hkpos.ne'
  refine ⟨fun t => (-(c.lamP / k)) • D t, fun t => (c.lamW / k) • D t, w,
    ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => map_zero _, fun t => ?_, fun t => ?_, hwa,
      ⟨0, fun t ω => by simp⟩, ⟨c.lamP / k * (B + B + Md), fun t ω => ?_⟩,
      ⟨c.lamW / k * (B + B + Md), fun t ω => ?_⟩, ⟨B, hwb⟩⟩, fun t => ?_⟩
  · funext ω
    have e := congrFun (hblock t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      add_zero]
    rw [e]
    field_simp
    ring
  · funext ω
    have e := congrFun (hblock t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      mul_zero, add_zero]
    rw [e]
    field_simp
  · funext ω
    simp only [hD_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [hD_def, map_smul, map_add, map_sub, hwa t, hpa t, hda t]
  · simp only [hD_def, map_smul, map_add, map_sub, hwa t, hpa t, hda t]
  · have hDb : |D t ω| ≤ B + B + Md := by
      simp only [hD_def, Pi.add_apply, Pi.sub_apply]
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hwb t ω) (hpb t ω))) (hdb t ω))
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos (div_pos hlp hkpos)]
    exact mul_le_mul_of_nonneg_left hDb (div_pos hlp hkpos).le
  · have hDb : |D t ω| ≤ B + B + Md := by
      simp only [hD_def, Pi.add_apply, Pi.sub_apply]
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hwb t ω) (hpb t ω))) (hdb t ω))
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (div_pos hlw hkpos)]
    exact mul_le_mul_of_nonneg_left hDb (div_pos hlw hkpos).le
  · funext ω
    simp only [pibar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hk_def]
    field_simp
    ring

/-- **Galí (2015), §6.4.3, pp. 183–184 (THE OPTIMAL POLICY IN THE SPECIAL CASE)**: with
`κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, `λ_p, λ_w > 0`, `0 < β < 1`, a bounded adapted `Δωⁿ` and a
bounded date-0-known `ω̃_{−1}`, there is a plan with `ỹ ≡ 0` and `π̄ ≡ 0` (strict composite
inflation targeting), it minimises the welfare loss among all plans state by state, and any plan
with the same loss at `ω` has `E_0 ỹ_t² = E_0 π̄_t² = 0` there. -/
theorem composite_targeting_solves {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → Ω → ℝ}
    {Md : ℝ} (hdb : ∀ t ω, |dn t ω| ≤ Md) (hda : 𝔼.Adapted dn) {w0 : Ω → ℝ} {M0 : ℝ}
    (hw0 : 𝔼.E 0 w0 = w0) (hw0b : ∀ ω, |w0 ω| ≤ M0) :
    ∃ pp pw w, Plan 𝔼 c dn w0 0 pp pw w ∧ (∀ t, pibar c pp pw t = 0) ∧
      ∀ y' pp' pw' w', Plan 𝔼 c dn w0 y' pp' pw' w' → ∀ ω,
        expLoss 𝔼 c 0 pp pw ω ≤ expLoss 𝔼 c y' pp' pw' ω ∧
          (expLoss 𝔼 c y' pp' pw' ω = expLoss 𝔼 c 0 pp pw ω → ∀ t,
            𝔼.E 0 (fun ω => y' t ω ^ 2) ω = 0 ∧
              𝔼.E 0 (fun ω => pibar c pp' pw' t ω ^ 2) ω = 0) := by
  obtain ⟨pp, pw, w, hC, hpi⟩ := exists_composite_plan 𝔼 hlp hlw hβ0 hβ1 hdb hda hw0 hw0b
  exact ⟨pp, pw, w, hC, hpi,
    composite_targeting_optimal 𝔼 hk hlp hlw hβ0 hβ1 hay hε hap haw hC rfl hpi⟩

/-- **Galí (2015), pp. 184–185 (strict composite targeting ⇔ output-gap stabilisation, ALL
parameters)**: for a plan (bounded adapted solution of (18), (20), (21)), with `λ_p + λ_w > 0`,
`λ_w κ_p + λ_p κ_w ≠ 0` and `|β| < 1`: `π̄ ≡ 0` iff `ỹ ≡ 0` (`⇒` from (36); `⇐`: the only bounded
solution of `π̄_t = β E_t π̄_{t+1}` is zero). -/
theorem composite_zero_iff {c : Coef} (hl : 0 < c.lamP + c.lamW)
    (hkb : c.lamW * c.kapP + c.lamP * c.kapW ≠ 0) (hβ : |c.β| < 1) {dn : ℕ → Ω → ℝ}
    {w0 : Ω → ℝ} {y pp pw w : ℕ → Ω → ℝ} (hp : Plan 𝔼 c dn w0 y pp pw w) :
    (∀ t, pibar c pp pw t = 0) ↔ y = 0 := by
  obtain ⟨hc, -, -, -, -, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, -⟩ := hp
  have hn := composite_nkpc 𝔼 hl.ne' hc
  have hkb' : (c.lamW * c.kapP + c.lamP * c.kapW) / (c.lamP + c.lamW) ≠ 0 :=
    div_ne_zero hkb hl.ne'
  constructor
  · intro h
    funext t ω
    have := congrFun (hn t) ω
    rw [h t, h (t + 1), map_zero] at this
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
      zero_add] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hkb'
  · rintro rfl
    have hb : BoundedProc (pibar c pp pw) := ⟨|c.lamW / (c.lamP + c.lamW)| * Bp +
        |c.lamP / (c.lamP + c.lamW)| * Bq, fun t ω => by
      simp only [pibar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul_of_nonneg_left (hBp t ω) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (hBq t ω) (abs_nonneg _)⟩
    have h1 : ∀ t, pibar c pp pw t = c.β • 𝔼.E t (pibar c pp pw (t + 1)) +
        (0 : ℕ → Ω → ℝ) t := fun t => by
      rw [hn t]; simp
    have h2 : ∀ t, (0 : ℕ → Ω → ℝ) t = c.β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) +
        (0 : ℕ → Ω → ℝ) t := fun t => by simp
    have := 𝔼.forward_unique hβ h1 h2 hb ⟨0, fun t ω => by simp⟩
    exact fun t => congrFun this t

end Stoch

/-! ### Composite weights (p. 184) -/

/-- Galí (2015), (6), p. 165, and (15), p. 170: the Calvo slope factor `(1 − θ)(1 − βθ)/θ`
(`λ_p = Θ · calvo β θ_p`, `λ_w = calvo β θ_w/(1 + ε_w φ)`). -/
noncomputable def calvo (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lamWOf (β εw φ θw : ℝ) : ℝ := calvo β θw / (1 + εw * φ)

/-- Galí (2015), p. 165: `λ_p = (1 − θ_p)(1 − βθ_p)/θ_p · (1 − α)/(1 − α + αε_p)`. -/
noncomputable def lamPOf (β α εp θp : ℝ) : ℝ := calvo β θp * ((1 - α) / (1 - α + α * εp))

/-- Galí (2015), p. 170: the Calvo slope factor is positive for `θ ∈ (0, 1)`, `β ≤ 1`. -/
theorem calvo_pos {β θ : ℝ} (hβ1 : β ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    0 < calvo β θ := by
  obtain ⟨h0, h1⟩ := hθ
  unfold calvo
  have : 0 < 1 - β * θ := by nlinarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- Galí (2015), pp. 179, 184: the Calvo slope factor is strictly decreasing in the degree of
stickiness `θ` on `(0, 1)` (`β ≤ 1`). -/
theorem calvo_strictAntiOn {β : ℝ} (hβ1 : β ≤ 1) :
    StrictAntiOn (calvo β) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  unfold calvo
  rw [div_lt_div_iff₀ hb0 ha0]
  have hab1 : β * (a * b) < 1 := by
    have : a * b < 1 := by nlinarith
    nlinarith [mul_pos ha0 hb0]
  nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hab1)]

/-- **Galí (2015), p. 184 (composite weights)**: the weight `λ_p/(λ_p + λ_w)` on wage inflation
in composite inflation is strictly increasing in the degree of wage stickiness `θ_w ∈ (0, 1)`
(`λ_p > 0`, `1 + ε_w φ > 0`, `β ≤ 1`). -/
theorem wage_weight_strictMonoOn {β εw φ lamP : ℝ} (hβ1 : β ≤ 1)
    (hlp : 0 < lamP) (hd : 0 < 1 + εw * φ) :
    StrictMonoOn (fun θw => lamP / (lamP + lamWOf β εw φ θw)) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hpa := calvo_pos hβ1 ha
  have hpb := calvo_pos hβ1 hb
  have hlt := calvo_strictAntiOn hβ1 ha hb hab
  simp only [lamWOf]
  have h1 : 0 < calvo β b / (1 + εw * φ) := div_pos hpb hd
  apply div_lt_div_of_pos_left hlp (by positivity)
  have := div_lt_div_of_pos_right hlt hd
  linarith

/-- **Galí (2015), p. 184 (composite weights)**: the weight `λ_w/(λ_p + λ_w)` on price inflation
in composite inflation is strictly increasing in the degree of price stickiness `θ_p ∈ (0, 1)`
(`λ_w > 0`, `α < 1`, `1 − α + αε_p > 0`, `β ≤ 1`). -/
theorem price_weight_strictMonoOn {β α εp lamW : ℝ} (hβ1 : β ≤ 1)
    (hlw : 0 < lamW) (hα1 : α < 1) (hd : 0 < 1 - α + α * εp) :
    StrictMonoOn (fun θp => lamW / (lamPOf β α εp θp + lamW)) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hpa := calvo_pos hβ1 ha
  have hpb := calvo_pos hβ1 hb
  have hlt := calvo_strictAntiOn hβ1 ha hb hab
  have hΘ : 0 < (1 - α) / (1 - α + α * εp) := div_pos (by linarith) hd
  simp only [lamPOf]
  have h1 : 0 < calvo β b * ((1 - α) / (1 - α + α * εp)) := mul_pos hpb hΘ
  apply div_lt_div_of_pos_left hlw (by positivity)
  have := mul_lt_mul_of_pos_right hlt hΘ
  linarith

/-! ### The special case under perfect foresight, among all finite-loss paths -/

namespace Det

/-- **Galí (2015), N6.1 (survey) (the relative-inflation block, finite-loss version)**: with
`0 < β < 1`, `k > 0`, the only solution of `D_t = β D_{t+1} − k ω̃_t`, `ω̃_t = ω̃_{t−1} + D_t`,
`ω̃_{−1} = 0`, with `∑ βᵗ D_t² < ∞` is zero. -/
theorem block_zero_finite {β k : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hk : 0 < k) {D w : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * D t ^ 2)) (h1 : ∀ t, D t = β * D (t + 1) - k * w t)
    (h2 : ∀ t, w t = prev 0 w t + D t) : D = 0 ∧ w = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := β) hk
  set v : ℕ → ℝ := fun t => w t - r * prev 0 w t with hv_def
  have hv : ∀ t, v t = β * r * v (t + 1) := by
    intro t
    have a := h1 t
    have b := h2 t
    have b' := h2 (t + 1)
    simp only [hv_def, prev_succ] at b' ⊢
    linear_combination r * a + r * b - r * β * b' + (w t) * hr
  -- `βᵗ ω̃_t² → 0`
  have hD0 := hs.tendsto_atTop_zero
  have hD1 : Tendsto (fun t => β ^ (t + 1) * D (t + 1) ^ 2) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hD0
  have hw0 : Tendsto (fun t => β ^ t * w t ^ 2) atTop (𝓝 0) := by
    have hup := (hD1.add hD0).const_mul (2 / k ^ 2)
    rw [add_zero, mul_zero] at hup
    refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
    have hwt : k * w t = β * D (t + 1) - D t := by linarith [h1 t]
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0.le t
    have hsq : k ^ 2 * w t ^ 2 ≤ 2 * (β * D (t + 1)) ^ 2 + 2 * D t ^ 2 := by
      rw [← mul_pow, hwt]; nlinarith [sq_nonneg (β * D (t + 1) + D t)]
    have hβD : β ^ t * (β * D (t + 1)) ^ 2 ≤ β ^ (t + 1) * D (t + 1) ^ 2 := by
      have hX : 0 ≤ β ^ (t + 1) * D (t + 1) ^ 2 := by positivity
      have : β ^ t * (β * D (t + 1)) ^ 2 = β * (β ^ (t + 1) * D (t + 1) ^ 2) := by ring
      rw [this]
      nlinarith
    rw [show 2 / k ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2 + β ^ t * D t ^ 2) =
      (2 * (β ^ (t + 1) * D (t + 1) ^ 2) + 2 * (β ^ t * D t ^ 2)) / k ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq hb
    nlinarith
  have hp0 : Tendsto (fun t => β ^ t * prev 0 w t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * prev 0 w (t + 1) ^ 2) = fun t => β * (β ^ t * w t ^ 2) := by
      funext t; rw [prev_succ, pow_succ]; ring
    rw [this]
    simpa using hw0.const_mul β
  have hvt : Tendsto (fun t => β ^ t * v t ^ 2) atTop (𝓝 0) := by
    have hup := (hw0.const_mul 2).add (hp0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0.le t
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have : v t ^ 2 ≤ 2 * w t ^ 2 + 2 * prev 0 w t ^ 2 := by
      simp only [hv_def]
      nlinarith [sq_nonneg (w t + r * prev 0 w t), sq_nonneg (prev 0 w t),
        mul_le_mul_of_nonneg_right hr2 (sq_nonneg (prev 0 w t))]
    nlinarith [mul_le_mul_of_nonneg_left this hb]
  have hvz : ∀ s, v s = 0 := by
    intro s
    have hit : ∀ n, β ^ s * v s ^ 2 = (β * r ^ 2) ^ n * (β ^ (s + n) * v (s + n) ^ 2) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih, hv (s + n), ← add_assoc]
        ring
    have hle : ∀ n, β ^ s * v s ^ 2 ≤ β ^ (s + n) * v (s + n) ^ 2 := by
      intro n
      rw [hit n]
      have h1 : (β * r ^ 2) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
      have h2 : 0 ≤ β ^ (s + n) * v (s + n) ^ 2 := by positivity
      nlinarith
    have hlim : Tendsto (fun n => β ^ (s + n) * v (s + n) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat s).2 hvt
      simpa [add_comm] using this
    have h0 : β ^ s * v s ^ 2 ≤ 0 := ge_of_tendsto' hlim hle
    have hbs : 0 < β ^ s := pow_pos hβ0 s
    have : v s ^ 2 = 0 := by nlinarith [sq_nonneg (v s)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hw : ∀ t, w t = 0 := by
    intro t
    induction t with
    | zero => have := hvz 0; simpa [hv_def] using this
    | succ t ih =>
      have := hvz (t + 1)
      simp only [hv_def, prev_succ, ih, mul_zero, sub_zero] at this
      exact this
  refine ⟨funext fun t => ?_, funext hw⟩
  have := h2 t
  rw [hw t] at this
  cases t with
  | zero => simpa using this.symm
  | succ t => simpa [hw t] using this.symm

/-- Galí (2015), N6.1 (survey): the projected price inflation `−λ_p/(λ_p + λ_w) · D_t`. -/
noncomputable def projP (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  -(c.lamP / (c.lamP + c.lamW)) * (pw t - pp t)

/-- Galí (2015), N6.1 (survey): the projected wage inflation `λ_w/(λ_p + λ_w) · D_t`. -/
noncomputable def projW (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.lamW / (c.lamP + c.lamW) * (pw t - pp t)

/-- Galí (2015), p. 184: composite inflation (perfect foresight). -/
noncomputable def pibar (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.lamW / (c.lamP + c.lamW) * pp t + c.lamP / (c.lamP + c.lamW) * pw t

/-- **Galí (2015), N6.1 (survey) (feasibility of the projection, deterministic)**: with
`κ_p = κ_w`, replacing `(ỹ, π̄)` by `(0, 0)` and keeping `D`, `ω̃` preserves (18), (20), (21). -/
theorem proj_feasible {c : Coef} (hk : c.kapP = c.kapW) (hl : 0 < c.lamP + c.lamW)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w : ℕ → ℝ} (hf : Feasible c dn w0 y pp pw w) :
    Feasible c dn w0 0 (projP c pp pw) (projW c pp pw) w := by
  intro t
  obtain ⟨e1, e2, e3⟩ := hf t
  have hl' := hl.ne'
  rw [hk] at e1
  refine ⟨?_, ?_, ?_⟩
  · simp only [projP, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination (-c.lamP) * (e2 - e1)
  · simp only [projW, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination c.lamW * (e2 - e1)
  · simp only [projP, projW]
    rw [e3]
    field_simp
    ring

/-- **Galí (2015), N6.1 (survey) (the projection lowers the loss, period by period)**: with
`a_p = ε/λ_p`, `a_w = ε/λ_w`, the discounted period loss exceeds that of the projection by
`βᵗ ½ (a_y ỹ_t² + ε(λ_p + λ_w)/(λ_p λ_w) π̄_t²)`. -/
theorem lossTerm_sub_proj {c : Coef} {ε : ℝ} (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) (y pp pw : ℕ → ℝ) (t : ℕ) :
    lossTerm c y pp pw t - lossTerm c 0 (projP c pp pw) (projW c pp pw) t =
      c.β ^ t * ((c.ay * y t ^ 2 +
        ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) * pibar c pp pw t ^ 2) / 2) := by
  have hs := separation hlp hlw ε (pp t) (pw t)
  have hl : 0 < c.lamP + c.lamW := by linarith
  simp only [lossTerm, projP, projW, pibar, Pi.zero_apply, hap, haw]
  field_simp
  field_simp at hs
  linear_combination c.β ^ t * hs

/-- **Galí (2015), §6.4.3, p. 184 (strict composite targeting is OPTIMAL, deterministic)**: in the
special case `κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, a feasible finite-loss path with `ỹ ≡ 0` and
`π̄ ≡ 0` solves the commitment problem (among all feasible finite-loss paths), and it is the
unique solution. The proof is the separation argument of survey Note N6.1 (the book's argument
only checks the necessary conditions (34)–(35): survey error 2). -/
theorem composite_targeting_optimal {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → ℝ} {w0 : ℝ}
    {pps pws ws : ℕ → ℝ} (hC : Feasible c dn w0 0 pps pws ws) (hCl : FiniteLoss c 0 pps pws)
    (hpi : ∀ t, pibar c pps pws t = 0) :
    IsOptimal c dn w0 0 pps pws ws ∧
      ∀ y pp pw w, IsOptimal c dn w0 y pp pw w ↔ y = 0 ∧ pp = pps ∧ pw = pws ∧ w = ws := by
  have hl : 0 < c.lamP + c.lamW := by linarith
  have hapos : 0 < c.ap := by rw [hap]; positivity
  have hawpos : 0 < c.aw := by rw [haw]; positivity
  set K := ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) with hK
  have hK0 : 0 < K := by positivity
  have hCproj : ∀ t, pps t = projP c pps pws t ∧ pws t = projW c pps pws t := by
    intro t
    have e := hpi t
    simp only [pibar, projP, projW] at e ⊢
    constructor <;> field_simp at e ⊢ <;> linarith
  -- every feasible finite-loss path projects onto the candidate
  have key : ∀ y pp pw w, Feasible c dn w0 y pp pw w → FiniteLoss c y pp pw →
      projP c pp pw = pps ∧ projW c pp pw = pws ∧ w = ws ∧
        HasSum (fun t => c.β ^ t * ((c.ay * y t ^ 2 + K * pibar c pp pw t ^ 2) / 2))
          (loss c y pp pw - loss c 0 pps pws) := by
    intro y pp pw w hf hfl
    obtain ⟨-, sp, sq⟩ := summable_sq hβ0.le hay hapos hawpos hfl
    obtain ⟨-, sps, sqs⟩ := summable_sq hβ0.le hay hapos hawpos hCl
    have sD := summable_sub_sq hβ0.le (summable_sub_sq hβ0.le sq sp)
      (summable_sub_sq hβ0.le sqs sps)
    have hb1 : ∀ t, (pw t - pp t) - (pws t - pps t) =
        c.β * ((pw (t + 1) - pp (t + 1)) - (pws (t + 1) - pps (t + 1))) -
          (c.lamP + c.lamW) * (w t - ws t) := by
      intro t
      obtain ⟨e1, e2, -⟩ := hf t
      obtain ⟨f1, f2, -⟩ := hC t
      simp only [Pi.zero_apply, mul_zero, add_zero] at f1 f2
      rw [hk] at e1
      linear_combination e2 - e1 - f2 + f1
    have hb2 : ∀ t, w t - ws t = prev 0 (fun s => w s - ws s) t +
        ((pw t - pp t) - (pws t - pps t)) := by
      intro t
      obtain ⟨-, -, e3⟩ := hf t
      obtain ⟨-, -, f3⟩ := hC t
      rw [← prev_sub w0 w ws t]
      linear_combination e3 - f3
    obtain ⟨hD0, hw0⟩ := block_zero_finite hβ0 hβ1 hl sD hb1 hb2
    have hDeq : ∀ t, pw t - pp t = pws t - pps t := fun t => by
      have := congrFun hD0 t
      simp only [Pi.zero_apply] at this
      linarith
    have hpp : projP c pp pw = pps := funext fun t => by
      rw [(hCproj t).1]; simp only [projP, hDeq t]
    have hpw : projW c pp pw = pws := funext fun t => by
      rw [(hCproj t).2]; simp only [projW, hDeq t]
    have hww : w = ws := funext fun t => by
      have := congrFun hw0 t
      simp only [Pi.zero_apply] at this
      linarith
    refine ⟨hpp, hpw, hww, ?_⟩
    have hS := hfl.hasSum.sub hCl.hasSum
    have hfun : (fun t => c.β ^ t * ((c.ay * y t ^ 2 + K * pibar c pp pw t ^ 2) / 2)) =
        fun t => lossTerm c y pp pw t - lossTerm c 0 pps pws t := by
      funext t
      have := lossTerm_sub_proj hlp hlw hap haw y pp pw t
      rw [hpp, hpw] at this
      rw [this, hK]
    rw [hfun]
    exact hS
  have hopt : IsOptimal c dn w0 0 pps pws ws := by
    refine ⟨hC, hCl, fun y pp pw w hf hfl => ?_⟩
    obtain ⟨-, -, -, hS⟩ := key y pp pw w hf hfl
    exact sub_nonneg.1 (hS.nonneg fun t => by positivity)
  refine ⟨hopt, fun y pp pw w => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨hf, hfl, hmin⟩ := h
    obtain ⟨hpp, hpw, hww, hS⟩ := key y pp pw w hf hfl
    have heq : loss c y pp pw = loss c 0 pps pws :=
      le_antisymm (hmin _ _ _ _ hC hCl) (hopt.2.2 _ _ _ _ hf hfl)
    rw [heq, sub_self] at hS
    have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hS
    have ht : ∀ t, y t = 0 ∧ pibar c pp pw t = 0 := fun t => by
      have h := congrFun hz t
      simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
        false_or] at h
      have k1 := mul_nonneg hay.le (sq_nonneg (y t))
      have k2 := mul_nonneg hK0.le (sq_nonneg (pibar c pp pw t))
      have e1 : c.ay * y t ^ 2 = 0 := by linarith
      have e2 : K * pibar c pp pw t ^ 2 = 0 := by linarith
      simp only [mul_eq_zero, hay.ne', hK0.ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff] at e1 e2
      exact ⟨e1, e2⟩
    have hproj : ∀ t, pp t = projP c pp pw t ∧ pw t = projW c pp pw t := by
      intro t
      have e := (ht t).2
      simp only [pibar, projP, projW] at e ⊢
      constructor <;> field_simp at e ⊢ <;> linarith
    refine ⟨funext fun t => (ht t).1, funext fun t => ?_, funext fun t => ?_, hww⟩
    · rw [(hproj t).1, hpp]
    · rw [(hproj t).2, hpw]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact hopt

/-- Galí (2015), (28), p. 179: a bounded path has finite loss (`0 ≤ β < 1`, nonnegative
weights). -/
theorem finiteLoss_of_bounded {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1) (hay : 0 ≤ c.ay)
    (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {y pp pw : ℕ → ℝ} {A B C : ℝ} (hy : ∀ t, |y t| ≤ A)
    (hp : ∀ t, |pp t| ≤ B) (hq : ∀ t, |pw t| ≤ C) : FiniteLoss c y pp pw := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right ((c.ay * A ^ 2 + c.ap * B ^ 2 +
      c.aw * C ^ 2) / 2))
  have h1 : y t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy t) 2
  have h2 : pp t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hp t) 2
  have h3 : pw t ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hq t) 2
  unfold lossTerm
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have := mul_le_mul_of_nonneg_left h1 hay
  have := mul_le_mul_of_nonneg_left h2 hap
  have := mul_le_mul_of_nonneg_left h3 haw
  linarith

/-- **Galí (2015), §6.4.3, pp. 183–184 (THE OPTIMAL POLICY IN THE SPECIAL CASE, deterministic)**:
with `κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, `λ_p, λ_w > 0`, `0 < β < 1` and a bounded known path
`Δωⁿ`, the commitment problem has exactly one solution, and it has `ỹ ≡ 0` and `π̄ ≡ 0`. -/
theorem composite_targeting_existsUnique {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → ℝ} {Md : ℝ}
    (hdb : ∀ t, |dn t| ≤ Md) (w0 : ℝ) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsOptimal c dn w0 p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ p.1 = 0 ∧
        ∀ t, pibar c p.2.1 p.2.2.1 t = 0 := by
  obtain ⟨pp, pw, w, hP, hpi⟩ := Stoch.exists_composite_plan perfectForesight (c := c) hlp hlw
    hβ0 hβ1 (dn := fun t _ => dn t) (fun t _ => hdb t) (fun _ => rfl) (w0 := fun _ => w0)
    (M0 := |w0|) rfl (fun _ => le_rfl)
  obtain ⟨hc, -, -, -, -, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, -⟩ := hP
  set pp' : ℕ → ℝ := fun t => pp t () with hpp'
  set pw' : ℕ → ℝ := fun t => pw t () with hpw'
  set w' : ℕ → ℝ := fun t => w t () with hw'
  have hprev : ∀ t, prev (fun _ => w0) w t () = prev w0 w' t := fun t => by cases t <;> rfl
  have hf : Feasible c dn w0 0 pp' pw' w' := by
    intro t
    obtain ⟨e1, e2, e3⟩ := hc t
    have e1' := congrFun e1 ()
    have e2' := congrFun e2 ()
    have e3' := congrFun e3 ()
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hprev] at e1' e2' e3'
    simp only [mul_zero, add_zero] at e1' e2'
    refine ⟨?_, ?_, e3'⟩
    · simp only [Pi.zero_apply, mul_zero, add_zero]
      exact e1'
    · simp only [Pi.zero_apply, mul_zero, add_zero]
      exact e2'
  have hfl : FiniteLoss c 0 pp' pw' := by
    have hapos : 0 ≤ c.ap := by rw [hap]; positivity
    have hawpos : 0 ≤ c.aw := by rw [haw]; positivity
    exact finiteLoss_of_bounded hβ0.le hβ1 hay.le hapos hawpos (A := 0) (fun t => by simp)
      (fun t => hBp t ()) (fun t => hBq t ())
  have hpi' : ∀ t, pibar c pp' pw' t = 0 := fun t => by
    have := congrFun (hpi t) ()
    simpa [Stoch.pibar, pibar] using this
  obtain ⟨hopt, hiff⟩ := composite_targeting_optimal hk hlp hlw hβ0 hβ1 hay hε hap haw hf hfl hpi'
  refine ⟨(0, pp', pw', w'), ⟨hopt, rfl, hpi'⟩, ?_⟩
  rintro ⟨y, a, b, d⟩ ⟨h, -, -⟩
  obtain ⟨h1, h2, h3, h4⟩ := (hiff y a b d).1 h
  rw [h1, h2, h3, h4]

end Det

/-- Galí (2015), §6.4.3, p. 183: for the book's coefficients, the special case `ε_p = ε_w(1 − α)
= ε` gives `a_p = ε/λ_p`, `a_w = ε/λ_w`, and (fn. 6) `κ_p = κ_w` gives
`κ_p (λ_p + λ_w) = λ_p λ_w a_y`: the hypotheses of `Stoch.composite_foc`,
`Stoch.composite_targeting_solves` and `Det.composite_targeting_existsUnique`. -/
theorem book_special_case {β σ φ α εp εw lamP lamW ε : ℝ} (hα : α ≠ 1)
    (hεp : εp = ε) (hεw : εw * (1 - α) = ε)
    (hk : (bookCoef β σ φ α εp εw lamP lamW).kapP = (bookCoef β σ φ α εp εw lamP lamW).kapW) :
    (bookCoef β σ φ α εp εw lamP lamW).ap = ε / (bookCoef β σ φ α εp εw lamP lamW).lamP ∧
      (bookCoef β σ φ α εp εw lamP lamW).aw = ε / (bookCoef β σ φ α εp εw lamP lamW).lamW ∧
        (bookCoef β σ φ α εp εw lamP lamW).kapP *
            ((bookCoef β σ φ α εp εw lamP lamW).lamP + (bookCoef β σ φ α εp εw lamP lamW).lamW) =
          (bookCoef β σ φ α εp εw lamP lamW).lamP * (bookCoef β σ φ α εp εw lamP lamW).lamW *
            (bookCoef β σ φ α εp εw lamP lamW).ay := by
  refine ⟨by simp only [bookCoef, hεp], by simp only [bookCoef, hεw], ?_⟩
  have h := book_composite_slope (β := β) (σ := σ) (φ := φ) (εp := εp) (εw := εw)
    (lamP := lamP) (lamW := lamW) hα
  rw [← hk] at h
  simp only [bookCoef] at h ⊢
  linear_combination h

/-- **Galí (2015), p. 184 (what the book checks; survey error 2)**: the strict composite-targeting
path satisfies the conditions (34)–(35) (`π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})`, `ỹ_{−1} = 0`) trivially.
These are only NECESSARY conditions (obtained by eliminating the multipliers from (30)–(32)); the
book's "optimal since it satisfies the optimality conditions (34) and (35)" is completed by the
separation argument `Det.composite_targeting_optimal` / `Stoch.composite_targeting_optimal`. -/
theorem composite_path_satisfies_34_35 (c : Coef) (ε : ℝ) {pp pw : ℕ → ℝ}
    (hpi : ∀ t, Det.pibar c pp pw t = 0) (t : ℕ) :
    Det.pibar c pp pw t = -(1 / ε) * ((0 : ℕ → ℝ) t - prev 0 (0 : ℕ → ℝ) t) := by
  rw [hpi t]
  cases t <;> simp

end Gali.StickyWagesPrices.OptimalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.1: optimal monetary policy in a sticky wage economy

Galí (2015), Chapter 6, Exercise 6.1, pp. 194–195. A competitive firm with technology
`y_t = a_t + n_t` and flexible prices, productivity `a_t = ρ_a a_{t−1} + ε_t`, labour supply
`w_t − p_t = φ n_t`. (The book writes `ρ` both for the persistence of `a` and for the discount
rate in the IS equation of part (c); we write `ρa` for the former.)

## (a) Flexible wages and prices
* `firm_optimal_iff`, `labor_demand_log`: the competitive firm (profit `P A N − W N`) employs
  a positive amount of labour iff `W = P A`, i.e. exactly `w − p = a` in logs.
* `flexEq_iff`: the flexible equilibrium is `n = a/φ`, `y = (1 + φ) a/φ` (and `w − p = a`).

## (b) Two-period staggered wages
* `inflation_eq_iff`: given the reset wage
  `w*_t = ½(p_t + E_t p_{t+1}) + (φ/2)(n_t + E_t n_{t+1})` and `p = w − a`, the wage index
  `w_t = ½(w*_t + w*_{t−1})` holds at a date **iff** inflation satisfies
  `π_t = E_t π_{t+1} + φ ň_t + u_t`, `ň_t = n_{t−1} + E_{t−1} n_t + n_t + E_t n_{t+1}`,
  `u_t = −4 a_t − (p_t − E_{t−1} p_t)` (exact; the book only asks for "⇒").

## (c) Optimal policy: replicating the flexible allocation
* `drift_const_of_bounded`: a general lemma (not in the core): a bounded adapted `z` with
  `E_t z_{t+1} − z_t = z_t − z_{t−1}` is constant.
* `optimal_unique`: in every sticky-wage equilibrium with the flexible allocation `n = a/φ`
  and a bounded adapted reset wage, the reset and average wages are constant (`π^w ≡ 0`),
  `p_t = w̄ − a_t`, price inflation is `π_t = −Δa_t`, and the nominal rate is
  `i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`.
* `optimal_exists`: conversely, for every initial reset wage `w̄` known at date 0 these
  processes form a sticky-wage equilibrium with the flexible allocation (existence).
-/

namespace Gali.StickyWagesPrices.Ex6_1

/-! ### (a) The firm and the flexible equilibrium -/

/-- Galí (2015), Exercise 6.1, p. 194 (competitive firm, `Y = A N`): a positive employment
level `N` maximises profit `P A N' − W N'` over `N' ≥ 0` iff `W = P A`. -/
theorem firm_optimal_iff {P A W N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → P * A * N' - W * N' ≤ P * A * N - W * N) ↔ W = P * A := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    have h2 := h (2 * N) (by positivity)
    have e : (P * A - W) * N = 0 := by nlinarith
    rcases mul_eq_zero.mp e with e | e
    · linarith
    · linarith
  · intro hW N' _
    rw [hW, sub_self, sub_self]

/-- Galí (2015), Exercise 6.1, p. 194: the condition `W = P A` is exactly `w − p = a` in
logs. -/
theorem labor_demand_log {P A W : ℝ} (hP : 0 < P) (hA : 0 < A) (hW : 0 < W) :
    W = P * A ↔ Real.log W - Real.log P = Real.log A := by
  constructor
  · intro h
    rw [h, Real.log_mul hP.ne' hA.ne']
    ring
  · intro h
    have e : Real.log W = Real.log (P * A) := by
      rw [Real.log_mul hP.ne' hA.ne']
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hW) (Set.mem_Ioi.mpr (mul_pos hP hA)) e

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.1(a), p. 194: the flexible wage and price equilibrium:
technology `y = a + n`, labour supply `w − p = φ n`, competitive labour demand `w − p = a`. -/
def FlexEq (φ : ℝ) (a n y w p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = a t + n t ∧ w t - p t = φ • n t ∧ w t - p t = a t

/-- Galí (2015), Exercise 6.1(a), p. 194 (**necessary and sufficient**): the flexible
equilibrium is `n_t = a_t/φ`, `y_t = (1 + φ) a_t/φ`, with real wage `w_t − p_t = a_t`. -/
theorem flexEq_iff {φ : ℝ} (hφ : φ ≠ 0) {a n y w p : ℕ → Ω → ℝ} :
    FlexEq φ a n y w p ↔
      ∀ t, n t = φ⁻¹ • a t ∧ y t = ((1 + φ) / φ) • a t ∧ w t - p t = a t := by
  refine forall_congr' fun t => ?_
  constructor
  · rintro ⟨hy, hs, hd⟩
    have hn : n t = φ⁻¹ • a t := by
      funext ω
      have e1 := congrFun hs ω
      have e2 := congrFun hd ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hφ]
      linarith
    refine ⟨hn, ?_, hd⟩
    funext ω
    have e1 := congrFun hy ω
    have e2 := congrFun hn ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
    field_simp
    ring
  · rintro ⟨hn, hy, hd⟩
    refine ⟨?_, ?_, hd⟩
    · funext ω
      have e1 := congrFun hy ω
      have e2 := congrFun hn ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2]
      field_simp
      ring
    · rw [hd, hn, smul_smul, mul_inv_cancel₀ hφ, one_smul]

/-! ### (b) Two-period staggered wages -/

/-- Galí (2015), Exercise 6.1(b), p. 194: the reset wage
`w*_t = ½(p_t + E_t p_{t+1}) + (φ/2)(n_t + E_t n_{t+1})`. -/
def ResetWage (φ : ℝ) (p n wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wstar t = (1 / 2 : ℝ) • (p t + 𝔼.E t (p (t + 1))) + (φ / 2) • (n t + 𝔼.E t (n (t + 1)))

/-- Galí (2015), Exercise 6.1(b), p. 194: the average wage `w_t = ½(w*_t + w*_{t−1})`
(stated from date 1 on). -/
def WageIndex (w wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = (1 / 2 : ℝ) • (wstar (t + 1) + wstar t)

/-- Galí (2015), Exercise 6.1, p. 194: flexible prices and a competitive firm, `p = w − a`. -/
def PriceEq (a w p : ℕ → Ω → ℝ) : Prop := ∀ t, p t = w t - a t

/-- Galí (2015), Exercise 6.1(b), p. 195: `ň_{t+1} = n_t + E_t n_{t+1} + n_{t+1} +
E_{t+1} n_{t+2}` (the book's `ň_t` one period later). -/
def nCheck (n : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  n t + 𝔼.E t (n (t + 1)) + n (t + 1) + 𝔼.E (t + 1) (n (t + 1 + 1))

/-- Galí (2015), Exercise 6.1(b), p. 195: `u_{t+1} = −4 a_{t+1} − (p_{t+1} − E_t p_{t+1})`. -/
def uShock (a p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -(4 : ℝ) • a (t + 1) - (p (t + 1) - 𝔼.E t (p (t + 1)))

/-- Galí (2015), Exercise 6.1(b), p. 195 (**necessary and sufficient**): with the reset wage
rule and `p = w − a`, the wage index `w_{t+1} = ½(w*_{t+1} + w*_t)` holds iff
`π_{t+1} = E_{t+1} π_{t+2} + φ ň_{t+1} + u_{t+1}`. -/
theorem inflation_eq_iff {φ : ℝ} {a n w p wstar : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p)
    (hr : ResetWage 𝔼 φ p n wstar) (hpe : PriceEq a w p) (t : ℕ) :
    w (t + 1) = (1 / 2 : ℝ) • (wstar (t + 1) + wstar t) ↔
      p (t + 1) - p t = 𝔼.E (t + 1) (p (t + 1 + 1) - p (t + 1)) + φ • nCheck 𝔼 n t +
        uShock 𝔼 a p t := by
  have hE : 𝔼.E (t + 1) (p (t + 1 + 1) - p (t + 1)) =
      𝔼.E (t + 1) (p (t + 1 + 1)) - p (t + 1) := by
    rw [map_sub, hp (t + 1)]
  rw [hE]
  have h0 := hr t
  have h1 := hr (t + 1)
  have hw := hpe (t + 1)
  constructor
  · intro h
    funext ω
    have e0 := congrFun h0 ω
    have e1 := congrFun h1 ω
    have e2 := congrFun hw ω
    have e3 := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nCheck,
      uShock] at e0 e1 e2 e3 ⊢
    linarith
  · intro h
    funext ω
    have e0 := congrFun h0 ω
    have e1 := congrFun h1 ω
    have e2 := congrFun hw ω
    have e3 := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nCheck,
      uShock] at e0 e1 e2 e3 ⊢
    linarith

/-! ### (c) Optimal policy -/

/-- Galí (2015), Exercise 6.1(c), p. 195: the dynamic IS equation
`y_t = −σ⁻¹(i_t − E_t π_{t+1} − ρ) + E_t y_{t+1}`, with `E_t π_{t+1} = E_t p_{t+1} − p_t`. -/
def IS (σ ρ : ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = -(σ⁻¹ • (i t - (𝔼.E t (p (t + 1)) - p t) - fun _ => ρ)) + 𝔼.E t (y (t + 1))

/-- Galí (2015), Exercise 6.1(b)–(c), pp. 194–195: an equilibrium of the sticky-wage economy
(technology, `p = w − a`, reset wage, wage index, IS equation). -/
def StickyEq (φ σ ρ : ℝ) (a n y w p wstar i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = a t + n t) ∧ PriceEq a w p ∧ ResetWage 𝔼 φ p n wstar ∧ WageIndex w wstar ∧
    IS 𝔼 σ ρ y p i

/-- Galí (2015), Exercise 6.1(c), p. 195 (general lemma, proved here): a bounded adapted
process whose expected change equals its last change, `E_{t+1} z_{t+2} − z_{t+1} =
z_{t+1} − z_t`, is constant. (Its expected path is linear, `E_{t+1} z_{t+1+k} =
z_{t+1} + k (z_{t+1} − z_t)`, and is bounded only with zero slope.) -/
theorem drift_const_of_bounded {z : ℕ → Ω → ℝ} (hza : 𝔼.Adapted z) (hzb : BoundedProc z)
    (hz : ∀ t, 𝔼.E (t + 1) (z (t + 1 + 1)) - z (t + 1) = z (t + 1) - z t) (t : ℕ) :
    z (t + 1) = z t := by
  obtain ⟨M, hM⟩ := hzb
  -- expected increments are constant
  have hinc : ∀ k, 𝔼.E (t + 1) (z (t + 1 + k + 1) - z (t + 1 + k)) = z (t + 1) - z t := by
    intro k
    induction k with
    | zero =>
      rw [map_sub, hza (t + 1)]
      simpa using hz t
    | succ k ih =>
      have hk := hz (t + 1 + k)
      have hk' : z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1)) =
          𝔼.E (t + 1 + k + 1) (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1)) +
            (z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1)) -
              𝔼.E (t + 1 + k + 1) (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1))) := by abel
      have hle : t + 1 ≤ t + 1 + k + 1 := by omega
      have hex : 𝔼.E (t + 1) (z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1))) =
          𝔼.E (t + 1) (𝔼.E (t + 1 + k + 1)
            (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1))) := by
        rw [𝔼.tower hle]
        rfl
      rw [hex, map_sub (𝔼.E (t + 1 + k + 1)), hza (t + 1 + k + 1), hk, ← ih]
  -- expected levels are linear in the horizon
  have hlev : ∀ k : ℕ, 𝔼.E (t + 1) (z (t + 1 + k)) = z (t + 1) + (k : ℝ) • (z (t + 1) - z t) := by
    intro k
    induction k with
    | zero => simpa using hza (t + 1)
    | succ k ih =>
      have hs : z (t + 1 + (k + 1)) = z (t + 1 + k) + (z (t + 1 + k + 1) - z (t + 1 + k)) := by
        rw [← add_assoc]; abel
      rw [hs, map_add, ih, hinc k]
      push_cast
      rw [add_smul, one_smul]
      abel
  funext ω
  by_contra hne
  have hd : z (t + 1) ω - z t ω ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / |z (t + 1) ω - z t ω|)
  have hb := 𝔼.abs_E_le (hM (t + 1 + k)) (t + 1) ω
  rw [hlev k] at hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hb
  have h1 := hM (t + 1) ω
  have hpos : 0 < |z (t + 1) ω - z t ω| := abs_pos.mpr hd
  have hkd : 2 * M < (k : ℝ) * |z (t + 1) ω - z t ω| := by
    rwa [div_lt_iff₀ hpos] at hk
  have htri : (k : ℝ) * |z (t + 1) ω - z t ω| ≤
      |z (t + 1) ω + (k : ℝ) * (z (t + 1) ω - z t ω)| + |z (t + 1) ω| := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkabs : (k : ℝ) * |z (t + 1) ω - z t ω| = |(k : ℝ) * (z (t + 1) ω - z t ω)| := by
      rw [abs_mul, abs_of_nonneg hk0]
    rw [hkabs]
    calc |(k : ℝ) * (z (t + 1) ω - z t ω)|
        = |(z (t + 1) ω + (k : ℝ) * (z (t + 1) ω - z t ω)) - z (t + 1) ω| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith

/-- Galí (2015), Exercise 6.1(c), p. 195: the nominal rate under the optimal policy,
`i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`. -/
noncomputable def iOpt (σ ρ φ ρa : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + ((1 - ρa) * (1 - σ * (1 + φ) / φ)) • a t

/-- Galí (2015), Exercise 6.1(c), p. 195 (**uniqueness**): in a sticky-wage equilibrium that
replicates the flexible allocation `n = a/φ`, with a bounded adapted reset wage, the reset
wage and the average wage are constant at `w̄ = w*_0` (zero wage inflation), the price level
is `p_t = w̄ − a_t`, price inflation is `π_{t+1} = −(a_{t+1} − a_t)`, and the nominal rate is
`i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`. -/
theorem optimal_unique {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a n y w p wstar i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (heq : StickyEq 𝔼 φ σ ρ a n y w p wstar i) (hflex : ∀ t, n t = φ⁻¹ • a t)
    (hza : 𝔼.Adapted wstar) (hzb : BoundedProc wstar) :
    ∀ t, wstar t = wstar 0 ∧ w t = wstar 0 ∧ w (t + 1) - w t = 0 ∧ p t = wstar 0 - a t ∧
      p (t + 1) - p t = -(a (t + 1) - a t) ∧ i t = iOpt σ ρ φ ρa a t := by
  obtain ⟨hy, hpe, hr, hwi, his⟩ := heq
  -- the reset wage in terms of the average wage
  have hrw : ∀ t, wstar t = (1 / 2 : ℝ) • (w t + 𝔼.E t (w (t + 1))) := by
    intro t
    rw [hr t, hflex t, hflex (t + 1), hpe t, hpe (t + 1)]
    funext ω
    simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdrift : ∀ t, 𝔼.E (t + 1) (wstar (t + 1 + 1)) - wstar (t + 1) =
      wstar (t + 1) - wstar t := by
    intro t
    have e1 := hrw (t + 1)
    rw [hwi (t + 1), hwi t, map_smul, map_add, hza (t + 1)] at e1
    funext ω
    have e := congrFun e1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  have hconst : ∀ t, wstar t = wstar 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [drift_const_of_bounded 𝔼 hza hzb hdrift t, ih]
  have hz0 : ∀ t, 𝔼.E t (wstar 0) = wstar 0 := fun t => by
    rw [← hza 0, 𝔼.known (Nat.zero_le t)]
  have hw1 : ∀ t, w (t + 1) = wstar 0 := fun t => by
    rw [hwi t, hconst (t + 1), hconst t]
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hw : ∀ t, w t = wstar 0 := by
    intro t
    cases t with
    | succ t => exact hw1 t
    | zero =>
      have e := hrw 0
      rw [hw1 0, hz0 0] at e
      funext ω
      have e' := congrFun e ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
      linarith
  have hp : ∀ t, p t = wstar 0 - a t := fun t => by rw [hpe t, hw t]
  intro t
  refine ⟨hconst t, hw t, by rw [hw, hw, sub_self], hp t, by rw [hp, hp]; abel, ?_⟩
  -- the nominal rate from the IS equation
  have e := his t
  rw [hy t, hy (t + 1), hflex t, hflex (t + 1), hp t, hp (t + 1), map_sub, hz0 t, map_add,
    map_smul, ha.2 t] at e
  funext ω
  have e' := congrFun e ω
  unfold iOpt
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  field_simp at e' ⊢
  linear_combination e'

/-- Galí (2015), Exercise 6.1(c), p. 195 (**existence**): for every initial reset wage `w̄`
known at date 0, constant wages `w* = w = w̄`, prices `p_t = w̄ − a_t`, the flexible
allocation `n = a/φ`, `y = (1 + φ) a/φ` and the rate `iOpt` form a sticky-wage equilibrium. -/
theorem optimal_exists {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    StickyEq 𝔼 φ σ ρ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun _ => c)
      (fun t => c - a t) (fun _ => c) (iOpt σ ρ φ ρa a) := by
  have hcE : ∀ t, 𝔼.E t c = c := fun t => by rw [← hc, 𝔼.known (Nat.zero_le t)]
  refine ⟨fun t => ?_, fun t => rfl, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [map_smul, map_sub, hcE t, ha.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  · rw [map_sub, hcE t, map_smul, ha.2 t]
    funext ω
    unfold iOpt
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
    ring

end Gali.StickyWagesPrices.Ex6_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.2: optimal monetary policy with wages set in advance

Galí (2015), Chapter 6, Exercise 6.2, pp. 195–196. A competitive firm with `y_t = a_t + n_t`
and flexible prices (so `p = w − a`, `firm_optimal_iff` in `Ex6_1`), productivity
`a_t = ρ_a a_{t−1} + ε^a_t`, labour supply `w − p = φ n`, and the dynamic IS equation
`y_t = −σ⁻¹(i_t − E_t π_{t+1} − ρ) + E_t y_{t+1}`. Dates are `t + 1` for `t : ℕ`; date-0
values are initial conditions, and the book's `E_{t−1}` is `E_t` applied to date-`t + 1`
variables.

## (a) Flexible wages and prices
* `flex_iff`: equilibrium ⇔ `n = a/φ`, `y = (1 + φ) a/φ`, `w − p = a` and the real rate equals
  the natural rate `r_t = ρ + σ(1 + φ)(ρ_a − 1) a_t/φ` (`rnat`).
* `flex_any_price`, `flex_two_equilibria`: nominal indeterminacy — every price path is an
  equilibrium path; two equilibria with different inflation and nominal rates are exhibited.

## (b) Wages set in advance
`WageInAdvance`: `w_t = E_{t−1} p_t + φ E_{t−1} n_t`. Part (b) poses no question (survey
error 9); it only introduces this rule.

## (c) The simple rule `i_t = ρ + φ_π π_t`
* `wage_facts`: under any policy, `E_{t−1} n_t = ρ_a a_{t−1}/φ`,
  `p_t − E_{t−1} p_t = −ε^a_t`, and the real wage is `w_t − p_t = a_t`.
* `expected_IS`, `n_from_IS`: the IS equation in expectation and solved for employment.
* `taylor_unique`: for `φ_π > 1`, `|ρ_a| < 1`, bounded `a`, every equilibrium with bounded
  inflation has `E_{t−1} π_t = γ a_{t−1}`, `π_t = γ a_{t−1} − ε^a_t`,
  `n_t = a_t/φ + c_ε ε^a_t`, `y_t = (1 + φ) a_t/φ + c_ε ε^a_t`, `w_t − p_t = a_t`,
  `γ = K ρ_a/(φ_π − ρ_a)`, `c_ε = φ_π (K + φ_π − ρ_a)/(σ(φ_π − ρ_a))`, `K = σ(1 + φ)(ρ_a − 1)/φ`.
* `taylor_exists`: this equilibrium exists (for any initial price level known at date 0)
  and has bounded inflation.

## (d) Optimal policy
* `optimal_real_rate`: in any equilibrium replicating the (efficient, by the exercise's
  assumption) flexible allocation `n = a/φ`, the real rate is the natural rate; the
  allocation is feasible under sticky wages (`optimal_exists`).
* `optimal_unique`, `optimal_exists`: the rule `i_t = r_t + φ_π E_{t−1} π_t` (natural rate
  plus a response to *expected* inflation) with `φ_π > 1` implements it as the unique
  equilibrium with bounded inflation: `n = a/φ`, `E_{t−1} π_t = 0`, `π_t = −ε^a_t`.
-/

namespace Gali.StickyWagesPrices.Ex6_2

open Gali.StickyWagesPrices.Ex6_1

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.2(a), p. 195: the slope `K = σ(1 + φ)(ρ_a − 1)/φ` of the natural
real rate in productivity. -/
noncomputable def Kc (σ φ ρa : ℝ) : ℝ := σ * (1 + φ) * (ρa - 1) / φ

/-- Galí (2015), Exercise 6.2(a), p. 195: the natural real rate
`r_t = ρ + σ(1 + φ)(ρ_a − 1) a_t/φ`. -/
noncomputable def rnat (σ ρ φ ρa : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + Kc σ φ ρa • a t

/-- Galí (2015), Exercise 6.2, p. 195: expected inflation `E_t π_{t+1} = E_t p_{t+1} − p_t`. -/
def qE (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (p (t + 1)) - p t

/-! ### (a) Flexible wages and prices -/

/-- Galí (2015), Exercise 6.2(a), p. 195 (**necessary and sufficient**): the flexible
equilibrium has `n = a/φ`, `y = (1 + φ) a/φ`, `w − p = a`, and the real rate
`i_t − E_t π_{t+1}` equals the natural rate `ρ + σ(1 + φ)(ρ_a − 1) a_t/φ`. -/
theorem flex_iff {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    (FlexEq φ a n y w p ∧ IS 𝔼 σ ρ y p i) ↔
      (∀ t, n t = φ⁻¹ • a t ∧ y t = ((1 + φ) / φ) • a t ∧ w t - p t = a t) ∧
        ∀ t, i t - qE 𝔼 p t = rnat σ ρ φ ρa a t := by
  rw [flexEq_iff hφ]
  refine and_congr_right fun hf => ?_
  have hy : ∀ t, y t = ((1 + φ) / φ) • a t := fun t => (hf t).2.1
  constructor
  · intro his t
    have e := his t
    rw [hy t, hy (t + 1), map_smul, ha.2 t] at e
    funext ω
    have e' := congrFun e ω
    unfold qE rnat Kc
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
    linear_combination (norm := skip) σ * e'
    field_simp
    ring
  · intro hr t
    rw [hy t, hy (t + 1), map_smul, ha.2 t]
    have e := hr t
    funext ω
    have e' := congrFun e ω
    unfold qE rnat Kc at e'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
    linear_combination (norm := skip) σ⁻¹ * e'
    field_simp
    ring

/-- Galí (2015), Exercise 6.2(a), p. 196 (**nominal indeterminacy**): for every price path
`p`, the flexible allocation with `w = p + a` and `i_t = r_t + E_t π_{t+1}` is an
equilibrium. -/
theorem flex_any_price {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (p : ℕ → Ω → ℝ) :
    FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p t + a t) p ∧
      IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p
        (fun t => rnat σ ρ φ ρa a t + qE 𝔼 p t) :=
  (flex_iff 𝔼 hφ hσ ha).mpr ⟨fun t => ⟨rfl, rfl, by abel⟩, fun t => by abel⟩

/-- Galí (2015), Exercise 6.2(a), p. 196 (**two distinct equilibria**): with a constant price
level and with prices rising one-for-one (`p_t = t`) the real allocation is the same, but
inflation and the nominal rate differ, so they are not determined. -/
theorem flex_two_equilibria [Nonempty Ω] {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    ∃ p₁ p₂ i₁ i₂ : ℕ → Ω → ℝ,
      (FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p₁ t + a t)
          p₁ ∧ IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p₁ i₁) ∧
      (FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p₂ t + a t)
          p₂ ∧ IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p₂ i₂) ∧
      p₁ 1 - p₁ 0 ≠ p₂ 1 - p₂ 0 ∧ i₁ 0 ≠ i₂ 0 := by
  refine ⟨fun _ _ => 0, fun t _ => (t : ℝ), _, _, flex_any_price 𝔼 hφ hσ ha _,
    flex_any_price 𝔼 hφ hσ ha _, ?_, ?_⟩
  · intro h
    have := congrFun h (Classical.arbitrary Ω)
    simp at this
  · intro h
    have := congrFun h (Classical.arbitrary Ω)
    have hc := 𝔼.const 0 (1 : ℝ)
    have hz := 𝔼.const 0 (0 : ℝ)
    unfold qE at this
    simp only [zero_add, Nat.cast_one, Nat.cast_zero, Pi.add_apply,
      Pi.sub_apply] at this
    rw [hc, hz] at this
    norm_num at this

/-! ### (b) Wages set in advance -/

/-- Galí (2015), Exercise 6.2(b), p. 196: nominal wages set at the end of the previous period,
`w_t = E_{t−1} p_t + φ E_{t−1} n_t` (stated for dates `t + 1`). Part (b) itself asks no
question (survey error 9): it only introduces this rule, used in (c) and (d). -/
def WageInAdvance (φ : ℝ) (p n w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = 𝔼.E t (p (t + 1)) + φ • 𝔼.E t (n (t + 1))

/-- Galí (2015), Exercise 6.2, p. 195: the IS equation from date 1 on,
`y_{t+1} = −σ⁻¹(i_{t+1} − E_{t+1} π_{t+2} − ρ) + E_{t+1} y_{t+2}`. -/
def ISfwd (σ ρ : ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y (t + 1) = -(σ⁻¹ • (i (t + 1) - qE 𝔼 p (t + 1) - fun _ => ρ)) +
    𝔼.E (t + 1) (y (t + 1 + 1))

/-- Galí (2015), Exercise 6.2(b)–(d), pp. 195–196: the sticky-wage economy (technology,
`p = w − a`, wages set in advance, IS equation), before monetary policy is specified. -/
def Block (φ σ ρ : ℝ) (a n y w p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = a t + n t) ∧ PriceEq a w p ∧ WageInAdvance 𝔼 φ p n w ∧ ISfwd 𝔼 σ ρ y p i

/-! ### (c) The simple rule -/

/-- Galí (2015), Exercise 6.2(c), p. 196 (key facts, under any policy): with wages set in
advance, `E_t n_{t+1} = ρ_a a_t/φ`, `p_{t+1} − E_t p_{t+1} = −ε^a_{t+1}` and the real wage is
`w_t − p_t = a_t`. -/
theorem wage_facts {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (n (t + 1)) = (ρa / φ) • a t ∧
      p (t + 1) - 𝔼.E t (p (t + 1)) = -(a (t + 1) - ρa • a t) ∧ w t - p t = a t := by
  obtain ⟨_, hpe, hw, _⟩ := hb
  have hwE : 𝔼.E t (w (t + 1)) = w (t + 1) := by
    rw [hw t, map_add, map_smul, 𝔼.E_E_self, 𝔼.E_E_self]
  have hpE : 𝔼.E t (p (t + 1)) = w (t + 1) - ρa • a t := by
    rw [hpe (t + 1), map_sub, hwE, ha.2 t]
  refine ⟨?_, ?_, by rw [hpe t]; abel⟩
  · have e := hw t
    rw [hpE] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp
    linarith
  · rw [hpE, hpe (t + 1)]
    abel

/-- Galí (2015), Exercise 6.2(c), p. 196: expected output, `E_t y_{t+1} = (1 + φ)ρ_a a_t/φ`. -/
theorem expected_y {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (y (t + 1)) = ((1 + φ) / φ * ρa) • a t := by
  rw [hb.1 (t + 1), map_add, ha.2 t, (wage_facts 𝔼 hφ ha hb t).1, ← add_smul]
  congr 1
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the IS equation in expectation,
`E_t i_{t+1} − ρ − E_t E_{t+1} π_{t+2} = K ρ_a a_t`, under any policy. -/
theorem expected_IS {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (i (t + 1)) - (fun _ => ρ) - 𝔼.E t (qE 𝔼 p (t + 1)) = (Kc σ φ ρa * ρa) • a t := by
  have e := congrArg (𝔼.E t) (hb.2.2.2 t)
  have hEy2 : 𝔼.E t (y (t + 1 + 1)) = ((1 + φ) / φ * ρa * ρa) • a t := by
    rw [← 𝔼.tower (Nat.le_succ t), expected_y 𝔼 hφ ha hb (t + 1), map_smul, ha.2 t, smul_smul]
  rw [map_add, 𝔼.tower (Nat.le_succ t), hEy2, map_neg, map_smul, map_sub, map_sub, 𝔼.const,
    expected_y 𝔼 hφ ha hb t] at e
  funext ω
  have e' := congrFun e ω
  unfold Kc
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  linear_combination (norm := skip) σ * e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the IS equation solved for employment,
`n_{t+1} = a_{t+1}/φ + (K/σ) a_{t+1} − σ⁻¹(i_{t+1} − E_{t+1} π_{t+2} − ρ)`. -/
theorem n_from_IS {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    n (t + 1) = φ⁻¹ • a (t + 1) + (Kc σ φ ρa / σ) • a (t + 1) -
      σ⁻¹ • (i (t + 1) - qE 𝔼 p (t + 1) - fun _ => ρ) := by
  have e := hb.2.2.2 t
  rw [expected_y 𝔼 hφ ha hb (t + 1), hb.1 (t + 1)] at e
  funext ω
  have e' := congrFun e ω
  unfold Kc
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  linear_combination (norm := skip) e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c), p. 196: the simple rule `i_t = ρ + φ_π π_t` (from date 1). -/
def TaylorRule (ρ φπ : ℝ) (p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = (fun _ => ρ) + φπ • (p (t + 1) - p t)

/-- Galí (2015), Exercise 6.2(c), p. 196: the response of expected inflation to productivity,
`γ = K ρ_a/(φ_π − ρ_a)`. -/
noncomputable def gam (σ φ ρa φπ : ℝ) : ℝ := Kc σ φ ρa * ρa / (φπ - ρa)

/-- Galí (2015), Exercise 6.2(c), p. 196: the response of employment to the productivity
innovation, `c_ε = φ_π (K + φ_π − ρ_a)/(σ(φ_π − ρ_a))`. -/
noncomputable def cEps (σ φ ρa φπ : ℝ) : ℝ :=
  φπ * (Kc σ φ ρa + φπ - ρa) / (σ * (φπ - ρa))

/-- Galí (2015), Exercise 6.2(c), p. 196: expected inflation is bounded when inflation is. -/
theorem qE_bounded {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) {M : ℝ}
    (hM : ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) : BoundedProc (qE 𝔼 p) := by
  refine ⟨M, fun t ω => ?_⟩
  have h : qE 𝔼 p t = 𝔼.E t (p (t + 1) - p t) := by rw [map_sub, hp t]; rfl
  rw [h]
  exact 𝔼.abs_E_le (fun ω' => by simpa using hM t ω') t ω

/-- Galí (2015), Exercise 6.2(c), p. 196 (**uniqueness**): under `i_t = ρ + φ_π π_t` with
`φ_π > 1`, `|ρ_a| < 1` and bounded productivity, every equilibrium with bounded inflation has
`E_t π_{t+1} = γ a_t`, `π_{t+1} = γ a_t − ε^a_{t+1}`, `n_{t+1} = a_{t+1}/φ + c_ε ε^a_{t+1}`,
`y_{t+1} = (1 + φ) a_{t+1}/φ + c_ε ε^a_{t+1}`, real wage `w_t − p_t = a_t`, and nominal rate
`i_{t+1} = ρ + φ_π (γ a_t − ε^a_{t+1})`. -/
theorem taylor_unique {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hφπ : 1 < φπ)
    (hρa : |ρa| < 1) {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hp : 𝔼.Adapted p) (hπb : ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M)
    (hb : Block 𝔼 φ σ ρ a n y w p i) (hr : TaylorRule ρ φπ p i) :
    ∀ t, qE 𝔼 p t = gam σ φ ρa φπ • a t ∧
      p (t + 1) - p t = gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t) ∧
      n (t + 1) = φ⁻¹ • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) ∧
      y (t + 1) = ((1 + φ) / φ) • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) ∧
      w t - p t = a t ∧
      i (t + 1) = (fun _ => ρ) + φπ • (gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t)) := by
  obtain ⟨M, hM⟩ := hπb
  have hφπ0 : φπ ≠ 0 := by positivity
  have hd : φπ - ρa ≠ 0 := by
    have := (abs_lt.mp hρa).2
    linarith
  -- the forward equation for expected inflation
  have hq : ∀ t, qE 𝔼 p t = φπ⁻¹ • 𝔼.E t (qE 𝔼 p (t + 1)) +
      (Kc σ φ ρa * ρa / φπ) • a t := by
    intro t
    have e := expected_IS 𝔼 hφ hσ ha hb t
    rw [hr t, map_add, 𝔼.const, map_smul, map_sub, hp t,
      show 𝔼.E t (p (t + 1)) - p t = qE 𝔼 p t from rfl] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp
    linarith
  have hg : ∀ t, gam σ φ ρa φπ • a t = φπ⁻¹ • 𝔼.E t (gam σ φ ρa φπ • a (t + 1)) +
      (Kc σ φ ρa * ρa / φπ) • a t := by
    intro t
    rw [map_smul, ha.2 t]
    funext ω
    unfold gam
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hinv : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φπ)]
    exact inv_lt_one_of_one_lt₀ hφπ
  have hgb : BoundedProc fun t => gam σ φ ρa φπ • a t := by
    obtain ⟨B, hB⟩ := hab
    refine ⟨|gam σ φ ρa φπ| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
  have hqe : qE 𝔼 p = fun t => gam σ φ ρa φπ • a t :=
    𝔼.forward_unique hinv hq hg (qE_bounded 𝔼 hp hM) hgb
  have hqt : ∀ t, qE 𝔼 p t = gam σ φ ρa φπ • a t := fun t => by rw [hqe]
  have hπ : ∀ t, p (t + 1) - p t = gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t) := by
    intro t
    have e := (wage_facts 𝔼 hφ ha hb t).2.1
    calc p (t + 1) - p t = (𝔼.E t (p (t + 1)) - p t) + (p (t + 1) - 𝔼.E t (p (t + 1))) := by
          abel
      _ = gam σ φ ρa φπ • a t + -(a (t + 1) - ρa • a t) := by
          rw [e, show 𝔼.E t (p (t + 1)) - p t = qE 𝔼 p t from rfl, hqt t]
      _ = _ := by rw [← sub_eq_add_neg]
  have hn : ∀ t, n (t + 1) = φ⁻¹ • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) := by
    intro t
    rw [n_from_IS 𝔼 hφ hσ ha hb t, hr t, hπ t, hqt (t + 1)]
    funext ω
    unfold cEps gam
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  intro t
  refine ⟨hqt t, hπ t, hn t, ?_, (wage_facts 𝔼 hφ ha hb t).2.2, by rw [hr t, hπ t]⟩
  rw [hb.1 (t + 1), hn t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Exercise 6.2, p. 195: the productivity innovation `ε^a_{t+1} =
a_{t+1} − ρ_a a_t` (zero at date 0). -/
def innov (ρa : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => a (t + 1) - ρa • a t

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the price path `p_{t+1} = p_t + g a_t −
ε^a_{t+1}` from the initial price level `p_0 = c`. -/
def pPath (g ρa : ℝ) (a : ℕ → Ω → ℝ) (c : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => c
  | t + 1 => pPath g ρa a c t + g • a t - innov ρa a (t + 1)

/-- Galí (2015), Exercise 6.2, p. 195: the innovation is known at its date. -/
theorem innov_adapted {ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    𝔼.Adapted (innov ρa a) := by
  intro t
  cases t with
  | zero => exact map_zero _
  | succ t =>
    simp only [innov]
    rw [map_sub, map_smul, ha.1 (t + 1), ← ha.1 t, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.2, p. 195: the innovation is unforecastable, `E_t ε^a_{t+1} = 0`. -/
theorem innov_E {ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    𝔼.E t (innov ρa a (t + 1)) = 0 := by
  simp only [innov]
  rw [map_sub, map_smul, ha.2 t, ha.1 t, sub_self]

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the price path is adapted. -/
theorem pPath_adapted {g ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ}
    (hc : 𝔼.E 0 c = c) : 𝔼.Adapted (pPath g ρa a c) := by
  intro t
  induction t with
  | zero => exact hc
  | succ t ih =>
    simp only [pPath]
    rw [map_sub, map_add, map_smul, innov_adapted 𝔼 ha (t + 1), ← ih, ← ha.1 t,
      𝔼.known (Nat.le_succ t), 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: along the price path, `E_t p_{t+1} = p_t + g a_t`. -/
theorem pPath_E {g ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ}
    (hc : 𝔼.E 0 c = c) (t : ℕ) :
    𝔼.E t (pPath g ρa a c (t + 1)) = pPath g ρa a c t + g • a t := by
  simp only [pPath]
  rw [map_sub, map_add, map_smul, innov_E 𝔼 ha t, pPath_adapted 𝔼 ha hc t, ha.1 t, sub_zero]

/-- Galí (2015), Exercise 6.2(c), p. 196 (**existence**): for every initial price level known
at date 0, the closed-form processes of `taylor_unique` (`p_{t+1} = p_t + γ a_t − ε^a_{t+1}`,
`w = p + a`, `n = a/φ + c_ε ε^a`, `y = a + n`, `i_{t+1} = ρ + φ_π π_{t+1}`) are an equilibrium
under the simple rule, with adapted prices and, for bounded `a`, bounded inflation. -/
theorem taylor_exists {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hd : φπ - ρa ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    let p := pPath (gam σ φ ρa φπ) ρa a c
    let n := fun t => φ⁻¹ • a t + cEps σ φ ρa φπ • innov ρa a t
    Block 𝔼 φ σ ρ a n (fun t => a t + n t) (fun t => p t + a t) p
        (fun t => (fun _ => ρ) + φπ • (p t - p (t - 1))) ∧
      TaylorRule ρ φπ p (fun t => (fun _ => ρ) + φπ • (p t - p (t - 1))) ∧ 𝔼.Adapted p ∧
      (BoundedProc a → ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) := by
  intro p n
  have hpE := pPath_E (g := gam σ φ ρa φπ) 𝔼 ha hc
  refine ⟨⟨fun t => rfl, fun t => (add_sub_cancel_right (p t) (a t)).symm, fun t => ?_,
    fun t => ?_⟩, fun t => rfl,
    pPath_adapted 𝔼 ha hc, ?_⟩
  · -- wages set in advance
    have hnE : 𝔼.E t (n (t + 1)) = (φ⁻¹ * ρa) • a t := by
      simp only [n]
      rw [map_add, map_smul, map_smul, ha.2 t, innov_E 𝔼 ha t, smul_zero, add_zero, smul_smul]
    rw [hnE, hpE t]
    funext ω
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · -- the IS equation
    have hyE : 𝔼.E (t + 1) (a (t + 1 + 1) + n (t + 1 + 1)) =
        ((1 + φ⁻¹) * ρa) • a (t + 1) := by
      simp only [n]
      rw [map_add, map_add, map_smul, map_smul, ha.2 (t + 1), innov_E 𝔼 ha (t + 1), smul_zero,
        add_zero, smul_smul, ← add_smul]
      congr 1
      ring
    have hq : qE 𝔼 p (t + 1) = gam σ φ ρa φπ • a (t + 1) := by
      unfold qE
      rw [hpE (t + 1)]
      abel
    rw [hyE, hq]
    funext ω
    simp only [n, p, pPath, innov, Nat.add_sub_cancel, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    unfold cEps gam Kc
    field_simp
    ring
  · rintro ⟨B, hB⟩
    refine ⟨|gam σ φ ρa φπ| * B + B + |ρa| * B, fun t ω => ?_⟩
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e1 := hB t ω
    have e2 := hB (t + 1) ω
    have h1 : |gam σ φ ρa φπ * a t ω| ≤ |gam σ φ ρa φπ| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    have h2 : |ρa * a t ω| ≤ |ρa| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    calc |pPath (gam σ φ ρa φπ) ρa a c t ω + gam σ φ ρa φπ * a t ω -
          (a (t + 1) ω - ρa * a t ω) - pPath (gam σ φ ρa φπ) ρa a c t ω|
        = |gam σ φ ρa φπ * a t ω - a (t + 1) ω + ρa * a t ω| := by ring_nf
      _ ≤ |gam σ φ ρa φπ * a t ω - a (t + 1) ω| + |ρa * a t ω| := abs_add_le _ _
      _ ≤ |gam σ φ ρa φπ * a t ω| + |a (t + 1) ω| + |ρa * a t ω| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith

/-! ### (d) Optimal policy -/

/-- Galí (2015), Exercise 6.2(d), p. 196: in any equilibrium replicating the flexible
allocation `n = a/φ` (efficient by the exercise's assumption), whatever the policy, the real
rate equals the natural rate: `i_{t+1} − E_{t+1} π_{t+2} = r_{t+1}`. -/
theorem optimal_real_rate {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i)
    (hflex : ∀ t, n t = φ⁻¹ • a t) (t : ℕ) :
    i (t + 1) - qE 𝔼 p (t + 1) = rnat σ ρ φ ρa a (t + 1) := by
  have e := n_from_IS 𝔼 hφ hσ ha hb t
  rw [hflex (t + 1)] at e
  funext ω
  have e' := congrFun e ω
  unfold rnat
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
  linear_combination (norm := skip) σ * e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(d), p. 196: the implementing rule
`i_t = r_t + φ_π E_{t−1} π_t` (natural rate plus a response to expected inflation). -/
def OptRule (σ ρ φ ρa φπ : ℝ) (a p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = rnat σ ρ φ ρa a (t + 1) + φπ • qE 𝔼 p t

/-- Galí (2015), Exercise 6.2(d), p. 196 (**uniqueness**): under `OptRule` with `φ_π > 1`,
every equilibrium with bounded inflation replicates the flexible allocation,
`n = a/φ`, `y = (1 + φ) a/φ`, with `E_t π_{t+1} = 0`, `π_{t+1} = −ε^a_{t+1}`, the real rate at
its natural level, and real wage `w − p = a`. -/
theorem optimal_unique {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hφπ : 1 < φπ)
    {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hp : 𝔼.Adapted p)
    (hπb : ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M)
    (hb : Block 𝔼 φ σ ρ a n y w p i) (hr : OptRule 𝔼 σ ρ φ ρa φπ a p i) :
    ∀ t, qE 𝔼 p t = 0 ∧ p (t + 1) - p t = -(a (t + 1) - ρa • a t) ∧
      n (t + 1) = φ⁻¹ • a (t + 1) ∧ y (t + 1) = ((1 + φ) / φ) • a (t + 1) ∧
      i (t + 1) - qE 𝔼 p (t + 1) = rnat σ ρ φ ρa a (t + 1) ∧ w t - p t = a t := by
  obtain ⟨M, hM⟩ := hπb
  have hφπ0 : φπ ≠ 0 := by positivity
  have hqa : ∀ t, 𝔼.E t (qE 𝔼 p t) = qE 𝔼 p t := fun t => by
    unfold qE
    rw [map_sub, 𝔼.E_E_self, hp t]
  have hq : ∀ t, qE 𝔼 p t = φπ⁻¹ • 𝔼.E t (qE 𝔼 p (t + 1)) + 0 := by
    intro t
    have e := expected_IS 𝔼 hφ hσ ha hb t
    rw [hr t, map_add, map_smul, hqa t] at e
    unfold rnat at e
    rw [map_add, 𝔼.const, map_smul, ha.2 t] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e' ⊢
    field_simp
    linarith
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  have hinv : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φπ)]
    exact inv_lt_one_of_one_lt₀ hφπ
  have hqe : qE 𝔼 p = 0 :=
    𝔼.forward_unique hinv hq hz (qE_bounded 𝔼 hp hM) ⟨0, fun t ω => by simp⟩
  have hqt : ∀ t, qE 𝔼 p t = 0 := fun t => by rw [hqe]; rfl
  have hn : ∀ t, n (t + 1) = φ⁻¹ • a (t + 1) := by
    intro t
    rw [n_from_IS 𝔼 hφ hσ ha hb t, hr t, hqt t, hqt (t + 1)]
    funext ω
    unfold rnat
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  intro t
  refine ⟨hqt t, ?_, hn t, ?_, ?_, (wage_facts 𝔼 hφ ha hb t).2.2⟩
  · have e := (wage_facts 𝔼 hφ ha hb t).2.1
    have e2 := hqt t
    unfold qE at e2
    rw [← e, ← sub_zero (p (t + 1) - p t), ← e2]
    abel
  · rw [hb.1 (t + 1), hn t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hr t, hqt t, hqt (t + 1), smul_zero, add_zero, sub_zero]

/-- Galí (2015), Exercise 6.2(d), p. 196 (**existence**): for every initial price level
known at date 0, the flexible allocation `n = a/φ` with `p_{t+1} = p_t − ε^a_{t+1}`,
`w = p + a` and `i = r` (natural rate) is an equilibrium under `OptRule`, with adapted prices
and, for bounded `a`, bounded inflation. -/
theorem optimal_exists {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    let p := pPath 0 ρa a c
    Block 𝔼 φ σ ρ a (fun t => φ⁻¹ • a t) (fun t => a t + φ⁻¹ • a t) (fun t => p t + a t) p
        (rnat σ ρ φ ρa a) ∧
      OptRule 𝔼 σ ρ φ ρa φπ a p (rnat σ ρ φ ρa a) ∧ 𝔼.Adapted p ∧
      (BoundedProc a → ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) := by
  intro p
  have hpE : ∀ t, 𝔼.E t (p (t + 1)) = p t := fun t => by
    rw [pPath_E 𝔼 ha hc t, zero_smul, add_zero]
  have hq : ∀ t, qE 𝔼 p t = 0 := fun t => by
    unfold qE
    rw [hpE t, sub_self]
  refine ⟨⟨fun t => rfl, fun t => (add_sub_cancel_right (p t) (a t)).symm, fun t => ?_,
    fun t => ?_⟩, fun t => ?_,
    pPath_adapted 𝔼 ha hc, ?_⟩
  · rw [hpE t, map_smul, ha.2 t]
    funext ω
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hq (t + 1), map_add, map_smul, ha.2 (t + 1)]
    funext ω
    unfold rnat Kc
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.zero_apply]
    field_simp
    ring
  · rw [hq t, smul_zero, add_zero]
  · rintro ⟨B, hB⟩
    refine ⟨B + |ρa| * B, fun t ω => ?_⟩
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : |ρa * a t ω| ≤ |ρa| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
    calc |pPath 0 ρa a c t ω + 0 * a t ω - (a (t + 1) ω - ρa * a t ω) - pPath 0 ρa a c t ω|
        = |-a (t + 1) ω + ρa * a t ω| := by ring_nf
      _ ≤ |-a (t + 1) ω| + |ρa * a t ω| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith [hB (t + 1) ω]

end Gali.StickyWagesPrices.Ex6_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.3: labour market institutions and long-run money non-neutrality

Galí (2015), Chapter 6, Exercise 6.3, pp. 196–197 (Blanchard and Summers 1986). A competitive
firm maximises `P_t Y_t − W_t N_t` with `Y_t = N_t^{1−α}`; labour supply is inelastic at one;
the goods market clears at `Y_t = M_t/P_t`; money follows `m_t = ρ_m m_{t−1} + ε_t`.

## The firm (exact)
* `hasDerivAt_profit`, `profit_le`, `labor_demand_iff`: for `0 ≤ α < 1`, `N > 0` maximises
  profit on `N > 0` iff `W = P (1 − α) N^{−α}` (necessity from the derivative, sufficiency from
  Bernoulli's inequality, i.e. concavity).
* `labor_demand_log`, `production_log`, `goods_log`: the three equations are exactly
  `w − p = log(1 − α) − α n`, `y = (1 − α) n`, `y = m − p` in logs, so the log-linear model
  `Static` is exact.
* `static_iff`: given the wage, `n = m − w + log(1 − α)`, `y = (1 − α) n`,
  `p = w − log(1 − α) + α n`.

## (a) Flexible competitive wages: `flexible_iff`
`n = 0` (inelastic supply at one), `y = 0`, `p = m`, `w − p = log(1 − α)`.

## (b) Wages set in advance, `E_{t−1} n_t = 0`
* `advance_iff`: the condition holds iff `w_t = ρ_m m_{t−1} + log(1 − α) (= E_{t−1} m_t + …)`.
* `advance_solution`: `n_t = m_t − E_{t−1} m_t = ε_t`, `y_t = (1 − α) ε_t`,
  `p_t = m_t − (1 − α) ε_t`, `w_t − p_t = log(1 − α) − α ε_t`, and
  `advance_no_persistence`: `E_t n_{t+k} = 0` for `k ≥ 1`.
* `advance_exists`: the equilibrium exists.

## (c) Union wage setting, `E_{t−1} n_t = n_{t−1}`
* `union_iff`: the condition holds iff `w_t = ρ_m m_{t−1} + log(1 − α) − n_{t−1}`.
* `union_solution`: `n_t = n_{t−1} + ε_t`, `y_t = y_{t−1} + (1 − α) ε_t` (unit root),
  `union_hysteresis`: `E_t n_{t+k} = n_t` for all `k` (shocks have permanent effects).
* `union_exists`: the equilibrium exists for any initial employment.

## (d)
Part (d) asks for a discussion of empirical relevance; it is not formalised.
-/

namespace Gali.StickyWagesPrices.Ex6_3

/-! ### The firm -/

/-- Galí (2015), Exercise 6.3, p. 196: the firm's profit `P N^{1−α} − W N`. -/
noncomputable def profit (P W α N : ℝ) : ℝ := P * N ^ (1 - α) - W * N

/-- Galí (2015), Exercise 6.3, p. 196: the marginal profit of labour is
`P (1 − α) N^{−α} − W`. -/
theorem hasDerivAt_profit (P W α : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun N' => profit P W α N') (P * ((1 - α) * N ^ (-α)) - W) N := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - α)) ((1 - α) * N ^ (1 - α - 1)) N :=
    Real.hasDerivAt_rpow_const (Or.inl hN.ne')
  have h2 := HasDerivAt.sub (h1.const_mul P) ((hasDerivAt_id N).const_mul W)
  rw [show 1 - α - 1 = -α by ring, mul_one] at h2
  exact h2

/-- Galí (2015), Exercise 6.3, p. 196 (**sufficiency**): if `W = P (1 − α) N^{−α}` then `N`
maximises profit over all `N' > 0` (Bernoulli's inequality, i.e. concavity of `N^{1−α}`). -/
theorem profit_le {P W α N N' : ℝ} (hP : 0 ≤ P) (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N)
    (hN' : 0 < N') (hW : W = P * ((1 - α) * N ^ (-α))) :
    profit P W α N' ≤ profit P W α N := by
  have hs : -1 ≤ N' / N - 1 := by
    have : 0 ≤ N' / N := by positivity
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (by linarith : 0 ≤ 1 - α)
    (by linarith : 1 - α ≤ 1)
  rw [show 1 + (N' / N - 1) = N' / N by ring, Real.div_rpow hN'.le hN.le] at hb
  have hX : N ^ (1 - α) = N * N ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
  have hpos : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
  rw [div_le_iff₀ hpos] at hb
  have key : N' ^ (1 - α) ≤ N * N ^ (-α) + (1 - α) * N ^ (-α) * (N' - N) := by
    calc N' ^ (1 - α) ≤ (1 + (1 - α) * (N' / N - 1)) * N ^ (1 - α) := hb
      _ = _ := by rw [hX]; field_simp
  unfold profit
  rw [hW, hX]
  nlinarith [mul_le_mul_of_nonneg_left key hP]

/-- Galí (2015), Exercise 6.3, p. 196 (**labour demand, necessary and sufficient**): for
`P > 0`, `0 ≤ α < 1`, `N > 0`, `N` maximises profit on `N > 0` iff
`W/P = (1 − α) N^{−α}`. -/
theorem labor_demand_iff {P W α N : ℝ} (hP : 0 < P) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hN : 0 < N) :
    IsMaxOn (fun N' => profit P W α N') (Set.Ioi 0) N ↔ W = P * ((1 - α) * N ^ (-α)) := by
  constructor
  · intro h
    have hz := (h.isLocalMax (Ioi_mem_nhds hN)).hasDerivAt_eq_zero (hasDerivAt_profit P W α hN)
    linarith
  · intro hW
    exact isMaxOn_iff.mpr fun N' hN' => profit_le hP.le hα0 hα1 hN hN' hW

/-- Galí (2015), Exercise 6.3, p. 196: labour demand in logs is exactly
`w − p = log(1 − α) − α n`. -/
theorem labor_demand_log {P W α N : ℝ} (hP : 0 < P) (hW : 0 < W) (hα1 : α < 1) (hN : 0 < N) :
    W = P * ((1 - α) * N ^ (-α)) ↔
      Real.log W - Real.log P = Real.log (1 - α) - α * Real.log N := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hr : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN _
  have hlog : Real.log (P * ((1 - α) * N ^ (-α))) =
      Real.log P + (Real.log (1 - α) - α * Real.log N) := by
    rw [Real.log_mul hP.ne' (by positivity), Real.log_mul h1.ne' hr.ne', Real.log_rpow hN]
    ring
  constructor
  · intro h
    rw [h, hlog]
    ring
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hW) (Set.mem_Ioi.mpr (by positivity)) ?_
    rw [hlog]
    linarith

/-- Galí (2015), Exercise 6.3, p. 196: the technology `Y = N^{1−α}` is exactly
`y = (1 − α) n` in logs. -/
theorem production_log {Y N α : ℝ} (hY : 0 < Y) (hN : 0 < N) :
    Y = N ^ (1 - α) ↔ Real.log Y = (1 - α) * Real.log N := by
  constructor
  · intro h
    rw [h, Real.log_rpow hN]
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hY)
      (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hN _)) ?_
    rw [h, Real.log_rpow hN]

/-- Galí (2015), Exercise 6.3, p. 196: goods market clearing `Y = M/P` is exactly
`y = m − p` in logs. -/
theorem goods_log {Y M P : ℝ} (hY : 0 < Y) (hM : 0 < M) (hP : 0 < P) :
    Y = M / P ↔ Real.log Y = Real.log M - Real.log P := by
  constructor
  · intro h
    rw [h, Real.log_div hM.ne' hP.ne']
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hY) (Set.mem_Ioi.mpr (by positivity)) ?_
    rw [h, Real.log_div hM.ne' hP.ne']

/-! ### The log-linear model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.3, p. 196: the (exact) log model given the wage: labour demand
`w − p = log(1 − α) − α n`, technology `y = (1 − α) n`, goods market `y = m − p`. -/
def Static (α : ℝ) (m n y p w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w t - p t = (fun _ => Real.log (1 - α)) - α • n t ∧ y t = (1 - α) • n t ∧
    y t = m t - p t

/-- Galí (2015), Exercise 6.3, p. 196: the static block solved given the wage,
`n = m − w + log(1 − α)`, `y = (1 − α) n`, `p = w − log(1 − α) + α n`. -/
theorem static_iff {α : ℝ} {m n y p w : ℕ → Ω → ℝ} :
    Static α m n y p w ↔ ∀ t, n t = m t - w t + (fun _ => Real.log (1 - α)) ∧
      y t = (1 - α) • n t ∧ p t = w t - (fun _ => Real.log (1 - α)) + α • n t := by
  refine forall_congr' fun t => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩ <;> funext ω <;>
    · have e1 := congrFun h1 ω
      have e2 := congrFun h2 ω
      have e3 := congrFun h3 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩ <;> funext ω <;>
    · have e1 := congrFun h1 ω
      have e2 := congrFun h2 ω
      have e3 := congrFun h3 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      linarith

/-- Galí (2015), Exercise 6.3(a), p. 196 (**necessary and sufficient**): with flexible
competitive wages and labour supply inelastic at one (`n = log 1 = 0`), the equilibrium is
`n = 0`, `y = 0`, `p = m`, `w − p = log(1 − α)`. -/
theorem flexible_iff {α : ℝ} {m n y p w : ℕ → Ω → ℝ} :
    (Static α m n y p w ∧ ∀ t, n t = 0) ↔
      ∀ t, n t = 0 ∧ y t = 0 ∧ p t = m t ∧ w t - p t = fun _ => Real.log (1 - α) := by
  constructor
  · rintro ⟨hs, hn⟩ t
    obtain ⟨h1, h2, h3⟩ := hs t
    have hy : y t = 0 := by rw [h2, hn t, smul_zero]
    refine ⟨hn t, hy, ?_, ?_⟩
    · rw [hy] at h3
      exact (sub_eq_zero.mp h3.symm).symm
    · rw [h1, hn t, smul_zero, sub_zero]
  · intro h
    refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => (h t).1⟩
    · rw [(h t).2.2.2, (h t).1, smul_zero, sub_zero]
    · rw [(h t).2.1, (h t).1, smul_zero]
    · rw [(h t).2.1, (h t).2.2.1, sub_self]

/-! ### (b) Wages set in advance -/

/-- Galí (2015), Exercise 6.3(b), p. 196 (**necessary and sufficient**): with a predetermined
wage, `E_{t−1} n_t = 0` holds iff `w_t = ρ_m m_{t−1} + log(1 − α)`. -/
theorem advance_iff {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w) :
    (∀ t, 𝔼.E t (n (t + 1)) = 0) ↔
      ∀ t, w (t + 1) = ρm • m t + fun _ => Real.log (1 - α) := by
  have hE : ∀ t, 𝔼.E t (n (t + 1)) = ρm • m t - w (t + 1) + fun _ => Real.log (1 - α) := by
    intro t
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, map_add, map_sub, hm.2 t, hw t, 𝔼.const]
  refine forall_congr' fun t => ?_
  rw [hE t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    linarith
  · intro h
    rw [h]
    abel

/-- Galí (2015), Exercise 6.3(b), pp. 196–197: with wages set in advance so that
`E_{t−1} n_t = 0`: `n_t = m_t − E_{t−1} m_t = ε_t`, `y_t = (1 − α) ε_t`,
`p_t = m_t − (1 − α) ε_t`, and the real wage `w_t − p_t = log(1 − α) − α ε_t`. -/
theorem advance_solution {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = 0) (t : ℕ) :
    n (t + 1) = m (t + 1) - 𝔼.E t (m (t + 1)) ∧ n (t + 1) = m (t + 1) - ρm • m t ∧
      y (t + 1) = (1 - α) • (m (t + 1) - ρm • m t) ∧
      p (t + 1) = m (t + 1) - (1 - α) • (m (t + 1) - ρm • m t) ∧
      w (t + 1) - p (t + 1) = (fun _ => Real.log (1 - α)) - α • (m (t + 1) - ρm • m t) := by
  have hwv := (advance_iff 𝔼 hm hw hs).mp hn t
  obtain ⟨h1, h2, h3⟩ := hs (t + 1)
  have hnv : n (t + 1) = m (t + 1) - ρm • m t := by
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, hwv]
    abel
  have hy : y (t + 1) = (1 - α) • (m (t + 1) - ρm • m t) := by rw [h2, hnv]
  refine ⟨by rw [hnv, hm.2 t], hnv, hy, ?_, by rw [h1, hnv]⟩
  rw [hy] at h3
  rw [h3]
  abel

/-- Galí (2015), Exercise 6.3(b), p. 197 (no persistence): with wages set in advance,
`E_t n_{t+k} = 0` for every `k ≥ 1`: a monetary shock affects employment for one period only. -/
theorem advance_no_persistence {n : ℕ → Ω → ℝ} (hn : ∀ t, 𝔼.E t (n (t + 1)) = 0) (t k : ℕ) :
    𝔼.E t (n (t + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), hn (t + k), map_zero]

/-- Galí (2015), Exercise 6.3(b), p. 196: the wage set in advance,
`w_{t+1} = ρ_m m_t + log(1 − α)`, from an initial wage `w_0`. -/
noncomputable def wAdv (α ρm : ℝ) (m : ℕ → Ω → ℝ) (w0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => w0
  | t + 1 => ρm • m t + fun _ => Real.log (1 - α)

/-- Galí (2015), Exercise 6.3(b), p. 196 (**existence**): with `w = wAdv` and the static block
solved, the wage is predetermined and `E_{t−1} n_t = 0`. -/
theorem advance_exists {α ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) (w0 : Ω → ℝ) :
    let w := wAdv α ρm m w0
    let n := fun t => m t - w t + fun _ => Real.log (1 - α)
    Static α m n (fun t => (1 - α) • n t) (fun t => w t - (fun _ => Real.log (1 - α)) + α • n t)
        w ∧
      (∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) ∧ ∀ t, 𝔼.E t (n (t + 1)) = 0 := by
  intro w n
  have hwp : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1) := fun t => by
    simp only [w, wAdv]
    rw [map_add, map_smul, hm.1 t, 𝔼.const]
  refine ⟨(static_iff (Ω := Ω)).mpr fun t => ⟨rfl, rfl, rfl⟩, hwp, fun t => ?_⟩
  simp only [n]
  rw [map_add, map_sub, hwp t, hm.2 t, 𝔼.const]
  simp only [w, wAdv]
  abel

/-! ### (c) Union wage setting -/

/-- Galí (2015), Exercise 6.3(c), p. 197 (**necessary and sufficient**): with a predetermined
wage and adapted employment, `E_{t−1} n_t = n_{t−1}` iff
`w_t = ρ_m m_{t−1} + log(1 − α) − n_{t−1}`. -/
theorem union_iff {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w) :
    (∀ t, 𝔼.E t (n (t + 1)) = n t) ↔
      ∀ t, w (t + 1) = ρm • m t + (fun _ => Real.log (1 - α)) - n t := by
  have hE : ∀ t, 𝔼.E t (n (t + 1)) = ρm • m t - w (t + 1) + fun _ => Real.log (1 - α) := by
    intro t
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, map_add, map_sub, hm.2 t, hw t, 𝔼.const]
  refine forall_congr' fun t => ?_
  rw [hE t]
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [h]
    abel

/-- Galí (2015), Exercise 6.3(c), p. 197: under union wage setting employment and output have
a unit root, `n_t = n_{t−1} + ε_t`, `y_t = y_{t−1} + (1 − α) ε_t`, with
`p_t = m_t − y_t` and real wage `w_t − p_t = log(1 − α) − α n_t`. -/
theorem union_solution {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = n t) (t : ℕ) :
    n (t + 1) = n t + (m (t + 1) - ρm • m t) ∧
      y (t + 1) = y t + (1 - α) • (m (t + 1) - ρm • m t) ∧ p (t + 1) = m (t + 1) - y (t + 1) ∧
      w (t + 1) - p (t + 1) = (fun _ => Real.log (1 - α)) - α • n (t + 1) := by
  have hwv := (union_iff 𝔼 hm hw hs).mp hn t
  have hnv : n (t + 1) = n t + (m (t + 1) - ρm • m t) := by
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, hwv]
    abel
  obtain ⟨h1, h2, h3⟩ := hs (t + 1)
  refine ⟨hnv, ?_, by rw [h3]; abel, h1⟩
  rw [h2, (hs t).2.1, hnv, smul_add]

/-- Galí (2015), Exercise 6.3(c), p. 197 (**hysteresis**): under union wage setting
`E_t n_{t+k} = n_t` for every horizon `k`: the effect of a monetary shock on employment is
permanent. -/
theorem union_hysteresis {n : ℕ → Ω → ℝ} (hna : 𝔼.Adapted n)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = n t) (t k : ℕ) : 𝔼.E t (n (t + k)) = n t := by
  induction k with
  | zero => exact hna t
  | succ k ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t k), hn (t + k), ← ih]

/-- Galí (2015), Exercise 6.3(c), p. 197: employment under union wage setting,
`n_{t+1} = n_t + ε_{t+1}` from an initial level `n_0`. -/
def nUnion (ρm : ℝ) (m : ℕ → Ω → ℝ) (n0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => n0
  | t + 1 => nUnion ρm m n0 t + (m (t + 1) - ρm • m t)

/-- Galí (2015), Exercise 6.3(c), p. 197: union employment is adapted. -/
theorem nUnion_adapted {ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) {n0 : Ω → ℝ}
    (hn0 : 𝔼.E 0 n0 = n0) : 𝔼.Adapted (nUnion ρm m n0) := by
  intro t
  induction t with
  | zero => exact hn0
  | succ t ih =>
    simp only [nUnion]
    rw [map_add, map_sub, map_smul, hm.1 (t + 1), ← ih, ← hm.1 t, 𝔼.known (Nat.le_succ t),
      𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.3(c), p. 197 (**existence**): for every initial employment level
known at date 0, the wage `w = m − n + log(1 − α)` with `n = nUnion` is predetermined, the
static block holds and `E_{t−1} n_t = n_{t−1}`. -/
theorem union_exists {α ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) {n0 : Ω → ℝ}
    (hn0 : 𝔼.E 0 n0 = n0) :
    let n := nUnion ρm m n0
    let w := fun t => m t - n t + fun _ => Real.log (1 - α)
    Static α m n (fun t => (1 - α) • n t) (fun t => w t - (fun _ => Real.log (1 - α)) + α • n t)
        w ∧
      (∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) ∧ ∀ t, 𝔼.E t (n (t + 1)) = n t := by
  intro n w
  have hna := nUnion_adapted 𝔼 hm hn0
  have hnE : ∀ t, 𝔼.E t (n (t + 1)) = n t := fun t => by
    simp only [n, nUnion]
    rw [map_add, map_sub, map_smul, hna t, hm.2 t, hm.1 t, sub_self, add_zero]
  refine ⟨(static_iff (Ω := Ω)).mpr fun t => ⟨by simp only [w]; abel, rfl, rfl⟩, fun t => ?_,
    hnE⟩
  have hw : w (t + 1) = ρm • m t - n t + fun _ => Real.log (1 - α) := by
    simp only [w, n, nUnion]
    abel
  rw [hw, map_add, map_sub, map_smul, hm.1 t, hna t, 𝔼.const]

end Gali.StickyWagesPrices.Ex6_3

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.4: monetary policy and real wage rigidities

Galí (2015), Chapter 6, Exercise 6.4, pp. 197–198. Utility `U(C, N) = C − N²/2`, technology
`Y = A N`, all output consumed, Calvo pricing giving `π_t = β E_t π_{t+1} − λ μ̂_t` with
`μ̂_t = μ_t − μ` the markup gap.

## (a) Efficient output: `efficient_hours_iff`, `hasDerivAt_planner`, `efficient_output_log`
The planner's `A N − N²/2` is uniquely maximised at `N = A`, so `Yᵉ = A²`, `yᵉ = 2a`.

## (b) The wage schedule: `hasDerivAt_utility_C`, `hasDerivAt_utility_N`,
`competitive_supply_log`, `real_wage_schedule`, `real_rigidity`
Competitive labour markets give `W/P = −U_N/U_C = N`, i.e. `w − p = n`; under the schedule
`w = p + n/(1 + δ)` the real wage moves by only `1/(1 + δ) < 1` per unit of employment: a
real rigidity.

## (c)–(d) The natural level and the markup gap
`hasDerivAt_cost` (marginal cost `W/A`), `markup_eq` (`μ_t = a_t − (y_t − a_t)/(1 + δ)`),
`natural_iff` (`μ_t = μ` iff `y_t = yⁿ_t = (2 + δ) a_t − (1 + δ) μ`), `markup_gap`
(`μ̂_t = −(y_t − yⁿ_t)/(1 + δ)`).

## (e) The inflation equation and the tradeoff
* `nkpc_iff`: `π = β E π' + (λ/(1+δ))(y − yᵉ) + (λ/(1+δ))(yᵉ − yⁿ)`; `cost_push`:
  `yᵉ − yⁿ = −δ a + (1 + δ) μ`.
* `divine_iff`, `divine_iff_mu0`, `tradeoff_iff_delta`, `strict_inflation_gap`: zero inflation
  and a zero welfare gap are jointly attainable iff the cost-push term vanishes; with `μ = 0`
  and nonzero productivity this holds iff `δ = 0`, so `δ > 0` creates a tradeoff (keeping
  `π ≡ 0` forces `y − yᵉ = δ a`).

## (f) Discretion with i.i.d. productivity
The loss's `y*_t` is undefined in the exercise (survey error 10): we read it as `yᵉ_t`, and
the "infinitesimally small" desired markup as `μ = 0` exactly.
* `period_problem_iff` (restated from the Chapter 5 project), `discretionEq_iff`: the
  discretionary equilibrium is the NKPC plus the targeting rule `x = −(κ/α_y) π`.
* `discretion_iid_iff`: with `a` i.i.d. (`E_t a_{t+1} = 0`) and bounded, the unique bounded
  discretionary equilibrium is `π_t = −α_y κ δ a_t/(α_y + κ²)`, `y_t − yᵉ_t = κ² δ a_t/(α_y + κ²)`,
  `κ = λ/(1 + δ)`; `discretion_output` gives `y_t = (2 + κ²δ/(α_y + κ²)) a_t`.
* `perfect_competition`: with `δ = 0` (competitive labour market) `π ≡ 0`, `y = yᵉ = 2a`.
-/

namespace Gali.StickyWagesPrices.Ex6_4

/-! ### (a) Efficient output -/

/-- Galí (2015), Exercise 6.4(a), p. 197: the planner's objective `A N − N²/2` (consumption
equals output `A N`) has derivative `A − N`. -/
theorem hasDerivAt_planner (A N : ℝ) :
    HasDerivAt (fun N' => A * N' - N' ^ 2 / 2) (A - N) N := by
  have h := HasDerivAt.sub ((hasDerivAt_id' N).const_mul A) ((hasDerivAt_pow 2 N).div_const 2)
  exact h.congr_deriv (by norm_num)

/-- Galí (2015), Exercise 6.4(a), p. 197 (**necessary and sufficient**): `N` maximises
`A N − N²/2` iff `N = A` (since `A N − N²/2 = A²/2 − (N − A)²/2`). -/
theorem efficient_hours_iff {A N : ℝ} :
    (∀ N', A * N' - N' ^ 2 / 2 ≤ A * N - N ^ 2 / 2) ↔ N = A := by
  constructor
  · intro h
    have h1 := h A
    have h2 : (N - A) ^ 2 ≤ 0 := by nlinarith
    have : N - A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm h2 (sq_nonneg _))
    linarith
  · intro hN N'
    rw [hN]
    nlinarith [sq_nonneg (N' - A)]

/-- Galí (2015), Exercise 6.4(a), p. 197: efficient output `Yᵉ = A · A` gives `yᵉ = 2a`. -/
theorem efficient_output_log {A : ℝ} (hA : 0 < A) : Real.log (A * A) = 2 * Real.log A := by
  rw [Real.log_mul hA.ne' hA.ne']
  ring

/-! ### (b) The wage schedule -/

/-- Galí (2015), Exercise 6.4(b), p. 197: the marginal utility of consumption is one. -/
theorem hasDerivAt_utility_C (C N : ℝ) : HasDerivAt (fun C' => C' - N ^ 2 / 2) 1 C := by
  exact (hasDerivAt_id' C).sub_const (N ^ 2 / 2)

/-- Galí (2015), Exercise 6.4(b), p. 197: the marginal disutility of hours is `N`, so the
marginal rate of substitution `−U_N/U_C` is `N`. -/
theorem hasDerivAt_utility_N (C N : ℝ) : HasDerivAt (fun N' => C - N' ^ 2 / 2) (-N) N := by
  have h := ((hasDerivAt_pow 2 N).div_const 2).const_sub C
  exact h.congr_deriv (by norm_num)

/-- Galí (2015), Exercise 6.4(b), p. 197: competitive labour supply `W/P = N` is exactly
`w − p = n` in logs. -/
theorem competitive_supply_log {W P N : ℝ} (hW : 0 < W) (hP : 0 < P) (hN : 0 < N) :
    W / P = N ↔ Real.log W - Real.log P = Real.log N := by
  rw [← Real.log_div hW.ne' hP.ne']
  constructor
  · intro h
    rw [h]
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hN) h

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.4(b), p. 197: the wage schedule `w_t = p_t + n_t/(1 + δ)`. -/
def Schedule (δ : ℝ) (n w p : ℕ → Ω → ℝ) : Prop := ∀ t, w t = p t + (1 + δ)⁻¹ • n t

/-- Galí (2015), Exercise 6.4, p. 197: technology in logs, `y = a + n`. -/
def Tech (a n y : ℕ → Ω → ℝ) : Prop := ∀ t, y t = a t + n t

/-- Galí (2015), Exercise 6.4(b), p. 197: under the schedule the real wage is
`w − p = n/(1 + δ) = (y − a)/(1 + δ)`, against `w − p = n` with a competitive labour market. -/
theorem real_wage_schedule {δ : ℝ} {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) :
    w t - p t = (1 + δ)⁻¹ • n t ∧ w t - p t = (1 + δ)⁻¹ • (y t - a t) := by
  have h1 : w t - p t = (1 + δ)⁻¹ • n t := by rw [hs t]; abel
  refine ⟨h1, ?_⟩
  rw [h1, ht t]
  abel_nf

/-- Galí (2015), Exercise 6.4(b), p. 197 (**real rigidity**): for `δ > 0` the response of the
real wage to employment, `1/(1 + δ)`, is below the competitive response `1`, so the real wage
moves strictly less than under competition whenever employment moves. -/
theorem real_rigidity {δ x : ℝ} (hδ : 0 < δ) (hx : x ≠ 0) :
    (1 + δ)⁻¹ < 1 ∧ |(1 + δ)⁻¹ * x| < |x| := by
  have h1 : (1 + δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h0 : 0 < (1 + δ)⁻¹ := by positivity
  refine ⟨h1, ?_⟩
  rw [abs_mul, abs_of_pos h0]
  have := abs_pos.mpr hx
  nlinarith

/-! ### (c)–(d) The natural level of output and the markup gap -/

/-- Galí (2015), Exercise 6.4(c), p. 197: with `Y = A N`, the cost of output `Y` is
`W Y/A`, so nominal marginal cost is `W/A` (`mc = w − a` in logs). -/
theorem hasDerivAt_cost (W A Y : ℝ) : HasDerivAt (fun Y' => W * (Y' / A)) (W / A) Y := by
  have h := ((hasDerivAt_id' Y).div_const A).const_mul W
  exact h.congr_deriv (by ring)

/-- Galí (2015), Exercise 6.4, p. 197: the (log) average markup `μ_t = p_t − (w_t − a_t)`,
price over nominal marginal cost. -/
def markup (a w p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - (w t - a t)

/-- Galí (2015), Exercise 6.4(c), p. 197: the natural level of output
`yⁿ_t = (2 + δ) a_t − (1 + δ) μ`. -/
def yn (δ μ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (2 + δ) • a t - fun _ => (1 + δ) * μ

/-- Galí (2015), Exercise 6.4(a), p. 197: efficient output `yᵉ_t = 2 a_t`. -/
def ye (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (2 : ℝ) • a t

/-- Galí (2015), Exercise 6.4(c), p. 197: under the schedule, `μ_t = a_t − (y_t − a_t)/(1 + δ)`. -/
theorem markup_eq {δ : ℝ} {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p) (ht : Tech a n y)
    (t : ℕ) : markup a w p t = a t - (1 + δ)⁻¹ • (y t - a t) := by
  unfold markup
  rw [hs t, ht t]
  abel_nf

/-- Galí (2015), Exercise 6.4(c), p. 197 (**necessary and sufficient**): the markup is at its
desired level `μ` iff output is at its natural level `yⁿ = (2 + δ) a − (1 + δ) μ`. -/
theorem natural_iff {δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) : markup a w p t = (fun _ => μ) ↔ y t = yn δ μ a t := by
  rw [markup_eq hs ht t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    unfold yn
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    unfold yn at e
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Galí (2015), Exercise 6.4(d), p. 197: the markup gap is `μ̂_t = −(y_t − yⁿ_t)/(1 + δ)`. -/
theorem markup_gap {δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) :
    markup a w p t - (fun _ => μ) = -((1 + δ)⁻¹ • (y t - yn δ μ a t)) := by
  rw [markup_eq hs ht t]
  funext ω
  unfold yn
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

/-! ### (e) The inflation equation and the tradeoff -/

/-- Galí (2015), Exercise 6.4, p. 197: the Calvo inflation equation
`π_t = β E_t π_{t+1} − λ μ̂_t`. -/
def NKPCmu (β lam μ : ℝ) (a w p infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - lam • (markup a w p t - fun _ => μ)

/-- Galí (2015), Exercise 6.4(e), p. 197: the inflation equation in the welfare-relevant gap,
`π_t = β E_t π_{t+1} + (λ/(1+δ))(y_t − yᵉ_t) + (λ/(1+δ))(yᵉ_t − yⁿ_t)`. -/
def NKPCgap (β lam δ μ : ℝ) (a y infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + (lam / (1 + δ)) • (y t - ye a t) +
    (lam / (1 + δ)) • (ye a t - yn δ μ a t)

/-- Galí (2015), Exercise 6.4(e), p. 197 (**equivalence**): under the wage schedule the Calvo
equation is the inflation equation in the welfare-relevant output gap. -/
theorem nkpc_iff {β lam δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p infl : ℕ → Ω → ℝ}
    (hs : Schedule δ n w p) (ht : Tech a n y) :
    NKPCmu 𝔼 β lam μ a w p infl ↔ NKPCgap 𝔼 β lam δ μ a y infl := by
  refine forall_congr' fun t => ?_
  rw [markup_gap hδ hs ht t]
  have e : -(lam • -((1 + δ)⁻¹ • (y t - yn δ μ a t))) =
      (lam / (1 + δ)) • (y t - ye a t) + (lam / (1 + δ)) • (ye a t - yn δ μ a t) := by
    funext ω
    unfold ye yn
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply]
    field_simp
    ring
  rw [sub_eq_add_neg, e, add_assoc]

/-- Galí (2015), Exercise 6.4(e), p. 197: the cost-push term is
`yᵉ_t − yⁿ_t = −δ a_t + (1 + δ) μ`. -/
theorem cost_push (δ μ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) :
    ye a t - yn δ μ a t = (-δ) • a t + fun _ => (1 + δ) * μ := by
  funext ω
  unfold ye yn
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 6.4(e), p. 197 (**no tradeoff iff no cost push**): for `λ ≠ 0`,
`1 + δ ≠ 0`, zero inflation together with `y = yᵉ` satisfies the inflation equation iff
`yᵉ − yⁿ ≡ 0`. -/
theorem divine_iff {β lam δ μ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ} :
    NKPCgap 𝔼 β lam δ μ a (ye a) 0 ↔ ∀ t, ye a t - yn δ μ a t = 0 := by
  have hc : lam / (1 + δ) ≠ 0 := div_ne_zero hlam hδ
  refine forall_congr' fun t => ?_
  simp only [Pi.zero_apply, map_zero, smul_zero, sub_self, zero_add]
  constructor
  · intro h
    exact (smul_eq_zero.mp h.symm).resolve_left hc
  · intro h
    rw [h, smul_zero]

/-- Galí (2015), Exercise 6.4(e), p. 197: with `μ = 0`, zero inflation and `y = yᵉ` are
jointly attainable iff `δ a_t = 0` at every date. -/
theorem divine_iff_mu0 {β lam δ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ} :
    NKPCgap 𝔼 β lam δ 0 a (ye a) 0 ↔ ∀ t, δ • a t = 0 := by
  rw [divine_iff 𝔼 hlam hδ]
  refine forall_congr' fun t => ?_
  rw [cost_push]
  simp only [mul_zero]
  constructor
  · intro h
    have : (-δ) • a t = 0 := by
      rw [← add_zero ((-δ) • a t)]
      exact h
    rwa [neg_smul, neg_eq_zero] at this
  · intro h
    rw [neg_smul, h, neg_zero, zero_add]
    rfl

/-- Galí (2015), Exercise 6.4(e), p. 198 (**the tradeoff**): with `μ = 0`, `λ ≠ 0`,
`1 + δ ≠ 0` and productivity not identically zero, zero inflation and a zero welfare-relevant
gap are jointly attainable iff `δ = 0`; real wage rigidity `δ > 0` creates a tradeoff. -/
theorem tradeoff_iff_delta {β lam δ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : ∃ t ω, a t ω ≠ 0) : NKPCgap 𝔼 β lam δ 0 a (ye a) 0 ↔ δ = 0 := by
  rw [divine_iff_mu0 𝔼 hlam hδ]
  constructor
  · intro h
    obtain ⟨t, ω, hne⟩ := ha
    have := congrFun (h t) ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right hne
  · intro h t
    rw [h, zero_smul]

/-- Galí (2015), Exercise 6.4(e), p. 198: fully stabilising inflation (`π ≡ 0`) forces the
welfare-relevant gap `y_t − yᵉ_t = −(yᵉ_t − yⁿ_t) = δ a_t − (1 + δ) μ`. -/
theorem strict_inflation_gap {β lam δ μ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0)
    {a y : ℕ → Ω → ℝ} (h : NKPCgap 𝔼 β lam δ μ a y 0) (t : ℕ) :
    y t - ye a t = δ • a t - fun _ => (1 + δ) * μ := by
  have hc : lam / (1 + δ) ≠ 0 := div_ne_zero hlam hδ
  have e := h t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at e
  rw [← smul_add] at e
  have e2 := (smul_eq_zero.mp e.symm).resolve_left hc
  rw [cost_push] at e2
  funext ω
  have e3 := congrFun e2 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e3 ⊢
  linarith

/-! ### (f) Optimal discretionary policy with i.i.d. productivity -/

/-- Galí (2015), Exercise 6.4(f), p. 198: the period objective after substituting the
constraint `π = κ x + υ`: `(κ x + υ)² + α_y x²` (restated from the Chapter 5 project). -/
def periodObj (κ αy υ x : ℝ) : ℝ := (κ * x + υ) ^ 2 + αy * x ^ 2

/-- Galí (2015), Exercise 6.4(f), p. 198 (completing the square; restated from the Chapter 5
project). -/
theorem periodObj_sub (κ αy υ x x' : ℝ) :
    periodObj κ αy υ x' - periodObj κ αy υ x
      = (κ ^ 2 + αy) * (x' - x) ^ 2 + 2 * (x' - x) * ((κ ^ 2 + αy) * x + κ * υ) := by
  unfold periodObj
  ring

/-- Galí (2015), Exercise 6.4(f), p. 198 (**necessary and sufficient**; restated from the
Chapter 5 project): for `α_y > 0`, `x` minimises the period objective iff
`x = −(κ/α_y)(κ x + υ)`. -/
theorem periodObj_isMinOn_iff {κ αy υ x : ℝ} (hαy : 0 < αy) :
    IsMinOn (periodObj κ αy υ) Set.univ x ↔ x = -(κ / αy) * (κ * x + υ) := by
  have hA : 0 < κ ^ 2 + αy := by positivity
  have hfoc : x = -(κ / αy) * (κ * x + υ) ↔ (κ ^ 2 + αy) * x + κ * υ = 0 := by
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
    set g := (κ ^ 2 + αy) * x + κ * υ
    have hle := h (Set.mem_univ (x - g / (κ ^ 2 + αy)))
    simp only [Set.mem_ofPred_eq] at hle
    have hd := periodObj_sub κ αy υ x (x - g / (κ ^ 2 + αy))
    have hval : (κ ^ 2 + αy) * (x - g / (κ ^ 2 + αy) - x) ^ 2 +
        2 * (x - g / (κ ^ 2 + αy) - x) * g = -(g ^ 2 / (κ ^ 2 + αy)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + αy) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h x' _
    have hd := periodObj_sub κ αy υ x x'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + αy) * (x' - x) ^ 2 := by positivity
    simp only [Set.mem_ofPred_eq]
    linarith

/-- Galí (2015), Exercise 6.4(f), p. 198 (**the period problem, necessary and sufficient**;
restated from the Chapter 5 project): for `α_y > 0`, `(π, x)` minimises `π² + α_y x²` subject
to `π = κ x + υ` iff it is feasible and `x = −(κ/α_y) π`. -/
theorem period_problem_iff {κ αy υ π x : ℝ} (hαy : 0 < αy) :
    (π = κ * x + υ ∧ ∀ π' x', π' = κ * x' + υ → π ^ 2 + αy * x ^ 2 ≤ π' ^ 2 + αy * x' ^ 2) ↔
      (π = κ * x + υ ∧ x = -(κ / αy) * π) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ αy υ) Set.univ x := fun x' _ => by
      have := hmin _ x' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hαy).mp this
  · rintro ⟨hc, hx⟩
    refine ⟨hc, fun π' x' hc' => ?_⟩
    rw [hc] at hx
    have := (periodObj_isMinOn_iff hαy).mpr hx (Set.mem_univ x')
    simp only [Set.mem_ofPred_eq, periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), Exercise 6.4(e)–(f), pp. 197–198: the inflation equation in the gap
`x = y − yᵉ` with slope `κ = λ/(1 + δ)` and cost push `κ g`, `g = yᵉ − yⁿ`. -/
def NKPCx (β κ : ℝ) (g x infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + κ • g t

/-- Galí (2015), Exercise 6.4(f), p. 198: a **discretionary equilibrium** for the loss
`E_0 ∑ βᵗ [α_y (y_t − yᵉ_t)² + π_t²]` (the book's undefined `y*_t` read as `yᵉ_t`): the
inflation equation holds and, date by date and state by state, `(π_t, x_t)` minimises
`π² + α_y x²` on `π = κ x + υ_t`, taking `υ_t = β E_t π_{t+1} + κ g_t` as given. -/
def DiscretionEq (β κ αy : ℝ) (g x infl : ℕ → Ω → ℝ) : Prop :=
  NKPCx 𝔼 β κ g x infl ∧ ∀ t ω, ∀ π' x' : ℝ,
    π' = κ * x' + (β * 𝔼.E t (infl (t + 1)) ω + κ * g t ω) →
      infl t ω ^ 2 + αy * x t ω ^ 2 ≤ π' ^ 2 + αy * x' ^ 2

/-- Galí (2015), Exercise 6.4(f), p. 198: for `α_y > 0` a discretionary equilibrium is exactly
the inflation equation plus the targeting rule `x_t = −(κ/α_y) π_t`. -/
theorem discretionEq_iff {β κ αy : ℝ} (hαy : 0 < αy) {g x infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ αy g x infl ↔
      NKPCx 𝔼 β κ g x infl ∧ ∀ t, x t = (-(κ / αy)) • infl t := by
  have hpt : ∀ (_ : NKPCx 𝔼 β κ g x infl) t ω,
      infl t ω = κ * x t ω + (β * 𝔼.E t (infl (t + 1)) ω + κ * g t ω) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  constructor
  · rintro ⟨h, hmin⟩
    refine ⟨h, fun t => funext fun ω => ?_⟩
    have := ((period_problem_iff hαy).mp ⟨hpt h t ω, hmin t ω⟩).2
    simpa using this
  · rintro ⟨h, hr⟩
    refine ⟨h, fun t ω => ((period_problem_iff hαy).mpr ⟨hpt h t ω, ?_⟩).2⟩
    have := congrFun (hr t) ω
    simpa using this

/-- Galí (2015), Exercise 6.4(f), p. 198: with `μ = 0` the cost-push term is `g = −δ a`. -/
theorem cost_push_mu0 (δ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : ye a t - yn δ 0 a t = (-δ) • a t := by
  rw [cost_push, mul_zero]
  funext ω
  simp

/-- Galí (2015), Exercise 6.4(f), p. 198 (**existence and uniqueness**): with `α_y > 0`,
`0 ≤ β < 1`, `μ = 0` (cost push `g = −δ a`) and i.i.d. bounded productivity
(`E_t a_{t+1} = 0`), a bounded `(x, π)` is a discretionary equilibrium iff
`π_t = −α_y κ δ a_t/(α_y + κ²)` and `x_t = κ² δ a_t/(α_y + κ²)`. -/
theorem discretion_iid_iff {β κ αy δ : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a x infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-δ) • a t) x infl ↔
      ∀ t, infl t = (-(αy * κ * δ / (αy + κ ^ 2))) • a t ∧
        x t = (κ ^ 2 * δ / (αy + κ ^ 2)) • a t := by
  have hA : 0 < αy + κ ^ 2 := by positivity
  have hEa : ∀ t, 𝔼.E t (a (t + 1)) = 0 := fun t => by rw [ha.2 t, zero_smul]
  rw [discretionEq_iff 𝔼 hαy]
  set c := -(αy * κ * δ / (αy + κ ^ 2)) with hc
  constructor
  · rintro ⟨h, hr⟩
    -- the forward equation for inflation
    have hf : ∀ t, infl t = (αy * β / (αy + κ ^ 2)) • 𝔼.E t (infl (t + 1)) +
        (αy * κ / (αy + κ ^ 2)) • (-δ • a t) := by
      intro t
      funext ω
      have p := congrFun (h t) ω
      have r := congrFun (hr t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
      rw [r] at p
      field_simp
      field_simp at p
      linarith
    have hs : ∀ t, c • a t = (αy * β / (αy + κ ^ 2)) • 𝔼.E t (c • a (t + 1)) +
        (αy * κ / (αy + κ ^ 2)) • (-δ • a t) := by
      intro t
      rw [map_smul, hEa t, smul_zero, smul_zero, zero_add, smul_smul, hc]
      congr 1
      field_simp
    have habs : |αy * β / (αy + κ ^ 2)| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hA]
      nlinarith [sq_nonneg κ]
    have hcb : BoundedProc fun t => c • a t := by
      obtain ⟨B, hB⟩ := hab
      refine ⟨|c| * B, fun t ω => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
    have heq : infl = fun t => c • a t := 𝔼.forward_unique habs hf hs hpb hcb
    intro t
    have hi : infl t = c • a t := by rw [heq]
    refine ⟨hi, ?_⟩
    rw [hr t, hi, smul_smul, hc]
    congr 1
    field_simp
  · intro h
    have hi : ∀ t, infl t = c • a t := fun t => (h t).1
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hi (t + 1), map_smul, hEa t, smul_zero, smul_zero, zero_add, hi t, (h t).2]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
      field_simp
      ring
    · rw [(h t).2, hi t, smul_smul, hc]
      congr 1
      field_simp

/-- Galí (2015), Exercise 6.4(f), p. 198: in the discretionary equilibrium output is
`y_t = yᵉ_t + x_t = (2 + κ² δ/(α_y + κ²)) a_t` (and employment `n = y − a`). -/
theorem discretion_output {β κ αy δ : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a y infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-δ) • a t) (fun t => y t - ye a t) infl ↔
      ∀ t, infl t = (-(αy * κ * δ / (αy + κ ^ 2))) • a t ∧
        y t = (2 + κ ^ 2 * δ / (αy + κ ^ 2)) • a t := by
  rw [discretion_iid_iff 𝔼 hαy hβ0 hβ1 ha hab hpb]
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  unfold ye
  rw [add_smul, sub_eq_iff_eq_add]
  constructor
  · intro h
    rw [h, add_comm]
  · intro h
    rw [h, add_comm]

/-- Galí (2015), Exercise 6.4(f), p. 198 (**perfect competition in the labour market**,
`δ = 0`): the unique bounded discretionary equilibrium has `π ≡ 0` and `y = yᵉ = 2a`; there is
no tradeoff. -/
theorem perfect_competition {β κ αy : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a y infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-(0 : ℝ)) • a t) (fun t => y t - ye a t) infl ↔
      ∀ t, infl t = 0 ∧ y t = ye a t := by
  rw [discretion_output 𝔼 hαy hβ0 hβ1 ha hab hpb]
  simp only [mul_zero, zero_div, neg_zero, zero_smul, add_zero]
  rfl

end Gali.StickyWagesPrices.Ex6_4

set_option linter.style.longLine false
#print axioms Gali.StickyWagesPrices.SchurStable
#print axioms Gali.StickyWagesPrices.disc
#print axioms Gali.StickyWagesPrices.root₁
#print axioms Gali.StickyWagesPrices.root₂
#print axioms Gali.StickyWagesPrices.root_sum
#print axioms Gali.StickyWagesPrices.root_prod
#print axioms Gali.StickyWagesPrices.root_eq
#print axioms Gali.StickyWagesPrices.normSq_root_of_neg
#print axioms Gali.StickyWagesPrices.norm_root_of_nonneg
#print axioms Gali.StickyWagesPrices.schurStable_iff_roots
#print axioms Gali.StickyWagesPrices.chSeq
#print axioms Gali.StickyWagesPrices.convSeq
#print axioms Gali.StickyWagesPrices.convSeq_rec
#print axioms Gali.StickyWagesPrices.chSeq_eq_convSeq
#print axioms Gali.StickyWagesPrices.norm_convSeq_le
#print axioms Gali.StickyWagesPrices.abs_chSeq_le
#print axioms Gali.StickyWagesPrices.tendsto_chSeq
#print axioms Gali.StickyWagesPrices.tr2
#print axioms Gali.StickyWagesPrices.det2
#print axioms Gali.StickyWagesPrices.tr2_eq_trace
#print axioms Gali.StickyWagesPrices.det2_eq_det
#print axioms Gali.StickyWagesPrices.sq_eq_cayleyHamilton
#print axioms Gali.StickyWagesPrices.pow_succ_eq
#print axioms Gali.StickyWagesPrices.abs_pow_entry_le
#print axioms Gali.StickyWagesPrices.tendsto_pow_entry
#print axioms Gali.StickyWagesPrices.BoundedSeq
#print axioms Gali.StickyWagesPrices.homogeneous_iterate
#print axioms Gali.StickyWagesPrices.abs_mulVec_le
#print axioms Gali.StickyWagesPrices.homogeneous_eq_zero
#print axioms Gali.StickyWagesPrices.eq_root_of_eq
#print axioms Gali.StickyWagesPrices.exists_eigenvector
#print axioms Gali.StickyWagesPrices.exists_bounded_homogeneous
#print axioms Gali.StickyWagesPrices.ExpectationSystem
#print axioms Gali.StickyWagesPrices.ExpectationSystem.mk
#print axioms Gali.StickyWagesPrices.ExpectationSystem.E
#print axioms Gali.StickyWagesPrices.ExpectationSystem.const
#print axioms Gali.StickyWagesPrices.ExpectationSystem.mono
#print axioms Gali.StickyWagesPrices.ExpectationSystem.tower
#print axioms Gali.StickyWagesPrices.ExpectationSystem.known
#print axioms Gali.StickyWagesPrices.perfectForesight
#print axioms Gali.StickyWagesPrices.BoundedProc
#print axioms Gali.StickyWagesPrices.BoundedVec
#print axioms Gali.StickyWagesPrices.ExpectationSystem.Adapted
#print axioms Gali.StickyWagesPrices.ExpectationSystem.IsAR1
#print axioms Gali.StickyWagesPrices.ExpectationSystem.E_neg
#print axioms Gali.StickyWagesPrices.ExpectationSystem.E_smul
#print axioms Gali.StickyWagesPrices.ExpectationSystem.E_E_self
#print axioms Gali.StickyWagesPrices.ExpectationSystem.abs_E_le
#print axioms Gali.StickyWagesPrices.ExpectationSystem.bounded_E
#print axioms Gali.StickyWagesPrices.ExpectationSystem.ar1_iterate
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forward_iterate
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forward_unique
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forward_ar1_solves
#print axioms Gali.StickyWagesPrices.ExpectationSystem.E_tsum
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forwardSeries
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forwardSeries_summable
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forwardSeries_solves
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.StickyWagesPrices.ExpectationSystem.eq_forwardSeries
#print axioms Gali.StickyWagesPrices.ExpectationSystem.forwardSeries_adapted
#print axioms Gali.StickyWagesPrices.ExpectationSystem.PullOut
#print axioms Gali.StickyWagesPrices.ExpectationSystem.Solves
#print axioms Gali.StickyWagesPrices.ExpectationSystem.AdaptedVec
#print axioms Gali.StickyWagesPrices.ExpectationSystem.system_iterate
#print axioms Gali.StickyWagesPrices.ExpectationSystem.system_unique
#print axioms Gali.StickyWagesPrices.ExpectationSystem.system_not_unique
#print axioms Gali.StickyWagesPrices.ExpectationSystem.Determinate
#print axioms Gali.StickyWagesPrices.ExpectationSystem.determinate_iff
#print axioms Gali.StickyWagesPrices.perfectForesight_pullOut
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinObs
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinTree
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinSystem
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.firstHeads
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinShock
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinAR1
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.StickyWagesPrices.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Gali.StickyWagesPrices.Determinacy4.inCount
#print axioms Gali.StickyWagesPrices.Determinacy4.circleIntegral_sub_inv
#print axioms Gali.StickyWagesPrices.Determinacy4.argument_principle
#print axioms Gali.StickyWagesPrices.Determinacy4.quart
#print axioms Gali.StickyWagesPrices.Determinacy4.eval_quart
#print axioms Gali.StickyWagesPrices.Determinacy4.eval_derivative_quart
#print axioms Gali.StickyWagesPrices.Determinacy4.inCount_path
#print axioms Gali.StickyWagesPrices.Determinacy4.Par
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.mk
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.β
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.σ
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.κp
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.κw
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.lamP
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.lamW
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.φp
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.φw
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.φy
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Ψ
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c0
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c1
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c2
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c3
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c4
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_one
#print axioms Gali.StickyWagesPrices.Determinacy4.circle_cert
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qv
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Qv
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.QC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_qC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_QC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_QC_eq
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_qC_ofReal
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_qC_conj
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_qC_mk
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Adm
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_neg_one
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Ψ_nonneg
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_neg_one_neg
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c0_neg
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.c4_neg
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_one_neg_of_root
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qC_ne_zero_of_norm_eq_one
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.QC_ne_zero_of_norm_eq_one
#print axioms Gali.StickyWagesPrices.Determinacy4.coeff_quart_four
#print axioms Gali.StickyWagesPrices.Determinacy4.quart_ne_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.mix
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.mix_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.mix_one
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.adm_mix
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.continuous_Qv_mix
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.inCount_QC_mix
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Pref
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.QC_ref
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.inCount_ref
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.adm_ref
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.endpt
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.inCount_QC
#print axioms Gali.StickyWagesPrices.Determinacy4.natDegree_quart
#print axioms Gali.StickyWagesPrices.Determinacy4.card_roots_quart
#print axioms Gali.StickyWagesPrices.Determinacy4.outCount
#print axioms Gali.StickyWagesPrices.Determinacy4.inCount_add_outCount
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.QC_ne_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.card_roots_QC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.outCount_QC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.dqr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_derivative_QC
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.continuous_qr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qC_eval_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.inv_mem_out
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.stable_root
#print axioms Gali.StickyWagesPrices.Determinacy4.pow_entry_bound
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_rvMul
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_add
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_sub
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_one
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.rvMul_apply
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.E_rvMul
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.FSolves
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.VAdapted
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.VBounded
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.fsolves_iterate
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.abs_rvMul_pow_le
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.fsolves_unique
#print axioms Gali.StickyWagesPrices.Determinacy4.Fwd.fsolves_exists
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.A0
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.A1
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_A0_sub_A1
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_A0_sub_A1_real
#print axioms Gali.StickyWagesPrices.Determinacy4.B0
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Dr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Brr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Hr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_factor
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.dqr_factor
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.StableVec
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.stableVec_of_hom
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.exists_stableVec
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Cm
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Dm
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Vm
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_Cm_sub_mul
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.rr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qC_eq_mul_rr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.rr_self
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.continuous_rr
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_Cm_sub
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.rr_ne_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Km
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Fm
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_Cm_ne_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Km_eigen
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.IsSol
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.Determinate
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.toS
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.transform
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.eq_iff_fwd
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.toS_adapted
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.toS_bounded
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.mseq
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.ofS
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.toS_ofS
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.mseq_adapted
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.mseq_bounded
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.determinate_of_pos
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_A0
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_A1
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eval_derivative_qC
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.sum_smul_rvMul
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.rvMul_const
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.multiple_solutions_of_mode
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_mode
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_eq
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.map_ofReal_eq
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.no_bounded_solution_of_no_root
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_no_root
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.closedRoots
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.qC_ne_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.mem_closedRoots
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.sr
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.qr_eq_sr
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.sr_self
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.closedRoots_card_ne_one
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.exists_real_eigvec
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.geom_mode
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.abs_pow_le_one
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_complex_root
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.exists_mode_of_two_real_roots
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_two_real_roots
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_double_root
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_neg
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.not_determinate_of_le
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.determinate_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Aw
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.det_A0_mul_det_charmat
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.charpoly_Aw
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.eigen_count_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.Dyn.eq24_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.Lhs
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_one_eq_mul
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.qr_one_pos_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.bookPar
#print axioms Gali.StickyWagesPrices.Determinacy4.bookPar_adm
#print axioms Gali.StickyWagesPrices.Determinacy4.bookPar_Ψ
#print axioms Gali.StickyWagesPrices.Determinacy4.bookPar_Lhs
#print axioms Gali.StickyWagesPrices.Determinacy4.determinacy_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.eigenvalues_iff
#print axioms Gali.StickyWagesPrices.Determinacy4.determinacy_iff_phiY_zero
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.inCount_QC_four
#print axioms Gali.StickyWagesPrices.Determinacy4.Par.no_root_of_inCount_four
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_coeffs
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_adm
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_lhs
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_circle
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_no_root
#print axioms Gali.StickyWagesPrices.Determinacy4.exNE_no_bounded_solution
#print axioms Gali.StickyWagesPrices.Determinacy4.baseline_lambdas
#print axioms Gali.StickyWagesPrices.Determinacy4.exBase
#print axioms Gali.StickyWagesPrices.Determinacy4.exBase_signs
#print axioms Gali.StickyWagesPrices.Determinacy4.exBase_two_roots
#print axioms Gali.StickyWagesPrices.Determinacy4.exBase_multiplicity
#print axioms Gali.StickyWagesPrices.LaborAggregation.cesIndex
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborDemand
#print axioms Gali.StickyWagesPrices.LaborAggregation.r_add_inv
#print axioms Gali.StickyWagesPrices.LaborAggregation.young_key
#print axioms Gali.StickyWagesPrices.LaborAggregation.young_le
#print axioms Gali.StickyWagesPrices.LaborAggregation.young_eq_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.cesIndex_pos
#print axioms Gali.StickyWagesPrices.LaborAggregation.cesIndex_rpow
#print axioms Gali.StickyWagesPrices.LaborAggregation.integral_relWage_rpow
#print axioms Gali.StickyWagesPrices.LaborAggregation.integrable_relWage_rpow
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex_demand
#print axioms Gali.StickyWagesPrices.LaborAggregation.wage_mul_demand
#print axioms Gali.StickyWagesPrices.LaborAggregation.wageBill_demand
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex_nonneg
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex_rpow
#print axioms Gali.StickyWagesPrices.LaborAggregation.integrated_young
#print axioms Gali.StickyWagesPrices.LaborAggregation.wageBill_ge
#print axioms Gali.StickyWagesPrices.LaborAggregation.wageBill_eq_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex_le_of_wageBill
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborIndex_eq_iff_of_wageBill
#print axioms Gali.StickyWagesPrices.LaborAggregation.integral_pos_of_pos
#print axioms Gali.StickyWagesPrices.LaborAggregation.unitInterval_ne_zero
#print axioms Gali.StickyWagesPrices.LaborAggregation.unitInterval_cost_minimisation
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.weightMeasure
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.weightMeasure_singleton
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.weightMeasure_univ_lt_top
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.integrable_weightMeasure
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.integral_weightMeasure
#print axioms Gali.StickyWagesPrices.LaborAggregation.Finite.finite_cost_minimisation
#print axioms Gali.StickyWagesPrices.LaborAggregation.laborDemand_feasible
#print axioms Gali.StickyWagesPrices.LaborAggregation.cost_min_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.dispIntegral
#print axioms Gali.StickyWagesPrices.LaborAggregation.wageDisp
#print axioms Gali.StickyWagesPrices.LaborAggregation.priceDisp
#print axioms Gali.StickyWagesPrices.LaborAggregation.dW
#print axioms Gali.StickyWagesPrices.LaborAggregation.dP
#print axioms Gali.StickyWagesPrices.LaborAggregation.firm_hours
#print axioms Gali.StickyWagesPrices.LaborAggregation.firm_index_level
#print axioms Gali.StickyWagesPrices.LaborAggregation.aggregate_employment
#print axioms Gali.StickyWagesPrices.LaborAggregation.employment_identity
#print axioms Gali.StickyWagesPrices.LaborAggregation.bernoulli_disp
#print axioms Gali.StickyWagesPrices.LaborAggregation.integral_bernoulli_lower
#print axioms Gali.StickyWagesPrices.LaborAggregation.one_le_dispIntegral
#print axioms Gali.StickyWagesPrices.LaborAggregation.log_dispIntegral_nonneg
#print axioms Gali.StickyWagesPrices.LaborAggregation.log_dispIntegral_eq_zero_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.ae_eq_index_iff_const
#print axioms Gali.StickyWagesPrices.LaborAggregation.wage_exponent_lt
#print axioms Gali.StickyWagesPrices.LaborAggregation.price_exponent_lt
#print axioms Gali.StickyWagesPrices.LaborAggregation.dW_nonneg
#print axioms Gali.StickyWagesPrices.LaborAggregation.dW_eq_zero_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.dW_eq_zero_iff_const
#print axioms Gali.StickyWagesPrices.LaborAggregation.dP_nonneg
#print axioms Gali.StickyWagesPrices.LaborAggregation.dP_eq_zero_iff
#print axioms Gali.StickyWagesPrices.LaborAggregation.dP_eq_zero_iff_const
#print axioms Gali.StickyWagesPrices.LaborAggregation.integrable_exp_mul
#print axioms Gali.StickyWagesPrices.LaborAggregation.interior_integrableExpSet
#print axioms Gali.StickyWagesPrices.LaborAggregation.cesIndex_family
#print axioms Gali.StickyWagesPrices.LaborAggregation.log_dispIntegral_family
#print axioms Gali.StickyWagesPrices.LaborAggregation.hasDerivAt_cgf_mul
#print axioms Gali.StickyWagesPrices.LaborAggregation.log_dispIntegral_family_first_order
#print axioms Gali.StickyWagesPrices.LaborAggregation.dW_family_first_order
#print axioms Gali.StickyWagesPrices.LaborAggregation.dP_family_first_order
#print axioms Gali.StickyWagesPrices.LaborAggregation.employment_first_order
#print axioms Gali.StickyWagesPrices.WageDispersion.crossVar
#print axioms Gali.StickyWagesPrices.WageDispersion.bigTheta
#print axioms Gali.StickyWagesPrices.WageDispersion.bigO_mul
#print axioms Gali.StickyWagesPrices.WageDispersion.bigO_weaken
#print axioms Gali.StickyWagesPrices.WageDispersion.monomial_isBigO
#print axioms Gali.StickyWagesPrices.WageDispersion.cgf_taylor
#print axioms Gali.StickyWagesPrices.WageDispersion.cgf_taylor_comp
#print axioms Gali.StickyWagesPrices.WageDispersion.integrable_bounded
#print axioms Gali.StickyWagesPrices.WageDispersion.crossVar_family
#print axioms Gali.StickyWagesPrices.WageDispersion.crossVar_family_isBigO
#print axioms Gali.StickyWagesPrices.WageDispersion.log_dispIntegral_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.dW_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.dP_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.dW_isBigO_sq
#print axioms Gali.StickyWagesPrices.WageDispersion.log_wageDisp_isBigO_sq
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWage
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWageMean
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWage_eq
#print axioms Gali.StickyWagesPrices.WageDispersion.integral_sq_affine
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWage_moments
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWageMean_isBigO
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWage_mean_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.relLogWage_sq_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.log_integral_exp_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.log_laborDemand_sub
#print axioms Gali.StickyWagesPrices.WageDispersion.integral_sq_employment
#print axioms Gali.StickyWagesPrices.WageDispersion.integral_sq_employment_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.GoodDist
#print axioms Gali.StickyWagesPrices.WageDispersion.crossMean
#print axioms Gali.StickyWagesPrices.WageDispersion.crossVarDist
#print axioms Gali.StickyWagesPrices.WageDispersion.wageMix
#print axioms Gali.StickyWagesPrices.WageDispersion.integral_wageMix
#print axioms Gali.StickyWagesPrices.WageDispersion.crossVarDist_eq
#print axioms Gali.StickyWagesPrices.WageDispersion.wageMix_good
#print axioms Gali.StickyWagesPrices.WageDispersion.wageMix_mean
#print axioms Gali.StickyWagesPrices.WageDispersion.wageMix_var
#print axioms Gali.StickyWagesPrices.WageDispersion.wageMix_var_meanChange
#print axioms Gali.StickyWagesPrices.WageDispersion.wage_good
#print axioms Gali.StickyWagesPrices.WageDispersion.wage_var_recursion
#print axioms Gali.StickyWagesPrices.WageDispersion.lemma2_partial
#print axioms Gali.StickyWagesPrices.WageDispersion.lemma2_nonneg
#print axioms Gali.StickyWagesPrices.WageDispersion.lemma2_hasSum
#print axioms Gali.StickyWagesPrices.WageDispersion.lemma2
#print axioms Gali.StickyWagesPrices.WageDispersion.wage_lemma2_calvo_inherited
#print axioms Gali.StickyWagesPrices.WageDispersion.wage_lemma2_calvo
#print axioms Gali.StickyWagesPrices.WageDispersion.logWageIndex_second_order
#print axioms Gali.StickyWagesPrices.WageDispersion.wageInflation_sub_meanChange
#print axioms Gali.StickyWagesPrices.WageDispersion.wageInflation_sq_sub_meanChange_sq
#print axioms Gali.StickyWagesPrices.WageSetting.summable_geometric_bounded
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_E_of_remainder
#print axioms Gali.StickyWagesPrices.WageSetting.remainder_le_of_lipschitz_deriv
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_E
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_tsum_E
#print axioms Gali.StickyWagesPrices.WageSetting.markup
#print axioms Gali.StickyWagesPrices.WageSetting.one_lt_markup
#print axioms Gali.StickyWagesPrices.WageSetting.markup_pos
#print axioms Gali.StickyWagesPrices.WageSetting.demand
#print axioms Gali.StickyWagesPrices.WageSetting.demand_eq
#print axioms Gali.StickyWagesPrices.WageSetting.demand_pos
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_demand
#print axioms Gali.StickyWagesPrices.WageSetting.profit
#print axioms Gali.StickyWagesPrices.WageSetting.objective
#print axioms Gali.StickyWagesPrices.WageSetting.focTerm
#print axioms Gali.StickyWagesPrices.WageSetting.focSum
#print axioms Gali.StickyWagesPrices.WageSetting.profitDeriv
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_profit
#print axioms Gali.StickyWagesPrices.WageSetting.E_profitDeriv
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_objective
#print axioms Gali.StickyWagesPrices.WageSetting.foc_of_isLocalMax
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_objective_of_pos
#print axioms Gali.StickyWagesPrices.WageSetting.focCore
#print axioms Gali.StickyWagesPrices.WageSetting.focTerm_eq
#print axioms Gali.StickyWagesPrices.WageSetting.focCore_sub_ge
#print axioms Gali.StickyWagesPrices.WageSetting.E_focCore_le
#print axioms Gali.StickyWagesPrices.WageSetting.E_weight_nonneg
#print axioms Gali.StickyWagesPrices.WageSetting.E_focCore_eq
#print axioms Gali.StickyWagesPrices.WageSetting.isMaxOn_iff_foc
#print axioms Gali.StickyWagesPrices.WageSetting.objective_flexible
#print axioms Gali.StickyWagesPrices.WageSetting.focSum_flexible
#print axioms Gali.StickyWagesPrices.WageSetting.flexible_foc_iff
#print axioms Gali.StickyWagesPrices.WageSetting.flexible_optimum
#print axioms Gali.StickyWagesPrices.WageSetting.steadyState_foc_iff
#print axioms Gali.StickyWagesPrices.WageSetting.logMarkup
#print axioms Gali.StickyWagesPrices.WageSetting.focLHS
#print axioms Gali.StickyWagesPrices.WageSetting.focSum_eq_focLHS
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_E_exp
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_focLHS_path
#print axioms Gali.StickyWagesPrices.WageSetting.eq12_iff
#print axioms Gali.StickyWagesPrices.WageSetting.Primitives
#print axioms Gali.StickyWagesPrices.WageSetting.weight_bounds
#print axioms Gali.StickyWagesPrices.WageSetting.demand_bounds
#print axioms Gali.StickyWagesPrices.WageSetting.profitDeriv_eq
#print axioms Gali.StickyWagesPrices.WageSetting.profitDeriv2
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_profitDeriv
#print axioms Gali.StickyWagesPrices.WageSetting.abs_profitDeriv_le
#print axioms Gali.StickyWagesPrices.WageSetting.abs_profitDeriv2_le
#print axioms Gali.StickyWagesPrices.WageSetting.lipschitz_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.dominated_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.summable_profit_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_objective_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.foc_of_isLocalMax_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.isMaxOn_iff_foc_of_primitives
#print axioms Gali.StickyWagesPrices.WageSetting.unionSurplus
#print axioms Gali.StickyWagesPrices.WageSetting.unionObjective
#print axioms Gali.StickyWagesPrices.WageSetting.E_tsum_unionObjective
#print axioms Gali.StickyWagesPrices.WageSetting.disutil
#print axioms Gali.StickyWagesPrices.WageSetting.dDisutil
#print axioms Gali.StickyWagesPrices.WageSetting.d2Disutil
#print axioms Gali.StickyWagesPrices.WageSetting.unionQ
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_disutil
#print axioms Gali.StickyWagesPrices.WageSetting.hasDerivAt_dDisutil
#print axioms Gali.StickyWagesPrices.WageSetting.d2Disutil_nonneg
#print axioms Gali.StickyWagesPrices.WageSetting.profit_unionQ
#print axioms Gali.StickyWagesPrices.WageSetting.unionObjective_eq
#print axioms Gali.StickyWagesPrices.WageSetting.mrsReset
#print axioms Gali.StickyWagesPrices.WageSetting.foc11Term
#print axioms Gali.StickyWagesPrices.WageSetting.foc11
#print axioms Gali.StickyWagesPrices.WageSetting.focTerm_union
#print axioms Gali.StickyWagesPrices.WageSetting.focSum_union
#print axioms Gali.StickyWagesPrices.WageSetting.UnionPrimitives
#print axioms Gali.StickyWagesPrices.WageSetting.rpow_le_add
#print axioms Gali.StickyWagesPrices.WageSetting.disutil_factor_bounds
#print axioms Gali.StickyWagesPrices.WageSetting.primitives_of_union
#print axioms Gali.StickyWagesPrices.WageSetting.union_hasDerivAt
#print axioms Gali.StickyWagesPrices.WageSetting.union_foc_of_isLocalMax
#print axioms Gali.StickyWagesPrices.WageSetting.union_isMaxOn_iff_foc
#print axioms Gali.StickyWagesPrices.WageSetting.cesIndex_const
#print axioms Gali.StickyWagesPrices.WageSetting.flexible_wage_index
#print axioms Gali.StickyWagesPrices.WageSetting.union_flexible
#print axioms Gali.StickyWagesPrices.WageSetting.union_steadyState_foc_iff
#print axioms Gali.StickyWagesPrices.WageSetting.foc11_eq_focLHS
#print axioms Gali.StickyWagesPrices.WageSetting.log_mrsReset
#print axioms Gali.StickyWagesPrices.WageSetting.mrs_correction_first_order
#print axioms Gali.StickyWagesPrices.WageSetting.markupGap
#print axioms Gali.StickyWagesPrices.WageSetting.eq13
#print axioms Gali.StickyWagesPrices.WageInflation.integral_wage_mix
#print axioms Gali.StickyWagesPrices.WageInflation.wage_recursion_of_dist
#print axioms Gali.StickyWagesPrices.WageInflation.wage_dist_law_of_motion
#print axioms Gali.StickyWagesPrices.WageInflation.wage_recursion
#print axioms Gali.StickyWagesPrices.WageInflation.lottery_model
#print axioms Gali.StickyWagesPrices.WageInflation.wage_recursion_lottery
#print axioms Gali.StickyWagesPrices.WageInflation.dist_k_step
#print axioms Gali.StickyWagesPrices.WageInflation.prob_identity
#print axioms Gali.StickyWagesPrices.WageInflation.prob_identity_range
#print axioms Gali.StickyWagesPrices.WageInflation.dist_k_step_mass
#print axioms Gali.StickyWagesPrices.WageInflation.rpow_eq_one_iff
#print axioms Gali.StickyWagesPrices.WageInflation.zero_wage_inflation_iff
#print axioms Gali.StickyWagesPrices.WageInflation.zero_wage_inflation_levels
#print axioms Gali.StickyWagesPrices.WageInflation.inflFn
#print axioms Gali.StickyWagesPrices.WageInflation.log_infl_eq_inflFn
#print axioms Gali.StickyWagesPrices.WageInflation.inflFn_zero
#print axioms Gali.StickyWagesPrices.WageInflation.hasDerivAt_inflFn
#print axioms Gali.StickyWagesPrices.WageInflation.inflFn_isLittleO
#print axioms Gali.StickyWagesPrices.WageInflation.recursion_levels_iff
#print axioms Gali.StickyWagesPrices.WageInflation.wage_index_recursion
#print axioms Gali.StickyWagesPrices.WageInflation.log_wage_law_of_motion
#print axioms Gali.StickyWagesPrices.WageInflation.log_wageIndex_eq
#print axioms Gali.StickyWagesPrices.WageInflation.eq14_tangent
#print axioms Gali.StickyWagesPrices.WageInflation.eq14_iff
#print axioms Gali.StickyWagesPrices.WageInflation.lambdaW
#print axioms Gali.StickyWagesPrices.WageInflation.wageInfl
#print axioms Gali.StickyWagesPrices.WageInflation.eq15_iff
#print axioms Gali.StickyWagesPrices.WageInflation.lambdaW_pos
#print axioms Gali.StickyWagesPrices.WageInflation.lambdaW_strictAntiOn_theta
#print axioms Gali.StickyWagesPrices.WageInflation.lambdaW_strictAntiOn_eps
#print axioms Gali.StickyWagesPrices.WageInflation.lambdaW_strictAntiOn_phi
#print axioms Gali.StickyWagesPrices.GapForm.psiYA
#print axioms Gali.StickyWagesPrices.GapForm.psiWA
#print axioms Gali.StickyWagesPrices.GapForm.psiY
#print axioms Gali.StickyWagesPrices.GapForm.thetaY
#print axioms Gali.StickyWagesPrices.GapForm.kappaP
#print axioms Gali.StickyWagesPrices.GapForm.kappaW
#print axioms Gali.StickyWagesPrices.GapForm.denom_pos
#print axioms Gali.StickyWagesPrices.GapForm.psiWA_eq
#print axioms Gali.StickyWagesPrices.GapForm.psiWA_pos
#print axioms Gali.StickyWagesPrices.GapForm.alpha_psiYA_lt_one
#print axioms Gali.StickyWagesPrices.GapForm.thetaY_pos
#print axioms Gali.StickyWagesPrices.GapForm.kappaP_nonneg
#print axioms Gali.StickyWagesPrices.GapForm.kappaW_pos
#print axioms Gali.StickyWagesPrices.GapForm.natural_allocation_iff
#print axioms Gali.StickyWagesPrices.GapForm.natWage_constant_ne_zero
#print axioms Gali.StickyWagesPrices.GapForm.priceMarkup_gap
#print axioms Gali.StickyWagesPrices.GapForm.wageMarkup_gap
#print axioms Gali.StickyWagesPrices.GapForm.PriceNKPC
#print axioms Gali.StickyWagesPrices.GapForm.WageNKPC
#print axioms Gali.StickyWagesPrices.GapForm.PriceGapNKPC
#print axioms Gali.StickyWagesPrices.GapForm.WageGapNKPC
#print axioms Gali.StickyWagesPrices.GapForm.priceNKPC_iff_gap
#print axioms Gali.StickyWagesPrices.GapForm.wageNKPC_iff_gap
#print axioms Gali.StickyWagesPrices.GapForm.priceNKPC_iff_gap_of_levels
#print axioms Gali.StickyWagesPrices.GapForm.wageNKPC_iff_gap_of_levels
#print axioms Gali.StickyWagesPrices.GapForm.wageGap_identity
#print axioms Gali.StickyWagesPrices.GapForm.EulerOutput
#print axioms Gali.StickyWagesPrices.GapForm.natOutput
#print axioms Gali.StickyWagesPrices.GapForm.natRate
#print axioms Gali.StickyWagesPrices.GapForm.DISGap
#print axioms Gali.StickyWagesPrices.GapForm.natRate_ar1
#print axioms Gali.StickyWagesPrices.GapForm.euler_iff_disGap
#print axioms Gali.StickyWagesPrices.GapForm.euler_iff_disGap_ar1
#print axioms Gali.StickyWagesPrices.GapForm.compositeInfl
#print axioms Gali.StickyWagesPrices.GapForm.kappaBar
#print axioms Gali.StickyWagesPrices.GapForm.composite_nkpc
#print axioms Gali.StickyWagesPrices.GapForm.kappaBar_eq
#print axioms Gali.StickyWagesPrices.GapForm.composite_nkpc_explicit
#print axioms Gali.StickyWagesPrices.GapForm.kappaBar_pos
#print axioms Gali.StickyWagesPrices.GapForm.kappaBar_strictly_between
#print axioms Gali.StickyWagesPrices.GapForm.kappa_common
#print axioms Gali.StickyWagesPrices.System.Rule
#print axioms Gali.StickyWagesPrices.System.WageGapLaw
#print axioms Gali.StickyWagesPrices.System.Equilibrium
#print axioms Gali.StickyWagesPrices.System.A0
#print axioms Gali.StickyWagesPrices.System.A1
#print axioms Gali.StickyWagesPrices.System.B0
#print axioms Gali.StickyWagesPrices.System.stateVec
#print axioms Gali.StickyWagesPrices.System.shockVec
#print axioms Gali.StickyWagesPrices.System.MatrixEq
#print axioms Gali.StickyWagesPrices.System.matrixEq_iff_rows
#print axioms Gali.StickyWagesPrices.System.equilibrium_iff_matrixEq
#print axioms Gali.StickyWagesPrices.System.u1_linear
#print axioms Gali.StickyWagesPrices.System.zeroPath_iff
#print axioms Gali.StickyWagesPrices.System.zeroPath_exists_iff
#print axioms Gali.StickyWagesPrices.System.zeroPath_iff_primitives
#print axioms Gali.StickyWagesPrices.System.zeroPath_solves_any_phiY
#print axioms Gali.StickyWagesPrices.System.zeroPath_fails_v_eq_rn
#print axioms Gali.StickyWagesPrices.System.detLHS
#print axioms Gali.StickyWagesPrices.System.det_A0_sub_A1
#print axioms Gali.StickyWagesPrices.System.det_A0_sub_A1_eq
#print axioms Gali.StickyWagesPrices.System.det_A0
#print axioms Gali.StickyWagesPrices.System.det_A0_pos
#print axioms Gali.StickyWagesPrices.System.one_eigenvalue_iff
#print axioms Gali.StickyWagesPrices.System.det_neg_iff
#print axioms Gali.StickyWagesPrices.System.detCondition_phiY_zero
#print axioms Gali.StickyWagesPrices.System.threshold
#print axioms Gali.StickyWagesPrices.System.detCondition_iff_threshold
#print axioms Gali.StickyWagesPrices.System.threshold_zero
#print axioms Gali.StickyWagesPrices.System.threshold_strictAnti
#print axioms Gali.StickyWagesPrices.Efficiency.utilC
#print axioms Gali.StickyWagesPrices.Efficiency.disutilN
#print axioms Gali.StickyWagesPrices.Efficiency.periodUtility
#print axioms Gali.StickyWagesPrices.Efficiency.hasDerivAt_utilC
#print axioms Gali.StickyWagesPrices.Efficiency.hasDerivAt_disutilN
#print axioms Gali.StickyWagesPrices.Efficiency.antitoneOn_margUtil
#print axioms Gali.StickyWagesPrices.Efficiency.le_tangent
#print axioms Gali.StickyWagesPrices.Efficiency.utilC_le_tangent
#print axioms Gali.StickyWagesPrices.Efficiency.disutilN_tangent_le
#print axioms Gali.StickyWagesPrices.Efficiency.utilC_lt_utilC
#print axioms Gali.StickyWagesPrices.Efficiency.marginal_utilities
#print axioms Gali.StickyWagesPrices.Efficiency.mrs
#print axioms Gali.StickyWagesPrices.Efficiency.mpn
#print axioms Gali.StickyWagesPrices.Efficiency.hasDerivAt_output
#print axioms Gali.StickyWagesPrices.Efficiency.mpn_pos
#print axioms Gali.StickyWagesPrices.Efficiency.rpow_le_tangent
#print axioms Gali.StickyWagesPrices.Efficiency.eq_of_rpow_eq_tangent
#print axioms Gali.StickyWagesPrices.Efficiency.symWelfare
#print axioms Gali.StickyWagesPrices.Efficiency.effEmployment
#print axioms Gali.StickyWagesPrices.Efficiency.hasDerivAt_symWelfare
#print axioms Gali.StickyWagesPrices.Efficiency.mrs_mul_eq
#print axioms Gali.StickyWagesPrices.Efficiency.effExponent_pos
#print axioms Gali.StickyWagesPrices.Efficiency.effEmployment_pos
#print axioms Gali.StickyWagesPrices.Efficiency.mrs_sym_eq_mpn_iff
#print axioms Gali.StickyWagesPrices.Efficiency.symWelfare_le_of_foc
#print axioms Gali.StickyWagesPrices.Efficiency.foc_of_symWelfare_isMax
#print axioms Gali.StickyWagesPrices.Efficiency.symWelfare_isMax_iff_foc
#print axioms Gali.StickyWagesPrices.Efficiency.symWelfare_le_eff
#print axioms Gali.StickyWagesPrices.Efficiency.symWelfare_lt
#print axioms Gali.StickyWagesPrices.Efficiency.existsUnique_efficient
#print axioms Gali.StickyWagesPrices.Efficiency.CES.PosAlloc
#print axioms Gali.StickyWagesPrices.Efficiency.CES.r_mem
#print axioms Gali.StickyWagesPrices.Efficiency.CES.q_mem
#print axioms Gali.StickyWagesPrices.Efficiency.CES.integrable_rpow
#print axioms Gali.StickyWagesPrices.Efficiency.CES.integral_rpow_le
#print axioms Gali.StickyWagesPrices.Efficiency.CES.cesIndex_of_ae_eq
#print axioms Gali.StickyWagesPrices.Efficiency.CES.cesIndex_le_integral
#print axioms Gali.StickyWagesPrices.Efficiency.CES.cesIndex_eq_integral_iff
#print axioms Gali.StickyWagesPrices.Efficiency.CES.output_rpow
#print axioms Gali.StickyWagesPrices.Efficiency.CES.symmetric_index
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourIndex
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.firmHours
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourSupply
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.totalHours
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.goodsOutput
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.aggConsumption
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.Feasible
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.firmHours_posAlloc
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourSupply_integral
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourIndex_nonneg
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourIndex_measurable
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.labourIndex_le_firmHours
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.aggConsumption_eq
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.integral_labourIndex_rpow
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.aggConsumption_le
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.symmetric_consequences
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.aggConsumption_pos
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.aggConsumption_eq_iff
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.disutility_ge
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_le_symWelfare
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_eq_symWelfare_iff
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_lt_symWelfare
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.feasible_const
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_const
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_le_eff
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.welfare_lt_of_not_symmetric
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.planner_optimal_iff
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.planner_optimal_iff_effEmployment
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.planner_existsUnique
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.isProbabilityMeasure_unitInterval
#print axioms Gali.StickyWagesPrices.Efficiency.Planner.planner_optimal_iff_unitInterval
#print axioms Gali.StickyWagesPrices.Efficiency.markup
#print axioms Gali.StickyWagesPrices.Efficiency.one_lt_markup
#print axioms Gali.StickyWagesPrices.Efficiency.markup_pos
#print axioms Gali.StickyWagesPrices.Efficiency.demand_at_equal_prices
#print axioms Gali.StickyWagesPrices.Efficiency.flexEmployment
#print axioms Gali.StickyWagesPrices.Efficiency.flexEmployment_pos
#print axioms Gali.StickyWagesPrices.Efficiency.mrs_eq_mpn_div_iff
#print axioms Gali.StickyWagesPrices.Efficiency.existsUnique_flex
#print axioms Gali.StickyWagesPrices.Efficiency.flexEmployment_eq_eff_iff
#print axioms Gali.StickyWagesPrices.Efficiency.flex_mrs_eq
#print axioms Gali.StickyWagesPrices.Efficiency.flex_efficient_iff_wedge
#print axioms Gali.StickyWagesPrices.Efficiency.wedge_eq_one_iff_subsidy
#print axioms Gali.StickyWagesPrices.Efficiency.optimalSubsidy_mem
#print axioms Gali.StickyWagesPrices.Efficiency.optimalSubsidy_flexWages
#print axioms Gali.StickyWagesPrices.Efficiency.flex_equilibrium
#print axioms Gali.StickyWagesPrices.Efficiency.flex_equilibrium_efficient_iff
#print axioms Gali.StickyWagesPrices.Efficiency.existsUnique_subsidy
#print axioms Gali.StickyWagesPrices.Welfare.upsilon
#print axioms Gali.StickyWagesPrices.Welfare.effWageDisp
#print axioms Gali.StickyWagesPrices.Welfare.ratio_rpow_family
#print axioms Gali.StickyWagesPrices.Welfare.dispIntegral_family_pos
#print axioms Gali.StickyWagesPrices.Welfare.effWageDisp_second_order
#print axioms Gali.StickyWagesPrices.Welfare.effWageDisp_sub_wageDisp
#print axioms Gali.StickyWagesPrices.Welfare.firmLabour_eq
#print axioms Gali.StickyWagesPrices.Welfare.disutility_types_eq
#print axioms Gali.StickyWagesPrices.Welfare.effectiveHours_identity
#print axioms Gali.StickyWagesPrices.Welfare.tendsto_zero_of_bigO
#print axioms Gali.StickyWagesPrices.Welfare.taylor_two
#print axioms Gali.StickyWagesPrices.Welfare.exp_taylor_two
#print axioms Gali.StickyWagesPrices.Welfare.exp_sub_one_bigO
#print axioms Gali.StickyWagesPrices.Welfare.logdev_taylor
#print axioms Gali.StickyWagesPrices.Welfare.gapCoeff
#print axioms Gali.StickyWagesPrices.Welfare.psiYA
#print axioms Gali.StickyWagesPrices.Welfare.secondOrderUtility
#print axioms Gali.StickyWagesPrices.Welfare.tip
#print axioms Gali.StickyWagesPrices.Welfare.welfareQuadratic
#print axioms Gali.StickyWagesPrices.Welfare.gapCoeff_mul_psiYA
#print axioms Gali.StickyWagesPrices.Welfare.gapCoeff_eq
#print axioms Gali.StickyWagesPrices.Welfare.upsilon_split
#print axioms Gali.StickyWagesPrices.Welfare.secondOrderUtility_eq
#print axioms Gali.StickyWagesPrices.Welfare.secondOrderUtility_distorted
#print axioms Gali.StickyWagesPrices.Welfare.period_utility_second_order
#print axioms Gali.StickyWagesPrices.Welfare.deriv_negDisutil
#print axioms Gali.StickyWagesPrices.Welfare.negDisutil_phi
#print axioms Gali.StickyWagesPrices.Welfare.negDisutil_contDiffAt
#print axioms Gali.StickyWagesPrices.Welfare.period_utility_second_order_families
#print axioms Gali.StickyWagesPrices.Welfare.lemma2_inherited
#print axioms Gali.StickyWagesPrices.Welfare.lemma2_printed_fails_with_inherited
#print axioms Gali.StickyWagesPrices.Welfare.lambdaP
#print axioms Gali.StickyWagesPrices.Welfare.lambdaW
#print axioms Gali.StickyWagesPrices.Welfare.priceWeight
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight
#print axioms Gali.StickyWagesPrices.Welfare.periodLoss
#print axioms Gali.StickyWagesPrices.Welfare.welfareLoss
#print axioms Gali.StickyWagesPrices.Welfare.avgLoss
#print axioms Gali.StickyWagesPrices.Welfare.priceWeight_of_dispersion
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_of_dispersion
#print axioms Gali.StickyWagesPrices.Welfare.welfare_eq_loss
#print axioms Gali.StickyWagesPrices.Welfare.welfare_eq_loss_inherited
#print axioms Gali.StickyWagesPrices.Welfare.welfare_eq_loss_calvo
#print axioms Gali.StickyWagesPrices.Welfare.welfare_stationary
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_eq
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_strictMonoOn_eps
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_strictAnti_alpha
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_strictMonoOn_theta
#print axioms Gali.StickyWagesPrices.Welfare.lambdaW_strictAntiOn_theta
#print axioms Gali.StickyWagesPrices.Welfare.wageWeight_pos
#print axioms Gali.StickyWagesPrices.LimitingCases.PricePC
#print axioms Gali.StickyWagesPrices.LimitingCases.WagePC
#print axioms Gali.StickyWagesPrices.LimitingCases.NKPC
#print axioms Gali.StickyWagesPrices.LimitingCases.kappaP
#print axioms Gali.StickyWagesPrices.LimitingCases.kappaW
#print axioms Gali.StickyWagesPrices.LimitingCases.kappaP_add
#print axioms Gali.StickyWagesPrices.LimitingCases.kappaW_add
#print axioms Gali.StickyWagesPrices.LimitingCases.flexWage_realWageGap
#print axioms Gali.StickyWagesPrices.LimitingCases.flexWage_nkpc
#print axioms Gali.StickyWagesPrices.LimitingCases.flexWage_no_wage_dispersion
#print axioms Gali.StickyWagesPrices.LimitingCases.lambdaW_tendsto_atTop
#print axioms Gali.StickyWagesPrices.LimitingCases.lambdaP_tendsto_atTop
#print axioms Gali.StickyWagesPrices.LimitingCases.wageWeight_tendsto_zero
#print axioms Gali.StickyWagesPrices.LimitingCases.priceWeight_tendsto_zero
#print axioms Gali.StickyWagesPrices.LimitingCases.flexPrice_realWageGap
#print axioms Gali.StickyWagesPrices.LimitingCases.flexPrice_nkpc
#print axioms Gali.StickyWagesPrices.LimitingCases.nkLoss
#print axioms Gali.StickyWagesPrices.LimitingCases.nkLoss_nonneg
#print axioms Gali.StickyWagesPrices.LimitingCases.nkLoss_zero
#print axioms Gali.StickyWagesPrices.LimitingCases.nkpc_zero
#print axioms Gali.StickyWagesPrices.LimitingCases.nk_zero_optimal
#print axioms Gali.StickyWagesPrices.LimitingCases.nk_zero_unique_pf
#print axioms Gali.StickyWagesPrices.LimitingCases.flexWage_optimal
#print axioms Gali.StickyWagesPrices.LimitingCases.flexWage_strictPrice_forces_zero_gap
#print axioms Gali.StickyWagesPrices.LimitingCases.flexPrice_optimal
#print axioms Gali.StickyWagesPrices.LimitingCases.Feasible
#print axioms Gali.StickyWagesPrices.LimitingCases.loss
#print axioms Gali.StickyWagesPrices.LimitingCases.dirY
#print axioms Gali.StickyWagesPrices.LimitingCases.dirP
#print axioms Gali.StickyWagesPrices.LimitingCases.dirW
#print axioms Gali.StickyWagesPrices.LimitingCases.dirOm
#print axioms Gali.StickyWagesPrices.LimitingCases.feasible_dir
#print axioms Gali.StickyWagesPrices.LimitingCases.feasible_add
#print axioms Gali.StickyWagesPrices.LimitingCases.loss_two
#print axioms Gali.StickyWagesPrices.LimitingCases.quad_improve
#print axioms Gali.StickyWagesPrices.LimitingCases.growth
#print axioms Gali.StickyWagesPrices.LimitingCases.zero_of_growth
#print axioms Gali.StickyWagesPrices.LimitingCases.sq_le_of_growth
#print axioms Gali.StickyWagesPrices.LimitingCases.not_summable_of_ge
#print axioms Gali.StickyWagesPrices.LimitingCases.bigM
#print axioms Gali.StickyWagesPrices.LimitingCases.priceShock
#print axioms Gali.StickyWagesPrices.LimitingCases.spY
#print axioms Gali.StickyWagesPrices.LimitingCases.spW
#print axioms Gali.StickyWagesPrices.LimitingCases.spOm
#print axioms Gali.StickyWagesPrices.LimitingCases.feasible_sp
#print axioms Gali.StickyWagesPrices.LimitingCases.sp_unique
#print axioms Gali.StickyWagesPrices.LimitingCases.strict_price_targeting_suboptimal
#print axioms Gali.StickyWagesPrices.LimitingCases.wageShock
#print axioms Gali.StickyWagesPrices.LimitingCases.swP
#print axioms Gali.StickyWagesPrices.LimitingCases.swOm
#print axioms Gali.StickyWagesPrices.LimitingCases.feasible_sw
#print axioms Gali.StickyWagesPrices.LimitingCases.sw_unique
#print axioms Gali.StickyWagesPrices.LimitingCases.strict_wage_targeting_suboptimal
#print axioms Gali.StickyWagesPrices.LimitingCases.model_coefficients
#print axioms Gali.StickyWagesPrices.LimitingCases.strict_price_targeting_suboptimal_model
#print axioms Gali.StickyWagesPrices.LimitingCases.strict_wage_targeting_suboptimal_model
#print axioms Gali.StickyWagesPrices.Calibration.lambdaP_baseline
#print axioms Gali.StickyWagesPrices.Calibration.lambdaW_baseline
#print axioms Gali.StickyWagesPrices.Calibration.kappaP_baseline
#print axioms Gali.StickyWagesPrices.Calibration.kappaW_baseline
#print axioms Gali.StickyWagesPrices.Calibration.compositeWeight_baseline
#print axioms Gali.StickyWagesPrices.Calibration.compositePriceWeight_baseline
#print axioms Gali.StickyWagesPrices.Calibration.gapCoeff_baseline
#print axioms Gali.StickyWagesPrices.Calibration.priceWeight_baseline
#print axioms Gali.StickyWagesPrices.Calibration.wageWeight_baseline
#print axioms Gali.StickyWagesPrices.Calibration.wageWeight_gt_priceWeight_baseline
#print axioms Gali.StickyWagesPrices.Calibration.tableLoss
#print axioms Gali.StickyWagesPrices.Calibration.table61_losses
#print axioms Gali.StickyWagesPrices.Calibration.table61_ranking
#print axioms Gali.StickyWagesPrices.Calibration.table61_flexible_swap
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.mk
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.β
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.kapP
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.kapW
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.lamP
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.lamW
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.ay
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.ap
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Coef.aw
#print axioms Gali.StickyWagesPrices.OptimalPolicy.bookCoef
#print axioms Gali.StickyWagesPrices.OptimalPolicy.prev
#print axioms Gali.StickyWagesPrices.OptimalPolicy.prev_zero
#print axioms Gali.StickyWagesPrices.OptimalPolicy.prev_succ
#print axioms Gali.StickyWagesPrices.OptimalPolicy.prev_sub
#print axioms Gali.StickyWagesPrices.OptimalPolicy.lagrangian_alg
#print axioms Gali.StickyWagesPrices.OptimalPolicy.hasSum_of_telescope
#print axioms Gali.StickyWagesPrices.OptimalPolicy.tendsto_disc_abs
#print axioms Gali.StickyWagesPrices.OptimalPolicy.tendsto_disc_partial
#print axioms Gali.StickyWagesPrices.OptimalPolicy.summable_sub_sq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.Feasible
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.FOC
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.BoundedMult
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.lossTerm
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.FiniteLoss
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.loss
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.IsOptimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.summable_sq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.prev_sub_eq_sum
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.loss_sub_hasSum
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.isOptimal_of_foc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.eq_of_loss_eq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.isOptimal_iff_foc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.existsUnique_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.Constr
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.Plan
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.FOCs
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.periodLoss
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.devLoss
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.cross
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.E_nonneg
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss_hasSum
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.period_identity
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.E0_identity
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.E0_devLoss_nonneg
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss_sub_hasSum
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss_le_of_foc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.eq_of_expLoss_eq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.commitment_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.A0
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.A1
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.B0
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.stateVec
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.MatrixSystem
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.matrix_form_iff
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.demand_zero_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss_nonneg
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.expLoss_zero
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.zero_plan
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.demand_zero_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.DIS
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.RuleEqm
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.RuleDeterminate
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.rule_implements
#print axioms Gali.StickyWagesPrices.OptimalPolicy.exists_block_root
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.block_zero
#print axioms Gali.StickyWagesPrices.OptimalPolicy.ruleA
#print axioms Gali.StickyWagesPrices.OptimalPolicy.det2_ruleA
#print axioms Gali.StickyWagesPrices.OptimalPolicy.tr2_ruleA
#print axioms Gali.StickyWagesPrices.OptimalPolicy.schur_ruleA_iff
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.stack
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.solves_ruleA_iff
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.ruleDeterminate_of_kap_eq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.not_ruleDeterminate
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.ruleDeterminate_iff
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.rulePar
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.rule_isSol
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.ruleDeterminate_of_phiP
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.ruleDeterminate_book
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.rule_implements_book
#print axioms Gali.StickyWagesPrices.OptimalPolicy.book_composite_slope
#print axioms Gali.StickyWagesPrices.OptimalPolicy.book_fn6
#print axioms Gali.StickyWagesPrices.OptimalPolicy.bookCoef_pos
#print axioms Gali.StickyWagesPrices.OptimalPolicy.composite_alg
#print axioms Gali.StickyWagesPrices.OptimalPolicy.kap_ne_zero
#print axioms Gali.StickyWagesPrices.OptimalPolicy.separation
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.composite_foc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.pibar
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.composite_nkpc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.composite_foc
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.projP
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.projW
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.block_of_constr
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.proj_plan
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.periodLoss_sub_proj
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.eq_proj_of_pibar
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.composite_targeting_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.wSeq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.wSeq_eq
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.prev_adapted
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.exists_composite_plan
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.composite_targeting_solves
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Stoch.composite_zero_iff
#print axioms Gali.StickyWagesPrices.OptimalPolicy.calvo
#print axioms Gali.StickyWagesPrices.OptimalPolicy.lamWOf
#print axioms Gali.StickyWagesPrices.OptimalPolicy.lamPOf
#print axioms Gali.StickyWagesPrices.OptimalPolicy.calvo_pos
#print axioms Gali.StickyWagesPrices.OptimalPolicy.calvo_strictAntiOn
#print axioms Gali.StickyWagesPrices.OptimalPolicy.wage_weight_strictMonoOn
#print axioms Gali.StickyWagesPrices.OptimalPolicy.price_weight_strictMonoOn
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.block_zero_finite
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.projP
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.projW
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.pibar
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.proj_feasible
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.lossTerm_sub_proj
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.composite_targeting_optimal
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.finiteLoss_of_bounded
#print axioms Gali.StickyWagesPrices.OptimalPolicy.Det.composite_targeting_existsUnique
#print axioms Gali.StickyWagesPrices.OptimalPolicy.book_special_case
#print axioms Gali.StickyWagesPrices.OptimalPolicy.composite_path_satisfies_34_35
#print axioms Gali.StickyWagesPrices.Ex6_1.firm_optimal_iff
#print axioms Gali.StickyWagesPrices.Ex6_1.labor_demand_log
#print axioms Gali.StickyWagesPrices.Ex6_1.FlexEq
#print axioms Gali.StickyWagesPrices.Ex6_1.flexEq_iff
#print axioms Gali.StickyWagesPrices.Ex6_1.ResetWage
#print axioms Gali.StickyWagesPrices.Ex6_1.WageIndex
#print axioms Gali.StickyWagesPrices.Ex6_1.PriceEq
#print axioms Gali.StickyWagesPrices.Ex6_1.nCheck
#print axioms Gali.StickyWagesPrices.Ex6_1.uShock
#print axioms Gali.StickyWagesPrices.Ex6_1.inflation_eq_iff
#print axioms Gali.StickyWagesPrices.Ex6_1.IS
#print axioms Gali.StickyWagesPrices.Ex6_1.StickyEq
#print axioms Gali.StickyWagesPrices.Ex6_1.drift_const_of_bounded
#print axioms Gali.StickyWagesPrices.Ex6_1.iOpt
#print axioms Gali.StickyWagesPrices.Ex6_1.optimal_unique
#print axioms Gali.StickyWagesPrices.Ex6_1.optimal_exists
#print axioms Gali.StickyWagesPrices.Ex6_2.Kc
#print axioms Gali.StickyWagesPrices.Ex6_2.rnat
#print axioms Gali.StickyWagesPrices.Ex6_2.qE
#print axioms Gali.StickyWagesPrices.Ex6_2.flex_iff
#print axioms Gali.StickyWagesPrices.Ex6_2.flex_any_price
#print axioms Gali.StickyWagesPrices.Ex6_2.flex_two_equilibria
#print axioms Gali.StickyWagesPrices.Ex6_2.WageInAdvance
#print axioms Gali.StickyWagesPrices.Ex6_2.ISfwd
#print axioms Gali.StickyWagesPrices.Ex6_2.Block
#print axioms Gali.StickyWagesPrices.Ex6_2.wage_facts
#print axioms Gali.StickyWagesPrices.Ex6_2.expected_y
#print axioms Gali.StickyWagesPrices.Ex6_2.expected_IS
#print axioms Gali.StickyWagesPrices.Ex6_2.n_from_IS
#print axioms Gali.StickyWagesPrices.Ex6_2.TaylorRule
#print axioms Gali.StickyWagesPrices.Ex6_2.gam
#print axioms Gali.StickyWagesPrices.Ex6_2.cEps
#print axioms Gali.StickyWagesPrices.Ex6_2.qE_bounded
#print axioms Gali.StickyWagesPrices.Ex6_2.taylor_unique
#print axioms Gali.StickyWagesPrices.Ex6_2.innov
#print axioms Gali.StickyWagesPrices.Ex6_2.pPath
#print axioms Gali.StickyWagesPrices.Ex6_2.innov_adapted
#print axioms Gali.StickyWagesPrices.Ex6_2.innov_E
#print axioms Gali.StickyWagesPrices.Ex6_2.pPath_adapted
#print axioms Gali.StickyWagesPrices.Ex6_2.pPath_E
#print axioms Gali.StickyWagesPrices.Ex6_2.taylor_exists
#print axioms Gali.StickyWagesPrices.Ex6_2.optimal_real_rate
#print axioms Gali.StickyWagesPrices.Ex6_2.OptRule
#print axioms Gali.StickyWagesPrices.Ex6_2.optimal_unique
#print axioms Gali.StickyWagesPrices.Ex6_2.optimal_exists
#print axioms Gali.StickyWagesPrices.Ex6_3.profit
#print axioms Gali.StickyWagesPrices.Ex6_3.hasDerivAt_profit
#print axioms Gali.StickyWagesPrices.Ex6_3.profit_le
#print axioms Gali.StickyWagesPrices.Ex6_3.labor_demand_iff
#print axioms Gali.StickyWagesPrices.Ex6_3.labor_demand_log
#print axioms Gali.StickyWagesPrices.Ex6_3.production_log
#print axioms Gali.StickyWagesPrices.Ex6_3.goods_log
#print axioms Gali.StickyWagesPrices.Ex6_3.Static
#print axioms Gali.StickyWagesPrices.Ex6_3.static_iff
#print axioms Gali.StickyWagesPrices.Ex6_3.flexible_iff
#print axioms Gali.StickyWagesPrices.Ex6_3.advance_iff
#print axioms Gali.StickyWagesPrices.Ex6_3.advance_solution
#print axioms Gali.StickyWagesPrices.Ex6_3.advance_no_persistence
#print axioms Gali.StickyWagesPrices.Ex6_3.wAdv
#print axioms Gali.StickyWagesPrices.Ex6_3.advance_exists
#print axioms Gali.StickyWagesPrices.Ex6_3.union_iff
#print axioms Gali.StickyWagesPrices.Ex6_3.union_solution
#print axioms Gali.StickyWagesPrices.Ex6_3.union_hysteresis
#print axioms Gali.StickyWagesPrices.Ex6_3.nUnion
#print axioms Gali.StickyWagesPrices.Ex6_3.nUnion_adapted
#print axioms Gali.StickyWagesPrices.Ex6_3.union_exists
#print axioms Gali.StickyWagesPrices.Ex6_4.hasDerivAt_planner
#print axioms Gali.StickyWagesPrices.Ex6_4.efficient_hours_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.efficient_output_log
#print axioms Gali.StickyWagesPrices.Ex6_4.hasDerivAt_utility_C
#print axioms Gali.StickyWagesPrices.Ex6_4.hasDerivAt_utility_N
#print axioms Gali.StickyWagesPrices.Ex6_4.competitive_supply_log
#print axioms Gali.StickyWagesPrices.Ex6_4.Schedule
#print axioms Gali.StickyWagesPrices.Ex6_4.Tech
#print axioms Gali.StickyWagesPrices.Ex6_4.real_wage_schedule
#print axioms Gali.StickyWagesPrices.Ex6_4.real_rigidity
#print axioms Gali.StickyWagesPrices.Ex6_4.hasDerivAt_cost
#print axioms Gali.StickyWagesPrices.Ex6_4.markup
#print axioms Gali.StickyWagesPrices.Ex6_4.yn
#print axioms Gali.StickyWagesPrices.Ex6_4.ye
#print axioms Gali.StickyWagesPrices.Ex6_4.markup_eq
#print axioms Gali.StickyWagesPrices.Ex6_4.natural_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.markup_gap
#print axioms Gali.StickyWagesPrices.Ex6_4.NKPCmu
#print axioms Gali.StickyWagesPrices.Ex6_4.NKPCgap
#print axioms Gali.StickyWagesPrices.Ex6_4.nkpc_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.cost_push
#print axioms Gali.StickyWagesPrices.Ex6_4.divine_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.divine_iff_mu0
#print axioms Gali.StickyWagesPrices.Ex6_4.tradeoff_iff_delta
#print axioms Gali.StickyWagesPrices.Ex6_4.strict_inflation_gap
#print axioms Gali.StickyWagesPrices.Ex6_4.periodObj
#print axioms Gali.StickyWagesPrices.Ex6_4.periodObj_sub
#print axioms Gali.StickyWagesPrices.Ex6_4.periodObj_isMinOn_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.period_problem_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.NKPCx
#print axioms Gali.StickyWagesPrices.Ex6_4.DiscretionEq
#print axioms Gali.StickyWagesPrices.Ex6_4.discretionEq_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.cost_push_mu0
#print axioms Gali.StickyWagesPrices.Ex6_4.discretion_iid_iff
#print axioms Gali.StickyWagesPrices.Ex6_4.discretion_output
#print axioms Gali.StickyWagesPrices.Ex6_4.perfect_competition
