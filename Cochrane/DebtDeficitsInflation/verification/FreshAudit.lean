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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.CondVar
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.MeasureTheory.Function.L2Space
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

namespace Cochrane.DebtDeficitsInflation

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

end Cochrane.DebtDeficitsInflation

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

namespace Cochrane.DebtDeficitsInflation

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

end Cochrane.DebtDeficitsInflation

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

namespace Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree

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

end Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree

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

namespace Cochrane.DebtDeficitsInflation.ForwardSolution

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

end Cochrane.DebtDeficitsInflation.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Innovations and moving-average representations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2, eq. (4.1), p. 87,
and §4.2.7, pp. 97–98.

Chapter 4 is written in terms of the innovation operator `Δ_{t+1} = E_{t+1} − E_t` (the book's
`ΔE_{t+1}`) and moving-average representations `s_t = ∑_{j ≥ 0} a_j ε_{t−j} = a(L) ε_t` with a
martingale-difference shock `ε`. This module builds that language on top of the core
`ExpectationSystem`, so every later result holds under perfect foresight and under genuine
uncertainty.

* Shocks are indexed by `ℤ`, so that the moving average (4.1) has a genuine infinite past;
  processes are indexed by `ℕ` and information by `ℕ` (date-`0` information contains the
  pre-sample shocks).
* `innov 𝔼 t` is the linear map `Δ_{t+1}`; `innov_of_known`, `innov_mean_zero`, `innov_known`.
* `IsMDS`: a martingale-difference shock (`E_t ε_k = ε_k` for `k ≤ t`, `E_t ε_{t+1} = 0`);
  `E_shock` (`E_t ε_k` is `ε_k` or `0`), `innov_shock` (`Δ_{t+1} ε_k` is `ε_{t+1}` or `0`).
  `IsMDSNat`, `extendShock`: an `ℕ`-indexed MDS extended by zero to the past;
  `IsMDSNat.E_future`, `IsMDSNat.E_past` (used by the VAR/invertibility modules).
* `E_tsum_abs`: `E_t` commutes with `∑ c_j x_j` for absolutely summable weights `c` and
  uniformly bounded `x_j` (the generalisation of the core `E_tsum` from geometric weights).
* `IsMA`, `IsMAVec` (scalar and vector shocks, absolutely summable coefficients), `gen` (the
  generating function `a(z) = ∑ a_j zʲ`), `genVec`, `dotShock` (`c'ε_k`).
* `innov_MAVec`, `innov_MA` (`Δ_{t+1} s_{t+1+j} = a_j'ε_{t+1}`), `innov_PV_vec`, `innov_PV`
  (`Δ_{t+1} ∑ ρʲ s_{t+1+j} = a(ρ)'ε_{t+1}`), and the termwise version
  `innov_PV_termwise_vec` valid for every `|ρ| ≤ 1` (in particular `ρ = 1`).
* `ar1_of_MA`, `MA_of_ar1`, `isAR1_of_MA`: the AR(1) (4.3) and its moving average.
* `coinShockZ`: a genuinely random martingale-difference shock (two coin flips), used for the
  counterexamples of the later modules.
-/

namespace Cochrane.DebtDeficitsInflation.Innovations

open Filter Topology
open Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The innovation operator -/

/-- Cochrane (2023), §4.2, eq. (4.2), p. 87: the innovation operator `Δ_{t+1} := E_{t+1} − E_t`
(written `ΔE_{t+1}` in the book), a linear map on random variables. -/
def innov (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t x = 𝔼.E (t + 1) x - 𝔼.E t x := rfl

/-- Cochrane (2023), p. 65 ("since `v_t` is known at time `t`, it disappears from this
innovation accounting"): a variable known at `t` has no innovation at `t + 1`. -/
theorem innov_of_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  rw [innov_apply, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx, hx, sub_self]

/-- Cochrane (2023), eq. (4.2), p. 87: innovations are unpredictable, `E_t Δ_{t+1} x = 0`. -/
theorem innov_mean_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  rw [innov_apply, map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), eq. (4.2), p. 87: the innovation `Δ_{t+1} x` is known at `t + 1`. -/
theorem innov_known (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  rw [innov_apply, map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), eq. (3.20), p. 65 ("taking time `t+1` innovations" of an expectation):
`Δ_{t+1} (E_m x) = Δ_{t+1} x` for every `m ≥ t + 1`. -/
theorem innov_E_of_le {t m : ℕ} (hm : t + 1 ≤ m) (x : Ω → ℝ) :
    innov 𝔼 t (𝔼.E m x) = innov 𝔼 t x := by
  rw [innov_apply, innov_apply, 𝔼.tower hm, 𝔼.tower (le_trans (Nat.le_succ t) hm)]

/-- Cochrane (2023), eq. (4.2), p. 87: for `x` known at `t + 1`, `Δ_{t+1} x = x − E_t x`. -/
theorem innov_of_known_succ {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    innov 𝔼 t x = x - 𝔼.E t x := by
  rw [innov_apply, hx]

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1}` of a constant is zero. -/
theorem innov_const (t : ℕ) (c : ℝ) : innov 𝔼 t (fun _ => c) = 0 :=
  innov_of_known 𝔼 (𝔼.const t c)

/-! ### Martingale-difference shocks -/

/-- Cochrane (2023), eq. (4.1), p. 87: a martingale-difference shock `ε_k`, `k ∈ ℤ`: known at
every date `t ≥ k`, and unpredictable one period ahead, `E_t ε_{t+1} = 0`. -/
def IsMDS (ε : ℤ → Ω → ℝ) : Prop :=
  (∀ (t : ℕ) (k : ℤ), k ≤ t → 𝔼.E t (ε k) = ε k) ∧ ∀ t : ℕ, 𝔼.E t (ε ((t : ℤ) + 1)) = 0

/-- Cochrane (2023), eq. (4.1), p. 87: a vector martingale-difference shock (each component is
a martingale difference). -/
def IsMDSVec {n : ℕ} (ε : ℤ → Fin n → Ω → ℝ) : Prop := ∀ i, IsMDS 𝔼 (fun k => ε k i)

/-- Cochrane (2023), eq. (4.1), p. 87: a martingale difference is unpredictable at every
horizon, `E_t ε_k = 0` for `k > t`. -/
theorem E_shock_eq_zero {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) {t : ℕ} {k : ℤ} (hk : (t : ℤ) < k) :
    𝔼.E t (ε k) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = ((t + n : ℕ) : ℤ) + 1 := ⟨(k - t - 1).toNat, by omega⟩
  rw [← 𝔼.tower (Nat.le_add_right t n), hn, h.2 (t + n), map_zero]

/-- Cochrane (2023), eq. (4.1), p. 87: `E_t ε_k = ε_k` if `k ≤ t` and `0` otherwise. -/
theorem E_shock {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) (t : ℕ) (k : ℤ) :
    𝔼.E t (ε k) = if k ≤ t then ε k else 0 := by
  split_ifs with hk
  · exact h.1 t k hk
  · exact E_shock_eq_zero 𝔼 h (by omega)

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1} ε_k = ε_{t+1}` if `k = t + 1` and `0`
otherwise. -/
theorem innov_shock {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) (t : ℕ) (k : ℤ) :
    innov 𝔼 t (ε k) = if k = (t : ℤ) + 1 then ε k else 0 := by
  rw [innov_apply, E_shock 𝔼 h, E_shock 𝔼 h]
  rcases lt_trichotomy k ((t : ℤ) + 1) with hk | hk | hk
  · have h1 : k ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : k ≤ (t : ℤ) := by omega
    have h3 : k ≠ (t : ℤ) + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte, sub_self]
  · subst hk
    have h1 : (t : ℤ) + 1 ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : ¬ ((t : ℤ) + 1 ≤ (t : ℤ)) := by omega
    simp only [h1, h2, ↓reduceIte, sub_zero]
  · have h1 : ¬ k ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : ¬ k ≤ (t : ℤ) := by omega
    have h3 : k ≠ (t : ℤ) + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte, sub_self]

/-- Cochrane (2023), §4.2.7, p. 98: componentwise version of `innov_shock` for a vector
martingale-difference shock. -/
theorem innov_shock_vec {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (h : IsMDSVec 𝔼 ε) (i : Fin n) (t : ℕ)
    (k : ℤ) : innov 𝔼 t (ε k i) = if k = (t : ℤ) + 1 then ε k i else 0 :=
  innov_shock 𝔼 (ε := fun k => ε k i) (h i) t k

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference (adapted, with
`E_t e_{t+1} = 0`). -/
def IsMDSNat (e : ℕ → Ω → ℝ) : Prop := 𝔼.Adapted e ∧ ∀ t, 𝔼.E t (e (t + 1)) = 0

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference has zero forecast at
every horizon, `E_t e_{t+1+k} = 0`. -/
theorem IsMDSNat.E_future {𝔼 : ExpectationSystem Ω} {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e)
    (t k : ℕ) : 𝔼.E t (e (t + 1 + k)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), show t + 1 + k = t + k + 1 by omega, h.2 (t + k),
    map_zero]

/-- Cochrane (2023), eq. (4.1), p. 87: a past `ℕ`-indexed shock is known,
`E_t e_s = e_s` for `s ≤ t`. -/
theorem IsMDSNat.E_past {𝔼 : ExpectationSystem Ω} {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e)
    {s t : ℕ} (hst : s ≤ t) : 𝔼.E t (e s) = e s := by
  rw [← h.1 s, 𝔼.known hst]

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed shock extended by zero to dates `k ≤ 0`
(no shocks before the sample). -/
def extendShock (e : ℕ → Ω → ℝ) (k : ℤ) : Ω → ℝ := if 0 < k then e k.toNat else 0

/-- Cochrane (2023), eq. (4.1), p. 87: the zero-extension of an `ℕ`-indexed martingale
difference is a martingale difference. -/
theorem isMDS_extendShock {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e) : IsMDS 𝔼 (extendShock e) := by
  refine ⟨fun t k hk => ?_, fun t => ?_⟩
  · unfold extendShock
    split_ifs with hk0
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (h.1 k.toNat)
    · exact map_zero _
  · unfold extendShock
    have h0 : (0 : ℤ) < (t : ℤ) + 1 := by omega
    rw [show ((t : ℤ) + 1).toNat = t + 1 by omega]
    simp only [h0, ↓reduceIte]
    exact h.2 t

/-- Cochrane (2023), eq. (4.1), p. 87: the zero-extension is bounded by any bound of the
original shock. -/
theorem extendShock_bounded {e : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M) (he : ∀ t ω, |e t ω| ≤ M)
    (k : ℤ) (ω : Ω) : |extendShock e k ω| ≤ M := by
  unfold extendShock
  split_ifs
  · exact he _ ω
  · simpa using hM

/-! ### Expectations of absolutely summable series -/

/-- Cochrane (2023), eq. (4.2), p. 87 (survey "new infrastructure" item 1): `E_t` commutes
with `∑ c_j x_j` for absolutely summable weights `c` and uniformly bounded `x_j`, generalising
the geometric-weight `E_tsum` of the core. -/
theorem E_tsum_abs {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' j, c j * x j ω') ω = ∑' j, c j * 𝔼.E t (x j) ω := by
  have h := ForwardSolution.E_tsum_dom 𝔼 (hc.mul_right M) (f := fun j => c j • x j)
    (fun j ω' => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j ω') (abs_nonneg _)) t ω
  simpa only [Pi.smul_apply, smul_eq_mul, map_smul] using h

/-- Cochrane (2023), eq. (4.2), p. 87: with absolutely summable weights the series of
conditional expectations is summable. -/
theorem summable_E_terms {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable fun j => c j * 𝔼.E t (x j) ω :=
  Summable.of_norm_bounded (hc.mul_right M) fun j => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx j) t ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1}` commutes with `∑ c_j x_j` for absolutely
summable weights and bounded `x_j`. -/
theorem innov_tsum_abs {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' j, c j * x j ω') ω = ∑' j, c j * innov 𝔼 t (x j) ω := by
  rw [innov_apply, Pi.sub_apply, E_tsum_abs 𝔼 hc hx, E_tsum_abs 𝔼 hc hx,
    ← (summable_E_terms 𝔼 hc hx _ ω).tsum_sub (summable_E_terms 𝔼 hc hx _ ω)]
  refine tsum_congr fun j => ?_
  rw [innov_apply, Pi.sub_apply, mul_sub]

/-! ### Moving-average representations -/

/-- Cochrane (2023), eq. (4.2), p. 87: the generating function `a(z) = ∑_{j ≥ 0} a_j zʲ` of a
coefficient sequence (the book's `a(ρ)`, `a(β)`). -/
noncomputable def gen (a : ℕ → ℝ) (z : ℝ) : ℝ := ∑' j, a j * z ^ j

/-- Cochrane (2023), eq. (4.1), p. 87: `s` has the moving-average representation
`s_t = ∑_{j ≥ 0} a_j ε_{t−j}` with absolutely summable coefficients. -/
def IsMA (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  Summable (fun j => |a j|) ∧ ∀ t ω, s t ω = ∑' j, a j * ε ((t : ℤ) - j) ω

/-- Cochrane (2023), §4.2.7, p. 97: a vector moving average `s_t = a(L)'ε_t =
∑_{j ≥ 0} ∑_i a_{j,i} ε_{t−j,i}` with absolutely summable coefficients. -/
def IsMAVec {n : ℕ} (a : ℕ → Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Summable (fun j => |a j i|)) ∧ ∀ t ω, s t ω = ∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω

/-- Cochrane (2023), §4.2.7, p. 98: the vector `a(z) = ∑_j a_j zʲ` of generating functions. -/
noncomputable def genVec {n : ℕ} (a : ℕ → Fin n → ℝ) (z : ℝ) (i : Fin n) : ℝ :=
  gen (fun j => a j i) z

/-- Cochrane (2023), §4.2.7, p. 98: the scalar product `c'ε_k` of a coefficient vector and a
shock. -/
def dotShock {n : ℕ} (c : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) : Ω → ℝ :=
  fun ω => ∑ i, c i * ε k i ω

/-- Cochrane (2023), §4.2.7, p. 98: `a(0) = a_0`. -/
theorem gen_zero (a : ℕ → ℝ) : gen a 0 = a 0 := by
  unfold gen
  rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
  simp

/-- Cochrane (2023), eq. (4.2), p. 87: absolutely summable coefficients give a summable
`∑ a_j zʲ` for `|z| ≤ 1`. -/
theorem summable_coeff_mul_pow {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {z : ℝ}
    (hz : |z| ≤ 1) : Summable fun j => a j * z ^ j :=
  Summable.of_norm_bounded ha fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)

/-- Cochrane (2023), eq. (4.1), p. 87: a scalar moving average is the one-shock case of the
vector moving average. -/
theorem isMA_iff_vec (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (s : ℕ → Ω → ℝ) :
    IsMA a ε s ↔ IsMAVec (n := 1) (fun j _ => a j) (fun k _ => ε k) s := by
  simp [IsMA, IsMAVec]

/-- Cochrane (2023), eq. (4.1), p. 87: a scalar martingale difference is a one-component
vector martingale difference. -/
theorem isMDSVec_of_isMDS {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) :
    IsMDSVec 𝔼 (n := 1) (fun k _ => ε k) := fun _ => h

/-- Cochrane (2023), eq. (4.1), p. 87: the date-`k` terms of a vector moving average are
dominated by `∑_i |a_{j,i}| M`. -/
theorem abs_ma_term_le {n : ℕ} (a : ℕ → Fin n → ℝ) {ε : ℤ → Fin n → Ω → ℝ} {M : ℝ}
    (hε : ∀ k i ω, |ε k i ω| ≤ M) (j : ℕ) (k : ℤ) (ω : Ω) :
    |∑ i, a j i * ε k i ω| ≤ ∑ i, |a j i| * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hε k i ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.1), p. 87: the dominating sequence `∑_i |a_{j,i}| M` is summable. -/
theorem summable_ma_bound {n : ℕ} {a : ℕ → Fin n → ℝ} (ha : ∀ i, Summable fun j => |a j i|)
    (M : ℝ) : Summable fun j => ∑ i, |a j i| * M :=
  summable_sum fun i _ => (ha i).mul_right M

/-- Cochrane (2023), eq. (4.1), p. 87: conditional expectations of a vector moving average,
`E_m s_t = ∑_j ∑_i a_{j,i} E_m ε_{t−j,i}` (`E_m` commutes with the infinite sum). -/
theorem E_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M) (m t : ℕ) (ω : Ω) :
    𝔼.E m (s t) ω = ∑' j, ∑ i, a j i * 𝔼.E m (ε ((t : ℤ) - j) i) ω := by
  have hst : s t = fun ω' => ∑' j, (∑ i, a j i • ε ((t : ℤ) - j) i) ω' := by
    funext ω'
    rw [hs.2 t ω']
    simp [Finset.sum_apply]
  rw [hst, ForwardSolution.E_tsum_dom 𝔼 (summable_ma_bound hs.1 M)
    (fun j ω' => by simpa [Finset.sum_apply] using abs_ma_term_le a hε j _ ω') m ω]
  simp [map_sum, Finset.sum_apply]

/-- Cochrane (2023), eq. (4.1), p. 87: the series of conditional expectations of the terms of a
vector moving average is summable. -/
theorem summable_E_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    (ha : ∀ i, Summable fun j => |a j i|) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M)
    (m t : ℕ) (ω : Ω) :
    Summable fun j => ∑ i, a j i * 𝔼.E m (ε ((t : ℤ) - j) i) ω :=
  Summable.of_norm_bounded (summable_ma_bound ha M) fun j => by
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hε _ i) m ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.1), p. 87: a moving average in a bounded shock is bounded, by
`∑_i (∑_j |a_{j,i}|) M`. -/
theorem abs_MAVec_le {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M) (t : ℕ) (ω : Ω) :
    |s t ω| ≤ ∑ i, (∑' j, |a j i|) * M := by
  have hsum : Summable fun j => ∑ i, a j i * ε ((t : ℤ) - j) i ω :=
    Summable.of_norm_bounded (summable_ma_bound hs.1 M) fun j => by
      rw [Real.norm_eq_abs]; exact abs_ma_term_le a hε j _ ω
  have hbound : ∑' j, ∑ i, |a j i| * M = ∑ i, (∑' j, |a j i|) * M := by
    rw [Summable.tsum_finsetSum fun i _ => (hs.1 i).mul_right M]
    exact Finset.sum_congr rfl fun i _ => tsum_mul_right
  rw [hs.2 t ω, ← hbound]
  calc |∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω|
      = ‖∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖∑ i, a j i * ε ((t : ℤ) - j) i ω‖ := norm_tsum_le_tsum_norm
      (hsum.abs.congr fun j => (Real.norm_eq_abs _).symm)
    _ = ∑' j, |∑ i, a j i * ε ((t : ℤ) - j) i ω| := by simp_rw [Real.norm_eq_abs]
    _ ≤ ∑' j, ∑ i, |a j i| * M :=
        Summable.tsum_le_tsum (fun j => abs_ma_term_le a hε j _ ω) hsum.abs
          (summable_ma_bound hs.1 M)

/-- Cochrane (2023), eq. (4.1), p. 87: a moving average in a martingale-difference shock is
adapted, `E_t s_t = s_t`. -/
theorem adapted_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) :
    𝔼.Adapted s := by
  intro t
  funext ω
  rw [E_MAVec 𝔼 hs hM t t ω, hs.2 t ω]
  refine tsum_congr fun j => Finset.sum_congr rfl fun i _ => ?_
  rw [(hε i).1 t _ (by omega)]

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent): the innovation in a future
value of a vector moving average is the corresponding coefficient,
`Δ_{t+1} s_{t+1+j} = a_j'ε_{t+1}`. -/
theorem innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    (t j : ℕ) : innov 𝔼 t (s (t + 1 + j)) = dotShock (a j) ε ((t : ℤ) + 1) := by
  funext ω
  rw [innov_apply, Pi.sub_apply, E_MAVec 𝔼 hs hM, E_MAVec 𝔼 hs hM,
    ← (summable_E_MAVec 𝔼 hs.1 hM _ _ ω).tsum_sub (summable_E_MAVec 𝔼 hs.1 hM _ _ ω)]
  have hterm : ∀ k, ∑ i, a k i * 𝔼.E (t + 1) (ε (((t + 1 + j : ℕ) : ℤ) - k) i) ω -
      ∑ i, a k i * 𝔼.E t (ε (((t + 1 + j : ℕ) : ℤ) - k) i) ω =
      if k = j then dotShock (a j) ε ((t : ℤ) + 1) ω else 0 := by
    intro k
    rw [← Finset.sum_sub_distrib]
    by_cases hk : k = j
    · subst hk
      have hm : ((t + 1 + k : ℕ) : ℤ) - (k : ℤ) = (t : ℤ) + 1 := by push_cast; ring
      simp only [hm, ↓reduceIte, dotShock]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub]
      congr 1
      have := congrFun (innov_shock_vec 𝔼 hε i t ((t : ℤ) + 1)) ω
      simpa only [innov_apply, ↓reduceIte, Pi.sub_apply] using this
    · have hm : ((t + 1 + j : ℕ) : ℤ) - (k : ℤ) ≠ (t : ℤ) + 1 := by push_cast; omega
      simp only [hk, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← mul_sub]
      have := congrFun (innov_shock_vec 𝔼 hε i t (((t + 1 + j : ℕ) : ℤ) - k)) ω
      simp only [hm, ↓reduceIte, innov_apply, Pi.sub_apply, Pi.zero_apply] at this
      rw [this, mul_zero]
  simp_rw [hterm]
  exact tsum_ite_eq j _

/-- Cochrane (2023), eq. (4.2), p. 87: scalar version of `innov_MAVec`,
`Δ_{t+1} s_{t+1+j} = a_j ε_{t+1}`. -/
theorem innov_MA {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = a j • ε ((t : ℤ) + 1) := by
  rw [innov_MAVec 𝔼 ((isMA_iff_vec a ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε)
    (fun k _ ω => hM k ω) t j]
  funext ω
  simp [dotShock]

/-- Cochrane (2023), eq. (4.4), p. 88: with the normalisation `a_0 = 1`, the shock is the
surplus innovation, `Δ_{t+1} s_{t+1} = ε_{t+1}`. -/
theorem innov_MA_zero {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (s (t + 1)) = ε ((t : ℤ) + 1) := by
  simpa [ha0] using innov_MA 𝔼 hs hε hM t 0

/-- Cochrane (2023), eq. (4.2), p. 87: the generating-function sum `∑_i a_i(ρ) c_i` written
as an infinite sum of the coefficients. -/
theorem hasSum_dot_gen {n : ℕ} {a : ℕ → Fin n → ℝ} {z : ℝ}
    (ha : ∀ i, Summable fun j => a j i * z ^ j) (e : Fin n → ℝ) :
    HasSum (fun j => z ^ j * ∑ i, a j i * e i) (∑ i, genVec a z i * e i) := by
  have h := hasSum_sum (s := Finset.univ) fun i _ => ((ha i).hasSum.mul_right (e i))
  convert h using 1
  · funext j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rfl

/-- Cochrane (2023), eq. (4.2), p. 87, termwise form valid for every `ρ` with
`∑ |a_j ρʲ| < ∞` (in particular `|ρ| ≤ 1`, including `ρ = 1`):
`∑_j ρʲ Δ_{t+1} s_{t+1+j} = a(ρ)'ε_{t+1}`. -/
theorem innov_PV_termwise_vec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : ∀ i, Summable fun j => a j i * ρ ^ j)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (dotShock (genVec a ρ) ε ((t : ℤ) + 1) ω) := by
  simp_rw [innov_MAVec 𝔼 hs hε hM]
  exact hasSum_dot_gen hρ _

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): for `|ρ| < 1`, the
innovation in the discounted sum of a vector moving average is `a(ρ)'ε_{t+1}`:
`Δ_{t+1} ∑_j ρʲ s_{t+1+j} = a(ρ)'ε_{t+1}`. -/
theorem innov_PV_vec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) = dotShock (genVec a ρ) ε ((t : ℤ) + 1) := by
  funext ω
  have hgeo : Summable fun j => |ρ ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  rw [innov_tsum_abs 𝔼 hgeo (fun j ω' => abs_MAVec_le hs hM (t + 1 + j) ω') t ω]
  exact (innov_PV_termwise_vec 𝔼 hs hε hM
    (fun i => summable_coeff_mul_pow (hs.1 i) hρ.le) t ω).tsum_eq

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): for `|ρ| < 1`,
`Δ_{t+1} ∑_j ρʲ s_{t+1+j} = ∑_j a_j ρʲ ε_{t+1} = a(ρ) ε_{t+1}`. -/
theorem innov_PV {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) = gen a ρ • ε ((t : ℤ) + 1) := by
  rw [innov_PV_vec 𝔼 ((isMA_iff_vec a ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε)
    (fun k _ ω => hM k ω) hρ t]
  funext ω
  simp [dotShock, genVec]

/-- Cochrane (2023), eq. (4.2), p. 87, termwise scalar form valid for `|ρ| ≤ 1`:
`∑_j ρʲ Δ_{t+1} s_{t+1+j} = a(ρ) ε_{t+1}`. -/
theorem innov_PV_termwise {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ)
    (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) (gen a ρ * ε ((t : ℤ) + 1) ω) := by
  simp_rw [innov_MA 𝔼 hs hε hM, Pi.smul_apply, smul_eq_mul]
  have h := (summable_coeff_mul_pow hs.1 hρ).hasSum.mul_right (ε ((t : ℤ) + 1) ω)
  convert h using 1
  · funext j
    ring
  · rfl

/-- Cochrane (2023), eq. (4.2), p. 87: the innovations of a moving average vanish at long
horizons fast enough for transversality: `ρᵀ Δ_{t+1} s_{t+1+T} → 0` for `|ρ| ≤ 1`. -/
theorem tendsto_pow_mul_innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 t (s (t + 1 + T)) ω) atTop (𝓝 0) := by
  simp_rw [innov_MAVec 𝔼 hs hε hM]
  have hterm : ∀ i, Tendsto (fun T => ρ ^ T * (a T i * ε ((t : ℤ) + 1) i ω)) atTop (𝓝 0) := by
    intro i
    have h0 : Tendsto (fun T => a T i) atTop (𝓝 0) := by
      have := (hs.1 i).tendsto_atTop_zero
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 this
    have hb : Tendsto (fun T => a T i * ε ((t : ℤ) + 1) i ω) atTop (𝓝 0) := by
      simpa using h0.mul_const (ε ((t : ℤ) + 1) i ω)
    refine squeeze_zero_norm (fun T => ?_) ((tendsto_zero_iff_norm_tendsto_zero).1 hb)
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => hterm i
  simp only [Finset.sum_const_zero] at h
  convert h using 1
  funext T
  simp [dotShock, Finset.mul_sum]

/-! ### The AR(1) and the i.i.d. process as moving averages -/

/-- Cochrane (2023), eq. (4.3), p. 87: a process with moving-average coefficients `a_j = ηʲ`
follows the AR(1) law `s_{t+1} = η s_t + ε_{t+1}`. -/
theorem ar1_of_MA {η : ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA (fun j => η ^ j) ε s)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    s (t + 1) = η • s t + ε ((t : ℤ) + 1) := by
  funext ω
  have hsum : Summable fun j : ℕ => η ^ j * ε (((t + 1 : ℕ) : ℤ) - j) ω :=
    Summable.of_norm_bounded (hs.1.mul_right M) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)
  rw [hs.2 (t + 1) ω, hsum.tsum_eq_zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hs.2 t ω, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  rw [add_comm]
  congr 1
  · refine tsum_congr fun j => ?_
    rw [pow_succ]
    push_cast
    rw [show (t : ℤ) + 1 - (j + 1) = t - j by ring]
    ring

/-- Cochrane (2023), eq. (4.3), p. 87: conversely, for `|η| < 1` and a bounded shock, the
AR(1) started from its infinite past `s_0 = ∑ ηʲ ε_{−j}` has moving-average coefficients `ηʲ`. -/
theorem MA_of_ar1 {η : ℝ} (hη : |η| < 1) {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    {s : ℕ → Ω → ℝ} (h0 : ∀ ω, s 0 ω = ∑' j : ℕ, η ^ j * ε (-(j : ℤ)) ω)
    (hrec : ∀ t, s (t + 1) = η • s t + ε ((t : ℤ) + 1)) : IsMA (fun j => η ^ j) ε s := by
  have habs : Summable fun j => |η ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg η) hη
  refine ⟨habs, fun t => ?_⟩
  induction t with
  | zero => intro ω; simpa using h0 ω
  | succ t ih =>
    intro ω
    have hsum : Summable fun j : ℕ => η ^ j * ε (((t + 1 : ℕ) : ℤ) - j) ω :=
      Summable.of_norm_bounded (habs.mul_right M) fun j => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)
    rw [hrec t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih ω, hsum.tsum_eq_zero_add,
      ← tsum_mul_left]
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
    rw [add_comm]
    congr 1
    · refine tsum_congr fun j => ?_
      rw [pow_succ]
      push_cast
      rw [show (t : ℤ) + 1 - (j + 1) = t - j by ring]
      ring

/-- Cochrane (2023), eq. (4.3), p. 87: a moving average with coefficients `ηʲ` in a
martingale-difference shock is an AR(1) in the sense of the core (`E_t s_{t+1} = η s_t`). -/
theorem isAR1_of_MA {η : ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA (fun j => η ^ j) ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) : 𝔼.IsAR1 η s := by
  have had : 𝔼.Adapted s :=
    adapted_MAVec 𝔼 ((isMA_iff_vec _ ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε) fun k _ ω => hM k ω
  refine ⟨had, fun t => ?_⟩
  rw [ar1_of_MA hs hM t, map_add, map_smul, had t, hε.2 t, add_zero]

/-- Cochrane (2023), p. 88 ("θ = 0 gives an i.i.d. surplus process"): the coefficients
`a_0 = 1`, `a_j = 0` (`j ≥ 1`) of an i.i.d. (white-noise) process. -/
def iidCoeff (j : ℕ) : ℝ := if j = 0 then 1 else 0

/-- Cochrane (2023), p. 88: the shock itself, `s_t = ε_t`, is a moving average with the
i.i.d. coefficients. -/
theorem isMA_iid (ε : ℤ → Ω → ℝ) : IsMA iidCoeff ε (fun t => ε t) := by
  refine ⟨?_, fun t ω => ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    simp only [Finset.mem_singleton] at hj
    simp [iidCoeff, hj]
  · rw [tsum_eq_single 0 fun j hj => by simp [iidCoeff, hj]]
    simp [iidCoeff]

/-- Cochrane (2023), p. 88: the i.i.d. process has `a(z) = 1` for every `z`. -/
theorem gen_iid (z : ℝ) : gen iidCoeff z = 1 := by
  unfold gen
  rw [tsum_eq_single 0 fun j hj => by simp [iidCoeff, hj]]
  simp [iidCoeff]

/-! ### A genuinely random shock -/

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock of the core finite tree (`±1` at
dates 1 and 2, zero otherwise), indexed by `ℤ` with no pre-sample shocks. -/
noncomputable def coinShockZ : ℤ → Bool × Bool → ℝ := extendShock coinShock

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is a martingale difference for the
coin-flip expectation system. -/
theorem coinShockZ_isMDS : IsMDS coinSystem coinShockZ := by
  refine isMDS_extendShock coinSystem ⟨fun t => ?_, coinShock_mean_zero⟩
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is bounded by one. -/
theorem coinShockZ_bounded (k : ℤ) (ω : Bool × Bool) : |coinShockZ k ω| ≤ 1 := by
  refine extendShock_bounded zero_le_one (fun t ω' => ?_) k ω
  unfold coinShock
  split_ifs <;> simp

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is genuinely random: `ε_1 = 1` after
heads. -/
theorem coinShockZ_one : coinShockZ 1 (true, true) = 1 := by
  simp [coinShockZ, extendShock, coinShock]

end Cochrane.DebtDeficitsInflation.Innovations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linearised government-debt identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, eqs. (3.17)–(3.25),
pp. 63–68, as used in Chapter 4 (pp. 86–98), proved here for this project.

The primitives are the linearised flow identity (3.17)
`ρ v_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` (with `r = rⁿ − π`) and the linearised
geometric-maturity bond-return identity of Online Appendix §1.3, `rⁿ_{t+1} = ω q_{t+1} − q_t`
(`q` the log bond price). Both are stated as exact equalities between random variables at every
date (they hold ex post). The derivation of these two first-order approximations from the
nonlinear model, as exact derivatives, is in `LinearizationDerivation`; here every claim the book
derives FROM them is proved exactly, for an arbitrary `ExpectationSystem`.

Infinite sums whose convergence the book merely assumes ("assuming that the sums converge")
are expressed with `SeriesTo f a` (the partial sums of `∑ f_j` converge to `a`, i.e. ordinary
convergence, which does not require absolute summability); `tsum` corollaries are given under
summability, and an `E_t`-of-`tsum` version for bounded processes.

## Main results

* `Recursion`, `rec_finite`, `rec_map_finite`, `rec_seriesTo_map`: forward iteration of
  `x_t = ρ x_{t+1} + f_{t+1}` and of any linear image of it (`E_m`, `Δ_{t+1}`), with the
  terminal condition as an explicit limit; `tvc_of_bound`, `tvc_E_of_bounded`,
  `tvc_innov_of_bounded`, `tvc_innov_of_MAVec`: sufficient conditions for it.
* `Flow` (3.17), `sOfFlow`, `flow_sOfFlow` (p. 66 / p. 86: inferring `s̃` from the identity makes
  it hold exactly), `pv_finite` (3.18), `pv_expected`, `pv_expected_tsum`,
  `pv_expected_bounded` (3.19).
* `unexpected_inflation_identity` (3.20), `BondReturn`, `bond_return_identity` (3.21),
  `weighted_inflation_identity` (3.22), and under constant expected returns
  (`ConstExpReturn`) and no growth: `weighted_inflation_identity_const` (3.23),
  `inflation_identity_const` (3.24), `bond_return_identity_const` (3.25); one-period debt:
  `inflation_identity_one_period` (p. 67) and `inflation_identity_one_period_const` (p. 66).
-/

namespace Cochrane.DebtDeficitsInflation.LinearizedIdentities

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Ordinary convergence of series -/

/-- Cochrane (2023), eq. (3.19), p. 64 ("assuming that the sums converge"): the series
`∑_{j ≥ 0} f_j` converges (its partial sums tend) to `a`. -/
def SeriesTo (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun T => ∑ j ∈ Finset.range T, f j) atTop (𝓝 a)

/-- Cochrane (2023), eq. (3.19), p. 64: an unconditionally convergent series converges. -/
theorem seriesTo_of_hasSum {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) : SeriesTo f a :=
  h.tendsto_sum_nat

/-- Cochrane (2023), eq. (3.19), p. 64: for a summable series both notions of sum agree. -/
theorem seriesTo_iff_hasSum {f : ℕ → ℝ} {a : ℝ} (hf : Summable f) : SeriesTo f a ↔ HasSum f a :=
  (hf.hasSum_iff_tendsto_nat).symm

/-- Cochrane (2023), eq. (3.19), p. 64: the limit of a convergent series is unique. -/
theorem SeriesTo.unique {f : ℕ → ℝ} {a b : ℝ} (ha : SeriesTo f a) (hb : SeriesTo f b) : a = b :=
  tendsto_nhds_unique ha hb

/-- Cochrane (2023), eq. (3.19), p. 64: termwise equal series have the same limit. -/
theorem SeriesTo.congr {f g : ℕ → ℝ} {a b : ℝ} (h : SeriesTo f a) (hfg : ∀ j, f j = g j)
    (hab : a = b) : SeriesTo g b := by
  subst hab
  unfold SeriesTo at h ⊢
  simp_rw [← hfg]
  exact h

/-- Cochrane (2023), eq. (3.19), p. 64: convergent series add. -/
theorem SeriesTo.add {f g : ℕ → ℝ} {a b : ℝ} (hf : SeriesTo f a) (hg : SeriesTo g b) :
    SeriesTo (fun j => f j + g j) (a + b) := by
  unfold SeriesTo at hf hg ⊢
  simp_rw [Finset.sum_add_distrib]
  exact hf.add hg

/-- Cochrane (2023), eq. (3.19), p. 64: convergent series subtract. -/
theorem SeriesTo.sub {f g : ℕ → ℝ} {a b : ℝ} (hf : SeriesTo f a) (hg : SeriesTo g b) :
    SeriesTo (fun j => f j - g j) (a - b) := by
  unfold SeriesTo at hf hg ⊢
  simp_rw [Finset.sum_sub_distrib]
  exact hf.sub hg

/-- Cochrane (2023), eq. (3.19), p. 64: a convergent series may be scaled. -/
theorem SeriesTo.const_mul {f : ℕ → ℝ} {a : ℝ} (hf : SeriesTo f a) (c : ℝ) :
    SeriesTo (fun j => c * f j) (c * a) := by
  unfold SeriesTo at hf ⊢
  simp_rw [← Finset.mul_sum]
  exact hf.const_mul c

/-- Cochrane (2023), eq. (3.19), p. 64: the zero series converges to zero. -/
theorem seriesTo_zero : SeriesTo (fun _ => 0) 0 := by
  unfold SeriesTo
  simp

/-- Cochrane (2023), eq. (3.20), p. 65 (the sums `∑_{j ≥ 1}`): dropping the first term,
`∑_{j ≥ 0} f_j = a` iff `∑_{j ≥ 0} f_{j+1} = a − f_0`. -/
theorem seriesTo_succ_iff {f : ℕ → ℝ} {a : ℝ} :
    SeriesTo f a ↔ SeriesTo (fun j => f (j + 1)) (a - f 0) := by
  unfold SeriesTo
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [Finset.sum_range_succ']
  constructor
  · intro h
    simpa using h.sub_const (f 0)
  · intro h
    simpa using h.add_const (f 0)

/-! ### Forward iteration of a valuation recursion -/

/-- Cochrane (2023), eq. (3.17), p. 63: the valuation recursion `x_t = ρ x_{t+1} + f_{t+1}`
(the flow identity, the Campbell–Shiller identity and the bond-price identity all have this
form). -/
def Recursion (ρ : ℝ) (x f : ℕ → Ω → ℝ) : Prop := ∀ t, x t = ρ • x (t + 1) + f (t + 1)

/-- Cochrane (2023), eq. (3.18), p. 63: forward iteration,
`x_t = ∑_{j<T} ρʲ f_{t+1+j} + ρᵀ x_{t+T}` (holds ex post). -/
theorem rec_finite {ρ : ℝ} {x f : ℕ → Ω → ℝ} (h : Recursion ρ x f) (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, ρ ^ j • f (t + 1 + j) + ρ ^ T • x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hx := h (t + T)
    rw [show t + T + 1 = t + (T + 1) by omega] at hx
    rw [ih, hx, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ,
      show t + 1 + T = t + (T + 1) by omega]
    abel

/-- Cochrane (2023), eq. (3.18), p. 63 ("holds ex post, so it holds ex ante"): any linear map
(e.g. `E_m` or `Δ_{t+1}`) applied to the forward iteration. -/
theorem rec_map_finite (L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (h : Recursion ρ x f) (t T : ℕ) :
    L (x t) = ∑ j ∈ Finset.range T, ρ ^ j • L (f (t + 1 + j)) + ρ ^ T • L (x (t + T)) := by
  conv_lhs => rw [rec_finite h t T]
  rw [map_add, map_sum, map_smul]
  simp_rw [map_smul]

/-- Cochrane (2023), eq. (3.19), p. 64: if the terminal term `ρᵀ L x_{t+T}` vanishes, the
linear image of the forward iteration converges: `L x_t = ∑_{j ≥ 0} ρʲ L f_{t+1+j}`. -/
theorem rec_seriesTo_map (L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (h : Recursion ρ x f) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * L (x (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * L (f (t + 1 + j)) ω) (L (x t) ω) := by
  have hS : ∀ T, ∑ j ∈ Finset.range T, ρ ^ j * L (f (t + 1 + j)) ω =
      L (x t) ω - ρ ^ T * L (x (t + T)) ω := by
    intro T
    have := congrFun (rec_map_finite L h t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  unfold SeriesTo
  simp_rw [hS]
  simpa using (tendsto_const_nhds (x := L (x t) ω)).sub hT

/-- Cochrane (2023), eq. (3.19), p. 64 ("the debt-to-GDP ratio is expected to grow no faster
than `ρ⁻ᵗ`"): for `|ρ| < 1` a bounded sequence satisfies the terminal condition
`ρᵀ y_T → 0`. -/
theorem tvc_of_bound {ρ : ℝ} (hρ : |ρ| < 1) {y : ℕ → ℝ} {K : ℝ} (hy : ∀ T, |y T| ≤ K) :
    Tendsto (fun T => ρ ^ T * y T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℕ => |ρ| ^ T * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy T) (pow_nonneg (abs_nonneg _) T)

/-- Cochrane (2023), eq. (3.19), p. 64: for `|ρ| < 1` a bounded process satisfies the
terminal condition `ρᵀ E_m x_{t+T} → 0`. -/
theorem tvc_E_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (m t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E m (x (t + T)) ω) atTop (𝓝 0) :=
  tvc_of_bound hρ fun T => 𝔼.abs_E_le (hx (t + T)) m ω

/-- Cochrane (2023), eq. (3.20), p. 65: for `|ρ| < 1` a bounded process satisfies the
innovation terminal condition `ρᵀ Δ_{s+1} x_{t+T} → 0`. -/
theorem tvc_innov_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (s t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 s (x (t + T)) ω) atTop (𝓝 0) :=
  tvc_of_bound hρ (K := M + M) fun T => by
    rw [innov_apply, Pi.sub_apply]
    exact (abs_sub _ _).trans
      (add_le_add (𝔼.abs_E_le (hx _) _ ω) (𝔼.abs_E_le (hx _) _ ω))

/-- Cochrane (2023), A2 §2.3, p. 606 ("imposing convergence of the last term"): a process with
an absolutely summable moving-average representation satisfies the innovation terminal
condition `ρᵀ Δ_{t+1} x_{t+T} → 0` for every `|ρ| ≤ 1` (including `ρ = 1`). -/
theorem tvc_innov_of_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 t (x (t + T)) ω) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h := (tendsto_pow_mul_innov_MAVec 𝔼 hx hε hM hρ t ω).const_mul ρ
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
  ring

/-! ### The flow identity and the present value -/

/-- Cochrane (2023), eq. (3.17), p. 63: the linearised flow identity
`ρ v_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` at every date. -/
def Flow (ρ : ℝ) (v r g s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + r (t + 1) - g (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (3.17), p. 63: the flow identity is the valuation recursion with
payoff `s̃ + g − r`. -/
theorem flow_iff_recursion (ρ : ℝ) (v r g s : ℕ → Ω → ℝ) :
    Flow ρ v r g s ↔ Recursion ρ v (fun t => s t + g t - r t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Cochrane (2023), p. 66 and §4.1, p. 86: the surplus inferred from the linearised flow
identity, `s̃_{t+1} := v_t + r_{t+1} − g_{t+1} − ρ v_{t+1}` (the date-0 value is irrelevant). -/
def sOfFlow (ρ : ℝ) (v r g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => v t + r (t + 1) - g (t + 1) - ρ • v (t + 1)

/-- Cochrane (2023), p. 66 and §4.1, p. 86: "I infer the surplus from the linearized flow
identity (3.17), so that linearized identities hold exactly". -/
theorem flow_sOfFlow (ρ : ℝ) (v r g : ℕ → Ω → ℝ) : Flow ρ v r g (sOfFlow ρ v r g) := by
  intro t
  simp only [sOfFlow]
  abel

/-- Cochrane (2023), p. 66 and §4.1, p. 86: the inferred surplus is the only one consistent
with the flow identity. -/
theorem eq_sOfFlow {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (t : ℕ) :
    s (t + 1) = sOfFlow ρ v r g (t + 1) := by
  simp only [sOfFlow]
  rw [h t]
  abel

/-- Cochrane (2023), eq. (3.18), p. 63: the ex-post present-value identity
`v_t = ∑_{j<T} ρʲ s̃_{t+1+j} + ∑_{j<T} ρʲ g_{t+1+j} − ∑_{j<T} ρʲ r_{t+1+j} + ρᵀ v_{t+T}`. -/
theorem pv_finite {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • s (t + 1 + j) +
      ∑ j ∈ Finset.range T, ρ ^ j • g (t + 1 + j) -
      ∑ j ∈ Finset.range T, ρ ^ j • r (t + 1 + j) + ρ ^ T • v (t + T) := by
  rw [rec_finite ((flow_iff_recursion ρ v r g s).1 h) t T]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Cochrane (2023), eq. (3.19), p. 64, combined form: under the terminal condition
`E_t ρᵀ v_{t+T} → 0`, `v_t = ∑_{j ≥ 0} ρʲ E_t (s̃ + g − r)_{t+1+j}`. -/
theorem pv_expected_combined {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) := by
  have h0 := rec_seriesTo_map (𝔼.E t) ((flow_iff_recursion ρ v r g s).1 h) hT
  rwa [hv t] at h0

/-- Cochrane (2023), eq. (3.19), p. 64: under the terminal condition, if the surplus and growth
present values converge (to `S`, `G`), so does the discount-rate term, to `S + G − v_t`; i.e.
`v_t = E_t ∑ ρʲ s̃_{t+1+j} + E_t ∑ ρʲ g_{t+1+j} − E_t ∑ ρʲ r_{t+1+j}`. -/
theorem pv_expected {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (hv : 𝔼.Adapted v)
    {t : ℕ} {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) (S + G - v t ω) := by
  refine ((hS.add hG).sub (pv_expected_combined 𝔼 h hv hT)).congr (fun j => ?_) rfl
  simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
  ring

/-- Cochrane (2023), eq. (3.19), p. 64, `tsum` form: when the three present values are
summable, `v_t = ∑ ρʲ E_t s̃_{t+1+j} + ∑ ρʲ E_t g_{t+1+j} − ∑ ρʲ E_t r_{t+1+j}`. -/
theorem pv_expected_tsum {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
    (hg : Summable fun j => ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) :
    v t ω = ∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω + ∑' j, ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω -
      ∑' j, ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω := by
  have h1 := pv_expected 𝔼 h hv hT (seriesTo_of_hasSum hs.hasSum) (seriesTo_of_hasSum hg.hasSum)
  have h2 := (seriesTo_of_hasSum hr.hasSum).unique h1
  linarith

/-- Cochrane (2023), eq. (3.19), p. 64, literal form `v_t = E_t ∑_{j ≥ 1} ρ^{j−1}(s̃ + g − r)_{t+j}`
for bounded processes and `|ρ| < 1` (the expectation of the infinite sum; the terminal
condition then holds automatically). -/
theorem pv_expected_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) {M : ℝ} (hvb : ∀ t ω, |v t ω| ≤ M)
    {K : ℝ} (hfb : ∀ t ω, |s t ω + g t ω - r t ω| ≤ K) (t : ℕ) :
    v t = 𝔼.E t (fun ω => ∑' j, ρ ^ j * (s (t + 1 + j) ω + g (t + 1 + j) ω -
      r (t + 1 + j) ω)) := by
  funext ω
  have hgeo : Summable fun j => |ρ ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  rw [E_tsum_abs 𝔼 hgeo (x := fun j ω' => s (t + 1 + j) ω' + g (t + 1 + j) ω' -
    r (t + 1 + j) ω') (fun j ω' => hfb _ ω') t ω]
  have hser := pv_expected_combined 𝔼 h hv (tvc_E_of_bounded 𝔼 hρ hvb t t ω)
  have hsum := summable_E_terms 𝔼 hgeo (x := fun j ω' => s (t + 1 + j) ω' +
    g (t + 1 + j) ω' - r (t + 1 + j) ω') (fun j ω' => hfb _ ω') t ω
  refine (seriesTo_of_hasSum hsum.hasSum).unique (hser.congr (fun j => ?_) rfl) |>.symm
  rfl

/-! ### Innovation identities -/

/-- Cochrane (2023), eq. (3.20), p. 65 (unexpected-inflation identity): with
`r = rⁿ − π`, `v_t` known at `t` and the innovation terminal condition
`ρᵀ Δ_{t+1} v_{t+T} → 0`, if the surplus and growth innovation sums converge to `S` and `G`,
then `∑_{j ≥ 1} ρʲ Δ_{t+1} r_{t+1+j}` converges to `Δ_{t+1}π_{t+1} − Δ_{t+1}rⁿ_{t+1} + S + G`,
i.e. `Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`. -/
theorem unexpected_inflation_identity {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) {t : ℕ} (hv : 𝔼.E t (v t) = v t)
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω + S + G) := by
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((flow_iff_recursion ρ v r g s).1 h) hT
  rw [innov_of_known 𝔼 hv] at h0
  have hR : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (r (t + 1 + j)) ω) (S + G - 0) := by
    refine ((hS.add hG).sub h0).congr (fun j => ?_) rfl
    simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
    ring
  refine (seriesTo_succ_iff.1 hR).congr (fun j => ?_) ?_
  · rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  · simp only [pow_zero, one_mul, add_zero, sub_zero]
    rw [hr (t + 1), map_sub, Pi.sub_apply]
    ring

/-- Cochrane (2023), eq. (3.20), p. 65, `tsum` form under summability:
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`. -/
theorem unexpected_inflation_identity_tsum {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) {t : ℕ} (hv : 𝔼.E t (v t) = v t)
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hg : Summable fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω)
    (hrs : Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω := by
  have h1 := unexpected_inflation_identity 𝔼 h hr hv hT (seriesTo_of_hasSum hs.hasSum)
    (seriesTo_of_hasSum hg.hasSum)
  have h2 := (seriesTo_of_hasSum hrs.hasSum).unique h1
  linarith

/-- Cochrane (2023), eq. (3.21), p. 65 and Online Appendix §1.3: the linearised return on a
geometric-maturity portfolio, `rⁿ_{t+1} = ω q_{t+1} − q_t` (`q` the log bond price, `ω` the
maturity decay). -/
def BondReturn (om : ℝ) (q rn : ℕ → Ω → ℝ) : Prop := ∀ t, rn (t + 1) = om • q (t + 1) - q t

/-- Cochrane (2023), eq. (3.21), p. 65: with `q` known at each date and the terminal condition
`ωᵀ Δ_{t+1} q_{t+1+T} → 0`, `Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1} rⁿ_{t+1+j}`. -/
theorem bond_return_identity {om : ℝ} {q rn : ℕ → Ω → ℝ} (hb : BondReturn om q rn)
    {t : ℕ} (hq : 𝔼.E t (q t) = q t) {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) ω)
      (-innov 𝔼 t (rn (t + 1)) ω) := by
  have hrec : Recursion om q (fun t => -rn t) := fun t => by
    funext ω
    have := congrFun (hb t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have h0 := (rec_seriesTo_map (innov 𝔼 t) hrec hT).const_mul (-om)
  have hrn : innov 𝔼 t (rn (t + 1)) = om • innov 𝔼 t (q (t + 1)) := by
    rw [hb t, map_sub, map_smul, innov_of_known 𝔼 hq, sub_zero]
  refine h0.congr (fun j => ?_) ?_
  · rw [show t + 1 + 1 + j = t + 2 + j by omega, map_neg, Pi.neg_apply, pow_succ]
    ring
  · rw [hrn, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (3.21), p. 65, second equality: in terms of real returns and
inflation, `Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1}[r_{t+1+j} + π_{t+1+j}]`. -/
theorem bond_return_identity_real {om : ℝ} {q rn r infl : ℕ → Ω → ℝ}
    (hb : BondReturn om q rn) (hr : ∀ t, r t = rn t - infl t) {t : ℕ}
    (hq : 𝔼.E t (q t) = q t) {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) *
        (innov 𝔼 t (r (t + 2 + j)) ω + innov 𝔼 t (infl (t + 2 + j)) ω))
      (-innov 𝔼 t (rn (t + 1)) ω) := by
  refine (bond_return_identity 𝔼 hb hq hT).congr (fun j => ?_) rfl
  rw [hr, map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 65 ("with one-period debt `ω = 0`, `rⁿ_{t+1} = i_t` and is known ahead
of time"): with `ω = 0` the nominal return has no innovation. -/
theorem one_period_innov_rn {q rn : ℕ → Ω → ℝ} (hb : BondReturn 0 q rn) (hq : 𝔼.Adapted q)
    (t : ℕ) : innov 𝔼 t (rn (t + 1)) = 0 := by
  rw [hb t, zero_smul, zero_sub, map_neg, innov_of_known 𝔼 (hq t), neg_zero]

/-- Cochrane (2023), eq. (3.22), p. 65 (weighted unexpected-inflation identity): combining
(3.20) and (3.21), if `∑_{j≥0} ωʲ Δ_{t+1}π_{t+1+j}` converges to `P` and the surplus and growth
sums to `S`, `G`, then `∑_{j≥1}(ρʲ − ωʲ)Δ_{t+1}r_{t+1+j}` converges to `P + S + G`, i.e.
`∑ ωʲΔπ_{t+1+j} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}`. -/
theorem weighted_inflation_identity {ρ om : ℝ} {v r rn infl g s q : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hb : BondReturn om q rn)
    (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hTv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hTq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {S G P : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G)
    (hP : SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω) P) :
    SeriesTo (fun j => (ρ ^ (j + 1) - om ^ (j + 1)) * innov 𝔼 t (r (t + 2 + j)) ω)
      (P + S + G) := by
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) hTv hS hG
  have h2 := bond_return_identity_real 𝔼 hb hr (hq t) hTq
  have h3 : SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (infl (t + 2 + j)) ω)
      (P - innov 𝔼 t (infl (t + 1)) ω) := by
    refine (seriesTo_succ_iff.1 hP).congr (fun j => ?_) ?_
    · rw [show t + 1 + (j + 1) = t + 2 + j by omega]
    · simp
  refine (h1.sub (h2.sub h3)).congr (fun j => ?_) (by ring)
  ring

/-- Cochrane (2023), p. 66 (constant expected returns): `E_t r_{t+1} = c` at every date. -/
def ConstExpReturn (r : ℕ → Ω → ℝ) (c : ℝ) : Prop := ∀ t, 𝔼.E t (r (t + 1)) = fun _ => c

/-- Cochrane (2023), p. 66: with constant expected returns there is no news about future
returns, `Δ_{t+1} r_{t+1+j} = 0` for `j ≥ 1`. -/
theorem innov_future_return_zero {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ConstExpReturn 𝔼 r c)
    (t j : ℕ) : innov 𝔼 t (r (t + 2 + j)) = 0 := by
  have h1 : 𝔼.E (t + 1) (r (t + 2 + j)) = fun _ => c := by
    rw [show t + 2 + j = t + 1 + j + 1 by omega, ← 𝔼.tower (Nat.le_add_right (t + 1) j),
      hc, 𝔼.const]
  have h2 : 𝔼.E t (r (t + 2 + j)) = fun _ => c := by
    rw [show t + 2 + j = t + 1 + j + 1 by omega, ← 𝔼.tower (show t ≤ t + 1 + j by omega),
      hc, 𝔼.const]
  rw [innov_apply, h1, h2, sub_self]

/-- Cochrane (2023), eq. (3.24), p. 68: with constant expected returns and no growth,
`Δ_{t+1}π_{t+1} − Δ_{t+1}rⁿ_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem inflation_identity_const {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω = -S := by
  have hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) hT hS hG
  have h0 : SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp [innov_future_return_zero 𝔼 hc]) rfl
  have := h0.unique h1
  linarith

/-- Cochrane (2023), eq. (3.25), p. 68: with constant expected returns,
`Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1} π_{t+1+j}`. -/
theorem bond_return_identity_const {om c : ℝ} {q rn r infl : ℕ → Ω → ℝ}
    (hb : BondReturn om q rn) (hr : ∀ t, r t = rn t - infl t) (hc : ConstExpReturn 𝔼 r c)
    (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (infl (t + 2 + j)) ω)
      (-innov 𝔼 t (rn (t + 1)) ω) :=
  (bond_return_identity_real 𝔼 hb hr (hq t) hT).congr
    (fun j => by simp [innov_future_return_zero 𝔼 hc]) rfl

/-- Cochrane (2023), eq. (3.23), p. 67: with constant expected returns and no growth,
`∑_{j ≥ 0} ωʲ Δ_{t+1} π_{t+1+j} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem weighted_inflation_identity_const {ρ om c : ℝ} {v r rn infl s q : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t) (hb : BondReturn om q rn)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hTv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hTq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω) (-S) := by
  have h1 := inflation_identity_const 𝔼 h hr hc hv hTv hS
  have h2 := bond_return_identity_const 𝔼 hb hr hc hq hTq
  refine seriesTo_succ_iff.2 (h2.congr (fun j => ?_) ?_)
  · rw [show t + 2 + j = t + 1 + (j + 1) by omega]
  · simp only [pow_zero, one_mul, add_zero]
    linarith

/-- Cochrane (2023), p. 67 (one-period debt, time-varying expected returns): if `rⁿ_{t+1}` is
known at `t`, then `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`, i.e. the
discount-rate sum converges to `Δπ_{t+1} + S + G`. -/
theorem inflation_identity_one_period {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v) {t : ℕ}
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (innov 𝔼 t (infl (t + 1)) ω + S + G) := by
  refine (unexpected_inflation_identity 𝔼 h hr (hv t) hT hS hG).congr (fun _ => rfl) ?_
  rw [innov_of_known 𝔼 hrn, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), p. 66 (constant expected returns, one-period debt, no growth):
`Δ_{t+1}π_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem inflation_identity_one_period_const {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) {t : ℕ}
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    innov 𝔼 t (infl (t + 1)) ω = -S := by
  have := inflation_identity_const 𝔼 h hr hc hv hT hS
  rw [innov_of_known 𝔼 hrn, Pi.zero_apply, sub_zero] at this
  exact this

end Cochrane.DebtDeficitsInflation.LinearizedIdentities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linearised identities as exact derivatives

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix §1.2, eqs.
(1.4)–(1.13), pp. 556–559, and §1.3, eqs. (1.21)–(1.25), pp. 561–564; used for (3.17) and
(3.21), pp. 63–65.

The linear model of `LinearizedIdentities` (`Flow`, `BondReturn`) is linked to the nonlinear
identities as an EXACT first derivative at the steady state.

* Flow identity. The exact identity `V_t R^n_{t+1} = P_{t+1}sp_{t+1} + V_{t+1}` (1.6) gives
  the ratio form (1.7) (`flow_ratio`) and its log (1.9) (`log_flow`):
  `v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`. The right-hand side
  `flowLog (v', sy) = log(sy + e^{v'})` has, at a steady state `(v, sy)` with `e^v + sy > 0`,
  the derivative `ρ dv + (ρ/e^v) dsy` with `ρ = e^v/(e^v + sy) = e^{−(r−g)}`
  (`flowLog_hasFDerivAt`, `rhoLin_eq_exp`, `steady_state_flow`). The constant of (1.11) is
  `flow_constant`, and the first-order identity (1.13) is exactly `Flow` with
  `s̃ = ρ sy/e^v` (`flow_iff_first_order`).
* Bond return. With geometric maturity, the portfolio return is
  `rⁿ_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t` (1.22, `bondLog`). The steady-state price is
  `Q = ∑ ω^{j−1}/(1+i)^j = 1/(1 + i − ω)` (1.23, `bondQ_hasSum`), and the steady-state return is
  `(1 + ωQ)/Q = 1 + i` (`bond_steady_return`). The exact derivative at the steady state is
  `(ω/(1+i)) dq' − dq` (`bondLog_hasFDerivAt`). The first-order identity is exactly
  `BondReturn (ω/(1+i))` (`bondReturn_iff_first_order`).
* Survey E23: (1.24) replaces the exact coefficient `ω/(1+i)` by `ω`
  (`approx_1_24_differs`). Survey E22: iterating the return identity gives
  `q_t = −∑_{j≥1} ω^{j−1} rⁿ_{t+j}` (`bond_price_series`), not `−∑ ωʲ rⁿ_{t+j}`
  (`printed_bond_price_counterexample`).
-/

namespace Cochrane.DebtDeficitsInflation.LinearizationDerivation

open Filter Topology
open Cochrane.DebtDeficitsInflation.LinearizedIdentities

variable {Ω : Type*}

/-! ### The nonlinear flow identity -/

/-- Cochrane (2023), A1 eqs. (1.6)–(1.7), p. 557: the exact flow identity
`V_t R_{t+1} = P_{t+1} sp_{t+1} + V_{t+1}`, in ratios to GDP, is
`(V_t/(P_t y_t)) R_{t+1} (P_t/P_{t+1}) / G_{t+1} = sp_{t+1}/y_{t+1} + V_{t+1}/(P_{t+1}y_{t+1})`,
with `G_{t+1} = y_{t+1}/y_t`. -/
theorem flow_ratio {V R P sp V' P' y y' : ℝ} (hP : P ≠ 0) (hP' : P' ≠ 0) (hy : y ≠ 0)
    (hy' : y' ≠ 0) (h : V * R = P' * sp + V') :
    V / (P * y) * R * (P / P') / (y' / y) = sp / y' + V' / (P' * y') := by
  field_simp
  rw [← h]

/-- Cochrane (2023), A1 eq. (1.9), p. 558: the logarithm of the ratio flow identity (1.7),
`v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`, with
`v = log(V/(Py))`, `rⁿ = log Rⁿ`, `π = log Π`, `g = log G`. -/
theorem log_flow {a R Pi G sy b : ℝ} (ha : 0 < a) (hR : 0 < R) (hPi : 0 < Pi) (hG : 0 < G)
    (hb : 0 < b) (h : a * R / Pi / G = sy + b) :
    Real.log a + Real.log R - Real.log Pi - Real.log G = Real.log (sy + Real.exp (Real.log b)) := by
  rw [Real.exp_log hb, ← h, Real.log_div (by positivity) hG.ne', Real.log_div (by positivity)
    hPi.ne', Real.log_mul ha.ne' hR.ne']

/-- Cochrane (2023), A1 eq. (1.9), p. 558: the right-hand side of the log flow identity as a
function of `(v_{t+1}, sy_{t+1})`, `log(sy + e^{v'})`. -/
noncomputable def flowLog (p : ℝ × ℝ) : ℝ := Real.log (p.2 + Real.exp p.1)

/-- Cochrane (2023), A1 eq. (1.12), p. 558: the linearisation constant
`ρ = e^v/(e^v + sy)` at the steady state `(v, sy)`. -/
noncomputable def rhoLin (v sy : ℝ) : ℝ := Real.exp v / (Real.exp v + sy)

/-- Cochrane (2023), A1 p. 558: the steady-state `r − g = log((e^v + sy)/e^v)`. -/
noncomputable def ssRate (v sy : ℝ) : ℝ := Real.log ((Real.exp v + sy) / Real.exp v)

/-- Cochrane (2023), A1 p. 558: at a steady state the log flow identity reads
`v + (r − g) = log(sy + e^v)`. -/
theorem steady_state_flow {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    flowLog (v, sy) = v + ssRate v sy := by
  unfold flowLog ssRate
  rw [Real.log_div h.ne' (Real.exp_pos v).ne', Real.log_exp, add_comm sy]
  ring

/-- Cochrane (2023), A1 eq. (1.12), p. 558: `ρ = e^{−(r−g)}`. -/
theorem rhoLin_eq_exp {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    rhoLin v sy = Real.exp (-ssRate v sy) := by
  unfold rhoLin ssRate
  rw [Real.exp_neg, Real.exp_log (div_pos h (Real.exp_pos v)), inv_div]

/-- Cochrane (2023), A1 eq. (1.12), p. 558: `0 < ρ`, and `ρ < 1` exactly when the steady-state
surplus is positive. -/
theorem rhoLin_pos_lt_one_iff {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    0 < rhoLin v sy ∧ (rhoLin v sy < 1 ↔ 0 < sy) := by
  unfold rhoLin
  refine ⟨div_pos (Real.exp_pos v) h, ?_⟩
  rw [div_lt_one h]
  constructor <;> intro <;> linarith

/-- Cochrane (2023), A1 eq. (1.11), p. 558: the derivative of `log(sy + e^{v'})` at the steady
state, `(dv, dsy) ↦ ρ dv + (ρ/e^v) dsy`. -/
noncomputable def flowDeriv (v sy : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  rhoLin v sy • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (rhoLin v sy / Real.exp v) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), A1 eq. (1.11), p. 558: `Df(dv, dsy) = ρ dv + (ρ/e^v) dsy`. -/
theorem flowDeriv_apply (v sy : ℝ) (p : ℝ × ℝ) :
    flowDeriv v sy p = rhoLin v sy * p.1 + rhoLin v sy / Real.exp v * p.2 := by
  simp [flowDeriv]

/-- Cochrane (2023), A1 eqs. (1.9)–(1.11), p. 558: the linearisation of the flow identity is the
EXACT Fréchet derivative of `log(sy + e^{v'})` at the steady state. -/
theorem flowLog_hasFDerivAt {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    HasFDerivAt flowLog (flowDeriv v sy) (v, sy) := by
  have hin : HasFDerivAt (fun p : ℝ × ℝ => p.2 + Real.exp p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + Real.exp v • ContinuousLinearMap.fst ℝ ℝ ℝ) (v, sy) :=
    hasFDerivAt_snd.add ((Real.hasDerivAt_exp v).comp_hasFDerivAt (f := Prod.fst) (v, sy)
      hasFDerivAt_fst)
  have hne : (fun p : ℝ × ℝ => p.2 + Real.exp p.1) (v, sy) ≠ 0 := by
    simp only; linarith
  refine (hin.log hne).congr_fderiv ?_
  ext <;> simp [flowDeriv, rhoLin] <;> field_simp <;> ring

/-- Cochrane (2023), A1 eq. (1.11), p. 558: the constant of the first-order expansion,
`log(e^v + sy) − ρv − (ρ/e^v)sy = r − g + (1 − ρ)(v − 1)`. -/
theorem flow_constant {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    flowLog (v, sy) - flowDeriv v sy (v, sy) = ssRate v sy + (1 - rhoLin v sy) * (v - 1) := by
  rw [steady_state_flow h]
  have hev := Real.exp_pos v
  rw [flowDeriv_apply]
  simp only [rhoLin]
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.13), p. 558, and eq. (3.17), p. 63: in deviations from the steady
state, the first-order flow identity `v_t + r_{t+1} − g_{t+1} = Df(v_{t+1}, sy_{t+1})` is exactly
the linear `Flow` with `ρ = e^v/(e^v + sy)` and `s̃ = ρ sy/e^v`. -/
theorem flow_iff_first_order (v0 sy0 : ℝ) (v r g sy : ℕ → Ω → ℝ) :
    Flow (rhoLin v0 sy0) v r g (fun t => (rhoLin v0 sy0 / Real.exp v0) • sy t) ↔
      ∀ t ω, v t ω + r (t + 1) ω - g (t + 1) ω = flowDeriv v0 sy0 (v (t + 1) ω, sy (t + 1) ω) := by
  simp only [Flow, flowDeriv_apply]
  constructor
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this
    linarith
  · intro h t
    funext ω
    have := h t ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    linarith

/-! ### The geometric-maturity bond return -/

/-- Cochrane (2023), A1 eq. (1.23), p. 563: the steady-state portfolio price
`Q = 1/(1 + i − ω)`. -/
noncomputable def bondQ (i om : ℝ) : ℝ := 1 / (1 + i - om)

/-- Cochrane (2023), A1 eq. (1.23), p. 563: `Q = ∑_{j ≥ 1} ω^{j−1}/(1+i)^j = 1/(1 + i − ω)` for
`0 ≤ ω < 1 + i`. -/
theorem bondQ_hasSum {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    HasSum (fun j : ℕ => om ^ j / (1 + i) ^ (j + 1)) (bondQ i om) := by
  have hi : 0 < 1 + i := by linarith
  have hq : |om / (1 + i)| < 1 := by
    rw [abs_of_nonneg (div_nonneg hom hi.le), div_lt_one hi]; exact h
  have := (hasSum_geometric_of_abs_lt_one hq).mul_left (1 / (1 + i))
  convert this using 1
  · funext j
    rw [div_pow, pow_succ]
    field_simp
  · unfold bondQ
    have : 1 + i - om ≠ 0 := by linarith
    field_simp

/-- Cochrane (2023), A1 eq. (1.21) at the steady state, p. 563: `(1 + ωQ)/Q = 1 + i`. -/
theorem bond_steady_return {i om : ℝ} (h : om < 1 + i) :
    (1 + om * bondQ i om) / bondQ i om = 1 + i := by
  unfold bondQ
  have : 1 + i - om ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the log portfolio return as a function of
`(q_{t+1}, q_t)`, `log(1 + ω e^{q_{t+1}}) − q_t`. -/
noncomputable def bondLog (om : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (1 + om * Real.exp p.1) - p.2

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the derivative at the steady state,
`(dq', dq) ↦ (ω/(1+i)) dq' − dq`. -/
noncomputable def bondDeriv (i om : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (om / (1 + i)) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), A1 eq. (1.22), p. 563: `Df(dq', dq) = (ω/(1+i)) dq' − dq`. -/
theorem bondDeriv_apply (i om : ℝ) (p : ℝ × ℝ) :
    bondDeriv i om p = om / (1 + i) * p.1 - p.2 := by
  simp [bondDeriv]

/-- Cochrane (2023), A1 eq. (1.22), p. 563: at the steady state the log return is
`log(1 + i)`. -/
theorem bond_steady_log {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    bondLog om (Real.log (bondQ i om), Real.log (bondQ i om)) = Real.log (1 + i) := by
  have hQ : 0 < bondQ i om := by unfold bondQ; exact div_pos one_pos (by linarith)
  unfold bondLog
  rw [Real.exp_log hQ, ← Real.log_div (by positivity) hQ.ne', bond_steady_return h]

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the linearised bond return is the EXACT Fréchet
derivative of `log(1 + ω e^{q'}) − q` at the steady state `q' = q = log Q`; its coefficient is
`ωQ/(1 + ωQ) = ω/(1 + i)`. -/
theorem bondLog_hasFDerivAt {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    HasFDerivAt (bondLog om) (bondDeriv i om)
      (Real.log (bondQ i om), Real.log (bondQ i om)) := by
  set x : ℝ × ℝ := (Real.log (bondQ i om), Real.log (bondQ i om)) with hx
  have hQ : 0 < bondQ i om := by unfold bondQ; exact div_pos one_pos (by linarith)
  have hin : HasFDerivAt (fun p : ℝ × ℝ => 1 + om * Real.exp p.1)
      (om • (Real.exp x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (((Real.hasDerivAt_exp x.1).comp_hasFDerivAt x hasFDerivAt_fst).const_mul om).const_add 1
  have hne : (fun p : ℝ × ℝ => 1 + om * Real.exp p.1) x ≠ 0 := by
    simp only; positivity
  have h2 := (hin.log hne).sub (hasFDerivAt_snd (p := x))
  refine h2.congr_fderiv ?_
  have hex : Real.exp x.1 = bondQ i om := by rw [hx]; exact Real.exp_log hQ
  have hi : 1 + i - om ≠ 0 := by linarith
  have hi' : 1 + i ≠ 0 := by linarith
  ext
  · simp [bondDeriv, hex, bondQ]
    field_simp
    linear_combination om * mul_inv_cancel₀ hi'
  · simp [bondDeriv]

/-- Cochrane (2023), A1 eqs. (1.22) and (1.24), p. 563, and eq. (3.21), p. 65: in deviations, the
first-order bond-return identity `rⁿ_{t+1} = Df(q_{t+1}, q_t)` is exactly
`BondReturn (ω/(1+i))`. -/
theorem bondReturn_iff_first_order (i om : ℝ) (q rn : ℕ → Ω → ℝ) :
    BondReturn (om / (1 + i)) q rn ↔
      ∀ t ω, rn (t + 1) ω = bondDeriv i om (q (t + 1) ω, q t ω) := by
  simp only [BondReturn, bondDeriv_apply]
  constructor
  · intro h t ω
    have := congrFun (h t) ω
    simpa using this
  · intro h t
    funext ω
    simpa using h t ω

/-- Cochrane (2023), A1 eq. (1.24), p. 563 (survey E23): the approximation `ω/(1+i) ≈ ω` is not
exact; for `ω ≠ 0` the two coefficients differ whenever `i ≠ 0`. -/
theorem approx_1_24_differs {i om : ℝ} (hom : om ≠ 0) (hi : i ≠ 0) (hi1 : 1 + i ≠ 0) :
    om / (1 + i) ≠ om := by
  intro h
  rw [div_eq_iff hi1] at h
  have : om * i = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hom h1
  · exact hi h1

/-- Cochrane (2023), A1 p. 564, corrected (survey E22): iterating `rⁿ_{t+1} = ω q_{t+1} − q_t`
forward with `ωᵀ q_{t+T} → 0` gives `q_t = −∑_{j ≥ 1} ω^{j−1} rⁿ_{t+j}`. -/
theorem bond_price_series {om : ℝ} {q rn : ℕ → Ω → ℝ} (hb : BondReturn om q rn) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * q (t + T) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ j * (-rn (t + 1 + j) ω)) (q t ω) := by
  have hrec : Recursion om q (fun t => -rn t) := fun t => by
    funext ω
    have := congrFun (hb t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  exact rec_seriesTo_map LinearMap.id hrec hT

/-- Cochrane (2023), A1 p. 564 (survey E22, counterexample): with `ω = 1/2`, constant
`rⁿ = 1` and `q = −2` the return identity holds and `q = −∑ ω^{j−1} rⁿ = −2`, but the printed
`−∑_{j≥1} ωʲ rⁿ_{t+j}` is `−1`. -/
theorem printed_bond_price_counterexample :
    BondReturn (Ω := Unit) (1 / 2) (fun _ _ => -2) (fun _ _ => 1) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * 1 = 2 ∧ ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * 1 = 1 := by
  refine ⟨fun t => by funext ω; norm_num, ?_, ?_⟩
  · simp only [mul_one]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · simp only [mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num

end Cochrane.DebtDeficitsInflation.LinearizationDerivation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The surplus process and unexpected inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2–§4.2.4, eqs.
(4.1)–(4.10), pp. 86–93.

The "simple model" of §4.2 is the linearised flow identity with one-period debt
(`rⁿ_{t+1} = i_t` known at `t`), a constant expected real return and no growth
(`SimpleModel`), together with the innovation terminal condition (`InnovTVC`, automatic for a
bounded value of debt and `|ρ| < 1`). The surplus has a moving-average representation
`s_t = a(L)ε_t` (4.1).

## Main results

* (4.2) Hansen–Roberds–Sargent: `innov_infl_eq_tsum`, `innov_infl_eq`
  (`Δ_{t+1}π_{t+1} = −∑ρʲΔ_{t+1}s̃_{t+1+j} = −a(ρ)ε_{t+1}`), for every `|ρ| ≤ 1`; (4.4)
  `innov_infl_eq_surplus`; volatility and correlation, exactly: `condVar_innov_infl`,
  `condCov_innov_infl`, `no_correlation_of_gen_zero`; the 11% example
  `ar1_volatility_example`.
* (4.3) the AR(1): `gen_ar1`, `one_lt_gen_ar1_iff` (`a(ρ) > 1` iff `η > 0`; survey E2:
  the book's "a number greater than one" needs `η > 0`, `gen_ar1_lt_one_example`);
  `exists_neg_coeff_of_gen_lt_one` (`a(ρ) < 1` forces a negative coefficient).
* The MA(1): `isMA_ma1`, `gen_ma1`, `gen_ma1_inv`, `gen_ma1_zero`, `one_lt_gen_ma1`,
  `gen_ma1_mem_Ioo`, `innov_ma1_now`, `innov_ma1_next`; survey E3: the signs of the p. 88 example
  (`ma1_printed_signs_false`).
* §4.2.2: (4.5) `value_ar1`, (4.6) `value_recursion`, (4.7) `rho_innov_value`,
  `rho_innov_value_eq`, `innov_value_pos_iff`, `innov_value_full_repayment`,
  `innov_value_eq_series`.
* §4.2.3 exact model (Section 2.7 valuation with a constant real rate): (4.8)
  `exact_innov_flow`, (4.9) `exact_innov_flow_pv`, (4.10) `exact_innov_flow_ma`; revenue from
  bond sales `revenue_innov`; financing cases `financing_by_debt`, `financing_by_inflation`,
  `financing_superinflation`; `exact_flow_of_valuation`.
* p. 87 exact line (survey E1): `exact_innov_line` (`(B_t/P_t)Δ(P_t/P_{t+1}) =
  Δ∑βʲs_{t+1+j} = a(β)ε_{t+1}`), the printed sum over `s_{t+j}` gives `β a(β) ε_{t+1}`
  (`printed_exact_line`, `printed_exact_line_iff`, counterexample
  `printed_exact_line_counterexample`).
* §4.2.4: `innov_return`, `innov_return_split`, `innov_return_riskfree`,
  `abs_innov_return_ge`; the one-step stochastic-discount-factor valuation of p. 93,
  `sdf_one_step`.
-/

namespace Cochrane.DebtDeficitsInflation.SurplusMA

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The simple model -/

/-- Cochrane (2023), §4.2, p. 87 ("one-period debt, a constant real rate, and flexible
prices"): the linearised flow identity (3.17) with no growth, `r = rⁿ − π`, `v` known at each
date, one-period debt (`rⁿ_{t+1} = i_t` known at `t`) and a constant expected real return
`E_t r_{t+1} = c`. -/
def SimpleModel (ρ c : ℝ) (v r rn infl s : ℕ → Ω → ℝ) : Prop :=
  Flow ρ v r (fun _ => 0) s ∧ (∀ t, r t = rn t - infl t) ∧ 𝔼.Adapted v ∧
    (∀ t, 𝔼.E t (rn (t + 1)) = rn (t + 1)) ∧ ConstExpReturn 𝔼 r c

/-- Cochrane (2023), eq. (3.19), p. 64 (the terminal condition, in innovations):
`ρᵀ Δ_{t+1} v_{t+T} → 0` at every date and state. -/
def InnovTVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 64 ("the assumption or observation that debt/GDP is a stationary
process is enough"): a bounded value of debt satisfies the innovation terminal condition for
`|ρ| < 1`. -/
theorem innovTVC_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v) :
    InnovTVC 𝔼 ρ v := by
  obtain ⟨M, hM⟩ := hv
  exact fun t ω => tvc_innov_of_bounded 𝔼 hρ hM t t ω

/-! ### (4.2): unexpected inflation is `−a(ρ)ε` -/

/-- Cochrane (2023), eq. (4.2), p. 87, first equality: in the simple model,
`Δ_{t+1}π_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`, valid for every `|ρ| ≤ 1`. -/
theorem innov_infl_eq_tsum {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω := by
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hS := innov_PV_termwise 𝔼 hs hε hM hρ t ω
  rw [inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) (hT t ω)
    (seriesTo_of_hasSum hS), hS.tsum_eq]

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): in the simple model
`Δ_{t+1}π_{t+1} = −∑_j a_j ρʲ ε_{t+1} = −a(ρ) ε_{t+1}`, for every `|ρ| ≤ 1`. -/
theorem innov_infl_eq {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) : innov 𝔼 t (infl (t + 1)) = -gen a ρ • ε ((t : ℤ) + 1) := by
  funext ω
  rw [innov_infl_eq_tsum 𝔼 hm hT hs hε hM hρ t ω,
    (innov_PV_termwise 𝔼 hs hε hM hρ t ω).tsum_eq]
  simp

/-- Cochrane (2023), eq. (4.4), p. 88: with the normalisation `a_0 = 1`,
`Δ_{t+1}π_{t+1} = −a(ρ) Δ_{t+1}s̃_{t+1}`. -/
theorem innov_infl_eq_surplus {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen a ρ • innov 𝔼 t (s (t + 1)) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, innov_MA_zero 𝔼 hs hε hM ha0]

/-- Cochrane (2023), §4.2.1, p. 88 (inflation volatility): the conditional variance of
unexpected inflation is `a(ρ)²` times that of the surplus shock,
`E_t[(Δπ_{t+1})²] = a(ρ)² E_t[ε²_{t+1}]`. -/
theorem condVar_innov_infl {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω ^ 2) =
      gen a ρ ^ 2 • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, ← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §4.2.1, pp. 88–89 (correlation of inflation and deficit shocks): the
conditional covariance of unexpected inflation with the surplus shock is
`E_t[Δπ_{t+1} ε_{t+1}] = −a(ρ) E_t[ε²_{t+1}]`. -/
theorem condCov_innov_infl {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) =
      -gen a ρ • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, ← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §4.2.1, p. 89 ("consider the case `a(ρ) = 0` ... the model predicts no
correlation between deficits and inflation"): with `a(ρ) = 0` there is no unexpected inflation
at all, so in particular no covariance with the surplus shock. -/
theorem no_correlation_of_gen_zero {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = 0 ∧
      𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) = 0 := by
  refine ⟨by rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, h0]; simp, ?_⟩
  rw [condCov_innov_infl 𝔼 hm hT hs hε hM hρ, h0, neg_zero, zero_smul]

/-- Cochrane (2023), §4.2.1, p. 88: the numerical example "5/(1 − 0.55) = 11%" (it is
`100/9 ≈ 11.1`). -/
theorem ar1_volatility_example : (5 : ℝ) / (1 - 0.55) = 100 / 9 ∧
    (11 : ℝ) < 5 / (1 - 0.55) ∧ (5 : ℝ) / (1 - 0.55) < 11.2 := by
  norm_num

/-! ### Examples: the AR(1) and the MA(1) -/

/-- Cochrane (2023), eq. (4.3), p. 88: for the AR(1), `a(ρ) = ∑ ηʲρʲ = 1/(1 − ρη)`
(`|ρη| < 1`). -/
theorem gen_ar1 {η ρ : ℝ} (h : |ρ * η| < 1) : gen (fun j => η ^ j) ρ = 1 / (1 - ρ * η) := by
  unfold gen
  simp_rw [← mul_pow]
  rw [mul_comm η ρ, tsum_geometric_of_abs_lt_one h, one_div]

/-- Cochrane (2023), p. 88, corrected (survey E2): "`a(ρ) = 1/(1 − ρη)` is a number greater than
one" holds exactly when `η > 0` (for `0 < ρ`, `|ρη| < 1`). -/
theorem one_lt_gen_ar1_iff {η ρ : ℝ} (hρ : 0 < ρ) (h : |ρ * η| < 1) :
    1 < gen (fun j => η ^ j) ρ ↔ 0 < η := by
  rw [gen_ar1 h]
  have h1 : 0 < 1 - ρ * η := by linarith [le_abs_self (ρ * η)]
  rw [lt_div_iff₀ h1, one_mul]
  constructor
  · intro h2
    by_contra h3
    push Not at h3
    nlinarith
  · intro h2
    nlinarith

/-- Cochrane (2023), p. 88 (survey E2, counterexample): with `η = −0.3` (and `ρ = 0.9`)
`a(ρ) = 1/1.27 < 1`, so the AR(1) does not always give `a(ρ) > 1`. -/
theorem gen_ar1_lt_one_example : gen (fun j => (-0.3 : ℝ) ^ j) 0.9 < 1 := by
  rw [gen_ar1 (by norm_num [abs_of_neg])]
  norm_num

/-- Cochrane (2023), p. 88 ("since by normalization `a_0 = 1 > 0`, `a(ρ) < 1` means that some of
the higher moving average terms `a_j` must be negative"), for `ρ > 0`. -/
theorem exists_neg_coeff_of_gen_lt_one {a : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsum : Summable fun j => a j * ρ ^ j) (ha0 : a 0 = 1) (hlt : gen a ρ < 1) :
    ∃ j, 1 ≤ j ∧ a j < 0 := by
  by_contra hcon
  push Not at hcon
  have hnn : ∀ j, 0 ≤ a (j + 1) * ρ ^ (j + 1) := fun j =>
    mul_nonneg (hcon (j + 1) (by omega)) (pow_nonneg hρ.le _)
  have : 1 ≤ gen a ρ := by
    unfold gen
    rw [hsum.tsum_eq_zero_add, ha0]
    simp only [pow_zero, mul_one, le_add_iff_nonneg_right]
    exact tsum_nonneg hnn
  linarith

/-- Cochrane (2023), p. 88: the MA(1) coefficients `a_0 = 1`, `a_1 = −θ`, `a_j = 0` for
`j ≥ 2`. -/
def ma1Coeff (θ : ℝ) (j : ℕ) : ℝ := if j = 0 then 1 else if j = 1 then -θ else 0

/-- Cochrane (2023), p. 88: `s_t = ε_t − θ ε_{t−1} = (1 − θL)ε_t` is a moving average with the
MA(1) coefficients. -/
theorem isMA_ma1 (θ : ℝ) (ε : ℤ → Ω → ℝ) :
    IsMA (ma1Coeff θ) ε (fun t => ε t - θ • ε ((t : ℤ) - 1)) := by
  refine ⟨summable_of_ne_finset_zero (s := {0, 1}) fun j hj => ?_, fun t ω => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [ma1Coeff, hj.1, hj.2]
  · rw [tsum_eq_sum (s := {0, 1}) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [ma1Coeff, hj.1, hj.2]]
    simp [ma1Coeff]
    ring

/-- Cochrane (2023), p. 88: the MA(1) has `a(z) = 1 − θz`. -/
theorem gen_ma1 (θ z : ℝ) : gen (ma1Coeff θ) z = 1 - θ * z := by
  unfold gen
  rw [tsum_eq_sum (s := {0, 1}) fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [ma1Coeff, hj.1, hj.2]]
  simp [ma1Coeff]
  ring

/-- Cochrane (2023), p. 88: "For `θ = ρ⁻¹`, we have `a(ρ) = 0`" (full repayment with
interest). -/
theorem gen_ma1_inv {ρ : ℝ} (hρ : ρ ≠ 0) : gen (ma1Coeff ρ⁻¹) ρ = 0 := by
  rw [gen_ma1, inv_mul_cancel₀ hρ, sub_self]

/-- Cochrane (2023), p. 88: "The value `θ = 0` gives an i.i.d. surplus process with
`a(ρ) = 1`". -/
theorem gen_ma1_zero (ρ : ℝ) : gen (ma1Coeff 0) ρ = 1 := by
  rw [gen_ma1, zero_mul, sub_zero]

/-- Cochrane (2023), p. 88: "a negative `θ` generates ... `a(ρ) > 1`" (for `ρ > 0`). -/
theorem one_lt_gen_ma1 {θ ρ : ℝ} (hθ : θ < 0) (hρ : 0 < ρ) : 1 < gen (ma1Coeff θ) ρ := by
  rw [gen_ma1]
  nlinarith

/-- Cochrane (2023), p. 88: "Smaller values of `θ` accommodate `0 < a(ρ) < 1`": for
`0 < θ < ρ⁻¹` (and `ρ > 0`), `0 < a(ρ) < 1`. -/
theorem gen_ma1_mem_Ioo {θ ρ : ℝ} (hρ : 0 < ρ) (hθ0 : 0 < θ) (hθ1 : θ < ρ⁻¹) :
    0 < gen (ma1Coeff θ) ρ ∧ gen (ma1Coeff θ) ρ < 1 := by
  rw [gen_ma1]
  have h : θ * ρ < 1 := by
    have := mul_lt_mul_of_pos_right hθ1 hρ
    rwa [inv_mul_cancel₀ hρ.ne'] at this
  constructor <;> nlinarith

/-- Cochrane (2023), p. 88: for the MA(1), the deficit shock is the surplus innovation,
`Δ_{t+1}s_{t+1} = ε_{t+1}`. -/
theorem innov_ma1_now {θ : ℝ} {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    innov 𝔼 t ((fun t : ℕ => ε t - θ • ε ((t : ℤ) - 1)) (t + 1)) = ε ((t : ℤ) + 1) :=
  innov_MA_zero 𝔼 (isMA_ma1 θ ε) hε hM (by simp [ma1Coeff]) t

/-- Cochrane (2023), p. 88: "that shock changes the expected value of the next surplus":
`Δ_{t+1}s_{t+2} = −θ ε_{t+1}` (so a deficit shock `ε_{t+1} = −1` raises it by `θ`). -/
theorem innov_ma1_next {θ : ℝ} {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    innov 𝔼 t ((fun t : ℕ => ε t - θ • ε ((t : ℤ) - 1)) (t + 1 + 1)) =
      -θ • ε ((t : ℤ) + 1) := by
  rw [innov_MA 𝔼 (isMA_ma1 θ ε) hε hM t 1]
  simp [ma1Coeff]

/-- Cochrane (2023), p. 88, corrected (survey E3): with `θ = ρ⁻¹` the shock sets
`Δ_{t+1}s_{t+1} = ε_{t+1}` and `Δ_{t+1}s_{t+2} = −ρ⁻¹ε_{t+1}`; the printed
"`s₁ = −ε₁` ... `s₂ = ρ⁻¹ε₁`" (both signs flipped) holds in a state only if there is no
shock in that state. -/
theorem ma1_printed_signs_false {ρ : ℝ} (hρ : ρ ≠ 0) {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) (ω : Ω)
    (hprinted : innov 𝔼 t ((fun t : ℕ => ε t - ρ⁻¹ • ε ((t : ℤ) - 1)) (t + 1)) ω =
        -ε ((t : ℤ) + 1) ω ∨
      innov 𝔼 t ((fun t : ℕ => ε t - ρ⁻¹ • ε ((t : ℤ) - 1)) (t + 1 + 1)) ω =
        ρ⁻¹ * ε ((t : ℤ) + 1) ω) :
    ε ((t : ℤ) + 1) ω = 0 := by
  rw [innov_ma1_now 𝔼 hε hM, innov_ma1_next 𝔼 hε hM] at hprinted
  simp only [Pi.smul_apply, smul_eq_mul] at hprinted
  have hi : ρ⁻¹ ≠ 0 := inv_ne_zero hρ
  rcases hprinted with h | h
  · linarith
  · have : 2 * ρ⁻¹ * ε ((t : ℤ) + 1) ω = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (mul_ne_zero two_ne_zero hi)
    · exact h1

/-! ### §4.2.2: surpluses and debt -/

/-- Cochrane (2023), eq. (4.6), p. 89: in the simple model,
`v_t = E_t(s̃_{t+1} + ρ v_{t+1}) − c` (with the book's normalisation `c = E_t r_{t+1} = 0`,
`v_t = E_t(s̃_{t+1} + ρ v_{t+1})`). -/
theorem value_recursion {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (t : ℕ) :
    v t = 𝔼.E t (s (t + 1) + ρ • v (t + 1)) - fun _ => c := by
  obtain ⟨hf, -, hv, -, hc⟩ := hm
  have h := hf t
  have hv' : v t = ρ • v (t + 1) + s (t + 1) - r (t + 1) := by
    rw [h]; funext ω; simp
  conv_lhs => rw [← hv t, hv']
  rw [map_sub, hc t, add_comm]

/-- Cochrane (2023), eq. (4.5), p. 89: with an AR(1) surplus (`E_t s_{t+1} = η s_t`) and
constant expected return normalised to zero, `v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j} = η s_t/(1 − ρη)`
(under the terminal condition `ρᵀ E_t v_{t+T} → 0`, `|ρη| < 1`). -/
theorem value_ar1 {ρ η : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ 0 v r rn infl s) (hs : 𝔼.IsAR1 η s) (hρη : |ρ * η| < 1) {t : ℕ}
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (v t ω) ∧
      v t ω = η * s t ω / (1 - ρ * η) := by
  obtain ⟨hf, -, hv, -, hc⟩ := hm
  have hE : ∀ j, 𝔼.E t (s (t + 1 + j)) ω = η ^ (j + 1) * s t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hs]
    rfl
  have hS : HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (η * s t ω / (1 - ρ * η)) := by
    have := (hasSum_geometric_of_abs_lt_one hρη).mul_left (η * s t ω)
    convert this using 1
    · funext j
      rw [hE, mul_pow]
      ring
    · field_simp
  have hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have hR := pv_expected 𝔼 hf hv hT (seriesTo_of_hasSum hS) hG
  have hR0 : SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) 0 := by
    refine seriesTo_zero.congr (fun j => ?_) rfl
    rw [← 𝔼.tower (show t ≤ t + j by omega), show t + 1 + j = t + j + 1 by omega, hc,
      𝔼.const, mul_zero]
  have heq := hR0.unique hR
  refine ⟨(seriesTo_of_hasSum hS).congr (fun _ => rfl) (by linarith), by linarith⟩

/-- Cochrane (2023), eq. (4.7), p. 89, first equality: innovations of the flow identity,
`ρ Δ_{t+1} v_{t+1} = −Δ_{t+1}π_{t+1} − Δ_{t+1}s̃_{t+1}` (no terminal condition needed). -/
theorem rho_innov_value {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (t : ℕ) :
    ρ • innov 𝔼 t (v (t + 1)) = -innov 𝔼 t (infl (t + 1)) - innov 𝔼 t (s (t + 1)) := by
  obtain ⟨hf, hr, hv, hrn, -⟩ := hm
  rw [← map_smul, hf t, map_sub, map_sub, map_add, innov_of_known 𝔼 (hv t), hr (t + 1),
    map_sub, innov_of_known 𝔼 (hrn t)]
  simp

/-- Cochrane (2023), eq. (4.7), p. 89: `ρ Δ_{t+1} v_{t+1} = [a(ρ) − 1] ε_{t+1}`. -/
theorem rho_innov_value_eq {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    ρ • innov 𝔼 t (v (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) := by
  rw [rho_innov_value 𝔼 hm, innov_infl_eq 𝔼 hm hT hs hε hM hρ, innov_MA_zero 𝔼 hs hε hM ha0,
    sub_smul, one_smul, neg_smul, neg_neg]

/-- Cochrane (2023), pp. 89–90: "If `a(ρ) > 1` ... a surprise surplus ... raises the value of
debt ... If `a(ρ) < 1` ... lowers the value of debt": for a positive surplus shock and `ρ > 0`,
`Δ_{t+1} v_{t+1} > 0` iff `a(ρ) > 1`. -/
theorem innov_value_pos_iff {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ0 : 0 < ρ) (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω)
    (hpos : 0 < ε ((t : ℤ) + 1) ω) : 0 < innov 𝔼 t (v (t + 1)) ω ↔ 1 < gen a ρ := by
  have h := congrFun (rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at h
  constructor
  · intro hv
    have : 0 < (gen a ρ - 1) * ε ((t : ℤ) + 1) ω := by rw [← h]; positivity
    have := (pos_iff_pos_of_mul_pos this).2 hpos
    linarith
  · intro hg
    have : 0 < ρ * innov 𝔼 t (v (t + 1)) ω := by
      rw [h]; exact mul_pos (by linarith) hpos
    exact (pos_iff_pos_of_mul_pos this).1 hρ0

/-- Cochrane (2023), p. 90: "In the case of full repayment `a(ρ) = 0`, then a higher surplus
lowers the value of debt one for one" (`ρΔv_{t+1} = −ε_{t+1}`, and inflation is unaffected);
with `a(ρ) = 1` the deficit is financed by inflation and the value of debt is unchanged. -/
theorem innov_value_full_repayment {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    (gen a ρ = 0 → ρ • innov 𝔼 t (v (t + 1)) = -ε ((t : ℤ) + 1) ∧
        innov 𝔼 t (infl (t + 1)) = 0) ∧
      (gen a ρ = 1 → ρ • innov 𝔼 t (v (t + 1)) = 0 ∧
        innov 𝔼 t (infl (t + 1)) = -innov 𝔼 t (s (t + 1))) := by
  have h1 := rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t
  have h2 := innov_infl_eq 𝔼 hm hT hs hε hM hρ t
  refine ⟨fun h0 => ⟨?_, ?_⟩, fun h0 => ⟨?_, ?_⟩⟩
  · rw [h1, h0]; simp
  · rw [h2, h0]; simp
  · rw [h1, h0]; simp
  · rw [h2, h0, innov_MA_zero 𝔼 hs hε hM ha0]; simp

/-- Cochrane (2023), p. 91 (the linearised rearrangement of (4.8)–(4.10)):
`ρ Δ_{t+1} v_{t+1} = ρ Δ_{t+1} ∑_{j ≥ 0} ρʲ s̃_{t+2+j} = [a(ρ) − 1] ε_{t+1}`: the series
`∑_j ρ^{j+1} Δ_{t+1} s̃_{t+2+j}` converges to `ρ Δ_{t+1} v_{t+1}`. -/
theorem innov_value_eq_series {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (s (t + 2 + j)) ω)
      (ρ * innov 𝔼 t (v (t + 1)) ω) := by
  obtain ⟨hf, -, -, -, hc⟩ := hm
  have hT' : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) ω) atTop (𝓝 0) := by
    have h := (hT t ω).const_mul ρ⁻¹
    rw [mul_zero] at h
    by_cases hρ : ρ = 0
    · subst hρ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT1
      rw [zero_pow (by omega), zero_mul]
    · rw [← tendsto_add_atTop_iff_nat 1] at h
      refine h.congr fun T => ?_
      rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
      field_simp
  have h0 := (rec_seriesTo_map (innov 𝔼 t)
    ((flow_iff_recursion ρ v r (fun _ => 0) s).1 hf) hT').const_mul ρ
  refine h0.congr (fun j => ?_) (by rw [mul_comm])
  rw [show t + 1 + 1 + j = t + 2 + j by omega, map_sub, map_add, Pi.sub_apply, Pi.add_apply,
    innov_future_return_zero 𝔼 hc, pow_succ]
  simp
  ring

/-! ### §4.2.4: the return on government debt -/

/-- Cochrane (2023), §4.2.4, p. 92: in the simple model the ex-post real return innovation is
`Δ_{t+1} r_{t+1} = −Δ_{t+1}π_{t+1} = a(ρ) ε_{t+1}`. -/
theorem innov_return {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (r (t + 1)) = -innov 𝔼 t (infl (t + 1)) ∧
      innov 𝔼 t (r (t + 1)) = gen a ρ • ε ((t : ℤ) + 1) := by
  have h1 : innov 𝔼 t (r (t + 1)) = -innov 𝔼 t (infl (t + 1)) := by
    obtain ⟨-, hr, -, hrn, -⟩ := hm
    rw [hr, map_sub, innov_of_known 𝔼 (hrn t), zero_sub]
  refine ⟨h1, ?_⟩
  rw [h1, innov_infl_eq 𝔼 hm hT hs hε hM hρ, neg_smul, neg_neg]

/-- Cochrane (2023), §4.2.4, p. 92: the return split into "price change" and "dividend",
`r_{t+1} = ρv_{t+1} − v_t + s̃_{t+1}` and `Δ_{t+1}r_{t+1} = ρΔv_{t+1} + Δs̃_{t+1} =
[a(ρ) − 1]ε_{t+1} + ε_{t+1}`. -/
theorem innov_return_split {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    r (t + 1) = ρ • v (t + 1) - v t + s (t + 1) ∧
      innov 𝔼 t (r (t + 1)) = ρ • innov 𝔼 t (v (t + 1)) + innov 𝔼 t (s (t + 1)) ∧
      innov 𝔼 t (r (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) + ε ((t : ℤ) + 1) := by
  have hsplit : r (t + 1) = ρ • v (t + 1) - v t + s (t + 1) := by
    rw [hm.1 t]; funext ω; simp; ring
  have h2 : innov 𝔼 t (r (t + 1)) = ρ • innov 𝔼 t (v (t + 1)) + innov 𝔼 t (s (t + 1)) := by
    rw [hsplit, map_add, map_sub, map_smul, innov_of_known 𝔼 (hm.2.2.1 t), sub_zero]
  refine ⟨hsplit, h2, ?_⟩
  rw [h2, rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ, innov_MA_zero 𝔼 hs hε hM ha0]

/-- Cochrane (2023), §4.2.4, p. 92: "With `a(ρ) = 0`, unexpected inflation ... is zero, and
nominal government bonds are risk free in real terms, for any volatility of surpluses". -/
theorem innov_return_riskfree {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℕ) : innov 𝔼 t (r (t + 1)) = 0 := by
  rw [(innov_return 𝔼 hm hT hs hε hM hρ t).2, h0, zero_smul]

/-- Cochrane (2023), §4.2.4, p. 92: "With `a(ρ) ≥ 1` ... the rate of return is more volatile
than surpluses": `|Δ_{t+1} r_{t+1}| ≥ |Δ_{t+1} s̃_{t+1}|` in every state. -/
theorem abs_innov_return_ge {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (h1 : 1 ≤ gen a ρ) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t (s (t + 1)) ω| ≤ |innov 𝔼 t (r (t + 1)) ω| := by
  rw [(innov_return 𝔼 hm hT hs hε hM hρ t).2, innov_MA_zero 𝔼 hs hε hM ha0, Pi.smul_apply,
    smul_eq_mul, abs_mul, abs_of_pos (show 0 < gen a ρ by linarith)]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

/-- Cochrane (2023), §4.2.4, p. 93: the one-step valuation with a stochastic discount factor
`Λ`: if `V_t = E_t ∑_{j ≥ 1} (Λ_{t+j}/Λ_t) s_{t+j}` at every date, then
`V_t = E_t[(Λ_{t+1}/Λ_t) s_{t+1}] + E_t[(Λ_{t+1}/Λ_t) V_{t+1}]` (with `V_t = Q_tB_t/P_t` and
`Λ_{t+1}/Λ_t = βu'(c_{t+1})/u'(c_t)` this is the book's display). -/
theorem sdf_one_step (hpull : 𝔼.PullOut) {Λ s V : ℕ → Ω → ℝ} (hΛ0 : ∀ t ω, Λ t ω ≠ 0)
    (hm : ∀ t, 𝔼.E (t + 1) (fun ω => Λ (t + 1) ω / Λ t ω) = fun ω => Λ (t + 1) ω / Λ t ω)
    (hsum : ∀ t ω, Summable fun j => Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω)
    (hV : ∀ t, V t = 𝔼.E t (fun ω => ∑' j, Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω))
    (t : ℕ) :
    V t = 𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * s (t + 1) ω) +
      𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * V (t + 1) ω) := by
  set m : Ω → ℝ := fun ω => Λ (t + 1) ω / Λ t ω with hm_def
  set R : Ω → ℝ := fun ω => ∑' j, Λ (t + 1 + 1 + j) ω / Λ (t + 1) ω * s (t + 1 + 1 + j) ω
    with hR_def
  have hsplit : (fun ω => ∑' j, Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω) =
      (fun ω => m ω * s (t + 1) ω) + m * R := by
    funext ω
    rw [(hsum t ω).tsum_eq_zero_add]
    simp only [Pi.add_apply, Pi.mul_apply, hm_def, hR_def, add_zero]
    rw [← tsum_mul_left]
    congr 1
    refine tsum_congr fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
    field_simp [hΛ0 t ω, hΛ0 (t + 1) ω]
  have hVR : 𝔼.E (t + 1) R = V (t + 1) := (hV (t + 1)).symm
  have hmR : 𝔼.E t (m * R) = 𝔼.E t (fun ω => m ω * V (t + 1) ω) := by
    rw [← 𝔼.tower (Nat.le_succ t), hpull (t + 1) m R (hm t), hVR]
    rfl
  rw [hV t, hsplit, map_add, hmR]

/-! ### §4.2.3: the exact model -/

/-- Cochrane (2023), §4.2.3, p. 91: the real value of maturing debt `B_t/P_{t+1}`. -/
noncomputable def realDebt (B P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => B t ω / P (t + 1) ω

/-- Cochrane (2023), §4.2.3, p. 91: the end-of-period debt deflated by today's price,
`B_t/P_t`. -/
noncomputable def realDebtEnd (B P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => B t ω / P t ω

/-- Cochrane (2023), §4.2.3, p. 91: the inverse gross inflation rate `P_t/P_{t+1}`. -/
noncomputable def deflation (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => P t ω / P (t + 1) ω

/-- Cochrane (2023), §2.7 and §4.2.3, p. 91 (constant real rate, flexible prices): the
one-period bond price `Q_t = β E_t(P_t/P_{t+1})`. -/
noncomputable def bondPrice (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := β • 𝔼.E t (deflation P t)

/-- Cochrane (2023), p. 87: the discounted sum `∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), §2.7 and §4.2, p. 87: the exact valuation equation
`B_t/P_{t+1} = E_{t+1} ∑_{j ≥ 0} βʲ s_{t+1+j}` at every date. -/
def ExactValuation (β : ℝ) (B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, realDebt B P t = 𝔼.E (t + 1) (pv β s (t + 1))

/-- Cochrane (2023), p. 91: `B_t/P_{t+1} = (B_t/P_t)(P_t/P_{t+1})`. -/
theorem realDebt_eq_mul {B P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    realDebt B P t = realDebtEnd B P t * deflation P t := by
  funext ω
  simp only [realDebt, realDebtEnd, deflation, Pi.mul_apply]
  field_simp [hP t ω, hP (t + 1) ω]

/-- Cochrane (2023), p. 87: `∑_{j ≥ 0} βʲ s_{t+j} = s_t + β ∑_{j ≥ 0} βʲ s_{t+1+j}` for a
bounded surplus and `|β| < 1`. -/
theorem pv_succ {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {K : ℝ} (hs : ∀ t ω, |s t ω| ≤ K)
    (t : ℕ) : pv β s t = s t + β • pv β s (t + 1) := by
  funext ω
  have hsum : Summable fun j => β ^ j * s (t + j) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right K)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hs _ ω) (pow_nonneg (abs_nonneg _) _)
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]
  ring

/-- Cochrane (2023), p. 91: real revenue from bond sales, `Q_t B_t/P_t = β E_t(B_t/P_{t+1})`
(uses the pull-out property, since `B_t/P_t` is known at `t`). -/
theorem revenue_eq (hpull : 𝔼.PullOut) {β : ℝ} {B P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t) (t : ℕ) :
    bondPrice 𝔼 β P t * realDebtEnd B P t = β • 𝔼.E t (realDebt B P t) := by
  rw [realDebt_eq_mul hP, hpull t _ _ (hBP t), bondPrice, smul_mul_assoc, mul_comm]

/-- Cochrane (2023), §2.7 and p. 91: the exact valuation equation implies the exact flow
identity `B_t/P_{t+1} = s_{t+1} + Q_{t+1} B_{t+1}/P_{t+1}`. -/
theorem exact_flow_of_valuation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t) (hsa : 𝔼.Adapted s) {K : ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s) (t : ℕ) :
    realDebt B P t = s (t + 1) + bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1) := by
  rw [revenue_eq 𝔼 hpull hP hBP, hval (t + 1), 𝔼.tower (Nat.le_succ (t + 1)), hval t,
    pv_succ hβ hsb, map_add, map_smul, hsa]

/-- Cochrane (2023), p. 87, corrected (survey E1): in the exact model,
`(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) = Δ_{t+1} ∑_{j ≥ 0} βʲ s_{t+1+j} = a(β) ε_{t+1}`. -/
theorem exact_innov_line (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) = innov 𝔼 t (pv β s (t + 1)) ∧
      innov 𝔼 t (pv β s (t + 1)) = gen a β • ε ((t : ℤ) + 1) := by
  have hknown : 𝔼.E (t + 1) (realDebtEnd B P t) = realDebtEnd B P t :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hBP t)
  refine ⟨?_, innov_PV 𝔼 hs hε hM hβ t⟩
  have hr : innov 𝔼 t (pv β s (t + 1)) = innov 𝔼 t (realDebt B P t) := by
    rw [hval t, innov_E_of_le 𝔼 le_rfl]
  rw [hr, realDebt_eq_mul hP, innov_apply, innov_apply, hpull (t + 1) _ _ hknown,
    hpull t _ _ (hBP t), mul_sub]

/-- Cochrane (2023), p. 87, as printed (survey E1): the innovation in `∑_{j ≥ 0} βʲ s_{t+j}`
(current surplus included) is `β a(β) ε_{t+1}`, not `a(β) ε_{t+1}`. -/
theorem printed_exact_line {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (t : ℕ) : innov 𝔼 t (pv β s t) = (β * gen a β) • ε ((t : ℤ) + 1) := by
  have hv := (isMA_iff_vec a ε s).1 hs
  have hsa := adapted_MAVec 𝔼 hv (isMDSVec_of_isMDS 𝔼 hε) (fun k _ ω => hM k ω)
  rw [pv_succ hβ (fun t ω => abs_MAVec_le hv (fun k _ ω => hM k ω) t ω), map_add, map_smul,
    innov_of_known 𝔼 (hsa t), zero_add]
  change β • innov 𝔼 t (fun ω => ∑' j, β ^ j * s (t + 1 + j) ω) = _
  rw [innov_PV 𝔼 hs hε hM hβ, smul_smul]

/-- Cochrane (2023), p. 87 (survey E1): the printed line `Δ_{t+1}∑βʲ s_{t+j} = a(β)ε_{t+1}`
holds in a state iff `(1 − β) a(β) ε_{t+1} = 0`; for `β < 1` iff `a(β) = 0` or there is no
shock. -/
theorem printed_exact_line_iff {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (pv β s t) ω = gen a β * ε ((t : ℤ) + 1) ω ↔
      gen a β = 0 ∨ ε ((t : ℤ) + 1) ω = 0 := by
  rw [printed_exact_line 𝔼 hβ hs hε hM, Pi.smul_apply, smul_eq_mul]
  have h1 : 1 - β ≠ 0 := by
    have := le_abs_self β
    intro h; linarith
  constructor
  · intro h
    have : (1 - β) * (gen a β * ε ((t : ℤ) + 1) ω) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd h2 h1
    · exact mul_eq_zero.1 h2
  · rintro (h | h) <;> simp [h]

/-- Cochrane (2023), p. 87 (survey E1, counterexample): for the i.i.d. coin-flip surplus
`s_t = ε_t` (`a(β) = 1`) and `β = 1/2`, `Δ_1 ∑ βʲ s_j = 1/2` in the state where the first coin is
heads, whereas the printed formula gives `a(β) ε_1 = 1`. -/
theorem printed_exact_line_counterexample :
    innov ExpectationsFiniteTree.coinSystem 0 (pv (1 / 2) (fun t => coinShockZ t) 0)
        (true, true) = 1 / 2 ∧
      gen iidCoeff (1 / 2) * coinShockZ ((0 : ℕ) + 1) (true, true) = 1 := by
  have hβ : |(1 / 2 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have h := printed_exact_line ExpectationsFiniteTree.coinSystem hβ (isMA_iid coinShockZ)
    coinShockZ_isMDS coinShockZ_bounded 0
  have h1 : coinShockZ ((0 : ℕ) + 1) (true, true) = 1 := by
    simpa using coinShockZ_one
  refine ⟨?_, by rw [gen_iid, h1, one_mul]⟩
  rw [h, Pi.smul_apply, smul_eq_mul, gen_iid, h1]
  norm_num

/-- Cochrane (2023), eq. (4.8), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
Δ_{t+1} s_{t+1} + β Δ_{t+1}(B_{t+1}/P_{t+2})`. -/
theorem exact_innov_flow (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hsa : 𝔼.Adapted s) {K : ℝ} (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s)
    (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) =
      innov 𝔼 t (s (t + 1)) + β • innov 𝔼 t (realDebt B P (t + 1)) := by
  have hknown : 𝔼.E (t + 1) (realDebtEnd B P t) = realDebtEnd B P t :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hBP t)
  have hlhs : realDebtEnd B P t * innov 𝔼 t (deflation P t) = innov 𝔼 t (realDebt B P t) := by
    rw [realDebt_eq_mul hP, innov_apply, innov_apply, hpull (t + 1) _ _ hknown,
      hpull t _ _ (hBP t), mul_sub]
  rw [hlhs, exact_flow_of_valuation 𝔼 hpull hβ hP hBP hsa hsb hval t,
    revenue_eq 𝔼 hpull hP hBP, map_add, map_smul, innov_E_of_le 𝔼 le_rfl]

/-- Cochrane (2023), eq. (4.9), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
Δ_{t+1} s_{t+1} + β Δ_{t+1} ∑_{j ≥ 0} βʲ s_{t+2+j}`. -/
theorem exact_innov_flow_pv (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hsa : 𝔼.Adapted s) {K : ℝ} (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s)
    (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) =
      innov 𝔼 t (s (t + 1)) + β • innov 𝔼 t (pv β s (t + 1 + 1)) := by
  rw [exact_innov_flow 𝔼 hpull hβ hP hBP hsa hsb hval t, hval (t + 1),
    innov_E_of_le 𝔼 (Nat.le_succ (t + 1))]

/-- Cochrane (2023), eq. (4.10), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
ε_{t+1} + [a(β) − 1] ε_{t+1}`; the second term is the revenue from bond sales. -/
theorem exact_innov_flow_ma (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (s (t + 1)) = ε ((t : ℤ) + 1) ∧
      β • innov 𝔼 t (pv β s (t + 1 + 1)) = (gen a β - 1) • ε ((t : ℤ) + 1) := by
  have hv := (isMA_iff_vec a ε s).1 hs
  have hsa := adapted_MAVec 𝔼 hv (isMDSVec_of_isMDS 𝔼 hε) (fun k _ ω => hM k ω)
  have hsb := fun t ω => abs_MAVec_le hv (fun k _ ω => hM k ω) t ω
  have h1 := exact_innov_flow_pv 𝔼 hpull hβ hP hBP hsa hsb hval t
  have h2 := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
  have h3 := innov_MA_zero 𝔼 hs hε hM ha0 t
  refine ⟨h3, ?_⟩
  rw [h2.1, h2.2, h3] at h1
  rw [sub_smul, one_smul, h1]
  abel

/-- Cochrane (2023), p. 91: the innovation in real revenue from bond sales at the end of
`t + 1` is `Δ_{t+1}(Q_{t+1}B_{t+1}/P_{t+1}) = [a(β) − 1] ε_{t+1}`. -/
theorem revenue_innov (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) =
      (gen a β - 1) • ε ((t : ℤ) + 1) := by
  rw [revenue_eq 𝔼 hpull hP hBP, map_smul, innov_E_of_le 𝔼 le_rfl, hval (t + 1),
    innov_E_of_le 𝔼 (Nat.le_succ (t + 1))]
  exact (exact_innov_flow_ma 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t).2

/-- Cochrane (2023), p. 91: "If `a(β) = 0`, that extra revenue completely finances the
deficit": the revenue innovation is `−ε_{t+1} = −Δs_{t+1}` and there is no inflation surprise. -/
theorem financing_by_debt (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h0 : gen a β = 0)
    (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) = -innov 𝔼 t (s (t + 1)) ∧
      realDebtEnd B P t * innov 𝔼 t (deflation P t) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, h0, innov_MA_zero 𝔼 hs hε hM ha0]
    simp
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, h0, zero_smul]

/-- Cochrane (2023), p. 91: "if `a(β) = a_0 = 1`, then the government gets no additional
revenue from bond sales. The extra deficit is entirely financed by inflating away outstanding
debt": revenue innovation zero, `(B_t/P_t)Δ(P_t/P_{t+1}) = ε_{t+1}`. -/
theorem financing_by_inflation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h1 : gen a β = 1)
    (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) = 0 ∧
      realDebtEnd B P t * innov 𝔼 t (deflation P t) = ε ((t : ℤ) + 1) := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, h1, sub_self, zero_smul]
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, h1, one_smul]

/-- Cochrane (2023), p. 91: "if `a(β) > 1`, then the government raises less revenue from
selling bonds": after a deficit shock `ε_{t+1} < 0` the revenue innovation is negative and the
devaluation `(B_t/P_t)Δ(P_t/P_{t+1})` exceeds the deficit. -/
theorem financing_superinflation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h1 : 1 < gen a β)
    (t : ℕ) (ω : Ω) (hneg : ε ((t : ℤ) + 1) ω < 0) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) ω < 0 ∧
      (realDebtEnd B P t * innov 𝔼 t (deflation P t)) ω < ε ((t : ℤ) + 1) ω := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, Pi.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (by linarith) hneg
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, Pi.smul_apply, smul_eq_mul]
    nlinarith

end Cochrane.DebtDeficitsInflation.SurplusMA

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stylised facts and the reasonableness of an s-shaped surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2.5–§4.2.6, pp. 94–97.

## Main results

* §4.2.5, "the phenomena are tied together". In the simple model, unexpected inflation, the
  debt response and the return innovation are all fixed multiples of the surplus shock with
  the single number `a(ρ)` (`tied_together`). `a(ρ)` is identified from second moments: from
  the inflation–surplus covariance and from the relative volatility of inflation and surpluses
  (`gen_identified`), and from the debt–surplus covariance (`gen_identified_debt`). These are
  the "indirect estimates" of p. 94.
* §4.2.6, p. 95: a borrower who must not inflate or default needs `a(ρ) = 0`
  (`no_inflation_iff_gen_zero`). In the exact model, raising revenue from bond sales after a
  deficit requires promising higher subsequent surpluses (`revenue_rises_iff`).
* §4.2.6, p. 96: with the debt-feedback surplus `s̃_{t+1} = αv_t + u_{s,t+1}` and
  `ρv_{t+1} = v_t − s̃_{t+1}` (no inflation, constant return), surpluses are fully repaid,
  `∑ ρʲ Δ_{t+1}s̃_{t+1+j} = 0`, i.e. `a_s(ρ) = 0` (`feedback_full_repayment`). This holds
  even when the disturbance is a persistent AR(1) with `a_u(ρ) = 1/(1 − ρη) > 1`
  (`ar1_innov_sum`, `feedback_repaid_despite_persistent_u`). Supporting lemmas:
  `fbValue`, `fbSurplus`, `fbValue_bounded`, `fbValue_adapted`, `fb_flow`, `fb_innov_surplus`.
  The book's further remark that this specification is "compatible with active fiscal
  policy" (survey E10) is a Chapter 5 statement and is not treated here.
-/

namespace Cochrane.DebtDeficitsInflation.SurplusProcessFacts

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §4.2.5: the facts are tied together by `a(ρ)` -/

/-- Cochrane (2023), §4.2.5, p. 94 ("These phenomena are tied together"): in the simple model,
unexpected inflation, the debt response and the ex-post return innovation are all
determined by the single number `a(ρ)`:
`Δπ = −a(ρ)ε`, `ρΔv = (a(ρ) − 1)ε`, `Δr = a(ρ)ε`. -/
theorem tied_together {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen a ρ • ε ((t : ℤ) + 1) ∧
      ρ • innov 𝔼 t (v (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) ∧
      innov 𝔼 t (r (t + 1)) = gen a ρ • ε ((t : ℤ) + 1) :=
  ⟨innov_infl_eq 𝔼 hm hT hs hε hM hρ t, rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t,
    (innov_return 𝔼 hm hT hs hε hM hρ t).2⟩

/-- Cochrane (2023), §4.2.5, p. 94 ("the indirect estimate of `a(ρ)` coming from the relative
volatility of inflation and surpluses"): whenever the shock has non-zero conditional variance,
`a(ρ) = −E_t[Δπ ε]/E_t[ε²]` and `a(ρ)² = E_t[(Δπ)²]/E_t[ε²]`. -/
theorem gen_identified {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) (hvar : 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω ≠ 0) :
    gen a ρ = -𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) ω /
        𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω ∧
      gen a ρ ^ 2 = 𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω ^ 2) ω /
        𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω := by
  rw [condCov_innov_infl 𝔼 hm hT hs hε hM hρ, condVar_innov_infl 𝔼 hm hT hs hε hM hρ]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor <;> field_simp

/-- Cochrane (2023), §4.2.5, p. 94 ("the correlation between surpluses and debt"): the
conditional covariance of the debt innovation with the surplus shock identifies `a(ρ)`,
`ρ E_t[Δv_{t+1} ε_{t+1}] = (a(ρ) − 1) E_t[ε²_{t+1}]`. -/
theorem gen_identified_debt {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    ρ • 𝔼.E t (fun ω => innov 𝔼 t (v (t + 1)) ω * ε ((t : ℤ) + 1) ω) =
      (gen a ρ - 1) • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  have h := rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t
  rw [← map_smul, ← map_smul]
  congr 1
  funext ω
  have hω := congrFun h ω
  simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
  rw [← mul_assoc, hω]
  ring

/-! ### §4.2.6: an s-shaped surplus process is reasonable -/

/-- Cochrane (2023), §4.2.6, p. 95 ("Governments under the gold standard, members of the euro,
... must follow a surplus process with `a(ρ) = 0` if they wish to avoid default"): in the simple
model, with a state in which the shock is non-zero, unexpected inflation (devaluation) is
ruled out at date `t + 1` iff `a(ρ) = 0`. -/
theorem no_inflation_iff_gen_zero {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (hne : ∃ ω, ε ((t : ℤ) + 1) ω ≠ 0) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔ gen a ρ = 0 := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ t]
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := hne
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul, neg_eq_zero] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hω
  · intro h
    rw [h, neg_zero, zero_smul]

/-- Cochrane (2023), §4.2.6, p. 95 ("wish to raise revenue from bond sales rather than just
drive down bond prices. To do so, they must credibly promise to raise subsequent surpluses"):
in the exact model, after a deficit shock `ε_{t+1} < 0`, the revenue from bond sales rises iff
`a(β) < 1`. Equivalently, the discounted value of subsequent surpluses
`β ∑ βʲ s_{t+2+j}` rises. -/
theorem revenue_rises_iff (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) (ω : Ω)
    (hneg : ε ((t : ℤ) + 1) ω < 0) :
    (0 < innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) ω ↔ gen a β < 1) ∧
      (0 < (β • innov 𝔼 t (pv β s (t + 1 + 1))) ω ↔ gen a β < 1) := by
  have h1 := revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t
  have h2 := (exact_innov_flow_ma 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t).2
  have key : 0 < (gen a β - 1) * ε ((t : ℤ) + 1) ω ↔ gen a β < 1 := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [h1, Pi.smul_apply, smul_eq_mul]; exact key
  · rw [h2, Pi.smul_apply, smul_eq_mul]; exact key

/-! ### §4.2.6, p. 96: surpluses that respond to debt are repaid -/

/-- Cochrane (2023), §4.2.6, p. 96: the value of debt under the debt-feedback surplus
`s̃_{t+1} = αv_t + u_{s,t+1}` and `ρv_{t+1} = v_t − s̃_{t+1}` (no inflation, constant return):
`v_{t+1} = ((1 − α)v_t − u_{t+1})/ρ`, from `v_0`. -/
noncomputable def fbValue (ρ α : ℝ) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => v0
  | t + 1 => ρ⁻¹ • ((1 - α) • fbValue ρ α v0 u t - u (t + 1))

/-- Cochrane (2023), §4.2.6, p. 96: the debt-feedback surplus `s̃_{t+1} = αv_t + u_{s,t+1}`
(the date-0 value is irrelevant). -/
noncomputable def fbSurplus (ρ α : ℝ) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => α • fbValue ρ α v0 u t + u (t + 1)

/-- Cochrane (2023), §4.2.6, p. 96: the debt-feedback model satisfies the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s̃_{t+1}` with `r = 0` (constant return, in deviations) and no
growth. -/
theorem fb_flow {ρ α : ℝ} (hρ : ρ ≠ 0) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) :
    Flow ρ (fbValue ρ α v0 u) (fun _ => 0) (fun _ => 0) (fbSurplus ρ α v0 u) := by
  intro t
  funext ω
  simp only [fbValue, fbSurplus, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §4.2.6, p. 96: if `|1 − α| < ρ` and the disturbance is bounded, the value
of debt is bounded (debt is stabilised by the surplus feedback). -/
theorem fbValue_bounded {ρ α : ℝ} (hρ : 0 < ρ) (hα : |1 - α| < ρ) {v0 : Ω → ℝ} {V0 : ℝ}
    (hv0 : ∀ ω, |v0 ω| ≤ V0) {u : ℕ → Ω → ℝ} {K : ℝ} (hu : ∀ t ω, |u t ω| ≤ K) :
    BoundedProc (fbValue ρ α v0 u) := by
  have hd : 0 < ρ - |1 - α| := by linarith
  set B := max V0 (K / (ρ - |1 - α|)) with hB
  refine ⟨B, fun t => ?_⟩
  induction t with
  | zero => intro ω; exact (hv0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    have hK : K / (ρ - |1 - α|) ≤ B := le_max_right _ _
    have hK' : K ≤ B * (ρ - |1 - α|) := by
      rwa [div_le_iff₀ hd] at hK
    simp only [fbValue, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]
    calc |(1 - α) * fbValue ρ α v0 u t ω - u (t + 1) ω|
        ≤ |1 - α| * |fbValue ρ α v0 u t ω| + |u (t + 1) ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ |1 - α| * B + K :=
          add_le_add (mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)) (hu _ ω)
      _ ≤ ρ * B := by nlinarith

/-- Cochrane (2023), §4.2.6, p. 96: with an adapted disturbance and `v_0` known at date 0, the
value of debt is adapted. -/
theorem fbValue_adapted {ρ α : ℝ} {v0 : Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.Adapted u) : 𝔼.Adapted (fbValue ρ α v0 u) := by
  intro t
  induction t with
  | zero => exact hv0
  | succ t ih =>
    simp only [fbValue]
    rw [map_smul, map_sub, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      hu (t + 1)]

/-- Cochrane (2023), §4.2.6, p. 96: the surplus innovation is the disturbance innovation,
`Δ_{t+1}s̃_{t+1} = Δ_{t+1}u_{s,t+1}` (the feedback term `αv_t` is known at `t`). -/
theorem fb_innov_surplus {ρ α : ℝ} {v0 : Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.Adapted u) (t : ℕ) :
    innov 𝔼 t (fbSurplus ρ α v0 u (t + 1)) = innov 𝔼 t (u (t + 1)) := by
  simp only [fbSurplus]
  rw [map_add, map_smul, innov_of_known 𝔼 (fbValue_adapted 𝔼 hv0 hu t), smul_zero, zero_add]

/-- Cochrane (2023), §4.2.6, p. 96 ("surpluses themselves `s_t` may be fully repaid with
`a_s(ρ) = 0`"): for `0 < ρ < 1`, `|1 − α| < ρ` and any bounded adapted disturbance, the
discounted sum of surplus innovations is zero, `∑_j ρʲ Δ_{t+1} s̃_{t+1+j} = 0`. -/
theorem feedback_full_repayment {ρ α : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : |1 - α| < ρ)
    {v0 : Ω → ℝ} {V0 : ℝ} (hv0b : ∀ ω, |v0 ω| ≤ V0) (hv0 : 𝔼.E 0 v0 = v0)
    {u : ℕ → Ω → ℝ} {K : ℝ} (hub : ∀ t ω, |u t ω| ≤ K) (hu : 𝔼.Adapted u) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j * innov 𝔼 t (fbSurplus ρ α v0 u (t + 1 + j)) ω) 0 := by
  obtain ⟨B, hB⟩ := fbValue_bounded hρ0 hα hv0b hub
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have h0 := rec_seriesTo_map (innov 𝔼 t)
    ((flow_iff_recursion ρ _ _ _ _).1 (fb_flow (α := α) hρ0.ne' v0 u))
    (tvc_innov_of_bounded 𝔼 hρa hB t t ω)
  rw [innov_of_known 𝔼 (fbValue_adapted 𝔼 hv0 hu t)] at h0
  exact h0.congr (fun j => by simp) rfl

/-- Cochrane (2023), §4.2.6, p. 96 (`a_u(ρ) > 1` for a persistent disturbance): for an AR(1)
disturbance (`E_t u_{t+1} = η u_t`, `|ρη| < 1`),
`∑_j ρʲ Δ_{t+1}u_{t+1+j} = Δ_{t+1}u_{t+1}/(1 − ρη)`. -/
theorem ar1_innov_sum {ρ η : ℝ} (h : |ρ * η| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (u (t + 1 + j)) ω)
      (innov 𝔼 t (u (t + 1)) ω / (1 - ρ * η)) := by
  have hI : ∀ j, innov 𝔼 t (u (t + 1 + j)) ω = η ^ j * innov 𝔼 t (u (t + 1)) ω := by
    intro j
    have h1 : 𝔼.E (t + 1) (u (t + 1 + j)) = η ^ j • u (t + 1) := 𝔼.ar1_iterate hu (t + 1) j
    have h2 : 𝔼.E t (u (t + 1 + j)) = η ^ (j + 1) • u t := by
      rw [show t + 1 + j = t + (j + 1) by omega]; exact 𝔼.ar1_iterate hu t (j + 1)
    have h3 : 𝔼.E t (u (t + 1)) = η • u t := hu.2 t
    rw [innov_apply, innov_apply, Pi.sub_apply, Pi.sub_apply, h1, h2, h3, (hu.1 (t + 1))]
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring
  have h1 : 1 - ρ * η ≠ 0 := by
    intro h0
    have : ρ * η = 1 := by linarith
    rw [this, abs_one] at h
    exact lt_irrefl _ h
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (innov 𝔼 t (u (t + 1)) ω)
  convert this using 1
  · funext j
    rw [hI, mul_pow]
    ring
  · field_simp

/-- Cochrane (2023), §4.2.6, p. 96 ("surpluses themselves may be fully repaid with
`a_s(ρ) = 0`, even if `a_u(ρ) > 1`"): with a bounded AR(1) disturbance of persistence `η > 0`,
the disturbance's discounted innovation is `1/(1 − ρη) > 1` times its impact
(`a_u(ρ) > 1`), while the surplus's discounted innovation is zero (`a_s(ρ) = 0`), although
both share the same impact innovation. -/
theorem feedback_repaid_despite_persistent_u {ρ α η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα : |1 - α| < ρ) (hη0 : 0 < η) (hρη : |ρ * η| < 1) {v0 : Ω → ℝ} {V0 : ℝ}
    (hv0b : ∀ ω, |v0 ω| ≤ V0) (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ} {K : ℝ}
    (hub : ∀ t ω, |u t ω| ≤ K) (hu : 𝔼.IsAR1 η u) (t : ℕ) (ω : Ω) :
    1 < 1 / (1 - ρ * η) ∧
      HasSum (fun j => ρ ^ j * innov 𝔼 t (u (t + 1 + j)) ω)
        (1 / (1 - ρ * η) * innov 𝔼 t (u (t + 1)) ω) ∧
      SeriesTo (fun j => ρ ^ j * innov 𝔼 t (fbSurplus ρ α v0 u (t + 1 + j)) ω) 0 ∧
      innov 𝔼 t (fbSurplus ρ α v0 u (t + 1)) = innov 𝔼 t (u (t + 1)) := by
  have hpos : 0 < 1 - ρ * η := by linarith [le_abs_self (ρ * η)]
  refine ⟨?_, ?_, feedback_full_repayment 𝔼 hρ0 hρ1 hα hv0b hv0 hub hu.1 t ω,
    fb_innov_surplus 𝔼 hv0 hu.1 t⟩
  · rw [lt_div_iff₀ hpos, one_mul]
    nlinarith
  · have := ar1_innov_sum 𝔼 hρη hu t ω
    convert this using 1
    ring

end Cochrane.DebtDeficitsInflation.SurplusProcessFacts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The generalised Hansen–Roberds–Sargent identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2.7, eqs. (4.11)–(4.13),
pp. 97–98, and Online Appendix A2, §2.3, p. 606.

Every series has a vector moving-average representation in a common vector
martingale-difference shock `ε` (`π_t = a_π(L)'ε_t`, `s̃_t = a_s(L)'ε_t`, ...), and the
linearised identities of §3.5 hold. Here `a_r` is the moving average of the ex-post real return
INCLUDING its `j = 0` term, as in (4.12), (4.13) and A2 §2.3.

## Main results

* Survey E4 (p. 98): the line before (4.11), `Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}`,
  is false: its right-hand side is identically zero (`printed_rhs_eq_zero`), so it holds iff
  there is no unexpected inflation (`printed_line_iff`), and it fails in a genuine model
  (`printed_line_counterexample`). The correct statement is `innov_pi_vector`:
  `Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}`.
* (4.11) is an identity, not a repayment condition: `identity_4_11` (shock form, every model)
  and `identity_4_11_vec` (coefficient form, non-degenerate shocks); `identity_A2` (A2 §2.3,
  `0 = a_s(ρ) − a_r(ρ)`). The repayment condition (no unexpected inflation with one-period
  debt) is `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)`: `repayment_iff`, `repayment_iff_vec`; with
  constant expected returns and no growth it is `a_s(ρ) = 0`: `const_expected_return_coeffs`,
  `repayment_reduces`.
* (4.12): `identity_4_12`.
* Campbell–Shiller: `CSReturn`, `campbellShiller_finite`, `campbellShiller`,
  `campbellShiller_expected`; Campbell–Ammer (survey E5 corrected): `campbellAmmer`,
  `campbellAmmer_MA`; the printed display fails: `printed_campbellAmmer_counterexample`;
  (4.13): `identity_4_13`, `identity_4_13_vec`.
* A2 §2.3: the constant-discount-rate present value relation is not an identity
  (`pv_constant_discount_iff`: it holds iff the discounted expected returns sum to zero);
  with constant expected returns `a_r(ρ) = a_r(0)` (`const_discount_gen`).
-/

namespace Cochrane.DebtDeficitsInflation.GeneralizedHRS

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Algebra of `c'ε` -/

/-- Cochrane (2023), §4.2.7, p. 98: `(c + d)'ε = c'ε + d'ε`. -/
theorem dotShock_add {n : ℕ} (c d : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (c + d) ε k = dotShock c ε k + dotShock d ε k := by
  funext ω
  simp [dotShock, add_mul, Finset.sum_add_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: `(c − d)'ε = c'ε − d'ε`. -/
theorem dotShock_sub {n : ℕ} (c d : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (c - d) ε k = dotShock c ε k - dotShock d ε k := by
  funext ω
  simp [dotShock, sub_mul, Finset.sum_sub_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: `(−c)'ε = −c'ε`. -/
theorem dotShock_neg {n : ℕ} (c : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (-c) ε k = -dotShock c ε k := by
  funext ω
  simp [dotShock, Finset.sum_neg_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: the shocks at date `k` are non-degenerate: no non-zero
combination `c'ε_k` vanishes identically (so coefficient vectors are identified). -/
def Nondeg {n : ℕ} (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) : Prop :=
  ∀ c : Fin n → ℝ, dotShock c ε k = 0 → c = 0

/-- Cochrane (2023), §4.2.7, p. 98: for `|ρ| ≤ 1`, the innovation sum of a vector moving
average converges, `∑_j ρʲ Δ_{t+1} x_{t+1+j} = a_x(ρ)'ε_{t+1}`. -/
theorem seriesTo_innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j * innov 𝔼 t (x (t + 1 + j)) ω)
      (dotShock (genVec a ρ) ε ((t : ℤ) + 1) ω) :=
  seriesTo_of_hasSum (innov_PV_termwise_vec 𝔼 hx hε hM
    (fun i => summable_coeff_mul_pow (hx.1 i) hρ) t ω)

/-- Cochrane (2023), §4.2.7, p. 98 (sums from `j = 1`):
`∑_{j ≥ 1} ρʲ Δ_{t+1} x_{t+1+j} = [a_x(ρ) − a_x(0)]'ε_{t+1}`. -/
theorem seriesTo_innov_MAVec_succ {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (x (t + 2 + j)) ω)
      (dotShock (genVec a ρ - a 0) ε ((t : ℤ) + 1) ω) := by
  refine (seriesTo_succ_iff.1 (seriesTo_innov_MAVec 𝔼 hx hε hM hρ t ω)).congr
    (fun j => by rw [show t + 1 + (j + 1) = t + 2 + j by omega]) ?_
  rw [dotShock_sub, Pi.sub_apply, innov_MAVec 𝔼 hx hε hM t 0]
  simp

/-- Cochrane (2023), A2 §2.3, p. 606: the generating-function vector at `z = 0` is `a_0`. -/
theorem genVec_zero {n : ℕ} (a : ℕ → Fin n → ℝ) : genVec a 0 = a 0 := by
  funext i
  exact gen_zero _

/-! ### The corrected unexpected-inflation formula and (4.11) -/

/-- Cochrane (2023), §4.2.7, p. 98, corrected (survey E4): from (3.20),
`Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}` (for `|ρ| ≤ 1`). -/
theorem innov_pi_vector {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) - innov 𝔼 t (rn (t + 1)) =
      dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ - ar 0) ε ((t : ℤ) + 1) := by
  funext ω
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) (hT t ω)
    (seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω) (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω)
  have h2 := (seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω).unique h1
  simp only [dotShock_sub, dotShock_add, dotShock_neg, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), §4.2.7, p. 98, and A2 §2.3, p. 606 ((4.11) in shock form): under the flow
identity and the terminal condition, `[a_s(ρ) + a_g(ρ) − a_r(ρ)]'ε_{t+1} = 0` identically. -/
theorem identity_4_11 {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ}
    (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ}
    (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec as ρ + genVec ag ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  funext ω
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((flow_iff_recursion ρ v r g s).1 h) (hT t ω)
  rw [innov_of_known 𝔼 (hv t)] at h0
  have h1 := ((seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω).add
    (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω)).sub (seriesTo_innov_MAVec 𝔼 har hε hM hρ t ω)
  have h2 := h0.unique (h1.congr (fun j => by
    simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]; ring) rfl)
  simp only [dotShock_sub, dotShock_add, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), eq. (4.11), p. 98, coefficient form: with non-degenerate shocks,
`a_s(ρ) + a_g(ρ) = a_r(ρ)` holds as an identity (in every model satisfying the flow identity and
the terminal condition, whatever the inflation process). -/
theorem identity_4_11_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ}
    (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ}
    (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) : genVec as ρ + genVec ag ρ = genVec ar ρ := by
  have := hnd _ (identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t)
  rw [sub_eq_zero] at this
  exact this

/-- Cochrane (2023), A2 §2.3, p. 606: "`0 = a_s(ρ) − a_r(ρ)` ... is an identity" (no growth). -/
theorem identity_A2 {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec as ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have hg : IsMAVec (fun _ _ => (0 : ℝ)) ε (fun _ => 0) :=
    ⟨fun _ => by simp, fun t ω => by simp⟩
  have := identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t
  have hz : genVec (n := n) (fun _ _ => (0 : ℝ)) ρ = 0 := by
    funext i; simp [genVec, gen]
  rwa [hz, add_zero] at this

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): the printed right-hand side
`[−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}` is identically zero. -/
theorem printed_rhs_eq_zero {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g)
    (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have := identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t
  rw [show -genVec as ρ - genVec ag ρ + genVec ar ρ =
    -(genVec as ρ + genVec ag ρ - genVec ar ρ) by abel, dotShock_neg, this, neg_zero]

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): the printed line
`Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}` holds iff there is no unexpected inflation. -/
theorem printed_line_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g)
    (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) =
        dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ) ε ((t : ℤ) + 1) ↔
      innov 𝔼 t (infl (t + 1)) = 0 := by
  rw [printed_rhs_eq_zero 𝔼 hρ h hv hT hε hM hs hg har t]

/-- Cochrane (2023), §4.2.7, p. 98: with one-period debt (`rⁿ_{t+1}` known at `t`), no unexpected
inflation iff `[a_s(ρ) + a_g(ρ) − a_r(ρ) + a_r(0)]'ε_{t+1} = 0` (the correct "debt repayment"
condition, survey E4). -/
theorem repayment_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔
      dotShock (genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0) ε ((t : ℤ) + 1) = 0 := by
  have h1 := innov_pi_vector 𝔼 hρ h hr hv hT hε hM hs hg har t
  rw [innov_of_known 𝔼 hrn, sub_zero] at h1
  rw [h1, show genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0 =
    -(-genVec as ρ - genVec ag ρ + genVec ar ρ - ar 0) by abel, dotShock_neg, neg_eq_zero]

/-- Cochrane (2023), eq. (4.11), p. 98, corrected (survey E4): with non-degenerate shocks and
one-period debt, there is no unexpected inflation iff `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)`. -/
theorem repayment_iff_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) (hnd : Nondeg ε ((t : ℤ) + 1)) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔ genVec as ρ + genVec ag ρ = genVec ar ρ - ar 0 := by
  rw [repayment_iff 𝔼 hρ h hr hv hT hε hM hs hg har t hrn]
  constructor
  · intro h0
    have := hnd _ h0
    rw [← sub_eq_zero, ← this]
    abel
  · intro h0
    rw [show genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0 = 0 by rw [h0]; abel]
    funext ω
    simp [dotShock]

/-- Cochrane (2023), p. 98 ("the condition `a(ρ) = 0` is the special case ... of constant
expected returns"): with constant expected returns and non-degenerate shocks, the return has
no moving-average coefficients beyond `j = 0`. -/
theorem const_expected_return_coeffs {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ConstExpReturn 𝔼 r c)
    {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ar : ℕ → Fin n → ℝ} (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) (j : ℕ) : ar (j + 1) = 0 := by
  refine hnd _ ?_
  rw [← innov_MAVec 𝔼 har hε hM t (j + 1), show t + 1 + (j + 1) = t + 2 + j by omega]
  exact innov_future_return_zero 𝔼 hc t j

/-- Cochrane (2023), A2 §2.3, p. 606: with no return coefficients beyond `j = 0`,
`a_r(ρ) = a_r(0)`. -/
theorem const_discount_gen {n : ℕ} {ar : ℕ → Fin n → ℝ} (h : ∀ j, ar (j + 1) = 0) (ρ : ℝ) :
    genVec ar ρ = ar 0 := by
  funext i
  unfold genVec gen
  rw [tsum_eq_single 0 fun j hj => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [h k]]
  simp

/-- Cochrane (2023), p. 98: "The condition `a(ρ) = 0` is the special case of no growth ... and
of constant expected returns": then the repayment condition `a_s + a_g = a_r(ρ) − a_r(0)` is
`a_s(ρ) = 0`. -/
theorem repayment_reduces {n : ℕ} {as ar : ℕ → Fin n → ℝ} (h : ∀ j, ar (j + 1) = 0) (ρ : ℝ) :
    genVec as ρ + genVec (fun _ _ => (0 : ℝ)) ρ = genVec ar ρ - ar 0 ↔ genVec as ρ = 0 := by
  have hz : genVec (n := n) (fun _ _ => (0 : ℝ)) ρ = 0 := by
    funext i; simp [genVec, gen]
  rw [hz, const_discount_gen h, add_zero, sub_self]

/-! ### A genuine counterexample to the printed line -/

/-- Cochrane (2023), p. 98 (survey E4 counterexample): one coin-flip shock. -/
noncomputable def cxShock : ℤ → Fin 1 → Bool × Bool → ℝ := fun k _ => coinShockZ k

/-- Cochrane (2023), p. 98 (survey E4 counterexample): i.i.d. coefficients as a one-shock
vector. -/
def cxCoeff (j : ℕ) (_ : Fin 1) : ℝ := iidCoeff j

/-- Cochrane (2023), p. 98 (survey E4 counterexample): the i.i.d. surplus `s_t = ε_t`, which is
also the ex-post real return. -/
noncomputable def cxSurplus : ℕ → Bool × Bool → ℝ := fun t => coinShockZ t

/-- Cochrane (2023), p. 98 (survey E4 counterexample): `cxSurplus` is a one-shock vector moving
average with i.i.d. coefficients. -/
theorem cx_isMAVec : IsMAVec cxCoeff cxShock cxSurplus :=
  (isMA_iff_vec iidCoeff coinShockZ (fun t => coinShockZ t)).1 (isMA_iid coinShockZ)

/-- Cochrane (2023), p. 98 (survey E4/E5 counterexamples): the date-1 innovations of the
coin-flip surplus after heads, `Δ_1 s_k = 1` if `k = 1` and `0` otherwise. -/
theorem cx_innov_shock (k : ℕ) :
    innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus k) (true, true) =
      if k = 1 then 1 else 0 := by
  have h := congrFun (innov_shock ExpectationsFiniteTree.coinSystem coinShockZ_isMDS 0 k)
    (true, true)
  simp only [cxSurplus]
  rw [h]
  by_cases hk : k = 1
  · subst hk
    simpa using coinShockZ_one
  · have : (k : ℤ) ≠ ((0 : ℕ) : ℤ) + 1 := by push_cast; omega
    simp [hk]

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): a genuine model in which the printed line
fails. Take the coin-flip shock, the i.i.d. surplus `s_t = ε_t`, zero value of debt and growth,
the ex-post real return `r_t = ε_t`, a zero nominal rate and inflation `π_t = −ε_t`. Then the
flow identity holds, `a_s(ρ) = a_r(ρ) = 1`, `a_g = 0`, so the printed right-hand side
`[−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_1` is `0`, while `Δ_1π_1 = −1` after heads. -/
theorem printed_line_counterexample (ρ : ℝ) :
    Flow ρ (fun _ => 0) cxSurplus (fun _ => 0) cxSurplus ∧
      (∀ t, cxSurplus t = (fun _ => 0) t - (fun t => -cxSurplus t) t) ∧
      IsMAVec cxCoeff cxShock cxSurplus ∧
      innov ExpectationsFiniteTree.coinSystem 0 (-cxSurplus (0 + 1)) (true, true) = -1 ∧
      dotShock (-genVec cxCoeff ρ - genVec (fun _ _ => (0 : ℝ)) ρ + genVec cxCoeff ρ) cxShock
        ((0 : ℕ) + 1) (true, true) = 0 := by
  refine ⟨fun t => by funext ω; simp, fun t => by funext ω; simp, cx_isMAVec, ?_, ?_⟩
  · rw [map_neg, Pi.neg_apply, cx_innov_shock]
    simp
  · simp [dotShock, genVec, gen]

/-! ### (4.12) -/

/-- Cochrane (2023), eq. (4.12), p. 98: with geometric-maturity debt (`|ω| ≤ 1`),
`a_π(ω)'ε_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(ω)]'ε_{t+1}` (the `j = 0` terms cancel), where
`∑_j ωʲ Δ_{t+1}π_{t+1+j} = a_π(ω)'ε_{t+1}`. -/
theorem identity_4_12 {ρ om : ℝ} (hρ : |ρ| ≤ 1) (hom : |om| ≤ 1)
    {v r rn infl g s q : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hb : BondReturn om q rn) (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) (hT : InnovTVC 𝔼 ρ v)
    (hTq : ∀ t ω, Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar ap : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (hp : IsMAVec ap ε infl) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω)
        (dotShock (genVec ap om) ε ((t : ℤ) + 1) ω) ∧
      dotShock (genVec ap om) ε ((t : ℤ) + 1) =
        dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ - genVec ar om) ε ((t : ℤ) + 1) := by
  have hP := seriesTo_innov_MAVec 𝔼 hp hε hM hom t
  refine ⟨hP ω, ?_⟩
  funext ω'
  have h1 := weighted_inflation_identity 𝔼 h hr hb hv hq (hT t ω') (hTq t ω')
    (seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω') (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω')
    (hP ω')
  have h2 := ((seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω').sub
    (seriesTo_innov_MAVec_succ 𝔼 har hε hM hom t ω')).unique
    (h1.congr (fun j => by ring) rfl)
  simp only [dotShock_sub, dotShock_add, dotShock_neg, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply] at h2 ⊢
  linarith

/-! ### Campbell–Shiller and Campbell–Ammer -/

/-- Cochrane (2023), p. 98 (Campbell and Shiller 1988): the linearised return identity
`r_{t+1} = ρ (p − d)_{t+1} − (p − d)_t + Δd_{t+1}` (variables in deviations from constants),
with `pd` the log price–dividend ratio and `dd` log dividend growth. -/
def CSReturn (ρ : ℝ) (pd dd r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, r (t + 1) = ρ • pd (t + 1) - pd t + dd (t + 1)

/-- Cochrane (2023), p. 98: the Campbell–Shiller identity is the valuation recursion with payoff
`Δd − r`. -/
theorem csReturn_iff_recursion (ρ : ℝ) (pd dd r : ℕ → Ω → ℝ) :
    CSReturn ρ pd dd r ↔ Recursion ρ pd (fun t => dd t - r t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Cochrane (2023), p. 98 (Campbell–Shiller, finite horizon, ex post):
`p_t − d_t = ∑_{j=1}^{T} ρ^{j−1}(Δd_{t+j} − r_{t+j}) + ρᵀ(p − d)_{t+T}`. -/
theorem campbellShiller_finite {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (t T : ℕ) :
    pd t = ∑ j ∈ Finset.range T, ρ ^ j • (dd (t + 1 + j) - r (t + 1 + j)) +
      ρ ^ T • pd (t + T) :=
  rec_finite ((csReturn_iff_recursion ρ pd dd r).1 h) t T

/-- Cochrane (2023), p. 98 (Campbell and Shiller 1988): ex post, under `ρᵀ(p − d)_{t+T} → 0`,
`p_t − d_t = ∑_{j ≥ 1} ρ^{j−1}(Δd_{t+j} − r_{t+j})`. -/
theorem campbellShiller {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * pd (t + T) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * (dd (t + 1 + j) ω - r (t + 1 + j) ω)) (pd t ω) :=
  rec_seriesTo_map LinearMap.id ((csReturn_iff_recursion ρ pd dd r).1 h) hT

/-- Cochrane (2023), p. 98: the Campbell–Shiller identity in expectation,
`p_t − d_t = E_t ∑_{j ≥ 1} ρ^{j−1}(Δd_{t+j} − r_{t+j})` under `ρᵀ E_t(p − d)_{t+T} → 0`. -/
theorem campbellShiller_expected {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (hpd : 𝔼.Adapted pd) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (pd (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (dd (t + 1 + j) - r (t + 1 + j)) ω) (pd t ω) := by
  have h0 := rec_seriesTo_map (𝔼.E t) ((csReturn_iff_recursion ρ pd dd r).1 h) hT
  rwa [hpd t] at h0

/-- Cochrane (2023), p. 98, corrected (survey E5; Campbell and Ammer 1993):
`Δ_{t+1} r_{t+1} = Δ_{t+1} ∑_{j ≥ 1} ρ^{j−1} Δd_{t+j} − Δ_{t+1} ∑_{j ≥ 2} ρ^{j−1} r_{t+j}`: if the
dividend-news sum converges to `D`, the return-news sum `∑_{j≥0} ρ^{j+1}Δ_{t+1}r_{t+2+j}`
converges to `D − Δ_{t+1}r_{t+1}`. -/
theorem campbellAmmer {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (hpd : 𝔼.Adapted pd) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (pd (t + T)) ω) atTop (𝓝 0)) {D : ℝ}
    (hD : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (dd (t + 1 + j)) ω) D) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (D - innov 𝔼 t (r (t + 1)) ω) := by
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((csReturn_iff_recursion ρ pd dd r).1 h) hT
  rw [innov_of_known 𝔼 (hpd t)] at h0
  have hR : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (r (t + 1 + j)) ω) (D - 0) :=
    hD.sub h0 |>.congr (fun j => by simp only [map_sub, Pi.sub_apply]; ring) rfl
  refine (seriesTo_succ_iff.1 hR).congr (fun j => ?_) (by simp)
  rw [show t + 1 + (j + 1) = t + 2 + j by omega]

/-- Cochrane (2023), p. 98 (Campbell–Ammer in moving-average form):
`Δ_{t+1} r_{t+1} = {a_d(ρ) − [a_r(ρ) − a_r(0)]}'ε_{t+1}` (for `|ρ| ≤ 1`). -/
theorem campbellAmmer_MA {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (r (t + 1)) = dotShock (genVec ad ρ - (genVec ar ρ - ar 0)) ε ((t : ℤ) + 1) := by
  funext ω
  have h1 := campbellAmmer 𝔼 h hpd (hT t ω) (seriesTo_innov_MAVec 𝔼 hd hε hM hρ t ω)
  have h2 := (seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω).unique h1
  simp only [dotShock_sub, Pi.sub_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), eq. (4.13), p. 98: `0 = [a_d(ρ) − a_r(ρ)]'ε_{t+1}`, an identity
generalising the Hansen–Roberds–Sargent test to time-varying expected returns. -/
theorem identity_4_13 {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec ad ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have h1 := campbellAmmer_MA 𝔼 hρ h hpd hT hε hM hd har t
  rw [innov_MAVec 𝔼 har hε hM t 0] at h1
  have h2 : dotShock (genVec ad ρ - genVec ar ρ) ε ((t : ℤ) + 1) =
      dotShock (genVec ad ρ - (genVec ar ρ - ar 0)) ε ((t : ℤ) + 1) - dotShock (ar 0) ε
        ((t : ℤ) + 1) := by
    rw [← dotShock_sub]
    congr 1
    abel
  rw [h2, ← h1]
  simp

/-- Cochrane (2023), eq. (4.13), p. 98, coefficient form: with non-degenerate shocks,
`a_d(ρ) = a_r(ρ)`. -/
theorem identity_4_13_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) : genVec ad ρ = genVec ar ρ :=
  sub_eq_zero.1 (hnd _ (identity_4_13 𝔼 hρ h hpd hT hε hM hd har t))

/-- Cochrane (2023), p. 98: the printed Campbell–Ammer right-hand side,
`Δ_{t+1}∑_{j≥1}ρ^{j−1}Δd_{t+1} − Δ_{t+1}∑_{j≥2}ρ^{j−1}Δr_{t+j}` (with
`Δr_{t+j} = r_{t+j} − r_{t+j−1}`, as typeset). -/
noncomputable def printedCampbellAmmer (ρ : ℝ) (dd r : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j : ℕ, ρ ^ j * innov 𝔼 t (dd (t + 1)) ω -
    ∑' j : ℕ, ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j) - r (t + 1 + j)) ω

/-- Cochrane (2023), p. 98 (survey E5 counterexample): with i.i.d. coin-flip dividend growth and
returns `Δd_t = r_t = ε_t`, a constant price–dividend ratio and `ρ = 1/2`, the Campbell–Shiller
identity holds and `Δ_1 r_1 = 1` after heads, but the printed display gives `5/2`. -/
theorem printed_campbellAmmer_counterexample :
    CSReturn (1 / 2) (fun _ => 0) cxSurplus cxSurplus ∧
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 1)) (true, true) = 1 ∧
      printedCampbellAmmer ExpectationsFiniteTree.coinSystem (1 / 2) cxSurplus cxSurplus 0
        (true, true) = 5 / 2 := by
  have hsh := cx_innov_shock
  refine ⟨fun t => by funext ω; simp, by simpa using hsh 1, ?_⟩
  unfold printedCampbellAmmer
  have h1 : ∀ j : ℕ, (1 / 2 : ℝ) ^ j *
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 1)) (true, true) =
      (1 / 2 : ℝ) ^ j := fun j => by rw [hsh]; simp
  have h2 : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 2 + j) - cxSurplus (0 + 1 + j))
        (true, true) = if j = 0 then -(1 / 2) else 0 := fun j => by
    rw [map_sub, Pi.sub_apply, hsh, hsh]
    rcases j with _ | j
    · norm_num
    · simp only [show 0 + 2 + (j + 1) ≠ 1 by omega, show 0 + 1 + (j + 1) ≠ 1 by omega,
        ↓reduceIte, sub_self, mul_zero, Nat.add_one_ne_zero]
  simp_rw [h1, h2]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num), tsum_ite_eq]
  norm_num

/-! ### A2 §2.3: what can and cannot be tested -/

/-- Cochrane (2023), A2 §2.3, p. 606 ("The present value relation in a model with a constant
discount rate is not an identity"): under the flow identity (no growth) and the terminal
condition, `v_t = E_t ∑ ρʲ s̃_{t+1+j}` holds iff the discounted expected returns sum to zero. -/
theorem pv_constant_discount_iff {ρ : ℝ} {v r s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) {S : ℝ}
    (hS : SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) S) :
    v t ω = S ↔ SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) 0 := by
  have hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have hR := pv_expected 𝔼 h hv hT hS hG
  constructor
  · intro hvS
    exact hR.congr (fun _ => rfl) (by rw [hvS]; ring)
  · intro h0
    have := h0.unique hR
    linarith

end Cochrane.DebtDeficitsInflation.GeneralizedHRS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Present-value examples

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A2, §2.1, pp. 603–604:
the classic present-value calculations whose "100% R²" predictions the book uses to show how
not to test present-value relations.

## Main results

* Dividend AR(1): `dividend_pv` (`E_t ∑_{j≥1} βʲ d_{t+j} = βρ_d d_t/(1 − βρ_d)`, termwise) and
  `dividend_pv_E` (`E_t` of the infinite sum, bounded dividends).
* Permanent income: `pih_consumption`
  (`c_t − c_{t−1} = rβ(y_t − ρ_y y_{t−1})/(1 − βρ_y)`).
* AR(1) surplus lines of p. 604: `surplus_pv_ar1` (`v_t = E_t ∑ ρʲ s_{t+1+j} = η s_t/(1 − ρη)`),
  `innov_infl_ar1` (`Δπ_{t+1} = −a(ρ)ε_{t+1} = −(s_{t+1} − ηs_t)/(1 − ρη)`); survey E15: the
  printed denominator `1 − βη` is right only when `β = ρ` (`printed_p604_iff`).
-/

namespace Cochrane.DebtDeficitsInflation.PresentValueExamples

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), A2 p. 603: with AR(1) dividends (`E_t d_{t+1} = ρ_d d_t`) and
`|βρ_d| < 1`, `E_t ∑_{j ≥ 1} βʲ d_{t+j} = βρ_d d_t / (1 − βρ_d)` (series of conditional
expectations). -/
theorem dividend_pv {β ρd : ℝ} (h : |β * ρd| < 1) {d : ℕ → Ω → ℝ} (hd : 𝔼.IsAR1 ρd d)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ (j + 1) * 𝔼.E t (d (t + 1 + j)) ω) (β * ρd * d t ω / (1 - β * ρd)) := by
  have hE : ∀ j, 𝔼.E t (d (t + 1 + j)) ω = ρd ^ (j + 1) * d t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hd]
    rfl
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (β * ρd * d t ω)
  convert this using 1
  · funext j
    rw [hE, mul_pow, pow_succ, pow_succ]
    ring
  · have h1 : 1 - β * ρd ≠ 0 := by
      intro h0
      have : β * ρd = 1 := by linarith
      rw [this, abs_one] at h
      exact lt_irrefl _ h
    field_simp

/-- Cochrane (2023), A2 p. 603: the same present value as the conditional expectation of the
infinite sum, `E_t ∑_{j ≥ 1} βʲ d_{t+j} = βρ_d d_t/(1 − βρ_d)`, for bounded dividends and
`|β| < 1`, `|βρ_d| < 1`. -/
theorem dividend_pv_E {β ρd : ℝ} (hβ : |β| < 1) (h : |β * ρd| < 1) {d : ℕ → Ω → ℝ}
    (hd : 𝔼.IsAR1 ρd d) {K : ℝ} (hK : ∀ t ω, |d t ω| ≤ K) (t : ℕ) :
    𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * d (t + 1 + j) ω) =
      fun ω => β * ρd * d t ω / (1 - β * ρd) := by
  funext ω
  have hgeo : Summable fun j : ℕ => |β ^ (j + 1)| := by
    have := (summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_left |β|
    refine this.congr fun j => ?_
    rw [abs_pow, pow_succ]
    ring
  rw [E_tsum_abs 𝔼 hgeo (x := fun j ω' => d (t + 1 + j) ω') (fun j ω' => hK _ ω') t ω]
  exact (dividend_pv 𝔼 h hd t ω).tsum_eq

/-- Cochrane (2023), A2 p. 603 (the permanent-income model): if
`c_{t+1} = c_t + rβ ∑_{j ≥ 0} βʲ (E_{t+1} − E_t) y_{t+1+j}` and income is an AR(1)
(`E_t y_{t+1} = ρ_y y_t`), then `c_{t+1} − c_t = rβ (y_{t+1} − ρ_y y_t)/(1 − βρ_y)` (an exact,
"100% R²" relation). -/
theorem pih_consumption {β ρy rr : ℝ} (h : |β * ρy| < 1) {y c : ℕ → Ω → ℝ}
    (hy : 𝔼.IsAR1 ρy y)
    (hc : ∀ t ω, c (t + 1) ω = c t ω + rr * β * ∑' j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω)
    (t : ℕ) (ω : Ω) :
    c (t + 1) ω - c t ω = rr * β * (y (t + 1) ω - ρy * y t ω) / (1 - β * ρy) := by
  have hterm : ∀ j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω =
      (y (t + 1) ω - ρy * y t ω) * (β * ρy) ^ j := by
    intro j
    rw [innov_apply, Pi.sub_apply, show t + 1 + j = (t + 1) + j by omega, 𝔼.ar1_iterate hy,
      show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hy, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, mul_pow, pow_succ]
    ring
  have hsum : ∑' j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω =
      (y (t + 1) ω - ρy * y t ω) / (1 - β * ρy) := by
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one h, div_eq_mul_inv]
  rw [hc t ω, hsum]
  ring

/-- Cochrane (2023), A2 p. 604 (and (4.5), p. 89): with an AR(1) surplus and `|ρη| < 1`,
`E_t ∑_{j ≥ 0} ρʲ s_{t+1+j} = η s_t/(1 − ρη)`. -/
theorem surplus_pv_ar1 {ρ η : ℝ} (h : |ρ * η| < 1) {s : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 η s)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (η * s t ω / (1 - ρ * η)) := by
  have hE : ∀ j, 𝔼.E t (s (t + 1 + j)) ω = η ^ (j + 1) * s t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hs]
    rfl
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (η * s t ω)
  convert this using 1
  · funext j
    rw [hE, mul_pow]
    ring
  · have h1 : 1 - ρ * η ≠ 0 := by
      intro h0
      have : ρ * η = 1 := by linarith
      rw [this, abs_one] at h
      exact lt_irrefl _ h
    field_simp

/-- Cochrane (2023), A2 p. 604, corrected (survey E15): in the simple model with an AR(1)
surplus (moving-average coefficients `ηʲ`), `Δ_{t+1}π_{t+1} = −a(ρ)ε_{t+1} =
−(s_{t+1} − η s_t)/(1 − ρη)`. -/
theorem innov_infl_ar1 {ρ c η : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℤ → Ω → ℝ}
    (hs : IsMA (fun j => η ^ j) ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (hρη : |ρ * η| < 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen (fun j => η ^ j) ρ • ε ((t : ℤ) + 1) ∧
      innov 𝔼 t (infl (t + 1)) = fun ω => -(s (t + 1) ω - η * s t ω) / (1 - ρ * η) := by
  have h1 := innov_infl_eq 𝔼 hm hT hs hε hM hρ t
  refine ⟨h1, ?_⟩
  rw [h1, gen_ar1 hρη, ar1_of_MA hs hM t]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  ring

/-- Cochrane (2023), A2 p. 604 (survey E15): the printed `−(s_{t+1} − η_s s_t)/(1 − βη_s)` equals
unexpected inflation, in a state with a non-zero shock and for `η ≠ 0`, iff `β = ρ`. -/
theorem printed_p604_iff {ρ c η β : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℤ → Ω → ℝ}
    (hs : IsMA (fun j => η ^ j) ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (hρη : |ρ * η| < 1) (hβη : 1 - β * η ≠ 0) (hη : η ≠ 0) (t : ℕ) (ω : Ω)
    (hne : ε ((t : ℤ) + 1) ω ≠ 0) :
    innov 𝔼 t (infl (t + 1)) ω = -(s (t + 1) ω - η * s t ω) / (1 - β * η) ↔ β = ρ := by
  have h1 := congrFun (innov_infl_ar1 𝔼 hm hT hs hε hM hρ hρη t).2 ω
  have he : s (t + 1) ω - η * s t ω = ε ((t : ℤ) + 1) ω := by
    have := congrFun (ar1_of_MA hs hM t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hρη' : 1 - ρ * η ≠ 0 := by
    intro h0
    have : ρ * η = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  rw [h1, he]
  constructor
  · intro h2
    rw [div_eq_div_iff hρη' hβη] at h2
    have h3 : ε ((t : ℤ) + 1) ω * ((β - ρ) * η) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hne
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · linarith
      · exact absurd h5 hη
  · rintro rfl
    rfl

end Cochrane.DebtDeficitsInflation.PresentValueExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# VAR identities: Neumann sums, the inflation decompositions and the PV tautology

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3–4.4, pp. 99–116, and
Online Appendix Chapter 2, §2.2, pp. 604–605.

The terms of the inflation decompositions (4.14)–(4.16) are sums of VAR impulse-response
functions, computed with matrix Neumann series; and with the value of debt in the VAR, the
present-value relation (2.26) is an identity (A2, (2.24)–(2.26)).

## Main definitions

* `innov 𝔼 t x` (from `Innovations`): the innovation (news) operator
  `Δ_{t+1} x = E_{t+1} x − E_t x` (the book's `ΔE_{t+1}`).
* `IsVAR A z ε`: the VAR (4.17) `z_{t+1} = A z_t + ε_{t+1}` with random-variable coordinates;
  `ShockMDS 𝔼 ε`: the shocks are adapted and unforecastable; `obs c y = c'y` an observable.
* `PowDecay A`: the powers of `A` decay geometrically (`powDecay_of_eigs`: implied by all complex
  eigenvalues in the open unit disc, Gelfand's formula).

## Main results

* `inv_one_sub_hasSum`, `neumann_bilin_hasSum` (pp. 111–112): `∑ Aʲ = (I − A)⁻¹`;
  `disc_rate_hasSum`: `∑_{j≥1} (1 − ωʲ) Aʲ = A(I − A)⁻¹ − ωA(I − ωA)⁻¹`.
* `var_forecast`, `var_innov`: `E_t z_{t+k} = Aᵏ z_t`, `Δ_{t+1} z_{t+1+k} = Aᵏ ε_{t+1}`;
  `var_sum_responses`, `var_disc_rate_sum`: the sums of responses of p. 112.
* `identity_4_15`, `identity_4_16`, `identity_4_14`: the decompositions for any processes
  satisfying the flow identity and the bond-return identity (with general `ρ`, `ω`; the book's
  case is `ρ = 1`), with the transversality-type limits and summability as explicit hypotheses;
  `identity_4_14_of_var`, `identity_4_15_of_var`: in a stable VAR satisfying the identities, all
  those hypotheses hold automatically ("all the variables are stationary, impulse-responses die
  out", p. 103).
* `regression_eq_cholesky`, `filled_shock_eq_orthogonalized`, `regression_coeff_single` (4.17):
  filling in shocks by regressions on the inflation shock is the Cholesky orthogonalisation with
  inflation ordered first; `functional_regression`, `surplus_shock_sum` (4.18).
* `flow_restriction_of_identity` (2.25), `flow_restriction_iff_pv` ((2.25) ⇔ (2.26), needing only
  `I − ρA` invertible, survey E18), `var_pv_identity`: in a stable VAR satisfying the flow
  identity, the VAR present value of surpluses *is* the value of debt (the tautology of p. 605).
-/

namespace Cochrane.DebtDeficitsInflation.VARIdentities

open Filter Topology
open scoped Matrix
open Cochrane.DebtDeficitsInflation.Innovations (innov innov_apply innov_of_known)
open Cochrane.DebtDeficitsInflation.LinearizedIdentities (Flow BondReturn seriesTo_of_hasSum
  unexpected_inflation_identity bond_return_identity)

/-! ### The innovation operator, VARs and shocks -/

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Cochrane (2023), eq. (4.17), p. 104: the VAR `z_{t+1} = A z_t + ε_{t+1}`, coordinate by
coordinate, with random-variable coordinates `z t i : Ω → ℝ`. -/
def IsVAR (A : Matrix κ κ ℝ) (z ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, z (t + 1) i = ∑ j, A i j • z t j + ε (t + 1) i

/-- Cochrane (2023), eq. (4.17), p. 104: the VAR shocks are unforecastable, `E_t ε_{t+1} = 0`. -/
def ShockMDS (𝔼 : ExpectationSystem Ω) (ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (ε (t + 1) i) = 0

/-- Cochrane (2023), p. 112 ("`a_s, a_g` pick `s` and `g` out of the VAR, `s_t = a_s' x_t`"):
the observable `c'y` of a vector of random variables. -/
def obs (c : κ → ℝ) (y : κ → Ω → ℝ) : Ω → ℝ := ∑ i, c i • y i

/-- Cochrane (2023), p. 112: the realisation of a vector of random variables at a state. -/
def vecAt (y : κ → Ω → ℝ) (w : Ω) : κ → ℝ := fun i => y i w

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: an observable evaluated at a state is a dot product. -/
theorem obs_apply (c : κ → ℝ) (y : κ → Ω → ℝ) (w : Ω) : obs c y w = c ⬝ᵥ vecAt y w := by
  simp [obs, vecAt, dotProduct, Finset.sum_apply]

/-! ### Geometric decay of matrix powers -/

/-- Cochrane (2023), p. 103 ("all the variables are stationary, impulse-responses die out"): the
entries of the powers of `A` decay geometrically. -/
def PowDecay (A : Matrix κ κ ℝ) : Prop :=
  ∃ Cb r : ℝ, 0 ≤ Cb ∧ 0 ≤ r ∧ r < 1 ∧ ∀ k i j, |(A ^ k) i j| ≤ Cb * r ^ k

/-- Cochrane (2023), Online Appendix p. 605 ("the eigenvalues of `A` are less than one"): the
complex eigenvalues of a real square matrix, with multiplicity (restated from the Woodford
Chapter 4 project, `InvariantSplit.eigs`). -/
noncomputable def eigs (K : Matrix κ κ ℝ) : Multiset ℂ := (K.map Complex.ofReal).charpoly.roots

/-- Cochrane (2023), Online Appendix p. 605: powers of the complexified matrix are the
complexified powers (restated from the Woodford Chapter 4 project). -/
theorem map_ofReal_pow (K : Matrix κ κ ℝ) (t : ℕ) :
    (K ^ t).map Complex.ofReal = K.map Complex.ofReal ^ t :=
  Matrix.map_pow K Complex.ofRealHom t

/-- Cochrane (2023), Online Appendix p. 605 ("so long as the variables are stationary, the
eigenvalues of `A` are less than one"): if every complex eigenvalue of `A` lies in the open unit
disc, the powers of `A` decay geometrically (Gelfand's formula; restated from the Woodford
Chapter 4 project, `InvariantSplit.pow_entry_bound`). -/
theorem powDecay_of_eigs (K : Matrix κ κ ℝ) (h : ∀ μ ∈ eigs K, ‖μ‖ < 1) : PowDecay K := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix κ κ ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    have hm : w ∈ A.charpoly.roots := by
      rw [Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero]; exact hw
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
  refine ⟨Cb, r, hCb0, hr0.le, hr1, fun k i j => ?_⟩
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

/-- Cochrane (2023), p. 112 (the weights `ωʲ`): scaling a decaying matrix by `|ω| ≤ 1` keeps the
geometric decay of its powers. -/
theorem powDecay_smul {A : Matrix κ κ ℝ} (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1) :
    PowDecay (ω • A) := by
  obtain ⟨Cb, r, hCb, hr0, hr1, hb⟩ := hA
  refine ⟨Cb, r, hCb, hr0, hr1, fun k i j => ?_⟩
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  calc |ω| ^ k * |(A ^ k) i j| ≤ 1 * (Cb * r ^ k) :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) hω) (hb k i j) (abs_nonneg _) zero_le_one
    _ = Cb * r ^ k := one_mul _

/-- Cochrane (2023), pp. 111–112: each entry of the powers of a decaying matrix is absolutely
summable. -/
theorem summable_pow_entry {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    Summable (fun k => (A ^ k) i j) := by
  obtain ⟨Cb, r, _, hr0, hr1, hb⟩ := hA
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left Cb)
    (fun k => by rw [Real.norm_eq_abs]; exact hb k i j)

/-- Cochrane (2023), pp. 111–112: the entries of the powers of a decaying matrix tend to zero. -/
theorem tendsto_pow_entry {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    Tendsto (fun k => (A ^ k) i j) atTop (𝓝 0) :=
  (summable_pow_entry hA i j).tendsto_atTop_zero

/-- Cochrane (2023), pp. 111–112: the Neumann sum `∑_k Aᵏ`, entry by entry. -/
noncomputable def neumannSum (A : Matrix κ κ ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑' k, (A ^ k) i j

/-- Cochrane (2023), pp. 111–112: `(∑_k Aᵏ)(I − A) = I` for a decaying matrix. -/
theorem neumannSum_mul {A : Matrix κ κ ℝ} (hA : PowDecay A) : neumannSum A * (1 - A) = 1 := by
  ext i j
  have hs := fun l => summable_pow_entry hA i l
  have hrow : ∀ k, ∑ l, (A ^ k) i l * (1 - A) l j = (A ^ k) i j - (A ^ (k + 1)) i j := by
    intro k
    rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one, ← pow_succ, Matrix.sub_apply]
  have hS : HasSum (fun k => (A ^ k) i j - (A ^ (k + 1)) i j) ((neumannSum A * (1 - A)) i j) := by
    simp only [Matrix.mul_apply, neumannSum, Matrix.of_apply]
    have := hasSum_sum (s := Finset.univ) fun l _ => (hs l).hasSum.mul_right ((1 - A) l j)
    simpa only [hrow] using this
  have h1 := summable_pow_entry hA i j
  have h2 : Summable (fun k => (A ^ (k + 1)) i j) := (summable_nat_add_iff 1).mpr h1
  rw [← hS.tsum_eq, Summable.tsum_sub h1 h2, h1.tsum_eq_zero_add, pow_zero, add_sub_cancel_right]

/-- Cochrane (2023), pp. 111–112: for a decaying matrix `I − A` is invertible and
`(I − A)⁻¹ = ∑_k Aᵏ`. -/
theorem inv_one_sub_eq {A : Matrix κ κ ℝ} (hA : PowDecay A) : (1 - A)⁻¹ = neumannSum A :=
  Matrix.inv_eq_left_inv (neumannSum_mul hA)

/-- Cochrane (2023), pp. 111–112: for a decaying matrix `I − A` is invertible. -/
theorem isUnit_det_one_sub {A : Matrix κ κ ℝ} (hA : PowDecay A) : IsUnit (1 - A).det :=
  Matrix.isUnit_det_of_left_inverse (neumannSum_mul hA)

/-- Cochrane (2023), pp. 111–112: the matrix Neumann series `∑_k Aᵏ = (I − A)⁻¹`, entry by entry,
for a matrix whose powers decay (e.g. all eigenvalues in the open unit disc). -/
theorem inv_one_sub_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    HasSum (fun k => (A ^ k) i j) ((1 - A)⁻¹ i j) := by
  rw [inv_one_sub_eq hA]
  exact (summable_pow_entry hA i j).hasSum

omit [DecidableEq κ] in
/-- Cochrane (2023), pp. 111–112 (tool): entrywise sums pass to a bilinear form `c'(·)e`. -/
theorem hasSum_bilin {M : ℕ → Matrix κ κ ℝ} {S : Matrix κ κ ℝ}
    (h : ∀ i j, HasSum (fun k => M k i j) (S i j)) (c e : κ → ℝ) :
    HasSum (fun k => c ⬝ᵥ (M k *ᵥ e)) (c ⬝ᵥ (S *ᵥ e)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
  have := ((h i j).mul_right (e j)).mul_left (c i)
  simpa [mul_assoc] using this

/-- Cochrane (2023), p. 112: `∑_k c'Aᵏe = c'(I − A)⁻¹e` — the sum of the responses of an
observable `c'z` to a VAR shock `e`. -/
theorem neumann_bilin_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) (c e : κ → ℝ) :
    HasSum (fun k => c ⬝ᵥ ((A ^ k) *ᵥ e)) (c ⬝ᵥ ((1 - A)⁻¹ *ᵥ e)) :=
  hasSum_bilin (inv_one_sub_hasSum hA) c e

/-- Cochrane (2023), p. 112 (the discount-rate shock): entrywise,
`∑_{j≥1} (1 − ωʲ) Aʲ = A(I − A)⁻¹ − ωA(I − ωA)⁻¹` for a decaying `A` and `|ω| ≤ 1`. -/
theorem disc_rate_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1)
    (i j : κ) :
    HasSum (fun k => (1 - ω ^ (k + 1)) * (A ^ (k + 1)) i j)
      ((A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹) i j) := by
  have hωA := powDecay_smul hA hω
  have h1 : HasSum (fun k => (A * A ^ k) i j) ((A * (1 - A)⁻¹) i j) := by
    simp only [Matrix.mul_apply]
    exact hasSum_sum fun l _ => (inv_one_sub_hasSum hA l j).mul_left _
  have h2 : HasSum (fun k => ((ω • A) * (ω • A) ^ k) i j) ((ω • A * (1 - ω • A)⁻¹) i j) := by
    simp only [Matrix.mul_apply]
    exact hasSum_sum fun l _ => (inv_one_sub_hasSum hωA l j).mul_left _
  have h3 := h1.sub h2
  rw [← Matrix.sub_apply] at h3
  convert h3 using 1
  funext k
  rw [← pow_succ', ← pow_succ', smul_pow, Matrix.smul_apply, smul_eq_mul, pow_succ' A k]
  ring

/-! ### VAR forecasts and impulse responses -/

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: the innovation of an observable is the observable of the
innovations. -/
theorem innov_obs (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : κ → ℝ) (y : κ → Ω → ℝ) :
    innov 𝔼 t (obs c y) = obs c (fun i => innov 𝔼 t (y i)) := by
  simp only [innov_apply, obs, map_sum, map_smul, smul_sub]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: the conditional expectation of an observable is the observable of
the conditional expectations. -/
theorem E_obs (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : κ → ℝ) (y : κ → Ω → ℝ) :
    𝔼.E t (obs c y) = obs c (fun i => 𝔼.E t (y i)) := by
  simp only [obs, map_sum, map_smul]

/-- Cochrane (2023), eq. (4.17), p. 104: VAR forecasts, `E_t z_{t+k} = Aᵏ z_t`. -/
theorem var_forecast (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : 𝔼.E t (z (t + k) i) = ∑ j, (A ^ k) i j • z t j := by
  induction k generalizing i with
  | zero =>
    simp [hz t i, Matrix.one_apply, ite_smul]
  | succ k ih =>
    have e : z (t + (k + 1)) i = ∑ j, A i j • z (t + k) j + ε (t + k + 1) i := hvar (t + k) i
    have hε : 𝔼.E t (ε (t + k + 1) i) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right t k), hmds (t + k) i, map_zero]
    rw [e, map_add, map_sum, hε, add_zero]
    simp only [map_smul, ih]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

/-- Cochrane (2023), eq. (4.17) and p. 104 ("I start the VAR at `ε_1`"): the impulse response,
`Δ_{t+1} z_{t+1+k} = Aᵏ ε_{t+1}`. -/
theorem var_innov (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : innov 𝔼 t (z (t + 1 + k) i) = ∑ j, (A ^ k) i j • ε (t + 1) j := by
  have h1 := var_forecast 𝔼 hvar hmds hz (t + 1) k i
  have h2 := var_forecast 𝔼 hvar hmds hz t (k + 1) i
  rw [show t + (k + 1) = t + 1 + k by omega] at h2
  rw [innov_apply, h1, h2]
  simp only [hvar t, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [pow_succ]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun x y => ((A ^ k) i x * A x y) • z t y)]
  abel

/-- Cochrane (2023), p. 112: the response of an observable, `Δ_{t+1} c'z_{t+1+k} = c'Aᵏε_{t+1}`. -/
theorem var_innov_obs (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (c : κ → ℝ) (t k : ℕ) (w : Ω) :
    innov 𝔼 t (obs c (z (t + 1 + k))) w = c ⬝ᵥ ((A ^ k) *ᵥ vecAt (ε (t + 1)) w) := by
  rw [innov_obs, obs_apply]
  congr 1
  funext i
  simp only [vecAt, var_innov 𝔼 hvar hmds hz t k, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]

/-- Cochrane (2023), p. 112: the forecast of an observable, `E_t c'z_{t+k} = c'Aᵏz_t`. -/
theorem var_forecast_obs (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (c : κ → ℝ) (t k : ℕ) (w : Ω) :
    𝔼.E t (obs c (z (t + k))) w = c ⬝ᵥ ((A ^ k) *ᵥ vecAt (z t) w) := by
  rw [E_obs, obs_apply]
  congr 1
  funext i
  simp only [vecAt, var_forecast 𝔼 hvar hmds hz t k, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 103: an observable of an adapted VAR state is known at its date. -/
theorem obs_adapted (𝔼 : ExpectationSystem Ω) {z : ℕ → κ → Ω → ℝ}
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (c : κ → ℝ) (t : ℕ) :
    𝔼.E t (obs c (z t)) = obs c (z t) := by
  rw [E_obs]
  simp only [hz]

/-- Cochrane (2023), p. 112: `ρʲ c'Aʲe = c'(ρA)ʲe`. -/
theorem weight_bilin (A : Matrix κ κ ℝ) (ρ : ℝ) (c e : κ → ℝ) (j : ℕ) :
    ρ ^ j * c ⬝ᵥ ((A ^ j) *ᵥ e) = c ⬝ᵥ (((ρ • A) ^ j) *ᵥ e) := by
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Cochrane (2023), pp. 111–112: in a stable VAR, the `ρ`-weighted sum of the responses of an
observable is `∑ ρʲ Δ_{t+1} c'z_{t+1+j} = c'(I − ρA)⁻¹ε_{t+1}` (`|ρ| ≤ 1`). -/
theorem var_weighted_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (obs c (z (t + 1 + j))) w)
      (c ⬝ᵥ ((1 - ρ • A)⁻¹ *ᵥ vecAt (ε (t + 1)) w)) := by
  simp only [var_innov_obs 𝔼 hvar hmds hz, weight_bilin]
  exact neumann_bilin_hasSum (powDecay_smul hA hρ) c _

/-- Cochrane (2023), p. 112: the response of the sum of current and future surpluses and growth,
`Δ_1 ∑_{j≥0} (s̃_{1+j} + g_{1+j}) = (a_s + a_g)'(I − A)⁻¹ε_1`. -/
theorem var_sum_responses (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => innov 𝔼 t (obs c (z (t + 1 + j))) w)
      (c ⬝ᵥ ((1 - A)⁻¹ *ᵥ vecAt (ε (t + 1)) w)) := by
  have := var_weighted_sum 𝔼 hvar hmds hz hA (ρ := 1) (by simp) c t w
  simpa using this

/-- Cochrane (2023), p. 112: the response of the discount-rate term, with `c = a_{rⁿ} − a_π`,
`Δ_1 ∑_{j≥1} (1 − ωʲ) r_{1+j} = c'[A(I − A)⁻¹ − ωA(I − ωA)⁻¹]ε_1` (`|ω| ≤ 1`). -/
theorem var_disc_rate_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => (1 - ω ^ (j + 1)) * innov 𝔼 t (obs c (z (t + 2 + j))) w)
      (c ⬝ᵥ ((A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹) *ᵥ vecAt (ε (t + 1)) w)) := by
  have h := hasSum_bilin (M := fun k => (1 - ω ^ (k + 1)) • A ^ (k + 1))
    (S := A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹)
    (fun i j => by simpa only [Matrix.smul_apply, smul_eq_mul] using disc_rate_hasSum hA hω i j)
    c (vecAt (ε (t + 1)) w)
  refine h.congr_fun fun j => ?_
  rw [show t + 2 + j = t + 1 + (j + 1) by omega, var_innov_obs 𝔼 hvar hmds hz,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-! ### The inflation decompositions (4.14)–(4.16) -/

/-- Cochrane (2023), eq. (4.15), p. 103 (= (3.20); with the index typo `g_{t+1+j}`, `r_{t+1+j}`
corrected to `g_{1+j}`, `r_{1+j}`, survey E6), for general `ρ` (the book uses `ρ = 1`): if the
flow identity `ρv_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s̃_{t+1}` holds at every date, `v_t`
is known at `t`, the revisions are summable and `ρᵀ Δ v_{t+1+T} → 0`, then
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`, `r = rⁿ − π`.
Derived from the canonical (3.20), `LinearizedIdentities.unexpected_inflation_identity`. -/
theorem identity_4_15 (𝔼 : ExpectationSystem Ω) {ρ : ℝ} {v s g rn pi : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rn (t + 1) - pi (t + 1) - g (t + 1) - s (t + 1))
    (t : ℕ) (hv : 𝔼.E t (v t) = v t) (w : Ω) {S G R : ℝ}
    (hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) w) S)
    (hG : HasSum (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) w) G)
    (hR : HasSum (fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) R)
    (hlim : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) w) atTop (𝓝 0)) :
    innov 𝔼 t (pi (t + 1)) w - innov 𝔼 t (rn (t + 1)) w = -S - G + R := by
  have hflow' : Flow ρ v (fun t => rn t - pi t) g s := fun t => by
    rw [hflow t]
    change _ = v t + (rn (t + 1) - pi (t + 1)) - g (t + 1) - s (t + 1)
    abel
  have hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) w) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have h := hlim.const_mul ρ
    rw [mul_zero] at h
    refine h.congr fun T => ?_
    rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
    ring
  have h1 := unexpected_inflation_identity 𝔼 hflow' (fun _ => rfl) hv hT
    (seriesTo_of_hasSum hS) (seriesTo_of_hasSum hG)
  have h2 := (seriesTo_of_hasSum hR).unique h1
  linarith

/-- Cochrane (2023), eq. (4.16), p. 104 (= (3.21)): if the bond return obeys
`rⁿ_{t+1} = ω q_{t+1} − q_t` (the geometric-maturity identity, `q` the log bond price), `q_t` is
known at `t`, the revisions are summable and `ωᵀ Δ q_{t+1+T} → 0`, then
`Δrⁿ_{t+1} = −∑_{j≥1} ωʲ Δrⁿ_{t+1+j}`. Derived from the canonical (3.21),
`LinearizedIdentities.bond_return_identity`. -/
theorem identity_4_16 (𝔼 : ExpectationSystem Ω) {om : ℝ} {q rn : ℕ → Ω → ℝ}
    (hbond : ∀ t, rn (t + 1) = om • q (t + 1) - q t) (t : ℕ) (hq : 𝔼.E t (q t) = q t)
    (w : Ω) {Q : ℝ} (hQ : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) w) Q)
    (hlim : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) w) atTop (𝓝 0)) :
    innov 𝔼 t (rn (t + 1)) w = -Q := by
  have h := bond_return_identity 𝔼 (om := om) (q := q) (rn := rn) hbond hq hlim
  have h2 := (seriesTo_of_hasSum hQ).unique h
  linarith

/-- Cochrane (2023), eq. (4.14), p. 103 (= (3.22)), for general `ρ` (the book's case is `ρ = 1`,
where the weights are `1 − ωʲ`): under the hypotheses of `identity_4_15` and `identity_4_16`,
`∑_{j≥0} ωʲΔπ_{t+1+j} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}`, each
series converging. -/
theorem identity_4_14 (𝔼 : ExpectationSystem Ω) {ρ om : ℝ} {v s g rn pi q : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rn (t + 1) - pi (t + 1) - g (t + 1) - s (t + 1))
    (hbond : ∀ t, rn (t + 1) = om • q (t + 1) - q t)
    (t : ℕ) (hv : 𝔼.E t (v t) = v t) (hq : 𝔼.E t (q t) = q t) (w : Ω) {S G R Qr Qp : ℝ}
    (hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) w) S)
    (hG : HasSum (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) w) G)
    (hR : HasSum (fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) R)
    (hQr : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) Qr)
    (hQp : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (pi (t + 2 + j)) w) Qp)
    (hlimv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) w) atTop (𝓝 0))
    (hlimq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) w) atTop (𝓝 0)) :
    HasSum (fun j => om ^ j * innov 𝔼 t (pi (t + 1 + j)) w) (-S - G + (R - Qr)) ∧
    HasSum (fun j => (ρ ^ (j + 1) - om ^ (j + 1)) *
      innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) (R - Qr) := by
  have hQ : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) w) (Qr + Qp) := by
    refine (hQr.add hQp).congr_fun fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  have h16 := identity_4_16 𝔼 hbond t hq w hQ hlimq
  have h15 := identity_4_15 𝔼 hflow t hv w hS hG hR hlimv
  refine ⟨?_, (hR.sub hQr).congr_fun fun j => by ring⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero]
  convert hQp using 1
  · funext j
    rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  · linarith

/-- Cochrane (2023), p. 103: in a stable VAR the shifted weighted sums of responses converge. -/
theorem var_shifted_summable (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (c : κ → ℝ) (t : ℕ) (w : Ω) :
    Summable (fun j => ρ ^ (j + 1) * innov 𝔼 t (obs c (z (t + 2 + j))) w) := by
  have h := (summable_nat_add_iff 1).mpr (var_weighted_sum 𝔼 hvar hmds hz hA hρ c t w).summable
  refine h.congr fun j => ?_
  rw [show t + 1 + (j + 1) = t + 2 + j by omega]

/-- Cochrane (2023), eq. (4.15), p. 103, in a stable VAR (`IsVAR`, `PowDecay`, `|ρ| ≤ 1`) whose
observables satisfy the flow identity at every date: every series converges and
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr` holds with no further hypothesis
(the book's "all the variables are stationary, impulse-responses die out", p. 103). -/
theorem identity_4_15_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    {av as ag arn api : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) (w : Ω) :
    innov 𝔼 t (obs api (z (t + 1))) w - innov 𝔼 t (obs arn (z (t + 1))) w =
      -(∑' j, ρ ^ j * innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, ρ ^ j * innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, ρ ^ (j + 1) * innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w := by
  have hR : Summable (fun j => ρ ^ (j + 1) *
      innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w) := by
    refine ((var_shifted_summable 𝔼 hvar hmds hz hA hρ arn t w).sub
      (var_shifted_summable 𝔼 hvar hmds hz hA hρ api t w)).congr fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  refine identity_4_15 𝔼 (v := fun t => obs av (z t)) (s := fun t => obs as (z t))
    (g := fun t => obs ag (z t)) (rn := fun t => obs arn (z t)) (pi := fun t => obs api (z t))
    hflow t (obs_adapted 𝔼 hz av t) w
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ as t w).summable.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ ag t w).summable.hasSum hR.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ av t w).summable.tendsto_atTop_zero

/-- Cochrane (2023), eqs. (4.14) and (4.16), pp. 103–104, in a stable VAR (`IsVAR`, `PowDecay`,
`|ρ| ≤ 1`, `|ω| ≤ 1`) whose observables satisfy the flow identity and the bond-return identity
`rⁿ_{t+1} = ωq_{t+1} − q_t` at every date: every series converges and
`∑ωʲΔπ_{t+1+j} = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}` (at `ρ = 1`: weights `1 − ωʲ`),
and `Δrⁿ_{t+1} = −∑_{j≥1}ωʲΔrⁿ_{t+1+j}`. -/
theorem identity_4_14_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ om : ℝ} (hρ : |ρ| ≤ 1)
    (hom : |om| ≤ 1) {av as ag arn api aq : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1)))
    (hbond : ∀ t, obs arn (z (t + 1)) = om • obs aq (z (t + 1)) - obs aq (z t)) (t : ℕ)
    (w : Ω) :
    ∑' j, om ^ j * innov 𝔼 t (obs api (z (t + 1 + j))) w =
      -(∑' j, ρ ^ j * innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, ρ ^ j * innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, (ρ ^ (j + 1) - om ^ (j + 1)) *
          innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w ∧
    innov 𝔼 t (obs arn (z (t + 1))) w =
      -∑' j, om ^ (j + 1) * innov 𝔼 t (obs arn (z (t + 2 + j))) w := by
  have hsub : ∀ {r : ℝ}, |r| ≤ 1 → Summable (fun j => r ^ (j + 1) *
      innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w) := by
    intro r hr
    refine ((var_shifted_summable 𝔼 hvar hmds hz hA hr arn t w).sub
      (var_shifted_summable 𝔼 hvar hmds hz hA hr api t w)).congr fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  have hlimv := (var_weighted_sum 𝔼 hvar hmds hz hA hρ av t w).summable.tendsto_atTop_zero
  have hlimq := (var_weighted_sum 𝔼 hvar hmds hz hA hom aq t w).summable.tendsto_atTop_zero
  have h := identity_4_14 𝔼 (v := fun t => obs av (z t)) (s := fun t => obs as (z t))
    (g := fun t => obs ag (z t)) (rn := fun t => obs arn (z t)) (pi := fun t => obs api (z t))
    (q := fun t => obs aq (z t)) hflow hbond t (obs_adapted 𝔼 hz av t) (obs_adapted 𝔼 hz aq t) w
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ as t w).summable.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ ag t w).summable.hasSum
    (hsub hρ).hasSum (hsub hom).hasSum
    (var_shifted_summable 𝔼 hvar hmds hz hA hom api t w).hasSum hlimv hlimq
  constructor
  · rw [h.1.tsum_eq, h.2.tsum_eq]
  · exact identity_4_16 𝔼 (q := fun t => obs aq (z t)) (rn := fun t => obs arn (z t)) hbond t
      (obs_adapted 𝔼 hz aq t) w (var_shifted_summable 𝔼 hvar hmds hz hA hom arn t w).hasSum hlimq

/-- Cochrane (2023), eq. (4.14), p. 103, exactly as used in the book (`ρ = 1`): in a stable VAR
whose observables satisfy the flow identity
`v_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s̃_{t+1}` and the bond-return identity, every
series converges and
`∑_{j≥0} ωʲΔπ_{t+1+j} = −∑_{j≥0}Δs̃_{t+1+j} − ∑_{j≥0}Δg_{t+1+j} + ∑_{j≥1}(1 − ωʲ)Δr_{t+1+j}`
(`|ω| ≤ 1`). -/
theorem identity_4_14_rho_one_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {om : ℝ} (hom : |om| ≤ 1)
    {av as ag arn api aq : κ → ℝ}
    (hflow : ∀ t, obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1)))
    (hbond : ∀ t, obs arn (z (t + 1)) = om • obs aq (z (t + 1)) - obs aq (z t)) (t : ℕ)
    (w : Ω) :
    ∑' j, om ^ j * innov 𝔼 t (obs api (z (t + 1 + j))) w =
      -(∑' j, innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, (1 - om ^ (j + 1)) *
          innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w := by
  have h := (identity_4_14_of_var 𝔼 hvar hmds hz hA (ρ := 1) (by simp) hom
    (fun t => by rw [one_smul]; exact hflow t) hbond t w).1
  simpa only [one_pow, one_mul] using h

/-! ### Filling in shocks: regressions and the Cholesky orthogonalisation (4.17)–(4.18) -/

namespace Regression

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

omit [DecidableEq m] in
/-- Cochrane (2023), eq. (4.17), p. 104 (tool): the shock covariance `Σ = LLᵀ` of a block-lower
triangular factor `L = [L₁₁ 0; L₂₁ L₂₂]` (the Cholesky factor with the first block ordered
first) has blocks `L₁₁L₁₁ᵀ`, `L₁₁L₂₁ᵀ`, `L₂₁L₁₁ᵀ`, `L₂₁L₂₁ᵀ + L₂₂L₂₂ᵀ`. -/
theorem cholesky_blocks (L11 : Matrix m m ℝ) (L21 : Matrix n m ℝ) (L22 : Matrix n n ℝ) :
    Matrix.fromBlocks L11 0 L21 L22 * (Matrix.fromBlocks L11 0 L21 L22)ᵀ =
      Matrix.fromBlocks (L11 * L11ᵀ) (L11 * L21ᵀ) (L21 * L11ᵀ) (L21 * L21ᵀ + L22 * L22ᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Cochrane (2023), eq. (4.17), p. 104: filling in the other shocks by regressions on the
first-block shocks (`ε_z = b_{z,π}ε_π + u_z`, the coefficient matrix `B` defined by the
orthogonality condition `Cov(ε₂ − Bε₁, ε₁) = Σ₂₁ − BΣ₁₁ = 0`) gives exactly `B = L₂₁L₁₁⁻¹` for the
Cholesky factor `Σ = LLᵀ` with the first block ordered first. The regression is unique. -/
theorem regression_eq_cholesky {L11 : Matrix m m ℝ} {L21 : Matrix n m ℝ} {L22 : Matrix n n ℝ}
    (hL : IsUnit L11.det) {Sig : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hSig : Sig = Matrix.fromBlocks L11 0 L21 L22 * (Matrix.fromBlocks L11 0 L21 L22)ᵀ)
    (B : Matrix n m ℝ) :
    B * Sig.toBlocks₁₁ = Sig.toBlocks₂₁ ↔ B = L21 * L11⁻¹ := by
  rw [hSig, cholesky_blocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
  have hT : IsUnit L11ᵀ.det := by rwa [Matrix.det_transpose]
  constructor
  · intro h
    have h1 : B * L11 = L21 := by
      have := congrArg (· * L11ᵀ⁻¹) h
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] at this
      exact this
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]
  · rintro rfl
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L11⁻¹, Matrix.nonsing_inv_mul _ hL, Matrix.one_mul]

/-- Cochrane (2023), eq. (4.17), p. 104 ("this procedure is equivalent to the usual
orthogonalization of the shock covariance matrix"): the filled-in shock vector `(x, Bx)` is the
response to orthogonalised shocks `u` (`ε = Lu`, `Var u = I`) loading only on the first block,
`u = (L₁₁⁻¹x, 0)`. -/
theorem filled_shock_eq_orthogonalized {L11 : Matrix m m ℝ} (hL : IsUnit L11.det)
    (L21 : Matrix n m ℝ) (L22 : Matrix n n ℝ) (x : m → ℝ) :
    Sum.elim x ((L21 * L11⁻¹) *ᵥ x) =
      Matrix.fromBlocks L11 0 L21 L22 *ᵥ Sum.elim (L11⁻¹ *ᵥ x) 0 := by
  rw [Matrix.fromBlocks_mulVec]
  simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL]

omit [DecidableEq m] in
/-- Cochrane (2023), eq. (4.17), p. 104 (single shock, inflation ordered first): the regression
coefficient `b_{z,π} = Σ_{zπ}/Σ_{ππ}` equals the Cholesky first column normalised by its first
entry, `L_{zπ}/L_{ππ}`, so the filled shock `ε_1 = (1, b_{z,π}, …)` is the first orthogonalised
shock scaled to `ε_π = 1`. -/
theorem regression_coeff_single {ℓ : ℝ} (hℓ : ℓ ≠ 0) (L21 : Matrix n Unit ℝ)
    (L22 : Matrix n n ℝ) {Sig : Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ}
    (hSig : Sig = Matrix.fromBlocks (Matrix.of fun _ _ => ℓ) 0 L21 L22 *
      (Matrix.fromBlocks (Matrix.of fun _ _ => ℓ) 0 L21 L22)ᵀ) (z : n) :
    Sig (Sum.inr z) (Sum.inl ()) / Sig (Sum.inl ()) (Sum.inl ()) = L21 z () / ℓ := by
  rw [hSig, cholesky_blocks]
  simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₁, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
  field_simp

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: the regression of the shocks on a linear combination
`f'ε` (e.g. `f'ε = (a_s + a_g)'(I − A)⁻¹ε`, the surplus shock), with coefficients defined by
`Cov(ε − b f'ε, f'ε) = Σf − b (f'Σf) = 0`, has the unique solution `b = Σf/(f'Σf)`. -/
theorem functional_regression {Sig : Matrix κ κ ℝ} {f : κ → ℝ} (hf : f ⬝ᵥ (Sig *ᵥ f) ≠ 0)
    (b : κ → ℝ) :
    Sig *ᵥ f = (f ⬝ᵥ (Sig *ᵥ f)) • b ↔ b = (f ⬝ᵥ (Sig *ᵥ f))⁻¹ • (Sig *ᵥ f) := by
  constructor
  · intro h
    calc b = (f ⬝ᵥ (Sig *ᵥ f))⁻¹ • ((f ⬝ᵥ (Sig *ᵥ f)) • b) := by
          rw [smul_smul, inv_mul_cancel₀ hf, one_smul]
      _ = _ := by rw [← h]
  · rintro rfl
    rw [smul_smul, mul_inv_cancel₀ hf, one_smul]

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: the regression coefficients are normalised so that the
filled-in shock moves the functional by one, `f'b = 1`. -/
theorem functional_regression_normalised {Sig : Matrix κ κ ℝ} {f : κ → ℝ}
    (hf : f ⬝ᵥ (Sig *ᵥ f) ≠ 0) : f ⬝ᵥ ((f ⬝ᵥ (Sig *ᵥ f))⁻¹ • (Sig *ᵥ f)) = 1 := by
  rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hf]

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: for a positive definite shock covariance and a nonzero
functional, `f'Σf > 0`, so the regression of (4.18) is well defined. -/
theorem quadForm_pos {Sig : Matrix κ κ ℝ} (hSig : Sig.PosDef) {f : κ → ℝ} (hf : f ≠ 0) :
    0 < f ⬝ᵥ (Sig *ᵥ f) := by
  simpa using hSig.dotProduct_mulVec_pos hf

/-- Cochrane (2023), eq. (4.18) and p. 112 ("I start the surplus-shock response function at
`ε_1 = −[b_{rⁿ} b_g b_π …]'`"): in a stable VAR, if the date-`t+1` shock is the negative of the
regression coefficients on `f'ε` with `f = ((I − A)⁻¹)'c` (`c = a_s + a_g`), the response of the
sum of current and future surpluses (and growth) is exactly `−1`. -/
theorem surplus_shock_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) (Sig : Matrix κ κ ℝ) (c : κ → ℝ) (t : ℕ) (w : Ω)
    (hf : (c ᵥ* (1 - A)⁻¹) ⬝ᵥ (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)) ≠ 0)
    (hshock : vecAt (ε (t + 1)) w = -(((c ᵥ* (1 - A)⁻¹) ⬝ᵥ (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)))⁻¹ •
      (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)))) :
    HasSum (fun j => innov 𝔼 t (obs c (z (t + 1 + j))) w) (-1) := by
  have h := var_sum_responses 𝔼 hvar hmds hz hA c t w
  rwa [Matrix.dotProduct_mulVec, hshock, dotProduct_neg,
    functional_regression_normalised hf] at h

end Regression

/-! ### The present-value relation in a VAR is an identity (A2 (2.24)–(2.26)) -/

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: observables are linear in the weights. -/
theorem obs_add (c d : κ → ℝ) (y : κ → Ω → ℝ) : obs (c + d) y = obs c y + obs d y := by
  simp [obs, add_smul, Finset.sum_add_distrib]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: observables are linear in the weights. -/
theorem obs_sub (c d : κ → ℝ) (y : κ → Ω → ℝ) : obs (c - d) y = obs c y - obs d y := by
  simp [obs, sub_smul, Finset.sum_sub_distrib]

/-- Cochrane (2023), Online Appendix eq. (2.25), p. 605: if the flow identity (2.24)
`ρv_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s_{t+1}` holds identically in the VAR (for every
state `z` and shock `e`, with `v = a_v'z` etc.), then the VAR coefficients obey
`a_v'(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)'A` — and also `ρa_v = a_{rⁿ} − a_π − a_g − a_s` on the
shocks. "These are not restrictions we need to impose." -/
theorem flow_restriction_of_identity {A : Matrix κ κ ℝ} {ρ : ℝ} {av as ag arn api : κ → ℝ}
    (h : ∀ zz e : κ → ℝ, ρ * (av ⬝ᵥ (A *ᵥ zz + e)) =
      av ⬝ᵥ zz + (arn - api - ag - as) ⬝ᵥ (A *ᵥ zz + e)) :
    av ᵥ* (1 - ρ • A) = (as + ag - arn + api) ᵥ* A ∧ ρ • av = arn - api - ag - as := by
  constructor
  · funext i
    have := h (Pi.single i 1) 0
    simp only [add_zero, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    simp only [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.add_vecMul, Matrix.sub_vecMul, Pi.add_apply]
    simp only [Matrix.sub_vecMul, Pi.sub_apply] at this
    linarith
  · funext i
    have := h 0 (Pi.single i 1)
    simp only [Matrix.mulVec_zero, zero_add, dotProduct_single, mul_one, dotProduct_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul, this]

/-- Cochrane (2023), Online Appendix p. 605 (tool): `I − ρA` commutes with `A`. -/
theorem one_sub_smul_mul_comm (A : Matrix κ κ ℝ) (ρ : ℝ) :
    (1 - ρ • A) * A = A * (1 - ρ • A) := by
  simp [Matrix.sub_mul, Matrix.mul_sub]

/-- Cochrane (2023), Online Appendix p. 605 (tool): `(I − ρA)⁻¹` commutes with `A`. -/
theorem inv_one_sub_mul_comm {A : Matrix κ κ ℝ} {ρ : ℝ} (hM : IsUnit (1 - ρ • A).det) :
    (1 - ρ • A)⁻¹ * A = A * (1 - ρ • A)⁻¹ := by
  have hc := one_sub_smul_mul_comm A ρ
  calc (1 - ρ • A)⁻¹ * A = (1 - ρ • A)⁻¹ * (A * (1 - ρ • A)) * (1 - ρ • A)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    _ = (1 - ρ • A)⁻¹ * ((1 - ρ • A) * A) * (1 - ρ • A)⁻¹ := by rw [hc]
    _ = A * (1 - ρ • A)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- Cochrane (2023), Online Appendix eqs. (2.25)–(2.26), p. 605: the coefficient restriction
from the flow identity, `a_v'(I − ρA) = d'A`, and the present-value restriction
`a_v' = d'(I − ρA)⁻¹A` (`d = a_s + a_g − a_{rⁿ} + a_π`) are the same restriction. Only the
invertibility of `I − ρA` is needed (the book says "so long as the eigenvalues of `A` are less
than one", survey E18; convergence of the present value is a separate matter, `var_pv_identity`). -/
theorem flow_restriction_iff_pv {A : Matrix κ κ ℝ} {ρ : ℝ} (hM : IsUnit (1 - ρ • A).det)
    (av d : κ → ℝ) : av ᵥ* (1 - ρ • A) = d ᵥ* A ↔ av = d ᵥ* ((1 - ρ • A)⁻¹ * A) := by
  constructor
  · intro h
    have := congrArg (· ᵥ* (1 - ρ • A)⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one] at this
    rw [this, inv_one_sub_mul_comm hM]
  · rintro rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, ← one_sub_smul_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- Cochrane (2023), Online Appendix p. 605 ("we derived (2.26) by iterating forward (2.24)"):
if `ρv_{t+1} = v_t − y_{t+1}` at every date, `v_t` is known at `t` and `ρᵀE_t v_{t+T} → 0`, then
`v_t = ∑_{j≥0} ρʲ E_t y_{t+1+j}` as the limit of the partial sums. -/
theorem pv_of_flow (𝔼 : ExpectationSystem Ω) {ρ : ℝ} {v y : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t - y (t + 1)) (t : ℕ) (hv : 𝔼.E t (v t) = v t) (w : Ω)
    (hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) w) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w) atTop
      (𝓝 (v t w)) := by
  set F : ℕ → ℝ := fun j => 𝔼.E t (v (t + j)) w with hF
  have hstep : ∀ j, F j = ρ * F (j + 1) + 𝔼.E t (y (t + 1 + j)) w := by
    intro j
    have h := congrArg (fun x => 𝔼.E t x w) (hflow (t + j))
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [hF, show t + (j + 1) = t + j + 1 by omega, show t + 1 + j = t + j + 1 by omega]
    linarith
  have hiter : ∀ T, F 0 = ρ ^ T * F T +
      ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [ih, Finset.sum_range_succ, hstep T]
      ring
  have hF0 : F 0 = v t w := by simp [hF, hv]
  have hlim' : Tendsto (fun T => F 0 - ρ ^ T * F T) atTop (𝓝 (F 0 - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero, hF0] at hlim'
  refine hlim'.congr fun T => ?_
  rw [← hF0, hiter T]
  ring

/-- Cochrane (2023), Online Appendix eqs. (2.24)–(2.26), p. 605 (the tautology: "with `v_t` in the
VAR … the constructed present value of surpluses comes out to be each day's value of debt,
exactly, and by construction"): in a stable VAR (`PowDecay A`, `|ρ| ≤ 1`) whose observables obey
the flow identity (2.24), the VAR present value converges and equals the value of debt,
`v_t = ∑_{j≥0} ρʲ E_t(s + g − rⁿ + π)_{t+1+j} = d'(I − ρA)⁻¹A z_t`, `d = a_s + a_g − a_{rⁿ} + a_π`.
(2.26) "reduces to `v_t = v_t`". -/
theorem var_pv_identity (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1) {av as ag arn api : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (obs (as + ag - arn + api) (z (t + 1 + j))) w)
      (obs av (z t) w) ∧
    obs av (z t) w = (as + ag - arn + api) ⬝ᵥ (((1 - ρ • A)⁻¹ * A) *ᵥ vecAt (z t) w) := by
  set d := as + ag - arn + api with hd
  have hflow' : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) - obs d (z (t + 1)) := by
    intro t
    rw [hflow t, hd, obs_add, obs_sub, obs_add]
    abel
  have hterm : ∀ j, ρ ^ j * 𝔼.E t (obs d (z (t + 1 + j))) w =
      d ⬝ᵥ (((ρ • A) ^ j) *ᵥ (A *ᵥ vecAt (z t) w)) := by
    intro j
    rw [show t + 1 + j = t + (j + 1) by omega, var_forecast_obs 𝔼 hvar hmds hz, pow_succ,
      ← Matrix.mulVec_mulVec, weight_bilin]
  have hsum : HasSum (fun j => ρ ^ j * 𝔼.E t (obs d (z (t + 1 + j))) w)
      (d ⬝ᵥ (((1 - ρ • A)⁻¹ * A) *ᵥ vecAt (z t) w)) := by
    simp only [hterm, ← Matrix.mulVec_mulVec]
    exact neumann_bilin_hasSum (powDecay_smul hA hρ) d _
  have hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (obs av (z (t + T))) w) atTop (𝓝 0) := by
    have h := (neumann_bilin_hasSum (powDecay_smul hA hρ) av (vecAt (z t) w)).summable
    refine h.tendsto_atTop_zero.congr fun T => ?_
    rw [var_forecast_obs 𝔼 hvar hmds hz, weight_bilin]
  have hpv := pv_of_flow 𝔼 (v := fun t => obs av (z t)) (y := fun t => obs d (z t)) hflow' t
    (obs_adapted 𝔼 hz av t) w hlim
  have heq := tendsto_nhds_unique hpv hsum.tendsto_sum_nat
  exact ⟨heq ▸ hsum, heq⟩

end Cochrane.DebtDeficitsInflation.VARIdentities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditioning down: people have more information than the VAR

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, pp. 101–102 and p. 108,
and Online Appendix Chapter 2, §2.1.7, eqs. (2.22)–(2.23), pp. 602–603.

The valuation equation holds with people's information `Ω_t`,
`v_t = E(∑ ρʲ s̃_{t+1+j} | Ω_t)`. Taking expectations conditional on a smaller information set
`I_t ⊂ Ω_t` (the VAR's) gives `v_t = E(∑ ρʲ s̃_{t+1+j} | I_t)` *if and only if* `v_t ∈ I_t`;
otherwise the left-hand side is `E(v_t | I_t)`.

Two information sets cannot be expressed by a single `ExpectationSystem`; the minimal structure is
a pair of systems with the *coarser* property `E^I_t E^Ω_t = E^I_t` (the tower property across
information sets).

## Main definitions

* `Coarser 𝔼I 𝔼Ω`: `𝔼I` conditions on less information than `𝔼Ω`.
* `fullInfo Ω`: the system in which every random variable is known (`E_t = id`).
* `condExpSystem μ ℱ`: the Mathlib conditional expectation `μ[· | ℱ t]` on a finite probability
  space with full support, as an `ExpectationSystem`.

## Main results

* `condDown_general`: `E^I_t(PV) = E^I_t v_t` always; `condDown`: `v_t = E^I_t(PV)` when
  `v_t ∈ I_t`; `condDown_iff`: and only then.
* `condDown_series`, `condDown_pathwise`: the same for the genuine present-value series of a
  bounded surplus, `0 ≤ ρ < 1`.
* `r_squared_one`: if people use only the VAR information (`I = Ω`), `v_t` is an exact function of
  the VAR information (100% R², p. 102); `info_larger_of_not_known`: so a `v_t` that is not
  known given the VAR information refutes `I = Ω`.
* `condDown_fails_example`: with `v_t ∉ I_t` conditioning down genuinely fails (coin-flip tree).
* `condExpSystem`, `condExpSystem_coarser`, `condExpSystem_known_iff`, `condDown_condExp_iff`:
  the measure-theoretic instance — for nested filtrations `ℱI ≤ ℱΩ`, `μ[X|ℱI_t] = v_t` for
  `v_t = μ[X|ℱΩ_t]` iff `v_t` is `ℱI_t`-measurable.
-/

namespace Cochrane.DebtDeficitsInflation.ConditioningDown

open MeasureTheory Filter Topology

variable {Ω : Type*}

/-! ### Coarser expectation systems -/

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the system `𝔼I` conditions on less information than
`𝔼Ω` — the tower property across information sets, `E(E(x|Ω_t)|I_t) = E(x|I_t)`. -/
def Coarser (𝔼I 𝔼Ω : ExpectationSystem Ω) : Prop := ∀ t x, 𝔼I.E t (𝔼Ω.E t x) = 𝔼I.E t x

/-- Cochrane (2023), p. 101: every system is coarser than itself. -/
theorem coarser_refl (𝔼 : ExpectationSystem Ω) : Coarser 𝔼 𝔼 := fun t x => 𝔼.E_E_self t x

/-- Cochrane (2023), p. 101: coarsening is transitive. -/
theorem coarser_trans {𝔼1 𝔼2 𝔼3 : ExpectationSystem Ω} (h12 : Coarser 𝔼1 𝔼2)
    (h23 : Coarser 𝔼2 𝔼3) : Coarser 𝔼1 𝔼3 := by
  intro t x
  rw [← h12 t (𝔼3.E t x), h23 t x, h12 t x]

/-- Cochrane (2023), Online Appendix p. 602 ("people have more information than we do"): the
full-information system, in which every random variable is known at every date (`E_t = id`). -/
def fullInfo (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), Online Appendix p. 602: every system is coarser than full information. -/
theorem coarser_fullInfo (𝔼 : ExpectationSystem Ω) : Coarser 𝔼 (fullInfo Ω) :=
  fun _ _ => rfl

/-! ### Conditioning down -/

/-- Cochrane (2023), p. 101 ("if not, the left-hand side should be `E(v_t|I_t)`"): if
`v_t = E(X | Ω_t)` and `I_t ⊂ Ω_t`, then `E(X | I_t) = E(v_t | I_t)` always. -/
theorem condDown_general {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ}
    {v X : Ω → ℝ} (hv : v = 𝔼Ω.E t X) : 𝔼I.E t X = 𝔼I.E t v := by
  rw [hv, hc t X]

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602: conditioning down is
valid when `v_t ∈ I_t` (`E(v_t|I_t) = v_t`): then `v_t = E(X | I_t)`. -/
theorem condDown {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) (hvI : 𝔼I.E t v = v) : v = 𝔼I.E t X := by
  rw [condDown_general hc hv, hvI]

/-- Cochrane (2023), p. 101 ("this conditioning down is valid, so long as `v_t ∈ I_t`") and
Online Appendix p. 602 ("only if we include the value of debt in the VAR"): given
`v_t = E(X | Ω_t)`, the conditioned-down relation `v_t = E(X | I_t)` holds if and only if
`v_t` is known given `I_t`. -/
theorem condDown_iff {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) : v = 𝔼I.E t X ↔ 𝔼I.E t v = v := by
  constructor
  · intro h
    rw [h, 𝔼I.E_E_self]
  · exact condDown hc hv

/-- Cochrane (2023), p. 101, with the present value as a sum of forecasts: if `s̃` is bounded,
`0 ≤ ρ < 1`, `v_t = ∑ ρʲ E(s̃_{t+1+j} | Ω_t)` and `v_t ∈ I_t`, then
`v_t = ∑ ρʲ E(s̃_{t+1+j} | I_t)` — the VAR forecasts discount to the value of debt. -/
theorem condDown_series {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {ρ M : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    {v : Ω → ℝ} (hv : v = fun ω => ∑' j, ρ ^ j * 𝔼Ω.E t (s (t + 1 + j)) ω)
    (hvI : 𝔼I.E t v = v) : v = fun ω => ∑' j, ρ ^ j * 𝔼I.E t (s (t + 1 + j)) ω := by
  have hf : ∀ k ω, |(ρ ^ k • 𝔼Ω.E t (s (t + 1 + k))) ω| ≤ ρ ^ k * M := by
    intro k ω
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼Ω.abs_E_le (hs (t + 1 + k)) t ω) (pow_nonneg hρ0 k)
  funext ω
  have h := 𝔼I.E_tsum hρ0 hρ1 hf t ω
  have hv' : v = fun ω' => ∑' k, (ρ ^ k • 𝔼Ω.E t (s (t + 1 + k))) ω' := by
    rw [hv]; rfl
  rw [← hvI, hv', h]
  refine tsum_congr fun k => ?_
  rw [map_smul, hc t, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 101, with the ex-post present value `X = ∑ ρʲ s̃_{t+1+j}` (pathwise, for
bounded `s̃` and `0 ≤ ρ < 1`): if `v_t = E(X|Ω_t)` and `v_t ∈ I_t`, then
`v_t = E(X|I_t) = ∑ ρʲ E(s̃_{t+1+j}|I_t)`. -/
theorem condDown_pathwise {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {ρ M : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    {v : Ω → ℝ} (hv : v = 𝔼Ω.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω))
    (hvI : 𝔼I.E t v = v) :
    v = 𝔼I.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) ∧
    v = fun ω => ∑' j, ρ ^ j * 𝔼I.E t (s (t + 1 + j)) ω := by
  refine ⟨condDown hc hv hvI, ?_⟩
  have hf : ∀ k ω, |(ρ ^ k • s (t + 1 + k)) ω| ≤ ρ ^ k * M := by
    intro k ω
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
    exact mul_le_mul_of_nonneg_left (hs (t + 1 + k) ω) (pow_nonneg hρ0 k)
  funext ω
  have h := 𝔼I.E_tsum hρ0 hρ1 hf t ω
  rw [condDown hc hv hvI]
  change 𝔼I.E t (fun ω' => ∑' k, (ρ ^ k • s (t + 1 + k)) ω') ω = _
  rw [h]
  refine tsum_congr fun k => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 102 ("the only way to rescue such a calculation is to assume that people
use exactly the same information … `I_t = Ω_t`. … But in that case, `v_t` would be an exact
function of the observed information, with 100% R²"): if `𝔼I = 𝔼Ω` and `v_t = E(X | Ω_t)`, then
`v_t` is known given the VAR information and the forecast residual `v_t − E(v_t|I_t)` is zero. -/
theorem r_squared_one {𝔼I 𝔼Ω : ExpectationSystem Ω} (hsame : 𝔼I = 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) : 𝔼I.E t v = v ∧ v - 𝔼I.E t v = 0 := by
  subst hsame
  have h : 𝔼I.E t v = v := by rw [hv, 𝔼I.E_E_self]
  exact ⟨h, by rw [h, sub_self]⟩

/-- Cochrane (2023), p. 102 ("it is a testable implicit assumption, and it fails"): if the value
of debt is not an exact function of the VAR information, people's information is strictly
larger, `𝔼I ≠ 𝔼Ω`. -/
theorem info_larger_of_not_known {𝔼I 𝔼Ω : ExpectationSystem Ω} {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) (hnot : 𝔼I.E t v ≠ v) : 𝔼I ≠ 𝔼Ω :=
  fun h => hnot (r_squared_one h hv).1

/-- Cochrane (2023), p. 101 and Online Appendix p. 602 ("leaving `v_t` out of the VAR, the
present value relation … does not imply the relation one tests with the VAR"): an explicit
failure. In the two-coin-flip tree, people see everything (`fullInfo`), the econometrician only
the date-0 information (the coin-flip system); with `v_0 = X =` heads on the first flip,
`v_0 = E(X|Ω_0)` but `E(X|I_0) = 1/2 ≠ v_0`. -/
theorem condDown_fails_example :
    Coarser ExpectationsFiniteTree.coinSystem (fullInfo (Bool × Bool)) ∧
    ExpectationsFiniteTree.firstHeads =
      (fullInfo (Bool × Bool)).E 0 ExpectationsFiniteTree.firstHeads ∧
    ExpectationsFiniteTree.firstHeads ≠
      ExpectationsFiniteTree.coinSystem.E 0 ExpectationsFiniteTree.firstHeads := by
  refine ⟨coarser_fullInfo _, rfl, fun h => ?_⟩
  have := congrFun h (true, true)
  rw [ExpectationsFiniteTree.coinSystem_E0_firstHeads] at this
  norm_num [ExpectationsFiniteTree.firstHeads] at this

/-! ### The measure-theoretic instance (Mathlib `condExp`) -/

namespace CondExp

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]

omit [MeasurableSingletonClass Ω] [Finite Ω] in
/-- Cochrane (2023), p. 101 (tool): on a space where every point has positive mass, almost-sure
equality is equality. -/
theorem eq_of_ae_eq {μ : Measure Ω} (hμ : ∀ ω, μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    f = g := by
  funext ω
  by_contra hne
  have h0 : μ {x | ¬ f x = g x} = 0 := ae_iff.mp h
  exact hμ ω (measure_mono_null (Set.singleton_subset_iff.mpr hne) h0)

omit [MeasurableSingletonClass Ω] [Finite Ω] in
/-- Cochrane (2023), p. 101 (tool): on a space where every point has positive mass, an almost-sure
inequality holds everywhere. -/
theorem le_of_ae_le {μ : Measure Ω} (hμ : ∀ ω, μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f ≤ᵐ[μ] g) :
    f ≤ g := by
  intro ω
  by_contra hne
  have h0 : μ {x | ¬ f x ≤ g x} = 0 := ae_iff.mp h
  exact hμ ω (measure_mono_null (Set.singleton_subset_iff.mpr hne) h0)

/-- Cochrane (2023), p. 101 (`E(·|Ω_t)` and `E(·|I_t)`): the Mathlib conditional expectation
`μ[· | ℱ t]` with respect to a filtration `ℱ` on a finite probability space whose points all have
positive mass, as an `ExpectationSystem`. -/
noncomputable def condExpSystem (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ) :
    ExpectationSystem Ω where
  E t :=
    { toFun := fun x => μ[x | ℱ t]
      map_add' := fun _ _ => eq_of_ae_eq hμ (condExp_add Integrable.of_finite
        Integrable.of_finite _)
      map_smul' := fun c x => eq_of_ae_eq hμ (condExp_smul c x _) }
  const t c := condExp_const (hℱ t) c
  mono _ {_ _} h := le_of_ae_le hμ (condExp_mono Integrable.of_finite Integrable.of_finite
    (ae_of_all _ h))
  tower {_ t} hst _ := eq_of_ae_eq hμ (condExp_condExp_of_le (hmono hst) (hℱ t))
  known {_ t} hst _ := condExp_of_stronglyMeasurable (hℱ t)
    (stronglyMeasurable_condExp.mono (hmono hst)) Integrable.of_finite

/-- Cochrane (2023), p. 101: the operators of `condExpSystem` are the Mathlib conditional
expectations. -/
theorem condExpSystem_E (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ)
    (t : ℕ) (x : Ω → ℝ) : (condExpSystem μ hμ ℱ hℱ hmono).E t x = μ[x | ℱ t] := rfl

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): for nested filtrations `ℱI_t ≤ ℱΩ_t`, the
conditional-expectation system of `ℱI` is coarser than that of `ℱΩ` (the tower property). -/
theorem condExpSystem_coarser (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱI ℱΩ : ℕ → MeasurableSpace Ω) (hI : ∀ t, ℱI t ≤ ‹MeasurableSpace Ω›)
    (hΩ : ∀ t, ℱΩ t ≤ ‹MeasurableSpace Ω›) (hmI : Monotone ℱI) (hmΩ : Monotone ℱΩ)
    (hle : ∀ t, ℱI t ≤ ℱΩ t) :
    Coarser (condExpSystem μ hμ ℱI hI hmI) (condExpSystem μ hμ ℱΩ hΩ hmΩ) := by
  intro t x
  exact eq_of_ae_eq hμ (condExp_condExp_of_le (hle t) (hΩ t))

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): in the conditional-expectation system, `E_t v = v`
exactly when `v` is `ℱ_t`-measurable. -/
theorem condExpSystem_known_iff (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ)
    (t : ℕ) (v : Ω → ℝ) :
    (condExpSystem μ hμ ℱ hℱ hmono).E t v = v ↔ StronglyMeasurable[ℱ t] v := by
  rw [condExpSystem_E]
  constructor
  · intro h
    rw [← h]
    exact stronglyMeasurable_condExp
  · intro h
    exact condExp_of_stronglyMeasurable (hℱ t) h Integrable.of_finite

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602, in measure-theoretic
form: for nested filtrations `ℱI ≤ ℱΩ` (VAR information inside people's information) and
`v_t = E(X | ℱΩ_t)`, the conditioned-down relation `v_t = E(X | ℱI_t)` holds if and only if `v_t`
is `ℱI_t`-measurable — "so long as we include `v_t` in the VAR". -/
theorem condDown_condExp_iff (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱI ℱΩ : ℕ → MeasurableSpace Ω) (hI : ∀ t, ℱI t ≤ ‹MeasurableSpace Ω›)
    (hΩ : ∀ t, ℱΩ t ≤ ‹MeasurableSpace Ω›) (hmI : Monotone ℱI) (hmΩ : Monotone ℱΩ)
    (hle : ∀ t, ℱI t ≤ ℱΩ t) (t : ℕ) {v X : Ω → ℝ} (hv : v = μ[X | ℱΩ t]) :
    v = μ[X | ℱI t] ↔ StronglyMeasurable[ℱI t] v := by
  have h := condDown_iff (condExpSystem_coarser μ hμ ℱI ℱΩ hI hΩ hmI hmΩ hle) (t := t) (X := X)
    (v := v) hv
  rw [← condExpSystem_known_iff μ hμ ℱI hI hmI]
  exact h

end CondExp

end Cochrane.DebtDeficitsInflation.ConditioningDown

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Invertibility: why a VAR without the value of debt cannot recover the surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.1–2.1.6, eqs. (2.1)–(2.21), pp. 594–602.

A government that repays its debts runs a surplus process `s_t = a(L)ε_t` with `a(ρ) = 0`; the
moving average then has a root inside the unit circle and cannot be recovered from the history of
surpluses (an autoregression recovers the invertible "Wold" representation, with the root
flipped from `ρ⁻¹` to `ρ`), while a VAR that includes the value of debt recovers it.

## Main definitions

* `gen a z = ∑ aⱼ zʲ` (the book's `a(z)`, and `a(ρ)`; from `Innovations`); `genFnC` its complex
  version. Shocks are `Innovations.IsMDSNat` martingale differences.
* `armaCoeff φ θ`: the MA coefficients of `(1 − θL)/(1 − φL)` (MA(1) when `φ = 0`).
* `autocov a σ² k = σ² ∑ aⱼ a_{j+k}`: autocovariances of an MA(∞) process.
* `Recoverable a`: the structural shock is an absolutely summable filter of current and past
  surpluses (`ε_t = ∑ b_k s_{t−k}`, `b * a = δ`).
* `maSeries`, `hsCoeff`: an MA process started from a zero pre-sample, and the Hansen–Sargent
  coefficients `c_k = ∑ⱼ ρʲ a_{k+1+j}`.
* Hilbert-space layer: `WhiteNoise e σ²` (orthogonal, equal variances, `ℤ`-indexed), `maProc a e`
  (the MA(∞) process `∑ a_k e_{t−k}`), `pastSpan s t` (the closed span of `s_t, s_{t−1}, …`),
  `woldInnov θ m` (`w_t = ∑ θ⁻ᵏ m_{t−k}`).

## Main results

* Autocovariance flip (p. 102, (2.13), (2.4)–(2.5), survey E12): `arma11_autocov_flip` — the
  ARMA(1,1) with MA root `θ` and innovation variance `σ²` has exactly the same autocovariances as
  the one with root `θ⁻¹` and variance `θ²σ²`; `ma1_autocov_flip` (`φ = 0`); `blaschke_norm`,
  `spectral_density_flip`.
* Non-invertibility (pp. 597, 600): `genFnC_ne_zero_of_recoverable` (a recoverable MA has no zero
  in the closed unit disc), `not_recoverable_of_aRho_eq_zero` (`a(ρ) = 0`, `|ρ| ≤ 1` ⇒ not
  recoverable); `ma1_formal_inverse`, `ma1_inverse_not_summable` (2.12).
* ARMA(1,1) of (2.1)–(2.8): `debt_ar1` (2.7), `arma11_time_domain` and `arma11_revision` (2.3),
  `arma11_aRho_params` (`a(ρ) = β_s`), `arma11_iid_of_one`, `arma11_noninvertible_iff` (the root
  lies inside the disc iff `β_s < (1 − ρ)/α` or `β_s > (1 + ρ)/α`), `arma11_wold_aRho` (fitted
  `a(ρ) = (1 − ρ²)/α`), `debt_var_tr_det`, `debt_var_stable`, `shock_from_debt` (2.6)–(2.8).
* MA(1) examples: `ma1_pv_forward`, `ma1_value_reveals_shock` (p. 102), `ma1_debt_value` (2.9),
  `ma1_no_inflation_iff`, `ma1_repaying_debt_value` (2.10)–(2.11), `printed_2_11_wrong` (E13),
  `ma1_fitted_pv_innov` (2.13), `ma1_debt_var` (2.14)–(2.16).
* Hansen–Sargent: `ma_forecast`, `hansenSargent`, `hansenSargent_E_tsum` (2.19) and
  `hansenSargent_genFn` (`∑ c_k zᵏ = (a(z) − a(ρ))/(z − ρ)`); `value_expost_of_aRho_zero` (2.18:
  with `a(ρ) = 0` the ex-post present value equals the ex-ante one); `factor_value` (2.20)–(2.21)
  and `factor_of_aRho_zero` (2.17: `a(ρ) = 0` iff `a(L)` has the factor `1 − ρ⁻¹L`).
* Hilbert-space Wold statements: `not_mem_pastSpan_of_aRho_eq_zero` — for any MA(∞) with
  `a(ρ) = 0`, `|ρ| < 1`, the structural shock `e_t` is not in the closed linear span of current and
  past surpluses (no linear procedure on the surplus history recovers it); `wold_innovation` — for
  a process whose MA polynomial has the root `θ⁻¹` (`|θ| > 1`) and which is an AR filter of
  `m_t = e_t − θe_{t−1}`, `w_t = ∑ θ⁻ᵏ m_{t−k}` is its Wold innovation: `w_t ⟂` the past,
  `s_t − w_t` in the past (so it is the orthogonal projection of `s_t` on the past), `w` is white
  noise with variance `θ²σ²`, and `m_t = w_t − θ⁻¹w_{t−1}` — the fitted MA root is `θ⁻¹ = ρ`;
  instances `ma1_wold` (p. 102, (2.13)) and `arma11_wold` ((2.4)–(2.5)).
-/

namespace Cochrane.DebtDeficitsInflation.Invertibility

open Filter Topology VARIdentities
open Cochrane.DebtDeficitsInflation.Innovations (gen IsMDSNat innov innov_apply)
open scoped Matrix

variable {Ω : Type*}

/-! ### Generating functions and ARMA(1,1) coefficients -/

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: the moving-average coefficients of
`(1 − θL)/(1 − φL)`: `a₀ = 1`, `a_{k+1} = (φ − θ)φᵏ` (an MA(1) `1 − θL` when `φ = 0`). -/
def armaCoeff (φ θ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (φ - θ) * φ ^ k

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: `a(z) = (1 − θz)/(1 − φz)` for
`|φz| < 1`. -/
theorem armaCoeff_hasSum {φ θ z : ℝ} (h : |φ * z| < 1) :
    HasSum (fun j => armaCoeff φ θ j * z ^ j) ((1 - θ * z) / (1 - φ * z)) := by
  have hne : 1 - φ * z ≠ 0 := by
    intro h0
    have : φ * z = 1 := by linarith
    rw [this, abs_one] at h
    exact lt_irrefl _ h
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, armaCoeff, pow_zero, mul_one]
  have hg := (hasSum_geometric_of_abs_lt_one h).mul_left ((φ - θ) * z)
  convert hg using 1
  · funext k
    simp only [pow_succ, mul_pow]
    ring
  · rw [div_sub_one hne, div_eq_mul_inv]
    ring

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: `a(z) = (1 − θz)/(1 − φz)`. -/
theorem genFn_armaCoeff {φ θ z : ℝ} (h : |φ * z| < 1) :
    gen (armaCoeff φ θ) z = (1 - θ * z) / (1 - φ * z) :=
  (armaCoeff_hasSum h).tsum_eq

/-- Cochrane (2023), Online Appendix p. 595: the ARMA(1,1) coefficients are absolutely summable
when `|φ| < 1`. -/
theorem summable_abs_armaCoeff {φ : ℝ} (hφ : |φ| < 1) (θ : ℝ) :
    Summable (fun k => |armaCoeff φ θ k|) := by
  rw [← summable_nat_add_iff 1]
  have := (summable_geometric_of_lt_one (abs_nonneg φ) hφ).mul_left |φ - θ|
  refine this.congr fun k => ?_
  simp [armaCoeff, abs_mul, abs_pow]

/-- Cochrane (2023), eq. (4.1), p. 87: the autocovariances `γ_k = σ² ∑ⱼ aⱼ a_{j+k}` of an MA(∞)
process with innovation variance `σ²`. -/
noncomputable def autocov (a : ℕ → ℝ) (σ2 : ℝ) (k : ℕ) : ℝ := σ2 * ∑' j, a j * a (j + k)

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597: the autocovariances of the
ARMA(1,1) `(1 − θL)/(1 − φL)`, `|φ| < 1`: `γ_k = σ²[a_k + (φ − θ)²φᵏ/(1 − φ²)]`. -/
theorem arma11_autocov {φ : ℝ} (hφ : |φ| < 1) (θ σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff φ θ) σ2 k =
      σ2 * (armaCoeff φ θ k + (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2)) := by
  have hφ2 : |φ ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg φ]
  have h : HasSum (fun j => armaCoeff φ θ j * armaCoeff φ θ (j + k))
      (armaCoeff φ θ k + (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, armaCoeff, one_mul, zero_add,
      add_sub_cancel_left]
    have hg := (hasSum_geometric_of_abs_lt_one hφ2).mul_left ((φ - θ) ^ 2 * φ ^ k)
    rw [show (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2) = (φ - θ) ^ 2 * φ ^ k * (1 - φ ^ 2)⁻¹ by
      rw [div_eq_mul_inv]]
    refine hg.congr_fun fun j => ?_
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only
    ring
  rw [autocov, h.tsum_eq]

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597, and survey E12 (the spectral
densities agree only after rescaling the innovation variance): the ARMA(1,1) with MA root `θ` and
innovation variance `σ²` has the same autocovariances at every lag as the one with root `θ⁻¹`
and variance `θ²σ²`. Second moments cannot tell them apart. -/
theorem arma11_autocov_flip {φ θ : ℝ} (hφ : |φ| < 1) (hθ : θ ≠ 0) (σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff φ θ) σ2 k = autocov (armaCoeff φ θ⁻¹) (θ ^ 2 * σ2) k := by
  have hφ2 : 1 - φ ^ 2 ≠ 0 := by
    have : φ ^ 2 < 1 := by nlinarith [abs_nonneg φ, sq_abs φ]
    linarith
  rw [arma11_autocov hφ, arma11_autocov hφ]
  cases k with
  | zero =>
    simp only [armaCoeff, pow_zero, mul_one]
    field_simp
    ring
  | succ k =>
    simp only [armaCoeff]
    field_simp
    ring

/-- Cochrane (2023), p. 102, and Online Appendix (2.13), p. 599: the MA(1) `s_t = ε_t − θε_{t−1}`
has autocovariances `(1 + θ²)σ²`, `−θσ²` and zero beyond lag one. -/
theorem ma1_autocov (θ σ2 : ℝ) :
    autocov (armaCoeff 0 θ) σ2 0 = (1 + θ ^ 2) * σ2 ∧
    autocov (armaCoeff 0 θ) σ2 1 = -θ * σ2 ∧
    ∀ k, autocov (armaCoeff 0 θ) σ2 (k + 2) = 0 := by
  have h0 : |(0 : ℝ)| < 1 := by simp
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [arma11_autocov h0]; simp [armaCoeff]; ring
  · rw [arma11_autocov h0]; simp [armaCoeff]; ring
  · rw [arma11_autocov h0]; simp [armaCoeff]

/-- Cochrane (2023), p. 102 ("an autoregression will estimate `s̃_t = u_t − θu_{t−1}` with
`θ = ρ`"), and Online Appendix (2.13), p. 599: the MA(1) with root `θ` and variance `σ²` and the
MA(1) with root `θ⁻¹` and variance `θ²σ²` have identical autocovariances. -/
theorem ma1_autocov_flip {θ : ℝ} (hθ : θ ≠ 0) (σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff 0 θ) σ2 k = autocov (armaCoeff 0 θ⁻¹) (θ ^ 2 * σ2) k :=
  arma11_autocov_flip (by simp) hθ σ2 k

/-- Cochrane (2023), Online Appendix p. 597 (the spectral density `S(ω) = a(e^{iω})a(e^{−iω})`):
the Blaschke identity — on the unit circle `|1 − ρ⁻¹z| = |ρ|⁻¹ |1 − ρz|`. -/
theorem blaschke_norm {ρ : ℝ} (hρ : ρ ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (ρ : ℂ)⁻¹ * z‖ = |ρ|⁻¹ * ‖1 - (ρ : ℂ) * z‖ := by
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have h1 : 1 - (ρ : ℂ)⁻¹ * z = (ρ : ℂ)⁻¹ * ((ρ : ℂ) - z) := by
    field_simp
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have h2 : 1 - (ρ : ℂ) * z = -(z * ((starRingEnd ℂ) ((ρ : ℂ) - z))) := by
    rw [map_sub, Complex.conj_ofReal, mul_sub, hzc]
    ring
  rw [h1, h2, norm_neg, norm_mul, norm_mul, hz, one_mul, Complex.norm_conj, norm_inv,
    Complex.norm_real, Real.norm_eq_abs]

/-- Cochrane (2023), Online Appendix p. 597 and survey E12: the spectral density of the
non-invertible numerator `1 − ρ⁻¹L` with innovation variance `σ²` equals that of the invertible
numerator `1 − ρL` with variance `σ²/ρ²`, at every frequency (`|z| = 1`). -/
theorem spectral_density_flip {ρ : ℝ} (hρ : ρ ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) (σ2 : ℝ) :
    ‖1 - (ρ : ℂ)⁻¹ * z‖ ^ 2 * σ2 = ‖1 - (ρ : ℂ) * z‖ ^ 2 * (σ2 / ρ ^ 2) := by
  rw [blaschke_norm hρ hz, mul_pow, inv_pow, sq_abs]
  field_simp

/-! ### Recoverability and the zeros of `a(z)` -/

/-- Cochrane (2023), p. 102 ("the shock `ε_t` is a function of current and future surpluses, not
current and past surpluses") and Online Appendix p. 600: the structural shock is recoverable
from current and past surpluses by an absolutely summable filter `ε_t = ∑ b_k s_{t−k}`, i.e.
`b * a = δ` (Cauchy product). -/
def Recoverable (a : ℕ → ℝ) : Prop :=
  ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
    ∀ n, ∑ k ∈ Finset.range (n + 1), b k * a (n - k) = if n = 0 then 1 else 0

/-- Cochrane (2023), Online Appendix p. 597 ("all zeros of the moving-average representation are
outside the unit circle"): the complex generating function `a(z) = ∑ aⱼ zʲ`. -/
noncomputable def genFnC (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' j, (a j : ℂ) * z ^ j

/-- Cochrane (2023), Online Appendix p. 597: at a real point the complex generating function is
the real one. -/
theorem genFnC_ofReal (a : ℕ → ℝ) (ρ : ℝ) : genFnC a (ρ : ℂ) = (gen a ρ : ℂ) := by
  rw [genFnC, gen, Complex.ofReal_tsum]
  push_cast
  rfl

/-- Cochrane (2023), Online Appendix pp. 597, 600 ("the condition for a moving-average
representation to correspond to an autoregression is that all the zeros of `a(z)` lie outside
the unit circle"): if the shock is recoverable from current and past surpluses, `a(z) ≠ 0` on
the closed unit disc. -/
theorem genFnC_ne_zero_of_recoverable {a : ℕ → ℝ} (ha : Summable (fun j => |a j|))
    (hrec : Recoverable a) {z : ℂ} (hz : ‖z‖ ≤ 1) : genFnC a z ≠ 0 := by
  obtain ⟨b, hb, hconv⟩ := hrec
  have hzn : ∀ n : ℕ, ‖z ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hf : Summable (fun n => ‖(b n : ℂ) * z ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hzn n)) hb
  have hg : Summable (fun n => ‖(a n : ℂ) * z ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hzn n)) ha
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hinner : ∀ n, ∑ k ∈ Finset.range (n + 1), (b k : ℂ) * z ^ k * ((a (n - k) : ℂ) *
      z ^ (n - k)) = if n = 0 then 1 else 0 := by
    intro n
    have : ∑ k ∈ Finset.range (n + 1), (b k : ℂ) * z ^ k * ((a (n - k) : ℂ) * z ^ (n - k)) =
        z ^ n * ((∑ k ∈ Finset.range (n + 1), b k * a (n - k) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
      rw [this]
      ring
    rw [this, hconv n]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [hinner] at hprod
  rw [tsum_ite_eq] at hprod
  intro h0
  rw [genFnC] at h0
  rw [h0, mul_zero] at hprod
  exact zero_ne_one hprod

/-- Cochrane (2023), Online Appendix p. 600: a zero of `a(z)` in the closed unit disc makes the
structural shock unrecoverable from current and past surpluses. -/
theorem not_recoverable_of_root {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (h0 : genFnC a z = 0) : ¬ Recoverable a :=
  fun hrec => genFnC_ne_zero_of_recoverable ha hrec hz h0

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 ("a government that pays back its debts
runs a surplus process with `a(ρ) = 0`, `ρ ≤ 1` … so the moving-average representation … must
be non-invertible") and p. 600: if `a(ρ) = 0` with `|ρ| ≤ 1`, the structural shock cannot be
recovered from current and past surpluses by any absolutely summable filter. -/
theorem not_recoverable_of_aRho_eq_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) : ¬ Recoverable a := by
  refine not_recoverable_of_root ha (z := (ρ : ℂ)) ?_ ?_
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact hρ
  · rw [genFnC_ofReal, h0, Complex.ofReal_zero]

/-! ### The MA(1) and ARMA(1,1) examples -/

/-- Cochrane (2023), p. 88 and p. 102: for the MA(1) `s_t = ε_t − θε_{t−1}`, `a(ρ) = 1 − θρ`. -/
theorem ma1_aRho (θ ρ : ℝ) : gen (armaCoeff 0 θ) ρ = 1 - θ * ρ := by
  rw [genFn_armaCoeff (by simp)]
  simp

/-- Cochrane (2023), p. 102: the MA(1) repays its debt, `a(ρ) = 0`, exactly when `θ = ρ⁻¹`. -/
theorem ma1_aRho_eq_zero_iff {θ ρ : ℝ} (hρ : ρ ≠ 0) : gen (armaCoeff 0 θ) ρ = 0 ↔ θ = ρ⁻¹ := by
  rw [ma1_aRho]
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- Cochrane (2023), p. 102 ("with only `θ < 1`, and thus `a(ρ) > 1 − ρ`, the moving average is
technically invertible"): for `0 ≤ θ < 1` and `ρ > 0`, `a(ρ) = 1 − θρ > 1 − ρ`. -/
theorem ma1_aRho_gt {θ ρ : ℝ} (hθ1 : θ < 1) (hρ : 0 < ρ) :
    1 - ρ < gen (armaCoeff 0 θ) ρ := by
  rw [ma1_aRho]
  nlinarith

/-- Cochrane (2023), p. 102 ("you will falsely estimate `a(ρ) = 1 − ρ² ≠ 0`"): the fitted
(flipped-root) MA(1) has `a(ρ) = 1 − ρ²`, nonzero for `|ρ| < 1`. -/
theorem ma1_fitted_aRho {ρ : ℝ} (hρ : |ρ| < 1) :
    gen (armaCoeff 0 ρ) ρ = 1 - ρ ^ 2 ∧ gen (armaCoeff 0 ρ) ρ ≠ 0 := by
  rw [ma1_aRho]
  refine ⟨by ring, ?_⟩
  have : ρ ^ 2 < 1 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
  nlinarith

/-- Cochrane (2023), Online Appendix eq. (2.12), p. 598: the only formal inverse of `1 − RL` is
`∑ Rᵏ Lᵏ` — if `b * (1 − RL) = δ` then `b_k = Rᵏ`. -/
theorem ma1_formal_inverse {R : ℝ} {b : ℕ → ℝ}
    (hb : ∀ n, ∑ k ∈ Finset.range (n + 1), b k * armaCoeff 0 R (n - k) =
      if n = 0 then 1 else 0) : ∀ k, b k = R ^ k := by
  have h0 : b 0 = 1 := by simpa [armaCoeff] using hb 0
  have hstep : ∀ k, b (k + 1) = R * b k := by
    intro k
    have h := hb (k + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    have hz : ∑ x ∈ Finset.range k, b x * armaCoeff 0 R (k + 1 - x) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxk : x < k := Finset.mem_range.mp hx
      rw [show k + 1 - x = (k - 1 - x + 1) + 1 by omega]
      simp [armaCoeff]
    rw [hz, show k + 1 - k = 0 + 1 by omega, Nat.sub_self] at h
    simp only [armaCoeff, pow_zero, mul_one, zero_add, zero_sub, Nat.add_one_ne_zero,
      ↓reduceIte] at h
    linarith
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [hstep k, ih, pow_succ, mul_comm]

/-- Cochrane (2023), Online Appendix eq. (2.12), p. 598 ("we see exploding coefficients"): for
`|R| ≥ 1` the inverse coefficients `Rᵏ` are not summable, and `1 − RL` is not recoverable. -/
theorem ma1_inverse_not_summable {R : ℝ} (hR : 1 ≤ |R|) :
    ¬ Summable (fun k => |R ^ k|) ∧ ¬ Recoverable (armaCoeff 0 R) := by
  constructor
  · intro h
    have := h.tendsto_atTop_zero
    have hge : ∀ k : ℕ, 1 ≤ |R ^ k| := fun k => by rw [abs_pow]; exact one_le_pow₀ hR
    have hev := this.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨k, hk⟩ := hev.exists
    linarith [hge k]
  · have hR0 : R ≠ 0 := by
      intro h; rw [h, abs_zero] at hR; linarith
    refine not_recoverable_of_aRho_eq_zero (ρ := R⁻¹) (summable_abs_armaCoeff (by simp) R) ?_ ?_
    · rw [abs_inv]; exact inv_le_one_of_one_le₀ hR
    · rw [ma1_aRho, mul_inv_cancel₀ hR0, sub_self]

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: with `φ = (1 − α)/ρ`,
`θ = (1 − αβ_s)/ρ` (`ρ ≠ 0`, `0 < α < 2` so that `|φρ| < 1`), `a(ρ) = β_s` — "β_s controls how
much of a shock is repaid, and how much results in inflation". -/
theorem arma11_aRho_params {ρ α βs : ℝ} (hρ : ρ ≠ 0) (hα0 : 0 < α) (hα2 : α < 2) :
    gen (armaCoeff ((1 - α) / ρ) ((1 - α * βs) / ρ)) ρ = βs := by
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  have hα : α ≠ 0 := hα0.ne'
  rw [genFn_armaCoeff h, div_mul_cancel₀ _ hρ, div_mul_cancel₀ _ hρ,
    show (1 : ℝ) - (1 - α * βs) = α * βs by ring, show (1 : ℝ) - (1 - α) = α by ring]
  field_simp

/-- Cochrane (2023), Online Appendix p. 595 ("in the case `β_s = 1`, the roots cancel and we
recover the i.i.d. shock"): `θ = φ` makes every coefficient after the first vanish. -/
theorem arma11_iid_of_one (φ : ℝ) (k : ℕ) : armaCoeff φ φ (k + 1) = 0 := by
  simp [armaCoeff]

/-- Cochrane (2023), Online Appendix p. 598 ("the non-invertibility problem occurs for any
`β_s < (1 − ρ)/α`"): with `α, ρ > 0`, the MA root `ρ/(1 − αβ_s)` of (2.3) lies strictly inside
the unit circle (`|θ| > 1`) iff `β_s < (1 − ρ)/α` or `β_s > (1 + ρ)/α`. (The second region,
`θ < −1`, is not mentioned in the book.) -/
theorem arma11_noninvertible_iff {ρ α βs : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    1 < |(1 - α * βs) / ρ| ↔ βs < (1 - ρ) / α ∨ (1 + ρ) / α < βs := by
  rw [abs_div, abs_of_pos hρ, one_lt_div hρ, lt_abs, lt_div_iff₀ hα, div_lt_iff₀ hα]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Cochrane (2023), Online Appendix p. 596: the MA root of (2.3) is `z* = ρ/(1 − αβ_s)`. -/
theorem arma11_root {ρ α βs : ℝ} (hρ : ρ ≠ 0) (h : 1 - α * βs ≠ 0) :
    1 - (1 - α * βs) / ρ * (ρ / (1 - α * βs)) = 0 := by
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 597 ("this ARMA(1,1) is not invertible, and hence it
cannot be recovered by any autoregression"): for `|φ| < 1 < |θ|` the ARMA(1,1) with MA root
`θ⁻¹` is not recoverable. -/
theorem arma11_not_recoverable {φ θ : ℝ} (hφ : |φ| < 1) (hθ : 1 < |θ|) :
    ¬ Recoverable (armaCoeff φ θ) := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hinv : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have hφθ : |φ * θ⁻¹| < 1 := by
    rw [abs_mul]
    calc |φ| * |θ⁻¹| ≤ |φ| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ < 1 := by linarith
  refine not_recoverable_of_aRho_eq_zero (summable_abs_armaCoeff hφ θ) hinv ?_
  rw [genFn_armaCoeff hφθ, mul_inv_cancel₀ hθ0, sub_self, zero_div]

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597: the fitted (Wold) ARMA(1,1)
`(1 − ρL)/(1 − φL)`, `φ = (1 − α)/ρ`, has `a(ρ) = (1 − ρ²)/α`, "not the correct answer
`a(ρ) = 0`". -/
theorem arma11_wold_aRho {ρ α : ℝ} (hρ : ρ ≠ 0) (hα0 : 0 < α) (hα2 : α < 2) :
    gen (armaCoeff ((1 - α) / ρ) ρ) ρ = (1 - ρ ^ 2) / α := by
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  rw [genFn_armaCoeff h, div_mul_cancel₀ _ hρ]
  congr 1
  · ring
  · ring


/-! ### The debt VAR (2.1)–(2.8) under any expectation system -/

/-- Cochrane (2023), Online Appendix eq. (2.7), p. 597: in the model (2.1)–(2.2) with
`a_u(L) = 1`, `s_{t+1} = αv_t + ε_{t+1}`, `ρv_{t+1} = v_t + β_sε_{t+1} − s_{t+1}`, the value of debt
is an AR(1), `v_{t+1} = ((1 − α)/ρ)v_t − ((1 − β_s)/ρ)ε_{t+1}`. -/
theorem debt_ar1 {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    v (t + 1) = ((1 - α) / ρ) • v t - ((1 - βs) / ρ) • ε (t + 1) := by
  funext w
  have h1 := congrFun (hv t) w
  have h2 := congrFun (hs t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  field_simp
  linarith

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 (first form): the surplus is an
ARMA(1,1), `s_{t+2} − ((1 − α)/ρ)s_{t+1} = ε_{t+2} − ((1 − αβ_s)/ρ)ε_{t+1}`. -/
theorem arma11_time_domain {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    s (t + 2) - ((1 - α) / ρ) • s (t + 1) = ε (t + 2) - ((1 - α * βs) / ρ) • ε (t + 1) := by
  funext w
  have h1 := congrFun (hs (t + 1)) w
  have h2 := congrFun (hs t) w
  have h3 := congrFun (debt_ar1 hρ hs hv t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 (second form): the surplus response to the
shock, `Δ_{t+1} s_{t+1+j} = a_j ε_{t+1}` with `a₀ = 1`, `a_{k+1} = −α(1 − β_s)ρ⁻¹((1 − α)/ρ)ᵏ`
("1 in one direction followed by a small and geometrically decaying set of responses in the
other direction"), i.e. `a = armaCoeff ((1 − α)/ρ) ((1 − αβ_s)/ρ)`. -/
theorem arma11_revision (𝔼 : ExpectationSystem Ω) {ρ α βs : ℝ} (hρ : ρ ≠ 0)
    {s v ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v)
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) =
      armaCoeff ((1 - α) / ρ) ((1 - α * βs) / ρ) j • ε (t + 1) := by
  set φ := (1 - α) / ρ with hφ
  have hv1 := debt_ar1 hρ hs hv
  have har : 𝔼.IsAR1 φ v := by
    refine ⟨hvad, fun τ => ?_⟩
    rw [hv1 τ, map_sub, map_smul, map_smul, hvad τ, hmds.2 τ, smul_zero, sub_zero]
  have hfc : ∀ τ k, 𝔼.E τ (s (τ + 1 + k)) = (α * φ ^ k) • v τ := by
    intro τ k
    rw [show τ + 1 + k = τ + k + 1 by omega, hs (τ + k), map_add, map_smul,
      𝔼.ar1_iterate har τ k, show τ + k + 1 = τ + 1 + k by omega, hmds.E_future τ k, add_zero,
      smul_smul]
  cases j with
  | zero =>
    have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
      rw [hs t, map_add, map_smul, ← hvad t, 𝔼.known (Nat.le_succ t), hvad t, hmds.1 (t + 1)]
    have h0 := hfc t 0
    rw [add_zero] at h0
    rw [add_zero, innov_apply, hk, h0, hs t]
    simp [armaCoeff]
  | succ k =>
    have h1 := hfc (t + 1) k
    have h2 := hfc t (k + 1)
    rw [show t + 1 + 1 + k = t + 1 + (k + 1) by omega] at h1
    rw [← hφ] at hv1
    have hcoef : φ - (1 - α * βs) / ρ = -(α * ((1 - βs) / ρ)) := by
      rw [hφ]; field_simp; ring
    rw [innov_apply, h1, h2, hv1 t]
    funext w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, armaCoeff]
    linear_combination (-(φ ^ k * ε (t + 1) w)) * hcoef

/-- Cochrane (2023), Online Appendix eq. (2.8), p. 597: the debt–surplus VAR in matrix form,
`(s_{t+1}, v_{t+1}) = [[0, α], [0, (1 − α)/ρ]](s_t, v_t) + (1, −(1 − β_s)/ρ)ε_{t+1}`. -/
theorem debt_var_eq {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) (w : Ω) :
    ![s (t + 1) w, v (t + 1) w] = !![0, α; 0, (1 - α) / ρ] *ᵥ ![s t w, v t w] +
      ε (t + 1) w • ![1, -((1 - βs) / ρ)] := by
  have h1 := congrFun (hs t) w
  have h2 := congrFun (debt_ar1 hρ hs hv t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  ext i
  fin_cases i
  · simp [h1]
    ring
  · simp [h2]
    ring

/-- Cochrane (2023), Online Appendix p. 598 ("the eigenvalues of the transition matrix are
`(1 − α)/ρ` and 0"): trace `(1 − α)/ρ` and determinant `0`. -/
theorem debt_var_tr_det (ρ α : ℝ) :
    tr2 !![0, α; 0, (1 - α) / ρ] = (1 - α) / ρ ∧ det2 !![0, α; 0, (1 - α) / ρ] = 0 := by
  simp [tr2, det2]

/-- Cochrane (2023), Online Appendix p. 598 ("both less than one, so this is the joint Wold
moving-average representation"): for `|(1 − α)/ρ| < 1` the debt VAR is stable (Schur–Cohn). -/
theorem debt_var_stable {ρ α : ℝ} (h : |(1 - α) / ρ| < 1) :
    SchurStable (tr2 !![0, α; 0, (1 - α) / ρ]) (det2 !![0, α; 0, (1 - α) / ρ]) := by
  rw [(debt_var_tr_det ρ α).1, (debt_var_tr_det ρ α).2]
  exact ⟨by simp, by simpa using h⟩

/-- Cochrane (2023), Online Appendix p. 598 ("the true surplus shock can be recovered from the
history of debt"): the VAR innovation of the surplus is the structural shock,
`ε_{t+1} = s_{t+1} − E_t s_{t+1}` with `E_t s_{t+1} = αv_t`. -/
theorem shock_from_debt (𝔼 : ExpectationSystem Ω) {α : ℝ} {s v ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v) (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (t : ℕ) : 𝔼.E t (s (t + 1)) = α • v t ∧ ε (t + 1) = s (t + 1) - 𝔼.E t (s (t + 1)) := by
  have h : 𝔼.E t (s (t + 1)) = α • v t := by
    rw [hs t, map_add, map_smul, hvad t, hmds.2 t, add_zero]
  refine ⟨h, ?_⟩
  rw [h, hs t]
  abel

/-! ### MA(1) examples (p. 102 and Online Appendix §2.1.5) -/

/-- Cochrane (2023), p. 102, and Online Appendix eq. (2.9), p. 598 (tool): for
`s_{t+1} = ε_{t+1} + cε_t` the forecasts are `E_t s_{t+1} = cε_t` and `E_t s_{t+2+k} = 0`. -/
theorem ma1_forecasts (𝔼 : ExpectationSystem Ω) {c : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) :
    𝔼.E t (s (t + 1)) = c • ε t ∧ ∀ k, 𝔼.E t (s (t + 2 + k)) = 0 := by
  constructor
  · rw [hs t, map_add, map_smul, hmds.2 t, hmds.1 t, zero_add]
  · intro k
    rw [show t + 2 + k = (t + 1 + k) + 1 by omega, hs, map_add, map_smul,
      show t + 1 + k + 1 = t + 1 + (k + 1) by omega, hmds.E_future, hmds.E_future, smul_zero,
      add_zero]

/-- Cochrane (2023), p. 102 (the MA(1) `s̃_t = ε_t − θε_{t−1}`): the value of debt
`v_t = E_t ∑ ρʲ s̃_{t+1+j}` equals `−θε_t`. -/
theorem ma1_pv_forward (𝔼 : ExpectationSystem Ω) {θ ρ : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) - θ • ε t) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) w) (-θ * ε t w) := by
  have hs' : ∀ t, s (t + 1) = ε (t + 1) + (-θ) • ε t := fun t => by
    rw [hs t, neg_smul, sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := ma1_forecasts 𝔼 hmds hs' t
  have h0 : ρ ^ 0 * 𝔼.E t (s (t + 1 + 0)) w = -θ * ε t w := by
    rw [add_zero, h1]; simp
  rw [← h0]
  refine hasSum_single 0 fun j hj => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [show t + 1 + k.succ = t + 2 + k by omega, h2 k]
  simp

/-- Cochrane (2023), p. 102 ("in this example, we have `v_t = −θε_t = −ρ⁻¹ε_t`. The value of
debt reveals the true shock"): with `θ = ρ⁻¹`, `ε_t = −ρ v_t`. -/
theorem ma1_value_reveals_shock (𝔼 : ExpectationSystem Ω) {ρ : ℝ} (hρ : ρ ≠ 0)
    {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) - ρ⁻¹ • ε t)
    (t : ℕ) (w : Ω) :
    (∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) w) = -ρ⁻¹ * ε t w ∧
    ε t w = -ρ * ∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) w := by
  rw [(ma1_pv_forward 𝔼 hmds hs t w).tsum_eq]
  refine ⟨rfl, ?_⟩
  field_simp

/-- Cochrane (2023), Online Appendix eq. (2.9), p. 598: for `s_t = ε_t + θε_{t−1}`, the value of
debt is `B_{t−1}/P_t = E_t ∑ βʲ s_{t+j} = (1 + βθ)ε_t + θε_{t−1}` (dates shifted by one). -/
theorem ma1_debt_value (𝔼 : ExpectationSystem Ω) {θ β : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + θ • ε t) (t : ℕ) (w : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w)
      ((1 + β * θ) * ε (t + 1) w + θ * ε t w) := by
  obtain ⟨h1, h2⟩ := ma1_forecasts 𝔼 hmds hs (t + 1)
  have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
    rw [hs t, map_add, map_smul, hmds.1 (t + 1), hmds.E_past (Nat.le_succ t)]
  have hval : (∑ j ∈ Finset.range 2, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) =
      (1 + β * θ) * ε (t + 1) w + θ * ε t w := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, pow_zero, one_mul,
      pow_one, zero_add]
    rw [hk, show t + 1 + 1 = t + 1 + 1 by rfl, h1, hs t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← hval]
  refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
  have hj2 : 2 ≤ j := by simp at hj; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj2
  rw [show t + 1 + (2 + k) = t + 1 + 2 + k by omega, h2 k]
  simp

/-- Cochrane (2023), Online Appendix p. 598 ("if a government wishes no unexpected inflation,
the surplus process must follow `a(β) = 1 + βθ = 0`. Therefore … `θ = −R`"), `R = β⁻¹`. -/
theorem ma1_no_inflation_iff {β θ : ℝ} (hβ : β ≠ 0) : 1 + β * θ = 0 ↔ θ = -β⁻¹ := by
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- Cochrane (2023), Online Appendix eqs. (2.10)–(2.11), p. 598: with `θ = −R`, `βR = 1`, the
value of debt is `B_{t−1}/P_t = −Rε_{t−1}`: the government borrows to fund the deficit and repays
it with interest one period later. -/
theorem ma1_repaying_debt_value (𝔼 : ExpectationSystem Ω) {β R : ℝ} (hβR : β * R = 1)
    {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-R) • ε t)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) (-R * ε t w) := by
  have h := ma1_debt_value 𝔼 (β := β) hmds hs t w
  rwa [show 1 + β * -R = 0 by linarith, zero_mul, zero_add] at h

/-- Cochrane (2023), Online Appendix eq. (2.11), p. 598, survey E13: the printed middle expression
`ε_t − Rε_{t−1} + βRε_t` (with `βR = 1`) equals the correct value `−Rε_{t−1}` only when
`ε_t = 0`; the sign of `βRε_t` must be minus (`βθ = −βR`). -/
theorem printed_2_11_wrong {β R : ℝ} (hβR : β * R = 1) (e1 e0 : ℝ) :
    e1 - R * e0 + β * R * e1 = -R * e0 ↔ e1 = 0 := by
  rw [hβR]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix p. 599 ((2.13): "`(E_t − E_{t−1}) ∑ βʲ s_{t+j} = (1 − β²)w_t`,
not zero"): for `s_{t+1} = w_{t+1} + cw_t` the news in the present value is `(1 + βc)w_{t+1}`
`= a(β)w_{t+1}`; for the autoregression's fitted `c = −β` it is `(1 − β²)w_{t+1}`. -/
theorem ma1_pv_innov (𝔼 : ExpectationSystem Ω) {c β : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) (w : Ω) :
    (∑' j, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) - (∑' j, β ^ j * 𝔼.E t (s (t + 1 + j)) w) =
      (1 + β * c) * ε (t + 1) w := by
  have hs' : ∀ t, s (t + 1) = ε (t + 1) - (-c) • ε t := fun t => by
    rw [hs t, neg_smul, sub_neg_eq_add]
  rw [(ma1_debt_value 𝔼 hmds hs t w).tsum_eq, (ma1_pv_forward 𝔼 (ρ := β) hmds hs' t w).tsum_eq]
  ring

/-- Cochrane (2023), Online Appendix eq. (2.13), p. 599: the fitted MA(1) `s_t = w_t − βw_{t−1}`
has `a(β) = 1 − β²` ("you predict volatile inflation"), nonzero for `|β| < 1`. -/
theorem ma1_fitted_pv_innov (𝔼 : ExpectationSystem Ω) {β : ℝ} {s w : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 w) (hs : ∀ t, s (t + 1) = w (t + 1) + (-β) • w t) (t : ℕ) (x : Ω) :
    (∑' j, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) x) - (∑' j, β ^ j * 𝔼.E t (s (t + 1 + j)) x) =
      (1 - β ^ 2) * w (t + 1) x := by
  rw [ma1_pv_innov 𝔼 hmds hs t x]
  ring

/-- Cochrane (2023), Online Appendix eqs. (2.14)–(2.16), p. 599: for `s_t = ε_t − Rε_{t−1}` and
`B_t/P = −Rε_t`, the joint process is the VAR `(s_t, B_t/P) = [[0, 1], [0, 0]](s_{t−1}, B_{t−1}/P)
+ (ε_t, −Rε_t)`, its matrix is nilpotent (the terms converge, unlike (2.12)), the structural shock
is recovered as `ε_t = s_t − B_{t−1}/P`, and debt forecasts surpluses, `E_{t−1}s_t = B_{t−1}/P`
(debt Granger-causes surpluses although surpluses are exogenous). -/
theorem ma1_debt_var (𝔼 : ExpectationSystem Ω) {R : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-R) • ε t) (t : ℕ) (w : Ω) :
    ![s (t + 1) w, -R * ε (t + 1) w] = !![0, 1; 0, 0] *ᵥ ![s t w, -R * ε t w] +
      ![ε (t + 1) w, -R * ε (t + 1) w] ∧
    (!![(0 : ℝ), 1; 0, 0]) ^ 2 = 0 ∧
    ε (t + 1) = s (t + 1) - (-R) • ε t ∧
    𝔼.E t (s (t + 1)) = (-R) • ε t := by
  refine ⟨?_, ?_, ?_, (ma1_forecasts 𝔼 hmds hs t).1⟩
  · have h1 := congrFun (hs t) w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    ext i
    fin_cases i
    · simp [h1]
      ring
    · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hs t]
    abel

/-! ### The Hansen–Sargent formula (2.19) and the value of debt (2.18), (2.20)–(2.21) -/

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: the moving average
`s_t = ∑_{j ≤ t} aⱼ ε_{t−j}` started from a zero pre-sample (shocks dated `0, 1, 2, …`). -/
def maSeries (a : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (t + 1), a j • ε (t - j)

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601: the Hansen–Sargent coefficients
`c_k = ∑ⱼ ρʲ a_{k+1+j}` of `[(a(L) − a(ρ))L⁻¹/(1 − ρL⁻¹)]`. -/
noncomputable def hsCoeff (a : ℕ → ℝ) (ρ : ℝ) (k : ℕ) : ℝ := ∑' j, ρ ^ j * a (k + 1 + j)

/-- Cochrane (2023), Online Appendix p. 601 (tool): the series defining `c_k` converges. -/
theorem summable_hs {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : Summable (fun j => ρ ^ j * a (k + 1 + j)) := by
  have h : Summable (fun j => |a (j + (k + 1))|) :=
    (summable_nat_add_iff (f := fun j => |a j|) (k + 1)).mpr ha
  refine Summable.of_norm_bounded h fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, show k + 1 + j = j + (k + 1) by omega]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)

/-- Cochrane (2023), Online Appendix p. 601 (tool): `c_k = a_{k+1} + ρ c_{k+1}`. -/
theorem hsCoeff_rec {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : hsCoeff a ρ k = a (k + 1) + ρ * hsCoeff a ρ (k + 1) := by
  rw [hsCoeff, (summable_hs ha hρ k).tsum_eq_zero_add, hsCoeff, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show k + 1 + (j + 1) = k + 1 + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 601 (tool): `ρc_0 = a(ρ) − a_0`. -/
theorem rho_hsCoeff_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ρ * hsCoeff a ρ 0 = gen a ρ - a 0 := by
  have hs : Summable (fun j => a j * ρ ^ j) :=
    Summable.of_norm_bounded ha fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  rw [gen, hs.tsum_eq_zero_add, hsCoeff, ← tsum_mul_left]
  simp only [pow_zero, mul_one, add_sub_cancel_left]
  refine tsum_congr fun j => ?_
  rw [show 0 + 1 + j = j + 1 by omega, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 601 (tool): `|c_k| ≤ ∑|aⱼ|` for `|ρ| ≤ 1`. -/
theorem abs_hsCoeff_le {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : |hsCoeff a ρ k| ≤ ∑' j, |a j| := by
  have h : Summable (fun j => |a (j + (k + 1))|) :=
    (summable_nat_add_iff (f := fun j => |a j|) (k + 1)).mpr ha
  have h1 : |hsCoeff a ρ k| ≤ ∑' j, |a (j + (k + 1))| := by
    have hb : ∀ j, ‖ρ ^ j * a (k + 1 + j)‖ ≤ |a (j + (k + 1))| := fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, show k + 1 + j = j + (k + 1) by omega]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
    have hn : Summable (fun j => ‖ρ ^ j * a (k + 1 + j)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb h
    rw [hsCoeff, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn h)
  have h2 := ha.sum_add_tsum_nat_add (k + 1)
  have h3 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (tool): the surplus `t + 1 + i` periods
ahead splits into future shocks and the shocks already known at `t`. -/
theorem ma_split (a : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t i : ℕ) :
    maSeries a ε (t + 1 + i) = ∑ j ∈ Finset.range (i + 1), a j • ε (t + 1 + (i - j)) +
      ∑ k ∈ Finset.range (t + 1), a (k + 1 + i) • ε (t - k) := by
  rw [maSeries, show t + 1 + i + 1 = (i + 1) + (t + 1) by omega, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [show t + 1 + i - j = t + 1 + (i - j) by omega]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [show i + 1 + k = k + 1 + i by omega, show t + 1 + i - (k + 1 + i) = t - k by omega]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601: the forecast of a moving average,
`E_t s_{t+1+i} = ∑_{k ≤ t} a_{k+1+i} ε_{t−k}` (future shocks are forecast to be zero). -/
theorem ma_forecast (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    (a : ℕ → ℝ) (t i : ℕ) :
    𝔼.E t (maSeries a ε (t + 1 + i)) = ∑ k ∈ Finset.range (t + 1), a (k + 1 + i) • ε (t - k) := by
  rw [ma_split, map_add, map_sum, map_sum]
  simp only [map_smul, hmds.E_future, smul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmds.E_past (Nat.sub_le t k)]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (the Hansen–Sargent prediction formula):
`E_t ∑ ρⁱ s_{t+1+i} = ∑_k c_k ε_{t−k}`, `c_k = ∑ⱼ ρʲ a_{k+1+j}` — the operator
`[(a(L) − a(ρ))L⁻¹/(1 − ρL⁻¹)]ε_t` (here as the sum of forecasts, `|ρ| ≤ 1`). -/
theorem hansenSargent (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (w : Ω) :
    HasSum (fun i => ρ ^ i * 𝔼.E t (maSeries a ε (t + 1 + i)) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) := by
  simp only [ma_forecast 𝔼 hmds, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine hasSum_sum fun k _ => ?_
  have := ((summable_hs ha hρ k).hasSum).mul_right (ε (t - k) w)
  refine this.congr_fun fun i => ?_
  ring

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601, for the genuine (pathwise) present value:
with bounded shocks and `|ρ| < 1`, `E_t(∑ ρⁱ s_{t+1+i}) = ∑_k c_k ε_{t−k}`. -/
theorem hansenSargent_E_tsum (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    {M : ℝ} (hM : ∀ t w, |ε t w| ≤ M) {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ}
    (hρ : |ρ| < 1) (t : ℕ) (w : Ω) :
    𝔼.E t (fun x => ∑' i, ρ ^ i * maSeries a ε (t + 1 + i) x) w =
      ∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w := by
  set A := ∑' j, |a j| with hA
  have hbound : ∀ n x, |maSeries a ε n x| ≤ M * A := by
    intro n x
    rw [maSeries, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 x)
    calc ∑ j ∈ Finset.range (n + 1), |(a j • ε (n - j)) x|
        ≤ ∑ j ∈ Finset.range (n + 1), |a j| * M := Finset.sum_le_sum fun j _ => by
          rw [Pi.smul_apply, smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hM _ x) (abs_nonneg _)
      _ = M * ∑ j ∈ Finset.range (n + 1), |a j| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ M * A := mul_le_mul_of_nonneg_left
          (ha.sum_le_tsum _ fun _ _ => abs_nonneg _) hM0
  have hu : Summable (fun i => |ρ| ^ i * (M * A)) :=
    (summable_geometric_of_lt_one (abs_nonneg _) hρ).mul_right _
  have hf : ∀ i x, |(ρ ^ i • maSeries a ε (t + 1 + i)) x| ≤ |ρ| ^ i * (M * A) := by
    intro i x
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hbound _ x) (pow_nonneg (abs_nonneg _) _)
  have h := ForwardSolution.E_tsum_dom 𝔼 hu hf t w
  change 𝔼.E t (fun x => ∑' i, (ρ ^ i • maSeries a ε (t + 1 + i)) x) w = _
  rw [h, ← (hansenSargent 𝔼 hmds ha hρ.le t w).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (generating-function form): for
`|ρ| ≤ 1`, `|z| < 1`, `z ≠ ρ`, `∑_k c_k zᵏ = (a(z) − a(ρ))/(z − ρ)`. -/
theorem hansenSargent_genFn {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ z : ℝ}
    (hρ : |ρ| ≤ 1) (hz : |z| < 1) (hzρ : z ≠ ρ) :
    ∑' k, hsCoeff a ρ k * z ^ k = (gen a z - gen a ρ) / (z - ρ) := by
  set c := hsCoeff a ρ with hc
  have hCs : Summable (fun k => c k * z ^ k) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg _) hz).mul_left (∑' j, |a j|)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (abs_hsCoeff_le ha hρ k) (pow_nonneg (abs_nonneg _) _)
  set C := ∑' k, c k * z ^ k with hCdef
  have hC := hCs.hasSum
  have hC1 : HasSum (fun k => c (k + 1) * z ^ (k + 1)) (C - c 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hC
    simpa using this
  have haz : Summable (fun j => a j * z ^ j) :=
    Summable.of_norm_bounded ha fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz.le)
  have hA1 : HasSum (fun k => a (k + 1) * z ^ (k + 1)) (gen a z - a 0) := by
    have := (hasSum_nat_add_iff' 1).mpr haz.hasSum
    simpa [gen] using this
  have hzC : HasSum (fun k => c k * z ^ (k + 1)) (z * C) := by
    refine (hC.mul_left z).congr_fun fun k => ?_
    rw [pow_succ]; ring
  have hrec : HasSum (fun k => c k * z ^ (k + 1)) (gen a z - a 0 + ρ * (C - c 0)) := by
    refine (hA1.add (hC1.mul_left ρ)).congr_fun fun k => ?_
    rw [hc, hsCoeff_rec ha hρ k]
    ring
  have h1 := hzC.unique hrec
  have h2 := rho_hsCoeff_zero ha hρ
  rw [← hc] at h2
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  rw [eq_div_iff hne]
  linear_combination h1 - h2

/-- Cochrane (2023), Online Appendix eq. (2.18), p. 600 ("debt equals the ex-post as well as
expected present value of surpluses"): if `a(ρ) = 0` (`|ρ| < 1`, bounded shocks), the realised
present value `∑ ρⁱ s_{t+1+i}` equals the forecast `∑_k c_k ε_{t−k}` path by path — future shocks
drop out because the government offsets each one. -/
theorem value_expost_of_aRho_zero {ε : ℕ → Ω → ℝ} {M : ℝ} (hM : ∀ t w, |ε t w| ≤ M)
    {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0)
    (t : ℕ) (w : Ω) :
    HasSum (fun i => ρ ^ i * maSeries a ε (t + 1 + i) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) := by
  have hf : Summable (fun j => ‖a j * ρ ^ j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)) ha
  have hg : Summable (fun m => ‖ρ ^ m * ε (t + 1 + m) w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hM _ w) (pow_nonneg (abs_nonneg _) _))
      ((summable_geometric_of_lt_one (abs_nonneg _) hρ).mul_right M)
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hf hg
  have hfz : ∑' n, a n * ρ ^ n = 0 := h0
  rw [hfz, zero_mul] at hcauchy
  have hknown : HasSum (fun i => ∑ k ∈ Finset.range (t + 1), ρ ^ i * a (k + 1 + i) * ε (t - k) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) :=
    hasSum_sum fun k _ => ((summable_hs ha hρ.le k).hasSum).mul_right (ε (t - k) w)
  have hsum := hcauchy.add hknown
  rw [zero_add] at hsum
  refine hsum.congr_fun fun i => ?_
  rw [ma_split, Pi.add_apply, Finset.sum_apply, Finset.sum_apply, mul_add, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Pi.smul_apply, smul_eq_mul]
    have : ρ ^ i = ρ ^ j * ρ ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' hji]
    rw [this]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), pp. 600–601: if the moving average has
the factor `1 − ρ⁻¹L`, `a(L) = (1 − ρ⁻¹L)g(L)` (`a₀ = g₀`, `a_{k+1} = g_{k+1} − ρ⁻¹g_k`,
`∑|g_k| < ∞`, `0 < |ρ| ≤ 1`), then `a(ρ) = 0` and the Hansen–Sargent coefficients are
`c_k = −ρ⁻¹g_k`: the debt is the *invertible* moving average `v_t = −ρ⁻¹g(L)ε_t` — "the
non-invertible root cancels". -/
theorem factor_value {a g : ℕ → ℝ} (hg : Summable (fun j => |g j|)) {ρ : ℝ} (hρ0 : ρ ≠ 0)
    (hρ : |ρ| ≤ 1) (h0 : a 0 = g 0) (hk : ∀ k, a (k + 1) = g (k + 1) - ρ⁻¹ * g k) :
    gen a ρ = 0 ∧ ∀ k, hsCoeff a ρ k = -ρ⁻¹ * g k := by
  have hgs : ∀ m, Summable (fun j => ρ ^ j * g (m + j)) := fun m => by
    have h : Summable (fun j => |g (j + m)|) :=
      (summable_nat_add_iff (f := fun j => |g j|) m).mpr hg
    refine Summable.of_norm_bounded h fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, add_comm m j]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  constructor
  · have hG : Summable (fun j => g j * ρ ^ j) := (hgs 0).congr fun j => by rw [zero_add, mul_comm]
    have h1 : HasSum (fun j => g (j + 1) * ρ ^ (j + 1)) (∑' j, g j * ρ ^ j - g 0) := by
      have := (hasSum_nat_add_iff' 1).mpr hG.hasSum
      simpa using this
    have h2 : HasSum (fun j => a (j + 1) * ρ ^ (j + 1)) (∑' j, g j * ρ ^ j - g 0 -
        ∑' j, g j * ρ ^ j) := by
      refine (h1.sub hG.hasSum).congr_fun fun j => ?_
      rw [hk j, pow_succ]
      field_simp
    have h3 : HasSum (fun j => a j * ρ ^ j) (a 0 + (∑' j, g j * ρ ^ j - g 0 -
        ∑' j, g j * ρ ^ j)) := by
      rw [← hasSum_nat_add_iff' 1]
      simpa using h2
    rw [gen, h3.tsum_eq, h0]
    ring
  · intro k
    have hsplit : ∑' j, ρ ^ j * g (k + j) = g k + ρ * ∑' j, ρ ^ j * g (k + 1 + j) := by
      rw [(hgs k).tsum_eq_zero_add, ← tsum_mul_left]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine tsum_congr fun j => ?_
      rw [pow_succ, show k + (j + 1) = k + 1 + j by omega]
      ring
    have hA : hsCoeff a ρ k = ∑' j, ρ ^ j * g (k + 1 + j) - ρ⁻¹ * ∑' j, ρ ^ j * g (k + j) := by
      rw [hsCoeff, ← tsum_mul_left, ← Summable.tsum_sub (hgs (k + 1)) ((hgs k).mul_left _)]
      refine tsum_congr fun j => ?_
      rw [show k + 1 + j = j + k + 1 by omega, hk (j + k), show j + k + 1 = k + 1 + j by omega,
        show j + k = k + j by omega]
      ring
    rw [hA, hsplit]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 ("if we have `a(ρ) = 0`, one of the
numerator factors must be `(1 − ρ⁻¹L)`"): if `a(ρ) = 0` (`ρ ≠ 0`, `|ρ| ≤ 1`), then
`a(L) = (1 − ρ⁻¹L)g(L)` with `g_k = −ρc_k` (bounded). With `factor_value`, `a(ρ) = 0` iff `a(L)`
has the factor `1 − ρ⁻¹L`. -/
theorem factor_of_aRho_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ0 : ρ ≠ 0)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) :
    a 0 = -ρ * hsCoeff a ρ 0 ∧
    (∀ k, a (k + 1) = -ρ * hsCoeff a ρ (k + 1) - ρ⁻¹ * (-ρ * hsCoeff a ρ k)) ∧
    ∀ k, |-ρ * hsCoeff a ρ k| ≤ ∑' j, |a j| := by
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · have := rho_hsCoeff_zero ha hρ
    rw [h0] at this
    linarith
  · rw [hsCoeff_rec ha hρ k]
    field_simp
    ring
  · rw [abs_mul, abs_neg]
    calc |ρ| * |hsCoeff a ρ k| ≤ 1 * ∑' j, |a j| :=
          mul_le_mul hρ (abs_hsCoeff_le ha hρ k) (abs_nonneg _) zero_le_one
      _ = ∑' j, |a j| := one_mul _

/-! ### Second moments in a Hilbert space: non-recoverability and the Wold innovation -/

namespace Hilbert

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 (white noise, `ℤ`-indexed so that moving
averages have an infinite past): pairwise orthogonal with common variance `σ²`. -/
def WhiteNoise (e : ℤ → H) (σ2 : ℝ) : Prop := ∀ t u, ⟪e t, e u⟫ = if t = u then σ2 else 0

/-- Cochrane (2023), eq. (4.1), p. 87: the moving average `s_t = ∑_k a_k e_{t−k}` in the Hilbert
space of second moments. -/
noncomputable def maProc (a : ℕ → ℝ) (e : ℤ → H) (t : ℤ) : H := ∑' k : ℕ, a k • e (t - k)

/-- Cochrane (2023), p. 102 ("any statistical procedure based on the history of surpluses
alone"): the closed linear span of `s_t, s_{t−1}, s_{t−2}, …` — everything linear (including
limits) that can be computed from current and past surpluses. -/
noncomputable def pastSpan (s : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun k : ℕ => s (t - k))).topologicalClosure

/-- Cochrane (2023), p. 102 and Online Appendix (2.4), p. 597: the MA(1) `m_t = e_t − θe_{t−1}`. -/
def maOne (θ : ℝ) (e : ℤ → H) (t : ℤ) : H := e t - θ • e (t - 1)

/-- Cochrane (2023), p. 102 ("`u_t = s_t − E(s_t|s_{t−1}, s_{t−2}, …)`") and Online Appendix
(2.5), p. 597: the candidate Wold innovation `w_t = ∑_k θ⁻ᵏ m_{t−k}`. -/
noncomputable def woldInnov (θ : ℝ) (m : ℤ → H) (t : ℤ) : H := ∑' k : ℕ, (θ⁻¹) ^ k • m (t - k)

/-- Cochrane (2023), Online Appendix p. 597 (tool): white noise has variance `σ²` and constant
norm. -/
theorem WhiteNoise.norm_eq {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (t : ℤ) :
    ‖e t‖ = ‖e 0‖ := by
  have h1 := he t t
  have h2 := he 0 0
  simp only [↓reduceIte, real_inner_self_eq_norm_sq] at h1 h2
  have : ‖e t‖ ^ 2 = ‖e 0‖ ^ 2 := by rw [h1, h2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- Cochrane (2023), Online Appendix p. 597 (tool): moving averages with absolutely summable
coefficients converge in the Hilbert space. -/
theorem maProc_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    HasSum (fun k : ℕ => a k • e (t - k)) (maProc a e t) := by
  refine (Summable.of_norm ?_).hasSum
  refine (ha.mul_right ‖e 0‖).congr fun k => ?_
  rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]

/-- Cochrane (2023), p. 102 (tool): inner products pass through convergent series. -/
theorem inner_hasSum_right {f : ℕ → H} {x : H} (h : HasSum f x) (y : H) :
    HasSum (fun k => ⟪y, f k⟫) ⟪y, x⟫ := by
  simpa [innerSL_apply_apply] using h.mapL (innerSL ℝ y)

/-- Cochrane (2023), p. 102 (tool): the covariance of a past shock with the moving average,
`⟪e_{t−n}, s_t⟫ = σ² a_n`. -/
theorem inner_e_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (n : ℕ) :
    ⟪e (t - n), maProc a e t⟫ = σ2 * a n := by
  have h := inner_hasSum_right (maProc_hasSum he ha t) (e (t - n))
  refine h.unique ?_
  have : σ2 * a n = (fun k : ℕ => ⟪e (t - n), a k • e (t - k)⟫) n := by
    change σ2 * a n = ⟪e (t - n), a n • e (t - n)⟫
    rw [real_inner_smul_right, he (t - n) (t - n)]
    simp only [↓reduceIte]
    ring
  rw [this]
  refine hasSum_single n fun k hk => ?_
  rw [real_inner_smul_right, he]
  have : t - (n : ℤ) ≠ t - k := by
    intro h; exact hk (by exact_mod_cast (sub_right_inj.mp h).symm)
  simp [this]

/-- Cochrane (2023), p. 102 (tool): the members `s_{t−k}` lie in the closed past span. -/
theorem mem_pastSpan_self (s : ℤ → H) (t : ℤ) (k : ℕ) : s (t - k) ∈ pastSpan s t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Cochrane (2023), p. 102 (tool): the past span grows with the date. -/
theorem pastSpan_mono (s : ℤ → H) {t t' : ℤ} (h : t ≤ t') : pastSpan s t ≤ pastSpan s t' := by
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  have : s (t - k) = s (t' - ((k + d : ℕ) : ℤ)) := by
    congr 1; push_cast; omega
  change s (t - k) ∈ _
  rw [this]
  exact Submodule.subset_span ⟨k + d, rfl⟩

/-- Cochrane (2023), p. 102 (tool): a vector orthogonal to every `s_{t−k}` is orthogonal to the
whole closed past span. -/
theorem mem_orthogonal_pastSpan {s : ℤ → H} {t : ℤ} {x : H} (h : ∀ k : ℕ, ⟪x, s (t - k)⟫ = 0) :
    x ∈ (pastSpan s t)ᗮ := by
  have hle : pastSpan s t ≤ (ℝ ∙ x)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (h k)
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)

/-- Cochrane (2023), p. 102 (tool): a convergent series of members of the closed past span lies
in it. -/
theorem hasSum_mem_pastSpan {s : ℤ → H} {t : ℤ} {f : ℕ → H} {x : H} (h : HasSum f x)
    (hf : ∀ k, f k ∈ pastSpan s t) : x ∈ pastSpan s t :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
    (Filter.Eventually.of_forall fun _ => Submodule.sum_mem _ fun k _ => hf k)

/-- Cochrane (2023), p. 102 ("you cannot recover them from any statistical procedure based on the
history of surpluses alone") and Online Appendix pp. 597, 600 (for any moving average with
`a(ρ) = 0`): if `s_t = ∑ a_k e_{t−k}` with `a(ρ) = 0`, `|ρ| < 1`, the structural shock `e_t` is not
in the closed linear span of `s_t, s_{t−1}, …`: the vector `∑ ρᵐ e_{t−m}` is orthogonal to every
`s_{t−j}` but not to `e_t`. -/
theorem not_mem_pastSpan_of_aRho_eq_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) : e t ∉ pastSpan (maProc a e) t := by
  have hg : Summable (fun m => |ρ ^ m|) := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  set u := maProc (fun m => ρ ^ m) e t with hu
  have horth : ∀ j : ℕ, ⟪u, maProc a e (t - j)⟫ = 0 := by
    intro j
    have h := inner_hasSum_right (maProc_hasSum he ha (t - j)) u
    have hsa : Summable (fun i => a i * ρ ^ i) :=
      Summable.of_norm_bounded ha fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)
    have h2 : HasSum (fun i => ⟪u, a i • e (t - j - i)⟫) (σ2 * ρ ^ j * gen a ρ) := by
      refine (hsa.hasSum.mul_left (σ2 * ρ ^ j)).congr_fun fun i => ?_
      rw [real_inner_smul_right, real_inner_comm,
        show t - (j : ℤ) - (i : ℤ) = t - ((j + i : ℕ) : ℤ) by push_cast; ring,
        hu, inner_e_maProc he hg t (j + i), pow_add]
      ring
    rw [h.unique h2, h0, mul_zero]
  intro hmem
  have hx : u ∈ (pastSpan (maProc a e) t)ᗮ := mem_orthogonal_pastSpan horth
  have h1 := Submodule.inner_right_of_mem_orthogonal hmem hx
  have h2 : ⟪e t, u⟫ = σ2 := by
    have := inner_e_maProc he hg t 0
    simpa using this
  rw [h1] at h2
  exact hσ h2.symm

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597 (tool): `w_t = ∑ θ⁻ᵏ m_{t−k}` converges. -/
theorem woldInnov_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    HasSum (fun k : ℕ => (θ⁻¹) ^ k • maOne θ e (t - k)) (woldInnov θ (maOne θ e) t) := by
  have hq : |θ⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  refine (Summable.of_norm ?_).hasSum
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_right ((1 + |θ|) * ‖e 0‖))
  rw [norm_smul, Real.norm_eq_abs, abs_pow, maOne]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
  calc ‖e (t - k) - θ • e (t - k - 1)‖ ≤ ‖e (t - k)‖ + ‖θ • e (t - k - 1)‖ := norm_sub_le _ _
    _ = (1 + |θ|) * ‖e 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k), he.norm_eq (t - k - 1)]; ring

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597: `w_t − θ⁻¹w_{t−1} = m_t`, i.e. the
fitted moving average has root `θ⁻¹` (`= ρ` when `θ = ρ⁻¹`). -/
theorem wold_recursion [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {θ : ℝ}
    (hθ : 1 < |θ|) (t : ℤ) :
    maOne θ e t = woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) := by
  have h := woldInnov_hasSum he hθ t
  rw [← hasSum_nat_add_iff' 1] at h
  have h1 := (woldInnov_hasSum he hθ (t - 1)).const_smul θ⁻¹
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_smul, Nat.cast_zero,
    sub_zero] at h
  have heq := h.unique (h1.congr_fun fun k => ?_)
  · rw [← heq]; abel
  · rw [smul_smul, ← pow_succ']
    congr 2
    push_cast
    ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): the covariance of `w_t` with the structural
shocks, `⟪e_{t−n}, w_t⟫ = σ²` for `n = 0` and `σ²θ⁻ⁿ(1 − θ²)` for `n ≥ 1`. -/
theorem inner_e_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {θ : ℝ}
    (hθ : 1 < |θ|) (t : ℤ) (n : ℕ) :
    ⟪e (t - n), woldInnov θ (maOne θ e) t⟫ =
      σ2 * (θ⁻¹) ^ n - (if n = 0 then 0 else σ2 * θ * (θ⁻¹) ^ (n - 1)) := by
  have h := inner_hasSum_right (woldInnov_hasSum he hθ t) (e (t - n))
  refine h.unique ?_
  have hterm : ∀ k : ℕ, ⟪e (t - n), (θ⁻¹) ^ k • maOne θ e (t - k)⟫ =
      (if k = n then σ2 * (θ⁻¹) ^ n else 0) -
        (if k + 1 = n then σ2 * θ * (θ⁻¹) ^ k else 0) := by
    intro k
    rw [real_inner_smul_right, maOne, inner_sub_right, real_inner_smul_right, he, he]
    have e1 : (t - (n : ℤ) = t - k) ↔ k = n := by
      constructor
      · intro h; exact_mod_cast (sub_right_inj.mp h).symm
      · rintro rfl; rfl
    have e2 : (t - (n : ℤ) = t - k - 1) ↔ k + 1 = n := by
      constructor
      · intro h; omega
      · intro h; subst h; push_cast; ring
    by_cases h1 : k = n <;> by_cases h2 : k + 1 = n <;> simp_all <;> ring
  simp only [hterm]
  refine HasSum.sub (hasSum_ite_eq n _) ?_
  cases n with
  | zero =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact hasSum_zero
  | succ n =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, Nat.add_right_cancel_iff]
    refine (hasSum_ite_eq n (σ2 * θ * (θ⁻¹) ^ n)).congr_fun fun k => ?_
    by_cases hk : k = n
    · simp [hk]
    · simp [hk]

/-- Cochrane (2023), Online Appendix p. 597 (tool): the covariance of `w_t` with the moving
average `s_{t−j}`, `j ≥ 1`, is `σ²(1 − θ²)θ⁻ʲ a(θ⁻¹)`. -/
theorem inner_wold_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (j : ℕ) :
    ⟪woldInnov θ (maOne θ e) t, maProc a e (t - (j + 1 : ℕ))⟫ =
      σ2 * (1 - θ ^ 2) * (θ⁻¹) ^ (j + 1) * gen a θ⁻¹ := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have h := inner_hasSum_right (maProc_hasSum he ha (t - (j + 1 : ℕ)))
    (woldInnov θ (maOne θ e) t)
  have hsa : Summable (fun i => a i * (θ⁻¹) ^ i) :=
    Summable.of_norm_bounded ha fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)
  refine h.unique ((hsa.hasSum.mul_left (σ2 * (1 - θ ^ 2) * (θ⁻¹) ^ (j + 1))).congr_fun
    fun i => ?_)
  rw [real_inner_smul_right, real_inner_comm,
    show t - ((j + 1 : ℕ) : ℤ) - (i : ℤ) = t - ((j + 1 + i : ℕ) : ℤ) by push_cast; ring,
    inner_e_wold he hθ t]
  simp only [show j + 1 + i ≠ 0 by omega, ↓reduceIte, show j + 1 + i - 1 = j + i by omega]
  have hinv : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
  rw [show j + 1 + i = (j + i) + 1 by omega, pow_succ, pow_add, pow_succ]
  linear_combination (a i * σ2 * (θ⁻¹) ^ j * (θ⁻¹) ^ i * θ) * hinv

/-- Cochrane (2023), p. 102, and Online Appendix pp. 597–601 (the Wold representation fitted by
an autoregression): let `s_t = ∑ a_k e_{t−k}` (white noise `e`, variance `σ²`) have `a₀ = 1` and
an MA root at `θ⁻¹`, `a(θ⁻¹) = 0`, `|θ| > 1` (with `θ = ρ⁻¹`: `a(ρ) = 0`), and let
`m_t = e_t − θe_{t−1}` differ from `s_t` by a member of the past span (an AR filter,
`m_t = s_t − φ₁s_{t−1} − …`). Then `w_t = ∑ θ⁻ᵏ m_{t−k}` is the Wold innovation of `s`:
`w_t ⟂` the past, `s_t − w_t` lies in the past span, hence `s_t − w_t` is the orthogonal
projection of `s_t` on its past ("`u_t = s_t − E(s_t|s_{t−1}, …)`"); `w` is white noise with
variance `θ²σ²` (= `σ²/ρ²`); `m_t = w_t − θ⁻¹w_{t−1}` (the fitted root is `θ⁻¹ = ρ`, not `ρ⁻¹`);
and the structural shock `e_t` is not in the closed span of current and past surpluses. -/
theorem wold_innovation [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    (ha0 : a 0 = 1) (hroot : gen a θ⁻¹ = 0)
    (hm : ∀ t, maOne θ e t - maProc a e t ∈ pastSpan (maProc a e) (t - 1)) (t : ℤ) :
    woldInnov θ (maOne θ e) t ∈ (pastSpan (maProc a e) (t - 1))ᗮ ∧
    maProc a e t - woldInnov θ (maOne θ e) t ∈ pastSpan (maProc a e) (t - 1) ∧
    (haveI : (pastSpan (maProc a e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc a e) (t - 1)).starProjection (maProc a e t)) =
      maProc a e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    (∀ u, u < t → ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) u⟫ = 0) ∧
    maOne θ e t = woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    e t ∉ pastSpan (maProc a e) t := by
  set s := maProc a e with hs
  set w := woldInnov θ (maOne θ e) with hw
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  -- orthogonality of `w τ` to the past of `s` at `τ − 1`
  have horth : ∀ τ, w τ ∈ (pastSpan s (τ - 1))ᗮ := by
    intro τ
    refine mem_orthogonal_pastSpan fun k => ?_
    rw [show τ - 1 - (k : ℤ) = τ - ((k + 1 : ℕ) : ℤ) by push_cast; ring, hs,
      inner_wold_maProc he hθ ha τ k, hroot, mul_zero]
  -- `m τ` and `w τ` lie in the past span at `τ`
  have hmS : ∀ τ, maOne θ e τ ∈ pastSpan s τ := by
    intro τ
    have h1 := pastSpan_mono s (show τ - 1 ≤ τ by omega) (hm τ)
    have h2 : s τ ∈ pastSpan s τ := by simpa using mem_pastSpan_self s τ 0
    simpa using Submodule.add_mem _ h1 h2
  have hwS : ∀ τ, w τ ∈ pastSpan s τ := by
    intro τ
    refine hasSum_mem_pastSpan (woldInnov_hasSum he hθ τ) fun k => ?_
    exact Submodule.smul_mem _ _ (pastSpan_mono s (by omega) (hmS (τ - k)))
  have hrec := wold_recursion he hθ t
  have hsub : s t - w t ∈ pastSpan s (t - 1) := by
    have : s t - w t = -(maOne θ e t - s t) - θ⁻¹ • w (t - 1) := by
      rw [hrec]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hm t)) (Submodule.smul_mem _ _ (hwS _))
  have : (pastSpan s (t - 1)).HasOrthogonalProjection := by
    unfold pastSpan; infer_instance
  have hproj : (pastSpan s (t - 1)).starProjection (s t) = s t - w t :=
    Submodule.eq_starProjection_of_mem_orthogonal hsub (by simpa using horth t)
  -- the variance of `w`
  have hnorm : ⟪w t, w t⟫ = θ ^ 2 * σ2 := by
    have h0 : ⟪w t, s t - w t⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hsub (horth t)
    have hws : ⟪w t, s t⟫ = θ ^ 2 * σ2 := by
      have h := inner_hasSum_right (maProc_hasSum he ha t) (w t)
      have hsa : Summable (fun i => a i * (θ⁻¹) ^ i) :=
        Summable.of_norm_bounded ha fun i => by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq.le)
      have h2 : HasSum (fun i => σ2 * (1 - θ ^ 2) * (a i * (θ⁻¹) ^ i) +
          (if i = 0 then σ2 * θ ^ 2 * a 0 else 0)) (σ2 * (1 - θ ^ 2) * gen a θ⁻¹ +
          σ2 * θ ^ 2 * a 0) :=
        (hsa.hasSum.mul_left _).add (hasSum_ite_eq 0 _)
      rw [hroot, ha0] at h2
      rw [h.unique (h2.congr_fun fun i => ?_)]
      · ring
      · rw [real_inner_smul_right, real_inner_comm, inner_e_wold he hθ t]
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi; simp [ha0]; field_simp; ring
        · simp only [show i ≠ 0 by omega, ↓reduceIte, add_zero]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
          rw [Nat.succ_sub_one, pow_succ]
          field_simp
    rw [inner_sub_right] at h0
    linarith
  have hwhite : ∀ u, u < t → ⟪w t, w u⟫ = 0 := by
    intro u hu
    exact Submodule.inner_left_of_mem_orthogonal
      (pastSpan_mono s (show u ≤ t - 1 by omega) (hwS u)) (horth t)
  have hnot : e t ∉ pastSpan s t :=
    not_mem_pastSpan_of_aRho_eq_zero he hσ ha hq hroot t
  exact ⟨horth t, hsub, hproj, hnorm, hwhite, hrec, hnot⟩

/-- Cochrane (2023), Online Appendix p. 597 (the lag operator on coefficients): `L a = (0, a₀, a₁,
…)`. -/
def shiftSeq (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a k

/-- Cochrane (2023), Online Appendix p. 597 (tool): the shifted coefficients are absolutely
summable. -/
theorem summable_abs_shiftSeq {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) :
    Summable (fun k => |shiftSeq a k|) := by
  rw [← summable_nat_add_iff 1]
  exact ha

/-- Cochrane (2023), Online Appendix p. 597 (tool): the lagged moving average,
`∑ (La)_k e_{t−k} = s_{t−1}`. -/
theorem maProc_shift_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    HasSum (fun k : ℕ => shiftSeq a k • e (t - k)) (maProc a e (t - 1)) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, shiftSeq, zero_smul, sub_zero]
  refine (maProc_hasSum he ha (t - 1)).congr_fun fun k => ?_
  congr 2
  push_cast
  ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): `maProc (La) e t = maProc a e (t − 1)`. -/
theorem maProc_shiftSeq [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    maProc (shiftSeq a) e t = maProc a e (t - 1) :=
  (maProc_shift_hasSum he ha t).tsum_eq

/-- Cochrane (2023), Online Appendix eqs. (2.3)–(2.5), (2.32), pp. 595–609 (tool): if the MA
coefficients satisfy the AR(2) recursion with an MA(1) numerator, `a₀ = 1`, `a₁ − φ₁a₀ = −θ`,
`a_{k+2} − φ₁a_{k+1} − φ₂a_k = 0`, then `s_t − φ₁s_{t−1} − φ₂s_{t−2} = e_t − θe_{t−1}` in the
Hilbert space (the ARMA(2,1) `(1 − φ₁L − φ₂L²)s = (1 − θL)e`; ARMA(1,1) when `φ₂ = 0`). -/
theorem ar2_filter_eq_maOne [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {φ1 φ2 θ : ℝ} (h0 : a 0 = 1)
    (h1 : a 1 - φ1 * a 0 = -θ) (h2 : ∀ k, a (k + 2) - φ1 * a (k + 1) - φ2 * a k = 0) (t : ℤ) :
    maProc a e t - φ1 • maProc a e (t - 1) - φ2 • maProc a e (t - 1 - 1) = maOne θ e t := by
  have hs0 := maProc_hasSum he ha t
  have hs1 := maProc_shift_hasSum he ha t
  have hs2 : HasSum (fun k : ℕ => shiftSeq (shiftSeq a) k • e (t - k))
      (maProc a e (t - 1 - 1)) := by
    have := maProc_shift_hasSum he (summable_abs_shiftSeq ha) t
    rwa [maProc_shiftSeq he ha] at this
  have hc := (hs0.sub (hs1.const_smul φ1)).sub (hs2.const_smul φ2)
  refine hc.unique ?_
  have hval : (∑ k ∈ Finset.range 2, ((a k • e (t - k) - φ1 • shiftSeq a k • e (t - k)) -
      φ2 • shiftSeq (shiftSeq a) k • e (t - k))) = maOne θ e t := by
    have ha1 : a 1 = φ1 - θ := by rw [h0] at h1; linarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, shiftSeq, Nat.cast_zero,
      Nat.cast_one, sub_zero, maOne, h0, ha1, one_smul, zero_smul, smul_zero]
    rw [sub_smul]
    abel
  rw [← hval]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  have hk2 : 2 ≤ k := by simp at hk; omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  rw [show 2 + j = j + 2 by omega]
  simp only [shiftSeq, smul_smul, ← sub_smul]
  rw [show a (j + 2) - φ1 * a (j + 1) - φ2 * a j = 0 from h2 j, zero_smul]

/-- Cochrane (2023), p. 102 ("an autoregression will estimate `s̃_t = u_t − θu_{t−1}` with
`θ = ρ`"), and Online Appendix (2.13), p. 599 (with `θ = R`): for the MA(1) `s_t = e_t − θe_{t−1}`
with `|θ| > 1` (`θ = ρ⁻¹`, so `a(ρ) = 0`), the Wold innovation `w_t` is the prediction error of
`s_t` on its past, has variance `θ²σ²`, and `s_t = w_t − θ⁻¹w_{t−1}`; the structural shock is not
in the closed span of the surplus history. -/
theorem ma1_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0)
    {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    maProc (armaCoeff 0 θ) e t = maOne θ e t ∧
    (haveI : (pastSpan (maProc (armaCoeff 0 θ) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (armaCoeff 0 θ) e) (t - 1)).starProjection
        (maProc (armaCoeff 0 θ) e t)) =
      maProc (armaCoeff 0 θ) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    maProc (armaCoeff 0 θ) e t =
      woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    e t ∉ pastSpan (maProc (armaCoeff 0 θ) e) t := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have ha := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  have hfilt : ∀ τ, maProc (armaCoeff 0 θ) e τ = maOne θ e τ := by
    intro τ
    have := ar2_filter_eq_maOne he ha (φ1 := 0) (φ2 := 0) (θ := θ) rfl (by simp [armaCoeff])
      (fun k => by simp [armaCoeff]) τ
    simpa using this
  have hroot : gen (armaCoeff 0 θ) θ⁻¹ = 0 := by
    rw [ma1_aRho, mul_inv_cancel₀ hθ0, sub_self]
  have hm : ∀ τ, maOne θ e τ - maProc (armaCoeff 0 θ) e τ ∈
      pastSpan (maProc (armaCoeff 0 θ) e) (τ - 1) := by
    intro τ
    rw [hfilt τ, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ :=
    wold_innovation he hσ hθ ha rfl hroot hm t
  exact ⟨hfilt t, hproj, hnorm, (hfilt t).trans hrec, hnot⟩

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597 ("if you generate data by (2.4),
run an autoregression, and find the implied moving average, you recover (2.5)"): for the
ARMA(1,1) `(1 − θL)/(1 − φL)` with `|φ| < 1 < |θ|` (`θ = ρ⁻¹`, so `a(ρ) = 0`), the Wold
innovation `w_t` is the prediction error of `s_t` on its past, has variance `θ²σ²` (= `σ²/ρ²`,
survey E12), and the fitted representation is `s_t − φs_{t−1} = w_t − θ⁻¹w_{t−1}` — the numerator
root `ρ` replaces `ρ⁻¹`; the structural shock is not in the closed span of the surplus history. -/
theorem arma11_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {φ θ : ℝ} (hφ : |φ| < 1) (hθ : 1 < |θ|) (t : ℤ) :
    maProc (armaCoeff φ θ) e t - φ • maProc (armaCoeff φ θ) e (t - 1) =
      woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    (haveI : (pastSpan (maProc (armaCoeff φ θ) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (armaCoeff φ θ) e) (t - 1)).starProjection
        (maProc (armaCoeff φ θ) e t)) =
      maProc (armaCoeff φ θ) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    e t ∉ pastSpan (maProc (armaCoeff φ θ) e) t := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have ha := summable_abs_armaCoeff hφ θ
  have hfilt : ∀ τ, maProc (armaCoeff φ θ) e τ - φ • maProc (armaCoeff φ θ) e (τ - 1) =
      maOne θ e τ := by
    intro τ
    have := ar2_filter_eq_maOne he ha (φ1 := φ) (φ2 := 0) (θ := θ) rfl
      (by simp [armaCoeff]) (fun k => by simp [armaCoeff]; ring) τ
    simpa using this
  have hinv : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have hφθ : |φ * θ⁻¹| < 1 := by
    rw [abs_mul]
    calc |φ| * |θ⁻¹| ≤ |φ| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ < 1 := by linarith
  have hroot : gen (armaCoeff φ θ) θ⁻¹ = 0 := by
    rw [genFn_armaCoeff hφθ, mul_inv_cancel₀ hθ0, sub_self, zero_div]
  have hm : ∀ τ, maOne θ e τ - maProc (armaCoeff φ θ) e τ ∈
      pastSpan (maProc (armaCoeff φ θ) e) (τ - 1) := by
    intro τ
    rw [← hfilt τ, show maProc (armaCoeff φ θ) e τ - φ • maProc (armaCoeff φ θ) e (τ - 1) -
      maProc (armaCoeff φ θ) e τ = -(φ • maProc (armaCoeff φ θ) e (τ - 1)) by abel]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_)
    simpa using mem_pastSpan_self (maProc (armaCoeff φ θ) e) (τ - 1) 0
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ :=
    wold_innovation he hσ hθ ha rfl hroot hm t
  exact ⟨(hfilt t).trans hrec, hproj, hnorm, hnot⟩

end Hilbert

end Cochrane.DebtDeficitsInflation.Invertibility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The permanent–transitory surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 2, §2.4,
eqs. (2.27)–(2.34), pp. 607–611.

The surplus is the sum of a persistent and a transitory AR(1),
`s_t = z_t + x_t`, `z_t = η_z z_{t−1} + ε_{z,t}`, `x_t = η_x x_{t−1} + ε_{x,t}`. Letting long-run
policy respond to transitory shocks as in (2.31), `a(ρ) = β_s` and `Δπ = −β_s ε_s`; with
`β_s = 0` all debt is repaid, the univariate surplus process is a non-invertible ARMA(2,1), an
autoregression recovers the wrong (invertible) representation (2.33), while the VAR in surplus and
debt (2.34) recovers the structural shocks — and has a *positive* coefficient of surplus on lagged
debt although surpluses are exogenous.

## Main results

* `pt_forecast`, `pt_revision`: `E_t s_{t+k} = η_zᵏz_t + η_xᵏx_t`,
  `Δ_{t+1}s_{t+1+j} = η_zʲε_{z,t+1} + η_xʲε_{x,t+1}`; `pt_pv_revision` (2.30).
* `pt_eps_s`, `pt_inflation_eq`, `pt_eps_z_zero`, `pt_no_inflation` ((2.31) and the lines after it):
  `ε_s = ρ(η_z − η_x)ε_x/D`, the present-value revision is `β_s ε_s` (so `Δπ = −β_sε_s`),
  `β_s = 1/(1 − ρη_x)` gives `ε_z = 0`.
* `ptCoeff`, `pt_coeff_zero`, `pt_revision_eps_s`, `pt_aRho` ("you can quickly verify
  `a(ρ) = β_s`").
* `pt_arma21_coeffs`, `pt_arma21_time`, `pt_theta_zero` (ARMA(2,1) form and (2.32)).
* `ar2ma1Coeff`, `ar2ma1_genFn`, `pt_fitted_aRho`, `pt_fit_ar1` ((2.33), the `ρ = η_z` case,
  fitted `a(ρ) = (1 − ρ²)/((1 − η_xρ)(1 − η_zρ))`); `pt_coeff_eq_ar2ma1`.
* `pt_wold` ((2.32)–(2.33) in the Hilbert space: with `β_s = 0` the autoregression's innovation
  `w` gives `(1 − η_xL)(1 − η_zL)s = (1 − ρL)w`; the structural shock is not recoverable from the
  surplus history), `pt_wold_ar1` (with `ρ = η_z`: `s_t − η_xs_{t−1} = w_t`, "exactly the wrong
  AR(1)").
* `pt_value` (corrected (p. 611), survey E16: `v_t = E_t∑_{j≥0}ρʲs_{t+j}`), `pt_value_printed`,
  `pt_value_printed_eq`, `printed_value_ne`; `pt_var` (2.34), `pt_var_tr_det`,
  `pt_coeff_pos` (positive surplus-on-debt coefficient), `pt_debt_coeff_gt_one`,
  `pt_shocks_recoverable`, `printed_value_var_fails` (E16: the printed `v` does not obey (2.34)).
-/

namespace Cochrane.DebtDeficitsInflation.PermanentTransitory

open Filter Topology VARIdentities Invertibility
open Cochrane.DebtDeficitsInflation.Innovations (gen IsMDSNat innov innov_apply)
open scoped Matrix

variable {Ω : Type*}

/-! ### Forecasts and revisions -/

/-- Cochrane (2023), Online Appendix eqs. (2.27)–(2.29), p. 607: `E_t s_{t+k} = η_zᵏz_t + η_xᵏx_t`
for `s = z + x`, both AR(1) with martingale-difference shocks. -/
theorem pt_forecast (𝔼 : ExpectationSystem Ω) {ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (t k : ℕ) :
    𝔼.E t (z (t + k) + x (t + k)) = ηz ^ k • z t + ηx ^ k • x t := by
  rw [map_add, 𝔼.ar1_iterate hz, 𝔼.ar1_iterate hx]

/-- Cochrane (2023), Online Appendix eqs. (2.27)–(2.29), p. 607: an AR(1) driven by
martingale-difference shocks is an `IsAR1` process. -/
theorem isAR1_of_shocks (𝔼 : ExpectationSystem Ω) {η : ℝ} {z ε : ℕ → Ω → ℝ}
    (hεm : IsMDSNat 𝔼 ε) (hzad : 𝔼.Adapted z) (hz : ∀ t, z (t + 1) = η • z t + ε (t + 1)) :
    𝔼.IsAR1 η z :=
  ⟨hzad, fun t => by rw [hz t, map_add, map_smul, hzad t, hεm.2 t, add_zero]⟩

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608: the revision of surplus forecasts,
`Δ_{t+1}s_{t+1+j} = η_zʲε_{z,t+1} + η_xʲε_{x,t+1}`. -/
theorem pt_revision (𝔼 : ExpectationSystem Ω) {ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (t j : ℕ) :
    innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) = ηz ^ j • εz (t + 1) + ηx ^ j • εx (t + 1) := by
  have hzA := isAR1_of_shocks 𝔼 hεz hzad hz
  have hxA := isAR1_of_shocks 𝔼 hεx hxad hx
  rw [innov_apply, pt_forecast 𝔼 hzA hxA (t + 1) j,
    show t + 1 + j = t + (j + 1) by omega, pt_forecast 𝔼 hzA hxA t (j + 1), hz t, hx t]
  simp only [pow_succ, smul_add, smul_smul]
  abel

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608: the news in the present value of
surpluses, `Δ_{t+1}∑ρʲs_{t+1+j} = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)` (so, in the constant-discount
short-debt model, `Δπ_{t+1}` is minus this). -/
theorem pt_pv_revision (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) w)
      (εz (t + 1) w / (1 - ρ * ηz) + εx (t + 1) w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (εz (t + 1) w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (εx (t + 1) w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [pt_revision 𝔼 hεz hεx hzad hxad hz hx t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-! ### The policy response (2.31), `a(ρ) = β_s` -/

/-- Cochrane (2023), Online Appendix eq. (2.31), p. 608: the response of long-run policy to the
transitory shock, `ε_z = −k ε_x` with
`k = [1 − (1 − ρη_x)β_s](1 − ρη_z)/([1 − (1 − ρη_z)β_s](1 − ρη_x))`. -/
noncomputable def kcoef (ρ ηx ηz βs : ℝ) : ℝ :=
  (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx))

/-- Cochrane (2023), Online Appendix p. 608: the surplus innovation
`ε_s = ε_z + ε_x = ρ(η_z − η_x)ε_x/([1 − (1 − ρη_z)β_s](1 − ρη_x))`. -/
theorem pt_eps_s {ρ ηx ηz βs : ℝ} (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (hD2 : 1 - ρ * ηx ≠ 0)
    (ex : ℝ) :
    -kcoef ρ ηx ηz βs * ex + ex =
      ρ * (ηz - ηx) / ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx)) * ex := by
  rw [kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("the inflation innovation is `ΔE_{t+1}π_{t+1} =
−β_sε_{s,t+1}`"): under (2.31) the present-value revision (2.30) equals `β_s ε_s`. -/
theorem pt_inflation_eq {ρ ηx ηz βs : ℝ} (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0)
    (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) (ex : ℝ) :
    (-kcoef ρ ηx ηz βs * ex) / (1 - ρ * ηz) + ex / (1 - ρ * ηx) =
      βs * (-kcoef ρ ηx ηz βs * ex + ex) := by
  rw [kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("for `β_s = 1/(1 − ρη_x)`, we have `ε_{z,t} = 0`"):
then there is no long-run tax response and the model reduces to the AR(1). -/
theorem pt_eps_z_zero {ρ ηx ηz : ℝ} (hx1 : 1 - ρ * ηx ≠ 0) :
    kcoef ρ ηx ηz (1 / (1 - ρ * ηx)) = 0 := by
  rw [kcoef]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("for `β_s = 0`, the government fully pays back
debts, and there is no inflation"): with `β_s = 0` the present-value revision is zero. -/
theorem pt_no_inflation {ρ ηx ηz : ℝ} (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) (ex : ℝ) :
    (-kcoef ρ ηx ηz 0 * ex) / (1 - ρ * ηz) + ex / (1 - ρ * ηx) = 0 := by
  rw [pt_inflation_eq (by simp) hz1 hx1, zero_mul]

/-- Cochrane (2023), Online Appendix p. 608: the moving-average coefficients of the surplus on
`ε_s`, `a_j = (D η_xʲ − N η_zʲ)/(ρ(η_z − η_x))` with `D = [1 − (1 − ρη_z)β_s](1 − ρη_x)` and
`N = [1 − (1 − ρη_x)β_s](1 − ρη_z)` (the difference of two AR(1)s). -/
noncomputable def ptCoeff (ρ ηx ηz βs : ℝ) (j : ℕ) : ℝ :=
  ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) * ηx ^ j -
    (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) * ηz ^ j) / (ρ * (ηz - ηx))

/-- Cochrane (2023), Online Appendix p. 608: the impact coefficient is one, `a₀ = 1`. -/
theorem pt_coeff_zero {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) : ptCoeff ρ ηx ηz βs 0 = 1 := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  rw [ptCoeff]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 608: under (2.31) the surplus responds to its own
innovation `ε_s = ε_z + ε_x` with the coefficients `ptCoeff`,
`Δ_{t+1}s_{t+1+j} = a_j ε_{s,t+1}`. -/
theorem pt_revision_eps_s (𝔼 : ExpectationSystem Ω) {ρ ηz ηx βs : ℝ} (hρ : ρ ≠ 0)
    (hne : ηz ≠ ηx) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hpol : ∀ t, εz t = -kcoef ρ ηx ηz βs • εx t) (t j : ℕ) :
    innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) =
      ptCoeff ρ ηx ηz βs j • (εz (t + 1) + εx (t + 1)) := by
  rw [pt_revision 𝔼 hεz hεx hzad hxad hz hx t j, hpol (t + 1)]
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ptCoeff, kcoef]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix p. 608 ("you can quickly verify `a(ρ) = β_s`"). -/
theorem pt_aRho {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1)
    (hρx : |ρ * ηx| < 1) : gen (ptCoeff ρ ηx ηz βs) ρ = βs := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hgx := (hasSum_geometric_of_abs_lt_one hρx).mul_left
    ((1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) / (ρ * (ηz - ηx)))
  have hgz := (hasSum_geometric_of_abs_lt_one hρz).mul_left
    ((1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / (ρ * (ηz - ηx)))
  have hs := hgx.sub hgz
  rw [gen, (hs.congr_fun fun j => ?_).tsum_eq]
  · field_simp
    ring
  · simp only [ptCoeff, mul_pow]
    field_simp

/-! ### The ARMA(2,1) form (2.32) -/

/-- Cochrane (2023), Online Appendix p. 609: the MA coefficient of the condensed ARMA(2,1),
`θ = [1 − β_s(1 − ρη_x)(1 − ρη_z)]/ρ`. -/
noncomputable def ptTheta (ρ ηx ηz βs : ℝ) : ℝ := (1 - βs * (1 - ρ * ηx) * (1 - ρ * ηz)) / ρ

/-- Cochrane (2023), Online Appendix p. 609 ("we can also condense the surplus process into a
single lag operator"): the coefficients satisfy
`(1 − η_xL)(1 − η_zL)a(L) = 1 − θL`, i.e. `a₀ = 1`, `a₁ − (η_x + η_z)a₀ = −θ`,
`a_{k+2} − (η_x + η_z)a_{k+1} + η_xη_z a_k = 0`. -/
theorem pt_arma21_coeffs {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) :
    ptCoeff ρ ηx ηz βs 0 = 1 ∧
    ptCoeff ρ ηx ηz βs 1 - (ηx + ηz) * ptCoeff ρ ηx ηz βs 0 = -ptTheta ρ ηx ηz βs ∧
    ∀ k, ptCoeff ρ ηx ηz βs (k + 2) - (ηx + ηz) * ptCoeff ρ ηx ηz βs (k + 1) -
      (-(ηx * ηz)) * ptCoeff ρ ηx ηz βs k = 0 := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨pt_coeff_zero hρ hne, ?_, fun k => ?_⟩
  · simp only [ptCoeff, ptTheta]
    field_simp
    ring
  · simp only [ptCoeff]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 609, in the time domain: under (2.31) at every date,
`s_{t+2} − (η_x + η_z)s_{t+1} + η_xη_z s_t = ε_{s,t+2} − θ ε_{s,t+1}`. -/
theorem pt_arma21_time {ρ ηz ηx βs : ℝ} (hρ : ρ ≠ 0) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0)
    (hx1 : 1 - ρ * ηx ≠ 0) {z x εz εx : ℕ → Ω → ℝ}
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hpol : ∀ t, εz t = -kcoef ρ ηx ηz βs • εx t) (t : ℕ) :
    (z (t + 2) + x (t + 2)) - (ηx + ηz) • (z (t + 1) + x (t + 1)) + (ηx * ηz) • (z t + x t) =
      (εz (t + 2) + εx (t + 2)) - ptTheta ρ ηx ηz βs • (εz (t + 1) + εx (t + 1)) := by
  funext w
  have h1 := congrFun (hz (t + 1)) w
  have h2 := congrFun (hz t) w
  have h3 := congrFun (hx (t + 1)) w
  have h4 := congrFun (hx t) w
  have h5 := congrFun (hpol (t + 1)) w
  have h6 := congrFun (hpol (t + 2)) w
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    neg_mul] at h1 h2 h3 h4 h5 h6 ⊢
  rw [h1, h2, h3, h4, h6, h5]
  rw [kcoef, ptTheta]
  set D1 := 1 - (1 - ρ * ηz) * βs with hD
  set N1 := 1 - (1 - ρ * ηx) * βs with hN
  field_simp
  rw [hD, hN]
  ring

/-- Cochrane (2023), Online Appendix eq. (2.32), p. 609: with `β_s = 0` the MA numerator is
`1 − ρ⁻¹L`. -/
theorem pt_theta_zero (ρ ηx ηz : ℝ) : ptTheta ρ ηx ηz 0 = ρ⁻¹ := by
  simp [ptTheta]

/-! ### The fitted representation (2.33) -/

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609 (tool): the impulse response of the AR(2)
`1/((1 − η_xL)(1 − η_zL))`, `h_j = (η_z^{j+1} − η_x^{j+1})/(η_z − η_x)`. -/
noncomputable def ar2Impulse (ηx ηz : ℝ) (j : ℕ) : ℝ := (ηz ^ (j + 1) - ηx ^ (j + 1)) / (ηz - ηx)

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609: the MA coefficients of
`(1 − θL)/((1 − η_xL)(1 − η_zL))`. -/
noncomputable def ar2ma1Coeff (ηx ηz θ : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => ar2Impulse ηx ηz (j + 1) - θ * ar2Impulse ηx ηz j

/-- Cochrane (2023), Online Appendix eq. (2.33), p. 609: `a(ρ) = (1 − θρ)/((1 − η_xρ)(1 − η_zρ))`
for the ARMA(2,1) `(1 − θL)/((1 − η_xL)(1 − η_zL))`. -/
theorem ar2ma1_genFn {ηx ηz θ ρ : ℝ} (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1)
    (hρx : |ρ * ηx| < 1) :
    gen (ar2ma1Coeff ηx ηz θ) ρ = (1 - θ * ρ) / ((1 - ηx * ρ) * (1 - ηz * ρ)) := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hz1' : 1 - ηz * ρ ≠ 0 := by rwa [mul_comm]
  have hx1' : 1 - ηx * ρ ≠ 0 := by rwa [mul_comm]
  have hH : HasSum (fun j => ar2Impulse ηx ηz j * ρ ^ j)
      (1 / ((1 - ηx * ρ) * (1 - ηz * ρ))) := by
    have hgz := (hasSum_geometric_of_abs_lt_one hρz).mul_left (ηz / (ηz - ηx))
    have hgx := (hasSum_geometric_of_abs_lt_one hρx).mul_left (ηx / (ηz - ηx))
    convert hgz.sub hgx using 1
    · funext j
      simp only [ar2Impulse, mul_pow, pow_succ]
      field_simp
    · field_simp
      ring
  have hfirst : HasSum (fun j => ar2ma1Coeff ηx ηz θ (j + 1) * ρ ^ (j + 1))
      (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)) - 1 - θ * ρ * (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)))) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hH
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at h1
    have h0 : ar2Impulse ηx ηz 0 = 1 := by simp [ar2Impulse, div_self h]
    rw [h0] at h1
    refine (h1.sub (hH.mul_left (θ * ρ))).congr_fun fun j => ?_
    simp only [ar2ma1Coeff, pow_succ]
    ring
  have hall : HasSum (fun j => ar2ma1Coeff ηx ηz θ j * ρ ^ j)
      (1 + (1 / ((1 - ηx * ρ) * (1 - ηz * ρ)) - 1 -
        θ * ρ * (1 / ((1 - ηx * ρ) * (1 - ηz * ρ))))) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [ar2ma1Coeff] using hfirst
  rw [gen, hall.tsum_eq]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 610 ("you measure `a(ρ) = (1 − ρ²)/((1 − η_xρ)(1 − η_zρ))`,
not the correct answer `a(ρ) = 0`"): the fitted (2.33), numerator `1 − ρL`. -/
theorem pt_fitted_aRho {ηx ηz ρ : ℝ} (hne : ηz ≠ ηx) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) :
    gen (ar2ma1Coeff ηx ηz ρ) ρ = (1 - ρ ^ 2) / ((1 - ηx * ρ) * (1 - ηz * ρ)) := by
  rw [ar2ma1_genFn hne hρz hρx, sq]

/-- Cochrane (2023), Online Appendix pp. 609–610 ("in the not-unreasonable case `ρ = η_z`, you
recover exactly the wrong AR(1) response function with coefficient `η_x`"): the coefficients of
`(1 − η_zL)/((1 − η_xL)(1 − η_zL))` are `η_xʲ`. -/
theorem pt_fit_ar1 {ηx ηz : ℝ} (hne : ηz ≠ ηx) (j : ℕ) : ar2ma1Coeff ηx ηz ηz j = ηx ^ j := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  cases j with
  | zero => rfl
  | succ j =>
    simp only [ar2ma1Coeff, ar2Impulse]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 609: the surplus MA coefficients `ptCoeff` are those of
the ARMA(2,1) `(1 − θL)/((1 − η_xL)(1 − η_zL))` with `θ = ptTheta`. -/
theorem pt_coeff_eq_ar2ma1 {ρ ηx ηz βs : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx) (j : ℕ) :
    ptCoeff ρ ηx ηz βs j = ar2ma1Coeff ηx ηz (ptTheta ρ ηx ηz βs) j := by
  have h : ηz - ηx ≠ 0 := sub_ne_zero.mpr hne
  cases j with
  | zero => rw [pt_coeff_zero hρ hne]; rfl
  | succ j =>
    simp only [ptCoeff, ar2ma1Coeff, ar2Impulse, ptTheta]
    field_simp
    ring


/-! ### The Wold representation fitted by an autoregression (2.32)–(2.33) -/

namespace HilbertPT

open Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Cochrane (2023), Online Appendix p. 609 (tool): the surplus coefficients are absolutely
summable when `|η_x|, |η_z| < 1`. -/
theorem summable_abs_ptCoeff {ρ ηx ηz βs : ℝ} (hηx : |ηx| < 1) (hηz : |ηz| < 1) :
    Summable (fun j => |ptCoeff ρ ηx ηz βs j|) := by
  set c1 := (1 - (1 - ρ * ηz) * βs) * (1 - ρ * ηx) / (ρ * (ηz - ηx))
  set c2 := (1 - (1 - ρ * ηx) * βs) * (1 - ρ * ηz) / (ρ * (ηz - ηx))
  have h : Summable (fun j => |c1| * |ηx| ^ j + |c2| * |ηz| ^ j) :=
    ((summable_geometric_of_lt_one (abs_nonneg _) hηx).mul_left _).add
      ((summable_geometric_of_lt_one (abs_nonneg _) hηz).mul_left _)
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_) h
  have e : ptCoeff ρ ηx ηz βs j = c1 * ηx ^ j - c2 * ηz ^ j := by
    simp only [ptCoeff, c1, c2]; ring
  rw [e]
  refine (abs_sub _ _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_pow]

/-- Cochrane (2023), Online Appendix eqs. (2.32)–(2.33), pp. 609–610 ("you cannot recover this
surplus response from running autoregressions … you recover an estimated model (2.33) …
`ρ` not `ρ⁻¹` in the moving-average term, and the regression error `w_t` is not the true
shock"): with `β_s = 0` (all debt repaid), `0 < ρ < 1`, `|η_x|, |η_z| < 1`, `η_z ≠ η_x`, the
Wold innovation `w` of the surplus gives
`s_t − (η_x + η_z)s_{t−1} + η_xη_z s_{t−2} = w_t − ρw_{t−1}`, `s_t − w_t` is the projection of
`s_t` on its past, `w` has variance `σ²/ρ²`, and the structural shock `e_t` is not in the closed
span of current and past surpluses. -/
theorem pt_wold {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ ηx ηz : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hηx : |ηx| < 1) (hηz : |ηz| < 1) (hne : ηz ≠ ηx) (t : ℤ) :
    maProc (ptCoeff ρ ηx ηz 0) e t - (ηx + ηz) • maProc (ptCoeff ρ ηx ηz 0) e (t - 1) +
        (ηx * ηz) • maProc (ptCoeff ρ ηx ηz 0) e (t - 1 - 1) =
      woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t - ρ • woldInnov ρ⁻¹ (maOne ρ⁻¹ e) (t - 1) ∧
    (haveI : (pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) (t - 1)).starProjection
        (maProc (ptCoeff ρ ηx ηz 0) e t)) =
      maProc (ptCoeff ρ ηx ηz 0) e t - woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t ∧
    ⟪woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t, woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t⟫ = σ2 / ρ ^ 2 ∧
    e t ∉ pastSpan (maProc (ptCoeff ρ ηx ηz 0) e) t := by
  set a := ptCoeff ρ ηx ηz 0 with ha_def
  have hρne : ρ ≠ 0 := hρ0.ne'
  have ha := summable_abs_ptCoeff (ρ := ρ) (βs := 0) hηx hηz
  have hθ : 1 < |ρ⁻¹| := by
    rw [abs_inv, abs_of_pos hρ0]; exact one_lt_inv₀ hρ0 |>.mpr hρ1
  have hρz : |ρ * ηz| < 1 := by
    rw [abs_mul, abs_of_pos hρ0]; nlinarith [abs_nonneg ηz]
  have hρx : |ρ * ηx| < 1 := by
    rw [abs_mul, abs_of_pos hρ0]; nlinarith [abs_nonneg ηx]
  have hroot : gen a ρ⁻¹⁻¹ = 0 := by rw [inv_inv, ha_def, pt_aRho hρne hne hρz hρx]
  obtain ⟨hc0, hc1, hc2⟩ := pt_arma21_coeffs (βs := 0) hρne hne
  rw [pt_theta_zero] at hc1
  have hfilt : ∀ τ, maProc a e τ - (ηx + ηz) • maProc a e (τ - 1) -
      (-(ηx * ηz)) • maProc a e (τ - 1 - 1) = maOne ρ⁻¹ e τ := fun τ =>
    ar2_filter_eq_maOne he ha hc0 hc1 hc2 τ
  have hm : ∀ τ, maOne ρ⁻¹ e τ - maProc a e τ ∈ pastSpan (maProc a e) (τ - 1) := by
    intro τ
    rw [← hfilt τ, show maProc a e τ - (ηx + ηz) • maProc a e (τ - 1) -
      (-(ηx * ηz)) • maProc a e (τ - 1 - 1) - maProc a e τ =
      -((ηx + ηz) • maProc a e (τ - 1)) + (ηx * ηz) • maProc a e (τ - 1 - 1) by
        rw [neg_smul]; abel]
    refine Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · simpa using mem_pastSpan_self (maProc a e) (τ - 1) 0
    · simpa using mem_pastSpan_self (maProc a e) (τ - 1) 1
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ := wold_innovation he hσ hθ ha hc0 hroot hm t
  refine ⟨?_, hproj, ?_, hnot⟩
  · rw [inv_inv] at hrec
    rw [← hrec, ← hfilt t, neg_smul, sub_neg_eq_add]
  · rw [hnorm, inv_pow]
    field_simp

/-- Cochrane (2023), Online Appendix pp. 609–610 ("in the not-unreasonable case `ρ = η_z`, you
recover exactly the wrong AR(1) response function with coefficient `η_x` … as if the taxes were
not there at all"): with `β_s = 0` and `η_z = ρ`, the surplus satisfies `s_t − η_xs_{t−1} = w_t`,
an AR(1) in its own Wold innovation. -/
theorem pt_wold_ar1 {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ ηx : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hηx : |ηx| < 1) (hne : ρ ≠ ηx) (t : ℤ) :
    maProc (ptCoeff ρ ηx ρ 0) e t - ηx • maProc (ptCoeff ρ ηx ρ 0) e (t - 1) =
      woldInnov ρ⁻¹ (maOne ρ⁻¹ e) t := by
  have hηz : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  set s := maProc (ptCoeff ρ ηx ρ 0) e with hs
  set w := woldInnov ρ⁻¹ (maOne ρ⁻¹ e) with hw
  set y : ℤ → H := fun τ => s τ - ηx • s (τ - 1) - w τ with hy
  have hrel : ∀ τ, y τ = ρ • y (τ - 1) := by
    intro τ
    have h := (pt_wold he hσ hρ0 hρ1 hηx hηz hne τ).1
    simp only [hy]
    rw [show τ - 1 - 1 = τ - 1 - 1 by rfl] at h
    have : s τ - ηx • s (τ - 1) - w τ - ρ • (s (τ - 1) - ηx • s (τ - 1 - 1) - w (τ - 1)) =
        (s τ - (ηx + ρ) • s (τ - 1) + (ηx * ρ) • s (τ - 1 - 1)) -
          (w τ - ρ • w (τ - 1)) := by
      simp only [add_smul, mul_smul, smul_sub]
      rw [smul_comm ρ ηx]
      abel
    rw [← sub_eq_zero, this, h, sub_self]
  -- bounds
  have ha := summable_abs_ptCoeff (ρ := ρ) (βs := 0) hηx hηz
  set B1 := (∑' k, |ptCoeff ρ ηx ρ 0 k|) * ‖e 0‖
  have hsb : ∀ τ, ‖s τ‖ ≤ B1 := by
    intro τ
    have hk : ∀ k : ℕ, ‖ptCoeff ρ ηx ρ 0 k • e (τ - k)‖ = |ptCoeff ρ ηx ρ 0 k| * ‖e 0‖ :=
      fun k => by rw [norm_smul, Real.norm_eq_abs, he.norm_eq (τ - k)]
    have hn : Summable (fun k : ℕ => ‖ptCoeff ρ ηx ρ 0 k • e (τ - k)‖) :=
      (ha.mul_right ‖e 0‖).congr fun k => (hk k).symm
    refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq ?_)
    simp_rw [hk]
    exact tsum_mul_right
  have hwb : ∀ τ, ‖w τ‖ = ‖w 0‖ := by
    intro τ
    have h1 := (pt_wold he hσ hρ0 hρ1 hηx hηz hne τ).2.2.1
    have h2 := (pt_wold he hσ hρ0 hρ1 hηx hηz hne 0).2.2.1
    rw [real_inner_self_eq_norm_sq] at h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)
  set B := B1 + |ηx| * B1 + ‖w 0‖
  have hyb : ∀ τ, ‖y τ‖ ≤ B := by
    intro τ
    calc ‖y τ‖ ≤ ‖s τ‖ + ‖ηx • s (τ - 1)‖ + ‖w τ‖ := by
          simp only [hy]
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ B1 + |ηx| * B1 + ‖w 0‖ := by
          rw [norm_smul, Real.norm_eq_abs, hwb τ]
          gcongr
          · exact hsb τ
          · exact hsb _
  have hiter : ∀ n : ℕ, y t = ρ ^ n • y (t - n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, hrel (t - n), smul_smul, ← pow_succ]
      congr 2
      push_cast
      ring
  have hle : ∀ n : ℕ, ‖y t‖ ≤ ρ ^ n * B := by
    intro n
    rw [hiter n, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hρ0]
    exact mul_le_mul_of_nonneg_left (hyb _) (pow_nonneg hρ0.le _)
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const B
  have h0 : ‖y t‖ ≤ 0 := ge_of_tendsto' hlim hle
  have : y t = 0 := norm_le_zero_iff.mp h0
  simp only [hy] at this
  exact sub_eq_zero.mp this

end HilbertPT

/-! ### The value of debt and the VAR (2.34) -/

/-- Cochrane (2023), Online Appendix p. 611 (corrected, survey E16): the value of debt
`v_t = E_t∑_{j≥0}ρʲs_{t+j} = z_t/(1 − ρη_z) + x_t/(1 − ρη_x)` (the current surplus included). -/
theorem pt_value (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (z (t + j) + x (t + j)) w)
      (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (z t w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (x t w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [pt_forecast 𝔼 hz hx t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the printed sum
`E_t∑_{j≥1}ρ^{j−1}s_{t+j}` equals `η_zz_t/(1 − ρη_z) + η_xx_t/(1 − ρη_x)`, not the printed
`z_t/(1 − ρη_z) + x_t/(1 − ρη_x)`. -/
theorem pt_value_printed (𝔼 : ExpectationSystem Ω) {ρ ηz ηx : ℝ} {z x : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ηz z) (hx : 𝔼.IsAR1 ηx x) (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (z (t + 1 + j) + x (t + 1 + j)) w)
      (ηz * z t w / (1 - ρ * ηz) + ηx * x t w / (1 - ρ * ηx)) := by
  have h1 := (hasSum_geometric_of_abs_lt_one hρz).mul_left (ηz * z t w)
  have h2 := (hasSum_geometric_of_abs_lt_one hρx).mul_left (ηx * x t w)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine (h1.add h2).congr_fun fun j => ?_
  rw [show t + 1 + j = t + (j + 1) by omega, pt_forecast 𝔼 hz hx t (j + 1)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the printed-index value is
`(v_t − s_t)/ρ`. -/
theorem pt_value_printed_eq {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0)
    (hx1 : 1 - ρ * ηx ≠ 0) (zt xt : ℝ) :
    ηz * zt / (1 - ρ * ηz) + ηx * xt / (1 - ρ * ηx) =
      ((zt / (1 - ρ * ηz) + xt / (1 - ρ * ηx)) - (zt + xt)) / ρ := by
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hZ : (1 - ρ * ηz) * (zt / (1 - ρ * ηz)) = zt := mul_div_cancel₀ zt hz1
  have hX : (1 - ρ * ηx) * (xt / (1 - ρ * ηx)) = xt := mul_div_cancel₀ xt hx1
  linear_combination (-ρ⁻¹) * hZ + (-ρ⁻¹) * hX -
    (ηz * (zt / (1 - ρ * ηz)) + ηx * (xt / (1 - ρ * ηx))) * hr

/-- Cochrane (2023), Online Appendix p. 611, survey E16: the two definitions really differ —
at `z_t = 1`, `x_t = 0` they are `1/(1 − ρη_z)` and `η_z/(1 − ρη_z)`, unequal unless `η_z = 1`. -/
theorem printed_value_ne {ρ ηz : ℝ} (hz1 : 1 - ρ * ηz ≠ 0) (hηz : ηz ≠ 1) :
    1 / (1 - ρ * ηz) ≠ ηz / (1 - ρ * ηz) := by
  intro h
  rw [div_eq_div_iff hz1 hz1] at h
  exact hηz (mul_right_cancel₀ hz1 h).symm

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611: with `v = z/(1 − ρη_z) + x/(1 − ρη_x)`,
`s = z + x`, the surplus and debt follow the VAR
`s_t = (η_x + η_z − ρ⁻¹)s_{t−1} + ρ⁻¹(1 − ρη_x)(1 − ρη_z)v_{t−1} + ε_{s,t}`,
`v_t = −ρ⁻¹s_{t−1} + ρ⁻¹v_{t−1} + ε_{v,t}`, with `ε_s = ε_z + ε_x`,
`ε_v = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)`. -/
theorem pt_var {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    (z0 x0 ez ex : ℝ) :
    (ηz * z0 + ez) + (ηx * x0 + ex) =
        (ηx + ηz - ρ⁻¹) * (z0 + x0) + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) *
          (z0 / (1 - ρ * ηz) + x0 / (1 - ρ * ηx)) + (ez + ex) ∧
    (ηz * z0 + ez) / (1 - ρ * ηz) + (ηx * x0 + ex) / (1 - ρ * ηx) =
        -ρ⁻¹ * (z0 + x0) + ρ⁻¹ * (z0 / (1 - ρ * ηz) + x0 / (1 - ρ * ηx)) +
          (ez / (1 - ρ * ηz) + ex / (1 - ρ * ηx)) := by
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hZ : (1 - ρ * ηz) * (z0 / (1 - ρ * ηz)) = z0 := mul_div_cancel₀ z0 hz1
  have hX : (1 - ρ * ηx) * (x0 / (1 - ρ * ηx)) = x0 := mul_div_cancel₀ x0 hx1
  constructor
  · linear_combination (ηx * z0 + ηz * x0) * hr - ρ⁻¹ * (1 - ρ * ηx) * hZ -
      ρ⁻¹ * (1 - ρ * ηz) * hX
  · linear_combination (-ρ⁻¹) * hZ + (-ρ⁻¹) * hX -
      (ηz * (z0 / (1 - ρ * ηz)) + ηx * (x0 / (1 - ρ * ηx))) * hr

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611, for the model's processes: if
`z_{t+1} = η_z z_t + ε_{z,t+1}`, `x_{t+1} = η_x x_t + ε_{x,t+1}`, then `(s, v)` obey the VAR (2.34)
at every date and state. -/
theorem pt_var_process {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0)
    {z x εz εx : ℕ → Ω → ℝ} (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1))
    (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1)) (t : ℕ) (w : Ω) :
    z (t + 1) w + x (t + 1) w =
        (ηx + ηz - ρ⁻¹) * (z t w + x t w) + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) *
          (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) + (εz (t + 1) w + εx (t + 1) w) ∧
    z (t + 1) w / (1 - ρ * ηz) + x (t + 1) w / (1 - ρ * ηx) =
        -ρ⁻¹ * (z t w + x t w) + ρ⁻¹ * (z t w / (1 - ρ * ηz) + x t w / (1 - ρ * ηx)) +
          (εz (t + 1) w / (1 - ρ * ηz) + εx (t + 1) w / (1 - ρ * ηx)) := by
  have h1 := congrFun (hz t) w
  have h2 := congrFun (hx t) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2]
  exact pt_var hρ hz1 hx1 _ _ _ _

/-- Cochrane (2023), Online Appendix p. 611 ("the construction already gives us a diagonalization
of the VAR transition matrix verifying stable eigenvalues `η_z`, `η_x`"): the (2.34) matrix has
trace `η_x + η_z` and determinant `η_xη_z`. -/
theorem pt_var_tr_det {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) :
    tr2 !![ηx + ηz - ρ⁻¹, ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz); -ρ⁻¹, ρ⁻¹] = ηx + ηz ∧
    det2 !![ηx + ηz - ρ⁻¹, ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz); -ρ⁻¹, ρ⁻¹] = ηx * ηz := by
  simp only [tr2, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · ring
  · field_simp
    ring

/-- Cochrane (2023), Online Appendix p. 611 ("the regression coefficient of surplus `s_t` on
value `v_{t−1}` is positive"): `ρ⁻¹(1 − ρη_x)(1 − ρη_z) > 0` for `ρ > 0`, `ρη_x, ρη_z < 1` —
although surpluses are exogenous, debt Granger-causes surpluses. -/
theorem pt_coeff_pos {ρ ηz ηx : ℝ} (hρ : 0 < ρ) (hx : ρ * ηx < 1) (hz : ρ * ηz < 1) :
    0 < ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) := by
  have h1 : 0 < 1 - ρ * ηx := by linarith
  have h2 : 0 < 1 - ρ * ηz := by linarith
  positivity

/-- Cochrane (2023), Online Appendix p. 611 ("the coefficient `ρ⁻¹ > 1` of debt on lagged debt
warns us to be careful about misinterpreting individual regression coefficients for
eigenvalues"): `ρ⁻¹ > 1` for `0 < ρ < 1`, while both eigenvalues `η_z, η_x` are stable. -/
theorem pt_debt_coeff_gt_one {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 1 < ρ⁻¹ :=
  (one_lt_inv₀ hρ0).mpr hρ1

/-- Cochrane (2023), Online Appendix p. 611 ("the structural shocks `ε_{z,t}, ε_{x,t}` are
recoverable from the regression residuals"): the VAR innovations
`u_s = ε_z + ε_x`, `u_v = ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)` determine the structural shocks when
`η_z ≠ η_x`. -/
theorem pt_shocks_recoverable {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hne : ηz ≠ ηx)
    (hz1 : 1 - ρ * ηz ≠ 0) (hx1 : 1 - ρ * ηx ≠ 0) {ez ex us uv : ℝ} (hus : us = ez + ex)
    (huv : uv = ez / (1 - ρ * ηz) + ex / (1 - ρ * ηx)) :
    ex = (uv - us / (1 - ρ * ηz)) / (1 / (1 - ρ * ηx) - 1 / (1 - ρ * ηz)) ∧ ez = us - ex := by
  have hBA : 1 / (1 - ρ * ηx) - 1 / (1 - ρ * ηz) ≠ 0 := by
    rw [div_sub_div _ _ hx1 hz1]
    refine div_ne_zero ?_ (mul_ne_zero hx1 hz1)
    intro h
    have : ρ * (ηx - ηz) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hρ h'
    · exact hne (by linarith)
  constructor
  · rw [eq_div_iff hBA, huv, hus]
    simp only [div_eq_mul_inv]
    ring
  · rw [hus]; ring

/-- Cochrane (2023), Online Appendix eq. (2.34), p. 611, survey E16: with the printed definition
`v'_t = η_zz_t/(1 − ρη_z) + η_xx_t/(1 − ρη_x)` the VAR (2.34) fails — at `z = 1`, `x = 0` and no
shocks the next surplus is `η_z`, but (2.34) predicts
`(η_x + η_z − ρ⁻¹) + ρ⁻¹(1 − ρη_x)(1 − ρη_z)·η_z/(1 − ρη_z) = η_z + (η_x − ρ⁻¹)(1 − η_z)`. -/
theorem printed_value_var_fails {ρ ηz ηx : ℝ} (hρ : ρ ≠ 0) (hz1 : 1 - ρ * ηz ≠ 0)
    (hηz : ηz ≠ 1) (hηx : ηx ≠ ρ⁻¹) :
    (ηx + ηz - ρ⁻¹) * 1 + ρ⁻¹ * (1 - ρ * ηx) * (1 - ρ * ηz) * (ηz / (1 - ρ * ηz)) ≠ ηz := by
  intro h
  have hr : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have hW : (1 - ρ * ηz) * (ηz / (1 - ρ * ηz)) = ηz := mul_div_cancel₀ ηz hz1
  have key : (ηx - ρ⁻¹) * (1 - ηz) = 0 := by
    linear_combination h + ηx * ηz * hr - ρ⁻¹ * (1 - ρ * ηx) * hW
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hηx (by linarith)
  · exact hηz (by linarith)

end Cochrane.DebtDeficitsInflation.PermanentTransitory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the innovation-accounting and the VAR/invertibility modules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2–4.3, pp. 87–112, and
Online Appendix Chapter 2, §§2.1–2.4, pp. 594–611.

The Hansen–Roberds–Sargent identity `Δπ_{t+1} = −a(ρ)ε_{t+1}` (`SurplusMA.innov_infl_eq`, for
moving averages in `ℤ`-indexed shocks) is applied to the surplus processes of the Online
Appendix (ARMA(1,1), MA(1), permanent–transitory), which are written in `ℕ`-indexed
martingale-difference shocks and in "revision form" `Δ_{t+1}s_{t+1+j} = a_j ε_{t+1}`.

## Main results

* Variant definitions: `armaCoeff_zero_eq_ma1Coeff` (`Invertibility.armaCoeff 0 θ` is
  `SurplusMA.ma1Coeff θ`), `armaCoeff_ar1`, `gen_armaCoeff_ar1`; `isMDSNat_iff_shockMDS` (the
  VAR shock condition `ShockMDS` plus adaptedness is `IsMDSNat` componentwise).
* `presample`, `isMDS_presample`, `maSeries_isMA`: the zero-presample moving average
  `Invertibility.maSeries` is an `Innovations.IsMA`; `innov_PV_maSeries` ((4.2) for it) and
  `hansenSargent_innov` (the Hansen–Sargent forecasts (2.19) revise by `a(ρ)ε_{t+1}`).
* `innov_infl_of_revision`: the HRS identity for any surplus in revision form;
  `arma11_innov_infl` (`Δπ = −β_sε`, A2 (2.3)), `ma1_revision`, `ma1_innov_infl`,
  `ma1_innov_infl_repay` (p. 102), `pt_innov_infl` (A2 p. 608, `Δπ = −β_sε_s`, the link the
  permanent–transitory module's `pt_inflation_eq` relies on), `pt_pv_revision_via_ar1`.
* `condDown_flow`: with the flow identity (3.17) holding ex post, the present value computed with
  any information set converges to `E^I_t v_t`, hence to `v_t` iff `v_t ∈ I_t` (p. 101, matching
  `ConditioningDown.condDown_iff`).
-/

namespace Cochrane.DebtDeficitsInflation.Links

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA (SimpleModel InnovTVC ma1Coeff)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Variant definitions of the same objects -/

/-- Cochrane (2023), p. 88, and Online Appendix eq. (2.3), p. 595: the MA(1) coefficients
`1 − θL` of the ARMA family `(1 − θL)/(1 − φL)` at `φ = 0` are the MA(1) coefficients of
§4.2. -/
theorem armaCoeff_zero_eq_ma1Coeff (θ : ℝ) : Invertibility.armaCoeff 0 θ = ma1Coeff θ := by
  funext j
  rcases j with _ | _ | j <;> simp [Invertibility.armaCoeff, ma1Coeff]

/-- Cochrane (2023), eq. (4.3), p. 88, and Online Appendix eq. (2.3), p. 595: at `θ = 0` the
ARMA coefficients are those of the AR(1), `aⱼ = φʲ`. -/
theorem armaCoeff_ar1 (φ : ℝ) : Invertibility.armaCoeff φ 0 = fun j => φ ^ j := by
  funext j
  rcases j with _ | j <;> simp [Invertibility.armaCoeff, pow_succ']

/-- Cochrane (2023), eq. (4.3), p. 88, and Online Appendix eq. (2.3), p. 595: the two closed
forms of the AR(1) generating function agree, `a(z) = 1/(1 − zφ) = (1 − 0·z)/(1 − φz)`. -/
theorem gen_armaCoeff_ar1 {φ z : ℝ} (h : |z * φ| < 1) :
    gen (Invertibility.armaCoeff φ 0) z = 1 / (1 - z * φ) ∧
    gen (Invertibility.armaCoeff φ 0) z = (1 - 0 * z) / (1 - φ * z) := by
  refine ⟨by rw [armaCoeff_ar1, SurplusMA.gen_ar1 h], ?_⟩
  exact Invertibility.genFn_armaCoeff (by rwa [mul_comm])

/-- Cochrane (2023), p. 88, and Online Appendix p. 600: the two MA(1) generating functions agree,
`a(ρ) = 1 − θρ`. -/
theorem gen_armaCoeff_zero (θ ρ : ℝ) :
    gen (Invertibility.armaCoeff 0 θ) ρ = gen (ma1Coeff θ) ρ ∧
    gen (Invertibility.armaCoeff 0 θ) ρ = 1 - θ * ρ :=
  ⟨by rw [armaCoeff_zero_eq_ma1Coeff], by rw [armaCoeff_zero_eq_ma1Coeff, SurplusMA.gen_ma1]⟩

/-- Cochrane (2023), eq. (4.17), p. 104, and eq. (4.1), p. 87: the VAR shocks are martingale
differences in every coordinate (`IsMDSNat`) iff they are unforecastable (`ShockMDS`) and
adapted. -/
theorem isMDSNat_iff_shockMDS {κ : Type*} (ε : ℕ → κ → Ω → ℝ) :
    (∀ i, IsMDSNat 𝔼 (fun t => ε t i)) ↔
      VARIdentities.ShockMDS 𝔼 ε ∧ ∀ t i, 𝔼.E t (ε t i) = ε t i :=
  ⟨fun h => ⟨fun t i => (h i).2 t, fun t i => (h i).1 t⟩,
    fun h i => ⟨fun t => h.2 t i, fun t => h.1 t i⟩⟩

/-! ### The zero-presample moving average and the Hansen–Sargent formula -/

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: an `ℕ`-indexed shock
`e_0, e_1, …` placed on the integers, with zero shocks before date `0`. -/
def presample (e : ℕ → Ω → ℝ) (k : ℤ) : Ω → ℝ := if 0 ≤ k then e k.toNat else 0

/-- Cochrane (2023), eq. (4.1), p. 87: `presample e (t + 1) = e (t + 1)`. -/
theorem presample_succ (e : ℕ → Ω → ℝ) (t : ℕ) : presample e ((t : ℤ) + 1) = e (t + 1) := by
  have h0 : (0 : ℤ) ≤ (t : ℤ) + 1 := by omega
  have h1 : ((t : ℤ) + 1).toNat = t + 1 := by omega
  simp only [presample, h0, ↓reduceIte, h1]

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference, extended by zero to
the past, is a martingale difference on `ℤ`. -/
theorem isMDS_presample {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e) : IsMDS 𝔼 (presample e) := by
  refine ⟨fun t k hk => ?_, fun t => ?_⟩
  · by_cases h0 : (0 : ℤ) ≤ k
    · simp only [presample, h0, ↓reduceIte]
      exact h.E_past (by omega)
    · simp only [presample, h0, ↓reduceIte, map_zero]
  · rw [presample_succ]
    exact h.2 t

/-- Cochrane (2023), eq. (4.1), p. 87: the presample shock inherits a bound. -/
theorem abs_presample_le {e : ℕ → Ω → ℝ} {M : ℝ} (hM : ∀ t ω, |e t ω| ≤ M) (k : ℤ) (ω : Ω) :
    |presample e k ω| ≤ M := by
  by_cases h0 : (0 : ℤ) ≤ k
  · simp only [presample, h0, ↓reduceIte]
    exact hM _ ω
  · simp only [presample, h0, ↓reduceIte, Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans (hM 0 ω)

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: the zero-presample moving
average `s_t = ∑_{j ≤ t} aⱼ e_{t−j}` of the Invertibility module is a moving average (4.1) in the
`ℤ`-indexed shock `presample e`. -/
theorem maSeries_isMA {a : ℕ → ℝ} (ha : Summable fun j => |a j|) (e : ℕ → Ω → ℝ) :
    IsMA a (presample e) (Invertibility.maSeries a e) := by
  refine ⟨ha, fun t ω => ?_⟩
  have hz : ∀ j ∉ Finset.range (t + 1), a j * presample e ((t : ℤ) - j) ω = 0 := by
    intro j hj
    have hj' : t < j := by simpa using hj
    have h0 : ¬ (0 : ℤ) ≤ (t : ℤ) - j := by omega
    simp only [presample, h0, ↓reduceIte, Pi.zero_apply, mul_zero]
  rw [tsum_eq_sum hz]
  simp only [Invertibility.maSeries, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have h0 : (0 : ℤ) ≤ (t : ℤ) - j := by omega
  have h1 : ((t : ℤ) - j).toNat = t - j := by omega
  simp only [presample, h0, ↓reduceIte, h1]

/-- Cochrane (2023), eq. (4.2), p. 87, for the zero-presample moving average of the Online
Appendix: `∑ ρʲ Δ_{t+1} s_{t+1+j} = a(ρ) e_{t+1}` (`|ρ| ≤ 1`, bounded shocks). -/
theorem innov_PV_maSeries {e : ℕ → Ω → ℝ} (he : IsMDSNat 𝔼 e) {M : ℝ}
    (hM : ∀ t ω, |e t ω| ≤ M) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (Invertibility.maSeries a e (t + 1 + j)) ω)
      (gen a ρ * e (t + 1) ω) := by
  have h := innov_PV_termwise 𝔼 (maSeries_isMA ha e) (isMDS_presample 𝔼 he)
    (abs_presample_le hM) hρ t ω
  rwa [presample_succ] at h

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601, and eq. (4.2), p. 87: the Hansen–Sargent
forecasts revise by `a(ρ)` times the shock. With `HS_t = ∑_{k ≤ t} c_k e_{t−k}` the forecast
`E_t ∑ ρⁱ s_{t+1+i}`, `s_{t+1} + ρ HS_{t+1} − HS_t = a(ρ) e_{t+1}`. -/
theorem hansenSargent_innov {e : ℕ → Ω → ℝ} (he : IsMDSNat 𝔼 e) {M : ℝ}
    (hM : ∀ t ω, |e t ω| ≤ M) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Invertibility.maSeries a e (t + 1) ω +
        ρ * ∑ k ∈ Finset.range (t + 1 + 1), Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω -
      ∑ k ∈ Finset.range (t + 1), Invertibility.hsCoeff a ρ k * e (t - k) ω =
      gen a ρ * e (t + 1) ω := by
  set s := Invertibility.maSeries a e with hsdef
  have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
    rw [hsdef, Invertibility.maSeries, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he.E_past (Nat.sub_le _ _)]
  have h1 := Invertibility.hansenSargent 𝔼 he ha hρ (t + 1) ω
  have h0 := Invertibility.hansenSargent 𝔼 he ha hρ t ω
  have hA : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * ∑ k ∈ Finset.range (t + 1 + 1),
        Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero, hk,
      add_sub_cancel_left]
    refine (h1.mul_left ρ).congr_fun fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega, pow_succ]
    ring
  have hI := innov_PV_maSeries 𝔼 he hM ha hρ t ω
  have hD : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * ∑ k ∈ Finset.range (t + 1 + 1),
        Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω -
        ∑ k ∈ Finset.range (t + 1), Invertibility.hsCoeff a ρ k * e (t - k) ω) := by
    refine (hA.sub h0).congr_fun fun j => ?_
    rw [innov_apply, Pi.sub_apply]
    ring
  exact hD.unique hI

/-! ### The HRS identity applied to the Online-Appendix surplus processes -/

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992), for a surplus given in
revision form: in the simple model, if `Δ_{t+1}s_{t+1+j} = aⱼ e` with `∑ aⱼρʲ` convergent, then
`Δ_{t+1}π_{t+1} = −a(ρ) e`. -/
theorem innov_infl_of_revision {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0)) {a : ℕ → ℝ}
    {e : Ω → ℝ} (hrev : ∀ j, innov 𝔼 t (s (t + 1 + j)) = a j • e)
    (ha : Summable fun j => a j * ρ ^ j) :
    innov 𝔼 t (infl (t + 1)) ω = -(gen a ρ * e ω) := by
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) (gen a ρ * e ω) := by
    refine (ha.hasSum.mul_right (e ω)).congr_fun fun j => ?_
    simp only [hrev j, Pi.smul_apply, smul_eq_mul]
    ring
  exact inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) hT (seriesTo_of_hasSum hS)

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 ("`β_s` controls how much of a shock is
repaid, and how much results in inflation") with eq. (4.2), p. 87: if the surplus follows the
ARMA(1,1) of (2.1)–(2.3), `s_{t+1} = αv_t + ε_{t+1}`, `ρv_{t+1} = v_t + β_sε_{t+1} − s_{t+1}`
(`0 < α < 2`), then in the simple model unexpected inflation is `Δπ_{t+1} = −β_s ε_{t+1}`. -/
theorem arma11_innov_infl {ρ c α βs : ℝ} {v' r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v' r rn infl s) (hT : InnovTVC 𝔼 ρ v') (hρ : ρ ≠ 0) (hα0 : 0 < α)
    (hα2 : α < 2) {v ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v)
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -βs • ε (t + 1) := by
  funext ω
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  rw [innov_infl_of_revision 𝔼 hm (hT t ω)
    (fun j => Invertibility.arma11_revision 𝔼 hρ hmds hvad hs hv t j)
    (Invertibility.armaCoeff_hasSum (θ := (1 - α * βs) / ρ) h).summable,
    Invertibility.arma11_aRho_params hρ hα0 hα2]
  simp

/-- Cochrane (2023), p. 102, and Online Appendix eq. (2.9), p. 598: the MA(1)
`s_{t+1} = ε_{t+1} + cε_t` in revision form, `Δ_{t+1}s_{t+1+j} = aⱼε_{t+1}` with the MA(1)
coefficients `1, c, 0, 0, …` (`armaCoeff 0 (−c)`). -/
theorem ma1_revision {c : ℝ} {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = Invertibility.armaCoeff 0 (-c) j • ε (t + 1) := by
  obtain ⟨h0, h0'⟩ := Invertibility.ma1_forecasts 𝔼 hmds hs t
  obtain ⟨h1, h1'⟩ := Invertibility.ma1_forecasts 𝔼 hmds hs (t + 1)
  rcases j with _ | _ | k
  · have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
      rw [hs t, map_add, map_smul, hmds.1 (t + 1), hmds.E_past (Nat.le_succ t)]
    rw [add_zero, innov_apply, hk, h0, hs t]
    simp [Invertibility.armaCoeff]
  · have h2 := h0' 0
    rw [add_zero] at h2
    rw [show t + 1 + (0 + 1) = t + 2 by omega, innov_apply, h2, show t + 2 = t + 1 + 1 by omega,
      h1]
    simp [Invertibility.armaCoeff]
  · have h2 := h0' (k + 1)
    have h3 := h1' k
    rw [show t + 1 + (k + 1 + 1) = t + 1 + 2 + k by omega, innov_apply, h3,
      show t + 1 + 2 + k = t + 2 + (k + 1) by omega, h2]
    simp [Invertibility.armaCoeff]

/-- Cochrane (2023), p. 102, and Online Appendix eqs. (2.9)–(2.13), pp. 598–599, with eq. (4.2),
p. 87: for the MA(1) `s_{t+1} = ε_{t+1} + cε_t`, unexpected inflation in the simple model is
`Δπ_{t+1} = −(1 + cρ)ε_{t+1} = −a(ρ)ε_{t+1}`. -/
theorem ma1_innov_infl {ρ c0 c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c0 v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -(1 + c * ρ) • ε (t + 1) := by
  funext ω
  have h : |(0 : ℝ) * ρ| < 1 := by simp
  rw [innov_infl_of_revision 𝔼 hm (hT t ω) (ma1_revision 𝔼 hmds hs t)
    (Invertibility.armaCoeff_hasSum (θ := -c) h).summable, Invertibility.ma1_aRho]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 102 ("`θ = ρ⁻¹` ... the government repays its debts"): for the MA(1)
`s_{t+1} = ε_{t+1} − ρ⁻¹ε_t`, `a(ρ) = 0` and there is no unexpected inflation. -/
theorem ma1_innov_infl_repay {ρ c0 : ℝ} (hρ : ρ ≠ 0) {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c0 v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-ρ⁻¹) • ε t) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = 0 := by
  rw [ma1_innov_infl 𝔼 hm hT hmds hs t, neg_mul, inv_mul_cancel₀ hρ, add_neg_cancel, neg_zero,
    zero_smul]

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608, from the AR(1) news formula of §4.2.6
(`SurplusProcessFacts.ar1_innov_sum`): `∑ρʲΔ(z + x)_{t+1+j} = Δz_{t+1}/(1 − ρη_z) +
Δx_{t+1}/(1 − ρη_x)`, with `Δz_{t+1} = ε_{z,t+1}` and `Δx_{t+1} = ε_{x,t+1}` (so this is
`PermanentTransitory.pt_pv_revision`). -/
theorem pt_pv_revision_via_ar1 {ρ ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) ω)
      (innov 𝔼 t (z (t + 1)) ω / (1 - ρ * ηz) + innov 𝔼 t (x (t + 1)) ω / (1 - ρ * ηx)) ∧
    innov 𝔼 t (z (t + 1)) = εz (t + 1) ∧ innov 𝔼 t (x (t + 1)) = εx (t + 1) := by
  have hzA := PermanentTransitory.isAR1_of_shocks 𝔼 hεz hzad hz
  have hxA := PermanentTransitory.isAR1_of_shocks 𝔼 hεx hxad hx
  refine ⟨?_, ?_, ?_⟩
  · refine ((SurplusProcessFacts.ar1_innov_sum 𝔼 hρz hzA t ω).add
      (SurplusProcessFacts.ar1_innov_sum 𝔼 hρx hxA t ω)).congr_fun fun j => ?_
    rw [map_add, Pi.add_apply]
    ring
  · rw [innov_apply, hzad (t + 1), hzA.2 t, hz t]
    abel
  · rw [innov_apply, hxad (t + 1), hxA.2 t, hx t]
    abel

/-- Cochrane (2023), Online Appendix p. 608 ("the inflation innovation is
`ΔE_{t+1}π_{t+1} = −β_sε_{s,t+1}`"): in the simple model with the permanent–transitory surplus
`s = z + x` and the policy response (2.31), `ε_z = −kε_x`, unexpected inflation is
`Δπ_{t+1} = −β_s(ε_{z,t+1} + ε_{x,t+1})`. This is the HRS identity (4.2) applied to the
present-value revision (2.30), via `PermanentTransitory.pt_inflation_eq`. -/
theorem pt_innov_infl {ρ c ηz ηx βs : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hsum : ∀ t, s t = z t + x t)
    (hpol : ∀ t, εz t = -PermanentTransitory.kcoef ρ ηx ηz βs • εx t)
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -βs • (εz (t + 1) + εx (t + 1)) := by
  funext ω
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hS := PermanentTransitory.pt_pv_revision 𝔼 hεz hεx hzad hxad hz hx hρz hρx t ω
  have hS' : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (εz (t + 1) ω / (1 - ρ * ηz) + εx (t + 1) ω / (1 - ρ * ηx)) :=
    hS.congr_fun fun j => by rw [hsum]
  rw [inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) (hT t ω)
    (seriesTo_of_hasSum hS')]
  have hp := congrFun (hpol (t + 1)) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  rw [hp, PermanentTransitory.pt_inflation_eq hD1 hz1 hx1]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hp]
  ring

/-! ### Information sets: the flow identity and conditioning down -/

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602, with eq. (3.19),
p. 64: because the flow identity (3.17) holds ex post, under people's information `𝔼Ω` (where
`v` is known) the present value of `s̃ + g − r` converges to `v_t`, while under ANY information
system `𝔼I` (with its terminal condition) it converges to `E^I_t v_t` — hence to `v_t` iff
`v_t ∈ I_t` (the conditioning-down condition of `ConditioningDown.condDown_iff`). -/
theorem condDown_flow {𝔼I 𝔼Ω : ExpectationSystem Ω} {ρ : ℝ} {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼Ω.Adapted v) {t : ℕ} {ω : Ω}
    (hTΩ : Tendsto (fun T => ρ ^ T * 𝔼Ω.E t (v (t + T)) ω) atTop (𝓝 0))
    (hTI : Tendsto (fun T => ρ ^ T * 𝔼I.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼Ω.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) ∧
    SeriesTo (fun j => ρ ^ j * 𝔼I.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (𝔼I.E t (v t) ω) ∧
    (SeriesTo (fun j => ρ ^ j * 𝔼I.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) ↔ 𝔼I.E t (v t) ω = v t ω) := by
  have hI := rec_seriesTo_map (𝔼I.E t) ((flow_iff_recursion ρ v r g s).1 h) hTI
  refine ⟨pv_expected_combined 𝔼Ω h hv hTΩ, hI, ⟨fun h1 => hI.unique h1, fun he => ?_⟩⟩
  rw [← he]
  exact hI

end Cochrane.DebtDeficitsInflation.Links

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Measure-theoretic conditional expectations

Cochrane (2023), Ch. 2, §2.3–2.4, pp. 29–30 (expectations `E_t`, the news operator
`ΔE_{t+1} = E_{t+1} − E_t` of eq. (2.13), forward-looking present values) and §2.7, p. 42 (AR(1)
surpluses). The core `ExpectationSystem` defines `E_t` on **all** functions `Ω → ℝ` with exact
equalities; on a countable `Ω` this forces finitely supported forecasts (proved in the Woodford
Chapter 2 project, `SGUStochasticMeasure.expectationSystem_finite_support`), so no genuine
infinite-horizon model with nondegenerate shocks fits it. This module is an **additive bridge**:
a probability space with a filtration and Mathlib's `condExp`, with every property stated in its
almost-everywhere form. Existing core theorems are untouched.

## How to use (API)

* `MeasExpectationSystem Ω` (fields `P : ProbabilityMeasure Ω`, `𝓕 : Filtration ℕ _`);
  `S.μ` the measure, `S.E t x = S.μ[x | S.𝓕 t]`.
* Carriers: plain functions `Ω → ℝ` and processes `ℕ → Ω → ℝ`; `S.BddRV x` (a.e. measurable,
  essentially bounded; closed under `add`, `sub`, `smul`, `mul`, `sq`, `E`; `.integrable`),
  `S.BddProc x` (uniform essential bound), Mathlib's `StronglyAdapted S.𝓕 x` (adapted).
* Axioms (a.e.): `E_add`, `E_sub`, `E_smul`, `E_const` (exact), `E_zero`, `E_mono`, `E_tower`,
  `E_known` (exact), `E_E_self`, `E_of_stronglyMeasurable` (exact), `E_of_aestronglyMeasurable`,
  `E_congr`, `E_pullOut`, `abs_E_le`, `integral_E`, `stronglyMeasurable_E`, `integrable_E`.
* News: `innov t x = ΔE_{t+1} x`, `E_innov` (martingale difference), `E_mul_innov`,
  `E_sub_E_eq_sum_innov`, `eq_E_add_innov`.
* Series: `E_hasSum` (`E_t` through a dominated `tsum`).
* Forward equation `z_t = a E_t z_{t+1} + u_t` (`Solves`): `forwardSol` (with `forwardSol_hasSum`:
  it is `∑ aᵏ E_t u_{t+k}`), `forwardSol_solves`, `forward_unique`, `existsUnique_forward`;
  for `|a| ≥ 1`: `sunspot`, `sunspot_solves`, `not_unique_of_one_le`, `sunspot_not_predictable`;
  criteria `unique_iff`, `existsUnique_iff`.
* AR(1) with martingale-difference shocks: `ar1_E`, `ar1_E_sq_dev`, `ar1_condVar`,
  `ar1_condVar_closed`.
* Bridges: `toExpectationSystem` (finite discrete full-support `Ω` → core system, with
  `toExpectationSystem_E`, `toExpectationSystem_pullOut`) and `TreeBridge.treeSystem` (core
  `FiniteTree` → measure system, `TreeBridge.treeSystem_E`: `E_t` equals the cell average at every
  state, `TreeBridge.treeSystem_toExpectationSystem_E`: round trip).

The genuine infinite-horizon instance (i.i.d. shocks on `ℕ → ℝ`) is `ExpectationsMeasureIID`.
To copy into another project: rename the namespace prefix and the `import` of
`ExpectationsFiniteTree`; the module uses the core only through `ExpectationSystem`,
`ExpectationSystem.PullOut`, `ExpectationsFiniteTree.FiniteTree` and its `condE`,
`condE_of_trivial`, `condE_tower`, `condE_congr`, `condE_of_const_on_cell`,
`toExpectationSystem_E`, `finiteTree_pullOut`.
-/

namespace Cochrane.DebtDeficitsInflation.ExpectationsMeasure

open MeasureTheory ProbabilityTheory Filter Topology

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Cochrane (2023), Ch. 2, pp. 29–30 (the conditional expectations `E_t`): a probability space
`(Ω, P)` with a filtration `𝓕 : ℕ → MeasurableSpace Ω`; `E_t x := P[x | 𝓕 t]`. -/
structure MeasExpectationSystem where
  /-- The probability measure. -/
  P : ProbabilityMeasure Ω
  /-- The information available at each date. -/
  𝓕 : Filtration ℕ mΩ

namespace MeasExpectationSystem

variable {Ω} (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), Ch. 2, p. 29: the probability measure as a measure. -/
abbrev μ : Measure Ω := S.P

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x = μ[x | 𝓕 t]`, Mathlib's conditional expectation. -/
noncomputable abbrev E (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.μ[x | S.𝓕 t]

/-- Cochrane (2023), Ch. 2, p. 29: a bounded random variable (a.e. strongly measurable and
essentially bounded). -/
def BddRV (x : Ω → ℝ) : Prop := AEStronglyMeasurable x S.μ ∧ ∃ M, ∀ᵐ ω ∂S.μ, |x ω| ≤ M

/-- Cochrane (2023), Ch. 2, p. 29: a uniformly (essentially) bounded process. -/
def BddProc (x : ℕ → Ω → ℝ) : Prop := ∃ M, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ M

/-- Cochrane (2023), Ch. 2, p. 29: a bounded random variable is integrable. -/
theorem BddRV.integrable {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) : Integrable x S.μ := by
  obtain ⟨hm, M, hM⟩ := hx
  exact Integrable.of_bound hm M (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is additive (a.e.). -/
theorem E_add {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x + y) =ᵐ[S.μ] S.E t x + S.E t y := condExp_add hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` commutes with differences (a.e.). -/
theorem E_sub {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x - y) =ᵐ[S.μ] S.E t x - S.E t y := condExp_sub hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is homogeneous (a.e.). -/
theorem E_smul (c : ℝ) (x : Ω → ℝ) (t : ℕ) : S.E t (c • x) =ᵐ[S.μ] c • S.E t x :=
  condExp_smul c x _

/-- Cochrane (2023), Ch. 2, pp. 29–30: constants are known (exactly). -/
theorem E_const (t : ℕ) (c : ℝ) : S.E t (fun _ => c) = fun _ => c :=
  condExp_const (S.𝓕.le t) c

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t 0 = 0`. -/
theorem E_zero (t : ℕ) : S.E t 0 = 0 := condExp_zero

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is monotone (a.e.). -/
theorem E_mono {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ)
    (hxy : x ≤ᵐ[S.μ] y) (t : ℕ) : S.E t x ≤ᵐ[S.μ] S.E t y := condExp_mono hx hy hxy

/-- Cochrane (2023), Ch. 2, pp. 29–30: the law of iterated expectations `E_s E_t = E_s`, `s ≤ t`
(a.e.). -/
theorem E_tower {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.E t x) =ᵐ[S.μ] S.E s x :=
  condExp_condExp_of_le (S.𝓕.mono hst) (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is `𝓕 t`-strongly measurable. -/
theorem stronglyMeasurable_E (t : ℕ) (x : Ω → ℝ) : StronglyMeasurable[S.𝓕 t] (S.E t x) :=
  stronglyMeasurable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is integrable. -/
theorem integrable_E (t : ℕ) (x : Ω → ℝ) : Integrable (S.E t x) S.μ := integrable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: what is known at `t` is its own forecast (exactly). -/
theorem E_of_stronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.E t x = x :=
  condExp_of_stronglyMeasurable (S.𝓕.le t) hx hi

/-- Cochrane (2023), Ch. 2, pp. 29–30: what is a.e. known at `t` is a.e. its own forecast. -/
theorem E_of_aestronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : AEStronglyMeasurable[S.𝓕 t] x S.μ)
    (hi : Integrable x S.μ) : S.E t x =ᵐ[S.μ] x :=
  condExp_of_aestronglyMeasurable' (S.𝓕.le t) hx hi

/-- Cochrane (2023), Ch. 2, pp. 29–30: earlier forecasts are known later, `E_t E_s = E_s` for
`s ≤ t` (exactly). -/
theorem E_known {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E t (S.E s x) = S.E s x :=
  S.E_of_stronglyMeasurable ((S.stronglyMeasurable_E s x).mono (S.𝓕.mono hst))
    (S.integrable_E s x)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is idempotent (exactly). -/
theorem E_E_self (t : ℕ) (x : Ω → ℝ) : S.E t (S.E t x) = S.E t x := S.E_known le_rfl x

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` respects a.e. equality. -/
theorem E_congr {x y : Ω → ℝ} (h : x =ᵐ[S.μ] y) (t : ℕ) : S.E t x =ᵐ[S.μ] S.E t y :=
  condExp_congr_ae h

/-- Cochrane (2023), Ch. 2, pp. 29–30: the unconditional mean of a forecast is the mean. -/
theorem integral_E (t : ℕ) (x : Ω → ℝ) : ∫ ω, S.E t x ω ∂S.μ = ∫ ω, x ω ∂S.μ :=
  integral_condExp (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: **pull-out** — a bounded factor known at `t` comes out of
`E_t` (a.e.). -/
theorem E_pullOut {t : ℕ} {f y : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f) {C : ℝ}
    (hfC : ∀ᵐ ω ∂S.μ, |f ω| ≤ C) (hy : Integrable y S.μ) :
    S.E t (f * y) =ᵐ[S.μ] f * S.E t y := by
  have hint : Integrable (f * y) S.μ :=
    hy.bdd_mul (hf.mono (S.𝓕.le t)).aestronglyMeasurable
      (hfC.mono fun ω h => by rwa [Real.norm_eq_abs])
  exact condExp_mul_of_stronglyMeasurable_left hf hint hy

/-- Cochrane (2023), Ch. 2, pp. 29–30: `|E_t x| ≤ M` a.e. whenever `|x| ≤ M` a.e. -/
theorem abs_E_le {x : Ω → ℝ} {M : ℝ} (hx : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |S.E t x ω| ≤ M :=
  ae_bdd_abs_condExp_of_ae_bdd_abs hx

/-! ### Bounded random variables -/

/-- Cochrane (2023), Ch. 2, p. 29: a variable known at `t` with an a.e. bound is bounded. -/
theorem BddRV.of_stronglyMeasurable {S : MeasExpectationSystem Ω}
    {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    {M : ℝ} (hM : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) : S.BddRV x :=
  ⟨(hx.mono (S.𝓕.le t)).aestronglyMeasurable, M, hM⟩

/-- Cochrane (2023), Ch. 2, p. 29: constants are bounded. -/
theorem BddRV.const {S : MeasExpectationSystem Ω} (c : ℝ) : S.BddRV (fun _ => c) :=
  ⟨aestronglyMeasurable_const, |c|, Eventually.of_forall fun _ => le_rfl⟩

/-- Cochrane (2023), Ch. 2, p. 29: sums of bounded variables are bounded. -/
theorem BddRV.add {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x + y) := by
  obtain ⟨hxm, M, hM⟩ := hx
  obtain ⟨hym, N, hN⟩ := hy
  refine ⟨hxm.add hym, M + N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Cochrane (2023), Ch. 2, p. 29: multiples of bounded variables are bounded. -/
theorem BddRV.smul {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) (c : ℝ) : S.BddRV (c • x) := by
  obtain ⟨hxm, M, hM⟩ := hx
  refine ⟨hxm.const_smul c, |c| * M, ?_⟩
  filter_upwards [hM] with ω h1
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

/-- Cochrane (2023), Ch. 2, p. 29: differences of bounded variables are bounded. -/
theorem BddRV.sub {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x - y) := by
  have h := hx.add (hy.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

/-- Cochrane (2023), Ch. 2, p. 29: products of bounded variables are bounded. -/
theorem BddRV.mul {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x * y) := by
  obtain ⟨hxm, M, hM⟩ := hx
  obtain ⟨hym, N, hN⟩ := hy
  refine ⟨hxm.mul hym, M * N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Cochrane (2023), Ch. 2, p. 29: forecasts of bounded variables are bounded. -/
theorem BddRV.E {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) (t : ℕ) : S.BddRV (S.E t x) := by
  obtain ⟨-, M, hM⟩ := hx
  exact ⟨(S.integrable_E t x).aestronglyMeasurable, M, S.abs_E_le hM t⟩

/-! ### Innovations (news) -/

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
noncomputable def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.E (t + 1) x - S.E t x

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation is known at `t + 1`. -/
theorem stronglyMeasurable_innov (t : ℕ) (x : Ω → ℝ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (S.innov t x) :=
  (S.stronglyMeasurable_E (t + 1) x).sub
    ((S.stronglyMeasurable_E t x).mono (S.𝓕.mono (Nat.le_succ t)))

/-- Cochrane (2023), eq. (2.13), p. 30: **innovations are martingale differences**,
`E_s ΔE_{t+1} x = 0` a.e. for every `s ≤ t`. -/
theorem E_innov {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.innov t x) =ᵐ[S.μ] 0 := by
  filter_upwards [S.E_sub (S.integrable_E (t + 1) x) (S.integrable_E t x) s,
    S.E_tower (hst.trans (Nat.le_succ t)) x, S.E_tower hst x] with ω h1 h2 h3
  rw [innov, h1, Pi.sub_apply, h2, h3, sub_self, Pi.zero_apply]

/-- Cochrane (2023), eq. (2.13), p. 30: news is uncorrelated with anything known before it,
`E_t (w ΔE_{t+1} x) = 0` for bounded `w` known at `t` and bounded `x`. -/
theorem E_mul_innov {t : ℕ} {w : Ω → ℝ} (hw : StronglyMeasurable[S.𝓕 t] w) {C : ℝ}
    (hwC : ∀ᵐ ω ∂S.μ, |w ω| ≤ C) (x : Ω → ℝ) :
    S.E t (w * S.innov t x) =ᵐ[S.μ] 0 := by
  have hi : Integrable (S.innov t x) S.μ := (S.integrable_E _ x).sub (S.integrable_E _ x)
  filter_upwards [S.E_pullOut hw hwC hi, S.E_innov le_rfl x] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp

/-- Cochrane (2023), eq. (2.13), p. 30: forecast revisions telescope into news,
`E_{t+n} x − E_t x = ∑_{i<n} ΔE_{t+i+1} x` (exactly). -/
theorem E_sub_E_eq_sum_innov (t n : ℕ) (x : Ω → ℝ) :
    S.E (t + n) x - S.E t x = ∑ i ∈ Finset.range n, S.innov (t + i) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, innov, ← add_assoc]
    abel

/-- Cochrane (2023), eq. (2.17), p. 35: a variable known at `t + 1` is its forecast plus its
news, `x = E_t x + ΔE_{t+1} x` (exactly). -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 (t + 1)] x)
    (hi : Integrable x S.μ) : x = S.E t x + S.innov t x := by
  rw [innov, S.E_of_stronglyMeasurable hx hi]
  abel

/-! ### `E_t` and dominated infinite sums -/

/-- Cochrane (2023), Ch. 2, p. 29 (present values as infinite sums): **`E_t` passes through a
dominated series** — if `|f_k| ≤ c_k` a.e. with `∑ c_k < ∞`, then a.e.
`∑_k E_t f_k = E_t ∑_k f_k` (as a genuine `HasSum`). -/
theorem E_hasSum {f : ℕ → Ω → ℝ} {c : ℕ → ℝ} (hc : Summable c)
    (hm : ∀ k, AEStronglyMeasurable (f k) S.μ) (hf : ∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ c k) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => S.E t (f k) ω) (S.E t (fun ω' => ∑' k, f k ω') ω) := by
  set F : Ω → ℝ := fun ω' => ∑' k, f k ω' with hF
  have hall : ∀ᵐ ω ∂S.μ, ∀ k, |f k ω| ≤ c k := ae_all_iff.2 hf
  have hsum : ∀ᵐ ω ∂S.μ, Summable (fun k => f k ω) := hall.mono fun ω h =>
    Summable.of_norm_bounded hc (fun k => by rw [Real.norm_eq_abs]; exact h k)
  have hFm : AEStronglyMeasurable F S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, f k ω)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hm k) ?_
    filter_upwards [hsum] with ω h
    exact h.hasSum.tendsto_sum_nat
  -- the tail bound
  have htail : ∀ N, ∀ᵐ ω ∂S.μ,
      |F ω - ∑ k ∈ Finset.range N, f k ω| ≤ ∑' k, c (k + N) := by
    intro N
    filter_upwards [hall, hsum] with ω h hs
    change |∑' k, f k ω - ∑ k ∈ Finset.range N, f k ω| ≤ _
    rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded ((summable_nat_add_iff N).2 hc).hasSum
      (fun k => by rw [Real.norm_eq_abs]; exact h (k + N))
  have hbF : ∀ᵐ ω ∂S.μ, |F ω| ≤ ∑' k, c k := by
    filter_upwards [htail 0] with ω h
    simpa using h
  have hint : ∀ k, Integrable (f k) S.μ := fun k => BddRV.integrable (S := S) ⟨hm k, c k, hf k⟩
  have hFi : Integrable F S.μ := BddRV.integrable (S := S) ⟨hFm, _, hbF⟩
  have hdiff : ∀ N, ∀ᵐ ω ∂S.μ,
      |S.E t F ω - ∑ k ∈ Finset.range N, S.E t (f k) ω| ≤ ∑' k, c (k + N) := by
    intro N
    have hpi : Integrable (∑ k ∈ Finset.range N, f k) S.μ :=
      integrable_finsetSum' _ fun k _ => hint k
    have hEs : S.E t (∑ k ∈ Finset.range N, f k) =ᵐ[S.μ] ∑ k ∈ Finset.range N, S.E t (f k) :=
      condExp_finsetSum (fun k _ => hint k) (S.𝓕 t)
    filter_upwards [S.E_sub hFi hpi t, hEs,
      S.abs_E_le (x := F - ∑ k ∈ Finset.range N, f k) (by
        filter_upwards [htail N] with ω h
        simpa [Finset.sum_apply] using h) t] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Finset.sum_apply] at h3
    exact h3
  have hEb : ∀ᵐ ω ∂S.μ, ∀ k, |S.E t (f k) ω| ≤ c k :=
    ae_all_iff.2 fun k => S.abs_E_le (hf k) t
  filter_upwards [ae_all_iff.2 hdiff, hEb] with ω hd hb
  have hs : Summable fun k => ‖S.E t (f k) ω‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hb k) hc
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun N => ?_) (tendsto_sum_nat_add c)
  rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
  exact hd N

/-! ### Forward solutions: existence and uniqueness for `|a| < 1` -/

/-- Cochrane (2023), Ch. 2, p. 29 (present values): the realised discounted sum
`∑_k aᵏ u_{t+k}`. -/
noncomputable def discSum (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * u (t + k) ω

/-- Cochrane (2023), Ch. 2, p. 29: a geometric series with bounded terms is summable. -/
theorem summable_geom_mul {a M : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : ∀ k, |x k| ≤ M) :
    Summable (fun k => a ^ k * x k) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (abs_nonneg a) k))

/-- Cochrane (2023), Ch. 2, p. 29: the bound `|∑ aᵏ x_k| ≤ M / (1 − |a|)`. -/
theorem abs_tsum_geom_mul_le {a M : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : ∀ k, |x k| ≤ M) :
    |∑' k, a ^ k * x k| ≤ M / (1 - |a|) := by
  rw [← Real.norm_eq_abs, div_eq_inv_mul]
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (abs_nonneg a) k)

omit mΩ in
/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum satisfies `U_t = u_t + a U_{t+1}` wherever
it converges. -/
theorem discSum_succ {a : ℝ} {u : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hs : Summable (fun k => a ^ k * u (t + k) ω)) :
    discSum a u t ω = u t ω + a * discSum a u (t + 1) ω := by
  unfold discSum
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum of a bounded process is bounded a.e. -/
theorem discSum_bdd {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |discSum a u t ω| ≤ M / (1 - |a|) := by
  filter_upwards [ae_all_iff.2 hb] with ω h
  exact abs_tsum_geom_mul_le ha fun k => h (t + k)

/-- Cochrane (2023), Ch. 2, p. 29: `U_t = u_t + a U_{t+1}` a.e. -/
theorem discSum_rec {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    discSum a u t =ᵐ[S.μ] u t + a • discSum a u (t + 1) := by
  filter_upwards [ae_all_iff.2 hb] with ω h
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact discSum_succ (summable_geom_mul ha fun k => h (t + k))

/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum is a.e. strongly measurable. -/
theorem aestronglyMeasurable_discSum {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    AEStronglyMeasurable (discSum a u t) S.μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ k ∈ Finset.range N, a ^ k * u (t + k) ω)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hm (t + k)).const_mul _) ?_
  filter_upwards [ae_all_iff.2 hb] with ω h
  exact (summable_geom_mul ha fun k => h (t + k)).hasSum.tendsto_sum_nat

/-- Cochrane (2023), Ch. 2, p. 29: `z` solves `z_t = a E_t z_{t+1} + u_t` (a.e. at every
date). -/
def Solves (a : ℝ) (u z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, z t =ᵐ[S.μ] a • S.E t (z (t + 1)) + u t

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution `z_t = E_t ∑_k aᵏ u_{t+k}`. -/
noncomputable def forwardSol (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.E t (discSum a u t)

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is adapted. -/
theorem forwardSol_adapted (a : ℝ) (u : ℕ → Ω → ℝ) : StronglyAdapted S.𝓕 (S.forwardSol a u) :=
  fun t => S.stronglyMeasurable_E t _

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is bounded by `M / (1 − |a|)`. -/
theorem forwardSol_bdd {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) : S.BddProc (S.forwardSol a u) :=
  ⟨M / (1 - |a|), fun t => S.abs_E_le (S.discSum_bdd ha hb t) t⟩

/-- Cochrane (2023), Ch. 2, p. 29: **existence** — for `|a| < 1` and bounded adapted `u`, the
forward solution solves `z_t = a E_t z_{t+1} + u_t`. -/
theorem forwardSol_solves {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) :
    S.Solves a u (S.forwardSol a u) := by
  intro t
  have hm : ∀ t, AEStronglyMeasurable (u t) S.μ :=
    fun t => ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hDi : ∀ s, Integrable (discSum a u s) S.μ := fun s =>
    BddRV.integrable ⟨S.aestronglyMeasurable_discSum ha hm hb s, _, S.discSum_bdd ha hb s⟩
  have hui : Integrable (u t) S.μ := BddRV.integrable ⟨hm t, M, hb t⟩
  have hEu : S.E t (u t) = u t := S.E_of_stronglyMeasurable (hua t) hui
  filter_upwards [S.E_congr (S.discSum_rec ha hb t) t, S.E_add hui ((hDi (t + 1)).smul a) t,
    S.E_smul a (discSum a u (t + 1)) t, S.E_tower (Nat.le_succ t) (discSum a u (t + 1))]
    with ω h1 h2 h3 h4
  change S.E t (discSum a u t) ω = (a • S.E t (S.E (t + 1) (discSum a u (t + 1))) + u t) ω
  rw [h1, h2, Pi.add_apply, hEu, h3, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h4,
    add_comm]

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is the genuine forward sum
`z_t = ∑_k aᵏ E_t u_{t+k}` (a.e., as a convergent series). -/
theorem forwardSol_hasSum {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => a ^ k * S.E t (u (t + k)) ω) (S.forwardSol a u t ω) := by
  have hsm : ∀ k, S.E t (fun ω => a ^ k * u (t + k) ω) =ᵐ[S.μ] a ^ k • S.E t (u (t + k)) :=
    fun k => S.E_smul (a ^ k) (u (t + k)) t
  filter_upwards [S.E_hasSum (f := fun k ω => a ^ k * u (t + k) ω)
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => (hm (t + k)).const_mul _) (fun k => by
      filter_upwards [hb (t + k)] with ω h
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg a) k)) t,
    ae_all_iff.2 hsm] with ω h1 h2
  have e : (fun k => a ^ k * S.E t (u (t + k)) ω) =
      fun k => S.E t (fun ω => a ^ k * u (t + k) ω) ω := by
    funext k
    rw [h2 k, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact h1

/-- Cochrane (2023), Ch. 2, p. 29: iterating a homogeneous forward equation,
`d_t = a^{k+1} E_t d_{t+k+1}` a.e. -/
theorem iterate_homog {a : ℝ} {d : ℕ → Ω → ℝ} (hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1)))
    (t k : ℕ) : d t =ᵐ[S.μ] a ^ (k + 1) • S.E t (d (t + (k + 1))) := by
  induction k with
  | zero => simpa using hd t
  | succ k ih =>
    have h2 := hd (t + (k + 1))
    have e : t + (k + 1) + 1 = t + (k + 1 + 1) := rfl
    rw [e] at h2
    filter_upwards [ih, S.E_congr h2 t, S.E_smul a (S.E (t + (k + 1)) (d (t + (k + 1 + 1)))) t,
      S.E_tower (Nat.le_add_right t (k + 1)) (d (t + (k + 1 + 1)))] with ω e1 e2 e3 e4
    rw [e1, Pi.smul_apply, e2, e3, Pi.smul_apply, e4, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), Ch. 2, p. 29: **uniqueness** — for `|a| < 1` the equation
`z_t = a E_t z_{t+1} + u_t` has at most one bounded (a.e. measurable) solution, up to a.e.
equality at every date. -/
theorem forward_unique {a : ℝ} (ha : |a| < 1) {u z₁ z₂ : ℕ → Ω → ℝ} (h₁ : S.Solves a u z₁)
    (h₂ : S.Solves a u z₂) (hm₁ : ∀ t, AEStronglyMeasurable (z₁ t) S.μ)
    (hm₂ : ∀ t, AEStronglyMeasurable (z₂ t) S.μ) (hb₁ : S.BddProc z₁) (hb₂ : S.BddProc z₂) :
    ∀ t, z₁ t =ᵐ[S.μ] z₂ t := by
  obtain ⟨M₁, hM₁⟩ := hb₁
  obtain ⟨M₂, hM₂⟩ := hb₂
  have hi₁ : ∀ t, Integrable (z₁ t) S.μ := fun t => BddRV.integrable ⟨hm₁ t, M₁, hM₁ t⟩
  have hi₂ : ∀ t, Integrable (z₂ t) S.μ := fun t => BddRV.integrable ⟨hm₂ t, M₂, hM₂ t⟩
  set d : ℕ → Ω → ℝ := fun t => z₁ t - z₂ t with hd_def
  have hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1)) := by
    intro t
    filter_upwards [h₁ t, h₂ t, S.E_sub (hi₁ (t + 1)) (hi₂ (t + 1)) t] with ω e1 e2 e3
    simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hdb : ∀ s, ∀ᵐ ω ∂S.μ, |d s ω| ≤ M₁ + M₂ := fun s => by
    filter_upwards [hM₁ s, hM₂ s] with ω e1 e2
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  intro t
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂S.μ, |d t ω| ≤ |a| ^ (k + 1) * (M₁ + M₂) := by
    intro k
    filter_upwards [S.iterate_homog hd t k, S.abs_E_le (hdb (t + (k + 1))) t] with ω e1 e2
    rw [e1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left e2 (pow_nonneg (abs_nonneg a) _)
  filter_upwards [ae_all_iff.2 hk] with ω h
  have hlim : Tendsto (fun k : ℕ => |a| ^ (k + 1) * (M₁ + M₂)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).comp
      (tendsto_add_atTop_nat 1)).mul_const (M₁ + M₂)
    simpa using this
  have h0 : d t ω = 0 := abs_nonpos_iff.mp (ge_of_tendsto' hlim h)
  simpa [hd_def, sub_eq_zero] using h0

/-- Cochrane (2023), Ch. 2, p. 29: **existence and uniqueness** of the bounded adapted solution
of `z_t = a E_t z_{t+1} + u_t` for `|a| < 1` and bounded adapted `u`: it is the forward solution
`∑ aᵏ E_t u_{t+k}` (`forwardSol_hasSum`), and every bounded a.e.-measurable solution equals it
a.e. at every date. -/
theorem existsUnique_forward {a : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u) :
    (S.Solves a u (S.forwardSol a u) ∧ StronglyAdapted S.𝓕 (S.forwardSol a u) ∧
      S.BddProc (S.forwardSol a u)) ∧
    ∀ z, S.Solves a u z → (∀ t, AEStronglyMeasurable (z t) S.μ) → S.BddProc z →
      ∀ t, z t =ᵐ[S.μ] S.forwardSol a u t := by
  obtain ⟨M, hb⟩ := hub
  refine ⟨⟨S.forwardSol_solves ha hua hb, S.forwardSol_adapted a u, S.forwardSol_bdd ha hb⟩,
    fun z hz hzm hzb => S.forward_unique ha hz (S.forwardSol_solves ha hua hb) hzm
      (fun t => ((S.forwardSol_adapted a u t).mono (S.𝓕.le t)).aestronglyMeasurable) hzb
      (S.forwardSol_bdd ha hb)⟩

/-! ### Nonuniqueness for `|a| ≥ 1`: genuinely random sunspots -/

/-- Cochrane (2023), Ch. 2, p. 29 (multiple equilibria when the root is not stable): the sunspot
started by a date-`s+1` shock `η`: `d_t = 0` for `t ≤ s` and `d_t = a^{-(t-s-1)} (η − E_s η)`
for `t > s`. -/
noncomputable def sunspot (a : ℝ) (s : ℕ) (η : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t ≤ s then 0 else a⁻¹ ^ (t - (s + 1)) • (η - S.E s η)

/-- Cochrane (2023), Ch. 2, p. 29: at date `s + 1` the sunspot is the news `η − E_s η`. -/
theorem sunspot_succ (a : ℝ) (s : ℕ) (η : Ω → ℝ) : S.sunspot a s η (s + 1) = η - S.E s η := by
  simp [sunspot]

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot is adapted. -/
theorem sunspot_adapted (a : ℝ) {s : ℕ} {η : Ω → ℝ} (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) :
    StronglyAdapted S.𝓕 (S.sunspot a s η) := by
  intro t
  unfold sunspot
  by_cases h : t ≤ s
  · simp only [h, ↓reduceIte]
    exact stronglyMeasurable_zero
  · simp only [h, ↓reduceIte]
    have h1 : s + 1 ≤ t := by omega
    exact ((hη.mono (S.𝓕.mono h1)).sub
      ((S.stronglyMeasurable_E s η).mono (S.𝓕.mono (by omega)))).const_smul _

/-- Cochrane (2023), Ch. 2, p. 29: for `|a| ≥ 1` the sunspot of a bounded shock is bounded. -/
theorem sunspot_bdd {a B : ℝ} (ha : 1 ≤ |a|) {s : ℕ} {η : Ω → ℝ}
    (hηb : ∀ᵐ ω ∂S.μ, |η ω| ≤ B) : S.BddProc (S.sunspot a s η) := by
  obtain ⟨ω₀, hω₀⟩ := hηb.exists
  have hB : 0 ≤ B := (abs_nonneg _).trans hω₀
  refine ⟨B + B, fun t => ?_⟩
  unfold sunspot
  by_cases h : t ≤ s
  · simp only [h, ↓reduceIte]
    exact Eventually.of_forall fun ω => by simp; linarith
  · simp only [h, ↓reduceIte]
    filter_upwards [hηb, S.abs_E_le hηb s] with ω h1 h2
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, Pi.sub_apply]
    have hp : |a⁻¹| ^ (t - (s + 1)) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (by rw [abs_inv]; exact inv_le_one_of_one_le₀ ha)
    have hs : |η ω - S.E s η ω| ≤ B + B := (abs_sub _ _).trans (add_le_add h1 h2)
    calc |a⁻¹| ^ (t - (s + 1)) * |η ω - S.E s η ω| ≤ 1 * (B + B) :=
          mul_le_mul hp hs (abs_nonneg _) zero_le_one
      _ = B + B := one_mul _

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot solves the homogeneous equation
`d_t = a E_t d_{t+1}` (a.e.) for every `a ≠ 0`. -/
theorem sunspot_solves {a : ℝ} (ha : a ≠ 0) {s : ℕ} {η : Ω → ℝ}
    (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) (hηi : Integrable η S.μ) (t : ℕ) :
    S.sunspot a s η t =ᵐ[S.μ] a • S.E t (S.sunspot a s η (t + 1)) := by
  rcases lt_trichotomy t s with h | rfl | h
  · have h1 : t ≤ s := h.le
    have h2 : t + 1 ≤ s := h
    unfold sunspot
    simp only [h1, h2, ↓reduceIte, S.E_zero, smul_zero]
    rfl
  · rw [S.sunspot_succ]
    unfold sunspot
    simp only [le_refl, ↓reduceIte]
    filter_upwards [S.E_sub hηi (S.integrable_E t η) t] with ω h1
    rw [Pi.smul_apply, h1, Pi.sub_apply, S.E_E_self, sub_self, smul_zero, Pi.zero_apply]
  · have h1 : ¬ t ≤ s := by omega
    have h2 : ¬ t + 1 ≤ s := by omega
    have hν : StronglyMeasurable[S.𝓕 t] (a⁻¹ ^ (t + 1 - (s + 1)) • (η - S.E s η)) :=
      ((hη.mono (S.𝓕.mono h)).sub
        ((S.stronglyMeasurable_E s η).mono (S.𝓕.mono h.le))).const_smul _
    have hνi : Integrable (a⁻¹ ^ (t + 1 - (s + 1)) • (η - S.E s η)) S.μ :=
      (hηi.sub (S.integrable_E s η)).smul _
    unfold sunspot
    simp only [h1, h2, ↓reduceIte]
    rw [S.E_of_stronglyMeasurable hν hνi, smul_smul]
    have e : t + 1 - (s + 1) = t - (s + 1) + 1 := by omega
    rw [e, pow_succ, ← mul_assoc, mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]

/-- Cochrane (2023), Ch. 2, p. 29: adding a solution of the homogeneous equation to a solution
gives a solution. -/
theorem solves_add {a : ℝ} {u z d : ℕ → Ω → ℝ} (hz : S.Solves a u z)
    (hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1))) (hzi : ∀ t, Integrable (z t) S.μ)
    (hdi : ∀ t, Integrable (d t) S.μ) : S.Solves a u (fun t => z t + d t) := by
  intro t
  filter_upwards [hz t, hd t, S.E_add (hzi (t + 1)) (hdi (t + 1)) t] with ω e1 e2 e3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  ring

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot shock is genuinely random — `η − E_s η` is not
a.e. equal to any variable known at date `s` — unless `η` is a.e. its own date-`s` forecast. -/
theorem sunspot_not_predictable {s : ℕ} {η : Ω → ℝ} (hηi : Integrable η S.μ)
    (hηr : ¬ η =ᵐ[S.μ] S.E s η) {g : Ω → ℝ} (hg : StronglyMeasurable[S.𝓕 s] g) :
    ¬ (η - S.E s η) =ᵐ[S.μ] g := by
  intro h
  have hνi : Integrable (η - S.E s η) S.μ := hηi.sub (S.integrable_E s η)
  have hgi : Integrable g S.μ := hνi.congr h
  have h0 : S.E s (η - S.E s η) =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_sub hηi (S.integrable_E s η) s] with ω h1
    rw [h1, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]
  have hg0 : g =ᵐ[S.μ] 0 := by
    have := (S.E_congr h s).symm.trans h0
    rwa [S.E_of_stronglyMeasurable hg hgi] at this
  apply hηr
  filter_upwards [h.trans hg0] with ω h1
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
  exact h1

/-- Cochrane (2023), Ch. 2, p. 29: **nonuniqueness for `|a| ≥ 1`** — next to every bounded
adapted solution of `z_t = a E_t z_{t+1} + u_t` there is another one, `z + d` with the sunspot
`d` driven by any bounded date-`s+1` shock `η` that is not a.e. its own date-`s` forecast; the
two differ with positive probability at date `s + 1`. -/
theorem not_unique_of_one_le {a B : ℝ} (ha : 1 ≤ |a|) {s : ℕ} {η : Ω → ℝ}
    (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) (hηb : ∀ᵐ ω ∂S.μ, |η ω| ≤ B)
    (hηr : ¬ η =ᵐ[S.μ] S.E s η) {u z : ℕ → Ω → ℝ} (hz : S.Solves a u z)
    (hza : StronglyAdapted S.𝓕 z) (hzb : S.BddProc z) :
    ∃ z', S.Solves a u z' ∧ StronglyAdapted S.𝓕 z' ∧ S.BddProc z' ∧
      ¬ z' (s + 1) =ᵐ[S.μ] z (s + 1) := by
  have ha0 : a ≠ 0 := fun h => by rw [h, abs_zero] at ha; linarith
  have hηi : Integrable η S.μ := BddRV.integrable (BddRV.of_stronglyMeasurable hη hηb)
  obtain ⟨M, hM⟩ := hzb
  obtain ⟨M', hM'⟩ := S.sunspot_bdd (s := s) ha hηb
  have hzi : ∀ t, Integrable (z t) S.μ := fun t =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (hza t) (hM t))
  have hdi : ∀ t, Integrable (S.sunspot a s η t) S.μ := fun t =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (S.sunspot_adapted a hη t) (hM' t))
  refine ⟨fun t => z t + S.sunspot a s η t,
    S.solves_add hz (S.sunspot_solves ha0 hη hηi) hzi hdi,
    fun t => (hza t).add (S.sunspot_adapted a hη t), ⟨M + M', fun t => ?_⟩, ?_⟩
  · filter_upwards [hM t, hM' t] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · intro h
    apply hηr
    filter_upwards [h] with ω h1
    rw [S.sunspot_succ, Pi.add_apply, Pi.sub_apply, add_eq_left, sub_eq_zero] at h1
    exact h1

/-- Cochrane (2023), Ch. 2, p. 29: the zero process solves `z_t = a E_t z_{t+1}`. -/
theorem solves_zero (a : ℝ) : S.Solves a 0 0 := fun t => by
  rw [Pi.zero_apply, Pi.zero_apply, S.E_zero, smul_zero, add_zero]

/-- Cochrane (2023), Ch. 2, p. 29: **determinacy criterion** — on a filtration carrying some
genuinely random bounded news (a bounded date-`s+1` variable that is not a.e. its own date-`s`
forecast), bounded adapted solutions of `z_t = a E_t z_{t+1} + u_t` are unique (for every
bounded adapted `u`) if and only if `|a| < 1`. -/
theorem unique_iff (hnd : ∃ s η B, StronglyMeasurable[S.𝓕 (s + 1)] η ∧
      (∀ᵐ ω ∂S.μ, |η ω| ≤ B) ∧ ¬ η =ᵐ[S.μ] S.E s η) (a : ℝ) :
    (∀ u z₁ z₂ : ℕ → Ω → ℝ, S.Solves a u z₁ → S.Solves a u z₂ → StronglyAdapted S.𝓕 z₁ →
      StronglyAdapted S.𝓕 z₂ → S.BddProc z₁ → S.BddProc z₂ → ∀ t, z₁ t =ᵐ[S.μ] z₂ t) ↔
      |a| < 1 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    obtain ⟨s, η, B, hη, hηb, hηr⟩ := hnd
    obtain ⟨z', hz', hza', hzb', hne⟩ := S.not_unique_of_one_le ha hη hηb hηr (S.solves_zero a)
      (fun _ => stronglyMeasurable_zero) ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
    exact hne (h 0 z' 0 hz' (S.solves_zero a) hza' (fun _ => stronglyMeasurable_zero) hzb'
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ (s + 1))
  · intro ha u z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂
    exact S.forward_unique ha h₁ h₂ (fun t => ((ha₁ t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => ((ha₂ t).mono (S.𝓕.le t)).aestronglyMeasurable) hb₁ hb₂

/-- Cochrane (2023), Ch. 2, p. 29: **existence and uniqueness iff `|a| < 1`** — under genuinely
random news, every bounded adapted `u` has a bounded adapted solution, unique up to a.e.
equality, exactly when `|a| < 1`. -/
theorem existsUnique_iff (hnd : ∃ s η B, StronglyMeasurable[S.𝓕 (s + 1)] η ∧
      (∀ᵐ ω ∂S.μ, |η ω| ≤ B) ∧ ¬ η =ᵐ[S.μ] S.E s η) (a : ℝ) :
    (∀ u : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 u → S.BddProc u →
      (∃ z, S.Solves a u z ∧ StronglyAdapted S.𝓕 z ∧ S.BddProc z) ∧
      ∀ z₁ z₂ : ℕ → Ω → ℝ, S.Solves a u z₁ → S.Solves a u z₂ → StronglyAdapted S.𝓕 z₁ →
        StronglyAdapted S.𝓕 z₂ → S.BddProc z₁ → S.BddProc z₂ → ∀ t, z₁ t =ᵐ[S.μ] z₂ t) ↔
      |a| < 1 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    obtain ⟨s, η, B, hη, hηb, hηr⟩ := hnd
    have h0 := (h 0 (fun _ => stronglyMeasurable_zero)
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩).2
    obtain ⟨z', hz', hza', hzb', hne⟩ := S.not_unique_of_one_le ha hη hηb hηr (S.solves_zero a)
      (fun _ => stronglyMeasurable_zero) ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
    exact hne (h0 z' 0 hz' (S.solves_zero a) hza' (fun _ => stronglyMeasurable_zero) hzb'
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ (s + 1))
  · intro ha u hua hub
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := S.existsUnique_forward ha hua hub
    exact ⟨⟨_, h1, h2, h3⟩, fun z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂ =>
      (S.unique_iff hnd a).2 ha u z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂⟩

/-! ### AR(1) processes driven by martingale-difference shocks -/

/-- Cochrane (2023), Ch. 2, p. 29: the square of a bounded variable is bounded. -/
theorem BddRV.sq {S : MeasExpectationSystem Ω} {x : Ω → ℝ} (hx : S.BddRV x) : S.BddRV (x ^ 2) := by
  rw [pow_two]
  exact hx.mul hx

/-- Cochrane (2023), p. 42 (AR(1) surpluses `s_t = η s_{t−1} + ε_t`): for
`u_{t+1} = ρ u_t + ε_{t+1}` with bounded adapted `u` and martingale-difference shocks
(`E_t ε_{t+1} = 0`), `E_t u_{t+j} = ρʲ u_t` a.e. -/
theorem ar1_E {ρ : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t j : ℕ) :
    S.E t (u (t + j)) =ᵐ[S.μ] ρ ^ j • u t := by
  obtain ⟨M, hM⟩ := hub
  have hui : ∀ s, Integrable (u s) S.μ := fun s =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (hua s) (hM s))
  have hεe : ∀ s, ε (s + 1) = u (s + 1) - ρ • u s := fun s => by
    rw [hrec s, add_sub_cancel_left]
  have hεi : ∀ s, Integrable (ε (s + 1)) S.μ := fun s => by
    rw [hεe]
    exact (hui _).sub ((hui s).smul ρ)
  induction j with
  | zero =>
    rw [add_zero, pow_zero, one_smul, S.E_of_stronglyMeasurable (hua t) (hui t)]
  | succ j ih =>
    have e : u (t + (j + 1)) = ρ • u (t + j) + ε (t + j + 1) := hrec (t + j)
    have hz : S.E t (ε (t + j + 1)) =ᵐ[S.μ] 0 := by
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (ε (t + j + 1))).symm,
        S.E_congr (hmd (t + j)) t] with ω h1 h2
      rw [h1, h2, S.E_zero]
    rw [e]
    filter_upwards [S.E_add ((hui _).smul ρ) (hεi (t + j)) t, S.E_smul ρ (u (t + j)) t, ih, hz]
      with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
    ring

/-- Cochrane (2023), p. 42: with conditionally homoskedastic shocks (`E_t ε_{t+1}² = σ²`), the
squared forecast error of an AR(1) has conditional mean `σ² ∑_{i<j} ρ^{2i}`. -/
theorem ar1_E_sq_dev {ρ σ2 : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    S.E t ((u (t + j) - ρ ^ j • u t) ^ 2) =ᵐ[S.μ]
      fun _ => σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) := by
  obtain ⟨M, hM⟩ := hub
  have hB : ∀ s, S.BddRV (u s) := fun s => BddRV.of_stronglyMeasurable (hua s) (hM s)
  have hεe : ∀ s, ε (s + 1) = u (s + 1) - ρ • u s := fun s => by
    rw [hrec s, add_sub_cancel_left]
  have hεB : ∀ s, S.BddRV (ε (s + 1)) := fun s => by
    rw [hεe]
    exact (hB _).sub ((hB s).smul ρ)
  induction j with
  | zero =>
    have h0 : (u (t + 0) - ρ ^ 0 • u t) ^ 2 = 0 := by
      funext ω
      simp
    rw [h0, S.E_zero]
    exact Eventually.of_forall fun ω => by simp
  | succ j ih =>
    set w := u (t + j) - ρ ^ j • u t with hw
    set e' := ε (t + j + 1) with he'
    have hwB : S.BddRV w := (hB _).sub ((hB t).smul _)
    have hwm : StronglyMeasurable[S.𝓕 (t + j)] w :=
      (hua (t + j)).sub (((hua t).mono (S.𝓕.mono (Nat.le_add_right t j))).const_smul _)
    have hsplit : (u (t + (j + 1)) - ρ ^ (j + 1) • u t) ^ 2 =
        ρ ^ 2 • w ^ 2 + (2 * ρ) • (w * e') + e' ^ 2 := by
      have e : u (t + (j + 1)) = ρ • u (t + j) + ε (t + j + 1) := hrec (t + j)
      rw [e]
      funext ω
      simp only [hw, he', Pi.add_apply, Pi.smul_apply, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply,
        smul_eq_mul]
      ring
    have hcross : S.E t (w * e') =ᵐ[S.μ] 0 := by
      obtain ⟨-, C, hC⟩ := hwB
      have hz : w * S.E (t + j) e' =ᵐ[S.μ] 0 := by
        filter_upwards [hmd (t + j)] with ω h
        rw [Pi.mul_apply, he', h, Pi.zero_apply, mul_zero]
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (w * e')).symm,
        S.E_congr (S.E_pullOut hwm hC (hεB (t + j)).integrable) t, S.E_congr hz t]
        with ω h1 h2 h3
      rw [h1, h2, h3, S.E_zero]
    have hsq : S.E t (e' ^ 2) =ᵐ[S.μ] fun _ => σ2 := by
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (e' ^ 2)).symm,
        S.E_congr (hvar (t + j)) t] with ω h1 h2
      rw [h1, h2, S.E_const]
    have I1 : Integrable (ρ ^ 2 • w ^ 2) S.μ := hwB.sq.integrable.smul _
    have I2 : Integrable ((2 * ρ) • (w * e')) S.μ := (hwB.mul (hεB (t + j))).integrable.smul _
    have I3 : Integrable (e' ^ 2) S.μ := (hεB (t + j)).sq.integrable
    have hs : ∑ i ∈ Finset.range (j + 1), ρ ^ (2 * i) =
        ρ ^ 2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    filter_upwards [S.E_add (I1.add I2) I3 t, S.E_add I1 I2 t, S.E_smul (ρ ^ 2) (w ^ 2) t,
      S.E_smul (2 * ρ) (w * e') t, ih, hcross, hsq] with ω h1 h2 h3 h4 h5 h6 h7
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, h7, hs,
      Pi.zero_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- Cochrane (2023), p. 42: **conditional variance of an AR(1)** —
`Var_t(u_{t+j}) = σ² ∑_{i<j} ρ^{2i}` a.e. (Mathlib's `condVar`). -/
theorem ar1_condVar {ρ σ2 : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    Var[u (t + j); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ => σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) := by
  change S.E t ((u (t + j) - S.E t (u (t + j))) ^ 2) =ᵐ[S.μ] _
  refine (S.E_congr ?_ t).trans (S.ar1_E_sq_dev hrec hua hub hmd hvar t j)
  filter_upwards [S.ar1_E hrec hua hub hmd t j] with ω h
  rw [Pi.pow_apply, Pi.pow_apply, Pi.sub_apply, Pi.sub_apply, h]

/-- Cochrane (2023), p. 42: the closed form `Var_t(u_{t+j}) = σ² (1 − ρ^{2j}) / (1 − ρ²)` for
`ρ² ≠ 1`. -/
theorem ar1_condVar_closed {ρ σ2 : ℝ} (hρ : ρ ^ 2 ≠ 1) {u ε : ℕ → Ω → ℝ}
    (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    Var[u (t + j); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ => σ2 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2) := by
  refine (S.ar1_condVar hrec hua hub hmd hvar t j).trans (Eventually.of_forall fun _ => ?_)
  have h1 : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hs : ∑ i ∈ Finset.range j, ρ ^ (2 * i) = (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2) := by
    simp_rw [pow_mul]
    rw [geom_sum_eq hρ, eq_div_iff h1, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hρ)]
    ring
  change σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) = σ2 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2)
  rw [hs, mul_div_assoc]

/-! ### Bridge to the core `ExpectationSystem` on a finite, fully supported state space -/

/-- Cochrane (2023), Ch. 2, p. 29: when every state has positive probability, a.e. equality is
equality. -/
theorem eq_of_ae_eq (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f =ᵐ[S.μ] g) : f = g := by
  funext ω
  by_contra hne
  have h0 : S.μ {ω' | f ω' ≠ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Cochrane (2023), Ch. 2, p. 29: when every state has positive probability, a.e. inequality is
inequality. -/
theorem le_of_ae_le (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f ≤ᵐ[S.μ] g) : f ≤ g := by
  intro ω
  by_contra hne
  have h0 : S.μ {ω' | ¬ f ω' ≤ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Cochrane (2023), Ch. 2, p. 29: `E_t` as a linear map on all of `Ω → ℝ`, for a finite discrete
state space with full support. -/
noncomputable def ELin [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun := S.E t
  map_add' _ _ := S.eq_of_ae_eq hfull (S.E_add Integrable.of_finite Integrable.of_finite t)
  map_smul' c x := S.eq_of_ae_eq hfull (S.E_smul c x t)

/-- Cochrane (2023), Ch. 2, p. 29: **bridge (b)** — on a finite discrete state space with full
support, a measure-theoretic expectation system is a core `ExpectationSystem`, with the same
`E_t` at every state, so every core theorem applies to it. -/
noncomputable def toExpectationSystem [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) : ExpectationSystem Ω where
  E := S.ELin hfull
  const := S.E_const
  mono t _ _ h := S.le_of_ae_le hfull
    (S.E_mono Integrable.of_finite Integrable.of_finite (Eventually.of_forall h) t)
  tower hst x := S.eq_of_ae_eq hfull (S.E_tower hst x)
  known hst x := S.E_known hst x

/-- Cochrane (2023), Ch. 2, p. 29: the core system's `E_t` is Mathlib's conditional
expectation, exactly. -/
theorem toExpectationSystem_E [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ) (x : Ω → ℝ) :
    (S.toExpectationSystem hfull).E t x = S.E t x := rfl

/-- Cochrane (2023), Ch. 2, p. 29: the core system obtained from a measure-theoretic one has the
pull-out property, so `PullOut`-hypothesis theorems of the core apply too. -/
theorem toExpectationSystem_pullOut [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) : (S.toExpectationSystem hfull).PullOut := by
  have := Fintype.ofFinite Ω
  intro t a y ha
  rw [toExpectationSystem_E] at ha ⊢
  rw [toExpectationSystem_E]
  have hm : StronglyMeasurable[S.𝓕 t] a := ha ▸ S.stronglyMeasurable_E t a
  refine S.eq_of_ae_eq hfull (S.E_pullOut hm (C := ∑ ω, |a ω|)
    (Eventually.of_forall fun ω => ?_) Integrable.of_finite)
  exact Finset.single_le_sum (f := fun ω => |a ω|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ ω)

end MeasExpectationSystem

/-! ### Bridge (a): every finite event tree is a measure-theoretic expectation system -/

namespace TreeBridge

open ExpectationsFiniteTree

variable {Ω} [Fintype Ω] (T : FiniteTree Ω)

/-- Cochrane (2023), Ch. 2, p. 29: the tree with an uninformative date prepended (date `0`
knows nothing, date `t + 1` knows what the original tree knows at `t`). -/
def trivialFirst : FiniteTree Ω where
  prob := T.prob
  prob_pos := T.prob_pos
  prob_sum := T.prob_sum
  info n := match n with
    | 0 => Setoid.ker (fun _ : Ω => ())
    | n + 1 => T.info n
  refines := by
    intro s t hst a b h
    cases s with
    | zero => exact Setoid.ker_def.2 rfl
    | succ s =>
      cases t with
      | zero => omega
      | succ t => exact T.refines (by omega) a b h

omit mΩ in
/-- Cochrane (2023), Ch. 2, p. 29: **the law of total expectation on a finite tree**,
`∑ p(ω) E_t x(ω) = ∑ p(ω) x(ω)`. -/
theorem sum_prob_condE (t : ℕ) (x : Ω → ℝ) :
    ∑ ω, T.prob ω * T.condE t x ω = ∑ ω, T.prob ω * x ω := by
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.prob_sum
    simp at this
  have htriv : ∀ a b, (trivialFirst T).info 0 a b := fun _ _ => Setoid.ker_def.2 rfl
  have h1 := (trivialFirst T).condE_of_trivial htriv ((trivialFirst T).condE (t + 1) x) ω₀
  have h2 := (trivialFirst T).condE_of_trivial htriv x ω₀
  rw [(trivialFirst T).condE_tower (Nat.zero_le (t + 1)) x] at h1
  exact h1.symm.trans h2

/-- Cochrane (2023), Ch. 2, p. 29: the tree's probabilities as a measure,
`μ = ∑_ω p(ω) δ_ω`. -/
noncomputable def treeMeasure : Measure Ω := ∑ ω, ENNReal.ofReal (T.prob ω) • Measure.dirac ω

/-- Cochrane (2023), Ch. 2, p. 29: `μ{ω} = p(ω)`. -/
theorem treeMeasure_singleton [DiscreteMeasurableSpace Ω] (ω : Ω) :
    treeMeasure T {ω} = ENNReal.ofReal (T.prob ω) := by
  classical
  rw [treeMeasure, Measure.finsetSum_apply, Finset.sum_eq_single ω]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton ω), smul_eq_mul,
      mul_one]
  · intro b _ hb
    rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hb),
      smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ ω) h

/-- Cochrane (2023), Ch. 2, p. 29: the tree measure is a probability measure. -/
theorem treeMeasure_univ : treeMeasure T Set.univ = 1 := by
  rw [treeMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => (T.prob_pos ω).le), T.prob_sum,
    ENNReal.ofReal_one]

/-- Cochrane (2023), Ch. 2, p. 29: the tree's probability measure. -/
noncomputable def treeProb : ProbabilityMeasure Ω := ⟨treeMeasure T, ⟨treeMeasure_univ T⟩⟩

/-- Cochrane (2023), Ch. 2, p. 29: integrals against the tree measure are weighted sums. -/
theorem integral_treeProb [DiscreteMeasurableSpace Ω] (f : Ω → ℝ) :
    ∫ ω, f ω ∂(treeProb T : Measure Ω) = ∑ ω, T.prob ω * f ω := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h : (treeProb T : Measure Ω) {ω} = ENNReal.ofReal (T.prob ω) := treeMeasure_singleton T ω
  rw [measureReal_def, h, ENNReal.toReal_ofReal (T.prob_pos ω).le, smul_eq_mul]

/-- Cochrane (2023), Ch. 2, p. 29: the tree's information as a filtration, `𝓕_t = σ(cell_t)`. -/
def treeFiltration [DiscreteMeasurableSpace Ω] : Filtration ℕ mΩ where
  seq t := MeasurableSpace.comap (Quotient.mk (T.info t)) ⊤
  mono' s t hst := by
    intro A hA
    obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Quotient.lift (Quotient.mk (T.info s)) (fun a b h => Quotient.sound (T.refines hst a b h))
        ⁻¹' B, MeasurableSpace.measurableSet_top, rfl⟩
  le' _ _ _ := MeasurableSet.of_discrete

/-- Cochrane (2023), Ch. 2, p. 29: the cell average `E_t x` is `𝓕_t`-measurable. -/
theorem stronglyMeasurable_condE [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    StronglyMeasurable[treeFiltration T t] (T.condE t x) := by
  have hm : Measurable[treeFiltration T t] (T.condE t x) := fun U _ =>
    MeasurableSpace.measurableSet_comap.2
      ⟨Quotient.lift (T.condE t x) (fun _ _ h => T.condE_congr x h) ⁻¹' U,
        MeasurableSpace.measurableSet_top, rfl⟩
  exact hm.stronglyMeasurable

/-- Cochrane (2023), Ch. 2, p. 29: the finite tree as a measure-theoretic expectation system. -/
noncomputable def treeSystem [DiscreteMeasurableSpace Ω] : MeasExpectationSystem Ω :=
  ⟨treeProb T, treeFiltration T⟩

/-- Cochrane (2023), Ch. 2, p. 29: every state of the tree has positive probability. -/
theorem treeSystem_fullSupport [DiscreteMeasurableSpace Ω] (ω : Ω) :
    (treeSystem T).μ {ω} ≠ 0 := by
  change treeMeasure T {ω} ≠ 0
  rw [treeMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact T.prob_pos ω

/-- Cochrane (2023), Ch. 2, p. 29: **bridge (a)** — the tree's cell average is Mathlib's
conditional expectation `μ[x | 𝓕_t]`, at every state and for every `x`. -/
theorem treeSystem_E [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    (treeSystem T).E t x = T.condE t x := by
  classical
  set S := treeSystem T
  refine (S.eq_of_ae_eq (treeSystem_fullSupport T)
    (ae_eq_condExp_of_forall_setIntegral_eq (S.𝓕.le t) Integrable.of_finite
      (fun _ _ _ => Integrable.of_finite.integrableOn) (fun A hA _ => ?_)
      (stronglyMeasurable_condE T t x).aestronglyMeasurable)).symm
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hA
  set a : Ω → ℝ := A.indicator fun _ => 1 with ha
  have hcell : ∀ ω ω', T.info t ω' ω → (ω' ∈ A ↔ ω ∈ A) := fun ω ω' h => by
    rw [← hB, Set.mem_preimage, Set.mem_preimage, Quotient.sound h]
  have hacell : T.condE t a = a := by
    funext ω
    refine T.condE_of_const_on_cell fun ω' h => ?_
    simp only [ha, Set.indicator, hcell ω ω' h]
  have hind : ∀ y : Ω → ℝ, A.indicator y = a * y := fun y => by
    funext ω
    by_cases h : ω ∈ A <;> simp [ha, Set.indicator, h]
  have hpo := finiteTree_pullOut T t a x hacell
  rw [FiniteTree.toExpectationSystem_E, FiniteTree.toExpectationSystem_E] at hpo
  rw [← integral_indicator MeasurableSet.of_discrete,
    ← integral_indicator MeasurableSet.of_discrete]
  change ∫ ω, A.indicator (T.condE t x) ω ∂(treeProb T : Measure Ω) =
    ∫ ω, A.indicator x ω ∂(treeProb T : Measure Ω)
  rw [integral_treeProb, integral_treeProb, hind, hind, ← hpo, sum_prob_condE]

/-- Cochrane (2023), Ch. 2, p. 29: the round trip — the core system obtained from the tree's
measure-theoretic system (bridge (b)) is the tree's own core system. -/
theorem treeSystem_toExpectationSystem_E [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    ((treeSystem T).toExpectationSystem (treeSystem_fullSupport T)).E t x =
      T.toExpectationSystem.E t x := by
  rw [MeasExpectationSystem.toExpectationSystem_E, treeSystem_E,
    FiniteTree.toExpectationSystem_E]

end TreeBridge

end Cochrane.DebtDeficitsInflation.ExpectationsMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A genuine infinite-horizon expectation system: i.i.d. shocks

Cochrane (2023), Ch. 2, §2.4, pp. 29–30 (unexpected inflation driven by news `ΔE_{t+1}`) and
§2.7, p. 42 (AR(1) surpluses `s_t = η s_{t−1} + ε_t`). The state space is `Ω = ℕ → ℝ` with the
infinite product `ν^ℕ` of a law `ν` on `ℝ` (Mathlib's `Measure.infinitePi`, built by
Ionescu-Tulcea/Carathéodory), the shocks are the coordinates `ε_t(ω) = ω_t`, and the filtration is
the natural one, `𝓕_t = σ(ε_0, …, ε_t)` (Mathlib's `Filtration.piLE`).

## How to use (API)

* `iidSystem ν : MeasExpectationSystem (ℕ → ℝ)` for any `ν : ProbabilityMeasure ℝ`; `shock t`.
* Independence: `indep_future` (future shocks ⟂ `𝓕_t`), `E_future` (`E_t g = E g` for `g`
  measurable w.r.t. the future), `E_shock_fun` (`E_t f(ε_{t+1}) = ∫ f dν`), `integral_shock_fun`.
* Moments (mean `0`, variance `σ² > 0`): `E_shock_zero`, `E_shock_sq_eq`, `condVar_shock`
  (`Var_t ε_{t+1} = σ²`).
* Nondegeneracy, not finitely supported: `shock_not_ae_E`, `singleton_lt_one`, `iid_singleton`
  (every history is null), `iid_countable_null`, `iid_not_finitely_supported`.
* Determinacy: `iid_news`, `iid_existsUnique_iff`, `iid_sunspot`.
* AR(1): `ar1`, `ar1_succ`, `ar1_adapted`, `ar1_bdd`, `iid_ar1_E`, `iid_ar1_condVar`,
  `iid_ar1_condVar_closed`.
* The fair `±1` coin: `coin`, `coin_mean`, `coin_var`, `coin_bdd`, `coin_economy`.
-/

namespace Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure

variable (ν : ProbabilityMeasure ℝ)

/-- Cochrane (2023), Ch. 2, p. 29: the law of the i.i.d. shock sequence, the infinite product
`ν^ℕ` on `Ω = ℕ → ℝ`. -/
noncomputable def iidProb : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨Measure.infinitePi (fun _ => (ν : Measure ℝ)), inferInstance⟩

/-- Cochrane (2023), Ch. 2, p. 29: the i.i.d. expectation system — `Ω = ℕ → ℝ`, `μ = ν^ℕ`, and the
natural filtration `𝓕_t = σ(ε_0, …, ε_t)`. -/
noncomputable def iidSystem : MeasExpectationSystem (ℕ → ℝ) := ⟨iidProb ν, Filtration.piLE⟩

/-- Cochrane (2023), Ch. 2, p. 29: the shock `ε_t(ω) = ω_t`. -/
def shock (t : ℕ) (ω : ℕ → ℝ) : ℝ := ω t

/-- Cochrane (2023), Ch. 2, p. 29: the shock of date `s ≤ t` is known at `t`. -/
theorem measurable_shock {s t : ℕ} (hst : s ≤ t) : Measurable[(iidSystem ν).𝓕 t] (shock s) := by
  change Measurable[MeasurableSpace.comap (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t)
    MeasurableSpace.pi] (fun ω => Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω ⟨s, hst⟩)
  exact (measurable_pi_apply (⟨s, hst⟩ : Set.Iic t)).comp (comap_measurable _)

/-! ### Independence: the future is independent of the present information -/

/-- Cochrane (2023), Ch. 2, p. 29: the σ-algebra generated by the date-`j` shock. -/
abbrev coordSigma (j : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun ω : ℕ → ℝ => ω j) inferInstance

/-- Cochrane (2023), Ch. 2, p. 29: the σ-algebra of the future shocks `ε_{t+1}, ε_{t+2}, …`. -/
abbrev futureSigma (t : ℕ) : MeasurableSpace (ℕ → ℝ) := ⨆ j ∈ Set.Ioi t, coordSigma j

/-- Cochrane (2023), Ch. 2, p. 29: each shock σ-algebra is a sub-σ-algebra. -/
theorem coordSigma_le (j : ℕ) : coordSigma j ≤ MeasurableSpace.pi :=
  (measurable_pi_apply j).comap_le

/-- Cochrane (2023), Ch. 2, p. 29: the future σ-algebra is a sub-σ-algebra. -/
theorem futureSigma_le (t : ℕ) : futureSigma t ≤ MeasurableSpace.pi :=
  iSup₂_le fun j _ => coordSigma_le j

/-- Cochrane (2023), Ch. 2, p. 29: the shocks are mutually independent under `ν^ℕ`. -/
theorem iIndep_coord : iIndep coordSigma (iidSystem ν).μ :=
  (iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
    (fun _ => measurable_id)).iIndep

/-- Cochrane (2023), Ch. 2, p. 29: date-`t` information is generated by `ε_0, …, ε_t`. -/
theorem filtration_le_past (t : ℕ) :
    (iidSystem ν).𝓕 t ≤ ⨆ j ∈ Set.Iic t, coordSigma j := by
  change MeasurableSpace.comap (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t)
    MeasurableSpace.pi ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup_le fun j => ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic t) => coordSigma i) j.1 j.2

/-- Cochrane (2023), Ch. 2, p. 29: **the future shocks are independent of date-`t` information**.
-/
theorem indep_future (t : ℕ) : Indep (futureSigma t) ((iidSystem ν).𝓕 t) (iidSystem ν).μ :=
  indep_of_indep_of_le_right (indep_iSup_of_disjoint coordSigma_le (iIndep_coord ν)
    (Set.disjoint_left.2 fun _ h1 h2 => absurd (Set.mem_Ioi.1 h1) (not_lt.2 (Set.mem_Iic.1 h2))))
    (filtration_le_past ν t)

/-- Cochrane (2023), Ch. 2, p. 29: **independence ⇒ the forecast of a function of the future is its
unconditional mean**, `E_t g = E g` a.e. -/
theorem E_future (t : ℕ) {g : (ℕ → ℝ) → ℝ} (hg : StronglyMeasurable[futureSigma t] g) :
    (iidSystem ν).E t g =ᵐ[(iidSystem ν).μ] fun _ => ∫ ω, g ω ∂(iidSystem ν).μ :=
  condExp_indep_eq (futureSigma_le t) ((iidSystem ν).𝓕.le t) hg (indep_future ν t)

/-- Cochrane (2023), Ch. 2, p. 29: a function of the next shock is measurable for the future. -/
theorem measurable_future_fun (t : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable[futureSigma t] (fun ω : ℕ → ℝ => f (ω (t + 1))) :=
  hf.comp (Measurable.of_comap_le
    (le_iSup₂ (f := fun i (_ : i ∈ Set.Ioi t) => coordSigma i) (t + 1) (Nat.lt_succ_self t)))

/-- Cochrane (2023), Ch. 2, p. 29: each shock has law `ν`, so `E f(ε_i) = ∫ f dν`. -/
theorem integral_shock_fun (i : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω i) ∂(iidSystem ν).μ = ∫ x, f x ∂(ν : Measure ℝ) := by
  have h := integral_map (μ := Measure.infinitePi (fun _ => (ν : Measure ℝ)))
    (φ := fun ω : ℕ → ℝ => ω i) (measurable_pi_apply i).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at h
  exact h.symm

/-- Cochrane (2023), Ch. 2, p. 29: `E_t f(ε_{t+1}) = ∫ f dν` a.e. -/
theorem E_shock_fun (t : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (iidSystem ν).E t (fun ω => f (ω (t + 1))) =ᵐ[(iidSystem ν).μ]
      fun _ => ∫ x, f x ∂(ν : Measure ℝ) := by
  rw [← integral_shock_fun ν (t + 1) hf]
  exact E_future ν t (measurable_future_fun t hf).stronglyMeasurable

/-- Cochrane (2023), Ch. 2, p. 29: `E_t ε_{t+1} = E ε` a.e. -/
theorem E_shock (t : ℕ) :
    (iidSystem ν).E t (shock (t + 1)) =ᵐ[(iidSystem ν).μ] fun _ => ∫ x, x ∂(ν : Measure ℝ) :=
  E_shock_fun ν t measurable_id

/-- Cochrane (2023), Ch. 2, p. 29: `E_t ε_{t+1}² = E ε²` a.e. -/
theorem E_shock_sq (t : ℕ) :
    (iidSystem ν).E t (shock (t + 1) ^ 2) =ᵐ[(iidSystem ν).μ]
      fun _ => ∫ x, x ^ 2 ∂(ν : Measure ℝ) :=
  E_shock_fun ν t (measurable_id.pow_const 2)

/-- Cochrane (2023), Ch. 2, p. 29: each shock is bounded when `ν` has bounded support. -/
theorem shock_ae_bdd {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, |shock t ω| ≤ B :=
  (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t).quasiMeasurePreserving.ae hbdd

/-! ### Mean-zero, nondegenerate shocks -/

variable {ν}

/-- Cochrane (2023), Ch. 2, p. 29: with mean-zero shocks, `E_t ε_{t+1} = 0` a.e. -/
theorem E_shock_zero (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (t : ℕ) :
    (iidSystem ν).E t (shock (t + 1)) =ᵐ[(iidSystem ν).μ] 0 := by
  filter_upwards [E_shock ν t] with ω h
  rw [h, hmean, Pi.zero_apply]

/-- Cochrane (2023), Ch. 2, p. 29: **constant conditional variance**, `E_t ε_{t+1}² = σ²` a.e. -/
theorem E_shock_sq_eq {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (t : ℕ) :
    (iidSystem ν).E t (shock (t + 1) ^ 2) =ᵐ[(iidSystem ν).μ] fun _ => σ2 := by
  filter_upwards [E_shock_sq ν t] with ω h
  rw [h, hvar]

/-- Cochrane (2023), Ch. 2, p. 29: the conditional variance of the next shock is `σ²`. -/
theorem condVar_shock {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (t : ℕ) :
    Var[shock (t + 1); (iidSystem ν).μ | (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ] fun _ => σ2 := by
  change (iidSystem ν).E t ((shock (t + 1) - (iidSystem ν).E t (shock (t + 1))) ^ 2) =ᵐ[_] _
  refine ((iidSystem ν).E_congr ?_ t).trans (E_shock_sq_eq hvar t)
  filter_upwards [E_shock_zero hmean t] with ω h
  rw [Pi.pow_apply, Pi.pow_apply, Pi.sub_apply, h, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), Ch. 2, p. 29: **the shocks are nondegenerate at every date** — `ε_{t+1}` is
not a.e. equal to its date-`t` forecast (a fortiori not known at `t`). -/
theorem shock_not_ae_E {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) (t : ℕ) :
    ¬ shock (t + 1) =ᵐ[(iidSystem ν).μ] (iidSystem ν).E t (shock (t + 1)) := by
  intro h
  have h0 := h.trans (E_shock_zero hmean t)
  have hi : ∫ ω, (ω (t + 1)) ^ 2 ∂(iidSystem ν).μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with ω h1
    simp only [shock, Pi.zero_apply] at h1
    simp [h1]
  rw [integral_shock_fun ν (t + 1) (f := fun x => x ^ 2) (measurable_id.pow_const 2), hvar] at hi
  linarith

/-- Cochrane (2023), Ch. 2, p. 29: a nondegenerate mean-zero law has no atom of mass one. -/
theorem singleton_lt_one {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) (x : ℝ) :
    (ν : Measure ℝ) {x} < 1 := by
  refine lt_of_le_of_ne prob_le_one fun h1 => ?_
  have hae : ∀ᵐ y ∂(ν : Measure ℝ), y = x := by
    rw [ae_iff]
    have hs : {y : ℝ | ¬ y = x} = {x}ᶜ := by
      ext y
      simp
    rw [hs, prob_compl_eq_zero_iff (measurableSet_singleton x)]
    exact h1
  have hm : ∫ y, y ∂(ν : Measure ℝ) = x := by
    rw [integral_congr_ae (f := fun y => y) (g := fun _ => x) hae]
    simp
  have hv : ∫ y, y ^ 2 ∂(ν : Measure ℝ) = x ^ 2 := by
    rw [integral_congr_ae (f := fun y => y ^ 2) (g := fun _ => x ^ 2)
      (hae.mono fun y h => by rw [h])]
    simp
  rw [hmean] at hm
  rw [hvar, ← hm] at hv
  linarith

/-- Cochrane (2023), Ch. 2, p. 29: the atoms of a nondegenerate mean-zero law are uniformly below
one: `ν{x} ≤ q < 1` for all `x`. -/
theorem exists_singleton_le {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) :
    ∃ q < 1, ∀ x, (ν : Measure ℝ) {x} ≤ q := by
  by_cases h : ∃ x₀, 2⁻¹ < (ν : Measure ℝ) {x₀}
  · obtain ⟨x₀, hx₀⟩ := h
    refine ⟨max 2⁻¹ ((ν : Measure ℝ) {x₀}),
      max_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) (singleton_lt_one hmean hvar hσ x₀),
      fun x => ?_⟩
    by_cases hx : x = x₀
    · rw [hx]
      exact le_max_right _ _
    · by_contra hlt
      push Not at hlt
      have h1 : (ν : Measure ℝ) {x} + (ν : Measure ℝ) {x₀} ≤ 1 := by
        rw [← measure_union (Set.disjoint_singleton.2 hx) (measurableSet_singleton _)]
        exact prob_le_one
      have h2 : 1 < (ν : Measure ℝ) {x} + (ν : Measure ℝ) {x₀} := by
        calc (1 : ENNReal) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
          _ < (ν : Measure ℝ) {x} + (ν : Measure ℝ) {x₀} :=
            ENNReal.add_lt_add (lt_of_le_of_lt (le_max_left _ _) hlt) hx₀
      exact absurd h1 (not_le.2 h2)
  · push Not at h
    exact ⟨2⁻¹, ENNReal.inv_lt_one.2 ENNReal.one_lt_two, h⟩

/-- Cochrane (2023), Ch. 2, p. 29: **every single history has probability zero** under `ν^ℕ`. -/
theorem iid_singleton {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) (ω : ℕ → ℝ) :
    (iidSystem ν).μ {ω} = 0 := by
  obtain ⟨q, hq, hle⟩ := exists_singleton_le hmean hvar hσ
  have hb : ∀ n, (iidSystem ν).μ {ω} ≤ q ^ n := by
    intro n
    calc (iidSystem ν).μ {ω}
        ≤ Measure.infinitePi (fun _ => (ν : Measure ℝ))
            (Set.pi ↑(Finset.range n) fun i => {ω i}) :=
          measure_mono fun ω' h i _ => by rw [Set.mem_singleton_iff.mp h]; rfl
      _ = ∏ i ∈ Finset.range n, (ν : Measure ℝ) {ω i} :=
          Measure.infinitePi_pi (fun _ => (ν : Measure ℝ)) fun i _ => measurableSet_singleton _
      _ ≤ q ^ n := by
          simpa using Finset.prod_le_pow_card (Finset.range n) _ q fun i _ => hle (ω i)
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hb)
    bot_le

/-- Cochrane (2023), Ch. 2, p. 29: **not finitely (or countably) supported** — every countable set
of histories is null, in contrast with a finite event tree. -/
theorem iid_countable_null {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) {F : Set (ℕ → ℝ)}
    (hF : F.Countable) : (iidSystem ν).μ F = 0 := by
  have : NullSingletonClass (iidSystem ν).μ := ⟨iid_singleton hmean hvar hσ⟩
  exact hF.measure_zero _

/-- Cochrane (2023), Ch. 2, p. 29: no finite set of histories carries the probability. -/
theorem iid_not_finitely_supported {σ2 : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2) (F : Finset (ℕ → ℝ)) :
    (iidSystem ν).μ ↑F ≠ 1 := by
  rw [iid_countable_null hmean hvar hσ F.countable_toSet]
  exact zero_ne_one

/-! ### Determinacy with i.i.d. news -/

/-- Cochrane (2023), Ch. 2, p. 29: the i.i.d. filtration carries genuinely random bounded news. -/
theorem iid_news {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    ∃ s η B, StronglyMeasurable[(iidSystem ν).𝓕 (s + 1)] η ∧
      (∀ᵐ ω ∂(iidSystem ν).μ, |η ω| ≤ B) ∧ ¬ η =ᵐ[(iidSystem ν).μ] (iidSystem ν).E s η :=
  ⟨0, shock 1, B, (measurable_shock ν le_rfl).stronglyMeasurable, shock_ae_bdd ν hbdd 1,
    shock_not_ae_E hmean hvar hσ 0⟩

/-- Cochrane (2023), Ch. 2, p. 29: **determinacy in the i.i.d. economy** — bounded adapted
solutions of `z_t = a E_t z_{t+1} + u_t` exist and are unique for every bounded adapted `u` iff
`|a| < 1`. -/
theorem iid_existsUnique_iff {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (a : ℝ) :
    (∀ u : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem ν).𝓕 u → (iidSystem ν).BddProc u →
      (∃ z, (iidSystem ν).Solves a u z ∧ StronglyAdapted (iidSystem ν).𝓕 z ∧
        (iidSystem ν).BddProc z) ∧
      ∀ z₁ z₂, (iidSystem ν).Solves a u z₁ → (iidSystem ν).Solves a u z₂ →
        StronglyAdapted (iidSystem ν).𝓕 z₁ → StronglyAdapted (iidSystem ν).𝓕 z₂ →
        (iidSystem ν).BddProc z₁ → (iidSystem ν).BddProc z₂ →
        ∀ t, z₁ t =ᵐ[(iidSystem ν).μ] z₂ t) ↔ |a| < 1 :=
  (iidSystem ν).existsUnique_iff (iid_news hmean hvar hσ hbdd) a

/-- Cochrane (2023), Ch. 2, p. 29: for `|a| ≥ 1` the i.i.d. economy has a bounded, genuinely random
sunspot solution of `z_t = a E_t z_{t+1}` next to `z = 0`, driven by the date-1 shock. -/
theorem iid_sunspot {σ2 B a : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (ha : 1 ≤ |a|) :
    ∃ z, (iidSystem ν).Solves a 0 z ∧ StronglyAdapted (iidSystem ν).𝓕 z ∧
      (iidSystem ν).BddProc z ∧ ¬ z 1 =ᵐ[(iidSystem ν).μ] 0 :=
  (iidSystem ν).not_unique_of_one_le ha (measurable_shock ν le_rfl).stronglyMeasurable
    (shock_ae_bdd ν hbdd 1) (shock_not_ae_E hmean hvar hσ 0) ((iidSystem ν).solves_zero a)
    (fun _ => stronglyMeasurable_zero) ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩

/-! ### AR(1) with i.i.d. innovations -/

/-- Cochrane (2023), p. 42: the AR(1) `u_0 = ε_0`, `u_{t+1} = ρ u_t + ε_{t+1}`. -/
def ar1 (ρ : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => shock 0
  | t + 1 => fun ω => ρ * ar1 ρ t ω + shock (t + 1) ω

/-- Cochrane (2023), p. 42: the AR(1) law of motion. -/
theorem ar1_succ (ρ : ℝ) (t : ℕ) : ar1 ρ (t + 1) = ρ • ar1 ρ t + shock (t + 1) := rfl

variable (ν) in
/-- Cochrane (2023), p. 42: the AR(1) is adapted. -/
theorem ar1_adapted (ρ : ℝ) : StronglyAdapted (iidSystem ν).𝓕 (ar1 ρ) := by
  intro t
  induction t with
  | zero => exact (measurable_shock ν le_rfl).stronglyMeasurable
  | succ t ih =>
    rw [ar1_succ]
    exact ((ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t))).const_smul ρ).add
      (measurable_shock ν le_rfl).stronglyMeasurable

/-- Cochrane (2023), p. 42: for `|ρ| < 1` and shocks bounded by `B`, `|u_t| ≤ B / (1 − |ρ|)`. -/
theorem ar1_bdd {ρ B : ℝ} (hρ : |ρ| < 1) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, |ar1 ρ t ω| ≤ B / (1 - |ρ|) := by
  obtain ⟨x₀, hx₀⟩ := hbdd.exists
  have hB : 0 ≤ B := (abs_nonneg _).trans hx₀
  have h1 : 0 < 1 - |ρ| := by linarith
  filter_upwards [ae_all_iff.2 (shock_ae_bdd ν hbdd)] with ω h
  induction t with
  | zero =>
    refine (h 0).trans ?_
    rw [le_div_iff₀ h1]
    nlinarith [abs_nonneg ρ]
  | succ t ih =>
    change |ρ * ar1 ρ t ω + shock (t + 1) ω| ≤ _
    have key : |ρ| * (B / (1 - |ρ|)) + B = B / (1 - |ρ|) := by
      field_simp
      ring
    calc |ρ * ar1 ρ t ω + shock (t + 1) ω| ≤ |ρ| * |ar1 ρ t ω| + |shock (t + 1) ω| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ |ρ| * (B / (1 - |ρ|)) + B :=
          add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg ρ)) (h (t + 1))
      _ = B / (1 - |ρ|) := key

/-- Cochrane (2023), p. 42: **AR(1) forecasts**, `E_t u_{t+j} = ρʲ u_t` a.e. -/
theorem iid_ar1_E {ρ B : ℝ} (hρ : |ρ| < 1) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t j : ℕ) :
    (iidSystem ν).E t (ar1 ρ (t + j)) =ᵐ[(iidSystem ν).μ] ρ ^ j • ar1 ρ t :=
  (iidSystem ν).ar1_E (ar1_succ ρ) (ar1_adapted ν ρ) ⟨_, ar1_bdd hρ hbdd⟩
    (E_shock_zero hmean) t j

/-- Cochrane (2023), p. 42: **AR(1) conditional variance**,
`Var_t(u_{t+j}) = σ² ∑_{i<j} ρ^{2i}` a.e. -/
theorem iid_ar1_condVar {ρ B σ2 : ℝ} (hρ : |ρ| < 1) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (t j : ℕ) :
    Var[ar1 ρ (t + j); (iidSystem ν).μ | (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ]
      fun _ => σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) :=
  (iidSystem ν).ar1_condVar (ar1_succ ρ) (ar1_adapted ν ρ) ⟨_, ar1_bdd hρ hbdd⟩
    (E_shock_zero hmean) (E_shock_sq_eq hvar) t j

/-- Cochrane (2023), p. 42: closed form `Var_t(u_{t+j}) = σ² (1 − ρ^{2j}) / (1 − ρ²)`. -/
theorem iid_ar1_condVar_closed {ρ B σ2 : ℝ} (hρ : |ρ| < 1)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t j : ℕ) :
    Var[ar1 ρ (t + j); (iidSystem ν).μ | (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ]
      fun _ => σ2 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2) := by
  have hρ2 : ρ ^ 2 ≠ 1 := by
    intro h
    have : |ρ| ^ 2 = 1 := by rw [sq_abs]; exact h
    nlinarith [abs_nonneg ρ]
  exact (iidSystem ν).ar1_condVar_closed hρ2 (ar1_succ ρ) (ar1_adapted ν ρ)
    ⟨_, ar1_bdd hρ hbdd⟩ (E_shock_zero hmean) (E_shock_sq_eq hvar) t j

/-! ### A concrete law: the fair `±1` coin -/

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin `ν = ½ δ₁ + ½ δ₋₁` as a measure. -/
noncomputable def coinMeasure : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac 1 + Measure.dirac (-1))

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin has total mass one. -/
theorem coinMeasure_univ : coinMeasure Set.univ = 1 := by
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin as a probability measure. -/
noncomputable def coin : ProbabilityMeasure ℝ := ⟨coinMeasure, ⟨coinMeasure_univ⟩⟩

/-- Cochrane (2023), Ch. 2, p. 29: integrals against the coin, `∫ f dν = (f 1 + f (−1)) / 2`. -/
theorem integral_coin (f : ℝ → ℝ) :
    ∫ x, f x ∂(coin : Measure ℝ) = (f 1 + f (-1)) / 2 := by
  change ∫ x, f x ∂coinMeasure = _
  rw [coinMeasure, integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Cochrane (2023), Ch. 2, p. 29: the coin has mean zero. -/
theorem coin_mean : ∫ x, x ∂(coin : Measure ℝ) = 0 := by
  rw [integral_coin]
  norm_num

/-- Cochrane (2023), Ch. 2, p. 29: the coin has variance one. -/
theorem coin_var : ∫ x, x ^ 2 ∂(coin : Measure ℝ) = 1 := by
  rw [integral_coin]
  norm_num

/-- Cochrane (2023), Ch. 2, p. 29: the coin is bounded by one. -/
theorem coin_bdd : ∀ᵐ x ∂(coin : Measure ℝ), |x| ≤ 1 := by
  change ∀ᵐ x ∂coinMeasure, |x| ≤ 1
  rw [ae_iff]
  have hs : MeasurableSet {x : ℝ | ¬ |x| ≤ 1} :=
    (measurableSet_le continuous_abs.measurable measurable_const).compl
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Set.indicator, Set.mem_ofPred_eq]
  norm_num

/-- Cochrane (2023), Ch. 2, p. 29 and p. 42: **the coin economy** — `ε_t = ±1` i.i.d. fair coins —
satisfies everything: `E_t ε_{t+1} = 0`, `Var_t ε_{t+1} = 1`, every history is null, the shock is
never predictable, determinacy holds iff `|a| < 1`, and the AR(1) has
`Var_t(u_{t+j}) = (1 − ρ^{2j}) / (1 − ρ²)`. -/
theorem coin_economy (ρ a : ℝ) (hρ : |ρ| < 1) :
    (∀ t, (iidSystem coin).E t (shock (t + 1)) =ᵐ[(iidSystem coin).μ] 0) ∧
    (∀ t, Var[shock (t + 1); (iidSystem coin).μ | (iidSystem coin).𝓕 t]
      =ᵐ[(iidSystem coin).μ] fun _ => 1) ∧
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
    (∀ t, ¬ shock (t + 1) =ᵐ[(iidSystem coin).μ] (iidSystem coin).E t (shock (t + 1))) ∧
    ((∀ u : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem coin).𝓕 u →
      (iidSystem coin).BddProc u →
      (∃ z, (iidSystem coin).Solves a u z ∧ StronglyAdapted (iidSystem coin).𝓕 z ∧
        (iidSystem coin).BddProc z) ∧
      ∀ z₁ z₂, (iidSystem coin).Solves a u z₁ → (iidSystem coin).Solves a u z₂ →
        StronglyAdapted (iidSystem coin).𝓕 z₁ → StronglyAdapted (iidSystem coin).𝓕 z₂ →
        (iidSystem coin).BddProc z₁ → (iidSystem coin).BddProc z₂ →
        ∀ t, z₁ t =ᵐ[(iidSystem coin).μ] z₂ t) ↔ |a| < 1) ∧
    (∀ t j, (iidSystem coin).E t (ar1 ρ (t + j)) =ᵐ[(iidSystem coin).μ] ρ ^ j • ar1 ρ t) ∧
    (∀ t j, Var[ar1 ρ (t + j); (iidSystem coin).μ | (iidSystem coin).𝓕 t]
      =ᵐ[(iidSystem coin).μ] fun _ => 1 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2)) :=
  ⟨E_shock_zero coin_mean, condVar_shock coin_mean coin_var,
    iid_singleton coin_mean coin_var one_pos, shock_not_ae_E coin_mean coin_var one_pos,
    iid_existsUnique_iff coin_mean coin_var one_pos coin_bdd a,
    iid_ar1_E hρ coin_mean coin_bdd, iid_ar1_condVar_closed hρ coin_mean coin_var coin_bdd⟩

end Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditioning down on a general probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, pp. 101–102, and
Online Appendix Chapter 2, §2.1.7, eqs. (2.22)–(2.23), pp. 602–603; the identities conditioned
down are (3.17)–(3.20), pp. 63–65, and (4.2), p. 87.

People condition on `𝓕_t` (`Ω_t` in the book), the econometrician on a coarser `𝓖_t ≤ 𝓕_t`
(`I_t ⊂ Ω_t`, the VAR's information). Both are filtrations on one probability space `(Ω, P)`, and
both expectation operators are Mathlib's conditional expectations `P[· | 𝓕_t]`, `P[· | 𝓖_t]`, so
nothing is finite or finitely supported. The cross-information tower property
`E(E(x|𝓕_t)|𝓖_t) = E(x|𝓖_t)` is Mathlib's `condExp_condExp_of_le`.

## Main definitions

* `coarsen S 𝓖`: the econometrician's system — same probability, filtration `𝓖`.
* `Nested S 𝓖`: `𝓖_t ≤ 𝓕_t` at every date; `MeasCoarser SI SΩ` for a pair of systems, and
  `eq_coarsen`: every nested pair is of the form `(coarsen SΩ 𝓖, SΩ)`.
* `KnownAE 𝓖 t v`: `v` is a.e. equal to a `𝓖_t`-measurable variable (`v_t ∈ I_t`).
* `lagFiltration S`: the econometrician sees the agents' information with a one-period lag.

## Main results

* `E_coarsen_tower`, `condDown_general` (`E(X|I_t) = E(v_t|I_t)` always), `condDown_iff`
  (`v_t = E(X|I_t)` iff `v_t ∈ I_t`), `known_iff_E_eq`.
* The valuation equation (2.22) ⇒ (2.23): `condDown_valuation` (the econometrician's discounted
  forecasts sum to `E(v_t|I_t)`) and `condDown_valuation_iff` (to `v_t` iff `v_t ∈ I_t`).
* The flow identity (3.17) ex post: `pv_ex_post`, `pv_E` (under ANY information, the discounted
  forecasts sum to the forecast of `v_t`), `pv_agents`, `condDown_flow_iff` (Links.condDown_flow
  on a general probability space).
* Unexpected inflation (3.20): `innov_pv`, `unexpected_inflation_any` — for ANY information set,
  `Δπ − Δrⁿ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr + Δ_{t+1}v_t`; `unexpected_inflation_agents` (the
  book's (3.20), the extra term vanishes); `innov_coarsen_of_known` (it also vanishes for the
  econometrician when `v_t ∈ I_t`); `E_coarsen_innov` (the agents' news is unforecastable with the
  coarser information).
* The simple model (4.2): `constExp_condDown`, `innov_return_condDown` (constant expected returns
  condition down), `simple_model_any` (`Δπ − Δrⁿ = −∑ρʲΔs̃ + Δ_{t+1}v_t` for any nested
  information), `simple_model_agents` (`Δπ = −∑ρʲΔs̃`), `simple_model_econ_iff` (the book's form
  holds for the econometrician iff `Δ^I_{t+1}v_t = 0`).
* Correction: `Example.econ_decomp_counterexample` — i.i.d. shocks, MA(1) surplus, lagged
  econometrician: the agents' decomposition holds, the econometrician's book-form decomposition
  fails.
* Links: `coarsen_toExpectationSystem_E` (the finite full-support case is the
  `ConditioningDown.CondExp.condExpSystem` of Mathlib), `coarser_core` (the abstract `Coarser`),
  `condDown_iff_core` (the general `condDown_iff` IS the abstract `ConditioningDown.condDown_iff`
  there), `unexpected_inflation_core` (the core (3.20) for the bridged system).
-/

namespace Cochrane.DebtDeficitsInflation.ConditioningDownMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.DebtDeficitsInflation.ExpectationsMeasure
open Cochrane.DebtDeficitsInflation.LinearizedIdentities (Recursion Flow rec_finite tvc_of_bound
  flow_iff_recursion)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Two nested information sets -/

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the econometrician's expectation system — the same
probability as the agents' system `S`, with the coarser filtration `𝓖`. -/
def coarsen (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) : MeasExpectationSystem Ω :=
  ⟨S.P, 𝓖⟩

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the econometrician's information is contained in the
agents' at every date. -/
def Nested (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) : Prop := ∀ t, 𝓖 t ≤ S.𝓕 t

/-- Cochrane (2023), Online Appendix p. 602 ("two nested expectation systems"): `SI` and `SΩ`
share the probability and `SI`'s information is contained in `SΩ`'s. -/
def MeasCoarser (SI SΩ : MeasExpectationSystem Ω) : Prop := SI.P = SΩ.P ∧ ∀ t, SI.𝓕 t ≤ SΩ.𝓕 t

/-- Cochrane (2023), Online Appendix p. 602: every nested pair of systems is the agents' system
together with its coarsening by the econometrician's filtration. -/
theorem eq_coarsen {SI SΩ : MeasExpectationSystem Ω} (h : MeasCoarser SI SΩ) :
    SI = coarsen SΩ SI.𝓕 ∧ Nested SΩ SI.𝓕 := by
  obtain ⟨hP, hle⟩ := h
  refine ⟨?_, hle⟩
  cases SI
  cases SΩ
  simp only at hP
  subst hP
  rfl

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): `v` is (a.e. equal to) a `𝓖_t`-measurable random
variable. -/
def KnownAE (μ : Measure Ω) (𝓖 : Filtration ℕ mΩ) (t : ℕ) (v : Ω → ℝ) : Prop :=
  ∃ w : Ω → ℝ, StronglyMeasurable[𝓖 t] w ∧ v =ᵐ[μ] w

/-- Cochrane (2023), p. 101: the econometrician's probability is the agents'. -/
theorem coarsen_μ (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) :
    (coarsen S 𝓖).μ = S.μ := rfl

/-- Cochrane (2023), p. 101: the econometrician's forecast is the Mathlib conditional expectation
given `𝓖_t`. -/
theorem coarsen_E (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) (t : ℕ) (x : Ω → ℝ) :
    (coarsen S 𝓖).E t x = S.μ[x | 𝓖 t] := rfl

/-- Cochrane (2023), p. 101 (`E(E(x|Ω_t)|I_s) = E(x|I_s)`, `s ≤ t`): the tower property across
information sets (Mathlib's `condExp_condExp_of_le`). -/
theorem E_coarsen_tower {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    (coarsen S 𝓖).E s (S.E t x) =ᵐ[S.μ] (coarsen S 𝓖).E s x :=
  condExp_condExp_of_le ((𝓖.mono hst).trans (h t)) (S.𝓕.le t)

/-- Cochrane (2023), p. 101 ("if not, the left-hand side should be `E(v_t|I_t)`"): if
`v_t = E(X|Ω_t)` a.e., then `E(X|I_t) = E(v_t|I_t)` a.e., for every random variable `X`. -/
theorem condDown_general {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {t : ℕ} {v X : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    (coarsen S 𝓖).E t X =ᵐ[S.μ] (coarsen S 𝓖).E t v :=
  ((E_coarsen_tower h le_rfl X).symm.trans ((coarsen S 𝓖).E_congr hv t).symm)

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): an integrable `v` is a.e. its own `I_t`-forecast iff it
is a.e. `𝓖_t`-measurable. -/
theorem known_iff_E_eq (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) {t : ℕ}
    {v : Ω → ℝ} (hi : Integrable v S.μ) :
    v =ᵐ[S.μ] (coarsen S 𝓖).E t v ↔ KnownAE S.μ 𝓖 t v := by
  constructor
  · intro h
    exact ⟨_, (coarsen S 𝓖).stronglyMeasurable_E t v, h⟩
  · rintro ⟨w, hw, hvw⟩
    have hwi : Integrable w S.μ := hi.congr hvw
    have hE : (coarsen S 𝓖).E t w = w := (coarsen S 𝓖).E_of_stronglyMeasurable hw hwi
    exact hvw.trans (hE ▸ ((coarsen S 𝓖).E_congr hvw t).symm)

/-- Cochrane (2023), p. 101 ("this conditioning down is valid, so long as `v_t ∈ I_t`") and Online
Appendix eqs. (2.22)–(2.23), p. 602 ("only if we include the value of debt in the VAR"): on any
probability space, if `v_t = E(X|Ω_t)` a.e., then `v_t = E(X|I_t)` a.e. **if and only if** `v_t` is
(a.e.) `I_t`-measurable. No integrability of `X` is needed. -/
theorem condDown_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {t : ℕ} {v X : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    v =ᵐ[S.μ] (coarsen S 𝓖).E t X ↔ KnownAE S.μ 𝓖 t v := by
  have hi : Integrable v S.μ := (S.integrable_E t X).congr hv.symm
  rw [← known_iff_E_eq S 𝓖 hi]
  have hg := condDown_general h hv
  constructor
  · intro h1
    exact h1.trans hg
  · intro h1
    exact h1.trans hg.symm

/-- Cochrane (2023), p. 102 ("the only way to rescue such a calculation is to assume … `I_t = Ω_t`
… `v_t` would be an exact function of the observed information"): with no coarsening, `v_t` is
always known. -/
theorem known_of_same (S : MeasExpectationSystem Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v =ᵐ[S.μ] S.E t X) : KnownAE S.μ S.𝓕 t v :=
  ⟨_, S.stronglyMeasurable_E t X, hv⟩

/-- Cochrane (2023), eq. (2.13), p. 30, across information sets: the agents' news
`Δ^Ω_{t+1}x = E(x|Ω_{t+1}) − E(x|Ω_t)` cannot be forecast with the coarser information,
`E(Δ^Ω_{t+1}x | I_s) = 0` for `s ≤ t`. -/
theorem E_coarsen_innov {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    (coarsen S 𝓖).E s (S.innov t x) =ᵐ[S.μ] 0 := by
  filter_upwards [(coarsen S 𝓖).E_sub (S.integrable_E (t + 1) x) (S.integrable_E t x) s,
    E_coarsen_tower h (hst.trans (Nat.le_succ t)) x, E_coarsen_tower h hst x] with ω h1 h2 h3
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, h1, Pi.sub_apply, h2, h3, sub_self,
    Pi.zero_apply]

/-! ### Present values: the valuation equation and the flow identity -/

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101: if the valuation equation holds with
the agents' information, `v_t = E(∑ρʲs_{t+1+j}|Ω_t)` a.e. (bounded measurable surpluses,
`|ρ| < 1`), then with the econometrician's information the discounted forecasts sum to
`E(v_t|I_t)`: a.e. `∑ρʲE(s_{t+1+j}|I_t) = E(v_t|I_t)`, a genuine `HasSum`. -/
theorem condDown_valuation {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ j, AEStronglyMeasurable (s j) S.μ) {K : ℝ} (hs : ∀ j, ∀ᵐ ω ∂S.μ, |s j ω| ≤ K)
    {t : ℕ} {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω)
      ((coarsen S 𝓖).E t v ω) := by
  set G := coarsen S 𝓖
  have hc : Summable fun j => |ρ| ^ j * K :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K
  have hb : ∀ j, ∀ᵐ ω ∂S.μ, |ρ ^ j * s (t + 1 + j) ω| ≤ |ρ| ^ j * K := fun j => by
    filter_upwards [hs (t + 1 + j)] with ω hω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left hω (pow_nonneg (abs_nonneg _) _)
  have hE := G.E_hasSum (f := fun j ω => ρ ^ j * s (t + 1 + j) ω) hc
    (fun j => (hsm (t + 1 + j)).const_mul _) hb t
  have hsmul : ∀ j, G.E t (fun ω => ρ ^ j * s (t + 1 + j) ω) =ᵐ[S.μ]
      fun ω => ρ ^ j * G.E t (s (t + 1 + j)) ω := fun j => G.E_smul (ρ ^ j) (s (t + 1 + j)) t
  filter_upwards [hE, ae_all_iff.2 hsmul, condDown_general h hv] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101 ("this conditioning down is valid, so
long as `v_t ∈ I_t`"): under the valuation equation with the agents' information, the
econometrician's discounted forecasts sum to `v_t` a.e. **iff** `v_t` is in the VAR information. -/
theorem condDown_valuation_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ j, AEStronglyMeasurable (s j) S.μ) {K : ℝ} (hs : ∀ j, ∀ᵐ ω ∂S.μ, |s j ω| ≤ K)
    {t : ℕ} {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω) (v ω)) ↔
      KnownAE S.μ 𝓖 t v := by
  have hi : Integrable v S.μ := (S.integrable_E t _).congr hv.symm
  rw [← known_iff_E_eq S 𝓖 hi]
  have hH := condDown_valuation h hρ hsm hs hv
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-- Cochrane (2023), eq. (3.18), p. 63, ex post on a probability space: if
`x_t = ρx_{t+1} + f_{t+1}` holds state by state, `|ρ| < 1` and `x`, `f` are (essentially) bounded,
then a.e. `x_t = ∑_{j≥0} ρʲ f_{t+1+j}` (a genuine `HasSum`). -/
theorem pv_ex_post {μ : Measure Ω} {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂μ, |x t ω| ≤ M)
    (hf : ∀ t, ∀ᵐ ω ∂μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ρ ^ j * f (t + 1 + j) ω) (x t ω) := by
  filter_upwards [ae_all_iff.2 hx, ae_all_iff.2 hf] with ω hMω hKω
  have hs : Summable fun j => ‖ρ ^ j * f (t + 1 + j) ω‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hKω _) (pow_nonneg (abs_nonneg _) _)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs]
  have hfin : (fun T => ∑ j ∈ Finset.range T, ρ ^ j * f (t + 1 + j) ω) =
      fun T => x t ω - ρ ^ T * x (t + T) ω := by
    funext T
    have := congrFun (rec_finite hrec t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  rw [hfin]
  simpa using tendsto_const_nhds.sub (tvc_of_bound hρ (fun T => hMω (t + T)))

/-- Cochrane (2023), eq. (3.19), p. 64, under ANY information: with the recursion holding ex post
and bounded measurable `x`, `f`, `|ρ| < 1`, for every date `m`, a.e.
`∑_{j≥0} ρʲ E_m f_{t+1+j} = E_m x_t`. -/
theorem pv_E (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (f t) T.μ) (hf : ∀ t, ∀ᵐ ω ∂T.μ, |f t ω| ≤ K)
    (t m : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.E m (f (t + 1 + j)) ω) (T.E m (x t) ω) := by
  have hc : Summable fun j => |ρ| ^ j * K :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K
  have hb : ∀ j, ∀ᵐ ω ∂T.μ, |ρ ^ j * f (t + 1 + j) ω| ≤ |ρ| ^ j * K := fun j => by
    filter_upwards [hf (t + 1 + j)] with ω hω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left hω (pow_nonneg (abs_nonneg _) _)
  have hE := T.E_hasSum (f := fun j ω => ρ ^ j * f (t + 1 + j) ω) hc
    (fun j => (hfm (t + 1 + j)).const_mul _) hb m
  have hsmul : ∀ j, T.E m (fun ω => ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ]
      fun ω => ρ ^ j * T.E m (f (t + 1 + j)) ω := fun j => T.E_smul (ρ ^ j) (f (t + 1 + j)) m
  have hX : (fun ω => ∑' j, ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ] x t := by
    filter_upwards [pv_ex_post hρ hrec hx hf t] with ω hω
    exact hω.tsum_eq
  filter_upwards [hE, ae_all_iff.2 hsmul, T.E_congr hX m] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eq. (3.19), p. 64: under the agents' information (`v_t` known at `t`) the
discounted forecasts of `s̃ + g − r` sum to `v_t` itself. -/
theorem pv_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {v f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ v f) (hvm : StronglyAdapted S.𝓕 v) {M K : ℝ}
    (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M) (hfm : ∀ t, AEStronglyMeasurable (f t) S.μ)
    (hf : ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (f (t + 1 + j)) ω) (v t ω) := by
  have hE : S.E t (v t) = v t :=
    S.E_of_stronglyMeasurable (hvm t) (MeasExpectationSystem.BddRV.integrable (S := S)
      ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩)
  filter_upwards [pv_E S hρ hrec hv hfm hf t t] with ω hω
  rwa [hE] at hω

/-- Cochrane (2023), p. 101, and Online Appendix p. 602, with the flow identity (3.17) holding ex
post (the measure-theoretic `Links.condDown_flow`): for any coarser information the discounted
forecasts of `s̃ + g − r` sum to `E(v_t|I_t)`, hence to `v_t` iff `v_t ∈ I_t`. -/
theorem condDown_flow_iff {S : MeasExpectationSystem Ω} (𝓖 : Filtration ℕ mΩ) {ρ : ℝ}
    (hρ : |ρ| < 1) {v r g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) {M K : ℝ}
    (hvm : ∀ t, AEStronglyMeasurable (v t) S.μ) (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (s t + g t - r t) S.μ)
    (hf : ∀ t, ∀ᵐ ω ∂S.μ, |(s t + g t - r t) ω| ≤ K) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω)) ∧
    ((∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) (v t ω)) ↔ KnownAE S.μ 𝓖 t (v t)) := by
  have hrec := (flow_iff_recursion ρ v r g s).1 hflow
  have hH := pv_E (coarsen S 𝓖) hρ hrec hv hfm hf t t
  have hi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S) ⟨hvm t, M, hv t⟩
  refine ⟨hH, ?_⟩
  rw [← known_iff_E_eq S 𝓖 hi]
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-! ### Unexpected inflation under any information set -/

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): the news about an essentially bounded variable is
bounded by twice the bound. -/
theorem abs_innov_le (T : MeasExpectationSystem Ω) {x : Ω → ℝ} {K : ℝ}
    (hx : ∀ᵐ ω ∂T.μ, |x ω| ≤ K) (t : ℕ) : ∀ᵐ ω ∂T.μ, |T.innov t x ω| ≤ 2 * K := by
  filter_upwards [T.abs_E_le hx (t + 1), T.abs_E_le hx t] with ω h1 h2
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  calc |T.E (t + 1) x ω - T.E t x ω| ≤ |T.E (t + 1) x ω| + |T.E t x ω| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (tool): discounted news about a bounded process is
summable a.e. -/
theorem summable_innov (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ}
    {K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ K) (t k : ℕ) :
    ∀ᵐ ω ∂T.μ, Summable fun j => ρ ^ j * T.innov t (x (k + j)) ω := by
  filter_upwards [ae_all_iff.2 fun j => abs_innov_le T (hx (k + j)) t] with ω hω
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (2 * K)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hω j) (pow_nonneg (abs_nonneg _) _)

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information: with the recursion
`x_t = ρx_{t+1} + f_{t+1}` ex post (bounded measurable `x`, `f`, `|ρ| < 1`), a.e.
`∑_{j≥0} ρʲ Δ_{t+1} f_{t+1+j} = Δ_{t+1} x_t`, where `Δ_{t+1} = E_{t+1} − E_t` is the news of the
information set at hand. -/
theorem innov_pv (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (f t) T.μ) (hf : ∀ t, ∀ᵐ ω ∂T.μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.innov t (f (t + 1 + j)) ω) (T.innov t (x t) ω) := by
  filter_upwards [pv_E T hρ hrec hx hfm hf t (t + 1), pv_E T hρ hrec hx hfm hf t t] with ω h1 h2
  refine (h1.sub h2).congr_fun fun j => ?_
  simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information set on a general probability space:
if the flow identity (3.17) `ρv_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` holds ex post with
`r = rⁿ − π` (bounded measurable `v`, `s̃`, `g`, `r`, integrable `rⁿ`, `|ρ| < 1`), then a.e.
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j} + Δ_{t+1}v_t`.
The last term — news about the date-`t` value of debt — vanishes for the agents (`v_t` known at
`t`) but not in general for a coarser information set. -/
theorem unexpected_inflation_any (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    {M Ks Kg Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂T.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) T.μ) (hs : ∀ t, ∀ᵐ ω ∂T.μ, |s t ω| ≤ Ks)
    (hgm : ∀ t, AEStronglyMeasurable (g t) T.μ) (hg : ∀ t, ∀ᵐ ω ∂T.μ, |g t ω| ≤ Kg)
    (hrm : ∀ t, AEStronglyMeasurable (r t) T.μ) (hrb : ∀ t, ∀ᵐ ω ∂T.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) T.μ) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, T.innov t (infl (t + 1)) ω - T.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * T.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * T.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω + T.innov t (v t) ω := by
  have hint : ∀ {x : ℕ → Ω → ℝ} {K : ℝ}, (∀ t, AEStronglyMeasurable (x t) T.μ) →
      (∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ K) → ∀ t, Integrable (x t) T.μ :=
    fun hm hb t => MeasExpectationSystem.BddRV.integrable (S := T) ⟨hm t, _, hb t⟩
  have hsi := hint hsm hs
  have hgi := hint hgm hg
  have hri := hint hrm hrb
  have hfm : ∀ t, AEStronglyMeasurable (s t + g t - r t) T.μ :=
    fun t => ((hsm t).add (hgm t)).sub (hrm t)
  have hfb : ∀ t, ∀ᵐ ω ∂T.μ, |(s t + g t - r t) ω| ≤ Ks + Kg + Kr := fun t => by
    filter_upwards [hs t, hg t, hrb t] with ω h1 h2 h3
    simp only [Pi.add_apply, Pi.sub_apply]
    calc |s t ω + g t ω - r t ω| ≤ |s t ω + g t ω| + |r t ω| := abs_sub _ _
      _ ≤ |s t ω| + |g t ω| + |r t ω| := by linarith [abs_add_le (s t ω) (g t ω)]
      _ ≤ Ks + Kg + Kr := by linarith
  have hH := innov_pv T hρ ((flow_iff_recursion ρ v r g s).1 hflow) hv hfm hfb t
  -- the news is linear (a.e.)
  have hlin : ∀ j, ∀ᵐ ω ∂T.μ, T.innov t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω =
      T.innov t (s (t + 1 + j)) ω + T.innov t (g (t + 1 + j)) ω -
        T.innov t (r (t + 1 + j)) ω := fun j => by
    have hsg := (hsi (t + 1 + j)).add (hgi (t + 1 + j))
    filter_upwards [T.E_sub hsg (hri (t + 1 + j)) (t + 1), T.E_sub hsg (hri (t + 1 + j)) t,
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) (t + 1),
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) t] with ω h1 h2 h3 h4
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply] at *
    rw [h1, h2, h3, h4]
    ring
  have hinfl : ∀ᵐ ω ∂T.μ, T.innov t (r (t + 1)) ω =
      T.innov t (rn (t + 1)) ω - T.innov t (infl (t + 1)) ω := by
    have hii : Integrable (infl (t + 1)) T.μ := by
      have : infl (t + 1) = rn (t + 1) - r (t + 1) := by rw [hr (t + 1)]; abel
      rw [this]
      exact (hrn (t + 1)).sub (hri (t + 1))
    filter_upwards [T.E_sub (hrn (t + 1)) hii (t + 1), T.E_sub (hrn (t + 1)) hii t] with ω h1 h2
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
    rw [hr (t + 1), h1, h2, Pi.sub_apply, Pi.sub_apply]
    ring
  filter_upwards [hH, ae_all_iff.2 hlin, hinfl, summable_innov T hρ hs t (t + 1),
    summable_innov T hρ hg t (t + 1), summable_innov T hρ hrb t (t + 1)] with ω h1 h2 h3 h4 h5 h6
  have hsum : HasSum (fun j => ρ ^ j * T.innov t (s (t + 1 + j)) ω +
      ρ ^ j * T.innov t (g (t + 1 + j)) ω - ρ ^ j * T.innov t (r (t + 1 + j)) ω)
      (T.innov t (v t) ω) := h1.congr_fun fun j => by rw [h2 j]; ring
  have hsplit := (h4.hasSum.add h5.hasSum).sub h6.hasSum
  have heq := hsum.unique hsplit
  have hr0 := h6.tsum_eq_zero_add
  simp only [pow_zero, one_mul, add_zero] at hr0
  have hr1 : ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 1 + (j + 1))) ω =
      ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω :=
    tsum_congr fun j => by rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  rw [hr1, h3] at hr0
  linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (the book's form, for the agents): when `v_t` is known at
`t` the extra term vanishes, `Δπ − Δrⁿ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr`. -/
theorem unexpected_inflation_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hvm : StronglyAdapted S.𝓕 v)
    {M Ks Kg Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hgm : ∀ t, AEStronglyMeasurable (g t) S.μ) (hg : ∀ t, ∀ᵐ ω ∂S.μ, |g t ω| ≤ Kg)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * S.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * S.innov t (r (t + 2 + j)) ω := by
  have hvi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
    ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩
  have h0 : S.innov t (v t) = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov,
      S.E_of_stronglyMeasurable ((hvm t).mono (S.𝓕.mono (Nat.le_succ t))) hvi,
      S.E_of_stronglyMeasurable (hvm t) hvi, sub_self]
  filter_upwards [unexpected_inflation_any S hρ hflow hr hv hsm hs hgm hg hrm hrb hrn t]
    with ω hω
  rw [hω, h0, Pi.zero_apply, add_zero]

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): if the value of debt is in the econometrician's
information, its news vanishes for the econometrician, `Δ^I_{t+1} v_t = 0` a.e. -/
theorem innov_coarsen_of_known (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) {t : ℕ}
    {v : Ω → ℝ} (hi : Integrable v S.μ) (hk : KnownAE S.μ 𝓖 t v) :
    (coarsen S 𝓖).innov t v =ᵐ[S.μ] 0 := by
  obtain ⟨w, hw, hvw⟩ := hk
  have hwi : Integrable w S.μ := hi.congr hvw
  have h1 : (coarsen S 𝓖).E (t + 1) w = w :=
    (coarsen S 𝓖).E_of_stronglyMeasurable (hw.mono (𝓖.mono (Nat.le_succ t))) hwi
  have h2 : (coarsen S 𝓖).E t w = w := (coarsen S 𝓖).E_of_stronglyMeasurable hw hwi
  filter_upwards [(coarsen S 𝓖).E_congr hvw (t + 1), (coarsen S 𝓖).E_congr hvw t] with ω a b
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, a, b, h1, h2, sub_self,
    Pi.zero_apply]

/-- Cochrane (2023), §4.2, p. 87 (constant expected returns) conditioned down: if the agents expect
a constant real return, `E(r_{t+1}|Ω_t) = c`, so does the econometrician at every earlier date,
`E(r_{t+1}|I_m) = c` for `m ≤ t`. -/
theorem constExp_condDown {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c) {m t : ℕ}
    (hmt : m ≤ t) : (coarsen S 𝓖).E m (r (t + 1)) =ᵐ[S.μ] fun _ => c := by
  filter_upwards [(E_coarsen_tower h hmt (r (t + 1))).symm, (coarsen S 𝓖).E_congr (hc t) m]
    with ω a b
  rw [a, b, (coarsen S 𝓖).E_const]

/-- Cochrane (2023), §4.2, p. 87: under constant expected returns the news about future returns
vanishes for the econometrician (and for the agents, `𝓖 = 𝓕`), `Δ^I_{t+1} r_{t+2+j} = 0`. -/
theorem innov_return_condDown {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {r : ℕ → Ω → ℝ} {c : ℝ}
    (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c) (t j : ℕ) :
    (coarsen S 𝓖).innov t (r (t + 2 + j)) =ᵐ[S.μ] 0 := by
  have e : t + 2 + j = (t + 1 + j) + 1 := by omega
  rw [e]
  filter_upwards [constExp_condDown h hc (show t + 1 ≤ t + 1 + j by omega),
    constExp_condDown h hc (show t ≤ t + 1 + j by omega)] with ω a b
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, a, b, sub_self,
    Pi.zero_apply]

/-- Cochrane (2023), eq. (4.2), p. 87, and (3.24), p. 66 (the simple model: no growth, constant
expected return), under ANY information nested in the agents': a.e.
`Δ^Iπ_{t+1} − Δ^Irⁿ_{t+1} = −∑ρʲΔ^I s̃_{t+1+j} + Δ^I_{t+1} v_t`. -/
theorem simple_model_any {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {ρ : ℝ} (hρ : |ρ| < 1) {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω +
        (coarsen S 𝓖).innov t (v t) ω := by
  have hg0 : (coarsen S 𝓖).innov t 0 = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov, (coarsen S 𝓖).E_zero,
      (coarsen S 𝓖).E_zero, sub_self]
  filter_upwards [unexpected_inflation_any (coarsen S 𝓖) hρ hflow hr (Kg := 0) hv hsm hs
    (fun _ => aestronglyMeasurable_const) (fun _ => Eventually.of_forall fun _ => by simp)
    hrm hrb hrn t, ae_all_iff.2 (innov_return_condDown h hc t)] with ω h1 h2
  rw [h1]
  have e1 : ∑' j, ρ ^ j * (coarsen S 𝓖).innov t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω = 0 := by
    simp [hg0]
  have e2 : ∑' j, ρ ^ (j + 1) * (coarsen S 𝓖).innov t (r (t + 2 + j)) ω = 0 := by
    simp only [h2, Pi.zero_apply, mul_zero, tsum_zero]
  rw [e1, e2]
  ring

/-- Cochrane (2023), eq. (4.2), p. 87 (`Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}`), for the agents: in the
simple model with one-period debt (`rⁿ_{t+1}` known at `t`) and `v_t` known at `t`, a.e. the
discounted surplus news sums to minus unexpected inflation. -/
theorem simple_model_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    (hvm : StronglyAdapted S.𝓕 v) (hrnm : ∀ t, StronglyMeasurable[S.𝓕 t] (rn (t + 1)))
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω)
      (-S.innov t (infl (t + 1)) ω) := by
  have hN : Nested S S.𝓕 := fun _ => le_rfl
  have hvi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
    ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩
  have hk : S.innov t (v t) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 hvi ⟨v t, hvm t, ae_eq_refl _⟩
  have hkr : S.innov t (rn (t + 1)) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 (hrn (t + 1)) ⟨rn (t + 1), hrnm t, ae_eq_refl _⟩
  filter_upwards [simple_model_any hN hρ hflow hr hc hv hsm hs hrm hrb hrn t, hk, hkr,
    summable_innov S hρ hs t (t + 1)] with ω h1 h2 h3 h4
  change S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
    -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω + S.innov t (v t) ω at h1
  rw [h2, h3, Pi.zero_apply] at h1
  have : -S.innov t (infl (t + 1)) ω = ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω := by linarith
  rw [this]
  exact h4.hasSum

/-- Cochrane (2023), eq. (4.2), p. 87, p. 101 and Online Appendix p. 602, for the econometrician:
in the simple model, the book's decomposition with the econometrician's news,
`Δ^I π_{t+1} − Δ^I rⁿ_{t+1} = −∑ρʲΔ^I s̃_{t+1+j}`, holds a.e. **iff** `Δ^I_{t+1} v_t = 0` a.e.;
in particular it holds when `v_t ∈ I_t` (`innov_coarsen_of_known`). -/
theorem simple_model_econ_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {v r rn infl s : ℕ → Ω → ℝ}
    (hflow : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t) {c : ℝ}
    (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω)
      (-((coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω))) ↔
      (coarsen S 𝓖).innov t (v t) =ᵐ[S.μ] 0 := by
  have hid := simple_model_any h hρ hflow hr hc hv hsm hs hrm hrb hrn t
  have hsum := summable_innov (coarsen S 𝓖) hρ hs t (t + 1)
  constructor
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [a.tsum_eq] at b
    rw [Pi.zero_apply]
    linarith
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [Pi.zero_apply] at a
    rw [b, a]
    simpa using c.hasSum

/-! ### Correction: the econometrician's decomposition fails when `v_t ∉ I_t` -/

/-- Cochrane (2023), p. 102 and Online Appendix p. 602 ("people have more information than we
do"): the econometrician sees the agents' information with a one-period lag, `𝓖_t = 𝓕_{t−1}`
(`𝓖_0 = 𝓕_0`). -/
def lagFiltration (S : MeasExpectationSystem Ω) : Filtration ℕ mΩ where
  seq t := S.𝓕 (t - 1)
  mono' _ _ h := S.𝓕.mono (Nat.sub_le_sub_right h 1)
  le' t := S.𝓕.le (t - 1)

/-- Cochrane (2023), p. 101: the lagged information is nested in the agents'. -/
theorem nested_lag (S : MeasExpectationSystem Ω) : Nested S (lagFiltration S) :=
  fun t => S.𝓕.mono (Nat.sub_le t 1)

namespace Example

open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID

/-- Cochrane (2023), p. 88 (the MA(1) surplus): `s̃_t = ε_t + θε_{t−1}`. -/
def exS (θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => ω t + θ * ω (t - 1)

/-- Cochrane (2023), p. 102 (`v_t = θε_t` for the MA(1)): the value of debt. -/
def exV (θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => θ * ω t

/-- Cochrane (2023), eq. (4.2), p. 87: the real return `r_t = a(ρ)ε_t`, `a(ρ) = 1 + ρθ`. -/
def exR (ρ θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => (1 + ρ * θ) * ω t

/-- Cochrane (2023), eq. (4.2), p. 87: inflation `π_t = −a(ρ)ε_t` (zero nominal rate). -/
def exInfl (ρ θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => -((1 + ρ * θ) * ω t)

/-- Cochrane (2023), §4.2, p. 87: the nominal return (one-period debt, `i = 0`). -/
def exRn : ℕ → (ℕ → ℝ) → ℝ := fun _ _ => 0

/-- Cochrane (2023), eq. (3.17), p. 63: the MA(1) example satisfies the flow identity ex post. -/
theorem ex_flow (ρ θ : ℝ) : Flow ρ (exV θ) (exR ρ θ) (fun _ => 0) (exS θ) := by
  intro t
  funext ω
  simp only [exV, exR, exS, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    smul_eq_mul, Nat.add_sub_cancel]
  ring

/-- Cochrane (2023), §4.2, p. 87: `r = rⁿ − π` in the example. -/
theorem ex_fisher (ρ θ : ℝ) (t : ℕ) : exR ρ θ t = exRn t - exInfl ρ θ t := by
  funext ω
  simp only [exR, exRn, exInfl, Pi.sub_apply]
  ring

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 102, and Online Appendix p. 602 (correction): with i.i.d. shocks (law `ν`,
mean `0`, variance `σ² > 0`, bounded), the MA(1) surplus `s̃_t = ε_t + θε_{t−1}` (`θ ≠ 0`) and a
lagged econometrician, the agents' decomposition `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}` holds at every date,
but the econometrician's version with his own news fails at `t = 1`: his news about `v_1 = θε_1`
is `θε_1 ≠ 0`. So the unexpected-inflation decomposition does NOT condition down in general; the
corrected statement is `simple_model_any` / `simple_model_econ_iff`. -/
theorem econ_decomp_counterexample {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {ρ θ : ℝ} (hρ : |ρ| < 1) (hθ : θ ≠ 0) :
    Flow ρ (exV θ) (exR ρ θ) (fun _ => 0) (exS θ) ∧
    Nested (iidSystem ν) (lagFiltration (iidSystem ν)) ∧
    (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, HasSum
      (fun j => ρ ^ j * (iidSystem ν).innov t (exS θ (t + 1 + j)) ω)
      (-(iidSystem ν).innov t (exInfl ρ θ (t + 1)) ω)) ∧
    ¬ (∀ᵐ ω ∂(iidSystem ν).μ, HasSum
      (fun j => ρ ^ j * (coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1
        (exS θ (1 + 1 + j)) ω)
      (-((coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1 (exInfl ρ θ (1 + 1)) ω -
        (coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1 (exRn (1 + 1)) ω))) := by
  set S := iidSystem ν
  have hB := shock_ae_bdd ν hbdd
  have hc : ∀ t, S.E t (exR ρ θ (t + 1)) =ᵐ[S.μ] fun _ => (0 : ℝ) := fun t => by
    have e : exR ρ θ (t + 1) = (1 + ρ * θ) • shock (t + 1) := rfl
    filter_upwards [e ▸ S.E_smul (1 + ρ * θ) (shock (t + 1)) t, E_shock_zero hmean t]
      with ω a b
    rw [a, Pi.smul_apply, b, Pi.zero_apply, smul_zero]
  have hvm : StronglyAdapted S.𝓕 (exV θ) := fun t =>
    ((measurable_shock ν le_rfl).const_mul θ).stronglyMeasurable
  have hv : ∀ t, ∀ᵐ ω ∂S.μ, |exV θ t ω| ≤ |θ| * B := fun t => by
    filter_upwards [hB t] with ω h
    simp only [exV, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg θ)
  have hsm : ∀ t, AEStronglyMeasurable (exS θ t) S.μ := fun t =>
    Measurable.aestronglyMeasurable (by unfold exS; fun_prop)
  have hs : ∀ t, ∀ᵐ ω ∂S.μ, |exS θ t ω| ≤ B + |θ| * B := fun t => by
    filter_upwards [hB t, hB (t - 1)] with ω h1 h2
    simp only [exS]
    calc |ω t + θ * ω (t - 1)| ≤ |ω t| + |θ * ω (t - 1)| := abs_add_le _ _
      _ ≤ B + |θ| * B := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg θ))
  have hrm : ∀ t, AEStronglyMeasurable (exR ρ θ t) S.μ := fun t =>
    ((measurable_pi_apply t).const_mul _).aestronglyMeasurable
  have hrb : ∀ t, ∀ᵐ ω ∂S.μ, |exR ρ θ t ω| ≤ |1 + ρ * θ| * B := fun t => by
    filter_upwards [hB t] with ω h
    simp only [exR, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hrn : ∀ t, Integrable (exRn t) S.μ := fun _ => integrable_const 0
  refine ⟨ex_flow ρ θ, nested_lag S, fun t => ?_, ?_⟩
  · exact simple_model_agents S hρ (ex_flow ρ θ) (ex_fisher ρ θ) hc hvm
      (fun _ => stronglyMeasurable_const) hv hsm hs hrm hrb hrn t
  · rw [simple_model_econ_iff (nested_lag S) hρ (ex_flow ρ θ) (ex_fisher ρ θ) hc hv hsm hs
      hrm hrb hrn 1]
    intro h0
    have hvi : Integrable (exV θ 1) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
      ⟨(hvm 1).mono (S.𝓕.le 1) |>.aestronglyMeasurable, _, hv 1⟩
    have h2 : (coarsen S (lagFiltration S)).E (1 + 1) (exV θ 1) = exV θ 1 :=
      S.E_of_stronglyMeasurable (hvm 1) hvi
    have h1 : (coarsen S (lagFiltration S)).E 1 (exV θ 1) =ᵐ[S.μ] 0 := by
      have e : exV θ 1 = θ • shock (0 + 1) := rfl
      change S.E 0 (exV θ 1) =ᵐ[S.μ] 0
      filter_upwards [e ▸ S.E_smul θ (shock (0 + 1)) 0, E_shock_zero hmean 0] with ω a b
      rw [a, Pi.smul_apply, b, Pi.zero_apply, smul_zero]
    have hz : ∀ᵐ ω ∂S.μ, ω 1 ^ 2 = 0 := by
      filter_upwards [h0, h1] with ω a b
      rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, h2, b] at a
      simp only [exV, Pi.zero_apply, sub_zero, mul_eq_zero] at a
      rcases a with a | a
      · exact absurd a hθ
      · rw [a]; ring
    have hint := integral_shock_fun ν 1 (f := fun x => x ^ 2) (measurable_id.pow_const 2)
    rw [integral_congr_ae hz, integral_zero, hvar] at hint
    linarith

end Example

/-! ### Links: the finite Mathlib instance and the abstract nested systems -/

/-- Cochrane (2023), p. 101: on a finite state space with full support, the econometrician's
system (bridged to the core) is exactly `ConditioningDown.CondExp.condExpSystem` for `𝓖`. -/
theorem coarsen_toExpectationSystem_E [Finite Ω] [DiscreteMeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ)
    (x : Ω → ℝ) :
    ((coarsen S 𝓖).toExpectationSystem hfull).E t x =
      (ConditioningDown.CondExp.condExpSystem S.μ hfull 𝓖 𝓖.le (fun _ _ h => 𝓖.mono h)).E t x :=
  rfl

/-- Cochrane (2023), p. 101: on a finite state space with full support, a nested pair of
measure-theoretic systems is a coarser pair of core systems in the abstract sense of
`ConditioningDown.Coarser`. -/
theorem coarser_core [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}
    {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖) (hfull : ∀ ω, S.μ {ω} ≠ 0) :
    ConditioningDown.Coarser ((coarsen S 𝓖).toExpectationSystem hfull)
      (S.toExpectationSystem hfull) :=
  fun _ x => S.eq_of_ae_eq hfull (E_coarsen_tower h le_rfl x)

/-- Cochrane (2023), p. 101, and Online Appendix (2.22)–(2.23), p. 602: on a finite state space
with full support, the general measure-theoretic `condDown_iff` and the abstract
`ConditioningDown.condDown_iff` for nested systems are the same statement: each side of the
general one is the corresponding side of the abstract one. -/
theorem condDown_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}
    {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖) (hfull : ∀ ω, S.μ {ω} ≠ 0) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = S.E t X) :
    (v =ᵐ[S.μ] (coarsen S 𝓖).E t X ↔ v = ((coarsen S 𝓖).toExpectationSystem hfull).E t X) ∧
    (KnownAE S.μ 𝓖 t v ↔ ((coarsen S 𝓖).toExpectationSystem hfull).E t v = v) ∧
    (v = ((coarsen S 𝓖).toExpectationSystem hfull).E t X ↔
      ((coarsen S 𝓖).toExpectationSystem hfull).E t v = v) := by
  refine ⟨⟨fun h1 => S.eq_of_ae_eq hfull h1, fun h1 => h1 ▸ ae_eq_refl _⟩, ?_,
    ConditioningDown.condDown_iff (coarser_core h hfull) hv⟩
  rw [← known_iff_E_eq S 𝓖 Integrable.of_finite]
  exact ⟨fun h1 => (S.eq_of_ae_eq hfull h1).symm,
    fun h1 => Eventually.of_forall fun ω => (congrFun h1 ω).symm⟩

/-- Cochrane (2023), Ch. 2, p. 29 (tool): when every state has positive probability, an a.e.
statement holds at every state. -/
theorem forall_of_ae [Finite Ω] {S : MeasExpectationSystem Ω} (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {p : Ω → Prop} (h : ∀ᵐ ω ∂S.μ, p ω) (ω : Ω) : p ω := by
  by_contra hω
  exact hfull ω (measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hω)
    (ae_iff.mp h))

/-- Cochrane (2023), eq. (3.20), p. 65: on a finite state space with full support, the core
innovation operator of the bridged system is the measure-theoretic news `E_{t+1} − E_t`. -/
theorem core_innov_eq [Finite Ω] [DiscreteMeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ) (x : Ω → ℝ) :
    Innovations.innov (S.toExpectationSystem hfull) t x = S.innov t x := rfl

/-- Cochrane (2023), eq. (3.20), p. 65, link to the core: on a finite state space with full
support, `unexpected_inflation_agents` specialises to the core statement
(`LinearizedIdentities.unexpected_inflation_identity_tsum`'s conclusion) for the bridged
`ExpectationSystem`, at every state. -/
theorem unexpected_inflation_core [Finite Ω] [DiscreteMeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (hfull : ∀ ω, S.μ {ω} ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hvm : StronglyAdapted S.𝓕 v) {M Ks Kg Kr : ℝ} (hv : ∀ t ω, |v t ω| ≤ M)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hg : ∀ t ω, |g t ω| ≤ Kg) (hrb : ∀ t ω, |r t ω| ≤ Kr) (t : ℕ)
    (ω : Ω) :
    Innovations.innov (S.toExpectationSystem hfull) t (infl (t + 1)) ω -
      Innovations.innov (S.toExpectationSystem hfull) t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * Innovations.innov (S.toExpectationSystem hfull) t (s (t + 1 + j)) ω -
        ∑' j, ρ ^ j * Innovations.innov (S.toExpectationSystem hfull) t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * Innovations.innov (S.toExpectationSystem hfull) t
          (r (t + 2 + j)) ω := by
  have hm : ∀ x : Ω → ℝ, AEStronglyMeasurable x S.μ := fun x =>
    (Measurable.of_discrete (f := x)).aestronglyMeasurable
  have hA := unexpected_inflation_any S hρ hflow hr (M := M)
    (fun t => Eventually.of_forall (hv t)) (fun t => hm _) (fun t => Eventually.of_forall (hs t))
    (fun t => hm _) (fun t => Eventually.of_forall (hg t)) (fun t => hm _)
    (fun t => Eventually.of_forall (hrb t)) (fun _ => Integrable.of_finite) t
  have hvi : Integrable (v t) S.μ := Integrable.of_finite
  have h0 : S.innov t (v t) = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov,
      S.E_of_stronglyMeasurable ((hvm t).mono (S.𝓕.mono (Nat.le_succ t))) hvi,
      S.E_of_stronglyMeasurable (hvm t) hvi, sub_self]
  have hB := forall_of_ae hfull hA ω
  rw [h0, Pi.zero_apply, add_zero] at hB
  exact hB

end Cochrane.DebtDeficitsInflation.ConditioningDownMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Invertibility, Wold and Granger causality in the Hilbert space of second moments

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, eqs. (2.4)–(2.5) and (2.17)–(2.21), pp. 597–601.

This module extends the Hilbert-space layer of `Invertibility` (white noise `e` in a real Hilbert
space `H`, moving averages `maProc a e`, closed past spans `pastSpan`). It is stated for an
arbitrary `H`; `InvertibilityMeasureL2` instantiates it on `L²(Ω, P)` of a genuine i.i.d.
probability space.

## Main definitions

* `eSpan e`: the closed span of all the shocks; `cconv b c`: the Cauchy product of coefficient
  sequences (the coefficients of `b(L)c(L)`).
* `factorCoeff θ g`: the coefficients of `(1 − θL)g(L)` (the book's factorisation (2.17));
  `jointSpan s v t`: the closed span of current and past `s` AND `v` (the debt–surplus VAR's
  information); the one-step-ahead forecast error `u_t = s_t − P(s_t|s_{t−1}, …)`
  (in `wold_factor`).

## Main results

* Tools: `inner_e_maProc_int`, `eq_of_inner_e`, `hasSum_filter_maProc`
  (`b(L)[c(L)e_t] = (b·c)(L)e_t` in `H`), `gen_factorCoeff` (`a(z) = (1 − θz)g(z)`).
* Non-invertibility at `|ρ| ≤ 1`, including `ρ = 1` (p. 102, A2 p. 600):
  `not_filter_of_aRho_eq_zero`
  — no absolutely summable filter of current and past surpluses converges in `H` to the shock.
* Correction at `|ρ| = 1`: `mem_pastSpan_unit_root` — for `s_t = e_t − ρe_{t−1}`, `ρ = ±1`
  (`a(ρ) = 0`), the shock IS in the closed span of current and past surpluses (Cesàro means of
  the filter partial sums converge to it, error variance `σ²/(n+1)`); so the closed-span
  statement `Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero` genuinely needs `|ρ| < 1`.
* Wold (A2 pp. 597, 600, the factorised claim (2.17)): `wold_factor` — for
  `a(L) = (1 − θL)g(L)`, `|θ| > 1`, `g₀ = 1` and `g` invertible (absolutely summable inverse),
  the autoregression's innovation is `w_t = ∑θ⁻ᵏm_{t−k}` (`m_t = e_t − θe_{t−1}`), with
  variance `θ²σ²`, `s_t = ∑ã_n w_{t−n}` for `ã(L) = (1 − θ⁻¹L)g(L)` (root flipped), fitted
  `ã(θ⁻¹) = (1 − θ⁻²)g(θ⁻¹) ≠ 0` while `a(θ⁻¹) = 0`, and `w_t ≠ e_t`.
* Debt (2.18)–(2.20): `summable_abs_hsCoeff` (for `|ρ| < 1` debt is a moving average),
  `debt_hasSum_expost` (with `a(ρ) = 0` debt is the ex-post present value, in `H`),
  `hsCoeff_factor` (`c = −θg`, "the non-invertible root cancels"), `shock_mem_debtSpan` (with `g`
  invertible the shock is recovered from the debt history), `debt_not_invertible_example`
  (correction: when another root of `a(L)` is inside the disc the debt is NOT invertible).
* Links: `factorCoeff_delta`, `recoverable_delta`, `wold_factor_ma1` (`g = 1` gives the MA(1)
  statements `Invertibility.Hilbert.ma1_wold`, `Invertibility.ma1_fitted_aRho`, and `v = −θe`).
* Granger causality ((2.21), p. 601): `exists_shift` (white noise has a unitary time shift),
  `granger_general` — for an ARBITRARY absolutely summable MA with `a₀ ≠ 0`, `a(ρ) = 0`,
  `|ρ| < 1`, the projection of `s_{t+1}` on the joint surplus–debt past differs from that on the
  surplus past, and the forecast-error norm is strictly smaller with debt; `granger_factor` —
  in the factorised case the two error variances are exactly `σ²` and `θ²σ² = σ²/ρ²`.
-/

namespace Cochrane.DebtDeficitsInflation.InvertibilityMeasure

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Tools: the closed span of the shocks and filters of moving averages -/

/-- Cochrane (2023), p. 102 (tool): the closed linear span of all the structural shocks. -/
noncomputable def eSpan (e : ℤ → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range e)).topologicalClosure

/-- Cochrane (2023), p. 102 (tool): a shock from the future is uncorrelated with the moving
average, `⟪e_{t+1+n}, s_t⟫ = 0`. -/
theorem inner_e_maProc_future [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (n : ℕ) :
    ⟪e (t + 1 + n), maProc a e t⟫ = 0 := by
  have h := inner_hasSum_right (maProc_hasSum he ha t) (e (t + 1 + n))
  refine h.unique ?_
  convert hasSum_zero with k
  rw [real_inner_smul_right, he]
  have : t + 1 + (n : ℤ) ≠ t - k := by omega
  simp [this]

/-- Cochrane (2023), p. 102 (tool): the covariance of any shock with the moving average,
`⟪e_u, s_t⟫ = σ² a_{t−u}` for `u ≤ t` and `0` for `u > t`. -/
theorem inner_e_maProc_int [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t u : ℤ) :
    ⟪e u, maProc a e t⟫ = if u ≤ t then σ2 * a (t - u).toNat else 0 := by
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    have e1 : u = t - ((t - u).toNat : ℕ) := by omega
    conv_lhs => rw [e1]
    exact inner_e_maProc he ha t _
  · simp only [hu, ↓reduceIte]
    have e1 : u = t + 1 + ((u - t - 1).toNat : ℕ) := by omega
    rw [e1]
    exact inner_e_maProc_future he ha t _

/-- Cochrane (2023), p. 102 (tool): a convergent series of members of the shock span lies in it. -/
theorem hasSum_mem_eSpan {e : ℤ → H} {f : ℕ → H} {x : H} (h : HasSum f x)
    (hf : ∀ k, f k ∈ eSpan e) : x ∈ eSpan e :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
    (Filter.Eventually.of_forall fun _ => Submodule.sum_mem _ fun k _ => hf k)

/-- Cochrane (2023), p. 102 (tool): each shock lies in the shock span. -/
theorem e_mem_eSpan (e : ℤ → H) (u : ℤ) : e u ∈ eSpan e :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨u, rfl⟩)

/-- Cochrane (2023), p. 102 (tool): a moving average lies in the shock span. -/
theorem maProc_mem_eSpan [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) : maProc a e t ∈ eSpan e :=
  hasSum_mem_eSpan (maProc_hasSum he ha t) fun _ => Submodule.smul_mem _ _ (e_mem_eSpan e _)

/-- Cochrane (2023), p. 102 (tool): two members of the shock span with the same covariances with
every shock are equal. -/
theorem eq_of_inner_e {e : ℤ → H} {x y : H} (hx : x ∈ eSpan e) (hy : y ∈ eSpan e)
    (h : ∀ u, ⟪e u, x⟫ = ⟪e u, y⟫) : x = y := by
  have hd : x - y ∈ eSpan e := Submodule.sub_mem _ hx hy
  have hle : eSpan e ≤ (ℝ ∙ (x - y))ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left,
      real_inner_comm, h u, real_inner_comm, sub_self]
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hd)
  rwa [inner_self_eq_zero, sub_eq_zero] at h0

/-- Cochrane (2023), p. 87 (tool): `‖s_t‖ ≤ (∑|a_k|)‖e_0‖`. -/
theorem norm_maProc_le [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    ‖maProc a e t‖ ≤ (∑' k, |a k|) * ‖e 0‖ := by
  have hs : Summable fun k : ℕ => ‖a k • e (t - k)‖ :=
    (ha.mul_right ‖e 0‖).congr fun k => by rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]
  calc ‖maProc a e t‖ ≤ ∑' k : ℕ, ‖a k • e (t - k)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k, |a k| * ‖e 0‖ := tsum_congr fun k => by
        rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]
    _ = (∑' k, |a k|) * ‖e 0‖ := tsum_mul_right

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the coefficients of the product
`b(L)c(L)`, `(b·c)_n = ∑_{k ≤ n} b_k c_{n−k}`. -/
noncomputable def cconv (b c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), b k * c (n - k)

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the product of absolutely summable
lag polynomials is absolutely summable. -/
theorem summable_cconv {b c : ℕ → ℝ} (hb : Summable (fun k => |b k|))
    (hc : Summable (fun k => |c k|)) : Summable (fun n => |cconv b c n|) := by
  have := summable_norm_sum_mul_range_of_summable_norm (f := b) (g := c)
    (by simpa [Real.norm_eq_abs] using hb) (by simpa [Real.norm_eq_abs] using hc)
  simpa [Real.norm_eq_abs, cconv] using this

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the product of lag polynomials is
the product of power series. -/
theorem mk_cconv (b c : ℕ → ℝ) :
    PowerSeries.mk (cconv b c) = PowerSeries.mk b * PowerSeries.mk c := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, cconv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/-- Cochrane (2023), Online Appendix pp. 597–601 (tool): **filters of moving averages** — for
absolutely summable `b`, `c`, `∑_k b_k s_{t−k} = (b·c)(L)e_t` in `H`, where `s = c(L)e`. -/
theorem hasSum_filter_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {b c : ℕ → ℝ} (hb : Summable (fun k => |b k|)) (hc : Summable (fun k => |c k|)) (t : ℤ) :
    HasSum (fun k : ℕ => b k • maProc c e (t - k)) (maProc (cconv b c) e t) := by
  have hsum : Summable (fun k : ℕ => b k • maProc c e (t - k)) := by
    refine Summable.of_norm_bounded (hb.mul_right ((∑' k, |c k|) * ‖e 0‖)) fun k => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_maProc_le he hc _) (abs_nonneg _)
  have hX := hsum.hasSum
  convert hX using 1
  refine eq_of_inner_e (maProc_mem_eSpan he (summable_cconv hb hc) t)
    (hasSum_mem_eSpan hX fun k => Submodule.smul_mem _ _ (maProc_mem_eSpan he hc _))
    fun u => ?_
  have h := inner_hasSum_right hX (e u)
  refine (h.unique ?_).symm
  rw [inner_e_maProc_int he (summable_cconv hb hc)]
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u = t - n := ⟨(t - u).toNat, by omega⟩
    subst hn
    have hn' : (t - (t - (n : ℤ))).toNat = n := by omega
    rw [hn']
    have hF : ∀ k, ⟪e (t - n), b k • maProc c e (t - k)⟫ =
        if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0 := by
      intro k
      rw [real_inner_smul_right, inner_e_maProc_int he hc]
      by_cases hk : k ∈ Finset.range (n + 1)
      · have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 : t - (n : ℤ) ≤ t - k := by omega
        have h2 : (t - (k : ℤ) - (t - n)).toNat = n - k := by omega
        simp only [h1, hk, ↓reduceIte]
        rw [h2]
        ring
      · have : ¬ t - (n : ℤ) ≤ t - k := by
          rw [Finset.mem_range] at hk; omega
        simp only [this, hk, ↓reduceIte, mul_zero]
    have hS : HasSum (fun k => if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0)
        (∑ k ∈ Finset.range (n + 1),
          if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp only [hk, ↓reduceIte]
    rw [Finset.sum_ite_of_true (fun _ hk => hk), ← Finset.mul_sum] at hS
    exact hS.congr_fun hF
  · simp only [hu, ↓reduceIte]
    convert hasSum_zero with k
    rw [real_inner_smul_right, inner_e_maProc_int he hc]
    have : ¬ u ≤ t - k := by omega
    simp only [this, ↓reduceIte, mul_zero]

/-! ### Non-invertibility at `|ρ| ≤ 1`, and what fails at `|ρ| = 1` -/

/-- Cochrane (2023), p. 102 ("the shock `ε_t` is a function of current and future surpluses, not
current and past surpluses") and Online Appendix p. 600, in the Hilbert space, for every
`|ρ| ≤ 1` including the book's `ρ = 1`: if `a(ρ) = 0`, no absolutely summable filter of current and
past surpluses converges (in mean square) to the structural shock `e_t`. -/
theorem not_filter_of_aRho_eq_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℤ) :
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc a e (t - k)) (e t) := by
  rintro ⟨b, hb, hsum⟩
  refine not_recoverable_of_aRho_eq_zero ha hρ h0 ⟨b, hb, fun n => ?_⟩
  have h1 := (hasSum_filter_maProc he hb ha t).unique hsum
  have h2 : ⟪e (t - n), maProc (cconv b a) e t⟫ = ⟪e (t - n), e t⟫ := by rw [h1]
  rw [inner_e_maProc he (summable_cconv hb ha) t n, he] at h2
  change cconv b a n = _
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero, sub_zero, ↓reduceIte] at h2 ⊢
    exact mul_left_cancel₀ hσ (h2.trans (mul_one σ2).symm)
  · have hne : t - (n : ℤ) ≠ t := by omega
    simp only [hne, hn, ↓reduceIte] at h2 ⊢
    exact (mul_eq_zero.mp h2).resolve_left hσ

/-- Cochrane (2023), p. 102 (tool): the MA(1) coefficients give `s_t = e_t − θe_{t−1}`. -/
theorem maProc_armaCoeff_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (θ : ℝ) (t : ℤ) : maProc (armaCoeff 0 θ) e t = maOne θ e t := by
  have ha := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  have := ar2_filter_eq_maOne he ha (φ1 := 0) (φ2 := 0) (θ := θ) rfl (by simp [armaCoeff])
    (fun k => by simp [armaCoeff]) t
  simpa using this

/-- Cochrane (2023), p. 102 (tool): the squared norm of a finite combination of distinct shocks,
`‖∑ c_m e_{f(m)}‖² = σ² ∑ c_m²`. -/
theorem inner_sum_e {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (c : ℕ → ℝ) (f : ℕ → ℤ)
    (hf : Function.Injective f) (N : ℕ) :
    ⟪∑ m ∈ Finset.range N, c m • e (f m), ∑ m ∈ Finset.range N, c m • e (f m)⟫ =
      σ2 * ∑ m ∈ Finset.range N, c m ^ 2 := by
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  have : ∀ m' ∈ Finset.range N, ⟪c m • e (f m), c m' • e (f m')⟫ =
      if m = m' then c m * c m' * σ2 else 0 := by
    intro m' _
    rw [real_inner_smul_left, real_inner_smul_right, he]
    simp only [hf.eq_iff]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  simp only [hm, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 ("`ρ ≤ 1`"), **correction at `|ρ| = 1`**:
for the MA(1) `s_t = e_t − ρe_{t−1}` with `ρ = ±1` we have `a(ρ) = 1 − ρ² = 0`, yet the structural
shock `e_t` IS in the closed linear span of current and past surpluses: the Cesàro means of the
filter partial sums `∑_{k≤m} ρᵏs_{t−k} = e_t − ρ^{m+1}e_{t−m−1}` converge to it, with error
variance `σ²/(n+1)`. So in mean square the shock can be recovered from the surplus history at
`|ρ| = 1` (though by no absolutely summable filter, `not_filter_of_aRho_eq_zero`), and
`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero` cannot be extended to `|ρ| = 1`. -/
theorem mem_pastSpan_unit_root [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {ρ : ℝ} (hρ : ρ ^ 2 = 1) (t : ℤ) :
    gen (armaCoeff 0 ρ) ρ = 0 ∧ e t ∈ pastSpan (maProc (armaCoeff 0 ρ) e) t := by
  refine ⟨by rw [ma1_aRho]; nlinarith, ?_⟩
  set s := maProc (armaCoeff 0 ρ) e with hs
  have hsm : ∀ τ, s τ = e τ - ρ • e (τ - 1) := fun τ => maProc_armaCoeff_zero he ρ τ
  -- partial sums of the filter
  have hP : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), ρ ^ k • s (t - k) =
      e t - ρ ^ (m + 1) • e (t - 1 - m) := by
    intro m
    induction m with
    | zero => simp [hsm]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hsm, smul_sub, smul_smul, ← pow_succ,
        show t - ((m + 1 : ℕ) : ℤ) = t - 1 - m by push_cast; ring,
        show t - 1 - (m : ℤ) - 1 = t - 1 - ((m + 1 : ℕ) : ℤ) by push_cast; ring]
      abel
  set y : ℕ → H := fun n => ((n : ℝ) + 1)⁻¹ •
    ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1), ρ ^ k • s (t - k) with hy
  have hymem : ∀ n, y n ∈ pastSpan s t := fun n =>
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ => Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (mem_pastSpan_self s t k))
  have hdiff : ∀ n, e t - y n = ((n : ℝ) + 1)⁻¹ •
      ∑ m ∈ Finset.range (n + 1), ρ ^ (m + 1) • e (t - 1 - m) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [hy, hP, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one,
      inv_mul_cancel₀ hn, one_smul]
    abel
  have hnorm : ∀ n, ‖e t - y n‖ ^ 2 = σ2 / ((n : ℝ) + 1) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [hdiff, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
      inner_sum_e he (fun m => ρ ^ (m + 1)) (fun m => t - 1 - m)
        (fun m m' h => by simpa using h) (n + 1)]
    have : ∀ m ∈ Finset.range (n + 1), (ρ ^ (m + 1)) ^ 2 = 1 := fun m _ => by
      rw [← pow_mul, mul_comm, pow_mul, hρ, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  have hlim : Tendsto y atTop (𝓝 (e t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => σ2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat σ2 |>.comp (tendsto_add_atTop_nat 1) |>.congr
        fun n => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [← hnorm, norm_sub_rev, Real.sqrt_sq (norm_nonneg _)]
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall hymem)

/-! ### The general (factorised) Wold statement -/

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600: the coefficients of `(1 − θL)g(L)`,
`a₀ = g₀`, `a_{k+1} = g_{k+1} − θg_k`. -/
def factorCoeff (θ : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => g 0
  | k + 1 => g (k + 1) - θ * g k

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): `(1 − θL)g(L)` is the product of
the lag polynomials `g(L)` and `1 − θL` (as power series). -/
theorem mk_factorCoeff (θ : ℝ) (g : ℕ → ℝ) :
    PowerSeries.mk (factorCoeff θ g) = PowerSeries.mk g * PowerSeries.mk (armaCoeff 0 θ) := by
  rw [← mk_cconv]
  congr 1
  funext n
  rcases n with _ | m
  · simp [factorCoeff, cconv, armaCoeff]
  · rw [cconv, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self,
      show m + 1 - m = 0 + 1 by omega, factorCoeff]
    have h0 : ∑ k ∈ Finset.range m, g k * armaCoeff 0 θ (m + 1 - k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hk' : m + 1 - k = (m - k) + 1 := by rw [Finset.mem_range] at hk; omega
        have hk'' : m - k ≠ 0 := by rw [Finset.mem_range] at hk; omega
        rw [hk', armaCoeff, zero_pow hk'', mul_zero, mul_zero]
    rw [h0]
    simp [armaCoeff]
    ring

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): `(1 − θL)g(L)` has absolutely
summable coefficients when `g` does. -/
theorem summable_factorCoeff (θ : ℝ) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) :
    Summable (fun k => |factorCoeff θ g k|) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    (((summable_nat_add_iff 1).mpr hg).add (hg.mul_left |θ|))
  change |g (k + 1) - θ * g k| ≤ |g (k + 1)| + |θ| * |g k|
  calc |g (k + 1) - θ * g k| ≤ |g (k + 1)| + |θ * g k| := abs_sub _ _
    _ = |g (k + 1)| + |θ| * |g k| := by rw [abs_mul]

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600: `a(z) = (1 − θz)g(z)` for `|z| ≤ 1`. -/
theorem gen_factorCoeff (θ : ℝ) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) {z : ℝ}
    (hz : |z| ≤ 1) : gen (factorCoeff θ g) z = (1 - θ * z) * gen g z := by
  have hgz : Summable (fun j => g j * z ^ j) :=
    Summable.of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)
  have h1 : HasSum (fun j => g (j + 1) * z ^ (j + 1)) (gen g z - g 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hgz.hasSum
    simpa [gen] using this
  have h2 : HasSum (fun j => factorCoeff θ g (j + 1) * z ^ (j + 1))
      (gen g z - g 0 - θ * z * gen g z) := by
    refine (h1.sub (hgz.hasSum.mul_left (θ * z))).congr_fun fun j => ?_
    simp only [factorCoeff, pow_succ]
    ring
  have h3 : HasSum (fun j => factorCoeff θ g j * z ^ j)
      (factorCoeff θ g 0 + (gen g z - g 0 - θ * z * gen g z)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using h2
  rw [gen, h3.tsum_eq, factorCoeff]
  ring

/-- Cochrane (2023), p. 600 (tool): an absolutely summable inverse of `g(L)` turns into the power
series identity `h(L)g(L) = 1`. -/
theorem mk_mul_eq_one {h g : ℕ → ℝ}
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), h k * g (n - k) = if n = 0 then 1 else 0) :
    PowerSeries.mk h * PowerSeries.mk g = 1 := by
  rw [← mk_cconv]
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, cconv, hconv]

/-- Cochrane (2023), Online Appendix p. 597 (tool): `∑ θ⁻ᵏ Lᵏ (1 − θ⁻¹L) = 1`. -/
theorem mk_geom_factor (θ : ℝ) :
    PowerSeries.mk (fun k => (θ⁻¹) ^ k) * PowerSeries.mk (armaCoeff 0 θ⁻¹) = 1 := by
  rw [← mk_factorCoeff]
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | m
  · simp [factorCoeff]
  · simp only [factorCoeff, pow_succ, Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): the coefficients of a power series determine
the sequence. -/
theorem eq_of_mk_eq {b c : ℕ → ℝ} (h : PowerSeries.mk b = PowerSeries.mk c) : b = c := by
  funext n
  have := congrArg (PowerSeries.coeff n) h
  simpa using this

/-- Cochrane (2023), Online Appendix pp. 597 and 600 (`(1 − ρ⁻¹L)` "blows up going backwards"; "if
you do run an autoregression you recover a representation that is invertible, by the Wold
decomposition theorem"), **the factorised claim made precise**: let `s_t = a(L)e_t` with
`a(L) = (1 − θL)g(L)` (the book's (2.17) with `θ = ρ⁻¹`), `|θ| > 1`, `g₀ = 1`, and `g`
absolutely summable with an absolutely summable inverse (all other roots outside the unit
circle, the book's "appropriately less than one"). Then, with `m_t = e_t − θe_{t−1}` and
`w_t = ∑θ⁻ᵏm_{t−k}`:
* `s_t − w_t` is the projection of `s_t` on its own past (`w` is the autoregression's error);
* `w` is white noise with variance `θ²σ²`;
* `s_t = ∑ ã_n w_{t−n}` with `ã(L) = (1 − θ⁻¹L)g(L)`: the root `θ` is flipped to `θ⁻¹ = ρ`;
* `a(θ⁻¹) = 0` but the fitted `ã(θ⁻¹) = (1 − θ⁻²)g(θ⁻¹) ≠ 0` ("the resulting estimate of
  `a(L)` does not have `a(ρ) = 0` even in infinite data");
* the structural shock is not in the closed span of the surplus history, and `w_t ≠ e_t`. -/
theorem wold_factor [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|))
    (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    (haveI : (pastSpan (maProc (factorCoeff θ g) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (factorCoeff θ g) e) (t - 1)).starProjection
        (maProc (factorCoeff θ g) e t)) =
      maProc (factorCoeff θ g) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    (∀ u, u < t → ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) u⟫ = 0) ∧
    HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ e) (t - n))
      (maProc (factorCoeff θ g) e t) ∧
    gen (factorCoeff θ g) θ⁻¹ = 0 ∧
    gen (factorCoeff θ⁻¹ g) θ⁻¹ = (1 - θ⁻¹ ^ 2) * gen g θ⁻¹ ∧
    gen (factorCoeff θ⁻¹ g) θ⁻¹ ≠ 0 ∧
    e t ∉ pastSpan (maProc (factorCoeff θ g) e) t ∧
    woldInnov θ (maOne θ e) t ≠ e t := by
  obtain ⟨h, hh, hconv⟩ := hrec
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  set a := factorCoeff θ g with ha_def
  have ha := summable_factorCoeff θ hg
  have hd := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  set s := maProc a e with hs
  have hroot : gen a θ⁻¹ = 0 := by
    rw [gen_factorCoeff θ hg hq.le, mul_inv_cancel₀ hθ0, sub_self, zero_mul]
  have ha0 : a 0 = 1 := hg0
  have hh0 : h 0 = 1 := by
    have := hconv 0
    simpa [hg0] using this
  -- `h(L)s_t = m_t`
  have hha : cconv h a = armaCoeff 0 θ := by
    refine eq_of_mk_eq ?_
    rw [mk_cconv, ha_def, mk_factorCoeff, ← mul_assoc, mk_mul_eq_one hconv, one_mul]
  have hm : ∀ τ, maOne θ e τ - s τ ∈ pastSpan s (τ - 1) := by
    intro τ
    have hf := hasSum_filter_maProc he hh ha τ
    rw [hha, maProc_armaCoeff_zero he] at hf
    rw [← hasSum_nat_add_iff' 1] at hf
    simp only [Finset.range_one, Finset.sum_singleton, hh0, one_smul, Nat.cast_zero,
      sub_zero] at hf
    refine hasSum_mem_pastSpan hf fun k => Submodule.smul_mem _ _ ?_
    rw [show τ - ((k + 1 : ℕ) : ℤ) = τ - 1 - k by push_cast; ring]
    exact mem_pastSpan_self s (τ - 1) k
  obtain ⟨-, hsub, hproj, hnorm, hwhite, -, hnot⟩ :=
    wold_innovation he hσ hθ ha ha0 hroot hm t
  -- `w = (θ⁻ᵏ)(L)(1 − θL)e`
  have hgeo : Summable (fun k => |(θ⁻¹) ^ k|) := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg _) hq
  have hw : ∀ τ, woldInnov θ (maOne θ e) τ =
      maProc (cconv (fun k => (θ⁻¹) ^ k) (armaCoeff 0 θ)) e τ := by
    intro τ
    refine (woldInnov_hasSum he hθ τ).unique ?_
    have := hasSum_filter_maProc he hgeo hd τ
    refine this.congr_fun fun k => ?_
    rw [maProc_armaCoeff_zero he]
  -- the fitted representation
  have hfit : HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ e) (t - n))
      (s t) := by
    have hft := hasSum_filter_maProc he (summable_factorCoeff θ⁻¹ hg)
      (summable_cconv hgeo hd) t
    have hcoef : cconv (factorCoeff θ⁻¹ g) (cconv (fun k => (θ⁻¹) ^ k) (armaCoeff 0 θ)) = a := by
      refine eq_of_mk_eq ?_
      rw [mk_cconv, mk_cconv, mk_factorCoeff, ha_def, mk_factorCoeff,
        show PowerSeries.mk g * PowerSeries.mk (armaCoeff 0 θ⁻¹) *
          (PowerSeries.mk (fun k => (θ⁻¹) ^ k) * PowerSeries.mk (armaCoeff 0 θ)) =
          PowerSeries.mk g * (PowerSeries.mk (fun k => (θ⁻¹) ^ k) *
            PowerSeries.mk (armaCoeff 0 θ⁻¹)) * PowerSeries.mk (armaCoeff 0 θ) by ring,
        mk_geom_factor θ, mul_one]
    rw [hcoef] at hft
    exact hft.congr_fun fun n => by rw [hw]
  have hfitted : gen (factorCoeff θ⁻¹ g) θ⁻¹ = (1 - θ⁻¹ ^ 2) * gen g θ⁻¹ := by
    rw [gen_factorCoeff θ⁻¹ hg hq.le, sq]
  have hgne : gen g θ⁻¹ ≠ 0 := by
    intro h0
    refine genFnC_ne_zero_of_recoverable hg ⟨h, hh, hconv⟩ (z := ((θ⁻¹ : ℝ) : ℂ)) ?_ ?_
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact hq.le
    · rw [genFnC_ofReal, h0, Complex.ofReal_zero]
  have hsq : (1 : ℝ) - θ⁻¹ ^ 2 ≠ 0 := by
    have : θ⁻¹ ^ 2 < 1 := by
      rw [← sq_abs]
      exact pow_lt_one₀ (abs_nonneg _) hq two_ne_zero
    linarith
  have hwne : woldInnov θ (maOne θ e) t ≠ e t := by
    intro hwe
    have hst : s t ∈ pastSpan s t := by simpa using mem_pastSpan_self s t 0
    have hsub' := pastSpan_mono s (show t - 1 ≤ t by omega) hsub
    have : e t ∈ pastSpan s t := by
      rw [← hwe]
      have := Submodule.sub_mem _ hst hsub'
      convert this using 1
      simp only [hs, ha_def]
      abel
    exact hnot this
  exact ⟨hproj, hnorm, hwhite, hfit, hroot, hfitted, by rw [hfitted]; exact mul_ne_zero hsq hgne,
    hnot, hwne⟩

/-! ### Debt: the ex-post present value, and recovering the shock from the debt history -/

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (tool): for `|ρ| < 1` the Hansen–Sargent
coefficients `c_k = ∑ⱼ ρʲ a_{k+1+j}` are absolutely summable, so debt `v_t = ∑ c_k e_{t−k}` is a
moving average. -/
theorem summable_abs_hsCoeff {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| < 1) : Summable (fun k => |hsCoeff a ρ k|) := by
  set F : ℕ × ℕ → ℝ := fun p => |ρ| ^ p.2 * |a (p.1 + 1 + p.2)| with hF
  have hF0 : 0 ≤ F := fun p => by positivity
  have hsw : Summable (F ∘ Prod.swap) := by
    have h0 : 0 ≤ F ∘ Prod.swap := fun p => hF0 p.swap
    rw [summable_prod_of_nonneg h0]
    have hj : ∀ j : ℕ, Summable fun k : ℕ => |ρ| ^ j * |a (k + 1 + j)| := fun j =>
      ((summable_nat_add_iff (f := fun i => |a i|) (1 + j)).mpr ha).mul_left (|ρ| ^ j) |>.congr
        fun k => by simp only [add_assoc]
    refine ⟨hj, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => h0 _) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (∑' i, |a i|))
    change ∑' k, |ρ| ^ j * |a (k + 1 + j)| ≤ |ρ| ^ j * ∑' i, |a i|
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑' k, |a (k + 1 + j)| = ∑' k, |a (k + (1 + j))| :=
          tsum_congr fun k => by rw [add_assoc]
      _ ≤ ∑' i, |a i| := by
          rw [← ha.sum_add_tsum_nat_add (1 + j)]
          exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hFs : Summable F := (Equiv.prodComm ℕ ℕ).summable_iff.mp hsw
  have hk := ((summable_prod_of_nonneg hF0).mp hFs).2
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hk
  have hsk : Summable fun j => ‖ρ ^ j * a (k + 1 + j)‖ :=
    ((summable_prod_of_nonneg hF0).mp hFs).1 k |>.congr fun j => by
      simp [hF]
  calc |hsCoeff a ρ k| = ‖∑' j, ρ ^ j * a (k + 1 + j)‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' j, ‖ρ ^ j * a (k + 1 + j)‖ := norm_tsum_le_tsum_norm hsk
    _ = ∑' j, F (k, j) := tsum_congr fun j => by simp [hF]

/-- Cochrane (2023), Online Appendix eq. (2.18), p. 600 ("debt equals the ex-post as well as
expected present value of surpluses"), in the Hilbert space: if `a(ρ) = 0`, `|ρ| < 1`, then
`∑_{j≥0} ρʲ s_{t+1+j}` converges to the debt `v_t = ∑ c_k e_{t−k}` (Hansen–Sargent `c`). -/
theorem debt_hasSum_expost [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0)
    (t : ℤ) :
    HasSum (fun j : ℕ => ρ ^ j • maProc a e (t + 1 + j)) (maProc (hsCoeff a ρ) e t) := by
  have hc := summable_abs_hsCoeff ha hρ
  have hsum : Summable (fun j : ℕ => ρ ^ j • maProc a e (t + 1 + j)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right ((∑' k, |a k|) * ‖e 0‖))
      fun j => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (norm_maProc_le he ha _) (by positivity)
  have hX := hsum.hasSum
  convert hX using 1
  refine eq_of_inner_e (maProc_mem_eSpan he hc t)
    (hasSum_mem_eSpan hX fun j => Submodule.smul_mem _ _ (maProc_mem_eSpan he ha _))
    fun u => ?_
  refine ((inner_hasSum_right hX (e u)).unique ?_).symm
  rw [inner_e_maProc_int he hc]
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = t - n := ⟨(t - u).toNat, by omega⟩
    have hn : (t - (t - (n : ℤ))).toNat = n := by omega
    rw [hn, hsCoeff]
    refine ((summable_hs ha hρ.le n).hasSum.mul_left σ2).congr_fun fun j => ?_
    rw [real_inner_smul_right, inner_e_maProc_int he ha]
    have h1 : t - (n : ℤ) ≤ t + 1 + j := by omega
    have h2 : (t + 1 + (j : ℤ) - (t - n)).toNat = n + 1 + j := by omega
    simp only [h1, ↓reduceIte, h2]
    ring
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = t + 1 + n := ⟨(u - t - 1).toNat, by omega⟩
    rw [← hasSum_nat_add_iff' n]
    have hz : ∑ i ∈ Finset.range n, ⟪e (t + 1 + n), ρ ^ i • maProc a e (t + 1 + i)⟫ = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [real_inner_smul_right, inner_e_maProc_int he ha]
        have : ¬ t + 1 + (n : ℤ) ≤ t + 1 + i := by rw [Finset.mem_range] at hi; omega
        simp [this]
    rw [hz, sub_zero]
    have hsa : Summable (fun i => a i * ρ ^ i) :=
      Summable.of_norm_bounded ha fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)
    have := hsa.hasSum.mul_left (σ2 * ρ ^ n)
    rw [← gen, h0, mul_zero] at this
    refine this.congr_fun fun i => ?_
    rw [real_inner_smul_right, inner_e_maProc_int he ha]
    have h1 : t + 1 + (n : ℤ) ≤ t + 1 + ((i + n : ℕ) : ℤ) := by push_cast; omega
    have h2 : (t + 1 + ((i + n : ℕ) : ℤ) - (t + 1 + n)).toNat = i := by push_cast; omega
    simp only [h1, ↓reduceIte, h2]
    ring

/-- Cochrane (2023), p. 102 (tool): the moving average with coefficients `δ₀ = 1`, `δ_k = 0`
otherwise is the shock itself. -/
theorem maProc_delta [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (t : ℤ) :
    maProc (fun n => if n = 0 then 1 else 0) e t = e t := by
  have hs : Summable (fun n : ℕ => |(if n = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  refine (maProc_hasSum he hs t).unique ?_
  convert hasSum_ite_eq (0 : ℕ) (e t) using 1
  funext n
  by_cases hn : n = 0 <;> simp [hn]

/-- Cochrane (2023), Online Appendix eq. (2.20), p. 601: with `a(L) = (1 − θL)g(L)`, `θ = ρ⁻¹`,
the Hansen–Sargent debt coefficients are `c_k = −θg_k`: "the non-invertible root cancels". -/
theorem hsCoeff_factor {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) :
    hsCoeff (factorCoeff θ g) θ⁻¹ = fun k => -θ * g k := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have := (factor_value (a := factorCoeff θ g) hg (inv_ne_zero hθ0) hq rfl (fun k => by
    simp only [factorCoeff, inv_inv])).2
  funext k
  rw [this k, inv_inv]

/-- Cochrane (2023), Online Appendix eq. (2.20), p. 601 ("thus, one can recover the structural
shock to surpluses from an autoregression of debt on past debt"): if `a(L) = (1 − θL)g(L)`,
`|θ| > 1`, and `g` has an absolutely summable inverse `h`, then `e_t = −θ⁻¹∑_k h_k v_{t−k}`: the
shock lies in the closed span of current and past debt. -/
theorem shock_mem_debtSpan [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hrec : Recoverable g)
    (t : ℤ) : e t ∈ pastSpan (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t := by
  obtain ⟨h, hh, hconv⟩ := hrec
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  rw [hsCoeff_factor hθ hg]
  have hcg : Summable (fun k => |-θ * g k|) := (hg.mul_left |θ|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hb : Summable (fun k => |-θ⁻¹ * h k|) := (hh.mul_left |θ⁻¹|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hf := hasSum_filter_maProc he hb hcg t
  have hco : cconv (fun k => -θ⁻¹ * h k) (fun k => -θ * g k) =
      fun n => if n = 0 then 1 else 0 := by
    funext n
    rw [cconv, ← hconv n]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hco, maProc_delta he] at hf
  refine hasSum_mem_pastSpan hf fun k => Submodule.smul_mem _ _ (mem_pastSpan_self _ t k)

/-- Cochrane (2023), Online Appendix p. 601 ("the debt is an invertible moving average of the
structural shock. Thus, one can recover the structural shock … from an autoregression of debt on
past debt"), **correction**: this needs the other roots of `a(L)` outside the unit circle. With
`a(L) = (1 − θL)(1 − 2L)`, `|θ| > 1`, the government repays (`a(θ⁻¹) = 0`) and debt is
`v_t = −θ(1 − 2L)e_t`, a function of current and past shocks, but the shock is NOT in the closed
span of current and past debt (the debt MA has the root `1/2` inside the disc). -/
theorem debt_not_invertible_example [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    gen (factorCoeff θ (armaCoeff 0 2)) θ⁻¹ = 0 ∧
    hsCoeff (factorCoeff θ (armaCoeff 0 2)) θ⁻¹ = (fun k => -θ * armaCoeff 0 2 k) ∧
    e t ∉ pastSpan (maProc (hsCoeff (factorCoeff θ (armaCoeff 0 2)) θ⁻¹) e) t := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  have hg := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) 2
  have hhs := hsCoeff_factor hθ hg
  refine ⟨by rw [gen_factorCoeff θ hg hq.le, mul_inv_cancel₀ hθ0, sub_self, zero_mul], hhs, ?_⟩
  rw [hhs]
  have hcg : Summable (fun k => |-θ * armaCoeff 0 2 k|) := (hg.mul_left |θ|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hroot : gen (fun k => -θ * armaCoeff 0 2 k) (1 / 2) = 0 := by
    have h1 : gen (fun k => -θ * armaCoeff 0 2 k) (1 / 2) =
        -θ * gen (armaCoeff 0 2) (1 / 2) := by
      rw [Cochrane.DebtDeficitsInflation.Innovations.gen,
        Cochrane.DebtDeficitsInflation.Innovations.gen, ← tsum_mul_left]
      exact tsum_congr fun j => by ring
    rw [h1, ma1_aRho]
    norm_num
  exact not_mem_pastSpan_of_aRho_eq_zero he hσ hcg (by norm_num) hroot t

/-! ### Granger causality: debt helps forecast surpluses -/

/-- Cochrane (2023), Online Appendix p. 597 (tool; stationarity of a moving average in white
noise): white noise with `σ² ≠ 0` has a unitary time shift `U e_t = e_{t+1}` of the whole
Hilbert space (extend the normalised shocks to a Hilbert basis and shift them, fixing the rest). -/
theorem exists_shift [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) : ∃ U : H ≃ₗᵢ[ℝ] H, ∀ t, U (e t) = e (t + 1) := by
  classical
  have hσn : σ2 = ‖e 0‖ ^ 2 := by
    have := he 0 0
    simp only [↓reduceIte, real_inner_self_eq_norm_sq] at this
    exact this.symm
  have hn : ‖e 0‖ ≠ 0 := by
    intro h0; rw [h0] at hσn; exact hσ (by simpa using hσn)
  set ê : ℤ → H := fun t => ‖e 0‖⁻¹ • e t with hê
  have hon : Orthonormal ℝ ê := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hê, real_inner_smul_left, real_inner_smul_right]
    rw [he i j]
    split_ifs
    · rw [hσn]; field_simp
    · ring
  have hinj : Function.Injective ê := hon.linearIndependent.injective
  have hsub : Orthonormal ℝ (Subtype.val : Set.range ê → H) :=
    (orthonormal_subtype_range hinj).2 hon
  obtain ⟨w, b, hsw, hb⟩ := hsub.exists_hilbertBasis_extension
  have hmem : ∀ t, ê t ∈ w := fun t => hsw ⟨t, rfl⟩
  have hch : ∀ t (h : ∃ s, ê s = ê t), h.choose = t := fun t h => hinj h.choose_spec
  let f : w → w := fun x => if h : ∃ t, ê t = x then ⟨ê (h.choose + 1), hmem _⟩ else x
  let g : w → w := fun x => if h : ∃ t, ê t = x then ⟨ê (h.choose - 1), hmem _⟩ else x
  have hf : ∀ t, f ⟨ê t, hmem t⟩ = ⟨ê (t + 1), hmem _⟩ := fun t => by
    have h : ∃ s, ê s = ê t := ⟨t, rfl⟩
    simp only [f, h, ↓reduceDIte, hch t h]
  have hg : ∀ t, g ⟨ê t, hmem t⟩ = ⟨ê (t - 1), hmem _⟩ := fun t => by
    have h : ∃ s, ê s = ê t := ⟨t, rfl⟩
    simp only [g, h, ↓reduceDIte, hch t h]
  have hgf : ∀ x, g (f x) = x := fun x => by
    by_cases h : ∃ t, ê t = x
    · obtain ⟨t, ht⟩ := h
      obtain rfl : x = ⟨ê t, hmem t⟩ := Subtype.ext ht.symm
      rw [hf, hg]
      simp
    · simp only [f, g, h, ↓reduceDIte]
  have hfg : ∀ x, f (g x) = x := fun x => by
    by_cases h : ∃ t, ê t = x
    · obtain ⟨t, ht⟩ := h
      obtain rfl : x = ⟨ê t, hmem t⟩ := Subtype.ext ht.symm
      rw [hg, hf]
      simp
    · simp only [f, g, h, ↓reduceDIte]
  let σ : w ≃ w := ⟨f, g, hgf, hfg⟩
  have hb' : Orthonormal ℝ (b ∘ σ) := b.orthonormal.comp σ σ.injective
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range (b ∘ σ))).topologicalClosure := by
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ, b.dense_span]
  refine ⟨b.repr.trans (HilbertBasis.mk hb' hsp).repr.symm, fun t => ?_⟩
  have key : ∀ i, (b.repr.trans (HilbertBasis.mk hb' hsp).repr.symm) (b i) = b (σ i) := by
    intro i
    rw [LinearIsometryEquiv.trans_apply, b.repr_self, HilbertBasis.repr_symm_single,
      HilbertBasis.coe_mk]
    rfl
  have hbi : ∀ τ, b ⟨ê τ, hmem τ⟩ = ê τ := fun τ => by rw [hb]
  have het : ∀ τ, e τ = ‖e 0‖ • ê τ := fun τ => by
    rw [hê, smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [het, map_smul, ← hbi, key]
  change ‖e 0‖ • b (f ⟨ê t, hmem t⟩) = e (t + 1)
  rw [hf, hbi, het (t + 1)]

/-- Cochrane (2023), Online Appendix p. 601 ("a VAR including surplus and value of debt"): the
closed linear span of current and past surpluses AND current and past debt. -/
noncomputable def jointSpan (s v : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun k : ℕ => s (t - k)) ∪
    Set.range (fun k : ℕ => v (t - k)))).topologicalClosure

/-- Cochrane (2023), p. 601 (tool): the surplus history is part of the VAR's information. -/
theorem pastSpan_le_jointSpan (s v : ℤ → H) (t : ℤ) : pastSpan s t ≤ jointSpan s v t :=
  Submodule.topologicalClosure_mono (Submodule.span_mono Set.subset_union_left)

/-- Cochrane (2023), p. 601 (tool): the debt history is part of the VAR's information. -/
theorem debt_mem_jointSpan (s v : ℤ → H) (t : ℤ) (k : ℕ) : v (t - k) ∈ jointSpan s v t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))

/-- Cochrane (2023), p. 601 (tool): the closed span of the debt history is part of the VAR's
information. -/
theorem pastSpan_debt_le_jointSpan (s v : ℤ → H) (t : ℤ) : pastSpan v t ≤ jointSpan s v t :=
  Submodule.topologicalClosure_mono (Submodule.span_mono Set.subset_union_right)

/-- Cochrane (2023), p. 597 (tool): a continuous linear map sending the generators of one past
span to those of another maps the closed spans into each other. -/
theorem map_pastSpan (L : H →L[ℝ] H) {s s' : ℤ → H} {t t' : ℤ}
    (h : ∀ k : ℕ, L (s (t - k)) = s' (t' - k)) {x : H} (hx : x ∈ pastSpan s t) :
    L x ∈ pastSpan s' t' := by
  have hle : pastSpan s t ≤ (pastSpan s' t').comap (L : H →ₗ[ℝ] H) := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨k, rfl⟩
      change L (s (t - k)) ∈ pastSpan s' t'
      rw [h k]
      exact mem_pastSpan_self s' t' k
    · exact (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  exact hle hx

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("VAR shocks to debt `ε_t` help to forecast
surpluses, so debt Granger-causes surpluses"), for an ARBITRARY absolutely summable moving
average: let `s_t = a(L)e_t` with `a₀ ≠ 0`, `a(ρ) = 0`, `|ρ| < 1`, and let `v_t = ∑c_ke_{t−k}` be
the debt (Hansen–Sargent coefficients; by `debt_hasSum_expost` the ex-post present value of
surpluses). Then the best linear forecast of `s_{t+1}` from current and past surpluses and debt
differs from the one from surpluses alone, and its error is strictly smaller. The proof uses
only stationarity (`exists_shift`): if debt did not help, the surplus innovations `u` would satisfy
`∑ρʲ⟪u_{t+1}, s_{t+1+j}⟫ = 0`, which makes `∑ρᵏu_{t−k}` a nonzero element of the surplus past
orthogonal to that past. -/
theorem granger_general [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (ha0 : a 0 ≠ 0) {ρ : ℝ}
    (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    (haveI : (pastSpan (maProc a e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc a e) t).starProjection (maProc a e (t + 1))) ≠
    (haveI : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).starProjection (maProc a e (t + 1))) ∧
    (haveI : (pastSpan (maProc a e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
    haveI : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      ‖maProc a e (t + 1) - (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).starProjection
        (maProc a e (t + 1))‖ <
      ‖maProc a e (t + 1) - (pastSpan (maProc a e) t).starProjection (maProc a e (t + 1))‖) := by
  have hS : ∀ τ, (pastSpan (maProc a e) τ).HasOrthogonalProjection := fun τ => by
    unfold pastSpan; infer_instance
  have hJ : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
    unfold jointSpan; infer_instance
  set s := maProc a e with hs
  set v := maProc (hsCoeff a ρ) e with hv
  obtain ⟨U, hU⟩ := exists_shift he hσ
  set UL : H →L[ℝ] H := U.toContinuousLinearEquiv.toContinuousLinearMap with hUL
  set UL' : H →L[ℝ] H := U.symm.toContinuousLinearEquiv.toContinuousLinearMap with hUL'
  have hUs : ∀ τ, U (s τ) = s (τ + 1) := by
    intro τ
    have h1 := (maProc_hasSum he ha τ).mapL UL
    refine h1.unique ((maProc_hasSum he ha (τ + 1)).congr_fun fun k => ?_)
    change U (a k • e (τ - k)) = a k • e (τ + 1 - k)
    rw [map_smul, hU, show τ - (k : ℤ) + 1 = τ + 1 - k by ring]
  have hUs' : ∀ τ, U.symm (s τ) = s (τ - 1) := fun τ => by
    rw [← U.symm_apply_apply (s (τ - 1)), hUs, sub_add_cancel]
  -- the spans move with the shift
  have hUS : ∀ τ x, x ∈ pastSpan s τ → U x ∈ pastSpan s (τ + 1) := fun τ x hx =>
    map_pastSpan UL (fun k => by
      change U (s (τ - k)) = s (τ + 1 - k)
      rw [hUs, show τ - (k : ℤ) + 1 = τ + 1 - k by ring]) hx
  have hUS' : ∀ τ x, x ∈ pastSpan s (τ + 1) → U.symm x ∈ pastSpan s τ := fun τ x hx =>
    map_pastSpan UL' (fun k => by
      change U.symm (s (τ + 1 - k)) = s (τ - k)
      rw [hUs', show τ + 1 - (k : ℤ) - 1 = τ - k by ring]) hx
  have hP : ∀ τ x, U ((pastSpan s τ).starProjection x) =
      (pastSpan s (τ + 1)).starProjection (U x) := by
    intro τ x
    refine (Submodule.eq_starProjection_of_mem_orthogonal
      (hUS τ _ (Submodule.starProjection_apply_mem _ x)) ?_).symm
    rw [← map_sub, Submodule.mem_orthogonal]
    intro y hy
    rw [← U.apply_symm_apply y, LinearIsometryEquiv.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal (hUS' τ y hy)
      (Submodule.sub_starProjection_mem_orthogonal x)
  -- the surplus innovations and their stationarity
  set u : ℤ → H := fun τ => s τ - (pastSpan s (τ - 1)).starProjection (s τ) with hu
  have hUu : ∀ τ, U (u τ) = u (τ + 1) := by
    intro τ
    simp only [hu, map_sub, hP, hUs, sub_add_cancel, add_sub_cancel_right]
  have hu_orth : ∀ τ, u τ ∈ (pastSpan s (τ - 1))ᗮ := fun τ =>
    Submodule.sub_starProjection_mem_orthogonal (s τ)
  have hs_mem : ∀ τ, s τ ∈ pastSpan s τ := fun τ => by simpa using mem_pastSpan_self s τ 0
  have hu_mem : ∀ τ, u τ ∈ pastSpan s τ := fun τ =>
    Submodule.sub_mem _ (hs_mem τ)
      (pastSpan_mono s (by omega) (Submodule.starProjection_apply_mem _ _))
  have hstep : ∀ τ (j : ℕ), ⟪u (τ + 1), s (τ + 1 + j)⟫ = ⟪u τ, s (τ + j)⟫ := by
    intro τ j
    rw [← hUu, show τ + 1 + (j : ℤ) = τ + j + 1 by ring, ← hUs, LinearIsometryEquiv.inner_map_map]
  have hγ : ∀ τ (j : ℕ), ⟪u τ, s (τ + j)⟫ = ⟪u 0, s j⟫ := by
    intro τ j
    induction τ using Int.induction_on with
    | zero => simp
    | succ i ih => rw [hstep, ih]
    | pred i ih =>
      rw [← ih, ← hstep (-(i : ℤ) - 1) j, show -(i : ℤ) - 1 + 1 = -i by ring]
  have huu : ∀ τ, ⟪u τ, u τ⟫ = ⟪u 0, s 0⟫ := by
    intro τ
    have h1 : ⟪u τ, (pastSpan s (τ - 1)).starProjection (s τ)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) (hu_orth τ)
    have h2 := hγ τ 0
    simp only [Nat.cast_zero, add_zero] at h2
    conv_lhs => rw [show u τ = s τ - (pastSpan s (τ - 1)).starProjection (s τ) from rfl]
    rw [inner_sub_right, h1, sub_zero, ← h2]
  -- the innovation is not zero
  have he_orth : ∀ τ, e τ ∈ (pastSpan s (τ - 1))ᗮ := fun τ =>
    mem_orthogonal_pastSpan fun k => by
      have := inner_e_maProc_future he ha (τ - 1 - k) k
      rwa [show τ - 1 - (k : ℤ) + 1 + k = τ by ring] at this
  have heu : ∀ τ, ⟪e τ, u τ⟫ = σ2 * a 0 := by
    intro τ
    have h1 : ⟪e τ, (pastSpan s (τ - 1)).starProjection (s τ)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) (he_orth τ)
    change ⟪e τ, s τ - (pastSpan s (τ - 1)).starProjection (s τ)⟫ = _
    rw [inner_sub_right, h1, sub_zero]
    simpa using inner_e_maProc he ha τ 0
  have hu0 : ⟪u t, u t⟫ ≠ 0 := by
    intro h
    have : u t = 0 := inner_self_eq_zero.mp h
    have := heu t
    rw [‹u t = 0›, inner_zero_right] at this
    exact mul_ne_zero hσ ha0 this.symm
  have hnu : ∀ τ, ‖u τ‖ = ‖u 0‖ := by
    intro τ
    have h1 := huu τ
    have h2 := huu 0
    rw [real_inner_self_eq_norm_sq] at h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)
  -- the main argument
  have hne : (pastSpan s t).starProjection (s (t + 1)) ≠
      (jointSpan s v t).starProjection (s (t + 1)) := by
    intro hEq
    have hut : u (t + 1) = s (t + 1) - (jointSpan s v t).starProjection (s (t + 1)) := by
      change s (t + 1) - (pastSpan s (t + 1 - 1)).starProjection (s (t + 1)) = _
      rw [add_sub_cancel_right, hEq]
    have hJo : u (t + 1) ∈ (jointSpan s v t)ᗮ := by
      rw [hut]; exact Submodule.sub_starProjection_mem_orthogonal _
    have hv0 : ⟪u (t + 1), v t⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (by simpa using debt_mem_jointSpan s v t 0) hJo
    -- `∑ρʲγ_j = 0`
    have hΓ : HasSum (fun j : ℕ => ρ ^ j * ⟪u 0, s j⟫) 0 := by
      have h := inner_hasSum_right (debt_hasSum_expost he ha hρ h0 t) (u (t + 1))
      rw [← hv, hv0] at h
      refine h.congr_fun fun j => ?_
      rw [real_inner_smul_right, ← hγ (t + 1) j]
    -- `y = ∑ρᵏu_{t−k}`
    have hys : Summable (fun k : ℕ => ρ ^ k • u (t - k)) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right ‖u 0‖) fun k => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_pow, hnu]
    have hy := hys.hasSum
    set y := ∑' k : ℕ, ρ ^ k • u (t - k) with hy_def
    have hyS : y ∈ pastSpan s t :=
      hasSum_mem_pastSpan hy fun k => Submodule.smul_mem _ _
        (pastSpan_mono s (by omega) (hu_mem (t - k)))
    have hyO : y ∈ (pastSpan s t)ᗮ := by
      refine mem_orthogonal_pastSpan fun j => ?_
      rw [real_inner_comm]
      have h := inner_hasSum_right hy (s (t - j))
      refine h.unique ?_
      rw [← hasSum_nat_add_iff' j]
      have hz : ∑ k ∈ Finset.range j, ⟪s (t - j), ρ ^ k • u (t - k)⟫ = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [real_inner_smul_right]
          have hkj : k < j := Finset.mem_range.mp hk
          have hmem : s (t - j) ∈ pastSpan s (t - k - 1) := by
            have := mem_pastSpan_self s (t - k - 1) (j - k - 1)
            rwa [show t - (k : ℤ) - 1 - ((j - k - 1 : ℕ) : ℤ) = t - j by omega]
              at this
          rw [Submodule.inner_right_of_mem_orthogonal hmem (hu_orth (t - k)), mul_zero]
      rw [hz, sub_zero]
      have := hΓ.mul_left (ρ ^ j)
      rw [mul_zero] at this
      refine this.congr_fun fun i => ?_
      rw [real_inner_smul_right, real_inner_comm,
        show t - ((i + j : ℕ) : ℤ) = t - j - i by push_cast; ring,
        show s (t - j) = s (t - j - i + i) by ring_nf, hγ, pow_add]
      ring
    have hy0 : y = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hyS hyO)
    have hyu : ⟪u t, y⟫ = ⟪u t, u t⟫ := by
      have h := inner_hasSum_right hy (u t)
      refine h.unique ?_
      have h1 : HasSum (fun k : ℕ => ⟪u t, ρ ^ k • u (t - k)⟫)
          ⟪u t, ρ ^ 0 • u (t - ((0 : ℕ) : ℤ))⟫ := hasSum_single 0 fun k hk => by
        rw [real_inner_smul_right]
        have hmem : u (t - k) ∈ pastSpan s (t - 1) :=
          pastSpan_mono s (by omega) (hu_mem (t - k))
        rw [Submodule.inner_left_of_mem_orthogonal hmem (hu_orth t), mul_zero]
      have e0 : ⟪u t, ρ ^ 0 • u (t - ((0 : ℕ) : ℤ))⟫ = ⟪u t, u t⟫ := by simp
      rwa [e0] at h1
    rw [hy0, inner_zero_right] at hyu
    exact hu0 hyu.symm
  refine ⟨hne, ?_⟩
  -- Pythagoras
  set p := (pastSpan s t).starProjection (s (t + 1))
  set q := (jointSpan s v t).starProjection (s (t + 1))
  have hpJ : p ∈ jointSpan s v t :=
    pastSpan_le_jointSpan s v t (Submodule.starProjection_apply_mem _ _)
  have hqp : q - p ∈ jointSpan s v t :=
    Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _) hpJ
  have horth : ⟪s (t + 1) - q, q - p⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hqp (Submodule.sub_starProjection_mem_orthogonal _)
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [show s (t + 1) - q + (q - p) = s (t + 1) - p by abel] at hpy
  have hpos : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have : ‖s (t + 1) - q‖ ^ 2 < ‖s (t + 1) - p‖ ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/-- Cochrane (2023), p. 601 (tool): a vector orthogonal to every current and past surplus and debt
is orthogonal to the joint span. -/
theorem mem_orthogonal_jointSpan {s v : ℤ → H} {t : ℤ} {x : H}
    (hs : ∀ k : ℕ, ⟪x, s (t - k)⟫ = 0) (hv : ∀ k : ℕ, ⟪x, v (t - k)⟫ = 0) :
    x ∈ (jointSpan s v t)ᗮ := by
  have hle : jointSpan s v t ≤ (ℝ ∙ x)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hs k)
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv k)
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), p. 601, and p. 102 ("the value of debt
reveals the true shock"), quantitatively: for `a(L) = (1 − θL)g(L)`, `|θ| > 1` (`ρ = θ⁻¹`), `g₀ = 1`
and `g` invertible, the joint surplus–debt forecast of `s_{t+1}` has error `e_{t+1}` (variance
`σ²`: the structural shock is recovered), the surplus-only forecast has error variance
`θ²σ² = σ²/ρ²`, and `σ² < θ²σ²`: debt Granger-causes surpluses. -/
theorem granger_factor [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|))
    (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    (haveI : (jointSpan (maProc (factorCoeff θ g) e)
        (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      Submodule.starProjection
        (jointSpan (maProc (factorCoeff θ g) e) (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t)
        (maProc (factorCoeff θ g) e (t + 1))) =
      maProc (factorCoeff θ g) e (t + 1) - e (t + 1) ∧
    (haveI : (pastSpan (maProc (factorCoeff θ g) e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff θ g) e (t + 1) - Submodule.starProjection
        (pastSpan (maProc (factorCoeff θ g) e) t) (maProc (factorCoeff θ g) e (t + 1))‖ ^ 2) =
      θ ^ 2 * σ2 ∧
    ‖e (t + 1)‖ ^ 2 = σ2 ∧ σ2 < θ ^ 2 * σ2 := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  have ha := summable_factorCoeff θ hg
  have hc := summable_abs_hsCoeff ha hq
  have hJ : (jointSpan (maProc (factorCoeff θ g) e)
      (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t).HasOrthogonalProjection := by
    unfold jointSpan; infer_instance
  set s := maProc (factorCoeff θ g) e with hs
  set v := maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e with hv
  have hσn : ‖e (t + 1)‖ ^ 2 = σ2 := by
    have := he (t + 1) (t + 1)
    simp only [↓reduceIte, real_inner_self_eq_norm_sq] at this
    exact this
  have hσp : 0 < σ2 := lt_of_le_of_ne (hσn ▸ sq_nonneg _) (Ne.symm hσ)
  -- the joint forecast
  have hJo : e (t + 1) ∈ (jointSpan s v t)ᗮ := mem_orthogonal_jointSpan
    (fun k => by
      have := inner_e_maProc_future he ha (t - k) k
      rwa [show t - (k : ℤ) + 1 + k = t + 1 by ring] at this)
    (fun k => by
      have := inner_e_maProc_future he hc (t - k) k
      rwa [show t - (k : ℤ) + 1 + k = t + 1 by ring] at this)
  have hqJ : s (t + 1) - e (t + 1) ∈ jointSpan s v t := by
    have h := maProc_hasSum he ha (t + 1)
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero] at h
    rw [show factorCoeff θ g 0 = 1 from hg0, one_smul] at h
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
      (Eventually.of_forall fun n => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
    rw [show t + 1 - ((k + 1 : ℕ) : ℤ) = t - k by push_cast; ring]
    exact pastSpan_debt_le_jointSpan s v t
      (pastSpan_mono v (by omega) (shock_mem_debtSpan he hθ hg hrec (t - k)))
  have hPJ : (jointSpan s v t).starProjection (s (t + 1)) = s (t + 1) - e (t + 1) :=
    Submodule.eq_starProjection_of_mem_orthogonal hqJ (by simpa using hJo)
  -- the surplus-only forecast
  obtain ⟨hproj, hnorm, -⟩ := wold_factor he hσ hθ hg hg0 hrec (t + 1)
  simp only [add_sub_cancel_right] at hproj
  have hS : (pastSpan s t).HasOrthogonalProjection := by unfold pastSpan; infer_instance
  have hPS : ‖s (t + 1) - (pastSpan s t).starProjection (s (t + 1))‖ ^ 2 = θ ^ 2 * σ2 := by
    rw [hproj, sub_sub_cancel, ← real_inner_self_eq_norm_sq, hnorm]
  have hθ2 : 1 < θ ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg θ]
  exact ⟨hPJ, hPS, hσn, by nlinarith⟩

/-! ### Links to the MA(1) statements of `Invertibility` -/

/-- Cochrane (2023), p. 102 (link): with `g = 1` the factorised moving average is the MA(1)
`1 − θL` of `Invertibility` (`armaCoeff 0 θ`). -/
theorem factorCoeff_delta (θ : ℝ) :
    factorCoeff θ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ := by
  funext k
  rcases k with _ | _ | k <;> simp [factorCoeff, armaCoeff]

/-- Cochrane (2023), p. 102 (link): `g = 1` is trivially invertible. -/
theorem recoverable_delta : Recoverable (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
  refine ⟨fun k => if k = 0 then 1 else 0,
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all, fun n => ?_⟩
  rcases n with _ | n
  · simp
  · rw [Finset.sum_eq_zero fun k _ => ?_]
    · simp
    · by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]

/-- Cochrane (2023), p. 102 and Online Appendix (2.13), p. 599 (link): for `g = 1`, `wold_factor`
is `Invertibility.Hilbert.ma1_wold` — structural MA(1) `1 − θL`, fitted MA(1) `1 − θ⁻¹L` with
`ã(ρ) = 1 − ρ²` at `ρ = θ⁻¹` (`Invertibility.ma1_fitted_aRho`), and debt `v_t = −θe_t`
(p. 102, "`v_t = −ρ⁻¹ε_t`"). -/
theorem wold_factor_ma1 {θ : ℝ} (hθ : 1 < |θ|) :
    factorCoeff θ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ ∧
    factorCoeff θ⁻¹ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ⁻¹ ∧
    gen (factorCoeff θ⁻¹ (fun k => if k = 0 then 1 else 0)) θ⁻¹ = 1 - θ⁻¹ ^ 2 ∧
    hsCoeff (armaCoeff 0 θ) θ⁻¹ = fun k => -θ * (if k = 0 then 1 else 0) := by
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  refine ⟨factorCoeff_delta θ, factorCoeff_delta θ⁻¹, ?_, ?_⟩
  · rw [factorCoeff_delta]
    exact (ma1_fitted_aRho hq).1
  · rw [← factorCoeff_delta θ]
    exact hsCoeff_factor hθ (summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all)

end Cochrane.DebtDeficitsInflation.InvertibilityMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Invertibility, Wold and Granger causality in `L²` of an i.i.d. probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, pp. 597–601.

The Hilbert-space statements of `Invertibility` and `InvertibilityMeasure` are instantiated in the
genuine probability setting: `H = L²(Ω, P)` with `Ω = ℕ → ℝ`, `P = ν^ℕ` the i.i.d. product of
`ExpectationsMeasureIID` (not finitely supported), and the structural shocks
`e_t = ε_{φ(t)}` for a bijection `φ : ℤ ≃ ℕ` (a `ℤ`-indexed i.i.d. sequence). Inner products are
covariances `E[XY]`, closed spans are mean-square limits of linear combinations, and orthogonal
projections are best linear forecasts (what a VAR estimates).

## Main results

* `iid_whiteNoise`: the shocks are white noise in `L²` (independence and mean zero).
* `iid_not_filter`: `a(ρ) = 0`, `|ρ| ≤ 1` (including `ρ = 1`): no absolutely summable filter of
  the surplus history converges in mean square to the shock.
* `iid_not_mem_pastSpan` (`|ρ| < 1`: the shock is not in the closed span of the surplus history).
* `iid_unit_root`: correction at `ρ = ±1` — the shock IS a mean-square limit of linear
  combinations of current and past surpluses for `s_t = e_t − ρe_{t−1}`;
  `closedSpan_fails_at_unit_root`: so the closed-span statement is false for `|ρ| ≤ 1`.
* `iid_wold_factor`, `iid_granger_general`, `iid_granger_factor`: the factorised Wold statement and
  "debt Granger-causes surpluses" in `L²`.
* `coin_L2`: the fair-coin instance (`σ² = 1`).
-/

namespace Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open Cochrane.DebtDeficitsInflation.ExpectationsMeasure
open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open Cochrane.DebtDeficitsInflation.InvertibilityMeasure
open scoped RealInnerProductSpace

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 102 (the shocks as second-moment random variables): a bounded i.i.d.
shock is square integrable. -/
theorem memLp_coord {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (i : ℕ) :
    MemLp (fun ω : ℕ → ℝ => ω i) 2 (iidSystem ν).μ :=
  MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable B
    ((shock_ae_bdd ν hbdd i).mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 102 and Online Appendix p. 597: the structural shocks as elements of
`L²(ν^ℕ)`, `e_t = ε_{φ(t)}` with `φ : ℤ ≃ ℕ`. -/
noncomputable def shockL2 {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t : ℤ) :
    Lp ℝ 2 (iidSystem ν).μ :=
  (memLp_coord hbdd (Equiv.intEquivNat t)).toLp _

/-- Cochrane (2023), p. 102 (tool): distinct coordinates of the i.i.d. product are uncorrelated
when the mean is zero, `E[ε_iε_j] = 0`. -/
theorem integral_coord_mul {i j : ℕ} (hij : i ≠ j) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) :
    ∫ ω, ω i * ω j ∂(iidSystem ν).μ = 0 := by
  have hind : iIndepFun (fun k (ω : ℕ → ℝ) => ω k) (iidSystem ν).μ :=
    iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
      (fun _ => measurable_id)
  rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
    (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable]
  have h := integral_shock_fun ν i (f := id) measurable_id
  simp only [id] at h
  change (∫ ω, ω i ∂(iidSystem ν).μ) * _ = 0
  rw [h, hmean, zero_mul]

/-- Cochrane (2023), p. 102, and Online Appendix p. 597: i.i.d. shocks with mean `0`, variance
`σ²` and bounded support are white noise in `L²(ν^ℕ)`: `E[e_te_u] = σ²` if `t = u`, `0`
otherwise. -/
theorem iid_whiteNoise {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    WhiteNoise (shockL2 hbdd) σ2 := by
  intro t u
  rw [L2.inner_def]
  have hc : ∀ τ, (shockL2 hbdd τ : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat τ) := fun τ => MemLp.coeFn_toLp _
  have hcongr : (fun ω => ⟪(shockL2 hbdd t : (ℕ → ℝ) → ℝ) ω,
      (shockL2 hbdd u : (ℕ → ℝ) → ℝ) ω⟫) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat t) * ω (Equiv.intEquivNat u) := by
    filter_upwards [hc t, hc u] with ω h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
      mul_comm]
  rw [integral_congr_ae hcongr]
  by_cases htu : t = u
  · subst htu
    simp only [↓reduceIte]
    have h := integral_shock_fun ν (Equiv.intEquivNat t) (f := fun x => x ^ 2)
      (measurable_id.pow_const 2)
    rw [hvar] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · simp only [htu, ↓reduceIte]
    exact integral_coord_mul ((Equiv.intEquivNat).injective.ne htu) hmean

/-! ### The statements in `L²` -/

/-- Cochrane (2023), p. 102, and Online Appendix p. 600, in `L²` of the i.i.d. probability space,
for every `|ρ| ≤ 1` including `ρ = 1`: if `a(ρ) = 0`, no absolutely summable filter of current and
past surpluses converges in mean square to the structural shock. -/
theorem iid_not_filter {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    {ρ : ℝ} (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℤ) :
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc a (shockL2 hbdd) (t - k)) (shockL2 hbdd t) :=
  not_filter_of_aRho_eq_zero (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha hρ h0 t

/-- Cochrane (2023), p. 102 and Online Appendix p. 597, **correction at `ρ = ±1`**, in `L²`: for
`s_t = e_t − ρe_{t−1}` with `ρ² = 1` (so `a(ρ) = 0`), the structural shock is in the closed span of
current and past surpluses (a mean-square limit of linear combinations of them), although no
absolutely summable filter recovers it. -/
theorem iid_unit_root {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {ρ : ℝ} (hρ : ρ ^ 2 = 1) (t : ℤ) :
    gen (armaCoeff 0 ρ) ρ = 0 ∧
    shockL2 hbdd t ∈ pastSpan (maProc (armaCoeff 0 ρ) (shockL2 hbdd)) t ∧
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (armaCoeff 0 ρ) (shockL2 hbdd) (t - k))
        (shockL2 hbdd t) := by
  have he := iid_whiteNoise hmean hvar hbdd
  have hρ1 : |ρ| ≤ 1 := by
    have : |ρ| ^ 2 = 1 := by rw [sq_abs, hρ]
    nlinarith [abs_nonneg ρ]
  obtain ⟨h0, hmem⟩ := mem_pastSpan_unit_root he hρ t
  exact ⟨h0, hmem, not_filter_of_aRho_eq_zero he hσ.ne' (summable_abs_armaCoeff (by simp) ρ)
    hρ1 h0 t⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, in `L²`: the factorised Wold statement
(`InvertibilityMeasure.wold_factor`) for i.i.d. shocks — the autoregression's error `w` has
variance `θ²σ²`, the fitted moving average has the flipped root and `ã(θ⁻¹) ≠ 0`, and
`w_t ≠ e_t`. -/
theorem iid_wold_factor {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ}
    (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    ⟪woldInnov θ (maOne θ (shockL2 hbdd)) t, woldInnov θ (maOne θ (shockL2 hbdd)) t⟫ =
      θ ^ 2 * σ2 ∧
    HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ (shockL2 hbdd)) (t - n))
      (maProc (factorCoeff θ g) (shockL2 hbdd) t) ∧
    gen (factorCoeff θ g) θ⁻¹ = 0 ∧ gen (factorCoeff θ⁻¹ g) θ⁻¹ ≠ 0 ∧
    shockL2 hbdd t ∉ pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t ∧
    woldInnov θ (maOne θ (shockL2 hbdd)) t ≠ shockL2 hbdd t := by
  obtain ⟨-, hn, -, hfit, hroot, -, hne, hnot, hw⟩ :=
    wold_factor (iid_whiteNoise hmean hvar hbdd) hσ.ne' hθ hg hg0 hrec t
  exact ⟨hn, hfit, hroot, hne, hnot, hw⟩

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("debt Granger-causes surpluses"), in the
genuine probability setting, for an ARBITRARY absolutely summable moving average with `a₀ ≠ 0`,
`a(ρ) = 0`, `|ρ| < 1`: the mean-square error of the best linear forecast of `s_{t+1}` from
current and past surpluses and debt is strictly smaller than from surpluses alone. -/
theorem iid_granger_general {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    (ha0 : a 0 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    (haveI : (pastSpan (maProc a (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
    haveI : (jointSpan (maProc a (shockL2 hbdd))
        (maProc (hsCoeff a ρ) (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      ‖maProc a (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (jointSpan (maProc a (shockL2 hbdd)) (maProc (hsCoeff a ρ) (shockL2 hbdd)) t)
        (maProc a (shockL2 hbdd) (t + 1))‖ <
      ‖maProc a (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (pastSpan (maProc a (shockL2 hbdd)) t) (maProc a (shockL2 hbdd) (t + 1))‖) :=
  (granger_general (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha ha0 hρ h0 t).2

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), p. 601, in `L²`: for
`a(L) = (1 − θL)g(L)` with `g` invertible, the debt history reveals the shock, the joint forecast
error of `s_{t+1}` is `e_{t+1}` (variance `σ²`) and the surplus-only one has variance
`θ²σ² > σ²`. -/
theorem iid_granger_factor {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ}
    (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    shockL2 hbdd t ∈ pastSpan (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) (shockL2 hbdd)) t ∧
    (haveI : (pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff θ g) (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t)
        (maProc (factorCoeff θ g) (shockL2 hbdd) (t + 1))‖ ^ 2) = θ ^ 2 * σ2 ∧
    ‖shockL2 hbdd (t + 1)‖ ^ 2 = σ2 ∧ σ2 < θ ^ 2 * σ2 := by
  have he := iid_whiteNoise hmean hvar hbdd
  obtain ⟨-, h2, h3, h4⟩ := granger_factor he hσ.ne' hθ hg hg0 hrec t
  exact ⟨shock_mem_debtSpan he hθ hg hrec t, h2, h3, h4⟩

/-- Cochrane (2023), p. 102 and Online Appendix pp. 597–601, for the fair `±1` coin (`σ² = 1`) on
the non-finitely-supported space `{±1}^ℕ`: (i) the MA(1) `s_t = e_t − e_{t−1}` (`ρ = 1`) has
`a(1) = 0`, its shock is in the closed span of past surpluses but no summable filter recovers it;
(ii) for `|ρ| < 1` the MA(1) `s_t = e_t − ρ⁻¹e_{t−1}` has `a(ρ) = 0` and debt strictly improves the
forecast of surpluses (error variances `1` versus `ρ⁻²`). -/
theorem coin_L2 {ρ : ℝ} (hρ0 : 0 < |ρ|) (hρ : |ρ| < 1) (t : ℤ) :
    (∀ F : Finset (ℕ → ℝ), (iidSystem coin).μ ↑F ≠ 1) ∧
    gen (armaCoeff 0 1) 1 = 0 ∧
    shockL2 coin_bdd t ∈ pastSpan (maProc (armaCoeff 0 1) (shockL2 coin_bdd)) t ∧
    (¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (armaCoeff 0 1) (shockL2 coin_bdd) (t - k))
        (shockL2 coin_bdd t)) ∧
    ‖shockL2 coin_bdd (t + 1)‖ ^ 2 = 1 ∧
    (haveI : (pastSpan (maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
        (shockL2 coin_bdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd) (t + 1) -
        Submodule.starProjection (pastSpan (maProc (factorCoeff ρ⁻¹
          (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd)) t)
        (maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd)
          (t + 1))‖ ^ 2) = (ρ⁻¹) ^ 2 * 1 ∧
    (1 : ℝ) < (ρ⁻¹) ^ 2 * 1 := by
  have hθ : 1 < |ρ⁻¹| := by rw [abs_inv]; exact one_lt_inv_iff₀.mpr ⟨hρ0, hρ⟩
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  have hrec := recoverable_delta
  obtain ⟨h1, h2, h3⟩ := iid_unit_root coin_mean coin_var one_pos coin_bdd (ρ := 1) (by norm_num) t
  obtain ⟨-, h5, h6, h7⟩ := iid_granger_factor coin_mean coin_var one_pos coin_bdd hθ hδ
    (by simp) hrec t
  exact ⟨iid_not_finitely_supported coin_mean coin_var one_pos, h1, h2, h3, h6, h5, h7⟩

/-- Cochrane (2023), p. 102 and Online Appendix p. 597, for `|ρ| < 1` in `L²` (the existing
`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero`, instantiated): with `a(ρ) = 0` the
shock is not in the closed span of current and past surpluses. -/
theorem iid_not_mem_pastSpan {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    shockL2 hbdd t ∉ pastSpan (maProc a (shockL2 hbdd)) t :=
  not_mem_pastSpan_of_aRho_eq_zero (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha hρ h0 t

/-- Cochrane (2023), p. 102 and Online Appendix p. 597 ("`ρ ≤ 1`"), **counterexample**: the
closed-span non-invertibility statement is false when extended to `|ρ| ≤ 1` — in `L²` of the
fair-coin product, the MA(1) `1 − L` has `a(1) = 0` but its shock is in the closed span of the
surplus history. -/
theorem closedSpan_fails_at_unit_root (t : ℤ) :
    ¬ ∀ a : ℕ → ℝ, Summable (fun k => |a k|) → ∀ ρ : ℝ, |ρ| ≤ 1 → gen a ρ = 0 →
      shockL2 coin_bdd t ∉ pastSpan (maProc a (shockL2 coin_bdd)) t := by
  intro h
  obtain ⟨h0, hmem, -⟩ := iid_unit_root coin_mean coin_var one_pos coin_bdd (ρ := 1)
    (by norm_num) t
  exact h _ (summable_abs_armaCoeff (by simp) 1) 1 (by simp) h0 hmem

end Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Wold decomposition theorem

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4 and 2.1.6, pp. 597 and 600 ("an autoregression of this surplus
process recovers the Wold representation, which has an invertible moving average"; "if you do
run an autoregression you recover a representation that is invertible, by the Wold
decomposition theorem").

The book invokes the Wold decomposition theorem without stating it. This module proves it in full
for a weakly stationary sequence `(x_t)_{t ∈ ℤ}` in a real Hilbert space `H` (in `L²` this is the
space of second moments; inner products are covariances, orthogonal projections are best linear
forecasts). Stationarity is either covariance stationarity (`⟪x_s, x_u⟫` depends only on
`s − u`) or, equivalently (`stationary_iff_exists_shift`), `x` is the orbit of a linear isometry
`U` of `H`, `U x_t = x_{t+1}`.

## Main definitions

* `past x t`: `H_t`, the closed span of `x_t, x_{t−1}, …`; `remote x`: `H_{−∞} = ⋂_t H_t`.
* `innov x t`: the innovation `e_t = x_t − P_{H_{t−1}} x_t` (the one-step-ahead linear forecast
  error, the error of the infinite autoregression).
* `woldCoeff x j`: `c_j = ⟪x_0, e_{−j}⟫ / ‖e‖²`; `detPart x t`: `d_t = P_{H_{−∞}} x_t`.
* `Deterministic x`: `x_t ∈ H_{t−1}` for all `t`; `Regular x`: `H_{−∞} = 0`.

## Main results

* (a) `innov_mem`, `innov_mem_orthogonal`, `innov_whiteNoise`: `e_t ∈ H_t`, `e_t ⟂ H_{t−1}`,
  the `e_t` are orthogonal with constant norm.
* (b) `wold_decomposition`: `x_t = ∑_{j ≥ 0} c_j e_{t−j} + d_t`, the series converging in `H`,
  `∑ c_j² < ∞` (with Bessel's bound), `c_0 = 1` when `e ≠ 0`, `c_j = ⟪x_t, e_{t−j}⟫/‖e‖²` for
  every `t`, `d_t ∈ H_{−∞}`, `d ⟂ e`.
* (c) `wold_unique`: any representation `x_t = ∑ b_j w_{t−j} + z_t` with `w_t ∈ H_t`,
  `w_t ⟂ H_{t−1}`, `b_0 = 1`, `z_t ∈ H_{−∞}` is the Wold one.
* (d) `deterministic_iff`, `regular_iff`, `wold_dichotomy`: `x` is deterministic iff `e = 0` iff
  `d = x`; regular iff `d = 0`; in general the regular part `u_t = ∑ c_j e_{t−j}` is regular, the
  deterministic part `d` is deterministic (`H_{−∞}` is the closed span of `d_{t−1}, d_{t−2}, …`),
  both are stationary and they are uncorrelated. `mixed_example`: neither part can be dropped.
* Stationarity: `stationary_of_shift`, `exists_shift_of_stationary`, `wold_of_stationary`.
* Correction (A2 p. 597, "the Wold representation, which has an invertible moving average"):
  `wold_unit_root`, `IIDEconomy.coin_wold_unit_root` — the Wold moving average is fundamental
  but can have a root on the unit circle (`s_t = ε_t − ε_{t−1}`), and then no absolutely
  summable autoregression recovers the Wold innovation.
* Links: `maProc_regular` (every absolutely summable moving average in white noise is regular);
  `wold_factor_is_wold` (the factorised `InvertibilityMeasure.wold_factor`: its `w_t` is the
  Wold innovation, its fitted coefficients `ã = (1 − θ⁻¹L)g` are the Wold coefficients, and
  `d = 0`); `IIDEconomy.iid_wold`, `IIDEconomy.iid_wold_factor_is_wold`,
  `IIDEconomy.iid_mixed`, `IIDEconomy.coin_wold` in `L²(ν^ℕ)` of the i.i.d. economy of
  `InvertibilityMeasureL2` (the mixed example `x_t = ε_t + 1`: the mean is the deterministic
  part).
-/

namespace Cochrane.DebtDeficitsInflation.Wold

open Filter Topology
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The past, the remote past and the innovations -/

/-- Cochrane (2023), Online Appendix p. 597 (`E(s_t|s_{t−1}, s_{t−2}, …)`): `H_t`, the closed
linear span of `x_t, x_{t−1}, …` (the same subspace as `Invertibility.Hilbert.pastSpan`). -/
noncomputable abbrev past (x : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun k : ℕ => x (t - k))).topologicalClosure

/-- Cochrane (2023), Online Appendix p. 597 (tool): `past` is `Invertibility.Hilbert.pastSpan`. -/
theorem past_eq_pastSpan (x : ℤ → H) (t : ℤ) : past x t = pastSpan x t := rfl

/-- Cochrane (2023), Online Appendix p. 600 (the Wold theorem): the remote past
`H_{−∞} = ⋂_t H_t` (written as its own closure, which `remote_eq` shows is no change). -/
noncomputable abbrev remote (x : ℤ → H) : Submodule ℝ H := (⨅ t, past x t).topologicalClosure

/-- Cochrane (2023), Online Appendix p. 597 ("`w_{s,t+1} = s_{t+1} − E(s_{t+1}|s_t, s_{t−1}, …)`"):
the Wold innovation `e_t = x_t − P_{H_{t−1}} x_t`, the one-step-ahead linear forecast error. -/
noncomputable def innov [CompleteSpace H] (x : ℤ → H) (t : ℤ) : H :=
  x t - (past x (t - 1)).starProjection (x t)

/-- Cochrane (2023), Online Appendix p. 600: the Wold coefficients
`c_j = ⟪x_0, e_{−j}⟫ / ‖e_0‖²` (`0` when `e = 0`). -/
noncomputable def woldCoeff [CompleteSpace H] (x : ℤ → H) (j : ℕ) : ℝ :=
  ⟪x 0, innov x (-j)⟫ / ‖innov x 0‖ ^ 2

/-- Cochrane (2023), Online Appendix p. 600: the deterministic part `d_t = P_{H_{−∞}} x_t`. -/
noncomputable def detPart [CompleteSpace H] (x : ℤ → H) (t : ℤ) : H :=
  (remote x).starProjection (x t)

/-- Cochrane (2023), Online Appendix p. 600: `x` is deterministic (perfectly linearly predictable
from its own past) if `x_t ∈ H_{t−1}` for every `t`. -/
def Deterministic (x : ℤ → H) : Prop := ∀ t, x t ∈ past x (t - 1)

/-- Cochrane (2023), Online Appendix p. 600: `x` is regular (purely non-deterministic) if its
remote past is trivial, `H_{−∞} = 0`. -/
def Regular (x : ℤ → H) : Prop := remote x = ⊥

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_{t−k} ∈ H_t`. -/
theorem mem_past (x : ℤ → H) (t : ℤ) (k : ℕ) : x (t - k) ∈ past x t :=
  mem_pastSpan_self x t k

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_t ∈ H_t`. -/
theorem self_mem_past (x : ℤ → H) (t : ℤ) : x t ∈ past x t := by
  simpa using mem_past x t 0

/-- Cochrane (2023), Online Appendix p. 597 (tool): `H_t` grows with `t`. -/
theorem past_mono (x : ℤ → H) {t t' : ℤ} (h : t ≤ t') : past x t ≤ past x t' :=
  pastSpan_mono x h

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_s ∈ H_t` for `s ≤ t`. -/
theorem mem_past_of_le (x : ℤ → H) {s t : ℤ} (h : s ≤ t) : x s ∈ past x t :=
  past_mono x h (self_mem_past x s)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the remote past is closed, so it equals
`⋂_t H_t`. -/
theorem remote_eq (x : ℤ → H) : remote x = ⨅ t, past x t := by
  refine IsClosed.submodule_topologicalClosure_eq ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun t => Submodule.isClosed_topologicalClosure _

/-- Cochrane (2023), Online Appendix p. 600 (tool): `H_{−∞} ≤ H_t`. -/
theorem remote_le (x : ℤ → H) (t : ℤ) : remote x ≤ past x t := by
  rw [remote_eq]; exact iInf_le _ t

/-- Cochrane (2023), Online Appendix p. 600 (tool): membership in `H_{−∞}`. -/
theorem mem_remote_iff {x : ℤ → H} {z : H} : z ∈ remote x ↔ ∀ t, z ∈ past x t := by
  rw [remote_eq, Submodule.mem_iInf]

variable [CompleteSpace H]

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): `e_t ∈ H_t`. -/
theorem innov_mem (x : ℤ → H) (t : ℤ) : innov x t ∈ past x t :=
  Submodule.sub_mem _ (self_mem_past x t)
    (past_mono x (by omega) (Submodule.starProjection_apply_mem _ _))

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): `e_t ⟂ H_{t−1}` (the forecast error is
uncorrelated with everything linear in the past). -/
theorem innov_mem_orthogonal (x : ℤ → H) (t : ℤ) : innov x t ∈ (past x (t - 1))ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- Cochrane (2023), Online Appendix p. 597 (tool): `⟪e_t, y⟫ = 0` for `y ∈ H_{t−1}`. -/
theorem inner_innov_of_mem {x : ℤ → H} {t : ℤ} {y : H} (hy : y ∈ past x (t - 1)) :
    ⟪innov x t, y⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hy (innov_mem_orthogonal x t)

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations are orthogonal,
`⟪e_t, e_s⟫ = 0` for `s < t`. -/
theorem inner_innov_lt (x : ℤ → H) {s t : ℤ} (h : s < t) : ⟪innov x t, innov x s⟫ = 0 :=
  inner_innov_of_mem (past_mono x (by omega) (innov_mem x s))

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_t = e_t + P_{H_{t−1}} x_t`. -/
theorem x_eq_innov_add (x : ℤ → H) (t : ℤ) :
    x t = innov x t + (past x (t - 1)).starProjection (x t) := by
  rw [innov, sub_add_cancel]

/-- Cochrane (2023), Online Appendix p. 597 (tool): `e_t = 0` iff `x_t ∈ H_{t−1}`. -/
theorem innov_eq_zero_iff (x : ℤ → H) (t : ℤ) : innov x t = 0 ↔ x t ∈ past x (t - 1) := by
  rw [innov, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- Cochrane (2023), Online Appendix p. 600 (tool, the key step of Wold's proof):
`H_t = H_{t−1} ⊕ span{e_t}`, in the form: an element of `H_t` orthogonal to `e_t` lies in
`H_{t−1}`. -/
theorem mem_past_pred {x : ℤ → H} {t : ℤ} {y : H} (hy : y ∈ past x t)
    (he : ⟪innov x t, y⟫ = 0) : y ∈ past x (t - 1) := by
  set K := past x (t - 1) with hK
  -- `Q = P_{Kᗮ}` maps `H_t` into the line through `e_t`
  have hcl : IsClosed (((ℝ ∙ innov x t).comap (Kᗮ.starProjection : H →ₗ[ℝ] H) : Set H)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.closed_of_finiteDimensional (ℝ ∙ innov x t)).preimage
      Kᗮ.starProjection.continuous
  have hle : past x t ≤ (ℝ ∙ innov x t).comap (Kᗮ.starProjection : H →ₗ[ℝ] H) := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hcl
    rintro _ ⟨k, rfl⟩
    change Kᗮ.starProjection (x (t - k)) ∈ ℝ ∙ innov x t
    rw [Submodule.starProjection_orthogonal_val]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [show t - ((0 : ℕ) : ℤ) = t by simp]
      exact Submodule.mem_span_singleton_self (innov x t)
    · have hmem : x (t - k) ∈ K := mem_past_of_le x (by omega)
      rw [(Submodule.starProjection_eq_self_iff).mpr hmem, sub_self]
      exact Submodule.zero_mem _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hle hy)
  change a • innov x t = Kᗮ.starProjection y at ha
  rw [Submodule.starProjection_orthogonal_val] at ha
  have h1 : ⟪innov x t, y - K.starProjection y⟫ = 0 := by
    rw [inner_sub_right, he, inner_innov_of_mem (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  rw [← ha, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : a • innov x t = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h, zero_smul]
    · rw [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h), smul_zero]
  rw [h2, eq_comm, sub_eq_zero] at ha
  rw [ha]
  exact Submodule.starProjection_apply_mem _ _

/-! ### Stationarity: the shift -/

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (tool; stationarity): the shift `U` maps `H_t` into
`H_{t+1}`. -/
theorem map_past {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) {t : ℤ} {y : H}
    (hy : y ∈ past x t) : U y ∈ past x (t + 1) :=
  InvertibilityMeasure.map_pastSpan U.toContinuousLinearMap
    (fun k => by
      change U (x (t - k)) = x (t + 1 - k)
      rw [hU]; congr 1; ring) hy

/-- Cochrane (2023), Online Appendix p. 597 (tool): the shift commutes with the forecast,
`P_{H_t} x_{t+1} = U P_{H_{t−1}} x_t`. -/
theorem starProjection_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : (past x t).starProjection (x (t + 1)) =
      U ((past x (t - 1)).starProjection (x t)) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · have := map_past hU (Submodule.starProjection_apply_mem (past x (t - 1)) (x t))
    rwa [sub_add_cancel] at this
  · rw [← hU, ← map_sub]
    refine mem_orthogonal_pastSpan fun k => ?_
    rw [show t - (k : ℤ) = t - 1 - k + 1 by ring, ← hU, LinearIsometry.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero _ _ (mem_past x (t - 1) k)

/-- Cochrane (2023), Online Appendix p. 597, Wold (a) (stationarity of the innovations):
`e_{t+1} = U e_t`. -/
theorem innov_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    innov x (t + 1) = U (innov x t) := by
  have h : innov x (t + 1) = x (t + 1) - (past x t).starProjection (x (t + 1)) := by
    simp only [innov, add_sub_cancel_right]
  rw [h, starProjection_shift hU, ← hU, innov, map_sub]

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): inner products of two processes that the
same isometry shifts are shift invariant, `⟪y_{s+t}, z_{u+t}⟫ = ⟪y_s, z_u⟫`. -/
theorem inner_shift {U : H →ₗᵢ[ℝ] H} {y z : ℤ → H} (hy : ∀ t, U (y t) = y (t + 1))
    (hz : ∀ t, U (z t) = z (t + 1)) (s u t : ℤ) : ⟪y (s + t), z (u + t)⟫ = ⟪y s, z u⟫ := by
  induction t using Int.induction_on with
  | zero => simp
  | succ n ih => rw [← add_assoc, ← add_assoc, ← hy, ← hz, LinearIsometry.inner_map_map, ih]
  | pred n ih =>
    rw [← ih]
    have h1 : y (s + -(n : ℤ)) = U (y (s + (-(n : ℤ) - 1))) := by rw [hy]; congr 1; ring
    have h2 : z (u + -(n : ℤ)) = U (z (u + (-(n : ℤ) - 1))) := by rw [hz]; congr 1; ring
    rw [h1, h2, LinearIsometry.inner_map_map]

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations have constant norm. -/
theorem norm_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    ‖innov x t‖ = ‖innov x 0‖ := by
  have hs : ∀ τ, U (innov x τ) = innov x (τ + 1) := fun τ => (innov_shift hU τ).symm
  have h := inner_shift hs hs 0 0 t
  rw [zero_add, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations are white noise with
variance `‖e_0‖²` (orthogonal, constant norm), in the sense of `Invertibility.Hilbert`. -/
theorem innov_whiteNoise {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) := by
  intro t u
  rcases lt_trichotomy t u with h | h | h
  · rw [real_inner_comm, inner_innov_lt x h]
    simp [h.ne]
  · subst h
    simp [norm_innov hU]
  · rw [inner_innov_lt x h]
    simp [h.ne']

/-- Cochrane (2023), Online Appendix p. 600 (tool): if `e = 0` at one date it is `0` at all. -/
theorem innov_eq_zero_of {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 = 0) (t : ℤ) : innov x t = 0 := by
  rw [← norm_eq_zero, norm_innov hU, h0, norm_zero]

/-! ### The Wold coefficients and the regular part -/

/-- Cochrane (2023), Online Appendix p. 600 (tool): `c_j` does not depend on the date,
`⟪x_t, e_{t−j}⟫ = ⟪x_0, e_{−j}⟫`. -/
theorem inner_x_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : ⟪x t, innov x (t - j)⟫ = ⟪x 0, innov x (-j)⟫ := by
  have h := inner_shift hU (fun τ => (innov_shift hU τ).symm) 0 (-j) t
  rwa [zero_add, show -(j : ℤ) + t = t - j by ring] at h

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `c_j = ⟪x_t, e_{t−j}⟫ / ‖e_t‖²` at every
date `t`. -/
theorem woldCoeff_eq {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : woldCoeff x j = ⟪x t, innov x (t - j)⟫ / ‖innov x t‖ ^ 2 := by
  rw [woldCoeff, inner_x_innov hU, norm_innov hU t]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `⟪e_{t−j}, x_t⟫ = c_j ‖e‖²`. -/
theorem inner_innov_x {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : ⟪innov x (t - j), x t⟫ = woldCoeff x j * ‖innov x 0‖ ^ 2 := by
  by_cases h0 : innov x 0 = 0
  · rw [innov_eq_zero_of hU h0, inner_zero_left, h0, norm_zero]; ring
  · rw [woldCoeff, real_inner_comm, inner_x_innov hU, div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `c_0 = 1` when `e ≠ 0`. -/
theorem woldCoeff_zero {x : ℤ → H} (h0 : innov x 0 ≠ 0) : woldCoeff x 0 = 1 := by
  have h : ⟪x 0, innov x 0⟫ = ‖innov x 0‖ ^ 2 := by
    rw [x_eq_innov_add x 0, inner_add_left, real_inner_self_eq_norm_sq, real_inner_comm,
      inner_innov_of_mem (Submodule.starProjection_apply_mem _ _), add_zero]
  rw [woldCoeff, Nat.cast_zero, neg_zero, h, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))]

/-- Cochrane (2023), Online Appendix p. 600 (tool): the normalised innovations
`e_{t−j}/‖e‖`, `j ≥ 0`, are orthonormal. -/
theorem orthonormal_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 ≠ 0) (t : ℤ) :
    Orthonormal ℝ (fun j : ℕ => ‖innov x 0‖⁻¹ • innov x (t - j)) := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [orthonormal_iff_ite]
  intro i j
  rw [real_inner_smul_left, real_inner_smul_right, innov_whiteNoise hU]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    field_simp
  · have : t - (i : ℤ) ≠ t - j := by omega
    simp [this, hij]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `c_j e_{t−j} = ⟪ê_j, x_t⟫ ê_j` with
`ê_j = e_{t−j}/‖e‖`. -/
theorem woldCoeff_smul {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 ≠ 0) (t : ℤ) (j : ℕ) :
    woldCoeff x j • innov x (t - j) =
      ⟪‖innov x 0‖⁻¹ • innov x (t - j), x t⟫ • (‖innov x 0‖⁻¹ • innov x (t - j)) := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [real_inner_smul_left, inner_innov_x hU, smul_smul]
  congr 1
  field_simp

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): the series `∑_{j ≥ 0} c_j e_{t−j}`
converges in `H` (to the regular part `maProc c e t`). -/
theorem hasSum_wold {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (maProc (woldCoeff x) (innov x) t) := by
  refine Summable.hasSum ?_
  by_cases h0 : innov x 0 = 0
  · simp only [innov_eq_zero_of hU h0, smul_zero]
    exact summable_zero
  · have hv := orthonormal_innov hU h0 t
    have hs := (hv.orthogonalFamily.summable_iff_norm_sq_summable
      (fun j => ⟪‖innov x 0‖⁻¹ • innov x (t - j), x t⟫)).mpr (hv.inner_products_summable (x t))
    refine hs.congr fun j => ?_
    rw [woldCoeff_smul hU h0 t j, LinearIsometry.toSpanSingleton_apply]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `‖⟪ê_j, x_0⟫‖² = ‖e‖² c_j²`. -/
theorem norm_inner_sq {x : ℤ → H} (h0 : innov x 0 ≠ 0) (j : ℕ) :
    ‖⟪‖innov x 0‖⁻¹ • innov x (0 - j), x 0⟫‖ ^ 2 = ‖innov x 0‖ ^ 2 * woldCoeff x j ^ 2 := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [Real.norm_eq_abs, sq_abs, real_inner_smul_left, zero_sub, real_inner_comm, woldCoeff]
  field_simp

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `∑ c_j² < ∞`. -/
theorem summable_sq_woldCoeff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Summable (fun j => woldCoeff x j ^ 2) := by
  by_cases h0 : innov x 0 = 0
  · simp [woldCoeff, h0]
  · have hv := orthonormal_innov hU h0 0
    have hn : ‖innov x 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
    exact (summable_mul_left_iff hn).mp
      ((hv.inner_products_summable (x 0)).congr (norm_inner_sq h0))

/-- Cochrane (2023), Online Appendix p. 600, Wold (b) (Bessel's bound):
`‖e‖² ∑ c_j² ≤ ‖x_0‖²`. -/
theorem tsum_sq_woldCoeff_le {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2 ≤ ‖x 0‖ ^ 2 := by
  by_cases h0 : innov x 0 = 0
  · rw [h0, norm_zero]; simp
  · have hv := orthonormal_innov hU h0 0
    calc ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2
        = ∑' j : ℕ, ‖innov x 0‖ ^ 2 * woldCoeff x j ^ 2 := tsum_mul_left.symm
      _ = ∑' j : ℕ, ‖⟪‖innov x 0‖⁻¹ • innov x (0 - j), x 0⟫‖ ^ 2 :=
          tsum_congr fun j => (norm_inner_sq h0 j).symm
      _ ≤ ‖x 0‖ ^ 2 := hv.tsum_inner_products_le (x 0)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the regular part lies in `H_t`. -/
theorem regPart_mem {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    maProc (woldCoeff x) (innov x) t ∈ past x t :=
  hasSum_mem_pastSpan (hasSum_wold hU t) fun _ =>
    Submodule.smul_mem _ _ (past_mono x (by omega) (innov_mem x _))

/-- Cochrane (2023), Online Appendix p. 600 (tool): for any convergent series
`y = ∑ b_j e_{t−j}` in the innovations, `⟪e_{t−j}, y⟫ = b_j ‖e‖²`. -/
theorem inner_innov_hasSum {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    {t : ℤ} {b : ℕ → ℝ} {y : H} (h : HasSum (fun j : ℕ => b j • innov x (t - j)) y) (j : ℕ) :
    ⟪innov x (t - j), y⟫ = b j * ‖innov x 0‖ ^ 2 := by
  have hf : ∀ k : ℕ, ⟪innov x (t - j), b k • innov x (t - k)⟫ =
      if k = j then b j * ‖innov x 0‖ ^ 2 else 0 := by
    intro k
    rw [real_inner_smul_right, innov_whiteNoise hU]
    by_cases hk : k = j
    · subst hk; simp
    · have : t - (j : ℤ) ≠ t - k := by omega
      simp [this, hk]
  exact (inner_hasSum_right h (innov x (t - j))).unique ((hasSum_ite_eq j _).congr_fun hf)

/-- Cochrane (2023), Online Appendix p. 600 (tool): `e_s ⟂ H_{−∞}`. -/
theorem innov_mem_orthogonal_remote (x : ℤ → H) (s : ℤ) : innov x s ∈ (remote x)ᗮ :=
  Submodule.orthogonal_le (remote_le x (s - 1)) (innov_mem_orthogonal x s)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the regular part is orthogonal to `H_{−∞}`. -/
theorem regPart_mem_orthogonal_remote {x : ℤ → H} {U : H →ₗᵢ[ℝ] H}
    (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    maProc (woldCoeff x) (innov x) t ∈ (remote x)ᗮ :=
  (Submodule.isClosed_orthogonal _).mem_of_tendsto (hasSum_wold hU t).tendsto_sum_nat
    (Eventually.of_forall fun _ => Submodule.sum_mem _ fun _ _ =>
      Submodule.smul_mem _ _ (innov_mem_orthogonal_remote x _))

/-- Cochrane (2023), Online Appendix p. 600 (the key step): `x_t − ∑ c_j e_{t−j}` lies in every
`H_s`, i.e. in `H_{−∞}`. -/
theorem sub_regPart_mem_remote {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : x t - maProc (woldCoeff x) (innov x) t ∈ remote x := by
  have hd0 : x t - maProc (woldCoeff x) (innov x) t ∈ past x t :=
    Submodule.sub_mem _ (self_mem_past x t) (regPart_mem hU t)
  have horth : ∀ s, ⟪innov x s, x t - maProc (woldCoeff x) (innov x) t⟫ = 0 := by
    intro s
    rcases le_or_gt s t with hs | hs
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = t - j := ⟨(t - s).toNat, by omega⟩
      rw [inner_sub_right, inner_innov_x hU, inner_innov_hasSum hU (hasSum_wold hU t), sub_self]
    · exact inner_innov_of_mem (past_mono x (by omega) hd0)
  have hmem : ∀ n : ℕ, x t - maProc (woldCoeff x) (innov x) t ∈ past x (t - n) := by
    intro n
    induction n with
    | zero => simpa using hd0
    | succ n ih =>
      have := mem_past_pred ih (horth _)
      rwa [show t - (n : ℤ) - 1 = t - ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this
  rw [mem_remote_iff]
  intro s
  rcases le_or_gt s t with hs | hs
  · have := hmem (t - s).toNat
    rwa [show t - ((t - s).toNat : ℤ) = s by omega] at this
  · exact past_mono x hs.le hd0

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): the deterministic part is
`d_t = P_{H_{−∞}} x_t = x_t − ∑ c_j e_{t−j}`. -/
theorem detPart_eq {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    detPart x t = x t - maProc (woldCoeff x) (innov x) t :=
  Submodule.eq_starProjection_of_mem_orthogonal (sub_regPart_mem_remote hU t)
    (by rw [sub_sub_cancel]; exact regPart_mem_orthogonal_remote hU t)

/-- Cochrane (2023), Online Appendix p. 600 (tool): `x_t = u_t + d_t`. -/
theorem x_eq_regPart_add_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : x t = maProc (woldCoeff x) (innov x) t + detPart x t := by
  rw [detPart_eq hU, add_sub_cancel]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `d_t ∈ H_{−∞}`. -/
theorem detPart_mem_remote (x : ℤ → H) (t : ℤ) : detPart x t ∈ remote x :=
  Submodule.starProjection_apply_mem _ _

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition theorem** (the book
invokes it; here proved): let `x` be weakly stationary in a real Hilbert space, `U x_t = x_{t+1}`
for a linear isometry `U`; let `e_t = x_t − P_{H_{t−1}} x_t`.
(a) `e_t ∈ H_t`, `e_t ⟂ H_{t−1}`, and `e` is white noise (orthogonal, constant norm);
(b) `∑ c_j² < ∞` (indeed `‖e‖² ∑ c_j² ≤ ‖x_0‖²`), `c_0 = 1` if `e ≠ 0`,
`c_j = ⟪x_t, e_{t−j}⟫/‖e_t‖²` at every date, and `x_t = ∑_{j ≥ 0} c_j e_{t−j} + d_t` with the
series converging in `H`, `d_t = P_{H_{−∞}} x_t ∈ H_{−∞}` and `d ⟂ e`. -/
theorem wold_decomposition {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    (∀ t, innov x t ∈ past x t) ∧ (∀ t, innov x t ∈ (past x (t - 1))ᗮ) ∧
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) ∧
    Summable (fun j => woldCoeff x j ^ 2) ∧
    ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2 ≤ ‖x 0‖ ^ 2 ∧
    (innov x 0 ≠ 0 → woldCoeff x 0 = 1) ∧
    (∀ t (j : ℕ), woldCoeff x j = ⟪x t, innov x (t - j)⟫ / ‖innov x t‖ ^ 2) ∧
    (∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t - detPart x t)) ∧
    (∀ t, detPart x t ∈ remote x) ∧
    (∀ s t, ⟪detPart x s, innov x t⟫ = 0) := by
  refine ⟨innov_mem x, innov_mem_orthogonal x, innov_whiteNoise hU, summable_sq_woldCoeff hU,
    tsum_sq_woldCoeff_le hU, woldCoeff_zero, woldCoeff_eq hU, fun t => ?_, detPart_mem_remote x,
    fun s t => ?_⟩
  · rw [detPart_eq hU, sub_sub_cancel]; exact hasSum_wold hU t
  · exact Submodule.inner_right_of_mem_orthogonal (detPart_mem_remote x s)
      (innov_mem_orthogonal_remote x t)

/-! ### Uniqueness -/

/-- Cochrane (2023), Online Appendix pp. 597 and 600, Wold (c), **uniqueness**: if
`x_t = ∑_{j ≥ 0} b_j w_{t−j} + z_t` (converging in `H`) with `w_t ∈ H_t`, `w_t ⟂ H_{t−1}`,
`b_0 = 1` and `z_t ∈ H_{−∞}`, then `w` is the Wold innovation, `z` the deterministic part, and
(when `e ≠ 0`) `b` the Wold coefficients. This is why "an autoregression recovers the Wold
representation": any one-sided representation in forecast errors is the Wold one. -/
theorem wold_unique {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) {w z : ℤ → H}
    {b : ℕ → ℝ} (hw : ∀ t, w t ∈ past x t) (hwo : ∀ t, w t ∈ (past x (t - 1))ᗮ)
    (hb0 : b 0 = 1) (hz : ∀ t, z t ∈ remote x)
    (hsum : ∀ t, HasSum (fun j : ℕ => b j • w (t - j)) (x t - z t)) :
    (∀ t, w t = innov x t) ∧ (∀ t, z t = detPart x t) ∧ (innov x 0 ≠ 0 → b = woldCoeff x) := by
  have hwe : ∀ t, w t = innov x t := by
    intro t
    have h1 := (hasSum_nat_add_iff' 1).mpr (hsum t)
    simp only [Finset.range_one, Finset.sum_singleton, hb0, one_smul, Nat.cast_zero,
      sub_zero] at h1
    have hmem : x t - z t - w t ∈ past x (t - 1) :=
      hasSum_mem_pastSpan h1 fun j => Submodule.smul_mem _ _ (past_mono x (by omega) (hw _))
    have hP : (past x (t - 1)).starProjection (x t) = x t - w t := by
      refine Submodule.eq_starProjection_of_mem_orthogonal ?_
        (by rw [sub_sub_cancel]; exact hwo t)
      have := Submodule.add_mem _ hmem (remote_le x (t - 1) (hz t))
      rwa [sub_right_comm, sub_add_cancel] at this
    rw [innov, hP, sub_sub_cancel]
  obtain rfl : w = innov x := funext hwe
  have hb : innov x 0 ≠ 0 → b = woldCoeff x := by
    intro h0
    funext j
    have h1 := inner_innov_hasSum hU (hsum 0) j
    have h2 : ⟪innov x (0 - j), z 0⟫ = 0 :=
      inner_innov_of_mem (remote_le x _ (hz 0))
    rw [inner_sub_right, h2, sub_zero, inner_innov_x hU] at h1
    exact (mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)) h1).symm
  refine ⟨hwe, fun t => ?_, hb⟩
  have hf : (fun j : ℕ => b j • innov x (t - j)) =
      fun j : ℕ => woldCoeff x j • innov x (t - j) := by
    funext j
    by_cases h0 : innov x 0 = 0
    · rw [innov_eq_zero_of hU h0, smul_zero, smul_zero]
    · rw [hb h0]
  have h := (hsum t).unique (hf ▸ (hasSum_wold hU t))
  rw [detPart_eq hU, ← h, sub_sub_cancel]

/-! ### The regular/deterministic dichotomy -/

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is deterministic iff its innovation
vanishes. -/
theorem deterministic_iff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Deterministic x ↔ innov x 0 = 0 :=
  ⟨fun h => (innov_eq_zero_iff x 0).mpr (h 0),
    fun h t => (innov_eq_zero_iff x t).mp (innov_eq_zero_of hU h t)⟩

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is deterministic iff it equals its
deterministic part. -/
theorem deterministic_iff_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Deterministic x ↔ ∀ t, detPart x t = x t := by
  rw [deterministic_iff hU]
  constructor
  · intro h t
    rw [detPart_eq hU]
    simp [maProc, innov_eq_zero_of hU h]
  · intro h
    refine (innov_eq_zero_iff x 0).mpr ?_
    rw [← h 0]
    exact remote_le x _ (detPart_mem_remote x 0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is regular (`H_{−∞} = 0`) iff its
deterministic part vanishes. -/
theorem regular_iff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular x ↔ ∀ t, detPart x t = 0 := by
  constructor
  · intro h t
    have hm := detPart_mem_remote x t
    rw [Regular] at h
    rwa [h, Submodule.mem_bot] at hm
  · intro h
    rw [Regular, Submodule.eq_bot_iff]
    intro z hz
    have hx : ∀ s, ⟪z, x s⟫ = 0 := by
      intro s
      rw [x_eq_regPart_add_detPart hU s, h s, add_zero]
      exact Submodule.inner_right_of_mem_orthogonal hz (regPart_mem_orthogonal_remote hU s)
    have h0 : z ∈ (past x 0)ᗮ := mem_orthogonal_pastSpan fun k => hx _
    exact inner_self_eq_zero.mp
      (Submodule.inner_right_of_mem_orthogonal (mem_remote_iff.mp hz 0) h0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is regular iff it is the moving
average of its innovations, `x_t = ∑ c_j e_{t−j}`. -/
theorem regular_iff_hasSum {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular x ↔ ∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t) := by
  rw [regular_iff hU]
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · have := hasSum_wold hU t
    rwa [← sub_zero (x t), ← h, detPart_eq hU, sub_sub_cancel]
  · rw [detPart_eq hU, (hasSum_wold hU t).unique h, sub_self]

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 600 (tool): a closed subspace containing
`y_t, y_{t−1}, …` contains their closed span. -/
theorem past_le_of_mem {y : ℤ → H} {t : ℤ} {K : Submodule ℝ H} (hK : IsClosed (K : Set H))
    (h : ∀ k : ℕ, y (t - k) ∈ K) : past y t ≤ K :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact h k)) hK

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): the remote past is the closed span of the
deterministic part's past at any date, `H_{−∞} = closure span{d_t, d_{t−1}, …}`. -/
theorem remote_eq_past_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : remote x = past (detPart x) t := by
  have hle : past (detPart x) t ≤ remote x :=
    past_le_of_mem (Submodule.isClosed_topologicalClosure _)
      fun k => detPart_mem_remote x _
  refine le_antisymm (fun h hh => ?_) hle
  set D := past (detPart x) t
  set k := h - D.starProjection h with hk
  have hkr : k ∈ remote x :=
    Submodule.sub_mem _ hh (hle (Submodule.starProjection_apply_mem _ _))
  have hkD : k ∈ Dᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hkx : k ∈ (past x t)ᗮ := by
    refine mem_orthogonal_pastSpan fun j => ?_
    rw [x_eq_regPart_add_detPart hU, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hkr (regPart_mem_orthogonal_remote hU _),
      zero_add]
    exact Submodule.inner_left_of_mem_orthogonal (mem_past (detPart x) t j) hkD
  have hk0 : k = 0 := inner_self_eq_zero.mp
    (Submodule.inner_right_of_mem_orthogonal (remote_le x t hkr) hkx)
  rw [hk, sub_eq_zero] at hk0
  rw [hk0]
  exact Submodule.starProjection_apply_mem _ _

/-- Cochrane (2023), Online Appendix p. 600, **Wold (d), the dichotomy**: the regular part
`u_t = ∑ c_j e_{t−j}` is regular, the deterministic part `d` is deterministic, `H_{−∞}` is
spanned by `d`'s past, `u` and `d` are uncorrelated at all dates, and both are stationary (shifted
by the same `U`). -/
theorem wold_dichotomy {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular (maProc (woldCoeff x) (innov x)) ∧ Deterministic (detPart x) ∧
    (∀ t, remote x = past (detPart x) t) ∧
    (∀ s t, ⟪maProc (woldCoeff x) (innov x) s, detPart x t⟫ = 0) ∧
    (∀ t, U (maProc (woldCoeff x) (innov x) t) = maProc (woldCoeff x) (innov x) (t + 1)) ∧
    (∀ t, U (detPart x t) = detPart x (t + 1)) := by
  set u := maProc (woldCoeff x) (innov x) with hu
  have hUu : ∀ t, U (u t) = u (t + 1) := by
    intro t
    have h := (hasSum_wold hU t).mapL U.toContinuousLinearMap
    refine h.unique ((hasSum_wold hU (t + 1)).congr_fun fun j => ?_)
    change U (woldCoeff x j • innov x (t - j)) = woldCoeff x j • innov x (t + 1 - j)
    rw [map_smul, ← innov_shift hU, show t - (j : ℤ) + 1 = t + 1 - j by ring]
  refine ⟨?_, fun t => ?_, remote_eq_past_detPart hU, fun s t => ?_, hUu, fun t => ?_⟩
  · -- the regular part is regular
    rw [Regular, Submodule.eq_bot_iff]
    intro z hz
    have hle : ∀ s, past u s ≤ past x s := fun s =>
      past_le_of_mem (Submodule.isClosed_topologicalClosure _)
        fun k => past_mono x (by omega) (regPart_mem hU _)
    have he : ∀ s, ⟪z, innov x s⟫ = 0 := fun s => by
      rw [real_inner_comm]
      exact inner_innov_of_mem (hle _ (mem_remote_iff.mp hz (s - 1)))
    have hzu : ∀ r, ⟪z, u r⟫ = 0 := fun r => by
      refine (inner_hasSum_right (hasSum_wold hU r) z).unique ?_
      convert hasSum_zero with j
      rw [real_inner_smul_right, he, mul_zero]
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal
      (mem_remote_iff.mp hz 0) (mem_orthogonal_pastSpan fun k => hzu _))
  · rw [← remote_eq_past_detPart hU]
    exact detPart_mem_remote x t
  · exact Submodule.inner_left_of_mem_orthogonal (detPart_mem_remote x t)
      (regPart_mem_orthogonal_remote hU s)
  · rw [detPart_eq hU, detPart_eq hU, map_sub, hU, ← hu, hUu]

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): a process both regular and deterministic
is zero. -/
theorem eq_zero_of_regular_deterministic {x : ℤ → H} {U : H →ₗᵢ[ℝ] H}
    (hU : ∀ t, U (x t) = x (t + 1)) (hr : Regular x) (hd : Deterministic x) (t : ℤ) :
    x t = 0 := by
  rw [← (deterministic_iff_detPart hU).mp hd t, (regular_iff hU).mp hr t]

/-! ### Stationarity: covariance stationarity is the same as a shift isometry -/

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (stationarity): the orbit of a linear isometry is
covariance stationary, `⟪x_s, x_u⟫ = γ(s − u)` with `γ(k) = ⟪x_k, x_0⟫`. -/
theorem stationary_of_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (s u : ℤ) : ⟪x s, x u⟫ = ⟪x (s - u), x 0⟫ := by
  have := inner_shift hU hU (s - u) 0 u
  rwa [sub_add_cancel, zero_add] at this

/-- Cochrane (2023), Online Appendix p. 597 (stationarity): a covariance-stationary sequence
(`⟪x_s, x_u⟫` depends only on `s − u`) is the orbit of a linear isometry `U` of `H`,
`U x_t = x_{t+1}`: `U` is the isometric extension of `∑ c_t x_t ↦ ∑ c_t x_{t+1}` to the closed
span `K` of the `x_t`, and the identity on `Kᗮ`. -/
theorem exists_shift_of_stationary {x : ℤ → H} {γ : ℤ → ℝ}
    (hγ : ∀ s u, ⟪x s, x u⟫ = γ (s - u)) : ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (x t) = x (t + 1) := by
  classical
  set K : Submodule ℝ H := (Submodule.span ℝ (Set.range x)).topologicalClosure with hK
  set L : (ℤ →₀ ℝ) →ₗ[ℝ] H := Finsupp.linearCombination ℝ x with hL
  set L' : (ℤ →₀ ℝ) →ₗ[ℝ] H := Finsupp.linearCombination ℝ (fun t => x (t + 1)) with hL'
  have hspan : ∀ c, L c ∈ Submodule.span ℝ (Set.range x) := fun c => by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c
  have hspan' : ∀ c, L' c ∈ Submodule.span ℝ (Set.range x) := fun c => by
    have : L' c ∈ Submodule.span ℝ (Set.range fun t => x (t + 1)) := by
      rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t + 1, rfl⟩) this
  let e : (ℤ →₀ ℝ) →ₗ[ℝ] K :=
    L.codRestrict K fun c => Submodule.le_topologicalClosure _ (hspan c)
  have hinner : ∀ c d : ℤ →₀ ℝ, ⟪L' c, L' d⟫ = ⟪L c, L d⟫ := by
    intro c d
    simp only [hL, hL', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, hγ, add_sub_add_right_eq_sub]
  have hnorm : ∀ c, ‖L' c‖ = ‖e c‖ := by
    intro c
    change ‖L' c‖ = ‖L c‖
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinner]
  have hdense : DenseRange e := by
    refine Subtype.dense_iff.mpr ?_
    rw [← Set.range_comp]
    change (K : Set H) ⊆ closure (Set.range (L : (ℤ →₀ ℝ) → H))
    rw [← LinearMap.coe_range, hL, Finsupp.range_linearCombination, hK,
      Submodule.topologicalClosure_coe]
  let V : K →ₗᵢ[ℝ] H := L'.extendOfIsometry hdense hnorm
  have hVe : ∀ c, V (e c) = L' c := fun c => LinearMap.extendOfIsometry_eq L' hdense hnorm c
  have hVK : ∀ y : K, V y ∈ K := by
    intro y
    refine hdense.induction_on y ?_ fun c => ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage V.continuous
    · rw [hVe]; exact Submodule.le_topologicalClosure _ (hspan' c)
  let T : H →ₗ[ℝ] H := V.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : H →ₗ[ℝ] K) +
    (LinearMap.id - (K.starProjection : H →ₗ[ℝ] H))
  have hT : ∀ y, T y = V (K.orthogonalProjectionOnto y) + (y - K.starProjection y) :=
    fun y => rfl
  have hPy : ∀ y, ((K.orthogonalProjectionOnto y : K) : H) = K.starProjection y := fun y => rfl
  refine ⟨⟨T, fun y => ?_⟩, fun t => ?_⟩
  · rw [hT]
    have h1 : ⟪V (K.orthogonalProjectionOnto y), y - K.starProjection y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hVK _)
        (Submodule.sub_starProjection_mem_orthogonal y)
    have h2 : ⟪K.starProjection y, y - K.starProjection y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
        (Submodule.sub_starProjection_mem_orthogonal y)
    have e1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h1
    have e2 := norm_add_sq_eq_norm_sq_add_norm_sq_real h2
    rw [add_sub_cancel] at e2
    have e3 : ‖V (K.orthogonalProjectionOnto y)‖ = ‖K.starProjection y‖ := by
      rw [LinearIsometry.norm_map]; rfl
    rw [e3, ← e2] at e1
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp e1
  · have hxK : x t ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)
    change T (x t) = x (t + 1)
    rw [hT, (Submodule.starProjection_eq_self_iff).mpr hxK, sub_self, add_zero]
    have hP : K.orthogonalProjectionOnto (x t) = e (Finsupp.single t 1) := by
      apply Subtype.ext
      rw [hPy, (Submodule.starProjection_eq_self_iff).mpr hxK]
      change x t = L (Finsupp.single t 1)
      rw [hL, Finsupp.linearCombination_single, one_smul]
    rw [hP, hVe, hL', Finsupp.linearCombination_single, one_smul]

/-- Cochrane (2023), Online Appendix p. 597 (stationarity): the two notions of weak
stationarity agree — `⟪x_s, x_u⟫` depends only on `s − u` iff `x` is the orbit of a linear
isometry of `H`. -/
theorem stationary_iff_exists_shift (x : ℤ → H) :
    (∃ γ : ℤ → ℝ, ∀ s u, ⟪x s, x u⟫ = γ (s - u)) ↔
      ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (x t) = x (t + 1) :=
  ⟨fun ⟨_, hγ⟩ => exists_shift_of_stationary hγ,
    fun ⟨_, hU⟩ => ⟨fun k => ⟪x k, x 0⟫, stationary_of_shift hU⟩⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition for a
covariance-stationary sequence**: innovations are white noise, `∑ c_j² < ∞`, `c_0 = 1` if
`e ≠ 0`, `x_t = ∑ c_j e_{t−j} + d_t` in `H` with `d_t ∈ H_{−∞}`, `d ⟂ e`, the regular part is
regular and the deterministic part deterministic. -/
theorem wold_of_stationary {x : ℤ → H} {γ : ℤ → ℝ} (hγ : ∀ s u, ⟪x s, x u⟫ = γ (s - u)) :
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) ∧ Summable (fun j => woldCoeff x j ^ 2) ∧
    (innov x 0 ≠ 0 → woldCoeff x 0 = 1) ∧
    (∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t - detPart x t)) ∧
    (∀ t, detPart x t ∈ remote x) ∧ (∀ s t, ⟪detPart x s, innov x t⟫ = 0) ∧
    Regular (maProc (woldCoeff x) (innov x)) ∧ Deterministic (detPart x) := by
  obtain ⟨U, hU⟩ := exists_shift_of_stationary hγ
  obtain ⟨-, -, h1, h2, -, h3, -, h4, h5, h6⟩ := wold_decomposition hU
  obtain ⟨h7, h8, -⟩ := wold_dichotomy hU
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### Neither part can be dropped: a mixed process -/

/-- Cochrane (2023), Online Appendix p. 600, Wold (d), **a mixed example**: white noise plus a
fixed vector orthogonal to it, `x_t = ε_t + v` with `v ≠ 0`, `v ⟂ ε`. Its Wold innovation is
`ε`, its coefficients are `c = (1, 0, 0, …)`, its deterministic part is `d_t = v` (a mean, in
`L²`), and it is neither regular nor deterministic. -/
theorem mixed_example {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {v : H}
    (hv : v ≠ 0) (hve : ∀ t, ⟪e t, v⟫ = 0) {x : ℤ → H} (hx : ∀ t, x t = e t + v) :
    (∀ t, innov x t = e t) ∧ (∀ t, detPart x t = v) ∧
    (∀ j, woldCoeff x j = if j = 0 then 1 else 0) ∧ ¬ Regular x ∧ ¬ Deterministic x := by
  have hγ : ∀ s u, ⟪x s, x u⟫ = (fun k : ℤ => (if k = 0 then σ2 else 0) + ‖v‖ ^ 2) (s - u) := by
    intro s u
    rw [hx, hx, inner_add_left, inner_add_right, inner_add_right, he, hve, real_inner_comm,
      hve, real_inner_self_eq_norm_sq]
    simp only [sub_eq_zero, add_zero, zero_add]
  obtain ⟨U, hU⟩ := exists_shift_of_stationary (x := x)
    (γ := fun k : ℤ => (if k = 0 then σ2 else 0) + ‖v‖ ^ 2) hγ
  -- `v` lies in every `H_s` (Cesàro means of the past)
  have hvmem : ∀ s, v ∈ past x s := by
    intro s
    set y : ℕ → H := fun n => ((n : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (n + 1), x (s - m) with hy
    have hymem : ∀ n, y n ∈ past x s := fun n =>
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ => mem_past x s m)
    have hdiff : ∀ n, y n - v =
        ((n : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (n + 1), (1 : ℝ) • e (s - m) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp only [hy, hx, one_smul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      rw [smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ hn, one_smul, add_sub_cancel_right]
    have hnorm : ∀ n, ‖y n - v‖ ^ 2 = σ2 / ((n : ℝ) + 1) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [hdiff, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
        InvertibilityMeasure.inner_sum_e he (fun _ => 1) (fun m => s - m)
          (fun m m' h => by simpa using h) (n + 1)]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      field_simp
    have hlim : Tendsto y atTop (𝓝 v) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n : ℕ => σ2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat σ2 |>.comp (tendsto_add_atTop_nat 1) |>.congr
          fun n => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
      (Eventually.of_forall hymem)
  have hw : ∀ t, e t ∈ past x t := fun t => by
    have : e t = x t - v := by rw [hx, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (self_mem_past x t) (hvmem t)
  have hwo : ∀ t, e t ∈ (past x (t - 1))ᗮ := fun t => mem_orthogonal_pastSpan fun k => by
    have : t ≠ t - 1 - k := by omega
    rw [hx, inner_add_right, he, hve]
    simp [this]
  have hsum : ∀ t, HasSum (fun j : ℕ => (if j = 0 then (1 : ℝ) else 0) • e (t - j)) (x t - v) := by
    intro t
    rw [hx, add_sub_cancel_right]
    convert hasSum_single (f := fun j : ℕ => (if j = 0 then (1 : ℝ) else 0) • e (t - j)) 0
      (fun j hj => by simp [hj]) using 1
    simp
  obtain ⟨h1, h2, h3⟩ := wold_unique hU hw hwo (by simp) (fun _ => mem_remote_iff.mpr hvmem)
    hsum
  have h0 : innov x 0 ≠ 0 := by
    rw [← h1 0]
    intro h
    have := he 0 0
    rw [h, inner_zero_left] at this
    simp only [↓reduceIte] at this
    exact hσ this.symm
  refine ⟨fun t => (h1 t).symm, fun t => (h2 t).symm, fun j => (congrFun (h3 h0) j).symm,
    fun hr => hv ?_, fun hd => h0 ((deterministic_iff hU).mp hd)⟩
  rw [h2 0]
  exact (regular_iff hU).mp hr 0

/-! ### Links: moving averages, and the factorised Wold statement -/

/-- Cochrane (2023), Online Appendix p. 597 (tool): an absolutely summable moving average in white
noise with `σ² ≠ 0` is stationary — the shift of the shocks shifts it. -/
theorem maProc_shift {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ}
    (ha : Summable (fun k => |a k|)) :
    ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (maProc a e t) = maProc a e (t + 1) := by
  obtain ⟨U, hU⟩ := InvertibilityMeasure.exists_shift he hσ
  refine ⟨U.toLinearIsometry, fun t => ?_⟩
  have h := (maProc_hasSum he ha t).mapL U.toLinearIsometry.toContinuousLinearMap
  refine h.unique ((maProc_hasSum he ha (t + 1)).congr_fun fun k => ?_)
  change U (a k • e (t - k)) = a k • e (t + 1 - k)
  rw [map_smul, hU, show t - (k : ℤ) + 1 = t + 1 - k by ring]

/-- Cochrane (2023), Online Appendix p. 597 ("the Wold representation, which has an invertible
moving average"): every absolutely summable moving average `s_t = ∑ a_k e_{t−k}` in white noise is
regular — its remote past is `0`, so its deterministic part vanishes and it is the moving average
of its own Wold innovations. -/
theorem maProc_regular {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {a : ℕ → ℝ}
    (ha : Summable (fun k => |a k|)) : Regular (maProc a e) := by
  rw [Regular, Submodule.eq_bot_iff]
  intro z hz
  have he0 : ∀ r, ⟪z, e r⟫ = 0 := by
    intro r
    have horth : e r ∈ (past (maProc a e) (r - 1))ᗮ := mem_orthogonal_pastSpan fun k => by
      rw [InvertibilityMeasure.inner_e_maProc_int he ha]
      have : ¬ r ≤ r - 1 - k := by omega
      simp only [this, ↓reduceIte]
    exact Submodule.inner_right_of_mem_orthogonal (mem_remote_iff.mp hz (r - 1)) horth
  have hzs : ∀ q, ⟪z, maProc a e q⟫ = 0 := fun q => by
    refine (inner_hasSum_right (maProc_hasSum he ha q) z).unique ?_
    convert hasSum_zero with k
    rw [real_inner_smul_right, he0, mul_zero]
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal
    (mem_remote_iff.mp hz 0) (mem_orthogonal_pastSpan fun k => hzs _))

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the factorised statement is an instance of
Wold**: for `s_t = a(L)e_t` with `a(L) = (1 − θL)g(L)`, `|θ| > 1`, `g₀ = 1`, `g` invertible
(`InvertibilityMeasure.wold_factor`), the abstract Wold innovation of `s` is the autoregression
error `w_t = ∑ θ⁻ᵏ(e_{t−k} − θe_{t−k−1})`, the abstract Wold coefficients are the fitted
`ã = (1 − θ⁻¹L)g` (the flipped root), `‖w‖² = θ²σ²`, the deterministic part is `0` and `s` is
regular. -/
theorem wold_factor_is_wold {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {θ : ℝ}
    (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1)
    (hrec : Invertibility.Recoverable g) :
    (∀ t, innov (maProc (InvertibilityMeasure.factorCoeff θ g) e) t =
      woldInnov θ (maOne θ e) t) ∧
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff θ g) e) =
      InvertibilityMeasure.factorCoeff θ⁻¹ g ∧
    (∀ t, detPart (maProc (InvertibilityMeasure.factorCoeff θ g) e) t = 0) ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff θ g) e) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff θ g) e) 0‖ ^ 2 = θ ^ 2 * σ2 := by
  set s := maProc (InvertibilityMeasure.factorCoeff θ g) e with hs
  obtain ⟨U, hU⟩ := maProc_shift he hσ (InvertibilityMeasure.summable_factorCoeff θ hg)
  have hW := InvertibilityMeasure.wold_factor he hσ hθ hg hg0 hrec
  have hw : ∀ t, innov s t = woldInnov θ (maOne θ e) t := by
    intro t
    have hP : (past s (t - 1)).starProjection (s t) = s t - woldInnov θ (maOne θ e) t :=
      (hW t).1
    rw [innov, hP, sub_sub_cancel]
  have hn : ‖innov s 0‖ ^ 2 = θ ^ 2 * σ2 := by
    rw [hw, ← real_inner_self_eq_norm_sq]
    exact (hW 0).2.1
  have h0 : innov s 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    have hθ0 : θ ≠ 0 := by intro h'; rw [h', abs_zero] at hθ; linarith
    exact mul_ne_zero (pow_ne_zero 2 hθ0) hσ (by rw [← hn]; ring)
  obtain ⟨-, h2, h3⟩ := wold_unique hU (w := woldInnov θ (maOne θ e))
    (b := InvertibilityMeasure.factorCoeff θ⁻¹ g) (z := fun _ => 0)
    (fun t => by rw [← hw t]; exact innov_mem s t)
    (fun t => by rw [← hw t]; exact innov_mem_orthogonal s t) hg0
    (fun _ => Submodule.zero_mem _) (fun t => by rw [sub_zero]; exact (hW t).2.2.2.1)
  exact ⟨hw, (h3 h0).symm, fun t => (h2 t).symm, (regular_iff hU).mpr fun t => (h2 t).symm, hn⟩

/-- Cochrane (2023), Online Appendix p. 597 ("the Wold representation, which has an invertible
moving average"), **correction**: the Wold moving average is fundamental (`e_t ∈ H_t`) but need not
be invertible. For `s_t = e_t − ρe_{t−1}` with `ρ = ±1`, the Wold innovation is the structural
shock, the Wold coefficients are `(1, −ρ, 0, …)`, so the Wold polynomial vanishes at `ρ` on the
unit circle, and no absolutely summable autoregression of current and past `s` converges to the
Wold innovation. -/
theorem wold_unit_root {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ : ℝ}
    (hρ : ρ ^ 2 = 1) :
    (∀ t, innov (maProc (Invertibility.armaCoeff 0 ρ) e) t = e t) ∧
    woldCoeff (maProc (Invertibility.armaCoeff 0 ρ) e) = Invertibility.armaCoeff 0 ρ ∧
    Regular (maProc (Invertibility.armaCoeff 0 ρ) e) ∧
    Innovations.gen (woldCoeff (maProc (Invertibility.armaCoeff 0 ρ) e)) ρ = 0 ∧ |ρ| = 1 ∧
    ∀ t, ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (Invertibility.armaCoeff 0 ρ) e (t - k))
        (innov (maProc (Invertibility.armaCoeff 0 ρ) e) t) := by
  set s := maProc (Invertibility.armaCoeff 0 ρ) e with hs
  have ha := Invertibility.summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) ρ
  obtain ⟨U, hU⟩ := maProc_shift he hσ ha
  have habs : |ρ| = 1 := by
    have : |ρ| ^ 2 = 1 := by rw [sq_abs, hρ]
    nlinarith [abs_nonneg ρ]
  have hroot : Innovations.gen (Invertibility.armaCoeff 0 ρ) ρ = 0 := by
    rw [Invertibility.ma1_aRho]; nlinarith
  have hwo : ∀ t, e t ∈ (past s (t - 1))ᗮ := fun t => mem_orthogonal_pastSpan fun k => by
    rw [InvertibilityMeasure.inner_e_maProc_int he ha]
    have : ¬ t ≤ t - 1 - k := by omega
    simp only [this, ↓reduceIte]
  obtain ⟨h1, h2, h3⟩ := wold_unique hU (w := e) (b := Invertibility.armaCoeff 0 ρ)
    (z := fun _ => 0) (fun t => (InvertibilityMeasure.mem_pastSpan_unit_root he hρ t).2) hwo
    rfl (fun _ => Submodule.zero_mem _)
    (fun t => by rw [sub_zero]; exact maProc_hasSum he ha t)
  have h0 : innov s 0 ≠ 0 := by
    rw [← h1 0]
    intro h
    have := he 0 0
    rw [h, inner_zero_left] at this
    simp only [↓reduceIte] at this
    exact hσ this.symm
  have hc := (h3 h0).symm
  have hroot' : Innovations.gen (woldCoeff s) ρ = 0 := by rw [hc]; exact hroot
  refine ⟨fun t => (h1 t).symm, hc, (regular_iff hU).mpr fun t => (h2 t).symm, hroot', habs,
    fun t => ?_⟩
  rw [← h1 t]
  exact InvertibilityMeasure.not_filter_of_aRho_eq_zero he hσ ha habs.le hroot t

/-! ### The i.i.d. economy in `L²(ν^ℕ)` -/

namespace IIDEconomy

open MeasureTheory ProbabilityTheory
open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2

/-- Cochrane (2023), Online Appendix p. 600 (the deterministic part as a mean): the constant
random variable `1` in `L²(ν^ℕ)`. -/
noncomputable def oneL2 (ν : ProbabilityMeasure ℝ) : Lp ℝ 2 (iidSystem ν).μ :=
  (memLp_const (1 : ℝ)).toLp _

/-- Cochrane (2023), Online Appendix p. 600 (tool): `E[1 · 1] = 1`. -/
theorem inner_oneL2 (ν : ProbabilityMeasure ℝ) : ⟪oneL2 ν, oneL2 ν⟫ = 1 := by
  rw [L2.inner_def]
  have h2 : (oneL2 ν : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hc : (fun ω => ⟪(oneL2 ν : (ℕ → ℝ) → ℝ) ω, (oneL2 ν : (ℕ → ℝ) → ℝ) ω⟫)
      =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := by
    filter_upwards [h2] with ω e2
    rw [e2]
    simp
  rw [integral_congr_ae hc]
  simp

/-- Cochrane (2023), Online Appendix p. 600 (tool): `1 ≠ 0` in `L²(ν^ℕ)`. -/
theorem oneL2_ne_zero (ν : ProbabilityMeasure ℝ) : oneL2 ν ≠ 0 := by
  intro h
  have := inner_oneL2 ν
  rw [h, inner_zero_left] at this
  exact zero_ne_one this

/-- Cochrane (2023), Online Appendix p. 600 (tool): mean-zero shocks are uncorrelated with the
constant, `E[ε_t · 1] = 0`. -/
theorem inner_shockL2_one {ν : ProbabilityMeasure ℝ} {B : ℝ}
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (t : ℤ) :
    ⟪shockL2 hbdd t, oneL2 ν⟫ = 0 := by
  rw [L2.inner_def]
  have h1 : (shockL2 hbdd t : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat t) := MemLp.coeFn_toLp _
  have h2 : (oneL2 ν : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hc : (fun ω => ⟪(shockL2 hbdd t : (ℕ → ℝ) → ℝ) ω, (oneL2 ν : (ℕ → ℝ) → ℝ) ω⟫)
      =ᵐ[(iidSystem ν).μ] fun ω => ω (Equiv.intEquivNat t) := by
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]
    simp
  rw [integral_congr_ae hc]
  have h := integral_shock_fun ν (Equiv.intEquivNat t) (f := id) measurable_id
  simp only [id] at h
  rw [h, hmean]

/-- Cochrane (2023), p. 102 and Online Appendix pp. 597 and 600, the Wold theorem in `L²` of the
i.i.d. economy: every absolutely summable moving average of the i.i.d. shocks is regular and is
the moving average `∑ c_j e_{t−j}` (converging in mean square) of its own Wold innovations, which
are white noise, with `∑ c_j² < ∞` and `c_0 = 1`. -/
theorem iid_wold {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) :
    WhiteNoise (innov (maProc a (shockL2 hbdd))) (‖innov (maProc a (shockL2 hbdd)) 0‖ ^ 2) ∧
    Summable (fun j => woldCoeff (maProc a (shockL2 hbdd)) j ^ 2) ∧
    (innov (maProc a (shockL2 hbdd)) 0 ≠ 0 → woldCoeff (maProc a (shockL2 hbdd)) 0 = 1) ∧
    Regular (maProc a (shockL2 hbdd)) ∧
    ∀ t, HasSum (fun j : ℕ => woldCoeff (maProc a (shockL2 hbdd)) j •
      innov (maProc a (shockL2 hbdd)) (t - j)) (maProc a (shockL2 hbdd) t) := by
  have he := iid_whiteNoise hmean hvar hbdd
  obtain ⟨U, hU⟩ := maProc_shift he hσ.ne' ha
  have hr := maProc_regular he ha
  obtain ⟨-, -, h1, h2, -, h3, -⟩ := wold_decomposition hU
  exact ⟨h1, h2, h3, hr, (regular_iff_hasSum hU).mp hr⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, in `L²` of the i.i.d. economy: for
`a(L) = (1 − θL)g(L)` (`|θ| > 1`, `g₀ = 1`, `g` invertible) the Wold innovation of the surplus is
the autoregression error `w` (not the structural shock), the Wold coefficients are the fitted
`ã = (1 − θ⁻¹L)g`, the Wold innovation variance is `θ²σ²`, and the surplus is regular. -/
theorem iid_wold_factor_is_wold {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|)
    {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1)
    (hrec : Invertibility.Recoverable g) :
    (∀ t, innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) t =
      woldInnov θ (maOne θ (shockL2 hbdd)) t) ∧
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) =
      InvertibilityMeasure.factorCoeff θ⁻¹ g ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) 0‖ ^ 2 =
      θ ^ 2 * σ2 ∧
    innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) 0 ≠ shockL2 hbdd 0 := by
  obtain ⟨h1, h2, -, h4, h5⟩ :=
    wold_factor_is_wold (iid_whiteNoise hmean hvar hbdd) hσ.ne' hθ hg hg0 hrec
  refine ⟨h1, h2, h4, h5, ?_⟩
  rw [h1]
  exact (iid_wold_factor hmean hvar hσ hbdd hθ hg hg0 hrec 0).2.2.2.2.2

/-- Cochrane (2023), Online Appendix p. 600, Wold (d), a mixed process in `L²` of the i.i.d.
economy: `x_t = ε_t + 1` (shocks with a nonzero mean). Its Wold innovation is `ε_t`, its
coefficients are `(1, 0, 0, …)`, its deterministic part is the mean `1`, and it is neither regular
nor deterministic. -/
theorem iid_mixed {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {x : ℤ → Lp ℝ 2 (iidSystem ν).μ}
    (hx : ∀ t, x t = shockL2 hbdd t + oneL2 ν) :
    (∀ t, innov x t = shockL2 hbdd t) ∧ (∀ t, detPart x t = oneL2 ν) ∧
    (∀ j, woldCoeff x j = if j = 0 then 1 else 0) ∧ ¬ Regular x ∧ ¬ Deterministic x :=
  mixed_example (iid_whiteNoise hmean hvar hbdd) hσ.ne' (oneL2_ne_zero ν)
    (inner_shockL2_one hbdd hmean) hx

/-- Cochrane (2023), Online Appendix pp. 597 and 600, the fair coin (`σ² = 1`, on the
non-finitely-supported `{±1}^ℕ`): for `|ρ| < 1`, the MA(1) `s_t = e_t − ρ⁻¹e_{t−1}` (`a(ρ) = 0`)
has Wold innovation variance `ρ⁻²`, Wold coefficients `(1, −ρ, 0, 0, …)` (the root flipped to
`ρ`), and is regular; `ε_t + 1` is a mixed process with deterministic part `1`. -/
theorem coin_wold {ρ : ℝ} (hρ0 : 0 < |ρ|) (hρ : |ρ| < 1) :
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) = InvertibilityMeasure.factorCoeff ρ (fun k => if k = 0 then 1 else 0) ∧
    InvertibilityMeasure.factorCoeff ρ (fun k => if k = 0 then 1 else 0) 1 = -ρ ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) 0‖ ^ 2 = (ρ⁻¹) ^ 2 * 1 ∧
    (∀ t, detPart (fun t => shockL2 coin_bdd t + oneL2 coin) t = oneL2 coin) := by
  have hθ : 1 < |ρ⁻¹| := by rw [abs_inv]; exact one_lt_inv_iff₀.mpr ⟨hρ0, hρ⟩
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  obtain ⟨-, h2, h3, h4, -⟩ := iid_wold_factor_is_wold coin_mean coin_var one_pos coin_bdd hθ hδ
    (by simp) InvertibilityMeasure.recoverable_delta
  obtain ⟨-, h5, -⟩ := iid_mixed coin_mean coin_var one_pos coin_bdd (x := fun t =>
    shockL2 coin_bdd t + oneL2 coin) fun _ => rfl
  refine ⟨by rwa [inv_inv] at h2, by simp [InvertibilityMeasure.factorCoeff], h3, h4, h5⟩

/-- Cochrane (2023), Online Appendix p. 597, **correction** in `L²` of the fair-coin economy: the
surplus `s_t = ε_t − ε_{t−1}` has Wold innovation `ε_t` and Wold polynomial `1 − z`, with a root at
`z = 1` on the unit circle; no absolutely summable autoregression recovers the Wold innovation. -/
theorem coin_wold_unit_root (t : ℤ) :
    innov (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd)) t = shockL2 coin_bdd t ∧
    Innovations.gen (woldCoeff (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd))) 1 = 0 ∧
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd) (t - k))
        (innov (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd)) t) := by
  obtain ⟨h1, -, -, h4, -, h6⟩ := wold_unit_root (iid_whiteNoise coin_mean coin_var coin_bdd)
    one_ne_zero (ρ := 1) (by norm_num)
  exact ⟨h1 t, h4, h6 t⟩

end IIDEconomy

end Cochrane.DebtDeficitsInflation.Wold

set_option linter.style.longLine false
#print axioms Cochrane.DebtDeficitsInflation.SchurStable
#print axioms Cochrane.DebtDeficitsInflation.disc
#print axioms Cochrane.DebtDeficitsInflation.root₁
#print axioms Cochrane.DebtDeficitsInflation.root₂
#print axioms Cochrane.DebtDeficitsInflation.root_sum
#print axioms Cochrane.DebtDeficitsInflation.root_prod
#print axioms Cochrane.DebtDeficitsInflation.root_eq
#print axioms Cochrane.DebtDeficitsInflation.normSq_root_of_neg
#print axioms Cochrane.DebtDeficitsInflation.norm_root_of_nonneg
#print axioms Cochrane.DebtDeficitsInflation.schurStable_iff_roots
#print axioms Cochrane.DebtDeficitsInflation.chSeq
#print axioms Cochrane.DebtDeficitsInflation.convSeq
#print axioms Cochrane.DebtDeficitsInflation.convSeq_rec
#print axioms Cochrane.DebtDeficitsInflation.chSeq_eq_convSeq
#print axioms Cochrane.DebtDeficitsInflation.norm_convSeq_le
#print axioms Cochrane.DebtDeficitsInflation.abs_chSeq_le
#print axioms Cochrane.DebtDeficitsInflation.tendsto_chSeq
#print axioms Cochrane.DebtDeficitsInflation.tr2
#print axioms Cochrane.DebtDeficitsInflation.det2
#print axioms Cochrane.DebtDeficitsInflation.tr2_eq_trace
#print axioms Cochrane.DebtDeficitsInflation.det2_eq_det
#print axioms Cochrane.DebtDeficitsInflation.sq_eq_cayleyHamilton
#print axioms Cochrane.DebtDeficitsInflation.pow_succ_eq
#print axioms Cochrane.DebtDeficitsInflation.abs_pow_entry_le
#print axioms Cochrane.DebtDeficitsInflation.tendsto_pow_entry
#print axioms Cochrane.DebtDeficitsInflation.BoundedSeq
#print axioms Cochrane.DebtDeficitsInflation.homogeneous_iterate
#print axioms Cochrane.DebtDeficitsInflation.abs_mulVec_le
#print axioms Cochrane.DebtDeficitsInflation.homogeneous_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.eq_root_of_eq
#print axioms Cochrane.DebtDeficitsInflation.exists_eigenvector
#print axioms Cochrane.DebtDeficitsInflation.exists_bounded_homogeneous
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.mk
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.const
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.mono
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.tower
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.known
#print axioms Cochrane.DebtDeficitsInflation.perfectForesight
#print axioms Cochrane.DebtDeficitsInflation.BoundedProc
#print axioms Cochrane.DebtDeficitsInflation.BoundedVec
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.Adapted
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.IsAR1
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.E_neg
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.E_smul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.E_E_self
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.abs_E_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.bounded_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.ar1_iterate
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forward_iterate
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forward_unique
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.E_tsum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forwardSeries
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.PullOut
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.Solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.AdaptedVec
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.system_iterate
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.system_unique
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.system_not_unique
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.Determinate
#print axioms Cochrane.DebtDeficitsInflation.ExpectationSystem.determinate_iff
#print axioms Cochrane.DebtDeficitsInflation.perfectForesight_pullOut
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.Solves
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.E_of_known
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.solves_adapted
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.iterate_A15
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.summable_A16
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.ScalarEq
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalarSol
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalarSol_apply
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalarEq_iff
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalar_homog
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sunspotFamily
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.homog_solves
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.solves_add_homog
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.existsUnique_iff
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.ar1_decay
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.predetermined_restriction
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.summable_geom_mul
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.abel_tsum
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.DebtDeficitsInflation.ForwardSolution.E_tsum_dom
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_apply
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_of_known
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_mean_zero
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_known
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_E_of_le
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_of_known_succ
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_const
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMDS
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMDSVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.E_shock_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.Innovations.E_shock
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_shock
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_shock_vec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMDSNat
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMDSNat.E_future
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMDSNat.E_past
#print axioms Cochrane.DebtDeficitsInflation.Innovations.extendShock
#print axioms Cochrane.DebtDeficitsInflation.Innovations.isMDS_extendShock
#print axioms Cochrane.DebtDeficitsInflation.Innovations.extendShock_bounded
#print axioms Cochrane.DebtDeficitsInflation.Innovations.E_tsum_abs
#print axioms Cochrane.DebtDeficitsInflation.Innovations.summable_E_terms
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_tsum_abs
#print axioms Cochrane.DebtDeficitsInflation.Innovations.gen
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMA
#print axioms Cochrane.DebtDeficitsInflation.Innovations.IsMAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.genVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.dotShock
#print axioms Cochrane.DebtDeficitsInflation.Innovations.gen_zero
#print axioms Cochrane.DebtDeficitsInflation.Innovations.summable_coeff_mul_pow
#print axioms Cochrane.DebtDeficitsInflation.Innovations.isMA_iff_vec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.isMDSVec_of_isMDS
#print axioms Cochrane.DebtDeficitsInflation.Innovations.abs_ma_term_le
#print axioms Cochrane.DebtDeficitsInflation.Innovations.summable_ma_bound
#print axioms Cochrane.DebtDeficitsInflation.Innovations.E_MAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.summable_E_MAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.abs_MAVec_le
#print axioms Cochrane.DebtDeficitsInflation.Innovations.adapted_MAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_MAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_MA
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_MA_zero
#print axioms Cochrane.DebtDeficitsInflation.Innovations.hasSum_dot_gen
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_PV_termwise_vec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_PV_vec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_PV
#print axioms Cochrane.DebtDeficitsInflation.Innovations.innov_PV_termwise
#print axioms Cochrane.DebtDeficitsInflation.Innovations.tendsto_pow_mul_innov_MAVec
#print axioms Cochrane.DebtDeficitsInflation.Innovations.ar1_of_MA
#print axioms Cochrane.DebtDeficitsInflation.Innovations.MA_of_ar1
#print axioms Cochrane.DebtDeficitsInflation.Innovations.isAR1_of_MA
#print axioms Cochrane.DebtDeficitsInflation.Innovations.iidCoeff
#print axioms Cochrane.DebtDeficitsInflation.Innovations.isMA_iid
#print axioms Cochrane.DebtDeficitsInflation.Innovations.gen_iid
#print axioms Cochrane.DebtDeficitsInflation.Innovations.coinShockZ
#print axioms Cochrane.DebtDeficitsInflation.Innovations.coinShockZ_isMDS
#print axioms Cochrane.DebtDeficitsInflation.Innovations.coinShockZ_bounded
#print axioms Cochrane.DebtDeficitsInflation.Innovations.coinShockZ_one
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.seriesTo_of_hasSum
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.seriesTo_iff_hasSum
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo.unique
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo.congr
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo.add
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo.sub
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.SeriesTo.const_mul
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.seriesTo_zero
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.seriesTo_succ_iff
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.Recursion
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.rec_finite
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.rec_map_finite
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.rec_seriesTo_map
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.tvc_of_bound
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.tvc_E_of_bounded
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.tvc_innov_of_bounded
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.tvc_innov_of_MAVec
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.Flow
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.flow_iff_recursion
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.sOfFlow
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.flow_sOfFlow
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.eq_sOfFlow
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.pv_finite
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.pv_expected_combined
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.pv_expected
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.pv_expected_tsum
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.pv_expected_bounded
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.unexpected_inflation_identity
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.unexpected_inflation_identity_tsum
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.BondReturn
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.bond_return_identity
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.bond_return_identity_real
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.one_period_innov_rn
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.weighted_inflation_identity
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.ConstExpReturn
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.innov_future_return_zero
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.inflation_identity_const
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.bond_return_identity_const
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.weighted_inflation_identity_const
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.inflation_identity_one_period
#print axioms Cochrane.DebtDeficitsInflation.LinearizedIdentities.inflation_identity_one_period_const
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flow_ratio
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.log_flow
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flowLog
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.rhoLin
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.ssRate
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.steady_state_flow
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.rhoLin_eq_exp
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.rhoLin_pos_lt_one_iff
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flowDeriv
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flowDeriv_apply
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flowLog_hasFDerivAt
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flow_constant
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.flow_iff_first_order
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondQ
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondQ_hasSum
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bond_steady_return
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondLog
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondDeriv
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondDeriv_apply
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bond_steady_log
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondLog_hasFDerivAt
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bondReturn_iff_first_order
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.approx_1_24_differs
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.bond_price_series
#print axioms Cochrane.DebtDeficitsInflation.LinearizationDerivation.printed_bond_price_counterexample
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.SimpleModel
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.InnovTVC
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innovTVC_of_bounded
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_infl_eq_tsum
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_infl_eq
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_infl_eq_surplus
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.condVar_innov_infl
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.condCov_innov_infl
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.no_correlation_of_gen_zero
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.ar1_volatility_example
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ar1
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.one_lt_gen_ar1_iff
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ar1_lt_one_example
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exists_neg_coeff_of_gen_lt_one
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.ma1Coeff
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.isMA_ma1
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ma1
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ma1_inv
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ma1_zero
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.one_lt_gen_ma1
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.gen_ma1_mem_Ioo
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_ma1_now
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_ma1_next
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.ma1_printed_signs_false
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.value_recursion
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.value_ar1
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.rho_innov_value
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.rho_innov_value_eq
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_value_pos_iff
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_value_full_repayment
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_value_eq_series
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_return
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_return_split
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.innov_return_riskfree
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.abs_innov_return_ge
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.sdf_one_step
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.realDebt
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.realDebtEnd
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.deflation
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.bondPrice
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.pv
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.ExactValuation
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.realDebt_eq_mul
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.pv_succ
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.revenue_eq
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exact_flow_of_valuation
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exact_innov_line
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.printed_exact_line
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.printed_exact_line_iff
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.printed_exact_line_counterexample
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exact_innov_flow
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exact_innov_flow_pv
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.exact_innov_flow_ma
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.revenue_innov
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.financing_by_debt
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.financing_by_inflation
#print axioms Cochrane.DebtDeficitsInflation.SurplusMA.financing_superinflation
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.tied_together
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.gen_identified
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.gen_identified_debt
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.no_inflation_iff_gen_zero
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.revenue_rises_iff
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fbValue
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fbSurplus
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fb_flow
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fbValue_bounded
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fbValue_adapted
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.fb_innov_surplus
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.feedback_full_repayment
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.ar1_innov_sum
#print axioms Cochrane.DebtDeficitsInflation.SurplusProcessFacts.feedback_repaid_despite_persistent_u
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.dotShock_add
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.dotShock_sub
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.dotShock_neg
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.Nondeg
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.seriesTo_innov_MAVec
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.seriesTo_innov_MAVec_succ
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.genVec_zero
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.innov_pi_vector
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_4_11
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_4_11_vec
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_A2
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.printed_rhs_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.printed_line_iff
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.repayment_iff
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.repayment_iff_vec
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.const_expected_return_coeffs
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.const_discount_gen
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.repayment_reduces
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.cxShock
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.cxCoeff
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.cxSurplus
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.cx_isMAVec
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.cx_innov_shock
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.printed_line_counterexample
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_4_12
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.CSReturn
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.csReturn_iff_recursion
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.campbellShiller_finite
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.campbellShiller
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.campbellShiller_expected
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.campbellAmmer
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.campbellAmmer_MA
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_4_13
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.identity_4_13_vec
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.printedCampbellAmmer
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.printed_campbellAmmer_counterexample
#print axioms Cochrane.DebtDeficitsInflation.GeneralizedHRS.pv_constant_discount_iff
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.dividend_pv
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.dividend_pv_E
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.pih_consumption
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.surplus_pv_ar1
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.innov_infl_ar1
#print axioms Cochrane.DebtDeficitsInflation.PresentValueExamples.printed_p604_iff
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.IsVAR
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.ShockMDS
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.obs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.vecAt
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.obs_apply
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.PowDecay
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.eigs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.map_ofReal_pow
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.powDecay_of_eigs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.powDecay_smul
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.summable_pow_entry
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.tendsto_pow_entry
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.neumannSum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.neumannSum_mul
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.inv_one_sub_eq
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.isUnit_det_one_sub
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.inv_one_sub_hasSum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.hasSum_bilin
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.neumann_bilin_hasSum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.disc_rate_hasSum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.innov_obs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.E_obs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_forecast
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_innov
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_innov_obs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_forecast_obs
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.obs_adapted
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.weight_bilin
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_weighted_sum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_sum_responses
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_disc_rate_sum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_15
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_16
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_14
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_shifted_summable
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_15_of_var
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_14_of_var
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.identity_4_14_rho_one_of_var
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.cholesky_blocks
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.regression_eq_cholesky
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.filled_shock_eq_orthogonalized
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.regression_coeff_single
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.functional_regression
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.functional_regression_normalised
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.quadForm_pos
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.Regression.surplus_shock_sum
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.obs_add
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.obs_sub
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.flow_restriction_of_identity
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.one_sub_smul_mul_comm
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.inv_one_sub_mul_comm
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.flow_restriction_iff_pv
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.pv_of_flow
#print axioms Cochrane.DebtDeficitsInflation.VARIdentities.var_pv_identity
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.Coarser
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.coarser_refl
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.coarser_trans
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.fullInfo
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.coarser_fullInfo
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown_general
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown_series
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown_pathwise
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.r_squared_one
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.info_larger_of_not_known
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.condDown_fails_example
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.eq_of_ae_eq
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.le_of_ae_le
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.condExpSystem
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.condExpSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.condExpSystem_coarser
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.condExpSystem_known_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDown.CondExp.condDown_condExp_iff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.armaCoeff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.armaCoeff_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.genFn_armaCoeff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.summable_abs_armaCoeff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.autocov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_autocov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_autocov_flip
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_autocov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_autocov_flip
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.blaschke_norm
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.spectral_density_flip
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Recoverable
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.genFnC
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.genFnC_ofReal
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.genFnC_ne_zero_of_recoverable
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.not_recoverable_of_root
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.not_recoverable_of_aRho_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_aRho
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_aRho_eq_zero_iff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_aRho_gt
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_fitted_aRho
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_formal_inverse
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_inverse_not_summable
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_aRho_params
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_iid_of_one
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_noninvertible_iff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_root
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_not_recoverable
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_wold_aRho
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.debt_ar1
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_time_domain
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.arma11_revision
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.debt_var_eq
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.debt_var_tr_det
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.debt_var_stable
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.shock_from_debt
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_forecasts
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_pv_forward
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_value_reveals_shock
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_debt_value
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_no_inflation_iff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_repaying_debt_value
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.printed_2_11_wrong
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_pv_innov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_fitted_pv_innov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma1_debt_var
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.maSeries
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.hsCoeff
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.summable_hs
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.hsCoeff_rec
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.rho_hsCoeff_zero
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.abs_hsCoeff_le
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma_split
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.ma_forecast
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.hansenSargent
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.hansenSargent_E_tsum
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.hansenSargent_genFn
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.value_expost_of_aRho_zero
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.factor_value
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.factor_of_aRho_zero
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.WhiteNoise
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.maProc
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.pastSpan
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.maOne
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.woldInnov
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.WhiteNoise.norm_eq
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.maProc_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.inner_hasSum_right
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.inner_e_maProc
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.mem_pastSpan_self
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.pastSpan_mono
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.mem_orthogonal_pastSpan
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.hasSum_mem_pastSpan
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.woldInnov_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.wold_recursion
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.inner_e_wold
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.inner_wold_maProc
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.wold_innovation
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.shiftSeq
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.summable_abs_shiftSeq
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.maProc_shift_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.maProc_shiftSeq
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.ar2_filter_eq_maOne
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.ma1_wold
#print axioms Cochrane.DebtDeficitsInflation.Invertibility.Hilbert.arma11_wold
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_forecast
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.isAR1_of_shocks
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_revision
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_pv_revision
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.kcoef
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_eps_s
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_inflation_eq
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_eps_z_zero
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_no_inflation
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.ptCoeff
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_coeff_zero
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_revision_eps_s
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_aRho
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.ptTheta
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_arma21_coeffs
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_arma21_time
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_theta_zero
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.ar2Impulse
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.ar2ma1Coeff
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.ar2ma1_genFn
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_fitted_aRho
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_fit_ar1
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_coeff_eq_ar2ma1
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.HilbertPT.summable_abs_ptCoeff
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.HilbertPT.pt_wold
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.HilbertPT.pt_wold_ar1
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_value
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_value_printed
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_value_printed_eq
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.printed_value_ne
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_var
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_var_process
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_var_tr_det
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_coeff_pos
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_debt_coeff_gt_one
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.pt_shocks_recoverable
#print axioms Cochrane.DebtDeficitsInflation.PermanentTransitory.printed_value_var_fails
#print axioms Cochrane.DebtDeficitsInflation.Links.armaCoeff_zero_eq_ma1Coeff
#print axioms Cochrane.DebtDeficitsInflation.Links.armaCoeff_ar1
#print axioms Cochrane.DebtDeficitsInflation.Links.gen_armaCoeff_ar1
#print axioms Cochrane.DebtDeficitsInflation.Links.gen_armaCoeff_zero
#print axioms Cochrane.DebtDeficitsInflation.Links.isMDSNat_iff_shockMDS
#print axioms Cochrane.DebtDeficitsInflation.Links.presample
#print axioms Cochrane.DebtDeficitsInflation.Links.presample_succ
#print axioms Cochrane.DebtDeficitsInflation.Links.isMDS_presample
#print axioms Cochrane.DebtDeficitsInflation.Links.abs_presample_le
#print axioms Cochrane.DebtDeficitsInflation.Links.maSeries_isMA
#print axioms Cochrane.DebtDeficitsInflation.Links.innov_PV_maSeries
#print axioms Cochrane.DebtDeficitsInflation.Links.hansenSargent_innov
#print axioms Cochrane.DebtDeficitsInflation.Links.innov_infl_of_revision
#print axioms Cochrane.DebtDeficitsInflation.Links.arma11_innov_infl
#print axioms Cochrane.DebtDeficitsInflation.Links.ma1_revision
#print axioms Cochrane.DebtDeficitsInflation.Links.ma1_innov_infl
#print axioms Cochrane.DebtDeficitsInflation.Links.ma1_innov_infl_repay
#print axioms Cochrane.DebtDeficitsInflation.Links.pt_pv_revision_via_ar1
#print axioms Cochrane.DebtDeficitsInflation.Links.pt_innov_infl
#print axioms Cochrane.DebtDeficitsInflation.Links.condDown_flow
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.mk
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.P
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.𝓕
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.μ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddProc
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.integrable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_add
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_sub
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_smul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_const
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_zero
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_mono
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_tower
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.integrable_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_of_stronglyMeasurable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_of_aestronglyMeasurable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_known
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_E_self
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_congr
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.integral_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_pullOut
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.abs_E_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.of_stronglyMeasurable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.const
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.add
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.smul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.sub
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.mul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_mul_innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.E_hasSum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.discSum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.discSum_succ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.discSum_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.discSum_rec
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.aestronglyMeasurable_discSum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.Solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forwardSol
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forwardSol_adapted
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forwardSol_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.iterate_homog
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.forward_unique
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.existsUnique_forward
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot_succ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot_adapted
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot_solves
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.solves_add
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.sunspot_not_predictable
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.not_unique_of_one_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.solves_zero
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.unique_iff
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.existsUnique_iff
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.BddRV.sq
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.ar1_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.ar1_E_sq_dev
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.ar1_condVar
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.ar1_condVar_closed
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.eq_of_ae_eq
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.le_of_ae_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.ELin
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.trivialFirst
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.sum_prob_condE
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeMeasure
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeMeasure_singleton
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeMeasure_univ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeProb
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.integral_treeProb
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeFiltration
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.stronglyMeasurable_condE
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeSystem_fullSupport
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasure.TreeBridge.treeSystem_toExpectationSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iidProb
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iidSystem
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.shock
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.measurable_shock
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coordSigma
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.futureSigma
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coordSigma_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.futureSigma_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iIndep_coord
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.filtration_le_past
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.indep_future
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_future
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.measurable_future_fun
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.integral_shock_fun
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_shock_fun
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_shock
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_shock_sq
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.shock_ae_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_shock_zero
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.E_shock_sq_eq
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.condVar_shock
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.shock_not_ae_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.singleton_lt_one
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.exists_singleton_le
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_singleton
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_countable_null
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_not_finitely_supported
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_news
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_existsUnique_iff
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_sunspot
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.ar1
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.ar1_succ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.ar1_adapted
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.ar1_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_ar1_E
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_ar1_condVar
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.iid_ar1_condVar_closed
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coinMeasure
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coinMeasure_univ
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coin
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.integral_coin
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coin_mean
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coin_var
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coin_bdd
#print axioms Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID.coin_economy
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.coarsen
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Nested
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.MeasCoarser
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.eq_coarsen
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.KnownAE
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.coarsen_μ
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.coarsen_E
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.E_coarsen_tower
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_general
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.known_iff_E_eq
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.known_of_same
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.E_coarsen_innov
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_valuation
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_valuation_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.pv_ex_post
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.pv_E
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.pv_agents
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_flow_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.abs_innov_le
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.summable_innov
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.innov_pv
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.unexpected_inflation_any
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.unexpected_inflation_agents
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.innov_coarsen_of_known
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.constExp_condDown
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.innov_return_condDown
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.simple_model_any
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.simple_model_agents
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.simple_model_econ_iff
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.lagFiltration
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.nested_lag
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.exS
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.exV
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.exR
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.exInfl
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.exRn
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.ex_flow
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.ex_fisher
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.Example.econ_decomp_counterexample
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.coarsen_toExpectationSystem_E
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.coarser_core
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.condDown_iff_core
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.forall_of_ae
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.core_innov_eq
#print axioms Cochrane.DebtDeficitsInflation.ConditioningDownMeasure.unexpected_inflation_core
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.eSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.inner_e_maProc_future
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.inner_e_maProc_int
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.hasSum_mem_eSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.e_mem_eSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.maProc_mem_eSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.eq_of_inner_e
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.norm_maProc_le
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.cconv
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.summable_cconv
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mk_cconv
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.hasSum_filter_maProc
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.not_filter_of_aRho_eq_zero
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.maProc_armaCoeff_zero
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.inner_sum_e
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mem_pastSpan_unit_root
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.factorCoeff
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mk_factorCoeff
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.summable_factorCoeff
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.gen_factorCoeff
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mk_mul_eq_one
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mk_geom_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.eq_of_mk_eq
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.wold_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.summable_abs_hsCoeff
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.debt_hasSum_expost
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.maProc_delta
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.hsCoeff_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.shock_mem_debtSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.debt_not_invertible_example
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.exists_shift
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.jointSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.pastSpan_le_jointSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.debt_mem_jointSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.pastSpan_debt_le_jointSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.map_pastSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.granger_general
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.mem_orthogonal_jointSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.granger_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.factorCoeff_delta
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.recoverable_delta
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasure.wold_factor_ma1
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.memLp_coord
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.shockL2
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.integral_coord_mul
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_whiteNoise
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_not_filter
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_unit_root
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_wold_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_granger_general
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_granger_factor
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.coin_L2
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.iid_not_mem_pastSpan
#print axioms Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2.closedSpan_fails_at_unit_root
#print axioms Cochrane.DebtDeficitsInflation.Wold.past
#print axioms Cochrane.DebtDeficitsInflation.Wold.past_eq_pastSpan
#print axioms Cochrane.DebtDeficitsInflation.Wold.remote
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov
#print axioms Cochrane.DebtDeficitsInflation.Wold.woldCoeff
#print axioms Cochrane.DebtDeficitsInflation.Wold.detPart
#print axioms Cochrane.DebtDeficitsInflation.Wold.Deterministic
#print axioms Cochrane.DebtDeficitsInflation.Wold.Regular
#print axioms Cochrane.DebtDeficitsInflation.Wold.mem_past
#print axioms Cochrane.DebtDeficitsInflation.Wold.self_mem_past
#print axioms Cochrane.DebtDeficitsInflation.Wold.past_mono
#print axioms Cochrane.DebtDeficitsInflation.Wold.mem_past_of_le
#print axioms Cochrane.DebtDeficitsInflation.Wold.remote_eq
#print axioms Cochrane.DebtDeficitsInflation.Wold.remote_le
#print axioms Cochrane.DebtDeficitsInflation.Wold.mem_remote_iff
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_mem
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_mem_orthogonal
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_innov_of_mem
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_innov_lt
#print axioms Cochrane.DebtDeficitsInflation.Wold.x_eq_innov_add
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_eq_zero_iff
#print axioms Cochrane.DebtDeficitsInflation.Wold.mem_past_pred
#print axioms Cochrane.DebtDeficitsInflation.Wold.map_past
#print axioms Cochrane.DebtDeficitsInflation.Wold.starProjection_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.norm_innov
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_whiteNoise
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_eq_zero_of
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_x_innov
#print axioms Cochrane.DebtDeficitsInflation.Wold.woldCoeff_eq
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_innov_x
#print axioms Cochrane.DebtDeficitsInflation.Wold.woldCoeff_zero
#print axioms Cochrane.DebtDeficitsInflation.Wold.orthonormal_innov
#print axioms Cochrane.DebtDeficitsInflation.Wold.woldCoeff_smul
#print axioms Cochrane.DebtDeficitsInflation.Wold.hasSum_wold
#print axioms Cochrane.DebtDeficitsInflation.Wold.norm_inner_sq
#print axioms Cochrane.DebtDeficitsInflation.Wold.summable_sq_woldCoeff
#print axioms Cochrane.DebtDeficitsInflation.Wold.tsum_sq_woldCoeff_le
#print axioms Cochrane.DebtDeficitsInflation.Wold.regPart_mem
#print axioms Cochrane.DebtDeficitsInflation.Wold.inner_innov_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Wold.innov_mem_orthogonal_remote
#print axioms Cochrane.DebtDeficitsInflation.Wold.regPart_mem_orthogonal_remote
#print axioms Cochrane.DebtDeficitsInflation.Wold.sub_regPart_mem_remote
#print axioms Cochrane.DebtDeficitsInflation.Wold.detPart_eq
#print axioms Cochrane.DebtDeficitsInflation.Wold.x_eq_regPart_add_detPart
#print axioms Cochrane.DebtDeficitsInflation.Wold.detPart_mem_remote
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_decomposition
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_unique
#print axioms Cochrane.DebtDeficitsInflation.Wold.deterministic_iff
#print axioms Cochrane.DebtDeficitsInflation.Wold.deterministic_iff_detPart
#print axioms Cochrane.DebtDeficitsInflation.Wold.regular_iff
#print axioms Cochrane.DebtDeficitsInflation.Wold.regular_iff_hasSum
#print axioms Cochrane.DebtDeficitsInflation.Wold.past_le_of_mem
#print axioms Cochrane.DebtDeficitsInflation.Wold.remote_eq_past_detPart
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_dichotomy
#print axioms Cochrane.DebtDeficitsInflation.Wold.eq_zero_of_regular_deterministic
#print axioms Cochrane.DebtDeficitsInflation.Wold.stationary_of_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.exists_shift_of_stationary
#print axioms Cochrane.DebtDeficitsInflation.Wold.stationary_iff_exists_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_of_stationary
#print axioms Cochrane.DebtDeficitsInflation.Wold.mixed_example
#print axioms Cochrane.DebtDeficitsInflation.Wold.maProc_shift
#print axioms Cochrane.DebtDeficitsInflation.Wold.maProc_regular
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_factor_is_wold
#print axioms Cochrane.DebtDeficitsInflation.Wold.wold_unit_root
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.oneL2
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.inner_oneL2
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.oneL2_ne_zero
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.inner_shockL2_one
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.iid_wold
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.iid_wold_factor_is_wold
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.iid_mixed
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.coin_wold
#print axioms Cochrane.DebtDeficitsInflation.Wold.IIDEconomy.coin_wold_unit_root
