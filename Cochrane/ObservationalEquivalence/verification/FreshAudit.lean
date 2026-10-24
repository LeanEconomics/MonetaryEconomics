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
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.Option
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

namespace Cochrane.ObservationalEquivalence

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

end Cochrane.ObservationalEquivalence

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

namespace Cochrane.ObservationalEquivalence

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

end Cochrane.ObservationalEquivalence

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

namespace Cochrane.ObservationalEquivalence.ExpectationsFiniteTree

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

end Cochrane.ObservationalEquivalence.ExpectationsFiniteTree

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

namespace Cochrane.ObservationalEquivalence.ForwardSolution

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

end Cochrane.ObservationalEquivalence.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Shared tools: innovations, full information, ex-post present values, flow identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, p. 495, §22.3,
p. 501 (footnote 1), §22.7, p. 508, and Online Appendix Chapter 2, §2.2–2.3, pp. 604–606.

Objects used by both chains of this project, collected in one place (dedupe pass):

* `innov`: the innovation operator `ΔE_{t+1} = E_{t+1} − E_t` (Cochrane (2023), (22.1), p. 495
  and p. 501, footnote 1), a linear map; `innov_apply`, `innov_of_known`.
* `fullInfo`: the expectation system with full information at every date, `E_t = id`
  (perfect foresight on an arbitrary state space).
* `pvExPost`: the ex-post present value `∑_{j ≥ 0} ρʲ s_{t+1+j}` (p. 495; Online Appendix
  §2.3, p. 606).
* `summable_pow_mul_of_bounded`, `tendsto_pow_mul_of_bounded`: geometric weights on bounded
  sequences (`|ρ| < 1`): the present value converges absolutely and the transversality term
  vanishes.
* `flow_telescope`: iterating a flow identity `ρ v_{t+1} = v_t − y_t` forward, in any real
  vector space (ex post for paths, or for random variables).
* `pv_of_flow`: iterating the flow identity under `E_t` and imposing the transversality
  condition gives the present-value relation (Online Appendix p. 605).
-/

namespace Cochrane.ObservationalEquivalence.ExpectationTools

open Filter Topology

variable {Ω : Type*}

/-! ### Innovations -/

/-- Cochrane (2023), (22.1), p. 495, and p. 501, footnote 1: the innovation operator
`ΔE_{t+1} = E_{t+1} − E_t`. -/
def innov (𝔼 : ExpectationSystem Ω) (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), (22.1), p. 495: `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) :
    innov 𝔼 t x = 𝔼.E (t + 1) x - 𝔼.E t x := rfl

/-- Cochrane (2023), (22.1), p. 495: a random variable known at date `t` has no date-`t + 1`
innovation, `ΔE_{t+1} x = 0`. -/
theorem innov_of_known (𝔼 : ExpectationSystem Ω) {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) :
    innov 𝔼 t x = 0 := by
  have h1 : 𝔼.E (t + 1) x = x := by
    rw [← hx]
    exact 𝔼.known (Nat.le_succ t) x
  rw [innov_apply, h1, hx, sub_self]

/-! ### Full information -/

/-- Cochrane (2023), §22.7, p. 508, and Online Appendix p. 602: the expectation system in which
every date has full information about the state, `E_t = id` (perfect foresight on an arbitrary
state space). -/
def fullInfo (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), §22.7, p. 508: under full information `E_t x = x`. -/
theorem fullInfo_E (t : ℕ) (x : Ω → ℝ) : (fullInfo Ω).E t x = x := rfl

/-! ### Present values with geometric weights -/

/-- Cochrane (2023), §22.1, p. 495, and Online Appendix §2.3, p. 606: the ex-post present value
`∑_{j ≥ 0} ρʲ s_{t+1+j}`, a random variable. -/
noncomputable def pvExPost (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω

/-- Cochrane (2023), §22.1, p. 495: with `|ρ| < 1` a bounded sequence has an absolutely
summable present value `∑ ρʲ x_j`. -/
theorem summable_pow_mul_of_bounded {ρ K : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ}
    (hx : ∀ j, |x j| ≤ K) : Summable (fun j => ρ ^ j * x j) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K)
    (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx j) (pow_nonneg (abs_nonneg ρ) j))

/-- Cochrane (2023), §22.1, p. 495 (bounded debt satisfies the transversality condition): with
`|ρ| < 1`, `ρᵀ x_T → 0` for every bounded sequence `x`. -/
theorem tendsto_pow_mul_of_bounded {ρ K : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ}
    (hx : ∀ T, |x T| ≤ K) : Tendsto (fun T => ρ ^ T * x T) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun T => |ρ| ^ T * K) (fun T => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hx T) (pow_nonneg (abs_nonneg ρ) T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K

/-! ### Iterating a flow identity -/

/-- Cochrane (2023), §22.1, p. 495, and Online Appendix §2.3, p. 606 (iterating the flow
condition forward): if `ρ v_{t+1} = v_t − y_t` at every date (in any real vector space), then
`v_t = ∑_{j<T} ρʲ y_{t+j} + ρᵀ v_{t+T}`. -/
theorem flow_telescope {M : Type*} [AddCommGroup M] [Module ℝ M] {ρ : ℝ} {v y : ℕ → M}
    (h : ∀ t, ρ • v (t + 1) = v t - y t) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • y (t + j) + ρ ^ T • v (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e : v (t + T) = ρ • v (t + (T + 1)) + y (t + T) := by
      rw [show t + (T + 1) = t + T + 1 by omega, h (t + T)]
      abel
    rw [ih, e, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ]
    abel

/-- Cochrane (2023), Online Appendix p. 605 ("we derived (2.26) by iterating forward (2.24)"),
and §22.1, p. 495: if `ρv_{t+1} = v_t − y_{t+1}` at every date, `v_t` is known at `t` and
`ρᵀE_t v_{t+T} → 0`, then `v_t = ∑_{j≥0} ρʲ E_t y_{t+1+j}` as the limit of the partial sums. -/
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

end Cochrane.ObservationalEquivalence.ExpectationTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scalar debt recursions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.7, pp. 508–509, and
Chapter 23, eqs. (23.1)–(23.4), pp. 512–513: whether fiscal policy is "active" or "passive" is a
statement about the scalar debt recursion `ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`.
This module collects the recursion facts used by the rest of the chain.

## Restated from the Woodford Chapter 4 project

Woodford (2003), *Interest and Prices*, Chapter 4, §4, pp. 311–314 (`Fiscal.lean` of the
`NeoWicksellianFramework` project, and `abs_rec_le`, `pow_bounded_eq_zero` of its
`BlanchardKahn` module): the recursion `dRec`, `eq_dRec`; bounded-input-bounded-state for
`|γ| < 1` (`rec_bounded`) and its failure for `|γ| ≥ 1` (`rec_unbounded`); Woodford's (4.2),
(4.4), (4.5) (`Debt42`, `Tax44`, `Debt45`, `debt42_iff_45`) and the definition of a
**locally Ricardian** tax rule with its characterisation `locallyRicardian_iff`
(`|β⁻¹(1 − τ_b)| < 1`) and `ricardian_iff_taub`. This is the boundedness criterion of Leeper
(1991) used to classify fiscal policy.

## General lemmas added here

* `dRec_adapted_of_succ`: the recursion is adapted when the date-`t` input is known at `t + 1`.
* `one_le_abs_one_sub_iff`, `abs_one_sub_lt_one_iff`: `|1 − γ| ≥ 1 ↔ γ ≤ 0 ∨ 2 ≤ γ` and
  `|1 − γ| < 1 ↔ 0 < γ < 2` (the corrected regime boundaries of survey error E12).
* `tendsto_pow_mul_iff`, `eq_zero_of_tendsto_pow_mul`: `qᵀ x → 0 ↔ |q| < 1 ∨ x = 0`.
* `tendsto_zero_of_stable_rec`: a stable recursion `y_{T+1} = q y_T + w_T`, `|q| < 1`, driven by
  geometrically vanishing inputs tends to zero (used for the transversality condition).
* `zero_of_E_succ_eq_smul`: a bounded adapted process with `E_t e_{t+1} = φ e_t`, `|φ| > 1`,
  is identically zero (the active-money uniqueness step).
-/

namespace Cochrane.ObservationalEquivalence.FiscalRec

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Woodford (2003), (4.2)–(4.5): the linearised debt dynamics under a tax rule -/

/-- Woodford (2003), eq. (4.2), p. 312 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508), with `d_t = b̂_{t−1}`:
`b̂_t = β⁻¹[b̂_{t−1} − b̄ π_t + Ĝ_t − τ̂_t] + b̄ î_t`. -/
def Debt42 (β bb : ℝ) (d π G τ i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • (d t - bb • π t + G t - τ t) + bb • i t

/-- Woodford (2003), eq. (4.4), p. 313 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508): the linear tax rule
`τ̂_t = τ_b b̂_{t−1} + τ_g Ĝ_t + τ_π π_t + τ_y Ŷ_t + τ_i î_t + v_t`. -/
def Tax44 (τb τg τπ τy τi : ℝ) (d G π Y i v τ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, τ t = τb • d t + τg • G t + τπ • π t + τy • Y t + τi • i t + v t

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508): the implied law of motion of real debt. -/
def Debt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Woodford (2003), (4.2), (4.4)–(4.5), p. 313 (restated from the Woodford Chapter 4 project;
used for Cochrane (2023), §22.7, p. 508): substituting the tax rule (4.4) into (4.2) gives (4.5). -/
theorem debt42_iff_45 {β bb τb τg τπ τy τi : ℝ} {d π G Y i v τ : ℕ → Ω → ℝ}
    (htax : Tax44 τb τg τπ τy τi d G π Y i v τ) :
    Debt42 β bb d π G τ i ↔ Debt45 β bb τb τg τπ τy τi d π G Y i v := by
  unfold Debt42 Debt45
  refine forall_congr' fun t => ?_
  rw [htax t]
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-! ### The scalar recursion `d_{t+1} = γ d_t + u_t` -/

/-- Woodford (2003), (4.5), p. 313 (restated from the Woodford Chapter 4 project; Cochrane (2023),
(23.4), p. 512): the path generated from `d_0` and inputs `u_t` by `d_{t+1} = γ d_t + u_t`. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Woodford (2003), (4.5), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane
(2023), (23.4), p. 512): a solution of `d_{t+1} = γ d_t + u_t` is determined by `d_0`. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Woodford (2003), p. 277 and Prop. C.2, p. 672 (restated from the Woodford Chapter 4 project;
Cochrane (2023), (23.4), p. 512): a stable scalar recursion `x_{t+1} = λ x_t + u_t`, `|λ| < 1`,
with bounded `u` stays bounded. -/
theorem abs_rec_le {lam C B : ℝ} (hl : |lam| < 1) {u x : ℕ → ℝ} (hu : ∀ t, |u t| ≤ C)
    (hx0 : |x 0| ≤ B) (hx : ∀ t, x (t + 1) = lam * x t + u t) (t : ℕ) :
    |x t| ≤ max B (C / (1 - |lam|)) := by
  have h1 : 0 < 1 - |lam| := by linarith
  induction t with
  | zero => exact le_max_of_le_left hx0
  | succ t ih =>
    rw [hx t]
    set K := max B (C / (1 - |lam|))
    have hK : C ≤ (1 - |lam|) * K := by
      have := le_max_right B (C / (1 - |lam|))
      rw [div_le_iff₀ h1] at this
      linarith
    calc |lam * x t + u t| ≤ |lam| * |x t| + |u t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |lam| * K + C := by gcongr; exact hu t
      _ ≤ K := by linarith

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `|γ| < 1` the recursion `d_{t+1} = γ d_t + u_t` is
bounded-input-bounded-state: `|d_t| ≤ B + U/(1 − |γ|)`. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `|γ| ≥ 1` the recursion is not bounded-input-bounded-state: with
`s = sign γ` and inputs `u_t = ε s^{t+1}`, the path from `d_0 = 0` satisfies `|d_t| ≥ ε t`. -/
theorem rec_unbounded {γ ε : ℝ} (hγ : 1 ≤ |γ|) (hε : 0 ≤ ε) {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d (t + 1) = γ • d t +
      fun _ => ε * (if 0 ≤ γ then (1 : ℝ) else -1) ^ (t + 1))
    (h0 : d 0 = 0) : ∀ t ω, ε * t ≤ |d t ω| := by
  set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
  have hss : s * s = 1 := by rw [hs]; split_ifs <;> norm_num
  have hγs : γ = s * |γ| := by
    rw [hs]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have key : ∀ t ω, ε * t ≤ s ^ t * d t ω := by
    intro t
    induction t with
    | zero => intro ω; simp [h0]
    | succ t ih =>
      intro ω
      rw [hd t]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : s ^ (t + 1) * (γ * d t ω + ε * s ^ (t + 1)) = |γ| * (s ^ t * d t ω) + ε := by
        have h2 : s ^ (t + 1) * s ^ (t + 1) = 1 := by
          rw [← mul_pow, hss, one_pow]
        have h3 : γ * d t ω = s * |γ| * d t ω := by rw [← hγs]
        rw [h3]
        calc s ^ (t + 1) * (s * |γ| * d t ω + ε * s ^ (t + 1))
            = |γ| * (s ^ t * (s * s) * d t ω) + ε * (s ^ (t + 1) * s ^ (t + 1)) := by ring
          _ = _ := by rw [hss, h2]; ring
      rw [e]
      push_cast
      have := ih ω
      have ht : 0 ≤ ε * t := mul_nonneg hε (Nat.cast_nonneg t)
      nlinarith
  intro t ω
  have hst : |s ^ t| = 1 := by
    rw [abs_pow]
    have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
    rw [this, one_pow]
  calc ε * t ≤ s ^ t * d t ω := key t ω
    _ ≤ |s ^ t * d t ω| := le_abs_self _
    _ = |d t ω| := by rw [abs_mul, hst, one_mul]

/-- Woodford (2003), p. 314 and App. C.8 (restated from the Woodford Chapter 4 project; Cochrane
(2023), §22.7, p. 508): if `|γ| > 1` and `γᵗ e₀` stays bounded, then `e₀ = 0`. -/
theorem pow_bounded_eq_zero {γ e0 M : ℝ} (hγ : 1 < |γ|) (h : ∀ t : ℕ, |γ ^ t * e0| ≤ M) :
    e0 = 0 := by
  by_contra hne
  have hpos : 0 < |e0| := abs_pos.mpr hne
  have ht := tendsto_pow_atTop_atTop_of_one_lt hγ
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (M / |e0|)).exists
  have := h n
  rw [abs_mul, abs_pow, div_lt_iff₀ hpos] at *
  linarith

/-- Woodford (2003), App. C.8, p. 685 (restated from the Woodford Chapter 4 project; Cochrane
(2023), (23.4), p. 512): the recursion driven by adapted inputs from a constant start is
adapted. -/
theorem dRec_adapted {γ b0 : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (dRec γ u (fun _ => b0)) := by
  intro t
  induction t with
  | zero => exact 𝔼.const 0 b0
  | succ t ih =>
    change 𝔼.E (t + 1) (γ • dRec γ u (fun _ => b0) t + u t) = γ • dRec γ u (fun _ => b0) t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t)]

/-- Cochrane (2023), (23.4), p. 512 (debt `v_{t+1}` depends on date-`t+1` inflation): the
recursion `d_{t+1} = γ d_t + u_t` is adapted when `d_0` is known at date 0 and the input `u_t`
is known at date `t + 1`. -/
theorem dRec_adapted_of_succ {γ : ℝ} {u : ℕ → Ω → ℝ} {d0 : Ω → ℝ} (h0 : 𝔼.E 0 d0 = d0)
    (hu : ∀ t, 𝔼.E (t + 1) (u t) = u t) : 𝔼.Adapted (dRec γ u d0) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    change 𝔼.E (t + 1) (γ • dRec γ u d0 t + u t) = γ • dRec γ u d0 t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, hu t]

/-! ### Locally Ricardian tax rules (the boundedness criterion) -/

/-- Woodford (2003), p. 312 (restated from the Woodford Chapter 4 project; the boundedness
criterion for passive fiscal policy, Cochrane (2023), §22.7, p. 508): a tax rule is **locally
Ricardian** if, substituted into (4.5), it keeps real debt bounded for every small initial debt
and all small paths of `π`, `Ŷ`, `î`, `Ĝ`, `v`. -/
def LocallyRicardian (Ω : Type*) (β bb τb τg τπ τy τi : ℝ) : Prop :=
  ∃ δ > 0, ∀ (b0 : ℝ) (d π Y i G v : ℕ → Ω → ℝ), |b0| ≤ δ →
    (∀ t ω, |π t ω| ≤ δ ∧ |Y t ω| ≤ δ ∧ |i t ω| ≤ δ ∧ |G t ω| ≤ δ ∧ |v t ω| ≤ δ) →
    d 0 = (fun _ => b0) → Debt45 β bb τb τg τπ τy τi d π G Y i v → BoundedProc d

/-- Woodford (2003), p. 313 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): a tax rule (4.4) is locally Ricardian iff `|β⁻¹(1 − τ_b)| < 1`. -/
theorem locallyRicardian_iff [Nonempty Ω] {β bb τb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb τb τg τπ τy τi ↔ |β⁻¹ * (1 - τb)| < 1 := by
  set γ := β⁻¹ * (1 - τb) with hγ
  constructor
  · intro hR
    by_contra hcon
    have h1 : 1 ≤ |γ| := not_lt.mp hcon
    obtain ⟨δ, hδ, hR⟩ := hR
    set ε := δ / (1 + β) with hε
    have hε0 : 0 < ε := div_pos hδ (by linarith)
    have hεβ : β * ε ≤ δ := by
      rw [hε, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
    have habs : ∀ n : ℕ, |s ^ n| = 1 := by
      intro n; rw [abs_pow]
      have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
      rw [this, one_pow]
    set u : ℕ → Ω → ℝ := fun t _ => ε * s ^ (t + 1) with hu
    set d := dRec γ u 0 with hd
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := fun t => rfl
    have hB := hR 0 d 0 0 0 0 (fun t _ => -(β * ε * s ^ (t + 1))) (by simp [hδ.le])
      (fun t ω => by
        refine ⟨by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], ?_⟩
        rw [abs_neg, abs_mul, habs, mul_one, abs_of_pos (mul_pos hβ hε0)]
        exact hεβ)
      (by funext ω; rfl) (fun t => by
        rw [hrec t]
        funext ω
        simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul]
        field_simp
        ring)
    obtain ⟨M, hM⟩ := hB
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have hgrow := rec_unbounded h1 hε0.le (d := d) (fun t => hrec t) rfl
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have := hgrow n ω
    have := hM n ω
    rw [div_lt_iff₀ hε0] at hn
    linarith
  · intro hγ1
    refine ⟨1, one_pos, fun b0 d π Y i G v hb0 hin hd0 hd => ?_⟩
    set U := β⁻¹ * (|bb + τπ| + |1 - τg| + |τy|) + |bb - β⁻¹ * τi| + β⁻¹ with hU
    have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
    have hU0 : 0 ≤ U := by positivity
    set u : ℕ → Ω → ℝ := fun t => β⁻¹ • (-(bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
      (bb - β⁻¹ * τi) • i t - β⁻¹ • v t with hu
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := by
      intro t
      rw [hd t]
      funext ω
      simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hub : ∀ t ω, |u t ω| ≤ U := by
      intro t ω
      obtain ⟨a1, a2, a3, a4, a5⟩ := hin t ω
      simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have q1 : |-(bb + τπ) * π t ω + (1 - τg) * G t ω - τy * Y t ω| ≤
          |bb + τπ| + |1 - τg| + |τy| := by
        refine (abs_sub _ _).trans ?_
        refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_neg]
        nlinarith [abs_nonneg (bb + τπ), abs_nonneg (1 - τg), abs_nonneg τy,
          mul_le_mul_of_nonneg_left a1 (abs_nonneg (bb + τπ)),
          mul_le_mul_of_nonneg_left a4 (abs_nonneg (1 - τg)),
          mul_le_mul_of_nonneg_left a2 (abs_nonneg τy)]
      refine (abs_sub _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβi]
      nlinarith [mul_le_mul_of_nonneg_left q1 hβi.le,
        mul_le_mul_of_nonneg_left a3 (abs_nonneg (bb - β⁻¹ * τi)),
        mul_le_mul_of_nonneg_left a5 hβi.le]
    exact ⟨1 + U / (1 - |γ|), rec_bounded hγ1 zero_le_one hU0 hub hrec
      (fun ω => by rw [hd0]; simpa using hb0)⟩

/-- Woodford (2003), p. 314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `0 < β` and `τ_b ≤ 1`, `|β⁻¹(1 − τ_b)| < 1` iff `τ_b > 1 − β`. -/
theorem ricardian_iff_taub {β τb : ℝ} (hβ : 0 < β) (hτ : τb ≤ 1) :
    |β⁻¹ * (1 - τb)| < 1 ↔ 1 - β < τb := by
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ.le) (by linarith)), ← div_eq_inv_mul,
    div_lt_one hβ]
  constructor <;> intro h <;> linarith

/-! ### Regime boundaries -/

/-- Cochrane (2023), pp. 495, 501, 512 (survey error E12): fiscal policy is active under the
transversality criterion, `|1 − γ| ≥ 1`, exactly when `γ ≤ 0` or `γ ≥ 2`. -/
theorem one_le_abs_one_sub_iff (γ : ℝ) : 1 ≤ |1 - γ| ↔ γ ≤ 0 ∨ 2 ≤ γ := by
  constructor
  · intro h
    rcases le_abs'.mp h with h1 | h1
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith

/-- Cochrane (2023), pp. 512–513 (survey error E12): `|1 − γ| < 1` exactly when `0 < γ < 2`. -/
theorem abs_one_sub_lt_one_iff (γ : ℝ) : |1 - γ| < 1 ↔ 0 < γ ∧ γ < 2 := by
  rw [abs_sub_lt_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Limits of geometric sequences -/

/-- Cochrane (2023), p. 513 (the transversality condition on `qᵀ x`): `qᵀ x → 0` iff
`|q| < 1` or `x = 0`. -/
theorem tendsto_pow_mul_iff (q x : ℝ) :
    Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0) ↔ |q| < 1 ∨ x = 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hq, hx⟩ := hc
    have hb : ∀ T : ℕ, |x| ≤ |q ^ T * x| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg x) (one_le_pow₀ hq)
    have h0 : Tendsto (fun T : ℕ => |q ^ T * x|) atTop (𝓝 0) := by
      simpa using h.abs
    have : |x| ≤ 0 := ge_of_tendsto' h0 hb
    exact hx (abs_nonpos_iff.mp this)
  · rintro (h | h)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const x
    · simp [h]

/-- Cochrane (2023), p. 513 ("only one value … keeps debt from exploding"): if `|q| ≥ 1` and
`qᵀ x → 0` then `x = 0`. -/
theorem eq_zero_of_tendsto_pow_mul {q x : ℝ} (hq : 1 ≤ |q|)
    (h : Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0)) : x = 0 := by
  rcases (tendsto_pow_mul_iff q x).mp h with h1 | h1
  · linarith
  · exact h1

/-- Cochrane (2023), p. 513 (debt growing more slowly than the interest rate is consistent with
the transversality condition): a stable recursion `y_{T+1} = q y_T + w_T` with `|q| < 1` and
geometrically vanishing inputs `|w_T| ≤ C rᵀ`, `0 ≤ r < 1`, tends to zero. -/
theorem tendsto_zero_of_stable_rec {q r C : ℝ} (hq : |q| < 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {y w : ℕ → ℝ} (hw : ∀ T, |w T| ≤ C * r ^ T) (hy : ∀ T, y (T + 1) = q * y T + w T) :
    Tendsto y atTop (𝓝 0) := by
  set R := max |q| r with hR
  have hR0 : 0 ≤ R := le_max_of_le_right hr0
  have hR1 : R < 1 := max_lt hq hr1
  have hC : 0 ≤ C := by
    have := (abs_nonneg (w 0)).trans (hw 0)
    simpa using this
  have hbound : ∀ T, |y T| ≤ R ^ T * |y 0| + C * T * R ^ (T - 1) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hy T]
      have hqR : |q| ≤ R := le_max_left _ _
      have hrR : r ^ T ≤ R ^ T := pow_le_pow_left₀ hr0 (le_max_right _ _) T
      have h1 : |q * y T + w T| ≤ R * |y T| + C * R ^ T := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ((hw T).trans ?_))
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hqR (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hrR hC
      refine h1.trans ?_
      have h2 : R * |y T| ≤ R * (R ^ T * |y 0| + C * T * R ^ (T - 1)) :=
        mul_le_mul_of_nonneg_left ih hR0
      rcases T with _ | T
      · simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_tsub] at h2 ⊢
        push_cast
        nlinarith
      · simp only [Nat.add_sub_cancel] at h2 ⊢
        push_cast at h2 ⊢
        have e : R * (R ^ (T + 1) * |y 0| + C * (T + 1) * R ^ T) + C * R ^ (T + 1) =
            R ^ (T + 1 + 1) * |y 0| + C * (T + 1 + 1) * R ^ (T + 1) := by ring
        linarith
  have hlim1 : Tendsto (fun T : ℕ => R ^ T * |y 0|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1).mul_const |y 0|
  have hlim2 : Tendsto (fun T : ℕ => C * T * R ^ (T - 1)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have h1 : Tendsto (fun T : ℕ => (T : ℝ) * R ^ T + R ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_self_mul_const_pow_of_lt_one hR0 hR1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1)
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => ?_) (by simpa using hlim1.add hlim2)
  rw [sub_zero, Real.norm_eq_abs]
  exact hbound T

/-! ### Active money: bounded solutions of `E_t e_{t+1} = φ e_t` -/

/-- Cochrane (2023), (22.1), p. 495, and (16.19), p. 371 (active money, `|φ| > 1`): a bounded
process with `E_t e_{t+1} = φ e_t` is identically zero. -/
theorem zero_of_E_succ_eq_smul {φ : ℝ} (hφ : 1 < |φ|) {e : ℕ → Ω → ℝ}
    (hb : BoundedProc e) (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t) : e = 0 := by
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, abs_zero] at hφ; linarith
  have hinv : |φ⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  refine 𝔼.forward_unique hinv (u := 0) (fun t => ?_) (fun t => ?_) hb ⟨0, fun _ _ => by simp⟩
  · rw [he t, smul_smul, inv_mul_cancel₀ hφ0, one_smul, Pi.zero_apply, add_zero]
  · simp

end Cochrane.ObservationalEquivalence.FiscalRec

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The government debt valuation equation in the frictionless linear model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–497,
eq. (22.2) (and (16.20)–(16.22), p. 373): the frictionless linear model
`i_t = E_t π_{t+1}` (`Fisher`) and `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`Flow`), with
`v_t` the real value of debt at the end of date `t` and `s̃` the real primary surplus.

"The government debt valuation formula results from iterating (22.2) forward and imposing the
transversality condition" (p. 495), and "the government debt valuation equation is an equilibrium
condition for all of these models" (p. 497). This module proves both: the valuation equation
`v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j}` and the unexpected-inflation identity
`ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑_{j ≥ 0} ρʲ s̃_{t+1+j}` follow from the Fisher equation, the flow
condition and the transversality condition alone — no policy rule is used, so they hold in every
regime (`valuation_all_regimes` in `StarredModel`).

## Main results

* `flow_iff_surprise`: given the Fisher equation, (22.2) is
  `ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}` ((16.22), (22.11)).
* `E_realReturn`: the ex-post real return `r_{t+1} = i_t − π_{t+1}` has `E_t r_{t+1+j} = 0`.
* `telescope` (ex post) and `telescope_E`:
  `v_t = ∑_{j<T} ρʲ E_t s̃_{t+1+j} + ρᵀ E_t v_{t+T}`.
* `tvc_iff_valuation`: the transversality condition `ρᵀ E_t v_{t+T} → 0` holds iff the partial
  sums of the present value converge to `v_t` (both directions); `valuation_tsum`,
  `valuation_E_exPost`: with bounded surpluses, `v_t = ∑' ρʲ E_t s̃_{t+1+j} = E_t ∑' ρʲ s̃_{t+1+j}`.
* `unexpected_inflation`, `unexpected_inflation_news`:
  `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`.
* `tvc_of_bounded`: bounded debt satisfies the transversality condition.

The innovation operator `innov` (`ΔE_{t+1}`), the ex-post present value `pvExPost` and the
flow-iteration lemmas `flow_telescope`, `pv_of_flow` are shared with chain B and live in
`ExpectationTools`; `surprise_eq_innov` identifies the surprise of an adapted process with its
innovation.
-/

namespace Cochrane.ObservationalEquivalence.Valuation

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply pvExPost
  summable_pow_mul_of_bounded tendsto_pow_mul_of_bounded flow_telescope pv_of_flow)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Definitions -/

/-- Cochrane (2023), eq. (22.2), p. 495 (and (16.20), p. 373): the Fisher equation
`i_t = E_t π_{t+1}`. -/
def Fisher (i π : ℕ → Ω → ℝ) : Prop := ∀ t, i t = 𝔼.E t (π (t + 1))

/-- Cochrane (2023), eq. (22.2), p. 495, and (22.11), p. 501: the linearised flow condition
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def Flow (ρ : ℝ) (v i π s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), (22.1), p. 495: unexpected inflation `ΔE_{t+1} x_{t+1} = x_{t+1} − E_t x_{t+1}`
of an adapted process. -/
def surprise (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := x (t + 1) - 𝔼.E t (x (t + 1))

/-- Cochrane (2023), §22.1, p. 495 (the real return in (22.2)): the ex-post real return on
one-period nominal debt, `r_{t+1} = i_t − π_{t+1}`. -/
def realReturn (i π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := i t - π (t + 1)

/-- Cochrane (2023), §22.1, p. 495 ("imposing the transversality condition"): at every date and
state, `lim_{T→∞} ρᵀ E_t v_{t+T} = 0`. -/
def TVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), §22.1, p. 495: the present value of surpluses as seen at date `m`,
`E_m ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`, written termwise as a genuine infinite sum. -/
noncomputable def pvE (ρ : ℝ) (s : ℕ → Ω → ℝ) (m t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω

/-! ### Expectational facts -/

/-- Cochrane (2023), (22.1), p. 495: surprises are unforecastable, `E_t ΔE_{t+1} x_{t+1} = 0`. -/
theorem E_surprise (x : ℕ → Ω → ℝ) (t : ℕ) : 𝔼.E t (surprise 𝔼 x t) = 0 := by
  rw [surprise, map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), (22.1), p. 495: later surprises are unforecastable,
`E_t ΔE_{t+k+1} x_{t+k+1} = 0`. -/
theorem E_surprise_later (x : ℕ → Ω → ℝ) (t k : ℕ) : 𝔼.E t (surprise 𝔼 x (t + k)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), E_surprise, map_zero]

/-- Cochrane (2023), (22.1), p. 495: for an adapted process the surprise is the revision of
expectations, `x_{t+1} − E_t x_{t+1} = ΔE_{t+1} x_{t+1}`. -/
theorem surprise_eq_innov {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    surprise 𝔼 x t = innov 𝔼 t (x (t + 1)) := by
  rw [surprise, innov_apply, hx (t + 1)]

/-- Cochrane (2023), (22.2), p. 495: with the Fisher equation the flow condition reads
`ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}` ((16.22), p. 373; (22.10)–(22.11), p. 501). -/
theorem flow_iff_surprise {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) :
    Flow ρ v i π s ↔ ∀ t, ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) := by
  refine forall_congr' fun t => ?_
  rw [hF t, surprise]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), (22.2), p. 495: the flow condition in terms of the ex-post real return,
`ρ v_{t+1} = v_t + r_{t+1} − s̃_{t+1}`. -/
theorem flow_iff_realReturn {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} :
    Flow ρ v i π s ↔ ∀ t, ρ • v (t + 1) = v t + realReturn i π t - s (t + 1) := by
  refine forall_congr' fun t => ?_
  rw [realReturn]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), §22.1, p. 495: with the Fisher equation, expected real returns are zero at
every horizon, `E_t r_{t+1+j} = 0` (constant real rate in the frictionless model). -/
theorem E_realReturn {i π : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) (t j : ℕ) :
    𝔼.E t (realReturn i π (t + j)) = 0 := by
  rw [realReturn, hF (t + j), map_sub, 𝔼.tower (Nat.le_add_right t j), sub_self]

/-! ### Iterating the flow condition -/

omit 𝔼 in
/-- Cochrane (2023), §22.1, p. 495 (iterating (22.2) forward, ex post):
`v_t = ∑_{j<T} ρʲ (s̃_{t+1+j} − r_{t+1+j}) + ρᵀ v_{t+T}`. -/
theorem telescope {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (h : Flow ρ v i π s) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • (s (t + 1 + j) - realReturn i π (t + j)) +
      ρ ^ T • v (t + T) := by
  rw [flow_telescope (ρ := ρ) (v := v) (y := fun k => s (k + 1) - realReturn i π k)
    (fun k => by rw [h k, realReturn]; abel) t T]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show t + j + 1 = t + 1 + j by omega]

/-- Cochrane (2023), §22.1, p. 495 (iterating (22.2) forward under expectations):
`v_t = ∑_{j<T} ρʲ E_t s̃_{t+1+j} + ρᵀ E_t v_{t+T}`. -/
theorem telescope_E {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • 𝔼.E t (s (t + 1 + j)) + ρ ^ T • 𝔼.E t (v (t + T)) := by
  have h1 := congrArg (𝔼.E t) (telescope h t T)
  rw [hv t] at h1
  rw [h1, map_add, map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_sub, E_realReturn 𝔼 hF t j, sub_zero]

/-- Cochrane (2023), §22.1, p. 495: iterating (22.2) and imposing the transversality condition
gives the valuation equation: the partial sums `∑_{j<T} ρʲ E_t s̃_{t+1+j}` converge to `v_t`. -/
theorem valuation_of_tvc {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) atTop
      (𝓝 (v t ω)) := by
  have hy : ∀ k, ρ • v (k + 1) = v k - (s (k + 1) - realReturn i π (k + 1 - 1)) :=
    fun k => by
      rw [Nat.add_sub_cancel, h k, realReturn]
      abel
  refine (pv_of_flow 𝔼 (y := fun m => s m - realReturn i π (m - 1)) hy t (hv t) ω
    (htvc t ω)).congr fun T =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [show t + 1 + j - 1 = t + j by omega, map_sub, Pi.sub_apply, E_realReturn 𝔼 hF t j,
    Pi.zero_apply, sub_zero]

/-- Cochrane (2023), §22.1, p. 495 (converse): if the present value converges to `v_t` at every
date and state, the transversality condition holds. -/
theorem tvc_of_valuation {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (hpv : ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
      atTop (𝓝 (v t ω))) : TVC 𝔼 ρ v := by
  intro t ω
  have hT : ∀ T, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω := by
    intro T
    have := congrFun (telescope_E 𝔼 hF h hv t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
    linarith
  simp_rw [hT]
  simpa using (tendsto_const_nhds (x := v t ω)).sub (hpv t ω)

/-- Cochrane (2023), §22.1, p. 495 (both directions): given the Fisher equation and the flow
condition, the transversality condition holds iff the valuation equation holds at every date. -/
theorem tvc_iff_valuation {ρ : ℝ} {v i π s : ℕ → Ω → ℝ} (hF : Fisher 𝔼 i π)
    (h : Flow ρ v i π s) (hv : 𝔼.Adapted v) :
    TVC 𝔼 ρ v ↔ ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
      atTop (𝓝 (v t ω)) :=
  ⟨fun htvc => valuation_of_tvc 𝔼 hF h hv htvc, tvc_of_valuation 𝔼 hF h hv⟩

/-! ### Genuine infinite sums -/

/-- Cochrane (2023), §22.1, p. 495: with `|ρ| < 1` and bounded surpluses the present value is
absolutely summable. -/
theorem pvE_summable {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (m t : ℕ) (ω : Ω) : Summable (fun j => ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω) :=
  summable_pow_mul_of_bounded hρ (x := fun j => 𝔼.E m (s (t + 1 + j)) ω)
    fun j => 𝔼.abs_E_le (hs (t + 1 + j)) m ω

/-- Cochrane (2023), §22.1, p. 495: the present value of bounded surpluses is bounded by
`M/(1 − |ρ|)`. -/
theorem abs_pvE_le {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (m t : ℕ) (ω : Ω) : |pvE 𝔼 ρ s m t ω| ≤ M / (1 - |ρ|) := by
  have hg : HasSum (fun j : ℕ => M * |ρ| ^ j) (M / (1 - |ρ|)) := by
    have := (hasSum_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun j => ρ ^ j * 𝔼.E m (s (t + 1 + j)) ω) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1 + j)) m ω)
      (pow_nonneg (abs_nonneg ρ) j)
  simpa [pvE, Real.norm_eq_abs] using this

/-- Cochrane (2023), §22.1, p. 495: the valuation equation as a genuine infinite sum,
`v_t = ∑_{j ≥ 0} ρʲ E_t s̃_{t+1+j}` (bounded surpluses, `|ρ| < 1`). -/
theorem valuation_tsum {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) : v t = pvE 𝔼 ρ s t t := by
  funext ω
  exact tendsto_nhds_unique (valuation_of_tvc 𝔼 hF h hv htvc t ω)
    (pvE_summable 𝔼 hρ hs t t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), §22.1, p. 495: `E_m` of the ex-post present value is the present value of
expected surpluses, `E_m ∑ ρʲ s̃_{t+1+j} = ∑ ρʲ E_m s̃_{t+1+j}` (`|ρ| < 1`, bounded `s̃`). -/
theorem E_pvExPost {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (m t : ℕ) : 𝔼.E m (pvExPost ρ s t) = pvE 𝔼 ρ s m t := by
  funext ω
  have hb : ∀ j ω', |(fun j ω => ρ ^ j * s (t + 1 + j) ω) j ω'| ≤ |ρ| ^ j * M :=
    fun j ω' => by
      simp only
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hs _ ω') (pow_nonneg (abs_nonneg ρ) j)
  have h1 := 𝔼.E_tsum (abs_nonneg ρ) hρ hb m ω
  change 𝔼.E m (fun ω' => ∑' j, ρ ^ j * s (t + 1 + j) ω') ω = _
  rw [h1]
  refine tsum_congr fun j => ?_
  change 𝔼.E m (ρ ^ j • s (t + 1 + j)) ω = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), §22.1, p. 495: the valuation equation in the book's form
`v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`. -/
theorem valuation_E_exPost {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) : v t = 𝔼.E t (pvExPost ρ s t) := by
  rw [E_pvExPost 𝔼 hρ hs, valuation_tsum 𝔼 hρ hs hF h hv htvc]

/-- Cochrane (2023), §22.1, p. 495: splitting off the first term,
`E_{t+1} ∑ ρʲ s̃_{t+1+j} = s̃_{t+1} + ρ E_{t+1} ∑ ρʲ s̃_{t+2+j}` (adapted, bounded `s̃`). -/
theorem pvE_succ_split {ρ M : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (hsa : 𝔼.Adapted s) (t : ℕ) :
    pvE 𝔼 ρ s (t + 1) t = s (t + 1) + ρ • pvE 𝔼 ρ s (t + 1) (t + 1) := by
  funext ω
  simp only [pvE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [(pvE_summable 𝔼 hρ hs (t + 1) t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero,
    hsa (t + 1), ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), §22.1, p. 495 and (16.24), p. 373: unexpected inflation equals minus the
revision in the present value of surpluses,
`ΔE_{t+1}π_{t+1} = −(E_{t+1} − E_t) ∑_{j ≥ 0} ρʲ s̃_{t+1+j}`. -/
theorem unexpected_inflation {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -(pvE 𝔼 ρ s (t + 1) t - pvE 𝔼 ρ s t t) := by
  have h1 := ((flow_iff_surprise 𝔼 hF).mp h) t
  have e1 := valuation_tsum 𝔼 hρ hs hF h hv htvc t
  have e2 := valuation_tsum 𝔼 hρ hs hF h hv htvc (t + 1)
  rw [pvE_succ_split 𝔼 hρ hs hsa t, ← e2, ← e1]
  funext ω
  have := congrFun h1 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
  linarith

/-- Cochrane (2023), §22.1, p. 495 (`|ρ| < 1`): unexpected inflation is minus the news about
the ex-post present value of surpluses, `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`. -/
theorem unexpected_inflation_news {ρ M : ℝ} (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hF : Fisher 𝔼 i π) (h : Flow ρ v i π s)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -innov 𝔼 t (pvExPost ρ s t) := by
  rw [unexpected_inflation 𝔼 hρ hs hsa hF h hv htvc t, innov_apply, E_pvExPost 𝔼 hρ hs,
    E_pvExPost 𝔼 hρ hs]

/-- Cochrane (2023), §22.1, p. 495: bounded debt satisfies the transversality condition when
`|ρ| < 1`. -/
theorem tvc_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v) :
    TVC 𝔼 ρ v := by
  obtain ⟨M, hM⟩ := hv
  intro t ω
  exact tendsto_pow_mul_of_bounded hρ (x := fun T => 𝔼.E t (v (t + T)) ω)
    fun T => 𝔼.abs_E_le (hM (t + T)) t ω

/-- Cochrane (2023), §22.1, p. 495: the transversality condition is linear — it holds for a
difference of two processes that satisfy it. -/
theorem tvc_sub {ρ : ℝ} {v w : ℕ → Ω → ℝ} (hv : TVC 𝔼 ρ v) (hw : TVC 𝔼 ρ w) :
    TVC 𝔼 ρ (fun t => v t - w t) := by
  intro t ω
  have := (hv t ω).sub (hw t ω)
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  simp only [map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), §22.1, p. 495: the transversality condition holds for a sum of two processes
that satisfy it. -/
theorem tvc_add {ρ : ℝ} {v w : ℕ → Ω → ℝ} (hv : TVC 𝔼 ρ v) (hw : TVC 𝔼 ρ w) :
    TVC 𝔼 ρ (fun t => v t + w t) := by
  intro t ω
  have := (hv t ω).add (hw t ω)
  rw [add_zero] at this
  refine this.congr fun T => ?_
  simp only [map_add, Pi.add_apply]
  ring

end Cochrane.ObservationalEquivalence.Valuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The starred-form policy rules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.6, eqs. (16.20)–(16.24),
p. 373; Chapter 22, §22.1, eqs. (22.1)–(22.2), p. 495, and §22.3, eqs. (22.7)–(22.11), p. 501;
Chapter 23, eqs. (23.1)–(23.4), p. 512; Chapter 24, eqs. (24.1)–(24.2), p. 520.

The frictionless model `i_t = E_t π_{t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` is closed
by monetary and fiscal policy written around a *target* path `(π*, i*, v*, s̃*)` (the starred
variables):

* `i_t = i*_t + φ (π_t − π*_t)` ((16.19), (22.1); with `i*_t = θπ*_t + u_{i,t}`, (22.8)),
* `s̃_{t+1} = s̃*_{t+1} + γ (v_t − v*_t)` with `s̃*_{t+1} = α v*_t + u_{s,t+1}` ((22.1), (22.9)),

where the target is itself consistent with the Fisher equation and the flow condition
((16.21), (22.10)). `φ` and `γ` describe behaviour *off* the target: they are the
equilibrium-selection parameters.

## Reading of the starred debt equation

As printed, (16.21) and (22.1)/(22.10) drive the starred debt `v*` with the *actual* surplus
`s̃_{t+1}`. Here the target is an exogenous consistent path: `v*` is driven by the target surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}` (`Consistent`, `StarredSurplus`). On the target both readings
coincide; off the target they differ. Under the printed reading `γ` drops out of the gap
dynamics and fiscal policy is passive iff `γ = α` (`LeeperRegions.literal_tvc_iff`); under the
reading used here fiscal policy is passive iff `0 < γ < 2` (`Equivalence.unique_iff`).

## Timing and the initial condition

Dates are `t : ℕ`. The flow condition links `v_t, i_t` to `π_{t+1}, v_{t+1}, s̃_{t+1}` for
`t ≥ 0`. At date 0 the inherited nominal debt and the date-0 surplus are common to every
candidate path, so the date-0 flow condition `ρ v_0 = v_{−1} + i_{−1} − π_0 − s̃_0` becomes the
initial condition `ρ v_0 + π_0 = ρ v*_0 + π*_0` (`Eqm`): a date-0 jump in inflation must be
matched by a change in the value of debt. This keeps the date-0 unexpected inflation of the book
in the model even under perfect foresight. The condition `π_0 = π*_0` is not imposed: in the
determinate regions it is derived (`Equivalence.unique_of_determinate`).

## Main definitions and results

* `Outcome`: a path `(π, i, v, s̃)`; `Consistent`: the target obeys the Fisher equation and the
  flow condition; `Admissible`: adapted, bounded inflation, transversality condition for debt.
* `Eqm`: an equilibrium of the `(φ, γ)` starred system around a target.
* `StarredSurplus`, `ThetaRule`: the parametrisations `s̃*_{t+1} = α v*_t + u_{s,t+1}` and
  `i*_t = θπ*_t + u_{i,t}`; `eq22_8`, `eq22_9`, `consistent_iff_eq22_10`, `eq23_4_starred`.
* `starred_eqm`: the target is an equilibrium for every `(φ, γ)`.
* `deviation_dynamics`: deviations `e = π − π*`, `d = v − v*` obey `E_t e_{t+1} = φ e_t`,
  `ρ d_{t+1} = (1 − γ) d_t − ΔE_{t+1} e_{t+1}`, `ρ d_0 + e_0 = 0`; `ofDev`, `ofDev_eqm`,
  `eq_ofDev`: every solution of these deviation equations gives an equilibrium and every
  equilibrium arises this way.
* `observables_eq16_23_24`: on the target the observables obey (16.23)–(16.24).
* `valuation_all_regimes` (p. 497): every admissible equilibrium of every `(φ, γ)` system
  satisfies the government debt valuation equation.
* `LeeperEqm`, `eq23_4`: the unstarred Leeper model (22.3)–(22.6) = (23.1)–(23.4) (with the `ρ`
  that (22.6) omits, survey error E13) and the substitution (23.4) of p. 512.
* `rule24_1_printed` (survey error E14): the printed rule (24.1) `i = θπ_t + φ(π_t − π*_t) + u` is
  the starred rule with target rate `θπ*_t + u` and off-target coefficient `θ + φ`.
-/

namespace Cochrane.ObservationalEquivalence.StarredModel

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation

variable (Ω : Type*)

/-- Cochrane (2023), (22.1)–(22.2), p. 495: a path of the observables — inflation `π_t`, the
nominal rate `i_t`, the real value of debt `v_t` and the real primary surplus `s̃_t`. -/
structure Outcome where
  /-- Inflation `π_t`. -/
  pi : ℕ → Ω → ℝ
  /-- The nominal interest rate `i_t`. -/
  i : ℕ → Ω → ℝ
  /-- The real value of government debt at the end of date `t`, `v_t`. -/
  v : ℕ → Ω → ℝ
  /-- The real primary surplus `s̃_t`. -/
  s : ℕ → Ω → ℝ

variable {Ω} (𝔼 : ExpectationSystem Ω)

omit 𝔼 in
/-- Cochrane (2023), (22.1), p. 495: two paths are equal when their four components are. -/
theorem outcome_ext {x y : Outcome Ω} (h1 : x.pi = y.pi) (h2 : x.i = y.i) (h3 : x.v = y.v)
    (h4 : x.s = y.s) : x = y := by
  cases x
  cases y
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-! ### Definitions -/

/-- Cochrane (2023), (16.21), p. 373, and (22.10), p. 501: the target path is consistent with
the model — `i*_t = E_t π*_{t+1}` and `ρ v*_{t+1} = v*_t + i*_t − π*_{t+1} − s̃*_{t+1}`. -/
def Consistent (ρ : ℝ) (tg : Outcome Ω) : Prop :=
  Fisher 𝔼 tg.i tg.pi ∧ Flow ρ tg.v tg.i tg.pi tg.s

/-- Cochrane (2023), §22.1, p. 495 (the equilibrium criterion): inflation and debt are adapted,
inflation is bounded ("the rule against nominal explosions", p. 508) and debt satisfies the
transversality condition. -/
def Admissible (ρ : ℝ) (x : Outcome Ω) : Prop :=
  𝔼.Adapted x.pi ∧ 𝔼.Adapted x.v ∧ BoundedProc x.pi ∧ TVC 𝔼 ρ x.v

/-- Cochrane (2023), (16.20)–(16.22), p. 373, and (22.1)–(22.2), p. 495: `x` is an equilibrium of
the starred system with off-target coefficients `φ` (money) and `γ` (fiscal) around the target
`tg`: the Fisher equation, `i_t = i*_t + φ(π_t − π*_t)`,
`s̃_{t+1} = s̃*_{t+1} + γ(v_t − v*_t)` (`s̃_0 = s̃*_0`), the flow condition, and the common
inherited debt at date 0, `ρ v_0 + π_0 = ρ v*_0 + π*_0`. -/
def Eqm (ρ φ γ : ℝ) (tg x : Outcome Ω) : Prop :=
  Fisher 𝔼 x.i x.pi ∧ (∀ t, x.i t = tg.i t + φ • (x.pi t - tg.pi t)) ∧ x.s 0 = tg.s 0 ∧
    (∀ t, x.s (t + 1) = tg.s (t + 1) + γ • (x.v t - tg.v t)) ∧ Flow ρ x.v x.i x.pi x.s ∧
    ρ • x.v 0 + x.pi 0 = ρ • tg.v 0 + tg.pi 0

/-- Cochrane (2023), (22.1), p. 495, and (22.9), p. 501: the starred surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}`. -/
def StarredSurplus (α : ℝ) (vS us sS : ℕ → Ω → ℝ) : Prop :=
  ∀ t, sS (t + 1) = α • vS t + us (t + 1)

/-- Cochrane (2023), (22.8), p. 501: the target interest rate `i*_t = θπ*_t + u_{i,t}`. -/
def ThetaRule (θ : ℝ) (piS ui iS : ℕ → Ω → ℝ) : Prop :=
  ∀ t, iS t = θ • piS t + ui t

/-! ### The equations of the starred system -/

omit 𝔼 in
/-- Cochrane (2023), eq. (22.8), p. 501: with `i*_t = θπ*_t + u_{i,t}` the monetary rule reads
`i_t = θπ*_t + φ(π_t − π*_t) + u_{i,t}`. -/
theorem eq22_8 {φ θ : ℝ} {tg x : Outcome Ω} {ui : ℕ → Ω → ℝ} (hθ : ThetaRule θ tg.pi ui tg.i)
    (hm : ∀ t, x.i t = tg.i t + φ • (x.pi t - tg.pi t)) (t : ℕ) :
    x.i t = θ • tg.pi t + φ • (x.pi t - tg.pi t) + ui t := by
  rw [hm t, hθ t]
  abel

omit 𝔼 in
/-- Cochrane (2023), eq. (22.9), p. 501 (and (24.2), p. 520): with `s̃*_{t+1} = α v*_t + u_{s,t+1}`
the fiscal rule reads `s̃_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`. -/
theorem eq22_9 {γ α : ℝ} {tg x : Outcome Ω} {us : ℕ → Ω → ℝ} (hα : StarredSurplus α tg.v us tg.s)
    (hs : ∀ t, x.s (t + 1) = tg.s (t + 1) + γ • (x.v t - tg.v t)) (t : ℕ) :
    x.s (t + 1) = α • tg.v t + γ • (x.v t - tg.v t) + us (t + 1) := by
  rw [hs t, hα t]
  abel

/-- Cochrane (2023), eq. (22.10), p. 501 (and (16.21), p. 373): a target obeying the Fisher
equation is consistent iff `ρ v*_{t+1} = v*_t − ΔE_{t+1}π*_{t+1} − s̃*_{t+1}`. -/
theorem consistent_iff_eq22_10 {ρ : ℝ} {tg : Outcome Ω} (hF : Fisher 𝔼 tg.i tg.pi) :
    Consistent 𝔼 ρ tg ↔
      ∀ t, ρ • tg.v (t + 1) = tg.v t - surprise 𝔼 tg.pi t - tg.s (t + 1) := by
  unfold Consistent
  rw [flow_iff_surprise 𝔼 hF]
  exact ⟨fun h => h.2, fun h => ⟨hF, h⟩⟩

/-- Cochrane (2023), (22.10), p. 501, and the substitution of (23.4), p. 512, for the target:
`ρ v*_{t+1} = (1 − α) v*_t − ΔE_{t+1}π*_{t+1} − u_{s,t+1}`. -/
theorem eq23_4_starred {ρ α : ℝ} {tg : Outcome Ω} {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (hα : StarredSurplus α tg.v us tg.s) (t : ℕ) :
    ρ • tg.v (t + 1) = (1 - α) • tg.v t - surprise 𝔼 tg.pi t - us (t + 1) := by
  rw [((consistent_iff_eq22_10 𝔼 hc.1).mp hc) t, hα t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), §16.6, p. 373, and §22.1, p. 495 ("in equilibrium, starred variables equal
their unstarred counterparts"): a consistent target is an equilibrium for every `φ` and `γ`. -/
theorem starred_eqm {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) :
    Eqm 𝔼 ρ φ γ tg tg :=
  ⟨hc.1, fun t => by simp, rfl, fun t => by simp, hc.2, rfl⟩

/-- Cochrane (2023), (16.23)–(16.24), p. 373: in an equilibrium on the target debt path the
observables obey
`i_t = E_t π_{t+1}`, `s̃_{t+1} = α v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}`;
neither `φ` nor `γ` appears. -/
theorem observables_eq16_23_24 {ρ φ γ α : ℝ} {tg x : Outcome Ω} {us : ℕ → Ω → ℝ}
    (hα : StarredSurplus α tg.v us tg.s) (hx : Eqm 𝔼 ρ φ γ tg x) (hv : x.v = tg.v) :
    Fisher 𝔼 x.i x.pi ∧ (∀ t, x.s (t + 1) = α • x.v t + us (t + 1)) ∧
      ∀ t, ρ • x.v (t + 1) = x.v t - surprise 𝔼 x.pi t - x.s (t + 1) := by
  obtain ⟨hF, -, -, hs, hflow, -⟩ := hx
  refine ⟨hF, fun t => ?_, (flow_iff_surprise 𝔼 hF).mp hflow⟩
  rw [hs t, hv, sub_self, smul_zero, add_zero, hα t]

/-! ### Deviation dynamics -/

/-- Cochrane (2023), (22.1), p. 495: the deviation equations. In any equilibrium,
`e = π − π*` and `d = v − v*` satisfy `E_t e_{t+1} = φ e_t`,
`ρ d_{t+1} = (1 − γ) d_t − ΔE_{t+1}e_{t+1}` and `ρ d_0 + e_0 = 0`. -/
theorem deviation_dynamics {ρ φ γ : ℝ} {tg x : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (hx : Eqm 𝔼 ρ φ γ tg x) :
    (∀ t, 𝔼.E t (x.pi (t + 1) - tg.pi (t + 1)) = φ • (x.pi t - tg.pi t)) ∧
      (∀ t, ρ • (x.v (t + 1) - tg.v (t + 1)) =
        (1 - γ) • (x.v t - tg.v t) - surprise 𝔼 (fun t => x.pi t - tg.pi t) t) ∧
      ρ • (x.v 0 - tg.v 0) + (x.pi 0 - tg.pi 0) = 0 := by
  obtain ⟨hF, hm, -, hs, hflow, h0⟩ := hx
  obtain ⟨hFt, hflowt⟩ := hc
  have he : ∀ t, 𝔼.E t (x.pi (t + 1) - tg.pi (t + 1)) = φ • (x.pi t - tg.pi t) := by
    intro t
    rw [map_sub, ← hF t, ← hFt t, hm t, add_sub_cancel_left]
  refine ⟨he, fun t => ?_, ?_⟩
  · funext ω
    have h1 := congrFun (hflow t) ω
    have h2 := congrFun (hflowt t) ω
    have h3 := congrFun (hm t) ω
    have h4 := congrFun (hs t) ω
    have h5 := congrFun (he t) ω
    simp only [surprise, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 ⊢
    rw [h5]
    linear_combination h1 - h2 + h3 - h4
  · rw [smul_sub]
    rw [← sub_eq_zero] at h0
    rw [← h0]
    abel

/-- Cochrane (2023), (22.1), p. 495: the lagged deviation `d_{t−1}` entering the surplus at
date `t` (zero at date 0, when the surplus is the target surplus). -/
def lag (d : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => d t

/-- Cochrane (2023), (22.1), p. 495: the path built from the target and deviations `e`, `d`:
`π = π* + e`, `i = i* + φ e`, `v = v* + d`, `s̃_{t+1} = s̃*_{t+1} + γ d_t`. -/
def ofDev (φ γ : ℝ) (tg : Outcome Ω) (e d : ℕ → Ω → ℝ) : Outcome Ω where
  pi := fun t => tg.pi t + e t
  i := fun t => tg.i t + φ • e t
  v := fun t => tg.v t + d t
  s := fun t => tg.s t + γ • lag d t

/-- Cochrane (2023), (22.1), p. 495 (converse of `deviation_dynamics`): any deviations obeying
the deviation equations give an equilibrium of the `(φ, γ)` system. -/
theorem ofDev_eqm {ρ φ γ : ℝ} {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) {e d : ℕ → Ω → ℝ}
    (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    Eqm 𝔼 ρ φ γ tg (ofDev φ γ tg e d) := by
  obtain ⟨hFt, hflowt⟩ := hc
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, fun t => ?_, ?_⟩
  · change tg.i t + φ • e t = 𝔼.E t (tg.pi (t + 1) + e (t + 1))
    rw [map_add, he t, hFt t]
  · change tg.i t + φ • e t = tg.i t + φ • (tg.pi t + e t - tg.pi t)
    rw [add_sub_cancel_left]
  · change tg.s 0 + γ • (0 : Ω → ℝ) = tg.s 0
    rw [smul_zero, add_zero]
  · change tg.s (t + 1) + γ • d t = tg.s (t + 1) + γ • (tg.v t + d t - tg.v t)
    rw [add_sub_cancel_left]
  · change ρ • (tg.v (t + 1) + d (t + 1)) =
      (tg.v t + d t) + (tg.i t + φ • e t) - (tg.pi (t + 1) + e (t + 1)) -
        (tg.s (t + 1) + γ • d t)
    funext ω
    have h1 := congrFun (hflowt t) ω
    have h2 := congrFun (hd t) ω
    have h3 := congrFun (he t) ω
    simp only [surprise, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    rw [h3] at h2
    linear_combination h1 + h2
  · change ρ • (tg.v 0 + d 0) + (tg.pi 0 + e 0) = ρ • tg.v 0 + tg.pi 0
    rw [smul_add, ← sub_eq_zero]
    rw [← h0]
    abel

/-- Cochrane (2023), (22.1), p. 495: every equilibrium is the path built from its own
deviations, `x = ofDev φ γ tg (π − π*) (v − v*)`. -/
theorem eq_ofDev {ρ φ γ : ℝ} {tg x : Outcome Ω} (hx : Eqm 𝔼 ρ φ γ tg x) :
    x = ofDev φ γ tg (fun t => x.pi t - tg.pi t) (fun t => x.v t - tg.v t) := by
  obtain ⟨-, hm, hs0, hs, -, -⟩ := hx
  refine outcome_ext ?_ ?_ ?_ ?_
  · funext t; simp [ofDev]
  · funext t; simp only [ofDev]; rw [hm t]
  · funext t; simp [ofDev]
  · funext t
    rcases t with _ | t
    · simp only [ofDev, lag, smul_zero, add_zero]; exact hs0
    · simp only [ofDev, lag]; rw [hs t]

omit 𝔼 in
/-- Cochrane (2023), (22.1), p. 495: zero deviations give back the target. -/
theorem ofDev_zero (φ γ : ℝ) (tg : Outcome Ω) : ofDev φ γ tg 0 0 = tg := by
  refine outcome_ext ?_ ?_ ?_ ?_
  · funext t; simp [ofDev]
  · funext t; simp [ofDev]
  · funext t; simp [ofDev]
  · funext t
    rcases t with _ | t <;> simp [ofDev, lag]

/-- Cochrane (2023), §22.1, p. 495: the deviations of an admissible equilibrium from an
admissible target are adapted, inflation deviations are bounded, and debt deviations satisfy the
transversality condition. -/
theorem dev_admissible {ρ : ℝ} {tg x : Outcome Ω} (htg : Admissible 𝔼 ρ tg)
    (hx : Admissible 𝔼 ρ x) :
    𝔼.Adapted (fun t => x.pi t - tg.pi t) ∧ BoundedProc (fun t => x.pi t - tg.pi t) ∧
      𝔼.Adapted (fun t => x.v t - tg.v t) ∧ TVC 𝔼 ρ (fun t => x.v t - tg.v t) := by
  obtain ⟨hpa, hva, ⟨M, hM⟩, htvc⟩ := hx
  obtain ⟨hpa', hva', ⟨M', hM'⟩, htvc'⟩ := htg
  refine ⟨fun t => ?_, ⟨M + M', fun t ω => ?_⟩, fun t => ?_, tvc_sub 𝔼 htvc htvc'⟩
  · simp only [map_sub, hpa t, hpa' t]
  · simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))
  · simp only [map_sub, hva t, hva' t]

/-- Cochrane (2023), §22.1, p. 495: a path built from an admissible target and adapted
deviations, with bounded `e` and `d` satisfying the transversality condition, is admissible. -/
theorem ofDev_admissible {ρ φ γ : ℝ} {tg : Outcome Ω} (htg : Admissible 𝔼 ρ tg)
    {e d : ℕ → Ω → ℝ} (hea : 𝔼.Adapted e) (heb : BoundedProc e) (hda : 𝔼.Adapted d)
    (hdt : TVC 𝔼 ρ d) : Admissible 𝔼 ρ (ofDev φ γ tg e d) := by
  obtain ⟨hpa, hva, ⟨M, hM⟩, htvc⟩ := htg
  obtain ⟨K, hK⟩ := heb
  refine ⟨fun t => ?_, fun t => ?_, ⟨M + K, fun t ω => ?_⟩, tvc_add 𝔼 htvc hdt⟩
  · change 𝔼.E t (tg.pi t + e t) = tg.pi t + e t
    rw [map_add, hpa t, hea t]
  · change 𝔼.E t (tg.v t + d t) = tg.v t + d t
    rw [map_add, hva t, hda t]
  · change |tg.pi t ω + e t ω| ≤ M + K
    exact (abs_add_le _ _).trans (add_le_add (hM t ω) (hK t ω))

/-! ### The valuation equation holds in every regime -/

/-- Cochrane (2023), §22.1, p. 497 ("the government debt valuation equation is an equilibrium
condition for all of these models"): every admissible equilibrium of every `(φ, γ)` system —
active money, active fiscal or otherwise — with bounded adapted surpluses satisfies
`v_t = ∑ ρʲ E_t s̃_{t+1+j}` and `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`. -/
theorem valuation_all_regimes {ρ φ γ M : ℝ} (hρ : |ρ| < 1) {tg x : Outcome Ω}
    (hx : Eqm 𝔼 ρ φ γ tg x) (hadm : Admissible 𝔼 ρ x) (hs : ∀ t ω, |x.s t ω| ≤ M)
    (hsa : 𝔼.Adapted x.s) :
    (∀ t, x.v t = pvE 𝔼 ρ x.s t t) ∧
      ∀ t, surprise 𝔼 x.pi t = -(pvE 𝔼 ρ x.s (t + 1) t - pvE 𝔼 ρ x.s t t) :=
  ⟨fun t => valuation_tsum 𝔼 hρ hs hx.1 hx.2.2.2.2.1 hadm.2.1 hadm.2.2.2 t,
    fun t => unexpected_inflation 𝔼 hρ hs hsa hx.1 hx.2.2.2.2.1 hadm.2.1 hadm.2.2.2 t⟩

/-! ### The unstarred Leeper model, (22.3)–(22.6) = (23.1)–(23.4) -/

/-- Cochrane (2023), eqs. (22.3)–(22.6), p. 500, and (23.1)–(23.4), p. 512 (with the `ρ` of (23.4);
(22.6) omits it, survey error E13): `i_t = E_t π_{t+1}`, `i_t = φπ_t + u_{i,t}`,
`s̃_{t+1} = γ v_t + u_{s,t+1}` (`s̃_0 = u_{s,0}`), `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`,
and the inherited debt at date 0, `ρ v_0 + π_0 = K` with `K` known at date 0. -/
def LeeperEqm (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) (x : Outcome Ω) : Prop :=
  Fisher 𝔼 x.i x.pi ∧ (∀ t, x.i t = φ • x.pi t + ui t) ∧ x.s 0 = us 0 ∧
    (∀ t, x.s (t + 1) = γ • x.v t + us (t + 1)) ∧ Flow ρ x.v x.i x.pi x.s ∧
    ρ • x.v 0 + x.pi 0 = K

/-- Cochrane (2023), p. 512 (the substitution after (23.4), verified): in the Leeper model
`ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`. -/
theorem eq23_4 {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (t : ℕ) :
    ρ • x.v (t + 1) = (1 - γ) • x.v t - surprise 𝔼 x.pi t - us (t + 1) := by
  obtain ⟨hF, -, -, hs, hflow, -⟩ := hx
  rw [((flow_iff_surprise 𝔼 hF).mp hflow) t, hs t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), (23.2), p. 512, with the Fisher equation (23.1): in the Leeper model expected
inflation follows `E_t π_{t+1} = φ π_t + u_{i,t}`. -/
theorem leeper_expected_inflation {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (t : ℕ) :
    𝔼.E t (x.pi (t + 1)) = φ • x.pi t + ui t := by
  rw [← hx.1 t, hx.2.1 t]

/-- Cochrane (2023), §22.3, p. 500, and (22.1), p. 495: the Leeper model is the starred system in
which the target is chosen as the equilibrium itself — an equilibrium of (22.3)–(22.6) is an
equilibrium of the starred system around itself for every `(φ', γ')`. -/
theorem leeper_is_starred {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (φ' γ' : ℝ) :
    Consistent 𝔼 ρ x ∧ Eqm 𝔼 ρ φ' γ' x x :=
  ⟨⟨hx.1, hx.2.2.2.2.1⟩, starred_eqm 𝔼 φ' γ' ⟨hx.1, hx.2.2.2.2.1⟩⟩

/-! ### The printed rule (24.1) -/

omit 𝔼 in
/-- Cochrane (2023), eq. (24.1), p. 520 (survey error E14): the printed rule
`i_t = θπ_t + φ(π_t − π*_t) + u_{i,t}` is the starred rule with target rate
`i*_t = θπ*_t + u_{i,t}` and off-target coefficient `θ + φ` (not `φ`); (22.8) has `θπ*_t`. -/
theorem rule24_1_printed (θ φ : ℝ) (π piS ui i : ℕ → Ω → ℝ) :
    (∀ t, i t = θ • π t + φ • (π t - piS t) + ui t) ↔
      ∀ t, i t = (θ • piS t + ui t) + (θ + φ) • (π t - piS t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

end Cochrane.ObservationalEquivalence.StarredModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Observational equivalence of interest-rate regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–497 (the
box on p. 495, the bullets on pp. 496–497 and the "recipe" of p. 497), and Chapter 16, §16.6,
pp. 372–374 ((16.20)–(16.24)).

The theorem the book states verbally: in the starred system, the target path `(π*, i*, v*, s̃*)`
is an equilibrium whatever the off-target coefficients `(φ, γ)`; in the active-money and in the
active-fiscal regions it is the *only* equilibrium; so equilibrium time series cannot tell the
regimes apart.

## The corrected regime boundaries (survey error E12)

Under the book's equilibrium criterion (bounded inflation, transversality condition for debt):

* `unique_of_active_money`: `|φ| > 1` (not only `φ > 1`) gives uniqueness, for every `γ`;
* `unique_of_active_fiscal`: `|1 − γ| ≥ 1`, i.e. `γ ≤ 0` or `γ ≥ 2` (not only `γ = 0`), gives
  uniqueness, for every `φ`;
* `continuum_double_passive`: `|φ| ≤ 1` and `0 < γ < 2` give a continuum of equilibria (indexed
  by the date-0 inflation jump, under any expectation system, even perfect foresight);
  `sunspot_eqm`: also every bounded martingale-difference sunspot gives an equilibrium, and on the
  coin-flip tree (`coin_sunspot_eqm`) such equilibria are genuinely random.
* `unique_iff`: the target is the unique admissible equilibrium **iff**
  `|φ| > 1 ∨ γ ≤ 0 ∨ γ ≥ 2`. In particular "both active" (`|φ| > 1`, `γ = 0`) is determinate in
  the starred form (`unique_double_active`, survey error E19), and `γ ≥ 2` is not passive.

## Observational equivalence, both ways (pp. 496–497)

* `recipe`: any path satisfying the equilibrium conditions common to all models (Fisher, flow,
  bounded inflation, transversality) is the unique equilibrium of the starred system around
  itself for every determinate `(φ, γ)` — the recipe that turns any new-Keynesian or monetarist
  equilibrium into a fiscal-theory equilibrium "without changing any of its implications for
  observable time series", and conversely (`oe_both_ways`, `leeper_recipe`).

## The new-Keynesian AR(1) example (§16.6, pp. 372–373)

* `nk_solution`, `nk_unique`, `nk_observables` ((16.15)–(16.18)): with `i_t = φπ_t + u_t`,
  `u` an AR(1) with persistence `η` and `|φ| > 1`, the unique bounded equilibrium is
  `π_t = −u_t/(φ − η)`; `i_t = ηπ_t` and `π_{t+1} = ηπ_t − ε_{t+1}/(φ − η)`.
* `ftpl_eq_nk`: the fiscal-theory equilibrium with rule `i_t = θπ_t`, `θ = η`, and fiscal shock
  `ε^Σ_{s,t+1} = ε_{t+1}/(φ − η)` is the same process.
* `nk_passive_fiscal_news`: in the new-Keynesian equilibrium the valuation equation forces the
  "passive" fiscal news `ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} = ε_{t+1}/(φ − η)` — the fiscal theorist's shock.
-/

namespace Cochrane.ObservationalEquivalence.Equivalence

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec
open Cochrane.ObservationalEquivalence.ExpectationTools (innov pvExPost)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 495 ("unique" equilibrium): the target is the only admissible
equilibrium of the `(φ, γ)` starred system. -/
def UniqueEqm (ρ φ γ : ℝ) (tg : Outcome Ω) : Prop :=
  ∀ x, Eqm 𝔼 ρ φ γ tg x → Admissible 𝔼 ρ x → x = tg

/-- Cochrane (2023), p. 495 (regime labels, corrected per survey error E12): the determinate set
under the transversality criterion, `|φ| > 1` (active money) or `|1 − γ| ≥ 1` (active fiscal). -/
def Determinate (φ γ : ℝ) : Prop := 1 < |φ| ∨ 1 ≤ |1 - γ|

/-! ### Existence -/

/-- Cochrane (2023), §22.1, p. 495, and §16.6, p. 373: the target is an admissible equilibrium of
the `(φ, γ)` system for every `φ` and `γ`. -/
theorem starred_admissible_eqm {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : Eqm 𝔼 ρ φ γ tg tg ∧ Admissible 𝔼 ρ tg :=
  ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-! ### Deviation lemmas -/

/-- Cochrane (2023), (22.1), p. 495: if inflation is on target (`e = 0`) the debt deviation
obeys `ρ d_{t+1} = (1 − γ) d_t` from `d_0 = 0`, so it is zero. -/
theorem d_zero_of_e_zero {ρ γ : ℝ} (hρ : ρ ≠ 0) {e d : ℕ → Ω → ℝ} (he : e = 0)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    d = 0 := by
  subst he
  have hs : ∀ t, surprise 𝔼 (0 : ℕ → Ω → ℝ) t = 0 := fun t => by
    simp [surprise]
  funext t
  induction t with
  | zero =>
    simp only [Pi.zero_apply, add_zero] at h0
    exact (smul_eq_zero.mp h0).resolve_left hρ
  | succ t ih =>
    have := hd t
    rw [ih, hs] at this
    simp only [Pi.zero_apply, smul_zero, sub_zero] at this ⊢
    exact (smul_eq_zero.mp this).resolve_left hρ

/-- Cochrane (2023), (22.1), p. 495: if debt is on target (`d = 0`), there is no surprise
inflation and no date-0 jump, so `e_{t+1} = φ e_t` from `e_0 = 0`, hence `e = 0`. -/
theorem e_zero_of_d_zero {ρ φ γ : ℝ} {e d : ℕ → Ω → ℝ} (hd0 : d = 0)
    (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    e = 0 := by
  subst hd0
  funext t
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have h1 := hd t
    simp only [Pi.zero_apply, smul_zero, zero_sub] at h1
    have h2 : surprise 𝔼 e t = 0 := neg_eq_zero.mp h1.symm
    rw [surprise, sub_eq_zero, he t, ih] at h2
    simp only [Pi.zero_apply, smul_zero] at h2 ⊢
    exact h2

/-- Cochrane (2023), (23.4), p. 512: with `ρ ≠ 0`, an adapted debt deviation obeying
`ρ d_{t+1} = (1 − γ) d_t − w_{t+1}` with unforecastable `w` is an AR(1),
`E_t d_{t+1} = ((1 − γ)/ρ) d_t`. -/
theorem isAR1_of_dyn {ρ γ : ℝ} (hρ : ρ ≠ 0) {d w : ℕ → Ω → ℝ} (hda : 𝔼.Adapted d)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - w t) (hw : ∀ t, 𝔼.E t (w t) = 0) :
    𝔼.IsAR1 ((1 - γ) / ρ) d := by
  refine ⟨hda, fun t => ?_⟩
  have h := congrArg (𝔼.E t) (hd t)
  rw [map_smul, map_sub, map_smul, hda t, hw t, sub_zero] at h
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hρ, one_smul]

/-- Cochrane (2023), p. 513: for an AR(1) debt deviation, `ρᵀ E_t d_{t+T} = (1 − γ)ᵀ d_t`. -/
theorem pow_mul_E_ar1 {ρ γ : ℝ} (hρ : ρ ≠ 0) {d : ℕ → Ω → ℝ} (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d)
    (t T : ℕ) (ω : Ω) : ρ ^ T * 𝔼.E t (d (t + T)) ω = (1 - γ) ^ T * d t ω := by
  rw [𝔼.ar1_iterate hAR t T, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_pow,
    mul_div_cancel₀ _ hρ]

/-- Cochrane (2023), p. 513 ("if `γ > 0` … any unexpected inflation is consistent with the
transversality condition", corrected to `0 < γ < 2`): an AR(1) debt deviation with
`|1 − γ| < 1` satisfies the transversality condition. -/
theorem tvc_of_ar1 {ρ γ : ℝ} (hρ : ρ ≠ 0) (hγ : |1 - γ| < 1) {d : ℕ → Ω → ℝ}
    (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d) : TVC 𝔼 ρ d := by
  intro t ω
  simp_rw [pow_mul_E_ar1 𝔼 hρ hAR t _ ω]
  exact (tendsto_pow_mul_iff _ _).mpr (Or.inl hγ)

/-- Cochrane (2023), p. 513 ("if `γ = 0`, then only one value of unexpected inflation keeps
debt from exploding", generalised to `|1 − γ| ≥ 1`): an AR(1) debt deviation satisfying the
transversality condition is zero. -/
theorem zero_of_ar1_tvc {ρ γ : ℝ} (hρ : ρ ≠ 0) (hγ : 1 ≤ |1 - γ|) {d : ℕ → Ω → ℝ}
    (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d) (htvc : TVC 𝔼 ρ d) : d = 0 := by
  funext t ω
  have h := htvc t ω
  simp_rw [pow_mul_E_ar1 𝔼 hρ hAR t _ ω] at h
  exact eq_zero_of_tendsto_pow_mul hγ h

/-! ### Uniqueness in the determinate regions -/

/-- Cochrane (2023), §22.1, p. 495, and §16.5–16.6, pp. 371–373 (active money, `|φ| > 1`; survey
error E12: `φ < −1` is also active): the target is the unique admissible equilibrium, for every
fiscal coefficient `γ`. -/
theorem unique_of_active_money {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < |φ|) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  intro x hx hadm
  obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
  obtain ⟨-, heb, -, -⟩ := dev_admissible 𝔼 htg hadm
  have e0 : (fun t => x.pi t - tg.pi t) = 0 := zero_of_E_succ_eq_smul 𝔼 hφ heb he
  have d0 := d_zero_of_e_zero 𝔼 (d := fun t => x.v t - tg.v t) hρ e0 hd h0
  rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.1, p. 495, and §16.6, p. 373 (active fiscal; survey error E12: every
`γ` with `|1 − γ| ≥ 1`, i.e. `γ ≤ 0` or `γ ≥ 2`, not only `γ = 0`): the target is the unique
admissible equilibrium, for every monetary coefficient `φ`. -/
theorem unique_of_active_fiscal {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hγ : 1 ≤ |1 - γ|) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  intro x hx hadm
  obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
  obtain ⟨-, -, hda, htvc⟩ := dev_admissible 𝔼 htg hadm
  have hAR := isAR1_of_dyn 𝔼 (d := fun t => x.v t - tg.v t) hρ hda hd
    (fun t => E_surprise 𝔼 _ t)
  have d0 := zero_of_ar1_tvc 𝔼 hρ hγ hAR htvc
  have e0 := e_zero_of_d_zero 𝔼 (e := fun t => x.pi t - tg.pi t) d0 he hd h0
  rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.1, p. 495 (the box): in the determinate set the target is the unique
admissible equilibrium. -/
theorem unique_of_determinate {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  rcases h with h | h
  · exact unique_of_active_money 𝔼 hρ h hc htg
  · exact unique_of_active_fiscal 𝔼 hρ h hc htg

/-- Cochrane (2023), §16.6, p. 373, and §22.1, p. 495 (the book's active-fiscal regime `γ = 0`,
any `φ`, most simply `φ = 0`): the target is the unique admissible equilibrium. -/
theorem unique_of_gamma_zero {ρ φ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ 0 tg :=
  unique_of_active_fiscal 𝔼 hρ (by norm_num) hc htg

/-- Cochrane (2023), §22.7, p. 508 (survey error E19, confirmed): "if `φ > 1` and `γ = 0` both
policies are active … no equilibrium can form" is false in the starred form — the coordinated
target is an equilibrium and it is the unique one. -/
theorem unique_double_active {ρ φ : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < φ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    (Eqm 𝔼 ρ φ 0 tg tg ∧ Admissible 𝔼 ρ tg) ∧ UniqueEqm 𝔼 ρ φ 0 tg :=
  ⟨starred_admissible_eqm 𝔼 φ 0 hc htg,
    unique_of_active_money 𝔼 hρ (by rw [abs_of_pos (by linarith)]; exact hφ) hc htg⟩

/-! ### The double-passive continuum -/

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive): the inflation deviation `e_t = c φᵗ`
of a date-0 jump `c`. -/
def famE (φ c : ℝ) : ℕ → Ω → ℝ := fun t _ => c * φ ^ t

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive): the debt deviation
`d_t = −(c/ρ) ((1 − γ)/ρ)ᵗ` matching a date-0 inflation jump `c`. -/
noncomputable def famD (ρ γ c : ℝ) : ℕ → Ω → ℝ := fun t _ => -(c / ρ) * ((1 - γ) / ρ) ^ t

/-- Cochrane (2023), §22.7, pp. 508–509: the equilibrium with date-0 inflation jump `c`. -/
noncomputable def famPath (ρ φ γ : ℝ) (tg : Outcome Ω) (c : ℝ) : Outcome Ω :=
  ofDev φ γ tg (famE φ c) (famD ρ γ c)

/-- Cochrane (2023), §22.7, pp. 508–509: the path with date-0 jump `c` is an equilibrium of the
`(φ, γ)` system for every `φ`, `γ` and `c` (`ρ ≠ 0`). -/
theorem famPath_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (c : ℝ) : Eqm 𝔼 ρ φ γ tg (famPath ρ φ γ tg c) := by
  have hs : ∀ t, surprise 𝔼 (famE φ c) t = 0 := fun t => by
    rw [surprise]
    change (fun _ => c * φ ^ (t + 1)) - 𝔼.E t (fun _ => c * φ ^ (t + 1)) = 0
    rw [𝔼.const, sub_self]
  refine ofDev_eqm 𝔼 hc (fun t => ?_) (fun t => ?_) ?_
  · change 𝔼.E t (fun _ => c * φ ^ (t + 1)) = φ • fun _ => c * φ ^ t
    rw [𝔼.const]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hs, sub_zero]
    funext ω
    simp only [famD, Pi.smul_apply, smul_eq_mul]
    have hq : ρ * ((1 - γ) / ρ) = 1 - γ := mul_div_cancel₀ _ hρ
    rw [pow_succ]
    linear_combination (-(c / ρ) * ((1 - γ) / ρ) ^ t) * hq
  · funext ω
    simp only [famD, famE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive, `|φ| ≤ 1`, `0 < γ < 2`): the path with
date-0 jump `c` is admissible (bounded inflation, transversality condition). -/
theorem famPath_admissible {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1) (hγ : |1 - γ| < 1)
    {tg : Outcome Ω} (htg : Admissible 𝔼 ρ tg) (c : ℝ) :
    Admissible 𝔼 ρ (famPath ρ φ γ tg c) := by
  refine ofDev_admissible 𝔼 htg (fun t => 𝔼.const t _) ⟨|c|, fun t ω => ?_⟩
    (fun t => 𝔼.const t _) (fun t ω => ?_)
  · simp only [famE, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg c) (pow_le_one₀ (abs_nonneg φ) hφ)
  · have e : ∀ T : ℕ, ρ ^ T * 𝔼.E t (famD ρ γ c (t + T)) ω =
        (1 - γ) ^ T * (-(c / ρ) * ((1 - γ) / ρ) ^ t) := by
      intro T
      change ρ ^ T * 𝔼.E t (fun _ => -(c / ρ) * ((1 - γ) / ρ) ^ (t + T)) ω = _
      rw [𝔼.const, pow_add, div_pow (1 - γ) ρ T]
      field_simp
    simp_rw [e]
    exact (tendsto_pow_mul_iff _ _).mpr (Or.inl hγ)

/-- Cochrane (2023), §22.7, pp. 508–509: different date-0 jumps give different paths. -/
theorem famPath_injective [Nonempty Ω] (ρ φ γ : ℝ) (tg : Outcome Ω) :
    Function.Injective (famPath ρ φ γ tg) := by
  intro c₁ c₂ h
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
  simpa [famPath, ofDev, famE] using this

/-- Cochrane (2023), §22.7, pp. 508–509 ("if … φ < 1 … and fiscal policy is also passive, γ > 0,
then we are back to indeterminacy"; corrected to `|φ| ≤ 1`, `0 < γ < 2`): the admissible
equilibria form an uncountable set. -/
theorem continuum_double_passive [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1)
    (hγ : 0 < γ ∧ γ < 2) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    ¬ {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x}.Countable := by
  intro hcount
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  have hmaps : Set.MapsTo (famPath ρ φ γ tg) Set.univ
      {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x} := fun c _ =>
    ⟨famPath_eqm 𝔼 hρ hc c, famPath_admissible 𝔼 hρ hφ hγ' htg c⟩
  exact Cardinal.not_countable_real
    (hmaps.countable_of_injOn (famPath_injective ρ φ γ tg).injOn hcount)

/-- Cochrane (2023), §22.7, pp. 508–509: in the double-passive region the target is not the
unique admissible equilibrium. -/
theorem not_unique_of_passive [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1)
    (hγ : |1 - γ| < 1) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    ¬ UniqueEqm 𝔼 ρ φ γ tg := by
  intro hu
  have h1 := hu _ (famPath_eqm 𝔼 hρ hc 1) (famPath_admissible 𝔼 hρ hφ hγ htg 1)
  have h0 : famPath ρ φ γ tg 0 = tg := by
    rw [famPath]
    have e1 : famE φ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famE]
    have e2 : famD ρ γ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famD]
    rw [e1, e2, ofDev_zero]
  have := famPath_injective ρ φ γ tg (h1.trans h0.symm)
  norm_num at this

/-- Cochrane (2023), §22.1, p. 495, and §22.7, pp. 508–509 (the complete classification under the
transversality criterion): for a consistent admissible target, the target is the unique
admissible equilibrium iff `|φ| > 1` or `|1 − γ| ≥ 1`. -/
theorem unique_iff [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    UniqueEqm 𝔼 ρ φ γ tg ↔ Determinate φ γ := by
  refine ⟨fun hu => ?_, fun h => unique_of_determinate 𝔼 hρ h hc htg⟩
  by_contra hd
  simp only [Determinate, not_or, not_lt, not_le] at hd
  exact not_unique_of_passive 𝔼 hρ hd.1 hd.2 hc htg hu

/-- Cochrane (2023), pp. 495, 501, 512 (survey error E12): the determinate set is
`|φ| > 1 ∨ γ ≤ 0 ∨ γ ≥ 2`. -/
theorem determinate_iff (φ γ : ℝ) : Determinate φ γ ↔ 1 < |φ| ∨ γ ≤ 0 ∨ 2 ≤ γ := by
  rw [Determinate, one_le_abs_one_sub_iff]

/-- Cochrane (2023), p. 495 (survey error E12, counterexample to the printed "`φ < 1`, `γ > 0`
is passive–passive"): `φ = −2 < 1` with `γ = 1 > 0` is determinate. -/
theorem printed_phi_lt_one_determinate : Determinate (-2) 1 := Or.inl (by norm_num)

/-- Cochrane (2023), p. 495 (survey error E12, counterexample to the printed "`γ > 0` is passive
fiscal"): `γ = 3 > 0` with `φ = 1/2 < 1` is determinate (fiscal policy is active). -/
theorem printed_gamma_pos_determinate : Determinate (1 / 2) 3 := Or.inr (by norm_num)

/-! ### Sunspot equilibria -/

/-- Cochrane (2023), §22.7, pp. 508–509 ("indeterminate … even if the ingredient is sunspots"):
in the double-passive region (`|φ| < 1`, `0 < γ < 2`), every bounded adapted martingale
difference `ν` (`E_t ν_{t+1} = 0`) and every date-0 jump `c` give an admissible equilibrium
with inflation deviation `e_{t+1} = φ e_t + ν_{t+1}`, `e_0 = c`. -/
theorem sunspot_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| < 1) (hγ : |1 - γ| < 1)
    {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) {ν : ℕ → Ω → ℝ}
    (hνa : 𝔼.Adapted ν) (hνb : BoundedProc ν) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) (c : ℝ) :
    Eqm 𝔼 ρ φ γ tg (ofDev φ γ tg (dRec φ (fun t => ν (t + 1)) (fun _ => c))
        (dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)))) ∧
      Admissible 𝔼 ρ (ofDev φ γ tg (dRec φ (fun t => ν (t + 1)) (fun _ => c))
        (dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)))) := by
  set e := dRec φ (fun t => ν (t + 1)) (fun _ => c) with he_def
  set d := dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)) with hd_def
  have hea : 𝔼.Adapted e := dRec_adapted_of_succ 𝔼 (𝔼.const 0 c) (fun t => hνa (t + 1))
  have hda : 𝔼.Adapted d := dRec_adapted_of_succ 𝔼 (𝔼.const 0 _) (fun t => by
    rw [map_smul, hνa (t + 1)])
  have hE : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t := fun t => by
    change 𝔼.E t (φ • e t + ν (t + 1)) = φ • e t
    rw [map_add, map_smul, hea t, hmd t, add_zero]
  have hsur : ∀ t, surprise 𝔼 e t = ν (t + 1) := fun t => by
    rw [surprise, hE t]
    change φ • e t + ν (t + 1) - φ • e t = ν (t + 1)
    abel
  have hdyn : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t := fun t => by
    rw [hsur t]
    change ρ • (((1 - γ) / ρ) • d t + (-ρ⁻¹) • ν (t + 1)) = _
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hρ, mul_neg, mul_inv_cancel₀ hρ,
      neg_one_smul]
    exact (sub_eq_add_neg _ _).symm
  have h0 : ρ • d 0 + e 0 = 0 := by
    funext ω
    change ρ * -(c / ρ) + c = 0
    field_simp
    ring
  refine ⟨ofDev_eqm 𝔼 hc hE hdyn h0, ofDev_admissible 𝔼 htg hea ?_ hda ?_⟩
  · obtain ⟨M, hM⟩ := hνb
    exact ⟨|c| + |M| / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (abs_nonneg M)
      (fun t ω => (hM (t + 1) ω).trans (le_abs_self M)) (fun t => rfl) (fun ω => le_rfl)⟩
  · have hAR := isAR1_of_dyn 𝔼 hρ hda hdyn (fun t => E_surprise 𝔼 e t)
    exact tvc_of_ar1 𝔼 hρ hγ hAR

/-- The coin-flip shock is adapted (used for Cochrane (2023), §22.7, p. 509: genuinely random
sunspot equilibria exist). -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := fun t => by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- The coin-flip shock is bounded by one (Cochrane (2023), §22.7, p. 509). -/
theorem coinShock_bounded : BoundedProc ExpectationsFiniteTree.coinShock :=
  ⟨1, fun t ω => by
    unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> norm_num⟩

/-- Cochrane (2023), §22.7, pp. 508–509, and survey §3.2 (OE-1 (3)): on the coin-flip tree, in
the double-passive region, there is an admissible equilibrium whose date-1 inflation differs
from the target by the coin flip `±1` — a genuinely random sunspot equilibrium. -/
theorem coin_sunspot_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| < 1) (hγ : |1 - γ| < 1)
    {tg : Outcome (Bool × Bool)} (hc : Consistent ExpectationsFiniteTree.coinSystem ρ tg)
    (htg : Admissible ExpectationsFiniteTree.coinSystem ρ tg) :
    ∃ x, Eqm ExpectationsFiniteTree.coinSystem ρ φ γ tg x ∧
      Admissible ExpectationsFiniteTree.coinSystem ρ x ∧ x.pi 0 = tg.pi 0 ∧
      x.pi 1 = tg.pi 1 + ExpectationsFiniteTree.coinShock 1 := by
  obtain ⟨h1, h2⟩ := sunspot_eqm ExpectationsFiniteTree.coinSystem hρ hφ hγ hc htg
    coinShock_adapted coinShock_bounded ExpectationsFiniteTree.coinShock_mean_zero 0
  refine ⟨_, h1, h2, ?_, ?_⟩
  · funext ω
    simp [ofDev, dRec]
  · funext ω
    simp [ofDev, dRec]

/-! ### Perfect foresight -/

/-- Cochrane (2023), §22.7, p. 509 (under perfect foresight the only indeterminacy is the date-0
jump): every equilibrium of the `(φ, γ)` system under perfect foresight is the path `famPath c`
with `c = π_0 − π*_0`. -/
theorem perfectForesight_eq_famPath {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg x : Outcome Unit}
    (hc : Consistent perfectForesight ρ tg) (hx : Eqm perfectForesight ρ φ γ tg x) :
    x = famPath ρ φ γ tg (x.pi 0 () - tg.pi 0 ()) := by
  obtain ⟨he, hd, h0⟩ := deviation_dynamics perfectForesight hc hx
  set c := x.pi 0 () - tg.pi 0 () with hc_def
  have hs : ∀ t, surprise perfectForesight (fun t => x.pi t - tg.pi t) t = 0 := fun t => by
    rw [surprise]
    change _ - (x.pi (t + 1) - tg.pi (t + 1)) = 0
    rw [sub_self]
  have hE : ∀ t, (fun t => x.pi t - tg.pi t) t = famE φ c t := by
    intro t
    induction t with
    | zero => funext u; simp [famE, hc_def]
    | succ t ih =>
      have h := he t
      change x.pi (t + 1) - tg.pi (t + 1) = _ at h
      change x.pi (t + 1) - tg.pi (t + 1) = _
      rw [h]
      change x.pi t - tg.pi t = _ at ih
      rw [ih]
      funext u
      simp only [famE, Pi.smul_apply, smul_eq_mul]
      ring
  have hD : ∀ t, (fun t => x.v t - tg.v t) t = famD ρ γ c t := by
    intro t
    induction t with
    | zero =>
      have h := congrFun h0 ()
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      funext u
      simp only [famD, pow_zero, mul_one]
      change x.v 0 () - tg.v 0 () = _
      rw [hc_def]
      field_simp
      linarith
    | succ t ih =>
      have h := hd t
      rw [hs t, sub_zero] at h
      change x.v t - tg.v t = _ at ih
      rw [ih] at h
      change x.v (t + 1) - tg.v (t + 1) = _
      funext u
      have h' := congrFun h u
      simp only [famD, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
      have hq : ρ * ((1 - γ) / ρ) = 1 - γ := mul_div_cancel₀ _ hρ
      apply mul_left_cancel₀ hρ
      rw [h', pow_succ]
      linear_combination (c / ρ * ((1 - γ) / ρ) ^ t) * hq
  rw [eq_ofDev perfectForesight hx, famPath]
  congr 1
  · funext t; exact hE t
  · funext t; exact hD t

/-! ### The recipe: observational equivalence goes both ways -/

/-- Cochrane (2023), §22.2.1, p. 497 ("a recipe by which one can transform any monetarist or
new-Keynesian model into a fiscal theory model, without changing any of its implications for
observable time series"): any path obeying the Fisher equation and the flow condition, with
bounded adapted inflation, adapted debt and the transversality condition, is the unique
admissible equilibrium of the starred system around itself for every determinate `(φ, γ)` —
in particular for active fiscal policy `φ = 0, γ = 0` and for active money `φ = 2`. -/
theorem recipe {ρ : ℝ} (hρ : ρ ≠ 0) {x : Outcome Ω} (hF : Fisher 𝔼 x.i x.pi)
    (hflow : Flow ρ x.v x.i x.pi x.s) (hadm : Admissible 𝔼 ρ x) :
    ∀ φ γ, Determinate φ γ → Eqm 𝔼 ρ φ γ x x ∧ UniqueEqm 𝔼 ρ φ γ x :=
  fun φ γ h => ⟨starred_eqm 𝔼 φ γ ⟨hF, hflow⟩,
    unique_of_determinate 𝔼 hρ h ⟨hF, hflow⟩ hadm⟩

/-- Cochrane (2023), §22.1, p. 496 ("any time series produced by an active-money/passive fiscal
regime can be produced by an active-fiscal/passive-money regime and vice versa"): an admissible
equilibrium of any `(φ₁, γ₁)` system is the unique admissible equilibrium of the `(φ₂, γ₂)`
system around itself, for every determinate `(φ₂, γ₂)`. -/
theorem oe_both_ways {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0) {tg x : Outcome Ω}
    (hx : Eqm 𝔼 ρ φ₁ γ₁ tg x) (hadm : Admissible 𝔼 ρ x) (h₂ : Determinate φ₂ γ₂) :
    Eqm 𝔼 ρ φ₂ γ₂ x x ∧ UniqueEqm 𝔼 ρ φ₂ γ₂ x :=
  recipe 𝔼 hρ hx.1 hx.2.2.2.2.1 hadm φ₂ γ₂ h₂

/-- Cochrane (2023), §22.3, p. 500, and §22.2.1, p. 497: an admissible equilibrium of the Leeper
model (22.3)–(22.6) with any coefficients (active money `φ > 1, γ > 0` included) is the unique
admissible equilibrium of the active-fiscal starred system (`φ = 0`, `γ = 0`) around itself. -/
theorem leeper_recipe {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    {x : Outcome Ω} (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    Eqm 𝔼 ρ 0 0 x x ∧ UniqueEqm 𝔼 ρ 0 0 x :=
  recipe 𝔼 hρ hx.1 hx.2.2.2.2.1 hadm 0 0 (Or.inr (by norm_num))

/-! ### §16.6: the new-Keynesian AR(1) model and its fiscal-theory twin -/

/-- Cochrane (2023), (16.10), p. 370, and (16.15), p. 371: with `i_t = φπ_t + u_t`, `u` an AR(1)
with persistence `η ≠ φ`, the process `π_t = −u_t/(φ − η)` solves `E_t π_{t+1} = φπ_t + u_t`. -/
theorem nk_solution {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (t : ℕ) :
    𝔼.E t ((-(φ - η)⁻¹) • u (t + 1)) = φ • ((-(φ - η)⁻¹) • u t) + u t := by
  have h : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  rw [map_smul, hu.2 t]
  funext ω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §16.5, p. 371 (active money, `|φ| > 1`): `π_t = −u_t/(φ − η)` is the unique
bounded solution of `E_t π_{t+1} = φπ_t + u_t`. -/
theorem nk_unique {φ η : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u π : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (hub : BoundedProc u) (hπb : BoundedProc π) (hπ : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + u t) :
    π = fun t => (-(φ - η)⁻¹) • u t := by
  obtain ⟨M, hM⟩ := hπb
  obtain ⟨K, hK⟩ := hub
  have hδ : (fun t => π t - (-(φ - η)⁻¹) • u t) = 0 := by
    refine zero_of_E_succ_eq_smul 𝔼 hφ ⟨M + |(φ - η)⁻¹| * K, fun t ω => ?_⟩ (fun t => ?_)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
    · rw [map_sub, hπ t, nk_solution 𝔼 hφη hu t]
      rw [smul_sub]
      abel
  funext t
  have h : π t - (-(φ - η)⁻¹) • u t = 0 := congrFun hδ t
  exact sub_eq_zero.mp h

/-- Cochrane (2023), (16.15)–(16.18), p. 371: in the new-Keynesian equilibrium the observables
are `i_t = ηπ_t`, `π_{t+1} = ηπ_t − ε_{t+1}/(φ − η)` and `ΔE_{t+1}π_{t+1} = −ε_{t+1}/(φ − η)`,
where `ε_{t+1} = u_{t+1} − ηu_t`; `φ` enters only through the shock scaling. -/
theorem nk_observables {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (t : ℕ) :
    φ • ((-(φ - η)⁻¹) • u t) + u t = η • ((-(φ - η)⁻¹) • u t) ∧
      (-(φ - η)⁻¹) • u (t + 1) =
        η • ((-(φ - η)⁻¹) • u t) - (φ - η)⁻¹ • (u (t + 1) - η • u t) ∧
      surprise 𝔼 (fun t => (-(φ - η)⁻¹) • u t) t = -((φ - η)⁻¹ • (u (t + 1) - η • u t)) := by
  have h : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · rw [surprise, map_smul, hu.2 t]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §16.6, p. 372 (observational equivalence of the AR(1) example): a
fiscal-theory equilibrium with rule `i_t = θπ_t`, `θ = η` (so `E_t π_{t+1} = ηπ_t`) and fiscal
shock `ΔE_{t+1}π_{t+1} = −ε^Σ_{s,t+1}`, `ε^Σ_{s,t+1} = ε_{t+1}/(φ − η)`, starting from the same
`π_0`, produces exactly the new-Keynesian inflation process. -/
theorem ftpl_eq_nk {φ η : ℝ} (hφη : φ ≠ η) {u π : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (hE : ∀ t, 𝔼.E t (π (t + 1)) = η • π t)
    (hs : ∀ t, surprise 𝔼 π t = -((φ - η)⁻¹ • (u (t + 1) - η • u t)))
    (h0 : π 0 = (-(φ - η)⁻¹) • u 0) : π = fun t => (-(φ - η)⁻¹) • u t := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    have h1 := hs t
    rw [surprise, hE t, ih] at h1
    rw [sub_eq_iff_eq_add.mp h1, (nk_observables 𝔼 hφη hu t).2.1]
    abel

/-- Cochrane (2023), §16.6, p. 372 ("after the central bank engineers a monetary contraction,
fiscal policy 'passively' raises surpluses by `ε^Σ_{s,t+1} = −ΔE_{t+1}π_{t+1} = ε_{t+1}/(φ − η)`"):
in the new-Keynesian equilibrium, any surplus and debt paths satisfying the flow condition and
the transversality condition carry the news `ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} = ε_{t+1}/(φ − η)`. -/
theorem nk_passive_fiscal_news {ρ φ η M : ℝ} (hρ : |ρ| < 1) (hφη : φ ≠ η)
    {u i v s : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hF : Fisher 𝔼 i (fun t => (-(φ - η)⁻¹) • u t))
    (hflow : Flow ρ v i (fun t => (-(φ - η)⁻¹) • u t) s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    innov 𝔼 t (pvExPost ρ s t) = (φ - η)⁻¹ • (u (t + 1) - η • u t) := by
  have h1 := unexpected_inflation_news 𝔼 hρ hs hsa hF hflow hv htvc t
  rw [(nk_observables 𝔼 hφη hu t).2.2] at h1
  exact (neg_inj.mp h1).symm

end Cochrane.ObservationalEquivalence.Equivalence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Non-identification of the equilibrium-selection parameters

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, p. 496 ("without
additional identifying assumptions, the parameters that separate regimes such as `γ` and `φ` are
not identified"), §22.3, pp. 500–502 ((22.7)–(22.11) and the discussion of the regressions
(22.4)–(22.5) and of disturbance restrictions), and Chapter 16, §16.5, pp. 370–372 (the
reverse-engineering argument).

## Main results

* NI-1: `eqmSet_eq_singleton`, `eqmSet_const_on_determinate`, `statistic_independent`: on the
  determinate set the set of admissible equilibria is the same singleton for every `(φ, γ)`, so
  every statistic of the observables (any likelihood) is constant in `(φ, γ)`;
  `target_mem_eqmSet`: the observed path is an admissible equilibrium for *every* `(φ, γ)`;
  `not_identified`: no function of the observed path recovers `(φ, γ)`.
* NI-2 (`θ` vs `φ`): `eqm_rate_theta` (`i_t = θπ_t + u_{i,t}` holds identically in equilibrium,
  whatever `φ`), `coef_from_moment` and `regression_identifies_theta` (a population moment
  condition recovers `θ`), `spec_forces_phi_eq_theta` (the specification `i_t = φπ_t + u_{i,t}`
  imposes `φ = θ`), `stationary_iff` (`|θ| < 1` is exactly the condition for inflation
  `π_{t+1} = θπ_t + w_t` to stay bounded for all bounded inputs), `thetaTarget`,
  `theta_target_unique` (any `|θ| < 1` combines with any `|φ| > 1`).
* NI-3 (`α` vs `γ`): `eqm_surplus_alpha`, `regression_identifies_alpha`,
  `spec_forces_gamma_eq_alpha`.
* Reverse engineering (§16.5, p. 371): `reverse_engineer_rule`, `reverse_engineer_leeper`,
  `rev_disturbances_differ`: any path obeying the Fisher equation and the flow condition is an
  equilibrium of the Leeper model for every `(φ, γ)`, with disturbances `u_i = i − φπ`,
  `u_{s,t+1} = s̃_{t+1} − γ v_t`.
* Disturbance restrictions (p. 502): `sshape_two_ways`, `leeper_sshape_two_ways` (a surplus
  response may come from `α > 0` with uncorrelated shocks or from `α = 0` with an s-shaped
  disturbance); the explicit impulse response `irfV`, `irfS`: `irf_flow`, `irf_surplus`,
  `irf_sshape` (positive on impact, negative afterwards for `0 < α < 1`) and `irf_pv_zero`
  (its present value is zero for `0 < α < 2`, so it moves no inflation).
-/

namespace Cochrane.ObservationalEquivalence.NonIdentification

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec Cochrane.ObservationalEquivalence.Equivalence

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 496: the set of admissible equilibria of the `(φ, γ)` system. -/
def EqmSet (ρ φ γ : ℝ) (tg : Outcome Ω) : Set (Outcome Ω) :=
  {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x}

/-! ### NI-1 -/

/-- Cochrane (2023), §22.1, p. 496 (NI-1): on the determinate set the admissible equilibria are
exactly the target. -/
theorem eqmSet_eq_singleton {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : EqmSet 𝔼 ρ φ γ tg = {tg} := by
  ext x
  refine ⟨fun hx => unique_of_determinate 𝔼 hρ h hc htg x hx.1 hx.2, fun hx => ?_⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-- Cochrane (2023), §22.1, p. 496 (NI-1, "the parameters that separate regimes such as `γ` and
`φ` are not identified"): the set of admissible equilibria is the same for all determinate
`(φ, γ)`. -/
theorem eqmSet_const_on_determinate {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0) (h₁ : Determinate φ₁ γ₁)
    (h₂ : Determinate φ₂ γ₂) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : EqmSet 𝔼 ρ φ₁ γ₁ tg = EqmSet 𝔼 ρ φ₂ γ₂ tg := by
  rw [eqmSet_eq_singleton 𝔼 hρ h₁ hc htg, eqmSet_eq_singleton 𝔼 hρ h₂ hc htg]

/-- Cochrane (2023), §22.1, p. 496, and §16.5, p. 371 ("the likelihood function does not involve
`φ`"): any statistic `F` of the observed equilibrium path — a likelihood, a regression
coefficient, an impulse response — takes the same value for all determinate `(φ, γ)`. -/
theorem statistic_independent {X : Type*} (F : Outcome Ω → X) {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0)
    (h₁ : Determinate φ₁ γ₁) (h₂ : Determinate φ₂ γ₂) {tg x₁ x₂ : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) (hx₁ : x₁ ∈ EqmSet 𝔼 ρ φ₁ γ₁ tg)
    (hx₂ : x₂ ∈ EqmSet 𝔼 ρ φ₂ γ₂ tg) : F x₁ = F x₂ := by
  rw [eqmSet_eq_singleton 𝔼 hρ h₁ hc htg, Set.mem_singleton_iff] at hx₁
  rw [eqmSet_eq_singleton 𝔼 hρ h₂ hc htg, Set.mem_singleton_iff] at hx₂
  rw [hx₁, hx₂]

/-- Cochrane (2023), §22.1, p. 496 ("the equilibrium conditions are the same in each regime"):
the observed target path is an admissible equilibrium for every `(φ, γ)` whatsoever, so no value
of `(φ, γ)` is rejected by the data. -/
theorem target_mem_eqmSet {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : tg ∈ EqmSet 𝔼 ρ φ γ tg :=
  ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-- Cochrane (2023), §22.1, p. 496 (non-identification, formally): there is no estimator — no
function of the observed path — that returns `(φ, γ)` whenever the path is an admissible
equilibrium of the `(φ, γ)` system. -/
theorem not_identified {ρ : ℝ} {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) :
    ¬ ∃ est : Outcome Ω → ℝ × ℝ, ∀ φ γ x, x ∈ EqmSet 𝔼 ρ φ γ tg → est x = (φ, γ) := by
  rintro ⟨est, hest⟩
  have h1 := hest 2 0 tg (target_mem_eqmSet 𝔼 2 0 hc htg)
  have h2 := hest 3 0 tg (target_mem_eqmSet 𝔼 3 0 hc htg)
  rw [h1] at h2
  have := congrArg Prod.fst h2
  norm_num at this

/-! ### NI-2: `θ` versus `φ` -/

/-- Cochrane (2023), (22.7)–(22.8), p. 501 (NI-2): in every admissible equilibrium of a
determinate system with `i*_t = θπ*_t + u_{i,t}`, the observed rule is `i_t = θπ_t + u_{i,t}`
identically; `φ` does not appear. -/
theorem eqm_rate_theta {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    x.i t = θ • x.pi t + ui t := by
  rw [eqmSet_eq_singleton 𝔼 hρ h hc htg, Set.mem_singleton_iff] at hx
  rw [hx, hθ t]

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the interest-rate policy rule parameter `θ` can, in principle, be
measured"): with a population moment `m` (any linear functional, e.g. an unconditional
expectation), if `y = b x + u` with `m(u x) = 0` and `m(x²) ≠ 0`, then
`b = m(y x)/m(x²)` — the population regression coefficient. -/
theorem coef_from_moment (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {y x u : Ω → ℝ} {b : ℝ} (h : y = b • x + u)
    (horth : m (u * x) = 0) (hvar : m (x * x) ≠ 0) : b = m (y * x) / m (x * x) := by
  have e : y * x = b • (x * x) + u * x := by
    rw [h]
    funext ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_add, map_smul, horth, add_zero, smul_eq_mul, mul_div_cancel_right₀ _ hvar]

/-- Cochrane (2023), p. 501 (NI-2): in a determinate equilibrium, regressing `i_t` on `π_t` with
a disturbance orthogonal to inflation recovers `θ` — never `φ`. -/
theorem regression_identifies_theta (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0)
    (h : Determinate φ γ) {tg x : Outcome Ω} {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg)
    (t : ℕ) (horth : m (ui t * x.pi t) = 0) (hvar : m (x.pi t * x.pi t) ≠ 0) :
    θ = m (x.i t * x.pi t) / m (x.pi t * x.pi t) :=
  coef_from_moment m (eqm_rate_theta 𝔼 hρ h hc htg hθ hx t) horth hvar

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the specification `i_t = φπ_t + u_{i,t}` thus adds an implicit
assumption, `φ = θ`"): if both `i_t = θπ_t + u_{i,t}` and `i_t = φπ_t + u_{i,t}` hold with the
same disturbance and `π_t` is not identically zero, then `φ = θ`. -/
theorem spec_forces_phi_eq_theta {θ φ : ℝ} {i π u : Ω → ℝ} (h1 : i = θ • π + u)
    (h2 : i = φ • π + u) {ω : Ω} (hω : π ω ≠ 0) : φ = θ := by
  have := congrFun (h1.symm.trans h2) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at this
  exact (mul_right_cancel₀ hω this).symm

/-- Cochrane (2023), (22.7)–(22.8), p. 501: in a determinate equilibrium inflation follows
`E_t π_{t+1} = θπ_t + u_{i,t}`. -/
theorem eqm_inflation_theta {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    𝔼.E t (x.pi (t + 1)) = θ • x.pi t + ui t := by
  rw [← hx.1.1 t, eqm_rate_theta 𝔼 hρ h hc htg hθ hx t]

/-- Cochrane (2023), p. 501 ("we should have `θ < 1` if we wish stationary solutions"; survey
error E12: `|θ| < 1`): the inflation recursion `π_{t+1} = θπ_t + w_t` keeps inflation bounded for
every bounded input and bounded start iff `|θ| < 1`. -/
theorem stationary_iff [Nonempty Ω] (θ : ℝ) :
    (∀ w π : ℕ → Ω → ℝ, BoundedProc w → (∃ B, ∀ ω, |π 0 ω| ≤ B) →
      (∀ t, π (t + 1) = θ • π t + w t) → BoundedProc π) ↔ |θ| < 1 := by
  constructor
  · intro h
    by_contra hθ
    have h1 : 1 ≤ |θ| := not_lt.mp hθ
    set w : ℕ → Ω → ℝ := fun t _ => 1 * (if 0 ≤ θ then (1 : ℝ) else -1) ^ (t + 1) with hw
    have hwb : BoundedProc w := ⟨1, fun t ω => by
      simp only [hw, one_mul, abs_pow]
      split_ifs <;> norm_num⟩
    obtain ⟨M, hM⟩ := h w (dRec θ w 0) hwb ⟨0, fun ω => by simp [dRec]⟩ (fun t => rfl)
    have hgrow := rec_unbounded h1 zero_le_one (d := dRec θ w 0) (fun t => rfl) rfl
    obtain ⟨n, hn⟩ := exists_nat_gt M
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := hgrow n ω
    have := hM n ω
    linarith
  · rintro hθ w π ⟨K, hK⟩ ⟨B, hB⟩ hπ
    exact ⟨|B| + |K| / (1 - |θ|), rec_bounded hθ (abs_nonneg B) (abs_nonneg K)
      (fun t ω => (hK t ω).trans (le_abs_self K)) hπ (fun ω => (hB ω).trans (le_abs_self B))⟩

/-- Cochrane (2023), (22.8), p. 501: a target built from an interest-rate rule with coefficient
`θ`: `π*_0 = 0`, `π*_{t+1} = θπ*_t + u_{i,t}`, `i*_t = θπ*_t + u_{i,t}`, with debt and surplus
targets zero. -/
noncomputable def thetaTarget (θ : ℝ) (ui : ℕ → Ω → ℝ) : Outcome Ω where
  pi := dRec θ ui 0
  i := fun t => θ • dRec θ ui 0 t + ui t
  v := 0
  s := 0

/-- Cochrane (2023), (22.8), p. 501: the `θ`-target is consistent and, for `|θ| < 1` and bounded
adapted `u_i`, admissible. -/
theorem thetaTarget_ok {ρ θ : ℝ} (hθ : |θ| < 1) {ui : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ui)
    (hub : BoundedProc ui) : Consistent 𝔼 ρ (thetaTarget θ ui) ∧
      Admissible 𝔼 ρ (thetaTarget θ ui) ∧ ThetaRule θ (thetaTarget θ ui).pi ui
        (thetaTarget θ ui).i := by
  have hpa : 𝔼.Adapted (dRec θ ui 0) := dRec_adapted (γ := θ) (b0 := 0) 𝔼 hua
  obtain ⟨K, hK⟩ := hub
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ⟨hpa, fun t => by simp [thetaTarget], ?_, fun t ω => ?_⟩,
    fun t => rfl⟩
  · change θ • dRec θ ui 0 t + ui t = 𝔼.E t (θ • dRec θ ui 0 t + ui t)
    rw [map_add, map_smul, hpa t, hua t]
  · change ρ • (0 : Ω → ℝ) = 0 + (θ • dRec θ ui 0 t + ui t) - (θ • dRec θ ui 0 t + ui t) - 0
    simp
  · exact ⟨0 + |K| / (1 - |θ|), rec_bounded hθ le_rfl (abs_nonneg K)
      (fun t ω => (hK t ω).trans (le_abs_self K)) (fun t => rfl) (fun ω => by
        change |dRec θ ui 0 0 ω| ≤ 0
        simp [dRec])⟩
  · simp [thetaTarget]

/-- Cochrane (2023), p. 501 ("the parameters `θ` and `φ` have distinct economic functions … there
is no reason the parameters should be the same"): for every `|θ| < 1` (stationary inflation)
and every `|φ| > 1` (determinacy), the `θ`-target is the unique admissible equilibrium, and in it
`i_t = θπ_t + u_{i,t}`. -/
theorem theta_target_unique {ρ θ φ γ : ℝ} (hρ : ρ ≠ 0) (hθ : |θ| < 1) (hφ : 1 < |φ|)
    {ui : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ui) (hub : BoundedProc ui) :
    UniqueEqm 𝔼 ρ φ γ (thetaTarget θ ui) ∧
      ∀ t, (thetaTarget θ ui).i t = θ • (thetaTarget θ ui).pi t + ui t := by
  obtain ⟨hc, htg, hth⟩ := thetaTarget_ok (ρ := ρ) 𝔼 hθ hua hub
  exact ⟨unique_of_active_money 𝔼 hρ hφ hc htg, hth⟩

/-! ### NI-3: `α` versus `γ` -/

/-- Cochrane (2023), (22.9), p. 501 (NI-3): in every admissible equilibrium of a determinate
system with `s̃*_{t+1} = α v*_t + u_{s,t+1}`, the observed surplus obeys
`s̃_{t+1} = α v_t + u_{s,t+1}` identically; `γ` does not appear. -/
theorem eqm_surplus_alpha {ρ φ γ α : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hα : StarredSurplus α tg.v us tg.s) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    x.s (t + 1) = α • x.v t + us (t + 1) := by
  rw [eqmSet_eq_singleton 𝔼 hρ h hc htg, Set.mem_singleton_iff] at hx
  rw [hx, hα t]

/-- Cochrane (2023), p. 501 (NI-3): regressing `s̃_{t+1}` on `v_t` with a disturbance orthogonal
to debt recovers `α` — never `γ`. -/
theorem regression_identifies_alpha (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {ρ φ γ α : ℝ} (hρ : ρ ≠ 0)
    (h : Determinate φ γ) {tg x : Outcome Ω} {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) (hα : StarredSurplus α tg.v us tg.s)
    (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) (horth : m (us (t + 1) * x.v t) = 0)
    (hvar : m (x.v t * x.v t) ≠ 0) : α = m (x.s (t + 1) * x.v t) / m (x.v t * x.v t) :=
  coef_from_moment m (eqm_surplus_alpha 𝔼 hρ h hc htg hα hx t) horth hvar

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the identifying assumption in (22.5) `s_{t+1} = γ v_t + u_{s,t+1}`
is `α = γ`"): if both `s̃_{t+1} = α v_t + u_{s,t+1}` and `s̃_{t+1} = γ v_t + u_{s,t+1}` hold
with the same disturbance and `v_t` is not identically zero, then `γ = α`. -/
theorem spec_forces_gamma_eq_alpha {α γ : ℝ} {s v u : Ω → ℝ} (h1 : s = α • v + u)
    (h2 : s = γ • v + u) {ω : Ω} (hω : v ω ≠ 0) : γ = α :=
  spec_forces_phi_eq_theta h1 h2 hω

/-! ### Reverse engineering (§16.5, p. 371) -/

/-- Cochrane (2023), §16.5, p. 371 ("Choose any process `{π_t}`. … Choose any `φ`. Construct
`u_t = i_t − φπ_t`"): for any inflation process and any `φ`, with `i_t = E_t π_{t+1}` and
`u_t := i_t − φπ_t`, the Fisher equation and the rule `i_t = φπ_t + u_t` hold. -/
theorem reverse_engineer_rule (π : ℕ → Ω → ℝ) (φ : ℝ) :
    Fisher 𝔼 (fun t => 𝔼.E t (π (t + 1))) π ∧
      ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + (𝔼.E t (π (t + 1)) - φ • π t) :=
  ⟨fun _ => rfl, fun t => by abel⟩

/-- Cochrane (2023), §16.5, p. 371: the reverse-engineered monetary disturbance
`u_{i,t} = i_t − φπ_t`. -/
def revUi (φ : ℝ) (x : Outcome Ω) : ℕ → Ω → ℝ := fun t => x.i t - φ • x.pi t

/-- Cochrane (2023), §22.3, p. 502: the reverse-engineered fiscal disturbance
`u_{s,t+1} = s̃_{t+1} − γ v_t` (`u_{s,0} = s̃_0`). -/
def revUs (γ : ℝ) (x : Outcome Ω) : ℕ → Ω → ℝ
  | 0 => x.s 0
  | t + 1 => x.s (t + 1) - γ • x.v t

/-- Cochrane (2023), §16.5, p. 371, and §22.3, p. 500 (the regressions (22.4)–(22.5) "estimate
`φ` or `γ` only under restrictions"): any path obeying the Fisher equation and the flow condition
is an equilibrium of the Leeper model (22.3)–(22.6) for every `(φ, γ)`, with the
reverse-engineered disturbances. -/
theorem reverse_engineer_leeper {ρ : ℝ} {x : Outcome Ω} (hF : Fisher 𝔼 x.i x.pi)
    (hflow : Flow ρ x.v x.i x.pi x.s) (φ γ : ℝ) :
    LeeperEqm 𝔼 ρ φ γ (revUi φ x) (revUs γ x) (ρ • x.v 0 + x.pi 0) x := by
  refine ⟨hF, fun t => ?_, rfl, fun t => ?_, hflow, rfl⟩
  · simp only [revUi]; abel
  · simp only [revUs]; abel

omit 𝔼 in
/-- Cochrane (2023), §16.5, p. 371 ("these parameters and variables always appear together, so
there are different combinations of `φ`, `u_t` … which give the same time series"): changing
`φ` changes the reverse-engineered disturbance by `(φ₂ − φ₁) π_t`. -/
theorem rev_disturbances_differ (φ₁ φ₂ : ℝ) (x : Outcome Ω) (t : ℕ) :
    revUi φ₁ x t - revUi φ₂ x t = (φ₂ - φ₁) • x.pi t := by
  simp only [revUi, sub_smul]
  abel

/-! ### Disturbance restrictions and the s-shaped surplus (p. 502) -/

omit 𝔼 in
/-- Cochrane (2023), p. 502 ("the surplus process can have an s-shaped response by virtue of
`α > 0` … or by virtue of an s-shaped `{u_{s,t+1}}` process with `α = 0`"): any starred surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}` is also `s̃*_{t+1} = α' v*_t + u'_{s,t+1}` for every `α'`, with
`u'_{s,t+1} = s̃*_{t+1} − α' v*_t`; the equilibrium set depends only on `s̃*`. -/
theorem sshape_two_ways {vS sS : ℕ → Ω → ℝ} (α' : ℝ) :
    StarredSurplus α' vS (fun t => sS t - α' • lag vS t) sS := by
  intro t
  simp only [lag]
  abel

/-- Cochrane (2023), p. 502 (the Leeper form): an equilibrium of (22.3)–(22.6) with fiscal
coefficient `γ` and disturbance `u_s` is the same path as an equilibrium with `γ' = 0` and
disturbance `u'_{s,t+1} = γ v_t + u_{s,t+1}`. -/
theorem leeper_sshape_two_ways {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) :
    LeeperEqm 𝔼 ρ φ 0 ui (revUs 0 x) K x := by
  obtain ⟨hF, hm, -, -, hflow, h0⟩ := hx
  refine ⟨hF, hm, rfl, fun t => ?_, hflow, h0⟩
  simp only [revUs, zero_smul, sub_zero, zero_add]

/-- Cochrane (2023), p. 502 (an explicit s-shaped response): real debt after a unit surplus
disturbance at date 1 with no inflation surprise, `v_0 = 0`, `v_{t+1} = −ρ⁻¹((1 − α)/ρ)ᵗ`. -/
noncomputable def irfV (α ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => -ρ⁻¹ * ((1 - α) / ρ) ^ t

/-- Cochrane (2023), p. 502: the surplus response, `s̃_1 = 1` and `s̃_{t+2} = α v_{t+1}`. -/
noncomputable def irfS (α ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | t + 2 => α * irfV α ρ (t + 1)

/-- Cochrane (2023), p. 502: a unit surplus disturbance at date 1. -/
def impulse (t : ℕ) : ℝ := if t = 1 then 1 else 0

/-- Cochrane (2023), (22.10), p. 501, with no inflation surprise: the response obeys the flow
condition `ρ v_{t+1} = v_t − s̃_{t+1}`. -/
theorem irf_flow {α ρ : ℝ} (hρ : ρ ≠ 0) (t : ℕ) :
    ρ * irfV α ρ (t + 1) = irfV α ρ t - irfS α ρ (t + 1) := by
  rcases t with _ | t
  · simp [irfV, irfS, hρ]
  · simp only [irfV, irfS]
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
    simp only [div_eq_mul_inv]
    rw [pow_succ]
    linear_combination (-(((1 - α) * ρ⁻¹) ^ t * ((1 - α) * ρ⁻¹))) * h1

/-- Cochrane (2023), (22.9), p. 501: the response is generated by `s̃_{t+1} = α v_t + u_{s,t+1}`
with the unit impulse `u_{s,1} = 1` — and equally by `α' = 0` with `u'_s = s̃` itself. -/
theorem irf_surplus (α ρ : ℝ) (t : ℕ) :
    irfS α ρ (t + 1) = α * irfV α ρ t + impulse (t + 1) ∧
      irfS α ρ (t + 1) = 0 * irfV α ρ t + irfS α ρ (t + 1) := by
  refine ⟨?_, by ring⟩
  rcases t with _ | t
  · simp [irfS, irfV, impulse]
  · simp [irfS, impulse]

/-- Cochrane (2023), p. 502 (the s-shape): for `0 < α < 1` and `ρ > 0` the surplus is positive
on impact and negative at every later date. -/
theorem irf_sshape {α ρ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) :
    irfS α ρ 1 = 1 ∧ ∀ t, irfS α ρ (t + 2) < 0 := by
  refine ⟨rfl, fun t => ?_⟩
  simp only [irfS, irfV]
  have h1 : 0 < ((1 - α) / ρ) ^ t := pow_pos (div_pos (by linarith) hρ) t
  have h2 : 0 < ρ⁻¹ := inv_pos.mpr hρ
  nlinarith [mul_pos h2 h1]

/-- Cochrane (2023), p. 502, and §4.2 (`a(ρ) = 0`): for `0 < α < 2` the present value of the
surplus response is zero, `∑_{j ≥ 0} ρʲ s̃_{1+j} = 0`, so the disturbance moves no inflation. -/
theorem irf_pv_zero {α ρ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hρ : ρ ≠ 0) :
    HasSum (fun j => ρ ^ j * irfS α ρ (j + 1)) 0 := by
  have hq : |1 - α| < 1 := (abs_one_sub_lt_one_iff α).mpr ⟨hα0, hα2⟩
  have hg : HasSum (fun j : ℕ => -α * (1 - α) ^ j) (-α * (1 - (1 - α))⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hq).mul_left (-α)
  have hval : -α * (1 - (1 - α))⁻¹ = 0 - ρ ^ 0 * irfS α ρ (0 + 1) := by
    rw [sub_sub_cancel, neg_mul, mul_inv_cancel₀ hα0.ne']
    simp [irfS]
  rw [hval] at hg
  have hshift : (fun j : ℕ => -α * (1 - α) ^ j) =
      fun j => ρ ^ (j + 1) * irfS α ρ (j + 1 + 1) := by
    funext j
    simp only [irfS, irfV]
    rw [pow_succ, div_pow]
    field_simp
  rw [hshift] at hg
  refine (hasSum_nat_add_iff' (f := fun j => ρ ^ j * irfS α ρ (j + 1)) 1).mp ?_
  rw [Finset.sum_range_one]
  exact hg

end Cochrane.ObservationalEquivalence.NonIdentification

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The four Leeper regions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, eqs. (22.3)–(22.6),
p. 500, and §22.7, pp. 508–509 ("Inconsistent or undetermined regimes"); Chapter 23, eqs.
(23.1)–(23.4) and the remarks on pp. 512–513.

The unstarred Leeper (1991) model `i_t = E_t π_{t+1}`, `i_t = φπ_t + u_{i,t}`,
`s̃_{t+1} = γ v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`LeeperEqm`, with the
`ρ` that (22.6) omits) and the inherited debt `ρ v_0 + π_0 = K`. Equilibrium criterion
(`Admissible`): adapted, bounded inflation, transversality condition for debt. Disturbances are
bounded and adapted.

## The four regions, with the corrected boundaries (survey error E12)

* (a) `region_a`: `|φ| > 1`, `0 < γ < 2`: exactly one admissible equilibrium.
* (b) `region_b`: `|φ| < 1`, `γ ≤ 0 ∨ γ ≥ 2` (the book: `γ = 0`): exactly one.
* (c) `region_c_iff`: `|φ| > 1`, `γ ≤ 0 ∨ γ ≥ 2` (both active): an equilibrium exists **iff** the
  date-0 restriction `π^m_0 + ρ v^f_0 = K` and the cross-restriction
  `ΔE_{t+1}π^m_{t+1} = (1 − γ)v^f_t − ρ v^f_{t+1} − u_{s,t+1}` hold, where `π^m` is the monetary
  forward solution and `v^f` the fiscal one. Generic non-existence: at most one `K` works
  (`region_c_unique_K`); with martingale-difference fiscal shocks no `K` works
  (`region_c_md_nonexistence`), e.g. on the coin-flip tree (`region_c_coin`).
* (d) `region_d`: `|φ| < 1`, `0 < γ < 2`: uncountably many admissible equilibria;
  `region_d_sunspot`: every bounded martingale-difference sunspot gives one, and on the coin-flip
  tree they are genuinely random (`region_d_coin`).
* The boundary `|φ| = 1` (`0 < γ < 2`): a continuum whenever the monetary equation has a bounded
  solution (`region_d_of_solution`, any `|φ| ≤ 1`), but no equilibrium at all for the bounded
  disturbance `u_{i,t} = −φ^{t+1}` (`region_d_unit_nonexistence`).
* Region (b) needs bounded inherited debt: `region_b_iff` (existence iff `K` bounded),
  `region_b_unbounded_K` (counterexample on `ℕ` with `fullInfo`).

## Remarks of pp. 512–513, made precise

* `tvc_passive` ("if `γ > 0` … any unexpected inflation is consistent with the transversality
  condition", corrected to `0 < γ < 2`): whatever the inflation path, debt from (23.4) satisfies
  the transversality condition.
* `active_fiscal_forced` ("if `γ = 0`, then only one value of unexpected inflation keeps debt from
  exploding", generalised to `|1 − γ| ≥ 1`): debt is the fiscal forward solution and unexpected
  inflation is pinned down, for every `φ`.
* `e19_starred_vs_unstarred` (survey error E19): both-active is determinate in the starred form
  but generically has no equilibrium in the unstarred form.

## Dependence on the equilibrium criterion

With "debt bounded" (Woodford/Leeper) instead of the transversality condition, in the starred
model: `uniqueB_iff` — unique iff `|φ| > 1` or `|1 − γ| > ρ`; the passive-fiscal range shrinks
from `0 < γ < 2` to `1 − ρ ≤ γ ≤ 1 + ρ`; `criterion_matters` gives a `γ` that is passive under
the transversality criterion and active under boundedness; `locallyRicardian_iff_gamma` links
the boundedness criterion to Woodford's locally Ricardian rules (`|1 − γ| < ρ`).

## The printed starred debt equation (16.21)–(16.22)

As printed (PDF p. 399), the starred debt equation uses the actual surplus. Then
`literal_gap`: the gap `v − v*` obeys `ρ d_{t+1} = d_t − ΔE_{t+1}(π − π*)_{t+1}` (no `γ`);
`literal_limit`: `ρᵀ E_t v_{t+T} → ((α − γ)/α)(v_t − v*_t)` for `0 < α < 2`; `literal_tvc_iff`:
the transversality condition holds iff `γ = α` or `v = v*`. So under the printed form fiscal
policy is passive iff `γ = α`, not for every `γ > 0`.
-/

namespace Cochrane.ObservationalEquivalence.LeeperRegions

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec Cochrane.ObservationalEquivalence.Equivalence
open Cochrane.ObservationalEquivalence.ExpectationTools (fullInfo)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Building paths of the Leeper model -/

/-- Cochrane (2023), (23.1)–(23.4), p. 512: the path with inflation `π` and debt `v`, the
interest rate from the rule `i_t = φπ_t + u_{i,t}` and the surplus from
`s̃_{t+1} = γ v_t + u_{s,t+1}`, `s̃_0 = u_{s,0}`. -/
def mkPath (φ γ : ℝ) (ui us π v : ℕ → Ω → ℝ) : Outcome Ω where
  pi := π
  i := fun t => φ • π t + ui t
  v := v
  s := fun t => γ • lag v t + us t

/-- Cochrane (2023), (23.1)–(23.4), p. 512: a path is an equilibrium of the Leeper model when
expected inflation obeys `E_t π_{t+1} = φπ_t + u_{i,t}`, debt obeys (23.4)
`ρ v_{t+1} = (1 − γ)v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`, and `ρ v_0 + π_0 = K`. -/
theorem mkPath_eqm {ρ φ γ : ℝ} {ui us π v : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hπ : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t)
    (hv : ∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1))
    (h0 : ρ • v 0 + π 0 = K) : LeeperEqm 𝔼 ρ φ γ ui us K (mkPath φ γ ui us π v) := by
  refine ⟨fun t => (hπ t).symm, fun t => rfl, ?_, fun t => rfl, fun t => ?_, h0⟩
  · change γ • (0 : Ω → ℝ) + us 0 = us 0
    rw [smul_zero, zero_add]
  · change ρ • v (t + 1) = v t + (φ • π t + ui t) - π (t + 1) - (γ • v t + us (t + 1))
    rw [hv t, surprise, hπ t, sub_smul, one_smul]
    abel

/-- Cochrane (2023), (23.1)–(23.4), p. 512: every equilibrium of the Leeper model is the path
built from its inflation and debt, and these obey the three conditions of `mkPath_eqm`. -/
theorem eq_mkPath {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) :
    x = mkPath φ γ ui us x.pi x.v ∧ (∀ t, 𝔼.E t (x.pi (t + 1)) = φ • x.pi t + ui t) ∧
      (∀ t, ρ • x.v (t + 1) = (1 - γ) • x.v t - surprise 𝔼 x.pi t - us (t + 1)) ∧
      ρ • x.v 0 + x.pi 0 = K := by
  refine ⟨outcome_ext rfl (funext fun t => hx.2.1 t) rfl (funext fun t => ?_),
    leeper_expected_inflation 𝔼 hx, eq23_4 𝔼 hx, hx.2.2.2.2.2⟩
  rcases t with _ | t
  · change x.s 0 = γ • (0 : Ω → ℝ) + us 0
    rw [smul_zero, zero_add, hx.2.2.1]
  · exact hx.2.2.2.1 t

/-- Cochrane (2023), (23.4), p. 512: debt generated by (23.4) from the inherited debt,
`v_0 = (K − π_0)/ρ`, `v_{t+1} = ((1 − γ)/ρ) v_t + ρ⁻¹(−ΔE_{t+1}π_{t+1} − u_{s,t+1})`. -/
noncomputable def vPath (ρ γ : ℝ) (us : ℕ → Ω → ℝ) (K : Ω → ℝ) (π : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  dRec ((1 - γ) / ρ) (fun t => ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1))) (ρ⁻¹ • (K - π 0))

/-- Cochrane (2023), (23.4), p. 512: `vPath` obeys (23.4) and the date-0 condition, and any debt
path obeying them is `vPath` (`ρ ≠ 0`). -/
theorem vPath_spec {ρ γ : ℝ} (hρ : ρ ≠ 0) {us π : ℕ → Ω → ℝ} {K : Ω → ℝ} :
    (∀ t, ρ • vPath 𝔼 ρ γ us K π (t + 1) =
      (1 - γ) • vPath 𝔼 ρ γ us K π t - surprise 𝔼 π t - us (t + 1)) ∧
      ρ • vPath 𝔼 ρ γ us K π 0 + π 0 = K ∧
      ∀ v : ℕ → Ω → ℝ, (∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1)) →
        ρ • v 0 + π 0 = K → v = vPath 𝔼 ρ γ us K π := by
  refine ⟨fun t => ?_, ?_, fun v hv h0 => ?_⟩
  · change ρ • (((1 - γ) / ρ) • vPath 𝔼 ρ γ us K π t +
      ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1))) = _
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hρ, mul_inv_cancel₀ hρ, one_smul]
    abel
  · change ρ • (ρ⁻¹ • (K - π 0)) + π 0 = K
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_add_cancel]
  · have hrec : ∀ t, v (t + 1) = ((1 - γ) / ρ) • v t +
        ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1)) := fun t => by
      have h := congrArg (fun z => ρ⁻¹ • z) (hv t)
      simp only [smul_smul, inv_mul_cancel₀ hρ, one_smul] at h
      rw [h]
      simp only [smul_sub, smul_neg, smul_smul, inv_mul_eq_div]
      abel
    have hv0 : v 0 = ρ⁻¹ • (K - π 0) := by
      rw [← h0, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hρ, one_smul]
    rw [eq_dRec hrec, hv0]
    rfl

/-- Cochrane (2023), (23.4), p. 512: `vPath` is adapted when inflation and `u_s` are adapted and
`K` is known at date 0. -/
theorem vPath_adapted {ρ γ : ℝ} {us π : ℕ → Ω → ℝ} {K : Ω → ℝ} (hK : 𝔼.E 0 K = K)
    (hπa : 𝔼.Adapted π) (husa : 𝔼.Adapted us) : 𝔼.Adapted (vPath 𝔼 ρ γ us K π) := by
  refine dRec_adapted_of_succ 𝔼 ?_ (fun t => ?_)
  · rw [map_smul, map_sub, hK, hπa 0]
  · rw [map_smul, map_sub, map_neg, surprise, map_sub, hπa (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (𝔼.E_E_self t _), husa (t + 1)]

/-! ### Passive fiscal policy: the transversality condition holds automatically -/

/-- Cochrane (2023), p. 513 ("if `γ > 0` the value of debt grows more slowly than the interest
rate, so any unexpected inflation `ΔE_{t+1}π_{t+1}` is consistent with the transversality
condition"; survey error E12: the exact range is `0 < γ < 2`): for `0 ≤ ρ < 1`, `|1 − γ| < 1`
and bounded `u_s`, any debt path obeying (23.4) — whatever the inflation path, bounded or not —
satisfies the transversality condition. -/
theorem tvc_passive {ρ γ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hγ : |1 - γ| < 1)
    {us π v : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hv : ∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1)) : TVC 𝔼 ρ v := by
  intro t ω
  refine tendsto_zero_of_stable_rec (q := 1 - γ) (r := ρ) (C := |M|)
    (w := fun T => -(ρ ^ T * 𝔼.E t (us (t + T + 1)) ω)) hγ hρ0 hρ1 (fun T => ?_) (fun T => ?_)
  · rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hρ0 T), mul_comm]
    exact mul_le_mul_of_nonneg_right ((𝔼.abs_E_le (hus _) t ω).trans (le_abs_self M))
      (pow_nonneg hρ0 T)
  · have h := congrFun (congrArg (𝔼.E t) (hv (t + T))) ω
    rw [map_smul, map_sub, map_sub, map_smul, E_surprise_later 𝔼 π t T] at h
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero] at h
    rw [show t + (T + 1) = t + T + 1 by omega, pow_succ, mul_assoc, h]
    ring

/-! ### Monetary and fiscal forward solutions -/

/-- Cochrane (2023), (23.1)–(23.2), p. 512 (active money): the monetary forward solution
`π^m_t = −∑_{j ≥ 0} φ^{−j−1} E_t u_{i,t+j}` of `E_t π_{t+1} = φπ_t + u_{i,t}`. -/
noncomputable def piM (φ : ℝ) (ui : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries φ⁻¹ (fun t => (-φ⁻¹) • ui t)

/-- Cochrane (2023), (23.1)–(23.2), p. 512: for `|φ| > 1` and bounded adapted `u_i`, `π^m` is a
bounded adapted solution of `E_t π_{t+1} = φπ_t + u_{i,t}`, and it is the only bounded one. -/
theorem piM_spec {φ M : ℝ} (hφ : 1 < |φ|) {ui : ℕ → Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ M)
    (huia : 𝔼.Adapted ui) :
    (∀ t, 𝔼.E t (piM 𝔼 φ ui (t + 1)) = φ • piM 𝔼 φ ui t + ui t) ∧
      BoundedProc (piM 𝔼 φ ui) ∧ 𝔼.Adapted (piM 𝔼 φ ui) ∧
      ∀ π : ℕ → Ω → ℝ, BoundedProc π → (∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t) →
        π = piM 𝔼 φ ui := by
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, abs_zero] at hφ; linarith
  have ha : |φ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  have hf : ∀ t ω, |(fun t => (-φ⁻¹) • ui t) t ω| ≤ |φ⁻¹| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hui t ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun t => (-φ⁻¹) • ui t) := fun t => by
    simp only [map_smul, huia t]
  have hconv : ∀ π : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t) ↔
      ForwardSolution.Solves 𝔼 φ⁻¹ (fun t => (-φ⁻¹) • ui t) π := by
    intro π
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hf hfa
  refine ⟨(hconv _).mpr hsol, ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hf,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hf, fun π hπb hπ => ?_⟩
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 ha hf hfa ((hconv π).mp hπ) hπb

/-- Cochrane (2023), (23.3)–(23.4), p. 512 (active fiscal): the fiscal forward solution
`v^f_t = ∑_{j ≥ 0} ρʲ (1 − γ)^{−j−1} E_t u_{s,t+1+j}` of
`(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}`. -/
noncomputable def vF (ρ γ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (ρ / (1 - γ)) (fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1)))

/-- Cochrane (2023), (23.3)–(23.4), p. 512: for `0 < ρ < 1`, `|1 − γ| ≥ 1` and bounded `u_s`, `v^f`
is a bounded adapted solution of `(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}`. -/
theorem vF_spec {ρ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    (∀ t, (1 - γ) • vF 𝔼 ρ γ us t = ρ • 𝔼.E t (vF 𝔼 ρ γ us (t + 1)) + 𝔼.E t (us (t + 1))) ∧
      BoundedProc (vF 𝔼 ρ γ us) ∧ 𝔼.Adapted (vF 𝔼 ρ γ us) ∧ |ρ / (1 - γ)| < 1 := by
  have hq0 : (1 - γ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hγ; linarith
  have ha : |ρ / (1 - γ)| < 1 := by
    rw [abs_div, abs_of_pos hρ0, div_lt_one (by linarith)]
    linarith
  have hf : ∀ t ω, |(fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1))) t ω| ≤ |(1 - γ)⁻¹| * M :=
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hus _) t ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1))) := fun t => by
    simp only [map_smul, 𝔼.E_E_self]
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hf hfa
  refine ⟨fun t => ?_, ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hf,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hf, ha⟩
  have h := congrArg (fun z => (1 - γ) • z) (hsol t)
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hq0, one_smul,
    mul_div_cancel₀ _ hq0] at h
  exact h

/-- Cochrane (2023), (23.4), p. 512: in the Leeper model, taking `E_t` of (23.4),
`(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}` (adapted debt). -/
theorem leeper_debt_E {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hva : 𝔼.Adapted x.v) (t : ℕ) :
    (1 - γ) • x.v t = ρ • 𝔼.E t (x.v (t + 1)) + 𝔼.E t (us (t + 1)) := by
  have h := congrArg (𝔼.E t) (eq23_4 𝔼 hx t)
  rw [map_smul, map_sub, map_sub, map_smul, hva t, E_surprise, sub_zero] at h
  rw [h]
  abel

/-- Cochrane (2023), p. 513 ("only one value of unexpected inflation keeps debt from exploding"):
for `|1 − γ| ≥ 1`, an adapted debt path with `(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}` that
satisfies the transversality condition is the fiscal forward solution `v^f`. -/
theorem eq_vF {ρ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|) {us v : ℕ → Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ M) (htvc : TVC 𝔼 ρ v)
    (hv : ∀ t, (1 - γ) • v t = ρ • 𝔼.E t (v (t + 1)) + 𝔼.E t (us (t + 1))) :
    v = vF 𝔼 ρ γ us := by
  have hq0 : (1 - γ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hγ; linarith
  obtain ⟨hsol, ⟨B, hB⟩, -, ha⟩ := vF_spec 𝔼 hρ0 hρ1 hγ hus
  set a := ρ / (1 - γ) with ha_def
  set δ : ℕ → Ω → ℝ := fun t => v t - vF 𝔼 ρ γ us t with hδ_def
  have hδ : ∀ t, δ t = a • 𝔼.E t (δ (t + 1)) := by
    intro t
    have e : (1 - γ) • δ t = ρ • 𝔼.E t (δ (t + 1)) := by
      simp only [hδ_def, map_sub, smul_sub]
      rw [hv t, hsol t]
      abel
    have e2 := congrArg (fun z => (1 - γ)⁻¹ • z) e
    simp only [smul_smul, inv_mul_cancel₀ hq0, one_smul] at e2
    rw [e2, ha_def, div_eq_inv_mul]
  funext t ω
  have hit : ∀ k, δ t ω = a ^ k * 𝔼.E t (v (t + k)) ω - a ^ k * 𝔼.E t (vF 𝔼 ρ γ us (t + k)) ω :=
    fun k => by
      have := congrFun (𝔼.forward_iterate hδ t k) ω
      rw [this]
      simp only [hδ_def, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
  have h1 : Tendsto (fun k : ℕ => a ^ k * 𝔼.E t (v (t + k)) ω) atTop (𝓝 0) := by
    have hq1 : ∀ k : ℕ, |a ^ k * 𝔼.E t (v (t + k)) ω| ≤ |ρ ^ k * 𝔼.E t (v (t + k)) ω| := by
      intro k
      rw [ha_def, div_pow, abs_mul, abs_mul, abs_div]
      have hpos : 0 < |(1 - γ) ^ k| := abs_pos.mpr (pow_ne_zero k hq0)
      have hge : 1 ≤ |(1 - γ) ^ k| := by rw [abs_pow]; exact one_le_pow₀ hγ
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hge
    have hT : Tendsto (fun k : ℕ => |ρ ^ k * 𝔼.E t (v (t + k)) ω|) atTop (𝓝 0) := by
      simpa using (htvc t ω).abs
    refine squeeze_zero_norm (fun k => ?_) hT
    rw [Real.norm_eq_abs]
    exact hq1 k
  have h2 : Tendsto (fun k : ℕ => a ^ k * 𝔼.E t (vF 𝔼 ρ γ us (t + k)) ω) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun k => |a| ^ k * B) (fun k => ?_) ?_
    · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB _) t ω) (pow_nonneg (abs_nonneg a) k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const B
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have h4 : Tendsto (fun _ : ℕ => δ t ω) atTop (𝓝 0) := h3.congr fun k => (hit k).symm
  have := tendsto_nhds_unique tendsto_const_nhds h4
  simpa [hδ_def, sub_eq_zero] using this

/-- Cochrane (2023), (23.4), p. 512: the unexpected inflation that the fiscal forward solution
requires, `ν^f_{t+1} = (1 − γ)v^f_t − ρ v^f_{t+1} − u_{s,t+1}`. -/
noncomputable def nuF (ρ γ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (1 - γ) • vF 𝔼 ρ γ us t - ρ • vF 𝔼 ρ γ us (t + 1) - us (t + 1)

/-- Cochrane (2023), p. 513 ("if `γ = 0`, then only one value of unexpected inflation keeps debt
from exploding", generalised to `|1 − γ| ≥ 1`, any `φ`): in every admissible equilibrium of the
Leeper model, debt is the fiscal forward solution and unexpected inflation is `ν^f`. -/
theorem active_fiscal_forced {ρ φ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|)
    {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    x.v = vF 𝔼 ρ γ us ∧ ∀ t, surprise 𝔼 x.pi t = nuF 𝔼 ρ γ us t := by
  have hv := eq_vF 𝔼 hρ0 hρ1 hγ hus hadm.2.2.2 (leeper_debt_E 𝔼 hx hadm.2.1)
  refine ⟨hv, fun t => ?_⟩
  have h := eq23_4 𝔼 hx t
  rw [hv] at h
  rw [nuF, h]
  abel

/-! ### Region (a): active money, passive fiscal -/

/-- Cochrane (2023), §22.7, p. 508, and (23.1)–(23.4), p. 512 (active money): for `|φ| > 1`
(any `γ`) inflation in every admissible equilibrium is `π^m`, and the whole path is
`mkPath π^m (vPath π^m)`. -/
theorem active_money_forced {ρ φ γ Mi : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < |φ|) {ui us : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi) (huia : 𝔼.Adapted ui) {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    x = mkPath φ γ ui us (piM 𝔼 φ ui) (vPath 𝔼 ρ γ us K (piM 𝔼 φ ui)) := by
  obtain ⟨hxe, hπ, hv, h0⟩ := eq_mkPath 𝔼 hx
  have hpi : x.pi = piM 𝔼 φ ui := (piM_spec 𝔼 hφ hui huia).2.2.2 x.pi hadm.2.2.1 hπ
  rw [hpi] at hv h0
  have hvv := (vPath_spec 𝔼 hρ).2.2 x.v hv h0
  rw [hxe, hpi, hvv]

/-- Cochrane (2023), §22.3, p. 500, §22.7, p. 508, and (23.1)–(23.4), p. 512, region (a): for
`|φ| > 1` and `0 < γ < 2` the Leeper model has exactly one admissible equilibrium. -/
theorem region_a {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    ∃! x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  obtain ⟨hπ, hπb, hπa, -⟩ := piM_spec 𝔼 hφ hui huia
  obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := piM 𝔼 φ ui)
  refine ⟨mkPath φ γ ui us (piM 𝔼 φ ui) (vPath 𝔼 ρ γ us K (piM 𝔼 φ ui)),
    ⟨mkPath_eqm 𝔼 hπ hv h0, hπa, vPath_adapted 𝔼 hK hπa husa, hπb,
      tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩, fun x hx => ?_⟩
  exact active_money_forced 𝔼 hρ0.ne' hφ hui huia hx.1 hx.2

/-! ### Region (b): active fiscal, passive money -/

/-- Cochrane (2023), (23.1)–(23.4), p. 512 (active fiscal): the inflation path
`π_0 = K − ρ v^f_0`, `π_{t+1} = φπ_t + u_{i,t} + ν^f_{t+1}`. -/
noncomputable def piB (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) : ℕ → Ω → ℝ :=
  dRec φ (fun t => ui t + nuF 𝔼 ρ γ us t) (K - ρ • vF 𝔼 ρ γ us 0)

/-- Cochrane (2023), §22.3, p. 500, §22.7, p. 508, and (23.1)–(23.4), p. 512, region (b) (the
book: `φ < 1, γ = 0`; survey error E12: `|φ| < 1` and `γ ≤ 0 ∨ γ ≥ 2`): exactly one admissible
equilibrium — the fiscal theory of the price level with an interest-rate rule (bounded `K`). -/
theorem region_b {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) (hKb : ∃ C, ∀ ω, |K ω| ≤ C) :
    ∃! x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  obtain ⟨hsol, ⟨B, hB⟩, hFa, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
  set π := piB 𝔼 ρ φ γ ui us K with hπ_def
  have hnu0 : ∀ t, 𝔼.E t (nuF 𝔼 ρ γ us t) = 0 := fun t => by
    rw [nuF, map_sub, map_sub, map_smul, map_smul, hFa t, hsol t]
    abel
  have hπa : 𝔼.Adapted π := by
    refine dRec_adapted_of_succ 𝔼 ?_ (fun t => ?_)
    · rw [map_sub, map_smul, hK, hFa 0]
    · rw [map_add, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t), nuF, map_sub,
        map_sub, map_smul, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t),
        hFa (t + 1), husa (t + 1)]
  have hπE : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t := fun t => by
    change 𝔼.E t (φ • π t + (ui t + nuF 𝔼 ρ γ us t)) = _
    rw [map_add, map_smul, map_add, hπa t, huia t, hnu0 t, add_zero]
  have hsur : ∀ t, surprise 𝔼 π t = nuF 𝔼 ρ γ us t := fun t => by
    rw [surprise, hπE t]
    change φ • π t + (ui t + nuF 𝔼 ρ γ us t) - (φ • π t + ui t) = _
    abel
  have hv : ∀ t, ρ • vF 𝔼 ρ γ us (t + 1) =
      (1 - γ) • vF 𝔼 ρ γ us t - surprise 𝔼 π t - us (t + 1) := fun t => by
    rw [hsur t, nuF]
    abel
  have h0 : ρ • vF 𝔼 ρ γ us 0 + π 0 = K := by
    change ρ • vF 𝔼 ρ γ us 0 + (K - ρ • vF 𝔼 ρ γ us 0) = K
    abel
  have hπb : BoundedProc π := by
    obtain ⟨C, hC⟩ := hKb
    refine ⟨(|C| + ρ * |B|) + (|Mi| + (|1 - γ| * |B| + ρ * |B| + |Ms|)) / (1 - |φ|),
      rec_bounded hφ (by positivity) (by positivity) (fun t ω => ?_) (fun t => rfl)
        (fun ω => ?_)⟩
    · have a1 := (hui t ω).trans (le_abs_self Mi)
      have a2 := (hB t ω).trans (le_abs_self B)
      have a3 := (hB (t + 1) ω).trans (le_abs_self B)
      have a4 := (hus (t + 1) ω).trans (le_abs_self Ms)
      simp only [Pi.add_apply, nuF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add a1 ?_)
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) a4)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
      · rw [abs_mul, abs_of_pos hρ0]; exact mul_le_mul_of_nonneg_left a3 hρ0.le
    · change |K ω - ρ * vF 𝔼 ρ γ us 0 ω| ≤ _
      refine (abs_sub _ _).trans (add_le_add ((hC ω).trans (le_abs_self C)) ?_)
      rw [abs_mul, abs_of_pos hρ0]
      exact mul_le_mul_of_nonneg_left ((hB 0 ω).trans (le_abs_self B)) hρ0.le
  refine ⟨mkPath φ γ ui us π (vF 𝔼 ρ γ us), ⟨mkPath_eqm 𝔼 hπE hv h0, hπa, hFa, hπb,
    tvc_of_bounded 𝔼 (by rw [abs_of_pos hρ0]; exact hρ1) ⟨B, hB⟩⟩, fun x hx => ?_⟩
  obtain ⟨hvx, hsx⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx.1 hx.2
  obtain ⟨hxe, hπx, -, h0x⟩ := eq_mkPath 𝔼 hx.1
  have hrec : ∀ t, x.pi (t + 1) = φ • x.pi t + (ui t + nuF 𝔼 ρ γ us t) := fun t => by
    have h1 := hsx t
    rw [surprise, hπx t] at h1
    rw [← h1]
    abel
  have hpi : x.pi = π := by
    change x.pi = dRec φ (fun t => ui t + nuF 𝔼 ρ γ us t) (K - ρ • vF 𝔼 ρ γ us 0)
    rw [eq_dRec hrec]
    congr 1
    rw [← h0x, hvx]
    abel
  rw [hxe, hpi, hvx]

/-! ### Region (c): both active -/

/-- Cochrane (2023), §22.7, p. 508 ("if `φ > 1` and `γ = 0` both policies are active … inflation
is overdetermined"), region (c) with `|φ| > 1`, `γ ≤ 0 ∨ γ ≥ 2`: an admissible equilibrium
exists iff the date-0 restriction `ρ v^f_0 + π^m_0 = K` and the cross-restriction
`ΔE_{t+1}π^m_{t+1} = ν^f_{t+1}` on the disturbances hold. -/
theorem region_c_iff {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔
      (ρ • vF 𝔼 ρ γ us 0 + piM 𝔼 φ ui 0 = K ∧
        ∀ t, surprise 𝔼 (piM 𝔼 φ ui) t = nuF 𝔼 ρ γ us t) := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  obtain ⟨hπ, hπb, hπa, hπu⟩ := piM_spec 𝔼 hφ hui huia
  obtain ⟨-, ⟨B, hB⟩, hFa, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
  constructor
  · rintro ⟨x, hx, hadm⟩
    obtain ⟨hvx, hsx⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx hadm
    have hpx : x.pi = piM 𝔼 φ ui := hπu x.pi hadm.2.2.1 (leeper_expected_inflation 𝔼 hx)
    refine ⟨?_, fun t => ?_⟩
    · rw [← hvx, ← hpx]; exact hx.2.2.2.2.2
    · rw [← hpx]; exact hsx t
  · rintro ⟨h0, hs⟩
    refine ⟨mkPath φ γ ui us (piM 𝔼 φ ui) (vF 𝔼 ρ γ us), mkPath_eqm 𝔼 hπ (fun t => ?_) h0,
      hπa, hFa, hπb, tvc_of_bounded 𝔼 (by rw [abs_of_pos hρ0]; exact hρ1) ⟨B, hB⟩⟩
    rw [hs t, nuF]
    abel

/-- Cochrane (2023), §22.7, p. 508 (generic non-existence in region (c)): for given
disturbances, at most one inherited debt `K` admits an admissible equilibrium. -/
theorem region_c_unique_K {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K₁ K₂ : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms)
    (h₁ : ∃ x, LeeperEqm 𝔼 ρ φ γ ui us K₁ x ∧ Admissible 𝔼 ρ x)
    (h₂ : ∃ x, LeeperEqm 𝔼 ρ φ γ ui us K₂ x ∧ Admissible 𝔼 ρ x) : K₁ = K₂ := by
  rw [← ((region_c_iff 𝔼 hρ0 hρ1 hφ hγ hui huia hus).mp h₁).1,
    ← ((region_c_iff 𝔼 hρ0 hρ1 hφ hγ hui huia hus).mp h₂).1]

/-- Cochrane (2023), (23.1)–(23.4), p. 512: with zero monetary disturbance the monetary forward
solution is zero. -/
theorem piM_zero (φ : ℝ) : piM 𝔼 φ (0 : ℕ → Ω → ℝ) = 0 := by
  funext t ω
  simp [piM, ExpectationSystem.forwardSeries]

/-- Cochrane (2023), (23.3)–(23.4), p. 512: when fiscal disturbances are unforecastable
(`E_t u_{s,t+1} = 0`) the fiscal forward solution is zero. -/
theorem vF_zero_of_md {ρ γ : ℝ} {us : ℕ → Ω → ℝ} (hmd : ∀ t, 𝔼.E t (us (t + 1)) = 0) :
    vF 𝔼 ρ γ us = 0 := by
  funext t ω
  simp [vF, ExpectationSystem.forwardSeries, hmd]

/-- Cochrane (2023), §22.7, p. 508 (the cross-restriction fails under genuine uncertainty): in
region (c), with no monetary disturbance and unforecastable fiscal disturbances that are not
identically zero, no inherited debt `K` admits an admissible equilibrium. -/
theorem region_c_md_nonexistence {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ Ms)
    (hmd : ∀ t, 𝔼.E t (us (t + 1)) = 0) (hne : ∃ t ω, us (t + 1) ω ≠ 0) (K : Ω → ℝ) :
    ¬ ∃ x, LeeperEqm 𝔼 ρ φ γ 0 us K x ∧ Admissible 𝔼 ρ x := by
  intro h
  have hz : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨-, hs⟩ := (region_c_iff 𝔼 hρ0 hρ1 hφ hγ hz (fun t => by simp) hus).mp h
  obtain ⟨t, ω, hω⟩ := hne
  have h1 := congrFun (hs t) ω
  rw [piM_zero, nuF, vF_zero_of_md 𝔼 hmd] at h1
  simp only [surprise, Pi.zero_apply, map_zero, Pi.sub_apply, sub_self, smul_zero, zero_sub,
    zero_eq_neg] at h1
  exact hω h1

/-- Cochrane (2023), §22.7, p. 508, on the coin-flip tree: with `φ = 2`, `γ = 0`, no monetary
disturbance and the coin-flip fiscal shock `u_{s,t} = ±1`, there is no admissible equilibrium for
any inherited debt — both-active policy is inconsistent under genuine uncertainty. -/
theorem region_c_coin {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (K : Bool × Bool → ℝ) :
    ¬ ∃ x, LeeperEqm ExpectationsFiniteTree.coinSystem ρ 2 0 0 ExpectationsFiniteTree.coinShock
      K x ∧ Admissible ExpectationsFiniteTree.coinSystem ρ x := by
  obtain ⟨M, hM⟩ := coinShock_bounded
  refine region_c_md_nonexistence ExpectationsFiniteTree.coinSystem hρ0 hρ1 (by norm_num)
    (Or.inl le_rfl) hM ExpectationsFiniteTree.coinShock_mean_zero ⟨0, (true, true), ?_⟩ K
  simp [ExpectationsFiniteTree.coinShock]

/-- Cochrane (2023), §22.7, p. 508 (survey error E19, confirmed): with `φ > 1` and `γ = 0`, in the
starred form every consistent admissible target is the unique admissible equilibrium, while in
the unstarred form (zero disturbances) no admissible equilibrium exists for any nonzero
inherited debt. -/
theorem e19_starred_vs_unstarred {ρ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < φ) :
    (∀ tg : Outcome Ω, Consistent 𝔼 ρ tg → Admissible 𝔼 ρ tg →
      Eqm 𝔼 ρ φ 0 tg tg ∧ UniqueEqm 𝔼 ρ φ 0 tg) ∧
    ∀ K : Ω → ℝ, K ≠ 0 → ¬ ∃ x, LeeperEqm 𝔼 ρ φ 0 0 0 K x ∧ Admissible 𝔼 ρ x := by
  have hφ' : 1 < |φ| := by rw [abs_of_pos (by linarith)]; exact hφ
  refine ⟨fun tg hc htg => ⟨starred_eqm 𝔼 φ 0 hc, (unique_double_active 𝔼 hρ0.ne' hφ hc htg).2⟩,
    fun K hK h => hK ?_⟩
  have hz : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨h0, -⟩ := (region_c_iff 𝔼 hρ0 hρ1 hφ' (Or.inl le_rfl) hz (fun t => by simp) hz).mp h
  rw [← h0, piM_zero, vF_zero_of_md 𝔼 (fun t => by simp)]
  simp

/-! ### Region (d): double passive -/

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) (`|φ| < 1`, `0 < γ < 2`, "we are back to
indeterminacy"): the admissible equilibria of the Leeper model form an uncountable set, indexed
by the date-0 inflation rate. -/
theorem region_d [Nonempty Ω] {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  let f : ℝ → Outcome Ω := fun c =>
    mkPath φ γ ui us (dRec φ ui (fun _ => c)) (vPath 𝔼 ρ γ us K (dRec φ ui (fun _ => c)))
  have hmaps : Set.MapsTo f Set.univ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x} := by
    intro c _
    have hπa : 𝔼.Adapted (dRec φ ui (fun _ => c)) := dRec_adapted 𝔼 huia
    obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K)
      (π := dRec φ ui (fun _ => c))
    refine ⟨mkPath_eqm 𝔼 (fun t => ?_) hv h0, hπa, vPath_adapted 𝔼 hK hπa husa,
      ⟨|c| + |Mi| / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (abs_nonneg Mi)
        (fun t ω => (hui t ω).trans (le_abs_self Mi)) (fun t => rfl) (fun ω => le_rfl)⟩,
      tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩
    change 𝔼.E t (φ • dRec φ ui (fun _ => c) t + ui t) = _
    rw [map_add, map_smul, hπa t, huia t]
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
    simpa [f, mkPath, dRec] using this
  intro hcount
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), p. 513 (survey error E12: "`γ > 0`" is not enough for passive fiscal policy):
with `γ = 3` the debt path and unexpected inflation of every admissible equilibrium are pinned
down (`v = v^f`, `ΔE_{t+1}π_{t+1} = ν^f_{t+1}`), whatever `φ`. -/
theorem gamma_three_active {ρ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ui us : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {x y : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ 3 ui us K x) (hxa : Admissible 𝔼 ρ x)
    (hy : LeeperEqm 𝔼 ρ φ 3 ui us K y) (hya : Admissible 𝔼 ρ y) :
    x.v = y.v ∧ ∀ t, surprise 𝔼 x.pi t = surprise 𝔼 y.pi t := by
  have hγ : 1 ≤ |1 - (3 : ℝ)| := by norm_num
  obtain ⟨h1, h2⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ hus hx hxa
  obtain ⟨h3, h4⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ hus hy hya
  exact ⟨h1.trans h3.symm, fun t => (h2 t).trans (h4 t).symm⟩

/-! ### Region (d): genuinely random sunspots and the boundary `|φ| = 1` -/

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) with sunspots (`|φ| < 1`, `0 < γ < 2`): for
every bounded adapted martingale difference `ν` and every date-0 inflation `c`, the inflation path
`π_0 = c`, `π_{t+1} = φπ_t + u_{i,t} + ν_{t+1}` with debt from (23.4) is an admissible equilibrium
whose unexpected inflation is `ν`. -/
theorem region_d_sunspot {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us ν : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) (hνa : 𝔼.Adapted ν) (hνb : BoundedProc ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) (c : ℝ) :
    LeeperEqm 𝔼 ρ φ γ ui us K (mkPath φ γ ui us (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c))
        (vPath 𝔼 ρ γ us K (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)))) ∧
      Admissible 𝔼 ρ (mkPath φ γ ui us (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c))
        (vPath 𝔼 ρ γ us K (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)))) ∧
      ∀ t, surprise 𝔼 (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)) t = ν (t + 1) := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  set π := dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c) with hπ_def
  have hπa : 𝔼.Adapted π := dRec_adapted_of_succ 𝔼 (𝔼.const 0 c) (fun t => by
    rw [map_add, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t), hνa (t + 1)])
  have hπE : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t := fun t => by
    change 𝔼.E t (φ • π t + (ui t + ν (t + 1))) = _
    rw [map_add, map_smul, map_add, hπa t, huia t, hmd t, add_zero]
  obtain ⟨M, hM⟩ := hνb
  obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := π)
  refine ⟨mkPath_eqm 𝔼 hπE hv h0, ⟨hπa, vPath_adapted 𝔼 hK hπa husa,
    ⟨|c| + (|Mi| + |M|) / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (by positivity)
      (fun t ω => (abs_add_le _ _).trans (add_le_add ((hui t ω).trans (le_abs_self Mi))
        ((hM (t + 1) ω).trans (le_abs_self M)))) (fun t => rfl) (fun ω => le_rfl)⟩,
    tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩, fun t => ?_⟩
  rw [surprise, hπE t]
  change φ • π t + (ui t + ν (t + 1)) - (φ • π t + ui t) = _
  abel

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) on the coin-flip tree: for `|φ| < 1`,
`0 < γ < 2` and any bounded adapted disturbances, the Leeper model has an admissible equilibrium
whose date-1 unexpected inflation is the coin flip `±1` — a genuinely random sunspot
equilibrium. -/
theorem region_d_coin {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Bool × Bool → ℝ} {K : Bool × Bool → ℝ}
    (hui : ∀ t ω, |ui t ω| ≤ Mi) (huia : ExpectationsFiniteTree.coinSystem.Adapted ui)
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : ExpectationsFiniteTree.coinSystem.Adapted us)
    (hK : ExpectationsFiniteTree.coinSystem.E 0 K = K) :
    ∃ x, LeeperEqm ExpectationsFiniteTree.coinSystem ρ φ γ ui us K x ∧
      Admissible ExpectationsFiniteTree.coinSystem ρ x ∧
      surprise ExpectationsFiniteTree.coinSystem x.pi 0 = ExpectationsFiniteTree.coinShock 1 := by
  obtain ⟨h1, h2, h3⟩ := region_d_sunspot ExpectationsFiniteTree.coinSystem hρ0 hρ1 hφ hγ hui
    huia hus husa hK coinShock_adapted coinShock_bounded
    ExpectationsFiniteTree.coinShock_mean_zero 0
  exact ⟨_, h1, h2, h3 0⟩

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) extended to `|φ| ≤ 1` (in particular the
boundary `|φ| = 1`): if the monetary equation `E_t π_{t+1} = φπ_t + u_{i,t}` has one bounded
adapted solution, the admissible equilibria form an uncountable set (indexed by the date-0
jump `c`, `π_t = π̄_t + c φᵗ`). -/
theorem region_d_of_solution [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : |φ| ≤ 1) (hγ : 0 < γ ∧ γ < 2) {ui us pb : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K)
    (hpa : 𝔼.Adapted pb) (hpb : BoundedProc pb) (hpE : ∀ t, 𝔼.E t (pb (t + 1)) = φ • pb t + ui t) :
    ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  obtain ⟨M, hM⟩ := hpb
  let g : ℝ → ℕ → Ω → ℝ := fun c t => pb t + fun _ => c * φ ^ t
  let f : ℝ → Outcome Ω := fun c => mkPath φ γ ui us (g c) (vPath 𝔼 ρ γ us K (g c))
  have hmaps : Set.MapsTo f Set.univ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x} := by
    intro c _
    have hga : 𝔼.Adapted (g c) := fun t => by
      change 𝔼.E t (pb t + fun _ => c * φ ^ t) = _
      rw [map_add, hpa t, 𝔼.const]
    have hgE : ∀ t, 𝔼.E t (g c (t + 1)) = φ • g c t + ui t := fun t => by
      change 𝔼.E t (pb (t + 1) + fun _ => c * φ ^ (t + 1)) = φ • (pb t + fun _ => c * φ ^ t) + ui t
      rw [map_add, hpE t, 𝔼.const]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := g c)
    refine ⟨mkPath_eqm 𝔼 hgE hv h0, hga, vPath_adapted 𝔼 hK hga husa,
      ⟨M + |c|, fun t ω => ?_⟩, tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩
    change |pb t ω + c * φ ^ t| ≤ M + |c|
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg c) (pow_le_one₀ (abs_nonneg φ) hφ)
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
    simpa [f, g, mkPath] using this
  intro hcount
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), §22.7, p. 508 (the boundary `|φ| = 1`, including `φ = −1 < 1` that the book
counts as passive): with the bounded monetary disturbance `u_{i,t} = −φ^{t+1}` the Leeper model
has no admissible equilibrium at all, for every `γ`, `u_s` and `K`. So at `|φ| = 1` neither
determinacy nor indeterminacy holds in general: existence depends on `u_i`. -/
theorem region_d_unit_nonexistence [Nonempty Ω] {ρ φ γ : ℝ} (hφ : φ ^ 2 = 1)
    {us : ℕ → Ω → ℝ} {K : Ω → ℝ} :
    ¬ ∃ x, LeeperEqm 𝔼 ρ φ γ (fun t _ => -(φ * φ ^ t)) us K x ∧ Admissible 𝔼 ρ x := by
  rintro ⟨x, hx, hadm⟩
  have hπ := leeper_expected_inflation 𝔼 hx
  have hsol : ForwardSolution.Solves 𝔼 φ (fun t _ => 1 * φ ^ t) x.pi := by
    intro t
    have h := congrArg (fun z => φ • z) (hπ t)
    funext ω
    have h' := congrFun h ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h' ⊢
    have hφ2 : φ * φ = 1 := by rw [← sq]; exact hφ
    linear_combination -h' - (x.pi t ω - φ ^ t) * hφ2
  exact ForwardSolution.no_bounded_solution_unit 𝔼 hφ one_ne_zero hsol hadm.2.2.1

/-! ### Region (b): the bounded inherited debt is necessary -/

/-- Cochrane (2023), §22.7, p. 508, region (b) without assuming `K` bounded: an admissible
equilibrium exists iff the inherited debt `K` is bounded (then it is unique, `region_b`), since
`π_0 = K − ρ v^f_0` is forced and must be bounded. -/
theorem region_b_iff {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ ∃ C, ∀ ω, |K ω| ≤ C := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  constructor
  · rintro ⟨x, hx, hadm⟩
    obtain ⟨hvx, -⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx hadm
    obtain ⟨-, ⟨B, hB⟩, -, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
    obtain ⟨M, hM⟩ := hadm.2.2.1
    refine ⟨ρ * B + M, fun ω => ?_⟩
    have h0 := congrFun hx.2.2.2.2.2 ω
    rw [hvx] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
    rw [← h0]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM 0 ω))
    rw [abs_mul, abs_of_pos hρ0]
    exact mul_le_mul_of_nonneg_left (hB 0 ω) hρ0.le
  · intro hKb
    exact (region_b 𝔼 hρ0 hρ1 hφ hγ hui huia hus husa hK hKb).exists

/-- Cochrane (2023), §22.7, p. 508 (the bounded-`K` hypothesis of `region_b` is needed): with
states `ω ∈ ℕ`, full information and the unbounded inherited debt `K ω = ω`, region (b) (e.g.
`φ = 0`, `γ = 0`, no disturbances) has no admissible equilibrium. -/
theorem region_b_unbounded_K {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ¬ ∃ x, LeeperEqm (fullInfo ℕ) ρ 0 0 0 0 (fun ω => (ω : ℝ)) x ∧
      Admissible (fullInfo ℕ) ρ x := by
  intro h
  have hz : ∀ t ω, |(0 : ℕ → ℕ → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨C, hC⟩ := (region_b_iff (fullInfo ℕ) hρ0 hρ1 (by norm_num) (Or.inl le_rfl) hz
    (fun t => rfl) hz (fun t => rfl) rfl).mp h
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC n
  rw [abs_of_nonneg (Nat.cast_nonneg n)] at this
  linarith

/-! ### Dependence on the equilibrium criterion: bounded debt -/

/-- Cochrane (2023), §22.7, p. 508 (the Woodford/Leeper criterion): inflation and debt adapted
and both bounded. -/
def AdmissibleB (x : Outcome Ω) : Prop :=
  𝔼.Adapted x.pi ∧ 𝔼.Adapted x.v ∧ BoundedProc x.pi ∧ BoundedProc x.v

/-- Cochrane (2023), §22.7, p. 508: the target is the unique equilibrium under the bounded-debt
criterion. -/
def UniqueEqmB (ρ φ γ : ℝ) (tg : Outcome Ω) : Prop :=
  ∀ x, Eqm 𝔼 ρ φ γ tg x → AdmissibleB 𝔼 x → x = tg

/-- Cochrane (2023), §22.1, p. 495: bounded debt satisfies the transversality condition, so the
bounded criterion is stronger. -/
theorem admissible_of_B {ρ : ℝ} (hρ : |ρ| < 1) {x : Outcome Ω} (h : AdmissibleB 𝔼 x) :
    Admissible 𝔼 ρ x :=
  ⟨h.1, h.2.1, h.2.2.1, tvc_of_bounded 𝔼 hρ h.2.2.2⟩

/-- Cochrane (2023), §22.7, p. 508 (and Woodford (2003), Prop. 4.11; survey "boundary depends on
the criterion"): under the bounded-debt criterion the target is the unique equilibrium iff
`|φ| > 1` or `|1 − γ| > ρ`, so the passive-fiscal range is `1 − ρ ≤ γ ≤ 1 + ρ` rather than
`0 < γ < 2`. -/
theorem uniqueB_iff [Nonempty Ω] {ρ φ γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : AdmissibleB 𝔼 tg) :
    UniqueEqmB 𝔼 ρ φ γ tg ↔ 1 < |φ| ∨ ρ < |1 - γ| := by
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  constructor
  · intro hu
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    obtain ⟨hφ, hγ⟩ := hcon
    have hq : |(1 - γ) / ρ| ≤ 1 := by
      rw [abs_div, abs_of_pos hρ0, div_le_one hρ0]; exact hγ
    have hx := famPath_eqm 𝔼 hρ0.ne' hc (φ := φ) (γ := γ) 1
    have hB : AdmissibleB 𝔼 (famPath ρ φ γ tg 1) := by
      obtain ⟨hpa, hva, ⟨M, hM⟩, ⟨N, hN⟩⟩ := htg
      refine ⟨fun t => ?_, fun t => ?_, ⟨M + 1, fun t ω => ?_⟩, ⟨N + |1 / ρ|, fun t ω => ?_⟩⟩
      · change 𝔼.E t (tg.pi t + famE φ 1 t) = tg.pi t + famE φ 1 t
        rw [map_add, hpa t]
        congr 1
        exact 𝔼.const t _
      · change 𝔼.E t (tg.v t + famD ρ γ 1 t) = tg.v t + famD ρ γ 1 t
        rw [map_add, hva t]
        congr 1
        exact 𝔼.const t _
      · change |tg.pi t ω + 1 * φ ^ t| ≤ M + 1
        refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
        rw [one_mul, abs_pow]
        exact pow_le_one₀ (abs_nonneg φ) hφ
      · change |tg.v t ω + -(1 / ρ) * ((1 - γ) / ρ) ^ t| ≤ N + |1 / ρ|
        refine (abs_add_le _ _).trans (add_le_add (hN t ω) ?_)
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)
    have h1 := hu _ hx hB
    have h0 : famPath ρ φ γ tg 0 = tg := by
      rw [famPath]
      have e1 : famE φ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famE]
      have e2 : famD ρ γ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famD]
      rw [e1, e2, ofDev_zero]
    have := famPath_injective ρ φ γ tg (h1.trans h0.symm)
    norm_num at this
  · rintro (hφ | hγ) x hx hxB
    · exact unique_of_active_money 𝔼 hρ0.ne' hφ hc (admissible_of_B 𝔼 hρa htg) x hx
        (admissible_of_B 𝔼 hρa hxB)
    · obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
      obtain ⟨hpa, hva, -, ⟨N, hN⟩⟩ := htg
      obtain ⟨-, hva', -, ⟨N', hN'⟩⟩ := hxB
      have hda : 𝔼.Adapted (fun t => x.v t - tg.v t) := fun t => by
        simp only [map_sub, hva t, hva' t]
      have hdb : BoundedProc (fun t => x.v t - tg.v t) := ⟨N' + N, fun t ω => by
        simp only [Pi.sub_apply]
        exact (abs_sub _ _).trans (add_le_add (hN' t ω) (hN t ω))⟩
      have hAR := isAR1_of_dyn 𝔼 (d := fun t => x.v t - tg.v t) hρ0.ne' hda hd
        (fun t => E_surprise 𝔼 _ t)
      have hgt : 1 < |(1 - γ) / ρ| := by
        rw [abs_div, abs_of_pos hρ0, one_lt_div hρ0]; exact hγ
      have d0 : (fun t => x.v t - tg.v t) = 0 := zero_of_E_succ_eq_smul 𝔼 hgt hdb hAR.2
      have e0 := e_zero_of_d_zero 𝔼 (e := fun t => x.pi t - tg.pi t) d0 he hd h0
      rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.7, p. 508, and pp. 512–513 (the regime boundary depends on the
criterion): for `|φ| ≤ 1` and `γ = (1 − ρ)/2 ∈ (0, 1 − ρ)`, fiscal policy is passive under the
transversality criterion (a continuum of equilibria) but active under the bounded-debt
criterion (the target is the unique equilibrium). -/
theorem criterion_matters [Nonempty Ω] {ρ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : AdmissibleB 𝔼 tg) :
    ¬ UniqueEqm 𝔼 ρ φ ((1 - ρ) / 2) tg ∧ UniqueEqmB 𝔼 ρ φ ((1 - ρ) / 2) tg := by
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have habs : |1 - (1 - ρ) / 2| = (1 + ρ) / 2 := by
    rw [abs_of_pos (by linarith)]; ring
  refine ⟨not_unique_of_passive 𝔼 hρ0.ne' hφ (by rw [habs]; linarith) hc
    (admissible_of_B 𝔼 hρa htg), (uniqueB_iff 𝔼 hρ0 hρ1 hc htg).mpr (Or.inr ?_)⟩
  rw [habs]
  linarith

/-- Woodford (2003), p. 313, in Cochrane's notation (Cochrane (2023), §22.7, p. 508): a fiscal
rule with debt feedback `γ` (Woodford's `τ_b`) and discount `ρ` (Woodford's `β`) is locally
Ricardian — keeps debt bounded — iff `|1 − γ| < ρ`. -/
theorem locallyRicardian_iff_gamma [Nonempty Ω] {ρ bb γ τg τπ τy τi : ℝ} (hρ : 0 < ρ) :
    LocallyRicardian Ω ρ bb γ τg τπ τy τi ↔ |1 - γ| < ρ := by
  rw [locallyRicardian_iff hρ, abs_mul, abs_inv, abs_of_pos hρ, inv_mul_lt_iff₀ hρ, mul_one]

/-! ### The printed (16.21)–(16.22): both debt equations use the actual surplus -/

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and (22.1), p. 495, as printed (PDF p. 399): when the
starred debt equation `ρ v*_{t+1} = v*_t − ΔE_{t+1}π*_{t+1} − s̃_{t+1}` uses the *actual* surplus,
the gap `d = v − v*` obeys `ρ d_{t+1} = d_t − ΔE_{t+1}(π − π*)_{t+1}`: `γ` drops out. -/
theorem literal_gap {ρ : ℝ} {piS π vS v s : ℕ → Ω → ℝ}
    (hS : ∀ t, ρ • vS (t + 1) = vS t - surprise 𝔼 piS t - s (t + 1))
    (h : ∀ t, ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1)) (t : ℕ) :
    ρ • (v (t + 1) - vS (t + 1)) = (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t := by
  rw [smul_sub, h t, hS t]
  simp only [surprise, map_sub]
  abel

/-- Cochrane (2023), (16.21), p. 373, as printed, with
`s̃_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`:
`ρ v*_{t+1} = (1 − α) v*_t − γ(v_t − v*_t) − ΔE_{t+1}π*_{t+1} − u_{s,t+1}`. -/
theorem literal_vS {ρ α γ : ℝ} {piS vS v s us : ℕ → Ω → ℝ}
    (hS : ∀ t, ρ • vS (t + 1) = vS t - surprise 𝔼 piS t - s (t + 1))
    (hs : ∀ t, s (t + 1) = α • vS t + γ • (v t - vS t) + us (t + 1)) (t : ℕ) :
    ρ • vS (t + 1) = (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1) := by
  rw [hS t, hs t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), (16.21)–(16.22), p. 373, as printed (coordinator note E6, confirmed): for
`0 < α < 2`, `ρᵀ E_t v_{t+T} → ((α − γ)/α)(v_t − v*_t)`. -/
theorem literal_limit {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 < α ∧ α < 2)
    {piS π vS v us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hda : 𝔼.Adapted (fun t => v t - vS t))
    (hgap : ∀ t, ρ • (v (t + 1) - vS (t + 1)) =
      (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t)
    (hvS : ∀ t, ρ • vS (t + 1) =
      (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 ((α - γ) / α * (v t ω - vS t ω))) := by
  have hα0 : α ≠ 0 := hα.1.ne'
  have hq : |1 - α| < 1 := (abs_one_sub_lt_one_iff α).mpr hα
  set d : ℕ → Ω → ℝ := fun t => v t - vS t with hd_def
  have hAR : 𝔼.IsAR1 ((1 - 0) / ρ) d :=
    isAR1_of_dyn 𝔼 hρ0.ne' hda (fun t => by rw [sub_zero, one_smul]; exact hgap t)
      (fun t => E_surprise 𝔼 _ t)
  have hdE : ∀ T : ℕ, ρ ^ T * 𝔼.E t (d (t + T)) ω = d t ω := fun T => by
    rw [pow_mul_E_ar1 𝔼 hρ0.ne' hAR t T ω, sub_zero, one_pow, one_mul]
  set y : ℕ → ℝ := fun T => ρ ^ T * 𝔼.E t (vS (t + T)) ω with hy_def
  have hz : Tendsto (fun T => y T + γ / α * d t ω) atTop (𝓝 0) := by
    refine tendsto_zero_of_stable_rec (q := 1 - α) (r := ρ) (C := |M|)
      (w := fun T => -(ρ ^ T * 𝔼.E t (us (t + T + 1)) ω)) hq hρ0.le hρ1 (fun T => ?_)
      (fun T => ?_)
    · rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le T), mul_comm]
      exact mul_le_mul_of_nonneg_right ((𝔼.abs_E_le (hus _) t ω).trans (le_abs_self M))
        (pow_nonneg hρ0.le T)
    · have h := congrFun (congrArg (𝔼.E t) (hvS (t + T))) ω
      rw [map_smul, map_sub, map_sub, map_sub, map_smul, map_smul,
        E_surprise_later 𝔼 piS t T] at h
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero] at h
      have h2 := hdE T
      simp only [hd_def] at h2
      simp only [hy_def]
      rw [show t + (T + 1) = t + T + 1 by omega, pow_succ, mul_assoc, h]
      field_simp
      linear_combination (-(γ * α)) * h2
  have hv : ∀ T : ℕ, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      (y T + γ / α * d t ω) + (α - γ) / α * d t ω := fun T => by
    have h2 := hdE T
    simp only [hd_def, map_sub, Pi.sub_apply] at h2 ⊢
    simp only [hy_def]
    field_simp
    linear_combination α * h2
  simp_rw [hv]
  have := hz.add_const ((α - γ) / α * d t ω)
  rw [zero_add] at this
  exact this

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and (22.1), p. 495, as printed: debt satisfies the
transversality condition iff `γ = α` or debt is on target at every date — fiscal policy is passive
**iff** `γ = α`, not for every `γ > 0` (nor for `0 < γ < 2`, the passive range of the unstarred
rule (23.3)). -/
theorem literal_tvc_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 < α ∧ α < 2)
    {piS π vS v us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hda : 𝔼.Adapted (fun t => v t - vS t))
    (hgap : ∀ t, ρ • (v (t + 1) - vS (t + 1)) =
      (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t)
    (hvS : ∀ t, ρ • vS (t + 1) =
      (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1)) :
    TVC 𝔼 ρ v ↔ γ = α ∨ v = vS := by
  have hlim := literal_limit 𝔼 hρ0 hρ1 hα hus hda hgap hvS
  constructor
  · intro htvc
    by_cases hγ : γ = α
    · exact Or.inl hγ
    · right
      funext t ω
      have h := tendsto_nhds_unique (hlim t ω) (htvc t ω)
      have hc : (α - γ) / α ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hγ)) hα.1.ne'
      have := (mul_eq_zero.mp h).resolve_left hc
      linarith
  · rintro (hγ | hv) t ω
    · have := hlim t ω
      rwa [hγ, sub_self, zero_div, zero_mul] at this
    · subst hv
      have := hlim t ω
      rwa [sub_self, mul_zero] at this

end Cochrane.ObservationalEquivalence.LeeperRegions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Observational equivalence of money-supply regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
simplest monetary-control model of §19.1), and §22.7, p. 508 ("if monetary policy fixes `M` and
fiscal policy fixes surpluses at an inconsistent value, no equilibrium can form").

With money paying interest (or surpluses responding one-for-one to seigniorage) the model is
`M_t V_t = P_t y_t` and `(B_{t−1} + M_{t−1})/P_t = ∑_{j ≥ 0} βʲ s_{t+j}` (perfect foresight). We
write `W_t = B_{t−1} + M_{t−1}` for the nominal liabilities carried into date `t`; velocity `V`
and output `y` are exogenous and positive, surpluses are bounded and `0 ≤ β < 1`, so the present
value is a genuine (absolutely convergent) infinite sum.

## Main results (OE-2)

* `pv_succ`, `flow_of_valuation`: the valuation equation at every date implies the flow
  constraint `W_t = P_t s_t + Q_t W_{t+1}` with bond price `Q_t = β P_t/P_{t+1}`.
* Active money: `activeMoney_price` (the money supply determines the price level) and
  `activeMoney_exists` (for every positive money supply and every nominal debt path with bounded
  real value, passive surpluses complete an equilibrium).
* Active fiscal: `activeFiscal_unique` and `activeFiscal_exists` (surpluses and nominal debt
  determine the price level, `P_t = W_t / PV_t`, and money follows passively).
* `oe2`: an equilibrium path is, at the same time, the unique equilibrium of the active-money
  regime given its `M` and the unique equilibrium of the active-fiscal regime given its `(W, s)` —
  "any time series produced by [one] regime can be produced by [the other] and vice versa".
* `inconsistent_iff`, `halve_money_no_eqm`: with `M`, `s` and `W` all fixed, an equilibrium exists
  iff `W_t y_t/(M_t V_t) = PV_t` at every date; cutting the money supply in half while holding
  surpluses fixed leaves no equilibrium.
-/

namespace Cochrane.ObservationalEquivalence.MoneyRegimes

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (summable_pow_mul_of_bounded
  tendsto_pow_mul_of_bounded)

/-- Cochrane (2023), §22.1, p. 496: the present value of surpluses `∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j, β ^ j * s (t + j)

/-- Cochrane (2023), §22.1, pp. 495–496: an equilibrium of the money model — a positive price
level, the quantity equation `M_t V_t = P_t y_t` and the valuation equation
`W_t / P_t = ∑ βʲ s_{t+j}` at every date. -/
def Eqm (β : ℝ) (V y P M W s : ℕ → ℝ) : Prop :=
  ∀ t, 0 < P t ∧ M t * V t = P t * y t ∧ W t / P t = pv β s t

/-- Cochrane (2023), §22.1, p. 496: bounded surpluses have an absolutely summable present value
for `0 ≤ β < 1`. -/
theorem pv_summable {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ K)
    (t : ℕ) : Summable (fun j => β ^ j * s (t + j)) :=
  summable_pow_mul_of_bounded (by rw [abs_of_nonneg hβ0]; exact hβ1) (x := fun j => s (t + j))
    fun j => hs (t + j)

/-- Cochrane (2023), §22.1, p. 496: `PV_t = s_t + β PV_{t+1}`. -/
theorem pv_succ {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ K)
    (t : ℕ) : pv β s t = s t + β * pv β s (t + 1) := by
  rw [pv, (pv_summable hβ0 hβ1 hs t).tsum_eq_zero_add, pv, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), §22.1, p. 496 (the valuation equation implies the flow constraint): with the
valuation equation at `t` and `t + 1`, `W_t = P_t s_t + Q_t W_{t+1}`, `Q_t = β P_t/P_{t+1}`. -/
theorem flow_of_valuation {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : Eqm β V y P M W s) (t : ℕ) :
    W t = P t * s t + (β * P t / P (t + 1)) * W (t + 1) := by
  obtain ⟨hP, -, hv⟩ := h t
  obtain ⟨hP1, -, hv1⟩ := h (t + 1)
  have e := pv_succ hβ0 hβ1 hs t
  rw [← hv, ← hv1] at e
  field_simp at e ⊢
  linear_combination e

/-! ### Active money -/

/-- Cochrane (2023), §22.1, p. 496 ("in an active-money passive-fiscal regime, the quantity of
money `M` determines the price level `P`"): `P_t = M_t V_t / y_t`. -/
theorem activeMoney_price {V y P M : ℕ → ℝ} (hy : ∀ t, 0 < y t)
    (h : ∀ t, M t * V t = P t * y t) : P = fun t => M t * V t / y t := by
  funext t
  rw [h t, mul_div_cancel_right₀ _ (hy t).ne']

/-- Cochrane (2023), §22.1, p. 496 ("surpluses `s` follow"): for every positive money supply and
every nominal-liability path whose real value `W_t y_t/(M_t V_t)` is bounded, the passive
surpluses `s_t = W_t/P_t − β W_{t+1}/P_{t+1}` complete an equilibrium with `P = MV/y`. -/
theorem activeMoney_exists {β X : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y M W : ℕ → ℝ}
    (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t) (hM : ∀ t, 0 < M t)
    (hX : ∀ t, |W t / (M t * V t / y t)| ≤ X) :
    Eqm β V y (fun t => M t * V t / y t) M W
      (fun t => W t / (M t * V t / y t) -
        β * (W (t + 1) / (M (t + 1) * V (t + 1) / y (t + 1)))) := by
  set x : ℕ → ℝ := fun t => W t / (M t * V t / y t) with hx
  have hsb : ∀ t, |x t - β * x (t + 1)| ≤ X + β * X := fun t => by
    refine (abs_sub _ _).trans (add_le_add (hX t) ?_)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hX (t + 1)) hβ0
  intro t
  refine ⟨div_pos (mul_pos (hM t) (hV t)) (hy t), by field_simp [(hy t).ne'], ?_⟩
  have hpart : ∀ T, ∑ j ∈ Finset.range T, β ^ j * (x (t + j) - β * x (t + j + 1)) =
      x t - β ^ T * x (t + T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, show t + (T + 1) = t + T + 1 by omega]
      ring
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * (x (t + j) - β * x (t + j + 1)))
      atTop (𝓝 (x t)) := by
    simp_rw [hpart]
    have h0 : Tendsto (fun T : ℕ => β ^ T * x (t + T)) atTop (𝓝 0) :=
      tendsto_pow_mul_of_bounded (by rw [abs_of_nonneg hβ0]; exact hβ1)
        (x := fun T => x (t + T)) fun T => hX (t + T)
    simpa using (tendsto_const_nhds (x := x t)).sub h0
  have hsum := pv_summable hβ0 hβ1 (s := fun t => x t - β * x (t + 1)) hsb t
  exact (tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat)

/-! ### Active fiscal -/

/-- Cochrane (2023), §22.1, p. 496 ("in an active-fiscal passive-money regime, fiscal surprises
control unexpected inflation, and then the central bank provides the needed money passively"):
given surpluses and nominal liabilities with `W_t ≠ 0`, the price level `P_t = W_t / PV_t` and
money `M_t = P_t y_t / V_t` are unique. -/
theorem activeFiscal_unique {β : ℝ} {V y P M P' M' W s : ℕ → ℝ} (hV : ∀ t, 0 < V t)
    (hW : ∀ t, W t ≠ 0) (h : Eqm β V y P M W s) (h' : Eqm β V y P' M' W s) :
    P = P' ∧ M = M' := by
  have hP : P = P' := by
    funext t
    obtain ⟨hp, -, hv⟩ := h t
    obtain ⟨hp', -, hv'⟩ := h' t
    have e : W t / P t = W t / P' t := hv.trans hv'.symm
    rw [div_eq_div_iff hp.ne' hp'.ne'] at e
    exact (mul_left_cancel₀ (hW t) e).symm
  refine ⟨hP, funext fun t => ?_⟩
  have e1 := (h t).2.1
  have e2 := (h' t).2.1
  rw [hP] at e1
  exact mul_right_cancel₀ (hV t).ne' (e1.trans e2.symm)

/-- Cochrane (2023), §22.1, p. 496 (active fiscal, existence): if `W_t` and `PV_t` are positive at
every date, `P_t = W_t / PV_t` and `M_t = P_t y_t / V_t` form an equilibrium. -/
theorem activeFiscal_exists {β : ℝ} {V y W s : ℕ → ℝ} (hV : ∀ t, 0 < V t)
    (hW : ∀ t, 0 < W t) (hpv : ∀ t, 0 < pv β s t) :
    Eqm β V y (fun t => W t / pv β s t) (fun t => W t / pv β s t * y t / V t) W s := by
  intro t
  refine ⟨div_pos (hW t) (hpv t), ?_, ?_⟩
  · field_simp [(hV t).ne']
  · field_simp [(hW t).ne', (hpv t).ne']

/-! ### OE-2 -/

/-- Cochrane (2023), §22.1, p. 496 (OE-2: "the equilibrium conditions are the same in each regime.
Any time series produced by an active-money/passive fiscal regime can be produced by an
active-fiscal/passive-money regime and vice versa"): an equilibrium path `(P, M, W, s)` is the
unique price path of the active-money regime given `M`, and the unique `(P, M)` of the
active-fiscal regime given `(W, s)`. -/
theorem oe2 {β : ℝ} {V y P M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hW : ∀ t, W t ≠ 0) (h : Eqm β V y P M W s) :
    (∀ P' : ℕ → ℝ, (∀ t, M t * V t = P' t * y t) → P' = P) ∧
      ∀ P' M' : ℕ → ℝ, Eqm β V y P' M' W s → P' = P ∧ M' = M := by
  refine ⟨fun P' hP' => ?_, fun P' M' h' => ?_⟩
  · rw [activeMoney_price hy hP', activeMoney_price hy (fun t => (h t).2.1)]
  · obtain ⟨e1, e2⟩ := activeFiscal_unique hV hW h h'
    exact ⟨e1.symm, e2.symm⟩

/-! ### Inconsistent money and fiscal policy (§22.7) -/

/-- Cochrane (2023), §22.7, p. 508 ("if monetary policy fixes `M` and fiscal policy fixes surpluses
at an inconsistent value, no equilibrium can form"): with `M`, `s` and `W` all fixed, an
equilibrium exists iff `W_t y_t / (M_t V_t) = PV_t` at every date. -/
theorem inconsistent_iff {β : ℝ} {V y M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hM : ∀ t, 0 < M t) :
    (∃ P, Eqm β V y P M W s) ↔ ∀ t, W t / (M t * V t / y t) = pv β s t := by
  constructor
  · rintro ⟨P, hP⟩ t
    have e := activeMoney_price hy (fun t => (hP t).2.1)
    rw [← (hP t).2.2, e]
  · intro h
    refine ⟨fun t => M t * V t / y t, fun t => ⟨div_pos (mul_pos (hM t) (hV t)) (hy t), ?_,
      h t⟩⟩
    field_simp [(hy t).ne']

/-- Cochrane (2023), §22.7, p. 508 ("suppose that the central bank cuts the money supply in half
and leaves it there … that would double the value of government debt"): if `(M, s, W)` admits an
equilibrium and `W_0 ≠ 0`, then `(M/2, s, W)` — surpluses unchanged — admits none. -/
theorem halve_money_no_eqm {β : ℝ} {V y M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hM : ∀ t, 0 < M t) (hW : W 0 ≠ 0) (h : ∃ P, Eqm β V y P M W s) :
    ¬ ∃ P, Eqm β V y P (fun t => M t / 2) W s := by
  intro h2
  have e1 := (inconsistent_iff hV hy hM).mp h 0
  have e2 := (inconsistent_iff hV hy (fun t => half_pos (hM t))).mp h2 0
  have hm := (hM 0).ne'
  have hv := (hV 0).ne'
  have hyy := (hy 0).ne'
  rw [← e1] at e2
  field_simp at e2
  apply hW
  linarith

end Cochrane.ObservationalEquivalence.MoneyRegimes

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite moving averages, covariances and the Kac–Murdock–Szegő kernel

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501, Chapter 24,
§24.1, p. 519, and Online Appendix Chapter 2 (introduction, p. 593): infrastructure for the
claim that "even with completely exogenous surpluses, we expect a positive regression
coefficient of surpluses on debt" (module `SurplusRegression`).

The book's time-series claims are about linear processes driven by serially uncorrelated
unit-variance shocks, `s_t = a(L)ε_t`. We represent such a process by its coefficient vector.
Covariances are computed with an abstract symmetric bilinear "covariance" form `B` on a real
vector space `V` of random variables, for which the shocks `e : ℤ → V` are orthonormal
(`WhiteNoise B e`). Any `L²` model (random variables on a probability space, `B(x, y) = E[xy]`,
with uncorrelated mean-zero unit-variance shocks) is an instance; `finsuppCov`/`finsuppNoise`
give a concrete instance, so the hypotheses are consistent.

## Main definitions

* `WhiteNoise B e`: `B(e_j, e_k) = 1` if `j = k` and `0` otherwise.
* `maProc a N e t = ∑_{k ≤ N} a_k e_{t−k}`: the finite moving average `a(L)e_t`.
* `autocov a N h = ∑_{k ≤ N} a_{k+h} a_k`: the lag-`h` autocovariance of the coefficients.
* `kmsKernel ρ k l = ρ^{|k−l|}`, `kmsForm ρ n x = ∑_{k,l<n} ρ^{|k−l|} x_k x_l` (the
  Kac–Murdock–Szegő quadratic form), `kmsTail ρ n x m = ∑_{k=m}^{n−1} ρ^{k−m} x_k`.

## Main results

* `cov_maProc`: `B(a(L)e_{t+h}, b(L)e_t) = ∑_k a_{k+h} b_k` — covariance is the inner product of
  the (shifted) coefficient vectors; `var_maProc`, `cov_maProc_stationary`.
* `var_maProc_eq_zero_iff`: a finite MA has zero variance iff all its coefficients vanish.
* `kmsForm_eq_ldl`: the LDL factorisation
  `∑_{k,l<n} ρ^{|k−l|} x_k x_l = y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`, `y_m = ∑_{k ≥ m} ρ^{k−m} x_k`;
  `kmsForm_nonneg` (`ρ² ≤ 1`), `kmsForm_eq_zero_iff`, `kmsForm_pos` (`ρ² < 1`): the kernel
  `ρ^{|k−l|}` is positive semidefinite for `|ρ| ≤ 1` and positive definite for `|ρ| < 1`;
  `kmsMatrix_posDef`: the same as a Mathlib `Matrix.PosDef` statement.
* `kmsTail_succ`: `x_m = y_m − ρ y_{m+1}` (the AR(1) filter inverts the tail sums).
-/

namespace Cochrane.ObservationalEquivalence.MACovariance

open Finset
open scoped Matrix

/-! ### White noise and finite moving averages -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Cochrane (2023), p. 501 and Online Appendix p. 593 (`s_t = a(L)ε_t` with serially
uncorrelated unit-variance shocks): the shocks `e_k` are orthonormal for the covariance form. -/
def WhiteNoise (B : LinearMap.BilinForm ℝ V) (e : ℤ → V) : Prop :=
  ∀ j k, B (e j) (e k) = if j = k then 1 else 0

/-- Cochrane (2023), Online Appendix p. 593: the finite moving average
`a(L)e_t = ∑_{k=0}^{N} a_k e_{t−k}`. -/
def maProc (a : ℕ → ℝ) (N : ℕ) (e : ℤ → V) (t : ℤ) : V :=
  ∑ k ∈ range (N + 1), a k • e (t - k)

/-- Cochrane (2023), Online Appendix p. 593: the lag-`h` autocovariance of a finite moving
average in terms of its coefficients, `∑_{k ≤ N} a_{k+h} a_k`. -/
def autocov (a : ℕ → ℝ) (N h : ℕ) : ℝ := ∑ k ∈ range (N + 1), a (k + h) * a k

/-- Cochrane (2023), p. 501 (covariances of moving averages): with white-noise shocks,
`B(a(L)e_{t+h}, b(L)e_t) = ∑_{k ≤ N} a_{k+h} b_k`, provided `a` vanishes beyond lag `N` — the
covariance is the inner product of the shifted coefficient vectors. -/
theorem cov_maProc {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (b : ℕ → ℝ) (t : ℤ) (h : ℕ) :
    B (maProc a N e (t + h)) (maProc b N e t) = ∑ l ∈ range (N + 1), a (l + h) * b l := by
  simp only [maProc, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hk : ∀ k : ℕ, (t + (h : ℤ) - k = t - l) ↔ k = l + h := by intro k; omega
  have he' : ∀ j k, B (e j) (e k) = if j = k then 1 else 0 := he
  simp only [he', hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hl
  · ring
  · rw [ha (l + h) (by omega)]; ring

/-- Cochrane (2023), p. 501: the variance of a finite moving average is the sum of its squared
coefficients, `B(a(L)e_t, a(L)e_t) = ∑ a_k²`. -/
theorem var_maProc {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) :
    B (maProc a N e t) (maProc a N e t) = ∑ l ∈ range (N + 1), a l ^ 2 := by
  have := cov_maProc he ha a t 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Cochrane (2023), p. 501 (stationarity): the covariance of a finite moving average with its
`h`-lead is `autocov a N h`, independent of the date `t`. -/
theorem cov_maProc_stationary {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) (h : ℕ) :
    B (maProc a N e (t + h)) (maProc a N e t) = autocov a N h :=
  cov_maProc he ha a t h

/-- Cochrane (2023), p. 501: a finite moving average has zero variance iff all its coefficients
`a_0, …, a_N` vanish. -/
theorem var_maProc_eq_zero_iff {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) :
    B (maProc a N e t) (maProc a N e t) = 0 ↔ ∀ k ≤ N, a k = 0 := by
  rw [var_maProc he ha, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_range, pow_eq_zero_iff two_ne_zero]
  exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩

/-! ### A concrete white-noise model -/

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the coordinate inner product
`B(x, y) = ∑_k x_k y_k` on finitely supported sequences `ℤ →₀ ℝ`. -/
noncomputable def finsuppCov : LinearMap.BilinForm ℝ (ℤ →₀ ℝ) :=
  Finsupp.lsum ℝ fun k => LinearMap.smulRight LinearMap.id (Finsupp.lapply k)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the unit vectors of `ℤ →₀ ℝ`. -/
noncomputable def finsuppNoise (k : ℤ) : ℤ →₀ ℝ := Finsupp.single k 1

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the unit vectors are white noise for
the coordinate inner product, so `WhiteNoise` is satisfiable. -/
theorem finsuppNoise_whiteNoise : WhiteNoise finsuppCov finsuppNoise := by
  intro j k
  simp only [finsuppCov, finsuppNoise, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

/-! ### The Kac–Murdock–Szegő kernel -/

/-- Cochrane (2023), p. 501 (Theorem RG of the survey): the kernel `ρ^{|k−l|}` (with `|k − l|`
written `(k − l) + (l − k)` in truncated natural subtraction). -/
def kmsKernel (ρ : ℝ) (k l : ℕ) : ℝ := ρ ^ (k - l + (l - k))

/-- Cochrane (2023), p. 501: the Kac–Murdock–Szegő quadratic form
`∑_{k,l<n} ρ^{|k−l|} x_k x_l`. -/
def kmsForm (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range n, ∑ l ∈ range n, kmsKernel ρ k l * x k * x l

/-- Cochrane (2023), p. 501: the tail sums `y_m = ∑_{k=m}^{n−1} ρ^{k−m} x_k`. -/
def kmsTail (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (n - m), ρ ^ k * x (m + k)

/-- Cochrane (2023), p. 501: the LDL form `y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`. -/
def kmsLDL (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range n, (if m = 0 then 1 else 1 - ρ ^ 2) * kmsTail ρ n x m ^ 2

/-- Cochrane (2023), p. 501: the kernel is symmetric. -/
theorem kmsKernel_symm (ρ : ℝ) (k l : ℕ) : kmsKernel ρ k l = kmsKernel ρ l k := by
  unfold kmsKernel; rw [add_comm]

/-- Cochrane (2023), p. 501: the kernel is shift invariant. -/
theorem kmsKernel_succ (ρ : ℝ) (k l : ℕ) : kmsKernel ρ (k + 1) (l + 1) = kmsKernel ρ k l := by
  unfold kmsKernel
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]

/-- Cochrane (2023), p. 501: the tail sum peels off its first term,
`y_0 = x_0 + ρ y_0(x_{·+1})`. -/
theorem kmsTail_zero_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsTail ρ (n + 1) x 0 = x 0 + ρ * kmsTail ρ n (fun k => x (k + 1)) 0 := by
  simp only [kmsTail, Nat.sub_zero, zero_add]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501: tail sums of the shifted vector,
`y_{m+1}(x) = y_m(x_{·+1})`. -/
theorem kmsTail_shift (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) (m : ℕ) :
    kmsTail ρ (n + 1) x (m + 1) = kmsTail ρ n (fun k => x (k + 1)) m := by
  simp only [kmsTail, Nat.add_sub_add_right]
  exact Finset.sum_congr rfl fun k _ => by rw [show m + 1 + k = m + k + 1 by omega]

/-- Cochrane (2023), p. 501: the AR(1) filter inverts the tail sums,
`x_m = y_m − ρ y_{m+1}` for `m < n`. -/
theorem kmsTail_succ (ρ : ℝ) {n m : ℕ} (hm : m < n) (x : ℕ → ℝ) :
    kmsTail ρ n x m = x m + ρ * kmsTail ρ n x (m + 1) := by
  simp only [kmsTail]
  obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
  rw [hr, show n - (m + 1) = r by omega, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, add_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [show m + (k + 1) = m + 1 + k by omega, pow_succ]; ring

/-- Cochrane (2023), p. 501: tail sums vanish from `n` on. -/
theorem kmsTail_of_le (ρ : ℝ) {n m : ℕ} (hm : n ≤ m) (x : ℕ → ℝ) : kmsTail ρ n x m = 0 := by
  simp [kmsTail, Nat.sub_eq_zero_of_le hm]

/-- Cochrane (2023), p. 501: the recursive structure of the quadratic form,
`Q_{n+1}(x) = x_0² + 2ρx_0 y_0(x_{·+1}) + Q_n(x_{·+1})`. -/
theorem kmsForm_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsForm ρ (n + 1) x = x 0 ^ 2 + 2 * ρ * x 0 * kmsTail ρ n (fun k => x (k + 1)) 0 +
      kmsForm ρ n (fun k => x (k + 1)) := by
  simp only [kmsForm, kmsTail, Nat.sub_zero, zero_add]
  rw [Finset.sum_range_succ']
  simp only [Finset.sum_range_succ', kmsKernel_succ]
  have h0 : ∀ l : ℕ, kmsKernel ρ 0 (l + 1) = ρ ^ (l + 1) := by
    intro l; simp [kmsKernel]
  have h0' : ∀ k : ℕ, kmsKernel ρ (k + 1) 0 = ρ ^ (k + 1) := by
    intro k; simp [kmsKernel]
  have hk00 : kmsKernel ρ 0 0 = 1 := by simp [kmsKernel]
  simp only [h0, h0', hk00, Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∑ i ∈ range n, ρ ^ (i + 1) * x 0 * x (i + 1) =
      ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  have e2 : ∑ i ∈ range n, ρ ^ (i + 1) * x (i + 1) * x 0 =
      ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  rw [e1, e2]
  have e3 : ∑ i ∈ range n, 2 * ρ * x 0 * (ρ ^ i * x (i + 1)) =
      2 * ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  ring

/-- Cochrane (2023), p. 501: the recursive structure of the LDL form,
`L_{n+1}(x) = x_0² + 2ρx_0 y_0(x_{·+1}) + L_n(x_{·+1})`. -/
theorem kmsLDL_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsLDL ρ (n + 1) x = x 0 ^ 2 + 2 * ρ * x 0 * kmsTail ρ n (fun k => x (k + 1)) 0 +
      kmsLDL ρ n (fun k => x (k + 1)) := by
  set y := fun m => kmsTail ρ n (fun k => x (k + 1)) m with hy
  have hsplit : kmsLDL ρ (n + 1) x =
      ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 + kmsTail ρ (n + 1) x 0 ^ 2 := by
    simp only [kmsLDL]
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, ↓reduceIte, one_mul, kmsTail_shift, hy]
  have hdiff : ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 =
      kmsLDL ρ n (fun k => x (k + 1)) - ρ ^ 2 * y 0 ^ 2 := by
    have h1 : kmsLDL ρ n (fun k => x (k + 1)) - ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 =
        ∑ m ∈ range n, (if m = 0 then ρ ^ 2 else 0) * y m ^ 2 := by
      simp only [kmsLDL, ← Finset.sum_sub_distrib, hy]
      exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
    have h2 : ∑ m ∈ range n, (if m = 0 then ρ ^ 2 else 0) * y m ^ 2 = ρ ^ 2 * y 0 ^ 2 := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs with hn
      · rfl
      · have : y 0 = 0 := kmsTail_of_le ρ (by omega) _
        rw [this]; ring
    linarith
  rw [hsplit, hdiff, kmsTail_zero_succ]
  ring

/-- Cochrane (2023), p. 501 (survey Theorem RG, positive-definiteness of the Kac–Murdock–Szegő
kernel): the LDL factorisation
`∑_{k,l<n} ρ^{|k−l|} x_k x_l = y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`. -/
theorem kmsForm_eq_ldl (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : kmsForm ρ n x = kmsLDL ρ n x := by
  induction n generalizing x with
  | zero => simp [kmsForm, kmsLDL]
  | succ n ih => rw [kmsForm_succ, kmsLDL_succ, ih]

/-- Cochrane (2023), p. 501: for `ρ² ≤ 1` the Kac–Murdock–Szegő form is positive
semidefinite. -/
theorem kmsForm_nonneg {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (n : ℕ) (x : ℕ → ℝ) : 0 ≤ kmsForm ρ n x := by
  rw [kmsForm_eq_ldl]
  refine Finset.sum_nonneg fun m _ => mul_nonneg ?_ (sq_nonneg _)
  split_ifs <;> linarith

/-- Cochrane (2023), p. 501: for `ρ² < 1` the Kac–Murdock–Szegő form vanishes only at `x = 0`
(on the first `n` coordinates). -/
theorem kmsForm_eq_zero_iff {ρ : ℝ} (hρ : ρ ^ 2 < 1) (n : ℕ) (x : ℕ → ℝ) :
    kmsForm ρ n x = 0 ↔ ∀ k < n, x k = 0 := by
  constructor
  · intro h
    rw [kmsForm_eq_ldl, kmsLDL] at h
    have hcoef : ∀ m, 0 < (if m = 0 then (1 : ℝ) else 1 - ρ ^ 2) := by
      intro m; split_ifs <;> linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun m _ => mul_nonneg (hcoef m).le (sq_nonneg (kmsTail ρ n x m)))).mp h
    have hy : ∀ m, kmsTail ρ n x m = 0 := by
      intro m
      by_cases hm : m < n
      · have := hall m (Finset.mem_range.mpr hm)
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (hcoef m).ne'
        · exact pow_eq_zero_iff two_ne_zero |>.mp h1
      · exact kmsTail_of_le ρ (by omega) x
    intro k hk
    have := kmsTail_succ ρ hk x
    rw [hy k, hy (k + 1)] at this
    linarith
  · intro h
    unfold kmsForm
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l _ => ?_
    rw [h k (Finset.mem_range.mp hk)]; ring

/-- Cochrane (2023), p. 501: for `ρ² < 1` the Kac–Murdock–Szegő form is positive definite. -/
theorem kmsForm_pos {ρ : ℝ} (hρ : ρ ^ 2 < 1) {n : ℕ} {x : ℕ → ℝ} (hx : ∃ k < n, x k ≠ 0) :
    0 < kmsForm ρ n x := by
  rcases (kmsForm_nonneg hρ.le n x).lt_or_eq with h | h
  · exact h
  · obtain ⟨k, hk, hxk⟩ := hx
    exact absurd ((kmsForm_eq_zero_iff hρ n x).mp h.symm k hk) hxk

/-- Cochrane (2023), p. 501: the Kac–Murdock–Szegő matrix `(ρ^{|k−l|})_{k,l<n}`. -/
def kmsMatrix (ρ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k l => kmsKernel ρ k l

/-- Cochrane (2023), p. 501: the quadratic form of the matrix is the Kac–Murdock–Szegő form of
the extended vector. -/
theorem kmsMatrix_quad (ρ : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    star x ⬝ᵥ (kmsMatrix ρ n *ᵥ x) =
      kmsForm ρ n (fun k => if h : k < n then x ⟨k, h⟩ else 0) := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, kmsMatrix, Matrix.of_apply, kmsForm]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range n,
    kmsKernel ρ k l * (if h : k < n then x ⟨k, h⟩ else 0) *
      (if h : l < n then x ⟨l, h⟩ else 0))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => kmsKernel ρ k l *
    (if h : k < n then x ⟨k, h⟩ else 0) * (if h : l < n then x ⟨l, h⟩ else 0)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
  ring

/-- Cochrane (2023), p. 501 (survey Theorem RG): for `|ρ| < 1` the Kac–Murdock–Szegő matrix
`(ρ^{|k−l|})` is positive definite. -/
theorem kmsMatrix_posDef {ρ : ℝ} (hρ : |ρ| < 1) (n : ℕ) : (kmsMatrix ρ n).PosDef := by
  have hρ2 : ρ ^ 2 < 1 := by
    have h0 := abs_nonneg ρ
    rw [← sq_abs]; nlinarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext k l
    simp [kmsMatrix, Matrix.conjTranspose_apply, kmsKernel_symm]
  · rw [kmsMatrix_quad]
    refine kmsForm_pos hρ2 ?_
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    exact ⟨i, i.isLt, by simpa using hi⟩

end Cochrane.ObservationalEquivalence.MACovariance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Surpluses on debt: a positive regression coefficient with exogenous surpluses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 ("We may easily
see a coefficient `γ > 0` from a fiscal-theory equilibrium"), Chapter 24, §24.1, p. 519 ("a
surplus moving average with `a(ρ) < 1` generates a regression coefficient `γ > 0`"), and Online
Appendix Chapter 2, introduction, p. 593 ("Even with completely exogenous surpluses, we expect a
positive regression coefficient of surpluses on debt").

## Setting

An active-fiscal equilibrium with a constant discount rate and an exogenous surplus: the surplus
is a finite moving average `s_t = a(L)ε_t = ∑_{k ≤ N} a_k ε_{t−k}` of white-noise shocks that are
a martingale difference sequence for the agents' information (`ShockInfo`), and the value of debt
is given by the valuation equation `v_t = E_t ∑_{j≥0} ρ^j s_{t+1+j}` (a genuine `tsum`, with
`|ρ| < 1` and bounded shocks). Covariances are taken with a covariance form `B` for which the
shocks are white noise. The population OLS coefficient of `s_{t+1}` on `v_t` is
`γ̂ = Cov(s_{t+1}, v_t)/Var(v_t)`.

## Main results

* `value_eq_maProc`: `v_t = b(L)ε_t` with `b_m = ∑_j ρ^j a_{m+1+j}`.
* `cov_surplus_value`: `Cov(s_{t+1}, v_t) = ∑_k a_{k+1} b_k`.
* `two_cov_eq_kms` (**Theorem RG** of the survey):
  `2 Cov(s_{t+1}, v_t) = ∑_{k≥1} a_k² + ∑_{k,l≥1} ρ^{|k−l|} a_k a_l`.
* `cov_pos_iff`, `regCoeff_pos_iff`: for `ρ² ≤ 1`, the covariance and the regression coefficient
  are strictly positive iff the surplus is not white noise (`a_k ≠ 0` for some `k ≥ 1`);
  `iid_cov_zero`: white-noise surpluses give `v ≡ 0`.
* `book_claim_aRho_lt_one`: the book's statement (`a(ρ) < 1` with `a_0 = 1` ⇒ `γ̂ > 0`) is true;
  `ma1_aRho_gt_one`, `ma1_regCoeff_pos`: but the hypothesis `a(ρ) < 1` is superfluous — e.g. the
  MA(1) `a = (1, 1)` has `a(ρ) = 1 + ρ > 1` and `γ̂ > 0` (survey **E16**).
* Infinite moving averages with `∑|a_k| < ∞` (`x_k = a_{k+1}`, `b_m = ∑_j ρ^j x_{m+j}`, all sums
  genuine with proved summability: `bInf_bound`, `covInf_summable`, `kmsInf_summable`,
  `sq_summable`, `bInf_sq_summable`): `two_covInf_eq`
  `2 ∑_m x_m b_m = ∑ x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l` (finite identity `two_finite_eq` passed to
  the limit by dominated convergence); the infinite Kac–Murdock–Szegő form is positive
  semidefinite (`kmsInf_nonneg`), bounded below by `(1−ρ²)/(1+|ρ|)² ∑ x_k²` (`kmsInf_lower`,
  from `kmsForm_lower`) and positive definite for `|ρ| < 1` (`kmsInf_pos`); `covInf_pos_iff`,
  `regInf_pos_iff`: covariance and regression coefficient are positive iff the surplus is not
  white noise; `cov_trunc_tendsto`: the genuine covariances of the lag-`N` truncations converge
  to `∑_m a_{m+1} b_m`; `ar1_covInf`: the AR(1) case `η²σ²/(1 − ρη)`, `σ² = 1/(1 − η²)`, as a
  corollary.
* `truncSystem`, `clampShock`, `truncCov`, `truncModel_regCoeff_pos`: a model (states = shock
  paths, `E_t` = set future shocks to zero) in which all the hypotheses hold with nonzero
  shocks, so the theorem is not vacuous.
* AR(1) surpluses (an infinite moving average, any `ExpectationSystem`): `ar1_value`
  `v_t = η s_t/(1 − ρη)`, `ar1_cov` `Cov(s_{t+1}, v_t) = η²σ²/(1 − ρη)`, `ar1_regCoeff`
  `γ̂ = 1 − ρη > 0` for every `η ≠ 0` with `|ρη| < 1` — including `η > 0`, where
  `a(ρ) = 1/(1 − ρη) > 1` (`ar1_aRho_gt_one`).
-/

namespace Cochrane.ObservationalEquivalence.SurplusRegression

open Finset Filter Topology Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.ExpectationTools (pvExPost)

variable {Ω : Type*}

/-! ### Exogenous moving-average surpluses and the value of debt -/

/-- Cochrane (2023), Online Appendix p. 602 (agents' information): the shocks are a martingale
difference sequence — `E_t ε_k = ε_k` for `k ≤ t` and `E_t ε_k = 0` for `k > t`. -/
def ShockInfo (𝔼 : ExpectationSystem Ω) (ε : ℤ → Ω → ℝ) : Prop :=
  ∀ (t : ℕ) (k : ℤ), 𝔼.E t (ε k) = if k ≤ (t : ℤ) then ε k else 0

/-- Cochrane (2023), p. 501 and Online Appendix p. 593: the exogenous surplus
`s_t = a(L)ε_t`, at the model dates `t ∈ ℕ`. -/
def surplus (a : ℕ → ℝ) (N : ℕ) (ε : ℤ → Ω → ℝ) (t : ℕ) : Ω → ℝ := maProc a N ε (t : ℤ)

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: the value of debt from the valuation
equation with a constant discount factor, `v_t = E_t ∑_{j≥0} ρ^j s_{t+1+j}` (the expectation of
the shared ex-post present value `pvExPost`). -/
noncomputable def valueOfDebt (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  𝔼.E t (pvExPost ρ s t)

/-- Cochrane (2023), p. 501: the moving-average coefficients of the value of debt,
`b_m = ∑_{j ≥ 0} ρ^j a_{m+1+j}`. -/
def vCoeff (ρ : ℝ) (a : ℕ → ℝ) (N m : ℕ) : ℝ := ∑ j ∈ range (N + 1), ρ ^ j * a (m + 1 + j)

/-- Cochrane (2023), p. 501: the population regression coefficient of `s_{t+1}` on `v_t`,
`Cov(s_{t+1}, v_t)/Var(v_t)`. -/
noncomputable def regCoeff (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (s v : Ω → ℝ) : ℝ :=
  B s v / B v v

/-- Cochrane (2023), Online Appendix p. 593: the surplus is white noise ("iid") when
`a_k = 0` for every `k ≥ 1`. -/
def IsIID (a : ℕ → ℝ) : Prop := ∀ k, 1 ≤ k → a k = 0

/-- Cochrane (2023), p. 519: `a(ρ) = ∑_{k ≤ N} ρ^k a_k`. -/
def aRho (a : ℕ → ℝ) (N : ℕ) (ρ : ℝ) : ℝ := ∑ k ∈ range (N + 1), ρ ^ k * a k

variable {𝔼 : ExpectationSystem Ω}

/-- Cochrane (2023), Online Appendix p. 602: conditional expectations of a moving average keep
the realised shocks and drop the future ones. -/
theorem E_maProc {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) (a : ℕ → ℝ) (N : ℕ) (τ : ℤ) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (maProc a N ε τ) ω =
      ∑ k ∈ range (N + 1), a k * (if τ - k ≤ (t : ℤ) then ε (τ - k) ω else 0) := by
  have hε' : ∀ k, 𝔼.E t (ε k) = if k ≤ (t : ℤ) then ε k else 0 := hε t
  simp only [maProc, map_sum, map_smul, hε', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- Cochrane (2023), p. 501: a bounded-shock moving average is bounded by `∑|a_k| M`. -/
theorem abs_maProc_le {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (a : ℕ → ℝ) (N : ℕ)
    (τ : ℤ) (ω : Ω) : |maProc a N ε τ ω| ≤ (∑ k ∈ range (N + 1), |a k|) * M := by
  simp only [maProc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)

/-- Cochrane (2023), p. 501 (index bookkeeping): the expected `(t+1+j)`-surplus is the moving
average `∑_m a_{m+1+j} ε_{t−m}` of the realised shocks. -/
theorem shifted_sum {ε : ℤ → Ω → ℝ} {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0)
    (t j : ℕ) (ω : Ω) :
    ∑ k ∈ range (N + 1), a k *
        (if ((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ) then ε (((t + 1 + j : ℕ) : ℤ) - k) ω else 0) =
      ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω := by
  set g : ℕ → ℝ := fun k => a k *
    (if ((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ) then ε (((t + 1 + j : ℕ) : ℤ) - k) ω else 0) with hg
  have h1 : ∑ k ∈ range (N + 1), g k = ∑ k ∈ range ((j + 1) + (N + 1)), g k := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k hk hk' => ?_
    have : N < k := by
      simp only [Finset.mem_range] at hk hk'; omega
    simp [hg, ha k this]
  rw [h1, Finset.sum_range_add]
  have h2 : ∑ k ∈ range (j + 1), g k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < j + 1 := Finset.mem_range.mp hk
    have hc : ¬ (((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ)) := by push_cast; omega
    simp only [hg]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), mul_zero]
  rw [h2, zero_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : ((t + 1 + j : ℕ) : ℤ) - ((j + 1 + m : ℕ) : ℤ) ≤ (t : ℤ) := by push_cast; omega
  have he : ((t + 1 + j : ℕ) : ℤ) - ((j + 1 + m : ℕ) : ℤ) = (t : ℤ) - m := by push_cast; ring
  simp only [hg]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), he, show j + 1 + m = m + 1 + j by omega]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: with an exogenous moving-average surplus,
the value of debt from the valuation equation is itself a moving average of the same shocks,
`v_t = b(L)ε_t`, `b_m = ∑_j ρ^j a_{m+1+j}` (the infinite sum is genuine; `|ρ| < 1`, bounded
shocks). -/
theorem value_eq_maProc {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus a N ε) t = maProc (vCoeff ρ a N) N ε (t : ℤ) := by
  funext ω
  set C : ℝ := (∑ k ∈ range (N + 1), |a k|) * M with hC
  have hbd : ∀ j ω', |ρ ^ j * surplus a N ε (t + 1 + j) ω'| ≤ |ρ| ^ j * C := by
    intro j ω'
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (abs_maProc_le hM a N _ ω') (pow_nonneg (abs_nonneg _) _)
  have hE := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω')
    hbd t ω
  unfold valueOfDebt pvExPost
  rw [hE]
  have hterm : ∀ j, 𝔼.E t (fun ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω') ω =
      ρ ^ j * ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω := by
    intro j
    have hf : (fun ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω') =
        ρ ^ j • surplus a N ε (t + 1 + j) := rfl
    rw [hf, map_smul, Pi.smul_apply, smul_eq_mul, surplus, E_maProc hε, shifted_sum ha]
  simp only [hterm]
  have hvanish : ∀ j ∉ range (N + 1),
      ρ ^ j * ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω = 0 := by
    intro j hj
    have hj' : N + 1 ≤ j := by simpa using hj
    rw [Finset.sum_eq_zero fun m _ => by rw [ha (m + 1 + j) (by omega), zero_mul], mul_zero]
  rw [tsum_eq_sum hvanish]
  simp only [maProc, vCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The covariance of surpluses with lagged debt -/

/-- Cochrane (2023), p. 501: the value-of-debt coefficients vanish beyond lag `N − 1`. -/
theorem vCoeff_of_le (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) {m : ℕ}
    (hm : N ≤ m) : vCoeff ρ a N m = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [ha (m + 1 + j) (by omega), mul_zero]

/-- Cochrane (2023), p. 501: the value-of-debt coefficients are the Kac–Murdock–Szegő tail sums
of the lagged surplus coefficients, `b_m = y_m(a_{·+1})`. -/
theorem vCoeff_eq_kmsTail (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (m : ℕ) :
    vCoeff ρ a N m = kmsTail ρ N (fun k => a (k + 1)) m := by
  unfold vCoeff kmsTail
  dsimp only
  symm
  refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hj' => ?_).trans
    (Finset.sum_congr rfl fun j _ => by rw [show m + j + 1 = m + 1 + j by omega])
  have : N < m + j + 1 := by simp only [Finset.mem_range] at hj hj'; omega
  rw [ha _ this, mul_zero]

/-- Cochrane (2023), p. 501: `Cov(s_{t+1}, v_t) = ∑_k a_{k+1} b_k` (stationary: independent of
`t`). -/
theorem cov_surplus_value {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k := by
  rw [value_eq_maProc hε hM hρ ha, surplus]
  have := cov_maProc hw ha (vCoeff ρ a N) (t : ℤ) 1
  simpa using this

/-- Cochrane (2023), p. 501: `Var(v_t) = ∑_k b_k²`. -/
theorem var_value {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    B (valueOfDebt 𝔼 ρ (surplus a N ε) t) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range (N + 1), vCoeff ρ a N k ^ 2 := by
  rw [value_eq_maProc hε hM hρ ha]
  exact var_maProc hw (fun k hk => vCoeff_of_le ρ ha hk.le) _

/-- Cochrane (2023), p. 501 (algebra of Theorem RG): with `b_m = y_m(a_{·+1})`,
`2 ∑_k a_{k+1} b_k = ∑_{k<N} a_{k+1}² + L_N(a_{·+1})`, the LDL form of the Kac–Murdock–Szegő
kernel. -/
theorem two_sum_eq_ldl (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) :
    2 * ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k =
      ∑ k ∈ range N, a (k + 1) ^ 2 + kmsLDL ρ N (fun k => a (k + 1)) := by
  set x : ℕ → ℝ := fun k => a (k + 1) with hx
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hb : ∀ m, vCoeff ρ a N m = y m := fun m => vCoeff_eq_kmsTail ρ ha m
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hxy : ∀ m ∈ range N, x m = y m - ρ * y (m + 1) := by
    intro m hm
    have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
    simp only [hy]; linarith
  have hcov : ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k = ∑ k ∈ range N, x k * y k := by
    rw [Finset.sum_range_succ, hb N, hyN, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [hb k]
  have hsq : ∑ k ∈ range N, a (k + 1) ^ 2 = ∑ k ∈ range N, (y k - ρ * y (k + 1)) ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [← hxy k hk]
  have hcross : ∑ k ∈ range N, x k * y k = ∑ k ∈ range N, (y k - ρ * y (k + 1)) * y k :=
    Finset.sum_congr rfl fun k hk => by rw [hxy k hk]
  have hshift : ∑ k ∈ range N, y (k + 1) ^ 2 =
      ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    have h1 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ k ∈ range N, y (k + 1) ^ 2 := by
      rw [Finset.sum_range_succ']; simp
    have h2 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
      rw [Finset.sum_range_succ, hyN]; ring
    rw [← h1, h2]
  have hldl : kmsLDL ρ N x = ∑ m ∈ range N, y m ^ 2 -
      ρ ^ 2 * ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    simp only [kmsLDL, Finset.mul_sum, ← Finset.sum_sub_distrib, hy]
    exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
  rw [hcov, hcross, hsq, hldl, ← hshift]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 and Online Appendix p. 593 (survey **Theorem RG**):
with an exogenous moving-average surplus and the valuation equation,
`2 Cov(s_{t+1}, v_t) = ∑_{k≥1} a_k² + ∑_{k,l≥1} ρ^{|k−l|} a_k a_l`. -/
theorem two_cov_eq_kms {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    2 * B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range N, a (k + 1) ^ 2 + kmsForm ρ N (fun k => a (k + 1)) := by
  rw [cov_surplus_value hw hε hM hρ ha, two_sum_eq_ldl ρ ha, kmsForm_eq_ldl]

/-- Cochrane (2023), p. 501: `∑_{k<N} a_{k+1}² > 0` iff the surplus is not white noise. -/
theorem sum_sq_pos_iff {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) :
    0 < ∑ k ∈ range N, a (k + 1) ^ 2 ↔ ¬ IsIID a := by
  constructor
  · intro h hiid
    rw [Finset.sum_eq_zero fun k _ => by rw [hiid (k + 1) (by omega)]; ring] at h
    exact lt_irrefl 0 h
  · intro h
    unfold IsIID at h
    push Not at h
    obtain ⟨k, hk1, hk⟩ := h
    have hkN : k ≤ N := by
      by_contra hcon; exact hk (ha k (by omega))
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨j, Finset.mem_range.mpr (by omega), by positivity⟩

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (survey Theorem RG, sign):
for `|ρ| < 1` the covariance of surpluses with lagged debt is strictly positive iff the
exogenous surplus is not white noise. -/
theorem cov_pos_iff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    0 < B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) ↔ ¬ IsIID a := by
  have h2 := two_cov_eq_kms hw hε hM hρ ha t
  have hρ2 : ρ ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  have hk := kmsForm_nonneg hρ2 N (fun k => a (k + 1))
  constructor
  · intro hpos hiid
    have hz : ∑ k ∈ range N, a (k + 1) ^ 2 = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hiid (k + 1) (by omega)]; ring
    have hkz : kmsForm ρ N (fun k => a (k + 1)) = 0 := by
      unfold kmsForm
      exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => by
        change kmsKernel ρ k l * a (k + 1) * a (l + 1) = 0
        rw [hiid (k + 1) (by omega)]; ring
    linarith
  · intro h
    have := (sum_sq_pos_iff ha).mpr h
    linarith

/-- Cochrane (2023), Online Appendix p. 593: with a white-noise surplus the value of debt is
identically zero (nothing is forecastable), so the covariance vanishes. -/
theorem iid_value_zero {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hiid : IsIID a) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus a N ε) t = 0 := by
  rw [value_eq_maProc hε hM hρ ha]
  have hb : ∀ m, vCoeff ρ a N m = 0 := fun m =>
    Finset.sum_eq_zero fun j _ => by rw [hiid (m + 1 + j) (by omega), mul_zero]
  simp [maProc, hb]

/-- Cochrane (2023), Online Appendix p. 593: with a white-noise surplus the covariance of
surpluses with lagged debt is zero. -/
theorem iid_cov_zero {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (hiid : IsIID a) (t : ℕ) :
    B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) = 0 := by
  rw [iid_value_zero hε hM hρ ha hiid, map_zero]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (survey Theorem RG): the
population regression coefficient `γ̂` of `s_{t+1}` on `v_t` is strictly positive iff the
exogenous surplus is not white noise — "even with completely exogenous surpluses, we expect a
positive regression coefficient of surpluses on debt". -/
theorem regCoeff_pos_iff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    0 < regCoeff B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) ↔
      ¬ IsIID a := by
  rw [← cov_pos_iff hw hε hM hρ ha t]
  unfold regCoeff
  constructor
  · intro h
    rcases lt_or_ge 0 (B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t))
      with hc | hc
    · exact hc
    · have hv : 0 ≤ B (valueOfDebt 𝔼 ρ (surplus a N ε) t)
          (valueOfDebt 𝔼 ρ (surplus a N ε) t) := by
        rw [var_value hw hε hM hρ ha]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      have := div_nonpos_of_nonpos_of_nonneg hc hv
      linarith
  · intro hc
    refine div_pos hc ?_
    rw [var_value hw hε hM hρ ha]
    rcases (Finset.sum_nonneg fun k (_ : k ∈ range (N + 1)) =>
      sq_nonneg (vCoeff ρ a N k)).lt_or_eq with hv | hv
    · exact hv
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (vCoeff ρ a N k)).mp
        hv.symm
      rw [cov_surplus_value hw hε hM hρ ha,
        Finset.sum_eq_zero fun k hk => by rw [pow_eq_zero_iff two_ne_zero |>.mp (hz k hk),
          mul_zero]] at hc
      exact lt_irrefl 0 hc

/-! ### The book's sufficient condition `a(ρ) < 1` and survey E16 -/

/-- Cochrane (2023), §24.1, p. 519 ("a surplus moving average with `a(ρ) < 1` generates a
regression coefficient `γ > 0`"), normalising `a_0 = 1`: true, because `a(ρ) < 1 = a_0` forces the
surplus not to be white noise. -/
theorem book_claim_aRho_lt_one {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (ha0 : a 0 = 1)
    (haρ : aRho a N ρ < 1) (t : ℕ) :
    0 < regCoeff B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) := by
  rw [regCoeff_pos_iff hw hε hM hρ ha]
  intro hiid
  have : aRho a N ρ = 1 := by
    unfold aRho
    rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => by
      rw [hiid (k + 1) (by omega), mul_zero]]
    simp [ha0]
  linarith

/-- Cochrane (2023), §24.1, p. 519 (survey E16): the MA(1) surplus `s_t = ε_t + ε_{t−1}`. -/
def ma1Coeff (k : ℕ) : ℝ := if k ≤ 1 then 1 else 0

/-- Cochrane (2023), §24.1, p. 519 (survey E16): the MA(1) `a = (1, 1)` has `a(ρ) = 1 + ρ > 1`
for `ρ > 0`. -/
theorem ma1_aRho_gt_one {ρ : ℝ} (hρ : 0 < ρ) : 1 < aRho ma1Coeff 1 ρ := by
  simp [aRho, ma1Coeff, Finset.sum_range_succ]
  linarith

/-- Cochrane (2023), §24.1, p. 519 (survey E16): nevertheless the MA(1) `a = (1, 1)` produces a
strictly positive regression coefficient of surpluses on debt, so the book's hypothesis
`a(ρ) < 1` is superfluous: every non-white-noise exogenous surplus does (`regCoeff_pos_iff`). -/
theorem ma1_regCoeff_pos {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) (t : ℕ) :
    0 < regCoeff B (surplus ma1Coeff 1 ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus ma1Coeff 1 ε) t) := by
  rw [regCoeff_pos_iff hw hε hM hρ (fun k hk => by simp [ma1Coeff]; omega)]
  intro hiid
  have := hiid 1 le_rfl
  simp [ma1Coeff] at this

/-! ### AR(1) surpluses -/

/-- Cochrane (2023), Online Appendix p. 604: with an AR(1) surplus `E_t s_{t+1} = ηs_t`
(any `ExpectationSystem`, bounded `s`, `|ρ| < 1`, `|ρη| < 1`), the valuation equation gives
`v_t = E_t ∑ ρ^j s_{t+1+j} = η s_t/(1 − ρη)`. -/
theorem ar1_value {η ρ M : ℝ} {s : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M)
    (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ) :
    valueOfDebt 𝔼 ρ s t = (η / (1 - ρ * η)) • s t := by
  funext ω
  have hbd : ∀ j ω', |ρ ^ j * s (t + 1 + j) ω'| ≤ |ρ| ^ j * M := by
    intro j ω'
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _ ω') (pow_nonneg (abs_nonneg _) _)
  have hE := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω' => ρ ^ j * s (t + 1 + j) ω') hbd t ω
  unfold valueOfDebt pvExPost
  rw [hE]
  have hterm : ∀ j, 𝔼.E t (fun ω' => ρ ^ j * s (t + 1 + j) ω') ω =
      η * s t ω * (ρ * η) ^ j := by
    intro j
    have hf : (fun ω' => ρ ^ j * s (t + 1 + j) ω') = ρ ^ j • s (t + (j + 1)) := by
      funext ω'; simp only [Pi.smul_apply, smul_eq_mul]; rw [show t + 1 + j = t + (j + 1) by omega]
    rw [hf, map_smul, 𝔼.ar1_iterate hs, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_pow, pow_succ]
    ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), p. 501 and Online Appendix p. 604: with an AR(1) surplus whose innovation
`s_{t+1} − ηs_t` is uncorrelated with `s_t` and with `Var(s_t) = σ²`,
`Cov(s_{t+1}, v_t) = η²σ²/(1 − ρη)`. -/
theorem ar1_cov {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {η ρ M σ2 : ℝ} {s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M) (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ)
    (hinn : B (s (t + 1) - η • s t) (s t) = 0) (hvar : B (s t) (s t) = σ2) :
    B (s (t + 1)) (valueOfDebt 𝔼 ρ s t) = η ^ 2 * σ2 / (1 - ρ * η) := by
  rw [ar1_value hs hM hρ hρη, map_smul, smul_eq_mul]
  have h1 : B (s (t + 1)) (s t) = η * σ2 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvar] at hinn
    linarith
  rw [h1]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 and Online Appendix p. 604: with an AR(1) surplus the
regression coefficient of `s_{t+1}` on `v_t` is exactly `γ̂ = 1 − ρη`, strictly positive whenever
`|ρη| < 1` (and `η ≠ 0`, `σ² > 0`, so that the regression is defined). -/
theorem ar1_regCoeff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {η ρ M σ2 : ℝ} {s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M) (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ)
    (hinn : B (s (t + 1) - η • s t) (s t) = 0) (hvar : B (s t) (s t) = σ2) (hη : η ≠ 0)
    (hσ : 0 < σ2) :
    regCoeff B (s (t + 1)) (valueOfDebt 𝔼 ρ s t) = 1 - ρ * η ∧ 0 < 1 - ρ * η := by
  have hpos : 0 < 1 - ρ * η := by have := (abs_lt.mp hρη).2; linarith
  refine ⟨?_, hpos⟩
  unfold regCoeff
  rw [ar1_cov hs hM hρ hρη t hinn hvar, ar1_value hs hM hρ hρη]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hvar]
  field_simp

/-- Cochrane (2023), §24.1, p. 519 and Online Appendix p. 604 (survey E16): the AR(1) has
`a(ρ) = ∑ ρ^j η^j = 1/(1 − ρη)`, which exceeds one when `0 < ρη < 1`; yet `γ̂ = 1 − ρη > 0`
(`ar1_regCoeff`). -/
theorem ar1_aRho_gt_one {η ρ : ℝ} (h0 : 0 < ρ * η) (h1 : ρ * η < 1) :
    HasSum (fun j : ℕ => ρ ^ j * η ^ j) (1 / (1 - ρ * η)) ∧ 1 < 1 / (1 - ρ * η) := by
  refine ⟨?_, ?_⟩
  · have := hasSum_geometric_of_lt_one h0.le h1
    rw [one_div]
    simpa [mul_pow] using this
  · rw [lt_div_iff₀ (by linarith)]; linarith

/-! ### Infinite moving averages with absolutely summable coefficients -/

/-- Cochrane (2023), p. 501 (infinite moving averages): the truncation `x_k 1{k < N}`. -/
def truncSeq (x : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ := if k < N then x k else 0

/-- Cochrane (2023), p. 501: the value-of-debt coefficients of an infinite moving average, with
`x_k = a_{k+1}`: `b_m = ∑_{j ≥ 0} ρ^j x_{m+j} = ∑_j ρ^j a_{m+1+j}`. -/
noncomputable def bInf (ρ : ℝ) (x : ℕ → ℝ) (m : ℕ) : ℝ := ∑' j, ρ ^ j * x (m + j)

/-- Cochrane (2023), p. 501: the covariance of surpluses with lagged debt in coefficient form,
`Cov(s_{t+1}, v_t) = ∑_m a_{m+1} b_m` (here `x_m = a_{m+1}`). -/
noncomputable def covInf (ρ : ℝ) (x : ℕ → ℝ) : ℝ := ∑' m, x m * bInf ρ x m

/-- Cochrane (2023), p. 501: the infinite Kac–Murdock–Szegő form
`∑_k ∑_l ρ^{|k−l|} x_k x_l` (an iterated genuine sum). -/
noncomputable def kmsInf (ρ : ℝ) (x : ℕ → ℝ) : ℝ := ∑' k, ∑' l, kmsKernel ρ k l * x k * x l

/-- Cochrane (2023), p. 501: `|ρ^{|k−l|}| ≤ 1` for `|ρ| ≤ 1`. -/
theorem abs_kmsKernel_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (k l : ℕ) : |kmsKernel ρ k l| ≤ 1 := by
  unfold kmsKernel; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hρ

/-- Cochrane (2023), p. 501 (tool): a series dominated by a summable sequence is summable and
`|∑ f| ≤ ∑ g`. -/
theorem abs_tsum_le_of_le {f g : ℕ → ℝ} (hg : Summable g) (h : ∀ k, |f k| ≤ g k) :
    Summable f ∧ |∑' k, f k| ≤ ∑' k, g k := by
  have hfa : Summable fun k => |f k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) h hg
  refine ⟨hfa.of_abs, ?_⟩
  have hn := norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hfa)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (Summable.tsum_le_tsum h hfa hg)

/-- Cochrane (2023), p. 501 (tool): tails of an absolutely summable sequence are absolutely
summable and bounded by the full sum. -/
theorem tail_abs {x : ℕ → ℝ} (hx : Summable fun k => |x k|) (m : ℕ) :
    Summable (fun j => |x (m + j)|) ∧ ∑' j, |x (m + j)| ≤ ∑' k, |x k| := by
  have hs : Summable (fun j => |x (j + m)|) := (summable_nat_add_iff m).mpr hx
  have e : (fun j => |x (m + j)|) = fun j => |x (j + m)| := by
    funext j; rw [add_comm]
  rw [e]
  refine ⟨hs, ?_⟩
  rw [← hx.sum_add_tsum_nat_add m]
  have : 0 ≤ ∑ i ∈ range m, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- Cochrane (2023), p. 501 (tool): `|x_k| ≤ ∑ |x|`. -/
theorem abs_le_tsum_abs {x : ℕ → ℝ} (hx : Summable fun k => |x k|) (k : ℕ) :
    |x k| ≤ ∑' k, |x k| :=
  hx.le_tsum k fun _ _ => abs_nonneg _

/-- Cochrane (2023), p. 501 (tool): truncation is dominated, `|x_k 1{k<N}| ≤ |x_k|`. -/
theorem abs_truncSeq_le (x : ℕ → ℝ) (N k : ℕ) : |truncSeq x N k| ≤ |x k| := by
  unfold truncSeq; split_ifs <;> simp

/-- Cochrane (2023), p. 501 (tool): truncations converge pointwise. -/
theorem tendsto_truncSeq (x : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N => truncSeq x N k) atTop (𝓝 (x k)) :=
  tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨k + 1, fun N hN => by
    simp [truncSeq, show k < N by omega]⟩)

/-- Cochrane (2023), p. 501: for any `y` dominated by an absolutely summable `x` and
`|ρ| ≤ 1`, `b_m(y)` is a genuine sum and `|b_m(y)| ≤ ∑_j |x_{m+j}| ≤ ∑ |x|`. -/
theorem bInf_bound {ρ : ℝ} (hρ : |ρ| ≤ 1) {x y : ℕ → ℝ} (hx : Summable fun k => |x k|)
    (hy : ∀ k, |y k| ≤ |x k|) (m : ℕ) :
    Summable (fun j => ρ ^ j * y (m + j)) ∧ |bInf ρ y m| ≤ ∑' k, |x k| := by
  obtain ⟨hs, hle⟩ := tail_abs hx m
  have hb : ∀ j, |ρ ^ j * y (m + j)| ≤ |x (m + j)| := by
    intro j
    rw [abs_mul, abs_pow]
    calc |ρ| ^ j * |y (m + j)| ≤ 1 * |x (m + j)| :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ) (hy _) (abs_nonneg _) zero_le_one
      _ = |x (m + j)| := one_mul _
  obtain ⟨h1, h2⟩ := abs_tsum_le_of_le hs hb
  exact ⟨h1, h2.trans hle⟩

/-- Cochrane (2023), p. 501: the terms of `covInf` are absolutely summable (a genuine sum). -/
theorem covInf_summable {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => x m * bInf ρ x m) := by
  refine (abs_tsum_le_of_le (hx.mul_right (∑' k, |x k|)) fun m => ?_).1
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (bInf_bound hρ hx (fun _ => le_rfl) m).2 (abs_nonneg _)

/-- Cochrane (2023), p. 501: the inner and outer sums of `kmsInf` are absolutely summable. -/
theorem kmsInf_summable {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    (∀ k, Summable (fun l => kmsKernel ρ k l * x k * x l)) ∧
      Summable (fun k => ∑' l, kmsKernel ρ k l * x k * x l) := by
  have hin : ∀ k l, |kmsKernel ρ k l * x k * x l| ≤ |x k| * |x l| := by
    intro k l
    rw [abs_mul, abs_mul]
    have := abs_kmsKernel_le hρ k l
    have h1 : |kmsKernel ρ k l| * |x k| ≤ 1 * |x k| :=
      mul_le_mul_of_nonneg_right this (abs_nonneg _)
    nlinarith [abs_nonneg (x l), abs_nonneg (x k)]
  refine ⟨fun k => (abs_tsum_le_of_le (hx.mul_left |x k|) (hin k)).1, ?_⟩
  refine (abs_tsum_le_of_le (hx.mul_right (∑' k, |x k|)) fun k => ?_).1
  have := (abs_tsum_le_of_le (hx.mul_left |x k|) (hin k)).2
  rwa [tsum_mul_left] at this

/-- Cochrane (2023), p. 501: `∑ x_k²` is a genuine sum for absolutely summable `x`. -/
theorem sq_summable {x : ℕ → ℝ} (hx : Summable fun k => |x k|) : Summable (fun k => x k ^ 2) :=
  (abs_tsum_le_of_le (hx.mul_left (∑' k, |x k|)) fun k => by
    rw [abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (abs_le_tsum_abs hx k) (abs_nonneg _)).1

/-! #### Truncations: the finite identities -/

/-- Cochrane (2023), p. 501: for the truncation, `b_m = y_m`, the Kac–Murdock–Szegő tail sum. -/
theorem bInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N m : ℕ) :
    bInf ρ (truncSeq x N) m = kmsTail ρ N x m := by
  unfold bInf kmsTail
  rw [tsum_eq_sum (s := range (N - m)) fun j hj => by
    have : ¬ m + j < N := by simp only [Finset.mem_range] at hj; omega
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun j hj => ?_
  have : m + j < N := by simp only [Finset.mem_range] at hj; omega
  simp [truncSeq, this]

/-- Cochrane (2023), p. 501: `covInf` of the truncation is the finite covariance
`∑_{k<N} x_k y_k`. -/
theorem covInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    covInf ρ (truncSeq x N) = ∑ k ∈ range N, x k * kmsTail ρ N x k := by
  unfold covInf
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [bInf_trunc]
  simp [truncSeq, Finset.mem_range.mp hk]

/-- Cochrane (2023), p. 501: `∑ x_k²` of the truncation. -/
theorem sq_trunc (x : ℕ → ℝ) (N : ℕ) :
    ∑' k, truncSeq x N k ^ 2 = ∑ k ∈ range N, x k ^ 2 := by
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  exact Finset.sum_congr rfl fun k hk => by simp [truncSeq, Finset.mem_range.mp hk]

/-- Cochrane (2023), p. 501: `kmsInf` of the truncation is the finite form `kmsForm`. -/
theorem kmsInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    kmsInf ρ (truncSeq x N) = kmsForm ρ N x := by
  unfold kmsInf kmsForm
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [tsum_eq_sum (s := range N) fun l hl => by
    have : ¬ l < N := by simpa using hl
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp [truncSeq, Finset.mem_range.mp hk, Finset.mem_range.mp hl]

/-- Cochrane (2023), p. 501 (Theorem RG, finite form):
`2 ∑_{k<N} x_k y_k = ∑_{k<N} x_k² + ∑_{k,l<N} ρ^{|k−l|} x_k x_l`, `y_k = ∑_{j} ρ^j x_{k+j}`. -/
theorem two_finite_eq (ρ : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    2 * ∑ k ∈ range N, x k * kmsTail ρ N x k =
      ∑ k ∈ range N, x k ^ 2 + kmsForm ρ N x := by
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hxy : ∀ m ∈ range N, x m = y m - ρ * y (m + 1) := by
    intro m hm
    have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
    simp only [hy]; linarith
  have hsq : ∑ k ∈ range N, x k ^ 2 = ∑ k ∈ range N, (y k - ρ * y (k + 1)) ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [← hxy k hk]
  have hcross : ∑ k ∈ range N, x k * kmsTail ρ N x k =
      ∑ k ∈ range N, (y k - ρ * y (k + 1)) * y k :=
    Finset.sum_congr rfl fun k hk => by rw [hxy k hk]
  have hshift : ∑ k ∈ range N, y (k + 1) ^ 2 =
      ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    have h1 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ k ∈ range N, y (k + 1) ^ 2 := by
      rw [Finset.sum_range_succ']; simp
    have h2 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
      rw [Finset.sum_range_succ, hyN]; ring
    rw [← h1, h2]
  have hldl : kmsLDL ρ N x = ∑ m ∈ range N, y m ^ 2 -
      ρ ^ 2 * ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    simp only [kmsLDL, Finset.mul_sum, ← Finset.sum_sub_distrib, hy]
    exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
  rw [kmsForm_eq_ldl, hcross, hsq, hldl, ← hshift]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501 (a uniform lower bound for the Kac–Murdock–Szegő form, the finite
version of the spectral bound `(1−ρ²)/|1−ρe^{iω}|² ≥ (1−|ρ|)/(1+|ρ|)`):
`(1 − ρ²) ∑_{k<N} x_k² ≤ (1 + |ρ|)² ∑_{k,l<N} ρ^{|k−l|} x_k x_l` for `ρ² ≤ 1`. -/
theorem kmsForm_lower {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (N : ℕ) (x : ℕ → ℝ) :
    (1 - ρ ^ 2) * ∑ k ∈ range N, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * kmsForm ρ N x := by
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hr0 := abs_nonneg ρ
  have hr2 : |ρ| ^ 2 = ρ ^ 2 := sq_abs ρ
  have hpt : ∀ m ∈ range N, x m ^ 2 ≤ (1 + |ρ|) * (y m ^ 2 + |ρ| * y (m + 1) ^ 2) := by
    intro m hm
    have hx : x m = y m - ρ * y (m + 1) := by
      have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
      simp only [hy]; linarith
    rw [hx]
    have hab : -(ρ * (y m * y (m + 1))) ≤ |ρ| * |y m| * |y (m + 1)| := by
      rw [mul_assoc, ← abs_mul, ← abs_mul]
      exact neg_le_abs _
    have hsq1 : y m ^ 2 = |y m| ^ 2 := (sq_abs _).symm
    have hsq2 : y (m + 1) ^ 2 = |y (m + 1)| ^ 2 := (sq_abs _).symm
    nlinarith [sq_nonneg (|y m| - |y (m + 1)|), mul_nonneg hr0 (sq_nonneg (|y m| - |y (m + 1)|))]
  have hshift : ∑ m ∈ range N, y (m + 1) ^ 2 ≤ ∑ m ∈ range N, y m ^ 2 := by
    have h1 := Finset.sum_range_succ' (fun m => y m ^ 2) N
    have h2 := Finset.sum_range_succ (fun m => y m ^ 2) N
    rw [hyN] at h2
    nlinarith [sq_nonneg (y 0)]
  have hsum : ∑ k ∈ range N, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2 := by
    calc ∑ k ∈ range N, x k ^ 2
        ≤ ∑ m ∈ range N, (1 + |ρ|) * (y m ^ 2 + |ρ| * y (m + 1) ^ 2) :=
          Finset.sum_le_sum hpt
      _ = (1 + |ρ|) * (∑ m ∈ range N, y m ^ 2 + |ρ| * ∑ m ∈ range N, y (m + 1) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (1 + |ρ|) * (∑ m ∈ range N, y m ^ 2 + |ρ| * ∑ m ∈ range N, y m ^ 2) := by
          gcongr
      _ = (1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2 := by ring
  have hL : (1 - ρ ^ 2) * ∑ m ∈ range N, y m ^ 2 ≤ kmsForm ρ N x := by
    rw [kmsForm_eq_ldl, kmsLDL, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    split_ifs
    · nlinarith [sq_nonneg (y m)]
    · exact le_of_eq (by simp only [hy])
  have h1r : 0 ≤ 1 - ρ ^ 2 := by linarith
  calc (1 - ρ ^ 2) * ∑ k ∈ range N, x k ^ 2
      ≤ (1 - ρ ^ 2) * ((1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2) :=
        mul_le_mul_of_nonneg_left hsum h1r
    _ = (1 + |ρ|) ^ 2 * ((1 - ρ ^ 2) * ∑ m ∈ range N, y m ^ 2) := by ring
    _ ≤ (1 + |ρ|) ^ 2 * kmsForm ρ N x := mul_le_mul_of_nonneg_left hL (by positivity)

/-! #### Passing to the limit -/

/-- Cochrane (2023), p. 501: the truncated covariances converge, `covInf(x 1{·<N}) → covInf x`
(dominated convergence). -/
theorem tendsto_covInf_trunc {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ}
    (hx : Summable fun k => |x k|) :
    Tendsto (fun N => covInf ρ (truncSeq x N)) atTop (𝓝 (covInf ρ x)) := by
  set S := ∑' k, |x k|
  unfold covInf
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => |x m| * S)
    (hx.mul_right S) (fun m => ?_) (Eventually.of_forall fun N m => ?_)
  · refine (tendsto_truncSeq x m).mul ?_
    unfold bInf
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => |x (m + j)|)
      (tail_abs hx m).1 (fun j => (tendsto_truncSeq x (m + j)).const_mul _)
      (Eventually.of_forall fun N j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |ρ| ^ j * |truncSeq x N (m + j)| ≤ 1 * |x (m + j)| :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ) (abs_truncSeq_le _ _ _) (abs_nonneg _)
            zero_le_one
      _ = |x (m + j)| := one_mul _
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_truncSeq_le _ _ _) (bInf_bound hρ hx (abs_truncSeq_le x N) m).2
      (abs_nonneg _) (abs_nonneg _)

/-- Cochrane (2023), p. 501: `∑ (x_k 1{k<N})² → ∑ x_k²`. -/
theorem tendsto_sq_trunc {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Tendsto (fun N => ∑' k, truncSeq x N k ^ 2) atTop (𝓝 (∑' k, x k ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => (∑' k, |x k|) * |x k|)
    (hx.mul_left _) (fun k => (tendsto_truncSeq x k).pow 2) (Eventually.of_forall fun N k => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq]
  exact mul_le_mul ((abs_truncSeq_le _ _ _).trans (abs_le_tsum_abs hx k)) (abs_truncSeq_le _ _ _)
    (abs_nonneg _) (by positivity)

/-- Cochrane (2023), p. 501: `kmsInf(x 1{·<N}) → kmsInf x`. -/
theorem tendsto_kmsInf_trunc {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ}
    (hx : Summable fun k => |x k|) :
    Tendsto (fun N => kmsInf ρ (truncSeq x N)) atTop (𝓝 (kmsInf ρ x)) := by
  set S := ∑' k, |x k|
  have hin : ∀ N k l, |kmsKernel ρ k l * truncSeq x N k * truncSeq x N l| ≤ |x k| * |x l| := by
    intro N k l
    rw [abs_mul, abs_mul]
    have h1 := abs_kmsKernel_le hρ k l
    have h2 := abs_truncSeq_le x N k
    have h3 := abs_truncSeq_le x N l
    have := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    calc |kmsKernel ρ k l| * |truncSeq x N k| * |truncSeq x N l| ≤ 1 * |x k| * |x l| :=
          mul_le_mul this h3 (abs_nonneg _) (by positivity)
      _ = |x k| * |x l| := by ring
  unfold kmsInf
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => |x k| * S)
    (hx.mul_right S) (fun k => ?_) (Eventually.of_forall fun N k => ?_)
  · refine tendsto_tsum_of_dominated_convergence (bound := fun l => |x k| * |x l|)
      (hx.mul_left _) (fun l => ?_) (Eventually.of_forall fun N l => ?_)
    · exact ((tendsto_truncSeq x k).const_mul _).mul (tendsto_truncSeq x l)
    · rw [Real.norm_eq_abs]; exact hin N k l
  · rw [Real.norm_eq_abs]
    have := (abs_tsum_le_of_le (hx.mul_left |x k|) (hin N k)).2
    rwa [tsum_mul_left] at this

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG for infinite
moving averages**): for absolutely summable `x` (`x_k = a_{k+1}`) and `|ρ| ≤ 1`, with every sum a
genuine (absolutely convergent) sum,
`2 ∑_m x_m b_m = ∑_k x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l`, `b_m = ∑_j ρ^j x_{m+j}`. -/
theorem two_covInf_eq {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    2 * covInf ρ x = ∑' k, x k ^ 2 + kmsInf ρ x := by
  have h1 := (tendsto_covInf_trunc hρ hx).const_mul 2
  have h2 := (tendsto_sq_trunc hx).add (tendsto_kmsInf_trunc hρ hx)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  rw [sq_trunc, kmsInf_trunc, covInf_trunc, two_finite_eq]

/-- Cochrane (2023), p. 501: the infinite Kac–Murdock–Szegő form is positive semidefinite on
absolutely summable sequences for `|ρ| ≤ 1`. -/
theorem kmsInf_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    0 ≤ kmsInf ρ x := by
  have hρ2 : ρ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  refine ge_of_tendsto' (tendsto_kmsInf_trunc hρ hx) fun N => ?_
  rw [kmsInf_trunc]; exact kmsForm_nonneg hρ2 N x

/-- Cochrane (2023), p. 501: the infinite form is bounded below,
`(1 − ρ²) ∑ x_k² ≤ (1 + |ρ|)² ∑_k ∑_l ρ^{|k−l|} x_k x_l`. -/
theorem kmsInf_lower {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    (1 - ρ ^ 2) * ∑' k, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * kmsInf ρ x := by
  have hρ2 : ρ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  refine le_of_tendsto_of_tendsto' ((tendsto_sq_trunc hx).const_mul _)
    ((tendsto_kmsInf_trunc hρ hx).const_mul _) fun N => ?_
  rw [sq_trunc, kmsInf_trunc]
  exact kmsForm_lower hρ2 N x

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the infinite Kac–Murdock–Szegő form is positive
definite on absolutely summable sequences. -/
theorem kmsInf_pos {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|)
    (hne : ∃ k, x k ≠ 0) : 0 < kmsInf ρ x := by
  obtain ⟨k, hk⟩ := hne
  have hsq : 0 < ∑' k, x k ^ 2 :=
    (sq_summable hx).tsum_pos (fun _ => sq_nonneg _) k (by positivity)
  have hρ2 : 0 < 1 - ρ ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  have := kmsInf_lower hρ.le hx
  have h1 : 0 < (1 - ρ ^ 2) * ∑' k, x k ^ 2 := mul_pos hρ2 hsq
  have h2 : 0 < (1 + |ρ|) ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG, infinite
moving averages**): for an absolutely summable surplus moving average `a` and `|ρ| ≤ 1`, the
covariance of surpluses with lagged debt, `∑_m a_{m+1} b_m`, is strictly positive iff the
surplus is not white noise. -/
theorem covInf_pos_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    0 < covInf ρ (fun k => a (k + 1)) ↔ ¬ IsIID a := by
  have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
  have h2 := two_covInf_eq hρ hx
  have hk := kmsInf_nonneg hρ hx
  constructor
  · intro hpos hiid
    have hz : covInf ρ (fun k => a (k + 1)) = 0 := by
      unfold covInf
      exact (tsum_congr fun m => by beta_reduce; rw [hiid (m + 1) (by omega), zero_mul]).trans
        tsum_zero
    linarith
  · intro h
    unfold IsIID at h
    push Not at h
    obtain ⟨k, hk1, hk0⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hsq : 0 < ∑' i, a (i + 1) ^ 2 :=
      (sq_summable hx).tsum_pos (fun _ => sq_nonneg _) j (by positivity)
    linarith

/-! #### The value of debt and the regression coefficient -/

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the value-of-debt coefficients `b` of an absolutely
summable moving average are themselves absolutely summable, so `Var(v) = ∑ b_m²` is a genuine
sum. -/
theorem bInf_abs_summable {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => |bInf ρ x m|) := by
  set g : ℕ × ℕ → ℝ := fun p => |ρ| ^ p.2 * |x (p.1 + p.2)| with hg
  have hg0 : 0 ≤ g := fun p => by positivity
  have hswap : Summable (fun p : ℕ × ℕ => g p.swap) := by
    refine (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => g p.swap)
      (fun p => hg0 p.swap)).mpr ⟨fun j => ?_, ?_⟩
    · simp only [hg, Prod.swap_prod_mk]
      have := (summable_nat_add_iff j).mpr hx
      exact this.mul_left _
    · refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => hg0 _) (fun j => ?_)
        ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (∑' k, |x k|))
      simp only [hg, Prod.swap_prod_mk]
      rw [tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h := tail_abs hx j
      simpa only [add_comm] using h.2
  have hgs : Summable g := by
    have := hswap.comp_injective Prod.swap_injective
    simpa [Function.comp_def] using this
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hgs.prod
  have hb : ∀ j, |ρ ^ j * x (m + j)| ≤ g (m, j) := by
    intro j; simp only [hg, abs_mul, abs_pow, le_refl]
  exact (abs_tsum_le_of_le (hgs.prod_factor m) hb).2

/-- Cochrane (2023), p. 501: the variance of the value of debt, `∑ b_m²`, is a genuine sum. -/
theorem bInf_sq_summable {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => bInf ρ x m ^ 2) :=
  (abs_tsum_le_of_le ((bInf_abs_summable hρ hx).mul_left (∑' k, |x k|)) fun m => by
    rw [abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (bInf_bound hρ.le hx (fun _ => le_rfl) m).2
      (abs_nonneg _)).1

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, regression form, infinite moving
averages): for `|ρ| < 1` the population regression coefficient
`γ̂ = ∑_m a_{m+1} b_m / ∑_m b_m²` of surpluses on lagged debt is strictly positive iff the
surplus is not white noise. -/
theorem regInf_pos_iff {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    0 < covInf ρ (fun k => a (k + 1)) / ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 ↔
      ¬ IsIID a := by
  rw [← covInf_pos_iff hρ.le ha]
  have hv0 : 0 ≤ ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := div_nonpos_of_nonpos_of_nonneg hc hv0
    linarith
  · intro hc
    refine div_pos hc (lt_of_le_of_ne hv0 fun h0 => ?_)
    have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
    have hz : ∀ m, bInf ρ (fun k => a (k + 1)) m = 0 := by
      intro m
      by_contra hm
      have := (bInf_sq_summable hρ hx).tsum_pos (fun _ => sq_nonneg _) m (by positivity)
      linarith
    have hcz : covInf ρ (fun k => a (k + 1)) = 0 := by
      unfold covInf
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rw [hz m, mul_zero]
    linarith

/-! #### Link with the covariances of the stochastic model -/

/-- Cochrane (2023), p. 501: the truncated surplus `a 1{k ≤ N}` (an `N`-lag moving average). -/
theorem truncSeq_support (a : ℕ → ℝ) (N : ℕ) : ∀ k, N < k → truncSeq a (N + 1) k = 0 := by
  intro k hk; simp [truncSeq, show ¬ k < N + 1 by omega]

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, infinite moving averages, stochastic
form): the genuine covariances `Cov(s^N_{t+1}, v^N_t)` of the surplus truncated at lag `N` and
the value of debt it implies (finite moving averages of the white-noise shocks, valuation
equation as a genuine `E_t ∑`) converge to `∑_m a_{m+1} b_m` as `N → ∞`. -/
theorem cov_trunc_tendsto {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) (t : ℕ) :
    Tendsto (fun N => B (surplus (truncSeq a (N + 1)) N ε (t + 1))
      (valueOfDebt 𝔼 ρ (surplus (truncSeq a (N + 1)) N ε) t)) atTop
      (𝓝 (covInf ρ (fun k => a (k + 1)))) := by
  have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
  refine (tendsto_covInf_trunc hρ.le hx).congr fun N => ?_
  rw [cov_surplus_value hw hε hM hρ (truncSeq_support a N), covInf_trunc,
    Finset.sum_range_succ]
  have hN : truncSeq a (N + 1) (N + 1) = 0 := truncSeq_support a N (N + 1) (by omega)
  rw [hN, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := Finset.mem_range.mp hk
  rw [vCoeff_eq_kmsTail ρ (truncSeq_support a N)]
  have e1 : truncSeq a (N + 1) (k + 1) = a (k + 1) := by simp [truncSeq, hk']
  rw [e1]
  congr 1
  unfold kmsTail
  refine Finset.sum_congr rfl fun j hj => ?_
  have : k + j + 1 < N + 1 := by simp only [Finset.mem_range] at hj; omega
  simp [truncSeq, this]

/-! #### AR(1) as a corollary -/

/-- Cochrane (2023), Online Appendix p. 604 (AR(1) surplus `a_k = η^k`, `|η| < 1`, `|ρ| < 1`):
`b_m = η^{m+1}/(1 − ρη)`. -/
theorem ar1_bInf {η ρ : ℝ} (hρη : |ρ * η| < 1) (m : ℕ) :
    bInf ρ (fun k => η ^ (k + 1)) m = η ^ (m + 1) / (1 - ρ * η) := by
  unfold bInf
  have e : ∀ j, ρ ^ j * η ^ (m + j + 1) = η ^ (m + 1) * (ρ * η) ^ j := by
    intro j; rw [mul_pow, pow_add, pow_add]; ring
  simp only [e]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, div_eq_mul_inv]

/-- Cochrane (2023), p. 501 and Online Appendix p. 604 (AR(1) as a corollary of the
infinite-MA Theorem RG): with `a_k = η^k`, `Cov(s_{t+1}, v_t) = η² σ²/(1 − ρη)` where
`σ² = ∑ η^{2k} = 1/(1 − η²)` is the variance of the surplus (agreeing with `ar1_cov`), and this
is strictly positive iff `η ≠ 0`. -/
theorem ar1_covInf {η ρ : ℝ} (hη : |η| < 1) (hρ : |ρ| < 1) :
    covInf ρ (fun k => η ^ (k + 1)) = η ^ 2 * (∑' k : ℕ, (η ^ k) ^ 2) / (1 - ρ * η) ∧
      ∑' k : ℕ, (η ^ k) ^ 2 = 1 / (1 - η ^ 2) ∧
      (0 < covInf ρ (fun k => η ^ (k + 1)) ↔ η ≠ 0) := by
  have hρη : |ρ * η| < 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg ρ, abs_nonneg η]
  have hη2 : |η ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg η]
  have hgeo : ∑' k : ℕ, (η ^ k) ^ 2 = 1 / (1 - η ^ 2) := by
    have e : (fun k : ℕ => (η ^ k) ^ 2) = fun k => (η ^ 2) ^ k :=
      funext fun k => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, tsum_geometric_of_abs_lt_one hη2, one_div]
  refine ⟨?_, hgeo, ?_⟩
  · unfold covInf
    simp only [ar1_bInf hρη]
    have e : ∀ m : ℕ, η ^ (m + 1) * (η ^ (m + 1) / (1 - ρ * η)) =
        η ^ 2 / (1 - ρ * η) * (η ^ m) ^ 2 := by
      intro m; rw [pow_succ]; ring
    simp only [e]
    rw [tsum_mul_left]
    ring
  · have ha : Summable fun k => |η ^ k| := by
      simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg η) hη
    rw [covInf_pos_iff hρ.le ha]
    constructor
    · intro h hη0
      exact h fun k hk => by rw [hη0, zero_pow (by omega)]
    · intro h hiid
      have := hiid 1 le_rfl
      simp only [pow_one] at this
      exact h this

/-! ### A model satisfying all the hypotheses -/

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): states are realisations
`ω : ℤ → ℝ` of the shock sequence, and `truncPath t ω` sets the shocks after date `t` to their
mean, zero. -/
def truncPath (t : ℕ) (ω : ℤ → ℝ) : ℤ → ℝ := fun k => if k ≤ (t : ℤ) then ω k else 0

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): truncating at `s ≤ t` after
truncating at `t`. -/
theorem truncPath_trunc_le {s t : ℕ} (hst : s ≤ t) (ω : ℤ → ℝ) :
    truncPath s (truncPath t ω) = truncPath s ω := by
  funext k
  simp only [truncPath]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): truncating at `t ≥ s` after
truncating at `s`. -/
theorem truncPath_le_trunc {s t : ℕ} (hst : s ≤ t) (ω : ℤ → ℝ) :
    truncPath t (truncPath s ω) = truncPath s ω := by
  funext k
  simp only [truncPath]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the expectation system
`E_t x(ω) = x(truncPath t ω)` — the conditional expectation of the linear (certainty-equivalent)
model, future mean-zero shocks replaced by zero. -/
def truncSystem : ExpectationSystem (ℤ → ℝ) where
  E t := LinearMap.funLeft ℝ ℝ (truncPath t)
  const _ _ := rfl
  mono _ _ _ h _ := h _
  tower {s t} hst x := by
    funext ω
    simp only [LinearMap.funLeft_apply, truncPath_le_trunc hst]
  known {s t} hst x := by
    funext ω
    simp only [LinearMap.funLeft_apply, truncPath_trunc_le hst]

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the bounded shocks
`ε_k(ω) = max(−1, min(1, ω_k))`. -/
def clampShock (k : ℤ) (ω : ℤ → ℝ) : ℝ := max (-1) (min 1 (ω k))

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are bounded by one. -/
theorem clampShock_bounded (k : ℤ) (ω : ℤ → ℝ) : |clampShock k ω| ≤ 1 := by
  unfold clampShock
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks satisfy `ShockInfo` in
the truncation system. -/
theorem clampShock_info : ShockInfo truncSystem clampShock := by
  intro t k
  funext ω
  simp only [truncSystem, LinearMap.funLeft_apply, clampShock, truncPath]
  split_ifs with h
  · rfl
  · simp

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are linearly
independent random variables. -/
theorem clampShock_linearIndependent : LinearIndependent ℝ clampShock := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg (Pi.single i 1)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [clampShock, hji])
    (fun h' => absurd hi h')] at h
  simpa [clampShock] using h

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): a linear map sending each shock
`ε_k` to the unit vector `e_k` (the shocks' coordinates, extended to all random variables). -/
noncomputable def shockCoord : ((ℤ → ℝ) → ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) :=
  Classical.choose (LinearMap.exists_extend clampShock_linearIndependent.repr)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): `shockCoord ε_k = e_k`. -/
theorem shockCoord_shock (k : ℤ) : shockCoord (clampShock k) = Finsupp.single k 1 := by
  have hspec := Classical.choose_spec (LinearMap.exists_extend
    clampShock_linearIndependent.repr)
  have hk : clampShock k ∈ Submodule.span ℝ (Set.range clampShock) :=
    Submodule.subset_span ⟨k, rfl⟩
  have := congrArg (fun f => f ⟨clampShock k, hk⟩) hspec
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [shockCoord, this, clampShock_linearIndependent.repr_eq_single k _ rfl]

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the covariance form
`B(x, y) = ⟨shockCoord x, shockCoord y⟩`. -/
noncomputable def truncCov : LinearMap.BilinForm ℝ ((ℤ → ℝ) → ℝ) :=
  finsuppCov.compl₁₂ shockCoord shockCoord

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are white noise for
`truncCov`. -/
theorem clampShock_whiteNoise : WhiteNoise truncCov clampShock := by
  intro j k
  simp only [truncCov, LinearMap.compl₁₂_apply, shockCoord_shock]
  exact finsuppNoise_whiteNoise j k

/-- Cochrane (2023), p. 501, §24.1 p. 519 (survey Theorem RG is not vacuous): in the truncation
model, with bounded white-noise shocks, the MA(1) surplus `s_t = ε_t + ε_{t−1}` has a strictly
positive regression coefficient on debt. -/
theorem truncModel_regCoeff_pos {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    0 < regCoeff truncCov (surplus ma1Coeff 1 clampShock (t + 1))
      (valueOfDebt truncSystem ρ (surplus ma1Coeff 1 clampShock) t) :=
  ma1_regCoeff_pos clampShock_whiteNoise clampShock_info clampShock_bounded hρ t

end Cochrane.ObservationalEquivalence.SurplusRegression

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Granger causality, news, and information sets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 (footnote 1)
and pp. 501–502, and Online Appendix Chapter 2, introduction (p. 593) and §2.1.7, eqs.
(2.22)–(2.23), pp. 602–604.

## Granger causality in a VAR

For a VAR `z_{t+1} = A z_t + ε_{t+1}` with martingale-difference shocks (any
`ExpectationSystem`), `var_forecast` gives `E_t z_{t+h} = A^h z_t` and `var_innov` the impulse
response `ΔE_{t+1} z_{t+1+j} = A^j ε_{t+1}` (`ΔE_{t+1} = E_{t+1} − E_t`, `innov`); with
orthonormal shocks `cov_innov_shock` shows that the covariance of the revision
`ΔE_{t+1} y_{t+1+j}` with the `x`-shock is `(A^j)_{yx}`. Hence the book's footnote definition ("x
Granger-causes y if surprises to x forecast subsequent surprises to y") is the statement that
some `(A^j)_{yx} ≠ 0`, `j ≥ 1`: `IRFNonCausal`. The standard one-step definition is
`A_{yx} = 0` (`OneStepNonCausal`: the one-step forecast of `y` does not load on `x`).

* `irf_nonCausal_iff_forecast`: IRF non-causality ⇔ no `h`-step forecast of `y` loads on `x`.
* `irf_imp_oneStep`: IRF non-causality implies one-step non-causality.
* `bivariate_oneStep_iff_irf`: in a bivariate VAR the two definitions coincide (the footnote's
  "equivalently").
* `trivariate_counterexample` (survey **E17**): with three variables `x → w → y`
  (`A = [[0,0,0],[1,0,0],[0,1,0]]`), `x` does not Granger-cause `y` at one step but the impulse
  response of `y` to `x` shocks is nonzero at horizon 2; so "x does not Granger-cause y iff the
  IRF is zero" is false for the standard definition with three or more variables.

## News (pp. 501–502, Online Appendix p. 593)

In the news model `s_{t+1} = ε_t` (the surplus is learned one period ahead; exogenous, iid
shocks) the valuation equation gives `v_t = ε_t` (`news_value`): the value of debt forecasts the
surplus perfectly (`news_surplus_eq_value`, regression coefficient one, `news_regCoeff`), while
past surpluses do not forecast it at all (`news_past_surplus_uncorrelated`). In VAR form
(`news_isVAR`) debt Granger-causes surpluses and surpluses do not Granger-cause debt
(`news_debt_causes_surplus`, `news_surplus_not_cause_debt`), although surpluses are exogenous.

## Information sets ((2.22)–(2.23))

`Coarser 𝕀 𝔼`: our information is coarser than the agents' (`𝕀_t(𝔼_t x) = 𝕀_t x`, the tower
property across information sets). `pv_ours_of_agents`: (2.22) implies
`E(v_t | I_t) = E(PV | I_t)`; `pv_ours_iff`: the present-value relation with our forecasts (2.23)
holds iff `v_t` is in our information set; `pv_ours_of_same`: it holds when `I = Ω`;
`pv_ours_fails`: a concrete two-state example where agents know more and (2.23) fails.
-/

namespace Cochrane.ObservationalEquivalence.Granger

open Finset Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open scoped Matrix
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply fullInfo pvExPost)

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Innovations and VARs -/

/-- Cochrane (2023), p. 501, footnote 1: the VAR `z_{t+1} = A z_t + ε_{t+1}` of the variables
`z_t` (restated from the Cochrane `DebtDeficitsInflation` project). -/
def IsVAR (A : Matrix κ κ ℝ) (z ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, z (t + 1) i = ∑ j, A i j • z t j + ε (t + 1) i

/-- Cochrane (2023), p. 501, footnote 1: the VAR shocks are unforecastable, `E_t ε_{t+1} = 0`. -/
def ShockMDS (𝔼 : ExpectationSystem Ω) (ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (ε (t + 1) i) = 0

/-- Cochrane (2023), p. 501, footnote 1: VAR forecasts, `E_t z_{t+k} = A^k z_t` (restated from the
Cochrane `DebtDeficitsInflation` project). -/
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

/-- Cochrane (2023), p. 501, footnote 1: the impulse response,
`ΔE_{t+1} z_{t+1+k} = A^k ε_{t+1}` (restated from the Cochrane `DebtDeficitsInflation`
project). -/
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

/-- Cochrane (2023), p. 501, footnote 1 ("surprises to `x` forecast surprises to subsequent
`y`"): with orthonormal date-`t+1` shocks, the covariance of the revision
`ΔE_{t+1} y_{t+1+k}` with the `x`-shock `ε_{x,t+1}` is the impulse response `(A^k)_{yx}`. -/
theorem cov_innov_shock (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    {B : LinearMap.BilinForm ℝ (Ω → ℝ)} (t : ℕ)
    (hB : ∀ i j, B (ε (t + 1) i) (ε (t + 1) j) = if i = j then 1 else 0) (k : ℕ) (x y : κ) :
    B (innov 𝔼 t (z (t + 1 + k) y)) (ε (t + 1) x) = (A ^ k) y x := by
  rw [var_innov 𝔼 hvar hmds hz t k y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-! ### Definitions of Granger non-causality -/

/-- Cochrane (2023), p. 501, footnote 1 (standard one-step definition): `x` does not
Granger-cause `y` when the one-step forecast of `y` does not load on `x`, `A_{yx} = 0`. -/
def OneStepNonCausal (A : Matrix κ κ ℝ) (x y : κ) : Prop := A y x = 0

/-- Cochrane (2023), p. 501, footnote 1 (the book's definition via surprises; the
"impulse-response" form): `x` does not Granger-cause `y` when the response of `y` to `x` shocks
is zero at every horizon `h ≥ 1`. -/
def IRFNonCausal (A : Matrix κ κ ℝ) (x y : κ) : Prop := ∀ h, 1 ≤ h → (A ^ h) y x = 0

/-- Cochrane (2023), p. 501, footnote 1: IRF non-causality is the same as "no `h`-step forecast
of `y` loads on `x`", `h ≥ 1` (the multi-horizon definition), since `E_t y_{t+h} = (A^h z_t)_y`
(`var_forecast`). -/
theorem irf_nonCausal_iff_forecast (A : Matrix κ κ ℝ) (x y : κ) :
    IRFNonCausal A x y ↔ ∀ h, 1 ≤ h → ∀ zz : κ → ℝ, (A ^ h *ᵥ zz) y = (A ^ h *ᵥ
      Function.update zz x 0) y := by
  constructor
  · intro hA h hh zz
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = x
    · subst hj; rw [hA h hh]; simp
    · rw [Function.update_of_ne hj]
  · intro hF h hh
    have e : Function.update (Pi.single (M := fun _ => ℝ) x 1) x 0 = 0 := by
      funext j
      by_cases hj : j = x
      · subst hj; simp
      · simp [hj]
    have := hF h hh (Pi.single (M := fun _ => ℝ) x 1)
    rw [e] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- Cochrane (2023), p. 501, footnote 1: IRF non-causality implies one-step non-causality. -/
theorem irf_imp_oneStep {A : Matrix κ κ ℝ} {x y : κ} (h : IRFNonCausal A x y) :
    OneStepNonCausal A x y := by
  have := h 1 le_rfl
  simpa [OneStepNonCausal] using this

/-- Cochrane (2023), p. 501, footnote 1 ("Equivalently, `x_t` does not Granger-cause `y_t` if the
impulse-response function of `y` to `x` shocks is zero"): true in a bivariate VAR — the two
definitions coincide. -/
theorem bivariate_oneStep_iff_irf (A : Matrix (Fin 2) (Fin 2) ℝ) {x y : Fin 2} (hxy : x ≠ y) :
    OneStepNonCausal A x y ↔ IRFNonCausal A x y := by
  refine ⟨fun h => ?_, irf_imp_oneStep⟩
  unfold OneStepNonCausal at h
  have hpow : ∀ n, (A ^ n) y x = 0 := by
    intro n
    induction n with
    | zero => simp [Ne.symm hxy]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases x <;> fin_cases y
      · exact absurd rfl hxy
      · simp_all
      · simp_all
      · exact absurd rfl hxy
  exact fun n _ => hpow n

/-- Cochrane (2023), p. 501, footnote 1 (survey E17): the three-variable chain `x → w → y`. -/
def chainA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0; 0, 1, 0]

/-- Cochrane (2023), p. 501, footnote 1 (survey E17): in the VAR with `A = chainA`
(`x = 0`, `w = 1`, `y = 2`), `x` does not Granger-cause `y` in the one-step sense
(`A_{yx} = 0`), yet the impulse response of `y` to an `x` shock is `(A²)_{yx} = 1 ≠ 0`. So the
footnote's "equivalently" fails for the standard definition with three or more variables. -/
theorem trivariate_counterexample :
    OneStepNonCausal chainA 0 2 ∧ (chainA ^ 2) 2 0 = 1 ∧ ¬ IRFNonCausal chainA 0 2 := by
  have h2 : (chainA ^ 2) 2 0 = 1 := by
    simp [sq, chainA, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by simp [OneStepNonCausal, chainA], h2, fun h => ?_⟩
  have := h 2 (by norm_num)
  rw [h2] at this
  exact one_ne_zero this

/-! ### The news model: debt Granger-causes an exogenous surplus -/

/-- Cochrane (2023), pp. 501–502 ("If people learn from reading the news that surpluses will be
poor…"): the news surplus `s_t = ε_{t−1}`, as the moving average with `a = (0, 1)`. -/
def newsCoeff (k : ℕ) : ℝ := if k = 1 then 1 else 0

/-- Cochrane (2023), pp. 501–502: the news surplus is `s_t = ε_{t−1}`. -/
theorem news_surplus (ε : ℤ → Ω → ℝ) (t : ℕ) :
    surplus newsCoeff 1 ε t = ε ((t : ℤ) - 1) := by
  simp [surplus, maProc, newsCoeff]

/-- Cochrane (2023), pp. 501–502: the news surplus coefficients vanish beyond lag one. -/
theorem newsCoeff_support : ∀ k, 1 < k → newsCoeff k = 0 := by
  intro k hk; simp [newsCoeff]; omega

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593: in the news model the valuation
equation gives `v_t = E_t ∑ ρ^j s_{t+1+j} = ε_t` — debt reveals the news. -/
theorem news_value {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t = ε (t : ℤ) := by
  rw [value_eq_maProc hε hM hρ newsCoeff_support]
  simp [maProc, vCoeff, newsCoeff, Finset.sum_range_succ]

/-- Cochrane (2023), pp. 501–502: in the news model the value of debt forecasts next period's
surplus exactly, `s_{t+1} = v_t`. -/
theorem news_surplus_eq_value {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    surplus newsCoeff 1 ε (t + 1) = valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t := by
  rw [news_value hε hM hρ, news_surplus]
  push_cast; ring_nf

/-- Cochrane (2023), pp. 501–502: in the news model the regression coefficient of `s_{t+1}` on
`v_t` is one (with unit-variance white-noise shocks). -/
theorem news_regCoeff {𝔼 : ExpectationSystem Ω} {B : LinearMap.BilinForm ℝ (Ω → ℝ)}
    {ε : ℤ → Ω → ℝ} (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    regCoeff B (surplus newsCoeff 1 ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t) =
      1 := by
  rw [news_surplus_eq_value hε hM hρ, news_value hε hM hρ, regCoeff, hw]
  simp

/-- Cochrane (2023), pp. 501–502: in the news model past and current surpluses do not forecast
next period's surplus: `Cov(s_{t+1}, s_{t−k}) = 0` for every `k ≥ 0` (the surplus is serially
uncorrelated, hence exogenous white noise to an econometrician who sees only surpluses). -/
theorem news_past_surplus_uncorrelated {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (t k : ℕ) (hk : k ≤ t) :
    B (surplus newsCoeff 1 ε (t + 1)) (surplus newsCoeff 1 ε (t - k)) = 0 := by
  rw [news_surplus, news_surplus, hw]
  have : ¬ (((t + 1 : ℕ) : ℤ) - 1 = ((t - k : ℕ) : ℤ) - 1) := by omega
  simp only [this, ↓reduceIte]

/-- Cochrane (2023), pp. 501–502 (the news model is not vacuous): in the truncation model of
`SurplusRegression` (bounded white-noise shocks), `s_{t+1} = v_t` and the regression coefficient
of `s_{t+1}` on `v_t` is one. -/
theorem truncModel_news {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    surplus newsCoeff 1 clampShock (t + 1) =
        valueOfDebt truncSystem ρ (surplus newsCoeff 1 clampShock) t ∧
      regCoeff truncCov (surplus newsCoeff 1 clampShock (t + 1))
        (valueOfDebt truncSystem ρ (surplus newsCoeff 1 clampShock) t) = 1 :=
  ⟨news_surplus_eq_value clampShock_info clampShock_bounded hρ t,
    news_regCoeff clampShock_whiteNoise clampShock_info clampShock_bounded hρ t⟩

/-- Cochrane (2023), pp. 501–502: the news model as a VAR in `z = (s, v)`:
`s_{t+1} = v_t`, `v_{t+1} = ε_{t+1}`, i.e. `A = [[0, 1], [0, 0]]`. -/
def newsA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Cochrane (2023), pp. 501–502: the VAR state of the news model, `z_t = (s_t, v_t)`. -/
noncomputable def newsZ (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) :
    Fin 2 → Ω → ℝ :=
  ![surplus newsCoeff 1 ε t, valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t]

/-- Cochrane (2023), pp. 501–502: the VAR shocks of the news model, `(0, ε_t)`. -/
def newsShock (ε : ℤ → Ω → ℝ) (t : ℕ) : Fin 2 → Ω → ℝ := ![0, ε (t : ℤ)]

/-- Cochrane (2023), pp. 501–502: the news model is the VAR `z_{t+1} = A z_t + (0, ε_{t+1})` with
`A = [[0, 1], [0, 0]]`. -/
theorem news_isVAR {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) :
    IsVAR newsA (newsZ 𝔼 ρ ε) (newsShock ε) := by
  intro t i
  fin_cases i
  · simp [newsZ, newsShock, newsA, Fin.sum_univ_two, news_surplus_eq_value hε hM hρ]
  · simp [newsZ, newsShock, newsA, Fin.sum_univ_two, news_value hε hM hρ]

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 ("debt [should] Granger-cause
surpluses"): in the news model debt Granger-causes surpluses in every sense — the one-step
forecast of `s` loads on `v` (`A_{sv} = 1`). -/
theorem news_debt_causes_surplus : ¬ OneStepNonCausal newsA 1 0 ∧ ¬ IRFNonCausal newsA 1 0 := by
  refine ⟨by simp [OneStepNonCausal, newsA], fun h => ?_⟩
  have := irf_imp_oneStep h
  simp [OneStepNonCausal, newsA] at this

/-- Cochrane (2023), pp. 501–502: in the news model surpluses do not Granger-cause debt at any
horizon, although debt is determined by the valuation equation and surpluses are exogenous. -/
theorem news_surplus_not_cause_debt : IRFNonCausal newsA 0 1 :=
  (bivariate_oneStep_iff_irf newsA (by decide)).mp (by simp [OneStepNonCausal, newsA])

/-! ### Information sets: (2.22) and (2.23) -/

/-- Cochrane (2023), Online Appendix p. 602 (`I_t ⊂ Ω_t`): our information `𝕀` is coarser than
the agents' information `𝔼` — the tower property across information sets. -/
def Coarser (𝕀 𝔼 : ExpectationSystem Ω) : Prop := ∀ t x, 𝕀.E t (𝔼.E t x) = 𝕀.E t x

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: if the value of debt is the
agents' present value (2.22), `v_t = E(PV | Ω_t)`, then with our coarser information
`E(v_t | I_t) = E(PV | I_t)` — "otherwise, we have `E(v_t | I_t)` on the left-hand side". -/
theorem pv_ours_of_agents {𝕀 𝔼 : ExpectationSystem Ω} (hc : Coarser 𝕀 𝔼) {t : ℕ}
    {v pv : Ω → ℝ} (h22 : v = 𝔼.E t pv) : 𝕀.E t v = 𝕀.E t pv := by
  rw [h22, hc]

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: given (2.22), the present-value
relation with our forecasts (2.23), `v_t = E(PV | I_t)`, holds if and only if the value of debt
is in our information set, `E(v_t | I_t) = v_t`. -/
theorem pv_ours_iff {𝕀 𝔼 : ExpectationSystem Ω} (hc : Coarser 𝕀 𝔼) {t : ℕ} {v pv : Ω → ℝ}
    (h22 : v = 𝔼.E t pv) : v = 𝕀.E t pv ↔ 𝕀.E t v = v := by
  rw [← pv_ours_of_agents hc h22]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Cochrane (2023), Online Appendix p. 602: if agents use no more information than we do
(`I_t = Ω_t`), (2.22) is (2.23). -/
theorem pv_ours_of_same (𝔼 : ExpectationSystem Ω) {t : ℕ} {v pv : Ω → ℝ}
    (h22 : v = 𝔼.E t pv) : v = 𝔼.E t pv := h22

/-- Cochrane (2023), Online Appendix p. 602 (example): averaging over the fair coin. -/
noncomputable def coinMean : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun x := fun _ => (x true + x false) / 2
  map_add' x y := by funext; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Cochrane (2023), Online Appendix p. 602 (example): the econometrician learns the coin only
at date `1`. -/
noncomputable def oursInfo : ExpectationSystem Bool where
  E := fun t => if t = 0 then coinMean else LinearMap.id
  const := fun t c => by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]; funext; simp [coinMean]
    · simp [ht]
  mono := fun t x y h => by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]
      intro ω
      simp only [coinMean, LinearMap.coe_mk, AddHom.coe_mk]
      linarith [h true, h false]
    · simpa [ht] using h
  tower := fun {s t} hst x => by
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs; subst ht; simp only [↓reduceIte]; funext; simp [coinMean]
      · simp [hs, ht]
    · have ht : t ≠ 0 := by omega
      simp [hs, ht]
  known := fun {s t} hst x => by
    by_cases ht : t = 0
    · have hs : s = 0 := by omega
      subst hs; subst ht; simp only [↓reduceIte]; funext; simp [coinMean]
    · by_cases hs : s = 0
      · simp [hs, ht]
      · simp [hs, ht]

/-- Cochrane (2023), Online Appendix p. 602 (example): our information is coarser than the
agents'. -/
theorem ours_coarser : Coarser oursInfo (fullInfo Bool) := fun _ _ => rfl

/-- Cochrane (2023), Online Appendix p. 602 (example): the surplus `s_1 = ±1` according to the
coin, zero at all other dates. -/
def coinSurplus (t : ℕ) (ω : Bool) : ℝ := if t = 1 then (if ω then 1 else -1) else 0

/-- Cochrane (2023), Online Appendix p. 602 (example): the date-`0` present value of the coin
surplus is `∑_j ρ^j s_{1+j} = s_1`. -/
theorem coinSurplus_pv (ρ : ℝ) (ω : Bool) :
    ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω = if ω then 1 else -1 := by
  rw [tsum_eq_single 0 fun j hj => by simp [coinSurplus, hj]]
  simp [coinSurplus]

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: when agents know more than we
do, (2.22) holds but (2.23) fails — the value of debt `v_0 = ±1` is the agents' present value,
while our forecast of the present value is `0`, and `v_0` is not in our information set. -/
theorem pv_ours_fails (ρ : ℝ) :
    valueOfDebt (fullInfo Bool) ρ coinSurplus 0 ≠
      oursInfo.E 0 (fun ω => ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω) ∧
    oursInfo.E 0 (valueOfDebt (fullInfo Bool) ρ coinSurplus 0) ≠
      valueOfDebt (fullInfo Bool) ρ coinSurplus 0 := by
  have hv : valueOfDebt (fullInfo Bool) ρ coinSurplus 0 = fun ω => if ω then 1 else -1 := by
    funext ω
    simp only [valueOfDebt, fullInfo, pvExPost, LinearMap.id_apply]
    exact coinSurplus_pv ρ ω
  have hpv : (fun ω => ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω) =
      fun ω => if ω then (1 : ℝ) else -1 := funext (coinSurplus_pv ρ)
  have hmean : oursInfo.E 0 (fun ω : Bool => if ω then (1 : ℝ) else -1) = 0 := by
    funext ω; simp [oursInfo, coinMean]
  refine ⟨?_, ?_⟩
  · rw [hv, hpv, hmean]
    intro h
    have := congrFun h true
    simp at this
  · rw [hv, hmean]
    intro h
    have := congrFun h true
    simp at this

end Cochrane.ObservationalEquivalence.Granger

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The present-value relation is an identity; the ex-post discount factor

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 2, §2.2
(eqs. (2.24)–(2.26), pp. 604–605) and §2.3 (pp. 606–607); Chapter 22, §22.2.4, p. 499 (the
discount-factor existence theorem applied to government debt) and §22.5, p. 505 ("as
observational equivalence and existence of discount factor theorems should indicate"). (§22.4,
pp. 503–505, "Plausibility and other evidence", is verbal and has no formal content.)

The VAR material (`PowDecay`, Neumann series, `flow_restriction_iff_pv`, `var_pv_identity`, …)
is restated from the Cochrane `DebtDeficitsInflation` project (`VARIdentities`), adapted to this
project's core. The innovation operator `innov`, the ex-post present value `pvExPost`, and the
flow-iteration lemmas `flow_telescope` and `pv_of_flow` are shared with chain A and live in
`ExpectationTools`.

## Main results

* (2.24)–(2.26), the VAR with `v`: `flow_restriction_of_identity` (the flow identity forces the
  coefficient restriction (2.25) `a_v'(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)'A`),
  `flow_restriction_iff_pv` ((2.25) ⇔ the present-value restriction, needing only `I − ρA`
  invertible), `var_pv_identity` (in a stable VAR satisfying the flow identity, the VAR present
  value converges and equals `v_t` — "(2.26) reduces to `v_t = v_t`").
* `flow_forces_singular`: a VAR satisfying the flow identity pathwise has singular shocks,
  `c'ε_{t+1} = 0` with `c = ρa_v − (a_{rⁿ} − a_π − a_g − a_s)`, and `a_v' = c'A`;
  `nondeg_forces_trivial`: with nondegenerate shocks this forces `v ≡ 0` (implicit in the book).
* §2.3, the linearised identity: `expost_pv_finite`
  `v_t = ∑_{j<T} ρ^j (s_{t+1+j} − r_{t+1+j}) + ρ^T v_{t+T}`, `expost_pv` (its limit, an ex-post
  identity for bounded paths); `pv_identity_exante`; `as_eq_ar_innov`:
  `ΔE_{t+1} ∑ ρ^j s_{t+1+j} = ΔE_{t+1} ∑ ρ^j r_{t+1+j}` in every model obeying the flow identity
  with bounded variables — "`0 = a_s(ρ) − a_r(ρ)` … is an identity"; `const_return_as_zero`: with
  a constant discount rate this becomes the testable `a(ρ) = 0` restriction (a restriction on the
  discount-rate model).
* `genVAR` (`a(ρ)` of an observable of a VAR), `genVAR_hasSum` (`a(ρ) = ∑ ρ^j a_j`),
  `innov_pv_var` (`ΔE_{t+1} ∑ ρ^j (a'z)_{t+1+j} = a(ρ)'ε_{t+1}`), `as_eq_ar_var`
  (`a_s(ρ) = a_r(ρ)` for nondegenerate shocks).
* Ex-post discount factor (p. 499): with one-period nominal debt, the flow
  `B_{t−1} = P_t s_t + Q_t B_t` and `Λ_{t+1}/Λ_t := Q_t P_{t+1}/P_t`: `sdf_pos` (positive when
  bond prices and the price level are positive), `sdf_prices_bond` (it prices the bond exactly),
  `sdf_valuation_finite`, `sdf_valuation_tendsto` and `sdf_valuation_hasSum`
  (`B_{t−1}/P_t = ∑_j (Λ_{t+j}/Λ_t) s_{t+j}` under the transversality condition), the converse
  `tvc_of_sdf_valuation`, and `sdf_valuation_E`
  (`B_{t−1}/P_t = E_t ∑_j (Λ_{t+j}/Λ_t) s_{t+j}` for any `ExpectationSystem`).
-/

namespace Cochrane.ObservationalEquivalence.PresentValueIdentity

open Filter Topology Finset
open scoped Matrix
open Cochrane.ObservationalEquivalence.Granger (IsVAR ShockMDS var_forecast var_innov)
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply innov_of_known pvExPost
  summable_pow_mul_of_bounded tendsto_pow_mul_of_bounded flow_telescope pv_of_flow)

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Observables and stable VARs (restated from the `DebtDeficitsInflation` project) -/

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
theorem tendsto_pow_entry_of_powDecay {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
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
than one", Ch. 4–5 survey E18; convergence of the present value is a separate matter,
`var_pv_identity`). -/
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


omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605: observables are homogeneous in the weights. -/
theorem obs_smul (r : ℝ) (c : κ → ℝ) (y : κ → Ω → ℝ) : obs (r • c) y = r • obs c y := by
  simp [obs, Finset.smul_sum, smul_smul]

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605: in the VAR, `c'z_{t+1} = (c'A) z_t + c'ε_{t+1}`. -/
theorem obs_var_succ {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε)
    (c : κ → ℝ) (t : ℕ) : obs c (z (t + 1)) = obs (c ᵥ* A) (z t) + obs c (ε (t + 1)) := by
  simp only [obs, hvar t, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    Matrix.vecMul, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun x y => (c x * A x y) • z t y)]

/-! ### The exact flow identity forces singular shocks -/

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix eqs. (2.24)–(2.25), p. 605: if the flow identity
`ρv_{t+1} = v_t + d'z_{t+1}` (`d = a_{rⁿ} − a_π − a_g − a_s`) holds pathwise in a VAR with
`v = a_v'z`, then the shocks are singular, `c'ε_{t+1} = 0` with `c = ρa_v − d`, and the value of
debt is `v_t = (c'A) z_t` (the restriction (2.25)). -/
theorem flow_forces_singular (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) {ρ : ℝ} {av d : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs d (z (t + 1))) (t : ℕ) :
    obs (ρ • av - d) (ε (t + 1)) = 0 ∧ obs av (z t) = obs ((ρ • av - d) ᵥ* A) (z t) := by
  set c := ρ • av - d with hc
  have h1 : obs c (z (t + 1)) = obs av (z t) := by
    rw [hc, obs_sub, obs_smul, hflow t]; abel
  rw [obs_var_succ hvar] at h1
  have hE : 𝔼.E t (obs c (ε (t + 1))) = 0 := by
    rw [E_obs]; simp [obs, hmds t]
  have h2 : obs av (z t) = obs (c ᵥ* A) (z t) := by
    have := congrArg (𝔼.E t) h1
    rw [map_add, hE, add_zero, obs_adapted 𝔼 hz, obs_adapted 𝔼 hz] at this
    exact this.symm
  refine ⟨?_, h2⟩
  rw [← h2] at h1
  exact add_eq_left.mp (h2 ▸ h1)

/-- Cochrane (2023), Online Appendix p. 605 (implicit): the shocks at date `t + 1` are
nondegenerate — no nonzero combination of them vanishes identically. -/
def ShockNondeg (ε : ℕ → κ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ c : κ → ℝ, obs c (ε (t + 1)) = 0 → c = 0

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605 (implicit): if the flow identity holds exactly in a
VAR with nondegenerate shocks at some date, then `ρa_v = a_{rⁿ} − a_π − a_g − a_s` and the value
of debt is identically zero — an exact identity among VAR variables requires a singular shock
covariance. -/
theorem nondeg_forces_trivial (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) {ρ : ℝ} {av d : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs d (z (t + 1))) {t0 : ℕ}
    (hnd : ShockNondeg ε t0) : ρ • av = d ∧ ∀ t, obs av (z t) = 0 := by
  have hc : ρ • av - d = 0 := hnd _ (flow_forces_singular 𝔼 hvar hmds hz hflow t0).1
  refine ⟨sub_eq_zero.mp hc, fun t => ?_⟩
  rw [(flow_forces_singular 𝔼 hvar hmds hz hflow t).2, hc, Matrix.zero_vecMul]
  simp [obs]

/-! ### §2.3: the linearised present-value identity -/

/-- Cochrane (2023), Online Appendix §2.3, p. 606: iterating the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s_{t+1}` (`r` the ex-post real return) gives the identity
`v_t = ∑_{j<T} ρ^j (s_{t+1+j} − r_{t+1+j}) + ρ^T v_{t+T}`, path by path. -/
theorem expost_pv_finite {ρ : ℝ} {v r s : ℕ → ℝ}
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t T : ℕ) :
    v t = ∑ j ∈ range T, ρ ^ j * (s (t + 1 + j) - r (t + 1 + j)) + ρ ^ T * v (t + T) := by
  have h := flow_telescope (ρ := ρ) (v := v) (y := fun k => s (k + 1) - r (k + 1))
    (fun k => by rw [smul_eq_mul, hflow k]; ring) t T
  simp only [smul_eq_mul] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show t + j + 1 = t + 1 + j by omega]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("Imposing convergence of the last term"):
for bounded paths and `|ρ| < 1` the linearised identity holds as a genuine infinite sum,
`v_t = ∑_{j≥0} ρ^j (s_{t+1+j} − r_{t+1+j})` — an ex-post identity. -/
theorem expost_pv {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1) {v r s : ℕ → ℝ} (hv : ∀ t, |v t| ≤ M)
    (hr : ∀ t, |r t| ≤ Kr) (hs : ∀ t, |s t| ≤ Ks)
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t : ℕ) :
    HasSum (fun j => ρ ^ j * (s (t + 1 + j) - r (t + 1 + j))) (v t) := by
  have hsum : Summable (fun j => ρ ^ j * (s (t + 1 + j) - r (t + 1 + j))) :=
    summable_pow_mul_of_bounded hρ (x := fun j => s (t + 1 + j) - r (t + 1 + j))
      (K := Ks + Kr) fun j => (abs_sub _ _).trans (add_le_add (hs _) (hr _))
  refine (hsum.hasSum_iff_tendsto_nat).mpr ?_
  have hlim : Tendsto (fun T => ρ ^ T * v (t + T)) atTop (𝓝 0) :=
    tendsto_pow_mul_of_bounded hρ (x := fun T => v (t + T)) fun T => hv (t + T)
  have h2 : Tendsto (fun T => v t - ρ ^ T * v (t + T)) atTop (𝓝 (v t - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero] at h2
  refine h2.congr fun T => ?_
  rw [expost_pv_finite hflow t T]
  ring

/-- Cochrane (2023), Online Appendix §2.3, p. 606: under the hypotheses of `expost_pv`, the
present values of surpluses and of returns converge separately and
`v_t = ∑ ρ^j s_{t+1+j} − ∑ ρ^j r_{t+1+j}`. -/
theorem expost_pv_split {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1) {v r s : ℕ → ℝ} (hv : ∀ t, |v t| ≤ M)
    (hr : ∀ t, |r t| ≤ Kr) (hs : ∀ t, |s t| ≤ Ks)
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t : ℕ) :
    v t = ∑' j, ρ ^ j * s (t + 1 + j) - ∑' j, ρ ^ j * r (t + 1 + j) := by
  have hb : ∀ (x : ℕ → ℝ) (K : ℝ), (∀ t, |x t| ≤ K) →
      Summable (fun j => ρ ^ j * x (t + 1 + j)) := fun x K hx =>
    summable_pow_mul_of_bounded hρ (x := fun j => x (t + 1 + j)) fun j => hx _
  rw [← Summable.tsum_sub (hb s Ks hs) (hb r Kr hr), (expost_pv hρ hv hr hs hflow t).tsum_eq.symm]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("It always holds ex-post, so it always holds
ex-ante"): for bounded processes obeying the flow identity with `v` known at `t`,
`v_t = E_t ∑ ρ^j s_{t+1+j} − E_t ∑ ρ^j r_{t+1+j}`. -/
theorem pv_identity_exante (𝔼 : ExpectationSystem Ω) {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1)
    {v r s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hr : ∀ t ω, |r t ω| ≤ Kr)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1))
    (hva : 𝔼.Adapted v) (t : ℕ) :
    v t = 𝔼.E t (pvExPost ρ s t) - 𝔼.E t (pvExPost ρ r t) := by
  have hpath : v t = pvExPost ρ s t - pvExPost ρ r t := by
    funext ω
    refine expost_pv_split hρ (v := fun k => v k ω) (r := fun k => r k ω)
      (s := fun k => s k ω) (fun k => hv k ω) (fun k => hr k ω) (fun k => hs k ω)
      (fun k => ?_) t
    have := congrFun (hflow k) ω
    simpa using this
  rw [← map_sub, ← hpath, hva t]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("taking `ΔE_{t+1}` of both sides, we obtain
`0 = a_s(ρ) − a_r(ρ)` … this relation derives from an identity, so it too is an identity"): in
every model in which bounded processes obey the flow identity and `v_t` is known at `t`, the
revision of the present value of surpluses equals the revision of the present value of
returns. -/
theorem as_eq_ar_innov (𝔼 : ExpectationSystem Ω) {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1)
    {v r s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hr : ∀ t ω, |r t ω| ≤ Kr)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1))
    (hva : 𝔼.Adapted v) (t : ℕ) :
    innov 𝔼 t (pvExPost ρ s t) = innov 𝔼 t (pvExPost ρ r t) := by
  have hpath : v t = pvExPost ρ s t - pvExPost ρ r t := by
    funext ω
    refine expost_pv_split hρ (v := fun k => v k ω) (r := fun k => r k ω)
      (s := fun k => s k ω) (fun k => hv k ω) (fun k => hr k ω) (fun k => hs k ω)
      (fun k => ?_) t
    have := congrFun (hflow k) ω
    simpa using this
  have h0 : innov 𝔼 t (v t) = 0 := by
    have h1 : 𝔼.E (t + 1) (𝔼.E t (v t)) = 𝔼.E t (v t) := 𝔼.known (Nat.le_succ t) _
    rw [hva t] at h1
    rw [innov_apply, h1, hva t, sub_self]
  rw [hpath, map_sub] at h0
  exact sub_eq_zero.mp h0

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("the constant discount factor model is just
`a_r(ρ) = 0`"): with a constant ex-post return, the revision of the present value of surpluses
is zero — the Hansen–Roberds–Sargent restriction `a(ρ) = 0`, testable only because it restricts
the discount rate. -/
theorem const_return_as_zero (𝔼 : ExpectationSystem Ω) {ρ M Ks c : ℝ} (hρ : |ρ| < 1)
    {v s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hs : ∀ t ω, |s t ω| ≤ Ks)
    (hflow : ∀ t, ρ • v (t + 1) = v t + (fun _ => c) - s (t + 1)) (hva : 𝔼.Adapted v)
    (t : ℕ) : innov 𝔼 t (pvExPost ρ s t) = 0 := by
  rw [as_eq_ar_innov 𝔼 hρ (r := fun _ _ => c) hv (fun _ _ => le_refl |c|) hs hflow hva t,
    innov_apply]
  unfold pvExPost
  rw [𝔼.const, 𝔼.const, sub_self]

/-! ### `a_s(ρ) = a_r(ρ)` in a VAR -/

/-- Cochrane (2023), Online Appendix §2.3, p. 606: for an observable `a'z` of a VAR the
moving-average coefficients are `a_j = (A^j)'a` and `a(ρ) = ∑ ρ^j a_j = ((I − ρA)⁻¹)'a`. -/
noncomputable def genVAR (A : Matrix κ κ ℝ) (ρ : ℝ) (a : κ → ℝ) : κ → ℝ := a ᵥ* (1 - ρ • A)⁻¹

/-- Cochrane (2023), Online Appendix §2.3, p. 606: `a(ρ)'e = ∑_j ρ^j a_j'e` for a stable VAR. -/
theorem genVAR_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (a e : κ → ℝ) :
    HasSum (fun j => ρ ^ j * ((a ᵥ* A ^ j) ⬝ᵥ e)) (genVAR A ρ a ⬝ᵥ e) := by
  simp only [genVAR, ← Matrix.dotProduct_mulVec, weight_bilin]
  exact neumann_bilin_hasSum (powDecay_smul hA hρ) a e

/-- Cochrane (2023), Online Appendix §2.3, p. 606: in a stable VAR with bounded states, the
revision of the present value of an observable is `ΔE_{t+1} ∑ ρ^j (a'z)_{t+1+j} = a(ρ)'ε_{t+1}`
(genuine infinite sums, `|ρ| < 1`). -/
theorem innov_pv_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ Mz : ℝ} (hρ : |ρ| < 1) (hzb : ∀ t i ω, |z t i ω| ≤ Mz) (a : κ → ℝ)
    (t : ℕ) (w : Ω) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * obs a (z (t + 1 + j)) ω) w =
      genVAR A ρ a ⬝ᵥ vecAt (ε (t + 1)) w := by
  set C : ℝ := (∑ i, |a i|) * Mz with hC
  have hob : ∀ k ω, |obs a (z k) ω| ≤ C := by
    intro k ω
    rw [obs_apply, hC, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [vecAt, abs_mul]
    exact mul_le_mul_of_nonneg_left (hzb k i ω) (abs_nonneg _)
  have hbd : ∀ j ω, |ρ ^ j * obs a (z (t + 1 + j)) ω| ≤ |ρ| ^ j * C := by
    intro j ω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hob _ ω) (pow_nonneg (abs_nonneg _) _)
  have hE1 := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω => ρ ^ j * obs a (z (t + 1 + j)) ω)
    hbd (t + 1) w
  have hE0 := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω => ρ ^ j * obs a (z (t + 1 + j)) ω)
    hbd t w
  have hgeo : Summable (fun j : ℕ => |ρ| ^ j * C) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right C
  have hs1 : Summable (fun j => 𝔼.E (t + 1) (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w) :=
    Summable.of_norm_bounded hgeo fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hbd j) _ w
  have hs0 : Summable (fun j => 𝔼.E t (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w) :=
    Summable.of_norm_bounded hgeo fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hbd j) _ w
  rw [innov_apply, Pi.sub_apply, hE1, hE0, ← Summable.tsum_sub hs1 hs0]
  have hterm : ∀ j, 𝔼.E (t + 1) (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w -
      𝔼.E t (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w =
      ρ ^ j * innov 𝔼 t (obs a (z (t + 1 + j))) w := by
    intro j
    have hf : (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) = ρ ^ j • obs a (z (t + 1 + j)) := rfl
    rw [hf, map_smul, map_smul, innov_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp only [hterm]
  rw [(var_weighted_sum 𝔼 hvar hmds hz hA hρ.le a t w).tsum_eq, genVAR,
    ← Matrix.dotProduct_mulVec]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("Imposing convergence of the last term …
we obtain `0 = a_s(ρ) − a_r(ρ)`"): if surpluses `s = a_s'z` and ex-post returns `r = a_r'z` are
observables of a stable bounded VAR, and a bounded adapted value of debt obeys the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s_{t+1}`, then `a_s(ρ)'ε_{t+1} = a_r(ρ)'ε_{t+1}`; with nondegenerate
shocks, `a_s(ρ) = a_r(ρ)` — an identity, not a testable restriction. -/
theorem as_eq_ar_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ Mz M : ℝ} (hρ : |ρ| < 1) (hzb : ∀ t i ω, |z t i ω| ≤ Mz)
    {as ar : κ → ℝ} {v : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hva : 𝔼.Adapted v)
    (hflow : ∀ t, ρ • v (t + 1) = v t + obs ar (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) :
    obs (genVAR A ρ as - genVAR A ρ ar) (ε (t + 1)) = 0 ∧
      (ShockNondeg ε t → genVAR A ρ as = genVAR A ρ ar) := by
  have hob : ∀ (a : κ → ℝ) (k : ℕ) (ω : Ω), |obs a (z k) ω| ≤ (∑ i, |a i|) * Mz := by
    intro a k ω
    rw [obs_apply, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [vecAt, abs_mul]
    exact mul_le_mul_of_nonneg_left (hzb k i ω) (abs_nonneg _)
  have hid := as_eq_ar_innov 𝔼 hρ (s := fun k => obs as (z k)) (r := fun k => obs ar (z k)) hv
    (hob ar) (hob as) hflow hva t
  unfold pvExPost at hid
  have hzero : obs (genVAR A ρ as - genVAR A ρ ar) (ε (t + 1)) = 0 := by
    funext w
    rw [obs_sub, Pi.sub_apply, obs_apply, obs_apply,
      ← innov_pv_var 𝔼 hvar hmds hz hA hρ hzb as t w,
      ← innov_pv_var 𝔼 hvar hmds hz hA hρ hzb ar t w, hid, sub_self, Pi.zero_apply]
  exact ⟨hzero, fun hnd => sub_eq_zero.mp (hnd _ hzero)⟩

/-! ### The ex-post discount factor (p. 499) -/

/-- Cochrane (2023), p. 499: the flow constraint with one-period nominal debt,
`B_{t−1} = P_t s_t + Q_t B_t`, written with `D t = B_{t−1}` (debt due at the start of `t`) and
`Q t` the price at `t` of a bond paying one unit of money at `t + 1`. -/
def DebtFlow (D P Q s : ℕ → ℝ) : Prop := ∀ t, D t = P t * s t + Q t * D (t + 1)

/-- Cochrane (2023), p. 499: the one-period ex-post discount factor
`Λ_{t+1}/Λ_t := Q_t P_{t+1}/P_t`. -/
noncomputable def sdfStep (P Q : ℕ → ℝ) (t : ℕ) : ℝ := Q t * P (t + 1) / P t

/-- Cochrane (2023), p. 499: the ex-post discount factor `Λ_t = ∏_{k<t} Q_k P_{k+1}/P_k`,
`Λ_0 = 1`. -/
noncomputable def sdf (P Q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => sdf P Q t * sdfStep P Q t

/-- Cochrane (2023), p. 499 ("Absent arbitrage, there is a discount factor"): with positive bond
prices and price levels the ex-post discount factor is strictly positive. -/
theorem sdf_pos {P Q : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    0 < sdf P Q t := by
  induction t with
  | zero => simp [sdf]
  | succ t ih => exact mul_pos ih (div_pos (mul_pos (hQ t) (hP (t + 1))) (hP t))

/-- Cochrane (2023), p. 499: the ex-post discount factor prices the one-period nominal bond
exactly, `(Λ_{t+1}/Λ_t)(1/P_{t+1}) = Q_t/P_t`. -/
theorem sdf_prices_bond {P Q : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    sdf P Q (t + 1) / sdf P Q t * (1 / P (t + 1)) = Q t / P t := by
  have h0 := (sdf_pos hP hQ t).ne'
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  simp only [sdf, sdfStep]
  field_simp

/-- Cochrane (2023), p. 499: in real terms the flow constraint is a one-period pricing
identity, `B_{t−1}/P_t = s_t + (Λ_{t+1}/Λ_t) B_t/P_{t+1}`. -/
theorem sdf_flow {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ) :
    D t / P t = s t + sdf P Q (t + 1) / sdf P Q t * (D (t + 1) / P (t + 1)) := by
  have h0 := (sdf_pos hP hQ t).ne'
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  rw [hD t]
  simp only [sdf, sdfStep]
  field_simp

/-- Cochrane (2023), p. 499: iterating, `B_{t−1}/P_t = ∑_{j<T} (Λ_{t+j}/Λ_t) s_{t+j} +
(Λ_{t+T}/Λ_t) B_{t+T−1}/P_{t+T}`. -/
theorem sdf_valuation_finite {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t T : ℕ) :
    D t / P t = ∑ j ∈ range T, sdf P Q (t + j) / sdf P Q t * s (t + j) +
      sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T)) := by
  induction T with
  | zero =>
    have h0 := (sdf_pos hP hQ t).ne'
    simp [h0]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, sdf_flow hP hQ hD (t + T),
      show t + (T + 1) = t + T + 1 by omega]
    have h0 := (sdf_pos hP hQ t).ne'
    have h1 := (sdf_pos hP hQ (t + T)).ne'
    field_simp
    ring

/-- Cochrane (2023), p. 499: under the transversality condition
`(Λ_{t+T}/Λ_t) B_{t+T−1}/P_{t+T} → 0`, the partial sums of `∑_j (Λ_{t+j}/Λ_t) s_{t+j}` converge
to `B_{t−1}/P_t`. -/
theorem sdf_valuation_tendsto {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (htvc : Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop
      (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ range T, sdf P Q (t + j) / sdf P Q t * s (t + j)) atTop
      (𝓝 (D t / P t)) := by
  have h2 : Tendsto (fun T => D t / P t -
      sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop (𝓝 (D t / P t - 0)) :=
    tendsto_const_nhds.sub htvc
  rw [sub_zero] at h2
  refine h2.congr fun T => ?_
  rw [sdf_valuation_finite hP hQ hD t T]
  ring

/-- Cochrane (2023), p. 499 (the discount-factor theorem applied to government debt): with
positive bond prices and price levels, the transversality condition and summability of the
discounted surpluses, `B_{t−1}/P_t = ∑_{j≥0} (Λ_{t+j}/Λ_t) s_{t+j}` for the ex-post discount
factor. -/
theorem sdf_valuation_hasSum {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (htvc : Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop
      (𝓝 0))
    (hsum : Summable (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j))) :
    HasSum (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j)) (D t / P t) :=
  hsum.hasSum_iff_tendsto_nat.mpr (sdf_valuation_tendsto hP hQ hD t htvc)

/-- Cochrane (2023), p. 499: conversely, if the valuation formula holds (as a genuine sum), the
transversality condition holds — so given the flow constraint, the valuation equation with the
ex-post discount factor is equivalent to the transversality condition. -/
theorem tvc_of_sdf_valuation {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (hval : HasSum (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j)) (D t / P t)) :
    Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := D t / P t)).sub hval.tendsto_sum_nat
  rw [sub_self] at h
  refine h.congr fun T => ?_
  rw [sdf_valuation_finite hP hQ hD t T]
  ring

/-- Cochrane (2023), p. 499, displayed equation: for random processes satisfying the flow
constraint, positivity, the transversality condition and summability state by state, with
`B_{t−1}/P_t` known at `t`, `B_{t−1}/P_t = E_t ∑_{j≥0} (Λ_{t+j}/Λ_t) s_{t+j}` for any
`ExpectationSystem` — present-value "puzzles" are puzzles of the discount factor. -/
theorem sdf_valuation_E (𝔼 : ExpectationSystem Ω) {D P Q s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hQ : ∀ t ω, 0 < Q t ω)
    (hD : ∀ ω, DebtFlow (fun k => D k ω) (fun k => P k ω) (fun k => Q k ω) (fun k => s k ω))
    (t : ℕ)
    (htvc : ∀ ω, Tendsto (fun T => sdf (fun k => P k ω) (fun k => Q k ω) (t + T) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * (D (t + T) ω / P (t + T) ω)) atTop (𝓝 0))
    (hsum : ∀ ω, Summable (fun j => sdf (fun k => P k ω) (fun k => Q k ω) (t + j) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω))
    (hknown : 𝔼.E t (fun ω => D t ω / P t ω) = fun ω => D t ω / P t ω) :
    (fun ω => D t ω / P t ω) = 𝔼.E t (fun ω => ∑' j, sdf (fun k => P k ω) (fun k => Q k ω)
      (t + j) / sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω) := by
  have hpath : (fun ω => ∑' j, sdf (fun k => P k ω) (fun k => Q k ω) (t + j) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω) = fun ω => D t ω / P t ω := by
    funext ω
    exact (sdf_valuation_hasSum (fun k => hP k ω) (fun k => hQ k ω) (hD ω) t (htvc ω)
      (hsum ω)).tsum_eq
  rw [hpath, hknown]

end Cochrane.ObservationalEquivalence.PresentValueIdentity

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Observational equivalence in asset pricing and the finite-state discount-factor theorem

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.2.4, pp. 498–499.

"Marginal utility and probability always enter together in asset pricing formulas,
`p = ∑_s π_s u'(c_s) x_s` … 'Rational' (`u'`) and 'behavioral' (misperceived probabilities `π`)
finance are observationally equivalent", formalised in the Harrison–Kreps martingale-measure and
Hansen–Richard discount-factor existence theorems.

## Main results

* `price π m x = ∑_s π_s m_s x_s`. `rational_behavioral_equiv`: for any full-support beliefs
  `π'`, the marginal utilities `m' = πm/π'` give identical prices for every payoff;
  `same_prices_iff`: two (belief, marginal-utility) pairs give the same prices for all payoffs
  iff `π_s m_s = π'_s m'_s` in every state — only the product is identified;
  `behavioral_pos`: positivity of marginal utility is preserved.
* `riskNeutral`: the risk-neutral (martingale) measure `q = πm/∑πm`, `p = (∑πm) E^q[x]`.
* Finite-state fundamental theorem of asset pricing (one period, finitely many assets
  `X : J → S → ℝ` with prices `p`): `NoArbitrage X p ↔ ∃ m, IsSDF X p m` (`ftap`), the
  discount-factor existence theorem behind "absent arbitrage, there is a discount factor"
  (p. 499). The hard direction is proved with the Hahn–Banach separation theorem
  (`exists_sdf_of_noArbitrage`); the easy one is `noArbitrage_of_sdf`.
  `sdf_expectation_form`: given any full-support probabilities, the price is the expectation
  `p_j = E^π[(m/π) X_j]`.
-/

namespace Cochrane.ObservationalEquivalence.AssetPricingOE

open Finset

variable {S : Type*} [Fintype S]

/-! ### Probabilities and marginal utility enter only as a product -/

/-- Cochrane (2023), p. 498: the asset-pricing formula `p = ∑_s π_s u'(c_s) x_s`, with
probabilities `π`, marginal utilities `m = u'(c)` and payoff `x`. -/
def price (π m x : S → ℝ) : ℝ := ∑ s, π s * m s * x s

/-- Cochrane (2023), p. 498 ("'Rational' and 'behavioral' finance are observationally
equivalent"): for any full-support beliefs `π'`, the marginal utilities `m' = πm/π'` price every
payoff exactly as `(π, m)` does. -/
theorem rational_behavioral_equiv (π m π' : S → ℝ) (hπ' : ∀ s, 0 < π' s) (x : S → ℝ) :
    price π m x = price π' (fun s => π s * m s / π' s) x := by
  unfold price
  refine Finset.sum_congr rfl fun s _ => ?_
  have := (hπ' s).ne'
  field_simp

omit [Fintype S] in
/-- Cochrane (2023), p. 498: if `π, m, π'` are strictly positive, so is `m' = πm/π'`. -/
theorem behavioral_pos {π m π' : S → ℝ} (hπ : ∀ s, 0 < π s) (hm : ∀ s, 0 < m s)
    (hπ' : ∀ s, 0 < π' s) (s : S) : 0 < π s * m s / π' s :=
  div_pos (mul_pos (hπ s) (hm s)) (hπ' s)

/-- Cochrane (2023), p. 498 ("probability and marginal utility always enter together"): two
pairs `(π, m)` and `(π', m')` give the same price to every payoff iff `π_s m_s = π'_s m'_s` in
every state — prices identify only the product. -/
theorem same_prices_iff (π m π' m' : S → ℝ) :
    (∀ x, price π m x = price π' m' x) ↔ ∀ s, π s * m s = π' s * m' s := by
  classical
  constructor
  · intro h s
    have := h (Pi.single s 1)
    simpa [price, Pi.single_apply] using this
  · intro h x
    unfold price
    exact Finset.sum_congr rfl fun s _ => by rw [h s]

/-- Cochrane (2023), pp. 498–499 (Harrison–Kreps martingale measure): with `π, m > 0` (and `S`
nonempty), `q = πm/∑πm` is a full-support probability and `p = (∑ πm) ∑_s q_s x_s`. -/
theorem riskNeutral [Nonempty S] {π m : S → ℝ} (hπ : ∀ s, 0 < π s) (hm : ∀ s, 0 < m s)
    (x : S → ℝ) :
    let Z := ∑ s, π s * m s
    (∀ s, 0 < π s * m s / Z) ∧ ∑ s, π s * m s / Z = 1 ∧
      price π m x = Z * ∑ s, (π s * m s / Z) * x s := by
  intro Z
  have hZ : 0 < Z := Finset.sum_pos (fun s _ => mul_pos (hπ s) (hm s)) Finset.univ_nonempty
  refine ⟨fun s => div_pos (mul_pos (hπ s) (hm s)) hZ, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hZ.ne']
  · unfold price
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by field_simp

/-! ### The finite-state discount-factor theorem -/

variable {J : Type*} [Fintype J]

/-- Cochrane (2023), p. 499: the cost `∑_j θ_j p_j` of a portfolio `θ`. -/
def cost (p : J → ℝ) (θ : J → ℝ) : ℝ := ∑ j, θ j * p j

/-- Cochrane (2023), p. 499: the payoff `∑_j θ_j X_j(s)` of a portfolio `θ` in state `s`. -/
def payoff (X : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * X j s

/-- Cochrane (2023), p. 499: an arbitrage — a portfolio with nonnegative payoff in every state
and nonpositive cost that either costs strictly less than zero or pays strictly positive in
some state. -/
def IsArbitrage (X : J → S → ℝ) (p : J → ℝ) (θ : J → ℝ) : Prop :=
  (∀ s, 0 ≤ payoff X θ s) ∧ cost p θ ≤ 0 ∧ (cost p θ < 0 ∨ ∃ s, 0 < payoff X θ s)

/-- Cochrane (2023), p. 499 ("absent arbitrage"): no portfolio is an arbitrage. -/
def NoArbitrage (X : J → S → ℝ) (p : J → ℝ) : Prop := ∀ θ, ¬ IsArbitrage X p θ

/-- Cochrane (2023), p. 499: a strictly positive (state-price) discount factor `m` that prices
every asset, `p_j = ∑_s m_s X_j(s)`. -/
def IsSDF (X : J → S → ℝ) (p : J → ℝ) (m : S → ℝ) : Prop :=
  (∀ s, 0 < m s) ∧ ∀ j, p j = ∑ s, m s * X j s

/-- Cochrane (2023), p. 499: with a discount factor, the cost of any portfolio is the
discounted value of its payoff. -/
theorem cost_eq_of_sdf {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m)
    (θ : J → ℝ) : cost p θ = ∑ s, m s * payoff X θ s := by
  simp only [cost, payoff, hm.2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

/-- Cochrane (2023), p. 499 (easy direction of the discount-factor theorem): a strictly
positive discount factor rules out arbitrage. -/
theorem noArbitrage_of_sdf {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m) :
    NoArbitrage X p := by
  rintro θ ⟨hpay, hcost, hstrict⟩
  have hc := cost_eq_of_sdf hm θ
  have hnn : ∀ s ∈ (Finset.univ : Finset S), 0 ≤ m s * payoff X θ s :=
    fun s _ => mul_nonneg (hm.1 s).le (hpay s)
  have h0 : 0 ≤ cost p θ := hc ▸ Finset.sum_nonneg hnn
  have hz : cost p θ = 0 := le_antisymm hcost h0
  rcases hstrict with hlt | ⟨s, hs⟩
  · linarith
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (hc ▸ hz)
    have := hall s (Finset.mem_univ s)
    rcases mul_eq_zero.mp this with h | h
    · exact (hm.1 s).ne' h
    · exact hs.ne' h

/-- Cochrane (2023), p. 499 (tool): the gains map `θ ↦ (−cost θ, payoff θ)` into
`ℝ^{1+S}`, the `none` coordinate holding minus the cost. -/
def gains (X : J → S → ℝ) (p : J → ℝ) : (J → ℝ) →ₗ[ℝ] (Option S → ℝ) where
  toFun θ := fun o => Option.elim o (-cost p θ) (payoff X θ)
  map_add' θ θ' := by
    funext o
    cases o <;> simp [cost, payoff, add_mul, Finset.sum_add_distrib]; ring
  map_smul' c θ := by
    funext o
    cases o <;> simp [cost, payoff, Finset.mul_sum, mul_assoc]

/-- Cochrane (2023), p. 499 (tool): the simplex of `ℝ^{1+S}`, nonnegative vectors summing to
one. -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

/-- Cochrane (2023), p. 499 (tool): the simplex is convex. -/
theorem convex_simplexSet (ι : Type*) [Fintype ι] : Convex ℝ (simplexSet ι) := by
  rintro f ⟨hf0, hf1⟩ g ⟨hg0, hg1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf0 i)) (mul_nonneg hb (hg0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf1, hg1, mul_one, hab]

/-- Cochrane (2023), p. 499 (tool): a linear functional on `ℝ^ι` is determined by its values on
the unit vectors. -/
theorem functional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ)
    (z : ι → ℝ) : f z = ∑ i, z i * f (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (z i) = z i • Pi.single (M := fun _ => ℝ) i 1 := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- Cochrane (2023), p. 499 (the discount-factor existence theorem, Harrison–Kreps /
Hansen–Richard, finite states): absent arbitrage there is a strictly positive discount factor
pricing every asset. Proof by strict separation (Hahn–Banach) of the simplex of `ℝ^{1+S}` from
the subspace of attainable (−cost, payoff) vectors. -/
theorem exists_sdf_of_noArbitrage {X : J → S → ℝ} {p : J → ℝ}
    (hna : NoArbitrage X p) : ∃ m, IsSDF X p m := by
  classical
  set L : Submodule ℝ (Option S → ℝ) := LinearMap.range (gains X p) with hL
  set K : Set (Option S → ℝ) :=
    convexHull ℝ (Set.range fun o : Option S => Pi.single (M := fun _ => ℝ) o 1) with hK
  have hKsub : K ⊆ simplexSet (Option S) := by
    refine convexHull_min ?_ (convex_simplexSet _)
    rintro _ ⟨o, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = o
      · subst h; simp
      · simp [h]
    · simp
  have hKc : IsCompact K := by
    rw [hK]; exact (Set.finite_range _).isCompact_convexHull ℝ
  have hdisj : Disjoint K (L : Set (Option S → ℝ)) := by
    rw [Set.disjoint_left]
    intro y hyK hyL
    obtain ⟨θ, rfl⟩ := hyL
    obtain ⟨hnn, hsum⟩ := hKsub hyK
    have hcost : cost p θ ≤ 0 := by
      have := hnn none; simp [gains] at this; linarith
    have hpay : ∀ s, 0 ≤ payoff X θ s := fun s => by simpa [gains] using hnn (some s)
    refine hna θ ⟨hpay, hcost, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hc0, hp0⟩ := hcon
    have hzero : ∀ o, gains X p θ o = 0 := by
      intro o
      cases o with
      | none => simp [gains]; linarith
      | some s => simp only [gains, LinearMap.coe_mk, AddHom.coe_mk, Option.elim_some]
                  exact le_antisymm (hp0 s) (hpay s)
    simp [hzero] at hsum
  obtain ⟨f, u, v, hfK, huv, hfL⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hKc L.convex
      L.closed_of_finiteDimensional hdisj
  have hfL0 : ∀ b ∈ (L : Set (Option S → ℝ)), f b = 0 := by
    intro b hb
    by_contra hne
    have hcb : ((v - 1) / f b) • b ∈ (L : Set (Option S → ℝ)) := L.smul_mem _ hb
    have := hfL _ hcb
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  have hv : v < 0 := by
    have := hfL 0 L.zero_mem
    simpa using this
  have hneg : ∀ o, f (Pi.single o 1) < 0 := fun o =>
    (hfK _ (subset_convexHull ℝ _ ⟨o, rfl⟩)).trans (huv.trans hv)
  refine ⟨fun s => f (Pi.single (some s) 1) / f (Pi.single none 1), fun s => ?_, fun j => ?_⟩
  · exact div_pos_of_neg_of_neg (hneg (some s)) (hneg none)
  · have h0 := hfL0 (gains X p (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
    have hrep := functional_eq_sum (f : (Option S → ℝ) →ₗ[ℝ] ℝ) (gains X p (Pi.single j 1))
    simp only [ContinuousLinearMap.coe_coe] at hrep
    rw [hrep, Fintype.sum_option] at h0
    have hc : cost p (Pi.single j 1) = p j := by simp [cost, Pi.single_apply]
    have hpj : ∀ s, payoff X (Pi.single j 1) s = X j s := by
      intro s; simp [payoff, Pi.single_apply]
    simp only [gains, LinearMap.coe_mk, AddHom.coe_mk, Option.elim_none, Option.elim_some,
      hc, hpj] at h0
    have hn := (hneg none).ne
    rw [Finset.sum_congr rfl fun s _ => (div_mul_eq_mul_div _ _ _).trans
      (by ring : f (Pi.single (some s) 1) * X j s / f (Pi.single none 1) =
        X j s * f (Pi.single (some s) 1) / f (Pi.single none 1)), ← Finset.sum_div]
    field_simp
    linarith

/-- Cochrane (2023), pp. 498–499 (finite-state fundamental theorem of asset pricing): there is
no arbitrage iff there is a strictly positive discount factor pricing every asset. -/
theorem ftap (X : J → S → ℝ) (p : J → ℝ) :
    NoArbitrage X p ↔ ∃ m, IsSDF X p m :=
  ⟨exists_sdf_of_noArbitrage, fun ⟨_, hm⟩ => noArbitrage_of_sdf hm⟩

omit [Fintype J] in
/-- Cochrane (2023), pp. 498–499: a discount factor in expectation form — for any full-support
probabilities `π`, `p_j = ∑_s π_s (m_s/π_s) X_j(s) = price π (m/π) X_j`, so the same prices are
"explained" by every belief `π` with a suitable positive marginal utility `m/π`. -/
theorem sdf_expectation_form {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m)
    {π : S → ℝ} (hπ : ∀ s, 0 < π s) (j : J) :
    p j = price π (fun s => m s / π s) (X j) ∧ ∀ s, 0 < m s / π s := by
  refine ⟨?_, fun s => div_pos (hm.1 s) (hπ s)⟩
  rw [hm.2 j]
  unfold price
  refine Finset.sum_congr rfl fun s _ => ?_
  have := (hπ s).ne'
  field_simp

end Cochrane.ObservationalEquivalence.AssetPricingOE

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov-switching monetary policy: the Davig–Leeper determinacy condition

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): policy-rule coefficients switch between regimes according to a Markov
process; "if an economy is currently in what looks like a passive … regime, but people expect a
switch …, then that future … policy selects equilibria"; "a time with `φ < 1` should be something
like 'locally passive' or 'temporarily passive'"), and Chapter 22, §22.3, p. 500 (Markov-switching
estimates of `φ` and `γ`).

## The frictionless model

Two regimes `S_t ∈ {0, 1}` follow a Markov chain with transition matrix `P` (`Transition`). The
frictionless model is the Fisher equation `i_t = E_t π_{t+1}` and the regime-dependent rule
`i_t = φ_{S_t} π_t + u_t`, so `E_t π_{t+1} = φ_{S_t} π_t + u_t`. With all uncertainty coming from
the regimes, a process is a function of the regime history: a node `(i, h)` is the current
regime `i` and the list `h` of past regimes (most recent first), and
`E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` (`Solves`). A solution is *bounded* if it is bounded over
all histories (`BoundedFn`). This contains every regime-dependent sunspot.

## Main results (`φ_0, φ_1 > 0`)

* `dl_iff_schur`: the Davig–Leeper "long-run Taylor principle"
  `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` together with `p_00/φ_0 + p_11/φ_1 < 2`
  (`DLCondition`) holds iff both eigenvalues of `M = Φ⁻¹P` lie in the open unit disc.
* `homog_eq_zero`: under the condition every bounded solution of the homogeneous model is zero;
  `exists_perron`, `homog_nonzero_of_not_dl`: otherwise there is a nonzero bounded solution
  `π(i, h) = w_i/r^{|h|}` (`r ≥ 1` the Perron root of `M`).
* `fwdSol_solves`, `fwdSol_bounded`: under the condition the forward solution exists and is
  bounded for every bounded disturbance `u`.
* `determinate_iff`: **the model has exactly one bounded equilibrium for every bounded
  disturbance iff the Davig–Leeper condition holds.**
* Examples: `both_active_determinate` (both regimes active), `both_passive_indeterminate`
  (both passive, `φ_i ≤ 1`), `temporarily_passive_determinate` (`φ = (2, ½)`: a passive regime
  that is expected to end is consistent with determinacy), `locally_active_indeterminate`
  (`φ = (2, ½)` with a persistent passive regime: the currently active regime does not determine
  inflation).
* `abstract_homog_eq_zero`, `abstract_homog_nonzero`: the same dichotomy for an arbitrary
  `ExpectationSystem` carrying a Markov regime process (so also excluding extraneous sunspots).
-/

namespace Cochrane.ObservationalEquivalence.MarkovRegimes

open Filter Topology Finset
open scoped Matrix

/-- Cochrane (2023), p. 522 ("switches … according to a Markov process"): the transition matrix
`P_{ij} = Pr(S_{t+1} = j | S_t = i)` of a two-state Markov chain. -/
structure Transition where
  /-- the transition probabilities -/
  P : Fin 2 → Fin 2 → ℝ
  /-- probabilities are nonnegative -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- rows sum to one -/
  rowSum : ∀ i, ∑ j, P i j = 1

/-- Cochrane (2023), p. 522: a node of the regime tree, the current regime and the list of past
regimes (most recent first). -/
abbrev Node := Fin 2 × List (Fin 2)

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov-switching `φ` (p. 522):
`E_t π_{t+1} = φ_{S_t} π_t + u_t`, where `E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` at node
`(i, h)`. -/
def Solves (T : Transition) (φ : Fin 2 → ℝ) (u π : Node → ℝ) : Prop :=
  ∀ i h, ∑ j, T.P i j * π (j, i :: h) = φ i * π (i, h) + u (i, h)

/-- Cochrane (2023), p. 500: a process bounded over all regime histories. -/
def BoundedFn (x : Node → ℝ) : Prop := ∃ B, ∀ n, |x n| ≤ B

/-- Cochrane (2023), p. 523 ("move eigenvalues from stable to unstable"): the matrix
`M = Φ⁻¹P`, `M_{ij} = P_{ij}/φ_i`, whose eigenvalues govern determinacy. -/
noncomputable def regM (T : Transition) (φ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => T.P i j / φ i

/-- Cochrane (2023), pp. 522–523 (Davig and Leeper's "long-run Taylor principle"):
`(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` and `p_00/φ_0 + p_11/φ_1 < 2`. -/
def DLCondition (T : Transition) (φ : Fin 2 → ℝ) : Prop :=
  1 < (1 - φ 1) * T.P 0 0 + (1 - φ 0) * T.P 1 1 + φ 0 * φ 1 ∧
    T.P 0 0 / φ 0 + T.P 1 1 / φ 1 < 2

/-! ### The eigenvalue condition -/

/-- Cochrane (2023), p. 523: `M` has nonnegative entries when `φ > 0`. -/
theorem regM_nonneg (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (i j : Fin 2) :
    0 ≤ regM T φ i j :=
  div_nonneg (T.nonneg i j) (hφ i).le

/-- Cochrane (2023), p. 522: the off-diagonal transition probabilities, `p_01 = 1 − p_00`. -/
theorem P01 (T : Transition) : T.P 0 1 = 1 - T.P 0 0 := by
  have := T.rowSum 0; rw [Fin.sum_univ_two] at this; linarith

/-- Cochrane (2023), p. 522: `p_10 = 1 − p_11`. -/
theorem P10 (T : Transition) : T.P 1 0 = 1 - T.P 1 1 := by
  have := T.rowSum 1; rw [Fin.sum_univ_two] at this; linarith

/-- Cochrane (2023), p. 523: the characteristic polynomial of `M` at `1`, times `φ_0φ_1`, is the
Davig–Leeper expression. -/
theorem charpoly_one_eq (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    (1 - tr2 (regM T φ) + det2 (regM T φ)) * (φ 0 * φ 1) =
      (1 - φ 1) * T.P 0 0 + (1 - φ 0) * T.P 1 1 + φ 0 * φ 1 - 1 := by
  have h0 := (hφ 0).ne'
  have h1 := (hφ 1).ne'
  simp only [tr2, det2, regM, Matrix.of_apply, P01, P10]
  field_simp
  ring

/-- Cochrane (2023), p. 523: for a `2 × 2` matrix with nonnegative entries, both eigenvalues lie
in the open unit disc iff `χ(1) = 1 − tr + det > 0` and `tr < 2`. -/
theorem schur_iff_of_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    SchurStable (tr2 A) (det2 A) ↔ 0 < 1 - tr2 A + det2 A ∧ tr2 A < 2 := by
  have hT : 0 ≤ tr2 A := add_nonneg (hA 0 0) (hA 1 1)
  have hdisc : 4 * det2 A ≤ tr2 A ^ 2 := by
    simp only [tr2, det2]
    nlinarith [sq_nonneg (A 0 0 - A 1 1), mul_nonneg (hA 0 1) (hA 1 0)]
  unfold SchurStable
  constructor
  · rintro ⟨hD, hTr⟩
    rw [abs_lt] at hD hTr
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨abs_lt.mpr ⟨by linarith, by nlinarith⟩, ?_⟩
    rw [abs_of_nonneg hT]; linarith

/-- Cochrane (2023), pp. 522–523 (Davig–Leeper): for `φ_0, φ_1 > 0`, the Davig–Leeper condition
holds iff both eigenvalues of `M = Φ⁻¹P` lie in the open unit disc. -/
theorem dl_iff_schur (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    DLCondition T φ ↔ SchurStable (tr2 (regM T φ)) (det2 (regM T φ)) := by
  rw [schur_iff_of_nonneg (regM_nonneg T hφ)]
  have key := charpoly_one_eq T hφ
  have hpos : 0 < φ 0 * φ 1 := mul_pos (hφ 0) (hφ 1)
  have htr : tr2 (regM T φ) = T.P 0 0 / φ 0 + T.P 1 1 / φ 1 := by
    simp [tr2, regM]
  unfold DLCondition
  rw [htr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra hcon
    push Not at hcon
    rw [← htr] at h2
    nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← htr] at h2
    nlinarith

/-! ### Uniqueness under the condition -/

/-- Cochrane (2023), p. 523: entries of `M^{k+1}` through `M^k`. -/
theorem pow_succ_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (i l : Fin 2) :
    (A ^ (k + 1)) i l = A i 0 * (A ^ k) 0 l + A i 1 * (A ^ k) 1 l := by
  rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]

/-- Cochrane (2023), p. 523 (iterating the expectational recursion): a bounded solution of the
homogeneous model satisfies `|π(i, h)| ≤ B ∑_j (M^k)_{ij}` for every `k`. -/
theorem abs_le_pow_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {e : Node → ℝ}
    (he : Solves T φ 0 e) {B : ℝ} (hB : ∀ n, |e n| ≤ B) (k : ℕ) :
    ∀ i h, |e (i, h)| ≤ B * ∑ j, (regM T φ ^ k) i j := by
  induction k with
  | zero =>
    intro i h
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB _
  | succ k ih =>
    intro i h
    have hφi := hφ i
    have heq : φ i * e (i, h) = ∑ j, T.P i j * e (j, i :: h) := by
      have := he i h; simp only [Pi.zero_apply, add_zero] at this; linarith
    have habs : φ i * |e (i, h)| ≤ ∑ j, T.P i j * |e (j, i :: h)| := by
      rw [← abs_of_pos hφi, ← abs_mul, heq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
    have hstep : ∑ j, T.P i j * |e (j, i :: h)| ≤
        ∑ j, T.P i j * (B * ∑ l, (regM T φ ^ k) j l) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
    have hval : ∑ j, T.P i j * (B * ∑ l, (regM T φ ^ k) j l) =
        φ i * (B * ∑ l, (regM T φ ^ (k + 1)) i l) := by
      simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    have := habs.trans (hstep.trans (le_of_eq hval))
    exact le_of_mul_le_mul_left this hφi

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the homogeneous model has no
bounded solution other than zero. -/
theorem homog_eq_zero (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {e : Node → ℝ} (he : Solves T φ 0 e) (hb : BoundedFn e) :
    e = 0 := by
  obtain ⟨B, hB⟩ := hb
  have hS := (dl_iff_schur T hφ).mp hdl
  funext n
  obtain ⟨i, h⟩ := n
  have hlim : Tendsto (fun k => B * ∑ j, (regM T φ ^ k) i j) atTop (𝓝 0) := by
    have h0 := tendsto_pow_entry hS i 0
    have h1 := tendsto_pow_entry hS i 1
    simpa [Fin.sum_univ_two] using (h0.add h1).const_mul B
  have hle : |e (i, h)| ≤ 0 :=
    ge_of_tendsto' hlim fun k => abs_le_pow_bound T hφ he hB k i h
  simpa using abs_nonpos_iff.mp hle

/-! ### Non-uniqueness when the condition fails -/

/-- Cochrane (2023), p. 523 (tool): `(Aw)_i = A_{i0} w_0 + A_{i1} w_1`. -/
theorem mulVec_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (i : Fin 2) :
    (A *ᵥ w) i = A i 0 * w 0 + A i 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Cochrane (2023), p. 523 (Perron–Frobenius for `2 × 2` nonnegative matrices): if the
eigenvalues of a nonnegative `A` are not both in the open unit disc, `A` has an eigenvalue
`r ≥ 1` with a nonzero nonnegative eigenvector. -/
theorem exists_perron {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hns : ¬ SchurStable (tr2 A) (det2 A)) :
    ∃ (r : ℝ) (w : Fin 2 → ℝ), 1 ≤ r ∧ (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧ A *ᵥ w = r • w := by
  rw [schur_iff_of_nonneg hA] at hns
  have hcase : 1 - tr2 A + det2 A ≤ 0 ∨ 2 ≤ tr2 A := by
    by_contra hcon
    push Not at hcon
    exact hns hcon
  simp only [tr2, det2] at hcase
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have ha := hA 0 0
  have hb := hA 0 1
  have hc := hA 1 0
  have hd := hA 1 1
  rcases hb.lt_or_eq with hbpos | hb0
  · -- `b > 0`: the Perron root `r = (a + d + √disc)/2` with eigenvector `(b, r − a)`
    set s := Real.sqrt ((a - d) ^ 2 + 4 * b * c) with hs
    have hdisc : 0 ≤ (a - d) ^ 2 + 4 * b * c := by positivity
    have hs2 : s ^ 2 = (a - d) ^ 2 + 4 * b * c := Real.sq_sqrt hdisc
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsad : |a - d| ≤ s := by
      rw [hs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    set r := (a + d + s) / 2 with hr
    have hra : 0 ≤ r - a := by
      have := (abs_le.mp hsad).2; rw [hr]; linarith
    have hr1 : 1 ≤ r := by
      rcases hcase with h1 | h2
      · by_contra hlt
        push Not at hlt
        have hr1' : (a + d - s) / 2 ≤ r := by rw [hr]; linarith
        have hprod : 1 - (a + d) + (a * d - b * c) = (1 - (a + d - s) / 2) * (1 - r) := by
          rw [hr]; nlinarith
        have : 0 < (1 - (a + d - s) / 2) * (1 - r) :=
          mul_pos (by linarith) (by linarith)
        linarith
      · rw [hr]; linarith
    refine ⟨r, ![b, r - a], hr1, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hb
      · simpa using hra
    · intro h
      have := congrFun h 0
      simp only [Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply] at this
      exact hbpos.ne' this
    · funext i
      fin_cases i
      · rw [mulVec_fin_two]
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
        change a * b + b * (r - a) = r * b
        ring
      · rw [mulVec_fin_two]
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, smul_eq_mul]
        change c * b + d * (r - a) = r * (r - a)
        have : r ^ 2 - (a + d) * r + (a * d - b * c) = 0 := by rw [hr]; nlinarith
        nlinarith
  · -- `b = 0`: lower triangular
    have hb0' : b = 0 := hb0.symm
    rw [hb0'] at hcase
    by_cases hd1 : 1 ≤ d
    · refine ⟨d, ![0, 1], hd1, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp
      · intro h
        have := congrFun h 1
        simp at this
      · funext i
        fin_cases i
        · rw [mulVec_fin_two]
          simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul,
            mul_zero]
          change 0 + b * 1 = 0
          rw [hb0']; ring
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          rfl
    · push Not at hd1
      have ha1 : 1 ≤ a := by
        rcases hcase with h1 | h2
        · by_contra hlt
          push Not at hlt
          nlinarith
        · linarith
      refine ⟨a, ![a - d, c], ha1, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> linarith
      · intro h
        have := congrFun h 0
        simp at this
        linarith
      · funext i
        fin_cases i
        · rw [mulVec_fin_two]
          simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
          change a * (a - d) + b * c = a * (a - d)
          rw [hb0']; ring
        · rw [mulVec_fin_two]
          simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, smul_eq_mul]
          change c * (a - d) + d * c = a * c
          ring

/-- Cochrane (2023), pp. 522–523: if the Davig–Leeper condition fails, the homogeneous model has
a nonzero bounded solution `π(i, h) = w_i/r^{|h|}` — inflation is not determined. -/
theorem homog_nonzero_of_not_dl (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hndl : ¬ DLCondition T φ) : ∃ e : Node → ℝ, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0 := by
  rw [dl_iff_schur T hφ] at hndl
  obtain ⟨r, w, hr1, hw0, hwne, hMw⟩ := exists_perron (regM_nonneg T hφ) hndl
  have hr0 : 0 < r := by linarith
  refine ⟨fun n => w n.1 / r ^ n.2.length, ?_, ?_, ?_⟩
  · intro i h
    have hrow := congrFun hMw i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, regM, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] at hrow
    have hφi := (hφ i).ne'
    have hrow' : T.P i 0 * w 0 + T.P i 1 * w 1 = φ i * (r * w i) := by
      field_simp at hrow; linarith
    have hpow : r ^ (h.length + 1) = r ^ h.length * r := pow_succ r h.length
    have hrl := (pow_pos hr0 h.length).ne'
    have hr0' := hr0.ne'
    have key : T.P i 0 * (w 0 / r ^ (h.length + 1)) + T.P i 1 * (w 1 / r ^ (h.length + 1)) =
        φ i * (w i / r ^ h.length) := by
      rw [hpow, show T.P i 0 * (w 0 / (r ^ h.length * r)) + T.P i 1 * (w 1 / (r ^ h.length * r))
        = (T.P i 0 * w 0 + T.P i 1 * w 1) / (r ^ h.length * r) by ring, hrow']
      field_simp
    simpa [Fin.sum_univ_two] using key
  · refine ⟨|w 0| + |w 1|, fun n => ?_⟩
    have hge : 1 ≤ r ^ n.2.length := one_le_pow₀ hr1
    rw [abs_div, abs_of_pos (pow_pos hr0 _)]
    have hwn : ∀ i : Fin 2, |w i| ≤ |w 0| + |w 1| := by
      intro i; fin_cases i <;> simp [abs_nonneg]
    exact (div_le_self (abs_nonneg _) hge).trans (hwn _)
  · intro h
    apply hwne
    funext i
    have := congrFun h (i, [])
    simpa using this

/-! ### Existence: the forward solution -/

/-- Cochrane (2023), p. 523: the matrix powers of a Schur-stable `2 × 2` matrix are absolutely
summable entry by entry. -/
theorem summable_pow_entry_of_schur {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 A) (det2 A)) (i j : Fin 2) : Summable (fun k => |(A ^ k) i j|) := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  set ρ := max ‖root₁ (tr2 A) (det2 A)‖ ‖root₂ (tr2 A) (det2 A)‖ with hρ
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  have hgeo : Summable (fun k : ℕ => ((k : ℝ) + 1) * ρ ^ k) := by
    have ha := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1)
    have hb := summable_geometric_of_lt_one hρ0 hρ1
    simpa [add_mul] using ha.add hb
  have hg : Summable (fun k : ℕ => ((k + 1 : ℕ) + 1 : ℝ) * ρ ^ (k + 1) * |A i j| +
      |det2 A| * (((k : ℝ) + 1) * ρ ^ k)) := by
    refine Summable.add ?_ (hgeo.mul_left _)
    have := (summable_nat_add_iff 1).mpr hgeo
    exact this.mul_right _
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hg
  refine (abs_pow_entry_le A k i j).trans ?_
  have hc1 := abs_chSeq_le (tr2 A) (det2 A) (k + 1)
  have hc0 := abs_chSeq_le (tr2 A) (det2 A) k
  push_cast at hc1 hc0 ⊢
  gcongr

/-- Cochrane (2023), p. 523 (the forward solution): the terms
`Δ_0 = −u/φ`, `Δ_{k+1}(i, h) = ∑_j P_{ij} Δ_k(j, i :: h)/φ_i`. -/
noncomputable def fwdTerm (T : Transition) (φ : Fin 2 → ℝ) (u : Node → ℝ) : ℕ → Node → ℝ
  | 0, n => -u n / φ n.1
  | k + 1, n => (∑ j, T.P n.1 j * fwdTerm T φ u k (j, n.1 :: n.2)) / φ n.1

/-- Cochrane (2023), p. 523: the forward solution `π = ∑_k Δ_k`. -/
noncomputable def fwdSol (T : Transition) (φ : Fin 2 → ℝ) (u : Node → ℝ) (n : Node) : ℝ :=
  ∑' k, fwdTerm T φ u k n

/-- Cochrane (2023), p. 523: `|Δ_k(i, h)| ≤ U ∑_l (M^k)_{il}/φ_l`. -/
theorem fwdTerm_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {u : Node → ℝ}
    {U : ℝ} (hU : ∀ n, |u n| ≤ U) (k : ℕ) :
    ∀ i h, |fwdTerm T φ u k (i, h)| ≤ U * ∑ l, (regM T φ ^ k) i l / φ l := by
  induction k with
  | zero =>
    intro i h
    simp only [fwdTerm, pow_zero, Matrix.one_apply, ite_div, zero_div, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rw [abs_div, abs_neg, abs_of_pos (hφ i), mul_one_div]
    exact div_le_div_of_nonneg_right (hU _) (hφ i).le
  | succ k ih =>
    intro i h
    have hφi := hφ i
    simp only [fwdTerm]
    rw [abs_div, abs_of_pos hφi, div_le_iff₀ hφi]
    calc |∑ j, T.P i j * fwdTerm T φ u k (j, i :: h)|
        ≤ ∑ j, T.P i j * |fwdTerm T φ u k (j, i :: h)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
      _ ≤ ∑ j, T.P i j * (U * ∑ l, (regM T φ ^ k) j l / φ l) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
      _ = (U * ∑ l, (regM T φ ^ (k + 1)) i l / φ l) * φ i := by
          simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
          have h0 := (hφ 0).ne'
          have h1 := (hφ 1).ne'
          field_simp
          ring

/-- Cochrane (2023), p. 523: the dominating sequence for the forward solution is summable under
the Davig–Leeper condition. -/
theorem summable_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) (U : ℝ) (i : Fin 2) :
    Summable (fun k => U * ∑ l, (regM T φ ^ k) i l / φ l) := by
  have hS := (dl_iff_schur T hφ).mp hdl
  refine Summable.mul_left U ?_
  simp only [Fin.sum_univ_two]
  refine Summable.add ?_ ?_
  · exact ((summable_pow_entry_of_schur hS i 0).of_abs).div_const _
  · exact ((summable_pow_entry_of_schur hS i 1).of_abs).div_const _

/-- Cochrane (2023), p. 523: the forward-solution terms are summable at every node. -/
theorem fwdTerm_summable (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) (n : Node) :
    Summable (fun k => fwdTerm T φ u k n) := by
  obtain ⟨i, h⟩ := n
  exact Summable.of_norm_bounded (summable_bound T hφ hdl U i) fun k => by
    rw [Real.norm_eq_abs]; exact fwdTerm_bound T hφ hU k i h

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the forward solution solves
the model `E_t π_{t+1} = φ_{S_t} π_t + u_t`. -/
theorem fwdSol_solves (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) :
    Solves T φ u (fwdSol T φ u) := by
  intro i h
  have hs := fun n => fwdTerm_summable T hφ hdl hU n
  have hφi := (hφ i).ne'
  have hsplit := (hs (i, h)).tsum_eq_zero_add
  have hsucc : ∀ k, fwdTerm T φ u (k + 1) (i, h) =
      (T.P i 0 * fwdTerm T φ u k (0, i :: h) + T.P i 1 * fwdTerm T φ u k (1, i :: h)) / φ i := by
    intro k; simp [fwdTerm, Fin.sum_univ_two]
  have hA : ∑ j, T.P i j * fwdSol T φ u (j, i :: h) =
      ∑' k, (T.P i 0 * fwdTerm T φ u k (0, i :: h) + T.P i 1 * fwdTerm T φ u k (1, i :: h)) := by
    simp only [fwdSol, Fin.sum_univ_two]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hs _).mul_left _)
      ((hs _).mul_left _)]
  have hB : fwdSol T φ u (i, h) = -u (i, h) / φ i +
      (∑' k, (T.P i 0 * fwdTerm T φ u k (0, i :: h) +
        T.P i 1 * fwdTerm T φ u k (1, i :: h))) / φ i := by
    unfold fwdSol
    rw [hsplit]
    simp only [hsucc]
    rw [tsum_div_const]
    rfl
  rw [hA, hB]
  field_simp
  ring

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the forward solution is
bounded. -/
theorem fwdSol_bounded (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) :
    BoundedFn (fwdSol T φ u) := by
  set g : Fin 2 → ℝ := fun i => ∑' k, U * ∑ l, (regM T φ ^ k) i l / φ l with hg
  refine ⟨|g 0| + |g 1|, fun n => ?_⟩
  obtain ⟨i, h⟩ := n
  have h1 : |fwdSol T φ u (i, h)| ≤ g i := by
    unfold fwdSol
    have hsa : Summable (fun k => |fwdTerm T φ u k (i, h)|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => fwdTerm_bound T hφ hU k i h)
        (summable_bound T hφ hdl U i)
    have hn := norm_tsum_le_tsum_norm (f := fun k => fwdTerm T φ u k (i, h))
      (by simpa only [Real.norm_eq_abs] using hsa)
    simp only [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    exact Summable.tsum_le_tsum (fun k => fwdTerm_bound T hφ hU k i h) hsa
      (summable_bound T hφ hdl U i)
  have h2 : g i ≤ |g 0| + |g 1| := by
    fin_cases i
    · simp only [Fin.zero_eta]; linarith [le_abs_self (g 0), abs_nonneg (g 1)]
    · simp only [Fin.mk_one]; linarith [le_abs_self (g 1), abs_nonneg (g 0)]
  exact h1.trans h2

/-- Cochrane (2023), pp. 522–523: the difference of two solutions solves the homogeneous
model. -/
theorem solves_sub (T : Transition) (φ : Fin 2 → ℝ) {u π₁ π₂ : Node → ℝ}
    (h₁ : Solves T φ u π₁) (h₂ : Solves T φ u π₂) : Solves T φ 0 (π₁ - π₂) := by
  intro i h
  have e1 := h₁ i h
  have e2 := h₂ i h
  simp only [Pi.sub_apply, Pi.zero_apply, Fin.sum_univ_two] at e1 e2 ⊢
  linarith

/-- Cochrane (2023), pp. 522–523 (Davig and Leeper's determinacy condition): for `φ_0, φ_1 > 0`
the frictionless Markov-switching model has exactly one bounded equilibrium for every bounded
disturbance iff `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` and `p_00/φ_0 + p_11/φ_1 < 2`. -/
theorem determinate_iff (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    (∀ u, BoundedFn u → ∃! π, Solves T φ u π ∧ BoundedFn π) ↔ DLCondition T φ := by
  constructor
  · intro h
    by_contra hndl
    obtain ⟨e, he, heb, hne⟩ := homog_nonzero_of_not_dl T hφ hndl
    obtain ⟨π, _, huniq⟩ := h 0 ⟨0, fun n => by simp⟩
    have h0 : (0 : Node → ℝ) = π := huniq 0 ⟨fun i h => by simp, ⟨0, fun n => by simp⟩⟩
    have he' : e = π := huniq e ⟨he, heb⟩
    exact hne (he'.trans h0.symm)
  · intro hdl u ⟨U, hU⟩
    refine ⟨fwdSol T φ u, ⟨fwdSol_solves T hφ hdl hU, fwdSol_bounded T hφ hdl hU⟩, ?_⟩
    rintro π ⟨hπ, hπb⟩
    have hd := solves_sub T φ hπ (fwdSol_solves T hφ hdl hU)
    obtain ⟨B1, hB1⟩ := hπb
    obtain ⟨B2, hB2⟩ := fwdSol_bounded T hφ hdl hU
    have hzero := homog_eq_zero T hφ hdl hd ⟨B1 + B2, fun n => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hB1 n) (hB2 n))⟩
    exact sub_eq_zero.mp hzero

/-! ### Examples -/

/-- Cochrane (2023), p. 523: if both regimes are active (`φ_i > 1`) the Davig–Leeper condition
holds. -/
theorem both_active_determinate (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 1 < φ i) :
    DLCondition T φ := by
  have h00 : T.P 0 0 ≤ 1 := by have := P01 T; linarith [T.nonneg 0 1]
  have h11 : T.P 1 1 ≤ 1 := by have := P10 T; linarith [T.nonneg 1 0]
  have hn0 := T.nonneg 0 0
  have hn1 := T.nonneg 1 1
  have hφ0 := hφ 0
  have hφ1 := hφ 1
  refine ⟨by nlinarith, ?_⟩
  have e0 : T.P 0 0 / φ 0 < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have e1 : T.P 1 1 / φ 1 < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- Cochrane (2023), p. 523: if both regimes are passive (`0 < φ_i ≤ 1`) the Davig–Leeper
condition fails: inflation is indeterminate. -/
theorem both_passive_indeterminate (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hφ1 : ∀ i, φ i ≤ 1) : ¬ DLCondition T φ := by
  intro hdl
  have hS := (dl_iff_schur T hφ).mp hdl
  have hrow : ∀ k i, 1 ≤ ∑ j, (regM T φ ^ k) i j := by
    intro k
    induction k with
    | zero => intro i; simp [Matrix.one_apply]
    | succ k ih =>
      intro i
      have hM0 := regM_nonneg T hφ i 0
      have hM1 := regM_nonneg T hφ i 1
      have hsum : 1 ≤ regM T φ i 0 + regM T φ i 1 := by
        simp only [regM, Matrix.of_apply]
        rw [← add_div, ← Fin.sum_univ_two (fun j => T.P i j), T.rowSum i,
          le_div_iff₀ (hφ i), one_mul]
        exact hφ1 i
      simp only [Fin.sum_univ_two, pow_succ_apply] at ih ⊢
      nlinarith [ih 0, ih 1]
  have hlim : Tendsto (fun k => ∑ j, (regM T φ ^ k) 0 j) atTop (𝓝 0) := by
    simpa [Fin.sum_univ_two] using
      (tendsto_pow_entry hS 0 0).add (tendsto_pow_entry hS 0 1)
  have := ge_of_tendsto' hlim fun k => hrow k 0
  linarith

/-- Cochrane (2023), p. 523 (example): an absorbing-free chain with `p_00 = 0.9`, `p_11 = 0.4`. -/
noncomputable def egShortPassive : Transition where
  P := ![![9 / 10, 1 / 10], ![6 / 10, 4 / 10]]
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  rowSum := by intro i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Cochrane (2023), p. 523 (example): a chain with a persistent passive regime,
`p_00 = p_11 = 0.9`. -/
noncomputable def egLongPassive : Transition where
  P := ![![9 / 10, 1 / 10], ![1 / 10, 9 / 10]]
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  rowSum := by intro i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Cochrane (2023), p. 523 ("A time with `φ < 1` should be something like … 'temporarily
passive'"): with `φ = (2, ½)` and a short-lived passive regime the equilibrium is determinate,
although regime `1` is passive. -/
theorem temporarily_passive_determinate : DLCondition egShortPassive ![2, 1 / 2] := by
  simp only [DLCondition, egShortPassive]
  norm_num

/-- Cochrane (2023), pp. 522–523: with `φ = (2, ½)` and a persistent passive regime the
equilibrium is indeterminate, although regime `0` is active — the expected future passive
regime undoes the current active one. -/
theorem locally_active_indeterminate : ¬ DLCondition egLongPassive ![2, 1 / 2] := by
  simp only [DLCondition, egLongPassive]
  norm_num

/-! ### The same dichotomy for an arbitrary expectation system -/

variable {Ω : Type*}

variable (𝔼₀ : ExpectationSystem Ω) (T₀ : Transition)

/-- Cochrane (2023), p. 522: a Markov regime process `S_t` in an expectation system — adapted,
and `E_t f(S_{t+1}) = ∑_j P_{S_t, j} f(j)`. -/
structure MarkovRegime where
  /-- the regime process -/
  S : ℕ → Ω → Fin 2
  /-- the Markov property -/
  markov : ∀ t (f : Fin 2 → ℝ), 𝔼₀.E t (f ∘ S (t + 1)) = fun ω => ∑ j, T₀.P (S t ω) j * f j

/-- Cochrane (2023), pp. 522–523: in any expectation system with a Markov regime process, a
bounded solution of `E_t π_{t+1} = φ_{S_t} π_t` (possibly driven by extraneous sunspots)
satisfies `|π_t| ≤ B ∑_j (M^k)_{S_t, j}` for every `k`. -/
theorem abstract_bound {𝔼 : ExpectationSystem Ω} {T : Transition} (R : MarkovRegime 𝔼 T)
    {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {e : ℕ → Ω → ℝ}
    (he : ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) {B : ℝ}
    (hB : ∀ t ω, |e t ω| ≤ B) (k : ℕ) :
    ∀ t ω, |e t ω| ≤ B * ∑ j, (regM T φ ^ k) (R.S t ω) j := by
  induction k with
  | zero =>
    intro t ω
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB t ω
  | succ k ih =>
    intro t ω
    set f : Fin 2 → ℝ := fun l => B * ∑ j, (regM T φ ^ k) l j with hf
    have hφi := hφ (R.S t ω)
    have hup : e (t + 1) ≤ f ∘ R.S (t + 1) :=
      fun ω' => (le_abs_self _).trans (ih (t + 1) ω')
    have hlo : -(f ∘ R.S (t + 1)) ≤ e (t + 1) :=
      fun ω' => by
        have := ih (t + 1) ω'; have := neg_abs_le (e (t + 1) ω')
        simp only [Pi.neg_apply, Function.comp_apply]; linarith
    have h1 := 𝔼.mono t hup ω
    have h2 := 𝔼.mono t hlo ω
    rw [map_neg, R.markov t f] at h2
    rw [R.markov t f] at h1
    beta_reduce at h1
    have hE : 𝔼.E t (e (t + 1)) ω = φ (R.S t ω) * e t ω := congrFun (he t) ω
    have hval : ∑ j, T.P (R.S t ω) j * f j =
        φ (R.S t ω) * (B * ∑ j, (regM T φ ^ (k + 1)) (R.S t ω) j) := by
      simp only [hf, pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    simp only [Pi.neg_apply] at h2
    rw [hE, hval] at h1 h2
    have habs : φ (R.S t ω) * |e t ω| ≤
        φ (R.S t ω) * (B * ∑ j, (regM T φ ^ (k + 1)) (R.S t ω) j) := by
      rw [← abs_of_pos hφi, ← abs_mul, abs_le]
      rw [abs_of_pos hφi]
      exact ⟨by linarith, h1⟩
    exact le_of_mul_le_mul_left habs hφi

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition, in any expectation system with
a Markov regime process, the only bounded solution of the homogeneous model is zero (no
regime-dependent or extraneous sunspots survive). -/
theorem abstract_homog_eq_zero {𝔼 : ExpectationSystem Ω} {T : Transition}
    (R : MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (hdl : DLCondition T φ)
    {e : ℕ → Ω → ℝ} (he : ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω)
    (hb : BoundedProc e) : e = 0 := by
  obtain ⟨B, hB⟩ := hb
  have hS := (dl_iff_schur T hφ).mp hdl
  funext t ω
  have hlim : Tendsto (fun k => B * ∑ j, (regM T φ ^ k) (R.S t ω) j) atTop (𝓝 0) := by
    have h0 := tendsto_pow_entry hS (R.S t ω) 0
    have h1 := tendsto_pow_entry hS (R.S t ω) 1
    simpa [Fin.sum_univ_two] using (h0.add h1).const_mul B
  have hle : |e t ω| ≤ 0 :=
    ge_of_tendsto' hlim fun k => abstract_bound R hφ he hB k t ω
  simpa using abs_nonpos_iff.mp hle

/-- Cochrane (2023), pp. 522–523: if the Davig–Leeper condition fails and both regimes are
possible at date `0`, then in any expectation system with a Markov regime process the
homogeneous model has a nonzero bounded solution `π_t = w_{S_t}/r^t`. -/
theorem abstract_homog_nonzero {𝔼 : ExpectationSystem Ω} {T : Transition}
    (R : MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (hndl : ¬ DLCondition T φ)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    ∃ e : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) ∧
      BoundedProc e ∧ e ≠ 0 := by
  rw [dl_iff_schur T hφ] at hndl
  obtain ⟨r, w, hr1, hw0, hwne, hMw⟩ := exists_perron (regM_nonneg T hφ) hndl
  have hr0 : 0 < r := by linarith
  refine ⟨fun t ω => w (R.S t ω) / r ^ t, ?_, ?_, ?_⟩
  · intro t
    have hm : 𝔼.E t (fun ω => w (R.S (t + 1) ω) / r ^ (t + 1)) =
        fun ω => ∑ j, T.P (R.S t ω) j * (w j / r ^ (t + 1)) :=
      R.markov t (fun l => w l / r ^ (t + 1))
    rw [hm]
    funext ω
    set i := R.S t ω
    have hrow := congrFun hMw i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, regM, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] at hrow
    have hφi := (hφ i).ne'
    have hrow' : T.P i 0 * w 0 + T.P i 1 * w 1 = φ i * (r * w i) := by
      field_simp at hrow; linarith
    have hrl := (pow_pos hr0 t).ne'
    have hr0' := hr0.ne'
    have key : T.P i 0 * (w 0 / r ^ (t + 1)) + T.P i 1 * (w 1 / r ^ (t + 1)) =
        φ i * (w i / r ^ t) := by
      rw [pow_succ, show T.P i 0 * (w 0 / (r ^ t * r)) + T.P i 1 * (w 1 / (r ^ t * r))
        = (T.P i 0 * w 0 + T.P i 1 * w 1) / (r ^ t * r) by ring, hrow']
      field_simp
    simpa [Fin.sum_univ_two] using key
  · refine ⟨|w 0| + |w 1|, fun t ω => ?_⟩
    have hge : 1 ≤ r ^ t := one_le_pow₀ hr1
    rw [abs_div, abs_of_pos (pow_pos hr0 _)]
    have hwn : ∀ i : Fin 2, |w i| ≤ |w 0| + |w 1| := by
      intro i; fin_cases i <;> simp [abs_nonneg]
    exact (div_le_self (abs_nonneg _) hge).trans (hwn _)
  · intro h
    apply hwne
    funext i
    obtain ⟨ω, hω⟩ := hS0 i
    have := congrFun (congrFun h 0) ω
    simpa [hω] using this

end Cochrane.ObservationalEquivalence.MarkovRegimes

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the two chains of the observational-equivalence project

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §§22.1–22.3 and 22.7,
pp. 495–509; Chapter 24, §24.2, pp. 522–523; Online Appendix Chapter 2, §2.3, p. 606.

Chain A (the frictionless linear model, regimes and observational equivalence) and chain B
(regressions, Granger causality, present-value identities, discount factors, Markov switching)
formalised overlapping book objects. This module proves that they agree.

* Full information and present values: `perfectForesight_eq_fullInfo`, `pvExPost_eq_pv`,
  `valueOfDebt_eq_valuation` (chain B's value of debt is chain A's valuation equation).
* The valuation formula for unexpected inflation (p. 495) from the ex-post present-value
  identity of Online Appendix §2.3 (p. 606): `unexpected_inflation_of_identity` — no
  transversality hypothesis beyond bounded debt, and agreeing with `unexpected_inflation_news`.
* The discount-factor valuation (p. 499) in the money model of §22.1 (p. 496):
  `sdf_of_const_step`, `moneyEqm_debtFlow`, `moneyEqm_sdfStep`, `moneyEqm_sdf_valuation`.
* The s-shaped surplus of p. 502 is exogenous and has zero present value, yet gives a positive
  regression coefficient of surpluses on debt (p. 501, Theorem RG): `sshape_summable`,
  `sshape_regression_pos`.
* The equilibrium criterion (§22.7, p. 508; Woodford (2003), Prop. 4.11, pp. 311–314):
  `uniqueB_iff_not_ricardian`, `ricardian_passive_not_unique`.
* Markov switching with a constant regime (pp. 522–523) is the Taylor principle:
  `dl_const_iff`, `markov_const_determinate_iff`, `markov_const_iff_starred_determinate`,
  `markov_const_iff_forward`.
* OE-2 and OE-1 (pp. 495–497): `moneyOutcome`, `moneyOutcome_consistent`,
  `moneyOutcome_admissible`, `oe2_oe1`.
* Geometric decay (p. 523; Online Appendix p. 605): `powDecay_of_schur` (a Schur-stable `2 × 2`
  matrix has geometrically decaying powers, chain B's `PowDecay`).
-/

namespace Cochrane.ObservationalEquivalence.Links

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply fullInfo pvExPost
  tendsto_pow_mul_of_bounded)

variable {Ω : Type*}

/-! ### Full information and present values -/

/-- Cochrane (2023), §22.7, p. 508: the core perfect-foresight system is full information on
the one-point state space. -/
theorem perfectForesight_eq_fullInfo : perfectForesight = fullInfo Unit := rfl

/-- Cochrane (2023), §22.1, pp. 495–496: the ex-post present value of the linear model is, state
by state, the money model's present value `∑ βʲ s_{t+j}` started one period later. -/
theorem pvExPost_eq_pv (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pvExPost ρ s t ω = MoneyRegimes.pv ρ (fun k => s k ω) (t + 1) := rfl

/-- Cochrane (2023), p. 501 and Online Appendix (2.22), p. 602: in the frictionless model
(Fisher equation, flow condition, transversality condition, bounded surpluses), the value of debt
is chain B's `valueOfDebt`, the expected discounted surplus stream. -/
theorem valueOfDebt_eq_valuation (𝔼 : ExpectationSystem Ω) {ρ M : ℝ} (hρ : |ρ| < 1)
    {v i π s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hF : Valuation.Fisher 𝔼 i π)
    (h : Valuation.Flow ρ v i π s) (hv : 𝔼.Adapted v) (htvc : Valuation.TVC 𝔼 ρ v) (t : ℕ) :
    v t = SurplusRegression.valueOfDebt 𝔼 ρ s t :=
  Valuation.valuation_E_exPost 𝔼 hρ hs hF h hv htvc t

/-! ### Unexpected inflation from the ex-post identity -/

/-- Cochrane (2023), §22.1, p. 495, from Online Appendix §2.3, p. 606 ("It always holds ex-post,
so it always holds ex-ante"): in the frictionless model with bounded adapted `v`, `i`, `π` and
bounded surpluses, the ex-post identity `ΔE_{t+1} ∑ ρʲ s_{t+1+j} = ΔE_{t+1} ∑ ρʲ r_{t+1+j}`
(`PresentValueIdentity.as_eq_ar_innov`, with the ex-post real return `r_{t+1} = i_t − π_{t+1}`)
gives the valuation formula for unexpected inflation, `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s_{t+1+j}`
(`Valuation.unexpected_inflation_news`) — with no transversality hypothesis beyond bounded debt,
and without assuming the surplus adapted. -/
theorem unexpected_inflation_of_identity (𝔼 : ExpectationSystem Ω) {ρ Mv Mi Mπ Ms : ℝ}
    (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ Mv)
    (hi : ∀ t ω, |i t ω| ≤ Mi) (hπ : ∀ t ω, |π t ω| ≤ Mπ) (hs : ∀ t ω, |s t ω| ≤ Ms)
    (hva : 𝔼.Adapted v) (hia : 𝔼.Adapted i) (hπa : 𝔼.Adapted π) (hF : Valuation.Fisher 𝔼 i π)
    (h : Valuation.Flow ρ v i π s) (t : ℕ) :
    Valuation.surprise 𝔼 π t = -innov 𝔼 t (pvExPost ρ s t) := by
  set r : ℕ → Ω → ℝ := fun k => Valuation.realReturn i π (k - 1) with hr
  have hrb : ∀ k ω, |r k ω| ≤ Mi + Mπ := fun k ω => by
    simp only [hr, Valuation.realReturn, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hi _ ω) (hπ _ ω))
  have hflow : ∀ k, ρ • v (k + 1) = v k + r (k + 1) - s (k + 1) := fun k => by
    simp only [hr, Nat.add_sub_cancel, Valuation.realReturn]
    rw [h k]
    abel
  have hid := PresentValueIdentity.as_eq_ar_innov 𝔼 hρ hv hrb hs hflow hva t
  have hE0 : 𝔼.E t (pvExPost ρ r t) = 0 := by
    rw [Valuation.E_pvExPost 𝔼 hρ hrb]
    funext ω
    simp only [Valuation.pvE, Pi.zero_apply]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    change ρ ^ j * 𝔼.E t (Valuation.realReturn i π (t + 1 + j - 1)) ω = 0
    rw [show t + 1 + j - 1 = t + j by omega, Valuation.E_realReturn 𝔼 hF t j, Pi.zero_apply,
      mul_zero]
  have hE1 : 𝔼.E (t + 1) (pvExPost ρ r t) = i t - π (t + 1) := by
    rw [Valuation.E_pvExPost 𝔼 hρ hrb]
    funext ω
    simp only [Valuation.pvE]
    rw [tsum_eq_single 0 fun j hj => ?_]
    · change ρ ^ 0 * 𝔼.E (t + 1) (Valuation.realReturn i π (t + 1 + 0 - 1)) ω =
        (i t - π (t + 1)) ω
      rw [show t + 1 + 0 - 1 = t by omega, Valuation.realReturn, map_sub,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hia t), hπa (t + 1), pow_zero, one_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      change ρ ^ (k + 1) * 𝔼.E (t + 1) (Valuation.realReturn i π (t + 1 + (k + 1) - 1)) ω = 0
      rw [show t + 1 + (k + 1) - 1 = t + 1 + k by omega, Valuation.E_realReturn 𝔼 hF (t + 1) k,
        Pi.zero_apply, mul_zero]
  have hinn : innov 𝔼 t (pvExPost ρ r t) = -Valuation.surprise 𝔼 π t := by
    rw [innov_apply, hE1, hE0, sub_zero, Valuation.surprise, hF t]
    abel
  rw [hid, hinn, neg_neg]

/-! ### The discount factor in the money model -/

/-- Cochrane (2023), p. 499: with a constant one-period discount factor `Λ_{t+1}/Λ_t = β`, the
ex-post discount factor is `Λ_t = βᵗ`. -/
theorem sdf_of_const_step {P Q : ℕ → ℝ} {β : ℝ}
    (h : ∀ t, PresentValueIdentity.sdfStep P Q t = β) (t : ℕ) :
    PresentValueIdentity.sdf P Q t = β ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change PresentValueIdentity.sdf P Q t * PresentValueIdentity.sdfStep P Q t = β ^ (t + 1)
    rw [ih, h t, pow_succ]

/-- Cochrane (2023), §22.1, p. 496, and p. 499: an equilibrium of the money model satisfies the
nominal flow constraint `W_t = P_t s_t + Q_t W_{t+1}` of p. 499 with bond price
`Q_t = β P_t/P_{t+1}`. -/
theorem moneyEqm_debtFlow {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) :
    PresentValueIdentity.DebtFlow W P (fun t => β * P t / P (t + 1)) s :=
  fun t => MoneyRegimes.flow_of_valuation hβ0 hβ1 hs h t

/-- Cochrane (2023), §22.1, p. 496, and p. 499: in the money model the one-period discount
factor `Q_t P_{t+1}/P_t` is the constant `β`. -/
theorem moneyEqm_sdfStep {β : ℝ} {V y P M W s : ℕ → ℝ} (h : MoneyRegimes.Eqm β V y P M W s)
    (t : ℕ) : PresentValueIdentity.sdfStep P (fun t => β * P t / P (t + 1)) t = β := by
  have h0 := (h t).1.ne'
  have h1 := (h (t + 1)).1.ne'
  simp only [PresentValueIdentity.sdfStep]
  field_simp

/-- Cochrane (2023), p. 499 and §22.1, p. 496: the discount-factor valuation of chain B,
applied to an equilibrium of the money model (`0 < β < 1`, bounded surpluses), has weights
`Λ_{t+j}/Λ_t = βʲ` and reproduces the money model's valuation equation
`W_t/P_t = ∑ βʲ s_{t+j}` (the transversality condition is proved, not assumed). -/
theorem moneyEqm_sdf_valuation {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) (t : ℕ) :
    (∀ j, PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
        PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t = β ^ j) ∧
      HasSum (fun j => PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
        PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t * s (t + j))
        (W t / P t) := by
  have hP : ∀ t, 0 < P t := fun t => (h t).1
  have hQ : ∀ t, 0 < β * P t / P (t + 1) := fun t =>
    div_pos (mul_pos hβ0 (hP t)) (hP (t + 1))
  have hsdf := sdf_of_const_step (moneyEqm_sdfStep h)
  have hw : ∀ j, PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
      PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t = β ^ j := fun j => by
    rw [hsdf, hsdf, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero t hβ0.ne')]
  refine ⟨hw, ?_⟩
  have hpvb : ∀ k, |MoneyRegimes.pv β s k| ≤ K / (1 - β) := fun k => by
    have hg : HasSum (fun j : ℕ => K * β ^ j) (K / (1 - β)) := by
      simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left K
    have := tsum_of_norm_bounded hg (f := fun j => β ^ j * s (k + j)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le j), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hs _) (pow_nonneg hβ0.le j)
    simpa [MoneyRegimes.pv, Real.norm_eq_abs] using this
  refine PresentValueIdentity.sdf_valuation_hasSum hP hQ (moneyEqm_debtFlow hβ0.le hβ1 hs h) t
    ?_ ?_
  · simp only [hw]
    refine (tendsto_pow_mul_of_bounded (by rw [abs_of_pos hβ0]; exact hβ1)
      (x := fun T => MoneyRegimes.pv β s (t + T)) fun T => hpvb (t + T)).congr fun T => ?_
    rw [(h (t + T)).2.2]
  · simp only [hw]
    exact MoneyRegimes.pv_summable hβ0.le hβ1 hs t

/-! ### The s-shaped surplus and the regression of surpluses on debt -/

/-- Cochrane (2023), p. 502: when `|1 − α| < ρ`, the s-shaped surplus response is absolutely
summable (a genuine infinite moving average). -/
theorem sshape_summable {α ρ : ℝ} (hρ : 0 < ρ) (hαρ : |1 - α| < ρ) :
    Summable fun k => |NonIdentification.irfS α ρ (k + 1)| := by
  rw [← summable_nat_add_iff 1]
  have hq : |(1 - α) / ρ| < 1 := by
    rw [abs_div, abs_of_pos hρ, div_lt_one hρ]
    exact hαρ
  refine ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_left (|α| * ρ⁻¹)).congr
    fun k => ?_
  change |α| * ρ⁻¹ * |(1 - α) / ρ| ^ k = |NonIdentification.irfS α ρ (k + 2)|
  simp only [NonIdentification.irfS, NonIdentification.irfV]
  rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hρ, abs_pow]
  ring

/-- Cochrane (2023), p. 502 with p. 501 and §24.1, p. 519 (Theorem RG): the s-shaped surplus
response (`0 < α < 2`, `0 < ρ < 1`, `|1 − α| < ρ`) has zero present value
(`NonIdentification.irf_pv_zero`, so it moves no inflation) and, viewed as an exogenous moving
average, it is not white noise, so the population regression of surpluses on lagged debt has a
strictly positive coefficient (`SurplusRegression.regInf_pos_iff`). A positive coefficient is
therefore consistent with the `α = 0` representation: it does not identify `α`. -/
theorem sshape_regression_pos {α ρ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hαρ : |1 - α| < ρ) :
    HasSum (fun j => ρ ^ j * NonIdentification.irfS α ρ (j + 1)) 0 ∧
      0 < SurplusRegression.covInf ρ (fun k => NonIdentification.irfS α ρ (k + 1 + 1)) /
        ∑' m, SurplusRegression.bInf ρ (fun k => NonIdentification.irfS α ρ (k + 1 + 1)) m ^ 2 := by
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  refine ⟨NonIdentification.irf_pv_zero hα0 hα2 hρ0.ne',
    (SurplusRegression.regInf_pos_iff hρ (a := fun k => NonIdentification.irfS α ρ (k + 1))
      (sshape_summable hρ0 hαρ)).mpr fun hiid => ?_⟩
  have h1 : NonIdentification.irfS α ρ 2 = 0 := hiid 1 le_rfl
  simp only [NonIdentification.irfS, NonIdentification.irfV, pow_zero, mul_one] at h1
  have : 0 < α * ρ⁻¹ := mul_pos hα0 (inv_pos.mpr hρ0)
  linarith

/-! ### The equilibrium criterion: bounded debt and locally Ricardian rules -/

/-- Cochrane (2023), §22.7, p. 508, and Woodford (2003), Prop. 4.11, pp. 311–314 (via
`FiscalRec.LocallyRicardian`): with passive money `|φ| ≤ 1`, the target is the unique equilibrium
under the bounded-debt criterion iff the fiscal rule is not locally Ricardian and is off the
boundary `|1 − γ| = ρ`. -/
theorem uniqueB_iff_not_ricardian (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {ρ φ γ bb τg τπ τy τi : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    {tg : StarredModel.Outcome Ω} (hc : StarredModel.Consistent 𝔼 ρ tg)
    (htg : LeeperRegions.AdmissibleB 𝔼 tg) :
    LeeperRegions.UniqueEqmB 𝔼 ρ φ γ tg ↔
      ¬ FiscalRec.LocallyRicardian Ω ρ bb γ τg τπ τy τi ∧ |1 - γ| ≠ ρ := by
  rw [LeeperRegions.uniqueB_iff 𝔼 hρ0 hρ1 hc htg,
    LeeperRegions.locallyRicardian_iff_gamma (Ω := Ω) hρ0]
  constructor
  · rintro (h | h)
    · linarith
    · exact ⟨by linarith, by intro he; linarith⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))

/-- Cochrane (2023), §22.7, p. 508, and Woodford (2003), Prop. 4.11, pp. 311–314: a locally
Ricardian fiscal rule with passive money leaves the equilibrium indeterminate under both
criteria — the transversality condition (`Equivalence.unique_iff`: `|1 − γ| < ρ < 1` is
double-passive) and bounded debt (`LeeperRegions.uniqueB_iff`). -/
theorem ricardian_passive_not_unique (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {ρ φ γ bb τg τπ τy τi : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    (hR : FiscalRec.LocallyRicardian Ω ρ bb γ τg τπ τy τi)
    {tg : StarredModel.Outcome Ω} (hc : StarredModel.Consistent 𝔼 ρ tg)
    (htg : LeeperRegions.AdmissibleB 𝔼 tg) :
    ¬ Equivalence.UniqueEqm 𝔼 ρ φ γ tg ∧ ¬ LeeperRegions.UniqueEqmB 𝔼 ρ φ γ tg := by
  have hγ := (LeeperRegions.locallyRicardian_iff_gamma (Ω := Ω) hρ0).mp hR
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hd := (Equivalence.unique_iff 𝔼 hρ0.ne' hc
      (LeeperRegions.admissible_of_B 𝔼 hρa htg)).mp hu
    rcases hd with hd | hd <;> linarith
  · rcases (LeeperRegions.uniqueB_iff 𝔼 hρ0 hρ1 hc htg).mp hu with hd | hd <;> linarith

/-! ### Markov switching with one regime: the Taylor principle -/

/-- Cochrane (2023), pp. 522–523: when both regimes have the same `φ > 0`, the Davig–Leeper
condition is the Taylor principle `φ > 1`. -/
theorem dl_const_iff (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    MarkovRegimes.DLCondition T (fun _ => φ) ↔ 1 < φ := by
  have hp0 := T.nonneg 0 0
  have hq0 := T.nonneg 1 1
  have hp1 : T.P 0 0 ≤ 1 := by have := MarkovRegimes.P01 T; linarith [T.nonneg 0 1]
  have hq1 : T.P 1 1 ≤ 1 := by have := MarkovRegimes.P10 T; linarith [T.nonneg 1 0]
  change 1 < (1 - φ) * T.P 0 0 + (1 - φ) * T.P 1 1 + φ * φ ∧ T.P 0 0 / φ + T.P 1 1 / φ < 2 ↔
    1 < φ
  rw [← add_div, div_lt_iff₀ hφ]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hle
    push Not at hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hle)]
  · intro h
    refine ⟨by nlinarith, by linarith⟩

/-- Cochrane (2023), pp. 522–523: with a constant regime `φ > 0`, the Markov-switching model has
exactly one bounded equilibrium for every bounded disturbance iff `|φ| > 1`. -/
theorem markov_const_determinate_iff (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      1 < |φ| := by
  rw [MarkovRegimes.determinate_iff T (fun _ => hφ), dl_const_iff T hφ, abs_of_pos hφ]

/-- Cochrane (2023), pp. 522–523 and p. 495: with one regime and passive fiscal policy
(`0 < γ < 2`), Markov determinacy is exactly the determinacy of the starred system of chain A
(`Equivalence.Determinate`): the Taylor principle. -/
theorem markov_const_iff_starred_determinate (T : MarkovRegimes.Transition) {φ γ : ℝ}
    (hφ : 0 < φ) (hγ : 0 < γ ∧ γ < 2) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      Equivalence.Determinate φ γ := by
  rw [markov_const_determinate_iff T hφ, Equivalence.determinate_iff]
  constructor
  · exact Or.inl
  · rintro (h | h | h)
    · exact h
    · linarith
    · linarith

/-- Cochrane (2023), pp. 522–523: with one regime the Markov model is the scalar forward
equation `π_t = φ⁻¹ E_t π_{t+1} − φ⁻¹ u_t`, and its determinacy condition is the core's
`|φ⁻¹| < 1` (`ForwardSolution.existsUnique_iff`). -/
theorem markov_const_iff_forward (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      |φ⁻¹| < 1 := by
  rw [markov_const_determinate_iff T hφ, abs_inv, inv_lt_one_iff₀]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · exact absurd h (not_le.mpr (abs_pos.mpr hφ.ne'))
    · exact h

/-! ### OE-2 and OE-1 -/

/-- Cochrane (2023), §22.1, pp. 495–496: the observable path of a money-model equilibrium in the
variables of the frictionless linear model, under perfect foresight: inflation
`π_t = log P_t − log P_{t−1}` (`π_0 = 0`), the interest rate `i_t = π_{t+1}`, the end-of-period
real debt `v_t = W_{t+1}/P_{t+1}` and the surplus `s_t`. -/
noncomputable def moneyOutcome (P W s : ℕ → ℝ) : StarredModel.Outcome Unit where
  pi := fun t _ => Real.log (P t) - Real.log (P (t - 1))
  i := fun t _ => Real.log (P (t + 1)) - Real.log (P t)
  v := fun t _ => W (t + 1) / P (t + 1)
  s := fun t _ => s t

/-- Cochrane (2023), §22.1, pp. 495–496: a money-model equilibrium (`0 ≤ β < 1`, bounded
surpluses) satisfies the Fisher equation and the flow condition (22.2) of the frictionless model
with `ρ = β` (zero real return). -/
theorem moneyOutcome_consistent {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) :
    StarredModel.Consistent perfectForesight β (moneyOutcome P W s) := by
  refine ⟨fun t => rfl, fun t => ?_⟩
  have e := MoneyRegimes.pv_succ hβ0 hβ1 hs (t + 1)
  rw [← (h (t + 1)).2.2, ← (h (t + 1 + 1)).2.2] at e
  funext u
  simp only [moneyOutcome, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Nat.add_sub_cancel]
  linarith

/-- Cochrane (2023), §22.1, p. 495: the money-model path is admissible in the frictionless model
when inflation is bounded (debt is bounded by `K/(1 − β)`, so the transversality condition
holds). -/
theorem moneyOutcome_admissible {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s)
    (hπ : BoundedProc (moneyOutcome P W s).pi) :
    StarredModel.Admissible perfectForesight β (moneyOutcome P W s) := by
  have hpvb : ∀ k, |MoneyRegimes.pv β s k| ≤ K / (1 - β) := fun k => by
    have hg : HasSum (fun j : ℕ => K * β ^ j) (K / (1 - β)) := by
      simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left K
    have := tsum_of_norm_bounded hg (f := fun j => β ^ j * s (k + j)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hs _) (pow_nonneg hβ0 j)
    simpa [MoneyRegimes.pv, Real.norm_eq_abs] using this
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  refine ⟨fun t => rfl, fun t => rfl, hπ, Valuation.tvc_of_bounded _ hβ ⟨K / (1 - β), ?_⟩⟩
  intro t u
  change |W (t + 1) / P (t + 1)| ≤ K / (1 - β)
  rw [(h (t + 1)).2.2]
  exact hpvb (t + 1)

/-- Cochrane (2023), §22.1, pp. 495–497 (OE-2 and OE-1 together): an equilibrium of the money
model (`0 < β < 1`, bounded surpluses and inflation, positive `V`, `y`, nonzero `W`) is at the
same time (OE-2, `MoneyRegimes.oe2`) the unique price path of the active-money regime given `M`
and the unique equilibrium of the active-fiscal regime given `(W, s)`, and (OE-1,
`Equivalence.recipe`) its observable path is the unique admissible equilibrium of every
determinate interest-rate regime `(φ, γ)` of the frictionless model around itself. -/
theorem oe2_oe1 {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t) (hW : ∀ t, W t ≠ 0) (hs : ∀ t, |s t| ≤ K)
    (h : MoneyRegimes.Eqm β V y P M W s) (hπ : BoundedProc (moneyOutcome P W s).pi) :
    ((∀ P' : ℕ → ℝ, (∀ t, M t * V t = P' t * y t) → P' = P) ∧
      ∀ P' M' : ℕ → ℝ, MoneyRegimes.Eqm β V y P' M' W s → P' = P ∧ M' = M) ∧
      ∀ φ γ, Equivalence.Determinate φ γ →
        StarredModel.Eqm perfectForesight β φ γ (moneyOutcome P W s) (moneyOutcome P W s) ∧
          Equivalence.UniqueEqm perfectForesight β φ γ (moneyOutcome P W s) := by
  have hc := moneyOutcome_consistent hβ0.le hβ1 hs h
  exact ⟨MoneyRegimes.oe2 hV hy hW h, Equivalence.recipe perfectForesight hβ0.ne' hc.1 hc.2
    (moneyOutcome_admissible hβ0.le hβ1 hs h hπ)⟩

/-! ### Geometric decay of matrix powers -/

/-- Cochrane (2023), p. 523 and Online Appendix p. 605 ("the eigenvalues of `A` are less than
one"): the powers of a Schur-stable `2 × 2` matrix (the core's root-location criterion, used by
`MarkovRegimes`) decay geometrically, `|(Aᵏ)_{ij}| ≤ C rᵏ` with `r < 1` — chain B's `PowDecay`.
Hence `MarkovRegimes.summable_pow_entry_of_schur` is also an instance of
`PresentValueIdentity.summable_pow_entry`. -/
theorem powDecay_of_schur {A : Matrix (Fin 2) (Fin 2) ℝ} (h : SchurStable (tr2 A) (det2 A)) :
    PresentValueIdentity.PowDecay A := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  set ρ := max ‖root₁ (tr2 A) (det2 A)‖ ‖root₂ (tr2 A) (det2 A)‖ with hρdef
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  set r : ℝ := (1 + ρ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  set q : ℝ := ρ / r with hq
  have hq0 : 0 ≤ q := div_nonneg hρ0 hr0.le
  have hq1 : q < 1 := (div_lt_one hr0).mpr (by rw [hr]; linarith)
  set G : ℝ := (1 - q)⁻¹ with hG
  have hG0 : 0 ≤ G := inv_nonneg.mpr (by linarith)
  have key : ∀ n : ℕ, ((n : ℝ) + 1) * ρ ^ n ≤ G * r ^ n := by
    intro n
    have hsum : ∑ j ∈ Finset.range (n + 1), q ^ j ≤ G := by
      rw [hG, ← tsum_geometric_of_lt_one hq0 hq1]
      exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
        (fun j _ => pow_nonneg hq0 j)
    have hle : ((n : ℝ) + 1) * q ^ n ≤ ∑ j ∈ Finset.range (n + 1), q ^ j := by
      have : ∑ _j ∈ Finset.range (n + 1), q ^ n ≤ ∑ j ∈ Finset.range (n + 1), q ^ j :=
        Finset.sum_le_sum fun j hj =>
          pow_le_pow_of_le_one hq0 hq1.le (by simp only [Finset.mem_range] at hj; omega)
      simpa using this
    have hpow : ρ ^ n = q ^ n * r ^ n := by rw [← mul_pow, hq, div_mul_cancel₀ _ hr0.ne']
    rw [hpow]
    have hrn := pow_nonneg hr0.le n
    nlinarith
  set N : ℝ := |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| with hN
  have hN0 : 0 ≤ N := by positivity
  have a00 := abs_nonneg (A 0 0)
  have a01 := abs_nonneg (A 0 1)
  have a10 := abs_nonneg (A 1 0)
  have a11 := abs_nonneg (A 1 1)
  have hAN : ∀ i j, |A i j| ≤ N :=
    Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨by linarith, by linarith⟩,
      Fin.forall_fin_two.mpr ⟨by linarith, by linarith⟩⟩
  have hD : |det2 A| ≤ 1 := h.1.le
  refine ⟨1 + N / r + G * N / r + G / r ^ 2, r, by positivity, hr0.le, hr1, fun k i j => ?_⟩
  have hNr : 0 ≤ N / r := div_nonneg hN0 hr0.le
  have hGNr : 0 ≤ G * N / r := div_nonneg (mul_nonneg hG0 hN0) hr0.le
  have hGr : 0 ≤ G / r ^ 2 := div_nonneg hG0 (pow_nonneg hr0.le 2)
  rcases k with _ | _ | n
  · rw [pow_zero, pow_zero, mul_one]
    have : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    linarith
  · rw [pow_one, zero_add, pow_one]
    have e : N = N / r * r := by field_simp
    have : N / r * r ≤ (1 + N / r + G * N / r + G / r ^ 2) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr0.le
    linarith [hAN i j]
  · have hb := abs_pow_entry_le A n i j
    have hc1 := abs_chSeq_le (tr2 A) (det2 A) (n + 1)
    have hc0 := abs_chSeq_le (tr2 A) (det2 A) n
    rw [← hρdef] at hc1 hc0
    have k1 := key (n + 1)
    have k0 := key n
    push_cast at hc1 k1
    have hA := hAN i j
    have hcs1 : |chSeq (tr2 A) (det2 A) (n + 1)| * |A i j| ≤ G * r ^ (n + 1) * N :=
      mul_le_mul (hc1.trans k1) hA (abs_nonneg _) (by positivity)
    have hcs0 : |det2 A| * |chSeq (tr2 A) (det2 A) n| ≤ 1 * (G * r ^ n) :=
      mul_le_mul hD (hc0.trans k0) (abs_nonneg _) zero_le_one
    have e1 : G * r ^ (n + 1) * N = G * N / r * r ^ (n + 2) := by
      field_simp
      ring
    have e0 : 1 * (G * r ^ n) = G / r ^ 2 * r ^ (n + 2) := by
      field_simp
      ring
    have hrn := pow_nonneg hr0.le (n + 2)
    have hfin : G * N / r * r ^ (n + 2) + G / r ^ 2 * r ^ (n + 2) ≤
        (1 + N / r + G * N / r + G / r ^ 2) * r ^ (n + 2) := by
      nlinarith
    rw [show n + 1 + 1 = n + 2 by omega]
    linarith

end Cochrane.ObservationalEquivalence.Links

set_option linter.style.longLine false
#print axioms Cochrane.ObservationalEquivalence.SchurStable
#print axioms Cochrane.ObservationalEquivalence.discQ
#print axioms Cochrane.ObservationalEquivalence.root₁
#print axioms Cochrane.ObservationalEquivalence.root₂
#print axioms Cochrane.ObservationalEquivalence.root_sum
#print axioms Cochrane.ObservationalEquivalence.root_prod
#print axioms Cochrane.ObservationalEquivalence.root_eq
#print axioms Cochrane.ObservationalEquivalence.normSq_root_of_neg
#print axioms Cochrane.ObservationalEquivalence.norm_root_of_nonneg
#print axioms Cochrane.ObservationalEquivalence.schurStable_iff_roots
#print axioms Cochrane.ObservationalEquivalence.chSeq
#print axioms Cochrane.ObservationalEquivalence.convSeq
#print axioms Cochrane.ObservationalEquivalence.convSeq_rec
#print axioms Cochrane.ObservationalEquivalence.chSeq_eq_convSeq
#print axioms Cochrane.ObservationalEquivalence.norm_convSeq_le
#print axioms Cochrane.ObservationalEquivalence.abs_chSeq_le
#print axioms Cochrane.ObservationalEquivalence.tendsto_chSeq
#print axioms Cochrane.ObservationalEquivalence.tr2
#print axioms Cochrane.ObservationalEquivalence.det2
#print axioms Cochrane.ObservationalEquivalence.tr2_eq_trace
#print axioms Cochrane.ObservationalEquivalence.det2_eq_det
#print axioms Cochrane.ObservationalEquivalence.sq_eq_cayleyHamilton
#print axioms Cochrane.ObservationalEquivalence.pow_succ_eq
#print axioms Cochrane.ObservationalEquivalence.abs_pow_entry_le
#print axioms Cochrane.ObservationalEquivalence.tendsto_pow_entry
#print axioms Cochrane.ObservationalEquivalence.BoundedSeq
#print axioms Cochrane.ObservationalEquivalence.homogeneous_iterate
#print axioms Cochrane.ObservationalEquivalence.abs_mulVec_le
#print axioms Cochrane.ObservationalEquivalence.homogeneous_eq_zero
#print axioms Cochrane.ObservationalEquivalence.eq_root_of_eq
#print axioms Cochrane.ObservationalEquivalence.exists_eigenvector
#print axioms Cochrane.ObservationalEquivalence.exists_bounded_homogeneous
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.mk
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.E
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.const
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.mono
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.tower
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.known
#print axioms Cochrane.ObservationalEquivalence.perfectForesight
#print axioms Cochrane.ObservationalEquivalence.BoundedProc
#print axioms Cochrane.ObservationalEquivalence.BoundedVec
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.Adapted
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.IsAR1
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.E_neg
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.E_smul
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.E_E_self
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.abs_E_le
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.bounded_E
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.ar1_iterate
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forward_iterate
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forward_unique
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.E_tsum
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forwardSeries
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.PullOut
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.Solves
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.AdaptedVec
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.system_iterate
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.system_unique
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.system_not_unique
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.Determinate
#print axioms Cochrane.ObservationalEquivalence.ExpectationSystem.determinate_iff
#print axioms Cochrane.ObservationalEquivalence.perfectForesight_pullOut
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.ObservationalEquivalence.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.Solves
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.E_of_known
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.solves_adapted
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.iterate_A15
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.summable_A16
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.ScalarEq
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalarSol
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalarSol_apply
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalarEq_iff
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalar_homog
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sunspotFamily
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.homog_solves
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.solves_add_homog
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.existsUnique_iff
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.ar1_decay
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.predetermined_restriction
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.summable_geom_mul
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.abel_tsum
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.ObservationalEquivalence.ForwardSolution.E_tsum_dom
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.innov
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.innov_apply
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.innov_of_known
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.fullInfo
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.fullInfo_E
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.pvExPost
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.summable_pow_mul_of_bounded
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.tendsto_pow_mul_of_bounded
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.flow_telescope
#print axioms Cochrane.ObservationalEquivalence.ExpectationTools.pv_of_flow
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.Debt42
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.Tax44
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.Debt45
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.debt42_iff_45
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.dRec
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.eq_dRec
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.abs_rec_le
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.rec_bounded
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.rec_unbounded
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.pow_bounded_eq_zero
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.dRec_adapted
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.dRec_adapted_of_succ
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.LocallyRicardian
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.locallyRicardian_iff
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.ricardian_iff_taub
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.one_le_abs_one_sub_iff
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.abs_one_sub_lt_one_iff
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.tendsto_pow_mul_iff
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.eq_zero_of_tendsto_pow_mul
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.tendsto_zero_of_stable_rec
#print axioms Cochrane.ObservationalEquivalence.FiscalRec.zero_of_E_succ_eq_smul
#print axioms Cochrane.ObservationalEquivalence.Valuation.Fisher
#print axioms Cochrane.ObservationalEquivalence.Valuation.Flow
#print axioms Cochrane.ObservationalEquivalence.Valuation.surprise
#print axioms Cochrane.ObservationalEquivalence.Valuation.realReturn
#print axioms Cochrane.ObservationalEquivalence.Valuation.TVC
#print axioms Cochrane.ObservationalEquivalence.Valuation.pvE
#print axioms Cochrane.ObservationalEquivalence.Valuation.E_surprise
#print axioms Cochrane.ObservationalEquivalence.Valuation.E_surprise_later
#print axioms Cochrane.ObservationalEquivalence.Valuation.surprise_eq_innov
#print axioms Cochrane.ObservationalEquivalence.Valuation.flow_iff_surprise
#print axioms Cochrane.ObservationalEquivalence.Valuation.flow_iff_realReturn
#print axioms Cochrane.ObservationalEquivalence.Valuation.E_realReturn
#print axioms Cochrane.ObservationalEquivalence.Valuation.telescope
#print axioms Cochrane.ObservationalEquivalence.Valuation.telescope_E
#print axioms Cochrane.ObservationalEquivalence.Valuation.valuation_of_tvc
#print axioms Cochrane.ObservationalEquivalence.Valuation.tvc_of_valuation
#print axioms Cochrane.ObservationalEquivalence.Valuation.tvc_iff_valuation
#print axioms Cochrane.ObservationalEquivalence.Valuation.pvE_summable
#print axioms Cochrane.ObservationalEquivalence.Valuation.abs_pvE_le
#print axioms Cochrane.ObservationalEquivalence.Valuation.valuation_tsum
#print axioms Cochrane.ObservationalEquivalence.Valuation.E_pvExPost
#print axioms Cochrane.ObservationalEquivalence.Valuation.valuation_E_exPost
#print axioms Cochrane.ObservationalEquivalence.Valuation.pvE_succ_split
#print axioms Cochrane.ObservationalEquivalence.Valuation.unexpected_inflation
#print axioms Cochrane.ObservationalEquivalence.Valuation.unexpected_inflation_news
#print axioms Cochrane.ObservationalEquivalence.Valuation.tvc_of_bounded
#print axioms Cochrane.ObservationalEquivalence.Valuation.tvc_sub
#print axioms Cochrane.ObservationalEquivalence.Valuation.tvc_add
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome.mk
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome.pi
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome.i
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome.v
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Outcome.s
#print axioms Cochrane.ObservationalEquivalence.StarredModel.outcome_ext
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Consistent
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Admissible
#print axioms Cochrane.ObservationalEquivalence.StarredModel.Eqm
#print axioms Cochrane.ObservationalEquivalence.StarredModel.StarredSurplus
#print axioms Cochrane.ObservationalEquivalence.StarredModel.ThetaRule
#print axioms Cochrane.ObservationalEquivalence.StarredModel.eq22_8
#print axioms Cochrane.ObservationalEquivalence.StarredModel.eq22_9
#print axioms Cochrane.ObservationalEquivalence.StarredModel.consistent_iff_eq22_10
#print axioms Cochrane.ObservationalEquivalence.StarredModel.eq23_4_starred
#print axioms Cochrane.ObservationalEquivalence.StarredModel.starred_eqm
#print axioms Cochrane.ObservationalEquivalence.StarredModel.observables_eq16_23_24
#print axioms Cochrane.ObservationalEquivalence.StarredModel.deviation_dynamics
#print axioms Cochrane.ObservationalEquivalence.StarredModel.lag
#print axioms Cochrane.ObservationalEquivalence.StarredModel.ofDev
#print axioms Cochrane.ObservationalEquivalence.StarredModel.ofDev_eqm
#print axioms Cochrane.ObservationalEquivalence.StarredModel.eq_ofDev
#print axioms Cochrane.ObservationalEquivalence.StarredModel.ofDev_zero
#print axioms Cochrane.ObservationalEquivalence.StarredModel.dev_admissible
#print axioms Cochrane.ObservationalEquivalence.StarredModel.ofDev_admissible
#print axioms Cochrane.ObservationalEquivalence.StarredModel.valuation_all_regimes
#print axioms Cochrane.ObservationalEquivalence.StarredModel.LeeperEqm
#print axioms Cochrane.ObservationalEquivalence.StarredModel.eq23_4
#print axioms Cochrane.ObservationalEquivalence.StarredModel.leeper_expected_inflation
#print axioms Cochrane.ObservationalEquivalence.StarredModel.leeper_is_starred
#print axioms Cochrane.ObservationalEquivalence.StarredModel.rule24_1_printed
#print axioms Cochrane.ObservationalEquivalence.Equivalence.UniqueEqm
#print axioms Cochrane.ObservationalEquivalence.Equivalence.Determinate
#print axioms Cochrane.ObservationalEquivalence.Equivalence.starred_admissible_eqm
#print axioms Cochrane.ObservationalEquivalence.Equivalence.d_zero_of_e_zero
#print axioms Cochrane.ObservationalEquivalence.Equivalence.e_zero_of_d_zero
#print axioms Cochrane.ObservationalEquivalence.Equivalence.isAR1_of_dyn
#print axioms Cochrane.ObservationalEquivalence.Equivalence.pow_mul_E_ar1
#print axioms Cochrane.ObservationalEquivalence.Equivalence.tvc_of_ar1
#print axioms Cochrane.ObservationalEquivalence.Equivalence.zero_of_ar1_tvc
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_of_active_money
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_of_active_fiscal
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_of_determinate
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_of_gamma_zero
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_double_active
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famE
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famD
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famPath
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famPath_eqm
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famPath_admissible
#print axioms Cochrane.ObservationalEquivalence.Equivalence.famPath_injective
#print axioms Cochrane.ObservationalEquivalence.Equivalence.continuum_double_passive
#print axioms Cochrane.ObservationalEquivalence.Equivalence.not_unique_of_passive
#print axioms Cochrane.ObservationalEquivalence.Equivalence.unique_iff
#print axioms Cochrane.ObservationalEquivalence.Equivalence.determinate_iff
#print axioms Cochrane.ObservationalEquivalence.Equivalence.printed_phi_lt_one_determinate
#print axioms Cochrane.ObservationalEquivalence.Equivalence.printed_gamma_pos_determinate
#print axioms Cochrane.ObservationalEquivalence.Equivalence.sunspot_eqm
#print axioms Cochrane.ObservationalEquivalence.Equivalence.coinShock_adapted
#print axioms Cochrane.ObservationalEquivalence.Equivalence.coinShock_bounded
#print axioms Cochrane.ObservationalEquivalence.Equivalence.coin_sunspot_eqm
#print axioms Cochrane.ObservationalEquivalence.Equivalence.perfectForesight_eq_famPath
#print axioms Cochrane.ObservationalEquivalence.Equivalence.recipe
#print axioms Cochrane.ObservationalEquivalence.Equivalence.oe_both_ways
#print axioms Cochrane.ObservationalEquivalence.Equivalence.leeper_recipe
#print axioms Cochrane.ObservationalEquivalence.Equivalence.nk_solution
#print axioms Cochrane.ObservationalEquivalence.Equivalence.nk_unique
#print axioms Cochrane.ObservationalEquivalence.Equivalence.nk_observables
#print axioms Cochrane.ObservationalEquivalence.Equivalence.ftpl_eq_nk
#print axioms Cochrane.ObservationalEquivalence.Equivalence.nk_passive_fiscal_news
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.EqmSet
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.eqmSet_eq_singleton
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.eqmSet_const_on_determinate
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.statistic_independent
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.target_mem_eqmSet
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.not_identified
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.eqm_rate_theta
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.coef_from_moment
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.regression_identifies_theta
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.spec_forces_phi_eq_theta
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.eqm_inflation_theta
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.stationary_iff
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.thetaTarget
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.thetaTarget_ok
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.theta_target_unique
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.eqm_surplus_alpha
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.regression_identifies_alpha
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.spec_forces_gamma_eq_alpha
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.reverse_engineer_rule
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.revUi
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.revUs
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.reverse_engineer_leeper
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.rev_disturbances_differ
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.sshape_two_ways
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.leeper_sshape_two_ways
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irfV
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irfS
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.impulse
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irf_flow
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irf_surplus
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irf_sshape
#print axioms Cochrane.ObservationalEquivalence.NonIdentification.irf_pv_zero
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.mkPath
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.mkPath_eqm
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.eq_mkPath
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vPath
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vPath_spec
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vPath_adapted
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.tvc_passive
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.piM
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.piM_spec
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vF
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vF_spec
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.leeper_debt_E
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.eq_vF
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.nuF
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.active_fiscal_forced
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.active_money_forced
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_a
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.piB
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_b
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_c_iff
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_c_unique_K
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.piM_zero
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.vF_zero_of_md
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_c_md_nonexistence
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_c_coin
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.e19_starred_vs_unstarred
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_d
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.gamma_three_active
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_d_sunspot
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_d_coin
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_d_of_solution
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_d_unit_nonexistence
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_b_iff
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.region_b_unbounded_K
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.AdmissibleB
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.UniqueEqmB
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.admissible_of_B
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.uniqueB_iff
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.criterion_matters
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.locallyRicardian_iff_gamma
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.literal_gap
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.literal_vS
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.literal_limit
#print axioms Cochrane.ObservationalEquivalence.LeeperRegions.literal_tvc_iff
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.pv
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.Eqm
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.pv_summable
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.pv_succ
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.flow_of_valuation
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.activeMoney_price
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.activeMoney_exists
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.activeFiscal_unique
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.activeFiscal_exists
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.oe2
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.inconsistent_iff
#print axioms Cochrane.ObservationalEquivalence.MoneyRegimes.halve_money_no_eqm
#print axioms Cochrane.ObservationalEquivalence.MACovariance.WhiteNoise
#print axioms Cochrane.ObservationalEquivalence.MACovariance.maProc
#print axioms Cochrane.ObservationalEquivalence.MACovariance.autocov
#print axioms Cochrane.ObservationalEquivalence.MACovariance.cov_maProc
#print axioms Cochrane.ObservationalEquivalence.MACovariance.var_maProc
#print axioms Cochrane.ObservationalEquivalence.MACovariance.cov_maProc_stationary
#print axioms Cochrane.ObservationalEquivalence.MACovariance.var_maProc_eq_zero_iff
#print axioms Cochrane.ObservationalEquivalence.MACovariance.finsuppCov
#print axioms Cochrane.ObservationalEquivalence.MACovariance.finsuppNoise
#print axioms Cochrane.ObservationalEquivalence.MACovariance.finsuppNoise_whiteNoise
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsKernel
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsTail
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsLDL
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsKernel_symm
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsKernel_succ
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsTail_zero_succ
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsTail_shift
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsTail_succ
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsTail_of_le
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm_succ
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsLDL_succ
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm_eq_ldl
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm_nonneg
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm_eq_zero_iff
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsForm_pos
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsMatrix
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsMatrix_quad
#print axioms Cochrane.ObservationalEquivalence.MACovariance.kmsMatrix_posDef
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ShockInfo
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.surplus
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.valueOfDebt
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.vCoeff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.regCoeff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.IsIID
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.aRho
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.E_maProc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.abs_maProc_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.shifted_sum
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.value_eq_maProc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.vCoeff_of_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.vCoeff_eq_kmsTail
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.cov_surplus_value
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.var_value
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.two_sum_eq_ldl
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.two_cov_eq_kms
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.sum_sq_pos_iff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.cov_pos_iff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.iid_value_zero
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.iid_cov_zero
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.regCoeff_pos_iff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.book_claim_aRho_lt_one
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ma1Coeff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ma1_aRho_gt_one
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ma1_regCoeff_pos
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_value
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_cov
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_regCoeff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_aRho_gt_one
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncSeq
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.bInf
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.covInf
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.abs_kmsKernel_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.abs_tsum_le_of_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.tail_abs
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.abs_le_tsum_abs
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.abs_truncSeq_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.tendsto_truncSeq
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.bInf_bound
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.covInf_summable
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf_summable
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.sq_summable
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.bInf_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.covInf_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.sq_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.two_finite_eq
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsForm_lower
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.tendsto_covInf_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.tendsto_sq_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.tendsto_kmsInf_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.two_covInf_eq
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf_nonneg
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf_lower
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.kmsInf_pos
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.covInf_pos_iff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.bInf_abs_summable
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.bInf_sq_summable
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.regInf_pos_iff
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncSeq_support
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.cov_trunc_tendsto
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_bInf
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.ar1_covInf
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncPath
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncPath_trunc_le
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncPath_le_trunc
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncSystem
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.clampShock
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.clampShock_bounded
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.clampShock_info
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.clampShock_linearIndependent
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.shockCoord
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.shockCoord_shock
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncCov
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.clampShock_whiteNoise
#print axioms Cochrane.ObservationalEquivalence.SurplusRegression.truncModel_regCoeff_pos
#print axioms Cochrane.ObservationalEquivalence.Granger.IsVAR
#print axioms Cochrane.ObservationalEquivalence.Granger.ShockMDS
#print axioms Cochrane.ObservationalEquivalence.Granger.var_forecast
#print axioms Cochrane.ObservationalEquivalence.Granger.var_innov
#print axioms Cochrane.ObservationalEquivalence.Granger.cov_innov_shock
#print axioms Cochrane.ObservationalEquivalence.Granger.OneStepNonCausal
#print axioms Cochrane.ObservationalEquivalence.Granger.IRFNonCausal
#print axioms Cochrane.ObservationalEquivalence.Granger.irf_nonCausal_iff_forecast
#print axioms Cochrane.ObservationalEquivalence.Granger.irf_imp_oneStep
#print axioms Cochrane.ObservationalEquivalence.Granger.bivariate_oneStep_iff_irf
#print axioms Cochrane.ObservationalEquivalence.Granger.chainA
#print axioms Cochrane.ObservationalEquivalence.Granger.trivariate_counterexample
#print axioms Cochrane.ObservationalEquivalence.Granger.newsCoeff
#print axioms Cochrane.ObservationalEquivalence.Granger.news_surplus
#print axioms Cochrane.ObservationalEquivalence.Granger.newsCoeff_support
#print axioms Cochrane.ObservationalEquivalence.Granger.news_value
#print axioms Cochrane.ObservationalEquivalence.Granger.news_surplus_eq_value
#print axioms Cochrane.ObservationalEquivalence.Granger.news_regCoeff
#print axioms Cochrane.ObservationalEquivalence.Granger.news_past_surplus_uncorrelated
#print axioms Cochrane.ObservationalEquivalence.Granger.truncModel_news
#print axioms Cochrane.ObservationalEquivalence.Granger.newsA
#print axioms Cochrane.ObservationalEquivalence.Granger.newsZ
#print axioms Cochrane.ObservationalEquivalence.Granger.newsShock
#print axioms Cochrane.ObservationalEquivalence.Granger.news_isVAR
#print axioms Cochrane.ObservationalEquivalence.Granger.news_debt_causes_surplus
#print axioms Cochrane.ObservationalEquivalence.Granger.news_surplus_not_cause_debt
#print axioms Cochrane.ObservationalEquivalence.Granger.Coarser
#print axioms Cochrane.ObservationalEquivalence.Granger.pv_ours_of_agents
#print axioms Cochrane.ObservationalEquivalence.Granger.pv_ours_iff
#print axioms Cochrane.ObservationalEquivalence.Granger.pv_ours_of_same
#print axioms Cochrane.ObservationalEquivalence.Granger.coinMean
#print axioms Cochrane.ObservationalEquivalence.Granger.oursInfo
#print axioms Cochrane.ObservationalEquivalence.Granger.ours_coarser
#print axioms Cochrane.ObservationalEquivalence.Granger.coinSurplus
#print axioms Cochrane.ObservationalEquivalence.Granger.coinSurplus_pv
#print axioms Cochrane.ObservationalEquivalence.Granger.pv_ours_fails
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.vecAt
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_apply
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.PowDecay
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.eigs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.map_ofReal_pow
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.powDecay_of_eigs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.powDecay_smul
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.summable_pow_entry
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.tendsto_pow_entry_of_powDecay
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.neumannSum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.neumannSum_mul
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.inv_one_sub_eq
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.isUnit_det_one_sub
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.inv_one_sub_hasSum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.hasSum_bilin
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.neumann_bilin_hasSum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.innov_obs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.E_obs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.var_innov_obs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.var_forecast_obs
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_adapted
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.weight_bilin
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.var_weighted_sum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_add
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_sub
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.flow_restriction_of_identity
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.one_sub_smul_mul_comm
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.inv_one_sub_mul_comm
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.flow_restriction_iff_pv
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.var_pv_identity
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_smul
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.obs_var_succ
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.flow_forces_singular
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.ShockNondeg
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.nondeg_forces_trivial
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.expost_pv_finite
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.expost_pv
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.expost_pv_split
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.pv_identity_exante
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.as_eq_ar_innov
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.const_return_as_zero
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.genVAR
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.genVAR_hasSum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.innov_pv_var
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.as_eq_ar_var
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.DebtFlow
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdfStep
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_pos
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_prices_bond
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_flow
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_valuation_finite
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_valuation_tendsto
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_valuation_hasSum
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.tvc_of_sdf_valuation
#print axioms Cochrane.ObservationalEquivalence.PresentValueIdentity.sdf_valuation_E
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.price
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.rational_behavioral_equiv
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.behavioral_pos
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.same_prices_iff
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.riskNeutral
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.cost
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.payoff
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.IsArbitrage
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.NoArbitrage
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.IsSDF
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.cost_eq_of_sdf
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.noArbitrage_of_sdf
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.gains
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.simplexSet
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.convex_simplexSet
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.functional_eq_sum
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.exists_sdf_of_noArbitrage
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.ftap
#print axioms Cochrane.ObservationalEquivalence.AssetPricingOE.sdf_expectation_form
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Transition
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Transition.mk
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Transition.P
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Transition.nonneg
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Transition.rowSum
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Node
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.Solves
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.BoundedFn
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.regM
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.DLCondition
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.regM_nonneg
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.P01
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.P10
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.charpoly_one_eq
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.schur_iff_of_nonneg
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.dl_iff_schur
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.pow_succ_apply
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.abs_le_pow_bound
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.homog_eq_zero
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.mulVec_fin_two
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.exists_perron
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.homog_nonzero_of_not_dl
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.summable_pow_entry_of_schur
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdTerm
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdSol
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdTerm_bound
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.summable_bound
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdTerm_summable
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdSol_solves
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.fwdSol_bounded
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.solves_sub
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.determinate_iff
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.both_active_determinate
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.both_passive_indeterminate
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.egShortPassive
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.egLongPassive
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.temporarily_passive_determinate
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.locally_active_indeterminate
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.MarkovRegime
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.MarkovRegime.mk
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.MarkovRegime.S
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.MarkovRegime.markov
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.abstract_bound
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.abstract_homog_eq_zero
#print axioms Cochrane.ObservationalEquivalence.MarkovRegimes.abstract_homog_nonzero
#print axioms Cochrane.ObservationalEquivalence.Links.perfectForesight_eq_fullInfo
#print axioms Cochrane.ObservationalEquivalence.Links.pvExPost_eq_pv
#print axioms Cochrane.ObservationalEquivalence.Links.valueOfDebt_eq_valuation
#print axioms Cochrane.ObservationalEquivalence.Links.unexpected_inflation_of_identity
#print axioms Cochrane.ObservationalEquivalence.Links.sdf_of_const_step
#print axioms Cochrane.ObservationalEquivalence.Links.moneyEqm_debtFlow
#print axioms Cochrane.ObservationalEquivalence.Links.moneyEqm_sdfStep
#print axioms Cochrane.ObservationalEquivalence.Links.moneyEqm_sdf_valuation
#print axioms Cochrane.ObservationalEquivalence.Links.sshape_summable
#print axioms Cochrane.ObservationalEquivalence.Links.sshape_regression_pos
#print axioms Cochrane.ObservationalEquivalence.Links.uniqueB_iff_not_ricardian
#print axioms Cochrane.ObservationalEquivalence.Links.ricardian_passive_not_unique
#print axioms Cochrane.ObservationalEquivalence.Links.dl_const_iff
#print axioms Cochrane.ObservationalEquivalence.Links.markov_const_determinate_iff
#print axioms Cochrane.ObservationalEquivalence.Links.markov_const_iff_starred_determinate
#print axioms Cochrane.ObservationalEquivalence.Links.markov_const_iff_forward
#print axioms Cochrane.ObservationalEquivalence.Links.moneyOutcome
#print axioms Cochrane.ObservationalEquivalence.Links.moneyOutcome_consistent
#print axioms Cochrane.ObservationalEquivalence.Links.moneyOutcome_admissible
#print axioms Cochrane.ObservationalEquivalence.Links.oe2_oe1
#print axioms Cochrane.ObservationalEquivalence.Links.powDecay_of_schur
