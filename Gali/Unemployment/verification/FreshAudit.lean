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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
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

Restated from the `Gali/StickyWagesPrices` project (each project in this
repository is self-contained).
-/

namespace Gali.Unemployment

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

end Gali.Unemployment

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

Restated from the `Gali/StickyWagesPrices` project (each project in this
repository is self-contained).
-/

namespace Gali.Unemployment

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

end Gali.Unemployment

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

Restated from the `Gali/StickyWagesPrices` project (each project in this
repository is self-contained).
-/

namespace Gali.Unemployment.ExpectationsFiniteTree

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

end Gali.Unemployment.ExpectationsFiniteTree

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

Restated from the `Gali/StickyWagesPrices` project (each project in this repository is
self-contained); Chapter 7's system is Chapter 6's plus a static equation for unemployment.
-/

namespace Gali.Unemployment.Determinacy4

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

end Gali.Unemployment.Determinacy4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Indivisible labour and the participation decision

Galí (2015), Chapter 7, §7.1.1, pp. 201–204, and the participation condition of §7.1.2,
p. 204. Each household has members `(j, s) ∈ [0, 1] × [0, 1]`; member `(j, s)` suffers the
disutility `χ s^φ` if employed (`χ > 0`, `φ > 0`). With full risk sharing the household's
period utility is the integral of its members' utilities, and with the employed members of
type `j` being `s ∈ [0, N(j)]`,

  `∫₀^{N(j)} χ s^φ ds = χ N(j)^{1+φ}/(1 + φ)`,

so the household's utility is exactly the Chapter 6 utility (p. 202). Member `(j, s)` is
willing to work iff `W(j)/P ≥ χ C^σ s^φ` (p. 204); the set of willing members is exactly the
interval `[0, L(j)]`, with `L(j)` the marginal participant defined by (5),
`W(j)/P = χ C^σ L(j)^φ`.

## Main results

* `integral_disutility`: `∫₀^N χ s^φ ds = χ N^{1+φ}/(1 + φ)` (a genuine interval integral,
  any real `N`, `φ > −1`).
* `householdUtility_eq_ch6`: the indivisible-labour household utility equals the Chapter 6
  utility `U(C, {N(j)}; Z) = (u(C) − χ ∫₀¹ N(j)^{1+φ}/(1+φ) dj) Z`.
* `hasDerivAt_disutility`: the marginal disutility of employing one more member is `χ N^φ`.
* `hasDerivAt_crra`, `marginal_value`: the marginal value to the household of member `s`
  working at real wage `ω` is `C^{−σ} ω − χ s^φ` (utility units), so
  `participates_iff`: member `s` participates iff `ω ≥ χ C^σ s^φ` (p. 204).
* `eq5_iff`: (5) has the unique nonnegative solution `L = (ω/(χ C^σ))^{1/φ}`.
* `participation_set_eq`: `{s ≥ 0 | χ C^σ s^φ ≤ ω} = [0, L]`, and
  `participation_set_unit`: within the unit interval of members it is `[0, min L 1]`.
* `marginal_indifferent`, `inframarginal_strict`, `supramarginal_refuses`: the marginal
  participant is indifferent; members below strictly gain, members above strictly lose.
* `laborForce_le_one_iff`: `L ≤ 1` iff `ω ≤ χ C^σ`.
-/

namespace Gali.Unemployment.IndivisibleLabor

/-! ### The disutility integral (p. 202) -/

/-- Galí (2015), p. 202: the total disutility of the employed members `s ∈ [0, N]` of a
labour type, `∫₀^N χ s^φ ds = χ N^{1+φ}/(1 + φ)`, for every real `N` and `φ > −1`
(in the model `φ > 0`, `N ∈ [0, 1]`). -/
theorem integral_disutility {χ φ : ℝ} (hφ : -1 < φ) (N : ℝ) :
    ∫ s in (0 : ℝ)..N, χ * s ^ φ = χ * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hφ)]
  have h0 : (0 : ℝ) ^ (φ + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, sub_zero, add_comm φ 1]
  ring

/-- Galí (2015), p. 202: the period utility of consumption, `(C^{1−σ} − 1)/(1 − σ)`, with its
limit `log C` at `σ = 1`. -/
noncomputable def crra (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 202, first line: the indivisible-labour household's period utility, the
integral of its members' utilities, `(u(C) − χ ∫₀¹ ∫₀^{N(j)} s^φ ds dj) Z`. -/
noncomputable def householdUtility (σ χ φ C Z : ℝ) (N : ℝ → ℝ) : ℝ :=
  (crra σ C - χ * ∫ j in (0 : ℝ)..1, ∫ s in (0 : ℝ)..N j, s ^ φ) * Z

/-- Galí (2015), p. 202, second line (the Chapter 6 period utility):
`(u(C) − χ ∫₀¹ N(j)^{1+φ}/(1 + φ) dj) Z`. -/
noncomputable def ch6Utility (σ χ φ C Z : ℝ) (N : ℝ → ℝ) : ℝ :=
  (crra σ C - χ * ∫ j in (0 : ℝ)..1, N j ^ (1 + φ) / (1 + φ)) * Z

/-- Galí (2015), p. 202: with indivisible labour and full risk sharing, the household's
utility equals the Chapter 6 utility, for every employment profile `N(·)` (no integrability
hypothesis is needed: the inner integrals agree pointwise). -/
theorem householdUtility_eq_ch6 {σ χ φ : ℝ} (hφ : -1 < φ) (C Z : ℝ) (N : ℝ → ℝ) :
    householdUtility σ χ φ C Z N = ch6Utility σ χ φ C Z N := by
  unfold householdUtility ch6Utility
  have h : ∀ j, ∫ s in (0 : ℝ)..N j, s ^ φ = N j ^ (1 + φ) / (1 + φ) := fun j => by
    have := integral_disutility (χ := 1) hφ (N j)
    simpa using this
  simp_rw [h]

/-- Galí (2015), p. 204: the marginal disutility of employing one more member of a type with
`N` members employed is `χ N^φ` (the disutility of the marginal member), for `φ > 0`. -/
theorem hasDerivAt_disutility {χ φ : ℝ} (hφ : 0 < φ) (N : ℝ) :
    HasDerivAt (fun M => ∫ s in (0 : ℝ)..M, χ * s ^ φ) (χ * N ^ φ) N := by
  have hfun : (fun M => ∫ s in (0 : ℝ)..M, χ * s ^ φ) = fun M => χ * M ^ (1 + φ) / (1 + φ) :=
    funext fun M => integral_disutility (by linarith) M
  rw [hfun]
  have h1 : HasDerivAt (fun M : ℝ => M ^ (1 + φ)) ((1 + φ) * N ^ (1 + φ - 1)) N :=
    Real.hasDerivAt_rpow_const (Or.inr (by linarith))
  have h2 := (h1.const_mul χ).div_const (1 + φ)
  refine h2.congr_deriv ?_
  have : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [show 1 + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 204: the marginal utility of consumption is `C^{−σ}`, for `C > 0` and
every `σ` (including the logarithmic case `σ = 1`). -/
theorem hasDerivAt_crra (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (crra σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : crra σ = Real.log := funext fun x => by simp [crra, hσ]
    rw [hfun, hσ, Real.rpow_neg hC.le, Real.rpow_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : crra σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [crra, hσ]
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - σ)) ((1 - σ) * C ^ (1 - σ - 1)) C :=
      Real.hasDerivAt_rpow_const (Or.inl hC.ne')
    have h2 := (h1.sub_const 1).div_const (1 - σ)
    refine h2.congr_deriv ?_
    have : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), p. 204 (using the household's welfare as the criterion): if the household's
consumption is `C₀ + ω M` when its members `s ∈ [0, M]` work at the real wage `ω`, the marginal
value of the member `s = M` working is `C^{−σ} ω − χ M^φ`, `C = C₀ + ω M > 0`. -/
theorem marginal_value {σ χ φ C₀ ω : ℝ} (hφ : 0 < φ) {M : ℝ} (hC : 0 < C₀ + ω * M) :
    HasDerivAt (fun K => crra σ (C₀ + ω * K) - ∫ s in (0 : ℝ)..K, χ * s ^ φ)
      ((C₀ + ω * M) ^ (-σ) * ω - χ * M ^ φ) M := by
  have hlin : HasDerivAt (fun K : ℝ => C₀ + ω * K) ω M := by
    simpa using ((hasDerivAt_id M).const_mul ω).const_add C₀
  have hc := (hasDerivAt_crra σ hC).comp M hlin
  exact HasDerivAt.sub hc (hasDerivAt_disutility hφ M)

/-- Galí (2015), p. 204: member `s` (disutility `χ s^φ`) gains weakly from working iff the
real wage exceeds the disutility expressed in consumption units:
`C^{−σ} ω − χ s^φ ≥ 0 ⟺ ω ≥ χ C^σ s^φ`, for `C > 0`. -/
theorem participates_iff {σ χ φ C ω s : ℝ} (hC : 0 < C) :
    0 ≤ C ^ (-σ) * ω - χ * s ^ φ ↔ χ * C ^ σ * s ^ φ ≤ ω := by
  have hpos : 0 < C ^ σ := Real.rpow_pos_of_pos hC σ
  have hinv : C ^ (-σ) = (C ^ σ)⁻¹ := Real.rpow_neg hC.le σ
  rw [hinv, sub_nonneg]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc (C ^ σ) (C ^ σ)⁻¹, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith [show χ * C ^ σ * s ^ φ = C ^ σ * (χ * s ^ φ) by ring]
  · intro h
    have h' : χ * s ^ φ * C ^ σ ≤ ω := by linarith
    rw [← le_div_iff₀ hpos] at h'
    rwa [inv_mul_eq_div]

/-! ### The marginal participant (5) -/

/-- Galí (2015), eq. (5), p. 204: the marginal supplier of type-`j` labour,
`L = (ω/(χ C^σ))^{1/φ}`, where `ω = W(j)/P`. -/
noncomputable def laborForce (σ χ φ C ω : ℝ) : ℝ := (ω / (χ * C ^ σ)) ^ φ⁻¹

/-- Galí (2015), eq. (5), p. 204: the marginal participant is nonnegative. -/
theorem laborForce_nonneg {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) :
    0 ≤ laborForce σ χ φ C ω :=
  Real.rpow_nonneg (div_nonneg hω (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).le) _

/-- Galí (2015), eq. (5), p. 204: `L^φ = ω/(χ C^σ)`. -/
theorem laborForce_rpow {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) (hφ : 0 < φ) :
    laborForce σ χ φ C ω ^ φ = ω / (χ * C ^ σ) :=
  Real.rpow_inv_rpow (div_nonneg hω (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).le) hφ.ne'

/-- Galí (2015), eq. (5), p. 204: for `L ≥ 0`, `ω = χ C^σ L^φ` holds iff `L` is the marginal
participant `(ω/(χ C^σ))^{1/φ}`; so (5) determines `L(j)` uniquely. -/
theorem eq5_iff {σ χ φ C ω L : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) (hφ : 0 < φ)
    (hL : 0 ≤ L) : ω = χ * C ^ σ * L ^ φ ↔ L = laborForce σ χ φ C ω := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  constructor
  · intro h
    have hq : ω / (χ * C ^ σ) = L ^ φ := by
      rw [h]
      field_simp
    unfold laborForce
    rw [hq, Real.rpow_rpow_inv hL hφ.ne']
  · intro h
    rw [h, laborForce_rpow hχ hC hω hφ]
    field_simp

/-- Galí (2015), p. 204: the set of members `s ≥ 0` willing to work at real wage `ω > 0`,
`{s ≥ 0 | χ C^σ s^φ ≤ ω}`, is exactly the interval `[0, L]`, `L` given by (5). -/
theorem participation_set_eq {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) :
    {s : ℝ | 0 ≤ s ∧ χ * C ^ σ * s ^ φ ≤ ω} = Set.Icc 0 (laborForce σ χ φ C ω) := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  refine and_congr_right fun hs => ?_
  rw [← Real.rpow_le_rpow_iff hs hL hφ, laborForce_rpow hχ hC hω hφ, le_div_iff₀ hk, mul_comm]

/-- Galí (2015), pp. 201, 204: within the unit interval of members, the participating
members of type `j` are exactly `[0, min L 1]`. -/
theorem participation_set_unit {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) :
    {s ∈ Set.Icc (0 : ℝ) 1 | χ * C ^ σ * s ^ φ ≤ ω} = Set.Icc 0 (min (laborForce σ χ φ C ω) 1) := by
  have h := participation_set_eq (σ := σ) hχ hC hω hφ
  ext s
  have hs := Set.ext_iff.mp h s
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff] at hs ⊢
  constructor
  · rintro ⟨⟨h0, h1⟩, hd⟩
    exact ⟨h0, (hs.mp ⟨h0, hd⟩).2, h1⟩
  · rintro ⟨h0, hL, h1⟩
    exact ⟨⟨h0, h1⟩, (hs.mpr ⟨h0, hL⟩).2⟩

/-- Galí (2015), eq. (5), p. 204: the marginal participant `L` is indifferent, i.e. its
disutility in consumption units equals the real wage, `χ C^σ L^φ = ω`. -/
theorem marginal_indifferent {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) : χ * C ^ σ * laborForce σ χ φ C ω ^ φ = ω :=
  ((eq5_iff hχ hC hω hφ (laborForce_nonneg hχ hC hω)).mpr rfl).symm

/-- Galí (2015), p. 204: members below the marginal participant, `0 ≤ s < L`, strictly gain
from working: `χ C^σ s^φ < ω`. -/
theorem inframarginal_strict {σ χ φ C ω s : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) (hs : 0 ≤ s) (hsL : s < laborForce σ χ φ C ω) : χ * C ^ σ * s ^ φ < ω := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have h := (Real.rpow_lt_rpow_iff hs (laborForce_nonneg hχ hC hω) hφ).mpr hsL
  rw [laborForce_rpow hχ hC hω hφ, lt_div_iff₀ hk] at h
  linarith

/-- Galí (2015), p. 204: members above the marginal participant, `s > L`, strictly lose
from working: `χ C^σ s^φ > ω`, so they stay out of the labour force. -/
theorem supramarginal_refuses {σ χ φ C ω s : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) (hsL : laborForce σ χ φ C ω < s) : ω < χ * C ^ σ * s ^ φ := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  have h := (Real.rpow_lt_rpow_iff hL (by linarith) hφ).mpr hsL
  rw [laborForce_rpow hχ hC hω hφ, div_lt_iff₀ hk] at h
  linarith

/-- Galí (2015), pp. 201, 204: the marginal participant lies in the unit interval of members,
`L ≤ 1`, iff the real wage does not exceed the disutility of the member `s = 1`,
`ω ≤ χ C^σ`. -/
theorem laborForce_le_one_iff {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) : laborForce σ χ φ C ω ≤ 1 ↔ ω ≤ χ * C ^ σ := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  rw [← Real.rpow_le_rpow_iff hL zero_le_one hφ, laborForce_rpow hχ hC hω hφ, Real.one_rpow,
    div_le_one hk]

end Gali.Unemployment.IndivisibleLabor

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Introducing unemployment: participation, the unemployment rate and the wage Phillips curve

Galí (2015), Chapter 7, §7.1.2, pp. 204–207. Taking logs of the participation condition (5)
gives, type by type and **exactly**, `w(j) − p = σ c + φ l(j) + ξ` (`ξ = log χ`); integrating
over `j` gives, again exactly, `∫ w(j) dj − p = σ c + φ ∫ l(j) dj + ξ`. The aggregate
participation equation (6), `w − p = σ c + φ l + ξ`, replaces `∫ w(j)` by the log wage index
`w` and `∫ l(j)` by the log labour force `l = log ∫ L(j) dj`: this is the ONLY approximation,
and it is first order (survey error 4) — along any family of wage distributions
`w(j) = w̄ + s z(j)` the residual of (6) vanishes with zero derivative at `s = 0`.

The unemployment rate (7) is `u ≡ l − n`, so `1 − N/L = 1 − e^{−u}`, within `u²/2` of `u`
for `u ≥ 0` (fn. 6). The average wage markup `μ^w = (w − p) − (σ c + φ n + ξ)` then
satisfies (8) `μ^w = φ u` exactly; the natural rate (10) is `uⁿ = μ^w/φ`; and the wage NKPC
(4) becomes the New Keynesian wage Phillips curve (11) `π^w = β E π^w' − λ_w φ (u − uⁿ)`.
With flexible wages (`θ_w = 0`) the wage markup is constant and `u ≡ uⁿ` (p. 206).

## Main results

* `eq6_type`: (5) in levels ⇒ `w(j) − p = σ c + φ l(j) + ξ` exactly.
* `eq6_integrated`: the exact aggregate relation `∫ w(j) − p = σ c + φ ∫ l(j) + ξ`.
* `eq6_residual_eq`: the residual of (6) is exactly `(w − ∫ w(j)) − φ (l − ∫ l(j))`.
* `wageIndex_first_order`, `laborForce_first_order`, `eq6_first_order`: the two aggregation
  gaps and the residual of (6) are zero with zero derivative at the symmetric point.
* `unemploymentRate_eq`, `rate_le_u`, `abs_rate_sub_u_le` (fn. 6), and
  `abs_rate_sub_u_bound_fails_neg`: the bound `u²/2` fails for negative `u`.
* `eq8_iff`: given the definition of `μ^w` and (7), (6) ⇔ (8) `μ^w = φ u`.
* `natRate_eq`, `natRate_pos`: (10) `uⁿ = μ^w/φ` and `uⁿ > 0` when `μ^w > 0`.
* `wageNKPC_iff_eq11`: (4) ⇔ (11) given (8) and (10).
* `flexible_iff`, `flexible_unemployment_constant`, `fluctuations_require_rigidity`: with
  `θ_w = 0`, the wage-setting rule holds iff `μ̂^w ≡ 0` iff `u ≡ uⁿ`; hence a deviation of `u`
  from `uⁿ` requires `θ_w ≠ 0`.
* `sticky_unemployment_gap_consistent`: conversely, with sticky wages every bounded adapted
  unemployment-gap path is consistent with (11), with a unique bounded wage-inflation path.
-/

namespace Gali.Unemployment.UnemploymentDef

open MeasureTheory ProbabilityTheory

/-! ### (6) type by type and integrated: exact -/

/-- Galí (2015), eq. (5) ⇒ (6) type by type, p. 204: taking logs of
`W(j)/P = χ C^σ L(j)^φ` (all positive) gives **exactly**
`log W(j) − log P = σ log C + φ log L(j) + log χ`. -/
theorem eq6_type {W P C L χ σ φ : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C) (hL : 0 < L)
    (hχ : 0 < χ) (h5 : W / P = χ * C ^ σ * L ^ φ) :
    Real.log W - Real.log P = σ * Real.log C + φ * Real.log L + Real.log χ := by
  have h := congrArg Real.log h5
  rw [Real.log_div hW.ne' hP.ne', Real.log_mul (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).ne'
    (Real.rpow_pos_of_pos hL φ).ne', Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hC, Real.log_rpow hL] at h
  linarith

variable {J : Type*} [MeasurableSpace J] {μ : Measure J}

/-- Galí (2015), eq. (6), p. 204 (**exact integrated form**): if `w(j) − p = σ c + φ l(j) + ξ`
for every type `j` and `l` is integrable for the probability measure of types (the book's
`[0, 1]`), then `∫ w(j) dj − p = σ c + φ ∫ l(j) dj + ξ` exactly. -/
theorem eq6_integrated [IsProbabilityMeasure μ] {w l : J → ℝ} {p σ c φ ξ : ℝ}
    (hl : Integrable l μ) (h6 : ∀ j, w j - p = σ * c + φ * l j + ξ) :
    ∫ j, w j ∂μ - p = σ * c + φ * ∫ j, l j ∂μ + ξ := by
  have hw : w = fun j => (p + σ * c + ξ) + φ * l j := funext fun j => by linarith [h6 j]
  rw [hw, integral_add (integrable_const _) (hl.const_mul φ), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-! ### The aggregation gaps are first order -/

/-- Galí (2015), eq. (4) of Chapter 6, p. 165: the wage index
`W = (∫ W(j)^{1−ε_w} dj)^{1/(1−ε_w)}` (restated from the Chapter 6 project,
`LaborAggregation.cesIndex`). -/
noncomputable def cesIndex (μ : Measure J) (ε : ℝ) (W : J → ℝ) : ℝ :=
  (∫ j, W j ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), p. 204: the aggregate labour force `L = ∫ L(j) dj`, with `L(j) = exp l(j)`. -/
noncomputable def laborForceAgg (μ : Measure J) (l : J → ℝ) : ℝ := ∫ j, Real.exp (l j) ∂μ

/-- Galí (2015), p. 204 (tool): bounded measurable `z` has integrable exponentials
(restated from the Chapter 6 project, `LaborAggregation.integrable_exp_mul`). -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (t : ℝ) : Integrable (fun j => Real.exp (t * z j)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z j ≤ |t * z j| := le_abs_self _
    _ = |t| * |z j| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB j) (abs_nonneg t)

/-- Galí (2015), p. 204 (tool): a bounded measurable `z` is integrable. -/
theorem integrable_of_bound [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) : Integrable z μ :=
  Integrable.of_bound hz.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)

/-- Galí (2015), p. 204 (tool): `s ↦ K(a s)` has derivative `a ∫ z` at `0`, `K` the
cumulant-generating function of a bounded `z` (restated from the Chapter 6 project,
`LaborAggregation.hasDerivAt_cgf_mul`). -/
theorem hasDerivAt_cgf_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    HasDerivAt (fun s => cgf z μ (a * s)) (a * ∫ j, z j ∂μ) 0 := by
  have hset : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hset, interior_univ]
    trivial
  have hd : HasDerivAt (cgf z μ) (∫ j, z j ∂μ) (a * 0) := by
    have := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at this
    rw [mul_zero]
    simpa using this
  have hl : HasDerivAt (fun s : ℝ => a * s) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  exact (hd.comp 0 hl).congr_deriv (by ring)

/-- Galí (2015), p. 204: along `W(j) = exp(w̄ + s z(j))`, **exactly**
`log W = w̄ + K((1 − ε) s)/(1 − ε)`, `K` the cumulant-generating function of `z`. -/
theorem log_cesIndex_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (wbar s : ℝ) :
    Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
      = wbar + cgf z μ ((1 - ε) * s) / (1 - ε) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ j, Real.exp (wbar + s * z j) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * wbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ j, Real.exp (wbar + s * z j) ^ (1 - ε)
        = Real.exp ((1 - ε) * wbar) * Real.exp ((1 - ε) * s * z j) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  have hpos : 0 < Real.exp ((1 - ε) * wbar) * mgf z μ ((1 - ε) * s) :=
    mul_pos (Real.exp_pos _) (hM _)
  unfold cesIndex
  rw [hsum, Real.log_rpow hpos, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  field_simp

/-- Galí (2015), p. 204: along `l(j) = l̄ + s z(j)`, **exactly**
`log ∫ exp l(j) dj = l̄ + K(s)`. -/
theorem log_laborForce_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (lbar s : ℝ) :
    Real.log (laborForceAgg μ (fun j => lbar + s * z j)) = lbar + cgf z μ s := by
  have hM : 0 < mgf z μ s := mgf_pos (integrable_exp_mul hz hB s)
  have hsum : laborForceAgg μ (fun j => lbar + s * z j) = Real.exp lbar * mgf z μ s := by
    unfold laborForceAgg
    simp_rw [Real.exp_add]
    rw [integral_const_mul]
    rfl
  rw [hsum, Real.log_mul (Real.exp_pos _).ne' hM.ne', Real.log_exp, cgf]

/-- Galí (2015), p. 204 (**`w ≃ ∫ w(j) dj` is first order**): along `w(j) = w̄ + s z(j)` with
bounded measurable `z`, the gap `log W(s) − ∫ w(j) dj` is `0` at `s = 0` with derivative `0`. -/
theorem wageIndex_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (wbar : ℝ) :
    Real.log (cesIndex μ ε (fun j => Real.exp (wbar + 0 * z j))) - ∫ j, (wbar + 0 * z j) ∂μ
        = 0 ∧
      HasDerivAt (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
        - ∫ j, (wbar + s * z j) ∂μ) 0 0 := by
  have hzi := integrable_of_bound (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hint : ∀ s, ∫ j, (wbar + s * z j) ∂μ = wbar + s * ∫ j, z j ∂μ := fun s => by
    rw [integral_add (integrable_const _) (hzi.const_mul s), integral_const_mul]
    simp
  have hfun : (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
      - ∫ j, (wbar + s * z j) ∂μ)
      = fun s => cgf z μ ((1 - ε) * s) / (1 - ε) - s * ∫ j, z j ∂μ := funext fun s => by
    rw [log_cesIndex_family hz hB hε, hint]
    ring
  refine ⟨by rw [log_cesIndex_family hz hB hε, hint]; simp [cgf_zero], ?_⟩
  rw [hfun]
  have h1 := (hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).div_const (1 - ε)
  have h2 := (hasDerivAt_id (0 : ℝ)).mul_const (∫ j, z j ∂μ)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp
  simp

/-- Galí (2015), p. 204 (**`l ≃ ∫ l(j) dj` is first order**): along `l(j) = l̄ + s z(j)` with
bounded measurable `z`, the gap `log ∫ L(j) dj − ∫ l(j) dj` is `0` at `s = 0` with
derivative `0`. -/
theorem laborForce_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (lbar : ℝ) :
    Real.log (laborForceAgg μ (fun j => lbar + 0 * z j)) - ∫ j, (lbar + 0 * z j) ∂μ = 0 ∧
      HasDerivAt (fun s => Real.log (laborForceAgg μ (fun j => lbar + s * z j))
        - ∫ j, (lbar + s * z j) ∂μ) 0 0 := by
  have hzi := integrable_of_bound (μ := μ) hz hB
  have hint : ∀ s, ∫ j, (lbar + s * z j) ∂μ = lbar + s * ∫ j, z j ∂μ := fun s => by
    rw [integral_add (integrable_const _) (hzi.const_mul s), integral_const_mul]
    simp
  have hfun : (fun s => Real.log (laborForceAgg μ (fun j => lbar + s * z j))
      - ∫ j, (lbar + s * z j) ∂μ) = fun s => cgf z μ (1 * s) - s * ∫ j, z j ∂μ :=
    funext fun s => by
      rw [log_laborForce_family hz hB, hint, one_mul]
      ring
  refine ⟨by rw [log_laborForce_family hz hB, hint]; simp [cgf_zero], ?_⟩
  rw [hfun]
  have h1 := hasDerivAt_cgf_mul (μ := μ) hz hB 1
  have h2 := (hasDerivAt_id (0 : ℝ)).mul_const (∫ j, z j ∂μ)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  simp

/-- Galí (2015), eq. (6), p. 204 (**the residual of (6) is exactly the aggregation gaps**): if
(6) holds type by type and `l(·)` is integrable, then for any aggregate `w`, `l`,
`(w − p) − (σ c + φ l + ξ) = (w − ∫ w(j)) − φ (l − ∫ l(j))`. -/
theorem eq6_residual_eq [IsProbabilityMeasure μ] {wj lj : J → ℝ} {p σ c φ ξ : ℝ}
    (hl : Integrable lj μ) (h6 : ∀ j, wj j - p = σ * c + φ * lj j + ξ) (w l : ℝ) :
    (w - p) - (σ * c + φ * l + ξ) = (w - ∫ j, wj j ∂μ) - φ * (l - ∫ j, lj j ∂μ) := by
  have := eq6_integrated hl h6
  linear_combination this

/-- Galí (2015), eq. (6), p. 204 (**(6) holds to first order**, survey error 4). Let wages be
`w(j) = w̄ + s z(j)` (`z` bounded measurable), let each type's labour force `l(j)` satisfy the
exact type-by-type relation (6), and let `w = log W` (the wage index, `ε_w ≠ 1`) and
`l = log ∫ L(j) dj`. Then the residual `R(s) = (w − p) − (σ c + φ l + ξ)` of the aggregate
equation (6) satisfies `R(0) = 0` and `R'(0) = 0`. -/
theorem eq6_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) {ε σ φ p c ξ wbar : ℝ} (hε : ε ≠ 1) (hφ : φ ≠ 0)
    {lj : ℝ → J → ℝ} (h6 : ∀ s j, wbar + s * z j - p = σ * c + φ * lj s j + ξ) :
    (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + 0 * z j))) - p)
        - (σ * c + φ * Real.log (laborForceAgg μ (lj 0)) + ξ) = 0 ∧
      HasDerivAt (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) - p)
        - (σ * c + φ * Real.log (laborForceAgg μ (lj s)) + ξ)) 0 0 := by
  set lbar := (wbar - p - σ * c - ξ) / φ
  have hlj : ∀ s, lj s = fun j => lbar + (s / φ) * z j := fun s => funext fun j => by
    have := h6 s j
    simp only [lbar]
    field_simp
    linear_combination -this
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR : ∀ s, (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) - p)
      - (σ * c + φ * Real.log (laborForceAgg μ (lj s)) + ξ)
      = cgf z μ ((1 - ε) * s) / (1 - ε) - φ * cgf z μ (φ⁻¹ * s) := fun s => by
    rw [log_cesIndex_family hz hB hε, hlj s, log_laborForce_family hz hB]
    simp only [lbar]
    rw [show s / φ = φ⁻¹ * s by ring]
    field_simp
    ring
  refine ⟨by rw [hR 0]; simp [cgf_zero], ?_⟩
  rw [funext hR]
  have h1 := (hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).div_const (1 - ε)
  have h2 := (hasDerivAt_cgf_mul (μ := μ) hz hB φ⁻¹).const_mul φ
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp
  ring

/-! ### The unemployment rate (7) and footnote 6 -/

/-- Galí (2015), eq. (7) and fn. 6, p. 205: with `u = l − n = log L − log N`
(`N, L > 0`), the conventional unemployment rate is `1 − N/L = 1 − e^{−u}`. -/
theorem unemploymentRate_eq {N L : ℝ} (hN : 0 < N) (hL : 0 < L) :
    1 - N / L = 1 - Real.exp (-(Real.log L - Real.log N)) := by
  rw [neg_sub, Real.exp_sub, Real.exp_log hN, Real.exp_log hL]

/-- Galí (2015), fn. 6, p. 205: `1 − e^{−u} ≤ u` for every `u`. -/
theorem rate_le_u (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  have := Real.add_one_le_exp (-u)
  linarith

/-- Galí (2015), fn. 6, p. 205 (tool): `e^{−u} ≤ 1 − u + u²/2` for `u ≥ 0`. -/
theorem exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  set g : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hg : ∀ x, HasDerivAt g (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + x) x := by
      have a := ((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_pow 2 x).div_const 2)
      refine a.congr_deriv ?_
      simp
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      have := (hasDerivAt_neg x).exp
      simpa [mul_comm] using this
    exact (HasDerivAt.sub h1 h2).congr_deriv (by ring)
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun x => (hg x).differentiableAt) fun x => ?_
    rw [(hg x).deriv]
    have := Real.add_one_le_exp (-x)
    linarith
  have h := hmono hu
  simp only [g] at h
  norm_num at h
  linarith

/-- Galí (2015), fn. 6, p. 205: `1 − N/L = 1 − e^{−u} ≃ u` near zero, quantitatively:
`|1 − e^{−u} − u| ≤ u²/2` for every `u ≥ 0`. -/
theorem abs_rate_sub_u_le {u : ℝ} (hu : 0 ≤ u) : |1 - Real.exp (-u) - u| ≤ u ^ 2 / 2 := by
  have h1 := rate_le_u u
  have h2 := exp_neg_le_quadratic hu
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Galí (2015), fn. 6, p. 205 (the bound is one-sided): for negative `u` the bound `u²/2`
fails; at `u = −1`, `|1 − e − (−1)| > 1/2`. -/
theorem abs_rate_sub_u_bound_fails_neg :
    (-1 : ℝ) ^ 2 / 2 < |1 - Real.exp (-(-1)) - (-1)| := by
  rw [neg_neg]
  have he := Real.exp_one_gt_d9
  rw [abs_of_neg (by linarith)]
  norm_num
  linarith

/-! ### (8) and (10) -/

/-- Galí (2015), p. 205: the average wage markup `μ^w = (w − p) − (σ c + φ n + ξ)`. -/
def wageMarkup (σ φ ξ w p c n : ℝ) : ℝ := (w - p) - (σ * c + φ * n + ξ)

/-- Galí (2015), eq. (8), p. 205: given the definition of `μ^w` and (7) `u = l − n`, the
participation equation (6) holds **iff** `μ^w = φ u`; so (8) is exact given (6). -/
theorem eq8_iff {σ φ ξ w p c n l : ℝ} :
    w - p = σ * c + φ * l + ξ ↔ wageMarkup σ φ ξ w p c n = φ * (l - n) := by
  unfold wageMarkup
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (10), p. 206: the natural rate of unemployment, `uⁿ = μ^w/φ`. -/
noncomputable def natRate (μw φ : ℝ) : ℝ := μw / φ

/-- Galí (2015), eq. (10), p. 206: absent wage rigidities the markup equals its desired value
`μ^w`, and by (8) `φ u = μ^w` iff `u = uⁿ = μ^w/φ` (`φ ≠ 0`). -/
theorem natRate_eq {μw φ u : ℝ} (hφ : φ ≠ 0) : φ * u = μw ↔ u = natRate μw φ := by
  unfold natRate
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 206: market power in the labour market (`μ^w > 0`) implies a positive
natural rate of unemployment, `uⁿ > 0` (for `φ > 0`). -/
theorem natRate_pos {μw φ : ℝ} (hμ : 0 < μw) (hφ : 0 < φ) : 0 < natRate μw φ :=
  div_pos hμ hφ

/-- Galí (2015), eqs. (8), (10), p. 206: the markup gap is proportional to the unemployment
gap, `μ^w_t − μ^w = φ (u_t − uⁿ)`, for `φ ≠ 0`. -/
theorem markupGap_eq {μw φ u : ℝ} (hφ : φ ≠ 0) : φ * u - μw = φ * (u - natRate μw φ) := by
  unfold natRate
  field_simp

/-! ### The New Keynesian wage Phillips curve (11) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (4), p. 203 (= Chapter 6 eq. (15), restated): the wage NKPC
`π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`, `μ̂^w_t = μ^w_t − μ^w`. -/
def WageNKPC (β lamW : ℝ) (pw muhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - lamW • muhat t

/-- Galí (2015), eq. (11), p. 207: the New Keynesian wage Phillips curve
`π^w_t = β E_t π^w_{t+1} − λ_w φ (u_t − uⁿ)`. -/
def WagePhillips (β lamW φ un : ℝ) (pw u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • (u t - fun _ => un)

/-- Galí (2015), eqs. (4), (8), (10), (11), pp. 203–207: if the average wage markup satisfies
(8) `μ^w_t = φ u_t` at every date and `μ̂^w_t = μ^w_t − μ^w`, then the wage NKPC (4) holds
**iff** the wage Phillips curve (11) holds with `uⁿ = μ^w/φ` (`φ ≠ 0`). -/
theorem wageNKPC_iff_eq11 {β lamW φ μw : ℝ} (hφ : φ ≠ 0) {pw u muW : ℕ → Ω → ℝ}
    (h8 : ∀ t, muW t = φ • u t) :
    WageNKPC 𝔼 β lamW pw (fun t => muW t - fun _ => μw) ↔
      WagePhillips 𝔼 β lamW φ (natRate μw φ) pw u := by
  have hk : ∀ t, lamW • (muW t - fun _ => μw) = (lamW * φ) • (u t - fun _ => natRate μw φ) :=
    fun t => by
      rw [h8 t]
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc, ← markupGap_eq hφ]
  unfold WageNKPC WagePhillips
  simp only [hk]

/-! ### Flexible wages: `u ≡ uⁿ` (p. 206) -/

/-- Galí (2015), eq. (13) of Chapter 6, p. 169 (restated): the recursive wage-setting rule
`w*_{t+1} = βθ_w E_{t+1} w*_{t+2} + (1 − βθ_w)(w_{t+1} − (1 + ε_wφ)⁻¹ μ̂^w_{t+1})`. -/
def ResetRule (β θ ε φ : ℝ) (wstar w muhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wstar (t + 1) = (β * θ) • 𝔼.E (t + 1) (wstar (t + 2)) +
    (1 - β * θ) • (w (t + 1) - (1 + ε * φ)⁻¹ • muhat (t + 1))

/-- Galí (2015), eq. (14) of Chapter 6, p. 169 (restated): the wage index law of motion
`w_{t+1} = θ_w w_t + (1 − θ_w) w*_{t+1}`. -/
def IndexLaw (θ : ℝ) (w wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1)

/-- Galí (2015), p. 206 (**flexible wages**): with `θ_w = 0` (every wage reset every period),
`1 + ε_wφ ≠ 0` and the index law, the wage-setting rule holds iff the markup gap is
identically zero, `μ̂^w_{t+1} = 0` for all `t`. -/
theorem flexible_iff {β ε φ : ℝ} (hεφ : 1 + ε * φ ≠ 0) {wstar w muhat : ℕ → Ω → ℝ}
    (h14 : IndexLaw 0 w wstar) :
    ResetRule 𝔼 β 0 ε φ wstar w muhat ↔ ∀ t, muhat (t + 1) = 0 := by
  have hw : ∀ t, w (t + 1) = wstar (t + 1) := fun t => by
    have := h14 t
    simpa using this
  have hinv : (1 + ε * φ)⁻¹ ≠ 0 := inv_ne_zero hεφ
  unfold ResetRule
  simp only [mul_zero, zero_smul, sub_zero, one_smul, zero_add]
  constructor
  · intro h t
    have e := h t
    rw [hw t] at e
    have e2 : (1 + ε * φ)⁻¹ • muhat (t + 1) = 0 := sub_eq_self.mp e.symm
    exact (smul_eq_zero.mp e2).resolve_left hinv
  · intro h t
    rw [h t, smul_zero, sub_zero, hw t]

/-- Galí (2015), p. 206 (**with flexible wages unemployment equals its natural rate**): with
`θ_w = 0`, the index law and the wage-setting rule, and (8) `μ^w_t = φ u_t` with
`μ̂^w_t = μ^w_t − μ^w`, the unemployment rate is `u_{t+1} = uⁿ` at every date (`φ ≠ 0`).
Conversely `u ≡ uⁿ` makes the wage-setting rule hold. -/
theorem flexible_unemployment_constant {β ε φ μw : ℝ} (hφ : φ ≠ 0) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w u muW : ℕ → Ω → ℝ} (h14 : IndexLaw 0 w wstar) (h8 : ∀ t, muW t = φ • u t) :
    ResetRule 𝔼 β 0 ε φ wstar w (fun t => muW t - fun _ => μw) ↔
      ∀ t, u (t + 1) = fun _ => natRate μw φ := by
  rw [flexible_iff 𝔼 hεφ h14]
  refine forall_congr' fun t => ?_
  rw [h8 (t + 1)]
  constructor
  · intro h
    funext x
    have e := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
    exact (natRate_eq hφ).mp (by linarith)
  · intro h
    funext x
    have e := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [e, natRate]
    field_simp
    ring

/-- Galí (2015), p. 206 (**unemployment fluctuations require nominal wage rigidity**): if the
wage-setting rule and index law hold with stickiness `θ_w`, (8) holds, and at some date the
unemployment rate differs from its natural rate, then `θ_w ≠ 0`. -/
theorem fluctuations_require_rigidity {β θ ε φ μw : ℝ} (hφ : φ ≠ 0) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w u muW : ℕ → Ω → ℝ} (h14 : IndexLaw θ w wstar) (h8 : ∀ t, muW t = φ • u t)
    (h13 : ResetRule 𝔼 β θ ε φ wstar w (fun t => muW t - fun _ => μw))
    (hdev : ∃ t, u (t + 1) ≠ fun _ => natRate μw φ) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨t, ht⟩ := hdev
  exact ht (((flexible_unemployment_constant 𝔼 hφ hεφ h14 h8).mp h13) t)

/-- Galí (2015), pp. 206–207 (**with sticky wages any bounded unemployment gap is possible**):
for `0 ≤ β < 1` and any bounded adapted path `u` (any `λ_w`, `φ`), the wage Phillips curve (11)
has exactly one bounded wage-inflation solution, the forward sum
`π^w_t = −λ_w φ ∑_k β^k E_t (u_{t+k} − uⁿ)`; so (11) by itself does not pin `u` to `uⁿ`. -/
theorem sticky_unemployment_gap_consistent {β lamW φ un M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t x, |u t x| ≤ M) (hua : 𝔼.Adapted u) :
    ∃! pw : ℕ → Ω → ℝ, BoundedProc pw ∧ WagePhillips 𝔼 β lamW φ un pw u := by
  set g : ℕ → Ω → ℝ := fun t => -((lamW * φ) • (u t - fun _ => un))
  have hg : ∀ t x, |g t x| ≤ |lamW| * |φ| * (M + |un|) := fun t x => by
    simp only [g, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact (abs_sub _ _).trans (by linarith [hu t x])
  have hga : 𝔼.Adapted g := fun t => by
    simp only [g, map_neg, map_smul, map_sub, hua t, 𝔼.const]
  have heq : ∀ pw : ℕ → Ω → ℝ, WagePhillips 𝔼 β lamW φ un pw u ↔
      ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + g t := fun pw => by
    unfold WagePhillips
    simp only [g, sub_eq_add_neg]
  refine ⟨𝔼.forwardSeries β g, ⟨𝔼.forwardSeries_bounded hβ0 hβ1 hg,
    (heq _).mpr fun t => 𝔼.forwardSeries_solves hβ0 hβ1 hg hga t⟩, ?_⟩
  rintro pw ⟨hb, hpw⟩
  exact 𝔼.eq_forwardSeries hβ0 hβ1 hg hga ((heq pw).mp hpw) hb

end Gali.Unemployment.UnemploymentDef

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium with unemployment

Galí (2015), Chapter 7, §7.2, pp. 207–208. The equilibrium conditions are the Chapter 6
gap-form equations — the DIS (12), the price NKPC (13), the wage-gap identity (15) — with the
wage Phillips curve written in the unemployment gap, (14) `π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`,
plus the static equation (16) `φ û_t = μ̂^w_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t`.

Footnote 8: given (16), (14) is exactly the Chapter 6 wage equation (20)
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `κ_w = λ_w (σ + φ/(1 − α))`. Hence the
Chapter 7 system is the Chapter 6 system plus the static equation (16), which determines the
new variable `û` (for `φ ≠ 0`); bounded solutions correspond one-to-one, and determinacy
transfers in both directions.

The gap-form equations are restated from the Chapter 6 project (`GapForm`, `System`). The
matrix system (24), its solution concept and the p. 174 determinacy theorem come from this
project's `Unemployment.Determinacy4` (the Chapter 6 module copied in): `Par`, `bookPar`,
`Dyn.IsSol`, `Dyn.Determinate`, `Dyn.eq24_iff`, `determinacy_iff`. The transfer lemma
`determinate_iff_ch6` shows that the Chapter 7 system under any rule (23) is determinate iff
the Chapter 6 system is; with `determinacy_iff` this gives the unconditional
`determinacy_ch7_iff` and the determinacy of the Taylor rule (17), `rule17_determinate`.

## Main results

* `eq16_levels`: (16) from the levels: (8), (10), the wage markup definition, labour demand
  (9) and the natural allocation.
* `eq14_iff_eq20` (fn. 8): given (16), (14) ⇔ Chapter 6's (20).
* `ch7_iff_ch6`: the Chapter 7 system (12)–(16) ⇔ the Chapter 6 system (22), (18), (20), (21)
  together with `û_t = φ⁻¹ (ω̃_t − (σ + φ/(1 − α)) ỹ_t)`.
* `isSol7_iff`: the same at the level of the matrix system with initial condition,
  adaptedness and predeterminedness.
* `determinate_iff_ch6`: determinacy of the Chapter 7 system ⇔ determinacy of (24).
* `determinacy_ch7_iff`, `determinacy_ch7_iff_phiY_zero`: the Chapter 7 equilibrium is
  determinate iff `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1` (p. 174 condition).
* `rule17_determinate`: under (17) (`φ_π = 1.5`, `φ_y = 0.125`) the Chapter 7 equilibrium is
  determinate for all admissible parameters, in particular at the baseline calibration.
-/

namespace Gali.Unemployment.Equilibrium

/-! ### (16) from the levels -/

/-- Galí (2015), eq. (16), p. 208: with the average wage markup
`μ^w_t = ω_t − (σ c_t + φ n_t + ξ)`, `c = y`, (8) `μ^w_t = φ u_t`, (10) `uⁿ = μ^w/φ`,
labour demand (9) `(1 − α) n = y − a` (also at the natural allocation) and the natural real
wage `ωⁿ = σ yⁿ + φ nⁿ + ξ + μ^w` (flexible wages: markup at its desired level), the
unemployment gap satisfies `φ (u_t − uⁿ) = μ^w_t − μ^w = ω̃_t − (σ + φ/(1 − α)) ỹ_t`. -/
theorem eq16_levels {σ φ α ξ μw a y yn n nn w wn u : ℝ} (hα1 : α ≠ 1) (hφ : φ ≠ 0)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = σ * yn + φ * nn + ξ + μw) (h8 : w - (σ * y + φ * n + ξ) = φ * u) :
    φ * (u - UnemploymentDef.natRate μw φ) = (w - (σ * y + φ * n + ξ)) - μw ∧
      (w - (σ * y + φ * n + ξ)) - μw = (w - wn) - (σ + φ / (1 - α)) * (y - yn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  refine ⟨?_, ?_⟩
  · rw [h8, ← UnemploymentDef.markupGap_eq hφ]
  · have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
    have hq : φ / (1 - α) * (y - yn) = φ * (n - nn) := by
      rw [hy]
      field_simp
    rw [add_mul, hq, hwn]
    ring

/-! ### The gap-form equations (12)–(16) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (12), p. 207 (Chapter 6 eq. (22), restated): the DIS in gaps,
`ỹ_t = −σ⁻¹ (i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i pp rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (13), p. 207 (Chapter 6 eq. (18), restated): the price NKPC in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PriceGapNKPC (β κp lamP : ℝ) (pp ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • ygap t + lamP • wgap t

/-- Galí (2015), Chapter 6 eq. (20), p. 172 (restated; fn. 8 of Chapter 7):
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WageGapNKPC (β κw lamW : ℝ) (pw ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • ygap t - lamW • wgap t

/-- Galí (2015), eq. (14), p. 207: the wage Phillips curve in the unemployment gap,
`π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`. -/
def WageUnempNKPC (β lamW φ : ℝ) (pw uhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • uhat t

/-- Galí (2015), eq. (15), p. 207, in the lagged convention `wl t = ω̃_{t−1}`:
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
def WageGapLaw (wl pp pw dwn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wl (t + 1) = wl t + pw t - pp t - dwn t

/-- Galí (2015), eq. (16), p. 208: `φ û_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t`; the parameter `sw`
stands for `σ + φ/(1 − α)`. -/
def UnempGapEq (φ sw : ℝ) (ygap wgap uhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φ • uhat t = wgap t - sw • ygap t

/-- Galí (2015), fn. 8, p. 208 (**(14) + (16) ⇔ (20)**): given (16) at every date,
the unemployment-gap wage Phillips curve (14) is equivalent to the Chapter 6 wage equation (20)
with `κ_w = λ_w (σ + φ/(1 − α)) = λ_w sw`. -/
theorem eq14_iff_eq20 {β lamW φ sw : ℝ} {pw ygap wgap uhat : ℕ → Ω → ℝ}
    (h16 : UnempGapEq φ sw ygap wgap uhat) :
    WageUnempNKPC 𝔼 β lamW φ pw uhat ↔ WageGapNKPC 𝔼 β (lamW * sw) lamW pw ygap wgap := by
  have hk : ∀ t, (lamW * φ) • uhat t = lamW • wgap t - (lamW * sw) • ygap t := fun t => by
    rw [mul_smul, h16 t, smul_sub, mul_smul]
  unfold WageUnempNKPC WageGapNKPC
  refine forall_congr' fun t => ?_
  rw [hk t]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Galí (2015), §6.2 (Chapter 6, p. 173): the Chapter 6 non-policy block (22), (18), (20),
(21) with `ω̃_t = wl (t + 1)` (restated from the Chapter 6 project, `System.Equilibrium`). -/
def Ch6Equilibrium (σ β κp κw lamP lamW : ℝ) (ygap pp pw wl i rn dwn : ℕ → Ω → ℝ) : Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageGapNKPC 𝔼 β κw lamW pw ygap (fun t => wl (t + 1)) ∧ WageGapLaw wl pp pw dwn

/-- Galí (2015), §7.2, pp. 207–208: the Chapter 7 non-policy block (12)–(16) with
`ω̃_t = wl (t + 1)` and the unemployment gap `û`. -/
def Ch7Equilibrium (σ β κp lamP lamW φ sw : ℝ) (ygap pp pw wl uhat i rn dwn : ℕ → Ω → ℝ) :
    Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageUnempNKPC 𝔼 β lamW φ pw uhat ∧ WageGapLaw wl pp pw dwn ∧
    UnempGapEq φ sw ygap (fun t => wl (t + 1)) uhat

/-- Galí (2015), §7.2 and fn. 8, pp. 207–208 (**the Chapter 7 system is the Chapter 6 system
plus the static equation (16)**): for `φ ≠ 0`, `(ỹ, π^p, π^w, ω̃, û)` solves (12)–(16) iff
`(ỹ, π^p, π^w, ω̃)` solves the Chapter 6 system (22), (18), (20), (21) with
`κ_w = λ_w (σ + φ/(1 − α))` and `û_t = φ⁻¹ (ω̃_t − (σ + φ/(1 − α)) ỹ_t)`. -/
theorem ch7_iff_ch6 {σ β κp lamP lamW φ sw : ℝ} (hφ : φ ≠ 0)
    {ygap pp pw wl uhat i rn dwn : ℕ → Ω → ℝ} :
    Ch7Equilibrium 𝔼 σ β κp lamP lamW φ sw ygap pp pw wl uhat i rn dwn ↔
      Ch6Equilibrium 𝔼 σ β κp (lamW * sw) lamP lamW ygap pp pw wl i rn dwn ∧
        ∀ t, uhat t = φ⁻¹ • (wl (t + 1) - sw • ygap t) := by
  have h16iff : UnempGapEq φ sw ygap (fun t => wl (t + 1)) uhat ↔
      ∀ t, uhat t = φ⁻¹ • (wl (t + 1) - sw • ygap t) := by
    unfold UnempGapEq
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      rw [← h, smul_smul, inv_mul_cancel₀ hφ, one_smul]
    · intro h
      rw [h, smul_smul, mul_inv_cancel₀ hφ, one_smul]
  constructor
  · rintro ⟨hd, h13, h14, h15, h16⟩
    exact ⟨⟨hd, h13, (eq14_iff_eq20 𝔼 h16).mp h14, h15⟩, h16iff.mp h16⟩
  · rintro ⟨⟨hd, h18, h20, h21⟩, hu⟩
    have h16 := h16iff.mpr hu
    exact ⟨hd, h18, (eq14_iff_eq20 𝔼 h16).mpr h20, h21, h16⟩

/-! ### The Chapter 7 system and the transfer of determinacy -/

/-- Galí (2015), §7.2, pp. 207–208: `(x, û)` with `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` solves
the Chapter 7 system: (12) with the rule (23) substituted (row 1 of (24)), the price NKPC (13),
the wage Phillips curve in the unemployment gap (14), the wage-gap identity (15) and the static
equation (16) `φ û_t = ω̃_t − sw ỹ_t` (`sw = σ + φ/(1 − α)`), with initial gap `ω̃_{−1}`, all
variables adapted and `ω̃_t` known at `t`. -/
def IsSol7 (P : Determinacy4.Par) (φ sw : ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ)
    (x : ℕ → Fin 4 → Ω → ℝ) (uhat : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, (P.σ + P.φy) * x t 0 ω + P.φp * x t 1 ω + P.φw * x t 2 ω =
      P.σ * 𝔼.E t (x (t + 1) 0) ω + 𝔼.E t (x (t + 1) 1) ω + u t 0 ω) ∧
    (∀ t ω, x t 1 ω = P.β * 𝔼.E t (x (t + 1) 1) ω + P.κp * x t 0 ω
      + P.lamP * 𝔼.E t (x (t + 1) 3) ω) ∧
    (∀ t ω, x t 2 ω = P.β * 𝔼.E t (x (t + 1) 2) ω - P.lamW * φ * uhat t ω) ∧
    (∀ t ω, 𝔼.E t (x (t + 1) 3) ω = x t 3 ω + x t 2 ω - x t 1 ω - u t 1 ω) ∧
    (∀ t ω, φ * uhat t ω = 𝔼.E t (x (t + 1) 3) ω - sw * x t 0 ω) ∧
    x 0 3 = ω0 ∧ Determinacy4.Fwd.VAdapted 𝔼 x ∧ (∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) ∧
    𝔼.Adapted uhat

/-- Galí (2015), p. 208: the unemployment gap implied by (16),
`û_t = φ⁻¹ (ω̃_t − sw ỹ_t)`. -/
noncomputable def uhatOf (φ sw : ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => φ⁻¹ • (x (t + 1) 3 - sw • x t 0)

/-- Galí (2015), §7.2 and fn. 8, pp. 207–208 (**solutions correspond**): for `φ ≠ 0` and
`κ_w = λ_w sw`, `(x, û)` solves the Chapter 7 system iff `x` solves the Chapter 6 system (24)
(`Determinacy4.Dyn.IsSol`: same forcing, same initial condition) and `û = φ⁻¹ (ω̃ − sw ỹ)`. -/
theorem isSol7_iff {P : Determinacy4.Par} {φ sw : ℝ} (hφ : φ ≠ 0) (hκ : P.κw = P.lamW * sw)
    (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) (uhat : ℕ → Ω → ℝ) :
    IsSol7 𝔼 P φ sw u ω0 x uhat ↔
      Determinacy4.Dyn.IsSol 𝔼 P u ω0 x ∧ uhat = uhatOf φ sw x := by
  constructor
  · rintro ⟨h0, h1, h14, h3, h16, hi, hax, hpre, -⟩
    have hu : uhat = uhatOf φ sw x := by
      funext t ω
      have e := h16 t ω
      rw [hpre t] at e
      simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      linarith
    refine ⟨⟨fun t => (Determinacy4.Dyn.eq24_iff 𝔼 P x u t).mpr fun ω =>
      ⟨h0 t ω, h1 t ω, ?_, h3 t ω⟩, hi, hax, hpre⟩, hu⟩
    rw [h14 t ω, mul_assoc, h16 t ω, hκ]
    ring
  · rintro ⟨⟨heq, hi, hax, hpre⟩, rfl⟩
    have hr := fun t => (Determinacy4.Dyn.eq24_iff 𝔼 P x u t).mp (heq t)
    have h16 : ∀ t ω, φ * uhatOf φ sw x t ω = 𝔼.E t (x (t + 1) 3) ω - sw * x t 0 ω := by
      intro t ω
      rw [hpre t]
      simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    refine ⟨fun t ω => (hr t ω).1, fun t ω => (hr t ω).2.1, fun t ω => ?_,
      fun t ω => (hr t ω).2.2.2, h16, hi, hax, hpre, fun t => ?_⟩
    · rw [mul_assoc, h16 t ω, (hr t ω).2.2.1, hκ]
      ring
    · simp only [uhatOf, map_smul, map_sub, hpre t, hax t 0]

/-- Galí (2015), p. 208 (tool): the unemployment gap implied by (16) is bounded when `x` is. -/
theorem uhatOf_bounded {φ sw : ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hx : Determinacy4.Fwd.VBounded x) :
    BoundedProc (uhatOf φ sw x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨|φ⁻¹| * (M + |sw| * M), fun t ω => ?_⟩
  simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |x (t + 1) 3 ω - sw * x t 0 ω| ≤ |x (t + 1) 3 ω| + |sw * x t 0 ω| := abs_sub _ _
    _ ≤ M + |sw| * M := by
      rw [abs_mul]
      exact add_le_add (hM _ _ _) (mul_le_mul_of_nonneg_left (hM _ _ _) (abs_nonneg _))

/-- Galí (2015), §7.2: determinacy of the Chapter 7 system — for every bounded adapted forcing
and bounded initial real wage gap known at `0`, exactly one bounded solution `(x, û)`. -/
def Determinate7 (P : Determinacy4.Par) (φ sw : ℝ) : Prop :=
  ∀ (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ), Determinacy4.Fwd.VBounded u →
    Determinacy4.Fwd.VAdapted 𝔼 u → (∃ M, ∀ x, |ω0 x| ≤ M) → 𝔼.E 0 ω0 = ω0 →
      ∃! p : (ℕ → Fin 4 → Ω → ℝ) × (ℕ → Ω → ℝ),
        IsSol7 𝔼 P φ sw u ω0 p.1 p.2 ∧ Determinacy4.Fwd.VBounded p.1 ∧ BoundedProc p.2

/-- Galí (2015), §7.2, pp. 207–208 (**the transfer lemma**): for `φ ≠ 0` and
`κ_w = λ_w (σ + φ/(1 − α))`, the Chapter 7 system with unemployment is determinate iff the
Chapter 6 system (24) is (`Determinacy4.Dyn.Determinate`), for every rule (23). -/
theorem determinate_iff_ch6 {P : Determinacy4.Par} {φ sw : ℝ} (hφ : φ ≠ 0)
    (hκ : P.κw = P.lamW * sw) :
    Determinate7 𝔼 P φ sw ↔ Determinacy4.Dyn.Determinate 𝔼 P := by
  constructor
  · intro h7 u ω0 hub hua hω0 hω0a
    obtain ⟨⟨x, uh⟩, ⟨hs, hbx, -⟩, huniq⟩ := h7 u ω0 hub hua hω0 hω0a
    have hs6 := ((isSol7_iff 𝔼 hφ hκ u ω0 x uh).mp hs).1
    refine ⟨x, ⟨hs6, hbx⟩, ?_⟩
    rintro y ⟨hy, hby⟩
    have := huniq (y, uhatOf φ sw y)
      ⟨(isSol7_iff 𝔼 hφ hκ u ω0 y _).mpr ⟨hy, rfl⟩, hby, uhatOf_bounded hby⟩
    exact congrArg Prod.fst this
  · intro h6 u ω0 hub hua hω0 hω0a
    obtain ⟨x, ⟨hs, hbx⟩, huniq⟩ := h6 u ω0 hub hua hω0 hω0a
    refine ⟨(x, uhatOf φ sw x),
      ⟨(isSol7_iff 𝔼 hφ hκ u ω0 x _).mpr ⟨hs, rfl⟩, hbx, uhatOf_bounded hbx⟩, ?_⟩
    rintro ⟨y, uy⟩ ⟨hy, hby, -⟩
    obtain ⟨hy6, rfl⟩ := (isSol7_iff 𝔼 hφ hκ u ω0 y uy).mp hy
    rw [huniq y ⟨hy6, hby⟩]

/-! ### Determinacy of the equilibrium with unemployment (pp. 174, 208–210) -/

/-- **Galí (2015), §7.2 with the p. 174 theorem — determinacy with unemployment.** Let
`0 < β < 1`, `σ > 0`, `φ > 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`, `φ_p, φ_w, φ_y ≥ 0` and
`κ_p = α λ_p/(1 − α)`, `κ_w = λ_w (σ + φ/(1 − α))` (`Determinacy4.bookPar`). The equilibrium of
the Chapter 7 system (12)–(16) under rule (23) is determinate (unique bounded `(x, û)` for every
bounded adapted forcing and bounded initial real wage gap) iff
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
theorem determinacy_ch7_iff [Nonempty Ω] {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP)
    (hlw : 0 < lamW) (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW φp φw φy) φ (σ + φ / (1 - α)) ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  rw [determinate_iff_ch6 𝔼 hφ.ne' rfl]
  exact Determinacy4.determinacy_iff 𝔼 hβ0 hβ1 hσ hφ.le hα0 hα1 hlp hlw hfp hfw hfy

/-- Galí (2015), p. 174 with `φ_y = 0`, §7.2: the Chapter 7 equilibrium under
`i_t = ρ + φ_p π^p_t + φ_w π^w_t + v_t` is determinate iff `φ_p + φ_w > 1`. -/
theorem determinacy_ch7_iff_phiY_zero [Nonempty Ω] {β σ φ α lamP lamW φp φw : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW φp φw 0) φ (σ + φ / (1 - α)) ↔
      1 < φp + φw := by
  rw [determinate_iff_ch6 𝔼 hφ.ne' rfl]
  exact Determinacy4.determinacy_iff_phiY_zero 𝔼 hβ0 hβ1 hσ hφ.le hα0 hα1 hlp hlw hfp hfw

/-- Galí (2015), eq. (17), p. 210: under the Taylor rule
`i_t = 0.01 + 1.5 π^p_t + 0.125 ŷ_t + v_t` (rule (23) with `φ_p = 1.5`, `φ_w = 0`,
`φ_y = 0.125`) the Chapter 7 equilibrium with unemployment is determinate for all
`0 < β < 1`, `σ > 0`, `φ > 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0` — in particular at the book's
baseline calibration. -/
theorem rule17_determinate [Nonempty Ω] {β σ φ α lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW (3 / 2) 0 (1 / 8)) φ
      (σ + φ / (1 - α)) := by
  rw [determinacy_ch7_iff 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw (by norm_num) le_rfl (by norm_num)]
  have h1α : 0 < 1 - α := by linarith
  have hΘ : 0 < σ + (α + φ) / (1 - α) := by positivity
  have : 0 ≤ 1 / 8 * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
    have : 0 < 1 - β := by linarith
    positivity
  linarith

end Gali.Unemployment.Equilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy design and unemployment fluctuations

Galí (2015), Section 7.3, pp. 208–216.

## Main results

* **Calibration, p. 209**: `markup_eq_exp` (`M_w = exp(φ uⁿ)` from (10)),
  `epsW_markup_iff` (`ε_w/(ε_w − 1) = M ⇔ ε_w = M/(M − 1)`), `exp_quarter_bounds`,
  `calibration_epsW` (`ε_w ∈ (4.5, 4.55)`), `calibration_markup` (net markup `∈ (0.28, 0.29)`),
  `calibration_book_epsW` (the printed `ε_w = 4.5` is a rounding: survey error 6).
* **Labour-force wealth effect, (17) and Fig. 7.2**: the participation equation (6) solved for `l`
  (`laborForce`), its exact derivative `hasDerivAt_laborForce` (`∂l/∂c = −σ/φ < 0` given the real
  wage), `laborForce_strictAnti`; the nonlinear marginal participant (5)
  (`marginalParticipant_eq5`, `log_marginalParticipant`, `hasDerivAt_log_marginalParticipant`).
* **fn. 12** (`θ_w → 0` kills unemployment fluctuations): `abs_unemp_le` (pathwise bound
  `|û_t| ≤ (1 + β) B/(λ_w φ)` from (14)), `tendsto_lamWOf_atTop` (`λ_w → ∞` as `θ_w → 0⁺`),
  `unemployment_vanishes` (uniformly along uniformly bounded `π^w` paths),
  `unemployment_volatility_vanishes` (conditional second moments), the counterexample
  `unemployment_need_not_vanish` (the uniform bound cannot be dropped), and the flexible-wage limit
  model `flexible_wages_no_unemployment_gap`.
* **Optimal policy, (18)–(21)**: the Chapter 6 deterministic commitment theory is restated
  (`Det.isOptimal_of_foc`, `Det.isOptimal_iff_foc`, `Det.demand_zero_optimal`, ...); fn. 8
  `fn8_wage_pc`; `feasible7_iff` (constraints (13)–(16) ⇔ Chapter 6 constraints + (16) for `û`);
  `isOptimal7_iff` (the Chapter 7 problem is the Chapter 6 problem); `foc7_iff_ch6` (the printed
  (18)–(21) ARE the Chapter 6 conditions (30)–(33): survey error 1, "chapter 3" on p. 212);
  `isOptimal7_iff_eq`, `existsUnique_optimal7`, `isOptimal7_iff_foc` (the optimum is the Chapter 6
  optimum with `û = (ω̃ − (σ + φ/(1 − α)) ỹ)/φ`).
* **p. 213, technology under `σ = 1`**: `psiYA_sigma_one`, `psiWA_sigma_one`,
  `participation_consistent` ((6) holds for `l = n + u`), `efficient_technology_sigma_one`
  (`y = a`, `n = l = û = 0`, real wage `= a`), `efficient_employment_zero_iff` (`n = 0` at the
  efficient allocation iff `σ = 1`).
* **p. 214, demand shocks**: `demand_shock_optimal_iff`, `demand_shock_labour_market` (all
  labour-market variables fully insulated).
* **(22)**: `rule22_level_iff_gap`, `rule22_book_intercept`, `rule22_level_not_steady`,
  `rule22_gap_steady`, `rule22_deviation` (the level/gap intercept imprecision, survey error 5).

Table 7.1 and Figures 7.2–7.6 are numerical simulations and are not formalised.
-/

namespace Gali.Unemployment.Policy

open Filter Topology

/-! ### Coefficients and lags -/

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (28), pp. 172, 179: the coefficients of the optimal-policy problem:
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

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (28), pp. 172, 179: the book's coefficients, with
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

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (21), p. 172: the lag `x_{t−1}` of a sequence with initial value `x_{−1} = x0`
(used for `ω̃_{t−1}` with `ω̃_{−1}` given, and for the multipliers with `ζ_{−1} = 0`). -/
def prev {α : Type*} (x0 : α) (x : ℕ → α) : ℕ → α
  | 0 => x0
  | t + 1 => x t

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: `x_{−1} = x0`. -/
@[simp] theorem prev_zero {α : Type*} (x0 : α) (x : ℕ → α) : prev x0 x 0 = x0 := rfl

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: the lag at date `t + 1` is the date-`t` value. -/
@[simp] theorem prev_succ {α : Type*} (x0 : α) (x : ℕ → α) (t : ℕ) : prev x0 x (t + 1) = x t :=
  rfl

/-! ### The Lagrangian identity -/

/-- Restated from the Chapter 6 project.
**Galí (2015), ch. 6, (30)–(33), p. 181 (the Lagrangian identity, one period)**:
if `(ỹ*, π^p*, π^w*,
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

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (the Lagrangian argument, abstract form): if `g_t = D_t + (h_{t+1} − h_t)`
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

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (transversality): if `∑ βᵗ x_t²` converges, `0 ≤ β < 1`, then
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

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (transversality for the predetermined real wage gap): if
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

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: `∑ βᵗ (a_t − b_t)²` converges when `∑ βᵗ a_t²` and `∑ βᵗ b_t²` do. -/
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

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (21), p. 172 (perfect foresight): the constraints
`π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, `π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`,
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, `t ≥ 0`, with `ω̃_{−1} = w0` given. -/
def Feasible (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) + c.kapW * y t - c.lamW * w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (30)–(33), p. 181 (perfect foresight): the first-order conditions with
multipliers `ζ₁, ζ₂, ζ₃` and `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOC (c : Coef) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, c.ay * y t + c.kapP * z1 t + c.kapW * z2 t = 0 ∧
    c.ap * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP * z1 t - c.lamW * z2 t + z3 t - c.β * z3 (t + 1) = 0

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: the multipliers are bounded. -/
def BoundedMult (z1 z2 z3 : ℕ → ℝ) : Prop := ∃ Z, ∀ t, |z1 t| ≤ Z ∧ |z2 t| ≤ Z ∧ |z3 t| ≤ Z

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the discounted period loss
`βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def lossTerm (c : Coef) (y pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.β ^ t * ((c.ay * y t ^ 2 + c.ap * pp t ^ 2 + c.aw * pw t ^ 2) / 2)

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the loss is finite. -/
def FiniteLoss (c : Coef) (y pp pw : ℕ → ℝ) : Prop := Summable (lossTerm c y pp pw)

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the loss `½ ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`
(used on finite-loss paths). -/
noncomputable def loss (c : Coef) (y pp pw : ℕ → ℝ) : ℝ := ∑' t, lossTerm c y pp pw t

/-- Restated from the Chapter 6 project.
Galí (2015), §6.4, p. 181: `(ỹ, π^p, π^w, ω̃)` solves the commitment problem: it is feasible,
has finite loss, and no feasible finite-loss path has a smaller loss. -/
def IsOptimal (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  Feasible c dn w0 y pp pw w ∧ FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w', Feasible c dn w0 y' pp' pw' w' → FiniteLoss c y' pp' pw' →
      loss c y pp pw ≤ loss c y' pp' pw'

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: on a finite-loss path `∑ βᵗ ỹ_t²`, `∑ βᵗ (π^p_t)²` and
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

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (21), p. 172: two feasible paths with the same `ω̃_{−1}` and the same shocks
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

/-- Restated from the Chapter 6 project.
**Galí (2015), ch. 6, (30)–(33), p. 181 (sufficiency of the first-order conditions,
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

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (optimality, deterministic)**: a feasible finite-loss path
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

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (uniqueness, deterministic)**: a feasible finite-loss path with
the same loss as a path satisfying (30)–(33) with bounded multipliers coincides with it (all
four variables; the real wage gap by (21)). -/
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

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (necessity and sufficiency of the first-order conditions,
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

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (existence and uniqueness, deterministic)**: if the first-order
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
namespace Det

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4.1, p. 181 (demand shocks, deterministic)**: with demand shocks only the
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

/-! ### Calibration, p. 209 -/

/-- Galí (2015), (10), p. 206, and p. 209: with `uⁿ = μ^w/φ` and `μ^w = log M_w` (`φ ≠ 0`), the
gross desired wage markup is `M_w = exp(φ uⁿ)`. -/
theorem markup_eq_exp {φ un Mw : ℝ} (hM : 0 < Mw) (hφ : φ ≠ 0)
    (h10 : un = Real.log Mw / φ) : Mw = Real.exp (φ * un) := by
  have h : φ * (Real.log Mw / φ) = Real.log Mw := by field_simp
  rw [h10, h, Real.exp_log hM]

/-- Galí (2015), p. 209: for `ε_w > 1` and `M > 1`, `M_w ≡ ε_w/(ε_w − 1) = M` holds iff
`ε_w = M/(M − 1)`. -/
theorem epsW_markup_iff {εw M : ℝ} (hε : 1 < εw) (hM : 1 < M) :
    εw / (εw - 1) = M ↔ εw = M / (M - 1) := by
  have h1 : εw - 1 ≠ 0 := (sub_pos.2 hε).ne'
  have h2 : M - 1 ≠ 0 := (sub_pos.2 hM).ne'
  rw [div_eq_iff h1, eq_div_iff h2]
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 209 (numerics): `1.2836 < e^{1/4} < 1.2841` (Taylor polynomial of degree 3
with Mathlib's remainder bound `Real.exp_bound`). -/
theorem exp_quarter_bounds : (1.2836 : ℝ) < Real.exp (1 / 4) ∧ Real.exp (1 / 4) < 1.2841 := by
  have h := Real.exp_bound (x := 1 / 4) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  have h2 := abs_le.1 h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  constructor <;> linarith [h2.1, h2.2]

/-- **Galí (2015), p. 209 (calibration of `ε_w`)**: with `φ = 5` and `uⁿ = 0.05`, the condition
`ε_w/(ε_w − 1) = exp(φ uⁿ)` (with `ε_w > 1`) gives `ε_w = e^{1/4}/(e^{1/4} − 1) ∈ (4.5, 4.55)`. -/
theorem calibration_epsW {εw : ℝ} (hε : 1 < εw)
    (h : εw / (εw - 1) = Real.exp (5 * 0.05)) :
    εw = Real.exp (1 / 4) / (Real.exp (1 / 4) - 1) ∧ 4.5 < εw ∧ εw < 4.55 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  rw [hq] at h
  obtain ⟨hl, hu⟩ := exp_quarter_bounds
  have he := (epsW_markup_iff hε (by linarith)).1 h
  have hpos : 0 < Real.exp (1 / 4) - 1 := by linarith
  refine ⟨he, ?_, ?_⟩
  · rw [he, lt_div_iff₀ hpos]; linarith
  · rw [he, div_lt_iff₀ hpos]; linarith

/-- **Galí (2015), p. 209 (average wage markup)**: at `φ = 5`, `uⁿ = 0.05` the net wage markup
`M_w − 1 = e^{1/4} − 1` lies in `(0.28, 0.29)` ("28 percent"). -/
theorem calibration_markup :
    (0.28 : ℝ) < Real.exp (5 * 0.05) - 1 ∧ Real.exp (5 * 0.05) - 1 < 0.29 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  rw [hq]
  obtain ⟨hl, hu⟩ := exp_quarter_bounds
  constructor <;> linarith

/-- **Galí (2015), p. 209 (survey error 6: rounding)**: the printed `ε_w = 4.5` does not satisfy
the calibration condition exactly (`4.5/3.5 = 9/7 ≠ e^{1/4}`); it implies a net markup
`2/7 ≈ 28.6%`, while the exact calibration gives `ε_w ≈ 4.52` and a markup `≈ 28.4%`. The log
markup `μ^w = φ uⁿ` is exactly `0.25`. -/
theorem calibration_book_epsW :
    (4.5 : ℝ) / (4.5 - 1) - 1 = 2 / 7 ∧ (4.5 : ℝ) / (4.5 - 1) ≠ Real.exp (5 * 0.05) ∧
      (5 : ℝ) * 0.05 = 0.25 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  obtain ⟨-, hu⟩ := exp_quarter_bounds
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [hq]
  intro h
  have : (4.5 : ℝ) / (4.5 - 1) = 9 / 7 := by norm_num
  rw [this] at h
  linarith

/-! ### The labour-force wealth effect, (17) and Fig. 7.2 -/

/-- Galí (2015), (6), p. 204: the participation equation `w − p = σ c + φ l + ξ` solved for the
labour force, `l = (ω − σ c − ξ)/φ`, given the real wage `ω = w − p` and consumption `c`. -/
noncomputable def laborForce (σ φ ξ ω c : ℝ) : ℝ := (ω - σ * c - ξ) / φ

/-- Galí (2015), (6), p. 204: `laborForce` satisfies (6), and is its unique solution
(`φ ≠ 0`). -/
theorem laborForce_iff {σ φ ξ ω c l : ℝ} (hφ : φ ≠ 0) :
    ω = σ * c + φ * l + ξ ↔ l = laborForce σ φ ξ ω c := by
  unfold laborForce
  rw [eq_div_iff hφ]
  constructor <;> intro h <;> linarith

/-- **Galí (2015), p. 210 (the wealth effect on participation)**: given the real wage,
`∂l/∂c = −σ/φ` (exact derivative of (6)). -/
theorem hasDerivAt_laborForce (σ φ ξ ω c : ℝ) :
    HasDerivAt (fun c => laborForce σ φ ξ ω c) (-σ / φ) c := by
  have h := HasDerivAt.div_const
    (HasDerivAt.sub_const ξ (HasDerivAt.const_sub ω (HasDerivAt.const_mul σ (hasDerivAt_id' c)))) φ
  exact HasDerivAt.congr_deriv h (by ring)

/-- **Galí (2015), p. 210 (countercyclical labour force)**: for `σ, φ > 0` the wealth effect is
negative, `−σ/φ < 0`, and the labour force is strictly decreasing in consumption at a given real
wage: a consumption decline (a monetary tightening, Fig. 7.2) raises participation. -/
theorem laborForce_strictAnti {σ φ ξ ω : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    -σ / φ < 0 ∧ StrictAnti (laborForce σ φ ξ ω) := by
  refine ⟨div_neg_of_neg_of_pos (by linarith) hφ, fun c c' hc => ?_⟩
  unfold laborForce
  rw [div_lt_div_iff_of_pos_right hφ]
  nlinarith

/-- Galí (2015), (5), p. 204: the marginal supplier of a labour type,
`L = (ω/(χ C^σ))^{1/φ}`, given the real wage `ω = W/P > 0` and consumption `C > 0`. -/
noncomputable def marginalParticipant (σ φ χ ω C : ℝ) : ℝ := (ω / (χ * C ^ σ)) ^ (1 / φ)

/-- **Galí (2015), (5), p. 204**: the marginal participant satisfies `ω = χ C^σ L^φ`. -/
theorem marginalParticipant_eq5 {σ φ χ ω C : ℝ} (hφ : φ ≠ 0) (hχ : 0 < χ) (hω : 0 < ω)
    (hC : 0 < C) : ω = χ * C ^ σ * marginalParticipant σ φ χ ω C ^ φ := by
  have hd : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  unfold marginalParticipant
  rw [← Real.rpow_mul (div_pos hω hd).le, one_div_mul_cancel hφ, Real.rpow_one]
  field_simp

/-- **Galí (2015), (5)–(6), p. 204 (exactness of (6) in `c`)**: with `c = log C`,
`log L = (log ω − σ c − log χ)/φ`, i.e. the log of the marginal participant is exactly
`laborForce` with `ξ = log χ`. -/
theorem log_marginalParticipant {σ φ χ ω : ℝ} (hχ : 0 < χ) (hω : 0 < ω) (c : ℝ) :
    Real.log (marginalParticipant σ φ χ ω (Real.exp c)) =
      laborForce σ φ (Real.log χ) (Real.log ω) c := by
  have hp : 0 < Real.exp c ^ σ := Real.rpow_pos_of_pos (Real.exp_pos c) σ
  unfold marginalParticipant laborForce
  rw [Real.log_rpow (div_pos hω (mul_pos hχ hp)), Real.log_div hω.ne' (mul_pos hχ hp).ne',
    Real.log_mul hχ.ne' hp.ne', Real.log_rpow (Real.exp_pos c), Real.log_exp]
  ring

/-- **Galí (2015), p. 210 (wealth effect, nonlinear model)**: the elasticity of the marginal
participant (5) with respect to consumption, at a given real wage, is `−σ/φ`:
`d log L / d log C = −σ/φ`. -/
theorem hasDerivAt_log_marginalParticipant {σ φ χ ω : ℝ} (hχ : 0 < χ) (hω : 0 < ω) (c : ℝ) :
    HasDerivAt (fun c => Real.log (marginalParticipant σ φ χ ω (Real.exp c))) (-σ / φ) c := by
  have h : (fun c => Real.log (marginalParticipant σ φ χ ω (Real.exp c))) =
      fun c => laborForce σ φ (Real.log χ) (Real.log ω) c :=
    funext fun c => log_marginalParticipant hχ hω c
  rw [h]
  exact hasDerivAt_laborForce _ _ _ _ c

/-! ### fn. 12: as `θ_w → 0` unemployment fluctuations vanish -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (14), p. 207: the wage Phillips curve in the unemployment gap,
`π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`. -/
def WagePC (β lamW φ : ℝ) (pw u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • u t

/-- **Galí (2015), (14), p. 207 (pathwise bound)**: if `|π^w_t| ≤ B` for all dates and states,
then (14) forces `|û_t| ≤ (1 + β) B/(λ_w φ)`. -/
theorem abs_unemp_le {β lamW φ B : ℝ} (hβ : 0 ≤ β) (hl : 0 < lamW) (hφ : 0 < φ)
    {pw u : ℕ → Ω → ℝ} (h14 : WagePC 𝔼 β lamW φ pw u) (hB : ∀ t ω, |pw t ω| ≤ B) (t : ℕ)
    (ω : Ω) : |u t ω| ≤ (1 + β) * B / (lamW * φ) := by
  have hk : 0 < lamW * φ := mul_pos hl hφ
  have e := congrFun (h14 t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
  have hE := abs_le.1 (𝔼.abs_E_le (hB (t + 1)) t ω)
  have hp := abs_le.1 (hB t ω)
  have hu : u t ω * (lamW * φ) = β * 𝔼.E t (pw (t + 1)) ω - pw t ω := by linarith
  rw [le_div_iff₀ hk, ← abs_of_pos hk, ← abs_mul, hu]
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [hE.1, hE.2, hp.1, hp.2]

/-- Galí (2015), p. 204: the wage Phillips curve slope as a function of the Calvo parameter,
`λ_w(θ_w) = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lamWOf (β εw φ θw : ℝ) : ℝ := (1 - θw) * (1 - β * θw) / θw / (1 + εw * φ)

/-- **Galí (2015), fn. 12, p. 211**: `λ_w → ∞` as `θ_w → 0⁺` (`1 + ε_w φ > 0`). -/
theorem tendsto_lamWOf_atTop {β εw φ : ℝ} (hd : 0 < 1 + εw * φ) :
    Tendsto (lamWOf β εw φ) (𝓝[>] 0) atTop := by
  have hc : Continuous (fun θ : ℝ => (1 - θ) * (1 - β * θ)) := by fun_prop
  have h1 : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ)) (𝓝[>] 0) (𝓝 1) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h3 := (Tendsto.pos_mul_atTop one_pos h1 tendsto_inv_nhdsGT_zero).atTop_div_const hd
  refine Tendsto.congr (fun θ => ?_) h3
  simp [lamWOf, div_eq_mul_inv]

/-- **Galí (2015), fn. 12, p. 211 (unemployment fluctuations vanish as `θ_w → 0`)**: let, for each
`θ_w ∈ (0, 1)`, `(π^w(θ_w), û(θ_w))` satisfy (14) with slope `λ_w(θ_w)`, and let the wage
inflation paths be uniformly bounded, `|π^w_t(θ_w)| ≤ B`. Then `û(θ_w) → 0` as `θ_w → 0⁺`,
uniformly in dates and states. -/
theorem unemployment_vanishes {β εw φ B : ℝ} (hβ : 0 ≤ β) (hφ : 0 < φ) (hεw : 0 ≤ εw)
    (pw u : ℝ → ℕ → Ω → ℝ)
    (h14 : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, WagePC 𝔼 β (lamWOf β εw φ θ) φ (pw θ) (u θ))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ t ω, |pw θ t ω| ≤ B) :
    ∀ ε > 0, ∀ᶠ θ in 𝓝[>] 0, ∀ t ω, |u θ t ω| ≤ ε := by
  intro ε hε
  have hd : 0 < 1 + εw * φ := by positivity
  have hev := (tendsto_lamWOf_atTop (β := β) hd).eventually_ge_atTop
    (max 1 ((1 + β) * B / (φ * ε)))
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ hmem t ω
  have hl : 0 < lamWOf β εw φ θ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hθ)
  refine (abs_unemp_le 𝔼 hβ hl hφ (h14 θ hmem) (hB θ hmem) t ω).trans ?_
  rw [div_le_iff₀ (mul_pos hl hφ)]
  have h2 : (1 + β) * B / (φ * ε) ≤ lamWOf β εw φ θ := (le_max_right _ _).trans hθ
  rw [div_le_iff₀ (mul_pos hφ hε)] at h2
  linarith [show lamWOf β εw φ θ * (φ * ε) = ε * (lamWOf β εw φ θ * φ) by ring]

/-- **Galí (2015), fn. 12, p. 211 (volatility)**: under the hypotheses of
`unemployment_vanishes`, the conditional second moments `E_s û_t²` converge to zero as
`θ_w → 0⁺`, uniformly in `s`, `t` and the state. -/
theorem unemployment_volatility_vanishes {β εw φ B : ℝ} (hβ : 0 ≤ β) (hφ : 0 < φ)
    (hεw : 0 ≤ εw) (pw u : ℝ → ℕ → Ω → ℝ)
    (h14 : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, WagePC 𝔼 β (lamWOf β εw φ θ) φ (pw θ) (u θ))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ t ω, |pw θ t ω| ≤ B) :
    ∀ ε > 0, ∀ᶠ θ in 𝓝[>] 0, ∀ s t ω, |𝔼.E s (fun ω' => u θ t ω' ^ 2) ω| ≤ ε := by
  intro ε hε
  have hm : 0 < min 1 ε := lt_min one_pos hε
  filter_upwards [unemployment_vanishes 𝔼 hβ hφ hεw pw u h14 hB (min 1 ε) hm] with θ hθ s t ω
  refine 𝔼.abs_E_le (fun ω' => ?_) s ω
  have h1 := hθ t ω'
  have h2 : |u θ t ω' ^ 2| ≤ min 1 ε ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : min 1 ε ^ 2 ≤ min 1 ε := by
    rw [sq]; exact mul_le_of_le_one_left hm.le (min_le_left _ _)
  exact h2.trans (h3.trans (min_le_right _ _))

/-- **Galí (2015), fn. 12, p. 211 (the uniform bound cannot be dropped)**: for every slope
`λ_w` (so for every `θ_w`), `û ≡ 1` with the constant, bounded wage inflation
`π^w ≡ −λ_w φ/(1 − β)` solves (14): without a bound on `π^w` uniform in `θ_w`, unemployment
fluctuations need not vanish. -/
theorem unemployment_need_not_vanish {β φ : ℝ} (hβ1 : β < 1) (lamW : ℝ) :
    WagePC 𝔼 β lamW φ (fun _ _ => -(lamW * φ) / (1 - β)) (fun _ _ => 1) := by
  intro t
  rw [𝔼.const t]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  have h : (1 : ℝ) - β ≠ 0 := (sub_pos.2 hβ1).ne'
  field_simp
  ring

/-- **Galí (2015), (16), p. 208 and p. 206 (the flexible-wage limit)**: with flexible wages the
wage markup is at its desired value, `μ̂^w ≡ 0`, and then `φ û_t = μ̂^w_t` gives `û ≡ 0`: no
unemployment fluctuations (`φ ≠ 0`). -/
theorem flexible_wages_no_unemployment_gap {φ : ℝ} (hφ : φ ≠ 0) (mu u : ℕ → Ω → ℝ)
    (h16 : ∀ t, φ • u t = mu t) (hflex : ∀ t, mu t = 0) (t : ℕ) : u t = 0 := by
  have h := h16 t
  rw [hflex t, smul_eq_zero] at h
  exact h.resolve_left hφ

/-! ### Optimal policy, (18)–(21) -/

/-- Galí (2015), (13)–(16), pp. 207–208 (perfect foresight): the constraints of the Chapter 7
optimal-policy problem, `t ≥ 0`, `ω̃_{−1} = w0`:
(13) `π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, (14) `π^w_t = β π^w_{t+1} − λ_w φ û_t`,
(15) `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, (16) `φ û_t = ω̃_t − s_y ỹ_t`
(in the book `s_y = σ + φ/(1 − α)`). -/
def Feasible7 (c : Coef) (φ sy : ℝ) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w u : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) - c.lamW * φ * u t ∧
    w t = prev w0 w t + pw t - pp t - dn t ∧
    φ * u t = w t - sy * y t

/-- **Galí (2015), fn. 8, p. 208**: (14) and (16) combine into the Chapter 6 wage Phillips curve
`π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `κ_w = λ_w s_y`. -/
theorem fn8_wage_pc {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) {pw pw' y w u : ℝ}
    (h14 : pw = c.β * pw' - c.lamW * φ * u) (h16 : φ * u = w - sy * y) :
    pw = c.β * pw' + c.kapW * y - c.lamW * w := by
  linear_combination h14 - y * hk - c.lamW * h16

/-- **Galí (2015), §7.2, pp. 207–208 (the Chapter 7 constraints are the Chapter 6 constraints
plus (16))**: for `κ_w = λ_w s_y` and `φ ≠ 0`, a path satisfies (13)–(16) iff it satisfies the
Chapter 6 constraints (18), (20), (21) and `û_t = (ω̃_t − s_y ỹ_t)/φ`. -/
theorem feasible7_iff {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) (hφ : φ ≠ 0)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w u : ℕ → ℝ} :
    Feasible7 c φ sy dn w0 y pp pw w u ↔
      Det.Feasible c dn w0 y pp pw w ∧ u = fun t => (w t - sy * y t) / φ := by
  constructor
  · intro h
    refine ⟨fun t => ⟨(h t).1, fn8_wage_pc hk (h t).2.1 (h t).2.2.2, (h t).2.2.1⟩,
      funext fun t => ?_⟩
    rw [eq_div_iff hφ, mul_comm]
    exact (h t).2.2.2
  · rintro ⟨h, rfl⟩ t
    have h16 : φ * ((w t - sy * y t) / φ) = w t - sy * y t := by field_simp
    refine ⟨(h t).1, ?_, (h t).2.2, h16⟩
    linear_combination (h t).2.1 + y t * hk + c.lamW * h16

/-- Galí (2015), §7.3.2, p. 212: `(ỹ, π^p, π^w, ω̃, û)` solves the Chapter 7 commitment problem:
it satisfies (13)–(16), has finite loss, and no path satisfying (13)–(16) with finite loss has a
smaller loss. The loss is the Chapter 6 loss (unemployment does not enter it, p. 212). -/
def IsOptimal7 (c : Coef) (φ sy : ℝ) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w u : ℕ → ℝ) : Prop :=
  Feasible7 c φ sy dn w0 y pp pw w u ∧ Det.FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w' u', Feasible7 c φ sy dn w0 y' pp' pw' w' u' →
      Det.FiniteLoss c y' pp' pw' → Det.loss c y pp pw ≤ Det.loss c y' pp' pw'

/-- **Galí (2015), §7.3.2, p. 212 (the Chapter 7 problem is the Chapter 6 problem)**: a path
solves the Chapter 7 problem iff `(ỹ, π^p, π^w, ω̃)` solves the Chapter 6 problem and unemployment
is given by (16), `û_t = (ω̃_t − s_y ỹ_t)/φ`. -/
theorem isOptimal7_iff {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) (hφ : φ ≠ 0)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w u : ℕ → ℝ} :
    IsOptimal7 c φ sy dn w0 y pp pw w u ↔
      Det.IsOptimal c dn w0 y pp pw w ∧ u = fun t => (w t - sy * y t) / φ := by
  constructor
  · rintro ⟨hf, hl, hmin⟩
    obtain ⟨hf6, hu⟩ := (feasible7_iff hk hφ).1 hf
    exact ⟨⟨hf6, hl, fun y' pp' pw' w' hf' hl' =>
      hmin y' pp' pw' w' _ ((feasible7_iff hk hφ).2 ⟨hf', rfl⟩) hl'⟩, hu⟩
  · rintro ⟨⟨hf6, hl, hmin⟩, hu⟩
    exact ⟨(feasible7_iff hk hφ).2 ⟨hf6, hu⟩, hl, fun y' pp' pw' w' _ hf' hl' =>
      hmin y' pp' pw' w' ((feasible7_iff hk hφ).1 hf').1 hl'⟩

/-- Galí (2015), (18)–(21), p. 212, as printed (perfect foresight, `Δζ_t = ζ_t − ζ_{t−1}`,
`ζ_{−1} = 0`), with `κ_p = αλ_p/(1 − α)` and `κ_w = λ_w(σ + φ/(1 − α))`. -/
def FOC7 (β σ φ α εp εw lamP lamW : ℝ) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, (σ + (φ + α) / (1 - α)) * y t + α * lamP / (1 - α) * z1 t +
      lamW * (σ + φ / (1 - α)) * z2 t = 0 ∧
    εp / lamP * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    εw * (1 - α) / lamW * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    lamP * z1 t - lamW * z2 t + z3 t - β * z3 (t + 1) = 0

/-- **Galí (2015), (18)–(21), p. 212 (survey error 1)**: the printed optimality conditions are
exactly the Chapter 6 conditions (30)–(33) for the book's coefficients. The text says they are
"identical to those derived in chapter 3"; it should say chapter 6 (as the paragraph's first
sentence does). Also, the multipliers pair with the constraints as `ζ₁` ↔ (13), `ζ₂` ↔ (14) and
(16) combined (the Chapter 6 wage curve, fn. 8), `ζ₃` ↔ (15); the printed attribution "(13),
(14), and (15) and (16) combined" groups (16) with the wrong constraint. -/
theorem foc7_iff_ch6 (β σ φ α εp εw lamP lamW : ℝ) (y pp pw z1 z2 z3 : ℕ → ℝ) :
    FOC7 β σ φ α εp εw lamP lamW y pp pw z1 z2 z3 ↔
      Det.FOC (bookCoef β σ φ α εp εw lamP lamW) y pp pw z1 z2 z3 :=
  Iff.rfl

/-- Galí (2015), (28), p. 179, and p. 212: the loss weights `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w` are positive. -/
theorem bookCoef_weights_pos {β σ φ α εp εw lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hlp : 0 < lamP)
    (hlw : 0 < lamW) :
    0 < (bookCoef β σ φ α εp εw lamP lamW).ay ∧ 0 < (bookCoef β σ φ α εp εw lamP lamW).ap ∧
      0 < (bookCoef β σ φ α εp εw lamP lamW).aw := by
  have h1 : 0 < 1 - α := by linarith
  exact ⟨add_pos_of_pos_of_nonneg hσ (div_nonneg (by linarith) h1.le), div_pos hεp hlp,
    div_pos (mul_pos hεw h1) hlw⟩

/-- **Galí (2015), §7.3.2, p. 212 (the Chapter 7 optimum)**: if the Chapter 6 conditions, i.e.
the printed (18)–(21), have a solution `(ỹ*, π^p*, π^w*, ω̃*)` satisfying the Chapter 6
constraints with finite loss and bounded multipliers, then a path solves the Chapter 7 problem
iff it is that path together with `û*_t = (ω̃*_t − (σ + φ/(1 − α)) ỹ*_t)/φ`. -/
theorem isOptimal7_iff_eq {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3)
    (y pp pw w u : ℕ → ℝ) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u ↔
      y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws ∧
        u = fun t => (ws t - (σ + φ / (1 - α)) * ys t) / φ := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  rw [isOptimal7_iff rfl hφ.ne']
  constructor
  · rintro ⟨hopt, rfl⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      (Det.isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ hopt.1 hopt.2.1).2.1 hopt
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨Det.isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ, rfl⟩

/-- **Galí (2015), §7.3.2, p. 212 (existence and uniqueness)**: under the hypotheses of
`isOptimal7_iff_eq`, the Chapter 7 commitment problem has exactly one solution
`(ỹ, π^p, π^w, ω̃, û)`. -/
theorem existsUnique_optimal7 {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have key := isOptimal7_iff_eq hβ0 hβ1 hσ hφ hα0 hα1 hεp hεw hlp hlw hfs hls hξ hZ
  refine ⟨(ys, pps, pws, ws, fun t => (ws t - (σ + φ / (1 - α)) * ys t) / φ),
    (key _ _ _ _ _).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨y, pp, pw, w, u⟩ h
  obtain ⟨h1, h2, h3, h4, h5⟩ := (key _ _ _ _ _).1 h
  simp only at h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]

/-- **Galí (2015), §7.3.2, p. 212 (necessity and sufficiency of (18)–(21))**: if the printed
conditions (18)–(21) have a Chapter 6-feasible finite-loss solution with bounded multipliers,
then a path satisfying (13)–(16) with finite loss is optimal iff it satisfies (18)–(21) with
bounded multipliers. -/
theorem isOptimal7_iff_foc {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3)
    {y pp pw w u : ℕ → ℝ}
    (hf : Feasible7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u)
    (hl : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) y pp pw) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u ↔
      ∃ z1' z2' z3', FOC7 β σ φ α εp εw lamP lamW y pp pw z1' z2' z3' ∧
        Det.BoundedMult z1' z2' z3' := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  obtain ⟨hf6, hu⟩ := (feasible7_iff rfl hφ.ne').1 hf
  rw [isOptimal7_iff rfl hφ.ne']
  have h := (Det.isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ hf6 hl).1
  exact ⟨fun h' => h.1 h'.1, fun h' => ⟨h.2 h', hu⟩⟩

/-! ### p. 213: the efficient response to technology under `σ = 1` -/

/-- Galí (2015), p. 208: `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), p. 208: `ψ_wa = (1 − α ψ_ya)/(1 − α)`. -/
noncomputable def psiWA (σ φ α : ℝ) : ℝ := (1 - α * psiYA σ φ α) / (1 - α)

/-- **Galí (2015), p. 213**: under `σ = 1`, `ψ_ya = 1` (`φ ≥ 0`). -/
theorem psiYA_sigma_one {φ α : ℝ} (hφ : 0 ≤ φ) : psiYA 1 φ α = 1 := by
  unfold psiYA
  rw [show (1 : ℝ) * (1 - α) + φ + α = 1 + φ by ring, div_self (by linarith)]

/-- **Galí (2015), p. 213**: under `σ = 1`, `ψ_wa = 1` (the natural real wage moves one-for-one
with technology). -/
theorem psiWA_sigma_one {φ α : ℝ} (hφ : 0 ≤ φ) (hα : α ≠ 1) : psiWA 1 φ α = 1 := by
  unfold psiWA
  rw [psiYA_sigma_one hφ, mul_one, div_self (sub_ne_zero.2 (Ne.symm hα))]

/-- Galí (2015), p. 208: output (log deviation from steady state) `ŷ = ψ_ya a + ỹ`. -/
noncomputable def outputDev (σ φ α a ygap : ℝ) : ℝ := psiYA σ φ α * a + ygap

/-- Galí (2015), (9), p. 206: employment `n̂ = (ŷ − a)/(1 − α)`. -/
noncomputable def employmentDev (σ φ α a ygap : ℝ) : ℝ := (outputDev σ φ α a ygap - a) / (1 - α)

/-- Galí (2015), (16), p. 208: the unemployment gap `û = (ω̃ − (σ + φ/(1 − α)) ỹ)/φ`. -/
noncomputable def unempGap (σ φ α wgap ygap : ℝ) : ℝ := (wgap - (σ + φ / (1 - α)) * ygap) / φ

/-- Galí (2015), (7), p. 205: the labour force `l̂ = n̂ + û`. -/
noncomputable def laborForceDev (σ φ α a wgap ygap : ℝ) : ℝ :=
  employmentDev σ φ α a ygap + unempGap σ φ α wgap ygap

/-- Galí (2015), p. 208: the real wage `ω̂ = ψ_wa a + ω̃`. -/
noncomputable def realWageDev (σ φ α a wgap : ℝ) : ℝ := psiWA σ φ α * a + wgap

/-- **Galí (2015), (6), (7), (9), (16), pp. 204–208 (consistency of participation)**: the labour
force `l̂ = n̂ + û` satisfies the participation equation (6) in deviations, with `c = y`:
`ω̂ = σ ŷ + φ l̂` (`φ ≠ 0`, `α ≠ 1`, `σ(1 − α) + φ + α ≠ 0`). -/
theorem participation_consistent {σ φ α a wgap ygap : ℝ} (hφ : φ ≠ 0) (hα : α ≠ 1)
    (hD : σ * (1 - α) + φ + α ≠ 0) :
    realWageDev σ φ α a wgap =
      σ * outputDev σ φ α a ygap + φ * laborForceDev σ φ α a wgap ygap := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold realWageDev outputDev laborForceDev employmentDev unempGap outputDev psiWA psiYA
  field_simp
  ring

/-- **Galí (2015), p. 213 (the efficient response to technology under `σ = 1`)**: at the efficient
allocation (zero output and real wage gaps), `ψ_ya = ψ_wa = 1`, output moves one-for-one with
technology (`ŷ = a`), employment and participation do not respond (`n̂ = l̂ = 0`), the unemployment
gap is zero, and the real wage moves one-for-one (`ω̂ = a`). -/
theorem efficient_technology_sigma_one {φ α : ℝ} (hφ : 0 < φ) (hα : α ≠ 1) (a : ℝ) :
    psiYA 1 φ α = 1 ∧ psiWA 1 φ α = 1 ∧ outputDev 1 φ α a 0 = a ∧ employmentDev 1 φ α a 0 = 0 ∧
      unempGap 1 φ α 0 0 = 0 ∧ laborForceDev 1 φ α a 0 0 = 0 ∧ realWageDev 1 φ α a 0 = a := by
  have hy := psiYA_sigma_one (α := α) hφ.le
  have hw := psiWA_sigma_one hφ.le hα
  have ho : outputDev 1 φ α a 0 = a := by simp [outputDev, hy]
  have hn : employmentDev 1 φ α a 0 = 0 := by simp [employmentDev, ho]
  have hu : unempGap 1 φ α 0 0 = 0 := by simp [unempGap]
  refine ⟨hy, hw, ho, hn, hu, by simp [laborForceDev, hn, hu], by simp [realWageDev, hw]⟩

/-- **Galí (2015), p. 213 (`σ = 1` is what makes employment unresponsive)**: for a nonzero
technology shock (`a ≠ 0`, `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`), employment at the efficient allocation
does not respond iff `σ = 1`. -/
theorem efficient_employment_zero_iff {σ φ α a : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (ha : a ≠ 0) : employmentDev σ φ α a 0 = 0 ↔ σ = 1 := by
  have h1 : 0 < 1 - α := by linarith
  have hD : 0 < σ * (1 - α) + φ + α := by positivity
  unfold employmentDev outputDev psiYA
  rw [div_eq_zero_iff, or_iff_left h1.ne', add_zero, sub_eq_zero, div_mul_eq_mul_div,
    div_eq_iff hD.ne']
  constructor
  · intro h
    have h2 : (1 + φ) = σ * (1 - α) + φ + α := mul_right_cancel₀ ha (by linarith)
    have h3 : (σ - 1) * (1 - α) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · linarith
  · rintro rfl
    ring

/-! ### p. 214: demand shocks -/

/-- **Galí (2015), p. 214 (demand shocks, optimal policy)**: with demand shocks only, technology
is constant, so `Δωⁿ ≡ 0` (`ωⁿ = ψ_wa a`, p. 208), and starting from `ω̃_{−1} = 0` the Chapter 7
optimum is unique and equal to zero in every variable, `û` included (Chapter 6 §6.4.1 plus (16)).
The demand shifter only moves `rⁿ`, which enters the dynamic IS equation (12), not the problem. -/
theorem demand_shock_optimal_iff {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) (y pp pw w u : ℕ → ℝ) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) 0 0 y pp pw w u ↔
      y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ u = 0 := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  rw [isOptimal7_iff rfl hφ.ne', (Det.demand_zero_optimal hβ0 hβ1 hay hap haw).2.2 y pp pw w]
  constructor
  · rintro ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    funext t
    simp
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    funext t
    simp

/-- **Galí (2015), p. 214 (full insulation of the labour market)**: under the optimal policy,
with demand shocks only (`a ≡ 0`), output, employment, the labour force, the unemployment rate
and the real wage do not respond at any date. -/
theorem demand_shock_labour_market {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {y pp pw w u : ℕ → ℝ}
    (h : IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) 0 0 y pp pw w u)
    (t : ℕ) :
    u t = 0 ∧ unempGap σ φ α (w t) (y t) = 0 ∧ outputDev σ φ α 0 (y t) = 0 ∧
      employmentDev σ φ α 0 (y t) = 0 ∧ laborForceDev σ φ α 0 (w t) (y t) = 0 ∧
      realWageDev σ φ α 0 (w t) = 0 := by
  obtain ⟨rfl, -, -, rfl, rfl⟩ :=
    (demand_shock_optimal_iff hβ0 hβ1 hσ hφ hα0 hα1 hεp hεw hlp hlw y pp pw w u).1 h
  simp [unempGap, outputDev, employmentDev, laborForceDev, realWageDev]

/-! ### (22): the simple rule with unemployment -/

/-- Galí (2015), (22), p. 214, as printed: `i_t = 0.01 + 1.5 π^p_t − 0.5 u_t`, with `u_t` the
unemployment rate in levels. -/
def Rule22Level (i pp u : ℝ) : Prop := i = 0.01 + 1.5 * pp - 0.5 * u

/-- **Galí (2015), (22), p. 214 (survey error 5)**: with `u_t = uⁿ + û_t`, the printed rule is the
gap rule `i_t = (0.01 − 0.5 uⁿ) + 1.5 π^p_t − 0.5 û_t`: the level/gap choice shifts the
intercept by `0.5 uⁿ`. -/
theorem rule22_level_iff_gap {un i pp uhat : ℝ} :
    Rule22Level i pp (un + uhat) ↔ i = (0.01 - 0.5 * un) + 1.5 * pp - 0.5 * uhat := by
  unfold Rule22Level
  constructor <;> intro h <;> linarith

/-- Galí (2015), (22), p. 214: at `uⁿ = 0.05` the implied gap-rule intercept is `−0.015`. -/
theorem rule22_book_intercept : (0.01 : ℝ) - 0.5 * 0.05 = -0.015 := by norm_num

/-- **Galí (2015), (22), p. 214 (survey error 5)**: read in levels, the rule is inconsistent with
the zero-inflation steady state `i = ρ ≈ 0.01`, `π^p = 0`, `u = uⁿ = 0.05`. -/
theorem rule22_level_not_steady : ¬ Rule22Level 0.01 0 0.05 := by
  unfold Rule22Level
  norm_num

/-- Galí (2015), (22), p. 214: read in the gap `û`, the rule is consistent with the zero-inflation
steady state (`i = 0.01`, `π^p = 0`, `û = 0`). -/
theorem rule22_gap_steady : (0.01 : ℝ) = 0.01 + 1.5 * 0 - 0.5 * 0 := by norm_num

/-- **Galí (2015), (22), p. 214 (the intercept is irrelevant for the impulse responses)**:
deviations from any reference point satisfying the rule obey `î = 1.5 π̂^p − 0.5 û`, whatever
the intercept; so Figs. 7.5–7.6 are unaffected by survey error 5. -/
theorem rule22_deviation {i pp u i' pp' u' : ℝ} (h : Rule22Level i pp u)
    (h' : Rule22Level i' pp' u') : i - i' = 1.5 * (pp - pp') - 0.5 * (u - u') := by
  unfold Rule22Level at h h'
  rw [h, h']
  ring

end Gali.Unemployment.Policy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 7.1: unemployment and monetary policy with flexible prices

Galí (2015), Chapter 7, Exercise 7.1, p. 220. The model of chapters 6–7 with technology
`Y_t = N_t`, flexible prices and an employment subsidy offsetting the goods-market distortion.

## (a) The price-inflation equation

* `profit_isMaxOn_iff`: with demand `(P/P̄)^{−ε_p} C` and marginal cost `m`, the profit-maximising
  price is exactly `M_p m`, `M_p = ε_p/(ε_p − 1)` (necessary and sufficient; Bernoulli's
  inequality). `subsidy_offsets`, `flexPrice_eq_wage`: with the subsidy `τ = 1/ε_p` and `Y = N`
  (marginal cost `(1 − τ) W`), every symmetric flexible-price equilibrium has `P_t = W_t`.
* `infl_eq_of_realWage_const`: a constant real wage gives `π^p = π^w`.
* `markup_eq_phi_u`: eqs. (6)–(8), `μ^w_t = φ u_t` (exact algebra).
* `ex7_1a`, `ex7_1a_from_primitives`: `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`.

## (b) The welfare loss

* `ch6PeriodLoss` (the Chapter 6 loss (28), restated), `priceWeight_tendsto_zero` (with
  flexible prices, `θ_p → 0`, the price-inflation weight `ε_p/λ_p → 0`),
  `ch6PeriodLoss_tendsto_flex`.
* `efficient_output_iff`, `phi_u_eq_gap`: `φ u_t = −(σ + φ)(y_t − yᵉ_t)` (exact).
* `alphaU`, `flexLoss_eq`: the loss is `(ε_w/(2λ_w)) [α_u u² + π²]`,
  `α_u = φ²λ_w/(ε_w(σ + φ))`; `welfare_tsum_eq`, `welfare_hasSum_iff`, `expected_welfare_eq`
  for the infinite discounted sum (and its expectation).
* Survey error 2 (the printed `β^k`): `printed_sum_not_summable`.
* Survey error 3 (the steady state is not efficient): `distortion_eq`, `distortion_calibration`
  (`Φ = 1 − e^{−φuⁿ} ∈ (0.22, 0.23)` at `φ = 5`, `uⁿ = 0.05`).

## (c) Discretion

`period_problem_iff`, `discretionEq_iff`, `discretionEq_iff_const` (existence and uniqueness
among bounded processes), `inflationBias_pos`, `expected_inflation_eq` (`E_t π_{t+k} = π* > 0`),
`piStar_primitives`, `uStar_primitives`, `uStar_lt_un`, and the ways to remove the bias
(`inflationBias_zero_iff`, `inflationBias_strictMonoOn`, `tendsto_inflationBias_zero`).

## (d) An implementing rule

`rule_implements` (for `φ_π > 1`, the rule `i_t = rᵉ_t + π* + φ_π (π_t − π*)` makes the
discretionary outcome the unique bounded equilibrium), `rule_indeterminate` (`φ_π ≤ 1`).

## (e) Commitment

`isOptimal_iff` (deterministic Lagrangian sufficiency and uniqueness, as in Chapter 5),
`commitment_tendsto` (no long-run bias: `π_t → 0`, `u_t → uⁿ`), `commInfl_lt_piStar`,
`commitment_beats_discretion`.
-/

namespace Gali.Unemployment.Ex7_1

open Filter Topology

/-! ### (a) Flexible price setting with the optimal subsidy -/

/-- Galí (2015), Exercise 7.1, p. 220 (with eq. (2), p. 203): the profit of a firm charging `P`
when the price index is `P̄`, demand is `(P/P̄)^{−ε_p} C` and marginal cost is `m` (with
`Y = N`, marginal cost is the subsidised wage `(1 − τ) W`). -/
noncomputable def profit (εp Pbar C m P : ℝ) : ℝ := (P - m) * ((P / Pbar) ^ (-εp) * C)

/-- Galí (2015), Exercise 7.1(a), p. 220 (Bernoulli's inequality): for `ε > 1`, `s > 0`,
`s ≠ 1`, `(εs − ε + 1) s^{−ε} < 1`. -/
theorem bernoulli_key {ε s : ℝ} (hε : 1 < ε) (hs : 0 < s) (hs1 : s ≠ 1) :
    (ε * s - ε + 1) * s ^ (-ε) < 1 := by
  have hb := one_add_mul_self_lt_rpow_one_add (s := s - 1) (by linarith)
    (sub_ne_zero.mpr hs1) hε
  have e1 : (1 : ℝ) + (s - 1) = s := by ring
  rw [e1] at hb
  have hpos : 0 < s ^ (-ε) := Real.rpow_pos_of_pos hs _
  have hone : s ^ ε * s ^ (-ε) = 1 := by
    rw [Real.rpow_neg hs.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs ε).ne']
  calc (ε * s - ε + 1) * s ^ (-ε) < s ^ ε * s ^ (-ε) :=
        mul_lt_mul_of_pos_right (by linarith) hpos
    _ = 1 := hone

/-- Galí (2015), Exercise 7.1(a), p. 220 (flexible prices): any price other than `M_p m`,
`M_p = ε_p/(ε_p − 1)`, gives strictly lower profits. -/
theorem profit_lt_opt {εp Pbar C m P : ℝ} (hε : 1 < εp) (hPbar : 0 < Pbar) (hC : 0 < C)
    (hm : 0 < m) (hP : 0 < P) (hne : P ≠ εp / (εp - 1) * m) :
    profit εp Pbar C m P < profit εp Pbar C m (εp / (εp - 1) * m) := by
  have hε1 : 0 < εp - 1 := by linarith
  have hPs0 : 0 < εp / (εp - 1) * m := by positivity
  have hs : 0 < P / (εp / (εp - 1) * m) := div_pos hP hPs0
  have hs1 : P / (εp / (εp - 1) * m) ≠ 1 := fun h => hne ((div_eq_one_iff_eq hPs0.ne').mp h)
  have hK : 0 < (εp / (εp - 1) * m / Pbar) ^ (-εp) * C := by positivity
  have hsplit : (P / Pbar) ^ (-εp) =
      (P / (εp / (εp - 1) * m)) ^ (-εp) * (εp / (εp - 1) * m / Pbar) ^ (-εp) := by
    rw [← Real.mul_rpow hs.le (div_pos hPs0 hPbar).le]
    congr 1
    field_simp
  have h1 : profit εp Pbar C m P = m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) *
      ((εp * (P / (εp / (εp - 1) * m)) - εp + 1) * (P / (εp / (εp - 1) * m)) ^ (-εp)) := by
    unfold profit
    rw [hsplit]
    field_simp
    ring
  have h2 : profit εp Pbar C m (εp / (εp - 1) * m) =
      m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) := by
    unfold profit
    field_simp
    ring
  rw [h1, h2]
  have hkey := bernoulli_key hε hs hs1
  have hc : 0 < m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) := by positivity
  nlinarith

/-- Galí (2015), Exercise 7.1(a), p. 220 (**flexible price setting, necessary and
sufficient**): for `ε_p > 1` and positive `P̄`, `C`, `m`, a price `P > 0` maximises profits over
all positive prices iff `P = M_p m` with `M_p = ε_p/(ε_p − 1)`. -/
theorem profit_isMaxOn_iff {εp Pbar C m P : ℝ} (hε : 1 < εp) (hPbar : 0 < Pbar) (hC : 0 < C)
    (hm : 0 < m) (hP : 0 < P) :
    IsMaxOn (profit εp Pbar C m) (Set.Ioi 0) P ↔ P = εp / (εp - 1) * m := by
  have hε1 : 0 < εp - 1 := by linarith
  have hPs0 : 0 < εp / (εp - 1) * m := by positivity
  constructor
  · intro h
    by_contra hne
    have h1 := profit_lt_opt hε hPbar hC hm hP hne
    have h2 := isMaxOn_iff.mp h _ (Set.mem_Ioi.mpr hPs0)
    linarith
  · rintro rfl
    refine isMaxOn_iff.mpr fun x hx => ?_
    by_cases hxe : x = εp / (εp - 1) * m
    · rw [hxe]
    · exact (profit_lt_opt hε hPbar hC hm hx hxe).le

/-- Galí (2015), Exercise 7.1, p. 220 (**the optimal subsidy**): `τ = 1/ε_p` exactly offsets the
goods-market markup, `M_p (1 − τ) = 1`. -/
theorem subsidy_offsets {εp : ℝ} (hε : 1 < εp) : εp / (εp - 1) * (1 - 1 / εp) = 1 := by
  have hε1 : εp - 1 ≠ 0 := by linarith
  have hε0 : εp ≠ 0 := by linarith
  field_simp

/-- Galí (2015), Exercise 7.1(a), p. 220 (**symmetric flexible-price equilibrium**): if at every
date and state the common price `P_t` maximises profits given the price index `P_t`, demand `C_t`
and marginal cost `(1 − τ) W_t` with `τ = 1/ε_p` (with `Y = N` one unit of labour per unit of
output), then `P_t = W_t`: the real wage is constant and equal to one. -/
theorem flexPrice_eq_wage {Ω : Type*} {εp : ℝ} (hε : 1 < εp) {P W C : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hW : ∀ t ω, 0 < W t ω) (hC : ∀ t ω, 0 < C t ω)
    (hopt : ∀ t ω, IsMaxOn (profit εp (P t ω) (C t ω) ((1 - 1 / εp) * W t ω)) (Set.Ioi 0)
      (P t ω)) : P = W := by
  have hτ : 0 < 1 - 1 / εp := by
    have : 1 / εp < 1 := by rw [div_lt_one (by linarith)]; exact hε
    linarith
  funext t ω
  have h := (profit_isMaxOn_iff hε (hP t ω) (hC t ω) (mul_pos hτ (hW t ω)) (hP t ω)).mp
    (hopt t ω)
  rw [h, ← mul_assoc, subsidy_offsets hε, one_mul]

/-- Galí (2015), Exercise 7.1(a), p. 220: inflation of a log-level process `p`, indexed from
date `−1` (`p 0 = p_{−1}`, `p (t + 1) = p_t`): `π_t = p_t − p_{t−1}`. -/
def inflOf {Ω : Type*} (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p (t + 1) - p t

/-- Galí (2015), Exercise 7.1(a), p. 220: if the (log) real wage `w_t − p_t` is constant, price
and wage inflation coincide, `π^p = π^w`. -/
theorem infl_eq_of_realWage_const {Ω : Type*} {p w : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (h : ∀ t, w t - p t = c) : inflOf p = inflOf w := by
  funext t ω
  have h1 := congrFun (h (t + 1)) ω
  have h0 := congrFun (h t) ω
  simp only [inflOf, Pi.sub_apply] at h1 h0 ⊢
  linarith

/-- Galí (2015), eqs. (6)–(8), pp. 204–205 (**exact algebra**): with the average markup
`μ^w = (w − p) − (σc + φn + ξ)`, the participation equation (6) `w − p = σc + φl + ξ` and the
unemployment rate (7) `u = l − n`, the markup is `μ^w = φu`. -/
theorem markup_eq_phi_u {σ φ ξ ω c n l u μ : ℝ} (hμ : μ = ω - (σ * c + φ * n + ξ))
    (h6 : ω = σ * c + φ * l + ξ) (h7 : u = l - n) : μ = φ * u := by
  rw [hμ, h6, h7]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 7.1(a), p. 220 (**the price-inflation equation**): with a constant
real wage, the wage-inflation equation (4) `π^w_t = β E_t π^w_{t+1} − λ_w (μ^w_t − μ^w)`, the
markup–unemployment relation (8) `μ^w_t = φ u_t` and the natural rate (10) `μ^w = φuⁿ`, price
inflation satisfies `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`. -/
theorem ex7_1a {β lamW φ μbar un : ℝ} (hun : μbar = φ * un) {p w μ u : ℕ → Ω → ℝ}
    {c : Ω → ℝ} (hrw : ∀ t, w t - p t = c)
    (h4 : ∀ t, inflOf w t = β • 𝔼.E t (inflOf w (t + 1)) - lamW • (μ t - fun _ => μbar))
    (h8 : ∀ t, μ t = φ • u t) :
    ∀ t, inflOf p t = β • 𝔼.E t (inflOf p (t + 1)) - (φ * lamW) • (u t - fun _ => un) := by
  rw [infl_eq_of_realWage_const hrw]
  intro t
  rw [h4 t, h8 t, hun]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 7.1(a), p. 220 (**from the primitives**): flexible prices with the
optimal subsidy (`flexPrice_eq_wage`), log prices and wages `p = log P`, `w = log W`, the
wage-inflation equation (4), the markup definition, participation (6), unemployment (7) and
the natural rate (10) give `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`. -/
theorem ex7_1a_from_primitives {εp β lamW σ φ μbar un : ℝ} (hε : 1 < εp) (hun : μbar = φ * un)
    {P W C : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hW : ∀ t ω, 0 < W t ω)
    (hC : ∀ t ω, 0 < C t ω)
    (hopt : ∀ t ω, IsMaxOn (profit εp (P t ω) (C t ω) ((1 - 1 / εp) * W t ω)) (Set.Ioi 0)
      (P t ω))
    {p w μ u c n l ξ : ℕ → Ω → ℝ} (hp : ∀ t ω, p t ω = Real.log (P t ω))
    (hw : ∀ t ω, w t ω = Real.log (W t ω))
    (h4 : ∀ t, inflOf w t = β • 𝔼.E t (inflOf w (t + 1)) - lamW • (μ t - fun _ => μbar))
    (hμ : ∀ t ω, μ t ω = (w (t + 1) ω - p (t + 1) ω) - (σ * c t ω + φ * n t ω + ξ t ω))
    (h6 : ∀ t ω, w (t + 1) ω - p (t + 1) ω = σ * c t ω + φ * l t ω + ξ t ω)
    (h7 : ∀ t ω, u t ω = l t ω - n t ω) :
    ∀ t, inflOf p t = β • 𝔼.E t (inflOf p (t + 1)) - (φ * lamW) • (u t - fun _ => un) := by
  have hPW := flexPrice_eq_wage hε hP hW hC hopt
  have hrw : ∀ t, w t - p t = fun _ => 0 := fun t => by
    funext ω
    simp [hp, hw, hPW]
  refine ex7_1a 𝔼 hun hrw h4 fun t => ?_
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  exact markup_eq_phi_u (hμ t ω) (h6 t ω) (h7 t ω)

/-! ### (b) The welfare loss -/

/-- Galí (2015), p. 166 with `α = 0` (so `Θ = 1`): `λ_p = (1 − θ_p)(1 − βθ_p)/θ_p`. -/
noncomputable def lambdaP (β θp : ℝ) : ℝ := (1 - θp) * (1 - β * θp) / θp

/-- Galí (2015), eq. (28), p. 179 (the Chapter 6 period loss, restated from the Chapter 6
project): `½[(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
noncomputable def ch6PeriodLoss (σ φ α εp εw lamP lamW ygap pp pw : ℝ) : ℝ :=
  ((σ + (φ + α) / (1 - α)) * ygap ^ 2 + εp / lamP * pp ^ 2 + εw * (1 - α) / lamW * pw ^ 2) / 2

/-- Galí (2015), Exercise 7.1(b), p. 220: the Chapter 6 period loss with `α = 0` and without
the price-dispersion term (flexible prices): `½[(σ + φ) ỹ² + (ε_w/λ_w)(π^w)²]`. -/
noncomputable def flexLoss (σ φ εw lamW ygap pw : ℝ) : ℝ :=
  ((σ + φ) * ygap ^ 2 + εw / lamW * pw ^ 2) / 2

/-- Galí (2015), Exercise 7.1(b), p. 220: at `α = 0` the Chapter 6 loss is the flexible-price
loss plus the price-dispersion term `(ε_p/λ_p)(π^p)²/2`. -/
theorem ch6PeriodLoss_alpha_zero (σ φ εp εw lamP lamW ygap pp pw : ℝ) :
    ch6PeriodLoss σ φ 0 εp εw lamP lamW ygap pp pw =
      flexLoss σ φ εw lamW ygap pw + εp / lamP * pp ^ 2 / 2 := by
  unfold ch6PeriodLoss flexLoss
  simp only [add_zero, sub_zero, div_one, mul_one]
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220 (**flexible prices remove the price-inflation term**):
as the Calvo parameter `θ_p → 0`, the weight `ε_p/λ_p = ε_p θ_p/((1 − θ_p)(1 − βθ_p)) → 0`. -/
theorem priceWeight_tendsto_zero (β εp : ℝ) :
    Tendsto (fun θ => εp / lambdaP β θ) (𝓝[>] 0) (𝓝 0) := by
  have he : (fun θ => εp / lambdaP β θ) = fun θ : ℝ => εp * θ / ((1 - θ) * (1 - β * θ)) := by
    funext θ
    rw [lambdaP, div_div_eq_mul_div]
  have hc : ContinuousAt (fun θ : ℝ => εp * θ / ((1 - θ) * (1 - β * θ))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have ht := hc.tendsto
  simp only [mul_zero, zero_div] at ht
  rw [he]
  exact ht.mono_left nhdsWithin_le_nhds

/-- Galí (2015), Exercise 7.1(b), p. 220: as `θ_p → 0` the Chapter 6 period loss with `α = 0`
converges, for any values of the arguments, to the flexible-price loss. -/
theorem ch6PeriodLoss_tendsto_flex (β σ φ εp εw lamW ygap pp pw : ℝ) :
    Tendsto (fun θ => ch6PeriodLoss σ φ 0 εp εw (lambdaP β θ) lamW ygap pp pw) (𝓝[>] 0)
      (𝓝 (flexLoss σ φ εw lamW ygap pw)) := by
  simp only [ch6PeriodLoss_alpha_zero]
  have h := ((priceWeight_tendsto_zero β εp).mul_const (pp ^ 2)).div_const 2
  simp only [zero_mul, zero_div] at h
  simpa using (tendsto_const_nhds (x := flexLoss σ φ εw lamW ygap pw)).add h

/-- Galí (2015), Exercise 7.1(b), p. 220: with `Y = N`, the efficient allocation equates the
marginal rate of substitution `σy + φy + ξ` to the (log) marginal product of labour `0`, i.e.
`yᵉ = −ξ/(σ + φ)`. -/
theorem efficient_output_iff {σ φ ξ y : ℝ} (hσφ : σ + φ ≠ 0) :
    σ * y + φ * y + ξ = 0 ↔ y = -ξ / (σ + φ) := by
  rw [eq_div_iff hσφ]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.1(b), p. 220 (**`φ u = −(σ + φ)(y − yᵉ)`, exact**): with flexible
prices and the subsidy the log real wage is `0` (`flexPrice_eq_wage`); with `C = Y = N`, the
markup definition and (8), `φ u_t = −(σ + φ)(y_t − yᵉ_t)` with `yᵉ_t = −ξ_t/(σ + φ)`. -/
theorem phi_u_eq_gap {σ φ ξ ω c n y u μ : ℝ} (hσφ : σ + φ ≠ 0) (hω : ω = 0) (hc : c = y)
    (hn : n = y) (hμ : μ = ω - (σ * c + φ * n + ξ)) (h8 : μ = φ * u) :
    φ * u = -(σ + φ) * (y - -ξ / (σ + φ)) := by
  rw [← h8, hμ, hω, hc, hn]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220: the weight `α_u = φ²λ_w/(ε_w(σ + φ))`. -/
noncomputable def alphaU (σ φ εw lamW : ℝ) : ℝ := φ ^ 2 * lamW / (εw * (σ + φ))

/-- Galí (2015), Exercise 7.1(b), p. 220: `α_u > 0`. -/
theorem alphaU_pos {σ φ εw lamW : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) : 0 < alphaU σ φ εw lamW := by
  unfold alphaU
  positivity

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the period loss, exact algebra**): if
`φ u = −(σ + φ) ỹ` and `π^w = π`, the flexible-price loss equals
`(ε_w/(2λ_w)) [α_u u² + π²]` with `α_u = φ²λ_w/(ε_w(σ + φ))`. -/
theorem flexLoss_eq {σ φ εw lamW ygap u infl : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) (hgap : φ * u = -(σ + φ) * ygap) :
    flexLoss σ φ εw lamW ygap infl = εw / (2 * lamW) * (alphaU σ φ εw lamW * u ^ 2 + infl ^ 2) := by
  have hy : ygap = -(φ * u) / (σ + φ) := by
    rw [eq_div_iff hσφ]
    linarith
  unfold flexLoss alphaU
  rw [hy]
  field_simp

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the discounted loss, up to a positive scalar**):
along any path with `φ u_t = −(σ + φ) ỹ_t`,
`∑ βᵗ L_t = (ε_w/(2λ_w)) ∑ βᵗ [α_u u_t² + π_t²]` (an identity of `tsum`s, valid whether or not
the sums converge, since the summands are proportional). -/
theorem welfare_tsum_eq {β σ φ εw lamW : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → ℝ} (hgap : ∀ t, φ * u t = -(σ + φ) * ygap t) :
    ∑' t, β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t) =
      εw / (2 * lamW) * ∑' t, β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  rw [flexLoss_eq hσφ hεw hlam (hgap t)]
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220 (convergence): along any path with
`φ u_t = −(σ + φ) ỹ_t`, the discounted Chapter 6 loss converges to `(ε_w/(2λ_w)) S` iff
`∑ βᵗ [α_u u_t² + π_t²]` converges to `S`. -/
theorem welfare_hasSum_iff {β σ φ εw lamW S : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → ℝ} (hgap : ∀ t, φ * u t = -(σ + φ) * ygap t) :
    HasSum (fun t => β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t)) (εw / (2 * lamW) * S) ↔
      HasSum (fun t => β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2)) S := by
  have hc : εw / (2 * lamW) ≠ 0 := div_ne_zero hεw (mul_ne_zero two_ne_zero hlam)
  have he : (fun t => β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t)) =
      fun t => εw / (2 * lamW) * (β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2)) := by
    funext t
    rw [flexLoss_eq hσφ hεw hlam (hgap t)]
    ring
  rw [he]
  exact hasSum_mul_left_iff hc

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the expected loss**): for stochastic paths with
`φ u_t = −(σ + φ) ỹ_t` state by state,
`E_0 ∑ βᵗ L_t = (ε_w/(2λ_w)) E_0 ∑ βᵗ [α_u u_t² + π_t²]`. -/
theorem expected_welfare_eq {β σ φ εw lamW : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → Ω → ℝ}
    (hgap : ∀ t ω, φ * u t ω = -(σ + φ) * ygap t ω) :
    𝔼.E 0 (fun ω => ∑' t, β ^ t * flexLoss σ φ εw lamW (ygap t ω) (infl t ω)) =
      (εw / (2 * lamW)) •
        𝔼.E 0 (fun ω => ∑' t, β ^ t * (alphaU σ φ εw lamW * u t ω ^ 2 + infl t ω ^ 2)) := by
  rw [← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  exact welfare_tsum_eq hσφ hεw hlam (fun t => hgap t ω)

/-- Galí (2015), Exercise 7.1(b), p. 220 (**survey error 2: the printed `β^k`**): the printed
loss `E_0 ∑_t β^k [α_u u_t² + π_t²]` has a discount factor that does not depend on the summation
index. Along any path with a constant nonzero period loss (e.g. the discretionary equilibrium
of part (c), `discretionEq_iff_const`), the printed sum diverges for every `k`, while the
intended `∑_t βᵗ [⋯]` converges (`correct_sum_hasSum`). -/
theorem printed_sum_not_summable {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (k : ℕ) :
    ¬ Summable (fun _ : ℕ => β ^ k * L) := by
  rw [summable_const_iff]
  exact (mul_pos (pow_pos hβ k) hL).ne'

/-- Galí (2015), Exercise 7.1(b), p. 220 (the corrected discounting `βᵗ`): a constant period
loss `L` has the finite discounted sum `L/(1 − β)`. -/
theorem correct_sum_hasSum {β L : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * L) (L / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right L
  convert h using 1
  field_simp

/-- Galí (2015), p. 209 and Exercise 7.1(b) (**survey error 3, the size of the steady-state
distortion**): with the goods-market distortion offset, the remaining steady-state distortion is
the wage markup, `Φ = 1 − 1/M_w`, `M_w = ε_w/(ε_w − 1)`; so `Φ = 1/ε_w`, and with
`M_w = exp(μ^w) = exp(φuⁿ)` (eq. (10)), `Φ = 1 − e^{−φuⁿ}`. -/
theorem distortion_eq {εw φ un : ℝ} (hεw : 1 < εw)
    (hMw : Real.log (εw / (εw - 1)) = φ * un) :
    1 - 1 / (εw / (εw - 1)) = 1 / εw ∧ 1 - 1 / (εw / (εw - 1)) = 1 - Real.exp (-(φ * un)) := by
  have hε1 : 0 < εw - 1 := by linarith
  have hM : 0 < εw / (εw - 1) := div_pos (by linarith) hε1
  refine ⟨by field_simp; ring, ?_⟩
  rw [← hMw, Real.exp_neg, Real.exp_log hM, one_div]

/-- Galí (2015), p. 209 and Exercise 7.1(b) (**survey error 3, numerically**): at the Chapter 7
calibration `φ = 5`, `uⁿ = 0.05`, the steady-state distortion `Φ = 1 − e^{−φuⁿ}` lies in
`(0.22, 0.23)`: it is not small. The Chapter 6 loss "taken as a starting point" was derived
around an efficient steady state (or for a small distortion), so the exercise's `α_u` holds
only under that approximation; with `Φ ≈ 0.22` a second-order approximation around the
distorted steady state (Benigno–Woodford) would in general change the weights. -/
theorem distortion_calibration :
    (0.22 : ℝ) < 1 - Real.exp (-((5 : ℝ) * 0.05)) ∧
      1 - Real.exp (-((5 : ℝ) * 0.05)) < (0.23 : ℝ) := by
  have e : -((5 : ℝ) * 0.05) = -(1 / 4) := by norm_num
  rw [e]
  have h := Real.exp_bound (x := -(1 / 4)) (by norm_num [abs_div]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> norm_num <;> linarith

/-! ### (c) Optimal discretionary policy -/

/-- Galí (2015), Exercise 7.1(c), p. 220: the period objective `π² + ϑ u²` (`ϑ = α_u`) after
substituting the constraint `π = −κ u + v` (`κ = φλ_w`, `v = β E_t π_{t+1} + κ uⁿ` taken as
given under discretion). -/
def periodObj (κ ϑ v u : ℝ) : ℝ := (-(κ * u) + v) ^ 2 + ϑ * u ^ 2

/-- Galí (2015), Exercise 7.1(c), p. 220 (completing the square). -/
theorem periodObj_sub (κ ϑ v u u' : ℝ) :
    periodObj κ ϑ v u' - periodObj κ ϑ v u
      = (κ ^ 2 + ϑ) * (u' - u) ^ 2 + 2 * (u' - u) * ((κ ^ 2 + ϑ) * u - κ * v) := by
  unfold periodObj
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**necessary and sufficient**, adapted from the
Chapter 5 project): for `ϑ > 0`, `u` minimises the period objective iff
`u = (κ/ϑ)(−κ u + v)`. -/
theorem periodObj_isMinOn_iff {κ ϑ v u : ℝ} (hϑ : 0 < ϑ) :
    IsMinOn (periodObj κ ϑ v) Set.univ u ↔ u = κ / ϑ * (-(κ * u) + v) := by
  have hA : 0 < κ ^ 2 + ϑ := by positivity
  have hfoc : u = κ / ϑ * (-(κ * u) + v) ↔ (κ ^ 2 + ϑ) * u - κ * v = 0 := by
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
    set g := (κ ^ 2 + ϑ) * u - κ * v
    have hle := isMinOn_iff.mp h (u - g / (κ ^ 2 + ϑ)) (Set.mem_univ _)
    have hd := periodObj_sub κ ϑ v u (u - g / (κ ^ 2 + ϑ))
    have hval : (κ ^ 2 + ϑ) * (u - g / (κ ^ 2 + ϑ) - u) ^ 2 +
        2 * (u - g / (κ ^ 2 + ϑ) - u) * g = -(g ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + ϑ) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h
    refine isMinOn_iff.mpr fun u' _ => ?_
    have hd := periodObj_sub κ ϑ v u u'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + ϑ) * (u' - u) ^ 2 := by positivity
    linarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the period problem under discretion, necessary and
sufficient**): for `ϑ > 0`, `(π, u)` minimises `π² + ϑ u²` subject to `π = −κ u + v` iff it is
feasible and satisfies the targeting rule `u = (κ/ϑ) π`. -/
theorem period_problem_iff {κ ϑ v infl u : ℝ} (hϑ : 0 < ϑ) :
    (infl = -(κ * u) + v ∧ ∀ π' u', π' = -(κ * u') + v →
        infl ^ 2 + ϑ * u ^ 2 ≤ π' ^ 2 + ϑ * u' ^ 2) ↔
      (infl = -(κ * u) + v ∧ u = κ / ϑ * infl) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ ϑ v) Set.univ u := isMinOn_iff.mpr fun u' _ => by
      have := hmin _ u' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hϑ).mp this
  · rintro ⟨hc, hu⟩
    refine ⟨hc, fun π' u' hc' => ?_⟩
    rw [hc] at hu
    have := isMinOn_iff.mp ((periodObj_isMinOn_iff hϑ).mpr hu) u' (Set.mem_univ u')
    simp only [periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), Exercise 7.1(a), p. 220: the price-inflation equation in unemployment,
`π_t = β E_t π_{t+1} − κ (u_t − uⁿ)`, `κ = φλ_w`. -/
def NKPCu (β κ un : ℝ) (u infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - κ • (u t - fun _ => un)

/-- Galí (2015), Exercise 7.1(c), p. 220: a **discretionary equilibrium**: the price-inflation
equation holds and, at each date and in each state, `(π_t, u_t)` minimises the period loss
`π² + ϑ u²` (`ϑ = α_u`) over the line `π = −κ u + v_t`, taking
`v_t = β E_t π_{t+1} + κ uⁿ` as given. -/
def DiscretionEq (β κ ϑ un : ℝ) (u infl : ℕ → Ω → ℝ) : Prop :=
  NKPCu 𝔼 β κ un u infl ∧ ∀ t ω, ∀ π' u' : ℝ,
    π' = -(κ * u') + (β * 𝔼.E t (infl (t + 1)) ω + κ * un) →
      infl t ω ^ 2 + ϑ * u t ω ^ 2 ≤ π' ^ 2 + ϑ * u' ^ 2

/-- Galí (2015), Exercise 7.1(c), p. 220: the discretionary targeting rule
`u_t = (κ/ϑ) π_t`. -/
def TargetingRule (κ ϑ : ℝ) (u infl : ℕ → Ω → ℝ) : Prop := ∀ t, u t = (κ / ϑ) • infl t

/-- Galí (2015), Exercise 7.1(c), p. 220: for `ϑ > 0` a discretionary equilibrium is exactly a
pair satisfying the price-inflation equation and the targeting rule `u = (κ/ϑ) π`. -/
theorem discretionEq_iff {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) {u infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ ϑ un u infl ↔ NKPCu 𝔼 β κ un u infl ∧ TargetingRule κ ϑ u infl := by
  have hpt : ∀ (h : NKPCu 𝔼 β κ un u infl) t ω,
      infl t ω = -(κ * u t ω) + (β * 𝔼.E t (infl (t + 1)) ω + κ * un) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
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

/-- Galí (2015), Exercise 7.1(c), p. 220: the discount factor of the discretionary inflation
equation, `a = ϑβ/(ϑ + κ²)`. -/
noncomputable def aDisc (β κ ϑ : ℝ) : ℝ := ϑ * β / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 7.1(c), p. 220: `0 ≤ a < 1` for `ϑ > 0`, `0 ≤ β < 1`. -/
theorem aDisc_mem {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ aDisc β κ ϑ ∧ aDisc β κ ϑ < 1 := by
  unfold aDisc
  have hA : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), Exercise 7.1(c), p. 220: under the targeting rule the price-inflation equation
is equivalent to `π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + ϑκuⁿ/(ϑ + κ²)`. -/
theorem inflation_forward_iff {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) {u infl : ℕ → Ω → ℝ}
    (hr : TargetingRule κ ϑ u infl) :
    NKPCu 𝔼 β κ un u infl ↔
      ∀ t, infl t = aDisc β κ ϑ • 𝔼.E t (infl (t + 1)) + fun _ => ϑ * κ * un / (ϑ + κ ^ 2) := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hϑ' : ϑ ≠ 0 := hϑ.ne'
  constructor
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r] at p
    unfold aDisc
    field_simp
    field_simp at p
    linarith
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r]
    unfold aDisc at p
    field_simp at p
    field_simp
    linarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**discretionary inflation**):
`π* = ϑκuⁿ/(κ² + ϑ(1 − β))`. -/
noncomputable def piStar (β κ ϑ un : ℝ) : ℝ := ϑ * κ * un / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), Exercise 7.1(c), p. 220 (**discretionary unemployment**):
`u* = (κ/ϑ) π* = κ² uⁿ/(κ² + ϑ(1 − β))`. -/
noncomputable def uStar (β κ ϑ un : ℝ) : ℝ := κ ^ 2 * un / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), Exercise 7.1(c), p. 220: `κ² + ϑ(1 − β) > 0`. -/
theorem den_pos {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) : 0 < κ ^ 2 + ϑ * (1 - β) := by
  have : 0 < ϑ * (1 - β) := mul_pos hϑ (by linarith)
  positivity

/-- Galí (2015), Exercise 7.1(c), p. 220: `u* = (κ/ϑ) π*` (the targeting rule). -/
theorem uStar_eq {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) :
    uStar β κ ϑ un = κ / ϑ * piStar β κ ϑ un := by
  unfold uStar piStar
  field_simp

/-- Galí (2015), Exercise 7.1(c), p. 220: the constants satisfy the price-inflation equation,
`π* = β π* − κ(u* − uⁿ)`. -/
theorem piStar_nkpc {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    piStar β κ ϑ un = β * piStar β κ ϑ un - κ * (uStar β κ ϑ un - un) := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar uStar
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**existence**): the constant pair `(u*, π*)` is a
discretionary equilibrium. -/
theorem discretion_const_isEq {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    DiscretionEq 𝔼 β κ ϑ un (fun _ _ => uStar β κ ϑ un) (fun _ _ => piStar β κ ϑ un) := by
  rw [discretionEq_iff 𝔼 hϑ]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [𝔼.const]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact piStar_nkpc hϑ hβ1
  · funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact uStar_eq hϑ

/-- Galí (2015), Exercise 7.1(c), p. 220 (**existence and uniqueness of the discretionary
equilibrium**): for `ϑ > 0`, `0 ≤ β < 1`, a pair `(u, π)` with `π` bounded is a discretionary
equilibrium iff `π_t = π*` and `u_t = u*` at every date and state. -/
theorem discretionEq_iff_const {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u infl : ℕ → Ω → ℝ} (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ un u infl ↔
      infl = (fun _ _ => piStar β κ ϑ un) ∧ u = (fun _ _ => uStar β κ ϑ un) := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  have ha : |aDisc β κ ϑ| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hc := discretion_const_isEq 𝔼 (κ := κ) (un := un) hϑ hβ1
  have hcb : BoundedProc (fun (_ : ℕ) (_ : Ω) => piStar β κ ϑ un) :=
    ⟨|piStar β κ ϑ un|, fun _ _ => le_rfl⟩
  constructor
  · intro h
    obtain ⟨hn, hr⟩ := (discretionEq_iff 𝔼 hϑ).mp h
    obtain ⟨hn', hr'⟩ := (discretionEq_iff 𝔼 hϑ).mp hc
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp hn
    have hf' := (inflation_forward_iff 𝔼 hϑ hr').mp hn'
    have hp : infl = fun _ _ => piStar β κ ϑ un := 𝔼.forward_unique ha hf hf' hpb hcb
    refine ⟨hp, funext fun t => ?_⟩
    rw [hr t, hp]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (uStar_eq hϑ).symm
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the inflation bias is positive**): for `κ, ϑ > 0`,
`β < 1` and a positive natural rate `uⁿ > 0`, `π* > 0`. -/
theorem inflationBias_pos {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ1 : β < 1)
    (hun : 0 < un) : 0 < piStar β κ ϑ un := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar
  positivity

/-- Galí (2015), Exercise 7.1(c), p. 220 (**average inflation is positive**): in the unique
bounded discretionary equilibrium, `E_t π_{t+k} = π* > 0` for every date `t`, horizon `k` and
state (so in particular the unconditional mean is `π*`). -/
theorem expected_inflation_eq {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hun : 0 < un) {u infl : ℕ → Ω → ℝ} (hpb : BoundedProc infl)
    (h : DiscretionEq 𝔼 β κ ϑ un u infl) (t k : ℕ) (ω : Ω) :
    𝔼.E t (infl (t + k)) ω = piStar β κ ϑ un ∧ 0 < 𝔼.E t (infl (t + k)) ω := by
  obtain ⟨hp, -⟩ := (discretionEq_iff_const 𝔼 hϑ hβ0 hβ1 hpb).mp h
  subst hp
  rw [𝔼.const]
  exact ⟨rfl, inflationBias_pos hκ hϑ hβ1 hun⟩

/-- Galí (2015), Exercise 7.1(c), p. 220: discretionary unemployment lies strictly between `0`
and the natural rate, `0 < u* < uⁿ` (for `κ ≠ 0`, `ϑ > 0`, `β < 1`, `uⁿ > 0`). -/
theorem uStar_lt_un {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ1 : β < 1) (hun : 0 < un) :
    0 < uStar β κ ϑ un ∧ uStar β κ ϑ un < un := by
  have hD := den_pos (κ := κ) hϑ hβ1
  have hk : 0 < κ ^ 2 := by positivity
  have h1 : 0 < ϑ * (1 - β) := mul_pos hϑ (by linarith)
  unfold uStar
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hD]
  nlinarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**closed form in the primitives**): with `κ = φλ_w`
and `ϑ = α_u = φ²λ_w/(ε_w(σ + φ))`, `π* = φλ_w uⁿ/(1 − β + λ_w ε_w (σ + φ))`. -/
theorem piStar_primitives {β σ φ εw lamW un : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) (hβ1 : β < 1) :
    piStar β (φ * lamW) (alphaU σ φ εw lamW) un =
      φ * lamW * un / (1 - β + lamW * εw * (σ + φ)) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β + lamW * εw * (σ + φ) := by positivity
  have hD := den_pos (κ := φ * lamW) (alphaU_pos hσ hφ hεw hlam) hβ1
  unfold piStar
  unfold alphaU at hD ⊢
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**closed form in the primitives**):
`u* = λ_w ε_w (σ + φ) uⁿ/(1 − β + λ_w ε_w (σ + φ))`. -/
theorem uStar_primitives {β σ φ εw lamW un : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) (hβ1 : β < 1) :
    uStar β (φ * lamW) (alphaU σ φ εw lamW) un =
      lamW * εw * (σ + φ) * un / (1 - β + lamW * εw * (σ + φ)) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β + lamW * εw * (σ + φ) := by positivity
  have hD := den_pos (κ := φ * lamW) (alphaU_pos hσ hφ hεw hlam) hβ1
  unfold uStar
  unfold alphaU at hD ⊢
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**removing the bias: eliminate the wage markup**): for
`κ, ϑ > 0`, `β < 1`, the bias vanishes iff `uⁿ = 0`. -/
theorem inflationBias_zero_iff {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    piStar β κ ϑ un = 0 ↔ un = 0 := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hϑ.ne'
        · exact absurd h'' hκ.ne'
      · exact h'
    · exact absurd h hD.ne'
  · intro h
    left
    rw [h, mul_zero]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**an employment subsidy removes the wage markup**): a
subsidy `τ_w = 1/ε_w` makes the effective desired wage markup `log(M_w (1 − τ_w)) = 0`, hence
`uⁿ = 0` (eq. (10)) and no inflation bias. -/
theorem wageSubsidy_markup_zero {εw : ℝ} (hεw : 1 < εw) :
    Real.log (εw / (εw - 1) * (1 - 1 / εw)) = 0 := by
  rw [subsidy_offsets hεw, Real.log_one]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**removing the bias: a conservative central
banker**): for `κ > 0`, `uⁿ > 0`, `β < 1`, the bias `π*` is strictly increasing in the weight
`ϑ` placed on unemployment. -/
theorem inflationBias_strictMonoOn {β κ un : ℝ} (hκ : 0 < κ) (hβ1 : β < 1) (hun : 0 < un) :
    StrictMonoOn (fun ϑ => piStar β κ ϑ un) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hDa := den_pos (κ := κ) ha0 hβ1
  have hDb := den_pos (κ := κ) hb0 hβ1
  simp only [piStar]
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < κ ^ 2 * (κ * un) := by positivity
  nlinarith [mul_lt_mul_of_pos_right hab hk]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the bias vanishes as the weight on unemployment
goes to zero**): `π* → 0` as `ϑ → 0⁺` (for `κ ≠ 0`). -/
theorem tendsto_inflationBias_zero {β κ un : ℝ} (hκ : κ ≠ 0) :
    Tendsto (fun ϑ => piStar β κ ϑ un) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun ϑ : ℝ => ϑ * κ * un / (κ ^ 2 + ϑ * (1 - β))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using pow_ne_zero 2 hκ
  have ht := hc.tendsto
  simp only [zero_mul, zero_div] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-! ### (d) An interest-rate rule implementing the discretionary outcome -/

/-- Galí (2015), Exercise 7.1(d), p. 220 (with `C = Y` and the Euler equation (3), p. 203): the
dynamic IS equation in a gap `x` with real rate `r`,
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r_t)` (restated from the Chapter 5 project). -/
def DIS (σ : ℝ) (x i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - r t)

/-- Galí (2015), Exercise 7.1(d), p. 220: the real rate consistent with an output path `y^v`,
`r_t = ζ_t + σ E_t{Δy^v_{t+1}}` (restated from the Chapter 5 project). -/
def rateOf (σ : ℝ) (ζ yv : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ζ t + σ • (𝔼.E t (yv (t + 1)) - yv t)

/-- Galí (2015), Exercise 7.1(d), p. 220 (**exact**, restated from the Chapter 5 project): for
`σ ≠ 0`, the DIS in `y − y^n` with rate `r^n` holds iff the DIS in the welfare-relevant gap
`y − yᵉ` with the efficient rate `rᵉ` holds. With `y^n = 0` and `ζ ≡ ρ` this turns the Euler
equation `y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)` into the DIS in `y − yᵉ`. -/
theorem dis_gap_iff {σ : ℝ} (hσ : σ ≠ 0) {y yn ye i infl ζ : ℕ → Ω → ℝ} :
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

/-- Galí (2015), Exercise 7.1(d), p. 220: the price-inflation equation in an output gap `x`
with slope `κ` and a forcing term `c`, `π_t = β E_t π_{t+1} + κ x_t + c_t`. -/
def NKPCx (β κ : ℝ) (x c infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + c t

/-- Galí (2015), Exercise 7.1(d), p. 220: the stacked vector `(x_t, π_t)` (restated from the
Chapter 5 project). -/
def stack (x infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the Chapter 5
project; Galí 2015, Exercise 7.1(d), p. 220). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the Chapter 5
project; Galí 2015, Exercise 7.1(d), p. 220). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Exercise 7.1(d), p. 220 (the system under a rule responding to inflation with
`φ_π`; ch. 4, eq. (13) with `φ_y = 0`; restated from the Chapter 5 project):
`A_T = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def AT (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), Exercise 7.1(d), p. 220: the forcing of the system under a rule
`i_t = r_t + ψ c_t + φ_π π_t` (restated from the Chapter 5 project). -/
noncomputable def wT (σ κ φπ ψ : ℝ) (c : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ + φπ) / (σ + κ * φπ)) • c t, ((σ - κ * ψ) / (σ + κ * φπ)) • c t]

/-- Galí (2015), Exercise 7.1(d), p. 220 (**exact**, restated from the Chapter 5 project): under
a rule `i_t = r_t + ψ c_t + φ_π π_t`, the Phillips curve and the DIS hold iff `(x, π)` solves
`(x_t, π_t) = A_T E_t (x_{t+1}, π_{t+1}) + w_t`. -/
theorem rule_iff_solves {β σ κ φπ ψ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {c x infl i r : ℕ → Ω → ℝ} (hrule : ∀ t, i t = r t + ψ • c t + φπ • infl t) :
    (NKPCx 𝔼 β κ x c infl ∧ DIS 𝔼 σ x i infl r) ↔
      𝔼.Solves (AT β σ κ φπ) (wT σ κ φπ ψ c) (stack x infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    have s : σ * x t ω + φπ * infl t ω
        = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * c t ω := by
      linear_combination σ * e -
        (ψ * c t ω + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω) * hinv
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
          = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * c t ω := by
        apply mul_left_cancel₀ hS
        linear_combination σ * e0 + φπ * e1
      linear_combination σ⁻¹ * s - (x t ω - 𝔼.E t (x (t + 1)) ω) * hinv

/-- Galí (2015), Exercise 7.1(d), p. 220: `tr A_T = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(d), p. 220: `det A_T = σβ/(σ + κφ_π)`. -/
theorem det2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the Taylor principle**, restated from the Chapter 5
project): for `σ, κ > 0`, `0 < β < 1`, `φ_π ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle iff `φ_π > 1`. -/
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

/-- Galí (2015), Exercise 7.1(d), p. 220: the rule
`i_t = rᵉ_t + π* + φ_π (π_t − π*)`. -/
def RuleD (πs φπ : ℝ) (re infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = re t + (fun _ => πs) + φπ • (infl t - fun _ => πs)

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the system in deviations, exact**): with
`ψ = φ/(σ + φ)` (the output gap is `y − yᵉ = −ψ u`, `phi_u_eq_gap`), `κ = φλ_w` and the rule
`i_t = rᵉ_t + π* + φ_π (π_t − π*)`, the price-inflation equation and the DIS in `−ψ u` hold iff
the deviations `x̂_t = −ψ(u_t − u*)`, `π̂_t = π_t − π*` solve
`(x̂_t, π̂_t) = A_T(β, σ, κ/ψ, φ_π) E_t (x̂_{t+1}, π̂_{t+1})`. -/
theorem dev_iff_solves {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hψ : 0 < ψ) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) {u infl i re : ℕ → Ω → ℝ}
    (hrule : RuleD (piStar β κ ϑ un) φπ re infl i) :
    (NKPCu 𝔼 β κ un u infl ∧ DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re) ↔
      𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0)
        (stack (fun t => (-ψ) • (u t - fun _ => uStar β κ ϑ un))
          (fun t => infl t - fun _ => piStar β κ ϑ un)) := by
  have hS : σ + κ / ψ * φπ ≠ 0 := by positivity
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hpn : πs = β * πs - κ * (us - un) := piStar_nkpc hϑ hβ1
  have hσ' : σ ≠ 0 := hσ.ne'
  have hψ' : ψ ≠ 0 := hψ.ne'
  have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ'
  have hdev : ∀ t, (fun t => φπ • (infl t - fun _ => πs)) t =
      (0 : ℕ → Ω → ℝ) t + (0 : ℝ) • (0 : ℕ → Ω → ℝ) t +
        φπ • (fun t => infl t - fun _ => πs) t := fun t => by simp
  rw [← rule_iff_solves 𝔼 hσ' hS hdev]
  have hEx : ∀ t ω, 𝔼.E t ((-ψ) • (u (t + 1) - fun _ => us)) ω =
      -ψ * 𝔼.E t (u (t + 1)) ω + ψ * us := fun t ω => by
    simp only [map_smul, map_sub, 𝔼.const, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hEp : ∀ t ω, 𝔼.E t (infl (t + 1) - fun _ => πs) ω = 𝔼.E t (infl (t + 1)) ω - πs :=
    fun t ω => by simp only [map_sub, 𝔼.const, Pi.sub_apply]
  have hEx' : ∀ t ω, 𝔼.E t ((-ψ) • u (t + 1)) ω = -ψ * 𝔼.E t (u (t + 1)) ω := fun t ω => by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hn, hd⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have p := congrFun (hn t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hEp]
      field_simp
      linear_combination p - hpn
    · have e := congrFun (hd t) ω
      have r := congrFun (hrule t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEx'] at e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hEx, hEp]
      rw [r] at e
      linear_combination e
  · rintro ⟨hn, hd⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have p := congrFun (hn t) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hEp] at p
      field_simp at p
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination p + hpn
    · have e := congrFun (hd t) ω
      have r := congrFun (hrule t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hEx, hEp] at e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEx']
      rw [r]
      linear_combination e

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the rule implements the discretionary outcome
uniquely**): for `σ, κ, ϑ, ψ > 0`, `0 < β < 1` and `φ_π > 1`, bounded adapted `(u, π)` and a
nominal rate `i` satisfy the price-inflation equation, the DIS (gap `−ψ u`, efficient rate
`rᵉ`) and the rule `i_t = rᵉ_t + π* + φ_π(π_t − π*)` iff `u ≡ u*`, `π ≡ π*` (the discretionary
equilibrium of part (c)) and `i_t = rᵉ_t + π*`. -/
theorem rule_implements {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hψ : 0 < ψ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) {u infl i re : ℕ → Ω → ℝ}
    (hua : 𝔼.Adapted u) (hpa : 𝔼.Adapted infl) (hub : BoundedProc u)
    (hpb : BoundedProc infl) :
    (NKPCu 𝔼 β κ un u infl ∧ DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re ∧
        RuleD (piStar β κ ϑ un) φπ re infl i) ↔
      (u = (fun _ _ => uStar β κ ϑ un) ∧ infl = (fun _ _ => piStar β κ ϑ un) ∧
        ∀ t, i t = re t + fun _ => piStar β κ ϑ un) := by
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hκψ : 0 < κ / ψ := div_pos hκ hψ
  have hz : 𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0) (fun _ _ => 0) := by
    intro t j
    fin_cases j <;> simp [wT]
  have hza : 𝔼.AdaptedVec (fun _ _ => (0 : Ω → ℝ)) := fun t j => by
    simp
  have hzb : BoundedVec (fun (_ : ℕ) (_ : Fin 2) (_ : Ω) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  constructor
  · rintro ⟨hn, hd, hr⟩
    have hs := (dev_iff_solves 𝔼 hσ hκ hϑ hψ hβ1 (by linarith) hr).mp ⟨hn, hd⟩
    have hxa : 𝔼.Adapted (fun t => (-ψ) • (u t - fun _ => us)) := fun t => by
      rw [map_smul, map_sub, hua t, 𝔼.const]
    have hpa' : 𝔼.Adapted (fun t => infl t - fun _ => πs) := fun t => by
      rw [map_sub, hpa t, 𝔼.const]
    have hxb : BoundedProc (fun t => (-ψ) • (u t - fun _ => us)) := by
      obtain ⟨M, hM⟩ := hub
      refine ⟨|ψ| * (M + |us|), fun t ω => ?_⟩
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hM t ω]))
        (abs_nonneg _)
    have hpb' : BoundedProc (fun t => infl t - fun _ => πs) := by
      obtain ⟨M, hM⟩ := hpb
      exact ⟨M + |πs|, fun t ω => (abs_sub _ _).trans (by simp only; linarith [hM t ω])⟩
    have heq := 𝔼.system_unique ((AT_schurStable_iff hσ hκψ hβ0 hβ1 (by linarith)).mpr hφ)
      hs hz (adaptedVec_stack 𝔼 hxa hpa') hza (boundedVec_stack hxb hpb') hzb
    have h0 : ∀ t ω, -ψ * (u t ω - us) = 0 := fun t ω => by
      simpa [stack] using congrFun (congrFun (congrFun heq t) 0) ω
    have h1 : ∀ t ω, infl t ω - πs = 0 := fun t ω => by
      simpa [stack] using congrFun (congrFun (congrFun heq t) 1) ω
    have hu' : u = fun _ _ => us := by
      funext t ω
      have := h0 t ω
      have hψ0 : -ψ ≠ 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hψ0
      linarith
    have hp' : infl = fun _ _ => πs := by
      funext t ω
      linarith [h1 t ω]
    refine ⟨hu', hp', fun t => ?_⟩
    rw [hr t, hp']
    funext ω
    simp
  · rintro ⟨rfl, rfl, hi⟩
    have hr : RuleD πs φπ re (fun _ _ => πs) i := fun t => by
      rw [hi t]
      funext ω
      simp
    refine ⟨((discretionEq_iff 𝔼 hϑ).mp (discretion_const_isEq 𝔼 hϑ hβ1)).1, ?_, hr⟩
    intro t
    funext ω
    simp only [hi t, map_smul, 𝔼.const, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the Taylor principle is needed**): for
`0 ≤ φ_π ≤ 1` the rule `i_t = rᵉ_t + π* + φ_π(π_t − π*)` does not determine the equilibrium:
there are bounded adapted `(u, π)` and a rate `i` satisfying the price-inflation equation, the
DIS and the rule, other than the discretionary outcome. -/
theorem rule_indeterminate [Nonempty Ω] {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hψ : 0 < ψ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    (re : ℕ → Ω → ℝ) :
    ∃ u infl i : ℕ → Ω → ℝ, NKPCu 𝔼 β κ un u infl ∧
      DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re ∧ RuleD (piStar β κ ϑ un) φπ re infl i ∧
      𝔼.Adapted u ∧ 𝔼.Adapted infl ∧ BoundedProc u ∧ BoundedProc infl ∧
      (u ≠ (fun _ _ => uStar β κ ϑ un) ∨ infl ≠ (fun _ _ => piStar β κ ϑ un)) := by
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hκψ : 0 < κ / ψ := div_pos hκ hψ
  have hz : 𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0) (fun _ _ => 0) := by
    intro t j
    fin_cases j <;> simp [wT]
  have hza : 𝔼.AdaptedVec (fun _ _ => (0 : Ω → ℝ)) := fun t j => by
    simp
  have hzb : BoundedVec (fun (_ : ℕ) (_ : Fin 2) (_ : Ω) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  have hns : ¬ SchurStable (tr2 (AT β σ (κ / ψ) φπ)) (det2 (AT β σ (κ / ψ) φπ)) := by
    rw [AT_schurStable_iff hσ hκψ hβ0 hβ1 hφ0]
    linarith
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique hns hz hza hzb
  set u : ℕ → Ω → ℝ := fun t => (fun _ => us) - ψ⁻¹ • y t 0
  set infl : ℕ → Ω → ℝ := fun t => y t 1 + fun _ => πs
  set i : ℕ → Ω → ℝ := fun t => re t + (fun _ => πs) + φπ • (infl t - fun _ => πs)
  have hr : RuleD πs φπ re infl i := fun _ => rfl
  have hψ' : ψ ≠ 0 := hψ.ne'
  have hst : stack (fun t => (-ψ) • (u t - fun _ => us)) (fun t => infl t - fun _ => πs) = y := by
    funext t j
    fin_cases j
    · funext ω
      simp [stack, u, smul_smul, hψ']
    · funext ω
      simp [stack, infl]
  obtain ⟨hn, hd⟩ := (dev_iff_solves 𝔼 hσ hκ hϑ hψ hβ1 hφ0 hr).mpr (hst ▸ hy)
  refine ⟨u, infl, i, hn, hd, hr, fun t => ?_, fun t => ?_, ?_, ?_, ?_⟩
  · simp only [u, map_sub, map_smul, 𝔼.const, hay t 0]
  · simp only [infl, map_add, 𝔼.const, hay t 1]
  · refine ⟨|us| + |ψ⁻¹| * B, fun t ω => ?_⟩
    simp only [u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    linarith [mul_le_mul_of_nonneg_left (hB t 0 ω) (abs_nonneg ψ⁻¹)]
  · refine ⟨B + |πs|, fun t ω => ?_⟩
    simp only [infl, Pi.add_apply]
    exact (abs_add_le _ _).trans (by linarith [hB t 1 ω])
  · by_contra hcon
    push Not at hcon
    apply hne
    rw [← hst, hcon.1, hcon.2]
    funext t j
    fin_cases j <;> funext ω <;> simp [stack]

/-! ### (e) Optimal policy under commitment

Exercise 7.1 has no exogenous shocks (`Y = N`, constant desired markups), so the commitment
problem is deterministic: choose `{π_t, u_t}` to minimise `∑ βᵗ (π_t² + ϑ u_t²)` subject to
`π_t = β π_{t+1} − κ (u_t − uⁿ)` for all `t ≥ 0`. The Lagrangian argument and the coefficient
`δ` are restated from the Chapter 5 project (with `x = −u` and a constant cost-push term
`κuⁿ`). -/

namespace Commit

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ ≡ ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ ≡ (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - √(1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ (1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), Ch. 5, (14)–(15) (restated): `γ (1 + β) < 1` iff `κ ≠ 0`. -/
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

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `4βγ² < 1`. -/
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

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `√(1 − 4βγ²)² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ · 2γβ = 1 − √(1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - √(1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `γβδ² − δ + γ = 0`. -/
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

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ < 1` iff `κ ≠ 0`. -/
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

/-- Galí (2015), Ch. 5, p. 143 (restated): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Galí (2015), Ch. 5, p. 135 (restated): the lag operator with zero initial condition,
`(lag p)_0 = 0`, `(lag p)_{t+1} = p_t` (encodes `ξ_{−1} = 0`). -/
def lag (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => p t

/-- Galí (2015), Ch. 5, p. 135 (restated): `(lag p)_0 = 0`. -/
@[simp] theorem lag_zero (p : ℕ → ℝ) : lag p 0 = 0 := rfl

/-- Galí (2015), Ch. 5, p. 135 (restated): `(lag p)_{t+1} = p_t`. -/
@[simp] theorem lag_succ (p : ℕ → ℝ) (t : ℕ) : lag p (t + 1) = p t := rfl

/-- Galí (2015), Ch. 5, p. 135: the price-level gap `p̂_t = p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceGap (infl : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), infl s

/-- Galí (2015), Ch. 5, p. 134 (restated; the Lagrangian argument, abstract form): if
`g_t = D_t + 2 (h_t − h_{t+1})` with `D_t ≥ 0`, `h_0 = 0` and `h_t → 0`, and `∑ g_t = G`, then
`∑ D_t = G`. -/
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

/-- Galí (2015), Exercise 7.1(e), p. 220: the constraints `π_t = β π_{t+1} − κ (u_t − uⁿ)`,
`t ≥ 0` (perfect foresight; there are no shocks). -/
def Feasible (β κ un : ℝ) (infl u : ℕ → ℝ) : Prop :=
  ∀ t, infl t = β * infl (t + 1) - κ * (u t - un)

/-- Galí (2015), Exercise 7.1(b),(e), p. 220: the discounted period loss
`βᵗ (π_t² + ϑ u_t²)` (`ϑ = α_u`, correct discounting `βᵗ`). -/
def lossTerm (β ϑ : ℝ) (infl u : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (infl t ^ 2 + ϑ * u t ^ 2)

/-- Galí (2015), Exercise 7.1(e), p. 220: the loss is finite. -/
def FiniteLoss (β ϑ : ℝ) (infl u : ℕ → ℝ) : Prop := Summable (lossTerm β ϑ infl u)

/-- Galí (2015), Exercise 7.1(e), p. 220: the loss `∑_{t ≥ 0} βᵗ (π_t² + ϑ u_t²)` (used on
finite-loss paths). -/
noncomputable def loss (β ϑ : ℝ) (infl u : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ infl u t

/-- Galí (2015), Exercise 7.1(e), p. 220: `(π, u)` solves the commitment problem: feasible,
finite loss, and loss no larger than that of any feasible finite-loss path. -/
def IsOptimal (β κ ϑ un : ℝ) (infl u : ℕ → ℝ) : Prop :=
  Feasible β κ un infl u ∧ FiniteLoss β ϑ infl u ∧
    ∀ π' u', Feasible β κ un π' u' → FiniteLoss β ϑ π' u' → loss β ϑ infl u ≤ loss β ϑ π' u'

/-- Galí (2015), Exercise 7.1(e), p. 220: the first-order conditions of the commitment
problem, `ϑ u_t = −κ ξ_t` and `π_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def FOC (κ ϑ : ℝ) (infl u ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * u t = -(κ * ξ t) ∧ infl t + ξ t - lag ξ t = 0

/-- Galí (2015), Exercise 7.1(e), p. 220 (**the targeting rule under commitment**): the
first-order conditions hold for some multipliers iff `u_t = (κ/ϑ) p̂_t` with
`p̂_t = ∑_{s ≤ t} π_s` (a rule in the price **level**, versus `u_t = (κ/ϑ) π_t` under
discretion). -/
theorem foc_iff_targeting {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (infl u : ℕ → ℝ) :
    (∃ ξ, FOC κ ϑ infl u ξ) ↔ ∀ t, u t = κ / ϑ * priceGap infl t := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have hξp : ∀ t, ξ t = -priceGap infl t := by
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
    refine ⟨fun t => -priceGap infl t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp
    · cases t with
      | zero => simp [priceGap]
      | succ t =>
        simp only [lag_succ, priceGap, Finset.sum_range_succ _ (t + 1)]
        ring

/-- Galí (2015), Exercise 7.1(e), p. 220 (restated from Chapter 5; transversality): on a
finite-loss path `βᵗ π_t² → 0` and `βᵗ u_t² → 0`. -/
theorem tendsto_disc_sq {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) {infl u : ℕ → ℝ}
    (hl : FiniteLoss β ϑ infl u) :
    Tendsto (fun t => β ^ t * infl t ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  have hL := hl.tendsto_atTop_zero
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * (ϑ * u t ^ 2) := by positivity
    simp only [lossTerm]
    nlinarith
  · have hL' := hL.div_const ϑ
    rw [zero_div] at hL'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL'
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * infl t ^ 2 := by positivity
    simp only [lossTerm]
    rw [le_div_iff₀ hϑ]
    nlinarith

/-- **Galí (2015), Exercise 7.1(e), p. 220 (sufficiency of the first-order conditions,
Lagrangian identity; adapted from the Chapter 5 project)**: if a feasible finite-loss path
`(π*, u*)` satisfies the first-order conditions with multipliers `ξ` (`ξ_{−1} = 0`), then for
every feasible finite-loss path `(π, u)`,
`L(π, u) − L(π*, u*) = ∑ βᵗ ((π_t − π*_t)² + ϑ (u_t − u*_t)²)`. -/
theorem loss_sub_hasSum {β κ ϑ un : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {infl u πs us ξ : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u)
    (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us) (hξ : FOC κ ϑ πs us ξ) :
    HasSum (fun t => β ^ t * ((infl t - πs t) ^ 2 + ϑ * (u t - us t) ^ 2))
      (loss β ϑ infl u - loss β ϑ πs us) := by
  have hξx : ∀ t, ξ t = -(ϑ / κ) * us t := fun t => by
    field_simp; linarith [(hξ t).1]
  obtain ⟨hπ0, -⟩ := tendsto_disc_sq hβ0 hϑ hl
  obtain ⟨hπs0, hxs0⟩ := tendsto_disc_sq hβ0 hϑ hls
  have hξ0 : Tendsto (fun t => β ^ t * ξ t ^ 2) atTop (𝓝 0) := by
    have : (fun t => β ^ t * ξ t ^ 2) = fun t => (ϑ / κ) ^ 2 * (β ^ t * us t ^ 2) := by
      funext t; rw [hξx t]; ring
    rw [this]
    simpa using hxs0.const_mul ((ϑ / κ) ^ 2)
  have hlag0 : Tendsto (fun t => β ^ t * lag ξ t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * lag ξ (t + 1) ^ 2) = fun t => β * (β ^ t * ξ t ^ 2) := by
      funext t; rw [lag_succ, pow_succ]; ring
    rw [this]
    simpa using hξ0.const_mul β
  have hd0 : Tendsto (fun t => β ^ t * (infl t - πs t) ^ 2) atTop (𝓝 0) := by
    have hup := (hπ0.const_mul 2).add (hπs0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun t => by positivity) (fun t => ?_)
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have : (infl t - πs t) ^ 2 ≤ 2 * infl t ^ 2 + 2 * πs t ^ 2 := by
      nlinarith [sq_nonneg (infl t + πs t)]
    have := mul_le_mul_of_nonneg_left this hb
    simp only
    nlinarith
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum)
    (fun t => by positivity) (h := fun t => β ^ t * lag ξ t * (infl t - πs t))
    (fun t => ?_) (by simp) ?_
  · have n1 := hf t
    have n2 := hfs t
    have f1 := (hξ t).1
    have f2 := (hξ t).2
    simp only [lossTerm, lag_succ]
    linear_combination β ^ t * (2 * (infl t - πs t) * f2 + 2 * (u t - us t) * f1 -
      2 * ξ t * (n1 - n2))
  · have hup := hlag0.add hd0
    rw [add_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have hab : |lag ξ t * (infl t - πs t)| ≤ lag ξ t ^ 2 + (infl t - πs t) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (lag ξ t + (infl t - πs t)),
        sq_nonneg (lag ξ t - (infl t - πs t))]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hb]
    nlinarith [mul_le_mul_of_nonneg_left hab hb]

/-- **Galí (2015), Exercise 7.1(e), p. 220 (optimality)**: a feasible finite-loss path satisfying
the first-order conditions is optimal. -/
theorem isOptimal_of_foc {β κ ϑ un : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {πs us ξ : ℕ → ℝ} (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us)
    (hξ : FOC κ ϑ πs us ξ) : IsOptimal β κ ϑ un πs us :=
  ⟨hfs, hls, fun _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hϑ hκ hf hl hfs hls hξ).nonneg (fun t => by positivity))⟩

/-- **Galí (2015), Exercise 7.1(e), p. 220 (uniqueness)**: a feasible finite-loss path with the
same loss as a path satisfying the first-order conditions coincides with it. -/
theorem eq_of_loss_eq {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {infl u πs us ξ : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u)
    (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us) (hξ : FOC κ ϑ πs us ξ)
    (heq : loss β ϑ infl u = loss β ϑ πs us) : infl = πs ∧ u = us := by
  have hs := loss_sub_hasSum hβ0.le hϑ hκ hf hl hfs hls hξ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, (infl t - πs t) ^ 2 + ϑ * (u t - us t) ^ 2 = 0 := fun t => by
    have := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have h1 := ht t
    have : (infl t - πs t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (infl t - πs t), sq_nonneg (u t - us t)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · have h1 := ht t
    have h2 : ϑ * (u t - us t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (infl t - πs t), sq_nonneg (u t - us t)]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hϑ.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith

/-- Galí (2015), Exercise 7.1(e), p. 220 (restated from Chapter 5): a bounded path has finite
loss. -/
theorem finiteLoss_of_bounded {β ϑ A B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {infl u : ℕ → ℝ} (hπ : ∀ t, |infl t| ≤ A) (hu : ∀ t, |u t| ≤ B) :
    FiniteLoss β ϑ infl u := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2))
  have h1 : infl t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπ t) 2
  have h2 : u t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hu t) 2
  unfold lossTerm
  exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h2 hϑ])
    (pow_nonneg hβ0 t)

/-- Galí (2015), Exercise 7.1(e), p. 220: the long-run price-level gap under commitment,
`p̄ = ϑuⁿ/κ`. -/
noncomputable def pbar (κ ϑ un : ℝ) : ℝ := ϑ * un / κ

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment inflation**):
`π_t = p̄ (1 − δ) δᵗ`. -/
noncomputable def commInfl (β κ ϑ un : ℝ) (t : ℕ) : ℝ :=
  pbar κ ϑ un * (1 - del β κ ϑ) * del β κ ϑ ^ t

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment unemployment**):
`u_t = uⁿ (1 − δ^{t+1})`. -/
noncomputable def commU (β κ ϑ un : ℝ) (t : ℕ) : ℝ := un * (1 - del β κ ϑ ^ (t + 1))

/-- Galí (2015), Exercise 7.1(e), p. 220: under commitment the price-level gap is
`p̂_t = p̄ (1 − δ^{t+1})`, and `u_t = (κ/ϑ) p̂_t`. -/
theorem priceGap_commInfl {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (t : ℕ) :
    priceGap (commInfl β κ ϑ un) t = pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)) ∧
      commU β κ ϑ un t = κ / ϑ * priceGap (commInfl β κ ϑ un) t := by
  have hg : priceGap (commInfl β κ ϑ un) t = pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)) := by
    induction t with
    | zero => simp [priceGap, commInfl]
    | succ t ih =>
      rw [priceGap, Finset.sum_range_succ, ← priceGap, ih, commInfl]
      ring
  refine ⟨hg, ?_⟩
  rw [hg, commU, pbar]
  field_simp

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path is feasible. -/
theorem comm_feasible {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    Feasible β κ un (commInfl β κ ϑ un) (commU β κ ϑ un) := by
  intro t
  have hk := kappa_sq_del (κ := κ) hβ0 hβ1 hϑ
  set d := del β κ ϑ
  have hk' : κ ^ 2 * d = ϑ * ((1 - d) * (1 - β * d)) := by
    rw [div_eq_iff hϑ.ne'] at hk
    linarith
  simp only [commInfl, commU, pbar, pow_succ]
  field_simp
  linear_combination (-(un * d ^ t)) * hk'

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path satisfies the first-order
conditions with `ξ_t = −p̂_t = −p̄(1 − δ^{t+1})`. -/
theorem comm_foc {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    FOC κ ϑ (commInfl β κ ϑ un) (commU β κ ϑ un)
      (fun t => -(pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)))) := by
  intro t
  refine ⟨?_, ?_⟩
  · simp only [commU, pbar]
    field_simp
  · cases t with
    | zero => simp [commInfl]
    | succ t =>
      simp only [lag_succ, commInfl]
      ring

/-- Galí (2015), Exercise 7.1(e), p. 220: `δ ∈ (0, 1)` for `κ ≠ 0`. -/
theorem del_mem {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    0 < del β κ ϑ ∧ del β κ ϑ < 1 :=
  ⟨del_pos hβ0 hϑ, (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ⟩

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path has finite loss. -/
theorem comm_finiteLoss {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) : FiniteLoss β ϑ (commInfl β κ ϑ un) (commU β κ ϑ un) := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ hϑ
  refine finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (A := |pbar κ ϑ un|) (B := |un|)
    (fun t => ?_) (fun t => ?_)
  · have h1 : |(1 - del β κ ϑ) * del β κ ϑ ^ t| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by linarith), abs_of_pos (pow_pos hd0 t)]
      have : del β κ ϑ ^ t ≤ 1 := pow_le_one₀ hd0.le hd1.le
      nlinarith [pow_pos hd0 t]
    simp only [commInfl, mul_assoc]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  · have h1 : |1 - del β κ ϑ ^ (t + 1)| ≤ 1 := by
      have h2 : 0 < del β κ ϑ ^ (t + 1) := pow_pos hd0 _
      have h3 : del β κ ϑ ^ (t + 1) ≤ 1 := pow_le_one₀ hd0.le hd1.le
      rw [abs_le]
      constructor <;> linarith
    simp only [commU]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- **Galí (2015), Exercise 7.1(e), p. 220 (THE OPTIMAL POLICY UNDER COMMITMENT)**: for
`κ ≠ 0`, `ϑ > 0`, `0 < β < 1`, the path `π_t = p̄(1 − δ)δᵗ`, `u_t = uⁿ(1 − δ^{t+1})` is optimal,
and it is the **only** optimal path. -/
theorem isOptimal_iff {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (infl u : ℕ → ℝ) :
    IsOptimal β κ ϑ un infl u ↔ infl = commInfl β κ ϑ un ∧ u = commU β κ ϑ un := by
  have hc : IsOptimal β κ ϑ un (commInfl β κ ϑ un) (commU β κ ϑ un) :=
    isOptimal_of_foc hβ0.le hϑ hκ (comm_feasible hβ0 hβ1 hκ hϑ) (comm_finiteLoss hβ0 hβ1 hκ hϑ)
      (comm_foc hκ hϑ)
  constructor
  · rintro ⟨hf, hl, hmin⟩
    have h1 := hmin _ _ hc.1 hc.2.1
    have h2 := hc.2.2 _ _ hf hl
    exact eq_of_loss_eq hβ0 hϑ hκ hf hl hc.1 hc.2.1 (comm_foc hκ hϑ) (le_antisymm h1 h2)
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- **Galí (2015), Exercise 7.1(e), p. 220 (first-order conditions necessary and
sufficient)**: a feasible finite-loss path is optimal iff it satisfies the targeting rule
`u_t = (κ/ϑ) p̂_t`. -/
theorem isOptimal_iff_targeting {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) {infl u : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u) :
    IsOptimal β κ ϑ un infl u ↔ ∀ t, u t = κ / ϑ * priceGap infl t := by
  rw [← foc_iff_targeting hϑ.ne']
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := (isOptimal_iff hβ0 hβ1 hκ hϑ infl u).1 h
    exact ⟨_, comm_foc hκ hϑ⟩
  · rintro ⟨ξ, hξ⟩
    exact isOptimal_of_foc hβ0.le hϑ hκ hf hl hξ

/-- Galí (2015), Exercise 7.1(e), p. 220 (**no long-run inflation bias under commitment**):
`π_t → 0` and `u_t → uⁿ`. -/
theorem commitment_tendsto {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) :
    Tendsto (commInfl β κ ϑ un) atTop (𝓝 0) ∧ Tendsto (commU β κ ϑ un) atTop (𝓝 un) := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ hϑ
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hd0.le hd1
  constructor
  · have h := hp.const_mul (pbar κ ϑ un * (1 - del β κ ϑ))
    rw [mul_zero] at h
    exact h
  · have hp1 : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hp
    have h := (hp1.const_sub 1).const_mul un
    rw [sub_zero, mul_one] at h
    exact h

/-- Galí (2015), Exercise 7.1(e), p. 220: with `uⁿ > 0`, `κ, ϑ > 0`, commitment inflation is
positive and strictly decreasing, and commitment unemployment rises strictly towards `uⁿ`. -/
theorem commitment_monotone {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) :
    (∀ t, 0 < commInfl β κ ϑ un t) ∧ StrictAnti (commInfl β κ ϑ un) ∧
      StrictMono (commU β κ ϑ un) ∧ ∀ t, commU β κ ϑ un t < un := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ.ne' hϑ
  have hp : 0 < pbar κ ϑ un := by unfold pbar; positivity
  have hc : 0 < pbar κ ϑ un * (1 - del β κ ϑ) := mul_pos hp (by linarith)
  refine ⟨fun t => by unfold commInfl; positivity, ?_, ?_, fun t => ?_⟩
  · refine strictAnti_nat_of_succ_lt fun t => ?_
    simp only [commInfl, pow_succ]
    have := pow_pos hd0 t
    nlinarith [mul_pos hc this]
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [commU, pow_succ]
    have := pow_pos hd0 t
    nlinarith [mul_pos (mul_pos this hd0) hun]
  · simp only [commU]
    have := pow_pos hd0 (t + 1)
    nlinarith

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment inflation is below discretionary
inflation at every date**): for `κ, ϑ > 0`, `0 < β < 1`, `uⁿ > 0`, `π^c_t < π*` for all `t`. -/
theorem commInfl_lt_piStar {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) (t : ℕ) : commInfl β κ ϑ un t < piStar β κ ϑ un := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ.ne' hϑ
  have hk := kappa_sq_del (κ := κ) hβ0 hβ1 hϑ
  set d := del β κ ϑ
  have hk' : κ ^ 2 * d = ϑ * ((1 - d) * (1 - β * d)) := by
    rw [div_eq_iff hϑ.ne'] at hk
    linarith
  have hD := den_pos (κ := κ) hϑ hβ1
  have h0 : commInfl β κ ϑ un t ≤ commInfl β κ ϑ un 0 := by
    have := (commitment_monotone hβ0 hβ1 hκ hϑ hun).2.1.antitone (Nat.zero_le t)
    exact this
  refine h0.trans_lt ?_
  simp only [commInfl, pbar, pow_zero, mul_one, piStar]
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hκ hD]
  -- `d((1 − d)(κ² + ϑ(1 − β)) − κ²) = −ϑβd(1 − d)²`, using `κ²d = ϑ(1 − d)(1 − βd)`
  have key : d * ((1 - d) * (κ ^ 2 + ϑ * (1 - β)) - κ ^ 2) = -(ϑ * β * d * (1 - d) ^ 2) := by
    linear_combination (-d) * hk'
  have hneg : (1 - d) * (κ ^ 2 + ϑ * (1 - β)) - κ ^ 2 < 0 := by
    have hr : 0 < ϑ * β * d * (1 - d) ^ 2 := by
      have : 0 < 1 - d := by linarith
      positivity
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hd0.le hc]
  have hpos : 0 < ϑ * un * κ := by positivity
  nlinarith [mul_lt_mul_of_pos_left hneg hpos]

/-- Galí (2015), Exercise 7.1(c),(e), p. 220: the discretionary path `(π*, u*)` is feasible in
the commitment problem and has finite loss. -/
theorem disc_feasible {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    Feasible β κ un (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) ∧
      FiniteLoss β ϑ (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) :=
  ⟨fun _ => piStar_nkpc hϑ hβ1,
    finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- **Galí (2015), Exercise 7.1(e), p. 220 (commitment versus discretion)**: for `κ, ϑ > 0`,
`0 < β < 1`, `uⁿ > 0`, the commitment path has strictly lower loss than the discretionary path;
commitment inflation is below `π*` at every date and converges to `0` (no long-run bias), while
under discretion `π_t = π* > 0` forever and `u_t = u* < uⁿ` forever (unemployment is held
permanently below its natural rate at the cost of permanently positive inflation). -/
theorem commitment_beats_discretion {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) :
    loss β ϑ (commInfl β κ ϑ un) (commU β κ ϑ un) <
        loss β ϑ (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) ∧
      (∀ t, commInfl β κ ϑ un t < piStar β κ ϑ un) ∧
      Tendsto (commInfl β κ ϑ un) atTop (𝓝 0) ∧ 0 < piStar β κ ϑ un ∧
      Tendsto (commU β κ ϑ un) atTop (𝓝 un) ∧ uStar β κ ϑ un < un := by
  have hc := (isOptimal_iff (un := un) hβ0 hβ1 hκ.ne' hϑ _ _).2 ⟨rfl, rfl⟩
  obtain ⟨hdf, hdl⟩ := disc_feasible (κ := κ) (un := un) hβ0 hβ1 hϑ
  have hle := hc.2.2 _ _ hdf hdl
  refine ⟨lt_of_le_of_ne hle fun heq => ?_, commInfl_lt_piStar hβ0 hβ1 hκ hϑ hun,
    (commitment_tendsto hβ0 hβ1 hκ.ne' hϑ).1, inflationBias_pos hκ hϑ hβ1 hun,
    (commitment_tendsto hβ0 hβ1 hκ.ne' hϑ).2, (uStar_lt_un hκ.ne' hϑ hβ1 hun).2⟩
  obtain ⟨h1, -⟩ := eq_of_loss_eq hβ0 hϑ hκ.ne' hdf hdl hc.1 hc.2.1 (comm_foc hκ.ne' hϑ)
    heq.symm
  have := commInfl_lt_piStar hβ0 hβ1 hκ hϑ hun 0
  rw [← h1] at this
  exact lt_irrefl _ this

end Commit

end Gali.Unemployment.Ex7_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 7.2: wage inflation with wage-markup and labour-supply shocks

Galí (2015), Chapter 7, Exercise 7.2, p. 221. Member `(j, s)` has labour disutility `χ_t s^φ`
with `ξ_t = log χ_t` exogenous, and the elasticity of substitution between labour types is
time-varying, so the desired wage markup `μ^w_t = log(ε_{w,t}/(ε_{w,t} − 1))` varies.

## (a) The wage equation: `ξ_t` and `μ^w_t` enter symmetrically

* `eq13` and `eq15_iff` are restated from the Chapter 6 project (the reset-wage rule (12) ⇒ its
  recursive form (13); (13) + the wage index (14) ⟺ the wage-inflation equation (15)).
* `eq13_timeVarying`: with a time-varying desired markup `μ^w_t` inside the reset-wage sum (12)
  (`μ^w_{t+k}` in place of the constant `μ^w`; the elasticity in labour demand is evaluated at
  its steady-state value, the usual first-order approximation), the recursive rule (13) holds
  with the markup gap `μ̂^w_t = (w_t − p_t − mrs_t) − μ^w_t`.
* `wageEq_iff_errorForm`, `ex7_2a`: with `mrs_t = σc_t + φn_t + ξ_t`,
  `π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w(ω_{t+1} − σc_{t+1} − φn_{t+1}) + λ_w(ξ_{t+1} + μ^w_{t+1})`;
  `errorForm_hat`: around a steady state the error is `λ_w(ξ̂_t + μ̂^w_t)`.
* `errorForm_depends_on_sum`, `errorForm_shift_iff`, `not_identified`: the equation depends on the
  two shocks only through `ξ_t + μ^w_t`; `(ξ + d, μ^w − d)` is observationally equivalent to
  `(ξ, μ^w)` for every process `d` (the Chari–Kehoe–McGrattan identification problem).

## (b) The unemployment form

* `participation_log`: the marginal participant `W/P = χ_t C^σ L^φ` gives (6) with `ξ_t`,
  `ω_t = σc_t + φl_t + ξ_t` (exact, in logs).
* `ex7_2b`: with participation and `u = l − n`, the wage equation is equivalent to
  `π^w_t = β E_t π^w_{t+1} − λ_wφ(u_t − uⁿ_t)`, `uⁿ_t = μ^w_t/φ`: only `μ^w_t` appears.
* `identified`: in the unemployment form, together with the participation equation, the
  observables `(π^w, ω, c, n, l)` determine both `ξ` and `μ^w` uniquely.
-/

namespace Gali.Unemployment.Ex7_2

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Restated from the Chapter 6 project: (12) ⇒ (13), and (13) + (14) ⟺ (15) -/

/-- Galí (2015), Ch. 6, p. 169 (restated from the Chapter 6 project): the gap of the average log
wage markup from its constant desired value, `μ̂^w_t = (w_t − p_t − mrs_t) − μ^w`. -/
noncomputable def markupGap (μw : ℝ) (w p mrs : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (w t ω - p t ω - mrs t ω) - μw

/-- Galí (2015), Ch. 6, eqs. (12)–(13), p. 169 (**the recursive wage-setting rule**; restated
from the Chapter 6 project). Let the reset
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

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`. -/
noncomputable def lambdaW (β θ ε φ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))

/-- Galí (2015), p. 169: wage inflation `π^w_{t+1} = w_{t+1} − w_t` (dated `t + 1`). -/
noncomputable def wageInfl {Ω : Type*} (w : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := w (t + 1) - w t

/-- Galí (2015), Ch. 6, eqs. (13)–(15), pp. 169–170 (**(13) + (14) ⟺ (15)**; restated from the
Chapter 6 project): with
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

/-! ### (a) A time-varying desired markup -/

/-- Galí (2015), Exercise 7.2(a), p. 221: the gap between the actual average wage markup
`w_t − p_t − mrs_t` and the time-varying desired markup `μ^w_t`. -/
def markupGapTV (w p mrs μd : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => w t ω - p t ω - mrs t ω - μd t ω

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the recursive wage-setting rule with a time-varying
desired markup**): if the reset wage satisfies
`w*_t = (1 − βθ_w) ∑ₖ (βθ_w)ᵏ E_t[μ^w_{t+k} + mrs_{t+k|t} + p_{t+k}]` with
`mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w*_t − w_{t+k})` (bounded adapted `w, p, mrs, μ^w`, adapted `w*`),
then `w*_t = βθ_w E_t w*_{t+1} + (1 − βθ_w)(w_t − (1 + ε_wφ)⁻¹ μ̂^w_t)` with
`μ̂^w_t = (w_t − p_t − mrs_t) − μ^w_t`. -/
theorem eq13_timeVarying {β θ ε φ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hεφ : 0 ≤ ε * φ) {wstar w p mrs μd : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hμ : ∀ t ω, |μd t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hμa : 𝔼.Adapted μd)
    (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + μd (t + k) ω' + p (t + k) ω') ω)
    (hmrs : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω)) :
    ∀ t, wstar t = (β * θ) • 𝔼.E t (wstar (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGapTV w p mrs μd t) := by
  have hm' : ∀ t ω, |(mrs + μd) t ω| ≤ M + M := fun t ω => by
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hm t ω) (hμ t ω))
  have hw' : ∀ t ω, |w t ω| ≤ M + M := fun t ω => by
    have := abs_nonneg (μd t ω)
    linarith [hw t ω, hμ t ω]
  have hp' : ∀ t ω, |p t ω| ≤ M + M := fun t ω => by
    have := abs_nonneg (μd t ω)
    linarith [hp t ω, hμ t ω]
  have hma' : 𝔼.Adapted (mrs + μd) := fun t => by
    simp only [Pi.add_apply, map_add, hma t, hμa t]
  have h12' : ∀ t ω, wstar t ω = 0 + (1 - β * θ) * ∑' k, (β * θ) ^ k *
      𝔼.E t (fun ω' => (fun t k ω => mrsR t k ω + μd (t + k) ω) t k ω' + p (t + k) ω') ω :=
    fun t ω => by rw [zero_add]; exact h12 t ω
  have hmrs' : ∀ t k ω, (fun t k ω => mrsR t k ω + μd (t + k) ω) t k ω =
      (mrs + μd) (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω) := fun t k ω => by
    simp only [Pi.add_apply, hmrs]
    ring
  have h := (eq13 𝔼 hβ0 hβ1 hθ0 hθ1 hεφ hw' hp' hm' hwa hpa hma' hsa h12' hmrs').1
  intro t
  have e : markupGap 0 w p (mrs + μd) t = markupGapTV w p mrs μd t := by
    funext ω
    simp only [markupGap, markupGapTV, Pi.add_apply]
    ring
  rw [h t, e]

/-- Galí (2015), Exercise 7.2(a), p. 221: the wage-inflation equation written as a function of
the real wage `ω`, consumption and employment, with the error term `λ_w (ξ_t + μ^w_t)`:
`π^w_t = β E_t π^w_{t+1} − λ_w (ω_t − σ c_t − φ n_t) + λ_w (ξ_t + μ^w_t)`. -/
def ErrorForm (β lamW σ φ : ℝ) (piW wr c n ξ μd : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piW t = β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) +
    lamW • (ξ t + μd t)

/-- Galí (2015), Exercise 7.2(a), p. 221 (**exact algebra**): with `mrs = σc + φn + ξ`, the
wage-inflation equation (15) `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`,
`μ̂^w_t = ω_t − mrs_t − μ^w_t`, is the error form with error `λ_w(ξ_t + μ^w_t)`. -/
theorem wageEq_iff_errorForm {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ} :
    (∀ t, piW t = β • 𝔼.E t (piW (t + 1)) -
        lamW • (wr t - (σ • c t + φ • n t + ξ t) - μd t)) ↔
      ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - (σ • c t + φ • n t + ξ t) - μd t) =
      β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) + lamW • (ξ t + μd t) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]

/-- **Galí (2015), Exercise 7.2(a), p. 221 (the wage equation, derived)**: given the reset-wage
rule (12) with time-varying desired markup `μ^w_t` (`eq13_timeVarying`), the wage index (14),
`mrs_t = σc_t + φn_t + ξ_t` and real wage `ω_t = w_t − p_t`, wage inflation
`π^w_{t+1} = w_{t+1} − w_t` satisfies the error form at every date `t + 1`:
`π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w(ω_{t+1} − σc_{t+1} − φn_{t+1}) + λ_w(ξ_{t+1} + μ^w_{t+1})`.
-/
theorem ex7_2a {β θ ε φ σ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 ≤ ε) (hφ : 0 ≤ φ) {wstar w p mrs μd c n ξ : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hμ : ∀ t ω, |μd t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hμa : 𝔼.Adapted μd)
    (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + μd (t + k) ω' + p (t + k) ω') ω)
    (hmrsR : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω))
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1))
    (hmrs : ∀ t, mrs t = σ • c t + φ • n t + ξ t) :
    ∀ t, wageInfl w t = β • 𝔼.E (t + 1) (wageInfl w (t + 1)) -
      lambdaW β θ ε φ • ((w (t + 1) - p (t + 1)) - σ • c (t + 1) - φ • n (t + 1)) +
      lambdaW β θ ε φ • (ξ (t + 1) + μd (t + 1)) := by
  have hεφ : 0 ≤ ε * φ := mul_nonneg hε hφ
  have h13 := eq13_timeVarying 𝔼 hβ0 hβ1 hθ0.le hθ1 hεφ hw hp hm hμ hwa hpa hma hμa hsa h12 hmrsR
  have h15 := (eq15_iff 𝔼 hθ0 hθ1 (by linarith) (μhat := markupGapTV w p mrs μd) hwa h14).mp
    fun t => h13 (t + 1)
  intro t
  rw [h15 t]
  funext ω
  simp only [markupGapTV, hmrs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the error in deviations, `λ_w(ξ̂ + μ̂^w)`**): if the
steady state satisfies `ω̄ − σc̄ − φn̄ = ξ̄ + μ̄` (the wage-markup condition), then writing every
variable as steady state plus deviation (`ω = ω̄ + ω̂`, …), the error form in levels holds iff
`π^w_t = β E_t π^w_{t+1} − λ_w(ω̂_t − σĉ_t − φn̂_t) + λ_w(ξ̂_t + μ̂^w_t)`. -/
theorem errorForm_hat {β lamW σ φ wbar cbar nbar ξbar μbar : ℝ}
    (hss : wbar - σ * cbar - φ * nbar = ξbar + μbar) {piW wh ch nh ξh μh : ℕ → Ω → ℝ} :
    ErrorForm 𝔼 β lamW σ φ piW (fun t => wh t + fun _ => wbar) (fun t => ch t + fun _ => cbar)
        (fun t => nh t + fun _ => nbar) (fun t => ξh t + fun _ => ξbar)
        (fun t => μh t + fun _ => μbar) ↔
      ErrorForm 𝔼 β lamW σ φ piW wh ch nh ξh μh := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • ((wh t + fun _ => wbar) -
      σ • (ch t + fun _ => cbar) - φ • (nh t + fun _ => nbar)) +
      lamW • ((ξh t + fun _ => ξbar) + (μh t + fun _ => μbar)) =
      β • 𝔼.E t (piW (t + 1)) - lamW • (wh t - σ • ch t - φ • nh t) + lamW • (ξh t + μh t) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-lamW) * hss
  rw [e]

/-- Galí (2015), Exercise 7.2(a), p. 221 (**symmetry: only the sum `ξ + μ^w` matters**): if
`ξ_t + μ^w_t = ξ'_t + μ'^w_t` at every date, the error forms with `(ξ, μ^w)` and `(ξ', μ'^w)`
are the same restriction on the observables `(π^w, ω, c, n)`. -/
theorem errorForm_depends_on_sum {β lamW σ φ : ℝ} {piW wr c n ξ μd ξ' μd' : ℕ → Ω → ℝ}
    (hsum : ∀ t, ξ t + μd t = ξ' t + μd' t) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd ↔ ErrorForm 𝔼 β lamW σ φ piW wr c n ξ' μd' := by
  refine forall_congr' fun t => ?_
  rw [hsum t]

/-- Galí (2015), Exercise 7.2(a), p. 221 (**observational equivalence**): for every process `d`,
`(ξ + d, μ^w − d)` satisfies the wage equation exactly when `(ξ, μ^w)` does. -/
theorem errorForm_shift_iff {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ}
    (d : ℕ → Ω → ℝ) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n (fun t => ξ t + d t) (fun t => μd t - d t) ↔
      ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd :=
  errorForm_depends_on_sum 𝔼 fun t => by abel

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the identification problem**, Chari, Kehoe and
McGrattan 2009): given any observables `(π^w, ω, c, n)` consistent with the wage equation for
some shocks `(ξ, μ^w)`, there is a **different** pair of shocks (`(ξ + 1, μ^w − 1)`) consistent
with the same observables: the wage equation alone cannot separate preference shocks from
wage-markup shocks. -/
theorem not_identified [Nonempty Ω] {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ}
    (h : ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd) :
    ∃ ξ' μd' : ℕ → Ω → ℝ, ErrorForm 𝔼 β lamW σ φ piW wr c n ξ' μd' ∧ ξ' ≠ ξ ∧ μd' ≠ μd := by
  refine ⟨fun t => ξ t + fun _ => 1, fun t => μd t - fun _ => 1,
    (errorForm_shift_iff 𝔼 (fun _ _ => 1)).mpr h, fun he => ?_, fun he => ?_⟩
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun he 0) ω
    simp only [Pi.add_apply] at this
    linarith
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun he 0) ω
    simp only [Pi.sub_apply] at this
    linarith

/-! ### (b) The unemployment form -/

/-- Galí (2015), Exercise 7.2(b), p. 221 (with (5)–(6), p. 204, **exact in logs**): the marginal
participant of a labour type satisfies `W/P = χ_t C^σ L^φ`; taking logs,
`ω = σc + φl + ξ` with `ω = log(W/P)`, `c = log C`, `l = log L`, `ξ = log χ`. -/
theorem participation_log {σ φ χ C L WP : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hL : 0 < L)
    (h5 : WP = χ * C ^ σ * L ^ φ) :
    Real.log WP = σ * Real.log C + φ * Real.log L + Real.log χ := by
  rw [h5, Real.log_mul (by positivity) (by positivity), Real.log_mul hχ.ne' (by positivity),
    Real.log_rpow hC, Real.log_rpow hL]
  ring

/-- Galí (2015), Exercise 7.2(b), p. 221: the wage equation in terms of the unemployment rate,
`π^w_t = β E_t π^w_{t+1} − λ_wφ(u_t − uⁿ_t)` with the natural rate `uⁿ_t = μ^w_t/φ`. -/
def UnempForm (β lamW φ : ℝ) (piW u μd : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piW t = β • 𝔼.E t (piW (t + 1)) - (lamW * φ) • (u t - φ⁻¹ • μd t)

/-- **Galí (2015), Exercise 7.2(b), p. 221 (only `μ^w_t` appears)**: with the participation
equation `ω_t = σc_t + φl_t + ξ_t` and `u_t = l_t − n_t`, the wage equation (error form, with
both shocks) holds iff the unemployment form holds, in which the preference shock `ξ_t` no
longer appears (it is absorbed into the labour force through participation) and the
wage-markup shock enters through the natural rate `uⁿ_t = μ^w_t/φ` (`φ ≠ 0`). -/
theorem ex7_2b {β lamW σ φ : ℝ} (hφ : φ ≠ 0) {piW wr c n l u ξ μd : ℕ → Ω → ℝ}
    (h6 : ∀ t, wr t = σ • c t + φ • l t + ξ t) (h7 : ∀ t, u t = l t - n t) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd ↔ UnempForm 𝔼 β lamW φ piW u μd := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) + lamW • (ξ t + μd t) =
      β • 𝔼.E t (piW (t + 1)) - (lamW * φ) • (u t - φ⁻¹ • μd t) := by
    rw [h6 t, h7 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [e]

/-- **Galí (2015), Exercise 7.2(b), p. 221 (the unemployment form restores identification)**:
for `λ_w ≠ 0`, `φ ≠ 0`, if two pairs of shocks `(ξ, μ^w)` and `(ξ', μ'^w)` are both consistent
with the same observables `(π^w, ω, c, l, u)` through the participation equation and the
unemployment form of the wage equation, then `ξ = ξ'` and `μ^w = μ'^w`: the participation
equation identifies `ξ_t = ω_t − σc_t − φl_t`, and the wage equation identifies
`μ^w_t = φ u_t − (π^w_t − β E_t π^w_{t+1})/λ_w`. -/
theorem identified {β lamW σ φ : ℝ} (hlam : lamW ≠ 0) (hφ : φ ≠ 0)
    {piW wr c l u ξ μd ξ' μd' : ℕ → Ω → ℝ}
    (h6 : ∀ t, wr t = σ • c t + φ • l t + ξ t) (h6' : ∀ t, wr t = σ • c t + φ • l t + ξ' t)
    (hU : UnempForm 𝔼 β lamW φ piW u μd) (hU' : UnempForm 𝔼 β lamW φ piW u μd') :
    ξ = ξ' ∧ μd = μd' := by
  refine ⟨funext fun t => ?_, funext fun t => funext fun ω => ?_⟩
  · have := (h6 t).symm.trans (h6' t)
    exact add_left_cancel this
  · have a := congrFun (hU t) ω
    have b := congrFun (hU' t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
    have hc : lamW * φ * φ⁻¹ ≠ 0 := by
      rw [mul_assoc, mul_inv_cancel₀ hφ, mul_one]
      exact hlam
    have : lamW * φ * φ⁻¹ * (μd t ω - μd' t ω) = 0 := by linear_combination b - a
    have := (mul_eq_zero.mp this).resolve_left hc
    linarith

end Gali.Unemployment.Ex7_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 7.3: taming the wealth effect on labour supply

Galí (2015), Chapter 7, Exercise 7.3, pp. 221–222. Member `(j, s)` has utility
`log C_t(j, s) − 1_t(j, s) χ_t Θ_t s^φ`, with `Θ_t = Z_t/C̄_t`, `C̄_t` aggregate consumption and
`Z_t = Z_{t−1}^{1−υ} C̄_t^υ`, `υ ∈ [0, 1]`; consumption is fully shared within the household.

## (a) Household utility

* `integral_disutility`: `∫₀¹ 1{s ≤ N} K s^φ ds = K N^{1+φ}/(1 + φ)` (a genuine interval
  integral; members `s ∈ [0, N]`, those with the lowest disutility, are employed).
* `member_integral`, `household_utility`: with full risk sharing `C_t(j, s) = C_t`,
  `∫₀¹∫₀¹ U(j, s) ds dj = log C_t − χ_tΘ_t ∫₀¹ N_t(j)^{1+φ}/(1 + φ) dj`.

## (b) Participation and the wealth effect

* `works_iff`: member `(j, s)` works iff `(W/P)/C ≥ χΘs^φ`; `participants_iff`: the participants
  of a type are exactly `s ≤ L = ((W/P)/(CχΘ))^{1/φ}`.
* `participation_log`: at the marginal participant, with `C = C̄`,
  `w − p = ξ_t + z_t + φ l` (exact in logs); `z_log`: `z_t = (1 − υ) z_{t−1} + υ c_t`.
* `zPath`, `zPath_one` (`υ = 1 ⇒ z = c`, the log-utility wealth effect of (6) with `σ = 1`,
  `participation_upsilon_one`), `zPath_zero` (`υ = 0 ⇒ z` constant: no wealth effect).
* `zPath_add`: the response of `z` to a consumption perturbation does not depend on the baseline;
  `zPath_permanent`: to a permanent change `Δ`, `z` responds by `(1 − (1 − υ)^{t+1}) Δ`;
  `labourForce_response`: the labour force responds by `−(1 − (1 − υ)^{t+1}) Δ/φ`.
* **Dampening** (`dampening_strictMonoOn`, `labourForce_dampening`): the size of that response is
  strictly increasing in `υ ∈ [0, 1]`, from `0` (`υ = 0`) to the full `|Δ|/φ` (`υ = 1`); the impact
  response to any consumption change is `υ` times the full one (`zPath_pulse`).
* Precision note (`lagged_pulse_not_monotone`): the response at lag `k ≥ 1` to a *one-period*
  consumption change, `υ(1 − υ)ᵏ`, is not monotone in `υ`; the dampening claim holds for impact and
  for persistent changes.
-/

namespace Gali.Unemployment.Ex7_3

/-! ### (a) Household utility -/

/-- Galí (2015), Exercise 7.3, p. 221: the period utility of member `s` of a labour type with
employment rate `N`: `log C − 1{s ≤ N} χΘ s^φ` (members `s ∈ [0, N]` work; `K = χΘ`). -/
noncomputable def memberU (C K φ N s : ℝ) : ℝ :=
  Real.log C - (Set.Iic N).indicator (fun s => K * s ^ φ) s

/-- Galí (2015), Exercise 7.3(a), p. 222: `s ↦ 1{s ≤ N} K s^φ` is interval integrable on
`[0, 1]` (for `φ ≥ 0`). -/
theorem disutility_intervalIntegrable {K φ N : ℝ} (hφ : 0 ≤ φ) :
    IntervalIntegrable ((Set.Iic N).indicator (fun s => K * s ^ φ)) MeasureTheory.volume 0 1 := by
  have hc : Continuous (fun s : ℝ => K * s ^ φ) :=
    continuous_const.mul (Real.continuous_rpow_const hφ)
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ?_
  exact (hc.intervalIntegrable 0 1).1.indicator measurableSet_Iic

/-- Galí (2015), Exercise 7.3(a), p. 222 (**the disutility integral**): for `φ ≥ 0` and
`0 ≤ N ≤ 1`, `∫₀¹ 1{s ≤ N} K s^φ ds = K N^{1+φ}/(1 + φ)`. -/
theorem integral_disutility {K φ N : ℝ} (hφ : 0 ≤ φ) (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    ∫ s in (0 : ℝ)..1, (Set.Iic N).indicator (fun s => K * s ^ φ) s =
      K * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iic N = Set.Ioc 0 N := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h0, -⟩, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩
      exact ⟨⟨h0, h2.trans hN1⟩, h2⟩
  rw [hset, ← intervalIntegral.integral_of_le hN0, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  rw [add_comm φ 1]
  ring

/-- Galí (2015), Exercise 7.3(a), p. 222 (**one labour type**): with full risk sharing
(`C(j, s) = C` for every member) the integral of members' utilities over `s ∈ [0, 1]` is
`log C − K N^{1+φ}/(1 + φ)`. -/
theorem member_integral {C K φ N : ℝ} (hφ : 0 ≤ φ) (hN0 : 0 ≤ N) (hN1 : N ≤ 1)
    {Cm : ℝ → ℝ} (hrs : ∀ s, Cm s = C) :
    ∫ s in (0 : ℝ)..1, memberU (Cm s) K φ N s = Real.log C - K * N ^ (1 + φ) / (1 + φ) := by
  simp only [memberU, hrs]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (disutility_intervalIntegrable hφ), intervalIntegral.integral_const,
    integral_disutility hφ hN0 hN1]
  simp

/-- Galí (2015), Exercise 7.3(a), p. 222: `Θ_t = Z_t/C̄_t`. -/
noncomputable def theta (Z Cbar : ℝ) : ℝ := Z / Cbar

/-- **Galí (2015), Exercise 7.3(a), p. 222 (the household's period utility)**: with full risk
sharing (`C(j, s) = C_t`), employment rates `N(j) ∈ [0, 1]` with `j ↦ N(j)^{1+φ}` integrable, and
`Θ_t = Z_t/C̄_t`, the integral over the household's members `(j, s) ∈ [0, 1]²` of
`log C(j, s) − 1(j, s) χ_t Θ_t s^φ` equals `log C_t − χ_tΘ_t ∫₀¹ N(j)^{1+φ}/(1 + φ) dj`. -/
theorem household_utility {C χ Z Cbar φ : ℝ} (hφ : 0 ≤ φ) {N : ℝ → ℝ}
    (hN0 : ∀ j, 0 ≤ N j) (hN1 : ∀ j, N j ≤ 1)
    (hint : IntervalIntegrable (fun j => N j ^ (1 + φ) / (1 + φ)) MeasureTheory.volume 0 1)
    {Cm : ℝ → ℝ → ℝ} (hrs : ∀ j s, Cm j s = C) :
    ∫ j in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, memberU (Cm j s) (χ * theta Z Cbar) φ (N j) s =
      Real.log C - χ * theta Z Cbar * ∫ j in (0 : ℝ)..1, N j ^ (1 + φ) / (1 + φ) := by
  have h1 : ∀ j, ∫ s in (0 : ℝ)..1, memberU (Cm j s) (χ * theta Z Cbar) φ (N j) s =
      Real.log C - χ * theta Z Cbar * (N j ^ (1 + φ) / (1 + φ)) := fun j => by
    rw [member_integral hφ (hN0 j) (hN1 j) (hrs j)]
    ring
  simp_rw [h1]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hint.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp

/-! ### (b) Participation -/

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participation condition**): measured in utility
(marginal utility of consumption `1/C` under log utility and full risk sharing), member `(j, s)`
gains from working iff `(1/C)(W/P) − χΘs^φ ≥ 0`, i.e. iff `(W/P)/C ≥ χΘ s^φ`. -/
theorem works_iff {WP C K φ s : ℝ} : 0 ≤ (1 / C) * WP - K * s ^ φ ↔ K * s ^ φ ≤ WP / C := by
  rw [one_div_mul_eq_div]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participants are an interval**): for `φ > 0`,
`K = χΘ > 0`, `R = (W/P)/C ≥ 0` and `s ≥ 0`, `K s^φ ≤ R` iff `s ≤ L` with
`L = (R/K)^{1/φ}`, the marginal participant (`K L^φ = R`). -/
theorem participants_iff {R K φ s : ℝ} (hφ : 0 < φ) (hK : 0 < K) (hR : 0 ≤ R) (hs : 0 ≤ s) :
    (K * s ^ φ ≤ R ↔ s ≤ (R / K) ^ (1 / φ)) ∧ K * ((R / K) ^ (1 / φ)) ^ φ = R := by
  have hRK : 0 ≤ R / K := div_nonneg hR hK.le
  have hinv : 0 < 1 / φ := by positivity
  refine ⟨?_, ?_⟩
  · rw [← le_div_iff₀' hK, ← Real.rpow_le_rpow_iff (Real.rpow_nonneg hs φ) hRK hinv,
      ← Real.rpow_mul hs, mul_one_div_cancel hφ.ne', Real.rpow_one]
  · rw [← Real.rpow_mul hRK, one_div_mul_cancel hφ.ne', Real.rpow_one]
    field_simp

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participation equation, exact in logs**): at the
marginal participant `(W/P)/C = χΘL^φ` with `Θ = Z/C̄` and, in equilibrium, `C = C̄`:
`log(W/P) = ξ + z + φ l` with `ξ = log χ`, `z = log Z`, `l = log L`. -/
theorem participation_log {WP C Cbar χ Z L φ : ℝ} (hC : 0 < C) (hχ : 0 < χ)
    (hZ : 0 < Z) (hL : 0 < L) (hm : WP / C = χ * theta Z Cbar * L ^ φ) (heq : C = Cbar) :
    Real.log WP = Real.log χ + Real.log Z + φ * Real.log L := by
  subst heq
  have hWP' : WP = χ * Z * L ^ φ := by
    unfold theta at hm
    field_simp at hm
    linarith
  rw [hWP', Real.log_mul (by positivity) (by positivity), Real.log_mul hχ.ne' hZ.ne',
    Real.log_rpow hL]

/-- Galí (2015), Exercise 7.3, p. 221 (**the law of motion of `z`, exact in logs**): from
`Z_t = Z_{t−1}^{1−υ} C̄_t^υ`, `z_t = (1 − υ) z_{t−1} + υ c_t`. -/
theorem z_log {Zprev Cbar υ : ℝ} (hZ : 0 < Zprev) (hC : 0 < Cbar) :
    Real.log (Zprev ^ (1 - υ) * Cbar ^ υ) = (1 - υ) * Real.log Zprev + υ * Real.log Cbar := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hZ, Real.log_rpow hC]

/-- Galí (2015), Exercise 7.3, p. 221: the path of `z_t` given `z_{−1} = z₀` and a consumption
path `c`, `z_t = (1 − υ) z_{t−1} + υ c_t`. -/
def zPath (υ z0 : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 - υ) * z0 + υ * c 0
  | t + 1 => (1 - υ) * zPath υ z0 c t + υ * c (t + 1)

/-- Galí (2015), Exercise 7.3(b), p. 222 (**`υ = 1`: the standard wealth effect**): `z = c`. -/
theorem zPath_one (z0 : ℝ) (c : ℕ → ℝ) : zPath 1 z0 c = c := by
  funext t
  cases t <;> simp [zPath]

/-- Galí (2015), Exercise 7.3(b), p. 222 (**`υ = 0`: no wealth effect**): `z_t = z_{−1}`. -/
theorem zPath_zero (z0 : ℝ) (c : ℕ → ℝ) (t : ℕ) : zPath 0 z0 c t = z0 := by
  induction t with
  | zero => simp [zPath]
  | succ t ih => simp [zPath, ih]

/-- Galí (2015), Exercise 7.3(b), p. 222: with `υ = 1` the participation equation
`w − p = ξ + z + φl` is the baseline (6) `w − p = σc + φl + ξ` with `σ = 1` (log utility). -/
theorem participation_upsilon_one {φ z0 : ℝ} {c wr ξ l : ℕ → ℝ} :
    (∀ t, wr t = ξ t + zPath 1 z0 c t + φ * l t) ↔ ∀ t, wr t = 1 * c t + φ * l t + ξ t := by
  rw [zPath_one]
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.3(b), p. 222 (**linearity**): `z` along `c + Δc` is `z` along `c`
plus the response `zPath υ 0 Δc`, which depends neither on `z_{−1}` nor on the baseline `c`. -/
theorem zPath_add (υ z0 : ℝ) (c dc : ℕ → ℝ) (t : ℕ) :
    zPath υ z0 (fun s => c s + dc s) t = zPath υ z0 c t + zPath υ 0 dc t := by
  induction t with
  | zero => simp [zPath]; ring
  | succ t ih => simp only [zPath, ih]; ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**response to a permanent consumption change**): a
permanent change `Δ` in consumption from date `0` on moves `z_t` by `(1 − (1 − υ)^{t+1}) Δ`. -/
theorem zPath_permanent (υ Δ : ℝ) (t : ℕ) :
    zPath υ 0 (fun _ => Δ) t = (1 - (1 - υ) ^ (t + 1)) * Δ := by
  induction t with
  | zero => simp [zPath]
  | succ t ih => simp only [zPath, ih, pow_succ]; ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**impact and lagged responses to a one-period
consumption change** at date `t₀`): `z` is unaffected before `t₀`, moves by `υ` on impact and by
`υ(1 − υ)ᵏ` after `k` periods. -/
theorem zPath_pulse (υ : ℝ) (t0 k : ℕ) :
    (∀ t < t0, zPath υ 0 (fun s => if s = t0 then 1 else 0) t = 0) ∧
      zPath υ 0 (fun s => if s = t0 then 1 else 0) (t0 + k) = υ * (1 - υ) ^ k := by
  have hbefore : ∀ t < t0, zPath υ 0 (fun s => if s = t0 then 1 else 0) t = 0 := by
    intro t ht
    induction t with
    | zero =>
      have : (0 : ℕ) ≠ t0 := by omega
      simp [zPath, this]
    | succ t ih =>
      have : t + 1 ≠ t0 := by omega
      simp [zPath, ih (by omega), this]
  refine ⟨hbefore, ?_⟩
  induction k with
  | zero =>
    cases t0 with
    | zero => simp [zPath]
    | succ t0 =>
      simp only [zPath, ↓reduceIte, pow_zero, mul_one]
      rw [hbefore t0 (by omega)]
      ring
  | succ k ih =>
    have : t0 + k + 1 ≠ t0 := by omega
    rw [← add_assoc]
    simp only [zPath, ih, this, ↓reduceIte, pow_succ]
    ring

/-- Galí (2015), Exercise 7.3(b), p. 222: the labour force implied by the participation equation,
`l_t = (ω_t − ξ_t − z_t)/φ`. -/
noncomputable def labourForce (φ : ℝ) (wr ξ z : ℕ → ℝ) (t : ℕ) : ℝ := (wr t - ξ t - z t) / φ

/-- Galí (2015), Exercise 7.3(b), p. 222: for `φ ≠ 0`, `l = labourForce` is the unique solution
of the participation equation `ω_t = ξ_t + z_t + φ l_t`. -/
theorem labourForce_iff {φ : ℝ} (hφ : φ ≠ 0) {wr ξ z l : ℕ → ℝ} :
    (∀ t, wr t = ξ t + z t + φ * l t) ↔ l = labourForce φ wr ξ z := by
  constructor
  · intro h
    funext t
    rw [labourForce, eq_div_iff hφ, h t]
    ring
  · rintro rfl t
    rw [labourForce]
    field_simp
    ring

/-- **Galí (2015), Exercise 7.3(b), p. 222 (the labour-force response to a permanent consumption
change)**: holding the real wage and `ξ` fixed, a permanent consumption change `Δ` changes the
labour force at date `t` by `−(1 − (1 − υ)^{t+1}) Δ/φ` (for any `z_{−1}` and baseline `c`). -/
theorem labourForce_response (φ υ z0 Δ : ℝ) (wr ξ c : ℕ → ℝ) (t : ℕ) :
    labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t - labourForce φ wr ξ (zPath υ z0 c) t =
      -((1 - (1 - υ) ^ (t + 1)) * Δ / φ) := by
  have h := zPath_add υ z0 c (fun _ => Δ) t
  rw [zPath_permanent] at h
  simp only [labourForce, h]
  ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**dampening**): for every horizon `t`, the share
`1 − (1 − υ)^{t+1}` of the full response is strictly increasing in `υ ∈ [0, 1]`, equals `0` at
`υ = 0` and `1` at `υ = 1`, and lies in `[0, 1]`. -/
theorem dampening_strictMonoOn (t : ℕ) :
    StrictMonoOn (fun υ : ℝ => 1 - (1 - υ) ^ (t + 1)) (Set.Icc 0 1) ∧
      (1 - (1 - (0 : ℝ)) ^ (t + 1) = 0) ∧ (1 - (1 - (1 : ℝ)) ^ (t + 1) = 1) ∧
      ∀ υ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 1 - (1 - υ) ^ (t + 1) ∧ 1 - (1 - υ) ^ (t + 1) ≤ 1 := by
  refine ⟨fun a ha b hb hab => ?_, by simp, by simp, fun υ hυ => ?_⟩
  · simp only
    have h1 : 0 ≤ 1 - b := by linarith [hb.2]
    have h2 : 1 - b < 1 - a := by linarith
    have := pow_lt_pow_left₀ h2 h1 (by omega : t + 1 ≠ 0)
    linarith
  · have h0 : 0 ≤ 1 - υ := by linarith [hυ.2]
    have h1 : 1 - υ ≤ 1 := by linarith [hυ.1]
    have hp0 : 0 ≤ (1 - υ) ^ (t + 1) := pow_nonneg h0 _
    have hp1 : (1 - υ) ^ (t + 1) ≤ 1 := pow_le_one₀ h0 h1
    constructor <;> linarith

/-- **Galí (2015), Exercise 7.3(b), p. 222 (an intermediate `υ` dampens the labour-force
response)**: for `φ > 0` and `Δ ≠ 0`, the absolute labour-force response at every date `t` to a
permanent consumption change `Δ` is strictly increasing in `υ ∈ [0, 1]`; it is `0` for `υ = 0`
and the full log-utility response `|Δ|/φ` for `υ = 1`. -/
theorem labourForce_dampening {φ Δ : ℝ} (hφ : 0 < φ) (hΔ : Δ ≠ 0) (z0 : ℝ) (wr ξ c : ℕ → ℝ)
    (t : ℕ) :
    StrictMonoOn (fun υ => |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath υ z0 c) t|) (Set.Icc 0 1) ∧
      |labourForce φ wr ξ (zPath 0 z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath 0 z0 c) t| = 0 ∧
      |labourForce φ wr ξ (zPath 1 z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath 1 z0 c) t| = |Δ| / φ := by
  have he : ∀ υ, |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
      labourForce φ wr ξ (zPath υ z0 c) t| = (1 - (1 - υ) ^ (t + 1)) * (|Δ| / φ) ∨
      (1 - (1 - υ) ^ (t + 1)) < 0 := by
    intro υ
    rw [labourForce_response]
    by_cases h : 0 ≤ 1 - (1 - υ) ^ (t + 1)
    · left
      rw [abs_neg, mul_div_assoc, abs_mul, abs_of_nonneg h, abs_div, abs_of_pos hφ]
    · right
      linarith
  obtain ⟨hmono, h0, h1, hrange⟩ := dampening_strictMonoOn t
  have hpos : 0 < |Δ| / φ := div_pos (abs_pos.mpr hΔ) hφ
  have key : ∀ υ ∈ Set.Icc (0 : ℝ) 1, |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
      labourForce φ wr ξ (zPath υ z0 c) t| = (1 - (1 - υ) ^ (t + 1)) * (|Δ| / φ) := by
    intro υ hυ
    rcases he υ with h | h
    · exact h
    · exact absurd (hrange υ hυ).1 (not_le.mpr h)
  refine ⟨fun a ha b hb hab => ?_, ?_, ?_⟩
  · simp only
    rw [key a ha, key b hb]
    exact mul_lt_mul_of_pos_right (hmono ha hb hab) hpos
  · rw [key 0 ⟨le_rfl, zero_le_one⟩, h0, zero_mul]
  · rw [key 1 ⟨zero_le_one, le_rfl⟩, h1, one_mul]

/-- Galí (2015), Exercise 7.3(b), p. 222 (**precision note**): the response at lag `k = 1` to a
one-period consumption change, `υ(1 − υ)`, is not monotone in `υ`: it is `1/4` at `υ = 1/2` but
`0` at `υ = 1`. The dampening claim concerns impact responses (`υ`, increasing) and persistent
changes (`labourForce_dampening`). -/
theorem lagged_pulse_not_monotone :
    ¬ MonotoneOn (fun υ : ℝ => zPath υ 0 (fun s => if s = 0 then 1 else 0) (0 + 1))
      (Set.Icc 0 1) := by
  intro h
  have hle := h ⟨by norm_num, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simp only [(zPath_pulse _ 0 1).2] at hle
  norm_num at hle

end Gali.Unemployment.Ex7_3

set_option linter.style.longLine false
#print axioms Gali.Unemployment.SchurStable
#print axioms Gali.Unemployment.disc
#print axioms Gali.Unemployment.root₁
#print axioms Gali.Unemployment.root₂
#print axioms Gali.Unemployment.root_sum
#print axioms Gali.Unemployment.root_prod
#print axioms Gali.Unemployment.root_eq
#print axioms Gali.Unemployment.normSq_root_of_neg
#print axioms Gali.Unemployment.norm_root_of_nonneg
#print axioms Gali.Unemployment.schurStable_iff_roots
#print axioms Gali.Unemployment.chSeq
#print axioms Gali.Unemployment.convSeq
#print axioms Gali.Unemployment.convSeq_rec
#print axioms Gali.Unemployment.chSeq_eq_convSeq
#print axioms Gali.Unemployment.norm_convSeq_le
#print axioms Gali.Unemployment.abs_chSeq_le
#print axioms Gali.Unemployment.tendsto_chSeq
#print axioms Gali.Unemployment.tr2
#print axioms Gali.Unemployment.det2
#print axioms Gali.Unemployment.tr2_eq_trace
#print axioms Gali.Unemployment.det2_eq_det
#print axioms Gali.Unemployment.sq_eq_cayleyHamilton
#print axioms Gali.Unemployment.pow_succ_eq
#print axioms Gali.Unemployment.abs_pow_entry_le
#print axioms Gali.Unemployment.tendsto_pow_entry
#print axioms Gali.Unemployment.BoundedSeq
#print axioms Gali.Unemployment.homogeneous_iterate
#print axioms Gali.Unemployment.abs_mulVec_le
#print axioms Gali.Unemployment.homogeneous_eq_zero
#print axioms Gali.Unemployment.eq_root_of_eq
#print axioms Gali.Unemployment.exists_eigenvector
#print axioms Gali.Unemployment.exists_bounded_homogeneous
#print axioms Gali.Unemployment.ExpectationSystem
#print axioms Gali.Unemployment.ExpectationSystem.mk
#print axioms Gali.Unemployment.ExpectationSystem.E
#print axioms Gali.Unemployment.ExpectationSystem.const
#print axioms Gali.Unemployment.ExpectationSystem.mono
#print axioms Gali.Unemployment.ExpectationSystem.tower
#print axioms Gali.Unemployment.ExpectationSystem.known
#print axioms Gali.Unemployment.perfectForesight
#print axioms Gali.Unemployment.BoundedProc
#print axioms Gali.Unemployment.BoundedVec
#print axioms Gali.Unemployment.ExpectationSystem.Adapted
#print axioms Gali.Unemployment.ExpectationSystem.IsAR1
#print axioms Gali.Unemployment.ExpectationSystem.E_neg
#print axioms Gali.Unemployment.ExpectationSystem.E_smul
#print axioms Gali.Unemployment.ExpectationSystem.E_E_self
#print axioms Gali.Unemployment.ExpectationSystem.abs_E_le
#print axioms Gali.Unemployment.ExpectationSystem.bounded_E
#print axioms Gali.Unemployment.ExpectationSystem.ar1_iterate
#print axioms Gali.Unemployment.ExpectationSystem.forward_iterate
#print axioms Gali.Unemployment.ExpectationSystem.forward_unique
#print axioms Gali.Unemployment.ExpectationSystem.forward_ar1_solves
#print axioms Gali.Unemployment.ExpectationSystem.E_tsum
#print axioms Gali.Unemployment.ExpectationSystem.forwardSeries
#print axioms Gali.Unemployment.ExpectationSystem.forwardSeries_summable
#print axioms Gali.Unemployment.ExpectationSystem.forwardSeries_solves
#print axioms Gali.Unemployment.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.Unemployment.ExpectationSystem.eq_forwardSeries
#print axioms Gali.Unemployment.ExpectationSystem.forwardSeries_adapted
#print axioms Gali.Unemployment.ExpectationSystem.PullOut
#print axioms Gali.Unemployment.ExpectationSystem.Solves
#print axioms Gali.Unemployment.ExpectationSystem.AdaptedVec
#print axioms Gali.Unemployment.ExpectationSystem.system_iterate
#print axioms Gali.Unemployment.ExpectationSystem.system_unique
#print axioms Gali.Unemployment.ExpectationSystem.system_not_unique
#print axioms Gali.Unemployment.ExpectationSystem.Determinate
#print axioms Gali.Unemployment.ExpectationSystem.determinate_iff
#print axioms Gali.Unemployment.perfectForesight_pullOut
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.Unemployment.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinObs
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinTree
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinSystem
#print axioms Gali.Unemployment.ExpectationsFiniteTree.firstHeads
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinShock
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinAR1
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.Unemployment.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.Unemployment.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Gali.Unemployment.Determinacy4.inCount
#print axioms Gali.Unemployment.Determinacy4.circleIntegral_sub_inv
#print axioms Gali.Unemployment.Determinacy4.argument_principle
#print axioms Gali.Unemployment.Determinacy4.quart
#print axioms Gali.Unemployment.Determinacy4.eval_quart
#print axioms Gali.Unemployment.Determinacy4.eval_derivative_quart
#print axioms Gali.Unemployment.Determinacy4.inCount_path
#print axioms Gali.Unemployment.Determinacy4.Par
#print axioms Gali.Unemployment.Determinacy4.Par.mk
#print axioms Gali.Unemployment.Determinacy4.Par.β
#print axioms Gali.Unemployment.Determinacy4.Par.σ
#print axioms Gali.Unemployment.Determinacy4.Par.κp
#print axioms Gali.Unemployment.Determinacy4.Par.κw
#print axioms Gali.Unemployment.Determinacy4.Par.lamP
#print axioms Gali.Unemployment.Determinacy4.Par.lamW
#print axioms Gali.Unemployment.Determinacy4.Par.φp
#print axioms Gali.Unemployment.Determinacy4.Par.φw
#print axioms Gali.Unemployment.Determinacy4.Par.φy
#print axioms Gali.Unemployment.Determinacy4.Par.Ψ
#print axioms Gali.Unemployment.Determinacy4.Par.c0
#print axioms Gali.Unemployment.Determinacy4.Par.c1
#print axioms Gali.Unemployment.Determinacy4.Par.c2
#print axioms Gali.Unemployment.Determinacy4.Par.c3
#print axioms Gali.Unemployment.Determinacy4.Par.c4
#print axioms Gali.Unemployment.Determinacy4.Par.qr
#print axioms Gali.Unemployment.Determinacy4.Par.qr_one
#print axioms Gali.Unemployment.Determinacy4.circle_cert
#print axioms Gali.Unemployment.Determinacy4.Par.qv
#print axioms Gali.Unemployment.Determinacy4.Par.qC
#print axioms Gali.Unemployment.Determinacy4.Par.Qv
#print axioms Gali.Unemployment.Determinacy4.Par.QC
#print axioms Gali.Unemployment.Determinacy4.Par.eval_qC
#print axioms Gali.Unemployment.Determinacy4.Par.eval_QC
#print axioms Gali.Unemployment.Determinacy4.Par.eval_QC_eq
#print axioms Gali.Unemployment.Determinacy4.Par.eval_qC_ofReal
#print axioms Gali.Unemployment.Determinacy4.Par.eval_qC_conj
#print axioms Gali.Unemployment.Determinacy4.Par.eval_qC_mk
#print axioms Gali.Unemployment.Determinacy4.Par.Adm
#print axioms Gali.Unemployment.Determinacy4.Par.qr_neg_one
#print axioms Gali.Unemployment.Determinacy4.Par.Ψ_nonneg
#print axioms Gali.Unemployment.Determinacy4.Par.qr_neg_one_neg
#print axioms Gali.Unemployment.Determinacy4.Par.c0_neg
#print axioms Gali.Unemployment.Determinacy4.Par.c4_neg
#print axioms Gali.Unemployment.Determinacy4.Par.qr_one_neg_of_root
#print axioms Gali.Unemployment.Determinacy4.Par.qC_ne_zero_of_norm_eq_one
#print axioms Gali.Unemployment.Determinacy4.Par.QC_ne_zero_of_norm_eq_one
#print axioms Gali.Unemployment.Determinacy4.coeff_quart_four
#print axioms Gali.Unemployment.Determinacy4.quart_ne_zero
#print axioms Gali.Unemployment.Determinacy4.Par.mix
#print axioms Gali.Unemployment.Determinacy4.Par.mix_zero
#print axioms Gali.Unemployment.Determinacy4.Par.mix_one
#print axioms Gali.Unemployment.Determinacy4.Par.adm_mix
#print axioms Gali.Unemployment.Determinacy4.Par.continuous_Qv_mix
#print axioms Gali.Unemployment.Determinacy4.Par.inCount_QC_mix
#print axioms Gali.Unemployment.Determinacy4.Par.Pref
#print axioms Gali.Unemployment.Determinacy4.Par.QC_ref
#print axioms Gali.Unemployment.Determinacy4.Par.inCount_ref
#print axioms Gali.Unemployment.Determinacy4.Par.adm_ref
#print axioms Gali.Unemployment.Determinacy4.Par.endpt
#print axioms Gali.Unemployment.Determinacy4.Par.inCount_QC
#print axioms Gali.Unemployment.Determinacy4.natDegree_quart
#print axioms Gali.Unemployment.Determinacy4.card_roots_quart
#print axioms Gali.Unemployment.Determinacy4.outCount
#print axioms Gali.Unemployment.Determinacy4.inCount_add_outCount
#print axioms Gali.Unemployment.Determinacy4.Par.QC_ne_zero
#print axioms Gali.Unemployment.Determinacy4.Par.card_roots_QC
#print axioms Gali.Unemployment.Determinacy4.Par.outCount_QC
#print axioms Gali.Unemployment.Determinacy4.Par.dqr
#print axioms Gali.Unemployment.Determinacy4.Par.eval_derivative_QC
#print axioms Gali.Unemployment.Determinacy4.Par.continuous_qr
#print axioms Gali.Unemployment.Determinacy4.Par.qr_zero
#print axioms Gali.Unemployment.Determinacy4.Par.qC_eval_zero
#print axioms Gali.Unemployment.Determinacy4.Par.inv_mem_out
#print axioms Gali.Unemployment.Determinacy4.Par.stable_root
#print axioms Gali.Unemployment.Determinacy4.pow_entry_bound
#print axioms Gali.Unemployment.Determinacy4.rvMul
#print axioms Gali.Unemployment.Determinacy4.rvMul_rvMul
#print axioms Gali.Unemployment.Determinacy4.rvMul_add
#print axioms Gali.Unemployment.Determinacy4.rvMul_sub
#print axioms Gali.Unemployment.Determinacy4.rvMul_one
#print axioms Gali.Unemployment.Determinacy4.rvMul_zero
#print axioms Gali.Unemployment.Determinacy4.rvMul_apply
#print axioms Gali.Unemployment.Determinacy4.Fwd.E_rvMul
#print axioms Gali.Unemployment.Determinacy4.Fwd.FSolves
#print axioms Gali.Unemployment.Determinacy4.Fwd.VAdapted
#print axioms Gali.Unemployment.Determinacy4.Fwd.VBounded
#print axioms Gali.Unemployment.Determinacy4.Fwd.fsolves_iterate
#print axioms Gali.Unemployment.Determinacy4.Fwd.abs_rvMul_pow_le
#print axioms Gali.Unemployment.Determinacy4.Fwd.fsolves_unique
#print axioms Gali.Unemployment.Determinacy4.Fwd.fsolves_exists
#print axioms Gali.Unemployment.Determinacy4.Par.A0
#print axioms Gali.Unemployment.Determinacy4.Par.A1
#print axioms Gali.Unemployment.Determinacy4.Par.det_A0_sub_A1
#print axioms Gali.Unemployment.Determinacy4.Par.det_A0_sub_A1_real
#print axioms Gali.Unemployment.Determinacy4.B0
#print axioms Gali.Unemployment.Determinacy4.Par.Dr
#print axioms Gali.Unemployment.Determinacy4.Par.Brr
#print axioms Gali.Unemployment.Determinacy4.Par.Hr
#print axioms Gali.Unemployment.Determinacy4.Par.qr_factor
#print axioms Gali.Unemployment.Determinacy4.Par.dqr_factor
#print axioms Gali.Unemployment.Determinacy4.Par.StableVec
#print axioms Gali.Unemployment.Determinacy4.Par.stableVec_of_hom
#print axioms Gali.Unemployment.Determinacy4.Par.exists_stableVec
#print axioms Gali.Unemployment.Determinacy4.Par.Cm
#print axioms Gali.Unemployment.Determinacy4.Par.Dm
#print axioms Gali.Unemployment.Determinacy4.Par.Vm
#print axioms Gali.Unemployment.Determinacy4.Par.det_Cm_sub_mul
#print axioms Gali.Unemployment.Determinacy4.Par.rr
#print axioms Gali.Unemployment.Determinacy4.Par.qC_eq_mul_rr
#print axioms Gali.Unemployment.Determinacy4.Par.rr_self
#print axioms Gali.Unemployment.Determinacy4.Par.continuous_rr
#print axioms Gali.Unemployment.Determinacy4.Par.det_Cm_sub
#print axioms Gali.Unemployment.Determinacy4.Par.rr_ne_zero
#print axioms Gali.Unemployment.Determinacy4.Par.Km
#print axioms Gali.Unemployment.Determinacy4.Par.Fm
#print axioms Gali.Unemployment.Determinacy4.Par.det_Cm_ne_zero
#print axioms Gali.Unemployment.Determinacy4.Par.Km_eigen
#print axioms Gali.Unemployment.Determinacy4.Dyn.IsSol
#print axioms Gali.Unemployment.Determinacy4.Dyn.Determinate
#print axioms Gali.Unemployment.Determinacy4.Dyn.toS
#print axioms Gali.Unemployment.Determinacy4.Dyn.transform
#print axioms Gali.Unemployment.Determinacy4.Dyn.eq_iff_fwd
#print axioms Gali.Unemployment.Determinacy4.Dyn.toS_adapted
#print axioms Gali.Unemployment.Determinacy4.Dyn.toS_bounded
#print axioms Gali.Unemployment.Determinacy4.Dyn.mseq
#print axioms Gali.Unemployment.Determinacy4.Dyn.ofS
#print axioms Gali.Unemployment.Determinacy4.Dyn.toS_ofS
#print axioms Gali.Unemployment.Determinacy4.Dyn.mseq_adapted
#print axioms Gali.Unemployment.Determinacy4.Dyn.mseq_bounded
#print axioms Gali.Unemployment.Determinacy4.Dyn.determinate_of_pos
#print axioms Gali.Unemployment.Determinacy4.Par.det_A0
#print axioms Gali.Unemployment.Determinacy4.Par.det_A1
#print axioms Gali.Unemployment.Determinacy4.Par.eval_derivative_qC
#print axioms Gali.Unemployment.Determinacy4.Dyn.sum_smul_rvMul
#print axioms Gali.Unemployment.Determinacy4.Dyn.rvMul_const
#print axioms Gali.Unemployment.Determinacy4.Dyn.multiple_solutions_of_mode
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_mode
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_eq
#print axioms Gali.Unemployment.Determinacy4.Dyn.map_ofReal_eq
#print axioms Gali.Unemployment.Determinacy4.Dyn.no_bounded_solution_of_no_root
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_no_root
#print axioms Gali.Unemployment.Determinacy4.Dyn.closedRoots
#print axioms Gali.Unemployment.Determinacy4.Dyn.qC_ne_zero
#print axioms Gali.Unemployment.Determinacy4.Dyn.mem_closedRoots
#print axioms Gali.Unemployment.Determinacy4.Dyn.sr
#print axioms Gali.Unemployment.Determinacy4.Dyn.qr_eq_sr
#print axioms Gali.Unemployment.Determinacy4.Dyn.sr_self
#print axioms Gali.Unemployment.Determinacy4.Dyn.closedRoots_card_ne_one
#print axioms Gali.Unemployment.Determinacy4.Dyn.exists_real_eigvec
#print axioms Gali.Unemployment.Determinacy4.Dyn.geom_mode
#print axioms Gali.Unemployment.Determinacy4.Dyn.abs_pow_le_one
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_complex_root
#print axioms Gali.Unemployment.Determinacy4.Dyn.exists_mode_of_two_real_roots
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_two_real_roots
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_double_root
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_neg
#print axioms Gali.Unemployment.Determinacy4.Dyn.not_determinate_of_le
#print axioms Gali.Unemployment.Determinacy4.Dyn.determinate_iff
#print axioms Gali.Unemployment.Determinacy4.Par.Aw
#print axioms Gali.Unemployment.Determinacy4.Par.det_A0_mul_det_charmat
#print axioms Gali.Unemployment.Determinacy4.Par.charpoly_Aw
#print axioms Gali.Unemployment.Determinacy4.Par.eigen_count_iff
#print axioms Gali.Unemployment.Determinacy4.Dyn.eq24_iff
#print axioms Gali.Unemployment.Determinacy4.Par.Lhs
#print axioms Gali.Unemployment.Determinacy4.Par.qr_one_eq_mul
#print axioms Gali.Unemployment.Determinacy4.Par.qr_one_pos_iff
#print axioms Gali.Unemployment.Determinacy4.bookPar
#print axioms Gali.Unemployment.Determinacy4.bookPar_adm
#print axioms Gali.Unemployment.Determinacy4.bookPar_Ψ
#print axioms Gali.Unemployment.Determinacy4.bookPar_Lhs
#print axioms Gali.Unemployment.Determinacy4.determinacy_iff
#print axioms Gali.Unemployment.Determinacy4.eigenvalues_iff
#print axioms Gali.Unemployment.Determinacy4.determinacy_iff_phiY_zero
#print axioms Gali.Unemployment.Determinacy4.Par.inCount_QC_four
#print axioms Gali.Unemployment.Determinacy4.Par.no_root_of_inCount_four
#print axioms Gali.Unemployment.Determinacy4.exNE
#print axioms Gali.Unemployment.Determinacy4.exNE_coeffs
#print axioms Gali.Unemployment.Determinacy4.exNE_adm
#print axioms Gali.Unemployment.Determinacy4.exNE_lhs
#print axioms Gali.Unemployment.Determinacy4.exNE_circle
#print axioms Gali.Unemployment.Determinacy4.exNE_no_root
#print axioms Gali.Unemployment.Determinacy4.exNE_no_bounded_solution
#print axioms Gali.Unemployment.Determinacy4.baseline_lambdas
#print axioms Gali.Unemployment.Determinacy4.exBase
#print axioms Gali.Unemployment.Determinacy4.exBase_signs
#print axioms Gali.Unemployment.Determinacy4.exBase_two_roots
#print axioms Gali.Unemployment.Determinacy4.exBase_multiplicity
#print axioms Gali.Unemployment.IndivisibleLabor.integral_disutility
#print axioms Gali.Unemployment.IndivisibleLabor.crra
#print axioms Gali.Unemployment.IndivisibleLabor.householdUtility
#print axioms Gali.Unemployment.IndivisibleLabor.ch6Utility
#print axioms Gali.Unemployment.IndivisibleLabor.householdUtility_eq_ch6
#print axioms Gali.Unemployment.IndivisibleLabor.hasDerivAt_disutility
#print axioms Gali.Unemployment.IndivisibleLabor.hasDerivAt_crra
#print axioms Gali.Unemployment.IndivisibleLabor.marginal_value
#print axioms Gali.Unemployment.IndivisibleLabor.participates_iff
#print axioms Gali.Unemployment.IndivisibleLabor.laborForce
#print axioms Gali.Unemployment.IndivisibleLabor.laborForce_nonneg
#print axioms Gali.Unemployment.IndivisibleLabor.laborForce_rpow
#print axioms Gali.Unemployment.IndivisibleLabor.eq5_iff
#print axioms Gali.Unemployment.IndivisibleLabor.participation_set_eq
#print axioms Gali.Unemployment.IndivisibleLabor.participation_set_unit
#print axioms Gali.Unemployment.IndivisibleLabor.marginal_indifferent
#print axioms Gali.Unemployment.IndivisibleLabor.inframarginal_strict
#print axioms Gali.Unemployment.IndivisibleLabor.supramarginal_refuses
#print axioms Gali.Unemployment.IndivisibleLabor.laborForce_le_one_iff
#print axioms Gali.Unemployment.UnemploymentDef.eq6_type
#print axioms Gali.Unemployment.UnemploymentDef.eq6_integrated
#print axioms Gali.Unemployment.UnemploymentDef.cesIndex
#print axioms Gali.Unemployment.UnemploymentDef.laborForceAgg
#print axioms Gali.Unemployment.UnemploymentDef.integrable_exp_mul
#print axioms Gali.Unemployment.UnemploymentDef.integrable_of_bound
#print axioms Gali.Unemployment.UnemploymentDef.hasDerivAt_cgf_mul
#print axioms Gali.Unemployment.UnemploymentDef.log_cesIndex_family
#print axioms Gali.Unemployment.UnemploymentDef.log_laborForce_family
#print axioms Gali.Unemployment.UnemploymentDef.wageIndex_first_order
#print axioms Gali.Unemployment.UnemploymentDef.laborForce_first_order
#print axioms Gali.Unemployment.UnemploymentDef.eq6_residual_eq
#print axioms Gali.Unemployment.UnemploymentDef.eq6_first_order
#print axioms Gali.Unemployment.UnemploymentDef.unemploymentRate_eq
#print axioms Gali.Unemployment.UnemploymentDef.rate_le_u
#print axioms Gali.Unemployment.UnemploymentDef.exp_neg_le_quadratic
#print axioms Gali.Unemployment.UnemploymentDef.abs_rate_sub_u_le
#print axioms Gali.Unemployment.UnemploymentDef.abs_rate_sub_u_bound_fails_neg
#print axioms Gali.Unemployment.UnemploymentDef.wageMarkup
#print axioms Gali.Unemployment.UnemploymentDef.eq8_iff
#print axioms Gali.Unemployment.UnemploymentDef.natRate
#print axioms Gali.Unemployment.UnemploymentDef.natRate_eq
#print axioms Gali.Unemployment.UnemploymentDef.natRate_pos
#print axioms Gali.Unemployment.UnemploymentDef.markupGap_eq
#print axioms Gali.Unemployment.UnemploymentDef.WageNKPC
#print axioms Gali.Unemployment.UnemploymentDef.WagePhillips
#print axioms Gali.Unemployment.UnemploymentDef.wageNKPC_iff_eq11
#print axioms Gali.Unemployment.UnemploymentDef.ResetRule
#print axioms Gali.Unemployment.UnemploymentDef.IndexLaw
#print axioms Gali.Unemployment.UnemploymentDef.flexible_iff
#print axioms Gali.Unemployment.UnemploymentDef.flexible_unemployment_constant
#print axioms Gali.Unemployment.UnemploymentDef.fluctuations_require_rigidity
#print axioms Gali.Unemployment.UnemploymentDef.sticky_unemployment_gap_consistent
#print axioms Gali.Unemployment.Equilibrium.eq16_levels
#print axioms Gali.Unemployment.Equilibrium.DISGap
#print axioms Gali.Unemployment.Equilibrium.PriceGapNKPC
#print axioms Gali.Unemployment.Equilibrium.WageGapNKPC
#print axioms Gali.Unemployment.Equilibrium.WageUnempNKPC
#print axioms Gali.Unemployment.Equilibrium.WageGapLaw
#print axioms Gali.Unemployment.Equilibrium.UnempGapEq
#print axioms Gali.Unemployment.Equilibrium.eq14_iff_eq20
#print axioms Gali.Unemployment.Equilibrium.Ch6Equilibrium
#print axioms Gali.Unemployment.Equilibrium.Ch7Equilibrium
#print axioms Gali.Unemployment.Equilibrium.ch7_iff_ch6
#print axioms Gali.Unemployment.Equilibrium.IsSol7
#print axioms Gali.Unemployment.Equilibrium.uhatOf
#print axioms Gali.Unemployment.Equilibrium.isSol7_iff
#print axioms Gali.Unemployment.Equilibrium.uhatOf_bounded
#print axioms Gali.Unemployment.Equilibrium.Determinate7
#print axioms Gali.Unemployment.Equilibrium.determinate_iff_ch6
#print axioms Gali.Unemployment.Equilibrium.determinacy_ch7_iff
#print axioms Gali.Unemployment.Equilibrium.determinacy_ch7_iff_phiY_zero
#print axioms Gali.Unemployment.Equilibrium.rule17_determinate
#print axioms Gali.Unemployment.Policy.Coef
#print axioms Gali.Unemployment.Policy.Coef.mk
#print axioms Gali.Unemployment.Policy.Coef.β
#print axioms Gali.Unemployment.Policy.Coef.kapP
#print axioms Gali.Unemployment.Policy.Coef.kapW
#print axioms Gali.Unemployment.Policy.Coef.lamP
#print axioms Gali.Unemployment.Policy.Coef.lamW
#print axioms Gali.Unemployment.Policy.Coef.ay
#print axioms Gali.Unemployment.Policy.Coef.ap
#print axioms Gali.Unemployment.Policy.Coef.aw
#print axioms Gali.Unemployment.Policy.bookCoef
#print axioms Gali.Unemployment.Policy.prev
#print axioms Gali.Unemployment.Policy.prev_zero
#print axioms Gali.Unemployment.Policy.prev_succ
#print axioms Gali.Unemployment.Policy.lagrangian_alg
#print axioms Gali.Unemployment.Policy.hasSum_of_telescope
#print axioms Gali.Unemployment.Policy.tendsto_disc_abs
#print axioms Gali.Unemployment.Policy.tendsto_disc_partial
#print axioms Gali.Unemployment.Policy.summable_sub_sq
#print axioms Gali.Unemployment.Policy.Det.Feasible
#print axioms Gali.Unemployment.Policy.Det.FOC
#print axioms Gali.Unemployment.Policy.Det.BoundedMult
#print axioms Gali.Unemployment.Policy.Det.lossTerm
#print axioms Gali.Unemployment.Policy.Det.FiniteLoss
#print axioms Gali.Unemployment.Policy.Det.loss
#print axioms Gali.Unemployment.Policy.Det.IsOptimal
#print axioms Gali.Unemployment.Policy.Det.summable_sq
#print axioms Gali.Unemployment.Policy.Det.prev_sub_eq_sum
#print axioms Gali.Unemployment.Policy.Det.loss_sub_hasSum
#print axioms Gali.Unemployment.Policy.Det.isOptimal_of_foc
#print axioms Gali.Unemployment.Policy.Det.eq_of_loss_eq
#print axioms Gali.Unemployment.Policy.Det.isOptimal_iff_foc
#print axioms Gali.Unemployment.Policy.Det.existsUnique_optimal
#print axioms Gali.Unemployment.Policy.Det.demand_zero_optimal
#print axioms Gali.Unemployment.Policy.markup_eq_exp
#print axioms Gali.Unemployment.Policy.epsW_markup_iff
#print axioms Gali.Unemployment.Policy.exp_quarter_bounds
#print axioms Gali.Unemployment.Policy.calibration_epsW
#print axioms Gali.Unemployment.Policy.calibration_markup
#print axioms Gali.Unemployment.Policy.calibration_book_epsW
#print axioms Gali.Unemployment.Policy.laborForce
#print axioms Gali.Unemployment.Policy.laborForce_iff
#print axioms Gali.Unemployment.Policy.hasDerivAt_laborForce
#print axioms Gali.Unemployment.Policy.laborForce_strictAnti
#print axioms Gali.Unemployment.Policy.marginalParticipant
#print axioms Gali.Unemployment.Policy.marginalParticipant_eq5
#print axioms Gali.Unemployment.Policy.log_marginalParticipant
#print axioms Gali.Unemployment.Policy.hasDerivAt_log_marginalParticipant
#print axioms Gali.Unemployment.Policy.WagePC
#print axioms Gali.Unemployment.Policy.abs_unemp_le
#print axioms Gali.Unemployment.Policy.lamWOf
#print axioms Gali.Unemployment.Policy.tendsto_lamWOf_atTop
#print axioms Gali.Unemployment.Policy.unemployment_vanishes
#print axioms Gali.Unemployment.Policy.unemployment_volatility_vanishes
#print axioms Gali.Unemployment.Policy.unemployment_need_not_vanish
#print axioms Gali.Unemployment.Policy.flexible_wages_no_unemployment_gap
#print axioms Gali.Unemployment.Policy.Feasible7
#print axioms Gali.Unemployment.Policy.fn8_wage_pc
#print axioms Gali.Unemployment.Policy.feasible7_iff
#print axioms Gali.Unemployment.Policy.IsOptimal7
#print axioms Gali.Unemployment.Policy.isOptimal7_iff
#print axioms Gali.Unemployment.Policy.FOC7
#print axioms Gali.Unemployment.Policy.foc7_iff_ch6
#print axioms Gali.Unemployment.Policy.bookCoef_weights_pos
#print axioms Gali.Unemployment.Policy.isOptimal7_iff_eq
#print axioms Gali.Unemployment.Policy.existsUnique_optimal7
#print axioms Gali.Unemployment.Policy.isOptimal7_iff_foc
#print axioms Gali.Unemployment.Policy.psiYA
#print axioms Gali.Unemployment.Policy.psiWA
#print axioms Gali.Unemployment.Policy.psiYA_sigma_one
#print axioms Gali.Unemployment.Policy.psiWA_sigma_one
#print axioms Gali.Unemployment.Policy.outputDev
#print axioms Gali.Unemployment.Policy.employmentDev
#print axioms Gali.Unemployment.Policy.unempGap
#print axioms Gali.Unemployment.Policy.laborForceDev
#print axioms Gali.Unemployment.Policy.realWageDev
#print axioms Gali.Unemployment.Policy.participation_consistent
#print axioms Gali.Unemployment.Policy.efficient_technology_sigma_one
#print axioms Gali.Unemployment.Policy.efficient_employment_zero_iff
#print axioms Gali.Unemployment.Policy.demand_shock_optimal_iff
#print axioms Gali.Unemployment.Policy.demand_shock_labour_market
#print axioms Gali.Unemployment.Policy.Rule22Level
#print axioms Gali.Unemployment.Policy.rule22_level_iff_gap
#print axioms Gali.Unemployment.Policy.rule22_book_intercept
#print axioms Gali.Unemployment.Policy.rule22_level_not_steady
#print axioms Gali.Unemployment.Policy.rule22_gap_steady
#print axioms Gali.Unemployment.Policy.rule22_deviation
#print axioms Gali.Unemployment.Ex7_1.profit
#print axioms Gali.Unemployment.Ex7_1.bernoulli_key
#print axioms Gali.Unemployment.Ex7_1.profit_lt_opt
#print axioms Gali.Unemployment.Ex7_1.profit_isMaxOn_iff
#print axioms Gali.Unemployment.Ex7_1.subsidy_offsets
#print axioms Gali.Unemployment.Ex7_1.flexPrice_eq_wage
#print axioms Gali.Unemployment.Ex7_1.inflOf
#print axioms Gali.Unemployment.Ex7_1.infl_eq_of_realWage_const
#print axioms Gali.Unemployment.Ex7_1.markup_eq_phi_u
#print axioms Gali.Unemployment.Ex7_1.ex7_1a
#print axioms Gali.Unemployment.Ex7_1.ex7_1a_from_primitives
#print axioms Gali.Unemployment.Ex7_1.lambdaP
#print axioms Gali.Unemployment.Ex7_1.ch6PeriodLoss
#print axioms Gali.Unemployment.Ex7_1.flexLoss
#print axioms Gali.Unemployment.Ex7_1.ch6PeriodLoss_alpha_zero
#print axioms Gali.Unemployment.Ex7_1.priceWeight_tendsto_zero
#print axioms Gali.Unemployment.Ex7_1.ch6PeriodLoss_tendsto_flex
#print axioms Gali.Unemployment.Ex7_1.efficient_output_iff
#print axioms Gali.Unemployment.Ex7_1.phi_u_eq_gap
#print axioms Gali.Unemployment.Ex7_1.alphaU
#print axioms Gali.Unemployment.Ex7_1.alphaU_pos
#print axioms Gali.Unemployment.Ex7_1.flexLoss_eq
#print axioms Gali.Unemployment.Ex7_1.welfare_tsum_eq
#print axioms Gali.Unemployment.Ex7_1.welfare_hasSum_iff
#print axioms Gali.Unemployment.Ex7_1.expected_welfare_eq
#print axioms Gali.Unemployment.Ex7_1.printed_sum_not_summable
#print axioms Gali.Unemployment.Ex7_1.correct_sum_hasSum
#print axioms Gali.Unemployment.Ex7_1.distortion_eq
#print axioms Gali.Unemployment.Ex7_1.distortion_calibration
#print axioms Gali.Unemployment.Ex7_1.periodObj
#print axioms Gali.Unemployment.Ex7_1.periodObj_sub
#print axioms Gali.Unemployment.Ex7_1.periodObj_isMinOn_iff
#print axioms Gali.Unemployment.Ex7_1.period_problem_iff
#print axioms Gali.Unemployment.Ex7_1.NKPCu
#print axioms Gali.Unemployment.Ex7_1.DiscretionEq
#print axioms Gali.Unemployment.Ex7_1.TargetingRule
#print axioms Gali.Unemployment.Ex7_1.discretionEq_iff
#print axioms Gali.Unemployment.Ex7_1.aDisc
#print axioms Gali.Unemployment.Ex7_1.aDisc_mem
#print axioms Gali.Unemployment.Ex7_1.inflation_forward_iff
#print axioms Gali.Unemployment.Ex7_1.piStar
#print axioms Gali.Unemployment.Ex7_1.uStar
#print axioms Gali.Unemployment.Ex7_1.den_pos
#print axioms Gali.Unemployment.Ex7_1.uStar_eq
#print axioms Gali.Unemployment.Ex7_1.piStar_nkpc
#print axioms Gali.Unemployment.Ex7_1.discretion_const_isEq
#print axioms Gali.Unemployment.Ex7_1.discretionEq_iff_const
#print axioms Gali.Unemployment.Ex7_1.inflationBias_pos
#print axioms Gali.Unemployment.Ex7_1.expected_inflation_eq
#print axioms Gali.Unemployment.Ex7_1.uStar_lt_un
#print axioms Gali.Unemployment.Ex7_1.piStar_primitives
#print axioms Gali.Unemployment.Ex7_1.uStar_primitives
#print axioms Gali.Unemployment.Ex7_1.inflationBias_zero_iff
#print axioms Gali.Unemployment.Ex7_1.wageSubsidy_markup_zero
#print axioms Gali.Unemployment.Ex7_1.inflationBias_strictMonoOn
#print axioms Gali.Unemployment.Ex7_1.tendsto_inflationBias_zero
#print axioms Gali.Unemployment.Ex7_1.DIS
#print axioms Gali.Unemployment.Ex7_1.rateOf
#print axioms Gali.Unemployment.Ex7_1.dis_gap_iff
#print axioms Gali.Unemployment.Ex7_1.NKPCx
#print axioms Gali.Unemployment.Ex7_1.stack
#print axioms Gali.Unemployment.Ex7_1.boundedVec_stack
#print axioms Gali.Unemployment.Ex7_1.adaptedVec_stack
#print axioms Gali.Unemployment.Ex7_1.AT
#print axioms Gali.Unemployment.Ex7_1.wT
#print axioms Gali.Unemployment.Ex7_1.rule_iff_solves
#print axioms Gali.Unemployment.Ex7_1.tr2_AT
#print axioms Gali.Unemployment.Ex7_1.det2_AT
#print axioms Gali.Unemployment.Ex7_1.AT_schurStable_iff
#print axioms Gali.Unemployment.Ex7_1.RuleD
#print axioms Gali.Unemployment.Ex7_1.dev_iff_solves
#print axioms Gali.Unemployment.Ex7_1.rule_implements
#print axioms Gali.Unemployment.Ex7_1.rule_indeterminate
#print axioms Gali.Unemployment.Ex7_1.Commit.gam
#print axioms Gali.Unemployment.Ex7_1.Commit.del
#print axioms Gali.Unemployment.Ex7_1.Commit.gam_pos
#print axioms Gali.Unemployment.Ex7_1.Commit.gam_mul_denom
#print axioms Gali.Unemployment.Ex7_1.Commit.gam_mul_le
#print axioms Gali.Unemployment.Ex7_1.Commit.gam_mul_lt_iff
#print axioms Gali.Unemployment.Ex7_1.Commit.four_beta_gam_sq_lt_one
#print axioms Gali.Unemployment.Ex7_1.Commit.sqrt_sq_eq
#print axioms Gali.Unemployment.Ex7_1.Commit.sqrt_lt_one
#print axioms Gali.Unemployment.Ex7_1.Commit.del_mul
#print axioms Gali.Unemployment.Ex7_1.Commit.del_pos
#print axioms Gali.Unemployment.Ex7_1.Commit.del_quad
#print axioms Gali.Unemployment.Ex7_1.Commit.del_lt_one_iff
#print axioms Gali.Unemployment.Ex7_1.Commit.kappa_sq_del
#print axioms Gali.Unemployment.Ex7_1.Commit.lag
#print axioms Gali.Unemployment.Ex7_1.Commit.lag_zero
#print axioms Gali.Unemployment.Ex7_1.Commit.lag_succ
#print axioms Gali.Unemployment.Ex7_1.Commit.priceGap
#print axioms Gali.Unemployment.Ex7_1.Commit.hasSum_of_telescope
#print axioms Gali.Unemployment.Ex7_1.Commit.Feasible
#print axioms Gali.Unemployment.Ex7_1.Commit.lossTerm
#print axioms Gali.Unemployment.Ex7_1.Commit.FiniteLoss
#print axioms Gali.Unemployment.Ex7_1.Commit.loss
#print axioms Gali.Unemployment.Ex7_1.Commit.IsOptimal
#print axioms Gali.Unemployment.Ex7_1.Commit.FOC
#print axioms Gali.Unemployment.Ex7_1.Commit.foc_iff_targeting
#print axioms Gali.Unemployment.Ex7_1.Commit.tendsto_disc_sq
#print axioms Gali.Unemployment.Ex7_1.Commit.loss_sub_hasSum
#print axioms Gali.Unemployment.Ex7_1.Commit.isOptimal_of_foc
#print axioms Gali.Unemployment.Ex7_1.Commit.eq_of_loss_eq
#print axioms Gali.Unemployment.Ex7_1.Commit.finiteLoss_of_bounded
#print axioms Gali.Unemployment.Ex7_1.Commit.pbar
#print axioms Gali.Unemployment.Ex7_1.Commit.commInfl
#print axioms Gali.Unemployment.Ex7_1.Commit.commU
#print axioms Gali.Unemployment.Ex7_1.Commit.priceGap_commInfl
#print axioms Gali.Unemployment.Ex7_1.Commit.comm_feasible
#print axioms Gali.Unemployment.Ex7_1.Commit.comm_foc
#print axioms Gali.Unemployment.Ex7_1.Commit.del_mem
#print axioms Gali.Unemployment.Ex7_1.Commit.comm_finiteLoss
#print axioms Gali.Unemployment.Ex7_1.Commit.isOptimal_iff
#print axioms Gali.Unemployment.Ex7_1.Commit.isOptimal_iff_targeting
#print axioms Gali.Unemployment.Ex7_1.Commit.commitment_tendsto
#print axioms Gali.Unemployment.Ex7_1.Commit.commitment_monotone
#print axioms Gali.Unemployment.Ex7_1.Commit.commInfl_lt_piStar
#print axioms Gali.Unemployment.Ex7_1.Commit.disc_feasible
#print axioms Gali.Unemployment.Ex7_1.Commit.commitment_beats_discretion
#print axioms Gali.Unemployment.Ex7_2.markupGap
#print axioms Gali.Unemployment.Ex7_2.eq13
#print axioms Gali.Unemployment.Ex7_2.lambdaW
#print axioms Gali.Unemployment.Ex7_2.wageInfl
#print axioms Gali.Unemployment.Ex7_2.eq15_iff
#print axioms Gali.Unemployment.Ex7_2.lambdaW_pos
#print axioms Gali.Unemployment.Ex7_2.markupGapTV
#print axioms Gali.Unemployment.Ex7_2.eq13_timeVarying
#print axioms Gali.Unemployment.Ex7_2.ErrorForm
#print axioms Gali.Unemployment.Ex7_2.wageEq_iff_errorForm
#print axioms Gali.Unemployment.Ex7_2.ex7_2a
#print axioms Gali.Unemployment.Ex7_2.errorForm_hat
#print axioms Gali.Unemployment.Ex7_2.errorForm_depends_on_sum
#print axioms Gali.Unemployment.Ex7_2.errorForm_shift_iff
#print axioms Gali.Unemployment.Ex7_2.not_identified
#print axioms Gali.Unemployment.Ex7_2.participation_log
#print axioms Gali.Unemployment.Ex7_2.UnempForm
#print axioms Gali.Unemployment.Ex7_2.ex7_2b
#print axioms Gali.Unemployment.Ex7_2.identified
#print axioms Gali.Unemployment.Ex7_3.memberU
#print axioms Gali.Unemployment.Ex7_3.disutility_intervalIntegrable
#print axioms Gali.Unemployment.Ex7_3.integral_disutility
#print axioms Gali.Unemployment.Ex7_3.member_integral
#print axioms Gali.Unemployment.Ex7_3.theta
#print axioms Gali.Unemployment.Ex7_3.household_utility
#print axioms Gali.Unemployment.Ex7_3.works_iff
#print axioms Gali.Unemployment.Ex7_3.participants_iff
#print axioms Gali.Unemployment.Ex7_3.participation_log
#print axioms Gali.Unemployment.Ex7_3.z_log
#print axioms Gali.Unemployment.Ex7_3.zPath
#print axioms Gali.Unemployment.Ex7_3.zPath_one
#print axioms Gali.Unemployment.Ex7_3.zPath_zero
#print axioms Gali.Unemployment.Ex7_3.participation_upsilon_one
#print axioms Gali.Unemployment.Ex7_3.zPath_add
#print axioms Gali.Unemployment.Ex7_3.zPath_permanent
#print axioms Gali.Unemployment.Ex7_3.zPath_pulse
#print axioms Gali.Unemployment.Ex7_3.labourForce
#print axioms Gali.Unemployment.Ex7_3.labourForce_iff
#print axioms Gali.Unemployment.Ex7_3.labourForce_response
#print axioms Gali.Unemployment.Ex7_3.dampening_strictMonoOn
#print axioms Gali.Unemployment.Ex7_3.labourForce_dampening
#print axioms Gali.Unemployment.Ex7_3.lagged_pulse_not_monotone
