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
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.GeomSum
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

Restated from the `Gali/Unemployment` project (each project in this
repository is self-contained).
-/

namespace Gali.OpenEconomy

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

end Gali.OpenEconomy

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

Restated from the `Gali/Unemployment` project (each project in this
repository is self-contained).
-/

namespace Gali.OpenEconomy

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

end Gali.OpenEconomy

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

Restated from the `Gali/Unemployment` project (each project in this
repository is self-contained).
-/

namespace Gali.OpenEconomy.ExpectationsFiniteTree

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

end Gali.OpenEconomy.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Preferences of the small open economy: home-bias CES over home and foreign goods

Galí (2015), Chapter 8, §8.1.1, pp. 225–228: eqs. (2), (4), (5), the expenditure identity
`P_H C_H + P_F C_F = P C` (p. 227) and footnotes 1 and 2.

The consumption index (2) is `C = ((1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η})^{η/(η−1)}`
with openness `0 < υ < 1` and elasticity `η > 0`, `η ≠ 1`; the CPI is
`P = ((1−υ) P_H^{1−η} + υ P_F^{1−η})^{1/(1−η)}`.

## Main results

* `rpow_tangent_le`, `rpow_tangent_eq_iff`: the tangent-line inequality
  `(u^r − 1)/r ≤ u − 1` for `r < 1`, `r ≠ 0` (weighted AM–GM), strict unless `u = 1`.
  This one inequality covers both `η > 1` (`0 < r < 1`) and `η < 1` (`r < 0`).
* `expenditure_ge`, `expenditure_eq_iff`: eq. (5) as expenditure minimisation — every bundle
  costs at least `P · C` (its own index `C`), with equality **iff** it is on the demand
  schedules (5). For `η > 1` zero quantities are allowed (`expenditure_ge_of_one_lt`,
  `expenditure_eq_iff_of_one_lt`).
* `cesIndex_demand`, `expenditure_demand`: the demands (5) deliver `C` and cost exactly
  `P C` (p. 227).
* `cpi_isLeast`: the CPI is the least cost of one unit of the index; `cesIndex_le_of_spend`.
* `importShare`: the import share is `υ (P_F/P)^{1−η}`, equal to `υ` when `η = 1` or
  `P_H = P_F` (p. 226).
* `cesIndex_tendsto_cd` (fn. 1): as `η → 1` the index tends to
  `C_H^{1−υ} C_F^υ / ((1−υ)^{1−υ} υ^υ)`; `cpi_tendsto_cd` (fn. 2): the CPI tends to
  `P_H^{1−υ} P_F^υ`.
* `expenditureCD_ge`, `expenditureCD_eq_iff`, `cesIndexCD_demand`, `expenditureCD_demand`
  (fn. 2): at `η = 1`, with the fn-1 normalisation, `P_H^{1−υ}P_F^υ` is exactly the unit cost
  and the demands are (5) with `η = 1`.
* `Variety` (eq. (4), p. 226): Dixit–Stiglitz demand over domestic varieties on `[0, 1]`,
  restated from the Chapter 3 project, and `two_stage_expenditure`:
  `∫ P_H(i) C_H(i) di + P_F C_F = P C`.
-/

namespace Gali.OpenEconomy.Preferences

open Filter Topology

/-! ### The tangent-line inequality for `u ↦ u^r` -/

/-- Galí (2015), (5), p. 226 (the inequality behind expenditure minimisation): for `r < 1`,
`r ≠ 0` and `u ≥ 0` (with `u > 0` when `r < 0`), `(u^r − 1)/r ≤ u − 1`. -/
theorem rpow_tangent_le {r u : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hu : 0 ≤ u)
    (hu' : 0 < r ∨ 0 < u) : (u ^ r - 1) / r ≤ u - 1 := by
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have hu0 : 0 < u := hu'.resolve_left (not_lt.2 hneg.le)
    have h1r : 0 < 1 - r := by linarith
    have hw1 : 0 ≤ 1 / (1 - r) := by positivity
    have hw2 : 0 ≤ -r / (1 - r) := div_nonneg (by linarith) h1r.le
    have hw : 1 / (1 - r) + -r / (1 - r) = 1 := by field_simp; ring
    have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 (Real.rpow_nonneg hu r) hu hw
    have hgm : (u ^ r) ^ (1 / (1 - r)) * u ^ (-r / (1 - r)) = 1 := by
      rw [← Real.rpow_mul hu, ← Real.rpow_add hu0]
      have : r * (1 / (1 - r)) + -r / (1 - r) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    have e : 1 / (1 - r) * u ^ r + -r / (1 - r) * u = (u ^ r - r * u) / (1 - r) := by
      field_simp
      ring
    rw [hgm, e, le_div_iff₀ h1r] at h
    rw [div_le_iff_of_neg hneg]
    nlinarith
  · have h1r : 0 ≤ 1 - r := by linarith
    have hw : r + (1 - r) = 1 := by ring
    have h := Real.geom_mean_le_arith_mean2_weighted hpos.le h1r hu zero_le_one hw
    rw [Real.one_rpow, mul_one, mul_one] at h
    rw [div_le_iff₀ hpos]
    nlinarith

/-- Galí (2015), (5), p. 226: equality in `rpow_tangent_le` holds iff `u = 1`. -/
theorem rpow_tangent_eq_iff {r u : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hu : 0 ≤ u)
    (hu' : 0 < r ∨ 0 < u) : (u ^ r - 1) / r = u - 1 ↔ u = 1 := by
  constructor
  swap
  · rintro rfl
    simp
  intro heq
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have hu0 : 0 < u := hu'.resolve_left (not_lt.2 hneg.le)
    have h1r : 0 < 1 - r := by linarith
    have hw1 : 0 < 1 / (1 - r) := by positivity
    have hw2 : 0 < -r / (1 - r) := div_pos (by linarith) h1r
    have hw : 1 / (1 - r) + -r / (1 - r) = 1 := by field_simp; ring
    have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hw1 hw2
      (Real.rpow_nonneg hu r) hu hw
    have hgm : (u ^ r) ^ (1 / (1 - r)) * u ^ (-r / (1 - r)) = 1 := by
      rw [← Real.rpow_mul hu, ← Real.rpow_add hu0]
      have : r * (1 / (1 - r)) + -r / (1 - r) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    have e : 1 / (1 - r) * u ^ r + -r / (1 - r) * u = (u ^ r - r * u) / (1 - r) := by
      field_simp
      ring
    rw [hgm, e] at hiff
    have h2 : u ^ r - r * u = 1 - r := by
      rw [div_eq_iff hneg.ne] at heq
      linarith
    have hur : u ^ r = u := hiff.1 (by rw [h2, div_self h1r.ne'])
    have hlog : r * Real.log u = Real.log u := by rw [← Real.log_rpow hu0, hur]
    have hl0 : Real.log u = 0 := by
      have : (r - 1) * Real.log u = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · exact h
    rcases Real.log_eq_zero.1 hl0 with h | h | h
    · rw [h] at hu0; exact absurd hu0 (lt_irrefl 0)
    · exact h
    · linarith
  · have h1r : 0 < 1 - r := by linarith
    have hw : r + (1 - r) = 1 := by ring
    have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hpos h1r hu zero_le_one hw
    rw [Real.one_rpow, mul_one, mul_one] at hiff
    refine hiff.1 ?_
    rw [div_eq_iff hpos.ne'] at heq
    linarith

/-- Galí (2015), (5), p. 226 (the aggregated tangent inequality): if positive weights
`ω₁ + ω₂ = 1` satisfy `ω₁ u^r + ω₂ v^r = 1`, then `ω₁ u + ω₂ v ≥ 1`, with equality iff
`u = v = 1`. -/
theorem weighted_tangent {r ω₁ ω₂ u v : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hω₁ : 0 < ω₁)
    (hω₂ : 0 < ω₂) (hω : ω₁ + ω₂ = 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : 0 < r ∨ (0 < u ∧ 0 < v)) (hc : ω₁ * u ^ r + ω₂ * v ^ r = 1) :
    1 ≤ ω₁ * u + ω₂ * v ∧ (ω₁ * u + ω₂ * v = 1 ↔ u = 1 ∧ v = 1) := by
  have hu' : 0 < r ∨ 0 < u := huv.imp_right And.left
  have hv' : 0 < r ∨ 0 < v := huv.imp_right And.right
  have h1 := rpow_tangent_le hr1 hr0 hu hu'
  have h2 := rpow_tangent_le hr1 hr0 hv hv'
  have hsum : ω₁ * ((u ^ r - 1) / r) + ω₂ * ((v ^ r - 1) / r) = 0 := by
    have : ω₁ * ((u ^ r - 1) / r) + ω₂ * ((v ^ r - 1) / r)
        = (ω₁ * u ^ r + ω₂ * v ^ r - (ω₁ + ω₂)) / r := by field_simp; ring
    rw [this, hc, hω, sub_self, zero_div]
  have k1 := mul_le_mul_of_nonneg_left h1 hω₁.le
  have k2 := mul_le_mul_of_nonneg_left h2 hω₂.le
  refine ⟨by nlinarith, ⟨fun heq => ?_, fun ⟨h1', h2'⟩ => by rw [h1', h2']; linarith⟩⟩
  have d1 : ω₁ * ((u - 1) - (u ^ r - 1) / r) = 0 := by nlinarith
  have d2 : ω₂ * ((v - 1) - (v ^ r - 1) / r) = 0 := by nlinarith
  rcases mul_eq_zero.1 d1 with h | h
  · exact absurd h hω₁.ne'
  rcases mul_eq_zero.1 d2 with h' | h'
  · exact absurd h' hω₂.ne'
  exact ⟨(rpow_tangent_eq_iff hr1 hr0 hu hu').1 (by linarith),
    (rpow_tangent_eq_iff hr1 hr0 hv hv').1 (by linarith)⟩

/-! ### The consumption index, the CPI and the demands (5) -/

/-- Galí (2015), eq. (2), p. 225: the home-bias CES consumption index
`C = ((1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η})^{η/(η−1)}` (for `η ≠ 1`). -/
noncomputable def cesIndex (υ η x y : ℝ) : ℝ :=
  ((1 - υ) ^ (1 / η) * x ^ ((η - 1) / η) + υ ^ (1 / η) * y ^ ((η - 1) / η)) ^ (η / (η - 1))

/-- Galí (2015), fn. 1, p. 225: the Cobb–Douglas index `C_H^{1−υ} C_F^υ/((1−υ)^{1−υ} υ^υ)`
(the `η = 1` case). -/
noncomputable def cesIndexCD (υ x y : ℝ) : ℝ :=
  x ^ (1 - υ) * y ^ υ / ((1 - υ) ^ (1 - υ) * υ ^ υ)

/-- Galí (2015), p. 226: the CPI `P = ((1−υ) P_H^{1−η} + υ P_F^{1−η})^{1/(1−η)}` (`η ≠ 1`). -/
noncomputable def cpi (υ η pH pF : ℝ) : ℝ :=
  ((1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η)) ^ (1 / (1 - η))

/-- Galí (2015), fn. 2, p. 226: the CPI at `η = 1`, `P = P_H^{1−υ} P_F^υ`. -/
noncomputable def cpiCD (υ pH pF : ℝ) : ℝ := pH ^ (1 - υ) * pF ^ υ

/-- Galí (2015), eq. (5), p. 226: home-goods demand `C_H = (1−υ)(P_H/P)^{−η} C`. -/
noncomputable def homeDemand (υ η pH P C : ℝ) : ℝ := (1 - υ) * (pH / P) ^ (-η) * C

/-- Galí (2015), eq. (5), p. 226: imported-goods demand `C_F = υ(P_F/P)^{−η} C`. -/
noncomputable def foreignDemand (υ η pF P C : ℝ) : ℝ := υ * (pF / P) ^ (-η) * C

variable {υ η pH pF : ℝ}

/-- Galí (2015), p. 226: the CPI is positive. -/
theorem cpi_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    0 < cpi υ η pH pF := by
  unfold cpi
  have : 0 < 1 - υ := by linarith
  positivity

/-- Galí (2015), p. 226: `P^{1−η} = (1−υ) P_H^{1−η} + υ P_F^{1−η}`. -/
theorem cpi_rpow (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    cpi υ η pH pF ^ (1 - η) = (1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η) := by
  have : 0 < 1 - υ := by linarith
  unfold cpi
  rw [one_div]
  exact Real.rpow_inv_rpow (by positivity) (sub_ne_zero.2 (Ne.symm hη1))

/-- Galí (2015), p. 226: the expenditure shares sum to one,
`(1−υ)(P_H/P)^{1−η} + υ(P_F/P)^{1−η} = 1`. -/
theorem shares_sum (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    (1 - υ) * (pH / cpi υ η pH pF) ^ (1 - η) + υ * (pF / cpi υ η pH pF) ^ (1 - η) = 1 := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  rw [Real.div_rpow hpH.le hP.le, Real.div_rpow hpF.le hP.le, cpi_rpow hυ0 hυ1 hη1 hpH hpF]
  have : 0 < (1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η) := by
    have : 0 < 1 - υ := by linarith
    positivity
  field_simp

/-- Galí (2015), (5), p. 226: the CES term of a demand,
`a^{1/η} (a z^{−η} C)^{(η−1)/η} = a z^{1−η} C^{(η−1)/η}`. -/
theorem demand_term {a z C : ℝ} (hη : 0 < η) (ha : 0 < a) (hz : 0 < z) (hC : 0 ≤ C) :
    a ^ (1 / η) * (a * z ^ (-η) * C) ^ ((η - 1) / η)
      = a * z ^ (1 - η) * C ^ ((η - 1) / η) := by
  rw [Real.mul_rpow (by positivity) hC, Real.mul_rpow ha.le (by positivity),
    ← Real.rpow_mul hz.le]
  have e1 : -η * ((η - 1) / η) = 1 - η := by field_simp; ring
  rw [e1, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ha]
  have e2 : 1 / η + (η - 1) / η = 1 := by field_simp; ring
  rw [e2, Real.rpow_one]

/-- Galí (2015), (5), p. 226: the cost of a demand, `p (a (p/P)^{−η} C) = a (p/P)^{1−η} P C`. -/
theorem spend_term {a p P C : ℝ} (hp : 0 < p) (hP : 0 < P) :
    p * (a * (p / P) ^ (-η) * C) = a * (p / P) ^ (1 - η) * (P * C) := by
  have hz : 0 < p / P := div_pos hp hP
  rw [sub_eq_add_neg, Real.rpow_add hz, Real.rpow_one]
  field_simp

/-- Galí (2015), p. 227: the demands (5) cost exactly `P_H C_H + P_F C_F = P C`. -/
theorem expenditure_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH)
    (hpF : 0 < pF) (C : ℝ) :
    pH * homeDemand υ η pH (cpi υ η pH pF) C + pF * foreignDemand υ η pF (cpi υ η pH pF) C
      = cpi υ η pH pF * C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  unfold homeDemand foreignDemand
  rw [spend_term hpH hP, spend_term hpF hP, ← add_mul, shares_sum hυ0 hυ1 hη1 hpH hpF, one_mul]

/-- Galí (2015), eq. (2): `C^{(η−1)/η} = (1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η}`. -/
theorem cesIndex_rpow (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cesIndex υ η x y ^ ((η - 1) / η)
      = (1 - υ) ^ (1 / η) * x ^ ((η - 1) / η) + υ ^ (1 / η) * y ^ ((η - 1) / η) := by
  have : 0 < 1 - υ := by linarith
  unfold cesIndex
  rw [show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
  exact Real.rpow_inv_rpow (by positivity)
    (div_ne_zero (sub_ne_zero.2 hη1) hη.ne')

/-- Galí (2015), eq. (5), p. 226: the demands (5) deliver exactly the index `C`. -/
theorem cesIndex_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ} (hC : 0 ≤ C) :
    cesIndex υ η (homeDemand υ η pH (cpi υ η pH pF) C)
      (foreignDemand υ η pF (cpi υ η pH pF) C) = C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  unfold cesIndex homeDemand foreignDemand
  rw [demand_term hη h1υ (div_pos hpH hP) hC, demand_term hη hυ0 (div_pos hpF hP) hC,
    ← add_mul, shares_sum hυ0 hυ1 hη1 hpH hpF, one_mul,
    show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
  exact Real.rpow_rpow_inv hC (div_ne_zero (sub_ne_zero.2 hη1) hη.ne')

/-- Galí (2015), (5): the index of a bundle with a positive quantity is positive. -/
theorem cesIndex_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : 0 < x ∨ 0 < y) : 0 < cesIndex υ η x y := by
  have h1υ : 0 < 1 - υ := by linarith
  unfold cesIndex
  apply Real.rpow_pos_of_pos
  rcases hxy with h | h
  · have := Real.rpow_pos_of_pos h ((η - 1) / η)
    have := Real.rpow_nonneg hy ((η - 1) / η)
    positivity
  · have := Real.rpow_pos_of_pos h ((η - 1) / η)
    have := Real.rpow_nonneg hx ((η - 1) / η)
    positivity

/-- Galí (2015), eq. (5), p. 226 (core of expenditure minimisation): for a bundle with
positive index `C`, the expenditure is at least `P C`, with equality iff the bundle is the
demand schedule (5) at `C`. Quantities may be zero only when `η > 1`. -/
theorem expenditure_core (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 1 < η ∨ (0 < x ∧ 0 < y)) (hC : 0 < cesIndex υ η x y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y ∧
      (pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
        x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
          y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y)) := by
  set P := cpi υ η pH pF with hPdef
  set C := cesIndex υ η x y with hCdef
  have hP : 0 < P := cpi_pos hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  set r := (η - 1) / η with hr
  have hr1 : r < 1 := by rw [hr, div_lt_one hη]; linarith
  have hr0 : r ≠ 0 := div_ne_zero (sub_ne_zero.2 hη1) hη.ne'
  set zH := pH / P
  set zF := pF / P
  have hzH : 0 < zH := div_pos hpH hP
  have hzF : 0 < zF := div_pos hpF hP
  set DH := (1 - υ) * zH ^ (-η) * C with hDH
  set DF := υ * zF ^ (-η) * C with hDF
  have hDH0 : 0 < DH := by positivity
  have hDF0 : 0 < DF := by positivity
  set ω₁ := (1 - υ) * zH ^ (1 - η)
  set ω₂ := υ * zF ^ (1 - η)
  have hω₁ : 0 < ω₁ := by positivity
  have hω₂ : 0 < ω₂ := by positivity
  have hω : ω₁ + ω₂ = 1 := shares_sum hυ0 hυ1 hη1 hpH hpF
  set u := x / DH
  set v := y / DF
  have hu : 0 ≤ u := div_nonneg hx hDH0.le
  have hv : 0 ≤ v := div_nonneg hy hDF0.le
  have hxu : x = u * DH := (div_mul_cancel₀ x hDH0.ne').symm
  have hyv : y = v * DF := (div_mul_cancel₀ y hDF0.ne').symm
  have hCr : 0 < C ^ r := Real.rpow_pos_of_pos hC r
  have hc : ω₁ * u ^ r + ω₂ * v ^ r = 1 := by
    have h := cesIndex_rpow hυ0 hυ1 hη hη1 hx hy
    rw [← hCdef, ← hr] at h
    have t1 : (1 - υ) ^ (1 / η) * x ^ r = u ^ r * (ω₁ * C ^ r) := by
      rw [hxu, Real.mul_rpow hu hDH0.le, ← demand_term hη h1υ hzH hC.le]
      ring
    have t2 : υ ^ (1 / η) * y ^ r = v ^ r * (ω₂ * C ^ r) := by
      rw [hyv, Real.mul_rpow hv hDF0.le, ← demand_term hη hυ0 hzF hC.le]
      ring
    rw [t1, t2] at h
    have : C ^ r * (ω₁ * u ^ r + ω₂ * v ^ r) = C ^ r * 1 := by
      linear_combination (-1 : ℝ) * h
    exact mul_left_cancel₀ hCr.ne' this
  have huv : 0 < r ∨ (0 < u ∧ 0 < v) := by
    rcases hxy with h | ⟨h1, h2⟩
    · left; rw [hr]; exact div_pos (by linarith) hη
    · right; exact ⟨div_pos h1 hDH0, div_pos h2 hDF0⟩
  obtain ⟨hle, hiff⟩ := weighted_tangent hr1 hr0 hω₁ hω₂ hω hu hv huv hc
  have hspend : pH * x + pF * y = P * C * (ω₁ * u + ω₂ * v) := by
    rw [hxu, hyv]
    have s1 := spend_term (η := η) (a := 1 - υ) (C := C) hpH hP
    have s2 := spend_term (η := η) (a := υ) (C := C) hpF hP
    have e1 : pH * (u * DH) = u * (pH * ((1 - υ) * (pH / P) ^ (-η) * C)) := by
      rw [hDH]; ring
    have e2 : pF * (v * DF) = v * (pF * (υ * (pF / P) ^ (-η) * C)) := by
      rw [hDF]; ring
    rw [e1, e2, s1, s2]
    ring
  have hPC : 0 < P * C := mul_pos hP hC
  refine ⟨?_, ?_⟩
  · rw [hspend]
    nlinarith
  · rw [hspend]
    constructor
    · intro h
      have h1 : ω₁ * u + ω₂ * v = 1 := by
        have : P * C * (ω₁ * u + ω₂ * v) = P * C * 1 := by rw [h, mul_one]
        exact mul_left_cancel₀ hPC.ne' this
      obtain ⟨hu1, hv1⟩ := hiff.1 h1
      refine ⟨?_, ?_⟩
      · rw [hxu, hu1, one_mul]; rfl
      · rw [hyv, hv1, one_mul]; rfl
    · rintro ⟨h1, h2⟩
      have hu1 : u = 1 := by
        change x / DH = 1
        rw [div_eq_one_iff_eq hDH0.ne']
        exact h1
      have hv1 : v = 1 := by
        change y / DF = 1
        rw [div_eq_one_iff_eq hDF0.ne']
        exact h2
      rw [hiff.2 ⟨hu1, hv1⟩, mul_one]

/-- Galí (2015), eq. (5), p. 226 (**expenditure minimisation**): every bundle of positive
quantities costs at least `P · C`, where `C` is its own consumption index (2). -/
theorem expenditure_ge (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y :=
  (expenditure_core hυ0 hυ1 hη hη1 hpH hpF hx.le hy.le (Or.inr ⟨hx, hy⟩)
    (cesIndex_pos hυ0 hυ1 hx.le hy.le (Or.inl hx))).1

/-- Galí (2015), eq. (5), p. 226: a bundle of positive quantities costs exactly `P · C` **iff**
it is the demand schedule `C_H = (1−υ)(P_H/P)^{−η} C`, `C_F = υ(P_F/P)^{−η} C`. -/
theorem expenditure_eq_iff (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
      x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
        y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y) :=
  (expenditure_core hυ0 hυ1 hη hη1 hpH hpF hx.le hy.le (Or.inr ⟨hx, hy⟩)
    (cesIndex_pos hυ0 hυ1 hx.le hy.le (Or.inl hx))).2

/-- Galí (2015), (2): with `η > 1` the empty bundle has index zero. -/
theorem cesIndex_zero (hη : 0 < η) (hη1 : 1 < η) : cesIndex υ η 0 0 = 0 := by
  have hr0 : (η - 1) / η ≠ 0 := div_ne_zero (by linarith) hη.ne'
  have he : η / (η - 1) ≠ 0 := div_ne_zero hη.ne' (by linarith)
  unfold cesIndex
  rw [Real.zero_rpow hr0, mul_zero, mul_zero, add_zero, Real.zero_rpow he]

/-- Galí (2015), eq. (5), p. 226, for `η > 1` with **nonnegative** quantities (zero
consumption of one good allowed): expenditure is at least `P · C`. -/
theorem expenditure_ge_of_one_lt (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : 1 < η)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y := by
  have hη : 0 < η := by linarith
  rcases hx.eq_or_lt with hx0 | hx0
  · rcases hy.eq_or_lt with hy0 | hy0
    · rw [← hx0, ← hy0, cesIndex_zero hη hη1]; simp
    · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
        (cesIndex_pos hυ0 hυ1 hx hy (Or.inr hy0))).1
  · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
      (cesIndex_pos hυ0 hυ1 hx hy (Or.inl hx0))).1

/-- Galí (2015), eq. (5), p. 226, for `η > 1` with nonnegative quantities: a bundle costs
exactly `P · C` iff it is the demand schedule (5). -/
theorem expenditure_eq_iff_of_one_lt (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : 1 < η)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
      x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
        y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y) := by
  have hη : 0 < η := by linarith
  rcases hx.eq_or_lt with hx0 | hx0
  · rcases hy.eq_or_lt with hy0 | hy0
    · rw [← hx0, ← hy0, cesIndex_zero hη hη1]
      simp [homeDemand, foreignDemand]
    · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
        (cesIndex_pos hυ0 hυ1 hx hy (Or.inr hy0))).2
  · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
      (cesIndex_pos hυ0 hυ1 hx hy (Or.inl hx0))).2

/-- Galí (2015), p. 226: the demands (5) are positive. -/
theorem demands_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ}
    (hC : 0 < C) : 0 < homeDemand υ η pH (cpi υ η pH pF) C ∧
      0 < foreignDemand υ η pF (cpi υ η pH pF) C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  have := div_pos hpH hP
  have := div_pos hpF hP
  unfold homeDemand foreignDemand
  constructor <;> positivity

/-- Galí (2015), p. 226: **the CPI is the minimum cost of one unit of the consumption index**:
`P = min {P_H C_H + P_F C_F : C_H, C_F > 0, C(C_H, C_F) = 1}`. -/
theorem cpi_isLeast (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) :
    IsLeast {e | ∃ x y, 0 < x ∧ 0 < y ∧ cesIndex υ η x y = 1 ∧ e = pH * x + pF * y}
      (cpi υ η pH pF) := by
  refine ⟨⟨homeDemand υ η pH (cpi υ η pH pF) 1, foreignDemand υ η pF (cpi υ η pH pF) 1,
    (demands_pos hυ0 hυ1 hpH hpF one_pos).1, (demands_pos hυ0 hυ1 hpH hpF one_pos).2,
    cesIndex_demand hυ0 hυ1 hη hη1 hpH hpF zero_le_one, ?_⟩, ?_⟩
  · rw [expenditure_demand hυ0 hυ1 hη1 hpH hpF, mul_one]
  · rintro e ⟨x, y, hx, hy, h1, rfl⟩
    have := expenditure_ge hυ0 hυ1 hη hη1 hpH hpF hx hy
    rwa [h1, mul_one] at this

/-- Galí (2015), (5) in dual form: with expenditure `X`, the attainable index is at most
`X / P`. -/
theorem cesIndex_le_of_spend (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y X : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hX : pH * x + pF * y = X) : cesIndex υ η x y ≤ X / cpi υ η pH pF := by
  rw [le_div_iff₀ (cpi_pos hυ0 hυ1 hpH hpF), mul_comm, ← hX]
  exact expenditure_ge hυ0 hυ1 hη hη1 hpH hpF hx hy

/-- Galí (2015), p. 226: the import expenditure share under (5) is `υ (P_F/P)^{1−η}`. -/
theorem importShare (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ}
    (hC : 0 < C) :
    pF * foreignDemand υ η pF (cpi υ η pH pF) C / (cpi υ η pH pF * C)
      = υ * (pF / cpi υ η pH pF) ^ (1 - η) := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  unfold foreignDemand
  rw [spend_term hpF hP]
  field_simp

/-- Galí (2015), p. 226: when `P_H = P_F` (e.g. the symmetric steady state) the CPI equals
the common price and the import share is exactly `υ`. -/
theorem importShare_of_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH)
    {C : ℝ} (hC : 0 < C) :
    cpi υ η pH pH = pH ∧
      pH * foreignDemand υ η pH (cpi υ η pH pH) C / (cpi υ η pH pH * C) = υ := by
  have hcpi : cpi υ η pH pH = pH := by
    unfold cpi
    rw [show (1 - υ) * pH ^ (1 - η) + υ * pH ^ (1 - η) = pH ^ (1 - η) by ring,
      ← Real.rpow_mul hpH.le, mul_one_div_cancel (sub_ne_zero.2 (Ne.symm hη1)), Real.rpow_one]
  refine ⟨hcpi, ?_⟩
  rw [importShare hυ0 hυ1 hpH hpH hC, hcpi, div_self hpH.ne', Real.one_rpow, mul_one]

/-! ### Footnotes 1 and 2: the limit `η → 1` -/

/-- Galí (2015), fns. 1–2, pp. 225–226: for weights `a, b > 0`, `a + b = 1` and `z₁, z₂ > 0`,
the power mean `(a z₁^s + b z₂^s)^{1/s}` tends to the geometric mean `z₁^a z₂^b` as `s → 0`. -/
theorem powerMean_tendsto {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) :
    Tendsto (fun s : ℝ => (a * z₁ ^ s + b * z₂ ^ s) ^ (1 / s)) (𝓝[≠] 0)
      (𝓝 (z₁ ^ a * z₂ ^ b)) := by
  set f : ℝ → ℝ := fun s => a * Real.exp (s * Real.log z₁) + b * Real.exp (s * Real.log z₂)
    with hfdef
  have hf0 : f 0 = 1 := by simp [f, hab]
  have hfpos : ∀ s, 0 < f s := fun s => by positivity
  have hfd : HasDerivAt f (a * Real.log z₁ + b * Real.log z₂) 0 := by
    have h3 := (((hasDerivAt_id' (0 : ℝ)).mul_const (Real.log z₁)).exp.const_mul a).add
      (((hasDerivAt_id' (0 : ℝ)).mul_const (Real.log z₂)).exp.const_mul b)
    simp only [zero_mul, Real.exp_zero, one_mul] at h3
    exact h3
  have hg : HasDerivAt (fun s => Real.log (f s)) (a * Real.log z₁ + b * Real.log z₂) 0 := by
    convert hfd.log (by rw [hf0]; norm_num) using 1
    rw [hf0, div_one]
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have hlim := (Real.continuous_exp.tendsto _).comp hslope
  have hK : Real.exp (a * Real.log z₁ + b * Real.log z₂) = z₁ ^ a * z₂ ^ b := by
    rw [Real.exp_add, Real.rpow_def_of_pos hz₁, Real.rpow_def_of_pos hz₂, mul_comm a,
      mul_comm b]
  rw [hK] at hlim
  refine hlim.congr fun s => ?_
  simp only [Function.comp_apply, zero_add, hf0, Real.log_one, sub_zero, smul_eq_mul]
  have hfs : f s = a * z₁ ^ s + b * z₂ ^ s := by
    simp only [f]
    rw [Real.rpow_def_of_pos hz₁, Real.rpow_def_of_pos hz₂, mul_comm (Real.log z₁),
      mul_comm (Real.log z₂)]
  rw [Real.rpow_def_of_pos (by rw [← hfs]; exact hfpos s), ← hfs, one_div, mul_comm]

/-- Galí (2015), fn. 1, p. 225: **as `η → 1` the consumption index (2) tends to the
Cobb–Douglas index** `C_H^{1−υ} C_F^υ / ((1−υ)^{1−υ} υ^υ)` (for `C_H, C_F > 0`). -/
theorem cesIndex_tendsto_cd (hυ0 : 0 < υ) (hυ1 : υ < 1) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    Tendsto (fun η => cesIndex υ η x y) (𝓝[≠] 1) (𝓝 (cesIndexCD υ x y)) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hM := powerMean_tendsto h1υ hυ0 (by ring) (div_pos hx h1υ) (div_pos hy hυ0)
  have hr : Tendsto (fun η : ℝ => (η - 1) / η) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun η : ℝ => (η - 1) / η) 1 :=
        (continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero
      have := hc.tendsto
      simp only [sub_self, zero_div] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · have h0 : ∀ᶠ η in 𝓝[≠] (1 : ℝ), η ≠ 0 :=
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
      filter_upwards [h0, self_mem_nhdsWithin] with η hη0 hη1
      exact div_ne_zero (sub_ne_zero.2 hη1) hη0
  have hlim := hM.comp hr
  have htarget : (x / (1 - υ)) ^ (1 - υ) * (y / υ) ^ υ = cesIndexCD υ x y := by
    rw [cesIndexCD, Real.div_rpow hx.le h1υ.le, Real.div_rpow hy.le hυ0.le]
    field_simp
  rw [htarget] at hlim
  refine hlim.congr' ?_
  have h0 : ∀ᶠ η in 𝓝[≠] (1 : ℝ), η ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
  filter_upwards [h0, self_mem_nhdsWithin] with η hη0 hη1
  have hη1' : η - 1 ≠ 0 := sub_ne_zero.2 hη1
  simp only [Function.comp_apply]
  unfold cesIndex
  have e1 : 1 / ((η - 1) / η) = η / (η - 1) := one_div_div _ _
  have hw : ∀ {a z : ℝ}, 0 < a → 0 < z →
      a * (z / a) ^ ((η - 1) / η) = a ^ (1 / η) * z ^ ((η - 1) / η) := by
    intro a z ha hz
    rw [Real.div_rpow hz.le ha.le]
    have : 1 / η = 1 - (η - 1) / η := by field_simp; ring
    rw [this, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [e1, hw h1υ hx, hw hυ0 hy]

/-- Galí (2015), fn. 2, p. 226: **as `η → 1` the CPI tends to `P_H^{1−υ} P_F^υ`**. -/
theorem cpi_tendsto_cd (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    Tendsto (fun η => cpi υ η pH pF) (𝓝[≠] 1) (𝓝 (cpiCD υ pH pF)) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hM := powerMean_tendsto h1υ hυ0 (by ring) hpH hpF
  have hs : Tendsto (fun η : ℝ => 1 - η) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun η : ℝ => 1 - η) 1 := continuousAt_const.sub continuousAt_id
      have := hc.tendsto
      simp only [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with η hη1
      exact sub_ne_zero.2 (Ne.symm hη1)
  exact hM.comp hs

/-! ### The Cobb–Douglas case `η = 1` (fn. 2) -/

/-- Galí (2015), eq. (5) with `η = 1`: demand `C_H = (1−υ)(P_H/P)^{−1} C = (1−υ) P C / P_H`
(and symmetrically for `C_F`), with `P = P_H^{1−υ} P_F^υ`. -/
theorem cesIndexCD_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {C : ℝ} (hC : 0 ≤ C) :
    cesIndexCD υ (homeDemand υ 1 pH (cpiCD υ pH pF) C)
      (foreignDemand υ 1 pF (cpiCD υ pH pF) C) = C := by
  have h1υ : 0 < 1 - υ := by linarith
  have hP : 0 < cpiCD υ pH pF := by unfold cpiCD; positivity
  set P := cpiCD υ pH pF with hPdef
  unfold cesIndexCD homeDemand foreignDemand
  rw [Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div]
  have e1 : (1 - υ) * (P / pH) * C = (1 - υ) * (P * C / pH) := by ring
  have e2 : υ * (P / pF) * C = υ * (P * C / pF) := by ring
  rw [e1, e2, Real.mul_rpow h1υ.le (by positivity), Real.mul_rpow hυ0.le (by positivity),
    Real.div_rpow (by positivity) hpH.le, Real.div_rpow (by positivity) hpF.le,
    Real.mul_rpow hP.le hC, Real.mul_rpow hP.le hC]
  have hPC : P ^ (1 - υ) * P ^ υ = P := by
    rw [← Real.rpow_add hP]; simp
  have hCC : C ^ (1 - υ) * C ^ υ = C := by
    rcases hC.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow h1υ.ne', zero_mul]
    · rw [← Real.rpow_add h]; simp
  have hPdef' : P = pH ^ (1 - υ) * pF ^ υ := rfl
  have key : (1 - υ) ^ (1 - υ) * (P ^ (1 - υ) * C ^ (1 - υ) / pH ^ (1 - υ)) *
      (υ ^ υ * (P ^ υ * C ^ υ / pF ^ υ)) / ((1 - υ) ^ (1 - υ) * υ ^ υ)
      = (P ^ (1 - υ) * P ^ υ) * (C ^ (1 - υ) * C ^ υ) / (pH ^ (1 - υ) * pF ^ υ) := by
    have : 0 < (1 - υ) ^ (1 - υ) := by positivity
    have : 0 < υ ^ υ := by positivity
    have : 0 < pH ^ (1 - υ) := by positivity
    have : 0 < pF ^ υ := by positivity
    field_simp
  rw [key, hPC, hCC, ← hPdef']
  field_simp

/-- Galí (2015), p. 227 with `η = 1`: the demands cost exactly `P C` with
`P = P_H^{1−υ} P_F^υ`. -/
theorem expenditureCD_demand (hpH : 0 < pH) (hpF : 0 < pF)
    (C : ℝ) :
    pH * homeDemand υ 1 pH (cpiCD υ pH pF) C + pF * foreignDemand υ 1 pF (cpiCD υ pH pF) C
      = cpiCD υ pH pF * C := by
  unfold homeDemand foreignDemand
  rw [Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div]
  field_simp
  ring

/-- Galí (2015), fn. 2, p. 226 (with the fn-1 normalisation): the index cost identity
`P · C(C_H, C_F) = (P_H C_H/(1−υ))^{1−υ} (P_F C_F/υ)^υ` at `η = 1`. -/
theorem cpiCD_mul_cesIndexCD (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpiCD υ pH pF * cesIndexCD υ x y
      = (pH * x / (1 - υ)) ^ (1 - υ) * (pF * y / υ) ^ υ := by
  have h1υ : 0 < 1 - υ := by linarith
  unfold cpiCD cesIndexCD
  rw [Real.div_rpow (by positivity) h1υ.le, Real.div_rpow (by positivity) hυ0.le,
    Real.mul_rpow hpH.le hx, Real.mul_rpow hpF.le hy]
  have : 0 < (1 - υ) ^ (1 - υ) := by positivity
  have : 0 < υ ^ υ := by positivity
  field_simp

/-- Galí (2015), fn. 2, p. 226: at `η = 1`, every bundle `C_H, C_F ≥ 0` costs at least
`P_H^{1−υ} P_F^υ · C`, `C` its Cobb–Douglas index (fn. 1): the CPI is exactly
`P_H^{1−υ}P_F^υ`. -/
theorem expenditureCD_ge (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpiCD υ pH pF * cesIndexCD υ x y ≤ pH * x + pF * y := by
  have h1υ : 0 < 1 - υ := by linarith
  rw [cpiCD_mul_cesIndexCD hυ0 hυ1 hpH hpF hx hy]
  have h := Real.geom_mean_le_arith_mean2_weighted h1υ.le hυ0.le
    (div_nonneg (mul_nonneg hpH.le hx) h1υ.le) (div_nonneg (mul_nonneg hpF.le hy) hυ0.le)
    (by ring)
  have e : (1 - υ) * (pH * x / (1 - υ)) + υ * (pF * y / υ) = pH * x + pF * y := by
    field_simp
  linarith

/-- Galí (2015), (5) and fn. 2 at `η = 1`: a bundle costs exactly `P · C` iff it is the
demand schedule `C_H = (1−υ)(P_H/P)^{−1} C`, `C_F = υ(P_F/P)^{−1} C`. -/
theorem expenditureCD_eq_iff (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pH * x + pF * y = cpiCD υ pH pF * cesIndexCD υ x y ↔
      x = homeDemand υ 1 pH (cpiCD υ pH pF) (cesIndexCD υ x y) ∧
        y = foreignDemand υ 1 pF (cpiCD υ pH pF) (cesIndexCD υ x y) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hP : 0 < cpiCD υ pH pF := by unfold cpiCD; positivity
  set X1 := pH * x / (1 - υ)
  set X2 := pF * y / υ
  have hX1 : 0 ≤ X1 := div_nonneg (mul_nonneg hpH.le hx) h1υ.le
  have hX2 : 0 ≤ X2 := div_nonneg (mul_nonneg hpF.le hy) hυ0.le
  have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h1υ hυ0 hX1 hX2 (by ring)
  have e : (1 - υ) * X1 + υ * X2 = pH * x + pF * y := by
    simp only [X1, X2]; field_simp
  have hPC := cpiCD_mul_cesIndexCD hυ0 hυ1 hpH hpF hx hy
  rw [e] at hiff
  set P := cpiCD υ pH pF
  set C := cesIndexCD υ x y
  have hdH : homeDemand υ 1 pH P C = (1 - υ) * (P * C) / pH := by
    unfold homeDemand; rw [Real.rpow_neg_one, inv_div]; ring
  have hdF : foreignDemand υ 1 pF P C = υ * (P * C) / pF := by
    unfold foreignDemand; rw [Real.rpow_neg_one, inv_div]; ring
  rw [hdH, hdF, hPC]
  set G := X1 ^ (1 - υ) * X2 ^ υ with hG
  rw [show (pH * x + pF * y = G) ↔ (G = pH * x + pF * y) from eq_comm, hiff]
  constructor
  · intro h
    have hX : G = X1 := by
      rw [hG, ← h, ← Real.rpow_add' hX1 (by norm_num : (1 - υ) + υ ≠ 0)]
      simp
    rw [hX]
    refine ⟨?_, ?_⟩
    · simp only [X1]; field_simp
    · rw [h]; simp only [X2]; field_simp
  · rintro ⟨h1, h2⟩
    have k1 : X1 = G := by simp only [X1]; rw [h1]; field_simp
    have k2 : X2 = G := by simp only [X2]; rw [h2]; field_simp
    rw [k1, k2]

namespace Variety

open MeasureTheory

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: the aggregate price index `P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 52–53: the CES consumption index
`C = (∫ C(i)^{(ε−1)/ε} di)^{ε/(ε−1)}`. -/
noncomputable def cesAgg (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1), p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C`. -/
noncomputable def demand (μ : Measure G) (ε : ℝ) (P : G → ℝ) (C : ℝ) (i : G) : ℝ :=
  (P i / priceIndex μ ε P) ^ (-ε) * C

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the factorisation behind `young_le`,
`c^r = (a c C^{−1/ε})^r (a^{1−ε} C^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    (a * c * C ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ^ (1 / ε)
      = c ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hC.le]
  have e1 : a ^ ((ε - 1) / ε) * c ^ ((ε - 1) / ε) * C ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * C ^ ((ε - 1) / ε * (1 / ε)))
      = c ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (C ^ (-1 / ε * ((ε - 1) / ε)) * C ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hC]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the pointwise weighted AM–GM (Young) inequality behind
expenditure minimisation. For a relative price `a > 0`, a quantity `c ≥ 0` and an aggregate
`C > 0`, `c^r ≤ r (a c C^{−1/ε}) + (1/ε) a^{1−ε} C^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: equality in `young_le` holds iff `c = a^{−ε} C`, i.e. iff
the quantity lies on the demand schedule (1). -/
theorem young_eq_iff {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ↔
      c = a ^ (-ε) * C := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * C ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * C ^ ((ε - 1) / ε) = a * C ^ (-1 / ε) * (a ^ (-ε) * C) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : C ^ ((ε - 1) / ε) = C ^ (-1 / ε) * C := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hC, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * c * C ^ (-1 / ε) = a * C ^ (-1 / ε) * c by ring]
  exact mul_right_inj' hk

variable {μ : Measure G} {ε : ℝ} {P : G → ℝ}

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: the price index is positive when `∫ P(i)^{1−ε} > 0`. -/
theorem priceIndex_pos (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) : 0 < priceIndex μ ε P :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: `P^{1−ε} = ∫ P(i)^{1−ε} di`, the defining property of the index. -/
theorem priceIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    priceIndex μ ε P ^ (1 - ε) = ∫ i, P i ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 85 (index condition): `∫ (P(i)/P)^{1−ε} di = 1`. -/
theorem integral_relPrice_rpow (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    ∫ i, (P i / priceIndex μ ε P) ^ (1 - ε) ∂μ = 1 := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  rw [integral_div, priceIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 85: the relative-price integrand `(P(i)/P)^{1−ε}` is integrable. -/
theorem integrable_relPrice_rpow (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    Integrable (fun i => (P i / priceIndex μ ε P) ^ (1 - ε)) μ := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  exact hPi.div_const _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1) and p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C` delivers
exactly the aggregate `C`. -/
theorem cesAgg_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {C : ℝ} (hC : 0 ≤ C) : cesAgg μ ε (demand μ ε P C) = C := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ i, demand μ ε P C i ^ ((ε - 1) / ε)
      = C ^ ((ε - 1) / ε) * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    rw [demand, Real.mul_rpow (by positivity) hC, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold cesAgg
  simp_rw [hpt]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one, Real.rpow_rpow_inv hC hr]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: `P(i) (P(i)/P)^{−ε} C = P C (P(i)/P)^{1−ε}` pointwise. -/
theorem price_mul_demand (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) (C : ℝ)
    (i : G) : P i * demand μ ε P C i
      = priceIndex μ ε P * C * (P i / priceIndex μ ε P) ^ (1 - ε) := by
  have hI := priceIndex_pos hpos
  have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
  have h1 : (P i / priceIndex μ ε P) ^ (1 - ε)
      = P i / priceIndex μ ε P * (P i / priceIndex μ ε P) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [demand, h1]
  field_simp

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: under the demand schedule, total expenditure is
`∫ P(i) C(i) di = P C`. -/
theorem spend_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    (C : ℝ) : ∫ i, P i * demand μ ε P C i ∂μ = priceIndex μ ε P * C := by
  simp_rw [price_mul_demand hP hpos C]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the CES aggregate is nonnegative. -/
theorem cesAgg_nonneg {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ cesAgg μ ε c :=
  Real.rpow_nonneg (integral_nonneg fun i => Real.rpow_nonneg (hc i) _) _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: `C^r = ∫ C(i)^r` for the CES aggregate `C`. -/
theorem cesAgg_rpow (hε : 1 < ε) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε c ^ ((ε - 1) / ε) = ∫ i, c i ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun i => Real.rpow_nonneg (hc i) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the integrated Young bound. For a bundle with positive
aggregate `C`, `C^r ≤ r C^{−1/ε} (∫ P c)/P + (1/ε) C^r`. -/
theorem integrated_young (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hC : 0 < cesAgg μ ε c) :
    Integrable (fun i => (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) μ ∧
      (∀ i, c i ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∧
      ∫ i, ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
          (∫ i, P i * c i ∂μ) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) := by
  have hI := priceIndex_pos hpos
  have hint1 := hpc.const_mul ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P))
  have hint2 := (integrable_relPrice_rpow hPi hP hpos).const_mul
    (1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun i => ?_, ?_⟩
  · have h := young_le hε (div_pos (hP i) hI) (hc i) hC
    have e : (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) * (P i * c i)
        = (ε - 1) / ε * (P i / priceIndex μ ε P * c i * cesAgg μ ε c ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53 and App. 3.1, p. 83 (**expenditure minimisation**): any bundle
`C(·) ≥ 0` costs at least `P · C`, where `C` is its CES aggregate. -/
theorem spend_ge (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    priceIndex μ ε P * cesAgg μ ε c ≤ ∫ i, P i * c i ∂μ := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ i, P i * c i ∂μ := integral_nonneg fun i => mul_nonneg (hP i).le (hc i)
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun i => Real.rpow_nonneg (hc i) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← cesAgg_rpow hε hc] at hmono
  set C := cesAgg μ ε c
  set S := ∫ i, P i * c i ∂μ
  have hK : 0 < C ^ (-1 / ε) := Real.rpow_pos_of_pos hC _
  have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hC, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (C * C ^ (-1 / ε)) ≤
      (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (C ^ (-1 / ε) / priceIndex μ ε P) * S
        = (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm C] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1), p. 53 and App. 3.1, p. 83: a bundle costs exactly `P · C` (its
aggregate `C`) **if and only if** it is the demand schedule `C(i) = (P(i)/P)^{−ε} C`
almost everywhere. -/
theorem spend_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    ∫ i, P i * c i ∂μ = priceIndex μ ε P * cesAgg μ ε c ↔
      c =ᵐ[μ] demand μ ε P (cesAgg μ ε c) := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← spend_demand hε hP hpos (cesAgg μ ε c)]
    refine integral_congr_ae ?_
    filter_upwards [h] with i hi
    rw [hi]
  intro heq
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg (hP i).le (hc i)) hpc).1 heq
    filter_upwards [hz] with i hi
    rw [← h0, demand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hP i).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  set C := cesAgg μ ε c
  have hcr : Integrable (fun i => c i ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← cesAgg_rpow hε hc]
    exact (Real.rpow_pos_of_pos hC _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (hle i)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← cesAgg_rpow hε hc, heq]
      have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hC, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with i hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hP i) hI) (hc i) hC).1 (by
    rw [← hi]
    ring)
  rw [this, demand]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83 (dual form): for a bundle with expenditure
`∫ P(i) C(i) = X`, the attainable consumption index is at most `X / P`. -/
theorem cesAgg_le_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) : cesAgg μ ε c ≤ X / priceIndex μ ε P := by
  rw [le_div_iff₀ (priceIndex_pos hpos), mul_comm, ← hX]
  exact spend_ge hε hP hPi hpos hc hpc

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83 (dual form, equality): with expenditure `X`, the index
attains `X / P` iff `C(i) = (P(i)/P)^{−ε} X/P` almost everywhere. -/
theorem cesAgg_eq_iff_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) :
    cesAgg μ ε c = X / priceIndex μ ε P ↔
      c =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) := by
  have hI := priceIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (spend_eq_iff hε hP hPi hpos hc hpc).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / priceIndex μ ε P := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun i => mul_nonneg (hP i).le (hc i)) hI.le
    have hagg : cesAgg μ ε c = cesAgg μ ε (demand μ ε P (X / priceIndex μ ε P)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hε hP hpos hX0]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ P(i)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : G → ℝ} (hμ : μ ≠ 0) (hf : ∀ i, 0 < f i)
    (hfi : Integrable f μ) : 0 < ∫ i, f i ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun i => (hf i).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun i => (hf i).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: Lebesgue measure on the goods continuum `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: §3.1, p. 53 and App. 3.1, p. 83, on the book's **continuum of goods
`[0, 1]` with Lebesgue measure**: (i) every bundle `C(·) ≥ 0` costs at least `P · C`;
(ii) it costs exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` for a.e. `i ∈ [0, 1]`;
(iii) the demand schedule attains any aggregate `C ≥ 0`; (iv) it costs `P C`. -/
theorem unitInterval_expenditure_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) {c : ℝ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hQc : IntegrableOn (fun i => Q i * c i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * cesAgg (volume.restrict (Set.Icc 0 1)) ε c
        ≤ ∫ i in Set.Icc 0 1, Q i * c i ∧
      (∫ i in Set.Icc 0 1, Q i * c i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε c ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          c i = demand (volume.restrict (Set.Icc 0 1)) ε Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε c) i) ∧
      (∀ C : ℝ, 0 ≤ C → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Q C) = C) ∧
      ∀ C : ℝ, ∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q C i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  exact ⟨spend_ge hε hQ hQi hpos hc hQc, spend_eq_iff hε hQ hQi hpos hc hQc,
    fun C hC => cesAgg_demand hε hQ hpos hC, spend_demand hε hQ hpos⟩

/-- Galí (2015), eqs. (4)–(5) and p. 227 (**two-stage budgeting**): with domestic varieties
`i ∈ [0, 1]` priced `Q(i)` and `P_H` their price index, the home demand `C_H` of (5) is
allocated across varieties by (4) and imports are `C_F` of (5); total spending is
`∫ P_H(i) C_H(i) di + P_F C_F = P C`. -/
theorem two_stage_expenditure {υ η ε pF : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1)
    (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) (hpF : 0 < pF) (C : ℝ) :
    (∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q
        (homeDemand υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q)
          (cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF) C) i)
      + pF * foreignDemand υ η pF
          (cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF) C
      = cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  rw [spend_demand hε hQ hpos]
  exact expenditure_demand hυ0 hυ1 hη1 (priceIndex_pos hpos) hpF C

end Variety

end Gali.OpenEconomy.Preferences

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Domestic inflation, CPI inflation, the real exchange rate and the terms of trade

Galí (2015), Chapter 8, §8.1.1.1, pp. 229–230: eqs. (12), (13), (14) and `q = (1−υ)s`.

Lower-case letters are logs: `p_H = log P_H`, `p_F = log P_F`, `s = p_F − p_H` (terms of
trade), `p = log P` with `P` the CPI of `Preferences`.

## Main results

* `log_cpi_eq` (eq. (12), exact for every `η ≠ 1`): `p = p_H + h(s)` where
  `h(s) = log P(1, e^s)` (`cpiGap`) — a consequence of the CPI being homogeneous of degree
  one (`cpi_homog`).
* `cpiGap_zero`, `hasDerivAt_cpiGap`: `h(0) = 0`, `h'(0) = υ`; hence (12) to first order.
* `hasFDerivAt_logCPI` (eq. (12) as an exact derivative): the log CPI as a function of
  `(p_H, p_F)` has derivative `(1−υ) dp_H + υ dp_F` at every symmetric point `p_H = p_F`.
* `log_cpiCD_eq` (fn. 4): at `η = 1`, `p = (1−υ)p_H + υp_F = p_H + υs` exactly.
* `cpi_inflation` (eq. (13)): `π_t = π_{H,t} + h(s_t) − h(s_{t−1})` exactly, with
  `hasFDerivAt_inflationGap` (first order: `υΔs_t`) and `cpi_inflation_cd` (exact at `η = 1`).
* `tot_lop` (eq. (14)): the law of one price `P_F = ℰP*` gives `s = e + p* − p_H`.
* `rer_eq` (p. 230): `q = p_F − p = s + p_H − p = s − h(s)`; `hasDerivAt_rerGap`:
  first order `q = (1−υ)s`; `rer_cd`: exact at `η = 1`.
-/

namespace Gali.OpenEconomy.Identities

open Preferences

variable {υ η : ℝ}

/-- Galí (2015), (12), p. 229: the CPI is homogeneous of degree one,
`P(λP_H, λP_F) = λ P(P_H, P_F)`. -/
theorem cpi_homog (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) {l a b : ℝ} (hl : 0 < l)
    (ha : 0 < a) (hb : 0 < b) : cpi υ η (l * a) (l * b) = l * cpi υ η a b := by
  have h1υ : 0 < 1 - υ := by linarith
  have hne : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη1)
  unfold cpi
  rw [Real.mul_rpow hl.le ha.le, Real.mul_rpow hl.le hb.le,
    show (1 - υ) * (l ^ (1 - η) * a ^ (1 - η)) + υ * (l ^ (1 - η) * b ^ (1 - η))
      = l ^ (1 - η) * ((1 - υ) * a ^ (1 - η) + υ * b ^ (1 - η)) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hl.le,
    mul_one_div_cancel hne, Real.rpow_one]

/-- Galí (2015), (12), p. 229: the log CPI in excess of the log domestic price as a function
of the log terms of trade, `h(s) = log P(1, e^s) = p − p_H`. -/
noncomputable def cpiGap (υ η s : ℝ) : ℝ := Real.log (cpi υ η 1 (Real.exp s))

/-- Galí (2015), eq. (12), p. 229, **exact form**: `p = p_H + h(s)` with `s = p_F − p_H`. -/
theorem log_cpi_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℝ) :
    Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) = pH + cpiGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 one_pos (Real.exp_pos (pF - pH))
  have e2 : Real.exp pF = Real.exp pH * Real.exp (pF - pH) := by
    rw [← Real.exp_add]; ring_nf
  have hh := cpi_homog hυ0 hυ1 hη1 (Real.exp_pos pH) one_pos (Real.exp_pos (pF - pH))
  rw [mul_one] at hh
  rw [cpiGap, e2, hh, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]

/-- Galí (2015), (12), p. 229: an explicit formula,
`h(s) = log((1−υ) + υ e^{(1−η)s}) / (1−η)`. -/
theorem cpiGap_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (s : ℝ) :
    cpiGap υ η s = Real.log ((1 - υ) + υ * Real.exp ((1 - η) * s)) / (1 - η) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hS : 0 < (1 - υ) + υ * Real.exp ((1 - η) * s) := by positivity
  unfold cpiGap cpi
  rw [Real.one_rpow, mul_one, ← Real.exp_mul, mul_comm s, Real.log_rpow hS]
  ring

/-- Galí (2015), (12), p. 229: in the symmetric steady state (`S = 1`, `s = 0`) the CPI equals
the domestic price index: `h(0) = 0`. -/
theorem cpiGap_zero (hυ0 : 0 < υ) (hυ1 : υ < 1) : cpiGap υ η 0 = 0 := by
  rw [cpiGap_eq hυ0 hυ1, mul_zero, Real.exp_zero, mul_one, sub_add_cancel, Real.log_one,
    zero_div]

/-- Galí (2015), eq. (12), p. 229 (**first order**): `h'(0) = υ`, so that
`p = p_H + υ s` up to first order around the symmetric steady state `s = 0`. -/
theorem hasDerivAt_cpiGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    HasDerivAt (cpiGap υ η) υ 0 := by
  have hne : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη1)
  have hfun : cpiGap υ η = fun s => Real.log ((1 - υ) + υ * Real.exp ((1 - η) * s)) / (1 - η) :=
    funext (cpiGap_eq hυ0 hυ1)
  rw [hfun]
  have hin : HasDerivAt (fun s => (1 - υ) + υ * Real.exp ((1 - η) * s))
      (υ * (Real.exp ((1 - η) * 0) * ((1 - η) * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - η)).exp.const_mul υ).const_add (1 - υ)
  have hval : (1 - υ) + υ * Real.exp ((1 - η) * 0) = 1 := by simp
  have hlog := hin.log (by rw [hval]; exact one_ne_zero)
  rw [hval] at hlog
  convert hlog.div_const (1 - η) using 1
  field_simp
  simp

/-- Galí (2015), eq. (12), p. 229, as an **exact derivative**: the log CPI
`(p_H, p_F) ↦ log P(e^{p_H}, e^{p_F})` has Fréchet derivative `(1−υ) dp_H + υ dp_F` at every
symmetric point `p_H = p_F = p̄`. -/
theorem hasFDerivAt_logCPI (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pbar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => Real.log (cpi υ η (Real.exp x.1) (Real.exp x.2)))
      ((1 - υ) • ContinuousLinearMap.fst ℝ ℝ ℝ + υ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (pbar, pbar) := by
  have hfun : (fun x : ℝ × ℝ => Real.log (cpi υ η (Real.exp x.1) (Real.exp x.2)))
      = fun x => x.1 + cpiGap υ η (x.2 - x.1) :=
    funext fun x => log_cpi_eq hυ0 hυ1 hη1 x.1 x.2
  rw [hfun]
  have hd : HasDerivAt (cpiGap υ η) υ ((pbar, pbar).2 - (pbar, pbar).1) := by
    simp only [sub_self]
    exact hasDerivAt_cpiGap hυ0 hυ1 hη1
  have hlin : HasFDerivAt (fun x : ℝ × ℝ => x.2 - x.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (pbar, pbar) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have hcomp := hd.comp_hasFDerivAt (pbar, pbar) hlin
  have hsum := hasFDerivAt_fst.add hcomp
  have hL : (1 - υ) • ContinuousLinearMap.fst ℝ ℝ ℝ + υ • ContinuousLinearMap.snd ℝ ℝ ℝ
      = ContinuousLinearMap.fst ℝ ℝ ℝ
        + υ • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [_root_.add_apply, _root_.smul_apply,
      _root_.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    ring
  rw [hL]
  exact hsum

/-- Galí (2015), eq. (12) and fn. 4, p. 229: **at `η = 1` the relation is exact**,
`p = (1−υ)p_H + υ p_F = p_H + υ s`. -/
theorem log_cpiCD_eq (pH pF : ℝ) :
    Real.log (cpiCD υ (Real.exp pH) (Real.exp pF)) = (1 - υ) * pH + υ * pF ∧
      (1 - υ) * pH + υ * pF = pH + υ * (pF - pH) := by
  refine ⟨?_, by ring⟩
  unfold cpiCD
  rw [Real.log_mul (Real.rpow_pos_of_pos (Real.exp_pos _) _).ne'
    (Real.rpow_pos_of_pos (Real.exp_pos _) _).ne', Real.log_rpow (Real.exp_pos _),
    Real.log_rpow (Real.exp_pos _), Real.log_exp, Real.log_exp]

/-- Galí (2015), eq. (13), p. 229, **exact form**: with `p_t = log P_t` the CPI of the
domestic and import price paths, CPI inflation is
`π_{t+1} = π_{H,t+1} + h(s_{t+1}) − h(s_t)`. -/
theorem cpi_inflation (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℕ → ℝ) (t : ℕ) :
    Real.log (cpi υ η (Real.exp (pH (t + 1))) (Real.exp (pF (t + 1))))
        - Real.log (cpi υ η (Real.exp (pH t)) (Real.exp (pF t)))
      = (pH (t + 1) - pH t)
        + (cpiGap υ η (pF (t + 1) - pH (t + 1)) - cpiGap υ η (pF t - pH t)) := by
  rw [log_cpi_eq hυ0 hυ1 hη1, log_cpi_eq hυ0 hυ1 hη1]
  ring

/-- Galí (2015), eq. (13), p. 229 (**first order**): the inflation gap
`(s_t, s_{t+1}) ↦ h(s_{t+1}) − h(s_t)` has derivative `υ (ds_{t+1} − ds_t)` at the steady
state, i.e. `π = π_H + υ Δs` to first order. -/
theorem hasFDerivAt_inflationGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    HasFDerivAt (fun x : ℝ × ℝ => cpiGap υ η x.2 - cpiGap υ η x.1)
      (υ • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)) (0, 0) := by
  have hd := hasDerivAt_cpiGap hυ0 hυ1 hη1
  have hs : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) :=
    hasFDerivAt_fst
  have h2 := hd.comp_hasFDerivAt ((0 : ℝ), (0 : ℝ)) hs
  have h1 := hd.comp_hasFDerivAt ((0 : ℝ), (0 : ℝ)) hf
  rw [smul_sub]
  exact h2.sub h1

/-- Galí (2015), eq. (13) and fn. 4, p. 229: **at `η = 1`**, exactly
`π_{t+1} = π_{H,t+1} + υ Δs_{t+1}`. -/
theorem cpi_inflation_cd (pH pF : ℕ → ℝ) (t : ℕ) :
    Real.log (cpiCD υ (Real.exp (pH (t + 1))) (Real.exp (pF (t + 1))))
        - Real.log (cpiCD υ (Real.exp (pH t)) (Real.exp (pF t)))
      = (pH (t + 1) - pH t) + υ * ((pF (t + 1) - pH (t + 1)) - (pF t - pH t)) := by
  rw [(log_cpiCD_eq _ _).1, (log_cpiCD_eq _ _).1]
  ring

/-- Galí (2015), eq. (14), p. 230: the law of one price `P_F = ℰ P*` gives
`s = log(P_F/P_H) = e + p* − p_H`. -/
theorem tot_lop {PH PF Ex Ps : ℝ} (hPH : 0 < PH) (hEx : 0 < Ex) (hPs : 0 < Ps)
    (hlop : PF = Ex * Ps) :
    Real.log (PF / PH) = Real.log Ex + Real.log Ps - Real.log PH := by
  rw [hlop, Real.log_div (by positivity) hPH.ne', Real.log_mul hEx.ne' hPs.ne']

/-- Galí (2015), p. 230: the log real exchange rate as a function of the terms of trade,
`g(s) = s − h(s)`. -/
noncomputable def rerGap (υ η s : ℝ) : ℝ := s - cpiGap υ η s

/-- Galí (2015), p. 230, **exact form**: with `𝒬 = P_F/P` (`= ℰP*/P` under the law of one
price), `q = p_F − p = s + p_H − p = s − h(s)`. -/
theorem rer_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℝ) :
    Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
        = (pF - pH) + pH - Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) ∧
      Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
        = rerGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 (Real.exp_pos pH) (Real.exp_pos pF)
  have h1 : Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
      = pF - Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) := by
    rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  refine ⟨by rw [h1]; ring, ?_⟩
  rw [h1, log_cpi_eq hυ0 hυ1 hη1, rerGap]
  ring

/-- Galí (2015), p. 230 (**first order**): `g(0) = 0` and `g'(0) = 1 − υ`, i.e.
`q = (1−υ)s` up to first order. -/
theorem hasDerivAt_rerGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    rerGap υ η 0 = 0 ∧ HasDerivAt (rerGap υ η) (1 - υ) 0 := by
  refine ⟨by rw [rerGap, cpiGap_zero hυ0 hυ1, sub_zero], ?_⟩
  exact (hasDerivAt_id' (0 : ℝ)).sub (hasDerivAt_cpiGap hυ0 hυ1 hη1)

/-- Galí (2015), p. 230: **at `η = 1` exactly** `q = s + p_H − p = (1−υ)s`. -/
theorem rer_cd (pH pF : ℝ) :
    Real.log (Real.exp pF / cpiCD υ (Real.exp pH) (Real.exp pF)) = (1 - υ) * (pF - pH) := by
  have hpos : 0 < cpiCD υ (Real.exp pH) (Real.exp pF) := by
    unfold cpiCD; positivity
  rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp, (log_cpiCD_eq _ _).1]
  ring

end Gali.OpenEconomy.Identities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Arrow securities, the stochastic discount factor and international risk sharing

Galí (2015), Chapter 8, §8.1.1 and §8.1.1.2, pp. 227–231: eqs. (8), (9), (10), fn. 3, (15),
(16), (17).

Uncertainty is modelled **state by state**, with no conditional-expectation operator in the
pricing conditions: at a node of the event tree the successor states form a finite set `ι`
with conditional probabilities `ξ j > 0`; an Arrow security `j` costs `V j` (domestic
currency) and pays one unit of domestic currency in state `j` only.

## Main results

* `periodUtility` (p. 227), `hasDerivAt_periodUtility`, `periodUtility_tangent`: the book's
  consumption utility `(C^{1−σ} − 1)/(1−σ)` (`log C` at `σ = 1`), with marginal utility
  `C^{−σ}` and the tangent (concavity) inequality.
* `arrow_foc_of_optimal` (eq. (8), **necessity by perturbation**): if a plan maximises
  `Z u(C) + β Σ_j ξ_j Z'_j u(C'_j)` subject to the budget `P C + Σ_j V_j D_j ≤ W`,
  `C'_j = (D_j + Y_j)/P'_j`, then `(V_j/P) Z C^{−σ} = ξ_j β Z'_j C'_j^{−σ}/P'_j` for every `j`.
* `optimal_of_arrow_foc` (sufficiency) and `arrow_optimal_iff`: with the budget binding,
  (8) for all `j` is necessary **and** sufficient for optimality.
* `arrow_sdf_iff` (eq. (9)): with `Q_{t,t+1} ≡ V/ξ` (fn. 3), (8) ⇔
  `β (C'/C)^{−σ} (Z'/Z)(P/P') = Q_{t,t+1}`; `portfolio_price` (fn. 3), `bond_price` and
  `bond_price_expectation` (eq. (10)).
* `foreign_optimal_iff`, `foreign_sdf_iff` (eq. (15)): the foreign household's problem and
  its Arrow condition `β (C*'/C*)^{−σ} (P*/P*')(ℰ/ℰ') = Q_{t,t+1}`.
* `riskSharing_ratio_const` (eq. (16)): if (9) and (15) hold at every date along every
  path, `C^{−σ} Z C*^σ 𝒬` is constant along every path (telescoping);
  `riskSharing` gives `C = ϑ C* Z^{1/σ} 𝒬^{1/σ}` and `vartheta_eq_one` gives `ϑ = 1` under
  symmetric initial conditions.
* `riskSharing_log` (eq. (17), first line), `riskSharing_log_tot` (general `η`:
  `c = y* + z/σ + g(s)/σ` with `g'(0) = 1 − υ`), `riskSharing_log_cd` (exact at `η = 1`).
-/

namespace Gali.OpenEconomy.RiskSharing

open Filter Topology Preferences Identities

/-! ### Period utility -/

/-- Galí (2015), p. 227: the consumption part of period utility,
`(C^{1−σ} − 1)/(1−σ)` for `σ ≠ 1` and `log C` for `σ = 1`. -/
noncomputable def periodUtility (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else (c ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 227: marginal utility of consumption is `C^{−σ}`. -/
theorem hasDerivAt_periodUtility (σ : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (periodUtility σ) (c ^ (-σ)) c := by
  by_cases hσ : σ = 1
  · have hfun : periodUtility σ = Real.log := funext fun x => by simp [periodUtility, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have hfun : periodUtility σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [periodUtility, hσ]
    rw [hfun]
    have hne : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
      (1 - σ)
    convert h using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), p. 227 (concavity of utility): the tangent inequality
`u(c) − u(c₀) ≤ c₀^{−σ}(c − c₀)` for `σ > 0`, `c, c₀ > 0`. -/
theorem periodUtility_tangent {σ c c₀ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hc₀ : 0 < c₀) :
    periodUtility σ c - periodUtility σ c₀ ≤ c₀ ^ (-σ) * (c - c₀) := by
  by_cases h1 : σ = 1
  · simp only [periodUtility, h1, ↓reduceIte, Real.rpow_neg_one]
    have := Real.log_le_sub_one_of_pos (div_pos hc hc₀)
    rw [Real.log_div hc.ne' hc₀.ne'] at this
    have e : c / c₀ - 1 = c₀⁻¹ * (c - c₀) := by field_simp
    linarith
  · simp only [periodUtility, h1, ↓reduceIte]
    have hr0 : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have key := rpow_tangent_le (r := 1 - σ) (u := c / c₀) (by linarith) hr0
      (div_pos hc hc₀).le (Or.inr (div_pos hc hc₀))
    have hcr : c ^ (1 - σ) = (c / c₀) ^ (1 - σ) * c₀ ^ (1 - σ) := by
      rw [Real.div_rpow hc.le hc₀.le]
      field_simp
    have hneg : c₀ ^ (-σ) = c₀ ^ (1 - σ) / c₀ := by
      rw [← Real.rpow_sub_one hc₀.ne']
      ring_nf
    have hpos : 0 < c₀ ^ (1 - σ) := Real.rpow_pos_of_pos hc₀ _
    have e1 : (c ^ (1 - σ) - 1) / (1 - σ) - (c₀ ^ (1 - σ) - 1) / (1 - σ)
        = c₀ ^ (1 - σ) * (((c / c₀) ^ (1 - σ) - 1) / (1 - σ)) := by
      rw [hcr]; field_simp; ring
    have e2 : c₀ ^ (-σ) * (c - c₀) = c₀ ^ (1 - σ) * (c / c₀ - 1) := by
      rw [hneg]; field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hpos.le

/-! ### The one-node portfolio problem: eq. (8) -/

variable {ι : Type*} [Fintype ι]

/-- Galí (2015), (1), (3), p. 226: the part of expected discounted utility affected by the
date-`t` choices at a node: `Z u(C) + β Σ_j ξ_j Z'_j u(C'_j)`, with next-period consumption
`C'_j = (D_j + Y_j)/P'_j` financed by the Arrow-security holdings `D_j` and other income
`Y_j` (wages, dividends, other assets) in state `j`. -/
noncomputable def nodeObjective (σ β Z : ℝ) (ξ Z' P' Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) : ℝ :=
  Z * periodUtility σ C + β * ∑ j, ξ j * (Z' j * periodUtility σ ((D j + Y j) / P' j))

/-- Galí (2015), eq. (3), p. 226: feasibility at the node — positive consumption now and
in every successor state, and the budget `P C + Σ_j V_j D_j ≤ W`. -/
def NodeFeasible (P W : ℝ) (V P' Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) : Prop :=
  0 < C ∧ (∀ j, 0 < (D j + Y j) / P' j) ∧ P * C + ∑ j, V j * D j ≤ W

/-- Galí (2015), eq. (8), p. 227: the Arrow-security optimality condition
`(V_j/P) Z C^{−σ} = ξ_j β Z'_j C'_j^{−σ} / P'_j`. -/
def ArrowFOC (σ β Z P : ℝ) (ξ Z' P' V Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) (j : ι) : Prop :=
  V j / P * (Z * C ^ (-σ)) = ξ j * β * (Z' j * ((D j + Y j) / P' j) ^ (-σ)) / P' j

/-- Galí (2015), eq. (8), p. 227 (**necessity, by perturbation**): if `(C, D)` maximises the
node objective over all feasible plans, then (8) holds for every Arrow security `j`. The
perturbation buys `x` more units of security `j` and finances it by consuming `V_j x/P`
less; it leaves the budget unchanged, so `x = 0` is a local maximum. -/
theorem arrow_foc_of_optimal {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hP : 0 < P) (hfeas : NodeFeasible P W V P' Y C D)
    (hopt : ∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
      nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D) (j : ι) :
    ArrowFOC σ β Z P ξ Z' P' V Y C D j := by
  classical
  obtain ⟨hC, hC', hbud⟩ := hfeas
  set φ : ℝ → ℝ := fun x => nodeObjective σ β Z ξ Z' P' Y (C - V j * x / P)
    (fun k => D k + if k = j then x else 0) with hφ
  have hφ0 : φ 0 = nodeObjective σ β Z ξ Z' P' Y C D := by
    simp [φ]
  -- feasibility of the perturbation near `x = 0`
  have hcont1 : ContinuousAt (fun x : ℝ => C - V j * x / P) 0 := by fun_prop
  have hcont2 : ContinuousAt (fun x : ℝ => (D j + x + Y j) / P' j) 0 := by fun_prop
  have hev1 : ∀ᶠ x in 𝓝 (0 : ℝ), (0 : ℝ) < C - V j * x / P := by
    have h0 : (0 : ℝ) < C - V j * 0 / P := by rw [mul_zero, zero_div, sub_zero]; exact hC
    exact hcont1.eventually (lt_mem_nhds h0)
  have hev2 : ∀ᶠ x in 𝓝 (0 : ℝ), (0 : ℝ) < (D j + x + Y j) / P' j := by
    have h0 : (0 : ℝ) < (D j + 0 + Y j) / P' j := by rw [add_zero]; exact hC' j
    exact hcont2.eventually (lt_mem_nhds h0)
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    rw [hφ0]
    refine hopt _ _ ⟨hx1, fun k => ?_, ?_⟩
    · by_cases hk : k = j
      · subst hk; simpa [add_right_comm] using hx2
      · simpa [hk] using hC' k
    · have hs : ∑ k, V k * (D k + if k = j then x else 0) = ∑ k, V k * D k + V j * x := by
        simp [mul_add, Finset.sum_add_distrib]
      rw [hs]
      have : P * (C - V j * x / P) = P * C - V j * x := by field_simp
      linarith
  -- the derivative of the perturbed objective at `0`
  have hd1 : HasDerivAt (fun x => periodUtility σ (C - V j * x / P))
      (C ^ (-σ) * (-(V j) / P)) 0 := by
    have hl : HasDerivAt (fun x : ℝ => C - V j * x / P) (-(V j) / P) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_mul (V j)).div_const P
      have := this.const_sub C
      convert this using 1
      ring
    have hy : C = C - V j * 0 / P := by rw [mul_zero, zero_div, sub_zero]
    exact HasDerivAt.comp_of_eq 0 (hasDerivAt_periodUtility σ hC) hl hy
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun x => ξ k * (Z' k * periodUtility σ ((D k + (if k = j then x else 0) + Y k) / P' k)))
      (if k = j then ξ j * (Z' j * (((D j + Y j) / P' j) ^ (-σ) * (1 / P' j))) else 0) 0 := by
    intro k _
    by_cases hk : k = j
    · subst hk
      simp only [↓reduceIte]
      have hl : HasDerivAt (fun x : ℝ => (D k + x + Y k) / P' k) (1 / P' k) 0 := by
        have := (((hasDerivAt_id' (0 : ℝ)).const_add (D k)).add_const (Y k)).div_const (P' k)
        simpa using this
      have hy : (D k + Y k) / P' k = (D k + 0 + Y k) / P' k := by rw [add_zero]
      have hc := HasDerivAt.comp_of_eq 0 (hasDerivAt_periodUtility σ (hC' k)) hl hy
      have hc2 := HasDerivAt.const_mul (Z' k) hc
      have hc3 := HasDerivAt.const_mul (ξ k) hc2
      simpa [Function.comp_def, mul_one_div] using hc3
    · simp only [hk, ↓reduceIte, add_zero]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum hterm
  rw [Finset.sum_ite_eq' Finset.univ j] at hsum
  simp only [Finset.mem_univ, ↓reduceIte] at hsum
  have hφd : HasDerivAt φ (Z * (C ^ (-σ) * (-(V j) / P)) +
      β * (ξ j * (Z' j * (((D j + Y j) / P' j) ^ (-σ) * (1 / P' j))))) 0 :=
    (hd1.const_mul Z).add (hsum.const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hφd
  unfold ArrowFOC
  have hP'j : P' j ≠ 0 := by
    intro h
    have := hC' j
    rw [h, div_zero] at this
    exact lt_irrefl 0 this
  field_simp at h0 ⊢
  linarith

/-- Galí (2015), eq. (8), p. 227 (**sufficiency**): if the budget binds and (8) holds for
every security, the plan maximises the node objective among all feasible plans
(`σ > 0`, positive `Z`, `P`, `P'`). -/
theorem optimal_of_arrow_foc {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hZ : 0 < Z) (hP : 0 < P) (hξ : ∀ j, 0 < ξ j)
    (hZ' : ∀ j, 0 < Z' j) (hP' : ∀ j, 0 < P' j)
    (hfeas : NodeFeasible P W V P' Y C D) (hbind : P * C + ∑ j, V j * D j = W)
    (hfoc : ∀ j, ArrowFOC σ β Z P ξ Z' P' V Y C D j) :
    ∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
      nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D := by
  intro C₂ D₂ ⟨hC₂, hC₂', hbud₂⟩
  obtain ⟨hC, hC', _⟩ := hfeas
  set m := Z * C ^ (-σ) / P with hm
  -- (8) rewritten: `β ξ_j Z'_j u'(C'_j) = m V_j P'_j`
  have hfoc' : ∀ j, β * (ξ j * (Z' j * ((D j + Y j) / P' j) ^ (-σ))) = m * V j * P' j := by
    intro j
    have h := hfoc j
    unfold ArrowFOC at h
    have hP'j := (hP' j).ne'
    rw [hm]
    field_simp at h ⊢
    linarith
  have hterm : ∀ j, β * (ξ j * (Z' j * periodUtility σ ((D₂ j + Y j) / P' j)))
      - β * (ξ j * (Z' j * periodUtility σ ((D j + Y j) / P' j)))
      ≤ m * V j * (D₂ j - D j) := by
    intro j
    have ht := periodUtility_tangent hσ (hC₂' j) (hC' j)
    have hw : 0 ≤ β * (ξ j * Z' j) := by
      have := hξ j; have := hZ' j; positivity
    have := mul_le_mul_of_nonneg_left ht hw
    have e : ((D₂ j + Y j) / P' j - (D j + Y j) / P' j) = (D₂ j - D j) / P' j := by
      field_simp; ring
    rw [e] at this
    have h8 := hfoc' j
    have hP'j := (hP' j).ne'
    have e2 : β * (ξ j * Z' j) * (((D j + Y j) / P' j) ^ (-σ) * ((D₂ j - D j) / P' j))
        = m * V j * (D₂ j - D j) := by
      rw [show β * (ξ j * Z' j) * (((D j + Y j) / P' j) ^ (-σ) * ((D₂ j - D j) / P' j))
        = β * (ξ j * (Z' j * ((D j + Y j) / P' j) ^ (-σ))) * (D₂ j - D j) / P' j by ring, h8]
      field_simp
    nlinarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [Finset.sum_sub_distrib] at hsum
  have h0 := periodUtility_tangent hσ hC₂ hC
  have hZm : Z * (C ^ (-σ) * (C₂ - C)) = m * (P * (C₂ - C)) := by rw [hm]; field_simp
  have hm0 : 0 ≤ m := by rw [hm]; have := Real.rpow_pos_of_pos hC (-σ); positivity
  have hS : ∑ j, m * V j * (D₂ j - D j) = m * (∑ j, V j * D₂ j - ∑ j, V j * D j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hS] at hsum
  have hzt := mul_le_mul_of_nonneg_left h0 hZ.le
  rw [hZm] at hzt
  have hbig : m * (P * (C₂ - C)) + m * (∑ j, V j * D₂ j - ∑ j, V j * D j) ≤ 0 := by
    have : P * (C₂ - C) + (∑ j, V j * D₂ j - ∑ j, V j * D j) ≤ 0 := by linarith
    nlinarith
  unfold nodeObjective
  rw [Finset.mul_sum, Finset.mul_sum]
  nlinarith

/-- Galí (2015), eq. (8), p. 227: for a feasible plan with a binding budget, **optimality is
equivalent to the Arrow-security condition (8) for every state**. -/
theorem arrow_optimal_iff {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hZ : 0 < Z) (hP : 0 < P) (hξ : ∀ j, 0 < ξ j)
    (hZ' : ∀ j, 0 < Z' j) (hP' : ∀ j, 0 < P' j)
    (hfeas : NodeFeasible P W V P' Y C D) (hbind : P * C + ∑ j, V j * D j = W) :
    (∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
        nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D) ↔
      ∀ j, ArrowFOC σ β Z P ξ Z' P' V Y C D j :=
  ⟨fun hopt => arrow_foc_of_optimal hP hfeas hopt,
    fun hfoc => optimal_of_arrow_foc hσ hβ hZ hP hξ hZ' hP' hfeas hbind hfoc⟩

/-! ### The stochastic discount factor: eqs. (9), (10) and fn. 3 -/

/-- Galí (2015), eq. (9), p. 228: with the stochastic discount factor `Q_{t,t+1} ≡ V/ξ`
(fn. 3), condition (8) is equivalent to `β (C'/C)^{−σ} (Z'/Z) (P/P') = Q_{t,t+1}`. -/
theorem arrow_sdf_iff {σ β Z Z' P P' C C' V ξ : ℝ} (hZ : 0 < Z) (hP : 0 < P)
    (hP' : 0 < P') (hC : 0 < C) (hC' : 0 < C') (hξ : 0 < ξ) :
    V / P * (Z * C ^ (-σ)) = ξ * β * (Z' * C' ^ (-σ)) / P' ↔
      β * (C' / C) ^ (-σ) * (Z' / Z) * (P / P') = V / ξ := by
  rw [Real.div_rpow hC'.le hC.le]
  have ha := Real.rpow_pos_of_pos hC (-σ)
  have hb := Real.rpow_pos_of_pos hC' (-σ)
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Galí (2015), fn. 3, p. 228: under complete markets a portfolio paying `D_j` in state `j`
costs `Σ_j V_j D_j = Σ_j ξ_j Q_j D_j`, the conditional expectation `E_t{Q_{t,t+1} D_{t+1}}`. -/
theorem portfolio_price (ξ V D : ι → ℝ) (hξ : ∀ j, 0 < ξ j) :
    ∑ j, V j * D j = ∑ j, ξ j * (V j / ξ j * D j) :=
  Finset.sum_congr rfl fun j _ => by field_simp [(hξ j).ne']

/-- Galí (2015), eq. (10), p. 228: the riskless bond (one unit of domestic currency in every
state) costs `Q_t = Σ_j V_j = E_t{Q_{t,t+1}}`, and under (9) in every state
`Q_t = β E_t{(C'/C)^{−σ}(Z'/Z)(P/P')}`. -/
theorem bond_price {σ β Z P C : ℝ} {ξ Z' P' C' V : ι → ℝ} (hξ : ∀ j, 0 < ξ j)
    (h9 : ∀ j, β * (C' j / C) ^ (-σ) * (Z' j / Z) * (P / P' j) = V j / ξ j) :
    ∑ j, V j = ∑ j, ξ j * (V j / ξ j) ∧
      ∑ j, V j = β * ∑ j, ξ j * ((C' j / C) ^ (-σ) * (Z' j / Z) * (P / P' j)) := by
  have h1 : ∑ j, V j = ∑ j, ξ j * (V j / ξ j) :=
    Finset.sum_congr rfl fun j _ => by field_simp [(hξ j).ne']
  refine ⟨h1, ?_⟩
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h9 j]
  ring

/-- Galí (2015), eq. (10), p. 228, for an arbitrary expectation system: if (9) holds in every
state, `Q_{t,t+1} = β M_{t+1}` with `M` the nominal marginal rate of substitution, then
`Q_t ≡ E_t{Q_{t,t+1}} = β E_t{M_{t+1}}`. -/
theorem bond_price_expectation {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β : ℝ}
    {Qtt1 M : ℕ → Ω → ℝ} (h9 : ∀ t, Qtt1 t = β • M t) (t : ℕ) :
    𝔼.E t (Qtt1 t) = β • 𝔼.E t (M t) := by
  rw [h9, map_smul]

/-! ### The foreign household: eq. (15) -/

/-- Galí (2015), p. 230: the foreign household's problem is the node problem in domestic
currency with price level `ℰP*`, next-period price `ℰ'_j P*'_j` and no preference shock;
its optimum is characterised by its Arrow condition (necessity and sufficiency). -/
theorem foreign_optimal_iff {σ β Ex Ps W : ℝ} {ξ Exn Psn V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hEx : 0 < Ex) (hPs : 0 < Ps) (hξ : ∀ j, 0 < ξ j)
    (hP' : ∀ j, 0 < Exn j * Psn j)
    (hfeas : NodeFeasible (Ex * Ps) W V (fun j => Exn j * Psn j) Y C D)
    (hbind : Ex * Ps * C + ∑ j, V j * D j = W) :
    (∀ C₂ D₂, NodeFeasible (Ex * Ps) W V (fun j => Exn j * Psn j) Y C₂ D₂ →
        nodeObjective σ β 1 ξ (fun _ => 1) (fun j => Exn j * Psn j) Y C₂ D₂
          ≤ nodeObjective σ β 1 ξ (fun _ => 1) (fun j => Exn j * Psn j) Y C D) ↔
      ∀ j, ArrowFOC σ β 1 (Ex * Ps) ξ (fun _ => 1) (fun j => Exn j * Psn j) V Y C D j :=
  arrow_optimal_iff hσ hβ one_pos (mul_pos hEx hPs) hξ (fun _ => one_pos) hP' hfeas hbind

/-- Galí (2015), eq. (15), p. 230: the foreign Arrow condition
`(V/(ℰP*)) C*^{−σ} = ξ β C*'^{−σ}/(ℰ'P*')` is equivalent to
`β (C*'/C*)^{−σ} (P*/P*') (ℰ/ℰ') = Q_{t,t+1}`. -/
theorem foreign_sdf_iff {σ β Ex Exn Ps Psn Cs Csn V ξ : ℝ} (hEx : 0 < Ex) (hExn : 0 < Exn)
    (hPs : 0 < Ps) (hPsn : 0 < Psn) (hCs : 0 < Cs) (hCsn : 0 < Csn) (hξ : 0 < ξ) :
    V / (Ex * Ps) * (1 * Cs ^ (-σ)) = ξ * β * (1 * Csn ^ (-σ)) / (Exn * Psn) ↔
      β * (Csn / Cs) ^ (-σ) * (Ps / Psn) * (Ex / Exn) = V / ξ := by
  rw [arrow_sdf_iff one_pos (mul_pos hEx hPs) (mul_pos hExn hPsn) hCs hCsn hξ]
  have : β * (Csn / Cs) ^ (-σ) * (1 / 1) * (Ex * Ps / (Exn * Psn))
      = β * (Csn / Cs) ^ (-σ) * (Ps / Psn) * (Ex / Exn) := by
    field_simp
  rw [this]

/-! ### International risk sharing: eqs. (16) and (17) -/

variable {Ω : Type*}

/-- Galí (2015), (16), p. 231: the risk-sharing ratio `C^{−σ} Z C*^{σ} 𝒬` with the real
exchange rate `𝒬 = ℰP*/P`. -/
noncomputable def rsRatio (σ : ℝ) (C Z Cs P Ps Ex : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  C t ω ^ (-σ) * Z t ω * Cs t ω ^ σ * (Ex t ω * Ps t ω / P t ω)

/-- Galí (2015), eq. (16), p. 231 (**telescoping**): if the domestic condition (9) and the
foreign condition (15) price the same Arrow securities at every date along every path `ω`,
the ratio `C^{−σ} Z C*^{σ} 𝒬` is constant along every path. -/
theorem riskSharing_ratio_const {σ β : ℝ} {C Z P Cs Ps Ex Q : ℕ → Ω → ℝ} (hβ : 0 < β)
    (hC : ∀ t ω, 0 < C t ω) (hZ : ∀ t ω, 0 < Z t ω) (hP : ∀ t ω, 0 < P t ω)
    (hCs : ∀ t ω, 0 < Cs t ω) (hPs : ∀ t ω, 0 < Ps t ω) (hEx : ∀ t ω, 0 < Ex t ω)
    (h9 : ∀ t ω, β * (C (t + 1) ω / C t ω) ^ (-σ) * (Z (t + 1) ω / Z t ω) *
      (P t ω / P (t + 1) ω) = Q t ω)
    (h15 : ∀ t ω, β * (Cs (t + 1) ω / Cs t ω) ^ (-σ) * (Ps t ω / Ps (t + 1) ω) *
      (Ex t ω / Ex (t + 1) ω) = Q t ω) :
    ∀ t ω, rsRatio σ C Z Cs P Ps Ex t ω = rsRatio σ C Z Cs P Ps Ex 0 ω := by
  intro t ω
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← ih]
    have h := (h9 t ω).trans (h15 t ω).symm
    have hc0 := hC t ω; have hc1 := hC (t + 1) ω
    have hs0 := hCs t ω; have hs1 := hCs (t + 1) ω
    have hz0 := hZ t ω; have hz1 := hZ (t + 1) ω
    have hp0 := hP t ω; have hp1 := hP (t + 1) ω
    have hq0 := hPs t ω; have hq1 := hPs (t + 1) ω
    have he0 := hEx t ω; have he1 := hEx (t + 1) ω
    rw [Real.div_rpow hc1.le hc0.le, Real.div_rpow hs1.le hs0.le] at h
    have a0 := Real.rpow_pos_of_pos hc0 (-σ); have a1 := Real.rpow_pos_of_pos hc1 (-σ)
    have b0 := Real.rpow_pos_of_pos hs0 (-σ); have b1 := Real.rpow_pos_of_pos hs1 (-σ)
    have g0 : Cs t ω ^ σ = (Cs t ω ^ (-σ))⁻¹ := by rw [Real.rpow_neg hs0.le, inv_inv]
    have g1 : Cs (t + 1) ω ^ σ = (Cs (t + 1) ω ^ (-σ))⁻¹ := by
      rw [Real.rpow_neg hs1.le, inv_inv]
    unfold rsRatio
    rw [g0, g1]
    set x0 := C t ω ^ (-σ); set x1 := C (t + 1) ω ^ (-σ)
    set y0 := Cs t ω ^ (-σ); set y1 := Cs (t + 1) ω ^ (-σ)
    have h' : x1 / x0 * (Z (t + 1) ω / Z t ω) * (P t ω / P (t + 1) ω)
        = y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω) := by
      have := mul_left_cancel₀ hβ.ne' (by simpa only [mul_assoc] using h)
      simpa only [mul_assoc] using this
    have hB : 0 < y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω) := by positivity
    have key : x1 * Z (t + 1) ω * y1⁻¹ * (Ex (t + 1) ω * Ps (t + 1) ω / P (t + 1) ω)
        = x0 * Z t ω * y0⁻¹ * (Ex t ω * Ps t ω / P t ω)
          * (x1 / x0 * (Z (t + 1) ω / Z t ω) * (P t ω / P (t + 1) ω))
          / (y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω)) := by
      field_simp
    rw [key, h', mul_div_assoc, div_self hB.ne', mul_one]

/-- Galí (2015), eq. (16), p. 231: the constant `ϑ = R_0^{−1/σ}` determined by initial
conditions, `R_0` the initial risk-sharing ratio. -/
noncomputable def vartheta (σ : ℝ) (C Z Cs P Ps Ex : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  rsRatio σ C Z Cs P Ps Ex 0 ω ^ (-1 / σ)

/-- Galí (2015), eq. (16), p. 231: from a constant ratio, `C = ϑ C* Z^{1/σ} 𝒬^{1/σ}` at every
date along every path (`σ > 0`). -/
theorem riskSharing {σ : ℝ} (hσ : 0 < σ) {C Z P Cs Ps Ex : ℕ → Ω → ℝ}
    (hC : ∀ t ω, 0 < C t ω) (hZ : ∀ t ω, 0 < Z t ω) (hP : ∀ t ω, 0 < P t ω)
    (hCs : ∀ t ω, 0 < Cs t ω) (hPs : ∀ t ω, 0 < Ps t ω) (hEx : ∀ t ω, 0 < Ex t ω)
    (hconst : ∀ t ω, rsRatio σ C Z Cs P Ps Ex t ω = rsRatio σ C Z Cs P Ps Ex 0 ω) (t : ℕ)
    (ω : Ω) :
    C t ω = vartheta σ C Z Cs P Ps Ex ω * Cs t ω * Z t ω ^ (1 / σ) *
      (Ex t ω * Ps t ω / P t ω) ^ (1 / σ) := by
  have hc := hC t ω; have hz := hZ t ω; have hs := hCs t ω
  have hq : 0 < Ex t ω * Ps t ω / P t ω := by
    have := hEx t ω; have := hPs t ω; have := hP t ω; positivity
  unfold vartheta
  rw [← hconst t ω, rsRatio]
  set q := Ex t ω * Ps t ω / P t ω
  have hσ0 : σ ≠ 0 := hσ.ne'
  rw [Real.mul_rpow (by positivity) hq.le, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hz.le, ← Real.rpow_mul hc.le, ← Real.rpow_mul hs.le]
  have e1 : -σ * (-1 / σ) = 1 := by field_simp
  have e2 : σ * (-1 / σ) = -1 := by field_simp
  rw [e1, e2, Real.rpow_one, Real.rpow_neg_one]
  have hz1 : Z t ω ^ (-1 / σ) * Z t ω ^ (1 / σ) = 1 := by
    rw [← Real.rpow_add hz, show -1 / σ + 1 / σ = (0 : ℝ) by ring, Real.rpow_zero]
  have hq1 : q ^ (-1 / σ) * q ^ (1 / σ) = 1 := by
    rw [← Real.rpow_add hq, show -1 / σ + 1 / σ = (0 : ℝ) by ring, Real.rpow_zero]
  symm
  calc _ = C t ω * ((Cs t ω)⁻¹ * Cs t ω) * (Z t ω ^ (-1 / σ) * Z t ω ^ (1 / σ))
        * (q ^ (-1 / σ) * q ^ (1 / σ)) := by ring
    _ = C t ω := by rw [inv_mul_cancel₀ hs.ne', hz1, hq1]; ring

/-- Galí (2015), p. 231: under symmetric initial conditions (`C_0 = C*_0`, `Z_0 = 1`,
`𝒬_0 = 1`), `ϑ = 1`. -/
theorem vartheta_eq_one {σ : ℝ} {C Z P Cs Ps Ex : ℕ → Ω → ℝ} {ω : Ω} (hC0 : 0 < C 0 ω)
    (hsym : Cs 0 ω = C 0 ω) (hZ0 : Z 0 ω = 1) (hQ0 : Ex 0 ω * Ps 0 ω / P 0 ω = 1) :
    vartheta σ C Z Cs P Ps Ex ω = 1 := by
  unfold vartheta rsRatio
  rw [hsym, hZ0, hQ0, mul_one, mul_one, ← Real.rpow_add hC0, neg_add_cancel, Real.rpow_zero,
    Real.one_rpow]

/-- Galí (2015), eq. (17), p. 231 (first line): with `ϑ = 1` and `C* = Y*`,
`C = Y* Z^{1/σ} 𝒬^{1/σ}` gives `c = y* + (1/σ)(z + q)`. -/
theorem riskSharing_log {σ C Ys Z Qr : ℝ} (hYs : 0 < Ys) (hZ : 0 < Z) (hQr : 0 < Qr)
    (h16 : C = Ys * Z ^ (1 / σ) * Qr ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * (Real.log Z + Real.log Qr) := by
  rw [h16, Real.log_mul (by positivity) (by positivity), Real.log_mul hYs.ne' (by positivity),
    Real.log_rpow hZ, Real.log_rpow hQr]
  ring

/-- Galí (2015), eq. (17), p. 231 (second line, **general `η`**): with the law of one price
`ℰP* = P_F` and the CES CPI, `c = y* + z/σ + g(s)/σ` where `g(s) = s − h(s)` satisfies
`g(0) = 0`, `g'(0) = 1 − υ` (`Identities.hasDerivAt_rerGap`): the second line of (17) holds
to first order. -/
theorem riskSharing_log_tot {υ η σ C Ys Z pH pF : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1)
    (hη1 : η ≠ 1) (hYs : 0 < Ys) (hZ : 0 < Z)
    (h16 : C = Ys * Z ^ (1 / σ) *
      (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF)) ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * Real.log Z + 1 / σ * rerGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 (Real.exp_pos pH) (Real.exp_pos pF)
  rw [riskSharing_log hYs hZ (div_pos (Real.exp_pos _) hpos) h16,
    (rer_eq hυ0 hυ1 hη1 pH pF).2]
  ring

/-- Galí (2015), eq. (17), p. 231, **exact at `η = 1`**:
`c = y* + z/σ + ((1−υ)/σ) s`. -/
theorem riskSharing_log_cd {υ σ C Ys Z pH pF : ℝ} (hYs : 0 < Ys) (hZ : 0 < Z)
    (h16 : C = Ys * Z ^ (1 / σ) *
      (Real.exp pF / cpiCD υ (Real.exp pH) (Real.exp pF)) ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * Real.log Z + (1 - υ) / σ * (pF - pH) := by
  have hpos : 0 < cpiCD υ (Real.exp pH) (Real.exp pF) := by unfold cpiCD; positivity
  rw [riskSharing_log hYs hZ (div_pos (Real.exp_pos _) hpos) h16, rer_cd]
  ring

end Gali.OpenEconomy.RiskSharing

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Uncovered interest parity and the terms of trade

Galí (2015), Chapter 8, §8.1.1.3, pp. 231–232: the exact UIP condition, eqs. (18), (19),
(20), fn. 5 and the closing remark of p. 232.

## Main results

* `uip_exact` (p. 231): from the bond-pricing equations `Q_t = E_t{Q_{t,t+1}}` and
  `ℰ_t Q*_t = E_t{Q_{t,t+1} ℰ_{t+1}}`, `E_t{Q_{t,t+1}[e^{i_t} − e^{i*_t} ℰ_{t+1}/ℰ_t]} = 0`.
* `uip_node_iff`, `uipGap_zero`, `hasFDerivAt_uipGap` (eq. (18) as an **exact derivative**):
  at a node with finitely many successor states, the exact condition is equivalent to
  `i − i* = G(q̂, Δe)` with `G` an explicit function of the SDF deviations `q̂_j` and the
  depreciations `Δe_j`; `G(0) = 0` and `DG(0)(dq̂, dΔe) = Σ_j ξ_j dΔe_j = E_t{dΔe}`, i.e.
  `i = i* + E_tΔe_{t+1}` to first order — the second-moment (risk-premium) terms are what the
  first-order approximation drops. `uipGap_const`: with no exchange-rate risk it is exact.
* `tot_difference` (eq. (19)): (14) and (18) give
  `s_t = (i*_t − E_tπ*_{t+1}) − (i_t − E_tπ_{H,t+1}) + E_t s_{t+1}`.
* `tot_forward` (eq. (20)): given `lim_T E_t s_T = 0` (**stated as a hypothesis**, see
  `forward_iff`), the partial sums of `E_t[(i*_{t+k} − π*_{t+k+1}) − (i_{t+k} − π_{H,t+k+1})]`
  converge to `s_t`; `forward_iff`: given (19), the representation holds iff the limit
  condition does; `forward_counterexample`: without it (20) fails.
* `tot_difference_of_eulers` (p. 232): (19) follows from the domestic Euler equation (11), the
  world Euler equation, risk sharing (17), the CPI identity (13) and `E_t z_{t+1} = ρ_z z_t`.
-/

namespace Gali.OpenEconomy.UIP

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The exact UIP condition -/

/-- Galí (2015), p. 231 (**exact UIP**): if the domestic bond price is
`e^{−i_t} = E_t{Q_{t,t+1}}` and the foreign-currency bond satisfies
`ℰ_t e^{−i*_t} = E_t{Q_{t,t+1} ℰ_{t+1}}`, and `e^{i_t}`, `e^{i*_t}/ℰ_t` are known at `t`, then
`E_t{Q_{t,t+1}[e^{i_t} − e^{i*_t} ℰ_{t+1}/ℰ_t]} = 0`. -/
theorem uip_exact (hpull : 𝔼.PullOut) {Q i is Ex : ℕ → Ω → ℝ} (t : ℕ)
    (hEx : ∀ ω, 0 < Ex t ω)
    (hdom : ∀ ω, Real.exp (-(i t ω)) = 𝔼.E t (Q t) ω)
    (hfor : ∀ ω, Ex t ω * Real.exp (-(is t ω)) = 𝔼.E t (Q t * Ex (t + 1)) ω)
    (hk1 : 𝔼.E t (fun ω => Real.exp (i t ω)) = fun ω => Real.exp (i t ω))
    (hk2 : 𝔼.E t (fun ω => Real.exp (is t ω) / Ex t ω) = fun ω => Real.exp (is t ω) / Ex t ω) :
    𝔼.E t (fun ω => Q t ω * (Real.exp (i t ω) - Real.exp (is t ω) * Ex (t + 1) ω / Ex t ω))
      = 0 := by
  have hfun : (fun ω => Q t ω * (Real.exp (i t ω) - Real.exp (is t ω) * Ex (t + 1) ω / Ex t ω))
      = (fun ω => Real.exp (i t ω)) * Q t
        - (fun ω => Real.exp (is t ω) / Ex t ω) * (Q t * Ex (t + 1)) := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun, map_sub, hpull t _ _ hk1, hpull t _ _ hk2]
  funext ω
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]
  rw [← hdom ω, ← hfor ω, ← Real.exp_add]
  have := hEx ω
  field_simp
  rw [← Real.exp_add]
  simp

/-! ### Eq. (18) as an exact derivative at a node -/

variable {ι : Type*} [Fintype ι]

/-- Galí (2015), eq. (18), p. 232: the exact interest differential at a node,
`G(q̂, Δe) = log Σ_j ξ_j e^{q̂_j + Δe_j} − log Σ_j ξ_j e^{q̂_j}`, where `Q_{t,t+1}(j) = Q̄ e^{q̂_j}`
and `Δe_j = log(ℰ_{t+1}(j)/ℰ_t)`. -/
noncomputable def uipGap (ξ : ι → ℝ) (x : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  Real.log (∑ j, ξ j * Real.exp (x.1 j + x.2 j)) - Real.log (∑ j, ξ j * Real.exp (x.1 j))

/-- Galí (2015), p. 231–232: at a node with successor probabilities `ξ_j > 0`, the exact UIP
condition `Σ_j ξ_j Q_j (e^{i} − e^{i*} e^{Δe_j}) = 0` (with `Q_j = Q̄ e^{q̂_j}`, `Q̄ > 0`) holds
**iff** `i − i* = G(q̂, Δe)`. -/
theorem uip_node_iff [Nonempty ι] {ξ : ι → ℝ} (hξ : ∀ j, 0 < ξ j) {Qbar i is : ℝ}
    (hQ : 0 < Qbar) (q de : ι → ℝ) :
    ∑ j, ξ j * (Qbar * Real.exp (q j) * (Real.exp i - Real.exp is * Real.exp (de j))) = 0 ↔
      i - is = uipGap ξ (q, de) := by
  have hA : 0 < ∑ j, ξ j * Real.exp (q j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have hB : 0 < ∑ j, ξ j * Real.exp (q j + de j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have hsum : ∑ j, ξ j * (Qbar * Real.exp (q j) * (Real.exp i - Real.exp is * Real.exp (de j)))
      = Qbar * (Real.exp i * ∑ j, ξ j * Real.exp (q j)
        - Real.exp is * ∑ j, ξ j * Real.exp (q j + de j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]
    ring
  rw [hsum, uipGap]
  simp only
  constructor
  · intro h
    have h1 : Real.exp i * ∑ j, ξ j * Real.exp (q j)
        = Real.exp is * ∑ j, ξ j * Real.exp (q j + de j) := by
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hQ.ne'
      · linarith
    have h2 := congrArg Real.log h1
    rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_mul (Real.exp_pos _).ne' hB.ne',
      Real.log_exp, Real.log_exp] at h2
    linarith
  · intro h
    have h1 : Real.exp i * ∑ j, ξ j * Real.exp (q j)
        = Real.exp is * ∑ j, ξ j * Real.exp (q j + de j) := by
      have h3 : i + Real.log (∑ j, ξ j * Real.exp (q j))
          = is + Real.log (∑ j, ξ j * Real.exp (q j + de j)) := by linarith
      have h4 := congrArg Real.exp h3
      rwa [Real.exp_add, Real.exp_add, Real.exp_log hA, Real.exp_log hB] at h4
    rw [h1, sub_self, mul_zero]

/-- Galí (2015), eq. (18), p. 232: at the deterministic steady state (`q̂ = 0`, `Δe = 0`) the
interest differential is zero, `G(0) = 0` (probabilities summing to one). -/
theorem uipGap_zero {ξ : ι → ℝ} (hsum : ∑ j, ξ j = 1) : uipGap ξ 0 = 0 := by
  simp [uipGap, hsum]

/-- Galí (2015), eq. (18), p. 232, with **no exchange-rate risk** (`Δe_j = d` in every state):
`G(q̂, Δe) = d`, so `i = i* + Δe_{t+1}` holds exactly whatever the SDF. -/
theorem uipGap_const [Nonempty ι] {ξ : ι → ℝ} (hξ : ∀ j, 0 < ξ j) (q : ι → ℝ) (d : ℝ) :
    uipGap ξ (q, fun _ => d) = d := by
  have hA : 0 < ∑ j, ξ j * Real.exp (q j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have : ∑ j, ξ j * Real.exp (q j + d) = Real.exp d * ∑ j, ξ j * Real.exp (q j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]; ring
  simp only [uipGap]
  rw [this, Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp]
  ring

/-- Galí (2015), eq. (18): the expectation functional `(dq̂, dΔe) ↦ Σ_j ξ_j dΔe_j`
(`E_t` of the depreciation perturbation) as a continuous linear map. -/
noncomputable def expectDe (ξ : ι → ℝ) : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, ξ j • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))

/-- Galí (2015), eq. (18): `expectDe ξ (dq̂, dΔe) = Σ_j ξ_j dΔe_j`. -/
theorem expectDe_apply (ξ : ι → ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    expectDe ξ v = ∑ j, ξ j * v.2 j := by
  simp [expectDe]

/-- Galí (2015), eq. (18), p. 232 (**log-linear UIP as an exact derivative**): at the
deterministic steady state the interest differential `G` has Fréchet derivative
`(dq̂, dΔe) ↦ Σ_j ξ_j dΔe_j = E_t{dΔe_{t+1}}`: to first order `i_t = i*_t + E_tΔe_{t+1}`, the
SDF perturbation `dq̂` dropping out. -/
theorem hasFDerivAt_uipGap {ξ : ι → ℝ} (hsum : ∑ j, ξ j = 1) :
    HasFDerivAt (uipGap ξ) (expectDe ξ) 0 := by
  classical
  set p1 : ι → (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))
  set p2 : ι → (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))
  have hB : HasFDerivAt (fun x : (ι → ℝ) × (ι → ℝ) => ∑ j, ξ j * Real.exp (x.1 j + x.2 j))
      (∑ j, ξ j • (Real.exp (0 + 0) • (p1 j + p2 j))) 0 := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h := ((((p1 j).hasFDerivAt (x := 0)).add
      ((p2 j).hasFDerivAt (x := 0))).exp).const_mul (ξ j)
    simpa [p1, p2] using h
  have hA : HasFDerivAt (fun x : (ι → ℝ) × (ι → ℝ) => ∑ j, ξ j * Real.exp (x.1 j))
      (∑ j, ξ j • (Real.exp 0 • p1 j)) 0 := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h := (((p1 j).hasFDerivAt (x := 0)).exp).const_mul (ξ j)
    simpa [p1] using h
  have hB0 : (∑ j, ξ j * Real.exp ((0 : (ι → ℝ) × (ι → ℝ)).1 j + (0 : (ι → ℝ) × (ι → ℝ)).2 j))
      = 1 := by simp [hsum]
  have hA0 : (∑ j, ξ j * Real.exp ((0 : (ι → ℝ) × (ι → ℝ)).1 j)) = 1 := by simp [hsum]
  have hlogB := hB.log (by rw [hB0]; exact one_ne_zero)
  have hlogA := hA.log (by rw [hA0]; exact one_ne_zero)
  rw [hB0, inv_one, one_smul] at hlogB
  rw [hA0, inv_one, one_smul] at hlogA
  have hd := hlogB.sub hlogA
  refine hd.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [expectDe, Real.exp_zero, add_zero, one_smul, _root_.sub_apply, p1, p2]
  simp only [FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Eqs. (19) and (20) -/

/-- Galí (2015), eq. (19), p. 232: combining the law of one price (14),
`s_t = e_t + p*_t − p_{H,t}`, with UIP (18), `i_t = i*_t + E_t e_{t+1} − e_t`, gives
`s_t = (i*_t − E_tπ*_{t+1}) − (i_t − E_tπ_{H,t+1}) + E_t s_{t+1}`
(with `p*`, `p_H` known at `t`). -/
theorem tot_difference {s e ps pH i is : ℕ → Ω → ℝ} (t : ℕ)
    (h14 : ∀ t ω, s t ω = e t ω + ps t ω - pH t ω)
    (h18 : ∀ ω, i t ω = is t ω + (𝔼.E t (e (t + 1)) ω - e t ω))
    (hps : 𝔼.E t (ps t) = ps t) (hpH : 𝔼.E t (pH t) = pH t) (ω : Ω) :
    s t ω = (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω) - (i t ω - 𝔼.E t (pH (t + 1) - pH t) ω)
      + 𝔼.E t (s (t + 1)) ω := by
  have hs1 : s (t + 1) = e (t + 1) + ps (t + 1) - pH (t + 1) := funext fun ω => h14 (t + 1) ω
  rw [hs1]
  simp only [map_sub, map_add, hps, hpH, Pi.add_apply, Pi.sub_apply]
  rw [h14 t ω, h18 ω]
  ring

/-- Galí (2015), (20), p. 232: iterating `s_t = d_t + E_t s_{t+1}` forward,
`s_t = Σ_{k<T} E_t d_{t+k} + E_t s_{t+T}` for every horizon `T`. -/
theorem forward_partial {s d : ℕ → Ω → ℝ} (hs : ∀ t, s t = d t + 𝔼.E t (s (t + 1)))
    (hadapt : ∀ t, 𝔼.E t (s t) = s t) (t T : ℕ) :
    s t = ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) + 𝔼.E t (s (t + T)) := by
  induction T with
  | zero => simp [hadapt t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [hs (t + T), map_add, 𝔼.tower (Nat.le_add_right t T), ← add_assoc]

/-- Galí (2015), eq. (20) and fn. 5, p. 232: given (19) in the form `s_t = d_t + E_t s_{t+1}`,
the forward representation `s_t = lim_T Σ_{k<T} E_t d_{t+k}` holds **iff**
`lim_T E_t s_T = 0`. -/
theorem forward_iff {s d : ℕ → Ω → ℝ} (hs : ∀ t, s t = d t + 𝔼.E t (s (t + 1)))
    (hadapt : ∀ t, 𝔼.E t (s t) = s t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) ω) atTop (𝓝 (s t ω)) ↔
      Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0) := by
  have hp : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) ω
      = s t ω - 𝔼.E t (s (t + T)) ω := fun T => by
    have := congrFun (forward_partial 𝔼 hs hadapt t T) ω
    simp only [Pi.add_apply] at this
    rw [Finset.sum_apply] at this
    linarith
  simp_rw [hp]
  have hshift : Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0) ↔
      Tendsto (fun T => 𝔼.E t (s (t + T)) ω) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat t]
    simp only [add_comm]
  rw [hshift]
  constructor
  · intro h
    have := (tendsto_const_nhds (x := s t ω)).sub h
    simpa using this
  · intro h
    have := (tendsto_const_nhds (x := s t ω)).sub h
    simpa using this

/-- Galí (2015), eq. (20), p. 232 (**forward solution**): under (14), (18) and the
**hypothesis** `lim_{T→∞} E_t s_T = 0` (fn. 5; not derived), the terms of trade equal the
limit of the partial sums of expected real-rate differentials,
`s_t = lim_T Σ_{k<T} E_t[(i*_{t+k} − π*_{t+k+1}) − (i_{t+k} − π_{H,t+k+1})]`.
(The book writes `E_t Σ_k`; the statement is the sum of conditional expectations, which needs
no interchange of `E_t` and an infinite sum.) -/
theorem tot_forward {s e ps pH i is : ℕ → Ω → ℝ}
    (h14 : ∀ t ω, s t ω = e t ω + ps t ω - pH t ω)
    (h18 : ∀ t ω, i t ω = is t ω + (𝔼.E t (e (t + 1)) ω - e t ω))
    (hps : ∀ t, 𝔼.E t (ps t) = ps t) (hpH : ∀ t, 𝔼.E t (pH t) = pH t)
    (hs : ∀ t, 𝔼.E t (s t) = s t) (t : ℕ) (ω : Ω)
    (hlim : Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (fun ω' =>
        (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
          - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω'))) ω)
      atTop (𝓝 (s t ω)) := by
  set d : ℕ → Ω → ℝ := fun u ω' => (is u ω' - 𝔼.E u (ps (u + 1) - ps u) ω')
    - (i u ω' - 𝔼.E u (pH (u + 1) - pH u) ω') with hd
  have hrec : ∀ u, s u = d u + 𝔼.E u (s (u + 1)) := fun u => by
    funext ω'
    rw [Pi.add_apply, tot_difference 𝔼 u h14 (h18 u) (hps u) (hpH u) ω']
  have hEd : ∀ k, 𝔼.E t (d (t + k)) = 𝔼.E t (fun ω' =>
      (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
        - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω'))) := by
    intro k
    have hle : t ≤ t + k := Nat.le_add_right t k
    have e1 : d (t + k) = is (t + k) - 𝔼.E (t + k) (ps (t + k + 1) - ps (t + k))
        - (i (t + k) - 𝔼.E (t + k) (pH (t + k + 1) - pH (t + k))) := rfl
    have e2 : (fun ω' => (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
        - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω')))
        = is (t + k) - (ps (t + k + 1) - ps (t + k))
          - (i (t + k) - (pH (t + k + 1) - pH (t + k))) := rfl
    rw [e1, e2]
    simp only [map_sub, 𝔼.tower hle]
  have := (forward_iff 𝔼 hrec hs t ω).2 hlim
  simpa only [hEd] using this

/-- Galí (2015), eq. (20) and fn. 5: **the limit hypothesis cannot be dropped**. Under perfect
foresight `s ≡ 1`, `d ≡ 0` satisfies `s_t = d_t + E_t s_{t+1}`, yet the forward sums (all zero)
do not converge to `s_0 = 1`. -/
theorem forward_counterexample :
    (∀ t, (fun _ _ => (1 : ℝ)) t = (fun _ _ => (0 : ℝ)) t +
        perfectForesight.E t ((fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) (t + 1))) ∧
      ¬ Tendsto (fun T => ∑ k ∈ Finset.range T,
          perfectForesight.E 0 ((fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) (0 + k)) ()) atTop
        (𝓝 1) := by
  refine ⟨fun t => by funext ω; simp [perfectForesight], fun h => ?_⟩
  have h0 : Tendsto (fun T => ∑ k ∈ Finset.range T,
      perfectForesight.E 0 ((fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) (0 + k)) ()) atTop (𝓝 0) := by
    simp [perfectForesight]
  exact one_ne_zero (tendsto_nhds_unique h h0)

/-! ### Eq. (19) is not an independent equilibrium condition (p. 232) -/

/-- Galí (2015), p. 232: **(19) is implied by** the domestic Euler equation (11) (with CPI
inflation), the world Euler equation, the risk-sharing condition (17), the CPI identity (13)
and the AR(1) law `E_t z_{t+1} = ρ_z z_t` (`σ ≠ 0`; `s` known at `t`). -/
theorem tot_difference_of_eulers {σ υ ρ ρz : ℝ} (hσ : σ ≠ 0)
    {c ys z s i is p pH ps : ℕ → Ω → ℝ} (t : ℕ)
    (h11 : ∀ ω, c t ω = 𝔼.E t (c (t + 1)) ω
      - 1 / σ * (i t ω - 𝔼.E t (p (t + 1) - p t) ω - ρ) + (1 - ρz) / σ * z t ω)
    (hW : ∀ ω, ys t ω = 𝔼.E t (ys (t + 1)) ω
      - 1 / σ * (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω - ρ))
    (h17 : ∀ u ω, c u ω = ys u ω + 1 / σ * z u ω + (1 - υ) / σ * s u ω)
    (h13 : ∀ ω, p (t + 1) ω - p t ω = (pH (t + 1) ω - pH t ω) + υ * (s (t + 1) ω - s t ω))
    (hz : 𝔼.E t (z (t + 1)) = ρz • z t) (hs : 𝔼.E t (s t) = s t) (ω : Ω) :
    s t ω = (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω) - (i t ω - 𝔼.E t (pH (t + 1) - pH t) ω)
      + 𝔼.E t (s (t + 1)) ω := by
  have hc1 : c (t + 1) = ys (t + 1) + (1 / σ) • z (t + 1) + ((1 - υ) / σ) • s (t + 1) :=
    funext fun ω => by simp [h17 (t + 1) ω, smul_eq_mul]
  have hp1 : p (t + 1) - p t = (pH (t + 1) - pH t) + υ • (s (t + 1) - s t) :=
    funext fun ω => by simp [h13 ω, smul_eq_mul]
  have e4 : 𝔼.E t (c (t + 1)) ω = 𝔼.E t (ys (t + 1)) ω + 1 / σ * 𝔼.E t (z (t + 1)) ω
      + (1 - υ) / σ * 𝔼.E t (s (t + 1)) ω := by
    rw [hc1, map_add, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have e6 : 𝔼.E t (p (t + 1) - p t) ω = 𝔼.E t (pH (t + 1) - pH t) ω
      + υ * (𝔼.E t (s (t + 1)) ω - s t ω) := by
    rw [hp1, map_add, map_smul, map_sub (𝔼.E t) (s (t + 1)) (s t), hs]
    simp [smul_eq_mul]
  have e5 : 𝔼.E t (z (t + 1)) ω = ρz * z t ω := by rw [hz]; simp [smul_eq_mul]
  have e1 := h11 ω
  have e2 := hW ω
  have e3 := h17 t ω
  linear_combination (norm := skip) σ * e1 - σ * e2 - σ * e3 + σ * e4 + e5 + e6
  field_simp
  ring

end Gali.OpenEconomy.UIP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregate demand in the small open economy

Galí (2015), Chapter 8, §8.1.3 (p. 234) and §8.2.1 (pp. 234–236).

The openness index is `υ ∈ [0, 1]`, `η > 0` is the elasticity of substitution between
domestic and foreign goods and `σ > 0` the inverse intertemporal elasticity. The book's
coefficients are `ϖ = ση + (1 − υ)(ση − 1)` (`varpi`), `Φ = 1/(1 + υ(ϖ − 1))` (`Phi`) and
`σ_υ = σΦ` (`sigmaU`).

## Main results

* `one_add_mul_varpi`, `Phi_pos`, `sigmaU_pos`: `1 + υ(ϖ − 1) = (1 − υ)² + υ(2 − υ)ση > 0`,
  so `Φ > 0` and `σ_υ > 0` (p. 235).
* `cpi_self`, `cpiCD_self`: at the symmetric steady state the CPI (`Preferences.cpi`,
  `Preferences.cpiCD`) equals `P_H`; identity (12) itself is `Identities.log_cpi_eq`,
  `Identities.hasDerivAt_cpiGap` and (exact at `η = 1`) `Identities.log_cpiCD_eq`.
* `exports_eq`, `trade_balanced_ss`, `netExports_ss`: exports `X = υ S^η Y*` and balanced
  trade at the symmetric steady state (p. 234).
* `eq24`: goods-market clearing (23) aggregates exactly to (24).
* `log_eq24`, `eq25`, `eq25_ces`, `eq25_cd`: log output is `logOutput υ η h c s y*` exactly
  (`h` the log relative price of (12)), and (25) `y = (1 − υ)c + υ(2 − υ)ηs + υy*` is its
  exact (Fréchet) derivative at the symmetric steady state, CES or Cobb–Douglas.
* `eq26`: the Euler equation in domestic inflation, from (11) and (13).
* `eq27`: the terms of trade `s = σ_υ(y − y*) − (1 − υ)Φz` from (17) and (25).
* `eq26_iff_eq28`: given (17) and (25), (26) is equivalent to the open-economy dynamic IS
  equation (28).
* `sigmaU_strictAntiOn`: if `ση > 1`, `σ_υ` is strictly decreasing in `υ` on `[0, 1]`
  (p. 235).
* `eq28_iff_eq29`: the gap form (29) with the natural rate (30).
* `hasFDerivAt_netExports`, `eq31`, `nxCoef_eq_zero`: (31)
  `nx = υ(ϖ/σ − 1)s − (υ/σ)z`, and `nx` does not depend on `s` when `σ = η = 1`.
* `nxCoef_one_nonpos`, `nxCoef_counterexample`, `not_large_openness_improves`: the p. 236
  claim that a large `υ` makes a terms-of-trade depreciation improve the trade balance is
  false (with `σ = 1`, `η = 0.9` the coefficient is negative for every `υ ∈ (0, 1]`).
  Corrected statements: `nxCoef_eventually_pos` (`η > 1` ⇒ positive for `υ` near `1`) and
  `nxCoef_pos_iff` (for fixed `υ ∈ (0, 1]`, positive iff `η > (σ + 1 − υ)/((2 − υ)σ)`).

The CES variety aggregation (`priceIndex`, `cesAgg`, `demand`, `cesAgg_demand`) is imported
from `Preferences.Variety`.
-/

namespace Gali.OpenEconomy.AggregateDemand

open MeasureTheory Filter Topology Preferences Preferences.Variety Identities

/-! ### The openness coefficients `ϖ`, `Φ`, `σ_υ` -/

/-- Galí (2015), p. 235: `ϖ ≡ ση + (1 − υ)(ση − 1)`. -/
def varpi (σ η υ : ℝ) : ℝ := σ * η + (1 - υ) * (σ * η - 1)

/-- Galí (2015), p. 235: `Φ ≡ 1/(1 + υ(ϖ − 1))`. -/
noncomputable def Phi (σ η υ : ℝ) : ℝ := 1 / (1 + υ * (varpi σ η υ - 1))

/-- Galí (2015), p. 235: `σ_υ ≡ σΦ`. -/
noncomputable def sigmaU (σ η υ : ℝ) : ℝ := σ * Phi σ η υ

/-- Galí (2015), p. 235: `ϖ − 1 = (2 − υ)(ση − 1)`. -/
theorem varpi_sub_one (σ η υ : ℝ) : varpi σ η υ - 1 = (2 - υ) * (σ * η - 1) := by
  unfold varpi
  ring

/-- Galí (2015), p. 235: `1 + υ(ϖ − 1) = (1 − υ)² + υ(2 − υ)ση`. -/
theorem one_add_mul_varpi (σ η υ : ℝ) :
    1 + υ * (varpi σ η υ - 1) = (1 - υ) ^ 2 + υ * (2 - υ) * (σ * η) := by
  unfold varpi
  ring

/-- Galí (2015), p. 235: for `σ, η > 0` and `υ ∈ [0, 1]`, `1 + υ(ϖ − 1) > 0`. -/
theorem one_add_mul_varpi_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ ≤ 1) : 0 < 1 + υ * (varpi σ η υ - 1) := by
  rw [one_add_mul_varpi]
  have hse : 0 < σ * η := mul_pos hσ hη
  rcases eq_or_lt_of_le hυ1 with h | h
  · subst h
    norm_num
    exact hse
  · have h1 : 0 < (1 - υ) ^ 2 := by
      have : 0 < 1 - υ := by linarith
      positivity
    have h2 : 0 ≤ υ * (2 - υ) * (σ * η) :=
      mul_nonneg (mul_nonneg hυ0 (by linarith)) hse.le
    linarith

/-- Galí (2015), p. 235: `Φ > 0`. -/
theorem Phi_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) :
    0 < Phi σ η υ :=
  one_div_pos.2 (one_add_mul_varpi_pos hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ > 0`. -/
theorem sigmaU_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) :
    0 < sigmaU σ η υ :=
  mul_pos hσ (Phi_pos hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ (1 + υ(ϖ − 1)) = σ`. -/
theorem sigmaU_mul {σ η υ : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) :
    sigmaU σ η υ * (1 + υ * (varpi σ η υ - 1)) = σ := by
  unfold sigmaU Phi
  field_simp

/-- Galí (2015), p. 239: if `ση > 1` (and `υ < 2`, in particular `υ ∈ [0, 1]`), `ϖ > 1`. -/
theorem one_lt_varpi {σ η υ : ℝ} (h : 1 < σ * η) (hυ : υ < 2) : 1 < varpi σ η υ := by
  have := varpi_sub_one σ η υ
  have : 0 < (2 - υ) * (σ * η - 1) := mul_pos (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 235: in the closed economy (`υ = 0`), `σ_υ = σ`. -/
theorem sigmaU_zero (σ η : ℝ) : sigmaU σ η 0 = σ := by
  simp [sigmaU, Phi]

/-- Galí (2015), p. 235: with `ση = 1` (e.g. `σ = η = 1`), `ϖ = 1`, `Φ = 1`, `σ_υ = σ` for
every degree of openness. -/
theorem sigmaU_of_sigma_mul_eta {σ η : ℝ} (h : σ * η = 1) (υ : ℝ) : sigmaU σ η υ = σ := by
  simp [sigmaU, Phi, varpi, h]

/-- Galí (2015), p. 235: **if `ση > 1`, `σ_υ` is strictly decreasing in the degree of
openness `υ` on `[0, 1]`**, so openness raises the interest sensitivity `1/σ_υ` of output. -/
theorem sigmaU_strictAntiOn {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (h : 1 < σ * η) :
    StrictAntiOn (sigmaU σ η) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have hDa := one_add_mul_varpi_pos hσ hη ha.1 ha.2
  have hlt : 1 + a * (varpi σ η a - 1) < 1 + b * (varpi σ η b - 1) := by
    rw [varpi_sub_one, varpi_sub_one]
    have : 0 < (σ * η - 1) * ((b - a) * (2 - a - b)) :=
      mul_pos (by linarith) (mul_pos (by linarith) (by linarith [hb.2]))
    nlinarith
  unfold sigmaU Phi
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hDa hlt) hσ

/-! ### The consumer price index and identity (12)

The CES consumer price index is `Preferences.cpi` (`η ≠ 1`), its Cobb–Douglas limit
`Preferences.cpiCD` (`η = 1`); the exact identity (12) and its first-order form are
`Identities.log_cpi_eq`, `Identities.hasDerivAt_cpiGap` and `Identities.log_cpiCD_eq`. -/

/-- Galí (2015), p. 227: a convex combination of positive numbers is positive. -/
theorem convex_comb_pos {υ a b : ℝ} (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - υ) * a + υ * b := by
  rcases eq_or_lt_of_le hυ1 with h | h
  · subst h
    simpa using hb
  · have : 0 < (1 - υ) * a := mul_pos (by linarith) ha
    have : 0 ≤ υ * b := mul_nonneg hυ0 hb.le
    linarith

/-- Galí (2015), p. 234: at the symmetric steady state `P_F = P_H` the CES consumer price
index equals `P_H` (any `υ`, `η ≠ 1`). -/
theorem cpi_self {υ η P : ℝ} (hη : η ≠ 1) (hP : 0 < P) : cpi υ η P P = P := by
  have h1 : (1 : ℝ) - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  unfold cpi
  rw [show (1 - υ) * P ^ (1 - η) + υ * P ^ (1 - η) = P ^ (1 - η) by ring, one_div,
    Real.rpow_rpow_inv hP.le h1]

/-- Galí (2015), fn. 2, p. 226, and p. 234: at the symmetric steady state `P_F = P_H` the
Cobb–Douglas consumer price index (`η = 1`) equals `P_H`. -/
theorem cpiCD_self {υ P : ℝ} (hP : 0 < P) : cpiCD υ P P = P := by
  unfold cpiCD
  rw [← Real.rpow_add hP]
  simp

/-! ### Exports and the steady-state trade balance (p. 234) -/

/-- Galí (2015), p. 234: with the law of one price `P_F = ℰP*`, exports
`X = υ(P_H/(ℰP*))^{−η}Y*` equal `υS^ηY*`, `S = P_F/P_H`. -/
theorem exports_eq {υ η PH PF ℰ Pstar Ystar : ℝ} (hPH : 0 < PH) (hE : 0 < ℰ)
    (hPs : 0 < Pstar) (hLOP : PF = ℰ * Pstar) :
    υ * (PH / (ℰ * Pstar)) ^ (-η) * Ystar = υ * (PF / PH) ^ η * Ystar := by
  rw [hLOP, Real.rpow_neg (div_pos hPH (mul_pos hE hPs)).le, ← Real.inv_rpow
    (div_pos hPH (mul_pos hE hPs)).le, inv_div]

/-- Galí (2015), p. 234: **trade is balanced at the symmetric steady state**: with `S = 1`
(`P_F = P_H`), the CPI `P_c` then equal to `P_H` (`cpi_self` for the CES index, `cpiCD_self`
for the Cobb–Douglas one), imports `C_F = υ(P_F/P_c)^{−η}C`, exports `X = υS^ηY*` and risk
sharing `C = Y*`, the value of exports equals the value of imports, `P_H X = P_F C_F`. -/
theorem trade_balanced_ss {υ η PH PF Pc C CF X Ystar : ℝ} (hPH : 0 < PH) (hS : PF = PH)
    (hPc : Pc = PH) (hC : C = Ystar) (hCF : CF = υ * (PF / Pc) ^ (-η) * C)
    (hX : X = υ * (PF / PH) ^ η * Ystar) :
    PH * X = PF * CF := by
  subst hS hC hPc
  rw [hCF, hX, div_self hPH.ne']
  simp

/-- Galí (2015), p. 234 and p. 236: at the symmetric steady state (CPI `P_c = P_H`, by
`cpi_self` or `cpiCD_self`) output equals consumption and net exports `Y − (P_c/P_H)C` are
zero. -/
theorem netExports_ss {υ η PH Pc Y C Ystar : ℝ} (hPH : 0 < PH) (hPc : Pc = PH)
    (hC : C = Ystar)
    (hY : Y = (1 - υ) * (PH / Pc) ^ (-η) * C + υ * (PH / PH) ^ η * Ystar) :
    Y = C ∧ Y - Pc / PH * C = 0 := by
  subst hPc
  rw [div_self hPH.ne'] at hY ⊢
  simp only [Real.one_rpow, mul_one] at hY
  subst hC
  constructor <;> linarith

/-! ### Goods-market clearing: (23) and (24)

The CES variety aggregation (`priceIndex`, `cesAgg`, `demand`, `cesAgg_demand`) is
`Preferences.Variety`. -/

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), (23) and **(24)**, pp. 234–235 (exact): if each domestic good `i` clears its
market, `Y(i) = C_H(i) + X(i)` with `C_H(i) = (P_H(i)/P_H)^{−ε}(1 − υ)(P_H/P)^{−η}C` and
`X(i) = (P_H(i)/P_H)^{−ε}υS^ηY*`, then aggregate output is
`Y = (1 − υ)(P_H/P)^{−η}C + υS^ηY*`. -/
theorem eq24 {μ : Measure G} {ε υ η P C S Ystar : ℝ} {PHi CH X Y : G → ℝ} (hε : 1 < ε)
    (hP : ∀ i, 0 < PHi i) (hpos : 0 < ∫ i, PHi i ^ (1 - ε) ∂μ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hPc : 0 < P) (hC : 0 ≤ C) (hS : 0 ≤ S) (hYs : 0 ≤ Ystar)
    (hCH : ∀ i, CH i = (PHi i / priceIndex μ ε PHi) ^ (-ε) *
      ((1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C))
    (hX : ∀ i, X i = (PHi i / priceIndex μ ε PHi) ^ (-ε) * (υ * S ^ η * Ystar))
    (hY : ∀ i, Y i = CH i + X i) :
    cesAgg μ ε Y = (1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C + υ * S ^ η * Ystar := by
  have hI := priceIndex_pos hpos
  have hYd : Y = demand μ ε PHi
      ((1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C + υ * S ^ η * Ystar) := by
    funext i
    rw [hY, hCH, hX, demand]
    ring
  rw [hYd]
  refine cesAgg_demand hε hP hpos (add_nonneg (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (div_pos hI hPc).le _)) hC) (mul_nonneg (mul_nonneg hυ0
    (Real.rpow_nonneg hS _)) hYs))

/-! ### Log-linear goods-market clearing (25) as an exact derivative -/

/-- Galí (2015), (24), p. 235, in logs: `log Y` as a function of `c = log C`, the log terms of
trade `s` and `y* = log Y*`, `log[(1 − υ)e^{c + η h(s)} + υe^{ηs + y*}]`, where
`h(s) = log(P/P_H)` is the log relative price of (12): `Identities.cpiGap υ η` for the CES
index (`η ≠ 1`) and `s ↦ υs` for the Cobb–Douglas index (`η = 1`). -/
noncomputable def logOutput (υ η : ℝ) (h : ℝ → ℝ) (c s ystar : ℝ) : ℝ :=
  Real.log ((1 - υ) * Real.exp (c + η * h s) + υ * Real.exp (η * s + ystar))

/-- Galí (2015), (24), p. 235 (exact): for a consumer price index `P_c` with log relative
price `h`, `log P_c − log P_H = h(p_F − p_H)` (identity (12): `Identities.log_cpi_eq` for the
CES index, `Identities.log_cpiCD_eq` for the Cobb–Douglas one), `log Y` is `logOutput`
evaluated at `c`, `s = p_F − p_H` and `y*`. -/
theorem log_eq24 {υ η PH PF Pc C Ystar Y : ℝ} {h : ℝ → ℝ} (hPH : 0 < PH) (hPF : 0 < PF)
    (hP : 0 < Pc) (hC : 0 < C) (hYs : 0 < Ystar)
    (hL : Real.log Pc - Real.log PH = h (Real.log PF - Real.log PH))
    (hY : Y = (1 - υ) * (PH / Pc) ^ (-η) * C + υ * (PF / PH) ^ η * Ystar) :
    Real.log Y
      = logOutput υ η h (Real.log C) (Real.log PF - Real.log PH) (Real.log Ystar) := by
  have e1 : (PH / Pc) ^ (-η) * C
      = Real.exp (Real.log C + η * h (Real.log PF - Real.log PH)) := by
    rw [Real.exp_add, Real.exp_log hC, ← hL, Real.rpow_def_of_pos (div_pos hPH hP),
      Real.log_div hPH.ne' hP.ne', mul_comm C]
    congr 2
    ring
  have e2 : (PF / PH) ^ η * Ystar
      = Real.exp (η * (Real.log PF - Real.log PH) + Real.log Ystar) := by
    rw [Real.exp_add, Real.exp_log hYs, Real.rpow_def_of_pos (div_pos hPF hPH),
      Real.log_div hPF.ne' hPH.ne', mul_comm (Real.log PF - Real.log PH)]
  unfold logOutput
  rw [hY, mul_assoc (1 - υ), e1, mul_assoc υ, e2]

/-- Galí (2015), (25), p. 235: the linear map
`(c, s, y*) ↦ (1 − υ)c + υ(2 − υ)ηs + υy*`. -/
noncomputable def eq25Map (υ η : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  (1 - υ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
    + (υ * (2 - υ) * η) •
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    + υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Galí (2015), (25), p. 235: `eq25Map` evaluated. -/
theorem eq25Map_apply (υ η c s ys : ℝ) :
    eq25Map υ η (c, s, ys) = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ys := by
  simp [eq25Map]

/-- Galí (2015), p. 234: at the symmetric steady state (`c = y* = ȳ`, `s = 0`), log output is
`ȳ`, i.e. `Y = C = Y*`. -/
theorem logOutput_ss (υ η ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0) :
    logOutput υ η h ybar 0 ybar = ybar := by
  unfold logOutput
  rw [h0]
  have : (1 - υ) * Real.exp (ybar + η * 0) + υ * Real.exp (η * 0 + ybar) = Real.exp ybar := by
    simp only [mul_zero, add_zero, zero_add]
    ring
  rw [this, Real.log_exp]

/-- Galí (2015), **(25)**, p. 235: `y = (1 − υ)c + υ(2 − υ)ηs + υy*` is the exact
(Fréchet) derivative of log (24) at the symmetric steady state `(c, s, y*) = (ȳ, 0, ȳ)`,
for every log relative price `h` with `h(0) = 0` and `h'(0) = υ` (the first-order form of
(12)), in particular in the CES case (`eq25_ces`) and the Cobb–Douglas case (`eq25_cd`). -/
theorem eq25 (υ η ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0) (hd : HasDerivAt h υ 0) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ η h x.1 x.2.1 x.2.2) (eq25Map υ η)
      (ybar, 0, ybar) := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_snd.snd
  have hL : HasFDerivAt (fun x : ℝ × ℝ × ℝ => h x.2.1)
      (υ • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := HasDerivAt.comp_hasFDerivAt (f := fun x : ℝ × ℝ × ℝ => x.2.1)
        (ybar, (0 : ℝ), ybar) hd h2
  have hA := h1.add (hL.const_mul η)
  have hB := (h2.const_mul η).add h3
  have hF := (hA.exp.const_mul (1 - υ)).add (hB.exp.const_mul υ)
  have hne : (1 - υ) * Real.exp (ybar + η * h 0) +
      υ * Real.exp (η * 0 + ybar) ≠ 0 := by
    rw [h0]
    simp only [mul_zero, add_zero, zero_add]
    ring_nf
    exact (Real.exp_pos _).ne'
  have hlog := hF.log hne
  refine hlog.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨c, s, ys⟩ := x
  rw [eq25Map_apply]
  simp only [Pi.add_apply, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  rw [h0]
  simp only [mul_zero, add_zero, zero_add]
  rw [show (1 - υ) * Real.exp ybar + υ * Real.exp ybar = Real.exp ybar by ring]
  have he := (Real.exp_pos ybar).ne'
  field_simp
  ring

/-- Galí (2015), **(25)**, p. 235, CES case (`η ≠ 1`, `0 < υ < 1`): with the exact CES log
relative price `h = Identities.cpiGap υ η` of (12), (25) is the derivative of log (24). -/
theorem eq25_ces {υ η : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (ybar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ η (cpiGap υ η) x.1 x.2.1 x.2.2)
      (eq25Map υ η) (ybar, 0, ybar) :=
  eq25 υ η ybar (cpiGap_zero hυ0 hυ1) (hasDerivAt_cpiGap hυ0 hυ1 hη1)

/-- Galí (2015), **(25)**, p. 235, Cobb–Douglas case (`η = 1`, fn. 4, p. 229): with the exact
log relative price `h(s) = υs` of (12), (25) is the derivative of log (24). -/
theorem eq25_cd (υ ybar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ 1 (fun s => υ * s) x.1 x.2.1 x.2.2)
      (eq25Map υ 1) (ybar, 0, ybar) :=
  eq25 υ 1 ybar (mul_zero υ) (by simpa using (hasDerivAt_id' (0 : ℝ)).const_mul υ)

/-! ### The terms of trade (27) and net exports (31) -/

/-- Galí (2015), **(27)**, p. 235: combining risk sharing (17)
`c = y* + z/σ + ((1 − υ)/σ)s` with (25) gives `s = σ_υ(y − y*) − (1 − υ)Φz`. -/
theorem eq27 {σ η υ c s y ystar z : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) :
    s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z := by
  have key : σ * (y - ystar) = (1 - υ) * z + (1 + υ * (varpi σ η υ - 1)) * s := by
    rw [h25, h17]
    unfold varpi
    field_simp
    ring
  unfold sigmaU Phi
  field_simp
  linear_combination -key

/-- Galí (2015), p. 236: the coefficient `υ(ϖ/σ − 1)` of the terms of trade in (31). -/
noncomputable def nxCoef (σ η υ : ℝ) : ℝ := υ * (varpi σ η υ / σ - 1)

/-- Galí (2015), **(31)**, p. 236: with `nx = y − c − υs` (the first-order net-export
identity, `hasFDerivAt_netExports`), (17) and (25), `nx = υ(ϖ/σ − 1)s − (υ/σ)z`. -/
theorem eq31 {σ η υ c s y ystar z nx : ℝ} (hσ : σ ≠ 0)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) (hnx : nx = y - c - υ * s) :
    nx = nxCoef σ η υ * s - υ / σ * z := by
  rw [hnx, h25, h17]
  unfold nxCoef varpi
  field_simp
  ring

/-- Galí (2015), p. 236: net exports in terms of domestic output relative to steady-state
output, `nx = (Y − (P/P_H)C)/Ȳ`, written in logs `y`, `c` and `s` (`ȳ = log Ȳ`), where `h`
is the log relative price `log(P/P_H)` of (12) as a function of `s` (see `logOutput`). -/
noncomputable def netExports (h : ℝ → ℝ) (ybar y c s : ℝ) : ℝ :=
  (Real.exp y - Real.exp (c + h s)) / Real.exp ybar

/-- Galí (2015), p. 236 (exact): for a CPI `P_c` with `log P_c − log P_H = h(p_F − p_H)`
(`Identities.log_cpi_eq`, `Identities.log_cpiCD_eq`), `(Y − (P_c/P_H)C)/Ȳ` is `netExports`
in logs. -/
theorem netExports_eq {PH PF Pc C Y Ybar : ℝ} {h : ℝ → ℝ} (hPH : 0 < PH) (hP : 0 < Pc)
    (hC : 0 < C) (hY : 0 < Y) (hYb : 0 < Ybar)
    (hL : Real.log Pc - Real.log PH = h (Real.log PF - Real.log PH)) :
    (Y - Pc / PH * C) / Ybar = netExports h (Real.log Ybar) (Real.log Y)
      (Real.log C) (Real.log PF - Real.log PH) := by
  unfold netExports
  rw [Real.exp_log hY, Real.exp_log hYb, Real.exp_add, Real.exp_log hC,
    ← hL, Real.exp_sub, Real.exp_log hP, Real.exp_log hPH, mul_comm C]

/-- Galí (2015), p. 236: the linear map `(y, c, s) ↦ y − c − υs`. -/
noncomputable def nxMap (υ : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
    - (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    - υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Galí (2015), p. 236: `nxMap` evaluated. -/
theorem nxMap_apply (υ y c s : ℝ) : nxMap υ (y, c, s) = y - c - υ * s := by
  simp [nxMap]

/-- Galí (2015), p. 236: **`nx = y − c − υs` to first order**: net exports vanish at the
symmetric steady state `(y, c, s) = (ȳ, ȳ, 0)`, and their exact derivative there is
`(y, c, s) ↦ y − c − υs`, for every log relative price `h` with `h(0) = 0`, `h'(0) = υ` (CES:
`Identities.cpiGap_zero`, `Identities.hasDerivAt_cpiGap`; Cobb–Douglas: `h(s) = υs`). -/
theorem hasFDerivAt_netExports (υ ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0)
    (hd : HasDerivAt h υ 0) :
    netExports h ybar ybar ybar 0 = 0 ∧
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => netExports h ybar x.1 x.2.1 x.2.2) (nxMap υ)
        (ybar, ybar, 0) := by
  refine ⟨by simp [netExports, h0], ?_⟩
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_snd.snd
  have hL : HasFDerivAt (fun x : ℝ × ℝ × ℝ => h x.2.2)
      (υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := HasDerivAt.comp_hasFDerivAt (f := fun x : ℝ × ℝ × ℝ => x.2.2)
        (ybar, ybar, (0 : ℝ)) hd h3
  have hF := HasFDerivAt.mul_const (HasFDerivAt.sub h1.exp (h2.add hL).exp) (Real.exp ybar)⁻¹
  have hfun : (fun x : ℝ × ℝ × ℝ => netExports h ybar x.1 x.2.1 x.2.2) = fun x =>
      (Real.exp x.1 - Real.exp (x.2.1 + h x.2.2)) * (Real.exp ybar)⁻¹ := by
    funext x
    simp [netExports, div_eq_mul_inv]
  rw [hfun]
  refine hF.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨y, c, s⟩ := x
  rw [nxMap_apply]
  simp only [h0, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    FunLike.coe_sub, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, add_zero]
  have he := (Real.exp_pos ybar).ne'
  field_simp
  ring

/-- Galí (2015), p. 236: **with `σ = η = 1`, net exports are invariant to the terms of trade**:
the coefficient of `s` in (31) is zero and `nx = −υz`. -/
theorem nxCoef_eq_zero (υ : ℝ) : nxCoef 1 1 υ = 0 := by
  simp [nxCoef, varpi]

/-- Galí (2015), p. 236: at `σ = η = 1`, (31) reads `nx = −υz`. -/
theorem eq31_unit {υ c s y ystar z nx : ℝ} (h17 : c = ystar + z / 1 + (1 - υ) / 1 * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * 1 * s + υ * ystar) (hnx : nx = y - c - υ * s) :
    nx = -υ * z := by
  rw [eq31 one_ne_zero h17 h25 hnx, nxCoef_eq_zero]
  ring

/-- Galí (2015), p. 236, **correction (error 2)**: at full openness `υ = 1` the coefficient of
the terms of trade is `η − 1`, so for `η ≤ 1` a depreciation never improves the trade balance
there, however open the economy. -/
theorem nxCoef_one_nonpos {σ η : ℝ} (hσ : 0 < σ) (hη : η ≤ 1) : nxCoef σ η 1 ≤ 0 := by
  have : nxCoef σ η 1 = η - 1 := by
    unfold nxCoef varpi
    field_simp
    ring
  linarith

/-- Galí (2015), p. 236, **counterexample (error 2)**: with `σ = 1` and `η = 0.9` the
coefficient `υ(ϖ/σ − 1)` of the terms of trade in (31) is negative for every
`υ ∈ (0, 1]`: a depreciation worsens the trade balance however large `υ` is. -/
theorem nxCoef_counterexample {υ : ℝ} (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) :
    nxCoef 1 (9 / 10) υ < 0 := by
  unfold nxCoef varpi
  norm_num
  nlinarith

/-- Galí (2015), p. 236, **the printed claim is false (error 2)**: it is not true that a
sufficiently large `υ` makes a terms-of-trade depreciation improve the trade balance
(`σ = 1`, `η = 0.9`). -/
theorem not_large_openness_improves :
    ¬ ∃ u0 < (1 : ℝ), ∀ υ, u0 < υ → υ ≤ 1 → 0 < nxCoef 1 (9 / 10) υ := by
  rintro ⟨u0, hu0, h⟩
  have h1 := h 1 hu0 le_rfl
  linarith [nxCoef_counterexample one_pos (le_refl (1 : ℝ))]

/-- Galí (2015), p. 236, **corrected statement (error 2), part 1**: if `η > 1`, the trade
balance improves with a depreciation (`nxCoef > 0`) for all `υ` close enough to `1`. -/
theorem nxCoef_eventually_pos {σ η : ℝ} (hσ : 0 < σ) (hη : 1 < η) :
    ∀ᶠ υ in 𝓝 1, 0 < nxCoef σ η υ := by
  have hc : Continuous fun υ => nxCoef σ η υ := by
    unfold nxCoef varpi
    fun_prop
  have h1 : 0 < nxCoef σ η 1 := by
    have : nxCoef σ η 1 = η - 1 := by
      unfold nxCoef varpi
      field_simp
      ring
    linarith
  exact (hc.tendsto 1).eventually (lt_mem_nhds h1)

/-- Galí (2015), p. 236, **corrected statement (error 2), part 2**: for a given degree of
openness `υ ∈ (0, 1]`, a depreciation improves the trade balance iff
`η > (σ + 1 − υ)/((2 − υ)σ)`. -/
theorem nxCoef_pos_iff {σ η υ : ℝ} (hσ : 0 < σ) (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) :
    0 < nxCoef σ η υ ↔ (σ + 1 - υ) / ((2 - υ) * σ) < η := by
  have e : nxCoef σ η υ = υ / σ * ((2 - υ) * σ * η - (σ + 1 - υ)) := by
    unfold nxCoef varpi
    field_simp
    ring
  have hd : 0 < (2 - υ) * σ := mul_pos (by linarith) hσ
  rw [e, mul_pos_iff_of_pos_left (div_pos hυ0 hσ), div_lt_iff₀ hd]
  constructor <;> intro h <;> linarith

/-! ### The dynamic IS equation (26)–(30) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), **(26)**, p. 235: the Euler equation (11) with CPI inflation, combined with
(13) `π_{t+1} = π_{H,t+1} + υΔs_{t+1}` (and `s` known at `t`), gives the Euler equation in
domestic inflation,
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{H,t+1} − ρ) + (υ/σ)E_tΔs_{t+1} + σ⁻¹(1 − ρ_z)z_t`. -/
theorem eq26 {σ υ ρ ρz : ℝ} {c i infl inflH s z : ℕ → Ω → ℝ} (t : ℕ)
    (h11 : c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
      + (σ⁻¹ * (1 - ρz)) • z t)
    (h13 : infl (t + 1) = inflH (t + 1) + υ • (s (t + 1) - s t)) (hs : 𝔼.E t (s t) = s t) :
    c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ / σ) • (𝔼.E t (s (t + 1)) - s t) + (σ⁻¹ * (1 - ρz)) • z t := by
  rw [h11, h13, map_add, map_smul, map_sub, hs]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), (27), p. 235, for processes: (17) and (25) at date `t` give
`s_t = σ_υ(y_t − y*_t) − (1 − υ)Φz_t`. -/
theorem eq27_proc {σ η υ : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {c s y ystar z : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : c t = ystar t + σ⁻¹ • z t + ((1 - υ) / σ) • s t)
    (h25 : y t = (1 - υ) • c t + (υ * (2 - υ) * η) • s t + υ • ystar t) :
    s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t := by
  funext ω
  have a := congrFun h17 ω
  have b := congrFun h25 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
  rw [eq27 hσ hD (c := c t ω) (s := s t ω) (y := y t ω) (ystar := ystar t ω) (z := z t ω)
    (by rw [a]; ring) b]

/-- Galí (2015), (26)–(28), p. 235: the algebraic identity behind (28): after substituting
(17) and (27) (at `t` and, in expectation, at `t + 1`, with `E_t z_{t+1} = ρ_z z_t`), the
(26) residual equals `Φ` times the (28) residual. Here `R = i_t − E_t π_{H,t+1} − ρ`. -/
theorem key_eq26_eq28 {σ η υ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (y Ey ys Eys z R : ℝ) :
    (ys + σ⁻¹ * z + (1 - υ) / σ * (sigmaU σ η υ * (y - ys) - (1 - υ) * Phi σ η υ * z))
      - ((Eys + σ⁻¹ * (ρz * z) + (1 - υ) / σ *
          (sigmaU σ η υ * (Ey - Eys) - (1 - υ) * Phi σ η υ * (ρz * z)))
        - σ⁻¹ * R + υ / σ * ((sigmaU σ η υ * (Ey - Eys) - (1 - υ) * Phi σ η υ * (ρz * z))
          - (sigmaU σ η υ * (y - ys) - (1 - υ) * Phi σ η υ * z)) + σ⁻¹ * (1 - ρz) * z)
    = Phi σ η υ * (y - (Ey - (sigmaU σ η υ)⁻¹ * R + υ * (varpi σ η υ - 1) * (Eys - ys)
        + (1 - υ) / σ * (1 - ρz) * z)) := by
  unfold sigmaU Phi
  field_simp
  ring

/-- Galí (2015), **(28)**, p. 235: given risk sharing (17) and goods-market clearing (25) at
all dates and `E_t z_{t+1} = ρ_z z_t`, the Euler equation (26) holds at `t` **if and only
if** the open-economy dynamic IS equation holds at `t`:
`y_t = E_t y_{t+1} − σ_υ⁻¹(i_t − E_t π_{H,t+1} − ρ) + υ(ϖ − 1)E_tΔy*_{t+1}
+ ((1 − υ)/σ)(1 − ρ_z)z_t`. -/
theorem eq26_iff_eq28 {σ η υ ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {c s y ystar i inflH z : ℕ → Ω → ℝ}
    (h17 : ∀ t, c t = ystar t + σ⁻¹ • z t + ((1 - υ) / σ) • s t)
    (h25 : ∀ t, y t = (1 - υ) • c t + (υ * (2 - υ) * η) • s t + υ • ystar t) (t : ℕ)
    (hz : 𝔼.E t (z (t + 1)) = ρz • z t) :
    (c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ / σ) • (𝔼.E t (s (t + 1)) - s t) + (σ⁻¹ * (1 - ρz)) • z t) ↔
    (y t = 𝔼.E t (y (t + 1)) - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ * (varpi σ η υ - 1)) • (𝔼.E t (ystar (t + 1)) - ystar t)
      + ((1 - υ) / σ * (1 - ρz)) • z t) := by
  have hs : ∀ t, s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t :=
    fun t => eq27_proc hσ hD t (h17 t) (h25 t)
  have hc' : 𝔼.E t (c (t + 1)) = 𝔼.E t (ystar (t + 1)) + σ⁻¹ • (ρz • z t)
      + ((1 - υ) / σ) • 𝔼.E t (s (t + 1)) := by
    rw [h17 (t + 1), map_add, map_add, map_smul, map_smul, hz]
  have hs' : 𝔼.E t (s (t + 1)) = sigmaU σ η υ • (𝔼.E t (y (t + 1)) - 𝔼.E t (ystar (t + 1)))
      - ((1 - υ) * Phi σ η υ) • (ρz • z t) := by
    rw [hs (t + 1), map_sub, map_smul, map_smul, map_sub, hz]
  have hΦ : Phi σ η υ ≠ 0 := one_div_ne_zero hD
  rw [hc', hs', h17 t, hs t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    have k := key_eq26_eq28 (ρz := ρz) hσ hD (y t ω) (𝔼.E t (y (t + 1)) ω) (ystar t ω)
      (𝔼.E t (ystar (t + 1)) ω) (z t ω) (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    have h0 : Phi σ η υ * (y t ω - (𝔼.E t (y (t + 1)) ω
        - (sigmaU σ η υ)⁻¹ * (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
        + υ * (varpi σ η υ - 1) * (𝔼.E t (ystar (t + 1)) ω - ystar t ω)
        + (1 - υ) / σ * (1 - ρz) * z t ω)) = 0 := by
      linear_combination -k + e
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hΦ
    · linear_combination h1
  · intro h
    funext ω
    have e := congrFun h ω
    have k := key_eq26_eq28 (ρz := ρz) hσ hD (y t ω) (𝔼.E t (y (t + 1)) ω) (ystar t ω)
      (𝔼.E t (ystar (t + 1)) ω) (z t ω) (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linear_combination k + Phi σ η υ * e

/-- Galí (2015), **(30)**, p. 235: the natural rate of interest of the small open economy,
`rⁿ_t = ρ + σ_υE_tΔyⁿ_{t+1} + σ_υυ(ϖ − 1)E_tΔy*_{t+1} + Φ(1 − υ)(1 − ρ_z)z_t`. -/
noncomputable def natRate (σ η υ ρ ρz : ℝ) (yn ystar z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + sigmaU σ η υ • (𝔼.E t (yn (t + 1)) - yn t)
    + (sigmaU σ η υ * (υ * (varpi σ η υ - 1))) • (𝔼.E t (ystar (t + 1)) - ystar t)
    + (Phi σ η υ * (1 - υ) * (1 - ρz)) • z t

/-- Galí (2015), **(29)**, p. 235: with the output gap `ỹ = y − yⁿ`, the dynamic IS equation
(28) at `t` is equivalent to
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹(i_t − E_t π_{H,t+1} − rⁿ_t)`, `rⁿ` as in (30). -/
theorem eq28_iff_eq29 {σ η υ ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {y yn ygap ystar i inflH z : ℕ → Ω → ℝ} (hgap : ∀ t, ygap t = y t - yn t) (t : ℕ) :
    (y t = 𝔼.E t (y (t + 1)) - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ * (varpi σ η υ - 1)) • (𝔼.E t (ystar (t + 1)) - ystar t)
      + ((1 - υ) / σ * (1 - ρz)) • z t) ↔
    ygap t = 𝔼.E t (ygap (t + 1))
      - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - natRate 𝔼 σ η υ ρ ρz yn ystar z t) := by
  rw [hgap t, hgap (t + 1), map_sub]
  unfold natRate
  have hΦ : Phi σ η υ ≠ 0 := one_div_ne_zero hD
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    unfold sigmaU Phi at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    unfold sigmaU Phi at e ⊢
    field_simp at e ⊢
    linear_combination e

end Gali.OpenEconomy.AggregateDemand

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The supply side of the small open economy

Galí (2015), Chapter 8, §8.2.2 (pp. 236–239).

Notation as in `AggregateDemand`: `ϖ = varpi σ η υ`, `Φ = Phi σ η υ`, `σ_υ = sigmaU σ η υ`;
`λ` is written `lam`.

## Main results

* `employment_identity`, `eq32_exact`, `eq32`, `dispersion_family_first_order`,
  `dispersion_second_order`: aggregate output and employment satisfy exactly
  `y = a + (1 − α)n − d`, where the price-dispersion term `d` is zero with zero derivative
  (indeed `O(s²)`) around a symmetric price distribution, so (32) `y = a + (1 − α)n` holds
  to first order (restated from the Chapter 3 project).
* `eq33`: the average markup (33),
  `μ = −(σ + (φ+α)/(1−α))y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α))a − υz`.
* `eq34`: the Phillips curve in `y`, `s`, `a`, `z`.
* `sigma_sub_eq_sigmaU`: the key identity `σ − υ(ϖ − 1)σ_υ = σ_υ`.
* `eq35_iff`, `GammaA_pos`: natural output (35) `yⁿ = Γ_a a + Γ_z z + Γ_* y*`, `Γ_a > 0`.
* `GammaStar_unit`, `GammaZ_unit_neg`, `GammaZ_zero`: `σ = η = 1` ⇒ `Γ_* = 0`, `Γ_z < 0`
  (for `υ > 0`); `υ = 0` ⇒ `Γ_z = 0` (fn. 8).
* `sgap_eq`, `eq36`, `eq37`: `s̃ = σ_υỹ`, `μ̂ = −(σ_υ + (φ+α)/(1−α))ỹ` and the open-economy
  Phillips curve `π_H = βE π_H' + κ_υ ỹ`.
* `kappaU_zero`, `kappaU_unit`, `kappaU_strictAntiOn`: `κ_υ = κ` if `υ = 0` or `σ = η = 1`;
  `ση > 1` ⇒ `κ_υ` strictly decreasing in `υ` on `[0, 1]`.
* `eq38`, `tendsto_PsiStar`, `tendsto_PsiZ`: the natural rate (38) and `Ψ_* → 0`,
  `Ψ_z → 1` as `υ → 0`.
-/

namespace Gali.OpenEconomy.Supply

open MeasureTheory ProbabilityTheory Filter Topology Gali.OpenEconomy.AggregateDemand
  Gali.OpenEconomy.Preferences.Variety

/-! ### Aggregate output and employment, (32) (restated from the Chapter 3 project) -/

variable {G : Type*} [MeasurableSpace G]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59 and App. 3.4, p. 86: the price-dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 60 and App. 3.4, p. 86: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), App. 3.4, p. 86: the cross-sectional variance
`var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ} {P : G → ℝ}

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59: with production `Y(i) = A N(i)^{1−α}` (5) and output on the demand
schedule `Y(i) = (P(i)/P)^{−ε} Y` (from (1) and goods-market clearing), aggregate employment
is `N = ∫ N(i) = (Y/A)^{1/(1−α)} ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
theorem employment_level (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α)) :
    ∫ i, N i ∂μ
      = (Y / A) ^ (1 - α)⁻¹ * ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ := by
  have hI := priceIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, N i = (Y / A) ^ (1 - α)⁻¹ * (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    have h1 : N i ^ (1 - α) = (P i / priceIndex μ ε P) ^ (-ε) * (Y / A) := by
      have := hprod i
      rw [demand] at this
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-ε), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59, eq. (14) before approximation (**exact**):
`(1 − α) log N = log Y − log A + d`. -/
theorem employment_identity (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α))
    (hD : 0 < ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) :
    (1 - α) * Real.log (∫ i, N i ∂μ) = Real.log Y - Real.log A + dispersion μ α ε P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [employment_level hα1 hP hpos hA hY.le hN hprod, Real.log_mul (by positivity) hD.ne',
    Real.log_rpow (by positivity), Real.log_div hY.ne' hA.ne', dispersion]
  field_simp

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59 (**`d_t` vanishes to first order**): along the family
`p(i) = p̄ + s z(i)`, `d(0) = 0` and `d'(0) = 0`. -/
theorem dispersion_family_first_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (pbar : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 ∧
      HasDerivAt (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) 0 0 := by
  have hd0 : dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 := by
    rw [dispersion_family_eq hz hB (by linarith) (by linarith)]
    simp [cgf_zero]
  refine ⟨hd0, ?_⟩
  rw [hasDerivAt_iff_isLittleO, hd0]
  have h2 := dispersion_family_isBigO_sq (μ := μ) hz hB hε hα0 hα1 pbar
  have h21 : (fun s : ℝ => s ^ 2) =o[nhds 0] fun s => s ^ 1 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 1 < 2)
  simpa using h2.trans_isLittleO h21

/-- Galí (2015), (32), p. 237 (**exact**): with production `Y(i) = A N(i)^{1−α}` and output
on the demand schedule, `y = a + (1 − α)n − d` with `n = log ∫ N(i) di` and `d` the
price-dispersion term. -/
theorem eq32_exact (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α))
    (hD : 0 < ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) :
    Real.log Y = Real.log A + (1 - α) * Real.log (∫ i, N i ∂μ) - dispersion μ α ε P := by
  rw [employment_identity hα1 hP hpos hA hY hN hprod hD]
  ring

/-- Galí (2015), **(32)**, p. 237: when the dispersion term vanishes (it is zero, with zero
derivative, at a symmetric price distribution: `dispersion_family_first_order`),
`y = a + (1 − α)n`. -/
theorem eq32 {α y a n d : ℝ} (h : y = a + (1 - α) * n - d) (hd : d = 0) :
    y = a + (1 - α) * n := by
  rw [h, hd, sub_zero]

/-! ### Markups and inflation, (33)–(34) -/

/-- Galí (2015), **(33)**, p. 237: the average markup (constants dropped)
`μ = p_H − (w − a + αn)`, with the labour supply condition (7) `w − p = σc + φn`, the CPI
identity (12) `p − p_H = υs`, risk sharing (17), goods-market clearing (25) and the
production function (32), equals
`−(σ + (φ+α)/(1−α))y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α))a − υz`. -/
theorem eq33 {σ η υ φ α mu pH w p a n c s y ystar z : ℝ} (hσ : σ ≠ 0) (hα : α < 1)
    (hmu : mu = pH - (w - a + α * n)) (h7 : w - p = σ * c + φ * n) (h12 : p - pH = υ * s)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) (h32 : y = a + (1 - α) * n) :
    mu = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s
      + (1 + (φ + α) / (1 - α)) * a - υ * z := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have key : σ * (y - ystar) = (1 - υ) * z + (1 + υ * (varpi σ η υ - 1)) * s := by
    rw [h25, h17]
    unfold varpi
    field_simp
    ring
  rw [hmu]
  linear_combination (norm := skip) (-1 : ℝ) * h7 - h12 - σ * h17 + key
    + ((φ + α) / (1 - α)) * h32
  field_simp
  ring

/-- Galí (2015), p. 237: `κ ≡ λ(σ + (φ+α)/(1−α))`, the closed-economy slope of Chapter 3. -/
noncomputable def kappa (lam σ φ α : ℝ) : ℝ := lam * (σ + (φ + α) / (1 - α))

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), **(34)**, p. 237: combining (22) `π_{H,t} = βE_t π_{H,t+1} − λμ̂_t` with the
markup (33) gives
`π_{H,t} = βE_t π_{H,t+1} + κy_t − λυ(ϖ − 1)s_t − λ(1 + (φ+α)/(1−α))a_t + λυz_t`. -/
theorem eq34 {lam β σ η υ φ α : ℝ} {inflH mu y s a z : ℕ → Ω → ℝ} (t : ℕ)
    (h22 : inflH t = β • 𝔼.E t (inflH (t + 1)) - lam • mu t)
    (h33 : mu t = (-(σ + (φ + α) / (1 - α))) • y t + (υ * (varpi σ η υ - 1)) • s t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t) :
    inflH t = β • 𝔼.E t (inflH (t + 1)) + kappa lam σ φ α • y t
      - (lam * υ * (varpi σ η υ - 1)) • s t - (lam * (1 + (φ + α) / (1 - α))) • a t
      + (lam * υ) • z t := by
  rw [h22, h33]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappa]
  ring

/-! ### Natural output, (35) -/

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` of the `Γ` coefficients. -/
noncomputable def natDen (σ η υ φ α : ℝ) : ℝ := sigmaU σ η υ * (1 - α) + φ + α

/-- Galí (2015), (35), p. 238: `Γ_a ≡ (1 + φ)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaA (σ η υ φ α : ℝ) : ℝ := (1 + φ) / natDen σ η υ φ α

/-- Galí (2015), (35), p. 238: `Γ_* ≡ −υ(ϖ − 1)σ_υ(1 − α)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaStar (σ η υ φ α : ℝ) : ℝ :=
  -(υ * (varpi σ η υ - 1) * sigmaU σ η υ * (1 - α)) / natDen σ η υ φ α

/-- Galí (2015), (35), p. 238: `Γ_z ≡ −υϖΦ(1 − α)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaZ (σ η υ φ α : ℝ) : ℝ :=
  -(υ * varpi σ η υ * Phi σ η υ * (1 - α)) / natDen σ η υ φ α

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` is positive. -/
theorem natDen_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < natDen σ η υ φ α := by
  unfold natDen
  have := mul_pos (sigmaU_pos hσ hη hυ0 hυ1) (sub_pos.2 hα1)
  linarith

/-- Galí (2015), (35), p. 238: `Γ_a > 0`. -/
theorem GammaA_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < GammaA σ η υ φ α :=
  div_pos (by linarith) (natDen_pos hσ hη hυ0 hυ1 hφ hα0 hα1)

/-- Galí (2015), p. 238, **the key identity** `σ − υ(ϖ − 1)σ_υ = σ_υ`. -/
theorem sigma_sub_eq_sigmaU {σ η υ : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) :
    σ - υ * (varpi σ η υ - 1) * sigmaU σ η υ = sigmaU σ η υ := by
  have := sigmaU_mul hD
  linear_combination -this

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_a = 1 + (φ+α)/(1−α)`. -/
theorem mul_GammaA {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaA σ η υ φ α = 1 + (φ + α) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaA
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_* = −υ(ϖ − 1)σ_υ`. -/
theorem mul_GammaStar {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaStar σ η υ φ α
      = -(υ * (varpi σ η υ - 1) * sigmaU σ η υ) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaStar
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_z = −υϖΦ`. -/
theorem mul_GammaZ {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaZ σ η υ φ α
      = -(υ * varpi σ η υ * Phi σ η υ) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaZ
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: after substituting the natural terms of trade (27), the
markup (33) at natural output equals `−(σ_υ + (φ+α)/(1−α))(yⁿ − Γ_a a − Γ_z z − Γ_*y*)`. -/
theorem markup_natural {σ η υ φ α yn a z ystar : ℝ} (hα : α ≠ 1)
    (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) (hden : natDen σ η υ φ α ≠ 0) :
    -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) *
        (sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z)
      + (1 + (φ + α) / (1 - α)) * a - υ * z
    = -(sigmaU σ η υ + (φ + α) / (1 - α)) *
        (yn - (GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar)) := by
  have pA := mul_GammaA hα hden
  have pS := mul_GammaStar hα hden
  have pZ := mul_GammaZ hα hden
  have hσD := sigmaU_mul hD
  have hΦD : Phi σ η υ * (1 + υ * (varpi σ η υ - 1)) = 1 := by
    unfold Phi
    field_simp
  linear_combination (-a) * pA + (-z) * pZ + (-ystar) * pS + yn * hσD + (υ * z) * hΦD

/-- Galí (2015), **(35)**, p. 238: with the natural terms of trade given by (27),
`sⁿ = σ_υ(yⁿ − y*) − (1 − υ)Φz`, the flexible-price markup condition (the markup (33) at its
steady-state value, zero once constants are dropped) holds **if and only if**
`yⁿ = Γ_a a + Γ_z z + Γ_* y*`. -/
theorem eq35_iff {σ η υ φ α yn sn a z ystar : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h27 : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    0 = -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) * sn
      + (1 + (φ + α) / (1 - α)) * a - υ * z ↔
    yn = GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar := by
  have hD := (one_add_mul_varpi_pos hσ hη hυ0 hυ1).ne'
  have hden := (natDen_pos hσ hη hυ0 hυ1 hφ hα0 hα1).ne'
  have hk : 0 < sigmaU σ η υ + (φ + α) / (1 - α) :=
    add_pos_of_pos_of_nonneg (sigmaU_pos hσ hη hυ0 hυ1) (div_nonneg (by linarith)
      (by linarith))
  rw [h27, markup_natural hα1.ne hD hden]
  constructor
  · intro h
    have h0 := h.symm
    rcases mul_eq_zero.1 h0 with h1 | h1
    · linarith
    · linarith
  · intro h
    rw [h]
    ring

/-- Galí (2015), p. 238: **with `σ = η = 1`, world output does not affect natural output**,
`Γ_* = 0`. -/
theorem GammaStar_unit (υ φ α : ℝ) : GammaStar 1 1 υ φ α = 0 := by
  simp [GammaStar, varpi]

/-- Galí (2015), p. 238: **with `σ = η = 1`, preference shocks lower natural output**,
`Γ_z < 0`, provided the economy is open (`υ > 0`; `Γ_z = 0` at `υ = 0`, fn. 8). -/
theorem GammaZ_unit_neg {υ φ α : ℝ} (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) : GammaZ 1 1 υ φ α < 0 := by
  have hden := natDen_pos one_pos one_pos hυ0.le hυ1 hφ hα0 hα1
  have hΦ := Phi_pos (σ := 1) (η := 1) one_pos one_pos hυ0.le hυ1
  have hv : varpi 1 1 υ = 1 := by simp [varpi]
  unfold GammaZ
  rw [hv]
  apply div_neg_of_neg_of_pos _ hden
  have : 0 < υ * 1 * Phi 1 1 υ * (1 - α) := by
    have := sub_pos.2 hα1
    positivity
  linarith

/-- Galí (2015), fn. 8, p. 238: in the closed economy (`υ = 0`), `Γ_z = 0`. -/
theorem GammaZ_zero (σ η φ α : ℝ) : GammaZ σ η 0 φ α = 0 := by
  simp [GammaZ]

/-- Galí (2015), p. 238: in the closed economy (`υ = 0`), `Γ_* = 0`. -/
theorem GammaStar_zero (σ η φ α : ℝ) : GammaStar σ η 0 φ α = 0 := by
  simp [GammaStar]

/-! ### The open-economy New Keynesian Phillips curve, (36)–(37) -/

/-- Galí (2015), p. 238: subtracting (27) at the natural level gives the terms-of-trade gap
`s̃ = σ_υỹ`. -/
theorem sgap_eq {σ η υ s sn y yn ystar z : ℝ}
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h27n : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    s - sn = sigmaU σ η υ * (y - yn) := by
  rw [h27, h27n]
  ring

/-- Galí (2015), **(36)**, p. 238: subtracting the markup (33) at the natural level from the
actual markup and using `s̃ = σ_υỹ`, `μ̂ = −(σ_υ + (φ+α)/(1−α))ỹ`. -/
theorem eq36 {σ η υ φ α mu mun y yn s sn a z ystar : ℝ}
    (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (h33 : mu = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s
      + (1 + (φ + α) / (1 - α)) * a - υ * z)
    (h33n : mun = -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) * sn
      + (1 + (φ + α) / (1 - α)) * a - υ * z)
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h27n : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    mu - mun = -(sigmaU σ η υ + (φ + α) / (1 - α)) * (y - yn) := by
  have hk := sigma_sub_eq_sigmaU hD
  have hs := sgap_eq h27 h27n
  rw [h33, h33n]
  linear_combination (υ * (varpi σ η υ - 1)) * hs - (y - yn) * hk

/-- Galí (2015), (37), p. 238: `κ_υ ≡ λ(σ_υ + (φ+α)/(1−α))`. -/
noncomputable def kappaU (lam σ η υ φ α : ℝ) : ℝ := lam * (sigmaU σ η υ + (φ + α) / (1 - α))

/-- Galí (2015), **(37)**, p. 238: the New Keynesian Phillips curve of the small open
economy. If domestic inflation satisfies (22) `π_{H,t} = βE_t π_{H,t+1} − λμ̂_t` with the
markup gap `μ̂_t = μ_t − μⁿ_t`, the markups are given by (33) at the actual and the natural
allocation, and the terms of trade by (27) in both, then
`π_{H,t} = βE_t π_{H,t+1} + κ_υ ỹ_t`, `ỹ_t = y_t − yⁿ_t`. -/
theorem eq37 {lam β σ η υ φ α : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {inflH mu mun y yn s sn a z ystar : ℕ → Ω → ℝ} (t : ℕ)
    (h22 : inflH t = β • 𝔼.E t (inflH (t + 1)) - lam • (mu t - mun t))
    (h33 : mu t = (-(σ + (φ + α) / (1 - α))) • y t + (υ * (varpi σ η υ - 1)) • s t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t)
    (h33n : mun t = (-(σ + (φ + α) / (1 - α))) • yn t + (υ * (varpi σ η υ - 1)) • sn t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t)
    (h27 : s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t)
    (h27n : sn t = sigmaU σ η υ • (yn t - ystar t) - ((1 - υ) * Phi σ η υ) • z t) :
    inflH t = β • 𝔼.E t (inflH (t + 1)) + kappaU lam σ η υ φ α • (y t - yn t) := by
  rw [h22]
  funext ω
  have e1 := congrFun h33 ω
  have e2 := congrFun h33n ω
  have e3 := congrFun h27 ω
  have e4 := congrFun h27n ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  have k := eq36 hD e1 e2 e3 e4
    (mu := mu t ω) (mun := mun t ω) (s := s t ω) (sn := sn t ω) (y := y t ω) (yn := yn t ω)
    (a := a t ω) (z := z t ω) (ystar := ystar t ω) (φ := φ) (α := α)
  unfold kappaU
  linear_combination (-lam) * k

/-- Galí (2015), p. 238: in the closed economy (`υ = 0`), `κ_υ = κ`. -/
theorem kappaU_zero (lam σ η φ α : ℝ) : kappaU lam σ η 0 φ α = kappa lam σ φ α := by
  simp [kappaU, kappa, sigmaU_zero]

/-- Galí (2015), p. 238: with `σ = η = 1`, `κ_υ = κ` for every degree of openness. -/
theorem kappaU_unit (lam υ φ α : ℝ) : kappaU lam 1 1 υ φ α = kappa lam 1 φ α := by
  simp [kappaU, kappa, sigmaU_of_sigma_mul_eta (σ := 1) (η := 1) (by norm_num)]

/-- Galí (2015), p. 239: **if `ση > 1`, an increase in openness lowers `κ_υ`**: `κ_υ` is
strictly decreasing in `υ` on `[0, 1]` (for `λ > 0`). -/
theorem kappaU_strictAntiOn {lam σ η φ α : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (hη : 0 < η)
    (h : 1 < σ * η) : StrictAntiOn (fun υ => kappaU lam σ η υ φ α) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have := sigmaU_strictAntiOn hσ hη h ha hb hab
  simp only [kappaU]
  nlinarith

/-! ### The natural rate of interest, (38) -/

/-- Galí (2015), (38), p. 239: `Ψ_* ≡ σ_υ(υ(ϖ − 1) + Γ_*)`. -/
noncomputable def PsiStar (σ η υ φ α : ℝ) : ℝ :=
  sigmaU σ η υ * (υ * (varpi σ η υ - 1) + GammaStar σ η υ φ α)

/-- Galí (2015), (38), p. 239: `Ψ_z ≡ (1 − υ)Φ − σ_υΓ_z`. -/
noncomputable def PsiZ (σ η υ φ α : ℝ) : ℝ :=
  (1 - υ) * Phi σ η υ - sigmaU σ η υ * GammaZ σ η υ φ α

/-- Galí (2015), **(38)**, p. 239: combining the natural rate (30) with natural output (35)
and AR(1) technology and preference shocks (`E_t a_{t+1} = ρ_a a_t`, `E_t z_{t+1} = ρ_z z_t`),
`rⁿ_t = ρ − σ_υΓ_a(1 − ρ_a)a_t + Ψ_*E_tΔy*_{t+1} + Ψ_z(1 − ρ_z)z_t`. -/
theorem eq38 {σ η υ φ α ρ ρz ρa : ℝ} {yn a z ystar : ℕ → Ω → ℝ} (t : ℕ)
    (hyn : ∀ t, yn t = GammaA σ η υ φ α • a t + GammaZ σ η υ φ α • z t
      + GammaStar σ η υ φ α • ystar t)
    (ha : 𝔼.E t (a (t + 1)) = ρa • a t) (hz : 𝔼.E t (z (t + 1)) = ρz • z t) :
    natRate 𝔼 σ η υ ρ ρz yn ystar z t
      = (fun _ => ρ) - (sigmaU σ η υ * GammaA σ η υ φ α * (1 - ρa)) • a t
        + PsiStar σ η υ φ α • (𝔼.E t (ystar (t + 1)) - ystar t)
        + (PsiZ σ η υ φ α * (1 - ρz)) • z t := by
  unfold natRate PsiStar PsiZ
  rw [hyn (t + 1), hyn t, map_add, map_add, map_smul, map_smul, map_smul, ha, hz]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 239: in the closed economy `Ψ_* = 0`. -/
theorem PsiStar_zero (σ η φ α : ℝ) : PsiStar σ η 0 φ α = 0 := by
  simp [PsiStar, GammaStar_zero]

/-- Galí (2015), p. 239: in the closed economy `Ψ_z = 1`. -/
theorem PsiZ_zero (σ η φ α : ℝ) : PsiZ σ η 0 φ α = 1 := by
  simp [PsiZ, GammaZ_zero, Phi]

/-- Galí (2015), p. 239: `σ_υ` is continuous in `υ` at `υ = 0`. -/
theorem continuousAt_sigmaU (σ η : ℝ) : ContinuousAt (fun υ => sigmaU σ η υ) 0 := by
  have hD : ContinuousAt (fun υ : ℝ => 1 + υ * (varpi σ η υ - 1)) 0 := by
    unfold varpi
    fun_prop
  have hPhi : ContinuousAt (fun υ => Phi σ η υ) 0 := continuousAt_const.div hD (by simp)
  exact continuousAt_const.mul hPhi

/-- Galí (2015), p. 239: **`lim_{υ→0} Ψ_* = 0`**. -/
theorem tendsto_PsiStar {σ η φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun υ => PsiStar σ η υ φ α) (𝓝 0) (𝓝 0) := by
  have hsig := continuousAt_sigmaU σ η
  have hvar : ContinuousAt (fun υ => varpi σ η υ) 0 := by
    unfold varpi
    fun_prop
  have hden0 : natDen σ η 0 φ α ≠ 0 := by
    unfold natDen
    rw [sigmaU_zero]
    have := mul_pos hσ (sub_pos.2 hα1)
    linarith
  have hden : ContinuousAt (fun υ => natDen σ η υ φ α) 0 := by
    unfold natDen
    fun_prop
  have hG : ContinuousAt (fun υ => GammaStar σ η υ φ α) 0 := by
    unfold GammaStar
    exact ((((continuousAt_id.mul (hvar.sub continuousAt_const)).mul hsig).mul
      continuousAt_const).neg).div hden hden0
  have hP : ContinuousAt (fun υ => PsiStar σ η υ φ α) 0 := by
    unfold PsiStar
    exact hsig.mul ((continuousAt_id.mul (hvar.sub continuousAt_const)).add hG)
  have := hP.tendsto
  rwa [PsiStar_zero] at this

/-- Galí (2015), p. 239: **`lim_{υ→0} Ψ_z = 1`**. -/
theorem tendsto_PsiZ {σ η φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun υ => PsiZ σ η υ φ α) (𝓝 0) (𝓝 1) := by
  have hsig := continuousAt_sigmaU σ η
  have hvar : ContinuousAt (fun υ => varpi σ η υ) 0 := by
    unfold varpi
    fun_prop
  have hD : ContinuousAt (fun υ : ℝ => 1 + υ * (varpi σ η υ - 1)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hvar.sub continuousAt_const))
  have hPhi : ContinuousAt (fun υ => Phi σ η υ) 0 := continuousAt_const.div hD (by simp)
  have hden0 : natDen σ η 0 φ α ≠ 0 := by
    unfold natDen
    rw [sigmaU_zero]
    have := mul_pos hσ (sub_pos.2 hα1)
    linarith
  have hden : ContinuousAt (fun υ => natDen σ η υ φ α) 0 := by
    unfold natDen
    fun_prop
  have hG : ContinuousAt (fun υ => GammaZ σ η υ φ α) 0 := by
    unfold GammaZ
    exact ((((continuousAt_id.mul hvar).mul hPhi).mul continuousAt_const).neg).div hden hden0
  have hP : ContinuousAt (fun υ => PsiZ σ η υ φ α) 0 := by
    unfold PsiZ
    exact ((continuousAt_const.sub continuousAt_id).mul hPhi).sub (hsig.mul hG)
  have := hP.tendsto
  rwa [PsiZ_zero] at this

end Gali.OpenEconomy.Supply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium dynamics under an interest-rate rule in the small open economy

Galí (2015), Chapter 8, §8.3, pp. 239–243. The non-policy block of the small
open economy is the domestic-inflation Phillips curve (37),
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t`, and the dynamic IS equation (29),
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)`, with
`σ_υ = σ / (1 + υ(ϖ − 1))`, `ϖ = ση + (1 − υ)(ση − 1)` and
`κ_υ = λ (σ_υ + (φ + α)/(1 − α))`. Policy follows the Taylor rule (39). The
system is the closed-economy system of Chapter 3 with `σ ↦ σ_υ`, `κ ↦ κ_υ`;
the closed-economy results are restated here from the Chapter 3 project
(`TaylorRuleSystem`, `ShockResponses`) for general `σ_υ, κ_υ > 0`.

## Main results

* `equilibrium_iff_solves`: (29), (37), (39) ⇔ the system (40)
  `x_t = A_υ E_t x_{t+1} + B_υ u_t`.
* `schurStable_AU_iff`, `determinate_iff_41`, `equilibrium_unique`,
  `equilibrium_not_unique`: determinacy ⇔ (41) `κ_υ(φ_π − 1) + (1 − β)φ_y > 0`.
* `equilibrium_iff_msv`, `monetary_shock`: the unique bounded equilibrium after a
  monetary shock (p. 241), `ỹ = −(1 − βρ_v)Λ_v v`, `π_H = −κ_υΛ_v v`, with the
  nominal and real rate responses; `msvLambda_pos`: `Λ_v > 0` under (41).
* `monetary_tot`, `monetary_exchangeRate`: `s = σ_υ ỹ` and `Δe_t` (pp. 241–242).
* `expected_inflation_hasSum`, `priceLevel_longRun`, `exchangeRate_longRun_change`:
  the permanent price-level fall `κ_υΛ_v/(1 − ρ_v)` (p. 242).
* `overshoot_iff`, `overshoot_iff_nominal_rises`: overshooting ⇔
  `σ_υ(1 − βρ_v)(1 − ρ_v) > κ_υρ_v` ⇔ the nominal rate rises on impact.
* `lambdaV_lt_of_slope_pos`, `lambdaV_strictMonoOn` (corrected p. 241 claim) and
  `counterexample_strictAntiOn`, `printed_monotonicity_false` (survey error 3):
  `ση > 1` alone does not make `Λ_v` increasing in openness.
* `closed_economy_equivalence`, `closed_economy_responses` (p. 243): with
  `ση = 1` (in particular `σ = η = 1`) the output-gap and domestic-inflation
  responses are those of the closed economy.
-/

namespace Gali.OpenEconomy.TaylorRule

open Filter Topology
open Gali.OpenEconomy.AggregateDemand (varpi Phi sigmaU varpi_sub_one one_add_mul_varpi_pos
  sigmaU_pos sigmaU_of_sigma_mul_eta sigmaU_strictAntiOn)
open Gali.OpenEconomy.Supply (kappaU)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Open-economy coefficients in terms of primitives

`ϖ`, `Φ`, `σ_υ = σΦ` and their properties are `AggregateDemand.varpi`, `AggregateDemand.Phi`,
`AggregateDemand.sigmaU`; `κ_υ = λ(σ_υ + (φ + α)/(1 − α))` is `Supply.kappaU`. -/

/-- Galí (2015), p. 238: `κ_υ > 0` for `λ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaU_pos {lamC σ η υ varphi α : ℝ} (hlam : 0 < lamC) (hσ : 0 < σ) (hη : 0 < η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < kappaU lamC σ η υ varphi α := by
  have h1 := sigmaU_pos hσ hη hυ0 hυ1
  have h2 : 0 ≤ (varphi + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  unfold kappaU
  positivity

/-- Galí (2015), p. 238: if `ση = 1` then `κ_υ = κ ≡ λ(σ + (φ + α)/(1 − α))`. -/
theorem kappaU_of_mul_eq_one {lamC σ η varphi α : ℝ} (h : σ * η = 1) (υ : ℝ) :
    kappaU lamC σ η υ varphi α = lamC * (σ + (varphi + α) / (1 - α)) := by
  rw [kappaU, sigmaU_of_sigma_mul_eta h]

/-! ### The non-policy block and the rule -/

/-- Galí (2015), p. 240: the real interest rate in terms of domestic goods,
`r_t ≡ i_t − E_t π_{H,t+1}`. -/
def realRate (i infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), eq. (37), p. 238: the domestic-inflation Phillips curve
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t` (`kU` is `κ_υ`). -/
def NKPC (β kU : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + kU • ygap t

/-- Galí (2015), eq. (29), p. 236: the open-economy DIS equation in gap form,
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)` (`sU` is `σ_υ`). -/
def DISGap (sU : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -sU⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (39), p. 239: `i_t = ρ + φ_π π_{H,t} + φ_y y_t + v_t`. -/
def InterestRule (ρ φπ φy : ℝ) (i infl y v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • y t + v t

/-- Galí (2015), p. 240: the rule (39) with `y_t = ỹ_t + y^n_t`,
`i_t = ρ + φ_π π_{H,t} + φ_y ỹ_t + φ_y y^n_t + v_t`. -/
def InterestRuleGap (ρ φπ φy : ℝ) (i infl ygap yn v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yn t + v t

/-- Galí (2015), p. 240: since `y_t = ỹ_t + y^n_t`, rule (39) is the same as its
output-gap form. -/
theorem taylorRule_iff_gap {ρ φπ φy : ℝ} {i infl y ygap yn v : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = ygap t + yn t) :
    InterestRule ρ φπ φy i infl y v ↔ InterestRuleGap ρ φπ φy i infl ygap yn v := by
  simp only [InterestRule, InterestRuleGap, hy, smul_add, add_assoc]

/-- Galí (2015), p. 240: the composite shock of (40),
`u_t ≡ r̂^n_t − φ_y y^n_t − v_t` with `r̂^n_t = r^n_t − ρ`. -/
def shockU (ρ φy : ℝ) (rn yn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - φy • yn t - v t

/-- Galí (2015), §8.3, pp. 239–240: an equilibrium under rule (39): the NKPC (37),
the DIS (29) and the rule in gap form. -/
def Equilibrium (β sU kU ρ φπ φy : ℝ) (rn yn v ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β kU ygap infl ∧ DISGap 𝔼 sU ygap i infl rn ∧
    InterestRuleGap ρ φπ φy i infl ygap yn v

/-- Galí (2015), p. 240: the equilibrium conditions with the interest rate
substituted out, `(σ_υ + φ_y) ỹ_t + φ_π π_{H,t} = σ_υ E_t ỹ_{t+1} + E_t π_{H,t+1} + u_t`
together with the NKPC (37). -/
def Structural (β sU kU φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (sU + φy) • ygap t + φπ • infl t
      = sU • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + kU • ygap t

/-- Galí (2015), p. 240: `Ω_υ ≡ 1/(σ_υ + φ_y + κ_υ φ_π)`. -/
noncomputable def omegaU (sU kU φπ φy : ℝ) : ℝ := 1 / (sU + φy + kU * φπ)

/-- Galí (2015), eq. (40), p. 240:
`A_υ ≡ Ω_υ [[σ_υ, 1 − βφ_π], [σ_υκ_υ, κ_υ + β(σ_υ + φ_y)]]`. -/
noncomputable def AU (β sU kU φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omegaU sU kU φπ φy * sU, omegaU sU kU φπ φy * (1 - β * φπ);
    omegaU sU kU φπ φy * (sU * kU), omegaU sU kU φπ φy * (kU + β * (sU + φy))]

/-- Galí (2015), eq. (40), p. 240: `B_υ ≡ Ω_υ (1, κ_υ)`. -/
noncomputable def BU (sU kU φπ φy : ℝ) : Fin 2 → ℝ :=
  ![omegaU sU kU φπ φy, omegaU sU kU φπ φy * kU]

/-- Galí (2015), eq. (40): the stacked vector `x_t = (ỹ_t, π_{H,t})`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (40): the forcing term `B_υ u_t`. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), p. 240: with the rule in gap form, (37) and (29) hold if and only
if the structural equations hold with `u_t = r̂^n_t − φ_y y^n_t − v_t`
(restated from the Chapter 3 project). -/
theorem nk_iff_structural {β sU kU ρ φπ φy : ℝ} (hσ : sU ≠ 0)
    {rn yn v ygap infl i : ℕ → Ω → ℝ} (hrule : InterestRuleGap ρ φπ φy i infl ygap yn v) :
    (NKPC 𝔼 β kU ygap infl ∧ DISGap 𝔼 sU ygap i infl rn) ↔
      Structural 𝔼 β sU kU φπ φy (shockU ρ φy rn yn v) ygap infl := by
  have hinv : sU * sU⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination sU * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination sU⁻¹ * e + sU⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eq. (40), p. 240: the structural equations are equivalent to
`x_t = A_υ E_t x_{t+1} + B_υ u_t`, provided `σ_υ + φ_y + κ_υ φ_π ≠ 0`. -/
theorem structural_iff_solves {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β sU kU φπ φy u ygap infl ↔
      𝔼.Solves (AU β sU kU φπ φy) (forcing (BU sU kU φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AU, BU, omegaU]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AU, BU, omegaU]
      field_simp
      linear_combination kU * e1 + (sU + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AU, omegaU, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BU] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (sU + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - kU * e0

/-- Galí (2015), eq. (40), p. 240: with the rule (39) in gap form, `(ỹ, π_H)`
satisfies (37) and (29) if and only if it solves `x_t = A_υ E_t x_{t+1} + B_υ u_t`. -/
theorem equilibrium_iff_solves {β sU kU ρ φπ φy : ℝ} (hσ : sU ≠ 0)
    (hS : sU + φy + kU * φπ ≠ 0) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : InterestRuleGap ρ φπ φy i infl ygap yn v) :
    Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i ↔
      𝔼.Solves (AU β sU kU φπ φy) (forcing (BU sU kU φπ φy) (shockU ρ φy rn yn v))
        (stack ygap infl) := by
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hrule]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- Galí (2015), p. 240: `tr A_υ = (σ_υ(1 + β) + κ_υ + βφ_y)/(σ_υ + φ_y + κ_υφ_π)`. -/
theorem tr2_AU {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0) :
    tr2 (AU β sU kU φπ φy) = (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ) := by
  simp only [tr2, AU, omegaU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 240: `det A_υ = σ_υβ/(σ_υ + φ_y + κ_υφ_π)`. -/
theorem det2_AU {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0) :
    det2 (AU β sU kU φπ φy) = sU * β / (sU + φy + kU * φπ) := by
  simp only [det2, AU, omegaU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (41), p. 240 (Bullard–Mitra): for `σ_υ, κ_υ > 0`, `0 < β < 1`
and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_υ` lie inside the unit circle if and
only if `κ_υ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem schurStable_AU_iff {β sU kU φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AU β sU kU φπ φy)) (det2 (AU β sU kU φπ φy)) ↔
      0 < kU * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < sU + φy + kU * φπ := by positivity
  rw [tr2_AU hS.ne', det2_AU hS.ne']
  have hD0 : 0 < sU * β / (sU + φy + kU * φπ) := by positivity
  have hD1 : sU * β / (sU + φy + kU * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ)
        < 1 + sU * β / (sU + φy + kU * φπ)
      ↔ sU * (1 + β) + kU + β * φy < sU + φy + kU * φπ + sU * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), eq. (41), p. 240: the system (40) is determinate (at most one
bounded adapted solution for every forcing process) if and only if
`κ_υ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem determinate_iff_41 [Nonempty Ω] {β sU kU φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AU β sU kU φπ φy) ↔ 0 < kU * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Galí (2015), eq. (41) in primitives: determinacy of (40) with
`σ_υ = σ/(1 + υ(ϖ − 1))` and `κ_υ = λ(σ_υ + (φ + α)/(1 − α))`. -/
theorem determinate_iff_41_primitives [Nonempty Ω] {β lamC σ η υ varphi α φπ φy : ℝ}
    (hlam : 0 < lamC) (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AU β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy) ↔
      0 < kappaU lamC σ η υ varphi α * (φπ - 1) + (1 - β) * φy :=
  determinate_iff_41 𝔼 (sigmaU_pos hσ hη hυ0 hυ1)
    (kappaU_pos hlam hσ hη hυ0 hυ1 hφ hα0 hα1) hβ0 hβ1 hφπ hφy

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

/-- Galí (2015), p. 240: under (41), two equilibria with bounded adapted output gap
and domestic inflation, driven by the same exogenous processes, coincide (output
gap, domestic inflation and the nominal rate). -/
theorem equilibrium_unique {β sU kU ρ φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy)
    {rn yn v ygap infl i ygap' infl' i' : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (he' : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap' infl' i')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' ∧ i = i' := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS he'.2.2).mp he'
  have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41) hx hy
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  have h1 : ygap = ygap' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = infl' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [he.2.2 t, he'.2.2 t, h1, h2]

/-- Galí (2015), p. 240: if (41) fails, next to any equilibrium with bounded adapted
output gap and domestic inflation there is a second one. -/
theorem equilibrium_not_unique [Nonempty Ω] {β sU kU ρ φπ φy : ℝ} (hσ : 0 < sU)
    (hκ : 0 < kU) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h41 : kU * (φπ - 1) + (1 - β) * φy ≤ 0) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AU β sU kU φπ φy)) (det2 (AU β sU kU φπ φy)) := by
    rw [schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : InterestRuleGap ρ φπ φy
      (fun t => (fun _ => ρ) + φπ • infl' t + φy • ygap' t + φy • yn t + v t)
      infl' ygap' yn v := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The minimum-state-variable solution -/

/-- Galí (2015), p. 241: the denominator
`(1 − βρ_v)[σ_υ(1 − ρ_v) + φ_y] + κ_υ(φ_π − ρ_v)` of `Λ_v`. -/
def msvDen (β sU kU φπ φy ρv : ℝ) : ℝ := (1 - β * ρv) * (sU * (1 - ρv) + φy) + kU * (φπ - ρv)

/-- Galí (2015), p. 241: `Λ_v ≡ 1/((1 − βρ_v)[σ_υ(1 − ρ_v) + φ_y] + κ_υ(φ_π − ρ_v))`. -/
noncomputable def msvLambda (β sU kU φπ φy ρv : ℝ) : ℝ := 1 / msvDen β sU kU φπ φy ρv

/-- Galí (2015), p. 241: the MSV output-gap coefficient `(1 − βρ_u)Λ_u`. -/
noncomputable def msvPsiY (β sU kU φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β sU kU φπ φy ρu

/-- Galí (2015), p. 241: the MSV domestic-inflation coefficient `κ_υΛ_u`. -/
noncomputable def msvPsiPi (β sU kU φπ φy ρu : ℝ) : ℝ := kU * msvLambda β sU kU φπ φy ρu

/-- Galí (2015), p. 241: the denominator of `Λ_v` equals
`(1 − ρ_v)((1 − βρ_v)σ_υ + κ_υ + βφ_y) + [κ_υ(φ_π − 1) + (1 − β)φ_y]`. -/
theorem msvDen_eq (β sU kU φπ φy ρv : ℝ) :
    msvDen β sU kU φπ φy ρv
      = (1 - ρv) * ((1 - β * ρv) * sU + kU + β * φy) + (kU * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 241: under (41) and `ρ_v < 1` the denominator of `Λ_v` is
positive. -/
theorem msvDen_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β sU kU φπ φy ρv := by
  rw [msvDen_eq]
  have hbr : β * ρv < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρv) * sU := by nlinarith
  have h2 : 0 ≤ (1 - ρv) * ((1 - β * ρv) * sU + kU + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 241: "as long as (41) is satisfied, `Λ_v > 0`" (for `ρ_v < 1`). -/
theorem msvLambda_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < msvLambda β sU kU φπ φy ρv :=
  one_div_pos.mpr (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41)

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- A scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {s : ℕ → Ω → ℝ} (hs : BoundedProc s) (c : ℝ) :
    BoundedProc (fun t => c • s t) := by
  obtain ⟨M, hM⟩ := hs
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 241 (undetermined coefficients): for an AR(1) composite shock
the MSV processes `ỹ_t = (1 − βρ_u)Λ_u u_t`, `π_{H,t} = κ_υΛ_u u_t` satisfy the
structural equations (existence). -/
theorem msv_structural {β sU kU φπ φy ρu : ℝ} (hD : msvDen β sU kU φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β sU kU φπ φy u (fun t => msvPsiY β sU kU φπ φy ρu • u t)
      (fun t => msvPsiPi β sU kU φπ φy ρu • u t) := by
  have c1 : (sU + φy) * msvPsiY β sU kU φπ φy ρu + φπ * msvPsiPi β sU kU φπ φy ρu
      = sU * (msvPsiY β sU kU φπ φy ρu * ρu) + msvPsiPi β sU kU φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β sU kU φπ φy ρu
      = β * (msvPsiPi β sU kU φπ φy ρu * ρu) + kU * msvPsiY β sU kU φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 241: under (41), for a bounded AR(1) composite shock with
`ρ_u < 1`, every bounded adapted solution of the structural equations is the MSV
solution (uniqueness). -/
theorem msv_unique {β sU kU φπ φy ρu : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {u ygap infl : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hub : BoundedProc u)
    (hs : Structural 𝔼 β sU kU φπ φy u ygap infl) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun t => msvPsiY β sU kU φπ φy ρu • u t) ∧
      infl = (fun t => msvPsiPi β sU kU φπ φy ρu • u t) := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
    ((structural_iff_solves 𝔼 hS _ _ _).mp (msv_structural 𝔼 hD hu))
    (adaptedVec_stack 𝔼 ha hb)
    (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hu _).1 (isAR1_smul 𝔼 hu _).1)
    (boundedVec_stack hba hbb) (boundedVec_stack (boundedProc_smul hub _)
      (boundedProc_smul hub _))
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- Galí (2015), pp. 240–241: under (41), with a bounded AR(1) composite shock of
persistence `ρ_u < 1`, a triple `(ỹ, π_H, i)` with bounded adapted `ỹ`, `π_H` is an
equilibrium if and only if it is the MSV solution with `i` given by the rule; the
MSV triple is bounded and adapted, so it is the unique bounded equilibrium. -/
theorem equilibrium_iff_msv {β sU kU ρ φπ φy ρu : ℝ} (hσ : 0 < sU) (hκ : 0 < kU)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {rn yn v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yn v)) (hub : BoundedProc (shockU ρ φy rn yn v))
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i ↔
      ygap = (fun t => msvPsiY β sU kU φπ φy ρu • shockU ρ φy rn yn v t) ∧
      infl = (fun t => msvPsiPi β sU kU φπ φy ρu • shockU ρ φy rn yn v t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yn t + v t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h41 hu hub
      ((nk_iff_structural 𝔼 hσ.ne' he.2.2).mp ⟨he.1, he.2.1⟩) ha hb hba hbb
    exact ⟨h1, h2, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : InterestRuleGap ρ φπ φy i infl ygap yn v := fun t => by rw [h3]
    have hs := (nk_iff_structural 𝔼 (β := β) (kU := kU) (rn := rn) hσ.ne' hrule).mpr
      (h1 ▸ h2 ▸ msv_structural 𝔼 hD hu)
    exact ⟨hs.1, hs.2, hrule⟩

/-! ### Monetary policy shock (§8.3.1, pp. 241–242) -/

/-- Galí (2015), p. 241: output-gap response `−(1 − βρ_v)Λ_v`. -/
noncomputable def monYgapCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -((1 - β * ρv) * msvLambda β sU kU φπ φy ρv)

/-- Galí (2015), p. 241: domestic-inflation response `−κ_υΛ_v`. -/
noncomputable def monInflCoef (β sU kU φπ φy ρv : ℝ) : ℝ := -(kU * msvLambda β sU kU φπ φy ρv)

/-- Galí (2015), p. 241: real-rate response; the book's bracket
`1 − Λ_v((φ_π − ρ_v)κ_υ + φ_y(1 − βρ_v))` equals `Λ_v(1 − βρ_v)σ_υ(1 − ρ_v)`
(`monRealCoef_eq_book`). -/
noncomputable def monRealCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  msvLambda β sU kU φπ φy ρv * (1 - β * ρv) * sU * (1 - ρv)

/-- Galí (2015), p. 241: nominal-rate response; the book's bracket
`1 − Λ_v(φ_πκ_υ + φ_y(1 − βρ_v))` equals `Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v]`
(`monNomCoef_eq_book`). -/
noncomputable def monNomCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) * (1 - ρv) - kU * ρv)

/-- Galí (2015), p. 241: the real-rate bracket in the book's form,
`1 − Λ_v((φ_π − ρ_v)κ_υ + φ_y(1 − βρ_v)) = Λ_v(1 − βρ_v)σ_υ(1 − ρ_v)`. -/
theorem monRealCoef_eq_book {β sU kU φπ φy ρv : ℝ} (hD : msvDen β sU kU φπ φy ρv ≠ 0) :
    1 - msvLambda β sU kU φπ φy ρv * ((φπ - ρv) * kU + φy * (1 - β * ρv))
      = monRealCoef β sU kU φπ φy ρv := by
  unfold monRealCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- Galí (2015), p. 241: the nominal-rate bracket in the book's form,
`1 − Λ_v(φ_πκ_υ + φ_y(1 − βρ_v)) = Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v]`. -/
theorem monNomCoef_eq_book {β sU kU φπ φy ρv : ℝ} (hD : msvDen β sU kU φπ φy ρv ≠ 0) :
    1 - msvLambda β sU kU φπ φy ρv * (φπ * kU + φy * (1 - β * ρv))
      = monNomCoef β sU kU φπ φy ρv := by
  unfold monNomCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- Galí (2015), p. 241: "the real rate increases unambiguously ... because the term
in square brackets is always positive": `Λ_v(1 − βρ_v)σ_υ(1 − ρ_v) > 0` under (41). -/
theorem monRealCoef_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < monRealCoef β sU kU φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h41
  have hbr : 0 < 1 - β * ρv := by nlinarith
  have h1 : 0 < 1 - ρv := by linarith
  unfold monRealCoef
  positivity

/-- **Monetary policy shock** (Galí 2015, p. 241): with `r^n_t = ρ` and `y^n_t = 0`,
an AR(1) monetary shock `v` with `ρ_v < 1` and (41), every equilibrium with bounded
adapted `ỹ`, `π_H` has `ỹ_t = −(1 − βρ_v)Λ_v v_t`, `π_{H,t} = −κ_υΛ_v v_t`,
`r_t − ρ = Λ_v(1 − βρ_v)σ_υ(1 − ρ_v) v_t` and
`i_t − ρ = Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v] v_t`. -/
theorem monetary_shock {β sU kU ρ φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yn t = 0) (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    (∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, i t - (fun _ => ρ) = monNomCoef β sU kU φπ φy ρv • v t) := by
  have hU : shockU ρ φy rn yn v = fun t => (-1 : ℝ) • v t := by
    funext t
    simp [shockU, hrn, hyn]
  have hu : 𝔼.IsAR1 ρv (shockU ρ φy rn yn v) := by rw [hU]; exact isAR1_smul 𝔼 hv _
  have hub : BoundedProc (shockU ρ φy rn yn v) := by rw [hU]; exact boundedProc_smul hvb _
  obtain ⟨h1, h2, -⟩ :=
    (equilibrium_iff_msv 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h41 hu hub ha hb hba hbb).mp he
  have hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t := fun t => by
    rw [h1, hU]; simp only [smul_smul, monYgapCoef, msvPsiY, mul_neg_one]
  have hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t := fun t => by
    rw [h2, hU]; simp only [smul_smul, monInflCoef, msvPsiPi, mul_neg_one]
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  have hLD : msvLambda β sU kU φπ φy ρv * msvDen β sU kU φπ φy ρv = 1 := by
    unfold msvLambda; field_simp
  have hinv : sU * sU⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hr : ∀ t, realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β sU kU φπ φy ρv • v t := by
    intro t
    have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hv.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    simp only [monYgapCoef, monRealCoef] at e ⊢
    linear_combination sU * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - ρ) * hinv
  refine ⟨hy, hp, hr, fun t => ?_⟩
  have h := hr t
  rw [realRate, hp (t + 1), map_smul, hv.2 t] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  simp only [monInflCoef, monRealCoef, monNomCoef] at e ⊢
  linear_combination e

/-- Galí (2015), p. 241: under (41) a monetary tightening lowers the output gap and
domestic inflation and raises the real rate. -/
theorem monetary_signs {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1) (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) :
    monYgapCoef β sU kU φπ φy ρv < 0 ∧ monInflCoef β sU kU φπ φy ρv < 0 ∧
      0 < monRealCoef β sU kU φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h41
  have hbr : 0 < 1 - β * ρv := by nlinarith
  refine ⟨?_, ?_, monRealCoef_pos hσ hκ hβ0 hβ1 hφy hρ1 h41⟩
  · unfold monYgapCoef; nlinarith [mul_pos hbr hL]
  · unfold monInflCoef; nlinarith [mul_pos hκ hL]

/-- Galí (2015), pp. 241–242, using (27) with `y^n = y* = 0` and no preference
shock: the terms of trade are `s_t = σ_υ ỹ_t = −σ_υ(1 − βρ_v)Λ_v v_t`. -/
theorem monetary_tot {sU β kU φπ φy ρv : ℝ} {ygap s v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (t : ℕ) : s t = (-(sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv)) • v t := by
  rw [hs, hy, smul_smul, monYgapCoef]
  congr 1
  ring

/-- Galí (2015), p. 242: with the terms of trade `s_t = e_t − p_{H,t}` (eq. (14),
`p* = 0`) and `p_{H,t+1} = p_{H,t} + π_{H,t+1}`, the nominal exchange rate moves by
`Δe_{t+1} = −Λ_v[σ_υ(1 − βρ_v) + κ_υ]v_{t+1} + σ_υ(1 − βρ_v)Λ_v v_t`. -/
theorem monetary_exchangeRate {sU β kU φπ φy ρv : ℝ} {ygap infl s e pH v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (t : ℕ) :
    e (t + 1) - e t
      = (-(msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) + kU))) • v (t + 1)
        + (sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv) • v t := by
  have e1 : e (t + 1) = s (t + 1) + pH (t + 1) := by rw [h14]; abel
  have e0 : e t = s t + pH t := by rw [h14]; abel
  rw [e1, e0, hpH, monetary_tot hs hy, monetary_tot hs hy, hp]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, monInflCoef]
  ring

/-! ### Long-run price level and exchange-rate overshooting (p. 242) -/

/-- Galí (2015), p. 242: the domestic price level is the sum of inflation,
`p_{H,t+1+k} = p_{H,t} + Σ_{j ≤ k} π_{H,t+1+j}`. -/
theorem priceLevel_sum {pH infl : ℕ → Ω → ℝ} (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (t k : ℕ) :
    pH (t + 1 + k) = pH t + ∑ j ∈ Finset.range (k + 1), infl (t + 1 + j) := by
  induction k with
  | zero => simp [hp t]
  | succ k ih =>
    have h : t + 1 + (k + 1) = (t + 1 + k) + 1 := by omega
    rw [h, hp, ih, Finset.sum_range_succ _ (k + 1), add_assoc, ← h]

/-- Galí (2015), p. 242: the expected price-level path after a monetary shock,
`E_{t+1} p_{H,t+1+k} = p_{H,t} + (Σ_{j ≤ k} c ρ_vʲ) v_{t+1}` when `π_H = c v`. -/
theorem expected_priceLevel {ρv c : ℝ} {pH infl v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH)
    (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (hinfl : ∀ t, infl t = c • v t)
    (hv : 𝔼.IsAR1 ρv v) (t k : ℕ) :
    𝔼.E (t + 1) (pH (t + 1 + k))
      = pH t + (∑ j ∈ Finset.range (k + 1), c * ρv ^ j) • v (t + 1) := by
  have h0 : 𝔼.E (t + 1) (pH t) = pH t := by
    have := 𝔼.known (Nat.le_succ t) (pH t)
    rwa [hpa t] at this
  rw [priceLevel_sum hp, map_add, h0, map_sum, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinfl, map_smul, 𝔼.ar1_iterate hv, smul_smul]

/-- Galí (2015), p. 242: the expected cumulative domestic inflation after a monetary
shock converges: `Σ_k E_t π_{H,t+k} = −κ_υΛ_v/(1 − ρ_v) · v_t` (for `0 ≤ ρ_v < 1`). -/
theorem expected_inflation_hasSum {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {infl v : ℕ → Ω → ℝ} (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (infl (t + k)) ω)
      (-(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v t ω) := by
  have hg := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
    (monInflCoef β sU kU φπ φy ρv)).mul_right (v t ω)
  convert hg using 1
  · funext k
    rw [hinfl, map_smul, 𝔼.ar1_iterate hv, smul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
  · rw [monInflCoef, div_eq_mul_inv]

/-- Galí (2015), p. 242: the tsum form of the permanent price-level fall,
`∑' k, E_t π_{H,t+k} = −κ_υΛ_v/(1 − ρ_v) · v_t`. -/
theorem expected_inflation_tsum {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {infl v : ℕ → Ω → ℝ} (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (ω : Ω) :
    ∑' k, 𝔼.E t (infl (t + k)) ω = -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v t ω :=
  (expected_inflation_hasSum 𝔼 hρ0 hρ1 hinfl hv t ω).tsum_eq

/-- Galí (2015), p. 242: the permanent decrease in the domestic price level,
`E_{t+1} p_{H,t+1+k} → p_{H,t} − κ_υΛ_v/(1 − ρ_v) · v_{t+1}` as `k → ∞`. -/
theorem priceLevel_longRun {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {pH infl v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH) (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t) (hv : 𝔼.IsAR1 ρv v)
    (t : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E (t + 1) (pH (t + 1 + k)) ω) atTop
      (𝓝 (pH t ω + -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v (t + 1) ω)) := by
  have hg := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
    (monInflCoef β sU kU φπ φy ρv)).tendsto_sum_nat
  have hg' := ((hg.comp (tendsto_add_atTop_nat 1)).mul_const (v (t + 1) ω)).const_add (pH t ω)
  rw [monInflCoef, ← div_eq_mul_inv] at hg'
  refine hg'.congr fun k => ?_
  rw [expected_priceLevel 𝔼 hpa hp hinfl hv t k]
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, monInflCoef]

/-- Galí (2015), p. 242: the impact response of the nominal exchange rate to a unit
shock from rest, `−Λ_v[σ_υ(1 − βρ_v) + κ_υ]`. -/
noncomputable def eImpact (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -(msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) + kU))

/-- Galí (2015), p. 242: the long-run response of the nominal exchange rate (equal to
the price-level response), `−κ_υΛ_v/(1 − ρ_v)`. -/
noncomputable def eLongRun (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv)

/-- Galí (2015), p. 242: starting from rest (`v_t = 0`) the exchange rate jumps on
impact by `eImpact · v_{t+1}`. -/
theorem exchangeRate_impact {sU β kU φπ φy ρv : ℝ} {ygap infl s e pH v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (t : ℕ)
    (hv0 : v t = 0) : e (t + 1) - e t = eImpact β sU kU φπ φy ρv • v (t + 1) := by
  rw [monetary_exchangeRate hs hy hp h14 hpH t, hv0, smul_zero, add_zero, eImpact]

/-- Galí (2015), p. 242: the terms of trade revert, so the expected exchange rate
converges to the expected price level: starting from rest (`v_t = 0`),
`E_{t+1} e_{t+1+k} − e_t → −κ_υΛ_v/(1 − ρ_v) · v_{t+1}`. -/
theorem exchangeRate_longRun_change {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {ygap infl s e pH v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH)
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (hv0 : v t = 0) (ω : Ω) :
    Tendsto (fun k => 𝔼.E (t + 1) (e (t + 1 + k)) ω - e t ω) atTop
      (𝓝 (eLongRun β sU kU φπ φy ρv * v (t + 1) ω)) := by
  let cs := -(sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv)
  have hee : ∀ n, e n = s n + pH n := fun n => by rw [h14]; abel
  have het : e t ω = pH t ω := by
    rw [hee, monetary_tot hs hy t, hv0]; simp
  have hS : ∀ k, 𝔼.E (t + 1) (s (t + 1 + k)) ω = cs * ρv ^ k * v (t + 1) ω := fun k => by
    rw [monetary_tot hs hy, map_smul, 𝔼.ar1_iterate hv, smul_smul]
    simp only [Pi.smul_apply, smul_eq_mul, cs]
  have hsl : Tendsto (fun k => cs * ρv ^ k * v (t + 1) ω) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul cs).mul_const
      (v (t + 1) ω)
  have hpl := priceLevel_longRun 𝔼 hρ0 hρ1 hpa hpH hp hv t ω
  have hsum := (hsl.add hpl).sub_const (pH t ω)
  rw [zero_add, add_sub_cancel_left] at hsum
  rw [eLongRun]
  refine hsum.congr fun k => ?_
  rw [het, hee, map_add, Pi.add_apply, hS]

/-- Galí (2015), p. 242: the exchange rate **overshoots** (appreciates on impact by
more than in the long run) if and only if `σ_υ(1 − βρ_v)(1 − ρ_v) > κ_υρ_v`. -/
theorem overshoot_iff {β sU kU φπ φy ρv : ℝ} (hL : 0 < msvLambda β sU kU φπ φy ρv)
    (hρ1 : ρv < 1) :
    eImpact β sU kU φπ φy ρv < eLongRun β sU kU φπ φy ρv ↔
      kU * ρv < sU * (1 - β * ρv) * (1 - ρv) := by
  have h1 : 0 < 1 - ρv := by linarith
  unfold eImpact eLongRun
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ h1]
  constructor
  · intro h
    have : 0 < msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) * (1 - ρv) - kU * ρv) := by
      nlinarith
    have := pos_of_mul_pos_right this hL.le
    linarith
  · intro h
    have := mul_pos hL (show 0 < sU * (1 - β * ρv) * (1 - ρv) - kU * ρv by linarith)
    nlinarith

/-- Galí (2015), p. 242: the overshooting condition "corresponds to that for an
increase in the nominal interest rate": overshooting ⇔ `i` rises on impact. -/
theorem overshoot_iff_nominal_rises {β sU kU φπ φy ρv : ℝ}
    (hL : 0 < msvLambda β sU kU φπ φy ρv) (hρ1 : ρv < 1) :
    eImpact β sU kU φπ φy ρv < eLongRun β sU kU φπ φy ρv ↔
      0 < monNomCoef β sU kU φπ φy ρv := by
  rw [overshoot_iff hL hρ1, monNomCoef]
  constructor
  · intro h; exact mul_pos hL (by linarith)
  · intro h; have := pos_of_mul_pos_right h hL.le; linarith

/-! ### `Λ_v` and the degree of openness (p. 241; survey error 3) -/

/-- Galí (2015), p. 241: `Λ_v` as a function of the primitives, with
`σ_υ = σ/(1 + υ(ϖ − 1))` and `κ_υ = λ(σ_υ + (φ + α)/(1 − α))`. -/
noncomputable def lambdaV (β lamC σ η varphi α φπ φy ρv υ : ℝ) : ℝ :=
  msvLambda β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv

/-- Galí (2015), p. 241: `1/Λ_v` is affine in `σ_υ` with slope
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v)`. -/
theorem msvDen_affine (β lamC sU m φπ φy ρv : ℝ) :
    msvDen β sU (lamC * (sU + m)) φπ φy ρv
      = sU * ((1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
        + ((1 - β * ρv) * φy + lamC * m * (φπ - ρv)) := by
  unfold msvDen; ring

/-- **Corrected p. 241 claim** (pairwise): if `ση > 1` and
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) > 0`, then for `0 ≤ υ₁ < υ₂ ≤ 1` with (41) at
`υ₂`, `Λ_v(υ₁) < Λ_v(υ₂)`: more openness amplifies the monetary shock. -/
theorem lambdaV_lt_of_slope_pos {β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : 0 < (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
    (h1 : υ₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : υ₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : υ₁ < υ₂)
    (h41 : 0 < kappaU lamC σ η υ₂ varphi α * (φπ - 1) + (1 - β) * φy) :
    lambdaV β lamC σ η varphi α φπ φy ρv υ₁ < lambdaV β lamC σ η varphi α φπ φy ρv υ₂ := by
  have hD2 := msvDen_pos (sigmaU_pos hσ hη h2.1 h2.2)
    (kappaU_pos hlam hσ hη h2.1 h2.2 hφ hα0 hα1) hβ0 hβ1 hφy hρ1 h41
  have hs := sigmaU_strictAntiOn hσ hη hση h1 h2 h12
  unfold lambdaV msvLambda
  unfold kappaU at hD2 ⊢
  simp only [msvDen_affine] at hD2 ⊢
  apply one_div_lt_one_div_of_lt hD2
  nlinarith

/-- **Corrected p. 241 claim**: if `ση > 1`, `(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) > 0`
(e.g. `φ_π ≥ ρ_v`) and (41) holds on `[0, 1]`, then `Λ_v` is strictly increasing in
the degree of openness `υ ∈ [0, 1]`. -/
theorem lambdaV_strictMonoOn {β lamC σ η varphi α φπ φy ρv : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : 0 < (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
    (h41 : ∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU lamC σ η υ varphi α * (φπ - 1) + (1 - β) * φy) :
    StrictMonoOn (lambdaV β lamC σ η varphi α φπ φy ρv) (Set.Icc 0 1) :=
  fun _ h1 υ₂ h2 h12 => lambdaV_lt_of_slope_pos hlam hσ hη hση hφ hα0 hα1 hβ0 hβ1 hφy hρ1
    hslope h1 h2 h12 (h41 υ₂ h2)

/-- Galí (2015), p. 241 (survey error 3): if `ση > 1` but
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) < 0`, then for `0 ≤ υ₁ < υ₂ ≤ 1` with (41) at
`υ₁`, `Λ_v(υ₂) < Λ_v(υ₁)`: openness *dampens* the monetary shock. -/
theorem lambdaV_lt_of_slope_neg {β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv) < 0)
    (h1 : υ₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : υ₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : υ₁ < υ₂)
    (h41 : 0 < kappaU lamC σ η υ₁ varphi α * (φπ - 1) + (1 - β) * φy) :
    lambdaV β lamC σ η varphi α φπ φy ρv υ₂ < lambdaV β lamC σ η varphi α φπ φy ρv υ₁ := by
  have hD1 := msvDen_pos (sigmaU_pos hσ hη h1.1 h1.2)
    (kappaU_pos hlam hσ hη h1.1 h1.2 hφ hα0 hα1) hβ0 hβ1 hφy hρ1 h41
  have hs := sigmaU_strictAntiOn hσ hη hση h1 h2 h12
  unfold lambdaV msvLambda
  unfold kappaU at hD1 ⊢
  simp only [msvDen_affine] at hD1 ⊢
  apply one_div_lt_one_div_of_lt hD1
  nlinarith

/-- Survey error 3: for `υ ∈ [0, 1]` and `ση = 2`, `σ = 1`, `σ_υ ≤ 1`. -/
theorem counterexample_sigmaU_le (υ : ℝ) (hυ : υ ∈ Set.Icc (0 : ℝ) 1) :
    sigmaU 1 2 υ ≤ 1 := by
  have hD := one_add_mul_varpi_pos (σ := 1) (η := 2) one_pos two_pos hυ.1 hυ.2
  unfold sigmaU Phi
  rw [one_mul, div_le_one hD, varpi_sub_one]
  have : 0 ≤ υ * (2 - υ) := mul_nonneg hυ.1 (by linarith [hυ.2])
  nlinarith

/-- **Counterexample to the p. 241 claim** (survey error 3): with `σ = 1`, `η = 2`
(`ση = 2 > 1`), `β = 0.99`, `λ = 17/300`, `φ = 1`, `α = 1/4`, `φ_π = 0`, `φ_y = 30`
and `ρ_v = 0.99`, condition (41) holds for every `υ ∈ [0, 1]` and yet `Λ_v` is
strictly *decreasing* in openness on `[0, 1]`. -/
theorem counterexample_strictAntiOn :
    (∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU (17 / 300) 1 2 υ 1 (1 / 4) * (0 - 1) + (1 - 99 / 100) * 30) ∧
    StrictAntiOn (lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100))
      (Set.Icc 0 1) := by
  have h41 : ∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU (17 / 300) 1 2 υ 1 (1 / 4) * (0 - 1) + (1 - 99 / 100) * 30 := by
    intro υ hυ
    have := counterexample_sigmaU_le υ hυ
    unfold kappaU
    norm_num
    linarith
  refine ⟨h41, fun υ₁ h1 υ₂ h2 h12 => ?_⟩
  exact lambdaV_lt_of_slope_neg (by norm_num) one_pos two_pos (by norm_num) zero_le_one
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h1 h2 h12 (h41 υ₁ h1)

/-- Survey error 3, a concrete strict decrease: in the counterexample economy
`Λ_v(υ = 1/2) < Λ_v(υ = 0)`, with (41) holding at both values. -/
theorem counterexample_values :
    lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) (1 / 2)
      < lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) 0 :=
  counterexample_strictAntiOn.2 ⟨le_refl 0, zero_le_one⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num)

/-- **The printed claim is false** (Galí 2015, p. 241; survey error 3): it is not true
that `ση > 1` (with the standard restrictions on the other parameters and (41))
makes `Λ_v` increasing in the degree of openness. -/
theorem printed_monotonicity_false :
    ¬ ∀ β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ, 0 < β → β < 1 → 0 < lamC → 0 < σ → 0 < η →
      1 < σ * η → 0 ≤ varphi → 0 ≤ α → α < 1 → 0 ≤ φπ → 0 ≤ φy → 0 ≤ ρv → ρv < 1 →
      0 ≤ υ₁ → υ₁ < υ₂ → υ₂ ≤ 1 →
      0 < kappaU lamC σ η υ₁ varphi α * (φπ - 1) + (1 - β) * φy →
      0 < kappaU lamC σ η υ₂ varphi α * (φπ - 1) + (1 - β) * φy →
      lambdaV β lamC σ η varphi α φπ φy ρv υ₁ ≤ lambdaV β lamC σ η varphi α φπ φy ρv υ₂ := by
  intro h
  have hc := counterexample_values
  have := h (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) 0 (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) one_pos two_pos (by norm_num) zero_le_one (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (counterexample_strictAntiOn.1 0 ⟨le_refl 0, zero_le_one⟩)
    (counterexample_strictAntiOn.1 (1 / 2) ⟨by norm_num, by norm_num⟩)
  linarith

/-! ### The case `σ = η = 1` (p. 243) -/

/-- Galí (2015), p. 243 (with `ση = 1`, in particular `σ = η = 1`): the open-economy
equilibrium conditions under rule (39) coincide with the closed-economy ones
(`σ_υ = σ`, `κ_υ = κ = λ(σ + (φ + α)/(1 − α))`), for every degree of openness. -/
theorem closed_economy_equivalence {β lamC σ η υ varphi α ρ φπ φy : ℝ} (h : σ * η = 1)
    (rn yn v ygap infl i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) ρ φπ φy rn yn v ygap infl i ↔
      Equilibrium 𝔼 β σ (lamC * (σ + (varphi + α) / (1 - α))) ρ φπ φy rn yn v ygap infl i := by
  rw [sigmaU_of_sigma_mul_eta h, kappaU_of_mul_eq_one h]

/-- Galí (2015), p. 243: with `ση = 1` (in particular `σ = η = 1`) the output-gap and
domestic-inflation responses to a monetary shock do not depend on openness and equal
those of the closed economy (`υ = 0`). -/
theorem closed_economy_responses {β lamC σ η υ varphi α φπ φy ρv : ℝ} (h : σ * η = 1) :
    monYgapCoef β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv
        = monYgapCoef β (sigmaU σ η 0) (kappaU lamC σ η 0 varphi α) φπ φy ρv ∧
      monInflCoef β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv
        = monInflCoef β (sigmaU σ η 0) (kappaU lamC σ η 0 varphi α) φπ φy ρv := by
  rw [sigmaU_of_sigma_mul_eta h, sigmaU_of_sigma_mul_eta h, kappaU_of_mul_eq_one h,
    kappaU_of_mul_eq_one h]
  exact ⟨rfl, rfl⟩

/-- Galí (2015), p. 243, the book's case `σ = η = 1`: `σ_υ = 1` and
`κ_υ = λ(1 + (φ + α)/(1 − α))` for every degree of openness. -/
theorem sigma_eta_one (lamC υ varphi α : ℝ) :
    sigmaU 1 1 υ = 1 ∧ kappaU lamC 1 1 υ varphi α = lamC * (1 + (varphi + α) / (1 - α)) :=
  ⟨sigmaU_of_sigma_mul_eta (by norm_num) υ, kappaU_of_mul_eq_one (by norm_num) υ⟩

end Gali.OpenEconomy.TaylorRule

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal monetary policy in the small open economy: the special case `σ = η = 1`

Galí (2015), Chapter 8, §8.4, pp. 244–249.

## Main results

* **The consumption/output possibilities set** (p. 246). `consumption_possibilities`: with
  `σ = η = 1`, `Z ≡ 1`, `ϑ = 1`, the CPI `P = P_H^{1−υ} P_F^υ` (fn. 2), the risk-sharing
  condition (16) `C = C* 𝒬` with `𝒬 = P_F/P`, `C* = Y*` and market clearing (24)
  `Y = (1−υ)(P_H/P)^{−η} C + υ S^η Y*` imply, **exactly and nonlinearly**, `Y = S Y*`,
  `C S^υ = Y` and `C = Y^{1−υ} (Y*)^υ`.
* **The planner** (p. 246). `plannerWelfare_le`, `plannerWelfare_lt`,
  `planner_optimal_iff`, `planner_existsUnique`: welfare `log C − N^{1+φ}/(1+φ)` along the
  possibilities set is maximised **iff** `C N^φ = (1−υ)(1−α) C/N` (MRS = MRT,
  `hasDerivAt_frontier`) **iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}` (`optEmployment`), the unique
  maximiser, for every realisation of `A` and `Y*`.
* **The flexible-price markup** (p. 246). `markup_eq`: `ℳ = P_H/((1−τ)W/MPN)
  = (1−α)(Y/N)/((1−τ) C N^φ S^υ) = (1−α)/((1−τ) N^{1+φ})`; `printedFirstLine_eq`,
  `printedFirstLine_eq_markup_iff`: the printed first line `P_H/(W/MPN)` omits `(1 − τ)` and
  agrees with the other two only if `τ = 0` (survey error 5).
* **The optimal subsidy** (p. 247). `flexEmployment_eq_opt_iff`: the flexible-price
  allocation is the efficient one **iff** `(1−τ)(1−υ)ℳ = 1`; `flex_optimal`;
  `optSubsidy_lt_closed` (the book's "smaller than necessary to offset market power");
  `optSubsidy_neg_iff`: the "subsidy" is negative **iff** `υ > 1/ε`;
  `optSubsidy_calibration`: at `ε = 9`, `υ = 0.4` it is `τ = −13/27`, a 48% employment
  **tax** (survey error 4).
* **SDIT is optimal** (p. 247). `divine_coincidence`: along a bounded equilibrium of the
  open-economy NKPC (37) and DIS (29), `ỹ ≡ 0 ⟺ π_H ≡ 0`; `optimal_policy`: any
  discounted quadratic loss `∑ βᵗ (a ỹ² + b π_H²)` (`a, b > 0`, the form (43)) is `≥ 0`,
  attained (zero) by SDIT with `i = rⁿ`, and zero loss forces SDIT.
* **Implementation, eq. (42)** (pp. 247–248). `TaylorRule.schurStable_AU_iff` (Bullard–Mitra,
  `σ_υ, κ_υ`), `rule42_unique`: under `i = rⁿ + φ_π π_H` with `φ_π > 1`, `ỹ = π_H = 0`,
  `i = rⁿ` is the **unique** bounded equilibrium; `rule42_not_determinate`: with
  `0 ≤ φ_π ≤ 1` it is not; `exogRule_not_determinate`, `exogRule_not_unique`: `i = rⁿ` is
  indeterminate (another bounded equilibrium next to every one).
* **Macroeconomic implications** (p. 248), for **general** `σ, η` (definitions
  `AggregateDemand.varpi`, `AggregateDemand.Phi`, `AggregateDemand.sigmaU`, `Supply.natDen`,
  `Supply.GammaA`, `Supply.GammaZ`, `Supply.GammaStar` of pp. 235, 238; eq. (27) from (17) and
  (25) is `AggregateDemand.eq27`; the positivity lemmas `..._of_lt_one` cover `η ≥ 0`,
  `0 ≤ υ < 1`): `markup_eq33` (eq. (33)),
  `natural_output_iff` (eq. (35) is the unique flexible-price output), `GammaA_pos_of_lt_one`,
  `natural_tot_eq`, `tot_tech_coeff_pos` (technology ⇒ real depreciation),
  `tot_pref_coeff_neg` (`σ_υ Γ_z − (1−υ)Φ < 0` for **all** admissible parameters, so a
  preference shock appreciates), `dit_exchange_rate_cpi` (`e^{DIT} = sⁿ − p*`,
  `p^{DIT} = υ sⁿ = υ(e^{DIT} + p*)`).
-/

namespace Gali.OpenEconomy.OptimalPolicy

open Filter Topology
open Gali.OpenEconomy.Preferences (cpiCD)
open Gali.OpenEconomy.AggregateDemand (varpi Phi sigmaU one_add_mul_varpi)
open Gali.OpenEconomy.Supply (natDen GammaA GammaZ GammaStar sigma_sub_eq_sigmaU)
open Gali.OpenEconomy.TaylorRule (NKPC omegaU AU stack boundedVec_stack adaptedVec_stack tr2_AU
  det2_AU schurStable_AU_iff)

/-! ### The consumption/output possibilities set (p. 246) -/

/-- Galí (2015), p. 229: the terms of trade `S = P_F/P_H`. -/
noncomputable def tot (PH PF : ℝ) : ℝ := PF / PH

/-- Galí (2015), fn. 2 and p. 230 (`η = 1`, exact): `P_F/P = S^{1−υ}` and `P_H/P = S^{−υ}`. -/
theorem relPrices_cpi {υ PH PF : ℝ} (hH : 0 < PH) (hF : 0 < PF) :
    PF / cpiCD υ PH PF = tot PH PF ^ (1 - υ) ∧ PH / cpiCD υ PH PF = tot PH PF ^ (-υ) := by
  unfold cpiCD tot
  have h1 : PF = PF ^ (1 - υ) * PF ^ υ := by
    rw [← Real.rpow_add hF, sub_add_cancel, Real.rpow_one]
  have h2 : PH = PH ^ (1 - υ) * PH ^ υ := by
    rw [← Real.rpow_add hH, sub_add_cancel, Real.rpow_one]
  have a1 := Real.rpow_pos_of_pos hH (1 - υ)
  have a2 := Real.rpow_pos_of_pos hF υ
  have a3 := Real.rpow_pos_of_pos hH υ
  have a4 := Real.rpow_pos_of_pos hF (1 - υ)
  refine ⟨?_, ?_⟩
  · rw [Real.div_rpow hF.le hH.le, div_eq_div_iff (by positivity) a1.ne']
    nth_rewrite 1 [h1]
    ring
  · rw [Real.rpow_neg (div_pos hF hH).le, Real.div_rpow hF.le hH.le, inv_div,
      div_eq_div_iff (by positivity) a2.ne']
    nth_rewrite 1 [h2]
    ring

/-- Galí (2015), p. 246 (**the exact consumption/output possibilities set**). With
`σ = η = 1`, `Z ≡ 1` and `ϑ = 1`: the CPI (fn. 2), the risk-sharing condition (16)
`C = C* (P_F/P)` (with `P_F = ℰP*`, so `P_F/P` is the real exchange rate), `C* = Y*`
(p. 231) and market clearing (24) `Y = (1−υ)(P_H/P)^{−η} C + υ S^η Y*` imply
`Y = S Y*`, `C S^υ = Y` and `C = Y^{1−υ} (Y*)^υ`, exactly. -/
theorem consumption_possibilities {υ η PH PF C Cstar Ystar Y : ℝ} (hH : 0 < PH) (hF : 0 < PF)
    (hYs : 0 < Ystar) (hη : η = 1) (hrs : C = Cstar * (PF / cpiCD υ PH PF))
    (hCs : Cstar = Ystar)
    (hmc : Y = (1 - υ) * (PH / cpiCD υ PH PF) ^ (-η) * C + υ * tot PH PF ^ η * Ystar) :
    Y = tot PH PF * Ystar ∧ C * tot PH PF ^ υ = Y ∧ C = Y ^ (1 - υ) * Ystar ^ υ := by
  subst hη
  rw [hCs] at hrs
  obtain ⟨e1, e2⟩ := relPrices_cpi (υ := υ) hH hF
  have hS : 0 < tot PH PF := div_pos hF hH
  rw [e1] at hrs
  rw [e2, ← Real.rpow_mul hS.le, Real.rpow_one] at hmc
  have hSS : tot PH PF ^ (-υ * -1) * tot PH PF ^ (1 - υ) = tot PH PF := by
    rw [← Real.rpow_add hS, show -υ * -1 + (1 - υ) = 1 by ring, Real.rpow_one]
  have hCS : C * tot PH PF ^ υ = Ystar * tot PH PF := by
    rw [hrs, mul_assoc, ← Real.rpow_add hS, show 1 - υ + υ = 1 by ring, Real.rpow_one]
  have hY : Y = tot PH PF * Ystar := by
    rw [hmc, hrs]
    linear_combination (1 - υ) * Ystar * hSS
  refine ⟨hY, by rw [hCS, hY]; ring, ?_⟩
  have hSY : tot PH PF = Y / Ystar := by rw [hY]; field_simp
  have hY0 : 0 < Y := by rw [hY]; positivity
  have := Real.rpow_pos_of_pos hYs (1 - υ)
  rw [hrs, hSY, Real.div_rpow hY0.le hYs.le, mul_div_assoc', div_eq_iff this.ne', mul_assoc,
    ← Real.rpow_add hYs, show υ + (1 - υ) = 1 by ring, Real.rpow_one]
  ring

/-- Galí (2015), p. 246, in logs: `log C = (1−υ) log Y + υ log Y*` (exact). -/
theorem log_consumption {υ Y Ystar : ℝ} (hY : 0 < Y) (hYs : 0 < Ystar) :
    Real.log (Y ^ (1 - υ) * Ystar ^ υ) = (1 - υ) * Real.log Y + υ * Real.log Ystar := by
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' (Real.rpow_pos_of_pos hYs _).ne',
    Real.log_rpow hY, Real.log_rpow hYs]

/-! ### The planner's problem (p. 246) -/

/-- Galí (2015), p. 246: consumption along the possibilities set as a function of employment,
`C(N) = (A N^{1−α})^{1−υ} (Y*)^υ`. -/
noncomputable def frontierC (υ α A Ystar N : ℝ) : ℝ := (A * N ^ (1 - α)) ^ (1 - υ) * Ystar ^ υ

/-- Galí (2015), p. 246: the planner's objective `U(C, N) = log C − N^{1+φ}/(1+φ)` (`σ = 1`,
`Z ≡ 1`) along the possibilities set. -/
noncomputable def plannerWelfare (υ φ α A Ystar N : ℝ) : ℝ :=
  Real.log (frontierC υ α A Ystar N) - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 246: the efficient level of employment
`N = [(1 − υ)(1 − α)]^{1/(1+φ)}`. -/
noncomputable def optEmployment (υ φ α : ℝ) : ℝ := ((1 - υ) * (1 - α)) ^ (1 + φ)⁻¹

/-- Galí (2015), p. 246: `log C(N) = (1−υ)(log A + (1−α) log N) + υ log Y*`. -/
theorem log_frontierC {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    Real.log (frontierC υ α A Ystar N)
      = (1 - υ) * (Real.log A + (1 - α) * Real.log N) + υ * Real.log Ystar := by
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  rw [frontierC, log_consumption hY hYs, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne',
    Real.log_rpow hN]

/-- Galí (2015), p. 246: `C(N) > 0`. -/
theorem frontierC_pos {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    0 < frontierC υ α A Ystar N :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hA (Real.rpow_pos_of_pos hN _)) _)
    (Real.rpow_pos_of_pos hYs _)

/-- Galí (2015), p. 246 (**the marginal rate of transformation**): along the possibilities
set `dC/dN = (1−υ)(1−α) C/N`. -/
theorem hasDerivAt_frontier {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    HasDerivAt (frontierC υ α A Ystar)
      ((1 - υ) * (1 - α) * frontierC υ α A Ystar N / N) N := by
  set k := (1 - α) * (1 - υ) with hk
  have heq : (fun n => A ^ (1 - υ) * Ystar ^ υ * n ^ k) =ᶠ[𝓝 N] frontierC υ α A Ystar := by
    filter_upwards [Ioi_mem_nhds hN] with n hn
    simp only [frontierC]
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg (le_of_lt hn) _), ← Real.rpow_mul hn.le]
    ring
  refine (((Real.hasDerivAt_rpow_const (p := k) (Or.inl hN.ne')).const_mul
    (A ^ (1 - υ) * Ystar ^ υ)).congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [← heq.eq_of_nhds, Real.rpow_sub_one hN.ne', show (1 - υ) * (1 - α) = k by rw [hk]; ring]
  field_simp

/-- Galí (2015), p. 246: the derivative of the planner's objective,
`U_c dC/dN + U_n = (1−υ)(1−α)/N − N^φ` (with `U_c = 1/C`, `U_n = −N^φ`). -/
theorem hasDerivAt_plannerWelfare {υ φ α A Ystar N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A)
    (hYs : 0 < Ystar) (hN : 0 < N) :
    HasDerivAt (plannerWelfare υ φ α A Ystar) ((1 - υ) * (1 - α) / N - N ^ φ) N := by
  have hC := frontierC_pos (υ := υ) (α := α) hA hYs hN
  have h1 := (hasDerivAt_frontier (υ := υ) (α := α) hA hYs hN).log hC.ne'
  have h2 : HasDerivAt (fun n : ℝ => n ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp

/-- Galí (2015), p. 246: `N^{1+φ} = (1−υ)(1−α)` at the efficient employment level. -/
theorem optEmployment_rpow {υ φ α : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ) :
    optEmployment υ φ α ^ (1 + φ) = (1 - υ) * (1 - α) := by
  have hk : 0 ≤ (1 - υ) * (1 - α) := mul_nonneg (by linarith) (by linarith)
  rw [optEmployment, Real.rpow_inv_rpow hk (by linarith)]

/-- Galí (2015), p. 246: efficient employment is positive. -/
theorem optEmployment_pos {υ φ α : ℝ} (hυ : υ < 1) (hα : α < 1) : 0 < optEmployment υ φ α :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (by linarith)) _

/-- Galí (2015), p. 246 (**the optimality condition**): for `C, N > 0`,
`C N^φ = (1−υ)(1−α) C/N` (i.e. `−U_n/U_c = MRT`) **iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem foc_iff {υ φ α C N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ) (hC : 0 < C)
    (hN : 0 < N) :
    C * N ^ φ = (1 - υ) * (1 - α) * C / N ↔ N = optEmployment υ φ α := by
  have hk : 0 < (1 - υ) * (1 - α) := mul_pos (by linarith) (by linarith)
  have hNN : N ^ (1 + φ) = N ^ φ * N := by
    rw [Real.rpow_add hN, Real.rpow_one, mul_comm]
  constructor
  · intro h
    have h2 : N ^ (1 + φ) = (1 - υ) * (1 - α) := by
      rw [hNN]
      field_simp at h
      nlinarith
    rw [optEmployment, ← h2, Real.rpow_rpow_inv hN.le (by linarith)]
  · intro h
    have h2 : N ^ φ * N = (1 - υ) * (1 - α) := by
      rw [← hNN, h, optEmployment_rpow hυ hα hφ]
    rw [eq_div_iff hN.ne']
    linear_combination C * h2

/-- Galí (2015), p. 246 (**sufficiency, with strictness**): for every `N > 0`,
`W(N) ≤ W(N*)`, with equality only at `N = N*` (strictly below otherwise), where
`N* = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem plannerWelfare_le {υ φ α A Ystar N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    plannerWelfare υ φ α A Ystar N ≤ plannerWelfare υ φ α A Ystar (optEmployment υ φ α) ∧
      (N ≠ optEmployment υ φ α →
        plannerWelfare υ φ α A Ystar N < plannerWelfare υ φ α A Ystar (optEmployment υ φ α)) := by
  set Ns := optEmployment υ φ α with hNs
  have hNs0 : 0 < Ns := optEmployment_pos hυ hα
  have hk : 0 < (1 - υ) * (1 - α) := mul_pos (by linarith) (by linarith)
  have hNk := optEmployment_rpow hυ hα hφ
  rw [← hNs] at hNk
  set x := N / Ns with hx
  have hx0 : 0 < x := div_pos hN hNs0
  have hNx : N = Ns * x := by rw [hx]; field_simp
  have hpow : N ^ (1 + φ) = (1 - υ) * (1 - α) * x ^ (1 + φ) := by
    rw [hNx, Real.mul_rpow hNs0.le hx0.le, hNk]
  have hbern : 1 + (1 + φ) * (x - 1) ≤ x ^ (1 + φ) := by
    have := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) (p := 1 + φ)
      (by linarith)
    simpa using this
  have hlog : Real.log N - Real.log Ns = Real.log x := by
    rw [hx, Real.log_div hN.ne' hNs0.ne']
  have hdiff : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns
      = (1 - υ) * (1 - α) * (Real.log x - (x ^ (1 + φ) - 1) / (1 + φ)) := by
    unfold plannerWelfare
    rw [log_frontierC hA hYs hN, log_frontierC hA hYs hNs0, hpow, hNk, ← hlog]
    field_simp
    ring
  have hφ1 : (0 : ℝ) < 1 + φ := by linarith
  have hb : x - 1 ≤ (x ^ (1 + φ) - 1) / (1 + φ) := by
    rw [le_div_iff₀ hφ1]
    nlinarith
  constructor
  · have hl := Real.log_le_sub_one_of_pos hx0
    have : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns ≤ 0 := by
      rw [hdiff]
      exact mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
    linarith
  · intro hne
    have hx1 : x ≠ 1 := by
      intro h1
      apply hne
      rw [hNx, h1, mul_one]
    have hl := Real.log_lt_sub_one_of_pos hx0 hx1
    have : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns < 0 := by
      rw [hdiff]
      exact mul_neg_of_pos_of_neg hk (by linarith)
    linarith

/-- Galí (2015), p. 246 (**necessary and sufficient**): `N > 0` maximises the planner's
objective over all `N' > 0` **iff** the optimality condition `C N^φ = (1−υ)(1−α) C/N` holds
**iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem planner_optimal_iff {υ φ α A Ystar N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    ((∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤ plannerWelfare υ φ α A Ystar N) ↔
      frontierC υ α A Ystar N * N ^ φ = (1 - υ) * (1 - α) * frontierC υ α A Ystar N / N) ∧
    (frontierC υ α A Ystar N * N ^ φ = (1 - υ) * (1 - α) * frontierC υ α A Ystar N / N ↔
      N = optEmployment υ φ α) := by
  have hfoc := foc_iff hυ hα hφ (frontierC_pos (υ := υ) (α := α) hA hYs hN) hN
  refine ⟨?_, hfoc⟩
  rw [hfoc]
  constructor
  · intro hmax
    by_contra hne
    have h1 := (plannerWelfare_le hυ hα hφ hA hYs hN).2 hne
    have h2 := hmax (optEmployment υ φ α) (optEmployment_pos hυ hα)
    linarith
  · rintro rfl N' hN'
    exact (plannerWelfare_le hυ hα hφ hA hYs hN').1

/-- Galí (2015), p. 246 (**existence and uniqueness**): for every realisation of `A > 0` and
`Y* > 0`, exactly one `N > 0` maximises the planner's objective, and it is the constant
`[(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem planner_existsUnique {υ φ α A Ystar : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤
      plannerWelfare υ φ α A Ystar N := by
  refine ⟨optEmployment υ φ α, ⟨optEmployment_pos hυ hα,
    fun N' hN' => (plannerWelfare_le hυ hα hφ hA hYs hN').1⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact ((planner_optimal_iff hυ hα hφ hA hYs hN).1.trans
    (planner_optimal_iff hυ hα hφ hA hYs hN).2).1 hmax

/-! ### The flexible-price markup and the optimal subsidy (pp. 246–247) -/

/-- Galí (2015), p. 246 (corrected first line): the gross price markup
`ℳ = P_H/((1−τ) W/MPN)`, with marginal cost `(1−τ)W/MPN` net of the employment subsidy. -/
noncomputable def markupH (τ PH W mpn : ℝ) : ℝ := PH / ((1 - τ) * (W / mpn))

/-- Galí (2015), p. 246, first line **as printed**: `P_H/(W/MPN)` (no subsidy). -/
noncomputable def printedFirstLine (PH W mpn : ℝ) : ℝ := PH / (W / mpn)

/-- Galí (2015), p. 246 (**the flexible-price markup**): with `P_H = P S^{−υ}` (fn. 2),
labour supply `W/P = C N^φ` (eq. (7), `σ = 1`), `MPN = (1−α) Y/N` and `C S^υ = Y`
(`consumption_possibilities`), the markup satisfies
`ℳ = (1−α)(Y/N)/((1−τ) C N^φ S^υ) = (1−α)/((1−τ) N^{1+φ})`. -/
theorem markup_eq {υ φ α τ P PH W C N Y S : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : 0 < N)
    (hS : 0 < S) (hτ : τ < 1) (hPH : PH = P * S ^ (-υ)) (hW : W = P * (C * N ^ φ))
    (hCS : C * S ^ υ = Y) :
    markupH τ PH W ((1 - α) * Y / N)
        = (1 - α) * (Y / N) / ((1 - τ) * (C * N ^ φ) * S ^ υ) ∧
      ((1 - α) * (Y / N) / ((1 - τ) * (C * N ^ φ) * S ^ υ)
        = (1 - α) / ((1 - τ) * N ^ (1 + φ))) := by
  have hSu := Real.rpow_pos_of_pos hS υ
  have hNφ := Real.rpow_pos_of_pos hN φ
  have hneg : S ^ (-υ) = (S ^ υ)⁻¹ := Real.rpow_neg hS.le υ
  have h1τ : (1 : ℝ) - τ ≠ 0 := by linarith
  have hNN : N ^ (1 + φ) = N * N ^ φ := by rw [Real.rpow_add hN, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne α 1 with hα | hα
    · subst hα
      simp [markupH]
    · have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
      have hY : Y ≠ 0 := by rw [← hCS]; positivity
      unfold markupH
      rw [hPH, hW, hneg]
      field_simp
  · rw [hNN, ← hCS]
    field_simp

/-- Galí (2015), p. 246 (survey error 5): under the same assumptions the printed first line
`P_H/(W/MPN)` equals `(1−α)/N^{1+φ}`, i.e. the markup computed **without** the subsidy. -/
theorem printedFirstLine_eq {υ φ α P PH W C N Y S : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : 0 < N)
    (hS : 0 < S) (hPH : PH = P * S ^ (-υ)) (hW : W = P * (C * N ^ φ))
    (hCS : C * S ^ υ = Y) :
    printedFirstLine PH W ((1 - α) * Y / N) = (1 - α) / N ^ (1 + φ) := by
  have h := (markup_eq (τ := 0) (α := α) hP hC hN hS (by norm_num) hPH hW hCS)
  have e : printedFirstLine PH W ((1 - α) * Y / N) = markupH 0 PH W ((1 - α) * Y / N) := by
    simp [printedFirstLine, markupH]
  rw [e, h.1, h.2]
  simp

/-- Galí (2015), p. 246 (survey error 5): the printed first line agrees with the (correct)
second and third lines **iff** `τ = 0` (given `α < 1`); so with a nonzero subsidy the first
line must read `P_H/((1−τ)W/MPN)`. -/
theorem printedFirstLine_eq_markup_iff {υ φ α τ P PH W C N Y S : ℝ} (hα : α < 1) (hP : 0 < P)
    (hC : 0 < C) (hN : 0 < N) (hS : 0 < S) (hτ : τ < 1) (hPH : PH = P * S ^ (-υ))
    (hW : W = P * (C * N ^ φ)) (hCS : C * S ^ υ = Y) :
    printedFirstLine PH W ((1 - α) * Y / N) = markupH τ PH W ((1 - α) * Y / N) ↔ τ = 0 := by
  rw [printedFirstLine_eq hP hC hN hS hPH hW hCS, (markup_eq hP hC hN hS hτ hPH hW hCS).1,
    (markup_eq hP hC hN hS hτ hPH hW hCS).2]
  have hNφ := Real.rpow_pos_of_pos hN (1 + φ)
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1τ : (0 : ℝ) < 1 - τ := by linarith
  constructor
  · intro h
    field_simp at h
    nlinarith
  · rintro rfl
    simp

/-- Galí (2015), p. 246: the desired (flexible-price) gross markup `ℳ = ε/(ε − 1)`. -/
noncomputable def desiredMarkup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 246: the desired markup exceeds one (`ε > 1`). -/
theorem one_lt_desiredMarkup {ε : ℝ} (hε : 1 < ε) : 1 < desiredMarkup ε := by
  rw [desiredMarkup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), pp. 246–247: in the flexible-price equilibrium the markup equals `ℳ > 0`,
so `(1−α)/((1−τ)N^{1+φ}) = ℳ`; then the flexible-price allocation is the efficient one
`N = [(1−υ)(1−α)]^{1/(1+φ)}` **iff** `(1−τ)(1−υ)ℳ = 1`. -/
theorem flexEmployment_eq_opt_iff {υ φ α τ M N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hτ : τ < 1) (hN : 0 < N) (hflex : (1 - α) / ((1 - τ) * N ^ (1 + φ)) = M) :
    N = optEmployment υ φ α ↔ (1 - τ) * (1 - υ) * M = 1 := by
  have hNφ := Real.rpow_pos_of_pos hN (1 + φ)
  have h1τ : (0 : ℝ) < 1 - τ := by linarith
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hf : (1 - α) = M * ((1 - τ) * N ^ (1 + φ)) := by
    rw [← hflex, div_mul_cancel₀]
    positivity
  constructor
  · intro h
    rw [h, optEmployment_rpow hυ hα hφ] at hf
    have : (1 - α) * ((1 - τ) * (1 - υ) * M - 1) = 0 := by linear_combination -hf
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith
  · intro h
    have hN2 : N ^ (1 + φ) = (1 - υ) * (1 - α) := by
      linear_combination (-(1 - υ)) * hf - N ^ (1 + φ) * h
    rw [optEmployment, ← hN2, Real.rpow_rpow_inv hN.le (by linarith)]

/-- Galí (2015), p. 247 (**the flexible-price allocation is optimal**): with
`(1−τ)(1−υ)ℳ = 1`, employment in the flexible-price equilibrium maximises the planner's
objective at every date, whatever the realisations of `A` and `Y*`. -/
theorem flex_optimal {υ φ α τ M N A Ystar : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hτ : τ < 1) (hN : 0 < N) (hA : 0 < A) (hYs : 0 < Ystar)
    (hflex : (1 - α) / ((1 - τ) * N ^ (1 + φ)) = M) (hsub : (1 - τ) * (1 - υ) * M = 1) :
    ∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤ plannerWelfare υ φ α A Ystar N := by
  have h := (flexEmployment_eq_opt_iff hυ hα hφ hτ hN hflex).2 hsub
  intro N' hN'
  rw [h]
  exact (plannerWelfare_le hυ hα hφ hA hYs hN').1

/-- Galí (2015), p. 247: the optimal employment subsidy `τ = 1 − 1/((1−υ)ℳ)`. -/
noncomputable def optSubsidy (υ M : ℝ) : ℝ := 1 - 1 / ((1 - υ) * M)

/-- Galí (2015), p. 247: `(1−τ)(1−υ)ℳ = 1` **iff** `τ = 1 − 1/((1−υ)ℳ)`. -/
theorem subsidy_iff {υ τ M : ℝ} (hυ : υ < 1) (hM : 0 < M) :
    (1 - τ) * (1 - υ) * M = 1 ↔ τ = optSubsidy υ M := by
  have h : (0 : ℝ) < (1 - υ) * M := mul_pos (by linarith) hM
  unfold optSubsidy
  constructor
  · intro h1
    have h2 : 1 - τ = 1 / ((1 - υ) * M) := by
      rw [eq_div_iff h.ne']
      linear_combination h1
    linarith
  · intro h1
    rw [h1, sub_sub_cancel, mul_assoc, one_div_mul_cancel h.ne']

/-- Galí (2015), p. 247 (**"the required subsidy is smaller than necessary to offset firms'
market power"**): for `0 < υ < 1` and `ℳ > 0`, `1 − 1/((1−υ)ℳ) < 1 − 1/ℳ`, the latter being
the closed-economy subsidy (`(1−τ)ℳ = 1`). -/
theorem optSubsidy_lt_closed {υ M : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hM : 0 < M) :
    optSubsidy υ M < 1 - 1 / M := by
  unfold optSubsidy
  have h1 : (1 - υ) * M < M := by nlinarith
  have h2 : 0 < (1 - υ) * M := mul_pos (by linarith) hM
  have := one_div_lt_one_div_of_lt h2 h1
  linarith

/-- Galí (2015), p. 247 (survey error 4): with `ℳ = ε/(ε−1)`, `ε > 1`, `0 ≤ υ < 1`, the
optimal "subsidy" is **negative** (a tax on employment) **iff** `υ > 1/ε`. -/
theorem optSubsidy_neg_iff {υ ε : ℝ} (hε : 1 < ε) (hυ1 : υ < 1) :
    optSubsidy υ (desiredMarkup ε) < 0 ↔ 1 / ε < υ := by
  unfold optSubsidy desiredMarkup
  have hε0 : (0 : ℝ) < ε := by linarith
  have hε1 : (0 : ℝ) < ε - 1 := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hpos : 0 < (1 - υ) * (ε / (ε - 1)) := by positivity
  rw [sub_neg, lt_div_iff₀ hpos, div_lt_iff₀ hε0]
  constructor
  · intro h
    have : (1 - υ) * ε < ε - 1 := by
      field_simp at h
      linarith
    linarith
  · intro h
    rw [one_mul, mul_div_assoc', div_lt_one hε1]
    linarith

/-- Galí (2015), pp. 247 and 250 (survey error 4): at the book's calibration `ε = 9`
(`ℳ = 1.125`) and `υ = 0.4` the optimal instrument is `τ = −13/27 ≈ −0.48`: a 48%
employment **tax**, whereas the closed-economy subsidy is `1/9 > 0`. -/
theorem optSubsidy_calibration :
    optSubsidy (2 / 5) (desiredMarkup 9) = -13 / 27 ∧ optSubsidy (2 / 5) (desiredMarkup 9) < 0 ∧
      optSubsidy (2 / 5) (desiredMarkup 9) < -(48 / 100) ∧
      1 - 1 / desiredMarkup 9 = 1 / 9 := by
  unfold optSubsidy desiredMarkup
  norm_num

/-! ### SDIT is optimal (p. 247) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (29), p. 235: the open-economy dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − rⁿ_t)`. -/
def DIS (συ : ℝ) (ygap i inflH rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - συ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - rn t)

/-- Galí (2015), p. 247: an equilibrium of the non-policy block, (29) and (37), given the
interest-rate path `i`. -/
def Equilibrium (β συ κυ : ℝ) (rn ygap inflH i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κυ ygap inflH ∧ DIS 𝔼 συ ygap i inflH rn

/-- Galí (2015), p. 247: `ỹ ≡ π_H ≡ 0` is an equilibrium **iff** `i_t = rⁿ_t` for all `t`
(`σ_υ ≠ 0`). Adapted from the Chapter 4 project. -/
theorem zero_equilibrium_iff {β συ κυ : ℝ} (hσ : συ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β συ κυ rn 0 0 i ↔ ∀ t, i t = rn t := by
  constructor
  · rintro ⟨-, hd⟩ t
    have h := hd t
    simp only [Pi.zero_apply, map_zero, zero_sub, sub_zero] at h
    have h2 : συ⁻¹ • (i t - rn t) = 0 := by
      have := congrArg Neg.neg h
      simp only [neg_zero, neg_neg] at this
      exact this.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (inv_eq_zero.1 h3) hσ
    · exact sub_eq_zero.1 h3
  · intro h
    refine ⟨fun t => by simp, fun t => ?_⟩
    simp [h t]

/-- Galí (2015), p. 247: a closed output gap and bounded domestic inflation force
`π_H ≡ 0` (eq. (37), `|β| < 1`). Adapted from the Chapter 4 project. -/
theorem inflH_zero_of_gap_zero {β κυ : ℝ} (hβ : |β| < 1) {inflH : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κυ 0 inflH) (hb : BoundedProc inflH) : inflH = 0 := by
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  refine 𝔼.forward_unique hβ (u := 0) (fun t => ?_) h0 hb ⟨0, fun _ _ => by simp⟩
  rw [hp t]
  simp

/-- Galí (2015), p. 247: `π_H ≡ 0` forces `ỹ ≡ 0` (eq. (37), `κ_υ ≠ 0`). -/
theorem gap_zero_of_inflH_zero {β κυ : ℝ} (hκ : κυ ≠ 0) {ygap : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κυ ygap 0) : ygap = 0 := by
  funext t
  have h := hp t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at h
  rcases smul_eq_zero.1 h.symm with h1 | h1
  · exact absurd h1 hκ
  · exact h1

/-- Galí (2015), p. 247 (**"(37) then implies that domestic prices are also stabilized"**):
along any equilibrium with bounded domestic inflation, `ỹ ≡ 0 ⟺ π_H ≡ 0`, and then
`i = rⁿ`. -/
theorem divine_coincidence {β συ κυ : ℝ} (hβ : |β| < 1) (hσ : συ ≠ 0) (hκ : κυ ≠ 0)
    {rn ygap inflH i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β συ κυ rn ygap inflH i)
    (hb : BoundedProc inflH) :
    (ygap = 0 ↔ inflH = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) := by
  have hiff : ygap = 0 ↔ inflH = 0 := by
    constructor
    · intro hy
      subst hy
      exact inflH_zero_of_gap_zero 𝔼 hβ heq.1 hb
    · intro hπ
      subst hπ
      exact gap_zero_of_inflH_zero 𝔼 hκ heq.1
  refine ⟨hiff, fun hy => ?_⟩
  have hπ := hiff.1 hy
  subst hy
  subst hπ
  exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-- Galí (2015), eq. (43), p. 249: the discounted quadratic loss along a state `ω`,
`∑ₜ βᵗ (a ỹ_t² + b π_{H,t}²)` (in (43), `a = ((1−υ)/2)(1+φ)/(1−α)`, `b = ((1−υ)/2) ε/λ`). -/
noncomputable def pathLoss (a b β : ℝ) (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2)

omit 𝔼 in
/-- Galí (2015), p. 249: for bounded processes and `0 ≤ β < 1` the loss series converges.
Adapted from the Chapter 4 project. -/
theorem pathLoss_summable {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ygap inflH : ℕ → Ω → ℝ} (hy : BoundedProc ygap) (hπ : BoundedProc inflH) (ω : Ω) :
    Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2) := by
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
/-- Galí (2015), p. 249: the loss is nonnegative (`a, b, β ≥ 0`). -/
theorem pathLoss_nonneg {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β)
    (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ pathLoss a b β ygap inflH ω :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _)))

omit 𝔼 in
/-- Galí (2015), p. 247: SDIT (`ỹ ≡ π_H ≡ 0`) has zero loss. -/
theorem pathLoss_zero (a b β : ℝ) (ω : Ω) : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 ω = 0 := by
  simp [pathLoss]

omit 𝔼 in
/-- Galí (2015), p. 247: with `a, b, β > 0` and a summable loss, the loss is zero **iff**
`ỹ_t(ω) = π_{H,t}(ω) = 0` for all `t`. Adapted from the Chapter 4 project. -/
theorem pathLoss_eq_zero_iff {a b β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    {ygap inflH : ℕ → Ω → ℝ} {ω : Ω}
    (hs : Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2)) :
    pathLoss a b β ygap inflH ω = 0 ↔ ∀ t, ygap t ω = 0 ∧ inflH t ω = 0 := by
  have hnn : ∀ t, 0 ≤ β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2) := fun t =>
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
      have hπ := mul_nonneg hb.le (sq_nonneg (inflH t ω))
      have e1 : a * ygap t ω ^ 2 = 0 := by linarith
      have e2 : b * inflH t ω ^ 2 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.1
          ((mul_eq_zero.1 e1).resolve_left ha.ne'),
        pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 e2).resolve_left hb.ne')⟩
  · intro h
    funext t
    simp [(h t).1, (h t).2]

/-- Galí (2015), p. 247 and eq. (43), p. 249 (**SDIT is the optimal policy**): for any loss
`∑ βᵗ (a ỹ² + b π_H²)` with `a, b > 0`, `0 < β < 1`: (i) every outcome has nonnegative loss in
every state and in expectation `E_0`, and the SDIT outcome attains the minimum; (ii) SDIT
with `i = rⁿ` is an equilibrium; (iii) any bounded equilibrium with zero loss in every state is
SDIT (`ỹ ≡ π_H ≡ 0`) with `i = rⁿ`. -/
theorem optimal_policy {a b β συ κυ : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : συ ≠ 0) (rn : ℕ → Ω → ℝ) :
    (∀ ygap inflH : ℕ → Ω → ℝ, (∀ ω, 0 ≤ pathLoss a b β ygap inflH ω) ∧
        ∀ ω, 𝔼.E 0 (pathLoss a b β (0 : ℕ → Ω → ℝ) 0) ω
          ≤ 𝔼.E 0 (pathLoss a b β ygap inflH) ω) ∧
      Equilibrium 𝔼 β συ κυ rn 0 0 rn ∧
      ∀ ygap inflH i : ℕ → Ω → ℝ, Equilibrium 𝔼 β συ κυ rn ygap inflH i →
        BoundedProc ygap → BoundedProc inflH → (∀ ω, pathLoss a b β ygap inflH ω = 0) →
        ygap = 0 ∧ inflH = 0 ∧ ∀ t, i t = rn t := by
  refine ⟨fun ygap inflH => ⟨pathLoss_nonneg ha.le hb.le hβ0.le ygap inflH, fun ω => ?_⟩,
    (zero_equilibrium_iff 𝔼 hσ rn rn).2 fun _ => rfl, ?_⟩
  · have h0 : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 = fun _ => (0 : ℝ) :=
      funext fun ω => pathLoss_zero a b β ω
    have := 𝔼.mono 0 (pathLoss_nonneg ha.le hb.le hβ0.le ygap inflH) ω
    rw [h0]
    simpa [𝔼.const] using this
  · intro ygap inflH i heq hy hπ hzero
    have hall : ∀ t ω, ygap t ω = 0 ∧ inflH t ω = 0 := fun t ω =>
      ((pathLoss_eq_zero_iff ha hb hβ0
        (pathLoss_summable ha.le hb.le hβ0.le hβ1 hy hπ ω)).1 (hzero ω)) t
    have hy0 : ygap = 0 := funext fun t => funext fun ω => (hall t ω).1
    have hπ0 : inflH = 0 := funext fun t => funext fun ω => (hall t ω).2
    refine ⟨hy0, hπ0, ?_⟩
    subst hy0
    subst hπ0
    exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-! ### Implementation: rule (42) (pp. 247–248) -/

/-- Galí (2015), eq. (42), p. 247, with an optional output-gap response (as in eq. (39)):
`i_t = rⁿ_t + φ_π π_{H,t} + φ_y ỹ_t`; (42) itself is the case `φ_y = 0`. -/
def TaylorRule (φπ φy : ℝ) (i rn inflH ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • inflH t + φy • ygap t

/-- Galí (2015), eq. (40), p. 240 (with `rⁿ` in the rule, as in (42)): given the rule, the
NKPC (37) and the DIS (29) hold iff `x_t = A_υ E_t x_{t+1}` (`σ_υ ≠ 0`,
`σ_υ + φ_y + κ_υφ_π ≠ 0`). Adapted from the Chapter 4 project. -/
theorem nk_iff_solves {β συ κυ φπ φy : ℝ} (hσ : συ ≠ 0) (hS : συ + φy + κυ * φπ ≠ 0)
    {rn ygap inflH i : ℕ → Ω → ℝ} (hrule : TaylorRule φπ φy i rn inflH ygap) :
    Equilibrium 𝔼 β συ κυ rn ygap inflH i ↔
      𝔼.Solves (AU β συ κυ φπ φy) 0 (stack ygap inflH) := by
  have hinv : συ * συ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    have s : (συ + φy) * ygap t ω + φπ * inflH t ω
        = συ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (inflH (t + 1)) ω := by
      linear_combination συ * e - r - (i t ω - 𝔼.E t (inflH (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AU, omegaU]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AU, omegaU]
      field_simp
      linear_combination κυ * s + (συ + φy) * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AU, omegaU] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κυ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      have r := congrFun (hrule t) ω
      simp [stack, AU, omegaU] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      have s : (συ + φy) * ygap t ω + φπ * inflH t ω
          = συ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (inflH (t + 1)) ω := by
        apply mul_left_cancel₀ hS
        linear_combination (συ + φy) * e0 + φπ * e1
      rw [r]
      linear_combination συ⁻¹ * s - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), pp. 247–248 (**rule (42) implements SDIT uniquely**): under
`i_t = rⁿ_t + φ_π π_{H,t} + φ_y ỹ_t` with `κ_υ(φ_π − 1) + (1 − β)φ_y > 0` (in particular
(42), `φ_y = 0`, `φ_π > 1`: `rule42_unique`), the SDIT outcome `ỹ = π_H = 0`, `i = rⁿ` is
the **unique** equilibrium with bounded adapted output gap and domestic inflation. -/
theorem equilibrium_iff_zero {β συ κυ φπ φy : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < κυ * (φπ - 1) + (1 - β) * φy)
    {rn ygap inflH i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted inflH)
    (hba : BoundedProc ygap) (hbb : BoundedProc inflH) :
    (Equilibrium 𝔼 β συ κυ rn ygap inflH i ∧ TaylorRule φπ φy i rn inflH ygap) ↔
      ygap = 0 ∧ inflH = 0 ∧ i = rn := by
  have hS : συ + φy + κυ * φπ ≠ 0 := by positivity
  have hr0 : TaylorRule φπ φy rn rn (0 : ℕ → Ω → ℝ) 0 := fun t => by simp
  constructor
  · rintro ⟨he, hr⟩
    have hx := (nk_iff_solves 𝔼 hσ.ne' hS hr).mp he
    have h0 := (nk_iff_solves 𝔼 (β := β) hσ.ne' hS hr0).mp
      ((zero_equilibrium_iff 𝔼 (β := β) (κυ := κυ) hσ.ne' rn rn).2 fun _ => rfl)
    have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41) hx h0
      (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
      (boundedVec_stack hba hbb) (boundedVec_stack ⟨0, fun t ω => by simp⟩
        ⟨0, fun t ω => by simp⟩)
    have h1 : ygap = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : inflH = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [hr t, h1, h2]
    simp
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact ⟨(zero_equilibrium_iff 𝔼 hσ.ne' rn rn).2 fun _ => rfl, hr0⟩

/-- Galí (2015), eq. (42), pp. 247–248 (**implementation of SDIT**): under
`i_t = rⁿ_t + φ_π π_{H,t}` with `φ_π > 1`, `ỹ = π_H = 0` and `i = rⁿ` is the unique
equilibrium with bounded adapted output gap and domestic inflation; in it the term `φ_π π_H`
vanishes, so `i = rⁿ` (p. 248). -/
theorem rule42_unique {β συ κυ φπ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 1 < φπ) {rn ygap inflH i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted inflH) (hba : BoundedProc ygap) (hbb : BoundedProc inflH) :
    (Equilibrium 𝔼 β συ κυ rn ygap inflH i ∧ TaylorRule φπ 0 i rn inflH ygap) ↔
      ygap = 0 ∧ inflH = 0 ∧ i = rn :=
  equilibrium_iff_zero 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
    (by have := mul_pos hκ (sub_pos.2 hφπ); linarith) ha hb hba hbb

/-- Galí (2015), p. 247 (sharpness of `φ_π > 1` in (42)): with `0 ≤ φ_π ≤ 1` and `φ_y = 0`
the system (40) is **not** determinate. -/
theorem rule42_not_determinate [Nonempty Ω] {β συ κυ φπ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ0 : 0 ≤ φπ) (hφπ1 : φπ ≤ 1) :
    ¬ 𝔼.Determinate (AU β συ κυ φπ 0) := by
  rw [𝔼.determinate_iff, schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ0 le_rfl]
  have := mul_nonpos_of_nonneg_of_nonpos hκ.le (sub_nonpos.2 hφπ1)
  linarith

/-- Galí (2015), eq. (10) of Ch. 4 with `σ ↦ σ_υ`, `κ ↦ κ_υ` (p. 247): under `i = rⁿ` the
system is `x_t = A_O E_t x_{t+1}`, `A_O = [[1, 1/σ_υ], [κ_υ, β + κ_υ/σ_υ]]`. -/
noncomputable def AO (β συ κυ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / συ; κυ, β + κυ / συ]

/-- Galí (2015), p. 247: under `i = rⁿ`, the NKPC (37) and the DIS (29) hold iff `(ỹ, π_H)`
solves `x_t = A_O E_t x_{t+1}`. Adapted from the Chapter 4 project. -/
theorem nk_iff_solves_exog {β συ κυ : ℝ} {rn ygap inflH : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β συ κυ rn ygap inflH rn ↔ 𝔼.Solves (AO β συ κυ) 0 (stack ygap inflH) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO]
      linear_combination e
    · simp [stack, AO]
      linear_combination p + κυ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κυ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

omit 𝔼 in
/-- Galí (2015), p. 247 (via Ch. 4, p. 105): `A_O` fails the Schur–Cohn condition, since
`tr A_O = 1 + det A_O + κ_υ/σ_υ > 1 + det A_O`. -/
theorem not_schurStable_AO {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) :
    ¬ SchurStable (tr2 (AO β συ κυ)) (det2 (AO β συ κυ)) := by
  rintro ⟨-, hT⟩
  have htr : tr2 (AO β συ κυ) = 1 + β + κυ / συ := by simp [tr2, AO]; ring
  have hdet : det2 (AO β συ κυ) = β := by simp [det2, AO]; field_simp; ring
  rw [htr, hdet] at hT
  have := div_pos hκ hσ
  have := le_abs_self (1 + β + κυ / συ)
  linarith

/-- Galí (2015), p. 247 (**`i_t = rⁿ_t` is associated with an indeterminate equilibrium**):
for `σ_υ, κ_υ > 0` the system under `i = rⁿ` is not determinate. -/
theorem exogRule_not_determinate [Nonempty Ω] {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) :
    ¬ 𝔼.Determinate (AO β συ κυ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- Galí (2015), p. 247 (**`i = rⁿ` does not guarantee full price stability**): next to every
equilibrium under `i = rⁿ` with bounded adapted output gap and domestic inflation (e.g. SDIT
itself) there is another one, with a different output gap or domestic inflation path. -/
theorem exogRule_not_unique [Nonempty Ω] {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ)
    {rn ygap inflH : ℕ → Ω → ℝ} (he : Equilibrium 𝔼 β συ κυ rn ygap inflH rn)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted inflH) (hba : BoundedProc ygap)
    (hbb : BoundedProc inflH) :
    ∃ ygap' inflH', Equilibrium 𝔼 β συ κυ rn ygap' inflH' rn ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted inflH' ∧ BoundedProc ygap' ∧ BoundedProc inflH' ∧
      (ygap' ≠ ygap ∨ inflH' ≠ inflH) := by
  have hx := (nk_iff_solves_exog 𝔼).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (nk_iff_solves_exog 𝔼).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### Macroeconomic implications for general `σ, η` (pp. 235, 238, 248) -/

/-- Galí (2015), p. 235: `1 + υ(ϖ − 1) > 0` for `0 ≤ υ < 1`, `σ > 0`, `η ≥ 0`. -/
theorem one_add_mul_varpi_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) :
    0 < 1 + υ * (varpi σ η υ - 1) := by
  rw [one_add_mul_varpi]
  have h1 : 0 < (1 - υ) ^ 2 := by have : 0 < 1 - υ := by linarith
                                  positivity
  have h2 : 0 ≤ υ * (2 - υ) * (σ * η) :=
    mul_nonneg (mul_nonneg hυ0 (by linarith)) (mul_nonneg hσ.le hη)
  linarith

/-- Galí (2015), p. 235: `Φ > 0`. -/
theorem Phi_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    0 < Phi σ η υ :=
  one_div_pos.2 (one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ > 0`. -/
theorem sigmaU_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    0 < sigmaU σ η υ :=
  mul_pos hσ (Phi_pos_of_lt_one hσ hη hυ0 hυ1)

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` is positive. -/
theorem natDen_pos_of_lt_one {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < natDen σ η υ φ α := by
  have := mul_pos (sigmaU_pos_of_lt_one hσ hη hυ0 hυ1) (by linarith : (0 : ℝ) < 1 - α)
  unfold natDen
  linarith

/-- Galí (2015), p. 235, `1/Φ − 1 = υ(ϖ − 1)` (used in (33)). -/
theorem inv_Phi_sub_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    1 / Phi σ η υ - 1 = υ * (varpi σ η υ - 1) := by
  have h := one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1
  unfold Phi
  field_simp
  ring

/-- Galí (2015), eq. (33), p. 237: the average markup
`μ = −(σc + φn) − υs + a − αn`, with (17), (27) and `y = a + (1 − α)n` (32), equals
`−(σ + (φ+α)/(1−α)) y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α)) a − υz`. -/
theorem markup_eq33 {σ η υ φ α c y ystar s z a n μ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) (hα1 : α < 1)
    (hμ : μ = -(σ * c + φ * n) - υ * s + a - α * n)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h32 : y = a + (1 - α) * n) :
    μ = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s +
      (1 + (φ + α) / (1 - α)) * a - υ * z := by
  have hP := Phi_pos_of_lt_one hσ hη hυ0 hυ1
  have hinv := inv_Phi_sub_one hσ hη hυ0 hυ1
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  have hn : n = (y - a) / (1 - α) := by rw [h32]; field_simp; ring
  have hys : σ * ystar = σ * y - (s + (1 - υ) * Phi σ η υ * z) / Phi σ η υ := by
    rw [h27]; unfold sigmaU; field_simp; ring
  rw [hμ, h17, hn, ← hinv]
  field_simp
  field_simp at hys
  linear_combination (-(1 - α)) * hys

/-- Galí (2015), eq. (35), p. 238 (**natural output**): at flexible prices the markup gap is
zero, so with `sⁿ = σ_υ(yⁿ − y*) − (1−υ)Φz` (eq. (27)) the flexible-price condition
`0 = −(σ + (φ+α)/(1−α)) yⁿ + υ(ϖ − 1)sⁿ + (1 + (φ+α)/(1−α)) a − υz` (eq. (33)) holds **iff**
`yⁿ = Γ_a a + Γ_z z + Γ_* y*`. -/
theorem natural_output_iff {σ η υ φ α a z ystar yn : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 = -(σ + (φ + α) / (1 - α)) * yn +
        υ * (varpi σ η υ - 1) * (sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) +
        (1 + (φ + α) / (1 - α)) * a - υ * z ↔
      yn = GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar := by
  have hkey := sigma_sub_eq_sigmaU (one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1).ne'
  have hvz : υ * varpi σ η υ * Phi σ η υ
      = υ * ((varpi σ η υ - 1) * ((1 - υ) * Phi σ η υ)) + υ := by
    have h := one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1
    unfold Phi
    field_simp
    ring
  have hD := natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1
  have h1α : (0 : ℝ) < 1 - α := by linarith
  unfold GammaA GammaZ GammaStar
  unfold natDen at hD ⊢
  rw [hvz]
  generalize varpi σ η υ = w at *
  generalize Phi σ η υ = P at *
  generalize sigmaU σ η υ = sU at *
  obtain rfl : σ = sU + υ * (w - 1) * sU := by linarith
  have hc : (sU * (1 - α) + φ + α) / (1 - α) ≠ 0 := (div_pos hD h1α).ne'
  have hid : -(sU + υ * (w - 1) * sU + (φ + α) / (1 - α)) * yn +
        υ * (w - 1) * (sU * (yn - ystar) - (1 - υ) * P * z) + (1 + (φ + α) / (1 - α)) * a -
        υ * z
      = (sU * (1 - α) + φ + α) / (1 - α) *
        ((1 + φ) / (sU * (1 - α) + φ + α) * a +
          -((υ * ((w - 1) * ((1 - υ) * P)) + υ) * (1 - α)) / (sU * (1 - α) + φ + α) * z +
          -(υ * (w - 1) * sU * (1 - α)) / (sU * (1 - α) + φ + α) * ystar - yn) := by
    field_simp
    ring
  rw [hid]
  constructor
  · intro h
    have := (mul_eq_zero.1 h.symm).resolve_left hc
    linarith
  · intro h
    rw [← h]
    ring

/-- Galí (2015), p. 248: `Γ_a > 0`, so domestic (natural) output always rises after a positive
domestic technology shock. -/
theorem GammaA_pos_of_lt_one {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < GammaA σ η υ φ α :=
  div_pos (by linarith) (natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1)

/-- Galí (2015), p. 248: the natural terms of trade
`sⁿ = σ_υ(yⁿ − y*) − (1−υ)Φz = σ_υΓ_a a + σ_υ(Γ_* − 1)y* + [σ_υΓ_z − (1−υ)Φ]z`. -/
theorem natural_tot_eq (σ η υ φ α a z ystar : ℝ) :
    sigmaU σ η υ * ((GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z +
        GammaStar σ η υ φ α * ystar) - ystar) - (1 - υ) * Phi σ η υ * z
      = sigmaU σ η υ * GammaA σ η υ φ α * a + sigmaU σ η υ * (GammaStar σ η υ φ α - 1) * ystar +
        (sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ) * z := by
  ring

/-- Galí (2015), p. 248 (**technology ⇒ real depreciation**): given world output, the
coefficient `σ_υΓ_a` of `a` in `sⁿ` is positive, and so is that of the real exchange rate
`q = (1 − υ)s` (p. 230). -/
theorem tot_tech_coeff_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < sigmaU σ η υ * GammaA σ η υ φ α ∧ 0 < (1 - υ) * (sigmaU σ η υ * GammaA σ η υ φ α) := by
  have h := mul_pos (sigmaU_pos_of_lt_one hσ hη hυ0 hυ1)
    (GammaA_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1)
  exact ⟨h, mul_pos (by linarith) h⟩

/-- Galí (2015), p. 248 (**preference shocks ⇒ real appreciation, for all parameters**):
`σ_υΓ_z − (1 − υ)Φ < 0` whenever `σ > 0`, `η ≥ 0`, `0 ≤ υ < 1`, `φ ≥ 0`, `0 ≤ α < 1`
(the book asserts the sign without proof; `ϖ` may be negative, but `ϖ ≥ −(1 − υ)`). -/
theorem tot_pref_coeff_neg {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ < 0 := by
  have hD := natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1
  have hP := Phi_pos_of_lt_one hσ hη hυ0 hυ1
  have hS := sigmaU_pos_of_lt_one hσ hη hυ0 hυ1
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hw : 0 ≤ varpi σ η υ + (1 - υ) := by
    have : varpi σ η υ + (1 - υ) = (2 - υ) * (σ * η) := by unfold varpi; ring
    rw [this]
    exact mul_nonneg (by linarith) (mul_nonneg hσ.le hη)
  have k1 : 0 ≤ sigmaU σ η υ * υ * (1 - α) * (varpi σ η υ + (1 - υ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hS.le hυ0) h1α.le) hw
  have k2 : 0 < (1 - υ) ^ 2 * sigmaU σ η υ * (1 - α) := by positivity
  have k3 : 0 ≤ (1 - υ) * (φ + α) := mul_nonneg h1υ.le (by linarith)
  have hkey : 0 < sigmaU σ η υ * υ * varpi σ η υ * (1 - α) + (1 - υ) * natDen σ η υ φ α := by
    have e : sigmaU σ η υ * υ * varpi σ η υ * (1 - α) + (1 - υ) * natDen σ η υ φ α
        = sigmaU σ η υ * υ * (1 - α) * (varpi σ η υ + (1 - υ)) +
          (1 - υ) ^ 2 * sigmaU σ η υ * (1 - α) + (1 - υ) * (φ + α) := by
      unfold natDen; ring
    rw [e]
    linarith
  have e2 : sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ
      = -(Phi σ η υ * (sigmaU σ η υ * υ * varpi σ η υ * (1 - α) +
          (1 - υ) * natDen σ η υ φ α) / natDen σ η υ φ α) := by
    unfold GammaZ
    field_simp
    ring
  rw [e2]
  exact neg_neg_of_pos (div_pos (mul_pos hP hkey) hD)

/-- Galí (2015), pp. 238 and 248 (**the special case `σ = η = 1`**): `ϖ = Φ = σ_υ = 1`,
`Γ_a = 1`, `Γ_* = 0`, `Γ_z = −υ(1−α)/(1+φ)`; hence `yⁿ = a − (υ(1−α)/(1+φ)) z` and the
coefficient of `y*` in `sⁿ` is `σ_υ(Γ_* − 1) = −1`. -/
theorem special_case (υ φ α : ℝ) (hφ : 0 ≤ φ) :
    varpi 1 1 υ = 1 ∧ Phi 1 1 υ = 1 ∧ sigmaU 1 1 υ = 1 ∧ GammaA 1 1 υ φ α = 1 ∧
      GammaStar 1 1 υ φ α = 0 ∧ GammaZ 1 1 υ φ α = -(υ * (1 - α)) / (1 + φ) ∧
      sigmaU 1 1 υ * (GammaStar 1 1 υ φ α - 1) = -1 := by
  have hv : varpi 1 1 υ = 1 := by unfold varpi; ring
  have hP : Phi 1 1 υ = 1 := by unfold Phi; rw [hv]; ring
  have hS : sigmaU 1 1 υ = 1 := by unfold sigmaU; rw [hP]; ring
  have hD : natDen 1 1 υ φ α = 1 + φ := by unfold natDen; rw [hS]; ring
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have hst : GammaStar 1 1 υ φ α = 0 := by unfold GammaStar; rw [hv]; ring
  refine ⟨hv, hP, hS, ?_, hst, ?_, ?_⟩
  · unfold GammaA; rw [hD]; field_simp
  · unfold GammaZ; rw [hD, hv, hP]; ring
  · rw [hS, hst]; ring

/-- Galí (2015), p. 248 (**the nominal exchange rate and the CPI under DIT**). Along a
realisation, let `p_H` start at the normalisation `p_{H,0} = 0` and accumulate domestic
inflation, `p_{H,t+1} = p_{H,t} + π_{H,t+1}`; let `s = e + p* − p_H` (eq. (14)),
`p = p_H + υs` (eq. (12)), and let `s − sⁿ = σ_υ(y − yⁿ)` (eq. (27) at actual and natural
values). Under SDIT (`π_H ≡ 0`, `ỹ ≡ 0`): `e_t = sⁿ_t − p*_t` and
`p_t = υ sⁿ_t = υ(e_t + p*_t)`. -/
theorem dit_exchange_rate_cpi {υ συ : ℝ} {pH inflH s e pstar p sn ygap : ℕ → ℝ}
    (hpH0 : pH 0 = 0) (hpH : ∀ t, pH (t + 1) = pH t + inflH (t + 1))
    (h14 : ∀ t, s t = e t + pstar t - pH t) (h12 : ∀ t, p t = pH t + υ * s t)
    (h27 : ∀ t, s t - sn t = συ * ygap t) (hsdit : ∀ t, inflH t = 0) (hgap : ∀ t, ygap t = 0)
    (t : ℕ) : e t = sn t - pstar t ∧ p t = υ * sn t ∧ p t = υ * (e t + pstar t) := by
  have hp0 : ∀ t, pH t = 0 := by
    intro t
    induction t with
    | zero => exact hpH0
    | succ n ih => rw [hpH n, ih, hsdit]; ring
  have hs : s t = sn t := by have := h27 t; rw [hgap t] at this; linarith
  have he : e t = sn t - pstar t := by have := h14 t; rw [hp0 t] at this; linarith
  refine ⟨he, ?_, ?_⟩
  · rw [h12 t, hp0 t, hs]; ring
  · rw [h12 t, hp0 t, hs, he]; ring

end Gali.OpenEconomy.OptimalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The welfare criterion of the small open economy

Galí (2015), Chapter 8, §8.4.3 (pp. 249–250), eqs. (43)–(44), and Appendix 8.1
(pp. 255–256), for the special case `σ = η = 1`, `Z ≡ 1`, around the efficient steady state
(the optimal subsidy `(1−τ)(1−υ)ℳ = 1` of `OptimalPolicy` in place).

## Main results

* **Lemma 1 and the analytic tools**: Lemma 1 is imported from `Supply` (`Supply.dispersion`,
  `Supply.bigTheta`, `Supply.crossVar`, `Supply.dispersion_second_order`:
  `d = (ε/(2Θ)) var_i p_H(i) + O(s³)`); restated from the Chapter 4 project here:
  `logPriceIndex_second_order`, `taylor_two`, `exp_taylor_two`, `bigO_mul`.
* **Exact layer.** `utility_exact`: with `U = log C − N^{1+φ}/(1+φ)`,
  `U(C e^ĉ, N e^n̂) − U(C, N) = ĉ − N^{1+φ}(e^{(1+φ)n̂} − 1)/(1+φ)` exactly; `marginal_utilities`
  (`U_c C = 1`, `U_n N = −N^{1+φ}`); `efficiency_iff` (`−U_n/U_c = (1−υ)(1−α)C/N` iff
  `N^{1+φ} = (1−υ)(1−α)`); `consumption_logdev` (`ĉ = (1−υ)ŷ + υŷ*` **exactly**, from
  `C = Y^{1−υ}(Y*)^υ`); `secondOrder_eq` (completing the square, exact identity with the
  explicit remainder `(1−υ)((ε/2Θ)v − d)`).
* **Analytic layer.** `period_utility_second_order`: along any one-parameter family of size `s`
  (`ŷ, â = O(s)`, `v = O(s²)`, Lemma 1 `d − (ε/2Θ)v = O(s³)`, exact employment identity
  `(1−α)n̂ = ŷ − â + d`), `(U_t − U)/(U_c C) = −((1−υ)/2)[(ε/Θ)v + ((1+φ)/(1−α))(ŷ − â)²]
  + t.i.p. + O(s³)`, with t.i.p. `= (1−υ)â + υŷ*` (world output enters only through
  t.i.p.).
* **The sign of `𝕎`** (survey error 1). `welfare_sign`: with `𝕎 ≡ −∑ βᵗ (U_t − U)/(U_c C)`,
  `𝕎 = +((1−υ)/2) ∑ βᵗ Q_t − ∑ βᵗ t.i.p._t`; `appendix_sign_error`: the displays of p. 255
  (last) and p. 256 (first), `𝕎 = −((1−υ)/2) …`, are false whenever the quadratic part is
  nonzero.
* **Lemma 2** (restated, exact for the Calvo cross-section, from the Chapter 4 project):
  `lemma2_hasSum`, `lemma2`, `lemma2_calvo`; `lemma2_printed_fails` (survey error 9): with an
  inherited dispersion `V_0 > 0` the printed equality fails by the policy-independent term
  `θV_0/(1−βθ)`, so Lemma 2 holds only up to t.i.p. (and with `π_H` replaced by `Δm`, which
  agrees to second order: `inflation_sq_sub_meanChange_sq`).
* **(43) and (44).** `welfare_eq_loss43`: exact given the Calvo recursion;
  `loss43_eq_pathLoss`, `loss43_weights_pos` connect (43) to `OptimalPolicy.optimal_policy`
  (SDIT minimises it); `welfare_stationary44`: the discounted loss of stationary variances is
  `𝕍/(1 − β)`, (44); `closed_economy_weights`: up to the factor `1 − υ` the weights are those
  of Ch. 4 with `σ = 1`.
* **`ỹ = (1−α)ñ`** (p. 256). `gap_eq_employment`: in the special case `yⁿ = a`, `nⁿ = 0`, and
  `ỹ = (1−α)ñ − d` exactly, i.e. `ỹ = (1−α)ñ` up to the second-order dispersion term.
-/

namespace Gali.OpenEconomy.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.OpenEconomy.Preferences.Variety (priceIndex)
open Gali.OpenEconomy.Supply (dispersion bigTheta crossVar priceIndex_family crossVar_family
  cgf_taylor_comp)

variable {G : Type*} [MeasurableSpace G]

/-! ### Lemma 1: price dispersion to second order

The dispersion term `Supply.dispersion`, `Supply.bigTheta`, `Supply.crossVar` and Lemma 1
(`Supply.dispersion_second_order`, with `Supply.cgf_taylor`, `Supply.priceIndex_family`,
`Supply.crossVar_family`, ...) are imported from `Supply` (restated there from the Chapter 3
project); the CES index is `Preferences.Variety.priceIndex`. -/

variable {μ : Measure G} {α ε : ℝ}

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


/-! ### App. 8.1: the exact layer (p. 255) -/

/-- Galí (2015), p. 233 (eq. (22)): `λ = (1 − θ)(1 − βθ)Θ/θ`, with `Θ = (1−α)/(1−α+αε)`. -/
noncomputable def lambdaH (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), App. 8.1, p. 255: period utility for `σ = 1`, `Z ≡ 1`,
`U(C, N) = log C − N^{1+φ}/(1+φ)`. -/
noncomputable def periodUtility (φ C N : ℝ) : ℝ := Real.log C - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), App. 8.1, p. 255: the marginal utilities `U_c = 1/C`, `U_n = −N^φ` (exact
derivatives), so `U_c C = 1` and `U_n N = −N^{1+φ}`. -/
theorem marginal_utilities {φ C N : ℝ} (hφ : 0 ≤ φ) (hC : 0 < C) (hN : 0 < N) :
    HasDerivAt (fun c => periodUtility φ c N) C⁻¹ C ∧
      HasDerivAt (fun n => periodUtility φ C n) (-(N ^ φ)) N ∧
      C⁻¹ * C = 1 ∧ -(N ^ φ) * N = -(N ^ (1 + φ)) := by
  refine ⟨(Real.hasDerivAt_log hC.ne').sub_const _, ?_, inv_mul_cancel₀ hC.ne', ?_⟩
  · have h2 : HasDerivAt (fun n : ℝ => n ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
      refine ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inr (by linarith))).div_const
        (1 + φ)).congr_deriv ?_
      rw [show (1 : ℝ) + φ - 1 = φ by ring]
      field_simp
    exact h2.const_sub (Real.log C)
  · rw [Real.rpow_add hN, Real.rpow_one]
    ring

/-- Galí (2015), App. 8.1, p. 255 (and p. 246): efficiency of the steady state,
`−U_n/U_c = (1−υ)(1−α) C/N` with `U_c = 1/C`, `U_n = −N^φ`, holds **iff**
`N^{1+φ} = (1−υ)(1−α)`. -/
theorem efficiency_iff {υ φ α C N : ℝ} (hC : 0 < C) (hN : 0 < N) :
    -(-(N ^ φ)) / C⁻¹ = (1 - υ) * (1 - α) * C / N ↔ N ^ (1 + φ) = (1 - υ) * (1 - α) := by
  rw [Real.rpow_add hN, Real.rpow_one, neg_neg, div_inv_eq_mul, eq_div_iff hN.ne']
  constructor
  · intro h
    have := mul_left_cancel₀ hC.ne' (by linear_combination h : C * (N ^ φ * N) =
      C * ((1 - υ) * (1 - α)))
    linear_combination this
  · intro h
    linear_combination C * h

/-- Galí (2015), App. 8.1, p. 255 (**exact**): with `C_t = C e^{ĉ}`, `N_t = N e^{n̂}`,
`U(C_t, N_t) − U(C, N) = ĉ − N^{1+φ}(e^{(1+φ)n̂} − 1)/(1+φ)`. -/
theorem utility_exact {φ C N : ℝ} (hC : 0 < C) (hN : 0 < N) (c n : ℝ) :
    periodUtility φ (C * Real.exp c) (N * Real.exp n) - periodUtility φ C N
      = c - N ^ (1 + φ) * (Real.exp ((1 + φ) * n) - 1) / (1 + φ) := by
  unfold periodUtility
  rw [Real.log_mul hC.ne' (Real.exp_pos c).ne', Real.log_exp,
    Real.mul_rpow hN.le (Real.exp_pos n).le, ← Real.exp_mul]
  rw [show n * (1 + φ) = (1 + φ) * n by ring]
  ring

/-- Galí (2015), App. 8.1, p. 255: `ĉ = (1 − υ)ŷ + υŷ*` holds **exactly** in log deviations
along the possibilities set `C = Y^{1−υ}(Y*)^υ` (`OptimalPolicy.consumption_possibilities`). -/
theorem consumption_logdev {υ Y Ys Yt Yst : ℝ} (hY : 0 < Y) (hYs : 0 < Ys) (hYt : 0 < Yt)
    (hYst : 0 < Yst) :
    Real.log (Yt ^ (1 - υ) * Yst ^ υ) - Real.log (Y ^ (1 - υ) * Ys ^ υ)
      = (1 - υ) * (Real.log Yt - Real.log Y) + υ * (Real.log Yst - Real.log Ys) := by
  rw [OptimalPolicy.log_consumption hYt hYst, OptimalPolicy.log_consumption hY hYs]
  ring

/-- Galí (2015), App. 8.1, p. 255 (**completing the square, exact**): if
`(1−α)n̂ = ŷ − â + d` (exact employment identity, `d` the dispersion term), then
`(1−υ)ŷ + υŷ* − (1−υ)(1−α)(n̂ + ((1+φ)/2)n̂²)
 = −((1−υ)/2)[(ε/Θ)v + (1+φ)(1−α)n̂²] + ((1−υ)â + υŷ*) + (1−υ)((ε/2Θ)v − d)`
for every `v`. The left side is the book's second-order polynomial with `U_c C = 1` and the
efficiency condition `U_n N = −(1−υ)(1−α)`. -/
theorem secondOrder_eq {υ φ α ε y ystar a n d v : ℝ} (hn : (1 - α) * n = y - a + d) :
    (1 - υ) * y + υ * ystar - (1 - υ) * (1 - α) * (n + (1 + φ) / 2 * n ^ 2)
      = -((1 - υ) / 2) * (ε / bigTheta α ε * v + (1 + φ) * (1 - α) * n ^ 2) +
          ((1 - υ) * a + υ * ystar) + (1 - υ) * (ε / (2 * bigTheta α ε) * v - d) := by
  linear_combination (-(1 - υ)) * hn

/-- Galí (2015), App. 8.1, p. 256: the employment term in output-gap form,
`(1+φ)(1−α)n̂² = ((1+φ)/(1−α))(ŷ − â + d)²` (exact, `α ≠ 1`). -/
theorem gap_form {φ α y a n d : ℝ} (hα : α ≠ 1) (hn : (1 - α) * n = y - a + d) :
    (1 + φ) * (1 - α) * n ^ 2 = (1 + φ) / (1 - α) * (y - a + d) ^ 2 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  rw [← hn]
  field_simp

/-! ### App. 8.1: the analytic layer -/

/-- Galí (2015), App. 8.1, pp. 255–256 (**second-order approximation of period utility,
rigorous form**). Utility `log C − N^{1+φ}/(1+φ)` (`σ = 1`, `Z ≡ 1`; `U_c C = 1`), efficient
steady state `N^{1+φ} = (1−υ)(1−α)`, consumption on the possibilities set
`C_t = C e^{(1−υ)ŷ + υŷ*}`. Along a one-parameter family of size `s` with `ŷ, â = O(s)`, a
cross-sectional price variance `v = O(s²)`, Lemma 1 `d − (ε/2Θ)v = O(s³)` and the exact
employment identity `(1−α)n̂ = ŷ − â + d`:
`U_t − U = −((1−υ)/2)[(ε/Θ)v + ((1+φ)/(1−α))(ŷ − â)²] + ((1−υ)â + υŷ*) + O(s³)`.
No order assumption on `ŷ*` is needed: it enters only the terms independent of policy. -/
theorem period_utility_second_order {υ φ α ε C N : ℝ} {y ystar a n d v : ℝ → ℝ}
    (hC : 0 < C) (hN : 0 < N) (hEff : N ^ (1 + φ) = (1 - υ) * (1 - α)) (hφ : 0 ≤ φ)
    (hα : α ≠ 1) (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => periodUtility φ (C * Real.exp ((1 - υ) * y s + υ * ystar s))
          (N * Real.exp (n s)) - periodUtility φ C N
        - (-((1 - υ) / 2) * (ε / bigTheta α ε * v s + (1 + φ) / (1 - α) * (y s - a s) ^ 2) +
          ((1 - υ) * a s + υ * ystar s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hφ1 : (1 : ℝ) + φ ≠ 0 := by linarith
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have hx1 : (fun s => (1 + φ) * n s) =O[𝓝 0] fun s => s ^ 1 := hn1.const_mul_left _
  have cube : (fun s => ((1 + φ) * n s) ^ 3) =O[𝓝 0] fun s => s ^ 3 := by
    have := hx1.pow 3
    simpa [← pow_mul] using this
  have hR : (fun s => Real.exp ((1 + φ) * n s) - 1 - (1 + φ) * n s - ((1 + φ) * n s) ^ 2 / 2)
      =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hx1)).trans cube
  have T1 : (fun s => (1 - υ) * (c * v s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left (1 - υ)).congr_left fun s => by ring
  have T2 := hR.const_mul_left (-(N ^ (1 + φ)) / (1 + φ))
  have T3 : (fun s => -((1 - υ) / 2) * ((1 + φ) / (1 - α)) *
      (2 * (y s - a s) * d s + d s ^ 2)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    exact (e1.add e2).const_mul_left _
  refine ((T1.add T2).add T3).congr_left fun s => ?_
  rw [utility_exact hC hN, hEff]
  have hns : n s = (y s - a s + d s) / (1 - α) := by
    rw [eq_div_iff h1]; linear_combination hn s
  generalize Real.exp ((1 + φ) * n s) = E
  rw [hns, hc]
  field_simp
  ring

/-! ### The sign of `𝕎` (survey error 1) -/

/-- Galí (2015), App. 8.1, pp. 255–256 (**the correct sign**): with
`𝕎 ≡ −∑ βᵗ (U_t − U)/(U_c C)` and `(U_t − U)/(U_c C) = −((1−υ)/2) Q_t + t.i.p._t`, the
welfare loss is `𝕎 = +((1−υ)/2) ∑ βᵗ Q_t − ∑ βᵗ t.i.p._t`. -/
theorem welfare_sign {υ β : ℝ} {dU Q tip : ℕ → ℝ}
    (hdU : ∀ t, dU t = -((1 - υ) / 2) * Q t + tip t) (hQ : Summable fun t => β ^ t * Q t)
    (hT : Summable fun t => β ^ t * tip t) :
    HasSum (fun t => -(β ^ t * dU t)) ((1 - υ) / 2 * ∑' t, β ^ t * Q t - ∑' t, β ^ t * tip t) := by
  have h := (hQ.hasSum.mul_left ((1 - υ) / 2)).sub hT.hasSum
  convert h using 1
  funext t
  rw [hdU t]
  ring

/-- Galí (2015), App. 8.1, p. 255 last display and p. 256 first display (**survey error 1**):
the printed `𝕎 = −((1−υ)/2) E₀ ∑ βᵗ […]` (up to t.i.p.) is false. For `υ < 1`, nonnegative
quadratic terms `Q_t` with `∑ βᵗ Q_t ≠ 0`, the true policy-dependent part of `𝕎` is
`+((1−υ)/2)∑ βᵗ Q_t > 0`, which differs from the printed `−((1−υ)/2)∑ βᵗ Q_t < 0`. -/
theorem appendix_sign_error {υ β : ℝ} {Q : ℕ → ℝ} (hυ : υ < 1) (hβ : 0 ≤ β)
    (hQ0 : ∀ t, 0 ≤ Q t) (hne : ∑' t, β ^ t * Q t ≠ 0) :
    0 < (1 - υ) / 2 * ∑' t, β ^ t * Q t ∧ -((1 - υ) / 2) * ∑' t, β ^ t * Q t < 0 ∧
      (1 - υ) / 2 * ∑' t, β ^ t * Q t ≠ -((1 - υ) / 2) * ∑' t, β ^ t * Q t := by
  have hS : 0 < ∑' t, β ^ t * Q t :=
    lt_of_le_of_ne (tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ t) (hQ0 t)) (Ne.symm hne)
  have hp : 0 < (1 - υ) / 2 * ∑' t, β ^ t * Q t := mul_pos (by linarith) hS
  refine ⟨hp, by linarith, fun h => by linarith⟩

/-! ### Lemma 2 up to t.i.p. (survey error 9) -/

/-- Galí (2015), Lemma 2, p. 256 (**survey error 9**): the printed equality
`∑ βᵗ var_t = θ/((1−βθ)(1−θ)) ∑ βᵗ π²` fails as an exact statement once there is inherited
dispersion: with `V_0 > 0`, `θ > 0` the left side exceeds the right side by the
policy-independent term `θ V_0/(1 − βθ)` (and `π_H` must be read as `Δm`, to second order,
`inflation_sq_sub_meanChange_sq`). -/
theorem lemma2_printed_fails {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hV0 : 0 < V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    ∑' t, β ^ t * V (t + 1)
        = θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t + θ * V 0 / (1 - β * θ) ∧
      ∑' t, β ^ t * V (t + 1) ≠ θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t := by
  have hβθ : β * θ < 1 := by nlinarith
  have h := lemma2_hasSum hθ0.le hβ0 hβθ (div_nonneg hθ0.le (by linarith)) hV0.le hq hrec hQ
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 0 < 1 - β * θ := by linarith
  have e : ∑' t, β ^ t * V (t + 1)
      = θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t + θ * V 0 / (1 - β * θ) := by
    rw [h.tsum_eq]
    field_simp
    ring
  refine ⟨e, fun h' => ?_⟩
  rw [e] at h'
  have : 0 < θ * V 0 / (1 - β * θ) := div_pos (mul_pos hθ0 hV0) h2
  linarith

/-! ### The loss function (43) and the average loss (44) -/

/-- Galí (2015), eq. (43), p. 249: the period loss
`((1−υ)/2)[((1+φ)/(1−α)) ỹ² + (ε/λ) π_H²]`. -/
noncomputable def periodLoss43 (β θ υ φ α ε ygap inflH : ℝ) : ℝ :=
  (1 - υ) / 2 * ((1 + φ) / (1 - α) * ygap ^ 2 + ε / lambdaH β θ α ε * inflH ^ 2)

/-- Galí (2015), eq. (43), p. 249: `𝕎 = ∑ βᵗ ((1−υ)/2)[((1+φ)/(1−α)) ỹ_t² + (ε/λ) π_{H,t}²]`
for a given path. -/
noncomputable def loss43 (β θ υ φ α ε : ℝ) (ygap inflH : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss43 β θ υ φ α ε (ygap t) (inflH t)

/-- Galí (2015), App. 8.1, p. 256: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`. -/
theorem inflWeight_of_dispersion {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaH β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaH bigTheta
  field_simp

/-- Galí (2015), App. 8.1, p. 256 and eq. (43) (**exact given the Calvo recursion**): if the
cross-sectional variance of domestic prices follows `V_{t+1} = θV_t + (θ/(1−θ))(Δm_t)²` with
no inherited dispersion, then
`∑ βᵗ ((1−υ)/2)[((1+φ)/(1−α)) ỹ_t² + (ε/Θ) V_{t+1}] = 𝕎(ỹ, Δm)` of (43). -/
theorem welfare_eq_loss43 {β θ υ φ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα : α < 1) {ygap Dm V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * Dm t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hD : Summable fun t => β ^ t * Dm t ^ 2) :
    HasSum (fun t => β ^ t * ((1 - υ) / 2 *
        ((1 + φ) / (1 - α) * ygap t ^ 2 + ε / bigTheta α ε * V (t + 1))))
      (loss43 β θ υ φ α ε ygap Dm) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => Dm t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hA := ((hY.hasSum.mul_left ((1 + φ) / (1 - α))).add
    (hL.mul_left (ε / bigTheta α ε))).mul_left ((1 - υ) / 2)
  have hB := ((hY.hasSum.mul_left ((1 + φ) / (1 - α))).add
    (hD.hasSum.mul_left (ε / lambdaH β θ α ε))).mul_left ((1 - υ) / 2)
  have hW : loss43 β θ υ φ α ε ygap Dm = (1 - υ) / 2 * ((1 + φ) / (1 - α) *
      ∑' t, β ^ t * ygap t ^ 2 + ε / lambdaH β θ α ε * ∑' t, β ^ t * Dm t ^ 2) := by
    rw [← hB.tsum_eq]
    unfold loss43 periodLoss43
    congr 1
    funext t
    ring
  rw [hW, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), eqs. (43)–(44), p. 249: the weights of (43) are positive for `υ < 1`,
`φ ≥ 0`, `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `β < 1`. -/
theorem loss43_weights_pos {β θ υ φ α ε : ℝ} (hυ : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < (1 - υ) / 2 * ((1 + φ) / (1 - α)) ∧ 0 < (1 - υ) / 2 * (ε / lambdaH β θ α ε) := by
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hβθ : 0 < 1 - β * θ := by nlinarith
  have hΘ : 0 < bigTheta α ε := div_pos h1α (by nlinarith)
  have hl : 0 < lambdaH β θ α ε := mul_pos (div_pos (mul_pos (by linarith) hβθ) hθ0) hΘ
  exact ⟨mul_pos (by linarith) (div_pos (by linarith) h1α),
    mul_pos (by linarith) (div_pos hε hl)⟩

/-- Galí (2015), eq. (43), p. 249: (43) along a state `ω` is the loss `pathLoss a b β` of
`OptimalPolicy` with `a = ((1−υ)/2)(1+φ)/(1−α)`, `b = ((1−υ)/2)ε/λ`; hence
(`OptimalPolicy.optimal_policy`, `loss43_weights_pos`) SDIT minimises it. -/
theorem loss43_eq_pathLoss {Ω : Type*} (β θ υ φ α ε : ℝ) (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) :
    loss43 β θ υ φ α ε (fun t => ygap t ω) (fun t => inflH t ω)
      = OptimalPolicy.pathLoss ((1 - υ) / 2 * ((1 + φ) / (1 - α)))
          ((1 - υ) / 2 * (ε / lambdaH β θ α ε)) β ygap inflH ω := by
  unfold loss43 periodLoss43 OptimalPolicy.pathLoss
  congr 1
  funext t
  ring

/-- Galí (2015), eq. (44), p. 249: the expected period loss
`𝕍 = ((1−υ)/2)[((1+φ)/(1−α)) var(ỹ) + (ε/λ) var(π_H)]`. -/
noncomputable def avgLoss44 (β θ υ φ α ε varY varPi : ℝ) : ℝ :=
  (1 - υ) / 2 * ((1 + φ) / (1 - α) * varY + ε / lambdaH β θ α ε * varPi)

/-- Galí (2015), eq. (44), p. 249 (**from (43) to (44)**): if the expected squared gap and
squared domestic inflation equal stationary variances at every date, the discounted expected
loss is `𝕍/(1 − β)`. -/
theorem welfare_stationary44 {β θ υ φ α ε varY varPi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {eY eP : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varPi) :
    HasSum (fun t => β ^ t * ((1 - υ) / 2 * ((1 + φ) / (1 - α) * eY t +
        ε / lambdaH β θ α ε * eP t)))
      (avgLoss44 β θ υ φ α ε varY varPi / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (avgLoss44 β θ υ φ α ε varY varPi)
  convert h using 1
  · funext t
    rw [heY, heP, avgLoss44]
  · rw [div_eq_inv_mul]

/-- Galí (2015), p. 249: "up to the multiplicative term `(1 − υ)`" the weights are those of the
closed economy (Ch. 4, p. 111) with `σ = 1`: `σ + (φ+α)/(1−α) = (1+φ)/(1−α)` at `σ = 1`. -/
theorem closed_economy_weights {φ α : ℝ} (hα : α ≠ 1) :
    1 + (φ + α) / (1 - α) = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-! ### `ỹ = (1 − α) ñ` (p. 256) -/

/-- Galí (2015), App. 8.1, p. 256: in the special case (`σ = η = 1`, `z = 0`) natural output
(35) is `yⁿ = Γ_a a + Γ_* y* = a`; at flexible prices there is no dispersion, so
`(1−α)nⁿ = yⁿ − a` gives `nⁿ = 0`; with `(1−α)n̂ = ŷ − â + d`,
`ỹ = ŷ − yⁿ = (1−α)(n̂ − nⁿ) − d` **exactly**, so the book's `ỹ = (1−α)ñ` holds up to the
second-order dispersion term `d`. -/
theorem gap_eq_employment {υ φ α a ystar yn nn y n d : ℝ} (hφ : 0 ≤ φ) (hα : α < 1)
    (hyn : yn = Supply.GammaA 1 1 υ φ α * a + Supply.GammaZ 1 1 υ φ α * 0 +
      Supply.GammaStar 1 1 υ φ α * ystar)
    (hnn : (1 - α) * nn = yn - a) (hn : (1 - α) * n = y - a + d) :
    yn = a ∧ nn = 0 ∧ y - yn = (1 - α) * (n - nn) - d := by
  obtain ⟨-, -, -, hA, hS, -, -⟩ := OptimalPolicy.special_case υ φ α hφ
  have hyn' : yn = a := by rw [hyn, hA, hS]; ring
  have hnn' : nn = 0 := by
    rw [hyn', sub_self] at hnn
    exact (mul_eq_zero.1 hnn).resolve_left (by linarith)
  refine ⟨hyn', hnn', ?_⟩
  rw [hyn', hnn']
  linear_combination -hn

end Gali.OpenEconomy.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Simple monetary policy rules for the small open economy

Galí (2015), Chapter 8, §8.5, pp. 250–252, Table 8.1 and footnotes 14–15.

## Main results

* **The regimes** (p. 250): `SDIT` (`π_H ≡ 0`), `SCIT` (`π ≡ 0`), `PEG` (`e ≡ 0`), `FDIT`
  (`i = ρ + 1.5π_H + 0.125y`), `FCIT` (`i = ρ + 1.5π + 0.125y`). `peg_rate`: under the UIP
  condition (18), a peg forces `i = i*` (p. 250).
* **Table 8.1, loss row** (pp. 251–252). `lambda_calibration` (`λ = 103/4800`, **including**
  `Θ = 1/4`), `tableLoss_eq_avgLoss44` (the row is (44) in percent of steady-state
  consumption), `tableLoss_values` (recomputed from the printed standard deviations:
  0.0559, 0.1745, 0.6037, 0.4325 against the printed .05, .17, .61, .43),
  `tableLoss_consistent` (each printed loss is attained by standard deviations that round to the
  printed ones), `tableLoss_noTheta_inconsistent` (with `λ` **without** `Θ` the FDIT loss
  would be below 0.2 for every admissible rounding, so the table uses `λ` with `Θ`),
  `tot_eq_output` (the `σ(s)` and `σ(y)` rows coincide since `s = y` here).
* **Survey error 6** (p. 251): `peg_not_most_volatile_inflation` (PEG does not have the largest
  `σ(π_H)`: FDIT and FCIT do), `peg_most_volatile_strict` (true among SDIT, SCIT, PEG),
  `peg_most_volatile_gap` (true for the output gap).
* **Survey error 7** (fn. 14): `world_output_effects`: with `σ = η = 1`, `yⁿ` (hence `ỹ`, `π_H`)
  does not depend on `y*`, but `sⁿ` has coefficient `−1` on `y*`, and `c`, the CPI under SDIT
  and `e^{DIT}` all move with `y*`.
* **Survey error 8** (fn. 15). `exchange_rate_identity` (`e = s + p_H − p* = (1−υ)s + p − p*`);
  `sdit_meanReverting`, `scit_meanReverting`, `peg_meanReverting`: under SDIT, SCIT and PEG
  the level of `e` is a fixed function of stationary variables and its response to a
  transitory shock dies out; `fdit_solution`, `fdit_unique`: the FDIT equilibrium response to
  an AR(1) technology shock (for any expectation system); `fdit_unit_root`,
  `fdit_permanent_shift`: under FDIT the
  level of `e` converges to `B a₀/(1−ρ_a) ≠ 0` after a one-time technology shock (a permanent
  shift, i.e. a unit root) while `Δe → 0`; `fcit_cumulative`: under FCIT the same accounting
  (`e_{T+1} − e_0 = φ_π(p_T − p_{−1}) + φ_y ∑ y_t`).
-/

namespace Gali.OpenEconomy.SimpleRules

open Filter Topology

/-! ### The regimes (p. 250) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 250: strict domestic inflation targeting, `π_{H,t} = 0` for all `t`. -/
def SDIT (inflH : ℕ → Ω → ℝ) : Prop := ∀ t, inflH t = 0

/-- Galí (2015), p. 250: strict CPI inflation targeting, `π_t = 0` for all `t`. -/
def SCIT (infl : ℕ → Ω → ℝ) : Prop := ∀ t, infl t = 0

/-- Galí (2015), p. 250: an exchange-rate peg, `e_t = 0` for all `t`. -/
def PEG (e : ℕ → Ω → ℝ) : Prop := ∀ t, e t = 0

/-- Galí (2015), p. 250: a Taylor-type rule `i_t = ρ + φ_π x_t + φ_y y_t` reacting to an
inflation measure `x` and to output `y`. -/
def TaylorType (rho φπ φy : ℝ) (i x y : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => rho) + φπ • x t + φy • y t

/-- Galí (2015), p. 250: FDIT, `i_t = 0.01 + 1.5 π_{H,t} + 0.125 y_t`. -/
def FDIT (i inflH y : ℕ → Ω → ℝ) : Prop := TaylorType (1 / 100) (3 / 2) (1 / 8) i inflH y

/-- Galí (2015), p. 250: FCIT, `i_t = 0.01 + 1.5 π_t + 0.125 y_t`. -/
def FCIT (i infl y : ℕ → Ω → ℝ) : Prop := TaylorType (1 / 100) (3 / 2) (1 / 8) i infl y

/-- Galí (2015), eq. (18), p. 232: uncovered interest parity
`i_t = i*_t + E_t{Δe_{t+1}}` (with `e` adapted). -/
def UIP (i istar e : ℕ → Ω → ℝ) : Prop := ∀ t, i t = istar t + (𝔼.E t (e (t + 1)) - e t)

/-- Galí (2015), p. 250: under UIP (18), a peg `e ≡ 0` "in turn requires that `i_t = i*_t`". -/
theorem peg_rate {i istar e : ℕ → Ω → ℝ} (huip : UIP 𝔼 i istar e) (hpeg : PEG e) :
    ∀ t, i t = istar t := by
  intro t
  rw [huip t, hpeg (t + 1), hpeg t, map_zero, sub_zero, add_zero]

/-! ### Table 8.1: the loss row (pp. 251–252) -/

/-- Galí (2015), p. 233 and the Ch. 3 baseline (p. 58: `β = 0.99`, `θ = 3/4`, `α = 1/4`,
`ε = 9`): `λ = (1−θ)(1−βθ)Θ/θ = 103/4800`, with `Θ = 1/4`. -/
theorem lambda_calibration :
    Supply.bigTheta (1 / 4) 9 = 1 / 4 ∧
      Welfare.lambdaH (99 / 100) (3 / 4) (1 / 4) 9 = 103 / 4800 := by
  unfold Welfare.lambdaH Supply.bigTheta
  norm_num

/-- Galí (2015), Table 8.1, p. 251: the welfare loss (44) in percent of steady-state
consumption, as a function of the standard deviations (in percent) of `ỹ` and `π_H`, at the
baseline `υ = 0.4`, `φ = 5`, `α = 1/4`, `ε = 9`, `ε/λ = 43200/103`. -/
noncomputable def tableLoss (sy sp : ℝ) : ℝ := 3 / 10 * (8 * sy ^ 2 + 43200 / 103 * sp ^ 2) / 100

/-- Galí (2015), Table 8.1 and eq. (44): `tableLoss` is `100 · 𝕍` with variances
`(sy/100)²`, `(sp/100)²` at the baseline calibration. -/
theorem tableLoss_eq_avgLoss44 (sy sp : ℝ) :
    tableLoss sy sp = 100 * Welfare.avgLoss44 (99 / 100) (3 / 4) (2 / 5) 5 (1 / 4) 9
      ((sy / 100) ^ 2) ((sp / 100) ^ 2) := by
  unfold Welfare.avgLoss44
  rw [lambda_calibration.2]
  unfold tableLoss
  ring

/-- Galí (2015), Table 8.1 (loss row recomputed): from the printed standard deviations the
losses are SDIT 0, SCIT ≈ 0.0559, PEG ≈ 0.1745, FDIT ≈ 0.6037, FCIT ≈ 0.4325 (printed: 0, .05,
.17, .61, .43). -/
theorem tableLoss_values :
    tableLoss 0 0 = 0 ∧
      (0.0558 < tableLoss 0.66 0.19 ∧ tableLoss 0.66 0.19 < 0.0559) ∧
      (0.1744 < tableLoss 0.92 0.35 ∧ tableLoss 0.92 0.35 < 0.1745) ∧
      (0.6036 < tableLoss 0.44 0.69 ∧ tableLoss 0.44 0.69 < 0.6038) ∧
      (0.4325 < tableLoss 0.62 0.58 ∧ tableLoss 0.62 0.58 < 0.4326) := by
  unfold tableLoss
  norm_num

/-- Galí (2015), Table 8.1 (**consistency with (44)**): for every regime there are standard
deviations that round (to two decimals) to the printed ones and whose loss rounds to the
printed loss: SCIT `(0.66, 0.186) ↦ 0.0540 ∈ [0.045, 0.055)`, PEG `(0.92, 0.35) ↦ 0.1745`,
FDIT `(0.44, 0.692) ↦ 0.6072 ∈ [0.605, 0.615)`, FCIT `(0.62, 0.58) ↦ 0.4325`. -/
theorem tableLoss_consistent :
    (0.045 ≤ tableLoss 0.66 0.186 ∧ tableLoss 0.66 0.186 < 0.055) ∧
      (0.165 ≤ tableLoss 0.92 0.35 ∧ tableLoss 0.92 0.35 < 0.175) ∧
      (0.605 ≤ tableLoss 0.44 0.692 ∧ tableLoss 0.44 0.692 < 0.615) ∧
      (0.425 ≤ tableLoss 0.62 0.58 ∧ tableLoss 0.62 0.58 < 0.435) := by
  unfold tableLoss
  norm_num

/-- Galí (2015), Table 8.1 with `λ` computed **without** `Θ` (`ε/λ = 10800/103`). -/
noncomputable def tableLossNoTheta (sy sp : ℝ) : ℝ :=
  3 / 10 * (8 * sy ^ 2 + 10800 / 103 * sp ^ 2) / 100

/-- Galí (2015), Table 8.1 (**the table uses `λ` with `Θ`**, p. 233): with `λ` lacking `Θ`,
every pair of standard deviations rounding to FDIT's printed `(0.44, 0.69)` gives a loss
below 0.2, far from the printed 0.61. -/
theorem tableLoss_noTheta_inconsistent {sy sp : ℝ} (hy0 : 0 ≤ sy) (hy1 : sy ≤ 0.445)
    (hp0 : 0 ≤ sp) (hp1 : sp ≤ 0.695) : tableLossNoTheta sy sp < 0.2 := by
  unfold tableLossNoTheta
  have h1 : sy ^ 2 ≤ 0.445 ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have h2 : sp ^ 2 ≤ 0.695 ^ 2 := pow_le_pow_left₀ hp0 hp1 2
  norm_num at h1 h2 ⊢
  nlinarith

/-- Galí (2015), Table 8.1 (rows `σ(y)` and `σ(s)` coincide): with `σ = η = 1`, technology
shocks only (`y* = z = 0`), eq. (27) gives `s = σ_υ(y − y*) − (1−υ)Φz = y`. -/
theorem tot_eq_output (υ y : ℝ) :
    AggregateDemand.sigmaU 1 1 υ * (y - 0) - (1 - υ) * AggregateDemand.Phi 1 1 υ * 0 = y := by
  obtain ⟨-, -, hS, -⟩ := OptimalPolicy.special_case υ 0 0 le_rfl
  rw [hS]
  ring

/-! ### Survey error 6: the volatility ranking (p. 251) -/

/-- Galí (2015), Table 8.1: `σ(π_H)` by regime, in the order SDIT, SCIT, PEG, FDIT, FCIT. -/
noncomputable def sdInflH : Fin 5 → ℝ := ![0, 0.19, 0.35, 0.69, 0.58]

/-- Galí (2015), Table 8.1: `σ(ỹ)` by regime, in the order SDIT, SCIT, PEG, FDIT, FCIT. -/
noncomputable def sdGap : Fin 5 → ℝ := ![0, 0.66, 0.92, 0.44, 0.62]

/-- Galí (2015), p. 251 (**survey error 6**): "the PEG regime is the one that amplifies …
domestic inflation volatility to the largest extent" is inconsistent with Table 8.1: FDIT
(0.69) and FCIT (0.58) have larger `σ(π_H)` than PEG (0.35). -/
theorem peg_not_most_volatile_inflation :
    ¬ (∀ r, sdInflH r ≤ sdInflH 2) ∧ sdInflH 2 < sdInflH 3 ∧ sdInflH 2 < sdInflH 4 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := h 3
    simp [sdInflH] at this
    norm_num at this
  · simp [sdInflH]; norm_num
  · simp [sdInflH]; norm_num

/-- Galí (2015), p. 251 (corrected reading): among the three strict regimes SDIT, SCIT, PEG,
PEG has the largest `σ(π_H)`. -/
theorem peg_most_volatile_strict : ∀ r : Fin 5, r.val ≤ 2 → sdInflH r ≤ sdInflH 2 := by
  intro r hr
  fin_cases r <;> simp [sdInflH] at hr ⊢ <;> norm_num

/-- Galí (2015), p. 251: PEG does have the largest output-gap volatility among all five. -/
theorem peg_most_volatile_gap : ∀ r : Fin 5, sdGap r ≤ sdGap 2 := by
  intro r
  fin_cases r <;> simp [sdGap] <;> norm_num

/-! ### Survey error 7: world output (fn. 14) -/

/-- Galí (2015), fn. 14, p. 251 (**survey error 7**): with `σ = η = 1` (and `z = 0`), natural
output `yⁿ = Γ_a a + Γ_* y*` does not depend on `y*` (so neither do `ỹ`, `π_H` under any
rule); but the natural terms of trade `sⁿ = σ_υΓ_a a + σ_υ(Γ_* − 1)y* = a − y*`, consumption
`c = (1−υ)y + υy*`, the CPI under SDIT `p = υsⁿ` and `e^{DIT} = sⁿ − p*` all move with `y*`
(for `υ > 0`): world output does affect the domestic economy. -/
theorem world_output_effects {υ φ α : ℝ} (hφ : 0 ≤ φ) (hυ : 0 < υ) (a y ystar ystar' pstar : ℝ)
    (hne : ystar ≠ ystar') :
    (Supply.GammaA 1 1 υ φ α * a + Supply.GammaStar 1 1 υ φ α * ystar
        = Supply.GammaA 1 1 υ φ α * a + Supply.GammaStar 1 1 υ φ α * ystar') ∧
      (AggregateDemand.sigmaU 1 1 υ * Supply.GammaA 1 1 υ φ α * a +
          AggregateDemand.sigmaU 1 1 υ * (Supply.GammaStar 1 1 υ φ α - 1) * ystar
        = a - ystar) ∧
      a - ystar ≠ a - ystar' ∧
      (1 - υ) * y + υ * ystar ≠ (1 - υ) * y + υ * ystar' ∧
      υ * (a - ystar) ≠ υ * (a - ystar') ∧
      (a - ystar) - pstar ≠ (a - ystar') - pstar := by
  obtain ⟨-, -, hS, hA, hst, -, -⟩ := OptimalPolicy.special_case υ φ α hφ
  refine ⟨by rw [hst]; ring, by rw [hS, hA, hst]; ring, fun h => hne (by linarith),
    fun h => hne ?_, fun h => hne ?_, fun h => hne (by linarith)⟩
  · have : υ * (ystar - ystar') = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hυ.ne'
    linarith
  · have : υ * (ystar' - ystar) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hυ.ne'
    linarith

/-! ### Survey error 8: stationarity of the nominal exchange rate (fn. 15) -/

/-- Galí (2015), eqs. (12) and (14), pp. 229–230: `e = s + p_H − p* = (1−υ)s + p − p*`. -/
theorem exchange_rate_identity {υ s e pstar pH p : ℝ} (h14 : s = e + pstar - pH)
    (h12 : p = pH + υ * s) : e = s + pH - pstar ∧ e = (1 - υ) * s + p - pstar := by
  constructor <;> linarith

/-- Galí (2015), fn. 15 (SDIT): with `p_H ≡ 0` and constant `p*`, `e_t = sⁿ_t − p*`, so the level
of `e` mean-reverts whenever the natural terms of trade do. -/
theorem sdit_meanReverting {sn e : ℕ → ℝ} {pstar : ℝ} (he : ∀ t, e t = sn t - pstar)
    (hs : Tendsto sn atTop (𝓝 0)) : Tendsto e atTop (𝓝 (-pstar)) := by
  have := hs.sub_const pstar
  simp only [zero_sub] at this
  exact this.congr fun t => (he t).symm

/-- Galí (2015), fn. 15 (SCIT): with `π ≡ 0` the CPI is constant (`p ≡ p_{−1} = 0`), so by (12)
`p_H = −υs` and `e = (1−υ)s − p*`; `e` mean-reverts whenever the terms of trade do. -/
theorem scit_meanReverting {υ pstar : ℝ} {s e p pH infl : ℕ → ℝ} (hp0 : p 0 = infl 0)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hscit : ∀ t, infl t = 0)
    (h14 : ∀ t, s t = e t + pstar - pH t) (h12 : ∀ t, p t = pH t + υ * s t)
    (hs : Tendsto s atTop (𝓝 0)) :
    (∀ t, e t = (1 - υ) * s t - pstar) ∧ Tendsto e atTop (𝓝 (-pstar)) := by
  have hp0' : ∀ t, p t = 0 := by
    intro t
    induction t with
    | zero => rw [hp0, hscit]
    | succ n ih => rw [hp n, ih, hscit]; ring
  have he : ∀ t, e t = (1 - υ) * s t - pstar := by
    intro t
    have := h12 t
    have := h14 t
    rw [hp0' t] at *
    linarith
  refine ⟨he, ?_⟩
  have := (hs.const_mul (1 - υ)).sub_const pstar
  simp only [mul_zero, zero_sub] at this
  exact this.congr fun t => (he t).symm

/-- Galí (2015), fn. 15 (PEG): `e ≡ 0` is trivially stationary. -/
theorem peg_meanReverting {e : ℕ → ℝ} (hpeg : ∀ t, e t = 0) : Tendsto e atTop (𝓝 0) := by
  have : e = fun _ => 0 := funext hpeg
  rw [this]
  exact tendsto_const_nhds

/-- Galí (2015), §8.5, technology shocks with `σ = η = 1`, `y* = z = 0`: the natural rate
(38) is `rⁿ_t = ρ − (1 − ρ_a)a_t` (`σ_υΓ_a = 1`) and natural output is `yⁿ = a`. -/
def natRate (rho ρa : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => rho) - (1 - ρa) • a t

/-- Galí (2015), §8.5: the FDIT response coefficient
`Λ = 1/((1 − βρ_a)(1 − ρ_a + φ_y) + κ(φ_π − ρ_a))`. -/
noncomputable def bigLambda (β κ φπ φy ρa : ℝ) : ℝ :=
  1 / ((1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa))

/-- Galí (2015), §8.5 (FDIT, technology shock, `σ_υ = 1`): with `g = φ_y + 1 − ρ_a`, the
output gap `ỹ = −g(1 − βρ_a)Λ a` and domestic inflation `π_H = −gκΛ a`, together with the rule
`i = ρ + φ_π π_H + φ_y(ỹ + a)` (output `y = ỹ + yⁿ = ỹ + a`), satisfy the NKPC (37) and the DIS
(29) for every expectation system, when `a` is AR(1) with persistence `ρ_a` and the
denominator of `Λ` is nonzero. -/
theorem fdit_solution {β κ φπ φy ρa rho : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hD : (1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa) ≠ 0) :
    OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a)
      (fun t => (-(φy + 1 - ρa) * (1 - β * ρa) * bigLambda β κ φπ φy ρa) • a t)
      (fun t => (-(φy + 1 - ρa) * κ * bigLambda β κ φπ φy ρa) • a t)
      (fun t => (fun _ => rho) + φπ • ((-(φy + 1 - ρa) * κ * bigLambda β κ φπ φy ρa) • a t) +
        φy • ((-(φy + 1 - ρa) * (1 - β * ρa) * bigLambda β κ φπ φy ρa) • a t + a t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [map_smul, ha.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold bigLambda
    field_simp
    ring
  · have hLD : bigLambda β κ φπ φy ρa * ((1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa)) = 1 := by
      unfold bigLambda
      field_simp
    simp only [map_smul, ha.2 t, natRate]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inv_one, one_mul]
    linear_combination (-(a t ω) * (φy + 1 - ρa)) * hLD

/-- Galí (2015), §8.5 (FDIT determinacy, eq. (41) with `σ_υ = 1`): any two equilibria under the
rule `i = ρ + φ_π π_H + φ_y(ỹ + a)` with bounded adapted output gap and domestic inflation
coincide, when `κ(φ_π − 1) + (1 − β)φ_y > 0` (at the FDIT values `φ_π = 1.5`, `φ_y = 0.125`,
for any `κ > 0`, `0 < β < 1`). -/
theorem fdit_unique {β κ φπ φy rho ρa : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {a y₁ y₂ π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ}
    (he₁ : OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a) y₁ π₁ i₁)
    (he₂ : OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a) y₂ π₂ i₂)
    (hr₁ : ∀ t, i₁ t = (fun _ => rho) + φπ • π₁ t + φy • (y₁ t + a t))
    (hr₂ : ∀ t, i₂ t = (fun _ => rho) + φπ • π₂ t + φy • (y₂ t + a t))
    (ha₁ : 𝔼.Adapted y₁) (ha₂ : 𝔼.Adapted y₂) (hb₁ : 𝔼.Adapted π₁) (hb₂ : 𝔼.Adapted π₂)
    (hB₁ : BoundedProc y₁) (hB₂ : BoundedProc y₂) (hC₁ : BoundedProc π₁)
    (hC₂ : BoundedProc π₂) : y₁ = y₂ ∧ π₁ = π₂ := by
  have heq : OptimalPolicy.Equilibrium 𝔼 β 1 κ 0 (y₁ - y₂) (π₁ - π₂) (i₁ - i₂) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [Pi.sub_apply, he₁.1 t, he₂.1 t]
      simp only [Pi.sub_apply, map_sub, smul_sub]
      abel
    · rw [Pi.sub_apply, he₁.2 t, he₂.2 t]
      simp only [Pi.sub_apply, Pi.zero_apply, map_sub, smul_sub, sub_zero]
      abel
  have hr : OptimalPolicy.TaylorRule φπ φy (i₁ - i₂) 0 (π₁ - π₂) (y₁ - y₂) := by
    intro t
    simp only [Pi.sub_apply, Pi.zero_apply, hr₁ t, hr₂ t, smul_sub, smul_add]
    abel
  have hbd : ∀ {x z : ℕ → Ω → ℝ}, BoundedProc x → BoundedProc z → BoundedProc (x - z) := by
    intro x z ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun t ω => ?_⟩
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))
  have had : ∀ {x z : ℕ → Ω → ℝ}, 𝔼.Adapted x → 𝔼.Adapted z → 𝔼.Adapted (x - z) := by
    intro x z hx hz t
    simp only [Pi.sub_apply, map_sub, hx t, hz t]
  obtain ⟨h1, h2, -⟩ := (OptimalPolicy.equilibrium_iff_zero 𝔼 one_pos hκ hβ0 hβ1 hφπ hφy h41
    (had ha₁ ha₂) (had hb₁ hb₂) (hbd hB₁ hB₂) (hbd hC₁ hC₂)).1 ⟨heq, hr⟩
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- Galí (2015), §8.5 at the FDIT coefficients: `g = φ_y + 1 − ρ_a > 0`, `Λ > 0`, hence the
inflation coefficient `B = −gκΛ` is **nonzero** (negative), for `κ > 0`, `0 ≤ β < 1`,
`ρ_a < 1`. -/
theorem fdit_coeff_neg {β κ ρa : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρa < 1) :
    -(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa < 0 := by
  have hb : 0 < 1 - β * ρa := by nlinarith
  have hL : 0 < bigLambda β κ (3 / 2) (1 / 8) ρa := by
    unfold bigLambda
    have : 0 < (1 - β * ρa) * (1 - ρa + 1 / 8) + κ * (3 / 2 - ρa) :=
      add_pos (mul_pos hb (by linarith)) (mul_pos hκ (by linarith))
    positivity
  have : 0 < (1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa :=
    mul_pos (mul_pos (by linarith) hκ) hL
  linarith

/-- Galí (2015), fn. 15 (**the unit root under FDIT**, perfect foresight): after a one-time
technology shock `a_t = ρ_aᵗ a₀` (`0 ≤ ρ_a < 1`), with `π_{H,t} = B a_t`, `ỹ_t = A a_t`,
`s_t = y_t = ỹ_t + a_t` (eq. (27), `σ_υ = 1`), `p_{H,t} = ∑_{k ≤ t} π_{H,k}` (`p_{H,−1} = 0`) and
`p* = 0`, the level `e_t = s_t + p_{H,t}` converges to `B a₀/(1 − ρ_a)` — a permanent shift
(nonzero when `B a₀ ≠ 0`, `fdit_coeff_neg`) — while the depreciation `Δe_t → 0`. -/
theorem fdit_unit_root {A B ρa a0 : ℝ} (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) {e pH : ℕ → ℝ}
    (hpH : ∀ t, pH t = ∑ k ∈ Finset.range (t + 1), B * (ρa ^ k * a0))
    (he : ∀ t, e t = (A * (ρa ^ t * a0) + ρa ^ t * a0) + pH t) :
    Tendsto e atTop (𝓝 (B * a0 / (1 - ρa))) ∧
      Tendsto (fun t => e (t + 1) - e t) atTop (𝓝 0) ∧
      (B * a0 ≠ 0 → B * a0 / (1 - ρa) ≠ 0) := by
  have hg : Tendsto (fun t : ℕ => ρa ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, ρa ^ k) atTop (𝓝 (1 - ρa)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat
  have hp : Tendsto pH atTop (𝓝 (B * a0 / (1 - ρa))) := by
    have h1 := ((hsum.comp (tendsto_add_atTop_nat 1)).const_mul (B * a0))
    refine h1.congr' (Eventually.of_forall fun t => ?_) |>.trans ?_
    · simp only [Function.comp_apply]
      rw [hpH t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [div_eq_mul_inv]
  have hs : Tendsto (fun t => A * (ρa ^ t * a0) + ρa ^ t * a0) atTop (𝓝 0) := by
    have := ((hg.mul_const a0).const_mul A).add (hg.mul_const a0)
    simpa using this
  have hE : Tendsto e atTop (𝓝 (B * a0 / (1 - ρa))) := by
    have := hs.add hp
    rw [zero_add] at this
    exact this.congr fun t => (he t).symm
  refine ⟨hE, ?_, fun h => div_ne_zero h (by linarith)⟩
  have := (hE.comp (tendsto_add_atTop_nat 1)).sub hE
  rw [sub_self] at this
  exact this

/-- Galí (2015), fn. 15 (**FDIT: the level of `e` shifts permanently**): at the FDIT
coefficients, with the equilibrium responses of `fdit_solution` (`B = −gκΛ`,
`A = −g(1 − βρ_a)Λ`, unique by `fdit_unique`), a one-time technology shock `a₀ ≠ 0` moves the
nominal exchange rate permanently: `e_t → B a₀/(1 − ρ_a) ≠ 0`, while `Δe_t → 0`. -/
theorem fdit_permanent_shift {β κ ρa a0 : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (ha0 : a0 ≠ 0) {e pH : ℕ → ℝ}
    (hpH : ∀ t, pH t = ∑ k ∈ Finset.range (t + 1),
      (-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * (ρa ^ k * a0))
    (he : ∀ t, e t = ((-(1 / 8 + 1 - ρa) * (1 - β * ρa) * bigLambda β κ (3 / 2) (1 / 8) ρa) *
      (ρa ^ t * a0) + ρa ^ t * a0) + pH t) :
    Tendsto e atTop (𝓝 ((-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * a0 /
        (1 - ρa))) ∧
      (-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * a0 / (1 - ρa) ≠ 0 ∧
      Tendsto (fun t => e (t + 1) - e t) atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := fdit_unit_root hρ0 hρ1 hpH he
  exact ⟨h1, h3 (mul_ne_zero (fdit_coeff_neg hκ hβ0 hβ1 hρ1).ne ha0), h2⟩

/-- Galí (2015), fn. 15 (FCIT accounting, perfect foresight): if UIP holds as
`i_t = i* + e_{t+1} − e_t` with constant `i* = ρ` and the FCIT rule
`i_t = ρ + φ_π π_t + φ_y y_t` with `π_t = p_t − p_{t−1}`, then for every `T`,
`e_{T+1} − e_0 = φ_π (p_T − p_{−1}) + φ_y ∑_{t ≤ T} y_t`: the exchange rate inherits the
cumulated CPI drift, which an inflation (not price-level) target does not undo. -/
theorem fcit_cumulative {rho φπ φy : ℝ} {i e p y : ℕ → ℝ} {pinit : ℝ}
    (huip : ∀ t, i t = rho + (e (t + 1) - e t))
    (hrule0 : i 0 = rho + φπ * (p 0 - pinit) + φy * y 0)
    (hrule : ∀ t, i (t + 1) = rho + φπ * (p (t + 1) - p t) + φy * y (t + 1)) (T : ℕ) :
    e (T + 1) - e 0 = φπ * (p T - pinit) + φy * ∑ t ∈ Finset.range (T + 1), y t := by
  induction T with
  | zero =>
    have h := huip 0
    rw [hrule0] at h
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    linarith
  | succ n ih =>
    have h := huip (n + 1)
    rw [hrule n] at h
    rw [Finset.sum_range_succ]
    linarith

end Gali.OpenEconomy.SimpleRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 8.1: a small open economy under financial autarky

Galí (2015), Chapter 8, Exercise 8.1, pp. 258–259. No international trade in assets (trade is
balanced, `p_t + c_t = p_{H,t} + y_t`), a constant world price level (`p*_t = 0`), the CPI
`p_t = (1 − υ) p_{H,t} + υ e_t`, the terms of trade `s_t = e_t − p_{H,t}` with
`s_t = y_t − y*_t` (unit elasticity of substitution), technology `y_t = a_t + n_t`, perfect
competition with flexible prices and wages, labour supply `w_t − p_t = σ c_t + φ n_t`, and money
demand `m_t − p_t = c_t`.

## Microfoundations (necessity and sufficiency)

* `firm_optimum_iff`: under perfect competition and `Y = A N`, hours `N > 0` maximise profits
  iff `W = P_H A`; in logs `w_t − p_{H,t} = a_t` (`firm_log_iff`); profits are then zero.
* `household_optimum_iff`: the household's static problem along its budget line
  `P C = W N + X` is solved at `C, N > 0` iff `W/P = C^σ N^φ` (concavity for sufficiency, the
  first-order condition for necessity; restated from the Chapter 2 project, without the
  preference shifter); `labour_supply_log_iff` gives `w − p = σ c + φ n` exactly.
* `budget_tradeBalance`, `tradeBalance_log_iff`: with no assets, the budget
  `P C = W N + Π` and the firm's profits `Π = P_H Y − W N` give balanced trade `P C = P_H Y`,
  i.e. `p + c = p_H + y` exactly.
* `tot_of_marketClearing`, `tot_log_iff`: with unit-elastic (Cobb–Douglas) demand, goods-market
  clearing `P_H Y = (1 − υ) P C + υ ℰ P* Y*` and balanced trade give `Y = S Y*`, i.e.
  `s = y − y*` (for `υ > 0`); the Cobb–Douglas CPI is exactly log-linear
  (`Identities.log_cpiCD_eq`).

## Part (a)

* `StaticEq`: the exercise's eight log equations at one date and state.
* `staticEq_iff`: they hold iff `y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`,
  `c = (1 − υ) y + υ y*`, `n = y − a`, `s = y − y*`, `e = m − y*`, `p_H = m − y`,
  `p = m − c`, `w = m − y + a`; `staticEq_existsUnique`, `equilibrium_iff` (processes).
* `denom_pos`: `υ + σ (1 − υ) + φ > 0` for `σ > 0`, `υ ∈ [0, 1]`, `φ ≥ 0`.
* `outputSol_sigma_one`: with `σ = 1`, `y = a` regardless of `y*`; `outputSol_indep_iff`: output
  is independent of world output iff `υ = 0` or `σ = 1`.
* `money_neutral_real`, `exchangeRate_one_for_one`: money is neutral for `y, c, n, s`; the
  nominal exchange rate `e = m − y*` moves one-for-one with money and does not depend on
  technology.

## Part (b)

* `peg_iff`, `peg_existsUnique`, `pegEquilibrium_iff`: under a fixed exchange rate `e_t = ē_t`
  the money supply is endogenous and uniquely equal to `m_t = ē_t + y*_t`; the real allocation
  is the same as in (a) (`peg_same_real_allocation`), and `p_H = ē + y* − y`.

## Part (c)

Part (c) asks for a verbal discussion (imperfect competition, sticky prices); it has no formal
content and is not formalised.
-/

namespace Gali.OpenEconomy.Ex8_1

open Filter Topology

/-! ### The competitive firm -/

/-- Galí (2015), Ex. 8.1, p. 259: profits of a competitive firm with technology `Y = A N`,
`P_H A N − W N`. -/
def profit (PH W A N : ℝ) : ℝ := PH * (A * N) - W * N

/-- Galí (2015), Ex. 8.1, p. 259 (perfect competition, **necessity and sufficiency**): hours
`N > 0` maximise profits over all `N' ≥ 0` iff the wage equals the value of the marginal
product, `W = P_H A`. -/
theorem firm_optimum_iff {PH W A N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → profit PH W A N' ≤ profit PH W A N) ↔ W = PH * A := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h (N + 1) (by linarith)
      unfold profit at this
      nlinarith
    · have := h (N / 2) (by linarith)
      unfold profit at this
      nlinarith
  · intro h N' _
    unfold profit
    rw [h]
    ring_nf
    rfl

/-- Galí (2015), Ex. 8.1, p. 259: at the competitive wage `W = P_H A` profits are zero. -/
theorem profit_zero {PH W A N : ℝ} (h : W = PH * A) : profit PH W A N = 0 := by
  unfold profit; rw [h]; ring

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): for positive levels, `W = P_H A` iff
`w − p_H = a` in logs. -/
theorem firm_log_iff {PH W A : ℝ} (hPH : 0 < PH) (hW : 0 < W) (hA : 0 < A) :
    W = PH * A ↔ Real.log W - Real.log PH = Real.log A := by
  rw [← Real.log_injOn_pos.eq_iff hW (mul_pos hPH hA), Real.log_mul hPH.ne' hA.ne']
  constructor <;> intro h <;> linarith

/-! ### The household's static problem (restated from the Chapter 2 project) -/

/-- Galí (2015), p. 20 (used in Ex. 8.1): disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 20 (used in Ex. 8.1): period utility `u(C) − N^{1+φ}/(1+φ)`, with `u` the
CRRA utility of consumption `RiskSharing.periodUtility`. -/
noncomputable def periodUtility (σ φ C N : ℝ) : ℝ :=
  RiskSharing.periodUtility σ C - disutilN φ N

/-- Galí (2015), eq. (7), p. 21: marginal disutility of labour `N^φ` (restated from the
Chapter 2 project). -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  have : (1 : ℝ) + φ ≠ 0 := by linarith
  field_simp

/-- Galí (2015), p. 18: a differentiable function on `(0, ∞)` with nonincreasing derivative
lies below its tangent lines (restated from the Chapter 2 project). -/
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

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`:
`v(x) + x^φ (y − x) ≤ v(y)` (restated from the Chapter 2 project). -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), eq. (7), p. 21, used in Ex. 8.1 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` with `C > 0`, then `W/P = N^φ C^σ`. -/
theorem static_foc_necessary {σ φ P W X C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N') N) :
    W / P = N ^ φ * C ^ σ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hu : HasDerivAt (RiskSharing.periodUtility σ) (((W * N + X) / P) ^ (-σ))
      ((W * N + X) / P) :=
    RiskSharing.hasDerivAt_periodUtility σ (by rw [hCeq]; exact hC)
  have hg : HasDerivAt (fun N' => periodUtility σ φ ((W * N' + X) / P) N')
      (C ^ (-σ) * (W / P) - N ^ φ) N := by
    have := HasDerivAt.sub (hu.comp N hin) (hasDerivAt_disutilN hφ N)
    rw [hCeq] at this
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hg
  have h1 : C ^ (-σ) * (W / P) = N ^ φ := by linarith
  have hCs : C ^ σ * C ^ (-σ) = 1 := by
    rw [Real.rpow_neg hC.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hC σ).ne'
  calc W / P = (C ^ σ * C ^ (-σ)) * (W / P) := by rw [hCs, one_mul]
    _ = N ^ φ * C ^ σ := by rw [mul_assoc, h1, mul_comm]

/-- Galí (2015), p. 19, used in Ex. 8.1: a global optimum of the static problem over feasible
plans (`N' ≥ 0`, `C' = (W N' + X)/P > 0`) with `N, C > 0` is a local optimum along the budget
line (restated from the Chapter 2 project). -/
theorem static_isLocalMax_of_optimal {σ φ P W X C N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N) :
    IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N') N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2'.le h1'

/-- Galí (2015), eq. (7), p. 21, used in Ex. 8.1 (**sufficiency**, by concavity): if
`W/P = N^φ C^σ` at `(C, N)` with `C, N > 0` on the budget line, then `(C, N)` maximises utility
among all feasible plans. -/
theorem static_foc_sufficient {σ φ P W X C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X)
    (hfoc : W / P = N ^ φ * C ^ σ) {N' : ℝ} (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N := by
  have hu := RiskSharing.periodUtility_tangent hσ hC' hC
  have hv := disutilN_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have hkey : C ^ (-σ) * (W / P) = N ^ φ := by
    rw [hfoc, Real.rpow_neg hC.le]
    field_simp [(Real.rpow_pos_of_pos hC σ).ne']
  unfold periodUtility
  rw [hdiff] at hu
  nlinarith

/-- Galí (2015), Ex. 8.1, p. 259 (labour supply, **necessity and sufficiency**): for `σ > 0`,
`φ ≥ 0`, a point with `C, N > 0` on the budget line `P C = W N + X` solves the household's
static problem iff `W/P = N^φ C^σ`. -/
theorem household_optimum_iff {σ φ P W X C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hC hbud (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hN hC hbud h hN' hC'⟩

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): for positive levels `W/P = N^φ C^σ` iff
`w − p = σ c + φ n` (restated from the Chapter 2 project). -/
theorem labour_supply_log_iff {σ φ W P C N : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C)
    (hN : 0 < N) :
    W / P = N ^ φ * C ^ σ ↔
      Real.log W - Real.log P = σ * Real.log C + φ * Real.log N := by
  have h1 : (0 : ℝ) < W / P := div_pos hW hP
  have h2 : (0 : ℝ) < N ^ φ * C ^ σ :=
    mul_pos (Real.rpow_pos_of_pos hN φ) (Real.rpow_pos_of_pos hC σ)
  rw [← Real.log_injOn_pos.eq_iff h1 h2, Real.log_div hW.ne' hP.ne',
    Real.log_mul (Real.rpow_pos_of_pos hN φ).ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hN, Real.log_rpow hC]
  constructor <;> intro h <;> linarith

/-! ### Balanced trade, the terms of trade and the CPI -/

/-- Galí (2015), Ex. 8.1, p. 258: with no assets the household spends its wage bill plus the
profits of the domestic firm, `P C = W N + Π` with `Π = P_H Y − W N`; with `Y = A N` this is
balanced trade, `P C = P_H Y`. -/
theorem budget_tradeBalance {P C W N PH A Y : ℝ} (hY : Y = A * N)
    (hbud : P * C = W * N + profit PH W A N) : P * C = PH * Y := by
  rw [hbud, hY]; unfold profit; ring

/-- Galí (2015), Ex. 8.1, p. 258 (**exact**): balanced trade `P C = P_H Y` iff
`p + c = p_H + y` in logs. -/
theorem tradeBalance_log_iff {P C PH Y : ℝ} (hP : 0 < P) (hC : 0 < C) (hPH : 0 < PH)
    (hY : 0 < Y) :
    P * C = PH * Y ↔ Real.log P + Real.log C = Real.log PH + Real.log Y := by
  rw [← Real.log_injOn_pos.eq_iff (mul_pos hP hC) (mul_pos hPH hY), Real.log_mul hP.ne' hC.ne',
    Real.log_mul hPH.ne' hY.ne']

/-- Galí (2015), Ex. 8.1, p. 259 (unit elasticity): with Cobb–Douglas demand, home spending on
home goods is `(1 − υ) P C` and exports are worth `υ ℰ P* Y*`; goods-market clearing
`P_H Y = (1 − υ) P C + υ ℰ P* Y*` and balanced trade `P C = P_H Y` give `P_H Y = ℰ P* Y*`
(`υ > 0`), i.e. `Y = S Y*` with `S = ℰ P*/P_H`. -/
theorem tot_of_marketClearing {υ P C PH Y Ecal Pstar Ystar : ℝ} (hυ : 0 < υ)
    (hmc : PH * Y = (1 - υ) * (P * C) + υ * (Ecal * Pstar * Ystar)) (htb : P * C = PH * Y) :
    PH * Y = Ecal * Pstar * Ystar := by
  rw [htb] at hmc
  have : υ * (PH * Y) = υ * (Ecal * Pstar * Ystar) := by linarith
  exact mul_left_cancel₀ hυ.ne' this

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): `P_H Y = ℰ P* Y*` iff
`s = e + p* − p_H = y − y*` in logs. -/
theorem tot_log_iff {PH Y Ecal Pstar Ystar : ℝ} (hPH : 0 < PH) (hY : 0 < Y) (hE : 0 < Ecal)
    (hPs : 0 < Pstar) (hYs : 0 < Ystar) :
    PH * Y = Ecal * Pstar * Ystar ↔
      Real.log Ecal + Real.log Pstar - Real.log PH = Real.log Y - Real.log Ystar := by
  rw [← Real.log_injOn_pos.eq_iff (mul_pos hPH hY) (mul_pos (mul_pos hE hPs) hYs),
    Real.log_mul hPH.ne' hY.ne',
    Real.log_mul (mul_pos hE hPs).ne' hYs.ne', Real.log_mul hE.ne' hPs.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), Ex. 8.1, p. 259 (**microfoundations of the supply block**): for positive
levels with the no-asset budget `P C = W N + Π`, the firm's optimum and the household's
optimum hold iff, in logs, `w − p_H = a` and `w − p = σ c + φ n` (balanced trade
`p + c = p_H + y` is `tradeBalance_log`). -/
theorem micro_iff {σ φ P C W N PH A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hC : 0 < C) (hW : 0 < W) (hN : 0 < N) (hPH : 0 < PH) (hA : 0 < A)
    (hbud : P * C = W * N + profit PH W A N) :
    ((∀ N', 0 ≤ N' → profit PH W A N' ≤ profit PH W A N) ∧
      (∀ N', 0 ≤ N' → 0 < (W * N' + profit PH W A N) / P →
        periodUtility σ φ ((W * N' + profit PH W A N) / P) N' ≤ periodUtility σ φ C N)) ↔
      (Real.log W - Real.log PH = Real.log A ∧
        Real.log W - Real.log P = σ * Real.log C + φ * Real.log N) := by
  rw [firm_optimum_iff hN, household_optimum_iff hσ hφ hP hN hC hbud,
    firm_log_iff hPH hW hA, labour_supply_log_iff hW hP hC hN]

/-- Galí (2015), Ex. 8.1, p. 258: balanced trade in logs, `p + c = p_H + y`, for positive
levels satisfying the no-asset budget with `Y = A N`. -/
theorem tradeBalance_log {P C W N PH A Y : ℝ} (hP : 0 < P) (hC : 0 < C) (hPH : 0 < PH)
    (hY0 : 0 < Y) (hY : Y = A * N) (hbud : P * C = W * N + profit PH W A N) :
    Real.log P + Real.log C = Real.log PH + Real.log Y :=
  (tradeBalance_log_iff hP hC hPH hY0).1 (budget_tradeBalance hY hbud)

/-! ### Part (a): the log-linear equilibrium -/

/-- Galí (2015), Ex. 8.1, pp. 258–259: the equilibrium conditions at one date (and state):
balanced trade, the CPI (`p* = 0`), the terms of trade (definition and `s = y − y*`),
technology, labour supply, the competitive firm `w − p_H = a`, and money demand. -/
def StaticEq (υ σ φ a ys m y c n w p pH e s : ℝ) : Prop :=
  p + c = pH + y ∧ p = (1 - υ) * pH + υ * e ∧ s = e - pH ∧ s = y - ys ∧ y = a + n ∧
    w - p = σ * c + φ * n ∧ w - pH = a ∧ m - p = c

/-- Galí (2015), Ex. 8.1(a): the denominator `υ + σ (1 − υ) + φ`. -/
def denom (υ σ φ : ℝ) : ℝ := υ + σ * (1 - υ) + φ

/-- Galí (2015), Ex. 8.1(a): equilibrium output
`y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`. -/
noncomputable def outputSol (υ σ φ a ys : ℝ) : ℝ :=
  ((1 + φ) * a + υ * (1 - σ) * ys) / denom υ σ φ

/-- Galí (2015), Ex. 8.1(a): `υ + σ (1 − υ) + φ > 0` for `σ > 0`, `0 ≤ υ ≤ 1`, `φ ≥ 0`. -/
theorem denom_pos {υ σ φ : ℝ} (hσ : 0 < σ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) :
    0 < denom υ σ φ := by
  unfold denom
  rcases hυ0.lt_or_eq with h | h
  · nlinarith
  · subst h; linarith

/-- Galí (2015), Ex. 8.1(a): in every equilibrium consumption is
`c = (1 − υ) y + υ y*` (from balanced trade, the CPI and the terms of trade). -/
theorem consumption_eq {υ σ φ a ys m y c n w p pH e s : ℝ}
    (h : StaticEq υ σ φ a ys m y c n w p pH e s) : c = (1 - υ) * y + υ * ys := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := h
  linear_combination h1 - h2 + υ * h3 - υ * h4

/-- **Ex. 8.1(a)** (Galí 2015, p. 259): with `υ + σ (1 − υ) + φ ≠ 0`, the equilibrium
conditions hold iff `y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`,
`c = (1 − υ) y + υ y*`, `n = y − a`, `s = y − y*`, `e = m − y*`, `p_H = m − y`, `p = m − c`
and `w = m − y + a`. -/
theorem staticEq_iff {υ σ φ a ys m y c n w p pH e s : ℝ} (hD : denom υ σ φ ≠ 0) :
    StaticEq υ σ φ a ys m y c n w p pH e s ↔
      y = outputSol υ σ φ a ys ∧ c = (1 - υ) * y + υ * ys ∧ n = y - a ∧ s = y - ys ∧
        e = m - ys ∧ pH = m - y ∧ p = m - c ∧ w = m - y + a := by
  constructor
  · intro h
    have hc := consumption_eq h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    have hy : denom υ σ φ * y = (1 + φ) * a + υ * (1 - σ) * ys := by
      unfold denom
      linear_combination h7 - h6 - h2 + υ * h3 - υ * h4 - σ * hc + φ * h5
    refine ⟨?_, hc, by linarith, h4, ?_, ?_, by linarith, ?_⟩
    · unfold outputSol
      rw [eq_div_iff hD]; linear_combination hy
    · linear_combination (1 - υ) * h4 - hc - h2 + (υ - 1) * h3 - h8
    · linear_combination -υ * h4 - hc - h2 + υ * h3 - h8
    · linear_combination -υ * h4 - hc - h2 + υ * h3 - h8 + h7
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    have hyD : denom υ σ φ * y = (1 + φ) * a + υ * (1 - σ) * ys := by
      rw [hy]; unfold outputSol; field_simp
    unfold denom at hyD
    refine ⟨by linarith, ?_, by linarith, hs, by linarith, ?_, by linarith, by linarith⟩
    · rw [hp, hpH, he, hc]; ring
    · rw [hw, hp, hc, hn]
      linear_combination -hyD

/-- Galí (2015), Ex. 8.1(a): for every technology level, world output and money supply there is
exactly one equilibrium `(y, c, n, w, p, p_H, e, s)`. -/
theorem staticEq_existsUnique {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a ys m : ℝ) :
    ∃ y c n w p pH e s, StaticEq υ σ φ a ys m y c n w p pH e s ∧
      ∀ y' c' n' w' p' pH' e' s', StaticEq υ σ φ a ys m y' c' n' w' p' pH' e' s' →
        y' = y ∧ c' = c ∧ n' = n ∧ w' = w ∧ p' = p ∧ pH' = pH ∧ e' = e ∧ s' = s := by
  set y := outputSol υ σ φ a ys
  set c := (1 - υ) * y + υ * ys
  refine ⟨y, c, y - a, m - y + a, m - c, m - y, m - ys, y - ys,
    (staticEq_iff hD).2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro y' c' n' w' p' pH' e' s' h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (staticEq_iff hD).1 h
  subst h1
  refine ⟨rfl, h2, h3, h8, ?_, h6, h5, h4⟩
  rw [h7, h2]

/-- Galí (2015), Ex. 8.1(a), p. 259: with `σ = 1` output is `y = a`, independent of world
output (and of `υ`, `φ`, provided `φ ≠ −1`). -/
theorem outputSol_sigma_one {υ φ : ℝ} (hφ : 1 + φ ≠ 0) (a ys : ℝ) :
    outputSol υ 1 φ a ys = a := by
  unfold outputSol denom
  rw [show υ + 1 * (1 - υ) + φ = 1 + φ by ring, show (1 : ℝ) - 1 = 0 by ring]
  field_simp
  ring

/-- Galí (2015), Ex. 8.1(a), p. 259: equilibrium output is independent of world output iff
`υ = 0` (a closed economy) or `σ = 1` (log utility). -/
theorem outputSol_indep_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a : ℝ) :
    (∀ ys ys', outputSol υ σ φ a ys = outputSol υ σ φ a ys') ↔ υ = 0 ∨ σ = 1 := by
  constructor
  · intro h
    have h01 := h 0 1
    unfold outputSol at h01
    rw [div_left_inj' hD] at h01
    have : υ * (1 - σ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h) ys ys' <;> unfold outputSol <;> rw [h] <;> ring

/-- Galí (2015), Ex. 8.1(a): the response of output to world output,
`∂y/∂y* = υ (1 − σ)/(υ + σ (1 − υ) + φ)`, negative for `σ > 1` and positive for `σ < 1`
(with `υ > 0` and a positive denominator). -/
theorem outputSol_ystar_slope {υ σ φ : ℝ} (a ys : ℝ) :
    outputSol υ σ φ a ys = outputSol υ σ φ a 0 + υ * (1 - σ) / denom υ σ φ * ys := by
  unfold outputSol; ring

/-- Galí (2015), Ex. 8.1(a): the response of output to technology is
`(1 + φ)/(υ + σ (1 − υ) + φ) > 0`. -/
theorem outputSol_a_slope_pos {υ σ φ : ℝ} (hσ : 0 < σ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) : 0 < (1 + φ) / denom υ σ φ ∧
      ∀ a ys, outputSol υ σ φ a ys = (1 + φ) / denom υ σ φ * a + outputSol υ σ φ 0 ys := by
  refine ⟨div_pos (by linarith) (denom_pos hσ hυ0 hυ1 hφ), fun a ys => ?_⟩
  unfold outputSol; ring

/-- Galí (2015), Ex. 8.1(a): money is neutral for the real allocation: two equilibria with the
same technology and world output but different money supplies have the same output,
consumption, employment and terms of trade. -/
theorem money_neutral_real {υ σ φ a ys m m' y c n w p pH e s y' c' n' w' p' pH' e' s' : ℝ}
    (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH e s)
    (h' : StaticEq υ σ φ a ys m' y' c' n' w' p' pH' e' s') :
    y' = y ∧ c' = c ∧ n' = n ∧ s' = s := by
  obtain ⟨hy, hc, hn, hs, -⟩ := (staticEq_iff hD).1 h
  obtain ⟨hy', hc', hn', hs', -⟩ := (staticEq_iff hD).1 h'
  have e1 : y' = y := hy'.trans hy.symm
  refine ⟨e1, by rw [hc, hc', e1], by rw [hn, hn', e1], by rw [hs, hs', e1]⟩

/-- Galí (2015), Ex. 8.1(a): the nominal exchange rate `e = m − y*` moves one-for-one with the
money supply and does not depend on technology: `e − e' = m − m'` across equilibria with the
same world output. -/
theorem exchangeRate_one_for_one {υ σ φ a a' ys m m' y c n w p pH e s y' c' n' w' p' pH' e'
    s' : ℝ} (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH e s)
    (h' : StaticEq υ σ φ a' ys m' y' c' n' w' p' pH' e' s') : e - e' = m - m' := by
  have he := ((staticEq_iff hD).1 h).2.2.2.2.1
  have he' := ((staticEq_iff hD).1 h').2.2.2.2.1
  rw [he, he']; ring

/-! ### Part (a) for processes -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 8.1, pp. 258–259: an equilibrium of the financially autarkic economy:
`StaticEq` holds at every date and state. Prices are flexible and there are no assets, so the
model is static date by date. -/
def Equilibrium (υ σ φ : ℝ) (a ys m y c n w p pH e s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, StaticEq υ σ φ (a t ω) (ys t ω) (m t ω) (y t ω) (c t ω) (n t ω) (w t ω) (p t ω)
    (pH t ω) (e t ω) (s t ω)

/-- **Ex. 8.1(a)** (Galí 2015, p. 259), processes: with an exogenous money supply the
equilibrium processes are uniquely `y_t = [(1 + φ) a_t + υ (1 − σ) y*_t]/(υ + σ (1 − υ) + φ)`,
`c_t = (1 − υ) y_t + υ y*_t`, `n_t = y_t − a_t`, `s_t = y_t − y*_t`, `e_t = m_t − y*_t`,
`p_{H,t} = m_t − y_t`, `p_t = m_t − c_t`, `w_t = m_t − y_t + a_t`. -/
theorem equilibrium_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) {a ys m y c n w p pH e s :
    ℕ → Ω → ℝ} :
    Equilibrium υ σ φ a ys m y c n w p pH e s ↔
      y = (fun t ω => outputSol υ σ φ (a t ω) (ys t ω)) ∧
        c = (fun t => (1 - υ) • y t + υ • ys t) ∧ n = (fun t => y t - a t) ∧
        s = (fun t => y t - ys t) ∧ e = (fun t => m t - ys t) ∧ pH = (fun t => m t - y t) ∧
        p = (fun t => m t - c t) ∧ w = (fun t => m t - y t + a t) := by
  constructor
  · intro h
    have k := fun t ω => (staticEq_iff hD).1 (h t ω)
    refine ⟨funext fun t => funext fun ω => (k t ω).1, funext fun t => funext fun ω => ?_,
      funext fun t => funext fun ω => (k t ω).2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.2.2⟩
    simpa using (k t ω).2.1
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩ t ω
    subst hy hc hn hs he hpH hp hw
    exact (staticEq_iff hD).2 ⟨rfl, by simp, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Part (b): a fixed exchange rate -/

/-- **Ex. 8.1(b)** (Galí 2015, p. 259): under a fixed exchange rate `e = ē` the money supply is
endogenous: the equilibrium conditions with `e = ē` hold iff the money supply is
`m = ē + y*` and the rest of the allocation is as in (a), with `p_H = ē + y* − y`. -/
theorem peg_iff {υ σ φ a ys ebar m y c n w p pH s : ℝ} (hD : denom υ σ φ ≠ 0) :
    StaticEq υ σ φ a ys m y c n w p pH ebar s ↔
      m = ebar + ys ∧ y = outputSol υ σ φ a ys ∧ c = (1 - υ) * y + υ * ys ∧ n = y - a ∧
        s = y - ys ∧ pH = ebar + ys - y ∧ p = ebar + ys - c ∧ w = ebar + ys - y + a := by
  rw [staticEq_iff hD]
  constructor
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    exact ⟨by linarith, hy, hc, hn, hs, by linarith, by linarith, by linarith⟩
  · rintro ⟨hm, hy, hc, hn, hs, hpH, hp, hw⟩
    subst hm
    exact ⟨hy, hc, hn, hs, by ring, hpH, hp, hw⟩

/-- **Ex. 8.1(b)** (Galí 2015, p. 259): for every peg `ē` there is exactly one money supply,
`m = ē + y*`, consistent with an equilibrium. -/
theorem peg_existsUnique {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a ys ebar : ℝ) :
    ∃! m, ∃ y c n w p pH s, StaticEq υ σ φ a ys m y c n w p pH ebar s := by
  refine ⟨ebar + ys, ?_, ?_⟩
  · obtain ⟨y, c, n, w, p, pH, e, s, h, -⟩ := staticEq_existsUnique hD a ys (ebar + ys)
    have he : e = ebar := by
      have := ((staticEq_iff hD).1 h).2.2.2.2.1
      linarith
    subst he
    exact ⟨y, c, n, w, p, pH, s, h⟩
  · rintro m ⟨y, c, n, w, p, pH, s, h⟩
    exact ((peg_iff hD).1 h).1

/-- Galí (2015), Ex. 8.1(b): the peg leaves the real allocation of (a) unchanged: an
equilibrium under the peg and one under any exogenous money supply (same technology and world
output) have the same output, consumption, employment and terms of trade. -/
theorem peg_same_real_allocation {υ σ φ a ys ebar m m' y c n w p pH s y' c' n' w' p' pH' e'
    s' : ℝ} (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH ebar s)
    (h' : StaticEq υ σ φ a ys m' y' c' n' w' p' pH' e' s') :
    y' = y ∧ c' = c ∧ n' = n ∧ s' = s :=
  money_neutral_real hD h h'

/-- **Ex. 8.1(b)** (Galí 2015, p. 259), processes: under a fixed exchange-rate regime
`e_t = ē_t` the equilibrium money supply is uniquely `m_t = ē_t + y*_t`; the real allocation is
as in (a) and `p_{H,t} = ē_t + y*_t − y_t`. -/
theorem pegEquilibrium_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) {a ys ebar m y c n w p pH s :
    ℕ → Ω → ℝ} :
    Equilibrium υ σ φ a ys m y c n w p pH ebar s ↔
      m = (fun t => ebar t + ys t) ∧ y = (fun t ω => outputSol υ σ φ (a t ω) (ys t ω)) ∧
        c = (fun t => (1 - υ) • y t + υ • ys t) ∧ n = (fun t => y t - a t) ∧
        s = (fun t => y t - ys t) ∧ pH = (fun t => ebar t + ys t - y t) ∧
        p = (fun t => ebar t + ys t - c t) ∧ w = (fun t => ebar t + ys t - y t + a t) := by
  rw [equilibrium_iff hD]
  constructor
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    subst he
    refine ⟨funext fun t => (sub_add_cancel _ _).symm, hy, hc, hn, hs, ?_, ?_, ?_⟩
    · rw [hpH]; funext t; rw [sub_add_cancel]
    · rw [hp]; funext t; rw [sub_add_cancel]
    · rw [hw]; funext t; rw [sub_add_cancel]
  · rintro ⟨hm, hy, hc, hn, hs, hpH, hp, hw⟩
    subst hm
    refine ⟨hy, hc, hn, hs, ?_, hpH, hp, hw⟩
    funext t
    exact (add_sub_cancel_right _ _).symm

end Gali.OpenEconomy.Ex8_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 8.2: technology shocks in the small open economy

Galí (2015), Chapter 8, Exercise 8.2, pp. 259–260. Domestic inflation and the output gap obey
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t` and
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)`, with `r^n_t = ρ − ψ_{ra} a_t`,
natural output `y^n_t = ψ_{ya} a_t` and technology an AR(1), `E_t a_{t+1} = ρ_a a_t`. With
`y* = p* = 0` (and no preference shocks), eq. (27) gives the terms of trade `s_t = σ_υ y_t`
and eq. (14) the nominal exchange rate `e_t = s_t + p_{H,t}`, where
`π_{H,t} = p_{H,t} − p_{H,t−1}` and `p_{H,−1}` is given. By eq. (38), p. 239,
`ψ_{ra} = σ_υ (1 − ρ_a) ψ_{ya}` (with `ψ_{ya} = Γ_a`); the closed forms are given for general
`ψ_{ra}` and specialised under this relation (`h38`).

## Part (a): the rule `i_t = ρ + φ_π π_{H,t}`

* `nk_iff_structural` (with `TaylorRule.Structural`, `TaylorRule.schurStable_AU_iff`,
  `TaylorRule.msv_unique`, imported from `TaylorRule`): the Ch. 3
  machinery (restated from the Chapter 3 project) with `σ ↦ σ_υ`, `κ ↦ κ_υ`, `φ_y = 0`.
* `taylor_determinate_iff`: the system is determinate iff `φ_π > 1` (Bullard–Mitra).
* `taylor_iff`, `taylor_exists`, `taylor_unique`: under `φ_π > 1` the equilibrium with bounded
  adapted `(ỹ, π_H)` exists and is unique:
  `ỹ_t = −(1 − βρ_a) Λ_a ψ_{ra} a_t`, `π_{H,t} = −κ_υ Λ_a ψ_{ra} a_t`,
  `Λ_a = 1/((1 − βρ_a) σ_υ (1 − ρ_a) + κ_υ (φ_π − ρ_a))`, `y_t = ỹ_t + ψ_{ya} a_t`,
  `s_t = σ_υ y_t`, `p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}`, `e_t = s_t + p_{H,t}`.
* `taylor_closed_forms_38`: under (38), `y_t = κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
  `s_t = σ_υ κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
  `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} [(φ_π − ρ_a) a_t − (1 − ρ_a) ∑_{k ≤ t} a_k]`,
  `i_t = ρ − φ_π σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t`; `taylor_signs_38`: for `ψ_{ya} > 0` a
  positive shock lowers `ỹ` and `π_H` and raises `y` and `s`.
* `taylor_irf_38`: for a one-time shock (`a_t = ρ_aᵗ a_0`),
  `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} (φ_π ρ_aᵗ − 1) a_0`: a nominal depreciation on impact
  (`φ_π > 1`) and a long-run appreciation (`taylor_irf_tendsto`), with the domestic price level
  permanently lower.

## Part (b): the peg `e_t = 0`

The peg gives `σ_υ ỹ_t = −p_{H,t} − σ_υ ψ_{ya} a_t`, and the Phillips curve becomes the
second-order equation `β E_t p_{H,t+1} − (1 + β + κ_υ/σ_υ) p_{H,t} + p_{H,t−1} = κ_υ ψ_{ya} a_t`
with `p_{H,t−1}` predetermined.

* `charQ`, `exists_root`, `root_unique`, `other_root`: `σ_υ β λ² − (σ_υ (1 + β) + κ_υ) λ + σ_υ`
  has exactly one root `λ ∈ (0, 1)`; the other root is `1/(βλ) > 1`.
* `peg_nkpc_iff` (**the factorisation**): with `w_t = p_{H,t} − λ p_{H,t−1}`, the Phillips curve
  holds iff `w_t = βλ E_t w_{t+1} − λ κ_υ ψ_{ya} a_t`, a forward equation with `0 < βλ < 1`.
* `peg_iff`, `peg_exists`, `peg_unique`: the bounded equilibrium exists and is unique:
  `p_{H,t} = λ p_{H,t−1} + θ a_t`, `θ = −λ κ_υ ψ_{ya}/(1 − βλρ_a)`,
  `ỹ_t = −σ_υ⁻¹ p_{H,t} − ψ_{ya} a_t`, `y_t = −σ_υ⁻¹ p_{H,t}`, `s_t = −p_{H,t}`,
  `i_t = ρ + (σ_υ (1 − ρ_a) ψ_{ya} − ψ_{ra}) a_t` (`= ρ = i*` under (38), `peg_rate_38`).
* `pegP_closed`: `p_{H,t} = λ^{t+1} p_{H,−1} + θ ∑_{k ≤ t} λ^{t−k} a_k`; `peg_irf_signs`: after a
  positive shock (`p_{H,−1} = 0`, `ψ_{ya} > 0`) the domestic price level falls and output and
  the terms of trade rise at every date.
-/

namespace Gali.OpenEconomy.Ex8_2

open Filter Topology
open Gali.OpenEconomy.TaylorRule (Structural AU msvDen msvLambda msvPsiY msvPsiPi msvDen_pos
  isAR1_smul boundedProc_smul msv_structural msv_unique schurStable_AU_iff)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Ex. 8.2, p. 259: the lagged domestic price level `p_{H,t−1}`, with
`p_{H,−1}` given. -/
def lagP (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pm1
  | t + 1 => p t

/-- Galí (2015), Ex. 8.2, p. 260: the natural rate `r^n_t = ρ − ψ_{ra} a_t`. -/
def natRate (ρ ψra : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (fun _ => ρ) - ψra • a t

/-- Galí (2015), Ex. 8.2, pp. 259–260, with eqs. (14) and (27), p. 230 and p. 235: the
non-policy block: the Phillips curve, the dynamic IS equation, `y_t = ỹ_t + ψ_{ya} a_t`,
`s_t = σ_υ y_t` (`y* = 0`), `π_{H,t} = p_{H,t} − p_{H,t−1}` and `e_t = s_t + p_{H,t}`
(`p* = 0`). -/
def Block (β σv κv ρ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piH t = β • 𝔼.E t (piH (t + 1)) + κv • ygap t ∧
    ygap t = 𝔼.E t (ygap (t + 1)) - σv⁻¹ • (i t - 𝔼.E t (piH (t + 1)) - natRate ρ ψra a t) ∧
    y t = ygap t + ψya • a t ∧ s t = σv • y t ∧ piH t = pH t - lagP pm1 pH t ∧
    e t = s t + pH t

/-- Galí (2015), Ex. 8.2(a), p. 260: an equilibrium under the rule `i_t = ρ + φ_π π_{H,t}`. -/
def TaylorEq (β σv κv ρ φπ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧ ∀ t, i t = (fun _ => ρ) + φπ • piH t

/-- Galí (2015), Ex. 8.2(b), p. 260: an equilibrium under the exchange-rate peg `e_t = 0`. -/
def PegEq (β σv κv ρ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧ ∀ t, e t = 0

/-- Galí (2015), Ex. 8.2: an initial condition known at date 0 is known at every date. -/
theorem known_pm1 {pm1 : Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (t : ℕ) : 𝔼.E t pm1 = pm1 := by
  have := 𝔼.known (Nat.zero_le t) pm1
  rwa [h] at this

/-- Galí (2015), Ex. 8.2: `π_{H,t} = p_{H,t} − p_{H,t−1}` for all `t` iff
`p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}`. -/
theorem cumsum_iff {pm1 : Ω → ℝ} {piH pH : ℕ → Ω → ℝ} :
    (∀ t, piH t = pH t - lagP pm1 pH t) ↔
      pH = fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k := by
  constructor
  · intro h
    funext t
    induction t with
    | zero =>
      have := h 0
      simp only [lagP] at this
      simp [this]
    | succ t ih =>
      have := h (t + 1)
      simp only [lagP] at this
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, this]
      abel
  · intro h t
    rw [h]
    cases t with
    | zero => simp [lagP]
    | succ t =>
      simp only [lagP]
      rw [Finset.sum_range_succ]
      abel

/-! ### Part (a): the Chapter 3 system

The structural equations, the matrices `A_υ`, `B_υ` (`TaylorRule.Structural`,
`TaylorRule.AU`, `TaylorRule.BU`, `TaylorRule.omegaU`), Bullard–Mitra
(`TaylorRule.schurStable_AU_iff`) and the MSV solution (`TaylorRule.msvDen`,
`TaylorRule.msvLambda`, `TaylorRule.msvPsiY`, `TaylorRule.msvPsiPi`,
`TaylorRule.msv_structural`, `TaylorRule.msv_unique`) are imported from `TaylorRule`; here
`σ ↦ σ_υ`, `κ ↦ κ_υ`, `φ_y = 0`. -/

/-! ### Part (a): the technology shock under `i_t = ρ + φ_π π_{H,t}` -/

/-- Galí (2015), Ex. 8.2(a): the composite shock `u_t = r^n_t − ρ = −ψ_{ra} a_t`. -/
def shock (ψra : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-ψra) • a t

/-- Galí (2015), Ex. 8.2(a): under `i_t = ρ + φ_π π_{H,t}` the Phillips curve and the dynamic
IS equation hold iff the structural equations hold with `φ_y = 0` and `u_t = −ψ_{ra} a_t`. -/
theorem nk_iff_structural {β σv κv ρ φπ ψra : ℝ} (hσ : σv ≠ 0)
    {a ygap piH i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = (fun _ => ρ) + φπ • piH t) :
    (∀ t, piH t = β • 𝔼.E t (piH (t + 1)) + κv • ygap t ∧
      ygap t = 𝔼.E t (ygap (t + 1)) - σv⁻¹ • (i t - 𝔼.E t (piH (t + 1)) - natRate ρ ψra a t))
      ↔ Structural 𝔼 β σv κv φπ 0 (shock ψra a) ygap piH := by
  have hinv : σv * σv⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · intro h t
    refine ⟨?_, (h t).1⟩
    funext ω
    have e := congrFun (h t).2 ω
    have r := congrFun (hrule t) ω
    simp only [shock, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σv * e - r -
      (i t ω - 𝔼.E t (piH (t + 1)) ω - (ρ - ψra * a t ω)) * hinv
  · intro h t
    refine ⟨(h t).2, ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shock, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σv⁻¹ * e + σv⁻¹ * r - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- **Determinacy** (Galí 2015, eq. (41), p. 240, with `φ_y = 0`; Ex. 8.2(a)): the system has at
most one bounded adapted solution for every forcing process iff `φ_π > 1`. -/
theorem taylor_determinate_iff [Nonempty Ω] {β σv κv φπ : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    𝔼.Determinate (AU β σv κv φπ 0) ↔ 1 < φπ := by
  rw [𝔼.determinate_iff, schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ le_rfl]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Ex. 8.2(a)** (Galí 2015, p. 260): under `φ_π > 1`, a tuple with bounded adapted output gap
and domestic inflation is an equilibrium iff `ỹ_t = (1 − βρ_a) Λ_a u_t`, `π_{H,t} = κ_υ Λ_a u_t`
(`u_t = −ψ_{ra} a_t`), `i_t = ρ + φ_π π_{H,t}`, `y_t = ỹ_t + ψ_{ya} a_t`, `s_t = σ_υ y_t`,
`p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}` and `e_t = s_t + p_{H,t}`. -/
theorem taylor_iff {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ} {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) :
    TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e ↔
      ygap = (fun t => msvPsiY β σv κv φπ 0 ρa • shock ψra a t) ∧
        piH = (fun t => msvPsiPi β σv κv φπ 0 ρa • shock ψra a t) ∧
        i = (fun t => (fun _ => ρ) + φπ • piH t) ∧ y = (fun t => ygap t + ψya • a t) ∧
        s = (fun t => σv • y t) ∧
        pH = (fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k) ∧
        e = (fun t => s t + pH t) := by
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hu : 𝔼.IsAR1 ρa (shock ψra a) := isAR1_smul 𝔼 ha (-ψra)
  have hub : BoundedProc (shock ψra a) := boundedProc_smul hab (-ψra)
  constructor
  · rintro ⟨hB, hrule⟩
    have hs := (nk_iff_structural 𝔼 hσ.ne' hrule).1 fun t => ⟨(hB t).1, (hB t).2.1⟩
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl hρ1 h28 hu hub hs
      hyA hpA hyB hpB
    exact ⟨h1, h2, funext hrule, funext fun t => (hB t).2.2.1,
      funext fun t => (hB t).2.2.2.1, cumsum_iff.1 fun t => (hB t).2.2.2.2.1,
      funext fun t => (hB t).2.2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hrule : ∀ t, i t = (fun _ => ρ) + φπ • piH t := fun t => by rw [h3]
    have hD := (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28).ne'
    have hs : Structural 𝔼 β σv κv φπ 0 (shock ψra a) ygap piH := by
      rw [h1, h2]; exact msv_structural 𝔼 hD hu
    have hnk := (nk_iff_structural 𝔼 hσ.ne' hrule).2 hs
    have hcum := cumsum_iff.2 h6
    exact ⟨fun t => ⟨(hnk t).1, (hnk t).2, by rw [h4], by rw [h5], hcum t, by rw [h7]⟩, hrule⟩

/-- **Ex. 8.2(a), existence** (Galí 2015, p. 260): under `φ_π > 1` the MSV tuple is an
equilibrium with bounded adapted output gap and domestic inflation. -/
theorem taylor_exists {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) (pm1 : Ω → ℝ) :
    ∃ ygap piH i y s pH e, TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted piH ∧ BoundedProc ygap ∧ BoundedProc piH := by
  have hu : 𝔼.IsAR1 ρa (shock ψra a) := isAR1_smul 𝔼 ha (-ψra)
  have hub : BoundedProc (shock ψra a) := boundedProc_smul hab (-ψra)
  set ygap : ℕ → Ω → ℝ := fun t => msvPsiY β σv κv φπ 0 ρa • shock ψra a t
  set piH : ℕ → Ω → ℝ := fun t => msvPsiPi β σv κv φπ 0 ρa • shock ψra a t
  set y : ℕ → Ω → ℝ := fun t => ygap t + ψya • a t
  set s : ℕ → Ω → ℝ := fun t => σv • y t
  set pH : ℕ → Ω → ℝ := fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k
  have hyA : 𝔼.Adapted ygap := (isAR1_smul 𝔼 hu _).1
  have hpA : 𝔼.Adapted piH := (isAR1_smul 𝔼 hu _).1
  have hyB : BoundedProc ygap := boundedProc_smul hub _
  have hpB : BoundedProc piH := boundedProc_smul hub _
  refine ⟨ygap, piH, fun t => (fun _ => ρ) + φπ • piH t, y, s, pH, fun t => s t + pH t,
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).2
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hyA, hpA, hyB, hpB⟩

/-- **Ex. 8.2(a), uniqueness** (Galí 2015, p. 260): under `φ_π > 1` two equilibria with bounded
adapted output gap and domestic inflation, driven by the same technology and initial price
level, coincide in every variable. -/
theorem taylor_unique {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e ygap' piH' i' y' s' pH' e' : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (h' : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap' piH' i' y' s' pH' e')
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (hyA' : 𝔼.Adapted ygap') (hpA' : 𝔼.Adapted piH')
    (hyB' : BoundedProc ygap') (hpB' : BoundedProc piH') :
    ygap = ygap' ∧ piH = piH' ∧ i = i' ∧ y = y' ∧ s = s' ∧ pH = pH' ∧ e = e' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA' hpA' hyB' hpB').1 h'
  have e1 : ygap = ygap' := a1.trans b1.symm
  have e2 : piH = piH' := a2.trans b2.symm
  have e3 : i = i' := by rw [a3, b3, e2]
  have e4 : y = y' := by rw [a4, b4, e1]
  have e5 : s = s' := by rw [a5, b5, e4]
  have e6 : pH = pH' := by rw [a6, b6, e2]
  exact ⟨e1, e2, e3, e4, e5, e6, by rw [a7, b7, e5, e6]⟩

/-- Galí (2015), p. 241, with `φ_y = 0`: `Λ_a msvDen = 1` when the denominator is nonzero. -/
theorem lambda_mul_den {β σv κv φπ ρa : ℝ} (hD : msvDen β σv κv φπ 0 ρa ≠ 0) :
    msvLambda β σv κv φπ 0 ρa * ((1 - β * ρa) * σv * (1 - ρa) + κv * (φπ - ρa)) = 1 := by
  have : (1 - β * ρa) * σv * (1 - ρa) + κv * (φπ - ρa) = msvDen β σv κv φπ 0 ρa := by
    unfold msvDen; ring
  rw [this]
  unfold msvLambda
  field_simp

/-- **Ex. 8.2(a), closed forms under (38)** (Galí 2015, p. 260, with `ψ_{ra} = σ_υ (1 − ρ_a)
ψ_{ya}`): in the equilibrium of `taylor_iff`, with `Λ_a = msvLambda`,
`ỹ_t = −σ_υ (1 − ρ_a)(1 − βρ_a) Λ_a ψ_{ya} a_t`, `π_{H,t} = −σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t`,
`y_t = κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`, `s_t = σ_υ κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
`i_t = ρ − φ_π σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t` and
`e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} [(φ_π − ρ_a) a_t − (1 − ρ_a) ∑_{k ≤ t} a_k]`. -/
theorem taylor_closed_forms_38 {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ} {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (t : ℕ) (ω : Ω) :
    ygap t ω = -(σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya) * a t ω ∧
      piH t ω = -(σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya) * a t ω ∧
      y t ω = κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      s t ω = σv * κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      i t ω = ρ - φπ * σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      e t ω = pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya *
        ((φπ - ρa) * a t ω - (1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hΛ := lambda_mul_den (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28).ne'
  set Λ := msvLambda β σv κv φπ 0 ρa with hΛdef
  have hyg : ∀ t ω, ygap t ω = -(σv * (1 - ρa) * (1 - β * ρa) * Λ * ψya) * a t ω := by
    intro t ω
    rw [h1]
    simp only [shock, Pi.smul_apply, smul_eq_mul, msvPsiY, h38, ← hΛdef]
    ring
  have hpi : ∀ t ω, piH t ω = -(σv * κv * (1 - ρa) * Λ * ψya) * a t ω := by
    intro t ω
    rw [h2]
    simp only [shock, Pi.smul_apply, smul_eq_mul, msvPsiPi, h38, ← hΛdef]
    ring
  have hy : ∀ t ω, y t ω = κv * (φπ - ρa) * Λ * ψya * a t ω := by
    intro t ω
    rw [h4]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hyg]
    linear_combination (-(ψya * a t ω)) * hΛ
  have hs : ∀ t ω, s t ω = σv * κv * (φπ - ρa) * Λ * ψya * a t ω := by
    intro t ω
    rw [h5]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy]; ring
  have hsum : ∀ t ω, ∑ k ∈ Finset.range (t + 1), piH k ω =
      -(σv * κv * (1 - ρa) * Λ * ψya) * ∑ k ∈ Finset.range (t + 1), a k ω := by
    intro t ω
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hpi k ω
  refine ⟨hyg t ω, hpi t ω, hy t ω, hs t ω, ?_, ?_⟩
  · rw [h3]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpi]; ring
  · rw [h7]
    simp only [Pi.add_apply]
    rw [h6]
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [hs, hsum]; ring

/-- **Ex. 8.2(a), signs** (Galí 2015, p. 260): with `ψ_{ya} > 0`, `ρ_a < 1` and `φ_π > 1`, the
coefficients on `a_t` are negative for the output gap and domestic inflation and positive for
output and the terms of trade (a real depreciation). -/
theorem taylor_signs_38 {β σv κv φπ ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) (hψ : 0 < ψya) :
    -(σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya) < 0 ∧
      -(σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya) < 0 ∧
      0 < κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya ∧
      0 < σv * κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hΛ : 0 < msvLambda β σv κv φπ 0 ρa :=
    one_div_pos.2 (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28)
  have h1 : 0 < 1 - ρa := by linarith
  have h2 : 0 < 1 - β * ρa := by nlinarith
  have h3 : 0 < φπ - ρa := by linarith
  refine ⟨?_, ?_, by positivity, by positivity⟩
  · have : 0 < σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by positivity
    linarith
  · have : 0 < σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by positivity
    linarith

/-- **Ex. 8.2(a), impulse response of the exchange rate** (Galí 2015, p. 260): for a one-time
shock `a_t = ρ_aᵗ a_0`, `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} (φ_π ρ_aᵗ − 1) a_0` and
`p_{H,t} = p_{H,−1} − σ_υ κ_υ Λ_a ψ_{ya} (1 − ρ_a^{t+1}) a_0`. -/
theorem taylor_irf_38 {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (t : ℕ) (ω : Ω) :
    e t ω = pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * ρa ^ t - 1) * a0 ω ∧
      pH t ω = pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (1 - ρa ^ (t + 1)) * a0 ω := by
  have hcf := taylor_closed_forms_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab h hyA hpA hyB hpB t ω
  have hgeo : (1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω = (1 - ρa ^ (t + 1)) * a0 ω := by
    rw [← mul_neg_geom_sum, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hirf k ω
  obtain ⟨-, hpi, -, hs, -, he⟩ := hcf
  obtain ⟨-, -, -, -, -, h6, h7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  refine ⟨?_, ?_⟩
  · rw [he, hgeo, hirf, pow_succ]; ring
  · have hp := (taylor_closed_forms_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab h hyA hpA hyB hpB)
    have hsum : ∑ k ∈ Finset.range (t + 1), piH k ω =
        -(σv * κv * msvLambda β σv κv φπ 0 ρa * ψya) *
          ((1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [(hp k ω).2.1]; ring
    rw [h6]
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [hsum, hgeo]; ring

/-- **Ex. 8.2(a), long run** (Galí 2015, p. 260): after a one-time shock with `0 ≤ ρ_a < 1`, the
nominal exchange rate converges to `p_{H,−1} − σ_υ κ_υ Λ_a ψ_{ya} a_0`: a permanent nominal
appreciation, after the depreciation on impact `e_0 − p_{H,−1} = σ_υ κ_υ Λ_a ψ_{ya}(φ_π − 1) a_0`
(positive for `a_0 > 0`, `ψ_{ya} > 0`). -/
theorem taylor_irf_tendsto {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (ω : Ω) :
    e 0 ω - pm1 ω = σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ - 1) * a0 ω ∧
      Tendsto (fun t => e t ω) atTop
        (𝓝 (pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * a0 ω)) := by
  have hirfE := fun t => (taylor_irf_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab hirf h hyA hpA hyB
    hpB t ω).1
  refine ⟨by rw [hirfE 0]; ring, ?_⟩
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hlim : Tendsto (fun t => pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya *
      (φπ * ρa ^ t - 1) * a0 ω) atTop
      (𝓝 (pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * 0 - 1) * a0 ω)) := by
    refine tendsto_const_nhds.add (((tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul hpow).sub tendsto_const_nhds))).mul tendsto_const_nhds)
  rw [show pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * 0 - 1) * a0 ω =
    pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * a0 ω by ring] at hlim
  exact hlim.congr fun t => (hirfE t).symm

/-! ### Part (b): the peg — the characteristic polynomial -/

/-- Galí (2015), Ex. 8.2(b): the characteristic polynomial of the peg dynamics,
`Q(λ) = σ_υ β λ² − (σ_υ (1 + β) + κ_υ) λ + σ_υ` (`σ_υ` times
`βλ² − (1 + β + κ_υ/σ_υ) λ + 1`). -/
def charQ (β σv κv r : ℝ) : ℝ := σv * β * r ^ 2 - (σv * (1 + β) + κv) * r + σv

/-- Galí (2015), Ex. 8.2(b): `Q(0) = σ_υ > 0` and `Q(1) = −κ_υ < 0`, so `Q` has a root in
`(0, 1)`. -/
theorem exists_root {β σv κv : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) :
    ∃ r, 0 < r ∧ r < 1 ∧ charQ β σv κv r = 0 := by
  have hc : Continuous (charQ β σv κv) := by unfold charQ; fun_prop
  have h := intermediate_value_Ioo' (zero_le_one' ℝ) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charQ β σv κv 1) (charQ β σv κv 0) by
      unfold charQ; constructor <;> nlinarith)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), Ex. 8.2(b): for `0 < β < 1`, `σ_υ, κ_υ > 0`, `Q` has at most one root below 1;
in particular the root in `(0, 1)` is unique. -/
theorem root_unique {β σv κv r r' : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hr1 : r < 1) (hr'1 : r' < 1)
    (hQ : charQ β σv κv r = 0) (hQ' : charQ β σv κv r' = 0) : r = r' := by
  by_contra hne
  have hsub : r - r' ≠ 0 := sub_ne_zero.2 hne
  have hsum : σv * β * (r + r') = σv * (1 + β) + κv := by
    apply mul_right_cancel₀ hsub
    unfold charQ at hQ hQ'
    linear_combination hQ - hQ'
  have h1 : σv * β * (r + r') < σv * β * 2 :=
    mul_lt_mul_of_pos_left (by linarith) (mul_pos hσ hβ0)
  nlinarith

/-- Galí (2015), Ex. 8.2(b): if `λ ∈ (0, 1)` is a root, the other root is `1/(βλ) > 1`: the
peg dynamics have exactly one stable and one unstable root (saddle path). -/
theorem other_root {β σv κv r : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hQ : charQ β σv κv r = 0) : charQ β σv κv (1 / (β * r)) = 0 ∧ 1 < 1 / (β * r) := by
  have hbr : 0 < β * r := mul_pos hβ0 hr0
  refine ⟨?_, ?_⟩
  · unfold charQ at hQ ⊢
    field_simp
    linear_combination hQ
  · rw [lt_div_iff₀ hbr]; nlinarith

/-! ### Part (b): the factorisation -/

/-- **The factorisation** (Galí 2015, Ex. 8.2(b), pointwise algebra): at a root `λ ≠ 0` of `Q`,
and given the peg relation `σ_υ ỹ_t + p_{H,t} + σ_υ ψ_{ya} a_t = 0`, the Phillips curve
`p_{H,t} − p_{H,t−1} = β (E_t p_{H,t+1} − p_{H,t}) + κ_υ ỹ_t` holds iff
`p_{H,t} − λ p_{H,t−1} = βλ (E_t p_{H,t+1} − λ p_{H,t}) − λ κ_υ ψ_{ya} a_t`. -/
theorem peg_nkpc_iff {β σv κv ψya r : ℝ} (hσ : σv ≠ 0) (hr : r ≠ 0)
    (hQ : charQ β σv κv r = 0) {p l Ep yg at' : ℝ} (hpeg : σv * yg + p + σv * ψya * at' = 0) :
    p - l = β * (Ep - p) + κv * yg ↔
      p - r * l = β * r * (Ep - r * p) + -(r * κv * ψya) * at' := by
  unfold charQ at hQ
  constructor
  · intro hN
    apply mul_left_cancel₀ hσ
    linear_combination (r * σv) * hN + (r * κv) * hpeg + p * hQ
  · intro hG
    apply mul_left_cancel₀ (mul_ne_zero hr hσ)
    linear_combination σv * hG - (r * κv) * hpeg - p * hQ

/-- Galí (2015), Ex. 8.2(b): the quasi-difference `w_t = p_{H,t} − λ p_{H,t−1}`. -/
def wseq (r : ℝ) (pm1 : Ω → ℝ) (pH : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := pH t - r • lagP pm1 pH t

/-- Galí (2015), Ex. 8.2(b): the forcing `−λ κ_υ ψ_{ya} a_t` of the forward equation for `w`. -/
def pegShock (r κv ψya : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(r * κv * ψya)) • a t

/-- Galí (2015), Ex. 8.2(b): the response coefficient `θ = (1 − βλρ_a)⁻¹ (−λ κ_υ ψ_{ya})`. -/
noncomputable def pegTheta (β κv ψya ρa r : ℝ) : ℝ := (1 - β * r * ρa)⁻¹ * (-(r * κv * ψya))

/-- Galí (2015), Ex. 8.2(b): `θ = −λ κ_υ ψ_{ya}/(1 − βλρ_a)`. -/
theorem pegTheta_eq (β κv ψya ρa r : ℝ) :
    pegTheta β κv ψya ρa r = -(r * κv * ψya) / (1 - β * r * ρa) := by
  unfold pegTheta; ring

/-- Galí (2015), Ex. 8.2(b): the candidate domestic price level, `p_{H,0} = λ p_{H,−1} + θ a_0`,
`p_{H,t+1} = λ p_{H,t} + θ a_{t+1}`. -/
def pegP (r θ : ℝ) (pm1 : Ω → ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => r • pm1 + θ • a 0
  | t + 1 => r • pegP r θ pm1 a t + θ • a (t + 1)

/-- Galí (2015), Ex. 8.2(b): `p_{H,t} = λ p_{H,t−1} + θ a_t` for all `t` iff `p_H = pegP`. -/
theorem pegP_iff {r θ : ℝ} {pm1 : Ω → ℝ} {a pH : ℕ → Ω → ℝ} :
    (∀ t, pH t = r • lagP pm1 pH t + θ • a t) ↔ pH = pegP r θ pm1 a := by
  constructor
  · intro h
    funext t
    induction t with
    | zero => rw [h 0]; rfl
    | succ t ih => rw [h (t + 1)]; simp only [lagP, pegP]; rw [ih]
  · rintro rfl t
    cases t <;> rfl

/-- Galí (2015), Ex. 8.2(b) (**closed form**): `p_{H,t} = λ^{t+1} p_{H,−1} + θ ∑_{k ≤ t}
λ^{t−k} a_k`. -/
theorem pegP_closed (r θ : ℝ) (pm1 : Ω → ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pegP r θ pm1 a t ω =
      r ^ (t + 1) * pm1 ω + θ * ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * a k ω := by
  induction t with
  | zero => simp [pegP]
  | succ t ih =>
    have hrec : pegP r θ pm1 a (t + 1) ω = r * pegP r θ pm1 a t ω + θ * a (t + 1) ω := rfl
    have hs : ∑ k ∈ Finset.range (t + 1), r ^ (t + 1 - k) * a k ω =
        r * ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * a k ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : t + 1 - k = t - k + 1 := by have := Finset.mem_range.1 hk; omega
      rw [this, pow_succ]; ring
    rw [hrec, ih, Finset.sum_range_succ (fun k => r ^ (t + 1 - k) * a k ω) (t + 1), hs,
      Nat.sub_self, pow_zero]
    ring

/-- Galí (2015), Ex. 8.2(b): `pegP` is adapted when `p_{H,−1}` is known at date 0. -/
theorem pegP_adapted {r θ ρa : ℝ} {pm1 : Ω → ℝ} {a : ℕ → Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1)
    (ha : 𝔼.IsAR1 ρa a) : 𝔼.Adapted (pegP r θ pm1 a) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 (r • pm1 + θ • a 0) = r • pm1 + θ • a 0
    rw [map_add, map_smul, map_smul, hpm, ha.1 0]
  | succ t ih =>
    change 𝔼.E (t + 1) (r • pegP r θ pm1 a t + θ • a (t + 1)) = _
    rw [map_add, map_smul, map_smul, ha.1 (t + 1)]
    have := 𝔼.known (Nat.le_succ t) (pegP r θ pm1 a t)
    rw [ih] at this
    rw [this]
    rfl

/-- Galí (2015), Ex. 8.2(b): `pegP` is bounded for `0 < λ < 1` and bounded `p_{H,−1}`, `a`. -/
theorem pegP_bounded {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {pm1 : Ω → ℝ} {a : ℕ → Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) (hab : BoundedProc a) : BoundedProc (pegP r θ pm1 a) := by
  obtain ⟨M0, hM0⟩ := hpmb
  obtain ⟨Ma, hMa⟩ := hab
  set K := |θ| * |Ma| / (1 - r) with hK
  have h1r : 0 < 1 - r := by linarith
  have hKeq : (1 - r) * K = |θ| * |Ma| := by rw [hK]; field_simp
  have hKnn : 0 ≤ K := by positivity
  have hθa : ∀ t ω, |θ * a t ω| ≤ |θ| * |Ma| := fun t ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hMa t ω).trans (le_abs_self Ma)) (abs_nonneg θ)
  refine ⟨|M0| + K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero =>
    change |r * pm1 ω + θ * a 0 ω| ≤ _
    have h1 : |r * pm1 ω| ≤ r * |M0| := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left ((hM0 ω).trans (le_abs_self M0)) hr0.le
    have h2 := hθa 0 ω
    have h3 : r * |M0| ≤ |M0| := by nlinarith [abs_nonneg M0]
    have h4 : |θ| * |Ma| ≤ K := by nlinarith
    linarith [abs_add_le (r * pm1 ω) (θ * a 0 ω)]
  | succ t ih =>
    change |r * pegP r θ pm1 a t ω + θ * a (t + 1) ω| ≤ _
    have h1 : |r * pegP r θ pm1 a t ω| ≤ r * (|M0| + K) := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left (ih ω) hr0.le
    have h2 := hθa (t + 1) ω
    have h3 : r * (|M0| + K) + |θ| * |Ma| ≤ |M0| + K := by nlinarith [abs_nonneg M0]
    linarith [abs_add_le (r * pegP r θ pm1 a t ω) (θ * a (t + 1) ω)]

/-! ### Part (b): existence and uniqueness of the bounded equilibrium under the peg -/

/-- Galí (2015), Ex. 8.2(b): the response coefficient `θ` makes `w_t = θ a_t` the forward
solution: `θ a_t = βλ E_t(θ a_{t+1}) − λ κ_υ ψ_{ya} a_t`. -/
theorem theta_solves {β κv ψya ρa r : ℝ} (hden : 1 - β * r * ρa ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    pegTheta β κv ψya ρa r • a t =
      (β * r) • 𝔼.E t (pegTheta β κv ψya ρa r • a (t + 1)) + pegShock r κv ψya a t := by
  have h := 𝔼.forward_ar1_solves hden (isAR1_smul 𝔼 ha (-(r * κv * ψya))) t
  simp only [smul_smul] at h
  unfold pegTheta pegShock
  exact h

/-- **Ex. 8.2(b)** (Galí 2015, p. 260): under the peg, with `λ` the root of `Q` in `(0, 1)`,
a tuple with bounded adapted domestic price level is an equilibrium iff
`p_{H,t} = λ p_{H,t−1} + θ a_t`, `ỹ_t = −σ_υ⁻¹ p_{H,t} − ψ_{ya} a_t`, `y_t = −σ_υ⁻¹ p_{H,t}`,
`s_t = −p_{H,t}`, `e_t = 0`, `π_{H,t} = p_{H,t} − p_{H,t−1}` and
`i_t = ρ + (σ_υ (1 − ρ_a) ψ_{ya} − ψ_{ra}) a_t`. -/
theorem peg_iff {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (hpA : 𝔼.Adapted pH) (hpB : BoundedProc pH) :
    PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ↔
      (∀ t, pH t = r • lagP pm1 pH t + pegTheta β κv ψya ρa r • a t) ∧
        ygap = (fun t => (-σv⁻¹) • pH t - ψya • a t) ∧ y = (fun t => (-σv⁻¹) • pH t) ∧
        s = (fun t => -pH t) ∧ e = (fun _ => 0) ∧ piH = (fun t => pH t - lagP pm1 pH t) ∧
        i = (fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) := by
  have hinv : σv * σv⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hbr : 0 < β * r := mul_pos hβ0 hr0
  have hbr1 : β * r < 1 := by nlinarith
  have hden : 1 - β * r * ρa ≠ 0 := by
    have : β * r * ρa < 1 := by
      rcases le_or_gt ρa 0 with h | h
      · nlinarith
      · nlinarith
    linarith
  -- expectations of the lagged and future price level
  have hEpi : ∀ t, 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) = 𝔼.E t (pH (t + 1)) - pH t := by
    intro t
    change 𝔼.E t (pH (t + 1) - pH t) = _
    rw [map_sub, hpA t]
  -- the forward equation for `w` and the explicit solution
  have hfwd : ∀ (ygap' : ℕ → Ω → ℝ),
      (∀ t ω, σv * ygap' t ω + pH t ω + σv * ψya * a t ω = 0) →
      ((∀ t, (pH t - lagP pm1 pH t) =
          β • 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) + κv • ygap' t) ↔
        ∀ t, wseq r pm1 pH t =
          (β * r) • 𝔼.E t (wseq r pm1 pH (t + 1)) + pegShock r κv ψya a t) := by
    intro ygap' hpeg
    have hEw : ∀ t, 𝔼.E t (wseq r pm1 pH (t + 1)) = 𝔼.E t (pH (t + 1)) - r • pH t := by
      intro t
      change 𝔼.E t (pH (t + 1) - r • pH t) = _
      rw [map_sub, map_smul, hpA t]
    constructor
    · intro hN t
      funext ω
      have e := congrFun (hN t) ω
      rw [hEpi] at e
      rw [hEw]
      simp only [wseq, pegShock, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      exact (peg_nkpc_iff hσ.ne' hr0.ne' hQ (hpeg t ω)).1 e
    · intro hG t
      funext ω
      have e := congrFun (hG t) ω
      rw [hEw] at e
      rw [hEpi]
      simp only [wseq, pegShock, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      exact (peg_nkpc_iff hσ.ne' hr0.ne' hQ (hpeg t ω)).2 e
  -- boundedness of `w` and of the candidate `θ a`
  have hlagB : BoundedProc (lagP pm1 pH) := by
    obtain ⟨M0, hM0⟩ := hpmb
    obtain ⟨Mp, hMp⟩ := hpB
    refine ⟨|M0| + |Mp|, fun t ω => ?_⟩
    cases t with
    | zero =>
      change |pm1 ω| ≤ _
      linarith [hM0 ω, le_abs_self M0, abs_nonneg Mp]
    | succ t =>
      change |pH t ω| ≤ _
      linarith [hMp t ω, le_abs_self Mp, abs_nonneg M0]
  have hwB : BoundedProc (wseq r pm1 pH) := by
    obtain ⟨M1, hM1⟩ := hpB
    obtain ⟨M2, hM2⟩ := hlagB
    refine ⟨M1 + |r| * M2, fun t ω => ?_⟩
    simp only [wseq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : |r * lagP pm1 pH t ω| ≤ |r| * M2 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM2 t ω) (abs_nonneg r)
    linarith [abs_sub (pH t ω) (r * lagP pm1 pH t ω), hM1 t ω]
  have hbrabs : |β * r| < 1 := by rw [abs_of_pos hbr]; exact hbr1
  have hθsol := theta_solves 𝔼 (κv := κv) (ψya := ψya) hden ha
  -- the DIS equation, given the peg relation for `ỹ`
  have hdis : ∀ (ygap' i' : ℕ → Ω → ℝ), (∀ t, ygap' t = (-σv⁻¹) • pH t - ψya • a t) →
      ((∀ t, ygap' t = 𝔼.E t (ygap' (t + 1)) -
          σv⁻¹ • (i' t - 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) - natRate ρ ψra a t)) ↔
        i' = fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) := by
    intro ygap' i' hyg
    have hEy : ∀ t, 𝔼.E t (ygap' (t + 1)) = (-σv⁻¹) • 𝔼.E t (pH (t + 1)) - (ψya * ρa) • a t := by
      intro t
      rw [hyg (t + 1), map_sub, map_smul, map_smul, ha.2 t, smul_smul]
    constructor
    · intro hD
      funext t ω
      have e := congrFun (hD t) ω
      rw [hEy, hEpi, hyg t] at e
      simp only [natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      linear_combination σv * e -
        (i' t ω - (𝔼.E t (pH (t + 1)) ω - pH t ω) - (ρ - ψra * a t ω) - pH t ω +
          𝔼.E t (pH (t + 1)) ω) * hinv
    · intro hi t
      funext ω
      rw [hEy, hEpi, hyg t, hi]
      simp only [natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ψya * a t ω * (1 - ρa)) * hinv
  constructor
  · rintro ⟨hB, hpeg⟩
    have hyg : ∀ t, ygap t = (-σv⁻¹) • pH t - ψya • a t := by
      intro t
      obtain ⟨-, -, h3, h4, -, h6⟩ := hB t
      funext ω
      have e3 := congrFun h3 ω
      have e4 := congrFun h4 ω
      have e6 := congrFun h6 ω
      have e0 := congrFun (hpeg t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
        at e3 e4 e6 e0 ⊢
      linear_combination -σv⁻¹ * (e6 - e0) - σv⁻¹ * e4 - σv⁻¹ * σv * e3 -
        (ygap t ω + ψya * a t ω) * hinv
    have hpegrel : ∀ t ω, σv * ygap t ω + pH t ω + σv * ψya * a t ω = 0 := by
      intro t ω
      rw [hyg t]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(pH t ω)) * hinv
    have hpiH : ∀ t, piH t = pH t - lagP pm1 pH t := fun t => (hB t).2.2.2.2.1
    have hN : ∀ t, (pH t - lagP pm1 pH t) =
        β • 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) + κv • ygap t := by
      intro t
      have := (hB t).1
      rw [hpiH t, hpiH (t + 1)] at this
      exact this
    have hw := (hfwd ygap hpegrel).1 hN
    have hweq := 𝔼.forward_unique hbrabs hw hθsol hwB (boundedProc_smul hab _)
    have hrec : ∀ t, pH t = r • lagP pm1 pH t + pegTheta β κv ψya ρa r • a t := by
      intro t
      have := congrFun hweq t
      simp only [wseq] at this
      rw [← this]; abel
    refine ⟨hrec, funext hyg, funext fun t => ?_, funext fun t => ?_, funext hpeg,
      funext hpiH, (hdis ygap i hyg).1 fun t => ?_⟩
    · obtain ⟨-, -, h3, -, -, -⟩ := hB t
      rw [h3, hyg t]; abel
    · obtain ⟨-, -, -, -, -, h6⟩ := hB t
      rw [hpeg t] at h6
      funext ω
      have := congrFun h6 ω
      simp only [Pi.zero_apply, Pi.add_apply] at this
      simp only [Pi.neg_apply]
      linarith
    · have := (hB t).2.1
      rw [hpiH (t + 1)] at this
      exact this
  · rintro ⟨hrec, hyg, hy, hs, he, hpiH, hi⟩
    have hyg' : ∀ t, ygap t = (-σv⁻¹) • pH t - ψya • a t := fun t => by rw [hyg]
    have hpegrel : ∀ t ω, σv * ygap t ω + pH t ω + σv * ψya * a t ω = 0 := by
      intro t ω
      rw [hyg' t]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(pH t ω)) * hinv
    have hweq : wseq r pm1 pH = fun t => pegTheta β κv ψya ρa r • a t := by
      funext t
      simp only [wseq]
      rw [hrec t]; abel
    have hw : ∀ t, wseq r pm1 pH t =
        (β * r) • 𝔼.E t (wseq r pm1 pH (t + 1)) + pegShock r κv ψya a t := by
      rw [hweq]; exact hθsol
    have hN := (hfwd ygap hpegrel).2 hw
    have hD := (hdis ygap i hyg').2 hi
    refine ⟨fun t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t => by rw [he]⟩
    · rw [hpiH]; exact hN t
    · rw [hpiH]; exact hD t
    · rw [hy, hyg]; simp only [sub_add_cancel]
    · rw [hs, hy]
      funext ω
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (pH t ω) * hinv
    · rw [hpiH]
    · rw [he, hs]; simp

/-- **Ex. 8.2(b), existence** (Galí 2015, p. 260): under the peg there is an equilibrium with a
bounded adapted domestic price level, `p_H = pegP` (for `λ` the root of `Q` in `(0, 1)`). -/
theorem peg_exists {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1)
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) :
    ∃ ygap piH i y s pH e, PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧
      pH = pegP r (pegTheta β κv ψya ρa r) pm1 a ∧ 𝔼.Adapted pH ∧ BoundedProc pH := by
  set pH := pegP r (pegTheta β κv ψya ρa r) pm1 a
  have hpA : 𝔼.Adapted pH := pegP_adapted 𝔼 hpm ha
  have hpB : BoundedProc pH := pegP_bounded hr0 hr1 hpmb hab
  refine ⟨fun t => (-σv⁻¹) • pH t - ψya • a t, fun t => pH t - lagP pm1 pH t,
    fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t, fun t => (-σv⁻¹) • pH t,
    fun t => -pH t, pH, fun _ => 0, ?_, rfl, hpA, hpB⟩
  exact (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA hpB).2
    ⟨pegP_iff.2 rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Ex. 8.2(b), uniqueness** (Galí 2015, p. 260): under the peg, every equilibrium with a
bounded adapted domestic price level has `p_H = pegP` and coincides with the one of
`peg_exists` in every variable. -/
theorem peg_unique {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M)
    {ygap piH i y s pH e ygap' piH' i' y' s' pH' e' : ℕ → Ω → ℝ}
    (h : PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e)
    (h' : PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap' piH' i' y' s' pH' e')
    (hpA : 𝔼.Adapted pH) (hpB : BoundedProc pH) (hpA' : 𝔼.Adapted pH')
    (hpB' : BoundedProc pH') :
    pH = pegP r (pegTheta β κv ψya ρa r) pm1 a ∧
      ygap = ygap' ∧ piH = piH' ∧ i = i' ∧ y = y' ∧ s = s' ∧ pH = pH' ∧ e = e' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA hpB).1 h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
    (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA' hpB').1 h'
  have hp : pH = pegP r (pegTheta β κv ψya ρa r) pm1 a := pegP_iff.1 a1
  have hp' : pH' = pegP r (pegTheta β κv ψya ρa r) pm1 a := pegP_iff.1 b1
  have e6 : pH = pH' := hp.trans hp'.symm
  refine ⟨hp, by rw [a2, b2, e6], by rw [a6, b6, e6], by rw [a7, b7], by rw [a3, b3, e6],
    by rw [a4, b4, e6], e6, by rw [a5, b5]⟩

/-- Galí (2015), Ex. 8.2(b), with (38) (`ψ_{ra} = σ_υ (1 − ρ_a) ψ_{ya}`): under the peg the
nominal rate is constant, `i_t = ρ = i*` — consistent with uncovered interest parity (18). -/
theorem peg_rate_38 {σv ρ ψra ψya ρa : ℝ} (h38 : ψra = σv * (1 - ρa) * ψya)
    (a : ℕ → Ω → ℝ) :
    (fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) = fun _ => fun _ => ρ := by
  funext t
  rw [h38, sub_self, zero_smul, add_zero]

/-- Galí (2015), Ex. 8.2(b): for `ψ_{ya} > 0` (and `κ_υ > 0`, `0 < λ < 1`) the response
coefficient `θ` is negative: a positive technology shock lowers the domestic price level. -/
theorem pegTheta_neg {β κv ψya ρa r : ℝ} (hκ : 0 < κv) (hψ : 0 < ψya) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    pegTheta β κv ψya ρa r < 0 := by
  rw [pegTheta_eq]
  have hbr : β * r < 1 := by nlinarith
  have hden : 0 < 1 - β * r * ρa := by
    rcases le_or_gt ρa 0 with h | h
    · nlinarith [mul_pos hβ0 hr0]
    · nlinarith [mul_pos hβ0 hr0]
  exact div_neg_of_neg_of_pos (by have := mul_pos (mul_pos hr0 hκ) hψ; linarith) hden

/-- **Ex. 8.2(b), impulse responses** (Galí 2015, p. 260): after a one-time positive shock
(`a_t = ρ_aᵗ a_0`, `a_0 > 0`, `0 ≤ ρ_a < 1`) from `p_{H,−1} = 0`, with `ψ_{ya} > 0`, the domestic
price level is `p_{H,t} = θ (∑_{k ≤ t} λ^{t−k} ρ_aᵏ) a_0 < 0` at every date, so output
`y_t = −σ_υ⁻¹ p_{H,t}` and the terms of trade `s_t = −p_{H,t}` rise at every date. -/
theorem peg_irf_signs {β σv κv ψya ρa r : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hψ : 0 < ψya)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1)
    {a : ℕ → Ω → ℝ} {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) (t : ℕ) (ω : Ω)
    (ha0 : 0 < a0 ω) :
    pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω =
        pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) * a0 ω ∧
      pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω < 0 ∧
      0 < -σv⁻¹ * pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω ∧
      0 < -pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω := by
  have hθ := pegTheta_neg hκ hψ hβ0 hβ1 hρ1 hr0 hr1
  have hform : pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω =
      pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) * a0 ω := by
    rw [pegP_closed, mul_zero, zero_add, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hirf]; ring
  have hsum : 0 < ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k := by
    have hle : r ^ (t - 0) * ρa ^ 0 ≤ ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k :=
      Finset.single_le_sum (f := fun k => r ^ (t - k) * ρa ^ k)
        (fun k _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos t))
    have : 0 < r ^ (t - 0) * ρa ^ 0 := by positivity
    linarith
  have hneg : pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω < 0 := by
    rw [hform]
    have : 0 < -pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) *
        a0 ω := by
      have : 0 < -pegTheta β κv ψya ρa r := by linarith
      positivity
    linarith
  refine ⟨hform, hneg, ?_, by linarith⟩
  have : 0 < σv⁻¹ := inv_pos.2 hσ
  nlinarith

end Gali.OpenEconomy.Ex8_2

set_option linter.style.longLine false
#print axioms Gali.OpenEconomy.SchurStable
#print axioms Gali.OpenEconomy.disc
#print axioms Gali.OpenEconomy.root₁
#print axioms Gali.OpenEconomy.root₂
#print axioms Gali.OpenEconomy.root_sum
#print axioms Gali.OpenEconomy.root_prod
#print axioms Gali.OpenEconomy.root_eq
#print axioms Gali.OpenEconomy.normSq_root_of_neg
#print axioms Gali.OpenEconomy.norm_root_of_nonneg
#print axioms Gali.OpenEconomy.schurStable_iff_roots
#print axioms Gali.OpenEconomy.chSeq
#print axioms Gali.OpenEconomy.convSeq
#print axioms Gali.OpenEconomy.convSeq_rec
#print axioms Gali.OpenEconomy.chSeq_eq_convSeq
#print axioms Gali.OpenEconomy.norm_convSeq_le
#print axioms Gali.OpenEconomy.abs_chSeq_le
#print axioms Gali.OpenEconomy.tendsto_chSeq
#print axioms Gali.OpenEconomy.tr2
#print axioms Gali.OpenEconomy.det2
#print axioms Gali.OpenEconomy.tr2_eq_trace
#print axioms Gali.OpenEconomy.det2_eq_det
#print axioms Gali.OpenEconomy.sq_eq_cayleyHamilton
#print axioms Gali.OpenEconomy.pow_succ_eq
#print axioms Gali.OpenEconomy.abs_pow_entry_le
#print axioms Gali.OpenEconomy.tendsto_pow_entry
#print axioms Gali.OpenEconomy.BoundedSeq
#print axioms Gali.OpenEconomy.homogeneous_iterate
#print axioms Gali.OpenEconomy.abs_mulVec_le
#print axioms Gali.OpenEconomy.homogeneous_eq_zero
#print axioms Gali.OpenEconomy.eq_root_of_eq
#print axioms Gali.OpenEconomy.exists_eigenvector
#print axioms Gali.OpenEconomy.exists_bounded_homogeneous
#print axioms Gali.OpenEconomy.ExpectationSystem
#print axioms Gali.OpenEconomy.ExpectationSystem.mk
#print axioms Gali.OpenEconomy.ExpectationSystem.E
#print axioms Gali.OpenEconomy.ExpectationSystem.const
#print axioms Gali.OpenEconomy.ExpectationSystem.mono
#print axioms Gali.OpenEconomy.ExpectationSystem.tower
#print axioms Gali.OpenEconomy.ExpectationSystem.known
#print axioms Gali.OpenEconomy.perfectForesight
#print axioms Gali.OpenEconomy.BoundedProc
#print axioms Gali.OpenEconomy.BoundedVec
#print axioms Gali.OpenEconomy.ExpectationSystem.Adapted
#print axioms Gali.OpenEconomy.ExpectationSystem.IsAR1
#print axioms Gali.OpenEconomy.ExpectationSystem.E_neg
#print axioms Gali.OpenEconomy.ExpectationSystem.E_smul
#print axioms Gali.OpenEconomy.ExpectationSystem.E_E_self
#print axioms Gali.OpenEconomy.ExpectationSystem.abs_E_le
#print axioms Gali.OpenEconomy.ExpectationSystem.bounded_E
#print axioms Gali.OpenEconomy.ExpectationSystem.ar1_iterate
#print axioms Gali.OpenEconomy.ExpectationSystem.forward_iterate
#print axioms Gali.OpenEconomy.ExpectationSystem.forward_unique
#print axioms Gali.OpenEconomy.ExpectationSystem.forward_ar1_solves
#print axioms Gali.OpenEconomy.ExpectationSystem.E_tsum
#print axioms Gali.OpenEconomy.ExpectationSystem.forwardSeries
#print axioms Gali.OpenEconomy.ExpectationSystem.forwardSeries_summable
#print axioms Gali.OpenEconomy.ExpectationSystem.forwardSeries_solves
#print axioms Gali.OpenEconomy.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.OpenEconomy.ExpectationSystem.eq_forwardSeries
#print axioms Gali.OpenEconomy.ExpectationSystem.forwardSeries_adapted
#print axioms Gali.OpenEconomy.ExpectationSystem.PullOut
#print axioms Gali.OpenEconomy.ExpectationSystem.Solves
#print axioms Gali.OpenEconomy.ExpectationSystem.AdaptedVec
#print axioms Gali.OpenEconomy.ExpectationSystem.system_iterate
#print axioms Gali.OpenEconomy.ExpectationSystem.system_unique
#print axioms Gali.OpenEconomy.ExpectationSystem.system_not_unique
#print axioms Gali.OpenEconomy.ExpectationSystem.Determinate
#print axioms Gali.OpenEconomy.ExpectationSystem.determinate_iff
#print axioms Gali.OpenEconomy.perfectForesight_pullOut
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinObs
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinTree
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinSystem
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.firstHeads
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinShock
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinAR1
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.OpenEconomy.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Gali.OpenEconomy.Preferences.rpow_tangent_le
#print axioms Gali.OpenEconomy.Preferences.rpow_tangent_eq_iff
#print axioms Gali.OpenEconomy.Preferences.weighted_tangent
#print axioms Gali.OpenEconomy.Preferences.cesIndex
#print axioms Gali.OpenEconomy.Preferences.cesIndexCD
#print axioms Gali.OpenEconomy.Preferences.cpi
#print axioms Gali.OpenEconomy.Preferences.cpiCD
#print axioms Gali.OpenEconomy.Preferences.homeDemand
#print axioms Gali.OpenEconomy.Preferences.foreignDemand
#print axioms Gali.OpenEconomy.Preferences.cpi_pos
#print axioms Gali.OpenEconomy.Preferences.cpi_rpow
#print axioms Gali.OpenEconomy.Preferences.shares_sum
#print axioms Gali.OpenEconomy.Preferences.demand_term
#print axioms Gali.OpenEconomy.Preferences.spend_term
#print axioms Gali.OpenEconomy.Preferences.expenditure_demand
#print axioms Gali.OpenEconomy.Preferences.cesIndex_rpow
#print axioms Gali.OpenEconomy.Preferences.cesIndex_demand
#print axioms Gali.OpenEconomy.Preferences.cesIndex_pos
#print axioms Gali.OpenEconomy.Preferences.expenditure_core
#print axioms Gali.OpenEconomy.Preferences.expenditure_ge
#print axioms Gali.OpenEconomy.Preferences.expenditure_eq_iff
#print axioms Gali.OpenEconomy.Preferences.cesIndex_zero
#print axioms Gali.OpenEconomy.Preferences.expenditure_ge_of_one_lt
#print axioms Gali.OpenEconomy.Preferences.expenditure_eq_iff_of_one_lt
#print axioms Gali.OpenEconomy.Preferences.demands_pos
#print axioms Gali.OpenEconomy.Preferences.cpi_isLeast
#print axioms Gali.OpenEconomy.Preferences.cesIndex_le_of_spend
#print axioms Gali.OpenEconomy.Preferences.importShare
#print axioms Gali.OpenEconomy.Preferences.importShare_of_eq
#print axioms Gali.OpenEconomy.Preferences.powerMean_tendsto
#print axioms Gali.OpenEconomy.Preferences.cesIndex_tendsto_cd
#print axioms Gali.OpenEconomy.Preferences.cpi_tendsto_cd
#print axioms Gali.OpenEconomy.Preferences.cesIndexCD_demand
#print axioms Gali.OpenEconomy.Preferences.expenditureCD_demand
#print axioms Gali.OpenEconomy.Preferences.cpiCD_mul_cesIndexCD
#print axioms Gali.OpenEconomy.Preferences.expenditureCD_ge
#print axioms Gali.OpenEconomy.Preferences.expenditureCD_eq_iff
#print axioms Gali.OpenEconomy.Preferences.Variety.priceIndex
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg
#print axioms Gali.OpenEconomy.Preferences.Variety.demand
#print axioms Gali.OpenEconomy.Preferences.Variety.r_add_inv
#print axioms Gali.OpenEconomy.Preferences.Variety.young_key
#print axioms Gali.OpenEconomy.Preferences.Variety.young_le
#print axioms Gali.OpenEconomy.Preferences.Variety.young_eq_iff
#print axioms Gali.OpenEconomy.Preferences.Variety.priceIndex_pos
#print axioms Gali.OpenEconomy.Preferences.Variety.priceIndex_rpow
#print axioms Gali.OpenEconomy.Preferences.Variety.integral_relPrice_rpow
#print axioms Gali.OpenEconomy.Preferences.Variety.integrable_relPrice_rpow
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg_demand
#print axioms Gali.OpenEconomy.Preferences.Variety.price_mul_demand
#print axioms Gali.OpenEconomy.Preferences.Variety.spend_demand
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg_nonneg
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg_rpow
#print axioms Gali.OpenEconomy.Preferences.Variety.integrated_young
#print axioms Gali.OpenEconomy.Preferences.Variety.spend_ge
#print axioms Gali.OpenEconomy.Preferences.Variety.spend_eq_iff
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg_le_of_spend
#print axioms Gali.OpenEconomy.Preferences.Variety.cesAgg_eq_iff_of_spend
#print axioms Gali.OpenEconomy.Preferences.Variety.integral_pos_of_pos
#print axioms Gali.OpenEconomy.Preferences.Variety.unitInterval_ne_zero
#print axioms Gali.OpenEconomy.Preferences.Variety.unitInterval_expenditure_minimisation
#print axioms Gali.OpenEconomy.Preferences.Variety.two_stage_expenditure
#print axioms Gali.OpenEconomy.Identities.cpi_homog
#print axioms Gali.OpenEconomy.Identities.cpiGap
#print axioms Gali.OpenEconomy.Identities.log_cpi_eq
#print axioms Gali.OpenEconomy.Identities.cpiGap_eq
#print axioms Gali.OpenEconomy.Identities.cpiGap_zero
#print axioms Gali.OpenEconomy.Identities.hasDerivAt_cpiGap
#print axioms Gali.OpenEconomy.Identities.hasFDerivAt_logCPI
#print axioms Gali.OpenEconomy.Identities.log_cpiCD_eq
#print axioms Gali.OpenEconomy.Identities.cpi_inflation
#print axioms Gali.OpenEconomy.Identities.hasFDerivAt_inflationGap
#print axioms Gali.OpenEconomy.Identities.cpi_inflation_cd
#print axioms Gali.OpenEconomy.Identities.tot_lop
#print axioms Gali.OpenEconomy.Identities.rerGap
#print axioms Gali.OpenEconomy.Identities.rer_eq
#print axioms Gali.OpenEconomy.Identities.hasDerivAt_rerGap
#print axioms Gali.OpenEconomy.Identities.rer_cd
#print axioms Gali.OpenEconomy.RiskSharing.periodUtility
#print axioms Gali.OpenEconomy.RiskSharing.hasDerivAt_periodUtility
#print axioms Gali.OpenEconomy.RiskSharing.periodUtility_tangent
#print axioms Gali.OpenEconomy.RiskSharing.nodeObjective
#print axioms Gali.OpenEconomy.RiskSharing.NodeFeasible
#print axioms Gali.OpenEconomy.RiskSharing.ArrowFOC
#print axioms Gali.OpenEconomy.RiskSharing.arrow_foc_of_optimal
#print axioms Gali.OpenEconomy.RiskSharing.optimal_of_arrow_foc
#print axioms Gali.OpenEconomy.RiskSharing.arrow_optimal_iff
#print axioms Gali.OpenEconomy.RiskSharing.arrow_sdf_iff
#print axioms Gali.OpenEconomy.RiskSharing.portfolio_price
#print axioms Gali.OpenEconomy.RiskSharing.bond_price
#print axioms Gali.OpenEconomy.RiskSharing.bond_price_expectation
#print axioms Gali.OpenEconomy.RiskSharing.foreign_optimal_iff
#print axioms Gali.OpenEconomy.RiskSharing.foreign_sdf_iff
#print axioms Gali.OpenEconomy.RiskSharing.rsRatio
#print axioms Gali.OpenEconomy.RiskSharing.riskSharing_ratio_const
#print axioms Gali.OpenEconomy.RiskSharing.vartheta
#print axioms Gali.OpenEconomy.RiskSharing.riskSharing
#print axioms Gali.OpenEconomy.RiskSharing.vartheta_eq_one
#print axioms Gali.OpenEconomy.RiskSharing.riskSharing_log
#print axioms Gali.OpenEconomy.RiskSharing.riskSharing_log_tot
#print axioms Gali.OpenEconomy.RiskSharing.riskSharing_log_cd
#print axioms Gali.OpenEconomy.UIP.uip_exact
#print axioms Gali.OpenEconomy.UIP.uipGap
#print axioms Gali.OpenEconomy.UIP.uip_node_iff
#print axioms Gali.OpenEconomy.UIP.uipGap_zero
#print axioms Gali.OpenEconomy.UIP.uipGap_const
#print axioms Gali.OpenEconomy.UIP.expectDe
#print axioms Gali.OpenEconomy.UIP.expectDe_apply
#print axioms Gali.OpenEconomy.UIP.hasFDerivAt_uipGap
#print axioms Gali.OpenEconomy.UIP.tot_difference
#print axioms Gali.OpenEconomy.UIP.forward_partial
#print axioms Gali.OpenEconomy.UIP.forward_iff
#print axioms Gali.OpenEconomy.UIP.tot_forward
#print axioms Gali.OpenEconomy.UIP.forward_counterexample
#print axioms Gali.OpenEconomy.UIP.tot_difference_of_eulers
#print axioms Gali.OpenEconomy.AggregateDemand.varpi
#print axioms Gali.OpenEconomy.AggregateDemand.Phi
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU
#print axioms Gali.OpenEconomy.AggregateDemand.varpi_sub_one
#print axioms Gali.OpenEconomy.AggregateDemand.one_add_mul_varpi
#print axioms Gali.OpenEconomy.AggregateDemand.one_add_mul_varpi_pos
#print axioms Gali.OpenEconomy.AggregateDemand.Phi_pos
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU_pos
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU_mul
#print axioms Gali.OpenEconomy.AggregateDemand.one_lt_varpi
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU_zero
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU_of_sigma_mul_eta
#print axioms Gali.OpenEconomy.AggregateDemand.sigmaU_strictAntiOn
#print axioms Gali.OpenEconomy.AggregateDemand.convex_comb_pos
#print axioms Gali.OpenEconomy.AggregateDemand.cpi_self
#print axioms Gali.OpenEconomy.AggregateDemand.cpiCD_self
#print axioms Gali.OpenEconomy.AggregateDemand.exports_eq
#print axioms Gali.OpenEconomy.AggregateDemand.trade_balanced_ss
#print axioms Gali.OpenEconomy.AggregateDemand.netExports_ss
#print axioms Gali.OpenEconomy.AggregateDemand.eq24
#print axioms Gali.OpenEconomy.AggregateDemand.logOutput
#print axioms Gali.OpenEconomy.AggregateDemand.log_eq24
#print axioms Gali.OpenEconomy.AggregateDemand.eq25Map
#print axioms Gali.OpenEconomy.AggregateDemand.eq25Map_apply
#print axioms Gali.OpenEconomy.AggregateDemand.logOutput_ss
#print axioms Gali.OpenEconomy.AggregateDemand.eq25
#print axioms Gali.OpenEconomy.AggregateDemand.eq25_ces
#print axioms Gali.OpenEconomy.AggregateDemand.eq25_cd
#print axioms Gali.OpenEconomy.AggregateDemand.eq27
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef
#print axioms Gali.OpenEconomy.AggregateDemand.eq31
#print axioms Gali.OpenEconomy.AggregateDemand.netExports
#print axioms Gali.OpenEconomy.AggregateDemand.netExports_eq
#print axioms Gali.OpenEconomy.AggregateDemand.nxMap
#print axioms Gali.OpenEconomy.AggregateDemand.nxMap_apply
#print axioms Gali.OpenEconomy.AggregateDemand.hasFDerivAt_netExports
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef_eq_zero
#print axioms Gali.OpenEconomy.AggregateDemand.eq31_unit
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef_one_nonpos
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef_counterexample
#print axioms Gali.OpenEconomy.AggregateDemand.not_large_openness_improves
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef_eventually_pos
#print axioms Gali.OpenEconomy.AggregateDemand.nxCoef_pos_iff
#print axioms Gali.OpenEconomy.AggregateDemand.eq26
#print axioms Gali.OpenEconomy.AggregateDemand.eq27_proc
#print axioms Gali.OpenEconomy.AggregateDemand.key_eq26_eq28
#print axioms Gali.OpenEconomy.AggregateDemand.eq26_iff_eq28
#print axioms Gali.OpenEconomy.AggregateDemand.natRate
#print axioms Gali.OpenEconomy.AggregateDemand.eq28_iff_eq29
#print axioms Gali.OpenEconomy.Supply.dispersion
#print axioms Gali.OpenEconomy.Supply.bigTheta
#print axioms Gali.OpenEconomy.Supply.crossVar
#print axioms Gali.OpenEconomy.Supply.employment_level
#print axioms Gali.OpenEconomy.Supply.employment_identity
#print axioms Gali.OpenEconomy.Supply.integrable_exp_mul
#print axioms Gali.OpenEconomy.Supply.interior_integrableExpSet
#print axioms Gali.OpenEconomy.Supply.cgf_taylor
#print axioms Gali.OpenEconomy.Supply.cgf_taylor_comp
#print axioms Gali.OpenEconomy.Supply.priceIndex_family
#print axioms Gali.OpenEconomy.Supply.dispersion_family_eq
#print axioms Gali.OpenEconomy.Supply.crossVar_family
#print axioms Gali.OpenEconomy.Supply.dispersion_second_order
#print axioms Gali.OpenEconomy.Supply.dispersion_family_isBigO_sq
#print axioms Gali.OpenEconomy.Supply.dispersion_family_first_order
#print axioms Gali.OpenEconomy.Supply.eq32_exact
#print axioms Gali.OpenEconomy.Supply.eq32
#print axioms Gali.OpenEconomy.Supply.eq33
#print axioms Gali.OpenEconomy.Supply.kappa
#print axioms Gali.OpenEconomy.Supply.eq34
#print axioms Gali.OpenEconomy.Supply.natDen
#print axioms Gali.OpenEconomy.Supply.GammaA
#print axioms Gali.OpenEconomy.Supply.GammaStar
#print axioms Gali.OpenEconomy.Supply.GammaZ
#print axioms Gali.OpenEconomy.Supply.natDen_pos
#print axioms Gali.OpenEconomy.Supply.GammaA_pos
#print axioms Gali.OpenEconomy.Supply.sigma_sub_eq_sigmaU
#print axioms Gali.OpenEconomy.Supply.mul_GammaA
#print axioms Gali.OpenEconomy.Supply.mul_GammaStar
#print axioms Gali.OpenEconomy.Supply.mul_GammaZ
#print axioms Gali.OpenEconomy.Supply.markup_natural
#print axioms Gali.OpenEconomy.Supply.eq35_iff
#print axioms Gali.OpenEconomy.Supply.GammaStar_unit
#print axioms Gali.OpenEconomy.Supply.GammaZ_unit_neg
#print axioms Gali.OpenEconomy.Supply.GammaZ_zero
#print axioms Gali.OpenEconomy.Supply.GammaStar_zero
#print axioms Gali.OpenEconomy.Supply.sgap_eq
#print axioms Gali.OpenEconomy.Supply.eq36
#print axioms Gali.OpenEconomy.Supply.kappaU
#print axioms Gali.OpenEconomy.Supply.eq37
#print axioms Gali.OpenEconomy.Supply.kappaU_zero
#print axioms Gali.OpenEconomy.Supply.kappaU_unit
#print axioms Gali.OpenEconomy.Supply.kappaU_strictAntiOn
#print axioms Gali.OpenEconomy.Supply.PsiStar
#print axioms Gali.OpenEconomy.Supply.PsiZ
#print axioms Gali.OpenEconomy.Supply.eq38
#print axioms Gali.OpenEconomy.Supply.PsiStar_zero
#print axioms Gali.OpenEconomy.Supply.PsiZ_zero
#print axioms Gali.OpenEconomy.Supply.continuousAt_sigmaU
#print axioms Gali.OpenEconomy.Supply.tendsto_PsiStar
#print axioms Gali.OpenEconomy.Supply.tendsto_PsiZ
#print axioms Gali.OpenEconomy.TaylorRule.kappaU_pos
#print axioms Gali.OpenEconomy.TaylorRule.kappaU_of_mul_eq_one
#print axioms Gali.OpenEconomy.TaylorRule.realRate
#print axioms Gali.OpenEconomy.TaylorRule.NKPC
#print axioms Gali.OpenEconomy.TaylorRule.DISGap
#print axioms Gali.OpenEconomy.TaylorRule.InterestRule
#print axioms Gali.OpenEconomy.TaylorRule.InterestRuleGap
#print axioms Gali.OpenEconomy.TaylorRule.taylorRule_iff_gap
#print axioms Gali.OpenEconomy.TaylorRule.shockU
#print axioms Gali.OpenEconomy.TaylorRule.Equilibrium
#print axioms Gali.OpenEconomy.TaylorRule.Structural
#print axioms Gali.OpenEconomy.TaylorRule.omegaU
#print axioms Gali.OpenEconomy.TaylorRule.AU
#print axioms Gali.OpenEconomy.TaylorRule.BU
#print axioms Gali.OpenEconomy.TaylorRule.stack
#print axioms Gali.OpenEconomy.TaylorRule.forcing
#print axioms Gali.OpenEconomy.TaylorRule.nk_iff_structural
#print axioms Gali.OpenEconomy.TaylorRule.structural_iff_solves
#print axioms Gali.OpenEconomy.TaylorRule.equilibrium_iff_solves
#print axioms Gali.OpenEconomy.TaylorRule.tr2_AU
#print axioms Gali.OpenEconomy.TaylorRule.det2_AU
#print axioms Gali.OpenEconomy.TaylorRule.schurStable_AU_iff
#print axioms Gali.OpenEconomy.TaylorRule.determinate_iff_41
#print axioms Gali.OpenEconomy.TaylorRule.determinate_iff_41_primitives
#print axioms Gali.OpenEconomy.TaylorRule.boundedVec_stack
#print axioms Gali.OpenEconomy.TaylorRule.adaptedVec_stack
#print axioms Gali.OpenEconomy.TaylorRule.equilibrium_unique
#print axioms Gali.OpenEconomy.TaylorRule.equilibrium_not_unique
#print axioms Gali.OpenEconomy.TaylorRule.msvDen
#print axioms Gali.OpenEconomy.TaylorRule.msvLambda
#print axioms Gali.OpenEconomy.TaylorRule.msvPsiY
#print axioms Gali.OpenEconomy.TaylorRule.msvPsiPi
#print axioms Gali.OpenEconomy.TaylorRule.msvDen_eq
#print axioms Gali.OpenEconomy.TaylorRule.msvDen_pos
#print axioms Gali.OpenEconomy.TaylorRule.msvLambda_pos
#print axioms Gali.OpenEconomy.TaylorRule.isAR1_smul
#print axioms Gali.OpenEconomy.TaylorRule.boundedProc_smul
#print axioms Gali.OpenEconomy.TaylorRule.msv_structural
#print axioms Gali.OpenEconomy.TaylorRule.msv_unique
#print axioms Gali.OpenEconomy.TaylorRule.equilibrium_iff_msv
#print axioms Gali.OpenEconomy.TaylorRule.monYgapCoef
#print axioms Gali.OpenEconomy.TaylorRule.monInflCoef
#print axioms Gali.OpenEconomy.TaylorRule.monRealCoef
#print axioms Gali.OpenEconomy.TaylorRule.monNomCoef
#print axioms Gali.OpenEconomy.TaylorRule.monRealCoef_eq_book
#print axioms Gali.OpenEconomy.TaylorRule.monNomCoef_eq_book
#print axioms Gali.OpenEconomy.TaylorRule.monRealCoef_pos
#print axioms Gali.OpenEconomy.TaylorRule.monetary_shock
#print axioms Gali.OpenEconomy.TaylorRule.monetary_signs
#print axioms Gali.OpenEconomy.TaylorRule.monetary_tot
#print axioms Gali.OpenEconomy.TaylorRule.monetary_exchangeRate
#print axioms Gali.OpenEconomy.TaylorRule.priceLevel_sum
#print axioms Gali.OpenEconomy.TaylorRule.expected_priceLevel
#print axioms Gali.OpenEconomy.TaylorRule.expected_inflation_hasSum
#print axioms Gali.OpenEconomy.TaylorRule.expected_inflation_tsum
#print axioms Gali.OpenEconomy.TaylorRule.priceLevel_longRun
#print axioms Gali.OpenEconomy.TaylorRule.eImpact
#print axioms Gali.OpenEconomy.TaylorRule.eLongRun
#print axioms Gali.OpenEconomy.TaylorRule.exchangeRate_impact
#print axioms Gali.OpenEconomy.TaylorRule.exchangeRate_longRun_change
#print axioms Gali.OpenEconomy.TaylorRule.overshoot_iff
#print axioms Gali.OpenEconomy.TaylorRule.overshoot_iff_nominal_rises
#print axioms Gali.OpenEconomy.TaylorRule.lambdaV
#print axioms Gali.OpenEconomy.TaylorRule.msvDen_affine
#print axioms Gali.OpenEconomy.TaylorRule.lambdaV_lt_of_slope_pos
#print axioms Gali.OpenEconomy.TaylorRule.lambdaV_strictMonoOn
#print axioms Gali.OpenEconomy.TaylorRule.lambdaV_lt_of_slope_neg
#print axioms Gali.OpenEconomy.TaylorRule.counterexample_sigmaU_le
#print axioms Gali.OpenEconomy.TaylorRule.counterexample_strictAntiOn
#print axioms Gali.OpenEconomy.TaylorRule.counterexample_values
#print axioms Gali.OpenEconomy.TaylorRule.printed_monotonicity_false
#print axioms Gali.OpenEconomy.TaylorRule.closed_economy_equivalence
#print axioms Gali.OpenEconomy.TaylorRule.closed_economy_responses
#print axioms Gali.OpenEconomy.TaylorRule.sigma_eta_one
#print axioms Gali.OpenEconomy.OptimalPolicy.tot
#print axioms Gali.OpenEconomy.OptimalPolicy.relPrices_cpi
#print axioms Gali.OpenEconomy.OptimalPolicy.consumption_possibilities
#print axioms Gali.OpenEconomy.OptimalPolicy.log_consumption
#print axioms Gali.OpenEconomy.OptimalPolicy.frontierC
#print axioms Gali.OpenEconomy.OptimalPolicy.plannerWelfare
#print axioms Gali.OpenEconomy.OptimalPolicy.optEmployment
#print axioms Gali.OpenEconomy.OptimalPolicy.log_frontierC
#print axioms Gali.OpenEconomy.OptimalPolicy.frontierC_pos
#print axioms Gali.OpenEconomy.OptimalPolicy.hasDerivAt_frontier
#print axioms Gali.OpenEconomy.OptimalPolicy.hasDerivAt_plannerWelfare
#print axioms Gali.OpenEconomy.OptimalPolicy.optEmployment_rpow
#print axioms Gali.OpenEconomy.OptimalPolicy.optEmployment_pos
#print axioms Gali.OpenEconomy.OptimalPolicy.foc_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.plannerWelfare_le
#print axioms Gali.OpenEconomy.OptimalPolicy.planner_optimal_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.planner_existsUnique
#print axioms Gali.OpenEconomy.OptimalPolicy.markupH
#print axioms Gali.OpenEconomy.OptimalPolicy.printedFirstLine
#print axioms Gali.OpenEconomy.OptimalPolicy.markup_eq
#print axioms Gali.OpenEconomy.OptimalPolicy.printedFirstLine_eq
#print axioms Gali.OpenEconomy.OptimalPolicy.printedFirstLine_eq_markup_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.desiredMarkup
#print axioms Gali.OpenEconomy.OptimalPolicy.one_lt_desiredMarkup
#print axioms Gali.OpenEconomy.OptimalPolicy.flexEmployment_eq_opt_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.flex_optimal
#print axioms Gali.OpenEconomy.OptimalPolicy.optSubsidy
#print axioms Gali.OpenEconomy.OptimalPolicy.subsidy_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.optSubsidy_lt_closed
#print axioms Gali.OpenEconomy.OptimalPolicy.optSubsidy_neg_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.optSubsidy_calibration
#print axioms Gali.OpenEconomy.OptimalPolicy.DIS
#print axioms Gali.OpenEconomy.OptimalPolicy.Equilibrium
#print axioms Gali.OpenEconomy.OptimalPolicy.zero_equilibrium_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.inflH_zero_of_gap_zero
#print axioms Gali.OpenEconomy.OptimalPolicy.gap_zero_of_inflH_zero
#print axioms Gali.OpenEconomy.OptimalPolicy.divine_coincidence
#print axioms Gali.OpenEconomy.OptimalPolicy.pathLoss
#print axioms Gali.OpenEconomy.OptimalPolicy.pathLoss_summable
#print axioms Gali.OpenEconomy.OptimalPolicy.pathLoss_nonneg
#print axioms Gali.OpenEconomy.OptimalPolicy.pathLoss_zero
#print axioms Gali.OpenEconomy.OptimalPolicy.pathLoss_eq_zero_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.optimal_policy
#print axioms Gali.OpenEconomy.OptimalPolicy.TaylorRule
#print axioms Gali.OpenEconomy.OptimalPolicy.nk_iff_solves
#print axioms Gali.OpenEconomy.OptimalPolicy.equilibrium_iff_zero
#print axioms Gali.OpenEconomy.OptimalPolicy.rule42_unique
#print axioms Gali.OpenEconomy.OptimalPolicy.rule42_not_determinate
#print axioms Gali.OpenEconomy.OptimalPolicy.AO
#print axioms Gali.OpenEconomy.OptimalPolicy.nk_iff_solves_exog
#print axioms Gali.OpenEconomy.OptimalPolicy.not_schurStable_AO
#print axioms Gali.OpenEconomy.OptimalPolicy.exogRule_not_determinate
#print axioms Gali.OpenEconomy.OptimalPolicy.exogRule_not_unique
#print axioms Gali.OpenEconomy.OptimalPolicy.one_add_mul_varpi_pos_of_lt_one
#print axioms Gali.OpenEconomy.OptimalPolicy.Phi_pos_of_lt_one
#print axioms Gali.OpenEconomy.OptimalPolicy.sigmaU_pos_of_lt_one
#print axioms Gali.OpenEconomy.OptimalPolicy.natDen_pos_of_lt_one
#print axioms Gali.OpenEconomy.OptimalPolicy.inv_Phi_sub_one
#print axioms Gali.OpenEconomy.OptimalPolicy.markup_eq33
#print axioms Gali.OpenEconomy.OptimalPolicy.natural_output_iff
#print axioms Gali.OpenEconomy.OptimalPolicy.GammaA_pos_of_lt_one
#print axioms Gali.OpenEconomy.OptimalPolicy.natural_tot_eq
#print axioms Gali.OpenEconomy.OptimalPolicy.tot_tech_coeff_pos
#print axioms Gali.OpenEconomy.OptimalPolicy.tot_pref_coeff_neg
#print axioms Gali.OpenEconomy.OptimalPolicy.special_case
#print axioms Gali.OpenEconomy.OptimalPolicy.dit_exchange_rate_cpi
#print axioms Gali.OpenEconomy.Welfare.logPriceIndex_second_order
#print axioms Gali.OpenEconomy.Welfare.bigO_mul
#print axioms Gali.OpenEconomy.Welfare.bigO_weaken
#print axioms Gali.OpenEconomy.Welfare.tendsto_zero_of_bigO
#print axioms Gali.OpenEconomy.Welfare.taylor_two
#print axioms Gali.OpenEconomy.Welfare.exp_taylor_two
#print axioms Gali.OpenEconomy.Welfare.exp_sub_one_bigO
#print axioms Gali.OpenEconomy.Welfare.GoodDist
#print axioms Gali.OpenEconomy.Welfare.crossMean
#print axioms Gali.OpenEconomy.Welfare.crossVarDist
#print axioms Gali.OpenEconomy.Welfare.calvoMix
#print axioms Gali.OpenEconomy.Welfare.integral_calvoMix
#print axioms Gali.OpenEconomy.Welfare.crossVarDist_eq
#print axioms Gali.OpenEconomy.Welfare.calvoMix_good
#print axioms Gali.OpenEconomy.Welfare.calvoMix_mean
#print axioms Gali.OpenEconomy.Welfare.calvoMix_var
#print axioms Gali.OpenEconomy.Welfare.calvoMix_var_meanChange
#print axioms Gali.OpenEconomy.Welfare.calvo_good
#print axioms Gali.OpenEconomy.Welfare.calvo_var_recursion
#print axioms Gali.OpenEconomy.Welfare.lemma2_partial
#print axioms Gali.OpenEconomy.Welfare.lemma2_nonneg
#print axioms Gali.OpenEconomy.Welfare.lemma2_hasSum
#print axioms Gali.OpenEconomy.Welfare.lemma2
#print axioms Gali.OpenEconomy.Welfare.lemma2_calvo_inherited
#print axioms Gali.OpenEconomy.Welfare.lemma2_calvo
#print axioms Gali.OpenEconomy.Welfare.inflation_sub_meanChange
#print axioms Gali.OpenEconomy.Welfare.inflation_sq_sub_meanChange_sq
#print axioms Gali.OpenEconomy.Welfare.lambdaH
#print axioms Gali.OpenEconomy.Welfare.periodUtility
#print axioms Gali.OpenEconomy.Welfare.marginal_utilities
#print axioms Gali.OpenEconomy.Welfare.efficiency_iff
#print axioms Gali.OpenEconomy.Welfare.utility_exact
#print axioms Gali.OpenEconomy.Welfare.consumption_logdev
#print axioms Gali.OpenEconomy.Welfare.secondOrder_eq
#print axioms Gali.OpenEconomy.Welfare.gap_form
#print axioms Gali.OpenEconomy.Welfare.period_utility_second_order
#print axioms Gali.OpenEconomy.Welfare.welfare_sign
#print axioms Gali.OpenEconomy.Welfare.appendix_sign_error
#print axioms Gali.OpenEconomy.Welfare.lemma2_printed_fails
#print axioms Gali.OpenEconomy.Welfare.periodLoss43
#print axioms Gali.OpenEconomy.Welfare.loss43
#print axioms Gali.OpenEconomy.Welfare.inflWeight_of_dispersion
#print axioms Gali.OpenEconomy.Welfare.welfare_eq_loss43
#print axioms Gali.OpenEconomy.Welfare.loss43_weights_pos
#print axioms Gali.OpenEconomy.Welfare.loss43_eq_pathLoss
#print axioms Gali.OpenEconomy.Welfare.avgLoss44
#print axioms Gali.OpenEconomy.Welfare.welfare_stationary44
#print axioms Gali.OpenEconomy.Welfare.closed_economy_weights
#print axioms Gali.OpenEconomy.Welfare.gap_eq_employment
#print axioms Gali.OpenEconomy.SimpleRules.SDIT
#print axioms Gali.OpenEconomy.SimpleRules.SCIT
#print axioms Gali.OpenEconomy.SimpleRules.PEG
#print axioms Gali.OpenEconomy.SimpleRules.TaylorType
#print axioms Gali.OpenEconomy.SimpleRules.FDIT
#print axioms Gali.OpenEconomy.SimpleRules.FCIT
#print axioms Gali.OpenEconomy.SimpleRules.UIP
#print axioms Gali.OpenEconomy.SimpleRules.peg_rate
#print axioms Gali.OpenEconomy.SimpleRules.lambda_calibration
#print axioms Gali.OpenEconomy.SimpleRules.tableLoss
#print axioms Gali.OpenEconomy.SimpleRules.tableLoss_eq_avgLoss44
#print axioms Gali.OpenEconomy.SimpleRules.tableLoss_values
#print axioms Gali.OpenEconomy.SimpleRules.tableLoss_consistent
#print axioms Gali.OpenEconomy.SimpleRules.tableLossNoTheta
#print axioms Gali.OpenEconomy.SimpleRules.tableLoss_noTheta_inconsistent
#print axioms Gali.OpenEconomy.SimpleRules.tot_eq_output
#print axioms Gali.OpenEconomy.SimpleRules.sdInflH
#print axioms Gali.OpenEconomy.SimpleRules.sdGap
#print axioms Gali.OpenEconomy.SimpleRules.peg_not_most_volatile_inflation
#print axioms Gali.OpenEconomy.SimpleRules.peg_most_volatile_strict
#print axioms Gali.OpenEconomy.SimpleRules.peg_most_volatile_gap
#print axioms Gali.OpenEconomy.SimpleRules.world_output_effects
#print axioms Gali.OpenEconomy.SimpleRules.exchange_rate_identity
#print axioms Gali.OpenEconomy.SimpleRules.sdit_meanReverting
#print axioms Gali.OpenEconomy.SimpleRules.scit_meanReverting
#print axioms Gali.OpenEconomy.SimpleRules.peg_meanReverting
#print axioms Gali.OpenEconomy.SimpleRules.natRate
#print axioms Gali.OpenEconomy.SimpleRules.bigLambda
#print axioms Gali.OpenEconomy.SimpleRules.fdit_solution
#print axioms Gali.OpenEconomy.SimpleRules.fdit_unique
#print axioms Gali.OpenEconomy.SimpleRules.fdit_coeff_neg
#print axioms Gali.OpenEconomy.SimpleRules.fdit_unit_root
#print axioms Gali.OpenEconomy.SimpleRules.fdit_permanent_shift
#print axioms Gali.OpenEconomy.SimpleRules.fcit_cumulative
#print axioms Gali.OpenEconomy.Ex8_1.profit
#print axioms Gali.OpenEconomy.Ex8_1.firm_optimum_iff
#print axioms Gali.OpenEconomy.Ex8_1.profit_zero
#print axioms Gali.OpenEconomy.Ex8_1.firm_log_iff
#print axioms Gali.OpenEconomy.Ex8_1.disutilN
#print axioms Gali.OpenEconomy.Ex8_1.periodUtility
#print axioms Gali.OpenEconomy.Ex8_1.hasDerivAt_disutilN
#print axioms Gali.OpenEconomy.Ex8_1.le_tangent
#print axioms Gali.OpenEconomy.Ex8_1.disutilN_tangent_le
#print axioms Gali.OpenEconomy.Ex8_1.static_foc_necessary
#print axioms Gali.OpenEconomy.Ex8_1.static_isLocalMax_of_optimal
#print axioms Gali.OpenEconomy.Ex8_1.static_foc_sufficient
#print axioms Gali.OpenEconomy.Ex8_1.household_optimum_iff
#print axioms Gali.OpenEconomy.Ex8_1.labour_supply_log_iff
#print axioms Gali.OpenEconomy.Ex8_1.budget_tradeBalance
#print axioms Gali.OpenEconomy.Ex8_1.tradeBalance_log_iff
#print axioms Gali.OpenEconomy.Ex8_1.tot_of_marketClearing
#print axioms Gali.OpenEconomy.Ex8_1.tot_log_iff
#print axioms Gali.OpenEconomy.Ex8_1.micro_iff
#print axioms Gali.OpenEconomy.Ex8_1.tradeBalance_log
#print axioms Gali.OpenEconomy.Ex8_1.StaticEq
#print axioms Gali.OpenEconomy.Ex8_1.denom
#print axioms Gali.OpenEconomy.Ex8_1.outputSol
#print axioms Gali.OpenEconomy.Ex8_1.denom_pos
#print axioms Gali.OpenEconomy.Ex8_1.consumption_eq
#print axioms Gali.OpenEconomy.Ex8_1.staticEq_iff
#print axioms Gali.OpenEconomy.Ex8_1.staticEq_existsUnique
#print axioms Gali.OpenEconomy.Ex8_1.outputSol_sigma_one
#print axioms Gali.OpenEconomy.Ex8_1.outputSol_indep_iff
#print axioms Gali.OpenEconomy.Ex8_1.outputSol_ystar_slope
#print axioms Gali.OpenEconomy.Ex8_1.outputSol_a_slope_pos
#print axioms Gali.OpenEconomy.Ex8_1.money_neutral_real
#print axioms Gali.OpenEconomy.Ex8_1.exchangeRate_one_for_one
#print axioms Gali.OpenEconomy.Ex8_1.Equilibrium
#print axioms Gali.OpenEconomy.Ex8_1.equilibrium_iff
#print axioms Gali.OpenEconomy.Ex8_1.peg_iff
#print axioms Gali.OpenEconomy.Ex8_1.peg_existsUnique
#print axioms Gali.OpenEconomy.Ex8_1.peg_same_real_allocation
#print axioms Gali.OpenEconomy.Ex8_1.pegEquilibrium_iff
#print axioms Gali.OpenEconomy.Ex8_2.lagP
#print axioms Gali.OpenEconomy.Ex8_2.natRate
#print axioms Gali.OpenEconomy.Ex8_2.Block
#print axioms Gali.OpenEconomy.Ex8_2.TaylorEq
#print axioms Gali.OpenEconomy.Ex8_2.PegEq
#print axioms Gali.OpenEconomy.Ex8_2.known_pm1
#print axioms Gali.OpenEconomy.Ex8_2.cumsum_iff
#print axioms Gali.OpenEconomy.Ex8_2.shock
#print axioms Gali.OpenEconomy.Ex8_2.nk_iff_structural
#print axioms Gali.OpenEconomy.Ex8_2.taylor_determinate_iff
#print axioms Gali.OpenEconomy.Ex8_2.taylor_iff
#print axioms Gali.OpenEconomy.Ex8_2.taylor_exists
#print axioms Gali.OpenEconomy.Ex8_2.taylor_unique
#print axioms Gali.OpenEconomy.Ex8_2.lambda_mul_den
#print axioms Gali.OpenEconomy.Ex8_2.taylor_closed_forms_38
#print axioms Gali.OpenEconomy.Ex8_2.taylor_signs_38
#print axioms Gali.OpenEconomy.Ex8_2.taylor_irf_38
#print axioms Gali.OpenEconomy.Ex8_2.taylor_irf_tendsto
#print axioms Gali.OpenEconomy.Ex8_2.charQ
#print axioms Gali.OpenEconomy.Ex8_2.exists_root
#print axioms Gali.OpenEconomy.Ex8_2.root_unique
#print axioms Gali.OpenEconomy.Ex8_2.other_root
#print axioms Gali.OpenEconomy.Ex8_2.peg_nkpc_iff
#print axioms Gali.OpenEconomy.Ex8_2.wseq
#print axioms Gali.OpenEconomy.Ex8_2.pegShock
#print axioms Gali.OpenEconomy.Ex8_2.pegTheta
#print axioms Gali.OpenEconomy.Ex8_2.pegTheta_eq
#print axioms Gali.OpenEconomy.Ex8_2.pegP
#print axioms Gali.OpenEconomy.Ex8_2.pegP_iff
#print axioms Gali.OpenEconomy.Ex8_2.pegP_closed
#print axioms Gali.OpenEconomy.Ex8_2.pegP_adapted
#print axioms Gali.OpenEconomy.Ex8_2.pegP_bounded
#print axioms Gali.OpenEconomy.Ex8_2.theta_solves
#print axioms Gali.OpenEconomy.Ex8_2.peg_iff
#print axioms Gali.OpenEconomy.Ex8_2.peg_exists
#print axioms Gali.OpenEconomy.Ex8_2.peg_unique
#print axioms Gali.OpenEconomy.Ex8_2.peg_rate_38
#print axioms Gali.OpenEconomy.Ex8_2.pegTheta_neg
#print axioms Gali.OpenEconomy.Ex8_2.peg_irf_signs
