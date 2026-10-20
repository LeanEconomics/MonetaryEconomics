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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
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

namespace Cochrane.AssetsRulesBalanceSheets

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

end Cochrane.AssetsRulesBalanceSheets

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

namespace Cochrane.AssetsRulesBalanceSheets

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

end Cochrane.AssetsRulesBalanceSheets

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

namespace Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree

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

end Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree

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

namespace Cochrane.AssetsRulesBalanceSheets.ForwardSolution

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

end Cochrane.AssetsRulesBalanceSheets.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Present values, transversality conditions and forward iteration

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.1, eqs. (8.1)–(8.2)
(pp. 239–240), and Chapter 9, §9.3.1–9.3.2 (pp. 265–266): the shared valuation machinery used by
the Chapter 8, 9 and 10 modules of this project.

Every valuation equation in these chapters has the same structure: a real value `x_t` obeys the
flow `x_t = s_t + β E_t x_{t+1}`, and iterating forward with a transversality condition gives
`x_t = E_t ∑ βʲ s_{t+j}`. This module proves that step once, in its expected form (for any
`ExpectationSystem`) and in its pathwise (ex post) form, together with the elementary price
uniqueness lemmas used throughout ("`B/P = V` determines `P`").

## Main results

* `epv`, `pv`: the ex post and expected present values (8.1)/(8.2); `pv_eq_forwardSeries`,
  `pv_bounded`.
* `TVC` (the transversality condition `βᵀ E_t x_{t+T} → 0`), `tvc_of_bounded`.
* `tendsto_partialSums_of_tvc`: flow plus TVC at `(t, ω)` gives convergence of the partial sums
  of `∑ βʲ E_t s_{t+j}` to `x_t` (no bound on `s` needed);
  `eq_forwardSeries_of_tvc`, `flow_tvc_iff_pv` (flow + TVC ⇔ `x = pv`), `eq_zero_of_tvc` (the
  homogeneous case: `X_t = β E_t X_{t+1}` plus TVC forces `X = 0`).
* Pathwise: `real_iterate`, `real_flow_tvc_iff`, `hasSum_of_tvc`, `summable_of_bounded`.
* Price uniqueness: `valuation_price_unique` (`B/P = V` with `B, V > 0`),
  `price_unique_of_strictMonoOn` (`b = s(P)` with `s` strictly increasing).
-/

namespace Cochrane.AssetsRulesBalanceSheets.PresentValue

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values -/

/-- Cochrane (2023), eq. (8.1), p. 239: the ex post discounted sum `∑_{j ≥ 0} βʲ s_{t+j}`,
state by state. -/
noncomputable def epv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), eq. (8.2), p. 240: the present value `E_t ∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (epv β s t)

/-- Cochrane (2023), eq. (8.2), p. 240: for bounded surpluses and `0 ≤ β < 1` the expectation
commutes with the sum, `E_t ∑ βʲ s_{t+j} = ∑ βʲ E_t s_{t+j}`. -/
theorem pv_eq_forwardSeries {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : pv 𝔼 β s t = 𝔼.forwardSeries β s t := by
  funext ω
  have hb : ∀ k ω', |β ^ k * s (t + k) ω'| ≤ β ^ k * M := fun k ω' => by
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + k) ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * s (t + k) ω') ω = ∑' k, β ^ k * 𝔼.E t (s (t + k)) ω
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • s (t + k)) ω = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (8.2), p. 240: the present value of bounded surpluses is bounded. -/
theorem pv_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : BoundedProc (pv 𝔼 β s) := by
  have h : pv 𝔼 β s = 𝔼.forwardSeries β s := funext (pv_eq_forwardSeries 𝔼 hβ0 hβ1 hs)
  rw [h]
  exact 𝔼.forwardSeries_bounded hβ0 hβ1 hs

/-! ### The transversality condition and forward iteration -/

/-- Cochrane (2023), p. 239 ("iterating forward"; survey E8.2): the transversality condition
`βᵀ E_t x_{t+T} → 0` for a real value process `x`, stated explicitly. -/
def TVC (β : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 239: a bounded value process satisfies the transversality condition. -/
theorem tvc_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (hx : BoundedProc x) : TVC 𝔼 β x := by
  obtain ⟨K, hK⟩ := hx
  intro t ω
  refine squeeze_zero_norm (a := fun T => β ^ T * K) (fun T => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK (t + T)) t ω) (pow_nonneg hβ0 T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K

/-- Cochrane (2023), eqs. (8.1)–(8.2), p. 239, and §9.2, p. 264 ("iterating forward"): if
`x_t = s_t + β E_t x_{t+1}` at every date with adapted `s`, and `βᵀ E_t x_{t+T} → 0` at `(t, ω)`,
then the partial sums of `∑ βʲ E_t s_{t+j}` converge to `x_t` at `ω`. No bound on `s` and no sign
of `β` is needed. -/
theorem tendsto_partialSums_of_tvc {β : ℝ} {s x : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hx : ForwardSolution.Solves 𝔼 β s x) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω)) := by
  have h1 : ∀ T, ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ T * 𝔼.E t (x (t + T)) ω := by
    intro T
    have h := congrFun (ForwardSolution.iterate_A15 𝔼 hsa hx t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    linarith
  simp_rw [h1]
  simpa using (tendsto_const_nhds (x := x t ω)).sub htvc

/-- Cochrane (2023), eq. (8.1), p. 239 (iterating forward): a solution of
`x_t = s_t + β E_t x_{t+1}` that satisfies the transversality condition is the forward sum
`∑ βʲ E_t s_{t+j}`. -/
theorem eq_forwardSeries_of_tvc {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s x : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hx : ForwardSolution.Solves 𝔼 β s x)
    (htvc : TVC 𝔼 β x) : x = 𝔼.forwardSeries β s := by
  funext t ω
  exact tendsto_nhds_unique (tendsto_partialSums_of_tvc 𝔼 hsa hx t ω (htvc t ω))
    (𝔼.forwardSeries_summable hβ0 hβ1 hs t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), eqs. (8.1)–(8.3), pp. 239–246 (the valuation equation from the flow
condition): for bounded adapted surpluses and `0 ≤ β < 1`, a value process satisfies the flow
`x_t = s_t + β E_t x_{t+1}` and the transversality condition if and only if
`x_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}` at every date. -/
theorem flow_tvc_iff_pv {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s x : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) :
    (ForwardSolution.Solves 𝔼 β s x ∧ TVC 𝔼 β x) ↔ x = pv 𝔼 β s := by
  have hpv : pv 𝔼 β s = 𝔼.forwardSeries β s := funext (pv_eq_forwardSeries 𝔼 hβ0 hβ1 hs)
  constructor
  · rintro ⟨hx, htvc⟩
    rw [hpv]
    exact eq_forwardSeries_of_tvc 𝔼 hβ0 hβ1 hs hsa hx htvc
  · intro hx
    rw [hx, hpv]
    exact ⟨fun t => 𝔼.forwardSeries_solves hβ0 hβ1 hs hsa t,
      tvc_of_bounded 𝔼 hβ0 hβ1 (𝔼.forwardSeries_bounded hβ0 hβ1 hs)⟩

/-- Cochrane (2023), p. 291 ("to avoid an explosion, a transversality-condition violation, both
sides must be zero"), and §9.2, p. 264: if `X_t = β E_t X_{t+1}` at every date and
`βᵀ E_t X_{t+T} → 0`, then `X_t = 0` at every date. -/
theorem eq_zero_of_tvc {β : ℝ} {X : ℕ → Ω → ℝ} (hX : ∀ t, X t = β • 𝔼.E t (X (t + 1)))
    (htvc : TVC 𝔼 β X) : ∀ t, X t = 0 := by
  have hsol : ForwardSolution.Solves 𝔼 β (fun _ => 0) X := fun t => by
    rw [hX t, add_zero]
  have hua : 𝔼.Adapted (fun _ : ℕ => (0 : Ω → ℝ)) := fun t => map_zero _
  intro t
  funext ω
  have h := tendsto_partialSums_of_tvc 𝔼 hua hsol t ω (htvc t ω)
  simp only [map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

/-! ### Pathwise iteration of a real flow -/

/-- Cochrane (2023), p. 239, and eq. (9.8), p. 266, iterated: if `b_t = s_t + β b_{t+1}` at
every date then `b_t = ∑_{j<T} βʲ s_{t+j} + βᵀ b_{t+T}`. -/
theorem real_iterate {β : ℝ} {b s : ℕ → ℝ} (h : ∀ t, b t = s t + β * b (t + 1)) (t T : ℕ) :
    b t = ∑ j ∈ Finset.range T, β ^ j * s (t + j) + β ^ T * b (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, h (t + T), Finset.sum_range_succ, pow_succ, show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), eq. (8.1), p. 239, pathwise and with the transversality condition explicit
(survey E8.2): the real flow `b_{t−1} = s_t + β b_t` at every date together with
`βᵀ b_{t+T−1} → 0` at every date is equivalent to the convergence, at every date, of the partial
sums of `∑_{j ≥ 0} βʲ s_{t+j}` to `b_{t−1}`. No summability, and no sign restriction on `β`, is
needed. -/
theorem real_flow_tvc_iff (β : ℝ) (b s : ℕ → ℝ) :
    ((∀ t, b t = s t + β * b (t + 1)) ∧
      ∀ t, Tendsto (fun T : ℕ => β ^ T * b (t + T)) atTop (𝓝 0)) ↔
    ∀ t, Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) atTop (𝓝 (b t)) := by
  constructor
  · rintro ⟨h, htvc⟩ t
    have h1 : ∀ T, ∑ j ∈ Finset.range T, β ^ j * s (t + j) = b t - β ^ T * b (t + T) :=
      fun T => by linarith [real_iterate h t T]
    simp_rw [h1]
    simpa using (tendsto_const_nhds (x := b t)).sub (htvc t)
  · intro hlim
    have hflow : ∀ t, b t = s t + β * b (t + 1) := by
      intro t
      have hsplit : ∀ T, ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j) =
          s t + β * ∑ j ∈ Finset.range T, β ^ j * s (t + 1 + j) := by
        intro T
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, one_mul, add_zero]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
        ring
      have hA : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j)) atTop
          (𝓝 (b t)) := (hlim t).comp (tendsto_add_atTop_nat 1)
      have hB : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j)) atTop
          (𝓝 (s t + β * b (t + 1))) := by
        simp_rw [hsplit]
        exact tendsto_const_nhds.add ((hlim (t + 1)).const_mul β)
      exact tendsto_nhds_unique hA hB
    refine ⟨hflow, fun t => ?_⟩
    have h1 : ∀ T, β ^ T * b (t + T) = b t - ∑ j ∈ Finset.range T, β ^ j * s (t + j) :=
      fun T => by linarith [real_iterate hflow t T]
    simp_rw [h1]
    simpa using (tendsto_const_nhds (x := b t)).sub (hlim t)

/-- Cochrane (2023), §9.3.2, p. 266 ("iterating forward and imposing the transversality
condition"), and eq. (8.1), p. 239: the flow `b_t = s_t + β b_{t+1}` with `βᵀ b_{t+T} → 0` at
date `t` gives `b_{t−1} = ∑ⱼ βʲ s_{t+j}` (ex post), as a genuine sum when the terms are
summable. -/
theorem hasSum_of_tvc {β : ℝ} {b s : ℕ → ℝ} (h : ∀ t, b t = s t + β * b (t + 1)) (t : ℕ)
    (htvc : Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0))
    (hsum : Summable (fun j => β ^ j * s (t + j))) :
    HasSum (fun j => β ^ j * s (t + j)) (b t) := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) atTop (𝓝 (b t)) := by
    have heq : (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) =
        fun T => b t - β ^ T * b (t + T) := by
      funext T
      have := real_iterate h t T
      linarith
    rw [heq]
    simpa using htvc.const_sub (b t)
  have h1 := hsum.hasSum
  rwa [tendsto_nhds_unique h1.tendsto_sum_nat hpart] at h1

/-- Cochrane (2023), §9.3.2, p. 266: for bounded surpluses and `0 ≤ β < 1` the discounted
surpluses are absolutely summable. -/
theorem summable_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ M) (t : ℕ) : Summable (fun j => β ^ j * s (t + j)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j)]
  exact mul_le_mul_of_nonneg_left (hs (t + j)) (pow_nonneg hβ0 j)

/-! ### Price uniqueness -/

/-- Cochrane (2023), p. 289 (`B_{t−1}/P_t = b_t`) and p. 295 (`N/P_t = E_t ∑ βʲ s_{t+j}`): the
valuation equation `B/P = V` with positive nominal claims `B` and positive real backing `V` has
exactly one positive solution, `P = B/V`. -/
theorem valuation_price_unique {B V : ℝ} (hB : 0 < B) (hV : 0 < V) :
    ∃! P : ℝ, 0 < P ∧ B / P = V := by
  refine ⟨B / V, ⟨div_pos hB hV, ?_⟩, ?_⟩
  · rw [div_div_eq_mul_div, mul_div_assoc, mul_div_cancel₀ V hB.ne']
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hV.ne', ← h]
    field_simp

/-- Cochrane (2023), §9.3.1, p. 265 (and §10.1.1, p. 289): if the surplus rises with the price
level (`s` strictly increasing on positive prices), `b_{T−1} = s_T(P_T)` has at most one
solution `P_T > 0`. -/
theorem price_unique_of_strictMonoOn {s : ℝ → ℝ} (hs : StrictMonoOn s (Set.Ioi 0))
    {b P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) (e₁ : b = s P₁) (e₂ : b = s P₂) : P₁ = P₂ :=
  hs.injOn h₁ h₂ (e₁.symm.trans e₂)

end Cochrane.AssetsRulesBalanceSheets.PresentValue

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Indexed debt, foreign debt, pegs and the gold standard

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.1 (pp. 239–240) and §8.2
(pp. 241–245).

Timing convention used throughout this project: a debt process `b : ℕ → Ω → ℝ` is indexed by the
date at which it comes due, so `b t` is Cochrane's `b_{t−1}` (issued at `t − 1`, paid at `t`) and
`b (t + 1)` is Cochrane's `b_t`, chosen at date `t`. The same applies to nominal debt `B`.

## Main results

* The general valuation machinery (`epv`, `pv`, `TVC`, `flow_tvc_iff_pv`, `real_iterate`,
  `real_flow_tvc_iff`, ...) lives in `PresentValue`, shared with the Chapter 9 and 10 modules.
* §8.1 indexed debt: `indexedPrice_eq` (the bracket in the flow is `β P_t`),
  `indexed_real_value` (the real value at `t − 1` of `b_{t−1}` is `β b_{t−1}`),
  `indexedFlow_iff` (`b_{t−1} = s_t + β b_t` state by state), `indexed_valuation_iff` ((8.1),
  pathwise, with the TVC made explicit), `indexed_valuation_tsum`, `indexed_pv_news_zero` (the
  surplus present value is predetermined: (8.1) is a restriction on surpluses),
  `indexedFlow_price_free` and `cashFlow_iff` (with only real debt the price level is not
  determined), `surplus_rule_determines` (surpluses `s(P)` can determine `P`).
* p. 240 mixed timing: `nominalIssue_flow_iff`, `realOutstanding_price_free` (real debt
  outstanding, nominal issued: `P_t` undetermined), `nominalOutstanding_price_unique` (nominal
  outstanding, real issued: `P_t = B_{t−1}/(s_t + β b_t)`).
* (8.2) foreign-currency debt: `nominalFlow_iff_solves`, `nominal_valuation_iff`,
  `haircut_of_fixed_price` (with the price level fixed, `B D/P̄ = V` forces the haircut
  `D = P̄ V/B`), `foreign_default_required`.
* §8.2 reserves and pegs: `reserves_price_unique`, `reserves_through_sum`,
  `gold_deflation_raises_pv`, `gold_devaluation`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.RealDebt

open Filter Topology PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §8.1 Indexed debt -/

/-- Cochrane (2023), p. 239: the nominal price at `t` of a one-period indexed bond paying
`P_{t+1}` dollars, the bracket `E_t[β (P_t/P_{t+1}) × P_{t+1}]` of the indexed-debt flow. -/
noncomputable def indexedPrice (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => β * (P t ω / P (t + 1) ω) * P (t + 1) ω)

/-- Cochrane (2023), p. 239: with an adapted, nowhere-zero price level the nominal price of an
indexed bond is `β P_t`. -/
theorem indexedPrice_eq {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) : indexedPrice 𝔼 β P t = β • P t := by
  have h : (fun ω => β * (P t ω / P (t + 1) ω) * P (t + 1) ω) = β • P t := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, div_mul_cancel₀ _ (hP (t + 1) ω)]
  rw [indexedPrice, h, map_smul, hPa t]

/-- Cochrane (2023), p. 239 (timing remark): the real price of the indexed bond is `β`, so the
real value at `t − 1` of `b_{t−1}` is `β b_{t−1}`. -/
theorem indexed_real_value {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (b : Ω → ℝ) (t : ℕ) (ω : Ω) :
    indexedPrice 𝔼 β P t ω / P t ω * b ω = β * b ω := by
  rw [indexedPrice_eq 𝔼 hPa hP t, Pi.smul_apply, smul_eq_mul, mul_div_assoc,
    div_self (hP t ω), mul_one]

/-- Cochrane (2023), p. 239: the nominal flow condition with only indexed debt,
`b_{t−1} P_t = P_t s_t + E_t[β (P_t/P_{t+1}) P_{t+1}] b_t`. -/
def IndexedFlow (β : ℝ) (b s P : ℕ → Ω → ℝ) : Prop :=
  ∀ t, b t * P t = P t * s t + indexedPrice 𝔼 β P t * b (t + 1)

/-- Cochrane (2023), p. 239: the indexed-debt flow is equivalent, for any adapted nowhere-zero
price level, to the real flow `b_{t−1} = s_t + β b_t` state by state. -/
theorem indexedFlow_iff {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) :
    IndexedFlow 𝔼 β b s P ↔ ∀ t ω, b t ω = s t ω + β * b (t + 1) ω := by
  simp only [IndexedFlow, indexedPrice_eq 𝔼 hPa hP, funext_iff, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h t ω
    have h1 : P t ω * b t ω = P t ω * (s t ω + β * b (t + 1) ω) := by
      linarith [h t ω]
    exact mul_left_cancel₀ (hP t ω) h1
  · intro h t ω
    rw [h t ω]
    ring

/-- Cochrane (2023), p. 239: with only real debt outstanding and surpluses independent of the
price level, the price level disappears: the flow holds for one adapted nowhere-zero price path
iff it holds for any other. -/
theorem indexedFlow_price_free {β : ℝ} {b s P P' : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hPa' : 𝔼.Adapted P') (hP' : ∀ t ω, P' t ω ≠ 0) :
    IndexedFlow 𝔼 β b s P ↔ IndexedFlow 𝔼 β b s P' := by
  rw [indexedFlow_iff 𝔼 hPa hP, indexedFlow_iff 𝔼 hPa' hP']

/-- Cochrane (2023), eq. (8.1), p. 239 (pathwise, TVC explicit): the indexed-debt flow plus
`βᵀ b_{t+T−1} → 0` in every state is equivalent to `b_{t−1} = ∑_{j ≥ 0} βʲ s_{t+j}` (as a
convergent series) in every state. -/
theorem indexed_valuation_iff {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) :
    (IndexedFlow 𝔼 β b s P ∧
      ∀ t ω, Tendsto (fun T : ℕ => β ^ T * b (t + T) ω) atTop (𝓝 0)) ↔
    ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j) ω) atTop (𝓝 (b t ω)) := by
  rw [indexedFlow_iff 𝔼 hPa hP]
  constructor
  · rintro ⟨h, htvc⟩ t ω
    exact (real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mp
      ⟨fun t => h t ω, fun t => htvc t ω⟩ t
  · intro h
    refine ⟨fun t ω => ?_, fun t ω => ?_⟩
    · exact ((real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mpr
        (fun t => h t ω)).1 t
    · exact ((real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mpr
        (fun t => h t ω)).2 t

/-- Cochrane (2023), eq. (8.1), p. 239: when the discounted surpluses are summable in every
state, the flow and the TVC give `b_{t−1} = ∑' βʲ s_{t+j}` (a genuine `tsum`). -/
theorem indexed_valuation_tsum {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : IndexedFlow 𝔼 β b s P)
    (htvc : ∀ t ω, Tendsto (fun T : ℕ => β ^ T * b (t + T) ω) atTop (𝓝 0))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * s (t + j) ω)) : ∀ t, b t = epv β s t := by
  intro t
  funext ω
  exact tendsto_nhds_unique ((indexed_valuation_iff 𝔼 hPa hP).mp ⟨hflow, htvc⟩ t ω)
    (hsum t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), p. 239 ("a restriction on surpluses", `a(ρ) = 0`): if indexed debt is
valued by (8.1) and `b_t` is chosen at `t` (known at `t`), the ex post present value of
surpluses from `t + 1` on is already known at `t`: it has no news,
`E_{t+1} ∑ βʲ s_{t+1+j} − E_t ∑ βʲ s_{t+1+j} = 0`. -/
theorem indexed_pv_news_zero {β : ℝ} {b s : ℕ → Ω → ℝ} (hb : ∀ t, b t = epv β s t)
    (hpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) (t : ℕ) :
    𝔼.E (t + 1) (epv β s (t + 1)) - 𝔼.E t (epv β s (t + 1)) = 0 := by
  rw [← hb (t + 1), hpre t, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hpre t), sub_self]

/-- Cochrane (2023), p. 240: the cash version of the flow, `P_t b_{t−1} = P_t s_t + P_t β b_t`,
holds for a nowhere-zero price path iff the real flow holds — for any price level if surpluses
obey (8.1), for none otherwise. -/
theorem cashFlow_iff {β : ℝ} {b s P : ℕ → ℝ} (hP : ∀ t, P t ≠ 0) :
    (∀ t, P t * b t = P t * s t + P t * (β * b (t + 1))) ↔
      ∀ t, b t = s t + β * b (t + 1) := by
  constructor
  · intro h t
    exact mul_left_cancel₀ (hP t) (by rw [h t]; ring)
  · intro h t
    rw [h t]
    ring

/-- Cochrane (2023), p. 239: surpluses that respond to the price level, `s_t = σ(P_t)` with
`σ` injective, can determine the price level even with only real debt: given `b_{t−1}` and
`b_t` there is at most one price level. -/
theorem surplus_rule_determines {β : ℝ} {σ : ℝ → ℝ} (hσ : Function.Injective σ)
    {b b' p p' : ℝ} (hp : b = σ p + β * b') (hp' : b = σ p' + β * b') : p = p' :=
  hσ (by linarith)

/-! ### p. 240: which kind of debt comes due -/

/-- Cochrane (2023), p. 240: real debt `b` outstanding and nominal debt `B_t` issued at price
`Q_t = β E_t(P_t/P_{t+1})`. With the pull-out property and a nowhere-zero date-`t` price `p` known
at `t`, the flow `p b = p s + Q_t B_t` is equivalent to `b = s + β E_t(1/P_{t+1}) B_t`, which
does not involve `p`. -/
theorem nominalIssue_flow_iff (hPO : 𝔼.PullOut) {t : ℕ} {β : ℝ} {b s p Pn Bn : Ω → ℝ}
    (hp : 𝔼.E t p = p) (hp0 : ∀ ω, p ω ≠ 0) :
    p * b = p * s + 𝔼.E t (β • (p / Pn)) * Bn ↔ b = s + β • (𝔼.E t Pn⁻¹ * Bn) := by
  have hE : 𝔼.E t (β • (p / Pn)) = β • (p * 𝔼.E t Pn⁻¹) := by
    rw [map_smul, div_eq_mul_inv, hPO t p Pn⁻¹ hp]
  rw [hE]
  simp only [funext_iff, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h ω
    exact mul_left_cancel₀ (hp0 ω) (by rw [h ω]; ring)
  · intro h ω
    rw [h ω]
    ring

/-- Cochrane (2023), p. 240: if real debt is outstanding but the government issues nominal
debt, the date-`t` price level is still undetermined: the flow holds at one nowhere-zero known
price iff it holds at any other. -/
theorem realOutstanding_price_free (hPO : 𝔼.PullOut) {t : ℕ} {β : ℝ} {b s p p' Pn Bn : Ω → ℝ}
    (hp : 𝔼.E t p = p) (hp0 : ∀ ω, p ω ≠ 0) (hp' : 𝔼.E t p' = p') (hp0' : ∀ ω, p' ω ≠ 0) :
    p * b = p * s + 𝔼.E t (β • (p / Pn)) * Bn ↔
      p' * b = p' * s + 𝔼.E t (β • (p' / Pn)) * Bn := by
  rw [nominalIssue_flow_iff 𝔼 hPO hp hp0, nominalIssue_flow_iff 𝔼 hPO hp' hp0']

/-- Cochrane (2023), p. 240: if nominal debt `B_{t−1} > 0` is outstanding and the government
issues real debt `b_t` (nominal price `β P_t`), the flow `B_{t−1} = P_t s_t + β P_t b_t`
determines the price level uniquely, `P_t = B_{t−1}/(s_t + β b_t)`, when `s_t + β b_t > 0`. -/
theorem nominalOutstanding_price_unique {β B s b : ℝ} (hB : 0 < B) (hv : 0 < s + β * b) :
    ∃! P : ℝ, 0 < P ∧ B = P * s + β * P * b := by
  refine ⟨B / (s + β * b), ⟨div_pos hB hv, ?_⟩, ?_⟩
  · field_simp
  · rintro P ⟨_, hP⟩
    rw [eq_div_iff hv.ne']
    rw [hP]
    ring

/-! ### (8.2) Foreign-currency debt -/

/-- Cochrane (2023), eq. (8.2), p. 240: the flow condition for nominal debt (in domestic or, for
(8.2), foreign currency) at bond price `Q_t = β E_t(P_t/P_{t+1})`,
`B_{t−1} = P_t s_t + Q_t B_t`. -/
def NominalFlow (β : ℝ) (B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t = P t * s t + 𝔼.E t (β • (P t / P (t + 1))) * B (t + 1)

/-- Cochrane (2023), eq. (8.2), p. 240: with the pull-out property, an adapted nowhere-zero
price level and debt `B_t` chosen at `t`, the nominal flow is the real recursion
`B_{t−1}/P_t = s_t + β E_t(B_t/P_{t+1})`. -/
theorem nominalFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {B P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    NominalFlow 𝔼 β B P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => B t / P t) := by
  have hE1 : ∀ t, 𝔼.E t (β • (P t / P (t + 1))) = β • (P t * 𝔼.E t (P (t + 1))⁻¹) := by
    intro t
    rw [map_smul, div_eq_mul_inv, hPO t (P t) (P (t + 1))⁻¹ (hPa t)]
  have hE2 : ∀ t, 𝔼.E t (B (t + 1) / P (t + 1)) = B (t + 1) * 𝔼.E t (P (t + 1))⁻¹ := by
    intro t
    rw [div_eq_mul_inv, hPO t (B (t + 1)) (P (t + 1))⁻¹ (hBpre t)]
  simp only [NominalFlow, ForwardSolution.Solves, hE1, hE2, funext_iff, Pi.add_apply,
    Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
  constructor
  · intro h t ω
    rw [div_eq_iff (hP t ω), h t ω]
    ring
  · intro h t ω
    have h1 := h t ω
    rw [div_eq_iff (hP t ω)] at h1
    rw [h1]
    ring

/-- Cochrane (2023), eq. (8.2), p. 240: for bounded adapted surpluses, `0 ≤ β < 1`, the
pull-out property, an adapted nowhere-zero price level `P` (for (8.2) the foreign price level
`P*`) and predetermined debt, the nominal flow plus the transversality condition on `B/P` is
equivalent to the valuation equation `B_{t−1}/P_t = E_t ∑ βʲ s_{t+j}` at every date. With `P*`
given from abroad this is a constraint on surpluses. -/
theorem nominal_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (NominalFlow 𝔼 β B P s ∧ TVC 𝔼 β (fun t => B t / P t)) ↔
      ∀ t, B t / P t = pv 𝔼 β s t := by
  rw [nominalFlow_iff_solves 𝔼 hPO hPa hP hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa, funext_iff]

/-- Cochrane (2023), p. 240 (foreign-currency debt) and §8.6, p. 257 (an independent central
bank): when the price level is fixed at `P̄ > 0` (from abroad, or by the central bank), the
valuation `B D/P̄ = V` with `B > 0` gives the haircut `D = P̄ V/B`, with `D = 1` iff `V = B/P̄`
and `D < 1` iff `V < B/P̄`. -/
theorem haircut_of_fixed_price {B Pbar V D : ℝ} (hB : 0 < B) (hP : 0 < Pbar)
    (hD : B * D / Pbar = V) :
    D = Pbar * V / B ∧ (D = 1 ↔ V = B / Pbar) ∧ (D < 1 ↔ V < B / Pbar) := by
  have hD' : D = Pbar * V / B := by
    rw [eq_div_iff hB.ne', ← hD]
    field_simp
  refine ⟨hD', ?_, ?_⟩
  · rw [hD', div_eq_one_iff_eq hB.ne', eq_div_iff hP.ne']
    constructor <;> intro h <;> linarith
  · rw [hD', div_lt_one hB, lt_div_iff₀ hP]
    constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 240 (Greece in the euro): with foreign-currency debt `B > 0` and the
foreign price level `P* > 0` given, the price level cannot adjust; if the present value of
surpluses `V` falls short of `B/P*`, the only way to satisfy `B D/P* = V` is an explicit
haircut, `D = P* V/B < 1`. -/
theorem foreign_default_required {B Pstar V D : ℝ} (hB : 0 < B) (hP : 0 < Pstar)
    (hshort : V < B / Pstar) (hD : B * D / Pstar = V) : D = Pstar * V / B ∧ D < 1 :=
  ⟨(haircut_of_fixed_price hB hP hD).1, (haircut_of_fixed_price hB hP hD).2.2.mpr hshort⟩

/-! ### §8.2 Reserves, pegs and the gold standard -/

/-- Cochrane (2023), p. 242: with reserves `G` the valuation equation is
`B_{t−1}/P_t = G_t + E_t ∑ βʲ s_{t+j}`; for `B > 0` and `G + V > 0` the price level is unique,
`P = B/(G + V)`. -/
theorem reserves_price_unique {B G V : ℝ} (hB : 0 < B) (hGV : 0 < G + V) :
    ∃! P : ℝ, 0 < P ∧ B / P = G + V :=
  valuation_price_unique hB hGV

/-- Cochrane (2023), p. 242: reserves "enter in parallel with the present value of surpluses":
the price level depends on reserves `G` and the surplus present value `V` only through
`G + V`. -/
theorem reserves_through_sum {B G V G' V' P : ℝ} (hsum : G + V = G' + V') :
    B / P = G + V ↔ B / P = G' + V' := by
  rw [hsum]

/-- Cochrane (2023), p. 243: the gold standard is passive with respect to the relative price of
goods and gold: a deflation (`q` falls) raises the surplus present value needed to pay the debt
at the peg. -/
theorem gold_deflation_raises_pv {B Pg q q' : ℝ} (hB : 0 < B) (hPg : 0 < Pg) (hq' : 0 < q')
    (hq : q' < q) : B / (Pg * q) < B / (Pg * q') := by
  apply div_lt_div_of_pos_left hB (mul_pos hPg hq') (mul_lt_mul_of_pos_left hq hPg)

/-- Cochrane (2023), pp. 242–243 ($20 to $32 per ounce): a devaluation from `P_g = 20` to
`P_g = 32` raises the price level by the factor `8/5` at a given relative price `q`, and cuts the
required present value of surpluses by the factor `5/8`. -/
theorem gold_devaluation {B q : ℝ} (hB : 0 < B) (hq : 0 < q) :
    (32 * q) / (20 * q) = 8 / 5 ∧ (B / (32 * q)) / (B / (20 * q)) = 5 / 8 := by
  constructor
  · field_simp
    norm_num
  · field_simp
    norm_num

end Cochrane.AssetsRulesBalanceSheets.RealDebt

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The corporate finance of government debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.3 (pp. 245–249),
eq. (8.3).

With real debt `b_{t−1}` and nominal debt `B_{t−1}` outstanding, the valuation equation is
`b_{t−1} + B_{t−1}/P_t = E_t ∑ βʲ s_{t+j} =: V_t` (8.3). Real debt is like corporate debt and
nominal debt like equity: the price level is determined by the nominal part only, and more real
debt (leverage) makes the price level more sensitive to fiscal news.

## Main results

* `mixedFlow_iff_solves`, `mixed_valuation_iff`: the flow with both kinds of debt plus the
  transversality condition is equivalent to (8.3).
* `mixed_price_unique` (`P = B/(V − b)` when `V > b`, `B > 0`), `mixed_no_price` (no price level
  when `V ≤ b`: default is needed), `mixed_zero_nominal` (with no nominal debt the price level is
  free when `V = b` and no price level exists otherwise).
* Leverage: `log_price_hasDerivAt`, `log_price_elasticity` (the exact elasticity
  `d log P/d log V = −V/(V − b)`), `elasticity_gt_one_iff`, `elasticity_strictMono`,
  `price_ratio`, `log_price_spread_strictMono` (for any two values of `V`, the log price-level
  difference strictly increases with real debt `b`), `default_prob_mono` (a larger real debt
  raises the conditional probability of explicit default).
* Cashless limit (p. 248): `cashless_sequence_determinate`, `cashless_nominal_vanishes`,
  `cashless_elasticity_explodes`, `cashless_limit_indeterminate`, and the pennies example
  `pennies_inflation` (exactly `10/9`, i.e. 11.1%, where the book says 10%).
-/

namespace Cochrane.AssetsRulesBalanceSheets.CapitalStructure

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The valuation equation (8.3) -/

/-- Cochrane (2023), eq. (8.3), p. 246 (flow form): with real debt `b` and nominal debt `B`,
`P_t b_{t−1} + B_{t−1} = P_t s_t + (β P_t) b_t + Q_t B_t`, the indexed bond selling at
`E_t[β (P_t/P_{t+1}) P_{t+1}]` and the nominal bond at `Q_t = β E_t(P_t/P_{t+1})`. -/
def MixedFlow (β : ℝ) (b B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, P t * b t + B t = P t * s t + indexedPrice 𝔼 β P t * b (t + 1) +
    𝔼.E t (β • (P t / P (t + 1))) * B (t + 1)

/-- Cochrane (2023), eq. (8.3), p. 246: with the pull-out property, an adapted nowhere-zero price
level, and both debts chosen at `t`, the mixed flow is the real recursion for the total real
value `x_t = b_{t−1} + B_{t−1}/P_t`, `x_t = s_t + β E_t x_{t+1}`. -/
theorem mixedFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {b B P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hbpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1))
    (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    MixedFlow 𝔼 β b B P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => b t + B t / P t) := by
  have hE1 : ∀ t, 𝔼.E t (β • (P t / P (t + 1))) = β • (P t * 𝔼.E t (P (t + 1))⁻¹) := by
    intro t
    rw [map_smul, div_eq_mul_inv, hPO t (P t) (P (t + 1))⁻¹ (hPa t)]
  have hE2 : ∀ t, 𝔼.E t (b (t + 1) + B (t + 1) / P (t + 1)) =
      b (t + 1) + B (t + 1) * 𝔼.E t (P (t + 1))⁻¹ := by
    intro t
    rw [map_add, hbpre t, div_eq_mul_inv, hPO t (B (t + 1)) (P (t + 1))⁻¹ (hBpre t)]
  simp only [MixedFlow, ForwardSolution.Solves, indexedPrice_eq 𝔼 hPa hP, hE1, hE2, funext_iff,
    Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
  constructor
  · intro h t ω
    have hPt := hP t ω
    have h1 := h t ω
    field_simp
    linear_combination h1
  · intro h t ω
    have hPt := hP t ω
    have h1 := h t ω
    field_simp at h1
    linear_combination h1

/-- Cochrane (2023), eq. (8.3), p. 246: for bounded adapted surpluses and `0 ≤ β < 1`, the mixed
flow plus the transversality condition on the total real value is equivalent to
`b_{t−1} + B_{t−1}/P_t = E_t ∑ βʲ s_{t+j}` at every date. -/
theorem mixed_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b B P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hbpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1))
    (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (MixedFlow 𝔼 β b B P s ∧ TVC 𝔼 β (fun t => b t + B t / P t)) ↔
      ∀ t, b t + B t / P t = pv 𝔼 β s t := by
  rw [mixedFlow_iff_solves 𝔼 hPO hPa hP hbpre hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa,
    funext_iff]

/-! ### Existence and uniqueness of the price level -/

/-- Cochrane (2023), eq. (8.3), p. 246: "the price level is determined by the ability to devalue
the nominal debt only": with `B > 0` and `V > b` there is exactly one positive price level,
`P = B/(V − b)`. -/
theorem mixed_price_unique {b B V : ℝ} (hB : 0 < B) (hVb : b < V) :
    ∃! P : ℝ, 0 < P ∧ b + B / P = V := by
  have hpos : 0 < V - b := sub_pos.mpr hVb
  refine ⟨B / (V - b), ⟨div_pos hB hpos, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hpos.ne', ← h]
    field_simp
    ring

/-- Cochrane (2023), §8.3, p. 246: if the present value of surpluses does not exceed the real
debt, `V ≤ b`, no positive price level satisfies (8.3): the real debt must be defaulted on. -/
theorem mixed_no_price {b B V : ℝ} (hB : 0 < B) (hVb : V ≤ b) :
    ¬ ∃ P : ℝ, 0 < P ∧ b + B / P = V := by
  rintro ⟨P, hP, h⟩
  have : 0 < B / P := div_pos hB hP
  linarith

/-- Cochrane (2023), §8.1 and §8.3, pp. 239, 246: with no nominal debt, (8.3) does not involve the
price level: every price level solves it if `V = b` and none does otherwise. -/
theorem mixed_zero_nominal (b V P : ℝ) : b + 0 / P = V ↔ V = b := by
  rw [zero_div, add_zero, eq_comm]

/-! ### Leverage and price-level volatility -/

/-- Cochrane (2023), §8.3, p. 246: the exact derivative of the log price level
`log P = log(B/(V − b))` with respect to the present value of surpluses is `−1/(V − b)`. -/
theorem log_price_hasDerivAt {b B V : ℝ} (hB : 0 < B) (hVb : b < V) :
    HasDerivAt (fun x => Real.log (B / (x - b))) (-(1 / (V - b))) V := by
  have hne : V - b ≠ 0 := (sub_pos.mpr hVb).ne'
  have h1 : HasDerivAt (fun x => x - b) 1 V := HasDerivAt.sub_const b (hasDerivAt_id V)
  have h2 : HasDerivAt (fun x => (x - b)⁻¹) (-1 / (V - b) ^ 2) V := HasDerivAt.inv h1 hne
  have h3 : HasDerivAt (fun x => B * (x - b)⁻¹) (B * (-1 / (V - b) ^ 2)) V :=
    HasDerivAt.const_mul B h2
  have h4 := HasDerivAt.log h3 (mul_ne_zero hB.ne' (inv_ne_zero hne))
  have hf : (fun x => Real.log (B / (x - b))) = fun x => Real.log (B * (x - b)⁻¹) := by
    funext x
    rw [div_eq_mul_inv]
  rw [hf]
  refine HasDerivAt.congr_deriv h4 ?_
  field_simp

/-- Cochrane (2023), §8.3, p. 246 (leverage): the exact elasticity of the price level with
respect to the present value of surpluses, `d log P/d log V = −V/(V − b)` at `V > max(b, 0)`. -/
theorem log_price_elasticity {b B V : ℝ} (hB : 0 < B) (hV : 0 < V) (hVb : b < V) :
    HasDerivAt (fun u => Real.log (B / (Real.exp u - b))) (-(V / (V - b))) (Real.log V) := by
  have h : HasDerivAt (fun x => Real.log (B / (x - b))) (-(1 / (V - b)))
      (Real.exp (Real.log V)) := by
    rw [Real.exp_log hV]
    exact log_price_hasDerivAt hB hVb
  have h2 := HasDerivAt.comp (Real.log V) h (Real.hasDerivAt_exp (Real.log V))
  refine HasDerivAt.congr_deriv h2 ?_
  rw [Real.exp_log hV]
  ring

/-- Cochrane (2023), §8.3, p. 246: the price level is more sensitive than one-for-one to fiscal
news, `V/(V − b) > 1`, exactly when there is real debt, `b > 0`. -/
theorem elasticity_gt_one_iff {b V : ℝ} (hVb : b < V) :
    1 < V / (V - b) ↔ 0 < b := by
  have hpos : 0 < V - b := sub_pos.mpr hVb
  rw [one_lt_div hpos]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.3, p. 246: "a government that issues more real debt and less nominal
debt ... increases the volatility of inflation": the elasticity `V/(V − b)` is strictly
increasing in real debt `b < V`. -/
theorem elasticity_strictMono {b b' V : ℝ} (hV : 0 < V) (hbb : b < b') (hb'V : b' < V) :
    V / (V - b) < V / (V - b') :=
  div_lt_div_of_pos_left hV (sub_pos.mpr hb'V) (by linarith)

/-- Cochrane (2023), eq. (8.3), p. 246: the exact price-level response to a change of the present
value from `V` to `V'` (both above `b`) is `P(V')/P(V) = (V − b)/(V' − b)`. -/
theorem price_ratio {b B V V' : ℝ} (hB : 0 < B) (hVb : b < V) (hV'b : b < V') :
    (B / (V' - b)) / (B / (V - b)) = (V - b) / (V' - b) := by
  have h1 : V - b ≠ 0 := (sub_pos.mpr hVb).ne'
  have h2 : V' - b ≠ 0 := (sub_pos.mpr hV'b).ne'
  field_simp

/-- Cochrane (2023), §8.3, p. 246 (leverage raises inflation volatility, exactly): for any two
present values `V₁ < V₂`, the log price-level difference
`log P(V₁) − log P(V₂) = log((V₂ − b)/(V₁ − b)) > 0` is strictly increasing in real debt
`b < V₁`. -/
theorem log_price_spread_strictMono {b b' B V₁ V₂ : ℝ} (hB : 0 < B) (hV : V₁ < V₂)
    (hbb : b < b') (hb'V : b' < V₁) :
    0 < Real.log (B / (V₁ - b)) - Real.log (B / (V₂ - b)) ∧
    Real.log (B / (V₁ - b)) - Real.log (B / (V₂ - b)) <
      Real.log (B / (V₁ - b')) - Real.log (B / (V₂ - b')) := by
  have p1 : 0 < V₁ - b := by linarith
  have p2 : 0 < V₂ - b := by linarith
  have p1' : 0 < V₁ - b' := by linarith
  have p2' : 0 < V₂ - b' := by linarith
  have key : ∀ c : ℝ, 0 < V₁ - c → 0 < V₂ - c →
      Real.log (B / (V₁ - c)) - Real.log (B / (V₂ - c)) = Real.log ((V₂ - c) / (V₁ - c)) := by
    intro c hc1 hc2
    rw [← Real.log_div (div_pos hB hc1).ne' (div_pos hB hc2).ne']
    congr 1
    field_simp
  rw [key b p1 p2, key b' p1' p2']
  constructor
  · apply Real.log_pos
    rw [one_lt_div p1]
    linarith
  · apply Real.log_lt_log (div_pos p2 p1)
    rw [div_lt_div_iff₀ p1 p1']
    nlinarith

/-- Cochrane (2023), §8.3, p. 246 ("raises the chance of explicit default"): with real debt `b`,
explicit default occurs in the states where `V < b`; its conditional probability
`E_t 1{V < b}` is weakly increasing in `b`. -/
theorem default_prob_mono (t : ℕ) (V : Ω → ℝ) {b b' : ℝ} (hbb : b ≤ b') :
    𝔼.E t (fun ω => if V ω < b then (1 : ℝ) else 0) ≤
      𝔼.E t (fun ω => if V ω < b' then (1 : ℝ) else 0) := by
  refine 𝔼.mono t fun ω => ?_
  by_cases h : V ω < b
  · have h' : V ω < b' := lt_of_lt_of_le h hbb
    simp [h, h']
  · by_cases h' : V ω < b'
    · simp [h, h']
    · simp [h, h']

/-! ### The cashless limit (p. 248) -/

/-- Cochrane (2023), §8.3, p. 248: along a sequence with real debt `b_n < V` and nominal debt
`B_n = P (V − b_n)`, the price level `P` is the unique positive solution of (8.3) at every `n`
("determinate all the way along"). -/
theorem cashless_sequence_determinate {P V : ℝ} (hP : 0 < P) {b : ℕ → ℝ}
    (hb : ∀ n, b n < V) (n : ℕ) :
    ∃! p : ℝ, 0 < p ∧ b n + P * (V - b n) / p = V := by
  have hpos : 0 < V - b n := sub_pos.mpr (hb n)
  obtain ⟨p, ⟨hp, hpv⟩, huniq⟩ := mixed_price_unique (mul_pos hP hpos) (hb n)
  refine ⟨p, ⟨hp, hpv⟩, huniq⟩

/-- Cochrane (2023), §8.3, p. 248: the solution in `cashless_sequence_determinate` is the same
price level `P` at every `n` ("so that inflation remains the same"). -/
theorem cashless_sequence_price {P V : ℝ} (hP : 0 < P) (b : ℕ → ℝ) (n : ℕ) :
    b n + P * (V - b n) / P = V := by
  have : P * (V - b n) / P = V - b n := by field_simp
  rw [this]
  ring

/-- Cochrane (2023), §8.3, p. 248: as real debt approaches the present value, `b_n → V`, the
nominal debt `B_n = P(V − b_n)` vanishes. -/
theorem cashless_nominal_vanishes {P V : ℝ} {b : ℕ → ℝ} (hlim : Tendsto b atTop (𝓝 V)) :
    Tendsto (fun n => P * (V - b n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => V - b n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := V)).sub hlim
  simpa using h.const_mul P

/-- Cochrane (2023), §8.3, p. 248: along the cashless sequence the elasticity of the price level
to fiscal news, `V/(V − b_n)`, diverges to `+∞`. -/
theorem cashless_elasticity_explodes {V : ℝ} (hV : 0 < V) {b : ℕ → ℝ} (hb : ∀ n, b n < V)
    (hlim : Tendsto b atTop (𝓝 V)) : Tendsto (fun n => V / (V - b n)) atTop atTop := by
  have h : Tendsto (fun n => V - b n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using (tendsto_const_nhds (x := V)).sub hlim
    · exact sub_pos.mpr (hb n)
  have h2 : Tendsto (fun n => (V - b n)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp h
  simpa [div_eq_mul_inv] using Tendsto.const_mul_atTop hV h2

/-- Cochrane (2023), §8.3, p. 248: at the limit point (`B = 0`, `b = V`) every positive price
level solves (8.3) — determinate along the sequence, not at the limit. -/
theorem cashless_limit_indeterminate (V p : ℝ) : V + 0 / p = V := by
  rw [zero_div, add_zero]

/-- Cochrane (2023), §8.3, p. 248 ($10 of pennies, survey E8.4): if the nominal debt is worth
`B/P = 10` and the surplus present value falls by `1` with real debt unchanged, the price level
rises by the exact factor `10/9` (11.1%; the book's "10%" is the first-order approximation). -/
theorem pennies_inflation {b B P P' V : ℝ} (hB : 0 < B) (hP : 0 < P) (hP' : 0 < P')
    (h0 : b + B / P = V) (h1 : b + B / P' = V - 1) (h10 : B / P = 10) : P' / P = 10 / 9 := by
  have h9 : B / P' = 9 := by linarith
  have e1 : P = B / 10 := by
    rw [eq_div_iff (by norm_num : (10 : ℝ) ≠ 0), ← h10]
    field_simp
  have e2 : P' = B / 9 := by
    rw [eq_div_iff (by norm_num : (9 : ℝ) ≠ 0), ← h9]
    field_simp
  rw [e1, e2]
  field_simp

end Cochrane.AssetsRulesBalanceSheets.CapitalStructure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Long versus short debt: the maturity buffer

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4 (pp. 249–254),
eq. (8.4) and the continuous-time present-value relation on p. 250.

## Main results

* `identity_84`: the weighted unexpected-inflation identity (8.4) is derived from the
  linearised identities (3.20) (with no growth term) and (3.21), which are taken as the model
  equations (they are approximations derived in Chapter 3). The real-rate terms in (8.4) are the
  news `ΔE_{t+1} r_{t+1+j}`, `j ≥ 1`, as in (3.22); (8.4) prints `r_{t+j}` (an index slip).
* `short_debt_identity` (`ω = 0`: the whole revision of the surplus present value is met by
  immediate inflation), `short_debt_constant_rates`, `matched_maturity_identity` (`ω = ρ`:
  real-rate news drops out), `rate_weights_antitone` (the weights `ρʲ − ωʲ` shrink as the
  maturity `ω` lengthens towards `ρ`).
* Continuous time, perfect foresight (p. 250): `matching_cancels` (if the real value of debt
  maturing at each date matches the surplus at that date, the present-value relation holds for
  every real-rate path) and `price_insulated` (the price level is then the same for every real
  rate path).
* The converse, in discrete time: `matching_necessary`, `price_insulated_only_if_matching`: if
  the price level is the same for every real-rate path (rates bounded below by some `r̲ > 0`),
  then debt maturity must match surpluses exactly.
* Survey E8.3: `matching_fails_under_uncertainty` — with stochastic real rates correlated with
  the price level, matching `B^{(t+τ)} E_t(1/P_{t+τ}) = s_{t+τ}` does not cancel the rates.
-/

namespace Cochrane.AssetsRulesBalanceSheets.MaturityBuffer

open Filter Topology MeasureTheory

/-! ### The identity (8.4) and its corollaries -/

/-- Cochrane (2023), eq. (3.20), p. 65, with no growth term, as used for (8.4), p. 250: the news
at `t + 1` in inflation `πN j = ΔE_{t+1} π_{t+1+j}`, surpluses `sN j = ΔE_{t+1} s_{t+1+j}`, real
returns `rN j = ΔE_{t+1} r_{t+1+j}` and the nominal bond return `rn = ΔE_{t+1} rⁿ_{t+1}` satisfy
`πN₀ − rn = −∑ ρʲ sN_j + ∑_{j ≥ 1} ρʲ rN_j`. -/
def Identity320 (ρ : ℝ) (πN sN rN : ℕ → ℝ) (rn : ℝ) : Prop :=
  πN 0 - rn = -(∑' j, ρ ^ j * sN j) + ∑' j, ρ ^ (j + 1) * rN (j + 1)

/-- Cochrane (2023), eq. (3.21), p. 65, as used for (8.4), p. 250: with geometric maturity `w`
(the book's `ω`), `rn = −∑_{j ≥ 1} wʲ (rN_j + πN_j)`. -/
def Identity321 (w : ℝ) (πN rN : ℕ → ℝ) (rn : ℝ) : Prop :=
  rn = -(∑' j, w ^ (j + 1) * (rN (j + 1) + πN (j + 1)))

/-- Cochrane (2023), eq. (8.4), p. 250 (derived from (3.20)–(3.21)):
`∑ wʲ ΔE π_{t+1+j} = −∑ ρʲ ΔE s_{t+1+j} + ∑_{j ≥ 1} (ρʲ − wʲ) ΔE r_{t+1+j}`, assuming the
real-rate and inflation news series weighted by `wʲ` and `ρʲ` are summable. -/
theorem identity_84 {ρ w rn : ℝ} {πN sN rN : ℕ → ℝ}
    (hs1 : Summable (fun j => w ^ (j + 1) * rN (j + 1)))
    (hs2 : Summable (fun j => w ^ (j + 1) * πN (j + 1)))
    (hs3 : Summable (fun j => ρ ^ (j + 1) * rN (j + 1)))
    (h320 : Identity320 ρ πN sN rN rn) (h321 : Identity321 w πN rN rn) :
    ∑' j, w ^ j * πN j =
      -(∑' j, ρ ^ j * sN j) + ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * rN (j + 1) := by
  have hsum0 : Summable (fun j => w ^ j * πN j) :=
    (summable_nat_add_iff (f := fun j => w ^ j * πN j) 1).mp hs2
  have e1 : ∑' j, w ^ j * πN j = πN 0 + ∑' j, w ^ (j + 1) * πN (j + 1) := by
    rw [hsum0.tsum_eq_zero_add]
    simp
  have e2 : ∑' j, w ^ (j + 1) * (rN (j + 1) + πN (j + 1)) =
      ∑' j, w ^ (j + 1) * rN (j + 1) + ∑' j, w ^ (j + 1) * πN (j + 1) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun j => by ring
  have e3 : ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * rN (j + 1) =
      ∑' j, ρ ^ (j + 1) * rN (j + 1) - ∑' j, w ^ (j + 1) * rN (j + 1) := by
    rw [← hs3.tsum_sub hs1]
    exact tsum_congr fun j => by ring
  unfold Identity320 at h320
  unfold Identity321 at h321
  rw [e1, e3]
  rw [e2] at h321
  linarith

/-- Cochrane (2023), §8.4, p. 250: "If `ω = 0`, short-term debt, then the entire revision in the
present value of surpluses must be met by immediate inflation":
`ΔE π_{t+1} = −∑ ρʲ ΔE s_{t+1+j} + ∑_{j ≥ 1} ρʲ ΔE r_{t+1+j}`. -/
theorem short_debt_identity {ρ rn : ℝ} {πN sN rN : ℕ → ℝ} (h320 : Identity320 ρ πN sN rN rn)
    (h321 : Identity321 0 πN rN rn) :
    πN 0 = -(∑' j, ρ ^ j * sN j) + ∑' j, ρ ^ (j + 1) * rN (j + 1) := by
  unfold Identity321 at h321
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_mul, tsum_zero, neg_zero] at h321
  unfold Identity320 at h320
  rw [h321, sub_zero] at h320
  exact h320

/-- Cochrane (2023), §8.4, p. 250: with short-term debt and no real-rate news, unexpected
inflation is exactly minus the revision of the present value of surpluses. -/
theorem short_debt_constant_rates {ρ rn : ℝ} {πN sN : ℕ → ℝ}
    (h320 : Identity320 ρ πN sN (fun _ => 0) rn) (h321 : Identity321 0 πN (fun _ => 0) rn) :
    πN 0 = -(∑' j, ρ ^ j * sN j) := by
  have h := short_debt_identity h320 h321
  simpa using h

/-- Cochrane (2023), §8.4, p. 250: "In the limit `ω = ρ`, a real-rate increase has no
inflationary effect": with `w = ρ` the real-rate news drops out of (8.4),
`∑ ρʲ ΔE π_{t+1+j} = −∑ ρʲ ΔE s_{t+1+j}`. -/
theorem matched_maturity_identity {ρ rn : ℝ} {πN sN rN : ℕ → ℝ}
    (hs1 : Summable (fun j => ρ ^ (j + 1) * rN (j + 1)))
    (hs2 : Summable (fun j => ρ ^ (j + 1) * πN (j + 1)))
    (h320 : Identity320 ρ πN sN rN rn) (h321 : Identity321 ρ πN rN rn) :
    ∑' j, ρ ^ j * πN j = -(∑' j, ρ ^ j * sN j) := by
  rw [identity_84 hs1 hs2 hs1 h320 h321]
  simp

/-- Cochrane (2023), §8.4, p. 250: "The larger `ω`, the smaller the weights `ρʲ − ωʲ`": for
`0 ≤ w ≤ w' ≤ ρ` the real-rate weights satisfy `0 ≤ ρʲ − w'ʲ ≤ ρʲ − wʲ`. -/
theorem rate_weights_antitone {ρ w w' : ℝ} (hw : 0 ≤ w) (hww : w ≤ w') (hw'ρ : w' ≤ ρ)
    (j : ℕ) : 0 ≤ ρ ^ j - w' ^ j ∧ ρ ^ j - w' ^ j ≤ ρ ^ j - w ^ j := by
  have h1 : w' ^ j ≤ ρ ^ j := pow_le_pow_left₀ (hw.trans hww) hw'ρ j
  have h2 : w ^ j ≤ w' ^ j := pow_le_pow_left₀ hw hww j
  constructor <;> linarith

/-! ### Continuous-time matching (perfect foresight) -/

/-- Cochrane (2023), §8.4, p. 250: the continuous-time discount factor
`exp(−∫₀^τ r_{t+j} dj)` along a perfect-foresight real-rate path `r`. -/
noncomputable def cdisc (r : ℝ → ℝ) (τ : ℝ) : ℝ := Real.exp (-∫ u in (0 : ℝ)..τ, r u)

/-- Cochrane (2023), §8.4, p. 250: if the real value of the debt maturing at each date, `x(τ)`,
matches the surplus at that date, `s(τ)`, for all `τ ≥ 0`, then the present-value relation
`∫₀^∞ e^{−∫r} x = ∫₀^∞ e^{−∫r} s` holds for every real-rate path `r`: real rates cancel. -/
theorem matching_cancels {x s : ℝ → ℝ} (hm : ∀ τ, 0 ≤ τ → x τ = s τ) (r : ℝ → ℝ) :
    ∫ τ in Set.Ioi 0, cdisc r τ * x τ = ∫ τ in Set.Ioi 0, cdisc r τ * s τ := by
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  rw [hm τ (le_of_lt hτ)]

/-- Cochrane (2023), §8.4, p. 250 (price-level form): with nominal debt `B(τ)` maturing at
`t + τ`, the price path `P_{t+τ} = P_t Π(τ)` (relative path `Π` set by monetary policy), and
matching `B(τ)/Π(τ) = κ s(τ)` for `τ ≥ 0`, the valuation
`(1/P_t) ∫ e^{−∫r} B/Π = ∫ e^{−∫r} s` holds iff `P_t = κ`, for every real-rate path with
`∫ e^{−∫r} s ≠ 0`: the price level is insulated from real rates. -/
theorem price_insulated {Bm Pi s : ℝ → ℝ} {κ : ℝ} (hm : ∀ τ, 0 ≤ τ → Bm τ / Pi τ = κ * s τ)
    (r : ℝ → ℝ) (hS : ∫ τ in Set.Ioi 0, cdisc r τ * s τ ≠ 0) {P0 : ℝ} (hP0 : P0 ≠ 0) :
    (∫ τ in Set.Ioi 0, cdisc r τ * (Bm τ / Pi τ)) / P0 = ∫ τ in Set.Ioi 0, cdisc r τ * s τ ↔
      P0 = κ := by
  have hX : ∫ τ in Set.Ioi 0, cdisc r τ * (Bm τ / Pi τ) =
      κ * ∫ τ in Set.Ioi 0, cdisc r τ * s τ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [hm τ (le_of_lt hτ)]
    ring
  rw [hX, div_eq_iff hP0]
  constructor
  · intro h
    have h2 : (κ - P0) * ∫ τ in Set.Ioi 0, cdisc r τ * s τ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hS
  · intro h
    rw [h]
    ring

/-! ### The converse in discrete time -/

/-- Cochrane (2023), §8.4, p. 250 (discrete-time analogue): the discount factor
`∏_{j<τ} (1 + r_j)⁻¹` along a real-rate path `r`. -/
noncomputable def ddisc (r : ℕ → ℝ) (τ : ℕ) : ℝ := ∏ j ∈ Finset.range τ, (1 + r j)⁻¹

/-- Cochrane (2023), §8.4, p. 250: along the constant path `r_j = r̲` the discount factor is
`(1 + r̲)⁻ᵗ`. -/
theorem ddisc_const (rl : ℝ) (τ : ℕ) : ddisc (fun _ => rl) τ = ((1 + rl)⁻¹) ^ τ := by
  simp [ddisc]

/-- Cochrane (2023), §8.4, p. 250: raising the rate of a single period `k` from `r̲` to `2r̲`
multiplies every later discount factor by `c = (1 + r̲)/(1 + 2r̲)`. -/
theorem ddisc_bump {rl : ℝ} (hrl : 0 < rl) (k τ : ℕ) :
    ddisc (fun j => if j = k then 2 * rl else rl) τ =
      ((1 + rl)⁻¹) ^ τ * (if k < τ then (1 + rl) / (1 + 2 * rl) else 1) := by
  have h1 : (1 + rl) ≠ 0 := by linarith
  have h2 : (1 + 2 * rl) ≠ 0 := by linarith
  induction τ with
  | zero => simp [ddisc]
  | succ τ ih =>
    rw [ddisc, Finset.prod_range_succ, ← ddisc, ih, pow_succ]
    by_cases hτk : τ = k
    · subst hτk
      simp only [lt_self_iff_false, ↓reduceIte, lt_add_iff_pos_right, Nat.lt_one_iff,
        mul_one]
      field_simp
    · simp only [hτk, ↓reduceIte]
      by_cases hk : k < τ
      · have hk' : k < τ + 1 := by omega
        simp only [hk, ↓reduceIte, hk']
        ring
      · have hk' : ¬ k < τ + 1 := by omega
        simp only [hk, ↓reduceIte, hk', mul_one]

/-- Cochrane (2023), §8.4, pp. 250–251 ("otherwise, the mismatch ... determines how the price
level reacts to real interest rates"), the converse of `matching_cancels` in discrete time: if a
bounded mismatch stream `y` has zero present value along every real-rate path with rates at
least `r̲ > 0`, then `y = 0`. -/
theorem matching_necessary {rl M : ℝ} (hrl : 0 < rl) {y : ℕ → ℝ} (hy : ∀ τ, |y τ| ≤ M)
    (h : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) → ∑' τ, ddisc r τ * y τ = 0) : ∀ τ, y τ = 0 := by
  set q : ℝ := (1 + rl)⁻¹ with hq
  set c : ℝ := (1 + rl) / (1 + 2 * rl) with hc
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hgeo : Summable (fun τ : ℕ => q ^ τ * M) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_right M
  have hsum0 : Summable (fun τ => q ^ τ * y τ) :=
    Summable.of_norm_bounded hgeo fun τ => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hq0]
      exact mul_le_mul_of_nonneg_left (hy τ) (pow_nonneg hq0.le τ)
  -- base path
  have hbase : ∑' τ, q ^ τ * y τ = 0 := by
    have := h (fun _ => rl) (fun _ => le_rfl)
    simpa [ddisc_const, hq] using this
  -- head and tail decomposition
  set H : ℕ → ℝ := fun k => ∑ τ ∈ Finset.range (k + 1), q ^ τ * y τ with hH
  set T : ℕ → ℝ := fun k => ∑' τ, q ^ (τ + (k + 1)) * y (τ + (k + 1)) with hT
  have hHT : ∀ k, H k + T k = 0 := by
    intro k
    rw [← hbase]
    exact hsum0.sum_add_tsum_nat_add (k + 1)
  have hbumpH : ∀ k, H k + c * T k = 0 := by
    intro k
    have hk := h (fun j => if j = k then 2 * rl else rl) (fun j => by
      by_cases hj : j = k
      · simp only [hj, ↓reduceIte]; linarith
      · simp only [hj, ↓reduceIte, le_refl])
    have hform : (fun τ => ddisc (fun j => if j = k then 2 * rl else rl) τ * y τ) =
        fun τ => q ^ τ * y τ * (if k < τ then c else 1) := by
      funext τ
      rw [ddisc_bump hrl k τ]
      ring
    rw [hform] at hk
    have hsumk : Summable (fun τ => q ^ τ * y τ * (if k < τ then c else 1)) :=
      Summable.of_norm_bounded hgeo fun τ => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos hq0]
        have hif : |(if k < τ then c else 1)| ≤ 1 := by
          split_ifs
          · rw [abs_of_nonneg hc0]; exact hc1.le
          · simp
        calc q ^ τ * |y τ| * |(if k < τ then c else 1)| ≤ q ^ τ * M * 1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left (hy τ) (pow_nonneg hq0.le τ)) hif
                (abs_nonneg _)
              exact mul_nonneg (pow_nonneg hq0.le τ) ((abs_nonneg _).trans (hy τ))
          _ = q ^ τ * M := mul_one _
    have hsplit := hsumk.sum_add_tsum_nat_add (k + 1)
    rw [hk] at hsplit
    have hhead : ∑ τ ∈ Finset.range (k + 1), q ^ τ * y τ * (if k < τ then c else 1) = H k := by
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have : ¬ k < τ := by
        have := Finset.mem_range.mp hτ
        omega
      simp [this]
    have htail : ∑' τ, q ^ (τ + (k + 1)) * y (τ + (k + 1)) *
        (if k < τ + (k + 1) then c else 1) = c * T k := by
      rw [hT, ← tsum_mul_left]
      refine tsum_congr fun τ => ?_
      have : k < τ + (k + 1) := by omega
      simp only [this, ↓reduceIte]
      ring
    rw [hhead, htail] at hsplit
    exact hsplit
  have hHzero : ∀ k, H k = 0 := by
    intro k
    have h1 := hHT k
    have h2 := hbumpH k
    have hT0 : T k = 0 := by
      have : (1 - c) * T k = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · linarith
      · exact h3
    linarith
  intro τ
  cases τ with
  | zero =>
    have := hHzero 0
    simpa [hH] using this
  | succ n =>
    have h1 := hHzero (n + 1)
    have h0 := hHzero n
    simp only [hH] at h1 h0
    rw [Finset.sum_range_succ, h0, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 (pow_ne_zero _ hq0.ne')
    · exact h3

/-- Cochrane (2023), §8.4, pp. 250–251 (price-level form of the converse): with bounded debt
payoffs `x` (real value of debt maturing at `τ` per unit of the current price level) and
surpluses `s`, if the valuation `∑ d_τ x_τ / κ = ∑ d_τ s_τ` gives the same price level `κ ≠ 0`
along every real-rate path with rates at least `r̲ > 0`, then the maturity structure matches
the surpluses exactly, `x_τ = κ s_τ`. -/
theorem price_insulated_only_if_matching {rl Mx Ms κ : ℝ} (hrl : 0 < rl) (hκ : κ ≠ 0)
    {x s : ℕ → ℝ} (hx : ∀ τ, |x τ| ≤ Mx) (hs : ∀ τ, |s τ| ≤ Ms)
    (h : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) →
      (∑' τ, ddisc r τ * x τ) / κ = ∑' τ, ddisc r τ * s τ) :
    ∀ τ, x τ = κ * s τ := by
  have hd : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) → ∀ τ, 0 < ddisc r τ ∧ ddisc r τ ≤ 1 := by
    intro r hr τ
    constructor
    · exact Finset.prod_pos fun j _ => inv_pos.mpr (by linarith [hr j])
    · exact Finset.prod_le_one₀ (fun j _ => (inv_pos.mpr (by linarith [hr j])).le)
        fun j _ => inv_le_one_of_one_le₀ (by linarith [hr j])
  have hzero := matching_necessary hrl (y := fun τ => x τ - κ * s τ) (M := Mx + |κ| * Ms)
    (fun τ => by
      calc |x τ - κ * s τ| ≤ |x τ| + |κ * s τ| := abs_sub _ _
        _ ≤ Mx + |κ| * Ms := by
          rw [abs_mul]
          exact add_le_add (hx τ) (mul_le_mul_of_nonneg_left (hs τ) (abs_nonneg κ)))
    (fun r hr => by
      have hq1 : (1 + rl)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      have hq0 : 0 ≤ (1 + rl)⁻¹ := (inv_pos.mpr (by linarith)).le
      have hdle : ∀ τ, ddisc r τ ≤ ((1 + rl)⁻¹) ^ τ := by
        intro τ
        have hc : ((1 + rl)⁻¹) ^ τ = ∏ j ∈ Finset.range τ, (1 + rl)⁻¹ := by simp
        rw [ddisc, hc]
        exact Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (by linarith [hr j])).le)
          fun j _ => inv_anti₀ (by linarith) (by linarith [hr j])
      have hsx : Summable (fun τ => ddisc r τ * x τ) :=
        Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right Mx)
          fun τ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd r hr τ).1]
            exact mul_le_mul (hdle τ) (hx τ) (abs_nonneg _) (pow_nonneg hq0 τ)
      have hss : Summable (fun τ => ddisc r τ * s τ) :=
        Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right Ms)
          fun τ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd r hr τ).1]
            exact mul_le_mul (hdle τ) (hs τ) (abs_nonneg _) (pow_nonneg hq0 τ)
      have hval := h r hr
      rw [div_eq_iff hκ] at hval
      have e : (fun τ => ddisc r τ * (x τ - κ * s τ)) =
          fun τ => ddisc r τ * x τ - κ * (ddisc r τ * s τ) := by
        funext τ
        ring
      rw [e, hsx.tsum_sub (hss.mul_left κ), tsum_mul_left, hval]
      ring)
  intro τ
  have := hzero τ
  linarith

/-! ### Survey E8.3: matching is not enough under uncertainty -/

/-- Cochrane (2023), §8.4, p. 250 (survey E8.3): with stochastic real rates correlated with the
price level, matching the expected real payoff of maturing debt to the surplus does not cancel
the rates. In the coin-flip tree, a unit of debt maturing at `τ` with `E₀(1/P_τ) = 1 = s_τ`
(matching) and a positive discount factor `D` correlated with `1/P_τ` give
`E₀[D/P_τ] = 1 ≠ 3/4 = E₀[D s_τ]`. -/
theorem matching_fails_under_uncertainty :
    ∃ (D X : Bool × Bool → ℝ) (s : ℝ), (∀ ω, 0 < D ω) ∧
      ExpectationsFiniteTree.coinSystem.E 0 X = (fun _ => s) ∧
      ExpectationsFiniteTree.coinSystem.E 0 (D * X) ≠
        ExpectationsFiniteTree.coinSystem.E 0 (fun ω => D ω * s) := by
  set fh := ExpectationsFiniteTree.firstHeads with hfh
  set 𝔼 := ExpectationsFiniteTree.coinSystem with h𝔼
  have hE : ∀ ω, 𝔼.E 0 fh ω = 1 / 2 := ExpectationsFiniteTree.coinSystem_E0_firstHeads
  have hfh2 : ∀ ω, fh ω * fh ω = fh ω := by
    intro ω
    simp only [hfh, ExpectationsFiniteTree.firstHeads]
    split_ifs <;> norm_num
  refine ⟨fun ω => 1 / 2 + 1 / 2 * fh ω, (2 : ℝ) • fh, 1, fun ω => ?_, ?_, ?_⟩
  · have : 0 ≤ fh ω := by
      simp only [hfh, ExpectationsFiniteTree.firstHeads]
      split_ifs <;> norm_num
    linarith
  · funext ω
    rw [map_smul, Pi.smul_apply, hE ω, smul_eq_mul]
    norm_num
  · intro h
    have h1 : (fun ω => 1 / 2 + 1 / 2 * fh ω) * (2 : ℝ) • fh = (2 : ℝ) • fh := by
      funext ω
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      have := hfh2 ω
      linear_combination this
    have h2 : (fun ω => (1 / 2 + 1 / 2 * fh ω) * 1) =
        (fun _ => (1 / 2 : ℝ)) + (1 / 2 : ℝ) • fh := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, h2, map_add, map_smul, map_smul, 𝔼.const] at h
    have h3 := congrFun h (true, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE] at h3
    norm_num at h3

end Cochrane.AssetsRulesBalanceSheets.MaturityBuffer

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Default

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.5 (pp. 254–255),
eqs. (8.5)–(8.7).

A haircut `D_t` (each dollar of maturing debt pays `D_t` dollars) enters the valuation equation
`B_{t−1} D_t/P_t = E_t ∑ βʲ s_{t+j}` (8.5); an expected haircut `D_{t+1}` enters the bond price
`Q_t = β E_t(P_t D_{t+1}/P_{t+1})` (8.7) of the flow condition (8.6).

## Main results

* (8.5): `haircut_price_unique`, `haircut_offsets_shock` (an unexpected haircut `D = V'/V`
  absorbs a fall of the surplus present value from `V` to `V'` with no inflation).
* (8.6)–(8.7): `bondPrice`, `DefaultFlow`, `revenue_eq`, `defaultFlow_iff_solves`,
  `default_valuation_iff` ((8.5) at every date ⇔ flow + transversality), `default_flow_pv`
  ((8.6) in present-value form), `expected_default_no_effect` (an expected haircut with
  unchanged surpluses does not move `P_t`), `bondPrice_known_haircut`.
* p. 255: `bondPrice_scale`, `scaled_flow_iff` ("2 bonds at a 50% haircut = 1 bond at none":
  the equilibrium is invariant under `(B_t, D_t) ↦ (k B_t, D_t/k)`), `two_bonds_half_haircut`;
  `fixedQ_perfectForesight`, `fixedQ_next_price_mono` (with `Q_t` fixed, an expected haircut
  lowers `P_{t+1}`; it is equivalent to selling `D_{t+1} B_t` bonds with no haircut).
* p. 255, the 10% haircut example (survey E8.1): `haircut_ten_percent`,
  `haircut_factor_eq_iff`, `haircut_factor_lt`, `money_value_ten_percent_iff` — the price level
  rises by the exact factor `(s_t + V)/(s_t + 0.9 V)`, which is `10/9` (11.1%) only when
  `s_t = 0` and below `10/9` when `s_t > 0`; `rate_follows_premium` (if the interest rate
  follows the default premium, `P_{t+1}` rises by the same factor as `P_t`).
-/

namespace Cochrane.AssetsRulesBalanceSheets.Default

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (8.5): an unexpected haircut -/

/-- Cochrane (2023), eq. (8.5), p. 254: with a haircut `D_t`, `B_{t−1} D_t/P_t = V_t`; for
`B D > 0` and `V > 0` the price level is still determined, `P_t = B D/V`. -/
theorem haircut_price_unique {B D V : ℝ} (hBD : 0 < B * D) (hV : 0 < V) :
    ∃! P : ℝ, 0 < P ∧ B * D / P = V :=
  PresentValue.valuation_price_unique hBD hV

/-- Cochrane (2023), §8.5, p. 254: "An unexpected partial default allows the government to adapt
to a negative surplus shock with less or no inflation": if the price level `P` satisfied
`B/P = V` before the present value fell to `V'`, it still satisfies (8.5) with haircut `D` iff
`D = V'/V`. -/
theorem haircut_offsets_shock {B D V V' P : ℝ} (hV : V ≠ 0) (h0 : B / P = V) :
    B * D / P = V' ↔ D = V' / V := by
  have h1 : B * D / P = D * V := by rw [← h0]; ring
  rw [h1, eq_div_iff hV]

/-! ### (8.6)–(8.7): expected haircuts -/

/-- Cochrane (2023), eq. (8.7), p. 254: the nominal bond price with an expected haircut,
`Q_t = β E_t(P_t D_{t+1}/P_{t+1})`. -/
noncomputable def bondPrice (β : ℝ) (P D : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  β • 𝔼.E t (P t * D (t + 1) / P (t + 1))

/-- Cochrane (2023), eq. (8.6), p. 254, with a haircut at every date:
`B_{t−1} D_t/P_t = s_t + Q_t B_t/P_t` (the book's (8.6) is the case `D_t = 1`). -/
def DefaultFlow (β : ℝ) (B D P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t * D t / P t = s t + bondPrice 𝔼 β P D t * B (t + 1) / P t

/-- Cochrane (2023), eqs. (8.6)–(8.7), p. 254: with the pull-out property, an adapted nowhere-zero
price level and debt `B_t` chosen at `t`, the real revenue from bond sales is
`Q_t B_t/P_t = β E_t(B_t D_{t+1}/P_{t+1})`. -/
theorem revenue_eq (hPO : 𝔼.PullOut) {β : ℝ} {B D P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) (t : ℕ) :
    bondPrice 𝔼 β P D t * B (t + 1) / P t =
      β • 𝔼.E t (B (t + 1) * D (t + 1) / P (t + 1)) := by
  have e1 : P t * D (t + 1) / P (t + 1) = P t * (D (t + 1) / P (t + 1)) := mul_div_assoc _ _ _
  have e2 : B (t + 1) * D (t + 1) / P (t + 1) = B (t + 1) * (D (t + 1) / P (t + 1)) :=
    mul_div_assoc _ _ _
  rw [bondPrice, e1, e2, hPO t (P t) _ (hPa t), hPO t (B (t + 1)) _ (hBpre t)]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hP t ω]

/-- Cochrane (2023), eq. (8.6), p. 254: the flow with haircuts is the real recursion
`v_t = s_t + β E_t v_{t+1}` for the post-haircut real value `v_t = B_{t−1} D_t/P_t`. -/
theorem defaultFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {B D P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    DefaultFlow 𝔼 β B D P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => B t * D t / P t) := by
  simp only [DefaultFlow, ForwardSolution.Solves, revenue_eq 𝔼 hPO hPa hP hBpre]
  constructor
  · intro h t
    rw [h t, add_comm]
  · intro h t
    rw [h t, add_comm]

/-- Cochrane (2023), eqs. (8.5)–(8.6), p. 254: for bounded adapted surpluses and `0 ≤ β < 1`,
the flow with haircuts plus the transversality condition is equivalent to the valuation
equation `B_{t−1} D_t/P_t = E_t ∑ βʲ s_{t+j}` at every date. -/
theorem default_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B D P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (DefaultFlow 𝔼 β B D P s ∧ TVC 𝔼 β (fun t => B t * D t / P t)) ↔
      ∀ t, B t * D t / P t = pv 𝔼 β s t := by
  rw [defaultFlow_iff_solves 𝔼 hPO hPa hP hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa, funext_iff]

/-- Cochrane (2023), eq. (8.6), p. 254 (present-value form): in an equilibrium the real revenue
from new bonds is the present value of surpluses from `t + 1` on, whatever the expected haircut:
`B_{t−1} D_t/P_t = s_t + Q_t B_t/P_t = s_t + E_t ∑_{j ≥ 1} βʲ s_{t+j}`. -/
theorem default_flow_pv (hPO : 𝔼.PullOut) {β : ℝ} {B D P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1))
    (hflow : DefaultFlow 𝔼 β B D P s) (hval : ∀ t, B t * D t / P t = pv 𝔼 β s t) (t : ℕ) :
    B t * D t / P t = s t + 𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * s (t + 1 + j) ω) := by
  rw [hflow t, revenue_eq 𝔼 hPO hPa hP hBpre t, hval (t + 1), pv,
    𝔼.tower (Nat.le_succ t), ← map_smul]
  congr 2
  funext ω
  simp only [epv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), §8.5, p. 254: "If at time `t` people expect a partial default `D_{t+1} < 1`,
with no change in surpluses, this change has no effect on the current price level": two
equilibria with the same surpluses and the same post-haircut maturing debt at `t` have the same
`P_t`, whatever the expected haircuts and new debt. -/
theorem expected_default_no_effect {β : ℝ} {s B D P B' D' P' : ℕ → Ω → ℝ}
    (hv : ∀ t, B t * D t / P t = pv 𝔼 β s t) (hv' : ∀ t, B' t * D' t / P' t = pv 𝔼 β s t)
    {t : ℕ} {ω : Ω} (hBD : B t ω * D t ω = B' t ω * D' t ω) (hpv : pv 𝔼 β s t ω ≠ 0)
    (hP : P t ω ≠ 0) (hP' : P' t ω ≠ 0) : P t ω = P' t ω := by
  have h1 := congrFun (hv t) ω
  have h2 := congrFun (hv' t) ω
  simp only [Pi.div_apply, Pi.mul_apply] at h1 h2
  have hnum : B t ω * D t ω ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h1
    exact hpv h1.symm
  rw [div_eq_iff hP] at h1
  rw [div_eq_iff hP'] at h2
  rw [← hBD] at h2
  exact mul_left_cancel₀ hpv (h1.symm.trans h2)

/-- Cochrane (2023), eq. (8.7), p. 254: when the haircut `D_{t+1}` is announced at `t` (known at
`t`), the bond price is proportional to it, `Q_t = β P_t D_{t+1} E_t(1/P_{t+1})`: an expected
default lowers bond prices. -/
theorem bondPrice_known_haircut (hPO : 𝔼.PullOut) {β : ℝ} {P D : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) {t : ℕ} (hD : 𝔼.E t (D (t + 1)) = D (t + 1)) :
    bondPrice 𝔼 β P D t = β • (P t * D (t + 1) * 𝔼.E t (P (t + 1))⁻¹) := by
  have hPD : 𝔼.E t (P t * D (t + 1)) = P t * D (t + 1) := by
    rw [hPO t (P t) (D (t + 1)) (hPa t), hD]
  rw [bondPrice, div_eq_mul_inv, hPO t _ _ hPD]

/-! ### p. 255: the interest rate is free -/

/-- Cochrane (2023), §8.5, p. 255: scaling the expected haircut by `1/k` (a deterministic
`k ≠ 0`) scales the bond price by `1/k`. -/
theorem bondPrice_scale {β : ℝ} {P D : ℕ → Ω → ℝ} {k : ℕ → ℝ} (t : ℕ) :
    bondPrice 𝔼 β P (fun t => (k t)⁻¹ • D t) t = (k (t + 1))⁻¹ • bondPrice 𝔼 β P D t := by
  have e : P t * (k (t + 1))⁻¹ • D (t + 1) / P (t + 1) =
      (k (t + 1))⁻¹ • (P t * D (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [bondPrice, bondPrice, e, map_smul, smul_comm]

/-- Cochrane (2023), §8.5, p. 255: "Selling 2 bonds when people expect a 50% haircut is exactly
the same as selling 1 bond when people expect no haircut, except nominal bond prices fall by
half": the flow with haircuts is invariant under `(B_t, D_t) ↦ (k_t B_t, D_t/k_t)` for any
deterministic `k_t ≠ 0`, with the same price level. -/
theorem scaled_flow_iff {β : ℝ} {B D P s : ℕ → Ω → ℝ} {k : ℕ → ℝ} (hk : ∀ t, k t ≠ 0) :
    DefaultFlow 𝔼 β (fun t => k t • B t) (fun t => (k t)⁻¹ • D t) P s ↔
      DefaultFlow 𝔼 β B D P s := by
  have h1 : ∀ t, k t • B t * (k t)⁻¹ • D t = B t * D t := by
    intro t
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hk t]
  have h2 : ∀ t, bondPrice 𝔼 β P (fun t => (k t)⁻¹ • D t) t * k (t + 1) • B (t + 1) =
      bondPrice 𝔼 β P D t * B (t + 1) := by
    intro t
    rw [bondPrice_scale]
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hk (t + 1)]
  simp only [DefaultFlow, h1, h2]

/-- Cochrane (2023), §8.5, p. 255 (the book's example): with a 50% expected haircut the bond price
is half the no-haircut price. -/
theorem two_bonds_half_haircut {β : ℝ} {P D : ℕ → Ω → ℝ} (t : ℕ) :
    bondPrice 𝔼 β P (fun t => (2 : ℝ)⁻¹ • D t) t = (2 : ℝ)⁻¹ • bondPrice 𝔼 β P D t :=
  bondPrice_scale 𝔼 (k := fun _ => 2) t

/-- Cochrane (2023), §8.5, p. 255 (perfect foresight): if the government holds `Q_t` fixed, the
real revenue condition `Q_t B_t/P_t = β V_{t+1}` and the valuation `B_t D_{t+1}/P_{t+1} = V_{t+1}`
give `B_t = β V_{t+1} P_t/Q_t`, independent of the haircut, and `P_{t+1} = β P_t D_{t+1}/Q_t`: the
same as selling `D_{t+1} B_t` bonds with no haircut. -/
theorem fixedQ_perfectForesight {β P Q B D P1 V1 : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hV1 : V1 ≠ 0)
    (hP1 : P1 ≠ 0) (hrev : Q * B / P = β * V1) (hval : B * D / P1 = V1) :
    B = β * V1 * P / Q ∧ P1 = β * P * D / Q := by
  have hB : B = β * V1 * P / Q := by
    rw [eq_div_iff hQ, ← hrev]
    field_simp
  refine ⟨hB, ?_⟩
  rw [div_eq_iff hP1] at hval
  rw [eq_div_iff hQ]
  have : V1 * P1 * Q = V1 * (β * P * D) := by
    rw [← hval, hB]
    field_simp
  have := mul_left_cancel₀ hV1 (by rw [← this]; ring : V1 * (P1 * Q) = V1 * (β * P * D))
  linarith

/-- Cochrane (2023), §8.5, p. 255: "if the government sticks to the nominal interest-rate target
... the expected future price level `P_{t+1}` declines": `β P_t D/Q_t` is strictly increasing in
the haircut factor `D`. -/
theorem fixedQ_next_price_mono {β P Q D D' : ℝ} (hβ : 0 < β) (hP : 0 < P) (hQ : 0 < Q)
    (hD : D' < D) : β * P * D' / Q < β * P * D / Q := by
  apply div_lt_div_of_pos_right _ hQ
  exact mul_lt_mul_of_pos_left hD (mul_pos hβ hP)

/-! ### p. 255: the 10% haircut example (survey E8.1) -/

/-- Cochrane (2023), §8.5, p. 255: a 10% haircut at `t + 1` with surpluses from `t + 1` on 10%
lower (`V ↦ 0.9 V`, `s_t` unchanged) raises the price level by the exact factor
`(s_t + V)/(s_t + 0.9 V)`. -/
theorem haircut_ten_percent {B s V P P' : ℝ} (hB : B ≠ 0) (hsV : s + V ≠ 0)
    (hsV' : s + 9 / 10 * V ≠ 0) (hP : B / P = s + V) (hP' : B / P' = s + 9 / 10 * V) :
    P' / P = (s + V) / (s + 9 / 10 * V) := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, div_zero] at hP
    exact hsV hP.symm
  have hP0' : P' ≠ 0 := by
    intro h
    rw [h, div_zero] at hP'
    exact hsV' hP'.symm
  have e1 : P = B / (s + V) := by rw [eq_div_iff hsV, ← hP]; field_simp
  have e2 : P' = B / (s + 9 / 10 * V) := by rw [eq_div_iff hsV', ← hP']; field_simp
  rw [e1, e2]
  field_simp

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): the price-level factor is exactly `10/9` (an
11.1% rise) iff `s_t = 0`. -/
theorem haircut_factor_eq_iff {s V : ℝ} (hs' : 0 < s + 9 / 10 * V) :
    (s + V) / (s + 9 / 10 * V) = 10 / 9 ↔ s = 0 := by
  rw [div_eq_iff hs'.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): with a positive current surplus `s_t > 0` the
price-level factor is strictly below `10/9`. -/
theorem haircut_factor_lt {s V : ℝ} (hV : 0 < V) (hs : 0 < s) :
    (s + V) / (s + 9 / 10 * V) < 10 / 9 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): the value of money `1/P` falls by exactly 10%,
`(s + 0.9 V)/(s + V) = 9/10`, iff `s_t = 0` (for `s + V > 0`); the book's "raises the price level
today by 10%" is the first-order version of this. -/
theorem money_value_ten_percent_iff {s V : ℝ} (hsV : 0 < s + V) :
    (s + 9 / 10 * V) / (s + V) = 9 / 10 ↔ s = 0 := by
  rw [div_eq_iff hsV.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.5, p. 255 (perfect foresight): "If the government allows the interest
rate to rise, to follow the increased default premium, then by (8.7), the expected price level at
`t + 1` is also ... higher": with inflation `P_{t+1}/P_t` unchanged, `P_{t+1}` rises by the same
factor as `P_t`, and the bond price `Q_t = β P_t D_{t+1}/P_{t+1}` falls by the factor `D'/D`. -/
theorem rate_follows_premium {β P P1 P' P1' D D' : ℝ} (hP : P ≠ 0) (hP1 : P1 ≠ 0)
    (hP' : P' ≠ 0) (hD : D ≠ 0) (hinf : P1' / P' = P1 / P) :
    P1' / P1 = P' / P ∧ β * P' * D' / P1' = D' / D * (β * P * D / P1) := by
  have h : P1' = P1 * P' / P := by
    rw [div_eq_iff hP'] at hinf
    rw [hinf]
    field_simp
  constructor
  · rw [h]
    field_simp
  · rw [h]
    field_simp

end Cochrane.AssetsRulesBalanceSheets.Default

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Central bank independence

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.6 (pp. 256–258).
§8.6 is largely institutional; this module formalises its precise claims.

## Main results

* `cb_purchase_neutral` (p. 256): a central-bank purchase of treasury debt paid for with
  reserves is the same as the treasury issuing reserves directly; the consolidated valuation
  equation, and hence the price level, is unchanged.
* `cash_left_pos_iff`, `cash_left_zero_iff` (p. 257, "inflation in the end comes from too much
  cash"): the government prints `B_{t−1}` to redeem maturing debt and soaks money up with
  surpluses and new debt; cash is left over exactly when the price level is below its
  equilibrium value.
* `unified_inflates`, `independence_default_vs_inflation` (p. 257; the default half is
  `RealDebt.haircut_of_fixed_price`): when an independent central bank pins the price level, a
  shortfall of treasury surpluses must be met by explicit default; when the treasury can print,
  the same shortfall is met by inflation.
-/

namespace Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence

open RealDebt

/-- Cochrane (2023), §8.6, p. 256: "If the treasury issues debt, the central bank buys that debt
and issues reserves or cash, it is the same as the treasury issuing reserves or cash rather than
treasury debt directly": moving `x` from publicly held treasury debt to reserves leaves the
consolidated valuation equation `(B + M)/P = V` unchanged. -/
theorem cb_purchase_neutral (B M x P V : ℝ) :
    ((B - x) + (M + x)) / P = V ↔ (B + M) / P = V := by
  rw [show (B - x) + (M + x) = B + M by ring]

/-- Cochrane (2023), §8.6, p. 257: the cash left in private hands at the end of date `t`, when
the government prints `B_{t−1}` to redeem maturing debt and soaks up `P_t s_t` with surpluses and
`P_t q_t` with new debt sales (`q_t = Q_t B_t/P_t` the real revenue). -/
def cashLeft (B P s q : ℝ) : ℝ := B - P * (s + q)

/-- Cochrane (2023), §8.6, p. 257: with positive real backing `s + q > 0`, cash is left over —
"too much cash" — exactly when the price level is below the value set by the flow condition,
`P < B/(s + q)`. -/
theorem cash_left_pos_iff {B P s q : ℝ} (hsq : 0 < s + q) :
    0 < cashLeft B P s q ↔ P < B / (s + q) := by
  rw [cashLeft, lt_div_iff₀ hsq]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.6, p. 257: no cash is left over iff the flow condition
`B_{t−1}/P_t = s_t + q_t` holds (for a nonzero price level). -/
theorem cash_left_zero_iff {B P s q : ℝ} (hP : P ≠ 0) :
    cashLeft B P s q = 0 ↔ B / P = s + q := by
  rw [cashLeft, div_eq_iff hP, sub_eq_zero, mul_comm]

/-- Cochrane (2023), §8.6, p. 257 (contrast): if the treasury can print money to redeem its debt
(no default, `D = 1`), the valuation `B/P = V` with `B, V > 0` sets `P = B/V`, which exceeds a
target `P̄ > 0` iff `V < B/P̄`. -/
theorem unified_inflates {B Pbar V P : ℝ} (hB : 0 < B) (hP : 0 < Pbar) (hV : 0 < V)
    (hval : B / P = V) : P = B / V ∧ (Pbar < P ↔ V < B / Pbar) := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, div_zero] at hval
    exact hV.ne hval
  have hPe : P = B / V := by
    rw [eq_div_iff hV.ne', ← hval]
    field_simp
  refine ⟨hPe, ?_⟩
  rw [hPe, lt_div_iff₀ hV, lt_div_iff₀ hP, mul_comm]

/-- Cochrane (2023), §8.6, p. 257: the same fiscal shortfall `V < B/P̄` produces explicit default
(`D < 1` at `P = P̄`) under an independent central bank and inflation (`P > P̄` with `D = 1`) under
a unified treasury and central bank. -/
theorem independence_default_vs_inflation {B Pbar V D P : ℝ} (hB : 0 < B) (hP : 0 < Pbar)
    (hV : 0 < V) (hshort : V < B / Pbar) (hind : B * D / Pbar = V) (huni : B / P = V) :
    D < 1 ∧ Pbar < P :=
  ⟨((haircut_of_fixed_price hB hP hind).2.2).mpr hshort,
    ((unified_inflates hB hP hV huni).2).mpr hshort⟩

end Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pots of assets: nominal liabilities backed by real assets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.1.1–10.1.2
(pp. 288–294), eqs. (10.1)–(10.6); and the real-bills doctrine of §11.5 (p. 322), which the
Chapters 11–19 survey assigns here.

A central bank issues nominal liabilities `B` and holds `b̂` shares of a real asset paying `ŝ`
per share, with ex-dividend price `q̂_t = E_t ∑ β^{j+1} ŝ_{t+1+j}` (10.1). Timing as in
`RealDebt`: `B t` is `B_{t−1}` and `bh t` is `b̂_{t−1}`, the holdings entering date `t`.

## Main results

* §10.1.1: `B_{t−1}/P_t = b_t` determines `P_t` (`PresentValue.valuation_price_unique`);
  `pot_unique_of_strictMono` and
  `pot_exists_of_continuous` (assets whose nominal value `P b(P)` is strictly increasing
  determine the price level), `pot_nominal_assets` (purely nominal assets cannot),
  `share_split` (varying `B_t` alone sets the future price level). The nominal flow on p. 290 is
  `RealDebt.nominalFlow_iff_solves`.
* (10.1)–(10.6): `qhat`, `qhat_recursion`, `pv_eq_sh_add_qhat`, `PotFlow` (10.2), `potX`,
  `potX_eq_pv_form`, `beta_E_potX`,
  `potFlow_iff_X` ((10.4)/(10.6): `X_t = β E_t X_{t+1}`), `PresentValue.eq_zero_of_tvc`
  ("both sides must be zero"), `pot_valuation_iff` ((10.3) ⇔ flow + transversality),
  `pot_valuation_pv` (the middle expression of (10.3)), `eq_10_5_eq_10_4` (survey E10.3:
  dropping `E_{t+1}` in (10.5) is harmless).
* Purchases at market prices: `purchases_irrelevant` (`P_t` does not depend on `b̂_t`) and
  `purchases_matched` (`β E_t(B_t/P_{t+1}) = q̂_t b̂_t`).
* §10.1.2: `sell_profit_pos_iff`, `buy_profit_pos_iff`, `no_arbitrage_iff` (a right to convert
  dollars and asset shares at `b̂_{t−1}/B_{t−1}` is arbitrage-free iff (10.3) holds);
  `discounted_wealth_const`, `wealth_tvc_iff`, `wealth_noPonzi_iff`, `wealth_explodes_pos`,
  `wealth_explodes_neg` (p. 294, the asymmetry of the transversality condition).
* §11.5 real bills: `real_bills_real_asset`, `real_bills_nominal_asset`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.PotOfAssets

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §10.1.1 Nominal debt and real assets -/

/-- Cochrane (2023), §10.1.1, p. 289: "It is enough that their value does not decline one-for-one
with the price level": if the nominal value of the assets `P ↦ P b(P)` is strictly increasing on
`P > 0`, then `B/P = b(P)` has at most one positive solution. -/
theorem pot_unique_of_strictMono {B : ℝ} {bf : ℝ → ℝ}
    (hN : StrictMonoOn (fun P => P * bf P) (Set.Ioi 0)) {P₁ P₂ : ℝ} (h1 : 0 < P₁)
    (h2 : 0 < P₂) (e1 : B / P₁ = bf P₁) (e2 : B / P₂ = bf P₂) : P₁ = P₂ := by
  have n1 : P₁ * bf P₁ = B := by rw [← e1]; field_simp
  have n2 : P₂ * bf P₂ = B := by rw [← e2]; field_simp
  exact price_unique_of_strictMonoOn hN h1 h2 n1.symm n2.symm

/-- Cochrane (2023), §10.1.1, p. 289: existence — if the nominal value `P ↦ P b(P)` is continuous
on `[p₁, p₂]` (`0 < p₁ ≤ p₂`) and the nominal liabilities `B` lie between its end values, some
price level in `[p₁, p₂]` solves `B/P = b(P)`. -/
theorem pot_exists_of_continuous {B p₁ p₂ : ℝ} {bf : ℝ → ℝ} (hp₁ : 0 < p₁) (hp : p₁ ≤ p₂)
    (hc : ContinuousOn (fun P => P * bf P) (Set.Icc p₁ p₂)) (hlo : p₁ * bf p₁ ≤ B)
    (hhi : B ≤ p₂ * bf p₂) : ∃ P ∈ Set.Icc p₁ p₂, B / P = bf P := by
  obtain ⟨P, hPmem, hPB⟩ := intermediate_value_Icc hp hc ⟨hlo, hhi⟩
  refine ⟨P, hPmem, ?_⟩
  have hP0 : P ≠ 0 := (lt_of_lt_of_le hp₁ hPmem.1).ne'
  rw [← hPB]
  field_simp

/-- Cochrane (2023), §10.1, p. 288: "nominal assets and nominal liabilities cannot define a
numeraire or determine the price level": if the assets are nominal, `b(P) = A/P`, then
`B/P = b(P)` holds at one nonzero price level iff it holds at every one (iff `B = A`). -/
theorem pot_nominal_assets {B A P : ℝ} (hP : P ≠ 0) : B / P = A / P ↔ B = A := by
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), §10.1.1, p. 289: the bank "can set expected inflation ... by varying nominal
debt `B_t` without changing the amount of real securities, effectively by share splits":
multiplying the nominal debt by `k` multiplies the price level that solves `B/P = v` by `k`. -/
theorem share_split {B P v k P' : ℝ} (hP : P ≠ 0) (hv : v ≠ 0) (hP' : P' ≠ 0)
    (h : B / P = v) : k * B / P' = v ↔ P' = k * P := by
  have hB : B = v * P := by rw [← h]; field_simp
  rw [hB, div_eq_iff hP']
  constructor
  · intro h2
    have : v * (k * P) = v * P' := by rw [← h2]; ring
    exact (mul_left_cancel₀ hv this).symm
  · intro h2
    rw [h2]
    ring

/-! ### (10.1)–(10.6) A managed portfolio of real assets -/

/-- Cochrane (2023), eq. (10.1), p. 290: the real ex-dividend price per share,
`q̂_t = E_t ∑_{j ≥ 0} β^{j+1} ŝ_{t+1+j}`. -/
noncomputable def qhat (β : ℝ) (sh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω)

/-- Cochrane (2023), eq. (10.1), p. 290: the share price satisfies the pricing recursion
`q̂_t = β E_t(ŝ_{t+1} + q̂_{t+1})` whenever the discounted dividends are summable state by
state. -/
theorem qhat_recursion {β : ℝ} {sh : ℕ → Ω → ℝ}
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    qhat 𝔼 β sh t = β • 𝔼.E t (sh (t + 1) + qhat 𝔼 β sh (t + 1)) := by
  have hpath : (fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω) =
      β • (sh (t + 1) + fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + 1 + j) ω) := by
    funext ω
    have hs : Summable (fun j => β ^ (j + 1) * sh (t + 1 + j) ω) :=
      ((hsum (t + 1) ω).mul_left β).congr fun j => by ring
    rw [hs.tsum_eq_zero_add]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · simp
    · exact tsum_congr fun j => by
        rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
        ring
  simp only [qhat]
  rw [hpath, map_smul, map_add, map_add, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (10.3), p. 291: the cum-dividend value of a share is
`E_t ∑_{j ≥ 0} βʲ ŝ_{t+j} = ŝ_t + q̂_t` for adapted summable dividends. -/
theorem pv_eq_sh_add_qhat {β : ℝ} {sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    pv 𝔼 β sh t = sh t + qhat 𝔼 β sh t := by
  have hpath : epv β sh t = sh t + fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω := by
    funext ω
    simp only [epv, Pi.add_apply]
    rw [(hsum t ω).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    exact tsum_congr fun j => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [pv, hpath, map_add, hsa t, qhat]

/-- Cochrane (2023), eq. (10.2), p. 290: the bank's flow condition with asset purchases,
`B_{t−1}/P_t = b̂_{t−1} ŝ_t + β E_t(B_t/P_{t+1}) − q̂_t (b̂_t − b̂_{t−1})`. -/
def PotFlow (β : ℝ) (B P bh sh : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t / P t = bh t * sh t + β • 𝔼.E t (B (t + 1) / P (t + 1)) -
    qhat 𝔼 β sh t * (bh (t + 1) - bh t)

/-- Cochrane (2023), eq. (10.6), p. 293: the net value
`X_t = B_{t−1}/P_t − b̂_{t−1}(ŝ_t + q̂_t)`. -/
noncomputable def potX (β : ℝ) (B P bh sh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  B t / P t - bh t * (sh t + qhat 𝔼 β sh t)

/-- Cochrane (2023), eqs. (10.4) and (10.6), pp. 291, 293: for adapted summable dividends the net
value in (10.6) is the left-hand side of (10.4),
`X_t = B_{t−1}/P_t − b̂_{t−1} E_t ∑ βʲ ŝ_{t+j}`. -/
theorem potX_eq_pv_form {β : ℝ} {B P bh sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    potX 𝔼 β B P bh sh t = B t / P t - bh t * pv 𝔼 β sh t := by
  rw [potX, pv_eq_sh_add_qhat 𝔼 hsa hsum t]

/-- Cochrane (2023), eq. (10.4), p. 291: with the pull-out property and holdings `b̂_t` chosen at
`t`, `β E_t X_{t+1} = β E_t(B_t/P_{t+1}) − b̂_t q̂_t`. -/
theorem beta_E_potX (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    β • 𝔼.E t (potX 𝔼 β B P bh sh (t + 1)) =
      β • 𝔼.E t (B (t + 1) / P (t + 1)) - bh (t + 1) * qhat 𝔼 β sh t := by
  rw [potX, map_sub, hPO t _ _ (hbpre t), qhat_recursion 𝔼 hsum t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eqs. (10.4) and (10.6), pp. 291, 293: the flow condition (10.2) holds at
every date iff the net value satisfies `X_t = β E_t X_{t+1}`. -/
theorem potFlow_iff_X (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) :
    PotFlow 𝔼 β B P bh sh ↔
      ∀ t, potX 𝔼 β B P bh sh t = β • 𝔼.E t (potX 𝔼 β B P bh sh (t + 1)) := by
  simp only [PotFlow, beta_E_potX 𝔼 hPO hbpre hsum]
  simp only [potX, funext_iff, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
    smul_eq_mul]
  constructor
  · intro h t ω
    linarith [h t ω]
  · intro h t ω
    linarith [h t ω]

/-- Cochrane (2023), eq. (10.3), p. 291: the flow (10.2) at every date plus the transversality
condition on `X` is equivalent to `B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)` at every date: the value
of nominal debt equals the value of the bank's assets. -/
theorem pot_valuation_iff (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) :
    (PotFlow 𝔼 β B P bh sh ∧ TVC 𝔼 β (potX 𝔼 β B P bh sh)) ↔
      ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
  have hzero_iff : (∀ t, potX 𝔼 β B P bh sh t = 0) ↔
      ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
    simp only [potX, sub_eq_zero]
  rw [← hzero_iff, potFlow_iff_X 𝔼 hPO hbpre hsum]
  constructor
  · rintro ⟨hX, htvc⟩
    exact eq_zero_of_tvc 𝔼 hX htvc
  · intro h0
    refine ⟨fun t => ?_, fun t ω => ?_⟩
    · rw [h0 t, h0 (t + 1), map_zero, smul_zero]
    · simp only [h0, map_zero, Pi.zero_apply, mul_zero]
      exact tendsto_const_nhds

/-- Cochrane (2023), eq. (10.3), p. 291 (middle expression): for adapted summable dividends,
`B_{t−1}/P_t = b̂_{t−1} E_t ∑ βʲ ŝ_{t+j}` is the same condition as
`B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)`. -/
theorem pot_valuation_pv {β : ℝ} {B P bh sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    B t / P t = bh t * pv 𝔼 β sh t ↔ B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
  rw [pv_eq_sh_add_qhat 𝔼 hsa hsum t]

/-- Cochrane (2023), eqs. (10.4)–(10.5), pp. 291, 293 (survey E10.3): (10.5) drops the
`E_{t+1}` inside the second term of (10.4); with the pull-out property and `b̂_t` known at `t`
the two right-hand sides are equal, so the omission is harmless. -/
theorem eq_10_5_eq_10_4 (hPO : 𝔼.PullOut) {t : ℕ} {Bn Pn bn Y : Ω → ℝ}
    (hb : 𝔼.E t bn = bn) :
    𝔼.E t (Bn / Pn - bn * 𝔼.E (t + 1) Y) = 𝔼.E t (Bn / Pn - bn * Y) := by
  rw [map_sub, map_sub, hPO t _ _ hb, hPO t _ _ hb, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 291: asset purchases at market prices do not affect the price level:
two equilibria with the same maturing nominal debt `B_{t−1}`, the same holdings `b̂_{t−1}` and
the same dividends have the same `P_t`, whatever the new purchases `b̂_t`. -/
theorem purchases_irrelevant {β : ℝ} {B P P' bh bh' sh : ℕ → Ω → ℝ}
    (hv : ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t))
    (hv' : ∀ t, B t / P' t = bh' t * (sh t + qhat 𝔼 β sh t)) {t : ℕ} {ω : Ω}
    (hbh : bh t ω = bh' t ω) (hB : B t ω ≠ 0) (hP : P t ω ≠ 0) (hP' : P' t ω ≠ 0) :
    P t ω = P' t ω := by
  have h1 := congrFun (hv t) ω
  have h2 := congrFun (hv' t) ω
  simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply] at h1 h2
  rw [← hbh, ← h1] at h2
  field_simp at h2
  exact mul_left_cancel₀ hB (by rw [mul_comm, h2, mul_comm])

/-- Cochrane (2023), p. 291: "Any increase in real assets ... is matched exactly by an increase in
the value of nominal liabilities": in an equilibrium, `β E_t(B_t/P_{t+1}) = b̂_t q̂_t`. -/
theorem purchases_matched (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω))
    (hv : ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t)) (t : ℕ) :
    β • 𝔼.E t (B (t + 1) / P (t + 1)) = bh (t + 1) * qhat 𝔼 β sh t := by
  have h0 : potX 𝔼 β B P bh sh (t + 1) = 0 := by
    rw [potX, hv (t + 1), sub_self]
  have h := beta_E_potX 𝔼 hPO hbpre hsum (B := B) (P := P) t
  rw [h0, map_zero, smul_zero] at h
  exact (sub_eq_zero.mp h.symm)

/-! ### §10.1.2 A right to trade real assets -/

/-- Cochrane (2023), §10.1.2, p. 293: selling one share (cum-dividend value `v = ŝ_t + q̂_t`) to
the bank at `B_{t−1}/b̂_{t−1}` dollars per share is profitable iff the price level is too low,
`B_{t−1}/P_t > b̂_{t−1} v`. -/
theorem sell_profit_pos_iff {B P bh v : ℝ} (hbh : 0 < bh) (hP : 0 < P) :
    0 < B / (bh * P) - v ↔ bh * v < B / P := by
  rw [sub_pos, lt_div_iff₀ (mul_pos hbh hP), lt_div_iff₀ hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.1.2, p. 294: buying `b̂_{t−1}/B_{t−1}` shares from the bank with one
dollar is profitable iff the price level is too high, `B_{t−1}/P_t < b̂_{t−1} v`. -/
theorem buy_profit_pos_iff {B P bh v : ℝ} (hB : 0 < B) (hP : 0 < P) :
    0 < bh / B * v - 1 / P ↔ B / P < bh * v := by
  rw [sub_pos, div_lt_iff₀ hP, div_mul_eq_mul_div, div_mul_eq_mul_div, lt_div_iff₀ hB,
    div_lt_iff₀ hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.1.2, pp. 293–294: with the conversion right, there is no profitable
trade in either direction iff the value of the bank's liabilities equals the value of its
assets, `B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)`. -/
theorem no_arbitrage_iff {B P bh v : ℝ} (hbh : 0 < bh) (hB : 0 < B) (hP : 0 < P) :
    (¬ 0 < B / (bh * P) - v ∧ ¬ 0 < bh / B * v - 1 / P) ↔ B / P = bh * v := by
  rw [sell_profit_pos_iff hbh hP, buy_profit_pos_iff hB hP]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  · intro h
    rw [h]
    exact ⟨lt_irrefl _, lt_irrefl _⟩

/-- Cochrane (2023), p. 293: in perfect foresight, if `X_t = β X_{t+1}` then the discounted
net private wealth `βᵀ X_{t+T}` is constant, equal to `X_t`. -/
theorem discounted_wealth_const {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1))
    (t T : ℕ) : β ^ T * X (t + T) = X t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [← ih, hX (t + T), pow_succ, show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), p. 294: the transversality condition `βᵀ X_{t+T} → 0` holds iff the
initial gap is zero, `X_t = 0`. -/
theorem wealth_tvc_iff {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1)) (t : ℕ) :
    Tendsto (fun T : ℕ => β ^ T * X (t + T)) atTop (𝓝 0) ↔ X t = 0 := by
  simp_rw [discounted_wealth_const hX t]
  constructor
  · intro h
    exact tendsto_nhds_unique tendsto_const_nhds h
  · intro h
    rw [h]
    exact tendsto_const_nhds

/-- Cochrane (2023), p. 294 ("negative net wealth ... is eventually ruled out by a budget
constraint"): the no-Ponzi condition `βᵀ X_{t+T} ≥ 0` for all `T` holds iff `X_t ≥ 0`; positive
net wealth violates only optimality (the transversality condition), not the budget
constraint. -/
theorem wealth_noPonzi_iff {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1)) (t : ℕ) :
    (∀ T, 0 ≤ β ^ T * X (t + T)) ↔ 0 ≤ X t := by
  simp_rw [discounted_wealth_const hX t]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- Cochrane (2023), p. 293: "If `P_t` is too low ... the net value grows at the real interest
rate": with `0 < β < 1` and `X_t > 0`, `X_{t+T} → +∞`. -/
theorem wealth_explodes_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℕ → ℝ}
    (hX : ∀ t, X t = β * X (t + 1)) {t : ℕ} (hpos : 0 < X t) :
    Tendsto (fun T => X (t + T)) atTop atTop := by
  have hgrow : ∀ T, X (t + T) = (β⁻¹) ^ T * X t := by
    intro T
    rw [← discounted_wealth_const hX t T, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hβ0.ne',
      one_pow, one_mul]
  simp_rw [hgrow]
  exact Tendsto.atTop_mul_const hpos
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.mpr hβ1))

/-- Cochrane (2023), p. 294: with `0 < β < 1` and `X_t < 0`, `X_{t+T} → −∞` (ruled out by the
budget constraint). -/
theorem wealth_explodes_neg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℕ → ℝ}
    (hX : ∀ t, X t = β * X (t + 1)) {t : ℕ} (hneg : X t < 0) :
    Tendsto (fun T => X (t + T)) atTop atBot := by
  have hX' : ∀ t, (-X) t = β * (-X) (t + 1) := fun t => by
    simp only [Pi.neg_apply]
    rw [hX t]
    ring
  have h := wealth_explodes_pos hβ0 hβ1 hX' (t := t) (by simp only [Pi.neg_apply]; linarith)
  exact Tendsto.congr (fun T => by simp) (tendsto_neg_atTop_atBot.comp h)

/-! ### §11.5 Real bills (p. 322) -/

/-- Cochrane (2023), §11.5, p. 322 (Chapters 11–19 survey V7): issuing `ΔM` of money against a
real asset worth `ΔM/P` at the initial price level `P` (with `B/P = V`) adds equally to both sides
of the valuation equation; the new equation `(B + ΔM)/P' = V + ΔM/P` holds iff `P' = P`. -/
theorem real_bills_real_asset {B ΔM V P P' : ℝ} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hBM : B + ΔM ≠ 0) (h : B / P = V) : (B + ΔM) / P' = V + ΔM / P ↔ P' = P := by
  rw [← h, ← add_div]
  constructor
  · intro h2
    rw [div_eq_div_iff hP' hP] at h2
    exact (mul_left_cancel₀ hBM h2).symm
  · intro h2
    rw [h2]

/-- Cochrane (2023), §11.5, p. 322: if instead the bill is nominal (worth `ΔM/P'` at any price
level `P'`), the new valuation equation `(B + ΔM)/P' = V + ΔM/P'` has exactly the same solutions
as the old one, `B/P' = V`. -/
theorem real_bills_nominal_asset (B ΔM V P' : ℝ) :
    (B + ΔM) / P' = V + ΔM / P' ↔ B / P' = V := by
  rw [add_div]
  constructor <;> intro h <;> linarith

end Cochrane.AssetsRulesBalanceSheets.PotOfAssets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Shares as money

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.1.3 (pp. 295–297),
eq. (10.7).

A potato farm with `N` shares sells `s_t` potatoes a day for its own shares and pays the shares
back out as dividends; `P_t` is the number of shares per potato. Then the farm's indexed
perpetuities, or one-period indexed bonds, are used as the numeraire.

## Main results

* `ShareFlow`, `shareFlow_iff_solves`, `pv_smul`, `share_valuation_iff` (a share that pays only
  shares is worth `(1/N) E_t ∑ βʲ s_{t+j}` potatoes), `potato_price_level`
  (`N/P_t = E_t ∑ βʲ s_{t+j}`; uniqueness is `PresentValue.valuation_price_unique`).
* (10.7): `pv_one`, `perpetuity_real_value` (`E_t ∑ βʲ P_{t+j}/P_{t+j} = 1/(1 − β)`),
  `one_sub_beta_inv` (`= (1 + r)/r`), `perpetuity_price_level`,
  `perpetuity_price_level_process` (`P_t = (1 + y) r/((1 + r) y)`), and survey E10.1: the printed
  `P_t = (1 + r) y/((1 + y) r)` is the reciprocal (`printed_reciprocal`), equal only when `y = r`
  (`printed_eq_iff`, `printed_counterexample`); `price_level_one_iff` (`P_t = 1` iff `y = r`,
  the book's conclusion is unaffected); `potato_perpetuity_unit`.
* `pv_sub_const`, `perpetuity_backing_bound`: positive equity bounds the perpetuities by the
  present value of potato sales.
* One-period indexed bonds as numeraire (survey E10.2): `oneperiod_real_value` (worth `β` goods),
  `oneperiod_price_level` (`P_t = 1/β`, so each maturing bond is redeemed for `1/β` new bonds),
  `printed_beta_wrong` (the printed `P_t = β` is wrong for `0 < β < 1`),
  `numeraire_one_plus_y`; survey E10.4: `bond_value_le`, `bond_value_no_default` (no default
  needs only `M_t ≤ s_{t+1}`, weak inequality).
-/

namespace Cochrane.AssetsRulesBalanceSheets.SharesAsMoney

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Potato-farm shares as money -/

/-- Cochrane (2023), §10.1.3, p. 295: the real value `v_t` of a share that pays `P_t s_t/N`
shares as its date-`t` dividend, each share being worth `1/P_t` potatoes:
`v_t = (P_t s_t/N)/P_t + β E_t v_{t+1}`. -/
def ShareFlow (β N : ℝ) (P s v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, v t = (fun ω => P t ω * s t ω / N / P t ω) + β • 𝔼.E t (v (t + 1))

/-- Cochrane (2023), §10.1.3, p. 295: "the value of shares is the same as if dividends delivered
potatoes": with a nowhere-zero price level the share flow is `v_t = s_t/N + β E_t v_{t+1}`. -/
theorem shareFlow_iff_solves {β N : ℝ} {P s v : ℕ → Ω → ℝ} (hN : N ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) :
    ShareFlow 𝔼 β N P s v ↔ ForwardSolution.Solves 𝔼 β (fun t => N⁻¹ • s t) v := by
  have e : ∀ t, (fun ω => P t ω * s t ω / N / P t ω) = N⁻¹ • s t := by
    intro t
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hP t ω]
  simp only [ShareFlow, ForwardSolution.Solves, e]
  constructor <;> intro h t <;> rw [h t, add_comm]

/-- Cochrane (2023), §10.1.3, p. 295: the present value is linear in a constant scale factor,
`E_t ∑ βʲ (c s_{t+j}) = c E_t ∑ βʲ s_{t+j}`. -/
theorem pv_smul (β c : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pv 𝔼 β (fun t => c • s t) t = c • pv 𝔼 β s t := by
  have h : epv β (fun t => c • s t) t = c • epv β s t := by
    funext ω
    simp only [epv, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [pv, h, map_smul, pv]

/-- Cochrane (2023), §10.1.3, p. 295: for bounded adapted potato sales and `0 ≤ β < 1`, the share
flow plus the transversality condition is equivalent to the share value
`v_t = (1/N) E_t ∑ βʲ s_{t+j}`. -/
theorem share_valuation_iff {β M N : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hN : N ≠ 0)
    {P s v : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hP : ∀ t ω, P t ω ≠ 0) :
    (ShareFlow 𝔼 β N P s v ∧ TVC 𝔼 β v) ↔ ∀ t, v t = N⁻¹ • pv 𝔼 β s t := by
  have hs' : ∀ t ω, |(fun t => N⁻¹ • s t) t ω| ≤ |N⁻¹| * M := by
    intro t ω
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hs t ω) (abs_nonneg _)
  have hsa' : 𝔼.Adapted (fun t => N⁻¹ • s t) := fun t => by
    simp only [map_smul, hsa t]
  rw [shareFlow_iff_solves 𝔼 hN hP, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs' hsa', funext_iff]
  simp only [pv_smul]

/-- Cochrane (2023), §10.1.3, p. 295: "The real value of a share in the goods market must be the
same as the real value of a share in the asset market": with share value `1/P_t`,
`N/P_t = E_t ∑ βʲ s_{t+j}`. -/
theorem potato_price_level {β N : ℝ} (hN : N ≠ 0) {P s v : ℕ → Ω → ℝ}
    (hval : ∀ t, v t = N⁻¹ • pv 𝔼 β s t) (hgoods : ∀ t, v t = (P t)⁻¹) (t : ℕ) (ω : Ω) :
    N / P t ω = pv 𝔼 β s t ω := by
  have h1 := congrFun (hval t) ω
  have h2 := congrFun (hgoods t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.inv_apply] at h1 h2
  rw [div_eq_mul_inv, ← h2, h1]
  field_simp

/-! ### Indexed perpetuities as numeraire: (10.7) -/

/-- Cochrane (2023), eq. (10.7), p. 296: a claim to one good every period is worth
`∑ βʲ = 1/(1 − β)` at every date, `0 ≤ β < 1`. -/
theorem pv_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    pv 𝔼 β (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t = fun _ => (1 - β)⁻¹ := by
  have h : epv β (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t = fun _ => (1 - β)⁻¹ := by
    funext ω
    simp only [epv, mul_one]
    exact tsum_geometric_of_lt_one hβ0 hβ1
  rw [pv, h, 𝔼.const]

/-- Cochrane (2023), eq. (10.7), p. 296: the perpetuity pays `P_{t+j}` dollars, i.e. one potato,
every period, so its real value is `E_t ∑ βʲ P_{t+j}/P_{t+j} = 1/(1 − β)` (nowhere-zero `P`). -/
theorem perpetuity_real_value {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    pv 𝔼 β (fun t ω => P t ω / P t ω) t = fun _ => (1 - β)⁻¹ := by
  have h : (fun t ω => P t ω / P t ω) = fun (_ : ℕ) (_ : Ω) => (1 : ℝ) := by
    funext t ω
    exact div_self (hP t ω)
  rw [h, pv_one 𝔼 hβ0 hβ1]

/-- Cochrane (2023), eq. (10.7), p. 296: with `β = 1/(1 + r)`, `r > 0`,
`1/(1 − β) = (1 + r)/r`. -/
theorem one_sub_beta_inv {r : ℝ} (hr : 0 < r) : (1 - 1 / (1 + r))⁻¹ = (1 + r) / r := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h3 : (1 : ℝ) - 1 / (1 + r) = r / (1 + r) := by
    rw [eq_div_iff h1, sub_mul, one_div, inv_mul_cancel₀ h1]
    ring
  rw [h3, inv_div]

/-- Cochrane (2023), eq. (10.7), p. 296 (survey E10.1, corrected): the dollar is `y/(1 + y)`
perpetuities, so a perpetuity is worth `(1 + y)/y` dollars; `((1 + y)/y)/P_t = (1 + r)/r` holds
iff `P_t = (1 + y) r/((1 + r) y)`. -/
theorem perpetuity_price_level {y r P : ℝ} (hy : 0 < y) (hr : 0 < r) (hP : P ≠ 0) :
    (1 + y) / y / P = (1 + r) / r ↔ P = (1 + y) * r / ((1 + r) * y) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [div_eq_div_iff hP hr.ne', eq_div_iff (mul_ne_zero h1 hy.ne')]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Cochrane (2023), eq. (10.7), p. 296 (survey E10.1): if (10.7) holds at every date and state
(`β = 1/(1 + r)`), the price level is the constant `(1 + y) r/((1 + r) y)`. -/
theorem perpetuity_price_level_process {y r : ℝ} (hy : 0 < y) (hr : 0 < r) {P : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0)
    (h107 : ∀ t ω, (1 + y) / y / P t ω = pv 𝔼 (1 / (1 + r)) (fun t ω => P t ω / P t ω) t ω)
    (t : ℕ) (ω : Ω) : P t ω = (1 + y) * r / ((1 + r) * y) := by
  have hβ0 : 0 ≤ 1 / (1 + r) := by positivity
  have hβ1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := h107 t ω
  rw [perpetuity_real_value 𝔼 hβ0 hβ1 hP t, one_sub_beta_inv hr] at h
  exact (perpetuity_price_level hy hr (hP t ω)).mp h

/-- Cochrane (2023), p. 296 (survey E10.1): the printed formula `(1 + r) y/((1 + y) r)` is the
reciprocal of the correct price level. -/
theorem printed_reciprocal (y r : ℝ) :
    (1 + r) * y / ((1 + y) * r) = ((1 + y) * r / ((1 + r) * y))⁻¹ := by
  rw [inv_div]

/-- Cochrane (2023), p. 296 (survey E10.1): the printed and the correct price levels agree iff
`y = r` (for `y, r > 0`). -/
theorem printed_eq_iff {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (1 + r) * y / ((1 + y) * r) = (1 + y) * r / ((1 + r) * y) ↔ y = r := by
  have ha : 0 < (1 + r) * y := by positivity
  have hb : 0 < (1 + y) * r := by positivity
  rw [div_eq_div_iff hb.ne' ha.ne']
  constructor
  · intro h
    have h2 : ((1 + r) * y - (1 + y) * r) * ((1 + r) * y + (1 + y) * r) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  · intro h
    rw [h]

/-- Cochrane (2023), p. 296 (survey E10.1): at `r = 0.04`, `y = 0.05` the correct price level is
`21/26 ≈ 0.808` while the printed formula gives `26/21 ≈ 1.238`. -/
theorem printed_counterexample :
    (1 + (0.05 : ℝ)) * 0.04 / ((1 + 0.04) * 0.05) = 21 / 26 ∧
      (1 + (0.04 : ℝ)) * 0.05 / ((1 + 0.05) * 0.04) = 26 / 21 := by
  constructor <;> norm_num

/-- Cochrane (2023), p. 296: "it is convenient to define `y = r` so `P_t = 1`": the corrected
price level equals one iff `y = r` (so the book's conclusion stands). -/
theorem price_level_one_iff {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (1 + y) * r / ((1 + r) * y) = 1 ↔ y = r := by
  rw [div_eq_one_iff_eq (by positivity)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 296: defining the dollar as `r/(1 + r)` perpetuities each paying one
potato a year gives a dollar worth `(r/(1 + r)) (1 + r)/r = 1` potato, a unit price level. -/
theorem potato_perpetuity_unit {r : ℝ} (hr : 0 < r) : r / (1 + r) * ((1 + r) / r) = 1 := by
  have h1 : (1 + r) ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), p. 296: for bounded surpluses, subtracting a constant payment `c` every period
lowers the present value by `c/(1 − β)`. -/
theorem pv_sub_const {β M c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    pv 𝔼 β (fun t ω => s t ω - c) t = pv 𝔼 β s t - fun _ => c * (1 - β)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => β ^ j) := summable_geometric_of_lt_one hβ0 hβ1
  have h : epv β (fun t ω => s t ω - c) t = epv β s t - fun _ => c * (1 - β)⁻¹ := by
    funext ω
    have hsum : Summable (fun j => β ^ j * s (t + j) ω) :=
      Summable.of_norm_bounded (hgeo.mul_right M) fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
        exact mul_le_mul_of_nonneg_left (hs (t + j) ω) (pow_nonneg hβ0 j)
    simp only [epv, Pi.sub_apply]
    rw [← tsum_geometric_of_lt_one hβ0 hβ1, ← tsum_mul_left, ← hsum.tsum_sub (hgeo.mul_left c)]
    exact tsum_congr fun j => by ring
  rw [pv, h, map_sub, 𝔼.const, pv]

/-- Cochrane (2023), p. 296: "the value of equity must be positive, so the value of the perpetuity
is limited by the present value of potato sales": if the stockholders' claim
`E_t ∑ βʲ (s_{t+j} − M)` is nonnegative, then `M/(1 − β) ≤ E_t ∑ βʲ s_{t+j}`. -/
theorem perpetuity_backing_bound {β Ms M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ Ms) {t : ℕ} {ω : Ω}
    (heq : 0 ≤ pv 𝔼 β (fun t ω => s t ω - M) t ω) : M * (1 - β)⁻¹ ≤ pv 𝔼 β s t ω := by
  rw [pv_sub_const 𝔼 hβ0 hβ1 hs t] at heq
  simp only [Pi.sub_apply] at heq
  linarith

/-! ### One-period indexed bonds as numeraire -/

/-- Cochrane (2023), p. 296: a one-period indexed bond pays `P_{t+1}` dollars, i.e. one potato, at
`t + 1`; its real value at `t` is `β E_t(P_{t+1}/P_{t+1}) = β`. -/
theorem oneperiod_real_value {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    β • 𝔼.E t (fun ω => P (t + 1) ω / P (t + 1) ω) = fun _ => β := by
  have h : (fun ω => P (t + 1) ω / P (t + 1) ω) = fun _ => (1 : ℝ) := by
    funext ω
    exact div_self (hP (t + 1) ω)
  rw [h, 𝔼.const]
  funext ω
  simp

/-- Cochrane (2023), p. 296 (survey E10.2, corrected): if the bond is the numeraire, a unit of
numeraire is worth `β` goods, so the price level (numeraire per good) is `P_t = 1/β`, and each
maturing bond (worth one good) is redeemed for `P_t = 1/β` new bonds. -/
theorem oneperiod_price_level {β P : ℝ} : 1 / P = β ↔ P = 1 / β := by
  constructor
  · intro h
    rw [← h, one_div_one_div]
  · intro h
    rw [h, one_div_one_div]

/-- Cochrane (2023), p. 296 (survey E10.2): the printed `P_t = β` is not the price level, since
`β ≠ 1/β` for `0 < β < 1`. -/
theorem printed_beta_wrong {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : β ≠ 1 / β := by
  intro h
  rw [eq_div_iff hβ0.ne'] at h
  nlinarith

/-- Cochrane (2023), pp. 296–297: defining the numeraire as `1 + y` one-period indexed bonds
(`β = 1/(1 + r)`) gives `P_t = (1 + r)/(1 + y)`, equal to one iff `y = r`. -/
theorem numeraire_one_plus_y {y r P : ℝ} (hy : 0 < 1 + y) (hr : 0 < 1 + r) (hP : P ≠ 0)
    (h : 1 / P = (1 + y) * (1 / (1 + r))) : P = (1 + r) / (1 + y) ∧ (P = 1 ↔ y = r) := by
  have hP' : P = (1 + r) / (1 + y) := by
    field_simp at h
    rw [eq_div_iff hy.ne']
    linarith
  refine ⟨hP', ?_⟩
  rw [hP', div_eq_one_iff_eq hy.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 296: bondholders receive `min(M_t, s_{t+1})` potatoes when stockholder
payments must be nonnegative, so the bonds are worth at most `β M_t`. -/
theorem bond_value_le {β M : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (t : ℕ) :
    β • 𝔼.E t (fun ω => min M (s (t + 1) ω)) ≤ fun _ => β * M := by
  intro ω
  have h1 : 𝔼.E t (fun ω => min M (s (t + 1) ω)) ≤ 𝔼.E t (fun _ => M) :=
    𝔼.mono t fun ω => min_le_left _ _
  rw [𝔼.const] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h1 ω) hβ

/-- Cochrane (2023), p. 296 (survey E10.4): there is no default, and the bonds are worth exactly
`β M_t`, as soon as `M_t ≤ s_{t+1}` in every state (the book's strict `M_t < min s_{t+1}` is not
needed). -/
theorem bond_value_no_default {β M : ℝ} {s : ℕ → Ω → ℝ} {t : ℕ} (hM : ∀ ω, M ≤ s (t + 1) ω) :
    β • 𝔼.E t (fun ω => min M (s (t + 1) ω)) = fun _ => β * M := by
  have h : (fun ω => min M (s (t + 1) ω)) = fun _ => M := by
    funext ω
    exact min_eq_left (hM ω)
  rw [h, 𝔼.const]
  funext ω
  simp

end Cochrane.AssetsRulesBalanceSheets.SharesAsMoney

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Central-bank and treasury balance sheets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.2–10.7 (pp. 297–311).
These sections are largely institutional; this module formalises their precise claims in the
two-balance-sheet valuation model: the central bank has nominal liabilities `M` (reserves and
cash), real assets with value `A` and treasury debt `B_c` (nominal); the treasury owes `B_p` to
the public and `B_c` to the central bank and has surplus present value `V_T`.

## Main results

* §10.3 (pp. 298–300): `consolidated_of_separate` ("that view only adds debt and the surpluses
  that repay it to left and right-hand sides"), `treasury_iff_consolidated`,
  `contingent_transfers_unite` (with residual profit rebates and recapitalisations, only the
  consolidated equation restricts the price level).
* p. 301 (Bassetto–Sargent): `nominal_cb_cannot_determine` (a central bank holding only nominal
  government debt cannot determine the price level), `real_cb_determines` (one holding real
  assets can).
* §10.2 (p. 298): `walled_off_insulated` (a walled-off central bank pins `P`; a treasury default
  on publicly held debt does not move it), `topping_up_lowers_price` (topping up central-bank
  assets lowers the price level, confiscating them raises it).
* §10.4 (p. 301): `asset_volatility_passes_through` (the log price level moves one-for-one with
  the log value of the real assets, so stable assets give a stable price level).
* §10.7 (p. 310): converting government debt into fixed-value floating-rate money leaves the
  price level unchanged — the same statement as `CentralBankIndependence.cb_purchase_neutral`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.BalanceSheets

/-- Cochrane (2023), §10.3, p. 299: if the central bank's valuation `M/P = A + B_c/P` and the
treasury's valuation `(B_p + B_c)/P = V_T` hold, so does the consolidated valuation
`(B_p + M)/P = V_T + A`: the consolidated view adds central-bank debt and the assets that back it
to both sides. -/
theorem consolidated_of_separate {M A Bc Bp VT P : ℝ} (hcb : M / P = A + Bc / P)
    (htr : (Bp + Bc) / P = VT) : (Bp + M) / P = VT + A := by
  rw [add_div] at htr ⊢
  linarith

/-- Cochrane (2023), §10.3, p. 300: "In any case, the price level still adjusts so that the
value of overall government liabilities is equal to the present value of overall surpluses":
given the central bank's valuation, the treasury's valuation holds iff the consolidated one
does. -/
theorem treasury_iff_consolidated {M A Bc Bp VT P : ℝ} (hcb : M / P = A + Bc / P) :
    (Bp + Bc) / P = VT ↔ (Bp + M) / P = VT + A := by
  rw [add_div, add_div]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.3, pp. 299–300: contingent transfers (profit rebates and
recapitalisations, real present value `τ` from the central bank to the treasury) unite the
balance sheets: there is a transfer making both separate valuations hold iff the consolidated
valuation holds. -/
theorem contingent_transfers_unite {M A Bc Bp VT P : ℝ} :
    (∃ τ : ℝ, M / P = A + Bc / P - τ ∧ (Bp + Bc) / P = VT + τ) ↔ (Bp + M) / P = VT + A := by
  constructor
  · rintro ⟨τ, h1, h2⟩
    rw [add_div] at h2 ⊢
    linarith
  · intro h
    refine ⟨A + Bc / P - M / P, by ring, ?_⟩
    rw [add_div] at h ⊢
    linarith

/-- Cochrane (2023), §10.3, p. 301 (Bassetto and Sargent): a central bank holding only nominal
government debt (`A = 0`) cannot determine the price level: `M/P = B_c/P` holds at one nonzero
price level iff it holds at all of them (iff `M = B_c`). -/
theorem nominal_cb_cannot_determine {M Bc P : ℝ} (hP : P ≠ 0) :
    M / P = 0 + Bc / P ↔ M = Bc := by
  rw [zero_add]
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), §10.3, p. 301 (Bassetto and Sargent): a central bank holding real assets
`A > 0` (with `M > B_c`) determines the price level, `P = (M − B_c)/A`. -/
theorem real_cb_determines {M A Bc : ℝ} (hA : 0 < A) (hM : Bc < M) :
    ∃! P : ℝ, 0 < P ∧ M / P = A + Bc / P := by
  have hpos : 0 < M - Bc := sub_pos.mpr hM
  refine ⟨(M - Bc) / A, ⟨div_pos hpos hA, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hA.ne']
    field_simp at h
    linarith

/-- Cochrane (2023), §10.2, p. 298: with a walled-off central bank, the price level
`P = (M − B_c)/A` is set by the central bank's balance sheet alone; a treasury that cannot meet
its debt to the public defaults on it, with haircut `D = (P V_T − B_c)/B_p`, without causing
inflation. -/
theorem walled_off_insulated {M A Bc Bp VT P D : ℝ} (hA : A ≠ 0) (hP : P ≠ 0) (hBp : Bp ≠ 0)
    (hcb : M / P = A + Bc / P) (htr : (Bp * D + Bc) / P = VT) :
    P = (M - Bc) / A ∧ D = (P * VT - Bc) / Bp := by
  constructor
  · rw [eq_div_iff hA]
    field_simp at hcb
    linarith
  · rw [eq_div_iff hBp]
    rw [div_eq_iff hP] at htr
    linarith

/-- Cochrane (2023), §10.2, p. 298: "topping up central bank assets would be a way to slow
inflation, and confiscating those asset would be a way to create inflation": `P = (M − B_c)/A`
is strictly decreasing in the real assets `A > 0` (for `M > B_c`). -/
theorem topping_up_lowers_price {M Bc A A' : ℝ} (hM : Bc < M) (hA : 0 < A) (hAA : A < A') :
    (M - Bc) / A' < (M - Bc) / A :=
  div_lt_div_of_pos_left (sub_pos.mpr hM) hA hAA

/-- Cochrane (2023), §10.4, p. 301: "It is also desirable for the assets on the right-hand side to
have a stable value, so as not to induce inflation volatility": with `P = (M − n)/a` (nominal
asset `n`, real asset value `a`), the log price level moves one-for-one, inversely, with the log
asset value. -/
theorem asset_volatility_passes_through {M n a₁ a₂ : ℝ} (hM : n < M) (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) :
    Real.log ((M - n) / a₁) - Real.log ((M - n) / a₂) = Real.log a₂ - Real.log a₁ := by
  have hpos : 0 < M - n := sub_pos.mpr hM
  rw [Real.log_div hpos.ne' h₁.ne', Real.log_div hpos.ne' h₂.ne']
  ring

end Cochrane.AssetsRulesBalanceSheets.BalanceSheets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exchange rates under the fiscal theory (Dupor 2000, Daniel 2001b)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.3 (p. 527), assigned to
this project by the Chapters 20–25 survey (foreign-currency debt, §8.1). Two countries issue
nominal debt `B₁`, `B₂` in their own currencies, price levels `P₁`, `P₂` of a common good, so the
exchange rate (domestic currency 1 per unit of currency 2) is `e = P₁/P₂`.

## Main results

* `separate_pools_determinate`, `separate_pools_exchange_rate`: when each country repays its own
  debt from its own surpluses (`B₁/P₁ = V₁`, `B₂/P₂ = V₂`), the price levels and the exchange
  rate are determinate, `e = (B₁/V₁)/(B₂/V₂)`, the ratio of nominal debt to the present value of
  surpluses; `exchange_rate_eq_ratio_pv` states this date by date and state by state.
* `common_pool_exchange_rate_free`, `common_pool_indeterminate`: when the two currencies are
  claims on a common pool of surpluses (`B₁/P₁ + B₂/P₂ = V`), every exchange rate `e > 0` is
  consistent with equilibrium (with unique price levels given `e`), so the exchange rate is
  indeterminate.
-/

namespace Cochrane.AssetsRulesBalanceSheets.ExchangeRates

open RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §24.3, p. 527 (Daniel 2001b): "When two countries with separate currencies pay
off their own debts, exchange rates are determinate": with positive debts and surplus present
values there is exactly one pair of positive price levels. -/
theorem separate_pools_determinate {B₁ B₂ V₁ V₂ : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ B₁ / p.1 = V₁ ∧ B₂ / p.2 = V₂ := by
  obtain ⟨P₁, ⟨h₁, e₁⟩, u₁⟩ := valuation_price_unique hB₁ hV₁
  obtain ⟨P₂, ⟨h₂, e₂⟩, u₂⟩ := valuation_price_unique hB₂ hV₂
  refine ⟨(P₁, P₂), ⟨h₁, h₂, e₁, e₂⟩, ?_⟩
  rintro ⟨p₁, p₂⟩ ⟨k₁, k₂, f₁, f₂⟩
  exact Prod.ext (u₁ p₁ ⟨k₁, f₁⟩) (u₂ p₂ ⟨k₂, f₂⟩)

/-- Cochrane (2023), §24.3, p. 527: with separate surplus pools the exchange rate is the ratio of
each country's nominal debt to the present value of its surpluses,
`e = P₁/P₂ = (B₁/V₁)/(B₂/V₂)`. -/
theorem separate_pools_exchange_rate {B₁ B₂ V₁ V₂ P₁ P₂ : ℝ} (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0) (e₁ : B₁ / P₁ = V₁) (e₂ : B₂ / P₂ = V₂) :
    P₁ / P₂ = (B₁ / V₁) / (B₂ / V₂) := by
  have h1 : P₁ = B₁ / V₁ := by rw [eq_div_iff hV₁, ← e₁]; field_simp
  have h2 : P₂ = B₂ / V₂ := by rw [eq_div_iff hV₂, ← e₂]; field_simp
  rw [h1, h2]

/-- Cochrane (2023), §24.3, p. 527, at every date and state: if each country's nominal debt is
valued by its own surpluses, `B_{i,t−1}/P_{i,t} = E_t ∑ βʲ s_{i,t+j}`, the exchange rate is
`P_{1,t}/P_{2,t} = (B_{1,t−1}/PV_{1,t})/(B_{2,t−1}/PV_{2,t})`. -/
theorem exchange_rate_eq_ratio_pv {β : ℝ} {B₁ B₂ P₁ P₂ s₁ s₂ : ℕ → Ω → ℝ}
    (hP₁ : ∀ t ω, P₁ t ω ≠ 0) (hP₂ : ∀ t ω, P₂ t ω ≠ 0)
    (hv₁ : ∀ t, B₁ t / P₁ t = pv 𝔼 β s₁ t) (hv₂ : ∀ t, B₂ t / P₂ t = pv 𝔼 β s₂ t)
    (hpv₁ : ∀ t ω, pv 𝔼 β s₁ t ω ≠ 0) (hpv₂ : ∀ t ω, pv 𝔼 β s₂ t ω ≠ 0) (t : ℕ) (ω : Ω) :
    P₁ t ω / P₂ t ω = (B₁ t ω / pv 𝔼 β s₁ t ω) / (B₂ t ω / pv 𝔼 β s₂ t ω) :=
  separate_pools_exchange_rate (hP₁ t ω) (hP₂ t ω) (hpv₁ t ω) (hpv₂ t ω)
    (congrFun (hv₁ t) ω) (congrFun (hv₂ t) ω)

/-- Cochrane (2023), §24.3, p. 527 (Dupor 2000): "Two currencies vie for a common pool of
surpluses, so the exchange rate is indeterminate": for every exchange rate `e > 0` there is
exactly one pair of positive price levels with `P₁ = e P₂` satisfying the common valuation
`B₁/P₁ + B₂/P₂ = V`. -/
theorem common_pool_exchange_rate_free {B₁ B₂ V e : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hV : 0 < V) (he : 0 < e) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ B₁ / p.1 + B₂ / p.2 = V ∧ p.1 = e * p.2 := by
  have hq : 0 < (B₁ / e + B₂) / V := div_pos (add_pos (div_pos hB₁ he) hB₂) hV
  refine ⟨(e * ((B₁ / e + B₂) / V), (B₁ / e + B₂) / V),
    ⟨mul_pos he hq, hq, ?_, rfl⟩, ?_⟩
  · simp only
    field_simp
  · rintro ⟨p₁, p₂⟩ ⟨h₁, h₂, hval, hp⟩
    simp only at h₁ h₂ hval hp
    have hp₂ : p₂ = (B₁ / e + B₂) / V := by
      rw [hp] at hval
      rw [eq_div_iff hV.ne', ← hval]
      field_simp
    refine Prod.ext ?_ ?_
    · simp only
      rw [hp, hp₂]
    · exact hp₂

/-- Cochrane (2023), §24.3, p. 527 (Dupor 2000): with a common surplus pool, the set of
equilibrium exchange rates `P₁/P₂` is the whole positive half-line. -/
theorem common_pool_indeterminate {B₁ B₂ V : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hV : 0 < V) :
    {e : ℝ | ∃ P₁ P₂ : ℝ, 0 < P₁ ∧ 0 < P₂ ∧ B₁ / P₁ + B₂ / P₂ = V ∧ e = P₁ / P₂} =
      Set.Ioi 0 := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨P₁, P₂, h₁, h₂, _, rfl⟩
    exact div_pos h₁ h₂
  · intro he
    obtain ⟨⟨P₁, P₂⟩, ⟨h₁, h₂, hval, hp⟩, _⟩ := common_pool_exchange_rate_free hB₁ hB₂ hV he
    simp only at h₁ h₂ hval hp
    refine ⟨P₁, P₂, h₁, h₂, hval, ?_⟩
    rw [hp]
    field_simp

end Cochrane.AssetsRulesBalanceSheets.ExchangeRates

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A simple model of an inflation target

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.2
"A simple model of an inflation target", eqs. (9.1)–(9.6), pp. 263–264.

The government keeps a state variable `V*_t`, the real value the debt would have if the price
level were always at the target `P*_t` ((9.1)–(9.2)); the surplus repays it,
`s_t = s_{0,t} + α V*_t` (9.4); the central bank sets the bond price consistent with the target,
`Q_t = β E_t (P*_t / P*_{t+1})` (9.5). The book concludes that `P_t = P*_t` is the unique
equilibrium price level.

## Dating convention

Lean date `t` is book date `t + 1`. `B t` is the nominal debt outstanding at the *start* of date
`t` (book `B_{t-1}`), so the one-period flow condition reads `B_t/P_t = s_t + Q_t B_{t+1}/P_t`
and `B (t + 1)` is chosen (known) at date `t`. (9.1) is `V 0 = B 0 / P* 0`.

## Main results

* `eq_9_3`, `eq_9_6`, `eq_9_6_rule`: the book's algebra, under an arbitrary `ExpectationSystem`
  with the pull-out property.
* `tendsto_state_forecast`: `β^T E_t V*_{t+T} → 0` for bounded `s₀` **when `0 < α < 2`**;
  `tendsto_state_forecast_iff`: with `s₀ = 0` this limit is zero iff `0 < α < 2`;
  `tendsto_state_forecast_alpha_zero`: at `α = 0` the limit is `V*_t − E_t ∑ βʲ s_{0,t+j}`.
  The book's claim "for bounded `{s_{0,t}}`" omits the condition `0 < α < 2` (error E9.1).
* `hasSum_state`: `V*_t = E_t ∑ βʲ s_{t+j}` as a genuine absolutely convergent series.
* `realDebt_eq_state`: `B_t/P_t = V*_t` at every date and state.
* `price_eq_target` (**Theorem IT**): `P = P*`. The base step is `P_1 = P*_1` in book dating
  (the book writes `P_0 = P_0^*`, error E9.2) and the induction step needs `V*_t ≠ s_t`;
  `price_eq_target_perfectForesight`: under perfect foresight `V*_t ≠ s_t` is not needed;
  `zero_debt_sunspot`: under genuine uncertainty it is (a coin-flip counterexample).
* `target_alone_insufficient`, `rule_alone_insufficient`: the book's two insufficiency claims
  ("the interest-rate target alone is insufficient", "the surplus rule is also insufficient";
  doubling nominal debt doubles the future price level).
-/

namespace Cochrane.AssetsRulesBalanceSheets.InflationTarget

open Filter Topology

/-! ### A contraction lemma -/

/-- Cochrane (2023), §9.2, p. 264 (the limit `β^T E_t V*_{t+T} → 0`): a sequence obeying
`|x_{T+1} − c x_T| ≤ βᵀ M` is bounded by `mᵀ (|x_0| + T M / m)` with `m = max |c| β`. -/
theorem abs_le_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hβ : 0 < β) (hM : 0 ≤ M)
    (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) (T : ℕ) :
    |x T| ≤ max |c| β ^ T * (|x 0| + T * M / max |c| β) := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  induction T with
  | zero => simp
  | succ T ih =>
    have hcm : |c| ≤ m := le_max_left _ _
    have hβm : β ^ T ≤ m ^ T := pow_le_pow_left₀ hβ.le (le_max_right _ _) T
    calc |x (T + 1)| = |(x (T + 1) - c * x T) + c * x T| := by ring_nf
      _ ≤ |x (T + 1) - c * x T| + |c * x T| := abs_add_le _ _
      _ ≤ β ^ T * M + m * (m ^ T * (|x 0| + T * M / m)) := by
          gcongr
          · exact hx T
          · rw [abs_mul]
            exact mul_le_mul hcm ih (abs_nonneg _) hm.le
      _ ≤ m ^ T * M + m * (m ^ T * (|x 0| + T * M / m)) := by gcongr
      _ = m ^ (T + 1) * (|x 0| + ((T + 1 : ℕ) : ℝ) * M / m) := by
          push_cast
          field_simp
          ring

/-- Cochrane (2023), §9.2, p. 264: a sequence obeying `|x_{T+1} − c x_T| ≤ βᵀ M` with `|c| < 1`
and `0 < β < 1` converges to zero. -/
theorem tendsto_zero_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hc : |c| < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hM : 0 ≤ M) (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) :
    Tendsto x atTop (𝓝 0) := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  have hm1 : m < 1 := max_lt hc hβ1
  have hlim : Tendsto (fun T : ℕ => m ^ T * |x 0| + (T * m ^ T) * (M / m)) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hm.le hm1).mul_const |x 0|
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hm.le hm1).mul_const (M / m)
    simpa using h1.add h2
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (abs_le_of_contraction hβ hM hx T).trans (le_of_eq ?_)
  rw [← hm_def]
  field_simp

/-- Cochrane (2023), §9.2, p. 264: a sequence obeying `|x_{T+1} − c x_T| ≤ βᵀ M` with `|c| < 1`
and `0 < β < 1` is absolutely summable. -/
theorem summable_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hc : |c| < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hM : 0 ≤ M) (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) :
    Summable x := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  have hm1 : m < 1 := max_lt hc hβ1
  have hg : Summable (fun T : ℕ => m ^ T * |x 0| + ((T : ℝ) ^ 1 * m ^ T) * (M / m)) := by
    refine ((summable_geometric_of_lt_one hm.le hm1).mul_right _).add ?_
    refine (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := m) ?_).mul_right _
    rw [Real.norm_eq_abs, abs_of_pos hm]
    exact hm1
  have hb : ∀ T : ℕ, ‖x T‖ ≤ m ^ T * |x 0| + ((T : ℝ) ^ 1 * m ^ T) * (M / m) := by
    intro T
    rw [Real.norm_eq_abs, pow_one]
    have h := abs_le_of_contraction hβ hM hx T
    rw [← hm_def] at h
    calc |x T| ≤ m ^ T * (|x 0| + T * M / m) := h
      _ = m ^ T * |x 0| + (T * m ^ T) * (M / m) := by ring
  exact Summable.of_norm_bounded hg hb

/-! ### Known random variables under the pull-out property -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.2, p. 264 (the book's use of `E_t` on products): under `PullOut`, a
product of two variables known at `t` is known at `t`. -/
theorem known_mul (h𝔼 : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [h𝔼 t a b ha, hb]

/-- Cochrane (2023), §9.2, p. 264: under `PullOut`, the reciprocal of a nowhere-zero variable
known at `t` is known at `t`. -/
theorem known_inv (h𝔼 : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (h0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 := h𝔼 t a a⁻¹ ha
  have hone : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp only [Pi.mul_apply, Pi.inv_apply]
    exact mul_inv_cancel₀ (h0 ω)
  rw [hone, 𝔼.const] at h1
  funext ω
  have h2 : (1 : ℝ) = a ω * 𝔼.E t a⁻¹ ω := congrFun h1 ω
  have ha0 := h0 ω
  change 𝔼.E t a⁻¹ ω = (a ω)⁻¹
  calc 𝔼.E t a⁻¹ ω = (a ω)⁻¹ * (a ω * 𝔼.E t a⁻¹ ω) := by field_simp
    _ = (a ω)⁻¹ := by rw [← h2, mul_one]

/-- Cochrane (2023), §9.2, p. 264: under `PullOut`, a ratio of variables known at `t` (nowhere
zero denominator) is known at `t`. -/
theorem known_div (h𝔼 : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (h0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv]
  exact known_mul 𝔼 h𝔼 ha (known_inv 𝔼 h𝔼 hb h0)

/-! ### The model -/

/-- Cochrane (2023), eq. (9.1), p. 263: the target state starts at `V*_1 = B_0 / P*_1`
(Lean date `0` is book date `1`). -/
def StateInit (B Pstar V : ℕ → Ω → ℝ) : Prop := V 0 = B 0 / Pstar 0

/-- Cochrane (2023), eq. (9.2), p. 263: `V*_{t+1} = (1/Q_t)(P*_t/P*_{t+1})(V*_t − s_t)`, the
real debt accumulated at the price-level target, with bond price `Q`. -/
def StateRec (Q Pstar s V : ℕ → Ω → ℝ) : Prop :=
  ∀ t, V (t + 1) = (Q t)⁻¹ * (Pstar t / Pstar (t + 1)) * (V t - s t)

/-- Cochrane (2023), eq. (9.4), p. 263: the surplus rule `s_t = s_{0,t} + α V*_t`. -/
def SurplusRule (α : ℝ) (s0 V s : ℕ → Ω → ℝ) : Prop := ∀ t, s t = s0 t + α • V t

/-- Cochrane (2023), eq. (9.5), p. 264: the interest-rate target `Q_t = β E_t (P*_t/P*_{t+1})`. -/
def RateTarget (β : ℝ) (Pstar Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Q t = β • 𝔼.E t (Pstar t / Pstar (t + 1))

variable (β : ℝ) (B P Q s : ℕ → Ω → ℝ)

/-- Cochrane (2023), §9.2, p. 263 (and §3.1 for the frictionless economy): the private-sector
equilibrium conditions with one-period nominal debt — positive prices, adapted variables, debt
`B_{t+1}` chosen at `t`, the flow condition `B_t/P_t = s_t + Q_t B_{t+1}/P_t`, bond pricing with a
constant real rate `Q_t = β E_t (P_t/P_{t+1})`, and the transversality condition
`β^T E_t (B_{t+T}/P_{t+T}) → 0`. -/
structure Economy where
  pos_P : ∀ t ω, 0 < P t ω
  pos_Q : ∀ t ω, 0 < Q t ω
  adapted_P : 𝔼.Adapted P
  adapted_Q : 𝔼.Adapted Q
  known_B0 : 𝔼.E 0 (B 0) = B 0
  predetermined_B : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)
  flow : ∀ t, B t / P t = s t + Q t * B (t + 1) / P t
  pricing : ∀ t, Q t = β • 𝔼.E t (P t / P (t + 1))
  tvc : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (B (t + T) / P (t + T)) ω) atTop (𝓝 0)

variable {𝔼 β B P Q s}

/-- Cochrane (2023), eq. (9.3), p. 263: the flow condition rearranged,
`B_{t+1}/P_{t+1} = (1/Q_t)(P_t/P_{t+1})(B_t/P_t − s_t)`. -/
theorem eq_9_3 (hE : Economy 𝔼 β B P Q s) (t : ℕ) :
    B (t + 1) / P (t + 1) = (Q t)⁻¹ * (P t / P (t + 1)) * (B t / P t - s t) := by
  funext ω
  have h := congrFun (hE.flow t) ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.inv_apply] at h ⊢
  have hP := (hE.pos_P t ω).ne'
  have hP1 := (hE.pos_P (t + 1) ω).ne'
  have hQ := (hE.pos_Q t ω).ne'
  rw [h]
  field_simp
  ring

/-- Cochrane (2023), §9.2, p. 264: the target state `V*` is adapted (known at each date). -/
theorem state_adapted (h𝔼 : 𝔼.PullOut) {α : ℝ} {Pstar s0 V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hQa : 𝔼.Adapted Q) (hPs : ∀ t ω, 0 < Pstar t ω)
    (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0) (hB0 : 𝔼.E 0 (B 0) = B 0)
    (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V) (h94 : SurplusRule α s0 V s) :
    𝔼.Adapted V := by
  intro t
  induction t with
  | zero =>
    rw [h91]
    exact known_div 𝔼 h𝔼 hB0 (hPsa 0) (fun ω => (hPs 0 ω).ne')
  | succ t ih =>
    have hup : ∀ {x : Ω → ℝ}, 𝔼.E t x = x → 𝔼.E (t + 1) x = x :=
      fun hx => ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx
    have hs : 𝔼.E t (s t) = s t := by
      rw [h94 t, map_add, map_smul, hs0a t, ih]
    rw [h92 t]
    refine known_mul 𝔼 h𝔼 (known_mul 𝔼 h𝔼 ?_ ?_) ?_
    · exact known_inv 𝔼 h𝔼 (hup (hQa t)) (fun ω => (hQ t ω).ne')
    · exact known_div 𝔼 h𝔼 (hup (hPsa t)) (hPsa (t + 1)) (fun ω => (hPs (t + 1) ω).ne')
    · rw [map_sub, hup ih, hup hs]

/-- Cochrane (2023), eq. (9.6), p. 264: substituting the target (9.5) into (9.2),
`β E_t V*_{t+1} = V*_t − s_t`. -/
theorem eq_9_6 (h𝔼 : 𝔼.PullOut) (hβ : β ≠ 0) {Pstar V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hVa : 𝔼.Adapted V)
    (hQa : 𝔼.Adapted Q) (hsa : 𝔼.Adapted s) (h92 : StateRec Q Pstar s V)
    (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) :
    β • 𝔼.E t (V (t + 1)) = V t - s t := by
  have hk : 𝔼.E t ((Q t)⁻¹ * (V t - s t)) = (Q t)⁻¹ * (V t - s t) := by
    refine known_mul 𝔼 h𝔼 (known_inv 𝔼 h𝔼 (hQa t) (fun ω => (hQ t ω).ne')) ?_
    rw [map_sub, hVa t, hsa t]
  have hV : V (t + 1) = ((Q t)⁻¹ * (V t - s t)) * (Pstar t / Pstar (t + 1)) := by
    rw [h92 t]
    ring
  rw [hV, h𝔼 t _ _ hk]
  funext ω
  have hT := congrFun (h95 t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.inv_apply, Pi.sub_apply] at hT ⊢
  have hQ0 := (hQ t ω).ne'
  have hE : 𝔼.E t (Pstar t / Pstar (t + 1)) ω = Q t ω / β := by
    rw [hT]
    field_simp
  rw [hE]
  field_simp

/-- Cochrane (2023), §9.2, p. 264 (display after (9.6)): with the rule (9.4),
`β E_t V*_{t+1} = (1 − α) V*_t − s_{0,t}`. -/
theorem eq_9_6_rule (h𝔼 : 𝔼.PullOut) (hβ : β ≠ 0) {α : ℝ} {Pstar s0 V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hVa : 𝔼.Adapted V)
    (hQa : 𝔼.Adapted Q) (hsa : 𝔼.Adapted s) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) :
    β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t := by
  rw [eq_9_6 h𝔼 hβ hQ hVa hQa hsa h92 h95 t, h94 t]
  funext ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §9.2, p. 264: the forecasts `x_T = βᵀ E_t V*_{t+T}` obey
`x_{T+1} = (1 − α) x_T − βᵀ E_t s_{0,t+T}`. -/
theorem state_forecast_succ {α : ℝ} {s0 V : ℕ → Ω → ℝ}
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t T : ℕ) (ω : Ω) :
    β ^ (T + 1) * 𝔼.E t (V (t + (T + 1))) ω =
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω := by
  have key := congrArg (𝔼.E t) (h6 (t + T))
  rw [map_smul, 𝔼.tower (Nat.le_add_right t T), map_sub, map_smul] at key
  have h := congrFun key ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  rw [show t + (T + 1) = t + T + 1 by ring, pow_succ]
  linear_combination (β ^ T) * h

/-- Cochrane (2023), §9.2, p. 264 (corrected, error E9.1): for bounded `{s_{0,t}}` and
**`0 < α < 2`**, `lim_T βᵀ E_t V*_{t+T} = 0`. -/
theorem tendsto_state_forecast (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine tendsto_zero_of_contraction hc hβ0 hβ1 hM0 (fun T => ?_)
  rw [state_forecast_succ h6 t T ω]
  rw [show (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω -
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) = -(β ^ T * 𝔼.E t (s0 (t + T)) ω) by ring,
    abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω) (pow_pos hβ0 T).le

/-- Cochrane (2023), §9.2, p. 264: with `s₀ = 0` the forecasts are
`βᵀ E_t V*_{t+T} = (1 − α)ᵀ V*_t`. -/
theorem state_forecast_of_s0_zero {α : ℝ} {V : ℕ → Ω → ℝ} (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - 0) (t T : ℕ) (ω : Ω) :
    β ^ T * 𝔼.E t (V (t + T)) ω = (1 - α) ^ T * V t ω := by
  induction T with
  | zero => simp [hVa t]
  | succ T ih =>
    have h := state_forecast_succ (s0 := fun _ => 0) h6 t T ω
    rw [h, ih]
    have h0 : 𝔼.E t (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const t 0
    simp only [map_zero, Pi.zero_apply, mul_zero, sub_zero]
    ring

/-- Cochrane (2023), §9.2, p. 264 (error E9.1, necessity and sufficiency): with `s₀ = 0` and
`V*_t ≠ 0`, `βᵀ E_t V*_{t+T} → 0` holds if and only if `0 < α < 2`. -/
theorem tendsto_state_forecast_iff {α : ℝ} {V : ℕ → Ω → ℝ} (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - 0) (t : ℕ) (ω : Ω) (hV : V t ω ≠ 0) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0) ↔ 0 < α ∧ α < 2 := by
  have hx := state_forecast_of_s0_zero hVa h6 t
  simp_rw [hx]
  constructor
  · intro h
    by_contra hα
    have hc : 1 ≤ |1 - α| := by
      rcases not_and_or.mp hα with h1 | h1
      · rw [abs_of_nonneg (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
      · rw [abs_of_nonpos (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
    have hlow : ∀ T : ℕ, |V t ω| ≤ |(1 - α) ^ T * V t ω| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hc)
    have habs := h.abs
    rw [abs_zero] at habs
    have : |V t ω| ≤ 0 := ge_of_tendsto' habs hlow
    exact hV (abs_nonpos_iff.mp this)
  · rintro ⟨h0, h2⟩
    have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).mul_const (V t ω)

/-- Cochrane (2023), §9.2, p. 264 (error E9.1): at `α = 0` the limit of `βᵀ E_t V*_{t+T}` is
`V*_t − ∑ⱼ βʲ E_t s_{0,t+j}`, which is not zero unless `V*_t` happens to equal the present
value of `s₀`. -/
theorem tendsto_state_forecast_alpha_zero (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℝ}
    {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M) (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - (0 : ℝ)) • V t - s0 t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop
      (𝓝 (V t ω - ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω)) := by
  have hab : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsum := ForwardSolution.summable_A16 𝔼 hab hM t ω
  have hx : ∀ T, β ^ T * 𝔼.E t (V (t + T)) ω =
      V t ω - ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
    intro T
    induction T with
    | zero => simp [hVa t]
    | succ T ih =>
      rw [state_forecast_succ h6 t T ω, ih, Finset.sum_range_succ]
      ring
  simp_rw [hx]
  exact hsum.hasSum.tendsto_sum_nat.const_sub _

/-- Cochrane (2023), §9.2, p. 264: iterating (9.6) forward with `0 < α < 2`, the target state is
the present value of surpluses, `V*_t = E_t ∑ⱼ βʲ s_{t+j}` (an absolutely convergent series). -/
theorem hasSum_state (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (h94 : SurplusRule α s0 V s) (h6s : ∀ t, β • 𝔼.E t (V (t + 1)) = V t - s t)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (V t ω) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hsolves : ForwardSolution.Solves 𝔼 β s V := by
    intro t
    rw [h6s t]
    abel
  have hpart := PresentValue.tendsto_partialSums_of_tvc 𝔼 hsa hsolves t ω
    (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6 t ω)
  have hx : ∀ T, |β ^ (T + 1) * 𝔼.E t (V (t + (T + 1))) ω -
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω)| ≤ β ^ T * M := by
    intro T
    rw [state_forecast_succ h6 t T ω]
    rw [show (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω -
        (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) = -(β ^ T * 𝔼.E t (s0 (t + T)) ω) by ring,
      abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω) (pow_pos hβ0 T).le
  have hsV := summable_of_contraction (x := fun T => β ^ T * 𝔼.E t (V (t + T)) ω) hc hβ0 hβ1
    hM0 hx
  have hab : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hs0 := ForwardSolution.summable_A16 𝔼 hab hM t ω
  have hsum : Summable (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) := by
    have heq : (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) = fun j =>
        β ^ j * 𝔼.E t (s0 (t + j)) ω + α * (β ^ j * 𝔼.E t (V (t + j)) ω) := by
      funext j
      rw [h94 (t + j), map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hs0.add (hsV.mul_left α)
  have h := hsum.hasSum
  rwa [tendsto_nhds_unique h.tendsto_sum_nat hpart] at h

/-- Cochrane (2023), §9.2, p. 264 ("the real value of nominal debt is also the present value of
surpluses"): with bond pricing and the pull-out property the real debt `b_t = B_t/P_t` obeys
`b_t = s_t + β E_t b_{t+1}`. -/
theorem realDebt_rec (h𝔼 : 𝔼.PullOut) (hE : Economy 𝔼 β B P Q s) (t : ℕ) :
    B t / P t = s t + β • 𝔼.E t (B (t + 1) / P (t + 1)) := by
  have hP0 : ∀ ω, P t ω ≠ 0 := fun ω => (hE.pos_P t ω).ne'
  have ha : 𝔼.E t (B (t + 1) / P t) = B (t + 1) / P t :=
    known_div 𝔼 h𝔼 (hE.predetermined_B t) (hE.adapted_P t) hP0
  have hprod : B (t + 1) / P (t + 1) = (B (t + 1) / P t) * (P t / P (t + 1)) := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [hP0 ω]
  rw [hE.flow t, hprod, h𝔼 t _ _ ha, hE.pricing t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), §9.2, p. 264: the real value of nominal debt equals the target state,
`B_t/P_t = V*_t`, at every date and state (both solve `y_t = s_t + β E_t y_{t+1}` and both
satisfy the limit condition). -/
theorem realDebt_eq_state (h𝔼 : 𝔼.PullOut) (hE : Economy 𝔼 β B P Q s) {V : ℕ → Ω → ℝ}
    (h6s : ∀ t, β • 𝔼.E t (V (t + 1)) = V t - s t)
    (hlim : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0)) (t : ℕ) :
    B t / P t = V t := by
  set d : ℕ → Ω → ℝ := fun t => B t / P t - V t with hd_def
  have hd : ∀ t, d t = β • 𝔼.E t (d (t + 1)) := by
    intro t
    simp only [hd_def, map_sub, smul_sub]
    rw [h6s t, realDebt_rec h𝔼 hE t]
    abel
  have htvc : PresentValue.TVC 𝔼 β d := fun t ω => by
    have e : ∀ k, β ^ k * 𝔼.E t (d (t + k)) ω = β ^ k * 𝔼.E t (B (t + k) / P (t + k)) ω -
        β ^ k * 𝔼.E t (V (t + k)) ω := fun k => by
      simp only [hd_def, map_sub, Pi.sub_apply]
      ring
    simp_rw [e]
    simpa using (hE.tvc t ω).sub (hlim t ω)
  have h0 := PresentValue.eq_zero_of_tvc 𝔼 hd htvc t
  rw [hd_def, sub_eq_zero] at h0
  exact h0

/-- Cochrane (2023), §9.2, p. 264 (**Theorem IT**, corrected): under the surplus rule (9.4)
with `0 < α < 2`, the interest-rate target (9.5), bounded `s₀`, nonzero initial debt and
`V*_t ≠ s_t` at every date (so that `B_{t+1} ≠ 0`), the unique equilibrium price level is
`P_t = P*_t`. The base step is `P_1 = P*_1` in the book's dating (error E9.2). -/
theorem price_eq_target (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hE : Economy 𝔼 β B P Q s)
    (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (hB0 : ∀ ω, B 0 ω ≠ 0)
    (hVs : ∀ t ω, V t ω ≠ s t ω) : P = Pstar := by
  have hVa := state_adapted h𝔼 hE.pos_Q hE.adapted_Q hPs hPsa hs0a hE.known_B0 h91 h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hb := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6)
  funext t
  induction t with
  | zero =>
    funext ω
    have h := congrFun (hb 0) ω
    rw [h91] at h
    simp only [Pi.div_apply] at h
    rw [div_eq_div_iff (hE.pos_P 0 ω).ne' (hPs 0 ω).ne'] at h
    exact (mul_left_cancel₀ (hB0 ω) h).symm
  | succ t ih =>
    funext ω
    have h3 := congrFun (eq_9_3 hE t) ω
    have h2 := congrFun (h92 t) ω
    have hbt := congrFun (hb t) ω
    have hbt1 := congrFun (hb (t + 1)) ω
    have hpt := congrFun ih ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Pi.sub_apply] at h3 h2 hbt hbt1
    rw [hbt1, hbt, hpt] at h3
    have hk : (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) ≠ 0 := by
      have := sub_ne_zero.mpr (hVs t ω)
      have hq := (inv_pos.mpr (hE.pos_Q t ω)).ne'
      exact mul_ne_zero (mul_ne_zero hq (hPs t ω).ne') this
    have hP1 := (hE.pos_P (t + 1) ω).ne'
    have hPs1 := (hPs (t + 1) ω).ne'
    have h4 : (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) / Pstar (t + 1) ω =
        (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) / P (t + 1) ω := by
      calc _ = (Q t ω)⁻¹ * (Pstar t ω / Pstar (t + 1) ω) * (V t ω - s t ω) := by ring
        _ = (Q t ω)⁻¹ * (Pstar t ω / P (t + 1) ω) * (V t ω - s t ω) := by
          rw [← h2]
          exact h3
        _ = _ := by ring
    rw [div_eq_div_iff hPs1 hP1] at h4
    exact mul_left_cancel₀ hk h4

/-- Cochrane (2023), §9.2, p. 264: in equilibrium the real value of nominal debt is the present
value of surpluses, `B_t/P_t = E_t ∑ⱼ βʲ s_{t+j}`. -/
theorem realDebt_hasSum (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hE : Economy 𝔼 β B P Q s)
    (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (B t ω / P t ω) := by
  have hVa := state_adapted h𝔼 hE.pos_Q hE.adapted_Q hPs hPsa hs0a hE.known_B0 h91 h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hb := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6) t
  have h := congrFun hb ω
  simp only [Pi.div_apply] at h
  rw [h]
  exact hasSum_state hβ0 hβ1 hα0 hα2 hM hsa h94 h6s h6 t ω

/-- Cochrane (2023), §9.2, p. 264: under perfect foresight Theorem IT needs no condition
`V*_t ≠ s_t`, because the interest-rate target fixes `P_{t+1}/P_t = P*_{t+1}/P*_t` directly. -/
theorem price_eq_target_perfectForesight {β α M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < α) (hα2 : α < 2) {B P Pstar Q s s0 V : ℕ → Unit → ℝ}
    (hE : Economy perfectForesight β B P Q s) (hPs : ∀ t ω, 0 < Pstar t ω)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget perfectForesight β Pstar Q)
    (hB0 : ∀ ω, B 0 ω ≠ 0) : P = Pstar := by
  have h𝔼 := perfectForesight_pullOut
  have hb := realDebt_hasSum h𝔼 hβ0 hβ1 hα0 hα2 hE hPs (fun _ => rfl) (fun _ => rfl) hM
    h91 h92 h94 h95
  have hVa : perfectForesight.Adapted V := fun _ => rfl
  have hsa : perfectForesight.Adapted s := fun _ => rfl
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hbV := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6)
  clear hb
  funext t
  induction t with
  | zero =>
    funext ω
    have h := congrFun (hbV 0) ω
    rw [h91] at h
    simp only [Pi.div_apply] at h
    rw [div_eq_div_iff (hE.pos_P 0 ω).ne' (hPs 0 ω).ne'] at h
    exact (mul_left_cancel₀ (hB0 ω) h).symm
  | succ t ih =>
    funext ω
    have h1 := congrFun (hE.pricing t) ω
    have h2 := congrFun (h95 t) ω
    have hpt := congrFun ih ω
    change Q t ω = β * (P t ω / P (t + 1) ω) at h1
    change Q t ω = β * (Pstar t ω / Pstar (t + 1) ω) at h2
    rw [h1, hpt] at h2
    have hP1 := (hE.pos_P (t + 1) ω).ne'
    have hPs1 := (hPs (t + 1) ω).ne'
    have hPt := (hPs t ω).ne'
    have h3 := mul_left_cancel₀ hβ0.ne' h2
    rw [div_eq_div_iff hP1 hPs1] at h3
    exact (mul_left_cancel₀ hPt h3).symm

/-- Cochrane (2023), §9.2, p. 264 (existence half of "`P_t = P*_t` is the unique equilibrium
price level"): with the surplus rule (9.4), `0 < α < 2`, bounded `s₀` and the target (9.5), the
price
path `P = P*` with nominal debt `B_t = P*_t V*_t` is an equilibrium (`Economy`) satisfying
(9.1)–(9.5). -/
theorem exists_equilibrium (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hQ : ∀ t ω, 0 < Q t ω)
    (hQa : 𝔼.Adapted Q) (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar)
    (hs0a : 𝔼.Adapted s0) (hM : ∀ t ω, |s0 t ω| ≤ M) (hV0 : 𝔼.E 0 (V 0) = V 0)
    (h92 : StateRec Q Pstar s V) (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) :
    Economy 𝔼 β (fun t => Pstar t * V t) Pstar Q s ∧
      StateInit (fun t => Pstar t * V t) Pstar V := by
  have hinit : StateInit (fun t => Pstar t * V t) Pstar V := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [(hPs 0 ω).ne']
  have hB0 : 𝔼.E 0 (Pstar 0 * V 0) = Pstar 0 * V 0 := known_mul 𝔼 h𝔼 (hPsa 0) hV0
  have hVa := state_adapted h𝔼 hQ hQa hPs hPsa hs0a hB0 hinit h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hQ hVa hQa hsa h92 h94 h95
  have hBV : ∀ t, (fun t => Pstar t * V t) t / Pstar t = V t := fun t => by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [(hPs t ω).ne']
  refine ⟨⟨hPs, hQ, hPsa, hQa, hB0, fun t => ?_, fun t => ?_, h95, fun t ω => ?_⟩, hinit⟩
  · have hkey : Pstar (t + 1) * V (t + 1) = (Q t)⁻¹ * Pstar t * (V t - s t) := by
      rw [h92 t]
      funext ω
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [(hPs (t + 1) ω).ne']
    change 𝔼.E t (Pstar (t + 1) * V (t + 1)) = Pstar (t + 1) * V (t + 1)
    rw [hkey]
    refine known_mul 𝔼 h𝔼 (known_mul 𝔼 h𝔼 ?_ (hPsa t)) ?_
    · exact known_inv 𝔼 h𝔼 (hQa t) (fun ω => (hQ t ω).ne')
    · rw [map_sub, hVa t, hsa t]
  · rw [hBV t]
    funext ω
    have h2 := congrFun (h92 t) ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.sub_apply] at h2 ⊢
    rw [h2]
    have hQ0 := (hQ t ω).ne'
    have hP0 := (hPs t ω).ne'
    have hP1 := (hPs (t + 1) ω).ne'
    field_simp
    ring
  · have := tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6 t ω
    refine this.congr fun T => ?_
    rw [hBV (t + T)]

/-! ### The two insufficiency claims -/

/-- Cochrane (2023), §9.2, p. 264, witness for "the interest-rate target alone is
insufficient": the target state for the witness `target_alone_insufficient`. -/
noncomputable def witnessState (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => β⁻¹ * (witnessState β t - 2 * (1 - β))

/-- Cochrane (2023), §9.2, p. 264: "The interest-rate target alone is insufficient." Under
perfect foresight, with the target (9.5) in force but a surplus that does not respond to the
target state (`α = 0`, bounded `s₀`), there is an equilibrium with `P ≠ P*` (here
`P ≡ 1/2`, `P* ≡ 1`). -/
theorem target_alone_insufficient {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ B P Pstar Q s s0 V : ℕ → Unit → ℝ, Economy perfectForesight β B P Q s ∧
      (∀ t ω, 0 < Pstar t ω) ∧ (∀ t ω, |s0 t ω| ≤ 2) ∧ StateInit B Pstar V ∧
      StateRec Q Pstar s V ∧ SurplusRule 0 s0 V s ∧ RateTarget perfectForesight β Pstar Q ∧
      (∀ ω, B 0 ω ≠ 0) ∧ P ≠ Pstar := by
  refine ⟨fun _ _ => 1, fun _ _ => 1 / 2, fun _ _ => 1, fun _ _ => β, fun _ _ => 2 * (1 - β),
    fun _ _ => 2 * (1 - β), fun t _ => witnessState β t, ⟨fun _ _ => by norm_num,
    fun _ _ => hβ0, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun t => ?_, fun t => ?_,
    fun t ω => ?_⟩, fun _ _ => by norm_num, fun _ _ => ?_, ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun _ => by norm_num, ?_⟩
  · funext ω
    simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · funext ω
    change β = β * ((1 / 2) / (1 / 2))
    norm_num
  · change Tendsto (fun T => β ^ T * (1 / (1 / 2))) atTop (𝓝 0)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 / (1 / 2) : ℝ)
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · funext ω
    simp [witnessState]
  · funext ω
    simp [witnessState]
  · funext ω
    simp
  · funext ω
    change β = β * (1 / 1)
    norm_num
  · intro h
    have := congrFun (congrFun h 0) ()
    norm_num at this

/-- Cochrane (2023), §9.2, p. 264, witness for "the surplus rule is also insufficient": the
target state `V*_t = ((1 − α)/β)ᵗ`. -/
noncomputable def ruleState (α β : ℝ) (t : ℕ) : ℝ := ((1 - α) / β) ^ t

/-- Cochrane (2023), §9.2, p. 264: "The surplus rule is also insufficient. Even with the rule
(9.4), a decision to double nominal debt without changing surpluses will have the usual effect
of doubling the future price level." Under perfect foresight with `0 < α < 2`, bounded `s₀`, and
the target state built from the target bond price `Q*_t = β E_t(P*_t/P*_{t+1})`, doubling the debt
sold at date `0` gives an equilibrium with `P_t = 2 P*_t` for `t ≥ 1`; the actual bond price then
misses the target, `Q ≠ Q*`. -/
theorem rule_alone_insufficient {α β : ℝ} (hβ0 : 0 < β) (hα0 : 0 < α)
    (hα2 : α < 2) :
    ∃ B P Pstar Q Qs s s0 V : ℕ → Unit → ℝ, Economy perfectForesight β B P Q s ∧
      (∀ t ω, 0 < Pstar t ω) ∧ (∀ t ω, |s0 t ω| ≤ 0) ∧ StateInit B Pstar V ∧
      StateRec Qs Pstar s V ∧ SurplusRule α s0 V s ∧ RateTarget perfectForesight β Pstar Qs ∧
      (∀ t, 1 ≤ t → ∀ ω, P t ω = 2 * Pstar t ω) ∧ Q ≠ Qs := by
  set P : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 2 with hP
  set V : ℕ → Unit → ℝ := fun t _ => ruleState α β t with hV
  set B : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 2 * ruleState α β t with hB
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => by
    simp only [hP]
    split_ifs <;> norm_num
  have hβne : β ≠ 0 := hβ0.ne'
  have hq : (1 - α) / β * β = 1 - α := by field_simp
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine ⟨B, P, fun _ _ => 1, fun t _ => β * (P t () / P (t + 1) ()), fun _ _ => β,
    fun t ω => α * V t ω, fun _ _ => 0, V, ⟨hPpos, fun t ω => ?_, fun _ => rfl, fun _ => rfl, rfl,
    fun _ => rfl, fun t => ?_, fun t => ?_, fun t ω => ?_⟩, fun _ _ => by norm_num,
    fun _ _ => by norm_num, ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t ht ω => ?_, ?_⟩
  · exact mul_pos hβ0 (div_pos (hPpos t ()) (hPpos (t + 1) ()))
  · funext ω
    simp only [hP, hB, hV, ruleState, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    have hbb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβne
    rcases t with _ | t
    · simp only [↓reduceIte, pow_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      linear_combination (α - 1) * hbb
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      linear_combination (α - 1) * ((1 - α) / β) ^ (t + 1) * hbb
  · funext ω
    rfl
  · change Tendsto (fun T => β ^ T * (B (t + T) ω / P (t + T) ω)) atTop (𝓝 0)
    have hev : ∀ T, 1 ≤ T → β ^ T * (B (t + T) ω / P (t + T) ω) =
        ruleState α β t * (1 - α) ^ T := by
      intro T hT
      have h0 : t + T ≠ 0 := by omega
      simp only [hB, hP, h0, ↓reduceIte, ruleState]
      rw [pow_add, show ∀ X : ℝ, 2 * X / 2 = X from fun X => by ring,
        show β ^ T * (((1 - α) / β) ^ t * ((1 - α) / β) ^ T) =
          ((1 - α) / β) ^ t * ((1 - α) / β * β) ^ T by rw [mul_pow]; ring, hq]
    have hlim : Tendsto (fun T : ℕ => ruleState α β t * (1 - α) ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).const_mul (ruleState α β t)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (hev T hT).symm
  · funext ω
    simp [hB, hV, ruleState]
  · funext ω
    simp only [hV, ruleState, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
    rw [pow_succ]
    field_simp
  · funext ω
    simp
  · funext ω
    change β = β * (1 / 1)
    norm_num
  · have h0 : t ≠ 0 := by omega
    simp [hP, h0]
  · intro h
    have := congrFun (congrFun h 0) ()
    simp only [hP, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false] at this
    have h2 : β * (1 / 2) = β := this
    linarith

/-! ### Why `V*_t ≠ s_t` is needed under uncertainty -/

/-- Cochrane (2023), §9.2, p. 264 (error E9.2): the date-`1` price level of the witness
`zero_debt_sunspot`, `2` if the first coin is heads and `2/3` otherwise. -/
noncomputable def coinPrice (ω : Bool × Bool) : ℝ := if ω.1 then 2 else 2 / 3

/-- Cochrane (2023), §9.2, p. 264: after date `1` the first coin flip is known. -/
theorem coin_first_known {t : ℕ} (ht : 1 ≤ t) {ω ω' : Bool × Bool}
    (h : ExpectationsFiniteTree.coinTree.info t ω' ω) : ω'.1 = ω.1 := by
  change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
  exact h.1

/-- Cochrane (2023), §9.2, p. 264: the coin-flip price `coinPrice` is known from date `1` on. -/
theorem coinPrice_known {t : ℕ} (ht : 1 ≤ t) :
    ExpectationsFiniteTree.coinSystem.E t coinPrice = coinPrice := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
  simp [coinPrice, coin_first_known ht h]

/-- Cochrane (2023), §9.2, p. 264: at date `0` the expected inverse of `coinPrice` is one,
`E_0 (1/P_1) = (1/2)(1/2) + (1/2)(3/2) = 1`. -/
theorem coinPrice_E0_inv (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 (fun ω => 1 / coinPrice ω) ω = 1 := by
  have htriv : ∀ a b, ExpectationsFiniteTree.coinTree.info 0 a b := fun a b => by
    change Setoid.ker (ExpectationsFiniteTree.coinObs 0) a b
    rw [Setoid.ker_def]
    simp [ExpectationsFiniteTree.coinObs]
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.coinTree.condE_of_trivial htriv]
  simp [ExpectationsFiniteTree.coinTree, coinPrice, Fintype.sum_prod_type]
  norm_num

/-- Cochrane (2023), §9.2, p. 264 (error E9.2): the hypothesis `V*_t ≠ s_t` of Theorem IT
cannot be dropped under uncertainty. In the two-coin tree, with `α = 1`, `s₀ = 0`, `P* ≡ 1`,
the debt is fully repaid at date `0` (`V*_0 = s_0`), and every other hypothesis holds, yet the
date-`1` price level is a sunspot (`2` or `2/3`) with `E_0(P_0/P_1) = 1`. -/
theorem zero_debt_sunspot {β : ℝ} (hβ0 : 0 < β) :
    ∃ B P Pstar Q s s0 V : ℕ → Bool × Bool → ℝ,
      Economy ExpectationsFiniteTree.coinSystem β B P Q s ∧ (∀ t ω, 0 < Pstar t ω) ∧
      ExpectationsFiniteTree.coinSystem.Adapted Pstar ∧
      ExpectationsFiniteTree.coinSystem.Adapted s0 ∧ (∀ t ω, |s0 t ω| ≤ 0) ∧
      StateInit B Pstar V ∧ StateRec Q Pstar s V ∧ SurplusRule 1 s0 V s ∧
      RateTarget ExpectationsFiniteTree.coinSystem β Pstar Q ∧ (∀ ω, B 0 ω ≠ 0) ∧
      V 0 = s 0 ∧ P ≠ Pstar := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem with h𝔼c
  set P : ℕ → Bool × Bool → ℝ := fun t ω => if t = 0 then 1 else coinPrice ω with hP
  set B : ℕ → Bool × Bool → ℝ := fun t _ => if t = 0 then 1 else 0 with hB
  have hcp : ∀ ω, 0 < coinPrice ω := fun ω => by
    unfold coinPrice
    split_ifs <;> norm_num
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => by
    simp only [hP]
    split_ifs
    · norm_num
    · exact hcp ω
  have hconst : ∀ t (c : ℝ), 𝔼c.E t (fun _ => c) = fun _ => c := fun t c => 𝔼c.const t c
  have hBc : ∀ t, B t = fun _ => (if t = 0 then 1 else 0 : ℝ) := fun t => rfl
  refine ⟨B, P, fun _ _ => 1, fun _ _ => β, B, fun _ _ => 0, B, ⟨hPpos, fun _ _ => hβ0,
    fun t => ?_, fun t => hconst t β, ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t ω => ?_⟩,
    fun _ _ => by norm_num, fun t => hconst t 1, fun t => hconst t 0, fun _ _ => by norm_num,
    ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun _ => by simp [hB], rfl, ?_⟩
  · rcases t with _ | t
    · exact hconst 0 1
    · have h : P (t + 1) = coinPrice := by
        funext ω
        simp [hP]
      rw [h]
      exact coinPrice_known (by omega)
  · exact hconst 0 1
  · rw [hBc]
    exact hconst t _
  · funext ω
    simp only [hB, hP, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    split_ifs <;> simp_all
  · rcases t with _ | t
    · have h : P 0 / P 1 = fun ω => 1 / coinPrice ω := by
        funext ω
        simp [hP]
      rw [h]
      funext ω
      change β = β * 𝔼c.E 0 (fun ω => 1 / coinPrice ω) ω
      rw [coinPrice_E0_inv]
      ring
    · have h : P (t + 1) / P (t + 1 + 1) = fun _ => 1 := by
        funext ω
        simp only [hP, Pi.div_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact div_self (hcp ω).ne'
      rw [h, hconst]
      funext ω
      simp
  · have hev : ∀ T, 1 ≤ T → β ^ T * 𝔼c.E t (B (t + T) / P (t + T)) ω = 0 := by
      intro T hT
      have h0 : t + T ≠ 0 := by omega
      have h : B (t + T) / P (t + T) = fun _ => 0 := by
        funext ω'
        simp only [hB, Pi.div_apply, h0, ↓reduceIte, zero_div]
      rw [h, hconst]
      simp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (hev T hT).symm
  · funext ω
    simp [hB]
  · funext ω
    simp only [hB, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
    simp
  · funext ω
    simp
  · funext ω
    change β = β * 𝔼c.E t (fun _ => 1 / 1) ω
    rw [hconst]
    norm_num
  · intro h
    have := congrFun (congrFun h 1) (true, true)
    simp [hP, coinPrice] at this

end Cochrane.AssetsRulesBalanceSheets.InflationTarget

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal rules with indexed debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.1–§9.3.3,
eqs. (9.7)–(9.14), pp. 265–269.

## Dating convention

Lean date `t` carries the real (indexed) debt `b t` outstanding at the start of date `t`, the
book's `b_{t−1}`. The flow condition (9.8) reads `b t = s t + β b (t + 1)`.

## Main results

* §9.3.1: `PresentValue.price_unique_of_strictMonoOn`, `existsUnique_price`: `b_{T−1} = s(P_T)`
  with `s`
  strictly increasing determines `P_T`; `eq_9_7_iff`: under (9.7) the price level is `P*_T`.
* §9.3.2: `PresentValue.real_iterate`, `PresentValue.hasSum_of_tvc`, `eq_9_9`: (9.8) iterated
  forward with the
  transversality condition gives (9.9) ex post; `hyperplane_equilibrium`,
  `not_determined_by_valuation`: (9.9) determines only the `β`-weighted sum of price levels;
  `price_eq_target_of_debtRule`, `money_pos_of_below`: the debt rule (9.11) gives `P = P*`, and
  `P < P*` means money is printed (9.10).
* **Theorem FR** for the interest-rate target (9.12):
  (a) `fr_perfectForesight`: under perfect foresight only `P = P*` satisfies (9.9) and (9.12);
  (b) `Sunspot.sunspot_counterexample`: under uncertainty the claim is **false** (error E9.9):
  an explicit infinite "settle-or-continue" event tree, for every `0 < β < 1` and every
  `0 < P_0 < 1 = P*_0`, satisfies (9.12) at every node, (9.8) on every edge with predetermined
  real debt, (9.9) at every node (genuine infinite sums of explicit conditional expectations),
  and the transversality condition;
  (c) `fr_jensen`: what survives under uncertainty is the one-sided bound `P_0 ≤ P*_0`;
  (d) `fr_unique_bounded` (via `unique_of_ratio_tvc`): uniqueness is restored under uncertainty if
  the price level is bounded above, or bounded away from zero — `Z_t = S_t/P_t` obeys
  `E_t Z_{t+1} = (Z_t − 1)/β`, so `Z_t − 1/(1 − β) = βᵏ E_t(Z_{t+k} − 1/(1 − β)) → 0`. The sunspot
  tree's prices are unbounded above and tend to zero (`settlePrice_unbounded`,
  `contPrice_tendsto_zero`).
* §9.3.3: `regular_solve`, `regular_tvc`, `regular_hasSum`: with `α_r > 0` the regular budget
  repays itself (the book's claim, checked correct, survey E9.6); `emergency_hasSum` (9.14);
  `total_hasSum`; the lagged-rule variant `lagged_tvc`, `lagged_tvc_iff`, `lagged_hasSum` needs
  `0 < α_r < 2`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRules

open Filter Topology PresentValue

/-! ### §9.3.1 Indexed debt in a one-period model -/

/-- Cochrane (2023), §9.3.1, p. 265: "this condition can determine the price level `P_T`,
although the debt is fully indexed" — with `s` strictly increasing and `b` in its range, there is
exactly one positive price level. -/
theorem existsUnique_price {s : ℝ → ℝ} (hs : StrictMonoOn s (Set.Ioi 0)) {b : ℝ}
    (hb : ∃ P, 0 < P ∧ b = s P) : ∃! P, 0 < P ∧ b = s P := by
  obtain ⟨P, hP, hbP⟩ := hb
  exact ⟨P, ⟨hP, hbP⟩, fun P' h' => price_unique_of_strictMonoOn hs h'.1 hP h'.2 hbP⟩

/-- Cochrane (2023), eq. (9.7), p. 265: with the rule `s_T(P_T) = b_{T−1} + θ (P_T − P*_T)`,
`θ ≠ 0`, the valuation `b_{T−1} = s_T(P_T)` holds if and only if `P_T = P*_T`. -/
theorem eq_9_7_iff {θ : ℝ} (hθ : θ ≠ 0) (b Pstar P : ℝ) :
    b = b + θ * (P - Pstar) ↔ P = Pstar := by
  constructor
  · intro h
    have h' : θ * (P - Pstar) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hθ
    · linarith
  · intro h
    rw [h]
    ring

/-! ### §9.3.2 A dynamic fiscal rule with indexed debt (ex post, along a path) -/

/-- Cochrane (2023), eq. (9.9), p. 266: with the surplus rule `s_t = s_{0,t} + θ (P_t − P*_t)`,
(9.8) and the transversality condition give
`b_{t−1} = ∑ⱼ βʲ s_{0,t+j} + θ ∑ⱼ βʲ (P_{t+j} − P*_{t+j})` (ex post). -/
theorem eq_9_9 {β θ : ℝ} {b s0 P Pstar : ℕ → ℝ}
    (h : ∀ t, b t = (s0 t + θ * (P t - Pstar t)) + β * b (t + 1)) (t : ℕ)
    (htvc : Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0))
    (hs0 : Summable (fun j => β ^ j * s0 (t + j)))
    (hP : Summable (fun j => β ^ j * (P (t + j) - Pstar (t + j)))) :
    b t = ∑' j, β ^ j * s0 (t + j) + θ * ∑' j, β ^ j * (P (t + j) - Pstar (t + j)) := by
  have hsum : Summable (fun j => β ^ j * (s0 (t + j) + θ * (P (t + j) - Pstar (t + j)))) := by
    have := hs0.add (hP.mul_left θ)
    refine this.congr fun j => ?_
    ring
  have hh := hasSum_of_tvc (s := fun t => s0 t + θ * (P t - Pstar t)) h t htvc hsum
  rw [← hh.tsum_eq, ← tsum_mul_left, ← hs0.tsum_add (hP.mul_left θ)]
  refine tsum_congr fun j => ?_
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267: an equilibrium path of the dynamic fiscal rule with
indexed debt (ex post, along one path): positive prices, the flow condition (9.8) with the rule
`s_t = s_{0,t} + θ (P_t − P*_t)`, and the transversality condition at every date. -/
def RuleEquilibrium (β θ : ℝ) (s0 Pstar P b : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, b t = (s0 t + θ * (P t - Pstar t)) + β * b (t + 1)) ∧
    ∀ t, Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0)

/-- Cochrane (2023), §9.3.2, p. 266: the discounted sum `Z_t = ∑ⱼ βʲ z_{t+j}` of a bounded
sequence obeys `Z_t = z_t + β Z_{t+1}`. -/
theorem tsum_shift {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} (hz : ∀ j, |z j| ≤ M)
    (t : ℕ) : ∑' j, β ^ j * z (t + j) = z t + β * ∑' j, β ^ j * z (t + 1 + j) := by
  rw [(summable_of_bounded hβ0 hβ1 hz t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by ring, pow_succ]
  ring

/-- Cochrane (2023), §9.3.2, p. 266: the discounted sum of a sequence bounded by `M` is bounded
by `M / (1 − β)`. -/
theorem abs_tsum_le {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} (hz : ∀ j, |z j| ≤ M)
    (t : ℕ) : |∑' j, β ^ j * z (t + j)| ≤ M / (1 - β) := by
  have hg : HasSum (fun j : ℕ => M * β ^ j) (M / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun j => β ^ j * z (t + j)) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hz (t + j)) (pow_nonneg hβ0 j)
  simpa [Real.norm_eq_abs] using this

/-- Cochrane (2023), §9.3.2, p. 266 ("the valuation equation and the surplus rule determine the
value of the sum `∑ βʲ P_{t+j}` but not the shape of that path"): adding to an equilibrium price
path any bounded `z` with `∑ⱼ βʲ zⱼ = 0` (keeping prices positive) gives another equilibrium with
the same initial debt; real debt changes by `θ ∑ⱼ βʲ z_{t+j}`. -/
theorem hyperplane_equilibrium {β θ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {s0 Pstar P b z : ℕ → ℝ} (hE : RuleEquilibrium β θ s0 Pstar P b)
    (hz : HasSum (fun j => β ^ j * z j) 0) (hzM : ∀ j, |z j| ≤ M) (hpos : ∀ t, 0 < P t + z t) :
    RuleEquilibrium β θ s0 Pstar (fun t => P t + z t)
        (fun t => b t + θ * ∑' j, β ^ j * z (t + j)) ∧
      b 0 + θ * ∑' j, β ^ j * z (0 + j) = b 0 := by
  obtain ⟨_, hflow, htvc⟩ := hE
  refine ⟨⟨hpos, fun t => ?_, fun t => ?_⟩, ?_⟩
  · beta_reduce
    rw [hflow t, tsum_shift hβ0 hβ1 hzM t]
    ring
  · have hZ : Tendsto (fun T => β ^ T * ∑' j, β ^ j * z (t + T + j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun T => β ^ T * (M / (1 - β))) (fun T => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
        exact mul_le_mul_of_nonneg_left (abs_tsum_le hβ0 hβ1 hzM (t + T)) (pow_nonneg hβ0 T)
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (M / (1 - β))
    have := (htvc t).add (hZ.const_mul θ)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun T => ?_
    ring
  · simp only [zero_add, hz.tsum_eq, mul_zero, add_zero]

/-- Cochrane (2023), §9.3.2, p. 266: the explicit deviation `z = (β/2, −1/2, 0, 0, …)`, whose
discounted sum is zero. -/
noncomputable def hyperplaneShift (β : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then β / 2 else if j = 1 then -1 / 2 else 0

/-- Cochrane (2023), §9.3.2, p. 266: `∑ⱼ βʲ zⱼ = 0` for `hyperplaneShift`. -/
theorem hasSum_hyperplaneShift (β : ℝ) : HasSum (fun j => β ^ j * hyperplaneShift β j) 0 := by
  have h : HasSum (fun j : ℕ => β ^ j * hyperplaneShift β j)
      (∑ j ∈ Finset.range 2, β ^ j * hyperplaneShift β j) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      simp [hyperplaneShift, h0, h1])
  convert h using 1
  simp [Finset.sum_range_succ, hyperplaneShift]
  ring

/-- Cochrane (2023), §9.3.2, p. 266 (perfect foresight): the valuation equation (9.9) and the
surplus rule do not determine the price level. With `P* ≡ 1`, `s₀ ≡ 1 − β` and real debt
`b ≡ 1`, both `P ≡ P*` and `P = P* + (β/2, −1/2, 0, …)` are equilibria with the same initial
debt. -/
theorem not_determined_by_valuation {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ P P' b b' : ℕ → ℝ, RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) P b ∧
      RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) P' b' ∧ b 0 = b' 0 ∧ P ≠ P' := by
  have hbase : RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    refine ⟨fun _ => one_pos, fun t => by ring, fun t => ?_⟩
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 : ℝ)
  have hzM : ∀ j, |hyperplaneShift β j| ≤ 1 := fun j => by
    unfold hyperplaneShift
    split_ifs
    · rw [abs_of_pos (by linarith)]
      linarith
    · norm_num
    · norm_num
  have hpos : ∀ t, 0 < (fun _ => (1 : ℝ)) t + hyperplaneShift β t := fun t => by
    unfold hyperplaneShift
    split_ifs <;> linarith
  obtain ⟨h1, h2⟩ := hyperplane_equilibrium hβ0.le hβ1 hbase (hasSum_hyperplaneShift β) hzM hpos
  refine ⟨_, _, _, _, hbase, h1, h2.symm, fun h => ?_⟩
  have := congrFun h 1
  simp [hyperplaneShift] at this

/-- Cochrane (2023), eqs. (9.10)–(9.11), p. 267: with the flow budget constraint including money,
`b_{t−1} = s_{0,t} + θ (P_t − P*_t) + β b_t + M_t/P_t`, the debt rule
`β b_t = b_{t−1} − s_{0,t}` and `M_t = 0` in equilibrium force `P_t = P*_t`. -/
theorem price_eq_target_of_debtRule {β θ b b' s0 P Pstar M : ℝ} (hθ : θ ≠ 0)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0) (hM : M = 0) :
    P = Pstar := by
  rw [hM, zero_div, add_zero, hrule] at hflow
  have h : θ * (P - Pstar) = 0 := by linarith
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hθ
  · linarith

/-- Cochrane (2023), §9.3.2, p. 267: under the debt rule (9.11), a price level below target
`P_t < P*_t` (with `θ > 0`) must result in money creation `M_t > 0` in (9.10). -/
theorem money_pos_of_below {β θ b b' s0 P Pstar M : ℝ} (hθ : 0 < θ) (hP : 0 < P)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0)
    (hlow : P < Pstar) : 0 < M := by
  rw [hrule] at hflow
  have h : M / P = θ * (Pstar - P) := by linarith
  have h2 : M = θ * (Pstar - P) * P := by
    field_simp at h
    linarith
  rw [h2]
  exact mul_pos (mul_pos hθ (by linarith)) hP

/-- Cochrane (2023), §9.3.2, p. 267: symmetrically, a price level above target means money is
soaked up, `M_t < 0`. -/
theorem money_neg_of_above {β θ b b' s0 P Pstar M : ℝ} (hθ : 0 < θ) (hP : 0 < P)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0)
    (hhigh : Pstar < P) : M < 0 := by
  rw [hrule] at hflow
  have h : M / P = θ * (Pstar - P) := by linarith
  have h2 : M = θ * (Pstar - P) * P := by
    field_simp at h
    linarith
  rw [h2]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hθ (by linarith)) hP

/-! ### Theorem FR (a): perfect foresight -/

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (a)**): under perfect foresight, if the
interest rate follows the target, `β P_t/P_{t+1} = β P*_t/P*_{t+1}` ((9.12)), and the valuation
(9.9) holds at date 0 with the initial debt equal to the present value of `s₀` (the book's
`a(β) = 0` case), then `P_t = P*_t` at every date (`θ ≠ 0`, `∑ βʲ P*_j < ∞`). -/
theorem fr_perfectForesight {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ≠ 0) {P Pstar s0 : ℕ → ℝ}
    {b0 : ℝ} (hP : ∀ t, 0 < P t) (hPs : ∀ t, 0 < Pstar t)
    (h912 : ∀ t, β * (P t / P (t + 1)) = β * (Pstar t / Pstar (t + 1)))
    (h99 : HasSum (fun j => β ^ j * (s0 j + θ * (P j - Pstar j))) b0)
    (hb : HasSum (fun j => β ^ j * s0 j) b0) (hPsum : Summable (fun j => β ^ j * Pstar j)) :
    P = Pstar := by
  set c := P 0 / Pstar 0 with hc
  have hscale : ∀ t, P t = c * Pstar t := by
    intro t
    induction t with
    | zero =>
      rw [hc]
      field_simp [(hPs 0).ne']
    | succ t ih =>
      have h := mul_left_cancel₀ hβ0.ne' (h912 t)
      rw [ih] at h
      have hP1 := (hP (t + 1)).ne'
      have hPs1 := (hPs (t + 1)).ne'
      have hPt := (hPs t).ne'
      rw [div_eq_div_iff hP1 hPs1] at h
      have : Pstar t * (c * Pstar (t + 1)) = Pstar t * P (t + 1) := by linarith
      exact (mul_left_cancel₀ hPt this).symm
  have hdiff := h99.sub hb
  have hfun : (fun j => β ^ j * (s0 j + θ * (P j - Pstar j)) - β ^ j * s0 j) =
      fun j => θ * (c - 1) * (β ^ j * Pstar j) := by
    funext j
    rw [hscale j]
    ring
  rw [hfun, sub_self] at hdiff
  have h2 := hPsum.hasSum.mul_left (θ * (c - 1))
  have h0 : θ * (c - 1) * ∑' j, β ^ j * Pstar j = 0 := h2.unique hdiff
  have hpos : 0 < ∑' j, β ^ j * Pstar j :=
    hPsum.tsum_pos (fun j => (mul_pos (pow_pos hβ0 j) (hPs j)).le) 0 (by simpa using hPs 0)
  have hc1 : c = 1 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hθ
      · linarith
    · linarith
  funext t
  rw [hscale t, hc1, one_mul]

/-- Cochrane (2023), §9.3.2, p. 267 (existence for Theorem FR (a)): under perfect foresight with
bounded `s₀`, the price path `P = P*` with real debt `b_t = ∑ⱼ βʲ s_{0,t+j}` is an equilibrium of
the
fiscal rule. -/
theorem fr_exists {β θ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s0 Pstar : ℕ → ℝ}
    (hPs : ∀ t, 0 < Pstar t) (hM : ∀ t, |s0 t| ≤ M) :
    RuleEquilibrium β θ s0 Pstar Pstar (fun t => ∑' j, β ^ j * s0 (t + j)) := by
  refine ⟨hPs, fun t => ?_, fun t => ?_⟩
  · beta_reduce
    rw [tsum_shift hβ0 hβ1 hM t]
    ring
  · refine squeeze_zero_norm (a := fun T => β ^ T * (M / (1 - β))) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
      exact mul_le_mul_of_nonneg_left (abs_tsum_le hβ0 hβ1 hM (t + T)) (pow_nonneg hβ0 T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (M / (1 - β))

/-- Cochrane (2023), §9.3.2, p. 266 ("with `s_{0,t} = a(L)ε_{s,t}` and `a(β) = 0` … as there are no
innovations to the first term of (9.9), there are no innovations to the second term as well"): if
real debt `b_{t−1}` and the first term `X` are known at `t − 1` and `b_{t−1} = X + θ Y` with `θ ≠
0`, then
the weighted sum of price deviations `Y` is known at `t − 1` (has no innovation at `t`) — only the
weighted sum, not each price level. -/
theorem no_innovation_weighted_sum {Ω : Type*} (𝔼 : ExpectationSystem Ω) {θ : ℝ} (hθ : θ ≠ 0)
    {s : ℕ} {b X Y : Ω → ℝ} (hb : 𝔼.E s b = b) (hX : 𝔼.E s X = X) (h : b = X + θ • Y) :
    𝔼.E s Y = Y := by
  have hY : Y = θ⁻¹ • (b - X) := by
    rw [h, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hθ, one_smul]
  rw [hY, map_smul, map_sub, hb, hX]

/-! ### Theorem FR (c): the Jensen bound under uncertainty -/

/-- Cochrane (2023), §9.3.2, p. 267 (supporting line for Theorem FR (c)): for `y, m > 0`,
`2/m − y/m² ≤ 1/y`. -/
theorem inv_ge_tangent {y m : ℝ} (hy : 0 < y) (hm : 0 < m) : 2 / m - y / m ^ 2 ≤ 1 / y := by
  have key : 0 ≤ m * (y - m) ^ 2 := mul_nonneg hm.le (sq_nonneg _)
  rw [div_sub_div _ _ hm.ne' (pow_ne_zero 2 hm.ne'), div_le_div_iff₀ (by positivity) hy]
  nlinarith [key]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.3.2, p. 267 (Jensen's inequality used in Theorem FR (c)): under `PullOut`,
`1/E_t y ≤ E_t (1/y)` for positive `y` with positive conditional mean. -/
theorem jensen_inv (h𝔼 : 𝔼.PullOut) {t : ℕ} {y : Ω → ℝ} (hy : ∀ ω, 0 < y ω)
    (hm : ∀ ω, 0 < 𝔼.E t y ω) (ω : Ω) : 1 / 𝔼.E t y ω ≤ 𝔼.E t (fun ω => 1 / y ω) ω := by
  set m := 𝔼.E t y with hm_def
  have hmk : 𝔼.E t m = m := 𝔼.E_E_self t y
  have hinv : 𝔼.E t m⁻¹ = m⁻¹ := InflationTarget.known_inv 𝔼 h𝔼 hmk (fun ω => (hm ω).ne')
  have hinv2 : 𝔼.E t (m⁻¹ * m⁻¹) = m⁻¹ * m⁻¹ := InflationTarget.known_mul 𝔼 h𝔼 hinv hinv
  have hle : (2 : ℝ) • m⁻¹ - (m⁻¹ * m⁻¹) * y ≤ fun ω => 1 / y ω := fun ω => by
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul]
    have h1 := inv_ge_tangent (hy ω) (hm ω)
    have h2 : 2 * (m ω)⁻¹ - (m ω)⁻¹ * (m ω)⁻¹ * y ω = 2 / m ω - y ω / m ω ^ 2 := by ring
    linarith
  have hmono := 𝔼.mono t hle ω
  rw [map_sub, map_smul, hinv, h𝔼 t _ _ hinv2] at hmono
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul] at hmono
  have hm0 := (hm ω).ne'
  calc 1 / m ω = 2 * (m ω)⁻¹ - (m ω)⁻¹ * (m ω)⁻¹ * m ω := by field_simp; ring
    _ ≤ _ := hmono

/-- Cochrane (2023), eq. (9.12), p. 267: with a deterministic target `P*`, the interest-rate
target `β E_t (P_t/P_{t+1}) = β P*_t/P*_{t+1}` makes `y_t = P*_t/P_t` a martingale. -/
theorem fr_martingale (h𝔼 : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) {P : ℕ → Ω → ℝ}
    {Pstar : ℕ → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPs : ∀ t, 0 < Pstar t) (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β * (Pstar t / Pstar (t + 1)))
    (t : ℕ) : 𝔼.E t (fun ω => Pstar (t + 1) / P (t + 1) ω) = fun ω => Pstar t / P t ω := by
  have hsplit : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  have h1 := h912 t
  rw [hsplit, h𝔼 t _ _ (hPa t)] at h1
  have hy : (fun ω => Pstar (t + 1) / P (t + 1) ω) = Pstar (t + 1) • fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hy, map_smul]
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h2 ⊢
  have hPt := (hP t ω).ne'
  have hPs1 := (hPs (t + 1)).ne'
  have h3 : 𝔼.E t (fun ω => 1 / P (t + 1) ω) ω = Pstar t / Pstar (t + 1) / P t ω := by
    field_simp
    have := mul_left_cancel₀ hβ0.ne' (by linarith : β * (P t ω * 𝔼.E t (fun ω =>
      1 / P (t + 1) ω) ω) = β * (Pstar t / Pstar (t + 1)))
    field_simp at this
    linarith
  rw [h3]
  field_simp

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (c)**): under genuine uncertainty, with a
deterministic target `P*`, the interest-rate target (9.12) and the date-0 valuation (9.9) in
expected form, `b_{−1} = ∑ βʲ E_0 s_{0,j} + θ ∑ βʲ E_0 (P_j − P*_j)`, with `b_{−1}` equal to the
present value of `s₀`, force only `P_0 ≤ P*_0` (Jensen's inequality, since `P*_t/P_t` is a
martingale). -/
theorem fr_jensen (h𝔼 : 𝔼.PullOut) {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ≠ 0) {P s0 : ℕ → Ω → ℝ}
    {Pstar : ℕ → ℝ} {b0 : Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPs : ∀ t, 0 < Pstar t)
    (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β * (Pstar t / Pstar (t + 1)))
    (h99 : ∀ ω, HasSum (fun j => β ^ j * (𝔼.E 0 (s0 j) ω + θ * (𝔼.E 0 (P j) ω - Pstar j)))
      (b0 ω))
    (hb : ∀ ω, HasSum (fun j => β ^ j * 𝔼.E 0 (s0 j) ω) (b0 ω))
    (hPsum : Summable (fun j => β ^ j * Pstar j)) (ω : Ω) : P 0 ω ≤ Pstar 0 := by
  set y : ℕ → Ω → ℝ := fun t ω => Pstar t / P t ω with hy_def
  have hypos : ∀ t ω, 0 < y t ω := fun t ω => div_pos (hPs t) (hP t ω)
  have hmart : ∀ t, 𝔼.E t (y (t + 1)) = y t :=
    fun t => fr_martingale 𝔼 h𝔼 hβ0 hP hPs hPa h912 t
  have hy0 : 𝔼.E 0 (y 0) = y 0 := by
    have : y 0 = Pstar 0 • (P 0)⁻¹ := by
      funext ω
      simp only [hy_def, Pi.smul_apply, Pi.inv_apply, smul_eq_mul]
      ring
    rw [this, map_smul, InflationTarget.known_inv 𝔼 h𝔼 (hPa 0) (fun ω => (hP 0 ω).ne')]
  have hE0 : ∀ j, 𝔼.E 0 (y j) = y 0 := by
    intro j
    induction j with
    | zero => exact hy0
    | succ j ih => rw [← 𝔼.tower (Nat.zero_le j), hmart j, ih]
  have hbound : ∀ j, (P 0 ω / Pstar 0) * Pstar j ≤ 𝔼.E 0 (P j) ω := by
    intro j
    have hJ := jensen_inv 𝔼 h𝔼 (hypos j) (fun ω => by rw [hE0 j]; exact hypos 0 ω) ω
    rw [hE0 j] at hJ
    have hfun : (fun ω => 1 / y j ω) = (Pstar j)⁻¹ • P j := by
      funext ω
      simp only [hy_def, Pi.smul_apply, smul_eq_mul]
      field_simp [(hP j ω).ne', (hPs j).ne']
    rw [hfun, map_smul] at hJ
    simp only [hy_def, Pi.smul_apply, smul_eq_mul] at hJ
    have hPs0 := (hPs 0).ne'
    have hP0 := (hP 0 ω).ne'
    have hPsj := hPs j
    rw [one_div_div] at hJ
    calc P 0 ω / Pstar 0 * Pstar j ≤ (Pstar j)⁻¹ * 𝔼.E 0 (P j) ω * Pstar j :=
          mul_le_mul_of_nonneg_right hJ hPsj.le
      _ = 𝔼.E 0 (P j) ω := by field_simp
  have hdiff := (h99 ω).sub (hb ω)
  rw [sub_self] at hdiff
  have hg : HasSum (fun j => β ^ j * (𝔼.E 0 (P j) ω - Pstar j)) 0 := by
    have := hdiff.mul_left θ⁻¹
    rw [mul_zero] at this
    refine this.congr_fun fun j => ?_
    field_simp
    ring
  set c := P 0 ω / Pstar 0 with hc
  have hf : HasSum (fun j => (c - 1) * (β ^ j * Pstar j)) ((c - 1) * ∑' j, β ^ j * Pstar j) :=
    hPsum.hasSum.mul_left (c - 1)
  have hle := hasSum_le (fun j => by
    have := hbound j
    have hb' := pow_pos hβ0 j
    nlinarith) hf hg
  have hpos : 0 < ∑' j, β ^ j * Pstar j :=
    hPsum.tsum_pos (fun j => (mul_pos (pow_pos hβ0 j) (hPs j)).le) 0 (by simpa using hPs 0)
  have hc1 : c ≤ 1 := by nlinarith
  rw [hc, div_le_one (hPs 0)] at hc1
  exact hc1

/-! ### Theorem FR (d): bounded price levels restore uniqueness -/

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (d)**, core, answering the open question of
E9.9): with `P* ≡ 1`, let `S_t` be a process with `S_t = P_t + β S_{t+1}`, `S_{t+1}` known at `t`
(predetermined real debt) and `S_0 = 1/(1 − β)`, and let `1/P` be a martingale ((9.12)). Then
`Z_t = S_t/P_t` obeys `E_t Z_{t+1} = (Z_t − 1)/β`; if `βᵏ E_t Z_{t+k} → 0`, then `P ≡ 1 = P*`. -/
theorem unique_of_ratio_tvc (h𝔼 : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {P S : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hmart : ∀ t, 𝔼.E t (fun ω => 1 / P (t + 1) ω) = fun ω => 1 / P t ω)
    (hrec : ∀ t, S t = P t + β • S (t + 1)) (hpre : ∀ t, 𝔼.E t (S (t + 1)) = S (t + 1))
    (hS0 : S 0 = fun _ => 1 / (1 - β))
    (hZ : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω)
      atTop (𝓝 0)) :
    P = fun _ _ => 1 := by
  set A := 1 / (1 - β) with hA_def
  have h1β : 1 - β ≠ 0 := by linarith
  have hA1 : 1 + β * A = A := by rw [hA_def]; field_simp; ring
  have hA0 : A ≠ 0 := by rw [hA_def]; exact one_div_ne_zero h1β
  -- the recursion for Z
  have hZrec : ∀ t, 𝔼.E t (fun ω => S (t + 1) ω / P (t + 1) ω) =
      fun ω => (S t ω / P t ω - 1) / β := by
    intro t
    have hsplit : (fun ω => S (t + 1) ω / P (t + 1) ω) =
        S (t + 1) * fun ω => 1 / P (t + 1) ω := by
      funext ω
      simp only [Pi.mul_apply]
      ring
    rw [hsplit, h𝔼 t _ _ (hpre t), hmart t]
    funext ω
    have h := congrFun (hrec t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h ⊢
    have hP0 := (hP t ω).ne'
    have hS1 : S (t + 1) ω = (S t ω - P t ω) / β := by
      rw [eq_div_iff hβ0.ne']
      linarith
    rw [hS1]
    field_simp
  set X : ℕ → Ω → ℝ := fun t ω => S t ω / P t ω - A with hX_def
  have hX : ∀ t, X t = β • 𝔼.E t (X (t + 1)) := by
    intro t
    have hXs : X (t + 1) = (fun ω => S (t + 1) ω / P (t + 1) ω) - fun _ => A := by
      funext ω
      simp [hX_def]
    rw [hXs, map_sub, hZrec t, 𝔼.const]
    funext ω
    simp only [hX_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linarith
  have hXtvc : TVC 𝔼 β X := fun t ω => by
    have e : ∀ k, β ^ k * 𝔼.E t (X (t + k)) ω =
        β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω - β ^ k * A := fun k => by
      have hXs : X (t + k) = (fun ω => S (t + k) ω / P (t + k) ω) - fun _ => A := by
        funext ω
        simp [hX_def]
      rw [hXs, map_sub, 𝔼.const]
      simp only [Pi.sub_apply]
      ring
    simp_rw [e]
    simpa using (hZ t ω).sub ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const A)
  have hX0 : ∀ t ω, X t ω = 0 := fun t ω => congrFun (eq_zero_of_tvc 𝔼 hX hXtvc t) ω
  have hSP : ∀ t ω, S t ω = A * P t ω := by
    intro t ω
    have h := hX0 t ω
    simp only [hX_def] at h
    have hP0 := (hP t ω).ne'
    field_simp at h
    linarith
  have hknown : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1) := by
    intro t
    have e : P (t + 1) = A⁻¹ • S (t + 1) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, hSP]
      field_simp
    rw [e, map_smul, hpre t]
  funext t
  induction t with
  | zero =>
    funext ω
    have h := hSP 0 ω
    rw [hS0] at h
    have : A * 1 = A * P 0 ω := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hA0 this).symm
  | succ t ih =>
    have hinv : 𝔼.E t (P (t + 1))⁻¹ = (P (t + 1))⁻¹ :=
      InflationTarget.known_inv 𝔼 h𝔼 (hknown t) (fun ω => (hP (t + 1) ω).ne')
    have e1 : (fun ω => 1 / P (t + 1) ω) = (P (t + 1))⁻¹ := by
      funext ω
      simp
    have h := hmart t
    rw [e1, hinv, ih] at h
    funext ω
    have h2 := congrFun h ω
    simp only [Pi.inv_apply] at h2
    have := (hP (t + 1) ω).ne'
    field_simp at h2
    linarith

/-- Cochrane (2023), §9.3.2, p. 266 (supporting Theorem FR (d)): if `S_t = P_t + β E_t S_{t+1}`
with `P > 0` adapted and the transversality condition `βᵏ E_t S_{t+k} → 0`, then
`0 ≤ S_t`, and `S_t ≤ M/(1 − β)` when `P ≤ M`. -/
theorem value_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P S : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P) (hsol : ForwardSolution.Solves 𝔼 β P S)
    (hTS : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0)) (t : ℕ) (ω : Ω) :
    0 ≤ S t ω ∧ ∀ M, (∀ t ω, P t ω ≤ M) → S t ω ≤ M / (1 - β) := by
  have hpart := tendsto_partialSums_of_tvc 𝔼 hPa hsol t ω (hTS t ω)
  have hEnn : ∀ j, 0 ≤ 𝔼.E t (P (t + j)) ω := fun j => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ P (t + j) from fun ω => (hP _ ω).le) ω
    rwa [𝔼.const] at this
  refine ⟨ge_of_tendsto' hpart fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg hβ0.le j) (hEnn j), fun M hM => ?_⟩
  have hM0 : 0 ≤ M := (hP 0 ω).le.trans (hM 0 ω)
  refine le_of_tendsto' hpart fun k => ?_
  have hEM : ∀ j, 𝔼.E t (P (t + j)) ω ≤ M := fun j => by
    have := 𝔼.mono t (show P (t + j) ≤ fun _ => M from fun ω => hM _ ω) ω
    rwa [𝔼.const] at this
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  calc ∑ j ∈ Finset.range k, β ^ j * 𝔼.E t (P (t + j)) ω
      ≤ ∑ j ∈ Finset.range k, β ^ j * M :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hEM j) (pow_nonneg hβ0.le j)
    _ = M * ∑ j ∈ Finset.range k, β ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ M * ∑' j, β ^ j := mul_le_mul_of_nonneg_left
        (hgeo.sum_le_tsum _ fun j _ => pow_nonneg hβ0.le j) hM0
    _ = M / (1 - β) := by rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]

/-- Cochrane (2023), §9.3.2, p. 266 (**Theorem FR (d)**, settling E9.9): under genuine
uncertainty (any expectation system with the pull-out property), with `P* ≡ 1`, real debt
following (9.8) with the rule `s_t = (1 − β) b̄ + θ (P_t − 1)` (`θ ≠ 0`), predetermined real debt,
initial debt `b_{−1} = b̄` equal to the present value of `s₀`, the transversality condition, and
the interest-rate target (9.12): if the price level is **bounded above, or bounded away from
zero**, then `P_t = P*_t = 1` at every date and state. Together with `Sunspot`, whose prices are
unbounded above and approach zero, this settles the question. -/
theorem fr_unique_bounded (h𝔼 : 𝔼.PullOut) {β θ bbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {P b : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (b (t + T)) ω) atTop (𝓝 0))
    (hbdd : (∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) :
    P = fun _ _ => 1 := by
  have h1β : 1 - β ≠ 0 := by linarith
  set A := 1 / (1 - β) with hA_def
  set S : ℕ → Ω → ℝ := fun t ω => A + (b t ω - bbar) / θ with hS_def
  have hSlin : ∀ t, S t = (fun _ => A - bbar / θ) + θ⁻¹ • b t := fun t => by
    funext ω
    simp only [hS_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hrec : ∀ t, S t = P t + β • S (t + 1) := by
    intro t
    funext ω
    simp only [hS_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hflow t ω, hA_def]
    field_simp
    ring
  have hSpre : ∀ t, 𝔼.E t (S (t + 1)) = S (t + 1) := fun t => by
    rw [hSlin, map_add, 𝔼.const, map_smul, hpre t]
  have hS0 : S 0 = fun _ => 1 / (1 - β) := by
    funext ω
    simp [hS_def, hb0 ω, hA_def]
  have hmart : ∀ t, 𝔼.E t (fun ω => 1 / P (t + 1) ω) = fun ω => 1 / P t ω := by
    intro t
    have h := fr_martingale 𝔼 h𝔼 hβ0 (Pstar := fun _ => 1) hP (fun _ => one_pos) hPa
      (fun t => by rw [h912 t]; funext; simp) t
    simpa using h
  have hTS : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0) := by
    intro t ω
    have e : ∀ k, β ^ k * 𝔼.E t (S (t + k)) ω =
        (A - bbar / θ) * β ^ k + θ⁻¹ * (β ^ k * 𝔼.E t (b (t + k)) ω) := fun k => by
      rw [hSlin, map_add, 𝔼.const, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [e]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (A - bbar / θ)).add
      ((htvc t ω).const_mul θ⁻¹)
  have hsol : ForwardSolution.Solves 𝔼 β P S := fun t => by
    rw [hSpre t, hrec t]
    abel
  have hbnd := value_bounds 𝔼 hβ0 hβ1 hP hPa hsol hTS
  have hyiter : ∀ t k, 𝔼.E t (fun ω => 1 / P (t + k) ω) = fun ω => 1 / P t ω := by
    intro t k
    induction k with
    | zero =>
      simp only [add_zero]
      rw [show (fun ω => 1 / P t ω) = (P t)⁻¹ from funext fun ω => by simp]
      exact InflationTarget.known_inv 𝔼 h𝔼 (hPa t) (fun ω => (hP t ω).ne')
    | succ k ih =>
      rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t k), hmart (t + k), ih]
  refine unique_of_ratio_tvc 𝔼 h𝔼 hβ0 hβ1 hP hmart hrec hSpre hS0 fun t ω => ?_
  have hZnn : ∀ k, 0 ≤ 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω := fun k => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ fun ω => S (t + k) ω / P (t + k) ω from
      fun ω => div_nonneg (hbnd _ ω).1 (hP _ ω).le) ω
    rwa [𝔼.const] at this
  rcases hbdd with ⟨M, hM⟩ | ⟨m, hm, hm'⟩
  · -- bounded above: E_t Z_{t+k} ≤ (M/(1 − β)) E_t (1/P_{t+k}) = (M/(1 − β))/P_t
    have hle : ∀ k, 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤ M / (1 - β) * (1 / P t ω) :=
      fun k => by
        have hmono := 𝔼.mono t (show (fun ω => S (t + k) ω / P (t + k) ω) ≤
            (M / (1 - β)) • fun ω => 1 / P (t + k) ω from fun ω => by
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right ((hbnd _ ω).2 M hM) (hP _ ω).le) ω
        rwa [map_smul, hyiter t k] at hmono
    refine squeeze_zero (fun k => mul_nonneg (pow_nonneg hβ0.le k) (hZnn k))
      (fun k => mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hβ0.le k)) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (M / (1 - β) * (1 / P t ω))
  · -- bounded away from zero: E_t Z_{t+k} ≤ E_t S_{t+k}/m
    have hle : ∀ k, 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤
        m⁻¹ * 𝔼.E t (S (t + k)) ω := fun k => by
      have hmono := 𝔼.mono t (show (fun ω => S (t + k) ω / P (t + k) ω) ≤
          m⁻¹ • S (t + k) from fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (hbnd _ ω).1 hm (hm' _ ω)) ω
      rwa [map_smul] at hmono
    have hb2 : ∀ k, β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤
        m⁻¹ * (β ^ k * 𝔼.E t (S (t + k)) ω) := fun k => by
      calc _ ≤ β ^ k * (m⁻¹ * 𝔼.E t (S (t + k)) ω) :=
            mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hβ0.le k)
        _ = _ := by ring
    refine squeeze_zero (fun k => mul_nonneg (pow_nonneg hβ0.le k) (hZnn k)) hb2 ?_
    simpa using (hTS t ω).const_mul m⁻¹

/-! ### Theorem FR (b): the settle-or-continue sunspot tree -/

namespace Sunspot

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the coefficient
`L = c₀/(1 − β²)` of the value of the continue node. -/
noncomputable def coefL (β c0 : ℝ) : ℝ := c0 / (1 - β ^ 2)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the coefficient
`K = 1/(1 − β) − c₀/(1 − β²)` of the value of the continue node. -/
noncomputable def coefK (β c0 : ℝ) : ℝ := 1 / (1 - β) - c0 / (1 - β ^ 2)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level `c₀ βⁿ` at the date-`n`
node where the path has not yet settled. -/
noncomputable def contPrice (β c0 : ℝ) (n : ℕ) : ℝ := c0 * β ^ n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): `S_n = K β⁻ⁿ + L βⁿ`, the expected
present value `∑ⱼ βʲ E_n P_{n+j}` at the date-`n` continue node (and the value of a node that
settled at date `n`). -/
noncomputable def value (β c0 : ℝ) (n : ℕ) : ℝ := coefK β c0 * β⁻¹ ^ n + coefL β c0 * β ^ n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level `(1 − β) S_n` at which
a path that settles at date `n` stays forever. -/
noncomputable def settlePrice (β c0 : ℝ) (n : ℕ) : ℝ := (1 - β) * value β c0 n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the probability of settling at date
`n + 1` given that the path has not settled by date `n`, chosen so that `1/P` is a martingale. -/
noncomputable def settleProb (β c0 : ℝ) (n : ℕ) : ℝ :=
  (1 / contPrice β c0 (n + 1) - 1 / contPrice β c0 n) /
    (1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the probability, at the date-`t`
continue node, that the path is still unsettled at date `t + j`. -/
noncomputable def contProb (β c0 : ℝ) (t j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (1 - settleProb β c0 (t + i))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the explicit conditional expectation,
at the date-`t` continue node, of a date-`(t + j)` random variable `X`. A node is `none` (not yet
settled) or `some k` (settled at date `k`); with probability `contProb t j` the path is still
unsettled, and with probability `contProb t i · settleProb (t + i)` it settled at date `t + i + 1`.
At a settled node the conditional expectation is the value itself. -/
noncomputable def condE (β c0 : ℝ) (t j : ℕ) (X : Option ℕ → ℝ) : ℝ :=
  contProb β c0 t j * X none +
    ∑ i ∈ Finset.range j, contProb β c0 t i * settleProb β c0 (t + i) * X (some (t + i + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level at a date-`n` node. -/
noncomputable def price (β c0 : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  x.elim (contPrice β c0 n) (settlePrice β c0)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): `∑ⱼ βʲ E_n P_{n+j}` at a date-`n`
node. -/
noncomputable def nodeValue (β c0 : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  x.elim (value β c0 n) (value β c0)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): real (indexed) debt outstanding at a
date-`n` node, `b̄ + θ (∑ⱼ βʲ E_n P_{n+j} − 1/(1 − β))`. -/
noncomputable def debt (β c0 θ bbar : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  bbar + θ * (nodeValue β c0 n x - 1 / (1 - β))

/-- Cochrane (2023), §9.3.2, p. 266 (counterexample E9.9): the surplus at a date-`n` node,
`s_{0} + θ (P − P*)` with `s₀ = (1 − β) b̄` and `P* ≡ 1`. -/
noncomputable def surplus (β c0 θ bbar : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  (1 - β) * bbar + θ * (price β c0 n x - 1)

variable {β c0 : ℝ}

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n = P_n + β S_{n+1}` along the continue path. -/
theorem value_rec (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    value β c0 n = contPrice β c0 n + β * value β c0 (n + 1) := by
  have hβ := hβ0.ne'
  have h2 : 1 - β ^ 2 ≠ 0 := by nlinarith
  unfold value contPrice coefL coefK
  rw [pow_succ β⁻¹, pow_succ β]
  field_simp
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_0 = 1/(1 − β)`, the present value of `P* ≡ 1`. -/
theorem value_zero : value β c0 0 = 1 / (1 - β) := by
  simp [value, coefK, coefL]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `K > 0` when `c₀ < 1`. -/
theorem coefK_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc1 : c0 < 1) : 0 < coefK β c0 := by
  unfold coefK
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β ^ 2 := by nlinarith
  rw [show 1 / (1 - β) - c0 / (1 - β ^ 2) = (1 + β - c0) / (1 - β ^ 2) by field_simp; ring]
  exact div_pos (by linarith) h2

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `L > 0`. -/
theorem coefL_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) : 0 < coefL β c0 :=
  div_pos hc0 (by nlinarith)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n > 0`. -/
theorem value_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    0 < value β c0 n := by
  unfold value
  have := coefK_pos hβ0 hβ1 hc1
  have := coefL_pos hβ0 hβ1 hc0
  positivity

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n ≤ (K + L) β⁻ⁿ`. -/
theorem value_le (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (n : ℕ) :
    value β c0 n ≤ (coefK β c0 + coefL β c0) * β⁻¹ ^ n := by
  unfold value
  have hL := coefL_pos hβ0 hβ1 hc0
  have h1 : β ^ n ≤ β⁻¹ ^ n := by
    have : β ^ n ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have : 1 ≤ β⁻¹ ^ n := one_le_pow₀ (one_le_inv₀ hβ0 |>.mpr hβ1.le)
    linarith
  nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settle price exceeds the current continue price,
`P_n < (1 − β) S_{n+1}`; this is where `c₀ < 1` (i.e. `P_0 < P*_0`) is used. -/
theorem contPrice_lt_settlePrice (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (n : ℕ) : contPrice β c0 n < settlePrice β c0 (n + 1) := by
  unfold contPrice settlePrice value coefK coefL
  set y := β ^ n with hy_def
  have hy : 0 < y := pow_pos hβ0 n
  have hy1 : y ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hβ := hβ0.ne'
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  have hinv : β⁻¹ ^ (n + 1) = (y * β)⁻¹ := by rw [inv_pow, pow_succ]
  rw [hinv, pow_succ β n, ← hy_def]
  rw [show (1 - β) * ((1 / (1 - β) - c0 / (1 - β ^ 2)) * (y * β)⁻¹ + c0 / (1 - β ^ 2) * (y * β))
      = ((1 + β - c0) + c0 * y ^ 2 * β ^ 2) / ((1 + β) * y * β) by
    have h3 : 1 - β ^ 2 = (1 - β) * (1 + β) := by ring
    rw [h3]
    field_simp]
  rw [lt_div_iff₀ (by positivity)]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have h4 : c0 * y ^ 2 * β ≤ c0 * β := by
    have := mul_le_mul_of_nonneg_left hy2 (mul_nonneg hc0.le hβ0.le)
    nlinarith
  nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settle probability lies strictly between
`1 − β` and `1`. -/
theorem settleProb_bounds (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    1 - β < settleProb β c0 n ∧ settleProb β c0 n < 1 := by
  have hlt := contPrice_lt_settlePrice hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  have hc' : contPrice β c0 (n + 1) = β * contPrice β c0 n := by
    unfold contPrice
    ring
  set c := contPrice β c0 n
  set H := settlePrice β c0 (n + 1)
  have hH : 0 < H := lt_trans hc hlt
  have hβ := hβ0.ne'
  unfold settleProb
  rw [hc']
  have hD : 0 < 1 / (β * c) - 1 / H := by
    rw [sub_pos, div_lt_div_iff₀ hH (by positivity)]
    nlinarith
  constructor
  · rw [lt_div_iff₀ hD]
    have : 0 < 1 / H := by positivity
    have e : (1 - β) * (1 / (β * c) - 1 / H) = (1 / (β * c) - 1 / c) - (1 - β) * (1 / H) := by
      field_simp
    rw [e]
    nlinarith
  · rw [div_lt_one hD, sub_lt_sub_iff_left]
    exact one_div_lt_one_div_of_lt hc hlt

/-- Cochrane (2023), eq. (9.12), p. 267 (E9.9): with these probabilities `1/P` is a martingale at
the continue node, `p/H_{n+1} + (1 − p)/P_{n+1} = 1/P_n`. -/
theorem martingale_inv (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    settleProb β c0 n / settlePrice β c0 (n + 1) +
      (1 - settleProb β c0 n) / contPrice β c0 (n + 1) = 1 / contPrice β c0 n := by
  have hlt := contPrice_lt_settlePrice hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  have hc' : 0 < contPrice β c0 (n + 1) := by unfold contPrice; positivity
  have hH : 0 < settlePrice β c0 (n + 1) := lt_trans hc hlt
  have h1 : contPrice β c0 (n + 1) < settlePrice β c0 (n + 1) := by
    have : contPrice β c0 (n + 1) = β * contPrice β c0 n := by unfold contPrice; ring
    rw [this]
    nlinarith
  have hne : settlePrice β c0 (n + 1) - contPrice β c0 (n + 1) ≠ 0 := by linarith
  have hD : 1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [div_eq_div_iff hc'.ne' hH.ne'] at h
    linarith
  have hp : settleProb β c0 n * (1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1)) =
      1 / contPrice β c0 (n + 1) - 1 / contPrice β c0 n := by
    unfold settleProb
    field_simp
  linear_combination -hp

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `contProb t (j + 1) = (1 − p_t) contProb (t + 1) j`. -/
theorem contProb_succ' (t j : ℕ) :
    contProb β c0 t (j + 1) = (1 - settleProb β c0 t) * contProb β c0 (t + 1) j := by
  unfold contProb
  rw [Finset.prod_range_succ']
  simp only [add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show t + (i + 1) = t + 1 + i by ring]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `0 ≤ contProb t j ≤ βʲ`. -/
theorem contProb_bounds (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t j : ℕ) :
    0 ≤ contProb β c0 t j ∧ contProb β c0 t j ≤ β ^ j := by
  induction j with
  | zero => simp [contProb]
  | succ j ih =>
    have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 (t + j)
    have h : contProb β c0 t (j + 1) = contProb β c0 t j * (1 - settleProb β c0 (t + j)) := by
      unfold contProb
      rw [Finset.prod_range_succ]
    rw [h, pow_succ]
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · exact mul_le_mul ih.2 (by linarith) (by linarith) (pow_nonneg hβ0.le j)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the law of iterated expectations on the tree,
`E_t X_{t+j+1} = p_t X(settled at t+1) + (1 − p_t) E_{t+1} X_{t+j+1}`. -/
theorem condE_succ (t j : ℕ) (X : Option ℕ → ℝ) :
    condE β c0 t (j + 1) X = settleProb β c0 t * X (some (t + 1)) +
      (1 - settleProb β c0 t) * condE β c0 (t + 1) j X := by
  unfold condE
  rw [contProb_succ', Finset.sum_range_succ']
  simp only [add_zero, contProb, Finset.range_zero, Finset.prod_empty, one_mul]
  rw [mul_add, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range j,
      (∏ i ∈ Finset.range (i + 1), (1 - settleProb β c0 (t + i))) * settleProb β c0 (t + (i + 1)) *
        X (some (t + (i + 1) + 1)) = (1 - settleProb β c0 t) *
        ((∏ i_1 ∈ Finset.range i, (1 - settleProb β c0 (t + 1 + i_1))) *
          settleProb β c0 (t + 1 + i) * X (some (t + 1 + i + 1))) := by
    intro i _
    have h := contProb_succ' (β := β) (c0 := c0) t i
    unfold contProb at h
    rw [h, show t + (i + 1) = t + 1 + i by ring]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): conditional expectations are affine,
`E (a + b X) = a + b E X` (so the probabilities sum to one). -/
theorem condE_affine (t j : ℕ) (a b : ℝ) (X : Option ℕ → ℝ) :
    condE β c0 t j (fun x => a + b * X x) = a + b * condE β c0 t j X := by
  induction j generalizing t with
  | zero => simp [condE, contProb]
  | succ j ih =>
    rw [condE_succ, condE_succ, ih]
    ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probabilities at each horizon sum to one. -/
theorem condE_const (t j : ℕ) (a : ℝ) : condE β c0 t j (fun _ => a) = a := by
  have := condE_affine (β := β) (c0 := c0) t j a 0 (fun _ => 0)
  simpa using this

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): conditional expectations of nonnegative variables
are nonnegative. -/
theorem condE_nonneg (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t j : ℕ)
    {X : Option ℕ → ℝ} (hX : ∀ x, 0 ≤ X x) : 0 ≤ condE β c0 t j X := by
  induction j generalizing t with
  | zero => simpa [condE, contProb] using hX none
  | succ j ih =>
    rw [condE_succ]
    have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 t
    have := ih (t + 1)
    have := hX (some (t + 1))
    have : 0 ≤ settleProb β c0 t := by linarith
    have : 0 ≤ 1 - settleProb β c0 t := by linarith
    positivity

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): for `(1 − β) ∑_{j<T} βʲ + βᵀ = 1`. -/
theorem geom_identity (T : ℕ) : (1 - β) * ∑ j ∈ Finset.range T, β ^ j + β ^ T = 1 := by
  have := geom_sum_mul β T
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the finite-horizon identity
`S_n = ∑_{j<T} βʲ E_n P_{n+j} + βᵀ E_n S_{n+T}` at the continue node. -/
theorem value_finite (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) (n : ℕ) :
    value β c0 n = ∑ j ∈ Finset.range T, β ^ j * condE β c0 n j (price β c0 (n + j)) +
      β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := by
  induction T generalizing n with
  | zero => simp [condE, contProb, nodeValue]
  | succ T ih =>
    have hsum : ∑ j ∈ Finset.range T, β ^ (j + 1) * condE β c0 n (j + 1) (price β c0 (n + (j + 1)))
        = settleProb β c0 n * settlePrice β c0 (n + 1) * β * ∑ j ∈ Finset.range T, β ^ j +
          (1 - settleProb β c0 n) * β *
            ∑ j ∈ Finset.range T, β ^ j * condE β c0 (n + 1) j (price β c0 (n + 1 + j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [condE_succ, show n + (j + 1) = n + 1 + j by ring]
      simp only [price, Option.elim_some]
      ring
    have hrem : condE β c0 n (T + 1) (nodeValue β c0 (n + (T + 1))) =
        settleProb β c0 n * value β c0 (n + 1) +
          (1 - settleProb β c0 n) * condE β c0 (n + 1) T (nodeValue β c0 (n + 1 + T)) := by
      rw [condE_succ, show n + (T + 1) = n + 1 + T by ring]
      simp only [nodeValue, Option.elim_some]
    rw [Finset.sum_range_succ', hsum, hrem]
    have hih := ih (n + 1)
    have hg := geom_identity (β := β) T
    have hrec := value_rec (c0 := c0) hβ0 hβ1 n
    have h0 : condE β c0 n 0 (price β c0 (n + 0)) = contPrice β c0 n := by
      simp [condE, contProb, price]
    rw [h0, hrec]
    unfold settlePrice
    rw [pow_succ]
    linear_combination (1 - settleProb β c0 n) * β * hih -
      settleProb β c0 n * β * value β c0 (n + 1) * hg

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9, the transversality condition for the value):
`βᵀ E_n S_{n+T} → 0` at the continue node. -/
theorem remainder_tendsto (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    Tendsto (fun T => β ^ T * condE β c0 n T (nodeValue β c0 (n + T))) atTop (𝓝 0) := by
  set C := coefK β c0 + coefL β c0 with hC
  have hCpos : 0 < C := add_pos (coefK_pos hβ0 hβ1 hc1) (coefL_pos hβ0 hβ1 hc0)
  have hβ := hβ0.ne'
  have hbound : ∀ T, β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) ≤
      β ^ T * (C * β⁻¹ ^ n) + (T * β ^ T) * (C * β⁻¹ ^ (n + 1)) := by
    intro T
    have hsplit : condE β c0 n T (nodeValue β c0 (n + T)) = contProb β c0 n T * value β c0 (n + T)
        + ∑ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
          value β c0 (n + i + 1) := by
      simp [condE, nodeValue]
    have h1 : contProb β c0 n T * value β c0 (n + T) ≤ C * β⁻¹ ^ n := by
      have hq := contProb_bounds hβ0 hβ1 hc0 hc1 n T
      have hv := value_le hβ0 hβ1 hc0 (n + T)
      have hvp := value_pos hβ0 hβ1 hc0 hc1 (n + T)
      calc contProb β c0 n T * value β c0 (n + T) ≤ β ^ T * (C * β⁻¹ ^ (n + T)) :=
            mul_le_mul hq.2 hv hvp.le (pow_nonneg hβ0.le T)
        _ = C * β⁻¹ ^ n * (β ^ T * β⁻¹ ^ T) := by rw [pow_add]; ring
        _ = C * β⁻¹ ^ n := by rw [← mul_pow, mul_inv_cancel₀ hβ, one_pow, mul_one]
    have h2 : ∑ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
        value β c0 (n + i + 1) ≤ T * (C * β⁻¹ ^ (n + 1)) := by
      have : ∀ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
          value β c0 (n + i + 1) ≤ C * β⁻¹ ^ (n + 1) := by
        intro i _
        have hq := contProb_bounds hβ0 hβ1 hc0 hc1 n i
        have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 (n + i)
        have hv := value_le hβ0 hβ1 hc0 (n + i + 1)
        have hvp := value_pos hβ0 hβ1 hc0 hc1 (n + i + 1)
        calc contProb β c0 n i * settleProb β c0 (n + i) * value β c0 (n + i + 1)
            ≤ β ^ i * 1 * (C * β⁻¹ ^ (n + i + 1)) := by
              apply mul_le_mul (mul_le_mul hq.2 hp.2.le (by linarith) (pow_nonneg hβ0.le i)) hv
                hvp.le (by positivity)
          _ = C * β⁻¹ ^ (n + 1) * (β ^ i * β⁻¹ ^ i) := by
              rw [show n + i + 1 = n + 1 + i by ring, pow_add]
              ring
          _ = C * β⁻¹ ^ (n + 1) := by rw [← mul_pow, mul_inv_cancel₀ hβ, one_pow, mul_one]
      calc _ ≤ ∑ _i ∈ Finset.range T, C * β⁻¹ ^ (n + 1) := Finset.sum_le_sum this
        _ = T * (C * β⁻¹ ^ (n + 1)) := by simp
    rw [hsplit, mul_add]
    have hβT := pow_pos hβ0 T
    refine add_le_add (mul_le_mul_of_nonneg_left h1 hβT.le) ?_
    calc _ ≤ β ^ T * (T * (C * β⁻¹ ^ (n + 1))) := mul_le_mul_of_nonneg_left h2 hβT.le
      _ = _ := by ring
  have hnonneg : ∀ T, 0 ≤ β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := fun T =>
    mul_nonneg (pow_nonneg hβ0.le T) (condE_nonneg hβ0 hβ1 hc0 hc1 n T (fun x => by
      cases x with
      | none => exact (value_pos hβ0 hβ1 hc0 hc1 _).le
      | some k => exact (value_pos hβ0 hβ1 hc0 hc1 k).le))
  have hlim : Tendsto (fun T : ℕ => β ^ T * (C * β⁻¹ ^ n) + (T * β ^ T) * (C * β⁻¹ ^ (n + 1)))
      atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (C * β⁻¹ ^ n)
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).mul_const (C * β⁻¹ ^ (n + 1))
    simpa using h1.add h2
  exact squeeze_zero hnonneg hbound hlim

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): at the date-`n` continue node the expected present
value of the price level is a genuine convergent series, `∑ⱼ βʲ E_n P_{n+j} = S_n`. -/
theorem hasSum_value (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    HasSum (fun j => β ^ j * condE β c0 n j (price β c0 (n + j))) (value β c0 n) := by
  have hnonneg : ∀ j, 0 ≤ β ^ j * condE β c0 n j (price β c0 (n + j)) := fun j =>
    mul_nonneg (pow_nonneg hβ0.le j) (condE_nonneg hβ0 hβ1 hc0 hc1 n j (fun x => by
      cases x with
      | none => exact (by unfold price contPrice; simp only [Option.elim_none]; positivity)
      | some k =>
        simp only [price, Option.elim_some, settlePrice]
        exact mul_nonneg (by linarith) (value_pos hβ0 hβ1 hc0 hc1 k).le))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have heq : (fun T => ∑ j ∈ Finset.range T, β ^ j * condE β c0 n j (price β c0 (n + j))) =
      fun T => value β c0 n - β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := by
    funext T
    have := value_finite (c0 := c0) hβ0 hβ1 T n
    linarith
  rw [heq]
  simpa using (remainder_tendsto hβ0 hβ1 hc0 hc1 n).const_sub (value β c0 n)

/-- Cochrane (2023), eq. (9.9), p. 266, at the continue node (E9.9): real debt equals the expected
present value of surpluses, `b_{n−1} = ∑ⱼ βʲ E_n s_{n+j}`. -/
theorem valuation_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (n : ℕ) :
    HasSum (fun j => β ^ j * condE β c0 n j (surplus β c0 θ bbar (n + j)))
      (debt β c0 θ bbar n none) := by
  have hsurp : ∀ j, condE β c0 n j (surplus β c0 θ bbar (n + j)) =
      ((1 - β) * bbar - θ) + θ * condE β c0 n j (price β c0 (n + j)) := by
    intro j
    rw [← condE_affine]
    unfold surplus
    congr 1
    funext x
    ring
  have hg := hasSum_geometric_of_lt_one hβ0.le hβ1
  have h := (hg.mul_left ((1 - β) * bbar - θ)).add ((hasSum_value hβ0 hβ1 hc0 hc1 n).mul_left θ)
  have h1 : (1 - β) ≠ 0 := by linarith
  convert h using 1
  · funext j
    rw [hsurp]
    ring
  · simp only [debt, nodeValue, Option.elim_none]
    field_simp
    ring

/-- Cochrane (2023), eq. (9.9), p. 266, at a settled node (E9.9): the price stays at `H_k`
forever and real debt equals the present value of the constant surplus. -/
theorem valuation_settled (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (some k))
      (debt β c0 θ bbar n (some k)) := by
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left
    ((1 - β) * bbar + θ * (settlePrice β c0 k - 1))
  have h1 : (1 - β) ≠ 0 := by linarith
  convert hg using 1
  · funext j
    simp only [surplus, price, Option.elim_some]
    ring
  · simp only [debt, nodeValue, Option.elim_some, settlePrice]
    field_simp

/-- Cochrane (2023), eq. (9.8), p. 266, on the edges out of the continue node (E9.9): real debt is
predetermined — both children carry the same debt — and `b_{n−1} = s_n + β b_n` on both edges. -/
theorem flow_cont (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n : ℕ) :
    debt β c0 θ bbar (n + 1) none = debt β c0 θ bbar (n + 1) (some (n + 1)) ∧
      debt β c0 θ bbar n none = surplus β c0 θ bbar n none + β * debt β c0 θ bbar (n + 1) none :=
    by
  refine ⟨by simp [debt, nodeValue], ?_⟩
  have hrec := value_rec (c0 := c0) hβ0 hβ1 n
  have h1 : (1 - β) ≠ 0 := by linarith
  simp only [debt, surplus, nodeValue, price, Option.elim_none]
  rw [hrec]
  field_simp
  ring

/-- Cochrane (2023), eq. (9.8), p. 266, at a settled node (E9.9). -/
theorem flow_settled (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    debt β c0 θ bbar n (some k) =
      surplus β c0 θ bbar n (some k) + β * debt β c0 θ bbar (n + 1) (some k) := by
  have h1 : (1 - β) ≠ 0 := by linarith
  simp only [debt, surplus, nodeValue, price, Option.elim_some, settlePrice]
  field_simp
  ring

/-- Cochrane (2023), eq. (9.12), p. 267, at the continue node (E9.9):
`E_n (P_n / P_{n+1}) = 1 = P*_n/P*_{n+1}`, so
`1/(1 + i_n) = β E_n(P_n/P_{n+1}) = β E_n(P*_n/P*_{n+1})`. -/
theorem rate_target_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    condE β c0 n 1 (fun x => price β c0 n none / price β c0 (n + 1) x) = 1 := by
  have hm := martingale_inv hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  simp only [condE, contProb, Finset.range_one, Finset.prod_singleton, Finset.sum_singleton,
    Finset.range_zero, Finset.prod_empty, one_mul, add_zero, price, Option.elim_none,
    Option.elim_some]
  have : contPrice β c0 n * (settleProb β c0 n / settlePrice β c0 (n + 1) +
      (1 - settleProb β c0 n) / contPrice β c0 (n + 1)) = 1 := by
    rw [hm]
    field_simp
  linear_combination this

/-- Cochrane (2023), eq. (9.12), p. 267, at a settled node (E9.9): the price is constant. -/
theorem rate_target_settled (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (n k : ℕ) : price β c0 n (some k) / price β c0 (n + 1) (some k) = 1 := by
  simp only [price, Option.elim_some, settlePrice]
  have := value_pos hβ0 hβ1 hc0 hc1 k
  have h1 : 0 < 1 - β := by linarith
  exact div_self (by positivity)

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the transversality condition at the continue node,
`βᵀ E_n b_{n+T−1} → 0`. -/
theorem tvc_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (θ bbar : ℝ)
    (n : ℕ) :
    Tendsto (fun T => β ^ T * condE β c0 n T (debt β c0 θ bbar (n + T))) atTop (𝓝 0) := by
  have hd : ∀ T, condE β c0 n T (debt β c0 θ bbar (n + T)) =
      (bbar - θ * (1 / (1 - β))) + θ * condE β c0 n T (nodeValue β c0 (n + T)) := by
    intro T
    rw [← condE_affine]
    unfold debt
    congr 1
    funext x
    ring
  simp_rw [hd]
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (bbar - θ * (1 / (1 - β)))
  have h2 := (remainder_tendsto hβ0 hβ1 hc0 hc1 n).const_mul θ
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  refine this.congr fun T => ?_
  ring

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the transversality condition at a settled node. -/
theorem tvc_settled (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    Tendsto (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) atTop (𝓝 0) := by
  have : (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) =
      fun T => β ^ T * debt β c0 θ bbar 0 (some k) := by
    funext T
    simp [debt, nodeValue]
  rw [this]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (debt β c0 θ bbar 0 (some k))

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settled price levels are unbounded (so the
counterexample does not settle whether bounded price levels would restore uniqueness). -/
theorem settlePrice_unbounded (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    ¬ ∃ M, ∀ k, settlePrice β c0 k ≤ M := by
  rintro ⟨M, hM⟩
  have hK := coefK_pos hβ0 hβ1 hc1
  have hL := coefL_pos hβ0 hβ1 hc0
  have h1 : 0 < 1 - β := by linarith
  have hlim : Tendsto (fun k : ℕ => (1 - β) * coefK β c0 * β⁻¹ ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hβ0).mpr hβ1)).const_mul_atTop
      (mul_pos h1 hK)
  obtain ⟨k, hk⟩ := (hlim.eventually_gt_atTop M).exists
  have := hM k
  have hle : (1 - β) * coefK β c0 * β⁻¹ ^ k ≤ settlePrice β c0 k := by
    unfold settlePrice value
    have : 0 ≤ coefL β c0 * β ^ k := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): along the unsettled path the price level tends to
zero, so the counterexample's prices are neither bounded above nor bounded away from zero
(consistent with `fr_unique_bounded`). -/
theorem contPrice_tendsto_zero (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => contPrice β c0 n) atTop (𝓝 0) := by
  simpa [contPrice] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul c0

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability of never settling is zero,
`contProb t j → 0`. -/
theorem contProb_tendsto_zero (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (t : ℕ) : Tendsto (fun j => contProb β c0 t j) atTop (𝓝 0) :=
  squeeze_zero (fun j => (contProb_bounds hβ0 hβ1 hc0 hc1 t j).1)
    (fun j => (contProb_bounds hβ0 hβ1 hc0 hc1 t j).2)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1)

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the node visited at date `n` by the path that settles
at date `k`. -/
def pathNode (k n : ℕ) : Option ℕ := if n < k then none else some k

/-- Cochrane (2023), eq. (9.9), p. 266, ex post (E9.9): along every path that settles (at any date
`k`), real debt equals the realised discounted sum of surpluses,
`b_{n−1} = ∑ⱼ βʲ s_{n+j}`, the path satisfying (9.8) and the pathwise transversality condition. -/
theorem valuation_expost (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (k n : ℕ) :
    HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (pathNode k (n + j)))
      (debt β c0 θ bbar n (pathNode k n)) := by
  set b : ℕ → ℝ := fun m => debt β c0 θ bbar m (pathNode k m) with hb
  set sp : ℕ → ℝ := fun m => surplus β c0 θ bbar m (pathNode k m) with hsp
  have hflow : ∀ m, b m = sp m + β * b (m + 1) := by
    intro m
    simp only [hb, hsp, pathNode]
    by_cases h1 : m + 1 < k
    · have h0 : m < k := by omega
      simp only [h0, h1, ↓reduceIte]
      exact (flow_cont hβ0 hβ1 θ bbar m).2
    · by_cases h0 : m < k
      · have hk' : k = m + 1 := by omega
        simp only [h0, h1, ↓reduceIte]
        rw [hk', ← (flow_cont (c0 := c0) hβ0 hβ1 θ bbar m).1]
        exact (flow_cont hβ0 hβ1 θ bbar m).2
      · simp only [h0, h1, ↓reduceIte]
        exact flow_settled hβ1 θ bbar m k
  have htvc : Tendsto (fun T => β ^ T * b (n + T)) atTop (𝓝 0) := by
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (debt β c0 θ bbar 0 (some k))
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop k] with T hT
    have h0 : ¬ (n + T < k) := by omega
    simp only [hb, pathNode, h0, ↓reduceIte, debt, nodeValue, Option.elim_some]
  have hbound : ∀ m, |sp m| ≤ |(1 - β) * bbar| + |θ| * (c0 + settlePrice β c0 k + 1) := by
    intro m
    have hH : 0 < settlePrice β c0 k :=
      mul_pos (by linarith) (value_pos hβ0 hβ1 hc0 hc1 k)
    have hP : 0 ≤ price β c0 m (pathNode k m) ∧
        price β c0 m (pathNode k m) ≤ c0 + settlePrice β c0 k := by
      unfold pathNode
      split_ifs
      · simp only [price, Option.elim_none, contPrice]
        have h1 : β ^ m ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
        constructor
        · positivity
        · nlinarith
      · simp only [price, Option.elim_some]
        constructor <;> linarith
    simp only [hsp, surplus]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    constructor <;> linarith [hP.1, hP.2]
  exact hasSum_of_tvc hflow n htvc (summable_of_bounded hβ0.le hβ1 hbound n)

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)**, error E9.9): the claim "only the sequence
`P_t = P*_t` satisfies both (9.9) and (9.12)" is false under uncertainty. For every `0 < β < 1`,
every initial price level `0 < P_0 = c₀ < 1 = P*_0`, every rule coefficient `θ` and initial real
debt `b̄` (equal to the present value of `s₀ = (1 − β) b̄`), the settle-or-continue tree has
genuine probabilities, satisfies (9.12) at every node, (9.8) on every edge with predetermined real
debt, (9.9) at every node and the transversality condition at every node. -/
theorem sunspot_counterexample (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) :
    (∀ n, 0 < settleProb β c0 n ∧ settleProb β c0 n < 1) ∧
    (∀ n, condE β c0 n 1 (fun x => price β c0 n none / price β c0 (n + 1) x) = 1) ∧
    (∀ n k, price β c0 n (some k) / price β c0 (n + 1) (some k) = 1) ∧
    (∀ n, debt β c0 θ bbar (n + 1) none = debt β c0 θ bbar (n + 1) (some (n + 1)) ∧
      debt β c0 θ bbar n none = surplus β c0 θ bbar n none + β * debt β c0 θ bbar (n + 1) none) ∧
    (∀ n k, debt β c0 θ bbar n (some k) =
      surplus β c0 θ bbar n (some k) + β * debt β c0 θ bbar (n + 1) (some k)) ∧
    (∀ n, HasSum (fun j => β ^ j * condE β c0 n j (surplus β c0 θ bbar (n + j)))
      (debt β c0 θ bbar n none)) ∧
    (∀ n k, HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (some k))
      (debt β c0 θ bbar n (some k))) ∧
    (∀ n, Tendsto (fun T => β ^ T * condE β c0 n T (debt β c0 θ bbar (n + T))) atTop (𝓝 0)) ∧
    (∀ n k, Tendsto (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) atTop (𝓝 0)) ∧
    HasSum (fun j => β ^ j * ((1 - β) * bbar)) bbar ∧ debt β c0 θ bbar 0 none = bbar ∧
    price β c0 0 none = c0 ∧ price β c0 0 none < 1 := by
  refine ⟨fun n => ?_, rate_target_cont hβ0 hβ1 hc0 hc1, rate_target_settled hβ0 hβ1 hc0 hc1,
    flow_cont hβ0 hβ1 θ bbar, flow_settled hβ1 θ bbar, valuation_cont hβ0 hβ1 hc0 hc1 θ bbar,
    valuation_settled hβ0 hβ1 θ bbar, tvc_cont hβ0 hβ1 hc0 hc1 θ bbar, tvc_settled hβ0 hβ1 θ bbar,
    ?_, ?_, ?_, ?_⟩
  · have := settleProb_bounds hβ0 hβ1 hc0 hc1 n
    exact ⟨by linarith, this.2⟩
  · have h1 : (1 - β) ≠ 0 := by linarith
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * bbar)
    convert this using 1
    · funext j
      ring
    · field_simp
  · simp [debt, nodeValue, value_zero]
  · simp [price, contPrice]
  · simp [price, contPrice, hc1]

end Sunspot

/-! ### §9.3.3 A better fiscal rule: regular and emergency budgets -/

/-- Cochrane (2023), §9.3.3, p. 269: with the same-date rule `s_{r,t} = s_{0,t} + α_r b_{r,t}` and
`b_{r,t} = R (b_{r,t−1} − s_{r,t})`, the regular debt evolves as
`b_{r,t} = R/(1 + R α_r) · (b_{r,t−1} − s_{0,t})`. -/
theorem regular_solve {R αr br br' sr s0 : ℝ} (hR : 0 < R) (hα : 0 < αr)
    (hrec : br' = R * (br - sr)) (hrule : sr = s0 + αr * br') :
    br' = R / (1 + R * αr) * (br - s0) := by
  have h : 0 < 1 + R * αr := by positivity
  rw [hrule] at hrec
  rw [div_mul_eq_mul_div, eq_div_iff h.ne']
  linear_combination hrec

/-- Cochrane (2023), §9.3.3, p. 269 (checked correct, survey E9.6): with `α_r > 0` and bounded
`s₀`, the regular debt satisfies the transversality condition `βᵀ b_{r,T} → 0` automatically, for
every `α_r > 0`. -/
theorem regular_tvc {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αr) {br sr s0 : ℕ → ℝ}
    (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br (t + 1)) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set c := β / (β + αr) with hc
  have hcpos : 0 < c := div_pos hβ0 (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hstep : ∀ T, br (T + 1) = (br T - s0 T) / (β + αr) := by
    intro T
    have := regular_solve (inv_pos.mpr hβ0) hα (hrec T) (hrule T)
    rw [this]
    field_simp
  refine InflationTarget.tendsto_zero_of_contraction (c := c) (M := c * M)
    (by rw [abs_of_pos hcpos]; exact hc1) hβ0 hβ1 (mul_nonneg hcpos.le hM0) (fun T => ?_)
  rw [hstep T, hc, pow_succ]
  rw [show β ^ T * β * ((br T - s0 T) / (β + αr)) - β / (β + αr) * (β ^ T * br T) =
      -(β / (β + αr) * (β ^ T * s0 T)) by field_simp; ring, abs_neg, abs_mul, abs_mul,
    abs_of_pos (div_pos hβ0 (by linarith : 0 < β + αr)), abs_of_pos (pow_pos hβ0 T)]
  have hcT : 0 ≤ β / (β + αr) * β ^ T := by positivity
  calc β / (β + αr) * (β ^ T * |s0 T|) = (β / (β + αr) * β ^ T) * |s0 T| := by ring
    _ ≤ (β / (β + αr) * β ^ T) * M := mul_le_mul_of_nonneg_left (hM T) hcT
    _ = _ := by ring

/-- Cochrane (2023), §9.3.3, p. 269: "With `α_r > 0`, the regular surplus repays its debts
automatically, without an extra `a(β) = 0` assumption": `b_{r,t−1} = ∑ⱼ βʲ s_{r,t+j}`. -/
theorem regular_hasSum {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αr)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br (t + 1)) (t : ℕ) :
    HasSum (fun j => β ^ j * sr (t + j)) (br t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hflow : ∀ t, br t = sr t + β * br (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hx := regular_tvc hβ0 hβ1 hα hM hrec hrule
  have hβt : (β ^ t)⁻¹ * β ^ t = 1 := inv_mul_cancel₀ (pow_ne_zero t hβ0.ne')
  have htvc : Tendsto (fun T => β ^ T * br (t + T)) atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat t)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [Function.comp, pow_add, add_comm T t]
    rw [← mul_assoc, ← mul_assoc, hβt, one_mul]
  -- summability of the regular surplus
  set c := β / (β + αr) with hc
  have hcpos : 0 < c := div_pos hβ0 (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hstep : ∀ T, br (T + 1) = (br T - s0 T) / (β + αr) := by
    intro T
    have := regular_solve (inv_pos.mpr hβ0) hα (hrec T) (hrule T)
    rw [this]
    field_simp
  have hsx : Summable (fun T => β ^ T * br T) := by
    refine InflationTarget.summable_of_contraction (c := c) (M := c * M)
      (by rw [abs_of_pos hcpos]; exact hc1) hβ0 hβ1 (mul_nonneg hcpos.le hM0) (fun T => ?_)
    rw [hstep T, hc, pow_succ]
    rw [show β ^ T * β * ((br T - s0 T) / (β + αr)) - β / (β + αr) * (β ^ T * br T) =
        -(β / (β + αr) * (β ^ T * s0 T)) by field_simp; ring, abs_neg, abs_mul, abs_mul,
      abs_of_pos (div_pos hβ0 (by linarith : 0 < β + αr)), abs_of_pos (pow_pos hβ0 T)]
    have hcT : 0 ≤ β / (β + αr) * β ^ T := by positivity
    calc β / (β + αr) * (β ^ T * |s0 T|) = (β / (β + αr) * β ^ T) * |s0 T| := by ring
      _ ≤ (β / (β + αr) * β ^ T) * M := mul_le_mul_of_nonneg_left (hM T) hcT
      _ = _ := by ring
  have hsb : Summable (fun j => β ^ j * br (t + j + 1)) := by
    have h1 := ((summable_nat_add_iff (t + 1)).mpr hsx).mul_left (β ^ (t + 1))⁻¹
    refine h1.congr fun j => ?_
    rw [show j + (t + 1) = t + j + 1 by ring, show t + j + 1 = (t + 1) + j by ring,
      pow_add β (t + 1) j, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hβ0.ne'),
      one_mul]
  have hsum : Summable (fun j => β ^ j * sr (t + j)) := by
    have := (summable_of_bounded hβ0.le hβ1 hM t).add (hsb.mul_left αr)
    refine this.congr fun j => ?_
    rw [hrule (t + j)]
    ring
  exact hasSum_of_tvc hflow t htvc hsum

/-- Cochrane (2023), eq. (9.14), p. 269: the price-level-stabilisation budget,
`b_{p,t} = R (b_{p,t−1} − s_{p,t})`, `s_{p,t} = θ (P_t − P*_t)`, with its transversality condition,
obeys `b_{p,t−1} = ∑ⱼ βʲ s_{p,t+j} = θ ∑ⱼ βʲ (P_{t+j} − P*_{t+j})`. -/
theorem emergency_hasSum {β θ : ℝ} (hβ0 : 0 < β) {bp sp P Pstar : ℕ → ℝ}
    (hrec : ∀ t, bp (t + 1) = β⁻¹ * (bp t - sp t)) (hrule : ∀ t, sp t = θ * (P t - Pstar t))
    (t : ℕ) (htvc : Tendsto (fun T => β ^ T * bp (t + T)) atTop (𝓝 0))
    (hsum : Summable (fun j => β ^ j * (P (t + j) - Pstar (t + j)))) :
    HasSum (fun j => β ^ j * sp (t + j)) (bp t) ∧
      bp t = θ * ∑' j, β ^ j * (P (t + j) - Pstar (t + j)) := by
  have hflow : ∀ t, bp t = sp t + β * bp (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hs : Summable (fun j => β ^ j * sp (t + j)) := by
    refine (hsum.mul_left θ).congr fun j => ?_
    rw [hrule (t + j)]
    ring
  have h := hasSum_of_tvc hflow t htvc hs
  refine ⟨h, ?_⟩
  rw [← h.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [hrule (t + j)]
  ring

/-- Cochrane (2023), §9.3.3, p. 269 ("we can pair this fiscal policy with a debt target, here
`b_{p,t} = 0`"): with the emergency budget held at zero debt, `b_{p,t} = R(b_{p,t−1} − s_{p,t})`
forces
`s_{p,t} = 0`, hence `P_t = P*_t` (`θ ≠ 0`). -/
theorem emergency_debt_target {β θ : ℝ} (hθ : θ ≠ 0) {bp sp P Pstar : ℕ → ℝ}
    (hrec : ∀ t, bp (t + 1) = β⁻¹ * (bp t - sp t)) (hrule : ∀ t, sp t = θ * (P t - Pstar t))
    (hzero : ∀ t, bp t = 0) (hβ : β ≠ 0) (t : ℕ) : P t = Pstar t := by
  have h := hrec t
  rw [hzero, hzero, zero_sub, hrule t] at h
  have h2 : θ * (P t - Pstar t) = 0 := by
    have := (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero hβ)
    linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hθ
  · linarith

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant, survey E9.6): with the lagged rule
`s_{r,t} = s_{0,t} + α_r b_{r,t−1}` and `b_{r,t} = R(b_{r,t−1} − s_{r,t})`, `R = 1/β`, bounded `s₀`
and
`0 < α_r < 2`, the regular debt satisfies `βᵀ b_{r,T} → 0`. -/
theorem lagged_tvc {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αr) (hα2 : αr < 2)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br t) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine InflationTarget.tendsto_zero_of_contraction (c := 1 - αr) hc hβ0 hβ1 hM0 (fun T => ?_)
  rw [hrec T, hrule T, pow_succ]
  rw [show β ^ T * β * (β⁻¹ * (br T - (s0 T + αr * br T))) - (1 - αr) * (β ^ T * br T) =
      -(β ^ T * s0 T) by field_simp; ring, abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
  exact mul_le_mul_of_nonneg_left (hM T) (pow_pos hβ0 T).le

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant): with `s₀ = 0`, `βᵀ b_{r,T} = (1 − α_r)ᵀ
b_{r,0}`,
so for `b_{r,0} ≠ 0` the transversality condition holds iff `0 < α_r < 2` (unlike the book's
same-date rule, which works for every `α_r > 0`). -/
theorem lagged_tvc_iff {β αr : ℝ} (hβ0 : 0 < β) {br sr : ℕ → ℝ}
    (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t)) (hrule : ∀ t, sr t = 0 + αr * br t)
    (hb : br 0 ≠ 0) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) ↔ 0 < αr ∧ αr < 2 := by
  have hx : ∀ T, β ^ T * br T = (1 - αr) ^ T * br 0 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hrec T, hrule T, pow_succ, pow_succ,
        show (1 - αr) ^ T * (1 - αr) * br 0 = (1 - αr) * ((1 - αr) ^ T * br 0) by ring, ← ih]
      field_simp
      ring
  simp_rw [hx]
  constructor
  · intro h
    by_contra hα
    have hc : 1 ≤ |1 - αr| := by
      rcases not_and_or.mp hα with h1 | h1
      · rw [abs_of_nonneg (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
      · rw [abs_of_nonpos (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
    have hlow : ∀ T : ℕ, |br 0| ≤ |(1 - αr) ^ T * br 0| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hc)
    have habs := h.abs
    rw [abs_zero] at habs
    exact hb (abs_nonpos_iff.mp (ge_of_tendsto' habs hlow))
  · rintro ⟨h0, h2⟩
    have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).mul_const (br 0)

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant): with `0 < α_r < 2` and bounded `s₀` the
regular debt is repaid, `b_{r,t−1} = ∑ⱼ βʲ s_{r,t+j}`. -/
theorem lagged_hasSum {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αr) (hα2 : αr < 2)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br t) (t : ℕ) :
    HasSum (fun j => β ^ j * sr (t + j)) (br t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hflow : ∀ t, br t = sr t + β * br (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hstep : ∀ T, |β ^ (T + 1) * br (T + 1) - (1 - αr) * (β ^ T * br T)| ≤ β ^ T * M := by
    intro T
    rw [hrec T, hrule T, pow_succ]
    rw [show β ^ T * β * (β⁻¹ * (br T - (s0 T + αr * br T))) - (1 - αr) * (β ^ T * br T) =
        -(β ^ T * s0 T) by field_simp; ring, abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hM T) (pow_pos hβ0 T).le
  have hx := lagged_tvc hβ0 hβ1 hα0 hα2 hM hrec hrule
  have hsx := InflationTarget.summable_of_contraction (x := fun T => β ^ T * br T) hc hβ0 hβ1
    hM0 hstep
  have hβt : (β ^ t)⁻¹ * β ^ t = 1 := inv_mul_cancel₀ (pow_ne_zero t hβ0.ne')
  have htvc : Tendsto (fun T => β ^ T * br (t + T)) atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat t)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [Function.comp, pow_add, add_comm T t]
    rw [← mul_assoc, ← mul_assoc, hβt, one_mul]
  have hsb : Summable (fun j => β ^ j * br (t + j)) := by
    have h1 := ((summable_nat_add_iff t).mpr hsx).mul_left (β ^ t)⁻¹
    refine h1.congr fun j => ?_
    rw [show j + t = t + j by ring, pow_add β t j, ← mul_assoc, ← mul_assoc, hβt, one_mul]
  have hsum : Summable (fun j => β ^ j * sr (t + j)) := by
    have := (summable_of_bounded hβ0.le hβ1 hM t).add (hsb.mul_left αr)
    refine this.congr fun j => ?_
    rw [hrule (t + j)]
    ring
  exact hasSum_of_tvc hflow t htvc hsum

/-- Cochrane (2023), §9.3.3, pp. 268–269: the total surplus `s = s_r + s_p` and debt
`b = b_r + b_p` obey the usual flow and valuation `b_{t−1} = ∑ⱼ βʲ s_{t+j}`. -/
theorem total_hasSum {β : ℝ} {br bp sr sp : ℕ → ℝ} {t : ℕ}
    (hr : HasSum (fun j => β ^ j * sr (t + j)) (br t))
    (hp : HasSum (fun j => β ^ j * sp (t + j)) (bp t)) :
    HasSum (fun j => β ^ j * (sr (t + j) + sp (t + j))) (br t + bp t) := by
  have := hr.add hp
  refine this.congr_fun fun j => ?_
  ring

end Cochrane.AssetsRulesBalanceSheets.FiscalRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A fiscal rule with inflation and interest rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.4
"A fiscal rule with inflation and interest rates", eqs. (9.15)–(9.16), pp. 269–270.

Monetary policy follows `i_t = θ_{iπ} π_t + u_t` with `u_t = η u_{t−1} + ε_t`; with flexible prices
and a constant real rate `i_t = E_t π_{t+1}`, so (9.15) `E_t π_{t+1} = θ_{iπ} π_t + u_t`. Fiscal
policy sets `s_t = s_{0,t} + θ_{sπ} π_t`, and only indexed debt is outstanding, so
`b_{t−1} = E_t ∑ⱼ βʲ (s_{0,t+j} + θ_{sπ} π_{t+j})`.

Lean date `t` carries the real debt `b t` outstanding at the start of date `t` (book `b_{t−1}`).
Expected present values are sums of conditional expectations `∑ⱼ βʲ E_t x_{t+j}`.

## Main results

* `eq_9_15`; `E_pi_iterate`: `E_t π_{t+j} = θʲ π_t + fⱼ u_t` with `fⱼ = ∑_{k<j} θ^{j−1−k} ηᵏ`;
  `coefSeq_closed`: `(θ − η) fⱼ = θʲ − ηʲ`.
* `tsum_coefSeq`: `∑ⱼ βʲ fⱼ = β/((1 − βθ)(1 − βη))`, for `|βθ| < 1`, `|βη| < 1`.
* `eq_9_16`: the valuation equation becomes
  `b_{t−1} = θ_{sπ}/(1 − βθ_{iπ}) π_t + βθ_{sπ}/((1 − βθ_{iπ})(1 − βη)) u_t + E_t ∑ βʲ s_{0,t+j}`.
* `pi_determined`, `pi_eq`: with `θ_{sπ} ≠ 0` inflation is determined at each date;
  `pi_not_determined_without_surplus_response`: with `θ_{sπ} = 0` it is not;
  `rate_rule_essential`: without the interest-rate rule the valuation equation alone does not
  pin down the inflation path.
* `eq_theta_i_zero`: the `θ_{iπ} = 0` case, with the book's typo corrected (`b_t` → `b_{t−1}`,
  error E9.3).
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalTaylor

open Filter Topology

/-- Cochrane (2023), (9.16), p. 270: the coefficients `f₀ = 0`, `f_{j+1} = θ fⱼ + ηʲ`, so that
`fⱼ = ∑_{k<j} θ^{j−1−k} ηᵏ = (θʲ − ηʲ)/(θ − η)`. -/
def coefSeq (θ η : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => θ * coefSeq θ η j + η ^ j

/-- Cochrane (2023), (9.16), p. 270: `(θ − η) fⱼ = θʲ − ηʲ`. -/
theorem coefSeq_closed (θ η : ℝ) (j : ℕ) : (θ - η) * coefSeq θ η j = θ ^ j - η ^ j := by
  induction j with
  | zero => simp [coefSeq]
  | succ j ih =>
    simp only [coefSeq]
    rw [pow_succ, pow_succ]
    linear_combination θ * ih

/-- Cochrane (2023), (9.16), p. 270: with `m ≥ |θ|, |η|`, `m > 0`, `|fⱼ| m ≤ j mʲ`. -/
theorem abs_coefSeq_le {θ η m : ℝ} (hθ : |θ| ≤ m) (hη : |η| ≤ m) (hm : 0 < m) (j : ℕ) :
    |coefSeq θ η j| * m ≤ j * m ^ j := by
  induction j with
  | zero => simp [coefSeq]
  | succ j ih =>
    simp only [coefSeq]
    have h1 : |θ * coefSeq θ η j + η ^ j| ≤ m * |coefSeq θ η j| + m ^ j := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      · rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hη j
    calc |θ * coefSeq θ η j + η ^ j| * m ≤ (m * |coefSeq θ η j| + m ^ j) * m :=
          mul_le_mul_of_nonneg_right h1 hm.le
      _ = m * (|coefSeq θ η j| * m) + m ^ (j + 1) := by ring
      _ ≤ m * (j * m ^ j) + m ^ (j + 1) := by gcongr
      _ = ((j + 1 : ℕ) : ℝ) * m ^ (j + 1) := by push_cast; ring

/-- Cochrane (2023), (9.16), p. 270: for `0 ≤ β < 1`, `|βθ| < 1` and `|βη| < 1` the series
`∑ βʲ fⱼ` converges absolutely. -/
theorem summable_coefSeq {β θ η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θ| < 1)
    (hη : |β * η| < 1) : Summable (fun j => β ^ j * coefSeq θ η j) := by
  set m := max (max |θ| |η|) 1 with hm_def
  have hm : 0 < m := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hθm : |θ| ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hηm : |η| ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have hβm : β * m < 1 := by
    rw [hm_def, mul_max_of_nonneg _ _ hβ0, mul_max_of_nonneg _ _ hβ0, mul_one]
    rw [abs_mul, abs_of_nonneg hβ0] at hθ hη
    exact max_lt (max_lt hθ hη) hβ1
  have hβm0 : 0 ≤ β * m := mul_nonneg hβ0 hm.le
  have hg : Summable (fun j : ℕ => ((j : ℝ) ^ 1 * (β * m) ^ j) * m⁻¹) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := β * m)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hβm0]; exact hβm)).mul_right _
  refine Summable.of_norm_bounded hg (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), pow_one, mul_pow]
  have h := abs_coefSeq_le hθm hηm hm j
  have h2 : |coefSeq θ η j| ≤ j * m ^ j * m⁻¹ := by
    rw [le_mul_inv_iff₀ hm]
    exact h
  calc β ^ j * |coefSeq θ η j| ≤ β ^ j * (j * m ^ j * m⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 j)
    _ = _ := by ring

/-- Cochrane (2023), (9.16), p. 270 (the double geometric sum):
`∑ⱼ βʲ fⱼ = β/((1 − βθ)(1 − βη))`. -/
theorem tsum_coefSeq {β θ η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θ| < 1)
    (hη : |β * η| < 1) : ∑' j, β ^ j * coefSeq θ η j = β / ((1 - β * θ) * (1 - β * η)) := by
  have hs := summable_coefSeq hβ0 hβ1 hθ hη
  have hgη := summable_geometric_of_abs_lt_one hη
  have h1θ : 1 - β * θ ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  have hrec : ∑' j, β ^ j * coefSeq θ η j =
      β * θ * ∑' j, β ^ j * coefSeq θ η j + β * (1 - β * η)⁻¹ := by
    conv_lhs => rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, coefSeq, mul_zero, zero_add]
    have hsplit : (fun j => β ^ (j + 1) * (θ * coefSeq θ η j + η ^ j)) =
        fun j => β * θ * (β ^ j * coefSeq θ η j) + β * (β * η) ^ j := by
      funext j
      rw [mul_pow]
      ring
    rw [hsplit, (hs.mul_left (β * θ)).tsum_add (hgη.mul_left β), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_abs_lt_one hη]
  set F := ∑' j, β ^ j * coefSeq θ η j
  have h2 : F * (1 - β * θ) = β * (1 - β * η)⁻¹ := by linear_combination hrec
  rw [eq_div_iff (mul_ne_zero h1θ h1η)]
  calc F * ((1 - β * θ) * (1 - β * η)) = (F * (1 - β * θ)) * (1 - β * η) := by ring
    _ = β * (1 - β * η)⁻¹ * (1 - β * η) := by rw [h2]
    _ = β := by field_simp

/-- Cochrane (2023), (9.16), p. 270: `∑ⱼ (βθ)ʲ = 1/(1 − βθ)`. -/
theorem tsum_theta {β θ : ℝ} (hθ : |β * θ| < 1) :
    ∑' j, β ^ j * θ ^ j = 1 / (1 - β * θ) := by
  simp_rw [← mul_pow]
  rw [tsum_geometric_of_abs_lt_one hθ, one_div]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (9.15), p. 270: the rule `i_t = θ_{iπ} π_t + u_t` with `i_t = E_t π_{t+1}`
gives `E_t π_{t+1} = θ_{iπ} π_t + u_t`. -/
theorem eq_9_15 {θ : ℝ} {π u i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = θ • π t + u t)
    (hfisher : ∀ t, i t = 𝔼.E t (π (t + 1))) (t : ℕ) :
    𝔼.E t (π (t + 1)) = θ • π t + u t := by
  rw [← hfisher t, hrule t]

/-- Cochrane (2023), §9.3.4, p. 270 ("using (9.15) to eliminate expected future inflation"):
`E_t π_{t+j} = θʲ π_t + fⱼ u_t` for an AR(1) disturbance `u` with persistence `η`. -/
theorem E_pi_iterate {θ η : ℝ} {π u : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t) (t j : ℕ) :
    𝔼.E t (π (t + j)) = θ ^ j • π t + coefSeq θ η j • u t := by
  induction j with
  | zero => simp [coefSeq, hπ t]
  | succ j ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j), h915 (t + j), map_add, map_smul, ih,
      𝔼.ar1_iterate hu t j, smul_add, smul_smul, smul_smul, coefSeq, pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (9.16), p. 270: substituting (9.15) into the valuation equation
`b_{t−1} = ∑ⱼ βʲ E_t (s_{0,t+j} + θ_{sπ} π_{t+j})` gives
`b_{t−1} = θ_{sπ}/(1 − βθ_{iπ}) π_t + βθ_{sπ}/((1 − βθ_{iπ})(1 − βη)) u_t + ∑ⱼ βʲ E_t s_{0,t+j}`
(convergence requires `|βθ_{iπ}| < 1` and `|βη| < 1`). -/
theorem eq_9_16 {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) {π u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    b t ω = θs / (1 - β * θi) * π t ω +
      β * θs / ((1 - β * θi) * (1 - β * η)) * u t ω + ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
  have hterm : ∀ j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω =
      β ^ j * 𝔼.E t (s0 (t + j)) ω + (θs * π t ω) * (β ^ j * θi ^ j) +
        (θs * u t ω) * (β ^ j * coefSeq θi η j) := by
    intro j
    rw [map_add, map_smul, E_pi_iterate 𝔼 hπ hu h915 t j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgθ : Summable (fun j => β ^ j * θi ^ j) := by
    simp_rw [← mul_pow]
    exact summable_geometric_of_abs_lt_one hθ
  have hsf := summable_coefSeq hβ0 hβ1 hθ hη
  have h1θ : 1 - β * θi ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  rw [hval t ω, tsum_congr hterm, ((hs0 t ω).add (hgθ.mul_left _)).tsum_add (hsf.mul_left _),
    (hs0 t ω).tsum_add (hgθ.mul_left _), tsum_mul_left, tsum_mul_left, tsum_theta hθ,
    tsum_coefSeq hβ0 hβ1 hθ hη]
  field_simp
  ring

/-- Cochrane (2023), §9.3.4, p. 270 ("this equation now determines inflation at each date"):
with `θ_{sπ} ≠ 0`, inflation is given explicitly by the predetermined real debt, the monetary
disturbance and the present value of `s₀`. -/
theorem pi_eq {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) (hθs : θs ≠ 0) {π u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.IsAR1 η u) (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    π t ω = (1 - β * θi) / θs * (b t ω - ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω) -
      β / (1 - β * η) * u t ω := by
  have h := eq_9_16 𝔼 hβ0 hβ1 hθ hη hπ hu h915 hs0 hval t ω
  have h1θ : 1 - β * θi ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  rw [h]
  field_simp
  ring

/-- Cochrane (2023), §9.3.4, p. 270: with `θ_{sπ} ≠ 0` inflation is determined — two inflation
processes satisfying (9.15) and the valuation equation with the same debt, disturbance and `s₀`
coincide. -/
theorem pi_determined {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) (hθs : θs ≠ 0) {π π' u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hπ' : 𝔼.Adapted π') (hu : 𝔼.IsAR1 η u) (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (h915' : ∀ t, 𝔼.E t (π' (t + 1)) = θi • π' t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω)
    (hval' : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π' (t + j)) ω) : π = π' := by
  funext t ω
  rw [pi_eq 𝔼 hβ0 hβ1 hθ hη hθs hπ hu h915 hs0 hval t ω,
    pi_eq 𝔼 hβ0 hβ1 hθ hη hθs hπ' hu h915' hs0 hval' t ω]

/-- Cochrane (2023), §9.3.4, p. 270 ("without this response, `π_t` drops from the equation"):
with `θ_{sπ} = 0`, under perfect foresight with `u = 0`, `s₀ = 0`, `b = 0`, both `π ≡ 0` and
`π_t = θ_{iπ}ᵗ` satisfy (9.15) and the valuation equation. -/
theorem pi_not_determined_without_surplus_response {β θi : ℝ} :
    ∃ π π' : ℕ → Unit → ℝ,
      (∀ t, perfectForesight.E t (π (t + 1)) = θi • π t + 0) ∧
      (∀ t, perfectForesight.E t (π' (t + 1)) = θi • π' t + 0) ∧
      (∀ t ω, (0 : ℝ) = ∑' j, β ^ j * perfectForesight.E t (0 + (0 : ℝ) • π (t + j)) ω) ∧
      (∀ t ω, (0 : ℝ) = ∑' j, β ^ j * perfectForesight.E t (0 + (0 : ℝ) • π' (t + j)) ω) ∧
      π ≠ π' := by
  refine ⟨fun _ _ => 0, fun t _ => θi ^ t, fun t => ?_, fun t => ?_, fun t ω => ?_, fun t ω => ?_,
    ?_⟩
  · funext ω
    simp [perfectForesight]
  · funext ω
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero]
    ring
  · simp [perfectForesight]
  · simp [perfectForesight]
  · intro h
    have := congrFun (congrFun h 0) ()
    simp at this

/-- Cochrane (2023), §9.3.4, p. 270 ("an interest-rate target is essential"): without the
interest-rate rule (9.15), the valuation equation with `θ_{sπ} ≠ 0` only pins down the
`β`-weighted sum of inflation. Under perfect foresight with `s₀ = 0` and `b_{−1} = 0`, both
`π ≡ 0` and `π = (β/2, −1/2, 0, …)` satisfy the date-0 valuation, with different `π_0`. -/
theorem rate_rule_essential {β : ℝ} (hβ : β ≠ 0) (θs : ℝ) :
    ∃ π π' : ℕ → ℝ, HasSum (fun j => β ^ j * (0 + θs * π j)) 0 ∧
      HasSum (fun j => β ^ j * (0 + θs * π' j)) 0 ∧ π 0 ≠ π' 0 := by
  refine ⟨fun _ => 0, FiscalRules.hyperplaneShift β, by simp, ?_, ?_⟩
  · have := (FiscalRules.hasSum_hyperplaneShift β).mul_left θs
    rw [mul_zero] at this
    refine this.congr_fun fun j => ?_
    ring
  · simp only [FiscalRules.hyperplaneShift, ↓reduceIte]
    intro h
    exact hβ (by linarith)

/-- Cochrane (2023), §9.3.4, p. 270, the `θ_{iπ} = 0` case (typo corrected, error E9.3: the book
writes `b_t` on the left, it is `b_{t−1}`, Lean `b t`): with `i_t = u_t`,
`b_{t−1} = θ_{sπ} π_t + βθ_{sπ}/(1 − βη) i_t + ∑ⱼ βʲ E_t s_{0,t+j}`. -/
theorem eq_theta_i_zero {β θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη : |β * η| < 1)
    {π u i s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (hrule : ∀ t, i t = (0 : ℝ) • π t + u t) (hfisher : ∀ t, i t = 𝔼.E t (π (t + 1)))
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    b t ω = θs * π t ω + β * θs / (1 - β * η) * i t ω + ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
  have h915 := eq_9_15 𝔼 hrule hfisher
  have h := eq_9_16 𝔼 hβ0 hβ1 (by simp) hη hπ hu h915 hs0 hval t ω
  have hi : i t ω = u t ω := by
    rw [hrule t]
    simp
  rw [h, hi]
  simp

end Cochrane.AssetsRulesBalanceSheets.FiscalTaylor

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal rules with nominal debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.5
"Fiscal rules with nominal debt", p. 271.

With real debt `b_{T−1}` and nominal debt `B_{T−1} > 0` outstanding, the one-period valuation
equation is `b_{T−1} + B_{T−1}/P_T = s(P_T)`.

## Main results

* `price_unique`: if `s` is nondecreasing on positive prices (in particular if `s` is constant —
  "a surplus rule is not strictly needed"), there is at most one positive price level;
  `multiplicity_needs_decreasing`: two distinct solutions force `s` to fall between them;
  `multiplicity_example`: with `s(P) = b + B/P` (strictly decreasing) every price level solves.
* `hasDerivAt_value`, `elasticity_value`: the elasticity of the debt value with respect to `P`
  is minus the nominal share; `ten_percent_rise`, `ten_percent_fall`: with a nominal share of
  10%, a 10% rise (fall) in `P` changes the value of the debt by `1/110 ≈ 0.91%`
  (`1/90 ≈ 1.11%`) — the book's "1%" is the first-order (elasticity) statement.
* `shock_decomposition`, `devaluationShare_strictAnti`: a surplus shock `ε` is met partly by
  inflating away nominal debt and partly by the induced fiscal tightening `γ (P₁ − P₀)`; the share
  met by devaluation, `k/(γ + k)`, falls as the surplus response `γ = s'(P)` rises.
-/

namespace Cochrane.AssetsRulesBalanceSheets.MixedDebtRules

/-- Cochrane (2023), §9.3.5, p. 271: with `B > 0` the real value `b + B/P` of the debt is strictly
decreasing in the price level. -/
theorem value_strictAntiOn {b B : ℝ} (hB : 0 < B) :
    StrictAntiOn (fun P => b + B / P) (Set.Ioi 0) := by
  intro P₁ h₁ P₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  simp only [add_lt_add_iff_left]
  exact div_lt_div_of_pos_left hB h₁ hlt

/-- Cochrane (2023), §9.3.5, p. 271 ("ruling out the passive possibility, which requires
`s'(P) < 0`, the price level is determined"): with nominal debt `B > 0` and a surplus that does
not fall with the price level, `b + B/P = s(P)` has at most one positive solution. -/
theorem price_unique {b B : ℝ} (hB : 0 < B) {s : ℝ → ℝ} (hs : MonotoneOn s (Set.Ioi 0))
    {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) (e₁ : b + B / P₁ = s P₁) (e₂ : b + B / P₂ = s P₂) :
    P₁ = P₂ := by
  have hf : StrictMonoOn (fun P => s P - B / P) (Set.Ioi 0) := fun P₁ h₁ P₂ h₂ hlt => by
    have h1 := value_strictAntiOn (b := 0) hB h₁ h₂ hlt
    have h2 := hs h₁ h₂ hlt.le
    simp only [zero_add] at h1
    change s P₁ - B / P₁ < s P₂ - B / P₂
    linarith
  exact PresentValue.price_unique_of_strictMonoOn (b := b) hf h₁ h₂
    (by linarith) (by linarith)

/-- Cochrane (2023), §9.3.5, p. 271 ("with any nominal debt, a surplus rule is not strictly needed
for determinacy"): with a constant surplus the positive price level is unique. -/
theorem price_unique_const {b B s : ℝ} (hB : 0 < B) {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂)
    (e₁ : b + B / P₁ = s) (e₂ : b + B / P₂ = s) : P₁ = P₂ :=
  price_unique (s := fun _ => s) hB (fun _ _ _ _ _ => le_rfl) h₁ h₂ e₁ e₂

/-- Cochrane (2023), §9.3.5, p. 271: multiplicity requires `s` to fall with the price level — if
`P₁ < P₂` both solve the valuation equation, then `s(P₂) < s(P₁)`. -/
theorem multiplicity_needs_decreasing {b B : ℝ} (hB : 0 < B) {s : ℝ → ℝ} {P₁ P₂ : ℝ}
    (h₁ : 0 < P₁) (hlt : P₁ < P₂) (e₁ : b + B / P₁ = s P₁) (e₂ : b + B / P₂ = s P₂) :
    s P₂ < s P₁ := by
  have h := value_strictAntiOn (b := b) hB (Set.mem_Ioi.mpr h₁)
    (Set.mem_Ioi.mpr (h₁.trans hlt)) hlt
  simp only at h
  linarith

/-- Cochrane (2023), §9.3.5, p. 271: the passive possibility does occur when `s' < 0` — with
`s(P) = b + B/P`, which is strictly decreasing, every positive price level solves. -/
theorem multiplicity_example {b B : ℝ} (hB : 0 < B) :
    StrictAntiOn (fun P => b + B / P) (Set.Ioi 0) ∧
      ∀ P, 0 < P → b + B / P = (fun P => b + B / P) P :=
  ⟨value_strictAntiOn hB, fun _ _ => rfl⟩

/-- Cochrane (2023), §9.3.5, p. 271: the derivative of the debt value, `d(b + B/P)/dP = −B/P²`. -/
theorem hasDerivAt_value (b B : ℝ) {P : ℝ} (hP : P ≠ 0) :
    HasDerivAt (fun P => b + B / P) (-(B / P ^ 2)) P := by
  have h := HasDerivAt.const_add b (HasDerivAt.const_mul B (hasDerivAt_inv hP))
  have e : (fun P : ℝ => b + B / P) = fun y => b + B * y⁻¹ := by
    funext y
    rw [div_eq_mul_inv]
  rw [e]
  exact HasDerivAt.congr_deriv h (by field_simp)

/-- Cochrane (2023), §9.3.5, p. 271: the elasticity of the debt value with respect to the price
level is minus the nominal share, `P V'(P)/V(P) = −(B/P)/(b + B/P)`. -/
theorem elasticity_value (b B : ℝ) {P : ℝ} (hP : P ≠ 0) :
    P * (-(B / P ^ 2)) / (b + B / P) = -((B / P) / (b + B / P)) := by
  rw [show P * (-(B / P ^ 2)) = -(B / P) by field_simp]
  ring

/-- Cochrane (2023), §9.3.5, p. 271 ("if nominal debt is only 10% of all debt, then a 10% change
in the price level only affects the value of government bonds by 1%"): with nominal share
`1/10`, a 10% rise in `P` lowers the debt value by exactly `1/110` of its value. -/
theorem ten_percent_rise {b B P : ℝ} (hP : 0 < P) (hV : b + B / P ≠ 0)
    (hshare : B / P = (1 / 10) * (b + B / P)) :
    ((b + B / P) - (b + B / (11 / 10 * P))) / (b + B / P) = 1 / 110 := by
  have h1 : B / (11 / 10 * P) = (10 / 11) * (B / P) := by
    field_simp
  rw [h1, show b + B / P - (b + 10 / 11 * (B / P)) = (1 / 11) * (B / P) by ring, div_eq_iff hV]
  linarith

/-- Cochrane (2023), §9.3.5, p. 271: with nominal share `1/10`, a 10% fall in `P` raises the debt
value by exactly `1/90` of its value. -/
theorem ten_percent_fall {b B P : ℝ} (hP : 0 < P) (hV : b + B / P ≠ 0)
    (hshare : B / P = (1 / 10) * (b + B / P)) :
    ((b + B / (9 / 10 * P)) - (b + B / P)) / (b + B / P) = 1 / 90 := by
  have h1 : B / (9 / 10 * P) = (10 / 9) * (B / P) := by
    field_simp
  rw [h1, show b + 10 / 9 * (B / P) - (b + B / P) = (1 / 9) * (B / P) by ring, div_eq_iff hV]
  linarith

/-- Cochrane (2023), §9.3.5, p. 271 ("the stronger `s'(P)`, the more that inflationary fiscal
shocks are met by an induced fiscal tightening, and the less they are met by inflating away
outstanding nominal government debt"): with the rule `s(P) = s₀ + γ (P − P*)`, a surplus shock `ε`
moves the price level from `P₀` to `P₁` with `(P₁ − P₀)(γ + B/(P₀P₁)) = −ε`; the shock is split into
debt devaluation `B/P₀ − B/P₁` and fiscal tightening `γ (P₁ − P₀)`. -/
theorem shock_decomposition {b B s0 γ Pstar ε P₀ P₁ : ℝ} (h₀ : 0 < P₀) (h₁ : 0 < P₁)
    (e₀ : b + B / P₀ = s0 + γ * (P₀ - Pstar)) (e₁ : b + B / P₁ = s0 + ε + γ * (P₁ - Pstar)) :
    (P₁ - P₀) * (γ + B / (P₀ * P₁)) = -ε ∧
      ε = (B / P₁ - B / P₀) - γ * (P₁ - P₀) ∧ B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
  have hdev : B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
    field_simp
  refine ⟨?_, by linarith, hdev⟩
  have : ε = (B / P₁ - B / P₀) - γ * (P₁ - P₀) := by linarith
  rw [this]
  linear_combination -hdev

/-- Cochrane (2023), §9.3.5, p. 271: the share of a fiscal shock met by devaluing nominal debt,
`k/(γ + k)` with `k = B/(P₀P₁) > 0`. -/
noncomputable def devaluationShare (k γ : ℝ) : ℝ := k / (γ + k)

/-- Cochrane (2023), §9.3.5, p. 271: the devaluation share falls strictly as the surplus response
`γ ≥ 0` rises. -/
theorem devaluationShare_strictAnti {k : ℝ} (hk : 0 < k) :
    StrictAntiOn (devaluationShare k) (Set.Ici 0) := by
  intro γ₁ h₁ γ₂ h₂ hlt
  simp only [Set.mem_Ici] at h₁ h₂
  unfold devaluationShare
  exact div_lt_div_of_pos_left hk (by linarith) (by linarith)

/-- Cochrane (2023), §9.3.5, p. 271: with the decomposition of `shock_decomposition`, the debt
devaluation absorbs exactly the share `k/(γ + k)` of the shock and fiscal tightening the rest. -/
theorem devaluation_part {B γ ε P₀ P₁ : ℝ} (h₀ : 0 < P₀) (h₁ : 0 < P₁) (hγ : 0 ≤ γ) (hB : 0 < B)
    (hsplit : (P₁ - P₀) * (γ + B / (P₀ * P₁)) = -ε) :
    B / P₀ - B / P₁ = -(devaluationShare (B / (P₀ * P₁)) γ * ε) ∧
      γ * (P₁ - P₀) = -((1 - devaluationShare (B / (P₀ * P₁)) γ) * ε) := by
  have hk : 0 < B / (P₀ * P₁) := by positivity
  have hne : γ + B / (P₀ * P₁) ≠ 0 := by linarith
  have hP : P₁ - P₀ = -ε / (γ + B / (P₀ * P₁)) := by
    rw [eq_div_iff hne]
    linarith
  unfold devaluationShare
  constructor
  · have hdev : B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
      field_simp
    rw [hdev, hP]
    field_simp
  · rw [hP]
    field_simp
    ring

end Cochrane.AssetsRulesBalanceSheets.MixedDebtRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Targeting the spread

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.4
"Targeting the spread" and §9.4.1 "Fiscal theory with a spread target", eqs. (9.17)–(9.26),
pp. 271–278.

## Main results

* §9.4: `taylor_spread_equiv` (a Taylor rule with a real rate that tracks it is a spread target,
  p. 273); `swap_rate`: the zero-cost inflation-swap rate is `β/Q_t`, the expected gross inflation
  under the nominal risk-neutral weights `m = β P_t/P_{t+1}` (p. 273).
* The simple model (9.17)–(9.20) (`SimpleModel`): `eq_9_21_mul`, `eq_9_21` (valid for every
  `θ ∈ [0, 1]`, including the spread target `θ = 1`), `lam_bounds`;
`indeterminate_without_valuation`:
  without (9.22) any initial inflation gives a bounded equilibrium.
* **Theorem ST** (`unexpected_inflation_iff`, `eq_9_23`): given (9.17)–(9.21), the linearised
  valuation equation (9.22) holds iff
  `ΔE_{t+1} π_{t+1} = −((1 − ρ)(1 − θ) + σκ)/((1 − ρ)(1 − θ) + σκ + ρ) · ε^{Σs}_{t+1}`;
  `exists_solution`, `solution_bounded`, `unique_solution`: existence, boundedness and uniqueness
  (given `π_0`) of the solution of (9.17)–(9.22), for every `θ ∈ [0, 1]`.
* `theta_zero`, `theta_one`, `tendsto_coef_theta_one`: the cases `θ = 0`, `θ = 1` (proved directly;
  the footnote's formula `r_t = (π^{e*} − E_t π_{t+1})/(1 − θ)` is undefined at `θ = 1`, error E9.5,
  see `footnote_r` and `r_eq`) and the limit `θ → 1`; `theta_one_paths`: the paths of `x`, `r`, `i`
  on p. 277.
* The full new-Keynesian model (9.24)–(9.25) with a spread target (`FullNK`): `x_formula`
  ((9.26) first line), `r_formula` (**(9.26) corrected**, error E9.4),
  `printed_9_26_fails_perfectForesight` (the printed `u_π` terms lack `1/κ`) and
  `printed_9_26_fails_coin` (the printed sign of `ΔE_t π_t` is wrong).
* `holden_unique`: the rule `i_t = r_t + π* + φ (π_t − π*)` with `|φ| > 1` has the unique bounded
  solution `π ≡ π*` (Holden 2020, p. 278).
-/

namespace Cochrane.AssetsRulesBalanceSheets.SpreadTarget

open Filter Topology

/-! ### §9.4: spreads, Taylor rules and inflation swaps -/

/-- Cochrane (2023), §9.4, p. 273: if the central bank follows `i = (r̄ + π*) + θ_π π + θ_x x` and
the
real rate tracks the same variables, `r = r̄ + θ_π π + θ_x x`, the spread `i − r` equals `π*`: the
Taylor rule is a spread target. -/
theorem taylor_spread_equiv {i r rbar πs θπ θx π x : ℝ} (hi : i = (rbar + πs) + θπ * π + θx * x)
    (hr : r = rbar + θπ * π + θx * x) : i - r = πs := by
  rw [hi, hr]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.4, p. 273 (inflation swaps): with a constant real rate, the dollar price of
a claim to `Π_{t+1} = P_{t+1}/P_t` dollars is `β`, the nominal bond costs `Q_t = β
E_t(P_t/P_{t+1})`,
so the swap paying `Π_{t+1} − Π*` costs `β − Π* Q_t`; it is zero iff `Π* = β/Q_t`, which equals the
expectation of `Π_{t+1}` under the nominal risk-neutral weights `m = β P_t/P_{t+1}`. -/
theorem swap_rate {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (ω : Ω)
    (hQ : 0 < β * 𝔼.E t (P t / P (t + 1)) ω) (Pis : ℝ) :
    (β - Pis * (β * 𝔼.E t (P t / P (t + 1)) ω) = 0 ↔
        Pis = β / (β * 𝔼.E t (P t / P (t + 1)) ω)) ∧
      β / (β * 𝔼.E t (P t / P (t + 1)) ω) =
        𝔼.E t ((β • (P t / P (t + 1))) * (P (t + 1) / P t)) ω /
          𝔼.E t (β • (P t / P (t + 1))) ω := by
  have hmPi : (β • (P t / P (t + 1))) * (P (t + 1) / P t) = fun _ => β := by
    funext ω'
    simp only [Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
    field_simp [(hP t ω').ne', (hP (t + 1) ω').ne']
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [eq_div_iff hQ.ne']
    linarith
  · rw [h, div_mul_cancel₀ _ hQ.ne', sub_self]
  · rw [hmPi, 𝔼.const, map_smul]
    rfl

/-! ### The simple model (9.17)–(9.20) -/

variable (σ κ θ πs : ℝ) (π x i r : ℕ → Ω → ℝ)

/-- Cochrane (2023), eqs. (9.17)–(9.20), p. 275: the static IS curve `x_t = −σ(i_t − E_t π_{t+1})`,
the Phillips curve `π_t = E_t π_{t+1} + κ x_t`, the real rate `r_t = i_t − E_t π_{t+1}`, and the
rule
`i_t = θ r_t + π^{e*}` (the spread target is `θ = 1`), with inflation adapted. -/
structure SimpleModel where
  adapted_pi : 𝔼.Adapted π
  is_9_17 : ∀ t, x t = (-σ) • (i t - 𝔼.E t (π (t + 1)))
  is_9_18 : ∀ t, π t = 𝔼.E t (π (t + 1)) + κ • x t
  is_9_19 : ∀ t, r t = i t - 𝔼.E t (π (t + 1))
  is_9_20 : ∀ t, i t = θ • r t + fun _ => πs

variable {𝔼 σ κ θ πs π x i r}

/-- Cochrane (2023), §9.4.1, p. 275 (footnote 1): the IS and Phillips curves give
`σκ r_t = E_t π_{t+1} − π_t` for every `θ` (this, not the footnote's division by `1 − θ`, pins
`r`). -/
theorem r_eq (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    (σ * κ) • r t = 𝔼.E t (π (t + 1)) - π t := by
  have h17 := hM.is_9_17 t
  have h18 := hM.is_9_18 t
  have h19 := hM.is_9_19 t
  funext ω
  have a := congrFun h17 ω
  have b := congrFun h18 ω
  have c := congrFun h19 ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at a b c ⊢
  rw [b, a, ← c]
  ring

/-- Cochrane (2023), eq. (9.21), p. 275, multiplied out:
`(1 − θ + σκ)(E_t π_{t+1} − π^{e*}) = (1 − θ)(π_t − π^{e*})`, valid for every `θ`. -/
theorem eq_9_21_mul (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    (1 - θ + σ * κ) • (𝔼.E t (π (t + 1)) - fun _ => πs) = (1 - θ) • (π t - fun _ => πs) := by
  have hr := r_eq hM t
  have h19 := hM.is_9_19 t
  have h20 := hM.is_9_20 t
  funext ω
  have a := congrFun hr ω
  have c := congrFun h19 ω
  have d := congrFun h20 ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at a c d ⊢
  have e : (1 - θ) * r t ω = πs - 𝔼.E t (π (t + 1)) ω := by linarith
  linear_combination (σ * κ) * e - (1 - θ) * a

/-- Cochrane (2023), eq. (9.21), p. 275: the persistence `λ = (1 − θ)/(1 − θ + σκ)`. -/
noncomputable def lam (σ κ θ : ℝ) : ℝ := (1 - θ) / (1 - θ + σ * κ)

/-- Cochrane (2023), eq. (9.21), p. 275: `E_t(π_{t+1} − π^{e*}) = (1 − θ)/(1 − θ + σκ) · (π_t −
π^{e*})`. -/
theorem eq_9_21 (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    𝔼.E t (π (t + 1)) - (fun _ => πs) = lam σ κ θ • (π t - fun _ => πs) := by
  have h := eq_9_21_mul hM t
  funext ω
  have a := congrFun h ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a ⊢
  unfold lam
  field_simp
  linarith

/-- Cochrane (2023), §9.4.1, p. 275 ("when the coefficient on the right-hand side is less than
one"): for `θ ∈ [0, 1]` and `σκ > 0`, `0 ≤ λ < 1`. -/
theorem lam_bounds {σ κ θ : ℝ} (hθ1 : θ ≤ 1) (hσκ : 0 < σ * κ) :
    0 ≤ lam σ κ θ ∧ lam σ κ θ < 1 := by
  unfold lam
  have h : 0 < 1 - θ + σ * κ := by linarith
  exact ⟨div_nonneg (by linarith) h.le, (div_lt_one h).mpr (by linarith)⟩

/-- Cochrane (2023), §9.4.1, p. 275 (footnote 1): `λ − 1 = −σκ/(1 − θ + σκ)`. -/
theorem lam_sub_one {σ κ θ : ℝ} (hD : 1 - θ + σ * κ ≠ 0) :
    lam σ κ θ - 1 = -(σ * κ) / (1 - θ + σ * κ) := by
  unfold lam
  field_simp
  ring

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): iterating (9.21),
`E_s π_{s+j} − π^{e*} = λʲ (π_s − π^{e*})`. -/
theorem E_pi_iter (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (s j : ℕ) :
    𝔼.E s (π (s + j)) - (fun _ => πs) = lam σ κ θ ^ j • (π s - fun _ => πs) := by
  induction j with
  | zero => simp [hM.adapted_pi s]
  | succ j ih =>
    have h := congrArg (𝔼.E s) (eq_9_21 hD hM (s + j))
    rw [map_sub, map_smul, map_sub, 𝔼.tower (Nat.le_add_right s j), 𝔼.const] at h
    have ih' : 𝔼.E s (π (s + j)) = (fun _ => πs) + lam σ κ θ ^ j • (π s - fun _ => πs) := by
      rw [← ih]
      abel
    rw [ih'] at h
    rw [← add_assoc, h, pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §9.4.1, p. 275 ("inflation is stable but indeterminate, as `ΔE_{t+1} π_{t+1}`
can be anything"): without the valuation equation (9.22), under perfect foresight, every initial
inflation `π_0 = π^{e*} + a` starts a bounded equilibrium of (9.17)–(9.20) (`θ ∈ [0, 1]`,
`σκ > 0`). -/
theorem indeterminate_without_valuation {σ κ θ πs : ℝ} (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (a : ℝ) :
    ∃ π x i r : ℕ → Unit → ℝ, SimpleModel perfectForesight σ κ θ πs π x i r ∧ BoundedProc π ∧
      π 0 () = πs + a := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul hσκ0
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hσκ0
  have hl := lam_bounds hθ1 hσκ
  set l := lam σ κ θ with hl_def
  set π : ℕ → Unit → ℝ := fun t _ => πs + l ^ t * a with hπ
  set r : ℕ → Unit → ℝ := fun t _ => (π (t + 1) () - π t ()) / (σ * κ) with hr
  refine ⟨π, fun t _ => -σ * r t (), fun t _ => r t () + π (t + 1) (), r, ⟨fun _ => rfl,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, ⟨|πs| + |a|, fun t ω => ?_⟩, by simp [hπ]⟩
  · funext ω
    change -σ * r t () = -σ * (r t () + π (t + 1) () - π (t + 1) ())
    ring
  · funext ω
    change π t () = π (t + 1) () + κ * (-σ * r t ())
    simp only [hr]
    field_simp
    ring
  · funext ω
    change r t () = r t () + π (t + 1) () - π (t + 1) ()
    ring
  · funext ω
    change r t () + π (t + 1) () = θ * r t () + πs
    have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
    rw [← hl_def] at hls
    simp only [hr, hπ]
    have e : (πs + l ^ (t + 1) * a - (πs + l ^ t * a)) / (σ * κ) =
        l ^ t * a * ((l - 1) / (σ * κ)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e, show (l - 1) / (σ * κ) = -1 / (1 - θ + σ * κ) by
      rw [hls]
      field_simp, pow_succ, hl_def]
    unfold lam
    field_simp
    ring
  · simp only [hπ]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg hl.1]
    exact mul_le_of_le_one_left (abs_nonneg a) (pow_le_one₀ hl.1 hl.2.le)

/-! ### The valuation equation (9.22) and Theorem ST -/

/-- Cochrane (2023), eq. (9.22), p. 275: the innovation operator
`ΔE_{t+1} y = E_{t+1} y − E_t y`. -/
def innov (𝔼 : ExpectationSystem Ω) (t : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) y - 𝔼.E t y

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): `ΔE_{t+1} π_{t+1+j} = λʲ ΔE_{t+1} π_{t+1}`. -/
theorem innov_pi_iter (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r)
    (t j : ℕ) : innov 𝔼 t (π (t + 1 + j)) = lam σ κ θ ^ j • innov 𝔼 t (π (t + 1)) := by
  have h1 := E_pi_iter hD hM (t + 1) j
  have h2 := congrArg (𝔼.E t) h1
  rw [map_sub, 𝔼.tower (by omega : t ≤ t + 1), 𝔼.const, map_smul, map_sub, 𝔼.const] at h2
  · unfold innov
    rw [hM.adapted_pi (t + 1)]
    have e1 : 𝔼.E (t + 1) (π (t + 1 + j)) =
        (fun _ => πs) + lam σ κ θ ^ j • (π (t + 1) - fun _ => πs) := by
      rw [← h1]
      abel
    have e2 : 𝔼.E t (π (t + 1 + j)) =
        (fun _ => πs) + lam σ κ θ ^ j • (𝔼.E t (π (t + 1)) - fun _ => πs) := by
      rw [← h2]
      abel
    rw [e1, e2]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): the innovation in the ex-post real return,
`ΔE_{t+1}(i_{t+1+j} − π_{t+2+j}) = −λʲ/(1 − θ + σκ) · ΔE_{t+1} π_{t+1}`. -/
theorem innov_return (hD : 1 - θ + σ * κ ≠ 0) (hσκ : σ * κ ≠ 0)
    (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t j : ℕ) :
    innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) =
      (-(lam σ κ θ ^ j / (1 - θ + σ * κ))) • innov 𝔼 t (π (t + 1)) := by
  set s := t + 1 + j with hs
  have hs2 : t + 2 + j = s + 1 := by omega
  rw [hs2]
  -- the real rate in terms of inflation
  have hr : r s = (-(1 / (1 - θ + σ * κ))) • (π s - fun _ => πs) := by
    have h1 := r_eq hM s
    have h2 := eq_9_21 hD hM s
    have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
    funext ω
    have a := congrFun h1 ω
    have b := congrFun h2 ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a b ⊢
    have hE : 𝔼.E s (π (s + 1)) ω = πs + lam σ κ θ * (π s ω - πs) := by linarith
    have e : σ * κ * r s ω = σ * κ * (-(1 / (1 - θ + σ * κ)) * (π s ω - πs)) := by
      rw [a, hE]
      unfold lam
      field_simp
      ring
    exact mul_left_cancel₀ hσκ e
  have hdecomp : i s - π (s + 1) =
      r s + (𝔼.E s (π (s + 1)) - π (s + 1)) := by
    rw [hM.is_9_19 s]
    abel
  have hts : t + 1 ≤ s := by omega
  have hz : innov 𝔼 t (𝔼.E s (π (s + 1)) - π (s + 1)) = 0 := by
    unfold innov
    rw [map_sub, map_sub, 𝔼.tower hts, 𝔼.tower (by omega : t ≤ s)]
    abel
  have hc : innov 𝔼 t (fun _ => πs) = 0 := by
    unfold innov
    rw [𝔼.const, 𝔼.const, sub_self]
  have hlin : ∀ y z : Ω → ℝ, innov 𝔼 t (y + z) = innov 𝔼 t y + innov 𝔼 t z := fun y z => by
    unfold innov
    rw [map_add, map_add]
    abel
  have hsm : ∀ (c : ℝ) (y : Ω → ℝ), innov 𝔼 t (c • y) = c • innov 𝔼 t y := fun c y => by
    unfold innov
    rw [map_smul, map_smul, smul_sub]
  have hsub : ∀ y z : Ω → ℝ, innov 𝔼 t (y - z) = innov 𝔼 t y - innov 𝔼 t z := fun y z => by
    unfold innov
    rw [map_sub, map_sub]
    abel
  rw [hdecomp, hlin, hz, add_zero, hr, hsm, hsub, hc, sub_zero, hs, innov_pi_iter hD hM t j,
    smul_smul]
  congr 1
  ring

/-- Cochrane (2023), eq. (9.22), p. 275: the linearised government debt valuation equation,
`ΔE_{t+1} π_{t+1} = −ε^{Σs}_{t+1} + ∑_{j≥1} ρʲ ΔE_{t+1}(i_{t+j} − π_{t+1+j})`, where
`ε^{Σs}_{t+1} = ΔE_{t+1} ∑ⱼ ρʲ s̃_{t+1+j}` is the surplus (fiscal) shock. -/
def Valuation (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (π i ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t, innov 𝔼 t (π (t + 1)) = -ε (t + 1) + fun ω =>
    ∑' j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω

/-- Cochrane (2023), eq. (9.23), p. 276: `D = (1 − ρ)(1 − θ) + σκ`. -/
noncomputable def coefD (σ κ θ ρ : ℝ) : ℝ := (1 - ρ) * (1 - θ) + σ * κ

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): the discount-rate term of (9.22) equals
`−(ρ/D) ΔE_{t+1} π_{t+1}`. -/
theorem valuation_sum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) (ω : Ω) :
    ∑' j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      -(ρ / coefD σ κ θ ρ) * innov 𝔼 t (π (t + 1)) ω := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hl := lam_bounds hθ1 hσκ
  have hρl : |ρ * lam σ κ θ| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hρ0 hl.1)]
    calc ρ * lam σ κ θ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hl.2.le hρ0
      _ < 1 := by linarith
  have hterm : ∀ j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      (-(ρ * innov 𝔼 t (π (t + 1)) ω / (1 - θ + σ * κ))) * (ρ * lam σ κ θ) ^ j := by
    intro j
    rw [innov_return hD hσκ.ne' hM t j]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_abs_lt_one hρl]
  have hDpos : 0 < coefD σ κ θ ρ := by
    unfold coefD
    have : 0 ≤ (1 - ρ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h1 : 1 - ρ * lam σ κ θ ≠ 0 := by
    have := (abs_lt.mp hρl).2
    linarith
  have hkey : (1 - θ + σ * κ) * (1 - ρ * lam σ κ θ) = coefD σ κ θ ρ := by
    unfold lam coefD
    field_simp
    ring
  rw [← hkey]
  field_simp

/-- Cochrane (2023), eq. (9.23), p. 276 (**Theorem ST**): given (9.17)–(9.20) with `θ ∈ [0, 1]`,
`σκ > 0` and `0 ≤ ρ < 1`, the valuation equation (9.22) holds if and only if
`ΔE_{t+1} π_{t+1} = −D/(D + ρ) · ε^{Σs}_{t+1}` with `D = (1 − ρ)(1 − θ) + σκ`. -/
theorem unexpected_inflation_iff {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ} :
    Valuation 𝔼 ρ π i ε ↔ ∀ t, innov 𝔼 t (π (t + 1)) =
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1) := by
  have hDpos : 0 < coefD σ κ θ ρ := by
    unfold coefD
    have : 0 ≤ (1 - ρ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hDρ : 0 < coefD σ κ θ ρ + ρ := by linarith
  constructor
  · intro hV t
    funext ω
    have h := congrFun (hV t) ω
    simp only [Pi.add_apply, Pi.neg_apply] at h
    rw [valuation_sum hρ0 hρ1 hθ1 hσκ hM t ω] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp at h ⊢
    linarith
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [valuation_sum hρ0 hρ1 hθ1 hσκ hM t ω, h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Cochrane (2023), eq. (9.23), p. 276: in any solution of (9.17)–(9.22),
`ΔE_{t+1} π_{t+1} = −((1 − ρ)(1 − θ) + σκ)/((1 − ρ)(1 − θ) + σκ + ρ) · ε^{Σs}_{t+1}`. -/
theorem eq_9_23 {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ}
    (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = (-(((1 - ρ) * (1 - θ) + σ * κ) /
      ((1 - ρ) * (1 - θ) + σ * κ + ρ))) • ε (t + 1) :=
  (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mp hV t

/-- Cochrane (2023), §9.4.1, p. 276: the solution path. In any solution of (9.17)–(9.22) with
inflation adapted, `π_{t+1} = π^{e*} + λ(π_t − π^{e*}) − D/(D + ρ) · ε^{Σs}_{t+1}`. -/
theorem pi_succ {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ}
    (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    π (t + 1) = (fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1) := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have h1 := (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mp hV t
  have h2 := eq_9_21 hD hM t
  unfold innov at h1
  rw [hM.adapted_pi (t + 1)] at h1
  rw [← h1, ← h2]
  abel

/-- Cochrane (2023), §9.4.1, pp. 275–276 (uniqueness): two solutions of (9.17)–(9.22) with the same
fiscal shocks and the same initial inflation coincide (inflation, output, and both rates). -/
theorem unique_solution {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) {ε : ℕ → Ω → ℝ} {π' x' i' r' : ℕ → Ω → ℝ}
    (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (hM' : SimpleModel 𝔼 σ κ θ πs π' x' i' r')
    (hV : Valuation 𝔼 ρ π i ε) (hV' : Valuation 𝔼 ρ π' i' ε) (h0 : π 0 = π' 0) :
    π = π' ∧ r = r' ∧ i = i' ∧ x = x' := by
  have hπ : π = π' := by
    funext t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [pi_succ hρ0 hρ1 hθ1 hσκ hM hV t, pi_succ hρ0 hρ1 hθ1 hσκ hM' hV' t, ih]
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hr : r = r' := by
    funext t
    have a := r_eq hM t
    have b := r_eq hM' t
    rw [← hπ] at b
    rw [← b] at a
    funext ω
    have := congrFun a ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hσκ0 this
  have hi : i = i' := by
    funext t
    rw [hM.is_9_20 t, hM'.is_9_20 t, hr]
  refine ⟨hπ, hr, hi, ?_⟩
  funext t
  rw [hM.is_9_17 t, hM'.is_9_17 t, hi, hπ]

/-- Cochrane (2023), §9.4.1, p. 276: the solution path `π_0`, `π_{t+1} = π^{e*} + λ(π_t − π^{e*}) −
k ε_{t+1}`. -/
noncomputable def solPi (lamv k πs : ℝ) (π0 : Ω → ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => (fun _ => πs) + lamv • (solPi lamv k πs π0 ε t - fun _ => πs) + (-k) • ε (t + 1)

/-- Cochrane (2023), §9.4.1, pp. 275–276 (**existence**): for any adapted fiscal shocks with
`E_t ε_{t+1} = 0` and any initial inflation known at date 0, the path `solPi` together with
`r_t = (E_t π_{t+1} − π_t)/(σκ)`, `x_t = −σ r_t`, `i_t = r_t + E_t π_{t+1}` solves (9.17)–(9.22). -/
theorem exists_solution {σ κ θ πs ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hε0 : ∀ t, 𝔼.E t (ε (t + 1)) = 0)
    {π0 : Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) :
    let π := solPi (lam σ κ θ) (coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) πs π0 ε
    let r := fun t => (1 / (σ * κ)) • (𝔼.E t (π (t + 1)) - π t)
    SimpleModel 𝔼 σ κ θ πs π (fun t => (-σ) • r t) (fun t => r t + 𝔼.E t (π (t + 1))) r ∧
      Valuation 𝔼 ρ π (fun t => r t + 𝔼.E t (π (t + 1))) ε := by
  intro π r
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul hσκ0
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hσκ0
  have hadapt : 𝔼.Adapted π := by
    intro t
    induction t with
    | zero => exact hπ0
    | succ t ih =>
      change 𝔼.E (t + 1) ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
        (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) = _
      rw [map_add, map_add, map_smul, map_smul, map_sub, 𝔼.const,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, hεa (t + 1)]
      rfl
  have hEπ : ∀ t, 𝔼.E t (π (t + 1)) = (fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) := by
    intro t
    change 𝔼.E t ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, map_sub, 𝔼.const, hadapt t, hε0 t, smul_zero,
      add_zero]
  have hM : SimpleModel 𝔼 σ κ θ πs π (fun t => (-σ) • r t)
      (fun t => r t + 𝔼.E t (π (t + 1))) r := by
    refine ⟨hadapt, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · simp only [add_sub_cancel_right]
    · funext ω
      simp only [r, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    · simp only [add_sub_cancel_right]
    · rw [hEπ t]
      funext ω
      simp only [r, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hEπ t]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
      have e : πs + lam σ κ θ * (π t ω - πs) - π t ω = (lam σ κ θ - 1) * (π t ω - πs) := by ring
      rw [e, hls]
      unfold lam
      field_simp
      ring
  refine ⟨hM, (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mpr fun t => ?_⟩
  unfold innov
  rw [hadapt (t + 1)]
  change ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) - 𝔼.E t (π (t + 1)) = _
  rw [hEπ t]
  abel

/-- Cochrane (2023), §9.4.1, p. 276: with bounded fiscal shocks the solution is bounded,
`|π_t − π^{e*}| ≤ |π_0 − π^{e*}| + k M/(1 − λ)` (`0 ≤ λ < 1`, `0 ≤ k`). -/
theorem solution_bounded {lamv k πs M : ℝ} (hl0 : 0 ≤ lamv) (hl1 : lamv < 1) (hk : 0 ≤ k)
    {π0 : Ω → ℝ} {B0 : ℝ} (hπ0 : ∀ ω, |π0 ω - πs| ≤ B0) {ε : ℕ → Ω → ℝ}
    (hε : ∀ t ω, |ε t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |solPi lamv k πs π0 ε t ω - πs| ≤ B0 + k * M / (1 - lamv) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hε 0 ω)
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans (hπ0 ω)
  have h1 : 0 < 1 - lamv := by linarith
  induction t with
  | zero =>
    have : 0 ≤ k * M / (1 - lamv) := by positivity
    exact (hπ0 ω).trans (by linarith)
  | succ t ih =>
    simp only [solPi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [show πs + lamv * (solPi lamv k πs π0 ε t ω - πs) + -k * ε (t + 1) ω - πs =
      lamv * (solPi lamv k πs π0 ε t ω - πs) + -k * ε (t + 1) ω by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hl0, abs_neg, abs_of_nonneg hk]
    have h2 : lamv * |solPi lamv k πs π0 ε t ω - πs| ≤ lamv * (B0 + k * M / (1 - lamv)) :=
      mul_le_mul_of_nonneg_left ih hl0
    have h3 : k * |ε (t + 1) ω| ≤ k * M := mul_le_mul_of_nonneg_left (hε (t + 1) ω) hk
    have h4 : lamv * (B0 + k * M / (1 - lamv)) + k * M ≤ B0 + k * M / (1 - lamv) := by
      have e : lamv * (B0 + k * M / (1 - lamv)) + k * M =
          lamv * B0 + k * M / (1 - lamv) := by
        field_simp
        ring
      rw [e]
      nlinarith
    linarith

/-! ### The cases `θ = 0` and `θ = 1` -/

/-- Cochrane (2023), §9.4.1, p. 276: at `θ = 0` (interest-rate peg) the coefficients are
`1/(1 + σκ)` and `(1 − ρ + σκ)/(1 + σκ)`. -/
theorem theta_zero (σ κ ρ : ℝ) :
    lam σ κ 0 = 1 / (1 + σ * κ) ∧
      coefD σ κ 0 ρ / (coefD σ κ 0 ρ + ρ) = (1 - ρ + σ * κ) / (1 + σ * κ) := by
  unfold lam coefD
  constructor
  · ring_nf
  · ring_nf

/-- Cochrane (2023), §9.4.1, p. 276 (`θ = 1`, the spread target, proved directly — error E9.5):
`λ = 0`, `D/(D + ρ) = σκ/(σκ + ρ)`, so in any solution `E_t π_{t+1} = π^{e*}` and
`π_{t+1} = π^{e*} − σκ/(σκ + ρ) ε^{Σs}_{t+1}`: inflation is serially uncorrelated around the
target. -/
theorem theta_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hσκ : 0 < σ * κ)
    (hM : SimpleModel 𝔼 σ κ 1 πs π x i r) {ε : ℕ → Ω → ℝ} (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    𝔼.E t (π (t + 1)) = (fun _ => πs) ∧
      π (t + 1) = (fun _ => πs) + (-(σ * κ / (σ * κ + ρ))) • ε (t + 1) := by
  have hl : lam σ κ 1 = 0 := by simp [lam]
  have hD : coefD σ κ 1 ρ = σ * κ := by simp [coefD]
  have h1 : (1 : ℝ) - 1 + σ * κ ≠ 0 := by linarith
  constructor
  · have := eq_9_21 h1 hM t
    rw [hl, zero_smul] at this
    exact sub_eq_zero.mp this
  · have := pi_succ hρ0 hρ1 le_rfl hσκ hM hV t
    rw [hl, hD, zero_smul, add_zero] at this
    exact this

/-- Cochrane (2023), p. 277 (`θ = 1`): output and the real and nominal rates follow inflation,
`x_t = (π_t − π^{e*})/κ`, `r_t = −(π_t − π^{e*})/(σκ)`, `i_t = π^{e*} − (π_t − π^{e*})/(σκ)`. -/
theorem theta_one_paths (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hM : SimpleModel 𝔼 σ κ 1 πs π x i r)
    (t : ℕ) : x t = (1 / κ) • (π t - fun _ => πs) ∧
      r t = (-(1 / (σ * κ))) • (π t - fun _ => πs) ∧
      i t = (fun _ => πs) + (-(1 / (σ * κ))) • (π t - fun _ => πs) := by
  have h21 := eq_9_21_mul hM t
  have hE : 𝔼.E t (π (t + 1)) = fun _ => πs := by
    have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
    funext ω
    have a := congrFun h21 ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_self, zero_mul, zero_add] at a
    have := (mul_eq_zero.mp a).resolve_left hσκ
    linarith
  have hr := r_eq hM t
  have h18 := hM.is_9_18 t
  have h19 := hM.is_9_19 t
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    have b := congrFun h18 ω
    rw [hE] at b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at b
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linarith
  · funext ω
    have a := congrFun hr ω
    rw [hE] at a
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a ⊢
    field_simp
    linarith
  · funext ω
    have a := congrFun hr ω
    have c := congrFun h19 ω
    rw [hE] at a c
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.add_apply] at a c ⊢
    have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
    have hr' : r t ω = (πs - π t ω) / (σ * κ) := by
      rw [eq_div_iff hσκ]
      linarith
    rw [show i t ω = r t ω + πs by linarith, hr']
    field_simp
    ring

/-- Cochrane (2023), p. 276, footnote 1 (error E9.5): for `θ ≠ 1` the rule gives
`r_t = (π^{e*} − E_t π_{t+1})/(1 − θ)`; this formula is undefined at `θ = 1`, where `r` is instead
pinned down by `σκ r_t = E_t π_{t+1} − π_t` (`r_eq`). -/
theorem footnote_r (hθ : θ ≠ 1) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    r t = (1 / (1 - θ)) • ((fun _ => πs) - 𝔼.E t (π (t + 1))) := by
  have h1 : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  funext ω
  have c := congrFun (hM.is_9_19 t) ω
  have d := congrFun (hM.is_9_20 t) ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.add_apply] at c d ⊢
  field_simp
  linarith

/-- Cochrane (2023), §9.4.1, p. 276 ("at `θ = 1` … equals the `θ → 1` limit"): the coefficient of
(9.23) is continuous in `θ` and tends to `σκ/(σκ + ρ)`, and `λ → 0`. -/
theorem tendsto_coef_theta_one {σ κ ρ : ℝ} (hσκ : 0 < σ * κ) (hρ0 : 0 ≤ ρ) :
    Tendsto (fun θ => coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) (𝓝 1) (𝓝 (σ * κ / (σ * κ + ρ))) ∧
      Tendsto (fun θ => lam σ κ θ) (𝓝 1) (𝓝 0) := by
  constructor
  · have h : ContinuousAt (fun θ => coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) 1 := by
      unfold coefD
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simp only [sub_self, mul_zero, zero_add]
      linarith
    have := h.tendsto
    simpa [coefD] using this
  · have h : ContinuousAt (fun θ => lam σ κ θ) 1 := by
      unfold lam
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simp only [sub_self, zero_add]
      exact hσκ.ne'
    have := h.tendsto
    simpa [lam] using this

/-! ### The full new-Keynesian model (9.24)–(9.26) -/

variable (𝔼 σ κ πs π x i)
variable (β : ℝ) (ux upi : ℕ → Ω → ℝ)

/-- Cochrane (2023), eqs. (9.24)–(9.25), p. 277: the IS curve `x_t = E_t x_{t+1} − σ(i_t − E_t
π_{t+1}) + u_{x,t}`,
the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_{π,t}`, and the spread target `E_t π_{t+1} =
π^{e*}`. -/
structure FullNK where
  is_9_24 : ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1))) + ux t
  is_9_25 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + upi t
  spread : ∀ t, 𝔼.E t (π (t + 1)) = fun _ => πs

variable {𝔼 σ κ πs π x i β ux upi}

/-- Cochrane (2023), (9.26) first line, p. 277: `κ x_t = π_t − β π^{e*} − u_{π,t}`, i.e.
`x_t = [(1 − β)π^{e*} + ΔE_t π_t − u_{π,t}]/κ` with `ΔE_t π_t = π_t − π^{e*}`. The IS shock `u_x`
does not
appear (given inflation; survey E9.7). -/
theorem x_formula (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t : ℕ) :
    κ • x t = (fun _ => (1 - β) * πs) + (π t - fun _ => πs) - upi t := by
  have h := hN.is_9_25 t
  rw [hN.spread t] at h
  funext ω
  have a := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at a ⊢
  linarith

/-- Cochrane (2023), §9.4.1, p. 277: with the spread target, the inflation innovation is
`ΔE_{t+1} π_{t+1} = π_{t+1} − π^{e*}` (for adapted inflation). -/
theorem innov_eq (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (hπ : 𝔼.Adapted π) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = π (t + 1) - fun _ => πs := by
  unfold innov
  rw [hπ (t + 1), hN.spread t]

/-- Cochrane (2023), eq. (9.26), p. 277, **corrected** (error E9.4): the real rate
`r_t = i_t − E_t π_{t+1}` obeys
`σ r_t = −ΔE_t π_t/κ + u_{x,t} + (u_{π,t} − E_t u_{π,t+1})/κ` (with `ΔE_t π_t = π_t − π^{e*}`); the
book prints `+ΔE_t π_t/κ` and omits the `1/κ` on the `u_π` terms. -/
theorem r_formula (hκ : κ ≠ 0) (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t : ℕ) :
    σ • (i t - 𝔼.E t (π (t + 1))) =
      (1 / κ) • (-(π t - fun _ => πs) + (upi t - 𝔼.E t (upi (t + 1)))) + ux t := by
  have h24 := hN.is_9_24 t
  have hx := x_formula hN t
  have hx1 := congrArg (𝔼.E t) (x_formula hN (t + 1))
  rw [map_smul, map_sub, map_add, 𝔼.const, map_sub, hN.spread t, 𝔼.const] at hx1
  funext ω
  have a := congrFun h24 ω
  have b := congrFun hx ω
  have c := congrFun hx1 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at a b c ⊢
  field_simp
  linear_combination κ * a - b + c

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4): the printed formula minus the correct one is
`(1/σ)[2 ΔE_t π_t/κ + (1 − 1/κ)(u_{π,t} − E_t u_{π,t+1})]`. -/
theorem printed_minus_corrected (σ κ D ux upi Eupi : ℝ) (hσ : σ ≠ 0) :
    (1 / σ) * (D / κ + ux + upi - Eupi) - (1 / σ) * (-D / κ + ux + (upi - Eupi) / κ) =
      (1 / σ) * (2 * D / κ + (1 - 1 / κ) * (upi - Eupi)) := by
  field_simp
  ring

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4, the `1/κ`): a perfect-foresight solution of
(9.24)–(9.25) with the spread target (`β = 1/2`, `σ = 1`, `κ = 2`, `π^{e*} = 0`, `π ≡ 0`, `u_x ≡ 0`,
`u_{π,0} = 1`, `u_{π,t} = 0` for `t ≥ 1`) where the printed formula gives `σ r_0 = 1` but `σ r_0 =
1/2`. -/
theorem printed_9_26_fails_perfectForesight :
    ∃ π x i ux upi : ℕ → Unit → ℝ, FullNK perfectForesight 1 2 0 π x i (1 / 2) ux upi ∧
      1 * (i 0 () - π 1 ()) = 1 / 2 ∧
      (0 - 0) / 2 + ux 0 () + upi 0 () - upi 1 () = 1 := by
  set upi : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 0 with hu
  set x : ℕ → Unit → ℝ := fun t _ => -upi t () / 2 with hx
  refine ⟨fun _ _ => 0, x, fun t _ => x (t + 1) () - x t (), fun _ _ => 0, upi,
    ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · funext ω
    change x t () = x (t + 1) () - 1 * (x (t + 1) () - x t () - 0) + 0
    ring
  · funext ω
    change (0 : ℝ) = 1 / 2 * 0 + 2 * x t () + upi t ()
    simp only [hx]
    ring
  · rfl
  · simp [hx, hu]
    norm_num
  · simp [hu]

/-- Cochrane (2023), §9.4.1, p. 277: the coin-flip inflation used in `printed_9_26_fails_coin`,
`π_t = ε_t` (the mean-zero coin shock). -/
noncomputable def coinPi (t : ℕ) (ω : Bool × Bool) : ℝ := ExpectationsFiniteTree.coinShock t ω

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4, the sign): under genuine uncertainty (the
two-coin tree), with `β = 1/2`, `σ = κ = 1`, `π^{e*} = 0`, no shocks `u_x = u_π = 0`, and inflation
equal to a mean-zero coin innovation, (9.24)–(9.25) and the spread target hold, and
`σ r_1 = −ΔE_1 π_1/κ`; at a state with `ΔE_1 π_1 = 1` this is `−1`, while the printed (9.26) gives
`+1`. -/
theorem printed_9_26_fails_coin :
    FullNK ExpectationsFiniteTree.coinSystem 1 1 0 coinPi coinPi
      (fun t => -(ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1))) + (-1 : ℝ) • coinPi t +
        ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1))) (1 / 2) 0 0 ∧
      innov ExpectationsFiniteTree.coinSystem 0 (coinPi 1) (true, true) = 1 ∧
      1 * ((-(ExpectationsFiniteTree.coinSystem.E 1 (coinPi 2)) + (-1 : ℝ) • coinPi 1 +
        ExpectationsFiniteTree.coinSystem.E 1 (coinPi 2)) - ExpectationsFiniteTree.coinSystem.E 1
          (coinPi 2)) (true, true) = -1 := by
  have hmean : ∀ t, ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1)) = 0 := fun t =>
    ExpectationsFiniteTree.coinShock_mean_zero t
  have hadapt : ExpectationsFiniteTree.coinSystem.Adapted coinPi := fun t => by
    funext ω
    rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
      ExpectationsFiniteTree.coinShock_measurable t h
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · simp only [hmean t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    ring
  · simp only [hmean t]
    funext ω
    simp
  · exact (hmean t).trans rfl
  · unfold innov
    rw [hadapt 1, hmean 0]
    simp [coinPi, ExpectationsFiniteTree.coinShock]
  · rw [hmean 1]
    simp [coinPi, ExpectationsFiniteTree.coinShock]

/-! ### Holden's rule -/

/-- Cochrane (2023), §9.4.1, p. 278 (Holden 2020): with the spread rule `i_t = r_t + π* + φ(π_t −
π*)`
and `r_t = i_t − E_t π_{t+1}`, i.e. `E_t π_{t+1} − π* = φ(π_t − π*)`, and `|φ| > 1`, the unique
bounded
inflation process is `π ≡ π*` (new-Keynesian equilibrium selection). -/
theorem holden_unique {φ πs : ℝ} (hφ : 1 < |φ|) {π i r : ℕ → Ω → ℝ}
    (hr : ∀ t, r t = i t - 𝔼.E t (π (t + 1)))
    (hrule : ∀ t, i t = r t + (fun _ => πs) + φ • (π t - fun _ => πs)) (hb : BoundedProc π) :
    π = fun _ _ => πs := by
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  have hE : ∀ t, 𝔼.E t (π (t + 1)) = (fun _ => πs) + φ • (π t - fun _ => πs) := by
    intro t
    have h1 := hr t
    rw [hrule t] at h1
    funext ω
    have := congrFun h1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  set d : ℕ → Ω → ℝ := fun t => π t - fun _ => πs with hd
  have hdsol : ∀ t, d t = φ⁻¹ • 𝔼.E t (d (t + 1)) + 0 := by
    intro t
    simp only [hd, map_sub, hE t, 𝔼.const, add_zero]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  have h0sol : ∀ t, (0 : Ω → ℝ) = φ⁻¹ • 𝔼.E t (0 : Ω → ℝ) + 0 := fun t => by simp
  have hinv : |φ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨M, hM⟩ := hb
  have hdb : BoundedProc d := ⟨M + |πs|, fun t ω => by
    simp only [hd, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
  have h := 𝔼.forward_unique hinv (u := fun _ => 0) (z₂ := fun _ => 0) hdsol h0sol hdb
    ⟨0, fun _ _ => by simp⟩
  funext t ω
  have := congrFun (congrFun h t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

end Cochrane.AssetsRulesBalanceSheets.SpreadTarget

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Debt sales with a spread target

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.4.2
"Debt sales with a spread target", eq. (9.27), pp. 278–280.

The end-of-period valuation equation (9.27) is `β b_t + β B_t E_t(1/P_{t+1}) = W` with
`W = E_t ∑_{j≥1} βʲ s_{t+j}` held fixed. Write `e = E_t(1/P_{t+1})`. The government sold `b₀` real
and
`B₀` nominal bonds and then swaps `P*` nominal bonds for each real bond,
`−(B_t − B₀) = (b_t − b₀) P*`.

## Main results

* `eq_9_27`: `Q_t B_t/P_t = β B_t E_t(1/P_{t+1})` (pull-out property); `end_of_period_valuation`.
* `market_price_irrelevant`: swaps at the market rate `e₀` leave `E_t(1/P_{t+1})` unchanged.
* `swap_valuation_iff`, `hasDerivAt_eSwap`: after a swap at `P*`, `e(B) = (W/β − b₀ + (B −
B₀)/P*)/B`
  and `de/dB = −(e − 1/P*)/B` (the book's differential, p. 280).
* **The hyperbola (error E9.8)**: `eSwap_sub_target`: `e(B) − 1/P* = C/B` with
  `C = W/β − b₀ − B₀/P* = B₀(e₀ − 1/P*)`; `swap_reaches_target_iff`: free exchange at `P*` reaches
  `E_t(1/P_{t+1}) = 1/P*` at some finite `B` iff the gap was zero to begin with — the book's bullet
  "offering to freely exchange real debt for nominal debt at the rate `P*` … drives the expected
  price level to `E_t(1/P_{t+1}) = 1/P*`" does not follow; `real_debt_exhausted`: when the public's
  real debt is exhausted the gap is still `C/(B₀ + P* b₀)`; `numeric_example` (gap `7/30 → 35/222`).
* `eSwap_strictAntiOn`, `eSwap_gt_target`: the book's qualitative direction is right — with
  `1/P* < e₀` the expected inverse price level falls as nominal debt rises, but stays above `1/P*`.
* `swap_invariant`, `passive_supply` (the corrected statement): swaps at `P*` leave `b + B/P*`
  unchanged, and the target is reached iff `β(b + B/P*) = W`; a passive supply of nominal debt
  (sold for goods, as with an interest-rate peg) reaches it at the unique `B = P*(W/β − b)`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.SpreadSwap

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (9.27), p. 279: with the nominal bond price `Q_t = β E_t(P_t/P_{t+1})`, the
pull-out property and `B_t`, `P_t` known at `t`, `Q_t B_t/P_t = β B_t E_t(1/P_{t+1})`. -/
theorem eq_9_27 (h𝔼 : 𝔼.PullOut) {β : ℝ} {P B Q : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (hQ : ∀ t, Q t = β • 𝔼.E t (P t / P (t + 1))) (t : ℕ) :
    Q t * B t / P t = β • (B t * 𝔼.E t (fun ω => 1 / P (t + 1) ω)) := by
  have hsplit : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  rw [hQ t, hsplit, h𝔼 t _ _ (hPa t)]
  funext ω
  simp only [Pi.div_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [(hP t ω).ne']

/-- Cochrane (2023), eq. (9.27), p. 279: subtracting the date-`t` surplus from the valuation
equation `b_{t−1} + B_{t−1}/P_t = E_t ∑_{j≥0} βʲ s_{t+j} = s_t + W` and the flow condition
`b_{t−1} + B_{t−1}/P_t = s_t + β b_t + Q_t B_t/P_t` gives `β b_t + Q_t B_t/P_t = W`. -/
theorem end_of_period_valuation {bprev Bprev P s b B Q W β : ℝ}
    (hval : bprev + Bprev / P = s + W) (hflow : bprev + Bprev / P = s + β * b + Q * B / P) :
    β * b + Q * B / P = W := by
  linarith

/-- Cochrane (2023), §9.4.2, p. 279: "if it exchanges real for nominal bonds at market prices, the
left-hand side does not change" — swapping at the market rate `e₀` (`b = b₀ − (B − B₀) e₀`) leaves
`E_t(1/P_{t+1}) = e₀` as the unique solution of (9.27), for every `B ≠ 0`. -/
theorem market_price_irrelevant {β W b0 B0 e0 B e : ℝ} (hβ : β ≠ 0) (hB : B ≠ 0)
    (h0 : β * b0 + β * B0 * e0 = W) :
    β * (b0 - (B - B0) * e0) + β * B * e = W ↔ e = e0 := by
  constructor
  · intro h
    have h2 : β * B * (e - e0) = 0 := by linear_combination h - h0
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero hβ hB)
    · linarith
  · intro h
    rw [h, ← h0]
    ring

/-- Cochrane (2023), §9.4.2, pp. 279–280: the expected inverse price level after swapping
`B − B₀` nominal bonds at `P*`, `e(B) = (W/β − b₀ + (B − B₀)/P*)/B`. -/
noncomputable def eSwap (β W b0 B0 Pstar B : ℝ) : ℝ := (W / β - b0 + (B - B0) / Pstar) / B

/-- Cochrane (2023), §9.4.2, p. 279 (the display after "Plug into (9.27)"): with real debt
`b = b₀ − (B − B₀)/P*`, the valuation (9.27) holds iff `E_t(1/P_{t+1}) = e(B)`. -/
theorem swap_valuation_iff {β W b0 B0 Pstar B e : ℝ} (hβ : β ≠ 0) (hB : B ≠ 0) :
    β * (b0 - (B - B0) / Pstar) + β * B * e = W ↔ e = eSwap β W b0 B0 Pstar B := by
  unfold eSwap
  rw [eq_div_iff hB]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Cochrane (2023), §9.4.2, p. 280 (**error E9.8**, the hyperbola): integrating the book's
differential, `e(B) − 1/P* = C/B` with `C = W/β − b₀ − B₀/P*`. -/
theorem eSwap_sub_target {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : B ≠ 0) :
    eSwap β W b0 B0 Pstar B - 1 / Pstar = (W / β - b0 - B0 / Pstar) / B := by
  unfold eSwap
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (the book's differential): `d e/dB = −(e − 1/P*)/B`. -/
theorem hasDerivAt_eSwap {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : B ≠ 0) :
    HasDerivAt (eSwap β W b0 B0 Pstar)
      (-(eSwap β W b0 B0 Pstar B - 1 / Pstar) / B) B := by
  set C := W / β - b0 - B0 / Pstar with hC
  have h := HasDerivAt.add_const (1 / Pstar) (HasDerivAt.const_mul C (hasDerivAt_inv hB))
  have hev : eSwap β W b0 B0 Pstar =ᶠ[𝓝 B] fun B => C * B⁻¹ + 1 / Pstar := by
    filter_upwards [isOpen_ne.mem_nhds hB] with B' hB'
    have := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB'
    rw [← hC] at this
    have e2 : C / B' = C * B'⁻¹ := div_eq_mul_inv _ _
    linarith
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h hev) ?_
  rw [eSwap_sub_target hP hB, ← hC]
  field_simp

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): the constant of the hyperbola is the initial gap times
initial nominal debt, `C = B₀ (e₀ − 1/P*)` with `e₀ = e(B₀)` the pre-swap market value. -/
theorem gap_const {β W b0 B0 Pstar : ℝ} (hB0 : B0 ≠ 0) :
    W / β - b0 - B0 / Pstar = B0 * (eSwap β W b0 B0 Pstar B0 - 1 / Pstar) := by
  unfold eSwap
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (**error E9.8**): free exchange at `P*` with surpluses and the
initial sales held fixed reaches `E_t(1/P_{t+1}) = 1/P*` at some finite nonzero `B` if and only if
the initial gap `e₀ − 1/P*` is already zero; otherwise the gap shrinks like `1/B` but never closes.
-/
theorem swap_reaches_target_iff {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0) (hB0 : B0 ≠ 0) :
    (∃ B, B ≠ 0 ∧ eSwap β W b0 B0 Pstar B = 1 / Pstar) ↔
      eSwap β W b0 B0 Pstar B0 = 1 / Pstar := by
  constructor
  · rintro ⟨B, hB, h⟩
    have h1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB
    rw [h, sub_self] at h1
    have hC : W / β - b0 - B0 / Pstar = 0 := by
      have := h1.symm
      rwa [div_eq_zero_iff, or_iff_left hB] at this
    have h2 := gap_const (β := β) (W := W) (b0 := b0) (Pstar := Pstar) hB0
    rw [hC] at h2
    have := (mul_eq_zero.mp h2.symm).resolve_left hB0
    linarith
  · intro h
    exact ⟨B0, hB0, h⟩

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): the public's real debt `b₀ − (B − B₀)/P*` is exhausted
at
`B₁ = B₀ + P* b₀`, where the gap is still `C/B₁`. -/
theorem real_debt_exhausted {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0) (hB1 : B0 + Pstar * b0 ≠ 0) :
    b0 - ((B0 + Pstar * b0) - B0) / Pstar = 0 ∧
      eSwap β W b0 B0 Pstar (B0 + Pstar * b0) - 1 / Pstar =
        (W / β - b0 - B0 / Pstar) / (B0 + Pstar * b0) := by
  refine ⟨by field_simp; ring, eSwap_sub_target hP hB1⟩

/-- Cochrane (2023), §9.4.2, p. 280: the book's direction is right — if `1/P* < e₀` (the government
offers more nominal bonds per real bond than the market) then, for `B > 0`, `E_t(1/P_{t+1})` falls
strictly as nominal debt rises. -/
theorem eSwap_strictAntiOn {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0)
    (hC : 0 < W / β - b0 - B0 / Pstar) :
    StrictAntiOn (eSwap β W b0 B0 Pstar) (Set.Ioi 0) := by
  intro B₁ h₁ B₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  have e1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP h₁.ne'
  have e2 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP h₂.ne'
  have : (W / β - b0 - B0 / Pstar) / B₂ < (W / β - b0 - B0 / Pstar) / B₁ :=
    div_lt_div_of_pos_left hC h₁ hlt
  linarith

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): with a positive gap the expected inverse price level
stays strictly above the target at every `B > 0`. -/
theorem eSwap_gt_target {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : 0 < B)
    (hC : 0 < W / β - b0 - B0 / Pstar) : 1 / Pstar < eSwap β W b0 B0 Pstar B := by
  have e1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB.ne'
  have : 0 < (W / β - b0 - B0 / Pstar) / B := div_pos hC hB
  linarith

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8), the survey's numerical example: `W = 10`, `β = 0.96`,
`b₀ = 3`, `B₀ = 5`, `P* = 0.8`. Then `C = 7/6`, the gap is `7/30 ≈ 0.233` before the swaps and
`35/222 ≈ 0.158` when the public's real debt is exhausted (`B = 7.4`). -/
theorem numeric_example :
    (10 : ℝ) / (24 / 25) - 3 - 5 / (4 / 5) = 7 / 6 ∧
      eSwap (24 / 25) 10 3 5 (4 / 5) 5 - 1 / (4 / 5) = 7 / 30 ∧
      eSwap (24 / 25) 10 3 5 (4 / 5) (5 + 4 / 5 * 3) - 1 / (4 / 5) = 35 / 222 ∧
      (3 : ℝ) - ((5 + 4 / 5 * 3) - 5) / (4 / 5) = 0 := by
  unfold eSwap
  norm_num

/-- Cochrane (2023), §9.4.2, p. 279: a swap at `P*` (`−(B − B₀) = (b − b₀)P*`) leaves `b + B/P*`
unchanged. -/
theorem swap_invariant {b b0 B B0 Pstar : ℝ} (hP : Pstar ≠ 0)
    (hswap : -(B - B0) = (b - b0) * Pstar) : b + B / Pstar = b0 + B0 / Pstar := by
  have : B = B0 - (b - b0) * Pstar := by linarith
  rw [this]
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (the corrected statement, E9.8): the target `E_t(1/P_{t+1}) =
1/P*`
is consistent with (9.27) iff the total debt valued at the target equals the present value,
`β(b + B/P*) = W`. Swaps at `P*` cannot change `b + B/P*` (`swap_invariant`); a passive supply of
nominal debt sold for goods (as with an interest-rate peg, the book's `P* = ∞` case) reaches the
target at the unique `B = P*(W/β − b)`. -/
theorem passive_supply {β W b Pstar : ℝ} (hβ : β ≠ 0) (hP : Pstar ≠ 0) :
    (∀ B, β * b + β * B * (1 / Pstar) = W ↔ β * (b + B / Pstar) = W) ∧
      ∃! B, β * b + β * B * (1 / Pstar) = W := by
  refine ⟨fun B => by constructor <;> intro h <;> linear_combination h, ?_⟩
  refine ⟨Pstar * (W / β - b), ?_, fun B hB => ?_⟩
  · field_simp
    ring
  · field_simp at hB
    field_simp
    linear_combination hB

end Cochrane.AssetsRulesBalanceSheets.SpreadSwap

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A price-level target via indexed debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.5
"A price-level target via indexed debt", eqs. (9.28)–(9.29), pp. 281–284.

The government pegs the nominal price of a one-period indexed bond (paying `$P_{t+1}`) at `β P*_t`,
so its real price is `q_t = β P*_t / P_t`. Real debt follows (9.28) `b_{t−1} = s_t + q_t b_t`; the
consumer's first-order condition and budget constraint are (9.29),
`(β P*_t/P_t) u'(c_t) = β u'(c_{t+1})` and `y + b_{t−1} = c_t + s_t + q_t b_t` (perfect foresight).
Lean date `n` carries the debt `b n` outstanding at the start of date `n` (book `b_{n−1}`).

## Main results

* `real_rate_low_iff`: the real return on the pegged bond, `P_t/(βP*_t)`, is below `1/β` iff
  `P_t < P*_t` (p. 281).
* `marginal_utility_strictAntiOn`: strict concavity gives a strictly decreasing marginal utility.
* **Theorem IP**: `one_period_deviation` — if `P_{t+j} = P*_{t+j}` for `j ≥ 1`, consumption is
constant
  from `t + 1` on, and `P_t < P*_t` implies `c_t > c_{t+1}` (`P_t > P*_t` implies `c_t < c_{t+1}`);
  `price_eq_target`: market clearing `c = y` forces `P_t = P*_t` at every date.
* `log_demand`, `log_demand_strictAntiOn`: with log utility the one-period-deviation consumption
  demand is finite at every price level, `c_t = (1 − β)(y + b_{t−1} − s_t) + β(P*_t/P_t)(y − (1 −
β)S)`,
  and falls as `P_t` rises when `y > (1 − β)S` ("with concave utility, consumption and bond demands
  do not explode at off-equilibrium prices", p. 282).
* `nominal_debt_crowds_out_real`: with the peg in place, extra nominal debt is matched one-for-one
  (at `1/P*_{t+1}`) by less real debt; `devaluation_lowers_value`.
* `price_eq_peg_times_rate`: `Q* = P*_t/(1 + r_t)`, so real-rate variation induces price-level
  variation (p. 283).
* `five_minute_example`, `five_minute_unbounded`, `annualised_rate`: the numbers of pp. 283–284
  (`250 · 1.25 = 312.5`; `100 (1.25³⁶⁵ − 1) ≈ 2.36 × 10³⁷` %).
-/

namespace Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg

open Filter Topology

/-- Cochrane (2023), §9.5, p. 281: "with the peg in place buying bonds gives a real return
`1/(1 + r_t) = βP*_t/P_t`. If `P_t < P*_t`, then the real interest rate is too low": the gross real
return `P_t/(βP*_t)` is below `1/β` iff `P_t < P*_t`. -/
theorem real_rate_low_iff {β P Pstar : ℝ} (hβ : 0 < β) (hPs : 0 < Pstar) :
    P / (β * Pstar) < 1 / β ↔ P < Pstar := by
  rw [div_lt_div_iff₀ (mul_pos hβ hPs) hβ]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Cochrane (2023), §9.5, p. 282 ("with concave utility"): a strictly concave utility with
derivative `u'` on positive consumption has strictly decreasing marginal utility. -/
theorem marginal_utility_strictAntiOn {u up : ℝ → ℝ}
    (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) (hd : ∀ c, 0 < c → HasDerivAt u (up c) c) :
    StrictAntiOn up (Set.Ioi 0) := by
  have h := hu.strictAntiOn_deriv (fun c hc => (hd c hc).differentiableAt)
  intro a ha b hb hab
  have e1 := (hd a ha).deriv
  have e2 := (hd b hb).deriv
  have := h ha hb hab
  rwa [e1, e2] at this

/-- Cochrane (2023), eq. (9.29), p. 281 (**Theorem IP**, one-period deviation, p. 282): under
perfect foresight with strictly decreasing marginal utility, if `P_{t+j} = P*_{t+j}` for all
`j ≥ 1`, then `c_{t+1+j} = c_{t+1}` for all `j`; and `P_t < P*_t` implies `c_t > c_{t+1}`, while
`P*_t < P_t` implies `c_t < c_{t+1}`. -/
theorem one_period_deviation {β : ℝ} (hβ : 0 < β) {up : ℝ → ℝ}
    (hup : StrictAntiOn up (Set.Ioi 0)) {c P Pstar : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hP : ∀ n, 0 < P n) (hPs : ∀ n, 0 < Pstar n) (hpos : ∀ n, 0 < up (c n))
    (hfoc : ∀ n, β * Pstar n / P n * up (c n) = β * up (c (n + 1))) (t : ℕ)
    (hlater : ∀ j, P (t + 1 + j) = Pstar (t + 1 + j)) :
    (∀ j, c (t + 1 + j) = c (t + 1)) ∧ (P t < Pstar t → c (t + 1) < c t) ∧
      (Pstar t < P t → c t < c (t + 1)) := by
  have hinj := hup.injOn
  have hstep : ∀ j, c (t + 1 + j + 1) = c (t + 1 + j) := by
    intro j
    have h := hfoc (t + 1 + j)
    rw [hlater j, mul_div_assoc, div_self (hPs _).ne', mul_one] at h
    have h2 := mul_left_cancel₀ hβ.ne' h
    exact (hinj (Set.mem_Ioi.mpr (hc _)) (Set.mem_Ioi.mpr (hc _)) h2).symm
  refine ⟨fun j => ?_, fun hlt => ?_, fun hgt => ?_⟩
  · induction j with
    | zero => simp
    | succ j ih => rw [← add_assoc, hstep j, ih]
  · have h := hfoc t
    have hratio : 1 < Pstar t / P t := (one_lt_div (hP t)).mpr hlt
    have hup_lt : up (c t) < up (c (t + 1)) := by
      have e : β * Pstar t / P t * up (c t) = β * (Pstar t / P t * up (c t)) := by ring
      rw [e] at h
      have h2 := mul_left_cancel₀ hβ.ne' h
      have := hpos t
      nlinarith
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt' | heq
    · have := hup (Set.mem_Ioi.mpr (hc t)) (Set.mem_Ioi.mpr (hc (t + 1))) hlt'
      linarith
    · rw [heq] at hup_lt
      exact lt_irrefl _ hup_lt
  · have h := hfoc t
    have hratio : Pstar t / P t < 1 := (div_lt_one (hP t)).mpr hgt
    have hup_lt : up (c (t + 1)) < up (c t) := by
      have e : β * Pstar t / P t * up (c t) = β * (Pstar t / P t * up (c t)) := by ring
      rw [e] at h
      have h2 := mul_left_cancel₀ hβ.ne' h
      have := hpos t
      nlinarith
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt' | heq
    · have := hup (Set.mem_Ioi.mpr (hc (t + 1))) (Set.mem_Ioi.mpr (hc t)) hlt'
      linarith
    · rw [heq] at hup_lt
      exact lt_irrefl _ hup_lt

/-- Cochrane (2023), §9.5, p. 281 (**Theorem IP**, "then we must have an equilibrium price level
`P_t = P*_t`"): with the indexed-bond peg and market clearing `c_t = y`, the first-order condition
(9.29) holds at every date if and only if `P_t = P*_t` at every date (`u'(y) > 0`): existence and
uniqueness. -/
theorem price_eq_target {β y : ℝ} (hβ : 0 < β) {up : ℝ → ℝ} (hy : 0 < up y) {P Pstar : ℕ → ℝ}
    (hP : ∀ n, 0 < P n) : (∀ n, β * Pstar n / P n * up y = β * up y) ↔ P = Pstar := by
  constructor
  · intro hfoc
    funext n
    have h := hfoc n
    have h2 : Pstar n / P n = 1 := by
      have e : β * Pstar n / P n * up y = (β * up y) * (Pstar n / P n) := by ring
      rw [e] at h
      exact mul_left_cancel₀ (mul_pos hβ hy).ne' (h.trans (mul_one _).symm)
    rw [div_eq_one_iff_eq (hP n).ne'] at h2
    exact h2.symm
  · rintro rfl n
    rw [mul_div_assoc, div_self (hP n).ne', mul_one]

/-- Cochrane (2023), eq. (9.28), p. 281: with market clearing `c_t = y`, the consumer's budget
constraint in (9.29), `y + b_{t−1} = c_t + s_t + q_t b_t`, is the government's flow condition
`b_{t−1} = s_t + q_t b_t`. -/
theorem eq_9_28_of_clearing {y b s q b' c : ℝ} (hc : c = y) (hbud : y + b = c + s + q * b') :
    b = s + q * b' := by
  rw [hc] at hbud
  linarith

/-- Cochrane (2023), eqs. (9.28)–(9.29), p. 282, with log utility (`u'(c) = 1/c`): in a one-period
deviation (`P_{t+j} = P*_{t+j}`, `j ≥ 1`), given the later budget constraints
`y + b_n = c̄ + s_n + β b_{n+1}`, the transversality condition and summable surpluses
`S = ∑ⱼ βʲ s_{t+1+j}`, consumption demand is
`c_t = (1 − β)(y + b_t − s_t) + β (P*_t/P_t)(y − (1 − β) S)` — finite at every price level. -/
theorem log_demand {β y Pt Pst ct cbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hPt : 0 < Pt)
    (hPst : 0 < Pst) {b s : ℕ → ℝ} (t : ℕ)
    (hfoc : β * Pst / Pt * (1 / ct) = β * (1 / cbar)) (hct : 0 < ct)
    (hbud : y + b t = ct + s t + β * Pst / Pt * b (t + 1))
    (hlater : ∀ n, t + 1 ≤ n → y + b n = cbar + s n + β * b (n + 1))
    (htvc : Tendsto (fun T => β ^ T * b (t + 1 + T)) atTop (𝓝 0))
    (hs : Summable (fun j => β ^ j * s (t + 1 + j))) :
    ct = (1 - β) * (y + b t - s t) +
      β * (Pst / Pt) * (y - (1 - β) * ∑' j, β ^ j * s (t + 1 + j)) := by
  have hβne := hβ0.ne'
  -- the forward value of later debt
  have hflow : ∀ n, b (t + 1 + n) = (cbar + s (t + 1 + n) - y) + β * b (t + 1 + n + 1) := by
    intro n
    have := hlater (t + 1 + n) (by omega)
    linarith
  set d : ℕ → ℝ := fun n => b (t + 1 + n) with hd
  set g : ℕ → ℝ := fun n => cbar + s (t + 1 + n) - y with hg
  have hflow' : ∀ n, d n = g n + β * d (n + 1) := by
    intro n
    simp only [hd, hg]
    rw [show t + 1 + (n + 1) = t + 1 + n + 1 by ring]
    exact hflow n
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hsum : Summable (fun j => β ^ j * g (0 + j)) := by
    have := ((hgeo.mul_right (cbar - y)).add hs)
    refine this.congr fun j => ?_
    simp only [hg, zero_add]
    ring
  have hhas := PresentValue.hasSum_of_tvc hflow' 0 (by simpa [hd] using htvc) hsum
  have hval : b (t + 1) = (cbar - y) / (1 - β) + ∑' j, β ^ j * s (t + 1 + j) := by
    have e1 := hhas.tsum_eq
    simp only [hd, hg, add_zero, zero_add] at e1
    rw [← e1]
    have hsplit : (fun j => β ^ j * (cbar + s (t + 1 + j) - y)) =
        fun j => (cbar - y) * β ^ j + β ^ j * s (t + 1 + j) := by
      funext j
      ring
    rw [hsplit, (hgeo.mul_left (cbar - y)).tsum_add hs, tsum_mul_left,
      tsum_geometric_of_lt_one hβ0.le hβ1]
    field_simp
  -- the first-order condition: cbar = ct Pt / Pst
  have hcbar : cbar = ct * Pt / Pst := by
    have hcb : cbar ≠ 0 := by
      intro h0
      rw [h0, div_zero, mul_zero] at hfoc
      have : 0 < β * Pst / Pt * (1 / ct) := by positivity
      linarith
    field_simp at hfoc
    field_simp
    nlinarith [hfoc]
  rw [hval, hcbar] at hbud
  have h1 : (1 - β) ≠ 0 := by linarith
  field_simp at hbud
  field_simp
  linear_combination -hbud

/-- Cochrane (2023), §9.5, p. 282 ("as the price level `P_t` falls, consumption demand `c_t`
rises"):
with log utility the demand of `log_demand` is strictly decreasing in `P_t > 0` when the endowment
exceeds the annuity value of future surpluses, `y > (1 − β) S`. -/
theorem log_demand_strictAntiOn {β y Pst A S : ℝ} (hβ0 : 0 < β) (hPst : 0 < Pst)
    (hS : (1 - β) * S < y) :
    StrictAntiOn (fun Pt => A + β * (Pst / Pt) * (y - (1 - β) * S)) (Set.Ioi 0) := by
  intro P₁ h₁ P₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  simp only [add_lt_add_iff_left]
  have hk : 0 < y - (1 - β) * S := by linarith
  have : Pst / P₂ < Pst / P₁ := div_lt_div_of_pos_left hPst h₁ hlt
  have hb : 0 < β * (y - (1 - β) * S) := mul_pos hβ0 hk
  nlinarith

/-- Cochrane (2023), §9.5, p. 282: with the peg in place (`P = P*`), the flow condition with both
debts, `b_{t−1} + B_{t−1}/P*_t = s_t + β b_t + Q_t B_t/P*_t` with `Q_t = β P*_t/P*_{t+1}`, shows
that
selling more nominal debt `B_t` "simply ends up selling less real debt `b_t`", one-for-one at
`1/P*_{t+1}`. -/
theorem nominal_debt_crowds_out_real {β bprev Bprev s Pst Pst1 b B b' B' : ℝ} (hβ : 0 < β)
    (hPst : 0 < Pst) (hPst1 : 0 < Pst1)
    (h : bprev + Bprev / Pst = s + β * b + (β * Pst / Pst1) * B / Pst)
    (h' : bprev + Bprev / Pst = s + β * b' + (β * Pst / Pst1) * B' / Pst) :
    b' - b = -(B' - B) / Pst1 := by
  have e : ∀ X : ℝ, (β * Pst / Pst1) * X / Pst = β * (X / Pst1) := fun X => by
    field_simp
  rw [e B] at h
  rw [e B'] at h'
  have h2 : β * ((b' - b) + (B' - B) / Pst1) = 0 := by linear_combination h - h'
  have h3 := (mul_eq_zero.mp h2).resolve_left hβ.ne'
  linear_combination h3

/-- Cochrane (2023), §9.5, p. 282 ("suppose the government unexpectedly devalues at time `t`,
raising the price level target `P*_t`"): the real value `B_{t−1}/P*_t` of outstanding nominal debt
falls strictly as the target rises. -/
theorem devaluation_lowers_value {Bprev : ℝ} (hB : 0 < Bprev) :
    StrictAntiOn (fun Pst : ℝ => Bprev / Pst) (Set.Ioi 0) := by
  simpa using MixedDebtRules.value_strictAntiOn (b := 0) hB

/-- Cochrane (2023), §9.5, p. 283: with a fixed nominal bond-price target `Q*`, the real bond price
`1/(1 + r_t) = Q*/P_t` gives `P_t = Q*(1 + r_t)`: real-interest-rate variation is price-level
variation (`P_t/P_s = (1 + r_t)/(1 + r_s)`). -/
theorem price_eq_peg_times_rate {Qs P r : ℕ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hP : ∀ n, 0 < P n) (hr : ∀ n, 0 < 1 + r n) (h : ∀ n, 1 / (1 + r n) = Q / P n)
    (hQs : ∀ n, Qs n = Q) (t s : ℕ) :
    P t = Qs t * (1 + r t) ∧ P t / P s = (1 + r t) / (1 + r s) ∧ (r t ≠ r s → P t ≠ P s) := by
  have hPt : ∀ n, P n = Q * (1 + r n) := by
    intro n
    have := h n
    rw [div_eq_div_iff (hr n).ne' (hP n).ne'] at this
    linarith
  refine ⟨by rw [hQs t, hPt t], ?_, fun hne heq => hne ?_⟩
  · rw [hPt t, hPt s]
    field_simp
  · rw [hPt t, hPt s] at heq
    have := mul_left_cancel₀ hQ.ne' heq
    linarith

/-- Cochrane (2023), §9.5, pp. 283–284 (the five-minute example): for `$200` one buys a claim to
`$250`; reinvesting, `250 · 1.25 = 312.5`; the overnight return is `100 (250/200 − 1) = 25` %. -/
theorem five_minute_example :
    (200 : ℝ) * (5 / 4) = 250 ∧ (250 : ℝ) * (5 / 4) = 312.5 ∧ 100 * ((250 : ℝ) / 200 - 1) = 25 := by
  norm_num

/-- Cochrane (2023), §9.5, p. 284 ("money is exploding"): repeatedly rolling over the pegged claim
multiplies dollars by `5/4` each round, so holdings `200 · (5/4)ⁿ` grow without bound. -/
theorem five_minute_unbounded :
    Tendsto (fun n : ℕ => (200 : ℝ) * (5 / 4) ^ n) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).const_mul_atTop (by norm_num)

set_option exponentiation.threshold 400 in
/-- Cochrane (2023), §9.5, p. 284: a 25% one-day return annualises to
`100 ((250/200)³⁶⁵ − 1) ≈ 2.36 × 10³⁷` %, between `2.3 × 10³⁷` and `2.4 × 10³⁷` (the book's
"`2.3 × 10³⁷` %"; the gross factor itself is `≈ 2.36 × 10³⁵`). -/
theorem annualised_rate :
    (2.3e37 : ℝ) < 100 * (((250 : ℝ) / 200) ^ 365 - 1) ∧
      100 * (((250 : ℝ) / 200) ^ 365 - 1) < 2.4e37 := by
  norm_num

end Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A CPI standard?

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.6
"A CPI standard?", pp. 284–286. The section is mostly verbal; this module formalises its precise
claims.

## Main results

* `commodity_standard_price`: pegging the dollar price `G` of a commodity whose relative price is
  `g_t` gives `P_t = G/g_t`, so variation in the relative price is price-level variation
  (p. 285, "the relative price of gold and everything else varies over time, so the gold
  standard leaves substantial inflation volatility").
* `hasSum_perpetuity`, `perpetuity_rises_more`: a real perpetuity costs `1/r`, a one-year indexed
  bond `1/(1 + r)`; when the real rate falls, the perpetuity's price rises by more (p. 285, "when
the
  real interest-rate declines, long-term real asset prices rise relative to the consumption basket,
  much more so than the price of a one-year indexed bond").
* `indexed_claim_price`, `indexed_peg_pins_price`: the dollar price of a claim to next period's
  basket is `β P_t`, so pegging it ties down today's price level (p. 286).
* `cpi_bet_unbounded`, `cpi_bet_example`: offering `$250` for a CPI-linked bet that pays the CPI
  of `260` today is an arbitrage whose reinvested proceeds grow without bound (p. 286).
-/

namespace Cochrane.AssetsRulesBalanceSheets.CPIStandard

open Filter Topology

/-- Cochrane (2023), §9.6, p. 285: under a commodity (gold) standard the dollar price of the
commodity is pegged at `G` and its relative price is `g_t` goods per unit, so `P_t = G/g_t`;
inflation
is `P_{t+1}/P_t = g_t/g_{t+1}` and any change in the relative price changes the price level. -/
theorem commodity_standard_price {G : ℝ} (hG : 0 < G) {g P : ℕ → ℝ} (hg : ∀ t, 0 < g t)
    (hpeg : ∀ t, P t * g t = G) (t s : ℕ) :
    P t = G / g t ∧ P (t + 1) / P t = g t / g (t + 1) ∧ (g t ≠ g s → P t ≠ P s) := by
  have hP : ∀ n, P n = G / g n := fun n => by
    rw [eq_div_iff (hg n).ne']
    exact hpeg n
  refine ⟨hP t, ?_, fun hne heq => hne ?_⟩
  · rw [hP t, hP (t + 1)]
    field_simp [(hg t).ne', (hg (t + 1)).ne', hG.ne']
  · rw [hP t, hP s] at heq
    rw [div_eq_div_iff (hg t).ne' (hg s).ne'] at heq
    exact (mul_left_cancel₀ hG.ne' heq).symm

/-- Cochrane (2023), §9.6, p. 285: a real perpetuity paying one unit of consumption at every future
date costs `∑_{j≥1} (1 + r)^{−j} = 1/r`. -/
theorem hasSum_perpetuity {r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => (1 / (1 + r)) ^ (j + 1)) (1 / r) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 / (1 + r))
  convert h using 1
  · funext j
    rw [pow_succ]
    ring
  · have hr0 := hr.ne'
    have h1r : 1 + r ≠ 0 := by linarith
    field_simp
    ring_nf
    field_simp

/-- Cochrane (2023), §9.6, p. 285: when the real rate falls from `r₂` to `r₁` (`0 < r₁ < r₂`), the
price of a real perpetuity rises by more than the price of a one-year indexed bond,
`1/r₁ − 1/r₂ > 1/(1 + r₁) − 1/(1 + r₂)`. -/
theorem perpetuity_rises_more {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (hlt : r₁ < r₂) :
    1 / (1 + r₁) - 1 / (1 + r₂) < 1 / r₁ - 1 / r₂ := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  rw [div_sub_div _ _ (by linarith) (by linarith), div_sub_div _ _ h₁.ne' h₂.ne',
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h₁ h₂, mul_pos (mul_pos h₁ h₂) (sub_pos.mpr hlt)]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.6, p. 286 ("the indexed debt peg ties down today's price of next-year's
basket"): with a constant real rate and the pull-out property, a claim paying `$P_{t+1}` (next
period's basket) has dollar price `P_t · β E_t (P_{t+1}/P_{t+1}) = β P_t`. -/
theorem indexed_claim_price {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) = β • P t := by
  have h1 : P (t + 1) / P (t + 1) = fun _ => 1 := by
    funext ω
    exact div_self (hP (t + 1) ω).ne'
  rw [h1, 𝔼.const]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §9.5–§9.6, pp. 281, 286: pegging the dollar price of that claim at `β P*_t`
ties down today's price level, `P_t = P*_t`. -/
theorem indexed_peg_pins_price {β : ℝ} (hβ : 0 < β) {P : ℕ → Ω → ℝ} {Pstar : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (hpeg : P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) =
      β • Pstar t) : P t = Pstar t := by
  rw [indexed_claim_price 𝔼 hP t] at hpeg
  funext ω
  have := congrFun hpeg ω
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hβ.ne' this

/-- Cochrane (2023), §9.6, p. 286 ("if the government offers to trade `$250` for a CPI-linked bet
that
pays off today, and the CPI is `260`, people will trade infinite amounts"): whenever the offer price
`p` is below the index value `v`, reinvesting `W` dollars `n` times yields `W (v/p)ⁿ → ∞`. -/
theorem cpi_bet_unbounded {p v W : ℝ} (hp : 0 < p) (hpv : p < v) (hW : 0 < W) :
    Tendsto (fun n : ℕ => W * (v / p) ^ n) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hp).mpr hpv)).const_mul_atTop hW

/-- Cochrane (2023), §9.6, p. 286: the book's numbers — each round turns `$250` into `$260`, and the
reinvested holdings `250 (260/250)ⁿ` grow without bound. -/
theorem cpi_bet_example :
    (250 : ℝ) * (260 / 250) = 260 ∧
      Tendsto (fun n : ℕ => (250 : ℝ) * (260 / 250) ^ n) atTop atTop :=
  ⟨by norm_num, cpi_bet_unbounded (by norm_num) (by norm_num) (by norm_num)⟩

end Cochrane.AssetsRulesBalanceSheets.CPIStandard

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between Chapters 8, 9 and 10

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapters 8 (pp. 239–258), 9
(pp. 259–286) and 10 (pp. 287–311). The chapters were formalised in two chains: Chapter 8 and
Chapter 10 (`RealDebt` … `BalanceSheets`) and Chapter 9 (`InflationTarget` … `CPIStandard`).
This module proves that the objects the two chains formalise separately are the same objects.

## Main results

* Valuation: `economy_nominalFlow`, `economy_valuation` — the §9.2 economy satisfies the §8.2
  nominal flow condition, so Theorem IT's real debt is the present value (8.2);
  `economy_tvc_iff`, `tvc_perfectForesight_iff` — the transversality conditions of the two
  chains are the same condition.
* Indexed debt: `ruleEquilibrium_iff_indexed` — the §9.3.2 rule equilibrium (ex post) is the
  §8.1 indexed-debt equilibrium under perfect foresight; `indexedFlow_eq_9_9` — under
  uncertainty, the §8.1 indexed flow with the §9.3.2 rule gives (9.9) state by state;
  `rule_97_determines` — (9.7) is an instance of the §8.1 "s(P) can determine P" claim.
* Indexed-debt pegs: `indexedPrice_eq_claimPrice`, `indexed_peg_iff`,
  `indexed_peg_foc_iff_market` — the §8.1 indexed-bond price is the §9.6 claim price, and the
  §9.5 peg holds iff the market price of indexed debt is `β P*_t`.
* Mixed debt: `mixed_existsUnique_iff`, `elasticities_reciprocal` — the §8.3 capital-structure
  price level and the §9.3.5 debt-value elasticity are reciprocal.
* Maturity: `valuation_922_of_short_debt`, `valuation_of_short_debt` — the §9.4.1 valuation
  equation (9.22) is the one-period-debt case (`ω = 0`) of the §8.4 identity.
* Bond prices: `bondPrice_no_haircut`, `revenue_eq_9_27` — the §8.5 bond price without a haircut
  is the §9.4.2 bond price of (9.27).
* Perpetuities: `pv_one_eq_one_add_perpetuity` — the §10.1.3 perpetuity value `1/(1 − β)` is the
  coupon plus the §9.6 ex-coupon value `1/r`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.Links

open Filter Topology PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §9.2 Theorem IT and the (8.2) valuation equation -/

/-- Cochrane (2023), §9.2, p. 263, and eq. (8.2), p. 240: the private-sector equilibrium of the
inflation-target model (`InflationTarget.Economy`: flow condition and bond pricing
`Q_t = β E_t(P_t/P_{t+1})`) satisfies the nominal flow condition `RealDebt.NominalFlow` of §8.2. -/
theorem economy_nominalFlow {β : ℝ} {B P Q s : ℕ → Ω → ℝ}
    (hE : InflationTarget.Economy 𝔼 β B P Q s) : RealDebt.NominalFlow 𝔼 β B P s := by
  intro t
  funext ω
  have h := congrFun (hE.flow t) ω
  have hq := congrFun (hE.pricing t) ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h hq
  have hP := (hE.pos_P t ω).ne'
  rw [map_smul]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hq]
  calc B t ω = B t ω / P t ω * P t ω := by field_simp
    _ = (s t ω + Q t ω * B (t + 1) ω / P t ω) * P t ω := by rw [h]
    _ = P t ω * s t ω + Q t ω * B (t + 1) ω := by rw [add_mul, div_mul_cancel₀ _ hP]; ring

/-- Cochrane (2023), §9.2, p. 264 ("the real value of nominal debt is also the present value of
surpluses") and eq. (8.2), p. 240: in the inflation-target economy with bounded adapted
surpluses, `0 ≤ β < 1` and the pull-out property, `B_t/P_t = E_t ∑ βʲ s_{t+j}` at every date —
the §8.2 valuation equation `RealDebt.nominal_valuation_iff`. -/
theorem economy_valuation (h𝔼 : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B P Q s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hE : InflationTarget.Economy 𝔼 β B P Q s) : ∀ t, B t / P t = pv 𝔼 β s t :=
  (RealDebt.nominal_valuation_iff 𝔼 h𝔼 hβ0 hβ1 hs hsa hE.adapted_P
    (fun t ω => (hE.pos_P t ω).ne') hE.predetermined_B).mp ⟨economy_nominalFlow 𝔼 hE, hE.tvc⟩

/-- Cochrane (2023), §9.2, p. 263, and p. 239: the transversality field of
`InflationTarget.Economy` is the condition `TVC` of `PresentValue` for real debt `B/P`. -/
theorem economy_tvc_iff {β : ℝ} {B P : ℕ → Ω → ℝ} :
    (∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (B (t + T) / P (t + T)) ω) atTop (𝓝 0)) ↔
      TVC 𝔼 β (fun t => B t / P t) :=
  Iff.rfl

/-- Cochrane (2023), §9.3.2, p. 266, and p. 239: under perfect foresight the expected
transversality condition `TVC` is the ex post condition `βᵀ b_{t+T} → 0` used by
`FiscalRules.RuleEquilibrium`. -/
theorem tvc_perfectForesight_iff {β : ℝ} {x : ℕ → Unit → ℝ} :
    TVC perfectForesight β x ↔ ∀ t, Tendsto (fun T => β ^ T * x (t + T) ()) atTop (𝓝 0) :=
  ⟨fun h t => h t (), fun h t _ => h t⟩

/-! ### §8.1 indexed debt and §9.3 fiscal rules -/

/-- Cochrane (2023), §9.3.2, pp. 266–267, and §8.1, p. 239: an ex post equilibrium of the dynamic
fiscal rule with indexed debt (`FiscalRules.RuleEquilibrium`) is exactly a perfect-foresight
equilibrium of the §8.1 indexed-debt flow (`RealDebt.IndexedFlow`) with the rule
`s_t = s_{0,t} + θ (P_t − P*_t)`, positive prices and the transversality condition. -/
theorem ruleEquilibrium_iff_indexed {β θ : ℝ} {s0 Pstar P b : ℕ → ℝ} :
    FiscalRules.RuleEquilibrium β θ s0 Pstar P b ↔ (∀ t, 0 < P t) ∧
      RealDebt.IndexedFlow perfectForesight β (fun t _ => b t)
        (fun t _ => s0 t + θ * (P t - Pstar t)) (fun t _ => P t) ∧
      TVC perfectForesight β (fun t _ => b t) := by
  constructor
  · rintro ⟨hP, hflow, htvc⟩
    exact ⟨hP, (RealDebt.indexedFlow_iff perfectForesight (fun _ => rfl)
      (fun t _ => (hP t).ne')).mpr fun t _ => hflow t, fun t _ => htvc t⟩
  · rintro ⟨hP, hflow, htvc⟩
    exact ⟨hP, fun t => (RealDebt.indexedFlow_iff perfectForesight (fun _ => rfl)
      (fun t _ => (hP t).ne')).mp hflow t (), fun t => htvc t ()⟩

/-- Cochrane (2023), eq. (9.9), p. 266, and §8.1, p. 239: under any expectation system, the §8.1
indexed-debt flow with the surplus rule `s_t = s_{0,t} + θ (P_t − P*_t)` and the ex post
transversality condition give (9.9) in every state,
`b_{t−1} = ∑ βʲ s_{0,t+j} + θ ∑ βʲ (P_{t+j} − P*_{t+j})`. -/
theorem indexedFlow_eq_9_9 {β θ : ℝ} {b s0 P Pstar : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : RealDebt.IndexedFlow 𝔼 β b (fun t => s0 t + θ • (P t - Pstar t)) P) (t : ℕ)
    (ω : Ω) (htvc : Tendsto (fun T => β ^ T * b (t + T) ω) atTop (𝓝 0))
    (hs0 : Summable (fun j => β ^ j * s0 (t + j) ω))
    (hPs : Summable (fun j => β ^ j * (P (t + j) ω - Pstar (t + j) ω))) :
    b t ω = ∑' j, β ^ j * s0 (t + j) ω + θ * ∑' j, β ^ j * (P (t + j) ω - Pstar (t + j) ω) := by
  have h := (RealDebt.indexedFlow_iff 𝔼 hPa hP).mp hflow
  refine FiscalRules.eq_9_9 (b := fun t => b t ω) (s0 := fun t => s0 t ω)
    (P := fun t => P t ω) (Pstar := fun t => Pstar t ω) (fun t => ?_) t htvc hs0 hPs
  have := h t ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
  exact this

/-- Cochrane (2023), eq. (9.7), p. 265, and p. 239 ("surpluses that respond to the price level
can determine it"): for `θ ≠ 0` the rule `s(P) = b + θ (P − P*)` is injective, so the §8.1 claim
`RealDebt.surplus_rule_determines` applies and the one-period valuation `b = s(P)` gives
`P = P*`. -/
theorem rule_97_determines {θ : ℝ} (hθ : θ ≠ 0) {β b Pstar P : ℝ}
    (h : b = (b + θ * (P - Pstar)) + β * 0) : P = Pstar := by
  have hinj : Function.Injective (fun p : ℝ => b + θ * (p - Pstar)) := fun p q hpq => by
    have h1 : θ * (p - q) = 0 := by simp only at hpq; linarith
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact absurd h0 hθ
    · linarith
  exact RealDebt.surplus_rule_determines (σ := fun p : ℝ => b + θ * (p - Pstar)) hinj h
    (by ring)

/-! ### §8.1 indexed debt and the §9.5–§9.6 pegs -/

/-- Cochrane (2023), p. 239 and §9.6, p. 286: the §8.1 nominal price of a one-period indexed
bond, `E_t[β (P_t/P_{t+1}) P_{t+1}]`, is the §9.6 dollar price of a claim to next period's
basket, `P_t β E_t(P_{t+1}/P_{t+1})`; both are `β P_t`. -/
theorem indexedPrice_eq_claimPrice {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    RealDebt.indexedPrice 𝔼 β P t = P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) := by
  rw [RealDebt.indexedPrice_eq 𝔼 hPa (fun t ω => (hP t ω).ne') t,
    CPIStandard.indexed_claim_price 𝔼 hP t]

/-- Cochrane (2023), §9.5, p. 281, and §9.6, p. 286, with the §8.1 bond price of p. 239: a peg
that sells one-period indexed debt at the nominal price `β P*_t` clears the market at date `t`
(the market price `RealDebt.indexedPrice` equals the peg) if and only if `P_t = P*_t`. -/
theorem indexed_peg_iff {β : ℝ} (hβ : 0 < β) {P Pstar : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    RealDebt.indexedPrice 𝔼 β P t = β • Pstar t ↔ P t = Pstar t := by
  rw [indexedPrice_eq_claimPrice 𝔼 hPa hP t]
  constructor
  · exact CPIStandard.indexed_peg_pins_price 𝔼 hβ hP t
  · intro h
    rw [CPIStandard.indexed_claim_price 𝔼 hP t, h]

/-- Cochrane (2023), §9.5, pp. 281–282, and p. 239: in the endowment economy (`c = y`) the
consumer's first-order condition at the indexed-debt peg holds at every date iff the §8.1
market price of indexed debt equals the peg `β P*_t` at every date (both iff `P = P*`). -/
theorem indexed_peg_foc_iff_market {β y : ℝ} (hβ : 0 < β) {up : ℝ → ℝ} (hy : 0 < up y)
    {P Pstar : ℕ → Unit → ℝ} (hP : ∀ t ω, 0 < P t ω) :
    (∀ n, β * Pstar n () / P n () * up y = β * up y) ↔
      ∀ t, RealDebt.indexedPrice perfectForesight β P t = β • Pstar t := by
  have hfoc := IndexedDebtPeg.price_eq_target (P := fun n => P n ()) (Pstar := fun n => Pstar n ())
    hβ hy (fun n => hP n ())
  rw [hfoc]
  simp only [indexed_peg_iff perfectForesight hβ (fun _ => rfl) hP]
  constructor
  · intro h t
    funext ω
    exact congrFun h t
  · intro h
    funext n
    exact congrFun (h n) ()

/-! ### §8.3 capital structure and §9.3.5 mixed debt rules -/

/-- Cochrane (2023), eq. (8.3), p. 246, and §9.3.5, p. 271: with nominal debt `B > 0` and real
debt `b`, the one-period valuation `b + B/P = V` (a constant surplus in §9.3.5) has a unique
positive price level iff `b < V` (`CapitalStructure.mixed_price_unique`,
`CapitalStructure.mixed_no_price`; uniqueness alone is `MixedDebtRules.price_unique_const`). -/
theorem mixed_existsUnique_iff {b B V : ℝ} (hB : 0 < B) :
    (∃! P : ℝ, 0 < P ∧ b + B / P = V) ↔ b < V := by
  constructor
  · intro h
    by_contra hbV
    exact CapitalStructure.mixed_no_price hB (not_lt.mp hbV) h.exists
  · exact CapitalStructure.mixed_price_unique hB

/-- Cochrane (2023), p. 246 (§8.3: more real debt makes the price level more volatile) and
§9.3.5, p. 271 (the debt value has elasticity minus the nominal share): at
`V = b + B/P`, the elasticity of `P` with respect to `V` from (8.3), `−V/(V − b)`, and the
elasticity of the debt value with respect to `P`, `P v'(P)/v(P)`, are reciprocal. -/
theorem elasticities_reciprocal {b B P : ℝ} (hB : 0 < B) (hP : 0 < P) (hV : 0 < b + B / P) :
    HasDerivAt (fun u => Real.log (B / (Real.exp u - b)))
        (-((b + B / P) / (b + B / P - b))) (Real.log (b + B / P)) ∧
      HasDerivAt (fun P => b + B / P) (-(B / P ^ 2)) P ∧
      -((b + B / P) / (b + B / P - b)) * (P * (-(B / P ^ 2)) / (b + B / P)) = 1 := by
  have hBP : 0 < B / P := div_pos hB hP
  refine ⟨CapitalStructure.log_price_elasticity hB hV (by linarith),
    MixedDebtRules.hasDerivAt_value b B hP.ne', ?_⟩
  have hV0 := hV.ne'
  have hP0 := hP.ne'
  have hB0 := hB.ne'
  have hbp : b * P + B ≠ 0 := by
    rw [show b * P + B = (b + B / P) * P by rw [add_mul, div_mul_cancel₀ _ hP0]]
    exact mul_ne_zero hV0 hP0
  rw [show b + B / P - b = B / P by ring]
  field_simp

/-! ### §8.4 maturity and the §9.4.1 valuation equation -/

/-- Cochrane (2023), eq. (8.4), p. 250 (`ω = 0`, short-term debt) and eq. (9.22), p. 275: if the
news in inflation, surpluses and real returns at `(t, ω)` satisfy the identities (3.20)–(3.21)
of §8.4 with one-period debt, the surplus news `∑ ρʲ ΔE s` is the fiscal shock `ε_{t+1}` and the
real-return news is `ΔE(i_{t+j} − π_{t+1+j})`, then the §9.4.1 valuation equation (9.22) holds
at `(t, ω)`. -/
theorem valuation_922_of_short_debt {ρ rn : ℝ} {πN sN rN : ℕ → ℝ} {π i ε : ℕ → Ω → ℝ}
    {t : ℕ} {ω : Ω} (h320 : MaturityBuffer.Identity320 ρ πN sN rN rn)
    (h321 : MaturityBuffer.Identity321 0 πN rN rn)
    (hπ : πN 0 = SpreadTarget.innov 𝔼 t (π (t + 1)) ω) (hε : ∑' j, ρ ^ j * sN j = ε (t + 1) ω)
    (hr : ∀ j, rN (j + 1) = SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) :
    SpreadTarget.innov 𝔼 t (π (t + 1)) ω = (-ε (t + 1) + fun ω =>
      ∑' j, ρ ^ (j + 1) * SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) ω := by
  have h := MaturityBuffer.short_debt_identity h320 h321
  rw [hπ, hε] at h
  rw [h]
  simp only [Pi.add_apply, Pi.neg_apply]
  congr 1
  exact tsum_congr fun j => by rw [hr j]

/-- Cochrane (2023), eq. (8.4), p. 250, and eq. (9.22), p. 275: if at every date and state the
news satisfies the §8.4 identities with one-period debt (`ω = 0`) as in
`valuation_922_of_short_debt`, then `SpreadTarget.Valuation` holds: (9.22) is the short-debt
case of (8.4). -/
theorem valuation_of_short_debt {ρ : ℝ} {π i ε : ℕ → Ω → ℝ}
    (h : ∀ t ω, ∃ (πN sN rN : ℕ → ℝ) (rn : ℝ), MaturityBuffer.Identity320 ρ πN sN rN rn ∧
      MaturityBuffer.Identity321 0 πN rN rn ∧ πN 0 = SpreadTarget.innov 𝔼 t (π (t + 1)) ω ∧
      ∑' j, ρ ^ j * sN j = ε (t + 1) ω ∧
      ∀ j, rN (j + 1) = SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) :
    SpreadTarget.Valuation 𝔼 ρ π i ε := by
  intro t
  funext ω
  obtain ⟨πN, sN, rN, rn, h320, h321, hπ, hε, hr⟩ := h t ω
  exact valuation_922_of_short_debt 𝔼 h320 h321 hπ hε hr

/-! ### §8.5 bond prices and (9.27) -/

/-- Cochrane (2023), eq. (8.7), p. 254, and eq. (9.27), p. 279: without a haircut (`D ≡ 1`) the
§8.5 bond price `Q_t = β E_t(P_t D_{t+1}/P_{t+1})` is the §9.4.2 bond price
`β E_t(P_t/P_{t+1})`. -/
theorem bondPrice_no_haircut (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Default.bondPrice 𝔼 β P (fun _ _ => 1) t = β • 𝔼.E t (P t / P (t + 1)) := by
  unfold Default.bondPrice
  congr 2
  funext ω
  simp only [Pi.div_apply, Pi.mul_apply, mul_one]

/-- Cochrane (2023), eq. (8.6), p. 254, and eq. (9.27), p. 279: with no haircut, the revenue
from selling `B_t` at the §8.5 bond price is the (9.27) expression `β B_t E_t(1/P_{t+1})`. -/
theorem revenue_eq_9_27 (h𝔼 : 𝔼.PullOut) {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (B : ℕ → Ω → ℝ) (t : ℕ) :
    Default.bondPrice 𝔼 β P (fun _ _ => 1) t * B t / P t =
      β • (B t * 𝔼.E t (fun ω => 1 / P (t + 1) ω)) :=
  SpreadSwap.eq_9_27 𝔼 h𝔼 (Q := fun t => Default.bondPrice 𝔼 β P (fun _ _ => 1) t) hP hPa
    (fun t => bondPrice_no_haircut 𝔼 β P t) t

/-! ### §10.1.3 perpetuities and §9.6 -/

/-- Cochrane (2023), eq. (10.7), p. 296, and §9.6, p. 285: with `β = 1/(1 + r)`, the §10.1.3
value of a perpetuity including today's coupon, `E_t ∑ βʲ = 1/(1 − β)`, is the coupon plus the
§9.6 ex-coupon value `∑_{j ≥ 1} (1 + r)^{−j} = 1/r`. -/
theorem pv_one_eq_one_add_perpetuity {r : ℝ} (hr : 0 < r) (t : ℕ) :
    pv 𝔼 (1 / (1 + r)) (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t =
      fun _ => 1 + ∑' j : ℕ, (1 / (1 + r)) ^ (j + 1) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  rw [SharesAsMoney.pv_one 𝔼 hq0 hq1 t, (CPIStandard.hasSum_perpetuity hr).tsum_eq,
    SharesAsMoney.one_sub_beta_inv hr]
  funext _
  field_simp
  ring

end Cochrane.AssetsRulesBalanceSheets.Links

set_option linter.style.longLine false
#print axioms Cochrane.AssetsRulesBalanceSheets.SchurStable
#print axioms Cochrane.AssetsRulesBalanceSheets.disc
#print axioms Cochrane.AssetsRulesBalanceSheets.root₁
#print axioms Cochrane.AssetsRulesBalanceSheets.root₂
#print axioms Cochrane.AssetsRulesBalanceSheets.root_sum
#print axioms Cochrane.AssetsRulesBalanceSheets.root_prod
#print axioms Cochrane.AssetsRulesBalanceSheets.root_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.normSq_root_of_neg
#print axioms Cochrane.AssetsRulesBalanceSheets.norm_root_of_nonneg
#print axioms Cochrane.AssetsRulesBalanceSheets.schurStable_iff_roots
#print axioms Cochrane.AssetsRulesBalanceSheets.chSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.convSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.convSeq_rec
#print axioms Cochrane.AssetsRulesBalanceSheets.chSeq_eq_convSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.norm_convSeq_le
#print axioms Cochrane.AssetsRulesBalanceSheets.abs_chSeq_le
#print axioms Cochrane.AssetsRulesBalanceSheets.tendsto_chSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.tr2
#print axioms Cochrane.AssetsRulesBalanceSheets.det2
#print axioms Cochrane.AssetsRulesBalanceSheets.tr2_eq_trace
#print axioms Cochrane.AssetsRulesBalanceSheets.det2_eq_det
#print axioms Cochrane.AssetsRulesBalanceSheets.sq_eq_cayleyHamilton
#print axioms Cochrane.AssetsRulesBalanceSheets.pow_succ_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.abs_pow_entry_le
#print axioms Cochrane.AssetsRulesBalanceSheets.tendsto_pow_entry
#print axioms Cochrane.AssetsRulesBalanceSheets.BoundedSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.homogeneous_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.abs_mulVec_le
#print axioms Cochrane.AssetsRulesBalanceSheets.homogeneous_eq_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.eq_root_of_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.exists_eigenvector
#print axioms Cochrane.AssetsRulesBalanceSheets.exists_bounded_homogeneous
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.mk
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.E
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.const
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.mono
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.tower
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.known
#print axioms Cochrane.AssetsRulesBalanceSheets.perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.BoundedProc
#print axioms Cochrane.AssetsRulesBalanceSheets.BoundedVec
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.Adapted
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.IsAR1
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.E_neg
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.E_smul
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.E_E_self
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.abs_E_le
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.bounded_E
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.ar1_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forward_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forward_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.E_tsum
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forwardSeries
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.PullOut
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.Solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.AdaptedVec
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.system_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.system_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.system_not_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.Determinate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationSystem.determinate_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.perfectForesight_pullOut
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.Solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.E_of_known
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.solves_adapted
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.iterate_A15
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.summable_A16
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.ScalarEq
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalarSol
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalarSol_apply
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalarEq_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalar_homog
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sunspotFamily
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.homog_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.solves_add_homog
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.existsUnique_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.ar1_decay
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.predetermined_restriction
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.summable_geom_mul
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.abel_tsum
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.ForwardSolution.E_tsum_dom
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.epv
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.pv
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.pv_eq_forwardSeries
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.pv_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.TVC
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.tvc_of_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.tendsto_partialSums_of_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.eq_forwardSeries_of_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.flow_tvc_iff_pv
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.eq_zero_of_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.real_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.real_flow_tvc_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.hasSum_of_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.summable_of_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.valuation_price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.PresentValue.price_unique_of_strictMonoOn
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexedPrice
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexedPrice_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexed_real_value
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.IndexedFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexedFlow_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexedFlow_price_free
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexed_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexed_valuation_tsum
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.indexed_pv_news_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.cashFlow_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.surplus_rule_determines
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.nominalIssue_flow_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.realOutstanding_price_free
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.nominalOutstanding_price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.NominalFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.nominalFlow_iff_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.nominal_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.haircut_of_fixed_price
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.foreign_default_required
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.reserves_price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.reserves_through_sum
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.gold_deflation_raises_pv
#print axioms Cochrane.AssetsRulesBalanceSheets.RealDebt.gold_devaluation
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.MixedFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.mixedFlow_iff_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.mixed_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.mixed_price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.mixed_no_price
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.mixed_zero_nominal
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.log_price_hasDerivAt
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.log_price_elasticity
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.elasticity_gt_one_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.elasticity_strictMono
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.price_ratio
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.log_price_spread_strictMono
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.default_prob_mono
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.cashless_sequence_determinate
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.cashless_sequence_price
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.cashless_nominal_vanishes
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.cashless_elasticity_explodes
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.cashless_limit_indeterminate
#print axioms Cochrane.AssetsRulesBalanceSheets.CapitalStructure.pennies_inflation
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.Identity320
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.Identity321
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.identity_84
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.short_debt_identity
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.short_debt_constant_rates
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.matched_maturity_identity
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.rate_weights_antitone
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.cdisc
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.matching_cancels
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.price_insulated
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.ddisc
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.ddisc_const
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.ddisc_bump
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.matching_necessary
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.price_insulated_only_if_matching
#print axioms Cochrane.AssetsRulesBalanceSheets.MaturityBuffer.matching_fails_under_uncertainty
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.haircut_price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.haircut_offsets_shock
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.bondPrice
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.DefaultFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.revenue_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.defaultFlow_iff_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.default_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.default_flow_pv
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.expected_default_no_effect
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.bondPrice_known_haircut
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.bondPrice_scale
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.scaled_flow_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.two_bonds_half_haircut
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.fixedQ_perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.fixedQ_next_price_mono
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.haircut_ten_percent
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.haircut_factor_eq_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.haircut_factor_lt
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.money_value_ten_percent_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Default.rate_follows_premium
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.cb_purchase_neutral
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.cashLeft
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.cash_left_pos_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.cash_left_zero_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.unified_inflates
#print axioms Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence.independence_default_vs_inflation
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pot_unique_of_strictMono
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pot_exists_of_continuous
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pot_nominal_assets
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.share_split
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.qhat
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.qhat_recursion
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pv_eq_sh_add_qhat
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.PotFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.potX
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.potX_eq_pv_form
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.beta_E_potX
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.potFlow_iff_X
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pot_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.pot_valuation_pv
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.eq_10_5_eq_10_4
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.purchases_irrelevant
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.purchases_matched
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.sell_profit_pos_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.buy_profit_pos_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.no_arbitrage_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.discounted_wealth_const
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.wealth_tvc_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.wealth_noPonzi_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.wealth_explodes_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.wealth_explodes_neg
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.real_bills_real_asset
#print axioms Cochrane.AssetsRulesBalanceSheets.PotOfAssets.real_bills_nominal_asset
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.ShareFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.shareFlow_iff_solves
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.pv_smul
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.share_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.potato_price_level
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.pv_one
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.perpetuity_real_value
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.one_sub_beta_inv
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.perpetuity_price_level
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.perpetuity_price_level_process
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.printed_reciprocal
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.printed_eq_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.printed_counterexample
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.price_level_one_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.potato_perpetuity_unit
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.pv_sub_const
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.perpetuity_backing_bound
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.oneperiod_real_value
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.oneperiod_price_level
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.printed_beta_wrong
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.numeraire_one_plus_y
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.bond_value_le
#print axioms Cochrane.AssetsRulesBalanceSheets.SharesAsMoney.bond_value_no_default
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.consolidated_of_separate
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.treasury_iff_consolidated
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.contingent_transfers_unite
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.nominal_cb_cannot_determine
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.real_cb_determines
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.walled_off_insulated
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.topping_up_lowers_price
#print axioms Cochrane.AssetsRulesBalanceSheets.BalanceSheets.asset_volatility_passes_through
#print axioms Cochrane.AssetsRulesBalanceSheets.ExchangeRates.separate_pools_determinate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExchangeRates.separate_pools_exchange_rate
#print axioms Cochrane.AssetsRulesBalanceSheets.ExchangeRates.exchange_rate_eq_ratio_pv
#print axioms Cochrane.AssetsRulesBalanceSheets.ExchangeRates.common_pool_exchange_rate_free
#print axioms Cochrane.AssetsRulesBalanceSheets.ExchangeRates.common_pool_indeterminate
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.abs_le_of_contraction
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.tendsto_zero_of_contraction
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.summable_of_contraction
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.known_mul
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.known_inv
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.known_div
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.StateInit
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.StateRec
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.SurplusRule
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.RateTarget
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.mk
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.pos_P
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.pos_Q
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.adapted_P
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.adapted_Q
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.known_B0
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.predetermined_B
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.flow
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.pricing
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.Economy.tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.eq_9_3
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.state_adapted
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.eq_9_6
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.eq_9_6_rule
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.state_forecast_succ
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.tendsto_state_forecast
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.state_forecast_of_s0_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.tendsto_state_forecast_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.tendsto_state_forecast_alpha_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.hasSum_state
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.realDebt_rec
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.realDebt_eq_state
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.price_eq_target
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.realDebt_hasSum
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.price_eq_target_perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.exists_equilibrium
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.witnessState
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.target_alone_insufficient
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.ruleState
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.rule_alone_insufficient
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.coinPrice
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.coin_first_known
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.coinPrice_known
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.coinPrice_E0_inv
#print axioms Cochrane.AssetsRulesBalanceSheets.InflationTarget.zero_debt_sunspot
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.existsUnique_price
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.eq_9_7_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.eq_9_9
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.RuleEquilibrium
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.tsum_shift
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.abs_tsum_le
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.hyperplane_equilibrium
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.hyperplaneShift
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.hasSum_hyperplaneShift
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.not_determined_by_valuation
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.price_eq_target_of_debtRule
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.money_pos_of_below
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.money_neg_of_above
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.fr_perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.fr_exists
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.no_innovation_weighted_sum
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.inv_ge_tangent
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.jensen_inv
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.fr_martingale
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.fr_jensen
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.unique_of_ratio_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.value_bounds
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.fr_unique_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.coefL
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.coefK
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contPrice
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.settlePrice
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.settleProb
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contProb
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.condE
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.price
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.nodeValue
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.debt
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.surplus
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value_rec
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.coefK_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.coefL_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value_pos
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value_le
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contPrice_lt_settlePrice
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.settleProb_bounds
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.martingale_inv
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contProb_succ'
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contProb_bounds
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.condE_succ
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.condE_affine
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.condE_const
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.condE_nonneg
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.geom_identity
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.value_finite
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.remainder_tendsto
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.hasSum_value
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.valuation_cont
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.valuation_settled
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.flow_cont
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.flow_settled
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.rate_target_cont
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.rate_target_settled
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.tvc_cont
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.tvc_settled
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.settlePrice_unbounded
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contPrice_tendsto_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.contProb_tendsto_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.pathNode
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.valuation_expost
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.Sunspot.sunspot_counterexample
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.regular_solve
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.regular_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.regular_hasSum
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.emergency_hasSum
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.emergency_debt_target
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.lagged_tvc
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.lagged_tvc_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.lagged_hasSum
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalRules.total_hasSum
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.coefSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.coefSeq_closed
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.abs_coefSeq_le
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.summable_coefSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.tsum_coefSeq
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.tsum_theta
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.eq_9_15
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.E_pi_iterate
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.eq_9_16
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.pi_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.pi_determined
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.pi_not_determined_without_surplus_response
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.rate_rule_essential
#print axioms Cochrane.AssetsRulesBalanceSheets.FiscalTaylor.eq_theta_i_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.value_strictAntiOn
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.price_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.price_unique_const
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.multiplicity_needs_decreasing
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.multiplicity_example
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.hasDerivAt_value
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.elasticity_value
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.ten_percent_rise
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.ten_percent_fall
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.shock_decomposition
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.devaluationShare
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.devaluationShare_strictAnti
#print axioms Cochrane.AssetsRulesBalanceSheets.MixedDebtRules.devaluation_part
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.taylor_spread_equiv
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.swap_rate
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.mk
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.adapted_pi
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.is_9_17
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.is_9_18
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.is_9_19
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.SimpleModel.is_9_20
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.r_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.eq_9_21_mul
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.lam
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.eq_9_21
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.lam_bounds
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.lam_sub_one
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.E_pi_iter
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.indeterminate_without_valuation
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.innov
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.innov_pi_iter
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.innov_return
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.Valuation
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.coefD
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.valuation_sum
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.unexpected_inflation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.eq_9_23
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.pi_succ
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.unique_solution
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.solPi
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.exists_solution
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.solution_bounded
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.theta_zero
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.theta_one
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.theta_one_paths
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.footnote_r
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.tendsto_coef_theta_one
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.FullNK
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.FullNK.mk
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.FullNK.is_9_24
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.FullNK.is_9_25
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.FullNK.spread
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.x_formula
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.innov_eq
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.r_formula
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.printed_minus_corrected
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.printed_9_26_fails_perfectForesight
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.coinPi
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.printed_9_26_fails_coin
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadTarget.holden_unique
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.eq_9_27
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.end_of_period_valuation
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.market_price_irrelevant
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.eSwap
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.swap_valuation_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.eSwap_sub_target
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.hasDerivAt_eSwap
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.gap_const
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.swap_reaches_target_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.real_debt_exhausted
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.eSwap_strictAntiOn
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.eSwap_gt_target
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.numeric_example
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.swap_invariant
#print axioms Cochrane.AssetsRulesBalanceSheets.SpreadSwap.passive_supply
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.real_rate_low_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.marginal_utility_strictAntiOn
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.one_period_deviation
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.price_eq_target
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.eq_9_28_of_clearing
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.log_demand
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.log_demand_strictAntiOn
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.nominal_debt_crowds_out_real
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.devaluation_lowers_value
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.price_eq_peg_times_rate
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.five_minute_example
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.five_minute_unbounded
#print axioms Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg.annualised_rate
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.commodity_standard_price
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.hasSum_perpetuity
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.perpetuity_rises_more
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.indexed_claim_price
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.indexed_peg_pins_price
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.cpi_bet_unbounded
#print axioms Cochrane.AssetsRulesBalanceSheets.CPIStandard.cpi_bet_example
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.economy_nominalFlow
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.economy_valuation
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.economy_tvc_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.tvc_perfectForesight_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.ruleEquilibrium_iff_indexed
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.indexedFlow_eq_9_9
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.rule_97_determines
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.indexedPrice_eq_claimPrice
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.indexed_peg_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.indexed_peg_foc_iff_market
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.mixed_existsUnique_iff
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.elasticities_reciprocal
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.valuation_922_of_short_debt
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.valuation_of_short_debt
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.bondPrice_no_haircut
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.revenue_eq_9_27
#print axioms Cochrane.AssetsRulesBalanceSheets.Links.pv_one_eq_one_add_perpetuity
