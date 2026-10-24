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
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
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

namespace Cochrane.IntertemporalModel

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

end Cochrane.IntertemporalModel

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

namespace Cochrane.IntertemporalModel

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

end Cochrane.IntertemporalModel

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

namespace Cochrane.IntertemporalModel.ExpectationsFiniteTree

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

end Cochrane.IntertemporalModel.ExpectationsFiniteTree

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

namespace Cochrane.IntertemporalModel.ForwardSolution

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

end Cochrane.IntertemporalModel.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Shared expectation tools for Chapter 2

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1 (p. 22), §2.4 (p. 30)
and §2.5 (p. 35): the general facts about the abstract expectation operators `E_t` that the
Chapter 2 modules share. Each fact is stated once here.

## Main results

* The innovation operator `innov` (the book's `ΔE_{t+1} = E_{t+1} − E_t`, p. 30) and its
  algebra: `innov_add`, `innov_sub`, `innov_smul`, `innov_neg`, `innov_const`,
  `innov_of_known`, `E_innov_zero` and `E_innov_zero_of_le` ("you can't expect future unexpected
  shocks"), `innov_known_next`, `innov_E_succ`, `innov_mul_known`, `eq_E_add_innov`.
* Known variables: with the pull-out property, products, reciprocals and quotients of date-`t`
  variables are known at `t` (`E_mul_known`, `E_inv_known`, `E_div_known`, `E_one_add_known`).
  `FunctionsKnown` (functions of known variables are known) and `Closed` (functions of two known
  variables are known, restated from the Woodford Chapter 2 project) are hypotheses, like
  `PullOut`, true for perfect foresight and for every finite event tree; `Closed` implies
  `FunctionsKnown` (`functionsKnown_of_closed`). `known_div` needs no nonvanishing denominator.
* Conditional monotone convergence `MonotoneConvergence` (restated from the Woodford Chapter 2
  project), with its two instances; `const_le_E`, `E_nonneg`, `abs_E_le_E_abs`;
  `summable_E_shift` (discounted forecasts of bounded surpluses are summable).
-/

namespace Cochrane.IntertemporalModel.ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Innovations `ΔE_{t+1} = E_{t+1} − E_t` -/

/-- Cochrane (2023), §2.4, p. 30 (notation `ΔE_{t+1} ≡ E_{t+1} − E_t`): the innovation of `x`
between dates `t` and `t + 1`. -/
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

/-- Cochrane (2023), p. 30 ("you can't expect future unexpected shocks"):
`E_t(ΔE_{t+1} x) = 0`. -/
theorem E_innov_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  unfold innov
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), p. 30: an earlier expectation of a later innovation is zero,
`E_s(ΔE_{t+1} x) = 0` for `s ≤ t` (no future innovation is forecastable). -/
theorem E_innov_zero_of_le {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : 𝔼.E s (innov 𝔼 t x) = 0 := by
  rw [← 𝔼.tower hst, E_innov_zero, map_zero]

/-- Cochrane (2023), p. 30: the date-`t + 1` innovation is known at date `t + 1`. -/
theorem innov_known_next (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  unfold innov
  rw [map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), p. 30: the innovation of `E_{t+1} x` is the innovation of `x`. -/
theorem innov_E_succ (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (𝔼.E (t + 1) x) = innov 𝔼 t x := by
  unfold innov
  rw [𝔼.E_E_self, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 30 (pull-out, used for (2.13)): a factor known at date `t` comes out of
the innovation, `ΔE_{t+1}(a y) = a ΔE_{t+1} y`. -/
theorem innov_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (y : Ω → ℝ) : innov 𝔼 t (a * y) = a * innov 𝔼 t y := by
  unfold innov
  rw [hPO (t + 1) a y (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ha), hPO t a y ha, mul_sub]

/-- Cochrane (2023), p. 30 and p. 35 ("Using `π_{t+1} = E_t π_{t+1} + ΔE_{t+1} π_{t+1}`"): any
random variable known at `t + 1` is its forecast plus its innovation. -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    x = 𝔼.E t x + innov 𝔼 t x := by
  unfold innov
  rw [hx]
  abel

/-! ### Known variables -/

/-- Cochrane (2023), p. 22 (the price level is known at `t`): with the pull-out property,
products of date-`t` variables are known at `t`. -/
theorem E_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hPO t a b ha, hb]

/-- Cochrane (2023), p. 22: with the pull-out property, the reciprocal of a nonvanishing
date-`t` variable is known at `t` (the abstract `ExpectationSystem` axioms alone do not give
this). -/
theorem E_inv_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (ha0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω; simp [ha0 ω]
  have h2 := hPO t a a⁻¹ ha
  rw [h1, 𝔼.const] at h2
  funext ω
  have h3 := congrFun h2 ω
  simp only [Pi.mul_apply] at h3
  simp only [Pi.inv_apply]
  field_simp [ha0 ω]
  linarith

/-- Cochrane (2023), p. 22: with the pull-out property, quotients of date-`t` variables (with
nonvanishing denominator) are known at `t`. -/
theorem E_div_known (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (hb0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv]
  exact E_mul_known 𝔼 hPO ha (E_inv_known 𝔼 hPO hb hb0)

/-- Cochrane (2023), (2.3), p. 22: the gross rate `1 + i` is known when `i` is. -/
theorem E_one_add_known {t : ℕ} {i : Ω → ℝ} (hi : 𝔼.E t i = i) : 𝔼.E t (1 + i) = 1 + i := by
  rw [map_add, hi]
  congr 1
  exact 𝔼.const t 1

/-- Cochrane (2023), p. 22 ("Debt `B_{t−1}` is predetermined at time `t`" and the price level is
a date-`t` variable): every function of a variable known at `t` is known at `t`. True for genuine
conditional expectations and for the two instances (`perfectForesight_functionsKnown`,
`finiteTree_functionsKnown`), but not implied by the `ExpectationSystem` axioms, so it is a
hypothesis where it is used (like `PullOut`). -/
def FunctionsKnown : Prop :=
  ∀ t (x : Ω → ℝ) (f : ℝ → ℝ), 𝔼.E t x = x → 𝔼.E t (fun ω => f (x ω)) = fun ω => f (x ω)

/-- Cochrane (2023), p. 22: under perfect foresight every variable is known. -/
theorem perfectForesight_functionsKnown : FunctionsKnown perfectForesight :=
  fun _ _ _ _ => rfl

/-- Cochrane (2023), p. 22: on a finite event tree a function of a variable that is constant on
date-`t` information cells is again constant on them, hence known at `t`. -/
theorem finiteTree_functionsKnown {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : FunctionsKnown T.toExpectationSystem := by
  intro t x f hx
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hx ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have : x ω' = x ω := by rw [← hx, T.condE_congr x h]
  rw [this]

/-- Cochrane (2023), p. 22: with pull-out and `FunctionsKnown`, the quotient `a/b` of two
variables known at `t` is known at `t` (no nonvanishing hypothesis, unlike `E_div_known`). -/
theorem known_div (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a) (hb : 𝔼.E t b = b) :
    𝔼.E t (fun ω => a ω / b ω) = fun ω => a ω / b ω := by
  have hsplit : (fun ω => a ω / b ω) = a * fun ω => (b ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ ha, hFK t b (fun r => r⁻¹) hb]

/-- Woodford (2003), App. A, §A.6, p. 639 (restated from the Woodford Chapter 2 project): a
function of two date-`t` known variables is known at date `t`. Used for Cochrane (2023), p. 33. -/
def Closed : Prop :=
  ∀ t (f : ℝ → ℝ → ℝ) (x y : Ω → ℝ), 𝔼.E t x = x → 𝔼.E t y = y →
    𝔼.E t (fun ω => f (x ω) (y ω)) = fun ω => f (x ω) (y ω)

/-- Woodford (2003), §A.6 (restated from the Woodford Chapter 2 project): perfect foresight has
the closure property. Used for Cochrane (2023), p. 33. -/
theorem perfectForesight_closed : Closed perfectForesight := fun _ _ _ _ _ _ => rfl

/-- Woodford (2003), §A.6 (restated from the Woodford Chapter 2 project): every finite event tree
has the closure property. Used for Cochrane (2023), p. 33. -/
theorem finiteTree_closed {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    Closed T.toExpectationSystem := by
  intro t f x y hx hy
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hx hy ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have hx' : x ω' = x ω := by
    rw [← hx]
    exact T.condE_congr x h
  have hy' : y ω' = y ω := by
    rw [← hy]
    exact T.condE_congr y h
  simp only [hx', hy']

/-- Cochrane (2023), p. 22 and p. 33: the two-variable closure property `Closed` (used for the
Chapter 2 links to Woodford) implies the one-variable `FunctionsKnown` (used for the
equilibrium price level `P_t = B_{t−1}/pv_t`). -/
theorem functionsKnown_of_closed (hC : Closed 𝔼) : FunctionsKnown 𝔼 :=
  fun t x f hx => hC t (fun a _ => f a) x x hx hx

/-! ### Conditional monotone convergence and order facts -/

/-- Cochrane (2023), p. 22 ("we can then iterate (2.5) to (2.7)"): the interchange of `E_t` and
infinite sums, as the conditional monotone convergence theorem for nonnegative summands.
Restated from the Woodford Chapter 2 project (`AssetPricing.MonotoneConvergence`). -/
def MonotoneConvergence : Prop :=
  ∀ t (f : ℕ → Ω → ℝ), (∀ k ω, 0 ≤ f k ω) → (∀ ω, Summable fun k => f k ω) →
    ∀ ω, HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω)

/-- Cochrane (2023), p. 22: perfect foresight satisfies conditional monotone convergence
(restated from the Woodford Chapter 2 project). -/
theorem perfectForesight_monotoneConvergence : MonotoneConvergence perfectForesight :=
  fun _ _ _ hs ω => (hs ω).hasSum

/-- Cochrane (2023), p. 22: every finite event tree satisfies conditional monotone convergence,
so (2.7) is not restricted to perfect foresight (restated from the Woodford Chapter 2
project). -/
theorem finiteTree_monotoneConvergence {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : MonotoneConvergence T.toExpectationSystem := by
  classical
  intro t f _ hs ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  split_ifs
  · exact (hs ω').hasSum.mul_left _
  · exact hasSum_zero

/-- Cochrane (2023), pp. 22 and 31: a constant lower bound passes through `E_t`: if `c ≤ x` in
every state then `c ≤ E_t x`. -/
theorem const_le_E {c : ℝ} {x : Ω → ℝ} (hx : ∀ ω, c ≤ x ω) (t : ℕ) (ω : Ω) :
    c ≤ 𝔼.E t x ω := by
  have h := 𝔼.mono t (x := fun _ => c) (y := x) hx ω
  rwa [𝔼.const] at h

/-- Cochrane (2023), p. 22: expectations of nonnegative variables are nonnegative. -/
theorem E_nonneg {t : ℕ} {x : Ω → ℝ} (hx : ∀ ω, 0 ≤ x ω) (ω : Ω) : 0 ≤ 𝔼.E t x ω :=
  const_le_E 𝔼 hx t ω

/-- Cochrane (2023), p. 22 (signed surpluses): `|E_t x| ≤ E_t|x|`. -/
theorem abs_E_le_E_abs (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    |𝔼.E t x ω| ≤ 𝔼.E t (fun ω' => |x ω'|) ω := by
  have h1 := 𝔼.mono t (show x ≤ fun ω' => |x ω'| from fun ω' => le_abs_self _) ω
  have h2 := 𝔼.mono t (show (fun ω' => -|x ω'|) ≤ x from fun ω' => neg_abs_le _) ω
  have h3 : 𝔼.E t (fun ω' => -|x ω'|) = -𝔼.E t (fun ω' => |x ω'|) := by
    rw [← map_neg]
    rfl
  rw [h3] at h2
  exact abs_le.mpr ⟨by simpa using h2, h1⟩

/-- Cochrane (2023), eqs. (2.7) and (2.17), pp. 22, 35: for bounded surpluses and `0 ≤ β < 1`
the discounted forecasts `∑ βᵏ E_n s_{t+k}` are (absolutely) summable, at every forecast date
`n` and starting date `t`. -/
theorem summable_E_shift {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (n t : ℕ) (ω : Ω) :
    Summable (fun k => β ^ k * 𝔼.E n (s (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) n ω) (pow_nonneg h0 k)

end Cochrane.IntertemporalModel.ExpectationTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The intertemporal model: environment

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23,
equations (2.1)–(2.5), and the proportional-tax remark on p. 23.

## Timing convention

The book's debt `B_t` is sold at the end of date `t` and matures at the start of `t + 1`; the
economy starts with `B_{−1}`. To index by natural numbers we write `Bm t` for the debt *maturing*
at date `t`, i.e. `Bm t = B_{t−1}` (so the book's `B_t` is `Bm (t + 1)`), and likewise
`Mm t = M_{t−1}` for money held overnight into date `t`. Random variables are `Ω → ℝ`, processes
`ℕ → Ω → ℝ`, and `E_t` is an arbitrary `ExpectationSystem`.

## Main results

* `GovFlow` (2.1), `HhFlow` (2.2); `hhFlow_iff_govFlow`: with goods-market clearing `c = y` the
  household flow constraint is exactly the government's (the "mirror image", p. 21).
* `HhOptimal`, `euler_of_optimal`: under perfect foresight an optimal household plan with
  positive bond holdings satisfies the nominal Euler equation (a variational proof);
  `bondPrice_of_optimal` gives (2.3) at `c = y`.
* `EulerNominal`, `EulerReal` (the first-order conditions behind (2.3)); `realBondPrice_of_euler`
  (`R = 1/β`), `bondPrice_of_euler` and `bondPrice_iff_euler` ((2.3), both directions, with
  constant marginal utility `u'(y)`), `bondPrice_eq_inv_one_add_rate` (`Q = 1/(1+i)`).
* Money demand (p. 22): `money_dominated` (with `i_t > 0` money held overnight is strictly
  dominated by bonds), `bonds_dominated_of_neg_rate` (with `i_t < 0` bonds are strictly dominated
  by money, so the government cannot sell debt: the rate cannot be negative),
  `perfect_substitutes` (with `i_t = 0` only `M + B` matters).
* `flow_of_govFlow` and `govFlow_merge`: eliminating money gives (2.4).
* `flow_real_25`, `flow_real_x`, `flow_iff_real_x`: (2.5), and its form
  `x_t = s_t + β E_t x_{t+1}` for real debt `x_t = B_{t−1}/P_t`.
* `propTax_real_surplus`, `propTax_surplus_indep_price`: proportional taxes keep the real
  surplus, hence the right-hand side of (2.7), free of the price level (p. 23).

The hypothesis `FunctionsKnown` (functions of known variables are known), used to show that the
equilibrium price level is adapted, lives in `ExpectationTools`.
-/

namespace Cochrane.IntertemporalModel.Environment

open Filter Topology

variable {Ω : Type*}

/-! ### Budget constraints (2.1), (2.2) -/

/-- Cochrane (2023), eq. (2.1), p. 21: the government flow budget constraint
`M_{t−1} + B_{t−1} = P_t s_t + M_t + Q_t B_t`, at every date and state, written with
`Mm t = M_{t−1}`, `Bm t = B_{t−1}`. -/
def GovFlow (Mm Bm P s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Mm t ω + Bm t ω = P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω

/-- Cochrane (2023), eq. (2.2), p. 21: the household flow budget constraint
`M_{t−1} + B_{t−1} + P_t y = P_t c_t + P_t s_t + M_t + Q_t B_t` with constant endowment `y`. -/
def HhFlow (y : ℝ) (Mm Bm P c s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Mm t ω + Bm t ω + P t ω * y =
    P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω

/-- Cochrane (2023), p. 21: with goods-market clearing `c_t = y` the household flow constraint
(2.2) is exactly the government flow constraint (2.1) ("almost the mirror of (2.1)"). -/
theorem hhFlow_iff_govFlow {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} (hc : ∀ t ω, c t ω = y) :
    HhFlow y Mm Bm P c s Q ↔ GovFlow Mm Bm P s Q := by
  constructor
  · intro h t ω
    have := h t ω
    rw [hc t ω] at this
    linarith
  · intro h t ω
    have := h t ω
    rw [hc t ω]
    linarith

/-- Cochrane (2023), pp. 21 and 23: the household and government flow constraints at the same
prices and policies differ exactly by the excess demand for goods,
`(2.2) − (2.1)`: household slack `= P_t (y − c_t) +` government slack. -/
theorem hhFlow_sub_govFlow (y : ℝ) (Mm Bm P c s Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (Mm t ω + Bm t ω + P t ω * y -
        (P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) =
      P t ω * (y - c t ω) +
        (Mm t ω + Bm t ω - (P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) := by
  ring

/-! ### Household optimisation under perfect foresight: the Euler equation -/

/-- Cochrane (2023), eq. (2.2), p. 21, under perfect foresight with no money held: a household
plan `(c, b)` (`b n = B_{n−1}`) is feasible from initial debt `b₀` if it satisfies the flow
constraint `b_n + P_n y = P_n c_n + P_n s_n + Q_n b_{n+1}` at every date and `B ≥ 0`. -/
def HhFeasible (y : ℝ) (P s Q : ℕ → ℝ) (b₀ : ℝ) (c b : ℕ → ℝ) : Prop :=
  b 0 = b₀ ∧ (∀ n, b n + P n * y = P n * c n + P n * s n + Q n * b (n + 1)) ∧ ∀ n, 0 ≤ b n

/-- Cochrane (2023), p. 21, "A representative household maximizes `∑ β^t u(c_t)`": a feasible
plan with summable discounted utility that no feasible plan with summable discounted utility
beats. -/
def HhOptimal (β y : ℝ) (u : ℝ → ℝ) (P s Q : ℕ → ℝ) (b₀ : ℝ) (c b : ℕ → ℝ) : Prop :=
  HhFeasible y P s Q b₀ c b ∧ Summable (fun n => β ^ n * u (c n)) ∧
    ∀ c' b', HhFeasible y P s Q b₀ c' b' → Summable (fun n => β ^ n * u (c' n)) →
      ∑' n, β ^ n * u (c' n) ≤ ∑' n, β ^ n * u (c n)

/-- Cochrane (2023), p. 21, "The consumer's first-order conditions", derived (perfect foresight):
if `(c, b)` is optimal, `u` is differentiable at `c_t` and `c_{t+1}` with derivatives `d₀, d₁`,
prices are positive, `Q_t > 0` and the household holds bonds `B_t > 0`, then shifting `ε` dollars
between consumption at `t` and bonds maturing at `t + 1` cannot raise utility, which gives the
nominal Euler equation `Q_t u'(c_t)/P_t = β u'(c_{t+1})/P_{t+1}`. -/
theorem euler_of_optimal {β y b₀ d₀ d₁ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {P s Q c b : ℕ → ℝ}
    (hopt : HhOptimal β y u P s Q b₀ c b) {t : ℕ} (hPt : 0 < P t) (hPt1 : 0 < P (t + 1))
    (hQ : 0 < Q t) (hb : 0 < b (t + 1)) (hu0 : HasDerivAt u d₀ (c t))
    (hu1 : HasDerivAt u d₁ (c (t + 1))) :
    Q t * (d₀ / P t) = β * (d₁ / P (t + 1)) := by
  obtain ⟨⟨hb0, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  -- the perturbed plans
  let cε : ℝ → ℕ → ℝ := fun ε n =>
    c n + (if n = t then ε / P t else if n = t + 1 then -(ε / (Q t * P (t + 1))) else 0)
  let bε : ℝ → ℕ → ℝ := fun ε n => b n - (if n = t + 1 then ε / Q t else 0)
  let φ : ℝ → ℝ := fun ε => β ^ t * (u (c t + ε / P t) - u (c t)) +
    β ^ (t + 1) * (u (c (t + 1) - ε / (Q t * P (t + 1))) - u (c (t + 1)))
  have hQ0 := hQ.ne'
  have hP0 := hPt.ne'
  have hP1 := hPt1.ne'
  have hfeas : ∀ ε, |ε| < Q t * b (t + 1) → HhFeasible y P s Q b₀ (cε ε) (bε ε) := by
    intro ε hε
    refine ⟨by simp [bε, hb0], fun n => ?_, fun n => ?_⟩
    · by_cases hn : n = t
      · subst hn
        simp only [cε, bε, ↓reduceIte, (show ¬ (n = n + 1) by omega)]
        have := hflow n
        field_simp
        linarith
      · by_cases hn1 : n = t + 1
        · subst hn1
          have := hflow (t + 1)
          simp only [cε, bε, ↓reduceIte, hn, (show ¬ (t + 1 + 1 = t + 1) by omega)]
          field_simp
          linear_combination (Q t) * this
        · have hn2 : n + 1 ≠ t + 1 := fun h => hn (by omega)
          simp only [cε, bε, hn, hn1, hn2, ↓reduceIte, add_zero, sub_zero]
          exact hflow n
    · simp only [bε]
      split_ifs with hn
      · subst hn
        have h1 : ε / Q t ≤ b (t + 1) := by
          rw [div_le_iff₀ hQ]
          linarith [le_abs_self ε, mul_comm (Q t) (b (t + 1))]
        linarith
      · simpa using hbnn n
  -- utility of the perturbed plan
  have hdiff : ∀ ε, HasSum (fun n => β ^ n * u (cε ε n)) (∑' n, β ^ n * u (c n) + φ ε) := by
    intro ε
    have hg : HasSum (fun n => β ^ n * u (cε ε n) - β ^ n * u (c n)) (φ ε) := by
      have h : HasSum (fun n => β ^ n * u (cε ε n) - β ^ n * u (c n))
          (∑ n ∈ ({t, t + 1} : Finset ℕ), (β ^ n * u (cε ε n) - β ^ n * u (c n))) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          simp [cε, hn.1, hn.2])
      convert h using 1
      rw [Finset.sum_pair (by omega)]
      simp only [cε, φ, ↓reduceIte, (show ¬ (t + 1 = t) by omega)]
      ring_nf
    convert hsum.hasSum.add hg using 1
    · funext n
      ring
  have hle : ∀ ε, |ε| < Q t * b (t + 1) → φ ε ≤ 0 := by
    intro ε hε
    have h1 := hbest (cε ε) (bε ε) (hfeas ε hε) (hdiff ε).summable
    rw [(hdiff ε).tsum_eq] at h1
    linarith
  -- φ has a local maximum at 0
  have hmax : IsLocalMax φ 0 := by
    have hpos : 0 < Q t * b (t + 1) := mul_pos hQ hb
    have hmem : Set.Ioo (-(Q t * b (t + 1))) (Q t * b (t + 1)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hpos
    filter_upwards [hmem] with ε hε
    have : φ 0 = 0 := by simp [φ]
    rw [this]
    exact hle ε (abs_lt.mpr hε)
  -- the derivative of φ at 0
  have hf0 : HasDerivAt (fun ε => c t + ε / P t) (1 / P t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const (P t)).const_add (c t)
  have hf1 : HasDerivAt (fun ε => c (t + 1) - ε / (Q t * P (t + 1)))
      (-(1 / (Q t * P (t + 1)))) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const (Q t * P (t + 1))).const_sub (c (t + 1))
  have hu0' : HasDerivAt u d₀ ((fun ε => c t + ε / P t) 0) := by simpa using hu0
  have hu1' : HasDerivAt u d₁ ((fun ε => c (t + 1) - ε / (Q t * P (t + 1))) 0) := by
    simpa using hu1
  have hφ : HasDerivAt φ (β ^ t * (d₀ * (1 / P t)) +
      β ^ (t + 1) * (d₁ * (-(1 / (Q t * P (t + 1)))))) 0 := by
    have a := ((hu0'.comp 0 hf0).sub_const (u (c t))).const_mul (β ^ t)
    have b' := ((hu1'.comp 0 hf1).sub_const (u (c (t + 1)))).const_mul (β ^ (t + 1))
    exact a.add b'
  have hzero := hmax.hasDerivAt_eq_zero hφ
  have hbt : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
  rw [pow_succ] at hzero
  field_simp at hzero
  have : β ^ t * (Q t * d₀ * P (t + 1) - β * d₁ * P t) = 0 := by linear_combination hzero
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hbt
  · field_simp
    linarith

/-- Cochrane (2023), eq. (2.3), p. 22, derived from optimisation (perfect foresight): if the
endowment plan `c = y` with bond holdings `B_t > 0` is optimal and `u'(y) > 0`, then
`Q_t = β P_t/P_{t+1}`. -/
theorem bondPrice_of_optimal {β y b₀ uy : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {P s Q b : ℕ → ℝ}
    (hopt : HhOptimal β y u P s Q b₀ (fun _ => y) b) {t : ℕ} (hPt : 0 < P t)
    (hPt1 : 0 < P (t + 1)) (hQ : 0 < Q t) (hb : 0 < b (t + 1)) (huy : 0 < uy)
    (hu : HasDerivAt u uy y) : Q t = β * (P t / P (t + 1)) := by
  have h := euler_of_optimal hβ hopt hPt hPt1 hQ hb hu hu
  have := hPt.ne'
  have := hPt1.ne'
  have h2 : uy * (Q t * P (t + 1) - β * P t) = 0 := by
    field_simp at h
    linear_combination uy * h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 huy.ne'
  · field_simp
    linarith

/-! ### First-order conditions and the bond price (2.3) -/

/-- Cochrane (2023), p. 21 ("the consumer's first-order conditions"): the Euler equation for the
nominal one-period bond, `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`, with `lam t = u'(c_t)`. -/
def EulerNominal (𝔼 : ExpectationSystem Ω) (β : ℝ) (lam P Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Q t * (fun ω => lam t ω / P t ω) = β • 𝔼.E t (fun ω => lam (t + 1) ω / P (t + 1) ω)

/-- Cochrane (2023), p. 21: the Euler equation for a one-period real (indexed) bond with price
`q_t`, `q_t u'(c_t) = β E_t u'(c_{t+1})`; the gross real rate is `R_t = 1/q_t`. -/
def EulerReal (𝔼 : ExpectationSystem Ω) (β : ℝ) (lam q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q t * lam t = β • 𝔼.E t (lam (t + 1))

/-- Cochrane (2023), p. 21: "equilibrium `c_t = y` then impl[ies] that the gross real interest rate
is `R = 1/β`": with constant positive marginal utility `u'(y)` the real bond price is `β`. -/
theorem realBondPrice_of_euler (𝔼 : ExpectationSystem Ω) {β uy : ℝ} (huy : 0 < uy)
    {lam q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy) (heu : EulerReal 𝔼 β lam q) (t : ℕ) :
    q t = fun _ => β := by
  have h := heu t
  rw [hlam t, hlam (t + 1), 𝔼.const] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hω
  have : (q t ω - β) * uy = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 huy.ne'

/-- Cochrane (2023), p. 21: the gross real rate `R = 1/q` equals `1/β`. -/
theorem realRate_eq_inv_beta (𝔼 : ExpectationSystem Ω) {β uy : ℝ} (huy : 0 < uy)
    {lam q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy) (heu : EulerReal 𝔼 β lam q) (t : ℕ)
    (ω : Ω) : (q t ω)⁻¹ = β⁻¹ := by
  rw [realBondPrice_of_euler 𝔼 huy hlam heu t]

/-- Cochrane (2023), eq. (2.3), p. 22: with constant positive marginal utility `u'(y)`, a
positive price level known at `t`, and the pull-out property, the nominal Euler equation gives
`Q_t = β E_t(P_t/P_{t+1})`. -/
theorem bondPrice_of_euler (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β uy : ℝ}
    (huy : 0 < uy) {lam P Q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy)
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P) (heu : EulerNominal 𝔼 β lam P Q) (t : ℕ) :
    Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := by
  have h := heu t
  have hsplit : (fun ω => lam (t + 1) ω / P (t + 1) ω) =
      (fun _ => uy) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; rw [hlam (t + 1)]; simp [div_eq_mul_inv]
  have hsplit2 : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ (𝔼.const t uy)] at h
  rw [hsplit2, hPO t _ _ (hPad t)]
  funext ω
  have hω := congrFun h ω
  rw [hlam t] at hω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
  have hP := (hPpos t ω).ne'
  set e := 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω
  have h2 : Q t ω * uy = (β * (P t ω * e)) * uy := by
    have h3 : Q t ω * uy = Q t ω * (uy / P t ω) * P t ω := by field_simp
    rw [h3, hω]
    ring
  exact mul_right_cancel₀ huy.ne' h2

/-- Cochrane (2023), eq. (2.3), p. 22, both directions: with constant positive marginal utility,
a positive adapted price level and the pull-out property, the nominal Euler equation holds iff
`Q_t = β E_t(P_t/P_{t+1})` at every date. -/
theorem bondPrice_iff_euler (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β uy : ℝ}
    (huy : 0 < uy) {lam P Q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy)
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P) :
    EulerNominal 𝔼 β lam P Q ↔ ∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := by
  refine ⟨fun h t => bondPrice_of_euler 𝔼 hPO huy hlam hPpos hPad h t, fun h t => ?_⟩
  have hsplit : (fun ω => lam (t + 1) ω / P (t + 1) ω) =
      (fun _ => uy) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; rw [hlam (t + 1)]; simp [div_eq_mul_inv]
  have hsplit2 : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ (𝔼.const t uy), h t, hsplit2, hPO t _ _ (hPad t)]
  funext ω
  rw [hlam t]
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hP := (hPpos t ω).ne'
  field_simp

/-- Cochrane (2023), p. 21: the nominal interest rate implied by the bond price,
`i_t = 1/Q_t − 1`. -/
noncomputable def rate (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := (Q t ω)⁻¹ - 1

/-- Cochrane (2023), p. 21: `Q_t = 1/(1 + i_t)`. -/
theorem bondPrice_eq_inv_one_add_rate (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Q t ω = (1 + rate Q t ω)⁻¹ := by
  simp [rate]

/-- Cochrane (2023), eq. (2.3), p. 22: `1/(1+i_t) = (1/R) E_t(P_t/P_{t+1})` with `R = 1/β`. -/
theorem inv_one_add_rate_eq (𝔼 : ExpectationSystem Ω) {β : ℝ} {P Q : ℕ → Ω → ℝ}
    {t : ℕ} (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) (ω : Ω) :
    (1 + rate Q t ω)⁻¹ = (β⁻¹)⁻¹ * 𝔼.E t (fun ω => P t ω / P (t + 1) ω) ω := by
  rw [← bondPrice_eq_inv_one_add_rate, inv_inv, h23]
  simp

/-- Cochrane (2023), p. 22: the rate is positive iff the bond price is below one (for `Q > 0`). -/
theorem rate_pos_iff {Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hQ : 0 < Q t ω) :
    0 < rate Q t ω ↔ Q t ω < 1 := by
  simp only [rate, sub_pos]
  rw [one_lt_inv₀ hQ]

/-- Cochrane (2023), p. 22: the rate is negative iff the bond price exceeds one (for `Q > 0`). -/
theorem rate_neg_iff {Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hQ : 0 < Q t ω) :
    rate Q t ω < 0 ↔ 1 < Q t ω := by
  simp only [rate, sub_neg]
  rw [inv_lt_one₀ hQ]

/-! ### Money demand (p. 22) -/

/-- Cochrane (2023), p. 22, "When `i_t > 0` the household demands no money `M_t = 0`": take any
household plan satisfying (2.2) at dates `t` and `t + 1` in state `ω`. Replace the money held
overnight `M_t` by `M_t/Q_t` more bonds, and spend the extra payoff `i_t M_t` at `t + 1`. The new
plan satisfies (2.2) at both dates, keeps `B_t ≥ 0`, `M_t = 0`, and raises date-`t+1`
consumption by `i_t M_t / P_{t+1}`, strictly if `M_t > 0`. -/
theorem money_dominated {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hQ : 0 < Q t ω) (hP1 : 0 < P (t + 1) ω)
    (h0 : Mm t ω + Bm t ω + P t ω * y =
      P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)
    (h1 : Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y =
      P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω +
        Q (t + 1) ω * Bm (t + 2) ω) :
    let B' := Bm (t + 1) ω + Mm (t + 1) ω / Q t ω
    let c' := c (t + 1) ω + rate Q t ω * Mm (t + 1) ω / P (t + 1) ω
    (Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + 0 + Q t ω * B') ∧
      (0 + B' + P (t + 1) ω * y = P (t + 1) ω * c' + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ∧
      (0 ≤ Bm (t + 1) ω → 0 ≤ Mm (t + 1) ω → 0 ≤ B') ∧
      (0 < rate Q t ω → 0 < Mm (t + 1) ω → c (t + 1) ω < c') := by
  intro B' c'
  have hQ0 := hQ.ne'
  have hP0 := hP1.ne'
  refine ⟨?_, ?_, fun hb hm => ?_, fun hi hm => ?_⟩
  · simp only [B']
    field_simp
    linarith
  · simp only [B', c', rate]
    field_simp
    linear_combination (Q t ω) * h1
  · exact add_nonneg hb (div_nonneg hm hQ.le)
  · simp only [c']
    have : 0 < rate Q t ω * Mm (t + 1) ω / P (t + 1) ω := by positivity
    linarith

/-- Cochrane (2023), p. 22, "The interest rate cannot be less than zero in this model": with
`i_t < 0` (`Q_t > 1`), any plan holding bonds `B_t > 0` is strictly dominated by holding their
cost `Q_t B_t` as money instead: (2.2) still holds at `t` and `t + 1`, money stays nonnegative,
`B_t = 0`, and date-`t+1` consumption rises by `(Q_t − 1) B_t / P_{t+1} > 0`. So no household
holds the government's debt at a negative rate. -/
theorem bonds_dominated_of_neg_rate {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hP1 : 0 < P (t + 1) ω)
    (h0 : Mm t ω + Bm t ω + P t ω * y =
      P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)
    (h1 : Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y =
      P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω +
        Q (t + 1) ω * Bm (t + 2) ω) :
    let M' := Mm (t + 1) ω + Q t ω * Bm (t + 1) ω
    let c' := c (t + 1) ω + (Q t ω - 1) * Bm (t + 1) ω / P (t + 1) ω
    (Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + M' + Q t ω * 0) ∧
      (M' + 0 + P (t + 1) ω * y = P (t + 1) ω * c' + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ∧
      (0 ≤ Mm (t + 1) ω → 0 ≤ Q t ω → 0 ≤ Bm (t + 1) ω → 0 ≤ M') ∧
      (1 < Q t ω → 0 < Bm (t + 1) ω → c (t + 1) ω < c') := by
  intro M' c'
  have hP0 := hP1.ne'
  refine ⟨?_, ?_, fun hm hq hb => ?_, fun hq hb => ?_⟩
  · simp only [M']
    linarith
  · simp only [M', c']
    field_simp
    linarith
  · exact add_nonneg hm (mul_nonneg hq hb)
  · simp only [c']
    have : 0 < (Q t ω - 1) * Bm (t + 1) ω / P (t + 1) ω :=
      div_pos (mul_pos (by linarith) hb) hP1
    linarith

/-- Cochrane (2023), p. 22, "When `i_t = 0` money and bonds are perfect substitutes, so the
symbol `B_t` can stand for their sum": with `Q_t = 1`, any reallocation `(M', B')` of the
overnight portfolio with the same total `M' + B' = M_t + B_t` leaves (2.2) at `t` and `t + 1`
unchanged. -/
theorem perfect_substitutes {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hQ : Q t ω = 1) {M' B' : ℝ} (hsum : M' + B' = Mm (t + 1) ω + Bm (t + 1) ω) :
    ((Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + M' + Q t ω * B') ↔
      (Mm t ω + Bm t ω + P t ω * y =
        P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) ∧
    ((M' + B' + P (t + 1) ω * y = P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ↔
      (Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y = P (t + 1) ω * c (t + 1) ω +
        P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω)) := by
  simp only [hQ, one_mul]
  exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩⟩

/-! ### Eliminating money: (2.4) -/

/-- Cochrane (2023), eq. (2.4), p. 22: if no money is held overnight (`M_t = 0` for all `t`,
including `M_{−1}`), the government constraint (2.1) is `B_{t−1} = P_t s_t + Q_t B_t`. -/
theorem flow_of_govFlow {Mm Bm P s Q : ℕ → Ω → ℝ} (hM : ∀ t ω, Mm t ω = 0)
    (h21 : GovFlow Mm Bm P s Q) (t : ℕ) (ω : Ω) :
    Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω := by
  have := h21 t ω
  rw [hM t ω, hM (t + 1) ω] at this
  linarith

/-- Cochrane (2023), eq. (2.4), p. 22, the general elimination of money: if at every date either
no money is held overnight (`i_t > 0`) or `Q_t = 1` (`i_t = 0`, money and bonds perfect
substitutes), then with `B` standing for the sum of money and bonds, (2.1) becomes (2.4). -/
theorem govFlow_merge {Mm Bm P s Q : ℕ → Ω → ℝ}
    (hMQ : ∀ t ω, Mm (t + 1) ω = 0 ∨ Q t ω = 1) (h21 : GovFlow Mm Bm P s Q) (t : ℕ) (ω : Ω) :
    Mm t ω + Bm t ω = P t ω * s t ω + Q t ω * (Mm (t + 1) ω + Bm (t + 1) ω) := by
  have := h21 t ω
  rcases hMQ t ω with h | h
  · rw [h] at this ⊢
    linarith
  · rw [h] at this ⊢
    linarith

/-! ### The real flow condition (2.5) -/

/-- Cochrane (2023), eq. (2.5), p. 22: substituting the bond price (2.3) into (2.4) and dividing
by `P_t > 0` (with `P_t` and `B_t` known at `t`, and the pull-out property),
`B_{t−1}/P_t = s_t + β B_t E_t(1/P_{t+1})`. -/
theorem flow_real_25 (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (h24 : ∀ ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (ω : Ω) :
    Bm t ω / P t ω = s t ω + β * Bm (t + 1) ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω := by
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ hPad] at h23
  have hQ := congrFun h23 ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hQ
  rw [h24 ω, hQ]
  have := (hPpos ω).ne'
  field_simp

/-- Cochrane (2023), eq. (2.5), p. 22, in terms of real debt `x_t = B_{t−1}/P_t`: with `B_t` known
at `t` and the pull-out property, `β B_t E_t(1/P_{t+1}) = β E_t x_{t+1}`, so (2.5) reads
`x_t = s_t + β E_t x_{t+1}`. -/
theorem flow_real_x (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P : ℕ → Ω → ℝ} {t : ℕ} (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) :
    (fun ω => β * Bm (t + 1) ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) =
      β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  have hsplit : (fun ω => Bm (t + 1) ω / P (t + 1) ω) =
      Bm (t + 1) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ hB]
  funext ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eqs. (2.4)–(2.5), p. 22, both directions: given (2.3), positive `P_t` known
at `t`, `B_t` known at `t` and pull-out, the nominal flow condition (2.4) at `t` holds iff the real
one `x_t = s_t + β E_t x_{t+1}` holds, `x_t = B_{t−1}/P_t`. -/
theorem flow_iff_real_x (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) :
    (∀ ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ↔
      (fun ω => Bm t ω / P t ω) =
        s t + β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  have hx := flow_real_x 𝔼 hPO (β := β) (P := P) hB
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : ∀ ω, Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    intro ω
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  constructor
  · intro h24
    rw [← hx]
    funext ω
    have := flow_real_25 𝔼 hPO hPpos hPad h23 h24 ω
    simpa using this
  · intro h ω
    have h1 := congrFun h ω
    rw [← hx] at h1
    simp only [Pi.add_apply] at h1
    have hP := (hPpos ω).ne'
    have hBP : Bm t ω = P t ω * (Bm t ω / P t ω) := by field_simp
    rw [hQ ω, hBP, h1]
    ring

/-! ### Proportional taxes (p. 23) -/

/-- Cochrane (2023), p. 23: with surpluses `P_t s_t = τ_t (P_t y) − P_t x_t` (a proportional
income tax less a real transfer) and `P_t ≠ 0`, the real surplus is `s_t = τ_t y − x_t`. -/
theorem propTax_real_surplus {y : ℝ} {P s τ xtr : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hP : P t ω ≠ 0) (h : P t ω * s t ω = τ t ω * (P t ω * y) - P t ω * xtr t ω) :
    s t ω = τ t ω * y - xtr t ω := by
  have : P t ω * (s t ω - (τ t ω * y - xtr t ω)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hP
  · linarith

/-- Cochrane (2023), p. 23: "This specification ensures that the price level is absent from the
right-hand side of (2.7)": two price paths (nonzero) with the same tax rates and real transfers
generate the same real surpluses. -/
theorem propTax_surplus_indep_price {y : ℝ} {P P' s s' τ xtr : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hP' : ∀ t ω, P' t ω ≠ 0)
    (h : ∀ t ω, P t ω * s t ω = τ t ω * (P t ω * y) - P t ω * xtr t ω)
    (h' : ∀ t ω, P' t ω * s' t ω = τ t ω * (P' t ω * y) - P' t ω * xtr t ω) : s = s' := by
  funext t ω
  rw [propTax_real_surplus (hP t ω) (h t ω), propTax_real_surplus (hP' t ω) (h' t ω)]

end Cochrane.IntertemporalModel.Environment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 22–23,
equations (2.5)–(2.8), and Online Appendix A1.1 "The transversality condition", pp. 554–556,
equations (1.1)–(1.3).

Real debt is `x_t = B_{t−1}/P_t` (`Bm t / P t` in the indexing of `Environment`). The flow
condition (2.5) is `x_t = s_t + β E_t x_{t+1}` (`FlowX`), the transversality condition (2.6)
is `lim_N β^N E_t x_{t+N} = 0` (`TVC`; `tvc_iff_tvcBook` relates it to the book's form
`lim_T β^T E_t x_T = 0`), and the present value of surpluses is the genuine infinite sum
`pv_t = ∑_{j ≥ 0} β^j E_t s_{t+j}` (`pv`).

## Hypotheses made explicit

Surpluses are signed, so the present value is controlled by *absolute* summability
`∑_j β^j E_t|s_{t+j}| < ∞` at every date and state (`AbsSummable`), not by nonnegativity; and
`E_t` is interchanged with infinite sums through conditional monotone convergence
(`MonotoneConvergence`, restated from the Woodford Chapter 2 project, true for perfect foresight
and every finite event tree), applied to the positive and negative parts of `s`.

## Main results

* `telescope`: `x_t = ∑_{j<N} β^j E_t s_{t+j} + β^N E_t x_{t+N}`.
* `valuation_iff` (2.5)–(2.7): the flow condition at every date plus the TVC at every date
  holds iff `x_t = ∑_j β^j E_t s_{t+j}` at every date (both directions).
* `IsEqm`: an equilibrium (positive adapted price level, bond price (2.3), flow (2.4), TVC (2.6)),
  and the fiscal-theory determination of the price level: `eqm_price_eq` (`P_t = B_{t−1}/pv_t`),
  `eqm_of_pv_pos` (existence), `existsUnique_eqm` (the price level and bond price are unique
  given debt and surpluses), `no_eqm_of_pv_nonpos` (no equilibrium if some `pv_t ≤ 0`).
* `hh_pv_iff` (2.8) and `excess_demand_of_gap` (p. 23).
* A1.1: `tvc_iff_noPonzi_and_optimal` (the box on p. 554), `noPonzi_of_nonneg_debt`,
  `hh_iterate` ((1.1)–(1.2), with exponent `T + 1`; the printed `R^{−T}` is refuted by
  `printed_A1_2_false`), `const_explodes`, `const_terminal_limit`, `const_tvc_iff`
  (the A1.1 example, p. 555, under uncertainty too), and the perfect-foresight deviation argument
  (1.3): `deviation_closed_form`, `deviation_feasible`, `deviation_improves`,
  `deviation_optimal`, `tooLow_not_equilibrium`; `bubble_deviation` (the general version: a
  pathwise bubble can be consumed).
* `tvc_of_optimal`, `valuation_of_optimal` (p. 22): under perfect foresight, household
  optimisation implies the transversality condition (2.6), and hence (2.7).
* `deviation_optimal_concave` (A1 p. 556) under the book's assumption (concave increasing `u`),
  via `concave_le_tangent` and `deriv_nonneg_of_monotone`.
* Under uncertainty (finite state space; `SFeasible`, `expUtil`, `SOptimal` state-contingent
  plans maximising `∑_t β^t E_0 u(c_t)`): `euler_of_optimal_stoch` (the conditional Euler
  equation `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`, by the variational argument along
  date-`t` measurable deviations), `tvc_of_optimal_stoch` (optimisation implies (2.6) at every
  date and state, given information that stops growing, `InfoStable`), and
  `valuation_of_optimal_stoch` ((2.7)). The extra hypotheses `Faithful` and `InfoStable` hold
  for every finite event tree (`finiteTree_faithful`, `finiteTree_infoStable`).
-/

namespace Cochrane.IntertemporalModel.Valuation

open Filter Topology Environment ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Flow, transversality and present value -/

/-- Cochrane (2023), eq. (2.5), p. 22: the real flow condition `x_t = s_t + β E_t x_{t+1}` at
every date, for real debt `x_t = B_{t−1}/P_t` (see `Environment.flow_iff_real_x`). -/
def FlowX (β : ℝ) (x s : ℕ → Ω → ℝ) : Prop := ∀ t, x t = s t + β • 𝔼.E t (x (t + 1))

/-- Cochrane (2023), eq. (2.6), p. 22: the transversality condition looking forward from date
`t`, `lim_{N→∞} β^N E_t x_{t+N} = 0` in every state. -/
def TVC (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N : ℕ => β ^ N * 𝔼.E t (x (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (2.6), p. 22, exactly as printed: `lim_{T→∞} E_t β^T B_{T−1}/P_T = 0`,
i.e. `lim_T β^T E_t x_T = 0`. -/
def TVCBook (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x T) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (2.6), p. 22: for `β > 0` the printed form `lim_T β^T E_t x_T = 0` and
the form `lim_N β^N E_t x_{t+N} = 0` are equivalent (they differ by the factor `β^t`). -/
theorem tvc_iff_tvcBook {β : ℝ} (hβ : 0 < β) (x : ℕ → Ω → ℝ) (t : ℕ) :
    TVC 𝔼 β x t ↔ TVCBook 𝔼 β x t := by
  have hb : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
  constructor
  · intro h ω
    rw [← Filter.tendsto_add_atTop_iff_nat t]
    have := (h ω).const_mul (β ^ t)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    rw [add_comm N t, pow_add]
    ring
  · intro h ω
    have h2 := ((Filter.tendsto_add_atTop_iff_nat t).mpr (h ω)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    rw [add_comm N t, pow_add]
    field_simp

/-- Cochrane (2023), eq. (2.7), p. 22 (signed surpluses): absolute summability
`∑_j β^j E_t|s_{t+j}| < ∞` at every date and in every state. -/
def AbsSummable (β : ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun j : ℕ => β ^ j * 𝔼.E t (fun ω' => |s (t + j) ω'|) ω

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of surpluses
`E_t ∑_{j ≥ 0} β^j s_{t+j}`, written as the genuine infinite sum `∑_j β^j E_t s_{t+j}`. This is
the core forward series `𝔼.forwardSeries β s t` under its book name (the one present-value
definition of the chapter; `FiscalMonetary.pv` is the ex-post form `E_t ∑ β^j s_{t+j}`, equal to
it under the hypotheses of `GeneralLinks.fm_pv_eq_pv`). -/
noncomputable abbrev pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.forwardSeries β s t

/-- Cochrane (2023), eq. (2.7), p. 22: the present value in coordinates,
`pv_t(ω) = ∑_j β^j E_t s_{t+j}(ω)`. -/
theorem pv_apply (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pv 𝔼 β s t ω = ∑' j : ℕ, β ^ j * 𝔼.E t (s (t + j)) ω := rfl

/-- Cochrane (2023), eq. (2.7), p. 22: under absolute summability the present-value series
converges in every state. -/
theorem summable_terms {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (t : ℕ) (ω : Ω) : Summable fun j : ℕ => β ^ j * 𝔼.E t (s (t + j)) ω :=
  Summable.of_norm_bounded (hs t ω) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (abs_E_le_E_abs 𝔼 t _ ω) (pow_nonneg hβ j)

/-- Cochrane (2023), eq. (2.5), p. 22: with adapted surpluses, real debt satisfying the flow
condition is known at each date. -/
theorem adapted_of_flow {β : ℝ} {x s : ℕ → Ω → ℝ} (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) :
    𝔼.Adapted x := by
  intro t
  calc 𝔼.E t (x t) = 𝔼.E t (s t + β • 𝔼.E t (x (t + 1))) := by rw [← h t]
    _ = s t + β • 𝔼.E t (x (t + 1)) := by rw [map_add, map_smul, hsad t, 𝔼.E_E_self]
    _ = x t := (h t).symm

/-- Cochrane (2023), p. 22 ("iterate (2.5)") and Online Appendix A1.1, p. 555: the exact
finite-horizon identity `x_t = ∑_{j<N} β^j E_t s_{t+j} + β^N E_t x_{t+N}`. -/
theorem telescope {β : ℝ} {x s : ℕ → Ω → ℝ} (h : FlowX 𝔼 β x s) {t : ℕ}
    (hxt : 𝔼.E t (x t) = x t) (N : ℕ) :
    x t = (∑ j ∈ Finset.range N, β ^ j • 𝔼.E t (s (t + j))) + β ^ N • 𝔼.E t (x (t + N)) := by
  induction N with
  | zero => simp [hxt]
  | succ N ih =>
    have step : 𝔼.E t (x (t + N)) = 𝔼.E t (s (t + N)) + β • 𝔼.E t (x (t + N + 1)) := by
      have := congrArg (𝔼.E t) (h (t + N))
      rwa [map_add, map_smul, 𝔼.tower (Nat.le_add_right t N)] at this
    rw [ih, step, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ, ← add_assoc]
    rfl

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22 (sufficiency): the flow condition at every date
and the TVC at `t` give `x_t = ∑_j β^j E_t s_{t+j}`, as a genuine convergent series. -/
theorem hasSum_of_flow_tvc {β : ℝ} (hβ : 0 ≤ β) {x s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) {t : ℕ} (htvc : TVC 𝔼 β x t) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (x t ω) := by
  have hxt := adapted_of_flow 𝔼 hsad h t
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ N * 𝔼.E t (x (t + N)) ω := by
    intro N
    have := congrFun (telescope 𝔼 h hxt N) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω)) := by
    simp_rw [hpart]
    simpa using (tendsto_const_nhds (x := x t ω)).sub (htvc ω)
  have hS := summable_terms 𝔼 hβ hs t ω
  rw [tendsto_nhds_unique hlim hS.hasSum.tendsto_sum_nat]
  exact hS.hasSum

/-- Cochrane (2023), p. 22 (signed surpluses), the step "iterate (2.5)" in the other
direction: the expectation at `t` of the date-`(t+N)` present value is the tail
`∑_j β^j E_t s_{t+N+j}`. Proof: split `s` into positive and negative parts and apply
conditional monotone convergence to each. -/
theorem hasSum_E_pv (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t N : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + N + j)) ω) (𝔼.E t (pv 𝔼 β s (t + N)) ω) := by
  set sp : ℕ → Ω → ℝ := fun n ω => max (s n ω) 0 with hsp
  set sn : ℕ → Ω → ℝ := fun n ω => max (-s n ω) 0 with hsn
  have hsplit : ∀ n, s n = sp n - sn n := fun n => by
    funext ω
    simp [hsp, hsn, max_zero_sub_max_neg_zero_eq_self]
  -- the summands for each part, as functions of the state
  have hpart : ∀ (r : ℕ → Ω → ℝ), (∀ n ω, 0 ≤ r n ω) → (∀ n ω, r n ω ≤ |s n ω|) →
      (∀ ω', Summable fun j : ℕ => β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω') ∧
      HasSum (fun j => β ^ j * 𝔼.E t (r (t + N + j)) ω)
        (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω') ω) := by
    intro r hr0 hrs
    set f : ℕ → Ω → ℝ := fun j ω' => β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω' with hf
    have hf0 : ∀ k ω', 0 ≤ f k ω' := fun k ω' =>
      mul_nonneg (pow_nonneg hβ k) (E_nonneg 𝔼 (hr0 _) ω')
    have hfs : ∀ ω', Summable fun k => f k ω' := fun ω' => by
      refine Summable.of_nonneg_of_le (fun k => hf0 k ω') (fun k => ?_) (hs (t + N) ω')
      exact mul_le_mul_of_nonneg_left (𝔼.mono _ (fun ω'' => hrs _ ω'') ω') (pow_nonneg hβ k)
    refine ⟨hfs, ?_⟩
    have hmc := hMC t f hf0 hfs ω
    refine hmc.congr_fun fun j => ?_
    have hfj : f j = β ^ j • 𝔼.E (t + N) (r (t + N + j)) := rfl
    rw [hfj, map_smul, 𝔼.tower (Nat.le_add_right t N)]
    rfl
  have hp := hpart sp (fun n ω => le_max_right _ _)
    (fun n ω => max_le (le_abs_self _) (abs_nonneg _))
  have hn := hpart sn (fun n ω => le_max_right _ _)
    (fun n ω => max_le (neg_le_abs _) (abs_nonneg _))
  have hpv : pv 𝔼 β s (t + N) =
      (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (sp (t + N + j)) ω') -
        (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (sn (t + N + j)) ω') := by
    funext ω'
    simp only [pv_apply, Pi.sub_apply]
    rw [← (hp.1 ω').tsum_sub (hn.1 ω')]
    refine tsum_congr fun j => ?_
    rw [hsplit (t + N + j), map_sub, Pi.sub_apply]
    ring
  rw [hpv, map_sub, Pi.sub_apply]
  refine (hp.2.sub hn.2).congr_fun fun j => ?_
  rw [hsplit (t + N + j), map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (2.7), p. 22: the present value is known at the date it is computed. -/
theorem E_pv_self (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t : ℕ) : 𝔼.E t (pv 𝔼 β s t) = pv 𝔼 β s t := by
  funext ω
  have h := hasSum_E_pv 𝔼 hMC hβ hs t 0 ω
  simp only [add_zero] at h
  exact h.tsum_eq.symm

/-- Cochrane (2023), eqs. (2.5) and (2.7), p. 22: the present value satisfies the flow
condition, `pv_t = s_t + β E_t pv_{t+1}`. -/
theorem pv_flow (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) : FlowX 𝔼 β (pv 𝔼 β s) s := by
  intro t
  funext ω
  have h1 := hasSum_E_pv 𝔼 hMC hβ hs t 1 ω
  have h0 := (summable_terms 𝔼 hβ hs t ω).tsum_eq_zero_add
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' j : ℕ, β ^ j * 𝔼.E t (s (t + j)) ω = _
  rw [h0, ← h1.tsum_eq, ← tsum_mul_left, pow_zero, one_mul, add_zero, hsad t]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]
  ring

/-- Cochrane (2023), eqs. (2.6)–(2.7), p. 22: the present value satisfies the transversality
condition: `β^N E_t pv_{t+N}` is the tail `∑_{j ≥ N} β^j E_t s_{t+j}`, which tends to zero. -/
theorem pv_tvc (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t : ℕ) : TVC 𝔼 β (pv 𝔼 β s) t := by
  intro ω
  set f : ℕ → ℝ := fun j => β ^ j * 𝔼.E t (s (t + j)) ω with hf
  have htail : (fun N : ℕ => β ^ N * 𝔼.E t (pv 𝔼 β s (t + N)) ω) =
      fun N => ∑' j, f (j + N) := by
    funext N
    rw [← (hasSum_E_pv 𝔼 hMC hβ hs t N ω).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hf]
    rw [pow_add, show t + N + j = t + (j + N) by omega]
    ring
  rw [htail]
  exact tendsto_sum_nat_add f

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22, both directions, with signed surpluses: for
`β ≥ 0`, adapted, absolutely summable surpluses and conditional monotone convergence, real debt
satisfies the flow condition (2.5) and the transversality condition (2.6) at every date iff it
equals the present value of surpluses (2.7) at every date. -/
theorem valuation_iff (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β)
    {x s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) :
    (FlowX 𝔼 β x s ∧ ∀ t, TVC 𝔼 β x t) ↔ ∀ t, x t = pv 𝔼 β s t := by
  constructor
  · rintro ⟨h, htvc⟩ t
    funext ω
    exact (hasSum_of_flow_tvc 𝔼 hβ hs hsad h (htvc t) ω).tsum_eq.symm
  · intro h
    have hx : x = pv 𝔼 β s := funext h
    rw [hx]
    exact ⟨pv_flow 𝔼 hMC hβ hs hsad, pv_tvc 𝔼 hMC hβ hs⟩

/-! ### The equilibrium price level -/

/-- Cochrane (2023), §2.1, pp. 21–22: an equilibrium given nominal debt `{B_t}` (`Bm`) and real
surpluses `{s_t}`: a positive price level known at each date, the bond price (2.3)
`Q_t = β E_t(P_t/P_{t+1})`, the flow condition (2.4) `B_{t−1} = P_t s_t + Q_t B_t`, and the
transversality condition (2.6) on real debt `B_{t−1}/P_t`, at every date. -/
def IsEqm (β : ℝ) (Bm s P Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted P ∧
    (∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) ∧
    (∀ t ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ∧
    ∀ t, TVC 𝔼 β (fun t ω => Bm t ω / P t ω) t

/-- Cochrane (2023), eq. (2.7), p. 22: in every equilibrium the real value of nominal debt equals
the present value of surpluses at every date (debt sold at `t` known at `t`). -/
theorem eqm_realDebt_eq_pv (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) :
    (fun ω => Bm t ω / P t ω) = pv 𝔼 β s t := by
  obtain ⟨hPpos, hPad, h23, h24, htvc⟩ := h
  have hflow : FlowX 𝔼 β (fun t ω => Bm t ω / P t ω) s := fun t =>
    (flow_iff_real_x 𝔼 hPO (hPpos t) (hPad t) (hB1 t) (h23 t)).mp (h24 t)
  exact (valuation_iff 𝔼 hMC hβ hs hsad).mp ⟨hflow, htvc⟩ t

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds": in every
equilibrium `P_t = B_{t−1}/pv_t` wherever `B_{t−1} ≠ 0`. -/
theorem eqm_price_eq (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) {t : ℕ} {ω : Ω}
    (hB : Bm t ω ≠ 0) : P t ω = Bm t ω / pv 𝔼 β s t ω := by
  have hx := congrFun (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h t) ω
  have hP := (h.1 t ω).ne'
  rw [← hx]
  field_simp

/-- Cochrane (2023), p. 22: with positive nominal debt, every equilibrium has a positive
present value of surpluses at every date and state. -/
theorem eqm_pv_pos (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) : 0 < pv 𝔼 β s t ω := by
  rw [← congrFun (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h t) ω]
  exact div_pos (hBpos t ω) (h.1 t ω)

/-- Cochrane (2023), p. 22 (the implicit hypothesis that the present value is positive, survey
item E3 for the two-period analogue): with positive nominal debt, if the present value of
surpluses is nonpositive at some date and state, there is no equilibrium. -/
theorem no_eqm_of_pv_nonpos (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω) {t : ℕ}
    {ω : Ω} (hpv : pv 𝔼 β s t ω ≤ 0) : ∀ P Q, ¬ IsEqm 𝔼 β Bm s P Q := fun _ _ h =>
  absurd (eqm_pv_pos 𝔼 hPO hMC hβ hs hsad hB1 hBpos h t ω) (not_lt.mpr hpv)

/-- Cochrane (2023), p. 22: the candidate equilibrium price level `P_t = B_{t−1}/pv_t`. -/
noncomputable def eqmPrice (β : ℝ) (Bm s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => Bm t ω / pv 𝔼 β s t ω

/-- Cochrane (2023), eq. (2.3), p. 22: the bond price at the candidate equilibrium price level,
`Q_t = β E_t(P_t/P_{t+1})`. -/
noncomputable def eqmBondPrice (β : ℝ) (Bm s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => β • 𝔼.E t (fun ω => eqmPrice 𝔼 β Bm s t ω / eqmPrice 𝔼 β Bm s (t + 1) ω)

/-- Cochrane (2023), p. 22, existence: with positive nominal debt known when issued, adapted
absolutely summable surpluses with positive present value at every date and state, the price
level `P_t = B_{t−1}/pv_t` with bond price `Q_t = β E_t(P_t/P_{t+1})` is an equilibrium. -/
theorem eqm_of_pv_pos (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (hB0 : ∀ t, 𝔼.E t (Bm t) = Bm t)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) :
    IsEqm 𝔼 β Bm s (eqmPrice 𝔼 β Bm s) (eqmBondPrice 𝔼 β Bm s) := by
  set P : ℕ → Ω → ℝ := eqmPrice 𝔼 β Bm s with hPdef
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => div_pos (hBpos t ω) (hpv t ω)
  have hPad : 𝔼.Adapted P := fun t =>
    known_div 𝔼 hPO hFK (hB0 t) (E_pv_self 𝔼 hMC hβ hs t)
  have hx : (fun t ω => Bm t ω / P t ω) = pv 𝔼 β s := by
    funext t ω
    have := (hBpos t ω).ne'
    have := (hpv t ω).ne'
    simp only [hPdef, eqmPrice]
    field_simp
  refine ⟨hPpos, hPad, fun t => rfl, fun t => ?_, fun t => ?_⟩
  · refine (flow_iff_real_x 𝔼 hPO (Q := eqmBondPrice 𝔼 β Bm s) (hPpos t) (hPad t) (hB1 t)
      rfl).mpr ?_
    have hfl := pv_flow 𝔼 hMC hβ hs hsad t
    have h1 := congrFun hx t
    have h2 := congrFun hx (t + 1)
    rw [h1, h2]
    exact hfl
  · rw [hx]
    exact pv_tvc 𝔼 hMC hβ hs t

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds", as the
fiscal-theory determination of the price level: given positive nominal debt (known when issued)
and adapted, absolutely summable surpluses with positive present value, there is exactly one
equilibrium price level and bond-price process. This is uniqueness of the price level given
surpluses, not uniqueness among bounded solutions of a difference equation. -/
theorem existsUnique_eqm (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (hB0 : ∀ t, 𝔼.E t (Bm t) = Bm t)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) :
    ∃! PQ : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), IsEqm 𝔼 β Bm s PQ.1 PQ.2 := by
  refine ⟨(eqmPrice 𝔼 β Bm s, eqmBondPrice 𝔼 β Bm s),
    eqm_of_pv_pos 𝔼 hPO hFK hMC hβ hs hsad hB0 hB1 hBpos hpv, ?_⟩
  rintro ⟨P, Q⟩ h
  have hP : P = eqmPrice 𝔼 β Bm s := by
    funext t ω
    exact eqm_price_eq 𝔼 hPO hMC hβ hs hsad hB1 h (hBpos t ω).ne'
  have hQ : Q = fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := funext h.2.2.1
  rw [hQ, hP]
  rfl

/-! ### The household present-value budget constraint (2.8) -/

/-- Cochrane (2023), eqs. (2.2) and (2.8), pp. 21–23: with no money held overnight, the bond
price (2.3), a positive price level known at `t` and `B_t` known at `t`, the household flow
constraint (2.2) at `t` is the real flow `x_t = (c_t − y + s_t) + β E_t x_{t+1}`. -/
theorem hh_flow_iff_real (hPO : 𝔼.PullOut) {β y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ}
    (hM : ∀ t ω, Mm t ω = 0) (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) :
    (∀ ω, Mm t ω + Bm t ω + P t ω * y =
        P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω) ↔
      (fun ω => Bm t ω / P t ω) =
        (fun ω => c t ω - y + s t ω) + β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  rw [← flow_iff_real_x 𝔼 hPO (s := fun t ω => c t ω - y + s t ω) hPpos hPad hB h23]
  refine forall_congr' fun ω => ?_
  rw [hM t ω, hM (t + 1) ω]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (2.8), p. 23 ("add the transversality condition to the household flow
budget constraint (2.2), iterate forward"): with no money held, (2.3), positive adapted prices,
debt known when sold, and adapted absolutely summable net demands `d_t = c_t − y + s_t`, the
household flow constraints plus the TVC at every date hold iff
`B_{t−1}/P_t = ∑_j β^j E_t(c_{t+j} − y + s_{t+j})` at every date. -/
theorem hh_pv_iff (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β y : ℝ} (hβ : 0 ≤ β)
    {Mm Bm P c s Q : ℕ → Ω → ℝ} (hM : ∀ t ω, Mm t ω = 0) (hPpos : ∀ t ω, 0 < P t ω)
    (hPad : 𝔼.Adapted P) (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : ∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (hd : AbsSummable 𝔼 β fun t ω => c t ω - y + s t ω)
    (hdad : 𝔼.Adapted fun t ω => c t ω - y + s t ω) :
    (HhFlow y Mm Bm P c s Q ∧ ∀ t, TVC 𝔼 β (fun t ω => Bm t ω / P t ω) t) ↔
      ∀ t, (fun ω => Bm t ω / P t ω) = pv 𝔼 β (fun t ω => c t ω - y + s t ω) t := by
  rw [← valuation_iff 𝔼 hMC hβ hd hdad]
  have hfl : HhFlow y Mm Bm P c s Q ↔ FlowX 𝔼 β (fun t ω => Bm t ω / P t ω)
      (fun t ω => c t ω - y + s t ω) := by
    constructor
    · intro h t
      exact (hh_flow_iff_real 𝔼 hPO hM (hPpos t) (hPad t) (hB1 t) (h23 t)).mp (h t)
    · intro h t
      exact (hh_flow_iff_real 𝔼 hPO hM (hPpos t) (hPad t) (hB1 t) (h23 t)).mpr (h t)
  rw [hfl]

/-- Cochrane (2023), p. 23, "If the value of debt is greater than present value of surpluses,
then the household has extra wealth, which they try to spend on consumption greater than
endowment": if (2.8) holds and `B_{t−1}/P_t > ∑_j β^j E_t s_{t+j}`, then the present value of
planned excess consumption `∑_j β^j (E_t c_{t+j} − y)` is positive, so `E_t c_{t+j} > y` at some
date `t + j`. -/
theorem excess_demand_of_gap {β y : ℝ} (hβ : 0 ≤ β) {c s : ℕ → Ω → ℝ} {x : ℝ} {t : ℕ}
    {ω : Ω} (hs : AbsSummable 𝔼 β s)
    (hcs : Summable fun j : ℕ => β ^ j * (𝔼.E t (c (t + j)) ω - y))
    (h28 : x = pv 𝔼 β (fun t ω => c t ω - y + s t ω) t ω) (hgap : pv 𝔼 β s t ω < x) :
    0 < ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) ∧ ∃ j, y < 𝔼.E t (c (t + j)) ω := by
  have hterm : ∀ j, β ^ j * 𝔼.E t (fun ω => c (t + j) ω - y + s (t + j) ω) ω =
      β ^ j * (𝔼.E t (c (t + j)) ω - y) + β ^ j * 𝔼.E t (s (t + j)) ω := by
    intro j
    have : (fun ω => c (t + j) ω - y + s (t + j) ω) = c (t + j) - (fun _ => y) + s (t + j) :=
      rfl
    rw [this, map_add, map_sub, 𝔼.const]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hsum : pv 𝔼 β (fun t ω => c t ω - y + s t ω) t ω =
      ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) + pv 𝔼 β s t ω := by
    simp only [pv_apply]
    rw [← hcs.tsum_add (summable_terms 𝔼 hβ hs t ω)]
    exact tsum_congr hterm
  have hpos : 0 < ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) := by linarith
  refine ⟨hpos, ?_⟩
  by_contra hne
  push Not at hne
  have : ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) ≤ 0 :=
    tsum_nonpos fun j => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ j)
      (by linarith [hne j])
  linarith

/-! ### Online Appendix A1.1: the transversality condition -/

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the "no-Ponzi" condition
`lim_T E_t β^T B_{T−1}/P_T ≥ 0`, stated without presupposing that the limit exists (as
`liminf ≥ 0`: eventually above `−ε` for every `ε > 0`). -/
def NoPonzi (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ N in atTop, -ε ≤ a N

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the optimality condition
`lim_T E_t β^T B_{T−1}/P_T ≤ 0` (as `limsup ≤ 0`). -/
def NoOverAccumulation (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ N in atTop, a N ≤ ε

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the transversality condition (limit zero)
holds iff both the no-Ponzi condition (`≥ 0`) and the optimality condition (`≤ 0`) hold. -/
theorem tendsto_zero_iff_noPonzi_and_optimal (a : ℕ → ℝ) :
    Tendsto a atTop (𝓝 0) ↔ NoPonzi a ∧ NoOverAccumulation a := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨N, hN⟩ := h ε hε
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      linarith
    · obtain ⟨N, hN⟩ := h ε hε
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      linarith
  · rintro ⟨h1, h2⟩ ε hε
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (h1 (ε / 2) (by linarith))
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (h2 (ε / 2) (by linarith))
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have a1 := hN1 n (le_of_max_le_left hn)
    have a2 := hN2 n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the TVC (2.6) at `t` holds iff in every
state both the no-Ponzi and the optimality halves hold. -/
theorem tvc_iff_noPonzi_and_optimal (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) :
    TVC 𝔼 β x t ↔ ∀ ω, NoPonzi (fun N => β ^ N * 𝔼.E t (x (t + N)) ω) ∧
      NoOverAccumulation (fun N => β ^ N * 𝔼.E t (x (t + N)) ω) :=
  forall_congr' fun _ => tendsto_zero_iff_noPonzi_and_optimal _

/-- Cochrane (2023), p. 22, "Non-negative debt `B_t ≥ 0` rules out a negative value", and Online
Appendix A1.1, p. 555 (the no-Ponzi half is a genuine budget constraint): with `B ≥ 0`,
`P > 0` and `β ≥ 0` every term `β^N E_t B_{t+N−1}/P_{t+N}` is nonnegative, so the no-Ponzi
condition holds automatically. -/
theorem noPonzi_of_nonneg_debt {β : ℝ} (hβ : 0 ≤ β) {Bm P : ℕ → Ω → ℝ}
    (hB : ∀ t ω, 0 ≤ Bm t ω) (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (ω : Ω) :
    NoPonzi (fun N => β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω) := by
  intro ε hε
  refine Filter.Eventually.of_forall fun N => ?_
  have : 0 ≤ β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω :=
    mul_nonneg (pow_nonneg hβ N)
      (E_nonneg 𝔼 (fun ω => div_nonneg (hB _ ω) (hP _ ω).le) ω)
  linarith

/-- Cochrane (2023), Online Appendix A1.1, eqs. (1.1)–(1.2), p. 554, the finite-horizon identity
(iterating the household flow (1.1)): with `d_t = c_t + s_t − y`,
`B_{t−1}/P_t = ∑_{j=0}^{T} β^j E_t d_{t+j} + β^{T+1} E_t B_{t+T}/P_{t+T+1}`. The printed (1.2)
has `R^{−T}` on the terminal term; the exponent is `T + 1` (survey E4, see
`printed_A1_2_false`). -/
theorem hh_iterate {β : ℝ} {x d : ℕ → Ω → ℝ} (hd : 𝔼.Adapted d) (h : FlowX 𝔼 β x d)
    (t T : ℕ) :
    x t = (∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (d (t + j))) +
      β ^ (T + 1) • 𝔼.E t (x (t + T + 1)) :=
  telescope 𝔼 h (adapted_of_flow 𝔼 hd h t) (T + 1)

/-- Cochrane (2023), Online Appendix A1.1, eq. (1.2), p. 554, and p. 28 (survey E4): the printed
terminal weight `β^T` (`R^{−T}`) is wrong. Under perfect foresight with `β = 1/2`, `d ≡ 0` and
`x_t = 2^t` the flow condition holds, but `x_0 ≠ ∑_{j ≤ 0} β^j d_j + β^0 x_1`. -/
theorem printed_A1_2_false :
    FlowX perfectForesight (1 / 2 : ℝ) (fun t _ => (2 : ℝ) ^ t) (fun _ _ => 0) ∧
      (fun _ => (2 : ℝ) ^ 0) ≠
        (∑ j ∈ Finset.range (0 + 1), (1 / 2 : ℝ) ^ j •
          perfectForesight.E 0 ((fun _ _ => (0 : ℝ)) (0 + j))) +
        (1 / 2 : ℝ) ^ 0 • perfectForesight.E 0 ((fun t (_ : Unit) => (2 : ℝ) ^ t) (0 + 0 + 1)) := by
  refine ⟨fun t => ?_, fun h => ?_⟩
  · funext ω
    change (2 : ℝ) ^ t = 0 + 1 / 2 * 2 ^ (t + 1)
    rw [pow_succ]
    ring
  · have := congrFun h ()
    change (2 : ℝ) ^ 0 = (∑ j ∈ Finset.range (0 + 1), (1 / 2 : ℝ) ^ j * 0) +
      (1 / 2) ^ 0 * 2 ^ (0 + 0 + 1) at this
    norm_num at this

/-- Cochrane (2023), Online Appendix A1.1, p. 555, the explosion with constant surpluses
(also under uncertainty): if `x_t = s + β E_t x_{t+1}` at every date with constant `s` and
`0 < β < 1`, then `E_t x_{t+n} − s/(1−β) = β^{−n} (x_t − s/(1−β))`. -/
theorem const_explodes {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t n : ℕ) :
    𝔼.E t (x (t + n)) - (fun _ => s / (1 - β)) =
      (β ^ n)⁻¹ • (x t - fun _ => s / (1 - β)) := by
  have hxt := adapted_of_flow 𝔼 (fun t => 𝔼.const t s) h t
  have hb : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
  have hb1 : 1 - β ≠ 0 := by linarith
  have hb2 : β - 1 ≠ 0 := by linarith
  have htel := telescope 𝔼 h hxt n
  have hsum : (∑ j ∈ Finset.range n, β ^ j • 𝔼.E t ((fun _ _ => s : ℕ → Ω → ℝ) (t + j))) =
      fun _ => s * (1 - β ^ n) / (1 - β) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, 𝔼.const, smul_eq_mul]
    rw [← Finset.sum_mul, geom_sum_eq hβ1.ne]
    field_simp
    ring
  rw [hsum] at htel
  funext ω
  have hω := congrFun htel ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hω]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix A1.1, p. 555, "The terminal or transversality term does not
go to zero": with constant surpluses, `β^n E_t x_{t+n} → x_t − s/(1−β)`. -/
theorem const_terminal_limit {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t : ℕ) (ω : Ω) :
    Tendsto (fun n : ℕ => β ^ n * 𝔼.E t (x (t + n)) ω) atTop (𝓝 (x t ω - s / (1 - β))) := by
  have hb : ∀ n, β ^ n * 𝔼.E t (x (t + n)) ω =
      β ^ n * (s / (1 - β)) + (x t ω - s / (1 - β)) := by
    intro n
    have := congrFun (const_explodes 𝔼 hβ0 hβ1 h t n) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    have h2 : 𝔼.E t (x (t + n)) ω = s / (1 - β) + (β ^ n)⁻¹ * (x t ω - s / (1 - β)) := by
      linarith
    rw [h2]
    field_simp
  simp_rw [hb]
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (s / (1 - β))).add_const (x t ω - s / (1 - β))
  simpa using hlim

/-- Cochrane (2023), Online Appendix A1.1, p. 555: with constant surpluses the TVC holds at `t`
iff `x_t = s/(1−β)` in every state, i.e. iff the price level is the equilibrium one; at a too-low
price level (`x_t > s/(1−β)`) the valuation equation acquires the extra term
`x_t − s/(1−β)`. -/
theorem const_tvc_iff {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t : ℕ) :
    TVC 𝔼 β x t ↔ ∀ ω, x t ω = s / (1 - β) := by
  constructor
  · intro htvc ω
    have := tendsto_nhds_unique (const_terminal_limit 𝔼 hβ0 hβ1 h t ω) (htvc ω)
    linarith
  · intro hx ω
    have := const_terminal_limit 𝔼 hβ0 hβ1 h t ω
    rwa [hx ω, sub_self] at this

/-- Cochrane (2023), Online Appendix A1.1, p. 555 (display after "taking the limit"): with
constant surpluses the finite-horizon valuation converges to
`x_t = ∑_j β^j s + (x_t − s/(1−β))`. -/
theorem const_valuation_limit {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (fun j : ℕ => β ^ j * s) (s / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right s
  simpa [div_eq_inv_mul] using this

/-! ### The deviation argument (A1.1, (1.3)), perfect foresight -/

/-- Cochrane (2023), Online Appendix A1.1, p. 556: under perfect foresight with constant
surplus `s` and consumption `y + Δc`, real debt evolves by `z_n = s + Δc + β z_{n+1}`; every such
path from `z_0 = x₀` is `z_n = K + β^{−n}(x₀ − K)` with `K = (s + Δc)/(1 − β)`. -/
theorem deviation_closed_form {β s Δc x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z : ℕ → ℝ}
    (hz0 : z 0 = x₀) (hz : ∀ n, z n = s + Δc + β * z (n + 1)) (n : ℕ) :
    z n = (s + Δc) / (1 - β) + (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β)) := by
  have hb1 : 1 - β ≠ 0 := by linarith
  induction n with
  | zero => simp [hz0]
  | succ n ih =>
    have h := hz n
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    have hz1 : z (n + 1) = (z n - (s + Δc)) / β := by
      field_simp
      linarith
    rw [hz1, ih, pow_succ]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix A1.1, eq. (1.3), p. 556: if the initial value of debt
satisfies (1.3) `x₀ ≥ (s + Δc)/(1 − β)` (and `x₀ ≥ 0`), the path
`z_n = K + β^{−n}(x₀ − K)` satisfies the flow constraint with consumption `y + Δc` and keeps debt
nonnegative, `z_n ≥ x₀ ≥ 0`: the deviation is feasible. -/
theorem deviation_feasible {β s Δc x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 ≤ x₀)
    (h13 : (s + Δc) / (1 - β) ≤ x₀) :
    let z : ℕ → ℝ := fun n => (s + Δc) / (1 - β) + (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β))
    z 0 = x₀ ∧ (∀ n, z n = s + Δc + β * z (n + 1)) ∧ ∀ n, x₀ ≤ z n ∧ 0 ≤ z n := by
  intro z
  have hb1 : 1 - β ≠ 0 := by linarith
  refine ⟨by simp [z], fun n => ?_, fun n => ?_⟩
  · have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    simp only [z, pow_succ]
    field_simp
    ring
  · have hge : 1 ≤ (β ^ n)⁻¹ := one_le_inv₀ (pow_pos hβ0 n) |>.mpr (pow_le_one₀ hβ0.le hβ1.le)
    have hk : 0 ≤ x₀ - (s + Δc) / (1 - β) := by linarith
    have : x₀ - (s + Δc) / (1 - β) ≤ (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β)) := by
      nlinarith
    constructor <;> simp only [z] <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "improves utility": for strictly increasing
`u` and `Δc > 0`, consuming `y + Δc` forever gives strictly higher utility
`∑ β^n u(y + Δc) > ∑ β^n u(y)` (`0 ≤ β < 1`). -/
theorem deviation_improves {β y Δc : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : StrictMono u) (hΔ : 0 < Δc) :
    ∑' n : ℕ, β ^ n * u y < ∑' n : ℕ, β ^ n * u (y + Δc) := by
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
  have h1 : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
  exact mul_lt_mul_of_pos_left (hu (by linarith)) h1

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "the increase `Δc` by which (1.3) holds with
equality is the optimal choice": let `Δc* = (1 − β)x₀ − s` and `c* = y + Δc*`. If `u` has a
supergradient `g ≥ 0` at `c*` (as for concave increasing `u`, with `g = u'(c*)`), then every
feasible plan (flow constraint `z_n = c_n − y + s + β z_{n+1}` from `z_0 = x₀` with `z ≥ 0`, and
summable discounted consumption and utility) gives no more utility than consuming `c*` forever. -/
theorem deviation_optimal {β y s x₀ g : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hg : 0 ≤ g) (hsup : ∀ c, u c ≤ u (y + ((1 - β) * x₀ - s)) +
      g * (c - (y + ((1 - β) * x₀ - s))))
    {c z : ℕ → ℝ} (hz0 : z 0 = x₀) (hz : ∀ n, z n = c n - y + s + β * z (n + 1))
    (hznn : ∀ n, 0 ≤ z n) (hcs : Summable fun n => β ^ n * c n)
    (hus : Summable fun n => β ^ n * u (c n)) :
    ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * u (y + ((1 - β) * x₀ - s)) := by
  set cs := y + ((1 - β) * x₀ - s) with hcs_def
  have hgeo : Summable fun n : ℕ => β ^ n := summable_geometric_of_lt_one hβ0 hβ1
  have hb1 : (1 - β) ≠ 0 := by linarith
  -- the budget: partial sums of discounted net demand are at most x₀
  have htel : ∀ N, x₀ = ∑ n ∈ Finset.range N, β ^ n * (c n - y + s) + β ^ N * z N := by
    intro N
    induction N with
    | zero => simp [hz0]
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, hz N, pow_succ]
      ring
  have hds : Summable fun n => β ^ n * (c n - y + s) := by
    have := hcs.add (hgeo.mul_right (s - y))
    refine this.congr fun n => ?_
    ring
  have hbud : ∑' n, β ^ n * (c n - y + s) ≤ x₀ := by
    refine hds.tsum_le_of_sum_range_le fun N => ?_
    have := htel N
    have : 0 ≤ β ^ N * z N := mul_nonneg (pow_nonneg hβ0 N) (hznn N)
    linarith
  -- the same sum for the constant plan equals x₀
  have hstar : ∑' n : ℕ, β ^ n * (cs - y + s) = x₀ := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, hcs_def]
    field_simp
    ring
  have hdiff : ∑' n : ℕ, β ^ n * (c n - cs) ≤ 0 := by
    have hcs' : Summable fun n : ℕ => β ^ n * (cs - y + s) := hgeo.mul_right _
    have : ∑' n : ℕ, β ^ n * (c n - cs) =
        ∑' n, β ^ n * (c n - y + s) - ∑' n : ℕ, β ^ n * (cs - y + s) := by
      rw [← hds.tsum_sub hcs']
      exact tsum_congr fun n => by ring
    linarith
  have hsum2 : Summable fun n : ℕ => β ^ n * (u cs + g * (c n - cs)) := by
    have := (hgeo.mul_right (u cs - g * cs)).add (hcs.mul_left g)
    refine this.congr fun n => ?_
    ring
  calc ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * (u cs + g * (c n - cs)) :=
        Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hsup (c n))
          (pow_nonneg hβ0 n)) hus hsum2
    _ = ∑' n : ℕ, β ^ n * u cs + g * ∑' n : ℕ, β ^ n * (c n - cs) := by
        have hd2 : Summable fun n : ℕ => β ^ n * (c n - cs) := by
          have := hcs.sub (hgeo.mul_right cs)
          refine this.congr fun n => ?_
          ring
        rw [← tsum_mul_left, ← (hgeo.mul_right (u cs)).tsum_add (hd2.mul_left g)]
        exact tsum_congr fun n => by ring
    _ ≤ ∑' n : ℕ, β ^ n * u cs := by
        have := mul_nonpos_of_nonneg_of_nonpos hg hdiff
        linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556 (concave utility): for `u` concave on `ℝ` with
derivative `g` at `x`, the tangent line lies above the graph, `u c ≤ u x + g (c − x)`. -/
theorem concave_le_tangent {u : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ u) {x g : ℝ}
    (hg : HasDerivAt u g x) (c : ℝ) : u c ≤ u x + g * (c - x) := by
  rcases lt_trichotomy c x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ c) (Set.mem_univ x) h hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst h
    simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ c) h hg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: a monotone function has a nonnegative
derivative wherever it is differentiable. -/
theorem deriv_nonneg_of_monotone {u : ℝ → ℝ} (hm : Monotone u) {x g : ℝ}
    (hg : HasDerivAt u g x) : 0 ≤ g := by
  have h := hg.tendsto_slope_zero_right
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have : u x ≤ u (x + t) := hm (by linarith)
  have : 0 ≤ t⁻¹ * (u (x + t) - u x) :=
    mul_nonneg (inv_nonneg.mpr ht'.le) (by linarith)
  simpa [smul_eq_mul] using this

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "the increase `Δc` by which (1.3) holds with
equality is the optimal choice", under the book's assumptions on utility: `u` concave and
increasing, differentiable at `c* = y + ((1 − β)x₀ − s)`. Every feasible plan (flow constraint
from `z_0 = x₀`, nonnegative debt, summable discounted consumption and utility) gives no more
utility than consuming `c*` forever. -/
theorem deviation_optimal_concave {β y s x₀ g : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hg : HasDerivAt u g (y + ((1 - β) * x₀ - s)))
    {c z : ℕ → ℝ} (hz0 : z 0 = x₀) (hz : ∀ n, z n = c n - y + s + β * z (n + 1))
    (hznn : ∀ n, 0 ≤ z n) (hcs : Summable fun n => β ^ n * c n)
    (hus : Summable fun n => β ^ n * u (c n)) :
    ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * u (y + ((1 - β) * x₀ - s)) :=
  deviation_optimal hβ0 hβ1 (deriv_nonneg_of_monotone hmono hg) (concave_le_tangent hconc hg)
    hz0 hz hznn hcs hus

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "with `Δc > 0`, i.e. `c > y`, this choice is
not an equilibrium, as the goods market does not clear": the optimal consumption
`y + ((1 − β)x₀ − s)` exceeds the endowment iff the price level is too low,
`x₀ > s/(1 − β)`; it equals `y` iff `x₀ = s/(1−β)`. -/
theorem tooLow_not_equilibrium {β y s x₀ : ℝ} (hβ1 : β < 1) :
    (y < y + ((1 - β) * x₀ - s) ↔ s / (1 - β) < x₀) ∧
      (y + ((1 - β) * x₀ - s) = y ↔ x₀ = s / (1 - β)) := by
  have hb : 0 < 1 - β := by linarith
  constructor
  · rw [div_lt_iff₀ hb]
    constructor <;> intro h <;> linarith
  · rw [eq_div_iff hb.ne']
    constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: the optimal plan `Δc* = (1 − β)x₀ − s` keeps
real debt constant at `x₀`, so it satisfies the transversality condition. -/
theorem optimal_plan_tvc {β s x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    let z : ℕ → ℝ := fun n => (s + ((1 - β) * x₀ - s)) / (1 - β) +
      (β ^ n)⁻¹ * (x₀ - (s + ((1 - β) * x₀ - s)) / (1 - β))
    (∀ n, z n = x₀) ∧ Tendsto (fun n => β ^ n * z n) atTop (𝓝 0) := by
  intro z
  have hb1 : 1 - β ≠ 0 := by linarith
  have hz : ∀ n, z n = x₀ := fun n => by
    simp only [z]
    field_simp
    ring
  refine ⟨hz, ?_⟩
  simp_rw [hz]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const x₀

/-! ### Optimisation implies the transversality condition (perfect foresight) -/

/-- Cochrane (2023), p. 22, "Household maximization, budget constraint, and equilibrium `c_t = y`
also imply the household transversality condition (2.6). If the term on the left is positive,
then the consumer can raise consumption at time `t`, lower this terminal value, and raise
utility", proved under perfect foresight: if `(c, b)` is an optimal household plan
(`Environment.HhOptimal`), `u` is strictly increasing, prices are positive, the bond price is
`Q_n = β P_n/P_{n+1}` (2.3), and discounted net demands `c_n − y + s_n` are summable, then
`lim_N β^N B_{N−1}/P_N = 0`. (If the limit were positive, consuming a little more at a late date
`T` and holding correspondingly less debt afterwards would be feasible and strictly better.) -/
theorem tvc_of_optimal {β y b₀ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u)
    {P s Q c b : ℕ → ℝ} (hopt : HhOptimal β y u P s Q b₀ c b) (hP : ∀ n, 0 < P n)
    (hQ : ∀ n, Q n = β * (P n / P (n + 1)))
    (hd : Summable fun n => β ^ n * (c n - y + s n)) :
    Tendsto (fun N => β ^ N * (b N / P N)) atTop (𝓝 0) := by
  obtain ⟨⟨hb0, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  set x : ℕ → ℝ := fun n => b n / P n with hxdef
  set d : ℕ → ℝ := fun n => c n - y + s n with hddef
  have hx : ∀ n, x n = d n + β * x (n + 1) := by
    intro n
    have h1 := hflow n
    have hP0 := (hP n).ne'
    have hP1 := (hP (n + 1)).ne'
    have key : b n = P n * d n + β * P n * x (n + 1) := by
      rw [hQ n] at h1
      simp only [hddef, hxdef]
      field_simp at h1 ⊢
      linear_combination h1
    simp only [hxdef] at key ⊢
    rw [key]
    field_simp
  have htel : ∀ N, x 0 = ∑ n ∈ Finset.range N, β ^ n * d n + β ^ N * x N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, hx N, pow_succ]
      ring
  set L := x 0 - ∑' n, β ^ n * d n with hL
  have hlim : Tendsto (fun N => β ^ N * x N) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := x 0)).sub hd.hasSum.tendsto_sum_nat
    refine h.congr fun N => ?_
    have := htel N
    simp only [hddef] at this ⊢
    linarith
  have hL0 : 0 ≤ L := ge_of_tendsto' hlim fun N =>
    mul_nonneg (pow_nonneg hβ.le N) (div_nonneg (hbnn N) (hP N).le)
  rcases hL0.lt_or_eq with hLpos | hLzero
  · exfalso
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (hlim.eventually (lt_mem_nhds (show L / 2 < L by linarith)))
    set δ : ℝ := L / 2 / β ^ T with hδ
    have hbT : 0 < β ^ T := pow_pos hβ T
    have hδpos : 0 < δ := div_pos (by linarith) hbT
    set c' : ℕ → ℝ := fun n => c n + if n = T then δ else 0 with hc'
    set b' : ℕ → ℝ := fun n => b n - if T < n then P n * δ * β ^ T / β ^ n else 0 with hb'
    have hfeas : HhFeasible y P s Q b₀ c' b' := by
      refine ⟨by simp [hb', hb0], fun n => ?_, fun n => ?_⟩
      · have h1 := hflow n
        have hP0 := (hP n).ne'
        have hP1 := (hP (n + 1)).ne'
        have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
        rcases lt_trichotomy n T with hn | hn | hn
        · have e1 : ¬ T < n := by omega
          have e2 : ¬ T < n + 1 := by omega
          have e3 : n ≠ T := by omega
          simp only [hc', hb', e1, e2, e3, ↓reduceIte, add_zero, sub_zero]
          exact h1
        · subst hn
          have e2 : n < n + 1 := by omega
          simp only [hc', hb', lt_irrefl, e2, ↓reduceIte, sub_zero]
          rw [hQ n] at h1 ⊢
          rw [pow_succ]
          field_simp at h1 ⊢
          linear_combination h1
        · have e2 : T < n + 1 := by omega
          have e3 : n ≠ T := by omega
          simp only [hc', hb', hn, e2, e3, ↓reduceIte, add_zero]
          rw [hQ n] at h1 ⊢
          rw [pow_succ]
          field_simp at h1 ⊢
          linear_combination (β ^ n) * h1
      · simp only [hb']
        split_ifs with hn
        · have hgt := hT n hn.le
          simp only [hxdef] at hgt
          have hbn : 0 < β ^ n := pow_pos hβ n
          have hPn := hP n
          have : P n * δ * β ^ T / β ^ n ≤ b n := by
            rw [div_le_iff₀ hbn]
            have e : δ * β ^ T = L / 2 := by rw [hδ]; field_simp
            have h3 : L / 2 < β ^ n * b n / P n := by
              calc L / 2 < β ^ n * (b n / P n) := hgt
                _ = β ^ n * b n / P n := by ring
            rw [lt_div_iff₀ hPn] at h3
            nlinarith
          linarith
        · simpa using hbnn n
    have hgain : HasSum (fun n => β ^ n * u (c' n))
        (∑' n, β ^ n * u (c n) + β ^ T * (u (c T + δ) - u (c T))) := by
      have hg : HasSum (fun n => β ^ n * u (c' n) - β ^ n * u (c n))
          (β ^ T * (u (c T + δ) - u (c T))) := by
        have h := hasSum_single (f := fun n => β ^ n * u (c' n) - β ^ n * u (c n)) T
          (fun n hn => by simp [hc', hn])
        convert h using 1
        simp only [hc', ↓reduceIte]
        ring
      convert hsum.hasSum.add hg using 1
      funext n
      ring
    have h1 := hbest c' b' hfeas hgain.summable
    rw [hgain.tsum_eq] at h1
    have : 0 < β ^ T * (u (c T + δ) - u (c T)) :=
      mul_pos hbT (sub_pos.mpr (hu (by linarith)))
    linarith
  · rw [← hLzero] at hlim
    exact hlim

/-- Cochrane (2023), eq. (2.7), p. 22, "As a result, we can then iterate (2.5) to (2.7)", derived
from household optimisation under perfect foresight: in an optimal plan at the endowment
(`c = y`) with the bond price (2.3) and summable discounted surpluses,
`B_{−1}/P_0 = ∑_n β^n s_n`. -/
theorem valuation_of_optimal {β y b₀ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u)
    {P s Q b : ℕ → ℝ} (hopt : HhOptimal β y u P s Q b₀ (fun _ => y) b) (hP : ∀ n, 0 < P n)
    (hQ : ∀ n, Q n = β * (P n / P (n + 1))) (hs : Summable fun n => β ^ n * s n) :
    HasSum (fun n => β ^ n * s n) (b₀ / P 0) := by
  have hd : Summable fun n => β ^ n * ((fun _ => y) n - y + s n) := by
    refine hs.congr fun n => ?_
    ring
  have htvc := tvc_of_optimal hβ hu hopt hP hQ hd
  obtain ⟨⟨hb0, hflow, -⟩, -, -⟩ := hopt
  have htel : ∀ N, b 0 / P 0 = ∑ n ∈ Finset.range N, β ^ n * s n + β ^ N * (b N / P N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, pow_succ]
      have h1 := hflow N
      rw [hQ N] at h1
      have hP0 := (hP N).ne'
      have hP1 := (hP (N + 1)).ne'
      have hbN : β ^ N ≠ 0 := pow_ne_zero N hβ.ne'
      have key : b N / P N = s N + β * (b (N + 1) / P (N + 1)) := by
        field_simp at h1 ⊢
        linear_combination h1
      rw [key]
      ring
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, β ^ n * s n) atTop (𝓝 (b₀ / P 0)) := by
    have h := (tendsto_const_nhds (x := b 0 / P 0)).sub htvc
    rw [sub_zero, hb0] at h
    refine h.congr fun N => ?_
    have := htel N
    rw [hb0] at this
    linarith
  rw [tendsto_nhds_unique hlim hs.hasSum.tendsto_sum_nat]
  exact hs.hasSum

/-- Cochrane (2023), p. 22 ("If the term on the left is positive, then the consumer can raise
consumption at time `t`, lower this terminal value, and raise utility") and Online Appendix A1.1,
p. 555, for any `ExpectationSystem`: from a plan satisfying the real household flow
`x_r = d_r + β E_r x_{r+1}` at every date, consume `δ` more at date `t` and hold
`x'_{t+n} = x_{t+n} − δβ^{−n}` (`n ≥ 1`) less debt. The new plan satisfies every flow constraint
from `t` on, lowers the terminal term by exactly `δ`, and is feasible (nonnegative debt) whenever
the old plan carries a pathwise bubble `x_{t+n} ≥ δβ^{−n}`. -/
theorem bubble_deviation {β δ : ℝ} (hβ0 : 0 < β) {x d : ℕ → Ω → ℝ} (h : FlowX 𝔼 β x d)
    (t : ℕ) :
    let x' : ℕ → Ω → ℝ := fun n => x (t + n) - fun _ => δ * (β ^ n)⁻¹
    (x t = d t + (fun _ => δ) + β • 𝔼.E t (x' 1)) ∧
      (∀ n, 1 ≤ n → x' n = d (t + n) + β • 𝔼.E (t + n) (x' (n + 1))) ∧
      (∀ N ω, 1 ≤ N → β ^ N * 𝔼.E t (x' N) ω = β ^ N * 𝔼.E t (x (t + N)) ω - δ) ∧
      ((∀ n ω, 1 ≤ n → δ * (β ^ n)⁻¹ ≤ x (t + n) ω) → ∀ n ω, 1 ≤ n → 0 ≤ x' n ω) := by
  intro x'
  have hb : β ≠ 0 := hβ0.ne'
  refine ⟨?_, fun n _ => ?_, fun N ω hN => ?_, fun hbub n ω hn => ?_⟩
  · funext ω
    have := congrFun (h t) ω
    simp only [x', map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      pow_one] at this ⊢
    rw [this]
    field_simp
    ring
  · funext ω
    have := congrFun (h (t + n)) ω
    simp only [x', map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at this ⊢
    rw [show t + (n + 1) = t + n + 1 by omega, this, pow_succ]
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hb
    field_simp
    ring
  · simp only [x', map_sub, 𝔼.const, Pi.sub_apply]
    have hbn : β ^ N ≠ 0 := pow_ne_zero N hb
    field_simp
  · simp only [x', Pi.sub_apply]
    linarith [hbub n ω hn]

/-! ### Household optimisation under uncertainty (finite state space) -/

/-- Cochrane (2023), p. 21 (expected utility over a finite set of states): on a finite state
space every `E_t` is a finite weighted sum of the values of its argument. -/
theorem E_eq_sum [Fintype Ω] [DecidableEq Ω] (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    𝔼.E t x ω = ∑ ω', x ω' * 𝔼.E t (Pi.single ω' 1) ω := by
  have hx : x = ∑ ω', x ω' • (Pi.single ω' (1 : ℝ) : Ω → ℝ) := by
    funext ω
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [map_smul]
  rfl

/-- Cochrane (2023), p. 22 (limits inside `E_t`, finite state space): if `f_N → g` in every
state, then `E_t f_N → E_t g`. -/
theorem E_tendsto [Finite Ω] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ ω', Tendsto (fun N => f N ω') atTop (𝓝 (g ω'))) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => 𝔼.E t (f N) ω) atTop (𝓝 (𝔼.E t g ω)) := by
  classical
  have := Fintype.ofFinite Ω
  have e : (fun N => 𝔼.E t (f N) ω) =
      fun N => ∑ ω', f N ω' * 𝔼.E t (Pi.single ω' 1) ω := funext fun N => E_eq_sum 𝔼 t (f N) ω
  rw [e, E_eq_sum 𝔼 t g ω]
  exact tendsto_finsetSum _ fun ω' _ => (h ω').mul_const _

/-- Cochrane (2023), p. 21 (differentiating expected utility, finite state space): if
`ε ↦ f ε ω'` has derivative `f' ω'` at `a` in every state, then `ε ↦ E_t (f ε)` has derivative
`E_t f'` at `a`. -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {a : ℝ}
    (h : ∀ ω', HasDerivAt (fun ε => f ε ω') (f' ω') a) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t f' ω) a := by
  classical
  have := Fintype.ofFinite Ω
  have e : (fun ε => 𝔼.E t (f ε) ω) =
      fun ε => ∑ ω', f ε ω' * 𝔼.E t (Pi.single ω' 1) ω := funext fun ε => E_eq_sum 𝔼 t (f ε) ω
  rw [e, E_eq_sum 𝔼 t f' ω]
  exact HasDerivAt.fun_sum fun ω' _ => (h ω').mul_const _

/-- Cochrane (2023), p. 22 (modifying a plan at finitely many dates): if `f'` agrees with the
summable `f` off a finite set `S`, then `∑ f' = ∑ f + ∑_{n ∈ S} (f' n − f n)`. -/
theorem hasSum_of_eq_off_finset {f f' : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (h : ∀ n ∉ S, f' n = f n) : HasSum f' (∑' n, f n + ∑ n ∈ S, (f' n - f n)) := by
  have h2 : HasSum (fun n => f' n - f n) (∑ n ∈ S, (f' n - f n)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [h n hn, sub_self]
  convert hf.hasSum.add h2 using 1
  funext n
  ring

/-- Cochrane (2023), p. 21 (every state has positive probability): the date-0 expectation sees
every state, i.e. a nonnegative variable with zero date-0 expectation in every state is zero.
True for perfect foresight and every finite event tree (`finiteTree_faithful`). -/
def Faithful : Prop :=
  ∀ x : Ω → ℝ, (∀ ω, 0 ≤ x ω) → (∀ ω, 𝔼.E 0 x ω = 0) → ∀ ω, x ω = 0

/-- Cochrane (2023), p. 21: perfect foresight is faithful. -/
theorem perfectForesight_faithful : Faithful perfectForesight :=
  fun _ _ h ω => h ω

/-- Cochrane (2023), p. 21: every finite event tree is faithful (strictly positive
probabilities). -/
theorem finiteTree_faithful {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    Faithful T.toExpectationSystem := by
  classical
  intro x hx h0 ω
  have h := h0 ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at h
  simp only [ExpectationsFiniteTree.FiniteTree.condE, div_eq_zero_iff] at h
  rcases h with h | h
  · unfold ExpectationsFiniteTree.FiniteTree.num at h
    have hnn : ∀ ω' ∈ Finset.univ,
        0 ≤ (if T.info 0 ω' ω then T.prob ω' * x ω' else 0) := fun ω' _ => by
      split_ifs
      · exact mul_nonneg (T.prob_pos ω').le (hx ω')
      · exact le_rfl
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h ω (Finset.mem_univ ω)
    simp only [(T.info 0).refl ω, ↓reduceIte] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (T.prob_pos ω).ne'
    · exact h1
  · exact absurd h (T.mass_pos 0 ω).ne'

/-- Cochrane (2023), p. 21 (a finite economy): information stops growing after date `K`,
`E_t = E_K` for all `t ≥ K`. True for every finite event tree (`finiteTree_infoStable`). -/
def InfoStable (K : ℕ) : Prop := ∀ t, K ≤ t → ∀ x, 𝔼.E t x = 𝔼.E K x

/-- Cochrane (2023), p. 21: perfect foresight is information-stable from date 0. -/
theorem perfectForesight_infoStable : InfoStable perfectForesight 0 :=
  fun _ _ _ => rfl

/-- Cochrane (2023), p. 21: on a finite event tree the refining partitions of a finite set
stabilise, so information stops growing after some date `K`. -/
theorem finiteTree_infoStable {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : ∃ K, InfoStable T.toExpectationSystem K := by
  classical
  let S : ℕ → Finset (Ω' × Ω') := fun t => Finset.univ.filter fun p => T.info t p.1 p.2
  have hsub : ∀ s t, s ≤ t → S t ⊆ S s := fun s t hst p hp => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact T.refines hst _ _ hp
  obtain ⟨K, hK⟩ : ∃ K, ∀ t, (S K).card ≤ (S t).card := by
    have hne : (Set.range fun t => (S t).card).Nonempty := ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨K, hK⟩ := Nat.sInf_mem hne
    have hK' : (S K).card = sInf (Set.range fun t => (S t).card) := hK
    exact ⟨K, fun t => by rw [hK']; exact Nat.sInf_le ⟨t, rfl⟩⟩
  refine ⟨K, fun t ht x => ?_⟩
  have heq : S t = S K := Finset.eq_of_subset_of_card_le (hsub K t ht) (hK t)
  have hinfo : T.info t = T.info K := by
    refine Setoid.ext fun a b => ?_
    have := congrArg (fun F => (a, b) ∈ F) heq
    simpa [S] using this
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  simp only [ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num,
    ExpectationsFiniteTree.FiniteTree.mass]
  rw [hinfo]

/-- Cochrane (2023), eq. (2.2), p. 21, under uncertainty: a state-contingent household plan
`(c, b)` (`b n = B_{n−1}`, no money held) is feasible from initial debt `b₀` if consumption is
known at each date, bonds bought at `n` are known at `n`, the flow constraint holds at every
date and state, and `B ≥ 0`. -/
def SFeasible (y : ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) : Prop :=
  b 0 = b₀ ∧ 𝔼.Adapted c ∧ (∀ n, 𝔼.E n (b (n + 1)) = b (n + 1)) ∧
    (∀ n ω, b n ω + P n ω * y = P n ω * c n ω + P n ω * s n ω + Q n ω * b (n + 1) ω) ∧
    ∀ n ω, 0 ≤ b n ω

/-- Cochrane (2023), p. 21: expected utility `E_0 ∑_t β^t u(c_t)`, written as the infinite sum
over dates `∑_t β^t E_0 u(c_t)` (as a date-0 random variable). -/
noncomputable def expUtil (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑' n, β ^ n * 𝔼.E 0 (fun ω' => u (c n ω')) ω

/-- Cochrane (2023), p. 21, "A representative household maximizes `E ∑ β^t u(c_t)`": a feasible
state-contingent plan with summable expected utility that no other such plan beats in any
date-0 state. -/
def SOptimal (β y : ℝ) (u : ℝ → ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) :
    Prop :=
  SFeasible 𝔼 y P s Q b₀ c b ∧
    (∀ ω, Summable fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c n ω')) ω) ∧
    ∀ c' b', SFeasible 𝔼 y P s Q b₀ c' b' →
      (∀ ω, Summable fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω) →
      ∀ ω, expUtil 𝔼 β u c' ω ≤ expUtil 𝔼 β u c ω

/-- Cochrane (2023), p. 21, "The consumer's first-order conditions", under uncertainty (finite
state space, pull-out, functions of known variables known, faithful `E_0`): if `(c, b)` is
optimal, `u` is differentiable with derivative `u'`, prices and the bond price are positive and
known when set, and the household holds bonds `B_t > 0` in every state, then the nominal Euler
equation holds: `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`. Proof: for every
date-`t` variable `z`, shifting `εz` dollars between consumption at `t` and bonds maturing at
`t + 1` is feasible for small `|ε|` and cannot raise expected utility, so the derivative in
`ε` vanishes; taking `z` equal to the Euler residual and using faithfulness gives the
conditional equation. -/
theorem euler_of_optimal_stoch [Finite Ω] [Nonempty Ω] (hPO : 𝔼.PullOut)
    (hFK : FunctionsKnown 𝔼) (hF : Faithful 𝔼) {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ c, HasDerivAt u (u' c) c) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ c b) (hPpos : ∀ n ω, 0 < P n ω) (hPad : 𝔼.Adapted P)
    {t : ℕ} (hQpos : ∀ ω, 0 < Q t ω) (hQad : 𝔼.E t (Q t) = Q t)
    (hb : ∀ ω, 0 < b (t + 1) ω) :
    Q t * (fun ω => u' (c t ω) / P t ω) =
      β • 𝔼.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) := by
  obtain ⟨⟨hb0, hcad, hbad, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  -- Step A: the first-order condition along every date-`t` deviation `z`
  have stepA : ∀ z : Ω → ℝ, 𝔼.E t z = z → ∀ ω₀,
      β ^ t * 𝔼.E 0 (fun ω => u' (c t ω) * (z ω / P t ω)) ω₀ -
        β ^ (t + 1) * 𝔼.E 0 (fun ω => u' (c (t + 1) ω) * (z ω / (Q t ω * P (t + 1) ω))) ω₀
        = 0 := by
    intro z hz ω₀
    set a₀ : Ω → ℝ := fun ω => z ω / P t ω with ha₀
    set a₁ : Ω → ℝ := fun ω => z ω / (Q t ω * P (t + 1) ω) with ha₁
    set a₂ : Ω → ℝ := fun ω => z ω / Q t ω with ha₂
    have ha₀k : 𝔼.E t a₀ = a₀ := known_div 𝔼 hPO hFK hz (hPad t)
    have hQ1 : 𝔼.E (t + 1) (Q t * P (t + 1)) = Q t * P (t + 1) := by
      rw [hPO (t + 1) _ _ (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hQad), hPad (t + 1)]
    have ha₁k : 𝔼.E (t + 1) a₁ = a₁ :=
      known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hz) hQ1
    have ha₂k : 𝔼.E t a₂ = a₂ := known_div 𝔼 hPO hFK hz hQad
    obtain ⟨ωm, hωm⟩ := Finite.exists_min (fun ω => Q t ω * b (t + 1) ω / (|z ω| + 1))
    set r := Q t ωm * b (t + 1) ωm / (|z ωm| + 1) with hr
    have hrpos : 0 < r := div_pos (mul_pos (hQpos ωm) (hb ωm)) (by positivity)
    let cε : ℝ → ℕ → Ω → ℝ := fun ε n ω =>
      c n ω + (if n = t then ε * a₀ ω else if n = t + 1 then -(ε * a₁ ω) else 0)
    let bε : ℝ → ℕ → Ω → ℝ := fun ε n ω => b n ω - (if n = t + 1 then ε * a₂ ω else 0)
    have hct : ∀ ε ω, cε ε t ω = c t ω + ε * a₀ ω := fun ε ω => by simp [cε]
    have hct1 : ∀ ε ω, cε ε (t + 1) ω = c (t + 1) ω - ε * a₁ ω := fun ε ω => by
      simp [cε, sub_eq_add_neg]
    have hcn : ∀ ε n, n ≠ t → n ≠ t + 1 → cε ε n = c n := fun ε n h1 h2 => by
      funext ω
      simp [cε, h1, h2]
    have hbt1 : ∀ ε ω, bε ε (t + 1) ω = b (t + 1) ω - ε * a₂ ω := fun ε ω => by simp [bε]
    have hbn : ∀ ε n, n ≠ t + 1 → bε ε n = b n := fun ε n h => by
      funext ω
      simp [bε, h]
    have hfeas : ∀ ε, |ε| < r → SFeasible 𝔼 y P s Q b₀ (cε ε) (bε ε) := by
      intro ε hε
      refine ⟨by rw [hbn ε 0 (by omega), hb0], fun n => ?_, fun n => ?_, fun n ω => ?_,
        fun n ω => ?_⟩
      · by_cases h1 : n = t
        · subst h1
          have e : cε ε n = c n + ε • a₀ := by
            funext ω
            rw [hct]
            rfl
          rw [e, map_add, map_smul, hcad n, ha₀k]
        · by_cases h2 : n = t + 1
          · subst h2
            have e : cε ε (t + 1) = c (t + 1) - ε • a₁ := by
              funext ω
              rw [hct1]
              rfl
            rw [e, map_sub, map_smul, hcad (t + 1), ha₁k]
          · rw [hcn ε n h1 h2, hcad n]
      · by_cases h1 : n = t
        · subst h1
          have e : bε ε (n + 1) = b (n + 1) - ε • a₂ := by
            funext ω
            rw [hbt1]
            rfl
          rw [e, map_sub, map_smul, hbad n, ha₂k]
        · rw [hbn ε (n + 1) (by omega), hbad n]
      · have h0 := hflow n ω
        by_cases h1 : n = t
        · subst h1
          rw [hct, hbn ε n (by omega), hbt1]
          have e1 : P n ω * (ε * a₀ ω) = ε * z ω := by
            simp only [ha₀]
            have := (hPpos n ω).ne'
            field_simp
          have e2 : Q n ω * (ε * a₂ ω) = ε * z ω := by
            simp only [ha₂]
            have := (hQpos ω).ne'
            field_simp
          linear_combination h0 - e1 + e2
        · by_cases h2 : n = t + 1
          · subst h2
            have h0' := hflow (t + 1) ω
            rw [hct1, hbt1, hbn ε (t + 1 + 1) (by omega)]
            have e3 : P (t + 1) ω * (ε * a₁ ω) = ε * a₂ ω := by
              simp only [ha₁, ha₂]
              have := (hPpos (t + 1) ω).ne'
              have := (hQpos ω).ne'
              field_simp
            linear_combination h0' + e3
          · rw [hcn ε n h1 h2, hbn ε n h2, hbn ε (n + 1) (by omega)]
            exact h0
      · by_cases h1 : n = t + 1
        · subst h1
          rw [hbt1]
          have hm : r ≤ Q t ω * b (t + 1) ω / (|z ω| + 1) := hωm ω
          rw [le_div_iff₀ (by positivity)] at hm
          have h2 : ε * z ω ≤ |ε| * (|z ω| + 1) := by
            have := le_abs_self (ε * z ω)
            rw [abs_mul] at this
            nlinarith [abs_nonneg ε]
          have h3 : |ε| * (|z ω| + 1) ≤ r * (|z ω| + 1) :=
            mul_le_mul_of_nonneg_right hε.le (by positivity)
          have h4 : ε * a₂ ω ≤ b (t + 1) ω := by
            simp only [ha₂]
            rw [← mul_div_assoc, div_le_iff₀ (hQpos ω)]
            linarith
          linarith
        · rw [hbn ε n h1]
          exact hbnn n ω
    -- the utility gain
    let φ : ℝ → ℝ := fun ε =>
      β ^ t * (𝔼.E 0 (fun ω => u (c t ω + ε * a₀ ω)) ω₀ - 𝔼.E 0 (fun ω => u (c t ω)) ω₀) +
      β ^ (t + 1) * (𝔼.E 0 (fun ω => u (c (t + 1) ω - ε * a₁ ω)) ω₀ -
        𝔼.E 0 (fun ω => u (c (t + 1) ω)) ω₀)
    have hdiff : ∀ ε ω, HasSum (fun n => β ^ n * 𝔼.E 0 (fun ω' => u (cε ε n ω')) ω)
        (expUtil 𝔼 β u c ω + (β ^ t * (𝔼.E 0 (fun ω' => u (c t ω' + ε * a₀ ω')) ω -
          𝔼.E 0 (fun ω' => u (c t ω')) ω) +
          β ^ (t + 1) * (𝔼.E 0 (fun ω' => u (c (t + 1) ω' - ε * a₁ ω')) ω -
          𝔼.E 0 (fun ω' => u (c (t + 1) ω')) ω))) := by
      intro ε ω
      have h := hasSum_of_eq_off_finset (hsum ω) {t, t + 1}
        (f' := fun n => β ^ n * 𝔼.E 0 (fun ω' => u (cε ε n ω')) ω) (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          rw [hcn ε n hn.1 hn.2])
      convert h using 1
      rw [Finset.sum_pair (by omega)]
      simp only [hct, hct1, expUtil]
      ring
    have hle : ∀ ε, |ε| < r → φ ε ≤ 0 := by
      intro ε hε
      have h1 := hbest (cε ε) (bε ε) (hfeas ε hε) (fun ω => (hdiff ε ω).summable) ω₀
      have e : expUtil 𝔼 β u (cε ε) ω₀ = expUtil 𝔼 β u c ω₀ + φ ε := (hdiff ε ω₀).tsum_eq
      linarith
    have hmax : IsLocalMax φ 0 := by
      have hmem : Set.Ioo (-r) r ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hrpos
      filter_upwards [hmem] with ε hε
      have : φ 0 = 0 := by simp [φ]
      rw [this]
      exact hle ε (abs_lt.mpr hε)
    have hd0 : HasDerivAt (fun ε => 𝔼.E 0 (fun ω => u (c t ω + ε * a₀ ω)) ω₀)
        (𝔼.E 0 (fun ω => u' (c t ω) * a₀ ω) ω₀) 0 :=
      hasDerivAt_E 𝔼 (f := fun ε ω => u (c t ω + ε * a₀ ω)) (fun ω => by
        have hin : HasDerivAt (fun ε : ℝ => c t ω + ε * a₀ ω) (a₀ ω) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ ω)).const_add (c t ω)
        have hu' : HasDerivAt u (u' (c t ω)) ((fun ε : ℝ => c t ω + ε * a₀ ω) 0) := by
          simpa using hu (c t ω)
        exact hu'.comp 0 hin) 0 ω₀
    have hd1 : HasDerivAt (fun ε => 𝔼.E 0 (fun ω => u (c (t + 1) ω - ε * a₁ ω)) ω₀)
        (𝔼.E 0 (fun ω => u' (c (t + 1) ω) * -a₁ ω) ω₀) 0 :=
      hasDerivAt_E 𝔼 (f := fun ε ω => u (c (t + 1) ω - ε * a₁ ω)) (fun ω => by
        have hin : HasDerivAt (fun ε : ℝ => c (t + 1) ω - ε * a₁ ω) (-a₁ ω) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₁ ω)).const_sub (c (t + 1) ω)
        have hu' : HasDerivAt u (u' (c (t + 1) ω))
            ((fun ε : ℝ => c (t + 1) ω - ε * a₁ ω) 0) := by
          simpa using hu (c (t + 1) ω)
        exact hu'.comp 0 hin) 0 ω₀
    have hφ := ((hd0.sub_const (𝔼.E 0 (fun ω => u (c t ω)) ω₀)).const_mul (β ^ t)).add
      ((hd1.sub_const (𝔼.E 0 (fun ω => u (c (t + 1) ω)) ω₀)).const_mul (β ^ (t + 1)))
    have hzero := hmax.hasDerivAt_eq_zero hφ
    have hneg : (fun ω => u' (c (t + 1) ω) * -a₁ ω) =
        -(fun ω => u' (c (t + 1) ω) * a₁ ω) := by
      funext ω
      simp
    rw [hneg, map_neg] at hzero
    simp only [Pi.neg_apply] at hzero
    linarith
  -- Step B: the conditional Euler equation
  set A : Ω → ℝ := fun ω => u' (c t ω) / P t ω with hA
  set G : Ω → ℝ := fun ω => u' (c (t + 1) ω) / P (t + 1) ω with hG
  set Qi : Ω → ℝ := fun ω => (Q t ω)⁻¹ with hQi
  have hAk : 𝔼.E t A = A := known_div 𝔼 hPO hFK (hFK t (c t) u' (hcad t)) (hPad t)
  have hQik : 𝔼.E t Qi = Qi := hFK t (Q t) (fun r => r⁻¹) hQad
  set D : Ω → ℝ := A - β • (Qi * 𝔼.E t G) with hD
  have hDk : 𝔼.E t D = D := by
    rw [hD, map_sub, map_smul, hAk, hPO t _ _ hQik, 𝔼.E_E_self]
  have key : ∀ z, 𝔼.E t z = z → ∀ ω₀, 𝔼.E 0 (z * D) ω₀ = 0 := by
    intro z hz ω₀
    have h := stepA z hz ω₀
    have e1 : (fun ω => u' (c t ω) * (z ω / P t ω)) = z * A := by
      funext ω
      simp only [hA, Pi.mul_apply]
      ring
    have e2 : (fun ω => u' (c (t + 1) ω) * (z ω / (Q t ω * P (t + 1) ω))) = (z * Qi) * G := by
      funext ω
      simp only [hQi, hG, Pi.mul_apply]
      ring
    have hzQ : 𝔼.E t (z * Qi) = z * Qi := by rw [hPO t _ _ hz, hQik]
    have e3 : 𝔼.E 0 ((z * Qi) * G) = 𝔼.E 0 ((z * Qi) * 𝔼.E t G) := by
      rw [← 𝔼.tower (Nat.zero_le t) ((z * Qi) * G), hPO t _ _ hzQ]
    have e4 : z * D = z * A - β • ((z * Qi) * 𝔼.E t G) := by
      rw [hD]
      funext ω
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2, e3] at h
    rw [e4, map_sub, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hbt : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
    have : β ^ t * (𝔼.E 0 (z * A) ω₀ - β * 𝔼.E 0 (z * Qi * 𝔼.E t G) ω₀) = 0 := by
      rw [pow_succ] at h
      linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hbt
    · exact h'
  have hDD : ∀ ω, D ω * D ω = 0 :=
    hF (D * D) (fun ω => mul_self_nonneg (D ω)) (key D hDk)
  have hD0 : ∀ ω, D ω = 0 := fun ω => mul_self_eq_zero.mp (hDD ω)
  funext ω
  have h := hD0 ω
  simp only [hD, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hQi] at h
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hQ0 := (hQpos ω).ne'
  have hA' : A ω = β * ((Q t ω)⁻¹ * 𝔼.E t G ω) := by linarith
  rw [hA']
  field_simp

/-- Cochrane (2023), p. 22, "Household maximization, budget constraint, and equilibrium ... imply
the household transversality condition (2.6)", under uncertainty: on a finite state space with
pull-out, functions of known variables known, a faithful `E_0`, and information that stops
growing after some date `K` (every finite event tree, `finiteTree_infoStable`), if `(c, b)` is an
optimal state-contingent plan, `u` is strictly increasing, prices are positive and adapted, the
bond price is (2.3) `Q_n = β E_n(P_n/P_{n+1})`, and discounted net demands
`β^n (c_n − y + s_n)` are summable in every state, then the transversality condition
`lim_N β^N E_t B_{t+N−1}/P_{t+N} = 0` holds at every date and state. Proof: real debt converges
pathwise, `β^n x_n → L ≥ 0`; if `L > 0` somewhere, consuming `L/(2β^T)` more at a late date
`T` and holding `P_n L/(2β^n)` less debt afterwards is feasible and raises expected utility. -/
theorem tvc_of_optimal_stoch [Finite Ω] (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hF : Faithful 𝔼) {K : ℕ} (hK : InfoStable 𝔼 K) {β y : ℝ} (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : StrictMono u) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ c b) (hPpos : ∀ n ω, 0 < P n ω) (hPad : 𝔼.Adapted P)
    (hQ : ∀ n, Q n = β • 𝔼.E n (fun ω => P n ω / P (n + 1) ω))
    (hd : ∀ ω, Summable fun n => β ^ n * (c n ω - y + s n ω)) (t : ℕ) :
    TVC 𝔼 β (fun n ω => b n ω / P n ω) t := by
  obtain ⟨⟨hb0, hcad, hbad, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  set x : ℕ → Ω → ℝ := fun n ω => b n ω / P n ω with hxdef
  have hstab : ∀ m n v, K ≤ m → K ≤ n → 𝔼.E m v = v → 𝔼.E n v = v := by
    intro m n v hm hn hv
    rw [hK n hn, ← hK m hm, hv]
  have hxk : ∀ n, 1 ≤ n → 𝔼.E n (x n) = x n := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ k) (hbad k))
      (hPad (k + 1))
  have hQp : ∀ n, K ≤ n → ∀ ω, Q n ω = β * (P n ω / P (n + 1) ω) := by
    intro n hn ω
    have hk : 𝔼.E n (fun ω => P n ω / P (n + 1) ω) = fun ω => P n ω / P (n + 1) ω :=
      hstab (n + 1) n _ (by omega) hn
        (known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ n) (hPad n))
          (hPad (n + 1)))
    rw [hQ n, hk]
    rfl
  have hxflow : ∀ n, K ≤ n → ∀ ω, x n ω = (c n ω - y + s n ω) + β * x (n + 1) ω := by
    intro n hn ω
    have h1 := hflow n ω
    rw [hQp n hn ω] at h1
    have hP0 := (hPpos n ω).ne'
    have e : β * (P n ω / P (n + 1) ω) * b (n + 1) ω =
        β * P n ω * (b (n + 1) ω / P (n + 1) ω) := by ring
    have key : b n ω = P n ω * (c n ω - y + s n ω) + β * P n ω * x (n + 1) ω := by
      simp only [hxdef]
      linarith
    simp only [hxdef] at key ⊢
    rw [key]
    field_simp
  -- pathwise limits of the discounted real debt
  have hlimL : ∀ ω, ∃ L, Tendsto (fun n => β ^ n * x n ω) atTop (𝓝 L) ∧ 0 ≤ L := by
    intro ω
    set d : ℕ → ℝ := fun j => β ^ j * (c (K + j) ω - y + s (K + j) ω) with hd'
    have hbK : β ^ K ≠ 0 := pow_ne_zero K hβ.ne'
    have hds : Summable d := by
      have := ((summable_nat_add_iff K).mpr (hd ω)).mul_left (β ^ K)⁻¹
      refine this.congr fun j => ?_
      simp only [hd']
      rw [add_comm j K, pow_add]
      field_simp
    have htel : ∀ N, x K ω = ∑ j ∈ Finset.range N, d j + β ^ N * x (K + N) ω := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [ih, Finset.sum_range_succ, hxflow (K + N) (by omega) ω, pow_succ,
          show K + (N + 1) = K + N + 1 by omega]
        simp only [hd']
        ring
    have hlim : Tendsto (fun N => β ^ N * x (K + N) ω) atTop (𝓝 (x K ω - ∑' j, d j)) := by
      have h := (tendsto_const_nhds (x := x K ω)).sub hds.hasSum.tendsto_sum_nat
      refine h.congr fun N => ?_
      have := htel N
      linarith
    refine ⟨β ^ K * (x K ω - ∑' j, d j), ?_, ?_⟩
    · rw [← Filter.tendsto_add_atTop_iff_nat K]
      refine (hlim.const_mul (β ^ K)).congr fun N => ?_
      rw [show N + K = K + N by omega, pow_add]
      ring
    · exact mul_nonneg (pow_nonneg hβ.le K) (ge_of_tendsto' hlim fun N =>
        mul_nonneg (pow_nonneg hβ.le N) (div_nonneg (hbnn _ ω) (hPpos _ ω).le))
  choose L hL hL0 using hlimL
  -- the limit is known at `K`
  have hLk : 𝔼.E K L = L := by
    funext ω
    have h1 := E_tendsto 𝔼 (f := fun n ω' => β ^ n * x n ω') (fun ω' => hL ω') K ω
    have h2 : Tendsto (fun n => 𝔼.E K (fun ω' => β ^ n * x n ω') ω) atTop (𝓝 (L ω)) := by
      refine (hL ω).congr' ?_
      filter_upwards [eventually_ge_atTop (K + 1)] with n hn
      have e : (fun ω' => β ^ n * x n ω') = β ^ n • x n := by
        funext ω'
        simp
      rw [e, map_smul, hstab n K (x n) (by omega) le_rfl (hxk n (by omega))]
      rfl
    exact tendsto_nhds_unique h1 h2
  have hLkn : ∀ n, K ≤ n → 𝔼.E n L = L := fun n hn => hstab K n L le_rfl hn hLk
  -- the limit vanishes in every state
  have hLz : ∀ ω, L ω = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ω0, h0⟩ := hcon
    have hpos : 0 < L ω0 := lt_of_le_of_ne (hL0 ω0) (Ne.symm h0)
    have hev : ∀ᶠ n in atTop, K + 1 ≤ n ∧ ∀ ω, L ω / 2 ≤ β ^ n * x n ω := by
      refine (eventually_ge_atTop (K + 1)).and (Filter.eventually_all.mpr fun ω => ?_)
      rcases (hL0 ω).lt_or_eq with hp | hz
      · exact ((hL ω).eventually (lt_mem_nhds (show L ω / 2 < L ω by linarith))).mono
          fun n hn => hn.le
      · refine Filter.Eventually.of_forall fun n => ?_
        rw [← hz, zero_div]
        exact mul_nonneg (pow_nonneg hβ.le n) (div_nonneg (hbnn _ ω) (hPpos _ ω).le)
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
    have hTK := (hT T le_rfl).1
    set δ : Ω → ℝ := fun ω => L ω / (2 * β ^ T) with hδ
    let c' : ℕ → Ω → ℝ := fun n ω => c n ω + (if n = T then δ ω else 0)
    let b' : ℕ → Ω → ℝ := fun n ω =>
      b n ω - (if T < n then P n ω * (L ω / (2 * β ^ n)) else 0)
    have hc'T : ∀ ω, c' T ω = c T ω + δ ω := fun ω => by simp [c']
    have hc'n : ∀ n, n ≠ T → c' n = c n := fun n h => by
      funext ω
      simp [c', h]
    have hb'n : ∀ n, ¬ T < n → b' n = b n := fun n h => by
      funext ω
      simp [b', h]
    have hb'gt : ∀ n, T < n → ∀ ω, b' n ω = b n ω - P n ω * (L ω / (2 * β ^ n)) :=
      fun n h ω => by simp [b', h]
    have hfeas : SFeasible 𝔼 y P s Q b₀ c' b' := by
      refine ⟨by rw [hb'n 0 (by omega), hb0], fun n => ?_, fun n => ?_, fun n ω => ?_,
        fun n ω => ?_⟩
      · by_cases h : n = T
        · have e : c' n = c n + (2 * β ^ T)⁻¹ • L := by
            funext ω
            rw [h, hc'T]
            simp only [hδ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [e, map_add, map_smul, hcad n, hLkn n (by omega)]
        · rw [hc'n n h, hcad n]
      · by_cases h : T < n + 1
        · have e : b' (n + 1) = b (n + 1) - P (n + 1) * ((2 * β ^ (n + 1))⁻¹ • L) := by
            funext ω
            rw [hb'gt (n + 1) h ω]
            simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [e, map_sub, hbad n,
            hPO n _ _ (hstab (n + 1) n _ (by omega) (by omega) (hPad (n + 1))), map_smul,
            hLkn n (by omega)]
        · rw [hb'n (n + 1) h, hbad n]
      · have h1 := hflow n ω
        rcases lt_trichotomy n T with h | h | h
        · rw [hc'n n (by omega), hb'n n (by omega), hb'n (n + 1) (by omega)]
          exact h1
        · subst h
          rw [hc'T, hb'n n (lt_irrefl n), hb'gt (n + 1) (by omega) ω, hQp n (by omega) ω]
          rw [hQp n (by omega) ω] at h1
          have hP0 := (hPpos n ω).ne'
          have hP1 := (hPpos (n + 1) ω).ne'
          have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
          have e : β * (P n ω / P (n + 1) ω) * (P (n + 1) ω * (L ω / (2 * β ^ (n + 1)))) =
              P n ω * δ ω := by
            simp only [hδ]
            rw [pow_succ]
            field_simp
          linear_combination h1 + e
        · rw [hc'n n (by omega), hb'gt n h ω, hb'gt (n + 1) (by omega) ω,
            hQp n (by omega) ω]
          rw [hQp n (by omega) ω] at h1
          have hP0 := (hPpos n ω).ne'
          have hP1 := (hPpos (n + 1) ω).ne'
          have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
          have e : β * (P n ω / P (n + 1) ω) * (P (n + 1) ω * (L ω / (2 * β ^ (n + 1)))) =
              P n ω * (L ω / (2 * β ^ n)) := by
            rw [pow_succ]
            field_simp
          linear_combination h1 + e
      · by_cases h : T < n
        · rw [hb'gt n h ω]
          have hn := (hT n h.le).2 ω
          simp only [hxdef] at hn
          have hbn : 0 < β ^ n := pow_pos hβ n
          have hPn := hPpos n ω
          have e : β ^ n * (b n ω / P n ω) * P n ω = β ^ n * b n ω := by field_simp
          have h2 : L ω / 2 * P n ω ≤ β ^ n * (b n ω / P n ω) * P n ω :=
            mul_le_mul_of_nonneg_right hn hPn.le
          rw [e] at h2
          have : P n ω * (L ω / (2 * β ^ n)) ≤ b n ω := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            linarith
          linarith
        · rw [hb'n n h]
          exact hbnn n ω
    have hdev : ∀ ω, HasSum (fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω)
        (expUtil 𝔼 β u c ω + β ^ T * (𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω -
          𝔼.E 0 (fun ω' => u (c T ω')) ω)) := by
      intro ω
      have h := hasSum_of_eq_off_finset (hsum ω) {T}
        (f' := fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω)
        (fun n hn => by rw [hc'n n (by simpa using hn)])
      convert h using 1
      simp only [Finset.sum_singleton, hc'T, expUtil]
      ring
    set g : Ω → ℝ := fun ω' => u (c T ω' + δ ω') - u (c T ω') with hg
    have hg0 : ∀ ω', 0 ≤ g ω' := fun ω' => sub_nonneg.mpr (hu.monotone
      (le_add_of_nonneg_right (div_nonneg (hL0 ω') (by positivity))))
    have hgpos : 0 < g ω0 := sub_pos.mpr (hu (lt_add_of_pos_right _ (div_pos hpos
      (by positivity))))
    obtain ⟨ω1, hω1⟩ : ∃ ω1, 𝔼.E 0 g ω1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := hF g hg0 hcon ω0
      linarith
    have hEpos : 0 < 𝔼.E 0 g ω1 := lt_of_le_of_ne (E_nonneg 𝔼 hg0 ω1) (Ne.symm hω1)
    have hle := hbest c' b' hfeas (fun ω => (hdev ω).summable) ω1
    have e : expUtil 𝔼 β u c' ω1 = expUtil 𝔼 β u c ω1 + β ^ T *
        (𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω1 - 𝔼.E 0 (fun ω' => u (c T ω')) ω1) :=
      (hdev ω1).tsum_eq
    have eg : 𝔼.E 0 g ω1 = 𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω1 -
        𝔼.E 0 (fun ω' => u (c T ω')) ω1 := by
      rw [hg, show (fun ω' => u (c T ω' + δ ω') - u (c T ω')) =
        (fun ω' => u (c T ω' + δ ω')) - (fun ω' => u (c T ω')) from rfl, map_sub]
      rfl
    have : 0 < β ^ T * 𝔼.E 0 g ω1 := mul_pos (pow_pos hβ T) hEpos
    rw [eg] at this
    linarith
  -- the transversality condition at every date
  intro ω
  have hpath : ∀ ω', Tendsto (fun N => β ^ N * x (t + N) ω') atTop (𝓝 0) := by
    intro ω'
    have h := (hL ω').comp (tendsto_add_atTop_nat t)
    rw [hLz ω'] at h
    have h2 := h.const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    simp only [Function.comp]
    rw [show N + t = t + N by omega, pow_add]
    have := pow_ne_zero t hβ.ne'
    field_simp
  have h := E_tendsto 𝔼 (f := fun N ω' => β ^ N * x (t + N) ω') (g := fun _ => 0) hpath t ω
  have h0 : 𝔼.E t (fun _ => (0 : ℝ)) ω = 0 := by rw [𝔼.const]
  rw [h0] at h
  refine h.congr fun N => ?_
  have e : (fun ω' => β ^ N * x (t + N) ω') = β ^ N • x (t + N) := by
    funext ω'
    simp
  rw [e, map_smul]
  rfl

/-- Cochrane (2023), eq. (2.7), p. 22, derived from household optimisation under uncertainty:
under the hypotheses of `tvc_of_optimal_stoch` with consumption at the endowment `c = y`,
adapted absolutely summable surpluses and conditional monotone convergence (every finite tree),
real debt equals the present value of surpluses at every date. -/
theorem valuation_of_optimal_stoch [Finite Ω] (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hF : Faithful 𝔼) (hMC : MonotoneConvergence 𝔼) {K : ℕ} (hK : InfoStable 𝔼 K) {β y : ℝ}
    (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u) {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ (fun _ _ => y) b) (hPpos : ∀ n ω, 0 < P n ω)
    (hPad : 𝔼.Adapted P) (hQ : ∀ n, Q n = β • 𝔼.E n (fun ω => P n ω / P (n + 1) ω))
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hd : ∀ ω, Summable fun n => β ^ n * s n ω) (t : ℕ) :
    (fun ω => b t ω / P t ω) = pv 𝔼 β s t := by
  have hd' : ∀ ω, Summable fun n => β ^ n * ((fun _ _ => y : ℕ → Ω → ℝ) n ω - y + s n ω) :=
    fun ω => (hd ω).congr fun n => by ring
  have htvc := tvc_of_optimal_stoch 𝔼 hPO hFK hF hK hβ hu hopt hPpos hPad hQ hd'
  obtain ⟨⟨-, -, hbad, hflow, -⟩, -, -⟩ := hopt
  have hfl : FlowX 𝔼 β (fun n ω => b n ω / P n ω) s := fun n =>
    (flow_iff_real_x 𝔼 hPO (hPpos n) (hPad n) (hbad n) (hQ n)).mp fun ω => by
      have := hflow n ω
      linarith
  exact (valuation_iff 𝔼 hMC hβ.le hs hsad).mp ⟨hfl, htvc⟩ t

end Cochrane.IntertemporalModel.Valuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic intuition and equilibrium formation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.2 "Dynamic intuition",
pp. 23–26, eq. (2.9), and §2.3 "Equilibrium formation", pp. 26–29, eqs. (2.10)–(2.11) and the
display on p. 28.

Notation as in `Environment` and `Valuation`: `Bm t = B_{t−1}`, real debt
`x_t = B_{t−1}/P_t`, present value `pv_t = ∑_j β^j E_t s_{t+j}`.

## Main results

* `realRevenue_hasSum`, `eqm_realRevenue` ((2.9), (2.11)): debt sales raise real revenue
  `Q_t B_t/P_t = ∑_{j ≥ 1} β^j E_t s_{t+j}`; `pv_eq_s_add_fwd`:
  `pv_t = s_t + ∑_{j≥1} β^j E_t s_{t+j}`.
* `deficit_financed_by_debt` (p. 24), `soak_up_retired` (the p. 24 formula `Q_tB_t = βE_ts_{t+1}`
  holds, in real terms, exactly when the debt is retired at `t + 1`), `no_rollover` (p. 24–25).
* `passive_every_price_eqm` (p. 24): under a "passive" surplus rule the valuation equation holds
  for every price level.
* `no_initial_debt_pv_zero`, `no_initial_debt_P0_free`, `no_initial_debt_not_unique`
  (pp. 25–26): with `B_{−1} = 0`, `P_0` is not determined.
* `money_overhang_iff`, `money_zero_iff`, `money_negative_iff` (p. 27, (2.10)–(2.11)):
  money is left overnight iff the price level is below its equilibrium value.
* `iterate_with_terminal`, `iterate_with_terminal_limit` (p. 28, with the terminal exponent
  `T + 1`), `printed_p28_false` (the printed `β^T`, survey E4).
* `tooHigh_explodes_down`, `tooHigh_violates_nonneg_debt` (p. 28): a too-high price level pushes
  debt negative, ruled out by `B ≥ 0`.
-/

namespace Cochrane.IntertemporalModel.EquilibriumFormation

open Filter Topology Environment Valuation ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Debt sales and the present value of following surpluses (2.9), (2.11) -/

/-- Cochrane (2023), eq. (2.7) split at its first term, p. 24: `pv_t = s_t + ∑_{j ≥ 1} β^j E_t
s_{t+j}`, for adapted absolutely summable surpluses. -/
theorem pv_eq_s_add_fwd {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (t : ℕ) (ω : Ω) :
    pv 𝔼 β s t ω = s t ω + ∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω := by
  have h0 := (summable_terms 𝔼 hβ hs t ω).tsum_eq_zero_add
  simp only [pv_apply]
  rw [h0, pow_zero, one_mul, add_zero, hsad t]
  congr 1
  exact tsum_congr fun j => by rw [show t + (j + 1) = t + 1 + j by omega]

/-- Cochrane (2023), eqs. (2.9) and (2.11), pp. 24 and 27: with the bond price (2.3), a positive
price level known at `t`, debt `B_t` known at `t`, pull-out, conditional monotone convergence,
and the valuation equation at `t + 1`, debt sales raise real revenue equal to the present value
of the following surpluses, `Q_t B_t/P_t = ∑_{j ≥ 1} β^j E_t s_{t+j}` (a convergent series). -/
theorem realRevenue_hasSum (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm P s Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) {t : ℕ}
    (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (hval : (fun ω => Bm (t + 1) ω / P (t + 1) ω) = pv 𝔼 β s (t + 1)) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω) := by
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  have hx := congrFun (flow_real_x 𝔼 hPO (β := β) (P := P) hB) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  have hrev : Q t ω * Bm (t + 1) ω / P t ω = β * 𝔼.E t (pv 𝔼 β s (t + 1)) ω := by
    rw [← hval, ← hx, hQ]
    have := (hPpos ω).ne'
    field_simp
  rw [hrev]
  have h1 := (hasSum_E_pv 𝔼 hMC hβ hs t 1 ω).mul_left β
  refine h1.congr_fun fun j => ?_
  rw [pow_succ]
  ring

/-- Cochrane (2023), eq. (2.11), p. 27, in every equilibrium:
`Q_tB_t/P_t = E_t∑_{j≥1}β^js_{t+j}`. -/
theorem eqm_realRevenue (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω) :=
  realRevenue_hasSum 𝔼 hPO hMC hβ hs (h.1 t) (h.2.1 t) (hB1 t) (h.2.2.1 t)
    (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h (t + 1)) ω

/-- Cochrane (2023), eq. (2.9), p. 24, "If the government needs to finance a war ... it will
want to run a deficit ... the government can soak up those dollars by debt sales": with a
deficit `s_t < 0` and `P_t > 0`, debt sales `Q_tB_t` exceed the maturing debt `B_{t−1}`. -/
theorem deficit_financed_by_debt {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h24 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (hP : 0 < P t ω)
    (hs : s t ω < 0) : Bm t ω < Q t ω * Bm (t + 1) ω := by
  have : P t ω * s t ω < 0 := mul_neg_of_pos_of_neg hP hs
  linarith

/-- Cochrane (2023), p. 24, "the government can soak up those dollars by debt sales
`Q_tB_t = βE_ts_{t+1}`": the formula is exact (in real terms, `Q_tB_t/P_t = βE_ts_{t+1}`) when
the debt is retired at `t + 1` (`B_{t+1} = 0`); in general the revenue is the whole present
value (2.11) (`realRevenue_hasSum`). -/
theorem soak_up_retired (hPO : 𝔼.PullOut) {β : ℝ} {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ}
    (hPpos : ∀ ω, 0 < P t ω) (hPpos1 : ∀ ω, 0 < P (t + 1) ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (h24 : ∀ ω, Bm (t + 1) ω = P (t + 1) ω * s (t + 1) ω + Q (t + 1) ω * Bm (t + 2) ω)
    (hret : ∀ ω, Bm (t + 2) ω = 0) (ω : Ω) :
    Q t ω * Bm (t + 1) ω / P t ω = β * 𝔼.E t (s (t + 1)) ω := by
  have hx1 : (fun ω => Bm (t + 1) ω / P (t + 1) ω) = s (t + 1) := by
    funext ω
    rw [h24 ω, hret ω, mul_zero, add_zero]
    have := (hPpos1 ω).ne'
    field_simp
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  have hx := congrFun (flow_real_x 𝔼 hPO (β := β) (P := P) hB) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  rw [← hx1, ← hx, hQ]
  have := (hPpos ω).ne'
  field_simp

/-- Cochrane (2023), pp. 24–25, "If the roll-over fails, or if the government retires the debt,
not selling new debt, we have `B_{t−1}/P_t = s_t` only as in the one-period model": with
`B_t = 0`, (2.4) gives `B_{t−1}/P_t = s_t`. -/
theorem no_rollover {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h24 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (hP : P t ω ≠ 0)
    (hB : Bm (t + 1) ω = 0) : Bm t ω / P t ω = s t ω := by
  rw [h24, hB, mul_zero, add_zero]
  field_simp

/-- Cochrane (2023), p. 25 (the flow equation `B_{t−1}/P_t = s_t + Q_tB_t/P_t`): for `P_t ≠ 0`,
(2.4) is equivalent to its real form. -/
theorem flow_div_iff {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hP : P t ω ≠ 0) :
    Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω ↔
      Bm t ω / P t ω = s t ω + Q t ω * Bm (t + 1) ω / P t ω := by
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have : Bm t ω = P t ω * (Bm t ω / P t ω) := by field_simp
    rw [this, h]
    field_simp

/-! ### Passive fiscal policy (p. 24) -/

/-- Cochrane (2023), p. 24: a "passive" surplus rule, which sets surpluses so that the real
flow condition holds at whatever price level obtains, `s_t = x_t − β E_t x_{t+1}` with
`x_t = B_{t−1}/P_t`. -/
noncomputable def passiveSurplus (β : ℝ) (Bm P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun ω => Bm t ω / P t ω) - β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω)

/-- Cochrane (2023), p. 24, "We only have to rule out or treat separately the special case of
'passive' policy, that the present value of surpluses reacts exactly one-for-one to changes in
the value of nominal debt brought about by changes in the price level, so that equation (2.7)
holds for any price level": with `0 ≤ β < 1`, debt known when sold and pull-out, every positive
adapted price level with bounded real debt is an equilibrium under the passive rule. -/
theorem passive_every_price_eqm (hPO : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm P : ℕ → Ω → ℝ} (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P)
    (hbdd : ∃ M, ∀ t ω, |Bm t ω / P t ω| ≤ M) :
    IsEqm 𝔼 β Bm (passiveSurplus 𝔼 β Bm P) P
      (fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) := by
  refine ⟨hPpos, hPad, fun t => rfl, fun t => ?_, fun t ω => ?_⟩
  · refine (flow_iff_real_x 𝔼 hPO (Q := fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
      (hPpos t) (hPad t) (hB1 t) rfl).mpr ?_
    simp [passiveSurplus]
  · obtain ⟨M, hM⟩ := hbdd
    have hb : ∀ N : ℕ, |β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω| ≤
        β ^ N * M := fun N => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 N)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω => hM (t + N) ω) t ω)
        (pow_nonneg hβ0 N)
    have hlim : Tendsto (fun N : ℕ => β ^ N * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const M
    exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N) hlim

/-! ### No initial debt (pp. 25–26) -/

/-- Cochrane (2023), pp. 25–26, "If we start with `B_{−1} = 0`": in every equilibrium the date-0
valuation equation reads `0 = pv_0`, a restriction on surpluses that does not involve `P_0`. -/
theorem no_initial_debt_pv_zero (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q)
    (hB0 : ∀ ω, Bm 0 ω = 0) : pv 𝔼 β s 0 = 0 := by
  rw [← eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h 0]
  funext ω
  simp [hB0 ω]

/-- Cochrane (2023), pp. 25–26, "If we start with `B_{−1} = 0`, then the price level `P_0` must
be determined by other means": replacing `P_0` in any equilibrium by an arbitrary positive
date-0 variable `P₀'` (and `Q_0` by the corresponding bond price) gives another equilibrium. -/
theorem no_initial_debt_P0_free (hPO : 𝔼.PullOut) {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ}
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q)
    (hB0 : ∀ ω, Bm 0 ω = 0) {P₀' : Ω → ℝ} (hP0pos : ∀ ω, 0 < P₀' ω)
    (hP0ad : 𝔼.E 0 P₀' = P₀') :
    IsEqm 𝔼 β Bm s (fun t => if t = 0 then P₀' else P t)
      (fun t => if t = 0 then β • 𝔼.E 0 (fun ω => P₀' ω / P 1 ω) else Q t) := by
  obtain ⟨hPpos, hPad, h23, h24, htvc⟩ := h
  set P' : ℕ → Ω → ℝ := fun t => if t = 0 then P₀' else P t with hP'
  set Q' : ℕ → Ω → ℝ :=
    fun t => if t = 0 then β • 𝔼.E 0 (fun ω => P₀' ω / P 1 ω) else Q t with hQ'
  have hP'0 : P' 0 = P₀' := rfl
  have hP'succ : ∀ t, P' (t + 1) = P (t + 1) := fun t => rfl
  have hP'pos : ∀ t ω, 0 < P' t ω := fun t ω => by
    cases t with
    | zero => exact hP0pos ω
    | succ t => exact hPpos (t + 1) ω
  have hP'ad : 𝔼.Adapted P' := fun t => by
    cases t with
    | zero => exact hP0ad
    | succ t => exact hPad (t + 1)
  have h23' : ∀ t, Q' t = β • 𝔼.E t (fun ω => P' t ω / P' (t + 1) ω) := fun t => by
    cases t with
    | zero => rfl
    | succ t => exact h23 (t + 1)
  have hx : (fun t ω => Bm t ω / P' t ω) = fun t ω => Bm t ω / P t ω := by
    funext t ω
    cases t with
    | zero => simp [hB0 ω]
    | succ t => rfl
  refine ⟨hP'pos, hP'ad, h23', fun t => ?_, fun t => by rw [hx]; exact htvc t⟩
  cases t with
  | zero =>
    have hr := (flow_iff_real_x 𝔼 hPO (hPpos 0) (hPad 0) (hB1 0) (h23 0)).mp (h24 0)
    refine (flow_iff_real_x 𝔼 hPO (hP'pos 0) (hP'ad 0) (hB1 0) (h23' 0)).mpr ?_
    have e0 := congrFun hx 0
    have e1 := congrFun hx 1
    rw [e0, e1]
    exact hr
  | succ t => exact h24 (t + 1)

/-- Cochrane (2023), pp. 25–26: with `B_{−1} = 0` the equilibrium price level is not unique:
next to any equilibrium there is another with `P_0` doubled. -/
theorem no_initial_debt_not_unique [Nonempty Ω] (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm s P Q : ℕ → Ω → ℝ} (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h : IsEqm 𝔼 β Bm s P Q) (hB0 : ∀ ω, Bm 0 ω = 0) :
    ∃ P' Q', IsEqm 𝔼 β Bm s P' Q' ∧ P' ≠ P := by
  have hpos : ∀ ω, 0 < (2 : ℝ) • P 0 ω := fun ω => by
    have := h.1 0 ω
    simp only [smul_eq_mul]
    linarith
  have had : 𝔼.E 0 ((2 : ℝ) • P 0) = (2 : ℝ) • P 0 := by rw [map_smul, h.2.1 0]
  refine ⟨_, _, no_initial_debt_P0_free 𝔼 hPO hB1 h hB0 (P₀' := (2 : ℝ) • P 0)
    (fun ω => by simpa using hpos ω) had, fun heq => ?_⟩
  have := congrFun (congrFun heq 0) (Classical.arbitrary Ω)
  have hp := h.1 0 (Classical.arbitrary Ω)
  simp only [↓reduceIte, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-! ### Money left overnight (2.10)–(2.11) -/

/-- Cochrane (2023), eqs. (2.10)–(2.11), p. 27, "if the price level `P_t` is too low, the current
surplus and the revenue from bond sales in (2.10) do not soak up all the money printed to redeem
bonds. Money `M_t` is left overnight": with `B_{t−1} = P_ts_t + Q_tB_t + M_t`, debt-sale revenue
`Q_tB_t/P_t = ∑_{j≥1}β^jE_ts_{t+j}`, `P_t > 0` and a positive present value, `M_t > 0` iff
`P_t < B_{t−1}/pv_t`. -/
theorem money_overhang_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    0 < M t ω ↔ P t ω < Bm t ω / pv 𝔼 β s t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  -- `M_t / P_t = B_{t−1}/P_t − pv_t`
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [lt_div_iff₀ hpv, hM]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), p. 27: under (2.10)–(2.11), no money is left overnight iff the price level
is exactly `B_{t−1}/pv_t`. -/
theorem money_zero_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    M t ω = 0 ↔ P t ω = Bm t ω / pv 𝔼 β s t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [eq_div_iff hpv.ne', hM]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 27, "If you're bothered by negative money in the opposite direction":
under (2.10)–(2.11), the money balance is negative iff the price level is above
`B_{t−1}/pv_t`. -/
theorem money_negative_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    M t ω < 0 ↔ Bm t ω / pv 𝔼 β s t ω < P t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [div_lt_iff₀ hpv, hM]
  constructor <;> intro h <;> nlinarith

/-! ### The terminal term (p. 28) -/

/-- Cochrane (2023), p. 28 (display), as an exact finite-horizon identity: if the flow condition
holds at every date (adapted surpluses), then
`B_{t−1}/P_t = s_t + ∑_{j=1}^{T} β^j E_t s_{t+j} + β^{T+1} E_t B_{t+T}/P_{t+T+1}`. The printed
terminal weight is `β^T` (survey E4); `printed_p28_false` refutes it. -/
theorem iterate_with_terminal {β : ℝ} {x s : ℕ → Ω → ℝ} (hsad : 𝔼.Adapted s)
    (h : FlowX 𝔼 β x s) (t T : ℕ) :
    x t = s t + (∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + 1 + j))) +
      β ^ (T + 1) • 𝔼.E t (x (t + T + 1)) := by
  rw [hh_iterate 𝔼 hsad h t T, Finset.sum_range_succ', pow_zero, one_smul, add_zero, hsad t]
  have : ∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + (j + 1))) =
      ∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + 1 + j)) :=
    Finset.sum_congr rfl fun j _ => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [this]
  abel

/-- Cochrane (2023), p. 28 (display, limit form): if the terminal term
`β^N E_t x_{t+N}` converges to `L`, then `x_t = s_t + ∑_{j ≥ 1} β^j E_t s_{t+j} + L`. -/
theorem iterate_with_terminal_limit {β : ℝ} (hβ : 0 ≤ β) {x s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) {t : ℕ} {ω : Ω}
    {L : ℝ} (hL : Tendsto (fun N : ℕ => β ^ N * 𝔼.E t (x (t + N)) ω) atTop (𝓝 L)) :
    x t ω = s t ω + (∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω) + L := by
  have hxt := adapted_of_flow 𝔼 hsad h t
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ N * 𝔼.E t (x (t + N)) ω := by
    intro N
    have := congrFun (telescope 𝔼 h hxt N) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω - L)) := by
    simp_rw [hpart]
    exact tendsto_const_nhds.sub hL
  have hS := summable_terms 𝔼 hβ hs t ω
  have hpv : pv 𝔼 β s t ω = x t ω - L :=
    tendsto_nhds_unique hS.hasSum.tendsto_sum_nat hlim
  have := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  linarith

/-- Cochrane (2023), p. 28 (survey E4): the printed terminal weight `β^T` is wrong. Under perfect
foresight with `β = 1/2`, `s ≡ 0` and `x_t = 2^t` (so the flow condition holds),
`x_0 ≠ s_0 + ∑_{j=1}^{1} β^j s_j + β^1 x_2`. -/
theorem printed_p28_false :
    FlowX perfectForesight (1 / 2 : ℝ) (fun t _ => (2 : ℝ) ^ t) (fun _ _ => 0) ∧
      (2 : ℝ) ^ 0 ≠ 0 + (1 / 2 : ℝ) ^ 1 * 0 + (1 / 2 : ℝ) ^ 1 * 2 ^ (0 + 1 + 1) := by
  refine ⟨(printed_A1_2_false).1, by norm_num⟩

/-! ### A too-high price level (p. 28) -/

/-- Cochrane (2023), p. 28, "a too-high price level pushes debt to negative values": with constant
surpluses `s`, `0 < β < 1`, and real debt below the equilibrium value `x_t < s/(1−β)` in state
`ω`, expected real debt `E_t x_{t+n}` tends to `−∞`. -/
theorem tooHigh_explodes_down {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) {t : ℕ} {ω : Ω} (hlow : x t ω < s / (1 - β)) :
    Tendsto (fun n : ℕ => 𝔼.E t (x (t + n)) ω) atTop atBot := by
  have hform : ∀ n : ℕ, 𝔼.E t (x (t + n)) ω =
      (β⁻¹) ^ n * (x t ω - s / (1 - β)) + s / (1 - β) := by
    intro n
    have := congrFun (const_explodes 𝔼 hβ0 hβ1 h t n) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [inv_pow]
    linarith
  simp_rw [hform]
  have hpow : Tendsto (fun n : ℕ => (β⁻¹) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.mpr hβ1)
  have hneg : Tendsto (fun n : ℕ => (β⁻¹) ^ n * (x t ω - s / (1 - β))) atTop atBot := by
    have := hpow.const_mul_atTop_of_neg (r := x t ω - s / (1 - β)) (by linarith)
    simpa [mul_comm] using this
  exact hneg.atBot_add tendsto_const_nhds

/-- Cochrane (2023), p. 28, "a too-high price level pushes debt to negative values, which is ruled
out by budget constraint": under the hypotheses of `tooHigh_explodes_down`, with positive prices,
nominal debt cannot stay nonnegative at all later dates and states. -/
theorem tooHigh_violates_nonneg_debt {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Bm P : ℕ → Ω → ℝ} (hPpos : ∀ t ω, 0 < P t ω)
    (h : FlowX 𝔼 β (fun t ω => Bm t ω / P t ω) fun _ _ => s) {t : ℕ} {ω : Ω}
    (hlow : Bm t ω / P t ω < s / (1 - β)) : ¬ ∀ n ω', 0 ≤ Bm (t + n) ω' := by
  intro hnn
  have hlim := tooHigh_explodes_down 𝔼 hβ0 hβ1 h hlow
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_atBot 0)).exists
  have : 0 ≤ 𝔼.E t (fun ω' => Bm (t + n) ω' / P (t + n) ω') ω :=
    E_nonneg 𝔼 (fun ω' => div_nonneg (hnn n ω') (hPpos _ ω').le) ω
  linarith

end Cochrane.IntertemporalModel.EquilibriumFormation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal and monetary policy in the intertemporal model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4 (pp. 29–34),
§2.7 (pp. 42–44), §2.8 (pp. 44–47) and §2.10 (pp. 49–51).

Conventions. `B t` is the nominal one-period debt sold at the end of date `t` (the book's `B_t`,
maturing at `t + 1`); `Bm1` is the initial debt `B_{−1}`. Present values are genuine `tsum`s:
`epv β s t = ∑_{j≥0} βʲ s_{t+j}` state by state, `pv = E_t epv` (the book's
`E_t ∑ βʲ s_{t+j}`) and `pvEx = E_t ∑_{j≥1} βʲ s_{t+j}`; `pv` equals the chapter's
`Valuation.pv` (`∑ βʲ E_t s_{t+j}`) under the hypotheses of `GeneralLinks.fm_pv_eq_pv`.
Innovations are `ExpectationTools.innov t x = E_{t+1} x − E_t x` (the book's `ΔE_{t+1}`). An
`Equilibrium` is an adapted positive price level, adapted debt and nominal rate `i > −1`
satisfying the valuation equation (2.7)/(2.12) at every date and the bond-pricing condition
(2.3)/(2.14); the valuation equation is stated here directly.
`GeneralLinks.equilibrium_iff_isEqm` proves that these are exactly the equilibria
`Valuation.IsEqm` derived from the flow condition (2.4) and the transversality condition (2.6).
Everything holds for an arbitrary `ExpectationSystem` with the pull-out property, so
under perfect foresight and under genuine uncertainty (the coin-flip economy at the end).

## Main results

* (2.13) `unexpected_inflation`, `unexpected_inflation_eq`, `no_surprise_iff`,
  `disinflation_iff`; expected inflation `expected_inflation`; (2.14)–(2.15)
  `expected_valuation`, `debt_eq`; (2.26) `eq_2_26`, `eq_2_26_zero`, `flow_nominal`; (2.27)
  `eq_2_27`; `inflation_decomposition` (target sets expected, fiscal news unexpected inflation).
* Debt with surpluses fixed: `revenue_invariant` (unit-elastic demand), `shareSplit`,
  `future_sales_irrelevant`.
* Interest-rate targets: `peg_equilibrium`, `peg_unique`, `peg_existsUnique` (any adapted
  target, no Taylor principle), `peg_expected_inflation`, `expected_inflation_indep_surplus`,
  `debt_ratio_of_rate`, `debt_growth_of_rate` and `rate_change_eq_debt_growth_iff`,
  `printed_one_percent_fails` (survey E7); real-rate pegs: `real_rate_forced`,
  `no_eqm_real_rate_peg`, `real_rate_peg_unbounded`; the contrast with the classic doctrine:
  `scaled_all_but_initial`, `scaled_not_initial`; perfect foresight: `pf_pricing_iff`,
  `pf_price_formula`, `pf_family`.
* §2.7: `equityIssue`, `equityIssue_finances_deficit`, `sShape_seq`, `sShape`,
  `reform_with_deficits`; AR(1) surpluses: `ar1_news`, `ar1_pv_news`,
  `ar1_unexpected_inflation` and `ar1_printed_fails` (survey E5), `ar1_value_news`,
  `ar1_value_falls`, `ar1_news_exceeds_deficit`.
* §2.8: `consolidation_irrelevant`. §2.10: `stimulus_no_jump`, `pf_stimulus_neutral`,
  `stimulus_price_iff`, `stimulus_unexpected_inflation`, `news_pv_add_known`, and the
  coin-flip counterexample `CoinExample.stimulus_not_neutral` ("no effect at all" holds under
  perfect foresight but not under uncertainty).
-/

namespace Cochrane.IntertemporalModel.FiscalMonetary

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values of surpluses -/

/-- Cochrane (2023), eq. (2.7), p. 22: the ex-post discounted sum of surpluses
`∑_{j ≥ 0} βʲ s_{t+j}` (a genuine `tsum`, state by state). -/
noncomputable def epv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of surpluses
`PV_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (epv β s t)

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value
`E_t ∑_{j ≥ 1} βʲ s_{t+j}`, the real value of the debt sold at the end of date `t`. -/
noncomputable def pvEx (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * s (t + (j + 1)) ω)

/-- Cochrane (2023), eq. (2.7), p. 22: the ex-post discounted sum converges in every state at
every date. -/
def SurplusSummable (β : ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun j => β ^ j * s (t + j) ω)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.7), p. 22: summability of `∑ βʲ s_j` at date `0` gives it at every
date (`β ≠ 0`). -/
theorem surplusSummable_of_zero {β : ℝ} (hβ : β ≠ 0) {s : ℕ → Ω → ℝ}
    (h : ∀ ω, Summable (fun j => β ^ j * s j ω)) : SurplusSummable β s := by
  intro t ω
  have h1 : Summable (fun j => β ^ (j + t) * s (j + t) ω) := (summable_nat_add_iff t).mpr (h ω)
  refine (h1.mul_left ((β ^ t)⁻¹)).congr fun j => ?_
  rw [pow_add, add_comm j t]
  field_simp

omit 𝔼 in
/-- Cochrane (2023), eq. (2.7), p. 22: bounded surpluses and `0 ≤ β < 1` give summability. -/
theorem surplusSummable_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : SurplusSummable β s := by
  intro t ω
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hs (t + j) ω) (pow_nonneg hβ0 j)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend sum is `β` times next date's sum,
`∑_{j ≥ 1} βʲ s_{t+j} = β ∑_{j ≥ 0} βʲ s_{t+1+j}` (no summability needed). -/
theorem exsum_eq (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    (fun ω => ∑' j, β ^ (j + 1) * s (t + (j + 1)) ω) = β • epv β s (t + 1) := by
  funext ω
  simp only [epv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

omit 𝔼 in
/-- Cochrane (2023), eq. (2.26), p. 42 (ex post): `∑_{j≥0} βʲ s_{t+j} = s_t + β ∑_{j≥0} βʲ
s_{t+1+j}`. -/
theorem epv_succ {β : ℝ} {s : ℕ → Ω → ℝ} (hs : SurplusSummable β s) (t : ℕ) :
    epv β s t = s t + β • epv β s (t + 1) := by
  rw [← exsum_eq]
  funext ω
  simp only [epv, Pi.add_apply]
  rw [(hs t ω).tsum_eq_zero_add]
  simp

/-- Cochrane (2023), eq. (2.15), p. 31: `E_t ∑_{j≥1} βʲ s_{t+j} = β E_t PV_{t+1}`. -/
theorem pvEx_eq (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pvEx 𝔼 β s t = β • 𝔼.E t (pv 𝔼 β s (t + 1)) := by
  rw [pvEx, exsum_eq, map_smul, pv, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (2.7), p. 22: the present value is known at date `t`. -/
theorem pv_adapted (β : ℝ) (s : ℕ → Ω → ℝ) : 𝔼.Adapted (pv 𝔼 β s) := fun t =>
  𝔼.E_E_self t _

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value is known at date `t`. -/
theorem pvEx_adapted (β : ℝ) (s : ℕ → Ω → ℝ) : 𝔼.Adapted (pvEx 𝔼 β s) := fun t =>
  𝔼.E_E_self t _

/-- Cochrane (2023), eq. (2.26), p. 42: `E_t ∑_{j≥0} βʲ s_{t+j} = s_t + E_t ∑_{j≥1} βʲ s_{t+j}`
for adapted surpluses. -/
theorem pv_eq_add_pvEx {β : ℝ} {s : ℕ → Ω → ℝ} (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (t : ℕ) : pv 𝔼 β s t = s t + pvEx 𝔼 β s t := by
  rw [pv, epv_succ hs, map_add, hsa t, pvEx, exsum_eq]

/-- Cochrane (2023), eq. (2.15), p. 31: a uniform positive lower bound `PV ≥ c > 0` gives a
positive ex-dividend present value `≥ β c`. -/
theorem pvEx_ge {β c : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hc : ∀ t ω, c ≤ pv 𝔼 β s t ω) (t : ℕ) (ω : Ω) : β * c ≤ pvEx 𝔼 β s t ω := by
  rw [pvEx_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (const_le_E 𝔼 (hc (t + 1)) t ω) hβ

/-! ### Present values and innovations `ΔE_{t+1} = E_{t+1} − E_t` -/

/-- Cochrane (2023), eq. (2.12), p. 30: `E_t PV_{t+1} = E_t ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem E_pv_succ (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E t (pv 𝔼 β s (t + 1)) = 𝔼.E t (epv β s (t + 1)) := by
  rw [pv, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation in the present value
`ΔE_{t+1} PV_{t+1}` is the innovation in the ex-post sum `ΔE_{t+1} ∑ βʲ s_{t+1+j}`. -/
theorem news_pv_succ (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    innov 𝔼 t (pv 𝔼 β s (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  rw [pv, innov_E_succ]

/-! ### Equilibrium -/

/-- Cochrane (2023), eqs. (2.7) and (2.12), pp. 22, 30: the government debt valuation equation
at every date, `B_{−1}/P_0 = E_0 ∑ βʲ s_j` and `B_t/P_{t+1} = E_{t+1} ∑ βʲ s_{t+1+j}`. Here
`B t` is the nominal debt sold at the end of date `t` (it matures at `t + 1`) and `Bm1` is the
initial debt `B_{−1}`. -/
def Valuation (β : ℝ) (Bm1 : Ω → ℝ) (s B P : ℕ → Ω → ℝ) : Prop :=
  Bm1 / P 0 = pv 𝔼 β s 0 ∧ ∀ t, B t / P (t + 1) = pv 𝔼 β s (t + 1)

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: the bond price
`Q_t = 1/(1 + i_t) = β E_t(P_t/P_{t+1})` at every date. -/
def BondPricing (β : ℝ) (P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + i t)⁻¹ = β • 𝔼.E t (P t / P (t + 1))

/-- Cochrane (2023), §2.1–§2.4, pp. 21–33: an equilibrium of the frictionless intertemporal
model given surpluses `s` and initial debt `B_{−1}`: an adapted positive price level `P`, adapted
debt `B`, an adapted nominal rate `i > −1`, the valuation equation at every date (which is the
flow condition (2.5) plus the transversality condition (2.6)) and the bond-pricing condition
(2.3). Whether `B` (a debt-quantity policy) or `i` (an interest-rate target) is the policy
instrument is a matter of which of them is given. -/
def Equilibrium (β : ℝ) (Bm1 : Ω → ℝ) (s B P i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted P ∧ (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted B ∧ 𝔼.Adapted i ∧ (∀ t ω, -1 < i t ω) ∧
    Valuation 𝔼 β Bm1 s B P ∧ BondPricing 𝔼 β P i

variable {𝔼}
variable {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.7), p. 22, "the price level must adjust so that (2.7) holds": in
equilibrium `P_0 = B_{−1}/PV_0` (when `PV_0 ≠ 0`). -/
theorem price_zero (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) (hpv : pv 𝔼 β s 0 ω ≠ 0) :
    P 0 ω = Bm1 ω / pv 𝔼 β s 0 ω := by
  have h1 := congrFun h.2.2.2.2.2.1.1 ω
  simp only [Pi.div_apply] at h1
  rw [← h1] at hpv ⊢
  rw [div_div_cancel₀ (by intro h0; exact hpv (by rw [h0, zero_div]))]

/-- Cochrane (2023), eq. (2.12), p. 30: in equilibrium `P_{t+1} = B_t/PV_{t+1}` (when
`PV_{t+1} ≠ 0`): the price level is determined by the debt outstanding and the present value
of surpluses. -/
theorem price_succ (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hpv : pv 𝔼 β s (t + 1) ω ≠ 0) : P (t + 1) ω = B t ω / pv 𝔼 β s (t + 1) ω := by
  have h1 := congrFun (h.2.2.2.2.2.1.2 t) ω
  simp only [Pi.div_apply] at h1
  rw [← h1] at hpv ⊢
  rw [div_div_cancel₀ (by intro h0; exact hpv (by rw [h0, zero_div]))]

/-- Cochrane (2023), §2.4.1, p. 30: the real value of the debt `B_t/P_t` is known at `t`
(pull-out property). -/
theorem realDebt_known (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    𝔼.E t (B t / P t) = B t / P t :=
  E_div_known 𝔼 hPO (h.2.2.1 t) (h.1 t) (fun ω => (h.2.1 t ω).ne')

/-- Cochrane (2023), eq. (2.13), p. 30, **unexpected inflation**:
`(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem unexpected_inflation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  have hsplit : B t / P (t + 1) = (B t / P t) * (P t / P (t + 1)) := by
    funext ω
    have := (h.2.1 t ω).ne'
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp
  rw [← innov_mul_known 𝔼 hPO (realDebt_known hPO h t), ← hsplit, h.2.2.2.2.2.1.2 t,
    news_pv_succ]

/-- Cochrane (2023), eq. (2.13), p. 30: unexpected inflation is the present-value news divided
by the real value of the debt. -/
theorem unexpected_inflation_eq (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ)
    (ω : Ω) (hB : B t ω ≠ 0) :
    innov 𝔼 t (P t / P (t + 1)) ω = innov 𝔼 t (epv β s (t + 1)) ω / (B t ω / P t ω) := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hP := (h.2.1 t ω).ne'
  rw [← h1]
  field_simp

/-- Cochrane (2023), p. 30, bullet: "unexpected inflation is determined entirely by changing
expectations of the present value of fiscal surpluses": with debt outstanding, unexpected
inflation is zero exactly when the present-value news is zero. -/
theorem no_surprise_iff (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hB : B t ω ≠ 0) :
    innov 𝔼 t (P t / P (t + 1)) ω = 0 ↔ innov 𝔼 t (epv β s (t + 1)) ω = 0 := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hV : B t ω / P t ω ≠ 0 := div_ne_zero hB (h.2.1 t ω).ne'
  rw [← h1]
  constructor
  · intro h0; rw [h0, mul_zero]
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left hV

/-- Cochrane (2023), p. 42 and §2.8, p. 44: with positive debt, a positive present-value news
produces a disinflation `ΔE_{t+1}(P_t/P_{t+1}) > 0`, and conversely. -/
theorem disinflation_iff (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hB : 0 < B t ω) :
    0 < innov 𝔼 t (P t / P (t + 1)) ω ↔ 0 < innov 𝔼 t (epv β s (t + 1)) ω := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hV : 0 < B t ω / P t ω := div_pos hB (h.2.1 t ω)
  rw [← h1]
  exact (mul_pos_iff_of_pos_left hV).symm

/-- Cochrane (2023), p. 30, "you can't expect future unexpected shocks": in equilibrium the
date-`t` forecast of every later unexpected inflation is zero. -/
theorem E_unexpected_inflation_zero (t k : ℕ) :
    𝔼.E t (innov 𝔼 (t + k) (P (t + k) / P (t + k + 1))) = 0 :=
  E_innov_zero_of_le 𝔼 (Nat.le_add_right t k) _

/-- Cochrane (2023), §2.4.2, p. 30 (display after (2.13)): **expected inflation**,
`(B_t/P_t) E_t(P_t/P_{t+1}) = E_t ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem expected_inflation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * 𝔼.E t (P t / P (t + 1)) = 𝔼.E t (epv β s (t + 1)) := by
  have hsplit : B t / P (t + 1) = (B t / P t) * (P t / P (t + 1)) := by
    funext ω
    have := (h.2.1 t ω).ne'
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp
  rw [← hPO t _ _ (realDebt_known hPO h t), ← hsplit, h.2.2.2.2.2.1.2 t, E_pv_succ]

/-- Cochrane (2023), eqs. (2.14)–(2.15), p. 31: the real revenue from bond sales,
`(B_t/P_t)/(1 + i_t) = (B_t/P_t) β E_t(P_t/P_{t+1}) = E_t ∑_{j≥1} βʲ s_{t+j}`. -/
theorem expected_valuation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * (1 + i t)⁻¹ = β • ((B t / P t) * 𝔼.E t (P t / P (t + 1))) ∧
      (B t / P t) * (1 + i t)⁻¹ = pvEx 𝔼 β s t := by
  have h1 : (B t / P t) * (1 + i t)⁻¹ = β • ((B t / P t) * 𝔼.E t (P t / P (t + 1))) := by
    rw [h.2.2.2.2.2.2 t, mul_smul_comm]
  refine ⟨h1, ?_⟩
  rw [h1, expected_inflation hPO h t, pvEx_eq, E_pv_succ]

/-- Cochrane (2023), eq. (2.15), p. 31, and p. 43: in equilibrium the debt sold is
`B_t = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j}`. -/
theorem debt_eq (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω = (1 + i t ω) * P t ω * pvEx 𝔼 β s t ω := by
  have h1 := congrFun (expected_valuation hPO h t).2 ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply] at h1
  have hP := (h.2.1 t ω).ne'
  have hi : 1 + i t ω ≠ 0 := by linarith [h.2.2.2.2.1 t ω]
  rw [← h1]
  field_simp

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42: the flow condition in real terms,
`B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1}) = s_{t+1} + E_{t+1} ∑_{j≥1} βʲ
s_{t+1+j}`. -/
theorem eq_2_26 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    B t / P (t + 1) = s (t + 1) + (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹ ∧
      B t / P (t + 1) = s (t + 1) + pvEx 𝔼 β s (t + 1) := by
  rw [(expected_valuation hPO h (t + 1)).2, h.2.2.2.2.2.1.2 t, pv_eq_add_pvEx 𝔼 hs hsa]
  exact ⟨rfl, rfl⟩

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42, at the initial date:
`B_{−1}/P_0 = s_0 + (B_0/P_0)/(1 + i_0) = s_0 + E_0 ∑_{j≥1} βʲ s_j`. -/
theorem eq_2_26_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) :
    Bm1 / P 0 = s 0 + (B 0 / P 0) * (1 + i 0)⁻¹ ∧ Bm1 / P 0 = s 0 + pvEx 𝔼 β s 0 := by
  rw [(expected_valuation hPO h 0).2, h.2.2.2.2.2.1.1, pv_eq_add_pvEx 𝔼 hs hsa]
  exact ⟨rfl, rfl⟩

/-- Cochrane (2023), eq. (2.4), p. 22: the nominal flow condition
`B_t = P_{t+1} s_{t+1} + Q_{t+1} B_{t+1}` with `Q = 1/(1 + i)`. -/
theorem flow_nominal (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω = P (t + 1) ω * s (t + 1) ω + (1 + i (t + 1) ω)⁻¹ * B (t + 1) ω := by
  have h1 := congrFun (eq_2_26 hPO hs hsa h t).1 ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply] at h1
  have hP := (h.2.1 (t + 1) ω).ne'
  field_simp at h1
  linear_combination h1

/-- Cochrane (2023), eq. (2.27), p. 42: innovations in the flow condition,
`(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1}[s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1})]
= ΔE_{t+1}[s_{t+1} + E_{t+1} ∑_{j≥1} βʲ s_{t+1+j}]`. -/
theorem eq_2_27 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) =
        innov 𝔼 t (s (t + 1) + (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹) ∧
      (B t / P t) * innov 𝔼 t (P t / P (t + 1)) =
        innov 𝔼 t (s (t + 1) + pvEx 𝔼 β s (t + 1)) := by
  rw [← (eq_2_26 hPO hs hsa h t).1, ← (eq_2_26 hPO hs hsa h t).2, h.2.2.2.2.2.1.2 t,
    news_pv_succ, unexpected_inflation hPO h t]
  exact ⟨rfl, rfl⟩

/-! ### Debt sales with surpluses fixed: share split, revenue, future sales (§2.4.2) -/

/-- Cochrane (2023), p. 31, unit-elastic demand: two equilibria with the same surpluses raise
the same real revenue `(B_t/P_t)/(1 + i_t)` from bond sales, whatever debt they sell. -/
theorem revenue_invariant (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') (t : ℕ) :
    (B' t / P' t) * (1 + i' t)⁻¹ = (B t / P t) * (1 + i t)⁻¹ := by
  rw [(expected_valuation hPO h' t).2, (expected_valuation hPO h t).2]

/-- Cochrane (2023), p. 31, "changing expectations of future bond sales `ΔE_{t+1}B_{t+j}`,
`j ≥ 1`, make no difference": two equilibria with the same surpluses and the same debt up to
date `t` have the same price level up to date `t + 1`, whatever debt they sell later. -/
theorem future_sales_irrelevant {B' P' i' : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i)
    (h' : Equilibrium 𝔼 β Bm1 s B' P' i') (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) {t : ℕ}
    (hB : ∀ k ≤ t, B' k = B k) : ∀ k ≤ t + 1, P' k = P k := by
  intro k hk
  funext ω
  cases k with
  | zero => rw [price_zero h' ω (hpv 0 ω), price_zero h ω (hpv 0 ω)]
  | succ k =>
    rw [price_succ h' k ω (hpv _ ω), price_succ h k ω (hpv _ ω), hB k (by omega)]

/-- Cochrane (2023), p. 31, bullet and "selling bonds without changing surpluses is again like a
share split": scaling the debt sold at `t` by `λ > 0` with surpluses unchanged leaves the price
level up to `t` unchanged, scales `P_{t+1}` and the gross nominal rate `1 + i_t` by `λ`, divides
expected gross deflation `E_t(P_t/P_{t+1})` by `λ` and leaves the real revenue unchanged. -/
theorem shareSplit (hPO : 𝔼.PullOut) {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1 s B' P' i')
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) {t : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hBk : ∀ k < t, B' k = B k) (hBt : B' t = lam • B t) (hB0 : ∀ ω, B t ω ≠ 0) :
    (∀ k ≤ t, P' k = P k) ∧ P' (t + 1) = lam • P (t + 1) ∧ 1 + i' t = lam • (1 + i t) ∧
      𝔼.E t (P' t / P' (t + 1)) = lam⁻¹ • 𝔼.E t (P t / P (t + 1)) ∧
      (B' t / P' t) * (1 + i' t)⁻¹ = (B t / P t) * (1 + i t)⁻¹ := by
  have hPk : ∀ k ≤ t, P' k = P k := by
    intro k hk
    funext ω
    cases k with
    | zero => rw [price_zero h' ω (hpv 0 ω), price_zero h ω (hpv 0 ω)]
    | succ k =>
      rw [price_succ h' k ω (hpv _ ω), price_succ h k ω (hpv _ ω), hBk k (by omega)]
  have hPt := hPk t le_rfl
  have hP1 : P' (t + 1) = lam • P (t + 1) := by
    funext ω
    rw [price_succ h' t ω (hpv _ ω), Pi.smul_apply, price_succ h t ω (hpv _ ω), hBt,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  refine ⟨hPk, hP1, ?_, ?_, revenue_invariant hPO h h' t⟩
  · funext ω
    have e1 := debt_eq hPO h' t ω
    have e2 := debt_eq hPO h t ω
    rw [hBt, hPt, Pi.smul_apply, smul_eq_mul] at e1
    have hne : P t ω * pvEx 𝔼 β s t ω ≠ 0 := by
      intro h0
      apply hB0 ω
      rw [e2, mul_assoc, h0, mul_zero]
    simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2] at e1
    apply mul_right_cancel₀ hne
    linear_combination -e1
  · have hfun : P' t / P' (t + 1) = lam⁻¹ • (P t / P (t + 1)) := by
      funext ω
      rw [hP1, hPt]
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hfun, map_smul]

/-! ### Interest-rate targets (§2.4.3–§2.4.4) -/

/-- Cochrane (2023), §2.4.3, p. 31: the price level of the interest-rate-target equilibrium,
`P_0 = B_{−1}/PV_0`, `P_{t+1} = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j} / PV_{t+1}`. -/
noncomputable def pegP (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => Bm1 / pv 𝔼 β s 0
  | t + 1 => (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t / pv 𝔼 β s (t + 1)

/-- Cochrane (2023), eq. (2.15), p. 31: the debt the government sells at the interest-rate
target (the flat supply curve), `B_t = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j}`. -/
noncomputable def pegB (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ)
    (t : ℕ) : Ω → ℝ :=
  (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t

/-- Cochrane (2023), §2.4.3, p. 31: `P_{t+1} = B_t / PV_{t+1}` along the target equilibrium. -/
theorem pegP_succ (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    pegP 𝔼 β Bm1 s i (t + 1) = pegB 𝔼 β Bm1 s i t / pv 𝔼 β s (t + 1) := rfl

/-- Cochrane (2023), §2.4.3, p. 31: the target-equilibrium price level is positive. -/
theorem pegP_pos {Bm1 : Ω → ℝ} (hB : ∀ ω, 0 < Bm1 ω) (hi : ∀ t ω, -1 < i t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) (t : ℕ) (ω : Ω) :
    0 < pegP 𝔼 β Bm1 s i t ω := by
  induction t with
  | zero => exact div_pos (hB ω) (hpv 0 ω)
  | succ t ih =>
    have h1 : 0 < 1 + i t ω := by linarith [hi t ω]
    change 0 < (1 + i t ω) * pegP 𝔼 β Bm1 s i t ω * pvEx 𝔼 β s t ω / pv 𝔼 β s (t + 1) ω
    have := hpvEx t ω
    have := hpv (t + 1) ω
    positivity

/-- Cochrane (2023), bullets pp. 31–33, "the government can target nominal interest rates by
offering debt for sale with no change in surpluses": for every adapted target `i > −1`,
positive initial debt and positive present values, the target path `(pegP, pegB)` is an
equilibrium. -/
theorem peg_equilibrium (hPO : 𝔼.PullOut) (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    Equilibrium 𝔼 β Bm1 s (pegB 𝔼 β Bm1 s i) (pegP 𝔼 β Bm1 s i) i := by
  have hpos := pegP_pos (𝔼 := 𝔼) hB hi hpv hpvEx
  have hpvne : ∀ t ω, pv 𝔼 β s t ω ≠ 0 := fun t ω => (hpv t ω).ne'
  have hPa : 𝔼.Adapted (pegP 𝔼 β Bm1 s i) := by
    intro t
    induction t with
    | zero => exact E_div_known 𝔼 hPO hBm1 (pv_adapted 𝔼 β s 0) (hpvne 0)
    | succ t ih =>
      have hnum : 𝔼.E t ((1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t) =
          (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t :=
        E_mul_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) ih)
          (pvEx_adapted 𝔼 β s t)
      exact E_div_known 𝔼 hPO (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hnum)
        (pv_adapted 𝔼 β s (t + 1)) (hpvne (t + 1))
  have hBa : 𝔼.Adapted (pegB 𝔼 β Bm1 s i) := fun t =>
    E_mul_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) (hPa t))
      (pvEx_adapted 𝔼 β s t)
  have hBpos : ∀ t ω, 0 < pegB 𝔼 β Bm1 s i t ω := by
    intro t ω
    have h1 : 0 < 1 + i t ω := by linarith [hi t ω]
    change 0 < (1 + i t ω) * pegP 𝔼 β Bm1 s i t ω * pvEx 𝔼 β s t ω
    have := hpos t ω
    have := hpvEx t ω
    positivity
  refine ⟨hPa, hpos, hBa, hia, hi, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
  · funext ω
    change Bm1 ω / (Bm1 ω / pv 𝔼 β s 0 ω) = pv 𝔼 β s 0 ω
    rw [div_div_cancel₀ (hB ω).ne']
  · funext ω
    rw [pegP_succ]
    change pegB 𝔼 β Bm1 s i t ω / (pegB 𝔼 β Bm1 s i t ω / pv 𝔼 β s (t + 1) ω) = _
    rw [div_div_cancel₀ (hBpos t ω).ne']
  · set c : Ω → ℝ := ((1 + i t) * pvEx 𝔼 β s t)⁻¹ with hc
    have hca : 𝔼.E t c = c :=
      E_inv_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) (pvEx_adapted 𝔼 β s t))
        (fun ω => mul_ne_zero (by simp only [Pi.add_apply, Pi.one_apply]; linarith [hi t ω])
          (hpvEx t ω).ne')
    have hfun : pegP 𝔼 β Bm1 s i t / pegP 𝔼 β Bm1 s i (t + 1) = c * pv 𝔼 β s (t + 1) := by
      funext ω
      rw [pegP_succ]
      have h1 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
      have := (hpos t ω).ne'
      have := (hpvEx t ω).ne'
      have := hpvne (t + 1) ω
      simp only [hc, pegB, Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Pi.add_apply,
        Pi.one_apply]
      field_simp
    rw [hfun, hPO t c _ hca]
    funext ω
    have e := congrFun (pvEx_eq 𝔼 β s t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    have h1 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
    have := (hpvEx t ω).ne'
    simp only [hc, Pi.inv_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    rw [mul_left_comm, ← e]
    field_simp

/-- Cochrane (2023), bullet p. 33, "inflation can be stable and determinate under an interest
rate target, or even an interest-rate peg": any equilibrium with the target `i` is the target
path `(pegP, pegB)`. -/
theorem peg_unique (hPO : 𝔼.PullOut) (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0)
    (h : Equilibrium 𝔼 β Bm1 s B P i) :
    P = pegP 𝔼 β Bm1 s i ∧ B = pegB 𝔼 β Bm1 s i := by
  have hP : ∀ t, P t = pegP 𝔼 β Bm1 s i t := by
    intro t
    induction t with
    | zero =>
      funext ω
      rw [price_zero h ω (hpv 0 ω)]
      rfl
    | succ t ih =>
      funext ω
      rw [price_succ h t ω (hpv _ ω), debt_eq hPO h t ω, ih]
      rfl
  refine ⟨funext hP, funext fun t => ?_⟩
  funext ω
  rw [debt_eq hPO h t ω, hP t]
  rfl

/-- Cochrane (2023), §2.4.3–§2.4.4, pp. 31–33: existence and uniqueness of the equilibrium
under an interest-rate target (time-varying, state-contingent `i` allowed). -/
theorem peg_existsUnique (hPO : 𝔼.PullOut) (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Equilibrium 𝔼 β Bm1 s x.2 x.1 i := by
  refine ⟨(pegP 𝔼 β Bm1 s i, pegB 𝔼 β Bm1 s i),
    peg_equilibrium hPO hBm1 hB hia hi hpv hpvEx, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := peg_unique hPO (fun t ω => (hpv t ω).ne') hx
  exact Prod.ext h1 h2

/-- Cochrane (2023), p. 32, bullet "the nominal interest-rate target determines expected
inflation": in every equilibrium `E_t(P_t/P_{t+1}) = 1/(β(1 + i_t))`. -/
theorem peg_expected_inflation (hβ : β ≠ 0) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    𝔼.E t (P t / P (t + 1)) = β⁻¹ • (1 + i t)⁻¹ := by
  rw [h.2.2.2.2.2.2 t, smul_smul, inv_mul_cancel₀ hβ, one_smul]

/-- Cochrane (2023), p. 33, bullet "monetary policy can target the nominal interest rate, and
determine expected inflation ... fiscal policy determines unexpected inflation": in equilibrium
`P_t/P_{t+1} = 1/(β(1 + i_t)) + ΔE_{t+1} ∑ βʲ s_{t+1+j} / (B_t/P_t)`. -/
theorem inflation_decomposition (hPO : 𝔼.PullOut) (hβ : β ≠ 0)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) (hB : B t ω ≠ 0) :
    (P t / P (t + 1)) ω =
      β⁻¹ * (1 + i t ω)⁻¹ + innov 𝔼 t (epv β s (t + 1)) ω / (B t ω / P t ω) := by
  have hk : 𝔼.E (t + 1) (P t / P (t + 1)) = P t / P (t + 1) :=
    E_div_known 𝔼 hPO (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (h.1 t)) (h.1 (t + 1))
      (fun ω => (h.2.1 (t + 1) ω).ne')
  have e := congrFun (eq_E_add_innov 𝔼 hk) ω
  rw [e, Pi.add_apply, peg_expected_inflation hβ h t, unexpected_inflation_eq hPO h t ω hB]
  rfl

/-- Cochrane (2023), p. 30 ("bad fiscal news affects inflation for one period only") and
p. 33: two equilibria with the same interest-rate target have the same expected inflation at
every date, whatever their surpluses and initial debt. -/
theorem expected_inflation_indep_surplus (hβ : β ≠ 0) {Bm1' : Ω → ℝ} {s' B' P' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i) (t : ℕ) :
    𝔼.E t (P' t / P' (t + 1)) = 𝔼.E t (P t / P (t + 1)) := by
  rw [peg_expected_inflation hβ h' t, peg_expected_inflation hβ h t]

/-- Cochrane (2023), p. 32, "if the government raises the interest-rate target ... it will sell
... more nominal debt": with the same surpluses and the same current price level, debt sold is
proportional to the gross rate, `B'_t/B_t = (1 + i'_t)/(1 + i_t)`. -/
theorem debt_ratio_of_rate (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω) (hB : B t ω ≠ 0) :
    B' t ω / B t ω = (1 + i' t ω) / (1 + i t ω) := by
  have e1 := debt_eq hPO h' t ω
  have e2 := debt_eq hPO h t ω
  rw [hPt] at e1
  have hne : P t ω * pvEx 𝔼 β s t ω ≠ 0 := by
    intro h0; apply hB; rw [e2, mul_assoc, h0, mul_zero]
  rw [e1, e2, mul_assoc, mul_assoc, mul_div_mul_right _ _ hne]

/-- Cochrane (2023), p. 32 (survey E7): the exact proportional rise in nominal debt is
`ΔB/B = Δi/(1 + i)`. -/
theorem debt_growth_of_rate (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω) (hB : B t ω ≠ 0) :
    B' t ω / B t ω - 1 = (i' t ω - i t ω) / (1 + i t ω) := by
  rw [debt_ratio_of_rate hPO h h' hPt ω hB]
  have hi : 1 + i t ω ≠ 0 := by linarith [h.2.2.2.2.1 t ω]
  field_simp
  ring

/-- Cochrane (2023), p. 32 (survey E7): "one percentage point higher rate, one percent more
debt" is exact only at `i = 0`: `Δi/(1 + i) = Δi` iff `Δi = 0` or `i = 0`. -/
theorem rate_change_eq_debt_growth_iff {i0 i1 : ℝ} (hi : -1 < i0) :
    (i1 - i0) / (1 + i0) = i1 - i0 ↔ i1 = i0 ∨ i0 = 0 := by
  have h1 : 1 + i0 ≠ 0 := by linarith
  rw [div_eq_iff h1]
  constructor
  · intro h
    have : (i1 - i0) * i0 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h2 | h2
    · left; linarith
    · right; exact h2
  · rintro (h2 | h2)
    · rw [h2]; ring
    · rw [h2]; ring

/-- Cochrane (2023), p. 32 (survey E7): numerical counterexample to the printed "one percent":
raising the rate from 5% to 6% raises nominal debt by `1/105`, not `1/100`. -/
theorem printed_one_percent_fails : ((1 + 0.06) / (1 + 0.05) - 1 : ℝ) ≠ 0.01 := by
  norm_num

/-- Cochrane (2023), p. 32, "an attempt to fix the real rate in this model would lead to
infinite demands": with `c_t = y` the household Euler equation for a real bond priced at `q`
reads `q u'(y) = β u'(y)`, so the real bond price is forced to `β` (`R = 1/β`). -/
theorem real_rate_forced {u' q : ℝ} (hu : u' ≠ 0) (h : q * u' = β * u') : q = β :=
  mul_right_cancel₀ hu h

/-- Cochrane (2023), p. 32: a real-rate peg `q ≠ β` has no equilibrium: buying `x` real
bonds at price `q` changes utility by `u(y − q x) + β u(y + x)`, whose derivative at `x = 0` is
`(β − q) u'(y) ≠ 0`, so consuming the endowment is not optimal. -/
theorem no_eqm_real_rate_peg {u : ℝ → ℝ} {u' y q : ℝ} (hu : HasDerivAt u u' y) (hu' : u' ≠ 0)
    (hq : q ≠ β) : ¬ IsLocalMax (fun x => u (y - q * x) + β * u (y + x)) 0 := by
  intro hmax
  have h1 : HasDerivAt (fun x : ℝ => y - q * x) (-q) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub y
  have h2 : HasDerivAt (fun x : ℝ => y + x) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add y
  have hu1 : HasDerivAt u u' (y - q * 0) := by simpa using hu
  have hu2 : HasDerivAt u u' (y + 0) := by simpa using hu
  have hd : HasDerivAt (fun x => u (y - q * x) + β * u (y + x)) (u' * -q + β * (u' * 1)) 0 :=
    HasDerivAt.add (hu1.comp 0 h1) ((hu2.comp 0 h2).const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hd
  apply hq
  apply mul_right_cancel₀ hu'
  linear_combination -h0

/-- Cochrane (2023), p. 32, "infinite demands": with linear utility a real-rate peg `q ≠ β`
makes the gain from trading real bonds unbounded. -/
theorem real_rate_peg_unbounded {y q : ℝ} (hq : q ≠ β) (M : ℝ) :
    ∃ x, M < (y - q * x) + β * (y + x) - (y + β * y) := by
  have hne : β - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  refine ⟨(|M| + 1) / (β - q), ?_⟩
  have : (y - q * ((|M| + 1) / (β - q))) + β * (y + (|M| + 1) / (β - q)) - (y + β * y) =
      |M| + 1 := by
    field_simp
    ring
  rw [this]
  linarith [le_abs_self M]

/-- Cochrane (2023), p. 33 (the classic doctrine: without the valuation equation the price
level is not determined): scaling a solution by `c > 0` preserves every equilibrium condition
except the initial valuation equation `B_{−1}/P_0 = PV_0`, which fails for `c ≠ 1`. -/
theorem scaled_all_but_initial (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) {c : ℝ}
    (hc : 0 < c) :
    𝔼.Adapted (fun t => c • P t) ∧ (∀ t ω, 0 < c * P t ω) ∧ 𝔼.Adapted (fun t => c • B t) ∧
      (∀ t, c • B t / c • P (t + 1) = pv 𝔼 β s (t + 1)) ∧
      BondPricing 𝔼 β (fun t => c • P t) i := by
  have _ := hPO
  refine ⟨fun t => by simp only [map_smul, h.1 t], fun t ω => mul_pos hc (h.2.1 t ω),
    fun t => by simp only [map_smul, h.2.2.1 t], fun t => ?_, fun t => ?_⟩
  · rw [← h.2.2.2.2.2.1.2 t]
    funext ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hc.ne']
  · rw [h.2.2.2.2.2.2 t]
    congr 2
    funext ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hc.ne']

/-- Cochrane (2023), p. 33: the initial valuation equation pins the scale: for `c ≠ 1` and
nonzero initial debt the scaled price level violates `B_{−1}/P_0 = PV_0`. -/
theorem scaled_not_initial (h : Equilibrium 𝔼 β Bm1 s B P i) {c : ℝ} (hc : c ≠ 1) {ω : Ω}
    (hB : Bm1 ω ≠ 0) : Bm1 / (c • P 0) ≠ pv 𝔼 β s 0 := by
  intro h1
  have e1 := congrFun h1 ω
  have e2 := congrFun h.2.2.2.2.2.1.1 ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  have hP := (h.2.1 0 ω).ne'
  rw [← e2] at e1
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_mul, div_zero] at e1; exact hB (by field_simp at e1; linarith)
  field_simp at e1
  exact hc e1.symm

/-- Cochrane (2023), p. 33, perfect foresight: the bond-pricing condition is
`P_{t+1} = β (1 + i_t) P_t`, so monetary policy alone gives a family of price paths. -/
theorem pf_pricing_iff (hβ : β ≠ 0) {P i : ℕ → Unit → ℝ} (hP : ∀ t u, 0 < P t u)
    (hi : ∀ t u, -1 < i t u) :
    BondPricing perfectForesight β P i ↔ ∀ t, P (t + 1) () = β * (1 + i t ()) * P t () := by
  constructor
  · intro h t
    have e := congrFun (h t) ()
    change (1 + i t ())⁻¹ = β * (P t () / P (t + 1) ()) at e
    have h1 : 1 + i t () ≠ 0 := by linarith [hi t ()]
    have := (hP t ()).ne'
    have := (hP (t + 1) ()).ne'
    field_simp at e
    linear_combination e
  · intro h t
    funext u
    cases u
    change (1 + i t ())⁻¹ = β * (P t () / P (t + 1) ())
    have h1 : 1 + i t () ≠ 0 := by linarith [hi t ()]
    have := (hP t ()).ne'
    rw [h t]
    field_simp

/-- Cochrane (2023), p. 33, "fiscal policy only determines ... the time-zero price level ...
thereby choosing which of the many price level paths is unique": under perfect foresight every
equilibrium has `P_t = (B_{−1}/PV_0) ∏_{k<t} β(1 + i_k)`. -/
theorem pf_price_formula {Bm1 : Unit → ℝ} {s B P i : ℕ → Unit → ℝ}
    (hβ : β ≠ 0) (h : Equilibrium perfectForesight β Bm1 s B P i)
    (hpv : pv perfectForesight β s 0 () ≠ 0)
    (t : ℕ) :
    P t () = Bm1 () / pv perfectForesight β s 0 () *
      ∏ k ∈ Finset.range t, (β * (1 + i k ())) := by
  have hrec := (pf_pricing_iff hβ h.2.1 h.2.2.2.2.1).mp h.2.2.2.2.2.2
  induction t with
  | zero => simp [price_zero h () hpv]
  | succ t ih =>
    rw [hrec t, ih, Finset.prod_range_succ]
    ring

/-- Cochrane (2023), p. 33: under perfect foresight every scale `c > 0` gives a path
`c ∏_{k<t} β(1 + i_k)` satisfying the bond-pricing condition (the family generated by monetary
policy, of which the valuation equation selects `c = B_{−1}/PV_0`). -/
theorem pf_family {i : ℕ → Unit → ℝ} (hβ : 0 < β) (hi : ∀ t u, -1 < i t u) {c : ℝ}
    (hc : 0 < c) :
    BondPricing perfectForesight β
      (fun t _ => c * ∏ k ∈ Finset.range t, (β * (1 + i k ()))) i := by
  have hpos : ∀ t (u : Unit), 0 < c * ∏ k ∈ Finset.range t, (β * (1 + i k ())) := by
    intro t _
    refine mul_pos hc (Finset.prod_pos fun k _ => mul_pos hβ (by linarith [hi k ()]))
  refine (pf_pricing_iff hβ.ne' hpos hi).mpr fun t => ?_
  rw [Finset.prod_range_succ]
  ring


/-! ### Fiscal policy and debt (§2.7) -/

/-- Cochrane (2023), eq. (2.7), p. 22: for bounded surpluses the date-`r` forecast of the
ex-post sum is the sum of forecasts, `E_r ∑ βʲ s_{t+j} = ∑ βʲ E_r s_{t+j}`. -/
theorem E_epv_tsum {M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M)
    (r t : ℕ) (ω : Ω) : 𝔼.E r (epv β s t) ω = ∑' j, β ^ j * 𝔼.E r (s (t + j)) ω := by
  have hb : ∀ j ω', |β ^ j * s (t + j) ω'| ≤ β ^ j * M := fun j ω' => by
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + j) ω') (pow_nonneg hβ0 j)
  change 𝔼.E r (fun ω' => ∑' j, β ^ j * s (t + j) ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb r ω]
  refine tsum_congr fun j => ?_
  change 𝔼.E r (β ^ j • s (t + j)) ω = _
  rw [map_smul]
  rfl

/-- Cochrane (2023), p. 43: for bounded surpluses the present-value news is the discounted sum
of surplus news, `ΔE_{t+1} ∑ βʲ s_{t+1+j} = ∑ βʲ ΔE_{t+1} s_{t+1+j}`. -/
theorem news_epv_tsum {M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (epv β s (t + 1)) ω = ∑' j, β ^ j * innov 𝔼 t (s (t + 1 + j)) ω := by
  have hsum : ∀ r, Summable (fun j => β ^ j * 𝔼.E r (s (t + 1 + j)) ω) := fun r =>
    summable_E_shift 𝔼 hβ0 hβ1 hs r (t + 1) ω
  simp only [innov, Pi.sub_apply]
  rw [E_epv_tsum hβ0 hβ1 hs, E_epv_tsum hβ0 hβ1 hs, ← (hsum (t + 1)).tsum_sub (hsum t)]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), p. 43, "the surplus process must have an s-shaped moving average": if the
discounted sum of news `∑ βʲ d_j` is zero and the current news `d_0` is a deficit, some later
news `d_j`, `j ≥ 1`, is a surplus. -/
theorem sShape_seq (hβ : 0 < β) {d : ℕ → ℝ} (hd : Summable (fun j => β ^ j * d j))
    (h0 : ∑' j, β ^ j * d j = 0) (hd0 : d 0 < 0) : ∃ j, 1 ≤ j ∧ 0 < d j := by
  by_contra hc
  push Not at hc
  have htail : ∑' j, β ^ (j + 1) * d (j + 1) ≤ 0 :=
    tsum_nonpos fun j => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le _)
      (hc (j + 1) (by omega))
  rw [hd.tsum_eq_zero_add] at h0
  simp only [pow_zero, one_mul] at h0
  linarith

/-- Cochrane (2023), p. 43: with bounded surpluses, zero unexpected present value and a current
deficit shock `ΔE_{t+1} s_{t+1} < 0` force a later positive surplus shock (the s-shape). -/
theorem sShape {M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω)
    (h0 : innov 𝔼 t (epv β s (t + 1)) ω = 0) (hd : innov 𝔼 t (s (t + 1)) ω < 0) :
    ∃ j, 1 ≤ j ∧ 0 < innov 𝔼 t (s (t + 1 + j)) ω := by
  have hsum : Summable (fun j => β ^ j * innov 𝔼 t (s (t + 1 + j)) ω) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right (M + M)) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0.le]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le j)
    simp only [innov, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hs _) _ ω) (𝔼.abs_E_le (hs _) _ ω))
  rw [news_epv_tsum hβ0.le hβ1 hs] at h0
  exact sShape_seq hβ0 hsum h0 (by simpa using hd)

/-- Cochrane (2023), p. 42, "a credible fiscal reform can coexist with ongoing or even larger
short-term deficits, yet produce a disinflation": a pattern of surplus news with deficits at the
first two dates and a positive present value. -/
theorem reform_with_deficits (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ d : ℕ → ℝ, d 0 < 0 ∧ d 1 < 0 ∧ Summable (fun j => β ^ j * d j) ∧
      0 < ∑' j, β ^ j * d j := by
  set d : ℕ → ℝ := fun j => if j = 2 then 3 / β ^ 2 else if j < 2 then -1 else 0 with hd
  have hz : ∀ j ∉ Finset.range 3, β ^ j * d j = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [hd, show j ≠ 2 by omega, show ¬ j < 2 by omega, ↓reduceIte, mul_zero]
  refine ⟨d, by simp [hd], by simp [hd], summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd]
  norm_num
  field_simp
  linarith

/-- Cochrane (2023), p. 42, the equity issue: if two equilibria share the current price level
and the debt sold rises in proportion to the expected subsequent surpluses
(`B'_t PV^{ex}_t = B_t PV'^{ex}_t`), the nominal rate is unchanged and real revenue rises in
proportion to the debt. -/
theorem equityIssue (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {s' B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω)
    (hprop : B' t ω * pvEx 𝔼 β s t ω = B t ω * pvEx 𝔼 β s' t ω)
    (hex : pvEx 𝔼 β s t ω ≠ 0) (hex' : pvEx 𝔼 β s' t ω ≠ 0) :
    i' t ω = i t ω ∧
      ((B' t / P' t) * (1 + i' t)⁻¹) ω * B t ω = ((B t / P t) * (1 + i t)⁻¹) ω * B' t ω := by
  have e1 := debt_eq hPO h' t ω
  have e2 := debt_eq hPO h t ω
  rw [hPt] at e1
  have hP := (h.2.1 t ω).ne'
  refine ⟨?_, ?_⟩
  · rw [e1, e2] at hprop
    have : (i' t ω - i t ω) * (P t ω * pvEx 𝔼 β s' t ω * pvEx 𝔼 β s t ω) = 0 := by
      linear_combination hprop
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exfalso
      exact mul_ne_zero (mul_ne_zero hP hex') hex h0
  · rw [(expected_valuation hPO h' t).2, (expected_valuation hPO h t).2]
    linear_combination -hprop

/-- Cochrane (2023), p. 42, "this extra money can finance a deficit, a lower `s_t`, with no
unexpected inflation": with the same debt outstanding, a deficit `s'_{t+1} = s_{t+1} − δ`
matched by higher subsequent surpluses `PV'^{ex}_{t+1} = PV^{ex}_{t+1} + δ` leaves the price
level unchanged and raises real bond revenue by `δ`. -/
theorem equityIssue_finances_deficit (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ}
    {s' B' P' i' : ℕ → Ω → ℝ} (hs : SurplusSummable β s) (hs' : SurplusSummable β s')
    (hsa : 𝔼.Adapted s) (hsa' : 𝔼.Adapted s') (h : Equilibrium 𝔼 β Bm1 s B P i)
    (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ} {δ : Ω → ℝ} (hBt : B' t = B t)
    (hst : s' (t + 1) = s (t + 1) - δ) (hex : pvEx 𝔼 β s' (t + 1) = pvEx 𝔼 β s (t + 1) + δ)
    (hpv : ∀ ω, pv 𝔼 β s (t + 1) ω ≠ 0) :
    P' (t + 1) = P (t + 1) ∧
      (B' (t + 1) / P' (t + 1)) * (1 + i' (t + 1))⁻¹ =
        (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹ + δ := by
  have hpveq : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) := by
    rw [pv_eq_add_pvEx 𝔼 hs' hsa', pv_eq_add_pvEx 𝔼 hs hsa, hst, hex]
    abel
  refine ⟨funext fun ω => ?_, ?_⟩
  · rw [price_succ h' t ω (by rw [hpveq]; exact hpv ω), price_succ h t ω (hpv ω), hBt, hpveq]
  · rw [(expected_valuation hPO h' (t + 1)).2, (expected_valuation hPO h (t + 1)).2, hex]

/-! ### AR(1) surpluses (§2.7, p. 43) -/

/-- Cochrane (2023), p. 43: for an AR(1) surplus `E_t s_{t+1} = η s_t`, the news about
`s_{t+1+j}` is `ηʲ ε_{s,t+1}` with `ε_{s,t+1} = s_{t+1} − η s_t`. -/
theorem ar1_news {η : ℝ} (hAR : 𝔼.IsAR1 η s) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = η ^ j • (s (t + 1) - η • s t) := by
  rw [innov, 𝔼.ar1_iterate hAR (t + 1) j, show t + 1 + j = t + (j + 1) by omega,
    𝔼.ar1_iterate hAR t (j + 1), smul_sub, smul_smul, pow_succ]

/-- Cochrane (2023), p. 43: for a bounded AR(1) surplus the present-value news is
`ΔE_{t+1} ∑ βʲ s_{t+1+j} = ε_{s,t+1}/(1 − βη)`. -/
theorem ar1_pv_news {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) :
    innov 𝔼 t (epv β s (t + 1)) = (1 - β * η)⁻¹ • (s (t + 1) - η • s t) := by
  funext ω
  rw [news_epv_tsum hβ0 hβ1 hs]
  simp only [ar1_news hAR, Pi.smul_apply, smul_eq_mul]
  have : ∀ j : ℕ, β ^ j * (η ^ j * (s (t + 1) - η • s t) ω) =
      (β * η) ^ j * (s (t + 1) - η • s t) ω := fun j => by rw [mul_pow]; ring
  simp only [this]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hβη]

/-- Cochrane (2023), p. 43, corrected (survey E5): with an AR(1) surplus the unexpected
inflation satisfies `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)`; the printed
`ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)` omits the factor `B_t/P_t`. -/
theorem ar1_unexpected_inflation (hPO : 𝔼.PullOut) {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβη : |β * η| < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) = (1 - β * η)⁻¹ • (s (t + 1) - η • s t) := by
  rw [unexpected_inflation hPO h t, ar1_pv_news hβ0 hβ1 hβη hs hAR]

/-- Cochrane (2023), p. 43 (survey E5): the printed formula
`ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)` fails whenever the shock is nonzero and the real
value of the debt `B_t/P_t` differs from one. -/
theorem ar1_printed_fails (hPO : 𝔼.PullOut) {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβη : |β * η| < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hε : (s (t + 1) - η • s t) ω ≠ 0) (hV : B t ω / P t ω ≠ 1) :
    innov 𝔼 t (P t / P (t + 1)) ω ≠ ((1 - β * η)⁻¹ • (s (t + 1) - η • s t)) ω := by
  intro he
  have e := congrFun (ar1_unexpected_inflation hPO hβ0 hβ1 hβη hs hAR h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at e
  rw [he] at e
  have h1 : 1 - β * η ≠ 0 := by
    intro h0; rw [show β * η = 1 by linarith, abs_one] at hβη; exact lt_irrefl _ hβη
  have hx : ((1 - β * η)⁻¹ • (s (t + 1) - η • s t)) ω ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero h1) hε
  apply hV
  apply mul_right_cancel₀ hx
  rw [one_mul, e]

/-- Cochrane (2023), p. 43: for an AR(1) surplus the news about the value of the debt sold,
`ΔE_{t+1} ∑_{j≥1} βʲ s_{t+1+j}`, is `βη/(1 − βη) ε_{s,t+1}`. -/
theorem ar1_value_news {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) :
    innov 𝔼 t (pvEx 𝔼 β s (t + 1)) = (β * η * (1 - β * η)⁻¹) • (s (t + 1) - η • s t) := by
  have hsum := surplusSummable_of_bounded hβ0 hβ1 hs
  have hpe : pvEx 𝔼 β s (t + 1) = pv 𝔼 β s (t + 1) - s (t + 1) := by
    rw [pv_eq_add_pvEx 𝔼 hsum hAR.1]; abel
  have hn0 := ar1_news hAR t 0
  simp only [add_zero, pow_zero, one_smul] at hn0
  rw [hpe, innov_sub, news_pv_succ, ar1_pv_news hβ0 hβ1 hβη hs hAR, hn0]
  have h1 : 1 - β * η ≠ 0 := by
    intro h0; rw [show β * η = 1 by linarith, abs_one] at hβη; exact lt_irrefl _ hβη
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), p. 43, "the AR(1) generates a value of debt ... that goes down when there
is a deficit": with `0 < βη < 1` a deficit shock lowers the value of the debt. -/
theorem ar1_value_falls {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hpos : 0 < β * η)
    (hlt : β * η < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) (ω : Ω)
    (hε : (s (t + 1) - η • s t) ω < 0) : innov 𝔼 t (pvEx 𝔼 β s (t + 1)) ω < 0 := by
  have hβη : |β * η| < 1 := by rw [abs_of_pos hpos]; exact hlt
  rw [ar1_value_news hβ0 hβ1 hβη hs hAR, Pi.smul_apply, smul_eq_mul]
  have : 0 < β * η * (1 - β * η)⁻¹ := mul_pos hpos (inv_pos.mpr (by linarith))
  exact mul_neg_of_pos_of_neg this hε

/-- Cochrane (2023), p. 43, "unexpected inflation is larger than the deficit shock": for
`0 < βη < 1` and a deficit `ε < 0`, the present-value news `ε/(1 − βη)` is below `ε`. -/
theorem ar1_news_exceeds_deficit {η ε : ℝ} (hpos : 0 < β * η) (hlt : β * η < 1) (hε : ε < 0) :
    (1 - β * η)⁻¹ * ε < ε := by
  have h1 : 0 < 1 - β * η := by linarith
  rw [inv_mul_lt_iff₀ h1]
  nlinarith

/-! ### The central bank and the Treasury (§2.8) and fiscal stimulus (§2.10) -/

/-- Cochrane (2023), p. 33 and §2.8, p. 44: the split between Treasury and central bank is
irrelevant: if the central bank finances its holdings `B^C` of Treasury debt by overnight
reserves `R = B^C` (perfect substitutes for bonds), the equilibrium conditions depend only on
the debt held by the public, `B^T − B^C + R = B^T`. -/
theorem consolidation_irrelevant {BT BC R : ℕ → Ω → ℝ} (hcb : ∀ t, R t = BC t) :
    Equilibrium 𝔼 β Bm1 s (fun t => BT t - BC t + R t) P i ↔ Equilibrium 𝔼 β Bm1 s BT P i := by
  have : (fun t => BT t - BC t + R t) = BT := funext fun t => by rw [hcb t]; abel
  rw [this]

/-- Cochrane (2023), p. 50, "borrow money, ... spend the money, repay the debt has no effect at
all on current ... inflation": a rearrangement of surpluses that leaves the present value at
`t + 1` unchanged, with the same debt outstanding, leaves `P_{t+1}` unchanged. -/
theorem stimulus_no_jump {s' B' P' i' : ℕ → Ω → ℝ} {Bm1' : Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ}
    (hBt : B' t = B t) (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1))
    (hpv0 : ∀ ω, pv 𝔼 β s (t + 1) ω ≠ 0) : P' (t + 1) = P (t + 1) := by
  funext ω
  rw [price_succ h' t ω (by rw [hpv]; exact hpv0 ω), price_succ h t ω (hpv0 ω), hBt, hpv]

/-- Cochrane (2023), p. 50, perfect foresight: a rearrangement of surpluses with the same
initial present value and the same interest-rate target leaves the whole price path unchanged
(no effect on current or expected future inflation). -/
theorem pf_stimulus_neutral (hβ : β ≠ 0) {s' B' P' : ℕ → Unit → ℝ} {Bm1 : Unit → ℝ}
    {s B P i : ℕ → Unit → ℝ} (h : Equilibrium perfectForesight β Bm1 s B P i)
    (h' : Equilibrium perfectForesight β Bm1 s' B' P' i)
    (hpv : pv perfectForesight β s' 0 = pv perfectForesight β s 0)
    (hpv0 : pv perfectForesight β s 0 () ≠ 0) : P' = P := by
  funext t u
  cases u
  rw [pf_price_formula hβ h' (by rw [hpv]; exact hpv0), pf_price_formula hβ h hpv0, hpv]

/-- Cochrane (2023), p. 50, corrected for uncertainty: a stimulus that adds a date-`t`-known
amount `D` to the present value at `t + 1` (same target `i`, same `P_t`) leaves `P_{t+1}`
unchanged in state `ω` iff `D = 0` there or there is no other fiscal news
`ΔE_{t+1} ∑ βʲ s_{t+1+j} = 0`. Under genuine uncertainty "no effect at all" fails. -/
theorem stimulus_price_iff (hPO : 𝔼.PullOut) (hβ : β ≠ 0) {s' B' P' : ℕ → Ω → ℝ}
    {Bm1' : Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i)
    {t : ℕ} (hPt : P' t = P t) {D : Ω → ℝ} (hD : 𝔼.E t D = D)
    (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) + D) (ω : Ω)
    (hpv0 : pv 𝔼 β s (t + 1) ω ≠ 0) (hpv0' : pv 𝔼 β s' (t + 1) ω ≠ 0) :
    P' (t + 1) ω = P (t + 1) ω ↔ D ω = 0 ∨ innov 𝔼 t (epv β s (t + 1)) ω = 0 := by
  have hex' : pvEx 𝔼 β s' t = pvEx 𝔼 β s t + β • D := by
    rw [pvEx_eq, pvEx_eq, hpv, map_add, hD, smul_add]
  have e1 : P' (t + 1) ω = (1 + i t ω) * P t ω * (pvEx 𝔼 β s t ω + β * D ω) /
      (pv 𝔼 β s (t + 1) ω + D ω) := by
    rw [price_succ h' t ω hpv0', debt_eq hPO h' t ω, hPt, hex', hpv]
    rfl
  have e2 : P (t + 1) ω = (1 + i t ω) * P t ω * pvEx 𝔼 β s t ω / pv 𝔼 β s (t + 1) ω := by
    rw [price_succ h t ω hpv0, debt_eq hPO h t ω]
  have hnews : innov 𝔼 t (epv β s (t + 1)) ω = pv 𝔼 β s (t + 1) ω - β⁻¹ * pvEx 𝔼 β s t ω := by
    rw [← news_pv_succ, innov, pv_adapted 𝔼 β s (t + 1), pvEx_eq]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hden : pv 𝔼 β s (t + 1) ω + D ω ≠ 0 := by
    have := congrFun hpv ω; simp only [Pi.add_apply] at this; rwa [← this]
  have hc : (1 + i t ω) * P t ω ≠ 0 :=
    mul_ne_zero (by linarith [h.2.2.2.2.1 t ω]) (h.2.1 t ω).ne'
  rw [e1, e2, hnews, div_eq_div_iff hden hpv0]
  constructor
  · intro heq
    have : D ω * (β * pv 𝔼 β s (t + 1) ω - pvEx 𝔼 β s t ω) * ((1 + i t ω) * P t ω) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp this with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact Or.inl h1
      · right
        field_simp
        linear_combination h1
    · exact absurd h0 hc
  · rintro (h0 | h0)
    · rw [h0]; ring
    · field_simp at h0
      linear_combination ((1 + i t ω) * P t ω * D ω) * h0

/-- Cochrane (2023), p. 50, corrected for uncertainty: if a stimulus leaves the present-value
news unchanged, unexpected inflation is rescaled by the real value of the debt,
`(B'_t/P'_t) ΔE_{t+1}(P'_t/P'_{t+1}) = (B_t/P_t) ΔE_{t+1}(P_t/P_{t+1})`. -/
theorem stimulus_unexpected_inflation (hPO : 𝔼.PullOut) {s' B' P' i' : ℕ → Ω → ℝ}
    {Bm1' : Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i')
    {t : ℕ} (hn : innov 𝔼 t (epv β s' (t + 1)) = innov 𝔼 t (epv β s (t + 1))) :
    (B' t / P' t) * innov 𝔼 t (P' t / P' (t + 1)) = (B t / P t) * innov 𝔼 t (P t / P (t + 1)) := by
  rw [unexpected_inflation hPO h' t, unexpected_inflation hPO h t, hn]

/-- Cochrane (2023), p. 50: adding a date-`t`-known amount to the present value at `t + 1`
does not change the present-value news. -/
theorem news_pv_add_known {s' : ℕ → Ω → ℝ} {t : ℕ} {D : Ω → ℝ} (hD : 𝔼.E t D = D)
    (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) + D) :
    innov 𝔼 t (epv β s' (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  rw [← news_pv_succ, ← news_pv_succ, hpv, innov_add, innov_of_known 𝔼 hD, add_zero]


/-! ### A coin-flip economy: fiscal stimulus is not neutral under uncertainty -/

namespace CoinExample

open ExpectationsFiniteTree

/-- Cochrane (2023), p. 50 (example economy): the indicator of heads on the first coin. -/
def fh (b : Bool) : ℝ := if b then 1 else 0

/-- Cochrane (2023), p. 50 (example economy): the first-coin indicator is `0` or `1`. -/
theorem fh_nonneg (b : Bool) : 0 ≤ fh b := by cases b <;> simp [fh]

/-- Cochrane (2023), p. 50 (example economy): a variable that depends only on the first coin is
known from date `1` on. -/
theorem coin_E_first {t : ℕ} (ht : 1 ≤ t) (f : Bool → ℝ) :
    coinSystem.E t (fun ω => f ω.1) = fun ω => f ω.1 := by
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  refine coinTree.condE_of_const_on_cell fun ω' h => ?_
  have h' := coinTree.refines ht ω' ω h
  change Setoid.ker (coinObs 1) ω' ω at h'
  rw [Setoid.ker_def] at h'
  simp only [coinObs, Prod.mk.injEq] at h'
  obtain ⟨h1, -⟩ := h'
  simp only [le_refl, ↓reduceIte] at h1
  rw [h1]

/-- Cochrane (2023), p. 50 (example economy): at date `0` the first coin is forecast at
`1/2`, so `E_0(a + b·fh) = a + b/2`. -/
theorem coin_E_zero (a b : ℝ) :
    coinSystem.E 0 (fun ω => a + b * fh ω.1) = fun _ => a + b / 2 := by
  have hsplit : (fun ω : Bool × Bool => a + b * fh ω.1) = (fun _ => a) + b • firstHeads := by
    funext ω
    simp [fh, firstHeads]
  funext ω
  rw [hsplit, map_add, map_smul, coinSystem.const, Pi.add_apply, Pi.smul_apply,
    coinSystem_E0_firstHeads, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 50 (example economy): baseline surpluses `s_0 = 1`,
`s_t = 1 + fh` for `t ≥ 1` (news about all future surpluses arrives at date `1`). -/
noncomputable def sB (t : ℕ) : Bool × Bool → ℝ := fun ω => if t = 0 then 1 else 1 + fh ω.1

/-- Cochrane (2023), p. 50 (example economy): the stimulus "borrow, spend, repay": half a unit
less surplus at date `0`, one unit more at date `1` (`(1/2)/β` with `β = 1/2`), the rest
unchanged. -/
noncomputable def sS (t : ℕ) : Bool × Bool → ℝ :=
  fun ω => if t = 0 then 1 / 2 else if t = 1 then 2 + fh ω.1 else 1 + fh ω.1

/-- Cochrane (2023), p. 50 (example economy): with `β = 1/2`, a surplus `1 + fh` forever has
ex-post value `2(1 + fh)`. -/
theorem epv_tail {x : ℕ → Bool × Bool → ℝ} {t : ℕ}
    (hx : ∀ j, x (t + j) = fun ω => 1 + fh ω.1) :
    epv (1 / 2) x t = fun ω => 2 * (1 + fh ω.1) := by
  funext ω
  simp only [epv, hx]
  rw [tsum_mul_right, tsum_geometric_two]

/-- Cochrane (2023), p. 50 (example economy): the surpluses are bounded. -/
theorem sB_bounded : ∀ t ω, |sB t ω| ≤ 3 := by
  intro t ω
  have := fh_nonneg ω.1
  have : fh ω.1 ≤ 1 := by cases ω.1 <;> simp [fh]
  simp only [sB]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- Cochrane (2023), p. 50 (example economy): the stimulus surpluses are bounded. -/
theorem sS_bounded : ∀ t ω, |sS t ω| ≤ 3 := by
  intro t ω
  have := fh_nonneg ω.1
  have : fh ω.1 ≤ 1 := by cases ω.1 <;> simp [fh]
  simp only [sS]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- Cochrane (2023), p. 50 (example economy): baseline ex-post values from date `1` on. -/
theorem epv_sB_succ (t : ℕ) : epv (1 / 2) sB (t + 1) = fun ω => 2 * (1 + fh ω.1) :=
  epv_tail fun j => funext fun ω => by simp [sB]

/-- Cochrane (2023), p. 50 (example economy): stimulus ex-post values from date `2` on. -/
theorem epv_sS_add_two (t : ℕ) : epv (1 / 2) sS (t + 2) = fun ω => 2 * (1 + fh ω.1) :=
  epv_tail fun j => funext fun ω => by
    simp only [sS, show t + 2 + j ≠ 0 by omega, show t + 2 + j ≠ 1 by omega, ↓reduceIte]

/-- Cochrane (2023), p. 50 (example economy): the stimulus ex-post value at date `1` is
`3 + 2 fh`. -/
theorem epv_sS_one : epv (1 / 2) sS 1 = fun ω => 3 + 2 * fh ω.1 := by
  rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sS_bounded),
    epv_sS_add_two 0]
  funext ω
  simp only [sS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  ring

/-- Cochrane (2023), p. 50 (example economy): baseline and stimulus have the same date-`0`
present value `5/2`. -/
theorem pv_zero_eq : pv coinSystem (1 / 2) sS 0 = pv coinSystem (1 / 2) sB 0 ∧
    pv coinSystem (1 / 2) sB 0 = fun _ => 5 / 2 := by
  have h1 : epv (1 / 2) sB 0 = fun ω => 2 + 1 * fh ω.1 := by
    rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sB_bounded),
      epv_sB_succ 0]
    funext ω
    simp only [sB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  have h2 : epv (1 / 2) sS 0 = fun ω => 2 + 1 * fh ω.1 := by
    rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sS_bounded),
      epv_sS_one]
    funext ω
    simp only [sS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  refine ⟨by rw [pv, pv, h1, h2], ?_⟩
  rw [pv, h1, coin_E_zero]
  norm_num

/-- Cochrane (2023), p. 50 (example economy): baseline present values from date `1` on. -/
theorem pv_sB_succ (t : ℕ) : pv coinSystem (1 / 2) sB (t + 1) = fun ω => 2 * (1 + fh ω.1) := by
  rw [pv, epv_sB_succ]
  exact coin_E_first (by omega) (fun b => 2 * (1 + fh b))

/-- Cochrane (2023), p. 50 (example economy): the baseline present value at date `1`. -/
theorem pv_sB_one : pv coinSystem (1 / 2) sB 1 = fun ω => 2 * (1 + fh ω.1) := pv_sB_succ 0

/-- Cochrane (2023), p. 50 (example economy): stimulus present values from date `2` on. -/
theorem pv_sS_add_two (t : ℕ) :
    pv coinSystem (1 / 2) sS (t + 2) = fun ω => 2 * (1 + fh ω.1) := by
  rw [pv, epv_sS_add_two]
  exact coin_E_first (by omega) (fun b => 2 * (1 + fh b))

/-- Cochrane (2023), p. 50 (example economy): the stimulus raises the date-`1` present value by
the known amount `1`. -/
theorem pv_sS_one : pv coinSystem (1 / 2) sS 1 = pv coinSystem (1 / 2) sB 1 + fun _ => 1 := by
  rw [pv, epv_sS_one, coin_E_first le_rfl (fun b => 3 + 2 * fh b), pv_sB_one]
  funext ω
  simp only [Pi.add_apply]
  ring

/-- Cochrane (2023), p. 50 (example economy): all baseline present values are positive. -/
theorem pv_sB_pos (t : ℕ) (ω : Bool × Bool) : 0 < pv coinSystem (1 / 2) sB t ω := by
  have := fh_nonneg ω.1
  match t with
  | 0 => rw [pv_zero_eq.2]; norm_num
  | t + 1 => rw [pv_sB_succ]; positivity

/-- Cochrane (2023), p. 50 (example economy): all stimulus present values are positive. -/
theorem pv_sS_pos (t : ℕ) (ω : Bool × Bool) : 0 < pv coinSystem (1 / 2) sS t ω := by
  have := fh_nonneg ω.1
  match t with
  | 0 => rw [pv_zero_eq.1, pv_zero_eq.2]; norm_num
  | 1 => rw [pv_sS_one, Pi.add_apply, pv_sB_one]; positivity
  | t + 2 => rw [pv_sS_add_two]; positivity

/-- Cochrane (2023), p. 50 (example economy): all baseline ex-dividend values are positive. -/
theorem pvEx_sB_pos (t : ℕ) (ω : Bool × Bool) : 0 < pvEx coinSystem (1 / 2) sB t ω := by
  have := fh_nonneg ω.1
  have e : (fun ω : Bool × Bool => 2 * (1 + fh ω.1)) = fun ω => 2 + 2 * fh ω.1 := by
    funext ω; ring
  rw [pvEx_eq]
  match t with
  | 0 =>
    rw [pv_sB_one, e, coin_E_zero]
    norm_num
  | t + 1 =>
    rw [pv_sB_succ, coin_E_first (by omega) (fun b => 2 * (1 + fh b))]
    simp only [Pi.smul_apply, smul_eq_mul]
    positivity

/-- Cochrane (2023), p. 50 (example economy): all stimulus ex-dividend values are positive. -/
theorem pvEx_sS_pos (t : ℕ) (ω : Bool × Bool) : 0 < pvEx coinSystem (1 / 2) sS t ω := by
  have := fh_nonneg ω.1
  rw [pvEx_eq]
  match t with
  | 0 =>
    have e : (pv coinSystem (1 / 2) sS 1) = fun ω => 3 + 2 * fh ω.1 := by
      rw [pv_sS_one, pv_sB_one]
      funext ω; simp only [Pi.add_apply]; ring
    rw [e, coin_E_zero]
    norm_num
  | t + 1 =>
    rw [pv_sS_add_two, coin_E_first (by omega) (fun b => 2 * (1 + fh b))]
    simp only [Pi.smul_apply, smul_eq_mul]
    positivity

/-- Cochrane (2023), p. 50 (example economy): the date-`1` fiscal news is
`ΔE_1 ∑ βʲ s_{1+j} = 2 fh − 1 = ±1`. -/
theorem news_sB : innov coinSystem 0 (epv (1 / 2) sB (0 + 1)) = fun ω => 2 * fh ω.1 - 1 := by
  have hr : epv (1 / 2) sB (0 + 1) = fun ω => 2 + 2 * fh ω.1 := by
    rw [epv_sB_succ 0]; funext ω; ring
  rw [innov, hr, coin_E_first (by norm_num : 1 ≤ 0 + 1) (fun b => 2 + 2 * fh b), coin_E_zero]
  funext ω; simp only [Pi.sub_apply]; ring

/-- Cochrane (2023), p. 50 (example economy): the fiscal news is nonzero in every state. -/
theorem news_sB_ne (ω : Bool × Bool) : innov coinSystem 0 (epv (1 / 2) sB (0 + 1)) ω ≠ 0 := by
  rw [news_sB]
  cases hb : ω.1 <;> norm_num [hb, fh]

/-- Cochrane (2023), p. 50 (example economy): the coin-flip expectations have the pull-out
property. -/
theorem coin_pullOut : coinSystem.PullOut := finiteTree_pullOut coinTree

/-- Cochrane (2023), p. 50 (example economy): the baseline economy with a zero interest-rate
target and unit initial debt has an equilibrium. -/
theorem eqm_sB : Equilibrium coinSystem (1 / 2) (fun _ => 1) sB
    (pegB coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0)
    (pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) (fun _ _ => 0) :=
  peg_equilibrium coin_pullOut (coinSystem.const 0 1) (fun _ => one_pos)
    (fun t => coinSystem.const t 0) (fun _ _ => by norm_num) pv_sB_pos pvEx_sB_pos

/-- Cochrane (2023), p. 50 (example economy): the stimulus economy with the same target and
initial debt has an equilibrium. -/
theorem eqm_sS : Equilibrium coinSystem (1 / 2) (fun _ => 1) sS
    (pegB coinSystem (1 / 2) (fun _ => 1) sS fun _ _ => 0)
    (pegP coinSystem (1 / 2) (fun _ => 1) sS fun _ _ => 0) (fun _ _ => 0) :=
  peg_equilibrium coin_pullOut (coinSystem.const 0 1) (fun _ => one_pos)
    (fun t => coinSystem.const t 0) (fun _ _ => by norm_num) pv_sS_pos pvEx_sS_pos

/-- Cochrane (2023), p. 50, counterexample to "borrow money, don't drive up interest rates,
spend the money, repay the debt — has no effect at all on current, unexpected, or expected
future inflation" under genuine uncertainty: in the coin-flip economy the stimulus
(`s'_0 = s_0 − 1/2`, `s'_1 = s_1 + 1`, `s'_t = s_t` otherwise, `β = 1/2`) leaves the date-`0`
present value, the date-`0` price level and expected inflation unchanged, but changes the
date-`1` price level in every state. -/
theorem stimulus_not_neutral :
    (sS 0 = fun ω => sB 0 ω - 1 / 2) ∧ (sS 1 = fun ω => sB 1 ω + 1) ∧
      (∀ t, 2 ≤ t → sS t = sB t) ∧
      pv coinSystem (1 / 2) sS 0 = pv coinSystem (1 / 2) sB 0 ∧
      pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 =
        pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 ∧
      ∀ ω, pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 1 ω ≠
        pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 1 ω := by
  have hP0 : pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 =
      pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 := by
    change (fun _ => (1 : ℝ)) / pv coinSystem (1 / 2) sS 0 =
      (fun _ => (1 : ℝ)) / pv coinSystem (1 / 2) sB 0
    rw [pv_zero_eq.1]
  refine ⟨funext fun ω => by norm_num [sS, sB], funext fun ω => by (simp [sS, sB]; ring),
    fun t ht => funext fun ω => by
      simp only [sS, sB, show t ≠ 0 by omega, show t ≠ 1 by omega, ↓reduceIte],
    pv_zero_eq.1, hP0, fun ω => ?_⟩
  intro heq
  have hiff := stimulus_price_iff coin_pullOut (by norm_num) eqm_sB eqm_sS hP0
    (coinSystem.const 0 1) pv_sS_one ω (pv_sB_pos 1 ω).ne' (pv_sS_pos 1 ω).ne'
  rcases hiff.mp heq with h0 | h0
  · norm_num at h0
  · exact news_sB_ne ω h0

/-- Cochrane (2023), eq. (2.13), p. 30, under genuine uncertainty: in the coin-flip economy the
date-`1` fiscal news produces nonzero unexpected inflation in every state. -/
theorem coin_unexpected_inflation_ne (ω : Bool × Bool) :
    innov coinSystem 0 ((pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) 0 /
      (pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) (0 + 1)) ω ≠ 0 := by
  have hB : (pegB coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) 0 ω ≠ 0 := by
    rw [debt_eq coin_pullOut eqm_sB 0 ω]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (eqm_sB.2.1 0 ω).ne') (pvEx_sB_pos 0 ω).ne'
  rw [Ne, no_surprise_iff coin_pullOut eqm_sB 0 ω hB]
  exact news_sB_ne ω

end CoinExample

end Cochrane.IntertemporalModel.FiscalMonetary

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The flat supply curve

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.9, pp. 47–49.

The central bank sets the interest rate; the Treasury then chooses the face value of debt `B_t`
from the flow condition (2.28) `B_{t−1}/P_t = s_t + Q_t B_t/P_t` given the bond price
`Q_t = 1/(1 + i_t)`. Together they sell any quantity of debt at the fixed rate: a flat supply
curve meeting the unit-elastic demand for debt.

## Main results

* `eq_2_28`, `eq_2_28_zero`: the flow condition (2.28) holds in equilibrium (the book cites it as
  "the flow condition (2.15)"; it is (2.4)/(2.9), survey E9).
* `treasury_rule_iff`: (2.28) is equivalent to the Treasury rule `B_t = (B_{t−1} − P_t s_t)/Q_t`;
  `treasury_rule_of_equilibrium`, `treasury_rule_of_equilibrium_zero`.
* `flat_supply_revenue`: whatever bond price the central bank sets, the Treasury rule raises the
  same nominal revenue `Q_t B_t = B_{t−1} − P_t s_t`; `flat_supply_meets_demand`: for every bond
  price exactly one quantity meets the unit-elastic demand `Q_t B_t/P_t = PV^{ex}_t`.
* `treasury_debt_ratio`: a higher rate raises the face value sold in proportion to `1 + i_t`;
  `one_percent_price_fall`, `one_percent_printed_fails` (a 1% lower bond price requires
  `1/99`, not 1%, more face value; survey E7).
* `twoStep`, `twoStep_eq_pegP`, `twoStep_debt_eq_pegB`, `twoStep_equilibrium`: the two-step
  process (central bank sets `i_t`, Treasury applies its rule, the price level satisfies the
  valuation equation) reproduces exactly the interest-rate-target equilibrium, so the central
  bank and Treasury together generate the flat supply curve.
-/

namespace Cochrane.IntertemporalModel.FlatSupply

open FiscalMonetary

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.28), p. 48: the flow condition
`B_t/P_{t+1} = s_{t+1} + Q_{t+1} B_{t+1}/P_{t+1}` with `Q = 1/(1 + i)` holds in equilibrium (the
book's reference "(2.15)" should be (2.4)/(2.9), survey E9). -/
theorem eq_2_28 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω / P (t + 1) ω = s (t + 1) ω + (1 + i (t + 1) ω)⁻¹ * (B (t + 1) ω / P (t + 1) ω) := by
  have e := congrFun (eq_2_26 hPO hs hsa h t).1 ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.one_apply] at e
  rw [e, mul_comm]

/-- Cochrane (2023), eq. (2.28), p. 48, at the initial date:
`B_{−1}/P_0 = s_0 + Q_0 B_0/P_0`. -/
theorem eq_2_28_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) :
    Bm1 ω / P 0 ω = s 0 ω + (1 + i 0 ω)⁻¹ * (B 0 ω / P 0 ω) := by
  have e := congrFun (eq_2_26_zero hPO hs hsa h).1 ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.one_apply] at e
  rw [e, mul_comm]

/-- Cochrane (2023), eq. (2.28), p. 48, "how much nominal debt `B_t` the Treasury must sell":
for `Q_t ≠ 0` and `P_t ≠ 0`, (2.28) holds iff `B_t = (B_{t−1} − P_t s_t)/Q_t`. -/
theorem treasury_rule_iff {Bprev Pt st Qt Bt : ℝ} (hQ : Qt ≠ 0) (hP : Pt ≠ 0) :
    Bprev / Pt = st + Qt * Bt / Pt ↔ Bt = (Bprev - Pt * st) / Qt := by
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hQ]
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (2.28), p. 48: in equilibrium the debt sold follows the Treasury rule
`B_{t+1} = (B_t − P_{t+1} s_{t+1})(1 + i_{t+1})`. -/
theorem treasury_rule_of_equilibrium (hPO : 𝔼.PullOut) (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B (t + 1) ω = (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  have e := flow_nominal hPO hs hsa h t ω
  have hi : 1 + i (t + 1) ω ≠ 0 := by linarith [h.2.2.2.2.1 (t + 1) ω]
  rw [e]
  field_simp
  ring

/-- Cochrane (2023), eq. (2.28), p. 48, at the initial date:
`B_0 = (B_{−1} − P_0 s_0)(1 + i_0)`. -/
theorem treasury_rule_of_equilibrium_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) :
    B 0 ω = (Bm1 ω - P 0 ω * s 0 ω) * (1 + i 0 ω) := by
  have e := eq_2_28_zero hPO hs hsa h ω
  have hi : 1 + i 0 ω ≠ 0 := by linarith [h.2.2.2.2.1 0 ω]
  have hP := (h.2.1 0 ω).ne'
  field_simp at e
  linear_combination -e

/-- Cochrane (2023), p. 48, "to obtain the same revenue": under the Treasury rule the nominal
revenue `Q_t B_t = B_{t−1} − P_t s_t` does not depend on the bond price the central bank sets,
so supply is flat at any price. -/
theorem flat_supply_revenue {Bprev Pt st Qt : ℝ} (hQ : Qt ≠ 0) :
    Qt * ((Bprev - Pt * st) / Qt) = Bprev - Pt * st := by
  field_simp

/-- Cochrane (2023), §2.4.3, p. 31, and §2.9, p. 48: a horizontal supply curve meets the
unit-elastic demand for debt `Q_t B_t/P_t = PV^{ex}_t` at exactly one quantity, whatever the
bond price `Q_t > 0`. -/
theorem flat_supply_meets_demand {Pt Qt R : ℝ} (hP : Pt ≠ 0) (hQ : Qt ≠ 0) :
    ∃! Bt : ℝ, Qt * Bt / Pt = R := by
  refine ⟨R * Pt / Qt, by field_simp, fun y hy => ?_⟩
  field_simp at hy ⊢
  linarith

/-- Cochrane (2023), p. 48, "if the central bank raises interest rates ... the Treasury then
raises the face value of debt it sells": with the same maturing debt, price level and surplus,
the Treasury rule at gross rates `1 + i` and `1 + i'` gives `B'_t/B_t = (1 + i'_t)/(1 + i_t)`. -/
theorem treasury_debt_ratio {Bprev Pt st i0 i1 : ℝ}
    (hrev : Bprev - Pt * st ≠ 0) :
    ((Bprev - Pt * st) * (1 + i1)) / ((Bprev - Pt * st) * (1 + i0)) = (1 + i1) / (1 + i0) :=
  mul_div_mul_left _ _ hrev

/-- Cochrane (2023), p. 48 (survey E7): when the bond price falls by one percent,
`Q' = 0.99 Q`, the Treasury rule raises the face value by exactly `1/99`. -/
theorem one_percent_price_fall {Bprev Pt st Qt : ℝ} (hQ : Qt ≠ 0) (hrev : Bprev - Pt * st ≠ 0) :
    ((Bprev - Pt * st) / (99 / 100 * Qt)) / ((Bprev - Pt * st) / Qt) - 1 = 1 / 99 := by
  field_simp
  ring

/-- Cochrane (2023), p. 48 (survey E7): the printed "raises the face value ... by one percent"
is an approximation: the exact rise `1/99` differs from `1/100`. -/
theorem one_percent_printed_fails : (1 / 99 : ℝ) ≠ 1 / 100 := by norm_num

/-! ### The two-step process: central bank sets `i`, Treasury follows its rule -/

/-- Cochrane (2023), §2.9, p. 48: the nominal debt maturing at date `t` in the two-step process:
`D_0 = B_{−1}`; the price level is `P_t = D_t/PV_t` (valuation equation) and the Treasury sells
`D_{t+1} = (D_t − P_t s_t)(1 + i_t)` at the rate the central bank sets. -/
noncomputable def twoStep (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 =>
    (twoStep 𝔼 β Bm1 s i t - twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t * s t) * (1 + i t)

/-- Cochrane (2023), §2.9, p. 48: the two-step process produces the interest-rate-target price
level, `D_t/PV_t = pegP_t`. -/
theorem twoStep_eq_pegP (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) (t : ℕ) :
    twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t = pegP 𝔼 β Bm1 s i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pegP_succ]
    congr 1
    change (twoStep 𝔼 β Bm1 s i t - twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t * s t) * (1 + i t) =
      (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t
    rw [← ih]
    funext ω
    have e := congrFun (pv_eq_add_pvEx 𝔼 hs hsa t) ω
    simp only [Pi.add_apply] at e
    have := hpv t ω
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
    rw [show pvEx 𝔼 β s t ω = pv 𝔼 β s t ω - s t ω by linarith]
    field_simp

/-- Cochrane (2023), §2.9, p. 48: the debt the Treasury sells in the two-step process is the
debt sold on the flat supply curve, `D_{t+1} = pegB_t`. -/
theorem twoStep_debt_eq_pegB (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) (t : ℕ) :
    twoStep 𝔼 β Bm1 s i (t + 1) = pegB 𝔼 β Bm1 s i t := by
  have h1 := twoStep_eq_pegP (Bm1 := Bm1) (i := i) hs hsa hpv (t + 1)
  rw [pegP_succ] at h1
  funext ω
  have e := congrFun h1 ω
  simp only [Pi.div_apply] at e
  have := hpv (t + 1) ω
  exact (div_left_inj' this).mp e

/-- Cochrane (2023), §2.9, p. 48, "the central bank plus Treasury thus really do sell any
quantity of debt at the fixed interest rate": the two-step process is the (unique)
interest-rate-target equilibrium. -/
theorem twoStep_equilibrium (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    Equilibrium 𝔼 β Bm1 s (fun t => twoStep 𝔼 β Bm1 s i (t + 1))
      (fun t => twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t) i := by
  have hpv' : ∀ t ω, pv 𝔼 β s t ω ≠ 0 := fun t ω => (hpv t ω).ne'
  have e1 : (fun t => twoStep 𝔼 β Bm1 s i (t + 1)) = pegB 𝔼 β Bm1 s i :=
    funext (twoStep_debt_eq_pegB hs hsa hpv')
  have e2 : (fun t => twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t) = pegP 𝔼 β Bm1 s i :=
    funext (twoStep_eq_pegP hs hsa hpv')
  rw [e1, e2]
  exact peg_equilibrium hPO hBm1 hB hia hi hpv hpvEx

end Cochrane.IntertemporalModel.FlatSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The fiscal theory of monetary policy: the linear model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5 "The fiscal theory of
monetary policy" and §2.6 "Interest-rate rules", pp. 34–42.

## Main results

* Innovations `ΔE_{t+1} = E_{t+1} − E_t` are `ExpectationTools.innov` (shared with
  `FiscalMonetary`): linear, zero on known variables, unforecastable, pull-out of known factors.
* (2.16) as an exact derivative: `fisher_log_form` (the exact Fisher equation
  `1/(1 + i_t) = β E_t(P_t/P_{t+1})` in logs), `fisher_deriv` (along any bounded direction of
  inflation the exact map has derivative `E_t π_{t+1}` at the steady state `log(1 + i) = r`),
  `fisher_pf_exact` (exact under perfect foresight).
* (2.17) exactly: `unexpected_inflation_exact` (`V_t ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} PV_{t+1}`
  with `V_t = B_t/P_t`), `innov_forwardSeries` (the PV news is `∑ βʲ ΔE_{t+1} s_{t+1+j}`, a
  genuine series), `pvNews_isShock`; the linear (2.17) as the first derivative of the exact one,
  `linear_217`; (2.18) exactly, `debt_218`.
* (2.19): `pegModel_iff`, `peg_existsUnique` — for every interest-rate path and every fiscal
  shock the model has exactly one solution given `π_0`, `π_{t+1} = i_t − ε_{Σs,t+1}`; it is
  bounded when the inputs are (`pegSol_bounded`).
* Figure 2.1 and p. 36: `irf_peg_impact`, `irf_peg_later`, `fig21_rate`, `fig21_fiscal`;
  announcements: `expected_inflation_ahead`, `announcement_invariant`,
  `no_announcement_effect`; fiscal news timing: `innov_of_news`, `pvNews_of_news`,
  `fig21_expected_fiscal` (inflation jumps when the fiscal news arrives, not when surpluses
  change); p. 37 `long_run_fisher`.
* §2.5.1: `pTarget_price` (`p_t = E_t p*_{t+1} − i_t`), `pTarget_rate_lowers_price`,
  `pTarget_fiscal_contraction`, `loggerhead`; survey error E6: `innov_pi_eq_innov_p` and
  `printed_E6_false`.
* p. 39 (passive fiscal policy): `passive_any_innovation` — any martingale difference is an
  equilibrium inflation innovation once fiscal policy accommodates.
* §2.6, (2.20)–(2.25): `ruleModel_iff`, `eq224_iff`, `rule_existsUnique` (**for every `θ`**: the
  FTPL needs no Taylor principle), `rule_eq_peg` (feeding the equilibrium rate into (2.19)),
  `ruleSol_bounded` (`|θ| < 1`), `ruleSol_unbounded` (`|θ| > 1`, survey item E30).
* Figure 2.2: the impulse responses as innovations, `irf_rule` (`ΔE_{t+1}π_{t+1+j} =
  −θʲ ε_{Σs,t+1} + c_j ε_{i,t+1}` with `c_j = (θʲ − ηʲ)/(θ − η)`), `irf_rule_rate`,
  `conv_eq`, `fig22_monetary`, `fig22_fiscal`; the hump `hump_step`, `hump_up`, `hump_down`,
  `hump_exists` (unimodal for every `0 < η < θ < 1`), `fig22_peak` (for `θ = .8`, `η = .7` the
  peak is `π_5 = 1.695`); p. 41 `fiscal_sets_impact`,
  `one_time_price_jump`, `price_level_returns`.

Expectations: an arbitrary `ExpectationSystem`; `PullOut` is a hypothesis where used. Inflation
`π_t`, rates `i_t` and shocks are random variables (`Ω → ℝ`) at each date.
-/

namespace Cochrane.IntertemporalModel.LinearFTMP

open Filter Topology Asymptotics ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.16): the Fisher equation as an exact derivative -/

/-- Cochrane (2023), eq. (2.16), p. 35 (exact form, from (2.3)): `1/(1 + i_t) = β E_t(P_t/P_{t+1})`
with `β = 1/R`. -/
def FisherExact (β : ℝ) (i P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 / (1 + i t ω) = β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω

/-- Cochrane (2023), eq. (2.16), p. 35: with positive prices, `1 + i_t > 0` and a positive
expectation, the exact Fisher equation is `log(1 + i_t) = r − log E_t[exp(−π_{t+1})]` with
`r = log R = −log β` and `π_{t+1} = log(P_{t+1}/P_t)`. -/
theorem fisher_log_form {β : ℝ} (hβ : 0 < β) {i P : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) :
    FisherExact 𝔼 β i P t ↔ ∀ ω, Real.log (1 + i t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have hX : (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) =
      fun ω' => P t ω' / P (t + 1) ω' := by
    funext ω'
    have h1 := hP t ω'
    have h2 := hP (t + 1) ω'
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [hX]
  refine forall_congr' fun ω => ?_
  have hE' := hE ω
  have hi' := hi ω
  have hlog : -Real.log β - Real.log (𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) =
      Real.log ((β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)⁻¹) := by
    rw [Real.log_inv, Real.log_mul hβ.ne' hE'.ne']
    ring
  rw [hlog]
  constructor
  · intro h
    rw [← h, one_div, inv_inv]
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr hi')
      (Set.mem_Ioi.mpr (inv_pos.mpr (mul_pos hβ hE'))) h
    rw [h', one_div, inv_inv]

/-- Cochrane (2023), eq. (2.16), p. 35 (exact under perfect foresight): with perfect foresight
the exact Fisher equation is `log(1 + i_t) = −log β + log(P_{t+1}/P_t)`, i.e. `i_t = r + π_{t+1}`
exactly in logs. -/
theorem fisher_pf_exact {β : ℝ} (hβ : 0 < β) {i P : ℕ → Unit → ℝ} {t : ℕ}
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω) :
    FisherExact perfectForesight β i P t ↔
      ∀ ω, Real.log (1 + i t ω) = -Real.log β + Real.log (P (t + 1) ω / P t ω) := by
  rw [fisher_log_form perfectForesight hβ hP hi (fun ω => div_pos (hP t ω) (hP (t + 1) ω))]
  refine forall_congr' fun ω => ?_
  change _ = _ - Real.log (Real.exp _) ↔ _
  rw [Real.log_exp]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (2.16), p. 35 (derivative of an expectation; restated from the Woodford
Chapter 2 project, `LogLinear.hasDerivAt_E_exp`): for a bounded random variable `X`,
`ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0`. -/
theorem hasDerivAt_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω) (𝔼.E t X ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hK : 0 ≤ |K| := abs_nonneg K
  have hbig : (fun h : ℝ => 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
      𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω) =O[𝓝 0] fun h => h ^ 2 := by
    refine IsBigO.of_bound (|K| ^ 2) ?_
    have hball : Metric.ball (0 : ℝ) (1 / (|K| + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
      intro ω'
      have hx : |h * X ω'| ≤ 1 := by
        rw [abs_mul]
        have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
        have h2 : |h| * (|K| + 1) ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hh
          exact hh.le
        nlinarith [abs_nonneg h, abs_nonneg (X ω')]
      refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
      rw [mul_pow, mul_comm (|K| ^ 2)]
      have : X ω' ^ 2 ≤ |K| ^ 2 := by
        rw [← sq_abs (X ω')]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
    have heq : 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
        𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω =
        𝔼.E t (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') ω := by
      have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
          (fun ω' => Real.exp (h * X ω')) - (fun _ => (1 : ℝ)) - h • X := by
        funext ω'
        simp
      rw [hfun, map_sub, map_sub, map_smul, 𝔼.const]
      simp [𝔼.const]
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact 𝔼.abs_E_le hrem t ω
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

/-- Cochrane (2023), eq. (2.16), p. 35, `i_t ≈ r + E_t π_{t+1}` as an exact derivative: along a
bounded direction `π̂` of inflation (`π_{t+1} = ε π̂`, so `P_t/P_{t+1} = exp(−ε π̂)`), the right
side of `fisher_log_form`, `ε ↦ −log β − log E_t[exp(−ε π̂)]`, has derivative `E_t π̂` at the
steady state `ε = 0`. -/
theorem fisher_deriv {K : ℝ} {πh : Ω → ℝ} (hb : ∀ ω, |πh ω| ≤ K) (β : ℝ) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (ε * -πh ω')) ω))
      (𝔼.E t πh ω) 0 := by
  have hX : ∀ ω', |(fun ω'' => -πh ω'') ω'| ≤ K := fun ω' => by
    simpa only [abs_neg] using hb ω'
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * -πh ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h := (hasDerivAt_E_exp 𝔼 hX t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at h
  have hneg : 𝔼.E t (fun ω'' => -πh ω'') ω = -𝔼.E t πh ω := by
    change 𝔼.E t (-πh) ω = _
    rw [map_neg, Pi.neg_apply]
  rw [hneg] at h
  have := h.const_sub (-Real.log β)
  simpa using this

/-- Cochrane (2023), eq. (2.16), p. 35: at the steady state `ε = 0` the exact Fisher map equals
`r = log R = −log β` ("when we think of variables as deviations from steady state, we drop
`r`"). -/
theorem fisher_deriv_value (πh : Ω → ℝ) (β : ℝ) (t : ℕ) (ω : Ω) :
    -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (0 * -πh ω')) ω) = -Real.log β := by
  simp only [zero_mul, Real.exp_zero]
  rw [𝔼.const, Real.log_one, sub_zero]

/-! ### (2.17)–(2.18): fiscal news and unexpected inflation, exactly -/

/-- Cochrane (2023), eq. (2.17), p. 35, exact form (eq. (2.13) at `t + 1`): if the valuation
equation `B_t/P_{t+1} = PV_{t+1}` holds and `V_t = B_t/P_t` is known at `t`, then
`V_t ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} PV_{t+1}`. -/
theorem unexpected_inflation_exact (hPO : 𝔼.PullOut) {B P PV : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ ω, P t ω ≠ 0)
    (hV : 𝔼.E t (fun ω => B t ω / P t ω) = fun ω => B t ω / P t ω)
    (hval : (fun ω => B t ω / P (t + 1) ω) = PV (t + 1)) :
    (fun ω => B t ω / P t ω) * innov 𝔼 t (fun ω => P t ω / P (t + 1) ω) =
      innov 𝔼 t (PV (t + 1)) := by
  rw [← innov_mul_known 𝔼 hPO hV, ← hval]
  congr 1
  funext ω
  simp only [Pi.mul_apply]
  rw [div_mul_div_comm, mul_comm (P t ω), mul_div_mul_right _ _ (hP ω)]

/-- Cochrane (2023), eq. (2.17), p. 35: the shock to the present value of (scaled) surpluses,
`ε_{Σs,t+1} = ΔE_{t+1} ∑_{j ≥ 0} βʲ s̃_{t+1+j} = ∑_{j ≥ 0} βʲ ΔE_{t+1} s̃_{t+1+j}`. -/
noncomputable def pvNews (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω

/-- Cochrane (2023), eqs. (2.17)–(2.18), p. 35: `E_t PV_{t+1} = ∑_{k ≥ 0} βᵏ E_t s_{t+1+k}`, with
`PV_{t+1} = E_{t+1} ∑ βᵏ s_{t+1+k}` the forward series (bounded surpluses, `0 ≤ β < 1`). -/
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
`ΔE_{t+1} PV_{t+1} = ∑_{k ≥ 0} βᵏ ΔE_{t+1} s_{t+1+k}` (bounded surpluses, `0 ≤ β < 1`). -/
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

/-- Cochrane (2023), p. 40 (terminology: a "shock" only moves unexpectedly): `ε_{t+1}` is known
at `t + 1` and `E_t ε_{t+1} = 0`. -/
def IsShock (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal news `ε_{Σs,t+1}` is a shock in the sense of
p. 40 (bounded surpluses, `0 ≤ β < 1`). -/
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

/-- Cochrane (2023), eq. (2.18), p. 35 (exact): from the Fisher equation and the valuation
equation at `t + 1`, `(B_t/P_t)/(1 + i_t) = (B_t/P_t) β E_t(P_t/P_{t+1}) = E_t ∑_{j ≥ 1} βʲ s_{t+j}`
(bounded surpluses, `0 ≤ β < 1`; `B_t/P_t` known at `t`). -/
theorem debt_218 (hPO : 𝔼.PullOut) {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {i B P s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ} (hP : ∀ ω, P t ω ≠ 0) (hfis : FisherExact 𝔼 β i P t)
    (hV : 𝔼.E t (fun ω => B t ω / P t ω) = fun ω => B t ω / P t ω)
    (hval : (fun ω => B t ω / P (t + 1) ω) = 𝔼.forwardSeries β s (t + 1)) (ω : Ω) :
    B t ω / P t ω * (1 / (1 + i t ω)) = ∑' k, β ^ (k + 1) * 𝔼.E t (s (t + 1 + k)) ω := by
  rw [hfis ω]
  have hpull := congrFun (hPO t _ (fun ω' => P t ω' / P (t + 1) ω') hV) ω
  have hprod : ((fun ω => B t ω / P t ω) * fun ω' => P t ω' / P (t + 1) ω') =
      fun ω => B t ω / P (t + 1) ω := by
    funext ω'
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm, mul_comm (P t ω'), mul_div_mul_right _ _ (hP ω')]
  rw [hprod, hval, Pi.mul_apply] at hpull
  calc B t ω / P t ω * (β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)
      = β * (B t ω / P t ω * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) := by ring
    _ = β * ∑' k, β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
        rw [← hpull, E_forwardSeries_succ 𝔼 h0 h1 hs t ω]
    _ = _ := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        ring

/-- Cochrane (2023), eq. (2.17), p. 35, the LINEAR (2.17) as the first derivative of the exact
(2.17): consider a family of economies indexed by `ε` with `π_{t+1} = ε π̂` (so
`P_t/P_{t+1} = exp(−ε π̂)`), PV news `ε V ΔE_{t+1} S̃` (surpluses scaled by steady-state debt
`V ≠ 0`, `s̃ = s/V`), and value of debt `V_t(ε)` differentiable with `V_t(0) = V`. If the exact
(2.17) holds along the family, then `ΔE_{t+1} π̂ = −ΔE_{t+1} S̃`. -/
theorem linear_217 {K V v' : ℝ} {πh S : Ω → ℝ} (hb : ∀ ω, |πh ω| ≤ K) (hV : V ≠ 0)
    {Vt : ℝ → ℝ} (hVt : HasDerivAt Vt v' 0) (hV0 : Vt 0 = V) (t : ℕ) (ω : Ω)
    (hfam : ∀ ε, Vt ε * innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω =
      ε * V * innov 𝔼 t S ω) :
    innov 𝔼 t πh ω = -innov 𝔼 t S ω := by
  have hX : ∀ ω', |(fun ω'' => -πh ω'') ω'| ≤ K := fun ω' => by
    simpa only [abs_neg] using hb ω'
  have hneg : ∀ n, 𝔼.E n (fun ω'' => -πh ω'') ω = -𝔼.E n πh ω := fun n => by
    change 𝔼.E n (-πh) ω = _
    rw [map_neg, Pi.neg_apply]
  have hg : HasDerivAt (fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω)
      (-innov 𝔼 t πh ω) 0 := by
    have h := HasDerivAt.sub (hasDerivAt_E_exp 𝔼 hX (t + 1) ω) (hasDerivAt_E_exp 𝔼 hX t ω)
    rw [hneg, hneg] at h
    have e : (fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω) =
        (fun ε => 𝔼.E (t + 1) (fun ω' => Real.exp (ε * -πh ω')) ω) -
          fun ε => 𝔼.E t (fun ω' => Real.exp (ε * -πh ω')) ω := by
      funext ε
      rfl
    rw [e]
    convert h using 1
    unfold innov
    rw [Pi.sub_apply]
    ring
  have hg0 : innov 𝔼 t (fun ω' => Real.exp (0 * -πh ω')) ω = 0 := by
    simp only [zero_mul, Real.exp_zero]
    rw [innov_const, Pi.zero_apply]
  have hL := hVt.mul hg
  rw [hg0, hV0, mul_zero, zero_add] at hL
  have hR : HasDerivAt (fun ε : ℝ => ε * V * innov 𝔼 t S ω) (V * innov 𝔼 t S ω) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const V).mul_const (innov 𝔼 t S ω)
    simpa using this
  have hfun : (Vt * fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω) =
      fun ε => ε * V * innov 𝔼 t S ω := funext hfam
  rw [hfun] at hL
  have h := hL.unique hR
  have h2 : V * (innov 𝔼 t πh ω + innov 𝔼 t S ω) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hV
  · linarith

/-! ### (2.19): the interest-rate peg -/

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35 (the linear model, variables as deviations from
steady state): `i_t = E_t π_{t+1}` and `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date. -/
def PegModel (i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: for adapted inflation, an adapted rate path and a fiscal
shock, the model (2.16)–(2.17) holds iff `π_{t+1} = i_t − ε_{Σs,t+1}` at every date. -/
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

/-- Cochrane (2023), eq. (2.19), p. 36: the solution `π_0` given, `π_{t+1} = i_t − ε_{Σs,t+1}`. -/
def pegSol (i ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => i t - ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: the solution is adapted. -/
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
(2.16)–(2.17) has exactly one adapted solution. No boundedness is imposed. -/
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
bounded `π_0`, rates and shocks the solution (2.19) is bounded. -/
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

/-! ### Figure 2.1: impulse responses as innovations -/

/-- Cochrane (2023), p. 40 (a shock "only moves unexpectedly"): a later shock has no innovation
at an earlier date, `ΔE_{t+1} ε_{t+2+j} = 0`. -/
theorem innov_shock_later {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t j : ℕ) :
    innov 𝔼 t (ε (t + 2 + j)) = 0 := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e]
  unfold innov
  rw [← 𝔼.tower (show t + 1 ≤ t + 1 + j by omega), hε.2, map_zero,
    ← 𝔼.tower (show t ≤ t + 1 + j by omega), hε.2, map_zero, sub_zero]

/-- Cochrane (2023), Figure 2.1 and p. 36 ("there is no unexpected time-`t` inflation without a
fiscal shock"): on impact, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever the rate news. -/
theorem irf_peg_impact {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  rw [h t, innov_sub, innov_of_known 𝔼 (hi t)]
  unfold innov
  rw [hε.1 t, hε.2 t]
  abel

/-- Cochrane (2023), Figure 2.1 and p. 36 ("inflation moves up one period later"): after impact
the inflation response is the rate response one period earlier,
`ΔE_{t+1} π_{t+2+j} = ΔE_{t+1} i_{t+1+j}`. -/
theorem irf_peg_later {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 2 + j)) = innov 𝔼 t (i (t + 1 + j)) := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e, h, innov_sub, ← e, innov_shock_later 𝔼 hε, sub_zero]

/-- Cochrane (2023), Figure 2.1, top panel: a permanent interest-rate shock at `t + 1` (news
`ΔE_{t+1} i_{t+1+j} = 1` for all `j`) with no fiscal shock gives no inflation on impact and
inflation `1` from `t + 2` on. -/
theorem fig21_rate {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {t : ℕ} {ω : Ω} (hε0 : ε (t + 1) ω = 0)
    (hnews : ∀ j, innov 𝔼 t (i (t + 1 + j)) ω = 1) :
    innov 𝔼 t (π (t + 1)) ω = 0 ∧ ∀ j, innov 𝔼 t (π (t + 2 + j)) ω = 1 := by
  refine ⟨?_, fun j => ?_⟩
  · rw [irf_peg_impact 𝔼 hi hε h t, Pi.neg_apply, hε0, neg_zero]
  · rw [irf_peg_later 𝔼 hε h t j, hnews j]

/-- Cochrane (2023), Figure 2.1, bottom panel: a fiscal shock `ε_{Σs,t+1} = −1` with no interest
rate news gives a one-period inflation `1` on impact and nothing afterwards. -/
theorem fig21_fiscal {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {t : ℕ} {ω : Ω} (hε1 : ε (t + 1) ω = -1)
    (hnews : ∀ j, innov 𝔼 t (i (t + 1 + j)) ω = 0) :
    innov 𝔼 t (π (t + 1)) ω = 1 ∧ ∀ j, innov 𝔼 t (π (t + 2 + j)) ω = 0 := by
  refine ⟨?_, fun j => ?_⟩
  · rw [irf_peg_impact 𝔼 hi hε h t, Pi.neg_apply, hε1, neg_neg]
  · rw [irf_peg_later 𝔼 hε h t j, hnews j]

/-! ### Announcements (p. 36) -/

/-- Cochrane (2023), p. 36 ("If `E_{t−k} i_t` rises, then `E_{t−k} π_{t+1}` rises"): for every
`s ≤ t`, `E_s π_{t+1} = E_s i_t`. -/
theorem expected_inflation_ahead {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (π (t + 1)) = 𝔼.E s (i t) := by
  rw [h t, map_sub, ← 𝔼.tower hst (ε (t + 1)), hε.2 t, map_zero, sub_zero]

/-- Cochrane (2023), p. 36 ("The response is the same if the interest-rate movement is announced
ahead of time"): two information structures `𝔼₁`, `𝔼₂` (e.g. the rate path announced early, or
revealed date by date) with the same realised adapted rate path, no fiscal shocks and the same
`π_0` give the same inflation path. -/
theorem announcement_invariant (𝔼₁ 𝔼₂ : ExpectationSystem Ω) {i π₁ π₂ : ℕ → Ω → ℝ}
    (hi₁ : 𝔼₁.Adapted i) (hi₂ : 𝔼₂.Adapted i) (hπ₁ : 𝔼₁.Adapted π₁) (hπ₂ : 𝔼₂.Adapted π₂)
    (h₁ : PegModel 𝔼₁ i 0 π₁) (h₂ : PegModel 𝔼₂ i 0 π₂) (h0 : π₁ 0 = π₂ 0) : π₁ = π₂ := by
  have hs₁ : IsShock 𝔼₁ 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  have hs₂ : IsShock 𝔼₂ 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  have e₁ := (pegModel_iff 𝔼₁ hπ₁ hi₁ hs₁).mp h₁
  have e₂ := (pegModel_iff 𝔼₂ hπ₂ hi₂ hs₂).mp h₂
  funext t
  cases t with
  | zero => exact h0
  | succ t => rw [e₁ t, e₂ t]

/-- Cochrane (2023), p. 36 ("in many models announcements of future policy can affect the
economy on the date of the announcement. Not in this case"): two rate paths that agree before
date `T` give the same inflation up to and including date `T`. -/
theorem no_announcement_effect {i i' ε π π' : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (h' : ∀ t, π' (t + 1) = i' t - ε (t + 1))
    (h0 : π 0 = π' 0) {T : ℕ} (hii : ∀ s < T, i s = i' s) : ∀ s ≤ T, π s = π' s := by
  intro s hs
  cases s with
  | zero => exact h0
  | succ s => rw [h s, h' s, hii s (by omega)]

/-- Cochrane (2023), p. 37 ("in the long run higher nominal interest rates must come with
higher inflation"): a constant rate `c` and no fiscal shocks give `π_{t+1} = c`. -/
theorem long_run_fisher {i ε π : ℕ → Ω → ℝ} {c : ℝ} (h : ∀ t, π (t + 1) = i t - ε (t + 1))
    (hc : ∀ t, i t = fun _ => c) (hε : ε = 0) (t : ℕ) : π (t + 1) = fun _ => c := by
  rw [h t, hc t, hε, Pi.zero_apply, sub_zero]

/-! ### Fiscal news: inflation when the news arrives (Figure 2.1, "expected fiscal shock") -/

/-- Cochrane (2023), Figure 2.1 and pp. 36–37: a random variable revealed at date `a + 1`
(`E_{a+1} x = x`, `E_a x = 0`) has innovation `x` at `a + 1` and none at any other date. -/
theorem innov_of_news {a : ℕ} {x : Ω → ℝ} (hxa : 𝔼.E (a + 1) x = x) (hx0 : 𝔼.E a x = 0)
    (t : ℕ) : innov 𝔼 t x = if t = a then x else 0 := by
  unfold innov
  rcases lt_trichotomy t a with hlt | heq | hgt
  · simp only [hlt.ne, ↓reduceIte]
    rw [← 𝔼.tower (show t + 1 ≤ a by omega), hx0, map_zero,
      ← 𝔼.tower hlt.le, hx0, map_zero, sub_zero]
  · subst heq
    simp only [↓reduceIte]
    rw [hxa, hx0, sub_zero]
  · simp only [hgt.ne', ↓reduceIte]
    rw [ForwardSolution.E_of_known 𝔼 (show a + 1 ≤ t + 1 by omega) hxa,
      ForwardSolution.E_of_known 𝔼 (show a + 1 ≤ t by omega) hxa, sub_self]

/-- Cochrane (2023), Figure 2.1 and pp. 36–37 ("The fiscal shock is a shock to the present value
of surpluses, so when surpluses actually change does not matter"): with surpluses
`s_k = c_k + D_k x`, `x` revealed at `a + 1`, the PV news is
`(∑ₖ βᵏ D_{a+1+k}) x` at date `a + 1` and zero at every other date, whatever the profile `D` of
the surplus change. -/
theorem pvNews_of_news {β : ℝ} {c D : ℕ → ℝ} {a : ℕ} {x : Ω → ℝ} (hxa : 𝔼.E (a + 1) x = x)
    (hx0 : 𝔼.E a x = 0) (t : ℕ) :
    pvNews 𝔼 β (fun k ω => c k + D k * x ω) t =
      fun ω => if t = a then (∑' k, β ^ k * D (a + 1 + k)) * x ω else 0 := by
  funext ω
  have hk : ∀ k, innov 𝔼 t (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') ω =
      D (t + 1 + k) * (if t = a then x ω else 0) := by
    intro k
    have e : (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') =
        (fun _ => c (t + 1 + k)) + D (t + 1 + k) • x := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, innov_add, innov_const, innov_smul, innov_of_news 𝔼 hxa hx0 t, zero_add]
    split_ifs <;> simp
  change ∑' k, β ^ k * innov 𝔼 t (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') ω = _
  simp_rw [hk]
  split_ifs with ht
  · subst ht
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  · simp

/-- Cochrane (2023), Figure 2.1, "expected fiscal shock" (pp. 36–37: "Inflation happens when the
shock is announced, not when surpluses appear"): with no rate response (`i = 0`) and fiscal
shocks equal to the PV news of surpluses `s_k = c_k + D_k x` announced at `a + 1`, inflation is
`−(∑ₖ βᵏ D_{a+1+k}) x` at the announcement date `a + 1` and zero at every other date, however
late the surpluses actually change. -/
theorem fig21_expected_fiscal {β : ℝ} {c D : ℕ → ℝ} {a : ℕ} {x : Ω → ℝ}
    (hxa : 𝔼.E (a + 1) x = x) (hx0 : 𝔼.E a x = 0) {π : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) = 0 - pvNews 𝔼 β (fun k ω => c k + D k * x ω) t) (t : ℕ) :
    π (t + 1) = fun ω => if t = a then -((∑' k, β ^ k * D (a + 1 + k)) * x ω) else 0 := by
  rw [h t, pvNews_of_news 𝔼 hxa hx0 t]
  funext ω
  split_ifs <;> simp

/-! ### §2.5.1: a fiscal price-level target -/

/-- Cochrane (2023), §2.5.1, p. 38: if fiscal policy attains the target `p_{t+1} = p*_{t+1}`
and the Fisher equation `i_t = E_t(p_{t+1} − p_t)` holds (log price level `p`, known at `t`),
then `p_t = E_t p*_{t+1} − i_t`. -/
theorem pTarget_price {i p pstar : ℕ → Ω → ℝ} {t : ℕ} (hp : 𝔼.E t (p t) = p t)
    (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (htarget : p (t + 1) = pstar (t + 1)) :
    p t = 𝔼.E t (pstar (t + 1)) - i t := by
  rw [hfis, map_sub, hp, htarget]
  abel

/-- Cochrane (2023), §2.5.1, p. 38 ("A higher interest rate now immediately lowers inflation"):
with the same targets, a higher rate `i'_t > i_t` gives a lower price level `p'_t < p_t`, hence
lower inflation `p'_t − p_{t−1} < p_t − p_{t−1}`. -/
theorem pTarget_rate_lowers_price {i i' p p' pstar : ℕ → Ω → ℝ} {t : ℕ}
    (hp : 𝔼.E t (p t) = p t) (hp' : 𝔼.E t (p' t) = p' t)
    (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (hfis' : i' t = 𝔼.E t (p' (t + 1) - p' t))
    (htarget : p (t + 1) = pstar (t + 1)) (htarget' : p' (t + 1) = pstar (t + 1)) {ω : Ω}
    (hlt : i t ω < i' t ω) (q : ℝ) : p' t ω < p t ω ∧ p' t ω - q < p t ω - q := by
  have h1 := congrFun (pTarget_price 𝔼 hp hfis htarget) ω
  have h2 := congrFun (pTarget_price 𝔼 hp' hfis' htarget') ω
  simp only [Pi.sub_apply] at h1 h2
  constructor <;> linarith

/-- Cochrane (2023), §2.5.1, p. 38 ("To defend the price level targets ... the fiscal authority
will be induced to raise future surpluses"): with targets `p*_{t+2}` known at `t`, the linear
valuation equation `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` forces the fiscal shock to equal the rate
news, `ε_{Σs,t+1} = ΔE_{t+1} i_{t+1}`. -/
theorem pTarget_fiscal_contraction {i p pstar ε : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p)
    (hfis : ∀ t, i t = 𝔼.E t (p (t + 1) - p t)) (htarget : ∀ t, p (t + 1) = pstar (t + 1))
    {t : ℕ} (hstar : 𝔼.E t (pstar (t + 2)) = pstar (t + 2))
    (h221 : innov 𝔼 t (p (t + 1) - p t) = -ε (t + 1)) : ε (t + 1) = innov 𝔼 t (i (t + 1)) := by
  have hp1 := pTarget_price 𝔼 (hp (t + 1)) (hfis (t + 1)) (htarget (t + 1))
  have hk : 𝔼.E (t + 1) (pstar (t + 1 + 1)) = pstar (t + 2) :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hstar
  rw [hk] at hp1
  rw [innov_sub, innov_of_known 𝔼 (hp t), sub_zero, hp1, innov_sub,
    innov_of_known 𝔼 hstar, zero_sub] at h221
  exact (neg_inj.mp h221).symm

/-- Cochrane (2023), §2.5.1, p. 38 ("then we are at a loggerhead"): if fiscal policy also sets
`p_t = p*_t` (targets known at `t`), the Fisher equation leaves monetary policy no freedom:
`i_t = p*_{t+1} − p*_t`. -/
theorem loggerhead {i p pstar : ℕ → Ω → ℝ} {t : ℕ} (hstar : 𝔼.E t (pstar (t + 1)) = pstar (t + 1))
    (hp : 𝔼.E t (p t) = p t) (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (h1 : p t = pstar t)
    (h2 : p (t + 1) = pstar (t + 1)) : i t = pstar (t + 1) - pstar t := by
  rw [pTarget_price 𝔼 hp hfis h2, hstar] at h1
  rw [← h1]
  abel

/-- Cochrane (2023), p. 38 (survey error E6, corrected): `ΔE_{t+1} π_{t+1} = ΔE_{t+1} p_{t+1}`
(`p_t` is known at `t`, so it has no innovation). -/
theorem innov_pi_eq_innov_p {p : ℕ → Ω → ℝ} {t : ℕ} (hp : 𝔼.E t (p t) = p t) :
    innov 𝔼 t (p (t + 1) - p t) = innov 𝔼 t (p (t + 1)) := by
  rw [innov_sub, innov_of_known 𝔼 hp, sub_zero]

/-- Cochrane (2023), p. 38, survey error E6: the printed `ΔE_t π_t = ΔE_t p_t − p_{t−1}` is false
(perfect foresight with `p ≡ 1`: the left side is `0`, the right side `−1`). -/
theorem printed_E6_false : ∃ p : ℕ → Unit → ℝ, perfectForesight.Adapted p ∧
    innov perfectForesight 0 (p 1 - p 0) ≠ innov perfectForesight 0 (p 1) - p 0 := by
  refine ⟨fun _ _ => 1, fun _ => rfl, fun h => ?_⟩
  have := congrFun h ()
  simp [innov, perfectForesight] at this

/-! ### p. 39: passive fiscal policy -/

/-- Cochrane (2023), p. 39: the passive fiscal policy of the new-Keynesian reading,
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` "in response to whatever inflation happens". -/
def passiveShock (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -innov 𝔼 t (π (t + 1))

/-- Cochrane (2023), p. 39: under passive fiscal policy the valuation equation holds for every
inflation path satisfying the Fisher equation. -/
theorem passive_valuation_holds {i π : ℕ → Ω → ℝ} (hfis : ∀ t, i t = 𝔼.E t (π (t + 1))) :
    PegModel 𝔼 i (passiveShock 𝔼 π) π := fun t => ⟨hfis t, by
      change _ = -(-innov 𝔼 t (π (t + 1)))
      rw [neg_neg]⟩

/-- Cochrane (2023), p. 39 ("The bank threatens hyperinflation for any but one value of
unexpected inflation"): with passive fiscal policy, EVERY shock `ν` is an equilibrium inflation
innovation: `π_{t+1} = i_t + ν_{t+1}` is adapted, satisfies the model with the passive fiscal
response, and has `ΔE_{t+1} π_{t+1} = ν_{t+1}`. -/
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

/-! ### §2.6: interest-rate rules, (2.20)–(2.25) -/

/-- Cochrane (2023), p. 40: a shock's innovation on arrival is the shock itself,
`ΔE_{t+1} ε_{t+1} = ε_{t+1}`. -/
theorem innov_shock {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t : ℕ) :
    innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  unfold innov
  rw [hε.1 t, hε.2 t, sub_zero]

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and the Taylor-type rule `i_t = θ π_t + u_t`. -/
def RuleModel (θ : ℝ) (i u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1) ∧ i t = θ • π t + u t

/-- Cochrane (2023), eq. (2.23), p. 40: the serially correlated disturbance
`u_t = η u_{t−1} + ε_{i,t}`. -/
def Disturbance (η : ℝ) (u εi : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + εi (t + 1)

/-- Cochrane (2023), eq. (2.24) with (2.21), p. 40: `E_t π_{t+1} = θ π_t + u_t` and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`. -/
def Eq224 (θ : ℝ) (u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eqs. (2.20)–(2.24), p. 40 ("Eliminating the interest rate"): the model
(2.20)–(2.22) holds iff the rate is given by the rule and inflation satisfies (2.24), (2.21). -/
theorem ruleModel_iff {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} :
    RuleModel 𝔼 θ i u ε π ↔ (∀ t, i t = θ • π t + u t) ∧ Eq224 𝔼 θ u ε π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2.2, fun t => ⟨(h t).1.symm.trans (h t).2.2, (h t).2.1⟩⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).1.symm, (h t).2, hi t⟩

/-- Cochrane (2023), eq. (2.25), p. 40: for adapted inflation and disturbance and a fiscal shock,
(2.24) with (2.21) holds iff `π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
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
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
def ruleSol (θ : ℝ) (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => θ • ruleSol θ u ε π0 t + u t - ε (t + 1)

/-- Cochrane (2023), eq. (2.25), p. 40: the solution is adapted. -/
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
given `π_0`, there is exactly one equilibrium `(π, i)` of (2.20)–(2.22) with `π` adapted. -/
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
equilibrium rate, and equals the peg solution (2.19) for that rate. -/
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
shocks, the equilibrium (2.25) is bounded. -/
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
linearisation of §2.5 is not justified along it; the equilibrium still exists and is unique. -/
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

/-! ### Figure 2.2: impulse responses as innovations -/

/-- Cochrane (2023), Figure 2.2, p. 41: the coefficients `c_0 = 0`, `c_{j+1} = θ c_j + ηʲ` of
the monetary-shock response, `c_j = ∑_{k<j} θ^{j−1−k} ηᵏ`. -/
def conv (θ η : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => θ * conv θ η j + η ^ j

/-- Cochrane (2023), Figure 2.2, p. 41: for `θ ≠ η`, `c_j = (θʲ − ηʲ)/(θ − η)`. -/
theorem conv_eq {θ η : ℝ} (h : θ ≠ η) (j : ℕ) : conv θ η j = (θ ^ j - η ^ j) / (θ - η) := by
  have hne : θ - η ≠ 0 := sub_ne_zero.mpr h
  induction j with
  | zero => simp [conv]
  | succ j ih =>
    rw [conv, ih]
    field_simp
    ring

/-- Cochrane (2023), eq. (2.23), p. 40: the response of the disturbance to a monetary shock,
`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{i,t+1}`. -/
theorem irf_disturbance {η : ℝ} {u εi : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi)
    (hd : Disturbance η u εi) (t j : ℕ) :
    innov 𝔼 t (u (t + 1 + j)) = η ^ j • εi (t + 1) := by
  induction j with
  | zero =>
    rw [add_zero, hd t, innov_add, innov_smul, innov_of_known 𝔼 (hu t), innov_shock 𝔼 hεi,
      smul_zero, zero_add, pow_zero, one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, hd, innov_add, innov_smul, ih,
      show t + 1 + j + 1 = t + 2 + j by omega, innov_shock_later 𝔼 hεi, add_zero, smul_smul,
      pow_succ, mul_comm η]

/-- Cochrane (2023), Figure 2.2 and eq. (2.25), pp. 40–41: impulse responses of inflation in the
rule model, `ΔE_{t+1} π_{t+1+j} = −θʲ ε_{Σs,t+1} + c_j ε_{i,t+1}`. -/
theorem irf_rule {θ η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) = (-θ ^ j) • ε (t + 1) + conv θ η j • εi (t + 1) := by
  induction j with
  | zero =>
    have hk : 𝔼.E t (θ • π t + u t) = θ • π t + u t := by rw [map_add, map_smul, hπ t, hu t]
    rw [add_zero, h t, innov_sub, innov_of_known 𝔼 hk, innov_shock 𝔼 hε, pow_zero, conv,
      zero_smul, add_zero, zero_sub, neg_one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, h, innov_sub, innov_add, innov_smul, ih,
      irf_disturbance 𝔼 hu hεi hd, show t + 1 + j + 1 = t + 2 + j by omega,
      innov_shock_later 𝔼 hε, sub_zero, conv, smul_add, smul_smul, smul_smul, add_smul,
      pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), Figure 2.2, p. 41: the interest-rate responses,
`ΔE_{t+1} i_{t+1+j} = −θ^{j+1} ε_{Σs,t+1} + c_{j+1} ε_{i,t+1}` (inflation follows the rate with
a one-period lag). -/
theorem irf_rule_rate {θ η : ℝ} {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) (t j : ℕ) :
    innov 𝔼 t (i (t + 1 + j)) = (-θ ^ (j + 1)) • ε (t + 1) + conv θ η (j + 1) • εi (t + 1) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  have hpeg := (rule_eq_peg 𝔼 hπ hu hε hm).1
  have hi : 𝔼.Adapted i := fun t => by rw [(hm t).2.2, map_add, map_smul, hπ t, hu t]
  have hp := (pegModel_iff 𝔼 hπ hi hε).mp hpeg
  rw [← irf_peg_later 𝔼 hε hp t j, show t + 2 + j = t + 1 + (j + 1) by omega,
    irf_rule 𝔼 hπ hu hεi hε hd h t (j + 1)]

/-- Cochrane (2023), Figure 2.2, top panel: a unit monetary shock `ε_{i,t+1} = 1` with no fiscal
shock: inflation responds `c_j = (θʲ − ηʲ)/(θ − η)` (`0` on impact: "`π_1` cannot jump"), the
rate `c_{j+1}`. -/
theorem fig22_monetary {θ η : ℝ} (hθη : θ ≠ η) {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) {t : ℕ} {ω : Ω} (h1 : εi (t + 1) ω = 1)
    (h0 : ε (t + 1) ω = 0) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = (θ ^ j - η ^ j) / (θ - η) ∧
      innov 𝔼 t (i (t + 1 + j)) ω = (θ ^ (j + 1) - η ^ (j + 1)) / (θ - η) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j, irf_rule_rate 𝔼 hπ hu hεi hε hd hm t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0, conv_eq hθη]
  constructor <;> ring

/-- Cochrane (2023), Figure 2.2, bottom panel: a unit fiscal shock `ε_{Σs,t+1} = −1` with no
monetary shock: inflation responds `θʲ` and the rate `θ^{j+1}` (`π_t = θ^{t−1}`, `i_t = θᵗ` with
the shock at date 1). -/
theorem fig22_fiscal {θ η : ℝ} {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) {t : ℕ} {ω : Ω} (h0 : εi (t + 1) ω = 0)
    (h1 : ε (t + 1) ω = -1) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = θ ^ j ∧ innov 𝔼 t (i (t + 1 + j)) ω = θ ^ (j + 1) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j, irf_rule_rate 𝔼 hπ hu hεi hε hd hm t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  constructor <;> ring

/-- Cochrane (2023), p. 41 ("fiscal policy alone sets the initial unexpected inflation of this
response function"): `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever `θ`, `η` and the monetary
shock. -/
theorem fiscal_sets_impact {θ η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  have := irf_rule 𝔼 hπ hu hεi hε hd h t 0
  rw [add_zero, pow_zero, conv, zero_smul, add_zero, neg_one_smul] at this
  exact this

/-- Cochrane (2023), p. 41 ("Monetary policy could turn the event into a one-time price level
shock, with no further inflation"): with `θ = 0` and no monetary shock, a fiscal shock
`ε_{Σs,t+1} = −1` raises inflation by `1` on impact and leaves later inflation unchanged. -/
theorem one_time_price_jump {η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = (0 : ℝ) • π t + u t - ε (t + 1)) {t : ℕ} {ω : Ω}
    (h0 : εi (t + 1) ω = 0) (h1 : ε (t + 1) ω = -1) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = if j = 0 then 1 else 0 := by
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  cases j with
  | zero => simp
  | succ j => simp

/-- Cochrane (2023), p. 41 ("Monetary policy could return the price level to its previous
value"): with `θ = 0`, `|η| < 1`, a fiscal shock `ε_{Σs,t+1} = −1` met by the monetary shock
`ε_{i,t+1} = −(1 − η)`, the inflation responses sum to zero: the price level returns. -/
theorem price_level_returns {η : ℝ} (hη : |η| < 1) {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = (0 : ℝ) • π t + u t - ε (t + 1)) {t : ℕ} {ω : Ω}
    (h0 : εi (t + 1) ω = -(1 - η)) (h1 : ε (t + 1) ω = -1) :
    HasSum (fun j => innov 𝔼 t (π (t + 1 + j)) ω) 0 := by
  have hx : ∀ j, innov 𝔼 t (π (t + 1 + j)) ω = -(0 : ℝ) ^ j * -1 + conv 0 η j * -(1 - η) := by
    intro j
    rw [irf_rule 𝔼 hπ hu hεi hε hd h t j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  have hc : ∀ j, conv 0 η (j + 1) = η ^ j := fun j => by simp [conv]
  have htail : HasSum (fun j => innov 𝔼 t (π (t + 1 + (j + 1))) ω) (-1) := by
    have hg := (hasSum_geometric_of_abs_lt_one hη).mul_left (-(1 - η))
    have h1η : 1 - η ≠ 0 := by
      have := (abs_lt.mp hη).2
      linarith
    have hv : -(1 - η) * (1 - η)⁻¹ = -1 := by
      rw [neg_mul, mul_inv_cancel₀ h1η]
    rw [hv] at hg
    convert hg using 1
    funext j
    rw [hx (j + 1), hc j]
    simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow]
    ring
  have hf0 : innov 𝔼 t (π (t + 1 + 0)) ω = 1 := by
    rw [hx 0]
    simp [conv]
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.sum_range_one, hf0, zero_sub]
  exact htail

/-! ### The hump (Figure 2.2, p. 40) -/

/-- Cochrane (2023), Figure 2.2, p. 40 ("a pretty hump-shaped inflation response"): for
`0 < η < θ < 1`, once the monetary response `c_j` stops rising it falls strictly ever after:
`c_{j+1} ≤ c_j → c_{j+2} < c_{j+1}`. -/
theorem hump_step {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) (j : ℕ)
    (h : conv θ η (j + 1) ≤ conv θ η j) : conv θ η (j + 2) < conv θ η (j + 1) := by
  have hne : θ ≠ η := hηθ.ne'
  have hd : 0 < θ - η := sub_pos.mpr hηθ
  rw [conv_eq hne, conv_eq hne, div_le_div_iff_of_pos_right hd] at h
  rw [conv_eq hne, conv_eq hne, div_lt_div_iff_of_pos_right hd]
  have hθ0 : 0 < θ := hη.trans hηθ
  have hpθ : 0 < θ ^ j := pow_pos hθ0 j
  have hpη : 0 < η ^ j := pow_pos hη j
  have h1 : (1 - η) * η ^ j ≤ (1 - θ) * θ ^ j := by
    rw [pow_succ, pow_succ] at h
    nlinarith
  have h2 : (1 - η) * η ^ j * η ≤ (1 - θ) * θ ^ j * η := mul_le_mul_of_nonneg_right h1 hη.le
  have h3 : (1 - θ) * θ ^ j * η < (1 - θ) * θ ^ j * θ :=
    mul_lt_mul_of_pos_left hηθ (mul_pos (by linarith) hpθ)
  have key : (1 - η) * η ^ j * η < (1 - θ) * θ ^ j * θ := h2.trans_lt h3
  have e : θ ^ (j + 1) - η ^ (j + 1) - (θ ^ (j + 2) - η ^ (j + 2)) =
      (1 - θ) * θ ^ j * θ - (1 - η) * η ^ j * η := by ring
  linarith

/-- Cochrane (2023), Figure 2.2, p. 40: before the peak the response rises,
`c_J < c_{J+1} → ∀ j ≤ J, c_j < c_{j+1}` (`0 < η < θ < 1`). -/
theorem hump_up {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) {J : ℕ}
    (h : conv θ η J < conv θ η (J + 1)) : ∀ j ≤ J, conv θ η j < conv θ η (j + 1) := by
  intro j hj
  induction J with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact h
  | succ J ih =>
    rcases Nat.lt_or_ge j (J + 1) with hlt | hge
    · refine ih ?_ (by omega)
      by_contra hc
      have := hump_step hη hηθ hθ J (not_lt.mp hc)
      linarith
    · obtain rfl : j = J + 1 := by omega
      exact h

/-- Cochrane (2023), Figure 2.2, p. 40: after the peak the response falls,
`c_{J+1} ≤ c_J → ∀ k, c_{J+2+k} < c_{J+1+k}` (`0 < η < θ < 1`). -/
theorem hump_down {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) {J : ℕ}
    (h : conv θ η (J + 1) ≤ conv θ η J) : ∀ k, conv θ η (J + 2 + k) < conv θ η (J + 1 + k) := by
  intro k
  induction k with
  | zero => exact hump_step hη hηθ hθ J h
  | succ k ih =>
    have := hump_step hη hηθ hθ (J + 1 + k) (by
      rw [show J + 1 + k + 1 = J + 2 + k by omega]
      exact ih.le)
    rw [show J + 2 + (k + 1) = J + 1 + k + 2 by omega,
      show J + 1 + (k + 1) = J + 1 + k + 1 by omega]
    exact this

/-- Cochrane (2023), Figure 2.2, p. 40 (the hump, in general): for `0 < η < θ < 1` the response
`c_j` is unimodal: strictly increasing up to some `J`, `c_{J+1} ≤ c_J`, and strictly decreasing
after `J`. -/
theorem hump_exists {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) :
    ∃ J, (∀ j < J, conv θ η j < conv θ η (j + 1)) ∧ conv θ η (J + 1) ≤ conv θ η J ∧
      ∀ j, J < j → conv θ η (j + 1) < conv θ η j := by
  have hne : θ ≠ η := hηθ.ne'
  have hθ0 : 0 < θ := hη.trans hηθ
  have hex : ∃ J, conv θ η (J + 1) ≤ conv θ η J := by
    by_contra hc
    push Not at hc
    have hmono : ∀ j, conv θ η 1 ≤ conv θ η (j + 1) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact ih.trans (hc (j + 1)).le
    have h1 : conv θ η 1 = 1 := by simp [conv]
    have hlim : Tendsto (fun j => conv θ η (j + 1)) atTop (𝓝 0) := by
      have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ).sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one hη.le (hηθ.trans hθ))).div_const (θ - η)
      rw [sub_zero, zero_div] at ht
      have ht' := ht.comp (tendsto_add_atTop_nat 1)
      refine ht'.congr fun j => ?_
      simp only [Function.comp_apply]
      rw [conv_eq hne]
    have := ge_of_tendsto' hlim (fun j => (h1 ▸ hmono j : (1 : ℝ) ≤ conv θ η (j + 1)))
    linarith
  classical
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex, fun j hj => ?_⟩
  · exact not_le.mp (Nat.find_min hex hj)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
    have := hump_down hη hηθ hθ (Nat.find_spec hex) k
    rw [show Nat.find hex + k + 1 + 1 = Nat.find hex + 2 + k by omega,
      show Nat.find hex + k + 1 = Nat.find hex + 1 + k by omega]
    exact this

/-- Cochrane (2023), Figure 2.2, p. 41 (`θ = 0.8`, `η = 0.7`): the inflation response rises up
to `c_4` (inflation at date 5 for a shock at date 1) and falls strictly afterwards; the peak is
`c_4 = 1.695`. -/
theorem fig22_peak :
    (∀ j < 4, conv (4 / 5) (7 / 10) j < conv (4 / 5) (7 / 10) (j + 1)) ∧
      (∀ j, 4 ≤ j → conv (4 / 5) (7 / 10) (j + 1) < conv (4 / 5) (7 / 10) j) ∧
      conv (4 / 5) (7 / 10) 4 = 339 / 200 := by
  have hη : (0 : ℝ) < 7 / 10 := by norm_num
  have hηθ : (7 / 10 : ℝ) < 4 / 5 := by norm_num
  have hθ : (4 / 5 : ℝ) < 1 := by norm_num
  have h34 : conv (4 / 5) (7 / 10) 3 < conv (4 / 5) (7 / 10) (3 + 1) := by
    norm_num [conv]
  have h54 : conv (4 / 5) (7 / 10) (4 + 1) ≤ conv (4 / 5) (7 / 10) 4 := by
    norm_num [conv]
  refine ⟨fun j hj => hump_up hη hηθ hθ h34 j (by omega), fun j hj => ?_, by norm_num [conv]⟩
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · have := h54
    rcases this.lt_or_eq with h | h
    · exact h
    · norm_num [conv] at h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have := hump_down hη hηθ hθ h54 k
    rw [show 4 + k + 1 + 1 = 4 + 2 + k by omega, show 4 + k + 1 = 4 + 1 + k by omega]
    exact this

end Cochrane.IntertemporalModel.LinearFTMP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links to the Woodford projects

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4 (p. 33), §2.5–2.6
(pp. 34–42), set against Woodford (2003), *Interest and Prices*, Chapter 2 (Propositions 2.5 and
2.6, eq. (4.2)) and Chapter 4 (eq. (4.1)). The Woodford results are restated here (copied, not
imported) and the contrast with the fiscal theory is proved. The restated closure property
`Closed` lives in `ExpectationTools`; the links among this chapter's own modules are in
`GeneralLinks`.

## Main results

* **Pegs.** Woodford's Proposition 2.5 (restated: `sunspot_fisher`, `sunspotPrice_injective`,
  `prop_2_5_uncountable`): with only the exact Fisher equation an interest-rate peg has
  uncountably many price paths with the same `P_0`. Cochrane p. 33 ("inflation is stable and
  determinate under a peg"): adding the government valuation equation, `PegEqm`, there is
  exactly one equilibrium for every adapted peg `i > −1` and every bounded surplus process with
  present value bounded away from zero (`peg_ftpl_existsUnique`); in the same coin-flip economy
  the equilibrium set is a singleton inside Woodford's uncountable set (`peg_contrast`).
* **Rules.** Woodford's Proposition 2.6 (restated: `prop_2_6_iff`, bounded solutions are unique
  iff `|φ_π| > 1`) against `LinearFTMP.rule_existsUnique` (unique for every `θ`):
  `rule_solves_eq26`, `taylor_contrast`, and in the coin-flip economy with `π_0 = 0` and
  `|θ| < 1`: uncountably many bounded solutions of Woodford's (2.6) versus exactly one
  equilibrium of (2.24)+(2.21) (`taylor_contrast_coin`).
* **Passive fiscal policy.** Woodford's (4.2) (restated: `ricardian_tvc`): a Ricardian rule makes
  the transversality condition hold along every path. Then the valuation equation holds for
  every initial price level (`passive_any_price`), while with exogenous surpluses it pins the
  price level (`active_unique_value`).
* **Timing.** Woodford's (4.1) `Budget` (restated) is Cochrane's (2.4) with `B_t = (1 + i_t) D_t`
  and `P_t s_t = T_t − P_t G_t` (`timing_link`); Woodford's real debt `b_t` is Cochrane's
  `V_t = B_t/P_t`, and `b_t/Π_{t+1} = B_t/P_{t+1}` (`timing_real`).
-/

namespace Cochrane.IntertemporalModel.Links

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Woodford, Chapter 2, Proposition 2.5 (restated) -/

/-- Woodford (2003), eq. (1.21), p. 71 (restated from the Woodford Chapter 2 project): the exact
Fisher equation `1 + i_t = β⁻¹ {E_t[u_c,t+1 P_t/(u_c,t P_{t+1})]}⁻¹`. -/
def FisherExactW (β : ℝ) (i uc P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω)⁻¹

/-- Cochrane (2023), eq. (2.3), p. 22 (constant marginal utility `c_t = y`) is Woodford's (1.21)
with `u_c ≡ 1`: `1/(1 + i_t) = β E_t(P_t/P_{t+1})` iff `1 + i_t = β⁻¹ [E_t(P_t/P_{t+1})]⁻¹`. -/
theorem fisher_iff_W {β : ℝ} {i P : ℕ → Ω → ℝ} {t : ℕ} :
    LinearFTMP.FisherExact 𝔼 β i P t ↔ FisherExactW 𝔼 β i (fun _ _ => 1) P t := by
  refine forall_congr' fun ω => ?_
  simp only [one_mul, one_div]
  rw [inv_eq_iff_eq_inv, mul_inv]

/-- Woodford (2003), §A.6, p. 639 (restated): `K_t = E_t[u_c,t+1(1 − ν_{t+1})]`. -/
noncomputable def Kexp (uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated): gross inflation
`Π_{t+1} = β(1 + i_t) K_t / (u_c,t (1 − ν_{t+1}))`. -/
noncomputable def grossInfl (β : ℝ) (i uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * Kexp 𝔼 uc ν t ω / (uc t ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated): the sunspot price path, `P_{t+1} = P_t Π_{t+1}`. -/
noncomputable def sunspotPrice (β : ℝ) (P0 : Ω → ℝ) (i uc ν : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => sunspotPrice β P0 i uc ν t ω * grossInfl 𝔼 β i uc ν t ω

/-- Woodford (2003), §A.6, p. 639 (restated): `u_c(1 − ν) ≥ m` implies `K_t ≥ m`. -/
theorem Kexp_ge {m : ℝ} {uc ν : ℕ → Ω → ℝ} (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ)
    (ω : Ω) : m ≤ Kexp 𝔼 uc ν t ω :=
  const_le_E 𝔼 (fun ω => hm (t + 1) ω) t ω

/-- Woodford (2003), §A.6, p. 639 (restated): gross inflation is positive. -/
theorem grossInfl_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {i uc ν : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) : 0 < grossInfl 𝔼 β i uc ν t ω := by
  have hK := Kexp_ge 𝔼 hm t ω
  have h1 := hi t ω
  have h2 := huc t ω
  have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
  exact div_pos (mul_pos (mul_pos hβ h1) (lt_of_lt_of_le hm0 hK)) (mul_pos h2 h3)

/-- Woodford (2003), §A.6, p. 639 (restated): the sunspot price path is positive. -/
theorem sunspotPrice_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {P0 : Ω → ℝ}
    (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ} (hi : ∀ t ω, 0 < 1 + i t ω)
    (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) :
    0 < sunspotPrice 𝔼 β P0 i uc ν t ω := by
  induction t with
  | zero => exact hP0 ω
  | succ t ih => exact mul_pos ih (grossInfl_pos 𝔼 hβ hm0 hi huc hν hm t ω)

/-- Woodford (2003), Proposition 2.5 and §A.6, pp. 87, 639 (restated): for an exogenous rate
target and any process `ν < 1` with `u_c(1 − ν) ≥ m > 0`, the sunspot price path satisfies the
exact Fisher equation (1.21) at every date. -/
theorem sunspot_fisher (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β m : ℝ} (hβ : 0 < β)
    (hm0 : 0 < m) {P0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ}
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω)
    (hν : ∀ t ω, ν t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) :
    FisherExactW 𝔼 β i uc (sunspotPrice 𝔼 β P0 i uc ν) t := by
  intro ω
  set c : Ω → ℝ := fun ω => (β * (1 + i t ω) * Kexp 𝔼 uc ν t ω)⁻¹ with hc
  set x : Ω → ℝ := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω) with hx
  have hcK : 𝔼.E t c = c := hC t (fun a b => (β * (1 + a) * b)⁻¹) (i t) (Kexp 𝔼 uc ν t)
    (hia t) (𝔼.E_E_self t _)
  have hfun : (fun ω' => uc (t + 1) ω' * sunspotPrice 𝔼 β P0 i uc ν t ω' /
      (uc t ω' * sunspotPrice 𝔼 β P0 i uc ν (t + 1) ω')) = c * x := by
    funext ω'
    have hP := sunspotPrice_pos 𝔼 hβ hm0 hP0 hi huc hν hm t ω'
    have hK := Kexp_ge 𝔼 hm t ω'
    have h1 := hi t ω'
    have h2 := huc t ω'
    have h3 : 0 < 1 - ν (t + 1) ω' := by linarith [hν (t + 1) ω']
    have hKp : 0 < Kexp 𝔼 uc ν t ω' := lt_of_lt_of_le hm0 hK
    simp only [sunspotPrice, grossInfl, Pi.mul_apply, hc, hx]
    field_simp
  have hE : 𝔼.E t (c * x) ω = (β * (1 + i t ω))⁻¹ := by
    rw [hPO t c x hcK, Pi.mul_apply]
    have hK : 𝔼.E t x ω = Kexp 𝔼 uc ν t ω := rfl
    have hKp : 0 < Kexp 𝔼 uc ν t ω := lt_of_lt_of_le hm0 (Kexp_ge 𝔼 hm t ω)
    have h1 := hi t ω
    rw [hK, hc]
    field_simp
  rw [hfun, hE]
  have h1 := hi t ω
  field_simp

/-- Woodford (2003), §A.6, p. 639 (restated): distinct martingale differences give distinct
sunspot price paths. -/
theorem sunspotPrice_injective (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β m m' : ℝ} (hβ : 0 < β)
    (hm0 : 0 < m) (hm0' : 0 < m') {P0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) {i uc ν ν' : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hν' : ∀ t ω, ν' t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hm' : ∀ t ω, m' ≤ uc t ω * (1 - ν' t ω)) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0)
    (hmd' : ∀ t, 𝔼.E t (ν' (t + 1)) = 0)
    (heq : sunspotPrice 𝔼 β P0 i uc ν = sunspotPrice 𝔼 β P0 i uc ν') (t : ℕ) :
    ν (t + 1) = ν' (t + 1) := by
  set c : Ω → ℝ := fun ω => Kexp 𝔼 uc ν' t ω / Kexp 𝔼 uc ν t ω with hc
  have hcK : 𝔼.E t c = c := hC t (fun a b => a / b) (Kexp 𝔼 uc ν' t) (Kexp 𝔼 uc ν t)
    (𝔼.E_E_self t _) (𝔼.E_E_self t _)
  have hPi : ∀ ω, grossInfl 𝔼 β i uc ν t ω = grossInfl 𝔼 β i uc ν' t ω := by
    intro ω
    have h1 := congrFun (congrFun heq (t + 1)) ω
    have h0 := congrFun (congrFun heq t) ω
    have hP := sunspotPrice_pos 𝔼 hβ hm0 hP0 hi huc hν hm t ω
    simp only [sunspotPrice] at h1
    rw [h0] at h1 hP
    exact mul_left_cancel₀ hP.ne' h1
  have hrel : (fun ω => 1 - ν' (t + 1) ω) = c * fun ω => 1 - ν (t + 1) ω := by
    funext ω
    have h := hPi ω
    have hK := lt_of_lt_of_le hm0 (Kexp_ge 𝔼 hm t ω)
    have hK' := lt_of_lt_of_le hm0' (Kexp_ge 𝔼 hm' t ω)
    have h1 := hi t ω
    have h2 := huc t ω
    have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
    have h3' : 0 < 1 - ν' (t + 1) ω := by linarith [hν' (t + 1) ω]
    simp only [grossInfl] at h
    simp only [Pi.mul_apply, hc]
    field_simp at h ⊢
    linear_combination h
  have hone : ∀ μ : ℕ → Ω → ℝ, 𝔼.E t (μ (t + 1)) = 0 →
      𝔼.E t (fun ω => 1 - μ (t + 1) ω) = fun _ => 1 := by
    intro μ hμ
    have : (fun ω => 1 - μ (t + 1) ω) = (fun _ => (1 : ℝ)) - μ (t + 1) := rfl
    rw [this, map_sub, 𝔼.const, hμ, sub_zero]
  have hc1 : c = fun _ => 1 := by
    have h := congrArg (𝔼.E t) hrel
    rw [hone ν' (hmd' t), hPO t c _ hcK, hone ν (hmd t)] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.mul_apply, mul_one] at this
    exact this.symm
  funext ω
  have := congrFun hrel ω
  rw [hc1] at this
  simp only [Pi.mul_apply, one_mul] at this
  linarith

/-- Woodford (2003), Proposition 2.5, p. 87 (restated from the Woodford Chapter 2 project): in
the coin-flip economy with `u_c ≡ 1`, a peg `i ≡ β⁻¹ − 1` and `P_0 = 1`, there are uncountably
many solutions of the exact Fisher equation (the sunspots `ν = s ε`, `s ∈ (−1, 1)`). -/
theorem prop_2_5_uncountable {β : ℝ} (hβ : 0 < β) :
    ¬ {P : ℕ → Bool × Bool → ℝ | (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1}.Countable := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hPO : 𝔼c.PullOut := ExpectationsFiniteTree.finiteTree_pullOut _
  have hC : Closed 𝔼c := finiteTree_closed _
  have hεb : ∀ t ω, |ExpectationsFiniteTree.coinShock t ω| ≤ 1 := by
    intro t ω
    unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> norm_num
  have hi : ∀ (t : ℕ) (ω : Bool × Bool), 0 < 1 + (fun (_ : ℕ) (_ : Bool × Bool) => β⁻¹ - 1) t ω :=
    fun _ _ => by simp [hβ]
  have hia : 𝔼c.Adapted (fun _ _ => β⁻¹ - 1) := fun t => 𝔼c.const t _
  let f : ℝ → ℕ → Bool × Bool → ℝ := fun s => sunspotPrice 𝔼c β (fun _ => 1) (fun _ _ => β⁻¹ - 1)
    (fun _ _ => 1) (fun t => s • ExpectationsFiniteTree.coinShock t)
  have hνlt : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ω,
      (fun t => s • ExpectationsFiniteTree.coinShock t) t ω < 1 := by
    intro s hs t ω
    have h1 : |s * ExpectationsFiniteTree.coinShock t ω| ≤ |s| := by
      rw [abs_mul]
      nlinarith [hεb t ω, abs_nonneg s]
    have h2 : |s| < 1 := abs_lt.mpr hs
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [le_abs_self (s * ExpectationsFiniteTree.coinShock t ω)]
  have hmlow : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ω, 1 - |s| ≤ (fun (_ : ℕ) (_ : Bool × Bool) =>
      (1 : ℝ)) t ω * (1 - (fun t => s • ExpectationsFiniteTree.coinShock t) t ω) := by
    intro s _ t ω
    have h1 : |s * ExpectationsFiniteTree.coinShock t ω| ≤ |s| := by
      rw [abs_mul]
      nlinarith [hεb t ω, abs_nonneg s]
    simp only [Pi.smul_apply, smul_eq_mul, one_mul]
    linarith [le_abs_self (s * ExpectationsFiniteTree.coinShock t ω)]
  have hmpos : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, 0 < 1 - |s| := fun s hs => by
    have := abs_lt.mpr hs
    linarith
  have hmd : ∀ s : ℝ, ∀ t, 𝔼c.E t ((fun t => s • ExpectationsFiniteTree.coinShock t) (t + 1)) =
      0 := by
    intro s t
    simp only [map_smul]
    rw [ExpectationsFiniteTree.coinShock_mean_zero, smul_zero]
  have hmaps : Set.MapsTo f (Set.Ioo (-1) 1) {P | (∀ t, FisherExactW 𝔼c β
      (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1} := by
    intro s hs
    exact ⟨fun t => sunspot_fisher 𝔼c hPO hC hβ (hmpos s hs) (fun _ => one_pos) hia hi
      (fun _ _ => one_pos) (hνlt s hs) (hmlow s hs) t, rfl⟩
  have hinj : Set.InjOn f (Set.Ioo (-1) 1) := by
    intro s hs s' hs' h
    have := sunspotPrice_injective 𝔼c hPO hC hβ (hmpos s hs) (hmpos s' hs') (fun _ => one_pos)
      hi (fun _ _ => one_pos) (hνlt s hs) (hνlt s' hs') (hmlow s hs) (hmlow s' hs')
      (hmd s) (hmd s') h 0
    have := congrFun this (true, true)
    simpa [ExpectationsFiniteTree.coinShock] using this
  intro hcount
  have := hmaps.countable_of_injOn hinj hcount
  rw [Cardinal.Real.Ioo_countable_iff] at this
  norm_num at this

/-! ### Cochrane p. 33: under the fiscal theory the peg is determinate -/

/-- Cochrane (2023), eqs. (2.3) and (2.7), pp. 22, 33: an equilibrium `(P, B)` under the
interest-rate peg `i`, with initial debt `B_{−1}` and present value of surpluses
`PV_t = E_t ∑ βʲ s_{t+j}`: positive adapted prices, adapted debt, the exact Fisher equation at
every date, and the valuation equation `B_{t−1}/P_t = PV_t` at every date. -/
def PegEqm (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) (P B : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted P ∧ 𝔼.Adapted B ∧ (∀ t ω, 0 < P t ω) ∧ (∀ t, LinearFTMP.FisherExact 𝔼 β i P t) ∧
    (∀ ω, Bm1 / P 0 ω = PV 0 ω) ∧ ∀ t ω, B t ω / P (t + 1) ω = PV (t + 1) ω

/-- Cochrane (2023), pp. 31–33 (debt follows from the rate target, cf. (2.18)): in any peg
equilibrium `B_t = β(1 + i_t) P_t E_t PV_{t+1}` and `P_{t+1} = B_t/PV_{t+1}`. -/
theorem pegEqm_debt (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β : ℝ}
    {i PV P B : ℕ → Ω → ℝ} {Bm1 c : ℝ} (hc : 0 < c) (hPV : ∀ t ω, c ≤ PV t ω)
    (hi : ∀ t ω, 0 < 1 + i t ω) (h : PegEqm 𝔼 β i PV Bm1 P B) (t : ℕ) (ω : Ω) :
    B t ω = β * (1 + i t ω) * (P t ω * 𝔼.E t (PV (t + 1)) ω) ∧
      P (t + 1) ω = B t ω / PV (t + 1) ω := by
  obtain ⟨hPa, hBa, hPpos, hfis, -, hval⟩ := h
  have hPV1 : ∀ ω', 0 < PV (t + 1) ω' := fun ω' => hc.trans_le (hPV (t + 1) ω')
  have hBpos : ∀ ω', 0 < B t ω' := fun ω' => by
    have h := hval t ω'
    rw [div_eq_iff (hPpos (t + 1) ω').ne'] at h
    rw [h]
    exact mul_pos (hPV1 ω') (hPpos (t + 1) ω')
  have hP1 : ∀ ω', P (t + 1) ω' = B t ω' / PV (t + 1) ω' := fun ω' => by
    have h := hval t ω'
    have hp := (hPpos (t + 1) ω').ne'
    rw [eq_div_iff (hPV1 ω').ne', ← h]
    field_simp
  have hratio : (fun ω' => P t ω' / P (t + 1) ω') =
      (fun ω' => P t ω' / B t ω') * PV (t + 1) := by
    funext ω'
    rw [hP1 ω', Pi.mul_apply, div_div_eq_mul_div, mul_div_right_comm]
  have hk : 𝔼.E t (fun ω' => P t ω' / B t ω') = fun ω' => P t ω' / B t ω' :=
    hC t (fun a b => a / b) (P t) (B t) (hPa t) (hBa t)
  have hf := hfis t ω
  rw [hratio, hPO t _ _ hk, Pi.mul_apply] at hf
  have hE := hc.trans_le (const_le_E 𝔼 (hPV (t + 1)) t ω)
  have h1 := hi t ω
  have h2 := hBpos ω
  refine ⟨?_, hP1 ω⟩
  field_simp at hf
  linarith

/-- Cochrane (2023), p. 33: the candidate equilibrium price path, `P_0 = B_{−1}/PV_0`,
`P_{t+1} = β(1 + i_t) P_t E_t PV_{t+1} / PV_{t+1}`. -/
noncomputable def ftplPrice (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Bm1 / PV 0 ω
  | t + 1 => fun ω => β * (1 + i t ω) * (ftplPrice β i PV Bm1 t ω * 𝔼.E t (PV (t + 1)) ω) /
      PV (t + 1) ω

/-- Cochrane (2023), p. 33: the candidate equilibrium debt `B_t = β(1 + i_t) P_t E_t PV_{t+1}`. -/
noncomputable def ftplDebt (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * (ftplPrice 𝔼 β i PV Bm1 t ω * 𝔼.E t (PV (t + 1)) ω)

/-- Cochrane (2023), p. 33 ("inflation is stable and determinate under a peg", fiscal theory):
for every adapted peg with `1 + i_t > 0`, adapted present values bounded below by `c > 0` and
initial debt `B_{−1} > 0`, there is exactly one peg equilibrium `(P, B)`. Uses the pull-out and
closure properties of the expectations (both hold on finite event trees). -/
theorem peg_ftpl_existsUnique (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β : ℝ} (hβ : 0 < β)
    {i PV : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i) (hi : ∀ t ω, 0 < 1 + i t ω) (hPVa : 𝔼.Adapted PV)
    {c : ℝ} (hc : 0 < c) (hPV : ∀ t ω, c ≤ PV t ω) {Bm1 : ℝ} (hB : 0 < Bm1) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PegEqm 𝔼 β i PV Bm1 q.1 q.2 := by
  have hPVp : ∀ t ω, 0 < PV t ω := fun t ω => hc.trans_le (hPV t ω)
  have hEp : ∀ t ω, 0 < 𝔼.E t (PV (t + 1)) ω := fun t ω =>
    hc.trans_le (const_le_E 𝔼 (hPV (t + 1)) t ω)
  have hpos : ∀ t ω, 0 < ftplPrice 𝔼 β i PV Bm1 t ω := by
    intro t
    induction t with
    | zero => exact fun ω => div_pos hB (hPVp 0 ω)
    | succ t ih =>
      intro ω
      exact div_pos (mul_pos (mul_pos hβ (hi t ω)) (mul_pos (ih ω) (hEp t ω))) (hPVp _ ω)
  have hdebt_of : ∀ t, 𝔼.E t (ftplPrice 𝔼 β i PV Bm1 t) = ftplPrice 𝔼 β i PV Bm1 t →
      𝔼.E t (ftplDebt 𝔼 β i PV Bm1 t) = ftplDebt 𝔼 β i PV Bm1 t := by
    intro t ht
    have hy := hC t (fun a b => a * b) (ftplPrice 𝔼 β i PV Bm1 t) (𝔼.E t (PV (t + 1))) ht
      (𝔼.E_E_self t _)
    exact hC t (fun a b => β * (1 + a) * b) (i t) _ (hia t) hy
  have hPa : 𝔼.Adapted (ftplPrice 𝔼 β i PV Bm1) := by
    intro t
    induction t with
    | zero => exact hC 0 (fun a _ => Bm1 / a) (PV 0) (PV 0) (hPVa 0) (hPVa 0)
    | succ t ih =>
      exact hC (t + 1) (fun a b => a / b) (ftplDebt 𝔼 β i PV Bm1 t) (PV (t + 1))
        (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hdebt_of t ih)) (hPVa (t + 1))
  have hBa : 𝔼.Adapted (ftplDebt 𝔼 β i PV Bm1) := fun t => hdebt_of t (hPa t)
  have hDpos : ∀ t ω, 0 < ftplDebt 𝔼 β i PV Bm1 t ω := fun t ω =>
    mul_pos (mul_pos hβ (hi t ω)) (mul_pos (hpos t ω) (hEp t ω))
  have heqm : PegEqm 𝔼 β i PV Bm1 (ftplPrice 𝔼 β i PV Bm1) (ftplDebt 𝔼 β i PV Bm1) := by
    refine ⟨hPa, hBa, hpos, fun t ω => ?_, fun ω => ?_, fun t ω => ?_⟩
    · have hratio : (fun ω' => ftplPrice 𝔼 β i PV Bm1 t ω' / ftplPrice 𝔼 β i PV Bm1 (t + 1) ω') =
          (fun ω' => ftplPrice 𝔼 β i PV Bm1 t ω' / ftplDebt 𝔼 β i PV Bm1 t ω') * PV (t + 1) := by
        funext ω'
        change _ / (ftplDebt 𝔼 β i PV Bm1 t ω' / PV (t + 1) ω') = _
        rw [Pi.mul_apply, div_div_eq_mul_div, mul_div_right_comm]
      have hk := hC t (fun a b => a / b) _ _ (hPa t) (hBa t)
      rw [hratio, hPO t _ _ hk, Pi.mul_apply]
      have h1 := hi t ω
      have h2 := hpos t ω
      have h3 := hEp t ω
      unfold ftplDebt
      field_simp
    · change Bm1 / (Bm1 / PV 0 ω) = PV 0 ω
      have := hPVp 0 ω
      field_simp
    · change ftplDebt 𝔼 β i PV Bm1 t ω / (ftplDebt 𝔼 β i PV Bm1 t ω / PV (t + 1) ω) = _
      have := hDpos t ω
      have := hPVp (t + 1) ω
      field_simp
  refine ⟨(ftplPrice 𝔼 β i PV Bm1, ftplDebt 𝔼 β i PV Bm1), heqm, ?_⟩
  rintro ⟨P, B⟩ h
  dsimp only at h
  have hd := pegEqm_debt 𝔼 hPO hC hc hPV hi h
  have hP : P = ftplPrice 𝔼 β i PV Bm1 := by
    funext t ω
    induction t generalizing ω with
    | zero =>
      have h0 := h.2.2.2.2.1 ω
      have hp := h.2.2.1 0 ω
      change P 0 ω = Bm1 / PV 0 ω
      rw [div_eq_iff hp.ne'] at h0
      rw [eq_div_iff (hPVp 0 ω).ne', h0, mul_comm]
    | succ t ih =>
      change P (t + 1) ω = β * (1 + i t ω) * (ftplPrice 𝔼 β i PV Bm1 t ω *
        𝔼.E t (PV (t + 1)) ω) / PV (t + 1) ω
      rw [(hd t ω).2, (hd t ω).1]
      rw [show P t = ftplPrice 𝔼 β i PV Bm1 t from funext ih]
  refine Prod.ext hP ?_
  funext t ω
  change B t ω = ftplDebt 𝔼 β i PV Bm1 t ω
  rw [(hd t ω).1, hP]
  rfl

/-- Cochrane (2023), p. 33: with constant surpluses `s ≡ 1 − β` (`0 ≤ β < 1`) the present value
`PV_t = ∑ βᵏ E_t s_{t+k}` is `1` at every date and state. -/
theorem pv_const {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (t : ℕ) :
    𝔼.forwardSeries β (fun _ _ => 1 - β) t = fun _ => 1 := by
  funext ω
  change ∑' k, β ^ k * 𝔼.E t (fun _ => 1 - β) ω = 1
  simp only [𝔼.const]
  rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1, inv_mul_cancel₀ (by linarith)]

/-- Cochrane (2023), p. 33 against Woodford (2003), Proposition 2.5, p. 87 ("the fiscal theory
overturns" the indeterminacy of pegs): in the same coin-flip economy with the peg
`i ≡ β⁻¹ − 1` and `u_c ≡ 1`, (a) the exact Fisher equation alone has uncountably many price
paths with `P_0 = 1`; (b) adding the valuation equation (`s ≡ 1 − β`, `B_{−1} = 1`) leaves exactly
one equilibrium price path, `P ≡ 1`; (c) that path is one of the paths in (a). -/
theorem peg_contrast {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ¬ {P : ℕ → Bool × Bool → ℝ | (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1}.Countable ∧
      {P : ℕ → Bool × Bool → ℝ | ∃ B, PegEqm ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (ExpectationsFiniteTree.coinSystem.forwardSeries β
          (fun _ _ => 1 - β)) 1 P B} = {fun _ _ => 1} ∧
      ∀ P B, PegEqm ExpectationsFiniteTree.coinSystem β (fun _ _ => β⁻¹ - 1)
        (ExpectationsFiniteTree.coinSystem.forwardSeries β (fun _ _ => 1 - β)) 1 P B →
        (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β (fun _ _ => β⁻¹ - 1)
          (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1 := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hPO : 𝔼c.PullOut := ExpectationsFiniteTree.finiteTree_pullOut _
  have hC : Closed 𝔼c := finiteTree_closed _
  have hpv := pv_const 𝔼c hβ.le hβ1
  have hia : 𝔼c.Adapted (fun _ _ => β⁻¹ - 1) := fun t => 𝔼c.const t _
  have hi : ∀ (t : ℕ) (ω : Bool × Bool), 0 < 1 + (fun (_ : ℕ) (_ : Bool × Bool) => β⁻¹ - 1) t ω :=
    fun _ _ => by simp [hβ]
  have hPVa : 𝔼c.Adapted (𝔼c.forwardSeries β (fun _ _ => 1 - β)) := fun t => by
    rw [hpv t, 𝔼c.const]
  have hPV : ∀ t ω, (1 : ℝ) ≤ 𝔼c.forwardSeries β (fun _ _ => 1 - β) t ω := fun t ω => by
    rw [hpv t]
  have hone : PegEqm 𝔼c β (fun _ _ => β⁻¹ - 1) (𝔼c.forwardSeries β (fun _ _ => 1 - β)) 1
      (fun _ _ => 1) (fun _ _ => 1) := by
    refine ⟨fun t => 𝔼c.const t 1, fun t => 𝔼c.const t 1, fun _ _ => one_pos, fun t ω => ?_,
      fun ω => ?_, fun t ω => ?_⟩
    · simp only [div_one]
      rw [𝔼c.const]
      field_simp
      ring
    · rw [hpv 0, div_one]
    · rw [hpv (t + 1), div_one]
  have hu := peg_ftpl_existsUnique 𝔼c hPO hC hβ hia hi hPVa one_pos hPV one_pos
  have hfish : ∀ P B, PegEqm 𝔼c β (fun _ _ => β⁻¹ - 1) (𝔼c.forwardSeries β (fun _ _ => 1 - β)) 1
      P B → (∀ t, FisherExactW 𝔼c β (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧
        P 0 = fun _ => 1 := by
    intro P B h
    refine ⟨fun t => (fisher_iff_W 𝔼c).mp (h.2.2.2.1 t), ?_⟩
    funext ω
    have h0 := h.2.2.2.2.1 ω
    rw [hpv 0, div_eq_one_iff_eq (h.2.2.1 0 ω).ne'] at h0
    exact h0.symm
  refine ⟨prop_2_5_uncountable hβ, ?_, hfish⟩
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨B, h⟩
    exact congrArg Prod.fst (hu.unique (y₁ := (P, B)) (y₂ := (fun _ _ => 1, fun _ _ => 1)) h hone)
  · rintro rfl
    exact ⟨_, hone⟩

/-! ### Woodford, Chapter 2, Proposition 2.6 (restated) and the Taylor principle -/

/-- Woodford (2003), eq. (2.6), p. 91 (restated from the Woodford Chapter 2 project):
`φ_π π_t = E_t π_{t+1} + (r̂_t − ī_t)`. Used for Cochrane (2023), §2.6. -/
def Eq26 (φπ : ℝ) (r ib π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φπ • π t = 𝔼.E t (π (t + 1)) + (r t - ib t)

/-- Woodford (2003), eq. (2.6), App. A, p. 636 (restated): for `φ_π ≠ 0`, (2.6) is the forward
equation with `a = φ_π⁻¹`, `u_t = φ_π⁻¹(r̂_t − ī_t)`. Used for Cochrane (2023), §2.6. -/
theorem eq26_iff_solves {φπ : ℝ} (hφ : φπ ≠ 0) {r ib π : ℕ → Ω → ℝ} :
    Eq26 𝔼 φπ r ib π ↔ ForwardSolution.Solves 𝔼 φπ⁻¹ (fun t => φπ⁻¹ • (r t - ib t)) π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), Proposition 2.6, p. 91 (restated from the Woodford Chapter 2 project):
(2.6) has a unique bounded solution for every bounded adapted `{r̂, ī}` iff `|φ_π| > 1`. -/
theorem prop_2_6_iff [Nonempty Ω] (φπ : ℝ) :
    (∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 φπ r ib π) ↔ 1 < |φπ| := by
  constructor
  · intro h
    by_contra hc
    have hc' : |φπ| ≤ 1 := not_lt.mp hc
    have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨π, -, hu⟩ := h 0 0 hzb hzb (fun t => map_zero _) (fun t => map_zero _)
    have e0 := hu 0 ⟨hzb, fun t => by simp⟩
    have e1 := hu (fun t _ => φπ ^ t) ⟨⟨1, fun t _ => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc'⟩, fun t => by
        rw [𝔼.const]
        funext ω
        simp [pow_succ]
        ring⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (e1.trans e0.symm) 0) ω
    simp at this
  · intro hφ r ib hrb hib hra hia
    have hne : φπ ≠ 0 := by
      intro h
      rw [h, abs_zero] at hφ
      linarith
    have ha : |φπ⁻¹| < 1 := by
      rw [abs_inv]
      exact inv_lt_one_of_one_lt₀ hφ
    obtain ⟨Mr, hr⟩ := hrb
    obtain ⟨Mi, hi⟩ := hib
    have hub : BoundedProc (fun t => φπ⁻¹ • (r t - ib t)) := by
      refine ⟨Mr + Mi, fun t ω => ?_⟩
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      calc |φπ⁻¹| * |r t ω - ib t ω| ≤ 1 * |r t ω - ib t ω| := by gcongr
        _ ≤ Mr + Mi := by
          rw [one_mul]; exact (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))
    have hua : 𝔼.Adapted (fun t => φπ⁻¹ • (r t - ib t)) := by
      intro t
      simp only [map_smul, map_sub, hra t, hia t]
    obtain ⟨z, hz, hu⟩ := ForwardSolution.existsUnique_bounded 𝔼 ha hub hua
    exact ⟨z, ⟨hz.1, (eq26_iff_solves 𝔼 hne).mpr hz.2⟩,
      fun π hπ => hu π ⟨hπ.1, (eq26_iff_solves 𝔼 hne).mp hπ.2⟩⟩

/-- Woodford (2003), App. A, p. 637 (restated): the family `π_0` given,
`π_{t+1} = φ_π π_t − (r̂_t − ī_t) + ν_{t+1}`. Used for Cochrane (2023), §2.6. -/
def sunspotInfl (φπ : ℝ) (r ib ν : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => φπ • sunspotInfl φπ r ib ν π0 t - (r t - ib t) + ν (t + 1)

/-- Woodford (2003), Proposition 2.6, p. 91 (restated): for any `φ_π` and any martingale
difference `ν`, `sunspotInfl` solves (2.6). Used for Cochrane (2023), §2.6. -/
theorem sunspotInfl_solves {φπ : ℝ} {r ib ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Eq26 𝔼 φπ r ib (sunspotInfl φπ r ib ν π0) := by
  have had : 𝔼.Adapted (sunspotInfl φπ r ib ν π0) := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      simp only [sunspotInfl, map_add, map_sub, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hra t),
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hia t), hνa (t + 1)]
  intro t
  simp only [sunspotInfl, map_add, map_sub, map_smul, had t, hra t, hia t, hmd t, add_zero]
  abel

/-- Woodford (2003), Proposition 2.6, p. 91 (restated): for `|φ_π| < 1` the family is bounded
when `π_0`, `r̂ − ī` and `ν` are. Used for Cochrane (2023), §2.6. -/
theorem sunspotInfl_bounded {φπ B G Mν : ℝ} (hφ : |φπ| < 1) {r ib ν : ℕ → Ω → ℝ}
    {π0 : Ω → ℝ} (h0 : ∀ ω, |π0 ω| ≤ B) (hg : ∀ t ω, |r t ω - ib t ω| ≤ G)
    (hν : ∀ t ω, |ν t ω| ≤ Mν) : BoundedProc (sunspotInfl φπ r ib ν π0) := by
  set K := |B| + (|G| + |Mν|) / (1 - |φπ|) with hK
  have h1 : 0 < 1 - |φπ| := by linarith
  have hfrac : 0 ≤ (|G| + |Mν|) / (1 - |φπ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self B).trans (by linarith))
  | succ t ih =>
    intro ω
    simp only [sunspotInfl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have ha : |φπ * sunspotInfl φπ r ib ν π0 t ω| ≤ |φπ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hg t ω).trans (le_abs_self G)
    have hc := (hν (t + 1) ω).trans (le_abs_self Mν)
    have hKe : K * (1 - |φπ|) = |B| * (1 - |φπ|) + (|G| + |Mν|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |B| * (1 - |φπ|) := mul_nonneg (abs_nonneg B) h1.le
    calc |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω) + ν (t + 1) ω|
        ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω)| + |ν (t + 1) ω| :=
          abs_add_le _ _
      _ ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω| + |r t ω - ib t ω| + |ν (t + 1) ω| := by
          gcongr; exact abs_sub _ _
      _ ≤ K := by nlinarith

/-- Cochrane (2023), eq. (2.24), p. 40, is Woodford (2003), eq. (2.6), p. 91, with `φ_π = θ`,
`r̂ = 0` and `ī = u`: `E_t π_{t+1} = θ π_t + u_t` iff `θ π_t = E_t π_{t+1} + (0 − u_t)`. -/
theorem eq26_iff_224 {θ : ℝ} {u π : ℕ → Ω → ℝ} :
    Eq26 𝔼 θ 0 u π ↔ ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §2.6, p. 40, against Woodford (2003), Proposition 2.6: every equilibrium of
(2.24)+(2.21) is a solution of Woodford's (2.6) (`φ_π = θ`, `r̂ = 0`, `ī = u`); the valuation
equation (2.21) selects one of them. -/
theorem rule_solves_eq26 {θ : ℝ} {u ε π : ℕ → Ω → ℝ} (hm : LinearFTMP.Eq224 𝔼 θ u ε π) :
    Eq26 𝔼 θ 0 u π :=
  (eq26_iff_224 𝔼).mpr fun t => (hm t).1

/-- Cochrane (2023), §2.6, pp. 39–40 ("no Taylor principle needed") against Woodford (2003),
Proposition 2.6: for `|θ| ≤ 1` the rule fails Woodford's determinacy criterion (bounded
solutions of (2.6) are not unique for all bounded disturbances), yet the fiscal-theory model
(2.20)–(2.22) has exactly one equilibrium for every disturbance, every fiscal shock and every
`π_0`. -/
theorem taylor_contrast [Nonempty Ω] {θ : ℝ} (hθ : |θ| ≤ 1) :
    (¬ ∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 θ r ib π) ∧
    ∀ (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ), 𝔼.E 0 π0 = π0 → 𝔼.Adapted u → LinearFTMP.IsShock 𝔼 ε →
      ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
        LinearFTMP.RuleModel 𝔼 θ q.2 u ε q.1 :=
  ⟨fun h => absurd ((prop_2_6_iff 𝔼 θ).mp h) (not_lt.mpr hθ),
    fun _ _ _ h0 hu hε => LinearFTMP.rule_existsUnique 𝔼 θ h0 hu hε⟩

/-- Cochrane (2023), §2.6, against Woodford (2003), Proposition 2.6 ("if instead `0 ≤ φ_π < 1`
... indeterminate"), in the coin-flip economy with no disturbances, `|θ| < 1` and `π_0 = 0`:
Woodford's (2.6) has uncountably many bounded solutions (sunspots `ν = s ε`), while the fiscal
theory's (2.24)+(2.21) with no fiscal shock has exactly one, `π ≡ 0`. -/
theorem taylor_contrast_coin {θ : ℝ} (hθ : |θ| < 1) :
    ¬ {π : ℕ → Bool × Bool → ℝ | BoundedProc π ∧ Eq26 ExpectationsFiniteTree.coinSystem θ 0 0 π ∧
        π 0 = 0}.Countable ∧
      {π : ℕ → Bool × Bool → ℝ | ExpectationsFiniteTree.coinSystem.Adapted π ∧ π 0 = 0 ∧
        LinearFTMP.Eq224 ExpectationsFiniteTree.coinSystem θ 0 0 π} = {0} := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hAR := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hzero : 𝔼c.Adapted (0 : ℕ → Bool × Bool → ℝ) := fun t => map_zero _
  have hb : ∀ t ω, |ExpectationsFiniteTree.coinAR1 0 t ω| ≤ 1 := by
    intro t ω
    cases t with
    | zero => simp [ExpectationsFiniteTree.coinAR1]
    | succ t =>
      simp only [ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
        ExpectationsFiniteTree.coinShock]
      split_ifs <;> norm_num
  have hs0 : LinearFTMP.IsShock 𝔼c 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  constructor
  · let f : ℝ → ℕ → Bool × Bool → ℝ := fun s =>
      sunspotInfl θ 0 0 (fun t => s • ExpectationsFiniteTree.coinAR1 0 t) (fun _ => 0)
    have hmaps : Set.MapsTo f Set.univ {π | BoundedProc π ∧ Eq26 𝔼c θ 0 0 π ∧ π 0 = 0} := by
      intro s _
      refine ⟨sunspotInfl_bounded hθ (B := 0) (G := 0) (Mν := |s|) (fun _ => by simp)
        (fun _ _ => by simp) (fun t ω => ?_), sunspotInfl_solves 𝔼c (𝔼c.const 0 0) hzero hzero
        (fun t => by rw [map_smul, hAR.1 t]) (fun t => ?_), rfl⟩
      · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        nlinarith [hb t ω, abs_nonneg s]
      · rw [map_smul, hAR.2 t, zero_smul, smul_zero]
    have hinj : Set.InjOn f Set.univ := by
      intro s _ s' _ h
      have := congrFun (congrFun h 1) (true, true)
      simpa [f, sunspotInfl, ExpectationsFiniteTree.coinAR1, ExpectationsFiniteTree.coinShock]
        using this
    intro hcount
    exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)
  · ext π
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, h0, hm⟩
      have h := (LinearFTMP.eq224_iff 𝔼c ha hzero hs0).mp hm
      funext t
      induction t with
      | zero => exact h0
      | succ t ih =>
        rw [h t, ih]
        simp
    · rintro rfl
      refine ⟨hzero, rfl, (LinearFTMP.eq224_iff 𝔼c hzero hzero hs0).mpr fun t => ?_⟩
      simp

/-! ### Woodford (4.2) (restated) and passive fiscal policy -/

/-- Woodford (2003), §1, p. 66 (restated from the Woodford Chapter 2 project): the
perfect-foresight discount factor `Q_{t,T} = ∏_{s=t}^{T−1} Q_{s,s+1}`. Used for Cochrane (2023),
p. 39. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Woodford (2003), (4.2), p. 124 (restated): under `T_t = αW_t − Δ_tM_t` the government budget
gives `Q_{t,t+1}W_{t+1} = (1 − α)W_t`. Used for Cochrane (2023), p. 39. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Woodford (2003), (4.2), p. 124 (restated): `Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`. Used for
Cochrane (2023), p. 39. -/
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

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): for
`0 < α ≤ 1` the transversality condition `Q_{t,T}W_T → 0` holds along every path. Used for
Cochrane (2023), p. 39. -/
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

/-- Cochrane (2023), eq. (2.5) with perfect foresight and A1 (1.1), p. 554: iterating the flow
condition `w_t = s_t + β w_{t+1}` (`w_t = B_{t−1}/P_t`),
`w_0 = ∑_{j<T} βʲ s_j + β^T w_T`: the perfect-foresight case of `Valuation.telescope`. -/
theorem pv_telescope {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1)) (T : ℕ) :
    w 0 = ∑ j ∈ Finset.range T, β ^ j * s j + β ^ T * w T := by
  have h := congrFun (Valuation.telescope perfectForesight (x := fun t _ => w t)
    (s := fun t _ => s t) (t := 0) (fun t => funext fun _ => hflow t) rfl T) ()
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h
  exact h

/-- Cochrane (2023), p. 39 (passive fiscal policy) via Woodford (2003), (4.2): with perfect
foresight, the flow condition `w_t = s_t + β w_{t+1}` and the passive rule `s_t = α w_t`
(`0 < α ≤ 1`), Woodford's `ricardian_tvc` gives the transversality condition along every
path, so the valuation equation `w_0 = ∑ βʲ s_j` holds for EVERY initial real debt `w_0`, i.e.
for every price level `P_0 = B_{−1}/w_0`: it no longer determines the price level. -/
theorem passive_any_price {β α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {w s : ℕ → ℝ}
    (hflow : ∀ t, w t = s t + β * w (t + 1)) (hrule : ∀ t, s t = α * w t) :
    HasSum (fun j => β ^ j * s j) (w 0) := by
  have hgov : ∀ t, (fun _ => β) t * w (t + 1) = w t - s t - (fun _ => (0 : ℝ)) t * 0 := by
    intro t
    have := hflow t
    simp only [zero_mul, sub_zero]
    linarith
  have hrule' : ∀ t, s t = α * w t - (fun _ => (0 : ℝ)) t * 0 := by
    intro t
    simp only [mul_zero, sub_zero]
    exact hrule t
  have hdisc : ∀ T, discount (fun _ => β) 0 T = β ^ T := fun T => by
    simp [discount, Finset.prod_const]
  have htvc := ricardian_tvc (q := fun _ => β) (W := w) (Tx := s) (M := fun _ => 0) hα0 hα1
    hgov hrule' 0
  simp only [hdisc] at htvc
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s j) atTop (𝓝 (w 0)) := by
    have := (tendsto_const_nhds (x := w 0)).sub htvc
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    rw [pv_telescope hflow T]
    ring
  have hgeo : ∀ j, β ^ j * s j = α * w 0 * (1 - α) ^ j := by
    intro j
    have h := ricardian_discounted (q := fun _ => β) (W := w) (Tx := s) (M := fun _ => 0)
      hgov hrule' 0 j
    rw [zero_add, hdisc] at h
    rw [hrule j, ← mul_assoc, mul_comm (β ^ j) α, mul_assoc, h]
    ring
  have hsum : Summable (fun j => β ^ j * s j) := by
    simp_rw [hgeo]
    exact (summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left _
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart) ▸ hsum.hasSum

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22, perfect foresight (the active case, contrasting
`passive_any_price`): with surpluses given and `∑ βʲ s_j` summable, the flow condition and the
transversality condition `β^T w_T → 0` pin down `w_0 = ∑ βʲ s_j`, hence the price level. -/
theorem active_unique_value {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1))
    (hsum : Summable (fun j => β ^ j * s j))
    (htvc : Tendsto (fun T => β ^ T * w T) atTop (𝓝 0)) : w 0 = ∑' j, β ^ j * s j := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s j) atTop (𝓝 (w 0)) := by
    have := (tendsto_const_nhds (x := w 0)).sub htvc
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    rw [pv_telescope hflow T]
    ring
  exact tendsto_nhds_unique hpart hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), A1, p. 555 (the active case): with given summable surpluses, any initial
real debt other than the present value violates the transversality condition. -/
theorem active_tvc_fails {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1))
    (hsum : Summable (fun j => β ^ j * s j)) (hne : w 0 ≠ ∑' j, β ^ j * s j) :
    ¬ Tendsto (fun T => β ^ T * w T) atTop (𝓝 0) :=
  fun htvc => hne (active_unique_value hflow hsum htvc)

/-! ### Woodford (4.1) (restated) and the timing of the budget constraint -/

/-- Woodford (2003), eq. (4.1), p. 311 (restated from the Woodford Chapter 4 project):
`D_{t+1} = (1 + i_t) D_t + (P_{t+1} G_{t+1} − T_{t+1})`, with `D_t` the end-of-period market value
of nominal debt. Used for Cochrane (2023), eq. (2.4), p. 22. -/
def Budget (D i P G T : ℕ → ℝ) : Prop :=
  ∀ t, D (t + 1) = (1 + i t) * D t + (P (t + 1) * G (t + 1) - T (t + 1))

/-- Cochrane (2023), eq. (2.4), p. 22, against Woodford (2003), eq. (4.1): with face value
`B_t = (1 + i_t) D_t` (Cochrane's debt sold at `t`, due at `t + 1`, price `Q_t = 1/(1 + i_t)`)
and nominal surplus `P_t s_t = T_t − P_t G_t`, Woodford's budget is Cochrane's
`B_t = P_{t+1} s_{t+1} + Q_{t+1} B_{t+1}`. -/
theorem timing_link {D i P G T B s : ℕ → ℝ} (hi : ∀ t, 1 + i t ≠ 0)
    (hB : ∀ t, B t = (1 + i t) * D t) (hs : ∀ t, P t * s t = T t - P t * G t) :
    Budget D i P G T ↔ ∀ t, B t = P (t + 1) * s (t + 1) + B (t + 1) / (1 + i (t + 1)) := by
  refine forall_congr' fun t => ?_
  rw [hB t, hB (t + 1), hs (t + 1), mul_div_cancel_left₀ _ (hi (t + 1))]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eqs. (2.5) and (2.17), pp. 22, 35, against Woodford (2003), p. 312: Woodford's
real debt `b_t = (1 + i_t) D_t/P_t` is Cochrane's `V_t = B_t/P_t`, and deflating by gross
inflation `Π_{t+1} = P_{t+1}/P_t` gives Cochrane's `B_t/P_{t+1}` (the left side of (2.5) at
`t + 1`). -/
theorem timing_real {D i P B : ℕ → ℝ} (hP : ∀ t, P t ≠ 0) (hB : ∀ t, B t = (1 + i t) * D t)
    (t : ℕ) : (1 + i t) * D t / P t = B t / P t ∧
      (1 + i t) * D t / P t / (P (t + 1) / P t) = B t / P (t + 1) := by
  rw [← hB t]
  refine ⟨rfl, ?_⟩
  have h1 := hP t
  have h2 := hP (t + 1)
  field_simp

end Cochrane.IntertemporalModel.Links

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links among the Chapter 2 formalisations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1–§2.6 and §2.9
(pp. 21–42, 47–49). The chapter is formalised three ways: `Valuation` derives the valuation
equation from the flow condition and the transversality condition (`Valuation.IsEqm`, debt
indexed by maturity date `Bm t = B_{t−1}`, bond price `Q`); `FiscalMonetary` takes the valuation
equation as the definition of equilibrium (`FiscalMonetary.Equilibrium`, debt indexed by issue
date `B t = B_t`, nominal rate `i`); `LinearFTMP` and `Links` study the exact Fisher equation and
the linear model. This module proves that they describe the same economics.

## Main results

* Present values: `fm_pv_eq_pv` (the ex-post form `E_t ∑ βʲ s_{t+j}` of `FiscalMonetary.pv`
  equals `Valuation.pv = ∑ βʲ E_t s_{t+j}` under conditional monotone convergence and ex-post
  absolute summability), `fm_pv_eq_pv_of_bounded` (bounded surpluses, any expectation system).
* Equilibrium: `equilibrium_iff_isEqm`: an equilibrium in the sense of `FiscalMonetary`
  (valuation equation plus bond pricing) is exactly an equilibrium in the sense of `Valuation`
  (flow condition (2.4), bond price (2.3), transversality condition (2.6)) with maturing debt
  `debtPath B_{−1} B` and bond price `Q = 1/(1 + i)`; so every result of `FiscalMonetary` and
  `FlatSupply` is about the equilibria derived in `Valuation`. Consequences:
  `equilibrium_price_eq_eqmPrice`, `peg_existsUnique_isEqm` (an interest-rate target selects
  exactly one derived equilibrium), `equilibrium_realRevenue` ((2.14)–(2.15) is (2.11)),
  `twoStep_eq_debtPath`.
* `bondPricing_iff_fisherExact`, `equilibrium_iff_pegEqm`: the bond-pricing condition is the
  exact Fisher equation of `LinearFTMP`, and `Links.PegEqm` with `PV = FiscalMonetary.pv` is
  `FiscalMonetary.Equilibrium`; `ftplPrice_eq_pegP`, `ftplDebt_eq_pegB`: the two peg
  equilibria constructed in `Links` and `FiscalMonetary` coincide.
* The linear model as the derivative of the nonlinear one: `isEqm_fisherExact` and
  `isEqm_fisher_log` (every derived equilibrium satisfies the exact Fisher equation in logs,
  whose derivative at the steady state is `LinearFTMP.fisher_deriv`, the linear (2.16));
  `innov_epv_eq_pvNews` and `equilibrium_pvNews` (the exact (2.13) of every equilibrium is the
  exact (2.17), with the fiscal shock `ε_{Σs}` of `LinearFTMP`, whose derivative is
  `LinearFTMP.linear_217`); `equilibrium_debt_218` ((2.18) in every equilibrium).
-/

namespace Cochrane.IntertemporalModel.GeneralLinks

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values -/

/-- Cochrane (2023), eq. (2.7), p. 22: the two forms of the present value agree,
`E_t ∑_j βʲ s_{t+j} = ∑_j βʲ E_t s_{t+j}`, under conditional monotone convergence when the
ex-post discounted sum converges absolutely in every state (signed surpluses: split into
positive and negative parts). -/
theorem fm_pv_eq_pv (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    {t : ℕ} (hex : ∀ ω, Summable fun j => β ^ j * |s (t + j) ω|) :
    FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t := by
  funext ω
  set sp : ℕ → Ω → ℝ := fun n ω => max (s n ω) 0 with hsp
  set sn : ℕ → Ω → ℝ := fun n ω => max (-s n ω) 0 with hsn
  have hsplit : ∀ n, s n = sp n - sn n := fun n => by
    funext ω
    simp [hsp, hsn, max_zero_sub_max_neg_zero_eq_self]
  have hpart : ∀ r : ℕ → Ω → ℝ, (∀ n ω, 0 ≤ r n ω) → (∀ n ω, r n ω ≤ |s n ω|) →
      (∀ ω', Summable fun j => β ^ j * r (t + j) ω') ∧
      HasSum (fun j => β ^ j * 𝔼.E t (r (t + j)) ω)
        (𝔼.E t (fun ω' => ∑' j, β ^ j * r (t + j) ω') ω) := by
    intro r hr0 hrs
    have hf0 : ∀ k ω', 0 ≤ β ^ k * r (t + k) ω' := fun k ω' =>
      mul_nonneg (pow_nonneg hβ k) (hr0 _ _)
    have hfs : ∀ ω', Summable fun k => β ^ k * r (t + k) ω' := fun ω' =>
      Summable.of_nonneg_of_le (fun k => hf0 k ω')
        (fun k => mul_le_mul_of_nonneg_left (hrs _ _) (pow_nonneg hβ k)) (hex ω')
    refine ⟨hfs, (hMC t (fun k ω' => β ^ k * r (t + k) ω') hf0 hfs ω).congr_fun fun j => ?_⟩
    change β ^ j * 𝔼.E t (r (t + j)) ω = 𝔼.E t (β ^ j • r (t + j)) ω
    rw [map_smul]
    rfl
  have hp := hpart sp (fun n ω => le_max_right _ _)
    (fun n ω => max_le (le_abs_self _) (abs_nonneg _))
  have hn := hpart sn (fun n ω => le_max_right _ _)
    (fun n ω => max_le (neg_le_abs _) (abs_nonneg _))
  have hepv : FiscalMonetary.epv β s t = (fun ω' => ∑' j, β ^ j * sp (t + j) ω') -
      (fun ω' => ∑' j, β ^ j * sn (t + j) ω') := by
    funext ω'
    simp only [FiscalMonetary.epv, Pi.sub_apply]
    rw [← (hp.1 ω').tsum_sub (hn.1 ω')]
    refine tsum_congr fun j => ?_
    rw [hsplit (t + j), Pi.sub_apply]
    ring
  change 𝔼.E t (FiscalMonetary.epv β s t) ω = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω
  rw [hepv, map_sub, Pi.sub_apply, ← hp.2.tsum_eq, ← hn.2.tsum_eq,
    ← hp.2.summable.tsum_sub hn.2.summable]
  refine tsum_congr fun j => ?_
  rw [hsplit (t + j), map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (2.7), p. 22: for bounded surpluses and `0 ≤ β < 1` the two forms of
the present value agree for every expectation system (no monotone convergence needed). -/
theorem fm_pv_eq_pv_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t :=
  funext fun ω => FiscalMonetary.E_epv_tsum (𝔼 := 𝔼) hβ0 hβ1 hs t t ω

/-! ### The two equilibrium notions -/

/-- Cochrane (2023), §2.1, p. 21 (timing): the nominal debt maturing at each date, `B_{−1}` at
date `0` and `B_t` at date `t + 1`, built from the initial debt and the debt sold. This is the
`Bm` of `Environment`/`Valuation` (`Bm t = B_{t−1}`) for the `B` of `FiscalMonetary`. -/
def debtPath (Bm1 : Ω → ℝ) (B : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 => B t

/-- Cochrane (2023), §2.1–§2.4, pp. 21–33: the equilibrium of `FiscalMonetary` (valuation
equation (2.7)/(2.12) at every date plus the bond-pricing condition (2.3)) is exactly the
equilibrium of `Valuation` (positive adapted price level, bond price (2.3), flow condition
(2.4) and transversality condition (2.6) at every date), with maturing debt
`debtPath B_{−1} B` and bond price `Q_t = 1/(1 + i_t)`. Hypotheses: pull-out, conditional
monotone convergence, `β ≥ 0`, adapted surpluses that are absolutely summable both in
expectation and ex post, adapted debt sold and an adapted rate `i > −1`. So the results of
`FiscalMonetary` and `FlatSupply` are about the equilibria derived from flow plus TVC. -/
theorem equilibrium_iff_isEqm (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBa : 𝔼.Adapted B) (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i ↔
      Valuation.IsEqm 𝔼 β (debtPath Bm1 B) s P (fun t => (1 + i t)⁻¹) := by
  have hpv : ∀ t, FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t := fun t =>
    fm_pv_eq_pv 𝔼 hMC hβ (hex t)
  have hB1 : ∀ t, 𝔼.E t (debtPath Bm1 B (t + 1)) = debtPath Bm1 B (t + 1) := hBa
  constructor
  · rintro ⟨hPa, hPpos, -, -, -, ⟨hv0, hv⟩, hbp⟩
    have hx : ∀ t, (fun ω => debtPath Bm1 B t ω / P t ω) = Valuation.pv 𝔼 β s t := by
      intro t
      cases t with
      | zero => exact hv0.trans (hpv 0)
      | succ t => exact (hv t).trans (hpv (t + 1))
    obtain ⟨hflow, htvc⟩ := (Valuation.valuation_iff 𝔼 hMC hβ hs hsad).mpr hx
    refine ⟨hPpos, hPa, hbp, fun t ω => ?_, htvc⟩
    exact (Environment.flow_iff_real_x 𝔼 hPO (Q := fun t => (1 + i t)⁻¹) (hPpos t) (hPa t)
      (hB1 t) (hbp t)).mpr (hflow t) ω
  · intro h
    have hx := Valuation.eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h
    exact ⟨h.2.1, h.1, hBa, hia, hi, ⟨(hx 0).trans (hpv 0).symm,
      fun t => (hx (t + 1)).trans (hpv (t + 1)).symm⟩, h.2.2.1⟩

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds", for the
equilibria of `FiscalMonetary`: under the hypotheses of `equilibrium_iff_isEqm` and positive
debt, the price level is `Valuation.eqmPrice`, `P_t = B_{t−1}/pv_t`. -/
theorem equilibrium_price_eq_eqmPrice (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼)
    {β : ℝ} (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}
    (hs : Valuation.AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|) (hBa : 𝔼.Adapted B)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hBpos : ∀ t ω, 0 < debtPath Bm1 B t ω)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) :
    P = Valuation.eqmPrice 𝔼 β (debtPath Bm1 B) s := by
  have hA := (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hBa hia hi).mp h
  funext t ω
  exact Valuation.eqm_price_eq 𝔼 hPO hMC hβ hs hsad (Bm := debtPath Bm1 B) hBa hA
    (hBpos t ω).ne'

/-- Cochrane (2023), pp. 31–33, in the language of `Valuation`: for every adapted
interest-rate target `i > −1` (with positive initial debt and positive present values) there is
exactly one pair (price level, debt sold) such that the debt is adapted and the economy with
maturing debt `debtPath B_{−1} B` and bond price `1/(1 + i)` is an equilibrium derived from
flow plus transversality. -/
theorem peg_existsUnique_isEqm (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < FiscalMonetary.pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < FiscalMonetary.pvEx 𝔼 β s t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted x.2 ∧
      Valuation.IsEqm 𝔼 β (debtPath Bm1 x.2) s x.1 (fun t => (1 + i t)⁻¹) := by
  obtain ⟨x, hx, hu⟩ := FiscalMonetary.peg_existsUnique hPO hBm1 hB hia hi hpv hpvEx
  refine ⟨x, ⟨hx.2.2.1, (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hx.2.2.1 hia hi).mp hx⟩,
    fun y hy => hu y ?_⟩
  exact (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hy.1 hia hi).mpr hy.2

/-- Cochrane (2023), eqs. (2.11) and (2.14)–(2.15), pp. 27, 31: in every equilibrium of
`FiscalMonetary` the real revenue from bond sales `(B_t/P_t)/(1 + i_t)` is the convergent series
`∑_{j≥0} β^{j+1} E_t s_{t+1+j}` of `EquilibriumFormation.eqm_realRevenue`. -/
theorem equilibrium_realRevenue (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBa : 𝔼.Adapted B) (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      ((B t / P t * (1 + i t)⁻¹) ω) := by
  have hA := (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hBa hia hi).mp h
  have hr := EquilibriumFormation.eqm_realRevenue 𝔼 hPO hMC hβ hs hsad
    (Bm := debtPath Bm1 B) hBa hA t ω
  convert hr using 1
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply, debtPath]
  ring

/-- Cochrane (2023), §2.9, p. 48: the nominal debt maturing at each date in the two-step process
(central bank sets `i`, Treasury follows its rule) is the maturing-debt path `Bm` of
`Valuation` built from the debt sold on the flat supply curve. -/
theorem twoStep_eq_debtPath {β : ℝ} {Bm1 : Ω → ℝ} {s i : ℕ → Ω → ℝ}
    (hs : FiscalMonetary.SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, FiscalMonetary.pv 𝔼 β s t ω ≠ 0) :
    FlatSupply.twoStep 𝔼 β Bm1 s i = debtPath Bm1 (FiscalMonetary.pegB 𝔼 β Bm1 s i) := by
  funext t
  cases t with
  | zero => rfl
  | succ t => exact FlatSupply.twoStep_debt_eq_pegB hs hsa hpv t

/-! ### Bond pricing, the exact Fisher equation and the peg equilibria -/

/-- Cochrane (2023), eqs. (2.3) and (2.16), pp. 22, 35: the bond-pricing condition of
`FiscalMonetary` is the exact Fisher equation of `LinearFTMP` at every date. -/
theorem bondPricing_iff_fisherExact {β : ℝ} {P i : ℕ → Ω → ℝ} :
    FiscalMonetary.BondPricing 𝔼 β P i ↔ ∀ t, LinearFTMP.FisherExact 𝔼 β i P t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.inv_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, one_div]
  exact Iff.rfl

/-- Cochrane (2023), pp. 22, 33: the peg equilibrium `Links.PegEqm` of chain C, with the present
value `FiscalMonetary.pv` and a constant initial debt, is exactly `FiscalMonetary.Equilibrium`
(for an adapted target `i > −1`). -/
theorem equilibrium_iff_pegEqm {β Bm1 : ℝ} {s B P i : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) :
    FiscalMonetary.Equilibrium 𝔼 β (fun _ => Bm1) s B P i ↔
      Links.PegEqm 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 P B := by
  constructor
  · rintro ⟨hPa, hPpos, hBa, -, -, ⟨hv0, hv⟩, hbp⟩
    exact ⟨hPa, hBa, hPpos, (bondPricing_iff_fisherExact 𝔼).mp hbp,
      fun ω => congrFun hv0 ω, fun t ω => congrFun (hv t) ω⟩
  · rintro ⟨hPa, hBa, hPpos, hfis, hv0, hv⟩
    exact ⟨hPa, hPpos, hBa, hia, hi, ⟨funext hv0, fun t => funext (hv t)⟩,
      (bondPricing_iff_fisherExact 𝔼).mpr hfis⟩

/-- Cochrane (2023), p. 33: the peg price path constructed in `Links` (`ftplPrice`, from the
exact Fisher equation and the valuation equation) is the peg price path of `FiscalMonetary`
(`pegP`) when the present value is `FiscalMonetary.pv`. No hypotheses are needed. -/
theorem ftplPrice_eq_pegP (β Bm1 : ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t =
      FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext ω
    have e := congrFun (FiscalMonetary.pvEx_eq 𝔼 β s t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    change β * (1 + i t ω) * (Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t ω *
        𝔼.E t (FiscalMonetary.pv 𝔼 β s (t + 1)) ω) / FiscalMonetary.pv 𝔼 β s (t + 1) ω =
      (1 + i t ω) * FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t ω *
        FiscalMonetary.pvEx 𝔼 β s t ω / FiscalMonetary.pv 𝔼 β s (t + 1) ω
    rw [ih, e]
    ring

/-- Cochrane (2023), p. 33: the peg debt of `Links` (`ftplDebt`) is the peg debt of
`FiscalMonetary` (`pegB`) when the present value is `FiscalMonetary.pv`. -/
theorem ftplDebt_eq_pegB (β Bm1 : ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    Links.ftplDebt 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t =
      FiscalMonetary.pegB 𝔼 β (fun _ => Bm1) s i t := by
  funext ω
  have e := congrFun (FiscalMonetary.pvEx_eq 𝔼 β s t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  change β * (1 + i t ω) * (Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t ω *
      𝔼.E t (FiscalMonetary.pv 𝔼 β s (t + 1)) ω) =
    (1 + i t ω) * FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t ω *
      FiscalMonetary.pvEx 𝔼 β s t ω
  rw [ftplPrice_eq_pegP, e]
  ring

/-! ### The linear model as the derivative of the nonlinear model -/

/-- Cochrane (2023), eqs. (2.3) and (2.16), pp. 22, 35: every equilibrium derived in
`Valuation` satisfies the exact Fisher equation of `LinearFTMP` with the nominal rate
`i_t = 1/Q_t − 1` (`Environment.rate`). -/
theorem isEqm_fisherExact {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} (h : Valuation.IsEqm 𝔼 β Bm s P Q)
    (t : ℕ) : LinearFTMP.FisherExact 𝔼 β (Environment.rate Q) P t := by
  intro ω
  rw [one_div, ← Environment.bondPrice_eq_inv_one_add_rate, h.2.2.1 t]
  rfl

/-- Cochrane (2023), eq. (2.16), p. 35: in every equilibrium derived in `Valuation` with
positive bond prices, the exact Fisher equation holds in logs,
`log(1 + i_t) = −log β − log E_t[exp(−π_{t+1})]`; `LinearFTMP.fisher_deriv` shows that its
derivative at the steady state is the linear (2.16), `i_t = r + E_t π_{t+1}`. -/
theorem isEqm_fisher_log {β : ℝ} (hβ : 0 < β) {Bm s P Q : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P Q) (hQ : ∀ t ω, 0 < Q t ω) (t : ℕ) (ω : Ω) :
    Real.log (1 + Environment.rate Q t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have hi : ∀ ω, 0 < 1 + Environment.rate Q t ω := fun ω => by
    simp only [Environment.rate]
    linarith [inv_pos.mpr (hQ t ω)]
  have hE : ∀ ω, 0 < 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω := fun ω => by
    have e := congrFun (h.2.2.1 t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hβ.le hc
    linarith [hQ t ω]
  exact (LinearFTMP.fisher_log_form 𝔼 hβ h.1 hi hE).mp (isEqm_fisherExact 𝔼 h t) ω

/-- Cochrane (2023), pp. 35, 43: for bounded surpluses the ex-post fiscal news of
`FiscalMonetary`, `ΔE_{t+1} ∑ βʲ s_{t+1+j}`, is the fiscal shock `ε_{Σs,t+1}` of `LinearFTMP`. -/
theorem innov_epv_eq_pvNews {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    innov 𝔼 t (FiscalMonetary.epv β s (t + 1)) = LinearFTMP.pvNews 𝔼 β s t :=
  funext fun ω => FiscalMonetary.news_epv_tsum hβ0 hβ1 hs t ω

/-- Cochrane (2023), eqs. (2.13) and (2.17), pp. 30, 35: in every equilibrium of
`FiscalMonetary` with bounded surpluses, the exact unexpected-inflation identity is the exact
(2.17) of `LinearFTMP` (`unexpected_inflation_exact` with `PV = Valuation.pv`), with the fiscal
shock `ε_{Σs,t+1}`: `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ε_{Σs,t+1}`. Its derivative along a
family of equilibria is the linear (2.17), `LinearFTMP.linear_217`. -/
theorem equilibrium_pvNews (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω) * innov 𝔼 t (fun ω => P t ω / P (t + 1) ω) =
      LinearFTMP.pvNews 𝔼 β s t := by
  rw [LinearFTMP.unexpected_inflation_exact 𝔼 hPO (PV := Valuation.pv 𝔼 β s)
    (fun ω => (h.2.1 t ω).ne') (FiscalMonetary.realDebt_known hPO h t)
    ((h.2.2.2.2.2.1.2 t).trans (fm_pv_eq_pv_of_bounded 𝔼 hβ0 hβ1 hs (t + 1)))]
  exact LinearFTMP.innov_forwardSeries 𝔼 hβ0 hβ1 hs t

/-- Cochrane (2023), eq. (2.18), p. 35: in every equilibrium of `FiscalMonetary` with bounded
surpluses, `(B_t/P_t)/(1 + i_t) = ∑_{k≥0} β^{k+1} E_t s_{t+1+k}` (`LinearFTMP.debt_218`). -/
theorem equilibrium_debt_218 (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω / P t ω * (1 / (1 + i t ω)) = ∑' k, β ^ (k + 1) * 𝔼.E t (s (t + 1 + k)) ω :=
  LinearFTMP.debt_218 𝔼 hPO hβ0 hβ1 hs (fun ω => (h.2.1 t ω).ne')
    ((bondPricing_iff_fisherExact 𝔼).mp h.2.2.2.2.2.2 t) (FiscalMonetary.realDebt_known hPO h t)
    ((h.2.2.2.2.2.1.2 t).trans (fm_pv_eq_pv_of_bounded 𝔼 hβ0 hβ1 hs (t + 1))) ω

end Cochrane.IntertemporalModel.GeneralLinks

set_option linter.style.longLine false
#print axioms Cochrane.IntertemporalModel.SchurStable
#print axioms Cochrane.IntertemporalModel.disc
#print axioms Cochrane.IntertemporalModel.root₁
#print axioms Cochrane.IntertemporalModel.root₂
#print axioms Cochrane.IntertemporalModel.root_sum
#print axioms Cochrane.IntertemporalModel.root_prod
#print axioms Cochrane.IntertemporalModel.root_eq
#print axioms Cochrane.IntertemporalModel.normSq_root_of_neg
#print axioms Cochrane.IntertemporalModel.norm_root_of_nonneg
#print axioms Cochrane.IntertemporalModel.schurStable_iff_roots
#print axioms Cochrane.IntertemporalModel.chSeq
#print axioms Cochrane.IntertemporalModel.convSeq
#print axioms Cochrane.IntertemporalModel.convSeq_rec
#print axioms Cochrane.IntertemporalModel.chSeq_eq_convSeq
#print axioms Cochrane.IntertemporalModel.norm_convSeq_le
#print axioms Cochrane.IntertemporalModel.abs_chSeq_le
#print axioms Cochrane.IntertemporalModel.tendsto_chSeq
#print axioms Cochrane.IntertemporalModel.tr2
#print axioms Cochrane.IntertemporalModel.det2
#print axioms Cochrane.IntertemporalModel.tr2_eq_trace
#print axioms Cochrane.IntertemporalModel.det2_eq_det
#print axioms Cochrane.IntertemporalModel.sq_eq_cayleyHamilton
#print axioms Cochrane.IntertemporalModel.pow_succ_eq
#print axioms Cochrane.IntertemporalModel.abs_pow_entry_le
#print axioms Cochrane.IntertemporalModel.tendsto_pow_entry
#print axioms Cochrane.IntertemporalModel.BoundedSeq
#print axioms Cochrane.IntertemporalModel.homogeneous_iterate
#print axioms Cochrane.IntertemporalModel.abs_mulVec_le
#print axioms Cochrane.IntertemporalModel.homogeneous_eq_zero
#print axioms Cochrane.IntertemporalModel.eq_root_of_eq
#print axioms Cochrane.IntertemporalModel.exists_eigenvector
#print axioms Cochrane.IntertemporalModel.exists_bounded_homogeneous
#print axioms Cochrane.IntertemporalModel.ExpectationSystem
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.mk
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.E
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.const
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.mono
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.tower
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.known
#print axioms Cochrane.IntertemporalModel.perfectForesight
#print axioms Cochrane.IntertemporalModel.BoundedProc
#print axioms Cochrane.IntertemporalModel.BoundedVec
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.Adapted
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.IsAR1
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.E_neg
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.E_smul
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.E_E_self
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.abs_E_le
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.bounded_E
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.ar1_iterate
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forward_iterate
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forward_unique
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.E_tsum
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forwardSeries
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.PullOut
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.Solves
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.AdaptedVec
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.system_iterate
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.system_unique
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.system_not_unique
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.Determinate
#print axioms Cochrane.IntertemporalModel.ExpectationSystem.determinate_iff
#print axioms Cochrane.IntertemporalModel.perfectForesight_pullOut
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.IntertemporalModel.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.IntertemporalModel.ForwardSolution.Solves
#print axioms Cochrane.IntertemporalModel.ForwardSolution.E_of_known
#print axioms Cochrane.IntertemporalModel.ForwardSolution.solves_adapted
#print axioms Cochrane.IntertemporalModel.ForwardSolution.iterate_A15
#print axioms Cochrane.IntertemporalModel.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.IntertemporalModel.ForwardSolution.summable_A16
#print axioms Cochrane.IntertemporalModel.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.IntertemporalModel.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.IntertemporalModel.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.IntertemporalModel.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.IntertemporalModel.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.IntertemporalModel.ForwardSolution.ScalarEq
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalarSol
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalarSol_apply
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalarEq_iff
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalar_homog
#print axioms Cochrane.IntertemporalModel.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sunspotFamily
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.IntertemporalModel.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.IntertemporalModel.ForwardSolution.homog_solves
#print axioms Cochrane.IntertemporalModel.ForwardSolution.solves_add_homog
#print axioms Cochrane.IntertemporalModel.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.IntertemporalModel.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.IntertemporalModel.ForwardSolution.existsUnique_iff
#print axioms Cochrane.IntertemporalModel.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.IntertemporalModel.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.IntertemporalModel.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.IntertemporalModel.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.IntertemporalModel.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.IntertemporalModel.ForwardSolution.ar1_decay
#print axioms Cochrane.IntertemporalModel.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.IntertemporalModel.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.IntertemporalModel.ForwardSolution.predetermined_restriction
#print axioms Cochrane.IntertemporalModel.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.IntertemporalModel.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.IntertemporalModel.ForwardSolution.summable_geom_mul
#print axioms Cochrane.IntertemporalModel.ForwardSolution.abel_tsum
#print axioms Cochrane.IntertemporalModel.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.IntertemporalModel.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.IntertemporalModel.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.IntertemporalModel.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.IntertemporalModel.ForwardSolution.E_tsum_dom
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_add
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_sub
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_smul
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_neg
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_const
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_of_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_innov_zero
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_innov_zero_of_le
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_known_next
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_E_succ
#print axioms Cochrane.IntertemporalModel.ExpectationTools.innov_mul_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.eq_E_add_innov
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_mul_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_inv_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_div_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_one_add_known
#print axioms Cochrane.IntertemporalModel.ExpectationTools.FunctionsKnown
#print axioms Cochrane.IntertemporalModel.ExpectationTools.perfectForesight_functionsKnown
#print axioms Cochrane.IntertemporalModel.ExpectationTools.finiteTree_functionsKnown
#print axioms Cochrane.IntertemporalModel.ExpectationTools.known_div
#print axioms Cochrane.IntertemporalModel.ExpectationTools.Closed
#print axioms Cochrane.IntertemporalModel.ExpectationTools.perfectForesight_closed
#print axioms Cochrane.IntertemporalModel.ExpectationTools.finiteTree_closed
#print axioms Cochrane.IntertemporalModel.ExpectationTools.functionsKnown_of_closed
#print axioms Cochrane.IntertemporalModel.ExpectationTools.MonotoneConvergence
#print axioms Cochrane.IntertemporalModel.ExpectationTools.perfectForesight_monotoneConvergence
#print axioms Cochrane.IntertemporalModel.ExpectationTools.finiteTree_monotoneConvergence
#print axioms Cochrane.IntertemporalModel.ExpectationTools.const_le_E
#print axioms Cochrane.IntertemporalModel.ExpectationTools.E_nonneg
#print axioms Cochrane.IntertemporalModel.ExpectationTools.abs_E_le_E_abs
#print axioms Cochrane.IntertemporalModel.ExpectationTools.summable_E_shift
#print axioms Cochrane.IntertemporalModel.Environment.GovFlow
#print axioms Cochrane.IntertemporalModel.Environment.HhFlow
#print axioms Cochrane.IntertemporalModel.Environment.hhFlow_iff_govFlow
#print axioms Cochrane.IntertemporalModel.Environment.hhFlow_sub_govFlow
#print axioms Cochrane.IntertemporalModel.Environment.HhFeasible
#print axioms Cochrane.IntertemporalModel.Environment.HhOptimal
#print axioms Cochrane.IntertemporalModel.Environment.euler_of_optimal
#print axioms Cochrane.IntertemporalModel.Environment.bondPrice_of_optimal
#print axioms Cochrane.IntertemporalModel.Environment.EulerNominal
#print axioms Cochrane.IntertemporalModel.Environment.EulerReal
#print axioms Cochrane.IntertemporalModel.Environment.realBondPrice_of_euler
#print axioms Cochrane.IntertemporalModel.Environment.realRate_eq_inv_beta
#print axioms Cochrane.IntertemporalModel.Environment.bondPrice_of_euler
#print axioms Cochrane.IntertemporalModel.Environment.bondPrice_iff_euler
#print axioms Cochrane.IntertemporalModel.Environment.rate
#print axioms Cochrane.IntertemporalModel.Environment.bondPrice_eq_inv_one_add_rate
#print axioms Cochrane.IntertemporalModel.Environment.inv_one_add_rate_eq
#print axioms Cochrane.IntertemporalModel.Environment.rate_pos_iff
#print axioms Cochrane.IntertemporalModel.Environment.rate_neg_iff
#print axioms Cochrane.IntertemporalModel.Environment.money_dominated
#print axioms Cochrane.IntertemporalModel.Environment.bonds_dominated_of_neg_rate
#print axioms Cochrane.IntertemporalModel.Environment.perfect_substitutes
#print axioms Cochrane.IntertemporalModel.Environment.flow_of_govFlow
#print axioms Cochrane.IntertemporalModel.Environment.govFlow_merge
#print axioms Cochrane.IntertemporalModel.Environment.flow_real_25
#print axioms Cochrane.IntertemporalModel.Environment.flow_real_x
#print axioms Cochrane.IntertemporalModel.Environment.flow_iff_real_x
#print axioms Cochrane.IntertemporalModel.Environment.propTax_real_surplus
#print axioms Cochrane.IntertemporalModel.Environment.propTax_surplus_indep_price
#print axioms Cochrane.IntertemporalModel.Valuation.FlowX
#print axioms Cochrane.IntertemporalModel.Valuation.TVC
#print axioms Cochrane.IntertemporalModel.Valuation.TVCBook
#print axioms Cochrane.IntertemporalModel.Valuation.tvc_iff_tvcBook
#print axioms Cochrane.IntertemporalModel.Valuation.AbsSummable
#print axioms Cochrane.IntertemporalModel.Valuation.pv
#print axioms Cochrane.IntertemporalModel.Valuation.pv_apply
#print axioms Cochrane.IntertemporalModel.Valuation.summable_terms
#print axioms Cochrane.IntertemporalModel.Valuation.adapted_of_flow
#print axioms Cochrane.IntertemporalModel.Valuation.telescope
#print axioms Cochrane.IntertemporalModel.Valuation.hasSum_of_flow_tvc
#print axioms Cochrane.IntertemporalModel.Valuation.hasSum_E_pv
#print axioms Cochrane.IntertemporalModel.Valuation.E_pv_self
#print axioms Cochrane.IntertemporalModel.Valuation.pv_flow
#print axioms Cochrane.IntertemporalModel.Valuation.pv_tvc
#print axioms Cochrane.IntertemporalModel.Valuation.valuation_iff
#print axioms Cochrane.IntertemporalModel.Valuation.IsEqm
#print axioms Cochrane.IntertemporalModel.Valuation.eqm_realDebt_eq_pv
#print axioms Cochrane.IntertemporalModel.Valuation.eqm_price_eq
#print axioms Cochrane.IntertemporalModel.Valuation.eqm_pv_pos
#print axioms Cochrane.IntertemporalModel.Valuation.no_eqm_of_pv_nonpos
#print axioms Cochrane.IntertemporalModel.Valuation.eqmPrice
#print axioms Cochrane.IntertemporalModel.Valuation.eqmBondPrice
#print axioms Cochrane.IntertemporalModel.Valuation.eqm_of_pv_pos
#print axioms Cochrane.IntertemporalModel.Valuation.existsUnique_eqm
#print axioms Cochrane.IntertemporalModel.Valuation.hh_flow_iff_real
#print axioms Cochrane.IntertemporalModel.Valuation.hh_pv_iff
#print axioms Cochrane.IntertemporalModel.Valuation.excess_demand_of_gap
#print axioms Cochrane.IntertemporalModel.Valuation.NoPonzi
#print axioms Cochrane.IntertemporalModel.Valuation.NoOverAccumulation
#print axioms Cochrane.IntertemporalModel.Valuation.tendsto_zero_iff_noPonzi_and_optimal
#print axioms Cochrane.IntertemporalModel.Valuation.tvc_iff_noPonzi_and_optimal
#print axioms Cochrane.IntertemporalModel.Valuation.noPonzi_of_nonneg_debt
#print axioms Cochrane.IntertemporalModel.Valuation.hh_iterate
#print axioms Cochrane.IntertemporalModel.Valuation.printed_A1_2_false
#print axioms Cochrane.IntertemporalModel.Valuation.const_explodes
#print axioms Cochrane.IntertemporalModel.Valuation.const_terminal_limit
#print axioms Cochrane.IntertemporalModel.Valuation.const_tvc_iff
#print axioms Cochrane.IntertemporalModel.Valuation.const_valuation_limit
#print axioms Cochrane.IntertemporalModel.Valuation.deviation_closed_form
#print axioms Cochrane.IntertemporalModel.Valuation.deviation_feasible
#print axioms Cochrane.IntertemporalModel.Valuation.deviation_improves
#print axioms Cochrane.IntertemporalModel.Valuation.deviation_optimal
#print axioms Cochrane.IntertemporalModel.Valuation.concave_le_tangent
#print axioms Cochrane.IntertemporalModel.Valuation.deriv_nonneg_of_monotone
#print axioms Cochrane.IntertemporalModel.Valuation.deviation_optimal_concave
#print axioms Cochrane.IntertemporalModel.Valuation.tooLow_not_equilibrium
#print axioms Cochrane.IntertemporalModel.Valuation.optimal_plan_tvc
#print axioms Cochrane.IntertemporalModel.Valuation.tvc_of_optimal
#print axioms Cochrane.IntertemporalModel.Valuation.valuation_of_optimal
#print axioms Cochrane.IntertemporalModel.Valuation.bubble_deviation
#print axioms Cochrane.IntertemporalModel.Valuation.E_eq_sum
#print axioms Cochrane.IntertemporalModel.Valuation.E_tendsto
#print axioms Cochrane.IntertemporalModel.Valuation.hasDerivAt_E
#print axioms Cochrane.IntertemporalModel.Valuation.hasSum_of_eq_off_finset
#print axioms Cochrane.IntertemporalModel.Valuation.Faithful
#print axioms Cochrane.IntertemporalModel.Valuation.perfectForesight_faithful
#print axioms Cochrane.IntertemporalModel.Valuation.finiteTree_faithful
#print axioms Cochrane.IntertemporalModel.Valuation.InfoStable
#print axioms Cochrane.IntertemporalModel.Valuation.perfectForesight_infoStable
#print axioms Cochrane.IntertemporalModel.Valuation.finiteTree_infoStable
#print axioms Cochrane.IntertemporalModel.Valuation.SFeasible
#print axioms Cochrane.IntertemporalModel.Valuation.expUtil
#print axioms Cochrane.IntertemporalModel.Valuation.SOptimal
#print axioms Cochrane.IntertemporalModel.Valuation.euler_of_optimal_stoch
#print axioms Cochrane.IntertemporalModel.Valuation.tvc_of_optimal_stoch
#print axioms Cochrane.IntertemporalModel.Valuation.valuation_of_optimal_stoch
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.pv_eq_s_add_fwd
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.realRevenue_hasSum
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.eqm_realRevenue
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.deficit_financed_by_debt
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.soak_up_retired
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.no_rollover
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.flow_div_iff
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.passiveSurplus
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.passive_every_price_eqm
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.no_initial_debt_pv_zero
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.no_initial_debt_P0_free
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.no_initial_debt_not_unique
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.money_overhang_iff
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.money_zero_iff
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.money_negative_iff
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.iterate_with_terminal
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.iterate_with_terminal_limit
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.printed_p28_false
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.tooHigh_explodes_down
#print axioms Cochrane.IntertemporalModel.EquilibriumFormation.tooHigh_violates_nonneg_debt
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.epv
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pv
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pvEx
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.SurplusSummable
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.surplusSummable_of_zero
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.surplusSummable_of_bounded
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.exsum_eq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.epv_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pvEx_eq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pv_adapted
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pvEx_adapted
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pv_eq_add_pvEx
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pvEx_ge
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.E_pv_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.news_pv_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.Valuation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.BondPricing
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.Equilibrium
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.price_zero
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.price_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.realDebt_known
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.unexpected_inflation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.unexpected_inflation_eq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.no_surprise_iff
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.disinflation_iff
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.E_unexpected_inflation_zero
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.expected_inflation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.expected_valuation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.debt_eq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.eq_2_26
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.eq_2_26_zero
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.flow_nominal
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.eq_2_27
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.revenue_invariant
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.future_sales_irrelevant
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.shareSplit
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pegP
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pegB
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pegP_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pegP_pos
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.peg_equilibrium
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.peg_unique
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.peg_existsUnique
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.peg_expected_inflation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.inflation_decomposition
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.expected_inflation_indep_surplus
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.debt_ratio_of_rate
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.debt_growth_of_rate
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.rate_change_eq_debt_growth_iff
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.printed_one_percent_fails
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.real_rate_forced
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.no_eqm_real_rate_peg
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.real_rate_peg_unbounded
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.scaled_all_but_initial
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.scaled_not_initial
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pf_pricing_iff
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pf_price_formula
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pf_family
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.E_epv_tsum
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.news_epv_tsum
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.sShape_seq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.sShape
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.reform_with_deficits
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.equityIssue
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.equityIssue_finances_deficit
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_news
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_pv_news
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_unexpected_inflation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_printed_fails
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_value_news
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_value_falls
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.ar1_news_exceeds_deficit
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.consolidation_irrelevant
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.stimulus_no_jump
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.pf_stimulus_neutral
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.stimulus_price_iff
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.stimulus_unexpected_inflation
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.news_pv_add_known
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.fh
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.fh_nonneg
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.coin_E_first
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.coin_E_zero
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.sB
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.sS
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.epv_tail
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.sB_bounded
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.sS_bounded
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.epv_sB_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.epv_sS_add_two
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.epv_sS_one
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_zero_eq
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sB_succ
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sB_one
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sS_add_two
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sS_one
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sB_pos
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pv_sS_pos
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pvEx_sB_pos
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.pvEx_sS_pos
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.news_sB
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.news_sB_ne
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.coin_pullOut
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.eqm_sB
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.eqm_sS
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.stimulus_not_neutral
#print axioms Cochrane.IntertemporalModel.FiscalMonetary.CoinExample.coin_unexpected_inflation_ne
#print axioms Cochrane.IntertemporalModel.FlatSupply.eq_2_28
#print axioms Cochrane.IntertemporalModel.FlatSupply.eq_2_28_zero
#print axioms Cochrane.IntertemporalModel.FlatSupply.treasury_rule_iff
#print axioms Cochrane.IntertemporalModel.FlatSupply.treasury_rule_of_equilibrium
#print axioms Cochrane.IntertemporalModel.FlatSupply.treasury_rule_of_equilibrium_zero
#print axioms Cochrane.IntertemporalModel.FlatSupply.flat_supply_revenue
#print axioms Cochrane.IntertemporalModel.FlatSupply.flat_supply_meets_demand
#print axioms Cochrane.IntertemporalModel.FlatSupply.treasury_debt_ratio
#print axioms Cochrane.IntertemporalModel.FlatSupply.one_percent_price_fall
#print axioms Cochrane.IntertemporalModel.FlatSupply.one_percent_printed_fails
#print axioms Cochrane.IntertemporalModel.FlatSupply.twoStep
#print axioms Cochrane.IntertemporalModel.FlatSupply.twoStep_eq_pegP
#print axioms Cochrane.IntertemporalModel.FlatSupply.twoStep_debt_eq_pegB
#print axioms Cochrane.IntertemporalModel.FlatSupply.twoStep_equilibrium
#print axioms Cochrane.IntertemporalModel.LinearFTMP.FisherExact
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fisher_log_form
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fisher_pf_exact
#print axioms Cochrane.IntertemporalModel.LinearFTMP.hasDerivAt_E_exp
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fisher_deriv
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fisher_deriv_value
#print axioms Cochrane.IntertemporalModel.LinearFTMP.unexpected_inflation_exact
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pvNews
#print axioms Cochrane.IntertemporalModel.LinearFTMP.E_forwardSeries_succ
#print axioms Cochrane.IntertemporalModel.LinearFTMP.innov_forwardSeries
#print axioms Cochrane.IntertemporalModel.LinearFTMP.IsShock
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pvNews_isShock
#print axioms Cochrane.IntertemporalModel.LinearFTMP.debt_218
#print axioms Cochrane.IntertemporalModel.LinearFTMP.linear_217
#print axioms Cochrane.IntertemporalModel.LinearFTMP.PegModel
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pegModel_iff
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pegSol
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pegSol_adapted
#print axioms Cochrane.IntertemporalModel.LinearFTMP.peg_existsUnique
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pegSol_bounded
#print axioms Cochrane.IntertemporalModel.LinearFTMP.innov_shock_later
#print axioms Cochrane.IntertemporalModel.LinearFTMP.irf_peg_impact
#print axioms Cochrane.IntertemporalModel.LinearFTMP.irf_peg_later
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig21_rate
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig21_fiscal
#print axioms Cochrane.IntertemporalModel.LinearFTMP.expected_inflation_ahead
#print axioms Cochrane.IntertemporalModel.LinearFTMP.announcement_invariant
#print axioms Cochrane.IntertemporalModel.LinearFTMP.no_announcement_effect
#print axioms Cochrane.IntertemporalModel.LinearFTMP.long_run_fisher
#print axioms Cochrane.IntertemporalModel.LinearFTMP.innov_of_news
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pvNews_of_news
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig21_expected_fiscal
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pTarget_price
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pTarget_rate_lowers_price
#print axioms Cochrane.IntertemporalModel.LinearFTMP.pTarget_fiscal_contraction
#print axioms Cochrane.IntertemporalModel.LinearFTMP.loggerhead
#print axioms Cochrane.IntertemporalModel.LinearFTMP.innov_pi_eq_innov_p
#print axioms Cochrane.IntertemporalModel.LinearFTMP.printed_E6_false
#print axioms Cochrane.IntertemporalModel.LinearFTMP.passiveShock
#print axioms Cochrane.IntertemporalModel.LinearFTMP.passive_valuation_holds
#print axioms Cochrane.IntertemporalModel.LinearFTMP.passive_any_innovation
#print axioms Cochrane.IntertemporalModel.LinearFTMP.innov_shock
#print axioms Cochrane.IntertemporalModel.LinearFTMP.RuleModel
#print axioms Cochrane.IntertemporalModel.LinearFTMP.Disturbance
#print axioms Cochrane.IntertemporalModel.LinearFTMP.Eq224
#print axioms Cochrane.IntertemporalModel.LinearFTMP.ruleModel_iff
#print axioms Cochrane.IntertemporalModel.LinearFTMP.eq224_iff
#print axioms Cochrane.IntertemporalModel.LinearFTMP.ruleSol
#print axioms Cochrane.IntertemporalModel.LinearFTMP.ruleSol_adapted
#print axioms Cochrane.IntertemporalModel.LinearFTMP.rule_existsUnique
#print axioms Cochrane.IntertemporalModel.LinearFTMP.rule_eq_peg
#print axioms Cochrane.IntertemporalModel.LinearFTMP.ruleSol_bounded
#print axioms Cochrane.IntertemporalModel.LinearFTMP.ruleSol_unbounded
#print axioms Cochrane.IntertemporalModel.LinearFTMP.conv
#print axioms Cochrane.IntertemporalModel.LinearFTMP.conv_eq
#print axioms Cochrane.IntertemporalModel.LinearFTMP.irf_disturbance
#print axioms Cochrane.IntertemporalModel.LinearFTMP.irf_rule
#print axioms Cochrane.IntertemporalModel.LinearFTMP.irf_rule_rate
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig22_monetary
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig22_fiscal
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fiscal_sets_impact
#print axioms Cochrane.IntertemporalModel.LinearFTMP.one_time_price_jump
#print axioms Cochrane.IntertemporalModel.LinearFTMP.price_level_returns
#print axioms Cochrane.IntertemporalModel.LinearFTMP.hump_step
#print axioms Cochrane.IntertemporalModel.LinearFTMP.hump_up
#print axioms Cochrane.IntertemporalModel.LinearFTMP.hump_down
#print axioms Cochrane.IntertemporalModel.LinearFTMP.hump_exists
#print axioms Cochrane.IntertemporalModel.LinearFTMP.fig22_peak
#print axioms Cochrane.IntertemporalModel.Links.FisherExactW
#print axioms Cochrane.IntertemporalModel.Links.fisher_iff_W
#print axioms Cochrane.IntertemporalModel.Links.Kexp
#print axioms Cochrane.IntertemporalModel.Links.grossInfl
#print axioms Cochrane.IntertemporalModel.Links.sunspotPrice
#print axioms Cochrane.IntertemporalModel.Links.Kexp_ge
#print axioms Cochrane.IntertemporalModel.Links.grossInfl_pos
#print axioms Cochrane.IntertemporalModel.Links.sunspotPrice_pos
#print axioms Cochrane.IntertemporalModel.Links.sunspot_fisher
#print axioms Cochrane.IntertemporalModel.Links.sunspotPrice_injective
#print axioms Cochrane.IntertemporalModel.Links.prop_2_5_uncountable
#print axioms Cochrane.IntertemporalModel.Links.PegEqm
#print axioms Cochrane.IntertemporalModel.Links.pegEqm_debt
#print axioms Cochrane.IntertemporalModel.Links.ftplPrice
#print axioms Cochrane.IntertemporalModel.Links.ftplDebt
#print axioms Cochrane.IntertemporalModel.Links.peg_ftpl_existsUnique
#print axioms Cochrane.IntertemporalModel.Links.pv_const
#print axioms Cochrane.IntertemporalModel.Links.peg_contrast
#print axioms Cochrane.IntertemporalModel.Links.Eq26
#print axioms Cochrane.IntertemporalModel.Links.eq26_iff_solves
#print axioms Cochrane.IntertemporalModel.Links.prop_2_6_iff
#print axioms Cochrane.IntertemporalModel.Links.sunspotInfl
#print axioms Cochrane.IntertemporalModel.Links.sunspotInfl_solves
#print axioms Cochrane.IntertemporalModel.Links.sunspotInfl_bounded
#print axioms Cochrane.IntertemporalModel.Links.eq26_iff_224
#print axioms Cochrane.IntertemporalModel.Links.rule_solves_eq26
#print axioms Cochrane.IntertemporalModel.Links.taylor_contrast
#print axioms Cochrane.IntertemporalModel.Links.taylor_contrast_coin
#print axioms Cochrane.IntertemporalModel.Links.discount
#print axioms Cochrane.IntertemporalModel.Links.ricardian_step
#print axioms Cochrane.IntertemporalModel.Links.ricardian_discounted
#print axioms Cochrane.IntertemporalModel.Links.ricardian_tvc
#print axioms Cochrane.IntertemporalModel.Links.pv_telescope
#print axioms Cochrane.IntertemporalModel.Links.passive_any_price
#print axioms Cochrane.IntertemporalModel.Links.active_unique_value
#print axioms Cochrane.IntertemporalModel.Links.active_tvc_fails
#print axioms Cochrane.IntertemporalModel.Links.Budget
#print axioms Cochrane.IntertemporalModel.Links.timing_link
#print axioms Cochrane.IntertemporalModel.Links.timing_real
#print axioms Cochrane.IntertemporalModel.GeneralLinks.fm_pv_eq_pv
#print axioms Cochrane.IntertemporalModel.GeneralLinks.fm_pv_eq_pv_of_bounded
#print axioms Cochrane.IntertemporalModel.GeneralLinks.debtPath
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_iff_isEqm
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_price_eq_eqmPrice
#print axioms Cochrane.IntertemporalModel.GeneralLinks.peg_existsUnique_isEqm
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_realRevenue
#print axioms Cochrane.IntertemporalModel.GeneralLinks.twoStep_eq_debtPath
#print axioms Cochrane.IntertemporalModel.GeneralLinks.bondPricing_iff_fisherExact
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_iff_pegEqm
#print axioms Cochrane.IntertemporalModel.GeneralLinks.ftplPrice_eq_pegP
#print axioms Cochrane.IntertemporalModel.GeneralLinks.ftplDebt_eq_pegB
#print axioms Cochrane.IntertemporalModel.GeneralLinks.isEqm_fisherExact
#print axioms Cochrane.IntertemporalModel.GeneralLinks.isEqm_fisher_log
#print axioms Cochrane.IntertemporalModel.GeneralLinks.innov_epv_eq_pvNews
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_pvNews
#print axioms Cochrane.IntertemporalModel.GeneralLinks.equilibrium_debt_218
