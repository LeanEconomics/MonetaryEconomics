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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
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

namespace Cochrane.LongTermDebtDynamics

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

end Cochrane.LongTermDebtDynamics

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

namespace Cochrane.LongTermDebtDynamics

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

end Cochrane.LongTermDebtDynamics

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

namespace Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree

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

end Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree

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

namespace Cochrane.LongTermDebtDynamics.ForwardSolution

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

end Cochrane.LongTermDebtDynamics.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maturity structure: flow and present-value relations with long-term debt

Cochrane (2023), Chapter 7, pp. 212–213 and 216 (equations (3.2), (3.3) recalled, and (7.1),
(7.2), (7.4), (7.5)).

Flexible prices, a constant real rate `1/β`, risk-neutral bond prices
`Q_t^{(t+j)} = β^j E_t(P_t / P_{t+j})`, and zero-coupon nominal debt of every maturity.

## Indexing

Dates are natural numbers. `D t m` is the face value of debt maturing at date `m` that is
outstanding at the *start* of date `t`, i.e. Cochrane's `B_{t−1}^{(m)}`. So Cochrane's inherited
maturity structure `B_{−1}^{(j)}` is `D 0 j`, his end-of-period-`t` debt `B_t^{(m)}` is
`D (t + 1) m`, and the sales at `t` of maturity-`m` debt are `B_t^{(m)} − B_{t−1}^{(m)} =
D (t + 1) m − D t m` (`sales`). As Cochrane recommends, the primitive price variable is
`x_t = 1/P_t`, so all systems are linear in `x`.

## Main results

* `bondPrice_eq`: `Q_t^{(t+j)} = β^j P_t E_t(1/P_{t+j})` (pull-out of `P_t`).
* `nominalFlow_iff_realFlow`: the nominal flow condition (3.2) is equivalent to the real flow
  condition (7.1)/(7.4) when `P_t > 0`.
* `nominalValue_eq`: the nominal market value of debt is `P_t` times the real value in (7.2).
* `realFlow_iff_recursion`: the flow condition at `t` is equivalent to the one-period
  recursion `V_t = s_t + β E_t V_{t+1}` for the real value of debt `V_t` (the left side of (7.2)).
* `debtValue_iterate`: `V_t = ∑_{k<N} β^k E_t s_{t+k} + β^N E_t V_{t+N}`.
* `presentValue_iff_tvc`: given the flow conditions, the present-value relation (7.2) at `t` is
  equivalent to the transversality condition `β^N E_t V_{t+N} → 0`.
* `flow_tvc_iff_presentValue`: the flow conditions at every date plus the transversality
  conditions are equivalent to the present-value relations (7.2)/(7.5) at every date.
* `presentValue_of_bounded`: with a bounded real value of debt the transversality condition
  holds automatically.
-/

namespace Cochrane.LongTermDebtDynamics.MaturityStructure

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 212: sales at date `t` of debt maturing at `m`,
`B_t^{(m)} − B_{t−1}^{(m)} = D (t + 1) m − D t m`. -/
def sales (D : ℕ → ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ := D (t + 1) m - D t m

/-- Cochrane (2023), p. 212: debt is predetermined. The inherited structure `B_{−1}^{(m)} = D 0 m`
is known at date 0 and the end-of-period stock `B_t^{(m)} = D (t + 1) m` is chosen at `t`. -/
def Predetermined (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ m, 𝔼.E 0 (D 0 m) = D 0 m) ∧ ∀ t m, 𝔼.E t (D (t + 1) m) = D (t + 1) m

/-- Cochrane (2023), p. 212: debt outstanding at the start of `t` is known at every date
`u ≥ t`. -/
theorem Predetermined.known {D : ℕ → ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t u : ℕ}
    (htu : t ≤ u) (m : ℕ) : 𝔼.E u (D t m) = D t m := by
  rcases t with _ | t
  · exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le u) (hD.1 m)
  · exact ForwardSolution.E_of_known 𝔼 (by omega) (hD.2 t m)

/-- Cochrane (2023), p. 212: debt chosen at `t` (the stock `D (t + 1) m`) is known at every
date `u ≥ t`. -/
theorem Predetermined.known_succ {D : ℕ → ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t u : ℕ}
    (htu : t ≤ u) (m : ℕ) : 𝔼.E u (D (t + 1) m) = D (t + 1) m :=
  ForwardSolution.E_of_known 𝔼 htu (hD.2 t m)

/-- Cochrane (2023), p. 212: the risk-neutral nominal bond price
`Q_t^{(t+j)} = β^j E_t(P_t / P_{t+j})`, written with `x = 1/P`. -/
noncomputable def bondPrice (β : ℝ) (P x : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  β ^ j • 𝔼.E t (P t * x (t + j))

/-- Cochrane (2023), p. 212: `Q_t^{(t+j)} = β^j P_t E_t(1/P_{t+j})`, pulling the known `P_t`
out of the expectation. -/
theorem bondPrice_eq (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (t j : ℕ) : bondPrice 𝔼 β P x t j = β ^ j • (P t * 𝔼.E t (x (t + j))) := by
  rw [bondPrice, hpo t _ _ (hP t)]

/-- Cochrane (2023), eq. (3.2) recalled on p. 212: the nominal flow condition
`B_{t−1}^{(t)} = P_t s_t + ∑_{j≥1} Q_t^{(t+j)} (B_t^{(t+j)} − B_{t−1}^{(t+j)})`, as a genuine
convergent series at every state. -/
def NominalFlow (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (P x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => bondPrice 𝔼 β P x t (j + 1) ω * sales D t (t + (j + 1)) ω)
    (D t t ω - P t ω * s t ω)

/-- Cochrane (2023), eq. (7.1), p. 213 (and (7.4), p. 216): the real flow condition
`B_{t−1}^{(t)}/P_t = s_t + ∑_{j≥1} β^j (B_t^{(t+j)} − B_{t−1}^{(t+j)}) E_t(1/P_{t+j})`. -/
def RealFlow (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
    𝔼.E t (x (t + (j + 1))) ω)) (D t t ω * x t ω - s t ω)

/-- Cochrane (2023), eq. (7.1), p. 213: the nominal flow condition (3.2) divided by `P_t > 0`
is the real flow condition (7.1), and conversely. -/
theorem nominalFlow_iff_realFlow (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hPpos : ∀ t ω, 0 < P t ω) (t : ℕ) :
    NominalFlow 𝔼 β D P x s t ↔ RealFlow 𝔼 β D x s t := by
  have hterm : ∀ ω j, bondPrice 𝔼 β P x t (j + 1) ω * sales D t (t + (j + 1)) ω =
      P t ω * (β ^ (j + 1) * (sales D t (t + (j + 1)) ω * 𝔼.E t (x (t + (j + 1))) ω)) := by
    intro ω j
    rw [bondPrice_eq 𝔼 hpo hP]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hval : ∀ ω, D t t ω - P t ω * s t ω = P t ω * (D t t ω * x t ω - s t ω) := by
    intro ω
    have := hPx t ω
    linear_combination (-(D t t ω)) * this
  constructor
  · intro h ω
    have h1 := (h ω).mul_left (P t ω)⁻¹
    simp only [hterm, hval, ← mul_assoc, inv_mul_cancel₀ (hPpos t ω).ne', one_mul] at h1
    convert h1 using 1
    funext j
    ring
  · intro h ω
    have h1 := (h ω).mul_left (P t ω)
    simp only [hterm, hval]
    exact h1

/-- Cochrane (2023), eq. (7.2), p. 213: the terms `β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j})` of the real
value of debt outstanding at the start of `t`. -/
noncomputable def debtTerm (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * (D t (t + j) ω * 𝔼.E t (x (t + j)) ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the real value of debt outstanding at the start of `t`,
`V_t = ∑_{j≥0} β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j})`. -/
noncomputable def debtValue (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, debtTerm 𝔼 β D x t j ω

/-- Cochrane (2023), eq. (7.2), p. 213: the terms `β^k E_t s_{t+k}` of the present value of
surpluses. -/
noncomputable def surplusTerm (β : ℝ) (s : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) : ℝ :=
  β ^ k * 𝔼.E t (s (t + k)) ω

/-- Cochrane (2023), eq. (7.2), p. 213: the present value of surpluses `E_t ∑_k β^k s_{t+k}`. -/
noncomputable def pvSurplus (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, surplusTerm 𝔼 β s t k ω

/-- Cochrane (2023), eq. (7.2), p. 213 (and (7.5), p. 216): the present-value relation at `t`,
`∑_j β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j}) = E_t ∑_j β^j s_{t+j}`, both sides genuine convergent
series. -/
def PresentValue (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Summable (fun k => surplusTerm 𝔼 β s t k ω) ∧
    HasSum (fun j => debtTerm 𝔼 β D x t j ω) (pvSurplus 𝔼 β s t ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the terms of the real value of debt are dominated by a
summable sequence at date `t` (the hypothesis that lets `E_{t−1}` pass through the series). -/
def DebtDominated (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∃ u : ℕ → ℝ, Summable u ∧ ∀ j ω, |debtTerm 𝔼 β D x t j ω| ≤ u j

/-- Cochrane (2023), eq. (3.3) recalled on p. 212: the nominal market value of debt
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` equals `P_t` times the real value `V_t` of (7.2). -/
theorem nominalValue_eq (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (t : ℕ) (ω : Ω) {v : ℝ} (hv : HasSum (fun j => debtTerm 𝔼 β D x t j ω) v) :
    HasSum (fun j => bondPrice 𝔼 β P x t j ω * D t (t + j) ω) (P t ω * v) := by
  have h := hv.mul_left (P t ω)
  refine h.congr_fun ?_
  intro j
  rw [bondPrice_eq 𝔼 hpo hP, debtTerm]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (7.2), p. 213: with `B_t^{(m)}` known at `t`,
`E_t V_{t+1} = ∑_{j≥0} β^j B_t^{(t+1+j)} E_t(1/P_{t+1+j})`, provided the series for `V_{t+1}` is
dominated. -/
theorem hasSum_E_debtValue_succ (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t : ℕ} (hdom : DebtDominated 𝔼 β D x (t + 1))
    (ω : Ω) :
    HasSum (fun j => β ^ j * (D (t + 1) (t + 1 + j) ω * 𝔼.E t (x (t + 1 + j)) ω))
      (𝔼.E t (debtValue 𝔼 β D x (t + 1)) ω) := by
  obtain ⟨u, hu, hb⟩ := hdom
  have hE := ForwardSolution.E_tsum_dom 𝔼 hu (f := fun j ω' => debtTerm 𝔼 β D x (t + 1) j ω')
    hb t ω
  have hterm : ∀ j, 𝔼.E t (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') ω =
      β ^ j * (D (t + 1) (t + 1 + j) ω * 𝔼.E t (x (t + 1 + j)) ω) := by
    intro j
    have hfun : (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') =
        β ^ j • (D (t + 1) (t + 1 + j) * 𝔼.E (t + 1) (x (t + 1 + j))) := by
      funext ω'
      simp [debtTerm]
    rw [hfun, map_smul, hpo t _ _ (hD.2 t _), 𝔼.tower (Nat.le_succ t)]
    simp
  have hsum : Summable (fun j => 𝔼.E t (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') ω) :=
    Summable.of_norm_bounded hu (fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hb j) t ω)
  have h2 := hsum.hasSum
  rw [← hE] at h2
  simp only [hterm] at h2
  exact h2

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213: the flow condition at `t` is equivalent to the
one-period recursion `V_t = s_t + β E_t V_{t+1}` for the real value of debt, given convergence of
the series for `V_t` and domination of the series for `V_{t+1}`. -/
theorem realFlow_iff_recursion (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x) {t : ℕ}
    (hsumm : ∀ ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : DebtDominated 𝔼 β D x (t + 1)) :
    RealFlow 𝔼 β D x s t ↔
      debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) := by
  -- the flow terms are `β b_j − a_{j+1}`
  have hkey : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω))
      (β * 𝔼.E t (debtValue 𝔼 β D x (t + 1)) ω - (debtValue 𝔼 β D x t ω - D t t ω * x t ω)) := by
    intro ω
    have hb := (hasSum_E_debtValue_succ 𝔼 hpo hD hdom ω).mul_left β
    have ha := (hasSum_nat_add_iff' 1).mpr (hsumm ω).hasSum
    have ha0 : ∑ i ∈ Finset.range 1, debtTerm 𝔼 β D x t i ω = D t t ω * x t ω := by
      simp [debtTerm, hx t]
    rw [ha0] at ha
    refine (hb.sub ha).congr_fun ?_
    intro j
    simp only [debtTerm, sales, Pi.sub_apply]
    rw [show t + 1 + j = t + (j + 1) by omega, pow_succ]
    ring
  constructor
  · intro h
    funext ω
    have := (h ω).unique (hkey ω)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h ω
    have hω := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω
    convert hkey ω using 1
    linarith

/-- Cochrane (2023), eq. (7.2), p. 213: the recursion `V_t = s_t + β E_t V_{t+1}` makes `V_t`
known at `t` when surpluses are. -/
theorem debtValue_adapted {β : ℝ} {V s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t : ℕ) : 𝔼.E t (V t) = V t := by
  conv_lhs => rw [hrec t]
  rw [map_add, map_smul, 𝔼.E_E_self, hs t, ← hrec t]

/-- Cochrane (2023), eq. (7.2), p. 213: iterating the recursion,
`V_t = ∑_{k<N} β^k E_t s_{t+k} + β^N E_t V_{t+N}`. -/
theorem debtValue_iterate {β : ℝ} {V s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t N : ℕ) :
    V t = ∑ k ∈ Finset.range N, β ^ k • 𝔼.E t (s (t + k)) + β ^ N • 𝔼.E t (V (t + N)) := by
  induction N with
  | zero => simp [debtValue_adapted 𝔼 hs hrec t]
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have h1 : 𝔼.E t (V (t + N)) = 𝔼.E t (s (t + N)) + β • 𝔼.E t (V (t + (N + 1))) := by
      conv_lhs => rw [hrec (t + N)]
      rw [map_add, map_smul, 𝔼.tower (Nat.le_add_right t N), ← add_assoc]
    rw [h1, smul_add, smul_smul, ← pow_succ]

/-- Cochrane (2023), eq. (7.2), p. 213: with bounded surpluses and `0 ≤ β < 1`, the surplus
series is absolutely convergent. -/
theorem summable_surplusTerm {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => surplusTerm 𝔼 β s t k ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) t ω) (pow_nonneg hβ0 k)

/-- Cochrane (2023), eq. (7.2), p. 213: the transversality condition at `t`,
`β^N E_t V_{t+N} → 0`. -/
def Transversality (β : ℝ) (V : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N => β ^ N * 𝔼.E t (V (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (7.2), p. 213: given the one-period recursion (equivalently the flow
conditions), the present-value relation at `t` holds if and only if the transversality
condition holds. -/
theorem presentValue_iff_tvc {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V s : ℕ → Ω → ℝ}
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t : ℕ) :
    (∀ ω, HasSum (fun k => surplusTerm 𝔼 β s t k ω) (V t ω)) ↔ Transversality 𝔼 β V t := by
  have hpart : ∀ ω N, ∑ k ∈ Finset.range N, surplusTerm 𝔼 β s t k ω =
      V t ω - β ^ N * 𝔼.E t (V (t + N)) ω := by
    intro ω N
    have h := congrFun (debtValue_iterate 𝔼 hs hrec t N) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    simp only [surplusTerm]
    linarith
  constructor
  · intro h ω
    have ht := (h ω).tendsto_sum_nat
    simp only [hpart] at ht
    have := (tendsto_const_nhds (x := V t ω)).sub ht
    simpa using this
  · intro h ω
    rw [(summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum_iff_tendsto_nat]
    simp only [hpart]
    simpa using (tendsto_const_nhds (x := V t ω)).sub (h ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the present value of bounded surpluses satisfies the
one-period recursion `PV_t = s_t + β E_t PV_{t+1}`. -/
theorem pvSurplus_recursion {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    pvSurplus 𝔼 β s t = s t + β • 𝔼.E t (pvSurplus 𝔼 β s (t + 1)) := by
  funext ω
  have hb : ∀ k ω', |surplusTerm 𝔼 β s (t + 1) k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  have hE := 𝔼.E_tsum hβ0 hβ1 hb t ω
  have hterm : ∀ k, 𝔼.E t (surplusTerm 𝔼 β s (t + 1) k) ω = β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
    intro k
    have hfun : surplusTerm 𝔼 β s (t + 1) k = β ^ k • 𝔼.E (t + 1) (s (t + 1 + k)) := by
      funext ω'; simp [surplusTerm]
    rw [hfun, map_smul, 𝔼.tower (Nat.le_succ t)]
    simp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, surplusTerm 𝔼 β s t k ω =
    s t ω + β * 𝔼.E t (fun ω' => ∑' k, surplusTerm 𝔼 β s (t + 1) k ω') ω
  rw [hE, (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).tsum_eq_zero_add]
  simp only [hterm]
  rw [← tsum_mul_left]
  congr 1
  · simp [surplusTerm, hs t]
  · refine tsum_congr fun k => ?_
    simp only [surplusTerm]
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213 (and (7.4)–(7.5), p. 216): **flow plus
transversality is equivalent to present value.** With bounded surpluses, predetermined debt,
convergent and dominated debt-value series, the flow conditions (7.1) at every date together with
the transversality conditions are equivalent to the present-value relations (7.2) at every
date. -/
theorem flow_tvc_iff_presentValue (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x)
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : ∀ t, DebtDominated 𝔼 β D x t) :
    ((∀ t, RealFlow 𝔼 β D x s t) ∧ ∀ t, Transversality 𝔼 β (debtValue 𝔼 β D x) t) ↔
      ∀ t, PresentValue 𝔼 β D x s t := by
  constructor
  · rintro ⟨hflow, htvc⟩ t ω
    have hrec : ∀ t, debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) :=
      fun t => (realFlow_iff_recursion 𝔼 hpo hD hx (hsumm t) (hdom (t + 1))).mp (hflow t)
    have hpv := (presentValue_iff_tvc 𝔼 hβ0 hβ1 hs hsb hrec t).mpr (htvc t) ω
    refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
    have heq : pvSurplus 𝔼 β s t ω = debtValue 𝔼 β D x t ω := hpv.tsum_eq
    rw [heq]
    exact (hsumm t ω).hasSum
  · intro hpv
    have hV : ∀ t, debtValue 𝔼 β D x t = pvSurplus 𝔼 β s t := by
      intro t
      funext ω
      exact (hpv t ω).2.tsum_eq
    have hrec : ∀ t, debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) := by
      intro t
      rw [hV t, hV (t + 1)]
      exact pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb t
    refine ⟨fun t => (realFlow_iff_recursion 𝔼 hpo hD hx (hsumm t) (hdom (t + 1))).mpr
      (hrec t), fun t => ?_⟩
    refine (presentValue_iff_tvc 𝔼 hβ0 hβ1 hs hsb hrec t).mp fun ω => ?_
    rw [hV t]
    exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum

/-- Cochrane (2023), eq. (7.2), p. 213: a bounded real value of debt satisfies the
transversality condition. -/
theorem transversality_of_bounded {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, |V t ω| ≤ K) (t : ℕ) : Transversality 𝔼 β V t := by
  intro ω
  have hlim : Tendsto (fun N : ℕ => β ^ N * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K
  refine squeeze_zero_norm (fun N => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hV (t + N)) t ω) (pow_nonneg hβ0 N)

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213: with a bounded real value of debt, the flow
conditions at every date imply the present-value relation at every date. -/
theorem presentValue_of_bounded (hpo : 𝔼.PullOut) {β M K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x)
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : ∀ t, DebtDominated 𝔼 β D x t) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hV : ∀ t ω, |debtValue 𝔼 β D x t ω| ≤ K) (t : ℕ) : PresentValue 𝔼 β D x s t :=
  (flow_tvc_iff_presentValue 𝔼 hpo hβ0 hβ1 hD hx hs hsb hsumm hdom).mp
    ⟨hflow, transversality_of_bounded 𝔼 hβ0 hβ1 hV⟩ t

end Cochrane.LongTermDebtDynamics.MaturityStructure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Forward guidance and bond-price targets

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214) and
Online Appendix §A1.2.1, pp. 559–561 (the geometric-maturity forward-guidance formulas behind
Figure 7.1, discrete and continuous time, and the steady-state sales).

At date 0 the government announces that the one-period rate, `r` until now, rises to `i` from
date `T` on. Bonds maturing at `j ≤ T` keep their prices `(1+r)^{-j}`, bonds maturing at `T + j`
are priced `((1+r)^T (1+i)^j)^{-1}`. With surpluses unchanged, the valuation equation (7.3)
`(∑_j Q_0^{(j)} B_{−1}^{(j)}) / P_0 = E_0 ∑_j β^j s_j` determines `P_0`.

## Main results

* `fgPrice_of_le`, `fgPrice_add`, `inv_pow_lt_fgPrice`, `fgPrice_lt`: the bond-price display on
  p. 214, including `Q_0^{(T+j)} > (1+i)^{-(T+j)}`.
* `fgPrice_mono`: the bond prices rise with the announcement horizon `T`.
* `fgPath_unique`, `fgPath_eq_of_le`, `fgPath_jump`, `fgPrice_eq_path`: perfect-foresight price
  path; the price level is flat until `T`, there is no second jump at `T`, and inflation starts
  only after the rate rises; the bond prices are `β^j P_0/P_j`.
* `valuation_iff`: (7.3) pins down `P_0` from bond prices (or bond-price targets).
* `priceLevel_fg_of_le`: forward guidance beyond the longest maturity `k` (`T ≥ k`, sharper than
  the book's `T > k`) leaves `P_0` unchanged; `priceLevel_fg_lt` shows `T ≥ k` is sharp.
* `priceLevel_mono`, `priceLevel_immediate_le`: forward guidance has a smaller effect than the
  same immediate rise, and the effect falls with the horizon.
* `hasSum_fg_geometric`, `fg_jump_geometric`: Online Appendix p. 560, the discrete geometric
  forward-guidance formula `P_0/P − 1 = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`;
  `fg_jump_immediate` is (1.16), `perpetuity_ratio_bounds` corrects the "25%" of p. 560.
* `fgJump_*`: the jump is negative, shrinks with `T`, tends to zero, and grows with `ω`.
* `integral_cfg`, `cfg_jump`, `cfgJump_*`: the continuous-time formula
  `P_0/P − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` (p. 561) with its comparative statics.
* `steady_sales`: the sales that maintain a geometric maturity structure (p. 561).
-/

namespace Cochrane.LongTermDebtDynamics.ForwardGuidance

open Filter Topology MeasureTheory

/-! ### Bond prices under forward guidance -/

/-- Cochrane (2023), §7.1, p. 214: the date-0 price of a zero-coupon bond maturing at `j` when the
one-period rate is `r` before date `T` and `i` from `T` on:
`Q_0^{(j)} = ((1+r)^{min(j,T)} (1+i)^{j−T})^{-1}`. -/
noncomputable def fgPrice (r i : ℝ) (T j : ℕ) : ℝ := ((1 + r) ^ min j T * (1 + i) ^ (j - T))⁻¹

/-- Cochrane (2023), §7.1, p. 214: bonds maturing at `j ≤ T` are unaffected by the announcement,
`Q_0^{(j)} = (1+r)^{-j}`. -/
theorem fgPrice_of_le (r i : ℝ) {T j : ℕ} (hj : j ≤ T) : fgPrice r i T j = ((1 + r) ^ j)⁻¹ := by
  rw [fgPrice, min_eq_left hj, Nat.sub_eq_zero_of_le hj, pow_zero, mul_one]

/-- Cochrane (2023), §7.1, p. 214: `Q_0^{(T+j)} = ((1+r)^T (1+i)^j)^{-1}`. -/
theorem fgPrice_add (r i : ℝ) (T j : ℕ) :
    fgPrice r i T (T + j) = ((1 + r) ^ T * (1 + i) ^ j)⁻¹ := by
  rw [fgPrice, min_eq_right (Nat.le_add_right T j), Nat.add_sub_cancel_left]

/-- Cochrane (2023), §7.1, p. 214: with no rate change the forward-guidance price is the
steady-state price `(1+r)^{-j}`. -/
theorem fgPrice_same (r : ℝ) (T j : ℕ) : fgPrice r r T j = ((1 + r) ^ j)⁻¹ := by
  rw [fgPrice, ← pow_add]
  congr 2
  omega

/-- Cochrane (2023), §7.1, p. 214: for `−1 < r < i` and `T ≥ 1`, the forward-guidance price
exceeds the price under an immediate rise, `Q_0^{(T+j)} > (1+i)^{-(T+j)}`. -/
theorem inv_pow_lt_fgPrice {r i : ℝ} (hr : -1 < r) (hri : r < i) {T : ℕ} (hT : 1 ≤ T)
    (j : ℕ) : ((1 + i) ^ (T + j))⁻¹ < fgPrice r i T (T + j) := by
  rw [fgPrice_add, pow_add]
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  apply inv_strictAnti₀ (mul_pos (pow_pos h1 _) (pow_pos h2 _))
  have : (1 + r) ^ T < (1 + i) ^ T := pow_lt_pow_left₀ (by linarith) h1.le (by omega)
  exact mul_lt_mul_of_pos_right this (by positivity)

/-- Cochrane (2023), §7.1, p. 214: bonds maturing after `T` fall in price,
`Q_0^{(j)} < (1+r)^{-j}` for `j > T` and `−1 < r < i`. -/
theorem fgPrice_lt {r i : ℝ} (hr : -1 < r) (hri : r < i) {T j : ℕ} (hj : T < j) :
    fgPrice r i T j < ((1 + r) ^ j)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, j = T + (k + 1) := ⟨j - T - 1, by omega⟩
  rw [fgPrice_add, show (1 + r) ^ (T + (k + 1)) = (1 + r) ^ T * (1 + r) ^ (k + 1) from
    pow_add _ _ _]
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  apply inv_strictAnti₀ (mul_pos (pow_pos h1 _) (pow_pos h1 _))
  have : (1 + r) ^ (k + 1) < (1 + i) ^ (k + 1) := pow_lt_pow_left₀ (by linarith) h1.le (by omega)
  exact mul_lt_mul_of_pos_left this (by positivity)

/-- Cochrane (2023), §7.1, p. 213: bond prices rise with the announcement horizon:
`T ↦ Q_0^{(j)}(T)` is monotone for `−1 < r ≤ i`. -/
theorem fgPrice_mono {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) (j : ℕ) :
    Monotone (fun T => fgPrice r i T j) := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  refine monotone_nat_of_le_succ fun T => ?_
  change fgPrice r i T j ≤ fgPrice r i (T + 1) j
  rcases le_or_gt j T with hj | hj
  · rw [fgPrice_of_le r i hj, fgPrice_of_le r i (Nat.le_succ_of_le hj)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = T + 1 + k := ⟨j - T - 1, by omega⟩
    rw [fgPrice_add, show T + 1 + k = T + (k + 1) by omega, fgPrice_add]
    apply inv_anti₀ (mul_pos (pow_pos h1 _) (pow_pos h2 _))
    rw [pow_succ, pow_succ]
    have : (1 + r) ^ T * (1 + i) ^ k * (1 + r) ≤ (1 + r) ^ T * (1 + i) ^ k * (1 + i) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos (pow_pos h1 _) (pow_pos h2 _)).le
    linarith [this]

/-! ### The perfect-foresight price path -/

/-- Cochrane (2023), §7.1, p. 213: the announced one-period rate path, `r` before `T`, `i` from
`T` on. -/
noncomputable def fgRate (r i : ℝ) (T t : ℕ) : ℝ := if t < T then r else i

/-- Cochrane (2023), §7.1, pp. 214–215: the price path after the announcement,
`P_t = P_0 ((1+i)/(1+r))^{t−T}` (flat until `T`, inflation `i − r` thereafter). -/
noncomputable def fgPath (P0 r i : ℝ) (T t : ℕ) : ℝ := P0 * ((1 + i) / (1 + r)) ^ (t - T)

/-- Cochrane (2023), §7.1, p. 215: the path satisfies the Fisher relation of the constant real
rate model, `P_{t+1} = P_t (1 + i_t)/(1 + r)` (i.e. `1 + i_t = β^{-1} P_{t+1}/P_t`). -/
theorem fgPath_succ (P0 r i : ℝ) (hr : -1 < r) (T t : ℕ) :
    fgPath P0 r i T (t + 1) = fgPath P0 r i T t * (1 + fgRate r i T t) / (1 + r) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  unfold fgPath fgRate
  by_cases ht : t < T
  · simp only [ht, ↓reduceIte, Nat.sub_eq_zero_of_le (show t + 1 ≤ T by omega),
      Nat.sub_eq_zero_of_le ht.le]
    field_simp
  · simp only [ht, ↓reduceIte, show t + 1 - T = t - T + 1 by omega, pow_succ]
    field_simp

/-- Cochrane (2023), §7.1, p. 215: under perfect foresight, the Fisher relation and `P_0` determine
the whole path: any path with `P_{t+1} = P_t(1+i_t)/(1+r)` is `fgPath`. -/
theorem fgPath_unique {P : ℕ → ℝ} {r i : ℝ} (hr : -1 < r) {T : ℕ}
    (hP : ∀ t, P (t + 1) = P t * (1 + fgRate r i T t) / (1 + r)) (t : ℕ) :
    P t = fgPath (P 0) r i T t := by
  induction t with
  | zero => simp [fgPath]
  | succ t ih => rw [hP t, ih, fgPath_succ (P 0) r i hr]

/-- Cochrane (2023), §7.1, pp. 214–215: the price level stays at its new level `P_0` up to and
including the date `T` at which the rate rises: there is no second jump. -/
theorem fgPath_eq_of_le (P0 r i : ℝ) {T t : ℕ} (ht : t ≤ T) : fgPath P0 r i T t = P0 := by
  simp [fgPath, Nat.sub_eq_zero_of_le ht]

/-- Cochrane (2023), §7.1, p. 215: inflation starts when the interest rate actually rises,
`P_{T+1} = P_T (1+i)/(1+r) > P_T` for `P_0 > 0` and `−1 < r < i`. -/
theorem fgPath_jump {P0 r i : ℝ} (hP0 : 0 < P0) (hr : -1 < r) (hri : r < i) (T : ℕ) :
    fgPath P0 r i T T < fgPath P0 r i T (T + 1) := by
  have h1 : 0 < 1 + r := by linarith
  simp only [fgPath, Nat.sub_self, pow_zero, mul_one, show T + 1 - T = 1 by omega, pow_one]
  rw [lt_mul_iff_one_lt_right hP0, one_lt_div h1]
  linarith

/-- Cochrane (2023), §7.1, p. 214: the forward-guidance bond prices are the perfect-foresight
prices `Q_0^{(j)} = β^j P_0/P_j` with `β = 1/(1+r)` along the path `fgPath`. -/
theorem fgPrice_eq_path {P0 r i : ℝ} (hP0 : P0 ≠ 0) (hr : -1 < r) (hi : -1 < i) (T j : ℕ) :
    fgPrice r i T j = ((1 + r)⁻¹) ^ j * (P0 / fgPath P0 r i T j) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (1 + i) ≠ 0 := by linarith
  have hj : (1 + r) ^ j = (1 + r) ^ min j T * (1 + r) ^ (j - T) := by
    rw [← pow_add]; congr 1; omega
  rw [fgPrice, fgPath, div_mul_cancel_left₀ hP0, div_pow, inv_div, inv_pow, hj]
  have h3 : (1 + r) ^ (j - T) ≠ 0 := pow_ne_zero _ h1
  have h4 : (1 + r) ^ min j T ≠ 0 := pow_ne_zero _ h1
  have h5 : (1 + i) ^ (j - T) ≠ 0 := pow_ne_zero _ h2
  field_simp

/-! ### The valuation equation (7.3) -/

/-- Cochrane (2023), eq. (7.3), p. 214: the price level implied by the valuation equation with
bond prices `Q`, outstanding debt `B_{−1}^{(j)}` (maturities `j ≤ k`) and present value of
surpluses `S`: `P_0 = (∑_{j ≤ k} Q_0^{(j)} B_{−1}^{(j)}) / S`. -/
noncomputable def priceLevel (Q B : ℕ → ℝ) (k : ℕ) (S : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), Q j * B j) / S

/-- Cochrane (2023), eq. (7.3), p. 214 and p. 215: the valuation equation determines the price
level from bond prices (or from bond-price targets): `(∑ Q B)/P_0 = S` iff `P_0 = priceLevel`. -/
theorem valuation_iff (Q B : ℕ → ℝ) (k : ℕ) {S P0 : ℝ} (hS : 0 < S) (hP0 : 0 < P0) :
    (∑ j ∈ Finset.range (k + 1), Q j * B j) / P0 = S ↔ P0 = priceLevel Q B k S := by
  rw [priceLevel, div_eq_iff hP0.ne', eq_div_iff hS.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §7.1, p. 214: if the announcement horizon reaches the longest outstanding
maturity, `T ≥ k`, the price level does not move. (The book says `T > k`; `T ≥ k` suffices.) -/
theorem priceLevel_fg_of_le (r i : ℝ) (B : ℕ → ℝ) {k T : ℕ} (hkT : k ≤ T) (S : ℝ) :
    priceLevel (fgPrice r i T) B k S = priceLevel (fgPrice r r T) B k S := by
  unfold priceLevel
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ T := by have := Finset.mem_range.mp hj; omega
  rw [fgPrice_of_le r i hj', fgPrice_same]

/-- Cochrane (2023), §7.1, p. 214: `T ≥ k` is sharp: if some maturity `j` with `T < j ≤ k` is
outstanding (`B_{−1}^{(j)} > 0`, all positions nonnegative), forward guidance lowers `P_0`. -/
theorem priceLevel_fg_lt {r i : ℝ} (hr : -1 < r) (hri : r < i) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) {k T j₀ : ℕ} (hTj : T < j₀) (hjk : j₀ ≤ k) (hBj : 0 < B j₀)
    {S : ℝ} (hS : 0 < S) :
    priceLevel (fgPrice r i T) B k S < priceLevel (fgPrice r r T) B k S := by
  unfold priceLevel
  apply div_lt_div_of_pos_right _ hS
  apply Finset.sum_lt_sum
  · intro j _
    rw [fgPrice_same]
    rcases le_or_gt j T with h | h
    · rw [fgPrice_of_le r i h]
    · exact mul_le_mul_of_nonneg_right (fgPrice_lt hr hri h).le (hB j)
  · refine ⟨j₀, Finset.mem_range.mpr (by omega), ?_⟩
    rw [fgPrice_same]
    exact mul_lt_mul_of_pos_right (fgPrice_lt hr hri hTj) hBj

/-- Cochrane (2023), §7.1, p. 213: the effect of forward guidance falls with the announcement
horizon: with nonnegative positions `P_0(T)` is monotone in `T`. -/
theorem priceLevel_mono {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j)
    (k : ℕ) {S : ℝ} (hS : 0 < S) : Monotone (fun T => priceLevel (fgPrice r i T) B k S) := by
  intro T T' hTT'
  unfold priceLevel
  apply div_le_div_of_nonneg_right _ hS.le
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (fgPrice_mono hr hri j hTT') (hB j)

/-- Cochrane (2023), §7.1, p. 213 (first bullet): forward guidance has less effect than the same
immediate rise: the immediate rise (`T = 0`) gives the lowest price level. -/
theorem priceLevel_immediate_le {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (k T : ℕ) {S : ℝ} (hS : 0 < S) :
    priceLevel (fgPrice r i 0) B k S ≤ priceLevel (fgPrice r i T) B k S :=
  priceLevel_mono hr hri hB k hS (Nat.zero_le T)

/-! ### Geometric maturity structure, discrete time (Online Appendix A1.2.1) -/

/-- Cochrane (2023), Online Appendix p. 560: the valuation sum `∑_j Q_0^{(j)} ω^j` under forward
guidance with a geometric maturity structure, in closed form with `a = ω/(1+r)`, `b = ω/(1+i)`. -/
noncomputable def fgSum (r i ω : ℝ) (T : ℕ) : ℝ :=
  (1 - (ω / (1 + r)) ^ (T + 1)) / (1 - ω / (1 + r)) +
    (ω / (1 + r)) ^ T * ((ω / (1 + i)) / (1 - ω / (1 + i)))

/-- Cochrane (2023), Online Appendix p. 560: `∑_j Q_0^{(j)} ω^j = fgSum` as a genuine convergent
series, for `0 ≤ ω < 1 + r`, `−1 < r ≤ i`. -/
theorem hasSum_fg_geometric {r i ω : ℝ} (hr : -1 < r) (hri : r ≤ i) (hω0 : 0 ≤ ω)
    (hω1 : ω < 1 + r) (T : ℕ) :
    HasSum (fun j => fgPrice r i T j * ω ^ j) (fgSum r i ω T) := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  have h1' : 1 + r ≠ 0 := h1.ne'
  have h2' : 1 + i ≠ 0 := h2.ne'
  set a := ω / (1 + r) with ha
  set b := ω / (1 + i) with hb
  have ha1 : a < 1 := by rw [ha, div_lt_one h1]; exact hω1
  have hb0 : 0 ≤ b := div_nonneg hω0 h2.le
  have hb1 : b < 1 := by rw [hb, div_lt_one h2]; linarith
  have hfin : ∑ j ∈ Finset.range (T + 1), fgPrice r i T j * ω ^ j =
      (1 - a ^ (T + 1)) / (1 - a) := by
    have : ∀ j ∈ Finset.range (T + 1), fgPrice r i T j * ω ^ j = a ^ j := by
      intro j hj
      rw [fgPrice_of_le r i (by have := Finset.mem_range.mp hj; omega), ha, div_pow]
      field_simp
    rw [Finset.sum_congr rfl this, geom_sum_eq ha1.ne]
    have : a - 1 ≠ 0 := by linarith
    have : 1 - a ≠ 0 := by linarith
    field_simp
    ring
  rw [← hasSum_nat_add_iff' (T + 1), hfin]
  have htail : HasSum (fun n : ℕ => a ^ T * b * b ^ n) (a ^ T * b * (1 - b)⁻¹) :=
    (hasSum_geometric_of_lt_one hb0 hb1).mul_left (a ^ T * b)
  convert htail using 1
  · funext n
    rw [show n + (T + 1) = T + (n + 1) by omega, fgPrice_add, ha, hb, div_pow, div_pow]
    field_simp
    ring
  · rw [fgSum]
    ring

/-- Cochrane (2023), Online Appendix eq. (1.15), p. 559: without a rate change the valuation sum
is `(1+r)/(1+r−ω) = 1/(1−a)`. -/
theorem fgSum_same {r ω : ℝ} (hr : -1 < r) (hω1 : ω < 1 + r) (T : ℕ) :
    fgSum r r ω T = 1 / (1 - ω / (1 + r)) := by
  have h1 : 0 < 1 + r := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  rw [fgSum]
  generalize ω / (1 + r) = a at *
  have : 1 - a ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 560: the forward-guidance price-level jump with a
geometric maturity structure, `J_T = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`. -/
noncomputable def fgJump (r i ω : ℝ) (T : ℕ) : ℝ :=
  (ω / (1 + r)) ^ T * ((1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) - 1)

/-- Cochrane (2023), Online Appendix p. 560: **the discrete forward-guidance formula.** Starting
from the steady state `(B/P) ∑ (ω/(1+r))^j = PV`, an announcement at 0 of a rise from `r` to `i`
at `T`, with the same debt `B` and surpluses, gives `P_0/P − 1 = J_T`. -/
theorem fg_jump_geometric {r i ω B P P0 PV : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hω1 : ω < 1 + r) (hP : 0 < P) (hP0 : 0 < P0) (T : ℕ)
    (hss : B / P * fgSum r r ω T = PV) (hfg : B / P0 * fgSum r i ω T = PV) (hPV : PV ≠ 0) :
    P0 / P - 1 = fgJump r i ω T := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have hb1 : ω / (1 + i) < 1 := by rw [div_lt_one h2]; linarith
  have hu : 1 - ω / (1 + r) ≠ 0 := by linarith
  rw [fgSum_same hr hω1, div_mul_div_comm, mul_one, div_eq_iff (mul_ne_zero hP.ne' hu)] at hss
  rw [div_mul_eq_mul_div, div_eq_iff hP0.ne'] at hfg
  have hratio : P0 / P = fgSum r i ω T * (1 - ω / (1 + r)) := by
    rw [div_eq_iff hP.ne']
    apply mul_left_cancel₀ hPV
    rw [← hfg, hss]
    ring
  have hfac : (1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) =
      (1 - ω / (1 + r)) / (1 - ω / (1 + i)) := by
    have : 1 + i - ω ≠ 0 := by linarith
    have : 1 + r ≠ 0 := h1.ne'
    have : 1 + i ≠ 0 := h2.ne'
    field_simp
  rw [hratio, fgSum, fgJump, hfac]
  generalize ω / (1 + r) = a at *
  generalize ω / (1 + i) = b at *
  have : 1 - a ≠ 0 := by linarith
  have : 1 - b ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (1.16), p. 559: an immediate permanent rise (`T = 0`)
gives `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))`. -/
theorem fg_jump_immediate (r i ω : ℝ) :
    fgJump r i ω 0 + 1 = (1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) := by
  simp [fgJump]

/-- Cochrane (2023), Online Appendix p. 560: the jump in closed form,
`J_T = −(ω/(1+r))^T ω (i − r)/((1+r)(1+i−ω))`. -/
theorem fgJump_eq {r i ω : ℝ} (hr : -1 < r) (hiω : ω < 1 + i) (T : ℕ) :
    fgJump r i ω T = -((ω / (1 + r)) ^ T * (ω * (i - r) / ((1 + r) * (1 + i - ω)))) := by
  have h1 : 1 + r ≠ 0 := by linarith
  have h2 : 1 + i - ω ≠ 0 := by linarith
  rw [fgJump]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 560: the price level jumps down,
`J_T < 0`, for `0 < ω < 1 + r` and `−1 < r < i`. -/
theorem fgJump_neg {r i ω : ℝ} (hr : -1 < r) (hri : r < i) (hω0 : 0 < ω) (hω1 : ω < 1 + r)
    (T : ℕ) : fgJump r i ω T < 0 := by
  have h1 : 0 < 1 + r := by linarith
  rw [fgJump_eq hr (by linarith) T, neg_lt_zero]
  have : 0 < 1 + i - ω := by linarith
  have : 0 < i - r := by linarith
  positivity

/-- Cochrane (2023), Online Appendix p. 561: a longer horizon gives a smaller jump,
`J_{T+1} = (ω/(1+r)) J_T`, so `|J_{T+1}| < |J_T|` for `0 < ω < 1 + r`. -/
theorem fgJump_succ (r i ω : ℝ) (T : ℕ) :
    fgJump r i ω (T + 1) = ω / (1 + r) * fgJump r i ω T := by
  rw [fgJump, fgJump, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 561: the jump shrinks strictly with the horizon. -/
theorem fgJump_abs_lt {r i ω : ℝ} (hr : -1 < r) (hri : r < i) (hω0 : 0 < ω) (hω1 : ω < 1 + r)
    (T : ℕ) : |fgJump r i ω (T + 1)| < |fgJump r i ω T| := by
  have h1 : 0 < 1 + r := by linarith
  have hJ := fgJump_neg hr hri hω0 hω1 T
  rw [fgJump_succ, abs_mul, abs_of_pos (div_pos hω0 h1)]
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have : 0 < |fgJump r i ω T| := abs_pos.mpr hJ.ne
  nlinarith

/-- Cochrane (2023), Online Appendix p. 561: as `T → ∞` the downward jump goes to zero. -/
theorem fgJump_tendsto {r i ω : ℝ} (hr : -1 < r) (hω0 : 0 ≤ ω) (hω1 : ω < 1 + r) :
    Tendsto (fun T => fgJump r i ω T) atTop (𝓝 0) := by
  have h1 : 0 < 1 + r := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hω0 h1.le) ha1).mul_const
    ((1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) - 1)
  simpa [fgJump] using this

/-- Cochrane (2023), Online Appendix p. 561: shorter maturity structures (lower `ω`) give a
smaller jump: `|J_T|` is monotone in `ω` on `[0, 1 + r)`. -/
theorem fgJump_abs_mono_omega {r i ω ω' : ℝ} (hr : -1 < r) (hri : r ≤ i) (hω0 : 0 ≤ ω)
    (hωω' : ω ≤ ω') (hω'1 : ω' < 1 + r) (T : ℕ) :
    |fgJump r i ω T| ≤ |fgJump r i ω' T| := by
  have h1 : 0 < 1 + r := by linarith
  rw [fgJump_eq hr (by linarith) T, fgJump_eq hr (by linarith) T, abs_neg, abs_neg]
  have hd : 0 < 1 + i - ω' := by linarith
  have hir : 0 ≤ i - r := by linarith
  have nn : ∀ v, 0 ≤ v → v < 1 + i →
      0 ≤ (v / (1 + r)) ^ T * (v * (i - r) / ((1 + r) * (1 + i - v))) := fun v hv0 hv1 =>
    mul_nonneg (pow_nonneg (div_nonneg hv0 h1.le) T)
      (div_nonneg (mul_nonneg hv0 hir) (mul_pos h1 (by linarith)).le)
  rw [abs_of_nonneg (nn ω hω0 (by linarith)), abs_of_nonneg (nn ω' (by linarith) (by linarith))]
  have hp : (ω / (1 + r)) ^ T ≤ (ω' / (1 + r)) ^ T :=
    pow_le_pow_left₀ (div_nonneg hω0 h1.le) (div_le_div_of_nonneg_right hωω' h1.le) T
  have hq : ω * (i - r) / ((1 + r) * (1 + i - ω)) ≤ ω' * (i - r) / ((1 + r) * (1 + i - ω')) :=
    div_le_div₀ (mul_nonneg (by linarith) hir) (mul_le_mul_of_nonneg_right hωω' hir)
      (mul_pos h1 hd) (mul_le_mul_of_nonneg_left (by linarith) h1.le)
  exact mul_le_mul hp hq (div_nonneg (mul_nonneg hω0 hir) (mul_pos h1 (by linarith)).le)
    (pow_nonneg (div_nonneg (by linarith) h1.le) T)

/-- Cochrane (2023), Online Appendix p. 560, Figure 7.1 calibration (`ω = 0.8`, `r = 2%`,
`i = 3%`): the immediate rise lowers the price level by 3.41%, forward guidance with `T = 3` by
1.65% (the book reports 3.5% and 1.6%). -/
theorem fgJump_calibration :
    -0.035 < fgJump 0.02 0.03 0.8 0 ∧ fgJump 0.02 0.03 0.8 0 < -0.034 ∧
      -0.017 < fgJump 0.02 0.03 0.8 3 ∧ fgJump 0.02 0.03 0.8 3 < -0.016 := by
  simp only [fgJump]
  norm_num

/-- Cochrane (2023), Online Appendix eq. (1.19), p. 560: for a discrete perpetuity (`ω = 1`) a rise
from 3% to 4% gives `P_0/P = (1+i) r/((1+r) i) ≈ 0.757`, a 24.3% drop; the "25%" quoted on p. 560
is the continuous-time ratio `r/i` of (1.20). -/
theorem perpetuity_ratio_bounds :
    fgJump 0.03 0.04 1 0 + 1 = (1 + 0.04) * 0.03 / ((1 + 0.03) * 0.04) ∧
      0.757 < fgJump 0.03 0.04 1 0 + 1 ∧ fgJump 0.03 0.04 1 0 + 1 < 0.758 := by
  simp only [fgJump]
  norm_num

/-! ### Continuous time (Online Appendix p. 561) -/

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time valuation integrand: maturity
density `ϖ e^{−ϖ j}` times the bond price `exp(−(r min(j,T) + i max(j−T,0)))`. -/
noncomputable def cfgIntegrand (r i ϖ T j : ℝ) : ℝ :=
  ϖ * Real.exp (-ϖ * j) * Real.exp (-(r * min j T + i * max (j - T) 0))

/-- Cochrane (2023), Online Appendix p. 561: the valuation integral in closed form,
`ϖ[(1 − e^{−(r+ϖ)T})/(r+ϖ) + e^{−(r+ϖ)T}/(i+ϖ)]`. -/
noncomputable def cfgValue (r i ϖ T : ℝ) : ℝ :=
  ϖ * ((1 - Real.exp (-(r + ϖ) * T)) / (r + ϖ) + Real.exp (-(r + ϖ) * T) / (i + ϖ))

/-- Cochrane (2023), Online Appendix p. 561: `∫_0^∞ ϖ e^{−ϖj} Q_0(j) dj = cfgValue`, a genuine
improper integral, for `r + ϖ > 0`, `i + ϖ > 0`, `T ≥ 0`. -/
theorem integral_cfg {r i ϖ T : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) (hT : 0 ≤ T) :
    ∫ j in Set.Ioi (0 : ℝ), cfgIntegrand r i ϖ T j = cfgValue r i ϖ T := by
  set g : ℝ → ℝ := fun j => ϖ * Real.exp (-(r + ϖ) * j) with hg
  set h : ℝ → ℝ := fun j => ϖ * Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * j) with hh
  have hgi : ∀ c, IntegrableOn g (Set.Ioi c) := fun c =>
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul ϖ
  have hhi : IntegrableOn h (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith) T).const_mul _
  have hgI : ∀ c, ∫ j in Set.Ioi c, g j = ϖ * (Real.exp (-(r + ϖ) * c) / (r + ϖ)) := by
    intro c
    rw [hg, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    field_simp
  have hhI : ∫ j in Set.Ioi T, h j = ϖ * (Real.exp (-(r + ϖ) * T) / (i + ϖ)) := by
    have hE : Real.exp (-(r + ϖ) * T) = Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    have hne : i + ϖ ≠ 0 := hiv.ne'
    rw [hh, integral_const_mul, integral_exp_mul_Ioi (by linarith), hE]
    field_simp
  have hEg : Set.EqOn (cfgIntegrand r i ϖ T) g (Set.Ioc 0 T) := by
    intro j hj
    simp only [cfgIntegrand, hg, min_eq_left hj.2, max_eq_right (by linarith [hj.2] : j - T ≤ 0),
      mul_zero, add_zero, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hEh : Set.EqOn (cfgIntegrand r i ϖ T) h (Set.Ioi T) := by
    intro j hj
    have hj' : T < j := hj
    simp only [cfgIntegrand, hh, min_eq_right hj'.le, max_eq_left (by linarith : 0 ≤ j - T),
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hfs : IntegrableOn (cfgIntegrand r i ϖ T) (Set.Ioc 0 T) :=
    ((hgi 0).mono_set Set.Ioc_subset_Ioi_self).congr_fun hEg.symm measurableSet_Ioc
  have hft : IntegrableOn (cfgIntegrand r i ϖ T) (Set.Ioi T) :=
    hhi.congr_fun hEh.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    hfs hft, setIntegral_congr_fun measurableSet_Ioc hEg,
    setIntegral_congr_fun measurableSet_Ioi hEh, hhI]
  have hsplit := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := T))
    measurableSet_Ioi ((hgi 0).mono_set Set.Ioc_subset_Ioi_self) (hgi T)
  rw [Set.Ioc_union_Ioi_eq_Ioi hT, hgI 0, hgI T] at hsplit
  have hgIoc : ∫ j in Set.Ioc 0 T, g j =
      ϖ * (Real.exp (-(r + ϖ) * 0) / (r + ϖ)) - ϖ * (Real.exp (-(r + ϖ) * T) / (r + ϖ)) := by
    linarith
  rw [hgIoc, cfgValue, mul_zero, Real.exp_zero]
  ring

/-- Cochrane (2023), Online Appendix eq. (1.17), p. 560: with no rate change the valuation
integral is `ϖ/(r+ϖ)`. -/
theorem cfgValue_same (r ϖ T : ℝ) (hrv : 0 < r + ϖ) : cfgValue r r ϖ T = ϖ / (r + ϖ) := by
  rw [cfgValue]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time forward-guidance jump
`e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)`. -/
noncomputable def cfgJump (r i ϖ T : ℝ) : ℝ := Real.exp (-(r + ϖ) * T) * ((r + ϖ) / (i + ϖ) - 1)

/-- Cochrane (2023), Online Appendix p. 561: **the continuous forward-guidance formula.** From
the steady state `(B/P)·ϖ/(r+ϖ) = PV`, the announcement gives `P_0/P − 1 = cfgJump`. -/
theorem cfg_jump {r i ϖ T B P P0 PV : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) (hϖ : 0 < ϖ)
    (hP : 0 < P) (hP0 : 0 < P0) (hss : B / P * cfgValue r r ϖ T = PV)
    (hfg : B / P0 * cfgValue r i ϖ T = PV) (hPV : PV ≠ 0) :
    P0 / P - 1 = cfgJump r i ϖ T := by
  rw [cfgValue_same r ϖ T hrv, div_mul_div_comm, div_eq_iff (mul_ne_zero hP.ne' hrv.ne')] at hss
  rw [div_mul_eq_mul_div, div_eq_iff hP0.ne'] at hfg
  have hP0eq : P0 = P * cfgValue r i ϖ T * (r + ϖ) / ϖ := by
    rw [eq_div_iff hϖ.ne']
    apply mul_left_cancel₀ hPV
    linear_combination (cfgValue r i ϖ T) * hss - ϖ * hfg
  rw [hP0eq, cfgValue, cfgJump]
  have : i + ϖ ≠ 0 := hiv.ne'
  have : r + ϖ ≠ 0 := hrv.ne'
  have : ϖ ≠ 0 := hϖ.ne'
  have : P ≠ 0 := hP.ne'
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (1.18), p. 560: the immediate rise (`T = 0`) gives
`P_0/P = (r+ϖ)/(i+ϖ)`, and for the perpetuity (`ϖ = 0`) eq. (1.20) `P_0/P = r/i`. -/
theorem cfgJump_zero (r i ϖ : ℝ) : cfgJump r i ϖ 0 + 1 = (r + ϖ) / (i + ϖ) := by
  simp [cfgJump]

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time jump is negative for `r < i`. -/
theorem cfgJump_neg {r i ϖ : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) (T : ℝ) : cfgJump r i ϖ T < 0 := by
  rw [cfgJump]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  rw [sub_neg, div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), Online Appendix p. 561: a longer horizon gives a smaller jump. -/
theorem cfgJump_abs_anti {r i ϖ : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) {T T' : ℝ} (hTT' : T < T') :
    |cfgJump r i ϖ T'| < |cfgJump r i ϖ T| := by
  rw [abs_of_neg (cfgJump_neg hrv hri T'), abs_of_neg (cfgJump_neg hrv hri T), neg_lt_neg_iff,
    cfgJump, cfgJump]
  have hc : (r + ϖ) / (i + ϖ) - 1 < 0 := by
    rw [sub_neg, div_lt_one (by linarith)]; linarith
  apply mul_lt_mul_of_neg_right _ hc
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- Cochrane (2023), Online Appendix p. 561: as `T → ∞` the continuous-time jump vanishes. -/
theorem cfgJump_tendsto {r i ϖ : ℝ} (hrv : 0 < r + ϖ) :
    Tendsto (fun T => cfgJump r i ϖ T) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => -(r + ϖ) * T) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have := (Real.tendsto_exp_atBot.comp h).mul_const ((r + ϖ) / (i + ϖ) - 1)
  simpa [cfgJump, Function.comp_def] using this

/-- Cochrane (2023), Online Appendix p. 561: a shorter maturity structure (larger `ϖ`) gives a
smaller jump: `|cfgJump|` is antitone in `ϖ` for `T ≥ 0`, `r < i`. -/
theorem cfgJump_abs_anti_varpi {r i ϖ ϖ' T : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) (hT : 0 ≤ T)
    (hϖ : ϖ ≤ ϖ') : |cfgJump r i ϖ' T| ≤ |cfgJump r i ϖ T| := by
  have hrv' : 0 < r + ϖ' := by linarith
  rw [abs_of_neg (cfgJump_neg hrv' hri T), abs_of_neg (cfgJump_neg hrv hri T), neg_le_neg_iff,
    cfgJump, cfgJump]
  have e1 : (r + ϖ) / (i + ϖ) - 1 = -((i - r) / (i + ϖ)) := by
    rw [div_sub_one (by linarith), neg_div', neg_sub]; congr 1; ring
  have e2 : (r + ϖ') / (i + ϖ') - 1 = -((i - r) / (i + ϖ')) := by
    rw [div_sub_one (by linarith), neg_div', neg_sub]; congr 1; ring
  rw [e1, e2, mul_neg, mul_neg, neg_le_neg_iff]
  have hexp : Real.exp (-(r + ϖ') * T) ≤ Real.exp (-(r + ϖ) * T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hfrac : (i - r) / (i + ϖ') ≤ (i - r) / (i + ϖ) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  exact mul_le_mul hexp hfrac (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le

/-! ### Steady-state sales (Online Appendix p. 561) -/

/-- Cochrane (2023), Online Appendix p. 561: to keep the geometric structure
`B_{t−1}^{(t+j)} = ω^j B` the government sells, of each maturity `t + (j + 1)`, the amount
`B_t^{(t+j+1)} − B_{t−1}^{(t+j+1)} = ω^j B − ω^{j+1} B = ω^j(1−ω)B = ((1−ω)/ω) B_{t−1}^{(t+j+1)}`
every period. -/
theorem steady_sales {ω B : ℝ} (hω : ω ≠ 0) (j : ℕ) :
    ω ^ j * B - ω ^ (j + 1) * B = ω ^ j * (1 - ω) * B ∧
      ω ^ j * B - ω ^ (j + 1) * B = (1 - ω) / ω * (ω ^ (j + 1) * B) := by
  constructor
  · ring
  · field_simp
    ring

end Cochrane.LongTermDebtDynamics.ForwardGuidance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maturing debt, the long-term-debt buffer, and roll-over runs

Cochrane (2023), §7.2.1 (pp. 216–218, equation (7.6)) and §7.2.2 (pp. 218–220, equation (7.7) and
the backward-induction display on p. 219).

## Main results

* `debt_eq_initial`, `price_eq_maturing` — (7.6): with no sales or repurchases after the
  inherited structure, `B_{−1}^{(t)}/P_t = B_{t−1}^{(t)}/P_t = s_t` at every date.
* `noSales_solution`: conversely `x_t = s_t / B_{−1}^{(t)}` solves every flow condition.
* `noSales_presentValue`: the present-value relation still holds, term by term.
* `noSales_E_price`, `noSales_bondPrice`: news about `s_{t+j}` moves `E_t(1/P_{t+j})` and the bond
  price `Q_t^{(t+j)} = β^j P_t E_t(s_{t+j})/B^{(t+j)}`.
* `noSales_price_news`, `noSales_bond_news`, `noSales_price_indep`: the buffer: unexpected
  inflation at `t` reflects only news about `s_t`; news about later surpluses shows up in bond
  prices only.
* `oneperiod_flow_iff` — (7.7): with one-period debt only, `B_{t−1}^{(t)}/P_t =
  s_t + β B_t^{(t+1)} E_t(1/P_{t+1})`, and `oneperiod_flow_E` the form with `E_t` outside.
* `oneperiod_backward`, `oneperiod_two_period` — the backward-induction ("run") recursion of
  p. 219: with the debt retired at `T`, `B_{t−1}^{(t)}/P_t = ∑_{k ≤ T−t} β^k E_t s_{t+k}`.
* `oneperiod_fear`: lower expected far-future surpluses raise today's price level.
-/

namespace Cochrane.LongTermDebtDynamics.MaturingDebt

open MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.2.1, p. 216: the government neither sells nor repurchases debt after it
inherits the maturity structure: `B_t^{(t+j)} = B_{t−1}^{(t+j)}` for every `t` and `j ≥ 1`. -/
def NoSales (D : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, D (t + 1) (t + (j + 1)) = D t (t + (j + 1))

/-- Cochrane (2023), §7.2.1, p. 216: with no sales, the bond outstanding at 0 becomes the bond
maturing at `t`: `B_{t−1}^{(t+k)} = B_{−1}^{(t+k)}`. -/
theorem debt_eq_initial {D : ℕ → ℕ → Ω → ℝ} (h : NoSales D) (t k : ℕ) :
    D t (t + k) = D 0 (t + k) := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 + k = t + (k + 1) by omega, h t k, ih]

/-- Cochrane (2023), eq. (7.6), p. 217: with no sales, the flow condition at `t` reads
`B_{−1}^{(t)}/P_t = B_{t−1}^{(t)}/P_t = s_t`. -/
theorem price_eq_maturing {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : NoSales D)
    {t : ℕ} (hflow : RealFlow 𝔼 β D x s t) (ω : Ω) : D 0 t ω * x t ω = s t ω := by
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  have h0 := hflow ω
  rw [hz] at h0
  have := h0.unique hasSum_zero
  have hD := debt_eq_initial h t 0
  rw [add_zero] at hD
  rw [← hD]
  linarith

/-- Cochrane (2023), eq. (7.6), p. 217: conversely, with no sales and `B_{−1}^{(t)} ≠ 0`, the
price levels `x_t = 1/P_t = s_t / B_{−1}^{(t)}` satisfy every flow condition. -/
theorem noSales_solution {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : NoSales D)
    (hD : ∀ t ω, D 0 t ω ≠ 0) (hx : ∀ t ω, x t ω = s t ω / D 0 t ω) (t : ℕ) :
    RealFlow 𝔼 β D x s t := by
  intro ω
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  rw [hz]
  have hD0 := debt_eq_initial h t 0
  rw [add_zero] at hD0
  rw [hD0, hx t ω, mul_div_cancel₀ _ (hD t ω), sub_self]
  exact hasSum_zero

/-- Cochrane (2023), §7.2.1, p. 217: with no sales, `B^{(t+j)} E_t(1/P_{t+j}) = E_t s_{t+j}`, so
news about the surplus `s_{t+j}` moves `E_t(1/P_{t+j})` one for one. -/
theorem noSales_E_price (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + j) * 𝔼.E t (x (t + j)) = 𝔼.E t (s (t + j)) := by
  have hm : D 0 (t + j) * x (t + j) = s (t + j) := by
    funext ω; exact price_eq_maturing 𝔼 h (hflow (t + j)) ω
  rw [← hpo t _ _ (Predetermined.known 𝔼 hD (Nat.zero_le t) _), hm]

/-- Cochrane (2023), §7.2.1, p. 217: with no sales the bond price is
`Q_t^{(t+j)} B^{(t+j)} = β^j P_t E_t s_{t+j}`: bad news about `s_{t+j}` lowers the bond price. -/
theorem noSales_bondPrice (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + j) * bondPrice 𝔼 β P x t j = β ^ j • (P t * 𝔼.E t (s (t + j))) := by
  rw [bondPrice_eq 𝔼 hpo hP, ← noSales_E_price 𝔼 hpo hD h hflow t j]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §7.2.1, p. 217: with no sales and bounded surpluses, the present-value
relation (7.2) still holds at every date, term by term. -/
theorem noSales_presentValue (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : NoSales D)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t : ℕ) :
    PresentValue 𝔼 β D x s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  have heq : (fun j => debtTerm 𝔼 β D x t j ω) = fun j => surplusTerm 𝔼 β s t j ω := by
    funext j
    rw [debtTerm, surplusTerm, debt_eq_initial h t j]
    congr 1
    exact congrFun (noSales_E_price 𝔼 hpo hD h hflow t j) ω
  rw [heq]
  exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum

/-- Cochrane (2023), §7.2.1, p. 217 (the buffer): with no sales, the unexpected price level at
`t + 1` reflects only news about the current surplus,
`B^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) = s_{t+1} − E_t s_{t+1}`. -/
theorem noSales_price_news (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t : ℕ) :
    D 0 (t + 1) * (x (t + 1) - 𝔼.E t (x (t + 1))) = s (t + 1) - 𝔼.E t (s (t + 1)) := by
  have hm : D 0 (t + 1) * x (t + 1) = s (t + 1) := by
    funext ω; exact price_eq_maturing 𝔼 h (hflow (t + 1)) ω
  rw [mul_sub, hm, noSales_E_price 𝔼 hpo hD h hflow t 1]

/-- Cochrane (2023), §7.2.1, p. 217 (the buffer): news at `t + 1` about a later surplus
`s_{t+1+j}` moves the expected future price level (and hence bond prices) one for one,
`B^{(t+1+j)} (E_{t+1} − E_t)(1/P_{t+1+j}) = (E_{t+1} − E_t) s_{t+1+j}`. -/
theorem noSales_bond_news (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + 1 + j) * (𝔼.E (t + 1) (x (t + 1 + j)) - 𝔼.E t (x (t + 1 + j))) =
      𝔼.E (t + 1) (s (t + 1 + j)) - 𝔼.E t (s (t + 1 + j)) := by
  have h1 := noSales_E_price 𝔼 hpo hD h hflow (t + 1) j
  have h2 := noSales_E_price 𝔼 hpo hD h hflow t (1 + j)
  rw [← add_assoc] at h2
  rw [mul_sub, h1, h2]

/-- Cochrane (2023), §7.2.1, pp. 216–217: with no sales, two surplus paths that agree at `t`
(differing only in later surpluses) give the same price level at `t`. -/
theorem noSales_price_indep {β β' : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x x' s s' : ℕ → Ω → ℝ}
    (h : NoSales D) {t : ℕ} (hD : ∀ ω, D 0 t ω ≠ 0) (hflow : RealFlow 𝔼 β D x s t)
    (hflow' : RealFlow 𝔼 β' D x' s' t) (hs : s t = s' t) : x t = x' t := by
  funext ω
  have h1 := price_eq_maturing 𝔼 h hflow ω
  have h2 := price_eq_maturing 𝔼 h hflow' ω
  rw [congrFun hs ω] at h1
  exact mul_left_cancel₀ (hD ω) (h1.trans h2.symm)

/-! ### One-period debt and the roll-over run (§7.2.2) -/

/-- Cochrane (2023), §7.2.2, p. 219: only one-period debt is ever outstanding:
`B_{t−1}^{(t+j)} = 0` for `j ≥ 1` at every date. -/
def OnePeriod (D : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, D t (t + (j + 1)) = 0

/-- Cochrane (2023), eq. (7.7), p. 219: with one-period debt the flow condition (7.1) is
`B_{t−1}^{(t)}/P_t = s_t + β B_t^{(t+1)} E_t(1/P_{t+1})`. -/
theorem oneperiod_flow_iff {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : OnePeriod D)
    (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔
      D t t * x t = s t + β • (D (t + 1) (t + 1) * 𝔼.E t (x (t + 1))) := by
  have hterms : ∀ ω, (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = Pi.single 0
        (β * (D (t + 1) (t + 1) ω * 𝔼.E t (x (t + 1)) ω)) := by
    intro ω
    funext j
    rcases j with _ | j
    · simp [sales, h t 0]
    · have h1 := h (t + 1) j
      rw [show t + 1 + (j + 1) = t + (j + 1 + 1) by omega] at h1
      simp [sales, h1, h t (j + 1)]
  constructor
  · intro hf
    funext ω
    have := (hf ω).unique (by rw [hterms ω]; exact hasSum_pi_single 0 _)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro he ω
    rw [hterms ω]
    have := congrFun he ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    convert hasSum_pi_single 0 _ using 1
    linarith

/-- Cochrane (2023), eq. (7.7), p. 219: the same condition with the expectation outside,
`B_{t−1}^{(t)}/P_t = s_t + E_t(β B_t^{(t+1)}/P_{t+1})` (pull-out of the known `B_t^{(t+1)}`). -/
theorem oneperiod_flow_E (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : OnePeriod D) (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔
      D t t * x t = s t + 𝔼.E t (β • (D (t + 1) (t + 1) * x (t + 1))) := by
  rw [oneperiod_flow_iff 𝔼 h, map_smul, hpo t _ _ (hD.2 t _)]

/-- Cochrane (2023), §7.2.2, p. 219 (backward induction): with one-period debt that is retired at
`T` (`B_T^{(T+1)} = 0`), the real value of maturing debt at `t ≤ T` is the finite present value
`B_{t−1}^{(t)}/P_t = ∑_{k ≤ T−t} β^k E_t s_{t+k}`. -/
theorem oneperiod_backward (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s) {T : ℕ}
    (hT : D (T + 1) (T + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) {t : ℕ} (htT : t ≤ T) :
    D t t * x t = ∑ k ∈ Finset.range (T - t + 1), β ^ k • 𝔼.E t (s (t + k)) := by
  have hf : ∀ t, D t t * x t = s t + 𝔼.E t (β • (D (t + 1) (t + 1) * x (t + 1))) :=
    fun t => (oneperiod_flow_E 𝔼 hpo hD h t).mp (hflow t)
  -- prove for `t = T - n` with `n ≤ T`, by induction on `n`
  have key : ∀ n, n ≤ T → D (T - n) (T - n) * x (T - n) =
      ∑ k ∈ Finset.range (n + 1), β ^ k • 𝔼.E (T - n) (s (T - n + k)) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.sub_zero, hf T, hT]
      simp [hs T]
    | succ n ih =>
      intro hn
      have ht : T - n = T - (n + 1) + 1 := by omega
      rw [hf (T - (n + 1)), ← ht, ih (by omega)]
      conv_rhs => rw [Finset.sum_range_succ']
      rw [map_smul, map_sum, Finset.smul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, 𝔼.tower (by omega : T - (n + 1) ≤ T - n), smul_smul, ← pow_succ',
          show T - n + k = T - (n + 1) + (k + 1) by omega]
      · simp [hs (T - (n + 1))]
  have := key (T - t) (Nat.sub_le T t)
  rwa [Nat.sub_sub_self htT] at this

/-- Cochrane (2023), §7.2.2, p. 219: the last two steps of the backward induction,
`B_{T−2}^{(T−1)}/P_{T−1} = s_{T−1} + E_{T−1}(β s_T)` when the debt is retired at `T` (here with
last payment date `T + 1`). -/
theorem oneperiod_two_period (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s) {T : ℕ}
    (hT : D (T + 1 + 1) (T + 1 + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) :
    D T T * x T = s T + 𝔼.E T (β • s (T + 1)) := by
  have := oneperiod_backward 𝔼 hpo hD h hs hT hflow (t := T) (by omega)
  rw [show T + 1 - T + 1 = 2 by omega] at this
  rw [this, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_smul, pow_one, add_zero,
    hs, map_smul]

/-- Cochrane (2023), §7.2.2, pp. 219–220: fear of low surpluses far in the future raises today's
price level: with one-period debt retired at `T`, positive maturing debt, and two surplus
processes with `s' ≤ s`, the price levels satisfy `1/P'_t ≤ 1/P_t` at every `t ≤ T`. -/
theorem oneperiod_fear (hpo : 𝔼.PullOut) {β : ℝ} (hβ : 0 ≤ β) {D : ℕ → ℕ → Ω → ℝ}
    {x x' s s' : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s)
    (hs' : 𝔼.Adapted s') {T : ℕ} (hT : D (T + 1) (T + 1) = 0) (hpos : ∀ t ω, 0 < D t t ω)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s' t)
    (hss : ∀ t, s' t ≤ s t) {t : ℕ} (htT : t ≤ T) (ω : Ω) : x' t ω ≤ x t ω := by
  have h1 := congrFun (oneperiod_backward 𝔼 hpo hD h hs hT hflow htT) ω
  have h2 := congrFun (oneperiod_backward 𝔼 hpo hD h hs' hT hflow' htT) ω
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hle : D t t ω * x' t ω ≤ D t t ω * x t ω := by
    rw [h1, h2]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (𝔼.mono _ (hss _) ω) (pow_nonneg hβ k)
  exact le_of_mul_le_mul_left hle (hpos _ ω)

end Cochrane.LongTermDebtDynamics.MaturingDebt

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bond sales and bond-price targets

Cochrane (2023), §7.3 and §7.3.1–7.3.2, pp. 220–224, equations (7.8)–(7.13).

The government inherits `B_{−1}^{(j)} = D 0 j`, sells `B_0^{(j)} − B_{−1}^{(j)}` at date 0
(`B_0^{(j)} = D 1 j`) and never trades again.

## Main results

* `maturing_eq` — (7.9): `B_0^{(j)}/P_j = s_j` for `j ≥ 1`.
* `E_price_eq` — `B_0^{(j)} E_0(1/P_j) = E_0 s_j`; `bondPrice_mul_debt` — (7.10);
  `real_revenue` — (7.11): `Q_0^{(j)} B_0^{(j)}/P_0 = β^j E_0 s_j`, independent of the amount sold.
* `dilution_formula` — (7.12): `B_{−1}^{(0)}/P_0 =
  s_0 + ∑_{j≥1} β^j ((B_0^{(j)} − B_{−1}^{(j)})/B_0^{(j)}) E_0 s_j`.
* `no_outstanding` — (7.13), and `no_outstanding_price_indep`: with no long-term debt outstanding,
  `P_0` does not depend on the sales.
* `sales_lower_bondPrice`, `sales_raise_future_price`: additional sales lower bond prices and raise
  future price levels.
* `bondPrice_target_iff`: a bond-price target is supported by a unique, finite quantity of debt;
  `unit_elasticity`: `d log B / d log Q = −1`.
* `outstanding_sales_lower_price`, `hasDerivAt_dilution`: with long-term debt outstanding,
  additional sales raise revenue and lower `P_0`.
* `offset_shock`: a state-contingent sale can offset a surplus shock at date 0, at the cost of a
  higher future price level.
-/

namespace Cochrane.LongTermDebtDynamics.BondSales

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.3, p. 221: debt is sold or bought at date 0 only: `B_t^{(t+j)} =
B_{t−1}^{(t+j)}` for every `t ≥ 1` and `j ≥ 1`. -/
def SalesAtZeroOnly (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ t j, D (t + 2) (t + 1 + (j + 1)) = D (t + 1) (t + 1 + (j + 1))

/-- Cochrane (2023), §7.3, p. 221: after date 0 the debt outstanding is `B_0^{(m)}`. -/
theorem debt_eq_one {D : ℕ → ℕ → Ω → ℝ} (h : SalesAtZeroOnly D) (t k : ℕ) :
    D (t + 1) (t + 1 + k) = D 1 (t + 1 + k) := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 + 1 + k = t + 1 + (k + 1) by omega, h t k, ih]

/-- Cochrane (2023), eq. (7.9), p. 221: after the date-0 sales each surplus pays off the debt
maturing at its date, `B_0^{(t)}/P_t = s_t` for `t ≥ 1`. -/
theorem maturing_eq {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : SalesAtZeroOnly D)
    {t : ℕ} (hflow : RealFlow 𝔼 β D x s (t + 1)) (ω : Ω) : D 1 (t + 1) ω * x (t + 1) ω =
      s (t + 1) ω := by
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  have h0 := hflow ω
  rw [hz] at h0
  have := h0.unique hasSum_zero
  have hD := debt_eq_one h t 0
  rw [add_zero] at hD
  rw [← hD]
  linarith

/-- Cochrane (2023), eqs. (7.9)–(7.10), p. 221: `B_0^{(j)} E_0(1/P_j) = E_0 s_j` for `j ≥ 1`
(pull-out of the date-0 choice `B_0^{(j)}`). -/
theorem E_price_eq (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (j : ℕ) : D 1 (j + 1) * 𝔼.E 0 (x (j + 1)) = 𝔼.E 0 (s (j + 1)) := by
  have hm : D 1 (j + 1) * x (j + 1) = s (j + 1) := by
    funext ω; exact maturing_eq 𝔼 h (hflow (j + 1)) ω
  rw [← hpo 0 _ _ (hD.2 0 _), hm]

/-- Cochrane (2023), eq. (7.10), p. 221: `Q_0^{(j)} = β^j E_0(P_0/P_j)`, so
`Q_0^{(j)} B_0^{(j)} = β^j P_0 E_0 s_j`. -/
theorem bondPrice_mul_debt (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) :
    bondPrice 𝔼 β P x 0 (j + 1) * D 1 (j + 1) = β ^ (j + 1) • (P 0 * 𝔼.E 0 (s (j + 1))) := by
  rw [bondPrice_eq 𝔼 hpo hP, ← E_price_eq 𝔼 hpo hD h hflow j]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, zero_add]
  ring

/-- Cochrane (2023), eq. (7.11), p. 221: the real end-of-period value of date-`j` debt is
`Q_0^{(j)} B_0^{(j)}/P_0 = β^j E_0 s_j`, independent of the amount sold. -/
theorem real_revenue (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) (ω : Ω) :
    bondPrice 𝔼 β P x 0 (j + 1) ω * D 1 (j + 1) ω * x 0 ω =
      β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω := by
  have := congrFun (bondPrice_mul_debt 𝔼 hpo hD h hP hflow j) ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [this]
  linear_combination (β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω) * hPx 0 ω

/-- Cochrane (2023), eq. (7.12), p. 222: **the dilution formula.** With sales at date 0 only and
`B_0^{(j)} ≠ 0`,
`B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^j ((B_0^{(j)} − B_{−1}^{(j)})/B_0^{(j)}) E_0 s_j`,
a genuine convergent series. -/
theorem dilution_formula (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * ((D 1 (j + 1) ω - D 0 (j + 1) ω) / D 1 (j + 1) ω *
      𝔼.E 0 (s (j + 1)) ω)) (D 0 0 ω * x 0 ω - s 0 ω) := by
  refine (hflow 0 ω).congr_fun fun j => ?_
  have he := congrFun (E_price_eq 𝔼 hpo hD h hflow j) ω
  simp only [Pi.mul_apply] at he
  simp only [sales, zero_add, Pi.sub_apply]
  rw [← he]
  field_simp [hD1 j ω]

/-- Cochrane (2023), eq. (7.13), p. 222: with no long-term debt outstanding
(`B_{−1}^{(j)} = 0`, `j ≥ 1`), `B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^j E_0 s_j`. -/
theorem no_outstanding (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hD0 : ∀ j, D 0 (j + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω) (D 0 0 ω * x 0 ω - s 0 ω) := by
  refine (dilution_formula 𝔼 hpo hD h hD1 hflow ω).congr_fun fun j => ?_
  rw [hD0 j, Pi.zero_apply, sub_zero, div_self (hD1 j ω), one_mul]

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): with no long-term debt outstanding, `P_0` is
determined by fiscal shocks alone: two debt policies with the same inherited debt and surpluses
give the same `P_0`, whatever the amounts sold. -/
theorem no_outstanding_price_indep (hpo : 𝔼.PullOut) {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ}
    {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hD' : Predetermined 𝔼 D')
    (h : SalesAtZeroOnly D) (h' : SalesAtZeroOnly D') (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hD1' : ∀ j ω, D' 1 (j + 1) ω ≠ 0) (hD0 : ∀ j, D 0 (j + 1) = 0) (hinit : D 0 0 = D' 0 0)
    (hD00 : ∀ ω, D 0 0 ω ≠ 0) (hD0' : ∀ j, D' 0 (j + 1) = 0)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D' x' s t) :
    x 0 = x' 0 := by
  funext ω
  have h1 := (no_outstanding 𝔼 hpo hD h hD1 hD0 hflow ω).unique
    (no_outstanding 𝔼 hpo hD' h' hD1' hD0' hflow' ω)
  rw [← hinit] at h1
  exact mul_left_cancel₀ (hD00 ω) (by linarith)

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): additional sales lower the bond price: with
`Q_0^{(j)} B_0^{(j)} = β^j P_0 E_0 s_j > 0` fixed, a larger `B_0^{(j)}` means a lower
`Q_0^{(j)}`. -/
theorem sales_lower_bondPrice {c b b' q q' : ℝ} (hc : 0 < c) (hb : 0 < b) (hbb' : b < b')
    (hq : q * b = c) (hq' : q' * b' = c) : q' < q := by
  have hb' : 0 < b' := hb.trans hbb'
  have e1 : q = c / b := by rw [eq_div_iff hb.ne']; exact hq
  have e2 : q' = c / b' := by rw [eq_div_iff hb'.ne']; exact hq'
  rw [e1, e2]
  exact div_lt_div_of_pos_left hc hb hbb'

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): additional sales raise the future price level:
`1/P_j = s_j / B_0^{(j)}` falls when `B_0^{(j)}` rises (for `s_j > 0`). -/
theorem sales_raise_future_price {sj b b' x x' : ℝ} (hs : 0 < sj) (hb : 0 < b) (hbb' : b < b')
    (hx : b * x = sj) (hx' : b' * x' = sj) : x' < x := by
  have hb' : 0 < b' := hb.trans hbb'
  have e1 : x = sj / b := by rw [eq_div_iff hb.ne', mul_comm]; exact hx
  have e2 : x' = sj / b' := by rw [eq_div_iff hb'.ne', mul_comm]; exact hx'
  rw [e1, e2]
  exact div_lt_div_of_pos_left hs hb hbb'

/-- Cochrane (2023), §7.3.1, p. 223 (bullet): the government can target the long-term bond price
`Q_0^{(j)} = q ≠ 0` by trading freely at that price; the quantity sold is then finite and unique,
`B_0^{(j)} = β^j P_0 E_0 s_j / q` (from (7.11)). -/
theorem bondPrice_target_iff (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) {q : ℝ} (hq : q ≠ 0) (ω : Ω)
    (hQ : bondPrice 𝔼 β P x 0 (j + 1) ω = q) :
    D 1 (j + 1) ω = β ^ (j + 1) * P 0 ω * 𝔼.E 0 (s (j + 1)) ω / q := by
  have := congrFun (bondPrice_mul_debt 𝔼 hpo hD h hP hflow j) ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hQ] at this
  rw [eq_div_iff hq, mul_comm, this]
  ring

/-- Cochrane (2023), §7.3.1, p. 223: unit elasticity: along the demand curve `B = c/Q`
(from (7.11)), `d log B / d log Q = −1`. -/
theorem unit_elasticity (c u : ℝ) (hc : 0 < c) :
    HasDerivAt (fun v => Real.log (c / Real.exp v)) (-1) u := by
  have : (fun v => Real.log (c / Real.exp v)) = fun v => Real.log c - v := by
    funext v
    rw [Real.log_div hc.ne' (Real.exp_pos v).ne', Real.log_exp]
  rw [this]
  simpa using (hasDerivAt_id u).const_sub (Real.log c)

/-- Cochrane (2023), §7.3.2, p. 223 (bullet): **with long-term debt outstanding, additional sales
lower `P_0`.** Compare two policies with the same inherited debt (`B_{−1}^{(j)} ≥ 0`, `B_{−1}^{(0)}
> 0`) and surpluses (`E_0 s_j ≥ 0`), where the second sells weakly more of every maturity, and
strictly more of a maturity `j` with `B_{−1}^{(j)} > 0`, `E_0 s_j > 0`: then `1/P_0` is strictly
higher. -/
theorem outstanding_sales_lower_price {β : ℝ} (hβ : 0 < β) {d0 b b' e : ℕ → ℝ}
    {D00 s0 x0 x0' : ℝ} (hD00 : 0 < D00) (hd : ∀ j, 0 ≤ d0 j) (hb : ∀ j, 0 < b j)
    (hbb' : ∀ j, b j ≤ b' j) (he : ∀ j, 0 ≤ e j) {j₀ : ℕ} (hd₀ : 0 < d0 j₀)
    (hb₀ : b j₀ < b' j₀) (he₀ : 0 < e j₀)
    (hx : HasSum (fun j => β ^ (j + 1) * ((b j - d0 j) / b j * e j)) (D00 * x0 - s0))
    (hx' : HasSum (fun j => β ^ (j + 1) * ((b' j - d0 j) / b' j * e j)) (D00 * x0' - s0)) :
    x0 < x0' := by
  have hmono : ∀ j, (b j - d0 j) / b j ≤ (b' j - d0 j) / b' j := by
    intro j
    have hb' : 0 < b' j := (hb j).trans_le (hbb' j)
    rw [sub_div, sub_div, div_self (hb j).ne', div_self hb'.ne']
    exact sub_le_sub_left (div_le_div_of_nonneg_left (hd j) (hb j) (hbb' j)) 1
  have hlt : (b j₀ - d0 j₀) / b j₀ < (b' j₀ - d0 j₀) / b' j₀ := by
    have hb' : 0 < b' j₀ := (hb j₀).trans hb₀
    rw [sub_div, sub_div, div_self (hb j₀).ne', div_self hb'.ne']
    exact sub_lt_sub_left (div_lt_div_of_pos_left hd₀ (hb j₀) hb₀) 1
  have := hasSum_lt (f := fun j => β ^ (j + 1) * ((b j - d0 j) / b j * e j))
    (g := fun j => β ^ (j + 1) * ((b' j - d0 j) / b' j * e j)) (i := j₀)
    (fun j => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmono j) (he j))
      (pow_nonneg hβ.le _))
    (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hlt he₀) (pow_pos hβ _)) hx hx'
  nlinarith

/-- Cochrane (2023), §7.3.2, p. 223: the marginal effect of selling more maturity-`j` debt on
`1/P_0`: with `B_{−1}^{(0)}/P_0 = c + β^j (1 − B_{−1}^{(j)}/B_0^{(j)}) E_0 s_j`, the derivative with
respect to `B_0^{(j)} = b` is `β^j B_{−1}^{(j)} E_0 s_j / (b² B_{−1}^{(0)}) > 0`. -/
theorem hasDerivAt_dilution (c βj d e D00 b : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun v => (c + βj * (1 - d / v) * e) / D00) (βj * d * e / (b ^ 2 * D00)) b := by
  have h1 : HasDerivAt (fun v => d / v) (-(d / b ^ 2)) b := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hb).const_mul d
  have h2 := ((((h1.const_sub 1).const_mul βj).mul_const e).const_add c).div_const D00
  convert h2 using 1
  field_simp

/-- Cochrane (2023), §7.3.2, p. 224 (bullet): **a state-contingent sale can offset a surplus
shock.** If the date-0 surplus falls by `δ ≥ 0` and the revenue from maturity `j`
(`R = β^j (1 − d/b) e`, `d = B_{−1}^{(j)} > 0`, `e = E_0 s_j > 0`) can rise by `δ`
(`R + δ < β^j e`),
there is a sale `b' ≥ b` raising exactly the extra revenue `δ`, so `P_0` is unchanged; when
`δ > 0` the sale is strictly larger, raising the future price level `P_j = b'/s_j`. -/
theorem offset_shock {βj d e b δ : ℝ} (hβ : 0 < βj) (hd : 0 < d) (he : 0 < e) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hR : βj * (1 - d / b) * e + δ < βj * e) :
    ∃ b', b ≤ b' ∧ βj * (1 - d / b') * e = βj * (1 - d / b) * e + δ ∧ (0 < δ → b < b') := by
  set R := βj * (1 - d / b) * e + δ with hRdef
  have hpos : 0 < βj * e - R := by linarith
  refine ⟨d * (βj * e) / (βj * e - R), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    have : βj * e - R = βj * e * d / b - δ := by rw [hRdef]; field_simp; ring
    rw [this]
    have hbe : 0 < βj * e := mul_pos hβ he
    have : b * (βj * e * d / b - δ) = βj * e * d - b * δ := by field_simp
    rw [this]
    nlinarith [mul_nonneg hb.le hδ]
  · have hne : βj * e - R ≠ 0 := hpos.ne'
    have hd0 : d ≠ 0 := hd.ne'
    have hbe : βj * e ≠ 0 := (mul_pos hβ he).ne'
    field_simp
    ring
  · intro hδpos
    rw [lt_div_iff₀ hpos]
    have : βj * e - R = βj * e * d / b - δ := by rw [hRdef]; field_simp; ring
    rw [this]
    have : b * (βj * e * d / b - δ) = βj * e * d - b * δ := by field_simp
    rw [this]
    nlinarith [mul_pos hb hδpos]

end Cochrane.LongTermDebtDynamics.BondSales

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expected future bond sales: the three-period economy

Cochrane (2023), §7.3.3, p. 224, and Online Appendix §A1.14, pp. 588–592, equations
(1.63)–(1.68).

Dates 0, 1, 2. Inherited debt `B_{−1}^{(0)}, B_{−1}^{(1)}, B_{−1}^{(2)}` (`D 0 0`, `D 0 1`, `D 0
2`);
at date 0 the government sells time-1 and time-2 debt (`B_0^{(1)} = D 1 1`, `B_0^{(2)} = D 1 2`);
at date 1 it may sell more time-2 debt, `B_1^{(2)} − B_0^{(2)}` (`B_1^{(2)} = D 2 2`), the expected
future sale. Surpluses are unchanged throughout.

## Main results

* `flows_of_realFlow`: the general flow conditions (7.1) reduce to the three flow equations.
* `price_two` (1.63), `price_one` (1.64), `price_zero` (1.65)/(1.66).
* `no_outstanding_price_zero`: with no long-term debt outstanding the expected sale has no effect on
  `P_0` (§A1.14.1).
* `price_two_symm`, `bondPrice_two_symm`: future sales enter symmetrically with date-0 sales in
  `P_2` and (with no outstanding debt) in `Q_0^{(2)}`; a date-0 purchase can be undone by an
  expected future sale.
* `x1_formula`, `future_sales_raise_Q1`: expected sales raise `E_0(1/P_1)` and the bond price
  `Q_0^{(1)}` when time-2 debt has been sold.
* `no_time0_sales`: with no date-0 sales the expected sale has no effect on `P_0` (interaction
  only).
* `price_zero_no_sale_two` (1.67), `price_zero_no_sale_one` (1.68).
* `x0_closed`, `hasDerivAt_x0`, `x0_strictMono`, `x0_strictAnti`, `x0_const`: the sign of the
  effect of expected sales on `P_0` is the sign of `A₂ − A₁`, with
  `A_k = (B_0^{(k)} − B_{−1}^{(k)})/B_0^{(k)}`.
-/

namespace Cochrane.LongTermDebtDynamics.FutureSales

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix §A1.14, pp. 589–590: in the three-period economy (no debt
maturing after date 2) the flow conditions (7.1) at dates 0, 1, 2 are the three displayed
equations. -/
theorem flows_of_realFlow {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β D x s 0) (h1 : RealFlow 𝔼 β D x s 1)
    (h2 : RealFlow 𝔼 β D x s 2) :
    D 2 2 * x 2 = s 2 ∧
      D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)) ∧
      D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
        β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales D 2 (2 + (j + 1)) ω *
        𝔼.E 2 (x (2 + (j + 1))) ω)) = fun _ => 0 := by
      funext j
      simp [sales, show 2 + (j + 1) = j + 3 by omega, hD3]
    have := (h2 ω)
    rw [hz] at this
    have := this.unique hasSum_zero
    simp only [Pi.mul_apply]
    linarith
  · funext ω
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales D 1 (1 + (j + 1)) ω *
        𝔼.E 1 (x (1 + (j + 1))) ω)) =
        Pi.single 0 (β * ((D 2 2 ω - D 1 2 ω) * 𝔼.E 1 (x 2) ω)) := by
      funext j
      rcases j with _ | j
      · simp [sales]
      · simp [sales, show 1 + (j + 1 + 1) = j + 3 by omega, hD3]
    have := (h1 ω)
    rw [hz] at this
    have := this.unique (hasSum_pi_single 0 _)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    linarith
  · funext ω
    have hfin : ∀ j ∉ ({0, 1} : Finset ℕ), β ^ (j + 1) * (sales D 0 (0 + (j + 1)) ω *
        𝔼.E 0 (x (0 + (j + 1))) ω) = 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      simp [sales, show 0 + (k + 2 + 1) = k + 3 by omega, hD3]
    have := (h0 ω).unique (hasSum_sum_of_ne_finset_zero hfin)
    simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton,
      sales] at this
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    norm_num at this ⊢
    linarith

/-- Cochrane (2023), Online Appendix eq. (1.63), p. 589: `B_1^{(2)}/P_2 = s_2`, so total time-2 debt
`B_1^{(2)} = B_0^{(2)} + (B_1^{(2)} − B_0^{(2)})` sets `P_2`. -/
theorem price_two {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) : x 2 = s 2 / D 2 2 := by
  funext ω
  have := congrFun F2 ω
  simp only [Pi.mul_apply] at this
  simp only [Pi.div_apply]
  rw [eq_div_iff (hD22 ω), ← this, mul_comm]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `B_0^{(1)}/P_1 =
s_1 + β ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) E_1 s_2` (pull-out of the date-1 choice `B_1^{(2)}`). -/
theorem price_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2))) (hD22 : ∀ ω, D 2 2 ω ≠ 0) :
    D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * 𝔼.E 1 (s 2)) := by
  rw [F1, ← F2, hpo 1 _ _ (hD.2 1 _)]
  congr 2
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply]
  field_simp [hD22 ω]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `B_0^{(1)} E_0(1/P_1) =
E_0[s_1 + β ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]`. -/
theorem E_price_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2))) (hD22 : ∀ ω, D 2 2 ω ≠ 0) :
    D 1 1 * 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
  have hk : (D 2 2 - D 1 2) / D 2 2 * s 2 = (D 2 2 - D 1 2) * x 2 := by
    rw [← F2]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
    field_simp [hD22 ω]
  have hk1 : 𝔼.E 1 (D 2 2 - D 1 2) = D 2 2 - D 1 2 := by
    rw [map_sub, hD.2 1, Predetermined.known_succ 𝔼 hD (Nat.zero_le 1)]
  rw [← hpo 0 _ _ (hD.2 0 _), F1, hk, map_add, map_add, map_smul, map_smul,
    ← hpo 1 _ _ hk1, 𝔼.tower (Nat.zero_le 1)]

/-- Cochrane (2023), Online Appendix eq. (1.65)/(1.66), pp. 590–591: the date-0 price level,
`B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]
  + E_0[β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) s_2]`, with `A₁ = (B_0^{(1)} −
B_{−1}^{(1)})/B_0^{(1)}`. -/
theorem price_zero (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) :
    D 0 0 * x 0 = s 0 + (D 1 1 - D 0 1) / D 1 1 *
        𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) +
      𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / D 2 2 * s 2)) := by
  have h1 := E_price_one 𝔼 hpo hD F2 F1 hD22
  have h2 : 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / D 2 2 * s 2)) =
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)) := by
    have hk : (D 1 2 - D 0 2) / D 2 2 * s 2 = (D 1 2 - D 0 2) * x 2 := by
      rw [← F2]
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [hD22 ω]
    have hk0 : 𝔼.E 0 (D 1 2 - D 0 2) = D 1 2 - D 0 2 := by
      rw [map_sub, hD.2 0, hD.1]
    rw [hk, map_smul, hpo 0 _ _ hk0]
  rw [F0, h2]
  congr 1
  congr 1
  have hE : 𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) =
      β • 𝔼.E 0 (s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
    rw [← map_smul, smul_add, smul_smul, ← pow_two]
  rw [hE, ← h1]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, Pi.div_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hD11 ω]

/-- Cochrane (2023), Online Appendix §A1.14.1, p. 590: with no long-term debt outstanding
(`B_{−1}^{(1)} = B_{−1}^{(2)} = 0`), `B_{−1}^{(0)}/P_0 = s_0 + E_0(β s_1 + β² s_2)`: the expected
sale `B_1^{(2)} − B_0^{(2)}` has no effect on `P_0`. -/
theorem no_outstanding_price_zero (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h01 : D 0 1 = 0) (h02 : D 0 2 = 0) :
    D 0 0 * x 0 = s 0 + 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) := by
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h01, h02, add_assoc]
  congr 1
  have hA : (D 1 1 - 0) / D 1 1 = 1 := by
    funext ω; simp [div_self (hD11 ω)]
  rw [hA, one_mul, ← map_add]
  congr 1
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply,
    Pi.zero_apply, smul_eq_mul]
  field_simp [hD22 ω]
  ring

/-- Cochrane (2023), Online Appendix p. 589 (bullet): expected future sales enter symmetrically
with date-0 sales in `P_2`: two policies with the same total `B_1^{(2)}` give the same `P_2`. -/
theorem price_two_symm {D D' : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (F2' : D' 2 2 * x' 2 = s 2) (hD22 : ∀ ω, D 2 2 ω ≠ 0) (htot : D 2 2 = D' 2 2) :
    x 2 = x' 2 := by
  funext ω
  have h1 := congrFun F2 ω
  have h2 := congrFun F2' ω
  simp only [Pi.mul_apply] at h1 h2
  rw [← htot] at h2
  exact mul_left_cancel₀ (hD22 ω) (h1.trans h2.symm)

/-- Cochrane (2023), Online Appendix p. 590 (bullets): with `P_0` fixed (as with no outstanding
long-term debt), expected future sales enter symmetrically with date-0 sales in the bond price
`Q_0^{(2)}`: the same total `B_1^{(2)}` gives the same `Q_0^{(2)}`, so a date-0 purchase can be
undone
by an expected future sale. -/
theorem bondPrice_two_symm {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ} {P x x' s : ℕ → Ω → ℝ}
    (F2 : D 2 2 * x 2 = s 2) (F2' : D' 2 2 * x' 2 = s 2) (hD22 : ∀ ω, D 2 2 ω ≠ 0)
    (htot : D 2 2 = D' 2 2) :
    bondPrice 𝔼 β P x 0 2 = bondPrice 𝔼 β P x' 0 2 := by
  simp only [bondPrice, zero_add, price_two_symm F2 F2' hD22 htot]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590, with deterministic debt: writing
`F = B_1^{(2)} − B_0^{(2)}`, `B_0^{(1)} E_0(1/P_1) = E_0 s_1 + β (F/(B_0^{(2)} + F)) E_0 s_2`. -/
theorem x1_formula {β b1 b2 F : ℝ} {x s : ℕ → Ω → ℝ}
    (h : b1 • 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1 + β • ((b2 + F - b2) / (b2 + F)) • s 2)) :
    b1 • 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1) + (β * (F / (b2 + F))) • 𝔼.E 0 (s 2) := by
  rw [h, map_add, map_smul, map_smul, smul_smul]
  congr 2
  rw [add_sub_cancel_left]

/-- Cochrane (2023), Online Appendix p. 591 (bullet): if time-2 debt has been sold at date 0
(`B_0^{(2)} > 0`), expected future sales `F` raise `B_0^{(1)} E_0(1/P_1)` (lower the expected
`P_1`),
and hence raise the bond price `Q_0^{(1)} = β P_0 E_0(1/P_1)` when `P_0` is fixed:
`F ↦ F/(B_0^{(2)} + F)` is strictly increasing on `F > −B_0^{(2)}`. -/
theorem future_sales_raise_Q1 {b2 F F' : ℝ} (hb2 : 0 < b2) (hF : -b2 < F) (hFF' : F < F') :
    F / (b2 + F) < F' / (b2 + F') := by
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-- Cochrane (2023), Online Appendix §A1.14.2, p. 591 (bullet): expected future sales have only an
interaction effect: with no date-0 sales (`B_0^{(1)} = B_{−1}^{(1)}`, `B_0^{(2)} = B_{−1}^{(2)}`),
`B_{−1}^{(0)}/P_0 = s_0` whatever the date-1 sale. -/
theorem no_time0_sales (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h1 : D 1 1 = D 0 1)
    (h2 : D 1 2 = D 0 2) : D 0 0 * x 0 = s 0 := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h1, h2]
  simp only [sub_self, z1, map_zero, smul_zero, add_zero]

/-- Cochrane (2023), Online Appendix eq. (1.67), p. 592: with no date-0 sale of time-2 debt
(`B_0^{(2)} = B_{−1}^{(2)}`), `B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} −
B_0^{(2)})/B_1^{(2)})
s_2]`. -/
theorem price_zero_no_sale_two (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h2 : D 1 2 = D 0 2) :
    D 0 0 * x 0 = s 0 + (D 1 1 - D 0 1) / D 1 1 *
      𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h2]
  simp only [sub_self, z1, smul_zero, map_zero, add_zero]

/-- Cochrane (2023), Online Appendix eq. (1.68), p. 592: with no date-0 sale of time-1 debt
(`B_0^{(1)} = B_{−1}^{(1)}`), `B_{−1}^{(0)}/P_0 = s_0 + E_0[β² ((B_0^{(2)} − B_{−1}^{(2)}) /
(B_{−1}^{(2)} + (B_0^{(2)} − B_{−1}^{(2)}) + (B_1^{(2)} − B_0^{(2)}))) s_2]`: dilution is relative
to all
claims, including expected future sales. -/
theorem price_zero_no_sale_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h1 : D 1 1 = D 0 1) :
    D 0 0 * x 0 = s 0 + 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) /
      (D 0 2 + (D 1 2 - D 0 2) + (D 2 2 - D 1 2)) * s 2)) := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h1,
    show D 0 2 + (D 1 2 - D 0 2) + (D 2 2 - D 1 2) = D 2 2 by ring]
  simp only [sub_self, z1, add_zero]

/-! ### The sign of the effect of expected future sales on `P_0` (deterministic debt) -/

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, with deterministic debt and the expected
sale `F = B_1^{(2)} − B_0^{(2)}` as a parameter: `B_{−1}^{(0)}/P_0 = s_0 + A₁ β e_1 +
β² e_2 (A₁ F + B_0^{(2)} − B_{−1}^{(2)})/(B_0^{(2)} + F)`, with `e_k = E_0 s_k`. -/
noncomputable def x0Fun (s0 e1 e2 β A1 b2 d2 D00 F : ℝ) : ℝ :=
  (s0 + A1 * β * e1 + β ^ 2 * e2 * ((A1 * F + (b2 - d2)) / (b2 + F))) / D00

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591: the closed form agrees with (1.65) term by
term: `A₁ β² (F/B_1^{(2)}) e_2 + β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) e_2`. -/
theorem x0_closed {s0 e1 e2 β A1 b2 d2 D00 F : ℝ} (hD00 : D00 ≠ 0) (hb : b2 + F ≠ 0) :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F * D00 =
      s0 + A1 * (β * e1 + β ^ 2 * (F / (b2 + F)) * e2) + β ^ 2 * ((b2 - d2) / (b2 + F)) * e2 := by
  rw [x0Fun, div_mul_cancel₀ _ hD00]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 592: the derivative of `1/P_0` with respect to the expected
sale, `β² e_2 B_0^{(2)} (A₁ − A₂)/((B_0^{(2)} + F)² B_{−1}^{(0)})` with
`A₂ = (B_0^{(2)} − B_{−1}^{(2)})/B_0^{(2)}`. -/
theorem hasDerivAt_x0 (s0 e1 e2 β A1 b2 d2 D00 F : ℝ) (hb2 : b2 ≠ 0) (hb : b2 + F ≠ 0) :
    HasDerivAt (fun G => x0Fun s0 e1 e2 β A1 b2 d2 D00 G)
      (β ^ 2 * e2 * b2 * (A1 - (b2 - d2) / b2) / ((b2 + F) ^ 2 * D00)) F := by
  have hq : HasDerivAt (fun G => (A1 * G + (b2 - d2)) / (b2 + G))
      ((A1 * (b2 + F) - (A1 * F + (b2 - d2)) * 1) / (b2 + F) ^ 2) F := by
    have h1 : HasDerivAt (fun G => A1 * G + (b2 - d2)) A1 F := by
      simpa using ((hasDerivAt_id F).const_mul A1).add_const (b2 - d2)
    have h2 : HasDerivAt (fun G => b2 + G) 1 F := by
      simpa using (hasDerivAt_id F).const_add b2
    exact h1.div h2 hb
  have := ((hq.const_mul (β ^ 2 * e2)).const_add (s0 + A1 * β * e1)).div_const D00
  have hnum : A1 * (b2 + F) - (A1 * F + (b2 - d2)) * 1 = b2 * (A1 - (b2 - d2) / b2) := by
    field_simp
    ring
  rw [hnum] at this
  unfold x0Fun
  convert this using 1
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (bullet): **if the government sells proportionally
more time-1 than time-2 debt at date 0 (`A₁ > A₂`), expected future sales lower `P_0`:** with
`E_0 s_2 > 0`, `B_0^{(2)} > 0`, `B_{−1}^{(0)} > 0`, `1/P_0` is strictly increasing in `F` on
`F > −B_0^{(2)}`. -/
theorem x0_strictMono {s0 e1 e2 β A1 b2 d2 D00 F F' : ℝ} (he2 : 0 < e2) (hβ : β ≠ 0)
    (hb2 : 0 < b2) (hD00 : 0 < D00) (hA : (b2 - d2) / b2 < A1) (hF : -b2 < F) (hFF' : F < F') :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F < x0Fun s0 e1 e2 β A1 b2 d2 D00 F' := by
  unfold x0Fun
  apply div_lt_div_of_pos_right _ hD00
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  have hβ2 : 0 < β ^ 2 * e2 := mul_pos (lt_of_le_of_ne (sq_nonneg β) (pow_ne_zero 2 hβ).symm) he2
  have hA' : b2 - d2 < A1 * b2 := by rwa [div_lt_iff₀ hb2] at hA
  have : (A1 * F + (b2 - d2)) / (b2 + F) < (A1 * F' + (b2 - d2)) / (b2 + F') := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  nlinarith

/-- Cochrane (2023), Online Appendix p. 592: conversely, if `A₁ < A₂`, expected future sales raise
`P_0`: `1/P_0` is strictly decreasing in `F` on `F > −B_0^{(2)}`. -/
theorem x0_strictAnti {s0 e1 e2 β A1 b2 d2 D00 F F' : ℝ} (he2 : 0 < e2) (hβ : β ≠ 0)
    (hb2 : 0 < b2) (hD00 : 0 < D00) (hA : A1 < (b2 - d2) / b2) (hF : -b2 < F) (hFF' : F < F') :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F' < x0Fun s0 e1 e2 β A1 b2 d2 D00 F := by
  unfold x0Fun
  apply div_lt_div_of_pos_right _ hD00
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  have hβ2 : 0 < β ^ 2 * e2 := mul_pos (lt_of_le_of_ne (sq_nonneg β) (pow_ne_zero 2 hβ).symm) he2
  have hA' : A1 * b2 < b2 - d2 := by rwa [lt_div_iff₀ hb2] at hA
  have : (A1 * F' + (b2 - d2)) / (b2 + F') < (A1 * F + (b2 - d2)) / (b2 + F) := by
    rw [div_lt_div_iff₀ h2 h1]
    nlinarith
  nlinarith

/-- Cochrane (2023), Online Appendix p. 592: when the two fractions are equal (`A₁ = A₂`), the last
two terms offset exactly and expected future sales have no effect on `P_0`. -/
theorem x0_const {s0 e1 e2 β A1 b2 d2 D00 F : ℝ} (hb2 : b2 ≠ 0) (hb : b2 + F ≠ 0)
    (hA : A1 = (b2 - d2) / b2) :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F = x0Fun s0 e1 e2 β A1 b2 d2 D00 0 := by
  unfold x0Fun
  congr 3
  rw [hA, add_zero, mul_zero, zero_add]
  field_simp
  ring

end Cochrane.LongTermDebtDynamics.FutureSales

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A general formula, and when the present-value system determines the price level

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17).

Write `y_t = B_{t−1}^{(t)}/P_t` for the real value of maturing debt and
`A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}` for the fraction of the debt due at `m`
that is
sold at `t`. The flow conditions (7.1) are the infinite upper-triangular linear system
`y_t = s_t + ∑_{j≥1} β^j E_t(A_t^{(t+j)} y_{t+j})` (`realFlow_iff_maturingSystem`).
Cochrane's weights are `W_t^{(0)} = 1`, `W_t^{(j)} = ∑_{k<j} A_{t+k}^{(t+j)} W_t^{(k)}` (`weight`),
and
(7.17) reads `y_t = E_t ∑_j β^j W_t^{(j)} s_{t+j}`.

## Main results

* `weight_first_step`: Cochrane's (last-step) recursion for `W` coincides with the first-step
  recursion `W_t^{(k+1)} = ∑_{j≤k} A_t^{(t+j+1)} W_{t+j+1}^{(k−j)}` produced by substitution.
* `comps`, `mem_comps`, `chainProd`, `chainProd_eq`, `chainSum`, `weight_eq_chainSum`: **Theorem W
  (ii)**: the weights are sums over strictly increasing chains `t = k₀ < … < k_n = t + m` of
  `∏ A_{k_i}^{(k_{i+1})}`.
* `theoremW_finite`: **Theorem W, finite horizon.** In an economy whose debt all matures by `T`,
  (7.17) holds exactly at every `t ≤ T`, under uncertainty.
* `abs_weight_le`, `sum_domWeight_le`: under the row condition `∑_j β^j a_j ≤ ρ < 1` on
  (deterministic bounds `a_j` for) the sale fractions, the weights are absolutely summable.
* `formulaW_solves`, `theoremW`: **Theorem W, infinite horizon.** Under the row condition and
bounded
  surpluses, (7.17) is a genuine convergent series, it solves the system, and every bounded
  solution equals it.
* `unique_of_row`, `unique_of_noBuyback`: **when the present-value system pins down the price
  level.** Bounded solutions are unique under the row condition, and also whenever the government
  never buys back debt (`B_t^{(m)} ≥ B_{t−1}^{(m)}`, nonnegative inherited debt).
* `bounded_of_presentValue`, `price_unique_noBuyback`: with nonnegative debt and positive prices
  the present-value relations force boundedness, so with no buy-backs the present-value relations
  determine the price level uniquely.
* `cx_*`: **the non-uniqueness counterexample** (E7.4): `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} =
2/β`,
  constant surplus. A one-parameter family of positive bounded price paths satisfies every flow and
  every present-value relation; the weights obey `W^{(k+2)} = (1 − 2/β) W^{(k+1)} + (2/β) W^{(k)}`,
  `β^k W^{(k)}` does not tend to zero, and (7.17) diverges. The policy buys back debt and violates
  the row condition, so both sufficient conditions are sharp in this sense.
* `unique_iff_homogeneous`: given one bounded solution, uniqueness of bounded solutions is
  equivalent to the homogeneous system having no nonzero bounded solution.
* `printed_715_fails`: the printed (7.15) without `β^j` is false (E7.2); `pvMatrix_row`: the
  corrected matrix display (7.16) (E7.3); `special_noSales`, `special_onePeriod`,
  `fracSold_onePeriod`: the special cases of §7.4.
* Labels (E7.1): on p. 225, (7.14) is the *flow* relation and (7.15) the *present-value*
  relation; the text swaps the two labels.
-/

namespace Cochrane.LongTermDebtDynamics.GeneralFormula

open Filter Topology MaturityStructure

/-! ### The weights and their two recursions -/

/-- Cochrane (2023), §7.4, p. 225–226: the weights `W_t^{(0)} = 1`,
`W_t^{(k+1)} = ∑_{n ≤ k} A_{t+n}^{(t+k+1)} W_t^{(n)}` (Cochrane's recursion, last step). -/
noncomputable def weight {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t : ℕ) : ℕ → R
  | 0 => 1
  | k + 1 => ∑ n : Fin (k + 1), A (t + n) (t + (k + 1)) * weight A t n
decreasing_by exact n.isLt

/-- Cochrane (2023), §7.4, p. 225: `W_t^{(0)} = 1`. -/
theorem weight_zero {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t : ℕ) : weight A t 0 = 1 := by
  rw [weight]

/-- Cochrane (2023), §7.4, p. 226: `W_t^{(k+1)} = ∑_{n<k+1} A_{t+n}^{(t+k+1)} W_t^{(n)}`. -/
theorem weight_succ {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t k : ℕ) :
    weight A t (k + 1) = ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) * weight A t n := by
  rw [weight, Fin.sum_univ_eq_sum_range (fun n => A (t + n) (t + (k + 1)) * weight A t n)]

/-- Cochrane (2023), §7.4, p. 226: reindexing a triangular double sum,
`∑_{j<N} ∑_{m<N−j} f j m = ∑_{k<N} ∑_{j≤k} f j (k − j)`. -/
theorem sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range (N - j), f j m =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), f j (k - j) := by
  symm
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun j => Finset.Ico j N)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  · intro k j
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- Cochrane (2023), §7.4, p. 226: **the two recursions agree.** Cochrane's last-step recursion
for `W` equals the first-step recursion obtained by substituting the flow condition forward,
`W_t^{(k+1)} = ∑_{j ≤ k} A_t^{(t+j+1)} W_{t+j+1}^{(k−j)}`. -/
theorem weight_first_step {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (k : ℕ) :
    ∀ t, weight A t (k + 1) =
      ∑ j ∈ Finset.range (k + 1), A t (t + (j + 1)) * weight A (t + (j + 1)) (k - j) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t
    rw [weight_succ, Finset.sum_range_succ' _ k, Finset.sum_range_succ _ k]
    simp only [add_zero, weight_zero, mul_one, Nat.sub_self]
    congr 1
    have hR : ∀ j ∈ Finset.range k, A t (t + (j + 1)) * weight A (t + (j + 1)) (k - j) =
        ∑ m ∈ Finset.range (k - j), A t (t + (j + 1)) *
          (A (t + (j + 1) + m) (t + (k + 1)) * weight A (t + (j + 1)) m) := by
      intro j hj
      have hjk := Finset.mem_range.mp hj
      obtain ⟨i, hi⟩ : ∃ i, k - j = i + 1 := ⟨k - j - 1, by omega⟩
      rw [hi, weight_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show t + (j + 1) + (i + 1) = t + (k + 1) by omega]
    rw [Finset.sum_congr rfl hR, sum_triangle k (fun j m => A t (t + (j + 1)) *
      (A (t + (j + 1) + m) (t + (k + 1)) * weight A (t + (j + 1)) m))]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ih n (Finset.mem_range.mp hn) t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show t + (j + 1) + (n - j) = t + (n + 1) by omega]
    ring

/-! ### Theorem W (ii): the weights as a sum over chains -/

/-- Cochrane (2023), §7.4, p. 226: the compositions of `m`, i.e. the lists of positive gaps
`(k₁ − k₀, k₂ − k₁, …, k_n − k_{n−1})` of the strictly increasing chains
`0 = k₀ < k₁ < … < k_n = m`. -/
def comps : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | m + 1 => (Finset.range (m + 1)).biUnion fun g =>
      (comps (m - g)).map ⟨List.cons (g + 1), List.cons_injective⟩
decreasing_by omega

/-- Cochrane (2023), §7.4, p. 226: a list is a composition of `m` iff its entries are positive and
sum to `m` (so `comps m` is exactly the set of strictly increasing chains from `0` to `m`). -/
theorem mem_comps (m : ℕ) : ∀ l : List ℕ, l ∈ comps m ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro l
    rcases m with _ | m
    · rw [comps]
      rcases l with _ | ⟨g, l⟩
      · simp
      · simp only [Finset.mem_singleton, reduceCtorEq, false_iff, not_and, List.mem_cons,
          List.sum_cons]
        intro h
        have := h g (Or.inl rfl)
        omega
    · rw [comps, Finset.mem_biUnion]
      constructor
      · rintro ⟨g, hg, hl⟩
        rw [Finset.mem_map] at hl
        obtain ⟨c, hc, rfl⟩ := hl
        have hg' := Finset.mem_range.mp hg
        obtain ⟨h1, h2⟩ := (ih (m - g) (by omega) c).mp hc
        refine ⟨fun x hx => ?_, ?_⟩
        · simp only [Function.Embedding.coeFn_mk, List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact h1 x hx
        · simp only [Function.Embedding.coeFn_mk, List.sum_cons, h2]
          omega
      · rintro ⟨hpos, hsum⟩
        rcases l with _ | ⟨g, c⟩
        · simp at hsum
        · have hg : 0 < g := hpos g (List.mem_cons_self ..)
          simp only [List.sum_cons] at hsum
          refine ⟨g - 1, Finset.mem_range.mpr (by omega), ?_⟩
          rw [Finset.mem_map]
          refine ⟨c, (ih (m - (g - 1)) (by omega) c).mpr ⟨fun x hx => hpos x
            (List.mem_cons_of_mem _ hx), by omega⟩, ?_⟩
          simp only [Function.Embedding.coeFn_mk]
          congr 1
          omega

/-- Cochrane (2023), §7.4, p. 226: the product of sale fractions along a chain starting at `t` with
gaps `l`: `chainProd A t [g₁, …, g_n] = A_t^{(t+g₁)} A_{t+g₁}^{(t+g₁+g₂)} ⋯`. -/
def chainProd {R : Type*} [CommRing R] (A : ℕ → ℕ → R) : ℕ → List ℕ → R
  | _, [] => 1
  | t, g :: l => A t (t + g) * chainProd A (t + g) l

/-- Cochrane (2023), §7.4, p. 226: the chain product written explicitly with the chain points
`k_i = t + g₁ + ⋯ + g_i`: `∏_{i<n} A_{k_i}^{(k_{i+1})}`. -/
theorem chainProd_eq {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (l : List ℕ) :
    ∀ t, chainProd A t l = ∏ i ∈ Finset.range l.length,
      A (t + (l.take i).sum) (t + (l.take (i + 1)).sum) := by
  induction l with
  | nil => intro t; simp [chainProd]
  | cons g l ih =>
    intro t
    rw [chainProd, ih, List.length_cons, Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [List.take_succ_cons, List.take_succ_cons]
      simp only [List.sum_cons, add_assoc]

/-- Cochrane (2023), §7.4, p. 226: the explicit weight, the sum over all chains
`t = k₀ < k₁ < … < k_n = t + m` of `∏ A_{k_i}^{(k_{i+1})}`. -/
noncomputable def chainSum {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t m : ℕ) : R :=
  ∑ c ∈ comps m, chainProd A t c

/-- Cochrane (2023), §7.4, p. 226: **Theorem W (ii).** Cochrane's recursively defined weights are
the sums over chains, `W_t^{(m)} = ∑_{t = k₀ < … < k_n = t + m} ∏_i A_{k_i}^{(k_{i+1})}`. -/
theorem weight_eq_chainSum {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (m : ℕ) :
    ∀ t, weight A t m = chainSum A t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [chainSum, comps, chainProd, weight_zero]
    · rw [weight_first_step, chainSum, comps, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun g hg => ?_
        rw [Finset.sum_map, ih (k - g) (by omega), chainSum, Finset.mul_sum]
        rfl
      · intro g _ g' _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [Finset.mem_map] at hx hx'
        obtain ⟨c, -, rfl⟩ := hx
        obtain ⟨c', -, h⟩ := hx'
        simp only [Function.Embedding.coeFn_mk, List.cons.injEq] at h
        exact hne (by omega)

/-! ### The maturing-debt system -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.4, p. 225: the fraction of the debt due at `m` sold at `t`,
`A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}`. -/
noncomputable def fracSold (D : ℕ → ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  (D (t + 1) m - D t m) / D m m

/-- Cochrane (2023), eq. (7.14), p. 225, in maturing-value form: with `y_t = B_{t−1}^{(t)}/P_t`, the
flow conditions are `y_t = s_t + ∑_{j≥0} β^{j+1} E_t(A_t^{(t+j+1)} y_{t+j+1})`. -/
def MaturingSystem (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (y s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω)
    (y t ω - s t ω)

/-- Cochrane (2023), eqs. (7.1)/(7.14), p. 225: the flow condition (7.1) at `t` is the maturing-debt
system at `t` for `y_t = B_{t−1}^{(t)}/P_t` and `A = fracSold`, when the debt coming due is never
zero. -/
theorem realFlow_iff_maturingSystem (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hDmm : ∀ m ω, D m m ω ≠ 0) (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔ MaturingSystem 𝔼 β (fracSold D) (fun u => D u u * x u) s t := by
  have hterm : ∀ m, sales D t m * 𝔼.E t (x m) = 𝔼.E t (fracSold D t m * (D m m * x m)) := by
    intro m
    have hk : 𝔼.E t (sales D t m) = sales D t m := by
      rw [sales, map_sub, hD.2 t m, Predetermined.known 𝔼 hD le_rfl m]
    have : fracSold D t m * (D m m * x m) = sales D t m * x m := by
      funext ω
      simp only [fracSold, sales, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [hDmm m ω]
    rw [this, hpo t _ _ hk]
  unfold RealFlow MaturingSystem
  refine forall_congr' fun ω => ?_
  have hf : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun j : ℕ => β ^ (j + 1) *
        𝔼.E t (fracSold D t (t + (j + 1)) *
          (D (t + (j + 1)) (t + (j + 1)) * x (t + (j + 1)))) ω := by
    funext j
    rw [← hterm]
    rfl
  rw [hf]
  exact Iff.rfl

/-- Cochrane (2023), §7.4, p. 226: if each sale fraction `A_t^{(t+j+1)}` is known at `t + j` (when
the last sale before maturity takes place), the weight `W_t^{(m+1)}` is known at `t + m`. -/
theorem weight_known (hpo : 𝔼.PullOut) {A : ℕ → ℕ → Ω → ℝ}
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1))) (t m : ℕ) :
    𝔼.E (t + m) (weight A t (m + 1)) = weight A t (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [weight_succ, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hAk : 𝔼.E (t + m) (A (t + n) (t + (m + 1))) = A (t + n) (t + (m + 1)) := by
      have := hA (t + n) (m - n)
      rwa [show t + n + (m - n) = t + m by omega, show t + n + (m - n + 1) = t + (m + 1) by omega]
        at this
    rw [hpo _ _ _ hAk]
    congr 1
    rcases n with _ | n
    · rw [weight_zero]; exact 𝔼.const _ 1
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (ih n (by omega))

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W, finite horizon.** Suppose no debt matures
after `T` (`A_t^{(m)} = 0` for `m > T`), each `A_t^{(t+j+1)}` is known at `t + j`, surpluses are
adapted and `y` solves the maturing-debt system. Then at every `t ≤ T`,
`y_t = ∑_{m ≤ T−t} β^m E_t(W_t^{(m)} s_{t+m})`, an exact identity under uncertainty. -/
theorem theoremW_finite (hpo : 𝔼.PullOut) {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y s : ℕ → Ω → ℝ}
    {T : ℕ} (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    (hT : ∀ t m, T < m → A t m = 0) (hs : 𝔼.Adapted s)
    (hsys : ∀ t, MaturingSystem 𝔼 β A y s t) {t : ℕ} (ht : t ≤ T) :
    y t = ∑ m ∈ Finset.range (T - t + 1), β ^ m • 𝔼.E t (weight A t m * s (t + m)) := by
  suffices key : ∀ N t, T - t = N → t ≤ T →
      y t = ∑ m ∈ Finset.range (N + 1), β ^ m • 𝔼.E t (weight A t m * s (t + m)) from
    key _ t rfl ht
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t hN ht
    -- the flow sum is finite
    have hfin : y t - s t = ∑ j ∈ Finset.range N,
        β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) := by
      funext ω
      have hz : ∀ j ∉ Finset.range N,
          β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω = 0 := by
        intro j hj
        rw [Finset.mem_range, not_lt] at hj
        rw [hT t _ (by omega), zero_mul, map_zero, Pi.zero_apply, mul_zero]
      have := (hsys t ω).unique (hasSum_sum_of_ne_finset_zero hz)
      rw [Pi.sub_apply, this, Finset.sum_apply]
      rfl
    -- expand each later maturing value by the induction hypothesis
    have hexp : ∀ j ∈ Finset.range N, β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) =
        ∑ m ∈ Finset.range (N - j), β ^ (j + 1 + m) • 𝔼.E t (A t (t + (j + 1)) *
          weight A (t + (j + 1)) m * s (t + (j + 1) + m)) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [ih (N - (j + 1)) (by omega) (t + (j + 1)) (by omega) (by omega),
        show N - (j + 1) + 1 = N - j by omega, Finset.mul_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
        ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
      rw [mul_smul_comm, map_smul, ← hpo _ _ _ hAk, 𝔼.tower (by omega), smul_smul, ← pow_add,
        mul_assoc]
    rw [Finset.sum_range_succ', weight_zero, one_mul, pow_zero, one_smul, add_zero, hs t]
    rw [eq_add_of_sub_eq hfin, Finset.sum_congr rfl hexp, sum_triangle N
      (fun j m => β ^ (j + 1 + m) • 𝔼.E t (A t (t + (j + 1)) * weight A (t + (j + 1)) m *
        s (t + (j + 1) + m)))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [weight_first_step, Finset.sum_mul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show j + 1 + (k - j) = k + 1 by omega, show t + (j + 1) + (k - j) = t + (k + 1) by omega]

/-! ### Infinite horizon: the row condition -/

/-- Cochrane (2023), eq. (7.17), p. 225: the **row condition**: the sale fractions are bounded by a
deterministic sequence, `|A_t^{(t+j+1)}| ≤ a_j`, with `∑_j β^{j+1} a_j ≤ ρ` (convergent). With
`ρ < 1` this is a contraction condition on the system (7.14). -/
def RowBound (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℝ) (ρ : ℝ) : Prop :=
  (∀ j, 0 ≤ a j) ∧ (∀ t j ω, |A t (t + (j + 1)) ω| ≤ a j) ∧
    Summable (fun j => β ^ (j + 1) * a j) ∧ ∑' j, β ^ (j + 1) * a j ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 226: the stationary dominating fractions
`(u, v) ↦ a_{v−u−1}`. -/
def domA (a : ℕ → ℝ) : ℕ → ℕ → ℝ := fun u v => a (v - u - 1)

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights, the weights of the stationary
fractions `a`. -/
noncomputable def domWeight (a : ℕ → ℝ) : ℕ → ℝ := weight (domA a) 0

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights do not depend on the start date. -/
theorem weight_domA (a : ℕ → ℝ) (m : ℕ) : ∀ u, weight (domA a) u m = domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro u
    rcases m with _ | k
    · rw [domWeight, weight_zero, weight_zero]
    · rw [domWeight, weight_succ, weight_succ]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn' := Finset.mem_range.mp hn
      rw [ih n hn' u, ih n hn' 0]
      simp only [domA]
      congr 2
      omega

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights are nonnegative. -/
theorem domWeight_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (m : ℕ) : 0 ≤ domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | k
    · rw [domWeight, weight_zero]; exact zero_le_one
    · rw [domWeight, weight_succ]
      refine Finset.sum_nonneg fun n hn => mul_nonneg (ha _) ?_
      exact ih n (Finset.mem_range.mp hn)

/-- Cochrane (2023), eq. (7.17), p. 226: first-step recursion for the dominating weights,
`w_{k+1} = ∑_{j ≤ k} a_j w_{k−j}`. -/
theorem domWeight_succ (a : ℕ → ℝ) (k : ℕ) :
    domWeight a (k + 1) = ∑ j ∈ Finset.range (k + 1), a j * domWeight a (k - j) := by
  rw [domWeight, weight_first_step]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weight_domA]
  simp only [domA]
  congr 2
  omega

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition, `|W_t^{(m)}| ≤ w_m`. -/
theorem abs_weight_le {β ρ : ℝ} {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (m : ℕ) : ∀ t ω, |weight A t m ω| ≤ domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t ω
    rcases m with _ | k
    · rw [weight_zero, domWeight, weight_zero]; simp
    · rw [weight_succ, domWeight, weight_succ, Finset.sum_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [Pi.mul_apply, abs_mul]
      have hA := hrow.2.1 (t + n) (k - n) ω
      rw [show t + n + (k - n + 1) = t + (k + 1) by omega] at hA
      have hdA : domA a (0 + n) (0 + (k + 1)) = a (k - n) := by
        simp only [domA]; congr 1; omega
      rw [hdA]
      exact mul_le_mul hA (ih n (by omega) t ω) (abs_nonneg _) ((hrow.1 _))

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition the finite sums of
`β^m w_m` are bounded by `∑_{n<N} ρ^n`. -/
theorem sum_domWeight_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ0 : 0 ≤ ρ) {a : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ (j + 1) * a j ≤ ρ) (N : ℕ) :
    ∑ m ∈ Finset.range N, β ^ m * domWeight a m ≤ ∑ n ∈ Finset.range N, ρ ^ n := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, domWeight, weight_zero,
        mul_one, pow_zero]
      have hexp : ∑ k ∈ Finset.range N, β ^ (k + 1) * weight (domA a) 0 (k + 1) =
          ∑ j ∈ Finset.range N, β ^ (j + 1) * a j *
            ∑ m ∈ Finset.range (N - j), β ^ m * domWeight a m := by
        have : ∀ k, β ^ (k + 1) * weight (domA a) 0 (k + 1) =
            ∑ j ∈ Finset.range (k + 1),
              β ^ (j + 1) * a j * (β ^ (k - j) * domWeight a (k - j)) := by
          intro k
          rw [← domWeight, domWeight_succ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
          ring
        simp only [this]
        rw [← sum_triangle N (fun j m => β ^ (j + 1) * a j * (β ^ m * domWeight a m))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
      rw [hexp]
      have hstep : ∑ j ∈ Finset.range N, β ^ (j + 1) * a j *
          ∑ m ∈ Finset.range (N - j), β ^ m * domWeight a m ≤
          ∑ j ∈ Finset.range N, β ^ (j + 1) * a j * ∑ n ∈ Finset.range N, ρ ^ n := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (pow_nonneg hβ0 _) (ha j))
        refine (ih (N - j) (by omega)).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N j))
          fun n _ _ => pow_nonneg hρ0 n
      have hgeo : 0 ≤ ∑ n ∈ Finset.range N, ρ ^ n := Finset.sum_nonneg fun n _ => pow_nonneg hρ0 n
      rw [← Finset.sum_mul] at hstep
      have h2 := mul_le_mul_of_nonneg_right (hpart N) hgeo
      have h3 : ∑ i ∈ Finset.range N, ρ ^ (i + 1) = ρ * ∑ n ∈ Finset.range N, ρ ^ n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_succ' ρ i
      rw [h3]
      linarith

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition with `ρ < 1`, `∑_m β^m w_m`
converges, with sum at most `1/(1−ρ)`. -/
theorem summable_domWeight {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) :
    Summable (fun m => β ^ m * domWeight a m) ∧ ∑' m, β ^ m * domWeight a m ≤ 1 / (1 - ρ) := by
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0 _) (hrow.1 j)
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ (j + 1) * a j ≤ ρ := fun N =>
    (hrow.2.2.1.sum_le_tsum _ fun j _ => hnn j).trans hrow.2.2.2
  have hρ0 : 0 ≤ ρ := (tsum_nonneg hnn).trans hrow.2.2.2
  have hbound : ∀ N, ∑ m ∈ Finset.range N, β ^ m * domWeight a m ≤ 1 / (1 - ρ) := by
    intro N
    refine (sum_domWeight_le hβ0 hρ0 hrow.1 hpart N).trans ?_
    have hg := summable_geometric_of_lt_one hρ0 hρ1
    refine (hg.sum_le_tsum _ fun n _ => pow_nonneg hρ0 n).trans ?_
    rw [tsum_geometric_of_lt_one hρ0 hρ1, one_div]
  have hnn' : ∀ m, 0 ≤ β ^ m * domWeight a m := fun m =>
    mul_nonneg (pow_nonneg hβ0 m) (domWeight_nonneg hrow.1 m)
  exact ⟨summable_of_sum_range_le hnn' hbound, Real.tsum_le_of_sum_range_le hnn' hbound⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the terms `β^m E_t(W_t^{(m)} s_{t+m})` of the weighted
present value. -/
noncomputable def formulaTerm (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t m : ℕ) (ω : Ω) :
    ℝ :=
  β ^ m * 𝔼.E t (weight A t m * s (t + m)) ω

/-- Cochrane (2023), eq. (7.17), p. 225: the weighted present value
`E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
noncomputable def formulaW (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' m, formulaTerm 𝔼 β A s t m ω

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition and `|s| ≤ M`, the terms of (7.17)
are dominated by `β^m w_m M`. -/
theorem abs_formulaTerm_le {β ρ M : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hrow : RowBound β A a ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (t m : ℕ) (ω : Ω) :
    |formulaTerm 𝔼 β A s t m ω| ≤ β ^ m * domWeight a m * M := by
  rw [formulaTerm, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) t ω) (pow_nonneg hβ0 m)
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (abs_weight_le hrow m t ω') (hsb _ ω') (abs_nonneg _)
    (domWeight_nonneg hrow.1 m)

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition (`ρ < 1`) and bounded surpluses,
the series (7.17) converges absolutely and `|E_t ∑ β^m W s| ≤ M/(1−ρ)`. -/
theorem formulaW_summable {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    Summable (fun m => formulaTerm 𝔼 β A s t m ω) ∧ |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ) := by
  obtain ⟨hsum, hle⟩ := summable_domWeight hβ0 hρ1 hrow
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb t ω)
  have hdom : Summable (fun m => β ^ m * domWeight a m * M) := hsum.mul_right M
  have hs : Summable (fun m => formulaTerm 𝔼 β A s t m ω) :=
    Summable.of_norm_bounded hdom (fun m => by
      rw [Real.norm_eq_abs]; exact abs_formulaTerm_le 𝔼 hβ0 hrow hsb t m ω)
  refine ⟨hs, ?_⟩
  have h1 : |formulaW 𝔼 β A s t ω| ≤ ∑' m, β ^ m * domWeight a m * M := by
    rw [formulaW]
    have h0 := norm_tsum_le_tsum_norm (f := fun m => formulaTerm 𝔼 β A s t m ω)
      (by simpa only [Real.norm_eq_abs] using hs.abs)
    simp only [Real.norm_eq_abs] at h0
    refine h0.trans ?_
    exact Summable.tsum_le_tsum (fun m => abs_formulaTerm_le 𝔼 hβ0 hrow hsb t m ω) hs.abs hdom
  refine h1.trans ?_
  rw [tsum_mul_right, div_eq_mul_inv, mul_comm M]
  exact mul_le_mul_of_nonneg_right (by simpa using hle) hM

/-- Cochrane (2023), eq. (7.17), p. 225: **the weighted present value solves the system.** Under
the row condition (`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j` and bounded adapted
surpluses, `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` satisfies the flow conditions (7.14) at every date.
The proof substitutes and regroups an absolutely convergent double series by antidiagonals,
using `weight_first_step`. -/
theorem formulaW_solves (hpo : 𝔼.PullOut) {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t := by
  intro ω
  obtain ⟨hsumw, -⟩ := summable_domWeight hβ0 hρ1 hrow
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb t ω)
  set Gf : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * (β ^ p.2 *
    𝔼.E t (A t (t + (p.1 + 1)) * (weight A (t + (p.1 + 1)) p.2 * s (t + (p.1 + 1) + p.2))) ω)
    with hGf
  have hEb : ∀ (j m : ℕ) (u : ℕ) (ω₀ : Ω), |𝔼.E u (A t (t + (j + 1)) *
      (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω₀| ≤ a j * (domWeight a m * M) := by
    intro j m u ω₀
    refine 𝔼.abs_E_le (fun ω' => ?_) u ω₀
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hrow.2.1 t j ω') (mul_le_mul (abs_weight_le hrow _ _ ω') (hsb _ ω')
      (abs_nonneg _) (domWeight_nonneg hrow.1 _)) (by positivity) (hrow.1 _)
  have hGb : ∀ p : ℕ × ℕ, ‖Gf p‖ ≤ (β ^ (p.1 + 1) * a p.1) * (β ^ p.2 * domWeight a p.2 * M) := by
    intro p
    rw [Real.norm_eq_abs, hGf]
    simp only [abs_mul, abs_pow, abs_of_nonneg hβ0]
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hEb p.1 p.2 t ω)
      (pow_nonneg hβ0 p.2)) (pow_nonneg hβ0 (p.1 + 1))
    refine h1.trans (le_of_eq ?_)
    ring
  have hprod : Summable (fun p : ℕ × ℕ => (β ^ (p.1 + 1) * a p.1) *
      (β ^ p.2 * domWeight a p.2 * M)) :=
    summable_mul_of_summable_norm (f := fun j => β ^ (j + 1) * a j)
      (g := fun m => β ^ m * domWeight a m * M)
      (by simpa only [Real.norm_eq_abs] using hrow.2.2.1.abs)
      (by simpa only [Real.norm_eq_abs] using (hsumw.mul_right M).abs)
  have hGsum : Summable Gf := Summable.of_norm_bounded hprod hGb
  -- (i) the fibres in `j`
  have hfib : ∀ j, HasSum (fun m => Gf (j, m))
      (β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1))) ω) := by
    intro j
    have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
      ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
    have hfun : A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1)) = fun ω' =>
        ∑' m, A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω' := by
      funext ω'
      rw [Pi.mul_apply, formulaW, tsum_mul_left]
    have hu : Summable (fun m => a j * (β ^ m * domWeight a m * M)) :=
      (hsumw.mul_right M).mul_left (a j)
    have hf : ∀ m ω', |A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω'| ≤
        a j * (β ^ m * domWeight a m * M) := by
      intro m ω'
      rw [abs_mul]
      exact mul_le_mul (hrow.2.1 t j ω') (abs_formulaTerm_le 𝔼 hβ0 hrow hsb _ m ω')
        (abs_nonneg _) (hrow.1 j)
    have hterm : ∀ m, 𝔼.E t (fun ω' => A t (t + (j + 1)) ω' *
        formulaTerm 𝔼 β A s (t + (j + 1)) m ω') ω = β ^ m * 𝔼.E t (A t (t + (j + 1)) *
          (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω := by
      intro m
      have hfm : (fun ω' => A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω') =
          β ^ m • 𝔼.E (t + (j + 1)) (A t (t + (j + 1)) *
            (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) := by
        rw [hpo _ _ _ hAk]
        funext ω'
        simp only [formulaTerm, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        ring
      rw [hfm, map_smul, 𝔼.tower (by omega)]
      rfl
    rw [hfun, ForwardSolution.E_tsum_dom 𝔼 hu hf t ω]
    simp only [hterm]
    have hinner : Summable (fun m => β ^ m * 𝔼.E t (A t (t + (j + 1)) *
        (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω) :=
      Summable.of_norm_bounded ((hsumw.mul_right M).mul_left (a j)) (fun m => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
        have := mul_le_mul_of_nonneg_left (hEb j m t ω) (pow_nonneg hβ0 m)
        refine this.trans (le_of_eq ?_)
        ring)
    exact hinner.hasSum.mul_left (β ^ (j + 1))
  -- (ii) summing the fibres
  have hrowsum := hGsum.hasSum.prod_fiberwise hfib
  -- (iii) summing by antidiagonals
  have hdiag : HasSum (fun k => formulaTerm 𝔼 β A s t (k + 1) ω) (∑' p, Gf p) := by
    have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := Gf)).mpr
      hGsum.hasSum
    have h2 := h1.sigma (fun k => hasSum_fintype _)
    convert h2 using 1
    funext k
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal k) Gf,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, formulaTerm, weight_first_step,
      Finset.sum_mul, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hGf]
    rw [show t + (j + 1) + (k - j) = t + (k + 1) by omega, mul_assoc,
      show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
    ring
  -- (iv) the value at `t`
  obtain ⟨hzs, -⟩ := formulaW_summable 𝔼 hβ0 hρ1 hrow hsb t ω
  have hz : formulaW 𝔼 β A s t ω = s t ω + ∑' p, Gf p := by
    rw [formulaW, hzs.tsum_eq_zero_add, hdiag.tsum_eq]
    simp [formulaTerm, weight_zero, hs t]
  rw [hz, add_sub_cancel_left]
  exact hrowsum

/-- Cochrane (2023), §7.4, p. 225: **uniqueness under the row condition.** If `ρ < 1`, the only
bounded solution of the homogeneous system `d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is
zero. -/
theorem unique_of_row {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0 _) (hrow.1 j)
  have hρ0 : 0 ≤ ρ := (tsum_nonneg hnn).trans hrow.2.2.2
  have hstep : ∀ n t ω, |d t ω| ≤ ρ ^ n * K := by
    intro n
    induction n with
    | zero => intro t ω; simpa using hK t ω
    | succ n ih =>
      intro t ω
      have hK0 : 0 ≤ ρ ^ n * K := (abs_nonneg _).trans (ih t ω)
      have hb : ∀ j, |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
          β ^ (j + 1) * a j * (ρ ^ n * K) := by
        intro j
        rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
        refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) t ω) (pow_nonneg hβ0 _)
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul (hrow.2.1 t j ω') (ih _ ω') (abs_nonneg _) (hrow.1 j)
      have hH : HasSum (fun j => β ^ (j + 1) * a j * (ρ ^ n * K))
          ((∑' j, β ^ (j + 1) * a j) * (ρ ^ n * K)) := hrow.2.2.1.hasSum.mul_right _
      have h1 := hasSum_le (fun j => (le_abs_self _).trans (hb j)) (hd t ω) hH
      have h2 := hasSum_le (fun j => (neg_le_abs _).trans (hb j)) (hd t ω).neg hH
      have h3 : (∑' j, β ^ (j + 1) * a j) * (ρ ^ n * K) ≤ ρ ^ (n + 1) * K := by
        rw [pow_succ, mul_comm (ρ ^ n) ρ, mul_assoc]
        exact mul_le_mul_of_nonneg_right hrow.2.2.2 hK0
      rw [abs_le]
      constructor <;> linarith
  funext t ω
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  have := ge_of_tendsto' hlim (fun n => hstep n t ω)
  simpa using abs_nonpos_iff.mp this

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W, infinite horizon.** Under the row condition
(`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j` and bounded adapted surpluses, every bounded
solution of the flow conditions (7.14) is given by the weighted present value (7.17):
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`, an absolutely convergent series. -/
theorem theoremW (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) := by
  have hz := formulaW_solves 𝔼 hpo hβ0 hρ1 hrow hA hs hsb
  have hd : y - formulaW 𝔼 β A s = 0 := by
    refine unique_of_row 𝔼 hβ0 hρ1 hrow (K := K + M / (1 - ρ)) (fun u ω' => ?_) (fun u ω' => ?_)
    · have := (hy u ω').sub (hz u ω')
      convert this using 1
      · funext j
        simp only [Pi.sub_apply, mul_sub, map_sub]
      · simp only [Pi.sub_apply]; ring
    · rw [Pi.sub_apply]
      exact (abs_sub _ _).trans
        (add_le_add (hyb u ω') (formulaW_summable 𝔼 hβ0 hρ1 hrow hsb u ω').2)
  have hyz : y t ω = formulaW 𝔼 β A s t ω := by
    have := congrFun (congrFun hd t) ω
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  rw [hyz]
  exact (formulaW_summable 𝔼 hβ0 hρ1 hrow hsb t ω).1.hasSum

/-! ### Uniqueness without buy-backs (the column condition) -/

/-- Cochrane (2023), §7.4, p. 225 (the "column" lemma behind uniqueness without buy-backs): let
`u ≥ 0` be summable and `G ≥ 0` with `G t m = 0` for `m ≤ t`. If `u_t ≤ ∑_m G t m` for every
`t ≥ τ` and every column satisfies `∑_{t<m} G t m ≤ u_m`, then `u_τ ≤ 0`. -/
theorem col_lemma {u : ℕ → ℝ} {G : ℕ → ℕ → ℝ} (hu0 : ∀ t, 0 ≤ u t) (hus : Summable u)
    (hG0 : ∀ t m, 0 ≤ G t m) (hGz : ∀ t m, m ≤ t → G t m = 0) {τ : ℕ}
    (hGs : ∀ t, τ ≤ t → Summable (G t)) (hH1 : ∀ t, τ ≤ t → u t ≤ ∑' m, G t m)
    (hcol : ∀ m, ∑ t ∈ Finset.range m, G t m ≤ u m) : u τ ≤ 0 := by
  classical
  set F : ℕ → ℕ → ℝ := fun k m => G (τ + k) m with hF
  set v : ℕ → ℝ := fun m => if τ < m then u m else 0 with hv
  have hFz : ∀ k m, m ≤ k → F k m = 0 := fun k m h => hGz _ _ (by omega)
  have hslm : ∀ m, Summable (fun k => F k m) := fun m =>
    summable_of_ne_finset_zero (s := Finset.range m) fun k hk =>
      hFz k m (by simpa using hk)
  have hFm : ∀ m, ∑' k, F k m ≤ v m := by
    intro m
    rw [tsum_eq_sum (s := Finset.range m) fun k hk => hFz k m (by simpa using hk)]
    by_cases hτm : τ < m
    · simp only [hv, hτm, ↓reduceIte, hF]
      have hre : ∑ x ∈ Finset.range m, G (τ + x) m = ∑ t ∈ Finset.Ico τ (τ + m), G t m := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rw [hre]
      refine le_trans ?_ (hcol m)
      rw [← Finset.sum_filter_of_ne (p := fun t => t < m) (fun t _ h => by
        by_contra hc; exact h (hGz t m (by omega)))]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun t ht => by simp only [Finset.mem_filter] at ht; exact Finset.mem_range.mpr ht.2)
        fun t _ _ => hG0 t m
    · simp only [hv, hτm, ↓reduceIte]
      exact le_of_eq (Finset.sum_eq_zero fun k _ => hGz _ _ (by omega))
  have hv0 : ∀ m, 0 ≤ v m := fun m => by
    simp only [hv]; split_ifs <;> simp [hu0 m]
  have hvs : Summable v := Summable.of_nonneg_of_le hv0
    (fun m => by simp only [hv]; split_ifs <;> simp [hu0 m]) hus
  have hH : Summable (fun p : ℕ × ℕ => F p.2 p.1) := by
    rw [summable_prod_of_nonneg (fun p => hG0 _ _)]
    exact ⟨fun m => hslm m, Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => hG0 _ _)
      hFm hvs⟩
  have hFsum : Summable (Function.uncurry F) := hH.prod_symm
  have hslk : ∀ k, Summable (F k) := fun k => hGs (τ + k) (by omega)
  have hcomm : ∑' m, ∑' k, F k m = ∑' k, ∑' m, F k m := hFsum.tsum_comm' hslk hslm
  have hus' : Summable (fun k => u (τ + k)) := by
    simpa [add_comm] using (summable_nat_add_iff τ).mpr hus
  have h1 : ∑' k, u (τ + k) ≤ ∑' k, ∑' m, F k m :=
    Summable.tsum_le_tsum (fun k => hH1 (τ + k) (by omega)) hus' hFsum.prod
  have h2 : ∑' m, ∑' k, F k m ≤ ∑' m, v m :=
    Summable.tsum_le_tsum hFm (Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => hG0 _ _)
      hFm hvs) hvs
  have h3 : ∑' m, v m = ∑' k, u (τ + (k + 1)) := by
    have hfin : ∑ i ∈ Finset.range (τ + 1), v i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hv, show ¬ τ < i by have := Finset.mem_range.mp hi; omega, ↓reduceIte]
    have := (hasSum_nat_add_iff' (τ + 1)).mpr hvs.hasSum
    rw [hfin, sub_zero] at this
    rw [← this.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [hv, show τ < k + (τ + 1) by omega, ↓reduceIte]
    congr 1
    omega
  have h4 : ∑' k, u (τ + k) = u τ + ∑' k, u (τ + (k + 1)) := by
    rw [hus'.tsum_eq_zero_add, add_zero]
  linarith

/-- Cochrane (2023), §7.4: `|E_t f| ≤ E_t |f|`. -/
theorem abs_E_le_E_abs (t : ℕ) (f : Ω → ℝ) (ω : Ω) :
    |𝔼.E t f ω| ≤ 𝔼.E t (fun ω' => |f ω'|) ω := by
  have h1 := 𝔼.mono t (fun ω' => le_abs_self (f ω')) ω
  have h2 := 𝔼.mono t (fun ω' => neg_abs_le (f ω')) ω
  have h3 : 𝔼.E t (fun ω' => -|f ω'|) ω = -𝔼.E t (fun ω' => |f ω'|) ω := by
    rw [show (fun ω' => -|f ω'|) = -(fun ω' => |f ω'|) from rfl, map_neg, Pi.neg_apply]
  rw [abs_le]
  constructor <;> linarith

/-- Cochrane (2023), §7.4, p. 225: **uniqueness without buy-backs.** Suppose the sale fractions are
nonnegative and each column sums to at most one, `∑_{t<m} A_t^{(m)} ≤ 1` (true when the government
never buys back debt and inherited positions are nonnegative), and `0 < β < 1`. Then the only
bounded solution of the homogeneous system `d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is
zero, under uncertainty. -/
theorem unique_of_noBuyback {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {A : ℕ → ℕ → Ω → ℝ}
    (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω)
    (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  classical
  have hA1 : ∀ t m ω, t < m → A t m ω ≤ 1 := fun t m ω h =>
    (Finset.single_le_sum (fun i hi => hA0 i m ω (Finset.mem_range.mp hi))
      (Finset.mem_range.mpr h)).trans (hcolA m ω)
  set e : ℕ → Ω → ℝ := fun t ω => |d t ω| with he
  have he0 : ∀ t ω, 0 ≤ e t ω := fun t ω => abs_nonneg _
  have heK : ∀ t ω, e t ω ≤ K := hK
  have hsumβ : Summable (fun j : ℕ => β ^ (j + 1) * K) :=
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left β).mul_right K |>.congr fun j => by ring
  -- bounds on the terms
  have hAe : ∀ (t j : ℕ) (u : ℕ) (ω : Ω), 0 ≤ 𝔼.E u (A t (t + (j + 1)) * e (t + (j + 1))) ω ∧
      𝔼.E u (A t (t + (j + 1)) * e (t + (j + 1))) ω ≤ K := by
    intro t j u ω
    have hlo : (fun _ => (0 : ℝ)) ≤ A t (t + (j + 1)) * e (t + (j + 1)) := fun ω' =>
      mul_nonneg (hA0 _ _ ω' (by omega)) (he0 _ ω')
    have hhi : A t (t + (j + 1)) * e (t + (j + 1)) ≤ fun _ => K := fun ω' =>
      (mul_le_of_le_one_left (he0 _ ω') (hA1 _ _ ω' (by omega))).trans (heK _ ω')
    have h1 := 𝔼.mono u hlo ω
    have h2 := 𝔼.mono u hhi ω
    rw [𝔼.const] at h1 h2
    exact ⟨h1, h2⟩
  -- `d` is adapted
  have hdad : ∀ t, 𝔼.E t (d t) = d t := by
    intro t
    funext ω
    have hfun : d t = fun ω' => ∑' j, β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω' := by
      funext ω'; exact (hd t ω').tsum_eq.symm
    have hb : ∀ j ω', |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω'| ≤
        β ^ (j + 1) * K := by
      intro j ω'
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω').trans ?_) (pow_nonneg hβ0.le _)
      have : (fun ω'' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω''|) =
          A t (t + (j + 1)) * e (t + (j + 1)) := by
        funext ω''
        simp only [Pi.mul_apply, abs_mul, he,
          abs_of_nonneg (hA0 _ _ ω'' (by omega : t < t + (j + 1)))]
      rw [this]
      exact (hAe t j t ω').2
    conv_lhs => rw [hfun]
    rw [ForwardSolution.E_tsum_dom 𝔼 hsumβ hb t ω]
    rw [← (hd t ω).tsum_eq]
    refine tsum_congr fun j => ?_
    rw [show (fun ω' => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω') =
      β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) from rfl, map_smul, 𝔼.E_E_self]
    rfl
  -- the pointwise inequality `e_t ≤ ∑ β^{j+1} E_t(A e)`
  have hR : ∀ t ω, e t ω ≤ ∑' j, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
    intro t ω
    have hsR : Summable (fun j => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0.le _) (hAe t j t ω).1)
        (fun j => mul_le_mul_of_nonneg_left (hAe t j t ω).2 (pow_nonneg hβ0.le _)) hsumβ
    have hle : ∀ j, |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
        β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
      intro j
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      have hfe : (fun ω'' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω''|) =
          A t (t + (j + 1)) * e (t + (j + 1)) := by
        funext ω''
        simp only [Pi.mul_apply, abs_mul, he,
          abs_of_nonneg (hA0 _ _ ω'' (by omega : t < t + (j + 1)))]
      have := abs_E_le_E_abs 𝔼 t (A t (t + (j + 1)) * d (t + (j + 1))) ω
      rw [hfe] at this
      exact mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le _)
    have h1 := hasSum_le (fun j => (le_abs_self _).trans (hle j)) (hd t ω) hsR.hasSum
    have h2 := hasSum_le (fun j => (neg_le_abs _).trans (hle j)) (hd t ω).neg hsR.hasSum
    simp only [he]
    rw [abs_le]
    constructor <;> linarith
  -- apply the column lemma at each date `τ` and state `ω`
  funext τ ω
  set u : ℕ → ℝ := fun t => β ^ t * 𝔼.E τ (e t) ω with hu
  set G : ℕ → ℕ → ℝ := fun t m => if t < m then β ^ m * 𝔼.E τ (A t m * e m) ω else 0 with hG
  have hEe : ∀ t, 0 ≤ 𝔼.E τ (e t) ω ∧ 𝔼.E τ (e t) ω ≤ K := by
    intro t
    have h1 := 𝔼.mono τ (show (fun _ => (0 : ℝ)) ≤ e t from fun ω' => he0 t ω') ω
    have h2 := 𝔼.mono τ (show e t ≤ fun _ => K from fun ω' => heK t ω') ω
    rw [𝔼.const] at h1 h2
    exact ⟨h1, h2⟩
  have hu0 : ∀ t, 0 ≤ u t := fun t => mul_nonneg (pow_nonneg hβ0.le t) (hEe t).1
  have hus : Summable u := Summable.of_nonneg_of_le hu0
    (fun t => mul_le_mul_of_nonneg_left (hEe t).2 (pow_nonneg hβ0.le t))
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
  have hGnn : ∀ t m, t < m → 0 ≤ 𝔼.E τ (A t m * e m) ω ∧ 𝔼.E τ (A t m * e m) ω ≤ K := by
    intro t m htm
    obtain ⟨j, rfl⟩ : ∃ j, m = t + (j + 1) := ⟨m - t - 1, by omega⟩
    exact hAe t j τ ω
  have hG0 : ∀ t m, 0 ≤ G t m := fun t m => by
    simp only [hG]; split_ifs with h
    · exact mul_nonneg (pow_nonneg hβ0.le _) (hGnn t m h).1
    · exact le_rfl
  have hGz : ∀ t m, m ≤ t → G t m = 0 := fun t m h => by
    simp only [hG, show ¬ t < m by omega, ↓reduceIte]
  have hGs : ∀ t, Summable (G t) := fun t =>
    Summable.of_nonneg_of_le (hG0 t) (fun m => by
      simp only [hG]; split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hGnn t m h).2 (pow_nonneg hβ0.le _)
      · exact mul_nonneg (pow_nonneg hβ0.le _) ((abs_nonneg _).trans (hK 0 ω)))
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
  have hH1 : ∀ t, τ ≤ t → u t ≤ ∑' m, G t m := by
    intro t ht
    -- `E_τ e_t ≤ ∑ β^{j+1} E_τ(A e)`
    have hb : ∀ j ω', |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω'| ≤
        β ^ (j + 1) * K := by
      intro j ω'
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (hAe t j t ω').1)]
      exact mul_le_mul_of_nonneg_left (hAe t j t ω').2 (pow_nonneg hβ0.le _)
    have hmono := 𝔼.mono τ (show e t ≤ fun ω' => ∑' j, β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω' from fun ω' => hR t ω') ω
    rw [ForwardSolution.E_tsum_dom 𝔼 hsumβ hb τ ω] at hmono
    have hterm : ∀ j, 𝔼.E τ (fun ω' => β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω') ω =
        β ^ (j + 1) * 𝔼.E τ (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
      intro j
      rw [show (fun ω' => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω') =
        β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) from rfl, map_smul,
        𝔼.tower ht]
      rfl
    simp only [hterm] at hmono
    have hshift : ∑' m, G t m = ∑' j, β ^ t * (β ^ (j + 1) *
        𝔼.E τ (A t (t + (j + 1)) * e (t + (j + 1))) ω) := by
      have hfin : ∑ i ∈ Finset.range (t + 1), G t i = 0 :=
        Finset.sum_eq_zero fun i hi => hGz t i (by have := Finset.mem_range.mp hi; omega)
      have := (hasSum_nat_add_iff' (t + 1)).mpr (hGs t).hasSum
      rw [hfin, sub_zero] at this
      rw [← this.tsum_eq]
      refine tsum_congr fun j => ?_
      rw [show j + (t + 1) = t + (j + 1) by omega]
      simp only [hG, show t < t + (j + 1) by omega, ↓reduceIte]
      ring
    rw [hshift, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmono (pow_nonneg hβ0.le t)
  have hcol : ∀ m, ∑ t ∈ Finset.range m, G t m ≤ u m := by
    intro m
    have hsum : ∑ t ∈ Finset.range m, G t m =
        β ^ m * 𝔼.E τ ((∑ t ∈ Finset.range m, A t m) * e m) ω := by
      rw [Finset.sum_mul, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [hG, Finset.mem_range.mp ht, ↓reduceIte]
    rw [hsum]
    refine mul_le_mul_of_nonneg_left (𝔼.mono τ (fun ω' => ?_) ω) (pow_nonneg hβ0.le m)
    simp only [Pi.mul_apply, Finset.sum_apply]
    exact mul_le_of_le_one_left (he0 m ω') (hcolA m ω')
  have hfin := col_lemma hu0 hus hG0 hGz (fun t _ => hGs t) hH1 hcol
  have hEτ : 𝔼.E τ (e τ) ω ≤ 0 := by
    have hp : 0 < β ^ τ := pow_pos hβ0 τ
    simp only [hu] at hfin
    nlinarith [(hEe τ).1]
  have habs : |d τ ω| ≤ 0 := by
    have := abs_E_le_E_abs 𝔼 τ (d τ) ω
    rw [hdad τ] at this
    exact this.trans hEτ
  simpa using abs_nonpos_iff.mp habs

/-! ### When the present-value relations determine the price level -/

/-- Cochrane (2023), §7.4, p. 225: the difference of two solutions of the maturing-debt system with
the same surpluses solves the homogeneous system. -/
theorem homogeneous_of_two {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y y' s : ℕ → Ω → ℝ}
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hy' : ∀ t, MaturingSystem 𝔼 β A y' s t) (t : ℕ)
    (ω : Ω) : HasSum (fun j : ℕ => β ^ (j + 1) *
      𝔼.E t (A t (t + (j + 1)) * (y - y') (t + (j + 1))) ω) ((y - y') t ω) := by
  have := (hy t ω).sub (hy' t ω)
  convert this using 1
  · funext j
    simp only [Pi.sub_apply, mul_sub, map_sub]
  · simp only [Pi.sub_apply]; ring

/-- Cochrane (2023), §7.4, pp. 225–226: given one bounded solution, bounded solutions of the
maturing-debt system are unique if and only if the homogeneous system has no nonzero bounded
solution. -/
theorem unique_iff_homogeneous {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y₀ s : ℕ → Ω → ℝ}
    (hy₀ : ∀ t, MaturingSystem 𝔼 β A y₀ s t) (hb₀ : ∃ K, ∀ t ω, |y₀ t ω| ≤ K) :
    (∀ y, (∀ t, MaturingSystem 𝔼 β A y s t) → (∃ K, ∀ t ω, |y t ω| ≤ K) → y = y₀) ↔
      ∀ d : ℕ → Ω → ℝ, (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω) (d t ω)) →
        (∃ K, ∀ t ω, |d t ω| ≤ K) → d = 0 := by
  constructor
  · intro hu d hd hdb
    have hsol : ∀ t, MaturingSystem 𝔼 β A (y₀ + d) s t := by
      intro t ω
      have := (hy₀ t ω).add (hd t ω)
      convert this using 1
      · funext j
        simp only [Pi.add_apply, mul_add, map_add]
      · simp only [Pi.add_apply]; ring
    obtain ⟨K₀, hK₀⟩ := hb₀
    obtain ⟨K, hK⟩ := hdb
    have := hu (y₀ + d) hsol ⟨K₀ + K, fun t ω => (abs_add_le _ _).trans
      (add_le_add (hK₀ t ω) (hK t ω))⟩
    funext t ω
    have h := congrFun (congrFun this t) ω
    simp only [Pi.add_apply] at h
    simp only [Pi.zero_apply]
    linarith
  · intro hh y hy hyb
    have := hh (y - y₀) (homogeneous_of_two 𝔼 hy hy₀) (by
      obtain ⟨K, hK⟩ := hyb
      obtain ⟨K₀, hK₀⟩ := hb₀
      exact ⟨K + K₀, fun t ω => (abs_sub _ _).trans (add_le_add (hK t ω) (hK₀ t ω))⟩)
    exact sub_eq_zero.mp this

/-- Cochrane (2023), §7.4, p. 225: the government never buys back debt (`B_t^{(m)} ≥ B_{t−1}^{(m)}`
for `t < m`), inherited positions are nonnegative and the debt coming due is positive. -/
def NoBuyback (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ m ω, 0 ≤ D 0 m ω) ∧ (∀ t m ω, t < m → D t m ω ≤ D (t + 1) m ω) ∧ ∀ m ω, 0 < D m m ω

/-- Cochrane (2023), §7.4: without buy-backs, debt outstanding is nonnegative up to maturity. -/
theorem NoBuyback.nonneg {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (t m : ℕ) (htm : t ≤ m)
    (ω : Ω) : 0 ≤ D t m ω := by
  induction t with
  | zero => exact h.1 m ω
  | succ t ih => exact (ih (by omega)).trans (h.2.1 t m ω (by omega))

/-- Cochrane (2023), §7.4: without buy-backs the sale fractions are nonnegative. -/
theorem NoBuyback.frac_nonneg {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (t m : ℕ) (ω : Ω)
    (htm : t < m) : 0 ≤ fracSold D t m ω := by
  simp only [fracSold, Pi.div_apply, Pi.sub_apply]
  exact div_nonneg (sub_nonneg.mpr (h.2.1 t m ω htm)) (h.2.2 m ω).le

/-- Cochrane (2023), §7.4: without buy-backs each column of sale fractions sums to
`(B_{m−1}^{(m)} − B_{−1}^{(m)})/B_{m−1}^{(m)} ≤ 1`. -/
theorem NoBuyback.col_le_one {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (m : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range m, fracSold D t m ω ≤ 1 := by
  simp only [fracSold, Pi.div_apply, Pi.sub_apply]
  rw [← Finset.sum_div, Finset.sum_range_sub (fun t => D t m ω), div_le_one (h.2.2 m ω)]
  linarith [h.1 m ω]

/-- Cochrane (2023), eq. (7.5), p. 216: with nonnegative debt and price levels, the present-value
relation bounds the real value of maturing debt: `0 ≤ B_{t−1}^{(t)}/P_t ≤ M/(1−β)`. -/
theorem bounded_of_presentValue {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hx0 : ∀ t ω, 0 ≤ x t ω)
    (hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω) (hsb : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    (hpv : PresentValue 𝔼 β D x s t) (ω : Ω) :
    0 ≤ D t t ω * x t ω ∧ D t t ω * x t ω ≤ M / (1 - β) := by
  have hEx : ∀ u v ω', 0 ≤ 𝔼.E u (x v) ω' := by
    intro u v ω'
    have := 𝔼.mono u (show (fun _ => (0 : ℝ)) ≤ x v from fun ω'' => hx0 v ω'') ω'
    rwa [𝔼.const] at this
  have hterm : ∀ j, 0 ≤ debtTerm 𝔼 β D x t j ω := fun j =>
    mul_nonneg (pow_nonneg hβ0 j) (mul_nonneg (hD0 t j ω) (hEx _ _ ω))
  have h0 : debtTerm 𝔼 β D x t 0 ω = D t t ω * x t ω := by
    simp [debtTerm, hx t]
  refine ⟨h0 ▸ hterm 0, ?_⟩
  have h1 := le_hasSum (hpv ω).2 0 (fun j _ => hterm j)
  rw [h0] at h1
  refine h1.trans ?_
  have hg : HasSum (fun k : ℕ => β ^ k * M) (M / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right M
    simpa [div_eq_mul_inv, mul_comm] using this
  refine hasSum_le (fun k => ?_) (hpv ω).1.hasSum hg
  rw [surplusTerm]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (𝔼.abs_E_le (hsb _) _ ω))
    (pow_nonneg hβ0 k)

/-- Cochrane (2023), §7.4, pp. 225–226: **the present-value relations determine the price level
when the government never buys back debt.** Two adapted, positive price-level paths `1/P`, `1/P'`
that both satisfy every flow condition (7.1) and every present-value relation (7.5), for the same
predetermined debt without buy-backs and the same bounded surpluses (`0 < β < 1`), coincide. -/
theorem price_unique_noBuyback (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hnb : NoBuyback D)
    (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x') (hx0 : ∀ t ω, 0 ≤ x t ω)
    (hx0' : ∀ t ω, 0 ≤ x' t ω) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hpv : ∀ t, PresentValue 𝔼 β D x s t) (hpv' : ∀ t, PresentValue 𝔼 β D x' s t) :
    x = x' := by
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  have hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω := fun t j ω => hnb.nonneg t (t + j) (by omega) ω
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hb : ∀ t ω, |D t t ω * x t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx hx0 hD0 hsb (hpv t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hb' : ∀ t ω, |D t t ω * x' t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx' hx0' hD0 hsb (hpv' t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hzero := unique_of_noBuyback 𝔼 hβ0 hβ1 (A := fracSold D)
    (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (homogeneous_of_two 𝔼 hy hy') (K := M / (1 - β) + M / (1 - β))
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), §7.4, p. 225: **the present-value relations determine the price level under
the row condition.** If the sale fractions satisfy the row condition with `ρ < 1`, two adapted price
paths satisfying every flow condition with bounded real values of maturing debt coincide. -/
theorem price_unique_row (hpo : 𝔼.PullOut) {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (hrow : RowBound β (fracSold D) a ρ)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (hb' : ∀ t ω, |D t t ω * x' t ω| ≤ K) : x = x' := by
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hzero := unique_of_row 𝔼 hβ0 hρ1 hrow (homogeneous_of_two 𝔼 hy hy') (K := K + K)
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), eq. (7.17), p. 225: **(7.17) for the price level.** In an equilibrium with
bounded real maturing debt, under the row condition and with each sale fraction known at the last
sale date, `B_{t−1}^{(t)}/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem price_formula (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (hrow : RowBound β (fracSold D) a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  theoremW 𝔼 hpo hβ0 hρ1 hrow hA hs hsb
    (fun u => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm u).mp (hflow u)) hb t ω

/-! ### Special cases (§7.4, p. 225) -/

/-- Cochrane (2023), §7.4, p. 225 (special case): with no sales after date 0 (`A_t^{(m)} = 0` for
`t ≥ 1`), `W_t^{(k)} = 0` for `k ≥ 1` and `t ≥ 1`, so (7.17) reduces to (7.6). -/
theorem special_noSales {R : Type*} [CommRing R] {A : ℕ → ℕ → R}
    (hA : ∀ t m, 1 ≤ t → A t m = 0) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) : weight A t (k + 1) = 0 := by
  rw [weight_succ]
  exact Finset.sum_eq_zero fun n _ => by rw [hA _ _ (by omega), zero_mul]

/-- Cochrane (2023), §7.4, p. 225 (special case): pure one-period roll-over (`A_t^{(t+1)} = 1`, no
other sales) gives `W ≡ 1`, so (7.17) is the standard present value `E_t ∑ β^j s_{t+j}`. -/
theorem special_onePeriod {R : Type*} [CommRing R] {A : ℕ → ℕ → R}
    (h1 : ∀ t, A t (t + 1) = 1) (h0 : ∀ t j, A t (t + (j + 2)) = 0) (k : ℕ) :
    ∀ t, weight A t k = 1 := by
  induction k with
  | zero => exact fun t => weight_zero A t
  | succ k ih =>
    intro t
    rw [weight_succ, Finset.sum_range_succ, ih t, mul_one,
      show t + (k + 1) = t + k + 1 by omega, h1 (t + k)]
    rw [Finset.sum_eq_zero fun n hn => ?_, zero_add]
    have hn' := Finset.mem_range.mp hn
    rw [show t + k + 1 = t + n + (k - n - 1 + 2) by omega, h0, zero_mul]

/-- Cochrane (2023), §7.4, p. 225: with one-period debt only, the sale fractions are
`A_t^{(t+1)} = 1` and `A_t^{(t+j+2)} = 0`, so the one-period special case applies. -/
theorem fracSold_onePeriod {Ω : Type*} {D : ℕ → ℕ → Ω → ℝ} (h : MaturingDebt.OnePeriod D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) :
    (∀ t, fracSold D t (t + 1) = 1) ∧ ∀ t j, fracSold D t (t + (j + 2)) = 0 := by
  constructor
  · intro t
    funext ω
    have := h t 0
    simp only [zero_add] at this
    simp only [fracSold, Pi.div_apply, this, sub_zero, Pi.one_apply]
    exact div_self (hDmm _ ω)
  · intro t j
    funext ω
    have h1 := h (t + 1) j
    have h2 := h t (j + 1)
    rw [show t + 1 + (j + 1) = t + (j + 2) by omega] at h1
    rw [show t + (j + 1 + 1) = t + (j + 2) by omega] at h2
    simp only [fracSold, Pi.div_apply, Pi.zero_apply, h1, h2, sub_zero, zero_div]

/-! ### The printed (7.15) omits `β^j` (E7.2) -/

/-- Cochrane (2023), eq. (7.15), p. 225: the illustrative debt: one unit due at dates 0 and 1,
nothing
later, no sales. -/
noncomputable def exD : ℕ → ℕ → Unit → ℝ := fun _ m _ => if m ≤ 1 then 1 else 0

/-- Cochrane (2023), eq. (7.15), p. 225: the illustrative surpluses `s_0 = s_1 = 1`, zero
afterwards. -/
noncomputable def exS : ℕ → Unit → ℝ := fun t _ => if t ≤ 1 then 1 else 0

/-- Cochrane (2023), eq. (7.15), p. 225 (E7.2): **the printed (7.15) is false.** In the illustration
(perfect foresight, `β < 1`, price level `1/P_t = 1`) every flow condition and the corrected
present-value relation (with `β^j`, as in (7.5)) hold at date 0, but the printed version without
`β^j` would require `∑_j B_{−1}^{(j)}/P_j = 2` to equal `∑_j β^j s_j = 1 + β`. -/
theorem printed_715_fails {β : ℝ} (hβ1 : β < 1) :
    (∀ t, RealFlow perfectForesight β exD (fun _ _ => 1) exS t) ∧
      PresentValue perfectForesight β exD (fun _ _ => 1) exS 0 ∧
      HasSum (fun j => exD 0 j () * 1) 2 ∧ HasSum (fun j => β ^ j * exS j ()) (1 + β) ∧
      (2 : ℝ) ≠ 1 + β := by
  have hS : HasSum (fun j => β ^ j * exS j ()) (1 + β) := by
    have : HasSum (fun j => β ^ j * exS j ())
        (∑ j ∈ Finset.range 2, β ^ j * exS j ()) := hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [exS, show ¬ j ≤ 1 by omega]
    simpa [Finset.sum_range_succ, exS] using this
  refine ⟨fun t ω => ?_, fun ω => ?_, ?_, hS, by linarith⟩
  · have hz : (fun j : ℕ => β ^ (j + 1) * (sales exD t (t + (j + 1)) ω *
        perfectForesight.E t (fun _ => (1 : ℝ)) ω)) = fun _ => 0 := by
      funext j; simp [sales, exD]
    rw [hz]
    convert hasSum_zero using 1
    by_cases ht : t ≤ 1 <;> simp [exD, exS, ht]
  · have hsum : ∀ k, surplusTerm perfectForesight β exS 0 k ω = β ^ k * exS k () := by
      intro k; simp [surplusTerm, perfectForesight, zero_add]
    have hsumm : Summable (fun k => surplusTerm perfectForesight β exS 0 k ω) := by
      simp only [hsum]; exact hS.summable
    refine ⟨hsumm, ?_⟩
    have hpv : pvSurplus perfectForesight β exS 0 ω = 1 + β := by
      rw [pvSurplus]; simp only [hsum]; exact hS.tsum_eq
    rw [hpv]
    have : HasSum (fun j => debtTerm perfectForesight β exD (fun _ _ => 1) 0 j ω)
        (∑ j ∈ Finset.range 2, debtTerm perfectForesight β exD (fun _ _ => 1) 0 j ω) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [debtTerm, exD, show ¬ j ≤ 1 by omega]
    simpa [Finset.sum_range_succ, debtTerm, exD, perfectForesight, add_comm] using this
  · have : HasSum (fun j => exD 0 j () * 1) (∑ j ∈ Finset.range 2, exD 0 j () * 1) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [exD, show ¬ j ≤ 1 by omega]
    have h2 : (∑ j ∈ Finset.range 2, exD 0 j () * 1) = 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [exD]
    rwa [h2] at this

/-! ### The matrix display (7.16), corrected (E7.3) -/

/-- Cochrane (2023), eq. (7.16), p. 225, corrected: row `t` of the upper-triangular matrix has entry
`β^{m−t} B_{t−1}^{(m)}` in column `m ≥ t` (the printed display starts row `t` with `B_t^{(t+1)}`,
one index too late, and omits `β^{m−t}`). -/
noncomputable def pvMatrix (β : ℝ) (D : ℕ → ℕ → ℝ) (t m : ℕ) : ℝ :=
  if t ≤ m then β ^ (m - t) * D t m else 0

/-- Cochrane (2023), eqs. (7.15)–(7.16), p. 225 (perfect foresight): row `t` of the corrected matrix
applied to `p = (1/P_m)_m` is the real value of debt `∑_j β^j B_{t−1}^{(t+j)}/P_{t+j}`. -/
theorem pvMatrix_row (β : ℝ) (D : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (t : ℕ) (v : ℝ) :
    HasSum (fun m => pvMatrix β D t m * x m) v ↔
      HasSum (fun j => β ^ j * D t (t + j) * x (t + j)) v := by
  have hfin : ∑ m ∈ Finset.range t, pvMatrix β D t m * x m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      simp [pvMatrix, show ¬ t ≤ m by have := Finset.mem_range.mp hm; omega]
  rw [← hasSum_nat_add_iff' t, hfin, sub_zero]
  have : (fun j => pvMatrix β D t (j + t) * x (j + t)) =
      fun j => β ^ j * D t (t + j) * x (t + j) := by
    funext j
    rw [add_comm j t]
    simp only [pvMatrix, show t ≤ t + j by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [this]

/-! ### The non-uniqueness counterexample (E7.4) -/

/-- Cochrane (2023), §7.4, p. 225 (counterexample to uniqueness): at every date one unit of debt
matures and `2/β` units are due the following date, `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} = 2/β`. -/
noncomputable def cxD (β : ℝ) : ℕ → ℕ → Unit → ℝ :=
  fun t m _ => if m = t then 1 else if m = t + 1 then 2 / β else 0

/-- Cochrane (2023), §7.4: the constant surplus `s`. -/
def cxS (s0 : ℝ) : ℕ → Unit → ℝ := fun _ _ => s0

/-- Cochrane (2023), §7.4: the fundamental level `x* = s/(3(1−β))`. -/
noncomputable def cxStar (β s0 : ℝ) : ℝ := s0 / (3 * (1 - β))

/-- Cochrane (2023), §7.4: the family of price paths `1/P_t = x* + ε (−1/2)^t`. -/
noncomputable def cxX (β s0 ε : ℝ) : ℕ → Unit → ℝ := fun t _ => cxStar β s0 + ε * (-1 / 2) ^ t

/-- Cochrane (2023), §7.4: `B_{t−1}^{(t)} = 1` in the counterexample. -/
theorem cxD_self (β : ℝ) (t : ℕ) (u : Unit) : cxD β t t u = 1 := by simp [cxD]

/-- Cochrane (2023), §7.4: `B_{t−1}^{(t+1)} = 2/β` in the counterexample. -/
theorem cxD_succ (β : ℝ) (t : ℕ) (u : Unit) : cxD β t (t + 1) u = 2 / β := by simp [cxD]

/-- Cochrane (2023), §7.4: no debt due after `t + 1` in the counterexample. -/
theorem cxD_far (β : ℝ) (t k : ℕ) (u : Unit) : cxD β t (t + (k + 2)) u = 0 := by
  simp only [cxD, show ¬ (t + (k + 2) = t) by omega, show ¬ (t + (k + 2) = t + 1) by omega,
    ↓reduceIte]

/-- Cochrane (2023), §7.4: the policy buys back debt: the sale at `t` of maturity-`t+1` debt is
`1 − 2/β < 0` (for `0 < β < 2`). -/
theorem cx_buyback {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (t : ℕ) (u : Unit) :
    sales (cxD β) t (t + 1) u < 0 := by
  simp only [sales, Pi.sub_apply, cxD_self, cxD_succ]
  rw [sub_neg, lt_div_iff₀ hβ0]
  linarith

/-- Cochrane (2023), §7.4 (E7.4): **every member of the family satisfies every flow condition**
(7.1)/(7.14), for any `ε`, under perfect foresight with `0 < β < 1`. -/
theorem cx_flow {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ε : ℝ) (t : ℕ) :
    RealFlow perfectForesight β (cxD β) (cxX β s0 ε) (cxS s0) t := by
  intro u
  have hz : ∀ j ∉ Finset.range 2, β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
      perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u) = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have h1 : cxD β (t + 1) (t + (k + 2 + 1)) u = 0 := by
      rw [show t + (k + 2 + 1) = t + 1 + (k + 2) by omega, cxD_far]
    have h2 : cxD β t (t + (k + 2 + 1)) u = 0 := by
      rw [show t + (k + 2 + 1) = t + (k + 1 + 2) by omega, cxD_far]
    simp [sales, h1, h2]
  have hs : HasSum (fun j => β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
      perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u))
      (∑ j ∈ Finset.range 2, β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
        perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u)) :=
    hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  have e1 : cxD β (t + 1) (t + (0 + 1)) u = 1 := by rw [zero_add, cxD_self]
  have e2 : cxD β t (t + (0 + 1)) u = 2 / β := by rw [zero_add, cxD_succ]
  have e3 : cxD β (t + 1) (t + (1 + 1)) u = 2 / β := by
    rw [show t + (1 + 1) = t + 1 + 1 by omega, cxD_succ]
  have e4 : cxD β t (t + (1 + 1)) u = 0 := by
    rw [show t + (1 + 1) = t + (0 + 2) by omega, cxD_far]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sales, Pi.sub_apply]
  rw [show t + (0 + 1) = t + 1 by omega] at e1 e2
  simp only [show t + (1 + 1) = t + 2 by omega] at e3 e4
  simp only [e1, e2, e3, e4, cxD_self, cxX, cxS, cxStar, perfectForesight, LinearMap.id_apply]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  rw [pow_succ (-1 / 2 : ℝ) (t + 1), pow_succ (-1 / 2 : ℝ) t]
  field_simp
  ring

/-- Cochrane (2023), §7.4 (E7.4): **every member of the family satisfies every present-value
relation** (7.5)/(7.15): `x_t + 2 x_{t+1} = s/(1−β)`. -/
theorem cx_presentValue {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ε : ℝ) (t : ℕ) :
    PresentValue perfectForesight β (cxD β) (cxX β s0 ε) (cxS s0) t := by
  intro u
  have hsT : ∀ k, surplusTerm perfectForesight β (cxS s0) t k u = β ^ k * s0 := by
    intro k; simp [surplusTerm, perfectForesight, cxS]
  have hgeo : HasSum (fun k => β ^ k * s0) (s0 / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right s0
    simpa [div_eq_mul_inv, mul_comm] using this
  have hsumm : Summable (fun k => surplusTerm perfectForesight β (cxS s0) t k u) := by
    simp only [hsT]; exact hgeo.summable
  refine ⟨hsumm, ?_⟩
  have hpv : pvSurplus perfectForesight β (cxS s0) t u = s0 / (1 - β) := by
    rw [pvSurplus]; simp only [hsT]; exact hgeo.tsum_eq
  rw [hpv]
  have hz : ∀ j ∉ Finset.range 2, debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    simp [debtTerm, cxD_far]
  have hs : HasSum (fun j => debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u)
      (∑ j ∈ Finset.range 2, debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u) :=
    hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, debtTerm, add_zero,
    cxD_self, cxD_succ, cxX, cxStar, perfectForesight, LinearMap.id_apply, pow_zero, pow_one]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  rw [pow_succ (-1 / 2 : ℝ) t]
  field_simp
  ring

/-- Cochrane (2023), §7.4 (E7.4): for `|ε| < x*` (possible when `s > 0`, `β < 1`), every price
level in the family is positive. -/
theorem cx_pos {β s0 ε : ℝ} (hε : |ε| < cxStar β s0) (t : ℕ) (u : Unit) :
    0 < cxX β s0 ε t u := by
  simp only [cxX]
  have hq : |(-1 / 2 : ℝ) ^ t| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (by norm_num [abs_div])
  have : |ε * (-1 / 2) ^ t| ≤ |ε| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hq
  have := neg_abs_le (ε * (-1 / 2) ^ t)
  linarith

/-- Cochrane (2023), §7.4 (E7.4): the family is bounded, `|1/P_t| ≤ x* + |ε|`. -/
theorem cx_bounded (β s0 ε : ℝ) (t : ℕ) (u : Unit) :
    |cxX β s0 ε t u| ≤ |cxStar β s0| + |ε| := by
  simp only [cxX]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _)
    (by norm_num [abs_div]))

/-- Cochrane (2023), §7.4 (E7.4): **non-uniqueness**: different `ε` give different price paths, so
the flow and present-value relations (7.14)–(7.16) do not determine the price level. -/
theorem cx_ne {β s0 ε ε' : ℝ} (h : ε ≠ ε') : cxX β s0 ε ≠ cxX β s0 ε' := by
  intro hx
  have := congrFun (congrFun hx 0) ()
  simp only [cxX, pow_zero, mul_one] at this
  exact h (by linarith)

/-- Cochrane (2023), §7.4 (E7.4): the sale fractions of the counterexample:
`A_t^{(t+1)} = 1 − 2/β`, `A_t^{(t+2)} = 2/β`, `A_t^{(t+k+3)} = 0`. -/
theorem cx_frac (β : ℝ) (t : ℕ) :
    fracSold (cxD β) t (t + 1) = (fun _ => 1 - 2 / β) ∧
      fracSold (cxD β) t (t + 2) = (fun _ => 2 / β) ∧
      ∀ k, fracSold (cxD β) t (t + (k + 3)) = fun _ => 0 := by
  refine ⟨?_, ?_, fun k => ?_⟩
  · funext u
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, cxD_self, cxD_succ, div_one]
  · funext u
    have e1 : cxD β (t + 1) (t + 2) u = 2 / β := by
      rw [show t + 2 = t + 1 + 1 by omega, cxD_succ]
    have e2 : cxD β t (t + 2) u = 0 := by rw [show t + 2 = t + (0 + 2) by omega, cxD_far]
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, e1, e2, cxD_self, sub_zero, div_one]
  · funext u
    have e1 : cxD β (t + 1) (t + (k + 3)) u = 0 := by
      rw [show t + (k + 3) = t + 1 + (k + 2) by omega, cxD_far]
    have e2 : cxD β t (t + (k + 3)) u = 0 := by
      rw [show t + (k + 3) = t + (k + 1 + 2) by omega, cxD_far]
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, e1, e2, sub_zero, zero_div]

/-- Cochrane (2023), §7.4 (E7.4): the weights obey
`W^{(k+2)} = (1 − 2/β) W^{(k+1)} + (2/β) W^{(k)}`. -/
theorem cx_weight_rec (β : ℝ) (t k : ℕ) :
    weight (fracSold (cxD β)) t (k + 2) = (fun _ => 1 - 2 / β) * weight (fracSold (cxD β)) t (k + 1)
      + (fun _ => 2 / β) * weight (fracSold (cxD β)) t k := by
  have h1 := fun t => (cx_frac β t).1
  have h2 := fun t => (cx_frac β t).2.1
  have h3 := fun t => (cx_frac β t).2.2
  rw [weight_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun n hn => ?_, zero_add]
  · rw [show t + (k + 1 + 1) = t + (k + 1) + 1 by omega, h1,
      show t + (k + 1) + 1 = t + k + 2 by omega, h2]
    ring
  · have hn' := Finset.mem_range.mp hn
    rw [show t + (k + 1 + 1) = t + n + (k - n - 1 + 3) by omega, h3]
    funext u
    simp

/-- Cochrane (2023), §7.4 (E7.4): the weights in closed form,
`W^{(k)} = (β + 2(−2/β)^k)/(β + 2)`. -/
theorem cx_weight {β : ℝ} (hβ0 : 0 < β) (t k : ℕ) :
    weight (fracSold (cxD β)) t k = fun _ => (β + 2 * (-2 / β) ^ k) / (β + 2) := by
  have hb : β ≠ 0 := hβ0.ne'
  have hb2 : β + 2 ≠ 0 := by linarith
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rw [weight_zero]
      funext u
      simp only [Pi.one_apply, pow_zero, mul_one]
      field_simp
    · rw [weight_succ, Finset.sum_range_one, weight_zero, add_zero, (cx_frac β t).1]
      funext u
      simp only [Pi.mul_apply, Pi.one_apply, mul_one, zero_add, pow_one]
      field_simp
      ring
    · rw [cx_weight_rec, ih (k + 1) (by omega), ih k (by omega)]
      funext u
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [pow_succ (-2 / β) (k + 1), pow_succ (-2 / β) k]
      generalize (-2 / β) ^ k = q
      field_simp
      ring

/-- Cochrane (2023), §7.4 (E7.4): **(7.17) diverges**: `β^k W^{(k)} = (β^{k+1} + 2(−2)^k)/(β+2)`
does not tend to zero, so with `s ≠ 0` the series `∑_k β^k W^{(k)} s` is not summable. -/
theorem cx_formula_diverges {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : s0 ≠ 0) (t : ℕ) :
    ¬ Summable (fun k => formulaTerm perfectForesight β (fracSold (cxD β)) (cxS s0) t k ()) := by
  intro hsum
  have hterm : ∀ k, formulaTerm perfectForesight β (fracSold (cxD β)) (cxS s0) t k () =
      (β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0 := by
    intro k
    simp only [formulaTerm, cx_weight hβ0, perfectForesight, LinearMap.id_apply, Pi.mul_apply,
      cxS]
    have hb : β ≠ 0 := hβ0.ne'
    have hb2 : β + 2 ≠ 0 := by linarith
    rw [div_pow, pow_succ]
    field_simp
  have hlim := hsum.tendsto_atTop_zero
  simp only [hterm] at hlim
  have hlow : ∀ k : ℕ, |s0| / 3 ≤ |(β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0| := by
    intro k
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < β + 2)]
    have hpow : β ^ (k + 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have hpow0 : 0 ≤ β ^ (k + 1) := pow_nonneg hβ0.le _
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hnum : 1 ≤ |β ^ (k + 1) + 2 * (-2 : ℝ) ^ k| := by
      have habs : |2 * (-2 : ℝ) ^ k| = 2 * 2 ^ k := by
        rw [abs_mul, abs_pow]; norm_num
      have := abs_sub_abs_le_abs_sub (2 * (-2 : ℝ) ^ k) (-(β ^ (k + 1)))
      rw [abs_neg, abs_of_nonneg hpow0, habs, sub_neg_eq_add] at this
      rw [add_comm]
      linarith
    have hs : 0 ≤ |s0| := abs_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < |s0| / 3 := by positivity
  have hlim' : Tendsto (fun k : ℕ => |(β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0|) atTop
      (𝓝 0) := by simpa using hlim.abs
  obtain ⟨k, hk⟩ := (hlim'.eventually (gt_mem_nhds hpos)).exists
  exact absurd (hlow k) (not_le.mpr hk)

/-- Cochrane (2023), §7.4 (E7.4): the counterexample violates the row condition: for any bound
`a` the sum `∑_j β^{j+1} a_j` is at least `2 + β > 1`. -/
theorem cx_not_row {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ¬ ∃ a ρ, ρ < 1 ∧ RowBound β (fracSold (cxD β)) a ρ := by
  rintro ⟨a, ρ, hρ, hrow⟩
  obtain ⟨h1, h2, -⟩ := cx_frac β 0
  have ha0 : 2 / β - 1 ≤ a 0 := by
    have := hrow.2.1 0 0 ()
    rw [h1] at this
    simp only at this
    rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hβ0]; linarith)] at this
    exact this
  have ha1 : 2 / β ≤ a 1 := by
    have := hrow.2.1 0 1 ()
    rw [show 0 + (1 + 1) = 0 + 2 by rfl, h2] at this
    simp only at this
    rwa [abs_of_pos (by positivity)] at this
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0.le _) (hrow.1 j)
  have hpart := hrow.2.2.1.sum_le_tsum (Finset.range 2) fun j _ => hnn j
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one,
    show 1 + 1 = 2 from rfl] at hpart
  have h3 : β * (2 / β - 1) + β ^ 2 * (2 / β) = 2 + β := by field_simp; ring
  have h4 : β * (2 / β - 1) + β ^ 2 * (2 / β) ≤ β * a 0 + β ^ 2 * a 1 :=
    add_le_add (mul_le_mul_of_nonneg_left ha0 hβ0.le)
      (mul_le_mul_of_nonneg_left ha1 (by positivity))
  linarith [hrow.2.2.2]

end Cochrane.LongTermDebtDynamics.GeneralFormula

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Constraints on policy

Cochrane (2023), §7.5, pp. 226–229, equations (7.18)–(7.21).

The present-value relation at date 0, (7.18),
`∑_j β^j B_{−1}^{(j)} E_0(1/P_j) = E_0 ∑_j β^j s_j`, is the only restriction that surplus-neutral
debt policy places on the sequence `{E_0(1/P_j)}`.

## Main results

* `DivClosed`, `perfectForesight_divClosed`, `finiteTree_divClosed`: quotients of known variables
  are known (true for perfect foresight and for every finite event tree); needed to state the
  policy (7.19), `B_0^{(j)} = E_0 s_j / E_0(1/P_j)`.
* `polOne_*` — **Theorem P, existence** via (7.19): for any positive targets `E_0(1/P_j)`
  consistent with (7.18), selling `B_0^{(j)} = E_0 s_j / E_0(1/P_j)` at date 0 and never trading
  again satisfies every flow and present-value relation, achieves the targets, and gives positive
  price levels.
* `polTwo_*` — the second policy (7.20): buy back the long-term debt at date 0 and roll over
  one-period debt with `B_{j−1}^{(j)}/P_j = E_j ∑ β^k s_{j+k}`; it achieves the same targets.
* `policies_differ`: many debt policies support the same price-level path.
* `presentValue_zero_nominal`: conversely every equilibrium satisfies (7.18).
* `onePeriod_price_zero`: with only one-period debt outstanding, `P_0` is independent of the
  future price levels.
* `qe_tradeoff`, `qe_tradeoff_strict`: with nonnegative positions `B_{−1}^{(j)} ≥ 0`, debt policy
  cannot raise some price levels without lowering others; `qe_negative_position` shows the
  nonnegativity hypothesis is needed (E7.8).
* `offset_shock`, `offset_shock_cost`: debt policy can absorb a fiscal shock at date 0, but only at
  the cost of higher future price levels.
* `end_of_period_value` — (7.21): the real end-of-period value of debt equals
  `E_0 ∑_{j≥1} β^j s_j`, whatever the quantities `B_0^{(j)}`.
-/

namespace Cochrane.LongTermDebtDynamics.PolicyConstraints

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.5, p. 227: quotients of variables known at `t` are known at `t` (the
measurability fact needed to write the policy (7.19)). Like `PullOut`, it is not implied by the
`ExpectationSystem` axioms, so results that use it take it as a hypothesis. -/
def DivClosed : Prop :=
  ∀ t (f g : Ω → ℝ), 𝔼.E t f = f → 𝔼.E t g = g → 𝔼.E t (f / g) = f / g

/-- Cochrane (2023), §7.5: perfect foresight is closed under quotients. -/
theorem perfectForesight_divClosed : DivClosed perfectForesight := fun _ _ _ _ _ => rfl

/-- Cochrane (2023), §7.5: every finite event tree is closed under quotients (a quotient of
variables constant on information cells is constant on them). -/
theorem finiteTree_divClosed {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) : DivClosed T.toExpectationSystem := by
  intro t f g hf hg
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hf hg ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have h1 : f ω' = f ω := by
    rw [← congrFun hf ω', ← congrFun hf ω]; exact T.condE_congr f h
  have h2 : g ω' = g ω := by
    rw [← congrFun hg ω', ← congrFun hg ω]; exact T.condE_congr g h
  simp only [Pi.div_apply, h1, h2]

/-- Cochrane (2023), §7.5: `E_t(f/b) = E_t(f)/b` for `b` known at `t`. -/
theorem E_div_known (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {t : ℕ} {b : Ω → ℝ}
    (hb : 𝔼.E t b = b) (f : Ω → ℝ) : 𝔼.E t (f / b) = 𝔼.E t f / b := by
  have h1 : 𝔼.E t (1 / b) = 1 / b := hdc t 1 b (𝔼.const t 1) hb
  have : f / b = (1 / b) * f := by funext ω; simp [div_eq_inv_mul]
  rw [this, hpo t _ _ h1]
  funext ω
  simp [div_eq_inv_mul]

/-! ### Theorem P: the first policy (7.19) -/

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales `B_0^{(j)} = E_0 s_j / E_0(1/P_j)` for
targets `e_j = E_0(1/P_j)`. -/
noncomputable def bOne (s e : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ := 𝔼.E 0 (s j) / e j

/-- Cochrane (2023), eq. (7.19), p. 227: the debt policy: inherit `B_{−1}`, sell up to
`B_0^{(j)} = bOne j` at date 0, then never trade. -/
noncomputable def polOneD (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  if t = 0 then D0 m else bOne 𝔼 s e m

/-- Cochrane (2023), eq. (7.19), p. 227: the resulting price levels, `1/P_0 = e_0` and
`1/P_j = s_j / B_0^{(j)}` (eq. (7.9)). -/
noncomputable def polOneX (s e : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t = 0 then e 0 else s t / bOne 𝔼 s e t

/-- Cochrane (2023), §7.5, p. 227: the standing hypotheses of Theorem P: positive surpluses after
date 0 with positive date-0 expectations, positive targets known at date 0, and the targets
consistent with the present-value relation (7.18). -/
def Targets (β : ℝ) (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) : Prop :=
  (∀ m, 𝔼.E 0 (D0 m) = D0 m) ∧ (∀ j, 𝔼.E 0 (e j) = e j) ∧ (∀ j ω, 0 < e j ω) ∧
    (∀ j ω, 0 < s (j + 1) ω) ∧ (∀ j ω, 0 < 𝔼.E 0 (s (j + 1)) ω) ∧
    ∀ ω, HasSum (fun j => β ^ j * (D0 j ω * e j ω)) (pvSurplus 𝔼 β s 0 ω)

/-- Cochrane (2023), eq. (7.20), p. 227: one-period debt `B_{j−1}^{(j)} = E_0 PV_j / e_j` with
`PV_j = E_j ∑_k β^k s_{j+k}`. -/
noncomputable def cTwo (β : ℝ) (s e : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ :=
  𝔼.E 0 (pvSurplus 𝔼 β s j) / e j

/-- Cochrane (2023), eq. (7.20), p. 227: the second policy: buy back all long-term debt at date 0
and roll over one-period debt. -/
noncomputable def polTwoD (β : ℝ) (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  if t = 0 then D0 m else if m = t then cTwo 𝔼 β s e m else 0

/-- Cochrane (2023), eq. (7.20), p. 227: the price levels, `B_{j−1}^{(j)}/P_j = E_j ∑ β^k s_{j+k}`.
-/
noncomputable def polTwoX (β : ℝ) (s e : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t = 0 then e 0 else pvSurplus 𝔼 β s t / cTwo 𝔼 β s e t

variable {𝔼}

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales are known at every date. -/
theorem bOne_known (hdc : DivClosed 𝔼) {s e : ℕ → Ω → ℝ} (he : ∀ j, 𝔼.E 0 (e j) = e j)
    (j t : ℕ) : 𝔼.E t (bOne 𝔼 s e j) = bOne 𝔼 s e j :=
  ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) (hdc 0 _ _ (𝔼.E_E_self 0 _) (he j))

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales are positive. -/
theorem bOne_pos {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e)
    (j : ℕ) (ω : Ω) : 0 < bOne 𝔼 s e (j + 1) ω :=
  div_pos (hT.2.2.2.2.1 j ω) (hT.2.2.1 (j + 1) ω)

/-- Cochrane (2023), eq. (7.19), p. 227: the policy is predetermined. -/
theorem polOne_predetermined (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ}
    (hT : Targets 𝔼 β D0 s e) : Predetermined 𝔼 (polOneD 𝔼 D0 s e) := by
  refine ⟨fun m => ?_, fun t m => ?_⟩
  · simp only [polOneD, ↓reduceIte]; exact hT.1 m
  · simp only [polOneD, Nat.add_one_ne_zero, ↓reduceIte]
    exact bOne_known hdc hT.2.1 m t

/-- Cochrane (2023), eqs. (7.9), (7.19), p. 227: `E_t(1/P_{j+1}) = E_t s_{j+1} / B_0^{(j+1)}` for
every `t`; in particular the policy achieves the targets `E_0(1/P_j) = e_j`. -/
theorem polOne_E (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (t j : ℕ) :
    𝔼.E t (polOneX 𝔼 s e (j + 1)) = 𝔼.E t (s (j + 1)) / bOne 𝔼 s e (j + 1) := by
  simp only [polOneX, Nat.add_one_ne_zero, ↓reduceIte]
  exact E_div_known 𝔼 hpo hdc (bOne_known hdc hT.2.1 _ t) _

/-- Cochrane (2023), §7.5, p. 227 (Theorem P): **the policy achieves every target**,
`E_0(1/P_j) = e_j` for all `j`, including `1/P_0 = e_0`. -/
theorem polOne_achieves (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    𝔼.E 0 (polOneX 𝔼 s e j) = e j := by
  rcases j with _ | j
  · simp only [polOneX, ↓reduceIte]; exact hT.2.1 0
  · rw [polOne_E hpo hdc hT]
    funext ω
    simp only [bOne, Pi.div_apply]
    have h1 := hT.2.2.2.2.1 j ω
    have h2 := hT.2.2.1 (j + 1) ω
    field_simp

/-- Cochrane (2023), eq. (7.19), p. 227: `B_0^{(j)} E_0(1/P_j) = E_0 s_j`. -/
theorem polOne_719 (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    polOneD 𝔼 D0 s e 1 (j + 1) * 𝔼.E 0 (polOneX 𝔼 s e (j + 1)) = 𝔼.E 0 (s (j + 1)) := by
  rw [polOne_achieves hpo hdc hT]
  funext ω
  simp only [polOneD, one_ne_zero, ↓reduceIte, bOne, Pi.mul_apply, Pi.div_apply]
  have := hT.2.2.1 (j + 1) ω
  field_simp

/-- Cochrane (2023), §7.5, p. 227 (Theorem P): the price levels are positive. -/
theorem polOne_pos {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e)
    (t : ℕ) (ω : Ω) : 0 < polOneX 𝔼 s e t ω := by
  rcases t with _ | j
  · simp only [polOneX, ↓reduceIte]; exact hT.2.2.1 0 ω
  · simp only [polOneX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    exact div_pos (hT.2.2.2.1 j ω) (bOne_pos hT j ω)

/-- Cochrane (2023), §7.5, pp. 227–228 (Theorem P): **the policy satisfies every flow condition**
(7.1). -/
theorem polOne_flow (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    RealFlow 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) s t := by
  intro ω
  rcases t with _ | t
  · -- date 0
    have hterm : ∀ j, β ^ (j + 1) * (sales (polOneD 𝔼 D0 s e) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (polOneX 𝔼 s e (0 + (j + 1))) ω) =
        β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω - β ^ (j + 1) * (D0 (j + 1) ω * e (j + 1) ω) := by
      intro j
      have hD1 : ∀ m, polOneD 𝔼 D0 s e 1 m = bOne 𝔼 s e m := fun m => by simp [polOneD]
      have hD0' : ∀ m, polOneD 𝔼 D0 s e 0 m = D0 m := fun m => by simp [polOneD]
      rw [zero_add, polOne_achieves hpo hdc hT]
      simp only [sales, zero_add, hD1, hD0', Pi.sub_apply, bOne, Pi.div_apply]
      have := hT.2.2.1 (j + 1) ω
      field_simp
    simp only [hterm]
    have h1 := (hasSum_nat_add_iff' 1).mpr (hT.2.2.2.2.2 ω)
    have h2 := (hasSum_nat_add_iff' 1).mpr
      (summable_surplusTerm 𝔼 hβ0 hβ1 hsb 0 ω).hasSum
    simp only [Finset.sum_range_one, pow_zero, one_mul] at h1 h2
    have h3 := h2.sub h1
    convert h3 using 1
    · funext j; simp [surplusTerm]
    · simp only [polOneD, polOneX, ↓reduceIte, surplusTerm, pow_zero, one_mul, hs 0, pvSurplus]
      ring
  · -- dates after 0: no trading
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales (polOneD 𝔼 D0 s e) (t + 1) (t + 1 + (j + 1)) ω *
        𝔼.E (t + 1) (polOneX 𝔼 s e (t + 1 + (j + 1))) ω)) = fun _ => 0 := by
      funext j
      simp [sales, polOneD]
    rw [hz]
    convert hasSum_zero using 1
    simp only [polOneD, polOneX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    have := bOne_pos hT t ω
    field_simp
    ring

/-- Cochrane (2023), §7.5, pp. 227–228 (Theorem P): **the policy satisfies every present-value
relation** (7.5), with (7.18) at date 0. -/
theorem polOne_presentValue (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M)
    (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    PresentValue 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  rcases t with _ | t
  · convert hT.2.2.2.2.2 ω using 1
    funext j
    simp only [debtTerm, zero_add, polOneD, ↓reduceIte, polOne_achieves hpo hdc hT]
  · have heq : (fun j => debtTerm 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) (t + 1) j ω) =
        fun j => surplusTerm 𝔼 β s (t + 1) j ω := by
      funext j
      simp only [debtTerm, surplusTerm, polOneD, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show t + 1 + j = t + j + 1 by omega, polOne_E hpo hdc hT, Pi.div_apply]
      have := bOne_pos hT (t + j) ω
      field_simp
    rw [heq]
    exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb _ ω).hasSum

/-! ### The second policy (7.20): roll over one-period debt -/

/-- Cochrane (2023), eq. (7.20), p. 227: the present value of bounded surpluses is known at its
date. -/
theorem pvSurplus_adapted {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : 𝔼.E t (pvSurplus 𝔼 β s t) = pvSurplus 𝔼 β s t := by
  funext ω
  have hb : ∀ k ω', |surplusTerm 𝔼 β s t k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, surplusTerm 𝔼 β s t k ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  have : surplusTerm 𝔼 β s t k = β ^ k • 𝔼.E t (s (t + k)) := by
    funext ω'; simp [surplusTerm]
  rw [this, map_smul, 𝔼.E_E_self]

/-- Cochrane (2023), eq. (7.20), p. 227: with positive surpluses (positive date-0 expectations)
the date-0 expected present value is positive. -/
theorem E_pvSurplus_pos {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (j : ℕ) (ω : Ω)
    (hE : 0 < 𝔼.E 0 (s j) ω) : 0 < 𝔼.E 0 (pvSurplus 𝔼 β s j) ω := by
  have hb : ∀ k ω', |surplusTerm 𝔼 β s j k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  change 0 < 𝔼.E 0 (fun ω' => ∑' k, surplusTerm 𝔼 β s j k ω') ω
  rw [𝔼.E_tsum hβ0 hβ1 hb 0 ω]
  have hterm : ∀ k, 𝔼.E 0 (surplusTerm 𝔼 β s j k) ω = β ^ k * 𝔼.E 0 (s (j + k)) ω := by
    intro k
    have : surplusTerm 𝔼 β s j k = β ^ k • 𝔼.E j (s (j + k)) := by
      funext ω'; simp [surplusTerm]
    rw [this, map_smul, 𝔼.tower (Nat.zero_le j)]
    rfl
  simp only [hterm]
  have hnn : ∀ k, 0 ≤ β ^ k * 𝔼.E 0 (s (j + k)) ω := fun k => by
    refine mul_nonneg (pow_nonneg hβ0 k) ?_
    have := 𝔼.mono 0 (show (fun _ => (0 : ℝ)) ≤ s (j + k) from fun ω' => hs0 _ ω') ω
    rwa [𝔼.const] at this
  have hsumm : Summable (fun k => β ^ k * 𝔼.E 0 (s (j + k)) ω) :=
    Summable.of_nonneg_of_le hnn (fun k => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (𝔼.abs_E_le (hsb _) 0 ω)) (pow_nonneg hβ0 k))
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
  refine lt_of_lt_of_le ?_ (hsumm.le_tsum 0 fun k _ => hnn k)
  simpa using hE

/-- Cochrane (2023), eq. (7.20), p. 227: the second policy achieves the same targets,
`E_0(1/P_j) = e_j`, with positive price levels. -/
theorem polTwo_achieves (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    𝔼.E 0 (polTwoX 𝔼 β s e j) = e j ∧ ∀ ω, 0 < polTwoX 𝔼 β s e j ω := by
  rcases j with _ | j
  · simp only [polTwoX, ↓reduceIte]; exact ⟨hT.2.1 0, hT.2.2.1 0⟩
  · have hc : 𝔼.E 0 (cTwo 𝔼 β s e (j + 1)) = cTwo 𝔼 β s e (j + 1) :=
      hdc 0 _ _ (𝔼.E_E_self 0 _) (hT.2.1 _)
    have hEpos : ∀ ω, 0 < 𝔼.E 0 (pvSurplus 𝔼 β s (j + 1)) ω := fun ω =>
      E_pvSurplus_pos hβ0 hβ1 hsb hs0 (j + 1) ω (hT.2.2.2.2.1 j ω)
    simp only [polTwoX, Nat.add_one_ne_zero, ↓reduceIte]
    refine ⟨?_, fun ω => ?_⟩
    · rw [E_div_known 𝔼 hpo hdc hc]
      funext ω
      simp only [cTwo, Pi.div_apply]
      have := hEpos ω
      have := hT.2.2.1 (j + 1) ω
      field_simp
    · simp only [Pi.div_apply, cTwo]
      have hpv : 0 < pvSurplus 𝔼 β s (j + 1) ω := by
        have hnn : ∀ k, 0 ≤ surplusTerm 𝔼 β s (j + 1) k ω := fun k => by
          refine mul_nonneg (pow_nonneg hβ0 k) ?_
          have := 𝔼.mono (j + 1) (show (fun _ => (0 : ℝ)) ≤ s (j + 1 + k) from
            fun ω' => hs0 _ ω') ω
          rwa [𝔼.const] at this
        have hfirst : surplusTerm 𝔼 β s (j + 1) 0 ω = s (j + 1) ω := by
          simp [surplusTerm, hs (j + 1)]
        refine lt_of_lt_of_le ?_ ((summable_surplusTerm 𝔼 hβ0 hβ1 hsb _ ω).le_tsum 0
          fun k _ => hnn k)
        rw [hfirst]
        exact hT.2.2.2.1 j ω
      exact div_pos hpv (div_pos (hEpos ω) (hT.2.2.1 _ ω))

/-- Cochrane (2023), eq. (7.20), p. 227: the one-period debt of the second policy is positive and
known at every date. -/
theorem cTwo_pos_known (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω)
    (hT : Targets 𝔼 β D0 s e) (j t : ℕ) :
    (∀ ω, 0 < cTwo 𝔼 β s e (j + 1) ω) ∧ 𝔼.E t (cTwo 𝔼 β s e j) = cTwo 𝔼 β s e j := by
  refine ⟨fun ω => div_pos (E_pvSurplus_pos hβ0 hβ1 hsb hs0 (j + 1) ω (hT.2.2.2.2.1 j ω))
    (hT.2.2.1 _ ω), ?_⟩
  exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) (hdc 0 _ _ (𝔼.E_E_self 0 _) (hT.2.1 _))

/-- Cochrane (2023), eq. (7.20), p. 227: `B_{j−1}^{(j)} E_t(1/P_j) = E_t PV_j` for the second
policy. -/
theorem polTwo_E (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω)
    (hT : Targets 𝔼 β D0 s e) (t j : ℕ) (ω : Ω) :
    cTwo 𝔼 β s e (j + 1) ω * 𝔼.E t (polTwoX 𝔼 β s e (j + 1)) ω =
      𝔼.E t (pvSurplus 𝔼 β s (j + 1)) ω := by
  have hpos := (cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT j t).1
  have hk := (cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT (j + 1) t).2
  simp only [polTwoX, Nat.add_one_ne_zero, ↓reduceIte]
  rw [E_div_known 𝔼 hpo hdc hk, Pi.div_apply]
  have := hpos ω
  field_simp

/-- Cochrane (2023), eq. (7.20), p. 227: **the second policy satisfies every flow condition.** -/
theorem polTwo_flow (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    RealFlow 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) s t := by
  intro ω
  have hrec := fun u => congrFun (pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb u) ω
  rcases t with _ | t
  · -- date 0: buy back long debt, issue one-period debt
    have hterm : ∀ j, β ^ (j + 1) * (sales (polTwoD 𝔼 β D0 s e) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (polTwoX 𝔼 β s e (0 + (j + 1))) ω) =
        (Pi.single 0 (β * 𝔼.E 0 (pvSurplus 𝔼 β s 1) ω) : ℕ → ℝ) j -
          β ^ (j + 1) * (D0 (j + 1) ω * e (j + 1) ω) := by
      intro j
      rw [zero_add, (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT (j + 1)).1]
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT 0 0 ω
        rw [(polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT 1).1] at h1
        simp only [sales, polTwoD, zero_add, one_ne_zero, ↓reduceIte, Pi.sub_apply,
          Pi.single_eq_same, pow_one]
        rw [← h1]
        ring
      · simp only [sales, polTwoD, zero_add, one_ne_zero, ↓reduceIte, Pi.sub_apply,
          show j + 1 + 1 ≠ 1 by omega, Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
        simp
    simp only [hterm]
    have h1 := (hasSum_nat_add_iff' 1).mpr (hT.2.2.2.2.2 ω)
    simp only [Finset.sum_range_one, pow_zero, one_mul] at h1
    have h2 := (hasSum_pi_single 0 (β * 𝔼.E 0 (pvSurplus 𝔼 β s 1) ω)).sub h1
    convert h2 using 1
    have h0 := hrec 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h0
    simp only [polTwoD, polTwoX, ↓reduceIte]
    linarith
  · -- later dates: one-period roll-over
    obtain ⟨hpos, -⟩ := cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT t 0
    have hterm : (fun j : ℕ => β ^ (j + 1) * (sales (polTwoD 𝔼 β D0 s e) (t + 1)
        (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (polTwoX 𝔼 β s e (t + 1 + (j + 1))) ω)) =
        Pi.single 0 (β * 𝔼.E (t + 1) (pvSurplus 𝔼 β s (t + 1 + 1)) ω) := by
      funext j
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT (t + 1) (t + 1) ω
        simp only [sales, polTwoD, Nat.add_one_ne_zero, ↓reduceIte, Pi.sub_apply,
          show t + 1 + (0 + 1) ≠ t + 1 by omega, zero_add, Pi.zero_apply, sub_zero,
          Pi.single_eq_same, pow_one]
        rw [h1]
      · simp only [sales, polTwoD, Nat.add_one_ne_zero, ↓reduceIte,
          show t + 1 + (j + 1 + 1) ≠ t + 1 by omega, show t + 1 + (j + 1 + 1) ≠ t + 1 + 1 by omega,
          Pi.sub_apply, sub_self, Pi.zero_apply, zero_mul, mul_zero,
          Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
    rw [hterm]
    convert hasSum_pi_single 0 (β * 𝔼.E (t + 1) (pvSurplus 𝔼 β s (t + 1 + 1)) ω) using 1
    have h0 := hrec (t + 1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
    simp only [polTwoD, polTwoX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    have := hpos ω
    field_simp
    linarith

/-- Cochrane (2023), eq. (7.20), p. 227: **the second policy satisfies every present-value
relation.** -/
theorem polTwo_presentValue (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    PresentValue 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  rcases t with _ | t
  · convert hT.2.2.2.2.2 ω using 1
    funext j
    simp only [debtTerm, zero_add, polTwoD, ↓reduceIte,
      (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT j).1]
  · have heq : (fun j => debtTerm 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) (t + 1) j ω) =
        Pi.single 0 (pvSurplus 𝔼 β s (t + 1) ω) := by
      funext j
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT (t + 1) t ω
        rw [pvSurplus_adapted hβ0 hβ1 hsb] at h1
        simp only [debtTerm, polTwoD, Nat.add_one_ne_zero, ↓reduceIte, add_zero, pow_zero,
          one_mul, Pi.single_eq_same]
        exact h1
      · simp only [debtTerm, polTwoD, Nat.add_one_ne_zero, ↓reduceIte,
          show t + 1 + (j + 1) ≠ t + 1 by omega, Pi.zero_apply, zero_mul, mul_zero,
          Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
    rw [heq]
    exact hasSum_pi_single 0 _

/-- Cochrane (2023), §7.5, p. 227 (bullet, and p. 226): **many debt policies support the same
price-level path.** The two policies achieve the same `{E_0(1/P_j)}` and `P_0` but differ: the first
leaves `B_0^{(2)} > 0` outstanding, the second `B_0^{(2)} = 0`. -/
theorem policies_differ (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (ω : Ω) :
    (∀ j, 𝔼.E 0 (polOneX 𝔼 s e j) = 𝔼.E 0 (polTwoX 𝔼 β s e j)) ∧
      polOneD 𝔼 D0 s e 1 2 ω ≠ polTwoD 𝔼 β D0 s e 1 2 ω := by
  refine ⟨fun j => by rw [polOne_achieves hpo hdc hT,
    (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT j).1], ?_⟩
  have h1 : polOneD 𝔼 D0 s e 1 2 ω = bOne 𝔼 s e 2 ω := by simp [polOneD]
  have h2 : polTwoD 𝔼 β D0 s e 1 2 ω = 0 := by simp [polTwoD]
  rw [h1, h2]
  exact (bOne_pos hT 1 ω).ne'

/-! ### Consequences of (7.18) -/

/-- Cochrane (2023), eq. (7.18), p. 227: conversely, every equilibrium satisfies (7.18), written
with nominal bond prices: `∑_j Q_0^{(j)} B_{−1}^{(j)} = P_0 E_0 ∑_j β^j s_j`. -/
theorem presentValue_zero_nominal (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hpv : PresentValue 𝔼 β D x s 0) (ω : Ω) :
    HasSum (fun j => bondPrice 𝔼 β P x 0 j ω * D 0 (0 + j) ω) (P 0 ω * pvSurplus 𝔼 β s 0 ω) :=
  nominalValue_eq 𝔼 hpo hP 0 ω (hpv ω).2

/-- Cochrane (2023), §7.5, p. 228: with only one-period debt outstanding at date 0
(`B_{−1}^{(j)} = 0` for `j ≥ 1`), `B_{−1}^{(0)}/P_0 = E_0 ∑ β^j s_j`: future price levels
(whatever debt policy sets them) do not affect `P_0`. -/
theorem onePeriod_price_zero {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (hD : ∀ j, D 0 (j + 1) = 0) (hpv : PresentValue 𝔼 β D x s 0) (ω : Ω) :
    D 0 0 ω * x 0 ω = pvSurplus 𝔼 β s 0 ω := by
  have hs : HasSum (fun j => debtTerm 𝔼 β D x 0 j ω) (D 0 0 ω * x 0 ω) := by
    have : (fun j => debtTerm 𝔼 β D x 0 j ω) = Pi.single 0 (D 0 0 ω * x 0 ω) := by
      funext j
      rcases j with _ | j
      · simp [debtTerm, hx 0]
      · simp [debtTerm, hD j]
    rw [this]
    exact hasSum_pi_single 0 _
  exact hs.unique (hpv ω).2

/-- Cochrane (2023), §7.5, p. 228: **no free lunch for QE.** With nonnegative inherited positions
`B_{−1}^{(j)} ≥ 0` and the same surpluses, two price paths both consistent with (7.18), the second
with weakly higher expected price levels at every date with debt outstanding
(`E_0(1/P'_j) ≤ E_0(1/P_j)` when `B_{−1}^{(j)} > 0`), have the same expected price level at every
such date: a QE policy cannot raise near-term price levels without lowering some other. -/
theorem qe_tradeoff {β : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ} {V : ℝ} (hd : ∀ j, 0 ≤ d j)
    (h : HasSum (fun j => β ^ j * (d j * e j)) V) (h' : HasSum (fun j => β ^ j * (d j * e' j)) V)
    (hle : ∀ j, 0 < d j → e' j ≤ e j) (j : ℕ) (hdj : 0 < d j) : e' j = e j := by
  have hdiff := h.sub h'
  rw [sub_self] at hdiff
  have hnn : ∀ i, 0 ≤ β ^ i * (d i * e i) - β ^ i * (d i * e' i) := fun i => by
    rw [← mul_sub, ← mul_sub]
    refine mul_nonneg (pow_nonneg hβ0.le i) ?_
    rcases (hd i).lt_or_eq with hdi | hdi
    · exact mul_nonneg (hd i) (sub_nonneg.mpr (hle i hdi))
    · rw [← hdi, zero_mul]
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hdiff) j
  simp only [Pi.zero_apply, ← mul_sub] at hz
  have := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero j hβ0.ne')
  have := (mul_eq_zero.mp this).resolve_left hdj.ne'
  linarith

/-- Cochrane (2023), §7.5, p. 228 (generalised "stepping on a rake"): with nonnegative inherited
positions, raising the expected price level at some date with debt outstanding requires lowering
it at some other date with debt outstanding. -/
theorem qe_tradeoff_strict {β : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ} {V : ℝ}
    (hd : ∀ j, 0 ≤ d j) (h : HasSum (fun j => β ^ j * (d j * e j)) V)
    (h' : HasSum (fun j => β ^ j * (d j * e' j)) V) {j : ℕ} (hdj : 0 < d j) (hj : e' j < e j) :
    ∃ i, 0 < d i ∧ e i < e' i := by
  by_contra hcon
  push Not at hcon
  exact absurd (qe_tradeoff hβ0 hd h h' hcon j hdj) hj.ne

/-- Cochrane (2023), §7.5, p. 228 (E7.8): the nonnegativity of positions is needed. With
`B_{−1}^{(0)} = 1` and a negative position `B_{−1}^{(1)} = −1` (the government is long the
date-1 bond), lowering both `1/P_0` and `1/P_1` (raising both price levels) keeps (7.18). -/
theorem qe_negative_position {β δ x0 e1 : ℝ} (hβ0 : 0 < β) (hδ : 0 < δ) :
    let d : ℕ → ℝ := fun j => if j = 0 then 1 else if j = 1 then -1 else 0
    let e : ℕ → ℝ := fun j => if j = 0 then x0 else e1
    let e' : ℕ → ℝ := fun j => if j = 0 then x0 - δ else e1 - δ / β
    HasSum (fun j => β ^ j * (d j * e j)) (x0 - β * e1) ∧
      HasSum (fun j => β ^ j * (d j * e' j)) (x0 - β * e1) ∧ e' 0 < e 0 ∧ e' 1 < e 1 := by
  intro d e e'
  have hz : ∀ (f : ℕ → ℝ), ∀ j ∉ Finset.range 2, β ^ j * (d j * f j) = 0 := by
    intro f j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [d, show j ≠ 0 by omega, show j ≠ 1 by omega]
  have h1 : HasSum (fun j => β ^ j * (d j * e j)) (∑ j ∈ Finset.range 2, β ^ j * (d j * e j)) :=
    hasSum_sum_of_ne_finset_zero (hz e)
  have h2 : HasSum (fun j => β ^ j * (d j * e' j))
      (∑ j ∈ Finset.range 2, β ^ j * (d j * e' j)) := hasSum_sum_of_ne_finset_zero (hz e')
  have v1 : ∑ j ∈ Finset.range 2, β ^ j * (d j * e j) = x0 - β * e1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d, e]
    norm_num
    ring
  have v2 : ∑ j ∈ Finset.range 2, β ^ j * (d j * e' j) = x0 - β * e1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d, e']
    norm_num
    field_simp
    ring
  rw [v1] at h1
  rw [v2] at h2
  refine ⟨h1, h2, ?_, ?_⟩
  · simp only [e, e', ↓reduceIte]; linarith
  · simp only [e, e', one_ne_zero, ↓reduceIte]
    have : 0 < δ / β := div_pos hδ hβ0
    linarith

/-- Cochrane (2023), §7.5, p. 228: **debt policy can offset a fiscal shock.** Suppose (7.18)
holds, `B_{−1}^{(0)} x_0 + ∑_{j≥1} β^j B_{−1}^{(j)} e_j = V`, and the present value of surpluses
falls to `V − Δ`. Lowering the target `e_{j₀}` of one maturity with `B_{−1}^{(j₀)} > 0` by
`Δ/(β^{j₀} B_{−1}^{(j₀)})` restores (7.18) with the same `1/P_0 = x_0`: no current inflation, at the
cost of a higher price level at `j₀`. -/
theorem offset_shock {β V R Δ x0 : ℝ} (hβ0 : 0 < β) {d e : ℕ → ℝ} (j₀ : ℕ)
    (hd : 0 < d (j₀ + 1))
    (hR : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e (j + 1))) R) (h718 : d 0 * x0 + R = V) :
    let e' : ℕ → ℝ := fun j => if j = j₀ + 1 then e j - Δ / (β ^ j * d j) else e j
    HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e' (j + 1))) (R - Δ) ∧
      d 0 * x0 + (R - Δ) = V - Δ ∧ (0 < Δ → e' (j₀ + 1) < e (j₀ + 1)) := by
  intro e'
  have hp : 0 < β ^ (j₀ + 1) * d (j₀ + 1) := mul_pos (pow_pos hβ0 _) hd
  refine ⟨?_, by linarith, fun hΔ => ?_⟩
  · have hcorr : HasSum (fun j => if j = j₀ then Δ else 0) Δ := hasSum_ite_eq j₀ Δ
    convert hR.sub hcorr using 1
    funext j
    by_cases hj : j = j₀
    · subst hj
      simp only [e', ↓reduceIte]
      field_simp
    · simp only [e', hj, ↓reduceIte, show j + 1 ≠ j₀ + 1 by omega, sub_zero]
  · simp only [e', ↓reduceIte]
    have : 0 < Δ / (β ^ (j₀ + 1) * d (j₀ + 1)) := div_pos hΔ hp
    linarith

/-- Cochrane (2023), §7.5, p. 228: **debt policy cannot eliminate the inflation.** If the present
value falls (`V' < V`) and `1/P_0 = x_0` is held fixed, then with nonnegative positions some
date with debt outstanding has a lower `E_0(1/P_j)` (a higher expected price level). -/
theorem offset_shock_cost {β V V' R R' x0 : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hR : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e (j + 1))) R)
    (hR' : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e' (j + 1))) R')
    (h718 : d 0 * x0 + R = V) (h718' : d 0 * x0 + R' = V') (hVV : V' < V) :
    ∃ j, 0 < d (j + 1) ∧ e' (j + 1) < e (j + 1) := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ j, β ^ (j + 1) * (d (j + 1) * e (j + 1)) ≤
      β ^ (j + 1) * (d (j + 1) * e' (j + 1)) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le _)
    rcases (hd (j + 1)).lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (hcon j h) (hd _)
    · rw [← h, zero_mul, zero_mul]
  have := hasSum_le hle hR hR'
  linarith

/-- Cochrane (2023), eq. (7.21), p. 228: **the end-of-period value of debt.** In any equilibrium
(present value at date 1, dominated debt series), `∑_{j≥1} β^j B_0^{(j)} E_0(1/P_j) =
E_0 ∑_{j≥1} β^j s_j`, whatever the quantities `B_0^{(j)}` sold. -/
theorem end_of_period_value (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hdom : DebtDominated 𝔼 β D x 1)
    (hpv : PresentValue 𝔼 β D x s 1) (ω : Ω) :
    HasSum (fun j => β ^ (j + 1) * (D 1 (j + 1) ω * 𝔼.E 0 (x (j + 1)) ω))
      (pvSurplus 𝔼 β s 0 ω - s 0 ω) := by
  have h1 := (hasSum_E_debtValue_succ 𝔼 hpo hD (t := 0) hdom ω).mul_left β
  have hV : debtValue 𝔼 β D x 1 = pvSurplus 𝔼 β s 1 := by
    funext ω'; exact (hpv ω').2.tsum_eq
  have hrec := congrFun (pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb 0) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at hrec
  rw [hV] at h1
  convert h1 using 1
  · funext j
    rw [zero_add, add_comm 1 j, pow_succ]
    ring
  · linarith

/-- Cochrane (2023), eq. (7.21), p. 228, in nominal form: `∑_{j≥1} Q_0^{(j)} B_0^{(j)} / P_0 =
E_0 ∑_{j≥1} β^j s_j`. -/
theorem end_of_period_value_nominal (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hdom : DebtDominated 𝔼 β D x 1)
    (hpv : PresentValue 𝔼 β D x s 1) (ω : Ω) :
    HasSum (fun j => bondPrice 𝔼 β P x 0 (j + 1) ω * D 1 (j + 1) ω * x 0 ω)
      (pvSurplus 𝔼 β s 0 ω - s 0 ω) := by
  convert end_of_period_value hpo hβ0 hβ1 hD hs hsb hdom hpv ω using 1
  funext j
  rw [bondPrice_eq 𝔼 hpo hP]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add]
  linear_combination (β ^ (j + 1) * D 1 (j + 1) ω * 𝔼.E 0 (x (j + 1)) ω) * hPx 0 ω

end Cochrane.LongTermDebtDynamics.PolicyConstraints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quantitative easing and friends

Cochrane (2023), §7.6, pp. 229–234, equations (7.22)–(7.24).

The Treasury keeps a geometric maturity structure `B_{t−1}^{(t+j)} = ω^j B`; the central bank buys
or sells long-term bonds once at date 0, `B̃_0^{(j)}` (held to maturity), and issues one-period
reserves `M_{t−1}^{(t)}`. As in the book the path after the date-0 shock is perfect foresight
(price levels are real numbers `P_j > 0`); the maturity-structure irrelevance result of §7.6.2 is
proved for an arbitrary expectation system.

## Main results

* `steady_state` — (7.22): `∑_j β^j ω^j B/P = B/(P(1−βω)) = s/(1−β)`, and the steady-state price
  level `steady_price`.
* `pv_iff_723` — (7.23): with (7.22), the present-value relation at `t` is equivalent to
  `M_{t−1}^{(t)} P/(B P_t) + ∑_{j≥t} β^{j−t}(ω^{j−t} + B̃_0^{(j)}/B) P/P_j = 1/(1−βω)`.
* `reserves_unique`, `reserves_formula`: reverse engineering: given the price path and the QE
  purchases, (7.23) determines the reserves uniquely ("All M" when `B̃ = 0`).
* `qe_unique`: given the price path and the reserves, the QE purchases are unique;
  `qe_exists`: they exist (explicit formula) when the residual's tail series converge (e.g. bounded,
  `qe_residual_summable`); `qe_exists_necessary`, `qe_counterexample`: existence requires
  `β^N R_{t+N} → 0` and fails for reserves making `R_t = β^{−t}` (`solve_tail*`).
* `pv_iff_724` — (7.24): the same relation written with bond prices `Q_t^{(j)} = β^{j−t} P_t/P_j`.
* `Irrelevance.maturity_irrelevance`: (§7.6.2) any two debt policies with the same nominal market
value at
  each date satisfy the same present-value relations, under uncertainty.
* `strong_qe`: (p. 233) with `B_0^{(j)} = P_j s_j`, scaling the supply by `λ` scales `P_j` by `λ`
  and the bond price `Q_0^{(j)}` by `1/λ`: a 1% *decrease* in supply *raises* the bond price by
  about 1% (the book says it lowers it).
-/

namespace Cochrane.LongTermDebtDynamics.QuantitativeEasing

open Filter Topology MaturityStructure

/-- Cochrane (2023), eq. (7.22), p. 230: the steady state with a geometric maturity structure,
`∑_j β^j ω^j B/P = B/(P(1−βω))`, for `0 ≤ βω < 1`. -/
theorem steady_state {β ω B P : ℝ} (h0 : 0 ≤ β * ω) (h1 : β * ω < 1) :
    HasSum (fun j : ℕ => β ^ j * (ω ^ j * B / P)) (B / (P * (1 - β * ω))) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_right (B / P)
  convert this using 1
  · funext j; rw [mul_pow]; ring
  · rw [div_mul_eq_div_div, div_eq_mul_inv, mul_comm]

/-- Cochrane (2023), eq. (7.22), p. 230: the steady-state price level solves
`B/(P(1−βω)) = s/(1−β)`, i.e. `P = B(1−β)/(s(1−βω))`. -/
theorem steady_price {β ω B P s : ℝ} (h1 : β * ω < 1) (hβ : β < 1) (hP : 0 < P) (hs : s ≠ 0) :
    B / (P * (1 - β * ω)) = s / (1 - β) ↔ P = B * (1 - β) / (s * (1 - β * ω)) := by
  have h2 : 1 - β * ω ≠ 0 := by linarith
  have h3 : 1 - β ≠ 0 := by linarith
  rw [div_eq_div_iff (mul_ne_zero hP.ne' h2) h3, eq_div_iff (mul_ne_zero hs h2)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §7.6.1, p. 230: the present-value relation at `t ≥ 1` with Treasury debt
`ω^{j−t} B`, QE bonds `B̃_0^{(j)} = b j` and reserves `M_{t−1}^{(t)} = Mr t` (perfect foresight):
`M_{t−1}^{(t)}/P_t + ∑_{j≥t} β^{j−t}(ω^{j−t}B + B̃_0^{(j)})/P_j = s/(1−β)`. -/
def QEPresentValue (β ω B s : ℝ) (b Mr P : ℕ → ℝ) (t : ℕ) : Prop :=
  HasSum (fun k : ℕ => β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k))) (s / (1 - β) - Mr t / P t)

/-- Cochrane (2023), eq. (7.23), p. 230: the normalised present-value relation
`M_{t−1}^{(t)} P/(B P_t) + ∑_{j≥t} β^{j−t}(ω^{j−t} + B̃_0^{(j)}/B) P/P_j = 1/(1−βω)`. -/
def Eq723 (β ω B Pss : ℝ) (b Mr P : ℕ → ℝ) (t : ℕ) : Prop :=
  HasSum (fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k)))
    (1 / (1 - β * ω) - Mr t * Pss / (B * P t))

/-- Cochrane (2023), eq. (7.23), p. 230: **using the steady state (7.22), the present-value
relation is equivalent to (7.23).** -/
theorem pv_iff_723 {β ω B s Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) (h1 : β * ω < 1)
    (hss : B / (Pss * (1 - β * ω)) = s / (1 - β)) {b Mr P : ℕ → ℝ} (t : ℕ) :
    QEPresentValue β ω B s b Mr P t ↔ Eq723 β ω B Pss b Mr P t := by
  have hc : Pss / B ≠ 0 := div_ne_zero hP.ne' hB.ne'
  unfold QEPresentValue Eq723
  rw [← hasSum_mul_left_iff hc]
  have h2 : 1 - β * ω ≠ 0 := by linarith
  have hfun : (fun k : ℕ => Pss / B * (β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k)))) =
      fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k)) := by
    funext k
    field_simp
  have hval : Pss / B * (s / (1 - β) - Mr t / P t) = 1 / (1 - β * ω) - Mr t * Pss / (B * P t) := by
    rw [← hss]
    field_simp
  rw [hfun, hval]

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering): given the price path and the QE
purchases (with a convergent series `S_t = ∑_k β^k (ω^k + B̃/B) P/P_{t+k}`), (7.23) holds exactly
for
the reserves `M_{t−1}^{(t)} = (B P_t / P)(1/(1−βω) − S_t)`, and for no others. -/
theorem reserves_formula {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {b Mr P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) {S : ℝ}
    (hS : HasSum (fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k))) S) :
    Eq723 β ω B Pss b Mr P t ↔ Mr t = B * P t / Pss * (1 / (1 - β * ω) - S) := by
  unfold Eq723
  constructor
  · intro h
    have := h.unique hS
    have hPt' := (hPt t).ne'
    field_simp at this ⊢
    rw [mul_sub, mul_one_div]
    linarith
  · intro h
    convert hS using 1
    rw [h]
    have hPt' := (hPt t).ne'
    field_simp
    ring

/-- Cochrane (2023), §7.6.1, p. 230: the reserves supporting a price path with given QE purchases
are unique. -/
theorem reserves_unique {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {b Mr Mr' P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) (h : Eq723 β ω B Pss b Mr P t)
    (h' : Eq723 β ω B Pss b Mr' P t) : Mr t = Mr' t := by
  have := h.unique h'
  have hPt' := (hPt t).ne'
  have hc : Pss / (B * P t) ≠ 0 := div_ne_zero hP.ne' (mul_ne_zero hB.ne' hPt')
  have : Mr t * (Pss / (B * P t)) = Mr' t * (Pss / (B * P t)) := by
    rw [mul_div_assoc', mul_div_assoc']; linarith
  exact mul_right_cancel₀ hc this

/-- Cochrane (2023), §7.6.1, p. 230 ("All M"): with no QE purchases, (7.23) determines the
reserves `M_{t−1}^{(t)} = (B P_t/P)(1/(1−βω) − ∑_k (βω)^k P/P_{t+k})`. -/
theorem all_M {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {Mr P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) {S : ℝ}
    (hS : HasSum (fun k : ℕ => (β * ω) ^ k * (Pss / P (t + k))) S) :
    Eq723 β ω B Pss (fun _ => 0) Mr P t ↔ Mr t = B * P t / Pss * (1 / (1 - β * ω) - S) := by
  refine reserves_formula hB hP hPt t ?_
  convert hS using 1
  funext k
  rw [mul_pow]
  simp only [zero_div, add_zero]
  ring

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering, the other direction): given the price
path and the reserves, the QE purchases satisfying (7.23) at every date `t ≥ 1` are unique. -/
theorem qe_unique {β ω B Pss : ℝ} (hB : 0 < B) {b b' Mr P : ℕ → ℝ} (hPt : ∀ t, 0 < P t)
    (h : ∀ t, Eq723 β ω B Pss b Mr P (t + 1)) (h' : ∀ t, Eq723 β ω B Pss b' Mr P (t + 1))
    (hPss : Pss ≠ 0) (t : ℕ) : b (t + 1) = b' (t + 1) := by
  -- `g_j = (b_j − b'_j) P/(B P_j)` has `∑_k β^k g_{t+k} = 0` at every `t ≥ 1`
  set g : ℕ → ℝ := fun j => (b j - b' j) / B * Pss / P j with hg
  have hG : ∀ t, HasSum (fun k : ℕ => β ^ k * g (t + 1 + k)) 0 := by
    intro t
    have := (h t).sub (h' t)
    rw [sub_self] at this
    convert this using 1
    funext k
    simp only [hg]
    ring
  have hrec := (hasSum_nat_add_iff' 1).mpr (hG t)
  simp only [Finset.sum_range_one, pow_zero, one_mul, add_zero, zero_sub] at hrec
  have h2 : HasSum (fun k : ℕ => β ^ (k + 1) * g (t + 1 + (k + 1))) 0 := by
    have := (hG (t + 1)).mul_left β
    rw [mul_zero] at this
    convert this using 1
    funext k
    rw [pow_succ, show t + 1 + (k + 1) = t + 1 + 1 + k by omega]
    ring
  have hg0 : g (t + 1) = 0 := by
    have := hrec.unique h2
    linarith
  simp only [hg] at hg0
  have hPt' := (hPt (t + 1)).ne'
  rcases mul_eq_zero.mp (div_eq_zero_iff.mp hg0 |>.resolve_right hPt') with h0 | h0
  · rcases div_eq_zero_iff.mp h0 with h00 | h00
    · linarith
    · exact absurd h00 hB.ne'
  · exact absurd h0 hPss

/-- Cochrane (2023), §7.6.1, p. 230 (solving `∑_k β^k c_{t+k} = R_t` for `c`): if every tail
series `∑_k β^k R_{t+k}` converges, then `c_t = R_t − β R_{t+1}` solves it at every date. -/
theorem solve_tail {β : ℝ} {R : ℕ → ℝ} (hR : ∀ t, Summable (fun k : ℕ => β ^ k * R (t + k)))
    (t : ℕ) : HasSum (fun k : ℕ => β ^ k * (R (t + k) - β * R (t + k + 1))) (R t) := by
  have h1 := (hR t).hasSum
  have h2 := ((hR (t + 1)).hasSum).mul_left β
  have hsplit := (hR t).tsum_eq_zero_add
  simp only [pow_zero, one_mul, add_zero] at hsplit
  convert h1.sub h2 using 1
  · funext k
    rw [show t + 1 + k = t + k + 1 by omega]
    ring
  · have : ∑' k : ℕ, β ^ (k + 1) * R (t + (k + 1)) =
        β * ∑' k : ℕ, β ^ k * R (t + 1 + k) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
      ring
    rw [hsplit, this]
    ring

/-- Cochrane (2023), §7.6.1, p. 230: conversely, a solution of `∑_k β^k c_{t+k} = R_t` at every
date is unique, `c_t = R_t − β R_{t+1}`, and it exists only if `β^N R_{t+N} → 0`. -/
theorem solve_tail_necessary {β : ℝ} {R c : ℕ → ℝ}
    (hc : ∀ t, HasSum (fun k : ℕ => β ^ k * c (t + k)) (R t)) (t : ℕ) :
    c t = R t - β * R (t + 1) ∧ Tendsto (fun N : ℕ => β ^ N * R (t + N)) atTop (𝓝 0) := by
  have hrec : ∀ u, R u = c u + β * R (u + 1) := by
    intro u
    have h := (hasSum_nat_add_iff' 1).mpr (hc u)
    simp only [Finset.sum_range_one, pow_zero, one_mul, add_zero] at h
    have h2 := (hc (u + 1)).mul_left β
    have : (fun k : ℕ => β ^ (k + 1) * c (u + (k + 1))) =
        fun k : ℕ => β * (β ^ k * c (u + 1 + k)) := by
      funext k; rw [pow_succ, show u + (k + 1) = u + 1 + k by omega]; ring
    rw [this] at h
    have := h.unique h2
    linarith
  refine ⟨by linarith [hrec t], ?_⟩
  have hpart : ∀ N, ∑ k ∈ Finset.range N, β ^ k * c (t + k) = R t - β ^ N * R (t + N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hrec (t + N), pow_succ, show t + (N + 1) = t + N + 1 by
        omega]
      ring
  have hlim := (hc t).tendsto_sum_nat
  simp only [hpart] at hlim
  have := (tendsto_const_nhds (x := R t)).sub hlim
  simpa using this

/-- Cochrane (2023), §7.6.1, p. 230: the condition `β^N R_{t+N} → 0` cannot be dropped: for
`0 < β < 1` and `R_t = β^{−t}` no sequence `c` has `∑_k β^k c_{t+k} = R_t` at every date. -/
theorem solve_tail_counterexample {β : ℝ} (hβ0 : 0 < β) :
    ¬ ∃ c : ℕ → ℝ, ∀ t, HasSum (fun k : ℕ => β ^ k * c (t + k)) ((β ^ t)⁻¹) := by
  rintro ⟨c, hc⟩
  have h := (solve_tail_necessary (R := fun t => (β ^ t)⁻¹) hc 0).2
  have : (fun N : ℕ => β ^ N * (fun t => (β ^ t)⁻¹) (0 + N)) = fun _ => 1 := by
    funext N; simp [mul_inv_cancel₀ (pow_ne_zero N hβ0.ne')]
  rw [this] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Cochrane (2023), §7.6.1, p. 230: the residual that the QE purchases must finance in (7.23),
`R_t = 1/(1−βω) − M_{t−1}^{(t)} P/(B P_t) − ∑_k (βω)^k P/P_{t+k}` (`T t` is the Treasury series). -/
noncomputable def qeResidual (β ω B Pss : ℝ) (Mr P T : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 / (1 - β * ω) - Mr t * Pss / (B * P t) - T t

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering, existence): given the price path and
the reserves, if the tail series of the residual converge (e.g. the residual is bounded,
`qe_residual_summable`), the QE purchases
`B̃_0^{(j)} = B (R_j − β R_{j+1}) P_j / P` satisfy (7.23) at every date. -/
theorem qe_exists {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {Mr P T : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t)
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t))
    (hR : ∀ t, Summable (fun k : ℕ => β ^ k * qeResidual β ω B Pss Mr P T (t + k))) (t : ℕ) :
    Eq723 β ω B Pss (fun j => B * (qeResidual β ω B Pss Mr P T j -
      β * qeResidual β ω B Pss Mr P T (j + 1)) * P j / Pss) Mr P t := by
  unfold Eq723
  have h := (hT t).add (solve_tail hR t)
  convert h using 1
  · funext k
    have hPk := (hPt (t + k)).ne'
    field_simp
  · simp only [qeResidual]
    ring

/-- Cochrane (2023), §7.6.1, p. 230: a bounded residual has convergent tail series (`0 ≤ β < 1`),
so under the book's bounded paths the QE purchases exist. -/
theorem qe_residual_summable {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {R : ℕ → ℝ}
    (hK : ∀ t, |R t| ≤ K) (t : ℕ) : Summable (fun k : ℕ => β ^ k * R (t + k)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hK _) (pow_nonneg hβ0 k)

/-- Cochrane (2023), §7.6.1, p. 230: conversely, if QE purchases satisfying (7.23) at every date
exist, then `β^N R_{t+N} → 0`; with reserves making `R_t = β^{−t}` (possible for any price path,
`qe_counterexample`) no QE policy supports the path. -/
theorem qe_exists_necessary {β ω B Pss : ℝ} {b Mr P T : ℕ → ℝ}
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t))
    (hb : ∀ t, Eq723 β ω B Pss b Mr P t) (t : ℕ) :
    Tendsto (fun N : ℕ => β ^ N * qeResidual β ω B Pss Mr P T (t + N)) atTop (𝓝 0) := by
  refine (solve_tail_necessary (c := fun j => b j / B * Pss / P j) (fun u => ?_) t).2
  have := (hb u).sub (hT u)
  convert this using 1
  · funext k
    ring
  · simp only [qeResidual]

/-- Cochrane (2023), §7.6.1, p. 230: **existence can fail.** For `0 < β < 1` and any positive price
path, the reserves `M_{t−1}^{(t)} = (1/(1−βω) − T_t − β^{−t}) B P_t / P` allow no QE purchases
satisfying (7.23) at every date. -/
theorem qe_counterexample {β ω B Pss : ℝ} (hβ0 : 0 < β) (hB : 0 < B) (hP : 0 < Pss)
    {P T : ℕ → ℝ} (hPt : ∀ t, 0 < P t)
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t)) :
    ¬ ∃ b : ℕ → ℝ, ∀ t, Eq723 β ω B Pss b
      (fun t => (1 / (1 - β * ω) - T t - (β ^ t)⁻¹) * B * P t / Pss) P t := by
  rintro ⟨b, hb⟩
  have h := qe_exists_necessary hT hb 0
  have hres : ∀ N, qeResidual β ω B Pss
      (fun t => (1 / (1 - β * ω) - T t - (β ^ t)⁻¹) * B * P t / Pss) P T (0 + N) =
      (β ^ N)⁻¹ := by
    intro N
    simp only [qeResidual, zero_add]
    have := (hPt N).ne'
    field_simp
    ring
  simp only [hres] at h
  have : (fun N : ℕ => β ^ N * (β ^ N)⁻¹) = fun _ => 1 := by
    funext N; exact mul_inv_cancel₀ (pow_ne_zero N hβ0.ne')
  rw [this] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Cochrane (2023), eq. (7.24), p. 232: with perfect-foresight bond prices
`Q_t^{(j)} = β^{j−t} P_t/P_j`, the present-value relation reads
`(M_{t−1}^{(t)} + ∑_{j≥t}(Bω^{j−t} + B̃_0^{(j)}) Q_t^{(j)})/P_t = B/((1−βω)P)`. -/
theorem pv_iff_724 {β ω B s Pss : ℝ} (hss : B / (Pss * (1 - β * ω)) = s / (1 - β))
    {b Mr P : ℕ → ℝ} (hPt : ∀ t, 0 < P t) (t : ℕ) :
    QEPresentValue β ω B s b Mr P t ↔
      HasSum (fun k : ℕ => (ω ^ k * B + b (t + k)) * (β ^ k * P t / P (t + k)) / P t)
        (B / ((1 - β * ω) * Pss) - Mr t / P t) := by
  unfold QEPresentValue
  have hPt' := (hPt t).ne'
  have hfun : (fun k : ℕ => (ω ^ k * B + b (t + k)) * (β ^ k * P t / P (t + k)) / P t) =
      fun k : ℕ => β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k)) := by
    funext k
    field_simp
  rw [hfun, show B / ((1 - β * ω) * Pss) = s / (1 - β) by rw [← hss, mul_comm]]

/-! ### Maturity structure is irrelevant (§7.6.2) -/

namespace Irrelevance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.6.2, p. 232: **only the total market value of debt matters.** Two debt
policies with the same nominal market value `∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` at date `t` satisfy
the
present-value relation at `t` for exactly the same price levels. -/
theorem maturity_irrelevance (hpo : 𝔼.PullOut) {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hPx : ∀ t ω, P t ω * x t ω = 1) (t : ℕ)
    {N : Ω → ℝ} (hN : ∀ ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω * D t (t + j) ω) (N ω))
    (hN' : ∀ ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω * D' t (t + j) ω) (N ω)) :
    PresentValue 𝔼 β D x s t ↔ PresentValue 𝔼 β D' x s t := by
  have hreal : ∀ (E : ℕ → ℕ → Ω → ℝ) ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω *
      E t (t + j) ω) (N ω) → HasSum (fun j => debtTerm 𝔼 β E x t j ω) (x t ω * N ω) := by
    intro E ω h
    have := h.mul_left (x t ω)
    convert this using 1
    funext j
    rw [bondPrice_eq 𝔼 hpo hP, debtTerm]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    linear_combination (-(β ^ j * E t (t + j) ω * 𝔼.E t (x (t + j)) ω)) * hPx t ω
  constructor
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← ((hreal D ω (hN ω)).unique (h ω).2)]
    exact hreal D' ω (hN' ω)
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← ((hreal D' ω (hN' ω)).unique (h ω).2)]
    exact hreal D ω (hN ω)

end Irrelevance

/-- Cochrane (2023), p. 233 (strong QE): with `B_0^{(j)} = P_j s_j` and `Q_0^{(j)} = β^j P_0/P_j`
(`P_0` fixed), scaling the supply by `λ > 0` scales `P_j` by `λ` and `Q_0^{(j)}` by `1/λ`. So a 1%
decrease in supply (`λ = 0.99`) lowers `P_j` by 1% and *raises* the bond price by about 1%
(`1/0.99 − 1 ∈ (1.01%, 1.02%)`); the book's "decrease in bond price" has the wrong sign. -/
theorem strong_qe {β P0 sj B lam : ℝ} (j : ℕ) (hs : sj ≠ 0) (hB : B ≠ 0) (hl : lam ≠ 0) :
    lam * B / sj = lam * (B / sj) ∧
      β ^ j * P0 / (lam * B / sj) = (β ^ j * P0 / (B / sj)) / lam ∧
      (0.0101 : ℝ) < 1 / 0.99 - 1 ∧ (1 / 0.99 - 1 : ℝ) < 0.0102 := by
  refine ⟨by ring, ?_, by norm_num, by norm_num⟩
  field_simp

end Cochrane.LongTermDebtDynamics.QuantitativeEasing

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The weighted present value state by state

Cochrane (2023), §7.4, pp. 224–226, equations (7.14) and (7.17).

The weighted present value (7.17) `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` is built from the
*pathwise* weighted sum `Z_t = ∑_m β^m W_t^{(m)} s_{t+m}`, a series of real numbers at each state.
This module proves two facts used by the existence results of the later TidyR5 modules:

* `pathZ_solves`: state by state, `Z` solves the flow system (7.14) without expectations,
  `Z_t = s_t + ∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`, whenever the weights are absolutely summable
  along every row. This is the perfect-foresight content of (7.17), with no row or column
  condition beyond absolute summability.
* `formulaW_solves_of_exchange`: if `E_t` passes through the two series involved (the series
  for `Z_t` and the series on the right of (7.14)), then `y_t = E_t Z_t` is (7.17) and solves the
  flow system (7.14) under uncertainty.

`weight_apply` evaluates Cochrane's weights at a state, and `hasSum_E_of_dom` is the dominated
interchange of `E_t` and a series in `HasSum` form.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5Pathwise

open Filter Topology MaturityStructure GeneralFormula

/-- Cochrane (2023), §7.4, p. 226: the weights of random sale fractions, evaluated at a state, are
the weights of the sale fractions at that state. -/
theorem weight_apply {Ω : Type*} (A : ℕ → ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    ∀ t, weight A t m ω = weight (fun u v => A u v ω) t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [weight_zero]
    · rw [weight_succ, weight_succ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Pi.mul_apply, ih n (Finset.mem_range.mp hn) t]

/-- Cochrane (2023), eq. (7.17), p. 225: the pathwise weighted present value
`Z_t = ∑_m β^m W_t^{(m)} s_{t+m}` for deterministic sale fractions and surpluses. -/
noncomputable def pathZ (β : ℝ) (A : ℕ → ℕ → ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' m, β ^ m * (weight A t m * s (t + m))

/-- Cochrane (2023), eq. (7.17), p. 225: the pathwise weighted present value at each state,
`Z_t(ω) = ∑_m β^m W_t^{(m)}(ω) s_{t+m}(ω)`. -/
noncomputable def pathZΩ {Ω : Type*} (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  pathZ β (fun u v => A u v ω) (fun u => s u ω) t

/-- Cochrane (2023), eq. (7.17), p. 225: with `0 ≤ β`, `|s| ≤ M` and `∑_m β^m |W_t^{(m)}| ≤ C`,
the series for `Z_t` converges absolutely and `|Z_t| ≤ C M`. -/
theorem pathZ_summable_bound {β M C : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → ℝ} {s : ℕ → ℝ}
    (hsb : ∀ u, |s u| ≤ M) {t : ℕ} (hW : Summable (fun m => β ^ m * |weight A t m|))
    (hWC : ∑' m, β ^ m * |weight A t m| ≤ C) :
    Summable (fun m => |β ^ m * (weight A t m * s (t + m))|) ∧ |pathZ β A s t| ≤ C * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0)
  have hb : ∀ m, |β ^ m * (weight A t m * s (t + m))| ≤ β ^ m * |weight A t m| * M := by
    intro m
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsb _) (abs_nonneg _))
      (pow_nonneg hβ0 m)
  have hdom : Summable (fun m => β ^ m * |weight A t m| * M) := hW.mul_right M
  have hs : Summable (fun m => |β ^ m * (weight A t m * s (t + m))|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hb hdom
  refine ⟨hs, ?_⟩
  have h0 := norm_tsum_le_tsum_norm (f := fun m => β ^ m * (weight A t m * s (t + m)))
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at h0
  refine h0.trans ((Summable.tsum_le_tsum hb hs hdom).trans ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right hWC hM

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **the pathwise weighted present value
solves the flow system.** With `0 ≤ β`, bounded surpluses, weights absolutely summable along every
row (`∑_m β^m |W_u^{(m)}| ≤ C`) and an absolutely summable row `∑_j β^{j+1}|A_t^{(t+j+1)}|`,
`Z_t = s_t + ∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`. The proof regroups an absolutely convergent
double series by antidiagonals, using `GeneralFormula.weight_first_step`. -/
theorem pathZ_solves {β M C : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → ℝ} {s : ℕ → ℝ}
    (hsb : ∀ u, |s u| ≤ M) (hW : ∀ u, Summable (fun m => β ^ m * |weight A u m|))
    (hWC : ∀ u, ∑' m, β ^ m * |weight A u m| ≤ C) (t : ℕ)
    (hrow : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1))|)) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) * pathZ β A s (t + (j + 1))))
      (pathZ β A s t - s t) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0)
  have hC : 0 ≤ C := (tsum_nonneg fun m => mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)).trans
    (hWC 0)
  set Gf : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * (A t (t + (p.1 + 1)) *
    (β ^ p.2 * (weight A (t + (p.1 + 1)) p.2 * s (t + (p.1 + 1) + p.2)))) with hGf
  set g : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * |A t (t + (p.1 + 1))| *
    (β ^ p.2 * |weight A (t + (p.1 + 1)) p.2| * M) with hg
  have hg0 : 0 ≤ g := fun p => mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
    (mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)) hM)
  have hGb : ∀ p, ‖Gf p‖ ≤ g p := by
    intro p
    rw [Real.norm_eq_abs, hGf, hg]
    simp only [abs_mul, abs_pow, abs_of_nonneg hβ0]
    have h1 : |s (t + (p.1 + 1) + p.2)| ≤ M := hsb _
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (pow_nonneg hβ0 (p.1 + 1))
      (abs_nonneg (A t (t + (p.1 + 1))))) (mul_nonneg (pow_nonneg hβ0 p.2)
        (abs_nonneg (weight A (t + (p.1 + 1)) p.2))))
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring
  have hgsum : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hg]
      exact ((hW (t + (j + 1))).mul_right M).mul_left (β ^ (j + 1) * |A t (t + (j + 1))|)
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => hg0 (j, m)) (fun j => ?_)
      (hrow.mul_right (C * M))
    simp only [hg]
    rw [tsum_mul_left, tsum_mul_right]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hWC _) hM)
      (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
  have hGsum : Summable Gf := Summable.of_norm_bounded hgsum hGb
  -- (i) the fibres
  have hfib : ∀ j, HasSum (fun m => Gf (j, m))
      (β ^ (j + 1) * (A t (t + (j + 1)) * pathZ β A s (t + (j + 1)))) := by
    intro j
    have hin := (pathZ_summable_bound hβ0 hsb (hW (t + (j + 1))) (hWC _)).1
    exact ((hin.of_abs).hasSum.mul_left (A t (t + (j + 1)))).mul_left (β ^ (j + 1))
  have hrowsum := hGsum.hasSum.prod_fiberwise hfib
  -- (ii) the antidiagonals
  have hdiag : HasSum (fun k => β ^ (k + 1) * (weight A t (k + 1) * s (t + (k + 1))))
      (∑' p, Gf p) := by
    have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := Gf)).mpr
      hGsum.hasSum
    have h2 := h1.sigma (fun k => hasSum_fintype _)
    convert h2 using 1
    funext k
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal k) Gf,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, weight_first_step, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hGf]
    rw [show t + (j + 1) + (k - j) = t + (k + 1) by omega,
      show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
    ring
  -- (iii) the value at `t`
  have hzs := (pathZ_summable_bound hβ0 hsb (hW t) (hWC t)).1.of_abs
  have hz : pathZ β A s t = s t + ∑' p, Gf p := by
    rw [pathZ, hzs.tsum_eq_zero_add, hdiag.tsum_eq]
    simp [weight_zero]
  rw [hz, add_sub_cancel_left]
  exact hrowsum

/-- Cochrane (2023), §7.4 (used for (7.17)): `E_t` passes through a series of random variables
dominated by a summable sequence, in `HasSum` form. -/
theorem hasSum_E_of_dom {Ω : Type*} (𝔼 : ExpectationSystem Ω) {u : ℕ → ℝ} (hu : Summable u)
    {f : ℕ → Ω → ℝ} (hf : ∀ k ω, |f k ω| ≤ u k) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω) := by
  rw [ForwardSolution.E_tsum_dom 𝔼 hu hf t ω]
  exact (Summable.of_norm_bounded hu (fun k => by
    rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)).hasSum

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.17), p. 225: if `E_t` passes through the series for `Z_t`, the
weighted present value (7.17) is `E_t Z_t`. -/
theorem formulaW_eq_E {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {s Z : ℕ → Ω → ℝ}
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω)) (t : ℕ) :
    formulaW 𝔼 β A s t = 𝔼.E t (Z t) :=
  funext fun ω => (hex1 t ω).tsum_eq

/-- Cochrane (2023), eq. (7.17), p. 225: if `E_t` passes through the series for `Z_t`, the
weighted present value (7.17) is known at `t`. -/
theorem formulaW_adapted_of_exchange {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {s Z : ℕ → Ω → ℝ}
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω)) (t : ℕ) :
    𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  rw [formulaW_eq_E 𝔼 hex1, 𝔼.E_E_self]

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **(7.17) solves the flow system, given the
two interchanges.** Let `Z` solve the flow system state by state, each sale fraction
`A_t^{(t+j+1)}` be known at `t + j`, surpluses be adapted, and suppose `E_t` passes through the
series for `Z_t` (hypothesis hex1) and through the series `∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`
(hypothesis hex2).
Then `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` satisfies (7.14) at `t`, under uncertainty. -/
theorem formulaW_solves_of_exchange (hpo : 𝔼.PullOut) {β : ℝ} {A : ℕ → ℕ → Ω → ℝ}
    {s Z : ℕ → Ω → ℝ} (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    (hs : 𝔼.Adapted s)
    (hpw : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω * Z (t + (j + 1)) ω))
      (Z t ω - s t ω))
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω))
    (hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω))
    (t : ℕ) : MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t := by
  intro ω
  have hfw := formulaW_eq_E 𝔼 hex1
  have hterm : ∀ j, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1))) ω =
      𝔼.E t (fun ω' => β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω := by
    intro j
    have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
      ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
    rw [hfw, ← hpo _ _ _ hAk, 𝔼.tower (by omega),
      show (fun ω' => β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) =
        β ^ (j + 1) • (A t (t + (j + 1)) * Z (t + (j + 1))) from rfl, map_smul]
    rfl
  have hsum : (fun ω' => ∑' j : ℕ, β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) =
      Z t - s t := funext fun ω' => (hpw t ω').tsum_eq
  have h := hex2 t ω
  rw [hsum, map_sub, hs t] at h
  simp only [hterm]
  rw [hfw t]
  exact h

end Cochrane.LongTermDebtDynamics.TidyR5Pathwise

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of a positive equilibrium without buy-backs

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17), with the flow and present-value
relations (7.1), (7.2), (7.5) of pp. 213 and 216.

`GeneralFormula.price_unique_noBuyback` shows that without buy-backs at most one positive price
path satisfies every flow and present-value relation. This module settles existence.

* `weight_mem_unit`: without buy-backs every weight `W_t^{(m)}` of (7.17) lies in `[0, 1]`, because
  each column of sale fractions sums to at most one. So (7.17) converges absolutely for bounded
  surpluses whatever the rows of the sale fractions look like.
* `formulaW_solves_noBuyback`: without buy-backs, (7.17) solves the flow system (7.14) for every
  expectation system with the pull-out property (no row condition).
* `equilibrium_of_formulaW_pos`, `maturing_eq_formulaW`, `exists_equilibrium_iff`: **the
  exact condition.** Without buy-backs, a positive equilibrium price path exists if and only if
  the weighted present value (7.17) is strictly positive at every date and state; it is then
  `1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`, and it is unique.
* `existsUnique_of_pos_surplus`: positive bounded surpluses suffice.
* `cb_*`: **no buy-backs alone do not give existence.** With debt of every maturity, no trading,
  and surpluses `s_0 = −1`, `s_t = 1` for `t ≥ 1`, there is no positive price level at date 0,
  although the present value of surpluses at date 0 is positive for `β > 1/2`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise

/-- Cochrane (2023), §7.4, p. 226: with nonnegative sale fractions whose columns sum to at most
one, every weight `W_t^{(m)}` lies in `[0, 1]`. -/
theorem weight_mem_unit {A : ℕ → ℕ → ℝ} (hA0 : ∀ t m, t < m → 0 ≤ A t m)
    (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) (m : ℕ) :
    ∀ t, 0 ≤ weight A t m ∧ weight A t m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [weight_zero]
    · rw [weight_succ]
      constructor
      · exact Finset.sum_nonneg fun n hn =>
          mul_nonneg (hA0 _ _ (by have := Finset.mem_range.mp hn; omega))
            (ih n (Finset.mem_range.mp hn) t).1
      · have h1 : ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) * weight A t n ≤
            ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) :=
          Finset.sum_le_sum fun n hn => mul_le_of_le_one_right
            (hA0 _ _ (by have := Finset.mem_range.mp hn; omega))
            (ih n (Finset.mem_range.mp hn) t).2
        have h2 : ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) =
            ∑ u ∈ Finset.Ico t (t + (k + 1)), A u (t + (k + 1)) := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        have h3 : ∑ u ∈ Finset.Ico t (t + (k + 1)), A u (t + (k + 1)) ≤
            ∑ u ∈ Finset.range (t + (k + 1)), A u (t + (k + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun u hu => Finset.mem_range.mpr (Finset.mem_Ico.mp hu).2)
            fun u hu _ => hA0 _ _ (Finset.mem_range.mp hu)
        linarith [hcolA (t + (k + 1))]

/-- Cochrane (2023), §7.4: with nonnegative sale fractions whose columns sum to at most one, each
fraction `A_t^{(m)}` (`t < m`) lies in `[0, 1]`. -/
theorem frac_le_one {A : ℕ → ℕ → ℝ} (hA0 : ∀ t m, t < m → 0 ≤ A t m)
    (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) {t m : ℕ} (htm : t < m) : A t m ≤ 1 :=
  (Finset.single_le_sum (fun i hi => hA0 i m (Finset.mem_range.mp hi))
    (Finset.mem_range.mpr htm)).trans (hcolA m)

/-- Cochrane (2023), eq. (7.17), p. 226: with weights in `[0, 1]` and `0 ≤ β < 1`,
`∑_m β^m |W_t^{(m)}|` converges with sum at most `1/(1−β)`. -/
theorem weight_series_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {A : ℕ → ℕ → ℝ}
    (hA0 : ∀ t m, t < m → 0 ≤ A t m) (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) (u : ℕ) :
    Summable (fun m => β ^ m * |weight A u m|) ∧
      ∑' m, β ^ m * |weight A u m| ≤ 1 / (1 - β) := by
  have hb : ∀ m, β ^ m * |weight A u m| ≤ β ^ m := fun m => by
    have h := weight_mem_unit hA0 hcolA m u
    rw [abs_of_nonneg h.1]
    exact mul_le_of_le_one_right (pow_nonneg hβ0 m) h.2
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hs : Summable (fun m => β ^ m * |weight A u m|) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)) hb hg
  refine ⟨hs, (Summable.tsum_le_tsum hb hs hg).trans ?_⟩
  rw [tsum_geometric_of_lt_one hβ0 hβ1, one_div]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: without buy-backs the pathwise weighted
present value `Z` solves the flow system state by state, and `|Z_t| ≤ M/(1−β)`. -/
theorem pathZΩ_noBuyback {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {A : ℕ → ℕ → Ω → ℝ}
    (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω) (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1)
    {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω *
      pathZΩ β A s (t + (j + 1)) ω)) (pathZΩ β A s t ω - s t ω)) ∧
      ∀ t ω, |pathZΩ β A s t ω| ≤ M / (1 - β) := by
  have hW := fun ω => weight_series_le hβ0 hβ1 (A := fun u v => A u v ω)
    (fun t m h => hA0 t m ω h) (fun m => hcolA m ω)
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · have hrow : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
        (fun j => ?_) ((summable_geometric_of_lt_one hβ0 hβ1).comp_injective
          (add_left_injective 1))
      rw [abs_of_nonneg (hA0 _ _ ω (by omega))]
      exact mul_le_of_le_one_right (pow_nonneg hβ0 _) (frac_le_one (A := fun u v => A u v ω)
        (fun t m h => hA0 t m ω h) (fun m => hcolA m ω) (by omega))
    exact pathZ_solves hβ0 (fun u => hsb u ω) (fun u => (hW ω u).1) (fun u => (hW ω u).2) t hrow
  · have := (pathZ_summable_bound hβ0 (fun u => hsb u ω) (hW ω t).1 (hW ω t).2).2
    rw [one_div_mul_eq_div] at this
    exact this

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **without buy-backs, (7.17) solves the
flow system**, with no row condition. Nonnegative sale fractions with column sums at most one,
each `A_t^{(t+j+1)}` known at `t + j`, bounded adapted surpluses, `0 ≤ β < 1`: then
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` (an absolutely convergent series with `|y_t| ≤ M/(1−β)`)
satisfies every flow condition (7.14), under uncertainty, and is known at `t`. -/
theorem formulaW_solves_noBuyback (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {A : ℕ → ℕ → Ω → ℝ} (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω)
    (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - β)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  obtain ⟨hpw, hZb⟩ := pathZΩ_noBuyback hβ0 hβ1 hA0 hcolA hsb
  have hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω)
      (𝔼.E t (pathZΩ β A s t) ω) := by
    intro t ω
    have hf : ∀ m ω', |β ^ m * (weight A t m ω' * s (t + m) ω')| ≤ β ^ m * M := by
      intro m ω'
      have h := weight_mem_unit (A := fun u v => A u v ω') (fun t m h => hA0 t m ω' h)
        (fun m => hcolA m ω') m t
      rw [← weight_apply] at h
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, abs_of_nonneg h.1]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (abs_nonneg _) h.2).trans
        (hsb _ ω')) (pow_nonneg hβ0 m)
    have h := hasSum_E_of_dom 𝔼 ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M) hf t ω
    have hZ : (fun ω' => ∑' m, β ^ m * (weight A t m ω' * s (t + m) ω')) = pathZΩ β A s t := by
      funext ω'
      simp only [pathZΩ, pathZ, weight_apply]
    rw [hZ] at h
    refine h.congr_fun fun m => ?_
    rw [formulaTerm, show (fun ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) =
      β ^ m • (weight A t m * s (t + m)) from rfl, map_smul]
    rfl
  have hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) *
        (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω) := by
    intro t ω
    refine hasSum_E_of_dom 𝔼 (((summable_geometric_of_lt_one hβ0 hβ1).comp_injective
      (add_left_injective 1)).mul_right (M / (1 - β))) (fun j ω' => ?_) t ω
    have hA1 : |A t (t + (j + 1)) ω'| ≤ 1 := by
      rw [abs_of_nonneg (hA0 _ _ ω' (by omega))]
      exact frac_le_one (A := fun u v => A u v ω') (fun t m h => hA0 t m ω' h)
        (fun m => hcolA m ω') (by omega)
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0]
    simp only [Function.comp_apply]
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (abs_nonneg _) hA1).trans
      (hZb _ ω')) (pow_nonneg hβ0 _)
  have hfw := formulaW_eq_E 𝔼 hex1
  refine ⟨formulaW_solves_of_exchange 𝔼 hpo hA hs hpw hex1 hex2, fun t ω => ?_,
    fun t ω => ?_, formulaW_adapted_of_exchange 𝔼 hex1⟩
  · rw [hfw t]; exact hex1 t ω
  · rw [hfw t]; exact 𝔼.abs_E_le (hZb t) t ω

/-! ### Positive equilibria without buy-backs -/

/-- Cochrane (2023), §7.4: without buy-backs, debt due at `m` outstanding at `t ≤ m` is at most the
debt coming due at `m`, `B_{t−1}^{(m)} ≤ B_{m−1}^{(m)}`. -/
theorem noBuyback_le_maturing {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (ω : Ω) (m : ℕ) :
    ∀ k t, t + k = m → D t m ω ≤ D m m ω := by
  intro k
  induction k with
  | zero => intro t htm; rw [← htm, add_zero]
  | succ k ih =>
    intro t htm
    exact (h.2.1 t m ω (by omega)).trans (ih (t + 1) (by omega))

/-- Cochrane (2023), §7.4, p. 225: with predetermined debt and quotients of known variables known,
the sale fraction `A_t^{(t+j+1)}` is known at `t + j`, the date of the last sale before maturity. -/
theorem fracSold_known (hdc : PolicyConstraints.DivClosed 𝔼) {D : ℕ → ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (t j : ℕ) :
    𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)) := by
  unfold fracSold
  apply hdc
  · rw [map_sub, Predetermined.known_succ 𝔼 hD (by omega), Predetermined.known 𝔼 hD (by omega)]
  · have := hD.2 (t + j) (t + (j + 1))
    rwa [show t + j + 1 = t + (j + 1) by omega] at this

/-- Cochrane (2023), eq. (7.17), p. 225: the candidate equilibrium,
`1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`. -/
noncomputable def eqX (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  formulaW 𝔼 β (fracSold D) s t / D t t

/-- Cochrane (2023), §7.4 and eq. (7.17), pp. 225–226: **sufficiency.** Without buy-backs
(`GeneralFormula.NoBuyback`), with predetermined debt, quotients of known variables known,
`0 < β < 1` and bounded adapted surpluses, if the weighted present value (7.17) is strictly
positive at every date and state, then `1/P_t = eqX` is a positive equilibrium: adapted, positive,
satisfying every flow condition (7.1) and every present-value relation (7.2)/(7.5). -/
theorem equilibrium_of_formulaW_pos (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hpos : ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω) :
    𝔼.Adapted (eqX 𝔼 β D s) ∧ (∀ t ω, 0 < eqX 𝔼 β D s t ω) ∧
      (∀ t, RealFlow 𝔼 β D (eqX 𝔼 β D s) s t) ∧ ∀ t, PresentValue 𝔼 β D (eqX 𝔼 β D s) s t := by
  obtain ⟨hsys, -, hzb, hzad⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  set x := eqX 𝔼 β D s with hxdef
  have hx : 𝔼.Adapted x := fun t => hdc t _ _ (hzad t) (Predetermined.known 𝔼 hD le_rfl t)
  have hy : (fun u => D u u * x u) = formulaW 𝔼 β (fracSold D) s := by
    funext u ω
    simp only [hxdef, eqX, Pi.mul_apply, Pi.div_apply]
    field_simp [hDmm u ω]
  have hflow : ∀ t, RealFlow 𝔼 β D x s t := fun t =>
    (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mpr (by rw [hy]; exact hsys t)
  have hcore : ∀ t j ω, |D t (t + j) ω * 𝔼.E t (x (t + j)) ω| ≤ M / (1 - β) := by
    intro t j ω
    have hpull := congrFun (hpo t _ (x (t + j)) (Predetermined.known 𝔼 hD le_rfl (t + j))) ω
    simp only [Pi.mul_apply] at hpull
    rw [← hpull]
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hr0 : 0 ≤ D t (t + j) ω' := hnb.nonneg t (t + j) (by omega) ω'
    have hr1 : D t (t + j) ω' ≤ D (t + j) (t + j) ω' :=
      noBuyback_le_maturing hnb ω' (t + j) j t rfl
    have hpos' := hnb.2.2 (t + j) ω'
    simp only [Pi.mul_apply, hxdef, eqX, Pi.div_apply]
    rw [show D t (t + j) ω' * (formulaW 𝔼 β (fracSold D) s (t + j) ω' / D (t + j) (t + j) ω') =
      D t (t + j) ω' / D (t + j) (t + j) ω' * formulaW 𝔼 β (fracSold D) s (t + j) ω' by ring,
      abs_mul, abs_of_nonneg (div_nonneg hr0 hpos'.le)]
    exact mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hpos').mpr hr1) |>.trans (hzb _ ω')
  have hdt : ∀ t j ω, |debtTerm 𝔼 β D x t j ω| ≤ β ^ j * (M / (1 - β)) := by
    intro t j ω
    rw [debtTerm, abs_mul, abs_pow, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (hcore t j ω) (pow_nonneg hβ0.le j)
  have hgeo : Summable (fun j : ℕ => β ^ j * (M / (1 - β))) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right _
  have hdom : ∀ t, DebtDominated 𝔼 β D x t := fun t => ⟨_, hgeo, hdt t⟩
  have hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω) := fun t ω =>
    Summable.of_norm_bounded hgeo (fun j => by rw [Real.norm_eq_abs]; exact hdt t j ω)
  have hV : ∀ t ω, |debtValue 𝔼 β D x t ω| ≤ ∑' j : ℕ, β ^ j * (M / (1 - β)) := by
    intro t ω
    have h0 := norm_tsum_le_tsum_norm (f := fun j => debtTerm 𝔼 β D x t j ω)
      (by simpa only [Real.norm_eq_abs] using (hsumm t ω).abs)
    simp only [Real.norm_eq_abs] at h0
    exact h0.trans (Summable.tsum_le_tsum (fun j => hdt t j ω) (hsumm t ω).abs hgeo)
  refine ⟨hx, fun t ω => div_pos (hpos t ω) (hnb.2.2 t ω), hflow, fun t => ?_⟩
  exact presentValue_of_bounded 𝔼 hpo hβ0.le hβ1 hD hx hs hsb hsumm hdom hflow hV t

/-- Cochrane (2023), §7.4 and eq. (7.17), pp. 225–226: **necessity.** Without buy-backs, in every
equilibrium with nonnegative `1/P` (adapted, every flow and present-value relation), the real
value of maturing debt is the weighted present value: `B_{t−1}^{(t)}/P_t =
E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem maturing_eq_formulaW (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hx : 𝔼.Adapted x) (hx0 : ∀ t ω, 0 ≤ x t ω) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hpv : ∀ t, PresentValue 𝔼 β D x s t) (t : ℕ) (ω : Ω) :
    D t t ω * x t ω = formulaW 𝔼 β (fracSold D) s t ω := by
  obtain ⟨hsys, -, hzb, -⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  have hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω := fun t j ω => hnb.nonneg t (t + j) (by omega) ω
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hb : ∀ t ω, |D t t ω * x t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx hx0 hD0 hsb (hpv t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hzero := unique_of_noBuyback 𝔼 hβ0 hβ1 (A := fracSold D)
    (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (homogeneous_of_two 𝔼 hy hsys) (K := M / (1 - β) + M / (1 - β))
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hzb t ω)))
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §7.4, pp. 225–226: **the exact condition for existence without buy-backs.**
Without buy-backs, with predetermined debt, quotients of known variables known, `0 < β < 1` and
bounded adapted surpluses, a positive equilibrium price path exists if and only if the weighted
present value (7.17) is strictly positive at every date and state. -/
theorem exists_equilibrium_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∃ x : ℕ → Ω → ℝ, 𝔼.Adapted x ∧ (∀ t ω, 0 < x t ω) ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
      ∀ t, PresentValue 𝔼 β D x s t) ↔ ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω := by
  constructor
  · rintro ⟨x, hx, hxpos, hflow, hpv⟩ t ω
    rw [← maturing_eq_formulaW 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hx (fun t ω => (hxpos t ω).le)
      hflow hpv t ω]
    exact mul_pos (hnb.2.2 t ω) (hxpos t ω)
  · intro hpos
    exact ⟨eqX 𝔼 β D s, equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hpos⟩

/-- Cochrane (2023), eq. (7.17), p. 225: with weights in `[0, 1]` and nonnegative surpluses,
(7.17) is at least the current surplus, `E_t ∑_m β^m W_t^{(m)} s_{t+m} ≥ s_t`. -/
theorem formulaW_ge_surplus (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hs0 : ∀ t ω, 0 ≤ s t ω) (t : ℕ) (ω : Ω) : s t ω ≤ formulaW 𝔼 β (fracSold D) s t ω := by
  obtain ⟨-, hsum, -, -⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have h0 : formulaTerm 𝔼 β (fracSold D) s t 0 ω = s t ω := by
    simp [formulaTerm, weight_zero, hs t]
  rw [← h0]
  refine le_hasSum (hsum t ω) 0 fun m _ => ?_
  rw [formulaTerm]
  refine mul_nonneg (pow_nonneg hβ0.le m) ?_
  have hnn : (fun _ => (0 : ℝ)) ≤ weight (fracSold D) t m * s (t + m) := fun ω' => by
    have h := weight_mem_unit (A := fun u v => fracSold D u v ω')
      (fun t m h => hnb.frac_nonneg t m ω' h) (fun m => hnb.col_le_one m ω') m t
    rw [← weight_apply] at h
    exact mul_nonneg h.1 (hs0 _ ω')
  have := 𝔼.mono t hnn ω
  rwa [𝔼.const] at this

/-- Cochrane (2023), §7.4, pp. 225–226: **positive surpluses suffice.** Without buy-backs, with
predetermined debt, quotients of known variables known, `0 < β < 1` and bounded adapted strictly
positive surpluses, there is exactly one positive equilibrium price path (every flow and
present-value relation), and it is `1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`. -/
theorem existsUnique_of_pos_surplus (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hspos : ∀ t ω, 0 < s t ω) :
    ∃! x : ℕ → Ω → ℝ, 𝔼.Adapted x ∧ (∀ t ω, 0 < x t ω) ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
      ∀ t, PresentValue 𝔼 β D x s t := by
  have hpos : ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω := fun t ω =>
    (hspos t ω).trans_le (formulaW_ge_surplus 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb
      (fun t ω => (hspos t ω).le) t ω)
  refine ⟨eqX 𝔼 β D s, equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hpos, ?_⟩
  rintro x' ⟨hx', hxpos', hflow', hpv'⟩
  obtain ⟨hx, hxpos, hflow, hpv⟩ := equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb
    hpos
  exact price_unique_noBuyback 𝔼 hpo hβ0 hβ1 hD hnb hx' hx (fun t ω => (hxpos' t ω).le)
    (fun t ω => (hxpos t ω).le) hsb hflow' hflow hpv' hpv

/-! ### No buy-backs alone do not give existence -/

/-- Cochrane (2023), §7.4 (counterexample to existence): one unit of debt due at every date, never
traded, `B_{t−1}^{(m)} = 1`. -/
def cbD : ℕ → ℕ → Unit → ℝ := fun _ _ _ => 1

/-- Cochrane (2023), §7.4 (counterexample to existence): a deficit at date 0 and surpluses after,
`s_0 = −1`, `s_t = 1` for `t ≥ 1`. -/
noncomputable def cbS : ℕ → Unit → ℝ := fun t _ => if t = 0 then -1 else 1

/-- Cochrane (2023), §7.4: the counterexample never buys back debt. -/
theorem cb_noBuyback : NoBuyback cbD :=
  ⟨fun _ _ => zero_le_one, fun _ _ _ _ => le_rfl, fun _ _ => one_pos⟩

/-- Cochrane (2023), §7.4: the counterexample's debt is predetermined (perfect foresight). -/
theorem cb_predetermined : Predetermined perfectForesight cbD := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Cochrane (2023), §7.4: the counterexample's surpluses are bounded, `|s_t| ≤ 1`. -/
theorem cb_bounded (t : ℕ) (u : Unit) : |cbS t u| ≤ 1 := by
  unfold cbS; split_ifs <;> simp

/-- Cochrane (2023), §7.4 (E7.4, existence): **no buy-backs alone do not give a positive
equilibrium.** In the counterexample no positive price level satisfies even the date-0 flow
condition (7.1), whatever `β`: with no sales it reads `B_{−1}^{(0)}/P_0 = s_0 = −1`. -/
theorem cb_no_positive_price (β : ℝ) :
    ¬ ∃ x : ℕ → Unit → ℝ, (∀ t u, 0 < x t u) ∧ RealFlow perfectForesight β cbD x cbS 0 := by
  rintro ⟨x, hx, hflow⟩
  have h := hflow ()
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales cbD 0 (0 + (j + 1)) () *
      perfectForesight.E 0 (x (0 + (j + 1))) ())) = fun _ => 0 := by
    funext j; simp [sales, cbD]
  rw [hz] at h
  have := h.unique hasSum_zero
  simp only [cbD, cbS, one_mul, ↓reduceIte] at this
  linarith [hx 0 ()]

/-- Cochrane (2023), §7.4 (E7.4, existence): in the counterexample the present value of surpluses
at date 0 is `(2β − 1)/(1 − β)`, positive for `1/2 < β < 1`: a positive present value of surpluses
does not rescue existence. -/
theorem cb_pv_pos {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    HasSum (fun k => surplusTerm perfectForesight β cbS 0 k ()) ((2 * β - 1) / (1 - β)) ∧
      0 < (2 * β - 1) / (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hg := hasSum_geometric_of_lt_one hβ0 hβ1
  have h2 : HasSum (fun k : ℕ => (Pi.single 0 (2 : ℝ) : ℕ → ℝ) k) 2 := hasSum_pi_single 0 2
  refine ⟨?_, div_pos (by linarith) (by linarith)⟩
  have h := hg.sub h2
  have hval : (1 - β)⁻¹ - 2 = (2 * β - 1) / (1 - β) := by
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  rcases k with _ | k
  · simp [surplusTerm, perfectForesight, cbS]; norm_num
  · simp [surplusTerm, perfectForesight, cbS]

end Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem W with random bounds on the sale fractions

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17).

`GeneralFormula.RowBound` bounds the sale fractions by a deterministic, date-independent sequence,
`|A_t^{(t+j+1)}| ≤ a_j` with `∑_j β^{j+1} a_j ≤ ρ < 1`. This module replaces it by the row
condition state by state and date by date,
`∑_j β^{j+1} |A_t^{(t+j+1)}(ω)| ≤ ρ < 1` for every `t` and `ω` (`RowBoundR`), which is implied by
any random bounds `a_{t,j}(ω)` (adapted or not) with `∑_j β^{j+1} a_{t,j}(ω) ≤ ρ`
(`rowBoundR_of_randomBound`), and so by the deterministic row condition
(`randomBound_of_rowBound`). It is strictly weaker than the deterministic condition even under
perfect foresight (`sx_rowBoundR`, `sx_not_rowBound`).

* `unique_of_rowR`: bounded solutions of the homogeneous system vanish, for every expectation
  system.
* `exists_bounded_solution`: the flow system (7.14) has a bounded solution, for every
  expectation system, by a contraction argument (`iterY`, `opK`); with `unique_of_rowR` it is
  the unique bounded solution (`existsUnique_bounded_solution`).
* `theoremW_rowR`: **Theorem W with random bounds.** If in addition `E_t` passes through
  absolutely convergent series (`SeriesExchange`, true for perfect foresight and every finite
  event tree: `perfectForesight_seriesExchange`, `finiteTree_seriesExchange`), the bounded
  solution is the weighted present value (7.17), an absolutely convergent series.

Why `SeriesExchange` appears here: with deterministic bounds the series in (7.17) are dominated
uniformly in the state, and `ForwardSolution.E_tsum_dom` interchanges `E_t` and the sum; with
random bounds the domination is state by state only. Uniqueness and existence do not need the
interchange; only the formula does. The hypothesis is in fact a theorem of the axioms (module
TidyR5SeriesExchange, `TidyR5SeriesExchange.seriesExchange`), because `E_t` is monotone and
linear on all random variables, unbounded ones included.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomRow

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise

/-! ### The weights under a row-by-row bound -/

/-- Cochrane (2023), eq. (7.17), p. 226: if every row of (deterministic) sale fractions satisfies
`∑_{j<N} β^{j+1}|A_t^{(t+j+1)}| ≤ ρ`, the partial sums of `β^m |W_u^{(m)}|` are at most
`∑_{n<N} ρ^n`, for every start date `u`. -/
theorem sum_abs_weight_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ0 : 0 ≤ ρ) {A : ℕ → ℕ → ℝ}
    (hrow : ∀ t N, ∑ j ∈ Finset.range N, β ^ (j + 1) * |A t (t + (j + 1))| ≤ ρ) (N : ℕ) :
    ∀ u, ∑ m ∈ Finset.range N, β ^ m * |weight A u m| ≤ ∑ n ∈ Finset.range N, ρ ^ n := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, weight_zero, abs_one, mul_one]
      have hk : ∀ k, β ^ (k + 1) * |weight A u (k + 1)| ≤
          ∑ j ∈ Finset.range (k + 1), β ^ (j + 1) * |A u (u + (j + 1))| *
            (β ^ (k - j) * |weight A (u + (j + 1)) (k - j)|) := by
        intro k
        rw [weight_first_step]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (pow_nonneg hβ0 _)).trans (le_of_eq ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [abs_mul, show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by
          rw [← pow_add]; congr 1; omega]
        ring
      have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) => hk k
      rw [← sum_triangle N (fun j m => β ^ (j + 1) * |A u (u + (j + 1))| *
        (β ^ m * |weight A (u + (j + 1)) m|))] at hsumk
      have hstep : ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range (N - j),
          β ^ (j + 1) * |A u (u + (j + 1))| * (β ^ m * |weight A (u + (j + 1)) m|) ≤
          ∑ j ∈ Finset.range N, β ^ (j + 1) * |A u (u + (j + 1))| *
            ∑ n ∈ Finset.range N, ρ ^ n := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ((ih (N - j) (by omega) _).trans ?_)
          (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N j))
          fun n _ _ => pow_nonneg hρ0 n
      rw [← Finset.sum_mul] at hstep
      have hgeo : 0 ≤ ∑ n ∈ Finset.range N, ρ ^ n := Finset.sum_nonneg fun n _ => pow_nonneg hρ0 n
      have h2 := mul_le_mul_of_nonneg_right (hrow u N) hgeo
      have h3 : ∑ i ∈ Finset.range N, ρ ^ (i + 1) = ρ * ∑ n ∈ Finset.range N, ρ ^ n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_succ' ρ i
      rw [h3]
      linarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.17), p. 225: **the row condition with random bounds**: at every date
and state, `∑_j β^{j+1} |A_t^{(t+j+1)}(ω)| ≤ ρ` (a convergent series). -/
def RowBoundR (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (ρ : ℝ) : Prop :=
  ∀ t ω, Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) ∧
    ∑' j : ℕ, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 225: random bounds `|A_t^{(t+j+1)}(ω)| ≤ a_{t,j}(ω)` with
`∑_j β^{j+1} a_{t,j}(ω) ≤ ρ` at every date and state. -/
def RandomBound (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → Ω → ℝ) (ρ : ℝ) : Prop :=
  (∀ t j ω, |A t (t + (j + 1)) ω| ≤ a t j ω) ∧
    ∀ t ω, Summable (fun j : ℕ => β ^ (j + 1) * a t j ω) ∧ ∑' j : ℕ, β ^ (j + 1) * a t j ω ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 225: random bounds imply the row condition `RowBoundR`. -/
theorem rowBoundR_of_randomBound {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℕ → Ω → ℝ} (h : RandomBound β A a ρ) : RowBoundR β A ρ := by
  intro t ω
  have hle : ∀ j : ℕ, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ β ^ (j + 1) * a t j ω := fun j =>
    mul_le_mul_of_nonneg_left (h.1 t j ω) (pow_nonneg hβ0 _)
  have hs : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)) hle
      (h.2 t ω).1
  exact ⟨hs, (Summable.tsum_le_tsum hle hs (h.2 t ω).1).trans (h.2 t ω).2⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the deterministic row condition
`GeneralFormula.RowBound` is the special case of constant bounds `a_{t,j}(ω) = a_j`. -/
theorem randomBound_of_rowBound {β ρ : ℝ} {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (h : RowBound β A a ρ) : RandomBound β A (fun _ j _ => a j) ρ :=
  ⟨h.2.1, fun _ _ => ⟨h.2.2.1, h.2.2.2⟩⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the partial sums of each row are at most `ρ`. -/
theorem RowBoundR.partial {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (t : ℕ) (ω : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range N, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ ρ :=
  ((h t ω).1.sum_le_tsum _ fun _ _ => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)).trans
    (h t ω).2

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition `ρ ≥ 0` (given any state). -/
theorem RowBoundR.nonneg {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (ω : Ω) : 0 ≤ ρ := by
  simpa using h.partial hβ0 0 ω 0

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition with `ρ < 1`, at every state
`∑_m β^m |W_u^{(m)}(ω)|` converges, with sum at most `1/(1−ρ)`. -/
theorem weight_series_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) (ω : Ω) (u : ℕ) :
    Summable (fun m => β ^ m * |weight (fun t v => A t v ω) u m|) ∧
      ∑' m, β ^ m * |weight (fun t v => A t v ω) u m| ≤ 1 / (1 - ρ) := by
  have hρ0 := h.nonneg hβ0 ω
  have hb : ∀ N, ∑ m ∈ Finset.range N, β ^ m * |weight (fun t v => A t v ω) u m| ≤
      1 / (1 - ρ) := by
    intro N
    refine (sum_abs_weight_le hβ0 hρ0 (fun t N => h.partial hβ0 t ω N) N u).trans ?_
    have hg := summable_geometric_of_lt_one hρ0 hρ1
    refine (hg.sum_le_tsum _ fun n _ => pow_nonneg hρ0 n).trans ?_
    rw [tsum_geometric_of_lt_one hρ0 hρ1, one_div]
  have hnn : ∀ m, 0 ≤ β ^ m * |weight (fun t v => A t v ω) u m| := fun m =>
    mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)
  exact ⟨summable_of_sum_range_le hnn hb, Real.tsum_le_of_sum_range_le hnn hb⟩

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: under the row condition with random bounds
the pathwise weighted present value `Z` solves the flow system state by state, and
`|Z_t| ≤ M/(1−ρ)`. -/
theorem pathZΩ_rowR {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω *
      pathZΩ β A s (t + (j + 1)) ω)) (pathZΩ β A s t ω - s t ω)) ∧
      ∀ t ω, |pathZΩ β A s t ω| ≤ M / (1 - ρ) := by
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · exact pathZ_solves hβ0 (fun u => hsb u ω) (fun u => (weight_series_le hβ0 hρ1 h ω u).1)
      (fun u => (weight_series_le hβ0 hρ1 h ω u).2) t (h t ω).1
  · have := (pathZ_summable_bound hβ0 (fun u => hsb u ω) (weight_series_le hβ0 hρ1 h ω t).1
      (weight_series_le hβ0 hρ1 h ω t).2).2
    rw [one_div_mul_eq_div] at this
    exact this

/-! ### Uniqueness, for every expectation system -/

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition the expected rows satisfy
`∑_{j<N} β^{j+1} E_t|A_t^{(t+j+1)}| ≤ ρ` (finite additivity of `E_t` suffices). -/
theorem E_row_partial {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (t : ℕ) (ω : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range N, β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω ≤ ρ := by
  have hle : (∑ j ∈ Finset.range N, β ^ (j + 1) • fun ω' => |A t (t + (j + 1)) ω'|) ≤
      fun _ => ρ := fun ω' => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact h.partial hβ0 t ω' N
  have := 𝔼.mono t hle ω
  rw [𝔼.const, map_sum, Finset.sum_apply] at this
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this

/-- Cochrane (2023), §7.4: a term of the system is bounded through the expected absolute row,
`|β^{j+1} E_t(A d)| ≤ β^{j+1} E_t|A| K` when `|d| ≤ K`. -/
theorem abs_term_le {β K : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} {d : ℕ → Ω → ℝ}
    (hK : ∀ t ω, |d t ω| ≤ K) (t j : ℕ) (ω : Ω) :
    |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
      β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω * K := by
  rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω).trans ?_) (pow_nonneg hβ0 _)
  have hle : (fun ω' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω'|) ≤
      K • fun ω' => |A t (t + (j + 1)) ω'| := fun ω' => by
    simp only [Pi.mul_apply, abs_mul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm K]
    exact mul_le_mul_of_nonneg_left (hK _ ω') (abs_nonneg _)
  have := 𝔼.mono t hle ω
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm K] at this
  exact this

/-- Cochrane (2023), eq. (7.14), p. 225: under the row condition, for `|d| ≤ K` the series
`∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` converges absolutely and its sum is at most `ρ K` in
absolute value. -/
theorem row_series {β ρ K : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    {d : ℕ → Ω → ℝ} (hK : ∀ t ω, |d t ω| ≤ K) (t : ℕ) (ω : Ω) :
    Summable (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω) ∧
      |∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤ ρ * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK t ω)
  set g : ℕ → ℝ := fun j => β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω * K
    with hg
  have hEA : ∀ j, 0 ≤ 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω := fun j => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ fun ω' => |A t (t + (j + 1)) ω'| from
      fun ω' => abs_nonneg _) ω
    rwa [𝔼.const] at this
  have hg0 : ∀ j, 0 ≤ g j := fun j => mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (hEA j)) hK0
  have hgN : ∀ N, ∑ j ∈ Finset.range N, g j ≤ ρ * K := fun N => by
    simp only [hg]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (E_row_partial 𝔼 hβ0 h t ω N) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hgN
  have hb : ∀ j, ‖β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω‖ ≤ g j :=
    fun j => by rw [Real.norm_eq_abs]; exact abs_term_le 𝔼 hβ0 hK t j ω
  have hs := Summable.of_norm_bounded hgs hb
  refine ⟨hs, ?_⟩
  have hsn : Summable (fun j : ℕ => ‖β ^ (j + 1) *
      𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  have h0 := norm_tsum_le_tsum_norm hsn
  rw [Real.norm_eq_abs] at h0
  exact h0.trans ((Summable.tsum_le_tsum hb hsn hgs).trans
    (Real.tsum_le_of_sum_range_le hg0 hgN))

/-- Cochrane (2023), §7.4, p. 225: **uniqueness under the row condition with random bounds.** If
`ρ < 1`, the only bounded solution of the homogeneous system
`d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is zero, for every expectation system. -/
theorem unique_of_rowR {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  have hstep : ∀ n t ω, |d t ω| ≤ ρ ^ n * K := by
    intro n
    induction n with
    | zero => intro t ω; simpa using hK t ω
    | succ n ih =>
      intro t ω
      have := (row_series 𝔼 hβ0 h ih t ω).2
      rw [(hd t ω).tsum_eq] at this
      rw [pow_succ, mul_comm (ρ ^ n) ρ, mul_assoc]
      exact this
  funext t ω
  have hρ0 := h.nonneg hβ0 ω
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  have := ge_of_tendsto' hlim (fun n => hstep n t ω)
  simpa using abs_nonpos_iff.mp this

/-! ### Existence, for every expectation system -/

/-- Cochrane (2023), eq. (7.14), p. 225: the right-hand operator of the flow system,
`(K y)_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} y_{t+j+1})`. -/
noncomputable def opK (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω

/-- Cochrane (2023), eq. (7.14), p. 225: the iterates `y⁰ = 0`, `y^{n+1} = s + K yⁿ`. -/
noncomputable def iterY (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun t ω => s t ω + opK 𝔼 β A (iterY β A s n) t ω

/-- Cochrane (2023), eq. (7.14), p. 225: on bounded processes the operator is a difference
operator, `K y − K y' = K(y − y')`. -/
theorem opK_sub {β ρ K K' : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    {y y' : ℕ → Ω → ℝ} (hK : ∀ t ω, |y t ω| ≤ K) (hK' : ∀ t ω, |y' t ω| ≤ K') (t : ℕ)
    (ω : Ω) : opK 𝔼 β A y t ω - opK 𝔼 β A y' t ω = opK 𝔼 β A (y - y') t ω := by
  unfold opK
  rw [← ((row_series 𝔼 hβ0 h hK t ω).1.hasSum.sub (row_series 𝔼 hβ0 h hK' t ω).1.hasSum).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Pi.sub_apply, mul_sub, map_sub]

/-- Cochrane (2023), eq. (7.14), p. 225: the iterates are bounded by `M/(1−ρ)` and successive
iterates differ by at most `M ρ^n`. -/
theorem iterY_bounds {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (n : ℕ) :
    (∀ t ω, |iterY 𝔼 β A s n t ω| ≤ M / (1 - ρ)) ∧
      ∀ t ω, |iterY 𝔼 β A s (n + 1) t ω - iterY 𝔼 β A s n t ω| ≤ M * ρ ^ n := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hb : ∀ n t ω, |iterY 𝔼 β A s n t ω| ≤ M / (1 - ρ) := by
    intro n
    induction n with
    | zero =>
      intro t ω
      simp only [iterY, abs_zero]
      exact div_nonneg ((abs_nonneg _).trans (hsb t ω)) h1ρ.le
    | succ n ih =>
      intro t ω
      simp only [iterY]
      have h2 := (row_series 𝔼 hβ0 h ih t ω).2
      have : M + ρ * (M / (1 - ρ)) = M / (1 - ρ) := by field_simp; ring
      refine (abs_add_le _ _).trans ?_
      rw [← this]
      exact add_le_add (hsb t ω) h2
  refine ⟨hb n, ?_⟩
  induction n with
  | zero =>
    intro t ω
    have h0 : opK 𝔼 β A (fun _ _ => 0) t ω = 0 := by
      unfold opK
      have : (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) *
          (fun _ _ => (0 : ℝ)) (t + (j + 1))) ω) = fun _ => 0 := by
        funext j
        rw [show (A t (t + (j + 1)) * (fun _ _ => (0 : ℝ)) (t + (j + 1))) = 0 from
          funext fun _ => mul_zero _, map_zero]
        simp
      rw [this, tsum_zero]
    simp only [iterY, h0, add_zero, sub_zero, pow_zero, mul_one]
    exact hsb t ω
  | succ n ih =>
    intro t ω
    have hd : iterY 𝔼 β A s (n + 1 + 1) t ω - iterY 𝔼 β A s (n + 1) t ω =
        opK 𝔼 β A (iterY 𝔼 β A s (n + 1) - iterY 𝔼 β A s n) t ω := by
      rw [← opK_sub 𝔼 hβ0 h (hb (n + 1)) (hb n)]
      simp only [iterY]
      ring
    rw [hd]
    have h2 := (row_series 𝔼 hβ0 h (d := iterY 𝔼 β A s (n + 1) - iterY 𝔼 β A s n)
      (fun t ω => by simpa only [Pi.sub_apply] using ih t ω) t ω).2
    refine h2.trans (le_of_eq ?_)
    ring

/-- Cochrane (2023), eq. (7.14), p. 225: **existence under the row condition with random
bounds**, for every expectation system: the flow system (7.14) has a solution with
`|y_t| ≤ M/(1−ρ)` (the limit of the iterates `iterY`). -/
theorem exists_bounded_solution {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    ∃ y : ℕ → Ω → ℝ, (∀ t, GeneralFormula.MaturingSystem 𝔼 β A y s t) ∧
      ∀ t ω, |y t ω| ≤ M / (1 - ρ) := by
  have hbd := fun n => iterY_bounds 𝔼 hβ0 hρ1 h hsb n
  have hcau : ∀ t ω, CauchySeq (fun n => iterY 𝔼 β A s n t ω) := fun t ω =>
    cauchySeq_of_le_geometric ρ M hρ1 fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact (hbd n).2 t ω
  set y : ℕ → Ω → ℝ := fun t ω => limUnder atTop (fun n => iterY 𝔼 β A s n t ω) with hy
  have hlim : ∀ t ω, Tendsto (fun n => iterY 𝔼 β A s n t ω) atTop (𝓝 (y t ω)) :=
    fun t ω => (hcau t ω).tendsto_limUnder
  have hyb : ∀ t ω, |y t ω| ≤ M / (1 - ρ) := fun t ω =>
    le_of_tendsto' (hlim t ω).abs fun n => (hbd n).1 t ω
  have hdist : ∀ n t ω, |iterY 𝔼 β A s n t ω - y t ω| ≤ M * ρ ^ n / (1 - ρ) := fun n t ω => by
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto ρ M hρ1 (fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact (hbd n).2 t ω) (hlim t ω) n
  have hfix : ∀ t ω, y t ω = s t ω + opK 𝔼 β A y t ω := by
    intro t ω
    have hρ0 := h.nonneg hβ0 ω
    have h1 : Tendsto (fun n => iterY 𝔼 β A s (n + 1) t ω) atTop (𝓝 (y t ω)) :=
      (hlim t ω).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => iterY 𝔼 β A s (n + 1) t ω) atTop
        (𝓝 (s t ω + opK 𝔼 β A y t ω)) := by
      have hc : Tendsto (fun n : ℕ => ρ * (M * ρ ^ n / (1 - ρ))) atTop (𝓝 0) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul M).div_const (1 - ρ)
        simpa using this.const_mul ρ
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc
      simp only [iterY, Real.norm_eq_abs]
      rw [show s t ω + opK 𝔼 β A (iterY 𝔼 β A s n) t ω - (s t ω + opK 𝔼 β A y t ω) =
        opK 𝔼 β A (iterY 𝔼 β A s n) t ω - opK 𝔼 β A y t ω by ring,
        opK_sub 𝔼 hβ0 h ((hbd n).1) hyb]
      exact (row_series 𝔼 hβ0 h (d := iterY 𝔼 β A s n - y)
        (fun t ω => by simpa only [Pi.sub_apply] using hdist n t ω) t ω).2
    exact tendsto_nhds_unique h1 h2
  refine ⟨y, fun t ω => ?_, hyb⟩
  have := (row_series 𝔼 hβ0 h hyb t ω).1.hasSum
  convert this using 1
  rw [hfix t ω, opK]
  ring

/-- Cochrane (2023), §7.4, p. 225: **existence and uniqueness under the row condition with random
bounds**, for every expectation system: the flow system (7.14) has exactly one bounded
solution. -/
theorem existsUnique_bounded_solution {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    ∃! y : ℕ → Ω → ℝ, (∀ t, GeneralFormula.MaturingSystem 𝔼 β A y s t) ∧
      ∃ K, ∀ t ω, |y t ω| ≤ K := by
  obtain ⟨y, hy, hyb⟩ := exists_bounded_solution 𝔼 hβ0 hρ1 h hsb
  refine ⟨y, ⟨hy, _, hyb⟩, ?_⟩
  rintro y' ⟨hy', K, hK⟩
  have := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy' hy)
    (K := K + M / (1 - ρ)) (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hK t ω) (hyb t ω)))
  exact sub_eq_zero.mp this

/-! ### Theorem W with random bounds -/

/-- Cochrane (2023), eq. (7.17), p. 225: `E_t` passes through absolutely convergent series of
random variables (a theorem of the axioms: `TidyR5SeriesExchange.seriesExchange`). -/
def SeriesExchange : Prop :=
  ∀ f : ℕ → Ω → ℝ, (∀ ω, Summable (fun n => |f n ω|)) → ∀ t ω,
    HasSum (fun n => 𝔼.E t (f n) ω) (𝔼.E t (fun ω' => ∑' n, f n ω') ω)

/-- Cochrane (2023), eq. (7.17): perfect foresight passes through absolutely convergent series. -/
theorem perfectForesight_seriesExchange : SeriesExchange perfectForesight := by
  intro f hf t ω
  exact ((hf ω).of_abs).hasSum

/-- Cochrane (2023), eq. (7.17): every finite event tree passes through absolutely convergent
series (a conditional expectation is a finite weighted sum). -/
theorem finiteTree_seriesExchange {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : SeriesExchange T.toExpectationSystem := by
  classical
  intro f hf t ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  by_cases hω : T.info t ω' ω
  · simp only [hω, ↓reduceIte]
    exact ((hf ω').of_abs).hasSum.mul_left _
  · simp only [hω, ↓reduceIte]
    exact hasSum_zero

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: under the row condition with random
bounds, if `E_t` passes through absolutely convergent series, (7.17) converges absolutely,
`|y_t| ≤ M/(1−ρ)`, it is known at `t`, and it solves the flow system (7.14). -/
theorem formulaW_solves_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  obtain ⟨hpw, hZb⟩ := pathZΩ_rowR hβ0 hρ1 h hsb
  have hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω)
      (𝔼.E t (pathZΩ β A s t) ω) := by
    intro t ω
    have habs : ∀ ω', Summable (fun m => |β ^ m * (weight A t m ω' * s (t + m) ω')|) := by
      intro ω'
      have := (pathZ_summable_bound hβ0 (fun u => hsb u ω') (weight_series_le hβ0 hρ1 h ω' t).1
        (weight_series_le hβ0 hρ1 h ω' t).2).1
      simpa only [weight_apply] using this
    have hh := hex (fun m ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) habs t ω
    have hZ : (fun ω' => ∑' m, β ^ m * (weight A t m ω' * s (t + m) ω')) = pathZΩ β A s t := by
      funext ω'
      simp only [pathZΩ, pathZ, weight_apply]
    rw [hZ] at hh
    refine hh.congr_fun fun m => ?_
    rw [formulaTerm, show (fun ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) =
      β ^ m • (weight A t m * s (t + m)) from rfl, map_smul]
    rfl
  have hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) *
        (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω) := by
    intro t ω
    refine hex _ (fun ω' => ?_) t ω
    refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
      ((h t ω').1.mul_right (M / (1 - ρ)))
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hZb _ ω') (abs_nonneg _))
      (pow_nonneg hβ0 _)
  have hfw := formulaW_eq_E 𝔼 hex1
  refine ⟨formulaW_solves_of_exchange 𝔼 hpo hA hs hpw hex1 hex2, fun t ω => ?_,
    fun t ω => ?_, formulaW_adapted_of_exchange 𝔼 hex1⟩
  · rw [hfw t]; exact hex1 t ω
  · rw [hfw t]; exact 𝔼.abs_E_le (hZb t) t ω

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W with random bounds.** Under the row condition
with random bounds (`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j`, bounded adapted
surpluses and an expectation system that passes through absolutely convergent series, every
bounded solution of the flow conditions (7.14) is the weighted present value (7.17),
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`, an absolutely convergent series. -/
theorem theoremW_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M K : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) := by
  obtain ⟨hz, hsum, hzb, -⟩ := formulaW_solves_rowR 𝔼 hpo hex hβ0 hρ1 h hA hs hsb
  have hd := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy hz)
    (K := K + M / (1 - ρ)) (fun u ω' => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hyb u ω') (hzb u ω')))
  have hyz : y t ω = formulaW 𝔼 β A s t ω := by
    have := congrFun (congrFun hd t) ω
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  rw [hyz]
  exact hsum t ω

/-- Cochrane (2023), §7.4, p. 225: **the price level is determined under the row condition with
random bounds**: two adapted price paths satisfying every flow condition (7.1) with bounded real
values of maturing debt coincide, for every expectation system with the pull-out property. -/
theorem price_unique_rowR (hpo : 𝔼.PullOut) {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (hb' : ∀ t ω, |D t t ω * x' t ω| ≤ K) : x = x' := by
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hzero := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy hy') (K := K + K)
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), eq. (7.17), p. 225: **(7.17) for the price level with random bounds.** In an
equilibrium with bounded real maturing debt, under the row condition with random bounds, with
each sale fraction known at the last sale date and an expectation system passing through
absolutely convergent series, `B_{t−1}^{(t)}/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem price_formula_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M K : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  theoremW_rowR 𝔼 hpo hex hβ0 hρ1 h hA hs hsb
    (fun u => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm u).mp (hflow u)) hb t ω

/-! ### The random row condition is strictly weaker than the deterministic one -/

/-- Cochrane (2023), §7.4 (illustration): sale fractions whose row `t` has a single entry
`ρ/β^{t+1}` at lag `t` (maturity `2t + 1`), perfect foresight. -/
noncomputable def sxA (β ρ : ℝ) : ℕ → ℕ → Unit → ℝ :=
  fun t m _ => if m = 2 * t + 1 then ρ / β ^ (t + 1) else 0

/-- Cochrane (2023), §7.4: each row of `sxA` sums to exactly `ρ`, so `sxA` satisfies the row
condition with (time-varying) bounds. -/
theorem sx_rowBoundR {β ρ : ℝ} (hβ0 : 0 < β) (hρ0 : 0 ≤ ρ) : RowBoundR β (sxA β ρ) ρ := by
  intro t u
  have hfun : (fun j : ℕ => β ^ (j + 1) * |sxA β ρ t (t + (j + 1)) u|) =
      Pi.single t ρ := by
    funext j
    by_cases hj : j = t
    · subst hj
      simp only [sxA, show j + (j + 1) = 2 * j + 1 by omega, ↓reduceIte, Pi.single_eq_same]
      rw [abs_of_nonneg (div_nonneg hρ0 (pow_nonneg hβ0.le _))]
      field_simp
    · simp only [sxA, show ¬ (t + (j + 1) = 2 * t + 1) by omega, ↓reduceIte, abs_zero, mul_zero]
      rw [Pi.single_eq_of_ne hj]
  rw [hfun]
  exact ⟨(hasSum_pi_single t ρ).summable, le_of_eq (hasSum_pi_single t ρ).tsum_eq⟩

/-- Cochrane (2023), §7.4: **the deterministic row condition fails for `sxA`** (`ρ > 0`): any
date-independent bound has `β^{j+1} a_j ≥ ρ` for every `j`, so `∑_j β^{j+1} a_j` diverges. -/
theorem sx_not_rowBound {β ρ : ℝ} (hβ0 : 0 < β) (hρ : 0 < ρ) :
    ¬ ∃ a ρ', RowBound β (sxA β ρ) a ρ' := by
  rintro ⟨a, ρ', hrow⟩
  have hge : ∀ j, ρ ≤ β ^ (j + 1) * a j := by
    intro j
    have := hrow.2.1 j j ()
    simp only [sxA, show j + (j + 1) = 2 * j + 1 by omega, ↓reduceIte] at this
    rw [abs_of_nonneg (div_nonneg hρ.le (pow_nonneg hβ0.le _)),
      div_le_iff₀ (pow_pos hβ0 _)] at this
    linarith
  have hlim := hrow.2.2.1.tendsto_atTop_zero
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hρ)).exists
  exact absurd (hge j) (not_le.mpr hj)

end Cochrane.LongTermDebtDynamics.TidyR5RandomRow

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expected future bond sales with random debt

Cochrane (2023), Online Appendix §A1.14, pp. 588–592, equations (1.63)–(1.68), and §7.3.3,
p. 224.

`FutureSales.x0Fun`, `FutureSales.hasDerivAt_x0` and `FutureSales.x1_formula` treat the expected
date-1 sale `F = B_1^{(2)} − B_0^{(2)}` as a number. Here the sale is a random variable known at
date 1 (a state-contingent sale), the date-0 positions `B_{−1}^{(j)}`, `B_0^{(j)}` are known at date
0, and surpluses are random. The sale is perturbed in a random direction `G` known at date 1:
`B_1^{(2)}(ε) = B_1^{(2)} + ε G` (`pertD`).

* `x0_eq_x0R`, `x0R_pull`: in every equilibrium of the three-period economy, `1/P_0` is the closed
  form (1.65)/(1.66) `x0R ε`, and with the date-0 quantities pulled out of `E_0`,
  `B_{−1}^{(0)} x0R ε = s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(β² s_2 B_0^{(2)}(A₂ − A₁)/B_1^{(2)}(ε))`
  with `A_k = (B_0^{(k)} − B_{−1}^{(k)})/B_0^{(k)}`.
* `hasDerivAt_x0R`: **the derivative with random debt**,
  `d(1/P_0)/dε = β² B_0^{(2)} (A₁ − A₂) E_0(G s_2/(B_1^{(2)})²)/B_{−1}^{(0)}`, an exact `HasDerivAt`
  (the deterministic `FutureSales.hasDerivAt_x0` is the case `G = 1`, `s_2` known).
* `x0R_mono`, `x0R_strictMono`, `x0R_anti`, `x0R_const`: **the sign rule with random debt**: if
  the government sells proportionally more time-1 than time-2 debt at date 0 (`A₁ ≥ A₂`), larger
  state-contingent future sales (`G ≥ 0`) lower `P_0`; strictly under uniform bounds; the reverse
  for `A₁ ≤ A₂`; no effect at all when `A₁ = A₂`. The hypothesis `s_2 ≥ 0` is not an extra
  restriction: positive `P_2` requires `s_2 > 0` (`price_two_pos_iff`).
* `E_x1_eq_x1R`, `hasDerivAt_x1R`, `x1R_mono`: (1.64) with random sales: expected future sales
  raise `E_0(1/P_1)` (and the bond price `Q_0^{(1)}` with `P_0` fixed) when `B_0^{(2)} ≥ 0`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom

open Filter Topology MaturityStructure Asymptotics

/-- Cochrane (2023), Online Appendix p. 592: the derivative of `ε ↦ E_t(h/(u + εG))` at `0` is
`E_t(−hG/u²)`, for `u ≥ δ > 0`, `|G| ≤ Γ` and `|h| ≤ H` (the remainder is `O(ε²)` uniformly in
the state, so it passes through `E_t`). -/
theorem hasDerivAt_E_div {Ω : Type*} (𝔼 : ExpectationSystem Ω) {δ Γ H : ℝ} (hδ : 0 < δ)
    {u G h : Ω → ℝ} (hu : ∀ ω, δ ≤ u ω) (hG : ∀ ω, |G ω| ≤ Γ) (hh : ∀ ω, |h ω| ≤ H) (t : ℕ)
    (ω : Ω) :
    HasDerivAt (fun ε : ℝ => 𝔼.E t (h / (u + ε • G)) ω) (𝔼.E t (-(h * G) / u ^ 2) ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hh ω)
  set η : ℝ := δ / (2 * (Γ + 1)) with hη
  have hηpos : 0 < η := div_pos hδ (by linarith)
  have hηΓ : η * Γ ≤ δ / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hbig : (fun e : ℝ => 𝔼.E t (h / (u + (0 + e) • G)) ω - 𝔼.E t (h / (u + (0 : ℝ) • G)) ω -
      e • 𝔼.E t (-(h * G) / u ^ 2) ω) =O[𝓝 0] (fun e : ℝ => e ^ 2) := by
    refine IsBigO.of_bound (2 * H * Γ ^ 2 / δ ^ 3) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have heΓ : |e| * Γ ≤ δ / 2 :=
      (mul_le_mul_of_nonneg_right he.le hΓ).trans hηΓ
    have hw : ∀ ω', δ / 2 ≤ u ω' + e * G ω' := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hG ω') (abs_nonneg e)).trans heΓ
      have := neg_abs_le (e * G ω')
      linarith [hu ω']
    have hfun : h / (u + (0 + e) • G) - h / (u + (0 : ℝ) • G) - e • (-(h * G) / u ^ 2) =
        fun ω' => h ω' * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω')) := by
      funext ω'
      have hv : 0 < u ω' := hδ.trans_le (hu ω')
      have hw' : 0 < u ω' + e * G ω' := (half_pos hδ).trans_le (hw ω')
      simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.neg_apply, Pi.mul_apply, Pi.pow_apply, zero_add, zero_mul, add_zero]
      field_simp
      ring
    have hval : 𝔼.E t (h / (u + (0 + e) • G)) ω - 𝔼.E t (h / (u + (0 : ℝ) • G)) ω -
        e • 𝔼.E t (-(h * G) / u ^ 2) ω =
        𝔼.E t (fun ω' => h ω' * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω'))) ω := by
      rw [← hfun, map_sub, map_sub, map_smul]
      rfl
    rw [hval, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hv : δ ≤ u ω' := hu ω'
    have hv0 : 0 < u ω' := hδ.trans_le hv
    have hw' := hw ω'
    have hden : δ ^ 2 * (δ / 2) ≤ u ω' ^ 2 * (u ω' + e * G ω') :=
      mul_le_mul (pow_le_pow_left₀ hδ.le hv 2) hw' (by positivity) (by positivity)
    have hG2 : G ω' ^ 2 ≤ Γ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hG ω') 2
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (G ω')),
      abs_of_nonneg (sq_nonneg e),
      abs_of_pos (mul_pos (pow_pos hv0 2) ((half_pos hδ).trans_le hw'))]
    calc |h ω'| * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω'))
        ≤ H * Γ ^ 2 * e ^ 2 / (δ ^ 2 * (δ / 2)) := by
          apply div_le_div₀ (by positivity) _ (by positivity) hden
          exact mul_le_mul_of_nonneg_right (mul_le_mul (hh ω') hG2 (sq_nonneg _) hH)
            (sq_nonneg e)
      _ = 2 * H * Γ ^ 2 / δ ^ 3 * e ^ 2 := by field_simp
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix p. 589: the policy with the date-1 sale of time-2 debt
perturbed in the random direction `G`: `B_1^{(2)}(ε) = B_1^{(2)} + ε G`, all else unchanged. -/
noncomputable def pertD (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) : ℕ → ℕ → Ω → ℝ :=
  fun t m => if t = 2 ∧ m = 2 then D 2 2 + ε • G else D t m

/-- Cochrane (2023), Online Appendix p. 589: the perturbed time-2 debt. -/
theorem pertD_22 (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) :
    pertD D G ε 2 2 = D 2 2 + ε • G := by simp [pertD]

/-- Cochrane (2023), Online Appendix p. 589: the other positions are unchanged. -/
theorem pertD_ne (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) {t m : ℕ} (h : ¬ (t = 2 ∧ m = 2)) :
    pertD D G ε t m = D t m := by simp [pertD, h]

/-- Cochrane (2023), Online Appendix p. 589: with the direction `G` known at date 1, the perturbed
debt is predetermined whenever the original debt is. -/
theorem pertD_predetermined {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG : 𝔼.E 1 G = G) (ε : ℝ) : Predetermined 𝔼 (pertD D G ε) := by
  refine ⟨fun m => ?_, fun t m => ?_⟩
  · rw [pertD_ne D G ε (by omega)]; exact hD.1 m
  · by_cases h : t + 1 = 2 ∧ m = 2
    · obtain ⟨h1, rfl⟩ := h
      obtain rfl : t = 1 := by omega
      rw [pertD_22, map_add, map_smul, hD.2 1 2, hG]
    · rw [pertD_ne D G ε h]; exact hD.2 t m

/-- Cochrane (2023), Online Appendix eq. (1.65)/(1.66), pp. 590–591: the closed form for `1/P_0`
along the perturbation, with random debt. -/
noncomputable def x0R (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  (s 0 + (D 1 1 - D 0 1) / D 1 1 *
      𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2)) +
    𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2))) / D 0 0

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66), pp. 589–591: **in every equilibrium of
the three-period economy with random debt**, `1/P_0 = x0R ε` (the flow conditions (7.1) at dates
0, 1, 2 with the perturbed policy). -/
theorem x0_eq_x0R (hpo : 𝔼.PullOut) {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hG : 𝔼.E 1 G = G)
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β (pertD D G ε) x s 0)
    (h1 : RealFlow 𝔼 β (pertD D G ε) x s 1) (h2 : RealFlow 𝔼 β (pertD D G ε) x s 2)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (hD00 : ∀ ω, D 0 0 ω ≠ 0) :
    x 0 = x0R 𝔼 β D G s ε := by
  have hD3' : ∀ t j, pertD D G ε t (j + 3) = 0 := fun t j => by
    rw [pertD_ne D G ε (by omega)]; exact hD3 t j
  obtain ⟨F2, F1, F0⟩ := FutureSales.flows_of_realFlow 𝔼 hD3' h0 h1 h2
  have hp := pertD_predetermined 𝔼 hD hG ε
  have h22 : ∀ ω, pertD D G ε 2 2 ω ≠ 0 := fun ω => by
    rw [pertD_22]; simpa using hD22 ω
  have h11 : ∀ ω, pertD D G ε 1 1 ω ≠ 0 := fun ω => by
    rw [pertD_ne D G ε (by omega)]; exact hD11 ω
  have hz := FutureSales.price_zero 𝔼 hpo hp F2 F1 F0 h22 h11
  rw [pertD_22, pertD_ne D G ε (show ¬ (0 = 2 ∧ 0 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (0 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 2 = 2) by omega),
    pertD_ne D G ε (show ¬ (0 = 2 ∧ 2 = 2) by omega)] at hz
  funext ω
  have := congrFun hz ω
  simp only [Pi.mul_apply, Pi.add_apply] at this
  rw [x0R, Pi.div_apply, eq_div_iff (hD00 ω), mul_comm, this]
  rfl

/-- Cochrane (2023), Online Appendix p. 592: Cochrane's date-0 sale fractions
`A₁ = (B_0^{(1)} − B_{−1}^{(1)})/B_0^{(1)}`, `A₂ = (B_0^{(2)} − B_{−1}^{(2)})/B_0^{(2)}`, random but
known at date 0. -/
noncomputable def fracA (D : ℕ → ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ := (D 1 k - D 0 k) / D 1 k

/-- Cochrane (2023), Online Appendix p. 592: the coefficient of the dilution term,
`β² s_2 B_0^{(2)}(A₂ − A₁)`, written as `β² s_2 ((B_0^{(2)} − B_{−1}^{(2)}) − A₁ B_0^{(2)})`. -/
noncomputable def kCoef (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) : Ω → ℝ :=
  β ^ 2 • (s 2 * ((D 1 2 - D 0 2) - fracA D 1 * D 1 2))

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, with the date-0 quantities pulled out of
`E_0`: `B_{−1}^{(0)} x0R ε = s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(k/B_1^{(2)}(ε))` with
`k = β² s_2 B_0^{(2)}(A₂ − A₁)` (`kCoef`), whenever `B_1^{(2)}(ε) ≠ 0` in every state. -/
theorem x0R_pull (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) :
    x0R 𝔼 β D G s ε = (s 0 + fracA D 1 * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) +
      𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G))) / D 0 0 := by
  have hA1 : 𝔼.E 0 (fracA D 1) = fracA D 1 :=
    hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 1)
  have hsplit : β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) =
      (β • s 1 + β ^ 2 • s 2) - β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)) := by
    funext ω
    have := hD22 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply]
    field_simp
    ring
  have hk : 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) -
      fracA D 1 * 𝔼.E 0 (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) =
      𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G)) := by
    rw [← hpo 0 _ _ hA1, ← map_sub]
    congr 1
    funext ω
    have := hD22 ω
    simp only [kCoef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.add_apply]
    field_simp
  rw [x0R]
  unfold fracA at hk ⊢
  rw [hsplit, map_sub, mul_sub, ← hk]
  congr 1
  ring

/-- Cochrane (2023), Online Appendix p. 592: `kCoef = β² s_2 B_0^{(2)} (A₂ − A₁)` when
`B_0^{(2)} ≠ 0`. -/
theorem kCoef_eq {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ} (h12 : ∀ ω, D 1 2 ω ≠ 0) :
    kCoef β D s = β ^ 2 • (s 2 * (D 1 2 * (fracA D 2 - fracA D 1))) := by
  funext ω
  have := h12 ω
  simp only [kCoef, fracA, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply,
    Pi.div_apply]
  field_simp

/-- Cochrane (2023), Online Appendix p. 592: **the derivative of `1/P_0` with respect to expected
future sales, with random debt.** For a state-contingent direction `G` known at date 1 with
`|G| ≤ Γ`, `B_1^{(2)} ≥ δ > 0`, `|s_2| ≤ H` and the date-0 positions bounded,
`d x0R/dε = β² B_0^{(2)} (A₁ − A₂) E_0(G s_2/(B_1^{(2)})²)/B_{−1}^{(0)}` at `ε = 0`. -/
theorem hasDerivAt_x0R (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β δ Γ K : ℝ} (hδ : 0 < δ) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hu : ∀ ω, δ ≤ D 2 2 ω) (hG : ∀ ω, |G ω| ≤ Γ)
    (hk : ∀ ω, |kCoef β D s ω| ≤ K) (h12 : ∀ ω, D 1 2 ω ≠ 0) (ω : Ω) :
    HasDerivAt (fun ε => x0R 𝔼 β D G s ε ω)
      (β ^ 2 * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) *
        𝔼.E 0 (G * s 2 / D 2 2 ^ 2) ω / D 0 0 ω) 0 := by
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hd := ((hasDerivAt_E_div 𝔼 hδ hu hG hk 0 ω).const_add
    (s 0 ω + fracA D 1 ω * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) ω)).div_const (D 0 0 ω)
  have hηpos : 0 < δ / (2 * (Γ + 1)) := div_pos hδ (by linarith)
  have hev : (fun ε => x0R 𝔼 β D G s ε ω) =ᶠ[𝓝 0] fun ε =>
      (s 0 ω + fracA D 1 ω * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) ω +
        𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G)) ω) / D 0 0 ω := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hne : ∀ ω', D 2 2 ω' + e * G ω' ≠ 0 := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]
        refine (mul_le_mul he.le (hG ω') (abs_nonneg _) hηpos.le).trans ?_
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have := neg_abs_le (e * G ω')
      have := hu ω'
      intro h0
      linarith
    rw [x0R_pull 𝔼 hpo hdc hD hne]
    rfl
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  have hA1 : 𝔼.E 0 (D 1 2 * (fracA D 1 - fracA D 2)) = D 1 2 * (fracA D 1 - fracA D 2) := by
    have k1 : 𝔼.E 0 (fracA D 1) = fracA D 1 :=
      hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 1)
    have k2 : 𝔼.E 0 (fracA D 2) = fracA D 2 :=
      hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 2)
    rw [hpo 0 _ _ (hD.2 0 2), map_sub, k1, k2]
  have hfun : -(kCoef β D s * G) / D 2 2 ^ 2 =
      β ^ 2 • ((D 1 2 * (fracA D 1 - fracA D 2)) * (G * s 2 / D 2 2 ^ 2)) := by
    rw [kCoef_eq h12]
    funext ω'
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, Pi.pow_apply]
    ring
  rw [hfun, map_smul, hpo 0 _ _ hA1]
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), Online Appendix eq. (1.63), p. 589: with `B_1^{(2)} > 0`, the price level
`P_2 = B_1^{(2)}/s_2` is positive if and only if `s_2 > 0`; so in an equilibrium with positive
prices the time-2 surplus is positive in every state. -/
theorem price_two_pos_iff {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (hD22 : ∀ ω, 0 < D 2 2 ω) (ω : Ω) : 0 < x 2 ω ↔ 0 < s 2 ω := by
  have := congrFun F2 ω
  simp only [Pi.mul_apply] at this
  rw [← this]
  exact ⟨fun h => mul_pos (hD22 ω) h, fun h => pos_of_mul_pos_right h (hD22 ω).le⟩

/-- Cochrane (2023), Online Appendix p. 592 (bullet), with random debt: **if the government sells
proportionally more time-1 than time-2 debt at date 0 (`A₁ ≥ A₂`, `B_0^{(2)} > 0`), larger
state-contingent future sales lower `P_0`**: for `G ≥ 0`, `s_2 ≥ 0`, `B_{−1}^{(0)} > 0`, `1/P_0` is
monotone in `ε` wherever `B_1^{(2)}(ε) > 0` in every state. -/
theorem x0R_mono (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω ≤ fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω ≤ x0R 𝔼 β D G s ε' ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  simp only [Pi.add_apply]
  have hle : kCoef β D s / (D 2 2 + ε • G) ≤ kCoef β D s / (D 2 2 + ε' • G) := fun ω' => by
    have hk : kCoef β D s ω' ≤ 0 := by
      rw [kCoef_eq (fun ω => (h12 ω).ne')]
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (mul_nonpos_of_nonneg_of_nonpos
        (hs2 ω') (mul_nonpos_of_nonneg_of_nonpos (h12 ω').le (by linarith [hA ω'])))
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_le_div_iff₀ (hpos ω') (hpos' ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  linarith [𝔼.mono 0 hle ω]

/-- Cochrane (2023), Online Appendix p. 592: conversely, if `A₁ ≤ A₂`, larger state-contingent
future sales raise `P_0`: `1/P_0` is antitone in `ε`. -/
theorem x0R_anti (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 1 ω ≤ fracA D 2 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x0R 𝔼 β D G s ε' ω ≤ x0R 𝔼 β D G s ε ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  simp only [Pi.add_apply]
  have hle : kCoef β D s / (D 2 2 + ε' • G) ≤ kCoef β D s / (D 2 2 + ε • G) := fun ω' => by
    have hk : 0 ≤ kCoef β D s ω' := by
      rw [kCoef_eq (fun ω => (h12 ω).ne')]
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonneg (sq_nonneg β) (mul_nonneg (hs2 ω')
        (mul_nonneg (h12 ω').le (by linarith [hA ω'])))
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_le_div_iff₀ (hpos' ω') (hpos ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  linarith [𝔼.mono 0 hle ω]

/-- Cochrane (2023), Online Appendix p. 592, with random debt: **when the two date-0 fractions
are equal (`A₁ = A₂`), expected future sales have no effect on `P_0` at all**, in any direction
`G` and for every `ε` with `B_1^{(2)}(ε) ≠ 0` in every state. -/
theorem x0R_const (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (h12 : ∀ ω, D 1 2 ω ≠ 0) (hA : fracA D 1 = fracA D 2)
    (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hne0 : ∀ ω, D 2 2 ω ≠ 0) :
    x0R 𝔼 β D G s ε = x0R 𝔼 β D G s 0 := by
  have hk : kCoef β D s = 0 := by
    rw [kCoef_eq h12, hA, sub_self]
    funext ω
    simp
  have hz : ∀ f : Ω → ℝ, (0 : Ω → ℝ) / f = 0 := fun f => funext fun ω => by simp
  rw [x0R_pull 𝔼 hpo hdc hD hne, x0R_pull 𝔼 hpo hdc hD (fun ω => by simpa using hne0 ω), hk,
    hz, hz]

/-- Cochrane (2023), Online Appendix p. 592 (bullet), with random debt, strict version: with
`A₁ − A₂ ≥ a > 0`, `B_0^{(2)} ≥ b > 0`, a direction `G ≥ γ > 0`, `s_2 ≥ σ > 0` and
`B_1^{(2)}(ε), B_1^{(2)}(ε') ≤ U`, larger future sales strictly lower `P_0`. -/
theorem x0R_strictMono (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β ε ε' a b γ σ U : ℝ} (hβ : β ≠ 0) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) (hσ : 0 < σ)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, γ ≤ G ω) (hs2 : ∀ ω, σ ≤ s 2 ω) (h12 : ∀ ω, b ≤ D 1 2 ω)
    (hA : ∀ ω, a ≤ fracA D 1 ω - fracA D 2 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hU : ∀ ω, D 2 2 ω + ε' * G ω ≤ U)
    (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω := by
  have hG0' : ∀ ω, 0 ≤ G ω := fun ω => hγ.le.trans (hG0 ω)
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0' ω]
  have h12' : ∀ ω, D 1 2 ω ≠ 0 := fun ω => (hb.trans_le (h12 ω)).ne'
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_lt_div_of_pos_right _ (hD00 ω)
  simp only [Pi.add_apply]
  set c : ℝ := β ^ 2 * σ * b * a * γ * (ε' - ε) / U ^ 2 with hc
  have hβ2 : 0 < β ^ 2 := by positivity
  have hU0 : 0 < U := (hpos' ω).trans_le (hU ω)
  have hcpos : 0 < c := by
    have : 0 < ε' - ε := by linarith
    positivity
  have hle : (fun _ => c) ≤ kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G) :=
    fun ω' => by
    rw [kCoef_eq h12']
    simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply]
    have hp := hpos ω'
    have hp' := hpos' ω'
    have hu' := hU ω'
    have hu : D 2 2 ω' + ε * G ω' ≤ U := by nlinarith [hG0' ω']
    set q : ℝ := β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 1 ω' - fracA D 2 ω'))) with hq
    have hq0 : β ^ 2 * σ * b * a ≤ q := by
      rw [hq]
      have h1 : σ * (b * a) ≤ s 2 ω' * (D 1 2 ω' * (fracA D 1 ω' - fracA D 2 ω')) :=
        mul_le_mul (hs2 ω') (mul_le_mul (h12 ω') (hA ω') ha.le (hb.le.trans (h12 ω')))
          (by positivity) (hσ.le.trans (hs2 ω'))
      nlinarith
    have hkey : β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 2 ω' - fracA D 1 ω'))) /
        (D 2 2 ω' + ε' * G ω') - β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 2 ω' - fracA D 1 ω'))) /
        (D 2 2 ω' + ε * G ω') = q * ((ε' - ε) * G ω') /
          ((D 2 2 ω' + ε * G ω') * (D 2 2 ω' + ε' * G ω')) := by
      rw [hq, div_sub_div _ _ hp'.ne' hp.ne', div_eq_div_iff (mul_ne_zero hp'.ne' hp.ne')
        (mul_ne_zero hp.ne' hp'.ne')]
      ring
    rw [hkey, hc]
    have hden : (D 2 2 ω' + ε * G ω') * (D 2 2 ω' + ε' * G ω') ≤ U ^ 2 := by
      rw [sq]; exact mul_le_mul hu hu' hp'.le hU0.le
    have hnum : β ^ 2 * σ * b * a * (γ * (ε' - ε)) ≤ q * ((ε' - ε) * G ω') := by
      have : γ * (ε' - ε) ≤ (ε' - ε) * G ω' := by nlinarith [hG0 ω']
      exact mul_le_mul hq0 this (by nlinarith)
        ((by positivity : (0 : ℝ) ≤ β ^ 2 * σ * b * a).trans hq0)
    rw [show β ^ 2 * σ * b * a * γ * (ε' - ε) / U ^ 2 =
      β ^ 2 * σ * b * a * (γ * (ε' - ε)) / U ^ 2 by ring]
    exact div_le_div₀ ((by positivity : (0 : ℝ) ≤ β ^ 2 * σ * b * a * (γ * (ε' - ε))).trans hnum)
      hnum (by positivity) hden
  have := 𝔼.mono 0 hle ω
  rw [𝔼.const, map_sub, Pi.sub_apply] at this
  linarith

/-! ### (1.64): the expected price level at date 1 -/

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `E_0(1/P_1)` along the perturbation,
`E_0[s_1 + β ((B_1^{(2)}(ε) − B_0^{(2)})/B_1^{(2)}(ε)) s_2] / B_0^{(1)}`. -/
noncomputable def x1R (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  𝔼.E 0 (s 1 + β • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2)) / D 1 1

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: in every equilibrium of the three-period
economy with random debt, `E_0(1/P_1) = x1R ε`. -/
theorem E_x1_eq_x1R (hpo : 𝔼.PullOut) {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hG : 𝔼.E 1 G = G)
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β (pertD D G ε) x s 0)
    (h1 : RealFlow 𝔼 β (pertD D G ε) x s 1) (h2 : RealFlow 𝔼 β (pertD D G ε) x s 2)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) :
    𝔼.E 0 (x 1) = x1R 𝔼 β D G s ε := by
  have hD3' : ∀ t j, pertD D G ε t (j + 3) = 0 := fun t j => by
    rw [pertD_ne D G ε (by omega)]; exact hD3 t j
  obtain ⟨F2, F1, -⟩ := FutureSales.flows_of_realFlow 𝔼 hD3' h0 h1 h2
  have hp := pertD_predetermined 𝔼 hD hG ε
  have h22 : ∀ ω, pertD D G ε 2 2 ω ≠ 0 := fun ω => by
    rw [pertD_22]; simpa using hD22 ω
  have hz := FutureSales.E_price_one 𝔼 hpo hp F2 F1 h22
  rw [pertD_22, pertD_ne D G ε (show ¬ (1 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 2 = 2) by omega)] at hz
  funext ω
  have := congrFun hz ω
  simp only [Pi.mul_apply] at this
  rw [x1R, Pi.div_apply, eq_div_iff (hD11 ω), mul_comm, this]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590, split: `x1R ε =
(E_0(s_1 + β s_2) − E_0(β B_0^{(2)} s_2/B_1^{(2)}(ε)))/B_0^{(1)}` when `B_1^{(2)}(ε) ≠ 0`. -/
theorem x1R_split {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) :
    x1R 𝔼 β D G s ε = (𝔼.E 0 (s 1 + β • s 2) -
      𝔼.E 0 (β • (D 1 2 * s 2) / (D 2 2 + ε • G))) / D 1 1 := by
  rw [x1R, ← map_sub]
  congr 2
  funext ω
  have := hD22 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
    Pi.sub_apply]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 591 (bullet), with random debt: the derivative of
`E_0(1/P_1)` with respect to expected future sales in a state-contingent direction `G`,
`β E_0(B_0^{(2)} G s_2/(B_1^{(2)})²)/B_0^{(1)}` (exact `HasDerivAt`, `B_1^{(2)} ≥ δ > 0`). -/
theorem hasDerivAt_x1R {β δ Γ H : ℝ} (hδ : 0 < δ) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hu : ∀ ω, δ ≤ D 2 2 ω) (hG : ∀ ω, |G ω| ≤ Γ)
    (hh : ∀ ω, |(β • (D 1 2 * s 2)) ω| ≤ H) (ω : Ω) :
    HasDerivAt (fun ε => x1R 𝔼 β D G s ε ω)
      (𝔼.E 0 (β • (D 1 2 * G * s 2 / D 2 2 ^ 2)) ω / D 1 1 ω) 0 := by
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hd := ((hasDerivAt_E_div 𝔼 hδ hu hG hh 0 ω).const_sub
    (𝔼.E 0 (s 1 + β • s 2) ω)).div_const (D 1 1 ω)
  have hηpos : 0 < δ / (2 * (Γ + 1)) := div_pos hδ (by linarith)
  have hev : (fun ε => x1R 𝔼 β D G s ε ω) =ᶠ[𝓝 0] fun ε =>
      (𝔼.E 0 (s 1 + β • s 2) ω - 𝔼.E 0 (β • (D 1 2 * s 2) / (D 2 2 + ε • G)) ω) / D 1 1 ω := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hne : ∀ ω', D 2 2 ω' + e * G ω' ≠ 0 := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]
        refine (mul_le_mul he.le (hG ω') (abs_nonneg _) hηpos.le).trans ?_
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have := neg_abs_le (e * G ω')
      have := hu ω'
      intro h0
      linarith
    rw [x1R_split 𝔼 hne]
    rfl
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  have hfun : -(β • (D 1 2 * s 2) * G) / D 2 2 ^ 2 = -(β • (D 1 2 * G * s 2 / D 2 2 ^ 2)) := by
    funext ω'
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul,
      Pi.pow_apply]
    ring
  rw [hfun, map_neg, Pi.neg_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 591 (bullet), with random debt: **if the government has
sold time-2 debt at date 0 (`B_0^{(2)} ≥ 0`), larger state-contingent future sales (`G ≥ 0`)
raise `E_0(1/P_1)`**, and so the bond price `Q_0^{(1)} = β P_0 E_0(1/P_1)` with `P_0` fixed
(`s_2 ≥ 0`, `β ≥ 0`, `B_0^{(1)} > 0`, `B_1^{(2)}(ε) > 0`). -/
theorem x1R_mono {β ε ε' : ℝ} (hβ : 0 ≤ β) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 ≤ D 1 2 ω)
    (hD11 : ∀ ω, 0 < D 1 1 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x1R 𝔼 β D G s ε ω ≤ x1R 𝔼 β D G s ε' ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x1R_split 𝔼 (fun ω => (hpos ω).ne'), x1R_split 𝔼 (fun ω => (hpos' ω).ne'),
    Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD11 ω).le
  have hle : β • (D 1 2 * s 2) / (D 2 2 + ε' • G) ≤ β • (D 1 2 * s 2) / (D 2 2 + ε • G) :=
    fun ω' => by
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    have hk : 0 ≤ β * (D 1 2 ω' * s 2 ω') := mul_nonneg hβ (mul_nonneg (h12 ω') (hs2 ω'))
    rw [div_le_div_iff₀ (hpos' ω') (hpos ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  simp only [Pi.sub_apply]
  linarith [𝔼.mono 0 hle ω]

end Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Forward guidance under uncertainty

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214), and
Online Appendix §A1.2.1, pp. 559–561 (the discrete geometric formula).

The book's forward-guidance analysis is deterministic. Here surpluses and price levels are
random (an arbitrary `ExpectationSystem` with the pull-out property), and the central bank
announces at date 0 a *known* path for the one-period nominal rate, `r` before `T` and `i` from
`T` on, implemented through the Fisher relation under uncertainty
`Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` (`FisherPath`), with `β = 1/(1+r)`.

* `bondPrice_eq_prod`, `stoch_fgPrice`: **bond prices are exactly the book's display**,
  `Q_0^{(j)} = ((1+r)^{min(j,T)}(1+i)^{j−T})^{-1}`, whatever the surplus uncertainty (the
  risk-neutral expectations hypothesis with a known rate path).
* `stoch_E0_path`: **the expected path**: `E_0(1/P_j) = 1/fgPath(P_0)`; the book's path is the
  path of expected values of `1/P_j`.
* `stoch_expected_inflation`, `stoch_no_expected_jump`, `stoch_expected_inflation_after`: the
  innovation form of "no second jump": before and at the rate rise the expected price ratio is
  one, `E_t(P_t/P_{t+1}) = 1` for `t < T`; from `T` on it is `(1+r)/(1+i) < 1`. Realised price
  levels move only with unforecastable news.
* `stoch_valuation`, `stoch_priceLevel`: the valuation equation (7.3) under uncertainty,
  `P_0 = (∑_j Q_0^{(j)} B_{−1}^{(j)}) / E_0 ∑ β^j s_j`, state by state.
* `stoch_fg_no_effect`, `stoch_fg_lowers`, `stoch_fg_mono`: the §7.1 claims under uncertainty:
  guidance beyond the longest maturity (`T ≥ k`) has no effect on `P_0`; otherwise, with some
  maturity `T < j₀ ≤ k` outstanding, nonnegative positions and `r < i`, it lowers `P_0`; the
  effect falls with the horizon (and the immediate rise has the largest effect).
* `stoch_geometric_value`, `stoch_fg_jump`: §A1.2.1 under uncertainty: with geometric
  maturities, the proportional jump `P_0/P − 1` (guidance versus no guidance, same surpluses) is
  the deterministic `ForwardGuidance.fgJump`, state by state.

The continuous-time formula of p. 561 is not restated: under the project's conventions continuous
time is deterministic (no stochastic calculus).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty

open Filter Topology MaturityStructure ForwardGuidance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): the announced, known path of one-period
nominal rates `i_t` is implemented: `Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` at every
date and state. -/
def FisherPath (β : ℝ) (P x : ℕ → Ω → ℝ) (i : ℕ → ℝ) : Prop :=
  ∀ t, bondPrice 𝔼 β P x t 1 = fun _ => (1 + i t)⁻¹

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the expectations hypothesis with a known
rate path.** If the announced rates `i_t` are implemented, every zero-coupon bond price is
deterministic, `Q_t^{(t+j)} = ∏_{u<j} (1 + i_{t+u})^{-1}`, however uncertain the price level. -/
theorem bondPrice_eq_prod (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} {i : ℕ → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 β P x i) (j : ℕ) :
    ∀ t, bondPrice 𝔼 β P x t j = fun _ => ∏ u ∈ Finset.range j, (1 + i (t + u))⁻¹ := by
  induction j with
  | zero =>
    intro t
    have h1 : P t * x (t + 0) = fun _ => (1 : ℝ) := funext fun ω => by simpa using hPx t ω
    simp only [bondPrice, pow_zero, one_smul, h1, 𝔼.const, Finset.range_zero, Finset.prod_empty]
  | succ j ih =>
    intro t
    have hsplit : P t * x (t + (j + 1)) = (P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j)) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [show t + 1 + j = t + (j + 1) by omega]
      have := hPx (t + 1) ω
      calc P t ω * x (t + (j + 1)) ω =
          P t ω * x (t + (j + 1)) ω * (P (t + 1) ω * x (t + 1) ω) := by rw [this, mul_one]
        _ = _ := by ring
    have hknown : 𝔼.E (t + 1) (P t * x (t + 1)) = P t * x (t + 1) := by
      rw [hpo _ _ _ (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hP t)), hx (t + 1)]
    have ih' : β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j)) =
        fun _ => ∏ u ∈ Finset.range j, (1 + i (t + 1 + u))⁻¹ := ih (t + 1)
    have hF' : β • 𝔼.E t (P t * x (t + 1)) = fun _ => (1 + i t)⁻¹ := by
      have := hF t
      simpa [bondPrice] using this
    have e1 : β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) = β • 𝔼.E t ((P t * x (t + 1)) *
        (β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j)))) := by
      rw [hsplit, ← 𝔼.tower (Nat.le_succ t) ((P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j))),
        hpo _ _ _ hknown, mul_smul_comm, map_smul, smul_smul, ← pow_succ']
    change β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) = _
    rw [e1, ih']
    set c : ℝ := ∏ u ∈ Finset.range j, (1 + i (t + 1 + u))⁻¹ with hc
    have h2 : (P t * x (t + 1)) * (fun _ => c) = c • (P t * x (t + 1)) := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h2, map_smul, smul_comm, hF']
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_range_succ', hc, add_zero]
    congr 1
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [show t + (u + 1) = t + 1 + u by omega]

/-- Cochrane (2023), §7.1, p. 214: the product of one-period discount factors along the announced
path is the forward-guidance bond price, `∏_{u<j}(1 + i_u)^{-1} = fgPrice r i T j`. -/
theorem prod_fgRate {r i : ℝ} (hr : -1 < r) (hi : -1 < i) (T j : ℕ) :
    ∏ u ∈ Finset.range j, (1 + fgRate r i T (0 + u))⁻¹ = fgPrice r i T j := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (1 + i) ≠ 0 := by linarith
  induction j with
  | zero => simp [fgPrice]
  | succ j ih =>
    rw [Finset.prod_range_succ, ih, zero_add]
    unfold fgPrice fgRate
    by_cases hj : j < T
    · simp only [hj, ↓reduceIte, min_eq_left (show j + 1 ≤ T by omega), min_eq_left hj.le,
        Nat.sub_eq_zero_of_le (show j + 1 ≤ T by omega), Nat.sub_eq_zero_of_le hj.le, pow_succ]
      field_simp
    · simp only [hj, ↓reduceIte, min_eq_right (show T ≤ j + 1 by omega),
        min_eq_right (show T ≤ j by omega), show j + 1 - T = j - T + 1 by omega, pow_succ]
      field_simp

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the bond-price display holds under
uncertainty**: with the announced path (`r` before `T`, `i` from `T` on) implemented and
`β = 1/(1+r)`, `Q_0^{(j)} = β^j E_0(P_0/P_j) = ((1+r)^{min(j,T)}(1+i)^{j−T})^{-1}` in every
state. -/
theorem stoch_fgPrice (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (j : ℕ) :
    bondPrice 𝔼 (1 + r)⁻¹ P x 0 j = fun _ => fgPrice r i T j := by
  rw [bondPrice_eq_prod 𝔼 hpo hP hx hPx hF j 0, prod_fgRate hr hi T j]

/-- Cochrane (2023), §7.1, pp. 214–215 (under uncertainty): **the expected path.** The book's
price path is the path of expected values of `1/P`: `E_0(1/P_j) = 1/fgPath(P_0)_j`, so `E_0(1/P_j)`
is flat until `T` and falls at the rate `(1+r)/(1+i)` afterwards. -/
theorem stoch_E0_path (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (j : ℕ) (ω : Ω) :
    𝔼.E 0 (x j) ω = (fgPath (P 0 ω) r i T j)⁻¹ := by
  have hP0 : P 0 ω ≠ 0 := fun h => by have := hPx 0 ω; rw [h, zero_mul] at this; simp at this
  have h1 : (1 + r) ≠ 0 := by linarith
  have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
  rw [bondPrice_eq 𝔼 hpo hP, fgPrice_eq_path hP0 hr hi] at hb
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
  have hβ : ((1 + r)⁻¹) ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero h1)
  have := mul_left_cancel₀ hβ hb
  rw [div_eq_mul_inv] at this
  exact mul_left_cancel₀ hP0 this

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): the Fisher relation with the announced path,
`E_t(P_t/P_{t+1}) = (1 + r)/(1 + i_t)`. -/
theorem stoch_expected_inflation {r i : ℝ} (hr : -1 < r) {T : ℕ} {P x : ℕ → Ω → ℝ}
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (t : ℕ) :
    𝔼.E t (P t * x (t + 1)) = fun _ => (1 + r) / (1 + fgRate r i T t) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have := hF t
  simp only [bondPrice, pow_one] at this
  funext ω
  have hω := congrFun this ω
  simp only [Pi.smul_apply, smul_eq_mul] at hω
  rw [div_eq_mul_inv, ← hω]
  field_simp

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **no predictable second jump**: up to and
including the date of the rate rise there is no expected price change,
`E_t(P_t/P_{t+1}) = 1` for every `t < T`; any change in the price level at `T` is news. -/
theorem stoch_no_expected_jump {r i : ℝ} (hr : -1 < r) {T : ℕ} {P x : ℕ → Ω → ℝ}
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) {t : ℕ} (ht : t < T) :
    𝔼.E t (P t * x (t + 1)) = fun _ => 1 := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [stoch_expected_inflation 𝔼 hr hF t]
  funext ω
  simp [fgRate, ht, div_self h1]

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **expected inflation starts when the rate
rises**: for `t ≥ T`, `E_t(P_t/P_{t+1}) = (1+r)/(1+i) < 1` when `−1 < r < i`. -/
theorem stoch_expected_inflation_after {r i : ℝ} (hr : -1 < r) (hri : r < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) {t : ℕ} (ht : T ≤ t)
    (ω : Ω) : 𝔼.E t (P t * x (t + 1)) ω = (1 + r) / (1 + i) ∧ (1 + r) / (1 + i) < 1 := by
  have hrate : fgRate r i T t = i := by simp [fgRate, show ¬ t < T by omega]
  rw [stoch_expected_inflation 𝔼 hr hF t, hrate]
  exact ⟨rfl, (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): **the valuation equation.** With
deterministic outstanding debt `B_{−1}^{(j)} = B_j` (none beyond maturity `k`) and the announced
path implemented, the date-0 present-value relation reads, state by state,
`(∑_{j≤k} Q_0^{(j)} B_{−1}^{(j)})/P_0 = E_0 ∑_j β^j s_j` with the book's bond prices. -/
theorem stoch_valuation (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0) (ω : Ω) :
    (∑ j ∈ Finset.range (k + 1), fgPrice r i T j * B j) / P 0 ω =
      pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω := by
  have hterm : ∀ j, debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x 0 j ω =
      x 0 ω * (fgPrice r i T j * B j) := by
    intro j
    have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
    rw [bondPrice_eq 𝔼 hpo hP] at hb
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
    simp only [debtTerm, zero_add]
    rw [← hb]
    have := hPx 0 ω
    linear_combination (-(B j * (1 + r)⁻¹ ^ j * 𝔼.E 0 (x j) ω)) * this
  have hfin : HasSum (fun j => debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x 0 j ω)
      (∑ j ∈ Finset.range (k + 1), x 0 ω * (fgPrice r i T j * B j)) := by
    simp only [hterm]
    exact hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [hBk j (by simpa using hj), mul_zero, mul_zero]
  have := (hpv ω).2.unique hfin
  rw [this, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  congr 1
  exact inv_eq_of_mul_eq_one_right (hPx 0 ω)

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): with a positive present value of
surpluses, `P_0 = priceLevel (fgPrice r i T) B k (E_0 ∑ β^j s_j)` state by state. -/
theorem stoch_priceLevel (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (hP0 : ∀ ω, 0 < P 0 ω)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) :
    P 0 ω = priceLevel (fgPrice r i T) B k (pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) :=
  (valuation_iff _ B k hS (hP0 ω)).mp (stoch_valuation 𝔼 hpo hr hi hBk hP hx hPx hF hpv ω)

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **guidance beyond the longest maturity
has no effect**: if `T ≥ k`, the equilibrium `P_0` with guidance equals the one without any rate
change, in every state (same surpluses and outstanding debt). -/
theorem stoch_fg_no_effect (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    (hkT : k ≤ T) {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω = P' 0 ω := by
  rw [stoch_priceLevel 𝔼 hpo hr hi hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hr hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_fg_of_le r i B hkT _

/-- Cochrane (2023), §7.1, pp. 213–214 (under uncertainty): **guidance within the
maturity structure lowers `P_0`**: if some maturity `j₀` with `T < j₀ ≤ k` is outstanding
(nonnegative positions, `r < i`), `P_0` with guidance is strictly below `P_0` without, in every
state. -/
theorem stoch_fg_lowers (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hri : r < i) {T k j₀ : ℕ}
    (hTj : T < j₀) (hjk : j₀ ≤ k) {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hBj : 0 < B j₀)
    (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω < P' 0 ω := by
  rw [stoch_priceLevel 𝔼 hpo hr (by linarith) hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hr hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_fg_lt hr hri hB hTj hjk hBj hS

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): **the effect of guidance falls with the
horizon**: with nonnegative positions, `P_0` under horizon `T` is at most `P_0` under horizon
`T' ≥ T`, in every state (`T = 0` is the immediate rise, the largest effect). -/
theorem stoch_fg_mono (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {T T' k : ℕ}
    (hTT' : T ≤ T') {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hBk : ∀ j, k < j → B j = 0)
    {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r i T'))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω ≤ P' 0 ω := by
  have hi : -1 < i := by linarith
  rw [stoch_priceLevel 𝔼 hpo hr hi hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hi hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_mono hr hri hB k hS hTT'

/-! ### Geometric maturity structure (Online Appendix A1.2.1) under uncertainty -/

/-- Cochrane (2023), Online Appendix p. 560 (under uncertainty): with a geometric
maturity structure `B_{−1}^{(j)} = ϖ^j B` (`0 ≤ ϖ < 1 + r`, `r ≤ i`) and the announced path
implemented,
the date-0 present-value relation reads `B (1/P_0) fgSum = E_0 ∑ β^j s_j`, state by state. -/
theorem stoch_geometric_value (hpo : 𝔼.PullOut) {r i om B : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hom0 : 0 ≤ om) (hom1 : om < 1 + r) {T : ℕ} {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x s 0) (ω : Ω) :
    B * x 0 ω * fgSum r i om T = pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω := by
  have hi : -1 < i := by linarith
  have hterm : ∀ j, debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x 0 j ω =
      B * x 0 ω * (fgPrice r i T j * om ^ j) := by
    intro j
    have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
    rw [bondPrice_eq 𝔼 hpo hP] at hb
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
    simp only [debtTerm, zero_add]
    rw [← hb]
    have := hPx 0 ω
    linear_combination (-(om ^ j * B * (1 + r)⁻¹ ^ j * 𝔼.E 0 (x j) ω)) * this
  have hs := (hasSum_fg_geometric hr hri hom0 hom1 T).mul_left (B * x 0 ω)
  simp only [← hterm] at hs
  exact hs.unique (hpv ω).2

/-- Cochrane (2023), Online Appendix p. 560 (under uncertainty): **the discrete
forward-guidance formula holds state by state.** Compare the equilibrium with guidance (rate `i`
from `T`) with the one without any rate change, same surpluses and geometric debt. Then in every
state `P_0/P − 1 = J_T = fgJump r i ϖ T`, the book's deterministic number. -/
theorem stoch_fg_jump (hpo : 𝔼.PullOut) {r i om B : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hom0 : 0 ≤ om) (hom1 : om < 1 + r) {T : ℕ} {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x' s 0) (ω : Ω)
    (hS : pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω ≠ 0) :
    P 0 ω / P' 0 ω - 1 = fgJump r i om T := by
  have hx0 : ∀ {P x : ℕ → Ω → ℝ}, (∀ t ω, P t ω * x t ω = 1) → (∀ ω, 0 < P 0 ω) →
      x 0 ω = 1 / P 0 ω := fun hPx hP0 => by
    rw [eq_div_iff (hP0 ω).ne', mul_comm]; exact hPx 0 ω
  have hfg := stoch_geometric_value 𝔼 hpo hr hri hom0 hom1 hP hx hPx hF hpv ω
  have hss := stoch_geometric_value 𝔼 hpo hr le_rfl hom0 hom1 hP' hx' hPx' hF' hpv' ω
  rw [hx0 hPx hP0, mul_one_div] at hfg
  rw [hx0 hPx' hP0', mul_one_div] at hss
  exact fg_jump_geometric hr hri hom1 (hP0' ω) (hP0 ω) T hss hfg hS

end Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quantitative easing with a separate Treasury and Fed, under uncertainty

Cochrane (2023), §7.6.1, pp. 229–232, equations (7.22)–(7.24).

In the book the path after the date-0 shock is perfect foresight ("I drop `E_0` in front of
`1/P_j`", p. 230), and "for a desired price-level path and a choice of one of monetary `M` or QE
purchases `B̃`, (7.23) gives us the other one". Here surpluses and price levels are random. The
Treasury keeps the geometric structure `ϖ^{j−t} B`, the QE purchases `B̃_0^{(j)}` are fixed at
date 0, and reserves `M_{t−1}^{(t)}` are chosen at `t − 1` (predetermined). At every `t ≥ 1` the
present-value relation is
`M_{t−1}^{(t)}/P_t + ∑_{j≥t} β^{j−t}(ϖ^{j−t}B + B̃_0^{(j)}) E_t(1/P_j) = E_t ∑_k β^k s_{t+k}`
(`QEPV`).

* `qe_iff`: given the price process, (7.23) determines the reserves state by state,
  `M_{t−1}^{(t)} = (E_t ∑ β^k s_{t+k} − V_t) P_t` with `V_t` the value of Treasury and QE bonds.
* `reserves_exist_iff`: **the reverse engineering under uncertainty.** Predetermined reserves
  supporting a given random price path exist (and are then unique, `reserves_unique`) if and only
  if `R_t = (E_t ∑ β^k s_{t+k} − V_t) P_t` is known at `t − 1` for every `t ≥ 1`. Under perfect
  foresight the condition is automatic, which is the book's statement
  (`perfectForesight_reserves_exist`).
* `innovation_form`: the content of (7.23) under uncertainty is an innovation restriction:
  `M_{t−1}^{(t)}(1/P_t − E_{t−1}(1/P_t)) = (news in the present value of surpluses) −
  (news in the value of Treasury and QE bonds)`. The central bank sets the expected path;
  fiscal news sets the surprises.
* `no_reserves_of_news`, `coin_no_reserves`: a price path known one period ahead (a
  deterministic one, say) cannot be supported when the present value of surpluses has news:
  with a coin-flip surplus shock and a deterministic desired price path there are no
  predetermined reserves at all.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): the present-value relation at `t` with
Treasury debt `ϖ^{j−t} B`, QE bonds `B̃_0^{(j)} = b j`, reserves `M_{t−1}^{(t)} = Mr t`:
`∑_k β^k (ϖ^k B + B̃_0^{(t+k)}) E_t(1/P_{t+k}) = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t`. -/
def QEPV (β om B : ℝ) (b Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) * 𝔼.E t (x (t + k)) ω))
    (pvSurplus 𝔼 β s t ω - Mr t ω * x t ω)

/-- Cochrane (2023), §7.6.1, p. 230: the reserves implied by (7.23) at `t`,
`R_t = (E_t ∑ β^k s_{t+k} − V_t)/(1/P_t)`, where `V_t` is the value of Treasury and QE bonds. -/
noncomputable def resv (β : ℝ) (V x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (pvSurplus 𝔼 β s t ω - V t ω) / x t ω

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): with `V_t` the (convergent) value of
Treasury and QE bonds and `1/P_t > 0`, the present-value relation at `t` holds if and only if the
reserves are `R_t`. -/
theorem qe_iff {β om B : ℝ} {b Mr x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) (t : ℕ) :
    QEPV 𝔼 β om B b Mr x s t ↔ Mr t = resv 𝔼 β V x s t := by
  constructor
  · intro h
    funext ω
    have := (h ω).unique (hV t ω)
    rw [resv, eq_div_iff (hx t ω).ne']
    linarith
  · intro h ω
    convert hV t ω using 1
    rw [h, resv]
    field_simp [(hx t ω).ne']
    ring

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): the reserves supporting a given random
price path, if any, are unique at every date `t ≥ 1`. -/
theorem reserves_unique {β om B : ℝ} {b Mr Mr' x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) (t : ℕ)
    (h : QEPV 𝔼 β om B b Mr x s t) (h' : QEPV 𝔼 β om B b Mr' x s t) : Mr t = Mr' t := by
  rw [(qe_iff 𝔼 hV hx t).mp h, (qe_iff 𝔼 hV hx t).mp h']

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): **reverse engineering of reserves.**
Given a random price path (`1/P > 0`) and the QE purchases, there are predetermined reserves
(`M_{t}^{(t+1)}` known at `t`) satisfying the present-value relation at every date `t ≥ 1` if
and only if the implied reserves `R_{t+1}` are known at `t` for every `t`. -/
theorem reserves_exist_iff {β om B : ℝ} {b x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) :
    (∃ Mr : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (Mr (t + 1)) = Mr (t + 1)) ∧
      ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) ↔
      ∀ t, 𝔼.E t (resv 𝔼 β V x s (t + 1)) = resv 𝔼 β V x s (t + 1) := by
  constructor
  · rintro ⟨Mr, hMr, hpv⟩ t
    rw [← (qe_iff 𝔼 hV hx (t + 1)).mp (hpv t)]
    exact hMr t
  · intro hR
    refine ⟨resv 𝔼 β V x s, hR, fun t => (qe_iff 𝔼 hV hx (t + 1)).mpr rfl⟩

/-- Cochrane (2023), §7.6.1, p. 230: **under perfect foresight (the book's case) the reserves
always exist**: for any positive price path and QE purchases, `M_{t−1}^{(t)} = R_t` satisfies
(7.23) at every `t ≥ 1`. -/
theorem perfectForesight_reserves_exist {β om B : ℝ} {b x s V : ℕ → Unit → ℝ}
    (hV : ∀ t u, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) u) *
      perfectForesight.E t (x (t + k)) u)) (V t u)) (hx : ∀ t u, 0 < x t u) :
    ∃ Mr : ℕ → Unit → ℝ, (∀ t, perfectForesight.E t (Mr (t + 1)) = Mr (t + 1)) ∧
      ∀ t, QEPV perfectForesight β om B b Mr x s (t + 1) :=
  (reserves_exist_iff perfectForesight hV hx).mpr fun _ => rfl

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **the innovation form.** With
predetermined reserves, `M_{t}^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1}))` equals the news in the present
value of surpluses minus the news in the value of Treasury and QE bonds. -/
theorem innovation_form (hpo : 𝔼.PullOut) {β om B : ℝ} {b Mr x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (t : ℕ) (hMr : 𝔼.E t (Mr (t + 1)) = Mr (t + 1))
    (h : QEPV 𝔼 β om B b Mr x s (t + 1)) :
    Mr (t + 1) * (x (t + 1) - 𝔼.E t (x (t + 1))) =
      (pvSurplus 𝔼 β s (t + 1) - 𝔼.E t (pvSurplus 𝔼 β s (t + 1))) -
        (V (t + 1) - 𝔼.E t (V (t + 1))) := by
  have hlev : Mr (t + 1) * x (t + 1) = pvSurplus 𝔼 β s (t + 1) - V (t + 1) := by
    funext ω
    have := (h ω).unique (hV (t + 1) ω)
    simp only [Pi.mul_apply, Pi.sub_apply]
    linarith
  have hE : Mr (t + 1) * 𝔼.E t (x (t + 1)) =
      𝔼.E t (pvSurplus 𝔼 β s (t + 1)) - 𝔼.E t (V (t + 1)) := by
    rw [← hpo t _ _ hMr, hlev, map_sub]
  rw [mul_sub, hlev, hE]
  ring

/-- Cochrane (2023), §7.6.1 (under uncertainty): **a price path known one period ahead cannot be
supported when the present value of surpluses has news.** If `1/P_{t+1}` and the bond value
`V_{t+1}` are known at `t` but `E_{t+1} ∑ β^k s_{t+1+k}` is not, no predetermined reserves satisfy
the present-value relation at `t + 1`. -/
theorem no_reserves_of_news (hpo : 𝔼.PullOut) {β om B : ℝ} {b x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (t : ℕ) (hxk : 𝔼.E t (x (t + 1)) = x (t + 1))
    (hVk : 𝔼.E t (V (t + 1)) = V (t + 1))
    (hnews : 𝔼.E t (pvSurplus 𝔼 β s (t + 1)) ≠ pvSurplus 𝔼 β s (t + 1)) :
    ¬ ∃ Mr : ℕ → Ω → ℝ, 𝔼.E t (Mr (t + 1)) = Mr (t + 1) ∧ QEPV 𝔼 β om B b Mr x s (t + 1) := by
  rintro ⟨Mr, hMr, h⟩
  have := innovation_form 𝔼 hpo hV t hMr h
  rw [hxk, sub_self, mul_zero, hVk, sub_self, sub_zero] at this
  exact hnews (sub_eq_zero.mp this.symm).symm

/-! ### A coin-flip surplus shock -/

/-- Cochrane (2023), §7.6.1 (illustration under uncertainty): surpluses `s_t = 1`, except a
fair coin-flip shock `±1` added at date 1 (revealed at date 1). -/
noncomputable def coinS : ℕ → Bool × Bool → ℝ :=
  fun t ω => 1 + if t = 1 then ExpectationsFiniteTree.coinShock 1 ω else 0

/-- Cochrane (2023), §7.6.1 (illustration): the present value of surpluses at date 1 is
`1/(1−β) + ε_1`, which carries the date-1 news `ε_1`. -/
theorem coin_pv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : Bool × Bool) :
    pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 ω =
      1 / (1 - β) + ExpectationsFiniteTree.coinShock 1 ω := by
  have hk1 : ExpectationsFiniteTree.coinSystem.E 1 (ExpectationsFiniteTree.coinShock 1) ω =
      ExpectationsFiniteTree.coinShock 1 ω := by
    rw [ExpectationsFiniteTree.coinSystem,
      ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
      ExpectationsFiniteTree.coinShock_measurable 1 h
  have hterm : ∀ k, surplusTerm ExpectationsFiniteTree.coinSystem β coinS 1 k ω =
      β ^ k * 1 + (Pi.single 0 (ExpectationsFiniteTree.coinShock 1 ω) : ℕ → ℝ) k := by
    intro k
    rcases k with _ | k
    · have hf : coinS (1 + 0) = (fun _ => (1 : ℝ)) + ExpectationsFiniteTree.coinShock 1 := by
        funext ω'; simp [coinS]
      simp only [surplusTerm, hf, map_add, ExpectationsFiniteTree.coinSystem.const, Pi.add_apply,
        hk1, pow_zero, one_mul, Pi.single_eq_same]
    · have hf : coinS (1 + (k + 1)) = fun _ => (1 : ℝ) := by
        funext ω'; simp [coinS]
      simp only [surplusTerm, hf, ExpectationsFiniteTree.coinSystem.const,
        Pi.single_eq_of_ne (show k + 1 ≠ 0 by omega), add_zero]
  have hs : HasSum (fun k => surplusTerm ExpectationsFiniteTree.coinSystem β coinS 1 k ω)
      (1 / (1 - β) + ExpectationsFiniteTree.coinShock 1 ω) := by
    simp only [hterm]
    have h := ((hasSum_geometric_of_lt_one hβ0 hβ1).mul_right 1).add
      (hasSum_pi_single 0 (ExpectationsFiniteTree.coinShock 1 ω))
    convert h using 1
    rw [mul_one, one_div]
  exact hs.tsum_eq

/-- Cochrane (2023), §7.6.1 (under uncertainty): **no reserves support a deterministic price path
when surpluses carry news.** In the coin-flip economy (`0 ≤ β < 1`), for any deterministic
path `1/P_t = p_t`, deterministic QE purchases and Treasury structure with a convergent
bond value, no reserves chosen at date 0 satisfy the present-value relation at date 1. -/
theorem coin_no_reserves {β om B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (p bq : ℕ → ℝ) {v : ℝ}
    (hv : HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + bq (1 + k)) * p (1 + k))) v) :
    ¬ ∃ Mr : ℕ → Bool × Bool → ℝ, ExpectationsFiniteTree.coinSystem.E 0 (Mr 1) = Mr 1 ∧
      QEPV ExpectationsFiniteTree.coinSystem β om B (fun j _ => bq j) Mr (fun t _ => p t)
        coinS 1 := by
  rintro ⟨Mr, hMr, h⟩
  have hc : ∀ (t : ℕ) (c : ℝ), ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun t c => ExpectationsFiniteTree.coinSystem.const t c
  -- the relation at date 1 pins the present value of surpluses to a date-0 known variable
  have hlev : ∀ ω, pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 ω = v + Mr 1 ω * p 1 := by
    intro ω
    have h1 := h ω
    simp only [hc] at h1
    have := h1.unique hv
    linarith
  have hfun : pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 =
      (fun _ => v) + p 1 • Mr 1 := by
    funext ω; rw [hlev ω]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hknown : ExpectationsFiniteTree.coinSystem.E 0
      (pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1) =
      pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 := by
    rw [hfun, map_add, map_smul, hc, hMr]
  -- but its date-0 forecast is `1/(1−β)` while its value after heads is `1/(1−β) + 1`
  have hpvfun : pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 =
      (fun _ => 1 / (1 - β)) + ExpectationsFiniteTree.coinShock 1 := by
    funext ω; rw [coin_pv hβ0 hβ1 ω]; rfl
  have hE0 := ExpectationsFiniteTree.coinShock_mean_zero 0
  rw [zero_add] at hE0
  rw [hpvfun, map_add, hc, hE0] at hknown
  have := congrFun hknown (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional expectations pass through absolutely convergent series

Cochrane (2023), §7.4, eq. (7.17), p. 225 (and every `E_t ∑` in the book).

`TidyR5RandomRow.theoremW_rowR` assumed `TidyR5RandomRow.SeriesExchange`: `E_t` passes through
absolutely convergent series of random variables. The question was whether a finitely additive
expectation system could violate it. It cannot: **`SeriesExchange` follows from the axioms of an
`ExpectationSystem`** (`seriesExchange`).

The reason is that `E_t` is linear and monotone on *all* random variables, unbounded ones
included. A finitely additive functional such as a Banach limit or a limit along a free
ultrafilter is defined only on bounded functions (or is infinite on some unbounded ones), so it is
not an `ExpectationSystem`. For a nonnegative series `F = ∑_n f_n` with tails `T_N`, the pointwise
bound (`tail_le_bound`)
`T_N ≤ ε + K h/(N+1) + F²/K`,
where `h` is the first index at which the tail falls below `ε`, together with linearity and
monotonicity, gives `E_t T_N → 0` (`E_tail_tendsto`). The two unbounded random variables `h` and
`F²` have finite expectations because `E_t` is defined on them.

Consequences: `theoremW_rowR'`, `price_formula_rowR'`, `formulaW_solves_rowR'` hold with no
interchange hypothesis, for every expectation system with the pull-out property.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange

open Filter Topology MaturityStructure GeneralFormula TidyR5RandomRow

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.4 (used for every `E_t ∑`): the tail `T_N = ∑_{n ≥ N} f_n` of a series of
random variables. -/
noncomputable def tailF (f : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ := fun ω => ∑' n, f (n + N) ω

/-- Cochrane (2023), §7.4: tails of a nonnegative convergent series decrease, `T_{N'} ≤ T_N` for
`N ≤ N'`. -/
theorem tailF_anti {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (ω : Ω) {N N' : ℕ} (h : N ≤ N') :
    tailF f N' ω ≤ tailF f N ω := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hs : Summable (fun n => f (n + N) ω) := (summable_nat_add_iff N).mpr (hfs ω)
  have := hs.sum_add_tsum_nat_add d
  simp only [tailF]
  rw [← this]
  have e : (fun n => f (n + d + N) ω) = fun n => f (n + (N + d)) ω := by
    funext n; congr 1; omega
  rw [← e]
  have : 0 ≤ ∑ i ∈ Finset.range d, f (i + N) ω := Finset.sum_nonneg fun i _ => hf0 _ ω
  linarith

/-- Cochrane (2023), §7.4: the tails of a series tend to zero at every state. -/
theorem tailF_tendsto (f : ℕ → Ω → ℝ) (ω : Ω) :
    Tendsto (fun N => tailF f N ω) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n => f n ω)

/-- Cochrane (2023), §7.4: tails are nonnegative for a nonnegative series. -/
theorem tailF_nonneg {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω) (N : ℕ) (ω : Ω) :
    0 ≤ tailF f N ω :=
  tsum_nonneg fun _ => hf0 _ ω

/-- Cochrane (2023), §7.4: the first index at which the tail is at most `ε`. -/
noncomputable def firstIdx (f : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  (sInf {M : ℕ | tailF f M ω ≤ ε} : ℕ)

/-- Cochrane (2023), §7.4: **the pointwise tail bound** `T_N ≤ ε + K h/(N+1) + F²/K` for `ε, K > 0`,
with `h` the first index at which the tail falls below `ε` and `F = T_0`. -/
theorem tail_le_bound {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) (N : ℕ)
    (ω : Ω) :
    tailF f N ω ≤ ε + K * (firstIdx f ε ω / (N + 1)) + tailF f 0 ω ^ 2 / K := by
  have hT0 := tailF_nonneg hf0 N ω
  have hh0 : 0 ≤ firstIdx f ε ω := Nat.cast_nonneg _
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hF2 : 0 ≤ tailF f 0 ω ^ 2 / K := div_nonneg (sq_nonneg _) hK.le
  by_cases h : tailF f N ω ≤ ε
  · have : 0 ≤ K * (firstIdx f ε ω / (N + 1)) := mul_nonneg hK.le (div_nonneg hh0 hN1.le)
    linarith
  · push Not at h
    have hne : {M : ℕ | tailF f M ω ≤ ε}.Nonempty := by
      obtain ⟨M, hM⟩ := ((tailF_tendsto f ω).eventually (ge_mem_nhds hε)).exists
      exact ⟨M, hM⟩
    have hlt : N < sInf {M : ℕ | tailF f M ω ≤ ε} := by
      by_contra hc
      push Not at hc
      have h1 := tailF_anti hf0 hfs ω hc
      have h2 : tailF f (sInf {M : ℕ | tailF f M ω ≤ ε}) ω ≤ ε := Nat.sInf_mem hne
      linarith
    have hge : 1 ≤ firstIdx f ε ω / (N + 1) := by
      rw [le_div_iff₀ hN1, one_mul, firstIdx]
      exact_mod_cast hlt
    have hTF : tailF f N ω ≤ tailF f 0 ω := tailF_anti hf0 hfs ω (Nat.zero_le N)
    have hK1 : K ≤ K * (firstIdx f ε ω / (N + 1)) := by nlinarith
    by_cases hFK : tailF f 0 ω ≤ K
    · linarith
    · push Not at hFK
      have : tailF f 0 ω ≤ tailF f 0 ω ^ 2 / K := by
        rw [le_div_iff₀ hK]; nlinarith
      nlinarith

/-- Cochrane (2023), §7.4: **expectations of the tails tend to zero**, for every expectation
system: `E_t T_N → 0` for a nonnegative series converging at every state. -/
theorem E_tail_tendsto {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => 𝔼.E t (tailF f N) ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  set a : ℝ := 𝔼.E t (firstIdx f η) ω with ha
  set c : ℝ := 𝔼.E t (fun ω' => tailF f 0 ω' ^ 2) ω with hc
  have hnn : ∀ g : Ω → ℝ, (∀ ω', 0 ≤ g ω') → 0 ≤ 𝔼.E t g ω := fun g hg => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ g from hg) ω
    rwa [𝔼.const] at this
  have ha0 : 0 ≤ a := hnn _ fun ω' => Nat.cast_nonneg _
  have hc0 : 0 ≤ c := hnn _ fun ω' => sq_nonneg _
  set K : ℝ := c / η + 1 with hK
  have hK0 : 0 < K := by positivity
  have hcK : c / K ≤ η := by
    rw [div_le_iff₀ hK0, hK]
    have : c = c / η * η := by field_simp
    nlinarith
  refine ⟨⌈K * a / η⌉₊, fun N hN => ?_⟩
  have hN' : K * a / η ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hKa : K * (a / (N + 1)) ≤ η := by
    rw [div_le_iff₀ hη0] at hN'
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hb : tailF f N ≤ (fun _ => η) + (K / (N + 1)) • firstIdx f η +
      (1 / K) • fun ω' => tailF f 0 ω' ^ 2 := fun ω' => by
    have := tail_le_bound hf0 hfs hη0 hK0 N ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc tailF f N ω' ≤ η + K * (firstIdx f η ω' / (N + 1)) + tailF f 0 ω' ^ 2 / K := this
      _ = _ := by ring
  have hup := 𝔼.mono t hb ω
  rw [map_add, map_add, map_smul, map_smul, 𝔼.const] at hup
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hup
  have hlo := hnn _ (tailF_nonneg hf0 N)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  have e1 : K / (N + 1) * a = K * (a / (N + 1)) := by ring
  have e2 : 1 / K * c = c / K := by ring
  rw [← ha, ← hc, e1, e2] at hup
  linarith

/-- Cochrane (2023), §7.4: **`E_t` passes through nonnegative series**, for every expectation
system: `∑_n E_t f_n = E_t ∑_n f_n`. -/
theorem hasSum_E_nonneg {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (t : ℕ) (ω : Ω) :
    HasSum (fun n => 𝔼.E t (f n) ω) (𝔼.E t (fun ω' => ∑' n, f n ω') ω) := by
  have hE0 : ∀ n, 0 ≤ 𝔼.E t (f n) ω := fun n => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ f n from fun ω' => hf0 n ω') ω
    rwa [𝔼.const] at this
  rw [hasSum_iff_tendsto_nat_of_nonneg hE0]
  have hpart : ∀ N, ∑ n ∈ Finset.range N, 𝔼.E t (f n) ω =
      𝔼.E t (fun ω' => ∑' n, f n ω') ω - 𝔼.E t (tailF f N) ω := by
    intro N
    have hfun : (fun ω' => ∑' n, f n ω') - tailF f N = ∑ n ∈ Finset.range N, f n := by
      funext ω'
      simp only [Pi.sub_apply, Finset.sum_apply, tailF]
      rw [← (hfs ω').sum_add_tsum_nat_add N]
      ring
    rw [← Pi.sub_apply, ← map_sub, hfun, map_sum, Finset.sum_apply]
  simp only [hpart]
  simpa using (tendsto_const_nhds (x := 𝔼.E t (fun ω' => ∑' n, f n ω') ω)).sub
    (E_tail_tendsto 𝔼 hf0 hfs t ω)

/-- Cochrane (2023), eq. (7.17), p. 225: **`SeriesExchange` is a theorem**: every expectation
system passes through absolutely convergent series of random variables. -/
theorem seriesExchange : SeriesExchange 𝔼 := by
  intro f hf t ω
  set fp : ℕ → Ω → ℝ := fun n ω' => max (f n ω') 0 with hfp
  set fm : ℕ → Ω → ℝ := fun n ω' => max (-f n ω') 0 with hfm
  have hp0 : ∀ n ω', 0 ≤ fp n ω' := fun n ω' => le_max_right _ _
  have hm0 : ∀ n ω', 0 ≤ fm n ω' := fun n ω' => le_max_right _ _
  have hps : ∀ ω', Summable (fun n => fp n ω') := fun ω' =>
    Summable.of_nonneg_of_le (fun n => hp0 n ω') (fun n => max_le (le_abs_self _)
      (abs_nonneg _)) (hf ω')
  have hms : ∀ ω', Summable (fun n => fm n ω') := fun ω' =>
    Summable.of_nonneg_of_le (fun n => hm0 n ω') (fun n => max_le (neg_le_abs _)
      (abs_nonneg _)) (hf ω')
  have hsplit : ∀ n, f n = fp n - fm n := fun n => by
    funext ω'
    simp only [hfp, hfm, Pi.sub_apply]
    rcases le_total 0 (f n ω') with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsum : (fun ω' => ∑' n, f n ω') =
      (fun ω' => ∑' n, fp n ω') - fun ω' => ∑' n, fm n ω' := by
    funext ω'
    simp only [Pi.sub_apply]
    rw [← (hps ω').tsum_sub (hms ω')]
    exact tsum_congr fun n => congrFun (hsplit n) ω'
  have h := (hasSum_E_nonneg 𝔼 hp0 hps t ω).sub (hasSum_E_nonneg 𝔼 hm0 hms t ω)
  rw [hsum, map_sub, Pi.sub_apply]
  refine h.congr_fun fun n => ?_
  rw [hsplit n, map_sub, Pi.sub_apply]

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: (7.17) solves the flow system under the
row condition with random bounds, for every expectation system with the pull-out property. -/
theorem formulaW_solves_rowR' (hpo : 𝔼.PullOut) {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t :=
  formulaW_solves_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 h hA hs hsb

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W with random bounds, with no interchange
hypothesis**: under the row condition with random bounds (`ρ < 1`), each `A_t^{(t+j+1)}` known at
`t + j` and bounded adapted surpluses, every bounded solution of (7.14) is the weighted present
value (7.17), for every expectation system with the pull-out property. -/
theorem theoremW_rowR' (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) :=
  theoremW_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 h hA hs hsb hy hyb t ω

/-- Cochrane (2023), eq. (7.17), p. 225: (7.17) for the price level with random bounds, with no
interchange hypothesis. -/
theorem price_formula_rowR' (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  price_formula_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 hD hDmm h hA hs hsb hflow hb t ω

end Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The innovation form of (7.12) at every date

Cochrane (2023), §7.3.2, p. 224 (the unnumbered innovation version of (7.12)), and §7.4,
eq. (7.17), p. 225.

`BondSales.dilution_formula` is (7.12) at date 0 and `BondSales.offset_shock` states its content at
date 0. Here (7.12) and its innovation form hold at every date `t`.

* `dilution_at`: **(7.12) at date `t₀`.** If the government trades at `t₀` (state-contingently)
  and never after,
  `B_{t₀−1}^{(t₀)}/P_{t₀} = s_{t₀} + ∑_{j≥1} β^j A_{t₀}^{(t₀+j)} E_{t₀} s_{t₀+j}` with
  `A_{t₀}^{(m)} = (B_{t₀}^{(m)} − B_{t₀−1}^{(m)})/B_{t₀}^{(m)}` (`fracNew`).
* `innovation_at`: **the innovation form at date `t + 1`**:
  `B_t^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) = ΔE_{t+1} s_{t+1} +
  ∑_j β^{j+1} [A E_{t+1} s_{t+1+j+1} − E_t(A s_{t+1+j+1})]`, a convergent series. The printed
  display
  mixes the dates `0` and `t` (E7.9); this is its corrected form at a general date.
* `no_surprise_iff`: there is no unexpected inflation at `t + 1` exactly when the surplus news is
  offset by the news in the dilution terms (the state-contingent sales).
* `innovation_rowR`: the innovation form of the general formula (7.17) at every date, for any
  sale policy under the row condition with random bounds:
  `y_{t+1} − E_t y_{t+1} = ∑_m β^m (E_{t+1} − E_t)(W_{t+1}^{(m)} s_{t+1+m})`.

The interchanges of `E_t` and the series use `TidyR5SeriesExchange.seriesExchange`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5InnovationForm

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise TidyR5RandomRow
  TidyR5SeriesExchange

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.3.2, p. 224: the government trades at date `t₀` and never after:
`B_u^{(m)} = B_{u−1}^{(m)}` for `t₀ < u < m`. -/
def NoSalesAfter (D : ℕ → ℕ → Ω → ℝ) (t₀ : ℕ) : Prop :=
  ∀ u m, t₀ < u → u < m → D (u + 1) m = D u m

/-- Cochrane (2023), eq. (7.12), p. 222 (at date `t₀`): the fraction of the date-`m` debt sold at
`t₀`, `A_{t₀}^{(m)} = (B_{t₀}^{(m)} − B_{t₀−1}^{(m)})/B_{t₀}^{(m)}`. -/
noncomputable def fracNew (D : ℕ → ℕ → Ω → ℝ) (t₀ m : ℕ) : Ω → ℝ :=
  (D (t₀ + 1) m - D t₀ m) / D (t₀ + 1) m

/-- Cochrane (2023), §7.3, p. 221 (at date `t₀`): after `t₀` the debt due at `m` is
`B_{t₀}^{(m)}`. -/
theorem debt_after {D : ℕ → ℕ → Ω → ℝ} {t₀ : ℕ} (h : NoSalesAfter D t₀) (m : ℕ) :
    ∀ k, t₀ + 1 + k ≤ m → D (t₀ + 1 + k) m = D (t₀ + 1) m := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [show t₀ + 1 + (k + 1) = t₀ + 1 + k + 1 by omega, h _ m (by omega) (by omega),
      ih (by omega)]

/-- Cochrane (2023), eq. (7.9), p. 221 (after date `t₀`): with no trading after `t₀`, each later
surplus pays off the debt maturing at its date, `B_{t₀}^{(u)}/P_u = s_u` for `u > t₀`. -/
theorem maturing_after {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t₀ : ℕ}
    (h : NoSalesAfter D t₀) {u : ℕ} (hu : t₀ < u) (hflow : RealFlow 𝔼 β D x s u) :
    D (t₀ + 1) u * x u = s u := by
  funext ω
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D u (u + (j + 1)) ω *
      𝔼.E u (x (u + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h u (u + (j + 1)) hu (by omega)]
  have h1 := hflow ω
  rw [hz] at h1
  have h2 := h1.unique hasSum_zero
  have hD : D u u = D (t₀ + 1) u := by
    have := debt_after h u (u - (t₀ + 1)) (by omega)
    rwa [show t₀ + 1 + (u - (t₀ + 1)) = u by omega] at this
  simp only [Pi.mul_apply]
  rw [← hD]
  linarith

/-- Cochrane (2023), eq. (7.12), p. 222, **at date `t₀`**: with trading at `t₀` only,
`B_{t₀−1}^{(t₀)}/P_{t₀} = s_{t₀} + ∑_{j≥0} β^{j+1} A_{t₀}^{(t₀+j+1)} E_{t₀} s_{t₀+j+1}`. -/
theorem dilution_at (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t₀ : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D t₀) (hflow : ∀ u, t₀ ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t₀ < m → D (t₀ + 1) m ω ≠ 0) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (fracNew D t₀ (t₀ + (j + 1)) ω *
      𝔼.E t₀ (s (t₀ + (j + 1))) ω)) (D t₀ t₀ ω * x t₀ ω - s t₀ ω) := by
  refine (hflow t₀ le_rfl ω).congr_fun fun j => ?_
  set m := t₀ + (j + 1) with hm
  have hx : x m = s m / D (t₀ + 1) m := by
    funext ω'
    have := congrFun (maturing_after 𝔼 h (show t₀ < m by omega) (hflow m (by omega))) ω'
    simp only [Pi.mul_apply] at this
    simp only [Pi.div_apply]
    rw [eq_div_iff (hD1 m ω' (by omega)), ← this, mul_comm]
  rw [hx, PolicyConstraints.E_div_known 𝔼 hpo hdc (hD.2 t₀ m)]
  simp only [sales, fracNew, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), §7.3.2, p. 224: the sale fractions `A_{t+1}^{(m)}` are known at `t + 1`. -/
theorem fracNew_known (hdc : PolicyConstraints.DivClosed 𝔼) {D : ℕ → ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (t₀ m : ℕ) : 𝔼.E t₀ (fracNew D t₀ m) = fracNew D t₀ m :=
  hdc t₀ _ _ (by rw [map_sub, hD.2 t₀ m, Predetermined.known 𝔼 hD le_rfl]) (hD.2 t₀ m)

/-- Cochrane (2023), §7.3.2, p. 224, **the innovation form of (7.12) at date `t + 1`** (corrected,
E7.9): with trading at `t + 1` only and an absolutely convergent dilution series,
`B_t^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) − (s_{t+1} − E_t s_{t+1}) =
∑_j β^{j+1} [A_{t+1}^{(m)} E_{t+1} s_m − E_t(A_{t+1}^{(m)} s_m)]` with `m = t + 1 + j + 1`. -/
theorem innovation_at (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D (t + 1)) (hflow : ∀ u, t + 1 ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t + 1 < m → D (t + 2) m ω ≠ 0)
    (habs : ∀ ω, Summable (fun j : ℕ => |β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω)|)) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
        𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω -
        𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω))
      (D (t + 1) (t + 1) ω * (x (t + 1) ω - 𝔼.E t (x (t + 1)) ω) -
        (s (t + 1) ω - 𝔼.E t (s (t + 1)) ω)) := by
  set g : ℕ → Ω → ℝ := fun j ω' => β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω' *
    𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω') with hg
  have hlev : ∀ ω', HasSum (fun j => g j ω')
      (D (t + 1) (t + 1) ω' * x (t + 1) ω' - s (t + 1) ω') := fun ω' =>
    dilution_at 𝔼 hpo hdc hD h hflow hD1 ω'
  have hex := seriesExchange 𝔼 g habs t ω
  have hsum : (fun ω' => ∑' j, g j ω') = D (t + 1) (t + 1) * x (t + 1) - s (t + 1) := by
    funext ω'; exact (hlev ω').tsum_eq
  rw [hsum, map_sub, hpo t _ _ (hD.2 t (t + 1))] at hex
  have hEg : ∀ j, 𝔼.E t (g j) ω = β ^ (j + 1) *
      𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω := by
    intro j
    have hk := fracNew_known 𝔼 hdc hD (t + 1) (t + 1 + (j + 1))
    rw [show g j = β ^ (j + 1) • (fracNew D (t + 1) (t + 1 + (j + 1)) *
      𝔼.E (t + 1) (s (t + 1 + (j + 1)))) from rfl, map_smul, ← hpo _ _ _ hk,
      𝔼.tower (Nat.le_succ t)]
    rfl
  have hd := (hlev ω).sub hex
  simp only [hEg] at hd
  convert hd using 1
  · funext j; simp only [hg]; ring
  · simp only [Pi.mul_apply, Pi.sub_apply]; ring

/-- Cochrane (2023), §7.3.2, p. 224 (bullet), at every date: **no unexpected inflation at
`t + 1` exactly when the surplus news is offset by the news in the dilution terms**: with
`B_t^{(t+1)} ≠ 0`, `1/P_{t+1} = E_t(1/P_{t+1})` iff
`s_{t+1} − E_t s_{t+1} + ∑_j β^{j+1}[A E_{t+1} s_m − E_t(A s_m)] = 0`. -/
theorem no_surprise_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D (t + 1)) (hflow : ∀ u, t + 1 ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t + 1 < m → D (t + 2) m ω ≠ 0)
    (habs : ∀ ω, Summable (fun j : ℕ => |β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω)|)) (ω : Ω) (hDt : D (t + 1) (t + 1) ω ≠ 0) :
    x (t + 1) ω = 𝔼.E t (x (t + 1)) ω ↔
      s (t + 1) ω - 𝔼.E t (s (t + 1)) ω + ∑' j : ℕ, β ^ (j + 1) *
        (fracNew D (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω -
          𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω) = 0 := by
  rw [(innovation_at 𝔼 hpo hdc hD h hflow hD1 habs ω).tsum_eq]
  constructor
  · intro hx; rw [hx]; ring
  · intro h0
    have : D (t + 1) (t + 1) ω * (x (t + 1) ω - 𝔼.E t (x (t + 1)) ω) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hDt
    · linarith

/-- Cochrane (2023), eq. (7.17), p. 225, **innovation form at every date for any sale policy**:
under the row condition with random bounds, for every bounded solution `y` of the flow system
(7.14), `y_{t+1} − E_t y_{t+1} = ∑_m β^m (E_{t+1}(W_{t+1}^{(m)} s_{t+1+m}) −
E_t(W_{t+1}^{(m)} s_{t+1+m}))`, a convergent series. -/
theorem innovation_rowR (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => β ^ m * (𝔼.E (t + 1) (weight A (t + 1) m * s (t + 1 + m)) ω -
        𝔼.E t (weight A (t + 1) m * s (t + 1 + m)) ω))
      (y (t + 1) ω - 𝔼.E t (y (t + 1)) ω) := by
  have hlev := fun ω' => theoremW_rowR' 𝔼 hpo hβ0 hρ1 h hA hs hsb hy hyb (t + 1) ω'
  -- absolute summability of the terms of (7.17) at each state
  have habs : ∀ ω', Summable (fun m => |formulaTerm 𝔼 β A s (t + 1) m ω'|) := by
    intro ω'
    have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0 ω')
    set g : ℕ → ℝ := fun m => β ^ m * 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' * M
      with hgdef
    have hEnn : ∀ m, 0 ≤ 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' := fun m => by
      have := 𝔼.mono (t + 1) (show (fun _ => (0 : ℝ)) ≤ fun ω'' => |weight A (t + 1) m ω''| from
        fun _ => abs_nonneg _) ω'
      rwa [𝔼.const] at this
    have hg0 : ∀ m, 0 ≤ g m := fun m => mul_nonneg (mul_nonneg (pow_nonneg hβ0 m) (hEnn m)) hM
    have hgN : ∀ N, ∑ m ∈ Finset.range N, g m ≤ 1 / (1 - ρ) * M := by
      intro N
      simp only [hgdef]
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hM
      have hle : (∑ m ∈ Finset.range N, β ^ m • fun ω'' => |weight A (t + 1) m ω''|) ≤
          fun _ => 1 / (1 - ρ) := fun ω'' => by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hw := weight_series_le hβ0 hρ1 h ω'' (t + 1)
        simp only [← weight_apply] at hw
        exact (hw.1.sum_le_tsum _ fun m _ => mul_nonneg (pow_nonneg hβ0 m)
          (abs_nonneg _)).trans hw.2
      have := 𝔼.mono (t + 1) hle ω'
      rw [𝔼.const, map_sum, Finset.sum_apply] at this
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
      (summable_of_sum_range_le hg0 hgN)
    rw [formulaTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    change _ ≤ β ^ m * 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' * M
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω').trans ?_) (pow_nonneg hβ0 m)
    have hle : (fun ω'' => |(weight A (t + 1) m * s (t + 1 + m)) ω''|) ≤
        M • fun ω'' => |weight A (t + 1) m ω''| := fun ω'' => by
      simp only [Pi.mul_apply, abs_mul, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hsb _ ω'') (abs_nonneg _)
    have := 𝔼.mono (t + 1) hle ω'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm M] at this
    exact this
  have hex := seriesExchange 𝔼 (fun m ω' => formulaTerm 𝔼 β A s (t + 1) m ω') habs t ω
  have hsum : (fun ω' => ∑' m, formulaTerm 𝔼 β A s (t + 1) m ω') = y (t + 1) := by
    funext ω'; exact (hlev ω').tsum_eq
  rw [hsum] at hex
  have hEt : ∀ m, 𝔼.E t (fun ω' => formulaTerm 𝔼 β A s (t + 1) m ω') ω =
      β ^ m * 𝔼.E t (weight A (t + 1) m * s (t + 1 + m)) ω := by
    intro m
    rw [show (fun ω' => formulaTerm 𝔼 β A s (t + 1) m ω') =
      β ^ m • 𝔼.E (t + 1) (weight A (t + 1) m * s (t + 1 + m)) from rfl, map_smul,
      𝔼.tower (Nat.le_succ t)]
    rfl
  simp only [hEt] at hex
  refine ((hlev ω).sub hex).congr_fun fun m => ?_
  simp only [formulaTerm]
  ring

end Cochrane.LongTermDebtDynamics.TidyR5InnovationForm

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quantitative easing reverse-engineered from reserves, under uncertainty

Cochrane (2023), §7.6.1, pp. 229–232, equation (7.23): "for a desired price-level path and a
choice of one of monetary `M` or QE purchases `B̃`, (7.23) gives us the other one". This module
treats the direction *given `M`, find `B̃`* under uncertainty. The QE purchases `B̃_0^{(j)}` are
chosen once, at date 0 (known at 0); reserves `M_{t−1}^{(t)}`, the price path and surpluses are
random.

Write `R_t = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t − V^T_t` for the value the QE bonds must carry
at `t` (`resid`, with `V^T_t` the value of Treasury debt) and
`c_t = (R_t − β E_t R_{t+1}) P_t` (`qeImplied`).

* `qe_split`: (7.23) at `t` holds iff the QE bonds are worth `R_t`.
* `qe_necessary`, `qe_unique`: if bounded date-0 purchases support the path, then
  `B̃_0^{(t)} = c_t` for every `t ≥ 1`: they are unique.
* `qe_sufficient`: conversely, if every `c_t` (`t ≥ 1`) is known at date 0, the purchases
  `B̃_0^{(t)} = c_t` satisfy (7.23) at every date `t ≥ 1`.
* `qe_exists_iff`: **the exact condition**: with bounded data and `1/P` bounded away from zero,
  bounded date-0 QE purchases supporting the path exist if and only if every `c_t` is known at
  date 0.
* `coin_no_qe`: **a date-0-fixed `B̃` cannot absorb later news**: with a coin-flip surplus shock at
  date 1, a deterministic desired price path and deterministic reserves, no bounded date-0 QE
  purchases exist.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5QEReverse

open Filter Topology MaturityStructure TidyR5QEUncertainty

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): the value the QE bonds must carry at
`t`, `R_t = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t − V^T_t`. -/
noncomputable def resid (β : ℝ) (VT Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => pvSurplus 𝔼 β s t ω - Mr t ω * x t ω - VT t ω

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): the implied QE purchases
`c_t = (R_t − β E_t R_{t+1})/(1/P_t)`. -/
noncomputable def qeImplied (β : ℝ) (VT Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (resid 𝔼 β VT Mr x s t - β • 𝔼.E t (resid 𝔼 β VT Mr x s (t + 1))) / x t

/-- Cochrane (2023), eq. (7.23), p. 230: given the value `V^T_t` of the Treasury's geometric debt,
the present-value relation at `t` holds iff the QE bonds are worth `R_t`,
`∑_k β^k B̃_0^{(t+k)} E_t(1/P_{t+k}) = R_t`. -/
theorem qe_split {β om B : ℝ} {b Mr x s VT : ℕ → Ω → ℝ}
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (t : ℕ) :
    QEPV 𝔼 β om B b Mr x s t ↔ ∀ ω, HasSum (fun k : ℕ => β ^ k * (b (t + k) ω *
      𝔼.E t (x (t + k)) ω)) (resid 𝔼 β VT Mr x s t ω) := by
  constructor
  · intro h ω
    refine ((h ω).sub (hT t ω)).congr_fun fun k => ?_
    ring
  · intro h ω
    have := (hT t ω).add (h ω)
    convert this using 1
    · funext k; ring
    · simp only [resid]; ring

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **necessity.** If bounded QE
purchases fixed at date 0 satisfy (7.23) at every date `t ≥ 1` (with `|1/P| ≤ K_x`), then
`B̃_0^{(t+1)}/P_{t+1} = R_{t+1} − β E_{t+1} R_{t+2}`. -/
theorem qe_necessary (hpo : 𝔼.PullOut) {β om B Kx Kb : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxb : ∀ t ω, |x t ω| ≤ Kx)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hb0 : ∀ j, 𝔼.E 0 (b j) = b j) (hbb : ∀ j ω, |b j ω| ≤ Kb)
    (hpv : ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) (t : ℕ) :
    b (t + 1) * x (t + 1) = resid 𝔼 β VT Mr x s (t + 1) -
      β • 𝔼.E (t + 1) (resid 𝔼 β VT Mr x s (t + 1 + 1)) := by
  have hq := fun v => (qe_split 𝔼 hT (v + 1)).mp (hpv v)
  have hbk : ∀ j v, 𝔼.E v (b j) = b j := fun j v => ForwardSolution.E_of_known 𝔼
    (Nat.zero_le v) (hb0 j)
  -- `E_{t+1} R_{t+2}` as a series
  set f : ℕ → Ω → ℝ := fun k ω' => β ^ k * (b (t + 1 + 1 + k) ω' *
    𝔼.E (t + 1 + 1) (x (t + 1 + 1 + k)) ω') with hf
  have hfb : ∀ k ω', |f k ω'| ≤ β ^ k * (Kb * Kx) := by
    intro k ω'
    rw [hf, abs_mul, abs_pow, abs_of_nonneg hβ0, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hbb _ ω') (𝔼.abs_E_le (hxb _) _ ω')
      (abs_nonneg _) ((abs_nonneg _).trans (hbb 0 ω'))) (pow_nonneg hβ0 k)
  have hRu1 : resid 𝔼 β VT Mr x s (t + 1 + 1) = fun ω' => ∑' k, f k ω' := by
    funext ω'; exact ((hq (t + 1)) ω').tsum_eq.symm
  have hEf : ∀ k, 𝔼.E (t + 1) (f k) = fun ω' => β ^ k * (b (t + 1 + 1 + k) ω' *
      𝔼.E (t + 1) (x (t + 1 + 1 + k)) ω') := by
    intro k
    rw [show f k = β ^ k • (b (t + 1 + 1 + k) * 𝔼.E (t + 1 + 1) (x (t + 1 + 1 + k))) from rfl,
      map_smul,
      hpo _ _ _ (hbk _ (t + 1)), 𝔼.tower (Nat.le_succ (t + 1))]
    rfl
  funext ω
  have hE := ForwardSolution.E_tsum_dom 𝔼 ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
    (Kb * Kx)) hfb (t + 1) ω
  rw [← hRu1] at hE
  simp only [hEf] at hE
  have hS := (hq t) ω
  have h0 := hS.summable.tsum_eq_zero_add
  rw [hS.tsum_eq] at h0
  simp only [pow_zero, one_mul, add_zero, hx (t + 1)] at h0
  have hshift : ∑' k, β ^ (k + 1) * (b (t + 1 + (k + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (k + 1))) ω) =
      β * 𝔼.E (t + 1) (resid 𝔼 β VT Mr x s (t + 1 + 1)) ω := by
    rw [hE, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show t + 1 + (k + 1) = t + 1 + 1 + k by omega, pow_succ]
    ring
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): bounded QE purchases fixed at date 0
that support a path are unique: two of them agree at every maturity `t ≥ 1`. -/
theorem qe_unique (hpo : 𝔼.PullOut) {β om B Kx Kb Kb' : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b b' Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxb : ∀ t ω, |x t ω| ≤ Kx)
    (hxpos : ∀ t ω, 0 < x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hb0 : ∀ j, 𝔼.E 0 (b j) = b j) (hbb : ∀ j ω, |b j ω| ≤ Kb)
    (hb0' : ∀ j, 𝔼.E 0 (b' j) = b' j) (hbb' : ∀ j ω, |b' j ω| ≤ Kb')
    (hpv : ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) (hpv' : ∀ t, QEPV 𝔼 β om B b' Mr x s (t + 1))
    (t : ℕ) : b (t + 1) = b' (t + 1) := by
  have h1 := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0 hbb hpv t
  have h2 := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0' hbb' hpv' t
  funext ω
  have := congrFun (h1.trans h2.symm) ω
  simp only [Pi.mul_apply] at this
  exact mul_right_cancel₀ (hxpos _ ω).ne' this

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **sufficiency.** If `R` is adapted and
bounded and every implied purchase `c_t` (`t ≥ 1`) is known at date 0, then the purchases
`B̃_0^{(t)} = c_t` satisfy (7.23) at every date `t ≥ 1`. -/
theorem qe_sufficient (hpo : 𝔼.PullOut) {β om B KR : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Mr x s VT : ℕ → Ω → ℝ} (hxpos : ∀ t ω, 0 < x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hRad : ∀ t, 𝔼.E t (resid 𝔼 β VT Mr x s t) = resid 𝔼 β VT Mr x s t)
    (hRb : ∀ t ω, |resid 𝔼 β VT Mr x s t ω| ≤ KR)
    (hc0 : ∀ t, 𝔼.E 0 (qeImplied 𝔼 β VT Mr x s (t + 1)) = qeImplied 𝔼 β VT Mr x s (t + 1))
    (t : ℕ) : QEPV 𝔼 β om B (qeImplied 𝔼 β VT Mr x s) Mr x s (t + 1) := by
  rw [qe_split 𝔼 hT]
  intro ω
  set u := t + 1 with hu
  set R := resid 𝔼 β VT Mr x s with hR
  set a : ℕ → ℝ := fun k => 𝔼.E u (R (u + k)) ω with ha
  have hcx : ∀ m, 1 ≤ m → qeImplied 𝔼 β VT Mr x s m * x m = R m - β • 𝔼.E m (R (m + 1)) := by
    intro m _
    funext ω'
    simp only [qeImplied, Pi.mul_apply, Pi.div_apply]
    exact div_mul_cancel₀ _ (hxpos m ω').ne'
  have hterm : ∀ k, β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω * 𝔼.E u (x (u + k)) ω) =
      β ^ k * a k - β ^ (k + 1) * a (k + 1) := by
    intro k
    have hk : 𝔼.E u (qeImplied 𝔼 β VT Mr x s (u + k)) = qeImplied 𝔼 β VT Mr x s (u + k) := by
      have := hc0 (t + k)
      rw [show t + k + 1 = u + k by omega] at this
      exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le u) this
    have h1 := congrFun (hpo u _ (x (u + k)) hk) ω
    simp only [Pi.mul_apply] at h1
    rw [← h1, hcx (u + k) (by omega), map_sub, map_smul, 𝔼.tower (show u ≤ u + k by omega)]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
    rw [show u + k + 1 = u + (k + 1) by omega, pow_succ]
    ring
  have hsumm : Summable (fun k : ℕ => β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω *
      𝔼.E u (x (u + k)) ω)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
      (KR + β * KR)) fun k => ?_
    rw [hterm, Real.norm_eq_abs]
    have h1 : |a k| ≤ KR := 𝔼.abs_E_le (hRb _) u ω
    have h2 : |a (k + 1)| ≤ KR := 𝔼.abs_E_le (hRb _) u ω
    rw [pow_succ, show β ^ k * a k - β ^ k * β * a (k + 1) = β ^ k * (a k - β * a (k + 1)) by
      ring, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (pow_nonneg hβ0 k)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hβ0)
  rw [hsumm.hasSum_iff_tendsto_nat]
  have hpart : ∀ N, ∑ k ∈ Finset.range N, β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω *
      𝔼.E u (x (u + k)) ω) = R u ω - β ^ N * a N := by
    intro N
    simp only [hterm]
    rw [Finset.sum_range_sub' (fun k => β ^ k * a k) N]
    simp only [ha, pow_zero, one_mul, add_zero, hRad u]
  simp only [hpart]
  have hlim : Tendsto (fun N : ℕ => β ^ N * a N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const KR)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 N)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb _) u ω) (pow_nonneg hβ0 N)
  simpa using (tendsto_const_nhds (x := R u ω)).sub hlim

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): **the exact condition for reverse
engineering QE from reserves.** With `1/P` adapted, bounded and bounded away from zero, and `R`
adapted and bounded, bounded QE purchases fixed at date 0 that satisfy (7.23) at every date
`t ≥ 1` exist if and only if every implied purchase `c_t` (`t ≥ 1`) is known at date 0. -/
theorem qe_exists_iff (hpo : 𝔼.PullOut) {β om B Kx KR xmin : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hxmin : 0 < xmin) {Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (hxb : ∀ t ω, |x t ω| ≤ Kx) (hxlo : ∀ t ω, xmin ≤ x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hRad : ∀ t, 𝔼.E t (resid 𝔼 β VT Mr x s t) = resid 𝔼 β VT Mr x s t)
    (hRb : ∀ t ω, |resid 𝔼 β VT Mr x s t ω| ≤ KR) :
    (∃ b : ℕ → Ω → ℝ, (∀ j, 𝔼.E 0 (b j) = b j) ∧ (∃ Kb, ∀ j ω, |b j ω| ≤ Kb) ∧
      ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) ↔
      ∀ t, 𝔼.E 0 (qeImplied 𝔼 β VT Mr x s (t + 1)) = qeImplied 𝔼 β VT Mr x s (t + 1) := by
  have hxpos : ∀ t ω, 0 < x t ω := fun t ω => hxmin.trans_le (hxlo t ω)
  constructor
  · rintro ⟨b, hb0, ⟨Kb, hbb⟩, hpv⟩ t
    have h := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0 hbb hpv t
    have hc : qeImplied 𝔼 β VT Mr x s (t + 1) = b (t + 1) := by
      funext ω
      have := congrFun h ω
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply] at this
      simp only [qeImplied, Pi.div_apply, Pi.sub_apply, Pi.smul_apply]
      rw [div_eq_iff (hxpos _ ω).ne', ← this]
    rw [hc]; exact hb0 _
  · intro hc0
    set b : ℕ → Ω → ℝ := fun j => if j = 0 then 0 else qeImplied 𝔼 β VT Mr x s j with hbdef
    refine ⟨b, fun j => ?_, ⟨(KR + β * KR) / xmin, fun j ω => ?_⟩, fun t ω => ?_⟩
    · rcases j with _ | j
      · simp only [hbdef, ↓reduceIte, map_zero]
      · simp only [hbdef, Nat.add_one_ne_zero, ↓reduceIte]; exact hc0 j
    · rcases j with _ | j
      · simp only [hbdef, ↓reduceIte, Pi.zero_apply, abs_zero]
        exact div_nonneg (add_nonneg ((abs_nonneg _).trans (hRb 0 ω))
          (mul_nonneg hβ0 ((abs_nonneg _).trans (hRb 0 ω)))) hxmin.le
      · simp only [hbdef, Nat.add_one_ne_zero, ↓reduceIte, qeImplied, Pi.div_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [abs_div, abs_of_pos (hxpos _ ω)]
        have hKR : 0 ≤ KR := (abs_nonneg _).trans (hRb 0 ω)
        have hK0 : 0 ≤ KR + β * KR := add_nonneg hKR (mul_nonneg hβ0 hKR)
        refine div_le_div₀ hK0 ?_ hxmin (hxlo _ ω)
        refine (abs_sub _ _).trans (add_le_add (hRb _ ω) ?_)
        rw [abs_mul, abs_of_nonneg hβ0]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb _) _ ω) hβ0
    · have h := qe_sufficient 𝔼 hpo hβ0 hβ1 hxpos hT hRad hRb hc0 t ω
      convert h using 2 with k
      simp only [hbdef, show t + 1 + k ≠ 0 by omega, ↓reduceIte]

/-! ### A date-0 QE policy cannot absorb later news -/

/-- Cochrane (2023), §7.6.1 (illustration): in the coin-flip economy the present value of
surpluses from date 2 on is `1/(1−β)` in every state (the shock is at date 1). -/
theorem coin_pv_two {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : Bool × Bool) :
    pvSurplus ExpectationsFiniteTree.coinSystem β coinS 2 ω = 1 / (1 - β) := by
  have hterm : ∀ k, surplusTerm ExpectationsFiniteTree.coinSystem β coinS 2 k ω = β ^ k := by
    intro k
    have hf : coinS (2 + k) = fun _ => (1 : ℝ) := by
      funext ω'; simp [coinS, show ¬ (2 + k = 1) by omega]
    simp only [surplusTerm, hf, ExpectationsFiniteTree.coinSystem.const, mul_one]
  rw [pvSurplus]
  simp only [hterm]
  rw [tsum_geometric_of_lt_one hβ0 hβ1, one_div]

/-- Cochrane (2023), §7.6.1 (under uncertainty): **a date-0-fixed QE policy cannot absorb later
news.** In the coin-flip economy (`0 ≤ β < 1`, surplus shock at date 1), for any bounded
deterministic desired path `1/P_t = p_t`, deterministic reserves `M_{t−1}^{(t)} = m_t` and a
convergent Treasury value, no bounded QE purchases fixed at date 0 satisfy (7.23) at every
`t ≥ 1`. -/
theorem coin_no_qe {β om B Kx : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (p m vt : ℕ → ℝ)
    (hpb : ∀ t, |p t| ≤ Kx)
    (hvt : ∀ t, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * p (t + k))) (vt t)) :
    ¬ ∃ b : ℕ → Bool × Bool → ℝ, (∀ j, ExpectationsFiniteTree.coinSystem.E 0 (b j) = b j) ∧
      (∃ Kb, ∀ j ω, |b j ω| ≤ Kb) ∧
      ∀ t, QEPV ExpectationsFiniteTree.coinSystem β om B b (fun t _ => m t) (fun t _ => p t)
        coinS (t + 1) := by
  rintro ⟨b, hb0, ⟨Kb, hbb⟩, hpv⟩
  have hc : ∀ (t : ℕ) (c : ℝ), ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun t c => ExpectationsFiniteTree.coinSystem.const t c
  have hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B *
      ExpectationsFiniteTree.coinSystem.E t ((fun t _ => p t) (t + k)) ω)) (vt t) := by
    intro t ω
    simp only [hc]
    exact hvt t
  have h := qe_necessary ExpectationsFiniteTree.coinSystem
    (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) hβ0 hβ1
    (x := fun t _ => p t)
    (VT := fun t _ => vt t) (fun t => hc t (p t)) (fun t _ => hpb t) hT hb0 hbb hpv 0
  -- the date-2 residual is a constant
  have hR2 : resid ExpectationsFiniteTree.coinSystem β (fun t _ => vt t) (fun t _ => m t)
      (fun t _ => p t) coinS 2 = fun _ => 1 / (1 - β) - m 2 * p 2 - vt 2 := by
    funext ω; simp only [resid, coin_pv_two hβ0 hβ1 ω]
  rw [hR2, hc] at h
  -- so `b_1 p_1 = 1/(1−β) + ε_1 − const`, which is not known at date 0
  have hfun : b 1 * (fun _ => p 1) = (fun _ => 1 / (1 - β) - m 1 * p 1 - vt 1 -
      β * (1 / (1 - β) - m 2 * p 2 - vt 2)) + ExpectationsFiniteTree.coinShock 1 := by
    rw [h]
    funext ω
    simp only [resid, coin_pv hβ0 hβ1 ω, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    ring
  have hpo : ExpectationsFiniteTree.coinSystem.PullOut :=
    ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree
  have hknown : ExpectationsFiniteTree.coinSystem.E 0 (b 1 * fun _ => p 1) =
      b 1 * fun _ => p 1 := by
    rw [mul_comm, hpo 0 _ _ (hc 0 (p 1)), hb0 1]
  have hE0 := ExpectationsFiniteTree.coinShock_mean_zero 0
  rw [zero_add] at hE0
  rw [hfun, map_add, hc, hE0] at hknown
  have := congrFun hknown (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.LongTermDebtDynamics.TidyR5QEReverse

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Forward guidance with a state-contingent rate path

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214).

The module TidyR5GuidanceUncertainty treats an announced rate path known at date 0. Here the
announced one-period rate `i_t` may be random (known at `t`, state-contingent guidance),
implemented through
`Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` (`RFisher`).

* `bondPrice_succ_eq`, `bondPrice_cov`, `bondPrice_cov_rate`: **the bond-price recursion with the
  covariance term explicit**:
  `Q_t^{(t+j+1)} = (1 + i_t)^{-1} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`.
  With a known rate path the covariance vanishes and the book's display follows
  (`TidyR5GuidanceUncertainty.bondPrice_eq_prod`); with random rates the bond price also differs
  from `E_t ∏ (1 + i)^{-1}` by convexity.
* `random_valuation`: (7.3) under uncertainty with random bond prices,
  `(∑_j Q_0^{(j)} B_{−1}^{(j)})/P_0 = E_0 ∑ β^j s_j`.
* **What survives.** `bondPrice_prefix`, `random_fg_no_effect`: if the rates before `T` are
  unchanged (`i_t = r`), bonds maturing by `T` keep their prices and guidance beyond the longest
  maturity (`T ≥ k`) has no effect on `P_0`, however random the later rates.
  `random_expected_ratio`, `random_no_expected_jump`: `E_t(P_t/P_{t+1}) = (1+r)/(1+i_t)` state by
  state; there is no expected jump where the rate is unchanged.
* **What fails.** `cg_counterexample`: "an announced rate rise lowers `P_0`" is false for
  state-contingent guidance. In a coin-flip economy the announced rate at date 1 is `2` or
  `1/5` (mean `11/10`, above `r = 1`) and `r` at every other date; with the same debt and
  surpluses the price level is `P_0 = 7/48` against `1/8` with no announcement: guidance with a
  higher expected rate path *raises* `P_0`. The bond price `Q_0^{(2)} = 7/24` exceeds `1/4`:
  `E_0 (1+i_1)^{-1} > (1 + E_0 i_1)^{-1}` (Jensen). The comparative statics of §7.1
  (`ForwardGuidance.priceLevel_fg_lt`, `ForwardGuidance.priceLevel_mono`,
  `ForwardGuidance.priceLevel_immediate_le`) are statements about the rate *path*; they extend to
  known paths (module TidyR5GuidanceUncertainty) but not to the expected path of random rates.

As in the book's §7.1 analysis, an equilibrium here means the Fisher relations at every date and
the date-0 valuation equation (7.3) (`MaturityStructure.PresentValue` at date 0).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance

open Filter Topology MaturityStructure ForwardGuidance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1 (under uncertainty): the conditional covariance
`Cov_t(a, b) = E_t(ab) − E_t a E_t b`. -/
noncomputable def condCov (t : ℕ) (a b : Ω → ℝ) : Ω → ℝ :=
  𝔼.E t (a * b) - 𝔼.E t a * 𝔼.E t b

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): a state-contingent announced rate path
`i_t` (known at `t`) is implemented: `Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)`. -/
def RFisher (β : ℝ) (P x : ℕ → Ω → ℝ) (i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, bondPrice 𝔼 β P x t 1 = fun ω => (1 + i t ω)⁻¹

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): the bond-price recursion
`Q_t^{(t+j+1)} = E_t[(β P_t/P_{t+1}) Q_{t+1}^{(t+j+1)}]`. -/
theorem bondPrice_succ_eq (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) =
      𝔼.E t ((β • (P t * x (t + 1))) * bondPrice 𝔼 β P x (t + 1) j) := by
  have hsplit : P t * x (t + (j + 1)) = (P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j)) := by
    funext ω
    simp only [Pi.mul_apply]
    rw [show t + 1 + j = t + (j + 1) by omega]
    have := hPx (t + 1) ω
    calc P t ω * x (t + (j + 1)) ω =
        P t ω * x (t + (j + 1)) ω * (P (t + 1) ω * x (t + 1) ω) := by rw [this, mul_one]
      _ = _ := by ring
  have hknown : 𝔼.E (t + 1) (P t * x (t + 1)) = P t * x (t + 1) := by
    rw [hpo _ _ _ (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hP t)), hx (t + 1)]
  change β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) =
    𝔼.E t ((β • (P t * x (t + 1))) * (β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j))))
  rw [hsplit, ← 𝔼.tower (Nat.le_succ t) ((P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j))),
    hpo _ _ _ hknown, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_smul, ← pow_succ']

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the covariance decomposition**,
`Q_t^{(t+j+1)} = Q_t^{(t+1)} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`. -/
theorem bondPrice_cov (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) = bondPrice 𝔼 β P x t 1 * 𝔼.E t (bondPrice 𝔼 β P x (t + 1) j) +
      condCov 𝔼 t (β • (P t * x (t + 1))) (bondPrice 𝔼 β P x (t + 1) j) := by
  rw [bondPrice_succ_eq 𝔼 hpo hP hx hPx, condCov]
  have h1 : bondPrice 𝔼 β P x t 1 = 𝔼.E t (β • (P t * x (t + 1))) := by
    rw [map_smul]; simp [bondPrice]
  rw [h1]
  ring

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): with a state-contingent rate path,
`Q_t^{(t+j+1)} = (1 + i_t)^{-1} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`. -/
theorem bondPrice_cov_rate (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : RFisher 𝔼 β P x i) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) = (fun ω => (1 + i t ω)⁻¹) *
      𝔼.E t (bondPrice 𝔼 β P x (t + 1) j) +
      condCov 𝔼 t (β • (P t * x (t + 1))) (bondPrice 𝔼 β P x (t + 1) j) := by
  rw [bondPrice_cov 𝔼 hpo hP hx hPx, hF t]

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **bonds maturing by `T` are unaffected**:
if the rate is the known `r` at every date before `T`, then
`Q_t^{(t+j)} = (1+r)^{-j}` whenever `t + j ≤ T`, whatever the rates from `T` on. -/
theorem bondPrice_prefix (hpo : 𝔼.PullOut) {β r : ℝ} {P x : ℕ → Ω → ℝ} {T : ℕ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : ∀ t, t < T → bondPrice 𝔼 β P x t 1 = fun _ => (1 + r)⁻¹) (j : ℕ) :
    ∀ t, t + j ≤ T → bondPrice 𝔼 β P x t j = fun _ => ((1 + r)⁻¹) ^ j := by
  induction j with
  | zero =>
    intro t _
    have h1 : P t * x (t + 0) = fun _ => (1 : ℝ) := funext fun ω => by simpa using hPx t ω
    simp only [bondPrice, pow_zero, one_smul, h1, 𝔼.const]
  | succ j ih =>
    intro t ht
    rw [bondPrice_succ_eq 𝔼 hpo hP hx hPx, ih (t + 1) (by omega)]
    have h2 : (β • (P t * x (t + 1))) * (fun _ => ((1 + r)⁻¹) ^ j) =
        ((1 + r)⁻¹) ^ j • (β • (P t * x (t + 1))) := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : 𝔼.E t (β • (P t * x (t + 1))) = fun _ => (1 + r)⁻¹ := by
      rw [map_smul]
      have := hF t (by omega)
      simpa [bondPrice] using this
    rw [h2, map_smul, h3]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): **the valuation equation with random
bond prices.** With deterministic outstanding debt `B_j` (none beyond `k`), in every state
`(∑_{j≤k} Q_0^{(j)} B_j)/P_0 = E_0 ∑ β^j s_j`. -/
theorem random_valuation (hpo : 𝔼.PullOut) {β : ℝ} {k : ℕ} {B : ℕ → ℝ}
    (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hpv : PresentValue 𝔼 β (fun _ j _ => B j) x s 0)
    (ω : Ω) :
    (∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P x 0 j ω * B j) / P 0 ω =
      pvSurplus 𝔼 β s 0 ω := by
  have hterm : ∀ j, debtTerm 𝔼 β (fun _ j _ => B j) x 0 j ω =
      x 0 ω * (bondPrice 𝔼 β P x 0 j ω * B j) := by
    intro j
    rw [bondPrice_eq 𝔼 hpo hP]
    simp only [debtTerm, zero_add, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have := hPx 0 ω
    linear_combination (-(B j * β ^ j * 𝔼.E 0 (x j) ω)) * this
  have hfin : HasSum (fun j => debtTerm 𝔼 β (fun _ j _ => B j) x 0 j ω)
      (∑ j ∈ Finset.range (k + 1), x 0 ω * (bondPrice 𝔼 β P x 0 j ω * B j)) := by
    simp only [hterm]
    exact hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [hBk j (by simpa using hj), mul_zero, mul_zero]
  rw [(hpv ω).2.unique hfin, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  congr 1
  exact inv_eq_of_mul_eq_one_right (hPx 0 ω)

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **guidance beyond the longest maturity has
no effect, even when it is state-contingent**: if the rates before `T ≥ k` are the known `r` in
both equilibria (rates from `T` on arbitrary and random in the first), `P_0` is the same in every
state with a nonzero present value of surpluses. -/
theorem random_fg_no_effect (hpo : 𝔼.PullOut) {β r : ℝ} {T k : ℕ} (hkT : k ≤ T) {B : ℕ → ℝ}
    (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : ∀ t, t < T → bondPrice 𝔼 β P x t 1 = fun _ => (1 + r)⁻¹)
    (hpv : PresentValue 𝔼 β (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hF' : ∀ t, t < T → bondPrice 𝔼 β P' x' t 1 = fun _ => (1 + r)⁻¹)
    (hpv' : PresentValue 𝔼 β (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : pvSurplus 𝔼 β s 0 ω ≠ 0) : P 0 ω = P' 0 ω := by
  have h1 := random_valuation 𝔼 hpo hBk hP hPx hpv ω
  have h2 := random_valuation 𝔼 hpo hBk hP' hPx' hpv' ω
  have hsame : ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P x 0 j ω * B j =
      ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P' x' 0 j ω * B j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT : 0 + j ≤ T := by have := Finset.mem_range.mp hj; omega
    rw [bondPrice_prefix 𝔼 hpo hP hx hPx hF j 0 hjT,
      bondPrice_prefix 𝔼 hpo hP' hx' hPx' hF' j 0 hjT]
  rw [hsame] at h1
  have hA : ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P' x' 0 j ω * B j ≠ 0 := by
    intro h0; rw [h0, zero_div] at h2; exact hS h2.symm
  have hP0 : P 0 ω ≠ 0 := fun h => by have := hPx 0 ω; rw [h, zero_mul] at this; simp at this
  have hP0' : P' 0 ω ≠ 0 := fun h => by
    have := hPx' 0 ω; rw [h, zero_mul] at this; simp at this
  have h3 := h1.trans h2.symm
  rw [div_eq_div_iff hP0 hP0'] at h3
  exact (mul_left_cancel₀ hA h3).symm

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): with a state-contingent rate path and
`β = 1/(1+r)`, `E_t(P_t/P_{t+1}) = (1 + r)/(1 + i_t)` in every state. -/
theorem random_expected_ratio {r : ℝ} (hr : -1 < r) {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hF : RFisher 𝔼 (1 + r)⁻¹ P x i) (t : ℕ) (ω : Ω) :
    𝔼.E t (P t * x (t + 1)) ω = (1 + r) / (1 + i t ω) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have := congrFun (hF t) ω
  simp only [bondPrice, pow_one, Pi.smul_apply, smul_eq_mul] at this
  rw [div_eq_mul_inv, ← this]
  field_simp

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **no expected jump where the rate is
unchanged**: if `i_t = r` in state `ω`, then `E_t(P_t/P_{t+1}) = 1` there. -/
theorem random_no_expected_jump {r : ℝ} (hr : -1 < r) {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hF : RFisher 𝔼 (1 + r)⁻¹ P x i) {t : ℕ} {ω : Ω} (hi : i t ω = r) :
    𝔼.E t (P t * x (t + 1)) ω = 1 := by
  rw [random_expected_ratio 𝔼 hr hF t ω, hi, div_self (by linarith)]

/-! ### The counterexample: state-contingent guidance can raise `P_0` -/

/-- Cochrane (2023), §7.1 (counterexample): the announced rates, `r = 1` at every date except
date 1, where the rate is `2` after heads and `1/5` after tails (mean `11/10`). -/
noncomputable def cgRate : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t = 1 then (if ω.1 then 2 else 1 / 5) else 1

/-- Cochrane (2023), §7.1 (counterexample): `1/P_t`: `48/7` at dates 0 and 1, then `32/7` after
heads and `80/7` after tails. -/
noncomputable def cgX : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t ≤ 1 then 48 / 7 else (if ω.1 then 32 / 7 else 80 / 7)

/-- Cochrane (2023), §7.1 (counterexample): the price level `P_t = 1/cgX`. -/
noncomputable def cgP : ℕ → Bool × Bool → ℝ := fun t ω => (cgX t ω)⁻¹

/-- Cochrane (2023), §7.1 (counterexample): `1/P'_t = 8`, the path with no announcement. -/
noncomputable def cgX' : ℕ → Bool × Bool → ℝ := fun _ _ => 8

/-- Cochrane (2023), §7.1 (counterexample): `P'_t = 1/8`. -/
noncomputable def cgP' : ℕ → Bool × Bool → ℝ := fun _ _ => 1 / 8

/-- Cochrane (2023), §7.1 (counterexample): one unit of debt due at date 2, nothing else. -/
noncomputable def cgB : ℕ → ℝ := fun j => if j = 2 then 1 else 0

/-- Cochrane (2023), §7.1 (counterexample): in the coin-flip tree, `E_0` averages the four
states. -/
theorem coin_E0 (f : Bool × Bool → ℝ) (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 f ω =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  have htriv : ∀ a b, ExpectationsFiniteTree.coinTree.info 0 a b := fun a b => by
    change Setoid.ker (ExpectationsFiniteTree.coinObs 0) a b
    rw [Setoid.ker_def]
    simp [ExpectationsFiniteTree.coinObs]
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.coinTree.condE_of_trivial htriv]
  simp [ExpectationsFiniteTree.coinTree, Fintype.sum_prod_type]
  ring

/-- Cochrane (2023), §7.1 (counterexample): from date 1 on, a variable that depends only on the
first flip is known. -/
theorem coin_known {f : Bool × Bool → ℝ} (hf : ∀ ω ω', ω.1 = ω'.1 → f ω = f ω') {t : ℕ}
    (ht : 1 ≤ t) : ExpectationsFiniteTree.coinSystem.E t f = f := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => hf _ _ ?_
  change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
  exact h.1

/-- Cochrane (2023), §7.1 (counterexample): the guidance path is adapted. -/
theorem cg_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgX := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgX 0 = fun _ => 48 / 7 := by funext ω; simp [cgX]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgX, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the guidance price level is adapted. -/
theorem cgP_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgP := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgP 0 = fun _ => 7 / 48 := by funext ω; simp [cgP, cgX]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgP, cgX, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): **the guidance path implements the state-contingent
rates**: `Q_t^{(t+1)} = (1/2) E_t(P_t/P_{t+1}) = 1/(1 + i_t)` at every date (`r = 1`, `β = 1/2`). -/
theorem cg_fisher : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX cgRate := by
  intro t
  rcases Nat.lt_or_ge t 1 with h0 | h1
  · obtain rfl : t = 0 := by omega
    have : cgP 0 * cgX (0 + 1) = fun _ => 1 := by funext ω; simp [cgP, cgX]
    simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
    funext ω; simp [cgRate]
  · rcases Nat.lt_or_ge t 2 with h2 | h2
    · obtain rfl : t = 1 := by omega
      have hk : ExpectationsFiniteTree.coinSystem.E 1 (cgP 1 * cgX (1 + 1)) =
          cgP 1 * cgX (1 + 1) :=
        coin_known (fun ω ω' h => by simp only [Pi.mul_apply, cgP, cgX, h]) le_rfl
      simp only [bondPrice, pow_one, hk]
      funext ω
      rcases ω with ⟨_ | _, _⟩ <;> simp [cgP, cgX, cgRate] <;> norm_num
    · have : cgP t * cgX (t + 1) = fun _ => 1 := by
        funext ω
        simp only [Pi.mul_apply, cgP, cgX, show ¬ (t ≤ 1) by omega,
          show ¬ (t + 1 ≤ 1) by omega, ↓reduceIte]
        split_ifs <;> norm_num
      simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
      funext ω
      simp [cgRate, show t ≠ 1 by omega]

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path implements the constant rate
`r = 1`. -/
theorem cg_fisher' : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP' cgX'
    (fun _ _ => 1) := by
  intro t
  have : cgP' t * cgX' (t + 1) = fun _ => 1 := by funext ω; simp [cgP', cgX']
  simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
  funext ω; norm_num

/-- Cochrane (2023), §7.1 (counterexample): the surpluses `s_t = 1` have present value `2`
(`β = 1/2`). -/
theorem cg_pv (ω : Bool × Bool) :
    HasSum (fun k => surplusTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (fun _ _ => 1) 0 k ω)
      2 := by
  have h := hasSum_geometric_of_lt_one (r := ((1 : ℝ) + 1)⁻¹) (by norm_num) (by norm_num)
  have e : (1 - ((1 : ℝ) + 1)⁻¹)⁻¹ = 2 := by norm_num
  rw [e] at h
  refine h.congr_fun fun k => ?_
  simp [surplusTerm, ExpectationsFiniteTree.coinSystem.const]

/-- Cochrane (2023), §7.1 (counterexample): the guidance path satisfies the date-0 valuation
equation (7.3) with debt `B_{−1}^{(2)} = 1` and surpluses `s_t = 1`: `β² E_0(1/P_2) = 2`. -/
theorem cg_presentValue : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add, coin_E0, cgX]
  norm_num

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path satisfies the same date-0
valuation equation: `β² · 8 = 2`. -/
theorem cg_presentValue' : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX' (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX' 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add]
  rw [show cgX' 2 = fun _ => (8 : ℝ) from rfl, ExpectationsFiniteTree.coinSystem.const]
  norm_num

/-- Cochrane (2023), §7.1, pp. 213–214 (state-contingent guidance): **an announced rise in
the expected rate path can raise `P_0`.** In the coin-flip economy with debt `B_{−1}^{(2)} = 1`,
surpluses `s_t = 1`, `r = 1`: both paths are adapted, positive, implement their rate paths
(`cg_fisher`, `cg_fisher'`) and satisfy (7.3) (`cg_presentValue`, `cg_presentValue'`); the
guidance rates equal `r` except at date 1, where their mean is `11/10 > r`; yet
`P_0 = 7/48 > 1/8 = P'_0` in every state, and `Q_0^{(2)} = 7/24 > 1/4 = (1+r)^{-2}`. -/
theorem cg_counterexample (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 (cgRate 1) ω = 11 / 10 ∧ (∀ t, t ≠ 1 → cgRate t ω = 1) ∧
      cgP 0 ω = 7 / 48 ∧ cgP' 0 ω = 1 / 8 ∧ cgP' 0 ω < cgP 0 ω ∧
      bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω = 7 / 24 ∧
      ((1 : ℝ) + 1)⁻¹ ^ 2 <
        bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω := by
  have hQ : bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω = 7 / 24 := by
    rw [bondPrice_eq ExpectationsFiniteTree.coinSystem
      (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) cgP_adapted]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add, coin_E0, cgP, cgX]
    norm_num
  refine ⟨?_, fun t ht => by simp [cgRate, ht], by simp [cgP, cgX], rfl,
    by simp [cgP, cgP', cgX]; norm_num, hQ, by rw [hQ]; norm_num⟩
  rw [coin_E0]
  simp [cgRate]
  norm_num

end Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Horizon comparisons for state-contingent forward guidance

Cochrane (2023), §7.1, p. 213 (first bullet): guidance has less effect than the same immediate
rise, and the effect falls with the horizon (`ForwardGuidance.priceLevel_mono`,
`ForwardGuidance.priceLevel_immediate_le`).

With a state-contingent announced rate path both comparisons fail.

* `cg2_fisher`, `cg2_presentValue`: an equilibrium (Fisher relations at every date and the date-0
  valuation (7.3), as in `TidyR5RandomGuidance`) for the rate path `cgRate2`. That path is
  `TidyR5RandomGuidance.cgRate` delayed by one period, with `r` inserted at date 0
  (`cgRate2_delay`).
* `cg_horizon_counterexample`: same debt and surpluses; the earlier announcement has the
  *higher* price level, `P_0 = 7/48 > 1/8`.
  - Read the shape as "`ρ` at the first date, `r` afterwards". Then horizon 1 versus horizon 2
    contradicts monotonicity in the horizon.
  - Read the shape as "`r`, then `ρ`, then `r`". Then the immediate rise (horizon 0) versus
    horizon 1 contradicts "the immediate rise has the largest effect".
* `cg_cov_zero`: the date-0 covariance term of `TidyR5RandomGuidance.bondPrice_cov_rate` is zero
  in this example. So rates uncorrelated with later bond prices do not rescue the comparisons; the
  failure is the convexity (Jensen) effect `E_0(1+i_1)^{-1} > (1 + E_0 i_1)^{-1}`.

The surviving version is the one for rate paths known at date 0:
`TidyR5GuidanceUncertainty.stoch_fg_mono`, of which the immediate-rise comparison is the case
`T = 0`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon

open Filter Topology MaturityStructure TidyR5RandomGuidance

/-- Cochrane (2023), §7.1 (counterexample): the rate path of `cgRate` delayed one period: `2`
after heads and `1/5` after tails at date 2, `r = 1` at every other date. -/
noncomputable def cgRate2 : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t = 2 then (if ω.1 then 2 else 1 / 5) else 1

/-- Cochrane (2023), §7.1 (counterexample): `cgRate2` is `cgRate` delayed by one period, with the
unchanged rate `r = 1` at date 0. -/
theorem cgRate2_delay (t : ℕ) (ω : Bool × Bool) :
    cgRate2 0 ω = 1 ∧ cgRate2 (t + 1) ω = cgRate t ω := by
  refine ⟨by simp [cgRate2], ?_⟩
  simp only [cgRate2, cgRate, show (t + 1 = 2) = (t = 1) by simp]

/-- Cochrane (2023), §7.1 (counterexample): `1/P_t` for the delayed path: `8` up to date 2, then
`16/3` after heads and `40/3` after tails. -/
noncomputable def cgX2 : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t ≤ 2 then 8 else (if ω.1 then 16 / 3 else 40 / 3)

/-- Cochrane (2023), §7.1 (counterexample): the price level `P_t = 1/cgX2`. -/
noncomputable def cgP2 : ℕ → Bool × Bool → ℝ := fun t ω => (cgX2 t ω)⁻¹

/-- Cochrane (2023), §7.1 (counterexample): the delayed path implements the rates `cgRate2`
(`β = 1/2`). -/
theorem cg2_fisher : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP2 cgX2 cgRate2 := by
  intro t
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · have : cgP2 t * cgX2 (t + 1) = fun _ => 1 := by
      funext ω
      simp [cgP2, cgX2, show t ≤ 2 by omega, show t + 1 ≤ 2 by omega]
    simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
    funext ω; simp [cgRate2, show t ≠ 2 by omega]
  · rcases Nat.lt_or_ge t 3 with h3 | h3
    · obtain rfl : t = 2 := by omega
      have hk : ExpectationsFiniteTree.coinSystem.E 2 (cgP2 2 * cgX2 (2 + 1)) =
          cgP2 2 * cgX2 (2 + 1) :=
        coin_known (fun ω ω' h => by simp only [Pi.mul_apply, cgP2, cgX2, h]) (by norm_num)
      simp only [bondPrice, pow_one, hk]
      funext ω
      rcases ω with ⟨_ | _, _⟩ <;> simp [cgP2, cgX2, cgRate2] <;> norm_num
    · have : cgP2 t * cgX2 (t + 1) = fun _ => 1 := by
        funext ω
        simp only [Pi.mul_apply, cgP2, cgX2, show ¬ (t ≤ 2) by omega,
          show ¬ (t + 1 ≤ 2) by omega, ↓reduceIte]
        split_ifs <;> norm_num
      simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
      funext ω
      simp [cgRate2, show t ≠ 2 by omega]

/-- Cochrane (2023), §7.1 (counterexample): the delayed path satisfies the date-0 valuation
equation (7.3) with debt `B_{−1}^{(2)} = 1` and surpluses `s_t = 1`: `β² · 8 = 2`. -/
theorem cg2_presentValue : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX2 (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX2 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add]
  rw [show cgX2 2 = fun _ => (8 : ℝ) from funext fun _ => by simp [cgX2],
    ExpectationsFiniteTree.coinSystem.const]
  norm_num

/-- Cochrane (2023), §7.1, p. 213 (first bullet), **counterexample for state-contingent guidance**:
the path `cgRate` and its one-period delay `cgRate2` (same debt `B_{−1}^{(2)} = 1`, surpluses
`s_t = 1`, `r = 1`) both have equilibria (`cg_fisher`, `cg_presentValue`, `cg2_fisher`,
`cg2_presentValue`), and the earlier announcement gives the higher price level,
`P_0 = 7/48 > 1/8`. This contradicts both monotonicity in the horizon and the immediate-rise
comparison. -/
theorem cg_horizon_counterexample (ω : Bool × Bool) :
    cgP 0 ω = 7 / 48 ∧ cgP2 0 ω = 1 / 8 ∧ cgP2 0 ω < cgP 0 ω := by
  refine ⟨by simp [cgP, cgX], by simp [cgP2, cgX2], ?_⟩
  simp [cgP, cgX, cgP2, cgX2]
  norm_num

/-- Cochrane (2023), §7.1 (counterexample): the covariance term
`Cov_0(β P_0/P_1, Q_1^{(2)})` of `TidyR5RandomGuidance.bondPrice_cov_rate` vanishes in the
counterexample (`P_0/P_1 = 1`), so the failure is not a correlation effect. -/
theorem cg_cov_zero :
    condCov ExpectationsFiniteTree.coinSystem 0 ((1 + 1 : ℝ)⁻¹ • (cgP 0 * cgX (0 + 1)))
      (bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX (0 + 1) 1) = 0 := by
  have hc : (1 + 1 : ℝ)⁻¹ • (cgP 0 * cgX (0 + 1)) = fun _ => (1 + 1 : ℝ)⁻¹ := by
    funext ω; simp [cgP, cgX]
  set b := bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX (0 + 1) 1
  have hm : (fun _ => (1 + 1 : ℝ)⁻¹) * b = (1 + 1 : ℝ)⁻¹ • b := by
    funext ω; simp
  rw [condCov, hc, hm, map_smul, ExpectationsFiniteTree.coinSystem.const]
  funext ω
  simp

end Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The strict sign rule for expected future sales with random debt

Cochrane (2023), Online Appendix §A1.14.2, p. 592 (last bullet), equations (1.65)–(1.66).

`TidyR5FutureSalesRandom.x0R_strictMono` proves the strict sign rule only under uniform positive
lower bounds, on the grounds that an abstract `ExpectationSystem` need not be strictly positive.
That rationale is wrong: monotonicity on *all* functions `Ω → ℝ`, unbounded ones included,
already forces strict positivity.

* `E_pos_iff`: **for every expectation system and every `f ≥ 0`,
  `E_t f > 0` at `ω` if and only if `E_t 1_{f>0} > 0` at `ω`**: `E_t` is strictly positive
  exactly on events of positive conditional probability. The proof uses the unbounded "level
  index" `levelIdx f` (the least `n` with `f > 1/(n+1)`) in one direction and
  `f ≤ M 1_{f>0} + f²/M` in the other. `E_pos_of_pos`: `f > 0` everywhere gives `E_t f > 0`
  everywhere, with no uniform bound.
* `x0R_strict_iff`: **the exact strict sign rule.** Under the book's sign conditions alone
  (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`, larger sales `G ≥ 0`, `B_{−1}^{(0)} > 0`), larger
  future sales strictly lower `P_0` in state `ω` if and only if `E_0 1_{G>0} > 0` there.
  Otherwise there is no effect at all (`x0R_eq_of_null`).
* `x0R_strictMono_pos`: if the sale is larger in every state (`G > 0`), the rule is strict in
  every state for every expectation system, **with no uniform bounds**.
* `nullSys`, `null_counterexample`, `null_counterexample_eqm`: **the exact counterexample.**
  Under an expectation system whose date-0 forecast puts all weight on one state, a larger sale
  only in the other state satisfies every sign condition, yet leaves `P_0` unchanged in every
  equilibrium. So the condition `E_0 1_{G>0} > 0` cannot be dropped. What is needed is *not* a
  uniform bound but positive conditional probability of a larger sale, exactly as on a
  probability space (module TidyR6StrictSignMeasure).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule

open MaturityStructure TidyR5FutureSalesRandom

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix p. 592: the indicator `1_{f>0}` of the event on which `f` is
positive (for `f = G`, the event on which future sales are larger). -/
noncomputable def posEvent (f : Ω → ℝ) : Ω → ℝ := fun ω => if 0 < f ω then 1 else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the indicator of `f > 1/(N+1)`. -/
noncomputable def levelInd (f : Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  fun ω => if 1 / ((N : ℝ) + 1) < f ω then 1 else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the level index of `f`, the least
`n` with `1/(n+1) < f ω` where `f ω > 0`, and `0` elsewhere. It is unbounded in general. -/
noncomputable def levelIdx (f : Ω → ℝ) : Ω → ℝ := fun ω =>
  if h : 0 < f ω then ((Nat.find (exists_nat_one_div_lt h) : ℕ) : ℝ) else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): `1_{f > 1/(N+1)} ≤ (N+1) f` for
`f ≥ 0`. -/
theorem levelInd_le {f : Ω → ℝ} (hf : 0 ≤ f) (N : ℕ) :
    levelInd f N ≤ ((N : ℝ) + 1) • f := fun ω => by
  simp only [levelInd, Pi.smul_apply, smul_eq_mul]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  split_ifs with h
  · rw [div_lt_iff₀ hN] at h; linarith
  · exact mul_nonneg hN.le (hf ω)

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the level index dominates
`N (1_{f>0} − 1_{f > 1/(N+1)})`. -/
theorem levelIdx_ge (f : Ω → ℝ) (N : ℕ) :
    (N : ℝ) • (posEvent f - levelInd f N) ≤ levelIdx f := fun ω => by
  simp only [posEvent, levelInd, levelIdx, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  by_cases h : 0 < f ω
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    split_ifs with h2
    · simp
    · have hge : N < Nat.find (exists_nat_one_div_lt h) := by
        by_contra hlt
        push Not at hlt
        have hs := Nat.find_spec (exists_nat_one_div_lt h)
        have hmono : 1 / ((N : ℝ) + 1) ≤ 1 / ((Nat.find (exists_nat_one_div_lt h) : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hlt 1
        exact h2 (lt_of_le_of_lt hmono hs)
      have : (N : ℝ) ≤ (Nat.find (exists_nat_one_div_lt h) : ℝ) := by exact_mod_cast hge.le
      linarith
  · have h2 : ¬ 1 / ((N : ℝ) + 1) < f ω := by
      intro h2; exact h ((by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)).trans h2)
    simp only [h, h2, ↓reduceIte, ↓reduceDIte, sub_self, mul_zero, le_refl]

/-- Cochrane (2023), Online Appendix p. 592: for `f ≥ 0`, if the event `{f > 0}` has positive
conditional probability at `ω`, then `E_t f > 0` at `ω`. -/
theorem E_pos_of_E_posEvent_pos {f : Ω → ℝ} (hf : 0 ≤ f) {t : ℕ} {ω : Ω}
    (h : 0 < 𝔼.E t (posEvent f) ω) : 0 < 𝔼.E t f ω := by
  by_contra hle
  push Not at hle
  have hlev : ∀ N : ℕ, 𝔼.E t (levelInd f N) ω ≤ 0 := fun N => by
    have h1 := 𝔼.mono t (levelInd_le hf N) ω
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h1
    nlinarith [(by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  have hbig : ∀ N : ℕ, (N : ℝ) * 𝔼.E t (posEvent f) ω ≤ 𝔼.E t (levelIdx f) ω := fun N => by
    have h1 := 𝔼.mono t (levelIdx_ge f N) ω
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    nlinarith [hlev N, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  obtain ⟨N, hN⟩ := exists_nat_gt (𝔼.E t (levelIdx f) ω / 𝔼.E t (posEvent f) ω)
  rw [div_lt_iff₀ h] at hN
  linarith [hbig N]

/-- Cochrane (2023), Online Appendix p. 592: for `f ≥ 0`, `E_t f > 0` at `ω` forces the event
`{f > 0}` to have positive conditional probability at `ω`. -/
theorem E_posEvent_pos_of_E_pos {f : Ω → ℝ} (hf : 0 ≤ f) {t : ℕ} {ω : Ω}
    (h : 0 < 𝔼.E t f ω) : 0 < 𝔼.E t (posEvent f) ω := by
  have hp0 : 0 ≤ 𝔼.E t (posEvent f) ω := by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ posEvent f from fun ω' => by
      simp only [posEvent]; split_ifs <;> norm_num) ω
    rwa [𝔼.const] at this
  by_contra hle
  push Not at hle
  have hp : 𝔼.E t (posEvent f) ω = 0 := le_antisymm hle hp0
  set Q := 𝔼.E t (f * f) ω with hQ
  have hQ0 : 0 ≤ Q := by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ f * f from fun ω' => mul_self_nonneg (f ω')) ω
    rwa [𝔼.const] at this
  set a := 𝔼.E t f ω with ha
  have hM : ∀ M : ℝ, 0 < M → a * M ≤ Q := fun M hM => by
    have hle : f ≤ M • posEvent f + M⁻¹ • (f * f) := fun ω' => by
      simp only [posEvent, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      have hf' := hf ω'
      have hsq : 0 ≤ M⁻¹ * (f ω' * f ω') :=
        mul_nonneg (inv_nonneg.mpr hM.le) (mul_self_nonneg _)
      by_cases hfM : f ω' ≤ M
      · split_ifs with hpos
        · linarith
        · have : f ω' = 0 := le_antisymm (not_lt.mp hpos) hf'
          rw [this]; simp
      · push Not at hfM
        have hpos : 0 < f ω' := hM.trans hfM
        simp only [hpos, ↓reduceIte, mul_one]
        have : f ω' ≤ M⁻¹ * (f ω' * f ω') := by
          rw [← div_eq_inv_mul, le_div_iff₀ hM]; nlinarith
        linarith
    have h1 := 𝔼.mono t hle ω
    rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, mul_zero, zero_add] at h1
    rw [← ha] at h1
    have := mul_le_mul_of_nonneg_right h1 hM.le
    rw [mul_assoc, mul_comm Q M, ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at this
    exact this
  have := hM (2 * (Q + 1) / a) (by positivity)
  have key : a * (2 * (Q + 1) / a) = 2 * (Q + 1) := by field_simp
  rw [key] at this
  linarith

/-- Cochrane (2023), Online Appendix p. 592: **expectations are strictly positive exactly on
events of positive conditional probability**: for every expectation system and every `f ≥ 0`,
`0 < E_t f` at `ω` if and only if `0 < E_t 1_{f>0}` at `ω`. -/
theorem E_pos_iff {f : Ω → ℝ} (hf : 0 ≤ f) (t : ℕ) (ω : Ω) :
    0 < 𝔼.E t f ω ↔ 0 < 𝔼.E t (posEvent f) ω :=
  ⟨E_posEvent_pos_of_E_pos 𝔼 hf, E_pos_of_E_posEvent_pos 𝔼 hf⟩

/-- Cochrane (2023), Online Appendix p. 592: **a strictly positive random variable has a strictly
positive expectation in every state, under every expectation system**, with no uniform lower
bound. -/
theorem E_pos_of_pos {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω) (t : ℕ) (ω : Ω) : 0 < 𝔼.E t f ω := by
  have h1 : posEvent f = fun _ => 1 := funext fun ω' => by simp [posEvent, hf ω']
  rw [E_pos_iff 𝔼 (fun ω' => (hf ω').le), h1, 𝔼.const]
  norm_num

/-- Cochrane (2023), Online Appendix p. 592: the change in `B_{−1}^{(0)}/P_0` from `ε` to `ε'`
is `E_0` of the dilution difference `kCoef/B_1^{(2)}(ε') − kCoef/B_1^{(2)}(ε)`. -/
noncomputable def dilDiff (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ)
    (ε ε' : ℝ) : Ω → ℝ :=
  kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G)

/-- Cochrane (2023), Online Appendix p. 592: the dilution difference in closed form,
`β² s_2 B_0^{(2)} (A₁ − A₂)(ε' − ε) G / (B_1^{(2)}(ε) B_1^{(2)}(ε'))`. -/
theorem dilDiff_eq {β ε ε' : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (h12 : ∀ ω, D 1 2 ω ≠ 0) (hpos : ∀ ω, D 2 2 ω + ε * G ω ≠ 0)
    (hpos' : ∀ ω, D 2 2 ω + ε' * G ω ≠ 0) (ω : Ω) :
    dilDiff β D G s ε ε' ω = β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) *
      ((ε' - ε) * G ω) / ((D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω)) := by
  rw [dilDiff, kCoef_eq h12]
  have h1 := hpos ω
  have h2 := hpos' ω
  simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [div_sub_div _ _ h2 h1, div_eq_div_iff (mul_ne_zero h2 h1) (mul_ne_zero h1 h2)]
  ring

/-- Cochrane (2023), Online Appendix p. 592: under the book's sign conditions the dilution
difference is nonnegative and positive exactly where the sale is larger, `1_{dilDiff>0} =
1_{G>0}`. -/
theorem dilDiff_sign {β ε ε' : ℝ} (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω)
    (hεε : ε < ε') :
    0 ≤ dilDiff β D G s ε ε' ∧ posEvent (dilDiff β D G s ε ε') = posEvent G := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hform := dilDiff_eq (β := β) (s := s) (fun ω => (h12 ω).ne') (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne')
  have hq : ∀ ω, 0 < β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) := fun ω => by
    have := sub_pos.mpr (hA ω)
    have := hs2 ω
    have := h12 ω
    positivity
  have hden : ∀ ω, 0 < (D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω) := fun ω =>
    mul_pos (hpos ω) (hpos' ω)
  have hd : 0 < ε' - ε := sub_pos.mpr hεε
  refine ⟨fun ω => ?_, funext fun ω => ?_⟩
  · rw [Pi.zero_apply, hform]
    have := hG0 ω
    have := hq ω
    have := hden ω
    positivity
  · simp only [posEvent]
    rw [hform]
    rcases (hG0 ω).lt_or_eq with hG | hG
    · have : 0 < β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) * ((ε' - ε) * G ω) /
          ((D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω)) := by
        have := hq ω
        have := hden ω
        positivity
      simp [this, hG]
    · rw [← hG]; simp

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591:
`x0R ε' − x0R ε = E_0(dilDiff)/B_{−1}^{(0)}` whenever `B_1^{(2)}(ε)`, `B_1^{(2)}(ε')` are nonzero
in every state. -/
theorem x0R_sub (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hne' : ∀ ω, D 2 2 ω + ε' * G ω ≠ 0) (ω : Ω) :
    x0R 𝔼 β D G s ε' ω - x0R 𝔼 β D G s ε ω = 𝔼.E 0 (dilDiff β D G s ε ε') ω / D 0 0 ω := by
  rw [x0R_pull 𝔼 hpo hdc hD hne, x0R_pull 𝔼 hpo hdc hD hne', dilDiff, map_sub]
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), with random debt: **the exact strict
sign rule.** Under the book's sign conditions alone (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`,
`β ≠ 0`, `B_{−1}^{(0)} > 0`, a larger sale `G ≥ 0`, `ε < ε'`), larger state-contingent future
sales strictly lower `P_0` in state `ω` if and only if the larger sale has positive conditional
probability, `E_0 1_{G>0} > 0`, at `ω`. No uniform bound is assumed. -/
theorem x0R_strict_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω ↔ 0 < 𝔼.E 0 (posEvent G) ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hsub := x0R_sub 𝔼 (β := β) (s := s) hpo hdc hD (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne') ω
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  rw [← sub_pos, hsub, div_pos_iff_of_pos_right (hD00 ω), E_pos_iff 𝔼 hnn, hev]

/-- Cochrane (2023), Online Appendix p. 592: where the larger sale has zero conditional
probability (`E_0 1_{G>0} = 0`), expected future sales have no effect on `P_0` at all. -/
theorem x0R_eq_of_null (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') {ω : Ω}
    (hnull : 𝔼.E 0 (posEvent G) ω = 0) :
    x0R 𝔼 β D G s ε' ω = x0R 𝔼 β D G s ε ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hsub := x0R_sub 𝔼 (β := β) (s := s) hpo hdc hD (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne') ω
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have h0 : 𝔼.E 0 (dilDiff β D G s ε ε') ω ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have := (E_pos_iff 𝔼 hnn 0 ω).1 hlt
    rw [hev, hnull] at this
    exact lt_irrefl _ this
  have h0' : 0 ≤ 𝔼.E 0 (dilDiff β D G s ε ε') ω := by
    have := 𝔼.mono 0 hnn ω
    rwa [show (0 : Ω → ℝ) = fun _ => 0 from rfl, 𝔼.const] at this
  have : 𝔼.E 0 (dilDiff β D G s ε ε') ω = 0 := le_antisymm h0 h0'
  rw [this, zero_div, sub_eq_zero] at hsub
  exact hsub

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), with random debt: **if the sale is
larger in every state (`G > 0`), larger future sales strictly lower `P_0` in every state, for
every expectation system, under the book's sign conditions alone** (no uniform bounds, unlike
`TidyR5FutureSalesRandom.x0R_strictMono`). -/
theorem x0R_strictMono_pos (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β ε ε' : ℝ} (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hG0 : ∀ ω, 0 < G ω) (hs2 : ∀ ω, 0 < s 2 ω)
    (h12 : ∀ ω, 0 < D 1 2 ω) (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω := by
  rw [x0R_strict_iff 𝔼 hpo hdc hβ hD (fun ω => (hG0 ω).le) hs2 h12 hA hD00 hpos hεε]
  exact E_pos_of_pos 𝔼 (fun ω' => by simp [posEvent, hG0 ω']) 0 ω

/-! ### The exact counterexample: a larger sale only in a zero-weight state -/

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the date-0 forecast that puts all
weight on the state `true`, `E_0 f = f(true)`; full information from date 1 on. -/
noncomputable def nullE (t : ℕ) : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) :=
  if t = 0 then LinearMap.pi (fun _ => LinearMap.proj true) else LinearMap.id

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` at date 0. -/
theorem nullE_zero (f : Bool → ℝ) : nullE 0 f = fun _ => f true := by
  simp [nullE]; rfl

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` from date 1 on. -/
theorem nullE_succ (t : ℕ) (f : Bool → ℝ) : nullE (t + 1) f = f := by
  simp [nullE]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` is an expectation system:
the state `false` has date-0 probability zero and is revealed at date 1. -/
noncomputable def nullSys : ExpectationSystem Bool where
  E := nullE
  const := fun t c => by
    rcases t with _ | t
    · rw [nullE_zero]
    · rw [nullE_succ]
  mono := fun t x y h => by
    rcases t with _ | t
    · rw [nullE_zero, nullE_zero]; exact fun _ => h true
    · rw [nullE_succ, nullE_succ]; exact h
  tower := fun {s t} hst x => by
    rcases s with _ | s
    · rcases t with _ | t
      · rw [nullE_zero, nullE_zero]
      · rw [nullE_succ]
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      simp only [nullE_succ]
  known := fun {s t} hst x => by
    rcases s with _ | s
    · rcases t with _ | t
      · rw [nullE_zero, nullE_zero]
      · rw [nullE_zero, nullE_succ]
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [nullE_succ, nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullSys` has the pull-out
property. -/
theorem nullSys_pullOut : nullSys.PullOut := by
  intro t a y ha
  rcases t with _ | t
  · change nullE 0 a = a at ha
    change nullE 0 (a * y) = a * nullE 0 y
    rw [nullE_zero] at ha ⊢
    rw [nullE_zero]
    funext ω
    have := congrFun ha ω
    simp only [Pi.mul_apply] at this ⊢
    rw [← this]
  · change nullE (t + 1) (a * y) = a * nullE (t + 1) y
    rw [nullE_succ, nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullSys` is closed under
quotients of known variables. -/
theorem nullSys_divClosed : PolicyConstraints.DivClosed nullSys := by
  intro t f g hf hg
  rcases t with _ | t
  · change nullE 0 f = f at hf
    change nullE 0 g = g at hg
    change nullE 0 (f / g) = f / g
    rw [nullE_zero] at hf hg ⊢
    funext ω
    have h1 := congrFun hf ω
    have h2 := congrFun hg ω
    simp only [Pi.div_apply] at h1 h2 ⊢
    rw [← h1, ← h2]
  · change nullE (t + 1) (f / g) = f / g
    rw [nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the debt positions, all known at
date 0: `B_{−1}^{(0)} = 1`, `B_{−1}^{(1)} = 0`, `B_0^{(1)} = 1`, `B_{−1}^{(2)} = B_0^{(2)} =
B_1^{(2)} = 1`, nothing longer. So `A₁ = 1 > 0 = A₂`. -/
noncomputable def nullD : ℕ → ℕ → Bool → ℝ := fun t m _ =>
  if m = 0 ∧ t = 0 then 1 else if m = 1 ∧ t = 1 then 1 else if m = 2 then 1 else 0

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the larger sale, `G = 1` in the
zero-probability state `false` only. -/
noncomputable def nullG : Bool → ℝ := fun ω => if ω then 0 else 1

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): **the book's sign conditions hold,
the sale is larger in some state, but `P_0` does not move.** Under `nullSys` (pull-out and
closed under quotients), with the debt `nullD`, surpluses `s ≡ 1`, `β = 1/2` and the direction
`nullG` (nonnegative, known at date 1, positive in the state `false`): `A₁ > A₂`,
`B_0^{(2)} > 0`, `s_2 > 0`, `B_{−1}^{(0)} > 0`, yet `x0R 0 = x0R 1` in every state, because
`E_0 1_{G>0} = 0`. -/
theorem null_counterexample :
    Predetermined nullSys nullD ∧ nullSys.E 1 nullG = nullG ∧ (∀ ω, 0 ≤ nullG ω) ∧
      nullG false = 1 ∧ (∀ ω, fracA nullD 2 ω < fracA nullD 1 ω) ∧ (∀ ω, 0 < nullD 1 2 ω) ∧
      (∀ ω, 0 < nullD 0 0 ω) ∧ (∀ ω, 0 < nullD 2 2 ω + 0 * nullG ω) ∧
      (∀ ω, nullSys.E 0 (posEvent nullG) ω = 0) ∧
      ∀ ω, x0R nullSys (1 / 2) nullD nullG (fun _ _ => 1) 1 ω =
        x0R nullSys (1 / 2) nullD nullG (fun _ _ => 1) 0 ω := by
  have hconst : ∀ u t m, nullSys.E u (nullD t m) = nullD t m := fun u t m => by
    have : nullD t m = fun _ => nullD t m true := funext fun _ => rfl
    rw [this, nullSys.const]
  have hnull : ∀ ω, nullSys.E 0 (posEvent nullG) ω = 0 := fun ω => by
    change nullE 0 (posEvent nullG) ω = 0
    rw [nullE_zero]; simp [posEvent, nullG]
  have hA : ∀ ω, fracA nullD 2 ω < fracA nullD 1 ω := fun ω => by
    simp [fracA, nullD]
  have hpred : Predetermined nullSys nullD :=
    ⟨fun m => hconst 0 0 m, fun t m => hconst t (t + 1) m⟩
  refine ⟨hpred, ?_, fun ω => by cases ω <;> simp [nullG], by simp [nullG], hA,
    fun ω => by simp [nullD], fun ω => by simp [nullD], fun ω => by simp [nullD], hnull,
    fun ω => ?_⟩
  · change nullE 1 nullG = nullG
    exact nullE_succ 0 nullG
  · exact x0R_eq_of_null nullSys nullSys_pullOut nullSys_divClosed (by norm_num) hpred
      (fun ω => by cases ω <;> simp [nullG]) (fun _ => one_pos) (fun ω => by simp [nullD]) hA
      (fun ω => by simp [nullD]) zero_lt_one (hnull ω)

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66) (counterexample, in equilibrium): in the
economy of `null_counterexample`, **every** equilibrium with the larger sale (`ε = 1`) has the same
`1/P_0` as every equilibrium without it (`ε = 0`): the flow conditions (7.1) at dates 0, 1, 2
pin `1/P_0 = x0R ε` (`TidyR5FutureSalesRandom.x0_eq_x0R`), and `x0R 1 = x0R 0`. -/
theorem null_counterexample_eqm {x x' : ℕ → Bool → ℝ}
    (h0 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 0)
    (h1 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 1)
    (h2 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 2)
    (h0' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 0)
    (h1' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 1)
    (h2' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 2) :
    x 0 = x' 0 := by
  obtain ⟨hpred, hG1, hG0, -, -, -, -, -, -, heq⟩ := null_counterexample
  have hD3 : ∀ t j, nullD t (j + 3) = 0 := fun t j => by
    funext ω; simp [nullD]
  have hD11 : ∀ ω, nullD 1 1 ω ≠ 0 := fun ω => by simp [nullD]
  have hD00 : ∀ ω, nullD 0 0 ω ≠ 0 := fun ω => by simp [nullD]
  have hne : ∀ ε : ℝ, 0 ≤ ε → ∀ ω, nullD 2 2 ω + ε * nullG ω ≠ 0 := fun ε hε ω => by
    have : nullD 2 2 ω = 1 := by simp [nullD]
    rw [this]
    have := mul_nonneg hε (hG0 ω)
    linarith
  rw [x0_eq_x0R nullSys nullSys_pullOut hpred hG1 hD3 h0 h1 h2 (hne 1 zero_le_one) hD11 hD00,
    x0_eq_x0R nullSys nullSys_pullOut hpred hG1 hD3 h0' h1' h2' (hne 0 le_rfl) hD11 hD00]
  exact funext heq

end Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The strict sign rule on a probability space

Cochrane (2023), Online Appendix §A1.14.2, p. 592 (last bullet), equations (1.65)–(1.66).

A genuine probability space `(Ω, μ)` with date-0 information `m ≤ mΩ`, and `E_0 = μ[· | m]`
(Mathlib's conditional expectation; every statement holds almost surely).

* `condExp_pos_iff_ae`: **the conditional expectation is strictly positive exactly on events of
  positive conditional probability.** If `f > 0` on a measurable `B` and `f = 0` off `B`, then
  almost surely `μ[f | m] > 0 ↔ μ[1_B | m] > 0`. `condExp_pos_ae`: `f > 0` everywhere gives
  `μ[f | m] > 0` almost surely. `condExp_bot_pos_iff`: with trivial date-0 information,
  `μ[f | ⊥] > 0` everywhere iff `μ B > 0`.
* `x0M`, `x0M66`, `x0M66_ae_eq`: the closed form (1.66) for `1/P_0` with `E_0 = μ[· | m]`, as
  printed (`x0M66`) and with the date-0 fraction `A₁` pulled out (`x0M`, the form of
  `TidyR5FutureSalesRandom.x0R_pull`); they agree almost surely.
* `x0M_strict_iff_ae`, `x0M66_strict_iff_ae`: **the strict sign rule under the book's sign
  conditions alone** (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`, `B_{−1}^{(0)} > 0`, larger sales
  `G ≥ 0`, and only the integrability that makes (1.66) meaningful): almost surely, larger
  state-contingent future sales strictly lower `P_0` iff the larger sale has positive conditional
  probability `μ[1_{G>0} | m] > 0`. `x0M_mono_ae` is the weak rule.
  `x0M_strictMono_ae`: if `G > 0` everywhere, the rule is strict almost surely.
* `x0_ae_eq_x0M66`: in every equilibrium of the three-period economy (flow conditions (7.1) at
  dates 2, 1, 0 with `E_t = μ[· | 𝓕_t]`, almost surely), `1/P_0 = x0M66` almost surely.
  `eqm_strict_iff_ae`: the strict sign rule for equilibrium price levels.
* `x0M_bot_strict_iff`: with trivial date-0 information (the book's three-period economy has
  date-0 debt known at 0), larger sales strictly lower `P_0` iff `μ{G > 0} > 0`, in every state.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure

open MeasureTheory Filter TidyR5FutureSalesRandom TidyR6StrictSignRule

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Cochrane (2023), Online Appendix p. 592 (measure theory): a nonnegative integrable function
whose integral over a measurable set is nonpositive vanishes almost everywhere on that set. -/
theorem ae_zero_on_of_setIntegral_nonpos {h : Ω → ℝ} {Z : Set Ω} (hZ : MeasurableSet Z)
    (h0 : 0 ≤ᵐ[μ] h) (hi : Integrable h μ) (hle : ∫ x in Z, h x ∂μ ≤ 0) :
    ∀ᵐ ω ∂μ, ω ∈ Z → h ω = 0 := by
  have hnn : 0 ≤ ∫ x in Z, h x ∂μ := setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae h0)
  have heq : ∫ x in Z, h x ∂μ = 0 := le_antisymm hle hnn
  have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae h0) hi.integrableOn).1 heq
  exact (ae_restrict_iff' hZ).1 h1

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space): **the conditional
expectation is strictly positive exactly where the event has positive conditional probability.**
If `f > 0` on a measurable set `B` and `f = 0` off `B`, then almost surely
`0 < μ[f | m] ↔ 0 < μ[1_B | m]`. -/
theorem condExp_pos_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → ℝ} {B : Set Ω}
    (hB : MeasurableSet B) (hfi : Integrable f μ) (hpos : ∀ ω ∈ B, 0 < f ω)
    (hzero : ∀ ω ∉ B, f ω = 0) :
    ∀ᵐ ω ∂μ, (0 < μ[f | m] ω ↔ 0 < μ[B.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  set ind : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hind
  have hii : Integrable ind μ := (integrable_const (1 : ℝ)).indicator hB
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    by_cases h : ω ∈ B
    · exact (hpos ω h).le
    · exact (hzero ω h).ge
  have hind0 : ∀ ω, 0 ≤ ind ω := fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hg0 : 0 ≤ᵐ[μ] μ[f | m] := condExp_nonneg (ae_of_all _ hf0)
  have hp0 : 0 ≤ᵐ[μ] μ[ind | m] := condExp_nonneg (ae_of_all _ hind0)
  -- Step 1: where `μ[f | m] ≤ 0`, the conditional probability of `B` vanishes.
  have hZm : MeasurableSet[m] (μ[f | m] ⁻¹' Set.Iic 0) :=
    stronglyMeasurable_condExp.measurable measurableSet_Iic
  have hZ := hm _ hZm
  have A1 : ∀ᵐ ω ∂μ, ω ∈ μ[f | m] ⁻¹' Set.Iic 0 → μ[ind | m] ω = 0 := by
    have hgZ : ∫ x in μ[f | m] ⁻¹' Set.Iic 0, (μ[f | m]) x ∂μ ≤ 0 :=
      setIntegral_nonpos hZ (fun x hx => hx)
    rw [setIntegral_condExp hm hfi hZm] at hgZ
    have hfZ := ae_zero_on_of_setIntegral_nonpos hZ (ae_of_all _ hf0) hfi hgZ
    have hindZ : ∫ x in μ[f | m] ⁻¹' Set.Iic 0, ind x ∂μ = 0 := by
      refine integral_eq_zero_of_ae ((ae_restrict_iff' hZ).2 ?_)
      filter_upwards [hfZ] with ω hω hωZ
      have h1 := hω hωZ
      have hnB : ω ∉ B := fun hb => (hpos ω hb).ne' h1
      simp [hind, hnB]
    rw [← setIntegral_condExp hm hii hZm] at hindZ
    exact ae_zero_on_of_setIntegral_nonpos hZ hp0 integrable_condExp hindZ.le
  -- Step 2: where `μ[1_B | m] ≤ 0`, the conditional expectation of `f` vanishes.
  have hZm' : MeasurableSet[m] (μ[ind | m] ⁻¹' Set.Iic 0) :=
    stronglyMeasurable_condExp.measurable measurableSet_Iic
  have hZ' := hm _ hZm'
  have A2 : ∀ᵐ ω ∂μ, ω ∈ μ[ind | m] ⁻¹' Set.Iic 0 → μ[f | m] ω = 0 := by
    have hpZ : ∫ x in μ[ind | m] ⁻¹' Set.Iic 0, (μ[ind | m]) x ∂μ ≤ 0 :=
      setIntegral_nonpos hZ' (fun x hx => hx)
    rw [setIntegral_condExp hm hii hZm'] at hpZ
    have hiZ := ae_zero_on_of_setIntegral_nonpos hZ' (ae_of_all _ hind0) hii hpZ
    have hfZ : ∫ x in μ[ind | m] ⁻¹' Set.Iic 0, f x ∂μ = 0 := by
      refine integral_eq_zero_of_ae ((ae_restrict_iff' hZ').2 ?_)
      filter_upwards [hiZ] with ω hω hωZ
      have h1 := hω hωZ
      have hnB : ω ∉ B := fun hb => by simp [hind, hb] at h1
      exact hzero ω hnB
    rw [← setIntegral_condExp hm hfi hZm'] at hfZ
    exact ae_zero_on_of_setIntegral_nonpos hZ' hg0 integrable_condExp hfZ.le
  filter_upwards [A1, A2, hg0, hp0] with ω h1 h2 hg hp
  constructor
  · intro hgpos
    by_contra hle
    push Not at hle
    have := h2 hle
    linarith
  · intro hppos
    by_contra hle
    push Not at hle
    have := h1 hle
    linarith

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space): a strictly positive
integrable random variable has a strictly positive conditional expectation almost surely, with no
uniform lower bound. -/
theorem condExp_pos_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → ℝ} (hfi : Integrable f μ)
    (hpos : ∀ ω, 0 < f ω) : ∀ᵐ ω ∂μ, 0 < μ[f | m] ω := by
  have h := condExp_pos_iff_ae (m := m) hm MeasurableSet.univ hfi (fun ω _ => hpos ω)
    (fun ω h => absurd (Set.mem_univ ω) h)
  rw [Set.indicator_univ, condExp_const hm] at h
  filter_upwards [h] with ω hω
  exact hω.2 one_pos

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space, trivial date-0
information): if `f > 0` on a measurable `B` and `f = 0` off `B`, then `μ[f | ⊥] > 0` in every
state iff `μ B > 0`. -/
theorem condExp_bot_pos_iff [IsProbabilityMeasure μ] {f : Ω → ℝ} {B : Set Ω}
    (hfi : Integrable f μ) (hpos : ∀ ω ∈ B, 0 < f ω) (hzero : ∀ ω ∉ B, f ω = 0) (ω : Ω) :
    0 < μ[f | ⊥] ω ↔ 0 < μ B := by
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    by_cases h : ω ∈ B
    · exact (hpos ω h).le
    · exact (hzero ω h).ge
  have hsupp : Function.support f = B := by
    ext ω
    simp only [Function.mem_support]
    constructor
    · intro h; by_contra hb; exact h (hzero ω hb)
    · intro hb; exact (hpos ω hb).ne'
  rw [condExp_bot', probReal_univ, inv_one, one_smul, ← hsupp]
  exact integral_pos_iff_support_of_nonneg_ae (ae_of_all _ hf0) hfi

/-! ### The closed form (1.66) with `E_0 = μ[· | m]` -/

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space, with the date-0
fraction pulled out (the form of `TidyR5FutureSalesRandom.x0R_pull`):
`1/P_0 = (s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(kCoef/B_1^{(2)}(ε)))/B_{−1}^{(0)}`. -/
noncomputable def x0M (mi : MeasurableSpace Ω) (μ : @Measure Ω mΩ) (β : ℝ) (D : ℕ → ℕ → Ω → ℝ)
    (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) : Ω → ℝ :=
  (s 0 + fracA D 1 * μ[β • s 1 + β ^ 2 • s 2 | mi] +
    μ[kCoef β D s / (D 2 2 + ε • G) | mi]) / D 0 0

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space, as printed:
`B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]
+ E_0[β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) s_2]`, with `B_1^{(2)}(ε) = B_1^{(2)} + ε G`. -/
noncomputable def x0M66 (mi : MeasurableSpace Ω) (μ : @Measure Ω mΩ) (β : ℝ) (D : ℕ → ℕ → Ω → ℝ)
    (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) : Ω → ℝ :=
  (s 0 + fracA D 1 *
      μ[β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) | mi] +
    μ[β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2) | mi]) / D 0 0

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space: the printed
form and the pulled-out form agree almost surely, when `A₁` is known at date 0 and the
expectations in (1.66) exist. -/
theorem x0M66_ae_eq {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hA1 : StronglyMeasurable[m] (fracA D 1)) (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0)
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ) :
    x0M66 m μ β D G s ε =ᵐ[μ] x0M m μ β D G s ε := by
  have hsplit : β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) =
      (β • s 1 + β ^ 2 • s 2) - β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)) := by
    funext ω
    have := hne ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply]
    field_simp
    ring
  have hk : β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2) -
      fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) = kCoef β D s / (D 2 2 + ε • G) := by
    funext ω
    have := hne ω
    simp only [kCoef, fracA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply]
    field_simp
  have e1 := condExp_sub (m := m) i1 i2
  have e2 := condExp_mul_of_stronglyMeasurable_left (μ := μ) hA1 i3 i2
  have e3 := condExp_sub (m := m) i4 i3
  rw [hk] at e3
  rw [← hsplit] at e1
  filter_upwards [e1, e2, e3] with ω h1 h2 h3
  simp only [x0M66, x0M, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [h1, h3]
  simp only [Pi.sub_apply]
  rw [h2]
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: **the weak
sign rule** under the book's sign conditions: almost surely `1/P_0` is larger with the larger
sale. -/
theorem x0M_mono_ae {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hG0 : ∀ ω, 0 ≤ G ω)
    (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω) (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω)
    (hD00 : ∀ ω, 0 < D 0 0 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, x0M m μ β D G s ε ω ≤ x0M m μ β D G s ε' ω := by
  obtain ⟨hnn, -⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have e := condExp_sub (m := m) hi' hi
  have hc : 0 ≤ᵐ[μ] μ[dilDiff β D G s ε ε' | m] := condExp_nonneg (ae_of_all _ hnn)
  filter_upwards [e, hc] with ω he hc
  simp only [dilDiff] at hc
  rw [he] at hc
  simp only [x0M, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hc ⊢
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  linarith

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: **the exact
strict sign rule under the book's sign conditions alone.** With `A₁ > A₂`, `B_0^{(2)} > 0`,
`s_2 > 0`, `β ≠ 0`, `B_{−1}^{(0)} > 0`, a measurable larger sale `G ≥ 0` and `ε < ε'`, and the
two dilution expectations of (1.66) defined (integrable), almost surely: larger
state-contingent future sales strictly lower `P_0` iff `μ[1_{G>0} | m] > 0`. -/
theorem x0M_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, (x0M m μ β D G s ε ω < x0M m μ β D G s ε' ω ↔
      0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have hB : MeasurableSet {ω | 0 < G ω} := measurableSet_lt measurable_const hGm
  have hfpos : ∀ ω ∈ {ω | 0 < G ω}, 0 < dilDiff β D G s ε ε' ω := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq.mp hω, ↓reduceIte] at this
    by_contra h
    simp [h] at this
  have hfzero : ∀ ω ∉ {ω | 0 < G ω}, dilDiff β D G s ε ε' ω = 0 := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq] at this hω
    simp only [hω, ↓reduceIte] at this
    by_contra h
    have hp : 0 < dilDiff β D G s ε ε' ω := lt_of_le_of_ne (hnn ω) (Ne.symm h)
    simp [hp] at this
  have key := condExp_pos_iff_ae (m := m) hm hB (hi'.sub hi) hfpos hfzero
  have e := condExp_sub (m := m) hi' hi
  filter_upwards [key, e] with ω hk he
  rw [← hk, he]
  simp only [x0M, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  rw [← sub_pos, ← sub_div, div_pos_iff_of_pos_right (hD00 ω)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: if the sale is
larger in every state (`G > 0`), larger future sales strictly lower `P_0` almost surely, with no
uniform bounds. -/
theorem x0M_strictMono_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hG0 : ∀ ω, 0 < G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, x0M m μ β D G s ε ω < x0M m μ β D G s ε' ω := by
  have h := x0M_strict_iff_ae hm hβ hGm (fun ω => (hG0 ω).le) hs2 h12 hA hD00 hpos hεε hi hi'
  have hset : {ω | 0 < G ω} = Set.univ := Set.eq_univ_of_forall hG0
  rw [hset, Set.indicator_univ, condExp_const hm] at h
  filter_upwards [h] with ω hω
  exact hω.2 one_pos

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space, as printed:
the exact strict sign rule for the printed closed form (1.66), almost surely, when `A₁` is known
at date 0 and the expectations in (1.66) exist at `ε` and `ε'`. -/
theorem x0M66_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hA1 : StronglyMeasurable[m] (fracA D 1))
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ)
    (i2' : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G))) μ)
    (i3' : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G)))) μ)
    (i4' : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε' • G) * s 2)) μ) :
    ∀ᵐ ω ∂μ, (x0M66 m μ β D G s ε ω < x0M66 m μ β D G s ε' ω ↔
      0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hk : ∀ e : ℝ, (∀ ω, D 2 2 ω + e * G ω ≠ 0) →
      β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + e • G) * s 2) -
        fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + e • G))) =
        kCoef β D s / (D 2 2 + e • G) := fun e hne => by
    funext ω
    have := hne ω
    simp only [kCoef, fracA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply]
    field_simp
  have hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ := by
    rw [← hk ε (fun ω => (hpos ω).ne')]; exact i4.sub i3
  have hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ := by
    rw [← hk ε' (fun ω => (hpos' ω).ne')]; exact i4'.sub i3'
  have h := x0M_strict_iff_ae hm hβ hGm hG0 hs2 h12 hA hD00 hpos hεε hi hi'
  have q := x0M66_ae_eq hA1 (fun ω => (hpos ω).ne') i1 i2 i3 i4
  have q' := x0M66_ae_eq hA1 (fun ω => (hpos' ω).ne') i1 i2' i3' i4'
  filter_upwards [h, q, q'] with ω hω hq hq'
  rw [hq, hq']
  exact hω

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space with trivial
date-0 information (`m = ⊥`; date-0 quantities are numbers, as in the book): **in every state,
larger future sales strictly lower `P_0` iff the larger sale has positive probability,
`μ{G > 0} > 0`.** -/
theorem x0M_bot_strict_iff [IsProbabilityMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) (ω : Ω) :
    x0M ⊥ μ β D G s ε ω < x0M ⊥ μ β D G s ε' ω ↔ 0 < μ {ω | 0 < G ω} := by
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have hfpos : ∀ ω ∈ {ω | 0 < G ω}, 0 < dilDiff β D G s ε ε' ω := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq.mp hω, ↓reduceIte] at this
    by_contra h
    simp [h] at this
  have hfzero : ∀ ω ∉ {ω | 0 < G ω}, dilDiff β D G s ε ε' ω = 0 := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq] at this hω
    simp only [hω, ↓reduceIte] at this
    by_contra h
    have hp : 0 < dilDiff β D G s ε ε' ω := lt_of_le_of_ne (hnn ω) (Ne.symm h)
    simp [hp] at this
  rw [← condExp_bot_pos_iff (hi'.sub hi) hfpos hfzero ω]
  have e1 : ∫ x, (kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G)) x ∂μ =
      ∫ x, (kCoef β D s / (D 2 2 + ε' • G)) x ∂μ - ∫ x, (kCoef β D s / (D 2 2 + ε • G)) x ∂μ :=
    integral_sub hi' hi
  simp only [x0M, condExp_bot', probReal_univ, inv_one, one_smul]
  rw [e1]
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [← sub_pos, ← sub_div, div_pos_iff_of_pos_right (hD00 ω)]
  constructor <;> intro h <;> linarith

/-! ### From the flow conditions to (1.66) on a probability space -/

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66), pp. 589–591, on a probability space:
**in every equilibrium of the three-period economy, `1/P_0` is the printed closed form (1.66)
almost surely.** Date-0 information `m ≤ m1` (date-1 information), `E_t = μ[· | 𝓕_t]`; the flow
conditions (7.1) at dates 2, 1, 0 (as in `FutureSales.flows_of_realFlow`) hold, the first
everywhere and the others almost surely, with the date-1 sale `B_1^{(2)}(ε) = B_1^{(2)} + ε G`;
`B_0^{(1)}`, `B_0^{(2)} − B_{−1}^{(2)}` are known at 0 and `B_1^{(2)}(ε) − B_0^{(2)}` at 1; the
conditional expectations in the flow conditions exist (integrability). -/
theorem x0_ae_eq_x0M66 {m1 : MeasurableSpace Ω} (hm01 : m ≤ m1) (hm1 : m1 ≤ mΩ)
    [IsFiniteMeasure μ] {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hu : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (hD00 : ∀ ω, D 0 0 ω ≠ 0)
    (mu : StronglyMeasurable[m1] (D 2 2 + ε • G - D 1 2)) (m11 : StronglyMeasurable[m] (D 1 1))
    (m12 : StronglyMeasurable[m] (D 1 2 - D 0 2))
    (F2 : (D 2 2 + ε • G) * x 2 = s 2)
    (F1 : D 1 1 * x 1 =ᵐ[μ] s 1 + β • ((D 2 2 + ε • G - D 1 2) * μ[x 2 | m1]))
    (F0 : D 0 0 * x 0 =ᵐ[μ] s 0 + β • ((D 1 1 - D 0 1) * μ[x 1 | m]) +
      β ^ 2 • ((D 1 2 - D 0 2) * μ[x 2 | m]))
    (ix1 : Integrable (x 1) μ) (ix2 : Integrable (x 2) μ) (is1 : Integrable (s 1) μ)
    (ia : Integrable ((D 2 2 + ε • G - D 1 2) * x 2) μ) (ib : Integrable (D 1 1 * x 1) μ)
    (ic : Integrable ((D 1 2 - D 0 2) * x 2) μ) :
    x 0 =ᵐ[μ] x0M66 m μ β D G s ε := by
  set u := D 2 2 + ε • G with hu_def
  have hx2 : ∀ ω, x 2 ω = s 2 ω / u ω := fun ω => by
    have := congrFun F2 ω
    simp only [Pi.mul_apply] at this
    have hne : u ω ≠ 0 := by simpa [hu_def] using hu ω
    rw [eq_div_iff hne, ← this, mul_comm]
  have hf1 : β • s 1 + β ^ 2 • ((u - D 1 2) / u * s 2) =
      β • (s 1 + β • ((u - D 1 2) * x 2)) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply, hx2 ω]
    ring
  have hf2 : β ^ 2 • ((D 1 2 - D 0 2) / u * s 2) = β ^ 2 • ((D 1 2 - D 0 2) * x 2) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, hx2 ω]
    ring
  have hx0M : x0M66 m μ β D G s ε = (s 0 + fracA D 1 * μ[β • (s 1 + β • ((u - D 1 2) * x 2)) | m]
      + μ[β ^ 2 • ((D 1 2 - D 0 2) * x 2) | m]) / D 0 0 := by
    unfold x0M66
    rw [← hf1, ← hf2]
  have eb := condExp_mul_of_stronglyMeasurable_left (μ := μ) mu ia ix2
  have iub : Integrable ((u - D 1 2) * μ[x 2 | m1]) μ := integrable_condExp.congr eb
  have a1 := condExp_smul (μ := μ) β (s 1 + β • ((u - D 1 2) * x 2)) m
  have a2 := condExp_add (m := m) is1 (ia.smul β)
  have a2' := condExp_smul (μ := μ) β ((u - D 1 2) * x 2) m
  have a3 := condExp_mul_of_stronglyMeasurable_left (μ := μ) m11 ib ix1
  have a4 := condExp_congr_ae (m := m) F1
  have a5 := condExp_add (m := m) is1 (iub.smul β)
  have a5' := condExp_smul (μ := μ) β ((u - D 1 2) * μ[x 2 | m1]) m
  have a6 := condExp_congr_ae (m := m) eb.symm
  have a7 := condExp_condExp_of_le (μ := μ) (f := (u - D 1 2) * x 2) hm01 hm1
  have a8 := condExp_smul (μ := μ) (β ^ 2) ((D 1 2 - D 0 2) * x 2) m
  have a9 := condExp_mul_of_stronglyMeasurable_left (μ := μ) m12 ic ix2
  rw [hx0M]
  filter_upwards [a1, a2, a2', a3, a4, a5, a5', a6, a7, a8, a9, F0] with ω h1 h2 h2' h3 h4 h5 h5'
    h6 h7 h8 h9 h0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 h2 h2' h5 h5' h8
  simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3 h9 h0
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [h1, h2, h2', h8, h9]
  rw [h3, h5, h5', h6, h7] at h4
  rw [eq_div_iff (hD00 ω), mul_comm, h0]
  simp only [fracA, Pi.sub_apply, Pi.div_apply] at h0 ⊢
  field_simp [hD11 ω]
  linear_combination (β * (D 1 1 ω - D 0 1 ω)) * h4

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space, **for
equilibrium prices**: if `x` is an equilibrium with the sale `B_1^{(2)} + ε G` and `x'` one with
`B_1^{(2)} + ε' G` (`x0_ae_eq_x0M66`), then under the book's sign conditions, almost surely,
`P'_0 < P_0` iff `μ[1_{G>0} | m] > 0`. -/
theorem eqm_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x x' s : ℕ → Ω → ℝ} (hGm : Measurable G) (hA1 : StronglyMeasurable[m] (fracA D 1))
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hx : x 0 =ᵐ[μ] x0M66 m μ β D G s ε) (hx' : x' 0 =ᵐ[μ] x0M66 m μ β D G s ε')
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ)
    (i2' : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G))) μ)
    (i3' : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G)))) μ)
    (i4' : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε' • G) * s 2)) μ) :
    ∀ᵐ ω ∂μ, (x 0 ω < x' 0 ω ↔ 0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  have h := x0M66_strict_iff_ae hm hβ hGm hA1 hG0 hs2 h12 hA hD00 hpos hεε i1 i2 i3
    i4 i2' i3' i4'
  filter_upwards [h, hx, hx'] with ω hω e e'
  rw [e, e']
  exact hω

end Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# State-contingent forward guidance with the flow conditions at every date

Cochrane (2023), §7.1, pp. 213–215 (equations (7.1)–(7.3)).

In `TidyR5RandomGuidance.cg_counterexample` and `TidyR5RandomHorizon.cg_horizon_counterexample` an
equilibrium meant the Fisher relations at every date plus the date-0 valuation (7.3). Here the
flow conditions (7.1) **and** the present-value relations (7.2) are imposed at **every** date,
under an explicit debt policy (`FullEqm`).

* `rollD`: **the debt policy.** The inherited debt is one bond maturing at date 2,
  `B_{−1}^{(2)} = 1`. From date 0 on the Treasury buys back all long-term debt and finances
  itself with one-period debt only: `B_t^{(t+1)} = b_t` (known at `t`), nothing longer.
  `rollD_flow_zero_iff`, `rollD_flow_succ_iff`, `rollD_pv_zero_iff`, `rollD_pv_succ_iff`: the
  flow and present-value relations under this policy.
* `rollover_valuation`: in every full equilibrium under this policy, with a nonzero constant
  present value of surpluses `V` from date 1 on, the policy quantities are pinned
  (`b_t (1/P_{t+1}) = V`), `1/P_{t+1}` is known at `t`, and
  `(1/P_0) E_0[(1+i_0)^{-1}(1+i_1)^{-1}] = E_0 ∑ β^j s_j`. So `P_0` is unique given the rates.
* `fullEqm_of_known`, `cg_full`, `cg'_full`, `cg2_full`: the three price paths of the earlier
  counterexamples are full equilibria under this policy, with `b_t = 2 P_{t+1}`.
* `cg_flows_counterexample`, `cg_horizon_flows_counterexample`: **both counterexamples survive.**
  Under the rollover policy each rate path has a full equilibrium, and in every full equilibrium
  `P_0 = 7/48` with the state-contingent guidance `cgRate`, against `P_0 = 1/8` with no
  announcement and with the one-period-delayed guidance `cgRate2`. So with the flow conditions
  imposed at every date, a higher expected rate path still raises `P_0`, and the earlier
  announcement still has the larger effect.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows

open Filter Topology MaturityStructure TidyR5RandomGuidance TidyR5RandomHorizon

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1 (debt policy): the inherited debt is `B_{−1}^{(2)} = 1` (`cgB`); from
date 0 on all debt is one-period debt, `B_t^{(t+1)} = b_t`, and long-term debt is bought back. -/
noncomputable def rollD (b : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, m => fun _ => cgB m
  | t + 1, m => if m = t + 1 then b t else 0

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **a full equilibrium** under the debt policy `D`:
predetermined debt, adapted and positive prices with `x = 1/P`, the announced rates implemented
(`RFisher`), and the flow condition (7.1) and present-value relation (7.2) at every date. -/
def FullEqm (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (P x s i : ℕ → Ω → ℝ) : Prop :=
  Predetermined 𝔼 D ∧ 𝔼.Adapted P ∧ 𝔼.Adapted x ∧ (∀ t ω, P t ω * x t ω = 1) ∧
    (∀ t ω, 0 < P t ω) ∧ RFisher 𝔼 β P x i ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
    ∀ t, PresentValue 𝔼 β D x s t

/-- Cochrane (2023), §7.1 (debt policy): the rollover policy is predetermined when each `b_t` is
known at `t`. -/
theorem rollD_predetermined {b : ℕ → Ω → ℝ} (hb : ∀ t, 𝔼.E t (b t) = b t) :
    Predetermined 𝔼 (rollD b) := by
  refine ⟨fun m => 𝔼.const 0 _, fun t m => ?_⟩
  simp only [rollD]
  split_ifs
  · exact hb t
  · exact map_zero _

/-- Cochrane (2023), eq. (7.1), p. 213, at date 0 under the rollover policy: the flow condition
holds iff `β b_0 E_0(1/P_1) − β² E_0(1/P_2) = −s_0` (the surplus buys back the long bond net of
the one-period issue). -/
theorem rollD_flow_zero_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} :
    RealFlow 𝔼 β (rollD b) x s 0 ↔
      ∀ ω, β * (b 0 ω * 𝔼.E 0 (x 1) ω) - β ^ 2 * 𝔼.E 0 (x 2) ω = -s 0 ω := by
  have hfin : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales (rollD b) 0 (0 + (j + 1)) ω *
      𝔼.E 0 (x (0 + (j + 1))) ω)) (β * (b 0 ω * 𝔼.E 0 (x 1) ω) - β ^ 2 * 𝔼.E 0 (x 2) ω) := by
    intro ω
    have hz : ∀ j ∉ ({0, 1} : Finset ℕ), β ^ (j + 1) * (sales (rollD b) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (x (0 + (j + 1))) ω) = 0 := fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [sales, rollD, cgB, hj.1, show j + 1 ≠ 2 by omega]
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hz using 1
    simp [sales, rollD, cgB]
    ring
  constructor
  · intro h ω
    have := (h ω).unique (hfin ω)
    simp only [rollD, cgB] at this
    norm_num at this
    linarith
  · intro h ω
    convert hfin ω using 1
    simp only [rollD, cgB]
    norm_num
    linarith [h ω]

/-- Cochrane (2023), eq. (7.1), p. 213, at date `t + 1` under the rollover policy: the flow
condition holds iff `β b_{t+1} E_{t+1}(1/P_{t+2}) = b_t/P_{t+1} − s_{t+1}`. -/
theorem rollD_flow_succ_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (t : ℕ) :
    RealFlow 𝔼 β (rollD b) x s (t + 1) ↔
      ∀ ω, β * (b (t + 1) ω * 𝔼.E (t + 1) (x (t + 2)) ω) = b t ω * x (t + 1) ω - s (t + 1) ω := by
  have hfin : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) *
      (sales (rollD b) (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω))
      (β * (b (t + 1) ω * 𝔼.E (t + 1) (x (t + 2)) ω)) := by
    intro ω
    have h := hasSum_single (f := fun j : ℕ => β ^ (j + 1) *
      (sales (rollD b) (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω)) 0
      (fun j hj => by
        simp [sales, rollD, hj])
    convert h using 1
    simp [sales, rollD]
  constructor
  · intro h ω
    have := (h ω).unique (hfin ω)
    simp only [rollD, ↓reduceIte] at this
    linarith
  · intro h ω
    convert hfin ω using 1
    simp only [rollD, ↓reduceIte]
    linarith [h ω]

/-- Cochrane (2023), eq. (7.2), p. 213, at date 0 under the rollover policy: the present-value
relation holds iff the surplus series converges and `β² E_0(1/P_2) = E_0 ∑ β^j s_j`. -/
theorem rollD_pv_zero_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} :
    PresentValue 𝔼 β (rollD b) x s 0 ↔ ∀ ω, Summable (fun k => surplusTerm 𝔼 β s 0 k ω) ∧
      β ^ 2 * 𝔼.E 0 (x 2) ω = pvSurplus 𝔼 β s 0 ω := by
  have hfin : ∀ ω, HasSum (fun j => debtTerm 𝔼 β (rollD b) x 0 j ω)
      (β ^ 2 * 𝔼.E 0 (x 2) ω) := by
    intro ω
    have h := hasSum_single (f := fun j => debtTerm 𝔼 β (rollD b) x 0 j ω) 2
      (fun j hj => by simp [debtTerm, rollD, cgB, hj])
    convert h using 1
    simp [debtTerm, rollD, cgB]
  constructor
  · intro h ω
    exact ⟨(h ω).1, (hfin ω).unique (h ω).2⟩
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← (h ω).2]
    exact hfin ω

/-- Cochrane (2023), eq. (7.2), p. 213, at date `t + 1` under the rollover policy: the
present-value relation holds iff the surplus series converges and
`b_t E_{t+1}(1/P_{t+1}) = E_{t+1} ∑ β^j s_{t+1+j}`. -/
theorem rollD_pv_succ_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (t : ℕ) :
    PresentValue 𝔼 β (rollD b) x s (t + 1) ↔
      ∀ ω, Summable (fun k => surplusTerm 𝔼 β s (t + 1) k ω) ∧
        b t ω * 𝔼.E (t + 1) (x (t + 1)) ω = pvSurplus 𝔼 β s (t + 1) ω := by
  have hfin : ∀ ω, HasSum (fun j => debtTerm 𝔼 β (rollD b) x (t + 1) j ω)
      (b t ω * 𝔼.E (t + 1) (x (t + 1)) ω) := by
    intro ω
    have h := hasSum_single (f := fun j => debtTerm 𝔼 β (rollD b) x (t + 1) j ω) 0
      (fun j hj => by simp [debtTerm, rollD, hj])
    convert h using 1
    simp [debtTerm, rollD]
  constructor
  · intro h ω
    exact ⟨(h ω).1, (hfin ω).unique (h ω).2⟩
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← (h ω).2]
    exact hfin ω

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **in every full equilibrium under the rollover
policy** (pull-out, `β ≠ 0`, a nonzero constant present value of surpluses `V` from date 1 on):
the policy quantities are pinned, `b_t/P_{t+1} = V`; `1/P_{t+1}` is known at `t`; and
`(1/P_0) E_0[(1+i_0)^{-1}(1+i_1)^{-1}] = E_0 ∑ β^j s_j`, which determines `P_0` from the
announced rates. -/
theorem rollover_valuation (hpo : 𝔼.PullOut) {β V : ℝ} (hβ : β ≠ 0) (hV : V ≠ 0)
    {b : ℕ → Ω → ℝ} {P x s i : ℕ → Ω → ℝ} (he : FullEqm 𝔼 β (rollD b) P x s i)
    (hpv : ∀ t ω, pvSurplus 𝔼 β s (t + 1) ω = V) :
    (∀ t ω, b t ω * x (t + 1) ω = V) ∧ (∀ t, 𝔼.E t (x (t + 1)) = x (t + 1)) ∧
      ∀ ω, x 0 ω * 𝔼.E 0 (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω = pvSurplus 𝔼 β s 0 ω := by
  obtain ⟨hD, hP, hx, hPx, -, hF, -, hPV⟩ := he
  have hb : ∀ t ω, b t ω * x (t + 1) ω = V := fun t ω => by
    have := ((rollD_pv_succ_iff 𝔼 t).1 (hPV (t + 1)) ω).2
    rwa [hx (t + 1), hpv] at this
  have hbk : ∀ t, 𝔼.E t (b t) = b t := fun t => by
    have := hD.2 t (t + 1)
    simpa [rollD] using this
  have hxk : ∀ t, 𝔼.E t (x (t + 1)) = x (t + 1) := fun t => by
    have hprod : b t * x (t + 1) = fun _ => V := funext fun ω => hb t ω
    have h1 : 𝔼.E t (b t * x (t + 1)) = b t * 𝔼.E t (x (t + 1)) := hpo t _ _ (hbk t)
    rw [hprod, 𝔼.const] at h1
    funext ω
    have h2 := congrFun h1 ω
    simp only [Pi.mul_apply] at h2
    have hbne : b t ω ≠ 0 := fun h0 => by
      have := hb t ω; rw [h0, zero_mul] at this; exact hV this.symm
    apply mul_left_cancel₀ hbne
    rw [← h2, hb t ω]
  have hstep : ∀ t ω, x (t + 1) ω = x t ω * (1 + i t ω)⁻¹ / β := fun t ω => by
    have h1 := congrFun (hF t) ω
    simp only [bondPrice, pow_one, Pi.smul_apply, smul_eq_mul] at h1
    rw [hpo t _ _ (hP t), hxk t] at h1
    simp only [Pi.mul_apply] at h1
    rw [← h1, eq_div_iff hβ]
    have := hPx t ω
    linear_combination (-(β * x (t + 1) ω)) * this
  refine ⟨hb, hxk, fun ω => ?_⟩
  have hx2 : x 2 = (β ^ 2)⁻¹ • (x 0 * fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) := by
    funext ω'
    rw [hstep 1 ω', hstep 0 ω']
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    field_simp
  have h0 := ((rollD_pv_zero_iff 𝔼).1 (hPV 0) ω).2
  rw [hx2, map_smul, hpo 0 _ _ (hx 0)] at h0
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h0
  rw [← h0]
  field_simp

/-- Cochrane (2023), §7.1 (counterexample economy): with `β = 1/2` and surpluses `s_t = 1`, the
present value of surpluses is `2` at every date, under every expectation system. -/
theorem pv_one (t : ℕ) (ω : Ω) :
    HasSum (fun k => surplusTerm 𝔼 (1 + 1)⁻¹ (fun _ _ => 1) t k ω) 2 := by
  have h := hasSum_geometric_of_lt_one (r := ((1 : ℝ) + 1)⁻¹) (by norm_num) (by norm_num)
  have e : (1 - ((1 : ℝ) + 1)⁻¹)⁻¹ = 2 := by norm_num
  rw [e] at h
  refine h.congr_fun fun k => ?_
  simp [surplusTerm, 𝔼.const]

/-- Cochrane (2023), §7.1 (counterexample economy): `E_t ∑ β^j s_{t+j} = 2` at every date. -/
theorem pvSurplus_one (t : ℕ) (ω : Ω) : pvSurplus 𝔼 (1 + 1)⁻¹ (fun _ _ => 1) t ω = 2 :=
  (pv_one 𝔼 t ω).tsum_eq

/-- Cochrane (2023), §7.1 (debt policy): the one-period issue `b_t = 2 P_{t+1}`, whose real
value at maturity is the present value of surpluses. -/
noncomputable def rollB (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => 2 * (x (t + 1) ω)⁻¹

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **sufficient conditions for a full equilibrium**
under the rollover policy with `b_t = 2 P_{t+1}` (`β = 1/2`, `s_t = 1`): an adapted positive price
path implementing the rates, with `1/P_{t+1}` and `2 P_{t+1}` known at `t`, and
`E_0(1/P_2) = 8`. -/
theorem fullEqm_of_known {P x i : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hPpos : ∀ t ω, 0 < P t ω)
    (hF : RFisher 𝔼 (1 + 1)⁻¹ P x i) (hxk : ∀ t, 𝔼.E t (x (t + 1)) = x (t + 1))
    (hbk : ∀ t, 𝔼.E t (rollB x t) = rollB x t) (hx2 : ∀ ω, 𝔼.E 0 (x 2) ω = 8) :
    FullEqm 𝔼 (1 + 1)⁻¹ (rollD (rollB x)) P x (fun _ _ => 1) i := by
  have hxne : ∀ t ω, x t ω ≠ 0 := fun t ω h0 => by
    have := hPx t ω; rw [h0, mul_zero] at this; exact zero_ne_one this
  refine ⟨rollD_predetermined 𝔼 hbk, hP, hx, hPx, hPpos, hF, fun t => ?_, fun t => ?_⟩
  · rcases t with _ | t
    · refine (rollD_flow_zero_iff 𝔼).2 fun ω => ?_
      rw [hxk 0, hx2]
      simp only [rollB]
      field_simp [hxne 1 ω]
      norm_num
    · refine (rollD_flow_succ_iff 𝔼 t).2 fun ω => ?_
      rw [hxk (t + 1)]
      simp only [rollB]
      field_simp [hxne (t + 1 + 1) ω, hxne (t + 1) ω]
      norm_num
  · rcases t with _ | t
    · refine (rollD_pv_zero_iff 𝔼).2 fun ω => ⟨(pv_one 𝔼 0 ω).summable, ?_⟩
      rw [hx2, pvSurplus_one]
      norm_num
    · refine (rollD_pv_succ_iff 𝔼 t).2 fun ω => ⟨(pv_one 𝔼 (t + 1) ω).summable, ?_⟩
      rw [hx (t + 1), pvSurplus_one]
      simp only [rollB]
      field_simp [hxne (t + 1) ω]

/-! ### The three counterexample paths are full equilibria -/

/-- Cochrane (2023), §7.1 (counterexample): the guidance path `cgX` with the state-contingent
rates `cgRate` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1}`. -/
theorem cg_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP
    cgX (fun _ _ => 1) cgRate := by
  refine fullEqm_of_known _ cgP_adapted cg_adapted (fun t ω => ?_) (fun t ω => ?_) cg_fisher
    (fun t => ?_) (fun t => ?_) (fun ω => ?_)
  · have : cgX t ω ≠ 0 := by simp only [cgX]; split_ifs <;> norm_num
    exact inv_mul_cancel₀ this
  · simp only [cgP, cgX]; split_ifs <;> norm_num
  · rcases t with _ | t
    · have : cgX (0 + 1) = fun _ => 48 / 7 := funext fun ω => by simp [cgX]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [cgX, h]) (by omega)
  · rcases t with _ | t
    · have : rollB cgX 0 = fun _ => 2 * (48 / 7)⁻¹ := funext fun ω => by simp [rollB, cgX]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [rollB, cgX, h]) (by omega)
  · rw [coin_E0]; simp [cgX]; norm_num

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path `cgX' = 8` with the constant
rate `r = 1` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1} = 1/4`. -/
theorem cg'_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX'))
    cgP' cgX' (fun _ _ => 1) (fun _ _ => 1) := by
  have hc : ∀ (c : ℝ) t, ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun c t => ExpectationsFiniteTree.coinSystem.const t c
  refine fullEqm_of_known _ (fun t => hc _ t) (fun t => hc _ t) (fun t ω => ?_)
    (fun t ω => ?_) cg_fisher' (fun t => hc _ t) (fun t => hc _ t) (fun ω => ?_)
  · simp [cgP', cgX']
  · simp [cgP']
  · rw [show cgX' 2 = fun _ => (8 : ℝ) from rfl, hc]

/-- Cochrane (2023), §7.1 (counterexample): the delayed path `cgX2` is adapted. -/
theorem cg2_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgX2 := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgX2 0 = fun _ => 8 := by funext ω; simp [cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgX2, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the delayed price level `cgP2` is adapted. -/
theorem cgP2_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgP2 := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgP2 0 = fun _ => 8⁻¹ := by funext ω; simp [cgP2, cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgP2, cgX2, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the one-period-delayed guidance path `cgX2` with the
rates `cgRate2` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1}`. -/
theorem cg2_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX2))
    cgP2 cgX2 (fun _ _ => 1) cgRate2 := by
  refine fullEqm_of_known _ cgP2_adapted cg2_adapted (fun t ω => ?_) (fun t ω => ?_) cg2_fisher
    (fun t => ?_) (fun t => ?_) (fun ω => ?_)
  · have : cgX2 t ω ≠ 0 := by simp only [cgX2]; split_ifs <;> norm_num
    exact inv_mul_cancel₀ this
  · simp only [cgP2, cgX2]; split_ifs <;> norm_num
  · rcases t with _ | t
    · have : cgX2 (0 + 1) = fun _ => 8 := funext fun ω => by simp [cgX2]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [cgX2, h]) (by omega)
  · rcases t with _ | t
    · have : rollB cgX2 0 = fun _ => 2 * 8⁻¹ := funext fun ω => by simp [rollB, cgX2]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [rollB, cgX2, h]) (by omega)
  · have : cgX2 2 = fun _ => 8 := funext fun ω => by simp [cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]

/-! ### Uniqueness of `P_0` and the surviving counterexamples -/

/-- Cochrane (2023), §7.1 (counterexample economy): in every full equilibrium under the rollover
policy (`β = 1/2`, `s_t = 1`, coin-flip tree), `P_0 = E_0[(1+i_0)^{-1}(1+i_1)^{-1}]/2` in every
state, and `b_t = 2 P_{t+1}`. -/
theorem coin_rollover_price {b : ℕ → Bool × Bool → ℝ} {P x i : ℕ → Bool × Bool → ℝ}
    (he : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) i)
    (ω : Bool × Bool) :
    P 0 ω = ExpectationsFiniteTree.coinSystem.E 0
      (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω / 2 ∧ ∀ t ω, b t ω = 2 * P (t + 1) ω := by
  obtain ⟨hb, -, hv⟩ := rollover_valuation ExpectationsFiniteTree.coinSystem
    (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) (by norm_num)
    (two_ne_zero) he (fun t ω => pvSurplus_one _ (t + 1) ω)
  obtain ⟨-, -, -, hPx, -⟩ := he
  refine ⟨?_, fun t ω' => ?_⟩
  · have h := hv ω
    rw [pvSurplus_one] at h
    have := hPx 0 ω
    linear_combination (ExpectationsFiniteTree.coinSystem.E 0
      (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω / 2) * this - P 0 ω / 2 * h
  · have h := hb t ω'
    have := hPx (t + 1) ω'
    linear_combination P (t + 1) ω' * h - b t ω' * this

/-- Cochrane (2023), §7.1, pp. 213–214, **with the flow conditions imposed at every date**: the
state-contingent guidance counterexample survives. Under the rollover policy (buy back the long
bond, then one-period debt only) both the guidance rates `cgRate` (mean `11/10 > r = 1` at date 1)
and the constant rate `r` have full equilibria (`cg_full`, `cg'_full`); in **every** full
equilibrium `P_0 = 7/48` with the guidance and `P_0 = 1/8` without it, so the announced rise in
the expected rate path raises `P_0`. -/
theorem cg_flows_counterexample :
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP cgX
      (fun _ _ => 1) cgRate ∧
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX')) cgP' cgX'
      (fun _ _ => 1) (fun _ _ => 1) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate →
        ∀ ω, P 0 ω = 7 / 48) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1)
        (fun _ _ => 1) → ∀ ω, P 0 ω = 1 / 8) ∧
    (1 : ℝ) / 8 < 7 / 48 := by
  refine ⟨cg_full, cg'_full, fun b P x he ω => ?_, fun b P x he ω => ?_, by norm_num⟩
  · rw [(coin_rollover_price he ω).1, coin_E0]
    simp [cgRate]
    norm_num
  · rw [(coin_rollover_price he ω).1, coin_E0]
    norm_num

/-- Cochrane (2023), §7.1, p. 213 (first bullet), **with the flow conditions imposed at every
date**: the horizon counterexample survives. Under the rollover policy the guidance `cgRate` and
its one-period delay `cgRate2` both have full equilibria (`cg_full`, `cg2_full`); in every full
equilibrium `P_0 = 7/48` for the earlier announcement and `P_0 = 1/8` for the later one, so the
earlier announcement has the larger effect on `P_0` (contradicting both monotonicity in the
horizon and the immediate-rise comparison). -/
theorem cg_horizon_flows_counterexample :
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP cgX
      (fun _ _ => 1) cgRate ∧
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX2)) cgP2 cgX2
      (fun _ _ => 1) cgRate2 ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate →
        ∀ ω, P 0 ω = 7 / 48) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate2 →
        ∀ ω, P 0 ω = 1 / 8) ∧
    (1 : ℝ) / 8 < 7 / 48 := by
  refine ⟨cg_full, cg2_full, (cg_flows_counterexample).2.2.1, fun b P x he ω => ?_,
    by norm_num⟩
  rw [(coin_rollover_price he ω).1, coin_E0]
  simp [cgRate2]
  norm_num

end Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows

set_option linter.style.longLine false
#print axioms Cochrane.LongTermDebtDynamics.SchurStable
#print axioms Cochrane.LongTermDebtDynamics.disc
#print axioms Cochrane.LongTermDebtDynamics.root₁
#print axioms Cochrane.LongTermDebtDynamics.root₂
#print axioms Cochrane.LongTermDebtDynamics.root_sum
#print axioms Cochrane.LongTermDebtDynamics.root_prod
#print axioms Cochrane.LongTermDebtDynamics.root_eq
#print axioms Cochrane.LongTermDebtDynamics.normSq_root_of_neg
#print axioms Cochrane.LongTermDebtDynamics.norm_root_of_nonneg
#print axioms Cochrane.LongTermDebtDynamics.schurStable_iff_roots
#print axioms Cochrane.LongTermDebtDynamics.chSeq
#print axioms Cochrane.LongTermDebtDynamics.convSeq
#print axioms Cochrane.LongTermDebtDynamics.convSeq_rec
#print axioms Cochrane.LongTermDebtDynamics.chSeq_eq_convSeq
#print axioms Cochrane.LongTermDebtDynamics.norm_convSeq_le
#print axioms Cochrane.LongTermDebtDynamics.abs_chSeq_le
#print axioms Cochrane.LongTermDebtDynamics.tendsto_chSeq
#print axioms Cochrane.LongTermDebtDynamics.tr2
#print axioms Cochrane.LongTermDebtDynamics.det2
#print axioms Cochrane.LongTermDebtDynamics.tr2_eq_trace
#print axioms Cochrane.LongTermDebtDynamics.det2_eq_det
#print axioms Cochrane.LongTermDebtDynamics.sq_eq_cayleyHamilton
#print axioms Cochrane.LongTermDebtDynamics.pow_succ_eq
#print axioms Cochrane.LongTermDebtDynamics.abs_pow_entry_le
#print axioms Cochrane.LongTermDebtDynamics.tendsto_pow_entry
#print axioms Cochrane.LongTermDebtDynamics.BoundedSeq
#print axioms Cochrane.LongTermDebtDynamics.homogeneous_iterate
#print axioms Cochrane.LongTermDebtDynamics.abs_mulVec_le
#print axioms Cochrane.LongTermDebtDynamics.homogeneous_eq_zero
#print axioms Cochrane.LongTermDebtDynamics.eq_root_of_eq
#print axioms Cochrane.LongTermDebtDynamics.exists_eigenvector
#print axioms Cochrane.LongTermDebtDynamics.exists_bounded_homogeneous
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.mk
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.E
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.const
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.mono
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.tower
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.known
#print axioms Cochrane.LongTermDebtDynamics.perfectForesight
#print axioms Cochrane.LongTermDebtDynamics.BoundedProc
#print axioms Cochrane.LongTermDebtDynamics.BoundedVec
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.Adapted
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.IsAR1
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.E_neg
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.E_smul
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.E_E_self
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.abs_E_le
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.bounded_E
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.ar1_iterate
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forward_iterate
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forward_unique
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.E_tsum
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forwardSeries
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.PullOut
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.Solves
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.AdaptedVec
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.system_iterate
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.system_unique
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.system_not_unique
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.Determinate
#print axioms Cochrane.LongTermDebtDynamics.ExpectationSystem.determinate_iff
#print axioms Cochrane.LongTermDebtDynamics.perfectForesight_pullOut
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.LongTermDebtDynamics.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.Solves
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.E_of_known
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.solves_adapted
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.iterate_A15
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.summable_A16
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.ScalarEq
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalarSol
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalarSol_apply
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalarEq_iff
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalar_homog
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sunspotFamily
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.homog_solves
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.solves_add_homog
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.existsUnique_iff
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.ar1_decay
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.predetermined_restriction
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.summable_geom_mul
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.abel_tsum
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.LongTermDebtDynamics.ForwardSolution.E_tsum_dom
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.sales
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.Predetermined
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.Predetermined.known
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.Predetermined.known_succ
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.bondPrice
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.bondPrice_eq
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.NominalFlow
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.RealFlow
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.nominalFlow_iff_realFlow
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.debtTerm
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.debtValue
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.surplusTerm
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.pvSurplus
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.PresentValue
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.DebtDominated
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.nominalValue_eq
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.hasSum_E_debtValue_succ
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.realFlow_iff_recursion
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.debtValue_adapted
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.debtValue_iterate
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.summable_surplusTerm
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.Transversality
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.presentValue_iff_tvc
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.pvSurplus_recursion
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.flow_tvc_iff_presentValue
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.transversality_of_bounded
#print axioms Cochrane.LongTermDebtDynamics.MaturityStructure.presentValue_of_bounded
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_of_le
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_add
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_same
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.inv_pow_lt_fgPrice
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_lt
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_mono
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgRate
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPath
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPath_succ
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPath_unique
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPath_eq_of_le
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPath_jump
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgPrice_eq_path
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.priceLevel
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.valuation_iff
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.priceLevel_fg_of_le
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.priceLevel_fg_lt
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.priceLevel_mono
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.priceLevel_immediate_le
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgSum
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.hasSum_fg_geometric
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgSum_same
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fg_jump_geometric
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fg_jump_immediate
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_eq
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_neg
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_succ
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_abs_lt
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_tendsto
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_abs_mono_omega
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.fgJump_calibration
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.perpetuity_ratio_bounds
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgIntegrand
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgValue
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.integral_cfg
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgValue_same
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfg_jump
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump_zero
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump_neg
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump_abs_anti
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump_tendsto
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.cfgJump_abs_anti_varpi
#print axioms Cochrane.LongTermDebtDynamics.ForwardGuidance.steady_sales
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.NoSales
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.debt_eq_initial
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.price_eq_maturing
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_solution
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_E_price
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_bondPrice
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_presentValue
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_price_news
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_bond_news
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.noSales_price_indep
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.OnePeriod
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.oneperiod_flow_iff
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.oneperiod_flow_E
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.oneperiod_backward
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.oneperiod_two_period
#print axioms Cochrane.LongTermDebtDynamics.MaturingDebt.oneperiod_fear
#print axioms Cochrane.LongTermDebtDynamics.BondSales.SalesAtZeroOnly
#print axioms Cochrane.LongTermDebtDynamics.BondSales.debt_eq_one
#print axioms Cochrane.LongTermDebtDynamics.BondSales.maturing_eq
#print axioms Cochrane.LongTermDebtDynamics.BondSales.E_price_eq
#print axioms Cochrane.LongTermDebtDynamics.BondSales.bondPrice_mul_debt
#print axioms Cochrane.LongTermDebtDynamics.BondSales.real_revenue
#print axioms Cochrane.LongTermDebtDynamics.BondSales.dilution_formula
#print axioms Cochrane.LongTermDebtDynamics.BondSales.no_outstanding
#print axioms Cochrane.LongTermDebtDynamics.BondSales.no_outstanding_price_indep
#print axioms Cochrane.LongTermDebtDynamics.BondSales.sales_lower_bondPrice
#print axioms Cochrane.LongTermDebtDynamics.BondSales.sales_raise_future_price
#print axioms Cochrane.LongTermDebtDynamics.BondSales.bondPrice_target_iff
#print axioms Cochrane.LongTermDebtDynamics.BondSales.unit_elasticity
#print axioms Cochrane.LongTermDebtDynamics.BondSales.outstanding_sales_lower_price
#print axioms Cochrane.LongTermDebtDynamics.BondSales.hasDerivAt_dilution
#print axioms Cochrane.LongTermDebtDynamics.BondSales.offset_shock
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.flows_of_realFlow
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_two
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_one
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.E_price_one
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_zero
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.no_outstanding_price_zero
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_two_symm
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.bondPrice_two_symm
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x1_formula
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.future_sales_raise_Q1
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.no_time0_sales
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_zero_no_sale_two
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.price_zero_no_sale_one
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x0Fun
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x0_closed
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.hasDerivAt_x0
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x0_strictMono
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x0_strictAnti
#print axioms Cochrane.LongTermDebtDynamics.FutureSales.x0_const
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_zero
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_succ
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.sum_triangle
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_first_step
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.comps
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.mem_comps
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.chainProd
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.chainProd_eq
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.chainSum
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_eq_chainSum
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.fracSold
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.MaturingSystem
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.realFlow_iff_maturingSystem
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_known
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.theoremW_finite
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.RowBound
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.domA
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.domWeight
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.weight_domA
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.domWeight_nonneg
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.domWeight_succ
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.abs_weight_le
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.sum_domWeight_le
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.summable_domWeight
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.formulaTerm
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.formulaW
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.abs_formulaTerm_le
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.formulaW_summable
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.formulaW_solves
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.unique_of_row
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.theoremW
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.col_lemma
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.abs_E_le_E_abs
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.unique_of_noBuyback
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.homogeneous_of_two
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.unique_iff_homogeneous
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.NoBuyback
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.NoBuyback.nonneg
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.NoBuyback.frac_nonneg
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.NoBuyback.col_le_one
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.bounded_of_presentValue
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.price_unique_noBuyback
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.price_unique_row
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.price_formula
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.special_noSales
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.special_onePeriod
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.fracSold_onePeriod
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.exD
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.exS
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.printed_715_fails
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.pvMatrix
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.pvMatrix_row
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxD
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxS
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxStar
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxX
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxD_self
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxD_succ
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cxD_far
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_buyback
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_flow
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_presentValue
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_pos
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_bounded
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_ne
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_frac
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_weight_rec
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_weight
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_formula_diverges
#print axioms Cochrane.LongTermDebtDynamics.GeneralFormula.cx_not_row
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.DivClosed
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.perfectForesight_divClosed
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.finiteTree_divClosed
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.E_div_known
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.bOne
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOneD
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOneX
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.Targets
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.cTwo
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwoD
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwoX
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.bOne_known
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.bOne_pos
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_predetermined
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_E
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_achieves
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_719
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_pos
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_flow
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polOne_presentValue
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.pvSurplus_adapted
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.E_pvSurplus_pos
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwo_achieves
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.cTwo_pos_known
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwo_E
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwo_flow
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.polTwo_presentValue
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.policies_differ
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.presentValue_zero_nominal
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.onePeriod_price_zero
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.qe_tradeoff
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.qe_tradeoff_strict
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.qe_negative_position
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.offset_shock
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.offset_shock_cost
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.end_of_period_value
#print axioms Cochrane.LongTermDebtDynamics.PolicyConstraints.end_of_period_value_nominal
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.steady_state
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.steady_price
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.QEPresentValue
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.Eq723
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.pv_iff_723
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.reserves_formula
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.reserves_unique
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.all_M
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qe_unique
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.solve_tail
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.solve_tail_necessary
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.solve_tail_counterexample
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qeResidual
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qe_exists
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qe_residual_summable
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qe_exists_necessary
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.qe_counterexample
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.pv_iff_724
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.Irrelevance.maturity_irrelevance
#print axioms Cochrane.LongTermDebtDynamics.QuantitativeEasing.strong_qe
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.weight_apply
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.pathZ
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.pathZΩ
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.pathZ_summable_bound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.pathZ_solves
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.hasSum_E_of_dom
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.formulaW_eq_E
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.formulaW_adapted_of_exchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5Pathwise.formulaW_solves_of_exchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.weight_mem_unit
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.frac_le_one
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.weight_series_le
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.pathZΩ_noBuyback
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.formulaW_solves_noBuyback
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.noBuyback_le_maturing
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.fracSold_known
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.eqX
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.equilibrium_of_formulaW_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.maturing_eq_formulaW
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.exists_equilibrium_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.formulaW_ge_surplus
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.existsUnique_of_pos_surplus
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cbD
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cbS
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cb_noBuyback
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cb_predetermined
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cb_bounded
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cb_no_positive_price
#print axioms Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence.cb_pv_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.sum_abs_weight_le
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.RowBoundR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.RandomBound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.rowBoundR_of_randomBound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.randomBound_of_rowBound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.RowBoundR.partial
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.RowBoundR.nonneg
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.weight_series_le
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.pathZΩ_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.E_row_partial
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.abs_term_le
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.row_series
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.unique_of_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.opK
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.iterY
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.opK_sub
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.iterY_bounds
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.exists_bounded_solution
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.existsUnique_bounded_solution
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.SeriesExchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.perfectForesight_seriesExchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.finiteTree_seriesExchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.formulaW_solves_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.theoremW_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.price_unique_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.price_formula_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.sxA
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.sx_rowBoundR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomRow.sx_not_rowBound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.hasDerivAt_E_div
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.pertD
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.pertD_22
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.pertD_ne
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.pertD_predetermined
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0_eq_x0R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.fracA
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.kCoef
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R_pull
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.kCoef_eq
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.hasDerivAt_x0R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.price_two_pos_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R_mono
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R_anti
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R_const
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x0R_strictMono
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x1R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.E_x1_eq_x1R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x1R_split
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.hasDerivAt_x1R
#print axioms Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom.x1R_mono
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.FisherPath
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.bondPrice_eq_prod
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.prod_fgRate
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_fgPrice
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_E0_path
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_expected_inflation
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_no_expected_jump
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_expected_inflation_after
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_valuation
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_priceLevel
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_fg_no_effect
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_fg_lowers
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_fg_mono
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_geometric_value
#print axioms Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty.stoch_fg_jump
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.QEPV
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.resv
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.qe_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.reserves_unique
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.reserves_exist_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.perfectForesight_reserves_exist
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.innovation_form
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.no_reserves_of_news
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.coinS
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.coin_pv
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty.coin_no_reserves
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.tailF
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.tailF_anti
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.tailF_tendsto
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.tailF_nonneg
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.firstIdx
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.tail_le_bound
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.E_tail_tendsto
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.hasSum_E_nonneg
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.seriesExchange
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.formulaW_solves_rowR'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.theoremW_rowR'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange.price_formula_rowR'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.NoSalesAfter
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.fracNew
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.debt_after
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.maturing_after
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.dilution_at
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.fracNew_known
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.innovation_at
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.no_surprise_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5InnovationForm.innovation_rowR
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.resid
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qeImplied
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qe_split
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qe_necessary
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qe_unique
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qe_sufficient
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.qe_exists_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.coin_pv_two
#print axioms Cochrane.LongTermDebtDynamics.TidyR5QEReverse.coin_no_qe
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.condCov
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.RFisher
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.bondPrice_succ_eq
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.bondPrice_cov
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.bondPrice_cov_rate
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.bondPrice_prefix
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.random_valuation
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.random_fg_no_effect
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.random_expected_ratio
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.random_no_expected_jump
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgRate
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgX
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgP
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgX'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgP'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgB
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.coin_E0
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.coin_known
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_adapted
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cgP_adapted
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_fisher
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_fisher'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_pv
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_presentValue
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_presentValue'
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance.cg_counterexample
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cgRate2
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cgRate2_delay
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cgX2
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cgP2
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cg2_fisher
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cg2_presentValue
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cg_horizon_counterexample
#print axioms Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon.cg_cov_zero
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.posEvent
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.levelInd
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.levelIdx
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.levelInd_le
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.levelIdx_ge
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.E_pos_of_E_posEvent_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.E_posEvent_pos_of_E_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.E_pos_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.E_pos_of_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.dilDiff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.dilDiff_eq
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.dilDiff_sign
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.x0R_sub
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.x0R_strict_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.x0R_eq_of_null
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.x0R_strictMono_pos
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullE
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullE_zero
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullE_succ
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullSys
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullSys_pullOut
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullSys_divClosed
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullD
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.nullG
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.null_counterexample
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule.null_counterexample_eqm
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.ae_zero_on_of_setIntegral_nonpos
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.condExp_pos_iff_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.condExp_pos_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.condExp_bot_pos_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M66
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M66_ae_eq
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M_mono_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M_strict_iff_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M_strictMono_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M66_strict_iff_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0M_bot_strict_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.x0_ae_eq_x0M66
#print axioms Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure.eqm_strict_iff_ae
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.FullEqm
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD_predetermined
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD_flow_zero_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD_flow_succ_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD_pv_zero_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollD_pv_succ_iff
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollover_valuation
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.pv_one
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.pvSurplus_one
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.rollB
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.fullEqm_of_known
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg_full
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg'_full
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg2_adapted
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cgP2_adapted
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg2_full
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.coin_rollover_price
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg_flows_counterexample
#print axioms Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows.cg_horizon_flows_counterexample
