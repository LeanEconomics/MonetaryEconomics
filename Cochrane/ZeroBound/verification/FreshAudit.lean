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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
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

namespace Cochrane.ZeroBound

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

end Cochrane.ZeroBound

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

namespace Cochrane.ZeroBound

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

end Cochrane.ZeroBound

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

namespace Cochrane.ZeroBound.ExpectationsFiniteTree

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

end Cochrane.ZeroBound.ExpectationsFiniteTree

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

namespace Cochrane.ZeroBound.ForwardSolution

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

end Cochrane.ZeroBound.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Global multiplicity despite local determinacy (restated from the Woodford Chapter 2 project)

Cochrane (2023), Chapter 20, §20.2.1, pp. 471–474: the one-dimensional piecewise-linear
perfect-foresight dynamics `π_{t+1} = f(π_t)` of (20.2)–(20.4) and Figure 20.3 are studied with
the lemmas of this module, restated verbatim (namespace adapted) from the Woodford Chapter 2
project, whose docstrings cite Woodford (2003)'s pages (the copy in the Cochrane Chapter 16
project, `NewKeynesianSelection`, served as the starting point).

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

namespace Cochrane.ZeroBound.GlobalDynamics

open Filter Topology

/-! ## L5: one-dimensional monotone maps -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), eq. (1.8), p. 67: the opportunity cost of money
`Δ_t = (i_t − i^m_t)/(1 + i_t)`; with `i^m = 0` (as in (4.2)) it is `i/(1+i)`. -/
noncomputable def oppCost (i im : ℝ) : ℝ := (i - im) / (1 + i)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), (4.2), p. 124: with `i^m = 0` the opportunity cost is `i/(1+i)`. -/
theorem oppCost_zero (i : ℝ) : oppCost i 0 = i / (1 + i) := by
  simp [oppCost]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), §1, p. 66: the perfect-foresight discount factor
`Q_{t,T} = ∏_{s=t}^{T-1} Q_{s,s+1}`. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), (4.2), p. 124 with the government flow budget constraint (1.25), p. 73
(the text cites (1.7), error E9): under `T_t = αW_t − Δ_tM_t` the government budget gives
`Q_{t,t+1}W_{t+1} = (1 − α)W_t`. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), eq. (4.5), p. 125: a perfect-foresight inflation path under the rule
`i_t = φ(Π_t)`: positive inflation with
`Π_{t+1}/λ(φ(Π_{t+1})) = β(1 + φ(Π_t))/λ(φ(Π_t))` at all dates. -/
def IsPath45 (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧
    ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), eq. (4.6), p. 125: the cashless/separable dynamics
`Π_{t+1} = β(1 + φ(Π_t))` with positive inflation. -/
def IsPath46 (β : ℝ) (φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧ ∀ t, Pi_ (t + 1) = β * (1 + φ (Pi_ t))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), (4.5) ⇒ (4.6), p. 125: in the cashless limit / separable case `λ` is a
positive constant and (4.5) reduces to (4.6). -/
theorem isPath45_iff_isPath46_of_const {β c : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hc : 0 < c) :
    IsPath45 β (fun _ => c) φ Pi_ ↔ IsPath46 β φ Pi_ := by
  unfold IsPath45 IsPath46
  refine and_congr Iff.rfl (forall_congr' fun t => ?_)
  rw [div_left_inj' hc.ne']

/-! ## Existence of solutions and the bound (4.4) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), eq. (4.6), p. 125: the map `Π ↦ β(1 + φ(Π))` (the solid curve of
Figure 2.4). -/
def map46 (β : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => β * (1 + φ x)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 125: the solution of (4.6) started from `Π₀`. -/
def orbit46 (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) : ℕ → ℝ := fun t => (map46 β φ)^[t] Pi0

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 125: the orbit obeys (4.6). -/
theorem orbit46_succ (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) (t : ℕ) :
    orbit46 β φ Pi0 (t + 1) = map46 β φ (orbit46 β φ Pi0 t) :=
  Function.iterate_succ_apply' _ _ _

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 125: a solution of (4.6) is pinned down by its initial inflation
rate. -/
theorem isPath46_eq_orbit {β : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (h : IsPath46 β φ Pi_) :
    Pi_ = orbit46 β φ (Pi_ 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ n ih => rw [h.2 n, orbit46_succ, ih]; rfl

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), eq. (4.4), p. 124: the summand `β^T λ(i_T)[ȳ + i_T/(1+i_T) L(i_T)]`. -/
noncomputable def bound44Term (β ybar : ℝ) (lam L : ℝ → ℝ) (i : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * (lam (i T) * (ybar + i T / (1 + i T) * L (i T)))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 124: the target `Π*` with `φ(Π*) = β⁻¹Π* − 1` is a steady state of
(4.6). -/
theorem target_isFixed {β Pis : ℝ} {φ : ℝ → ℝ} (hβ : β ≠ 0) (htarget : φ Pis = Pis / β - 1) :
    map46 β φ Pis = Pis := by
  simp only [map46, htarget]
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 125: the derivative of the map (4.6) is `βφ'`. -/
theorem hasDerivAt_map46 {β d x : ℝ} {φ : ℝ → ℝ} (hd : HasDerivAt φ d x) :
    HasDerivAt (map46 β φ) (β * d) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).add hd).const_mul β
  rw [zero_add] at h
  exact h

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 125: the Taylor coefficient `φ_π = Π*φ'(Π*)/(1 + φ(Π*))` (the elasticity
of `1 + i` with respect to `Π` at the target) equals `βφ'(Π*)`, the slope of the curve of
Figure 2.4 at `Π*`; so "the Taylor principle" `φ_π > 1` is "the curve cuts the diagonal from
below". -/
theorem taylorCoeff_eq_slope {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : 0 < Pis)
    (htarget : φ Pis = Pis / β - 1) : Pis * d / (1 + φ Pis) = β * d := by
  rw [htarget, show 1 + (Pis / β - 1) = Pis / β by ring]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 126, "eventually, actual deflation": with `β < 1`, inflation along a
self-fulfilling deflation is eventually below one. -/
theorem deflation46_eventually_deflation {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1)
    (hpath : IsPath46 β φ Pi_) (h0 : Pi_ 0 ∈ Set.Ioo β Pis) : ∀ᶠ t in atTop, Pi_ t < 1 :=
  (self_fulfilling_deflation46 hβ hφ0 hcont hφβ hbelow hpath h0).2.2.eventually
    (gt_mem_nhds hβ1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 127, error E6: the policy function of the counterexample,
`φ(Π) = max(0, min(3Π − 2, 2))` (with `β = 1/2`, `Π* = 1`): it saturates at `2`, so the curve of
Figure 2.4 crosses the diagonal again at `Π = 3/2`. -/
noncomputable def phiCE (x : ℝ) : ℝ := max 0 (min (3 * x - 2) 2)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), (4.5), p. 127: the steady states of (4.5) are those of (4.6), since `λ`
cancels at a constant inflation rate. -/
theorem steady_state45_iff {β x : ℝ} {lam φ : ℝ → ℝ} (hl : 0 < lam (φ x)) :
    x / lam (φ x) = β * (1 + φ x) / lam (φ x) ↔ map46 β φ x = x := by
  rw [div_left_inj' hl.ne', map46, eq_comm]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
Woodford (2003), p. 127: the policy rule of the counterexample showing that some restriction
on how strongly `λ` increases is needed: `φ(Π) = max(0, 3Π − 2)` (`β = 1/2`, `Π* = 1`). -/
noncomputable def phiCE45 (x : ℝ) : ℝ := max 0 (3 * x - 2)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §20.2.1).
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

end Cochrane.ZeroBound.GlobalDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The new-Keynesian model at an interest-rate peg: the zero bound

Cochrane (2023), Chapter 20, §20.1, pp. 465–469.

At the zero bound the nominal rate is pegged, `i_t = ī` (`ī = 0` at the bound). The book's three
claims about the standard new-Keynesian model (5.1)–(5.2), p. 118, at a peg are made precise here
for an arbitrary `ExpectationSystem` (so under perfect foresight and under uncertainty):

* p. 467, "stable": the two roots (5.6), p. 119, straddle the unit circle, `λ₂ < 1 < λ₁`
  (`lam2_lt_one`, `one_lt_lam1`, `pegMatrix_roots`); every bounded equilibrium converges in
  expectation to the steady state `π = ī` (`peg_expected_converges`).
* p. 467, "indeterminate": the backward matrix fails Schur–Cohn (`peg_not_schurStable`), so the
  system is not determinate (`peg_not_determinate`). Exact characterisation of all bounded
  equilibria (`peg_equilibrium_iff`, `peg_equilibrium_char`): the unstable combination
  `κx_t + (λ₂ − 1)π_t` is pinned (`peg_slaving`), and `p_t = π_t − ī` is ANY bounded solution
  of `p_t = λ₁ E_t p_{t+1}` — a sunspot recursion `p_{t+1} = λ₁⁻¹p_t + δ_{t+1}` driven by an
  arbitrary bounded martingale difference `δ` (`sunspot_equilibrium`, `sunspot_innovation`);
  uncountably many equilibria (`peg_continuum`) and a genuinely random sunspot on a coin-flip
  tree (`coin_sunspot_equilibrium`).
* p. 469, "add active fiscal policy, and inflation can be stable, determinate and quiet at the
  zero bound": with the linearised valuation equation (5.13), p. 121, at a constant interest
  rate, `ΔE_{t+1} ∑ ρʲ π_{t+1+j} = −ε_{t+1}` (genuine `HasSum`), there is exactly one bounded
  equilibrium (`fiscal_selects`); its unexpected inflation is pinned by fiscal news
  (`fiscal_unexpected_inflation`), it is stable (`fiscal_stable`), quiet without fiscal news
  (`fiscal_quiet`), and a date-0 deflation requires a fiscal contraction
  (`deflation_iff_fiscal_contraction`).
-/

namespace Cochrane.ZeroBound.ZLBPeg

open Filter Topology
open Cochrane.ZeroBound

/-! ## The roots (5.6) -/

/-- Cochrane (2023), eq. (5.6), p. 119: the larger root `λ₁`; the discriminant
`(1 + β + σκ)² − 4β` is the core `discQ` of trace `1 + β + σκ` and determinant `β`. -/
noncomputable def lam1 (β σ κ : ℝ) : ℝ :=
  ((1 + β + σ * κ) + Real.sqrt (discQ (1 + β + σ * κ) β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the smaller root `λ₂`. -/
noncomputable def lam2 (β σ κ : ℝ) : ℝ :=
  ((1 + β + σ * κ) - Real.sqrt (discQ (1 + β + σ * κ) β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the discriminant `(1 + β + σκ)² − 4β` is positive
(`β > 0`, `σκ > 0`). -/
theorem disc_pos {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 0 < discQ (1 + β + σ * κ) β := by
  unfold discQ
  nlinarith [sq_nonneg (1 - β), mul_pos hσκ hβ, sq_nonneg (σ * κ)]

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ + λ₂ = 1 + β + σκ`. -/
theorem lam_add (β σ κ : ℝ) : lam1 β σ κ + lam2 β σ κ = 1 + β + σ * κ := by
  unfold lam1 lam2
  ring

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁λ₂ = β`. -/
theorem lam_mul {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : lam1 β σ κ * lam2 β σ κ = β := by
  have hs : Real.sqrt (discQ (1 + β + σ * κ) β) ^ 2 = (1 + β + σ * κ) ^ 2 - 4 * β :=
    Real.sq_sqrt (disc_pos hβ hσκ).le
  unfold lam1 lam2
  linear_combination (-1 / 4 : ℝ) * hs

/-- Cochrane (2023), eq. (5.6), p. 119: both roots solve `λ² − (1 + β + σκ)λ + β = 0`. -/
theorem lam_root {β σ κ lam : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (h : lam = lam1 β σ κ ∨ lam = lam2 β σ κ) : lam ^ 2 - (1 + β + σ * κ) * lam + β = 0 := by
  have ha := lam_add β σ κ
  have hm := lam_mul hβ hσκ
  rcases h with rfl | rfl
  · linear_combination lam1 β σ κ * ha - hm
  · linear_combination lam2 β σ κ * ha - hm

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ ≤ λ₁`. -/
theorem lam2_le_lam1 (β σ κ : ℝ) : lam2 β σ κ ≤ lam1 β σ κ := by
  unfold lam1 lam2
  linarith [Real.sqrt_nonneg (discQ (1 + β + σ * κ) β)]

/-- Cochrane (2023), p. 119 ("`λ₁ > 1`"): the larger root lies outside the unit circle. -/
theorem one_lt_lam1 {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 1 < lam1 β σ κ := by
  have h1 := lam_add β σ κ
  have h2 := lam_mul hβ hσκ
  have h3 := lam2_le_lam1 β σ κ
  by_contra h
  push Not at h
  nlinarith

/-- Cochrane (2023), p. 119 ("`λ₂ < 1`"): the smaller root lies inside the unit circle. -/
theorem lam2_lt_one {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : lam2 β σ κ < 1 := by
  have h1 := lam_add β σ κ
  have h2 := lam_mul hβ hσκ
  have h3 := one_lt_lam1 hβ hσκ
  nlinarith

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ > 0`. -/
theorem lam2_pos {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 0 < lam2 β σ κ := by
  have h2 := lam_mul hβ hσκ
  have h3 := one_lt_lam1 hβ hσκ
  nlinarith

/-! ## The matrix form and indeterminacy -/

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118, at a peg: the backward form
`(x_t, π_t) = A E_t (x_{t+1}, π_{t+1}) + w` has `A = [[1, σ], [κ, β + σκ]]`. -/
def pegMatrix (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, σ; κ, β + σ * κ]

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118: the constant forcing `w = (−σī, −κσī)` of the
backward form at the peg `i_t = ī`. -/
def pegForcing {Ω : Type*} (σ κ ibar : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun _ => ![fun _ => -(σ * ibar), fun _ => -(κ * σ * ibar)]

/-- Cochrane (2023), eq. (5.6), p. 119: trace `1 + β + σκ` and determinant `β` of the peg
matrix, so its characteristic polynomial is the quadratic of (5.6). -/
theorem pegMatrix_tr_det (β σ κ : ℝ) :
    tr2 (pegMatrix β σ κ) = 1 + β + σ * κ ∧ det2 (pegMatrix β σ κ) = β := by
  simp only [tr2, det2, pegMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> ring

/-- Cochrane (2023), eq. (5.6), p. 119: the eigenvalues of the peg matrix are `λ₁` and `λ₂`,
and they straddle the unit circle (`‖λ₂‖ < 1 < ‖λ₁‖`), p. 467. -/
theorem pegMatrix_roots {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) :
    root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam1 β σ κ : ℂ) ∧
      root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam2 β σ κ : ℂ) ∧
      ‖root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ))‖ < 1 ∧
      1 < ‖root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ))‖ := by
  obtain ⟨ht, hd⟩ := pegMatrix_tr_det β σ κ
  have h0 : 0 ≤ discQ (1 + β + σ * κ) β := (disc_pos hβ hσκ).le
  have e1 : root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam1 β σ κ : ℂ) := by
    rw [ht, hd]
    unfold root₁
    simp only [h0, ↓reduceIte, lam1]
  have e2 : root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam2 β σ κ : ℂ) := by
    rw [ht, hd]
    unfold root₂
    simp only [h0, ↓reduceIte, lam2]
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lam2_pos hβ hσκ)]
    exact lam2_lt_one hβ hσκ
  · rw [e1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans one_pos (one_lt_lam1 hβ hσκ))]
    exact one_lt_lam1 hβ hσκ

/-- Cochrane (2023), §20.1, p. 467: the peg matrix fails the Schur–Cohn condition. -/
theorem peg_not_schurStable {β σ κ : ℝ} (hσκ : 0 < σ * κ) :
    ¬ SchurStable (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) := by
  obtain ⟨ht, hd⟩ := pegMatrix_tr_det β σ κ
  rw [ht, hd]
  rintro ⟨-, h⟩
  have := le_abs_self (1 + β + σ * κ)
  linarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118, with `i_t = ī` (§20.1, p. 467): the IS curve
`x_t = E_t x_{t+1} − σ(ī − E_t π_{t+1})` and the Phillips curve `π_t = βE_tπ_{t+1} + κx_t`, at
every date and state. -/
def PegEq (β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = 𝔼.E t (x (t + 1)) ω - σ * (ibar - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), (5.1)–(5.2), p. 118: `E_t` of an affine combination. -/
theorem E_affine2 (t : ℕ) (a b c : ℝ) (y z : Ω → ℝ) (ω : Ω) :
    𝔼.E t (fun ω => a * y ω + b * z ω + c) ω = a * 𝔼.E t y ω + b * 𝔼.E t z ω + c := by
  have h : (fun ω => a * y ω + b * z ω + c) = a • y + b • z + fun _ => c := by
    funext ω
    simp
  rw [h, map_add, map_add, map_smul, map_smul, 𝔼.const]
  simp

/-- Cochrane (2023), (5.1)–(5.2), p. 118: the model at a peg is the backward system
`z_t = A E_t z_{t+1} + w` of the core module with `A = pegMatrix`. -/
theorem pegEq_iff_solves (β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) :
    PegEq 𝔼 β σ κ ibar x π ↔
      𝔼.Solves (pegMatrix β σ κ) (pegForcing σ κ ibar) (fun t => ![x t, π t]) := by
  constructor
  · intro h t i
    fin_cases i
    · funext ω
      obtain ⟨h1, -⟩ := h t ω
      simp [pegMatrix, pegForcing]
      linarith
    · funext ω
      obtain ⟨h1, h2⟩ := h t ω
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, pegMatrix, Matrix.of_apply, Matrix.cons_val_zero, pegForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, h1]
      ring
  · intro h t ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      pegMatrix, Matrix.of_apply, one_smul, Matrix.cons_val_one, pegForcing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at h0 h1
    refine ⟨by linarith, ?_⟩
    rw [h1, h0]
    ring

/-- Cochrane (2023), §20.1, p. 467 ("off-the-shelf new-Keynesian models predict that inflation
is indeterminate at the zero bound"): the peg system is not determinate. -/
theorem peg_not_determinate [Nonempty Ω] {β σ κ : ℝ} (hσκ : 0 < σ * κ) :
    ¬ 𝔼.Determinate (pegMatrix β σ κ) :=
  fun h => peg_not_schurStable hσκ ((𝔼.determinate_iff _).mp h)

/-- Cochrane (2023), §20.1, p. 467: the steady state at the peg, `π = ī`,
`x = (1 − β)ī/κ`. -/
theorem peg_steady {β σ κ : ℝ} (hκ : κ ≠ 0) (ibar : ℝ) :
    PegEq 𝔼 β σ κ ibar (fun _ _ => (1 - β) * ibar / κ) (fun _ _ => ibar) := by
  intro t ω
  simp only [𝔼.const]
  constructor
  · ring
  · field_simp
    ring

/-! ## All bounded equilibria at the peg -/

/-- Cochrane (2023), §20.1, p. 467: the combination `q_t = κx_t + (λ − 1)π_t + (β − λ)ī`
attached to a root `λ` of (5.6). -/
def pegQ (β κ ibar lam : ℝ) (x π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => κ * x t ω + (lam - 1) * π t ω + (β - lam) * ibar

/-- Cochrane (2023), §20.1, p. 467, eq. (5.6): for a root `λ`, `q_t = λ E_t q_{t+1}`. -/
theorem peg_q_step {β σ κ ibar lam : ℝ} (hlam : lam ^ 2 - (1 + β + σ * κ) * lam + β = 0)
    {x π : ℕ → Ω → ℝ} (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) :
    pegQ β κ ibar lam x π t = lam • 𝔼.E t (pegQ β κ ibar lam x π (t + 1)) := by
  funext ω
  obtain ⟨h1, h2⟩ := h t ω
  rw [show pegQ β κ ibar lam x π (t + 1) = fun ω => κ * x (t + 1) ω + (lam - 1) * π (t + 1) ω +
    (β - lam) * ibar from rfl, Pi.smul_apply, smul_eq_mul, E_affine2]
  simp only [pegQ]
  linear_combination (lam - 1) * h2 + lam * κ * h1 +
    (ibar - 𝔼.E t (π (t + 1)) ω) * hlam

/-- Cochrane (2023), §20.1, p. 467: in a bounded equilibrium the unstable combination is
pinned, `κx_t + (λ₂ − 1)π_t = (λ₂ − β)ī`. -/
theorem peg_slaving {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Ω → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) (ω : Ω) :
    κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar := by
  set l := lam2 β σ κ
  have hl : |l| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [lam2_pos hβ hσκ, lam2_lt_one hβ hσκ]
  obtain ⟨M1, hM1⟩ := hbx
  obtain ⟨M2, hM2⟩ := hbπ
  have hq : BoundedProc (pegQ β κ ibar l x π) := by
    refine ⟨|κ| * M1 + |l - 1| * M2 + |(β - l) * ibar|, fun t ω => ?_⟩
    simp only [pegQ]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM1 t ω) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM2 t ω) (abs_nonneg _)
  have h0 := 𝔼.forward_unique (u := 0) (z₁ := pegQ β κ ibar l x π) (z₂ := 0) hl
    (fun t => by
      rw [Pi.zero_apply, add_zero]
      exact peg_q_step 𝔼 (lam_root hβ hσκ (Or.inr rfl)) h t)
    (fun t => by simp) hq ⟨0, fun _ _ => by simp⟩
  have := congrFun (congrFun h0 t) ω
  simp only [pegQ, Pi.zero_apply] at this
  linarith

/-- Cochrane (2023), §20.1, p. 467: in a bounded equilibrium inflation deviations obey
`π_t − ī = λ₁(E_tπ_{t+1} − ī)`, i.e. `E_t(π_{t+1} − ī) = λ₁⁻¹(π_t − ī)`: stable forward. -/
theorem peg_pi_rec {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Ω → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) (ω : Ω) :
    π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar) := by
  have hs := peg_slaving 𝔼 hβ hσκ hbx hbπ h t ω
  obtain ⟨-, h2⟩ := h t ω
  have hm := lam_mul hβ hσκ
  have hp := lam2_pos hβ hσκ
  have key : lam2 β σ κ * ((π t ω - ibar) - lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar)) = 0 := by
    linear_combination h2 + hs - (𝔼.E t (π (t + 1)) ω - ibar) * hm
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · linarith

/-- Cochrane (2023), §20.1, p. 467 (converse): the slaving relation and the stable recursion
imply the model equations (no boundedness needed). -/
theorem pegEq_of_slaving {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ}
    (hs : ∀ t ω, κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar)
    (hr : ∀ t ω, π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar)) :
    PegEq 𝔼 β σ κ ibar x π := by
  intro t ω
  have hx : x (t + 1) = fun ω => (-(lam2 β σ κ - 1) / κ) * π (t + 1) ω + 0 * π (t + 1) ω +
      (lam2 β σ κ - β) * ibar / κ := by
    funext ω
    have := hs (t + 1) ω
    field_simp
    linarith
  have hEx : 𝔼.E t (x (t + 1)) ω = (-(lam2 β σ κ - 1) / κ) * 𝔼.E t (π (t + 1)) ω +
      (lam2 β σ κ - β) * ibar / κ := by
    rw [hx, E_affine2]
    ring
  have hm := lam_mul hβ hσκ
  have ha := lam_add β σ κ
  have h1 := hs t ω
  have h2 := hr t ω
  have hEx' : κ * 𝔼.E t (x (t + 1)) ω = -(lam2 β σ κ - 1) * 𝔼.E t (π (t + 1)) ω +
      (lam2 β σ κ - β) * ibar := by
    rw [hEx]
    field_simp
  constructor
  · apply mul_left_cancel₀ hκ
    linear_combination h1 - hEx' - (lam2 β σ κ - 1) * h2 +
      (𝔼.E t (π (t + 1)) ω - ibar) * (ha - hm)
  · linear_combination -h1 + lam2 β σ κ * h2 + (𝔼.E t (π (t + 1)) ω - ibar) * hm

/-- Cochrane (2023), §20.1, p. 467: a bounded pair `(x, π)` is an equilibrium at the peg iff
the unstable combination is pinned and `π − ī` follows the stable recursion. -/
theorem peg_equilibrium_iff {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    PegEq 𝔼 β σ κ ibar x π ↔
      (∀ t ω, κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar) ∧
        ∀ t ω, π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar) :=
  ⟨fun h => ⟨peg_slaving 𝔼 hβ hσκ hbx hbπ h, peg_pi_rec 𝔼 hβ hσκ hbx hbπ h⟩,
    fun h => pegEq_of_slaving 𝔼 hβ hσκ hκ h.1 h.2⟩

/-- Cochrane (2023), §20.1, p. 467: the inflation path `π_t = ī + p_t`. -/
def pegPi (ibar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => ibar + p t ω

/-- Cochrane (2023), §20.1, p. 467: the output path `x_t = ((1 − β)ī + (1 − λ₂)p_t)/κ`. -/
noncomputable def pegX (β σ κ ibar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ((1 - β) * ibar + (1 - lam2 β σ κ) * p t ω) / κ

/-- Cochrane (2023), §20.1, p. 467: `E_s π_t = ī + E_s p_t`. -/
theorem E_pegPi (s t : ℕ) (ibar : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) :
    𝔼.E s (pegPi ibar p t) ω = ibar + 𝔼.E s (p t) ω := by
  have h := E_affine2 𝔼 s 1 0 ibar (p t) (p t) ω
  have e : (fun ω => 1 * p t ω + 0 * p t ω + ibar) = pegPi ibar p t := by
    funext ω
    simp [pegPi]
    ring
  rw [e] at h
  rw [h]
  ring

/-- Cochrane (2023), §20.1, p. 467: every solution of `p_t = λ₁ E_t p_{t+1}` gives an
equilibrium at the peg. -/
theorem pegEq_of_sunspot {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {p : ℕ → Ω → ℝ} (hp : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p) :
    PegEq 𝔼 β σ κ ibar (pegX β σ κ ibar p) (pegPi ibar p) := by
  refine pegEq_of_slaving 𝔼 hβ hσκ hκ (fun t ω => ?_) (fun t ω => ?_)
  · simp only [pegX, pegPi]
    field_simp
    ring
  · rw [E_pegPi]
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [pegPi]
    rw [this]
    ring

/-- Cochrane (2023), §20.1, p. 467: every bounded equilibrium is of the form
`π = ī + p`, `x = pegX p` with `p` a bounded solution of `p_t = λ₁E_tp_{t+1}`. -/
theorem peg_equilibrium_char {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) :
    ∃ p, ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p ∧ BoundedProc p ∧
      x = pegX β σ κ ibar p ∧ π = pegPi ibar p := by
  obtain ⟨M, hM⟩ := hbπ
  refine ⟨fun t ω => π t ω - ibar, fun t => ?_, ⟨M + |ibar|, fun t ω => ?_⟩, ?_, ?_⟩
  · funext ω
    have hr := peg_pi_rec 𝔼 hβ hσκ hbx ⟨M, hM⟩ h t ω
    have hE := E_affine2 𝔼 t 1 0 (-ibar) (π (t + 1)) (π (t + 1)) ω
    have e : (fun ω => 1 * π (t + 1) ω + 0 * π (t + 1) ω + -ibar) =
        fun ω => π (t + 1) ω - ibar := by
      funext ω
      ring
    rw [e] at hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    rw [hE, hr]
    ring
  · exact (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  · funext t ω
    have hs := peg_slaving 𝔼 hβ hσκ hbx ⟨M, hM⟩ h t ω
    simp only [pegX]
    field_simp
    linarith
  · funext t ω
    simp [pegPi]

/-! ## Sunspots -/

/-- Cochrane (2023), §20.1, p. 467 and Figure 16.2: for any `p₀` known at date 0 and any
bounded martingale-difference sunspot `δ`, the recursion `p_{t+1} = λ₁⁻¹p_t + δ_{t+1}` (core
`sunspotFamily`) gives a bounded adapted equilibrium at the peg. -/
theorem sunspot_equilibrium {β σ κ ibar B Mδ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ ω, |p0 ω| ≤ B)
    (hδa : 𝔼.Adapted δ) (hδb : ∀ t ω, |δ t ω| ≤ Mδ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    let p := ForwardSolution.sunspotFamily (lam1 β σ κ) 0 δ p0
    PegEq 𝔼 β σ κ ibar (pegX β σ κ ibar p) (pegPi ibar p) ∧
      𝔼.Adapted (pegX β σ κ ibar p) ∧ 𝔼.Adapted (pegPi ibar p) ∧
      BoundedProc (pegX β σ κ ibar p) ∧ BoundedProc (pegPi ibar p) := by
  intro p
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 hp0 hua hδa hδ
  have hpa : 𝔼.Adapted p := ForwardSolution.sunspotFamily_adapted 𝔼 hp0 hua hδa
  obtain ⟨K, hK⟩ : BoundedProc p :=
    ForwardSolution.sunspotFamily_bounded (by rw [abs_of_pos (by linarith)]; exact hl1) hp0b
      (Mu := 0) (fun _ _ => by simp) hδb
  refine ⟨pegEq_of_sunspot 𝔼 hβ hσκ hκ hsol, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · funext ω
    have e : pegX β σ κ ibar p t =
        fun ω => ((1 - lam2 β σ κ) / κ) * p t ω + 0 * p t ω + (1 - β) * ibar / κ := by
      funext ω
      simp only [pegX]
      field_simp
      ring
    rw [e, E_affine2, hpa t]
  · funext ω
    rw [E_pegPi, hpa t]
    rfl
  · refine ⟨|(1 - β) * ibar / κ| + |(1 - lam2 β σ κ) / κ| * K, fun t ω => ?_⟩
    have e : pegX β σ κ ibar p t ω = (1 - β) * ibar / κ + (1 - lam2 β σ κ) / κ * p t ω := by
      simp only [pegX]
      field_simp
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
  · exact ⟨|ibar| + K, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hK t ω))⟩

/-- Cochrane (2023), §20.1, p. 467: in the sunspot equilibrium the inflation surprise is the
sunspot, `π_{t+1} − E_tπ_{t+1} = δ_{t+1}`. -/
theorem sunspot_innovation {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) (ω : Ω) :
    let p := ForwardSolution.sunspotFamily (lam1 β σ κ) 0 δ p0
    pegPi ibar p (t + 1) ω - 𝔼.E t (pegPi ibar p (t + 1)) ω = δ (t + 1) ω := by
  intro p
  have hl0 : lam1 β σ κ ≠ 0 := by linarith [one_lt_lam1 hβ hσκ]
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 hp0 hua hδa hδ
  have hs := congrFun (hsol t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at hs
  rw [E_pegPi]
  have hsucc : p (t + 1) ω = (lam1 β σ κ)⁻¹ * (p t ω - 0) + δ (t + 1) ω := by
    simp [p, ForwardSolution.sunspotFamily_succ]
  simp only [pegPi]
  rw [hsucc, hs]
  field_simp
  ring

/-- Cochrane (2023), §20.1, p. 467 ("inflation is stable at the zero bound"): in every bounded
equilibrium, expected inflation converges to the peg, `E_s π_{s+k} → ī` as `k → ∞`. -/
theorem peg_expected_converges {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π)
    (h : PegEq 𝔼 β σ κ ibar x π) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (π (s + k)) ω) atTop (𝓝 ibar) := by
  obtain ⟨p, hp, -, -, hπ⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ hbx hbπ h
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  have hpa : 𝔼.Adapted p := fun t => by
    funext ω
    have := congrFun (hπa t) ω
    rw [hπ, E_pegPi] at this
    simp only [pegPi] at this
    linarith
  have har : 𝔼.IsAR1 (lam1 β σ κ)⁻¹ p := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  have e : (fun k => 𝔼.E s (π (s + k)) ω) =
      fun k => ibar + (lam1 β σ κ)⁻¹ ^ k * p s ω := by
    funext k
    rw [hπ, E_pegPi, 𝔼.ar1_iterate har s k]
    rfl
  rw [e]
  have h0 : Tendsto (fun k : ℕ => (lam1 β σ κ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1)
  simpa using (h0.mul_const (p s ω)).const_add ibar

/-- Cochrane (2023), §20.1, p. 467 ("there are many equilibria"): the set of bounded adapted
equilibria at the peg is uncountable. -/
theorem peg_continuum [Nonempty Ω] {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hκ : κ ≠ 0) :
    ¬ {z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2}.Countable := by
  intro hc
  set S := {z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2} with hS
  let f : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) := fun c =>
    (pegX β σ κ ibar (ForwardSolution.sunspotFamily (lam1 β σ κ) 0 0 (fun _ => c)),
      pegPi ibar (ForwardSolution.sunspotFamily (lam1 β σ κ) 0 0 (fun _ => c)))
  have hmaps : Set.MapsTo f Set.univ S := fun c _ => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := sunspot_equilibrium 𝔼 (ibar := ibar) (B := |c|) (Mδ := 0)
      hβ hσκ hκ (p0 := fun _ => c) (δ := 0) (𝔼.const 0 c) (fun _ => le_rfl)
      (fun t => by simp) (fun _ _ => by simp) (fun t => by simp)
    exact ⟨h1, h2, h3, h4, h5⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Prod.snd h) 0) ω
    simpa [f, pegPi, ForwardSolution.sunspotFamily] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-- Cochrane (2023), §20.1, p. 467 ("the economy can jump between them following sunspots"):
on the coin-flip tree there is a bounded adapted equilibrium at the peg whose date-1 inflation
differs across states, driven by a pure sunspot. -/
theorem coin_sunspot_equilibrium {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hκ : κ ≠ 0) :
    ∃ x π : ℕ → Bool × Bool → ℝ, PegEq ExpectationsFiniteTree.coinSystem β σ κ ibar x π ∧
      ExpectationsFiniteTree.coinSystem.Adapted x ∧
      ExpectationsFiniteTree.coinSystem.Adapted π ∧ BoundedProc x ∧ BoundedProc π ∧
      π 1 (true, true) ≠ π 1 (false, true) := by
  set δ := ExpectationsFiniteTree.coinAR1 0
  have har := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hδb : ∀ t ω, |δ t ω| ≤ 1 := by
    intro t ω
    cases t with
    | zero => simp [δ, ExpectationsFiniteTree.coinAR1]
    | succ t =>
      simp only [δ, ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
        ExpectationsFiniteTree.coinShock]
      split_ifs <;> norm_num
  obtain ⟨h1, h2, h3, h4, h5⟩ := sunspot_equilibrium ExpectationsFiniteTree.coinSystem
    (ibar := ibar) (B := 0) hβ hσκ hκ (p0 := fun _ => 0) (δ := δ)
    (ExpectationsFiniteTree.coinSystem.const 0 0) (fun _ => by simp) har.1 hδb
    (fun t => by rw [har.2 t, zero_smul])
  refine ⟨_, _, h1, h2, h3, h4, h5, ?_⟩
  obtain ⟨n1, n2, -⟩ := ExpectationsFiniteTree.coinAR1_nondegenerate 0
  simp only [pegPi, ForwardSolution.sunspotFamily, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    sub_zero, smul_eq_mul, mul_zero, zero_add]
  rw [show δ 1 (true, true) = 1 from n1, show δ 1 (false, true) = -1 from n2]
  norm_num

/-! ## Fiscal theory at the peg -/

/-- Cochrane (2023), eq. (5.13), p. 121, with the interest rate constant at `ī` (one-period
debt): the linearised valuation equation `ΔE_{t+1}∑_{j≥0} ρʲπ_{t+1+j} = −ε_{t+1}`, where
`ε_{t+1} = ΔE_{t+1}∑ρʲs̃_{t+1+j}` is the fiscal news, as a genuine sum (`HasSum`). At date 0 the
economy starts from the steady state (date `−1` expectations `E_{−1}π_j = ī`), so the date-0
news sets `∑ρʲ(E₀π_j − ī) = −ε₀`. -/
def Valuation (ρ ibar : ℝ) (ε π : ℕ → Ω → ℝ) : Prop :=
  (∀ ω, HasSum (fun j => ρ ^ j * (𝔼.E 0 (π j) ω - ibar)) (-ε 0 ω)) ∧
    ∀ t ω, HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (π (t + 1 + j)) ω - 𝔼.E t (π (t + 1 + j)) ω))
      (-ε (t + 1) ω)

/-- Cochrane (2023), eq. (5.13), p. 121: for `p` with `E_tp_{t+1} = rp_t` and `0 ≤ ρr < 1`,
the date-0 discounted sum equals `p₀/(1 − ρr)`. -/
theorem valuation_sum0 {ρ r ibar : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r < 1) {p : ℕ → Ω → ℝ}
    (hp : 𝔼.IsAR1 r p) (ω : Ω) :
    HasSum (fun j => ρ ^ j * (𝔼.E 0 (pegPi ibar p j) ω - ibar)) ((1 - ρ * r)⁻¹ * p 0 ω) := by
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_right (p 0 ω)
  convert hg using 1
  funext j
  rw [E_pegPi]
  have := 𝔼.ar1_iterate hp 0 j
  rw [zero_add] at this
  rw [this, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), eq. (5.13), p. 121: for `p` with `E_tp_{t+1} = rp_t`, the discounted
revision of expected inflation equals `(p_{t+1} − rp_t)/(1 − ρr)`. -/
theorem valuation_sum {ρ r ibar : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r < 1) {p : ℕ → Ω → ℝ}
    (hp : 𝔼.IsAR1 r p) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (pegPi ibar p (t + 1 + j)) ω -
      𝔼.E t (pegPi ibar p (t + 1 + j)) ω)) ((1 - ρ * r)⁻¹ * (p (t + 1) ω - r * p t ω)) := by
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_right (p (t + 1) ω - r * p t ω)
  convert hg using 1
  funext j
  rw [E_pegPi, E_pegPi, 𝔼.ar1_iterate hp (t + 1) j]
  have e := 𝔼.ar1_iterate hp t (1 + j)
  rw [show t + (1 + j) = t + 1 + j by ring] at e
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_pow, pow_add]
  ring

/-- Cochrane (2023), §20.1, p. 469: the fiscal-theory equilibrium inflation deviation,
`p₀ = −kε₀`, `p_{t+1} = λ₁⁻¹p_t − kε_{t+1}`, with `k = 1 − ρ/λ₁`. -/
noncomputable def fiscalP (β σ κ ρ : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ForwardSolution.sunspotFamily (lam1 β σ κ) 0 (fun t => (-(1 - ρ * (lam1 β σ κ)⁻¹)) • ε t)
    ((-(1 - ρ * (lam1 β σ κ)⁻¹)) • ε 0)

/-- Cochrane (2023), §20.1, p. 469: any bounded equilibrium satisfying the valuation equation
has inflation `ī + fiscalP`. -/
theorem valuation_pins {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε x π : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π)
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π)
    (hv : Valuation 𝔼 ρ ibar ε π) : π = pegPi ibar (fiscalP β σ κ ρ ε) := by
  obtain ⟨p, hp, -, -, hπ⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ hbx hbπ h
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  set r := (lam1 β σ κ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hl1
  have h0 : 0 ≤ ρ * r := mul_nonneg hρ0 hr0.le
  have h1 : ρ * r < 1 := by nlinarith
  have hk : 0 < 1 - ρ * r := by linarith
  have hpa : 𝔼.Adapted p := fun t => by
    funext ω
    have := congrFun (hπa t) ω
    rw [hπ, E_pegPi] at this
    simp only [pegPi] at this
    linarith
  have har : 𝔼.IsAR1 r p := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul, hr]
    field_simp
    linarith
  rw [hπ] at hv
  have hpeq : p = fiscalP β σ κ ρ ε := by
    funext t ω
    induction t generalizing ω with
    | zero =>
      have := (hv.1 ω).unique (valuation_sum0 𝔼 h0 h1 har ω)
      simp only [fiscalP, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
      rw [← hr]
      field_simp at this ⊢
      linarith
    | succ t ih =>
      have := (hv.2 t ω).unique (valuation_sum 𝔼 h0 h1 har t ω)
      rw [fiscalP, ForwardSolution.sunspotFamily_succ, ← fiscalP]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero,
        smul_eq_mul]
      rw [← ih ω, ← hr]
      field_simp at this ⊢
      linarith
  rw [hπ, hpeq]

/-- Cochrane (2023), §20.1, p. 469 ("Add active fiscal policy to the new-Keynesian model, and
inflation can be stable, determinate, and quiet at the zero bound"): with the valuation equation
(5.13) at the peg, there is exactly one bounded adapted equilibrium, for every bounded adapted
fiscal-news process `ε` (`E_tε_{t+1} = 0`) and every `0 ≤ ρ ≤ 1`. -/
theorem fiscal_selects {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    ∃! z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2 ∧ Valuation 𝔼 ρ ibar ε z.2 := by
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  set r := (lam1 β σ κ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hl1
  have h0 : 0 ≤ ρ * r := mul_nonneg hρ0 hr0.le
  have h1 : ρ * r < 1 := by nlinarith
  have hk : 0 < 1 - ρ * r := by linarith
  set k := 1 - ρ * r with hkdef
  have hk' : 1 - ρ * r ≠ 0 := by linarith
  obtain ⟨Me, hMe⟩ := hεb
  have hνa : 𝔼.Adapted (fun t => (-k) • ε t) := fun t => by rw [map_smul, hεa t]
  have hν0 : 𝔼.E 0 ((-k) • ε 0) = (-k) • ε 0 := by rw [map_smul, hεa 0]
  have hνmd : ∀ t, 𝔼.E t ((fun t => (-k) • ε t) (t + 1)) = 0 := fun t => by
    simp only [map_smul, hεmd t, smul_zero]
  have hνb : ∀ t ω, |((fun t => (-k) • ε t) t) ω| ≤ k * Me := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left (hMe t ω) hk.le
  obtain ⟨he1, he2, he3, he4, he5⟩ := sunspot_equilibrium 𝔼 (ibar := ibar) hβ hσκ hκ hν0
    (hνb 0) hνa hνb hνmd
  have hp : fiscalP β σ κ ρ ε = ForwardSolution.sunspotFamily (lam1 β σ κ) 0
      (fun t => (-k) • ε t) ((-k) • ε 0) := rfl
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol := ForwardSolution.sunspotFamily_solves 𝔼 hl0 hν0 hua hνa hνmd
  have hpa := ForwardSolution.sunspotFamily_adapted 𝔼 (a := lam1 β σ κ) hν0 hua hνa
  have har : 𝔼.IsAR1 r (fiscalP β σ κ ρ ε) := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hsol t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [hp, Pi.smul_apply, smul_eq_mul, hr]
    field_simp
    linarith
  have hval : Valuation 𝔼 ρ ibar ε (pegPi ibar (fiscalP β σ κ ρ ε)) := by
    refine ⟨fun ω => ?_, fun t ω => ?_⟩
    · convert valuation_sum0 𝔼 h0 h1 har ω using 1
      simp only [hp, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
      rw [hkdef]
      field_simp
    · convert valuation_sum 𝔼 h0 h1 har t ω using 1
      simp only [hp, ForwardSolution.sunspotFamily_succ, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, sub_zero, smul_eq_mul]
      generalize ForwardSolution.sunspotFamily (lam1 β σ κ) 0 (fun t => -k • ε t) (-k • ε 0) t ω = S
      have hrl : r * lam1 β σ κ = 1 := by rw [hr]; exact inv_mul_cancel₀ hl0
      rw [hkdef]
      field_simp
      linear_combination S * hrl
  refine ⟨(pegX β σ κ ibar (fiscalP β σ κ ρ ε), pegPi ibar (fiscalP β σ κ ρ ε)),
    ⟨he1, he2, he3, he4, he5, hval⟩, ?_⟩
  rintro ⟨x, π⟩ ⟨g1, -, g3, g4, g5, g6⟩
  have hπ := valuation_pins 𝔼 hβ hσκ hκ hρ0 hρ1 g3 g4 g5 g1 g6
  obtain ⟨q, -, -, hx, hπq⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ g4 g5 g1
  have hq : q = fiscalP β σ κ ρ ε := by
    funext t ω
    have := congrFun (congrFun (hπq.symm.trans hπ) t) ω
    simp only [pegPi] at this
    linarith
  simp only [Prod.mk.injEq]
  exact ⟨hx.trans (by rw [hq]), hπ⟩

/-- Cochrane (2023), §20.1, p. 469: in the fiscal equilibrium, unexpected inflation is pinned
by fiscal news, `π_{t+1} − E_tπ_{t+1} = −(1 − ρ/λ₁)ε_{t+1}`. -/
theorem fiscal_unexpected_inflation {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (t : ℕ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ ε) (t + 1) ω - 𝔼.E t (pegPi ibar (fiscalP β σ κ ρ ε) (t + 1)) ω
      = -(1 - ρ / lam1 β σ κ) * ε (t + 1) ω := by
  set k := 1 - ρ * (lam1 β σ κ)⁻¹
  have hνa : 𝔼.Adapted (fun t => (-k) • ε t) := fun t => by rw [map_smul, hεa t]
  have hν0 : 𝔼.E 0 ((-k) • ε 0) = (-k) • ε 0 := by rw [map_smul, hεa 0]
  have hνmd : ∀ t, 𝔼.E t ((fun t => (-k) • ε t) (t + 1)) = 0 := fun t => by
    simp only [map_smul, hεmd t, smul_zero]
  have := sunspot_innovation 𝔼 (ibar := ibar) hβ hσκ hν0 hνa hνmd t ω
  simp only [smul_eq_mul, Pi.smul_apply] at this
  rw [fiscalP, this, div_eq_mul_inv]

/-- Cochrane (2023), §20.1, p. 469 ("stable"): in the fiscal equilibrium expected inflation
converges to the peg. -/
theorem fiscal_stable {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (pegPi ibar (fiscalP β σ κ ρ ε) (s + k)) ω) atTop (𝓝 ibar) := by
  obtain ⟨z, ⟨g1, -, g3, g4, g5, g6⟩, -⟩ :=
    fiscal_selects 𝔼 (ibar := ibar) hβ hσκ hκ hρ0 hρ1 hεa hεb hεmd
  have hπ := valuation_pins 𝔼 hβ hσκ hκ hρ0 hρ1 g3 g4 g5 g1 g6
  rw [← hπ]
  exact peg_expected_converges 𝔼 hβ hσκ hκ g3 g4 g5 g1 s ω

/-- Cochrane (2023), §20.1, p. 469 ("quiet"): without fiscal news the fiscal equilibrium is the
steady state, `π_t = ī` at every date and state. -/
theorem fiscal_quiet (β σ κ ibar ρ : ℝ) (t : ℕ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ (0 : ℕ → Ω → ℝ)) t ω = ibar := by
  have : fiscalP β σ κ ρ (0 : ℕ → Ω → ℝ) t ω = 0 := by
    induction t generalizing ω with
    | zero => simp [fiscalP, ForwardSolution.sunspotFamily]
    | succ t ih =>
      rw [fiscalP, ForwardSolution.sunspotFamily_succ, ← fiscalP]
      simp [ih]
  simp [pegPi, this]

/-- Cochrane (2023), §20.1, p. 469 ("were a deflation to break out, our fiscal authorities
would not respond with sharp tax increases"): in the fiscal equilibrium a date-0 deflation
below the peg happens iff the date-0 fiscal news is a contraction, `ε₀ > 0`. -/
theorem deflation_iff_fiscal_contraction {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hρ1 : ρ ≤ 1) (ε : ℕ → Ω → ℝ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ ε) 0 ω < ibar ↔ 0 < ε 0 ω := by
  have hl1 := one_lt_lam1 hβ hσκ
  have hr1 : (lam1 β σ κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hr0 : 0 < (lam1 β σ κ)⁻¹ := by positivity
  have hk : 0 < 1 - ρ * (lam1 β σ κ)⁻¹ := by nlinarith
  simp only [pegPi, fiscalP, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

end Cochrane.ZeroBound.ZLBPeg

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An active rule that hits the zero bound

Cochrane (2023), Chapter 20, §20.2.1 "Removing sunspots?", pp. 471–474, and Figure 20.3.

The static-IS model of §16.1, `x_t = −σ(i_t − E_tπ_{t+1} − u_{r,t})`, `π_t = E_tπ_{t+1} + κx_t`,
with the kinked rule (20.1) `i_t = max[π* + φ(π_t − π*), 0]`, for an arbitrary
`ExpectationSystem`.

## Main results

* (20.2): `eq20_2_iff`; in map form `E_tπ_{t+1} = f_u(π_t)`, `eq20_2_iff_map`, with
  `f_u(π) = (π + σκ·max[π* + φ(π − π*), 0] − σκu)/(1 + σκ)` (`fmap`).
* (20.3)/(20.4) with the CORRECTED kink (survey E1, confirmed): the zero-bound branch applies iff
  `π ≤ π*(φ − 1)/φ` (`kink_iff`, `eq20_3`, `eq20_4`); the printed threshold `π* + (φ − 1)` is
  false (`e1_printed_threshold_false`: at the Figure 20.3 values `π = 1.5 < 3` but (20.3) fails).
* The map: continuous, strictly increasing, onto (`fmap_continuous`, `fmap_strictMono`,
  `fmap_surjective`), with slopes `1/(1 + σκ) < 1` and `(1 + φσκ)/(1 + σκ)`, `> 1 ↔ φ > 1`
  (`hasDerivAt_fmap_left`, `hasDerivAt_fmap_right`, `slope_left_lt_one`, `slope_right_gt_one_iff`).
* Steady states (p. 472): `fixed_iff`, `steady_exists_iff` (a steady state exists iff
  `−u ≤ π*(φ − 1)/φ`, then `−u` and `π* + u/(φ − 1)` are the steady states), `fixed_u_zero` (with
  `u = 0`: exactly `0` and `π*`), `steady_states_pushed_in`, `lower_attracting`, `upper_repelling`.
  Survey E2, confirmed: at the Figure 20.3 calibration there is NO steady state during the shock,
  `f_u(π) − π ≥ 1/3` for all `π` (`fig203_no_steady_state`, `fig203_printed_steady_states_false`).
* Global vs local (pp. 473–474), `u = 0`: orbits starting above `π*` explode
  (`orbit_above`), orbits starting below converge to zero inflation and zero rates
  (`orbit_below_tendsto_zero`, `orbit_below_rate_zero`),
  so the bounded orbits are exactly those with `π₀ ≤ π*` (`bounded_orbits_eq`), a continuum,
  while `π*` is the only locally bounded one (`locally_bounded_unique`), also under any
  `ExpectationSystem` (`locally_bounded_unique_E`).
* Figure 20.3 (pp. 472–473): selection by the future rule. `backward_unique`,
  `backward_exists` (for any `ExpectationSystem` the path before `T` is pinned and
  deterministic once `π_T` is), `fig203_selection` (`π_t = π*` for `t ≥ T`, and
  `π₉ = 3/2, π₈ = 9/8, π₇ = 11/16, π₆ = 1/32`), and survey E3, confirmed: the rate lifts off two
  periods before `T`, `i₉ = 1`, `i₈ = 1/4` (`fig203_early_liftoff`). Forward contraction on the
  zero-bound branch and expansion on the active branch (`zlb_branch_contraction`,
  `active_branch_expansion`).
-/

namespace Cochrane.ZeroBound.ZLBRule

open Filter Topology
open Cochrane.ZeroBound

/-- Cochrane (2023), eq. (20.1), p. 472: the rule `i = max[π* + φ(π − π*), 0]`. -/
noncomputable def rule (φ πs π : ℝ) : ℝ := max (πs + φ * (π - πs)) 0

/-- Cochrane (2023), eq. (20.2), p. 472, solved for expected inflation:
`E_tπ_{t+1} = (π_t + σκ i(π_t) − σκu_t)/(1 + σκ)`. -/
noncomputable def fmap (σ κ φ πs u : ℝ) (π : ℝ) : ℝ :=
  (π + σ * κ * rule φ πs π - σ * κ * u) / (1 + σ * κ)

/-- Cochrane (2023), eqs. (20.3)–(20.4), p. 472 (corrected, survey E1): the kink of the map,
`π*(φ − 1)/φ`, where `π* + φ(π − π*) = 0`. -/
noncomputable def kink (φ πs : ℝ) : ℝ := πs * (φ - 1) / φ

/-- Cochrane (2023), eq. (20.4), p. 472: the slope `(1 + φσκ)/(1 + σκ)` of the active branch. -/
noncomputable def slopeR (σ κ φ : ℝ) : ℝ := (1 + φ * (σ * κ)) / (1 + σ * κ)

/-! ## The model and (20.2) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §20.2.1, p. 471 and eq. (20.1), p. 472: `i_t = max[π* + φ(π_t − π*), 0]`,
`x_t = −σ(i_t − E_tπ_{t+1} − u_{r,t})`, `π_t = E_tπ_{t+1} + κx_t`, at every date and state. -/
def ZLBEq (σ κ φ πs : ℝ) (u x π i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = rule φ πs (π t ω) ∧
    x t ω = -σ * (i t ω - 𝔼.E t (π (t + 1)) ω - u t ω) ∧
    π t ω = 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), eq. (20.2), p. 472: eliminating `x`, the model is
`max[π* + φ(π_t − π*), 0] = −π_t/(σκ) + ((1 + σκ)/(σκ))E_tπ_{t+1} + u_{r,t}` (with
`x_t = (π_t − E_tπ_{t+1})/κ`). -/
theorem eq20_2_iff {σ κ φ πs : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (u x π i : ℕ → Ω → ℝ) :
    ZLBEq 𝔼 σ κ φ πs u x π i ↔ ∀ t ω, i t ω = rule φ πs (π t ω) ∧
      x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ ∧
      rule φ πs (π t ω) = -(1 / (σ * κ)) * π t ω +
        ((1 + σ * κ) / (σ * κ)) * 𝔼.E t (π (t + 1)) ω + u t ω := by
  have hs : σ * κ ≠ 0 := mul_ne_zero hσ hκ
  have e : ∀ a b c : ℝ, -(1 / (σ * κ)) * a + ((1 + σ * κ) / (σ * κ)) * b + c =
      (-a + (1 + σ * κ) * b + σ * κ * c) / (σ * κ) := fun a b c => by
    field_simp
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [e, eq_div_iff hs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ := by
      field_simp
      linarith
    refine ⟨h1, hx, ?_⟩
    rw [← h1]
    linear_combination h3 + κ * h2
  · rintro ⟨h1, h2, h3⟩
    have h2' : κ * x t ω = π t ω - 𝔼.E t (π (t + 1)) ω := by
      rw [h2]
      field_simp
    refine ⟨h1, ?_, by linarith⟩
    rw [← h1] at h3
    apply mul_left_cancel₀ hκ
    linear_combination h2' + h3

/-- Cochrane (2023), eq. (20.2), p. 472: in map form, the model is
`E_tπ_{t+1} = f_{u_t}(π_t)` together with the rule and `x_t = (π_t − E_tπ_{t+1})/κ`. -/
theorem eq20_2_iff_map {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (u x π i : ℕ → Ω → ℝ) :
    ZLBEq 𝔼 σ κ φ πs u x π i ↔ ∀ t ω, i t ω = rule φ πs (π t ω) ∧
      x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ ∧
      𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs (u t ω) (π t ω) := by
  have hσ : σ ≠ 0 := by rintro rfl; simp at hσκ
  have hκ : κ ≠ 0 := by rintro rfl; simp at hσκ
  rw [eq20_2_iff 𝔼 hσ hκ]
  refine forall_congr' fun t => forall_congr' fun ω => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  unfold fmap
  have h1 : (1 + σ * κ) ≠ 0 := by linarith
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    field_simp at h
    field_simp
    linarith

/-! ## The branches (20.3)–(20.4) and survey error E1 -/

/-- Cochrane (2023), eqs. (20.3)–(20.4), p. 472 (survey E1): for `φ > 0` the rule is at the
bound, `π* + φ(π − π*) ≤ 0`, iff `π ≤ π*(φ − 1)/φ`. -/
theorem kink_iff {φ πs π : ℝ} (hφ : 0 < φ) : πs + φ * (π - πs) ≤ 0 ↔ π ≤ kink φ πs := by
  unfold kink
  rw [le_div_iff₀ hφ]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), eq. (20.3), p. 472: on the zero-bound branch
`E_tπ_{t+1} = π_t/(1 + σκ) − σκu/(1 + σκ)`. -/
theorem eq20_3 {σ κ φ πs u π : ℝ} (h : πs + φ * (π - πs) ≤ 0) :
    fmap σ κ φ πs u π = 1 / (1 + σ * κ) * π - σ * κ / (1 + σ * κ) * u := by
  unfold fmap rule
  rw [max_eq_right h]
  ring

/-- Cochrane (2023), eq. (20.4), p. 472: on the active branch
`E_tπ_{t+1} − π* = ((1 + φσκ)/(1 + σκ))(π_t − π*) − σκu/(1 + σκ)`. -/
theorem eq20_4 {σ κ φ πs u π : ℝ} (hσκ : 0 < σ * κ) (h : 0 ≤ πs + φ * (π - πs)) :
    fmap σ κ φ πs u π - πs = slopeR σ κ φ * (π - πs) - σ * κ / (1 + σ * κ) * u := by
  unfold fmap rule slopeR
  rw [max_eq_left h]
  have : (1 + σ * κ) ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Figure 20.3 values (`φ = 2`, `π* = 2`): the true kink is `1`, while the
printed threshold `π* + (φ − 1)` is `3`. -/
theorem kink_fig203 : kink 2 2 = 1 ∧ (2 : ℝ) + (2 - 1) = 3 := by
  unfold kink
  norm_num

/-- Cochrane (2023), eq. (20.3), p. 472, survey error E1: the printed side condition
"(20.3) when `π_t < π* + (φ − 1)`" is false. At the Figure 20.3 values (`σ = 1`, `κ = 1/2`,
`φ = 2`, `π* = 2`, `u = 0`), `π = 3/2 < 3` but `E_tπ_{t+1} = 4/3 ≠ 1`, the (20.3) value. -/
theorem e1_printed_threshold_false :
    (3 / 2 : ℝ) < 2 + (2 - 1) ∧ fmap 1 (1 / 2) 2 2 0 (3 / 2) = 4 / 3 ∧
      fmap 1 (1 / 2) 2 2 0 (3 / 2) ≠
        1 / (1 + 1 * (1 / 2)) * (3 / 2) - 1 * (1 / 2) / (1 + 1 * (1 / 2)) * 0 := by
  have h : fmap 1 (1 / 2) 2 2 0 (3 / 2) = 4 / 3 := by
    unfold fmap rule
    rw [max_eq_left (by norm_num)]
    norm_num
  refine ⟨by norm_num, h, ?_⟩
  rw [h]
  norm_num

/-! ## Properties of the map -/

/-- Cochrane (2023), eq. (20.2), p. 472: the map `f_u` is continuous. -/
theorem fmap_continuous (σ κ φ πs u : ℝ) : Continuous (fmap σ κ φ πs u) := by
  unfold fmap rule
  fun_prop

/-- Cochrane (2023), eq. (20.2), p. 472: for `φ ≥ 0` and `σκ > 0` the map is strictly
increasing (both slopes positive). -/
theorem fmap_strictMono {σ κ φ πs u : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) :
    StrictMono (fmap σ κ φ πs u) := by
  intro a b hab
  unfold fmap
  have hr : rule φ πs a ≤ rule φ πs b := by
    unfold rule
    exact max_le_max (by nlinarith) le_rfl
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

/-- Cochrane (2023), eq. (20.2), p. 472: the map is onto, so every `E_tπ_{t+1}` is reached
by exactly one `π_t` (with `fmap_strictMono`). -/
theorem fmap_surjective {σ κ φ πs u : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) :
    Function.Surjective (fmap σ κ φ πs u) := by
  intro y
  set s := σ * κ
  set R := max πs 0
  set b := (1 + s) * y + s * u
  set a := min πs (b - s * R)
  have hab : a ≤ b := by
    have : 0 ≤ s * R := mul_nonneg hσκ.le (le_max_right _ _)
    exact (min_le_right _ _).trans (by linarith)
  have hfa : fmap σ κ φ πs u a ≤ y := by
    unfold fmap
    have hra : rule φ πs a ≤ R := by
      unfold rule
      refine max_le_max ?_ le_rfl
      have : a ≤ πs := min_le_left _ _
      nlinarith
    have : a ≤ b - s * R := min_le_right _ _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hfb : y ≤ fmap σ κ φ πs u b := by
    unfold fmap
    have : 0 ≤ rule φ πs b := le_max_right _ _
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  obtain ⟨c, -, hc⟩ :=
    intermediate_value_Icc hab (fmap_continuous σ κ φ πs u).continuousOn ⟨hfa, hfb⟩
  exact ⟨c, hc⟩

/-- Cochrane (2023), eq. (20.3), p. 472: left of the kink the map has slope `1/(1 + σκ)`. -/
theorem hasDerivAt_fmap_left {σ κ φ πs u π : ℝ} (hφ : 0 < φ) (h : π < kink φ πs) :
    HasDerivAt (fmap σ κ φ πs u) (1 / (1 + σ * κ)) π := by
  have hd : HasDerivAt (fun y => 1 / (1 + σ * κ) * y - σ * κ / (1 + σ * κ) * u)
      (1 / (1 + σ * κ)) π := by
    simpa using ((hasDerivAt_id' π).const_mul (1 / (1 + σ * κ))).sub_const
      (σ * κ / (1 + σ * κ) * u)
  refine hd.congr_of_eventuallyEq (Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy => ?_)
  exact eq20_3 ((kink_iff hφ).mpr (le_of_lt hy))

/-- Cochrane (2023), eq. (20.4), p. 472: right of the kink the map has slope
`(1 + φσκ)/(1 + σκ)`. -/
theorem hasDerivAt_fmap_right {σ κ φ πs u π : ℝ} (hφ : 0 < φ) (hσκ : 0 < σ * κ)
    (h : kink φ πs < π) : HasDerivAt (fmap σ κ φ πs u) (slopeR σ κ φ) π := by
  have hd : HasDerivAt (fun y => πs + slopeR σ κ φ * (y - πs) - σ * κ / (1 + σ * κ) * u)
      (slopeR σ κ φ) π := by
    simpa using (((hasDerivAt_id' π).sub_const πs).const_mul (slopeR σ κ φ)).const_add
      πs |>.sub_const (σ * κ / (1 + σ * κ) * u)
  refine hd.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy => ?_)
  have hy' : 0 ≤ πs + φ * (y - πs) := by
    by_contra hc
    push Not at hc
    have := (kink_iff hφ).mp hc.le
    exact absurd hy (not_lt.mpr this)
  have := eq20_4 (u := u) hσκ hy'
  simp only
  linarith

/-- Cochrane (2023), p. 472 ("slope less than one"): `1/(1 + σκ) < 1`. -/
theorem slope_left_lt_one {σ κ : ℝ} (hσκ : 0 < σ * κ) : 1 / (1 + σ * κ) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), p. 472 ("slope greater than one"): `(1 + φσκ)/(1 + σκ) > 1 ↔ φ > 1`. -/
theorem slope_right_gt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) : 1 < slopeR σ κ φ ↔ 1 < φ := by
  unfold slopeR
  rw [one_lt_div (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), eq. (20.4), p. 472: at or above the kink the rule is not at the bound. -/
theorem active_of_kink_le {φ πs π : ℝ} (hφ : 0 < φ) (h : kink φ πs ≤ π) :
    0 ≤ πs + φ * (π - πs) := by
  unfold kink at h
  rw [div_le_iff₀ hφ] at h
  nlinarith

/-- Cochrane (2023), §20.2.1, p. 473 ("converging as time goes forward"): two points on the
zero-bound branch are brought closer, `|f(x) − f(y)| = |x − y|/(1 + σκ)`. -/
theorem zlb_branch_contraction {σ κ φ πs u x y : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ)
    (hx : x ≤ kink φ πs) (hy : y ≤ kink φ πs) :
    |fmap σ κ φ πs u x - fmap σ κ φ πs u y| = |x - y| / (1 + σ * κ) := by
  rw [eq20_3 ((kink_iff hφ).mpr hx), eq20_3 ((kink_iff hφ).mpr hy)]
  rw [show 1 / (1 + σ * κ) * x - σ * κ / (1 + σ * κ) * u -
      (1 / (1 + σ * κ) * y - σ * κ / (1 + σ * κ) * u) = (x - y) / (1 + σ * κ) by ring,
    abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + σ * κ)]

/-- Cochrane (2023), §20.2.1, p. 472 ("alternative equilibria diverge"): two points on the
active branch are pushed apart, `|f(x) − f(y)| = ((1 + φσκ)/(1 + σκ))|x − y|`. -/
theorem active_branch_expansion {σ κ φ πs u x y : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ)
    (hx : kink φ πs ≤ x) (hy : kink φ πs ≤ y) :
    |fmap σ κ φ πs u x - fmap σ κ φ πs u y| = slopeR σ κ φ * |x - y| := by
  have h1 := active_of_kink_le hφ hx
  have h2 := active_of_kink_le hφ hy
  have ex := eq20_4 (u := u) hσκ h1
  have ey := eq20_4 (u := u) hσκ h2
  have hpos : 0 < slopeR σ κ φ := by
    unfold slopeR
    apply div_pos _ (by linarith)
    nlinarith
  rw [show fmap σ κ φ πs u x - fmap σ κ φ πs u y = slopeR σ κ φ * (x - y) by linarith,
    abs_mul, abs_of_pos hpos]

/-! ## Steady states (p. 472) and survey error E2 -/

/-- Cochrane (2023), p. 472: the steady states of `f_u` (for `φ > 1`, `σκ > 0`) are `−u`, when
it lies on the zero-bound branch, and `π* + u/(φ − 1)`, when it lies on the active branch. -/
theorem fixed_iff {σ κ φ πs u π : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) :
    fmap σ κ φ πs u π = π ↔ (π = -u ∧ -u ≤ kink φ πs) ∨
      (π = πs + u / (φ - 1) ∧ kink φ πs ≤ πs + u / (φ - 1)) := by
  have hφ0 : 0 < φ := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hs1 : (1 + σ * κ) ≠ 0 := by linarith
  have hσκ' : σ * κ ≠ 0 := hσκ.ne'
  constructor
  · intro h
    by_cases hk : π ≤ kink φ πs
    · rw [eq20_3 ((kink_iff hφ0).mpr hk)] at h
      field_simp at h
      have : π = -u := by
        apply mul_left_cancel₀ hσκ'
        linarith
      exact Or.inl ⟨this, this ▸ hk⟩
    · push Not at hk
      have := eq20_4 (u := u) hσκ (active_of_kink_le hφ0 hk.le)
      rw [h] at this
      unfold slopeR at this
      field_simp at this
      have hp : π = πs + u / (φ - 1) := by
        field_simp
        apply mul_left_cancel₀ hσκ'
        linarith
      exact Or.inr ⟨hp, hp ▸ hk.le⟩
  · rintro (⟨rfl, hk⟩ | ⟨rfl, hk⟩)
    · rw [eq20_3 ((kink_iff hφ0).mpr hk)]
      field_simp
      ring
    · have := eq20_4 (u := u) hσκ (active_of_kink_le hφ0 hk)
      unfold slopeR at this
      have e : fmap σ κ φ πs u (πs + u / (φ - 1)) - (πs + u / (φ - 1)) = 0 := by
        rw [show fmap σ κ φ πs u (πs + u / (φ - 1)) - (πs + u / (φ - 1)) =
          (fmap σ κ φ πs u (πs + u / (φ - 1)) - πs) - u / (φ - 1) by ring, this]
        field_simp
        ring
      linarith

/-- Cochrane (2023), p. 472: the two candidate steady states lie on their branches under the
same condition: `π* + u/(φ − 1) ≥ π*(φ − 1)/φ ↔ −u ≤ π*(φ − 1)/φ`. -/
theorem upper_on_branch_iff {φ πs u : ℝ} (hφ : 1 < φ) :
    kink φ πs ≤ πs + u / (φ - 1) ↔ -u ≤ kink φ πs := by
  have hφ0 : 0 < φ := by linarith
  have hφ1 : 0 < φ - 1 := by linarith
  unfold kink
  rw [div_le_iff₀ hφ0, le_div_iff₀ hφ0]
  have e : (πs + u / (φ - 1)) * φ = πs * φ + u * φ / (φ - 1) := by ring
  rw [e]
  constructor
  · intro h
    have : πs * (φ - 1) - πs * φ ≤ u * φ / (φ - 1) := by linarith
    rw [le_div_iff₀ hφ1] at this
    nlinarith
  · intro h
    have : πs * (φ - 1) - πs * φ ≤ u * φ / (φ - 1) := by
      rw [le_div_iff₀ hφ1]
      nlinarith
    linarith

/-- Cochrane (2023), p. 472, corrected (survey E2): a steady state exists iff
`−u ≤ π*(φ − 1)/φ`; then both `−u` and `π* + u/(φ − 1)` are steady states. -/
theorem steady_exists_iff {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) :
    (∃ π, fmap σ κ φ πs u π = π) ↔ -u ≤ kink φ πs := by
  constructor
  · rintro ⟨π, h⟩
    rcases (fixed_iff hφ hσκ).mp h with ⟨-, hk⟩ | ⟨-, hk⟩
    · exact hk
    · exact (upper_on_branch_iff hφ).mp hk
  · intro h
    exact ⟨-u, (fixed_iff hφ hσκ).mpr (Or.inl ⟨rfl, h⟩)⟩

/-- Cochrane (2023), p. 472: when `−u ≤ π*(φ − 1)/φ`, both `−u` and `π* + u/(φ − 1)` are steady
states. -/
theorem both_steady {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (h : -u ≤ kink φ πs) :
    fmap σ κ φ πs u (-u) = -u ∧ fmap σ κ φ πs u (πs + u / (φ - 1)) = πs + u / (φ - 1) :=
  ⟨(fixed_iff hφ hσκ).mpr (Or.inl ⟨rfl, h⟩),
    (fixed_iff hφ hσκ).mpr (Or.inr ⟨rfl, (upper_on_branch_iff hφ).mpr h⟩)⟩

/-- Cochrane (2023), p. 472 ("with `u_{r,t} = 0`, a stable steady state at `π = 0` … and an
unstable … steady state at `π = π*`"): for `φ > 1`, `π* > 0`, the steady states are exactly
`0` and `π*`. -/
theorem fixed_u_zero {σ κ φ πs π : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs) :
    fmap σ κ φ πs 0 π = π ↔ π = 0 ∨ π = πs := by
  have hk : 0 ≤ kink φ πs := by
    unfold kink
    apply div_nonneg _ (by linarith)
    nlinarith
  rw [fixed_iff hφ hσκ]
  simp only [neg_zero, zero_div, add_zero]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, hk⟩
    · refine Or.inr ⟨h, ?_⟩
      have := (upper_on_branch_iff (πs := πs) (u := 0) hφ).mpr (by simpa using hk)
      simpa using this

/-- Cochrane (2023), p. 472 ("a negative `u_{r,t}` … pushes the steady states in"): for
`u < 0` the lower steady state `−u` lies above `0` and the upper one below `π*`. -/
theorem steady_states_pushed_in {φ πs u : ℝ} (hφ : 1 < φ) (hu : u < 0) :
    0 < -u ∧ πs + u / (φ - 1) < πs := by
  refine ⟨by linarith, ?_⟩
  have : u / (φ - 1) < 0 := div_neg_of_neg_of_pos hu (by linarith)
  linarith

/-- Cochrane (2023), p. 472 ("a stable steady state … where the phase diagram has slope less
than one"): if `−u` lies strictly on the zero-bound branch, it is locally attracting. -/
theorem lower_attracting {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (h : -u < kink φ πs) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = fmap σ κ φ πs u (x t)) → |x 0 - -u| < δ →
      (∀ t, |x t - -u| < δ) ∧ Tendsto x atTop (𝓝 (-u)) := by
  refine GlobalDynamics.attracting_of_abs_deriv_lt_one (both_steady hφ hσκ h.le).1
    (hasDerivAt_fmap_left (by linarith) h) ?_
  rw [abs_of_pos (by apply div_pos one_pos; linarith)]
  exact slope_left_lt_one hσκ

/-- Cochrane (2023), p. 472 ("an unstable locally-determinate steady state … slope greater
than one"): if `π* + u/(φ − 1)` lies strictly on the active branch, it is repelling. -/
theorem upper_repelling {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ)
    (h : kink φ πs < πs + u / (φ - 1)) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = fmap σ κ φ πs u (x t)) →
      x 0 ≠ πs + u / (φ - 1) → ∃ t, δ ≤ |x t - (πs + u / (φ - 1))| := by
  refine GlobalDynamics.repelling_of_one_lt_abs_deriv
    (both_steady hφ hσκ ((upper_on_branch_iff hφ).mp h.le)).2
    (hasDerivAt_fmap_right (by linarith) hσκ h) ?_
  have := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  rw [abs_of_pos (by linarith)]
  exact this

/-- Cochrane (2023), p. 472, survey error E2: at the Figure 20.3 calibration (`σ = 1`,
`κ = 1/2`, `φ = 2`, `π* = 2`, `u_r = −2`) there is no steady state during the shock:
`f_u(π) − π ≥ 1/3` for every `π`. -/
theorem fig203_no_steady_state (π : ℝ) : 1 / 3 ≤ fmap 1 (1 / 2) 2 2 (-2) π - π := by
  unfold fmap rule
  rcases le_total (2 + 2 * (π - 2)) 0 with h | h
  · rw [max_eq_right h, le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    linarith
  · rw [max_eq_left h, le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    linarith

/-- Cochrane (2023), p. 472, survey error E2: the printed steady states "`π = −u_{r,t}`" and
"`π = π* + u_{r,t}/(φ − 1)`" are not steady states at the Figure 20.3 values (`2` and `0`). -/
theorem fig203_printed_steady_states_false :
    fmap 1 (1 / 2) 2 2 (-2) 2 ≠ 2 ∧
      fmap 1 (1 / 2) 2 2 (-2) (2 + (-2) / (2 - 1)) ≠ 2 + (-2) / (2 - 1) := by
  constructor <;> intro h <;> linarith [fig203_no_steady_state 2, fig203_no_steady_state 0,
    show (2 : ℝ) + (-2) / (2 - 1) = 0 by norm_num]

/-! ## Global versus local (pp. 473–474), `u = 0` -/

/-- Cochrane (2023), eq. (20.4), p. 472, with `u = 0`: on the active branch
`f(π) − π* = ((1 + φσκ)/(1 + σκ))(π − π*)`. -/
theorem active_affine {σ κ φ πs π : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ) (h : kink φ πs ≤ π) :
    fmap σ κ φ πs 0 π - πs = slopeR σ κ φ * (π - πs) := by
  have := eq20_4 (u := 0) hσκ (active_of_kink_le hφ h)
  simpa using this

/-- Cochrane (2023), p. 472: the kink lies strictly between `0` and `π*` (`φ > 1`, `π* > 0`). -/
theorem kink_mem {φ πs : ℝ} (hφ : 1 < φ) (hπs : 0 < πs) : 0 < kink φ πs ∧ kink φ πs < πs := by
  unfold kink
  constructor
  · apply div_pos _ (by linarith)
    nlinarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-- Cochrane (2023), p. 473 ("alternative equilibria diverge from the inflation target"):
with `u = 0`, an orbit starting above `π*` satisfies `π_t − π* = cᵗ(π₀ − π*)` and explodes. -/
theorem orbit_above {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : πs < x 0) :
    (∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs)) ∧ Tendsto x atTop atTop := by
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hk := kink_mem hφ hπs
  have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hpos : 0 < x t - πs := by
        rw [ih]; exact mul_pos (pow_pos (by linarith) t) (by linarith)
      rw [hx t, active_affine hσκ (by linarith) (by linarith), ih, pow_succ]
      ring
  refine ⟨key, ?_⟩
  have hp := (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const (sub_pos.mpr h0)
  have e : x = fun t => slopeR σ κ φ ^ t * (x 0 - πs) + πs := by
    funext t
    linarith [key t]
  rw [e]
  exact tendsto_atTop_add_const_right _ _ hp

/-- Cochrane (2023), p. 473 ("Equilibria in which inflation undershoots … return back to zero
inflation and zero interest rates"): with `u = 0`, every orbit starting below `π*` converges to
`0`. -/
theorem orbit_below_tendsto_zero {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : x 0 < πs) :
    Tendsto x atTop (𝓝 0) := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hk := kink_mem hφ hπs
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  have hbelow : ∀ t, x t < πs := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [hx t]
      have := fmap_strictMono (πs := πs) (u := 0) hφ0.le hσκ ih
      rwa [hfix] at this
  -- some date reaches the zero-bound branch
  have hT : ∃ T, x T ≤ kink φ πs := by
    by_contra hcon
    push Not at hcon
    have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [hx t, active_affine hσκ hφ0 (hcon t).le, ih, pow_succ]
        ring
    have hp := (tendsto_pow_atTop_atTop_of_one_lt hc).eventually
      (eventually_gt_atTop ((πs - kink φ πs) / (πs - x 0)))
    obtain ⟨t, ht⟩ := hp.exists
    have h1 := key t
    have h2 := hcon t
    have hd : 0 < πs - x 0 := by linarith
    rw [div_lt_iff₀ hd] at ht
    nlinarith
  obtain ⟨T, hT⟩ := hT
  have hinv : ∀ y, y ≤ kink φ πs → fmap σ κ φ πs 0 y = (1 + σ * κ)⁻¹ * y := by
    intro y hy
    rw [eq20_3 ((kink_iff hφ0).mpr hy)]
    ring
  have hstay : ∀ n, x (T + n) = (1 + σ * κ)⁻¹ ^ n * x T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : x (T + n) ≤ kink φ πs := by
        rw [ih]
        rcases le_or_gt 0 (x T) with h | h
        · calc (1 + σ * κ)⁻¹ ^ n * x T ≤ 1 * x T := by
                gcongr
                exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
            _ ≤ kink φ πs := by linarith
        · have : (1 + σ * κ)⁻¹ ^ n * x T ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
          linarith
      rw [← add_assoc, hx, hinv _ hle, ih, pow_succ]
      ring
  have hlim : Tendsto (fun n => x (T + n)) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (1 + σ * κ)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    have := hr.mul_const (x T)
    simp only [zero_mul] at this
    refine this.congr fun n => ?_
    rw [hstay n]
  have e : (fun n => x (T + n)) = fun n => x (n + T) := by
    funext n; rw [add_comm]
  rw [e] at hlim
  exact (tendsto_add_atTop_iff_nat T).mp hlim

/-- Cochrane (2023), p. 473 ("return back to zero inflation and zero interest rates"): with
`u = 0`, along every orbit starting below `π*` the interest rate is eventually zero. -/
theorem orbit_below_rate_zero {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : x 0 < πs) :
    ∀ᶠ t in atTop, rule φ πs (x t) = 0 :=
  ((orbit_below_tendsto_zero hφ hσκ hπs hx h0).eventually
    (Iio_mem_nhds (kink_mem hφ hπs).1)).mono fun _ ht =>
      max_eq_right ((kink_iff (by linarith)).mpr (le_of_lt ht))

/-- Cochrane (2023), pp. 473–474 ("the only locally bounded equilibrium, but … not the only
globally bounded one"): with `u = 0`, the orbit from `π₀` is bounded iff `π₀ ≤ π*` — a
continuum of bounded paths. -/
theorem bounded_orbits_eq {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs) :
    {π0 : ℝ | ∃ M, ∀ t, |(fmap σ κ φ πs 0)^[t] π0| ≤ M} = Set.Iic πs := by
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  ext π0
  simp only [Set.mem_ofPred_eq, Set.mem_Iic]
  have hx : ∀ t, (fmap σ κ φ πs 0)^[t + 1] π0 = fmap σ κ φ πs 0 ((fmap σ κ φ πs 0)^[t] π0) :=
    fun t => Function.iterate_succ_apply' _ _ _
  constructor
  · rintro ⟨M, hM⟩
    by_contra hc
    push Not at hc
    have := (orbit_above (x := fun t => (fmap σ κ φ πs 0)^[t] π0) hφ hσκ hπs hx
      (by simpa using hc)).2
    obtain ⟨t, ht⟩ := (this.eventually (eventually_gt_atTop M)).exists
    linarith [le_abs_self ((fmap σ κ φ πs 0)^[t] π0), hM t]
  · intro h
    rcases h.lt_or_eq with h | h
    · have hl := orbit_below_tendsto_zero (x := fun t => (fmap σ κ φ πs 0)^[t] π0) hφ hσκ hπs
        hx (by simpa using h)
      obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hl).exists_norm_le
      exact ⟨M, fun t => by simpa using hM _ ⟨t, rfl⟩⟩
    · refine ⟨|πs|, fun t => ?_⟩
      rw [h, Function.iterate_fixed hfix]

/-- Cochrane (2023), p. 473 ("`π_t = π*` is the only locally bounded equilibrium"): with
`u = 0`, an orbit that stays within `π* − π*(φ − 1)/φ` of `π*` is constant at `π*`. -/
theorem locally_bounded_unique {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t))
    (hb : ∀ t, |x t - πs| < πs - kink φ πs) : ∀ t, x t = πs := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hon : ∀ t, kink φ πs ≤ x t := fun t => by
    have := hb t
    rw [abs_lt] at this
    linarith
  have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hx t, active_affine hσκ hφ0 (hon t), ih, pow_succ]
      ring
  have h0 : x 0 = πs := by
    by_contra hne
    have hd : 0 < |x 0 - πs| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually
      (eventually_gt_atTop ((πs - kink φ πs) / |x 0 - πs|))).exists
    have := hb t
    rw [key t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    rw [div_lt_iff₀ hd] at ht
    linarith
  intro t
  have := key t
  rw [h0, sub_self, mul_zero] at this
  linarith

/-- Cochrane (2023), §20.2.1, p. 472: the expectation system shifted to start at date `T`,
`E'_t = E_{T+t}`. -/
def shiftE (T : ℕ) : ExpectationSystem Ω where
  E := fun t => 𝔼.E (T + t)
  const := fun t c => 𝔼.const (T + t) c
  mono := fun t _ _ h => 𝔼.mono (T + t) h
  tower := fun hst x => 𝔼.tower (by omega) x
  known := fun hst x => 𝔼.known (by omega) x

/-- Cochrane (2023), p. 473 ("`π_t = π*` is the only locally bounded equilibrium"), under any
`ExpectationSystem`: if from date `T` on `u = 0`, `E_tπ_{t+1} = f(π_t)` and `π` stays within
`ε < π* − π*(φ − 1)/φ` of `π*`, then `π_t = π*` for all `t ≥ T`. -/
theorem locally_bounded_unique_E {σ κ φ πs ε : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (T : ℕ)
    {π : ℕ → Ω → ℝ} (h : ∀ t ω, T ≤ t → 𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs 0 (π t ω))
    (hε : ε < πs - kink φ πs) (hb : ∀ t ω, T ≤ t → |π t ω - πs| ≤ ε) :
    ∀ t, T ≤ t → π t = fun _ => πs := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hc0 : 0 < slopeR σ κ φ := by linarith
  set d : ℕ → Ω → ℝ := fun t ω => π (T + t) ω - πs with hd
  have hstep : ∀ t, d t = (slopeR σ κ φ)⁻¹ • (shiftE 𝔼 T).E t (d (t + 1)) +
      (0 : ℕ → Ω → ℝ) t := by
    intro t
    funext ω
    have hon : kink φ πs ≤ π (T + t) ω := by
      have := hb (T + t) ω (by omega)
      rw [abs_le] at this
      linarith
    have he := h (T + t) ω (by omega)
    have hE : (shiftE 𝔼 T).E t (d (t + 1)) ω = 𝔼.E (T + t) (π (T + t + 1)) ω - πs := by
      change 𝔼.E (T + t) (π (T + (t + 1)) - fun _ => πs) ω = _
      rw [map_sub, 𝔼.const, ← add_assoc]
      rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, hd]
    rw [hE, he, active_affine hσκ hφ0 hon]
    field_simp
  have hinv : |(slopeR σ κ φ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos hc0]
    exact inv_lt_one_of_one_lt₀ hc
  have h0 := (shiftE 𝔼 T).forward_unique hinv (u := 0) (z₁ := d) (z₂ := 0) hstep
    (fun t => by simp) ⟨ε, fun t ω => hb (T + t) ω (by omega)⟩ ⟨0, fun _ _ => by simp⟩
  intro t ht
  funext ω
  have := congrFun (congrFun h0 (t - T)) ω
  simp only [hd, Pi.zero_apply, show T + (t - T) = t by omega] at this
  linarith

/-! ## Figure 20.3: selection by the future rule -/

/-- Cochrane (2023), §20.2.1, p. 472: backward uniqueness. For any `ExpectationSystem`, any
deterministic natural-rate path `u`, `φ ≥ 0`, `σκ > 0`: two processes satisfying
`E_tπ_{t+1} = f_{u_t}(π_t)` that share the same deterministic date-`T` value agree at every
earlier date and are deterministic there. -/
theorem backward_unique {σ κ φ πs : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) (u : ℕ → ℝ) (T : ℕ)
    {π π' : ℕ → Ω → ℝ} (h : ∀ t ω, 𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs (u t) (π t ω))
    (h' : ∀ t ω, 𝔼.E t (π' (t + 1)) ω = fmap σ κ φ πs (u t) (π' t ω)) {c : ℝ}
    (hT : ∀ ω, π T ω = c) (hT' : ∀ ω, π' T ω = c) :
    ∀ k, k ≤ T → ∃ b, ∀ ω, π (T - k) ω = b ∧ π' (T - k) ω = b := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨c, fun ω => ⟨hT ω, hT' ω⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨b', hb'⟩ := fmap_surjective (u := u (T - (k + 1))) (πs := πs) hφ hσκ b
    have hconst : π (T - (k + 1) + 1) = fun _ => b := by
      funext ω; rw [show T - (k + 1) + 1 = T - k by omega]; exact (hb ω).1
    have hconst' : π' (T - (k + 1) + 1) = fun _ => b := by
      funext ω; rw [show T - (k + 1) + 1 = T - k by omega]; exact (hb ω).2
    refine ⟨b', fun ω => ⟨?_, ?_⟩⟩
    · have := h (T - (k + 1)) ω
      rw [hconst, 𝔼.const, ← hb'] at this
      exact ((fmap_strictMono hφ hσκ).injective this).symm
    · have := h' (T - (k + 1)) ω
      rw [hconst', 𝔼.const, ← hb'] at this
      exact ((fmap_strictMono hφ hσκ).injective this).symm

/-- Cochrane (2023), §20.2.1, p. 472: existence of the selected path. For `φ > 1`, a
natural-rate path with `u_t = 0` for `t ≥ T` and target `π*`, there is a deterministic path with
`π_t = π*` for `t ≥ T` and `π_{t+1} = f_{u_t}(π_t)` at every date; it solves the model under any
`ExpectationSystem`. -/
theorem backward_exists {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    (u : ℕ → ℝ) (T : ℕ) (hu : ∀ t, T ≤ t → u t = 0) :
    ∃ p : ℕ → ℝ, (∀ t, T ≤ t → p t = πs) ∧ (∀ t, p (t + 1) = fmap σ κ φ πs (u t) (p t)) ∧
      ∀ t ω, 𝔼.E t (fun _ => p (t + 1)) ω = fmap σ κ φ πs (u t) ((fun _ => p t) ω) := by
  have hφ0 : 0 ≤ φ := by linarith
  have hsurj := fun t => fmap_surjective (u := u t) (πs := πs) hφ0 hσκ
  -- `b k` is the value at date `T - k`
  let b : ℕ → ℝ := fun k => Nat.rec πs (fun k bk => Function.surjInv (hsurj (T - (k + 1))) bk) k
  have hb : ∀ k, fmap σ κ φ πs (u (T - (k + 1))) (b (k + 1)) = b k := fun k =>
    Function.surjInv_eq (hsurj (T - (k + 1))) (b k)
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  let p : ℕ → ℝ := fun t => if T ≤ t then πs else b (T - t)
  have hstep : ∀ t, p (t + 1) = fmap σ κ φ πs (u t) (p t) := by
    intro t
    by_cases ht : T ≤ t
    · simp only [p, ht, show T ≤ t + 1 by omega, ↓reduceIte]
      rw [hu t ht, hfix]
    · simp only [p, ht, ↓reduceIte]
      by_cases ht1 : T ≤ t + 1
      · have hTt : T = t + 1 := by omega
        simp only [ht1, ↓reduceIte]
        have := hb 0
        rw [show T - (0 + 1) = t by omega] at this
        rw [show T - t = 0 + 1 by omega, this]
        rfl
      · simp only [ht1, ↓reduceIte]
        have := hb (T - (t + 1))
        rw [show T - (T - (t + 1) + 1) = t by omega, show T - (t + 1) + 1 = T - t by omega]
          at this
        exact this.symm
  refine ⟨p, fun t ht => by simp [p, ht], hstep, fun t ω => ?_⟩
  rw [𝔼.const, hstep t]

/-- Cochrane (2023), Figure 20.3, p. 473: the natural rate, `u_r = −2` before `T = 10` and `0`
from `T` on (the reading under which `π_t = π*` for `t ≥ T` solves the model). -/
noncomputable def uFig (t : ℕ) : ℝ := if t < 10 then -2 else 0

/-- Cochrane (2023), Figure 20.3, pp. 472–473: selection by the future rule. For any
`ExpectationSystem`, if `π` solves the model with `σ = 1`, `κ = 1/2`, `φ = 2`, `π* = 2` and the
natural-rate path `uFig`, and stays within `ε < 1` of `π* = 2` from `T = 10` on (local
boundedness under the active rule), then `π_t = 2` for `t ≥ 10` and, at every state,
`π₉ = 3/2`, `π₈ = 9/8`, `π₇ = 11/16`, `π₆ = 1/32`. -/
theorem fig203_selection {π : ℕ → Ω → ℝ} {ε : ℝ}
    (h : ∀ t ω, 𝔼.E t (π (t + 1)) ω = fmap 1 (1 / 2) 2 2 (uFig t) (π t ω)) (hε : ε < 1)
    (hb : ∀ t ω, 10 ≤ t → |π t ω - 2| ≤ ε) :
    (∀ t, 10 ≤ t → π t = fun _ => 2) ∧ ∀ ω, π 9 ω = 3 / 2 ∧ π 8 ω = 9 / 8 ∧
      π 7 ω = 11 / 16 ∧ π 6 ω = 1 / 32 := by
  have hσκ : (0 : ℝ) < 1 * (1 / 2) := by norm_num
  have hk : kink 2 2 = 1 := kink_fig203.1
  have hsel := locally_bounded_unique_E 𝔼 (σ := 1) (κ := 1 / 2) (φ := 2) (πs := 2)
    (by norm_num) hσκ 10 (π := π) (fun t ω ht => by
      have := h t ω
      rw [show uFig t = 0 by simp [uFig]; omega] at this
      exact this) (by rw [hk]; linarith) hb
  refine ⟨hsel, ?_⟩
  have inj := (fmap_strictMono (σ := 1) (κ := 1 / 2) (φ := 2) (πs := 2) (u := -2) (by norm_num)
    hσκ).injective
  have hu : ∀ t, t < 10 → uFig t = -2 := fun t ht => by simp [uFig, ht]
  have step : ∀ t c d, t < 10 → (π (t + 1) = fun _ => c) →
      fmap 1 (1 / 2) 2 2 (-2) d = c → π t = fun _ => d := by
    intro t c d ht hc hd
    funext ω
    have := h t ω
    rw [hc, 𝔼.const, hu t ht, ← hd] at this
    exact (inj this).symm
  have v9 : fmap 1 (1 / 2) 2 2 (-2) (3 / 2) = 2 := by
    unfold fmap rule; rw [max_eq_left (by norm_num)]; norm_num
  have v8 : fmap 1 (1 / 2) 2 2 (-2) (9 / 8) = 3 / 2 := by
    unfold fmap rule; rw [max_eq_left (by norm_num)]; norm_num
  have v7 : fmap 1 (1 / 2) 2 2 (-2) (11 / 16) = 9 / 8 := by
    unfold fmap rule; rw [max_eq_right (by norm_num)]; norm_num
  have v6 : fmap 1 (1 / 2) 2 2 (-2) (1 / 32) = 11 / 16 := by
    unfold fmap rule; rw [max_eq_right (by norm_num)]; norm_num
  have p9 := step 9 2 (3 / 2) (by norm_num) (hsel 10 le_rfl) v9
  have p8 := step 8 (3 / 2) (9 / 8) (by norm_num) p9 v8
  have p7 := step 7 (9 / 8) (11 / 16) (by norm_num) p8 v7
  have p6 := step 6 (11 / 16) (1 / 32) (by norm_num) p7 v6
  intro ω
  exact ⟨by rw [p9], by rw [p8], by rw [p7], by rw [p6]⟩

/-- Cochrane (2023), p. 472, survey error E3 ("Before `t = T`, while the nominal rate remains
stuck at zero"): on the selected path of Figure 20.3 the rate lifts off two periods before
`T = 10`: `i₉ = 1`, `i₈ = 1/4`, while `i₇ = i₆ = 0`. -/
theorem fig203_early_liftoff :
    rule 2 2 (3 / 2) = 1 ∧ rule 2 2 (9 / 8) = 1 / 4 ∧ rule 2 2 (11 / 16) = 0 ∧
      rule 2 2 (1 / 32) = 0 := by
  unfold rule
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [max_eq_left (by norm_num)]; norm_num
  · rw [max_eq_left (by norm_num)]; norm_num
  · rw [max_eq_right (by norm_num)]
  · rw [max_eq_right (by norm_num)]

end Cochrane.ZeroBound.ZLBRule

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Selection by expected future policy

Cochrane (2023), Chapter 20, §20.2.1, pp. 471–472 ("the expectation of future
equilibrium-selection policy can select equilibria even when policy is currently or locally
passive"), and Chapter 24, pp. 522–524 (Davig and Leeper: "If an economy is currently in what
looks like a passive-fiscal regime, but people expect a switch to what looks like an
active-fiscal regime, then that future active fiscal policy selects equilibria").

Everything holds for an arbitrary `ExpectationSystem`, with a deterministic switch date `T`.

## Main results

* `switch_scalar`: the engine. `c_t y_t = d E_t y_{t+1} + f_t` with `c_t ≠ 0` before `T` and
  `c_t = c_A`, `|d| < |c_A|` from `T` on has exactly one bounded adapted solution for every
  bounded adapted `f`. `bounded_of_rec` is the boundedness lemma used for recursions that are
  contracting after `T`.
* Monetary switch (§20.2.1): the frictionless model `E_tπ_{t+1} = φ_tπ_t + u_t` with ANY nonzero
  `φ_t` before `T` (e.g. passive `|φ_t| < 1`) and active `|φ_A| > 1` from `T` on has a unique
  bounded equilibrium (`future_selection`). Without the switch, passive policy leaves
  uncountably many (`passive_forever_not_unique`); the hypothesis `φ_t ≠ 0` cannot be dropped
  (`zero_coefficient_not_unique`: a pure peg before `T` leaves `π₀` free).
* Fiscal switch (Ch. 24, Leeper model (23.1)–(23.4) with time-varying `φ_t`, `γ_t`):
  passive fiscal policy (`γ_t ≠ 1`, any `φ_t`) before `T` and active fiscal / passive money
  (`γ = 0`, `|φ_P| < 1`) from `T` on give a unique bounded equilibrium (`fiscal_switch_selects`),
  in which fiscal news moves inflation even while money is "active"
  (`fiscal_switch_unexpected_inflation`, and the explicit example
  `fiscal_switch_example`, where `φ₀ = 2` yet `π₀ = −2δ` for a post-switch surplus `δ`). Without
  the switch (active money forever) inflation does not depend on fiscal policy at all
  (`no_switch_fiscal_irrelevant`).
-/

namespace Cochrane.ZeroBound.FutureSelection

open Filter Topology
open Cochrane.ZeroBound

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ## Two general lemmas -/

omit 𝔼 in
/-- Cochrane (2023), §20.2.1, p. 472 (boundedness of the selected path): a recursion
`|x_{t+1}| ≤ c_t|x_t| + K_t` with `c_t = a < 1` and `K_t ≤ K` from date `T` on, started from a
bounded `x₀`, is bounded. -/
theorem bounded_of_rec {T : ℕ} {a B K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {c Kt : ℕ → ℝ}
    (hc0 : ∀ t, 0 ≤ c t) (hcT : ∀ t, T ≤ t → c t = a) (hKT : ∀ t, T ≤ t → Kt t ≤ K)
    {x : ℕ → Ω → ℝ} (h0 : ∀ ω, |x 0 ω| ≤ B)
    (hrec : ∀ t ω, |x (t + 1) ω| ≤ c t * |x t ω| + Kt t) : BoundedProc x := by
  let b : ℕ → ℝ := fun t => Nat.rec B (fun t bt => c t * bt + Kt t) t
  have hbs : ∀ t, b (t + 1) = c t * b t + Kt t := fun t => rfl
  have hb : ∀ t ω, |x t ω| ≤ b t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      intro ω
      rw [hbs]
      have := mul_le_mul_of_nonneg_left (ih ω) (hc0 t)
      linarith [hrec t ω]
  set m := max (b T) (K / (1 - a))
  have hm : ∀ n, b (T + n) ≤ m := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      rw [← add_assoc, hbs, hcT _ (by omega)]
      have h1 := hKT (T + n) (by omega)
      have h2 : K / (1 - a) ≤ m := le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at h2
      nlinarith [mul_le_mul_of_nonneg_left ih ha0]
  refine ⟨|m| + ∑ k ∈ Finset.range (T + 1), |b k|, fun t ω => (hb t ω).trans ?_⟩
  have hs : 0 ≤ ∑ k ∈ Finset.range (T + 1), |b k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases ht : t ≤ T
  · have := Finset.single_le_sum (f := fun k => |b k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    linarith [le_abs_self (b t), abs_nonneg m]
  · have := hm (t - T)
    rw [show T + (t - T) = t by omega] at this
    linarith [le_abs_self m]

/-- Cochrane (2023), §20.2.1, p. 472, and Ch. 24, p. 523: the scalar switching equation
`c_t y_t = d E_t y_{t+1} + f_t`, with `c_t ≠ 0` before `T` and `c_t = c_A`, `|d| < |c_A|` from
`T` on, has exactly one bounded adapted solution for every bounded adapted `f`: forward
stability after the switch pins `y_T`, and the equation, solved backward, pins every earlier
date. -/
theorem switch_scalar {T : ℕ} {cA d : ℝ} {c : ℕ → ℝ} (hc : ∀ t, t < T → c t ≠ 0)
    (hcA : ∀ t, T ≤ t → c t = cA) (hd : |d| < |cA|) {f : ℕ → Ω → ℝ} (hfb : BoundedProc f)
    (hfa : 𝔼.Adapted f) :
    ∃! y : ℕ → Ω → ℝ, BoundedProc y ∧ 𝔼.Adapted y ∧
      ∀ t, c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
  set S := ZLBRule.shiftE 𝔼 T with hS
  set g : ℕ → Ω → ℝ := fun t => f (T + t) with hg
  obtain ⟨K, hK⟩ := hfb
  have hga : S.Adapted g := fun t => hfa (T + t)
  obtain ⟨hzs, hzb, hza, hzu⟩ :=
    ForwardSolution.scalar_existsUnique S hd (fun t ω => hK (T + t) ω) hga
  set z := ForwardSolution.scalarSol S cA d g with hz
  have hSE : ∀ t, S.E t = 𝔼.E (T + t) := fun t => rfl
  -- the backward part: `back k` is the value at date `T - k`
  let back : ℕ → Ω → ℝ := fun k => Nat.rec (z 0)
    (fun k bk => (c (T - (k + 1)))⁻¹ • (d • 𝔼.E (T - (k + 1)) bk + f (T - (k + 1)))) k
  have hback : ∀ k, back (k + 1) =
      (c (T - (k + 1)))⁻¹ • (d • 𝔼.E (T - (k + 1)) (back k) + f (T - (k + 1))) := fun k => rfl
  let y : ℕ → Ω → ℝ := fun t => if T ≤ t then z (t - T) else back (T - t)
  have hyT : ∀ t, T ≤ t → y t = z (t - T) := fun t ht => by simp [y, ht]
  have hyB : ∀ k, k ≤ T → y (T - k) = back k := by
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      simp [y, back]
    · simp only [y, show ¬ T ≤ T - k by omega, ↓reduceIte, show T - (T - k) = k by omega]
  -- the equation after `T`
  have eqA : ∀ t, T ≤ t → c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
    intro t ht
    have h := hzs (t - T)
    rw [hSE, show T + (t - T) = t by omega] at h
    rw [hcA t ht, hyT t ht, hyT (t + 1) (by omega), show t + 1 - T = t - T + 1 by omega]
    simpa [hg, show T + (t - T) = t by omega] using h
  -- the equation before `T`
  have eqB : ∀ k, k < T → c (T - (k + 1)) • y (T - (k + 1)) =
      d • 𝔼.E (T - (k + 1)) (y (T - (k + 1) + 1)) + f (T - (k + 1)) := by
    intro k hk
    rw [hyB (k + 1) (by omega), show T - (k + 1) + 1 = T - k by omega, hyB k (by omega),
      hback, smul_smul, mul_inv_cancel₀ (hc _ (by omega)), one_smul]
  have eqAll : ∀ t, c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
    intro t
    by_cases ht : T ≤ t
    · exact eqA t ht
    · have := eqB (T - (t + 1)) (by omega)
      rwa [show T - (T - (t + 1) + 1) = t by omega] at this
  refine ⟨y, ⟨?_, ?_, eqAll⟩, ?_⟩
  · -- boundedness
    obtain ⟨Mz, hMz⟩ := hzb
    have hbk : ∀ k, ∃ B, ∀ ω, |back k ω| ≤ B := by
      intro k
      induction k with
      | zero => exact ⟨Mz, hMz 0⟩
      | succ k ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨|(c (T - (k + 1)))⁻¹| * (|d| * B + K), fun ω => ?_⟩
        rw [hback]
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul]
        gcongr
        refine (abs_add_le _ _).trans (add_le_add ?_ (hK _ ω))
        rw [abs_mul]
        gcongr
        exact 𝔼.abs_E_le hB _ ω
    choose B hB using hbk
    refine ⟨|Mz| + ∑ k ∈ Finset.range (T + 1), |B k|, fun t ω => ?_⟩
    have hs : 0 ≤ ∑ k ∈ Finset.range (T + 1), |B k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases ht : T ≤ t
    · rw [hyT t ht]
      linarith [hMz (t - T) ω, le_abs_self Mz]
    · have e := hyB (T - t) (by omega)
      rw [show T - (T - t) = t by omega] at e
      rw [e]
      have := Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (show T - t < T + 1 by omega))
      linarith [hB (T - t) ω, le_abs_self (B (T - t)), abs_nonneg Mz]
  · -- adaptedness
    intro t
    by_cases ht : T ≤ t
    · rw [hyT t ht]
      have := hza (t - T)
      rwa [hSE, show T + (t - T) = t by omega] at this
    · have e := hyB (T - t) (by omega)
      rw [show T - (T - t) = t by omega] at e
      rw [e]
      obtain ⟨k, hk⟩ : ∃ k, T - t = k + 1 := ⟨T - t - 1, by omega⟩
      rw [hk, hback, show T - (k + 1) = t by omega, map_smul, map_add, map_smul, 𝔼.E_E_self,
        hfa t]
  · -- uniqueness
    rintro y' ⟨hb', ha', he'⟩
    have hpost : (fun t => y' (T + t)) = z := by
      refine hzu _ (fun t => ?_) ?_
      · have := he' (T + t)
        rw [hcA _ (by omega), show T + t + 1 = T + (t + 1) by omega] at this
        exact this
      · obtain ⟨M, hM⟩ := hb'
        exact ⟨M, fun t ω => hM (T + t) ω⟩
    have hA : ∀ t, T ≤ t → y' t = y t := by
      intro t ht
      rw [hyT t ht, ← hpost]
      simp only [show T + (t - T) = t by omega]
    have hB' : ∀ k, k ≤ T → y' (T - k) = y (T - k) := by
      intro k
      induction k with
      | zero => exact fun _ => hA _ (by omega)
      | succ k ih =>
        intro hk
        have h1 := he' (T - (k + 1))
        have h2 := eqAll (T - (k + 1))
        rw [show T - (k + 1) + 1 = T - k by omega] at h1 h2
        rw [ih (by omega), ← h2] at h1
        exact smul_right_injective _ (hc _ (by omega)) h1
    funext t
    by_cases ht : T ≤ t
    · exact hA t ht
    · have := hB' (T - t) (by omega)
      rwa [show T - (T - t) = t by omega] at this

/-! ## The monetary switch (§20.2.1) -/

/-- Cochrane (2023), §20.2.1, p. 472 (frictionless version of the future-selection model):
the Fisher equation `i_t = E_tπ_{t+1}` and the rule `i_t = φ_tπ_t + u_t` give
`E_tπ_{t+1} = φ_tπ_t + u_t`, with a time-varying rule coefficient `φ_t`. -/
def RuleEq (φ : ℕ → ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (π (t + 1)) = φ t • π t + u t

/-- Cochrane (2023), §20.2.1, p. 472: `E_tπ_{t+1} = φ_tπ_t + u_t` is the scalar switching
equation `φ_t π_t = E_tπ_{t+1} − u_t`. -/
theorem ruleEq_iff (φ : ℕ → ℝ) (u π : ℕ → Ω → ℝ) :
    RuleEq 𝔼 φ u π ↔ ∀ t, φ t • π t = (1 : ℝ) • 𝔼.E t (π (t + 1)) + (-u t) := by
  refine forall_congr' fun t => ?_
  rw [one_smul]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), §20.2.1, p. 472 ("the expectation of future equilibrium-selection policy
can select equilibria even when policy is currently … passive"): with any nonzero `φ_t` before
`T` (in particular passive, `|φ_t| < 1`) and an active `|φ_A| > 1` from `T` on, the model has
exactly one bounded adapted equilibrium for every bounded adapted disturbance, under any
`ExpectationSystem`. -/
theorem future_selection {T : ℕ} {φA : ℝ} {φ : ℕ → ℝ} (hP : ∀ t, t < T → φ t ≠ 0)
    (hA : ∀ t, T ≤ t → φ t = φA) (hφA : 1 < |φA|) {u : ℕ → Ω → ℝ} (hub : BoundedProc u)
    (hua : 𝔼.Adapted u) :
    ∃! π : ℕ → Ω → ℝ, BoundedProc π ∧ 𝔼.Adapted π ∧ RuleEq 𝔼 φ u π := by
  obtain ⟨M, hM⟩ := hub
  have h := switch_scalar 𝔼 (d := 1) hP hA (by rw [abs_one]; exact hφA) (f := fun t => -u t)
    ⟨M, fun t ω => by simpa using hM t ω⟩ (fun t => by rw [map_neg, hua t])
  simpa only [ruleEq_iff] using h

/-- Cochrane (2023), §20.2.1, p. 467 and p. 472 (contrast): without the future switch, a
passive rule `0 < |φ_P| < 1` at every date leaves uncountably many bounded equilibria. -/
theorem passive_forever_not_unique [Nonempty Ω] {φP : ℝ} (h0 : φP ≠ 0) (h1 : |φP| < 1)
    {u : ℕ → Ω → ℝ} (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    ¬ {π : ℕ → Ω → ℝ | BoundedProc π ∧ RuleEq 𝔼 (fun _ => φP) u π}.Countable := by
  have ha : 1 < |φP⁻¹| := by
    rw [abs_inv]
    exact one_lt_inv_iff₀.mpr ⟨abs_pos.mpr h0, h1⟩
  obtain ⟨Mu, hMu⟩ := hub
  have hub' : BoundedProc (fun t => -(φP⁻¹) • u t) :=
    ⟨|φP⁻¹| * Mu, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hMu t ω) (abs_nonneg _)⟩
  have hua' : 𝔼.Adapted (fun t => -(φP⁻¹) • u t) := fun t => by rw [map_smul, hua t]
  have hset : {π : ℕ → Ω → ℝ | BoundedProc π ∧ RuleEq 𝔼 (fun _ => φP) u π} =
      {π | BoundedProc π ∧ ForwardSolution.Solves 𝔼 φP⁻¹ (fun t => -(φP⁻¹) • u t) π} := by
    ext π
    simp only [Set.mem_ofPred_eq, RuleEq, ForwardSolution.Solves]
    refine and_congr_right fun _ => forall_congr' fun t => ?_
    constructor
    · intro h
      rw [h]
      ext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · intro h
      rw [h]
      ext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  rw [hset]
  exact (ForwardSolution.exists_bounded_of_one_lt 𝔼 ha hub' hua').2

/-- Cochrane (2023), §20.2.1, p. 472: the hypothesis `φ_t ≠ 0` before the switch cannot be
dropped. With a pure peg (`φ₀ = 0`) at date 0, an active rule from `T = 1` on and `u = 0`,
under perfect foresight, both `π ≡ 0` and the path with `π₀ = 1`, `π_t = 0` afterwards are
bounded equilibria: future policy does not pin down `π₀`. -/
theorem zero_coefficient_not_unique :
    ∃ π π' : ℕ → Unit → ℝ, π ≠ π' ∧ BoundedProc π ∧ BoundedProc π' ∧
      RuleEq perfectForesight (fun t => if t = 0 then 0 else 2) 0 π ∧
      RuleEq perfectForesight (fun t => if t = 0 then 0 else 2) 0 π' := by
  refine ⟨fun _ _ => 0, fun t _ => if t = 0 then 1 else 0, ?_, ⟨0, fun _ _ => by simp⟩,
    ⟨1, fun t _ => by dsimp only; split_ifs <;> norm_num⟩, fun t => ?_, fun t => ?_⟩
  · intro h
    have := congrFun (congrFun h 0) ()
    simp at this
  · funext ω
    rcases t with _ | t <;> simp [perfectForesight]
  · funext ω
    rcases t with _ | t <;> simp [perfectForesight]

/-! ## The fiscal switch (Chapter 24, Davig and Leeper) -/

/-- Cochrane (2023), eqs. (23.1)–(23.4), p. 512, with time-varying policy (Ch. 24, p. 522):
`i_t = E_tπ_{t+1}`, `i_t = φ_tπ_t + u_{i,t}`, `s̃_{t+1} = γ_tv_t + u_{s,t+1}`,
`ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`, and the date-0 flow `ρv₀ = c₀ − π₀`, where
`c₀ = v_{−1} + i_{−1} − s̃₀` is known at date 0. -/
def LeeperEq (ρ : ℝ) (φ γ : ℕ → ℝ) (c0 : Ω → ℝ) (ui us π v : ℕ → Ω → ℝ) : Prop :=
  ρ • v 0 = c0 - π 0 ∧ ∀ t, 𝔼.E t (π (t + 1)) = φ t • π t + ui t ∧
    ρ • v (t + 1) = v t + (φ t • π t + ui t) - π (t + 1) - (γ t • v t + us (t + 1))

/-- Cochrane (2023), p. 512 (the substitution after (23.4)): taking `E_t` of the flow and using
the Fisher equation, `ρE_tv_{t+1} = (1 − γ_t)v_t − E_tu_{s,t+1}`. -/
theorem leeper_debt_eq {ρ : ℝ} {φ γ : ℕ → ℝ} {c0 : Ω → ℝ} {ui us π v : ℕ → Ω → ℝ}
    (hπa : 𝔼.Adapted π) (hva : 𝔼.Adapted v) (hui : 𝔼.Adapted ui)
    (h : LeeperEq 𝔼 ρ φ γ c0 ui us π v) (t : ℕ) :
    (1 - γ t) • v t = ρ • 𝔼.E t (v (t + 1)) + 𝔼.E t (us (t + 1)) := by
  obtain ⟨h1, h2⟩ := (h.2 t)
  have := congrArg (𝔼.E t) h2
  simp only [map_sub, map_add, map_smul, hva t, hπa t, hui t, h1] at this
  ext ω
  have e := congrFun this ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  linarith

/-- Cochrane (2023), Ch. 24, p. 523 (Davig and Leeper 2007): passive fiscal policy
(`γ_t ≠ 1`) together with ANY monetary rule (`φ_t`, e.g. active `φ_t > 1`) before `T`, and active
fiscal (`γ = 0`) / passive money (`|φ_P| < 1`) from `T` on: for `|ρ| < 1` and bounded adapted
disturbances there is exactly one bounded adapted equilibrium — "then we are in the
active-fiscal regime all along". -/
theorem fiscal_switch_selects {T : ℕ} {ρ φP : ℝ} {φ γ : ℕ → ℝ} (hρ : |ρ| < 1) (hφP : |φP| < 1)
    (hγ : ∀ t, t < T → γ t ≠ 1) (hγT : ∀ t, T ≤ t → γ t = 0) (hφT : ∀ t, T ≤ t → φ t = φP)
    {c0 : Ω → ℝ} (hc0 : 𝔼.E 0 c0 = c0) (hc0b : ∃ B, ∀ ω, |c0 ω| ≤ B)
    {ui us : ℕ → Ω → ℝ} (huib : BoundedProc ui) (huia : 𝔼.Adapted ui) (husb : BoundedProc us)
    (husa : 𝔼.Adapted us) :
    ∃! z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc z.1 ∧ BoundedProc z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ LeeperEq 𝔼 ρ φ γ c0 ui us z.1 z.2 := by
  -- the debt equation
  obtain ⟨Ms, hMs⟩ := husb
  obtain ⟨Mi, hMi⟩ := huib
  obtain ⟨B0, hB0⟩ := hc0b
  have hfb : BoundedProc (fun t => 𝔼.E t (us (t + 1))) :=
    ⟨Ms, fun t ω => 𝔼.abs_E_le (hMs (t + 1)) t ω⟩
  have hfa : 𝔼.Adapted (fun t => 𝔼.E t (us (t + 1))) := fun t => 𝔼.E_E_self t _
  obtain ⟨v, ⟨⟨Mv, hMv⟩, hva, hveq⟩, hvu⟩ := switch_scalar 𝔼 (c := fun t => 1 - γ t) (cA := 1)
    (d := ρ) (fun t ht => sub_ne_zero.mpr (hγ t ht).symm)
    (fun t ht => by simp [hγT t ht]) (by rwa [abs_one]) hfb hfa
  -- inflation, recursively
  let π : ℕ → Ω → ℝ := fun t => Nat.rec (c0 - ρ • v 0)
    (fun t πt => (1 - γ t) • v t + φ t • πt + ui t - us (t + 1) - ρ • v (t + 1)) t
  have hπ0 : π 0 = c0 - ρ • v 0 := rfl
  have hπs : ∀ t, π (t + 1) = (1 - γ t) • v t + φ t • π t + ui t - us (t + 1) - ρ • v (t + 1) :=
    fun t => rfl
  have hπa : 𝔼.Adapted π := by
    intro t
    induction t with
    | zero => rw [hπ0, map_sub, map_smul, hc0, hva 0]
    | succ t ih =>
      have k1 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hva t)
      have k2 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih
      have k3 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t)
      rw [hπs, map_sub, map_sub, map_add, map_add, map_smul, map_smul, map_smul, k1, k2, k3,
        husa, hva]
  have hsol : LeeperEq 𝔼 ρ φ γ c0 ui us π v := by
    refine ⟨by rw [hπ0]; abel, fun t => ⟨?_, ?_⟩⟩
    · have hv := hveq t
      rw [hπs, map_sub, map_sub, map_add, map_add, map_smul, map_smul, map_smul, hva t, hπa t,
        huia t]
      rw [hv]
      abel
    · rw [hπs]
      ext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hπb : BoundedProc π := by
    have hMv' : ∀ t ω, |v t ω| ≤ |Mv| := fun t ω => (hMv t ω).trans (le_abs_self _)
    have hMi' : ∀ t ω, |ui t ω| ≤ |Mi| := fun t ω => (hMi t ω).trans (le_abs_self _)
    have hMs' : ∀ t ω, |us t ω| ≤ |Ms| := fun t ω => (hMs t ω).trans (le_abs_self _)
    refine bounded_of_rec (T := T) (a := |φP|) (B := B0 + |ρ| * |Mv|)
      (K := |Mv| + |Mi| + |Ms| + |ρ| * |Mv|) (abs_nonneg _) hφP (c := fun t => |φ t|)
      (Kt := fun t => |1 - γ t| * |Mv| + |Mi| + |Ms| + |ρ| * |Mv|) (fun t => abs_nonneg _)
      (fun t ht => by simp [hφT t ht]) (fun t ht => by simp [hγT t ht]) (fun ω => ?_)
      (fun t ω => ?_)
    · rw [hπ0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add (hB0 ω) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMv' 0 ω) (abs_nonneg _)
    · rw [hπs]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 := mul_le_mul_of_nonneg_left (hMv' t ω) (abs_nonneg (1 - γ t))
      have e2 := mul_le_mul_of_nonneg_left (hMv' (t + 1) ω) (abs_nonneg ρ)
      have a1 := abs_sub ((1 - γ t) * v t ω + φ t * π t ω + ui t ω - us (t + 1) ω)
        (ρ * v (t + 1) ω)
      have a2 := abs_sub ((1 - γ t) * v t ω + φ t * π t ω + ui t ω) (us (t + 1) ω)
      have a3 := abs_add_le ((1 - γ t) * v t ω + φ t * π t ω) (ui t ω)
      have a4 := abs_add_le ((1 - γ t) * v t ω) (φ t * π t ω)
      rw [abs_mul] at a1 a4
      rw [abs_mul] at a4
      linarith [hMi' t ω, hMs' (t + 1) ω]
  refine ⟨(π, v), ⟨hπb, ⟨Mv, hMv⟩, hπa, hva, hsol⟩, ?_⟩
  rintro ⟨π', v'⟩ ⟨hb1, hb2, ha1, ha2, hs'⟩
  have hv' : v' = v := hvu v' ⟨hb2, ha2, fun t => leeper_debt_eq 𝔼 ha1 ha2 huia hs' t⟩
  subst hv'
  have hπ' : ∀ t, π' t = π t := by
    intro t
    induction t with
    | zero =>
      have := hs'.1
      ext ω
      have e := congrFun this ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
      simp only [hπ0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    | succ t ih =>
      rw [hπs, ← ih]
      have := (hs'.2 t).2
      ext ω
      have h := congrFun this ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      linarith
  exact Prod.ext (funext hπ') rfl

/-- Cochrane (2023), Ch. 24, pp. 523–524 ("The expected switch to active fiscal means that
fiscal shocks affect inflation immediately even in the locally-active money/passive fiscal
repayment regime"): in every equilibrium of the Leeper model, unexpected inflation is
`π_{t+1} − E_tπ_{t+1} = −ρ(v_{t+1} − E_tv_{t+1}) − (u_{s,t+1} − E_tu_{s,t+1})`. -/
theorem fiscal_switch_unexpected_inflation {ρ : ℝ} {φ γ : ℕ → ℝ} {c0 : Ω → ℝ}
    {ui us π v : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π) (hva : 𝔼.Adapted v) (hui : 𝔼.Adapted ui)
    (h : LeeperEq 𝔼 ρ φ γ c0 ui us π v) (t : ℕ) :
    π (t + 1) - 𝔼.E t (π (t + 1)) =
      -(ρ • (v (t + 1) - 𝔼.E t (v (t + 1)))) - (us (t + 1) - 𝔼.E t (us (t + 1))) := by
  have hd := leeper_debt_eq 𝔼 hπa hva hui h t
  obtain ⟨h1, h2⟩ := h.2 t
  rw [h1]
  ext ω
  have a := congrFun h2 ω
  have b := congrFun hd ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at a b ⊢
  linarith

/-- Cochrane (2023), Ch. 24, p. 523 (contrast): without the switch — the same active monetary
rule `|φ| > 1` at every date — inflation in a bounded equilibrium does not depend on fiscal
policy at all: two equilibria with the same monetary disturbance but different fiscal rules and
surplus disturbances have the same inflation. -/
theorem no_switch_fiscal_irrelevant {ρ φ : ℝ} (hφ : 1 < |φ|) {γ γ' : ℕ → ℝ} {c0 c0' : Ω → ℝ}
    {ui us us' π π' v v' : ℕ → Ω → ℝ} (huib : BoundedProc ui) (huia : 𝔼.Adapted ui)
    (hπb : BoundedProc π) (hπb' : BoundedProc π') (hπa : 𝔼.Adapted π) (hπa' : 𝔼.Adapted π')
    (h : LeeperEq 𝔼 ρ (fun _ => φ) γ c0 ui us π v)
    (h' : LeeperEq 𝔼 ρ (fun _ => φ) γ' c0' ui us' π' v') : π = π' := by
  obtain ⟨p, -, hpu⟩ := future_selection 𝔼 (T := 0) (φ := fun _ => φ) (φA := φ)
    (fun t ht => absurd ht (Nat.not_lt_zero t)) (fun _ _ => rfl) hφ huib huia
  rw [hpu π ⟨hπb, hπa, fun t => (h.2 t).1⟩, hpu π' ⟨hπb', hπa', fun t => (h'.2 t).1⟩]

/-- Cochrane (2023), Ch. 24, p. 523, worked example: perfect foresight, switch at `T = 1`,
active money `φ₀ = 2` and passive fiscal `γ₀ = 1/2` at date 0, then a peg (`φ = 0`) with active
fiscal (`γ = 0`), `ρ = 1/2`, `c₀ = 0`, `u_i = 0` and post-switch surpluses `u_{s,t} = δ`
(`t ≥ 1`). The unique bounded equilibrium has `π₀ = −2δ`, `π₁ = −4δ`, `π_t = 0` after: the
expected future surplus moves inflation at date 0, although money is active at date 0. -/
theorem fiscal_switch_example (δ : ℝ) :
    ∃! z : (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ), BoundedProc z.1 ∧ BoundedProc z.2 ∧
      perfectForesight.Adapted z.1 ∧ perfectForesight.Adapted z.2 ∧
      LeeperEq perfectForesight (1 / 2) (fun t => if t = 0 then 2 else 0)
        (fun t => if t = 0 then 1 / 2 else 0) (fun _ => 0) 0 (fun t _ => if t = 0 then 0 else δ)
        z.1 z.2 ∧ z.1 0 () = -2 * δ ∧ z.1 1 () = -4 * δ := by
  have hex := fiscal_switch_selects perfectForesight (T := 1) (ρ := 1 / 2) (φP := 0)
    (φ := fun t => if t = 0 then 2 else 0) (γ := fun t => if t = 0 then 1 / 2 else 0)
    (by norm_num [abs_of_pos]) (by simp) (fun t ht => by simp [show t = 0 by omega])
    (fun t ht => by simp [show t ≠ 0 by omega]) (fun t ht => by simp [show t ≠ 0 by omega])
    (c0 := fun _ => 0) rfl ⟨0, fun _ => by simp⟩ (ui := 0) ⟨0, fun _ _ => by simp⟩
    (fun _ => rfl) (us := fun t _ => if t = 0 then 0 else δ)
    ⟨|δ|, fun t _ => by dsimp only; split_ifs <;> simp⟩ (fun _ => rfl)
  let πe : ℕ → Unit → ℝ := fun t _ => if t = 0 then -2 * δ else if t = 1 then -4 * δ else 0
  let ve : ℕ → Unit → ℝ := fun t _ => if t = 0 then 4 * δ else 2 * δ
  have hsol : LeeperEq perfectForesight (1 / 2) (fun t => if t = 0 then 2 else 0)
      (fun t => if t = 0 then 1 / 2 else 0) (fun _ => 0) 0 (fun t _ => if t = 0 then 0 else δ)
      πe ve := by
    refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
    · funext ω
      simp [πe, ve]
      ring
    · funext ω
      rcases t with _ | _ | t <;> (simp [perfectForesight, πe]; try ring)
    · funext ω
      rcases t with _ | _ | t <;> simp [πe, ve] <;> ring
  have hb1 : BoundedProc πe := ⟨4 * |δ|, fun t _ => by
    simp only [πe]
    split_ifs <;> (simp [abs_mul]; try linarith [abs_nonneg δ])⟩
  have hb2 : BoundedProc ve := ⟨4 * |δ|, fun t _ => by
    simp only [ve]
    split_ifs <;> (simp [abs_mul]; try linarith [abs_nonneg δ])⟩
  obtain ⟨z, hz, hzu⟩ := hex
  have hz' : z = (πe, ve) := (hzu (πe, ve) ⟨hb1, hb2, fun _ => rfl, fun _ => rfl, hsol⟩).symm
  refine ⟨z, ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hz']
    simp [πe]
  · rw [hz']
    simp [πe]
  · exact hzu y ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1⟩

end Cochrane.ZeroBound.FutureSelection

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gabaix's behavioural new-Keynesian model at a peg

Cochrane (2023), Chapter 20, §20.2.6, pp. 482–483, eqs. (20.11)–(20.12):
`x_t = M E_tx_{t+1} − σ(i_t − E_tπ_{t+1})`, `π_t = M^f βE_tπ_{t+1} + κx_t`, with the interest rate
pegged, `i_t = ī`, for an arbitrary `ExpectationSystem`.

## Main results

* `gabaixEq_iff_solves`: the model is the backward system `z_t = A E_tz_{t+1} + w` with
  `A = [[M, σ], [κM, M^fβ + σκ]]`, `tr A = M + M^fβ + σκ`, `det A = MM^fβ` (`gabaix_tr_det`),
  and `1 − tr A + det A = (1 − M)(1 − βM^f) − σκ` (`gabaix_charpoly_one`).
* `gabaix_determinate_iff`: for `0 ≤ M, M^f ≤ 1`, `0 < β < 1`, `σκ ≥ 0`, the peg is determinate
  (a unique bounded equilibrium: "traditional forward-explosive, backward-stable dynamics") iff
  `(1 − M)(1 − βM^f) > σκ`; equivalently both roots of `A` lie inside the unit circle
  (`gabaix_roots_iff`). Then the unique bounded equilibrium is the steady state
  (`gabaix_unique`, `gabaix_steady`); otherwise there are other bounded equilibria
  (`gabaix_not_unique`).
* p. 483 corollaries: at the rational IS curve `M = 1` the peg is never determinate
  (`rational_IS_indeterminate`); as prices become less sticky determinacy always fails
  (`frictionless_limit_indeterminate`); determinacy requires `M < 1 − σκ`, `σκ < 1 − βM^f`
  (`determinate_bounded_away`); on the boundary a root equals one (`boundary_root_one`: the
  eigenvalues must cross one).
* Survey error E8, confirmed: "one needs `M` less than a half, together with … `σκ` less than
  about a half" is neither necessary (`e8_half_not_necessary`, `e8_half_not_necessary'`) nor
  sufficient (`e8_not_sufficient`).
-/

namespace Cochrane.ZeroBound.Gabaix

open Cochrane.ZeroBound

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the backward-form matrix
`A = [[M, σ], [κM, M^fβ + σκ]]` of the model at a peg. -/
def gabaixMatrix (M Mf β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![M, σ; κ * M, Mf * β + σ * κ]

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the constant forcing `(−σī, −κσī)` at the
peg `i_t = ī`. -/
def gabaixForcing {Ω : Type*} (σ κ ibar : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun _ => ![fun _ => -(σ * ibar), fun _ => -(κ * σ * ibar)]

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: trace and determinant of the peg matrix. -/
theorem gabaix_tr_det (M Mf β σ κ : ℝ) :
    tr2 (gabaixMatrix M Mf β σ κ) = M + Mf * β + σ * κ ∧
      det2 (gabaixMatrix M Mf β σ κ) = M * Mf * β := by
  simp only [tr2, det2, gabaixMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> ring

/-- Cochrane (2023), §20.2.6, p. 483: the characteristic polynomial at one,
`1 − tr A + det A = (1 − M)(1 − βM^f) − σκ`. -/
theorem gabaix_charpoly_one (M Mf β σ κ : ℝ) :
    1 - tr2 (gabaixMatrix M Mf β σ κ) + det2 (gabaixMatrix M Mf β σ κ) =
      (1 - M) * (1 - β * Mf) - σ * κ := by
  rw [(gabaix_tr_det M Mf β σ κ).1, (gabaix_tr_det M Mf β σ κ).2]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482, with `i_t = ī`:
`x_t = M E_tx_{t+1} − σ(ī − E_tπ_{t+1})` and `π_t = M^fβE_tπ_{t+1} + κx_t`. -/
def GabaixEq (M Mf β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = M * 𝔼.E t (x (t + 1)) ω - σ * (ibar - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = Mf * β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the model is the system
`z_t = A E_tz_{t+1} + w` of the core module. -/
theorem gabaixEq_iff_solves (M Mf β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) :
    GabaixEq 𝔼 M Mf β σ κ ibar x π ↔
      𝔼.Solves (gabaixMatrix M Mf β σ κ) (gabaixForcing σ κ ibar) (fun t => ![x t, π t]) := by
  constructor
  · intro h t i
    fin_cases i
    · funext ω
      obtain ⟨h1, -⟩ := h t ω
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, gabaixMatrix, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, gabaixForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · funext ω
      obtain ⟨h1, h2⟩ := h t ω
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, gabaixMatrix, Matrix.of_apply, Matrix.cons_val_zero, gabaixForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, h1]
      ring
  · intro h t ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      gabaixMatrix, Matrix.of_apply, Matrix.cons_val_one, gabaixForcing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at h0 h1
    refine ⟨by linarith, ?_⟩
    rw [h1, h0]
    ring

/-- Cochrane (2023), §20.2.6, pp. 482–483 (survey E8, exact boundary): for `0 ≤ M ≤ 1`,
`0 ≤ M^f ≤ 1`, `0 < β < 1`, `σκ ≥ 0`, the Schur–Cohn condition holds iff
`(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_schur_iff {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    SchurStable (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ)) ↔
      σ * κ < (1 - M) * (1 - β * Mf) := by
  obtain ⟨ht, hd⟩ := gabaix_tr_det M Mf β σ κ
  rw [ht, hd]
  have hdet0 : 0 ≤ M * Mf * β := by positivity
  have hdet1 : M * Mf * β < 1 := by
    have : M * Mf ≤ 1 := by nlinarith
    nlinarith
  have htr : 0 ≤ M + Mf * β + σ * κ := by positivity
  unfold SchurStable
  rw [abs_of_nonneg hdet0, abs_of_nonneg htr]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    exact ⟨hdet1, by nlinarith⟩

/-- Cochrane (2023), §20.2.6, pp. 482–483: in terms of roots, both roots of
`λ² − tr A λ + det A` lie inside the unit circle (the forward dynamics are explosive in both
directions, "forward-explosive, backward-stable") iff `(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_roots_iff {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    (‖root₁ (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ))‖ < 1 ∧
      ‖root₂ (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ))‖ < 1) ↔
      σ * κ < (1 - M) * (1 - β * Mf) := by
  rw [← schurStable_iff_roots]
  exact gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ

/-- Cochrane (2023), §20.2.6, pp. 482–483 (survey E8): the peg in Gabaix's model is determinate
(at most one bounded adapted equilibrium for every forcing) iff `(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_determinate_iff [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    𝔼.Determinate (gabaixMatrix M Mf β σ κ) ↔ σ * κ < (1 - M) * (1 - β * Mf) := by
  rw [𝔼.determinate_iff]
  exact gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the steady state at the peg,
`π̄ = −σκī/((1 − M)(1 − βM^f) − σκ)`, `x̄ = (1 − βM^f)π̄/κ`. -/
theorem gabaix_steady {M Mf β σ κ ibar : ℝ} (hκ : κ ≠ 0)
    (hp : (1 - M) * (1 - β * Mf) - σ * κ ≠ 0) :
    GabaixEq 𝔼 M Mf β σ κ ibar
      (fun _ _ => (1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ)
      (fun _ _ => -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) := by
  have hPD : -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ) *
      ((1 - M) * (1 - β * Mf) - σ * κ) = -(σ * κ * ibar) := div_mul_cancel₀ _ hp
  intro t ω
  simp only [𝔼.const]
  generalize -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ) = P at hPD ⊢
  constructor
  · apply mul_left_cancel₀ hκ
    field_simp
    linear_combination hPD
  · field_simp
    ring

/-- Cochrane (2023), §20.2.6, p. 482: under `(1 − M)(1 − βM^f) > σκ` the unique bounded adapted
equilibrium at the peg is the steady state. -/
theorem gabaix_unique {M Mf β σ κ ibar : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) (hκ : κ ≠ 0)
    (hc : σ * κ < (1 - M) * (1 - β * Mf)) {x π : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hπa : 𝔼.Adapted π) (hxb : BoundedProc x) (hπb : BoundedProc π)
    (h : GabaixEq 𝔼 M Mf β σ κ ibar x π) :
    x = (fun _ _ => (1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ) ∧
      π = (fun _ _ => -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) := by
  have hp : (1 - M) * (1 - β * Mf) - σ * κ ≠ 0 := by linarith
  have hs := gabaix_steady 𝔼 (ibar := ibar) hκ hp
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mp, hMp⟩ := hπb
  have heq := 𝔼.system_unique ((gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mpr hc)
    ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp h)
    ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp hs)
    (fun t i => by fin_cases i <;> simp [hxa t, hπa t])
    (fun t i => by fin_cases i <;> simp [𝔼.const])
    ⟨max Mx Mp, fun t i ω => by
      fin_cases i
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMp t ω).trans (le_max_right _ _)⟩
    ⟨|(1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ| +
      |-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)|, fun t i ω => by
      fin_cases i
      · simp
      · simp⟩
  exact ⟨funext fun t => by simpa using congrFun heq t |> fun e => congrFun e 0,
    funext fun t => by simpa using congrFun heq t |> fun e => congrFun e 1⟩

/-- Cochrane (2023), §20.2.6, p. 483: when `(1 − M)(1 − βM^f) ≤ σκ`, next to every bounded
adapted equilibrium there is another one (the new-Keynesian indeterminacy reappears). -/
theorem gabaix_not_unique [Nonempty Ω] {M Mf β σ κ ibar : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ)
    (hc : (1 - M) * (1 - β * Mf) ≤ σ * κ) {x π : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hπa : 𝔼.Adapted π) (hxb : BoundedProc x) (hπb : BoundedProc π)
    (h : GabaixEq 𝔼 M Mf β σ κ ibar x π) :
    ∃ y, 𝔼.Solves (gabaixMatrix M Mf β σ κ) (gabaixForcing σ κ ibar) y ∧ 𝔼.AdaptedVec y ∧
      BoundedVec y ∧ y ≠ fun t => ![x t, π t] := by
  have hn : ¬ SchurStable (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ)) :=
    fun hs => absurd ((gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mp hs) (not_lt.mpr hc)
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mp, hMp⟩ := hπb
  exact 𝔼.system_not_unique hn ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp h)
    (fun t i => by fin_cases i <;> simp [hxa t, hπa t])
    ⟨max Mx Mp, fun t i ω => by
      fin_cases i
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMp t ω).trans (le_max_right _ _)⟩

/-- Cochrane (2023), §20.2.6, p. 483 ("Gabaix's result is bounded away from rationality"): with
the rational IS curve `M = 1` the peg is never determinate. -/
theorem rational_IS_indeterminate [Nonempty Ω] {Mf β σ κ : ℝ} (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    ¬ 𝔼.Determinate (gabaixMatrix 1 Mf β σ κ) := by
  rw [gabaix_determinate_iff 𝔼 zero_le_one le_rfl hMf0 hMf1 hβ0 hβ1 hσκ]
  simp only [sub_self, zero_mul, not_lt]
  exact hσκ

/-- Cochrane (2023), §20.2.6, p. 483 ("As prices become less sticky, new-Keynesian dynamics
always reappear"): for `σ > 0` and any `M, M^f`, the peg is indeterminate for all `κ ≥ 1/σ`. -/
theorem frictionless_limit_indeterminate [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M)
    (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 1 / σ ≤ κ) : ¬ 𝔼.Determinate (gabaixMatrix M Mf β σ κ) := by
  have h1 : 1 ≤ σ * κ := by
    rw [div_le_iff₀ hσ] at hκ
    linarith
  rw [gabaix_determinate_iff 𝔼 hM0 hM1 hMf0 hMf1 hβ0 hβ1 (by linarith), not_lt]
  have : (1 - M) * (1 - β * Mf) ≤ 1 := by
    have a : 0 ≤ 1 - M := by linarith
    have b : 0 ≤ β * Mf := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §20.2.6, p. 483 ("bounded away from rationality … bounded away from the
frictionless price limit"): determinacy requires `M < 1 − σκ`, `σκ < 1 − βM^f` and `σκ < 1`. -/
theorem determinate_bounded_away [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ)
    (h : 𝔼.Determinate (gabaixMatrix M Mf β σ κ)) :
    M < 1 - σ * κ ∧ σ * κ < 1 - β * Mf ∧ σ * κ < 1 := by
  have hc := (gabaix_determinate_iff 𝔼 hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mp h
  have a : 0 ≤ 1 - M := by linarith
  have b : 0 ≤ β * Mf := by positivity
  have c : β * Mf ≤ 1 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Cochrane (2023), §20.2.6, p. 482 ("Eigenvalues must switch from greater to less than one"):
on the boundary `(1 − M)(1 − βM^f) = σκ`, one is a root of the characteristic polynomial. -/
theorem boundary_root_one {M Mf β σ κ : ℝ} (h : (1 - M) * (1 - β * Mf) = σ * κ) :
    (1 : ℝ) ^ 2 - tr2 (gabaixMatrix M Mf β σ κ) * 1 + det2 (gabaixMatrix M Mf β σ κ) = 0 := by
  have := gabaix_charpoly_one M Mf β σ κ
  rw [h, sub_self] at this
  linarith

/-- Cochrane (2023), p. 483, survey error E8: "`M` less than a half" is not necessary. With
`M = M^f = 3/5`, `β = 0.99`, `σ = 1`, `κ = 1/10` the peg is determinate. -/
theorem e8_half_not_necessary [Nonempty Ω] :
    (1 / 2 : ℝ) < 3 / 5 ∧ 𝔼.Determinate (gabaixMatrix (3 / 5) (3 / 5) (99 / 100) 1 (1 / 10)) := by
  refine ⟨by norm_num, ?_⟩
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

/-- Cochrane (2023), p. 483, survey error E8 (the survey's example): `M = 0.9`, `M^f = 1/2`,
`β = 0.99`, `σκ = 0.05` is determinate, so `M` can be close to one. -/
theorem e8_half_not_necessary' [Nonempty Ω] :
    𝔼.Determinate (gabaixMatrix (9 / 10) (1 / 2) (99 / 100) 1 (1 / 20)) := by
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

/-- Cochrane (2023), p. 483, survey error E8: "`M` less than a half, together with … `σκ` less
than about a half" is not sufficient: `M = M^f = 2/5`, `β = 0.99`, `σκ = 2/5` is
indeterminate. -/
theorem e8_not_sufficient [Nonempty Ω] :
    (2 / 5 : ℝ) < 1 / 2 ∧ (1 : ℝ) * (2 / 5) < 1 / 2 ∧
      ¬ 𝔼.Determinate (gabaixMatrix (2 / 5) (2 / 5) (99 / 100) 1 (2 / 5)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

end Cochrane.ZeroBound.Gabaix

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Covid inflation: model claims

Cochrane (2023), Chapter 21, pp. 486–494. Only the model claims of this chapter are formalised;
the rest is data and speculation.

## Main results

* Helicopter drop (pp. 487, 490), frictionless one-period debt `B/P = S` (valuation equation):
  more debt with unchanged surpluses raises the price level proportionally
  (`helicopter_exact`, 30% more debt ⇒ 30% higher prices, `helicopter_thirty`); with a fraction
  `f` of the new debt backed, `P′/P = (1 + Δ)/(1 + fΔ)` and the real value of debt rises by the
  factor `1 + fΔ` (`partial_backing`). p. 488, survey error E10, confirmed: two-thirds backing
  of 30% new debt gives 8.33% inflation (`P′/P = 13/12`), not 10%, while "+20% real value" is
  exact (`partial_backing_example`, `e10_printed_pair_inconsistent`); 10% is the first-order term
  `d(P′/P)/dΔ|₀ = 1 − f` (`hasDerivAt_priceRatio`) with exact remainder
  `−f(1 − f)Δ²/(1 + fΔ)` (`priceRatio_remainder`). More backing, less inflation
  (`priceRatio_strictAnti`); only reserves unbacked (`reserves_only_unbacked`).
* p. 491: in the frictionless model, fiscal news moves only unexpected inflation
  (`fiscal_news_only_unexpected`, (5.10)–(5.12)).
* p. 492: under an interest-rate peg with fiscal backing, inflation returns to the peg
  (`peg_inflation_returns`, from `ZLBPeg`).
* p. 493: Phillips-curve disinflation algebra (`pc_output`, `disinflation_joint`,
  `disinflation_alone`, `joint_less_painful`, `painless_limit`, `fisherian_rate_fall`).
* p. 493: interest-cost arithmetic (`interest_cost_four_times`) and the 1981 bond windfall,
  survey error E11, confirmed: the real return is 11.5%, not 12% (`windfall_real_return`).
* Data arithmetic (pp. 486, 488): `cpi_rise`, `table_21_1`, `debt_increase_nearly_30`.
-/

namespace Cochrane.ZeroBound.Covid

open Filter Topology
open Cochrane.ZeroBound

/-! ## The helicopter drop -/

/-- Cochrane (2023), p. 487 (frictionless valuation equation `B_{t−1}/P_t = E_t∑βʲs_{t+j}`, §2):
the price level `P = B/S` given nominal debt `B` and the present value of surpluses `S`. -/
noncomputable def priceLevel (B S : ℝ) : ℝ := B / S

/-- Cochrane (2023), p. 490 ("If the expansion came with no change at all in expected future
surpluses, that will result in a cumulative 30% price-level rise"): with `S` unchanged,
`(1 + Δ)B` of debt gives `P′/P = 1 + Δ`. -/
theorem helicopter_exact {B S Δ : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) :
    priceLevel ((1 + Δ) * B) S / priceLevel B S = 1 + Δ := by
  unfold priceLevel
  field_simp

/-- Cochrane (2023), pp. 487, 490: a 30% debt expansion with no new backing gives a 30% price
rise. -/
theorem helicopter_thirty {B S : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) :
    priceLevel ((1 + 3 / 10) * B) S / priceLevel B S - 1 = 3 / 10 := by
  rw [helicopter_exact hB hS]
  ring

/-- Cochrane (2023), p. 488 ("If people expect two thirds of the debt to be repaid"): the price
ratio `(1 + Δ)/(1 + fΔ)` when debt grows by the fraction `Δ` and the fraction `f` of the new debt
is backed by new surpluses. -/
noncomputable def priceRatio (f Δ : ℝ) : ℝ := (1 + Δ) / (1 + f * Δ)

/-- Cochrane (2023), p. 488: with debt `(1 + Δ)B` and surpluses `S′ = (1 + fΔ)S` (the fraction
`f` of the new debt backed at the old price level), `P′/P = (1 + Δ)/(1 + fΔ)` and the real
value of debt rises by the factor `1 + fΔ`. -/
theorem partial_backing {B S f Δ : ℝ} (hB : B ≠ 0) (hS : S ≠ 0) (hΔ : 1 + Δ ≠ 0) :
    priceLevel ((1 + Δ) * B) ((1 + f * Δ) * S) / priceLevel B S = priceRatio f Δ ∧
      (1 + Δ) * B / priceLevel ((1 + Δ) * B) ((1 + f * Δ) * S) =
        (1 + f * Δ) * (B / priceLevel B S) := by
  unfold priceLevel priceRatio
  constructor <;> field_simp

/-- Cochrane (2023), p. 488, survey error E10: with 30% new debt of which two thirds is backed,
the price level rises by the factor `13/12` (8.33%), and the real value of debt by exactly
`6/5` (+20%). -/
theorem partial_backing_example :
    priceRatio (2 / 3) (3 / 10) = 13 / 12 ∧ priceRatio (2 / 3) (3 / 10) - 1 < 1 / 10 ∧
      1 + (2 / 3 : ℝ) * (3 / 10) = 6 / 5 := by
  unfold priceRatio
  norm_num

/-- Cochrane (2023), p. 488, survey error E10: the printed pair "inflation stops at a cumulative
10% and the real value of debt rises by 20%" is inconsistent with a 30% rise in nominal debt,
since `1.1 × 1.2 ≠ 1.3`. -/
theorem e10_printed_pair_inconsistent : (1 + 1 / 10 : ℝ) * (1 + 1 / 5) ≠ 1 + 3 / 10 := by
  norm_num

/-- Cochrane (2023), p. 488: the 10% of the text is the first-order effect,
`d/dΔ [(1 + Δ)/(1 + fΔ)] = 1 − f` at `Δ = 0` (`= 1/3` for two-thirds backing, times `Δ = 0.3`). -/
theorem hasDerivAt_priceRatio (f : ℝ) : HasDerivAt (priceRatio f) (1 - f) 0 := by
  have h1 : HasDerivAt (fun Δ : ℝ => 1 + Δ) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun Δ : ℝ => 1 + f * Δ) f 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul f).const_add 1
  have h := HasDerivAt.div h1 h2 (by simp)
  unfold priceRatio
  convert h using 1
  simp

/-- Cochrane (2023), p. 488: the exact remainder of the first-order approximation,
`(1 + Δ)/(1 + fΔ) − 1 − (1 − f)Δ = −f(1 − f)Δ²/(1 + fΔ)`. -/
theorem priceRatio_remainder {f Δ : ℝ} (h : 1 + f * Δ ≠ 0) :
    priceRatio f Δ - 1 - (1 - f) * Δ = -(f * (1 - f) * Δ ^ 2) / (1 + f * Δ) := by
  unfold priceRatio
  rw [eq_div_iff h, sub_mul, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- Cochrane (2023), p. 488: at two-thirds backing of 30% new debt the first-order term is
exactly the book's 10%. -/
theorem first_order_example : (1 - 2 / 3 : ℝ) * (3 / 10) = 1 / 10 := by norm_num

/-- Cochrane (2023), p. 490 ("if people expect partial repayment, the price-level increase will
be smaller"): for `Δ > 0` the price ratio is strictly decreasing in the backed fraction
`f ≥ 0`. -/
theorem priceRatio_strictAnti {Δ : ℝ} (hΔ : 0 < Δ) :
    StrictAntiOn (fun f => priceRatio f Δ) (Set.Ici 0) := by
  intro f₁ hf₁ f₂ hf₂ hlt
  simp only [Set.mem_Ici] at hf₁ hf₂
  unfold priceRatio
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  nlinarith

/-- Cochrane (2023), p. 490 ("If only the increase in reserves is considered unbacked"): with
3/5 of the 30% new debt in unbacked reserves (`f = 2/5`) the price level rises by `65/56`,
less than the 30% of a fully unbacked expansion. -/
theorem reserves_only_unbacked :
    priceRatio (2 / 5) (3 / 10) = 65 / 56 ∧ priceRatio (2 / 5) (3 / 10) < 1 + 3 / 10 := by
  unfold priceRatio
  norm_num

/-! ## Fiscal news and unexpected inflation (p. 491) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 491 ("bad fiscal news can only affect unexpected inflation"), in the
frictionless model (5.10)–(5.12): if `i_t = E_tπ_{t+1}` and `π_{t+1} − E_tπ_{t+1} = −ε_{t+1}`
in two economies with the same interest-rate path but different fiscal news `ε`, `ε′`, expected
inflation is the same and `π_{t+1} = i_t − ε_{t+1}`. -/
theorem fiscal_news_only_unexpected {i π π' ε ε' : ℕ → Ω → ℝ}
    (hf : ∀ t, i t = 𝔼.E t (π (t + 1))) (hf' : ∀ t, i t = 𝔼.E t (π' (t + 1)))
    (hv : ∀ t, π (t + 1) - 𝔼.E t (π (t + 1)) = -ε (t + 1))
    (hv' : ∀ t, π' (t + 1) - 𝔼.E t (π' (t + 1)) = -ε' (t + 1)) (t : ℕ) :
    𝔼.E t (π (t + 1)) = 𝔼.E t (π' (t + 1)) ∧ π (t + 1) = i t - ε (t + 1) ∧
      π (t + 1) - π' (t + 1) = ε' (t + 1) - ε (t + 1) := by
  refine ⟨by rw [← hf t, ← hf' t], ?_, ?_⟩
  · rw [hf t, sub_eq_add_neg, ← hv t]
    abel
  · have a := hv t
    have b := hv' t
    rw [← hf t] at a
    rw [← hf' t] at b
    rw [show π (t + 1) = i t + -ε (t + 1) by rw [← a]; abel,
      show π' (t + 1) = i t + -ε' (t + 1) by rw [← b]; abel]
    abel

/-- Cochrane (2023), p. 492 ("If the Fed left the interest rate alone, inflation would
eventually return"): in the sticky-price model at a peg with the fiscal valuation equation, the
unique equilibrium (`ZLBPeg.fiscal_selects`) has expected inflation converging back to the
peg. -/
theorem peg_inflation_returns {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (ZLBPeg.pegPi ibar (ZLBPeg.fiscalP β σ κ ρ ε) (s + k)) ω) atTop
      (𝓝 ibar) :=
  ZLBPeg.fiscal_stable 𝔼 hβ hσκ hκ hρ0 hρ1 hεa hεb hεmd s ω

/-! ## Phillips-curve disinflation (p. 493) -/

/-- Cochrane (2023), p. 493: the Phillips curve `π_t = βE_tπ_{t+1} + κx_t` determines output,
`x_t = (π_t − βE_tπ_{t+1})/κ`. -/
theorem pc_output {β κ π Eπ x : ℝ} (hκ : κ ≠ 0) :
    π = β * Eπ + κ * x ↔ x = (π - β * Eπ) / κ := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), p. 493 ("inflation reduction can be relatively painless if expected
inflation declines"): lowering both `π_t` and `E_tπ_{t+1}` by `d` changes output by
`−(1 − β)d/κ`. -/
theorem disinflation_joint (β κ π Eπ d : ℝ) :
    (π - d - β * (Eπ - d)) / κ - (π - β * Eπ) / κ = -((1 - β) * d / κ) := by
  ring

/-- Cochrane (2023), p. 493 ("and painful if it does not decline"): lowering `π_t` by `d` with
`E_tπ_{t+1}` unchanged changes output by `−d/κ`. -/
theorem disinflation_alone (β κ π Eπ d : ℝ) :
    (π - d - β * Eπ) / κ - (π - β * Eπ) / κ = -(d / κ) := by
  ring

/-- Cochrane (2023), p. 493: for `0 < β < 1`, `κ > 0`, `d > 0`, the output cost of a credible
joint disinflation is strictly smaller than that of a disinflation without lower expected
inflation. -/
theorem joint_less_painful {β κ d : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hd : 0 < d) :
    |-((1 - β) * d / κ)| < |-(d / κ)| := by
  rw [abs_neg, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  apply div_lt_div_of_pos_right _ hκ
  nlinarith

/-- Cochrane (2023), p. 493 ("relatively painless"): the output cost `(1 − β)d/κ` of a joint
disinflation vanishes as `β → 1`. -/
theorem painless_limit (κ d : ℝ) :
    Tendsto (fun β : ℝ => (1 - β) * d / κ) (𝓝 1) (𝓝 0) := by
  have h : Continuous (fun β : ℝ => (1 - β) * d / κ) := by fun_prop
  simpa using h.tendsto 1

/-- Cochrane (2023), p. 493 ("nominal interest rates fall immediately in Fisherian fashion"):
with `i_t = r + E_tπ_{t+1}`, lowering expected inflation by `d` lowers the nominal rate by `d`
at once. -/
theorem fisherian_rate_fall (r Eπ d : ℝ) : (r + (Eπ - d)) - (r + Eπ) = -d := by ring

/-! ## Interest costs and the 1981 windfall (p. 493) -/

/-- Cochrane (2023), p. 493 ("four times larger real interest costs … 5% real interest rates mean
5% of GDP additional deficit"): the interest cost `r·b` at `r = 5%` is 5% of GDP at a 100%
debt ratio, four times the cost at the 25% ratio of 1980. -/
theorem interest_cost_four_times :
    (5 / 100 : ℝ) * 1 = 5 / 100 ∧ ((5 / 100 : ℝ) * 1) / ((5 / 100) * (1 / 4)) = 4 := by
  norm_num

/-- Cochrane (2023), p. 493: for any real rate `r ≠ 0`, the interest cost at a 100% debt ratio is
four times that at 25%. -/
theorem interest_cost_ratio {r : ℝ} (hr : r ≠ 0) : (r * 1) / (r * (1 / 4)) = 4 := by
  field_simp

/-- Cochrane (2023), p. 493, survey error E11: a 15.84% nominal yield with 3.9% inflation gives
the real return `(1 + y)/(1 + π) − 1 = (y − π)/(1 + π)`, which is between 11.49% and 11.5%,
not 12% (12% is the approximation `y − π = 11.94%`). -/
theorem windfall_real_return :
    (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 = (1584 / 10000 - 39 / 1000) / (1 + 39 / 1000) ∧
      1149 / 10000 < (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 ∧
      (1 + 1584 / 10000 : ℝ) / (1 + 39 / 1000) - 1 < 115 / 1000 ∧
      (1584 / 10000 - 39 / 1000 : ℝ) = 1194 / 10000 := by
  norm_num

/-! ## Data arithmetic (pp. 486, 488) -/

/-- Cochrane (2023), p. 486: the CPI rose from 263.161 to 276.724, i.e. by 5.15%, and over the
eight months this is a 7.8% annual rate: `r^{3/2} ∈ (1.078, 1.079)`, stated as
`r³ ∈ (1.078², 1.079²)`. -/
theorem cpi_rise :
    (515 / 10000 : ℝ) < 276.724 / 263.161 - 1 ∧ (276.724 / 263.161 : ℝ) - 1 < 516 / 10000 ∧
      (1.078 : ℝ) ^ 2 < (276.724 / 263.161) ^ 3 ∧ ((276.724 : ℝ) / 263.161) ^ 3 < 1.079 ^ 2 := by
  norm_num

/-- Cochrane (2023), Table 21.1, p. 488: the arithmetic of the table (A + B − C and the
differences). -/
theorem table_21_1 :
    (17187 + 3427 - 2329 : ℝ) = 18285 ∧ (22304 + 6389 - 5431 : ℝ) = 23262 ∧
      (23262 - 18285 : ℝ) = 4977 ∧ (22304 - 17187 : ℝ) = 5117 ∧ (6389 - 3427 : ℝ) = 2962 ∧
      (5431 - 2329 : ℝ) = 3102 ∧ (20994 - 15325 : ℝ) = 5669 := by
  norm_num

/-- Cochrane (2023), p. 486 ("$5 trillion is a nearly 30% increase in the $17 trillion of debt
outstanding"): `5/17 ∈ (0.29, 0.30)`. -/
theorem debt_increase_nearly_30 : (29 / 100 : ℝ) < 5 / 17 ∧ (5 / 17 : ℝ) < 3 / 10 := by
  norm_num

end Cochrane.ZeroBound.Covid

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The continuous-time new-Keynesian model: roots, integrals and linear ODEs

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–475
(the roots `λ^f`, `λ^b` and the forward-stable solution (20.8)), building on §5.7 and Online
Appendix A1 §1.12, pp. 579–580. Much of the calculus is restated from the Cochrane Chapter 5
project (`StickyPriceFiscal.CTSimple`).

Continuous time is formalised with deterministic paths `ℝ → ℝ`, exact `HasDerivAt` ODEs, and
infinite-horizon integrals as genuine Bochner integrals with proved integrability.

## Main results

* The roots `λ^f = (√(ρ²+4κσ)+ρ)/2`, `λ^b = (√(ρ²+4κσ)−ρ)/2` (p. 475): `lamf_pos`, `lamb_pos`,
  `lamf_mul_lamb` (`λ^fλ^b = κσ`), `lamf_sub_lamb` (`λ^f − λ^b = ρ`), `lamf_add_lamb`,
  `charpoly_factor` (`D² − ρD − κσ = (D − λ^f)(D + λ^b)`); monotonicity and divergence in `κ`
  (`lamb_strictMono`, `lamb_tendsto_atTop`, `lamf_tendsto_atTop`).
* Forward and backward integrals: `fwdInt a z t = ∫_0^∞ e^{−aτ} z_{t+τ} dτ` and the two-sided
  backward integral `bwdInfInt b z t = ∫_0^∞ e^{−bτ} z_{t−τ} dτ = ∫_{−∞}^t e^{−b(t−s)} z_s ds`,
  with their ODEs `fwdInt_hasDerivAt`, `bwdInfInt_hasDerivAt`.
* Variation of constants with a countable exceptional set (piecewise-smooth paths):
  `linear_ode_Icc`, `affine_ode_Icc`, `linear_ode_Ici`, `unstable_bdd_zero`, `linear_ode_univ`.
* The Green's-function solution (20.8): `greenPi`, `greenPi_hasDerivAt`, and
  `forward_stable_iff`: a solution of `(D − λ^f)(D + λ^b)π = −z` is forward-stable
  (`e^{−λ^f t}π_t → 0`) iff it is `greenPi C` for some `C` (then unique, `greenPi_injective`).
-/

namespace Cochrane.ZeroBound.ContinuousTimeNK

open Filter Topology MeasureTheory

/-! ## The roots `λ^f`, `λ^b` (p. 475) -/

/-- Cochrane (2023), §20.2.2, p. 475: the forward root `λ^f = (√(ρ² + 4κσ) + ρ)/2`. -/
noncomputable def lamf (ρ κ σ : ℝ) : ℝ := (Real.sqrt (ρ ^ 2 + 4 * κ * σ) + ρ) / 2

/-- Cochrane (2023), §20.2.2, p. 475: the backward root `λ^b = (√(ρ² + 4κσ) − ρ)/2`. -/
noncomputable def lamb (ρ κ σ : ℝ) : ℝ := (Real.sqrt (ρ ^ 2 + 4 * κ * σ) - ρ) / 2

/-- Cochrane (2023), §20.2.2, p. 475: for `κ, σ > 0`, `|ρ| < √(ρ² + 4κσ)`. -/
theorem abs_lt_sqrt_disc {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    |ρ| < Real.sqrt (ρ ^ 2 + 4 * κ * σ) := by
  rw [Real.lt_sqrt (abs_nonneg ρ), sq_abs]
  nlinarith [mul_pos hκ hσ]

/-- Cochrane (2023), §20.2.2, p. 475: `(√(ρ² + 4κσ))² = ρ² + 4κσ` for `κσ ≥ 0`. -/
theorem sq_sqrt_disc {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    Real.sqrt (ρ ^ 2 + 4 * κ * σ) ^ 2 = ρ ^ 2 + 4 * κ * σ :=
  Real.sq_sqrt (by nlinarith [mul_pos hκ hσ, sq_nonneg ρ])

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f > 0`. -/
theorem lamf_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lamf ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := neg_abs_le ρ
  unfold lamf
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: `λ^b > 0`. -/
theorem lamb_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lamb ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := le_abs_self ρ
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.2, p. 475 (A1 p. 579): `λ^f λ^b = κσ`. -/
theorem lamf_mul_lamb {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamf ρ κ σ * lamb ρ κ σ = κ * σ := by
  have h := sq_sqrt_disc (ρ := ρ) hκ hσ
  unfold lamf lamb
  linear_combination h / 4

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f − λ^b = ρ`. -/
theorem lamf_sub_lamb (ρ κ σ : ℝ) : lamf ρ κ σ - lamb ρ κ σ = ρ := by
  unfold lamf lamb
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f + λ^b = √(ρ² + 4κσ)`. -/
theorem lamf_add_lamb (ρ κ σ : ℝ) :
    lamf ρ κ σ + lamb ρ κ σ = Real.sqrt (ρ ^ 2 + 4 * κ * σ) := by
  unfold lamf lamb
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f + λ^b > 0`. -/
theorem lamf_add_lamb_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    0 < lamf ρ κ σ + lamb ρ κ σ :=
  add_pos (lamf_pos hκ hσ) (lamb_pos hκ hσ)

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f` is a root of `λ² − ρλ − κσ`. -/
theorem lamf_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamf ρ κ σ ^ 2 = ρ * lamf ρ κ σ + κ * σ := by
  linear_combination lamf_mul_lamb (ρ := ρ) hκ hσ + lamf ρ κ σ * lamf_sub_lamb ρ κ σ

/-- Cochrane (2023), §20.2.2, p. 475: `−λ^b` is a root of `λ² − ρλ − κσ`. -/
theorem lamb_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamb ρ κ σ ^ 2 + ρ * lamb ρ κ σ = κ * σ := by
  linear_combination lamf_mul_lamb (ρ := ρ) hκ hσ - lamb ρ κ σ * lamf_sub_lamb ρ κ σ

/-- Cochrane (2023), §20.2.2, p. 475 (A1 p. 579): the factorisation
`(D − λ^f)(D + λ^b) = D² − ρD − κσ` of the characteristic polynomial. -/
theorem charpoly_factor {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (z : ℝ) :
    (z - lamf ρ κ σ) * (z + lamb ρ κ σ) = z ^ 2 - ρ * z - κ * σ := by
  linear_combination (-z) * lamf_sub_lamb ρ κ σ - lamf_mul_lamb (ρ := ρ) hκ hσ

/-- Cochrane (2023), §20.2.2, p. 475: `κσ/λ^f = λ^b`. -/
theorem kappa_sigma_div_lamf {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    κ * σ / lamf ρ κ σ = lamb ρ κ σ := by
  rw [div_eq_iff (lamf_pos hκ hσ).ne', ← lamf_mul_lamb hκ hσ]
  ring

/-- Cochrane (2023), §20.2.2, p. 475: with a nonnegative discount rate, `λ^b ≤ λ^f`. -/
theorem lamb_le_lamf {ρ κ σ : ℝ} (hρ : 0 ≤ ρ) : lamb ρ κ σ ≤ lamf ρ κ σ := by
  have := lamf_sub_lamb ρ κ σ
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: the lower bound `λ^b ≥ √(κσ) − ρ/2`. -/
theorem sqrt_sub_le_lamb (ρ κ σ : ℝ) :
    Real.sqrt (κ * σ) - ρ / 2 ≤ lamb ρ κ σ := by
  have h4 : Real.sqrt (4 * (κ * σ)) = 2 * Real.sqrt (κ * σ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hle : Real.sqrt (4 * (κ * σ)) ≤ Real.sqrt (ρ ^ 2 + 4 * κ * σ) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ρ])
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: the lower bound `λ^f ≥ √(κσ) + ρ/2`. -/
theorem sqrt_add_le_lamf (ρ κ σ : ℝ) :
    Real.sqrt (κ * σ) + ρ / 2 ≤ lamf ρ κ σ := by
  have := sqrt_sub_le_lamb ρ κ σ
  have := lamf_sub_lamb ρ κ σ
  linarith

/-- Cochrane (2023), §20.2.4, p. 479 ("less sticky ⇒ faster dynamics"): `λ^b` is strictly
increasing in `κ` on `κ > 0`. -/
theorem lamb_strictMono {ρ κ κ' σ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hlt : κ < κ') :
    lamb ρ κ σ < lamb ρ κ' σ := by
  have h : Real.sqrt (ρ ^ 2 + 4 * κ * σ) < Real.sqrt (ρ ^ 2 + 4 * κ' * σ) :=
    Real.sqrt_lt_sqrt (by nlinarith [mul_pos hκ hσ, sq_nonneg ρ]) (by nlinarith)
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `λ^f` is strictly increasing in `κ` on `κ > 0`. -/
theorem lamf_strictMono {ρ κ κ' σ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hlt : κ < κ') :
    lamf ρ κ σ < lamf ρ κ' σ := by
  have := lamb_strictMono (ρ := ρ) hσ hκ hlt
  have := lamf_sub_lamb ρ κ σ
  have := lamf_sub_lamb ρ κ' σ
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `√(κσ) → ∞` as `κ → ∞` (`σ > 0`). -/
theorem sqrt_kappa_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ : ℝ => Real.sqrt (κ * σ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hσ)

/-- Cochrane (2023), §20.2.3–20.2.4, pp. 477–479: `λ^b → ∞` as prices become flexible,
`κ → ∞`. -/
theorem lamb_tendsto_atTop (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => lamb ρ κ σ) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-(ρ / 2)) (sqrt_kappa_tendsto hσ))
  exact Eventually.of_forall fun κ => by
    have := sqrt_sub_le_lamb ρ κ σ
    linarith

/-- Cochrane (2023), §20.2.3, p. 477: `λ^f → ∞` as `κ → ∞`. -/
theorem lamf_tendsto_atTop (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => lamf ρ κ σ) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (ρ / 2) (sqrt_kappa_tendsto hσ))
  exact Eventually.of_forall fun κ => sqrt_add_le_lamf ρ κ σ

/-! ## Exponentials and improper integrals (restated from the Cochrane Chapter 5 project) -/

/-- Cochrane (2023), §5.7, p. 164 (restated from the Cochrane Chapter 5 project): the discount
factor `e^{−aτ}` has derivative `−a e^{−aτ}`. -/
theorem hasDerivAt_expNeg (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(a * u))) (-a * Real.exp (-(a * τ))) τ := by
  have h1 : HasDerivAt (fun u => -(a * u)) (-a) τ :=
    (HasDerivAt.neg ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), §5.7, p. 164 (restated from the Cochrane Chapter 5 project): the growth
factor `e^{aτ}` has derivative `a e^{aτ}`. -/
theorem hasDerivAt_expPos (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (a * u)) (a * Real.exp (a * τ)) τ :=
  (HasDerivAt.exp ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)

/-- Cochrane (2023), §20.2.2, p. 475: `e^{−at} → 0` as `t → ∞` for `a > 0`. -/
theorem tendsto_expNeg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => Real.exp (-(a * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)

/-- Cochrane (2023), §20.2.2, p. 475: `e^{at} → ∞` as `t → ∞` for `a > 0`. -/
theorem tendsto_expPos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => Real.exp (a * t)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)

/-- Cochrane (2023), §5.7, p. 163 (restated from the Cochrane Chapter 5 project): if `G' = g`
on `(t, ∞)`, `G` is continuous on `[t, ∞)` and `g` is integrable on `(t, ∞)`, then
`G(T) → G(t) + ∫_t^∞ g`. -/
theorem tendsto_of_deriv_Ioi {G g : ℝ → ℝ} {t : ℝ} (hc : ContinuousOn G (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt G (g τ) τ) (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto G atTop (𝓝 (G t + ∫ τ in Set.Ioi t, g τ)) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id).const_add (G t)
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hint : IntervalIntegrable g volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (hc.mono Set.Icc_subset_Ici_self) (fun x hx => hd x hx.1) hint
  simp only [id]
  rw [hftc]
  ring

/-- Cochrane (2023), §5.7, p. 163 (restated from the Cochrane Chapter 5 project): the shift
`∫_0^∞ g(t+τ) dτ = ∫_t^∞ g(τ) dτ`. -/
theorem integral_Ioi_shift (g : ℝ → ℝ) (t : ℝ) :
    ∫ τ in Set.Ioi 0, g (t + τ) = ∫ τ in Set.Ioi t, g τ := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : (Set.Ioi (0 : ℝ)).indicator (fun τ => g (t + τ)) =
      fun τ => (Set.Ioi t).indicator g (t + τ) := by
    funext τ
    by_cases hτ : 0 < τ
    · have : t < t + τ := by linarith
      simp [Set.indicator, hτ, this]
    · have : ¬ t < t + τ := by linarith
      simp [Set.indicator, hτ, this]
  rw [h, integral_add_left_eq_self (fun x => (Set.Ioi t).indicator g x) t]

/-- Cochrane (2023), §5.7, p. 165 (restated from the Cochrane Chapter 5 project):
`∫_0^∞ e^{−aτ} f(t+τ) dτ = e^{at} ∫_t^∞ e^{−aτ} f(τ) dτ`. -/
theorem integral_exp_shift (a t : ℝ) (f : ℝ → ℝ) :
    ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) =
      Real.exp (a * t) * ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ := by
  rw [← integral_const_mul,
    ← integral_Ioi_shift (fun τ => Real.exp (a * t) * (Real.exp (-(a * τ)) * f τ)) t]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): a path
bounded on `[t, ∞)` satisfies `e^{−aT}x_T → 0` for `a > 0`. -/
theorem tvc_of_bounded {x : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (hb : ∀ T, t ≤ T → |x T| ≤ K) :
    Tendsto (fun T => Real.exp (-(a * T)) * x T) atTop (𝓝 0) := by
  have hK := (tendsto_expNeg ha).mul_const K
  rw [zero_mul] at hK
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb T hT) (Real.exp_pos _).le

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): a
measurable path bounded on `(t, ∞)`, discounted at `a > 0`, is integrable on `(t, ∞)`. -/
theorem integrableOn_exp_mul_of_bdd {z : ℝ → ℝ} {a t M : ℝ} (ha : 0 < a)
    (hm : AEStronglyMeasurable z (volume.restrict (Set.Ioi t)))
    (hb : ∀ τ, t < τ → |z τ| ≤ M) :
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * z τ) (Set.Ioi t) := by
  have hint := (integrableOn_exp_mul_Ioi (a := -a) (by linarith) t).const_mul M
  have hc : Continuous fun τ : ℝ => Real.exp (-(a * τ)) := by fun_prop
  refine Integrable.mono' hint (hc.aestronglyMeasurable.mul hm)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : t < τ) => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project):
`|∫_0^∞ e^{−aτ} z(τ) dτ| ≤ M/a` when `|z| ≤ M` on `(0, ∞)`, `a > 0`. -/
theorem abs_integral_exp_le {z : ℝ → ℝ} {a M : ℝ} (ha : 0 < a)
    (hb : ∀ τ, 0 < τ → |z τ| ≤ M) :
    |∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z τ| ≤ M / a := by
  have hint := (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul M
  have hbound : ‖∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z τ‖ ≤
      ∫ τ in Set.Ioi 0, M * Real.exp (-a * τ) := by
    refine norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
  simp only [mul_zero, Real.exp_zero] at hbound
  have hval : M * (-1 / -a) = M / a := by field_simp
  rw [hval, Real.norm_eq_abs] at hbound
  exact hbound

/-- Cochrane (2023), §5.7.1, p. 166 (restated from the Cochrane Chapter 5 project):
`∫_0^∞ e^{−aτ} dτ = 1/a` for `a > 0`. -/
theorem integral_exp_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(a * τ)) = 1 / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]
  field_simp

/-- Cochrane (2023), §5.7.1, p. 166 (restated from the Cochrane Chapter 5 project): `e^{−aτ}` is
integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(a * τ))) (Set.Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  simpa only [neg_mul] using h

/-- Cochrane (2023), §5.7.1, p. 167 (restated from the Cochrane Chapter 5 project):
`∫_0^T e^{−bτ} dτ = (1 − e^{−bT})/b` for `b ≠ 0`. -/
theorem intervalIntegral_exp {b : ℝ} (hb : b ≠ 0) (T : ℝ) :
    ∫ τ in (0 : ℝ)..T, Real.exp (-(b * τ)) = (1 - Real.exp (-(b * T))) / b := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u => -Real.exp (-(b * u)) / b) (Real.exp (-(b * x))) x := by
    intro x _
    have := ((hasDerivAt_expNeg b x).neg).div_const b
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(b * τ))).intervalIntegrable 0 T)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-- Cochrane (2023), §5.7.1, p. 165, (5.95) (restated from the Cochrane Chapter 5 project):
**the forward value iff the transversality condition.** If `v' = a v − f` on `(t, ∞)`, `v` is
continuous on `[t, ∞)` and `e^{−aτ} f_τ` is integrable on `(t, ∞)`, then `e^{−aT} v_T → 0` iff
`v_t = ∫_0^∞ e^{−aτ} f_{t+τ} dτ`. -/
theorem tvc_iff_forward {v f : ℝ → ℝ} {a t : ℝ} (hc : ContinuousOn v (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) := by
  have hG : ∀ τ, t < τ → HasDerivAt (fun u => Real.exp (-(a * u)) * v u)
      (-(Real.exp (-(a * τ)) * f τ)) τ := fun τ hτ =>
    ((hasDerivAt_expNeg a τ).mul (hd τ hτ)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u => Real.exp (-(a * u)) * v u) (Set.Ici t) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousOn.mul hc
  have hlim := tendsto_of_deriv_Ioi hGc hG hint.neg
  rw [integral_neg] at hlim
  rw [integral_exp_shift]
  have hinv : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  constructor
  · intro h0
    have h := tendsto_nhds_unique hlim h0
    have : Real.exp (-(a * t)) * v t = ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ := by
      linarith
    rw [← this, ← mul_assoc, hinv, one_mul]
  · intro hv
    have : Real.exp (-(a * t)) * v t + -∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ = 0 := by
      rw [hv, ← mul_assoc, mul_comm (Real.exp (-(a * t))), hinv, one_mul]
      ring
    rwa [this] at hlim

/-! ## The forward and backward integrals (A1 §1.12) -/

/-- Cochrane (2023), (20.8), p. 474 (A1 §1.12, p. 580): the forward integral
`∫_t^∞ e^{−a(s−t)} z_s ds = ∫_0^∞ e^{−aτ} z_{t+τ} dτ`. -/
noncomputable def fwdInt (a : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z (t + τ)

/-- Cochrane (2023), A1 §1.12, p. 580 (restated from the Cochrane Chapter 5 project): for a
globally bounded continuous `z` and `a > 0`,
`F_a(z)(t) = e^{at}(∫_0^∞ e^{−as} z_s ds − ∫_0^t e^{−as} z_s ds)`. -/
theorem fwdInt_eq {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    fwdInt a z t = Real.exp (a * t) * ((∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s) -
      ∫ s in (0 : ℝ)..t, Real.exp (-(a * s)) * z s) := by
  have hI : ∀ c, IntegrableOn (fun s => Real.exp (-(a * s)) * z s) (Set.Ioi c) := fun c =>
    integrableOn_exp_mul_of_bdd ha hz.aestronglyMeasurable (fun τ _ => hM τ)
  rw [fwdInt, integral_exp_shift, ← intervalIntegral.integral_interval_add_Ioi (hI 0) (hI t)]
  ring

/-- Cochrane (2023), A1 §1.12, p. 580 (restated from the Cochrane Chapter 5 project): for a
globally bounded continuous `z` and `a > 0`, `F_a(z)' = a F_a(z) − z` at every date. -/
theorem fwdInt_hasDerivAt {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (fwdInt a z) (a * fwdInt a z t - z t) t := by
  have hfun : fwdInt a z = fun u => Real.exp (a * u) *
      ((∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s) -
        ∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * z s) := funext (fwdInt_eq ha hz hM)
  have hgc : Continuous fun s => Real.exp (-(a * s)) * z s := by fun_prop
  have hP := HasDerivAt.sub (hasDerivAt_const t (∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s))
    (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := (hasDerivAt_expPos a t).mul hP
  rw [hfun]
  convert h using 1
  rw [← hfun]
  have hinv : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [fwdInt_eq ha hz hM t]
  simp only [Pi.sub_apply]
  linear_combination (z t) * hinv

/-- Cochrane (2023), A1 §1.12, p. 580: `|F_a(z)(t)| ≤ M/a` when `|z| ≤ M` on `[t, ∞)`. -/
theorem fwdInt_abs_le {a M t : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hM : ∀ s, t ≤ s → |z s| ≤ M) :
    |fwdInt a z t| ≤ M / a :=
  abs_integral_exp_le ha fun τ hτ => hM (t + τ) (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the two-sided backward integral
`∫_{−∞}^t e^{−b(t−s)} z_s ds = ∫_0^∞ e^{−bτ} z_{t−τ} dτ`. -/
noncomputable def bwdInfInt (b : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(b * τ)) * z (t - τ)

/-- Cochrane (2023), (20.8), p. 474: the backward integral is the forward integral of the
time-reversed path, `B_b(z)(t) = F_b(z ∘ neg)(−t)`. -/
theorem bwdInfInt_eq_fwdInt (b : ℝ) (z : ℝ → ℝ) (t : ℝ) :
    bwdInfInt b z t = fwdInt b (fun u => z (-u)) (-t) := by
  unfold bwdInfInt fwdInt
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  simp only [neg_add, neg_neg, sub_eq_add_neg]

/-- Cochrane (2023), (20.8), p. 474: for a globally bounded continuous `z` and `b > 0`, the
backward integral solves `B' = −b B + z` at every date. -/
theorem bwdInfInt_hasDerivAt {b M : ℝ} {z : ℝ → ℝ} (hb : 0 < b) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (bwdInfInt b z) (-b * bwdInfInt b z t + z t) t := by
  have hz' : Continuous fun u => z (-u) := hz.comp continuous_neg
  have hF := fwdInt_hasDerivAt hb hz' (fun s => hM (-s)) (-t)
  have hc := HasDerivAt.scomp t hF (hasDerivAt_neg t)
  have hfun : bwdInfInt b z = (fwdInt b fun u => z (-u)) ∘ fun u => -u :=
    funext fun u => bwdInfInt_eq_fwdInt b z u
  rw [hfun]
  refine hc.congr_deriv ?_
  simp only [Function.comp, smul_eq_mul, neg_neg]
  ring

/-- Cochrane (2023), (20.8), p. 474: `|B_b(z)(t)| ≤ M/b` when `|z| ≤ M` on `(−∞, t]`. -/
theorem bwdInfInt_abs_le {b M t : ℝ} {z : ℝ → ℝ} (hb : 0 < b)
    (hM : ∀ s, s ≤ t → |z s| ≤ M) : |bwdInfInt b z t| ≤ M / b :=
  abs_integral_exp_le hb fun τ hτ => hM (t - τ) (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the backward integral is continuous (globally bounded
continuous `z`, `b > 0`). -/
theorem bwdInfInt_continuous {b M : ℝ} {z : ℝ → ℝ} (hb : 0 < b) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) : Continuous (bwdInfInt b z) :=
  continuous_iff_continuousAt.2 fun t => (bwdInfInt_hasDerivAt hb hz hM t).continuousAt

/-- Cochrane (2023), (20.8), p. 474: the forward integral is continuous (globally bounded
continuous `z`, `a > 0`). -/
theorem fwdInt_continuous {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) : Continuous (fwdInt a z) :=
  continuous_iff_continuousAt.2 fun t => (fwdInt_hasDerivAt ha hz hM t).continuousAt

/-! ## Variation of constants for piecewise-smooth paths -/

/-- Cochrane (2023), §20.2.2, p. 475 (solving piecewise): a function continuous on `[p, q]`
whose derivative vanishes on `(p, q)` off a countable set is constant: `G q = G p`. -/
theorem const_of_hasDerivAt_zero_off {G : ℝ → ℝ} {p q : ℝ} {S : Set ℝ} (hpq : p ≤ q)
    (hS : S.Countable) (hc : ContinuousOn G (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt G 0 t) : G q = G p := by
  have h := integral_eq_of_hasDerivAt_off_countable_of_le G (fun _ => (0 : ℝ)) hpq hS hc hd
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- Cochrane (2023), §20.2.2, p. 475 (A1 §1.12): **uniqueness for `f' = a f` on an interval**,
off a countable set: `f t = e^{a(t−p)} f p` on `[p, q]`. -/
theorem linear_ode_Icc {f : ℝ → ℝ} {a p q : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hc : ContinuousOn f (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt f (a * f t) t) :
    ∀ t ∈ Set.Icc p q, f t = Real.exp (a * (t - p)) * f p := by
  intro t ht
  have hG := const_of_hasDerivAt_zero_off (G := fun u => Real.exp (-(a * u)) * f u)
    (p := p) (q := t) ht.1 hS
    (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousOn).mul
      (hc.mono (Set.Icc_subset_Icc le_rfl ht.2)))
    (fun u hu => ((hasDerivAt_expNeg a u).mul (hd u ⟨⟨hu.1.1, lt_of_lt_of_le hu.1.2 ht.2⟩,
      hu.2⟩)).congr_deriv (by ring))
  have h1 : Real.exp (a * (t - p)) * Real.exp (-(a * t)) = Real.exp (-(a * p)) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc f t = Real.exp (a * t) * (Real.exp (-(a * t)) * f t) := by
        rw [← mul_assoc, h2, one_mul]
    _ = Real.exp (a * t) * (Real.exp (-(a * p)) * f p) := by rw [hG]
    _ = Real.exp (a * (t - p)) * f p := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- Cochrane (2023), §20.2.2, p. 475 (A1 §1.12): **the affine ODE `f' = a f + b` on an
interval** (off a countable set), `a ≠ 0`:
`f t + b/a = e^{a(t−p)}(f p + b/a)` on `[p, q]`. -/
theorem affine_ode_Icc {f : ℝ → ℝ} {a b p q : ℝ} {S : Set ℝ} (ha : a ≠ 0) (hS : S.Countable)
    (hc : ContinuousOn f (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt f (a * f t + b) t) :
    ∀ t ∈ Set.Icc p q, f t + b / a = Real.exp (a * (t - p)) * (f p + b / a) :=
  linear_ode_Icc (f := fun u => f u + b / a) hS (hc.add continuousOn_const)
    fun t ht => ((hd t ht).add_const (b / a)).congr_deriv (by field_simp)

/-- Cochrane (2023), §20.2.2, p. 475: uniqueness for `f' = a f` on a half-line `[p, ∞)`, off a
countable set: `f t = e^{a(t−p)} f p`. -/
theorem linear_ode_Ici {f : ℝ → ℝ} {a p : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hc : ContinuousOn f (Set.Ici p))
    (hd : ∀ t, p < t → t ∉ S → HasDerivAt f (a * f t) t) :
    ∀ t, p ≤ t → f t = Real.exp (a * (t - p)) * f p := fun t ht =>
  linear_ode_Icc (q := t) hS (hc.mono Set.Icc_subset_Ici_self)
    (fun u hu => hd u hu.1.1 hu.2) t ⟨ht, le_rfl⟩

/-- Cochrane (2023), §20.2.2, p. 475 ("forward-explosive solutions are ruled out"): if
`f' = a f` with `a > 0` on `(p, ∞)` off a countable set, `f` is continuous on `[p, ∞)` and
bounded there, then `f ≡ 0` on `[p, ∞)`. -/
theorem unstable_bdd_zero {f : ℝ → ℝ} {a p K : ℝ} {S : Set ℝ} (ha : 0 < a) (hS : S.Countable)
    (hc : ContinuousOn f (Set.Ici p))
    (hd : ∀ t, p < t → t ∉ S → HasDerivAt f (a * f t) t)
    (hb : ∀ t, p ≤ t → |f t| ≤ K) : ∀ t, p ≤ t → f t = 0 := by
  have hsol := linear_ode_Ici hS hc hd
  have hp : f p = 0 := by
    by_contra hne
    have hpos : 0 < |f p| := abs_pos.2 hne
    have ht : Tendsto (fun t => Real.exp (a * (t - p)) * |f p|) atTop atTop := by
      refine Tendsto.atTop_mul_const hpos ?_
      exact Real.tendsto_exp_atTop.comp
        ((tendsto_atTop_add_const_right atTop (-p) tendsto_id).const_mul_atTop ha |>.congr
          fun t => by simp [sub_eq_add_neg])
    obtain ⟨t, ht1, ht2⟩ := ((ht.eventually_gt_atTop K).and (eventually_ge_atTop p)).exists
    have := hb t ht2
    rw [hsol t ht2, abs_mul, abs_of_pos (Real.exp_pos _)] at this
    linarith
  intro t ht
  rw [hsol t ht, hp, mul_zero]

/-- Cochrane (2023), (20.8), p. 474: uniqueness for `f' = a f` on the whole line:
`f t = e^{at} f 0`. -/
theorem linear_ode_univ {f : ℝ → ℝ} {a : ℝ} (hd : ∀ t, HasDerivAt f (a * f t) t) (t : ℝ) :
    f t = Real.exp (a * t) * f 0 := by
  have hG : ∀ u, HasDerivAt (fun u => Real.exp (-(a * u)) * f u) 0 u := fun u =>
    ((hasDerivAt_expNeg a u).mul (hd u)).congr_deriv (by ring)
  have hc : ∀ u v, Real.exp (-(a * u)) * f u = Real.exp (-(a * v)) * f v := fun u v =>
    is_const_of_deriv_eq_zero (fun w => (hG w).differentiableAt)
      (fun w => (hG w).deriv) u v
  have h0 := hc t 0
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h0
  have h2 : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc f t = Real.exp (a * t) * (Real.exp (-(a * t)) * f t) := by
        rw [← mul_assoc, h2, one_mul]
    _ = Real.exp (a * t) * f 0 := by rw [h0]

/-! ## The forward-stable solution (20.8) -/

/-- Cochrane (2023), (20.8), p. 474: the forward-stable family
`π_t = C e^{−λ^b t} + (λ^f + λ^b)⁻¹[∫_{−∞}^t e^{−λ^b(t−s)} z_s ds + ∫_t^∞ e^{−λ^f(s−t)} z_s ds]`,
written for generic roots `lf, lb`. -/
noncomputable def greenPi (lf lb : ℝ) (z : ℝ → ℝ) (C t : ℝ) : ℝ :=
  C * Real.exp (-(lb * t)) + (bwdInfInt lb z t + fwdInt lf z t) / (lf + lb)

/-- Cochrane (2023), (20.8), p. 474: every member of the family satisfies
`π' = −λ^b π + ∫_t^∞ e^{−λ^f(s−t)} z_s ds` (globally bounded continuous `z`, `lf, lb > 0`). -/
theorem greenPi_hasDerivAt {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hz : Continuous z) (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (greenPi lf lb z C) (-lb * greenPi lf lb z C t + fwdInt lf z t) t := by
  have hd := ((hasDerivAt_expNeg lb t).const_mul C).add
    (((bwdInfInt_hasDerivAt hb hz hM t).add (fwdInt_hasDerivAt hf hz hM t)).div_const (lf + lb))
  refine hd.congr_deriv ?_
  simp only [greenPi]
  field_simp
  ring

/-- Cochrane (2023), (20.8), p. 474: `|π_t − C e^{−λ^b t}| ≤ (M/λ^b + M/λ^f)/(λ^f + λ^b)` —
the particular part of the family is bounded. -/
theorem greenPi_sub_abs_le {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    |greenPi lf lb z C t - C * Real.exp (-(lb * t))| ≤ (M / lb + M / lf) / (lf + lb) := by
  simp only [greenPi, add_sub_cancel_left]
  rw [abs_div, abs_of_pos (by linarith : 0 < lf + lb)]
  exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add
    (bwdInfInt_abs_le hb fun s _ => hM s) (fwdInt_abs_le hf fun s _ => hM s)))
    (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the family is injective in `C` (the constant is pinned by
`π_0`). -/
theorem greenPi_injective {lf lb C C' : ℝ} {z : ℝ → ℝ}
    (h : greenPi lf lb z C = greenPi lf lb z C') : C = C' := by
  have := congrFun h 0
  simp only [greenPi, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  linarith

/-- Cochrane (2023), (20.8), p. 474, the "forward-stable" criterion: along the family,
`e^{−λ^f t} π_t → 0`. -/
theorem greenPi_forward_stable {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hM : ∀ s, |z s| ≤ M) :
    Tendsto (fun t => Real.exp (-(lf * t)) * greenPi lf lb z C t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => C * Real.exp (-((lf + lb) * t))) atTop (𝓝 0) := by
    simpa using (tendsto_expNeg (by linarith : 0 < lf + lb)).const_mul C
  have h2 := tvc_of_bounded (x := fun t => greenPi lf lb z C t - C * Real.exp (-(lb * t)))
    (t := 0) hf fun T _ => greenPi_sub_abs_le hf hb hM T
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun t => ?_
  have he : Real.exp (-((lf + lb) * t)) = Real.exp (-(lf * t)) * Real.exp (-(lb * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  ring

/-- Cochrane (2023), (20.8), p. 474: **the forward-stable solutions are exactly the family
(20.8).** Let `z` be continuous and bounded, `lf, lb > 0`. Suppose `π' = −λ^b π + y` and
`y' = λ^f y − z` at every date (i.e. `(D − λ^f)(D + λ^b)π = −z` in first-order form). Then
`e^{−λ^f t}π_t → 0` iff `π = greenPi C` for some `C`; and then `y = ∫_t^∞ e^{−λ^f(s−t)}z_s ds`. -/
theorem forward_stable_iff {lf lb M : ℝ} {z π y : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hz : Continuous z) (hM : ∀ s, |z s| ≤ M)
    (hπ : ∀ t, HasDerivAt π (-lb * π t + y t) t) (hy : ∀ t, HasDerivAt y (lf * y t - z t) t) :
    Tendsto (fun t => Real.exp (-(lf * t)) * π t) atTop (𝓝 0) ↔
      ∃ C, π = greenPi lf lb z C ∧ y = fwdInt lf z := by
  set F := fwdInt lf z with hF
  -- `w = y − F` solves `w' = λ^f w`
  have hw := linear_ode_univ (f := fun t => y t - F t) (a := lf) fun t =>
    ((hy t).sub (fwdInt_hasDerivAt hf hz hM t)).congr_deriv (by ring)
  set w0 := y 0 - F 0
  -- `D = π − greenPi 0 − w0 e^{λ^f t}/(lf+lb)` solves `D' = −λ^b D`
  have hD := linear_ode_univ (a := -lb)
    (f := fun t => π t - greenPi lf lb z 0 t - w0 * Real.exp (lf * t) / (lf + lb)) fun t => by
      have := ((hπ t).sub (greenPi_hasDerivAt (C := 0) hf hb hz hM t)).sub
        (((hasDerivAt_expPos lf t).const_mul w0).div_const (lf + lb))
      refine this.congr_deriv ?_
      have hwt := hw t
      field_simp
      linear_combination (lf + lb) * hwt
  set D0 := π 0 - greenPi lf lb z 0 0 - w0 * Real.exp (lf * 0) / (lf + lb)
  have hrep : ∀ t, π t = greenPi lf lb z D0 t + w0 * Real.exp (lf * t) / (lf + lb) := by
    intro t
    have h := hD t
    simp only [greenPi] at h ⊢
    have he : Real.exp (-lb * t) = Real.exp (-(lb * t)) := by ring_nf
    rw [he] at h
    linarith
  constructor
  · intro hlim
    have hstab := greenPi_forward_stable (C := D0) hf hb hM
    have hdiff : Tendsto (fun _ : ℝ => w0 / (lf + lb)) atTop (𝓝 0) := by
      have hs := hlim.sub hstab
      rw [sub_zero] at hs
      refine hs.congr fun t => ?_
      rw [hrep t]
      have : Real.exp (-(lf * t)) * Real.exp (lf * t) = 1 := by
        rw [← Real.exp_add]; simp
      field_simp
      linear_combination w0 * this
    have hw0 : w0 / (lf + lb) = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
    have hw00 : w0 = 0 := by
      rcases div_eq_zero_iff.1 hw0 with h | h
      · exact h
      · linarith
    refine ⟨D0, funext fun t => ?_, funext fun t => ?_⟩
    · rw [hrep t, hw00]; ring
    · have := hw t
      rw [hw00, mul_zero] at this
      linarith
  · rintro ⟨C, hC, -⟩
    rw [hC]
    exact greenPi_forward_stable hf hb hM

end Cochrane.ZeroBound.ContinuousTimeNK

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Werning (2012) zero-bound model in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476,
equations (20.5)–(20.10).

The IS curve and Phillips curve (20.5)–(20.6) are `dx/dt = σ(i − π − u_r)`,
`dπ/dt = ρπ − κ(x + g)`. The experiment: after unexpected news at `t = 0`, the natural rate is
`u_r = u` (the book: `−2%`) on `[0, T)` and `0` afterwards; the nominal rate is `i = 0` on
`[0, T)` and `i = u_r = 0` afterwards; the Phillips-curve disturbance is `g` on `[0, T)` and `0`
afterwards (`g = 0` in §20.2.2, used in §20.2.5). Paths are deterministic `ℝ → ℝ`, continuous
on `[0, ∞)`, satisfying the ODEs by `HasDerivAt` off a countable set (here `{T}`, where the
forcing jumps). Survey error E6: with piecewise-constant `g`, `dg/dt` in (20.9) is a measure
(Dirac masses at `0` and `T`); we solve piecewise, with `x` and `π` continuous at `T` (the jump
conditions), and separately prove (20.8) for continuous forcing on the whole line and its
Stieltjes reading for the experiment.

## Main results

* `IsPath` (20.5)–(20.6); linearity (`IsPath.add`, `IsPath.sub`); `homog_bdd`: bounded
  solutions of the unforced system are `π_t = e^{−λ^b t}π_0`, `κx = λ^f π` (the forward-explosive
  root `C_f e^{λ^f t}` is ruled out, p. 475).
* The closed-form family `wPi`, `wX` indexed by `π_T`; `wPath_isPath`, `wPath_bdd`;
  **`bdd_path_iff`**: the bounded paths of the experiment are exactly this one-parameter family;
  `bdd_path_existsUnique` (the constant is `π_T`); `wPi_shift` (members differ by
  `(π_T − π_T')e^{λ^b(T−t)}`).
* Jump conditions at `T`: `jump_pi`, `jump_x` (`π̇(T⁺) − π̇(T⁻) = κ g`, `ẋ(T⁺) − ẋ(T⁻) = σ u`).
* (20.8)–(20.10) for continuous forcing on the whole line: `eq20_8_solves`, `eq20_8_iff` (both
  directions; `z = κσ(i − u_r) + κ dg/dt`, (20.9)), `family_equiv` (`ℝ ≃` the forward-stable
  solutions, via `C`).
* The Stieltjes reading of (20.8)/(20.10) for the experiment (E6): `experiment_eq20_8`.
* (20.7): `eq20_7_selects` — after `T`, an active rule `i = i* + φ(π − π*)`, `φ > 1`, selects the
  chosen path as the unique bounded one.
-/

namespace Cochrane.ZeroBound.WerningModel

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK

/-! ## The model (20.5)–(20.6) -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474: `(x, π)` is a path of the continuous-time model
with interest rate `i`, natural rate `u` and Phillips-curve disturbance `g`: both continuous on
`[0, ∞)`, and for `t > 0` off the countable set `S` (the dates where the forcing jumps)
`dx/dt = σ(i − π − u)` and `dπ/dt = ρπ − κ(x + g)`. -/
def IsPath (σ ρ κ : ℝ) (i u g : ℝ → ℝ) (S : Set ℝ) (x π : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ContinuousOn π (Set.Ici 0) ∧
    ∀ t, 0 < t → t ∉ S → HasDerivAt x (σ * (i t - π t - u t)) t ∧
      HasDerivAt π (ρ * π t - κ * (x t + g t)) t

/-- Cochrane (2023), §20.2.2, p. 474 ("do not explode as time increases"): bounded on
`[0, ∞)`. -/
def BddOnIci (f : ℝ → ℝ) : Prop := ∃ K, ∀ t, 0 ≤ t → |f t| ≤ K

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the model is linear — sums of paths are paths for
the summed forcing. -/
theorem IsPath.add {σ ρ κ : ℝ} {i u g i' u' g' x π x' π' : ℝ → ℝ} {S S' : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (h' : IsPath σ ρ κ i' u' g' S' x' π') :
    IsPath σ ρ κ (fun t => i t + i' t) (fun t => u t + u' t) (fun t => g t + g' t) (S ∪ S')
      (fun t => x t + x' t) (fun t => π t + π' t) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ S := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ S' := fun hh => hS (Or.inr hh)
  obtain ⟨a1, b1⟩ := h.2.2 t ht hS1
  obtain ⟨a2, b2⟩ := h'.2.2 t ht hS2
  exact ⟨(a1.add a2).congr_deriv (by ring), (b1.add b2).congr_deriv (by ring)⟩

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the difference of two paths with the same forcing
solves the unforced model. -/
theorem IsPath.sub {σ ρ κ : ℝ} {i u g x π x' π' : ℝ → ℝ} {S S' : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (h' : IsPath σ ρ κ i u g S' x' π') :
    IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) (S ∪ S')
      (fun t => x t - x' t) (fun t => π t - π' t) := by
  refine ⟨h.1.sub h'.1, h.2.1.sub h'.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ S := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ S' := fun hh => hS (Or.inr hh)
  obtain ⟨a1, b1⟩ := h.2.2 t ht hS1
  obtain ⟨a2, b2⟩ := h'.2.2 t ht hS2
  exact ⟨(a1.sub a2).congr_deriv (by ring), (b1.sub b2).congr_deriv (by ring)⟩

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the model only involves the paths on `[0, ∞)`. -/
theorem IsPath.congr {σ ρ κ : ℝ} {i u g x π x' π' : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (hx : ∀ t, 0 ≤ t → x' t = x t)
    (hπ : ∀ t, 0 ≤ t → π' t = π t) : IsPath σ ρ κ i u g S x' π' := by
  refine ⟨h.1.congr fun t ht => hx t ht, h.2.1.congr fun t ht => hπ t ht, fun t ht hS => ?_⟩
  have evx : x =ᶠ[𝓝 t] x' := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hx s hs.le).symm
  have evπ : π =ᶠ[𝓝 t] π' := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hπ s hs.le).symm
  obtain ⟨a, b⟩ := h.2.2 t ht hS
  rw [hx t ht.le, hπ t ht.le]
  exact ⟨a.congr_of_eventuallyEq evx.symm, b.congr_of_eventuallyEq evπ.symm⟩

/-- Cochrane (2023), §20.2.2, p. 475 ("we set to zero … forward-explosive equilibria
`C_f e^{λ^f t}`"): **bounded solutions of the unforced model.** If `(x, π)` solves the model with
`i = u = g = 0` (off a countable set) and both are bounded on `[0, ∞)`, then
`π_t = e^{−λ^b t} π_0` and `κ x_t = λ^f π_t` for all `t ≥ 0`. -/
theorem homog_bdd {σ ρ κ : ℝ} {x π : ℝ → ℝ} {S : Set ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hS : S.Countable)
    (h : IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) S x π) (hx : BddOnIci x)
    (hπ : BddOnIci π) :
    ∀ t, 0 ≤ t → π t = Real.exp (-(lamb ρ κ σ * t)) * π 0 ∧ κ * x t = lamf ρ κ σ * π t := by
  obtain ⟨hxc, hπc, hd⟩ := h
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  -- `y = λ^f π − κ x` satisfies `y' = λ^f y`
  have hy := unstable_bdd_zero (f := fun t => lf * π t - κ * x t) (a := lf) (p := 0)
    (K := lf * Kπ + κ * Kx) hf hS ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc))
    (fun t ht hts => by
      obtain ⟨a, b⟩ := hd t ht hts
      refine ((b.const_mul lf).sub (a.const_mul κ)).congr_deriv ?_
      linear_combination (-(π t)) * hroot)
    (fun t ht => by
      calc |lf * π t - κ * x t| ≤ |lf * π t| + |κ * x t| := abs_sub _ _
        _ = lf * |π t| + κ * |x t| := by rw [abs_mul, abs_mul, abs_of_pos hf, abs_of_pos hκ]
        _ ≤ lf * Kπ + κ * Kx := add_le_add (mul_le_mul_of_nonneg_left (hKπ t ht) hf.le)
            (mul_le_mul_of_nonneg_left (hKx t ht) hκ.le))
  have hπsol := linear_ode_Ici (f := π) (a := -lb) (p := 0) hS hπc fun t ht hts => by
    obtain ⟨-, b⟩ := hd t ht hts
    refine b.congr_deriv ?_
    have := hy t ht.le
    linear_combination this - (π t) * hsub
  intro t ht
  refine ⟨?_, ?_⟩
  · rw [hπsol t ht]; ring_nf
  · have := hy t ht
    linarith

/-! ## The experiment: closed-form solutions -/

/-- Cochrane (2023), §20.2.2, p. 474: a step path, `c` on `[0, T)` and `0` from `T` on (the
natural rate `u_r`, and the disturbance `g` of §20.2.5). -/
noncomputable def trapStep (c T t : ℝ) : ℝ := if t < T then c else 0

/-- Cochrane (2023), §20.2.2, p. 475: the function
`h(s) = (λ^f e^{λ^b s} + λ^b e^{−λ^f s})/(λ^f + λ^b)` (`s = T − t` is time to the end of the
trap), written for generic roots. -/
noncomputable def hh (lf lb s : ℝ) : ℝ :=
  (lf * Real.exp (lb * s) + lb * Real.exp (-(lf * s))) / (lf + lb)

/-- Cochrane (2023), §20.2.5, p. 481: the function
`k(s) = (e^{λ^b s} − e^{−λ^f s})/(λ^f + λ^b)`, the response to `g` during the trap. -/
noncomputable def kk (lf lb s : ℝ) : ℝ :=
  (Real.exp (lb * s) - Real.exp (-(lf * s))) / (lf + lb)

/-- Cochrane (2023), §20.2.2, p. 475: inflation during the trap, `s = T − t` before its end,
with forcing `A = i − u_r = −u`, disturbance `g`, and end-of-trap inflation `π_T`:
`π = π_T e^{λ^b s} + A(1 − h(s)) + κ g k(s)`. -/
noncomputable def trapPi (lf lb κ A g πT s : ℝ) : ℝ :=
  πT * Real.exp (lb * s) + A * (1 - hh lf lb s) + κ * g * kk lf lb s

/-- Cochrane (2023), §20.2.2, p. 475: during the trap, `y = λ^f π − κ(x + g)` (the forward
integral of the forcing) equals `λ^b A (1 − e^{−λ^f s}) − κ g e^{−λ^f s}`. -/
noncomputable def trapY (lf lb κ A g s : ℝ) : ℝ :=
  lb * A * (1 - Real.exp (-(lf * s))) - κ * g * Real.exp (-(lf * s))

/-- Cochrane (2023), §20.2.2, pp. 475–476 (Figure 20.4): the inflation path of the
equilibrium indexed by `π_T`: the trap formula on `[0, T]`, `π_T e^{−λ^b(t−T)}` after. -/
noncomputable def wPi (σ κ ρ T u g πT t : ℝ) : ℝ :=
  if t ≤ T then trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t)
  else πT * Real.exp (-(lamb ρ κ σ * (t - T)))

/-- Cochrane (2023), (20.6) and (20.10), p. 475: the output-gap path of the equilibrium indexed
by `π_T`: `x = (λ^f π − y)/κ − g` on `[0, T]` and `x = λ^f π/κ` after. -/
noncomputable def wX (σ κ ρ T u g πT t : ℝ) : ℝ :=
  if t ≤ T then
    (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) -
      trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)) / κ - g
  else lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (t - T)))) / κ

/-- Cochrane (2023), §20.2.2, p. 475: `h(0) = 1`. -/
theorem hh_zero {lf lb : ℝ} (h : lf + lb ≠ 0) : hh lf lb 0 = 1 := by
  simp only [hh, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact div_self h

/-- Cochrane (2023), §20.2.5, p. 481: `k(0) = 0`. -/
theorem kk_zero (lf lb : ℝ) : kk lf lb 0 = 0 := by
  simp [kk]

/-- Cochrane (2023), §20.2.2, p. 475: `h'(s) = λ^f λ^b k(s)`. -/
theorem hh_hasDerivAt {lf lb : ℝ} (h : lf + lb ≠ 0) (s : ℝ) :
    HasDerivAt (hh lf lb) (lf * lb * kk lf lb s) s := by
  have := (((hasDerivAt_expPos lb s).const_mul lf).add
    ((hasDerivAt_expNeg lf s).const_mul lb)).div_const (lf + lb)
  refine this.congr_deriv ?_
  simp only [kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481: `k'(s) = (λ^b e^{λ^b s} + λ^f e^{−λ^f s})/(λ^f + λ^b)`. -/
theorem kk_hasDerivAt (lf lb s : ℝ) :
    HasDerivAt (kk lf lb)
      ((lb * Real.exp (lb * s) + lf * Real.exp (-(lf * s))) / (lf + lb)) s := by
  have := ((hasDerivAt_expPos lb s).sub (hasDerivAt_expNeg lf s)).div_const (lf + lb)
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475: in time-to-go `s`, the trap formula satisfies
`dπ/ds = λ^b π − y`. -/
theorem trapPi_hasDerivAt {lf lb κ A g πT : ℝ} (h : lf + lb ≠ 0) (s : ℝ) :
    HasDerivAt (trapPi lf lb κ A g πT)
      (lb * trapPi lf lb κ A g πT s - trapY lf lb κ A g s) s := by
  have := ((((hasDerivAt_expPos lb s).const_mul πT).add
    (((hasDerivAt_const s (1 : ℝ)).sub (hh_hasDerivAt h s)).const_mul A)).add
    ((kk_hasDerivAt lf lb s).const_mul (κ * g)))
  refine this.congr_deriv ?_
  simp only [trapPi, trapY, hh, kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `dy/ds = λ^f (λ^b A + κ g) e^{−λ^f s}`. -/
theorem trapY_hasDerivAt (lf lb κ A g s : ℝ) :
    HasDerivAt (trapY lf lb κ A g)
      (lf * (lb * A + κ * g) * Real.exp (-(lf * s))) s := by
  have := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_expNeg lf s)).const_mul (lb * A)).sub
    ((hasDerivAt_expNeg lf s).const_mul (κ * g))
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475: at the end of the trap the formula gives `π_T`. -/
theorem trapPi_zero {lf lb : ℝ} (h : lf + lb ≠ 0) (κ A g πT : ℝ) :
    trapPi lf lb κ A g πT 0 = πT := by
  simp [trapPi, hh_zero h, kk_zero]

/-- Cochrane (2023), §20.2.2, p. 475: at the end of the trap `y = −κ g`. -/
theorem trapY_zero (lf lb κ A g : ℝ) : trapY lf lb κ A g 0 = -(κ * g) := by
  simp [trapY]

/-- Cochrane (2023), §20.2.2, p. 475: the trap formula is affine in `π_T`. -/
theorem trapPi_shift (lf lb κ A g πT s : ℝ) :
    trapPi lf lb κ A g πT s = trapPi lf lb κ A g 0 s + πT * Real.exp (lb * s) := by
  simp only [trapPi]
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `π_T` is the value of the path at `T`. -/
theorem wPi_T {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    wPi σ κ ρ T u g πT T = πT := by
  simp [wPi, trapPi_zero (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne']

/-- Cochrane (2023), §20.2.2, p. 475 (Figure 20.4): two members of the family differ by
`(π_T − π_T') e^{λ^b(T − t)}` at every date — here, `π(π_T) = π(0) + π_T e^{λ^b(T−t)}`. -/
theorem wPi_shift (σ κ ρ T u g πT t : ℝ) :
    wPi σ κ ρ T u g πT t = wPi σ κ ρ T u g 0 t + πT * Real.exp (lamb ρ κ σ * (T - t)) := by
  unfold wPi
  split_ifs
  · rw [trapPi_shift]
  · have : -(lamb ρ κ σ * (t - T)) = lamb ρ κ σ * (T - t) := by ring
    rw [this]
    ring

/-- Cochrane (2023), (20.10), p. 475: the output gaps of two members differ by
`λ^f(π_T − π_T') e^{λ^b(T−t)}/κ`. -/
theorem wX_shift (σ κ ρ T u g πT t : ℝ) :
    wX σ κ ρ T u g πT t =
      wX σ κ ρ T u g 0 t + lamf ρ κ σ * (πT * Real.exp (lamb ρ κ σ * (T - t))) / κ := by
  unfold wX
  split_ifs
  · rw [trapPi_shift]
    ring
  · have : -(lamb ρ κ σ * (t - T)) = lamb ρ κ σ * (T - t) := by ring
    rw [this]
    ring

/-- Cochrane (2023), §20.2.2, p. 475: the inflation path is continuous. -/
theorem wPi_continuous (σ κ ρ T u g πT : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    Continuous (wPi σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have h1 : Continuous fun t => trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) := by
    unfold trapPi hh kk
    fun_prop (disch := exact hne)
  have h2 : Continuous fun t => πT * Real.exp (-(lamb ρ κ σ * (t - T))) := by fun_prop
  exact Continuous.if_le (f := fun t => t) (g := fun _ => T) h1 h2 continuous_id
    continuous_const fun t (ht : t = T) => by
      subst ht
      rw [sub_self, trapPi_zero hne]
      simp

/-- Cochrane (2023), (20.10), p. 475: the output-gap path is continuous (`x` does not jump at
`T`). -/
theorem wX_continuous (σ κ ρ T u g πT : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    Continuous (wX σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have h1 : Continuous fun t => (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT
      (T - t) - trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)) / κ - g := by
    unfold trapPi trapY hh kk
    fun_prop (disch := exact hne)
  have h2 : Continuous fun t =>
      lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (t - T)))) / κ := by fun_prop
  exact Continuous.if_le (f := fun t => t) (g := fun _ => T) h1 h2 continuous_id
    continuous_const fun t (ht : t = T) => by
      subst ht
      rw [sub_self, trapPi_zero hne, trapY_zero]
      field_simp
      simp

/-- Cochrane (2023), (20.5)–(20.6), p. 474: **every member of the family is a path of the
experiment** (`i = 0`, `u_r = u` then `0`, `g` then `0`; the ODEs hold off `{T}`). -/
theorem wPath_isPath {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T}
      (wX σ κ ρ T u g πT) (wPi σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  refine ⟨(wX_continuous σ κ ρ T u g πT hκ hσ).continuousOn,
    (wPi_continuous σ κ ρ T u g πT hκ hσ).continuousOn, fun t _ hT => ?_⟩
  have hT' : t ≠ T := hT
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  rcases lt_or_gt_of_ne hT' with hlt | hgt
  · -- during the trap
    have evπ : wPi σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => trapPi lf lb κ (-u) g πT (T - s) := by
      filter_upwards [Iio_mem_nhds hlt] with s (hs : s < T)
      simp [wPi, le_of_lt hs, lf, lb]
    have evx : wX σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => (lf * trapPi lf lb κ (-u) g πT (T - s) -
          trapY lf lb κ (-u) g (T - s)) / κ - g := by
      filter_upwards [Iio_mem_nhds hlt] with s (hs : s < T)
      simp [wX, le_of_lt hs, lf, lb]
    have hP := (trapPi_hasDerivAt (κ := κ) (A := -u) (g := g) (πT := πT) hne (T - t)).comp t
      ((hasDerivAt_id t).const_sub T)
    have hY := (trapY_hasDerivAt lf lb κ (-u) g (T - t)).comp t ((hasDerivAt_id t).const_sub T)
    have hπv : wPi σ κ ρ T u g πT t = trapPi lf lb κ (-u) g πT (T - t) := evπ.eq_of_nhds
    have hxv : wX σ κ ρ T u g πT t = (lf * trapPi lf lb κ (-u) g πT (T - t) -
        trapY lf lb κ (-u) g (T - t)) / κ - g := evx.eq_of_nhds
    have hst : trapStep u T t = u := by simp [trapStep, hlt]
    have hgt' : trapStep g T t = g := by simp [trapStep, hlt]
    rw [hst, hgt', hπv, hxv]
    refine ⟨?_, ?_⟩
    · refine (((hP.const_mul lf).sub hY).div_const κ |>.sub_const g).congr_of_eventuallyEq
        evx |>.congr_deriv ?_
      simp only [trapY]
      field_simp
      linear_combination (-u - trapPi lf lb κ (-u) g πT (T - t)) * hmul
    · refine (hP.congr_of_eventuallyEq evπ).congr_deriv ?_
      field_simp
      linear_combination (trapPi lf lb κ (-u) g πT (T - t)) * hsub
  · -- after the trap
    have evπ : wPi σ κ ρ T u g πT =ᶠ[𝓝 t] fun s => πT * Real.exp (-(lb * (s - T))) := by
      filter_upwards [Ioi_mem_nhds hgt] with s (hs : T < s)
      simp [wPi, not_le.2 hs, lb]
    have evx : wX σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => lf * (πT * Real.exp (-(lb * (s - T)))) / κ := by
      filter_upwards [Ioi_mem_nhds hgt] with s (hs : T < s)
      simp [wX, not_le.2 hs, lf, lb]
    have hE : HasDerivAt (fun s => πT * Real.exp (-(lb * (s - T))))
        (πT * (-lb * Real.exp (-(lb * (t - T))))) t := by
      have := ((hasDerivAt_expNeg lb (t - T)).comp t ((hasDerivAt_id t).sub_const T)).const_mul πT
      simpa [Function.comp] using this
    have hst : trapStep u T t = 0 := by simp [trapStep, not_lt.2 hgt.le]
    have hgt' : trapStep g T t = 0 := by simp [trapStep, not_lt.2 hgt.le]
    rw [hst, hgt', evπ.eq_of_nhds, evx.eq_of_nhds]
    refine ⟨?_, ?_⟩
    · refine ((hE.const_mul lf).div_const κ).congr_of_eventuallyEq evx |>.congr_deriv ?_
      field_simp
      linear_combination (-(πT * Real.exp (-(lb * (t - T))))) * hmul
    · refine (hE.congr_of_eventuallyEq evπ).congr_deriv ?_
      field_simp
      linear_combination (πT * Real.exp (-(lb * (t - T)))) * hsub

/-- Cochrane (2023), §20.2.2, p. 474: a continuous path that is `c e^{−λ^b(t−T)}` after `T` is
bounded on `[0, ∞)`. -/
theorem bdd_of_cont_exp {f : ℝ → ℝ} {T c b : ℝ} (hf : Continuous f) (hb : 0 ≤ b)
    (hafter : ∀ t, T < t → f t = c * Real.exp (-(b * (t - T)))) : BddOnIci f := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C |c|, fun t ht => ?_⟩
  rcases le_or_gt t T with h | h
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · rw [hafter t h, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine le_trans ?_ (le_max_right _ _)
    refine mul_le_of_le_one_right (abs_nonneg c) ?_
    rw [Real.exp_le_one_iff]
    nlinarith

/-- Cochrane (2023), §20.2.2, p. 474: **every member of the family is bounded** ("does not
explode as time increases"). -/
theorem wPath_bdd {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    BddOnIci (wX σ κ ρ T u g πT) ∧ BddOnIci (wPi σ κ ρ T u g πT) := by
  have hb := (lamb_pos (ρ := ρ) hκ hσ).le
  refine ⟨bdd_of_cont_exp (c := lamf ρ κ σ * πT / κ) (T := T)
      (wX_continuous σ κ ρ T u g πT hκ hσ) hb fun t ht => ?_,
    bdd_of_cont_exp (c := πT) (T := T) (wPi_continuous σ κ ρ T u g πT hκ hσ) hb fun t ht => ?_⟩
  · simp only [wX, not_le.2 ht, ↓reduceIte]
    ring
  · simp [wPi, not_le.2 ht]

/-- Cochrane (2023), §20.2.2, pp. 474–475: **the bounded paths of the experiment are exactly
the one-parameter family indexed by `π_T`** (Figure 20.4). For `σ, κ > 0`, `(x, π)` is a path
(20.5)–(20.6) with `i = 0`, `u_r = u` on `[0,T)` and `0` after, `g` on `[0,T)` and `0` after,
bounded on `[0, ∞)`, iff for some `π_T` it equals `(wX π_T, wPi π_T)` on `[0, ∞)`. -/
theorem bdd_path_iff {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) {x π : ℝ → ℝ} :
    (IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
        BddOnIci π) ↔
      ∃ πT, ∀ t, 0 ≤ t → π t = wPi σ κ ρ T u g πT t ∧ x t = wX σ κ ρ T u g πT t := by
  constructor
  · rintro ⟨hp, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
    obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g 0
    have hd := hp.sub (wPath_isPath (ρ := ρ) hκ hσ T u g 0)
    have hh := homog_bdd hσ hκ ((Set.countable_singleton T).union (Set.countable_singleton T))
      hd ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
      ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
    set D := π 0 - wPi σ κ ρ T u g 0 0
    refine ⟨Real.exp (-(lamb ρ κ σ * T)) * D, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hh t ht
    have he : Real.exp (-(lamb ρ κ σ * T)) * D * Real.exp (lamb ρ κ σ * (T - t)) =
        Real.exp (-(lamb ρ κ σ * t)) * D := by
      rw [mul_comm _ D, mul_assoc, ← Real.exp_add]; ring_nf
    rw [wPi_shift, wX_shift, he]
    refine ⟨by linarith, ?_⟩
    rw [← h1]
    field_simp
    linarith
  · rintro ⟨πT, h⟩
    obtain ⟨hx, hπ⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g πT
    refine ⟨(wPath_isPath (ρ := ρ) hκ hσ T u g πT).congr (fun t ht => (h t ht).2)
      (fun t ht => (h t ht).1), ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hx
      exact ⟨K, fun t ht => by rw [(h t ht).2]; exact hK t ht⟩
    · obtain ⟨K, hK⟩ := hπ
      exact ⟨K, fun t ht => by rw [(h t ht).1]; exact hK t ht⟩

/-- Cochrane (2023), §20.2.2, p. 475: **the free constant is unique**: a bounded path of the
experiment equals exactly one member of the family (its constant is `π_T`). -/
theorem bdd_path_existsUnique {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T)
    {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    ∃! πT, ∀ t, 0 ≤ t → π t = wPi σ κ ρ T u g πT t ∧ x t = wX σ κ ρ T u g πT t := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  refine ⟨πT, hπT, fun πT' h' => ?_⟩
  have a := (h' T hT).1
  have b := (hπT T hT).1
  rw [wPi_T hκ hσ] at a b
  rw [← a, b]

/-! ### Jump conditions at `T` -/

/-- Cochrane (2023), §20.2.2, p. 475: the trap branch of the inflation path has derivative
`−(λ^b π − y)` in calendar time. -/
theorem trapBranch_hasDerivAt {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT t : ℝ) :
    HasDerivAt (fun s => trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - s))
      (-(lamb ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) -
        trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t))) t := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hP := (trapPi_hasDerivAt (κ := κ) (A := -u) (g := g) (πT := πT) hne (T - t)).comp t
    ((hasDerivAt_id t).const_sub T)
  exact hP.congr_deriv (by ring)

/-- Cochrane (2023), §20.2.2, p. 475: the trap branch of the output-gap path has derivative
`σ(A − π)` in calendar time. -/
theorem trapBranchX_hasDerivAt {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT t : ℝ) :
    HasDerivAt (fun s => (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - s) -
        trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - s)) / κ - g)
      (σ * (-u - trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t))) t := by
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hP := trapBranch_hasDerivAt (ρ := ρ) hκ hσ T u g πT t
  have hY := (trapY_hasDerivAt (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)).comp t
    ((hasDerivAt_id t).const_sub T)
  refine (((hP.const_mul (lamf ρ κ σ)).sub hY).div_const κ |>.sub_const g).congr_deriv ?_
  simp only [trapY]
  field_simp
  linear_combination (-u - trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t)) * hmul

/-- Cochrane (2023), §20.2.2, p. 475: the post-trap branch `π_T e^{−λ^b(t−T)}` has derivative
`−λ^b` times itself. -/
theorem postBranch_hasDerivAt (b T c t : ℝ) :
    HasDerivAt (fun s => c * Real.exp (-(b * (s - T))))
      (-b * (c * Real.exp (-(b * (t - T))))) t := by
  have := ((hasDerivAt_expNeg b (t - T)).comp t ((hasDerivAt_id t).sub_const T)).const_mul c
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (survey E6: the jump conditions): along any bounded path of
the experiment, `π` is continuous at `T` and its one-sided derivatives there are
`π̇(T⁻) = ρπ_T − κ(x_T + g)` and `π̇(T⁺) = ρπ_T − κ x_T`, so `π̇(T⁺) − π̇(T⁻) = κ g`
(`= κ(g(T⁻) − g(T⁺))`). -/
theorem jump_pi {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    HasDerivWithinAt π (ρ * π T - κ * (x T + g)) (Set.Icc 0 T) T ∧
      HasDerivWithinAt π (ρ * π T - κ * (x T + 0)) (Set.Ici T) T := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hsub := lamf_sub_lamb ρ κ σ
  have hxT : x T = lamf ρ κ σ * πT / κ := by
    rw [(hπT T hT).2]
    simp [wX, trapPi_zero hne, trapY_zero]
    field_simp
    ring
  have hπTv : π T = πT := by rw [(hπT T hT).1, wPi_T hκ hσ]
  refine ⟨?_, ?_⟩
  · have hd := (trapBranch_hasDerivAt (ρ := ρ) hκ hσ T u g πT T).hasDerivWithinAt
      (s := Set.Icc 0 T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t ht.1).1]
      simp [wPi, ht.2]
    · rw [(hπT T hT).1]
      simp [wPi]
    · rw [sub_self, trapPi_zero hne, trapY_zero, hπTv, hxT]
      field_simp
      linear_combination πT * hsub
  · have hd := (postBranch_hasDerivAt (lamb ρ κ σ) T πT T).hasDerivWithinAt (s := Set.Ici T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t (le_trans hT ht)).1]
      rcases eq_or_lt_of_le (Set.mem_Ici.1 ht) with h | h
      · subst h
        simp [wPi, trapPi_zero hne]
      · simp [wPi, not_le.2 h]
    · rw [(hπT T hT).1]
      simp [wPi, trapPi_zero hne]
    · rw [hπTv, hxT]
      simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      field_simp
      linear_combination πT * hsub

/-- Cochrane (2023), §20.2.2, p. 475 (the jump conditions): along any bounded path, `x` is
continuous at `T`, `ẋ(T⁻) = σ(0 − π_T − u)` and `ẋ(T⁺) = σ(0 − π_T − 0)`, so
`ẋ(T⁺) − ẋ(T⁻) = σ u` (the natural rate jumps from `u` to `0`). -/
theorem jump_x {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    HasDerivWithinAt x (σ * (0 - π T - u)) (Set.Icc 0 T) T ∧
      HasDerivWithinAt x (σ * (0 - π T - 0)) (Set.Ici T) T := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hπTv : π T = πT := by rw [(hπT T hT).1, wPi_T hκ hσ]
  refine ⟨?_, ?_⟩
  · have hd := (trapBranchX_hasDerivAt (ρ := ρ) hκ hσ T u g πT T).hasDerivWithinAt
      (s := Set.Icc 0 T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t ht.1).2]
      simp [wX, ht.2]
    · rw [(hπT T hT).2]
      simp [wX]
    · rw [sub_self, trapPi_zero hne, hπTv]
      ring
  · have hd := ((postBranch_hasDerivAt (lamb ρ κ σ) T πT T).const_mul (lamf ρ κ σ)).div_const κ
      |>.hasDerivWithinAt (s := Set.Ici T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t (le_trans hT ht)).2]
      rcases eq_or_lt_of_le (Set.mem_Ici.1 ht) with h | h
      · subst h
        simp [wX, trapPi_zero hne, trapY_zero]
        field_simp
        ring
      · simp [wX, not_le.2 h]
    · rw [(hπT T hT).2]
      simp [wX, trapPi_zero hne, trapY_zero]
      field_simp
      ring
    · rw [hπTv]
      simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      field_simp
      linear_combination (-πT) * hmul

/-! ## (20.8)–(20.10) for continuous forcing on the whole line -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474, on the whole time line: `x`, `π` differentiable at
every date with `ẋ = σ(i − π − u)`, `π̇ = ρπ − κ(x + g)`. -/
def IsGlobalSol (σ ρ κ : ℝ) (i u g x π : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (σ * (i t - π t - u t)) t ∧ HasDerivAt π (ρ * π t - κ * (x t + g t)) t

/-- Cochrane (2023), (20.9), p. 475 (survey E6: `r_t` there is the natural rate `u_{r,t}`):
the forcing `z = κσ(i − u_r) + κ dg/dt`, with `g'` the derivative of `g`. -/
noncomputable def zForce (σ κ : ℝ) (i u g' : ℝ → ℝ) (t : ℝ) : ℝ :=
  κ * σ * (i t - u t) + κ * g' t

/-- Cochrane (2023), (20.10), p. 475: the output gap of the member with constant `C`,
`κx = −κg + λ^f C e^{−λ^b t} + (λ^f + λ^b)⁻¹[λ^f ∫_{−∞}^t … − λ^b ∫_t^∞ …]`. -/
noncomputable def bookX (σ κ ρ : ℝ) (g z : ℝ → ℝ) (C t : ℝ) : ℝ :=
  (-(κ * g t) + lamf ρ κ σ * C * Real.exp (-(lamb ρ κ σ * t)) +
    (lamf ρ κ σ * bwdInfInt (lamb ρ κ σ) z t - lamb ρ κ σ * fwdInt (lamf ρ κ σ) z t) /
      (lamf ρ κ σ + lamb ρ κ σ)) / κ

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **every member of the family solves the
model**: for each `C`, `(x, π) = ((20.10), (20.8))` satisfies (20.5)–(20.6) at every date
(continuous `i`, `u`; differentiable `g` with continuous derivative; bounded forcing (20.9)). -/
theorem eq20_8_solves {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M) (C : ℝ) :
    IsGlobalSol σ ρ κ i u g (bookX σ κ ρ g (zForce σ κ i u g') C)
      (greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : Continuous (zForce σ κ i u g') := by unfold zForce; fun_prop
  set z := zForce σ κ i u g' with hzdef
  intro t
  have hB := bwdInfInt_hasDerivAt hb hz hM t
  have hF := fwdInt_hasDerivAt hf hz hM t
  refine ⟨?_, ?_⟩
  · have := (((((hg t).const_mul κ).neg.add ((hasDerivAt_expNeg (lamb ρ κ σ) t).const_mul
      (lamf ρ κ σ * C))).add (((hB.const_mul (lamf ρ κ σ)).sub
        (hF.const_mul (lamb ρ κ σ))).div_const (lamf ρ κ σ + lamb ρ κ σ))).div_const κ)
    refine this.congr_deriv ?_
    simp only [greenPi, hzdef, zForce]
    field_simp
    linear_combination (-(C * Real.exp (-(lamb ρ κ σ * t)) * (lamf ρ κ σ + lamb ρ κ σ)) -
      (bwdInfInt (lamb ρ κ σ) z t + fwdInt (lamf ρ κ σ) z t)) * hmul
  · have key : κ * bookX σ κ ρ g z C t = -(κ * g t) +
        lamf ρ κ σ * greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t - fwdInt (lamf ρ κ σ) z t := by
      simp only [bookX, greenPi]
      field_simp
      ring
    refine (greenPi_hasDerivAt hf hb hz hM t).congr_deriv ?_
    linear_combination key + greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t * hsub

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **the forward-stable solutions are exactly the
family (20.8)–(20.10)** (both directions). For a solution of (20.5)–(20.6) at every date (with
continuous `i`, `u`, differentiable `g` with continuous derivative, and bounded forcing (20.9)),
`e^{−λ^f t}π_t → 0` (no forward explosion) iff `π` is (20.8) and `x` is (20.10) for some `C`. -/
theorem eq20_8_iff {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' x π : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M)
    (h : IsGlobalSol σ ρ κ i u g x π) :
    Tendsto (fun t => Real.exp (-(lamf ρ κ σ * t)) * π t) atTop (𝓝 0) ↔
      ∃ C, π = greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C ∧
        x = bookX σ κ ρ g (zForce σ κ i u g') C := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : Continuous (zForce σ κ i u g') := by unfold zForce; fun_prop
  set z := zForce σ κ i u g' with hzdef
  set y : ℝ → ℝ := fun t => lamf ρ κ σ * π t - κ * (x t + g t) with hy
  have hπd : ∀ t, HasDerivAt π (-lamb ρ κ σ * π t + y t) t := fun t =>
    (h t).2.congr_deriv (by simp only [hy]; linear_combination (-(π t)) * hsub)
  have hyd : ∀ t, HasDerivAt y (lamf ρ κ σ * y t - z t) t := fun t => by
    have := (((h t).2.const_mul (lamf ρ κ σ)).sub (((h t).1.add (hg t)).const_mul κ))
    refine this.congr_deriv ?_
    simp only [hy, hzdef, zForce]
    linear_combination (-(π t)) * hroot
  rw [forward_stable_iff hf hb hz hM hπd hyd]
  constructor
  · rintro ⟨C, hC, hyF⟩
    refine ⟨C, hC, funext fun t => ?_⟩
    have hyt := congrFun hyF t
    simp only [hy] at hyt
    have hπt := congrFun hC t
    have key : κ * bookX σ κ ρ g z C t = -(κ * g t) +
        lamf ρ κ σ * greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t - fwdInt (lamf ρ κ σ) z t := by
      simp only [bookX, greenPi]
      field_simp
      ring
    apply mul_left_cancel₀ hκ.ne'
    rw [key, ← hπt]
    linarith
  · rintro ⟨C, hC, hx⟩
    refine ⟨C, hC, funext fun t => ?_⟩
    simp only [hy, congrFun hx t, congrFun hC t, bookX, greenPi]
    field_simp
    ring

/-- Cochrane (2023), §20.2.2, p. 475 ("multiple forward-stable equilibrium inflation paths,
indexed by the free constant `C`"): **the forward-stable solutions are in bijection with `ℝ`
via `C`.** -/
noncomputable def family_equiv {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M) :
    ℝ ≃ {p : (ℝ → ℝ) × (ℝ → ℝ) // IsGlobalSol σ ρ κ i u g p.1 p.2 ∧
      Tendsto (fun t => Real.exp (-(lamf ρ κ σ * t)) * p.2 t) atTop (𝓝 0)} where
  toFun C := ⟨(bookX σ κ ρ g (zForce σ κ i u g') C,
      greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C),
    eq20_8_solves hσ hκ hi hu hg hg' hM C,
    greenPi_forward_stable (lamf_pos hκ hσ) (lamb_pos hκ hσ) hM⟩
  invFun p := p.1.2 0 - (bwdInfInt (lamb ρ κ σ) (zForce σ κ i u g') 0 +
    fwdInt (lamf ρ κ σ) (zForce σ κ i u g') 0) / (lamf ρ κ σ + lamb ρ κ σ)
  left_inv C := by
    simp [greenPi]
  right_inv p := by
    obtain ⟨⟨x, π⟩, hsol, hst⟩ := p
    obtain ⟨C, hC, hx⟩ := (eq20_8_iff hσ hκ hi hu hg hg' hM hsol).1 hst
    subst hC hx
    simp [greenPi]

/-! ## The Stieltjes reading of (20.8)–(20.10) for the experiment (survey E6) -/

/-- Cochrane (2023), (20.8), p. 474: the Green's kernel of (20.8),
`K(t, s) = e^{−λ^b(t−s)}` for `s ≤ t` and `e^{−λ^f(s−t)}` for `s > t`. -/
noncomputable def kern (lf lb t s : ℝ) : ℝ :=
  if s ≤ t then Real.exp (-(lb * (t - s))) else Real.exp (-(lf * (s - t)))

/-- Cochrane (2023), (20.9), p. 475, in the experiment (`i = 0`): the absolutely continuous part
of the forcing, `κσ(i − u_r)`. -/
noncomputable def zTrap (σ κ u T s : ℝ) : ℝ := κ * σ * (0 - trapStep u T s)

/-- Cochrane (2023), (20.8), p. 474: `∫_p^q c e^{−b(t−s)} ds = c(e^{−b(t−q)} − e^{−b(t−p)})/b`. -/
theorem integral_exp_bwd {b : ℝ} (hb : b ≠ 0) (c t p q : ℝ) :
    ∫ s in p..q, c * Real.exp (-(b * (t - s))) =
      c * (Real.exp (-(b * (t - q))) - Real.exp (-(b * (t - p)))) / b := by
  have hd : ∀ s ∈ Set.uIcc p q, HasDerivAt (fun s => c * Real.exp (-(b * (t - s))) / b)
      (c * Real.exp (-(b * (t - s)))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(b * (t - s))) b s := by
      have := ((hasDerivAt_id s).const_sub t).const_mul b |>.neg
      refine this.congr_deriv ?_
      ring
    have := ((h1.exp).const_mul c).div_const b
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => c * Real.exp (-(b * (t - s)))).intervalIntegrable
      p q)]
  ring

/-- Cochrane (2023), (20.8), p. 474: `∫_p^q c e^{−a(s−t)} ds = c(e^{−a(p−t)} − e^{−a(q−t)})/a`. -/
theorem integral_exp_fwd {a : ℝ} (ha : a ≠ 0) (c t p q : ℝ) :
    ∫ s in p..q, c * Real.exp (-(a * (s - t))) =
      c * (Real.exp (-(a * (p - t))) - Real.exp (-(a * (q - t)))) / a := by
  have hd : ∀ s ∈ Set.uIcc p q, HasDerivAt (fun s => -(c * Real.exp (-(a * (s - t)))) / a)
      (c * Real.exp (-(a * (s - t)))) s := by
    intro s _
    have := (((hasDerivAt_expNeg a (s - t)).comp s ((hasDerivAt_id s).sub_const t)).const_mul
      c).neg.div_const a
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => c * Real.exp (-(a * (s - t)))).intervalIntegrable
      p q)]
  ring

/-- Cochrane (2023), (20.8), p. 474, the backward integral in the trap (`0 ≤ t ≤ T`):
`∫_0^t e^{−b(t−s)} z_s ds = c(1 − e^{−bt})/b` for `z = c` on `[0, T)`. -/
theorem bwd_step_le {b c T t : ℝ} (hb : b ≠ 0) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      c * (1 - Real.exp (-(b * t))) / b := by
  have h : ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      ∫ s in (0 : ℝ)..t, c * Real.exp (-(b * (t - s))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume T] with s hs hmem
    rw [Set.uIoc_of_le ht] at hmem
    have : s < T := lt_of_le_of_ne (le_trans hmem.2 htT) hs
    simp [trapStep, this, mul_comm]
  rw [h, integral_exp_bwd hb]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]

/-- Cochrane (2023), (20.8), p. 474, the backward integral after the trap (`0 ≤ T ≤ t`):
`∫_0^t e^{−b(t−s)} z_s ds = c(e^{−b(t−T)} − e^{−bt})/b`. -/
theorem bwd_step_ge {b c T t : ℝ} (hb : b ≠ 0) (hT : 0 ≤ T) (htT : T ≤ t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      c * (Real.exp (-(b * (t - T))) - Real.exp (-(b * t))) / b := by
  have hind : (fun s => Real.exp (-(b * (t - s))) * trapStep c T s) =
      (Set.Iio T).indicator fun s => c * Real.exp (-(b * (t - s))) := by
    funext s
    by_cases hs : s < T
    · simp [trapStep, hs, Set.indicator, mul_comm]
    · simp [trapStep, hs, Set.indicator]
  rw [intervalIntegral.integral_of_le (le_trans hT htT), hind,
    setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc 0 t ∩ Set.Iio T = Set.Ioo 0 T := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT,
    integral_exp_bwd hb]
  simp only [sub_zero]

/-- Cochrane (2023), (20.8), p. 474, the forward integral in the trap (`t ≤ T`):
`∫_t^∞ e^{−a(s−t)} z_s ds = c(1 − e^{−a(T−t)})/a`. -/
theorem fwd_step_le {a c T t : ℝ} (ha : a ≠ 0) (htT : t ≤ T) :
    ∫ s in Set.Ioi t, Real.exp (-(a * (s - t))) * trapStep c T s =
      c * (1 - Real.exp (-(a * (T - t)))) / a := by
  have hind : (fun s => Real.exp (-(a * (s - t))) * trapStep c T s) =
      (Set.Iio T).indicator fun s => c * Real.exp (-(a * (s - t))) := by
    funext s
    by_cases hs : s < T
    · simp [trapStep, hs, Set.indicator, mul_comm]
    · simp [trapStep, hs, Set.indicator]
  rw [hind, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le htT, integral_exp_fwd ha]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- Cochrane (2023), (20.8), p. 474, the forward integral after the trap (`T ≤ t`): `0`. -/
theorem fwd_step_ge {a c T t : ℝ} (htT : T ≤ t) :
    ∫ s in Set.Ioi t, Real.exp (-(a * (s - t))) * trapStep c T s = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun s (hs : t < s) => ?_
  have : ¬ s < T := by linarith
  simp [trapStep, this]

/-- Cochrane (2023), (20.8), p. 475: the constant `C` of the member indexed by `π_T` (the
correspondence `π_T ↦ C` is affine with slope `e^{λ^b T}`):
`C = π_T e^{λ^b T} − (e^{λ^b T} − 1)(λ^f A − κ g)/(λ^f + λ^b)`, `A = −u`. -/
noncomputable def bookC (σ κ ρ T u g πT : ℝ) : ℝ :=
  πT * Real.exp (lamb ρ κ σ * T) -
    (Real.exp (lamb ρ κ σ * T) - 1) * (lamf ρ κ σ * (-u) - κ * g) / (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.8), p. 474 (Stieltjes reading, survey E6): the contribution of the
atoms of `κ dg = κ g(δ_0 − δ_T)` that lie at or before `t`. -/
noncomputable def atomsB (lf lb κ g T t : ℝ) : ℝ :=
  κ * g * (kern lf lb t 0 - if T ≤ t then kern lf lb t T else 0)

/-- Cochrane (2023), (20.8), p. 474 (Stieltjes reading): the contribution of the atom of
`κ dg` that lies after `t` (the `−κ g δ_T` at the end of the trap). -/
noncomputable def atomsF (lf lb κ g T t : ℝ) : ℝ :=
  -(κ * g * if T ≤ t then 0 else kern lf lb t T)

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **the book's formulas for the experiment.**
With `dg/dt` read as the measure `g(δ_0 − δ_T)` (survey E6), the member indexed by `π_T` is, for
every `t ≥ 0`, `π_t = C e^{−λ^b t} + (λ^f+λ^b)⁻¹[∫_0^t e^{−λ^b(t−s)}z_s ds +
∫_t^∞ e^{−λ^f(s−t)}z_s ds + atoms]` (20.8) and `κx_t = −κg_t + λ^f C e^{−λ^b t} +
(λ^f+λ^b)⁻¹[λ^f(∫_0^t … + atoms ≤ t) − λ^b(∫_t^∞ … + atoms > t)]` (20.10), with
`C = bookC π_T`. -/
theorem book_form {σ κ ρ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) (πT t : ℝ)
    (ht : 0 ≤ t) :
    wPi σ κ ρ T u g πT t = bookC σ κ ρ T u g πT * Real.exp (-(lamb ρ κ σ * t)) +
        ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
          (∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
          atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) /
          (lamf ρ κ σ + lamb ρ κ σ) ∧
      κ * wX σ κ ρ T u g πT t = -(κ * trapStep g T t) +
        lamf ρ κ σ * bookC σ κ ρ T u g πT * Real.exp (-(lamb ρ κ σ * t)) +
        (lamf ρ κ σ * ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s)
            + atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) -
          lamb ρ κ σ * ((∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) *
            zTrap σ κ u T s) + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t)) /
          (lamf ρ κ σ + lamb ρ κ σ) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : ∀ s, zTrap σ κ u T s = trapStep (κ * σ * (0 - u)) T s := fun s => by
    unfold zTrap trapStep; split_ifs <;> ring
  simp only [hz]
  have eA : Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  have eB : Real.exp (-(lamb ρ κ σ * (t - T))) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  rcases le_or_gt t T with htT | htT
  · rw [bwd_step_le hb.ne' ht htT, fwd_step_le hf.ne' htT]
    rcases eq_or_lt_of_le htT with h | h
    · subst h
      simp only [wPi, wX, le_refl, ↓reduceIte, atomsB, atomsF, kern, ht, trapStep, lt_irrefl,
        trapPi, trapY, hh, kk, bookC, sub_self, sub_zero, mul_zero, neg_zero, Real.exp_zero,
        mul_one, Real.exp_neg]
      rw [← hmul]
      constructor
      · field_simp
        ring
      · field_simp
        ring
    · simp only [wPi, wX, htT, ↓reduceIte, atomsB, atomsF, kern, ht, not_le.2 h, trapStep, h,
        trapPi, trapY, hh, kk, bookC, sub_zero]
      rw [eA, ← hmul]
      constructor
      · field_simp
        ring
      · field_simp
        ring
  · rw [bwd_step_ge hb.ne' hT htT.le, fwd_step_ge htT.le]
    simp only [wPi, wX, not_le.2 htT, ↓reduceIte, atomsB, atomsF, kern, ht, htT.le, trapStep,
      not_lt.2 htT.le, bookC, sub_zero]
    rw [eB, ← hmul]
    constructor
    · field_simp
      ring
    · field_simp
      ring

/-- Cochrane (2023), (20.8), p. 474, for the experiment (Stieltjes reading): the right-hand side
of (20.8) with constant `C`. -/
noncomputable def bookPi (σ κ ρ T u g C t : ℝ) : ℝ :=
  C * Real.exp (-(lamb ρ κ σ * t)) +
    ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
      (∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
      atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) /
      (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.10), p. 475, for the experiment (Stieltjes reading): the right-hand
side of (20.10) (`κ x_t`) with constant `C`. -/
noncomputable def bookKX (σ κ ρ T u g C t : ℝ) : ℝ :=
  -(κ * trapStep g T t) + lamf ρ κ σ * C * Real.exp (-(lamb ρ κ σ * t)) +
    (lamf ρ κ σ * ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
        atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) -
      lamb ρ κ σ * ((∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
        atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t)) / (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475, for the experiment (survey E6): **the bounded
paths are exactly the book's formulas (20.8) and (20.10)**, for some constant `C`, with
`dg/dt` read as the measure `g(δ_0 − δ_T)`. -/
theorem experiment_eq20_8 {σ κ ρ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    {x π : ℝ → ℝ} :
    (IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
        BddOnIci π) ↔
      ∃ C, ∀ t, 0 ≤ t → π t = bookPi σ κ ρ T u g C t ∧ κ * x t = bookKX σ κ ρ T u g C t := by
  rw [bdd_path_iff hκ hσ]
  constructor
  · rintro ⟨πT, h⟩
    refine ⟨bookC σ κ ρ T u g πT, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := book_form (ρ := ρ) (u := u) (g := g) hσ hκ hT πT t ht
    rw [(h t ht).1, (h t ht).2]
    exact ⟨h1, h2⟩
  · rintro ⟨C, h⟩
    have hE := Real.exp_pos (lamb ρ κ σ * T)
    set K0 := (Real.exp (lamb ρ κ σ * T) - 1) * (lamf ρ κ σ * (-u) - κ * g) /
      (lamf ρ κ σ + lamb ρ κ σ)
    refine ⟨(C + K0) / Real.exp (lamb ρ κ σ * T), fun t ht => ?_⟩
    have hC : bookC σ κ ρ T u g ((C + K0) / Real.exp (lamb ρ κ σ * T)) = C := by
      simp only [bookC, K0]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := book_form (ρ := ρ) (u := u) (g := g) hσ hκ hT
      ((C + K0) / Real.exp (lamb ρ κ σ * T)) t ht
    rw [hC] at h1 h2
    refine ⟨by rw [(h t ht).1]; exact h1.symm, ?_⟩
    apply mul_left_cancel₀ hκ.ne'
    rw [(h t ht).2]
    exact h2.symm

/-- Cochrane (2023), (20.8), p. 475: the constant `C` in (20.8) is pinned by `π_0`, so it is
unique. -/
theorem bookPi_C_unique {σ κ ρ T u g C C' : ℝ}
    (h : bookPi σ κ ρ T u g C 0 = bookPi σ κ ρ T u g C' 0) : C = C' := by
  simp only [bookPi, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  linarith

/-! ## (20.7): an active rule after `T` selects the chosen path -/

/-- Cochrane (2023), (20.7), p. 474: **deviations from the chosen path under an active rule
explode.** If `p = π − π*` and `d = x − x*` are continuous on `[T, ∞)`, bounded there, and on
`(T, ∞)` (off a countable set) `ḋ = σ(φ − 1)p`, `ṗ = ρp − κd`, with `σ, κ, ρ > 0` and `φ > 1`,
then `p = d = 0` on `[T, ∞)` (both roots of `λ² − ρλ + κσ(φ−1)` have positive real part). -/
theorem active_rule_dev_zero {σ κ ρ φ T : ℝ} {p d : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ) (hφ : 1 < φ) (hpc : ContinuousOn p (Set.Ici T))
    (hdc : ContinuousOn d (Set.Ici T))
    (hd : ∀ t, T < t → t ∉ S →
      HasDerivAt d (σ * (φ - 1) * p t) t ∧ HasDerivAt p (ρ * p t - κ * d t) t)
    (Kp Kd : ℝ) (hpb : ∀ t, T ≤ t → |p t| ≤ Kp) (hdb : ∀ t, T ≤ t → |d t| ≤ Kd) :
    ∀ t, T ≤ t → p t = 0 ∧ d t = 0 := by
  set c := κ * σ * (φ - 1) with hc
  have hcpos : 0 < c := by have := mul_pos hκ hσ; simp only [hc]; nlinarith
  -- `q = ρp − κd` is `ṗ`, and `q̇ = ρq − c p`
  have hqd : ∀ t, T < t → t ∉ S →
      HasDerivAt (fun s => ρ * p s - κ * d s) (ρ * (ρ * p t - κ * d t) - c * p t) t :=
    fun t ht hts => by
      obtain ⟨a, b⟩ := hd t ht hts
      exact ((b.const_mul ρ).sub (a.const_mul κ)).congr_deriv (by simp only [hc]; ring)
  have hqc : ContinuousOn (fun s => ρ * p s - κ * d s) (Set.Ici T) :=
    (continuousOn_const.mul hpc).sub (continuousOn_const.mul hdc)
  have hqb : ∀ t, T ≤ t → |ρ * p t - κ * d t| ≤ ρ * Kp + κ * Kd := fun t ht => by
    calc |ρ * p t - κ * d t| ≤ |ρ * p t| + |κ * d t| := abs_sub _ _
      _ = ρ * |p t| + κ * |d t| := by rw [abs_mul, abs_mul, abs_of_pos hρ, abs_of_pos hκ]
      _ ≤ ρ * Kp + κ * Kd := add_le_add (mul_le_mul_of_nonneg_left (hpb t ht) hρ.le)
          (mul_le_mul_of_nonneg_left (hdb t ht) hκ.le)
  set q : ℝ → ℝ := fun s => ρ * p s - κ * d s with hqdef
  have hpd : ∀ t, T < t → t ∉ S → HasDerivAt p (q t) t := fun t ht hts => (hd t ht hts).2
  have hpq : ∀ t, T ≤ t → p t = 0 ∧ q t = 0 := by
    rcases lt_or_ge (ρ ^ 2) (4 * c) with hdisc | hdisc
    · -- complex roots: `V = q² − ρpq + cp²` grows at rate `ρ`
      have hV := unstable_bdd_zero (f := fun s => q s ^ 2 - ρ * p s * q s + c * p s ^ 2)
        (a := ρ) (p := T) (K := (ρ * Kp + κ * Kd) ^ 2 + ρ * Kp * (ρ * Kp + κ * Kd) + c * Kp ^ 2)
        hρ hS (((hqc.pow 2).sub ((continuousOn_const.mul hpc).mul hqc)).add
          (continuousOn_const.mul (hpc.pow 2)))
        (fun t ht hts => by
          have hq := hqd t ht hts
          have hp := hpd t ht hts
          refine (((hq.pow 2).sub ((hp.const_mul ρ).mul hq)).add
            ((hp.pow 2).const_mul c)).congr_deriv ?_
          simp only [hqdef]
          ring)
        (fun t ht => by
          have h1 := hpb t ht
          have h2 := hqb t ht
          have hKp : 0 ≤ Kp := le_trans (abs_nonneg _) h1
          calc |q t ^ 2 - ρ * p t * q t + c * p t ^ 2|
              ≤ |q t ^ 2| + |ρ * p t * q t| + |c * p t ^ 2| := by
                refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
            _ = |q t| ^ 2 + ρ * |p t| * |q t| + c * |p t| ^ 2 := by
                rw [abs_pow, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hρ,
                  abs_of_pos hcpos]
            _ ≤ (ρ * Kp + κ * Kd) ^ 2 + ρ * Kp * (ρ * Kp + κ * Kd) + c * Kp ^ 2 := by
                have a1 := abs_nonneg (p t)
                have a2 := abs_nonneg (q t)
                gcongr)
      intro t ht
      have h0 := hV t ht
      have e1 : (2 * q t - ρ * p t) ^ 2 + (4 * c - ρ ^ 2) * p t ^ 2 = 0 := by
        linear_combination 4 * h0
      have hp0 : p t = 0 := by
        have := sq_nonneg (2 * q t - ρ * p t)
        have h4 : 0 < 4 * c - ρ ^ 2 := by linarith
        have : (4 * c - ρ ^ 2) * p t ^ 2 = 0 := by nlinarith [sq_nonneg (p t)]
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      refine ⟨hp0, ?_⟩
      rw [hp0] at e1
      have : (2 * q t) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · -- real roots `λ₁ ≥ λ₂ > 0`
      set D := Real.sqrt (ρ ^ 2 - 4 * c) with hD
      have hD2 : D ^ 2 = ρ ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
      have hD0 : 0 ≤ D := Real.sqrt_nonneg _
      have hDρ : D < ρ := by
        rw [hD, Real.sqrt_lt' hρ]
        linarith
      set l1 := (ρ + D) / 2
      set l2 := (ρ - D) / 2
      have hl1 : 0 < l1 := by simp only [l1]; linarith
      have hl2 : 0 < l2 := by simp only [l2]; linarith
      have hprod : l1 * l2 = c := by simp only [l1, l2]; linear_combination (-1 / 4) * hD2
      have hsum : l1 + l2 = ρ := by simp only [l1, l2]; ring
      have hm := unstable_bdd_zero (f := fun s => q s - l1 * p s) (a := l2) (p := T)
        (K := (ρ * Kp + κ * Kd) + l1 * Kp) hl2 hS (hqc.sub (continuousOn_const.mul hpc))
        (fun t ht hts => by
          refine ((hqd t ht hts).sub ((hpd t ht hts).const_mul l1)).congr_deriv ?_
          simp only [hqdef]
          linear_combination (p t) * hprod - (ρ * p t - κ * d t) * hsum)
        (fun t ht => by
          calc |q t - l1 * p t| ≤ |q t| + |l1 * p t| := abs_sub _ _
            _ = |q t| + l1 * |p t| := by rw [abs_mul, abs_of_pos hl1]
            _ ≤ (ρ * Kp + κ * Kd) + l1 * Kp :=
              add_le_add (hqb t ht) (mul_le_mul_of_nonneg_left (hpb t ht) hl1.le))
      have hp := unstable_bdd_zero (f := p) (a := l1) (p := T) (K := Kp) hl1 hS hpc
        (fun t ht hts => (hpd t ht hts).congr_deriv (by
          have := hm t ht.le
          linarith)) hpb
      intro t ht
      have h1 := hm t ht
      refine ⟨hp t ht, ?_⟩
      rw [hp t ht] at h1
      linarith
  intro t ht
  obtain ⟨h1, h2⟩ := hpq t ht
  refine ⟨h1, ?_⟩
  simp only [hqdef, h1, mul_zero, zero_sub, neg_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · linarith
  · exact h

/-- Cochrane (2023), (20.7), p. 474: **adding active monetary policy after the trap selects the
chosen path.** Let `(x*, π*)` solve (20.5)–(20.6) on `(T, ∞)` with interest rate `i*`, and
`(x, π)` solve them with the rule `i = i* + φ(π − π*)`, `φ > 1` (same `u_r`, `g`). If both are
continuous and bounded on `[T, ∞)` then `(x, π) = (x*, π*)` on `[T, ∞)`. -/
theorem eq20_7_selects {σ κ ρ φ T : ℝ} {istar u g x π xs πs : ℝ → ℝ} {S : Set ℝ}
    (hS : S.Countable) (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ) (hφ : 1 < φ)
    (hxc : ContinuousOn x (Set.Ici T)) (hπc : ContinuousOn π (Set.Ici T))
    (hxsc : ContinuousOn xs (Set.Ici T)) (hπsc : ContinuousOn πs (Set.Ici T))
    (h : ∀ t, T < t → t ∉ S →
      HasDerivAt x (σ * ((istar t + φ * (π t - πs t)) - π t - u t)) t ∧
        HasDerivAt π (ρ * π t - κ * (x t + g t)) t)
    (hs : ∀ t, T < t → t ∉ S →
      HasDerivAt xs (σ * (istar t - πs t - u t)) t ∧
        HasDerivAt πs (ρ * πs t - κ * (xs t + g t)) t)
    (Kx Kπ Kxs Kπs : ℝ) (hxb : ∀ t, T ≤ t → |x t| ≤ Kx) (hπb : ∀ t, T ≤ t → |π t| ≤ Kπ)
    (hxsb : ∀ t, T ≤ t → |xs t| ≤ Kxs) (hπsb : ∀ t, T ≤ t → |πs t| ≤ Kπs) :
    ∀ t, T ≤ t → π t = πs t ∧ x t = xs t := by
  have := active_rule_dev_zero (p := fun s => π s - πs s) (d := fun s => x s - xs s) hS hσ hκ
    hρ hφ (hπc.sub hπsc) (hxc.sub hxsc)
    (fun t ht hts => by
      obtain ⟨a, b⟩ := h t ht hts
      obtain ⟨a', b'⟩ := hs t ht hts
      exact ⟨(a.sub a').congr_deriv (by ring), (b.sub b').congr_deriv (by ring)⟩)
    (Kπ + Kπs) (Kx + Kxs)
    (fun t ht => (abs_sub _ _).trans (add_le_add (hπb t ht) (hπsb t ht)))
    (fun t ht => (abs_sub _ _).trans (add_le_add (hxb t ht) (hxsb t ht)))
  intro t ht
  obtain ⟨h1, h2⟩ := this t ht
  exact ⟨by linarith, by linarith⟩

end Cochrane.ZeroBound.WerningModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium selection at the zero bound: the deflation jump and the frictionless limit

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2–20.2.3,
pp. 474–478.

In the Werning experiment (`WerningModel`) the bounded equilibria form a one-parameter family.
The new-Keynesian selection picks `π_T = 0`; the fiscal selection picks no inflation jump,
`π_0 = 0`. Throughout `u < 0` is the natural rate during the trap (the book: `−2%`), `g = 0`.

## Main results

* Properties of `h(s) = (λ^f e^{λ^b s} + λ^b e^{−λ^f s})/(λ^f+λ^b)`: `hh_strictMonoOn`,
  `one_lt_hh`, `hh_ge`, `kk_pos`; and `hh_strictMono_kappa` (via the `cosh`/`sinh` form
  `hh_eq_cosh`): `h` increases as prices become more flexible (`ρ ≥ 0`).
* The `π_T = 0` equilibrium (p. 475–476): `pi0NK_eq` (`π_0 = −u(1 − h(T))`), `pi0NK_book` (the
  closed form with `(1 − e^{−λ^f T})/λ^f − (e^{λ^b T} − 1)/λ^b`); deflation throughout the trap
  (`nk_pi_neg`), steadily improving (`nk_pi_strictMonoOn`), no inflation after (`nk_after`);
  output gap negative and rising (`nk_x_neg`, `nk_x_strictMonoOn`).
* "Backward explosion" and the frictionless limit: `pi0NK_tendsto_T`, `pi0NK_tendsto_kappa`,
  `nk_tendsto_kappa` (every date of the trap), `pi0NK_strictAnti_kappa` (deflation larger as
  `κ` rises), `x0NK_tendsto_kappa` (and the output gap); `nk_x_eq_HH`
  (`x_t = σu∫_0^{T−t} h`), `nk_x_strictAnti_kappa`, `x0NK_strictAnti_kappa` (the output gap is
  strictly decreasing in `κ` at every date of the trap).
* The frictionless model (p. 477): `frictionless_iff` (`x = −g`, `π = i − u_r`, a unique path).
* The discontinuity (p. 478): `nk_discontinuity`.
* The `π_0 = 0` equilibrium (pp. 476, 478): `nj_pi0`, `nj_formula`, `nj_pos`, `nj_lt`
  (`0 < π_t < −u`), `nj_tendsto_time`, the smooth square-wave limit `nj_limit_trap`,
  `nj_limit_after`, uniformly on compacts (`nj_uniform_trap`, `nj_uniform_after`).
* The fiscal reading (p. 476): `jump_eq_fiscal` — across equilibria
  `π_0 − π_0' = −(r + λ^b)(PV(s̃) − PV(s̃'))`; `nk_fiscal_contraction` — the `π_T = 0`
  equilibrium needs a fiscal contraction, unboundedly large as `κ → ∞`.
* `gap_neg_iff` (p. 476): with `g = 0`, `x_t < 0` iff `dπ/dt > ρπ_t`.
-/

namespace Cochrane.ZeroBound.ZLBSelection

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel

/-! ## The function `h` -/

/-- Cochrane (2023), §20.2.5, p. 481: `k(s) > 0` for `s > 0`. -/
theorem kk_pos {lf lb s : ℝ} (hf : 0 < lf) (hb : 0 < lb) (hs : 0 < s) : 0 < kk lf lb s := by
  unfold kk
  refine div_pos (sub_pos.2 (Real.exp_lt_exp.2 ?_)) (by linarith)
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481: `k` is strictly increasing. -/
theorem kk_strictMono {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) : StrictMono (kk lf lb) :=
  strictMono_of_deriv_pos fun s => by
    rw [(kk_hasDerivAt lf lb s).deriv]
    have := Real.exp_pos (lb * s)
    have := Real.exp_pos (-(lf * s))
    positivity

/-- Cochrane (2023), §20.2.2, p. 475: `h` is strictly increasing on `[0, ∞)`. -/
theorem hh_strictMonoOn {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) :
    StrictMonoOn (hh lf lb) (Set.Ici 0) := by
  have hne : lf + lb ≠ 0 := by linarith
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun s _ => (hh_hasDerivAt hne s).continuousAt.continuousWithinAt) fun s hs => ?_
  rw [interior_Ici] at hs
  rw [(hh_hasDerivAt hne s).deriv]
  have := kk_pos hf hb hs
  positivity

/-- Cochrane (2023), §20.2.2, p. 475: `h(s) > 1` for `s > 0`. -/
theorem one_lt_hh {lf lb s : ℝ} (hf : 0 < lf) (hb : 0 < lb) (hs : 0 < s) : 1 < hh lf lb s := by
  have h := hh_strictMonoOn hf hb (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  rwa [hh_zero (by linarith)] at h

/-- Cochrane (2023), §20.2.2, p. 475: the exponential lower bound
`h(s) ≥ λ^f e^{λ^b s}/(λ^f + λ^b)`. -/
theorem hh_ge {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) (s : ℝ) :
    lf * Real.exp (lb * s) / (lf + lb) ≤ hh lf lb s := by
  unfold hh
  have := Real.exp_pos (-(lf * s))
  exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)

/-- Cochrane (2023), §20.2.3, p. 477: `sinh v / v` is strictly increasing on `(0, ∞)`. -/
theorem sinhc_strictMonoOn : StrictMonoOn (fun v => Real.sinh v / v) (Set.Ioi 0) := by
  -- `v cosh v − sinh v > 0` for `v > 0`
  have hg : StrictMonoOn (fun v => v * Real.cosh v - Real.sinh v) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) fun v hv => ?_
    rw [interior_Ici] at hv
    have hd : HasDerivAt (fun v => v * Real.cosh v - Real.sinh v) (v * Real.sinh v) v := by
      have := ((hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)).sub (Real.hasDerivAt_sinh v)
      refine this.congr_deriv ?_
      simp only [id]
      ring
    rw [hd.deriv]
    exact mul_pos hv (Real.sinh_pos_iff.2 hv)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun v hv => ((Real.continuous_sinh.continuousAt.div continuousAt_id
      (ne_of_gt hv)).continuousWithinAt)) fun v hv => ?_
  rw [interior_Ioi] at hv
  have hv0 : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hd : HasDerivAt (fun v => Real.sinh v / v)
      ((v * Real.cosh v - Real.sinh v) / v ^ 2) v := by
    have := (Real.hasDerivAt_sinh v).div (hasDerivAt_id v) hv0
    refine this.congr_deriv ?_
    simp only [id]
    ring
  rw [hd.deriv]
  have h0 := hg (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv.le) hv
  simp only [Real.sinh_zero, zero_mul, sub_zero] at h0
  positivity

/-- Cochrane (2023), §20.2.3, p. 477: the hyperbolic form of `h`. With `S = λ^f + λ^b`,
`ρ = λ^f − λ^b` and `v = Ss/2 > 0`: `h(s) = e^{−ρs/2}(cosh v + (ρs/2) sinh v / v)`. -/
theorem hh_eq_cosh {lf lb s : ℝ} (hS : 0 < lf + lb) (hs : 0 < s) :
    hh lf lb s = Real.exp (-((lf - lb) * s / 2)) *
      (Real.cosh ((lf + lb) * s / 2) + (lf - lb) * s / 2 *
        (Real.sinh ((lf + lb) * s / 2) / ((lf + lb) * s / 2))) := by
  have hv : (lf + lb) * s / 2 ≠ 0 := by positivity
  rw [Real.cosh_eq, Real.sinh_eq]
  unfold hh
  have e1 : Real.exp (lb * s) =
      Real.exp (-((lf - lb) * s / 2)) * Real.exp ((lf + lb) * s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lf * s)) =
      Real.exp (-((lf - lb) * s / 2)) * Real.exp (-((lf + lb) * s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  field_simp
  ring

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation … larger as price stickiness is reduced"):
for `ρ ≥ 0` and `s > 0`, `h(s)` is strictly increasing in `κ`. -/
theorem hh_strictMono_kappa {ρ σ κ κ' s : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlt : κ < κ') (hs : 0 < s) :
    hh (lamf ρ κ σ) (lamb ρ κ σ) s < hh (lamf ρ κ' σ) (lamb ρ κ' σ) s := by
  have hκ' : 0 < κ' := by linarith
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have hS' := lamf_add_lamb_pos (ρ := ρ) hκ' hσ
  rw [hh_eq_cosh hS hs, hh_eq_cosh hS' hs, lamf_sub_lamb, lamf_sub_lamb]
  have hSlt : lamf ρ κ σ + lamb ρ κ σ < lamf ρ κ' σ + lamb ρ κ' σ := by
    have := lamb_strictMono (ρ := ρ) hσ hκ hlt
    have := lamf_strictMono (ρ := ρ) hσ hκ hlt
    linarith
  have hv : 0 < (lamf ρ κ σ + lamb ρ κ σ) * s / 2 := by positivity
  have hvlt : (lamf ρ κ σ + lamb ρ κ σ) * s / 2 < (lamf ρ κ' σ + lamb ρ κ' σ) * s / 2 := by
    have := mul_lt_mul_of_pos_right hSlt hs
    linarith
  have hc : Real.cosh ((lamf ρ κ σ + lamb ρ κ σ) * s / 2) <
      Real.cosh ((lamf ρ κ' σ + lamb ρ κ' σ) * s / 2) := by
    rw [Real.cosh_lt_cosh, abs_of_pos hv, abs_of_pos (by linarith)]
    exact hvlt
  have hsh := sinhc_strictMonoOn (Set.mem_Ioi.2 hv) (Set.mem_Ioi.2 (by linarith)) hvlt
  simp only at hsh
  have hρs : 0 ≤ ρ * s / 2 := by positivity
  refine mul_lt_mul_of_pos_left ?_ (Real.exp_pos _)
  nlinarith

/-! ## The `π_T = 0` (new-Keynesian) equilibrium -/

/-- Cochrane (2023), §20.2.2, p. 475: initial inflation `π_0` in the new-Keynesian `π_T = 0`
equilibrium (`g = 0`). -/
noncomputable def pi0NK (σ κ ρ T u : ℝ) : ℝ := wPi σ κ ρ T u 0 0 0

/-- Cochrane (2023), §20.2.2, p. 475: the `π_T = 0` path during the trap,
`π_t = −u(1 − h(T − t))` for `t ≤ T`. -/
theorem nk_pi_eq {σ κ ρ T u t : ℝ} (htT : t ≤ T) :
    wPi σ κ ρ T u 0 0 t = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t)) := by
  simp [wPi, htT, trapPi]

/-- Cochrane (2023), §20.2.2, p. 475: `π_0 = −u(1 − h(T))` in the `π_T = 0` equilibrium. -/
theorem pi0NK_eq {σ κ ρ T u : ℝ} (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) := by
  rw [pi0NK, nk_pi_eq hT, sub_zero]

/-- Cochrane (2023), §20.2.2, pp. 475–476 (cf. Figure 20.5, survey closed form):
`π_0 = −u (κσ/(λ^f+λ^b)) [(1 − e^{−λ^f T})/λ^f − (e^{λ^b T} − 1)/λ^b]`. -/
theorem pi0NK_book {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u = -u * (κ * σ / (lamf ρ κ σ + lamb ρ κ σ)) *
      ((1 - Real.exp (-(lamf ρ κ σ * T))) / lamf ρ κ σ -
        (Real.exp (lamb ρ κ σ * T) - 1) / lamb ρ κ σ) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  rw [pi0NK_eq hT, hh, ← lamf_mul_lamb hκ hσ]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 476: in the `π_T = 0` equilibrium there is deflation
throughout the trap: `π_t < 0` for `0 ≤ t < T` (when `u < 0`). -/
theorem nk_pi_neg {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (htT : t < T) :
    wPi σ κ ρ T u 0 0 t < 0 := by
  rw [nk_pi_eq htT.le]
  have := one_lt_hh (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (sub_pos.2 htT)
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476: in the `π_T = 0` equilibrium inflation and the output gap
are zero from `T` on. -/
theorem nk_after {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : T ≤ t) :
    wPi σ κ ρ T u 0 0 t = 0 ∧ wX σ κ ρ T u 0 0 t = 0 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  rcases eq_or_lt_of_le htT with h | h
  · subst h
    refine ⟨by simp [wPi, trapPi_zero hne], ?_⟩
    simp [wX, trapPi_zero hne, trapY_zero]
  · exact ⟨by simp [wPi, not_le.2 h], by simp [wX, not_le.2 h]⟩

/-- Cochrane (2023), §20.2.2, p. 476 ("deflation steadily improves … no deflation spiral"): the
`π_T = 0` inflation path is strictly increasing on `[0, T]` (when `u < 0`). -/
theorem nk_pi_strictMonoOn {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    StrictMonoOn (wPi σ κ ρ T u 0 0) (Set.Icc 0 T) := by
  intro t1 h1 t2 h2 hlt
  rw [nk_pi_eq h1.2, nk_pi_eq h2.2]
  have := hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ)
    (Set.mem_Ici.2 (sub_nonneg.2 h2.2)) (Set.mem_Ici.2 (sub_nonneg.2 h1.2))
    (by linarith : T - t2 < T - t1)
  nlinarith

/-- Cochrane (2023), (20.10), p. 475: the `π_T = 0` output gap during the trap,
`κ x_t = λ^f(−u)(1 − h(s)) − λ^b(−u)(1 − e^{−λ^f s})`, `s = T − t`. -/
theorem nk_x_eq {σ κ ρ T u t : ℝ} (hκ : 0 < κ) (htT : t ≤ T) :
    κ * wX σ κ ρ T u 0 0 t = lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t))) -
      lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t)))) := by
  simp only [wX, htT, ↓reduceIte, trapPi, trapY, zero_mul, mul_zero, add_zero, sub_zero,
    zero_add]
  field_simp

/-- Cochrane (2023), §20.2.2, p. 476 ("a large output gap"): in the `π_T = 0` equilibrium the
output gap is negative throughout the trap (when `u < 0`). -/
theorem nk_x_neg {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (htT : t < T) :
    wX σ κ ρ T u 0 0 t < 0 := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have h1 := one_lt_hh hf hb (sub_pos.2 htT)
  have h2 : Real.exp (-(lamf ρ κ σ * (T - t))) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have h := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ htT.le
  have : κ * wX σ κ ρ T u 0 0 t < 0 := by
    rw [h]
    have a : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t))) < 0 := by
      apply mul_neg_of_pos_of_neg hf; nlinarith
    have b : 0 ≤ lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t)))) := by
      apply mul_nonneg (mul_nonneg hb.le (by linarith)); linarith
    linarith
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476 ("expected output growth is strong"): the `π_T = 0` output
gap rises strictly over `[0, T]` (when `u < 0`). -/
theorem nk_x_strictMonoOn {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    StrictMonoOn (wX σ κ ρ T u 0 0) (Set.Icc 0 T) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  intro t1 h1 t2 h2 hlt
  have e1 := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ h1.2
  have e2 := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ h2.2
  have hh12 := hh_strictMonoOn hf hb (Set.mem_Ici.2 (sub_nonneg.2 h2.2))
    (Set.mem_Ici.2 (sub_nonneg.2 h1.2)) (by linarith : T - t2 < T - t1)
  have hex : Real.exp (-(lamf ρ κ σ * (T - t1))) < Real.exp (-(lamf ρ κ σ * (T - t2))) := by
    rw [Real.exp_lt_exp]; nlinarith
  have : κ * wX σ κ ρ T u 0 0 t1 < κ * wX σ κ ρ T u 0 0 t2 := by
    rw [e1, e2]
    have a : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t1))) <
        lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t2))) := by
      apply mul_lt_mul_of_pos_left _ hf; nlinarith
    have b : lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t2)))) ≤
        lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t1)))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.le (by linarith)); linarith
    linarith
  exact lt_of_mul_lt_mul_left this hκ.le

/-- Cochrane (2023), §20.2.2, p. 477: a lower bound on the deflation jump,
`π_0 ≤ −u(1 − λ^f e^{λ^b T}/(λ^f + λ^b))`. -/
theorem pi0NK_le {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u ≤
      -u * (1 - lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ)) := by
  rw [pi0NK_eq hT]
  have := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) T
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 477 ("as we move the length of the zero bound episode `T` to
the right, the new-Keynesian deflation blows up"): `π_0 → −∞` as `T → ∞`. -/
theorem pi0NK_tendsto_T {σ κ ρ u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    Tendsto (fun T => pi0NK σ κ ρ T u) atTop atBot := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  set c := -u * lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ)
  have hu' : 0 < -u := by linarith
  have hc : 0 < c := by simp only [c]; positivity
  have h1 : Tendsto (fun T => -u - c * Real.exp (lamb ρ κ σ * T)) atTop atBot := by
    have := ((tendsto_expPos hb).const_mul_atTop hc)
    exact tendsto_atBot_add_const_left _ (-u) (tendsto_neg_atTop_atBot.comp this) |>.congr
      fun T => by simp [sub_eq_add_neg]
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have := pi0NK_le (ρ := ρ) hσ hκ hu hT
  simp only [c]
  calc pi0NK σ κ ρ T u ≤ -u * (1 - lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) /
      (lamf ρ κ σ + lamb ρ κ σ)) := this
    _ = _ := by ring

/-- Cochrane (2023), §20.2.3, p. 477: for `ρ ≥ 0`, `λ^f/(λ^f + λ^b) ≥ 1/2`. -/
theorem half_le_weight {ρ κ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ) :
    1 / 2 ≤ lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  rw [div_le_div_iff₀ (by norm_num) hS]
  have := lamb_le_lamf (κ := κ) (σ := σ) hρ
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `e^{λ^b T} → ∞` as `κ → ∞` (`T > 0`). -/
theorem expLamb_tendsto_kappa {ρ σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun κ => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  Real.tendsto_exp_atTop.comp ((lamb_tendsto_atTop ρ hσ).atTop_mul_const hT)

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation gets worse without limit as prices become
less sticky"): in the `π_T = 0` equilibrium, every date `t ∈ [0, T)` of the trap has
`π_t → −∞` as `κ → ∞` (`ρ ≥ 0`, `u < 0`). -/
theorem nk_tendsto_kappa {σ ρ T u t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (htT : t < T) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 0 t) atTop atBot := by
  have hE := expLamb_tendsto_kappa (ρ := ρ) hσ (sub_pos.2 htT)
  have h1 : Tendsto (fun κ => -u - (-u / 2) * Real.exp (lamb ρ κ σ * (T - t))) atTop atBot := by
    have := hE.const_mul_atTop (by linarith : 0 < -u / 2)
    exact tendsto_atBot_add_const_left _ (-u) (tendsto_neg_atTop_atBot.comp this) |>.congr
      fun κ => by simp [sub_eq_add_neg]
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  rw [nk_pi_eq htT.le]
  have hh1 := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (T - t)
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * (T - t))
  have : Real.exp (lamb ρ κ σ * (T - t)) / 2 ≤ hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
    refine le_trans ?_ hh1
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: `π_0 → −∞` as `κ → ∞` in the `π_T = 0` equilibrium. -/
theorem pi0NK_tendsto_kappa {σ ρ T u : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (hT : 0 < T) :
    Tendsto (fun κ => pi0NK σ κ ρ T u) atTop atBot :=
  nk_tendsto_kappa hσ hρ hu hT

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation … become[s] larger as price stickiness is
reduced"): for `ρ ≥ 0`, `u < 0`, and every date `t ∈ [0, T)`, `π_t` in the `π_T = 0`
equilibrium is strictly decreasing in `κ`. -/
theorem nk_strictAnti_kappa {σ ρ T u t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (htT : t < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wPi σ κ' ρ T u 0 0 t < wPi σ κ ρ T u 0 0 t := by
  rw [nk_pi_eq htT.le, nk_pi_eq htT.le]
  have := hh_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: `π_0` in the `π_T = 0` equilibrium is strictly decreasing
in `κ`. -/
theorem pi0NK_strictAnti_kappa {σ ρ T u κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hκ : 0 < κ) (hlt : κ < κ') : pi0NK σ κ' ρ T u < pi0NK σ κ ρ T u :=
  nk_strictAnti_kappa hσ hρ hu hT hκ hlt

/-- Cochrane (2023), §20.2.3, p. 477 ("(not shown) output gaps become larger"): the time-0 output
gap of the `π_T = 0` equilibrium tends to `−∞` as `κ → ∞` (`ρ ≥ 0`, `u < 0`, `T > 0`). -/
theorem x0NK_tendsto_kappa {σ ρ T u : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (hT : 0 < T) :
    Tendsto (fun κ => wX σ κ ρ T u 0 0 0) atTop atBot := by
  -- `x_0 ≤ σ(−u)(1 − e^{λ^b T}/2)/λ^b ≤ −u σ T/2 … `: use `e^{y}/y → ∞`
  have hy : Tendsto (fun κ => lamb ρ κ σ * T) atTop atTop :=
    (lamb_tendsto_atTop ρ hσ).atTop_mul_const hT
  have hq : Tendsto (fun κ => Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) atTop atTop := by
    exact ((Real.tendsto_exp_div_pow_atTop 1).comp hy).congr fun κ => by simp
  have h1 : Tendsto (fun κ => σ * (-u) * T * ((1 : ℝ) - Real.exp (lamb ρ κ σ * T) /
      (lamb ρ κ σ * T) / 2)) atTop atBot := by
    have h2 : Tendsto (fun κ => (1 : ℝ) - Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T) / 2)
        atTop atBot := by
      have := (hq.atTop_div_const (by norm_num : (0 : ℝ) < 2))
      exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp this) |>.congr
        fun κ => by simp [sub_eq_add_neg]
    have hu' : 0 < -u := by linarith
    exact h2.const_mul_atBot (by positivity)
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0, hy.eventually_ge_atTop 1] with κ hκ hy1
  have hu' : 0 < -u := by linarith
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have e := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ hT.le
  rw [sub_zero] at e
  have hh1 := hh_ge hf hb T
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * T)
  have hF : 0 ≤ 1 - Real.exp (-(lamf ρ κ σ * T)) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
  have hhalf : Real.exp (lamb ρ κ σ * T) / 2 ≤ hh (lamf ρ κ σ) (lamb ρ κ σ) T := by
    refine le_trans ?_ hh1
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  -- `κ x_0 ≤ λ^f (−u)(1 − e^{λ^b T}/2)` and `λ^f/κ = σ/λ^b`
  have hx : κ * wX σ κ ρ T u 0 0 0 ≤ lamf ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
    rw [e]
    have : 0 ≤ lamb ρ κ σ * -u * (1 - Real.exp (-(lamf ρ κ σ * T))) :=
      mul_nonneg (mul_nonneg hb.le (by linarith)) hF
    have : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T)) ≤
        lamf ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hf.le; nlinarith
    linarith
  have hσl : lamf ρ κ σ / κ = σ / lamb ρ κ σ := by
    field_simp; linarith
  have hx' : wX σ κ ρ T u 0 0 0 ≤ σ / lamb ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
    rw [← hσl, div_mul_eq_mul_div, le_div_iff₀ hκ]
    linarith
  refine hx'.trans ?_
  have key : σ * -u * T * (1 - Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T) / 2) *
      lamb ρ κ σ = σ * -u * (lamb ρ κ σ * T - Real.exp (lamb ρ κ σ * T) / 2) := by
    field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ hb, key]
  have := mul_pos hσ hu'
  nlinarith

/-! ## The frictionless model (p. 477) -/

/-- Cochrane (2023), §20.2.3, p. 477: the frictionless (`κ = ∞`) model: the Phillips curve
divided by `κ` gives `x + g = 0` on `[0, ∞)`, and the IS curve (20.5) holds off `S`. -/
def IsFrictionless (σ : ℝ) (i u g : ℝ → ℝ) (S : Set ℝ) (x π : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → x t + g t = 0) ∧
    ∀ t, 0 < t → t ∉ S → HasDerivAt x (σ * (i t - π t - u t)) t

/-- Cochrane (2023), §20.2.3, p. 477: **the frictionless solution is unique**: with `σ ≠ 0`,
`(x, π)` solves the frictionless model of the experiment iff `x = −g` and `π = i − u_r = −u` on
`(0, T)`, `0` after `T` ("inflation simply jumps up to 2% … returning to 0 the minute the shock
ends"; no output gap when `g = 0`). -/
theorem frictionless_iff {σ T u g : ℝ} (hσ : σ ≠ 0) {x π : ℝ → ℝ} :
    IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ↔
      (∀ t, 0 ≤ t → x t = -trapStep g T t) ∧ ∀ t, 0 < t → t ≠ T → π t = -trapStep u T t := by
  have hloc : ∀ t, 0 < t → t ≠ T → ∀ x : ℝ → ℝ, (∀ s, 0 ≤ s → x s = -trapStep g T s) →
      HasDerivAt x 0 t := by
    intro t ht htT x hx
    rcases lt_or_gt_of_ne htT with h | h
    · have ev : (fun _ => -g) =ᶠ[𝓝 t] x := by
        filter_upwards [Ioo_mem_nhds ht h] with s hs
        rw [hx s hs.1.le]; simp [trapStep, hs.2]
      exact (hasDerivAt_const t (-g)).congr_of_eventuallyEq ev.symm
    · have ev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 t] x := by
        filter_upwards [Ioi_mem_nhds h, Ioi_mem_nhds ht] with s (hs : T < s) (hs0 : 0 < s)
        rw [hx s hs0.le]; simp [trapStep, not_lt.2 hs.le]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ev.symm
  constructor
  · rintro ⟨h1, h2⟩
    have hx : ∀ t, 0 ≤ t → x t = -trapStep g T t := fun t ht => by linarith [h1 t ht]
    refine ⟨hx, fun t ht htT => ?_⟩
    have := (h2 t ht htT).unique (hloc t ht htT x hx)
    have h0 : 0 - π t - trapStep u T t = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hσ
      · exact h
    linarith
  · rintro ⟨hx, hπ⟩
    refine ⟨fun t ht => by rw [hx t ht]; ring, fun t ht htT => ?_⟩
    refine (hloc t ht htT x hx).congr_deriv ?_
    rw [hπ t ht htT]
    ring

/-- Cochrane (2023), §20.2.3, p. 478 (**the puzzling discontinuity**): with `ρ ≥ 0`, `u < 0`, at
every date `t ∈ (0, T)` the `π_T = 0` inflation `π_t(κ)` does not converge, as `κ → ∞`, to the
frictionless value `−u` (it diverges to `−∞`), although the frictionless model is well behaved
(`frictionless_iff`). -/
theorem nk_discontinuity {σ ρ T u t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (htT : t < T) :
    ¬ Tendsto (fun κ => wPi σ κ ρ T u 0 0 t) atTop (𝓝 (-u)) := fun h =>
  not_tendsto_nhds_of_tendsto_atBot (nk_tendsto_kappa hσ hρ hu htT) (-u) h

/-! ## The `π_0 = 0` (no-jump) equilibrium -/

/-- Cochrane (2023), §20.2.2, p. 476: the end-of-trap inflation of the no-jump equilibrium,
`π_T = −u(h(T) − 1)e^{−λ^b T}`. -/
noncomputable def piTnj (σ κ ρ T u : ℝ) : ℝ :=
  -u * (hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1) * Real.exp (-(lamb ρ κ σ * T))

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump equilibrium has `π_0 = 0`. -/
theorem nj_pi0 {σ κ ρ T u : ℝ} (hT : 0 ≤ T) : wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) 0 = 0 := by
  simp only [wPi, hT, ↓reduceIte, trapPi, piTnj, sub_zero, zero_mul, mul_zero, add_zero]
  have : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * T) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-u * (hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1)) * this

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump path during the trap, for `0 ≤ t ≤ T`:
`π_t = −u[1 − e^{−λ^b t} − (λ^b/(λ^f+λ^b))(e^{−λ^f(T−t)} − e^{−λ^f T}e^{−λ^b t})]`. -/
theorem nj_formula {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t = -u * (1 - Real.exp (-(lamb ρ κ σ * t)) -
      lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (Real.exp (-(lamf ρ κ σ * (T - t))) -
        Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t)))) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [wPi, htT, ↓reduceIte, trapPi, piTnj, hh, zero_mul, mul_zero, add_zero]
  have e4 : Real.exp (lamb ρ κ σ * (T - t)) = Real.exp (lamb ρ κ σ * T) *
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  rw [e4, Real.exp_neg (lamb ρ κ σ * T)]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 476: the key inequality behind `0 < π_t` in the no-jump
equilibrium, `λ^f(1 − e^{−λ^b t}) > λ^b e^{−λ^b t}(1 − e^{−λ^f t})` for `t > 0`. -/
theorem nj_key {lf lb t : ℝ} (hf : 0 < lf) (hb : 0 < lb) (ht : 0 < t) :
    lb * Real.exp (-(lb * t)) * (1 - Real.exp (-(lf * t))) <
      lf * (1 - Real.exp (-(lb * t))) := by
  have hE : lb * t + 1 < Real.exp (lb * t) := Real.add_one_lt_exp (by positivity)
  have hG : -(lf * t) + 1 ≤ Real.exp (-(lf * t)) := Real.add_one_le_exp _
  have hinv : Real.exp (-(lb * t)) * Real.exp (lb * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (lb * t)
  have ha := Real.exp_pos (-(lb * t))
  -- multiply through by `e^{λ^b t}`
  have h1 : lb * (1 - Real.exp (-(lf * t))) < lf * (Real.exp (lb * t) - 1) := by
    have : lb * (1 - Real.exp (-(lf * t))) ≤ lb * (lf * t) :=
      mul_le_mul_of_nonneg_left (by linarith) hb.le
    have : lf * (lb * t) < lf * (Real.exp (lb * t) - 1) :=
      mul_lt_mul_of_pos_left (by linarith) hf
    nlinarith
  have h2 := mul_lt_mul_of_pos_left h1 ha
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476 ("the declining natural rate is met by a slight inflation
rise"): in the no-jump equilibrium inflation is positive at every `t > 0` (`u < 0`, `T > 0`). -/
theorem nj_pos {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T)
    (ht : 0 < t) : 0 < wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  -- the value on the trap
  have htrap : ∀ s, 0 < s → s ≤ T → 0 < wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) s := by
    intro s hs hsT
    rw [nj_formula hσ hκ hsT]
    have hkey := nj_key hf hb hs
    set a := Real.exp (-(lamb ρ κ σ * s))
    set c := Real.exp (-(lamf ρ κ σ * s))
    set b := Real.exp (-(lamf ρ κ σ * (T - s)))
    have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
      simp only [b, c]; rw [← Real.exp_add]; ring_nf
    have hb1 : b ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hb0 : 0 < b := Real.exp_pos _
    have ha0 : 0 < a := Real.exp_pos _
    have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hc0 : 0 < c := Real.exp_pos _
    have ha1 : a < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    rw [hH]
    have hac : 0 ≤ 1 - c * a := by nlinarith
    have : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) ≤
        lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (1 - c * a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have hfrac : 0 < 1 - a - lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (1 - c * a) := by
      rw [div_mul_eq_mul_div, sub_pos, div_lt_iff₀ hS]
      nlinarith
    have : 0 < 1 - a - lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by linarith
    have hu' : 0 < -u := by linarith
    positivity
  rcases le_or_gt t T with h | h
  · exact htrap t ht h
  · have hT' := htrap T hT le_rfl
    rw [wPi_T hκ hσ] at hT'
    simp only [wPi, not_le.2 h, ↓reduceIte]
    positivity

/-- Cochrane (2023), §20.2.2, p. 476: in the no-jump equilibrium inflation stays below the
frictionless value `−u` (`= 2%` in the book) at every `t ≥ 0`. -/
theorem nj_lt {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 ≤ T)
    (ht : 0 ≤ t) : wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t < -u := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have htrap : ∀ s, 0 ≤ s → s ≤ T → wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) s < -u := by
    intro s hs hsT
    rw [nj_formula hσ hκ hsT]
    set a := Real.exp (-(lamb ρ κ σ * s))
    set c := Real.exp (-(lamf ρ κ σ * s))
    set b := Real.exp (-(lamf ρ κ σ * (T - s)))
    have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
      simp only [b, c]; rw [← Real.exp_add]; ring_nf
    have hb0 : 0 < b := Real.exp_pos _
    have ha0 : 0 < a := Real.exp_pos _
    have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hc0 : 0 < c := Real.exp_pos _
    have ha1 : a ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    rw [hH]
    have : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by
      apply mul_nonneg (by positivity)
      have : c * a ≤ 1 := by nlinarith
      nlinarith
    have hu' : 0 < -u := by linarith
    nlinarith
  rcases le_or_gt t T with h | h
  · exact htrap t ht h
  · have hT' := htrap T hT le_rfl
    rw [wPi_T hκ hσ] at hT'
    simp only [wPi, not_le.2 h, ↓reduceIte]
    have hle : Real.exp (-(lamb ρ κ σ * (t - T))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h0 : 0 ≤ piTnj σ κ ρ T u := by
      rcases eq_or_lt_of_le hT with h0 | h0
      · subst h0
        simp [piTnj, hh_zero (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne']
      · have := nj_pos (ρ := ρ) hσ hκ hu h0 h0
        rw [wPi_T hκ hσ] at this
        exact this.le
    nlinarith [Real.exp_pos (-(lamb ρ κ σ * (t - T)))]

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump end-of-trap inflation satisfies
`0 < π_T < −u` (it is "only slightly higher" than in the `π_T = 0` equilibrium). -/
theorem piTnj_bounds {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T) :
    0 < piTnj σ κ ρ T u ∧ piTnj σ κ ρ T u < -u := by
  have h1 := nj_pos (ρ := ρ) hσ hκ hu hT hT
  have h2 := nj_lt (ρ := ρ) hσ hκ hu hT.le hT.le
  rw [wPi_T hκ hσ] at h1 h2
  exact ⟨h1, h2⟩

/-- Cochrane (2023), §20.2.2, p. 476: after the trap the no-jump inflation decays to zero. -/
theorem nj_tendsto_time {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun t => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 0) := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have h : Tendsto (fun t => piTnj σ κ ρ T u * Real.exp (-(lamb ρ κ σ * (t - T)))) atTop
      (𝓝 0) := by
    have := ((tendsto_expNeg hb).comp (tendsto_atTop_add_const_right atTop (-T) tendsto_id))
    have := this.const_mul (piTnj σ κ ρ T u)
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp [Function.comp, sub_eq_add_neg]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  simp [wPi, not_le.2 ht]

/-- Cochrane (2023), §20.2.3, p. 478: `e^{−λ^b c} → 0` and `e^{−λ^f c} → 0` as `κ → ∞`
(`c > 0`). -/
theorem expNeg_lam_tendsto {ρ σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    Tendsto (fun κ => Real.exp (-(lamb ρ κ σ * c))) atTop (𝓝 0) ∧
      Tendsto (fun κ => Real.exp (-(lamf ρ κ σ * c))) atTop (𝓝 0) :=
  ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp ((lamb_tendsto_atTop ρ hσ).atTop_mul_const hc),
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((lamf_tendsto_atTop ρ hσ).atTop_mul_const hc)⟩

/-- Cochrane (2023), §20.2.3, p. 478: during the trap, the no-jump inflation is within
`−u(e^{−λ^b t} + e^{−λ^f(T−t)})` of the frictionless value `−u`. -/
theorem nj_dist_trap {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t - -u| ≤
      -u * (Real.exp (-(lamb ρ κ σ * t)) + Real.exp (-(lamf ρ κ σ * (T - t)))) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  rw [nj_formula hσ hκ htT]
  set a := Real.exp (-(lamb ρ κ σ * t))
  set c := Real.exp (-(lamf ρ κ σ * t))
  set b := Real.exp (-(lamf ρ κ σ * (T - t)))
  have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
    simp only [b, c]; rw [← Real.exp_add]; ring_nf
  have hb0 : 0 < b := Real.exp_pos _
  have ha0 : 0 < a := Real.exp_pos _
  have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  have hc0 : 0 < c := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  rw [hH]
  have hα0 : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) := by positivity
  have hα1 : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) ≤ 1 := by
    rw [div_le_one hS]; linarith
  have hca : 0 ≤ 1 - c * a := by nlinarith
  have hm : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by
    apply mul_nonneg hα0; nlinarith
  have hM : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) ≤ b := by
    have : 0 ≤ b * c * a := by positivity
    have : b - b * c * a ≤ b := by linarith
    calc _ ≤ 1 * (b - b * c * a) := by
          apply mul_le_mul_of_nonneg_right hα1; nlinarith
      _ ≤ b := by linarith
  have hu' : 0 < -u := by linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- Cochrane (2023), §20.2.3, p. 478 ("inflation smoothly rises to fill out a square function,
2% inflation from `t = 0` to `t = T`"): at every `t ∈ (0, T)`, the no-jump inflation converges to
the frictionless value `−u` as `κ → ∞`. -/
theorem nj_limit_trap {σ ρ T u t : ℝ} (hσ : 0 < σ) (hu : u < 0) (ht : 0 < t) (htT : t < T) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 (-u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (expNeg_lam_tendsto (ρ := ρ) hσ ht).1
  have h2 := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 htT)).2
  have h3 := (h1.add h2).const_mul (-u)
  rw [add_zero, mul_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  exact nj_dist_trap hσ hκ hu ht.le htT.le

/-- Cochrane (2023), §20.2.3, p. 478 ("ε price stickiness implies δ deviation"): the
convergence to the frictionless square wave is uniform on every compact `[t₁, t₂] ⊂ (0, T)`. -/
theorem nj_uniform_trap {σ ρ T u t1 t2 : ℝ} (hσ : 0 < σ) (hu : u < 0) (h1 : 0 < t1)
    (h2 : t2 < T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ κ in atTop, ∀ t ∈ Set.Icc t1 t2,
      |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t - -u| < ε := by
  have ha := (expNeg_lam_tendsto (ρ := ρ) hσ h1).1
  have hb := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 h2)).2
  have h3 := (ha.add hb).const_mul (-u)
  rw [add_zero, mul_zero] at h3
  filter_upwards [eventually_gt_atTop 0, h3.eventually (gt_mem_nhds hε)] with κ hκ hlt t ht
  refine lt_of_le_of_lt (nj_dist_trap hσ hκ hu (by linarith [ht.1]) (by linarith [ht.2])) ?_
  have hb0 := lamb_pos (ρ := ρ) hκ hσ
  have hf0 := lamf_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (-(lamb ρ κ σ * t)) ≤ Real.exp (-(lamb ρ κ σ * t1)) :=
    Real.exp_le_exp.2 (by nlinarith [ht.1])
  have e2 : Real.exp (-(lamf ρ κ σ * (T - t))) ≤ Real.exp (-(lamf ρ κ σ * (T - t2))) :=
    Real.exp_le_exp.2 (by nlinarith [ht.2])
  have hu' : 0 < -u := by linarith
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 478: after the trap (`t > T`) the no-jump inflation converges to
the frictionless value `0` as `κ → ∞`, uniformly on `[t₃, ∞)` for every `t₃ > T`. -/
theorem nj_uniform_after {σ ρ T u t3 : ℝ} (hσ : 0 < σ) (hu : u < 0) (hT : 0 < T) (h3 : T < t3)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ κ in atTop, ∀ t, t3 ≤ t → |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t| < ε := by
  have ha := ((expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 h3)).1).const_mul (-u)
  rw [mul_zero] at ha
  filter_upwards [eventually_gt_atTop 0, ha.eventually (gt_mem_nhds hε)] with κ hκ hlt t ht
  have hb0 := lamb_pos (ρ := ρ) hκ hσ
  obtain ⟨p0, p1⟩ := piTnj_bounds (ρ := ρ) hσ hκ hu hT
  have htT : T < t := by linarith
  simp only [wPi, not_le.2 htT, ↓reduceIte]
  rw [abs_of_pos (by positivity)]
  have e1 : Real.exp (-(lamb ρ κ σ * (t - T))) ≤ Real.exp (-(lamb ρ κ σ * (t3 - T))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have := Real.exp_pos (-(lamb ρ κ σ * (t - T)))
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 478: pointwise after the trap, the no-jump inflation converges
to the frictionless value `0` as `κ → ∞`. -/
theorem nj_limit_after {σ ρ T u t : ℝ} (hσ : 0 < σ) (hu : u < 0) (hT : 0 < T) (ht : T < t) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [nj_uniform_after (ρ := ρ) hσ hu hT ht hε] with κ hκ
  rw [Real.dist_eq, sub_zero]
  exact hκ t le_rfl

/-! ## The fiscal reading of the time-0 jump (p. 476) -/

/-- Cochrane (2023), §20.2.2, p. 476 (and §5.7, (5.93)): the government debt valuation along a
path with `i = 0`: `v` continuous on `[0, ∞)`, `dv/dt = rv + (i − π) − s̃` on `(0, ∞)`, and the
transversality condition `e^{−rT}v_T → 0`. -/
def IsValuation (r : ℝ) (π s v : ℝ → ℝ) : Prop :=
  ContinuousOn v (Set.Ici 0) ∧ (∀ t, 0 < t → HasDerivAt v (r * v t + (0 - π t) - s t) t) ∧
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)

/-- Cochrane (2023), §20.2.2, p. 476 ("a fiscal theorist picks the equilibrium by the fiscal
innovation at time 0"): **the inflation jump is the fiscal innovation.** For two bounded
equilibria of the experiment with the same predetermined debt `v_0` (and integrable discounted
surpluses), `π_0 − π_0' = −(r + λ^b)(∫_0^∞ e^{−rτ}s̃_τ dτ − ∫_0^∞ e^{−rτ}s̃'_τ dτ)`. -/
theorem jump_eq_fiscal {σ κ ρ T u g r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 < r)
    {x π x' π' s s' v v' : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π)
    (h' : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x' π' ∧ BddOnIci x' ∧
      BddOnIci π')
    (hv : IsValuation r π s v) (hv' : IsValuation r π' s' v') (h0 : v 0 = v' 0)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0)) :
    π 0 - π' 0 = -(r + lamb ρ κ σ) * ((∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  -- the two inflation paths differ by `(π_0 − π_0') e^{−λ^b t}`
  have hdiff := homog_bdd hσ hκ ((Set.countable_singleton T).union (Set.countable_singleton T))
    (h.1.sub h'.1)
    (by obtain ⟨K1, h1⟩ := h.2.1; obtain ⟨K2, h2⟩ := h'.2.1
        exact ⟨K1 + K2, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h2 t ht))⟩)
    (by obtain ⟨K1, h1⟩ := h.2.2; obtain ⟨K2, h2⟩ := h'.2.2
        exact ⟨K1 + K2, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h2 t ht))⟩)
  -- integrability of the discounted inflation paths
  have hint : ∀ (p : ℝ → ℝ), ContinuousOn p (Set.Ici 0) → BddOnIci p →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * p τ) (Set.Ioi 0) := by
    intro p hp ⟨K, hK⟩
    exact integrableOn_exp_mul_of_bdd hr
      ((hp.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      fun τ hτ => hK τ hτ.le
  have iπ := hint π h.1.2.1 h.2.2
  have iπ' := hint π' h'.1.2.1 h'.2.2
  -- the valuation equation at `0`
  have val : ∀ (p q w : ℝ → ℝ), IsValuation r p q w →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * q τ) (Set.Ioi 0) →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * p τ) (Set.Ioi 0) →
      w 0 = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * q τ) +
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * p τ := by
    intro p q w ⟨hc, hd, htvc⟩ iq ip
    have hI : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (q τ + p τ)) (Set.Ioi 0) :=
      (iq.add ip).congr_fun (fun τ _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
    have := (tvc_iff_forward (f := fun τ => q τ + p τ) (t := 0) hc
      (fun τ hτ => (hd τ hτ).congr_deriv (by ring)) hI).1 htvc
    rw [this, ← integral_add iq ip]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    simp only [zero_add]
    ring
  have e1 := val π s v hv hs iπ
  have e2 := val π' s' v' hv' hs' iπ'
  -- `∫ e^{−rτ}(π − π') = (π_0 − π_0')/(r + λ^b)`
  have hpi : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π τ =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π' τ) + (π 0 - π' 0) / (r + lamb ρ κ σ) := by
    have hEq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * π τ)
        (fun τ => Real.exp (-(r * τ)) * π' τ +
          (π 0 - π' 0) * Real.exp (-((r + lamb ρ κ σ) * τ))) (Set.Ioi 0) := by
      intro τ hτ
      have := (hdiff τ (le_of_lt hτ)).1
      simp only at this ⊢
      have he : Real.exp (-((r + lamb ρ κ σ) * τ)) =
          Real.exp (-(r * τ)) * Real.exp (-(lamb ρ κ σ * τ)) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      linear_combination Real.exp (-(r * τ)) * this
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_add iπ'
      ((integrableOn_exp_Ioi (by linarith : 0 < r + lamb ρ κ σ)).const_mul _),
      integral_const_mul, integral_exp_Ioi (by linarith)]
    ring
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  rw [h0] at e1
  rw [e1, hpi] at e2
  have hq : (π 0 - π' 0) / (r + lamb ρ κ σ) = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ := by linarith
  rw [div_eq_iff hrb.ne'] at hq
  rw [hq]
  ring

/-- Cochrane (2023), §20.2.2, p. 476 ("the deflation jump must correspond to a large fiscal
contraction"): the extra present value of surpluses required by the `π_T = 0` equilibrium
relative to the no-jump equilibrium, `−π_0^{NK}/(r + λ^b)`. -/
noncomputable def fiscalContraction (σ κ ρ T u r : ℝ) : ℝ :=
  -pi0NK σ κ ρ T u / (r + lamb ρ κ σ)

/-- Cochrane (2023), §20.2.2, p. 476: **the `π_T = 0` equilibrium requires a fiscal
contraction**: with the same predetermined debt, the present value of surpluses in any
`π_T = 0` equilibrium exceeds that of any no-jump (`π_0 = 0`) equilibrium by
`fiscalContraction > 0` (`u < 0`, `T > 0`). -/
theorem nk_fiscal_contraction {σ κ ρ T u r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 < r)
    (hu : u < 0) (hT : 0 < T) {x π x' π' s s' v v' : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep 0 T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) (hNK : π T = 0)
    (h' : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep 0 T) {T} x' π' ∧ BddOnIci x' ∧
      BddOnIci π') (hNJ : π' 0 = 0)
    (hv : IsValuation r π s v) (hv' : IsValuation r π' s' v') (h0 : v 0 = v' 0)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0)) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
        (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) = fiscalContraction σ κ ρ T u r ∧
      0 < fiscalContraction σ κ ρ T u r := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  have hj := jump_eq_fiscal hσ hκ hr h h' hv hv' h0 hs hs'
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hπT0 : πT = 0 := by rw [← wPi_T hκ hσ T u 0 πT, ← (hπT T hT.le).1, hNK]
  have hπ0 : π 0 = pi0NK σ κ ρ T u := by rw [(hπT 0 le_rfl).1, hπT0, pi0NK]
  rw [hπ0, hNJ, sub_zero] at hj
  have hneg : pi0NK σ κ ρ T u < 0 := nk_pi_neg hσ hκ hu hT
  refine ⟨?_, div_pos (by linarith) hrb⟩
  rw [fiscalContraction, hj]
  field_simp

/-- Cochrane (2023), §20.2.2–20.2.3, pp. 476–477: the required fiscal contraction grows without
bound as prices become flexible (`ρ ≥ 0`, `u < 0`, `T > 0`). -/
theorem fiscalContraction_tendsto {σ ρ T u r : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hr : 0 < r) :
    Tendsto (fun κ => fiscalContraction σ κ ρ T u r) atTop atTop := by
  have hy : Tendsto (fun κ => lamb ρ κ σ * T) atTop atTop :=
    (lamb_tendsto_atTop ρ hσ).atTop_mul_const hT
  have hq : Tendsto (fun κ => Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) atTop atTop :=
    ((Real.tendsto_exp_div_pow_atTop 1).comp hy).congr fun κ => by simp
  have hu' : 0 < -u := by linarith
  -- `fiscalContraction ≥ (−u)(T/4) e^{λ^b T}/(λ^b T) − (−u)/r` once `λ^b ≥ r`
  have h1 : Tendsto (fun κ => -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) -
      -u / r) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hq.const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0, (lamb_tendsto_atTop ρ hσ).eventually_ge_atTop r]
    with κ hκ hbr
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  have hE0 := Real.exp_pos (lamb ρ κ σ * T)
  have hle := pi0NK_le (ρ := ρ) hσ hκ hu hT.le
  have hw := half_le_weight hρ hσ hκ
  have hhalf : Real.exp (lamb ρ κ σ * T) / 2 ≤
      lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ) := by
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  -- `−π_0 ≥ (−u)(e^{λ^b T}/2 − 1)`
  have hpi : -u * (Real.exp (lamb ρ κ σ * T) / 2 - 1) ≤ -pi0NK σ κ ρ T u := by nlinarith
  unfold fiscalContraction
  rw [le_div_iff₀ hrb]
  -- `(r + λ^b) ≤ 2λ^b`
  have key : (-u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) - -u / r) *
      (r + lamb ρ κ σ) ≤ -u * (Real.exp (lamb ρ κ σ * T) / 2 - 1) := by
    have e1 : -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) * lamb ρ κ σ =
        -u * Real.exp (lamb ρ κ σ * T) / 4 := by field_simp
    have e2 : -u / r * r = -u := by field_simp
    have hA : 0 ≤ -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) := by positivity
    have e3 : -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) * r ≤
        -u * Real.exp (lamb ρ κ σ * T) / 4 := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left hbr hA
    have hB : 0 ≤ -u / r * lamb ρ κ σ := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §20.2.2, p. 476 ("the forward-looking Phillips curve (20.6) only produces a
large output gap when inflation is lower today than in the future"): along a path, at a date
where (20.6) holds and `g_t = 0`, `x_t < 0` iff `dπ/dt > ρπ_t`. -/
theorem gap_neg_iff {σ ρ κ t : ℝ} (hκ : 0 < κ) {i u g x π : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (ht : 0 < t) (hS : t ∉ S) (hg : g t = 0) :
    x t < 0 ↔ ρ * π t < deriv π t := by
  rw [((h.2.2 t ht hS).2).deriv, hg, add_zero]
  constructor
  · intro hx; nlinarith
  · intro hx; nlinarith

/-! ## The output gap of the `π_T = 0` equilibrium is strictly decreasing in `κ` (p. 477) -/

/-- Cochrane (2023), §20.2.3, p. 477: the antiderivative of `h`,
`H(s) = [(λ^f/λ^b)(e^{λ^b s} − 1) + (λ^b/λ^f)(1 − e^{−λ^f s})]/(λ^f + λ^b) = ∫_0^s h`. -/
noncomputable def HH (lf lb s : ℝ) : ℝ :=
  (lf / lb * (Real.exp (lb * s) - 1) + lb / lf * (1 - Real.exp (-(lf * s)))) / (lf + lb)

/-- Cochrane (2023), §20.2.3, p. 477: `H(0) = 0`. -/
theorem HH_zero (lf lb : ℝ) : HH lf lb 0 = 0 := by
  simp [HH]

/-- Cochrane (2023), §20.2.3, p. 477: `H' = h`. -/
theorem HH_hasDerivAt {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) (s : ℝ) :
    HasDerivAt (HH lf lb) (hh lf lb s) s := by
  have := ((((hasDerivAt_expPos lb s).sub_const 1).const_mul (lf / lb)).add
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_expNeg lf s)).const_mul (lb / lf))).div_const
    (lf + lb)
  refine this.congr_deriv ?_
  simp only [hh]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (the IS curve integrated back from `x_T = 0`): during the
trap the `π_T = 0` output gap is `x_t = σ u H(T − t)`, i.e. `x_t = −σ(−u)∫_0^{T−t} h`. -/
theorem nk_x_eq_HH {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    wX σ κ ρ T u 0 0 t = σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have e := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ htT
  apply mul_left_cancel₀ hκ.ne'
  rw [e]
  have key : κ * (σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t)) =
      lamf ρ κ σ * lamb ρ κ σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
    rw [hmul]; ring
  rw [key]
  simp only [HH, hh]
  field_simp
  ring

/-- Cochrane (2023), §20.2.3, p. 477: for `ρ ≥ 0` and `s > 0`, `H(s)` is strictly increasing in
`κ` (because `h` is, at every date). -/
theorem HH_strictMono_kappa {ρ σ κ κ' s : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlt : κ < κ') (hs : 0 < s) :
    HH (lamf ρ κ σ) (lamb ρ κ σ) s < HH (lamf ρ κ' σ) (lamb ρ κ' σ) s := by
  have hκ' : 0 < κ' := by linarith
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf' := lamf_pos (ρ := ρ) hκ' hσ
  have hb' := lamb_pos (ρ := ρ) hκ' hσ
  have hd : ∀ r, HasDerivAt (fun r => HH (lamf ρ κ' σ) (lamb ρ κ' σ) r -
      HH (lamf ρ κ σ) (lamb ρ κ σ) r)
      (hh (lamf ρ κ' σ) (lamb ρ κ' σ) r - hh (lamf ρ κ σ) (lamb ρ κ σ) r) r := fun r =>
    (HH_hasDerivAt hf' hb' r).sub (HH_hasDerivAt hf hb r)
  have hmono : StrictMonoOn (fun r => HH (lamf ρ κ' σ) (lamb ρ κ' σ) r -
      HH (lamf ρ κ σ) (lamb ρ κ σ) r) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun r _ => (hd r).continuousAt.continuousWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    rw [(hd r).deriv]
    linarith [hh_strictMono_kappa hρ hσ hκ hlt hr (ρ := ρ)]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  simp only [HH_zero, sub_zero] at this
  linarith

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation and (not shown) output gaps become larger as
price stickiness is reduced"): **at every date `t ∈ [0, T)` of the trap, the output gap of the
`π_T = 0` equilibrium is strictly decreasing in `κ`** (`ρ ≥ 0`, `σ > 0`, `u < 0`). From `T` on it
is `0` for every `κ` (`nk_after`), so strictness holds exactly on the trap. -/
theorem nk_x_strictAnti_kappa {σ ρ T u t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (htT : t < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wX σ κ' ρ T u 0 0 t < wX σ κ ρ T u 0 0 t := by
  rw [nk_x_eq_HH hσ (by linarith) htT.le, nk_x_eq_HH hσ hκ htT.le]
  have h := HH_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)
  have hσu : σ * u < 0 := mul_neg_of_pos_of_neg hσ hu
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: in particular the time-0 output gap of the `π_T = 0`
equilibrium is strictly decreasing in `κ` (`T > 0`). -/
theorem x0NK_strictAnti_kappa {σ ρ T u κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wX σ κ' ρ T u 0 0 0 < wX σ κ ρ T u 0 0 0 :=
  nk_x_strictAnti_kappa hσ hρ hu hT hκ hlt

end Cochrane.ZeroBound.ZLBSelection

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Forward guidance at the zero bound

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4, pp. 478–480.

In the Werning experiment the equilibria are indexed by end-of-trap inflation `π_T`. Selecting
by `π_T` ("forward guidance" about inflation at `T`) gives promises enormous power.

## Main results

* `dpi0_dpiT`: across the family, `π_0 − π_0' = e^{λ^b T}(π_T − π_T')`; more generally
  `dpi_dpiT` at every date `t ≤ T`, `e^{λ^b(T−t)}`.
* `piTnj_eq`: the no-jump equilibrium has `π_T = −π_0^{NK} e^{−λ^b T}`, and `glide_path`: the
  required "glide path" `0 < π_T < −u` is bounded by the size of the shock, while the deflation
  it removes is unbounded (`pi0NK_tendsto_kappa`).
* "Promises further in the future matter more": `sensitivity_strictMono_T`,
  `sensitivity_tendsto_T`. "Less sticky ⇒ greater effect": `sensitivity_strictMono_kappa`,
  `sensitivity_tendsto_kappa`. "No effect at the limit point": `frictionless_unique`.
* Delayed lift-off (Woodford 2012, Werning 2012; p. 479): with a positive post-trap natural rate
  `u₂` and the rate held at zero until `L = T + τ`, the `π_L = 0` equilibrium `delayPi`
  (`delay_isPath`, `delay_bdd`, `delay_after`, `delay_unique`) has
  `π_0 = −u(1 − h(T)) + u₂(h(T+τ) − h(T))` (`delay_pi0`), strictly increasing in the delay
  (`delay_pi0_strictMono`) and unbounded (`delay_pi0_tendsto`): committing to delay the rate
  rise has the same power as promising time-`T` inflation.
-/

namespace Cochrane.ZeroBound.ForwardGuidance

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.ZLBSelection

/-! ## Sensitivity of `π_0` to `π_T` -/

/-- Cochrane (2023), §20.2.4, p. 479 ("inflation at time 0 is sensitive to its expectation at
time T"): at every date `t`, `π_t(π_T) − π_t(π_T') = e^{λ^b(T−t)}(π_T − π_T')`. -/
theorem dpi_dpiT (σ κ ρ T u g πT πT' t : ℝ) :
    wPi σ κ ρ T u g πT t - wPi σ κ ρ T u g πT' t =
      Real.exp (lamb ρ κ σ * (T - t)) * (πT - πT') := by
  rw [wPi_shift σ κ ρ T u g πT, wPi_shift σ κ ρ T u g πT']
  ring

/-- Cochrane (2023), §20.2.4, p. 479: **`π_0 − π_0' = e^{λ^b T}(π_T − π_T')`**. -/
theorem dpi0_dpiT (σ κ ρ T u g πT πT' : ℝ) :
    wPi σ κ ρ T u g πT 0 - wPi σ κ ρ T u g πT' 0 =
      Real.exp (lamb ρ κ σ * T) * (πT - πT') := by
  rw [dpi_dpiT, sub_zero]

/-- Cochrane (2023), §20.2.4, p. 479: `π_0` is an affine function of the promise `π_T` with
derivative `e^{λ^b T}` (an exact derivative). -/
theorem hasDerivAt_pi0_piT (σ κ ρ T u g πT : ℝ) :
    HasDerivAt (fun p => wPi σ κ ρ T u g p 0) (Real.exp (lamb ρ κ σ * T)) πT := by
  have h : (fun p => wPi σ κ ρ T u g p 0) =
      fun p => wPi σ κ ρ T u g 0 0 + p * Real.exp (lamb ρ κ σ * (T - 0)) :=
    funext fun p => wPi_shift σ κ ρ T u g p 0
  rw [h, sub_zero]
  exact ((hasDerivAt_id πT).mul_const _).const_add _ |>.congr_deriv (by simp)

/-- Cochrane (2023), §20.2.4, p. 479: the no-jump equilibrium's end-of-trap inflation is
`π_T = −π_0^{NK} e^{−λ^b T}`. -/
theorem piTnj_eq {σ κ ρ T u : ℝ} (hT : 0 ≤ T) :
    piTnj σ κ ρ T u = -pi0NK σ κ ρ T u * Real.exp (-(lamb ρ κ σ * T)) := by
  rw [pi0NK_eq hT, piTnj]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 ("if only the central bank could allow a small amount of
time-T inflation, a glide path back to its target, then the huge deflation … would be solved"):
the glide path that removes the deflation jump satisfies `0 < π_T < −u` for every `κ` and `T`
(bounded by the size of the shock), although the deflation it removes is unbounded
(`pi0NK_tendsto_kappa`, `pi0NK_tendsto_T`). -/
theorem glide_path {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T) :
    0 < piTnj σ κ ρ T u ∧ piTnj σ κ ρ T u < -u ∧ wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) 0 = 0 :=
  ⟨(piTnj_bounds hσ hκ hu hT).1, (piTnj_bounds hσ hκ hu hT).2, nj_pi0 hT.le⟩

/-- Cochrane (2023), §20.2.4, p. 479 ("promises about actions further in the future have greater
effects today"): the sensitivity `e^{λ^b T}` is strictly increasing in the horizon `T`. -/
theorem sensitivity_strictMono_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono fun T => Real.exp (lamb ρ κ σ * T) := fun _ _ h =>
  Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left h (lamb_pos hκ hσ))

/-- Cochrane (2023), §20.2.4, p. 479: the sensitivity `e^{λ^b T}` is unbounded in `T`. -/
theorem sensitivity_tendsto_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun T => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  tendsto_expPos (lamb_pos hκ hσ)

/-- Cochrane (2023), §20.2.4, p. 479 ("as prices become less sticky … forward guidance has
greater and greater effect"): the sensitivity is strictly increasing in `κ` (`T > 0`). -/
theorem sensitivity_strictMono_kappa {σ ρ T κ κ' : ℝ} (hσ : 0 < σ) (hT : 0 < T) (hκ : 0 < κ)
    (hlt : κ < κ') : Real.exp (lamb ρ κ σ * T) < Real.exp (lamb ρ κ' σ * T) :=
  Real.exp_lt_exp.2 (mul_lt_mul_of_pos_right (lamb_strictMono hσ hκ hlt) hT)

/-- Cochrane (2023), §20.2.4, p. 479: the sensitivity is unbounded as `κ → ∞` (`T > 0`). -/
theorem sensitivity_tendsto_kappa {σ ρ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun κ => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  expLamb_tendsto_kappa hσ hT

/-- Cochrane (2023), §20.2.4, p. 479 ("until all of a sudden at the flexible-price limit point,
forward guidance has no effect at all"): in the frictionless model there is no free constant —
any two solutions coincide (`x` on `[0, ∞)`, `π` off the date `T`), so nothing announced about
`π_T` or later can move `π_0`. -/
theorem frictionless_unique {σ T u g : ℝ} (hσ : σ ≠ 0) {x π x' π' : ℝ → ℝ}
    (h : IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π)
    (h' : IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x' π') :
    (∀ t, 0 ≤ t → x t = x' t) ∧ ∀ t, 0 < t → t ≠ T → π t = π' t := by
  obtain ⟨a, b⟩ := (frictionless_iff hσ).1 h
  obtain ⟨a', b'⟩ := (frictionless_iff hσ).1 h'
  exact ⟨fun t ht => by rw [a t ht, a' t ht], fun t ht htT => by rw [b t ht htT, b' t ht htT]⟩

/-! ## Delayed lift-off (p. 479) -/

/-- Cochrane (2023), (20.5)–(20.6): the model depends on `i` and `u_r` only through `i − u_r`. -/
theorem isPath_congr_forcing {σ ρ κ : ℝ} {i u g i' u' g' x π : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (hiu : ∀ t, 0 < t → t ∉ S → i t - u t = i' t - u' t)
    (hg : ∀ t, 0 < t → t ∉ S → g t = g' t) : IsPath σ ρ κ i' u' g' S x π := by
  refine ⟨h.1, h.2.1, fun t ht hS => ?_⟩
  obtain ⟨a, b⟩ := h.2.2 t ht hS
  refine ⟨a.congr_deriv ?_, b.congr_deriv ?_⟩
  · have := hiu t ht hS
    linear_combination σ * this
  · rw [hg t ht hS]

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off interest rate: `0` until `L`, then
the post-trap natural rate `u₂`. -/
noncomputable def delayI (u2 L t : ℝ) : ℝ := if t < L then 0 else u2

/-- Cochrane (2023), §20.2.4, p. 479: the natural rate: `u` during the trap, `u₂` afterwards. -/
noncomputable def delayU (u u2 T t : ℝ) : ℝ := if t < T then u else u2

/-- Cochrane (2023), §20.2.4, p. 479: the `π_L = 0` inflation path under delayed lift-off,
the superposition of a trap of length `T` with forcing `u₂ − u` and one of length `L` with
forcing `−u₂`. -/
noncomputable def delayPi (σ κ ρ T L u u2 t : ℝ) : ℝ :=
  wPi σ κ ρ T (u - u2) 0 0 t + wPi σ κ ρ L u2 0 0 t

/-- Cochrane (2023), §20.2.4, p. 479: the corresponding output gap. -/
noncomputable def delayX (σ κ ρ T L u u2 t : ℝ) : ℝ :=
  wX σ κ ρ T (u - u2) 0 0 t + wX σ κ ρ L u2 0 0 t

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off path solves (20.5)–(20.6) with
`i = delayI`, `u_r = delayU`, `g = 0` (off `{T, L}`). -/
theorem delay_isPath {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    IsPath σ ρ κ (delayI u2 L) (delayU u u2 T) (fun _ => 0) ({T} ∪ {L})
      (delayX σ κ ρ T L u u2) (delayPi σ κ ρ T L u u2) := by
  have h := (wPath_isPath (ρ := ρ) hκ hσ T (u - u2) 0 0).add
    (wPath_isPath (ρ := ρ) hκ hσ L u2 0 0)
  refine isPath_congr_forcing h (fun t _ _ => ?_) (fun t _ _ => by simp [trapStep])
  simp only [delayI, delayU, trapStep]
  split_ifs <;> ring

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off path is bounded. -/
theorem delay_bdd {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    BddOnIci (delayX σ κ ρ T L u u2) ∧ BddOnIci (delayPi σ κ ρ T L u u2) := by
  obtain ⟨⟨K1, h1⟩, ⟨K2, h2⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T (u - u2) 0 0
  obtain ⟨⟨K3, h3⟩, ⟨K4, h4⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ L u2 0 0
  exact ⟨⟨K1 + K3, fun t ht => (abs_add_le _ _).trans (add_le_add (h1 t ht) (h3 t ht))⟩,
    ⟨K2 + K4, fun t ht => (abs_add_le _ _).trans (add_le_add (h2 t ht) (h4 t ht))⟩⟩

/-- Cochrane (2023), §20.2.4, p. 479: inflation and output are zero from lift-off on. -/
theorem delay_after {σ κ ρ T L u u2 t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hTL : T ≤ L)
    (ht : L ≤ t) : delayPi σ κ ρ T L u u2 t = 0 ∧ delayX σ κ ρ T L u u2 t = 0 := by
  obtain ⟨a1, b1⟩ := nk_after (ρ := ρ) (u := u - u2) hσ hκ (le_trans hTL ht)
  obtain ⟨a2, b2⟩ := nk_after (ρ := ρ) (u := u2) hσ hκ ht
  simp only [delayPi, delayX, a1, b1, a2, b2, add_zero, and_self]

/-- Cochrane (2023), §20.2.4, p. 479: **uniqueness of the `π_L = 0` equilibrium under delayed
lift-off**: any bounded path of the delayed experiment with `π_L = 0` is `delayPi`. -/
theorem delay_unique {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hTL : T ≤ L)
    (hL : 0 ≤ L) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (delayI u2 L) (delayU u u2 T) (fun _ => 0) ({T} ∪ {L}) x π)
    (hx : BddOnIci x) (hπ : BddOnIci π) (hπL : π L = 0) :
    ∀ t, 0 ≤ t → π t = delayPi σ κ ρ T L u u2 t ∧ x t = delayX σ κ ρ T L u u2 t := by
  obtain ⟨⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩ := (⟨hx, hπ⟩ : BddOnIci x ∧ BddOnIci π)
  obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := delay_bdd (ρ := ρ) (T := T) (L := L) (u := u)
    (u2 := u2) hσ hκ
  have hS : ({T} ∪ {L} ∪ ({T} ∪ {L}) : Set ℝ).Countable :=
    ((Set.countable_singleton T).union (Set.countable_singleton L)).union
      ((Set.countable_singleton T).union (Set.countable_singleton L))
  have hh := homog_bdd hσ hκ hS (h.sub (delay_isPath (ρ := ρ) hσ hκ))
    ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
    ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
  have hc : π 0 - delayPi σ κ ρ T L u u2 0 = 0 := by
    have := (hh L hL).1
    rw [hπL, (delay_after (ρ := ρ) (u := u) (u2 := u2) hσ hκ hTL le_rfl).1, sub_zero] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  intro t ht
  obtain ⟨h1, h2⟩ := hh t ht
  rw [hc, mul_zero] at h1
  have h1' : π t = delayPi σ κ ρ T L u u2 t := by linarith
  refine ⟨h1', ?_⟩
  rw [h1', sub_self, mul_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hκ.ne'
  · linarith

/-- Cochrane (2023), §20.2.4, p. 479: initial inflation under delayed lift-off,
`π_0 = −u(1 − h(T)) + u₂(h(L) − h(T))`. -/
theorem delay_pi0 {σ κ ρ T L u u2 : ℝ} (hT : 0 ≤ T) (hTL : T ≤ L) :
    delayPi σ κ ρ T L u u2 0 = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) +
      u2 * (hh (lamf ρ κ σ) (lamb ρ κ σ) L - hh (lamf ρ κ σ) (lamb ρ κ σ) T) := by
  rw [delayPi, nk_pi_eq hT, nk_pi_eq (le_trans hT hTL), sub_zero, sub_zero]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 ("a policy that commits to delaying an interest-rate rise …
has the same effect"): with a positive post-trap natural rate `u₂ > 0`, initial inflation is
strictly increasing in the delay `τ ≥ 0` (lift-off at `T + τ`). -/
theorem delay_pi0_strictMono {σ κ ρ T u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    (hu2 : 0 < u2) :
    StrictMonoOn (fun τ => delayPi σ κ ρ T (T + τ) u u2 0) (Set.Ici 0) := by
  intro τ1 h1 τ2 h2 hlt
  simp only
  rw [delay_pi0 hT (by linarith [Set.mem_Ici.1 h1]),
    delay_pi0 hT (by linarith [Set.mem_Ici.1 h2])]
  have := hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ)
    (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 h1] : (0 : ℝ) ≤ T + τ1))
    (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 h2] : (0 : ℝ) ≤ T + τ2))
    (by linarith : T + τ1 < T + τ2)
  nlinarith

/-- Cochrane (2023), §20.2.4, p. 479: with no delay the `π_L = 0` equilibrium is the standard
`π_T = 0` one: `π_0 = π_0^{NK}`. -/
theorem delay_zero {σ κ ρ T u u2 : ℝ} (hT : 0 ≤ T) :
    delayPi σ κ ρ T (T + 0) u u2 0 = pi0NK σ κ ρ T u := by
  rw [delay_pi0 hT (by linarith), add_zero, pi0NK_eq hT]
  ring

/-- Cochrane (2023), §20.2.4, p. 479: a long enough delay produces any initial inflation:
`π_0 → ∞` as the delay `τ → ∞` (`u₂ > 0`). -/
theorem delay_pi0_tendsto {σ κ ρ T u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    (hu2 : 0 < u2) : Tendsto (fun τ => delayPi σ κ ρ T (T + τ) u u2 0) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  set c0 := -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) -
    u2 * hh (lamf ρ κ σ) (lamb ρ κ σ) T
  have hE : Tendsto (fun τ => u2 * (lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ)) *
      Real.exp (lamb ρ κ σ * (T + τ))) atTop atTop := by
    have : Tendsto (fun τ => Real.exp (lamb ρ κ σ * (T + τ))) atTop atTop :=
      Real.tendsto_exp_atTop.comp ((tendsto_atTop_add_const_left atTop T tendsto_id).const_mul_atTop
        hb)
    exact this.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop c0 hE)
  filter_upwards [eventually_ge_atTop 0] with τ hτ
  rw [delay_pi0 hT (by linarith)]
  have := hh_ge hf hb (T + τ)
  have e : lamf ρ κ σ * Real.exp (lamb ρ κ σ * (T + τ)) / (lamf ρ κ σ + lamb ρ κ σ) =
      lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * Real.exp (lamb ρ κ σ * (T + τ)) := by ring
  rw [e] at this
  simp only [c0]
  nlinarith

end Cochrane.ZeroBound.ForwardGuidance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Magical multipliers and Bastiat banished

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.5, pp. 480–482.

A Phillips-curve disturbance `g` (government spending, or deliberate cost increases) is `g` on
the trap `[0, T)` and `0` afterwards. The multiplier is `∂x_t/∂g` at `g = 0`.

## Main results

* The IS curve solved forward (p. 480): `is_forward` (any path with `x_T → 0` and an
  integrable real-rate gap) and `experiment_is_forward` (every bounded path of the experiment):
  `x_t = −∫_0^∞ σ(i_{t+s} − u_{r,t+s} − π_{t+s}) ds`.
* Output is affine in `g` (`xNK_affine`, `xNJ_affine`), with exact derivatives
  `hasDerivAt_xNK`, `hasDerivAt_xNJ` — the multipliers `multNK` (standard, `π_T = 0`) and
  `multNJ` (no-jump, `π_0 = 0`).
* Standard multipliers (p. 481): `multNK_pos`; `multNK_tendsto_kappa` (→ ∞ as prices become
  flexible), `multNK_strictMono_kappa` (increasing as `κ` rises); `multNK0_strictMonoOn_T`,
  `multNK0_ge` (exponential lower bound), `multNK0_tendsto_T`, `multNK0_gt_one_eventually`
  (`> 1` for long traps). **E20**: the book's "substantially greater than one" fails for short
  traps — `multNK0_lt_one_short` (`< 1` for all small `T`) and the numerical counterexample
  `e20_counterexample` (`0 < m₀ < 1` at `κ = σ = 1`, `ρ = 0.05`, `T = 1`).
* The limit point (p. 481): `frictionless_multiplier` (`x = −g`, multiplier `−1`).
* No-jump multipliers (p. 481): `multNJ_formula`, `multNJ_bounds` (`−1 < m < 0` during the
  trap: small, near the frictionless value), `multNJ_tendsto_kappa`, `multNJ_tendsto_T`
  (→ `−1`).
* "Spending in the future is exponentially more effective" (p. 481, not shown in the book):
  `window_isPath`, `window_unique`, `window_x0`, `windowMult_strictMono`, `windowMult_tendsto`.
-/

namespace Cochrane.ZeroBound.Multipliers

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.ZLBSelection

/-! ## The IS curve solved forward (p. 480) -/

/-- Cochrane (2023), §20.2.5, p. 480: **the IS equation (20.5) solved forward.** Along a path
(differentiable off a countable set), if `x_T → 0` and the real-rate gap `i − u_r − π` is
integrable on `(t, ∞)` (`t ≥ 0`), then `x_t = −∫_0^∞ σ(i_{t+s} − u_{r,t+s} − π_{t+s}) ds`. -/
theorem is_forward {σ ρ κ t : ℝ} {i u g x π : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (h : IsPath σ ρ κ i u g S x π) (ht : 0 ≤ t) (hx : Tendsto x atTop (𝓝 0))
    (hint : IntegrableOn (fun s => i s - u s - π s) (Set.Ioi t)) :
    x t = -∫ s in Set.Ioi 0, σ * (i (t + s) - u (t + s) - π (t + s)) := by
  have hf : IntegrableOn (fun s => σ * (i s - π s - u s)) (Set.Ioi t) :=
    IntegrableOn.congr_fun (hint.const_mul σ) (fun s _ => by ring) measurableSet_Ioi
  have hftc : ∀ b, t ≤ b → ∫ s in t..b, σ * (i s - π s - u s) = x b - x t := fun b hb =>
    integral_eq_of_hasDerivAt_off_countable_of_le x _ hb hS
      (h.1.mono fun s hs => le_trans ht hs.1)
      (fun s hs => (h.2.2 s (by linarith [hs.1.1]) hs.2).1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2
        (hf.mono_set Set.Ioc_subset_Ioi_self))
  have hlim := intervalIntegral_tendsto_integral_Ioi t hf tendsto_id
  have hlim2 : Tendsto (fun b => x b - x t) atTop
      (𝓝 (∫ s in Set.Ioi t, σ * (i s - π s - u s))) :=
    hlim.congr' (by filter_upwards [eventually_ge_atTop t] with b hb; exact hftc b hb)
  have hlim3 := hx.sub_const (x t)
  have := tendsto_nhds_unique hlim3 hlim2
  rw [← integral_Ioi_shift] at this
  have e : ∫ s in Set.Ioi 0, σ * (i (t + s) - π (t + s) - u (t + s)) =
      ∫ s in Set.Ioi 0, σ * (i (t + s) - u (t + s) - π (t + s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [← e]
  linarith

/-- Cochrane (2023), §20.2.5, p. 480: the natural-rate step `trapStep u T` is integrable on
every `(t, ∞)`. -/
theorem trapStep_integrableOn (u T t : ℝ) : IntegrableOn (trapStep u T) (Set.Ioi t) := by
  have hind : trapStep u T = (Set.Iio T).indicator fun _ => u := by
    funext s
    by_cases hs : s < T <;> simp [trapStep, hs, Set.indicator]
  rw [hind, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  exact integrableOn_const (by simp)

/-- Cochrane (2023), §20.2.5, p. 480: **the forward IS solution holds along every bounded path of
the experiment** (for every `t ≥ 0`). -/
theorem experiment_is_forward {σ κ ρ T u g t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t)
    {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    x t = -∫ s in Set.Ioi 0, σ * (0 - trapStep u T (t + s) - π (t + s)) := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hb := lamb_pos (ρ := ρ) hκ hσ
  obtain ⟨K, hK⟩ := h.2.2
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 le_rfl)
  -- `|π_s| ≤ M e^{−λ^b s}` on `[0, ∞)`
  set M := (K + |πT|) * Real.exp (lamb ρ κ σ * T)
  have hbound : ∀ s, 0 ≤ s → |π s| ≤ M * Real.exp (-(lamb ρ κ σ * s)) := by
    intro s hs
    have e : M * Real.exp (-(lamb ρ κ σ * s)) =
        (K + |πT|) * Real.exp (lamb ρ κ σ * (T - s)) := by
      simp only [M]; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    rcases le_or_gt s T with hsT | hsT
    · have : 1 ≤ Real.exp (lamb ρ κ σ * (T - s)) := Real.one_le_exp (by nlinarith)
      nlinarith [hK s hs, abs_nonneg πT]
    · rw [(hπT s hs).1]
      simp only [wPi, not_le.2 hsT, ↓reduceIte]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have : -(lamb ρ κ σ * (s - T)) = lamb ρ κ σ * (T - s) := by ring
      rw [this]
      nlinarith [Real.exp_pos (lamb ρ κ σ * (T - s))]
  have hπint : IntegrableOn π (Set.Ioi t) := by
    have hdom := (integrableOn_exp_mul_Ioi (a := -lamb ρ κ σ) (by linarith) t).const_mul M
    refine Integrable.mono' hdom
      ((h.1.2.1.mono fun s (hs : t < s) => (show (0 : ℝ) ≤ s by linarith :
        s ∈ Set.Ici (0 : ℝ))).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s (hs : t < s) => ?_))
    rw [Real.norm_eq_abs, neg_mul]
    exact hbound s (by linarith)
  have hint : IntegrableOn (fun s => (fun _ => (0 : ℝ)) s - trapStep u T s - π s)
      (Set.Ioi t) := by
    have := (trapStep_integrableOn u T t).neg.sub hπint
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have hx : Tendsto x atTop (𝓝 0) := by
    have hl : Tendsto (fun s => lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (s - T)))) / κ)
        atTop (𝓝 0) := by
      have := ((tendsto_expNeg hb).comp (tendsto_atTop_add_const_right atTop (-T) tendsto_id))
      have := ((this.const_mul πT).const_mul (lamf ρ κ σ)).div_const κ
      simp only [mul_zero, zero_div] at this
      refine this.congr fun s => ?_
      simp [Function.comp, sub_eq_add_neg]
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop T, eventually_ge_atTop 0] with s hs hs0
    rw [(hπT s hs0).2]
    simp [wX, not_le.2 hs]
  exact is_forward (Set.countable_singleton T) h.1 ht hx hint

/-! ## Multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the output gap in the standard (`π_T = 0`) equilibrium
with Phillips-curve disturbance `g` during the trap. -/
noncomputable def xNK (σ κ ρ T u g t : ℝ) : ℝ := wX σ κ ρ T u g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: end-of-trap inflation of the no-jump (`π_0 = 0`)
equilibrium with disturbance `g`. -/
noncomputable def piTnjg (σ κ ρ T u g : ℝ) : ℝ :=
  -(-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) + κ * g * kk (lamf ρ κ σ) (lamb ρ κ σ) T) *
    Real.exp (-(lamb ρ κ σ * T))

/-- Cochrane (2023), §20.2.5, p. 481: the output gap in the no-jump equilibrium with
disturbance `g`. -/
noncomputable def xNJ (σ κ ρ T u g t : ℝ) : ℝ := wX σ κ ρ T u g (piTnjg σ κ ρ T u g) t

/-- Cochrane (2023), §20.2.5, p. 481: the standard multiplier `∂x_t/∂g`:
`h(T − t) − 1` during the trap and `0` afterwards. -/
noncomputable def multNK (σ κ ρ T t : ℝ) : ℝ :=
  if t ≤ T then hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t) - 1 else 0

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier `∂x_t/∂g`:
the standard one minus `λ^f k(T) e^{−λ^b t}`. -/
noncomputable def multNJ (σ κ ρ T t : ℝ) : ℝ :=
  multNK σ κ ρ T t - lamf ρ κ σ * kk (lamf ρ κ σ) (lamb ρ κ σ) T * Real.exp (-(lamb ρ κ σ * t))

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump selection with disturbance `g` has `π_0 = 0`. -/
theorem nj_g_pi0 {σ κ ρ T u g : ℝ} (hT : 0 ≤ T) :
    wPi σ κ ρ T u g (piTnjg σ κ ρ T u g) 0 = 0 := by
  simp only [wPi, hT, ↓reduceIte, trapPi, piTnjg, sub_zero]
  have : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * T) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-(-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) +
    κ * g * kk (lamf ρ κ σ) (lamb ρ κ σ) T)) * this

/-- Cochrane (2023), §20.2.5, p. 481: in the standard equilibrium output is affine in `g`,
`x_t(g) = x_t(0) + g · multNK_t`. -/
theorem xNK_affine {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g t : ℝ) :
    xNK σ κ ρ T u g t = xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  unfold xNK multNK wX
  split_ifs
  · simp only [trapPi, trapY, hh, kk]
    field_simp
    ring
  · simp

/-- Cochrane (2023), §20.2.5, p. 481: in the no-jump equilibrium output is affine in `g`,
`x_t(g) = x_t(0) + g · multNJ_t`. -/
theorem xNJ_affine {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g t : ℝ) :
    xNJ σ κ ρ T u g t = xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * (t - T))) =
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  unfold xNJ multNJ multNK wX piTnjg
  split_ifs
  · simp only [trapPi, trapY, hh, kk]
    rw [← e1]
    field_simp
    ring
  · rw [← e2]
    field_simp
    ring

/-- Cochrane (2023), §20.2.5, p. 481: **the standard multiplier is the exact derivative**
`∂x_t/∂g` (at any `g`, in particular at `g = 0`). -/
theorem hasDerivAt_xNK {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u t g0 : ℝ) :
    HasDerivAt (fun g => xNK σ κ ρ T u g t) (multNK σ κ ρ T t) g0 := by
  have h : (fun g => xNK σ κ ρ T u g t) =
      fun g => xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t :=
    funext fun g => xNK_affine hσ hκ T u g t
  rw [h]
  exact ((hasDerivAt_id g0).mul_const _).const_add _ |>.congr_deriv (by simp)

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier is the exact derivative
`∂x_t/∂g`. -/
theorem hasDerivAt_xNJ {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u t g0 : ℝ) :
    HasDerivAt (fun g => xNJ σ κ ρ T u g t) (multNJ σ κ ρ T t) g0 := by
  have h : (fun g => xNJ σ κ ρ T u g t) =
      fun g => xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t :=
    funext fun g => xNJ_affine hσ hκ T u g t
  rw [h]
  exact ((hasDerivAt_id g0).mul_const _).const_add _ |>.congr_deriv (by simp)

/-! ### Standard multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the standard multiplier is positive during the trap. -/
theorem multNK_pos {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t < T) :
    0 < multNK σ κ ρ T t := by
  simp only [multNK, htT.le, ↓reduceIte]
  linarith [one_lt_hh (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (sub_pos.2 htT)]

/-- Cochrane (2023), §20.2.5, p. 481 ("in the limit that price stickiness goes to zero, the
multiplier goes to infinity"): for `t < T` and `ρ ≥ 0`, `multNK_t → ∞` as `κ → ∞`. -/
theorem multNK_tendsto_kappa {σ ρ T t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (htT : t < T) :
    Tendsto (fun κ => multNK σ κ ρ T t) atTop atTop := by
  have hE := expLamb_tendsto_kappa (ρ := ρ) hσ (sub_pos.2 htT)
  have h1 : Tendsto (fun κ => Real.exp (lamb ρ κ σ * (T - t)) / 2 - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hE.atTop_div_const (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  simp only [multNK, htT.le, ↓reduceIte]
  have hh1 := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (T - t)
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * (T - t))
  have := mul_le_mul_of_nonneg_right hw hE0.le
  rw [mul_div_right_comm] at hh1
  linarith

/-- Cochrane (2023), §20.2.5, p. 481 ("multipliers increase as price stickiness is reduced"):
for `t < T` and `ρ ≥ 0`, `multNK_t` is strictly increasing in `κ`. -/
theorem multNK_strictMono_kappa {σ ρ T t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (htT : t < T)
    (hκ : 0 < κ) (hlt : κ < κ') : multNK σ κ ρ T t < multNK σ κ' ρ T t := by
  simp only [multNK, htT.le, ↓reduceIte]
  linarith [hh_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)]

/-- Cochrane (2023), §20.2.5, p. 481: the time-0 standard multiplier is `h(T) − 1`. -/
theorem multNK0_eq {σ κ ρ T : ℝ} (hT : 0 ≤ T) :
    multNK σ κ ρ T 0 = hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1 := by
  simp [multNK, hT]

/-- Cochrane (2023), §20.2.5, p. 481 ("the multipliers increase … as the length of the liquidity
trap increases"): `m_0(T)` is strictly increasing in `T ≥ 0`. -/
theorem multNK0_strictMonoOn_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMonoOn (fun T => multNK σ κ ρ T 0) (Set.Ici 0) := by
  intro T1 h1 T2 h2 hlt
  simp only
  rw [multNK0_eq h1, multNK0_eq h2]
  linarith [hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) h1 h2 hlt]

/-- Cochrane (2023), §20.2.5, p. 481 ("increase exponentially"): the exponential lower bound
`m_0(T) ≥ λ^f e^{λ^b T}/(λ^f + λ^b) − 1`. -/
theorem multNK0_ge {σ κ ρ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) :
    lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ) - 1 ≤
      multNK σ κ ρ T 0 := by
  rw [multNK0_eq hT]
  linarith [hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) T]

/-- Cochrane (2023), §20.2.5, p. 481: `m_0(T) → ∞` as the trap lengthens. -/
theorem multNK0_tendsto_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun T => multNK σ κ ρ T 0) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have h1 : Tendsto (fun T => lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) *
      Real.exp (lamb ρ κ σ * T) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_expPos (lamb_pos (ρ := ρ) hκ hσ)).const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have := multNK0_ge (ρ := ρ) hσ hκ hT
  rw [mul_div_right_comm] at this
  linarith

/-- Cochrane (2023), §20.2.5, p. 481: for long enough traps the standard multiplier exceeds
one. -/
theorem multNK0_gt_one_eventually {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ T0, ∀ T, T0 ≤ T → 1 < multNK σ κ ρ T 0 := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 ((multNK0_tendsto_T (ρ := ρ) hσ hκ).eventually_gt_atTop 1)
  exact ⟨T0, hT0⟩

/-- Cochrane (2023), §20.2.5, p. 481, **survey error E20** ("multipliers are large and
substantially greater than one" needs a long trap): for every `κ, σ > 0` there is `T₀ > 0` with
`0 < m_0(T) < 1` for all `T ∈ (0, T₀)`. -/
theorem multNK0_lt_one_short {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ T0, 0 < T0 ∧ ∀ T, 0 < T → T < T0 → 0 < multNK σ κ ρ T 0 ∧ multNK σ κ ρ T 0 < 1 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hc : ContinuousAt (hh (lamf ρ κ σ) (lamb ρ κ σ)) 0 :=
    (hh_hasDerivAt hne 0).continuousAt
  have hev : ∀ᶠ T in 𝓝 0, hh (lamf ρ κ σ) (lamb ρ κ σ) T < 2 := by
    have := hc.eventually (gt_mem_nhds (show hh (lamf ρ κ σ) (lamb ρ κ σ) 0 < 2 by
      rw [hh_zero hne]; norm_num))
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun T hT hTε => ⟨multNK_pos hσ hκ hT, ?_⟩⟩
  rw [multNK0_eq hT.le]
  have := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hT]; exact hTε)
  linarith

/-- Cochrane (2023), §20.2.5, p. 481, **E20 counterexample**: at `κ = σ = 1`, `ρ = 0.05` and a
trap of length `T = 1`, the standard time-0 multiplier satisfies `0 < m_0 < 1` (numerically
`0.53`). -/
theorem e20_counterexample :
    0 < multNK 1 1 (1 / 20) 1 0 ∧ multNK 1 1 (1 / 20) 1 0 < 1 := by
  refine ⟨multNK_pos one_pos one_pos one_pos, ?_⟩
  rw [multNK0_eq zero_le_one]
  set S := Real.sqrt ((1 / 20 : ℝ) ^ 2 + 4 * 1 * 1) with hSdef
  have hS2 : 2 < S := by
    rw [hSdef, Real.lt_sqrt (by norm_num)]; norm_num
  have hS3 : S < 2001 / 1000 := by
    rw [hSdef, Real.sqrt_lt' (by norm_num)]; norm_num
  have hf : lamf (1 / 20) 1 1 = (S + 1 / 20) / 2 := by simp only [lamf, hSdef]
  have hb : lamb (1 / 20) 1 1 = (S - 1 / 20) / 2 := by simp only [lamb, hSdef]
  have hsum : lamf (1 / 20) 1 1 + lamb (1 / 20) 1 1 = S := by rw [hf, hb]; ring
  have hlb1 : lamb (1 / 20) 1 1 * 1 ≤ 1 := by rw [hb]; linarith
  have he1 : Real.exp (lamb (1 / 20) 1 1 * 1) < 2.7182818286 :=
    lt_of_le_of_lt (Real.exp_le_exp.2 hlb1) Real.exp_one_lt_d9
  have he2 : Real.exp (-(lamf (1 / 20) 1 1 * 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff, hf]; linarith
  have hpf : 0 < lamf (1 / 20) 1 1 := by rw [hf]; linarith
  have hpb : 0 < lamb (1 / 20) 1 1 := by rw [hb]; linarith
  unfold hh
  rw [hsum, sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
  have : lamf (1 / 20) 1 1 * Real.exp (lamb (1 / 20) 1 1 * 1) ≤
      lamf (1 / 20) 1 1 * 2.7182818286 := mul_le_mul_of_nonneg_left he1.le hpf.le
  have : lamb (1 / 20) 1 1 * Real.exp (-(lamf (1 / 20) 1 1 * 1)) ≤ lamb (1 / 20) 1 1 :=
    by nlinarith
  rw [hf, hb] at *
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481 ("the multiplier is −1 at the limit point, since
`x_t = −g_t`"): in the frictionless model, for each `g` let `x_g` be a frictionless solution;
then `∂x_t/∂g = −1` during the trap (`0 ≤ t < T`). -/
theorem frictionless_multiplier {σ T u t g0 : ℝ} (hσ : σ ≠ 0) (ht : 0 ≤ t) (htT : t < T)
    {X P : ℝ → ℝ → ℝ}
    (h : ∀ g, IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} (X g) (P g)) :
    HasDerivAt (fun g => X g t) (-1) g0 := by
  have e : (fun g => X g t) = fun g => -g := funext fun g => by
    rw [((frictionless_iff hσ).1 (h g)).1 t ht]
    simp [trapStep, htT]
  rw [e]
  exact (hasDerivAt_id g0).neg

/-! ### No-jump multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier during the trap,
`m_t = −1 + (λ^b e^{−λ^f(T−t)} + λ^f e^{−λ^f T}e^{−λ^b t})/(λ^f + λ^b)`. -/
theorem multNJ_formula {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    multNJ σ κ ρ T t = -1 + (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  simp only [multNJ, multNK, htT, ↓reduceIte, hh, kk]
  rw [e1]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481 ("the multiplier in the no-jump equilibrium is small, and
clustered around the frictionless value −1"): `−1 < m_t < 0` throughout the trap. -/
theorem multNJ_bounds {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 < T) (ht : 0 ≤ t)
    (htT : t ≤ T) : -1 < multNJ σ κ ρ T t ∧ multNJ σ κ ρ T t < 0 := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  rw [multNJ_formula hσ hκ htT]
  have b1 : Real.exp (-(lamf ρ κ σ * (T - t))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have b2 : Real.exp (-(lamf ρ κ σ * T)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have b3 : Real.exp (-(lamb ρ κ σ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have p1 := Real.exp_pos (-(lamf ρ κ σ * (T - t)))
  have p2 := Real.exp_pos (-(lamf ρ κ σ * T))
  have p3 := Real.exp_pos (-(lamb ρ κ σ * t))
  have hpos : 0 < (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by positivity
  have hlt : (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) < 1 := by
    rw [div_lt_one hS]
    have : Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t)) < 1 := by nlinarith
    nlinarith
  constructor <;> linarith

/-- Cochrane (2023), §20.2.5, p. 481: `|m_t + 1| ≤ e^{−λ^f(T−t)} + e^{−λ^f T}` during the trap
(no-jump multiplier). -/
theorem multNJ_dist {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t) (htT : t ≤ T) :
    |multNJ σ κ ρ T t - -1| ≤
      Real.exp (-(lamf ρ κ σ * (T - t))) + Real.exp (-(lamf ρ κ σ * T)) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e : multNJ σ κ ρ T t - -1 = (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by
    rw [multNJ_formula hσ hκ htT]; ring
  rw [e]
  have b3 : Real.exp (-(lamb ρ κ σ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have p1 := Real.exp_pos (-(lamf ρ κ σ * (T - t)))
  have p2 := Real.exp_pos (-(lamf ρ κ σ * T))
  have p3 := Real.exp_pos (-(lamb ρ κ σ * t))
  rw [abs_of_pos (by positivity), div_le_iff₀ hS]
  have q1 := mul_le_mul_of_nonneg_left b3 (mul_pos hf p2).le
  have q2 := mul_pos hf p1
  have q3 := mul_pos hb p2
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481 ("as price-stickiness is reduced … the no-jump equilibrium
multipliers converge smoothly to −1"): for `0 ≤ t < T`, `m_t → −1` as `κ → ∞`. -/
theorem multNJ_tendsto_kappa {σ ρ T t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (htT : t < T) :
    Tendsto (fun κ => multNJ σ κ ρ T t) atTop (𝓝 (-1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 htT)).2
  have h2 := (expNeg_lam_tendsto (ρ := ρ) hσ (by linarith : 0 < T)).2
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  exact multNJ_dist hσ hκ ht htT.le

/-- Cochrane (2023), §20.2.5, p. 481 ("or the period of the trap lengthens"): for fixed `t ≥ 0`,
the no-jump multiplier `m_t → −1` as `T → ∞`. -/
theorem multNJ_tendsto_T {σ κ ρ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t) :
    Tendsto (fun T => multNJ σ κ ρ T t) atTop (𝓝 (-1)) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun T => Real.exp (-(lamf ρ κ σ * (T - t)))) atTop (𝓝 0) :=
    (tendsto_expNeg hf).comp ((tendsto_atTop_add_const_right atTop (-t) tendsto_id).congr
      fun T => by simp [sub_eq_add_neg])
  have h3 := h1.add (tendsto_expNeg hf)
  rw [add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_ge_atTop t] with T hT
  exact multNJ_dist hσ hκ ht hT

/-! ### Future spending (p. 481, "not shown") -/

/-- Cochrane (2023), §20.2.5, p. 481: spending `g` on the window `[a, a + Δ)` and `0`
otherwise. -/
noncomputable def gWindow (g a Δ t : ℝ) : ℝ := trapStep g (a + Δ) t - trapStep g a t

/-- Cochrane (2023), §20.2.5, p. 481: the output path of the standard equilibrium for spending
on the window `[a, a + Δ)` (no natural-rate shock; superposition of two traps). -/
noncomputable def windowX (σ κ ρ g a Δ t : ℝ) : ℝ := wX σ κ ρ (a + Δ) 0 g 0 t - wX σ κ ρ a 0 g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: the corresponding inflation path. -/
noncomputable def windowPi (σ κ ρ g a Δ t : ℝ) : ℝ :=
  wPi σ κ ρ (a + Δ) 0 g 0 t - wPi σ κ ρ a 0 g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: the window path solves (20.5)–(20.6) with `i = u_r = 0`
and disturbance `gWindow` (off `{a + Δ, a}`). -/
theorem window_isPath {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (g a Δ : ℝ) :
    IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (gWindow g a Δ) ({a + Δ} ∪ {a})
      (windowX σ κ ρ g a Δ) (windowPi σ κ ρ g a Δ) := by
  have h1 := wPath_isPath (ρ := ρ) hκ hσ (a + Δ) 0 g 0
  have h2 := wPath_isPath (ρ := ρ) hκ hσ a 0 g 0
  refine ⟨h1.1.sub h2.1, h1.2.1.sub h2.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ ({a + Δ} : Set ℝ) := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ ({a} : Set ℝ) := fun hh => hS (Or.inr hh)
  obtain ⟨p1, q1⟩ := h1.2.2 t ht hS1
  obtain ⟨p2, q2⟩ := h2.2.2 t ht hS2
  have z1 : trapStep 0 (a + Δ) t = 0 := by simp [trapStep]
  have z2 : trapStep 0 a t = 0 := by simp [trapStep]
  rw [z1] at p1
  rw [z2] at p2
  exact ⟨(p1.sub p2).congr_deriv (by simp only [windowPi]; ring),
    (q1.sub q2).congr_deriv (by simp only [windowPi, windowX, gWindow]; ring)⟩

/-- Cochrane (2023), §20.2.5, p. 481: the window path vanishes from `a + Δ` on, so it is the
standard (`π_T = 0`) equilibrium for any trap end `T ≥ a + Δ`; it is bounded. -/
theorem window_after {σ κ ρ g a Δ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 ≤ Δ)
    (ht : a + Δ ≤ t) : windowPi σ κ ρ g a Δ t = 0 ∧ windowX σ κ ρ g a Δ t = 0 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have k1 : ∀ T' : ℝ, T' ≤ t → wPi σ κ ρ T' 0 g 0 t = 0 ∧ wX σ κ ρ T' 0 g 0 t = 0 := by
    intro T' hT'
    rcases eq_or_lt_of_le hT' with h | h
    · subst h
      refine ⟨by simp [wPi, trapPi_zero hne], ?_⟩
      simp [wX, trapPi_zero hne, trapY_zero]
      field_simp
      ring
    · exact ⟨by simp [wPi, not_le.2 h], by simp [wX, not_le.2 h]⟩
  obtain ⟨a1, b1⟩ := k1 (a + Δ) ht
  obtain ⟨a2, b2⟩ := k1 a (by linarith)
  simp only [windowPi, windowX, a1, b1, a2, b2, sub_zero, and_self]

/-- Cochrane (2023), §20.2.5, p. 481: the window path is bounded. -/
theorem window_bdd {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (g a Δ : ℝ) :
    BddOnIci (windowX σ κ ρ g a Δ) ∧ BddOnIci (windowPi σ κ ρ g a Δ) := by
  obtain ⟨⟨K1, h1⟩, ⟨K2, h2⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ (a + Δ) 0 g 0
  obtain ⟨⟨K3, h3⟩, ⟨K4, h4⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ a 0 g 0
  exact ⟨⟨K1 + K3, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h3 t ht))⟩,
    ⟨K2 + K4, fun t ht => (abs_sub _ _).trans (add_le_add (h2 t ht) (h4 t ht))⟩⟩

/-- Cochrane (2023), §20.2.5, p. 481: **uniqueness**: for a trap end `T ≥ a + Δ`, any bounded
path for the window disturbance with `π_T = 0` is the window path. -/
theorem window_unique {σ κ ρ g a Δ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 ≤ Δ)
    (hT : a + Δ ≤ T) (hT0 : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (gWindow g a Δ) ({a + Δ} ∪ {a}) x π)
    (hx : BddOnIci x) (hπ : BddOnIci π) (hπT : π T = 0) :
    ∀ t, 0 ≤ t → π t = windowPi σ κ ρ g a Δ t ∧ x t = windowX σ κ ρ g a Δ t := by
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := window_bdd (ρ := ρ) hσ hκ g a Δ
  have hS : ({a + Δ} ∪ {a} ∪ ({a + Δ} ∪ {a}) : Set ℝ).Countable :=
    ((Set.countable_singleton _).union (Set.countable_singleton _)).union
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  have hh := homog_bdd hσ hκ hS (h.sub (window_isPath (ρ := ρ) hσ hκ g a Δ))
    ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
    ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
  have hc : π 0 - windowPi σ κ ρ g a Δ 0 = 0 := by
    have := (hh T hT0).1
    rw [hπT, (window_after (ρ := ρ) hσ hκ hΔ hT).1, sub_zero] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  intro t ht
  obtain ⟨h1, h2⟩ := hh t ht
  rw [hc, mul_zero] at h1
  have h1' : π t = windowPi σ κ ρ g a Δ t := by linarith
  refine ⟨h1', ?_⟩
  rw [h1', sub_self, mul_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hκ.ne'
  · linarith

/-- Cochrane (2023), §20.2.5, p. 481: the time-0 multiplier of window spending,
`h(a + Δ) − h(a)`. -/
noncomputable def windowMult (σ κ ρ a Δ : ℝ) : ℝ :=
  hh (lamf ρ κ σ) (lamb ρ κ σ) (a + Δ) - hh (lamf ρ κ σ) (lamb ρ κ σ) a

/-- Cochrane (2023), §20.2.5, p. 481: time-0 output responds to window spending by
`x_0 = g · windowMult` (`a ≥ 0`, `Δ ≥ 0`). -/
theorem window_x0 {σ κ ρ g a Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) :
    windowX σ κ ρ g a Δ 0 = g * windowMult σ κ ρ a Δ := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [windowX, windowMult, wX, ha, (by linarith : (0 : ℝ) ≤ a + Δ), ↓reduceIte, trapPi,
    trapY, hh, kk, sub_zero]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481: the window multiplier in closed form,
`[λ^f(e^{λ^b Δ} − 1)e^{λ^b a} − λ^b(1 − e^{−λ^f Δ})e^{−λ^f a}]/(λ^f + λ^b)`. -/
theorem windowMult_eq (σ κ ρ a Δ : ℝ) :
    windowMult σ κ ρ a Δ = (lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) *
      Real.exp (lamb ρ κ σ * a) - lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) *
        Real.exp (-(lamf ρ κ σ * a))) / (lamf ρ κ σ + lamb ρ κ σ) := by
  have e1 : Real.exp (lamb ρ κ σ * (a + Δ)) =
      Real.exp (lamb ρ κ σ * Δ) * Real.exp (lamb ρ κ σ * a) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lamf ρ κ σ * (a + Δ))) =
      Real.exp (-(lamf ρ κ σ * Δ)) * Real.exp (-(lamf ρ κ σ * a)) := by
    rw [← Real.exp_add]; ring_nf
  simp only [windowMult, hh, e1, e2]
  ring

/-- Cochrane (2023), §20.2.5, p. 481 ("spending … in the future is exponentially more effective
than spending today"): for a window of fixed length `Δ > 0`, the time-0 multiplier is strictly
increasing in the window's start date `a`. -/
theorem windowMult_strictMono {σ κ ρ Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 < Δ) :
    StrictMono fun a => windowMult σ κ ρ a Δ := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have c1 : 0 < lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) := by
    have : 1 < Real.exp (lamb ρ κ σ * Δ) := Real.one_lt_exp_iff.2 (by positivity)
    nlinarith
  have c2 : 0 < lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) := by
    have : Real.exp (-(lamf ρ κ σ * Δ)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    nlinarith
  intro a1 a2 hlt
  simp only [windowMult_eq]
  rw [div_lt_div_iff_of_pos_right hS]
  have e1 : Real.exp (lamb ρ κ σ * a1) < Real.exp (lamb ρ κ σ * a2) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hlt hb)
  have e2 : Real.exp (-(lamf ρ κ σ * a2)) < Real.exp (-(lamf ρ κ σ * a1)) :=
    Real.exp_lt_exp.2 (by nlinarith)
  nlinarith [mul_lt_mul_of_pos_left e1 c1, mul_lt_mul_of_pos_left e2 c2]

/-- Cochrane (2023), §20.2.5, p. 481: the window multiplier grows without bound (exponentially)
as the window moves into the future. -/
theorem windowMult_tendsto {σ κ ρ Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 < Δ) :
    Tendsto (fun a => windowMult σ κ ρ a Δ) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have c1 : 0 < lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) := by
    have : 1 < Real.exp (lamb ρ κ σ * Δ) := Real.one_lt_exp_iff.2 (by positivity)
    nlinarith
  have hc0 : 0 ≤ lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) := by
    have : Real.exp (-(lamf ρ κ σ * Δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have h1 : Tendsto (fun a => (lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) *
      Real.exp (lamb ρ κ σ * a) - lamb ρ κ σ) / (lamf ρ κ σ + lamb ρ κ σ)) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ ((tendsto_expPos hb).const_mul_atTop c1)).atTop_div_const
      hS
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with a ha
  rw [windowMult_eq, div_le_div_iff_of_pos_right hS]
  have : Real.exp (-(lamf ρ κ σ * a)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hc1 : lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) ≤ lamb ρ κ σ := by
    have := Real.exp_pos (-(lamf ρ κ σ * Δ))
    nlinarith
  nlinarith [Real.exp_pos (-(lamf ρ κ σ * a))]

end Cochrane.ZeroBound.Multipliers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Welfare at the zero-bound steady state

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.3, pp. 484–485.

The book: "The zero-bound left equilibrium `Π_L` in Figure 16.2 has greater welfare than the
desired right-hand equilibrium `Π*`. Less inflation means that firms are closer to their optimal
prices, and relative prices are less distorted." We make this precise in the Calvo model with
constant (log) inflation `π`.

* The stationary Calvo age distribution: a fraction `(1−α)αʲ` of firms last reset their price
  `j` periods ago; their log relative price is `p* − jπ`, with the reset price `p*` fixed by
  the (log-linear) price-index normalisation `∑ (1−α)αʲ p_j = 0`, i.e. `p* = απ/(1−α)`
  (`relPrice_mean`).
* **Exact** relative-price dispersion (cross-sectional variance of log prices)
  `dispersion_eq`: `∑ (1−α)αʲ p_j² = απ²/(1−α)²`, the steady state of Woodford's
  second-order recursion `Δ = αΔ + (α/(1−α))π²` (`dispersion_fixed_point`); and the average
  squared distance from the optimal (reset) price, `resetGap_eq`: `α(1+α)π²/(1−α)²`.
* Both are increasing in `|π|`: `dispersion_lt_iff`, `resetGap_lt_iff`; zero iff `π = 0`
  (`dispersion_eq_zero_iff`, all firms at the optimal price).
* The steady-state quadratic welfare loss `π² + λx̄²` with the steady-state Phillips curve
  `x̄ = (1−β)π/κ` (`ss_phillips_iff`) is also `∝ π²`: `ssLoss_lt_iff`.
* The zero-bound steady state has `Π_L = β` (`zlb_steady_state`, from `Π' = β(1+i)` with
  `i = 0`). **The book's claim holds iff the real rate is below the inflation target**:
  `zlb_better_iff` (`1 < βΠ*`), `zlb_worse_iff` (`βΠ* < 1`); survey **E9** is confirmed as a
  missing qualifier: `e9_counterexample` (`β = 0.95`, `Π* = 1.02`); the book's own numbers
  (`r = 1%`, `Π* = 2%`) satisfy it (`book_calibration`), as does every `Π_L ∈ [1, Π*)`
  (`zlb_better_of_one_le`).
-/

namespace Cochrane.ZeroBound.ZLBWelfare

open Filter Topology

/-! ## The stationary Calvo distribution -/

/-- Cochrane (2023), §20.3, p. 485 (Calvo pricing):
the stationary share of firms whose price was last reset `j` periods ago, `(1−α)αʲ`. -/
noncomputable def calvoW (α : ℝ) (j : ℕ) : ℝ := (1 - α) * α ^ j

/-- Cochrane (2023), §20.3, p. 485: the log relative price of a firm that last reset `j` periods
ago under constant inflation `π`, `p_j = απ/(1−α) − jπ`. -/
noncomputable def relPrice (α π : ℝ) (j : ℕ) : ℝ := α * π / (1 - α) - j * π

/-- Cochrane (2023), §20.3, p. 485 ("relative prices are less distorted"): the cross-sectional
dispersion (variance) of log prices, `∑ (1−α)αʲ p_j²`. -/
noncomputable def dispersion (α π : ℝ) : ℝ := ∑' j, calvoW α j * relPrice α π j ^ 2

/-- Cochrane (2023), §20.3, p. 485 ("firms are closer to their optimal prices"): the average
squared distance of prices from the optimal (reset) price, `∑ (1−α)αʲ (jπ)²`. -/
noncomputable def resetGap (α π : ℝ) : ℝ := ∑' j, calvoW α j * ((j : ℝ) * π) ^ 2

/-- Cochrane (2023), §20.3, p. 485: the age weights sum to one. -/
theorem hasSum_calvoW {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) : HasSum (calvoW α) 1 := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - α)
  rwa [mul_inv_cancel₀ (by linarith : (1 : ℝ) - α ≠ 0)] at this

/-- Cochrane (2023), §20.3, p. 485: the mean age, `∑ (1−α)αʲ j = α/(1−α)`. -/
theorem hasSum_calvoW_mul {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => calvoW α j * j) (α / (1 - α)) := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 - α)
  have e : (1 - α) * (α / (1 - α) ^ 2) = α / (1 - α) := by
    field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [calvoW]
  ring

/-- Cochrane (2023), §20.3, p. 485: `∑ j² αʲ = α(1+α)/(1−α)³` for `0 ≤ α < 1`. -/
theorem hasSum_sq_mul_geometric {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => (j : ℝ) ^ 2 * α ^ j) (α * (1 + α) / (1 - α) ^ 3) := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hs2 : Summable (fun j : ℕ => (j : ℝ) ^ 2 * α ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have hS1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hS0 := hasSum_geometric_of_lt_one h0 h1
  set S2 := ∑' j : ℕ, (j : ℝ) ^ 2 * α ^ j
  -- the shift `S₂ = α(S₂ + 2S₁ + S₀)`
  have hshift : S2 = α * (S2 + 2 * (α / (1 - α) ^ 2) + (1 - α)⁻¹) := by
    have e1 := hs2.tsum_eq_zero_add
    have hsucc : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 * α ^ (j + 1))
        (α * (S2 + 2 * (α / (1 - α) ^ 2) + (1 - α)⁻¹)) := by
      have := ((hs2.hasSum.add (hS1.mul_left 2)).add hS0).mul_left α
      refine this.congr_fun fun j => ?_
      push_cast
      ring
    simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      pow_zero, mul_one, zero_add] at e1
    exact e1.trans hsucc.tsum_eq
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have hval : S2 = α * (1 + α) / (1 - α) ^ 3 := by
    field_simp at hshift ⊢
    linear_combination hshift
  rw [← hval]
  exact hs2.hasSum

/-- Cochrane (2023), §20.3, p. 485: the second moment of the age,
`∑ (1−α)αʲ j² = α(1+α)/(1−α)²`. -/
theorem hasSum_calvoW_sq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => calvoW α j * (j : ℝ) ^ 2) (α * (1 + α) / (1 - α) ^ 2) := by
  have := (hasSum_sq_mul_geometric h0 h1).mul_left (1 - α)
  have e : (1 - α) * (α * (1 + α) / (1 - α) ^ 3) = α * (1 + α) / (1 - α) ^ 2 := by
    field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [calvoW]
  ring

/-- Cochrane (2023), §20.3, p. 485: the price-index normalisation — the weighted mean of log
relative prices is zero, `∑ (1−α)αʲ p_j = 0`. -/
theorem relPrice_mean {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    HasSum (fun j => calvoW α j * relPrice α π j) 0 := by
  have := ((hasSum_calvoW h0 h1).mul_left (α * π / (1 - α))).sub
    ((hasSum_calvoW_mul h0 h1).mul_left π)
  have e : α * π / (1 - α) * 1 - π * (α / (1 - α)) = 0 := by ring
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [relPrice]
  ring

/-- Cochrane (2023), §20.3, p. 485: **the exact steady-state dispersion**,
`∑ (1−α)αʲ p_j² = απ²/(1−α)²` (`0 ≤ α < 1`). -/
theorem dispersion_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = α * π ^ 2 / (1 - α) ^ 2 := by
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have h := (((hasSum_calvoW h0 h1).mul_left ((α * π / (1 - α)) ^ 2)).sub
    ((hasSum_calvoW_mul h0 h1).mul_left (2 * (α * π / (1 - α)) * π))).add
    ((hasSum_calvoW_sq h0 h1).mul_left (π ^ 2))
  have e : (α * π / (1 - α)) ^ 2 * 1 - 2 * (α * π / (1 - α)) * π * (α / (1 - α)) +
      π ^ 2 * (α * (1 + α) / (1 - α) ^ 2) = α * π ^ 2 / (1 - α) ^ 2 := by
    field_simp
    ring
  rw [e] at h
  rw [dispersion, ← h.tsum_eq]
  congr 1
  funext j
  simp only [relPrice]
  ring

/-- Cochrane (2023), §20.3, p. 485: the average squared distance from the optimal price,
`∑ (1−α)αʲ (jπ)² = α(1+α)π²/(1−α)²`. -/
theorem resetGap_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    resetGap α π = α * (1 + α) * π ^ 2 / (1 - α) ^ 2 := by
  have h := (hasSum_calvoW_sq h0 h1).mul_left (π ^ 2)
  rw [resetGap, ← (show π ^ 2 * (α * (1 + α) / (1 - α) ^ 2) =
    α * (1 + α) * π ^ 2 / (1 - α) ^ 2 by ring), ← h.tsum_eq]
  congr 1
  funext j
  ring

/-- Cochrane (2023), §20.3, p. 485 (Woodford's (2.20) in steady state): the dispersion is the
fixed point of `Δ = αΔ + (α/(1−α))π²`. -/
theorem dispersion_fixed_point {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = α * dispersion α π + α / (1 - α) * π ^ 2 := by
  rw [dispersion_eq h0 h1]
  field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  ring

/-- Cochrane (2023), §20.3, p. 485: with price stickiness (`0 < α < 1`), relative prices are
undistorted iff inflation is zero. -/
theorem dispersion_eq_zero_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = 0 ↔ π = 0 := by
  rw [dispersion_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · linarith
  · rintro rfl; simp

/-- Cochrane (2023), §20.3, p. 485: at zero inflation every firm is at the optimal price. -/
theorem relPrice_zero (α : ℝ) (j : ℕ) : relPrice α 0 j = 0 := by
  simp [relPrice]

/-- Cochrane (2023), §20.3, p. 485 ("less inflation means … relative prices are less
distorted"): dispersion is strictly increasing in `|π|` (`0 < α < 1`). -/
theorem dispersion_lt_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π1 π2 : ℝ) :
    dispersion α π1 < dispersion α π2 ↔ |π1| < |π2| := by
  rw [dispersion_eq h0.le h1, dispersion_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have hd : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hd, mul_lt_mul_iff_right₀ h0, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-- Cochrane (2023), §20.3, p. 485 ("firms are closer to their optimal prices"): the average
squared distance from the optimal price is strictly increasing in `|π|`. -/
theorem resetGap_lt_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π1 π2 : ℝ) :
    resetGap α π1 < resetGap α π2 ↔ |π1| < |π2| := by
  rw [resetGap_eq h0.le h1, resetGap_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have hd : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  have hc : 0 < α * (1 + α) := by positivity
  rw [div_lt_div_iff_of_pos_right hd, mul_lt_mul_iff_right₀ hc, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-! ## Steady-state welfare loss -/

/-- Cochrane (2023), §20.3, p. 485 (the new-Keynesian Phillips curve in steady state):
`π = βπ + κx̄` iff `x̄ = (1−β)π/κ`. -/
theorem ss_phillips_iff {β κ π x : ℝ} (hκ : κ ≠ 0) :
    π = β * π + κ * x ↔ x = (1 - β) * π / κ := by
  rw [eq_div_iff hκ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §20.3, p. 485: the steady-state quadratic welfare loss
`π² + λx̄²` at the steady state `x̄ = (1−β)π/κ` of inflation `π`. -/
noncomputable def ssLoss (lam β κ π : ℝ) : ℝ := π ^ 2 + lam * ((1 - β) * π / κ) ^ 2

/-- Cochrane (2023), §20.3, p. 485: the steady-state loss is `π²(1 + λ(1−β)²/κ²)`, strictly
increasing in `|π|` (`λ ≥ 0`). -/
theorem ssLoss_lt_iff {lam β κ : ℝ} (hlam : 0 ≤ lam) (π1 π2 : ℝ) :
    ssLoss lam β κ π1 < ssLoss lam β κ π2 ↔ |π1| < |π2| := by
  have e : ∀ π, ssLoss lam β κ π = π ^ 2 * (1 + lam * ((1 - β) / κ) ^ 2) := fun π => by
    simp only [ssLoss]; ring
  have hc : 0 < 1 + lam * ((1 - β) / κ) ^ 2 := by positivity
  rw [e, e, mul_lt_mul_iff_left₀ hc, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-! ## The zero-bound steady state `Π_L` versus `Π*` -/

/-- Cochrane (2023), §20.3, p. 484, with (16.28) `Π' = β(1+i)`: at the zero bound (`i = 0`) the
steady state is `Π_L = β` (deflation at the real rate). -/
theorem zlb_steady_state {β PL i : ℝ} (hfisher : PL = β * (1 + i)) (hi : i = 0) : PL = β := by
  rw [hfisher, hi]; ring

/-- Cochrane (2023), §20.3, pp. 484–485, **corrected** (survey E9): with `0 < β ≤ 1` and a
target `Π* ≥ 1`, the zero-bound steady state `Π_L = β` has strictly less relative-price
dispersion than `Π*` iff `1 < βΠ*` (the real rate is below the target inflation rate). -/
theorem zlb_better_iff {α β Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    dispersion α (Real.log β) < dispersion α (Real.log Pstar) ↔ 1 < β * Pstar := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), neg_lt_iff_pos_add, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_pos_iff (by positivity)]

/-- Cochrane (2023), §20.3, pp. 484–485 (survey E9): conversely the zero-bound steady state is
strictly *worse* iff `βΠ* < 1` (the real rate exceeds the target). -/
theorem zlb_worse_iff {α β Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    dispersion α (Real.log Pstar) < dispersion α (Real.log β) ↔ β * Pstar < 1 := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), lt_neg_iff_add_neg, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_neg_iff (by positivity)]

/-- Cochrane (2023), §20.3, pp. 484–485, the same comparison for the steady-state quadratic
welfare loss: `Π_L = β` is better than `Π*` iff `1 < βΠ*`. -/
theorem zlb_welfare_better_iff {lam βd κ β Pstar : ℝ} (hlam : 0 ≤ lam) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    ssLoss lam βd κ (Real.log β) < ssLoss lam βd κ (Real.log Pstar) ↔ 1 < β * Pstar := by
  rw [ssLoss_lt_iff hlam, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), neg_lt_iff_pos_add, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_pos_iff (by positivity)]

/-- Cochrane (2023), §20.3, p. 485, **E9 counterexample**: with a 5% real rate (`β = 0.95`) and a
2% target (`Π* = 1.02`), the zero-bound steady state has strictly more relative-price
dispersion than `Π*` (for every Calvo parameter `0 < α < 1`). -/
theorem e9_counterexample {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    dispersion α (Real.log (1.02 : ℝ)) < dispersion α (Real.log (0.95 : ℝ)) :=
  (zlb_worse_iff h0 h1 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- Cochrane (2023), §20.3 and p. 380 (the book's numbers): with `r = 1%` (`β = 1/1.01`) and a
2% target, the zero-bound steady state (`−1%` inflation) has less dispersion than `Π*`. -/
theorem book_calibration {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    dispersion α (Real.log (1 / 1.01 : ℝ)) < dispersion α (Real.log (1.02 : ℝ)) :=
  (zlb_better_iff h0 h1 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- Cochrane (2023), §20.3, p. 380 ("`Π_L` may occur at, say, 1% inflation"): any zero-bound
steady state with `1 ≤ Π_L < Π*` has strictly less dispersion than `Π*`. -/
theorem zlb_better_of_one_le {α PL Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hL : 1 ≤ PL)
    (hlt : PL < Pstar) : dispersion α (Real.log PL) < dispersion α (Real.log Pstar) := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonneg (Real.log_nonneg hL),
    abs_of_nonneg (Real.log_nonneg (by linarith))]
  exact Real.log_lt_log (by linarith) hlt

end Cochrane.ZeroBound.ZLBWelfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the sections of Chapters 20–21

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, pp. 465–485 (and §5.7.1,
p. 165, for the discrete-to-continuous-time limit). The discrete-time sections (§20.1 peg,
§20.2.1 rule with a bound, §20.2.6 Gabaix, Ch. 21) and the continuous-time sections (§§20.2.2–
20.2.5, Werning's model, and §20.3 welfare) were formalised separately; this module proves how
their overlapping objects relate.

* Roots. The discrete roots (5.6) of `ZLBPeg` with period length `h` (`β = 1 − ρh`, slopes
  `σh`, `κh`) are `λ₁ = 1 + h·scaledRoot` exactly (`lam1_scaled_eq`, `lam2_scaled_eq`), and
  `(λ₁ − 1)/h → λ^b`, `(λ₂ − 1)/h → −λ^f`, the continuous-time roots of `ContinuousTimeNK`
  (`tendsto_lam1_scaled`, `tendsto_lam2_scaled`); the per-period decay `λ₁^{−n}` over `n`
  periods of length `t/n` tends to `e^{−λ^b t}` (`tendsto_peg_decay`).
* The indeterminate peg. Under perfect foresight every bounded `ZLBPeg` equilibrium is
  `π_t − ī = λ₁^{−t}(π₀ − ī)` (`peg_pf_path`), a one-parameter family like the continuous-time
  family `WerningModel.bdd_path_iff`; with the same initial inflation the discrete equilibria
  converge to the continuous-time one (`peg_paths_converge`). Both families are uncountable
  (`ZLBPeg.peg_continuum`, `werning_continuum`).
* Fiscal selection. The discrete impact coefficient `1 − ρ/λ₁` of
  `ZLBPeg.fiscal_unexpected_inflation`, per unit of time, tends to the coefficient `r + λ^b` of
  `ZLBSelection.jump_eq_fiscal` (`tendsto_peg_impact`); in the frictionless limit it is `1`, the
  coefficient of `Covid.fiscal_news_only_unexpected` (`fiscal_impact_frictionless`).
* Future selection. The continuous-time counterpart of `FutureSelection.future_selection` and
  `ZLBRule.fig203_selection`: an active rule after the trap selects the `π_T = 0` member of the
  Werning family (`werning_future_selection`).
* Gabaix. At `M = M^f = 1` the Gabaix matrix is the peg matrix, the determinacy condition fails
  and the roots straddle the unit circle (`gabaix_rational_eq_peg`, `gabaixEq_rational_iff`,
  `gabaix_rational_straddle`).
* The lower-bound steady state. `Π_L = β` (`ZLBWelfare.zlb_steady_state`) is the fixed point of
  the Chapter 16 map at the bound (`map46_fixed_beta_iff`, `zlb_fixed_point_eq_beta`), and its
  logarithm is the zero-bound steady state `−u` of `ZLBRule` with natural rate `u = −log β`
  (`zlb_steady_log`).
-/

namespace Cochrane.ZeroBound.Links

open Filter Topology
open Cochrane.ZeroBound

/-! ## The roots: discrete (5.6) and continuous time -/

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): the scaled
root `(−ρ + σκh + √((ρ − σκh)² + 4σκ))/2`, a continuous function of the period length `h`. -/
noncomputable def scaledRoot (ρ σ κ h : ℝ) : ℝ :=
  (-ρ + σ * κ * h + Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0`
(`β = 1 − ρh`, IS slope `σh`, Phillips-curve slope `κh`) the peg root of `ZLBPeg` is exactly
`λ₁ = 1 + h·scaledRoot ρ σ κ h`. -/
theorem lam1_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h) = 1 + h * scaledRoot ρ σ κ h := by
  have hd : discQ (1 + (1 - ρ * h) + σ * h * (κ * h)) (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    unfold discQ
    ring
  rw [ZLBPeg.lam1, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le, scaledRoot]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0` the stable
root of `ZLBPeg` is `λ₂ = 1 + h(−ρ + σκh − √((ρ − σκh)² + 4σκ))/2`. -/
theorem lam2_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    ZLBPeg.lam2 (1 - ρ * h) (σ * h) (κ * h) =
      1 + h * ((-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) := by
  have hd : discQ (1 + (1 - ρ * h) + σ * h * (κ * h)) (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    unfold discQ
    ring
  rw [ZLBPeg.lam2, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  ring

/-- Cochrane (2023), §5.7.1, p. 165 and p. 475: at `h = 0` the scaled root is the
continuous-time root `λ^b = (√(ρ² + 4κσ) − ρ)/2` of `ContinuousTimeNK`. -/
theorem scaledRoot_zero (ρ σ κ : ℝ) : scaledRoot ρ σ κ 0 = ContinuousTimeNK.lamb ρ κ σ := by
  rw [scaledRoot, ContinuousTimeNK.lamb]
  simp only [mul_zero, add_zero, sub_zero]
  rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
  ring

/-- Cochrane (2023), §5.7.1, p. 165 (the scaled root is continuous in `h`). -/
theorem continuous_scaledRoot (ρ σ κ : ℝ) : Continuous (scaledRoot ρ σ κ) := by
  unfold scaledRoot
  fun_prop

/-- Cochrane (2023), §5.7.1, p. 165 (tool): for `σκ > 0` the scaled root is positive. -/
theorem scaledRoot_pos {ρ σ κ : ℝ} (ha : 0 < σ * κ) (h : ℝ) : 0 < scaledRoot ρ σ κ h := by
  unfold scaledRoot
  have hlt : |ρ - σ * κ * h| < Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := le_abs_self (ρ - σ * κ * h)
  linarith

/-- Cochrane (2023), (5.6), p. 119 (§20.1, p. 467) → p. 475 (**discrete → continuous time**): as
the period length `h → 0⁺`, `(λ₁ − 1)/h` converges to the continuous-time root `λ^b` of
`ContinuousTimeNK` (the discrete unstable root `λ₁ > 1` is the per-period decay factor of the
peg equilibria, `λ^b` their continuous-time decay rate). -/
theorem tendsto_lam1_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
  rw [← scaledRoot_zero]
  refine ((continuous_scaledRoot ρ σ κ).tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam1_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), (5.6), p. 119 → p. 475: as `h → 0⁺`, `(λ₂ − 1)/h` converges to minus the
continuous-time root `λ^f` of `ContinuousTimeNK`. -/
theorem tendsto_lam2_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (ZLBPeg.lam2 (1 - ρ * h) (σ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (-ContinuousTimeNK.lamf ρ κ σ)) := by
  have hc : Continuous fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2 := by fun_prop
  have h0 : (fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) 0 =
      -ContinuousTimeNK.lamf ρ κ σ := by
    simp only [ContinuousTimeNK.lamf, mul_zero, add_zero, sub_zero]
    rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
    ring
  rw [← h0]
  refine (hc.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam2_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), §20.1, p. 467 (peg equilibria decay like `λ₁^{−j}` per period) → p. 475
(`WerningModel.homog_bdd`: decay `e^{−λ^b t}`): over a fixed time `t > 0` cut into `n` periods
of length `t/n`, the discrete decay factor `λ₁^{−n}` converges to `e^{−λ^b t}` (restated from
the Cochrane Chapter 5 project). -/
theorem tendsto_peg_decay {ρ σ κ t : ℝ} (ha : 0 < σ * κ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (ZLBPeg.lam1 (1 - ρ * (t / n)) (σ * (t / n)) (κ * (t / n)))⁻¹ ^ n)
      atTop (𝓝 (Real.exp (-(ContinuousTimeNK.lamb ρ κ σ * t)))) := by
  have hgt : Tendsto (fun n : ℕ => scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
    rw [← scaledRoot_zero]
    exact ((continuous_scaledRoot ρ σ κ).tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hup : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := hgt.const_mul t
  have hlo : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n) /
      (1 + t / n * scaledRoot ρ σ κ (t / n))) atTop (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := by
    have hd : Tendsto (fun n : ℕ => 1 + t / n * scaledRoot ρ σ κ (t / n)) atTop
        (𝓝 (1 + 0 * ContinuousTimeNK.lamb ρ κ σ)) :=
      tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat t).mul hgt)
    rw [zero_mul, add_zero] at hd
    have := hup.div hd one_ne_zero
    rw [div_one] at this
    exact this
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + t / n * scaledRoot ρ σ κ (t / n)))
      atTop (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hy : 0 < t / n * scaledRoot ρ σ κ (t / n) :=
        mul_pos (div_pos ht hn') (scaledRoot_pos ha _)
      have hl := Real.one_sub_inv_le_log_of_pos
        (by linarith : (0 : ℝ) < 1 + t / n * scaledRoot ρ σ κ (t / n))
      have e : t * scaledRoot ρ σ κ (t / n) / (1 + t / n * scaledRoot ρ σ κ (t / n)) =
          n * (1 - (1 + t / n * scaledRoot ρ σ κ (t / n))⁻¹) := by
        have h1 : (1 + t / n * scaledRoot ρ σ κ (t / n)) ≠ 0 := by linarith
        have hty : t * scaledRoot ρ σ κ (t / n) = n * (t / n * scaledRoot ρ σ κ (t / n)) := by
          field_simp
        rw [hty, mul_div_assoc]
        congr 1
        generalize t / n * scaledRoot ρ σ κ (t / n) = y at h1 ⊢
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hl hn'.le
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hy : 0 < t / n * scaledRoot ρ σ κ (t / n) :=
        mul_pos (div_pos ht hn') (scaledRoot_pos ha _)
      have hl := Real.log_le_sub_one_of_pos
        (by linarith : (0 : ℝ) < 1 + t / n * scaledRoot ρ σ κ (t / n))
      have e : t * scaledRoot ρ σ κ (t / n) =
          n * (1 + t / n * scaledRoot ρ σ κ (t / n) - 1) := by
        rw [add_sub_cancel_left]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hl hn'.le
  have hexp := (Real.continuous_exp.tendsto _).comp hlog.neg
  rw [show -(ContinuousTimeNK.lamb ρ κ σ * t) = -(t * ContinuousTimeNK.lamb ρ κ σ) by ring]
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < 1 + t / n * scaledRoot ρ σ κ (t / n) := by
    have := mul_pos (div_pos ht hn') (scaledRoot_pos (ρ := ρ) ha (t / n))
    linarith
  rw [lam1_scaled_eq (div_pos ht hn'), inv_pow, ← Real.exp_log (pow_pos hpos n), Real.log_pow,
    ← Real.exp_neg]
  rfl

/-! ## The indeterminate peg: discrete and continuous families -/

/-- Cochrane (2023), §20.1, p. 467, under perfect foresight: every bounded equilibrium at the
peg is `π_t − ī = λ₁^{−t}(π₀ − ī)`, a one-parameter family indexed by `π₀` (the discrete
counterpart of the continuous-time family `WerningModel.bdd_path_iff`, p. 475). -/
theorem peg_pf_path {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Unit → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : ZLBPeg.PegEq perfectForesight β σ κ ibar x π)
    (t : ℕ) : π t () - ibar = (ZLBPeg.lam1 β σ κ)⁻¹ ^ t * (π 0 () - ibar) := by
  have hl : ZLBPeg.lam1 β σ κ ≠ 0 := by linarith [ZLBPeg.one_lt_lam1 hβ hσκ]
  induction t with
  | zero => simp
  | succ t ih =>
    have hr := ZLBPeg.peg_pi_rec perfectForesight hβ hσκ hbx hbπ h t ()
    change π t () - ibar = ZLBPeg.lam1 β σ κ * (π (t + 1) () - ibar) at hr
    have hs : π (t + 1) () - ibar = (ZLBPeg.lam1 β σ κ)⁻¹ * (π t () - ibar) := by
      rw [hr]
      field_simp
    rw [hs, ih, pow_succ]
    ring

/-- Cochrane (2023), §20.1, p. 467 → §20.2.2, p. 475 (**the discrete peg converges to the
continuous-time peg**): take the peg model with period length `t/n` (`β = 1 − ρt/n`, slopes
`σt/n`, `κt/n`), and for each `n` a bounded perfect-foresight equilibrium with initial inflation
`ī + c`. Let `(x, π)` be a bounded path of the continuous-time model (20.5)–(20.6) at the peg with
no shocks and `π₀ = c`. Then inflation after `n` periods (time `t`) converges to `π_t`:
`π^{(n)}_n − ī → π_t = e^{−λ^b t}c`. -/
theorem peg_paths_converge {ρ σ κ t ibar c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 < t)
    {X P : ℕ → ℕ → Unit → ℝ}
    (hP : ∀ n : ℕ, 0 < n → ZLBPeg.PegEq perfectForesight (1 - ρ * (t / n)) (σ * (t / n))
      (κ * (t / n)) ibar (X n) (P n) ∧ BoundedProc (X n) ∧ BoundedProc (P n))
    (h0 : ∀ n, P n 0 () = ibar + c) {S : Set ℝ} (hS : S.Countable) {x π : ℝ → ℝ}
    (hc : WerningModel.IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) S x π)
    (hxb : WerningModel.BddOnIci x) (hπb : WerningModel.BddOnIci π) (hπ0 : π 0 = c) :
    Tendsto (fun n => P n n () - ibar) atTop (𝓝 (π t)) := by
  have hdec := tendsto_peg_decay (ρ := ρ) (mul_pos hσ hκ) ht
  rw [(WerningModel.homog_bdd hσ hκ hS hc hxb hπb t ht.le).1, hπ0]
  have hsmall : ∀ᶠ n : ℕ in atTop, ρ * (t / n) < 1 := by
    have hlim : Tendsto (fun n : ℕ => ρ * (t / n)) atTop (𝓝 (ρ * 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat t).const_mul ρ
    rw [mul_zero] at hlim
    exact hlim.eventually (gt_mem_nhds one_pos)
  refine (hdec.mul_const c).congr' ?_
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hβ : 0 < 1 - ρ * (t / n) := by linarith
  have hσκ : 0 < σ * (t / n) * (κ * (t / n)) := by positivity
  obtain ⟨hpeg, hbx, hbπ⟩ := hP n hn0
  have := peg_pf_path hβ hσκ hbx hbπ hpeg n
  rw [this, h0]
  ring

/-- Cochrane (2023), §20.2.2, pp. 474–475 (the continuous-time counterpart of
`ZLBPeg.peg_continuum`, p. 467): the bounded paths of the zero-bound experiment form an
uncountable set (they are indexed injectively by `π_T`). -/
theorem werning_continuum {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ¬ {p : (ℝ → ℝ) × (ℝ → ℝ) | WerningModel.IsPath σ ρ κ (fun _ => 0)
      (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} p.1 p.2 ∧
      WerningModel.BddOnIci p.1 ∧ WerningModel.BddOnIci p.2}.Countable := by
  intro hc
  let f : ℝ → (ℝ → ℝ) × (ℝ → ℝ) := fun c =>
    (WerningModel.wX σ κ ρ T u g c, WerningModel.wPi σ κ ρ T u g c)
  have hmaps : Set.MapsTo f Set.univ {p : (ℝ → ℝ) × (ℝ → ℝ) | WerningModel.IsPath σ ρ κ
      (fun _ => 0) (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} p.1 p.2 ∧
      WerningModel.BddOnIci p.1 ∧ WerningModel.BddOnIci p.2} := fun c _ =>
    (WerningModel.bdd_path_iff hκ hσ).2 ⟨c, fun _ _ => ⟨rfl, rfl⟩⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrArg Prod.snd h) T
    simpa [f, WerningModel.wPi_T hκ hσ] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-! ## Fiscal selection: discrete and continuous impact coefficients -/

/-- Cochrane (2023), §20.1, p. 469 (`ZLBPeg.fiscal_unexpected_inflation`: unexpected inflation
`−(1 − ρ_v/λ₁)ε`) → §20.2.2, p. 476 (`ZLBSelection.jump_eq_fiscal`: inflation jump
`−(r + λ^b)×` the fiscal innovation): with period length `h`, valuation discount
`ρ_v = 1 − rh` and `β = 1 − ρh` in the Phillips curve, the discrete impact coefficient per unit
of time converges to the continuous-time one, `(1 − (1 − rh)/λ₁)/h → r + λ^b` as `h → 0⁺`
(restated from the Cochrane Chapter 5 project). -/
theorem tendsto_peg_impact {ρ σ κ : ℝ} (r : ℝ) (ha : 0 < σ * κ) :
    Tendsto (fun h => (1 - (1 - r * h) / ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h)) / h)
      (𝓝[>] 0) (𝓝 (r + ContinuousTimeNK.lamb ρ κ σ)) := by
  have hg := (continuous_scaledRoot ρ σ κ).tendsto 0
  have hnum : Tendsto (fun h => scaledRoot ρ σ κ h + r) (𝓝 0) (𝓝 (scaledRoot ρ σ κ 0 + r)) :=
    hg.add_const r
  have hden : Tendsto (fun h => 1 + h * scaledRoot ρ σ κ h) (𝓝 0)
      (𝓝 (1 + 0 * scaledRoot ρ σ κ 0)) :=
    tendsto_const_nhds.add (tendsto_id.mul hg)
  rw [zero_mul, add_zero] at hden
  have hlim := hnum.div hden one_ne_zero
  rw [div_one, scaledRoot_zero, add_comm] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < 1 + h * scaledRoot ρ σ κ h := by
    have := mul_pos (Set.mem_Ioi.mp hh) (scaledRoot_pos (ρ := ρ) ha h)
    linarith
  change (scaledRoot ρ σ κ h + r) / (1 + h * scaledRoot ρ σ κ h) = _
  rw [lam1_scaled_eq hh]
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  have hp' : 1 + h * scaledRoot ρ σ κ h ≠ 0 := hp.ne'
  rw [eq_div_iff hh', div_mul_eq_mul_div, eq_comm, sub_eq_iff_eq_add, ← add_div,
    eq_div_iff hp']
  ring

/-- Cochrane (2023), §20.1, p. 469 → Ch. 21, p. 491 (`Covid.fiscal_news_only_unexpected`: in the
frictionless model unexpected inflation is `−ε` one for one): as prices become flexible
(`κ → ∞`), the impact coefficient `1 − ρ/λ₁` of `ZLBPeg.fiscal_unexpected_inflation` tends to
`1`. -/
theorem fiscal_impact_frictionless {β σ ρ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => 1 - ρ / ZLBPeg.lam1 β σ κ) atTop (𝓝 1) := by
  have hlow : Tendsto (fun κ => (1 + β + σ * κ) / 2) atTop atTop := by
    refine Tendsto.atTop_div_const two_pos ?_
    exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hσ)
  have hlam : Tendsto (fun κ => ZLBPeg.lam1 β σ κ) atTop atTop := by
    refine tendsto_atTop_mono (fun κ => ?_) hlow
    unfold ZLBPeg.lam1
    linarith [Real.sqrt_nonneg (discQ (1 + β + σ * κ) β)]
  have h0 : Tendsto (fun κ => ρ / ZLBPeg.lam1 β σ κ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlam
  simpa using h0.const_sub 1

/-! ## Future selection in continuous time -/

/-- Cochrane (2023), (20.7), p. 474, with §20.2.2, p. 475 (the continuous-time counterpart of
`FutureSelection.future_selection` and `ZLBRule.fig203_selection`, §20.2.1, p. 472): in the
zero-bound experiment, if the interest rate is pegged at zero during the trap and follows the
active rule `i = φπ` (`φ > 1`) from `T` on, then every bounded path is the `π_T = 0` member of
the Werning family `(wX 0, wPi 0)`: the expected future rule selects the equilibrium. -/
theorem werning_future_selection {σ κ ρ φ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hφ : 1 < φ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : WerningModel.IsPath σ ρ κ (fun t => if t < T then 0 else φ * π t)
      (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} x π)
    (hx : WerningModel.BddOnIci x) (hπ : WerningModel.BddOnIci π) :
    ∀ t, 0 ≤ t → π t = WerningModel.wPi σ κ ρ T u g 0 t ∧
      x t = WerningModel.wX σ κ ρ T u g 0 t := by
  obtain ⟨hxc, hπc, hd⟩ := h
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  have hsel := WerningModel.eq20_7_selects (istar := fun _ => 0)
    (u := WerningModel.trapStep u T) (g := WerningModel.trapStep g T) (xs := fun _ => 0)
    (πs := fun _ => 0) (Set.countable_singleton T) hσ hκ hρ hφ
    (hxc.mono (Set.Ici_subset_Ici.2 hT)) (hπc.mono (Set.Ici_subset_Ici.2 hT))
    continuousOn_const continuousOn_const
    (fun t ht htS => by
      obtain ⟨a, b⟩ := hd t (lt_of_le_of_lt hT ht) htS
      have hnot : ¬ t < T := not_lt.2 ht.le
      refine ⟨a.congr_deriv ?_, b⟩
      simp only [hnot, ↓reduceIte]
      ring)
    (fun t ht _ => by
      have hnot : ¬ t < T := not_lt.2 ht.le
      simp only [WerningModel.trapStep, hnot, ↓reduceIte]
      exact ⟨(hasDerivAt_const t (0 : ℝ)).congr_deriv (by ring),
        (hasDerivAt_const t (0 : ℝ)).congr_deriv (by ring)⟩)
    Kx Kπ 0 0 (fun t ht => hKx t (hT.trans ht)) (fun t ht => hKπ t (hT.trans ht))
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hpath : WerningModel.IsPath σ ρ κ (fun _ => 0) (WerningModel.trapStep u T)
      (WerningModel.trapStep g T) {T} x π := by
    refine ⟨hxc, hπc, fun t ht htS => ?_⟩
    obtain ⟨a, b⟩ := hd t ht htS
    refine ⟨a.congr_deriv ?_, b⟩
    by_cases htT : t < T
    · simp only [htT, ↓reduceIte]
    · have h0 := (hsel t (not_lt.1 htT)).1
      simp only [htT, ↓reduceIte, h0, mul_zero]
  obtain ⟨πT, hπT⟩ := (WerningModel.bdd_path_iff hκ hσ).1 ⟨hpath, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
  have h0 : πT = 0 := by
    have := (hπT T hT).1
    rw [WerningModel.wPi_T hκ hσ] at this
    rw [← this]
    exact (hsel T le_rfl).1
  intro t ht
  rw [← h0]
  exact hπT t ht

/-! ## Gabaix at the rational limit is the peg -/

/-- Cochrane (2023), (20.11)–(20.12), p. 482, at `M = M^f = 1` (rational expectations): the
Gabaix matrix is the peg matrix of (5.1)–(5.2), §20.1, p. 467. -/
theorem gabaix_rational_eq_peg (β σ κ : ℝ) :
    Gabaix.gabaixMatrix 1 1 β σ κ = ZLBPeg.pegMatrix β σ κ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gabaix.gabaixMatrix, ZLBPeg.pegMatrix]

/-- Cochrane (2023), (20.11)–(20.12), p. 482 and (5.1)–(5.2), p. 118: at `M = M^f = 1` the Gabaix
model at a peg is the standard new-Keynesian model at a peg, under any `ExpectationSystem`. -/
theorem gabaixEq_rational_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β σ κ ibar : ℝ)
    (x π : ℕ → Ω → ℝ) :
    Gabaix.GabaixEq 𝔼 1 1 β σ κ ibar x π ↔ ZLBPeg.PegEq 𝔼 β σ κ ibar x π := by
  rw [Gabaix.gabaixEq_iff_solves, ZLBPeg.pegEq_iff_solves, gabaix_rational_eq_peg]
  rfl

/-- Cochrane (2023), pp. 482–483 → §20.1, p. 467: at `M = M^f = 1` the Gabaix determinacy
condition `(1 − M)(1 − βM^f) > σκ` reads `0 > σκ` and fails, and correspondingly the roots of the
Gabaix matrix are the (5.6) roots `λ₁`, `λ₂` of `ZLBPeg`, which straddle the unit circle:
`‖λ₂‖ < 1 < ‖λ₁‖` (indeterminacy). -/
theorem gabaix_rational_straddle {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 < σ * κ) :
    ((‖root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1 ∧
      ‖root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1)
        ↔ σ * κ < (1 - 1) * (1 - β * 1)) ∧
      ¬ σ * κ < (1 - 1) * (1 - β * 1) ∧
      root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ)) =
        (ZLBPeg.lam1 β σ κ : ℂ) ∧
      root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ)) =
        (ZLBPeg.lam2 β σ κ : ℂ) ∧
      ‖root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1 ∧
      1 < ‖root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ := by
  refine ⟨Gabaix.gabaix_roots_iff zero_le_one le_rfl zero_le_one le_rfl hβ0 hβ1 hσκ.le, ?_, ?_⟩
  · rw [sub_self, zero_mul]
    exact not_lt.2 hσκ.le
  · rw [gabaix_rational_eq_peg]
    exact ZLBPeg.pegMatrix_roots hβ0 hσκ

/-! ## The lower-bound steady state `Π_L = β` -/

/-- Cochrane (2023), (16.28), p. 379 and §20.3, p. 484, with the global map
`Π' = β(1 + φ(Π))` of `GlobalDynamics.map46` (Woodford (2003), eq. (4.6), p. 125): `β` is a
steady state iff the rule sets the rate to zero there, `φ(β) = 0` (`β ≠ 0`). -/
theorem map46_fixed_beta_iff {β : ℝ} (hβ : β ≠ 0) (φ : ℝ → ℝ) :
    GlobalDynamics.map46 β φ β = β ↔ φ β = 0 := by
  change β * (1 + φ β) = β ↔ φ β = 0
  constructor
  · intro h
    have := mul_left_cancel₀ hβ (h.trans (mul_one β).symm)
    linarith
  · intro h
    rw [h]
    ring

/-- Cochrane (2023), §20.3, p. 484 (E9, `ZLBWelfare.zlb_steady_state`) and (16.28), p. 379: any
steady state of the Chapter 16 map `GlobalDynamics.map46` at which the rule is at the bound,
`φ(Π) = 0`, is the zero-bound steady state `Π_L = β` of §20.3. -/
theorem zlb_fixed_point_eq_beta {β P : ℝ} {φ : ℝ → ℝ} (hfix : GlobalDynamics.map46 β φ P = P)
    (hφ : φ P = 0) : P = β :=
  ZLBWelfare.zlb_steady_state (i := φ P) hfix.symm hφ

/-- Cochrane (2023), §20.2.1, p. 472 (`ZLBRule`, the lower steady state `π = −u` with `i = 0`)
and §20.3, p. 484 (`Π_L = β`): with natural rate `u = −log β` (`β > 0`) and `log β` on the
zero-bound branch, `π = log β` is a steady state of the (20.2) map, the rule is at the bound
there, and `e^{log β} = β(1 + 0)` is the gross steady state `Π_L` of
`ZLBWelfare.zlb_steady_state`. -/
theorem zlb_steady_log {σ κ φ πs β : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hβ : 0 < β)
    (hk : Real.log β ≤ ZLBRule.kink φ πs) :
    ZLBRule.fmap σ κ φ πs (-Real.log β) (Real.log β) = Real.log β ∧
      ZLBRule.rule φ πs (Real.log β) = 0 ∧ Real.exp (Real.log β) = β := by
  have h := (ZLBRule.both_steady (σ := σ) (κ := κ) hφ hσκ (u := -Real.log β)
    (by rwa [neg_neg])).1
  rw [neg_neg] at h
  refine ⟨h, ?_, Real.exp_log hβ⟩
  have := (ZLBRule.kink_iff (π := Real.log β) (by linarith : (0 : ℝ) < φ)).2 hk
  unfold ZLBRule.rule
  exact max_eq_right this

end Cochrane.ZeroBound.Links

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links with Galí's and Woodford's treatments of the zero bound

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20: §20.1 (pp. 465–469),
§20.2.4 "Forward guidance" (pp. 478–480) and §20.3 (pp. 484–485), compared with Galí (2015),
§5.4 (pp. 144–152) and Woodford (2003), Chapter 6, §4.2 (pp. 427–435) and Proposition 6.3.

## Galí's commitment policy is delayed lift-off plus a glide path (Galí §5.4.2)

Galí's model (restated from the Galí Chapter 5 project): `π_t = βπ_{t+1} + κx_t`,
`x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1} − rⁿ_t)`, natural rate `−η` on `[0, t_Z]` and `ρ > 0` after.

* Zero-rate dynamics are a monotone backward map (`backStep_lt`, `zr_strict`, `zr_le`,
  `zr_lower`): a higher state at a later date gives a strictly higher state at every earlier date
  of a zero-rate spell.
* The discrete delayed-lift-off family `delayPath L` (rate `0` before `L`, the natural rate and
  `x = π = 0` from `L` on; the counterpart of `ForwardGuidance.delayPi`): `delay_isPath`,
  `delay_eq_disc` (lift-off at `t_Z + 1` is Galí's discretionary path), `delay_lt_of_lt`
  (strictly increasing in `L`, the counterpart of `ForwardGuidance.delay_pi0_strictMono`) and
  `delay_pi0_tendsto` (unbounded, the counterpart of `ForwardGuidance.delay_pi0_tendsto`).
* `comm_gt_delay`, `comm_gt_disc`, `comm_rates`: Galí's optimal commitment path (in the form of
  his algorithm, `ZLBCommitment.algorithm_verification`) lies strictly above the delayed-lift-off
  path with the same lift-off date, hence strictly above the discretionary path at EVERY date
  (higher `x_t` and `π_t`), keeps `i = 0 < rⁿ` on `(t_Z, t_C]`, and `comm_loss_lt`: if it is the
  commitment optimum, the discretionary path has strictly larger loss; `comm_loss_lt_alg`: the
  same from the algorithm's conditions alone, via Galí's verification theorem
  `algorithm_verification` (restated with its proof, KKT sufficiency `kkt_sufficient`).
* `xi1_eq`, `xi_pos_iff`, `longrun_price`: the precise condition for `ξ₁,t_C+1 > 0` (price level
  at lift-off below its long-run level `(βσ)⁻¹∑ξ₂ ≥ 0`); `comm_gt_disc_of_state` (dominance on
  the zero-rate spell from a positive lift-off state only); the exact point `cex_optimal`
  (`β = 9/10`, `κ = 1/10`, `ϑ = 1/819`, `σ = 1`, `ρ = 1/10`, `η = 1/100`, `t_Z = 0`), verified
  optimal, with `cex_liftoff_at_shock_end` (`t_C = t_Z`) and `cex_xi_neg` (`ξ₁,1 < 0`, output and
  inflation negative after lift-off): corrections to Galí p. 150.

## The discrete Werning family and forward guidance about `π_T`

* `wState c`: the rate is `0` during the trap and equal to the natural rate afterwards, with the
  bounded post-trap peg continuation `π_{t_Z+1+k} = λ₁⁻ᵏ c` (`λ₁` the root (5.6) of `ZLBPeg`).
  `w_isPath`, `w_bdd`, `w_unique` (**all** bounded paths with this rate path are members:
  a one-parameter family indexed by `c = π_{t_Z+1}`, like `WerningModel.bdd_path_iff`),
  `w_zero` (`c = 0` is Galí's discretionary path, the new-Keynesian selection `π_T = 0`).
* `w_sub`, `w_pi0_sub`: `π_t(c) − π_t(c') = λ₁^{t_Z+1−t}(c − c')`, the discrete
  `ForwardGuidance.dpi_dpiT`; `w_sensitivity_strictMono`, `w_sensitivity_tendsto`; and
  `sensitivity_tendsto_exp`: with period length `t/n`, `λ₁ⁿ → e^{λ^b t}`, the continuous-time
  sensitivity of `ForwardGuidance.dpi0_dpiT`.
* `comm_promise`: the commitment path's date-0 inflation equals that of exactly one member of the
  family, and its promise `c` is strictly positive; `comm_not_member` (if `t_C > t_Z`).

## Woodford's moment constraint versus Cochrane's pathwise bound (Woodford Prop. 6.9)

* `dAvg` (restated from the Woodford Chapter 6 project), `MomentFeasible` ((4.18)–(4.19)) and
  `PathwiseZLB` (`i_t ≥ 0` at every date and state, Cochrane §20.1).
* `pathwise_mean_nonneg`; `band_moment_feasible` (a pathwise band `a ≤ i ≤ b`, `0 ≤ a`,
  `(b − a)² ≤ 4(K − 1)a²` gives Woodford's constraint); `violation_freq_le` (Woodford's
  constraint bounds the discounted frequency of `i < 0` by `(K − 1)/K = 1/(1 + k²)`, a Cantelli
  bound; Cochrane's requires it to be `0`, `pathwise_violation_freq`);
  `pathwise_not_moment`, `moment_not_pathwise`, `neither_implies`: neither constraint implies the
  other (at Woodford's `k = 2.26`).

## The zero-bound steady state and Woodford's welfare loss

* `DispRec` (Woodford's (2.20), restated): at constant inflation `π` the dispersion converges to
  `ZLBWelfare.dispersion α π` (`disp_const_closed`, `disp_const_tendsto`,
  `disp_const_stationary`), and Woodford's discounted dispersion is
  `απ²/((1−α)(1−αβ))` plus a term independent of `π` (`disp_const_discounted`,
  `disp_const_avg`), so `woodford_zlb_better_iff`: Woodford's welfare criterion ranks `Π_L = β`
  above `Π*` iff `1 < βΠ*`, exactly as `ZLBWelfare.zlb_better_iff`.
* `gali_deflation_steady`: Galí's deflationary steady state `π = −ρ`, `i = 0` with `ρ = −log β`
  is Cochrane's `Π_L = β`, with the same output gap; `gali_deflation_worse`: it is strictly worse
  than Galí's target `π = 0`. `quadLoss_steady`: Woodford's quadratic loss at a steady state is
  `ZLBWelfare.ssLoss`.
-/

namespace Cochrane.ZeroBound.LinksGaliWoodford

open Filter Topology
open Cochrane.ZeroBound

/-! ## Galí's zero-bound model (restated from the Galí Chapter 5 project) -/

/-- Galí (2015), p. 145, restated from the Galí Chapter 5 project (`ZLBDiscretion.natRate`);
Cochrane (2023), §20.2.2, p. 474 (the trap): the natural rate, `−η` on `[0, t_Z]`, `ρ` after. -/
noncomputable def natRate (ρ η : ℝ) (tZ t : ℕ) : ℝ := if t ≤ tZ then -η else ρ

/-- Galí (2015), p. 145 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 474: the
natural rate on the shock interval. -/
theorem natRate_of_le {ρ η : ℝ} {tZ t : ℕ} (ht : t ≤ tZ) : natRate ρ η tZ t = -η := by
  simp [natRate, ht]

/-- Galí (2015), p. 145 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 474: the
natural rate after the shock interval. -/
theorem natRate_of_lt {ρ η : ℝ} {tZ t : ℕ} (ht : tZ < t) : natRate ρ η tZ t = ρ := by
  simp [natRate, Nat.not_le.mpr ht]

/-- Galí (2015), eq. (29), p. 145, restated from the Galí Chapter 5 project; Cochrane (2023),
eq. (5.2), p. 118: the deterministic Phillips curve `π_t = βπ_{t+1} + κx_t`. -/
def NKPC (β κ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : Prop := π t = β * π (t + 1) + κ * x t

/-- Galí (2015), eq. (30) and p. 152, restated from the Galí Chapter 5 project; Cochrane (2023),
eq. (5.1), p. 118: the rate implied by the IS curve, `i_t = rⁿ_t + π_{t+1} + σ(x_{t+1} − x_t)`. -/
noncomputable def impliedRate (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  rn t + π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), p. 146, restated from the Galí Chapter 5 project; Cochrane (2023), §20.1,
p. 467: `υ₁,t = x_{t+1} + (π_{t+1} + rⁿ_t)/σ`, the output gap at which the bound binds. -/
noncomputable def ups1 (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  x (t + 1) + (π (t + 1) + rn t) / σ

/-- Galí (2015), p. 146 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 467: the
implied rate is `σ(υ₁,t − x_t)`. -/
theorem impliedRate_eq {σ : ℝ} (hσ : σ ≠ 0) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = σ * (ups1 σ rn x π t - x t) := by
  unfold impliedRate ups1
  field_simp
  ring

/-- Galí (2015), eq. (34), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023),
§20.2.2, p. 475 (the model at a zero rate is a backward recursion): one backward step at a rate
`i_t = rⁿ_t + e`, `(x_t, π_t) = A(x_{t+1}, π_{t+1}) − B e` (`e = η` on a binding bound). -/
noncomputable def backStep (β κ σ e : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 / σ - e / σ, κ * s.1 + (β + κ / σ) * s.2 - κ * e / σ)

/-- Galí (2015), eq. (34), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023),
p. 475: `n` backward steps from the terminal state `s_T`. -/
noncomputable def backState (β κ σ η : ℝ) (sT : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sT
  | n + 1 => backStep β κ σ η (backState β κ σ η sT n)

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023), p. 475: the
path solving (34) backward on `[0, t_Z]` from `s_T` at `t_Z + 1`, equal to `s_T` after `t_Z`. -/
noncomputable def zlbPath (β κ σ η : ℝ) (tZ : ℕ) (sT : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η sT (tZ + 1 - t) else sT

/-- Galí (2015), eq. (34), p. 147 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 475: on `[0, t_Z]` the path obeys (34). -/
theorem zlbPath_of_le {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : t ≤ tZ) :
    zlbPath β κ σ η tZ sT t = backStep β κ σ η (zlbPath β κ σ η tZ sT (t + 1)) := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 := by omega
  simp only [ht, ↓reduceIte, e, backState]
  by_cases h : t + 1 ≤ tZ
  · simp only [h, ↓reduceIte]
  · have e2 : tZ + 1 - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e2, backState]

/-- Galí (2015), p. 147 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 475:
after `t_Z` the path is at its terminal state. -/
theorem zlbPath_of_lt {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : tZ < t) :
    zlbPath β κ σ η tZ sT t = sT := by
  simp [zlbPath, Nat.not_le.mpr ht]

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project (`ZLBDiscretion.discX`, the
discretionary equilibrium, `disc_exists`/`disc_unique` there); Cochrane (2023), p. 475: the
discretionary output gap, (34) on `[0, t_Z]` from `(0, 0)`, zero afterwards. -/
noncomputable def discX (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).1

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023), p. 475: the
discretionary inflation path, (34) on `[0, t_Z]` from `(0, 0)`, zero afterwards. -/
noncomputable def discPi (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).2

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project
(`ZLBCommitment.Feasible`); Cochrane (2023), §20.1, p. 465 (the bound `i ≥ 0`): the Phillips
curve and `x_t ≤ υ₁,t` (i.e. `i_t ≥ 0`) at every date. -/
def Feasible (β κ σ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  ∀ t, NKPC β κ x π t ∧ x t ≤ ups1 σ rn x π t

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project; Cochrane (2023), §20.3,
p. 485: the period loss `β^t (π_t² + ϑ x_t²)`. -/
noncomputable def lossTerm (β ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project; Cochrane (2023), p. 485: the
loss `∑ β^t (π_t² + ϑ x_t²)` (a `tsum`; `Optimal` requires summability). -/
noncomputable def loss (β ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x π t

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project
(`ZLBCommitment.Optimal`); Cochrane (2023), §20.2.4, p. 479 (optimal forward guidance): `(x, π)`
solves the commitment problem. -/
def Optimal (β κ σ ϑ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ Summable (lossTerm β ϑ x π) ∧
    ∀ y q, Feasible β κ σ rn y q → Summable (lossTerm β ϑ y q) → loss β ϑ x π ≤ loss β ϑ y q

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project; Cochrane (2023), p. 479: the
lag with initial condition `ξ₋₁ = 0`. -/
def lag (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => f t

/-- Galí (2015), eq. (36), p. 149, restated from the Galí Chapter 5 project; Cochrane (2023),
p. 479: `ϑ x_t − κ ξ₁,t + ξ₂,t − ξ₂,t−1/β = 0`. -/
def FOC36 (β κ ϑ : ℝ) (x ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  ϑ * x t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0

/-- Galí (2015), (14), p. 135, restated from the Galí Chapter 5 project
(`Commitment.gam`); Cochrane (2023), p. 479: `γ = ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), (15), p. 136, restated from the Galí Chapter 5 project
(`Commitment.del`); Cochrane (2023), p. 479: `δ = (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), (14), p. 135 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), (14), p. 135 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `γ(1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), (14)–(15), pp. 135–136 (restated from the Galí Chapter 5 project); Cochrane
(2023), p. 479: `γ(1 + β) < 1` iff `κ ≠ 0`. -/
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

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `δ < 1` iff `κ ≠ 0`. -/
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
    have h1 : 1 - 2 * g * β < Real.sqrt (1 - 4 * β * g ^ 2) := by linarith
    have h2 := (Real.lt_sqrt h0).1 h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hgb.le (sub_nonneg.2 hc)]
  · intro h
    have h2 : (1 - 2 * g * β) ^ 2 < 1 - 4 * β * g ^ 2 := by nlinarith
    have := (Real.lt_sqrt h0).2 h2
    linarith

/-- Galí (2015), eq. (42), p. 150, restated from the Galí Chapter 5 project
(`ZLBCommitment.postX`); Cochrane (2023), §20.2.4, p. 479 (the glide path): after lift-off
`x_{t_C+2+k} = κ δ^{k+1} ξ / ϑ`, `ξ = ξ₁,t_C+1`. -/
noncomputable def postX (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := κ * del β κ ϑ ^ (k + 1) * ξ / ϑ

/-- Galí (2015), eq. (43), p. 150, restated from the Galí Chapter 5 project
(`ZLBCommitment.postPi`); Cochrane (2023), p. 479: `π_{t_C+2+k} = (1 − δ) δ^k ξ`. -/
noncomputable def postPi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ :=
  (1 - del β κ ϑ) * del β κ ϑ ^ k * ξ

/-- Galí (2015), eq. (42), p. 150 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: with `ξ > 0` the output gap is positive after lift-off. -/
theorem post_eq42_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : 0 < ξ)
    (k : ℕ) : 0 < postX β κ ϑ ξ k := by
  have := del_pos (κ := κ) hβ hϑ
  unfold postX; positivity

/-- Galí (2015), eq. (43), p. 150 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: with `ξ > 0` inflation is positive after lift-off. -/
theorem post_eq43_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hξ : 0 < ξ) (k : ℕ) : 0 < postPi β κ ϑ ξ k := by
  have h0 := del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - del β κ ϑ := by
    linarith [(del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold postPi; positivity

/-! ## Zero-rate dynamics are a monotone backward map -/

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475: a backward step at rate
`i_t = rⁿ_t + e` gives the Phillips curve and that rate (generalising the Galí Chapter 5
project's `backStep_nkpc_rate`, `e = −rⁿ_t`). -/
theorem backStep_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = rn t + e := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hx]; field_simp; ring

/-- Galí (2015), eqs. (29)–(30), p. 145; Cochrane (2023), p. 475: conversely the Phillips curve
and the rate `i_t = rⁿ_t + e` give the backward step. -/
theorem backStep_of_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (hN : NKPC β κ x π t) (hi : impliedRate σ rn x π t = rn t + e) :
    (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1)) := by
  unfold NKPC at hN
  unfold impliedRate at hi
  have hx : x t = x (t + 1) + π (t + 1) / σ - e / σ := by
    have h2 : σ * x t = σ * x (t + 1) + π (t + 1) - e := by linarith
    field_simp
    linarith
  rw [Prod.ext_iff]
  simp only [backStep]
  refine ⟨hx, ?_⟩
  rw [hN, hx]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 (backward induction over a trap of finite length): a
property holding at `N` and propagating from `t + 1` to `t` for `t < N` holds on `[0, N]`. -/
theorem down_ind {P : ℕ → Prop} {N : ℕ} (hN : P N) (hstep : ∀ t, t < N → P (t + 1) → P t) :
    ∀ t, t ≤ N → P t := by
  have key : ∀ n t, t + n = N → P t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      obtain rfl : t = N := by omega
      exact hN
    | succ n ih => intro t ht; exact hstep t (by omega) (ih (t + 1) (by omega))
  intro t ht
  exact key (N - t) t (by omega)

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: the difference of two backward
steps (same forcing), first component: `Δx_t = Δx_{t+1} + Δπ_{t+1}/σ`. -/
theorem backStep_sub_fst (β κ σ e : ℝ) (s s' : ℝ × ℝ) :
    (backStep β κ σ e s).1 - (backStep β κ σ e s').1 = (s.1 - s'.1) + (s.2 - s'.2) / σ := by
  simp only [backStep]; ring

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: the difference of two backward
steps, second component: `Δπ_t = κΔx_{t+1} + (β + κ/σ)Δπ_{t+1}`. -/
theorem backStep_sub_snd (β κ σ e : ℝ) (s s' : ℝ × ℝ) :
    (backStep β κ σ e s).2 - (backStep β κ σ e s').2 =
      κ * (s.1 - s'.1) + (β + κ / σ) * (s.2 - s'.2) := by
  simp only [backStep]; ring

/-- Galí (2015), p. 147 (`A`, `B` entrywise positive); Cochrane (2023), §20.2.4, p. 479 (higher
promised future inflation raises current inflation and output): a weakly higher next state,
strictly higher in one component, gives a strictly higher current state in both. -/
theorem backStep_lt {β κ σ e : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {s s' : ℝ × ℝ}
    (h1 : s'.1 ≤ s.1) (h2 : s'.2 ≤ s.2) (hs : s'.1 < s.1 ∨ s'.2 < s.2) :
    (backStep β κ σ e s').1 < (backStep β κ σ e s).1 ∧
      (backStep β κ σ e s').2 < (backStep β κ σ e s).2 := by
  have e1 := backStep_sub_fst β κ σ e s s'
  have e2 := backStep_sub_snd β κ σ e s s'
  have hc : 0 < β + κ / σ := by positivity
  have ha : 0 ≤ s.1 - s'.1 := by linarith
  have hb : 0 ≤ s.2 - s'.2 := by linarith
  have hbσ : 0 ≤ (s.2 - s'.2) / σ := div_nonneg hb hσ.le
  rcases hs with h | h
  · have ha' : 0 < s.1 - s'.1 := by linarith
    have := mul_pos hκ ha'
    have := mul_nonneg hc.le hb
    constructor <;> linarith
  · have hb' : 0 < s.2 - s'.2 := by linarith
    have := div_pos hb' hσ
    have := mul_pos hc hb'
    have := mul_nonneg hκ.le ha
    constructor <;> linarith

/-- Galí (2015), p. 147; Cochrane (2023), p. 479: a weakly higher next state gives a weakly
higher current state. -/
theorem backStep_le {β κ σ e : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {s s' : ℝ × ℝ}
    (h1 : s'.1 ≤ s.1) (h2 : s'.2 ≤ s.2) :
    (backStep β κ σ e s').1 ≤ (backStep β κ σ e s).1 ∧
      (backStep β κ σ e s').2 ≤ (backStep β κ σ e s).2 := by
  have e1 := backStep_sub_fst β κ σ e s s'
  have e2 := backStep_sub_snd β κ σ e s s'
  have hc : 0 < β + κ / σ := by positivity
  have ha : 0 ≤ s.1 - s'.1 := by linarith
  have hb : 0 ≤ s.2 - s'.2 := by linarith
  have := div_nonneg hb hσ.le
  have := mul_nonneg hκ.le ha
  have := mul_nonneg hc.le hb
  constructor <;> linarith

/-- Cochrane (2023), §20.2.4, p. 479 (discrete form of "promises … have enormous power"):
two paths obeying the same zero-rate backward recursion before `N`, with the state of `p` at `N`
weakly above that of `q` and strictly above in one component, satisfy `q_t < p_t` in both
components at every `t < N`. -/
theorem zr_strict {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {e : ℕ → ℝ} {N : ℕ}
    {p q : ℕ → ℝ × ℝ} (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : (q N).1 ≤ (p N).1) (h2 : (q N).2 ≤ (p N).2)
    (hs : (q N).1 < (p N).1 ∨ (q N).2 < (p N).2) (t : ℕ) (ht : t < N) :
    (q t).1 < (p t).1 ∧ (q t).2 < (p t).2 := by
  refine down_ind (P := fun t => t < N → (q t).1 < (p t).1 ∧ (q t).2 < (p t).2)
    (fun h => absurd h (lt_irrefl N)) (fun s hs' ih _ => ?_) t ht.le ht
  rw [hp s hs', hq s hs']
  rcases Nat.lt_or_ge (s + 1) N with h | h
  · obtain ⟨a, b⟩ := ih h
    exact backStep_lt hβ hκ hσ a.le b.le (Or.inl a)
  · obtain rfl : s + 1 = N := by omega
    exact backStep_lt hβ hκ hσ h1 h2 hs

/-- Cochrane (2023), §20.2.4, p. 479: the weak version of `zr_strict`, on `[0, N]`. -/
theorem zr_le {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {e : ℕ → ℝ} {N : ℕ}
    {p q : ℕ → ℝ × ℝ} (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : (q N).1 ≤ (p N).1) (h2 : (q N).2 ≤ (p N).2) (t : ℕ) (ht : t ≤ N) :
    (q t).1 ≤ (p t).1 ∧ (q t).2 ≤ (p t).2 := by
  refine down_ind (P := fun t => (q t).1 ≤ (p t).1 ∧ (q t).2 ≤ (p t).2) ⟨h1, h2⟩
    (fun s hs ih => ?_) t ht
  rw [hp s hs, hq s hs]
  exact backStep_le hβ hκ hσ ih.1 ih.2

/-- Cochrane (2023), §20.2.4, p. 479: two paths obeying the same zero-rate recursion before `N`
and agreeing at `N` agree on `[0, N]` (the trap path is pinned by its end state). -/
theorem zr_eq {β κ σ : ℝ} {e : ℕ → ℝ} {N : ℕ} {p q : ℕ → ℝ × ℝ}
    (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1))) (hN : p N = q N) (t : ℕ)
    (ht : t ≤ N) : p t = q t := by
  refine down_ind (P := fun t => p t = q t) hN (fun s hs ih => ?_) t ht
  rw [hp s hs, hq s hs, ih]

/-- Cochrane (2023), §20.2.4, p. 479 (quantitative form): if `p` exceeds `q` at `N` by at least
`m ≥ 0` in output and weakly in inflation, then at every `t < N` it exceeds `q` by at least `m` in
output and `κ m` in inflation. -/
theorem zr_lower {β κ σ m : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hm : 0 ≤ m)
    {e : ℕ → ℝ} {N : ℕ} {p q : ℕ → ℝ × ℝ}
    (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : m ≤ (p N).1 - (q N).1) (h2 : (q N).2 ≤ (p N).2) (t : ℕ) (ht : t < N) :
    m ≤ (p t).1 - (q t).1 ∧ κ * m ≤ (p t).2 - (q t).2 := by
  have hc : 0 < β + κ / σ := by positivity
  have key := down_ind (P := fun t => m ≤ (p t).1 - (q t).1 ∧ 0 ≤ (p t).2 - (q t).2 ∧
      (t < N → κ * m ≤ (p t).2 - (q t).2)) ⟨h1, by linarith, fun h => absurd h (lt_irrefl N)⟩
    (fun s hs ih => by
      obtain ⟨a, b, -⟩ := ih
      have e1 := backStep_sub_fst β κ σ (e s) (p (s + 1)) (q (s + 1))
      have e2 := backStep_sub_snd β κ σ (e s) (p (s + 1)) (q (s + 1))
      rw [← hp s hs, ← hq s hs] at e1 e2
      have := div_nonneg b hσ.le
      have := mul_le_mul_of_nonneg_left a hκ.le
      have := mul_nonneg hc.le b
      have := mul_nonneg hκ.le hm
      exact ⟨by linarith, by linarith, fun _ => by linarith⟩) t ht.le
  exact ⟨key.1, key.2.2 ht⟩

/-- Cochrane (2023), §20.2.4, p. 479: Galí's model is feasible if the Phillips curve holds
and the implied rate is nonnegative at every date (restated from the Galí Chapter 5 project's
`ZLBCommitment.feasible_iff`, one direction). -/
theorem feasible_of_rate {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ}
    (h : ∀ t, NKPC β κ x π t ∧ 0 ≤ impliedRate σ rn x π t) : Feasible β κ σ rn x π := by
  intro t
  refine ⟨(h t).1, ?_⟩
  have := (h t).2
  rw [impliedRate_eq hσ.ne'] at this
  have := (mul_nonneg_iff_of_pos_left hσ).mp this
  linarith

/-! ## Zero-rate paths and the discrete delayed-lift-off family -/

/-- Cochrane (2023), §20.2.4, p. 479: `n` backward zero-rate steps from the state `s_L` at the
lift-off date `L`, with date-dependent forcing `e` (the step from `L − n` to `L − n − 1`). -/
noncomputable def zrAux (β κ σ : ℝ) (e : ℕ → ℝ) (L : ℕ) (sL : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sL
  | n + 1 => backStep β κ σ (e (L - (n + 1))) (zrAux β κ σ e L sL n)

/-- Cochrane (2023), §20.2.4, p. 479: the path that solves the backward recursion with forcing
`e` before `L` and sits at `s_L` from `L` on. -/
noncomputable def zrPath (β κ σ : ℝ) (e : ℕ → ℝ) (L : ℕ) (sL : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if L ≤ t then sL else zrAux β κ σ e L sL (L - t)

/-- Cochrane (2023), §20.2.4, p. 479: before `L` the path obeys the backward recursion. -/
theorem zrPath_of_lt {β κ σ : ℝ} {e : ℕ → ℝ} {L t : ℕ} {sL : ℝ × ℝ} (ht : t < L) :
    zrPath β κ σ e L sL t = backStep β κ σ (e t) (zrPath β κ σ e L sL (t + 1)) := by
  unfold zrPath
  have h1 : ¬ L ≤ t := by omega
  have e1 : L - t = (L - (t + 1)) + 1 := by omega
  have e2 : L - (L - (t + 1) + 1) = t := by omega
  simp only [h1, ↓reduceIte, e1, zrAux, e2]
  by_cases h : L ≤ t + 1
  · have e3 : L - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e3, zrAux]
  · simp only [h, ↓reduceIte]

/-- Cochrane (2023), §20.2.4, p. 479: from `L` on the path is at `s_L`. -/
theorem zrPath_of_ge {β κ σ : ℝ} {e : ℕ → ℝ} {L t : ℕ} {sL : ℝ × ℝ} (ht : L ≤ t) :
    zrPath β κ σ e L sL t = sL := by
  simp [zrPath, ht]

/-- Cochrane (2023), §20.2.4, p. 479 (delayed lift-off, Woodford 2012, Werning 2012), in Galí's
discrete model: the rate is `0` before the lift-off date `L` and equal to the natural rate from
`L` on, with `x = π = 0` from `L` on (the discrete counterpart of `ForwardGuidance.delayPi`,
whose `π_L = 0`). -/
noncomputable def delayPath (β κ σ ρ η : ℝ) (tZ L : ℕ) : ℕ → ℝ × ℝ :=
  zrPath β κ σ (fun t => -natRate ρ η tZ t) L (0, 0)

/-- Cochrane (2023), §20.2.4, p. 479: before lift-off the delayed path obeys the zero-rate
recursion. -/
theorem delay_step {β κ σ ρ η : ℝ} {tZ L t : ℕ} (ht : t < L) :
    delayPath β κ σ ρ η tZ L t =
      backStep β κ σ (-natRate ρ η tZ t) (delayPath β κ σ ρ η tZ L (t + 1)) :=
  zrPath_of_lt ht

/-- Cochrane (2023), §20.2.4, p. 479: from lift-off on, `x = π = 0`. -/
theorem delay_after {β κ σ ρ η : ℝ} {tZ L t : ℕ} (ht : L ≤ t) :
    delayPath β κ σ ρ η tZ L t = (0, 0) :=
  zrPath_of_ge ht

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_isPath`, discrete): the delayed
lift-off path satisfies the Phillips curve at every date, has `i_t = 0` before `L` and
`i_t = ρ = rⁿ_t` from `L ≥ t_Z + 1` on; with `ρ ≥ 0` it is feasible (`i ≥ 0`). -/
theorem delay_isPath {β κ σ ρ η : ℝ} (hσ : 0 < σ) {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    (∀ t, NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t) ∧
      (∀ t, t < L → impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = 0) ∧
      (∀ t, L ≤ t → impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = ρ) := by
  have hlt : ∀ t, t < L → NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = 0 := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (delayPath β κ σ ρ η tZ L s).1)
      (π := fun s => (delayPath β κ σ ρ η tZ L s).2) (t := t) hσ.ne' (delay_step ht)
    exact ⟨h.1, by rw [h.2]; ring⟩
  have hge : ∀ t, L ≤ t → NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = ρ := by
    intro t ht
    have a := delay_after (β := β) (κ := κ) (σ := σ) (ρ := ρ) (η := η) (tZ := tZ) ht
    have b := delay_after (β := β) (κ := κ) (σ := σ) (ρ := ρ) (η := η) (tZ := tZ)
      (show L ≤ t + 1 by omega)
    refine ⟨?_, ?_⟩
    · simp only [NKPC, a, b]; ring
    · simp only [impliedRate, a, b, natRate_of_lt (show tZ < t by omega)]; ring
  refine ⟨fun t => ?_, fun t ht => (hlt t ht).2, fun t ht => (hge t ht).2⟩
  rcases Nat.lt_or_ge t L with h | h
  · exact (hlt t h).1
  · exact (hge t h).1

/-- Cochrane (2023), §20.2.4, p. 479: with `ρ ≥ 0` the delayed lift-off path is feasible in
Galí's sense (Phillips curve and `i ≥ 0`). -/
theorem delay_feasible {β κ σ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) {tZ L : ℕ}
    (hL : tZ + 1 ≤ L) :
    Feasible β κ σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
      (fun s => (delayPath β κ σ ρ η tZ L s).2) := by
  obtain ⟨h1, h2, h3⟩ := delay_isPath (β := β) (κ := κ) (ρ := ρ) (η := η) hσ hL
  refine feasible_of_rate hσ fun t => ⟨h1 t, ?_⟩
  rcases Nat.lt_or_ge t L with h | h
  · rw [h2 t h]
  · rw [h3 t h]; exact hρ

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 147: lift-off at the end of the shock,
`L = t_Z + 1`, is Galí's discretionary path (`discX`, `discPi`): the new-Keynesian selection
"rates rise as soon as the natural rate does, with no promised inflation". -/
theorem delay_eq_disc (β κ σ ρ η : ℝ) (tZ t : ℕ) :
    delayPath β κ σ ρ η tZ (tZ + 1) t = zlbPath β κ σ η tZ (0, 0) t := by
  rcases Nat.lt_or_ge tZ t with h | h
  · rw [delay_after (by omega), zlbPath_of_lt h]
  · refine zr_eq (e := fun t => -natRate ρ η tZ t) (N := tZ + 1)
      (fun s hs => delay_step hs) (fun s hs => ?_) ?_ t (by omega)
    · rw [natRate_of_le (by omega : s ≤ tZ), neg_neg]
      exact zlbPath_of_le (by omega)
    · rw [delay_after le_rfl, zlbPath_of_lt (by omega)]

/-- Cochrane (2023), §20.2.4, p. 479 ("a policy that commits to delaying an interest-rate rise",
discrete): postponing lift-off by one period, from `L ≥ t_Z + 1` to `L + 1`, raises output and
inflation strictly at every date `t ≤ L` and leaves them unchanged after. -/
theorem delay_succ {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    (∀ t, t ≤ L → (delayPath β κ σ ρ η tZ L t).1 < (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 < (delayPath β κ σ ρ η tZ (L + 1) t).2) ∧
    ∀ t, (delayPath β κ σ ρ η tZ L t).1 ≤ (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 ≤ (delayPath β κ σ ρ η tZ (L + 1) t).2 := by
  have hL0 : delayPath β κ σ ρ η tZ L L = (0, 0) := delay_after le_rfl
  have hL1 : delayPath β κ σ ρ η tZ (L + 1) L = (ρ / σ, κ * ρ / σ) := by
    rw [delay_step (by omega), delay_after le_rfl, natRate_of_lt (by omega)]
    simp only [backStep]
    ext <;> simp only <;> ring
  have hpos : 0 < ρ / σ := div_pos hρ hσ
  have hpos2 : 0 < κ * ρ / σ := by positivity
  have hstrict : ∀ t, t ≤ L → (delayPath β κ σ ρ η tZ L t).1 <
      (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 < (delayPath β κ σ ρ η tZ (L + 1) t).2 := by
    intro t ht
    rcases Nat.lt_or_ge t L with h | h
    · refine zr_strict hβ hκ hσ (e := fun t => -natRate ρ η tZ t) (N := L)
        (fun s hs => delay_step (by omega)) (fun s hs => delay_step hs) ?_ ?_ ?_ t h
      · rw [hL0, hL1]; exact hpos.le
      · rw [hL0, hL1]; exact hpos2.le
      · rw [hL0, hL1]; exact Or.inl hpos
    · obtain rfl : t = L := by omega
      rw [hL0, hL1]
      exact ⟨hpos, hpos2⟩
  refine ⟨hstrict, fun t => ?_⟩
  rcases Nat.lt_or_ge L t with h | h
  · rw [delay_after h.le, delay_after (by omega)]
    exact ⟨le_rfl, le_rfl⟩
  · exact ⟨(hstrict t h).1.le, (hstrict t h).2.le⟩

/-- Cochrane (2023), §20.2.4, p. 479: a later lift-off gives a weakly higher path at every
date. -/
theorem delay_le_of_le {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L1 L2 : ℕ} (hL1 : tZ + 1 ≤ L1) (h12 : L1 ≤ L2) (t : ℕ) :
    (delayPath β κ σ ρ η tZ L1 t).1 ≤ (delayPath β κ σ ρ η tZ L2 t).1 ∧
      (delayPath β κ σ ρ η tZ L1 t).2 ≤ (delayPath β κ σ ρ η tZ L2 t).2 := by
  obtain ⟨n, rfl⟩ : ∃ n, L2 = L1 + n := ⟨L2 - L1, by omega⟩
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have h := (delay_succ (η := η) hβ hκ hσ hρ (tZ := tZ) (L := L1 + n) (by omega)).2 t
    rw [← add_assoc]
    exact ⟨(ih (by omega)).1.trans h.1, (ih (by omega)).2.trans h.2⟩

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_pi0_strictMono`, discrete):
**output and inflation are strictly increasing in the lift-off date** at every date before the
later lift-off. -/
theorem delay_lt_of_lt {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L1 L2 t : ℕ} (hL1 : tZ + 1 ≤ L1) (h12 : L1 < L2) (ht : t < L2) :
    (delayPath β κ σ ρ η tZ L1 t).1 < (delayPath β κ σ ρ η tZ L2 t).1 ∧
      (delayPath β κ σ ρ η tZ L1 t).2 < (delayPath β κ σ ρ η tZ L2 t).2 := by
  obtain ⟨L, rfl⟩ : ∃ L, L2 = L + 1 := ⟨L2 - 1, by omega⟩
  have a := delay_le_of_le (η := η) hβ hκ hσ hρ hL1 (show L1 ≤ L by omega) t
  have b := (delay_succ (η := η) hβ hκ hσ hρ (tZ := tZ) (L := L) (by omega)).1 t (by omega)
  exact ⟨a.1.trans_lt b.1, a.2.trans_lt b.2⟩

/-- Cochrane (2023), §20.2.4, p. 479: between the end of the shock and lift-off (rate `0`
below the natural rate `ρ`), output is at least `(L − t)ρ/σ` and inflation is nonnegative. -/
theorem delay_growth {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {tZ L t : ℕ} (htZ : tZ + 1 ≤ t) (htL : t ≤ L) :
    ((L : ℝ) - t) * ρ / σ ≤ (delayPath β κ σ ρ η tZ L t).1 ∧
      0 ≤ (delayPath β κ σ ρ η tZ L t).2 := by
  have hc : 0 < β + κ / σ := by positivity
  refine down_ind (N := L) (P := fun t => tZ + 1 ≤ t → ((L : ℝ) - t) * ρ / σ ≤
      (delayPath β κ σ ρ η tZ L t).1 ∧ 0 ≤ (delayPath β κ σ ρ η tZ L t).2)
    (fun _ => by rw [delay_after le_rfl]; simp) (fun s hs ih hs1 => ?_) t htL htZ
  obtain ⟨a, b⟩ := ih (by omega)
  rw [delay_step hs, natRate_of_lt (by omega)]
  simp only [backStep]
  have hm : 0 ≤ ((L : ℝ) - ((s + 1 : ℕ) : ℝ)) * ρ / σ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hs
    have : 0 ≤ (L : ℝ) - ((s + 1 : ℕ) : ℝ) := by linarith
    positivity
  have e : ((L : ℝ) - s) * ρ / σ = ((L : ℝ) - ((s + 1 : ℕ) : ℝ)) * ρ / σ + ρ / σ := by
    push_cast; ring
  have h1 := div_nonneg b hσ.le
  have h2 := mul_nonneg hκ.le (hm.trans a)
  have h3 := mul_nonneg hc.le b
  have h4 : 0 ≤ κ * ρ / σ := by positivity
  constructor
  · rw [e]
    have : -(ρ / σ) = -ρ / σ := by ring
    linarith
  · have : -(κ * -ρ / σ) = κ * ρ / σ := by ring
    linarith

/-- Cochrane (2023), §20.2.4, p. 479 (discrete form of `ForwardGuidance.delay_pi0_tendsto`):
with lift-off at `L ≥ t_Z + 1`, date-0 inflation exceeds the discretionary one by at least
`κ(L − t_Z − 1)ρ/σ`, and output by at least `(L − t_Z − 1)ρ/σ`. -/
theorem delay_lower {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    discX β κ σ η tZ 0 + ((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ ≤ (delayPath β κ σ ρ η tZ L 0).1 ∧
      discPi β κ σ η tZ 0 + κ * (((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ) ≤
        (delayPath β κ σ ρ η tZ L 0).2 := by
  have hm : 0 ≤ ((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ := by
    have : ((tZ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hL
    have : 0 ≤ (L : ℝ) - (tZ + 1 : ℕ) := by linarith
    positivity
  have hg := delay_growth (β := β) (η := η) hβ hκ hσ hρ (t := tZ + 1) le_rfl hL
  have hd : delayPath β κ σ ρ η tZ (tZ + 1) (tZ + 1) = (0, 0) := delay_after le_rfl
  have h := zr_lower hβ hκ hσ hm (e := fun t => -natRate ρ η tZ t) (N := tZ + 1)
    (p := delayPath β κ σ ρ η tZ L) (q := delayPath β κ σ ρ η tZ (tZ + 1))
    (fun s hs => delay_step (by omega)) (fun s hs => delay_step hs)
    (by rw [hd]; simpa using hg.1) (by rw [hd]; exact hg.2) 0 (by omega)
  rw [delay_eq_disc] at h
  exact ⟨by unfold discX; linarith [h.1], by unfold discPi; linarith [h.2]⟩

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_pi0_tendsto`, discrete): **a long
enough delay produces any initial inflation** — date-0 inflation tends to `+∞` as the lift-off
date `L → ∞` (`ρ > 0`). -/
theorem delay_pi0_tendsto {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    (tZ : ℕ) : Tendsto (fun L : ℕ => (delayPath β κ σ ρ η tZ L 0).2) atTop atTop := by
  set c := discPi β κ σ η tZ 0 - κ * ((tZ + 1 : ℕ) : ℝ) * ρ / σ
  have hk : 0 < κ * ρ / σ := by positivity
  have hE : Tendsto (fun L : ℕ => c + κ * ρ / σ * (L : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop c (tendsto_natCast_atTop_atTop.const_mul_atTop hk)
  refine tendsto_atTop_mono' atTop ?_ hE
  filter_upwards [eventually_ge_atTop (tZ + 1)] with L hL
  have := (delay_lower (η := η) hβ hκ hσ hρ.le hL).2
  have e : c + κ * ρ / σ * (L : ℝ) = discPi β κ σ η tZ 0 +
      κ * (((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ) := by
    simp only [c]; ring
  rw [e]
  exact this

/-! ## Galí's commitment path is delayed lift-off plus a glide path -/

/-- Galí (2015), eqs. (48)–(49), p. 151; Cochrane (2023), §20.2.4, p. 479: on the announced
zero-rate spell `[0, t_C]` the commitment path obeys the zero-rate recursion with forcing
`−rⁿ_t` (the same recursion as the delayed-lift-off family). -/
theorem comm_step {β κ σ ρ η : ℝ} {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (t : ℕ) (ht : t < tC + 1) :
    (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)) := by
  rcases le_or_gt t tZ with h | h
  · rw [natRate_of_le h, neg_neg]; exact h48 t h
  · rw [natRate_of_lt h]; exact h49 t h (by omega)

/-- Galí (2015), eqs. (36), (29), (43), pp. 149–150; Cochrane (2023), §20.2.4, p. 479 (the
promise at lift-off): at the lift-off date `t_C + 1` of Galí's algorithm, with `ξ₂,t_C ≥ 0`,
`ξ₂,t_C+1 = 0` and `ξ₁,t_C+1 > 0`, both output and inflation are strictly positive. -/
theorem comm_liftoff_pos {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ} (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) (hsign : 0 ≤ ξ2 tC)
    (hξ : 0 < ξ1 (tC + 1)) : 0 < x (tC + 1) ∧ 0 < π (tC + 1) := by
  have hl : lag ξ2 (tC + 1) = ξ2 tC := rfl
  unfold FOC36 at h36
  rw [hl, hξ2] at h36
  have h1 : ϑ * x (tC + 1) = κ * ξ1 (tC + 1) + ξ2 tC / β := by linarith
  have h2 : 0 < κ * ξ1 (tC + 1) + ξ2 tC / β :=
    add_pos_of_pos_of_nonneg (mul_pos hκ hξ) (div_nonneg hsign hβ.le)
  have hx : 0 < x (tC + 1) := (mul_pos_iff_of_pos_left hϑ).mp (h1 ▸ h2)
  refine ⟨hx, ?_⟩
  unfold NKPC at h46
  have hp := post_eq43_pos hβ hβ1 hκ hϑ hξ 0
  rw [← hπ2] at hp
  rw [h46]
  have h3 : 0 < β * π (tC + 1 + 1) := mul_pos hβ hp
  exact add_pos h3 (mul_pos hκ hx)

/-- Cochrane (2023), §20.2.4, p. 479 (forward guidance = delayed lift-off **plus** a promise),
for Galí's (2015) optimal commitment path, pp. 149–152: on `[0, t_C + 1]` the commitment path
lies strictly above the delayed-lift-off path with the same lift-off date `t_C + 1` (both
components). Both obey the same zero-rate recursion; they differ only in the promise at lift-off,
`(x, π)_{t_C+1} > 0` (`comm_liftoff_pos`) against `0`. -/
theorem comm_gt_delay {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) (hsign : 0 ≤ ξ2 tC)
    (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) (ht : t ≤ tC + 1) :
    (delayPath β κ σ ρ η tZ (tC + 1) t).1 < x t ∧ (delayPath β κ σ ρ η tZ (tC + 1) t).2 < π t := by
  obtain ⟨hx, hp⟩ := comm_liftoff_pos hβ hβ1 hκ hϑ h36 h46 hξ2 hπ2 hsign hξ
  have hd : delayPath β κ σ ρ η tZ (tC + 1) (tC + 1) = (0, 0) := delay_after le_rfl
  rcases Nat.lt_or_ge t (tC + 1) with h | h
  · exact zr_strict hβ.le hκ hσ (e := fun t => -natRate ρ η tZ t) (N := tC + 1)
      (p := fun t => (x t, π t)) (fun s hs => comm_step h48 h49 s hs)
      (fun s hs => delay_step hs) (by rw [hd]; exact hx.le) (by rw [hd]; exact hp.le)
      (by rw [hd]; exact Or.inl hx) t h
  · obtain rfl : t = tC + 1 := by omega
    rw [hd]
    exact ⟨hx, hp⟩

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2, pp. 148–152: **the optimal
commitment path raises output and inflation at every date relative to discretion**. Assume the
form of the path delivered by Galí's algorithm (`ZLBCommitment.algorithm_verification`):
(48)–(49) on the zero-rate spell `[0, t_C]` with `t_C ≥ t_Z`, the FOC (36) and the Phillips curve at
`t_C + 1`, `ξ₂,t_C ≥ 0 = ξ₂,t_C+1`, `ξ₁,t_C+1 > 0`, and the closed form (42)–(43) after lift-off,
we get `discX_t < x_t` and `discPi_t < π_t` for every `t`. -/
theorem comm_gt_disc {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) :
    discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t := by
  have hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0 := by simpa using (hpost 0).2
  rcases Nat.lt_or_ge t (tC + 2) with h | h
  · have a := comm_gt_delay hβ hβ1 hκ hσ hϑ (ρ := ρ) (η := η) (tZ := tZ) h48 h49 h36 h46 hξ2
      hπ2 hsign hξ t (by omega)
    have b := delay_le_of_le (η := η) hβ.le hκ hσ hρ (tZ := tZ) le_rfl
      (show tZ + 1 ≤ tC + 1 by omega) t
    rw [delay_eq_disc] at b
    exact ⟨b.1.trans_lt a.1, b.2.trans_lt a.2⟩
  · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
    have hz := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ)))
      (show tZ < tC + k + 2 by omega)
    unfold discX discPi
    rw [hz, (hpost k).1, (hpost k).2]
    exact ⟨post_eq42_pos hβ hκ hϑ hξ k, post_eq43_pos hβ hβ1 hκ hϑ hξ k⟩

/-- Cochrane (2023), §20.2.4, p. 479 ("commits to delaying an interest-rate rise"), Galí (2015),
pp. 151–152: the commitment path keeps `i = 0` on `[0, t_C]`; on `(t_Z, t_C]` this is strictly
below the natural rate `ρ` (the delayed lift-off), whereas the discretionary rate equals the
natural rate `ρ` at every date after `t_Z`. -/
theorem comm_rates {β κ σ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) :
    (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tZ < t → t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t < natRate ρ η tZ t) ∧
      ∀ t, tZ < t →
        impliedRate σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) t = ρ := by
  have h0 : ∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0 := by
    intro t ht
    have := (backStep_rate (rn := natRate ρ η tZ) hσ.ne' (comm_step h48 h49 t (by omega))).2
    rw [this]; ring
  refine ⟨h0, fun t h1 h2 => ?_, fun t ht => ?_⟩
  · rw [h0 t h2, natRate_of_lt h1]; exact hρ
  · have a := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ))) ht
    have b := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ)))
      (show tZ < t + 1 by omega)
    simp only [impliedRate, discX, discPi, a, b, natRate_of_lt ht]
    ring

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 485: a
nonnegative summable sequence with nonpositive sum vanishes. -/
theorem eq_zero_of_tsum_nonpos {D : ℕ → ℝ} (h0 : ∀ t, 0 ≤ D t) (hs : Summable D)
    (h : ∑' t, D t ≤ 0) (t : ℕ) : D t = 0 :=
  le_antisymm ((hs.le_tsum t fun j _ => h0 j).trans h) (h0 t)

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 485:
`β^t (a² + ϑ b²) = 0` forces `a = b = 0`. -/
theorem sq_terms_zero {β ϑ a b : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (t : ℕ)
    (h : β ^ t * (a ^ 2 + ϑ * b ^ 2) = 0) : a = 0 ∧ b = 0 := by
  have hp : 0 < β ^ t := pow_pos hβ t
  have h2 : a ^ 2 + ϑ * b ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hp.ne'
    · exact h'
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hϑ.le (sq_nonneg b)]
  have hb : ϑ * b ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp hb).resolve_left hϑ.ne')⟩

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project
(`ZLBCommitment.optimal_unique`); Cochrane (2023), §20.2.4, p. 479: strict convexity — two
optimal paths of the commitment problem coincide. -/
theorem optimal_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x1 π1 x2 π2 : ℕ → ℝ}
    (h1 : Optimal β κ σ ϑ rn x1 π1) (h2 : Optimal β κ σ ϑ rn x2 π2) : x1 = x2 ∧ π1 = π2 := by
  obtain ⟨hF1, hs1, ho1⟩ := h1
  obtain ⟨hF2, hs2, ho2⟩ := h2
  set xm : ℕ → ℝ := fun t => (x1 t + x2 t) / 2 with hxm
  set πm : ℕ → ℝ := fun t => (π1 t + π2 t) / 2 with hπm
  have hFm : Feasible β κ σ rn xm πm := by
    intro t
    obtain ⟨a1, b1⟩ := hF1 t
    obtain ⟨a2, b2⟩ := hF2 t
    unfold NKPC at a1 a2
    refine ⟨?_, ?_⟩
    · unfold NKPC; simp only [hxm, hπm]; linarith
    · have e : ups1 σ rn xm πm t = (ups1 σ rn x1 π1 t + ups1 σ rn x2 π2 t) / 2 := by
        simp only [ups1, hxm, hπm]; ring
      rw [e]; simp only [hxm]; linarith
  set D : ℕ → ℝ := fun t => β ^ t * ((π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hs1.add hs2).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2 ≤
        2 * ((π1 t ^ 2 + ϑ * x1 t ^ 2) + (π2 t ^ 2 + ϑ * x2 t ^ 2)) := by
      nlinarith [sq_nonneg (π1 t + π2 t), sq_nonneg (x1 t + x2 t)]
    nlinarith
  have hterm : ∀ t, lossTerm β ϑ xm πm t =
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 := by
    intro t; simp only [lossTerm, hDdef, hxm, hπm]; ring
  have hsm : Summable (lossTerm β ϑ xm πm) := by
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    exact ((hs1.add hs2).div_const 2).sub (hDs.div_const 4)
  have hlm : loss β ϑ xm πm = (loss β ϑ x1 π1 + loss β ϑ x2 π2) / 2 - (∑' t, D t) / 4 := by
    unfold loss
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    rw [((hs1.add hs2).div_const 2).tsum_sub (hDs.div_const 4), tsum_div_const,
      tsum_div_const, hs1.tsum_add hs2]
  have l12 := ho1 x2 π2 hF2 hs2
  have l21 := ho2 x1 π1 hF1 hs1
  have l1m := ho1 xm πm hFm hsm
  have hz := eq_zero_of_tsum_nonpos hD0 hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Galí (2015), pp. 146–147; Cochrane (2023), §20.2.4, p. 479: the discretionary path is
feasible for the commitment problem (`i ≥ 0`, with `ρ ≥ 0`) and has finite loss (it vanishes
after `t_Z`). -/
theorem disc_feasible_summable {β κ σ ϑ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (tZ : ℕ) :
    Feasible β κ σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) ∧
      Summable (lossTerm β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ)) := by
  have e1 : discX β κ σ η tZ = fun s => (delayPath β κ σ ρ η tZ (tZ + 1) s).1 :=
    funext fun s => by rw [delay_eq_disc]; rfl
  have e2 : discPi β κ σ η tZ = fun s => (delayPath β κ σ ρ η tZ (tZ + 1) s).2 :=
    funext fun s => by rw [delay_eq_disc]; rfl
  refine ⟨by rw [e1, e2]; exact delay_feasible hσ hρ le_rfl, ?_⟩
  refine summable_of_ne_finset_zero (s := Finset.range (tZ + 1)) fun t ht => ?_
  have h : tZ < t := by simp only [Finset.mem_range, not_lt] at ht; omega
  have hz := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ))) h
  simp only [lossTerm, discX, discPi, hz]
  ring

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2, p. 152: **discretion is strictly
worse than commitment**. If the commitment path of `comm_gt_disc` is the commitment optimum (as
`ZLBCommitment.algorithm_verification` proves when its sign conditions hold), the discretionary
path, feasible with finite loss, has strictly larger loss. -/
theorem comm_loss_lt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1))
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  obtain ⟨hdF, hdS⟩ := disc_feasible_summable (ϑ := ϑ) (η := η) hσ hρ.le tZ
  have hle := hopt.2.2 _ _ hdF hdS
  by_contra hnot
  push Not at hnot
  have hdopt : Optimal β κ σ ϑ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) :=
    ⟨hdF, hdS, fun y q hy hs => hnot.trans (hopt.2.2 y q hy hs)⟩
  have heq := optimal_unique hβ hϑ hopt hdopt
  have h0 := comm_gt_disc hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h36 h46 hξ2 hpost hsign hξ 0
  rw [heq.1] at h0
  exact lt_irrefl _ h0.1

/-! ## The discrete Werning family: forward guidance about `π_T` -/

/-- Cochrane (2023), eq. (5.6), p. 119 and §20.1, p. 467: the unstable root `λ₁` of the peg
(`ZLBPeg.lam1`) for Galí's model, whose IS slope `σ⁻¹` is Cochrane's `σ`. -/
noncomputable def l1 (β σ κ : ℝ) : ℝ := ZLBPeg.lam1 β σ⁻¹ κ

/-- Cochrane (2023), eq. (5.6), p. 119: the stable root `λ₂` (`ZLBPeg.lam2`) for Galí's model. -/
noncomputable def l2 (β σ κ : ℝ) : ℝ := ZLBPeg.lam2 β σ⁻¹ κ

/-- Cochrane (2023), §20.1, p. 467 (`ZLBPeg.peg_slaving`): the output gap per unit of inflation
on a bounded peg path, `x = (1 − λ₂)π/κ`. -/
noncomputable def vx (β σ κ : ℝ) : ℝ := (1 - l2 β σ κ) / κ

/-- Cochrane (2023), eq. (5.6), p. 119: `1 < λ₁` for Galí's model. -/
theorem one_lt_l1 {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) : 1 < l1 β σ κ :=
  ZLBPeg.one_lt_lam1 hβ (by positivity)

/-- Cochrane (2023), eq. (5.6), p. 119 and p. 475 (the bounded peg path is an eigenvector of the
backward map): `λ₁ v_x = v_x + σ⁻¹`. -/
theorem l1_vx {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l1 β σ κ * vx β σ κ = vx β σ κ + σ⁻¹ := by
  have ha := ZLBPeg.lam_add β σ⁻¹ κ
  have hm := ZLBPeg.lam_mul hβ (show 0 < σ⁻¹ * κ by positivity)
  have key : (l1 β σ κ - 1) * (1 - l2 β σ κ) = σ⁻¹ * κ := by
    unfold l1 l2
    linear_combination ha - hm
  have e : l1 β σ κ * vx β σ κ - vx β σ κ = (l1 β σ κ - 1) * (1 - l2 β σ κ) / κ := by
    unfold vx; ring
  rw [key, mul_div_assoc, div_self hκ.ne', mul_one] at e
  linarith

/-- Cochrane (2023), eq. (5.6), p. 119: `κ v_x + β + κ/σ = λ₁`. -/
theorem kappa_vx {β σ κ : ℝ} (hκ : 0 < κ) : κ * vx β σ κ + (β + κ / σ) = l1 β σ κ := by
  have ha : l1 β σ κ + l2 β σ κ = 1 + β + σ⁻¹ * κ := ZLBPeg.lam_add β σ⁻¹ κ
  have hv : κ * vx β σ κ = 1 - l2 β σ κ := by
    unfold vx; field_simp
  rw [hv, div_eq_mul_inv]
  linarith

/-- Cochrane (2023), §20.1, p. 467 and §20.2.2, p. 475: at a rate equal to the natural rate
(`e = 0`) the backward map multiplies the peg direction `(v_x, 1)` by `λ₁`. -/
theorem backStep_eigen {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (a : ℝ) :
    backStep β κ σ 0 (a * vx β σ κ, a) = (l1 β σ κ * (a * vx β σ κ), l1 β σ κ * a) := by
  have h1 := l1_vx hβ hσ hκ
  have h2 := kappa_vx (β := β) (σ := σ) hκ
  simp only [backStep]
  ext
  · simp only
    linear_combination (-a) * h1
  · simp only
    linear_combination a * h2

/-- Cochrane (2023), §20.2.2, p. 475 (the Werning family), in Galí's discrete model: rate `0`
during the trap `[0, t_Z]`, rate equal to the natural rate afterwards, and the bounded peg
continuation `π_{t_Z+1+k} = λ₁⁻ᵏ c`, `x = v_x π` after the trap; `c = π_{t_Z+1}` plays the role
of Werning's `π_T`. -/
noncomputable def wState (β κ σ η : ℝ) (tZ : ℕ) (c : ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η (c * vx β σ κ, c) (tZ + 1 - t)
  else ((l1 β σ κ)⁻¹ ^ (t - (tZ + 1)) * (c * vx β σ κ), (l1 β σ κ)⁻¹ ^ (t - (tZ + 1)) * c)

/-- Cochrane (2023), p. 475: after the trap the family member is on the peg path. -/
theorem w_post {β κ σ η : ℝ} {tZ : ℕ} (c : ℝ) (k : ℕ) :
    wState β κ σ η tZ c (tZ + 1 + k) =
      ((l1 β σ κ)⁻¹ ^ k * (c * vx β σ κ), (l1 β σ κ)⁻¹ ^ k * c) := by
  simp only [wState, show ¬ tZ + 1 + k ≤ tZ by omega, ↓reduceIte,
    show tZ + 1 + k - (tZ + 1) = k by omega]

/-- Cochrane (2023), p. 475: at the end of the trap the member is at `(c v_x, c)`. -/
theorem w_end {β κ σ η : ℝ} {tZ : ℕ} (c : ℝ) :
    wState β κ σ η tZ c (tZ + 1) = (c * vx β σ κ, c) := by
  have := w_post (β := β) (κ := κ) (σ := σ) (η := η) (tZ := tZ) c 0
  simpa using this

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: during the trap the member obeys the
binding-bound recursion (34). -/
theorem w_trap {β κ σ η : ℝ} {tZ t : ℕ} (c : ℝ) (ht : t ≤ tZ) :
    wState β κ σ η tZ c t = backStep β κ σ η (wState β κ σ η tZ c (t + 1)) := by
  by_cases h : t + 1 ≤ tZ
  · simp only [wState, ht, h, ↓reduceIte, show tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 by omega,
      backState]
  · have htz : tZ = t := by omega
    subst htz
    rw [w_end]
    simp only [wState, le_rfl, ↓reduceIte, show tZ + 1 - tZ = 0 + 1 by omega, backState]

/-- Cochrane (2023), §20.1, p. 467: after the trap the member obeys the peg recursion
`(x_t, π_t) = A(x_{t+1}, π_{t+1})` (rate equal to the natural rate). -/
theorem w_after {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ t : ℕ} (c : ℝ)
    (ht : tZ < t) :
    wState β κ σ η tZ c t = backStep β κ σ 0 (wState β κ σ η tZ c (t + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
  rw [show tZ + 1 + k + 1 = tZ + 1 + (k + 1) by omega, w_post, w_post,
    show (l1 β σ κ)⁻¹ ^ (k + 1) * (c * vx β σ κ) = ((l1 β σ κ)⁻¹ ^ (k + 1) * c) * vx β σ κ by
      ring, backStep_eigen hβ hσ hκ]
  have hl : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ * ((l1 β σ κ)⁻¹ ^ (k + 1) * c) = (l1 β σ κ)⁻¹ ^ k * c := by
    rw [pow_succ]; field_simp
  have e2 : l1 β σ κ * ((l1 β σ κ)⁻¹ ^ (k + 1) * c * vx β σ κ) =
      (l1 β σ κ)⁻¹ ^ k * c * vx β σ κ := by rw [← mul_assoc, e]
  rw [e, e2]
  ext
  · simp only; ring
  · simp only

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPath_isPath`, discrete): every member
satisfies the Phillips curve at every date, has `i = 0` during the trap and `i = rⁿ` after. -/
theorem w_isPath {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ} (c : ℝ) :
    (∀ t, NKPC β κ (fun s => (wState β κ σ η tZ c s).1) (fun s => (wState β κ σ η tZ c s).2) t) ∧
      (∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = 0) ∧
      (∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = natRate ρ η tZ t) := by
  have hA : ∀ t, t ≤ tZ → NKPC β κ (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = 0 := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (wState β κ σ η tZ c s).1)
      (π := fun s => (wState β κ σ η tZ c s).2) (t := t) hσ.ne' (w_trap c ht)
    exact ⟨h.1, by rw [h.2, natRate_of_le ht]; ring⟩
  have hB : ∀ t, tZ < t → NKPC β κ (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = natRate ρ η tZ t := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (wState β κ σ η tZ c s).1)
      (π := fun s => (wState β κ σ η tZ c s).2) (t := t) hσ.ne' (w_after hβ hσ hκ c ht)
    exact ⟨h.1, by rw [h.2, add_zero]⟩
  refine ⟨fun t => ?_, fun t ht => (hA t ht).2, fun t ht => (hB t ht).2⟩
  rcases le_or_gt t tZ with h | h
  · exact (hA t h).1
  · exact (hB t h).1

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPath_bdd`, discrete): every member is
bounded. -/
theorem w_bdd {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (tZ : ℕ) (c : ℝ) :
    ∃ M, ∀ t, |(wState β κ σ η tZ c t).1| ≤ M ∧ |(wState β κ σ η tZ c t).2| ≤ M := by
  set S := ∑ s ∈ Finset.range (tZ + 1),
    (|(wState β κ σ η tZ c s).1| + |(wState β κ σ η tZ c s).2|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hl := one_lt_l1 hβ hσ hκ
  have hi0 : 0 ≤ (l1 β σ κ)⁻¹ := inv_nonneg.2 (by linarith)
  have hi1 : (l1 β σ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl.le
  refine ⟨S + |c * vx β σ κ| + |c|, fun t => ?_⟩
  have a1 := abs_nonneg (c * vx β σ κ)
  have a2 := abs_nonneg c
  rcases le_or_gt t tZ with h | h
  · have hle := Finset.single_le_sum
      (f := fun s => |(wState β κ σ η tZ c s).1| + |(wState β κ σ η tZ c s).2|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    have b1 := abs_nonneg (wState β κ σ η tZ c t).1
    have b2 := abs_nonneg (wState β κ σ η tZ c t).2
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
    rw [w_post]
    have hp0 : 0 ≤ (l1 β σ κ)⁻¹ ^ k := pow_nonneg hi0 k
    have hp1 : (l1 β σ κ)⁻¹ ^ k ≤ 1 := pow_le_one₀ hi0 hi1
    simp only [abs_mul, abs_of_nonneg hp0]
    have e1 : (l1 β σ κ)⁻¹ ^ k * (|c| * |vx β σ κ|) ≤ |c| * |vx β σ κ| :=
      mul_le_of_le_one_left (by positivity) hp1
    have e2 : (l1 β σ κ)⁻¹ ^ k * |c| ≤ |c| := mul_le_of_le_one_left a2 hp1
    rw [abs_mul] at a1
    constructor <;> nlinarith

/-- Cochrane (2023), §20.2.2, p. 475 (the new-Keynesian selection `π_T = 0`) and Galí (2015),
p. 147: the member with `c = 0` is Galí's discretionary path. -/
theorem w_zero (β κ σ η : ℝ) (tZ t : ℕ) :
    wState β κ σ η tZ 0 t = zlbPath β κ σ η tZ (0, 0) t := by
  by_cases h : t ≤ tZ
  · simp only [wState, zlbPath, h, ↓reduceIte, zero_mul]
  · simp only [wState, zlbPath, h, ↓reduceIte, zero_mul, mul_zero]

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.dpi_dpiT`, discrete): across the family,
`π_t(c) − π_t(c') = λ₁^{t_Z+1−t}(c − c')` and `x_t(c) − x_t(c') = λ₁^{t_Z+1−t}(c − c')v_x` at
every date of the trap and at its end. -/
theorem w_sub {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ t : ℕ} (c c' : ℝ)
    (ht : t ≤ tZ + 1) :
    (wState β κ σ η tZ c t).1 - (wState β κ σ η tZ c' t).1 =
        l1 β σ κ ^ (tZ + 1 - t) * ((c - c') * vx β σ κ) ∧
      (wState β κ σ η tZ c t).2 - (wState β κ σ η tZ c' t).2 =
        l1 β σ κ ^ (tZ + 1 - t) * (c - c') := by
  have h1 := l1_vx hβ hσ hκ
  have h2 := kappa_vx (β := β) (σ := σ) hκ
  refine down_ind (N := tZ + 1) (P := fun t => (wState β κ σ η tZ c t).1 -
      (wState β κ σ η tZ c' t).1 = l1 β σ κ ^ (tZ + 1 - t) * ((c - c') * vx β σ κ) ∧
      (wState β κ σ η tZ c t).2 - (wState β κ σ η tZ c' t).2 =
        l1 β σ κ ^ (tZ + 1 - t) * (c - c')) ?_ (fun s hs ih => ?_) t ht
  · rw [w_end, w_end]
    exact ⟨by simp only [Nat.sub_self, pow_zero, one_mul]; ring,
      by simp only [Nat.sub_self, pow_zero, one_mul]⟩
  · have e := backStep_sub_fst β κ σ η (wState β κ σ η tZ c (s + 1))
      (wState β κ σ η tZ c' (s + 1))
    have f := backStep_sub_snd β κ σ η (wState β κ σ η tZ c (s + 1))
      (wState β κ σ η tZ c' (s + 1))
    rw [← w_trap c (by omega), ← w_trap c' (by omega), ih.1, ih.2] at e f
    rw [e, f, show tZ + 1 - s = (tZ + 1 - (s + 1)) + 1 by omega, pow_succ]
    constructor
    · linear_combination (-(l1 β σ κ ^ (tZ + 1 - (s + 1)) * (c - c'))) * h1
    · linear_combination l1 β σ κ ^ (tZ + 1 - (s + 1)) * (c - c') * h2

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.dpi0_dpiT`, discrete): **date-0
inflation moves one-for-`λ₁^{t_Z+1}` with the promise `c`**: `π₀(c) − π₀(c') =
λ₁^{t_Z+1}(c − c')`, and `π₀(c) = π₀^{disc} + λ₁^{t_Z+1} c`. -/
theorem w_pi0_sub {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (tZ : ℕ) (c c' : ℝ) :
    (wState β κ σ η tZ c 0).2 - (wState β κ σ η tZ c' 0).2 = l1 β σ κ ^ (tZ + 1) * (c - c') ∧
      (wState β κ σ η tZ c 0).2 = discPi β κ σ η tZ 0 + l1 β σ κ ^ (tZ + 1) * c := by
  have h := (w_sub (η := η) hβ hσ hκ (tZ := tZ) (t := 0) c c' (by omega)).2
  have h0 := (w_sub (η := η) hβ hσ hκ (tZ := tZ) (t := 0) c 0 (by omega)).2
  rw [Nat.sub_zero] at h h0
  refine ⟨h, ?_⟩
  rw [w_zero] at h0
  unfold discPi
  linarith

/-- Cochrane (2023), §20.2.4, p. 479 ("promises about actions further in the future have greater
effects today", `ForwardGuidance.sensitivity_strictMono_T`, discrete): the sensitivity `λ₁ⁿ` is
strictly increasing in the length `n` of the trap. -/
theorem w_sensitivity_strictMono {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono fun n : ℕ => l1 β σ κ ^ n :=
  pow_right_strictMono₀ (one_lt_l1 hβ hσ hκ)

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.sensitivity_tendsto_T`, discrete): the
sensitivity is unbounded in the length of the trap. -/
theorem w_sensitivity_tendsto {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => l1 β σ κ ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (one_lt_l1 hβ hσ hκ)

/-- Cochrane (2023), §5.7.1, p. 165 and §20.2.4, p. 479 (**the discrete sensitivity converges to
Werning's `e^{λ^b T}`**, `ForwardGuidance.dpi0_dpiT`): with period length `t/n` (`β = 1 − ρt/n`,
Galí's IS slope `σ⁻¹ = σt/n`, `κt/n`), the sensitivity `λ₁ⁿ` of `π₀` to the promise after `n`
periods tends to `e^{λ^b t}` (via `Links.tendsto_peg_decay`). -/
theorem sensitivity_tendsto_exp {ρ σ κ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => l1 (1 - ρ * (t / n)) (σ * (t / n))⁻¹ (κ * (t / n)) ^ n) atTop
      (𝓝 (Real.exp (ContinuousTimeNK.lamb ρ κ σ * t))) := by
  have h := (Links.tendsto_peg_decay (ρ := ρ) (mul_pos hσ hκ) ht).inv₀ (Real.exp_pos _).ne'
  rw [Real.exp_neg, inv_inv] at h
  refine h.congr fun n => ?_
  simp only [l1, inv_inv, inv_pow]

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.bdd_path_iff`, discrete): **every** bounded
path with the Phillips curve, `i = 0` during the trap and `i = rⁿ` after it is the member
`c = π_{t_Z+1}` of the family (the post-trap peg pins `x = v_x π` and `π_{t+1} = λ₁⁻¹π_t` by
`ZLBPeg.peg_slaving` and `Links.peg_pf_path`; the trap is pinned backward). -/
theorem w_unique {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ}
    {x π : ℕ → ℝ} (hb : ∃ M, ∀ t, |x t| ≤ M ∧ |π t| ≤ M) (hN : ∀ t, NKPC β κ x π t)
    (h0 : ∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) x π t = 0)
    (h1 : ∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) x π t = natRate ρ η tZ t) (t : ℕ) :
    (x t, π t) = wState β κ σ η tZ (π (tZ + 1)) t := by
  obtain ⟨M, hM⟩ := hb
  have hσκ : 0 < σ⁻¹ * κ := by positivity
  set X : ℕ → Unit → ℝ := fun k _ => x (tZ + 1 + k) with hX
  set P : ℕ → Unit → ℝ := fun k _ => π (tZ + 1 + k) with hP
  have hbX : BoundedProc X := ⟨M, fun k _ => (hM _).1⟩
  have hbP : BoundedProc P := ⟨M, fun k _ => (hM _).2⟩
  have hpeg : ZLBPeg.PegEq perfectForesight β σ⁻¹ κ 0 X P := by
    intro k ω
    have hr := h1 (tZ + 1 + k) (by omega)
    unfold impliedRate at hr
    rw [natRate_of_lt (by omega)] at hr
    have hn := hN (tZ + 1 + k)
    unfold NKPC at hn
    have e : tZ + 1 + (k + 1) = tZ + 1 + k + 1 := by omega
    constructor
    · change x (tZ + 1 + k) = x (tZ + 1 + (k + 1)) - σ⁻¹ * (0 - π (tZ + 1 + (k + 1)))
      rw [e]
      have h3 : σ * (x (tZ + 1 + k + 1) - x (tZ + 1 + k)) = -π (tZ + 1 + k + 1) := by linarith
      have h4 : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
      linear_combination (-σ⁻¹) * h3 + (x (tZ + 1 + k + 1) - x (tZ + 1 + k)) * h4
    · change π (tZ + 1 + k) = β * π (tZ + 1 + (k + 1)) + κ * x (tZ + 1 + k)
      rw [e]; exact hn
  have hpost : ∀ k, (x (tZ + 1 + k), π (tZ + 1 + k)) =
      wState β κ σ η tZ (π (tZ + 1)) (tZ + 1 + k) := by
    intro k
    have hs := ZLBPeg.peg_slaving perfectForesight hβ hσκ hbX hbP hpeg k ()
    have hp := Links.peg_pf_path hβ hσκ hbX hbP hpeg k
    simp only [hX, hP, add_zero, sub_zero, mul_zero] at hs hp
    rw [w_post]
    have hπk : π (tZ + 1 + k) = (l1 β σ κ)⁻¹ ^ k * π (tZ + 1) := hp
    have hs' : κ * x (tZ + 1 + k) + (l2 β σ κ - 1) * π (tZ + 1 + k) = 0 := hs
    have hv : κ * vx β σ κ = 1 - l2 β σ κ := by unfold vx; field_simp
    have hxk : x (tZ + 1 + k) = π (tZ + 1 + k) * vx β σ κ := by
      apply mul_left_cancel₀ hκ.ne'
      linear_combination hs' - π (tZ + 1 + k) * hv
    rw [hxk, hπk]
    ext
    · simp only; ring
    · simp only
  rcases Nat.lt_or_ge tZ t with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
    exact hpost k
  · refine zr_eq (e := fun _ => η) (N := tZ + 1) (p := fun t => (x t, π t))
      (fun s hs => backStep_of_rate (rn := natRate ρ η tZ) hσ.ne' (hN s) ?_)
      (fun s hs => w_trap (tZ := tZ) (t := s) _ (by omega)) ?_ t (by omega)
    · rw [h0 s (by omega), natRate_of_le (by omega)]; ring
    · simpa using hpost 0

/-- Cochrane (2023), §20.2.2, p. 475: the discrete Werning family is exactly the set of bounded
paths with the Phillips curve, `i = 0` in the trap and `i = rⁿ` after it, and the index is
`c = π_{t_Z+1}` (existence, uniqueness and characterisation). -/
theorem w_family_iff {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ}
    {x π : ℕ → ℝ} :
    ((∃ M, ∀ t, |x t| ≤ M ∧ |π t| ≤ M) ∧ (∀ t, NKPC β κ x π t) ∧
      (∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) x π t = natRate ρ η tZ t)) ↔
      ∃ c, ∀ t, (x t, π t) = wState β κ σ η tZ c t := by
  constructor
  · rintro ⟨hb, hN, h0, h1⟩
    exact ⟨π (tZ + 1), w_unique hβ hσ hκ hb hN h0 h1⟩
  · rintro ⟨c, hc⟩
    have hx : x = fun s => (wState β κ σ η tZ c s).1 := funext fun s => by rw [← hc s]
    have hπ : π = fun s => (wState β κ σ η tZ c s).2 := funext fun s => by rw [← hc s]
    obtain ⟨M, hM⟩ := w_bdd (η := η) hβ hσ hκ tZ c
    obtain ⟨a, b, d⟩ := w_isPath (ρ := ρ) (η := η) hβ hσ hκ (tZ := tZ) c
    rw [hx, hπ]
    exact ⟨⟨M, hM⟩, a, b, d⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2: **the commitment path is
equivalent, for date-0 inflation, to exactly one forward-guidance promise about `π_T`, and that
promise is strictly positive** (a glide path `c > 0`, `ForwardGuidance.glide_path`). -/
theorem comm_promise {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    (∃! c, (wState β κ σ η tZ c 0).2 = π 0) ∧
      ∀ c, (wState β κ σ η tZ c 0).2 = π 0 → 0 < c := by
  have hl := one_lt_l1 hβ hσ hκ
  have hp : 0 < l1 β σ κ ^ (tZ + 1) := pow_pos (by linarith) _
  have hg := (comm_gt_disc hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h36 h46 hξ2 hpost hsign hξ 0).2
  have hw : ∀ c, (wState β κ σ η tZ c 0).2 = discPi β κ σ η tZ 0 + l1 β σ κ ^ (tZ + 1) * c :=
    fun c => (w_pi0_sub (η := η) hβ hσ hκ tZ c 0).2
  refine ⟨⟨(π 0 - discPi β κ σ η tZ 0) / l1 β σ κ ^ (tZ + 1), ?_, fun c hc => ?_⟩,
    fun c hc => ?_⟩
  · beta_reduce
    rw [hw]; field_simp; ring
  · beta_reduce at hc
    rw [hw] at hc
    field_simp
    linarith
  · rw [hw] at hc
    have : 0 < l1 β σ κ ^ (tZ + 1) * c := by linarith
    exact (mul_pos_iff_of_pos_left hp).mp this

/-- Cochrane (2023), §20.2.4, p. 479: when Galí's commitment keeps the rate at zero after the
shock ends (`t_C > t_Z`) its path is **not** a member of the Werning family (whose rate
returns to the natural rate at `t_Z + 1`): commitment is delayed lift-off, not only a promise
about `π_T`. -/
theorem comm_not_member {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ < tC) {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (c : ℝ) : ¬ ∀ t, (x t, π t) = wState β κ σ η tZ c t := by
  intro h
  have hx : x = fun s => (wState β κ σ η tZ c s).1 := funext fun s => by rw [← h s]
  have hπ : π = fun s => (wState β κ σ η tZ c s).2 := funext fun s => by rw [← h s]
  have a := (comm_rates (β := β) (κ := κ) hσ hρ h48 h49).1 (tZ + 1) (by omega)
  have b := (w_isPath (ρ := ρ) (η := η) hβ hσ hκ (tZ := tZ) c).2.2 (tZ + 1) (by omega)
  rw [← hx, ← hπ, natRate_of_lt (by omega)] at b
  linarith

/-! ## Woodford's moment constraint versus Cochrane's pathwise bound -/

namespace Moments

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (4.18)–(4.20), p. 428, restated from the Woodford Chapter 6 project
(`ZLB.dAvg`); Cochrane (2023), §20.1, p. 465: the discounted average
`Ê[f] = (1 − β) ∑ βᵗ E₀ f_t`, evaluated in the date-0 state `ω₀`. -/
noncomputable def dAvg (β : ℝ) (f : ℕ → Ω → ℝ) (ω0 : Ω) : ℝ :=
  (1 - β) * ∑' t, β ^ t * 𝔼.E 0 (f t) ω0

/-- Woodford (2003), (2.21), p. 400 (restated from the Woodford Chapter 6 project's
`Sequences.hasSum_dsum`); Cochrane (2023), p. 465: the discounted expected sum of a bounded
process converges. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (ω0 : Ω) : Summable fun t => β ^ t * 𝔼.E 0 (f t) ω0 := by
  obtain ⟨M, hM⟩ := hf
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  have h := 𝔼.abs_E_le (fun ω => hM t ω) 0 ω0
  have := pow_nonneg hβ0 t
  nlinarith

/-- Woodford (2003), (4.18)–(4.20) (restated from the Woodford Chapter 6 project's
`ZLB.dAvg_lincomb`); Cochrane (2023), p. 465: `Ê[a f + b g + c] = a Ê[f] + b Ê[g] + c`. -/
theorem dAvg_lincomb {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (a b c : ℝ) (ω0 : Ω) :
    dAvg 𝔼 β (fun t ω => a * f t ω + b * g t ω + c) ω0 =
      a * dAvg 𝔼 β f ω0 + b * dAvg 𝔼 β g ω0 + c := by
  have hE : ∀ t, 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0 =
      a * 𝔼.E 0 (f t) ω0 + b * 𝔼.E 0 (g t) ω0 + c := by
    intro t
    have : (fun ω => a * f t ω + b * g t ω + c) = a • f t + b • g t + (fun _ => c) := by
      funext ω; simp [smul_eq_mul]
    rw [this, map_add, map_add, map_smul, map_smul, 𝔼.const]
    rfl
  have hsf := summable_disc 𝔼 hβ0 hβ1 hf ω0
  have hsg := summable_disc 𝔼 hβ0 hβ1 hg ω0
  have hgeo : HasSum (fun t => β ^ t * c) (c / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right c
    rwa [div_eq_inv_mul]
  have htot := ((hsf.hasSum.mul_left a).add (hsg.hasSum.mul_left b)).add hgeo
  unfold dAvg
  rw [show (fun t => β ^ t * 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0) =
      fun t => a * (β ^ t * 𝔼.E 0 (f t) ω0) + b * (β ^ t * 𝔼.E 0 (g t) ω0) + β ^ t * c from
      funext fun t => by rw [hE t]; ring, htot.tsum_eq]
  have h1 : 1 - β ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), (4.18) (restated from the Woodford Chapter 6 project); Cochrane (2023),
p. 465: `Ê[c] = c`. -/
theorem dAvg_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) (ω0 : Ω) :
    dAvg 𝔼 β (fun _ _ => c) ω0 = c := by
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have := dAvg_lincomb 𝔼 hβ0 hβ1 h0 h0 0 0 c ω0
  simpa using this

/-- Woodford (2003), p. 428 (restated from the Woodford Chapter 6 project's `ZLB.dAvg_mono`);
Cochrane (2023), p. 465: `Ê` is monotone on bounded processes. -/
theorem dAvg_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (hfg : ∀ t ω, f t ω ≤ g t ω) (ω0 : Ω) :
    dAvg 𝔼 β f ω0 ≤ dAvg 𝔼 β g ω0 := by
  unfold dAvg
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_disc 𝔼 hβ0 hβ1 hf ω0)
    (summable_disc 𝔼 hβ0 hβ1 hg ω0)
  exact mul_le_mul_of_nonneg_left (𝔼.mono 0 (fun ω => hfg t ω) ω0) (pow_nonneg hβ0 t)

/-- Woodford (2003), p. 428, restated from the Woodford Chapter 6 project (`ZLB.bigK`);
Cochrane (2023), §20.1, p. 465: `K = 1 + k⁻²` (the mean at least `k` standard deviations
above zero). -/
noncomputable def bigK (k : ℝ) : ℝ := 1 + k⁻¹ ^ 2

/-- Woodford (2003), (4.18)–(4.19), p. 428, restated from the Woodford Chapter 6 project
(`ZLB.Feasible`); Cochrane (2023), §20.1, p. 465: Woodford's moment form of the bound,
`Ê[i] ≥ 0` and `Ê[i²] ≤ K (Ê[i])²`. -/
def MomentFeasible (β K : ℝ) (i : ℕ → Ω → ℝ) (ω0 : Ω) : Prop :=
  0 ≤ dAvg 𝔼 β i ω0 ∧ dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0 ≤ K * dAvg 𝔼 β i ω0 ^ 2

/-- Cochrane (2023), §20.1, p. 465 ("interest rates cannot go below zero"): the pathwise
bound `i_t ≥ 0` at every date and in every state. -/
def PathwiseZLB (i : ℕ → Ω → ℝ) : Prop := ∀ t ω, 0 ≤ i t ω

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), (4.18), p. 428: the pathwise bound
implies the first of Woodford's two moment conditions, `Ê[i] ≥ 0`. -/
theorem pathwise_mean_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {i : ℕ → Ω → ℝ}
    (hb : BoundedProc i) (h : PathwiseZLB i) (ω0 : Ω) : 0 ≤ dAvg 𝔼 β i ω0 := by
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have := dAvg_mono 𝔼 hβ0 hβ1 h0 hb h ω0
  rwa [dAvg_const 𝔼 hβ0 hβ1] at this

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), (4.18)–(4.19), p. 428: a **pathwise
band** `a ≤ i_t ≤ b` with `0 ≤ a` and `(b − a)² ≤ 4(K − 1)a²` (`K ≥ 1`) satisfies Woodford's
moment constraint (by `Ê[(i − a)(b − i)] ≥ 0`, the Bhatia–Davis bound). -/
theorem band_moment_feasible {β K a b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hK : 1 ≤ K)
    (ha : 0 ≤ a) (hab : (b - a) ^ 2 ≤ 4 * (K - 1) * a ^ 2) {i : ℕ → Ω → ℝ}
    (hlo : ∀ t ω, a ≤ i t ω) (hhi : ∀ t ω, i t ω ≤ b) (ω0 : Ω) :
    MomentFeasible 𝔼 β K i ω0 := by
  have hb : BoundedProc i := ⟨|a| + |b|, fun t ω => by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, le_abs_self b, abs_nonneg b, hlo t ω]
    · linarith [le_abs_self b, abs_nonneg a, hhi t ω]⟩
  have hsq : BoundedProc (fun t ω => i t ω ^ 2) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M ^ 2, fun t ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM t ω) 2⟩
  have hc : ∀ c : ℝ, BoundedProc (fun _ _ => c : ℕ → Ω → ℝ) := fun c => ⟨|c|, fun _ _ => le_rfl⟩
  set m := dAvg 𝔼 β i ω0
  set m2 := dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0
  have h1 : a ≤ m := by
    have := dAvg_mono 𝔼 hβ0 hβ1 (hc a) hb hlo ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1] at this
  have h2 : m ≤ b := by
    have := dAvg_mono 𝔼 hβ0 hβ1 hb (hc b) hhi ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1] at this
  have h3 : 0 ≤ -1 * m2 + (a + b) * m + -(a * b) := by
    have hq : BoundedProc (fun t ω => -1 * i t ω ^ 2 + (a + b) * i t ω + -(a * b)) := by
      obtain ⟨M1, hM1⟩ := hsq
      obtain ⟨M2, hM2⟩ := hb
      refine ⟨M1 + |a + b| * M2 + |a * b|, fun t ω => ?_⟩
      have e1 := hM1 t ω
      have e2 := hM2 t ω
      simp only at e1
      calc |-1 * i t ω ^ 2 + (a + b) * i t ω + -(a * b)|
          ≤ |-1 * i t ω ^ 2| + |(a + b) * i t ω| + |-(a * b)| := abs_add_three _ _ _
        _ = |i t ω ^ 2| + |a + b| * |i t ω| + |a * b| := by
          rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_one, one_mul]
        _ ≤ M1 + |a + b| * M2 + |a * b| := by gcongr
    have := dAvg_mono 𝔼 hβ0 hβ1 (hc 0) hq (fun t ω => by
      nlinarith [hlo t ω, hhi t ω]) ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1, dAvg_lincomb 𝔼 hβ0 hβ1 hsq hb] at this
  refine ⟨ha.trans h1, ?_⟩
  nlinarith [sq_nonneg (2 * m - a - b), mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h1 2)
    (by linarith : (0 : ℝ) ≤ K - 1)]

/-- Woodford (2003), p. 428 (the motivation: "the mean is at least `k` standard deviations above
zero" keeps violations rare), made precise as a Cantelli bound; Cochrane (2023), §20.1, p. 465.
If Woodford's constraint holds with `Ê[i] > 0` and `K ≥ 1`, the **discounted frequency of
violating the bound**, `Ê[1{i < 0}]`, is at most `(K − 1)/K` (`= 1/(1 + k²)` for `K = 1 + k⁻²`). -/
theorem violation_freq_le {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hK : 1 ≤ K)
    {i : ℕ → Ω → ℝ} (hb : BoundedProc i) {ω0 : Ω} (hF : MomentFeasible 𝔼 β K i ω0)
    (hm : 0 < dAvg 𝔼 β i ω0) :
    dAvg 𝔼 β (fun t ω => if i t ω < 0 then 1 else 0) ω0 ≤ (K - 1) / K := by
  have hsq : BoundedProc (fun t ω => i t ω ^ 2) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M ^ 2, fun t ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM t ω) 2⟩
  set m := dAvg 𝔼 β i ω0
  set m2 := dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0
  have hK0 : 0 < K := by linarith
  set s := K * m with hs
  have hs0 : 0 < s := mul_pos hK0 hm
  have hind : BoundedProc (fun t ω => if i t ω < 0 then (1 : ℝ) else 0) :=
    ⟨1, fun t ω => by
      change |(if i t ω < 0 then (1 : ℝ) else 0)| ≤ 1
      split_ifs <;> norm_num⟩
  have hR : BoundedProc (fun t ω => 1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1) := by
    obtain ⟨M1, hM1⟩ := hsq
    obtain ⟨M2, hM2⟩ := hb
    refine ⟨|1 / s ^ 2| * M1 + |-2 / s| * M2 + 1, fun t ω => ?_⟩
    have e1 := hM1 t ω
    have e2 := hM2 t ω
    simp only at e1
    calc |1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1|
        ≤ |1 / s ^ 2 * i t ω ^ 2| + |-2 / s * i t ω| + |(1 : ℝ)| := abs_add_three _ _ _
      _ = |1 / s ^ 2| * |i t ω ^ 2| + |-2 / s| * |i t ω| + 1 := by
        rw [abs_mul, abs_mul, abs_one]
      _ ≤ |1 / s ^ 2| * M1 + |-2 / s| * M2 + 1 := by gcongr
  have hpt : ∀ t ω, (if i t ω < 0 then (1 : ℝ) else 0) ≤
      1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1 := by
    intro t ω
    have e : 1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1 = (s - i t ω) ^ 2 / s ^ 2 := by
      field_simp; ring
    rw [e]
    split_ifs with h
    · rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith
    · positivity
  have hle := dAvg_mono 𝔼 hβ0 hβ1 hind hR hpt ω0
  rw [dAvg_lincomb 𝔼 hβ0 hβ1 hsq hb] at hle
  have h1 : 1 / s ^ 2 * m2 ≤ 1 / s ^ 2 * (K * m ^ 2) :=
    mul_le_mul_of_nonneg_left hF.2 (by positivity)
  have h2 : 1 / s ^ 2 * (K * m ^ 2) = 1 / K := by
    rw [hs]; field_simp
  have h3 : -2 / s * m = -2 / K := by
    rw [hs]; field_simp
  have h4 : 1 / K + -2 / K + 1 = (K - 1) / K := by field_simp; ring
  linarith

/-- Cochrane (2023), §20.1, p. 465: under the pathwise bound the discounted frequency of
violations is `0` (the indicator vanishes identically). -/
theorem pathwise_violation_freq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {i : ℕ → Ω → ℝ}
    (h : PathwiseZLB i) (ω0 : Ω) :
    dAvg 𝔼 β (fun t ω => if i t ω < 0 then 1 else 0) ω0 = 0 := by
  have e : (fun t ω => if i t ω < 0 then (1 : ℝ) else 0) = fun _ _ => 0 := by
    funext t ω
    simp [not_lt.mpr (h t ω)]
  rw [e, dAvg_const 𝔼 hβ0 hβ1]

/-- Cochrane (2023), §20.1, p. 465 (perfect foresight): `Ê` under perfect foresight is the plain
discounted average. -/
theorem dAvg_pf (β : ℝ) (f : ℕ → Unit → ℝ) :
    dAvg perfectForesight β f () = (1 - β) * ∑' t, β ^ t * f t () := rfl

/-- Cochrane (2023), §20.1, p. 465: a one-period spike `i_0 = 1`, `i_t = 0` after. -/
noncomputable def spike (t : ℕ) (_ : Unit) : ℝ := if t = 0 then 1 else 0

/-- Cochrane (2023), §20.1, p. 465: a one-period violation, `i_0 = −1`, `i_t = 9` after. -/
noncomputable def dip (t : ℕ) (_ : Unit) : ℝ := if t = 0 then -1 else 9

/-- Cochrane (2023), §20.1, p. 465: with `β = 9/10`, `Ê[spike] = Ê[spike²] = 1/10`. -/
theorem spike_moments :
    dAvg perfectForesight (9 / 10) spike () = 1 / 10 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => spike t ω ^ 2) () = 1 / 10 := by
  have e1 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * spike t ()) = fun t => if t = 0 then 1 else 0 := by
    funext t; unfold spike; split_ifs with h <;> simp [h]
  have e2 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * spike t () ^ 2) =
      fun t => if t = 0 then 1 else 0 := by
    funext t; unfold spike; split_ifs with h <;> simp [h]
  rw [dAvg_pf, dAvg_pf, e1, e2, tsum_ite_eq]
  norm_num

/-- Cochrane (2023), §20.1, p. 465: with `β = 9/10`, `Ê[dip] = 8`, `Ê[dip²] = 73`, and the
discounted frequency of `dip < 0` is `1/10`. -/
theorem dip_moments :
    dAvg perfectForesight (9 / 10) dip () = 8 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => dip t ω ^ 2) () = 73 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => if dip t ω < 0 then 1 else 0) () = 1 / 10 := by
  have hg : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t) (1 - 9 / 10)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t * dip t ()) (9 * (1 - 9 / 10)⁻¹ - 10) := by
    refine ((hg.mul_left 9).sub (hasSum_ite_eq 0 (10 : ℝ))).congr_fun fun t => ?_
    unfold dip; split_ifs with h <;> simp [h] <;> ring
  have h2 : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t * dip t () ^ 2) (81 * (1 - 9 / 10)⁻¹ - 80) := by
    refine ((hg.mul_left 81).sub (hasSum_ite_eq 0 (80 : ℝ))).congr_fun fun t => ?_
    unfold dip; split_ifs with h <;> simp [h] <;> ring
  have e3 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * (if dip t () < 0 then 1 else 0)) =
      fun t => if t = 0 then 1 else 0 := by
    funext t; unfold dip; by_cases h : t = 0 <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [dAvg_pf, h1.tsum_eq]; norm_num
  · rw [dAvg_pf, h2.tsum_eq]; norm_num
  · rw [dAvg_pf, e3, tsum_ite_eq]; norm_num

/-- Cochrane (2023), §20.1, p. 465, against Woodford (2003), p. 428: **the pathwise bound does
not imply Woodford's constraint** — the spike `i_0 = 1`, `i_t = 0` is pathwise feasible but
violates `Ê[i²] ≤ K (Ê[i])²` at Woodford's `K = 1 + 2.26⁻²` (`β = 9/10`). -/
theorem pathwise_not_moment :
    BoundedProc spike ∧ PathwiseZLB spike ∧
      ¬ MomentFeasible perfectForesight (9 / 10) (bigK 2.26) spike () := by
  obtain ⟨h1, h2⟩ := spike_moments
  refine ⟨⟨1, fun t _ => by unfold spike; split_ifs <;> norm_num⟩,
    fun t _ => by unfold spike; split_ifs <;> norm_num, fun h => ?_⟩
  have := h.2
  rw [h1, h2] at this
  unfold bigK at this
  norm_num at this

/-- Woodford (2003), p. 428, against Cochrane (2023), §20.1, p. 465: **Woodford's constraint
does not imply the pathwise bound** — `i_0 = −1`, `i_t = 9` satisfies `Ê[i] = 8 ≥ 0` and
`Ê[i²] = 73 ≤ K · 64` at `K = 1 + 2.26⁻²` (`β = 9/10`) but violates `i ≥ 0` at date 0, with
discounted violation frequency `1/10 > 0` (within the Cantelli bound `violation_freq_le`). -/
theorem moment_not_pathwise :
    BoundedProc dip ∧ MomentFeasible perfectForesight (9 / 10) (bigK 2.26) dip () ∧
      ¬ PathwiseZLB dip ∧
      dAvg perfectForesight (9 / 10) (fun t ω => if dip t ω < 0 then 1 else 0) () = 1 / 10 := by
  obtain ⟨h1, h2, h3⟩ := dip_moments
  refine ⟨⟨9, fun t _ => by unfold dip; split_ifs <;> norm_num⟩, ⟨?_, ?_⟩, fun h => ?_, h3⟩
  · rw [h1]; norm_num
  · rw [h1, h2]; unfold bigK; norm_num
  · have := h 0 ()
    unfold dip at this
    norm_num at this

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), Proposition 6.9, p. 428: **neither
treatment of the bound implies the other** (bounded rate paths, `β = 9/10`, `K = 1 + 2.26⁻²`). -/
theorem neither_implies :
    (¬ ∀ i : ℕ → Unit → ℝ, BoundedProc i → PathwiseZLB i →
        MomentFeasible perfectForesight (9 / 10) (bigK 2.26) i ()) ∧
      ¬ ∀ i : ℕ → Unit → ℝ, BoundedProc i →
        MomentFeasible perfectForesight (9 / 10) (bigK 2.26) i () → PathwiseZLB i := by
  obtain ⟨a1, a2, a3⟩ := pathwise_not_moment
  obtain ⟨b1, b2, b3, -⟩ := moment_not_pathwise
  exact ⟨fun h => a3 (h _ a1 a2), fun h => b3 (h _ b1 b2)⟩

end Moments

/-! ## The zero-bound steady state and Woodford's welfare loss -/

/-- Woodford (2003), App. E.3, p. 696, restated from the Woodford Chapter 6 project
(`Sequences.lagS`); Cochrane (2023), §20.3, p. 485: the lag `a_{t−1}` with initial value
`a_{−1}`. -/
def lagS (am1 : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => am1
  | t + 1 => a t

/-- Woodford (2003), eq. (2.20), p. 399 (Proposition 6.3), restated from the Woodford
Chapter 6 project (the hypothesis of `Sequences.disp_bdd`); Cochrane (2023), §20.3, p. 485:
the dispersion law of motion `Δ_t = αΔ_{t−1} + α/(1 − α) p_t²`. -/
def DispRec (α Δm1 : ℝ) (Δ p : ℕ → ℝ) : Prop :=
  ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2

/-- Woodford (2003), (2.20), p. 399, and Cochrane (2023), §20.3, p. 485: at constant inflation
`π`, Woodford's dispersion is `Δ_t = D + α^{t+1}(Δ_{−1} − D)`, `D = ZLBWelfare.dispersion α π`
(the shared object: Cochrane's stationary Calvo dispersion is Woodford's fixed point). -/
theorem disp_const_closed {α Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α Δm1 Δ fun _ => π) (t : ℕ) :
    Δ t = ZLBWelfare.dispersion α π + α ^ (t + 1) * (Δm1 - ZLBWelfare.dispersion α π) := by
  have hfix := ZLBWelfare.dispersion_fixed_point h0 h1 π
  induction t with
  | zero =>
    rw [hrec 0]
    simp only [lagS, zero_add, pow_one]
    linear_combination -hfix
  | succ t ih =>
    rw [hrec (t + 1)]
    simp only [lagS]
    rw [ih, pow_succ]
    linear_combination -hfix

/-- Woodford (2003), (2.20), and Cochrane (2023), §20.3, p. 485: at constant inflation Woodford's
dispersion converges to Cochrane's stationary dispersion `ZLBWelfare.dispersion α π`. -/
theorem disp_const_tendsto {α Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α Δm1 Δ fun _ => π) :
    Tendsto Δ atTop (𝓝 (ZLBWelfare.dispersion α π)) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
    (tendsto_add_atTop_nat 1)).mul_const (Δm1 - ZLBWelfare.dispersion α π)
  rw [zero_mul] at h
  have h2 := h.const_add (ZLBWelfare.dispersion α π)
  rw [add_zero] at h2
  exact h2.congr fun t => (disp_const_closed h0 h1 hrec t).symm

/-- Woodford (2003), (2.20), and Cochrane (2023), §20.3, p. 485: started at Cochrane's
stationary dispersion, Woodford's dispersion stays there. -/
theorem disp_const_stationary {α π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α (ZLBWelfare.dispersion α π) Δ fun _ => π) (t : ℕ) :
    Δ t = ZLBWelfare.dispersion α π := by
  rw [disp_const_closed h0 h1 hrec t, sub_self, mul_zero, add_zero]

/-- Woodford (2003), p. 400 (the discounted dispersion, `Sequences.disp_discounted`), at
constant inflation; Cochrane (2023), §20.3, p. 485: `∑ βᵗΔ_t = D/(1 − β) + α(Δ_{−1} − D)/(1 − αβ)`
(genuine `HasSum`). -/
theorem disp_const_discounted {α β Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {Δ : ℕ → ℝ} (hrec : DispRec α Δm1 Δ fun _ => π) :
    HasSum (fun t => β ^ t * Δ t) (ZLBWelfare.dispersion α π / (1 - β) +
      α * (Δm1 - ZLBWelfare.dispersion α π) / (1 - α * β)) := by
  have hab0 : 0 ≤ α * β := mul_nonneg h0 hβ0
  have hab1 : α * β < 1 := by nlinarith
  have hA := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (ZLBWelfare.dispersion α π)
  have hB := (hasSum_geometric_of_lt_one hab0 hab1).mul_left
    (α * (Δm1 - ZLBWelfare.dispersion α π))
  convert hA.add hB using 1
  · funext t
    rw [disp_const_closed h0 h1 hrec t, mul_pow, pow_succ]
    ring
  · rw [div_eq_mul_inv, div_eq_mul_inv]

/-- Woodford (2003), Proposition 6.3, p. 400 (the weight `α/((1 − α)(1 − αβ))` on `π²` in the
welfare loss), and Cochrane (2023), §20.3, p. 485: at constant inflation Woodford's discounted
average dispersion is Cochrane's stationary dispersion times `(1 − α)/(1 − αβ)`, which is
`απ²/((1 − α)(1 − αβ))`, plus a term `(1 − β)αΔ_{−1}/(1 − αβ)` independent of `π`. -/
theorem disp_const_avg {α β Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {Δ : ℕ → ℝ} (hrec : DispRec α Δm1 Δ fun _ => π) :
    (1 - β) * ∑' t, β ^ t * Δ t =
        ZLBWelfare.dispersion α π * ((1 - α) / (1 - α * β)) +
          (1 - β) * α * Δm1 / (1 - α * β) ∧
      ZLBWelfare.dispersion α π * ((1 - α) / (1 - α * β)) =
        α * π ^ 2 / ((1 - α) * (1 - α * β)) := by
  have hab : 0 < 1 - α * β := by nlinarith
  have h1' : 0 < 1 - α := by linarith
  have hb' : 0 < 1 - β := by linarith
  have hne : 1 - α * β ≠ 0 := hab.ne'
  have hne2 : 1 - β ≠ 0 := hb'.ne'
  rw [(disp_const_discounted h0 h1 hβ0 hβ1 hrec).tsum_eq]
  refine ⟨?_, ?_⟩
  · have hu : (1 - α * β) * (1 - α * β)⁻¹ = 1 := mul_inv_cancel₀ hne
    have hv : (1 - β) * (1 - β)⁻¹ = 1 := mul_inv_cancel₀ hne2
    simp only [div_eq_mul_inv]
    linear_combination ZLBWelfare.dispersion α π * hv - ZLBWelfare.dispersion α π * hu
  · rw [ZLBWelfare.dispersion_eq h0 h1]
    field_simp

/-- Cochrane (2023), §20.3, pp. 484–485 (`ZLBWelfare.zlb_better_iff`, corrected E9), in
**Woodford's (2003) welfare criterion** (discounted dispersion, Proposition 6.3, p. 400): with
the same initial dispersion and discount factor, the zero-bound steady state `Π_L = β`
(constant inflation `log β`) has strictly lower discounted dispersion than the target
`Π* ≥ 1` iff `1 < βΠ*`. -/
theorem woodford_zlb_better_iff {α β Δm1 Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hP : 1 ≤ Pstar) {ΔL ΔS : ℕ → ℝ}
    (hL : DispRec α Δm1 ΔL fun _ => Real.log β) (hS : DispRec α Δm1 ΔS fun _ => Real.log Pstar) :
    (1 - β) * ∑' t, β ^ t * ΔL t < (1 - β) * ∑' t, β ^ t * ΔS t ↔ 1 < β * Pstar := by
  have hab : 0 < 1 - α * β := by nlinarith
  have hc : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) hab
  rw [(disp_const_avg h0.le h1 hβ0.le hβ1 hL).1, (disp_const_avg h0.le h1 hβ0.le hβ1 hS).1,
    add_lt_add_iff_right, mul_lt_mul_iff_left₀ hc]
  exact ZLBWelfare.zlb_better_iff h0 h1 hβ0 hβ1.le hP

/-- Woodford (2003), (2.24), p. 402 (the quadratic loss `π² + λx²`), and Cochrane (2023),
§20.3, p. 485: at a steady state with inflation `π` and `x̄ = (1 − β)π/κ`, the discounted
average loss `(1 − β)∑ βᵗ(π² + λx̄²)` is `ZLBWelfare.ssLoss`. -/
theorem quadLoss_steady {lam β κ π : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t => β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2))
        (ZLBWelfare.ssLoss lam β κ π / (1 - β)) ∧
      (1 - β) * ∑' t, β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2) =
        ZLBWelfare.ssLoss lam β κ π := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (ZLBWelfare.ssLoss lam β κ π)
  have hb : (1 : ℝ) - β ≠ 0 := by linarith
  have h' : HasSum (fun t => β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2))
      (ZLBWelfare.ssLoss lam β κ π / (1 - β)) := by
    convert h using 1
    · funext t; unfold ZLBWelfare.ssLoss; ring
    · rw [div_eq_inv_mul]
  refine ⟨h', ?_⟩
  rw [h'.tsum_eq]
  field_simp

/-- Galí (2015), p. 146 (correction C5 of the Galí Chapter 5 project, `ZLBDiscretion.deflGap`),
restated: the deflationary steady-state output gap `x̄ = −(1 − β)ρ/κ`; Cochrane (2023), §20.3,
p. 485. -/
noncomputable def deflGap (β κ ρ : ℝ) : ℝ := -((1 - β) * ρ / κ)

/-- Galí (2015), p. 146 (the deflationary steady state `π = −ρ`, `i = 0`, of the Galí Chapter 5
project's `deflation_discEq`), with Galí's `ρ ≡ −log β`, **is Cochrane's (2023) zero-bound
steady state `Π_L = β`** (§20.3, p. 484, `ZLBWelfare.zlb_steady_state`): the constant path solves
the Phillips curve and has `i = 0`, its inflation is `log β = log Π_L`, and its output gap is the
steady-state Phillips-curve gap `(1 − β) log β / κ` (`ZLBWelfare.ss_phillips_iff`). -/
theorem gali_deflation_steady {β κ σ ρ : ℝ} (hβ0 : 0 < β) (hκ : κ ≠ 0)
    (hρ : ρ = -Real.log β) :
    (∀ t, NKPC β κ (fun _ => deflGap β κ ρ) (fun _ => -ρ) t) ∧
      (∀ t, impliedRate σ (fun _ => ρ) (fun _ => deflGap β κ ρ) (fun _ => -ρ) t = 0) ∧
      -ρ = Real.log β ∧ Real.exp (-ρ) = β ∧
      (∀ PL, PL = β * (1 + 0) → PL = Real.exp (-ρ)) ∧
      deflGap β κ ρ = (1 - β) * Real.log β / κ := by
  have hl : -ρ = Real.log β := by rw [hρ, neg_neg]
  have he : Real.exp (-ρ) = β := by rw [hl, Real.exp_log hβ0]
  refine ⟨fun t => ?_, fun t => ?_, hl, he, fun PL hPL => ?_, ?_⟩
  · unfold NKPC deflGap
    field_simp
    ring
  · unfold impliedRate
    ring
  · rw [ZLBWelfare.zlb_steady_state hPL rfl, he]
  · unfold deflGap
    rw [← hl]
    ring

/-- Cochrane (2023), §20.3, pp. 484–485 (`ZLBWelfare.zlb_worse_iff`), applied to Galí's (2015)
setting, whose target is zero inflation (`Π* = 1`): Galí's deflationary steady state
(`π = −ρ = log β`, `0 < β < 1`) has strictly more relative-price dispersion, a strictly larger
Woodford discounted dispersion (same initial dispersion), and a strictly larger steady-state
quadratic loss than the target. -/
theorem gali_deflation_worse {α β Δm1 lam κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hlam : 0 ≤ lam) {ΔL ΔS : ℕ → ℝ}
    (hL : DispRec α Δm1 ΔL fun _ => Real.log β) (hS : DispRec α Δm1 ΔS fun _ => 0) :
    ZLBWelfare.dispersion α 0 < ZLBWelfare.dispersion α (Real.log β) ∧
      (1 - β) * ∑' t, β ^ t * ΔS t < (1 - β) * ∑' t, β ^ t * ΔL t ∧
      ZLBWelfare.ssLoss lam β κ 0 < ZLBWelfare.ssLoss lam β κ (Real.log β) := by
  have hlog : Real.log β < 0 := Real.log_neg hβ0 hβ1
  have hd : ZLBWelfare.dispersion α 0 < ZLBWelfare.dispersion α (Real.log β) := by
    have := (ZLBWelfare.zlb_worse_iff h0 h1 hβ0 hβ1.le (le_refl (1 : ℝ))).2 (by linarith)
    rwa [Real.log_one] at this
  have hab : 0 < 1 - α * β := by nlinarith
  have hc : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) hab
  refine ⟨hd, ?_, ?_⟩
  · rw [(disp_const_avg h0.le h1 hβ0.le hβ1 hL).1, (disp_const_avg h0.le h1 hβ0.le hβ1 hS).1,
      add_lt_add_iff_right, mul_lt_mul_iff_left₀ hc]
    exact hd
  · rw [ZLBWelfare.ssLoss_lt_iff hlam, abs_zero, abs_pos]
    exact hlog.ne


/-! ## Galí's verification theorem (restated from the Galí Chapter 5 project) -/

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (14), p. 135: `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: `4βγ² < 1`, so `δ` is real (for every `κ`). -/
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

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: the square root `s = Real.sqrt (1 − 4βγ²)` satisfies `s² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: `δ · 2γβ = 1 − Real.sqrt (1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136 and footnote 4: `δ` is a root of `γβδ² − δ + γ = 0`, the
undetermined-coefficients condition for `p̂_t = δ p̂_{t−1} + b u_t` to solve (14). -/
theorem del_quad {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    gam β κ ϑ * β * del β κ ϑ ^ 2 - del β κ ϑ + gam β κ ϑ = 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hδ := del_mul (κ := κ) hβ0 hϑ
  have hs2 := sqrt_sq_eq (κ := κ) hβ0 hβ1 hϑ
  set g := gam β κ ϑ
  set s := Real.sqrt (1 - 4 * β * g ^ 2)
  set d := del β κ ϑ
  have h4 : (4 * g * β) * (g * β * d ^ 2 - d + g) = 0 := by
    linear_combination (2 * g * β * d + (1 - s) - 2) * hδ + hs2
  rcases mul_eq_zero.1 h4 with h | h
  · exfalso; have : 0 < 4 * g * β := by positivity
    linarith
  · exact h

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 143 (key identity, used for (15) and (24)): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: `lag f (t + 1) = f t`. -/
@[simp] theorem lag_succ (f : ℕ → ℝ) (t : ℕ) : lag f (t + 1) = f t := rfl

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: `lag f 0 = 0` (the initial conditions `ξ₁,₋₁ = ξ₂,₋₁ = 0`). -/
@[simp] theorem lag_zero (f : ℕ → ℝ) : lag f 0 = 0 := rfl

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (35), p. 149: `π_t + ξ₁,t − ξ₁,t−1 − ξ₂,t−1/(βσ) = 0`. -/
def FOC35 (β σ : ℝ) (π ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  π t + ξ1 t - lag ξ1 t - lag ξ2 t / (β * σ) = 0

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: the KKT system of the commitment problem — feasibility, the FOCs
(35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, and the slackness conditions `ξ₂ ≥ 0`, `ξ₂ i = 0`. -/
def KKT (β κ σ ϑ : ℝ) (rn x π ξ1 ξ2 : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ ∀ t, FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t ∧ 0 ≤ ξ2 t ∧
    ξ2 t * impliedRate σ rn x π t = 0

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: the Lagrangian identity (summation by parts). For a direction
`(dx, dπ)` satisfying the linearised Phillips curve, the first variation of the truncated loss
equals the inequality-multiplier terms plus a boundary term. -/
theorem lagrangian_identity {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {x π ξ1 ξ2 dx dπ : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (π t * dπ t + ϑ * x t * dx t) =
      ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * (dx (s + 1) + dπ (s + 1) / σ - dx s)) -
        β ^ T * ξ2 T * dx T - β ^ (T + 1) * ξ1 T * dπ (T + 1) := by
  induction T with
  | zero =>
    have a := h35 0
    have b := h36 0
    simp only [FOC35, FOC36, lag_zero, zero_div, sub_zero] at a b
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, pow_zero,
      pow_one, one_mul, zero_sub]
    linear_combination dπ 0 * a + dx 0 * b - ξ1 0 * hd 0
  | succ T ih =>
    have a := h35 (T + 1)
    have b := h36 (T + 1)
    simp only [FOC35, FOC36, lag_succ] at a b
    have e1 : β ^ (T + 1) * (ξ2 T / (β * σ)) = β ^ T * ξ2 T / σ := by
      rw [pow_succ]; field_simp
    have e2 : β ^ (T + 1) * (ξ2 T / β) = β ^ T * ξ2 T := by
      rw [pow_succ]; field_simp
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    linear_combination β ^ (T + 1) * dπ (T + 1) * a + β ^ (T + 1) * dx (T + 1) * b -
      β ^ (T + 1) * ξ1 (T + 1) * hd (T + 1) + dπ (T + 1) * e1 + dx (T + 1) * e2

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: if `∑ β^t a_t²` is summable-small (`β^t a_t² → 0`) and `0 ≤ β < 1`,
then `β^t |a_t| → 0`. -/
theorem tendsto_pow_mul_abs {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ}
    (h : Filter.Tendsto (fun t => β ^ t * a t ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => β ^ t * |a t|) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun t => (β ^ t + β ^ t * a t ^ 2) / 2) Filter.atTop
      (nhds ((0 + 0) / 2)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).add h).div_const 2
  rw [add_zero, zero_div] at hg
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hg
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have : |a t| ≤ (1 + a t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a t| - 1), sq_abs (a t)]
  nlinarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: SUFFICIENCY of the KKT system (Lagrangian + convexity). If `(x, π)`
satisfies the KKT system with bounded multipliers and has finite loss, then for every feasible
`(y, q)` with finite loss, `loss (x, π) + ∑ β^t ((q_t − π_t)² + ϑ (y_t − x_t)²) ≤ loss (y, q)`. -/
theorem kkt_sufficient {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q)) :
    Summable (fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2)) ∧
      loss β ϑ x π + ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) ≤
        loss β ϑ y q := by
  obtain ⟨hF, hK⟩ := hK
  obtain ⟨C, hC⟩ := hb
  set D : ℕ → ℝ := fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hsy.add hs).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2 ≤
        2 * ((q t ^ 2 + ϑ * y t ^ 2) + (π t ^ 2 + ϑ * x t ^ 2)) := by
      nlinarith [sq_nonneg (q t + π t), sq_nonneg (y t + x t)]
    nlinarith
  refine ⟨hDs, ?_⟩
  -- the boundary terms vanish
  have hD_lim := hDs.tendsto_atTop_zero
  have hdx : Filter.Tendsto (fun t => β ^ t * |y t - x t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      (by simpa using hD_lim.div_const ϑ))
    simp only [hDdef]
    rw [le_div_iff₀ hϑ]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [sq_nonneg (q t - π t)]
  have hdπ : Filter.Tendsto (fun t => β ^ t * |q t - π t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      hD_lim)
    simp only [hDdef]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [mul_nonneg hp (mul_nonneg hϑ.le (sq_nonneg (y t - x t)))]
  set b : ℕ → ℝ := fun T => C * (β ^ T * |y T - x T|) +
    C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) with hbdef
  have hb_lim : Filter.Tendsto (fun T => -(2 * b T)) Filter.atTop (nhds 0) := by
    have := ((hdx.const_mul C).add ((hdπ.comp (Filter.tendsto_add_atTop_nat 1)).const_mul C))
    simpa [hbdef] using (this.const_mul 2).neg
  -- partial sums
  have hlimL : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t)
      Filter.atTop (nhds (loss β ϑ y q - loss β ϑ x π - ∑' t, D t)) := by
    have h1 := hsy.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h3 := hDs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact (h1.sub h2).sub h3
  have hineq : ∀ T, -(2 * b T) ≤ ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t := by
    intro T
    have hsplit : ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
        ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t =
        2 * ∑ t ∈ Finset.range (T + 1),
          β ^ t * (π t * (q t - π t) + ϑ * x t * (y t - x t)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, hDdef]
      ring
    have hd : ∀ t, q t - π t = β * (q (t + 1) - π (t + 1)) + κ * (y t - x t) := by
      intro t
      have h1 := (hy t).1
      have h2 := (hF t).1
      unfold NKPC at h1 h2
      linarith
    have hid := lagrangian_identity hβ.ne' hσ.ne' (fun t => (hK t).1) (fun t => (hK t).2.1)
      (dx := fun t => y t - x t) (dπ := fun t => q t - π t) hd T
    rw [hsplit, hid]
    have hsum : 0 ≤ ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * ((y (s + 1) - x (s + 1)) +
        (q (s + 1) - π (s + 1)) / σ - (y s - x s))) := by
      refine Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hβ.le s) ?_
      have hslack : ξ2 s * (ups1 σ rn x π s - x s) = 0 := by
        have h := (hK s).2.2.2
        rw [impliedRate_eq hσ.ne'] at h
        rw [mul_left_comm] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hσ.ne'
        · exact h'
      have hfy : 0 ≤ ξ2 s * (ups1 σ rn y q s - y s) :=
        mul_nonneg (hK s).2.2.1 (by linarith [(hy s).2])
      have e : ξ2 s * ((y (s + 1) - x (s + 1)) + (q (s + 1) - π (s + 1)) / σ - (y s - x s)) =
          ξ2 s * (ups1 σ rn y q s - y s) - ξ2 s * (ups1 σ rn x π s - x s) := by
        unfold ups1; ring
      rw [e, hslack]
      linarith
    have hC1 := (hC T).2
    have hC2 := (hC T).1
    have hp : 0 ≤ β ^ T := pow_nonneg hβ.le T
    have hp1 : 0 ≤ β ^ (T + 1) := pow_nonneg hβ.le (T + 1)
    have k1 : |β ^ T * ξ2 T * (y T - x T)| ≤ C * (β ^ T * |y T - x T|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp]
      have := abs_nonneg (y T - x T)
      nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (mul_nonneg hp this)]
    have k2 : |β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1))| ≤
        C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp1]
      have := abs_nonneg (q (T + 1) - π (T + 1))
      nlinarith [mul_nonneg (sub_nonneg.mpr hC2) (mul_nonneg hp1 this)]
    have k3 := le_abs_self (β ^ T * ξ2 T * (y T - x T))
    have k4 := le_abs_self (β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1)))
    simp only [hbdef]
    linarith
  have := le_of_tendsto_of_tendsto' hb_lim hlimL hineq
  unfold loss at this ⊢
  linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: a KKT path with bounded multipliers and finite loss is optimal. -/
theorem kkt_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π)) :
    Optimal β κ σ ϑ rn x π := by
  refine ⟨hK.1, hs, fun y q hy hsy => ?_⟩
  obtain ⟨hDs, hle⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have : 0 ≤ ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) :=
    tsum_nonneg fun t => by positivity
  linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: UNIQUENESS — a KKT path (bounded multipliers, finite loss) is the
only feasible path with finite loss whose loss is no larger. -/
theorem kkt_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q))
    (hle : loss β ϑ y q ≤ loss β ϑ x π) : y = x ∧ q = π := by
  obtain ⟨hDs, hle2⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have hz := eq_zero_of_tsum_nonpos (fun t => by positivity) hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), pp. 149–150: the multiplier `ξ₁,t_C+1+k = δ^k ξ` (from (38) and (42)). -/
noncomputable def postXi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := del β κ ϑ ^ k * ξ

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (37), p. 149: `π_t + ξ₁,t − ξ₁,t−1 = 0` after liftoff. -/
theorem post_eq37 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k + postXi β κ ϑ ξ (k + 1) - postXi β κ ϑ ξ k = 0 := by
  unfold postPi postXi; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (38), p. 149: `ϑ x_t − κ ξ₁,t = 0` after liftoff. -/
theorem post_eq38 {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    ϑ * postX β κ ϑ ξ k - κ * postXi β κ ϑ ξ (k + 1) = 0 := by
  unfold postX postXi; field_simp; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (39), p. 149: the Phillips curve `π_t = β π_{t+1} + κ x_t` after liftoff. -/
theorem post_eq39 {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k = β * postPi β κ ϑ ξ (k + 1) + κ * postX β κ ϑ ξ k := by
  have key : κ ^ 2 * del β κ ϑ =
      ϑ * (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
    have h := kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  unfold postPi postX
  set δ := del β κ ϑ
  field_simp
  linear_combination (-(δ ^ k * ξ)) * key

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: after liftoff the implied rate is
`i_{t_C+2+k} = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`. -/
theorem post_rate {β κ σ ϑ ρ η : ℝ} (hϑ : ϑ ≠ 0) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    {ξ : ℝ} (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k) (k : ℕ) :
    impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) =
      ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (k + 1) * ξ := by
  unfold impliedRate
  rw [natRate_of_lt (by omega), show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hx, hπ]
  unfold postX postPi
  field_simp
  ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: the infinitely many conditions `i_t ≥ 0`, `t ≥ t_C + 2`, reduce to the
single condition `i_{t_C+2} ≥ 0` (the rate moves monotonically towards `ρ > 0`). -/
theorem post_rate_nonneg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ} {ξ : ℝ}
    (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k) (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k)
    (h0 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (k : ℕ) :
    0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have e0 : impliedRate σ (natRate ρ η tZ) x π (tC + 2) =
      ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (0 + 1) * ξ :=
    post_rate hϑ.ne' htC hx hπ 0
  rw [e0] at h0
  rw [post_rate hϑ.ne' htC hx hπ k]
  set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  have hk : (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (k + 1) * ξ =
      A * del β κ ϑ ^ (k + 1) := by rw [hA]; ring
  have h0' : (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (0 + 1) * ξ =
      A * del β κ ϑ := by rw [hA]; ring
  rw [hk]
  rw [h0'] at h0
  have hp : del β κ ϑ ^ (k + 1) ≤ del β κ ϑ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1.le)
  have hp0 : 0 ≤ del β κ ϑ ^ (k + 1) := pow_nonneg hδ0.le _
  rcases le_or_gt 0 A with hA0 | hA0
  · have := mul_nonneg hA0 hp0; linarith
  · nlinarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: one backward step of (48)/(49) gives the Phillips curve and `i_t = 0`. -/
theorem backStep_nkpc_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) (hr : rn t = -e) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hr, hx]; field_simp; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152, VERIFICATION THEOREM for the algorithm. Guess `t_C ≥ t_Z`. Suppose the
candidate path satisfies (48) on `[0, t_Z]`, (49) on `(t_Z, t_C]`, (50) for `t ≤ t_C + 1`, the
Phillips curve at `t_C + 1` (i.e. (46)), `ξ₂,t_C+1 = 0`, and follows (42)–(43) (with
`ξ₁,t = δ^{t−t_C−1} ξ₁,t_C+1`, `ξ₂,t = 0`) after `t_C + 1`. If the sign conditions
`ξ₂,t ≥ 0` hold on `[0, t_C]` and `i ≥ 0` at `t_C + 1` and `t_C + 2`, then the candidate
satisfies the KKT system, is optimal, keeps `i_t = 0` on `[0, t_C]` (with `i ≥ 0` everywhere),
and is the unique optimal path. -/
theorem algorithm_verification {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) :
    KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, 0 ≤ impliedRate σ (natRate ρ η tZ) x π t) ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact backStep_nkpc_rate hσ.ne' (h48 t h) (by rw [hrn, natRate_of_le h])
    · exact backStep_nkpc_rate hσ.ne' (h49 t h ht) (by rw [hrn, natRate_of_lt h, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrate : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hi1
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        exact post_rate_nonneg hβ hβ1 hκ hϑ hρ htC hx hπ hi2 k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨feasible_of_rate hσ fun t => ⟨hnkpc t, hrate t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1 : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2 : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1, l2, x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2, x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  -- bounded multipliers
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  -- finite loss
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  refine ⟨hK, kkt_optimal hβ hβ1 hσ hϑ hK hb hs, fun t ht => (hbind t ht).2, hrate,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2, p. 152: **discretion is strictly
worse than commitment**, from the algorithm's conditions alone. Under the hypotheses of
`algorithm_verification` and `ξ₁,t_C+1 > 0`, the candidate is the commitment optimum and the
discretionary path has strictly larger loss (and strictly lower `x_t`, `π_t` at every date,
`comm_gt_disc`). -/
theorem comm_loss_lt_alg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (hξ : 0 < ξ1 (tC + 1)) :
    Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  have hopt := (algorithm_verification hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h50 h46 hξ2 hpost hsign
    hi1 hi2).2.1
  exact ⟨hopt, comm_loss_lt hβ hβ1 hκ hσ hϑ hρ htC h48 h49 (h50 (tC + 1) le_rfl).2 h46 hξ2
    (fun k => ⟨(hpost k).1, (hpost k).2.1⟩) (hsign tC le_rfl) hξ hopt⟩


/-! ## The sign of `ξ₁,t_C+1` and the lift-off date at the optimum -/

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), §20.2.4, p. 479: summing (35) with
`ξ₋₁ = 0`, `ξ₁,N = (βσ)⁻¹ ∑_{s<N} ξ₂,s − p_N` with `p_N = ∑_{s≤N} π_s` the price level
(`p₋₁ = 0`). -/
theorem xi1_eq {β σ : ℝ} {π ξ1 ξ2 : ℕ → ℝ} {N : ℕ}
    (h35 : ∀ t, t ≤ N → FOC35 β σ π ξ1 ξ2 t) :
    ξ1 N = (∑ s ∈ Finset.range N, ξ2 s) / (β * σ) - ∑ s ∈ Finset.range (N + 1), π s := by
  induction N with
  | zero =>
    have h := h35 0 le_rfl
    unfold FOC35 at h
    simp only [lag_zero, zero_div, sub_zero] at h
    simp only [Finset.range_zero, Finset.sum_empty, zero_div, zero_add, Finset.sum_range_one,
      zero_sub]
    linarith
  | succ N ih =>
    have h := h35 (N + 1) le_rfl
    unfold FOC35 at h
    simp only [lag_succ] at h
    have hN := ih (fun t ht => h35 t (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun s => π s) (N + 1), add_div]
    linarith

/-- Galí (2015), pp. 149–150; Cochrane (2023), §20.2.4, p. 479: **the precise condition for
`ξ₁,t_C+1 > 0`** (the sign Galí assumes for (42)–(43)): it holds iff the price level at lift-off
is below `(βσ)⁻¹ ∑_{s≤t_C} ξ₂,s`, i.e. below its long-run level (`longrun_price`). -/
theorem xi_pos_iff {β σ : ℝ} {π ξ1 ξ2 : ℕ → ℝ} {tC : ℕ}
    (h35 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t) :
    0 < ξ1 (tC + 1) ↔
      ∑ s ∈ Finset.range (tC + 2), π s < (∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ) := by
  rw [xi1_eq h35]
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (41), p. 150; Cochrane (2023), §20.2.4, p. 479 (price-level targeting under
commitment): under (35) up to lift-off and the closed form (43) after it, the price level
converges to `(βσ)⁻¹ ∑_{s≤t_C} ξ₂,s`, which is `≥ 0` (the initial level) when `ξ₂ ≥ 0`. -/
theorem longrun_price {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {π ξ1 ξ2 : ℕ → ℝ} {tC : ℕ} (h35 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k) :
    Tendsto (fun k => ∑ s ∈ Finset.range (tC + 2 + k), π s) atTop
      (𝓝 ((∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ))) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1)
  set P := ∑ s ∈ Finset.range (tC + 2), π s
  have hsum : ∀ k, ∑ s ∈ Finset.range (tC + 2 + k), π s = P + ξ * (1 - del β κ ϑ ^ k) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      rw [show tC + 2 + (k + 1) = tC + 2 + k + 1 by omega, Finset.sum_range_succ, ih,
        show tC + 2 + k = tC + k + 2 by omega, hπ k]
      unfold postPi
      ring
  have hlim : Tendsto (fun k => P + ξ * (1 - del β κ ϑ ^ k)) atTop (𝓝 (P + ξ * (1 - 0))) :=
    tendsto_const_nhds.add
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).const_sub 1).const_mul ξ)
  have hx := xi1_eq h35
  rw [sub_zero, mul_one] at hlim
  have e : P + ξ = (∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ) := by
    simp only [ξ, P]; rw [hx]; ring
  rw [e] at hlim
  exact hlim.congr fun k => (hsum k).symm

/-- Galí (2015), eqs. (42)–(43), p. 150; Cochrane (2023), p. 479: with `ξ₁,t_C+1 < 0` output and
inflation are strictly NEGATIVE at every date after lift-off (the signs of (42)–(43) reverse). -/
theorem post_neg {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : ξ < 0)
    (k : ℕ) : postX β κ ϑ ξ k < 0 ∧ postPi β κ ϑ ξ k < 0 := by
  have h0 := del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - del β κ ϑ := by linarith [(del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  have hp : 0 < del β κ ϑ ^ k := pow_pos h0 k
  have hp1 : 0 < del β κ ϑ ^ (k + 1) := pow_pos h0 _
  unfold postX postPi
  constructor
  · have : κ * del β κ ϑ ^ (k + 1) * ξ < 0 := mul_neg_of_pos_of_neg (by positivity) hξ
    exact div_neg_of_neg_of_pos this hϑ
  · exact mul_neg_of_pos_of_neg (by positivity) hξ

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: the commitment path lies strictly
above the delayed-lift-off path with the same lift-off date on `[0, t_C]` whenever its lift-off
state is weakly positive and nonzero — no assumption on the sign of `ξ₁,t_C+1`. -/
theorem comm_gt_delay_of_state {β κ σ ρ η : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) :
    (delayPath β κ σ ρ η tZ (tC + 1) t).1 < x t ∧ (delayPath β κ σ ρ η tZ (tC + 1) t).2 < π t := by
  have hd : delayPath β κ σ ρ η tZ (tC + 1) (tC + 1) = (0, 0) := delay_after le_rfl
  exact zr_strict hβ.le hκ hσ (e := fun t => -natRate ρ η tZ t) (N := tC + 1)
    (p := fun t => (x t, π t)) (fun s hs => comm_step h48 h49 s hs)
    (fun s hs => delay_step hs) (by rw [hd]; exact hx) (by rw [hd]; exact hp)
    (by rw [hd]; exact hs) t (by omega)

/-- Cochrane (2023), §20.2.4, p. 479: hence, with a weakly positive nonzero lift-off state, the
commitment path is strictly above discretion on the whole zero-rate spell `[0, t_C]`. -/
theorem comm_gt_disc_of_state {β κ σ ρ η : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) : discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t := by
  have a := comm_gt_delay_of_state hβ hκ hσ (ρ := ρ) h48 h49 hx hp hs t ht
  have b := delay_le_of_le (η := η) hβ.le hκ hσ hρ (tZ := tZ) le_rfl
    (show tZ + 1 ≤ tC + 1 by omega) t
  rw [delay_eq_disc] at b
  exact ⟨b.1.trans_lt a.1, b.2.trans_lt a.2⟩

/-! ### An exact parameter point: lift-off at the end of the shock and `ξ₁,t_C+1 < 0` -/

/-- Galí (2015), (15), p. 136; Cochrane (2023), p. 479: at `β = 9/10`, `κ = 1/10`,
`ϑ = 1/819` the coefficient `δ` is exactly `1/10` (`γ = 100/1009`,
`√(1 − 4βγ²) = 991/1009`). -/
theorem del_cex : del (9 / 10) (1 / 10) (1 / 819) = 1 / 10 := by
  unfold del gam
  have hs : Real.sqrt (1 - 4 * (9 / 10) * ((1 / 819) / ((1 / 819) * (1 + 9 / 10) +
      (1 / 10) ^ 2)) ^ 2) = 991 / 1009 := by
    rw [show (1 - 4 * (9 / 10) * ((1 / 819) / ((1 / 819) * (1 + 9 / 10) + (1 / 10) ^ 2)) ^ 2 :
      ℝ) = (991 / 1009) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs]
  norm_num

/-- Cochrane (2023), §20.2.4, p. 479: the multiplier `ξ₁,1` at the exact point. -/
noncomputable def cexXi : ℝ := -743471 / 4255023510

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the output gap of the exact point
(`t_Z = t_C = 0`): `x₀, x₁`, then (42). -/
noncomputable def cexX (t : ℕ) : ℝ :=
  if t = 0 then -2226861 / 472780390 else if t = 1 then 23344139 / 4727803900
  else postX (9 / 10) (1 / 10) (1 / 819) cexXi (t - 2)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: inflation at the exact point: `π₀, π₁`, then
(43). -/
noncomputable def cexPi (t : ℕ) : ℝ :=
  if t = 0 then -7281 / 47278039 else if t = 1 then 166529 / 472780390
  else postPi (9 / 10) (1 / 10) (1 / 819) cexXi (t - 2)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the multiplier `ξ₁` at the exact point. -/
noncomputable def cexXi1 (t : ℕ) : ℝ :=
  if t = 0 then 7281 / 47278039 else postXi (9 / 10) (1 / 10) (1 / 819) cexXi (t - 1)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the ZLB multiplier `ξ₂` at the exact point
(positive at date 0 only). -/
noncomputable def cexXi2 (t : ℕ) : ℝ := if t = 0 then 1000 / 47278039 else 0

/-- Cochrane (2023), p. 479: `ξ₁,1 = ξ` at the exact point. -/
theorem cexXi1_one : cexXi1 1 = cexXi := by
  simp [cexXi1, postXi]

/-- Galí (2015), p. 152 (`algorithm_verification` at an exact point); Cochrane (2023), §20.2.4,
p. 479: with `β = 9/10`, `κ = 1/10`, `σ = 1`, `ϑ = 1/819` (so `δ = 1/10`), `ρ = 1/10`,
`η = 1/100`, `t_Z = 0`, the path `cexX`, `cexPi` with multipliers `cexXi1`, `cexXi2` passes the
algorithm with `t_C = t_Z = 0`: it is the commitment optimum, and the unique one. -/
theorem cex_optimal :
    Optimal (9 / 10) (1 / 10) 1 (1 / 819) (natRate (1 / 10) (1 / 100) 0) cexX cexPi ∧
      (∀ y q, Optimal (9 / 10) (1 / 10) 1 (1 / 819) (natRate (1 / 10) (1 / 100) 0) y q →
        y = cexX ∧ q = cexPi) ∧
      impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi 0 = 0 := by
  have hd := del_cex
  have hv := algorithm_verification (β := 9 / 10) (κ := 1 / 10) (σ := 1) (ϑ := 1 / 819)
    (ρ := 1 / 10) (η := 1 / 100) (tZ := 0) (tC := 0) (x := cexX) (π := cexPi) (ξ1 := cexXi1)
    (ξ2 := cexXi2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp only [cexX, cexPi, backStep]
      norm_num)
    (fun t h1 h2 => absurd h2 (by omega))
    (fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · simp only [FOC35, FOC36, lag_zero, cexX, cexPi, cexXi1, cexXi2]
        norm_num
      · simp only [FOC35, FOC36, lag_succ, cexX, cexPi, cexXi1, cexXi2, postXi, cexXi]
        norm_num)
    (by simp only [NKPC, cexX, cexPi, postPi, hd, cexXi]; norm_num)
    (by simp [cexXi2])
    (fun k => by
      rw [cexXi1_one]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [cexX, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]
      · simp only [cexPi, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]
      · simp only [cexXi1, show 0 + k + 2 ≠ 0 by omega, ↓reduceIte,
          show 0 + k + 2 - 1 = k + 1 by omega]
      · simp [cexXi2])
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp only [cexXi2]; norm_num)
    (by
      simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
      norm_num)
    (by
      simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
      norm_num)
  obtain ⟨-, hopt, hzero, -, -⟩ := hv
  exact ⟨hopt, fun y q h => (optimal_unique (by norm_num) (by norm_num) h hopt),
    hzero 0 le_rfl⟩

/-- Cochrane (2023), §20.2.4, p. 479, against Galí (2015), §5.4.2 (correction): at the exact
point the commitment optimum **lifts off at the end of the shock**, `t_C = t_Z = 0`: the rate
is `0` at date 0 and strictly positive at every later date. So "keeping the rate at zero beyond
the end of the shock" (`t_C > t_Z`) is not a property of every commitment optimum. -/
theorem cex_liftoff_at_shock_end :
    impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi 0 = 0 ∧
      ∀ t, 1 ≤ t → 0 < impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi t := by
  have hd := del_cex
  refine ⟨cex_optimal.2.2, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl : t = 1 := by omega
    simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, t = 0 + k + 2 := ⟨t - 2, by omega⟩
    rw [post_rate (β := 9 / 10) (κ := 1 / 10) (σ := 1) (ϑ := 1 / 819) (ρ := 1 / 10)
      (η := 1 / 100) (by norm_num) le_rfl (ξ := cexXi)
      (fun k => by simp only [cexX, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega])
      (fun k => by simp only [cexPi, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]) k, hd]
    have hp : (0 : ℝ) < (1 / 10) ^ (k + 1) := by positivity
    unfold cexXi
    nlinarith

/-- Cochrane (2023), §20.2.4, p. 479, against Galí (2015), eqs. (42)–(43), p. 150 (correction):
at the exact point the commitment optimum has `ξ₁,t_C+1 < 0`, and **output and inflation are
strictly negative at every date after lift-off** (inflation strictly below the discretionary
path for `t ≥ 2`); the sign hypothesis `ξ₁,t_C+1 > 0` of `comm_gt_disc` cannot be dropped.
At the same time the lift-off state is positive, so the optimum still lies strictly above discretion
during the zero-rate spell (`comm_gt_disc_of_state`). -/
theorem cex_xi_neg :
    cexXi1 1 < 0 ∧ (∀ t, 2 ≤ t → cexX t < 0 ∧ cexPi t < 0) ∧
      (∀ t, 2 ≤ t → cexPi t < discPi (9 / 10) (1 / 10) 1 (1 / 100) 0 t) ∧
      discX (9 / 10) (1 / 10) 1 (1 / 100) 0 0 < cexX 0 ∧
      discPi (9 / 10) (1 / 10) 1 (1 / 100) 0 0 < cexPi 0 := by
  have hneg : cexXi < 0 := by unfold cexXi; norm_num
  have hpost : ∀ t, 2 ≤ t → cexX t < 0 ∧ cexPi t < 0 := by
    intro t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    simp only [cexX, cexPi, show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, ↓reduceIte,
      Nat.add_sub_cancel]
    exact post_neg (by norm_num) (by norm_num) (by norm_num) (by norm_num) hneg k
  refine ⟨by rw [cexXi1_one]; exact hneg, hpost, fun t ht => ?_, ?_, ?_⟩
  · have hz := zlbPath_of_lt (β := 9 / 10) (κ := 1 / 10) (σ := 1) (η := 1 / 100)
      (sT := ((0 : ℝ), (0 : ℝ))) (show 0 < t by omega)
    unfold discPi
    rw [hz]
    exact (hpost t ht).2
  · simp only [discX, zlbPath, le_refl, ↓reduceIte, Nat.sub_zero, zero_add, backState,
      backStep, cexX]
    norm_num
  · simp only [discPi, zlbPath, le_refl, ↓reduceIte, Nat.sub_zero, zero_add, backState,
      backStep, cexPi]
    norm_num

end Cochrane.ZeroBound.LinksGaliWoodford

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The discrete Werning trap paths converge to the continuous-time ones

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476
(the Werning model (20.5)–(20.6) and its family of equilibria indexed by `π_T`), and §5.7.1,
p. 165 (discrete and continuous time).

Galí's discrete model with period length `h` (`β = 1 − ρh`, IS slope `σ⁻¹ = σh`, Phillips-curve
slope `κh`, rates per unit of time) during a zero-bound trap with natural rate `u`
(`η = −u`) is solved backward from the end-of-trap state `(c v_x, c)` of the discrete Werning
family (`LinksGaliWoodford.wState`). We prove the exact closed form of the discrete trap path
(two geometric modes `λ₁ᵐ`, `λ₂ᵐ` around the trap steady state) and that, cutting the time
`T − t` before the end of the trap into `n + 1` periods, the discrete output gap and inflation at
the date `n + 1` periods before the end converge to the continuous-time Werning paths
`WerningModel.wX`, `WerningModel.wPi` (with `π_T = c`, `g = 0`) at time `t`.

## Main results

* `tendsto_one_add_pow`: `(1 + τ g_n/(n+1))^{n+1} → e^{τL}` when `g_n → L`.
* `backState_modes`: the discrete trap path is `s̄ + λ₁ᵐ a v₁ + λ₂ᵐ b v₂` exactly.
* `trapDisc_closed`: the closed form at period length `h`, with the scaled roots `sr1`, `sr2`.
* `trapDisc_eq_wState`: the trap path is the discrete Werning family member `wState`.
* `trap_tendsto`, `trap_pi_tendsto`, `trap_x_tendsto`: **convergence of whole trap paths** to
  `wPi`, `wX` at every time `t < T`.
-/

namespace Cochrane.ZeroBound.LinksGaliWoodfordLimit

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford

/-- Cochrane (2023), §5.7.1, p. 165 (the exponential limit of compounding over `n + 1`
periods): if `g_n → L` then `(1 + τ g_n/(n + 1))^{n+1} → e^{τL}`. -/
theorem tendsto_one_add_pow {g : ℕ → ℝ} {L τ : ℝ} (hg : Tendsto g atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (1 + τ / ((n : ℝ) + 1) * g n) ^ (n + 1)) atTop
      (𝓝 (Real.exp (τ * L))) := by
  set y : ℕ → ℝ := fun n => τ / ((n : ℝ) + 1) * g n with hy
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => τ / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hy0 : Tendsto y atTop (𝓝 0) := by
    have := hdiv.mul hg
    rwa [zero_mul] at this
  have hny : ∀ n : ℕ, ((n : ℝ) + 1) * y n = τ * g n := by
    intro n
    simp only [hy]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hev : ∀ᶠ n in atTop, -(1 / 2 : ℝ) < y n :=
    hy0.eventually (lt_mem_nhds (by norm_num))
  have hup : Tendsto (fun n : ℕ => τ * g n) atTop (𝓝 (τ * L)) := hg.const_mul τ
  have hlo : Tendsto (fun n : ℕ => τ * g n / (1 + y n)) atTop (𝓝 (τ * L)) := by
    have h1 : Tendsto (fun n : ℕ => 1 + y n) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hy0
    rw [add_zero] at h1
    have := hup.div h1 one_ne_zero
    rwa [div_one] at this
  have hlog : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log (1 + y n)) atTop
      (𝓝 (τ * L)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [hev] with n hn
      have hpos : 0 < 1 + y n := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos hpos
      have e : τ * g n / (1 + y n) = ((n : ℝ) + 1) * (1 - (1 + y n)⁻¹) := by
        rw [← hny n]
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    · filter_upwards [hev] with n hn
      have hpos : 0 < 1 + y n := by linarith
      have hl := Real.log_le_sub_one_of_pos hpos
      rw [← hny n]
      have : Real.log (1 + y n) ≤ y n := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hev] with n hn
  have hpos : 0 < 1 + y n := by linarith
  simp only [Function.comp_apply]
  rw [← Real.exp_log (pow_pos hpos (n + 1)), Real.log_pow]
  push_cast
  rfl

/-! ## The exact closed form of a discrete trap path -/

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475 (two modes around the trap
steady state `(x̄, π̄) = ((1 − β)η/κ, η)`): if `λ₁, λ₂` solve
`λ² − (1 + β + κ/σ)λ + β = 0`, the backward step maps `s̄ + a v₁ + b v₂` to
`s̄ + λ₁ a v₁ + λ₂ b v₂`, `v_i = (1, σ(λ_i − 1))`. -/
theorem backStep_modes {β κ σ η l1 l2 a b : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (h1 : l1 ^ 2 - (1 + β + κ / σ) * l1 + β = 0) (h2 : l2 ^ 2 - (1 + β + κ / σ) * l2 + β = 0) :
    backStep β κ σ η ((1 - β) * η / κ + a + b, η + a * σ * (l1 - 1) + b * σ * (l2 - 1)) =
      ((1 - β) * η / κ + l1 * a + l2 * b,
        η + l1 * a * σ * (l1 - 1) + l2 * b * σ * (l2 - 1)) := by
  simp only [backStep]
  ext
  · simp only
    field_simp
    ring
  · simp only
    field_simp
    have hσ' : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
    linear_combination (-(a * σ ^ 2)) * h1 - b * σ ^ 2 * h2 - κ * σ * (a * l1 + b * l2) * hσ'

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475: `m` backward steps act on
the modes by `λ₁ᵐ`, `λ₂ᵐ` — the exact closed form of the discrete trap path. -/
theorem backState_modes {β κ σ η l1 l2 a b : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (h1 : l1 ^ 2 - (1 + β + κ / σ) * l1 + β = 0) (h2 : l2 ^ 2 - (1 + β + κ / σ) * l2 + β = 0)
    (m : ℕ) :
    backState β κ σ η ((1 - β) * η / κ + a + b, η + a * σ * (l1 - 1) + b * σ * (l2 - 1)) m =
      ((1 - β) * η / κ + l1 ^ m * a + l2 ^ m * b,
        η + l1 ^ m * a * σ * (l1 - 1) + l2 ^ m * b * σ * (l2 - 1)) := by
  induction m with
  | zero => simp [backState]
  | succ m ih =>
    rw [backState, ih, backStep_modes hκ hσ h1 h2, pow_succ, pow_succ]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-! ## Period length `h`: scaled roots -/

/-- Cochrane (2023), §5.7.1, p. 165: `S(h) = √((ρ − σκh)² + 4σκ)`. -/
noncomputable def sqS (ρ σ κ h : ℝ) : ℝ := Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))

/-- Cochrane (2023), §5.7.1, p. 165: the scaled unstable root `(λ₁ − 1)/h` (`Links.scaledRoot`). -/
noncomputable def sr1 (ρ σ κ h : ℝ) : ℝ := (-ρ + σ * κ * h + sqS ρ σ κ h) / 2

/-- Cochrane (2023), §5.7.1, p. 165: the scaled stable root `(λ₂ − 1)/h`. -/
noncomputable def sr2 (ρ σ κ h : ℝ) : ℝ := (-ρ + σ * κ * h - sqS ρ σ κ h) / 2

/-- Cochrane (2023), §5.7.1, p. 165: both scaled roots solve `g² + (ρ − σκh)g − σκ = 0`. -/
theorem sr_root {ρ σ κ h : ℝ} (hσκ : 0 < σ * κ) :
    sr1 ρ σ κ h ^ 2 + (ρ - σ * κ * h) * sr1 ρ σ κ h - σ * κ = 0 ∧
      sr2 ρ σ κ h ^ 2 + (ρ - σ * κ * h) * sr2 ρ σ κ h - σ * κ = 0 := by
  have hs : sqS ρ σ κ h ^ 2 = (ρ - σ * κ * h) ^ 2 + 4 * (σ * κ) :=
    Real.sq_sqrt (by positivity)
  unfold sr1 sr2
  constructor <;> linear_combination hs / 4

/-- Cochrane (2023), §5.7.1, p. 165: `sr1 − sr2 = S(h) > 0`. -/
theorem sr_sub_pos {ρ σ κ h : ℝ} (hσκ : 0 < σ * κ) : 0 < sr1 ρ σ κ h - sr2 ρ σ κ h := by
  have : 0 < sqS ρ σ κ h := Real.sqrt_pos.2 (by positivity)
  unfold sr1 sr2
  linarith

/-- Cochrane (2023), §5.7.1, p. 165 and p. 475: at `h = 0`, `sr1 = λ^b` and `sr2 = −λ^f`. -/
theorem sr_zero (ρ σ κ : ℝ) :
    sr1 ρ σ κ 0 = ContinuousTimeNK.lamb ρ κ σ ∧ sr2 ρ σ κ 0 = -ContinuousTimeNK.lamf ρ κ σ := by
  unfold sr1 sr2 sqS ContinuousTimeNK.lamb ContinuousTimeNK.lamf
  simp only [mul_zero, add_zero, sub_zero]
  rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
  constructor <;> ring

/-- Cochrane (2023), §5.7.1, p. 165: the scaled roots are continuous in `h`. -/
theorem sr_continuous (ρ σ κ : ℝ) : Continuous (sr1 ρ σ κ) ∧ Continuous (sr2 ρ σ κ) := by
  unfold sr1 sr2 sqS
  constructor <;> fun_prop

/-- Cochrane (2023), §5.7.1, p. 165: with `β = 1 − ρh`, Galí's IS slope `σ⁻¹ = σh` and `κh`,
`λ = 1 + h g` solves Galí's characteristic equation `λ² − (1 + β + κ_G/σ_G)λ + β = 0` whenever
`g` solves `g² + (ρ − σκh)g − σκ = 0`. -/
theorem char_of_scaled {ρ σ κ h g : ℝ} (hg : g ^ 2 + (ρ - σ * κ * h) * g - σ * κ = 0) :
    (1 + h * g) ^ 2 - (1 + (1 - ρ * h) + κ * h / (σ * h)⁻¹) * (1 + h * g) + (1 - ρ * h) = 0 := by
  rw [div_inv_eq_mul]
  linear_combination h ^ 2 * hg

/-- Cochrane (2023), §20.2.2, p. 475: the discrete trap path at period length `h`, `m` periods
before the end of the trap, from the end-of-trap state `(c v_x, c)`, `v_x = −sr2/κ`. -/
noncomputable def trapDisc (σ κ ρ u c h : ℝ) (m : ℕ) : ℝ × ℝ :=
  backState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) (c * (-sr2 ρ σ κ h / κ), c) m

/-- Cochrane (2023), §20.2.2, p. 475: the weight on the unstable mode for scaled roots
`g₁, g₂`: `A = (σ(c + u) − g₂D)/(g₁ − g₂)`, `D = (−g₂c + ρu)/κ = c v_x − x̄`. -/
noncomputable def coefA (σ κ ρ u c g1 g2 : ℝ) : ℝ :=
  (σ * (c + u) - g2 * ((-g2 * c + ρ * u) / κ)) / (g1 - g2)

/-- Cochrane (2023), §20.2.2, p. 475: the weight on the stable mode,
`B = (g₁D − σ(c + u))/(g₁ − g₂)`. -/
noncomputable def coefB (σ κ ρ u c g1 g2 : ℝ) : ℝ :=
  (g1 * ((-g2 * c + ρ * u) / κ) - σ * (c + u)) / (g1 - g2)

/-- Cochrane (2023), §20.2.2, p. 475 and §5.7.1, p. 165: **the exact closed form of the discrete
trap path** at period length `h ≠ 0`, for any two distinct solutions `g₁, g₂` of
`g² + (ρ − σκh)g − σκ = 0` (the scaled roots, `λ_i = 1 + h g_i`), starting from the end-of-trap
state `(c v_x, c)`, `v_x = −g₂/κ`: `x_m = −ρu/κ + λ₁ᵐA + λ₂ᵐB`,
`π_m = −u + λ₁ᵐA g₁/σ + λ₂ᵐB g₂/σ`. -/
theorem closed_generic {σ κ ρ u c h g1 g2 : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hh : h ≠ 0)
    (hd : g1 - g2 ≠ 0) (r1 : g1 ^ 2 + (ρ - σ * κ * h) * g1 - σ * κ = 0)
    (r2 : g2 ^ 2 + (ρ - σ * κ * h) * g2 - σ * κ = 0) (m : ℕ) :
    backState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) (c * (-g2 / κ), c) m =
      (-(ρ * u) / κ + (1 + h * g1) ^ m * coefA σ κ ρ u c g1 g2 +
          (1 + h * g2) ^ m * coefB σ κ ρ u c g1 g2,
        -u + (1 + h * g1) ^ m * coefA σ κ ρ u c g1 g2 * g1 / σ +
          (1 + h * g2) ^ m * coefB σ κ ρ u c g1 g2 * g2 / σ) := by
  have hκh : κ * h ≠ 0 := mul_ne_zero hκ hh
  have hσh : (σ * h)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσ hh)
  have key := backState_modes (β := 1 - ρ * h) (η := -u) (a := coefA σ κ ρ u c g1 g2)
    (b := coefB σ κ ρ u c g1 g2) hκh hσh (char_of_scaled r1) (char_of_scaled r2) m
  have hstart : (c * (-g2 / κ), c) =
      ((1 - (1 - ρ * h)) * -u / (κ * h) + coefA σ κ ρ u c g1 g2 + coefB σ κ ρ u c g1 g2,
        -u + coefA σ κ ρ u c g1 g2 * (σ * h)⁻¹ * (1 + h * g1 - 1) +
          coefB σ κ ρ u c g1 g2 * (σ * h)⁻¹ * (1 + h * g2 - 1)) := by
    unfold coefA coefB
    refine Prod.ext ?_ ?_
    · simp only
      field_simp
      ring
    · simp only
      field_simp
      ring
  rw [hstart, key]
  unfold coefA coefB
  refine Prod.ext ?_ ?_
  · simp only
    field_simp
    ring
  · simp only
    field_simp
    ring

/-- Cochrane (2023), §20.2.2, p. 475: the closed form with the scaled roots `sr1`, `sr2`
(`h > 0`). -/
theorem trapDisc_closed {σ κ ρ u c h : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hh : 0 < h) (m : ℕ) :
    trapDisc σ κ ρ u c h m =
      (-(ρ * u) / κ + (1 + h * sr1 ρ σ κ h) ^ m * coefA σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) +
          (1 + h * sr2 ρ σ κ h) ^ m * coefB σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h),
        -u + (1 + h * sr1 ρ σ κ h) ^ m * coefA σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) *
            sr1 ρ σ κ h / σ +
          (1 + h * sr2 ρ σ κ h) ^ m * coefB σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) *
            sr2 ρ σ κ h / σ) := by
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  obtain ⟨r1, r2⟩ := sr_root (ρ := ρ) (h := h) hσκ
  exact closed_generic hσ.ne' hκ.ne' hh.ne' (sr_sub_pos hσκ).ne' r1 r2 m

/-- Cochrane (2023), §20.2.2, p. 475: the discrete trap path is the trap part of the discrete
Werning family member `LinksGaliWoodford.wState` (Galí's parameters `1 − ρh`, `κh`, `(σh)⁻¹`,
`η = −u`): at the date `k ≤ t_Z`, `m = t_Z + 1 − k` periods before the end. -/
theorem trapDisc_eq_wState {σ κ ρ u c h : ℝ} (hκ : 0 < κ) (hh : 0 < h)
    {tZ k : ℕ} (hk : k ≤ tZ) :
    wState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) tZ c k = trapDisc σ κ ρ u c h (tZ + 1 - k) := by
  have hv : vx (1 - ρ * h) (σ * h)⁻¹ (κ * h) = -sr2 ρ σ κ h / κ := by
    unfold vx l2
    rw [inv_inv, Links.lam2_scaled_eq hh]
    have : κ * h ≠ 0 := by positivity
    unfold sr2 sqS
    field_simp
    ring
  simp only [wState, hk, ↓reduceIte, trapDisc, hv]

/-! ## Convergence to the continuous-time Werning paths -/

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPi` with `g = 0`, `π_T = c`): during the
trap, `π_t = −u + A₀e^{λ^b s} + B₀e^{−λ^f s}`, `s = T − t`, with `A₀ = c + uλ^f/(λ^f + λ^b)` and
`B₀ = uλ^b/(λ^f + λ^b)`. -/
theorem wPi_modes {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t ≤ T) :
    WerningModel.wPi σ κ ρ T u 0 c t =
      -u + (c + u * ContinuousTimeNK.lamf ρ κ σ /
          (ContinuousTimeNK.lamf ρ κ σ + ContinuousTimeNK.lamb ρ κ σ)) *
          Real.exp (ContinuousTimeNK.lamb ρ κ σ * (T - t)) +
        u * ContinuousTimeNK.lamb ρ κ σ /
          (ContinuousTimeNK.lamf ρ κ σ + ContinuousTimeNK.lamb ρ κ σ) *
          Real.exp (-(ContinuousTimeNK.lamf ρ κ σ * (T - t))) := by
  have hS := ContinuousTimeNK.lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [WerningModel.wPi, ht, ↓reduceIte, WerningModel.trapPi, WerningModel.hh,
    WerningModel.kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (algebra of the limit): with `λ^fλ^b = κσ` and
`λ^f − λ^b = ρ`, the limit weight of the unstable mode in inflation is `c + uλ^f/(λ^f + λ^b)`. -/
theorem algA {σ κ ρ u c lf lb : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    coefA σ κ ρ u c lb (-lf) * lb / σ = c + u * lf / (lf + lb) := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefA
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (algebra of the limit): the limit weight of the stable mode
in inflation is `uλ^b/(λ^f + λ^b)`. -/
theorem algB {σ κ ρ u c lf lb : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    coefB σ κ ρ u c lb (-lf) * -lf / σ = u * lb / (lf + lb) := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefB
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), (20.10), p. 475 (algebra of the limit): the output gap of the two-mode
limit is the continuous-time trap output gap `(λ^f π − y)/κ`. -/
theorem algX {σ κ ρ u c lf lb E1 E2 : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    -(ρ * u) / κ + E1 * coefA σ κ ρ u c lb (-lf) + E2 * coefB σ κ ρ u c lb (-lf) =
      (lf * (c * E1 + -u * (1 - (lf * E1 + lb * E2) / (lf + lb))) -
        lb * -u * (1 - E2)) / κ := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefA coefB
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 and §5.7.1, p. 165 (**whole trap paths converge**): fix
`t < T` and cut the time `T − t` to the end of the trap into `n + 1` periods of length
`h_n = (T − t)/(n + 1)`. The discrete Werning trap path (Galí's model with `β = 1 − ρh_n`,
slopes `σh_n`, `κh_n`, natural rate `u`, end-of-trap inflation `c`), taken `n + 1` periods
before the trap ends, converges — output gap and inflation — to the continuous-time Werning path
`(wX, wPi)` with `π_T = c`, `g = 0`, at time `t`. -/
theorem trap_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)) atTop
      (𝓝 (WerningModel.wX σ κ ρ T u 0 c t, WerningModel.wPi σ κ ρ T u 0 c t)) := by
  have hτ : 0 < T - t := by linarith
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  have hlf := ContinuousTimeNK.lamf_pos (ρ := ρ) hκ hσ
  have hlb := ContinuousTimeNK.lamb_pos (ρ := ρ) hκ hσ
  have hm := ContinuousTimeNK.lamf_mul_lamb (ρ := ρ) hκ hσ
  have hs := ContinuousTimeNK.lamf_sub_lamb ρ κ σ
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh0 : Tendsto (fun n : ℕ => (T - t) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hpos : ∀ n : ℕ, 0 < (T - t) / ((n : ℝ) + 1) := fun n => by positivity
  obtain ⟨z1, z2⟩ := sr_zero ρ σ κ
  obtain ⟨c1, c2⟩ := sr_continuous ρ σ κ
  have G1 : Tendsto (fun n : ℕ => sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1))) atTop
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
    rw [← z1]; exact (c1.tendsto 0).comp hh0
  have G2 : Tendsto (fun n : ℕ => sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1))) atTop
      (𝓝 (-ContinuousTimeNK.lamf ρ κ σ)) := by
    rw [← z2]; exact (c2.tendsto 0).comp hh0
  have P1 := tendsto_one_add_pow (τ := T - t) G1
  have P2 := tendsto_one_add_pow (τ := T - t) G2
  have hne : ContinuousTimeNK.lamb ρ κ σ - -ContinuousTimeNK.lamf ρ κ σ ≠ 0 := by linarith
  have hD : Tendsto (fun n : ℕ => (-sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)) * c + ρ * u) / κ) atTop
      (𝓝 ((-(-ContinuousTimeNK.lamf ρ κ σ) * c + ρ * u) / κ)) :=
    ((G2.neg.mul tendsto_const_nhds).add tendsto_const_nhds).div_const κ
  have hA : Tendsto (fun n : ℕ => coefA σ κ ρ u c (sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1)))
      (sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)))) atTop
      (𝓝 (coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ))) := by
    unfold coefA
    exact (tendsto_const_nhds.sub (G2.mul hD)).div (G1.sub G2) hne
  have hB : Tendsto (fun n : ℕ => coefB σ κ ρ u c (sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1)))
      (sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)))) atTop
      (𝓝 (coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ))) := by
    unfold coefB
    exact ((G1.mul hD).sub tendsto_const_nhds).div (G1.sub G2) hne
  have hX := (tendsto_const_nhds (x := -(ρ * u) / κ)).add (P1.mul hA) |>.add (P2.mul hB)
  have hP := ((tendsto_const_nhds (x := -u)).add (((P1.mul hA).mul G1).div_const σ)).add
    (((P2.mul hB).mul G2).div_const σ)
  have hvx : WerningModel.wX σ κ ρ T u 0 c t =
      -(ρ * u) / κ + Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ) *
          coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) +
        Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) *
          coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) := by
    rw [algX hσ hlf hlb hm hs]
    simp only [WerningModel.wX, ht.le, ↓reduceIte, WerningModel.trapPi, WerningModel.trapY,
      WerningModel.hh, WerningModel.kk, mul_zero, zero_mul, add_zero, sub_zero]
    rw [show (T - t) * ContinuousTimeNK.lamb ρ κ σ = ContinuousTimeNK.lamb ρ κ σ * (T - t) by
      ring, show (T - t) * -ContinuousTimeNK.lamf ρ κ σ = -(ContinuousTimeNK.lamf ρ κ σ *
        (T - t)) by ring]
  have hvp : WerningModel.wPi σ κ ρ T u 0 c t =
      -u + Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ) *
          coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) *
          ContinuousTimeNK.lamb ρ κ σ / σ +
        Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) *
          coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) *
          -ContinuousTimeNK.lamf ρ κ σ / σ := by
    have a := algA (u := u) (c := c) hσ hlf hlb hm hs
    have b := algB (u := u) (c := c) hσ hlf hlb hm hs
    rw [wPi_modes hσ hκ ht.le, show ContinuousTimeNK.lamb ρ κ σ * (T - t) =
      (T - t) * ContinuousTimeNK.lamb ρ κ σ by ring, show -(ContinuousTimeNK.lamf ρ κ σ * (T - t)) =
      (T - t) * -ContinuousTimeNK.lamf ρ κ σ by ring]
    linear_combination (-Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ)) * a -
      Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) * b
  rw [hvx, hvp]
  refine (hX.prodMk_nhds hP).congr fun n => ?_
  rw [trapDisc_closed hσ hκ (hpos n) (n + 1)]

/-- Cochrane (2023), §20.2.2, p. 475: the convergence of `trap_tendsto` for inflation. -/
theorem trap_pi_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => (trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)).2) atTop
      (𝓝 (WerningModel.wPi σ κ ρ T u 0 c t)) :=
  (continuous_snd.tendsto _).comp (trap_tendsto hσ hκ ht)

/-- Cochrane (2023), §20.2.2, p. 475: the convergence of `trap_tendsto` for the output gap. -/
theorem trap_x_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => (trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)).1) atTop
      (𝓝 (WerningModel.wX σ κ ρ T u 0 c t)) :=
  (continuous_fst.tendsto _).comp (trap_tendsto hσ hκ ht)

/-- Cochrane (2023), §20.2.2, p. 475: the same convergence stated for the discrete Werning family
member itself: for any trap `[0, t_Z]` and date `k ≤ t_Z` with `t_Z + 1 − k = n + 1` periods to
the end of the trap, `wState` at `k` (period length `(T − t)/(n + 1)`) converges to
`(wX, wPi)` at `t`. -/
theorem wState_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T)
    {tZ k : ℕ → ℕ} (hk : ∀ n, k n ≤ tZ n) (hlen : ∀ n, tZ n + 1 - k n = n + 1) :
    Tendsto (fun n : ℕ => wState (1 - ρ * ((T - t) / ((n : ℝ) + 1)))
        (κ * ((T - t) / ((n : ℝ) + 1))) (σ * ((T - t) / ((n : ℝ) + 1)))⁻¹ (-u) (tZ n) c (k n))
      atTop (𝓝 (WerningModel.wX σ κ ρ T u 0 c t, WerningModel.wPi σ κ ρ T u 0 c t)) := by
  refine (trap_tendsto hσ hκ ht).congr fun n => ?_
  have hp : 0 < (T - t) / ((n : ℝ) + 1) := div_pos (by linarith) (by positivity)
  rw [trapDisc_eq_wState hκ hp (hk n), hlen n]

end Cochrane.ZeroBound.LinksGaliWoodfordLimit

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lift-off timing: at the commitment optimum the zero bound binds throughout the shock

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4 "Forward guidance"
(pp. 478–480), compared with Galí (2015), §5.4.2 (pp. 148–152), in the model of
`LinksGaliWoodford` (loss `∑ βᵗ(π_t² + ϑ x_t²)`, `π_t = βπ_{t+1} + κx_t`,
`x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1} − rⁿ_t)`, `i_t ≥ 0`, `rⁿ_t = −η` on `[0, t_Z]`, `ρ` after).

Galí's algorithm guesses a lift-off date `t_C ≥ t_Z`; `LinksGaliWoodford` carried `t_Z ≤ t_C`
(and the zero rate on the whole shock, (48)) as hypotheses. Here both are **proved** for the
commitment optimum, for all `β ∈ (0,1)`, `κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`.

## Necessity of the KKT conditions (`kkt_necessary`)
* `mult`, `mxi1`, `mxi2`: the multipliers solving (35)–(36) forward (`foc35_mult`,
  `foc36_mult`, unique: `mult_unique`).
* `foc_dir`: an optimum has a nonnegative derivative in every feasible direction.
* `hdir s`: raise the rate at `s` alone (finite support); `cross_hdir`: its derivative is
  `β^s ξ₂,s / σ` (Lagrangian identity), so `ξ₂ ≥ 0` with complementary slackness.
* `wdir`: the bounded peg mode (zero rate gaps), with zero derivative (`cross_wdir`);
  `ddir = hdir − c₁λ₁ˢ wdir` is localised (`backState_closed`, `ddir_le`, `ddir_gt`,
  `ddir_bound`); by Tannery's theorem `β^t ξ₂,t → 0` (`tendsto_mxi2`, transversality).

## The sign argument (`trap_mult_pos`)
Write `gap_t = i_t − rⁿ_t` and `lam_t = π_{t+1} + (ϑ/κ)(x_{t+1} − x_t)`; then
`gap = r·lam − (r−1)π_{+1}` with `r = σκ/ϑ` (`gap_lam`) and `κ·lam_t = cξ₂,t − ξ₂,t+1 −
ξ₂,t−1/β` (`lam_mult`). Under the Phillips curve both are second-difference operators of `π`
(`gap_comb`, `lam_comb`), which gives discrete maximum principles.
* `pi_le_bound`/`optimal_pi_le`: commitment inflation never exceeds `η`.
* `σκ ≤ ϑ` (`slack_contra_le`): a slack shock date `s` would give
  `gap_s ≤ (1 − r)π_{s+1} ≤ (1 − r)η < η`, i.e. `i_s < 0`.
* `ϑ < σκ` (`slack_contra_gt`): a slack date forces `π_{s+1} ≤ −η/(r−1)`; a minimum principle on
  the shock carries this to its end with inflation falling there; inflation then stays negative
  (`post_nonpos`), the multipliers vanish from `s` on (`mult_zero_left`, `mult_zero_right`),
  and the remaining peg dynamics explode (`comb_blowup`), contradicting the finite loss.

## Results
* `optimal_trap_binds`, `optimal_h48`: at the optimum `i_t = 0` and `ξ₂,t > 0` on `[0, t_Z]`.
* `liftoff_ge`, `liftoff_ge_mult`, `liftoff_after_shock`: the lift-off date satisfies
  `t_C ≥ t_Z`.
* Hypothesis-free versions (no `t_Z ≤ t_C`, no (48)): `comm_gt_disc_opt`, `comm_loss_lt_opt`,
  `comm_promise_opt`, `comm_gt_disc_of_state_opt`, and the verification theorem for an arbitrary
  guess `algorithm_verification_gen` (it proves `t_Z ≤ t_C`), `comm_loss_lt_alg_gen`.
-/

namespace Cochrane.ZeroBound.LiftoffTiming

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford

/-! ## Second differences and geometric blow-up -/

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (29)–(30), p. 145, with `x` eliminated by
the Phillips curve): `u_{t+1} + a((u_{t+1} − u_t) + β(u_{t+1} − u_{t+2}))`. With `a = σ/κ` it is
the rate gap `i_t − rⁿ_t` (`gap_comb`), with `a = ϑ/κ²` the multiplier combination
`lam` (`lam_comb`). -/
noncomputable def comb (β a : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  u (t + 1) + a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)))

/-- Cochrane (2023), p. 479: at a weak local minimum `comb` is at most the value there. -/
theorem comb_le_of_min {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) {u : ℕ → ℝ} {t : ℕ}
    (h1 : u (t + 1) ≤ u t) (h2 : u (t + 1) ≤ u (t + 2)) : comb β a u t ≤ u (t + 1) := by
  unfold comb
  have h3 : β * (u (t + 1) - u (t + 2)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  have h4 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha (by linarith)
  linarith

/-- Cochrane (2023), p. 479: if `comb ≤ B < u_{t+1}` and `u_t ≤ u_{t+1}`, the sequence keeps
rising: `u_{t+1} < u_{t+2}`. -/
theorem comb_up {β a B : ℝ} (hβ : 0 < β) (ha : 0 < a) {u : ℕ → ℝ} {t : ℕ}
    (h : comb β a u t ≤ B) (hB : B < u (t + 1)) (hu : u t ≤ u (t + 1)) :
    u (t + 1) < u (t + 2) := by
  unfold comb at h
  have h1 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) < 0 := by linarith
  have h2 : (u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)) < 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_nonneg ha.le hc]
  have h4 : u (t + 1) - u (t + 2) < 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_nonneg hβ.le hc]
  linarith

/-- Cochrane (2023), p. 479: if `comb ≤ B ≤ u_{t+1}`, the increment grows by at least the
factor `β⁻¹`: `(u_{t+1} − u_t)/β ≤ u_{t+2} − u_{t+1}`. -/
theorem comb_step {β a B : ℝ} (hβ : 0 < β) (ha : 0 < a) {u : ℕ → ℝ} {t : ℕ}
    (h : comb β a u t ≤ B) (hB : B ≤ u (t + 1)) :
    (u (t + 1) - u t) / β ≤ u (t + 2) - u (t + 1) := by
  unfold comb at h
  have h1 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) ≤ 0 := by linarith
  have h2 : (u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)) ≤ 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_pos ha hc]
  rw [div_le_iff₀ hβ]
  linarith

/-- Cochrane (2023), p. 479: `comb` is odd in the sequence. -/
theorem comb_neg (β a : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => -u n) t = -comb β a u t := by
  unfold comb; ring

/-- Cochrane (2023), §20.2.4, p. 479 (the explosive direction of the zero-rate dynamics,
`ForwardGuidance`): if, from `n₀` on, every rise above `B` makes the next increment at least
`β⁻¹` times the previous one, then a rise at `n₀` grows geometrically:
`u_{n₀+1} − u_{n₀} ≤ β^k (u_{n₀+k+1} − u_{n₀+k})` and `B < u_{n₀+k+1}`. -/
theorem grow {β : ℝ} (hβ0 : 0 < β) {u : ℕ → ℝ} {n0 : ℕ} {B : ℝ}
    (hstep : ∀ n, n0 ≤ n → B < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : B < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) (k : ℕ) :
    u (n0 + 1) - u n0 ≤ β ^ k * (u (n0 + k + 1) - u (n0 + k)) ∧ B < u (n0 + k + 1) := by
  induction k with
  | zero => simp only [pow_zero, one_mul, add_zero, le_refl, h0, and_self]
  | succ k ih =>
    obtain ⟨ha, hb⟩ := ih
    have hpk : 0 < β ^ k := pow_pos hβ0 k
    have hd : 0 < u (n0 + k + 1) - u (n0 + k) := by
      by_contra hc
      push Not at hc
      have : β ^ k * (u (n0 + k + 1) - u (n0 + k)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpk.le hc
      linarith
    have hs := hstep (n0 + k) (by omega) hb (by linarith)
    rw [show n0 + k + 2 = n0 + (k + 1) + 1 by omega,
      show n0 + k + 1 = n0 + (k + 1) by omega] at hs
    rw [show n0 + (k + 1) = n0 + k + 1 by omega] at hs ⊢
    rw [div_le_iff₀ hβ0] at hs
    have hdpos : 0 < (u (n0 + k + 1) - u (n0 + k)) / β := div_pos hd hβ0
    constructor
    · have e : β ^ (k + 1) * (u (n0 + k + 1 + 1) - u (n0 + k + 1)) =
          β ^ k * ((u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β) := by ring
      rw [e]
      have : β ^ k * (u (n0 + k + 1) - u (n0 + k)) ≤
          β ^ k * ((u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β) :=
        mul_le_mul_of_nonneg_left hs hpk.le
      linarith
    · have : u (n0 + k + 1) - u (n0 + k) ≤ (u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β := hs
      have hβd : 0 < (u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β := by linarith
      have : 0 < u (n0 + k + 1 + 1) - u (n0 + k + 1) :=
        (pos_iff_pos_of_mul_pos hβd).mpr hβ0
      linarith

/-- Cochrane (2023), p. 479: such geometric growth is incompatible with a finite discounted loss,
`β^t u_t² ↛ 0` (with `0 ≤ B`, `0 < β ≤ 1`). -/
theorem not_tendsto_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {u : ℕ → ℝ} {n0 : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hstep : ∀ n, n0 ≤ n → B < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : B < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  intro hT
  set d := u (n0 + 1) - u n0 with hd
  have hdpos : 0 < d := by linarith
  have hc : 0 < β ^ (n0 + 1) * d ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 _ hc)
  have key : β ^ (n0 + 1) * d ^ 2 ≤ β ^ (n0 + (N + 1) + 1) * u (n0 + (N + 1) + 1) ^ 2 := by
    obtain ⟨g1, g2⟩ := grow hβ0 hstep h0 h1 (N + 1)
    obtain ⟨-, g3⟩ := grow hβ0 hstep h0 h1 N
    rw [show n0 + (N + 1) = n0 + N + 1 by omega] at g1 g2 ⊢
    set v := u (n0 + N + 1 + 1)
    have hv0 : 0 ≤ u (n0 + N + 1) := by linarith
    have hpk : 0 < β ^ (N + 1) := pow_pos hβ0 _
    have hvd : d ≤ β ^ (N + 1) * v := by
      have : β ^ (N + 1) * (v - u (n0 + N + 1)) ≤ β ^ (N + 1) * v :=
        mul_le_mul_of_nonneg_left (by linarith) hpk.le
      linarith
    have hsq : d ^ 2 ≤ (β ^ (N + 1) * v) ^ 2 := pow_le_pow_left₀ hdpos.le hvd 2
    have hle : β ^ (N + 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have e : β ^ (n0 + N + 1 + 1) = β ^ (n0 + 1) * β ^ (N + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    have hp1 : 0 ≤ β ^ (n0 + 1) := pow_nonneg hβ0.le _
    have : (β ^ (N + 1) * v) ^ 2 ≤ β ^ (N + 1) * v ^ 2 := by
      rw [mul_pow, sq (β ^ (N + 1))]
      have := mul_le_mul_of_nonneg_right hle (mul_nonneg hpk.le (sq_nonneg v))
      nlinarith
    calc β ^ (n0 + 1) * d ^ 2 ≤ β ^ (n0 + 1) * (β ^ (N + 1) * v ^ 2) :=
          mul_le_mul_of_nonneg_left (hsq.trans this) hp1
      _ = β ^ (n0 + 1) * β ^ (N + 1) * v ^ 2 := by ring
  have := hN (n0 + (N + 1) + 1) (by omega)
  linarith

/-- Cochrane (2023), p. 479: the same growth with `u ≥ 0` is incompatible with `β^t u_t → 0`
(used for the multipliers). -/
theorem not_tendsto_lin {β : ℝ} (hβ0 : 0 < β) {u : ℕ → ℝ} {n0 : ℕ} (hnn : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, n0 ≤ n → 0 < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : 0 < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t) atTop (𝓝 0) := by
  intro hT
  set d := u (n0 + 1) - u n0 with hd
  have hdpos : 0 < d := by linarith
  have hc : 0 < β ^ (n0 + 1) * d := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 _ hc)
  have key : β ^ (n0 + 1) * d ≤ β ^ (n0 + N + 1) * u (n0 + N + 1) := by
    obtain ⟨g1, -⟩ := grow hβ0 hstep h0 h1 N
    have e : β ^ (n0 + N + 1) = β ^ (n0 + 1) * β ^ N := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    have hpN : 0 ≤ β ^ N := pow_nonneg hβ0.le _
    have : β ^ N * (u (n0 + N + 1) - u (n0 + N)) ≤ β ^ N * u (n0 + N + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hnn (n0 + N)]) hpN
    have hp1 : 0 ≤ β ^ (n0 + 1) := pow_nonneg hβ0.le _
    calc β ^ (n0 + 1) * d ≤ β ^ (n0 + 1) * (β ^ N * u (n0 + N + 1)) :=
          mul_le_mul_of_nonneg_left (g1.trans this) hp1
      _ = β ^ (n0 + 1) * β ^ N * u (n0 + N + 1) := by ring
  have := hN (n0 + N + 1) (by omega)
  linarith

/-- Cochrane (2023), §20.2.4, p. 479: if from `N₀` on one of two `comb` combinations (positive
weights) is at most `B ≥ 0`, a rise above `B` at some `m₀ ≥ N₀` makes `β^t u_t² ↛ 0`. -/
theorem comb_blowup {β a1 a2 B : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hB : 0 ≤ B) {u : ℕ → ℝ} {N0 m0 : ℕ}
    (hd : ∀ n, N0 ≤ n → comb β a1 u n ≤ B ∨ comb β a2 u n ≤ B) (hm : N0 ≤ m0)
    (h0 : B < u (m0 + 1)) (h1 : u m0 < u (m0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  refine not_tendsto_sq hβ0 hβ1 hB (fun n hn hb _ => ?_) h0 h1
  rcases hd n (by omega) with h | h
  · exact comb_step hβ0 ha1 h hb.le
  · exact comb_step hβ0 ha2 h hb.le

/-! ## The rate gap and the multiplier combination -/

/-- Cochrane (2023), §20.1, p. 465, and Galí (2015), eq. (30), p. 145: the rate gap
`i_t − rⁿ_t = π_{t+1} + σ(x_{t+1} − x_t)` (`impliedRate_eq_gap`). -/
noncomputable def gap (σ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the combination
`π_{t+1} + (ϑ/κ)(x_{t+1} − x_t)`, which the first-order conditions express through the zero-bound
multipliers alone (`lam_mult`). -/
noncomputable def lam (κ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  π (t + 1) + ϑ / κ * (x (t + 1) - x t)

/-- Galí (2015), eqs. (35)–(36) at `t = 0`, p. 149; Cochrane (2023), p. 479: `π₀ + (ϑ/κ) x₀`
(`= −ξ₂,₀/κ`, `lamI_mult`). -/
noncomputable def lamI (κ ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := π 0 + ϑ / κ * x 0

/-- Galí (2015), eq. (30), p. 145; Cochrane (2023), p. 465: the implied rate is the natural rate
plus the rate gap. -/
theorem impliedRate_eq_gap (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = rn t + gap σ x π t := by
  unfold impliedRate gap; ring

/-- Galí (2015), eq. (29), p. 145; Cochrane (2023), eq. (5.2), p. 118: the Phillips curve solved
for the output gap, `x_t = (π_t − βπ_{t+1})/κ`. -/
theorem x_of_nkpc {β κ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h : NKPC β κ x π t) :
    x t = (π t - β * π (t + 1)) / κ := by
  unfold NKPC at h; field_simp; linarith

/-- Galí (2015), eqs. (29)–(30), p. 145; Cochrane (2023), p. 479: under the Phillips curve the
rate gap is `comb β (σ/κ) π t`. -/
theorem gap_comb {β κ σ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h0 : NKPC β κ x π t)
    (h1 : NKPC β κ x π (t + 1)) : gap σ x π t = comb β (σ / κ) π t := by
  have e0 := x_of_nkpc hκ h0
  have e1 := x_of_nkpc hκ h1
  rw [show t + 1 + 1 = t + 2 by omega] at e1
  unfold gap comb
  rw [e0, e1]
  field_simp
  ring

/-- Galí (2015), eqs. (29), (35)–(36), p. 149; Cochrane (2023), p. 479: under the Phillips curve
`lam` is `comb β (ϑ/κ²) π t`. -/
theorem lam_comb {β κ ϑ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h0 : NKPC β κ x π t)
    (h1 : NKPC β κ x π (t + 1)) : lam κ ϑ x π t = comb β (ϑ / κ ^ 2) π t := by
  have e0 := x_of_nkpc hκ h0
  have e1 := x_of_nkpc hκ h1
  rw [show t + 1 + 1 = t + 2 by omega] at e1
  unfold lam comb
  rw [e0, e1]
  field_simp
  ring

/-- Galí (2015), eq. (29), p. 145; Cochrane (2023), p. 479: `lamI = π₀ + (ϑ/κ²)(π₀ − βπ₁)`. -/
theorem lamI_eq {β κ ϑ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} (h0 : NKPC β κ x π 0) :
    lamI κ ϑ x π = π 0 + ϑ / κ ^ 2 * (π 0 - β * π 1) := by
  unfold lamI
  rw [x_of_nkpc hκ h0]
  field_simp

/-- Cochrane (2023), §20.2.4, p. 479: with `r = σκ/ϑ`, the rate gap is
`r · lam − (r − 1) π_{t+1}`. -/
theorem gap_lam {κ σ ϑ : ℝ} (hκ : κ ≠ 0) (hϑ : ϑ ≠ 0) (x π : ℕ → ℝ) (t : ℕ) :
    gap σ x π t = σ * κ / ϑ * lam κ ϑ x π t - (σ * κ / ϑ - 1) * π (t + 1) := by
  unfold gap lam
  field_simp
  ring

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the first-order
conditions give `κ · lam_t = c ξ₂,t − ξ₂,t+1 − ξ₂,t−1/β` with `c = 1 + 1/β + κ/(βσ)`: the
multiplier combination is a three-term (`Z`-matrix) operator of the multipliers. -/
theorem lam_mult {β κ σ ϑ : ℝ} (hκ : κ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ} {t : ℕ}
    (h35 : FOC35 β σ π ξ1 ξ2 (t + 1)) (h36a : FOC36 β κ ϑ x ξ1 ξ2 t)
    (h36b : FOC36 β κ ϑ x ξ1 ξ2 (t + 1)) :
    κ * lam κ ϑ x π t = (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β := by
  have e : κ * lam κ ϑ x π t = κ * π (t + 1) + ϑ * (x (t + 1) - x t) := by
    unfold lam; field_simp
  rw [e]
  unfold FOC35 at h35
  unfold FOC36 at h36a h36b
  simp only [lag_succ] at h35 h36b
  linear_combination κ * h35 + h36b - h36a

/-- Galí (2015), eqs. (35)–(36) at `t = 0`, p. 149; Cochrane (2023), p. 479:
`κ (π₀ + (ϑ/κ) x₀) = −ξ₂,₀`. -/
theorem lamI_mult {β κ σ ϑ : ℝ} (hκ : κ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ}
    (h35 : FOC35 β σ π ξ1 ξ2 0) (h36 : FOC36 β κ ϑ x ξ1 ξ2 0) :
    κ * lamI κ ϑ x π = -ξ2 0 := by
  have e : κ * lamI κ ϑ x π = κ * π 0 + ϑ * x 0 := by
    unfold lamI; field_simp
  rw [e]
  unfold FOC35 at h35
  unfold FOC36 at h36
  simp only [lag_zero, zero_div, sub_zero] at h35 h36
  linear_combination κ * h35 + h36

/-- Galí (2015), p. 149; Cochrane (2023), §20.1, p. 465: on a feasible path the implied rate is
nonnegative at every date. -/
theorem rate_nonneg {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ} (hF : Feasible β κ σ rn x π)
    (t : ℕ) : 0 ≤ impliedRate σ rn x π t := by
  rw [impliedRate_eq hσ.ne']
  exact mul_nonneg hσ.le (by linarith [(hF t).2])

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: a finite loss forces `β^t π_t² → 0`. -/
theorem tendsto_pi_sq {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0) := by
  refine (Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) hs).tendsto_atTop_zero
  unfold lossTerm
  have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
  nlinarith

/-! ## Maximum principles for the Karush–Kuhn–Tucker system -/

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (35)–(36)): a nonnegative multiplier sequence
vanishing at `s` whose three-term operator is `≤ 0` on `[0, s)` (with `ξ₂,₋₁ = 0`) vanishes on
`[0, s]` (finite maximum principle). -/
theorem mult_zero_left {β cc : ℝ} (hβ : 0 < β) (hcc : 1 + 1 / β < cc) {ξ2 : ℕ → ℝ}
    (hpos : ∀ t, 0 ≤ ξ2 t) {s : ℕ} (hs : ξ2 s = 0)
    (h : ∀ t, t < s → cc * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β ≤ 0) :
    ∀ t, t ≤ s → ξ2 t = 0 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · intro t ht
    obtain rfl : t = 0 := by omega
    exact hs
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range s) ξ2 ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hm
  have hM0 : 0 ≤ ξ2 m := hpos m
  have hnext : ξ2 (m + 1) ≤ ξ2 m := by
    rcases Nat.lt_or_ge (m + 1) s with h' | h'
    · exact hmax _ (Finset.mem_range.mpr h')
    · obtain rfl : s = m + 1 := by omega
      rw [hs]; exact hM0
  have hprev : lag ξ2 m ≤ ξ2 m := by
    rcases m with _ | j
    · simpa using hM0
    · simpa using hmax j (Finset.mem_range.mpr (by omega))
  have hM : ξ2 m ≤ 0 := by
    have h1 := h m hm
    have h2 : lag ξ2 m / β ≤ ξ2 m / β := div_le_div_of_nonneg_right hprev hβ.le
    have h3 : (cc - 1 - 1 / β) * ξ2 m ≤ 0 := by
      have : ξ2 m / β = 1 / β * ξ2 m := by ring
      nlinarith
    by_contra hc
    push Not at hc
    have : 0 < (cc - 1 - 1 / β) * ξ2 m := mul_pos (by linarith) hc
    linarith
  intro t ht
  rcases ht.eq_or_lt with rfl | ht'
  · exact hs
  · exact le_antisymm ((hmax t (Finset.mem_range.mpr ht')).trans hM) (hpos t)

/-- Cochrane (2023), §20.2.4, p. 479 (transversality, Galí (2015), p. 149): a nonnegative
multiplier sequence vanishing at `s`, with three-term operator `≤ 0` after `s` and
`β^t ξ₂,t → 0`, vanishes on `[s, ∞)` (otherwise it grows at least like `β⁻ᵗ`). -/
theorem mult_zero_right {β cc : ℝ} (hβ : 0 < β) (hcc : 1 + 1 / β < cc) {ξ2 : ℕ → ℝ}
    (hpos : ∀ t, 0 ≤ ξ2 t) {s : ℕ} (hs : ξ2 s = 0)
    (h : ∀ t, s < t → cc * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β ≤ 0)
    (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0)) :
    ∀ t, s ≤ t → ξ2 t = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ t, s ≤ t ∧ ξ2 t ≠ 0 := hcon
  set t1 := Nat.find hex with ht1
  obtain ⟨ht1s, ht1z⟩ := Nat.find_spec hex
  have ht1ne : t1 ≠ s := by
    intro h'
    rw [← ht1, h'] at ht1z
    exact ht1z hs
  obtain ⟨n0, hn0⟩ : ∃ n0, t1 = n0 + 1 := ⟨t1 - 1, by omega⟩
  have hn0s : s ≤ n0 := by omega
  have hz0 : ξ2 n0 = 0 := by
    by_contra hz
    have := Nat.find_min hex (show n0 < Nat.find hex by omega)
    exact this ⟨hn0s, hz⟩
  have hpos1 : 0 < ξ2 (n0 + 1) := by
    rw [← hn0]
    exact lt_of_le_of_ne (hpos _) (Ne.symm ht1z)
  refine not_tendsto_lin hβ hpos (n0 := n0) (fun n hn _ _ => ?_) hpos1 (by linarith) hlim
  have h1 := h (n + 1) (by omega)
  simp only [lag_succ] at h1
  have h2 : 0 ≤ (cc - 1 - 1 / β) * ξ2 (n + 1) := mul_nonneg (by linarith) (hpos _)
  rw [show n + 1 + 1 = n + 2 by omega] at h1
  have e : (ξ2 (n + 1) - ξ2 n) / β = 1 / β * ξ2 (n + 1) - ξ2 n / β := by ring
  rw [e]
  nlinarith

/-- Cochrane (2023), §20.2.4, p. 479: **inflation never exceeds `B ≥ 0`** on a path where at
every date either the rate gap is at most `B` or the multiplier combination is `≤ 0`, with
`lamI ≤ 0` and `β^t π_t² → 0` (a discrete maximum principle; with `B = η` this is "commitment
inflation never exceeds the depth of the shock"). -/
theorem pi_le_bound {β κ σ ϑ B : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hB : 0 ≤ B) {x π : ℕ → ℝ} (hN : ∀ t, NKPC β κ x π t)
    (hd : ∀ t, gap σ x π t ≤ B ∨ lam κ ϑ x π t ≤ 0) (hI : lamI κ ϑ x π ≤ 0)
    (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0)) (n : ℕ) : π n ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) π ⟨n, by simp⟩
  rw [Finset.mem_range] at hm0
  have hpm : B < π m0 := lt_of_lt_of_le hcon (hmax n (by simp))
  have hθ : 0 < ϑ / κ ^ 2 := by positivity
  have hsk : 0 < σ / κ := by positivity
  have hdc : ∀ t, comb β (σ / κ) π t ≤ B ∨ comb β (ϑ / κ ^ 2) π t ≤ B := by
    intro t
    rcases hd t with h | h
    · left; rwa [← gap_comb hκ.ne' (hN t) (hN (t + 1))]
    · right; rw [← lam_comb hκ.ne' (hN t) (hN (t + 1))]; linarith
  have hup : π m0 < π (m0 + 1) := by
    rcases m0 with _ | j
    · rw [lamI_eq hκ.ne' (hN 0)] at hI
      by_contra hc
      push Not at hc
      have h0 : 0 < π 0 := by linarith
      have : (1 - β) * π 0 ≤ π 0 - β * π 1 := by nlinarith
      have : 0 ≤ ϑ / κ ^ 2 * (π 0 - β * π 1) :=
        mul_nonneg hθ.le (by nlinarith [mul_pos (show 0 < 1 - β by linarith) h0])
      linarith
    · have hj : π j ≤ π (j + 1) := hmax j (Finset.mem_range.mpr (by omega))
      rcases hdc j with h | h
      · exact comb_up hβ hsk h hpm hj
      · exact comb_up hβ hθ h hpm hj
  exact comb_blowup hβ hβ1.le hsk hθ hB (fun t _ => hdc t) (Nat.zero_le m0) (hpm.trans hup)
    hup hS

/-- Cochrane (2023), §20.2.4, p. 479: after date `K`, if at every date either the rate gap is
`≤ 0` or the multiplier combination is `≤ 0`, then negative inflation at `K + 1` stays
nonpositive forever (`β^t π_t² → 0`). -/
theorem post_nonpos {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {x π : ℕ → ℝ} (hN : ∀ t, NKPC β κ x π t) {K : ℕ}
    (hd : ∀ t, K ≤ t → gap σ x π t ≤ 0 ∨ lam κ ϑ x π t ≤ 0) (hK : π (K + 1) < 0)
    (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0)) (n : ℕ) (hn : K + 1 ≤ n) :
    π n ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.Icc (K + 1) n) π
    ⟨n, Finset.mem_Icc.mpr ⟨hn, le_rfl⟩⟩
  rw [Finset.mem_Icc] at hm0
  have hpm : 0 < π m0 := lt_of_lt_of_le hcon (hmax n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
  have hθ : 0 < ϑ / κ ^ 2 := by positivity
  have hsk : 0 < σ / κ := by positivity
  have hdc : ∀ t, K ≤ t → comb β (σ / κ) π t ≤ 0 ∨ comb β (ϑ / κ ^ 2) π t ≤ 0 := by
    intro t ht
    rcases hd t ht with h | h
    · left; rwa [← gap_comb hκ.ne' (hN t) (hN (t + 1))]
    · right; rwa [← lam_comb hκ.ne' (hN t) (hN (t + 1))]
  have hne : m0 ≠ K + 1 := by rintro rfl; linarith
  obtain ⟨j, rfl⟩ : ∃ j, m0 = j + 1 := ⟨m0 - 1, by omega⟩
  have hj : π j ≤ π (j + 1) := hmax j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hup : π (j + 1) < π (j + 2) := by
    rcases hdc j (by omega) with h | h
    · exact comb_up hβ hsk h hpm hj
    · exact comb_up hβ hθ h hpm hj
  exact comb_blowup hβ hβ1.le hsk hθ le_rfl hdc (show K ≤ j + 1 by omega) (hpm.trans hup)
    hup hS

/-! ## A slack date inside the shock is impossible -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **case `σκ ≤ ϑ`.** On a path
satisfying the first-order conditions (`hmult`, `hmI`) with nonnegative multipliers, binding
dates as stated and `β^t π_t² → 0`, the multiplier `ξ₂,s` of a date `s ≤ t_Z` of the shock cannot
vanish: otherwise the rate gap at `s` is at most `(1 − σκ/ϑ) π_{s+1} ≤ (1 − σκ/ϑ) η < η`
(`pi_le_bound`), so `i_s < 0`. -/
theorem slack_contra_le {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ ≤ ϑ) {tZ s : ℕ} (hsZ : s ≤ tZ) {x π ξ2 : ℕ → ℝ}
    (hN : ∀ t, NKPC β κ x π t) (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0))
    (hpos : ∀ t, 0 ≤ ξ2 t)
    (hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β)
    (hmI : κ * lamI κ ϑ x π = -ξ2 0)
    (htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t)
    (hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η)
    (hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0) (hs0 : ξ2 s = 0) : False := by
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have h := hmult t
    rw [ht] at h
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [h]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc]
  have hd : ∀ t, gap σ x π t ≤ η ∨ lam κ ϑ x π t ≤ 0 := by
    intro t
    rcases (hpos t).eq_or_lt with h | h
    · exact Or.inr (hslack t h.symm)
    · rcases le_or_gt t tZ with ht | ht
      · exact Or.inl (hbind t ht h).le
      · exact Or.inl ((hpost t ht h).trans hη.le)
  have hI : lamI κ ϑ x π ≤ 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc, hpos 0]
  have hpi := pi_le_bound hβ hβ1 hκ hσ hϑ hη.le hN hd hI hS (s + 1)
  have hg := htrap s hsZ
  rw [gap_lam hκ.ne' hϑ.ne'] at hg
  have hl := hslack s hs0
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hϑ]; exact hr
  have h1 : r * lam κ ϑ x π s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le hl
  have h2 : (1 - r) * π (s + 1) ≤ (1 - r) * η := mul_le_mul_of_nonneg_left hpi (by linarith)
  have h3 : 0 < r * η := mul_pos hr0 hη
  linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **case `ϑ < σκ`.** Under the
hypotheses of `slack_contra_le` and `β^t ξ₂,t → 0`, a vanishing multiplier `ξ₂,s = 0` at a date
`s ≤ t_Z` is impossible. A slack date forces `π_{s+1} ≤ c = −η/(σκ/ϑ − 1)`; a discrete minimum
principle on the shock (the rate gap is `≥ η` there) propagates `π ≤ c` to the end of the shock
and makes inflation fall at its end; then inflation stays negative after the shock
(`post_nonpos`), the multipliers vanish from `s` on (`mult_zero_left`, `mult_zero_right`), and
the resulting peg dynamics explode, contradicting the finite loss. -/
theorem slack_contra_gt {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) (hr : ϑ < σ * κ) {tZ s : ℕ} (hsZ : s ≤ tZ) {x π ξ2 : ℕ → ℝ}
    (hN : ∀ t, NKPC β κ x π t) (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0))
    (hpos : ∀ t, 0 ≤ ξ2 t) (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0))
    (hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β)
    (hmI : κ * lamI κ ϑ x π = -ξ2 0)
    (htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t)
    (hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η)
    (hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0) (hs0 : ξ2 s = 0) : False := by
  set r := σ * κ / ϑ with hrdef
  have hr1 : 1 < r := by rw [hrdef, lt_div_iff₀ hϑ]; linarith
  have hr0 : 0 < r := by linarith
  set c := -η / (r - 1) with hcdef
  have hc : c < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hrc : (r - 1) * c = -η := by
    have hne : r - 1 ≠ 0 := by linarith
    rw [hcdef]; field_simp
  set θ := ϑ / κ ^ 2 with hθdef
  have hθ0 : 0 < θ := by positivity
  set cc := 1 + 1 / β + κ / (β * σ) with hccdef
  have hcc : 1 + 1 / β < cc := by
    have : 0 < κ / (β * σ) := by positivity
    linarith
  have hgl : ∀ t, gap σ x π t = r * lam κ ϑ x π t - (r - 1) * π (t + 1) :=
    fun t => gap_lam hκ.ne' hϑ.ne' x π t
  have hlamc : ∀ t, lam κ ϑ x π t = comb β θ π t := fun t => lam_comb hκ.ne' (hN t) (hN (t + 1))
  have hgapc : ∀ t, gap σ x π t = comb β (σ / κ) π t :=
    fun t => gap_comb hκ.ne' (hN t) (hN (t + 1))
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have h := hmult t
    rw [ht] at h
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [h]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc'
    push Not at hc'
    linarith [mul_pos hκ hc']
  have hBLt : ∀ t, t ≤ tZ → π (t + 1) ≤ c → lam κ ϑ x π t ≤ 0 := by
    intro t ht hp
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hbind t ht h
      rw [hgl t] at hg
      have : (r - 1) * π (t + 1) ≤ (r - 1) * c := mul_le_mul_of_nonneg_left hp (by linarith)
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc'
      push Not at hc'
      linarith [mul_pos hr0 hc']
  have hBLp : ∀ t, tZ < t → π (t + 1) ≤ 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht hp
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hpost t ht h
      rw [hgl t] at hg
      have : (r - 1) * π (t + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hp
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc'
      push Not at hc'
      linarith [mul_pos hr0 hc']
  have hn0 : π (s + 1) ≤ c := by
    have hg := htrap s hsZ
    have hl := hslack s hs0
    rw [hgl s] at hg
    have : r * lam κ ϑ x π s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le hl
    have h1 : (r - 1) * π (s + 1) ≤ (r - 1) * c := by linarith
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hTMP : ∀ j, j ≤ tZ → π (j + 1) ≤ π j → π (j + 1) ≤ π (j + 2) → η ≤ π (j + 1) := by
    intro j hj h1 h2
    have := htrap j hj
    rw [hgapc j] at this
    exact this.trans (comb_le_of_min hβ.le (by positivity) h1 h2)
  have hP0 : (∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c) → π 1 < π 0 := by
    intro hL
    have hz := mult_zero_left hβ hcc hpos hs0 (fun t ht => by
      have hl := hBLt t (by omega) (hL (t + 1) (by omega) (by omega))
      rw [← hmult t]
      exact mul_nonpos_of_nonneg_of_nonpos hκ.le hl) 0 (Nat.zero_le _)
    rw [hz, neg_zero] at hmI
    have hI0 : lamI κ ϑ x π = 0 := (mul_eq_zero.mp hmI).resolve_left hκ.ne'
    rw [lamI_eq hκ.ne' (hN 0)] at hI0
    have hp1 : π 1 < 0 := lt_of_le_of_lt (hL 1 le_rfl (by omega)) hc
    by_contra hcon
    push Not at hcon
    have h1 : θ * (π 0 - β * π 1) ≤ θ * (π 1 - β * π 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0.le
    have h2 : π 1 + θ * (π 1 - β * π 1) < 0 := by
      have : π 1 + θ * (π 1 - β * π 1) = π 1 * (1 + θ * (1 - β)) := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos hp1 (by nlinarith)
    linarith
  have hR : ∀ n, s + 1 ≤ n → n ≤ tZ + 1 → π n ≤ c := by
    intro n hn1 hn2
    by_contra hb
    push Not at hb
    have hns : s + 1 < n := by
      rcases hn1.eq_or_lt with h | h
      · subst h; linarith
      · exact h
    by_cases hL : ∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c
    · have h01 := hP0 hL
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc 0 n) π
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hmin 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        linarith
      have hmn : m ≠ n := by
        rintro rfl
        linarith
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      linarith
    · push Not at hL
      obtain ⟨a, ha1, ha2, hac⟩ := hL
      have has : a < s + 1 := by
        rcases ha2.eq_or_lt with h | h
        · subst h; linarith
        · exact h
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc a n) π
        ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hma : m ≠ a := by
        rintro rfl
        linarith
      have hmn : m ≠ n := by
        rintro rfl
        linarith
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      linarith
  have hE : π (tZ + 2) ≤ π (tZ + 1) := by
    by_cases hL : ∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c
    · have h01 := hP0 hL
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc 0 (tZ + 2)) π
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hmin 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        linarith
      by_cases hmt : m = tZ + 2
      · subst hmt
        exact hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        linarith
    · push Not at hL
      obtain ⟨a, ha1, ha2, hac⟩ := hL
      have has : a < s + 1 := by
        rcases ha2.eq_or_lt with h | h
        · subst h; linarith
        · exact h
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc a (tZ + 2)) π
        ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hma : m ≠ a := by
        rintro rfl
        linarith
      by_cases hmt : m = tZ + 2
      · subst hmt
        exact hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        linarith
  have hK1 : π (tZ + 2) < 0 := lt_of_le_of_lt hE (lt_of_le_of_lt (hR (tZ + 1) (by omega) le_rfl) hc)
  have hB1 : ∀ n, tZ + 2 ≤ n → π n ≤ 0 := by
    intro n hn
    refine post_nonpos hβ hβ1 hκ hσ hϑ hN (K := tZ + 1) (fun t ht => ?_) hK1 hS n hn
    rcases (hpos t).eq_or_lt with h | h
    · exact Or.inr (hslack t h.symm)
    · exact Or.inl (hpost t (by omega) h)
  have hlam : ∀ t, s ≤ t → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact hBLt t h (hR (t + 1) (by omega) (by omega))
    · exact hBLp t h (hB1 (t + 1) (by omega))
  have hz := mult_zero_right hβ hcc hpos hs0 (fun t ht => by
    rw [← hmult t]
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (hlam t ht.le)) hlim
  have hharm : ∀ t, s + 1 ≤ t → lam κ ϑ x π t = 0 := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h := hmult (t' + 1)
    rw [lag_succ, hz t' (by omega), hz (t' + 1) (by omega), hz (t' + 1 + 1) (by omega)] at h
    have h' : κ * lam κ ϑ x π (t' + 1) = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp h').resolve_left hκ.ne'
  have hθa : ∀ n, s + 1 ≤ n → comb β θ (fun k => -π k) n ≤ 0 ∨ comb β θ (fun k => -π k) n ≤ 0 :=
    fun n hn => Or.inl (by rw [comb_neg, ← hlamc n, hharm n hn, neg_zero])
  have h3 : π (tZ + 3) < π (tZ + 2) := by
    have h := hharm (tZ + 1) (by omega)
    rw [hlamc] at h
    unfold comb at h
    rw [show tZ + 1 + 1 = tZ + 2 by omega, show tZ + 1 + 2 = tZ + 3 by omega] at h
    by_contra hcon
    push Not at hcon
    have e1 : θ * (π (tZ + 2) - π (tZ + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ0.le (by linarith)
    have e2 : θ * (β * (π (tZ + 2) - π (tZ + 3))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ0.le
        (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
    have e3 : θ * ((π (tZ + 2) - π (tZ + 1)) + β * (π (tZ + 2) - π (tZ + 3))) =
        θ * (π (tZ + 2) - π (tZ + 1)) + θ * (β * (π (tZ + 2) - π (tZ + 3))) := by ring
    linarith
  have hbl := comb_blowup hβ hβ1.le hθ0 hθ0 le_rfl (u := fun k => -π k) (N0 := s + 1)
    (m0 := tZ + 2) hθa (by omega) (by change 0 < -π (tZ + 3); linarith)
    (by change -π (tZ + 2) < -π (tZ + 3); linarith)
  apply hbl
  simpa only [neg_sq] using hS

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **on a KKT path whose multipliers
satisfy `β^t ξ₂,t → 0`, every zero-bound multiplier of the shock interval is strictly positive**,
`0 < ξ₂,s` for all `s ≤ t_Z` (any `β ∈ (0,1)`, `κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`). -/
theorem trap_mult_pos {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hF : Feasible β κ σ (natRate ρ η tZ) x π) (hs : Summable (lossTerm β ϑ x π))
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hpos : ∀ t, 0 ≤ ξ2 t) (hcs : ∀ t, ξ2 t * impliedRate σ (natRate ρ η tZ) x π t = 0)
    (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0)) (s : ℕ) (hsZ : s ≤ tZ) :
    0 < ξ2 s := by
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hs
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (h35 (t + 1)) (h36 t) (h36 (t + 1))
  have hmI := lamI_mult hκ.ne' (h35 0) (h36 0)
  have hrate : ∀ t, 0 < ξ2 t → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hcs t)).resolve_left ht.ne'
  have htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t := by
    intro t ht
    have := rate_nonneg hσ hF t
    rw [impliedRate_eq_gap, natRate_of_le ht] at this
    linarith
  have hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η := by
    intro t ht h
    have := hrate t h
    rw [impliedRate_eq_gap, natRate_of_le ht] at this
    linarith
  have hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0 := by
    intro t ht h
    have := hrate t h
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  rcases (hpos s).eq_or_lt with h0 | h0
  · exfalso
    rcases le_or_gt (σ * κ) ϑ with hr | hr
    · exact slack_contra_le hβ hβ1 hκ hσ hϑ hη hr hsZ hN hS hpos hmult hmI htrap hbind hpost
        h0.symm
    · exact slack_contra_gt hβ hβ1 hκ hσ hϑ hη hr hsZ hN hS hpos hlim hmult hmI htrap hbind
        hpost h0.symm
  · exact h0

/-! ## Necessity of the Karush–Kuhn–Tucker conditions -/

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the multipliers
`(ξ₁, ξ₂)` attached to a path by solving (35)–(36) forward from `ξ₁,₋₁ = ξ₂,₋₁ = 0`. -/
noncomputable def mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (-π 0, -(κ * π 0) - ϑ * x 0)
  | t + 1 =>
    ((mult β κ σ ϑ x π t).1 + (mult β κ σ ϑ x π t).2 / (β * σ) - π (t + 1),
      (mult β κ σ ϑ x π t).2 / β +
        κ * ((mult β κ σ ϑ x π t).1 + (mult β κ σ ϑ x π t).2 / (β * σ) - π (t + 1)) -
          ϑ * x (t + 1))

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), p. 479: the Phillips-curve multiplier
`ξ₁` of `mult`. -/
noncomputable def mxi1 (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := (mult β κ σ ϑ x π t).1

/-- Galí (2015), eq. (36), p. 149; Cochrane (2023), p. 479: the zero-bound multiplier `ξ₂` of
`mult`. -/
noncomputable def mxi2 (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := (mult β κ σ ϑ x π t).2

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), p. 479: `mult` satisfies (35) at every date. -/
theorem foc35_mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) :
    FOC35 β σ π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t := by
  unfold FOC35
  cases t with
  | zero => simp [mxi1, mult]
  | succ t => simp only [lag_succ, mxi1, mxi2, mult]; ring

/-- Galí (2015), eq. (36), p. 149; Cochrane (2023), p. 479: `mult` satisfies (36) at every date. -/
theorem foc36_mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) :
    FOC36 β κ ϑ x (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t := by
  unfold FOC36
  cases t with
  | zero => simp only [lag_zero, mxi1, mxi2, mult]; ring
  | succ t => simp only [lag_succ, mxi1, mxi2, mult]; ring

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), p. 479: the multipliers solving
(35)–(36) on `[0, N]` are unique (they are `mult`). -/
theorem mult_unique {β κ σ ϑ : ℝ} {x π ξ1 ξ2 : ℕ → ℝ} {N : ℕ}
    (h : ∀ t, t ≤ N → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t) :
    ∀ t, t ≤ N → ξ1 t = mxi1 β κ σ ϑ x π t ∧ ξ2 t = mxi2 β κ σ ϑ x π t := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨a, b⟩ := h 0 (Nat.zero_le _)
    unfold FOC35 at a
    unfold FOC36 at b
    simp only [lag_zero, zero_div, sub_zero] at a b
    simp only [mxi1, mxi2, mult]
    exact ⟨by linear_combination a, by linear_combination b + κ * a⟩
  | succ t ih =>
    intro ht
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨a, b⟩ := h (t + 1) ht
    unfold FOC35 at a
    unfold FOC36 at b
    simp only [lag_succ] at a b
    have e1 : ξ1 (t + 1) = mxi1 β κ σ ϑ x π (t + 1) := by
      simp only [mxi1, mult]
      rw [← mxi1, ← mxi2, ← i1, ← i2]
      linarith
    refine ⟨e1, ?_⟩
    simp only [mxi2, mult]
    rw [← mxi1, ← mxi2, ← i1, ← i2]
    have : ξ1 (t + 1) = ξ1 t + ξ2 t / (β * σ) - π (t + 1) := by linarith
    rw [← this]
    linarith

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the cross term `β^t (π_t dπ_t + ϑ x_t dx_t)`
of the loss in a direction `(dx, dπ)`. -/
noncomputable def cross (β ϑ : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t * dπ t + ϑ * x t * dx t)

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the loss term along `(x, π) + ε (dx, dπ)`. -/
theorem lossTerm_pert (β ϑ ε : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) t =
      lossTerm β ϑ x π t + 2 * ε * cross β ϑ x π dx dπ t + ε ^ 2 * lossTerm β ϑ dx dπ t := by
  unfold lossTerm cross; ring

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: with finite losses the cross term is summable. -/
theorem summable_cross {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 < ϑ) {x π dx dπ : ℕ → ℝ}
    (h1 : Summable (lossTerm β ϑ x π)) (h2 : Summable (lossTerm β ϑ dx dπ)) :
    Summable (cross β ϑ x π dx dπ) := by
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) (fun t => ?_)
  unfold cross lossTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have ha : |π t * dπ t + ϑ * x t * dx t| ≤
      ((π t ^ 2 + ϑ * x t ^ 2) + (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (π t + dπ t), sq_nonneg (x t + dx t), mul_nonneg hϑ.le
        (sq_nonneg (x t + dx t))]
    · nlinarith [sq_nonneg (π t - dπ t), sq_nonneg (x t - dx t), mul_nonneg hϑ.le
        (sq_nonneg (x t - dx t))]
  calc β ^ t * |π t * dπ t + ϑ * x t * dx t|
      ≤ β ^ t * (((π t ^ 2 + ϑ * x t ^ 2) + (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left ha hp
    _ = (β ^ t * (π t ^ 2 + ϑ * x t ^ 2) + β ^ t * (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2 := by ring

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **first-order necessary condition**.
If `(x, π)` is optimal and `(x, π) + ε (dx, dπ)` is feasible for all small `ε > 0` (`dx, dπ` with
finite loss), the derivative of the loss in that direction is nonnegative:
`0 ≤ ∑ β^t (π_t dπ_t + ϑ x_t dx_t)`. -/
theorem foc_dir {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x π dx dπ : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ rn x π) (hd : Summable (lossTerm β ϑ dx dπ)) {ε0 : ℝ}
    (hε0 : 0 < ε0)
    (hfe : ∀ ε, 0 < ε → ε ≤ ε0 →
      Feasible β κ σ rn (fun t => x t + ε * dx t) (fun t => π t + ε * dπ t)) :
    0 ≤ ∑' t, cross β ϑ x π dx dπ t := by
  obtain ⟨-, hs, hmin⟩ := hopt
  have hc := summable_cross hβ.le hϑ hs hd
  set B := ∑' t, cross β ϑ x π dx dπ t with hB
  set L := ∑' t, lossTerm β ϑ dx dπ t with hL
  have hL0 : 0 ≤ L := tsum_nonneg fun t => by unfold lossTerm; positivity
  have key : ∀ ε, 0 < ε → ε ≤ ε0 → 0 ≤ 2 * B + ε * L := by
    intro ε hε he0
    have hsum : Summable (lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s)) := by
      have := (hs.add (hc.mul_left (2 * ε))).add (hd.mul_left (ε ^ 2))
      exact this.congr fun t => (lossTerm_pert β ϑ ε x π dx dπ t).symm
    have hle := hmin _ _ (hfe ε hε he0) hsum
    have he : loss β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) =
        loss β ϑ x π + 2 * ε * B + ε ^ 2 * L := by
      unfold loss
      rw [show (fun t => lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) t) =
        fun t => (lossTerm β ϑ x π t + 2 * ε * cross β ϑ x π dx dπ t) +
          ε ^ 2 * lossTerm β ϑ dx dπ t from funext fun t => lossTerm_pert β ϑ ε x π dx dπ t]
      rw [(hs.add (hc.mul_left (2 * ε))).tsum_add (hd.mul_left (ε ^ 2)),
        hs.tsum_add (hc.mul_left (2 * ε)), tsum_mul_left, tsum_mul_left]
    rw [he] at hle
    have h2 : 0 ≤ ε * (2 * B + ε * L) := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_pos_of_neg hε hc]
  by_contra hneg
  push Not at hneg
  set ε := min ε0 (-B / (L + 1)) with hε
  have hεpos : 0 < ε := lt_min hε0 (div_pos (by linarith) (by linarith))
  have k := key ε hεpos (min_le_left _ _)
  have h1 : ε * L ≤ -B / (L + 1) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0
  have h2 : -B / (L + 1) * L < -B := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 479:
`(x, π) + ε (dx, dπ)` is feasible when `(dx, dπ)` satisfies the linear Phillips curve and the
change of `x_t − υ₁,t` keeps the bound: `(x_t − υ₁,t) + ε (dx_t − dx_{t+1} − dπ_{t+1}/σ) ≤ 0`. -/
theorem feasible_pert {β κ σ ε : ℝ} {rn x π dx dπ : ℕ → ℝ} (hF : Feasible β κ σ rn x π)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t)
    (hb : ∀ t, x t - ups1 σ rn x π t + ε * (dx t - dx (t + 1) - dπ (t + 1) / σ) ≤ 0) :
    Feasible β κ σ rn (fun t => x t + ε * dx t) (fun t => π t + ε * dπ t) := by
  intro t
  obtain ⟨hN, -⟩ := hF t
  refine ⟨?_, ?_⟩
  · unfold NKPC at hN ⊢
    simp only
    rw [hN, hd t]
    ring
  · have := hb t
    unfold ups1 at this ⊢
    simp only
    have e : x (t + 1) + ε * dx (t + 1) + (π (t + 1) + ε * dπ (t + 1) + rn t) / σ =
        x (t + 1) + (π (t + 1) + rn t) / σ + ε * (dx (t + 1) + dπ (t + 1) / σ) := by ring
    rw [e]
    linarith

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the cross term is odd in the direction. -/
theorem cross_neg (β ϑ : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) :
    cross β ϑ x π (fun s => -dx s) (fun s => -dπ s) t = -cross β ϑ x π dx dπ t := by
  unfold cross; ring

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: a direction obeying one backward step
at forcing `e` satisfies the linear Phillips curve and changes `x_t − υ₁,t` by `−e/σ` (raises
the rate gap by `e`). -/
theorem dir_of_step {β κ σ e : ℝ} (hσ : σ ≠ 0) {d : ℕ → ℝ × ℝ} {t : ℕ}
    (h : d t = backStep β κ σ e (d (t + 1))) :
    (d t).2 = β * (d (t + 1)).2 + κ * (d t).1 ∧
      (d t).1 - (d (t + 1)).1 - (d (t + 1)).2 / σ = -(e / σ) := by
  rw [h]
  simp only [backStep]
  constructor
  · field_simp; ring
  · ring

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (34)): the direction **"raise the rate at date
`s` by one, holding all other rates and the path after `s` fixed"**: zero after `s`,
`(−1/σ, −κ/σ)` at `s`, and the zero-gap backward recursion before `s` (finite support). -/
noncomputable def hdir (β κ σ : ℝ) (s t : ℕ) : ℝ × ℝ :=
  if t ≤ s then backState β κ σ 0 (-(1 / σ), -(κ / σ)) (s - t) else (0, 0)

/-- Cochrane (2023), p. 479: `hdir` is zero after `s`. -/
theorem hdir_gt {β κ σ : ℝ} {s t : ℕ} (h : s < t) : hdir β κ σ s t = (0, 0) := by
  simp [hdir, Nat.not_le.mpr h]

/-- Cochrane (2023), p. 479 (Galí (2015), (34)): `hdir` obeys one backward step at forcing `1`
at `s` and `0` elsewhere. -/
theorem hdir_step (β κ σ : ℝ) (s t : ℕ) :
    hdir β κ σ s t = backStep β κ σ (if t = s then 1 else 0) (hdir β κ σ s (t + 1)) := by
  rcases lt_trichotomy t s with h | rfl | h
  · unfold hdir
    simp only [show t ≤ s from h.le, show t + 1 ≤ s from h, ↓reduceIte, h.ne]
    rw [show s - t = (s - (t + 1)) + 1 by omega]
    rfl
  · rw [hdir_gt (show t < t + 1 by omega)]
    simp only [hdir, le_refl, ↓reduceIte, Nat.sub_self, backState, backStep]
    ext <;> simp
  · rw [hdir_gt h, hdir_gt (show s < t + 1 by omega)]
    simp only [h.ne', ↓reduceIte, backStep]
    ext <;> simp

/-- Cochrane (2023), p. 479: `hdir` satisfies the linear Phillips curve and raises the rate gap
by one exactly at `s`. -/
theorem hdir_dir {β κ σ : ℝ} (hσ : σ ≠ 0) (s t : ℕ) :
    (hdir β κ σ s t).2 = β * (hdir β κ σ s (t + 1)).2 + κ * (hdir β κ σ s t).1 ∧
      (hdir β κ σ s t).1 - (hdir β κ σ s (t + 1)).1 - (hdir β κ σ s (t + 1)).2 / σ =
        -((if t = s then 1 else 0) / σ) :=
  dir_of_step hσ (d := hdir β κ σ s) (hdir_step β κ σ s t)

/-- Galí (2015), p. 148: `hdir` has finite loss (finite support). -/
theorem hdir_summable (β ϑ κ σ : ℝ) (s : ℕ) :
    Summable (lossTerm β ϑ (fun t => (hdir β κ σ s t).1) (fun t => (hdir β κ σ s t).2)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (s + 1)) fun t ht => ?_
  rw [Finset.mem_range, not_lt] at ht
  simp [lossTerm, hdir_gt (show s < t by omega)]

/-- Galí (2015), p. 149 (the Lagrangian identity `lagrangian_identity`); Cochrane (2023), p. 479:
the derivative of the loss in the direction `hdir s` is `β^s ξ₂,s / σ`, for any multipliers
solving (35)–(36). -/
theorem cross_hdir {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t) (s : ℕ) :
    ∑' t, cross β ϑ x π (fun t => (hdir β κ σ s t).1) (fun t => (hdir β κ σ s t).2) t =
      β ^ s * ξ2 s / σ := by
  have hd : ∀ t, (hdir β κ σ s t).2 = β * (hdir β κ σ s (t + 1)).2 + κ * (hdir β κ σ s t).1 :=
    fun t => (hdir_dir hσ s t).1
  rw [tsum_eq_sum (s := Finset.range (s + 1 + 1)) fun t ht => by
    rw [Finset.mem_range, not_lt] at ht
    simp [cross, hdir_gt (show s < t by omega)]]
  unfold cross
  rw [lagrangian_identity hβ hσ h35 h36 hd (s + 1)]
  rw [hdir_gt (show s < s + 1 by omega), hdir_gt (show s < s + 1 + 1 by omega)]
  simp only [mul_zero, sub_zero]
  rw [Finset.sum_eq_single s]
  · have := (hdir_dir (β := β) (κ := κ) hσ s s).2
    simp only [↓reduceIte] at this
    have e : (hdir β κ σ s (s + 1)).1 + (hdir β κ σ s (s + 1)).2 / σ - (hdir β κ σ s s).1 =
        1 / σ := by linarith
    rw [e]
    ring
  · intro u _ hu
    have := (hdir_dir (β := β) (κ := κ) hσ s u).2
    simp only [hu, ↓reduceIte, zero_div, neg_zero] at this
    have e : (hdir β κ σ s (u + 1)).1 + (hdir β κ σ s (u + 1)).2 / σ - (hdir β κ σ s u).1 = 0 :=
      by linarith
    rw [e]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Cochrane (2023), §20.1, p. 467 (`ZLBPeg`), §20.2.2, p. 475: the bounded peg mode
`w_t = λ₁⁻ᵗ (v_x, 1)`, a direction with zero rate gap at every date. -/
noncomputable def wdir (β κ σ : ℝ) (t : ℕ) : ℝ × ℝ :=
  ((l1 β σ κ)⁻¹ ^ t * vx β σ κ, (l1 β σ κ)⁻¹ ^ t)

/-- Cochrane (2023), p. 475 (`backStep_eigen`): `w` obeys the zero-gap backward recursion. -/
theorem wdir_step {β κ σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (t : ℕ) :
    wdir β κ σ t = backStep β κ σ 0 (wdir β κ σ (t + 1)) := by
  have hl : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  unfold wdir
  rw [backStep_eigen hβ hσ hκ]
  have e : l1 β σ κ * (l1 β σ κ)⁻¹ ^ (t + 1) = (l1 β σ κ)⁻¹ ^ t := by
    rw [pow_succ]; field_simp
  ext
  · simp only; rw [← mul_assoc, e]
  · simp only; rw [e]

/-- Cochrane (2023), p. 475: `w` satisfies the linear Phillips curve and leaves every rate gap
unchanged. -/
theorem wdir_dir {β κ σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (t : ℕ) :
    (wdir β κ σ t).2 = β * (wdir β κ σ (t + 1)).2 + κ * (wdir β κ σ t).1 ∧
      (wdir β κ σ t).1 - (wdir β κ σ (t + 1)).1 - (wdir β κ σ (t + 1)).2 / σ = 0 := by
  have := dir_of_step hσ.ne' (d := wdir β κ σ) (wdir_step hβ hσ hκ t)
  simpa using this

/-- Galí (2015), p. 148: the peg mode has finite loss (`β λ₁⁻² < 1`). -/
theorem wdir_summable {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) :
    Summable (lossTerm β ϑ (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2)) := by
  have hl := one_lt_l1 hβ hσ hκ
  set q := (l1 β σ κ)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hl
  have hg : β * q ^ 2 < 1 := by
    have : q ^ 2 < 1 := by nlinarith
    nlinarith
  have e : (lossTerm β ϑ (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2)) =
      fun t => (1 + ϑ * vx β σ κ ^ 2) * (β * q ^ 2) ^ t := by
    funext t
    simp only [lossTerm, wdir]
    rw [← hq]
    ring
  rw [e]
  exact (summable_geometric_of_lt_one (by positivity) hg).mul_left _

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479 (the choice among the peg family is
free): at an optimum the derivative of the loss in the peg direction vanishes. -/
theorem cross_wdir {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    ∑' t, cross β ϑ x π (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2) t = 0 := by
  have hw := wdir_summable (ϑ := ϑ) hβ hβ1 hσ hκ
  have hd := fun t => (wdir_dir hβ hσ hκ t)
  have h1 := foc_dir hβ hϑ hopt hw one_pos fun ε _ _ =>
    feasible_pert hopt.1 (fun t => (hd t).1) fun t => by
      rw [(hd t).2, mul_zero, add_zero]; linarith [(hopt.1 t).2]
  have hwn : Summable (lossTerm β ϑ (fun t => -(wdir β κ σ t).1) fun t => -(wdir β κ σ t).2) :=
    hw.congr fun t => by simp [lossTerm]
  have h2 := foc_dir hβ hϑ hopt hwn one_pos fun ε _ _ =>
    feasible_pert hopt.1 (fun t => by rw [(hd t).1]; ring) fun t => by
      have := (hd t).2
      have e : -(wdir β κ σ t).1 - -(wdir β κ σ (t + 1)).1 - -(wdir β κ σ (t + 1)).2 / σ = 0 := by
        rw [neg_div]; linarith
      rw [e, mul_zero, add_zero]; linarith [(hopt.1 t).2]
  simp only [cross_neg, tsum_neg] at h2
  linarith

/-! ### The two modes of the zero-gap dynamics and transversality of the multipliers -/

/-- Cochrane (2023), eq. (5.6), p. 119: the output-gap coordinate `(1 − λ₁)/κ` of the stable
backward mode `λ₂` of the zero-gap dynamics. -/
noncomputable def vx2 (β σ κ : ℝ) : ℝ := (1 - l1 β σ κ) / κ

/-- Cochrane (2023), p. 479: the coefficient of the `λ₁`-mode in `(−1/σ, −κ/σ)`. -/
noncomputable def cf1 (β σ κ : ℝ) : ℝ := -(κ / σ) * l1 β σ κ / (l1 β σ κ - l2 β σ κ)

/-- Cochrane (2023), p. 479: the coefficient of the `λ₂`-mode in `(−1/σ, −κ/σ)`. -/
noncomputable def cf2 (β σ κ : ℝ) : ℝ := κ / σ * l2 β σ κ / (l1 β σ κ - l2 β σ κ)

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ + λ₂ = 1 + β + κ/σ`. -/
theorem l_add (β σ κ : ℝ) : l1 β σ κ + l2 β σ κ = 1 + β + κ / σ := by
  have := ZLBPeg.lam_add β σ⁻¹ κ
  unfold l1 l2
  rw [this]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ λ₂ = β`. -/
theorem l_mul {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l1 β σ κ * l2 β σ κ = β :=
  ZLBPeg.lam_mul hβ (by positivity)

/-- Cochrane (2023), eq. (5.6), p. 119: `0 < λ₂ < 1 < λ₁`. -/
theorem l2_bounds {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    0 < l2 β σ κ ∧ l2 β σ κ < 1 :=
  ⟨ZLBPeg.lam2_pos hβ (by positivity), ZLBPeg.lam2_lt_one hβ (by positivity)⟩

/-- Cochrane (2023), p. 475: `λ₂ v₂ = v₂ + σ⁻¹` (the `λ₂` eigenvector of the backward map). -/
theorem l2_vx2 {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l2 β σ κ * vx2 β σ κ = vx2 β σ κ + σ⁻¹ := by
  have ha := l_add β σ κ
  have hm := l_mul hβ hσ hκ
  have key : (l2 β σ κ - 1) * (1 - l1 β σ κ) = κ / σ := by linear_combination ha - hm
  unfold vx2
  rw [show l2 β σ κ * ((1 - l1 β σ κ) / κ) =
    (1 - l1 β σ κ) / κ + (l2 β σ κ - 1) * (1 - l1 β σ κ) / κ by ring, key]
  field_simp

/-- Cochrane (2023), p. 475: `κ v₂ + β + κ/σ = λ₂`. -/
theorem kappa_vx2 {β σ κ : ℝ} (hκ : 0 < κ) : κ * vx2 β σ κ + (β + κ / σ) = l2 β σ κ := by
  have ha := l_add β σ κ
  have : κ * vx2 β σ κ = 1 - l1 β σ κ := by unfold vx2; field_simp
  rw [this]
  linarith

/-- Cochrane (2023), p. 479: `(−1/σ, −κ/σ) = c₁ (v_x, 1) + c₂ (v₂, 1)`, first coordinate. -/
theorem cf_vx {β σ κ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hl : l1 β σ κ - l2 β σ κ ≠ 0) :
    cf1 β σ κ * vx β σ κ + cf2 β σ κ * vx2 β σ κ = -(1 / σ) := by
  unfold cf1 cf2 vx vx2
  field_simp
  ring

/-- Cochrane (2023), p. 479: `(−1/σ, −κ/σ) = c₁ (v_x, 1) + c₂ (v₂, 1)`, second coordinate. -/
theorem cf_sum {β σ κ : ℝ} (hl : l1 β σ κ - l2 β σ κ ≠ 0) :
    cf1 β σ κ + cf2 β σ κ = -(κ / σ) := by
  unfold cf1 cf2
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (Galí (2015), (34)): `k` zero-gap backward steps from
`(−1/σ, −κ/σ)` are `c₁ λ₁ᵏ (v_x, 1) + c₂ λ₂ᵏ (v₂, 1)`. -/
theorem backState_closed {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (k : ℕ) :
    backState β κ σ 0 (-(1 / σ), -(κ / σ)) k =
      (cf1 β σ κ * l1 β σ κ ^ k * vx β σ κ + cf2 β σ κ * l2 β σ κ ^ k * vx2 β σ κ,
        cf1 β σ κ * l1 β σ κ ^ k + cf2 β σ κ * l2 β σ κ ^ k) := by
  have hl : l1 β σ κ - l2 β σ κ ≠ 0 := by
    have := one_lt_l1 hβ hσ hκ
    have := (l2_bounds hβ hσ hκ).2
    linarith
  have h1 := l1_vx hβ hσ hκ
  have h2 := l2_vx2 hβ hσ hκ
  have g1 := kappa_vx (β := β) (σ := σ) hκ
  have g2 := kappa_vx2 (β := β) (σ := σ) hκ
  induction k with
  | zero =>
    simp only [backState, pow_zero, mul_one]
    rw [cf_vx hκ hσ hl, cf_sum hl]
  | succ k ih =>
    simp only [backState]
    rw [ih]
    simp only [backStep]
    ext
    · simp only
      linear_combination (-(cf1 β σ κ * l1 β σ κ ^ k)) * h1 - cf2 β σ κ * l2 β σ κ ^ k * h2
    · simp only
      linear_combination (cf1 β σ κ * l1 β σ κ ^ k) * g1 + (cf2 β σ κ * l2 β σ κ ^ k) * g2

/-- Cochrane (2023), p. 479: the direction `hdir s` minus `c₁ λ₁ˢ` times the peg mode: only the
stable backward mode `λ₂^{s−t}` survives before `s`, and the forward-decaying `λ₁^{-(t−s)}`
after. -/
noncomputable def ddir (β κ σ : ℝ) (s t : ℕ) : ℝ × ℝ :=
  ((hdir β κ σ s t).1 - cf1 β σ κ * l1 β σ κ ^ s * (wdir β κ σ t).1,
    (hdir β κ σ s t).2 - cf1 β σ κ * l1 β σ κ ^ s * (wdir β κ σ t).2)

/-- Cochrane (2023), p. 479: `ddir` before `s`. -/
theorem ddir_le {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {s t : ℕ} (h : t ≤ s) :
    ddir β κ σ s t = (cf2 β σ κ * l2 β σ κ ^ (s - t) * vx2 β σ κ,
      cf2 β σ κ * l2 β σ κ ^ (s - t)) := by
  have hl0 : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t = l1 β σ κ ^ (s - t) := by
    rw [show s = (s - t) + t by omega, pow_add, Nat.add_sub_cancel, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hl0, one_pow, mul_one]
  unfold ddir wdir
  rw [show hdir β κ σ s t = backState β κ σ 0 (-(1 / σ), -(κ / σ)) (s - t) by
    simp [hdir, h], backState_closed hβ hσ hκ]
  ext
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * ((l1 β σ κ)⁻¹ ^ t * vx β σ κ) =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) * vx β σ κ by ring, e]
    ring
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) by ring, e]
    ring

/-- Cochrane (2023), p. 479: `ddir` after `s`. -/
theorem ddir_gt {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {s t : ℕ} (h : s < t) :
    ddir β κ σ s t = (-(cf1 β σ κ * (l1 β σ κ)⁻¹ ^ (t - s) * vx β σ κ),
      -(cf1 β σ κ * (l1 β σ κ)⁻¹ ^ (t - s))) := by
  have hl0 : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t = (l1 β σ κ)⁻¹ ^ (t - s) := by
    rw [show t = (t - s) + s by omega, pow_add, Nat.add_sub_cancel, mul_comm, mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hl0, one_pow, mul_one]
  unfold ddir wdir
  rw [hdir_gt h]
  ext
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * ((l1 β σ κ)⁻¹ ^ t * vx β σ κ) =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) * vx β σ κ by ring, e]
    ring
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) by ring, e]
    ring

/-- Cochrane (2023), p. 479: `ddir` is bounded uniformly in `s` and `t`. -/
theorem ddir_bound {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (s t : ℕ) :
    |(ddir β κ σ s t).1| ≤ |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1) ∧
      |(ddir β κ σ s t).2| ≤
        |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1) := by
  obtain ⟨h20, h21⟩ := l2_bounds hβ hσ hκ
  have hl := one_lt_l1 hβ hσ hκ
  have hq0 : 0 < (l1 β σ κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (l1 β σ κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl).le
  have a1 := abs_nonneg (cf1 β σ κ)
  have a2 := abs_nonneg (cf2 β σ κ)
  have b1 := abs_nonneg (vx β σ κ)
  have b2 := abs_nonneg (vx2 β σ κ)
  rcases le_or_gt t s with h | h
  · rw [ddir_le hβ hσ hκ h]
    have p0 : 0 ≤ l2 β σ κ ^ (s - t) := pow_nonneg h20.le _
    have p1 : l2 β σ κ ^ (s - t) ≤ 1 := pow_le_one₀ h20.le h21.le
    simp only [abs_mul, abs_of_nonneg p0]
    constructor
    · have : |cf2 β σ κ| * l2 β σ κ ^ (s - t) * |vx2 β σ κ| ≤ |cf2 β σ κ| * |vx2 β σ κ| := by
        have := mul_le_mul_of_nonneg_left p1 a2
        nlinarith
      nlinarith
    · have : |cf2 β σ κ| * l2 β σ κ ^ (s - t) ≤ |cf2 β σ κ| :=
        mul_le_of_le_one_right a2 p1
      nlinarith
  · rw [ddir_gt hβ hσ hκ h]
    have p0 : 0 ≤ (l1 β σ κ)⁻¹ ^ (t - s) := pow_nonneg hq0.le _
    have p1 : (l1 β σ κ)⁻¹ ^ (t - s) ≤ 1 := pow_le_one₀ hq0.le hq1
    simp only [abs_neg, abs_mul, abs_of_nonneg p0]
    constructor
    · have : |cf1 β σ κ| * (l1 β σ κ)⁻¹ ^ (t - s) * |vx β σ κ| ≤ |cf1 β σ κ| * |vx β σ κ| := by
        have := mul_le_mul_of_nonneg_left p1 a1
        nlinarith
      nlinarith
    · have : |cf1 β σ κ| * (l1 β σ κ)⁻¹ ^ (t - s) ≤ |cf1 β σ κ| :=
        mul_le_of_le_one_right a1 p1
      nlinarith

/-- Galí (2015), p. 148: with a finite loss, `β^t |π_t|` and `β^t |x_t|` are summable. -/
theorem summable_abs {β ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) :
    Summable (fun t => β ^ t * |π t|) ∧ Summable (fun t => β ^ t * |x t|) := by
  have hg : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.le hβ1
  have hp : Summable (fun t => β ^ t * π t ^ 2) := by
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) hs
    unfold lossTerm
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    nlinarith
  have hx : Summable (fun t => β ^ t * x t ^ 2) := by
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hs.div_const ϑ)
    unfold lossTerm
    rw [le_div_iff₀ hϑ]
    have : 0 ≤ β ^ t * π t ^ 2 * ϑ := by positivity
    nlinarith
  constructor
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      ((hg.add hp).div_const 2)
    have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : |π t| ≤ (1 + π t ^ 2) / 2 := by nlinarith [sq_nonneg (|π t| - 1), sq_abs (π t)]
    nlinarith
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      ((hg.add hx).div_const 2)
    have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : |x t| ≤ (1 + x t ^ 2) / 2 := by nlinarith [sq_nonneg (|x t| - 1), sq_abs (x t)]
    nlinarith

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **transversality of the multipliers**.
At an optimum the zero-bound multipliers of `mult` satisfy `β^t ξ₂,t → 0`: the derivative in the
direction `hdir t` equals that in the localised direction `ddir t` (the peg-mode derivative is
zero, `cross_wdir`), which tends to zero by dominated convergence (Tannery). -/
theorem tendsto_mxi2 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    Tendsto (fun t => β ^ t * mxi2 β κ σ ϑ x π t) atTop (𝓝 0) := by
  have hs := hopt.2.1
  have hw := wdir_summable (ϑ := ϑ) hβ hβ1 hσ hκ
  have hcw := summable_cross hβ.le hϑ hs hw
  have hw0 := cross_wdir hβ hβ1 hκ hσ hϑ hopt
  have hsplit : ∀ s, β ^ s * mxi2 β κ σ ϑ x π s / σ =
      ∑' t, cross β ϑ x π (fun t => (ddir β κ σ s t).1) (fun t => (ddir β κ σ s t).2) t := by
    intro s
    rw [← cross_hdir hβ.ne' hσ.ne' (foc35_mult β κ σ ϑ x π) (foc36_mult β κ σ ϑ x π) s]
    have hch := summable_cross hβ.le hϑ hs (hdir_summable β ϑ κ σ s)
    set c := cf1 β σ κ * l1 β σ κ ^ s
    have e : (fun t => cross β ϑ x π (fun t => (hdir β κ σ s t).1)
        (fun t => (hdir β κ σ s t).2) t) = fun t =>
        cross β ϑ x π (fun t => (ddir β κ σ s t).1) (fun t => (ddir β κ σ s t).2) t +
          c * cross β ϑ x π (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2) t := by
      funext t
      simp only [cross, ddir, c]
      ring
    have hcd : Summable (fun t => cross β ϑ x π (fun t => (ddir β κ σ s t).1)
        (fun t => (ddir β κ σ s t).2) t) := by
      have := hch.sub (hcw.mul_left c)
      refine this.congr fun t => ?_
      have := congrFun e t
      linarith
    rw [e, hcd.tsum_add (hcw.mul_left c), tsum_mul_left, hw0, mul_zero, add_zero]
  obtain ⟨hsp, hsx⟩ := summable_abs hβ hβ1 hϑ hs
  set C := |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1)
  have hC : 0 ≤ C := by positivity
  have hT : Tendsto (fun s => ∑' t, cross β ϑ x π (fun t => (ddir β κ σ s t).1)
      (fun t => (ddir β κ σ s t).2) t) atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun t =>
      C * (β ^ t * |π t|) + ϑ * C * (β ^ t * |x t|))
      ((hsp.mul_left C).add (hsx.mul_left (ϑ * C))) (fun t => ?_) ?_
    · obtain ⟨h20, h21⟩ := l2_bounds hβ hσ hκ
      have hp : Tendsto (fun s : ℕ => l2 β σ κ ^ (s - t)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one h20.le h21).comp (tendsto_sub_atTop_nat t)
      have hm := hp.const_mul (β ^ t * cf2 β σ κ * (π t + ϑ * x t * vx2 β σ κ))
      rw [mul_zero] at hm
      refine hm.congr' ?_
      filter_upwards [eventually_ge_atTop t] with s hst
      simp only [cross, ddir_le hβ hσ hκ hst]
      ring
    · refine Eventually.of_forall fun s t => ?_
      obtain ⟨b1, b2⟩ := ddir_bound hβ hσ hκ s t
      unfold cross
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
      have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
      have h1 : |π t * (ddir β κ σ s t).2 + ϑ * x t * (ddir β κ σ s t).1| ≤
          |π t| * C + ϑ * |x t| * C := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hϑ]
        have := mul_le_mul_of_nonneg_left b2 (abs_nonneg (π t))
        have := mul_le_mul_of_nonneg_left b1 (mul_nonneg hϑ.le (abs_nonneg (x t)))
        nlinarith
      calc β ^ t * |π t * (ddir β κ σ s t).2 + ϑ * x t * (ddir β κ σ s t).1|
          ≤ β ^ t * (|π t| * C + ϑ * |x t| * C) := mul_le_mul_of_nonneg_left h1 hpt
        _ = C * (β ^ t * |π t|) + ϑ * C * (β ^ t * |x t|) := by ring
  rw [tsum_zero] at hT
  have := hT.const_mul σ
  rw [mul_zero] at this
  refine this.congr fun s => ?_
  rw [← hsplit s]
  field_simp

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **necessity of the KKT conditions**.
If `(x, π)` solves the commitment problem (for any natural-rate path), the multipliers `mult`
solve (35)–(36), are nonnegative, satisfy complementary slackness, and `β^t ξ₂,t → 0`. -/
theorem kkt_necessary {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    KKT β κ σ ϑ rn x π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) ∧
      Tendsto (fun t => β ^ t * mxi2 β κ σ ϑ x π t) atTop (𝓝 0) := by
  have hF := hopt.1
  have hcr := fun s => cross_hdir hβ.ne' hσ.ne' (foc35_mult β κ σ ϑ x π)
    (foc36_mult β κ σ ϑ x π) (ϑ := ϑ) (κ := κ) s
  have hdd := fun s t => hdir_dir (β := β) (κ := κ) hσ.ne' s t
  have hnn : ∀ s, 0 ≤ mxi2 β κ σ ϑ x π s := by
    intro s
    have h := foc_dir hβ hϑ hopt (hdir_summable β ϑ κ σ s) one_pos fun ε hε _ =>
      feasible_pert hF (fun t => (hdd s t).1) fun t => by
        rw [(hdd s t).2]
        have h1 : 0 ≤ (if t = s then (1 : ℝ) else 0) / σ := by
          split_ifs <;> positivity
        have := (hF t).2
        nlinarith
    rw [hcr s] at h
    have hp : 0 < β ^ s := pow_pos hβ s
    by_contra hc
    push Not at hc
    have : β ^ s * mxi2 β κ σ ϑ x π s / σ < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hc) hσ
    linarith
  refine ⟨⟨hF, fun t => ⟨foc35_mult β κ σ ϑ x π t, foc36_mult β κ σ ϑ x π t, hnn t, ?_⟩⟩,
    tendsto_mxi2 hβ hβ1 hκ hσ hϑ hopt⟩
  rcases (rate_nonneg hσ hF t).eq_or_lt with h | h
  · rw [← h, mul_zero]
  · have hneg : Summable (lossTerm β ϑ (fun u => -(hdir β κ σ t u).1)
        fun u => -(hdir β κ σ t u).2) :=
      (hdir_summable β ϑ κ σ t).congr fun u => by simp [lossTerm]
    have hb := foc_dir hβ hϑ hopt hneg h fun ε hε hεi =>
      feasible_pert hF (fun u => by rw [(hdd t u).1]; ring) fun u => by
        have e := (hdd t u).2
        have e2 : -(hdir β κ σ t u).1 - -(hdir β κ σ t (u + 1)).1 -
            -(hdir β κ σ t (u + 1)).2 / σ = (if u = t then (1 : ℝ) else 0) / σ := by
          rw [neg_div]; linarith
        rw [e2]
        have hr := impliedRate_eq hσ.ne' rn x π u
        split_ifs with hu
        · subst hu
          have : ε / σ ≤ ups1 σ rn x π u - x u := by
            rw [div_le_iff₀ hσ]; nlinarith
          have e3 : ε * (1 / σ) = ε / σ := by ring
          rw [e3]; linarith
        · rw [zero_div, mul_zero, add_zero]; linarith [(hF u).2]
    simp only [cross_neg, tsum_neg] at hb
    rw [hcr t] at hb
    have hp : 0 < β ^ t := pow_pos hβ t
    have hle : mxi2 β κ σ ϑ x π t ≤ 0 := by
      by_contra hc
      push Not at hc
      have : 0 < β ^ t * mxi2 β κ σ ϑ x π t / σ := by positivity
      linarith
    rw [le_antisymm hle (hnn t), zero_mul]

/-! ## At the commitment optimum the zero bound binds throughout the shock -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2, pp. 148–152: **at the
commitment optimum the interest rate is zero at every date of the shock**, `i_t = 0` for all
`t ≤ t_Z`, and the zero-bound multiplier is strictly positive there (any `β ∈ (0,1)`,
`κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`). This is the step Galí's algorithm assumes (`t_C ≥ t_Z`). -/
theorem optimal_trap_binds {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ) (ht : t ≤ tZ) :
    impliedRate σ (natRate ρ η tZ) x π t = 0 ∧ 0 < mxi2 β κ σ ϑ x π t := by
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hpos := trap_mult_pos hβ hβ1 hκ hσ hϑ hρ hη hF hopt.2.1 (fun t => (hK t).1)
    (fun t => (hK t).2.1) (fun t => (hK t).2.2.1) (fun t => (hK t).2.2.2) hlim t ht
  exact ⟨(mul_eq_zero.mp (hK t).2.2.2).resolve_left hpos.ne', hpos⟩

/-- Galí (2015), eq. (48), p. 151; Cochrane (2023), p. 479: hence the optimum obeys the zero-rate
recursion (48) on the whole shock interval (the hypothesis `h48` of Galí's algorithm). -/
theorem optimal_h48 {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ) (ht : t ≤ tZ) :
    (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)) := by
  refine backStep_of_rate hσ.ne' (rn := natRate ρ η tZ) (hopt.1 t).1 ?_
  rw [(optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t ht).1, natRate_of_le ht]
  ring

/-- Cochrane (2023), p. 479, Galí (2015), p. 152: **the lift-off date is at least the end of the
shock**: if the optimal rate is positive at `t_C + 1`, then `t_Z ≤ t_C`. -/
theorem liftoff_ge {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hlift : 0 < impliedRate σ (natRate ρ η tZ) x π (tC + 1)) : tZ ≤ tC := by
  by_contra h
  push Not at h
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt (tC + 1) (by omega)).1
  linarith

/-- Galí (2015), pp. 149–152; Cochrane (2023), p. 479: the same in terms of multipliers: if
`ξ₁, ξ₂` solve (35)–(36) on `[0, t_C + 1]` along the optimum and `ξ₂,t_C+1 = 0` (Galí's lift-off
condition), then `t_Z ≤ t_C`. -/
theorem liftoff_ge_mult {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (hξ2 : ξ2 (tC + 1) = 0) : tZ ≤ tC := by
  by_contra h
  push Not at h
  have e := (mult_unique h50 (tC + 1) le_rfl).2
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt (tC + 1) (by omega)).2
  rw [← e, hξ2] at this
  exact lt_irrefl _ this

/-- Cochrane (2023), p. 479, Galí (2015), p. 152: equivalently, **every date with a positive
optimal interest rate lies after the shock**: `0 < i_t ⇒ t_Z < t`. -/
theorem liftoff_after_shock {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ)
    (ht : 0 < impliedRate σ (natRate ρ η tZ) x π t) : tZ < t := by
  by_contra h
  push Not at h
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t h).1
  linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **commitment inflation never exceeds
the depth of the shock**: at the optimum `π_t ≤ η` at every date (admissible parameters), a discrete
maximum principle for the KKT system (`pi_le_bound`). -/
theorem optimal_pi_le {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (n : ℕ) : π n ≤ η := by
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hd : ∀ t, gap σ x π t ≤ η ∨ lam κ ϑ x π t ≤ 0 := by
    intro t
    rcases (hK t).2.2.1.eq_or_lt with h | h
    · right
      have hl : 0 ≤ lag ξ2 t := by
        cases t with
        | zero => simp
        | succ n => simpa using (hK n).2.2.1
      have hk : κ * lam κ ϑ x π t ≤ 0 := by
        rw [hmult t, ← h]
        have := div_nonneg hl hβ.le
        have := (hK (t + 1)).2.2.1
        linarith
      by_contra hc
      push Not at hc
      linarith [mul_pos hκ hc]
    · left
      have hr := (mul_eq_zero.mp (hK t).2.2.2).resolve_left h.ne'
      rw [impliedRate_eq_gap] at hr
      unfold natRate at hr
      split_ifs at hr <;> linarith
  have hI : lamI κ ϑ x π ≤ 0 := by
    have := lamI_mult hκ.ne' (hK 0).1 (hK 0).2.1
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc, (hK 0).2.2.1]
  exact pi_le_bound hβ hβ1 hκ hσ hϑ hη (fun t => (hF t).1) hd hI
    (tendsto_pi_sq hβ hϑ hopt.2.1) n

/-! ## Hypothesis-free versions of the commitment theorems -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2: `comm_gt_disc` without the
assumptions `t_Z ≤ t_C` and (48): for the commitment optimum, with (35)–(36) on `[0, t_C + 1]`,
(49), (46), `ξ₂,t_C+1 = 0`, the closed form after lift-off, `ξ₂,t_C ≥ 0` and `ξ₁,t_C+1 > 0`,
output and inflation exceed discretion at every date. -/
theorem comm_gt_disc_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) :
    discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t :=
  comm_gt_disc hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ t

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 152: `comm_loss_lt` without the
assumptions `t_Z ≤ t_C` and (48): discretion has strictly larger loss than the optimum. -/
theorem comm_loss_lt_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) :=
  comm_loss_lt hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ hopt

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.glide_path`): `comm_promise` without the
assumptions `t_Z ≤ t_C` and (48): the optimum's date-0 inflation equals that of exactly one
Werning-family member, whose promise `c` is strictly positive. -/
theorem comm_promise_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    (∃! c, (wState β κ σ η tZ c 0).2 = π 0) ∧
      ∀ c, (wState β κ σ η tZ c 0).2 = π 0 → 0 < c :=
  comm_promise hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ

/-- Cochrane (2023), §20.2.4, p. 479: `comm_gt_disc_of_state` without the assumptions
`t_Z ≤ t_C` and (48): for the optimum with lift-off at `t_C + 1` (positive rate there), (49), and
a weakly positive nonzero lift-off state, output and inflation exceed discretion on `[0, t_C]`. -/
theorem comm_gt_disc_of_state_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hlift : 0 < impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) : discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t :=
  comm_gt_disc_of_state hβ hκ hσ hρ (liftoff_ge hβ hβ1 hκ hσ hϑ hρ.le hη hopt hlift)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 hx hp hs t ht

/-- Galí (2015), p. 152, **verification theorem for an arbitrary guess `t_C`** (no `t_Z ≤ t_C`):
if the candidate keeps the rate at zero on `[0, t_C]` (whatever the natural rate there),
satisfies (35)–(36) on `[0, t_C + 1]`, (46), `ξ₂,t_C+1 = 0`, the closed form (42)–(43) after
lift-off, `ξ₂ ≥ 0` on `[0, t_C]` and `i ≥ 0` at every date after `t_C`, then it is the unique
optimum, satisfies the KKT system, and necessarily `t_Z ≤ t_C`: the guess in Galí's algorithm
is without loss of generality. -/
theorem algorithm_verification_gen {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hzero : ∀ t, t ≤ tC →
      (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hrate : ∀ k, 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1 + k)) :
    tZ ≤ tC ∧ KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧
      Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 :=
    fun t ht => backStep_nkpc_rate hσ.ne' (hzero t ht) (by rw [hrn, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrt : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      exact hrate k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨feasible_of_rate hσ fun t => ⟨hnkpc t, hrt t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1' : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2' : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1', l2', x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2', x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have hopt := kkt_optimal hβ hβ1 hσ hϑ hK hb hs
  exact ⟨liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ hη hopt h50 hξ2, hK, hopt,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 152: `comm_loss_lt_alg` for an
arbitrary guess `t_C` (no `t_Z ≤ t_C`): under the hypotheses of `algorithm_verification_gen` and
`ξ₁,t_C+1 > 0`, the candidate is the optimum, `t_Z ≤ t_C`, and discretion is strictly worse. -/
theorem comm_loss_lt_alg_gen {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hzero : ∀ t, t ≤ tC →
      (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hrate : ∀ k, 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1 + k))
    (hξ : 0 < ξ1 (tC + 1)) :
    tZ ≤ tC ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  obtain ⟨htC, -, hopt, -⟩ := algorithm_verification_gen hβ hβ1 hκ hσ hϑ hρ.le hη hzero h50 h46
    hξ2 hpost hsign hrate
  refine ⟨htC, hopt, comm_loss_lt_opt hβ hβ1 hκ hσ hϑ hρ hη hopt h50 (fun t h1 h2 => ?_) h46
    hξ2 (fun k => ⟨(hpost k).1, (hpost k).2.1⟩) (hsign tC le_rfl) hξ⟩
  rw [hzero t h2, natRate_of_lt h1]

end Cochrane.ZeroBound.LiftoffTiming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The commitment optimum: existence, uniqueness and the shape of the zero-rate spell

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4 (pp. 478–480),
compared with Galí (2015), §5.4.2 (pp. 148–152), in the model of `LinksGaliWoodford`.
Continues `LiftoffTiming` (the zero bound binds on the whole shock, `t_C ≥ t_Z`).

* Existence (`exists_optimal`, `optimal_exists_unique`): paths are coded in the Hilbert space
  `ℓ²(ℕ ⊕ ℕ)` (`PathSpace`, `enc`, `decX`, `decP`) so that the loss is the squared norm
  (`loss_dec`); the feasible codes form a nonempty closed convex set (`feasSet_closed`,
  `feasSet_convex`), and the minimal-norm element is the optimum (`ρ ≥ 0`, any `t_Z`).
* No re-binding (`no_return`): once the zero-bound multiplier vanishes after the shock it stays
  zero (a maximum principle for `(σκ/ϑ − 1)π`).
* Finite lift-off (`exists_slack_after`, `ρ > 0`): binding forever would drive inflation to the
  deflation steady state (`two_root`) and the multipliers would explode or turn negative.
* Galí's closed form after lift-off is necessary (`post_form`).
* `optimal_binding`, `optimal_liftoff`: there is `t_C ≥ t_Z` with `i = 0` exactly on `[0, t_C]`
  and `i > 0` afterwards; `optimal_algorithm_form`: the optimum satisfies every hypothesis of
  Galí's algorithm; `commitment_characterisation`: existence, uniqueness and this shape.
* `ρ = 0` (`liftoff_rates`, `rho_zero_structure`): either the rate is zero at every date, or
  `σκ ≠ ϑ` and the shape above holds; at `σκ = ϑ` the rate never lifts off
  (`rho_zero_unit_ratio`, `rho_zero_no_liftoff`, exact instance `rho_zero_instance`), so `ρ > 0`
  in `commitment_characterisation` is necessary.
-/

namespace Cochrane.ZeroBound.LiftoffStructure

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford Cochrane.ZeroBound.LiftoffTiming

/-! ## Auxiliary algebra -/

/-- Cochrane (2023), p. 479: `comb` is homogeneous in the sequence. -/
theorem comb_smul (β a c : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => c * u n) t = c * comb β a u t := by
  unfold comb; ring

/-- Cochrane (2023), p. 479: `comb` shifts by constants. -/
theorem comb_add_const (β a c : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => u n + c) t = comb β a u t + c := by
  unfold comb; ring

/-- Galí (2015), (15), p. 136; Cochrane (2023), p. 479: `δ` solves
`βδ² − (1 + β + κ²/ϑ)δ + 1 = 0`. -/
theorem del_root {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    β * del β κ ϑ ^ 2 - (1 + β + κ ^ 2 / ϑ) * del β κ ϑ + 1 = 0 := by
  have hg := gam_pos (κ := κ) hβ hϑ
  have hq := del_quad (κ := κ) hβ hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ hϑ
  have h : gam β κ ϑ * (β * del β κ ϑ ^ 2 - (1 + β + κ ^ 2 / ϑ) * del β κ ϑ + 1) = 0 := by
    have e : gam β κ ϑ * (1 + β + κ ^ 2 / ϑ) = 1 := by
      have : gam β κ ϑ * (1 + β + κ ^ 2 / ϑ) = gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) / ϑ := by
        field_simp
      rw [this, hm, div_self hϑ.ne']
    linear_combination hq - del β κ ϑ * e
  exact (mul_eq_zero.mp h).resolve_left hg.ne'

/-- Cochrane (2023), §5.7.1 and p. 479: **the bounded solutions of a two-root recursion**. If
`β u_{n+2} − (1+β+k) u_{n+1} + u_n = 0` from `n₀` on, `0 < μ < 1` is the stable root
(`βμ² − (1+β+k)μ + 1 = 0`) and `β^n u_n² → 0`, then `u_{n+1} = μ u_n` from `n₀` on (the other
root `1/(βμ)` violates the growth bound). -/
theorem two_root {β k μ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hq : β * μ ^ 2 - (1 + β + k) * μ + 1 = 0) {u : ℕ → ℝ} {n0 : ℕ}
    (hrec : ∀ n, n0 ≤ n → β * u (n + 2) - (1 + β + k) * u (n + 1) + u n = 0)
    (hT : Tendsto (fun n => β ^ n * u n ^ 2) atTop (𝓝 0)) :
    ∀ n, n0 ≤ n → u (n + 1) = μ * u n := by
  set f : ℕ → ℝ := fun n => u (n + 1) - μ * u n with hf
  have hμinv : μ * (1 / μ) = 1 := by field_simp
  have hk : 1 + β + k = β * μ + 1 / μ := by
    have e : β * μ + 1 / μ - (1 + β + k) = (β * μ ^ 2 - (1 + β + k) * μ + 1) * (1 / μ) := by
      linear_combination ((1 + β + k) - β * μ) * hμinv
    rw [hq, zero_mul] at e
    linarith
  have hstep : ∀ n, n0 ≤ n → f (n + 1) = f n / (β * μ) := by
    intro n hn
    have h := hrec n hn
    simp only [hf]
    rw [hk] at h
    rw [eq_div_iff (by positivity)]
    linear_combination μ * h + u (n + 1) * hμinv
  have hfT : Tendsto (fun n => β ^ n * f n ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => β ^ (n + 1) * u (n + 1) ^ 2) atTop (𝓝 0) :=
      hT.comp (tendsto_add_atTop_nat 1)
    have h2 := ((h1.const_mul (2 / β)).add (hT.const_mul 2))
    rw [mul_zero, mul_zero, add_zero] at h2
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
    simp only [hf]
    have hp : 0 < β ^ n := pow_pos hβ0 n
    have e1 : 2 / β * (β ^ (n + 1) * u (n + 1) ^ 2) = 2 * (β ^ n * u (n + 1) ^ 2) := by
      rw [pow_succ]; field_simp
    rw [e1]
    have : (u (n + 1) - μ * u n) ^ 2 ≤ 2 * u (n + 1) ^ 2 + 2 * u n ^ 2 := by
      have : μ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (u (n + 1) + μ * u n), sq_nonneg (u n)]
    nlinarith
  intro n hn
  by_contra hne
  have hfn : f n ≠ 0 := fun h => hne (by simp only [hf] at h; linarith)
  have hpow : ∀ j, f (n + j) = f n * (1 / (β * μ)) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show n + (j + 1) = (n + j) + 1 by omega, hstep _ (by omega), ih, pow_succ]
      ring
  have hc : 0 < β ^ n * f n ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hfT).2 _ hc)
  have key := hN (n + N) (by omega)
  rw [hpow N] at key
  have hb : 1 ≤ (1 / (β * μ ^ 2)) ^ N := one_le_pow₀ (by
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_lt_mul_of_pos_left hμ1 hμ0])
  have hq2 : β * (1 / (β * μ)) ^ 2 = 1 / (β * μ ^ 2) := by field_simp
  have e : β ^ (n + N) * (f n * (1 / (β * μ)) ^ N) ^ 2 =
      β ^ n * f n ^ 2 * (1 / (β * μ ^ 2)) ^ N := by
    rw [← hq2]
    ring
  rw [e] at key
  nlinarith

/-! ## No return to the zero bound after a slack date following the shock -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 150: **once the zero-bound multiplier
vanishes after the shock it stays zero** (no re-binding): if `(x, π)` is optimal, `t_Z < s` and
`ξ₂,s = 0`, then `ξ₂,t = 0` for every `t ≥ s` (any `ρ ≥ 0`). A maximum principle for
`v = (σκ/ϑ − 1)π` gives `v ≤ ρ` after `s`, hence the multiplier combination is `≤ 0` there, and
`mult_zero_right` applies. -/
theorem no_return {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) {s : ℕ} (hs : tZ < s)
    (h0 : mxi2 β κ σ ϑ x π s = 0) : ∀ t, s ≤ t → mxi2 β κ σ ϑ x π t = 0 := by
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hopt.2.1
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hpos : ∀ t, 0 ≤ ξ2 t := fun t => (hK t).2.2.1
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [hmult t, ht]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc]
  have hbind : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t = -ρ := by
    intro t ht h
    have := (mul_eq_zero.mp (hK t).2.2.2).resolve_left h.ne'
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  have hfeas : ∀ t, tZ < t → -ρ ≤ gap σ x π t := by
    intro t ht
    have := rate_nonneg hσ hF t
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hgl : ∀ t, gap σ x π t = r * lam κ ϑ x π t - (r - 1) * π (t + 1) :=
    fun t => gap_lam hκ.ne' hϑ.ne' x π t
  set v : ℕ → ℝ := fun n => (r - 1) * π n with hv
  have hvs : ∀ t, tZ < t → ξ2 t = 0 → v (t + 1) ≤ ρ := by
    intro t ht h
    have h1 := hfeas t ht
    have h2 := hslack t h
    rw [hgl t] at h1
    have : r * lam κ ϑ x π t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le h2
    simp only [hv]
    linarith
  have hvc : ∀ t, tZ < t → 0 < ξ2 t → comb β (σ / κ) v t ≤ ρ := by
    intro t ht h
    rw [comb_smul, ← gap_comb hκ.ne' (hN t) (hN (t + 1)), hbind t ht h]
    have : 0 ≤ r * ρ := mul_nonneg hr0.le hρ
    nlinarith
  have hvT : Tendsto (fun n => β ^ n * v n ^ 2) atTop (𝓝 0) := by
    have := hS.const_mul ((r - 1) ^ 2)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hv]
    ring
  have hsk : 0 < σ / κ := by positivity
  have hV : ∀ n, s + 1 ≤ n → v n ≤ ρ := by
    intro m hm
    by_contra hcon
    push Not at hcon
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.Icc (s + 1) m) v
      ⟨m, Finset.mem_Icc.mpr ⟨hm, le_rfl⟩⟩
    rw [Finset.mem_Icc] at hm0
    have hpm : ρ < v m0 := lt_of_lt_of_le hcon (hmax m (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩))
    have hne : m0 ≠ s + 1 := by
      rintro rfl
      linarith [hvs s hs h0]
    obtain ⟨j, rfl⟩ : ∃ j, m0 = j + 1 := ⟨m0 - 1, by omega⟩
    have hj : v j ≤ v (j + 1) := hmax j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbj : ∀ n, tZ < n → ρ < v (n + 1) → 0 < ξ2 n := by
      intro n hn hvn
      rcases (hpos n).eq_or_lt with h | h
      · linarith [hvs n hn h.symm]
      · exact h
    have hup : v (j + 1) < v (j + 2) :=
      comb_up hβ hsk (hvc j (by omega) (hbj j (by omega) hpm)) hpm hj
    refine not_tendsto_sq hβ hβ1.le hρ (n0 := j + 1) (fun n hn hb _ => ?_) (hpm.trans hup)
      hup hvT
    exact comb_step hβ hsk (hvc n (by omega) (hbj n (by omega) hb)) hb.le
  have hlam : ∀ t, s ≤ t → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hbind t (by omega) h
      rw [hgl t] at hg
      have := hV (t + 1) (by omega)
      simp only [hv] at this
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc
      push Not at hc
      linarith [mul_pos hr0 hc]
  have hcc : 1 + 1 / β < 1 + 1 / β + κ / (β * σ) := by
    have : 0 < κ / (β * σ) := by positivity
    linarith
  exact mult_zero_right hβ hcc hpos h0 (fun t ht => by
    rw [← hmult t]
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (hlam t ht.le)) hlim

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152: **the rate lifts off in finite time**
(`ρ > 0`): some date after the shock has a zero multiplier. If the bound bound forever, inflation
would converge to the deflation steady state `−ρ` (`two_root`), the multiplier combination would
stay below `−ρ/2`, and the multipliers would either explode (violating `β^t ξ₂,t → 0`) or turn
negative. -/
theorem exists_slack_after {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hopt.2.1
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hpos : ∀ t, 0 ≤ ξ2 t := fun t => (hK t).2.2.1
  have hb : ∀ t, tZ < t → 0 < ξ2 t :=
    fun t ht => lt_of_le_of_ne (hpos t) (Ne.symm (hcon t ht))
  have hgap : ∀ t, tZ < t → gap σ x π t = -ρ := by
    intro t ht
    have := (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hb t ht).ne'
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  set e : ℕ → ℝ := fun n => π n + ρ with he
  have hab : σ / κ * (κ / σ) = 1 := by field_simp
  have hrec : ∀ n, tZ + 1 ≤ n → β * e (n + 2) - (1 + β + κ / σ) * e (n + 1) + e n = 0 := by
    intro n hn
    have h := hgap n (by omega)
    rw [gap_comb hκ.ne' (hN n) (hN (n + 1))] at h
    unfold comb at h
    simp only [he]
    linear_combination (-(κ / σ)) * h +
      ((π (n + 1) - π n) + β * (π (n + 1) - π (n + 2))) * hab
  have heT : Tendsto (fun n => β ^ n * e n ^ 2) atTop (𝓝 0) := by
    have h2 := (hS.const_mul 2).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul (2 * ρ ^ 2))
    rw [mul_zero, mul_zero, add_zero] at h2
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
    simp only [he]
    have hp : 0 ≤ β ^ n := pow_nonneg hβ.le n
    have : (π n + ρ) ^ 2 ≤ 2 * π n ^ 2 + 2 * ρ ^ 2 := by nlinarith [sq_nonneg (π n - ρ)]
    nlinarith
  have hks : 0 < κ * σ := by positivity
  set μ := del β κ (κ * σ) with hμ
  have hμ0 : 0 < μ := del_pos hβ hks
  have hμ1 : μ < 1 := (del_lt_one_iff hβ hβ1 hks).mpr hκ.ne'
  have hq : β * μ ^ 2 - (1 + β + κ / σ) * μ + 1 = 0 := by
    have := del_root (κ := κ) hβ hβ1 hks
    rw [show κ ^ 2 / (κ * σ) = κ / σ by field_simp] at this
    exact this
  have hgeo := two_root hβ hβ1 hμ0 hμ1 hq hrec heT
  have hpow : ∀ j, e (tZ + 1 + j) = μ ^ j * e (tZ + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tZ + 1 + (j + 1) = (tZ + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hlamf : ∀ t, tZ < t → lam κ ϑ x π t = -ρ + (r - 1) / r * e (t + 1) := by
    intro t ht
    have h := gap_lam (σ := σ) hκ.ne' hϑ.ne' x π t
    rw [hgap t ht] at h
    simp only [he]
    field_simp
    linarith
  have hT : Tendsto (fun t => (r - 1) / r * e (t + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℕ => μ ^ (t - tZ)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).comp (tendsto_sub_atTop_nat tZ)
    have h2 := h1.const_mul ((r - 1) / r * e (tZ + 1))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop tZ] with t ht
    rw [show t + 1 = tZ + 1 + (t - tZ) by omega, hpow]
    ring
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 (ρ / 2) (by linarith))
  set T0 := max N1 (tZ + 1) with hT0
  have hlamT : ∀ t, T0 ≤ t → κ * lam κ ϑ x π t < -(κ * ρ / 2) := by
    intro t ht
    rw [hlamf t (by omega)]
    have := hN1 t (by omega)
    nlinarith
  have hcc : 0 < κ / (β * σ) := by positivity
  by_cases hA : ∃ t0, T0 ≤ t0 ∧ ξ2 t0 < ξ2 (t0 + 1)
  · obtain ⟨t0, ht0, hlt⟩ := hA
    refine not_tendsto_lin hβ hpos (n0 := t0) (fun n hn _ _ => ?_)
      (lt_of_le_of_lt (hpos t0) hlt) hlt hlim
    have h1 := hlamT (n + 1) (by omega)
    rw [hmult (n + 1)] at h1
    simp only [lag_succ] at h1
    rw [show n + 1 + 1 = n + 2 by omega] at h1
    have h2 : 0 ≤ κ / (β * σ) * ξ2 (n + 1) := mul_nonneg hcc.le (hpos _)
    have e1 : (ξ2 (n + 1) - ξ2 n) / β = 1 / β * ξ2 (n + 1) - ξ2 n / β := by ring
    rw [e1]
    nlinarith
  · push Not at hA
    have hdec : ∀ t, T0 ≤ t → ξ2 (t + 1) - ξ2 t ≤ -(β * κ * ρ / 2) := by
      intro t ht
      have h1 := hlamT (t + 1) (by omega)
      rw [hmult (t + 1)] at h1
      simp only [lag_succ] at h1
      have h3 := hA (t + 1) (by omega)
      have h2 : 0 ≤ κ / (β * σ) * ξ2 (t + 1) := mul_nonneg hcc.le (hpos _)
      have h4 : (ξ2 (t + 1) - ξ2 t) / β < -(κ * ρ / 2) := by
        have e1 : (ξ2 (t + 1) - ξ2 t) / β = 1 / β * ξ2 (t + 1) - ξ2 t / β := by ring
        rw [e1]
        nlinarith
      rw [div_lt_iff₀ hβ] at h4
      nlinarith
    have hlin : ∀ k : ℕ, ξ2 (T0 + k) ≤ ξ2 T0 - k * (β * κ * ρ / 2) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hdec (T0 + k) (by omega)
        rw [show T0 + (k + 1) = T0 + k + 1 by omega]
        push_cast
        linarith
    have hd : 0 < β * κ * ρ / 2 := by positivity
    obtain ⟨k, hk⟩ := exists_nat_gt (ξ2 T0 / (β * κ * ρ / 2))
    have h1 := hlin k
    have h2 : ξ2 T0 < k * (β * κ * ρ / 2) := by rwa [div_lt_iff₀ hd] at hk
    linarith [hpos (T0 + k)]

/-! ## Galí's closed form after lift-off is necessary -/

/-- Galí (2015), eqs. (37)–(43), pp. 149–150; Cochrane (2023), p. 479: **after the last binding
date `t_B` the optimum follows Galí's closed form**: if the multipliers vanish from `t_B + 1` on,
then `ξ₁,t_B+1+k = δᵏ ξ`, `π_{t_B+2+k} = (1 − δ)δᵏ ξ`, `x_{t_B+2+k} = κδ^{k+1}ξ/ϑ` with
`ξ = ξ₁,t_B+1` (the unstable root is excluded by the finite loss, `two_root`). -/
theorem post_form {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) {tB : ℕ}
    (hz : ∀ t, tB + 1 ≤ t → mxi2 β κ σ ϑ x π t = 0) (k : ℕ) :
    x (tB + k + 2) = postX β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) k ∧
      π (tB + k + 2) = postPi β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) k ∧
      mxi1 β κ σ ϑ x π (tB + k + 2) = postXi β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) (k + 1) ∧
      mxi2 β κ σ ϑ x π (tB + k + 2) = 0 := by
  have h35 := foc35_mult β κ σ ϑ x π
  have h36 := foc36_mult β κ σ ϑ x π
  set ξ1 := mxi1 β κ σ ϑ x π with hξ1
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hopt.1 t).1
  have hx : ∀ n, tB + 1 ≤ n → x (n + 1) = κ / ϑ * ξ1 (n + 1) := by
    intro n hn
    have h := h36 (n + 1)
    unfold FOC36 at h
    rw [lag_succ, hz n hn, hz (n + 1) (by omega)] at h
    simp only [zero_div, sub_zero, add_zero] at h
    field_simp
    linarith
  have hp : ∀ n, tB + 1 ≤ n → π (n + 1) = ξ1 n - ξ1 (n + 1) := by
    intro n hn
    have h := h35 (n + 1)
    unfold FOC35 at h
    rw [lag_succ, lag_succ, hz n hn] at h
    simp only [zero_div, sub_zero] at h
    linarith
  have hrec : ∀ n, tB + 1 ≤ n →
      β * ξ1 (n + 2) - (1 + β + κ ^ 2 / ϑ) * ξ1 (n + 1) + ξ1 n = 0 := by
    intro n hn
    have h := hN (n + 1)
    unfold NKPC at h
    rw [hp n hn, hp (n + 1) (by omega), hx n hn] at h
    rw [show n + 1 + 1 = n + 2 by omega] at h
    linear_combination h
  have hT : Tendsto (fun n => β ^ n * ξ1 n ^ 2) atTop (𝓝 0) := by
    have hxs : Summable (fun n => β ^ n * x n ^ 2) := by
      refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
        (hopt.2.1.div_const ϑ)
      unfold lossTerm
      rw [le_div_iff₀ hϑ]
      have : 0 ≤ β ^ t * π t ^ 2 * ϑ := by positivity
      nlinarith
    have h1 := hxs.tendsto_atTop_zero.const_mul ((ϑ / κ) ^ 2)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (tB + 2)] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hx m (by omega)]
    field_simp
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have hgeo := two_root hβ hβ1 hδ0 hδ1 (del_root hβ hβ1 hϑ) hrec hT
  have hpow : ∀ j, ξ1 (tB + 1 + j) = del β κ ϑ ^ j * ξ1 (tB + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tB + 1 + (j + 1) = (tB + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  have e1 : ξ1 (tB + k + 2) = del β κ ϑ ^ (k + 1) * ξ1 (tB + 1) := by
    rw [show tB + k + 2 = tB + 1 + (k + 1) by omega, hpow]
  have e0 : ξ1 (tB + k + 1) = del β κ ϑ ^ k * ξ1 (tB + 1) := by
    rw [show tB + k + 1 = tB + 1 + k by omega, hpow]
  refine ⟨?_, ?_, ?_, hz _ (by omega)⟩
  · rw [show tB + k + 2 = (tB + k + 1) + 1 by omega, hx _ (by omega),
      show tB + k + 1 + 1 = tB + k + 2 by omega, e1]
    unfold postX
    ring
  · rw [show tB + k + 2 = (tB + k + 1) + 1 by omega, hp _ (by omega),
      show tB + k + 1 + 1 = tB + k + 2 by omega, e1, e0]
    unfold postPi
    ring
  · rw [e1]
    unfold postXi
    ring

/-! ## The zero-rate spell is an initial interval -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, Galí (2015), §5.4.2 (`ρ, η > 0`): **the binding set
of the optimum**. There is `t_B ≥ t_Z` such that the zero-bound multiplier is positive
exactly on `[0, t_B]` (so `i = 0` there), and the interest rate is strictly positive at every
date after `t_B + 1`. -/
theorem optimal_binding {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tB, tZ ≤ tB ∧ (∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t) ∧
      (∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0) ∧
      (∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tB + 1 < t → 0 < impliedRate σ (natRate ρ η tZ) x π t) := by
  classical
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hex := exists_slack_after hβ hβ1 hκ hσ hϑ hρ hopt
  set s0 := Nat.find hex with hs0
  obtain ⟨hs0Z, hs0z⟩ := Nat.find_spec hex
  obtain ⟨tB, htB⟩ : ∃ tB, s0 = tB + 1 := ⟨s0 - 1, by omega⟩
  have htBZ : tZ ≤ tB := by omega
  have hposB : ∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ.le hη hopt t h).2
    · have hmin := Nat.find_min hex (show t < Nat.find hex by omega)
      push Not at hmin
      exact lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hmin h))
  have hzero : ∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0 := by
    intro t ht
    have := no_return hβ hβ1 hκ hσ hϑ hρ.le hopt hs0Z hs0z
    exact this t (by omega)
  have hrate0 : ∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hposB t ht).ne'
  refine ⟨tB, htBZ, hposB, hzero, hrate0, fun t ht => ?_⟩
  have hpost := post_form hβ hβ1 hκ hϑ hopt (tB := tB) fun t ht => hzero t (by omega)
  set ξ := mxi1 β κ σ ϑ x π (tB + 1) with hξ
  set δ := del β κ ϑ with hδ
  have hδ0 : 0 < δ := del_pos hβ hϑ
  have hδ1 : δ < 1 := (del_lt_one_iff hβ hβ1 hϑ).mpr hκ.ne'
  set A := (1 - δ) * (1 - σ * κ / ϑ) * ξ with hA
  have hrk : ∀ k, impliedRate σ (natRate ρ η tZ) x π (tB + k + 2) = ρ + A * δ ^ (k + 1) := by
    intro k
    rw [post_rate hϑ.ne' htBZ (fun k => (hpost k).1) (fun k => (hpost k).2.1) k, hA]
    ring
  have hr1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) < ρ + A := by
    have h36 := foc36_mult β κ σ ϑ x π (tB + 1)
    unfold FOC36 at h36
    rw [lag_succ, hzero (tB + 1) (by omega), ← hξ] at h36
    have hx1 : x (tB + 1) = (κ * ξ + mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      rw [eq_div_iff hϑ.ne']
      linarith
    have hp := hposB tB le_rfl
    have e1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) =
        ρ + A - σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      unfold impliedRate
      rw [natRate_of_lt (by omega), show tB + 1 + 1 = tB + 0 + 2 by omega, (hpost 0).1,
        (hpost 0).2.1, hx1, hA]
      unfold postX postPi
      field_simp
      ring
    rw [e1]
    have : 0 < σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by positivity
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
  rw [hrk k]
  by_contra hc
  push Not at hc
  have hprev : A * δ ^ k < -ρ := by
    by_contra h'
    push Not at h'
    have e : A * δ ^ (k + 1) = A * δ ^ k * δ := by ring
    rw [e] at hc
    rcases le_or_gt 0 (A * δ ^ k) with h0 | h0
    · have : 0 ≤ A * δ ^ k * δ := mul_nonneg h0 hδ0.le
      linarith
    · have : -ρ * δ ≤ A * δ ^ k * δ := mul_le_mul_of_nonneg_right h' hδ0.le
      nlinarith
  rcases k with _ | j
  · have := rate_nonneg hσ hF (tB + 1)
    simp only [pow_zero, mul_one] at hprev
    linarith
  · have := rate_nonneg hσ hF (tB + j + 2)
    rw [hrk j] at this
    rw [show j + 1 = j + 1 from rfl] at hprev
    linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152 (`ρ, η > 0`): **the zero-rate spell
is an initial interval**: there is `t_C ≥ t_Z` with `i_t = 0` exactly for `t ≤ t_C` and
`i_t > 0` for every `t > t_C` (no re-binding after lift-off). -/
theorem optimal_liftoff {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      ∀ t, tC < t → 0 < impliedRate σ (natRate ρ η tZ) x π t := by
  obtain ⟨tB, htB, -, -, h0, hpos⟩ := optimal_binding hβ hβ1 hκ hσ hϑ hρ hη hopt
  rcases (rate_nonneg hσ hopt.1 (tB + 1)).eq_or_lt with h | h
  · refine ⟨tB + 1, by omega, fun t ht => ?_, fun t ht => hpos t ht⟩
    rcases ht.eq_or_lt with rfl | ht'
    · exact h.symm
    · exact h0 t (by omega)
  · refine ⟨tB, htB, h0, fun t ht => ?_⟩
    rcases (show tB + 1 = t ∨ tB + 1 < t by omega) with rfl | ht'
    · exact h
    · exact hpos t ht'

/-- Galí (2015), p. 152; Cochrane (2023), p. 479 (`ρ, η > 0`): **the optimum is always found by
Galí's algorithm**: with the multipliers `mult` and `t_C` the last binding date, every hypothesis
of `algorithm_verification` holds — `t_Z ≤ t_C`, (48), (49), (35)–(36) on `[0, t_C + 1]`, (46),
`ξ₂,t_C+1 = 0`, the closed form (42)–(43) after lift-off, `ξ₂ ≥ 0` on `[0, t_C]`, and
`i ≥ 0` at `t_C + 1`, `t_C + 2`. -/
theorem optimal_algorithm_form {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tC, tZ ≤ tC ∧
      (∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) ∧
      (∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) ∧
      (∀ t, t ≤ tC + 1 → FOC35 β σ π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t ∧
        FOC36 β κ ϑ x (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t) ∧
      NKPC β κ x π (tC + 1) ∧ mxi2 β κ σ ϑ x π (tC + 1) = 0 ∧
      (∀ k, x (tC + k + 2) = postX β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) k ∧
        π (tC + k + 2) = postPi β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) k ∧
        mxi1 β κ σ ϑ x π (tC + k + 2) = postXi β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) (k + 1) ∧
        mxi2 β κ σ ϑ x π (tC + k + 2) = 0) ∧
      (∀ t, t ≤ tC → 0 ≤ mxi2 β κ σ ϑ x π t) ∧
      0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1) ∧
      0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2) := by
  obtain ⟨tB, htB, hpos, hz, h0, -⟩ := optimal_binding hβ hβ1 hκ hσ hϑ hρ hη hopt
  refine ⟨tB, htB, optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt, fun t h1 h2 => ?_,
    fun t _ => ⟨foc35_mult β κ σ ϑ x π t, foc36_mult β κ σ ϑ x π t⟩, (hopt.1 _).1,
    hz _ (by omega), post_form hβ hβ1 hκ hϑ hopt fun t ht => hz t (by omega),
    fun t ht => (hpos t ht).le, rate_nonneg hσ hopt.1 _, rate_nonneg hσ hopt.1 _⟩
  refine backStep_of_rate hσ.ne' (rn := natRate ρ η tZ) (hopt.1 t).1 ?_
  rw [h0 t h2, natRate_of_lt h1]
  ring

/-! ## Existence of the commitment optimum -/

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the Hilbert space `ℓ²(ℕ ⊕ ℕ)` of weighted
paths, whose squared norm is the loss (`loss_dec`). -/
abbrev PathSpace : Type := lp (fun _ : ℕ ⊕ ℕ => ℝ) 2

/-- Galí (2015), p. 148: the inflation path coded by `z`, `π_t = z(inl t)/√β^t`. -/
noncomputable def decP (β : ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) : ℝ := z (Sum.inl t) / Real.sqrt β ^ t

/-- Galí (2015), p. 148: the output-gap path coded by `z`, `x_t = z(inr t)/(√β^t √ϑ)`. -/
noncomputable def decX (β ϑ : ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) : ℝ :=
  z (Sum.inr t) / (Real.sqrt β ^ t * Real.sqrt ϑ)

/-- Galí (2015), p. 148: the code of a path `(x, π)`. -/
noncomputable def enc (β ϑ : ℝ) (x π : ℕ → ℝ) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun t => Real.sqrt β ^ t * π t) (fun t => Real.sqrt β ^ t * Real.sqrt ϑ * x t)

/-- Galí (2015), p. 148: `(√β^t)² = β^t`. -/
theorem sqrt_pow_sq {β : ℝ} (hβ : 0 ≤ β) (t : ℕ) : (Real.sqrt β ^ t) ^ 2 = β ^ t := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hβ]

/-- Galí (2015), p. 148: decoding a code returns the inflation path. -/
theorem decP_enc {β : ℝ} (hβ : 0 < β) (ϑ : ℝ) (x π : ℕ → ℝ) : decP β (enc β ϑ x π) = π := by
  funext t
  have : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  simp only [decP, enc, Sum.elim_inl]
  field_simp

/-- Galí (2015), p. 148: decoding a code returns the output-gap path. -/
theorem decX_enc {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (x π : ℕ → ℝ) :
    decX β ϑ (enc β ϑ x π) = x := by
  funext t
  have : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  have : Real.sqrt ϑ ≠ 0 := (Real.sqrt_pos.mpr hϑ).ne'
  simp only [decX, enc, Sum.elim_inr]
  field_simp

/-- Galí (2015), p. 148: the loss term of a decoded path is `z(inl t)² + z(inr t)²`. -/
theorem lossTerm_dec {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ (decX β ϑ z) (decP β z) t = z (Sum.inl t) ^ 2 + z (Sum.inr t) ^ 2 := by
  have h1 : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  have h2 : Real.sqrt ϑ ≠ 0 := (Real.sqrt_pos.mpr hϑ).ne'
  unfold lossTerm decX decP
  rw [div_pow, div_pow, mul_pow, sqrt_pow_sq hβ.le, Real.sq_sqrt hϑ.le]
  have : β ^ t ≠ 0 := pow_ne_zero _ hβ.ne'
  field_simp

/-- Galí (2015), p. 148: the squares of an `ℓ²` element are summable. -/
theorem summable_sq (z : PathSpace) : Summable (fun i => z i ^ 2) := by
  have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 (lp.memℓp z)
  refine h.congr fun i => ?_
  rw [Real.norm_eq_abs, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two, sq_abs]

/-- Galí (2015), p. 148: `‖z‖² = ∑ z_i²`. -/
theorem norm_sq_eq (z : PathSpace) : ‖z‖ ^ 2 = ∑' i, z i ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) z
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two] at h
  rw [h]
  congr 1
  funext i
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: **the loss of a decoded path is the squared
norm**, and it is finite. -/
theorem loss_dec {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (z : PathSpace) :
    Summable (lossTerm β ϑ (decX β ϑ z) (decP β z)) ∧
      loss β ϑ (decX β ϑ z) (decP β z) = ‖z‖ ^ 2 := by
  set f : ℕ ⊕ ℕ → ℝ := fun i => z i ^ 2 with hf
  have hs : Summable f := summable_sq z
  have h1 : Summable (f ∘ Sum.inl) := hs.comp_injective Sum.inl_injective
  have h2 : Summable (f ∘ Sum.inr) := hs.comp_injective Sum.inr_injective
  have e : lossTerm β ϑ (decX β ϑ z) (decP β z) = fun t => (f ∘ Sum.inl) t + (f ∘ Sum.inr) t :=
    funext fun t => lossTerm_dec hβ hϑ z t
  refine ⟨by rw [e]; exact h1.add h2, ?_⟩
  have h3 : ∑' i, f i = ∑' t, (f ∘ Sum.inl) t + ∑' t, (f ∘ Sum.inr) t := Summable.tsum_sum h1 h2
  unfold loss
  rw [e, h1.tsum_add h2, norm_sq_eq, ← h3]

/-- Galí (2015), p. 148: a path with finite loss has an `ℓ²` code. -/
theorem memℓp_enc {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) : Memℓp (enc β ϑ x π) 2 := by
  refine (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 ?_
  have e : (fun i => ‖enc β ϑ x π i‖ ^ (2 : ENNReal).toReal) = fun i => enc β ϑ x π i ^ 2 := by
    funext i
    rw [Real.norm_eq_abs, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      sq_abs]
  rw [e]
  refine Summable.sum _ ?_ ?_
  · refine Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hs
    simp only [Function.comp, enc, Sum.elim_inl, lossTerm]
    rw [mul_pow, sqrt_pow_sq hβ.le]
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    nlinarith
  · refine Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hs
    simp only [Function.comp, enc, Sum.elim_inr, lossTerm]
    rw [mul_pow, mul_pow, sqrt_pow_sq hβ.le, Real.sq_sqrt hϑ.le]
    have : 0 ≤ β ^ t * π t ^ 2 := by positivity
    nlinarith

/-- Galí (2015), p. 149: a convex combination of feasible paths is feasible. -/
theorem feasible_convex {β κ σ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {rn x π y q : ℕ → ℝ} (hab : a + b = 1)
    (h1 : Feasible β κ σ rn x π) (h2 : Feasible β κ σ rn y q) :
    Feasible β κ σ rn (fun t => a * x t + b * y t) (fun t => a * π t + b * q t) := by
  intro t
  obtain ⟨n1, u1⟩ := h1 t
  obtain ⟨n2, u2⟩ := h2 t
  unfold NKPC at n1 n2 ⊢
  unfold ups1 at u1 u2 ⊢
  simp only
  refine ⟨by rw [n1, n2]; ring, ?_⟩
  have e : a * x (t + 1) + b * y (t + 1) + (a * π (t + 1) + b * q (t + 1) + rn t) / σ =
      a * (x (t + 1) + (π (t + 1) + rn t) / σ) + b * (y (t + 1) + (q (t + 1) + rn t) / σ) := by
    linear_combination (-(rn t / σ)) * hab
  rw [e]
  have := mul_le_mul_of_nonneg_left u1 ha
  have := mul_le_mul_of_nonneg_left u2 hb
  linarith

/-- Galí (2015), p. 149: the codes of feasible paths. -/
def feasSet (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : Set PathSpace :=
  {z | Feasible β κ σ rn (decX β ϑ z) (decP β z)}

/-- Galí (2015), p. 148: evaluation at a coordinate is continuous on `ℓ²`. -/
theorem coord_continuous (i : ℕ ⊕ ℕ) : Continuous fun z : PathSpace => z i :=
  (continuous_apply i).comp lp.uniformContinuous_coe.continuous

/-- Galí (2015), p. 149: the feasible set (Phillips curve and `i ≥ 0` at every date) is closed. -/
theorem feasSet_closed (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : IsClosed (feasSet β κ σ ϑ rn) := by
  have hP : ∀ t, Continuous fun z : PathSpace => decP β z t := fun t => by
    simp only [decP]; exact (coord_continuous _).div_const _
  have hX : ∀ t, Continuous fun z : PathSpace => decX β ϑ z t := fun t => by
    simp only [decX]; exact (coord_continuous _).div_const _
  have e : feasSet β κ σ ϑ rn = ⋂ t, ({z : PathSpace |
      decP β z t = β * decP β z (t + 1) + κ * decX β ϑ z t} ∩
      {z | decX β ϑ z t ≤ decX β ϑ z (t + 1) + (decP β z (t + 1) + rn t) / σ}) := by
    ext z
    simp only [feasSet, Feasible, NKPC, ups1, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun t =>
    (isClosed_eq (hP t) (((hP _).const_mul β).add ((hX t).const_mul κ))).inter
      (isClosed_le (hX t) ((hX _).add (((hP _).add continuous_const).div_const σ)))

/-- Galí (2015), p. 149: the feasible set is convex. -/
theorem feasSet_convex (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : Convex ℝ (feasSet β κ σ ϑ rn) := by
  intro z hz w hw a b ha hb hab
  have eP : decP β ⇑(a • z + b • w) = fun t => a * decP β z t + b * decP β w t := by
    funext t
    simp only [decP, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eX : decX β ϑ ⇑(a • z + b • w) = fun t => a * decX β ϑ z t + b * decX β ϑ w t := by
    funext t
    simp only [decX, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change Feasible β κ σ rn (decX β ϑ ⇑(a • z + b • w)) (decP β ⇑(a • z + b • w))
  rw [eP, eX]
  exact feasible_convex ha hb hab hz hw

/-- Galí (2015), p. 148; Cochrane (2023), §20.2.4, p. 479: **existence of the commitment
optimum** for any natural-rate path for which some feasible path has finite loss: the loss is the
squared norm of the code in `ℓ²`, the feasible codes form a nonempty closed convex set, and the
element of minimal norm (projection of `0`, `exists_norm_eq_iInf_of_complete_convex`) is
optimal. -/
theorem exists_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hne : ∃ y q, Feasible β κ σ rn y q ∧ Summable (lossTerm β ϑ y q)) :
    ∃ x π, Optimal β κ σ ϑ rn x π := by
  obtain ⟨y0, q0, hF0, hS0⟩ := hne
  have hmem : ∀ y q, Feasible β κ σ rn y q → ∀ hs : Summable (lossTerm β ϑ y q),
      (⟨enc β ϑ y q, memℓp_enc hβ hϑ hs⟩ : PathSpace) ∈ feasSet β κ σ ϑ rn := by
    intro y q hy hs
    change Feasible β κ σ rn (decX β ϑ (enc β ϑ y q)) (decP β (enc β ϑ y q))
    rw [decX_enc hβ hϑ, decP_enc hβ]
    exact hy
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex ⟨_, hmem y0 q0 hF0 hS0⟩
    (feasSet_closed β κ σ ϑ rn).isComplete (feasSet_convex β κ σ ϑ rn) 0
  obtain ⟨hsv, hlv⟩ := loss_dec hβ hϑ v
  refine ⟨decX β ϑ v, decP β v, hvK, hsv, fun y q hy hsy => ?_⟩
  set w : PathSpace := ⟨enc β ϑ y q, memℓp_enc hβ hϑ hsy⟩ with hw
  have hwK := hmem y q hy hsy
  have hle : ‖v‖ ≤ ‖w‖ := by
    have h1 : ‖(0 : PathSpace) - v‖ ≤ ‖(0 : PathSpace) - w‖ := by
      rw [hv]
      exact ciInf_le ⟨0, by rintro _ ⟨u, rfl⟩; exact norm_nonneg _⟩
        (⟨w, hwK⟩ : feasSet β κ σ ϑ rn)
    simpa only [zero_sub, norm_neg] using h1
  obtain ⟨-, hlw⟩ := loss_dec hβ hϑ w
  have e1 : decX β ϑ ⇑w = y := decX_enc hβ hϑ y q
  have e2 : decP β ⇑w = q := decP_enc hβ ϑ y q
  rw [e1, e2] at hlw
  rw [hlv, hlw]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-! ## The commitment optimum, fully characterised -/

/-- Galí (2015), §5.4.2, Cochrane (2023), §20.2.4: **the commitment optimum exists and is
unique** for all `β > 0`, `σ, ϑ > 0`, any `κ, η`, `ρ ≥ 0` and `t_Z` (discretion is feasible
with finite loss). -/
theorem optimal_exists_unique {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (hρ : 0 ≤ ρ) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      ∀ y q, Optimal β κ σ ϑ (natRate ρ η tZ) y q → y = x ∧ q = π := by
  obtain ⟨hF, hS⟩ := disc_feasible_summable (κ := κ) (ϑ := ϑ) (η := η) hσ hρ tZ
  obtain ⟨x, π, hopt⟩ := exists_optimal (κ := κ) (σ := σ) hβ hϑ ⟨_, _, hF, hS⟩
  exact ⟨x, π, hopt, fun y q h => optimal_unique hβ hϑ h hopt⟩

/-- Cochrane (2023), §20.2.4, pp. 478–480, and Galí (2015), §5.4.2, pp. 148–152: **the
commitment optimum, fully characterised** (`β ∈ (0,1)`, `κ, σ, ϑ, ρ, η > 0`, any `t_Z`): it
exists, it is unique, and there is a lift-off date `t_C ≥ t_Z` such that the interest rate is
zero exactly on `[0, t_C]` and strictly positive at every later date. Moreover it satisfies all
the conditions of Galí's algorithm (`optimal_algorithm_form`). -/
theorem commitment_characterisation {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ y q, Optimal β κ σ ϑ (natRate ρ η tZ) y q → y = x ∧ q = π) ∧
      ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
        ∀ t, tC < t → 0 < impliedRate σ (natRate ρ η tZ) x π t := by
  obtain ⟨x, π, hopt, huniq⟩ := optimal_exists_unique (κ := κ) (η := η) hβ hσ hϑ hρ.le tZ
  exact ⟨x, π, hopt, huniq, optimal_liftoff hβ hβ1 hκ hσ hϑ hρ hη hopt⟩

/-! ## A zero post-shock natural rate (`ρ = 0`) -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152 (`ρ ≥ 0`): **rates after a finite
lift-off**. If some date after the shock has a zero multiplier, then with `t_B` the last binding
date (`t_Z ≤ t_B`, `ξ₂ > 0` exactly on `[0, t_B]`, `i = 0` there) and
`A = (1 − δ)(1 − σκ/ϑ) ξ₁,t_B+1`: `i_{t_B+1} < ρ + A` and `i_{t_B+2+k} = ρ + A δ^{k+1}`. -/
theorem liftoff_rates {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hex : ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0) :
    ∃ tB, tZ ≤ tB ∧ (∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t) ∧
      (∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0) ∧
      (∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      impliedRate σ (natRate ρ η tZ) x π (tB + 1) <
        ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) ∧
      ∀ k, impliedRate σ (natRate ρ η tZ) x π (tB + k + 2) =
        ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) *
          del β κ ϑ ^ (k + 1) := by
  classical
  obtain ⟨⟨-, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set s0 := Nat.find hex with hs0
  obtain ⟨hs0Z, hs0z⟩ := Nat.find_spec hex
  obtain ⟨tB, htB⟩ : ∃ tB, s0 = tB + 1 := ⟨s0 - 1, by omega⟩
  have htBZ : tZ ≤ tB := by omega
  have hposB : ∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t h).2
    · have hmin := Nat.find_min hex (show t < Nat.find hex by omega)
      push Not at hmin
      exact lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hmin h))
  have hzero : ∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0 := by
    intro t ht
    exact no_return hβ hβ1 hκ hσ hϑ hρ hopt hs0Z hs0z t (by omega)
  have hrate0 : ∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hposB t ht).ne'
  have hpost := post_form hβ hβ1 hκ hϑ hopt (tB := tB) fun t ht => hzero t (by omega)
  set ξ := mxi1 β κ σ ϑ x π (tB + 1) with hξ
  set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  refine ⟨tB, htBZ, hposB, hzero, hrate0, ?_, fun k => ?_⟩
  · have h36 := foc36_mult β κ σ ϑ x π (tB + 1)
    unfold FOC36 at h36
    rw [lag_succ, hzero (tB + 1) (by omega), ← hξ] at h36
    have hx1 : x (tB + 1) = (κ * ξ + mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      rw [eq_div_iff hϑ.ne']
      linarith
    have hp := hposB tB le_rfl
    have e1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) =
        ρ + A - σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      unfold impliedRate
      rw [natRate_of_lt (by omega), show tB + 1 + 1 = tB + 0 + 2 by omega, (hpost 0).1,
        (hpost 0).2.1, hx1, hA]
      unfold postX postPi
      field_simp
      ring
    rw [e1]
    have : 0 < σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by positivity
    linarith
  · rw [post_rate hϑ.ne' htBZ (fun k => (hpost k).1) (fun k => (hpost k).2.1) k, hξ]
    ring

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **the binding set when the
post-shock natural rate is zero** (`ρ = 0`; the optimum exists and is unique,
`optimal_exists_unique`). The zero bound still binds on the whole shock and never re-binds after
a lift-off (`optimal_trap_binds`, `no_return`), and exactly one of the following holds: either
the rate is zero at every date, or `σκ ≠ ϑ` and there is `t_C ≥ t_Z` with `i = 0` exactly on
`[0, t_C]` and `i > 0` afterwards. -/
theorem rho_zero_structure {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    (∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) ∨
      (σ * κ ≠ ϑ ∧ ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
        ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t) := by
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  by_cases hex : ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0
  · right
    obtain ⟨tB, htB, -, -, h0, h1, hk⟩ := liftoff_rates hβ hβ1 hκ hσ hϑ le_rfl hη hopt hex
    set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) with hA
    have hδ0 : 0 < del β κ ϑ := del_pos hβ hϑ
    have hApos : 0 < A := by
      have := rate_nonneg hσ hF (tB + 1)
      linarith
    have hr : σ * κ ≠ ϑ := by
      intro h
      rw [hA, h, div_self hϑ.ne', sub_self, mul_zero, zero_mul] at hApos
      exact lt_irrefl _ hApos
    have hpos : ∀ t, tB + 1 < t → 0 < impliedRate σ (natRate 0 η tZ) x π t := by
      intro t ht
      obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
      rw [hk k, zero_add]
      positivity
    refine ⟨hr, ?_⟩
    rcases (rate_nonneg hσ hF (tB + 1)).eq_or_lt with h | h
    · refine ⟨tB + 1, by omega, fun t ht => ?_, fun t ht => hpos t ht⟩
      rcases ht.eq_or_lt with rfl | ht'
      · exact h.symm
      · exact h0 t (by omega)
    · refine ⟨tB, htB, h0, fun t ht => ?_⟩
      rcases (show tB + 1 = t ∨ tB + 1 < t by omega) with rfl | ht'
      · exact h
      · exact hpos t ht'
  · left
    push Not at hex
    intro t
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ le_rfl hη hopt t h).1
    · exact (mul_eq_zero.mp (hK t).2.2.2).resolve_left
        (lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hex t h))).ne'

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152: **with `ρ = 0` and `σκ = ϑ` the
optimal interest rate is zero at every date** — the rate never lifts off. -/
theorem rho_zero_unit_ratio {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ = ϑ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) (t : ℕ) :
    impliedRate σ (natRate 0 η tZ) x π t = 0 := by
  rcases rho_zero_structure hβ hβ1 hκ hσ hϑ hη hopt with h | ⟨h, -⟩
  · exact h t
  · exact absurd hr h

/-- Cochrane (2023), §20.2.4 and Galí (2015), §5.4.2: **the hypothesis `ρ > 0` of
`commitment_characterisation` cannot be dropped**: for every `β ∈ (0,1)`, `κ, σ, η > 0`, `t_Z`,
with `ρ = 0` and `ϑ = σκ` the optimum exists and is unique, but no `t_C` has `i > 0` after it. -/
theorem rho_zero_no_liftoff {β κ σ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hη : 0 < η) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ (σ * κ) (natRate 0 η tZ) x π ∧
      (∀ y q, Optimal β κ σ (σ * κ) (natRate 0 η tZ) y q → y = x ∧ q = π) ∧
      ¬ ∃ tC, ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t := by
  have hϑ : 0 < σ * κ := by positivity
  obtain ⟨x, π, hopt, hu⟩ := optimal_exists_unique (κ := κ) (η := η) hβ hσ hϑ le_rfl tZ
  refine ⟨x, π, hopt, hu, fun ⟨tC, h⟩ => ?_⟩
  have := h (tC + 1) (by omega)
  rw [rho_zero_unit_ratio hβ hβ1 hκ hσ hϑ hη rfl hopt] at this
  exact lt_irrefl _ this

/-- Cochrane (2023), §20.2.4, Galí (2015), §5.4.2: an exact instance (`β = 1/2`,
`κ = σ = ϑ = 1`, `η = 1`, `ρ = 0`, `t_Z = 0`): the unique optimum keeps the rate at zero forever. -/
theorem rho_zero_instance :
    ∃ x π, Optimal (1 / 2) 1 1 1 (natRate 0 1 0) x π ∧
      (∀ y q, Optimal (1 / 2) 1 1 1 (natRate 0 1 0) y q → y = x ∧ q = π) ∧
      ∀ t, impliedRate 1 (natRate 0 1 0) x π t = 0 := by
  obtain ⟨x, π, hopt, hu⟩ := optimal_exists_unique (β := (1 : ℝ) / 2) (κ := 1) (σ := 1)
    (ϑ := 1) (η := 1) (by norm_num) one_pos one_pos le_rfl 0
  exact ⟨x, π, hopt, hu, rho_zero_unit_ratio (by norm_num) (by norm_num) one_pos one_pos
    one_pos one_pos (by norm_num) hopt⟩

end Cochrane.ZeroBound.LiftoffStructure

set_option linter.style.longLine false
#print axioms Cochrane.ZeroBound.SchurStable
#print axioms Cochrane.ZeroBound.discQ
#print axioms Cochrane.ZeroBound.root₁
#print axioms Cochrane.ZeroBound.root₂
#print axioms Cochrane.ZeroBound.root_sum
#print axioms Cochrane.ZeroBound.root_prod
#print axioms Cochrane.ZeroBound.root_eq
#print axioms Cochrane.ZeroBound.normSq_root_of_neg
#print axioms Cochrane.ZeroBound.norm_root_of_nonneg
#print axioms Cochrane.ZeroBound.schurStable_iff_roots
#print axioms Cochrane.ZeroBound.chSeq
#print axioms Cochrane.ZeroBound.convSeq
#print axioms Cochrane.ZeroBound.convSeq_rec
#print axioms Cochrane.ZeroBound.chSeq_eq_convSeq
#print axioms Cochrane.ZeroBound.norm_convSeq_le
#print axioms Cochrane.ZeroBound.abs_chSeq_le
#print axioms Cochrane.ZeroBound.tendsto_chSeq
#print axioms Cochrane.ZeroBound.tr2
#print axioms Cochrane.ZeroBound.det2
#print axioms Cochrane.ZeroBound.tr2_eq_trace
#print axioms Cochrane.ZeroBound.det2_eq_det
#print axioms Cochrane.ZeroBound.sq_eq_cayleyHamilton
#print axioms Cochrane.ZeroBound.pow_succ_eq
#print axioms Cochrane.ZeroBound.abs_pow_entry_le
#print axioms Cochrane.ZeroBound.tendsto_pow_entry
#print axioms Cochrane.ZeroBound.BoundedSeq
#print axioms Cochrane.ZeroBound.homogeneous_iterate
#print axioms Cochrane.ZeroBound.abs_mulVec_le
#print axioms Cochrane.ZeroBound.homogeneous_eq_zero
#print axioms Cochrane.ZeroBound.eq_root_of_eq
#print axioms Cochrane.ZeroBound.exists_eigenvector
#print axioms Cochrane.ZeroBound.exists_bounded_homogeneous
#print axioms Cochrane.ZeroBound.ExpectationSystem
#print axioms Cochrane.ZeroBound.ExpectationSystem.mk
#print axioms Cochrane.ZeroBound.ExpectationSystem.E
#print axioms Cochrane.ZeroBound.ExpectationSystem.const
#print axioms Cochrane.ZeroBound.ExpectationSystem.mono
#print axioms Cochrane.ZeroBound.ExpectationSystem.tower
#print axioms Cochrane.ZeroBound.ExpectationSystem.known
#print axioms Cochrane.ZeroBound.perfectForesight
#print axioms Cochrane.ZeroBound.BoundedProc
#print axioms Cochrane.ZeroBound.BoundedVec
#print axioms Cochrane.ZeroBound.ExpectationSystem.Adapted
#print axioms Cochrane.ZeroBound.ExpectationSystem.IsAR1
#print axioms Cochrane.ZeroBound.ExpectationSystem.E_neg
#print axioms Cochrane.ZeroBound.ExpectationSystem.E_smul
#print axioms Cochrane.ZeroBound.ExpectationSystem.E_E_self
#print axioms Cochrane.ZeroBound.ExpectationSystem.abs_E_le
#print axioms Cochrane.ZeroBound.ExpectationSystem.bounded_E
#print axioms Cochrane.ZeroBound.ExpectationSystem.ar1_iterate
#print axioms Cochrane.ZeroBound.ExpectationSystem.forward_iterate
#print axioms Cochrane.ZeroBound.ExpectationSystem.forward_unique
#print axioms Cochrane.ZeroBound.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.ZeroBound.ExpectationSystem.E_tsum
#print axioms Cochrane.ZeroBound.ExpectationSystem.forwardSeries
#print axioms Cochrane.ZeroBound.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.ZeroBound.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.ZeroBound.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.ZeroBound.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.ZeroBound.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.ZeroBound.ExpectationSystem.PullOut
#print axioms Cochrane.ZeroBound.ExpectationSystem.Solves
#print axioms Cochrane.ZeroBound.ExpectationSystem.AdaptedVec
#print axioms Cochrane.ZeroBound.ExpectationSystem.system_iterate
#print axioms Cochrane.ZeroBound.ExpectationSystem.system_unique
#print axioms Cochrane.ZeroBound.ExpectationSystem.system_not_unique
#print axioms Cochrane.ZeroBound.ExpectationSystem.Determinate
#print axioms Cochrane.ZeroBound.ExpectationSystem.determinate_iff
#print axioms Cochrane.ZeroBound.perfectForesight_pullOut
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.ZeroBound.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.ZeroBound.ForwardSolution.Solves
#print axioms Cochrane.ZeroBound.ForwardSolution.E_of_known
#print axioms Cochrane.ZeroBound.ForwardSolution.solves_adapted
#print axioms Cochrane.ZeroBound.ForwardSolution.iterate_A15
#print axioms Cochrane.ZeroBound.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.ZeroBound.ForwardSolution.summable_A16
#print axioms Cochrane.ZeroBound.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.ZeroBound.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.ZeroBound.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.ZeroBound.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.ZeroBound.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.ZeroBound.ForwardSolution.ScalarEq
#print axioms Cochrane.ZeroBound.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.ZeroBound.ForwardSolution.scalarSol
#print axioms Cochrane.ZeroBound.ForwardSolution.scalarSol_apply
#print axioms Cochrane.ZeroBound.ForwardSolution.scalarEq_iff
#print axioms Cochrane.ZeroBound.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.ZeroBound.ForwardSolution.scalar_homog
#print axioms Cochrane.ZeroBound.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.ZeroBound.ForwardSolution.sunspotFamily
#print axioms Cochrane.ZeroBound.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.ZeroBound.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.ZeroBound.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.ZeroBound.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.ZeroBound.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.ZeroBound.ForwardSolution.homog_solves
#print axioms Cochrane.ZeroBound.ForwardSolution.solves_add_homog
#print axioms Cochrane.ZeroBound.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.ZeroBound.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.ZeroBound.ForwardSolution.existsUnique_iff
#print axioms Cochrane.ZeroBound.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.ZeroBound.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.ZeroBound.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.ZeroBound.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.ZeroBound.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.ZeroBound.ForwardSolution.ar1_decay
#print axioms Cochrane.ZeroBound.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.ZeroBound.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.ZeroBound.ForwardSolution.predetermined_restriction
#print axioms Cochrane.ZeroBound.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.ZeroBound.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.ZeroBound.ForwardSolution.summable_geom_mul
#print axioms Cochrane.ZeroBound.ForwardSolution.abel_tsum
#print axioms Cochrane.ZeroBound.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.ZeroBound.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.ZeroBound.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.ZeroBound.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.ZeroBound.ForwardSolution.E_tsum_dom
#print axioms Cochrane.ZeroBound.GlobalDynamics.orbit_monotone_of_le
#print axioms Cochrane.ZeroBound.GlobalDynamics.orbit_antitone_of_ge
#print axioms Cochrane.ZeroBound.GlobalDynamics.fixed_of_tendsto
#print axioms Cochrane.ZeroBound.GlobalDynamics.monotone_orbit_atTop_or_fixed
#print axioms Cochrane.ZeroBound.GlobalDynamics.antitone_orbit_atBot_or_fixed
#print axioms Cochrane.ZeroBound.GlobalDynamics.sign_near_of_deriv_pos
#print axioms Cochrane.ZeroBound.GlobalDynamics.repelling_of_one_lt_abs_deriv
#print axioms Cochrane.ZeroBound.GlobalDynamics.attracting_of_abs_deriv_lt_one
#print axioms Cochrane.ZeroBound.GlobalDynamics.oppCost
#print axioms Cochrane.ZeroBound.GlobalDynamics.oppCost_zero
#print axioms Cochrane.ZeroBound.GlobalDynamics.discount
#print axioms Cochrane.ZeroBound.GlobalDynamics.ricardian_step
#print axioms Cochrane.ZeroBound.GlobalDynamics.ricardian_discounted
#print axioms Cochrane.ZeroBound.GlobalDynamics.ricardian_tvc
#print axioms Cochrane.ZeroBound.GlobalDynamics.ricardian_tvc_fails_of_alpha_zero
#print axioms Cochrane.ZeroBound.GlobalDynamics.eq45_iff_fisher
#print axioms Cochrane.ZeroBound.GlobalDynamics.IsPath45
#print axioms Cochrane.ZeroBound.GlobalDynamics.IsPath46
#print axioms Cochrane.ZeroBound.GlobalDynamics.fisher_path_iff_eq45
#print axioms Cochrane.ZeroBound.GlobalDynamics.isPath45_iff_isPath46_of_const
#print axioms Cochrane.ZeroBound.GlobalDynamics.map46
#print axioms Cochrane.ZeroBound.GlobalDynamics.orbit46
#print axioms Cochrane.ZeroBound.GlobalDynamics.orbit46_succ
#print axioms Cochrane.ZeroBound.GlobalDynamics.orbit46_isPath
#print axioms Cochrane.ZeroBound.GlobalDynamics.isPath46_eq_orbit
#print axioms Cochrane.ZeroBound.GlobalDynamics.bound44Term
#print axioms Cochrane.ZeroBound.GlobalDynamics.bound44_summable
#print axioms Cochrane.ZeroBound.GlobalDynamics.continuum_pf_equilibria
#print axioms Cochrane.ZeroBound.GlobalDynamics.target_isFixed
#print axioms Cochrane.ZeroBound.GlobalDynamics.hasDerivAt_map46
#print axioms Cochrane.ZeroBound.GlobalDynamics.taylorCoeff_eq_slope
#print axioms Cochrane.ZeroBound.GlobalDynamics.second_steady_state
#print axioms Cochrane.ZeroBound.GlobalDynamics.map46_step_down
#print axioms Cochrane.ZeroBound.GlobalDynamics.self_fulfilling_deflation46
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation46_strictAnti
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation46_eventually_deflation
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflationary_steady_state_indeterminate
#print axioms Cochrane.ZeroBound.GlobalDynamics.inflation_unbounded46
#print axioms Cochrane.ZeroBound.GlobalDynamics.inflation_unbounded_iff
#print axioms Cochrane.ZeroBound.GlobalDynamics.phiCE
#print axioms Cochrane.ZeroBound.GlobalDynamics.e6_counterexample
#print axioms Cochrane.ZeroBound.GlobalDynamics.target_locally_repelling
#print axioms Cochrane.ZeroBound.GlobalDynamics.target_locally_unique
#print axioms Cochrane.ZeroBound.GlobalDynamics.ratio_strictMonoOn
#print axioms Cochrane.ZeroBound.GlobalDynamics.steady_state45_iff
#print axioms Cochrane.ZeroBound.GlobalDynamics.isPath45_unique
#print axioms Cochrane.ZeroBound.GlobalDynamics.step45_down
#print axioms Cochrane.ZeroBound.GlobalDynamics.self_fulfilling_deflation45
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation45_exists
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation45_bound44
#print axioms Cochrane.ZeroBound.GlobalDynamics.step45_down_gen
#print axioms Cochrane.ZeroBound.GlobalDynamics.self_fulfilling_deflation45_gen
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation45_exists_gen
#print axioms Cochrane.ZeroBound.GlobalDynamics.antitone_lam_gives_gen
#print axioms Cochrane.ZeroBound.GlobalDynamics.phiCE45
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation45_counterexample
#print axioms Cochrane.ZeroBound.GlobalDynamics.bound44_summable_path
#print axioms Cochrane.ZeroBound.GlobalDynamics.deflation45_bound44_gen
#print axioms Cochrane.ZeroBound.ZLBPeg.lam1
#print axioms Cochrane.ZeroBound.ZLBPeg.lam2
#print axioms Cochrane.ZeroBound.ZLBPeg.disc_pos
#print axioms Cochrane.ZeroBound.ZLBPeg.lam_add
#print axioms Cochrane.ZeroBound.ZLBPeg.lam_mul
#print axioms Cochrane.ZeroBound.ZLBPeg.lam_root
#print axioms Cochrane.ZeroBound.ZLBPeg.lam2_le_lam1
#print axioms Cochrane.ZeroBound.ZLBPeg.one_lt_lam1
#print axioms Cochrane.ZeroBound.ZLBPeg.lam2_lt_one
#print axioms Cochrane.ZeroBound.ZLBPeg.lam2_pos
#print axioms Cochrane.ZeroBound.ZLBPeg.pegMatrix
#print axioms Cochrane.ZeroBound.ZLBPeg.pegForcing
#print axioms Cochrane.ZeroBound.ZLBPeg.pegMatrix_tr_det
#print axioms Cochrane.ZeroBound.ZLBPeg.pegMatrix_roots
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_not_schurStable
#print axioms Cochrane.ZeroBound.ZLBPeg.PegEq
#print axioms Cochrane.ZeroBound.ZLBPeg.E_affine2
#print axioms Cochrane.ZeroBound.ZLBPeg.pegEq_iff_solves
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_not_determinate
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_steady
#print axioms Cochrane.ZeroBound.ZLBPeg.pegQ
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_q_step
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_slaving
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_pi_rec
#print axioms Cochrane.ZeroBound.ZLBPeg.pegEq_of_slaving
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_equilibrium_iff
#print axioms Cochrane.ZeroBound.ZLBPeg.pegPi
#print axioms Cochrane.ZeroBound.ZLBPeg.pegX
#print axioms Cochrane.ZeroBound.ZLBPeg.E_pegPi
#print axioms Cochrane.ZeroBound.ZLBPeg.pegEq_of_sunspot
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_equilibrium_char
#print axioms Cochrane.ZeroBound.ZLBPeg.sunspot_equilibrium
#print axioms Cochrane.ZeroBound.ZLBPeg.sunspot_innovation
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_expected_converges
#print axioms Cochrane.ZeroBound.ZLBPeg.peg_continuum
#print axioms Cochrane.ZeroBound.ZLBPeg.coin_sunspot_equilibrium
#print axioms Cochrane.ZeroBound.ZLBPeg.Valuation
#print axioms Cochrane.ZeroBound.ZLBPeg.valuation_sum0
#print axioms Cochrane.ZeroBound.ZLBPeg.valuation_sum
#print axioms Cochrane.ZeroBound.ZLBPeg.fiscalP
#print axioms Cochrane.ZeroBound.ZLBPeg.valuation_pins
#print axioms Cochrane.ZeroBound.ZLBPeg.fiscal_selects
#print axioms Cochrane.ZeroBound.ZLBPeg.fiscal_unexpected_inflation
#print axioms Cochrane.ZeroBound.ZLBPeg.fiscal_stable
#print axioms Cochrane.ZeroBound.ZLBPeg.fiscal_quiet
#print axioms Cochrane.ZeroBound.ZLBPeg.deflation_iff_fiscal_contraction
#print axioms Cochrane.ZeroBound.ZLBRule.rule
#print axioms Cochrane.ZeroBound.ZLBRule.fmap
#print axioms Cochrane.ZeroBound.ZLBRule.kink
#print axioms Cochrane.ZeroBound.ZLBRule.slopeR
#print axioms Cochrane.ZeroBound.ZLBRule.ZLBEq
#print axioms Cochrane.ZeroBound.ZLBRule.eq20_2_iff
#print axioms Cochrane.ZeroBound.ZLBRule.eq20_2_iff_map
#print axioms Cochrane.ZeroBound.ZLBRule.kink_iff
#print axioms Cochrane.ZeroBound.ZLBRule.eq20_3
#print axioms Cochrane.ZeroBound.ZLBRule.eq20_4
#print axioms Cochrane.ZeroBound.ZLBRule.kink_fig203
#print axioms Cochrane.ZeroBound.ZLBRule.e1_printed_threshold_false
#print axioms Cochrane.ZeroBound.ZLBRule.fmap_continuous
#print axioms Cochrane.ZeroBound.ZLBRule.fmap_strictMono
#print axioms Cochrane.ZeroBound.ZLBRule.fmap_surjective
#print axioms Cochrane.ZeroBound.ZLBRule.hasDerivAt_fmap_left
#print axioms Cochrane.ZeroBound.ZLBRule.hasDerivAt_fmap_right
#print axioms Cochrane.ZeroBound.ZLBRule.slope_left_lt_one
#print axioms Cochrane.ZeroBound.ZLBRule.slope_right_gt_one_iff
#print axioms Cochrane.ZeroBound.ZLBRule.active_of_kink_le
#print axioms Cochrane.ZeroBound.ZLBRule.zlb_branch_contraction
#print axioms Cochrane.ZeroBound.ZLBRule.active_branch_expansion
#print axioms Cochrane.ZeroBound.ZLBRule.fixed_iff
#print axioms Cochrane.ZeroBound.ZLBRule.upper_on_branch_iff
#print axioms Cochrane.ZeroBound.ZLBRule.steady_exists_iff
#print axioms Cochrane.ZeroBound.ZLBRule.both_steady
#print axioms Cochrane.ZeroBound.ZLBRule.fixed_u_zero
#print axioms Cochrane.ZeroBound.ZLBRule.steady_states_pushed_in
#print axioms Cochrane.ZeroBound.ZLBRule.lower_attracting
#print axioms Cochrane.ZeroBound.ZLBRule.upper_repelling
#print axioms Cochrane.ZeroBound.ZLBRule.fig203_no_steady_state
#print axioms Cochrane.ZeroBound.ZLBRule.fig203_printed_steady_states_false
#print axioms Cochrane.ZeroBound.ZLBRule.active_affine
#print axioms Cochrane.ZeroBound.ZLBRule.kink_mem
#print axioms Cochrane.ZeroBound.ZLBRule.orbit_above
#print axioms Cochrane.ZeroBound.ZLBRule.orbit_below_tendsto_zero
#print axioms Cochrane.ZeroBound.ZLBRule.orbit_below_rate_zero
#print axioms Cochrane.ZeroBound.ZLBRule.bounded_orbits_eq
#print axioms Cochrane.ZeroBound.ZLBRule.locally_bounded_unique
#print axioms Cochrane.ZeroBound.ZLBRule.shiftE
#print axioms Cochrane.ZeroBound.ZLBRule.locally_bounded_unique_E
#print axioms Cochrane.ZeroBound.ZLBRule.backward_unique
#print axioms Cochrane.ZeroBound.ZLBRule.backward_exists
#print axioms Cochrane.ZeroBound.ZLBRule.uFig
#print axioms Cochrane.ZeroBound.ZLBRule.fig203_selection
#print axioms Cochrane.ZeroBound.ZLBRule.fig203_early_liftoff
#print axioms Cochrane.ZeroBound.FutureSelection.bounded_of_rec
#print axioms Cochrane.ZeroBound.FutureSelection.switch_scalar
#print axioms Cochrane.ZeroBound.FutureSelection.RuleEq
#print axioms Cochrane.ZeroBound.FutureSelection.ruleEq_iff
#print axioms Cochrane.ZeroBound.FutureSelection.future_selection
#print axioms Cochrane.ZeroBound.FutureSelection.passive_forever_not_unique
#print axioms Cochrane.ZeroBound.FutureSelection.zero_coefficient_not_unique
#print axioms Cochrane.ZeroBound.FutureSelection.LeeperEq
#print axioms Cochrane.ZeroBound.FutureSelection.leeper_debt_eq
#print axioms Cochrane.ZeroBound.FutureSelection.fiscal_switch_selects
#print axioms Cochrane.ZeroBound.FutureSelection.fiscal_switch_unexpected_inflation
#print axioms Cochrane.ZeroBound.FutureSelection.no_switch_fiscal_irrelevant
#print axioms Cochrane.ZeroBound.FutureSelection.fiscal_switch_example
#print axioms Cochrane.ZeroBound.Gabaix.gabaixMatrix
#print axioms Cochrane.ZeroBound.Gabaix.gabaixForcing
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_tr_det
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_charpoly_one
#print axioms Cochrane.ZeroBound.Gabaix.GabaixEq
#print axioms Cochrane.ZeroBound.Gabaix.gabaixEq_iff_solves
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_schur_iff
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_roots_iff
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_determinate_iff
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_steady
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_unique
#print axioms Cochrane.ZeroBound.Gabaix.gabaix_not_unique
#print axioms Cochrane.ZeroBound.Gabaix.rational_IS_indeterminate
#print axioms Cochrane.ZeroBound.Gabaix.frictionless_limit_indeterminate
#print axioms Cochrane.ZeroBound.Gabaix.determinate_bounded_away
#print axioms Cochrane.ZeroBound.Gabaix.boundary_root_one
#print axioms Cochrane.ZeroBound.Gabaix.e8_half_not_necessary
#print axioms Cochrane.ZeroBound.Gabaix.e8_half_not_necessary'
#print axioms Cochrane.ZeroBound.Gabaix.e8_not_sufficient
#print axioms Cochrane.ZeroBound.Covid.priceLevel
#print axioms Cochrane.ZeroBound.Covid.helicopter_exact
#print axioms Cochrane.ZeroBound.Covid.helicopter_thirty
#print axioms Cochrane.ZeroBound.Covid.priceRatio
#print axioms Cochrane.ZeroBound.Covid.partial_backing
#print axioms Cochrane.ZeroBound.Covid.partial_backing_example
#print axioms Cochrane.ZeroBound.Covid.e10_printed_pair_inconsistent
#print axioms Cochrane.ZeroBound.Covid.hasDerivAt_priceRatio
#print axioms Cochrane.ZeroBound.Covid.priceRatio_remainder
#print axioms Cochrane.ZeroBound.Covid.first_order_example
#print axioms Cochrane.ZeroBound.Covid.priceRatio_strictAnti
#print axioms Cochrane.ZeroBound.Covid.reserves_only_unbacked
#print axioms Cochrane.ZeroBound.Covid.fiscal_news_only_unexpected
#print axioms Cochrane.ZeroBound.Covid.peg_inflation_returns
#print axioms Cochrane.ZeroBound.Covid.pc_output
#print axioms Cochrane.ZeroBound.Covid.disinflation_joint
#print axioms Cochrane.ZeroBound.Covid.disinflation_alone
#print axioms Cochrane.ZeroBound.Covid.joint_less_painful
#print axioms Cochrane.ZeroBound.Covid.painless_limit
#print axioms Cochrane.ZeroBound.Covid.fisherian_rate_fall
#print axioms Cochrane.ZeroBound.Covid.interest_cost_four_times
#print axioms Cochrane.ZeroBound.Covid.interest_cost_ratio
#print axioms Cochrane.ZeroBound.Covid.windfall_real_return
#print axioms Cochrane.ZeroBound.Covid.cpi_rise
#print axioms Cochrane.ZeroBound.Covid.table_21_1
#print axioms Cochrane.ZeroBound.Covid.debt_increase_nearly_30
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.abs_lt_sqrt_disc
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.sq_sqrt_disc
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_pos
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb_pos
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_mul_lamb
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_sub_lamb
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_add_lamb
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_add_lamb_pos
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_root
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb_root
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.charpoly_factor
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.kappa_sigma_div_lamf
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb_le_lamf
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.sqrt_sub_le_lamb
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.sqrt_add_le_lamf
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb_strictMono
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_strictMono
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.sqrt_kappa_tendsto
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamb_tendsto_atTop
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.lamf_tendsto_atTop
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.hasDerivAt_expNeg
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.hasDerivAt_expPos
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.tendsto_expNeg
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.tendsto_expPos
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.tendsto_of_deriv_Ioi
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.integral_Ioi_shift
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.integral_exp_shift
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.tvc_of_bounded
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.integrableOn_exp_mul_of_bdd
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.abs_integral_exp_le
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.integral_exp_Ioi
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.integrableOn_exp_Ioi
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.intervalIntegral_exp
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.tvc_iff_forward
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.fwdInt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.fwdInt_eq
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.fwdInt_hasDerivAt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.fwdInt_abs_le
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.bwdInfInt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.bwdInfInt_eq_fwdInt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.bwdInfInt_hasDerivAt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.bwdInfInt_abs_le
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.bwdInfInt_continuous
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.fwdInt_continuous
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.const_of_hasDerivAt_zero_off
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.linear_ode_Icc
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.affine_ode_Icc
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.linear_ode_Ici
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.unstable_bdd_zero
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.linear_ode_univ
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.greenPi
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.greenPi_hasDerivAt
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.greenPi_sub_abs_le
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.greenPi_injective
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.greenPi_forward_stable
#print axioms Cochrane.ZeroBound.ContinuousTimeNK.forward_stable_iff
#print axioms Cochrane.ZeroBound.WerningModel.IsPath
#print axioms Cochrane.ZeroBound.WerningModel.BddOnIci
#print axioms Cochrane.ZeroBound.WerningModel.IsPath.add
#print axioms Cochrane.ZeroBound.WerningModel.IsPath.sub
#print axioms Cochrane.ZeroBound.WerningModel.IsPath.congr
#print axioms Cochrane.ZeroBound.WerningModel.homog_bdd
#print axioms Cochrane.ZeroBound.WerningModel.trapStep
#print axioms Cochrane.ZeroBound.WerningModel.hh
#print axioms Cochrane.ZeroBound.WerningModel.kk
#print axioms Cochrane.ZeroBound.WerningModel.trapPi
#print axioms Cochrane.ZeroBound.WerningModel.trapY
#print axioms Cochrane.ZeroBound.WerningModel.wPi
#print axioms Cochrane.ZeroBound.WerningModel.wX
#print axioms Cochrane.ZeroBound.WerningModel.hh_zero
#print axioms Cochrane.ZeroBound.WerningModel.kk_zero
#print axioms Cochrane.ZeroBound.WerningModel.hh_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.kk_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.trapPi_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.trapY_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.trapPi_zero
#print axioms Cochrane.ZeroBound.WerningModel.trapY_zero
#print axioms Cochrane.ZeroBound.WerningModel.trapPi_shift
#print axioms Cochrane.ZeroBound.WerningModel.wPi_T
#print axioms Cochrane.ZeroBound.WerningModel.wPi_shift
#print axioms Cochrane.ZeroBound.WerningModel.wX_shift
#print axioms Cochrane.ZeroBound.WerningModel.wPi_continuous
#print axioms Cochrane.ZeroBound.WerningModel.wX_continuous
#print axioms Cochrane.ZeroBound.WerningModel.wPath_isPath
#print axioms Cochrane.ZeroBound.WerningModel.bdd_of_cont_exp
#print axioms Cochrane.ZeroBound.WerningModel.wPath_bdd
#print axioms Cochrane.ZeroBound.WerningModel.bdd_path_iff
#print axioms Cochrane.ZeroBound.WerningModel.bdd_path_existsUnique
#print axioms Cochrane.ZeroBound.WerningModel.trapBranch_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.trapBranchX_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.postBranch_hasDerivAt
#print axioms Cochrane.ZeroBound.WerningModel.jump_pi
#print axioms Cochrane.ZeroBound.WerningModel.jump_x
#print axioms Cochrane.ZeroBound.WerningModel.IsGlobalSol
#print axioms Cochrane.ZeroBound.WerningModel.zForce
#print axioms Cochrane.ZeroBound.WerningModel.bookX
#print axioms Cochrane.ZeroBound.WerningModel.eq20_8_solves
#print axioms Cochrane.ZeroBound.WerningModel.eq20_8_iff
#print axioms Cochrane.ZeroBound.WerningModel.family_equiv
#print axioms Cochrane.ZeroBound.WerningModel.kern
#print axioms Cochrane.ZeroBound.WerningModel.zTrap
#print axioms Cochrane.ZeroBound.WerningModel.integral_exp_bwd
#print axioms Cochrane.ZeroBound.WerningModel.integral_exp_fwd
#print axioms Cochrane.ZeroBound.WerningModel.bwd_step_le
#print axioms Cochrane.ZeroBound.WerningModel.bwd_step_ge
#print axioms Cochrane.ZeroBound.WerningModel.fwd_step_le
#print axioms Cochrane.ZeroBound.WerningModel.fwd_step_ge
#print axioms Cochrane.ZeroBound.WerningModel.bookC
#print axioms Cochrane.ZeroBound.WerningModel.atomsB
#print axioms Cochrane.ZeroBound.WerningModel.atomsF
#print axioms Cochrane.ZeroBound.WerningModel.book_form
#print axioms Cochrane.ZeroBound.WerningModel.bookPi
#print axioms Cochrane.ZeroBound.WerningModel.bookKX
#print axioms Cochrane.ZeroBound.WerningModel.experiment_eq20_8
#print axioms Cochrane.ZeroBound.WerningModel.bookPi_C_unique
#print axioms Cochrane.ZeroBound.WerningModel.active_rule_dev_zero
#print axioms Cochrane.ZeroBound.WerningModel.eq20_7_selects
#print axioms Cochrane.ZeroBound.ZLBSelection.kk_pos
#print axioms Cochrane.ZeroBound.ZLBSelection.kk_strictMono
#print axioms Cochrane.ZeroBound.ZLBSelection.hh_strictMonoOn
#print axioms Cochrane.ZeroBound.ZLBSelection.one_lt_hh
#print axioms Cochrane.ZeroBound.ZLBSelection.hh_ge
#print axioms Cochrane.ZeroBound.ZLBSelection.sinhc_strictMonoOn
#print axioms Cochrane.ZeroBound.ZLBSelection.hh_eq_cosh
#print axioms Cochrane.ZeroBound.ZLBSelection.hh_strictMono_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_pi_eq
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_eq
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_book
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_pi_neg
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_after
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_pi_strictMonoOn
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_x_eq
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_x_neg
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_x_strictMonoOn
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_le
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_tendsto_T
#print axioms Cochrane.ZeroBound.ZLBSelection.half_le_weight
#print axioms Cochrane.ZeroBound.ZLBSelection.expLamb_tendsto_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_tendsto_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_tendsto_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_strictAnti_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.pi0NK_strictAnti_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.x0NK_tendsto_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.IsFrictionless
#print axioms Cochrane.ZeroBound.ZLBSelection.frictionless_iff
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_discontinuity
#print axioms Cochrane.ZeroBound.ZLBSelection.piTnj
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_pi0
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_formula
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_key
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_pos
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_lt
#print axioms Cochrane.ZeroBound.ZLBSelection.piTnj_bounds
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_tendsto_time
#print axioms Cochrane.ZeroBound.ZLBSelection.expNeg_lam_tendsto
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_dist_trap
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_limit_trap
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_uniform_trap
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_uniform_after
#print axioms Cochrane.ZeroBound.ZLBSelection.nj_limit_after
#print axioms Cochrane.ZeroBound.ZLBSelection.IsValuation
#print axioms Cochrane.ZeroBound.ZLBSelection.jump_eq_fiscal
#print axioms Cochrane.ZeroBound.ZLBSelection.fiscalContraction
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_fiscal_contraction
#print axioms Cochrane.ZeroBound.ZLBSelection.fiscalContraction_tendsto
#print axioms Cochrane.ZeroBound.ZLBSelection.gap_neg_iff
#print axioms Cochrane.ZeroBound.ZLBSelection.HH
#print axioms Cochrane.ZeroBound.ZLBSelection.HH_zero
#print axioms Cochrane.ZeroBound.ZLBSelection.HH_hasDerivAt
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_x_eq_HH
#print axioms Cochrane.ZeroBound.ZLBSelection.HH_strictMono_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.nk_x_strictAnti_kappa
#print axioms Cochrane.ZeroBound.ZLBSelection.x0NK_strictAnti_kappa
#print axioms Cochrane.ZeroBound.ForwardGuidance.dpi_dpiT
#print axioms Cochrane.ZeroBound.ForwardGuidance.dpi0_dpiT
#print axioms Cochrane.ZeroBound.ForwardGuidance.hasDerivAt_pi0_piT
#print axioms Cochrane.ZeroBound.ForwardGuidance.piTnj_eq
#print axioms Cochrane.ZeroBound.ForwardGuidance.glide_path
#print axioms Cochrane.ZeroBound.ForwardGuidance.sensitivity_strictMono_T
#print axioms Cochrane.ZeroBound.ForwardGuidance.sensitivity_tendsto_T
#print axioms Cochrane.ZeroBound.ForwardGuidance.sensitivity_strictMono_kappa
#print axioms Cochrane.ZeroBound.ForwardGuidance.sensitivity_tendsto_kappa
#print axioms Cochrane.ZeroBound.ForwardGuidance.frictionless_unique
#print axioms Cochrane.ZeroBound.ForwardGuidance.isPath_congr_forcing
#print axioms Cochrane.ZeroBound.ForwardGuidance.delayI
#print axioms Cochrane.ZeroBound.ForwardGuidance.delayU
#print axioms Cochrane.ZeroBound.ForwardGuidance.delayPi
#print axioms Cochrane.ZeroBound.ForwardGuidance.delayX
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_isPath
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_bdd
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_after
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_unique
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_pi0
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_pi0_strictMono
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_zero
#print axioms Cochrane.ZeroBound.ForwardGuidance.delay_pi0_tendsto
#print axioms Cochrane.ZeroBound.Multipliers.is_forward
#print axioms Cochrane.ZeroBound.Multipliers.trapStep_integrableOn
#print axioms Cochrane.ZeroBound.Multipliers.experiment_is_forward
#print axioms Cochrane.ZeroBound.Multipliers.xNK
#print axioms Cochrane.ZeroBound.Multipliers.piTnjg
#print axioms Cochrane.ZeroBound.Multipliers.xNJ
#print axioms Cochrane.ZeroBound.Multipliers.multNK
#print axioms Cochrane.ZeroBound.Multipliers.multNJ
#print axioms Cochrane.ZeroBound.Multipliers.nj_g_pi0
#print axioms Cochrane.ZeroBound.Multipliers.xNK_affine
#print axioms Cochrane.ZeroBound.Multipliers.xNJ_affine
#print axioms Cochrane.ZeroBound.Multipliers.hasDerivAt_xNK
#print axioms Cochrane.ZeroBound.Multipliers.hasDerivAt_xNJ
#print axioms Cochrane.ZeroBound.Multipliers.multNK_pos
#print axioms Cochrane.ZeroBound.Multipliers.multNK_tendsto_kappa
#print axioms Cochrane.ZeroBound.Multipliers.multNK_strictMono_kappa
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_eq
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_strictMonoOn_T
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_ge
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_tendsto_T
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_gt_one_eventually
#print axioms Cochrane.ZeroBound.Multipliers.multNK0_lt_one_short
#print axioms Cochrane.ZeroBound.Multipliers.e20_counterexample
#print axioms Cochrane.ZeroBound.Multipliers.frictionless_multiplier
#print axioms Cochrane.ZeroBound.Multipliers.multNJ_formula
#print axioms Cochrane.ZeroBound.Multipliers.multNJ_bounds
#print axioms Cochrane.ZeroBound.Multipliers.multNJ_dist
#print axioms Cochrane.ZeroBound.Multipliers.multNJ_tendsto_kappa
#print axioms Cochrane.ZeroBound.Multipliers.multNJ_tendsto_T
#print axioms Cochrane.ZeroBound.Multipliers.gWindow
#print axioms Cochrane.ZeroBound.Multipliers.windowX
#print axioms Cochrane.ZeroBound.Multipliers.windowPi
#print axioms Cochrane.ZeroBound.Multipliers.window_isPath
#print axioms Cochrane.ZeroBound.Multipliers.window_after
#print axioms Cochrane.ZeroBound.Multipliers.window_bdd
#print axioms Cochrane.ZeroBound.Multipliers.window_unique
#print axioms Cochrane.ZeroBound.Multipliers.windowMult
#print axioms Cochrane.ZeroBound.Multipliers.window_x0
#print axioms Cochrane.ZeroBound.Multipliers.windowMult_eq
#print axioms Cochrane.ZeroBound.Multipliers.windowMult_strictMono
#print axioms Cochrane.ZeroBound.Multipliers.windowMult_tendsto
#print axioms Cochrane.ZeroBound.ZLBWelfare.calvoW
#print axioms Cochrane.ZeroBound.ZLBWelfare.relPrice
#print axioms Cochrane.ZeroBound.ZLBWelfare.dispersion
#print axioms Cochrane.ZeroBound.ZLBWelfare.resetGap
#print axioms Cochrane.ZeroBound.ZLBWelfare.hasSum_calvoW
#print axioms Cochrane.ZeroBound.ZLBWelfare.hasSum_calvoW_mul
#print axioms Cochrane.ZeroBound.ZLBWelfare.hasSum_sq_mul_geometric
#print axioms Cochrane.ZeroBound.ZLBWelfare.hasSum_calvoW_sq
#print axioms Cochrane.ZeroBound.ZLBWelfare.relPrice_mean
#print axioms Cochrane.ZeroBound.ZLBWelfare.dispersion_eq
#print axioms Cochrane.ZeroBound.ZLBWelfare.resetGap_eq
#print axioms Cochrane.ZeroBound.ZLBWelfare.dispersion_fixed_point
#print axioms Cochrane.ZeroBound.ZLBWelfare.dispersion_eq_zero_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.relPrice_zero
#print axioms Cochrane.ZeroBound.ZLBWelfare.dispersion_lt_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.resetGap_lt_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.ss_phillips_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.ssLoss
#print axioms Cochrane.ZeroBound.ZLBWelfare.ssLoss_lt_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.zlb_steady_state
#print axioms Cochrane.ZeroBound.ZLBWelfare.zlb_better_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.zlb_worse_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.zlb_welfare_better_iff
#print axioms Cochrane.ZeroBound.ZLBWelfare.e9_counterexample
#print axioms Cochrane.ZeroBound.ZLBWelfare.book_calibration
#print axioms Cochrane.ZeroBound.ZLBWelfare.zlb_better_of_one_le
#print axioms Cochrane.ZeroBound.Links.scaledRoot
#print axioms Cochrane.ZeroBound.Links.lam1_scaled_eq
#print axioms Cochrane.ZeroBound.Links.lam2_scaled_eq
#print axioms Cochrane.ZeroBound.Links.scaledRoot_zero
#print axioms Cochrane.ZeroBound.Links.continuous_scaledRoot
#print axioms Cochrane.ZeroBound.Links.scaledRoot_pos
#print axioms Cochrane.ZeroBound.Links.tendsto_lam1_scaled
#print axioms Cochrane.ZeroBound.Links.tendsto_lam2_scaled
#print axioms Cochrane.ZeroBound.Links.tendsto_peg_decay
#print axioms Cochrane.ZeroBound.Links.peg_pf_path
#print axioms Cochrane.ZeroBound.Links.peg_paths_converge
#print axioms Cochrane.ZeroBound.Links.werning_continuum
#print axioms Cochrane.ZeroBound.Links.tendsto_peg_impact
#print axioms Cochrane.ZeroBound.Links.fiscal_impact_frictionless
#print axioms Cochrane.ZeroBound.Links.werning_future_selection
#print axioms Cochrane.ZeroBound.Links.gabaix_rational_eq_peg
#print axioms Cochrane.ZeroBound.Links.gabaixEq_rational_iff
#print axioms Cochrane.ZeroBound.Links.gabaix_rational_straddle
#print axioms Cochrane.ZeroBound.Links.map46_fixed_beta_iff
#print axioms Cochrane.ZeroBound.Links.zlb_fixed_point_eq_beta
#print axioms Cochrane.ZeroBound.Links.zlb_steady_log
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.natRate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.natRate_of_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.natRate_of_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.NKPC
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.impliedRate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.ups1
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.impliedRate_eq
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backState
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zlbPath
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zlbPath_of_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zlbPath_of_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.discX
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.discPi
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Feasible
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lossTerm
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.loss
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Optimal
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lag
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.FOC36
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gam
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gam_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gam_mul_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gam_mul_lt_iff
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.sqrt_lt_one
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del_lt_one_iff
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.postX
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.postPi
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_eq42_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_eq43_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_rate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_of_rate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.down_ind
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_sub_fst
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_sub_snd
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zr_strict
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zr_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zr_eq
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zr_lower
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.feasible_of_rate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zrAux
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zrPath
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zrPath_of_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.zrPath_of_ge
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delayPath
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_step
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_after
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_isPath
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_feasible
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_eq_disc
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_succ
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_le_of_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_lt_of_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_growth
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_lower
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.delay_pi0_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_step
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_liftoff_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_gt_delay
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_gt_disc
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_rates
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.eq_zero_of_tsum_nonpos
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.sq_terms_zero
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.optimal_unique
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disc_feasible_summable
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_loss_lt
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.l1
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.l2
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.vx
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.one_lt_l1
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.l1_vx
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.kappa_vx
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_eigen
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.wState
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_post
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_end
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_trap
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_after
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_isPath
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_bdd
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_zero
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_sub
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_pi0_sub
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_sensitivity_strictMono
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_sensitivity_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.sensitivity_tendsto_exp
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_unique
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.w_family_iff
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_promise
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_not_member
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dAvg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.summable_disc
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dAvg_lincomb
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dAvg_const
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dAvg_mono
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.bigK
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.MomentFeasible
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.PathwiseZLB
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.pathwise_mean_nonneg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.band_moment_feasible
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.violation_freq_le
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.pathwise_violation_freq
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dAvg_pf
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.spike
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dip
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.spike_moments
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.dip_moments
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.pathwise_not_moment
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.moment_not_pathwise
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.Moments.neither_implies
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lagS
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.DispRec
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disp_const_closed
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disp_const_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disp_const_stationary
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disp_const_discounted
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.disp_const_avg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.woodford_zlb_better_iff
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.quadLoss_steady
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.deflGap
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gali_deflation_steady
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gali_deflation_worse
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.gam_mul_denom
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.four_beta_gam_sq_lt_one
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.sqrt_sq_eq
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del_mul
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del_quad
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.kappa_sq_del
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lag_succ
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lag_zero
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.FOC35
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.KKT
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.lagrangian_identity
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.tendsto_pow_mul_abs
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.kkt_sufficient
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.kkt_optimal
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.kkt_unique
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.postXi
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_eq37
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_eq38
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_eq39
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_rate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_rate_nonneg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.backStep_nkpc_rate
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.algorithm_verification
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_loss_lt_alg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.xi1_eq
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.xi_pos_iff
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.longrun_price
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.post_neg
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_gt_delay_of_state
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.comm_gt_disc_of_state
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.del_cex
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexXi
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexX
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexPi
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexXi1
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexXi2
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cexXi1_one
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cex_optimal
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cex_liftoff_at_shock_end
#print axioms Cochrane.ZeroBound.LinksGaliWoodford.cex_xi_neg
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.tendsto_one_add_pow
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.backStep_modes
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.backState_modes
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sqS
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr1
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr2
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr_root
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr_sub_pos
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr_zero
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.sr_continuous
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.char_of_scaled
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trapDisc
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.coefA
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.coefB
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.closed_generic
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trapDisc_closed
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trapDisc_eq_wState
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.wPi_modes
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.algA
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.algB
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.algX
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trap_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trap_pi_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.trap_x_tendsto
#print axioms Cochrane.ZeroBound.LinksGaliWoodfordLimit.wState_tendsto
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb_le_of_min
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb_up
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb_step
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb_neg
#print axioms Cochrane.ZeroBound.LiftoffTiming.grow
#print axioms Cochrane.ZeroBound.LiftoffTiming.not_tendsto_sq
#print axioms Cochrane.ZeroBound.LiftoffTiming.not_tendsto_lin
#print axioms Cochrane.ZeroBound.LiftoffTiming.comb_blowup
#print axioms Cochrane.ZeroBound.LiftoffTiming.gap
#print axioms Cochrane.ZeroBound.LiftoffTiming.lam
#print axioms Cochrane.ZeroBound.LiftoffTiming.lamI
#print axioms Cochrane.ZeroBound.LiftoffTiming.impliedRate_eq_gap
#print axioms Cochrane.ZeroBound.LiftoffTiming.x_of_nkpc
#print axioms Cochrane.ZeroBound.LiftoffTiming.gap_comb
#print axioms Cochrane.ZeroBound.LiftoffTiming.lam_comb
#print axioms Cochrane.ZeroBound.LiftoffTiming.lamI_eq
#print axioms Cochrane.ZeroBound.LiftoffTiming.gap_lam
#print axioms Cochrane.ZeroBound.LiftoffTiming.lam_mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.lamI_mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.rate_nonneg
#print axioms Cochrane.ZeroBound.LiftoffTiming.tendsto_pi_sq
#print axioms Cochrane.ZeroBound.LiftoffTiming.mult_zero_left
#print axioms Cochrane.ZeroBound.LiftoffTiming.mult_zero_right
#print axioms Cochrane.ZeroBound.LiftoffTiming.pi_le_bound
#print axioms Cochrane.ZeroBound.LiftoffTiming.post_nonpos
#print axioms Cochrane.ZeroBound.LiftoffTiming.slack_contra_le
#print axioms Cochrane.ZeroBound.LiftoffTiming.slack_contra_gt
#print axioms Cochrane.ZeroBound.LiftoffTiming.trap_mult_pos
#print axioms Cochrane.ZeroBound.LiftoffTiming.mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.mxi1
#print axioms Cochrane.ZeroBound.LiftoffTiming.mxi2
#print axioms Cochrane.ZeroBound.LiftoffTiming.foc35_mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.foc36_mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.mult_unique
#print axioms Cochrane.ZeroBound.LiftoffTiming.cross
#print axioms Cochrane.ZeroBound.LiftoffTiming.lossTerm_pert
#print axioms Cochrane.ZeroBound.LiftoffTiming.summable_cross
#print axioms Cochrane.ZeroBound.LiftoffTiming.foc_dir
#print axioms Cochrane.ZeroBound.LiftoffTiming.feasible_pert
#print axioms Cochrane.ZeroBound.LiftoffTiming.cross_neg
#print axioms Cochrane.ZeroBound.LiftoffTiming.dir_of_step
#print axioms Cochrane.ZeroBound.LiftoffTiming.hdir
#print axioms Cochrane.ZeroBound.LiftoffTiming.hdir_gt
#print axioms Cochrane.ZeroBound.LiftoffTiming.hdir_step
#print axioms Cochrane.ZeroBound.LiftoffTiming.hdir_dir
#print axioms Cochrane.ZeroBound.LiftoffTiming.hdir_summable
#print axioms Cochrane.ZeroBound.LiftoffTiming.cross_hdir
#print axioms Cochrane.ZeroBound.LiftoffTiming.wdir
#print axioms Cochrane.ZeroBound.LiftoffTiming.wdir_step
#print axioms Cochrane.ZeroBound.LiftoffTiming.wdir_dir
#print axioms Cochrane.ZeroBound.LiftoffTiming.wdir_summable
#print axioms Cochrane.ZeroBound.LiftoffTiming.cross_wdir
#print axioms Cochrane.ZeroBound.LiftoffTiming.vx2
#print axioms Cochrane.ZeroBound.LiftoffTiming.cf1
#print axioms Cochrane.ZeroBound.LiftoffTiming.cf2
#print axioms Cochrane.ZeroBound.LiftoffTiming.l_add
#print axioms Cochrane.ZeroBound.LiftoffTiming.l_mul
#print axioms Cochrane.ZeroBound.LiftoffTiming.l2_bounds
#print axioms Cochrane.ZeroBound.LiftoffTiming.l2_vx2
#print axioms Cochrane.ZeroBound.LiftoffTiming.kappa_vx2
#print axioms Cochrane.ZeroBound.LiftoffTiming.cf_vx
#print axioms Cochrane.ZeroBound.LiftoffTiming.cf_sum
#print axioms Cochrane.ZeroBound.LiftoffTiming.backState_closed
#print axioms Cochrane.ZeroBound.LiftoffTiming.ddir
#print axioms Cochrane.ZeroBound.LiftoffTiming.ddir_le
#print axioms Cochrane.ZeroBound.LiftoffTiming.ddir_gt
#print axioms Cochrane.ZeroBound.LiftoffTiming.ddir_bound
#print axioms Cochrane.ZeroBound.LiftoffTiming.summable_abs
#print axioms Cochrane.ZeroBound.LiftoffTiming.tendsto_mxi2
#print axioms Cochrane.ZeroBound.LiftoffTiming.kkt_necessary
#print axioms Cochrane.ZeroBound.LiftoffTiming.optimal_trap_binds
#print axioms Cochrane.ZeroBound.LiftoffTiming.optimal_h48
#print axioms Cochrane.ZeroBound.LiftoffTiming.liftoff_ge
#print axioms Cochrane.ZeroBound.LiftoffTiming.liftoff_ge_mult
#print axioms Cochrane.ZeroBound.LiftoffTiming.liftoff_after_shock
#print axioms Cochrane.ZeroBound.LiftoffTiming.optimal_pi_le
#print axioms Cochrane.ZeroBound.LiftoffTiming.comm_gt_disc_opt
#print axioms Cochrane.ZeroBound.LiftoffTiming.comm_loss_lt_opt
#print axioms Cochrane.ZeroBound.LiftoffTiming.comm_promise_opt
#print axioms Cochrane.ZeroBound.LiftoffTiming.comm_gt_disc_of_state_opt
#print axioms Cochrane.ZeroBound.LiftoffTiming.algorithm_verification_gen
#print axioms Cochrane.ZeroBound.LiftoffTiming.comm_loss_lt_alg_gen
#print axioms Cochrane.ZeroBound.LiftoffStructure.comb_smul
#print axioms Cochrane.ZeroBound.LiftoffStructure.comb_add_const
#print axioms Cochrane.ZeroBound.LiftoffStructure.del_root
#print axioms Cochrane.ZeroBound.LiftoffStructure.two_root
#print axioms Cochrane.ZeroBound.LiftoffStructure.no_return
#print axioms Cochrane.ZeroBound.LiftoffStructure.exists_slack_after
#print axioms Cochrane.ZeroBound.LiftoffStructure.post_form
#print axioms Cochrane.ZeroBound.LiftoffStructure.optimal_binding
#print axioms Cochrane.ZeroBound.LiftoffStructure.optimal_liftoff
#print axioms Cochrane.ZeroBound.LiftoffStructure.optimal_algorithm_form
#print axioms Cochrane.ZeroBound.LiftoffStructure.PathSpace
#print axioms Cochrane.ZeroBound.LiftoffStructure.decP
#print axioms Cochrane.ZeroBound.LiftoffStructure.decX
#print axioms Cochrane.ZeroBound.LiftoffStructure.enc
#print axioms Cochrane.ZeroBound.LiftoffStructure.sqrt_pow_sq
#print axioms Cochrane.ZeroBound.LiftoffStructure.decP_enc
#print axioms Cochrane.ZeroBound.LiftoffStructure.decX_enc
#print axioms Cochrane.ZeroBound.LiftoffStructure.lossTerm_dec
#print axioms Cochrane.ZeroBound.LiftoffStructure.summable_sq
#print axioms Cochrane.ZeroBound.LiftoffStructure.norm_sq_eq
#print axioms Cochrane.ZeroBound.LiftoffStructure.loss_dec
#print axioms Cochrane.ZeroBound.LiftoffStructure.memℓp_enc
#print axioms Cochrane.ZeroBound.LiftoffStructure.feasible_convex
#print axioms Cochrane.ZeroBound.LiftoffStructure.feasSet
#print axioms Cochrane.ZeroBound.LiftoffStructure.coord_continuous
#print axioms Cochrane.ZeroBound.LiftoffStructure.feasSet_closed
#print axioms Cochrane.ZeroBound.LiftoffStructure.feasSet_convex
#print axioms Cochrane.ZeroBound.LiftoffStructure.exists_optimal
#print axioms Cochrane.ZeroBound.LiftoffStructure.optimal_exists_unique
#print axioms Cochrane.ZeroBound.LiftoffStructure.commitment_characterisation
#print axioms Cochrane.ZeroBound.LiftoffStructure.liftoff_rates
#print axioms Cochrane.ZeroBound.LiftoffStructure.rho_zero_structure
#print axioms Cochrane.ZeroBound.LiftoffStructure.rho_zero_unit_ratio
#print axioms Cochrane.ZeroBound.LiftoffStructure.rho_zero_no_liftoff
#print axioms Cochrane.ZeroBound.LiftoffStructure.rho_zero_instance
