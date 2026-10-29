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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.CondVar
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
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

namespace Cochrane.FiscalConstraints

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

end Cochrane.FiscalConstraints

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

namespace Cochrane.FiscalConstraints

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

end Cochrane.FiscalConstraints

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

namespace Cochrane.FiscalConstraints.ExpectationsFiniteTree

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

end Cochrane.FiscalConstraints.ExpectationsFiniteTree

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

namespace Cochrane.FiscalConstraints.ForwardSolution

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

end Cochrane.FiscalConstraints.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exponential integrals on `[0, ∞)`

Infrastructure for Cochrane (2023), Chapter 6, *Fiscal constraints*, §6.1–§6.4 (pp. 189–199).
Every present value in the continuous-time parts of the chapter is an improper integral
`∫₀^∞ e^{-a u} f(u) du`: the present value of tax revenue (p. 189), the value of debt (6.2)
(p. 191) and (6.3) (p. 195), and the forward solution of the debt-to-GDP equation (6.4)
(p. 196). This module collects the exact facts used.

## Main results

* `integrableOn_exp_neg_mul`, `integral_exp_neg_mul_Ioi`, `integral_exp_neg_mul_Ioi_zero`:
  `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`.
* `not_integrableOn_exp_neg_mul`: for `a ≤ 0` and `c ≠ 0` the integrand `c e^{-a u}` is not
  integrable on `(0, ∞)` (the present value is genuinely infinite, not a junk value).
* `integral_exp_growth`, `not_integrableOn_exp_growth`: the growing-stream present value
  `∫₀^∞ e^{-r u} c e^{g u} du = c/(r - g)` iff `r > g` (pp. 189, 191, 195).
* `integrableOn_exp_mul_bdd`, `abs_integral_exp_mul_le`: discounted bounded continuous streams
  are integrable, with the bound `M e^{-a c}/a`.
* `integral_Ioi_comp_add`, `integral_exp_shift`: translation of `(0, ∞)` to `(t, ∞)`.
* `integral_Ioi_sub_interval`: `∫_{(0,∞)} - ∫_0^t = ∫_{(t,∞)}`.
* `intervalIntegral_exp_neg_mul`: `∫₀^T e^{-a u} du = (1 - e^{-aT})/a`.
* `tendsto_const_mul_exp_zero_iff`, `tendsto_const_mul_exp_atTop`: `K e^{aT} → 0` iff `a < 0`,
  and `→ ∞` for `a > 0` (p. 200).
* `tvc_of_bounded`: a bounded path satisfies `e^{-a(T-t)} w_T → 0` for `a > 0` (p. 201).
-/

namespace Cochrane.FiscalConstraints.ExpIntegrals

open Real MeasureTheory Filter Topology

/-- Cochrane (2023), §6.1, p. 189: the discount factor `e^{-a u}` is integrable on `(c, ∞)` when
`a > 0`. -/
theorem integrableOn_exp_neg_mul {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun u : ℝ => exp (-a * u)) (Set.Ioi c) :=
  integrableOn_exp_mul_Ioi (by linarith) c

/-- Cochrane (2023), §6.1, p. 189: `∫_c^∞ e^{-a u} du = e^{-a c}/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ u in Set.Ioi c, exp (-a * u) = exp (-a * c) / a := by
  rw [integral_exp_mul_Ioi (by linarith) c, neg_div, div_neg, neg_neg]

/-- Cochrane (2023), §6.1, p. 189: `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) = 1 / a := by
  rw [integral_exp_neg_mul_Ioi ha 0, mul_zero, exp_zero]

/-- Cochrane (2023), §6.1, p. 189 and §6.4, p. 195: for `a ≤ 0` and `c ≠ 0` the stream
`c e^{-a u}` is NOT integrable on `(0, ∞)`: its present value is infinite. -/
theorem not_integrableOn_exp_neg_mul {a : ℝ} (ha : a ≤ 0) {c : ℝ} (hc : c ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => c * exp (-a * u)) (Set.Ioi 0) := by
  intro h
  have h1 : IntegrableOn (fun _ : ℝ => c) (Set.Ioi 0) := by
    refine Integrable.mono h aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : (0 : ℝ) < u := hu
    have he : 1 ≤ exp (-a * u) := one_le_exp (by nlinarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    nlinarith [abs_nonneg c]
  rw [integrableOn_const_iff] at h1
  rcases h1 with h1 | h1
  · exact hc (enorm_eq_zero.1 h1)
  · rw [Real.volume_Ioi] at h1
    exact lt_irrefl _ h1

/-- Cochrane (2023), §6.1, p. 189, and (6.2), p. 191: the integrand of the present value of a
stream `c e^{g u}` discounted at `r` is `c e^{-(r-g)u}`. -/
theorem exp_growth_eq (r g c u : ℝ) :
    exp (-r * u) * (c * exp (g * u)) = c * exp (-(r - g) * u) := by
  rw [mul_left_comm, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.1, p. 189: for `r > g` a stream growing at `g` has an integrable
present value. -/
theorem integrableOn_exp_growth {r g : ℝ} (h : g < r) (c : ℝ) :
    IntegrableOn (fun u : ℝ => exp (-r * u) * (c * exp (g * u))) (Set.Ioi 0) := by
  simp_rw [exp_growth_eq]
  exact (integrableOn_exp_neg_mul (by linarith) 0).const_mul c

/-- Cochrane (2023), §6.1, p. 189, (6.2), p. 191, and (6.3), p. 195: for `r > g`,
`∫₀^∞ e^{-r u} c e^{g u} du = c/(r - g)`. -/
theorem integral_exp_growth {r g : ℝ} (h : g < r) (c : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (c * exp (g * u)) = c / (r - g) := by
  simp_rw [exp_growth_eq]
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero (by linarith)]
  ring

/-- Cochrane (2023), §6.4, p. 195: for `r ≤ g` and `c ≠ 0` the present value of a stream
growing at `g` is infinite (the integrand is not integrable). -/
theorem not_integrableOn_exp_growth {r g : ℝ} (h : r ≤ g) {c : ℝ} (hc : c ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => exp (-r * u) * (c * exp (g * u))) (Set.Ioi 0) := by
  simp_rw [exp_growth_eq]
  exact not_integrableOn_exp_neg_mul (by linarith) hc

/-- Cochrane (2023), §6.4.1, p. 196: a bounded continuous surplus stream discounted at `a > 0`
is integrable on `(c, ∞)`. -/
theorem integrableOn_exp_mul_bdd {a M : ℝ} (ha : 0 < a) {σ : ℝ → ℝ} (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (c : ℝ) :
    IntegrableOn (fun u => exp (-a * u) * σ u) (Set.Ioi c) := by
  have := Integrable.bdd_mul (integrableOn_exp_neg_mul ha c) hσ.aestronglyMeasurable
    (c := M) (ae_of_all _ fun u => (Real.norm_eq_abs _).le.trans (hM u))
  exact Integrable.congr this (ae_of_all _ fun u => mul_comm _ _)

/-- Cochrane (2023), §6.4.1, p. 196: `|∫_c^∞ e^{-a u} σ(u) du| ≤ M e^{-a c}/a` when `|σ| ≤ M`. -/
theorem abs_integral_exp_mul_le {a M : ℝ} (ha : 0 < a) {σ : ℝ → ℝ}
    (hM : ∀ u, |σ u| ≤ M) (c : ℝ) :
    |∫ u in Set.Ioi c, exp (-a * u) * σ u| ≤ M * (exp (-a * c) / a) := by
  have hint : IntegrableOn (fun u : ℝ => M * exp (-a * u)) (Set.Ioi c) :=
    (integrableOn_exp_neg_mul ha c).const_mul M
  have := norm_integral_le_of_norm_le (f := fun u => exp (-a * u) * σ u) hint
    (ae_of_all _ fun u => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM u) (exp_pos _).le)
  rw [Real.norm_eq_abs, integral_const_mul, integral_exp_neg_mul_Ioi ha c] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (infrastructure): translating `(0, ∞)` to `(t, ∞)`,
`∫₀^∞ f(t + u) du = ∫_t^∞ f(v) dv` (no integrability needed: both sides are Bochner integrals
of translates). -/
theorem integral_Ioi_comp_add (f : ℝ → ℝ) (t : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), f (t + u) = ∫ v in Set.Ioi t, f v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (μ := volume) (fun v => Set.indicator (Set.Ioi t) f v) t]
  congr 1
  funext u
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu),
      Set.indicator_of_mem (show u + t ∈ Set.Ioi t by simp [hu]), add_comm]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (0 : ℝ) from hu),
      Set.indicator_of_notMem (show u + t ∉ Set.Ioi t by simpa using hu)]

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value at date `t`,
`∫₀^∞ e^{-a u} σ(t + u) du = e^{a t} ∫_t^∞ e^{-a v} σ(v) dv`. -/
theorem integral_exp_shift (a t : ℝ) (σ : ℝ → ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) * σ (t + u) =
      exp (a * t) * ∫ v in Set.Ioi t, exp (-a * v) * σ v := by
  rw [← integral_const_mul,
    ← integral_Ioi_comp_add (fun v => exp (a * t) * (exp (-a * v) * σ v)) t]
  congr 1
  funext u
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.4.1, p. 196 (infrastructure): `∫_{(0,∞)} f - ∫_0^t f = ∫_{(t,∞)} f` for
`f` integrable on every `(c, ∞)`. -/
theorem integral_Ioi_sub_interval {f : ℝ → ℝ} (hf : ∀ c, IntegrableOn f (Set.Ioi c)) (t : ℝ) :
    (∫ v in Set.Ioi (0 : ℝ), f v) - ∫ v in (0 : ℝ)..t, f v = ∫ v in Set.Ioi t, f v := by
  rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hf 0) (hf t)]
  exact sub_sub_cancel (∫ v in Set.Ioi (0 : ℝ), f v) (∫ v in Set.Ioi t, f v)

/-- Cochrane (2023), §6.4.2, p. 198 (infrastructure): `∫₀^T e^{-a u} du = (1 - e^{-a T})/a` for
`a ≠ 0`. -/
theorem intervalIntegral_exp_neg_mul {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, exp (-a * u) = (1 - exp (-a * T)) / a := by
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [intervalIntegral.integral_comp_mul_left (fun u => exp u) hna, integral_exp, mul_zero,
    exp_zero, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §6.4.4, p. 200 (infrastructure, moved here from `GrowthTheoryTVC`):
`K e^{a T} → 0` as `T → ∞` iff `a < 0`, for `K > 0`. -/
theorem tendsto_const_mul_exp_zero_iff {K a : ℝ} (hK : 0 < K) :
    Tendsto (fun T : ℝ => K * Real.exp (a * T)) atTop (𝓝 0) ↔ a < 0 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have hge : ∀ T : ℝ, 0 ≤ T → K ≤ K * Real.exp (a * T) := fun T hT => by
      have : 1 ≤ Real.exp (a * T) := Real.one_le_exp (mul_nonneg ha hT)
      nlinarith
    have hev : ∀ᶠ T in atTop, K ≤ K * Real.exp (a * T) :=
      (eventually_ge_atTop 0).mono hge
    have := ge_of_tendsto h hev
    linarith
  · intro ha
    have h1 : Tendsto (fun T : ℝ => a * T) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg ha
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul K

/-- Cochrane (2023), §6.4.4, p. 200 (infrastructure, moved here from `GrowthTheoryTVC`):
for `K > 0` and `a > 0`, `K e^{a T} → ∞`. -/
theorem tendsto_const_mul_exp_atTop {K a : ℝ} (hK : 0 < K) (ha : 0 < a) :
    Tendsto (fun T : ℝ => K * Real.exp (a * T)) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => a * T) atTop atTop := tendsto_id.const_mul_atTop ha
  exact (Real.tendsto_exp_atTop.comp h1).const_mul_atTop hK

/-- Cochrane (2023), §6.4.5, p. 201 (infrastructure, moved here from `MoneyLiquidity`):
with `a > 0`, a bounded solution satisfies the transversality condition
`e^{−a(T−t)} w_T → 0`. -/
theorem tvc_of_bounded {a C : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hC : ∀ τ, |w τ| ≤ C) (t : ℝ) :
    Tendsto (fun T => Real.exp (-a * (T - t)) * w T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T => -a * (T - t)) atTop atBot := by
    have : Tendsto (fun T : ℝ => T - t) atTop atTop := tendsto_atTop_add_const_right _ _
      tendsto_id
    exact this.const_mul_atTop_of_neg (by linarith)
  have h2 : Tendsto (fun T => Real.exp (-a * (T - t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 : Tendsto (fun T => Real.exp (-a * (T - t)) * C) atTop (𝓝 0) := by
    have := h2.mul_const C
    rwa [zero_mul] at this
  refine squeeze_zero_norm (fun T => ?_) h3
  rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC T) (Real.exp_pos _).le

end Cochrane.FiscalConstraints.ExpIntegrals

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The present-value Laffer curve

Cochrane (2023), Chapter 6, §6.1 *The present-value Laffer curve*, pp. 187–190.

A flat income tax at rate `τ` on output `y` raises revenue `τ y`. The static Laffer elasticity is
`∂ log(τ y)/∂ log τ = 1 + ∂ log y/∂ log τ` (p. 189). With output growing at rate `g` and
discount rate `r > g`, the present value of revenue is
`PV = ∫₀^∞ e^{-r u} τ y e^{g u} du = τ y/(r - g)` (p. 189), and its elasticity is
`∂ log PV/∂ log τ = 1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ` (p. 190).

All elasticities are exact derivatives (`HasDerivAt`) with respect to `log τ`, of functions of
`v = log τ` (so `τ = e^v`); the derivative of `g` with respect to `log τ` is `τ g'(τ)`.

## Main results

* `pv_tax_eq`, `pv_tax_not_integrable`: the present value formula, and its genuine divergence
  for `r ≤ g`.
* `static_elasticity`, `output_elasticity`: the static Laffer elasticity (p. 189).
* `pv_elasticity`: the present-value elasticity of the closed form (p. 190), and
  `pv_integral_elasticity`: the same for the improper integral itself.
* `pv_elasticity_zero_of`, `pv_elasticity_nonpos_iff`, `book_top_of_curve`: the top of the
  present-value Laffer curve; with `r - g = 0.01`, `∂g/∂ log τ = -0.01` and no static effect the
  elasticity is exactly zero (p. 190).
* `log_pv_hasDerivAt_g`, `log_pv_hasDerivAt_r`, `semi_elasticity_strictAntiOn`: "r closer to g
  makes the present value more sensitive" (p. 190).
* `log_tax_ratio_bounds`, `book_growth_reduction_bounds` (survey E6.3): a rise of `τ` from 50% to
  60% is a log change of `log 1.2 ∈ (0.18, 0.19)`, not 20%, so the implied growth reduction is
  between 0.18 and 0.19 percentage points rather than 0.2.
-/

namespace Cochrane.FiscalConstraints.Laffer

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals

/-- Cochrane (2023), §6.1, p. 189: the present value of tax revenue
`PV_t = ∫₀^∞ e^{-r u} τ y_t e^{g u} du = τ y_t/(r - g)` when `r > g`. -/
theorem pv_tax_eq {r g : ℝ} (h : g < r) (τ y : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (τ * y * exp (g * u)) = τ * y / (r - g) :=
  integral_exp_growth h (τ * y)

/-- Cochrane (2023), §6.1, p. 189: for `r ≤ g` and positive revenue the present value of tax
revenue is infinite (the integrand is not integrable). -/
theorem pv_tax_not_integrable {r g : ℝ} (h : r ≤ g) {τ y : ℝ} (hτy : τ * y ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => exp (-r * u) * (τ * y * exp (g * u))) (Set.Ioi 0) :=
  not_integrableOn_exp_growth h hτy

/-- Cochrane (2023), §6.1, p. 189: the output elasticity `∂ log y/∂ log τ = τ y'(τ)/y(τ)`, as the
exact derivative of `v ↦ log y(e^v)` at `v = log τ`. -/
theorem output_elasticity {y : ℝ → ℝ} {y' τ : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hd : HasDerivAt y y' τ) :
    HasDerivAt (fun v => log (y (exp v))) (τ * y' / y τ) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 := h1.log (show y (exp (log τ)) ≠ 0 by rw [he]; exact hy.ne')
  refine h2.congr_deriv ?_
  rw [he]
  ring

/-- Cochrane (2023), §6.1, p. 189: the static Laffer elasticity
`∂ log(τ y)/∂ log τ = 1 + ∂ log y/∂ log τ`, as the exact derivative of `v ↦ log(e^v y(e^v))` at
`v = log τ`. -/
theorem static_elasticity {y : ℝ → ℝ} {y' τ : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hd : HasDerivAt y y' τ) :
    HasDerivAt (fun v => log (exp v * y (exp v))) (1 + τ * y' / y τ) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 : HasDerivAt (fun v => exp v * y (exp v)) (τ * y τ + τ * (y' * τ)) (log τ) := by
    have := HasDerivAt.mul (hasDerivAt_exp (log τ)) h1
    rw [he] at this
    exact this
  have h3 := h2.log (show exp (log τ) * y (exp (log τ)) ≠ 0 by
    rw [he]; exact (mul_pos hτ hy).ne')
  refine h3.congr_deriv ?_
  rw [he]
  field_simp

/-- Cochrane (2023), §6.1, p. 190: the elasticity of the present value of tax revenue,
`∂ log PV/∂ log τ = 1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ`, as the exact derivative of
`v ↦ log(e^v y(e^v)/(r - g(e^v)))` at `v = log τ` (with `∂g/∂ log τ = τ g'(τ)`). -/
theorem pv_elasticity {y g : ℝ → ℝ} {y' g' τ r : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hr : g τ < r) (hyd : HasDerivAt y y' τ) (hgd : HasDerivAt g g' τ) :
    HasDerivAt (fun v => log (exp v * y (exp v) / (r - g (exp v))))
      (1 + τ * y' / y τ + 1 / (r - g τ) * (τ * g')) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hyd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have hg1 : HasDerivAt (fun v => g (exp v)) (g' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hgd : HasDerivAt g g' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 : HasDerivAt (fun v => exp v * y (exp v)) (τ * y τ + τ * (y' * τ)) (log τ) := by
    have := HasDerivAt.mul (hasDerivAt_exp (log τ)) h1
    rw [he] at this
    exact this
  have hden : HasDerivAt (fun v => r - g (exp v)) (-(g' * τ)) (log τ) := by
    simpa using hg1.const_sub r
  have hrg : r - g (exp (log τ)) ≠ 0 := by rw [he]; linarith
  have h3 := HasDerivAt.div h2 hden hrg
  have hpos : exp (log τ) * y (exp (log τ)) / (r - g (exp (log τ))) ≠ 0 := by
    rw [he]; exact (div_pos (mul_pos hτ hy) (by linarith)).ne'
  have h4 := h3.log hpos
  refine h4.congr_deriv ?_
  have hrg' : r - g τ ≠ 0 := by linarith
  simp only [Pi.div_apply, he]
  field_simp
  ring

/-- Cochrane (2023), §6.1, pp. 189–190: the present-value elasticity holds for the improper
integral `PV(τ) = ∫₀^∞ e^{-r u} τ y(τ) e^{g(τ) u} du` itself: `v ↦ log PV(e^v)` has derivative
`1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ` at `log τ` (the closed form holds near `τ` by
continuity of `g`). -/
theorem pv_integral_elasticity {y g : ℝ → ℝ} {y' g' τ r : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hr : g τ < r) (hyd : HasDerivAt y y' τ) (hgd : HasDerivAt g g' τ) :
    HasDerivAt (fun v => log (∫ u in Set.Ioi (0 : ℝ),
        exp (-r * u) * (exp v * y (exp v) * exp (g (exp v) * u))))
      (1 + τ * y' / y τ + 1 / (r - g τ) * (τ * g')) (log τ) := by
  refine (pv_elasticity hτ hy hr hyd hgd).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun v => g (exp v)) (log τ) := by
    have : ContinuousAt g (exp (log τ)) := by rw [exp_log hτ]; exact hgd.continuousAt
    exact this.comp (continuous_exp.continuousAt)
  have hev : ∀ᶠ v in 𝓝 (log τ), g (exp v) < r := by
    apply hc.eventually (gt_mem_nhds _)
    change g (exp (log τ)) < r
    rw [exp_log hτ]; exact hr
  filter_upwards [hev] with v hv
  rw [pv_tax_eq hv]

/-- Cochrane (2023), §6.1, p. 190: with no static effect (`∂ log y/∂ log τ = 0`) and
`∂g/∂ log τ = -(r - g)`, the present-value elasticity is exactly zero: the top of the present-value
Laffer curve. -/
theorem pv_elasticity_zero_of {r g dg : ℝ} (hrg : g < r) (hdg : dg = -(r - g)) :
    1 + 0 + 1 / (r - g) * dg = 0 := by
  have : r - g ≠ 0 := by linarith
  rw [hdg]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: the present-value elasticity
`1 + ε_y + (1/(r - g)) ∂g/∂ log τ` is nonpositive (we are at or beyond the top of the
present-value Laffer curve) iff `∂g/∂ log τ ≤ -(r - g)(1 + ε_y)`. -/
theorem pv_elasticity_nonpos_iff {r g εy dg : ℝ} (hrg : g < r) :
    1 + εy + 1 / (r - g) * dg ≤ 0 ↔ dg ≤ -(r - g) * (1 + εy) := by
  have hpos : 0 < r - g := by linarith
  have key : 1 + εy + 1 / (r - g) * dg = (dg + (r - g) * (1 + εy)) / (r - g) := by
    field_simp
    ring
  rw [key, div_nonpos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hpos.le⟩

/-- Cochrane (2023), §6.1, p. 190: the book's example: `r - g = 0.01` and
`dg/d log τ = -0.01` put us at the top of the present-value Laffer curve with no static effect. -/
theorem book_top_of_curve : (1 : ℝ) + 0 + 1 / (0.01 : ℝ) * (-0.01) = 0 := by
  norm_num

/-- Cochrane (2023), §6.1, p. 190: the semi-elasticity of the present value `c/(r - g)` with
respect to `g` is `1/(r - g)`: exact derivative of `g ↦ log(c/(r - g))`. -/
theorem log_pv_hasDerivAt_g {c r g : ℝ} (hc : 0 < c) (hrg : g < r) :
    HasDerivAt (fun h => log (c / (r - h))) (1 / (r - g)) g := by
  have hd : HasDerivAt (fun h => r - h) (-1) g := by simpa using (hasDerivAt_id g).const_sub r
  have h1 := (HasDerivAt.div (hasDerivAt_const g c) hd (by linarith : r - g ≠ 0)).log
    (div_pos hc (by linarith)).ne'
  convert h1 using 1
  have : r - g ≠ 0 := by linarith
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: the semi-elasticity of the present value `c/(r - g)` with
respect to `r` is `-1/(r - g)`. -/
theorem log_pv_hasDerivAt_r {c r g : ℝ} (hc : 0 < c) (hrg : g < r) :
    HasDerivAt (fun q => log (c / (q - g))) (-(1 / (r - g))) r := by
  have hd : HasDerivAt (fun q => q - g) 1 r := by simpa using (hasDerivAt_id r).sub_const g
  have h1 := (HasDerivAt.div (hasDerivAt_const r c) hd (by linarith : r - g ≠ 0)).log
    (div_pos hc (by linarith)).ne'
  convert h1 using 1
  have : r - g ≠ 0 := by linarith
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: "r closer to g makes the present value more sensitive": the
semi-elasticity `1/(r - g)` is strictly decreasing in the spread `r - g > 0`. -/
theorem semi_elasticity_strictAntiOn :
    StrictAntiOn (fun d : ℝ => 1 / d) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact one_div_lt_one_div_of_lt ha hab

/-- Cochrane (2023), §6.1, p. 190 (survey E6.3): a tax-rate rise from 50% to 60% is a log change
`log(0.6/0.5) = log 1.2` with `0.18 < log 1.2 < 0.19`, not the 20% used in the text. -/
theorem log_tax_ratio_bounds :
    (0.18 : ℝ) < log (0.6 / 0.5) ∧ log (0.6 / 0.5) < 0.19 := by
  have h12 : (0.6 : ℝ) / 0.5 = 1.2 := by norm_num
  rw [h12]
  constructor
  · rw [lt_log_iff_exp_lt (by norm_num)]
    have hb := Real.exp_bound (x := 0.18) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have := (abs_le.1 hb).2
    linarith
  · rw [log_lt_iff_lt_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (x := 0.19) (by norm_num)
    linarith

/-- Cochrane (2023), §6.1, p. 190 (survey E6.3): with `dg/d log τ = -0.01`, the growth reduction
implied by the tax-rate rise from 50% to 60% is `0.01 · log 1.2`, strictly between 0.18 and
0.19 percentage points (the book's "0.2 percentage point" uses the 20% arithmetic change). -/
theorem book_growth_reduction_bounds :
    (0.0018 : ℝ) < 0.01 * log (0.6 / 0.5) ∧ 0.01 * log (0.6 / 0.5) < 0.0019 ∧
      0.01 * log (0.6 / 0.5) ≠ (0.002 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_tax_ratio_bounds
  refine ⟨by linarith, by linarith, by intro h; linarith⟩

end Cochrane.FiscalConstraints.Laffer

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discount rates and growth

Cochrane (2023), Chapter 6, §6.2 *Discount rates*, eqs. (6.1)–(6.2), pp. 191–193, and the
consumer first-order condition (6.6) with population growth, §6.4.4, pp. 199–200.

The representative consumer's first-order condition links the real rate to growth,
`r = δ + γ g` (6.1). The value of debt with a constant surplus/GDP ratio is
`B/(P y) = (s/y)/(r - g)` (6.2). Substituting (6.1), the value is `(s/y)/(δ + (γ - 1) g)`: for
`γ = 1` it does not depend on `g`, for `γ > 1` it falls with `g` (p. 191).

## Main results

* `euler_discrete_iff`: the discrete-time Euler equation `e^{-δ}(1+g)^{-γ}(1+r) = 1` holds iff
  `log(1+r) = δ + γ log(1+g)` (the exact log form of (6.1)).
* `marginalValue_hasDerivAt`, `euler_continuous_iff`: in continuous time the discounted marginal
  utility of a unit invested at `r`, `e^{-δt} c(t)^{-γ} e^{rt}`, is stationary at `t` iff
  `r = δ + γ ċ/c`; `euler_exponential_iff`: along `c(t) = c₀ e^{gt}` it is constant iff
  `r = δ + γ g` (6.1), (6.6).
* `value_of_debt_eq` (6.2), `value_of_debt_not_integrable`.
* `value_indep_of_g` (`γ = 1`), `value_hasDerivAt`, `value_strictAntiOn` (`γ > 1`),
  `value_strictMonoOn` (`γ < 1`), `log_value_hasDerivAt` (cash-flow effect `1/(r-g)` minus
  discount-rate effect `γ/(r-g)`).
* `percapita_growth`, `euler_population_iff`, `r_lt_g_population_iff`: with population growth `n`
  the per-capita first-order condition is `r = δ + γ(g - n)` (p. 200), so `r < g` iff
  `δ + (γ - 1) g < γ n`.
-/

namespace Cochrane.FiscalConstraints.DiscountGrowth

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals

/-- Cochrane (2023), eq. (6.1), p. 191 (discrete-time exact form): with gross growth `1 + g > 0`
and gross return `1 + r > 0`, the consumer's Euler equation `e^{-δ}(1+g)^{-γ}(1+r) = 1` holds iff
`log(1+r) = δ + γ log(1+g)`. -/
theorem euler_discrete_iff {r g : ℝ} (hr : 0 < 1 + r) (hg : 0 < 1 + g) (δ γ : ℝ) :
    exp (-δ) * (1 + g) ^ (-γ) * (1 + r) = 1 ↔ log (1 + r) = δ + γ * log (1 + g) := by
  have h : exp (-δ) * (1 + g) ^ (-γ) * (1 + r) =
      exp (-δ - γ * log (1 + g) + log (1 + r)) := by
    rw [rpow_def_of_pos hg, exp_add, exp_log hr, sub_eq_add_neg, exp_add]
    ring_nf
  rw [h, exp_eq_one_iff]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), eq. (6.1), p. 191: the time-`t` value, in marginal utility, of a unit
invested at the real rate `r`: `λ(t) = e^{-δt} c(t)^{-γ} e^{rt}`. -/
noncomputable def marginalValue (δ γ r : ℝ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (-δ * t) * c t ^ (-γ) * exp (r * t)

/-- Cochrane (2023), eq. (6.1), p. 191: exact derivative of `λ(t) = e^{-δt} c(t)^{-γ} e^{rt}`,
`λ'(t) = λ(t) (r - δ - γ ċ/c)`. -/
theorem marginalValue_hasDerivAt {δ γ r : ℝ} {c : ℝ → ℝ} {c' t : ℝ} (hc : 0 < c t)
    (hd : HasDerivAt c c' t) :
    HasDerivAt (marginalValue δ γ r c)
      (marginalValue δ γ r c t * (r - δ - γ * (c' / c t))) t := by
  have h1 : HasDerivAt (fun s => exp (-δ * s)) (exp (-δ * t) * -δ) t := by
    simpa using ((hasDerivAt_id t).const_mul (-δ)).exp
  have h3 : HasDerivAt (fun s => exp (r * s)) (exp (r * t) * r) t := by
    simpa using ((hasDerivAt_id t).const_mul r).exp
  have h2 : HasDerivAt (fun s => c s ^ (-γ)) (c' * (-γ) * c t ^ (-γ - 1)) t :=
    hd.rpow_const (Or.inl hc.ne')
  have h := (h1.mul h2).mul h3
  unfold marginalValue
  refine h.congr_deriv ?_
  have hcpow : c t ^ (-γ - 1) = c t ^ (-γ) / c t := by
    rw [rpow_sub hc, rpow_one]
  rw [hcpow]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), eq. (6.1), p. 191: the consumer is indifferent to shifting consumption at
`t` (the marginal value `λ` is stationary, `λ'(t) = 0`) iff `r = δ + γ ċ/c`. -/
theorem euler_continuous_iff {δ γ r : ℝ} {c : ℝ → ℝ} {c' t : ℝ} (hc : 0 < c t)
    (hd : HasDerivAt c c' t) :
    HasDerivAt (marginalValue δ γ r c) 0 t ↔ r = δ + γ * (c' / c t) := by
  have h := marginalValue_hasDerivAt (δ := δ) (γ := γ) (r := r) hc hd
  have hpos : 0 < marginalValue δ γ r c t := by
    unfold marginalValue
    exact mul_pos (mul_pos (exp_pos _) (rpow_pos_of_pos hc _)) (exp_pos _)
  constructor
  · intro h0
    have := h.unique h0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpos.ne'
    · linarith
  · intro hr
    have : r - δ - γ * (c' / c t) = 0 := by linarith
    rw [this, mul_zero] at h
    exact h

/-- Cochrane (2023), eqs. (6.1), p. 191, and (6.6), p. 199: along consumption growing at rate
`g`, `c(t) = c₀ e^{g t}` with `c₀ > 0`, the marginal value `λ(t)` is constant over time iff
`r = δ + γ g`. -/
theorem euler_exponential_iff {c₀ : ℝ} (hc₀ : 0 < c₀) (δ γ r g : ℝ) :
    (∀ t, marginalValue δ γ r (fun s => c₀ * exp (g * s)) t =
        marginalValue δ γ r (fun s => c₀ * exp (g * s)) 0) ↔ r = δ + γ * g := by
  have key : ∀ t, marginalValue δ γ r (fun s => c₀ * exp (g * s)) t =
      c₀ ^ (-γ) * exp ((r - δ - γ * g) * t) := by
    intro t
    unfold marginalValue
    rw [mul_rpow hc₀.le (exp_pos _).le, ← exp_mul]
    have : exp (-δ * t) * (c₀ ^ (-γ) * exp (g * t * -γ)) * exp (r * t) =
        c₀ ^ (-γ) * (exp (-δ * t) * exp (g * t * -γ) * exp (r * t)) := by ring
    rw [this, ← exp_add, ← exp_add]
    ring_nf
  simp only [key, mul_zero, exp_zero, mul_one]
  have hc : 0 < c₀ ^ (-γ) := rpow_pos_of_pos hc₀ _
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one] at h1
    have h2 : exp (r - δ - γ * g) = 1 := by
      have := mul_left_cancel₀ hc.ne' (h1.trans (mul_one _).symm)
      exact this
    rw [exp_eq_one_iff] at h2
    linarith
  · intro hr t
    have : r - δ - γ * g = 0 := by linarith
    rw [this, zero_mul, exp_zero, mul_one]

/-- Cochrane (2023), eq. (6.2), p. 191: with output growing at `g`, `y(t+u) = y(t) e^{g u}`, and a
constant surplus/GDP ratio `σ = s/y`, the value of debt is
`B_t/(P_t y_t) = ∫₀^∞ e^{-r u} σ (y_{t+u}/y_t) du = σ/(r - g)` for `r > g`. -/
theorem value_of_debt_eq {r g σ t : ℝ} (h : g < r) {y : ℝ → ℝ} (hy : y t ≠ 0)
    (hgrow : ∀ u, y (t + u) = y t * exp (g * u)) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (σ * (y (t + u) / y t)) = σ / (r - g) := by
  have : ∀ u, σ * (y (t + u) / y t) = σ * exp (g * u) := by
    intro u
    rw [hgrow u]
    field_simp
  simp_rw [this]
  exact integral_exp_growth h σ

/-- Cochrane (2023), eq. (6.2), p. 191: for `r ≤ g` and `σ ≠ 0` the integral in (6.2) diverges. -/
theorem value_of_debt_not_integrable {r g σ t : ℝ} (h : r ≤ g) (hσ : σ ≠ 0) {y : ℝ → ℝ}
    (hy : y t ≠ 0) (hgrow : ∀ u, y (t + u) = y t * exp (g * u)) :
    ¬ IntegrableOn (fun u => exp (-r * u) * (σ * (y (t + u) / y t))) (Set.Ioi 0) := by
  have : ∀ u, σ * (y (t + u) / y t) = σ * exp (g * u) := by
    intro u
    rw [hgrow u]
    field_simp
  simp_rw [this]
  exact not_integrableOn_exp_growth h hσ

/-- Cochrane (2023), §6.2, p. 191: substituting `r = δ + γ g` (6.1) into (6.2), the value of debt
is `σ/(δ + γ g - g)`. -/
noncomputable def valueOfDebt (σ δ γ g : ℝ) : ℝ := σ / (δ + γ * g - g)

/-- Cochrane (2023), §6.2, p. 191: if `γ = 1`, `r` and `g` move one for one and the value of debt
does not depend on growth. -/
theorem value_indep_of_g (σ δ g g' : ℝ) : valueOfDebt σ δ 1 g = valueOfDebt σ δ 1 g' := by
  unfold valueOfDebt
  ring_nf

/-- Cochrane (2023), §6.2, p. 191: the exact derivative of the value of debt with respect to
growth, `∂/∂g [σ/(δ + (γ-1) g)] = -σ(γ - 1)/(δ + (γ - 1) g)²`. -/
theorem value_hasDerivAt {σ δ γ g : ℝ} (hpos : 0 < δ + γ * g - g) :
    HasDerivAt (valueOfDebt σ δ γ) (-(σ * (γ - 1)) / (δ + γ * g - g) ^ 2) g := by
  have hd : HasDerivAt (fun h => δ + γ * h - h) (γ - 1) g := by
    have h1 : HasDerivAt (fun h => δ + γ * h) γ g := by
      simpa using ((hasDerivAt_id' g).const_mul γ).const_add δ
    exact HasDerivAt.sub h1 (hasDerivAt_id' g)
  have h := (hasDerivAt_const g σ).div hd hpos.ne'
  unfold valueOfDebt
  refine h.congr_deriv ?_
  ring

/-- Cochrane (2023), §6.2, p. 191: with `γ > 1` and positive surpluses, higher growth lowers the
value of debt (on the region `r > g`, i.e. `δ + (γ-1) g > 0`). -/
theorem value_strictAntiOn {σ δ γ : ℝ} (hσ : 0 < σ) (hγ : 1 < γ) :
    StrictAntiOn (valueOfDebt σ δ γ) {g | 0 < δ + γ * g - g} := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < δ + γ * a - a := ha
  have hb' : (0 : ℝ) < δ + γ * b - b := hb
  unfold valueOfDebt
  apply div_lt_div_of_pos_left hσ ha'
  nlinarith

/-- Cochrane (2023), §6.2, p. 191: with `γ < 1` and positive surpluses, higher growth raises the
value of debt (the cash-flow effect dominates). -/
theorem value_strictMonoOn {σ δ γ : ℝ} (hσ : 0 < σ) (hγ : γ < 1) :
    StrictMonoOn (valueOfDebt σ δ γ) {g | 0 < δ + γ * g - g} := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < δ + γ * a - a := ha
  have hb' : (0 : ℝ) < δ + γ * b - b := hb
  unfold valueOfDebt
  apply div_lt_div_of_pos_left hσ hb'
  nlinarith

/-- Cochrane (2023), §6.2, p. 191: "the discount rate effect is larger than the cashflow
effect": the semi-elasticity of the value of debt with respect to `g` is the cash-flow effect
`1/(r - g)` minus the discount-rate effect `γ/(r - g)`, with `r - g = δ + (γ - 1) g`. -/
theorem log_value_hasDerivAt {σ δ γ g : ℝ} (hσ : 0 < σ) (hpos : 0 < δ + γ * g - g) :
    HasDerivAt (fun h => log (valueOfDebt σ δ γ h))
      (1 / (δ + γ * g - g) - γ / (δ + γ * g - g)) g := by
  have h := (value_hasDerivAt (σ := σ) hpos).log
    (by unfold valueOfDebt; exact (div_pos hσ hpos).ne')
  refine h.congr_deriv ?_
  unfold valueOfDebt
  field_simp
  ring

/-- Cochrane (2023), §6.4.4, p. 200: with aggregate consumption `C₀ e^{g t}` and population
`N₀ e^{n t}`, per-capita consumption grows at `g - n`. -/
theorem percapita_growth {C₀ N₀ : ℝ} (hN : N₀ ≠ 0) (g n t : ℝ) :
    C₀ * exp (g * t) / (N₀ * exp (n * t)) = C₀ / N₀ * exp ((g - n) * t) := by
  rw [sub_mul, exp_sub]
  field_simp

/-- Cochrane (2023), §6.4.4, p. 200: the per-capita first-order condition with population growth:
along per-capita consumption `(C₀/N₀) e^{(g - n) t}` the marginal value is constant iff
`r = δ + γ (g - n)`. -/
theorem euler_population_iff {C₀ N₀ : ℝ} (hC : 0 < C₀) (hN : 0 < N₀) (δ γ r g n : ℝ) :
    (∀ t, marginalValue δ γ r (fun s => C₀ / N₀ * exp ((g - n) * s)) t =
        marginalValue δ γ r (fun s => C₀ / N₀ * exp ((g - n) * s)) 0) ↔
      r = δ + γ * (g - n) :=
  euler_exponential_iff (div_pos hC hN) δ γ r (g - n)

/-- Cochrane (2023), §6.4.4, p. 200: with `r = δ + γ (g - n)`, `r < g` iff
`δ + (γ - 1) g < γ n`: population growth makes `r < g` easier. -/
theorem r_lt_g_population_iff {δ γ r g n : ℝ} (hr : r = δ + γ * (g - n)) :
    r < g ↔ δ + (γ - 1) * g < γ * n := by
  rw [hr]
  constructor <;> intro h <;> linarith

end Cochrane.FiscalConstraints.DiscountGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Crashes and breakouts: Miller's two-period model

Cochrane (2023), Chapter 6, §6.3 *Crashes and breakouts*, pp. 193–195.

The two-period model of §1.3 (budget (1.2) `B₋₁ = P₀ s₀ + Q₀ B₀`, bond price (1.3)
`Q₀ = 1/(1+i₀) = β P₀/P₁` under perfect foresight) with the fiscal rule of §2.5.1 capped by a
maximum surplus: `s₁ = min(B₀/P*, s₁^max)`, and terminal condition `B₀/P₁ = s₁`. The central bank
sets `i₀`. Write `q = β(1 + i₀)`.

* Unconstrained regime (`s₁ < s^max`): `P₁ = P*`, `P₀ = P*/q`, independent of `s₀`; a higher
  `i₀` lowers `P₀`.
* Constrained regime (`s₁ = s^max`): `B₋₁/P₀ = s₀ + β s^max`, so deficits pass into `P₀`, `i₀`
  has no effect on `P₀` and only raises `P₁`.
* The regime switches endogenously: `s₁ < s^max` iff `q B₋₁/P* - s₀ < β s^max` (p. 194).

We prove these claims, the global formula `P₀ = max(P*/q, B₋₁/(s₀ + β s^max))` (continuous and
monotone in debt, deficits and the interest rate), existence iff `s₀ + β s^max > 0`, and exact
comparative statics in the interior of each regime. The book's claims need outstanding debt
`B₀ ≠ 0`: when `s₀ > 0` there is also an equilibrium with `B₀ = 0` (the government retires all
debt at date 0, and the rule `s₁ = B₀/P*` then does not pin `P₁`), with `s₁ = 0 < s^max` but
`P₁ ≠ P*` (`degenerate_equilibrium`, `degenerate_price0_ne`). Miller's learning model (p. 195)
is a verbal summary and is not formalised.

## Main results

* `IsEquilibrium`, `fisher`, `valuation`, `isEquilibrium_iff` (the book's equilibrium
  conditions follow from budget, bond pricing and the rule, and conversely).
* `unconstrained_regime`, `constrained_regime`, `boundary_iff`, `boundary_iff_debt`.
* `price0`, `eq_price0`, `isEquilibrium_price0`, `exists_equilibrium_iff`, `price0_unique`.
* `price0_antitoneOn_s0`, `price0_antitoneOn_i0`, `price0_monotone_debt`, `price1_monotoneOn_i0`,
  `continuousOn_price0_s0`, `continuousOn_price0_i0`.
* `hasDerivAt_price0_s0_unconstrained` (`∂P₀/∂s₀ = 0`), `hasDerivAt_price0_i0_unconstrained`
  (`∂P₀/∂i₀ < 0`), `hasDerivAt_price1_i0_unconstrained` (`∂P₁/∂i₀ = 0`),
  `hasDerivAt_price0_s0_constrained` (`∂P₀/∂s₀ < 0`), `hasDerivAt_price0_i0_constrained`
  (`∂P₀/∂i₀ = 0`), `hasDerivAt_price1_i0_constrained` (`∂P₁/∂i₀ > 0`).
* `degenerate_equilibrium`, `degenerate_price0_ne`.
-/

namespace Cochrane.FiscalConstraints.Crash

open Filter Topology

/-- Cochrane (2023), §6.3, p. 194: the capped fiscal rule `s₁ = min(B₀/P*, s₁^max)`. -/
noncomputable def surplus1 (Pst smax B0 : ℝ) : ℝ := min (B0 / Pst) smax

/-- Cochrane (2023), §6.3, p. 194 (with Ch. 1 (1.2), (1.3), p. 8): an equilibrium `(P₀, P₁, B₀)`
given `β`, the target `P*`, the cap `s^max`, initial debt `B₋₁`, the surplus `s₀` and the
interest-rate target `i₀`: positive price levels, the budget `B₋₁ = P₀ s₀ + B₀/(1+i₀)`, the bond
price `1/(1+i₀) = β P₀/P₁`, and the terminal condition `B₀/P₁ = s₁` with the capped rule. -/
def IsEquilibrium (β Pst smax Bm s0 i0 P0 P1 B0 : ℝ) : Prop :=
  0 < P0 ∧ 0 < P1 ∧ Bm = P0 * s0 + B0 / (1 + i0) ∧ 1 / (1 + i0) = β * P0 / P1 ∧
    B0 / P1 = surplus1 Pst smax B0

variable {β Pst smax Bm s0 i0 P0 P1 B0 : ℝ}

/-- Cochrane (2023), §6.3, p. 194: in equilibrium the gross nominal rate is positive,
`1 + i₀ > 0` (the bond price `β P₀/P₁` is positive). -/
theorem one_add_pos (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    0 < 1 + i0 := by
  obtain ⟨hP0, hP1, -, hQ, -⟩ := h
  have : 0 < 1 / (1 + i0) := by rw [hQ]; positivity
  exact one_div_pos.1 this

/-- Cochrane (2023), eq. (1.9) used in §6.3, p. 194: the interest-rate target fixes expected
inflation, `P₁ = β(1 + i₀) P₀`. -/
theorem fisher (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    P1 = β * (1 + i0) * P0 := by
  have hi := one_add_pos hβ h
  obtain ⟨hP0, hP1, -, hQ, -⟩ := h
  field_simp at hQ
  linarith

/-- Cochrane (2023), §6.3, p. 194: in equilibrium the valuation equation
`B₋₁/P₀ = s₀ + β s₁` holds, with `s₁ = B₀/P₁`. -/
theorem valuation (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    Bm / P0 = s0 + β * (B0 / P1) := by
  have hi := one_add_pos hβ h
  have hf := fisher hβ h
  obtain ⟨hP0, hP1, hB, -, -⟩ := h
  rw [hB, hf]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: "Equilibrium still consists of `B₀/P₁ = s₁`,
`B₋₁/P₀ = s₀ + β s₁`": given positive prices and `1 + i₀ > 0`, the budget/pricing/rule
definition is equivalent to the Fisher relation, the terminal condition and the valuation
equation. -/
theorem isEquilibrium_iff (hβ : 0 < β) (hP0 : 0 < P0) (hP1 : 0 < P1) (hi : 0 < 1 + i0) :
    IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0 ↔
      P1 = β * (1 + i0) * P0 ∧ B0 / P1 = surplus1 Pst smax B0 ∧
        Bm / P0 = s0 + β * (B0 / P1) := by
  constructor
  · intro h
    exact ⟨fisher hβ h, h.2.2.2.2, valuation hβ h⟩
  · rintro ⟨hf, hs, hv⟩
    refine ⟨hP0, hP1, ?_, ?_, hs⟩
    · rw [hf] at hv
      field_simp at hv
      field_simp
      linarith
    · rw [hf]
      field_simp

/-- Cochrane (2023), §6.3, p. 194: in the unconstrained regime `s₁ < s^max` (with outstanding
debt `B₀ ≠ 0`) the fiscal rule delivers `P₁ = P*`, and then `P₀ = P*/(β(1 + i₀))`, unaffected by
`s₀`. -/
theorem unconstrained_regime (hβ : 0 < β) (hPst : 0 < Pst)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0)
    (hs : surplus1 Pst smax B0 < smax) :
    P1 = Pst ∧ P0 = Pst / (β * (1 + i0)) := by
  have hi := one_add_pos hβ h
  have hf := fisher hβ h
  obtain ⟨hP0, hP1, -, -, hT⟩ := h
  have hlt : B0 / Pst < smax := by
    unfold surplus1 at hs
    rcases min_lt_iff.1 hs with h' | h'
    · exact h'
    · exact absurd h' (lt_irrefl _)
  have hs1 : surplus1 Pst smax B0 = B0 / Pst := min_eq_left hlt.le
  rw [hs1] at hT
  have hP : P1 = Pst := by
    rw [div_eq_div_iff hP1.ne' hPst.ne'] at hT
    exact (mul_left_cancel₀ hB0 (by linarith : B0 * Pst = B0 * P1)).symm
  refine ⟨hP, ?_⟩
  rw [← hP, hf]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: in the constrained regime `s₁ = s^max`,
`B₋₁/P₀ = s₀ + β s^max` and `B₀/P₁ = s^max`. -/
theorem constrained_regime (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0)
    (hs : surplus1 Pst smax B0 = smax) :
    Bm / P0 = s0 + β * smax ∧ B0 / P1 = smax := by
  have hv := valuation hβ h
  have hT := h.2.2.2.2
  rw [hT, hs] at hv
  exact ⟨hv, hT.trans hs⟩

/-- Cochrane (2023), §6.3, p. 194: the regime boundary. With outstanding debt `B₀ ≠ 0`, positive
initial debt and a positive cap, `s₁ < s^max` iff `β(1 + i₀) B₋₁/P* - s₀ < β s^max`. -/
theorem boundary_iff (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    surplus1 Pst smax B0 < smax ↔ β * (1 + i0) * Bm / Pst - s0 < β * smax := by
  have hi := one_add_pos hβ h
  have hv := valuation hβ h
  have hf := fisher hβ h
  have hP0 := h.1
  have hP1 := h.2.1
  have hT := h.2.2.2.2
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  constructor
  · intro hs
    obtain ⟨-, hP⟩ := unconstrained_regime hβ hPst h hB0 hs
    rw [hT, hP] at hv
    have e : Bm / (Pst / (β * (1 + i0))) = β * (1 + i0) * Bm / Pst := by
      field_simp
    rw [e] at hv
    nlinarith
  · intro hc
    by_contra hns
    have hs1 : surplus1 Pst smax B0 = smax := by
      unfold surplus1 at hns ⊢
      exact min_eq_right (by
        by_contra h'
        exact hns (min_lt_iff.2 (Or.inl (lt_of_not_ge h'))))
    have hge : smax ≤ B0 / Pst := by
      unfold surplus1 at hs1
      by_contra h'
      push Not at h'
      rw [min_eq_left h'.le] at hs1
      linarith
    rw [hT, hs1] at hv
    have hB0' : B0 = P1 * smax := by
      have := hT.trans hs1
      field_simp at this
      linarith
    have hP1ge : Pst ≤ P1 := by
      rw [hB0', le_div_iff₀ hPst] at hge
      nlinarith
    have hP0ge : Pst / (β * (1 + i0)) ≤ P0 := by
      rw [div_le_iff₀ hq]
      nlinarith
    have : Bm / P0 ≤ β * (1 + i0) * Bm / Pst := by
      rw [div_le_div_iff₀ hP0 hPst]
      rw [div_le_iff₀ hq] at hP0ge
      nlinarith
    linarith

/-- Cochrane (2023), §6.3, p. 194: "a lot of outstanding debt `B₋₁`" (printed `B₁`, survey E6.4):
the economy is in the unconstrained regime iff initial debt is below the threshold
`P*(s₀ + β s^max)/(β(1 + i₀))`. -/
theorem boundary_iff_debt (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    surplus1 Pst smax B0 < smax ↔ Bm < Pst * (s0 + β * smax) / (β * (1 + i0)) := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ (one_add_pos hβ h)
  rw [boundary_iff hβ hPst hsmax hBm h hB0, lt_div_iff₀ hq, sub_lt_iff_lt_add,
    div_lt_iff₀ hPst]
  constructor <;> intro h' <;> nlinarith

/-- Cochrane (2023), §6.3, p. 194: the global price-level formula
`P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + β s^max))`. -/
noncomputable def price0 (β Pst smax Bm s0 i0 : ℝ) : ℝ :=
  max (Pst / (β * (1 + i0))) (Bm / (s0 + β * smax))

/-- Cochrane (2023), §6.3, p. 194: the date-1 price level implied by the formula,
`P₁ = β(1 + i₀) P₀`. -/
noncomputable def price1 (β Pst smax Bm s0 i0 : ℝ) : ℝ :=
  β * (1 + i0) * price0 β Pst smax Bm s0 i0

/-- Cochrane (2023), §6.3, p. 194: in the unconstrained region the formula gives
`P₀ = P*/(β(1 + i₀))`. -/
theorem price0_eq_left (hq : 0 < β * (1 + i0)) (hPst : 0 < Pst) (hpos : 0 < s0 + β * smax)
    (hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax) :
    price0 β Pst smax Bm s0 i0 = Pst / (β * (1 + i0)) := by
  unfold price0
  refine max_eq_left ?_
  rw [div_le_div_iff₀ hpos hq]
  rw [sub_le_iff_le_add, div_le_iff₀ hPst] at hc
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: in the constrained region the formula gives
`P₀ = B₋₁/(s₀ + β s^max)`. -/
theorem price0_eq_right (hq : 0 < β * (1 + i0)) (hPst : 0 < Pst) (hpos : 0 < s0 + β * smax)
    (hc : β * smax ≤ β * (1 + i0) * Bm / Pst - s0) :
    price0 β Pst smax Bm s0 i0 = Bm / (s0 + β * smax) := by
  unfold price0
  refine max_eq_right ?_
  rw [div_le_div_iff₀ hq hpos]
  rw [le_sub_iff_add_le, le_div_iff₀ hPst] at hc
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: every equilibrium with outstanding debt `B₀ ≠ 0` has
`P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + β s^max))`: the two regimes of §2.5.1 emerge endogenously
from one formula. -/
theorem eq_price0 (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    P0 = price0 β Pst smax Bm s0 i0 := by
  have hi := one_add_pos hβ h
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  have hv := valuation hβ h
  have hP0 := h.1
  have hT := h.2.2.2.2
  have hs1le : surplus1 Pst smax B0 ≤ smax := min_le_right _ _
  have hpos : 0 < s0 + β * smax := by
    have : 0 < Bm / P0 := div_pos hBm hP0
    rw [hT] at hv
    nlinarith
  by_cases hs : surplus1 Pst smax B0 < smax
  · have hc := (boundary_iff hβ hPst hsmax hBm h hB0).1 hs
    rw [price0_eq_left hq hPst hpos hc.le]
    exact (unconstrained_regime hβ hPst h hB0 hs).2
  · have hs1 : surplus1 Pst smax B0 = smax := le_antisymm hs1le (not_lt.1 hs)
    have hc : β * smax ≤ β * (1 + i0) * Bm / Pst - s0 := by
      by_contra h'
      exact hs ((boundary_iff hβ hPst hsmax hBm h hB0).2 (lt_of_not_ge h'))
    rw [price0_eq_right hq hPst hpos hc]
    have := (constrained_regime hβ h hs1).1
    field_simp at this ⊢
    linarith

/-- Cochrane (2023), §6.3, p. 194: when `s₀ + β s^max > 0` the formula is an equilibrium price
level: with `P₁ = β(1 + i₀) P₀` and `B₀ = P₁ (B₋₁/P₀ - s₀)/β` all conditions hold. -/
theorem isEquilibrium_price0 (hβ : 0 < β) (hPst : 0 < Pst) (hBm : 0 < Bm)
    (hsmax : 0 ≤ smax) (hi : 0 < 1 + i0) (hpos : 0 < s0 + β * smax) :
    IsEquilibrium β Pst smax Bm s0 i0 (price0 β Pst smax Bm s0 i0)
      (price1 β Pst smax Bm s0 i0)
      (price1 β Pst smax Bm s0 i0 * ((Bm / price0 β Pst smax Bm s0 i0 - s0) / β)) := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  set F := price0 β Pst smax Bm s0 i0 with hF
  have hFpos : 0 < F := lt_of_lt_of_le (div_pos hPst hq) (le_max_left _ _)
  have hP1pos : 0 < β * (1 + i0) * F := mul_pos hq hFpos
  have hP1 : price1 β Pst smax Bm s0 i0 = β * (1 + i0) * F := rfl
  rw [hP1, isEquilibrium_iff hβ hFpos hP1pos hi]
  have hB : β * (1 + i0) * F * ((Bm / F - s0) / β) / (β * (1 + i0) * F) = (Bm / F - s0) / β := by
    field_simp
  refine ⟨rfl, ?_, ?_⟩
  · rw [hB]
    unfold surplus1
    by_cases hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax
    · have hFe : F = Pst / (β * (1 + i0)) := price0_eq_left hq hPst hpos hc
      have e1 : (Bm / F - s0) / β = (β * (1 + i0) * Bm / Pst - s0) / β := by
        rw [hFe]; field_simp
      have e2 : β * (1 + i0) * F * ((Bm / F - s0) / β) / Pst = (Bm / F - s0) / β := by
        rw [hFe]; field_simp
      rw [e2]
      refine (min_eq_left ?_).symm
      rw [e1, div_le_iff₀ hβ]
      linarith
    · push Not at hc
      have hFe : F = Bm / (s0 + β * smax) := price0_eq_right hq hPst hpos hc.le
      have e1 : (Bm / F - s0) / β = smax := by
        rw [hFe]; field_simp; ring
      rw [e1]
      refine (min_eq_right ?_).symm
      have hFge : Pst / (β * (1 + i0)) ≤ F := le_max_left _ _
      rw [div_le_iff₀ hq] at hFge
      rw [le_div_iff₀ hPst]
      nlinarith [mul_le_mul_of_nonneg_left hFge hsmax]
  · rw [hB]
    field_simp
    ring

/-- Cochrane (2023), §6.3, p. 194: an equilibrium exists iff `s₀ + β s^max > 0`: if even the
maximal future surplus cannot cover the debt left after `s₀`, no price level works. -/
theorem exists_equilibrium_iff (hβ : 0 < β) (hPst : 0 < Pst) (hBm : 0 < Bm)
    (hsmax : 0 ≤ smax) (hi : 0 < 1 + i0) :
    (∃ P0 P1 B0, IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) ↔ 0 < s0 + β * smax := by
  constructor
  · rintro ⟨P0, P1, B0, h⟩
    have hv := valuation hβ h
    have hT := h.2.2.2.2
    have hle : surplus1 Pst smax B0 ≤ smax := min_le_right _ _
    have : 0 < Bm / P0 := div_pos hBm h.1
    rw [hT] at hv
    nlinarith
  · intro hpos
    exact ⟨_, _, _, isEquilibrium_price0 hβ hPst hBm hsmax hi hpos⟩

/-- Cochrane (2023), §6.3, p. 194: uniqueness: any two equilibria with outstanding debt have the
same price levels. -/
theorem price0_unique (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    {P0' P1' B0' : ℝ} (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0)
    (h' : IsEquilibrium β Pst smax Bm s0 i0 P0' P1' B0') (hB0' : B0' ≠ 0) :
    P0 = P0' ∧ P1 = P1' := by
  have e := (eq_price0 hβ hPst hsmax hBm h hB0).trans
    (eq_price0 hβ hPst hsmax hBm h' hB0').symm
  refine ⟨e, ?_⟩
  rw [fisher hβ h, fisher hβ h', e]

/-- Cochrane (2023), §6.3, p. 194 (imprecision): with `s₀ > 0` there is also an equilibrium with
no outstanding debt, `B₀ = 0`: `P₀ = B₋₁/s₀`, `P₁ = β(1 + i₀) B₋₁/s₀`, `s₁ = 0`. -/
theorem degenerate_equilibrium (hβ : 0 < β) (hBm : 0 < Bm) (hs0 : 0 < s0) (hi : 0 < 1 + i0)
    (hsmax : 0 ≤ smax) :
    IsEquilibrium β Pst smax Bm s0 i0 (Bm / s0) (β * (1 + i0) * (Bm / s0)) 0 := by
  refine ⟨div_pos hBm hs0, mul_pos (mul_pos hβ hi) (div_pos hBm hs0), ?_, ?_, ?_⟩
  · rw [zero_div, add_zero, div_mul_cancel₀ _ hs0.ne']
  · field_simp
  · unfold surplus1
    simp [hsmax]

/-- Cochrane (2023), §6.3, p. 194 (imprecision): the degenerate `B₀ = 0` equilibrium has
`s₁ = 0 < s^max`, yet its `P₀` differs from the formula (and so `P₁ ≠ P*`) unless
`s₀ = β(1 + i₀) B₋₁/P*` exactly. -/
theorem degenerate_price0_ne (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (hs0 : 0 < s0) (hi : 0 < 1 + i0) (hne : s0 ≠ β * (1 + i0) * Bm / Pst) :
    Bm / s0 ≠ price0 β Pst smax Bm s0 i0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  have hpos : 0 < s0 + β * smax := by nlinarith
  by_cases hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax
  · rw [price0_eq_left hq hPst hpos hc]
    intro h
    apply hne
    field_simp at h ⊢
    linarith
  · push Not at hc
    rw [price0_eq_right hq hPst hpos hc.le]
    intro h
    field_simp at h
    nlinarith

/-- Cochrane (2023), §6.3, p. 194: larger deficits (lower `s₀`) weakly raise `P₀`: the formula is
antitone in `s₀` on `s₀ + β s^max > 0`. -/
theorem price0_antitoneOn_s0 (hBm : 0 ≤ Bm) (Pst i0 : ℝ) :
    AntitoneOn (fun s => price0 β Pst smax Bm s i0) (Set.Ioi (-(β * smax))) := by
  intro a ha b hb hab
  have ha' : 0 < a + β * smax := by have : -(β * smax) < a := ha; linarith
  have hb' : 0 < b + β * smax := by have : -(β * smax) < b := hb; linarith
  unfold price0
  refine max_le_max le_rfl ?_
  exact div_le_div_of_nonneg_left hBm ha' (by linarith)

/-- Cochrane (2023), §6.3, p. 194: a higher interest-rate target weakly lowers `P₀`. -/
theorem price0_antitoneOn_i0 (hβ : 0 < β) (hPst : 0 ≤ Pst) (smax Bm s0 : ℝ) :
    AntitoneOn (fun i => price0 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have : -1 < a := ha; linarith
  unfold price0
  refine max_le_max ?_ le_rfl
  exact div_le_div_of_nonneg_left hPst (mul_pos hβ ha') (by nlinarith)

/-- Cochrane (2023), §6.3, p. 194: more initial debt weakly raises `P₀`. -/
theorem price0_monotone_debt (hpos : 0 < s0 + β * smax) (Pst i0 : ℝ) :
    Monotone (fun B => price0 β Pst smax B s0 i0) := by
  intro a b hab
  unfold price0
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hab hpos.le)

/-- Cochrane (2023), §6.3, p. 194: `P₁ = max(P*, β(1 + i₀) B₋₁/(s₀ + β s^max))` weakly rises with
the interest-rate target. -/
theorem price1_monotoneOn_i0 (hβ : 0 < β) (hBm : 0 ≤ Bm) (hpos : 0 < s0 + β * smax)
    (Pst : ℝ) : MonotoneOn (fun i => price1 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  have key : ∀ i, -1 < i → price1 β Pst smax Bm s0 i =
      max Pst (β * (1 + i) * Bm / (s0 + β * smax)) := by
    intro i hi
    have hq : 0 < β * (1 + i) := mul_pos hβ (by linarith)
    have hi' : 1 + i ≠ 0 := by linarith
    unfold price1 price0
    rw [mul_max_of_nonneg _ _ hq.le]
    congr 1
    · field_simp
    · ring
  intro a ha b hb hab
  simp only
  rw [key a ha, key b hb]
  refine max_le_max le_rfl ?_
  apply div_le_div_of_nonneg_right _ hpos.le
  have : 0 ≤ β * Bm := mul_nonneg hβ.le hBm
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: the formula is continuous in `s₀` (no jump at the regime
switch). -/
theorem continuousOn_price0_s0 (β Pst smax Bm i0 : ℝ) :
    ContinuousOn (fun s => price0 β Pst smax Bm s i0) (Set.Ioi (-(β * smax))) := by
  unfold price0
  refine ContinuousOn.sup continuousOn_const ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro s hs
  have : -(β * smax) < s := hs
  linarith

/-- Cochrane (2023), §6.3, p. 194: the formula is continuous in `i₀` on `i₀ > -1`. -/
theorem continuousOn_price0_i0 (hβ : 0 < β) (Pst smax Bm s0 : ℝ) :
    ContinuousOn (fun i => price0 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  unfold price0
  refine ContinuousOn.sup ?_ continuousOn_const
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro i hi
  have : -1 < i := hi
  exact (mul_pos hβ (by linarith)).ne'

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region, deficits have no
effect on `P₀`: `∂P₀/∂s₀ = 0`. -/
theorem hasDerivAt_price0_s0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun s => price0 β Pst smax Bm s i0) 0 s0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  refine (hasDerivAt_const s0 (Pst / (β * (1 + i0)))).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ s in 𝓝 s0, β * (1 + i0) * Bm / Pst - s < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ s in 𝓝 s0, 0 < s + β * smax :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hpos
  filter_upwards [h1, h2] with s hs1 hs2
  exact price0_eq_left hq hPst hs2 hs1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region, raising the
interest-rate target lowers `P₀`: `∂P₀/∂i₀ = -P*/(β(1 + i₀)²) < 0`. -/
theorem hasDerivAt_price0_i0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun i => price0 β Pst smax Bm s0 i) (-(Pst / (β * (1 + i0) ^ 2))) i0 ∧
      -(Pst / (β * (1 + i0) ^ 2)) < 0 := by
  refine ⟨?_, by have := div_pos hPst (mul_pos hβ (pow_pos hi 2)); linarith⟩
  have hd : HasDerivAt (fun i => Pst / (β * (1 + i))) (-(Pst / (β * (1 + i0) ^ 2))) i0 := by
    have h1 : HasDerivAt (fun i => β * (1 + i)) β i0 := by
      simpa using ((hasDerivAt_id' i0).const_add 1).const_mul β
    have := (hasDerivAt_const i0 Pst).div h1 (mul_pos hβ hi).ne'
    refine this.congr_deriv ?_
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * (1 + i) * Bm / Pst - s0 < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  exact price0_eq_left (mul_pos hβ hi2) hPst hpos hi1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region the interest rate
leaves `P₁ = P*` alone: `∂P₁/∂i₀ = 0`. -/
theorem hasDerivAt_price1_i0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun i => price1 β Pst smax Bm s0 i) 0 i0 := by
  refine (hasDerivAt_const i0 Pst).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * (1 + i) * Bm / Pst - s0 < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  have hq : 0 < β * (1 + i) := mul_pos hβ hi2
  unfold price1
  rw [price0_eq_left hq hPst hpos hi1.le]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region deficits flow into
`P₀`: `∂P₀/∂s₀ = -B₋₁/(s₀ + β s^max)² < 0`. -/
theorem hasDerivAt_price0_s0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hBm : 0 < Bm) (hpos : 0 < s0 + β * smax)
    (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun s => price0 β Pst smax Bm s i0) (-(Bm / (s0 + β * smax) ^ 2)) s0 ∧
      -(Bm / (s0 + β * smax) ^ 2) < 0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  refine ⟨?_, by have := div_pos hBm (pow_pos hpos 2); linarith⟩
  have hd : HasDerivAt (fun s => Bm / (s + β * smax)) (-(Bm / (s0 + β * smax) ^ 2)) s0 := by
    have h1 : HasDerivAt (fun s => s + β * smax) 1 s0 := (hasDerivAt_id' s0).add_const _
    have := (hasDerivAt_const s0 Bm).div h1 hpos.ne'
    refine this.congr_deriv ?_
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ s in 𝓝 s0, β * smax < β * (1 + i0) * Bm / Pst - s :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ s in 𝓝 s0, 0 < s + β * smax :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hpos
  filter_upwards [h1, h2] with s hs1 hs2
  exact price0_eq_right hq hPst hs2 hs1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region the interest rate has
no effect on `P₀`: `∂P₀/∂i₀ = 0`. -/
theorem hasDerivAt_price0_i0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun i => price0 β Pst smax Bm s0 i) 0 i0 := by
  refine (hasDerivAt_const i0 (Bm / (s0 + β * smax))).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * smax < β * (1 + i) * Bm / Pst - s0 :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  exact price0_eq_right (mul_pos hβ hi2) hPst hpos hi1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region a higher interest
rate "just increases inflation `P₁`": `∂P₁/∂i₀ = β B₋₁/(s₀ + β s^max) > 0`. -/
theorem hasDerivAt_price1_i0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hBm : 0 < Bm) (hpos : 0 < s0 + β * smax)
    (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun i => price1 β Pst smax Bm s0 i) (β * (Bm / (s0 + β * smax))) i0 ∧
      0 < β * (Bm / (s0 + β * smax)) := by
  refine ⟨?_, mul_pos hβ (div_pos hBm hpos)⟩
  have hd : HasDerivAt (fun i => β * (1 + i) * (Bm / (s0 + β * smax)))
      (β * (Bm / (s0 + β * smax))) i0 := by
    simpa using (((hasDerivAt_id' i0).const_add 1).const_mul β).mul_const
      (Bm / (s0 + β * smax))
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * smax < β * (1 + i) * Bm / Pst - s0 :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  unfold price1
  rw [price0_eq_right (mul_pos hβ hi2) hPst hpos hi1.le]

end Cochrane.FiscalConstraints.Crash

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The debt-to-GDP equation and linear first-order ODEs

Cochrane (2023), Chapter 6, §6.4.1, eqs. (6.4)–(6.5), p. 196.

Debt grows at the real rate less the surplus, `ḃ = r b - s`, and GDP grows at `g`, `ẏ = g y`;
hence the debt-to-GDP ratio obeys (6.4): `d(b/y)/dt = (r - g)(b/y) - s/y`. Writing `x = b/y`,
`σ = s/y` and `a = r - g`, this is the linear ODE `x' = a x - σ`, whose solution from `x(t₀)` is
given by variation of constants. The book's backward solution (6.5) is printed as
`x_t = ∫₀^t e^{aτ} σ_{t-τ} dτ + e^{a} x₀`; the correct formula is
`x_t = e^{a t} x₀ - ∫₀^t e^{aτ} σ_{t-τ} dτ` (survey E6.1: the integral has the wrong sign and the
exponent of the homogeneous term lacks `t`).

## Main results

* `debt_gdp_ode` (6.4): the exact derivative of `b/y` (time-varying `r`, `g`, `s`);
  `debt_gdp_discrete`: the discrete-time analogue `x_{t+1} = ((1+r)/(1+g)) x_t - σ_{t+1}`.
* `vocFrom`, `vocFrom_self`, `vocFrom_hasDerivAt`: the variation-of-constants solution from
  `(t₀, x₀)` is a solution.
* `eq_vocFrom`: every solution on `[t₀, T]` (continuous on the closed interval, differentiable
  inside) equals it; `solution_unique`.
* `corrected_6_5`: `vocFrom a σ 0 x₀ t = e^{a t} x₀ - ∫₀^t e^{aτ} σ(t - τ) dτ`.
* `printed65`, `printed_6_5_wrong_exponent`, `printed_6_5_wrong_sign`: the printed (6.5) is not the
  solution (two counterexamples, isolating each error).
* `finite_horizon_identity`, `vocFrom_eq_of_global`: for a solution on all of `ℝ`,
  `w_t = ∫_t^T e^{-a(τ-t)} f_τ dτ + e^{-a(T-t)} w_T` for all `t, T` (the identity behind
  (6.12)–(6.13), pp. 202–203), equivalently `w_T = vocFrom a f t w_t T`.
* `forward_present_value`: for `a > 0`, bounded continuous `f` and the transversality condition,
  `w_t = ∫_t^∞ e^{-a(τ-t)} f_τ dτ` (the present value (6.9), p. 201).
-/

namespace Cochrane.FiscalConstraints.LinearODE

open Real MeasureTheory Filter Topology

/-- Cochrane (2023), eq. (6.4), p. 196: if debt obeys `ḃ = r b - s` and GDP `ẏ = g y`, the
debt-to-GDP ratio obeys `d(b/y)/dt = (r - g)(b/y) - s/y` (exact derivative; `r`, `g`, `s` may
vary over time). -/
theorem debt_gdp_ode {b y r g s : ℝ → ℝ} {t : ℝ} (hb : HasDerivAt b (r t * b t - s t) t)
    (hy : HasDerivAt y (g t * y t) t) (hy0 : y t ≠ 0) :
    HasDerivAt (fun u => b u / y u) ((r t - g t) * (b t / y t) - s t / y t) t := by
  refine (hb.div hy hy0).congr_deriv ?_
  field_simp
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (discrete-time analogue of (6.4)): if
`b_{t+1} = (1 + r) b_t - s_{t+1}` and `y_{t+1} = (1 + g) y_t`, then
`b_{t+1}/y_{t+1} = ((1 + r)/(1 + g)) (b_t/y_t) - s_{t+1}/y_{t+1}`. -/
theorem debt_gdp_discrete {b y s : ℕ → ℝ} {r g : ℝ}
    (hb : ∀ t, b (t + 1) = (1 + r) * b t - s (t + 1))
    (hy : ∀ t, y (t + 1) = (1 + g) * y t) (hy0 : ∀ t, y t ≠ 0) (hg : 1 + g ≠ 0) (t : ℕ) :
    b (t + 1) / y (t + 1) = (1 + r) / (1 + g) * (b t / y t) - s (t + 1) / y (t + 1) := by
  have h0 := hy0 t
  rw [hb t, hy t]
  field_simp

/-- Cochrane (2023), eq. (6.5), p. 196 (corrected): the variation-of-constants solution of
`x' = a x - σ` from `x(t₀) = x₀`,
`x(t) = e^{a t}(e^{-a t₀} x₀ - ∫_{t₀}^t e^{-a u} σ(u) du)`. -/
noncomputable def vocFrom (a : ℝ) (σ : ℝ → ℝ) (t0 x0 t : ℝ) : ℝ :=
  exp (a * t) * (exp (-a * t0) * x0 - ∫ u in t0..t, exp (-a * u) * σ u)

/-- Cochrane (2023), eq. (6.5), p. 196: the variation-of-constants solution starts at `x₀`. -/
theorem vocFrom_self (a : ℝ) (σ : ℝ → ℝ) (t0 x0 : ℝ) : vocFrom a σ t0 x0 t0 = x0 := by
  unfold vocFrom
  rw [intervalIntegral.integral_same, sub_zero, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), eqs. (6.4)–(6.5), p. 196: the variation-of-constants formula solves
`x' = a x - σ` at every date, for continuous `σ`. -/
theorem vocFrom_hasDerivAt (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) (t0 x0 t : ℝ) :
    HasDerivAt (vocFrom a σ t0 x0) (a * vocFrom a σ t0 x0 t - σ t) t := by
  have hf : Continuous (fun u => exp (-a * u) * σ u) := by fun_prop
  have hI := (hf.integral_hasStrictDerivAt t0 t).hasDerivAt
  have hE : HasDerivAt (fun u => exp (a * u)) (exp (a * t) * a) t := by
    simpa using ((hasDerivAt_id' t).const_mul a).exp
  have h := hE.mul (hI.const_sub (exp (-a * t0) * x0))
  unfold vocFrom
  refine h.congr_deriv ?_
  have : exp (a * t) * exp (-a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  linear_combination (-(σ t)) * this

/-- Cochrane (2023), eqs. (6.4)–(6.5), p. 196: uniqueness. Any `x` continuous on `[t₀, T]` that
solves `x' = a x - σ` on `(t₀, T)` equals the variation-of-constants solution at `T`. -/
theorem eq_vocFrom (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) {x : ℝ → ℝ} {t0 T : ℝ}
    (hle : t0 ≤ T) (hc : ContinuousOn x (Set.Icc t0 T))
    (hd : ∀ t ∈ Set.Ioo t0 T, HasDerivAt x (a * x t - σ t) t) :
    x T = vocFrom a σ t0 (x t0) T := by
  set w : ℝ → ℝ := fun t => exp (-a * t) * x t with hw
  have hwc : ContinuousOn w (Set.Icc t0 T) :=
    ContinuousOn.mul (by fun_prop) hc
  have hwd : ∀ t ∈ Set.Ioo t0 T, HasDerivAt w (-(exp (-a * t) * σ t)) t := by
    intro t ht
    have hE : HasDerivAt (fun u => exp (-a * u)) (exp (-a * t) * -a) t := by
      simpa using ((hasDerivAt_id' t).const_mul (-a)).exp
    refine (hE.mul (hd t ht)).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun t => -(exp (-a * t) * σ t)) volume t0 T :=
    (by fun_prop : Continuous (fun t => -(exp (-a * t) * σ t))).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hwc hwd hint
  rw [intervalIntegral.integral_neg] at hftc
  have hwT : w T = exp (-a * t0) * x t0 - ∫ u in t0..T, exp (-a * u) * σ u := by
    simp only [hw] at hftc ⊢
    linarith
  unfold vocFrom
  rw [← hwT, hw]
  simp only
  rw [← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), eq. (6.5), p. 196: two solutions of `x' = a x - σ` on `[t₀, T]` that agree at
`t₀` agree at `T`. -/
theorem solution_unique (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) {x z : ℝ → ℝ} {t0 T : ℝ}
    (hle : t0 ≤ T) (hcx : ContinuousOn x (Set.Icc t0 T)) (hcz : ContinuousOn z (Set.Icc t0 T))
    (hdx : ∀ t ∈ Set.Ioo t0 T, HasDerivAt x (a * x t - σ t) t)
    (hdz : ∀ t ∈ Set.Ioo t0 T, HasDerivAt z (a * z t - σ t) t) (h0 : x t0 = z t0) :
    x T = z T := by
  rw [eq_vocFrom a hσ hle hcx hdx, eq_vocFrom a hσ hle hcz hdz, h0]

/-- Cochrane (2023), eq. (6.5), p. 196, corrected (survey E6.1): the backward solution of (6.4)
from `x₀` is `x_t = e^{a t} x₀ - ∫₀^t e^{aτ} σ_{t-τ} dτ`. -/
theorem corrected_6_5 (a : ℝ) (σ : ℝ → ℝ) (x0 t : ℝ) :
    vocFrom a σ 0 x0 t = exp (a * t) * x0 - ∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ) := by
  have h1 : (∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ)) =
      ∫ τ in (0 : ℝ)..t, (fun u => exp (a * (t - u)) * σ u) (t - τ) := by
    congr 1
    funext τ
    simp only [sub_sub_cancel]
  rw [h1, intervalIntegral.integral_comp_sub_left (fun u => exp (a * (t - u)) * σ u) t,
    sub_self, sub_zero]
  unfold vocFrom
  rw [mul_sub, ← intervalIntegral.integral_const_mul, mul_zero, exp_zero, one_mul]
  congr 2
  funext u
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), eq. (6.5), p. 196, as printed: `∫₀^t e^{aτ} σ_{t-τ} dτ + e^{a} x₀`. -/
noncomputable def printed65 (a : ℝ) (σ : ℝ → ℝ) (x0 t : ℝ) : ℝ :=
  (∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ)) + exp a * x0

/-- Cochrane (2023), eq. (6.5), p. 196 (survey E6.1, the exponent): with `a = 1`, no surpluses
and `x₀ = 1`, the solution at `t = 2` is `e²`, while the printed formula gives `e`. -/
theorem printed_6_5_wrong_exponent :
    vocFrom 1 (fun _ => 0) 0 1 2 = exp 2 ∧ printed65 1 (fun _ => 0) 1 2 = exp 1 ∧
      exp (2 : ℝ) ≠ exp 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [corrected_6_5]
    simp
  · unfold printed65
    simp
  · intro h
    have := exp_injective h
    norm_num at this

/-- Cochrane (2023), eq. (6.5), p. 196 (survey E6.1, the sign): with `a = 0` (`r = g`), a constant
surplus ratio `σ = 1` and `x₀ = 0`, the solution at `t = 1` is `-1` (surpluses pay debt down),
while the printed formula gives `+1`. -/
theorem printed_6_5_wrong_sign :
    vocFrom 0 (fun _ => 1) 0 0 1 = -1 ∧ printed65 0 (fun _ => 1) 0 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [corrected_6_5]
    simp
  · unfold printed65
    simp

/-- Cochrane (2023), (6.12) and (6.13) pp. 202–203 (variation of constants, moved here from
`MoneyLiquidity`): if
`dw/dτ = a w − f` with `f` continuous, then for all `t, T`,
`w_t = ∫_t^T e^{−a(τ−t)} f_τ dτ + e^{−a(T−t)} w_T`. -/
theorem finite_horizon_identity {a : ℝ} {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    w t = (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) + Real.exp (-a * (T - t)) * w T := by
  have hφ : ∀ τ ∈ Set.uIcc t T, HasDerivAt (fun x => Real.exp (-a * (x - t)) * w x)
      (-(Real.exp (-a * (τ - t)) * f τ)) τ := by
    intro τ _
    have h1 : HasDerivAt (fun x => -a * (x - t)) (-a * 1) τ :=
      ((hasDerivAt_id τ).sub_const t).const_mul (-a)
    have h2 := h1.exp.mul (hw τ)
    convert h2 using 1
    ring
  have hint : IntervalIntegrable (fun τ => -(Real.exp (-a * (τ - t)) * f τ)) volume t T :=
    (by fun_prop : Continuous fun τ => -(Real.exp (-a * (τ - t)) * f τ)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ hint
  rw [intervalIntegral.integral_neg] at hftc
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hftc
  linarith

/-- Cochrane (2023), eqs. (6.5) and (6.12)–(6.13), pp. 196 and 202–203: the finite-horizon
identity and the variation-of-constants formula agree: a solution of `w' = a w - f` on all of `ℝ`
satisfies `w_T = vocFrom a f t w_t T` for every pair of dates `t, T` (in either order). -/
theorem vocFrom_eq_of_global {a : ℝ} {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    w T = vocFrom a f t (w t) T := by
  have h := finite_horizon_identity hw hf t T
  have hI : (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) =
      exp (a * t) * ∫ τ in t..T, exp (-a * τ) * f τ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext τ
    rw [← mul_assoc, ← exp_add]
    ring_nf
  rw [hI] at h
  have e4 : exp (-a * t) * exp (a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have e5 : exp (a * T) * exp (-a * t) * exp (-a * (T - t)) = 1 := by
    rw [← exp_add, ← exp_add]; ring_nf; exact exp_zero
  unfold vocFrom
  rw [h]
  linear_combination (-(exp (a * T) * ∫ τ in t..T, exp (-a * τ) * f τ)) * e4 + (-(w T)) * e5

/-- Cochrane (2023), (6.9) p. 201, the infinite-horizon present value (moved here from
`MoneyLiquidity`): if `dw/dτ = a w − f`
with `a = r^f − g > 0`, `f` continuous and bounded, and the transversality condition
`e^{−a(T−t)} w_T → 0` holds, then `f` discounted at `a` is integrable on `(t, ∞)` and
`w_t = ∫_t^∞ e^{−a(τ−t)} f_τ dτ`. -/
theorem forward_present_value {a K : ℝ} (ha : 0 < a) {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K)
    (t : ℝ) (htvc : Tendsto (fun T => Real.exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    IntegrableOn (fun τ => Real.exp (-a * (τ - t)) * f τ) (Set.Ioi t) ∧
      w t = ∫ τ in Set.Ioi t, Real.exp (-a * (τ - t)) * f τ := by
  have hint : IntegrableOn (fun τ => Real.exp (-a * (τ - t)) * f τ) (Set.Ioi t) := by
    have hexp : IntegrableOn (fun τ => K * (Real.exp (a * t) * Real.exp (-a * τ)))
        (Set.Ioi t) := ((exp_neg_integrableOn_Ioi t ha).const_mul _).const_mul K
    refine hexp.mono' ?_ (Filter.Eventually.of_forall fun τ => ?_)
    · exact (by fun_prop : Continuous fun τ => Real.exp (-a * (τ - t)) * f τ)
        |>.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Real.norm_eq_abs,
        mul_comm]
      have : -a * (τ - t) = a * t + -a * τ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hK τ) (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi t hint tendsto_id
  have hsum := hlim.add htvc
  rw [add_zero] at hsum
  have hconst : (fun T => (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) +
      Real.exp (-a * (T - t)) * w T) = fun _ => w t := by
    funext T; exact (finite_horizon_identity hw hf t T).symm
  simp only [id] at hsum
  rw [hconst] at hsum
  exact tendsto_nhds_unique tendsto_const_nhds hsum

end Cochrane.FiscalConstraints.LinearODE

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# What if r < g?

Cochrane (2023), Chapter 6, §6.4 *What if r < g?*, §6.4.1–§6.4.3, eqs. (6.3)–(6.5),
pp. 195–199.

The debt-to-GDP ratio `x = b/y` obeys (6.4), `x' = a x - σ` with `a = r - g` and `σ = s/y`. We
prove the dichotomy behind "in a perfect-foresight frictionless model, `r < g` implies price-level
indeterminacy, not infinity" (p. 195), in continuous and in discrete time:

* (D1) `a > 0`: the forward present value `x̂_t = ∫₀^∞ e^{-a u} σ_{t+u} du` is a bounded solution;
  every solution satisfies `x_t - x̂_t = e^{a t}(x₀ - x̂₀)`; a solution is bounded iff `x₀ = x̂₀`,
  and otherwise `|x_t| → ∞`; the transversality condition `e^{-a t} x_t → 0` (equivalently
  `e^{-r t} b_t → 0`) holds iff `x₀ = x̂₀`. With nominal debt `B₀` and `x₀ = B₀/(P₀ y₀)`, exactly
  one price level `P₀ = B₀/(y₀ x̂₀)` gives a bounded path.
* (D2) `a < 0`: every solution is bounded, `|x_t| ≤ |x₀| + M/|a|`, and any two converge; so every
  `P₀ > 0` gives a bounded debt-to-GDP path (indeterminacy). The transversality condition
  `e^{-r t} b_t → 0` instead fails for every solution when the surplus ratio is a nonzero
  constant: no `P₀` satisfies it ("infinity" in the present-value sense).
* (D3) `a = 0`: `x_t = x₀ - ∫₀^t σ`, bounded iff the cumulated surpluses are bounded; with a
  constant nonzero surplus ratio no solution is bounded.
* (D4) temporary `r < g`: `a = a₁` on `[0, T₀)`, `a = a₂ > 0` after. There is exactly one bounded
  solution, the forward present value with time-varying discounting,
  `x̂_t = ∫_t^{T₀} e^{-a₁(v-t)} σ_v dv + e^{-a₁(T₀-t)} x̂^{(2)}_{T₀}`, and every other solution
  diverges. For `a₁ = -0.01`, `T₀ = 20`, `a₂ = 0.01` this is the book's 20-year formula with
  FUTURE surpluses `σ_{t+τ}`; the printed version with past surpluses `σ_{t-τ}` is wrong
  (survey E6.2).
* (D5) discrete time, `x_{t+1} = γ x_t - w_t` with `γ = (1+r)/(1+g)`: `γ > 1` gives the unique
  bounded solution `x_t = ∑_j γ^{-(j+1)} w_{t+j}`; `0 < γ < 1` makes every solution bounded and
  any two converge; `γ = 1` is the knife edge.
* (D6) the steady-state surplus `σ* = a x*` is continuous across `a = 0` (§6.4.2), with the book's
  numbers: `±0.01%` of GDP at 100% debt, `log 3/10⁻⁴ ∈ (10986, 10987)` years ("11,000"),
  `150 e^{1.1} ∈ (450.6, 450.7)`, exact factors `1/3` and `3`; `r - g = -1%` at 100% debt funds a
  1% of GDP deficit (§6.4.3); `e^{-0.2} ∈ (0.8187, 0.8188)`, not 80%.

Continuous-time solutions are taken on `[0, ∞)`: `x` is continuous on `[0, ∞)` and satisfies the
ODE at every `t > 0`. Surplus ratios are continuous and bounded by `M`.
-/

namespace Cochrane.FiscalConstraints.RvsG

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals Cochrane.FiscalConstraints.LinearODE

/-- Cochrane (2023), eq. (6.4), p. 196: `x` solves the debt-to-GDP equation `x' = a x - σ` on
`[0, ∞)` (continuous on `[0, ∞)`, differentiable with the right derivative at every `t > 0`). -/
def SolvesOn (a : ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ∀ t, 0 < t → HasDerivAt x (a * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196: the debt-to-GDP path is bounded on `[0, ∞)` (it does not
explode). -/
def BddOn (x : ℝ → ℝ) : Prop := ∃ K, ∀ t, 0 ≤ t → |x t| ≤ K

/-- Cochrane (2023), eqs. (6.3), p. 195, and §6.4.1, p. 196: the forward present value of
surplus/GDP ratios discounted at `a = r - g`, `x̂_t = ∫₀^∞ e^{-a u} σ_{t+u} du`. -/
noncomputable def pv (a : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) * σ (t + u)

variable {a M a₂ : ℝ} {σ x z : ℝ → ℝ}

/-- Cochrane (2023), eq. (6.5), p. 196: every solution on `[0, ∞)` is the backward
(variation-of-constants) solution from its initial value. -/
theorem solvesOn_eq (hσ : Continuous σ) (hx : SolvesOn a σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t = vocFrom a σ 0 (x 0) t :=
  eq_vocFrom a hσ ht (hx.1.mono Set.Icc_subset_Ici_self) (fun s hs => hx.2 s hs.1)

/-- Cochrane (2023), eq. (6.5), p. 196: for every initial value `x₀` the backward solution solves
(6.4): any initial debt-to-GDP ratio is consistent with the flow equation. -/
theorem vocFrom_solvesOn (a : ℝ) (hσ : Continuous σ) (x0 : ℝ) :
    SolvesOn a σ (vocFrom a σ 0 x0) :=
  ⟨fun t _ => (vocFrom_hasDerivAt a hσ 0 x0 t).continuousAt.continuousWithinAt,
    fun t _ => vocFrom_hasDerivAt a hσ 0 x0 t⟩

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions differ by `e^{a t}(x₀ - z₀)`. -/
theorem vocFrom_sub (a : ℝ) (σ : ℝ → ℝ) (x0 z0 t : ℝ) :
    vocFrom a σ 0 x0 t - vocFrom a σ 0 z0 t = exp (a * t) * (x0 - z0) := by
  unfold vocFrom
  rw [mul_zero, exp_zero, one_mul, one_mul]
  ring

/-- Cochrane (2023), §6.4.1, p. 196: for `a > 0` the forward present value is the backward
solution started at `x̂₀`: `x̂_t = e^{a t}(x̂₀ - ∫₀^t e^{-a u} σ_u du)`, for every `t`. -/
theorem pv_eq_voc (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    pv a σ t = vocFrom a σ 0 (pv a σ 0) t := by
  have hint : ∀ c, IntegrableOn (fun v => exp (-a * v) * σ v) (Set.Ioi c) :=
    integrableOn_exp_mul_bdd ha hσ hM
  have h0 : pv a σ 0 = ∫ v in Set.Ioi (0 : ℝ), exp (-a * v) * σ v := by
    unfold pv
    simp only [zero_add]
  unfold vocFrom
  rw [h0, mul_zero, exp_zero, one_mul, integral_Ioi_sub_interval hint t]
  unfold pv
  exact integral_exp_shift a t σ

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value is bounded, `|x̂_t| ≤ M/a`. -/
theorem abs_pv_le (ha : 0 < a) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) : |pv a σ t| ≤ M / a := by
  have := abs_integral_exp_mul_le ha (σ := fun u => σ (t + u)) (fun u => hM (t + u)) 0
  rw [mul_zero, exp_zero] at this
  unfold pv
  calc _ ≤ M * (1 / a) := this
    _ = M / a := by ring

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value solves (6.4) at every date. -/
theorem pv_hasDerivAt (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    HasDerivAt (pv a σ) (a * pv a σ t - σ t) t := by
  have he : pv a σ = vocFrom a σ 0 (pv a σ 0) := funext (pv_eq_voc ha hσ hM)
  rw [he]
  exact vocFrom_hasDerivAt a hσ 0 _ t

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the forward present value is a solution of
(6.4) on `[0, ∞)`. -/
theorem pv_solvesOn (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) :
    SolvesOn a σ (pv a σ) :=
  ⟨fun t _ => (pv_hasDerivAt ha hσ hM t).continuousAt.continuousWithinAt,
    fun t _ => pv_hasDerivAt ha hσ hM t⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the forward present value is bounded. -/
theorem pv_bddOn (ha : 0 < a) (hM : ∀ u, |σ u| ≤ M) : BddOn (pv a σ) :=
  ⟨M / a, fun t _ => abs_pv_le ha hM t⟩

/-- Cochrane (2023), eq. (6.3), p. 195: with a constant surplus/GDP ratio `c` and `r > g`, the
present value is `b/y = c/(r - g)`. -/
theorem pv_const (ha : 0 < a) (c t : ℝ) : pv a (fun _ => c) t = c / a := by
  unfold pv
  rw [integral_mul_const, integral_exp_neg_mul_Ioi_zero ha]
  ring

/-- Cochrane (2023), eq. (6.3), p. 195: with a constant surplus/GDP ratio `c ≠ 0` and `r ≤ g`,
the present-value integral diverges ("the present value of surpluses is then apparently
infinite"). -/
theorem pv_const_not_integrable (ha : a ≤ 0) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    ¬ IntegrableOn (fun u => exp (-a * u) * (fun _ => c) (t + u)) (Set.Ioi 0) := by
  have := not_integrableOn_exp_neg_mul ha hc
  simp only [mul_comm (exp _) c] at this ⊢
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D1): every solution differs from the present value by an
exploding term, `x_t - x̂_t = e^{a t}(x₀ - x̂₀)`. -/
theorem sub_pv (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (hx : SolvesOn a σ x)
    {t : ℝ} (ht : 0 ≤ t) : x t - pv a σ t = exp (a * t) * (x 0 - pv a σ 0) := by
  rw [solvesOn_eq hσ hx ht, pv_eq_voc ha hσ hM t, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g`, a solution that does not start at the
present value explodes: `|x_t| → ∞`. -/
theorem tendsto_abs_of_ne (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) (hne : x 0 ≠ pv a σ 0) :
    Tendsto (fun t => |x t|) atTop atTop := by
  set d := |x 0 - pv a σ 0| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hlow : ∀ t, 0 ≤ t → exp (a * t) * d + -(M / a) ≤ |x t| := by
    intro t ht
    have h1 := sub_pv ha hσ hM hx ht
    have h2 := abs_pv_le ha hM t
    have h3 : exp (a * t) * d = |x t - pv a σ t| := by
      rw [h1, abs_mul, abs_of_pos (exp_pos _)]
    have h4 := abs_sub (x t) (pv a σ t)
    linarith
  have hlim : Tendsto (fun t => exp (a * t) * d + -(M / a)) atTop atTop := by
    have : Tendsto (fun t => exp (a * t)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
    exact tendsto_atTop_add_const_right _ _ (this.atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` a solution of (6.4) is bounded iff it starts
at the present value of surpluses, `x₀ = ∫₀^∞ e^{-(r-g)u} σ_u du`. -/
theorem bddOn_iff (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) : BddOn x ↔ x 0 = pv a σ 0 := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (tendsto_abs_of_ne ha hσ hM hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    refine ⟨M / a, fun t ht => ?_⟩
    have := sub_pv ha hσ hM hx ht
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact abs_pv_le ha hM t

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` a bounded solution IS the present value at
every date: `x_t = ∫₀^∞ e^{-(r-g)u} σ_{t+u} du`. -/
theorem eq_pv_of_bddOn (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) (hb : BddOn x) {t : ℝ} (ht : 0 ≤ t) : x t = pv a σ t := by
  have := sub_pv ha hσ hM hx ht
  rw [(bddOn_iff ha hσ hM hx).1 hb, sub_self, mul_zero, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the debt-to-GDP equation has exactly one
bounded solution on `[0, ∞)` (up to values before date 0). -/
theorem existsUnique_bdd (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) :
    SolvesOn a σ (pv a σ) ∧ BddOn (pv a σ) ∧
      ∀ x, SolvesOn a σ x → BddOn x → ∀ t, 0 ≤ t → x t = pv a σ t :=
  ⟨pv_solvesOn ha hσ hM, pv_bddOn ha hM, fun _ hx hb _ ht => eq_pv_of_bddOn ha hσ hM hx hb ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D1, transversality): for `r > g`, `e^{-a t} x_t → 0` iff
`x₀` equals the present value. -/
theorem tvc_iff (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) :
    Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 0) ↔ x 0 = pv a σ 0 := by
  have hev : ∀ᶠ t in atTop,
      exp (-a * t) * pv a σ t + (x 0 - pv a σ 0) = exp (-a * t) * x t := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 := sub_pv ha hσ hM hx ht
    have e : exp (-a * t) * exp (a * t) = 1 := by
      rw [← exp_add]
      ring_nf
      exact exp_zero
    have : x t = pv a σ t + exp (a * t) * (x 0 - pv a σ 0) := by linarith
    rw [this]
    linear_combination (-(x 0 - pv a σ 0)) * e
  have hdec : Tendsto (fun t => exp (-a * t)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
    refine this.congr fun t => ?_
    simp [neg_mul]
  have hpv : Tendsto (fun t => exp (-a * t) * pv a σ t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => exp (-a * t) * (M / a)) (fun t => ?_)
      (by simpa using hdec.mul_const (M / a))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_pv_le ha hM t) (exp_pos _).le
  have hlim : Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 (x 0 - pv a σ 0)) := by
    have := hpv.add_const (x 0 - pv a σ 0)
    rw [zero_add] at this
    exact this.congr' hev
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rw [h, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D1, transversality in levels): with debt `b_t = x_t y_t`,
GDP `y_t = y₀ e^{g t}` and discount rate `r = a + g > g`, `e^{-r t} b_t → 0` iff `x₀` equals the
present value of surpluses. -/
theorem tvc_levels_iff {g y0 : ℝ} (hy0 : y0 ≠ 0) (ha : 0 < a) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesOn a σ x) :
    Tendsto (fun t => exp (-(a + g) * t) * (x t * (y0 * exp (g * t)))) atTop (𝓝 0) ↔
      x 0 = pv a σ 0 := by
  have e : ∀ t, exp (-(a + g) * t) * (x t * (y0 * exp (g * t))) =
      y0 * (exp (-a * t) * x t) := by
    intro t
    have : exp (-(a + g) * t) * exp (g * t) = exp (-a * t) := by
      rw [← exp_add]
      ring_nf
    linear_combination (y0 * x t) * this
  simp_rw [e]
  rw [← tvc_iff ha hσ hM hx]
  constructor
  · intro h
    have := h.const_mul y0⁻¹
    simp only [mul_zero] at this
    refine this.congr fun t => ?_
    field_simp
  · intro h
    simpa using h.const_mul y0

/-- Cochrane (2023), §6.4.1, p. 196 (D1, nominal debt): for `r > g`, with nominal debt
`B₀ > 0` and GDP `y₀ > 0`, the price level `P₀ > 0` yields a bounded debt-to-GDP path iff
`P₀ = B₀/(y₀ x̂₀)`: the valuation equation determines the price level. -/
theorem nominal_determinacy (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {B0 y0 P0 : ℝ} (hB0 : 0 < B0) (hy0 : 0 < y0) (hP0 : 0 < P0) :
    (∃ x, SolvesOn a σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x) ↔
      P0 = B0 / (y0 * pv a σ 0) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (bddOn_iff ha hσ hM hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pv a σ 0 := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pv a σ 0 := by
      have : 0 < B0 / (y0 * pv a σ 0) := hP ▸ hP0
      have h2 := (div_pos_iff.1 this)
      rcases h2 with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pv a σ 0 := pos_of_mul_pos_right hpos hy0.le
    refine ⟨pv a σ, pv_solvesOn ha hσ hM, ?_, pv_bddOn ha hM⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` every solution of (6.4) is bounded,
`|x_t| ≤ |x₀| + M/(g - r)`. -/
theorem abs_le_of_neg (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) {t : ℝ} (ht : 0 ≤ t) : |x t| ≤ |x 0| + M / (-a) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hna : 0 < -a := neg_pos.2 ha
  have hI : |∫ u in (0 : ℝ)..t, exp (-a * u) * σ u| ≤ M * ((1 - exp (-a * t)) / a) := by
    have hg : IntervalIntegrable (fun u => M * exp (-a * u)) volume 0 t :=
      (by fun_prop : Continuous (fun u => M * exp (-a * u))).intervalIntegrable _ _
    have := intervalIntegral.norm_integral_le_of_norm_le ht
      (f := fun u => exp (-a * u) * σ u) (ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hM u) (exp_pos _).le) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      intervalIntegral_exp_neg_mul ha.ne t] at this
    exact this
  have hE : exp (a * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hE0 := exp_pos (a * t)
  have hprod : exp (a * t) * exp (-a * t) = 1 := by
    rw [← exp_add]
    ring_nf
    exact exp_zero
  rw [solvesOn_eq hσ hx ht]
  unfold vocFrom
  rw [mul_zero, exp_zero, one_mul, abs_mul, abs_of_pos hE0]
  have h1 : |x 0 - ∫ u in (0 : ℝ)..t, exp (-a * u) * σ u| ≤
      |x 0| + M * ((1 - exp (-a * t)) / a) :=
    (abs_sub _ _).trans (by linarith)
  have h2 : exp (a * t) * (M * ((1 - exp (-a * t)) / a)) = M * (1 - exp (a * t)) / (-a) := by
    rw [neg_mul, exp_neg]
    field_simp
    ring
  calc exp (a * t) * |x 0 - ∫ u in (0 : ℝ)..t, exp (-a * u) * σ u|
      ≤ exp (a * t) * (|x 0| + M * ((1 - exp (-a * t)) / a)) :=
        mul_le_mul_of_nonneg_left h1 hE0.le
    _ = exp (a * t) * |x 0| + M * (1 - exp (a * t)) / (-a) := by rw [mul_add, h2]
    _ ≤ |x 0| + M / (-a) := by
        have h3 : exp (a * t) * |x 0| ≤ |x 0| := by
          nlinarith [abs_nonneg (x 0)]
        have h4 : M * (1 - exp (a * t)) / (-a) ≤ M / (-a) := by
          apply div_le_div_of_nonneg_right _ hna.le
          nlinarith
        linarith

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` every solution of (6.4) is bounded. -/
theorem bddOn_of_neg (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) : BddOn x :=
  ⟨_, fun _ ht => abs_le_of_neg ha hσ hM hx ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` any two solutions converge:
`x_t - z_t = e^{a t}(x₀ - z₀) → 0` ("the larger debt-to-GDP ratio melts away"). -/
theorem tendsto_sub_of_neg (ha : a < 0) (hσ : Continuous σ) (hx : SolvesOn a σ x)
    (hz : SolvesOn a σ z) : Tendsto (fun t => x t - z t) atTop (𝓝 0) := by
  have hdec : Tendsto (fun t => exp (a * t)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (neg_pos.2 ha))
    refine this.congr fun t => ?_
    simp
  have := hdec.mul_const (x 0 - z 0)
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [solvesOn_eq hσ hx ht, solvesOn_eq hσ hz ht, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D2, "indeterminacy, not infinity"): for `r < g`, every
price level `P₀ > 0` gives a solution of (6.4) from `x₀ = B₀/(P₀ y₀)` that is bounded: boundedness
of the debt-to-GDP ratio cannot select `P₀`. -/
theorem nominal_indeterminacy (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (B0 y0 P0 : ℝ) : ∃ x, SolvesOn a σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x :=
  ⟨_, vocFrom_solvesOn a hσ _, vocFrom_self a σ 0 _,
    bddOn_of_neg ha hσ hM (vocFrom_solvesOn a hσ _)⟩

/-- Cochrane (2023), §6.4.1, pp. 195–196 (D2, the transversality condition): for `r < g` and a
constant nonzero surplus ratio `c`, NO solution satisfies `e^{-a t} x_t → 0` (equivalently
`e^{-r t} b_t → 0`): in this sense the present value is infinite for every `P₀`. -/
theorem tvc_fails_of_neg (ha : a < 0) {c : ℝ} (hc : c ≠ 0)
    (hx : SolvesOn a (fun _ => c) x) :
    ¬ Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 0) := by
  intro h
  have hk : c / a ≠ 0 := div_ne_zero hc ha.ne
  have hform : ∀ t, 0 ≤ t → exp (-a * t) = (exp (-a * t) * x t - (x 0 - c / a)) / (c / a) := by
    intro t ht
    rw [solvesOn_eq continuous_const hx ht]
    unfold vocFrom
    rw [intervalIntegral.integral_mul_const, intervalIntegral_exp_neg_mul ha.ne t, mul_zero,
      exp_zero, one_mul]
    rw [neg_mul, exp_neg]
    have hE := (exp_pos (a * t)).ne'
    have ha0 : a ≠ 0 := ha.ne
    field_simp
    ring
  have hlim : Tendsto (fun t => (exp (-a * t) * x t - (x 0 - c / a)) / (c / a)) atTop
      (𝓝 ((0 - (x 0 - c / a)) / (c / a))) :=
    (h.sub_const _).div_const _
  have hinf : Tendsto (fun t => exp (-a * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.2 ha))
  have hlim' : Tendsto (fun t => exp (-a * t)) atTop (𝓝 ((0 - (x 0 - c / a)) / (c / a))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hform t ht).symm
  exact not_tendsto_nhds_of_tendsto_atTop hinf _ hlim'

/-- Cochrane (2023), §6.4.1, p. 196 (D3, the knife edge `r = g`): every solution is
`x_t = x₀ - ∫₀^t σ`. -/
theorem eq_of_zero (hσ : Continuous σ) (hx : SolvesOn 0 σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t = x 0 - ∫ u in (0 : ℝ)..t, σ u := by
  rw [solvesOn_eq hσ hx ht]
  unfold vocFrom
  simp

/-- Cochrane (2023), §6.4.1, p. 196 (D3): for `r = g` a solution is bounded iff the cumulated
surplus ratios `∫₀^t σ` are bounded. -/
theorem bddOn_iff_zero (hσ : Continuous σ) (hx : SolvesOn 0 σ x) :
    BddOn x ↔ ∃ K, ∀ t, 0 ≤ t → |∫ u in (0 : ℝ)..t, σ u| ≤ K := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |x 0|, fun t ht => ?_⟩
    have h1 := eq_of_zero hσ hx ht
    have h2 := hK t ht
    have : ∫ u in (0 : ℝ)..t, σ u = x 0 - x t := by linarith
    rw [this]
    exact (abs_sub _ _).trans (by linarith)
  · rintro ⟨K, hK⟩
    refine ⟨|x 0| + K, fun t ht => ?_⟩
    rw [eq_of_zero hσ hx ht]
    exact (abs_sub _ _).trans (by linarith [hK t ht])

/-- Cochrane (2023), §6.4.1, p. 196 (D3): for `r = g` and a constant nonzero surplus ratio, no
solution is bounded. -/
theorem not_bddOn_zero_const {c : ℝ} (hc : c ≠ 0) (hx : SolvesOn 0 (fun _ => c) x) :
    ¬ BddOn x := by
  rw [bddOn_iff_zero continuous_const hx]
  rintro ⟨K, hK⟩
  have hcpos : 0 < |c| := abs_pos.2 hc
  have := hK ((|K| + 1) / |c|) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (|K| + 1) / |c|), div_mul_cancel₀ _ hcpos.ne'] at this
  linarith [le_abs_self K]

/-! ### (D4) Temporary `r < g` -/

/-- Cochrane (2023), §6.4.1, p. 196: `x` solves (6.4) on `[0, ∞)` with `r - g = a₁` before `T₀`
and `r - g = a₂` after (continuous on `[0, ∞)`, the ODE on `(0, T₀)` and on `(T₀, ∞)`). -/
def SolvesStep (a₁ a₂ T0 : ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ (∀ t ∈ Set.Ioo 0 T0, HasDerivAt x (a₁ * x t - σ t) t) ∧
    ∀ t, T0 < t → HasDerivAt x (a₂ * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula, survey E6.2): the forward present
value at date 0 with time-varying discounting,
`x̂₀ = ∫₀^{T₀} e^{-a₁ v} σ_v dv + e^{-a₁ T₀} ∫₀^∞ e^{-a₂ u} σ_{T₀+u} du`. -/
noncomputable def stepPV0 (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula at every date): the forward
present value `∫₀^∞ exp(-∫_t^{t+u} a) σ_{t+u} du`, written out for the two-regime `a`. -/
noncomputable def pvStep (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ T0 then
    (∫ v in t..T0, exp (-a₁ * (v - t)) * σ v) + exp (-a₁ * (T0 - t)) * pv a₂ σ T0
  else pv a₂ σ t

/-- Cochrane (2023), §6.4.1, p. 196: the glued solution: the backward solution from `x̂₀` before
`T₀`, the forward present value after. -/
noncomputable def stepSol (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ T0 then vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t else pv a₂ σ t

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions from the same date `t₀` differ by
`e^{a(t - t₀)}(x₀ - z₀)`. -/
theorem vocFrom_sub_from (a : ℝ) (σ : ℝ → ℝ) (t0 x0 z0 t : ℝ) :
    vocFrom a σ t0 x0 t - vocFrom a σ t0 z0 t = exp (a * (t - t0)) * (x0 - z0) := by
  unfold vocFrom
  have : exp (a * t) * exp (-a * t0) = exp (a * (t - t0)) := by rw [← exp_add]; ring_nf
  linear_combination (x0 - z0) * this

/-- Cochrane (2023), §6.4.1, p. 196: started from `x̂₀`, the backward solution reaches the forward
present value of the post-`T₀` surpluses at `T₀`. -/
theorem vocFrom_stepPV0 (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) :
    vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) T0 = pv a₂ σ T0 := by
  unfold vocFrom stepPV0
  rw [mul_zero, exp_zero, one_mul, add_sub_cancel_left, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), §6.4.1, p. 196: a two-regime solution, after `T₀`, is the backward solution
from its value at `T₀`. -/
theorem step_after (hσ : Continuous σ) {a₁ a₂ T0 : ℝ} (hT0 : 0 ≤ T0)
    (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ} (ht : T0 ≤ t) :
    x t = vocFrom a₂ σ T0 (x T0) t :=
  eq_vocFrom a₂ hσ ht (hx.1.mono fun _ hs => le_trans hT0 hs.1) (fun s hs => hx.2.2 s hs.1)

/-- Cochrane (2023), §6.4.1, p. 196: a two-regime solution, before `T₀`, is the backward solution
from its initial value. -/
theorem step_before (hσ : Continuous σ) {a₁ a₂ T0 : ℝ} (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ T0) : x t = vocFrom a₁ σ 0 (x 0) t :=
  eq_vocFrom a₁ hσ ht0 (hx.1.mono Set.Icc_subset_Ici_self)
    (fun s hs => hx.2.1 s ⟨hs.1, lt_of_lt_of_le hs.2 ht⟩)

/-- Cochrane (2023), §6.4.1, p. 196: after `T₀` every two-regime solution differs from the forward
present value by `e^{a₂(t - T₀)} e^{a₁ T₀}(x₀ - x̂₀)`. -/
theorem step_sub_pv (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {a₁ T0 : ℝ}
    (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ} (ht : T0 ≤ t) :
    x t - pv a₂ σ t =
      exp (a₂ * (t - T0)) * (exp (a₁ * T0) * (x 0 - stepPV0 a₁ a₂ T0 σ)) := by
  have hpv : pv a₂ σ t = vocFrom a₂ σ T0 (pv a₂ σ T0) t :=
    eq_vocFrom a₂ hσ ht (fun s _ => (pv_hasDerivAt ha₂ hσ hM s).continuousAt.continuousWithinAt)
      (fun s _ => pv_hasDerivAt ha₂ hσ hM s)
  rw [step_after hσ hT0 hx ht, hpv, vocFrom_sub_from]
  congr 1
  rw [step_before hσ hx hT0 le_rfl, ← vocFrom_stepPV0 a₁ a₂ T0 σ, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g`, a solution that does not start
at the forward present value `x̂₀` explodes: `|x_t| → ∞`. -/
theorem step_tendsto_abs_of_ne (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {a₁ T0 : ℝ} (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x)
    (hne : x 0 ≠ stepPV0 a₁ a₂ T0 σ) : Tendsto (fun t => |x t|) atTop atTop := by
  set d := exp (a₁ * T0) * |x 0 - stepPV0 a₁ a₂ T0 σ| with hd_def
  have hd : 0 < d := mul_pos (exp_pos _) (abs_pos.2 (sub_ne_zero.2 hne))
  have hlow : ∀ t, T0 ≤ t → exp (a₂ * (t - T0)) * d + -(M / a₂) ≤ |x t| := by
    intro t ht
    have h1 := step_sub_pv ha₂ hσ hM hT0 hx ht
    have h2 := abs_pv_le ha₂ hM t
    have h3 : exp (a₂ * (t - T0)) * d = |x t - pv a₂ σ t| := by
      rw [h1, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _), hd_def]
    have h4 := abs_sub (x t) (pv a₂ σ t)
    linarith
  have hlim : Tendsto (fun t => exp (a₂ * (t - T0)) * d + -(M / a₂)) atTop atTop := by
    have h1 : Tendsto (fun t => a₂ * (t - T0)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-T0) tendsto_id).const_mul_atTop ha₂
    exact tendsto_atTop_add_const_right _ _ ((tendsto_exp_atTop.comp h1).atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop T0).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g` (`a₂ > 0` after `T₀`), a solution
is bounded iff it starts at the forward present value `x̂₀`: "values of debt different from this
forward-looking integral lead to explosions". -/
theorem step_bddOn_iff (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {a₁ T0 : ℝ}
    (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x) :
    BddOn x ↔ x 0 = stepPV0 a₁ a₂ T0 σ := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (step_tendsto_abs_of_ne ha₂ hσ hM hT0 hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T0)).exists_bound_of_continuousOn
      (hx.1.mono Set.Icc_subset_Ici_self)
    refine ⟨max C (M / a₂), fun t ht => ?_⟩
    rcases le_total t T0 with htT | htT
    · exact (hC t ⟨ht, htT⟩).trans (le_max_left _ _)
    · have := step_sub_pv ha₂ hσ hM hT0 hx htT
      rw [h, sub_self, mul_zero, mul_zero, sub_eq_zero] at this
      rw [this]
      exact (abs_pv_le ha₂ hM t).trans (le_max_right _ _)

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the bounded solution at every date `t ≤ T₀` is the
forward present value with time-varying discounting,
`x̂_t = ∫_t^{T₀} e^{-a₁(v-t)} σ_v dv + e^{-a₁(T₀-t)} x̂^{(2)}_{T₀}`. -/
theorem vocFrom_stepPV0_eq (hσ : Continuous σ) (a₁ a₂ T0 t : ℝ) :
    vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t =
      (∫ v in t..T0, exp (-a₁ * (v - t)) * σ v) + exp (-a₁ * (T0 - t)) * pv a₂ σ T0 := by
  have hf : Continuous (fun v => exp (-a₁ * v) * σ v) := by fun_prop
  have hsplit := intervalIntegral.integral_interval_sub_left
    (hf.intervalIntegrable (μ := volume) 0 T0) (hf.intervalIntegrable (μ := volume) 0 t)
  unfold vocFrom stepPV0
  rw [mul_zero, exp_zero, one_mul]
  have e1 : (∫ v in (0 : ℝ)..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0 -
      ∫ v in (0 : ℝ)..t, exp (-a₁ * v) * σ v =
      (∫ v in t..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0 := by
    rw [← hsplit]
    ring
  rw [e1, mul_add, ← intervalIntegral.integral_const_mul, ← mul_assoc, ← exp_add]
  congr 1
  · congr 1
    funext v
    rw [← mul_assoc, ← exp_add]
    ring_nf
  · ring_nf

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the glued path coincides with the forward present value
`pvStep` at every date. -/
theorem stepSol_eq_pvStep (hσ : Continuous σ) (a₁ a₂ T0 t : ℝ) :
    stepSol a₁ a₂ T0 σ t = pvStep a₁ a₂ T0 σ t := by
  unfold stepSol pvStep
  split_ifs
  · exact vocFrom_stepPV0_eq hσ a₁ a₂ T0 t
  · rfl

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the glued path solves the two-regime equation. -/
theorem stepSol_solvesStep (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (a₁ T0 : ℝ) : SolvesStep a₁ a₂ T0 σ (stepSol a₁ a₂ T0 σ) := by
  have hv : ∀ t, HasDerivAt (vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ))
      (a₁ * vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t - σ t) t :=
    fun t => vocFrom_hasDerivAt a₁ hσ 0 _ t
  have hp : ∀ t, HasDerivAt (pv a₂ σ) (a₂ * pv a₂ σ t - σ t) t :=
    fun t => pv_hasDerivAt ha₂ hσ hM t
  have hcont : Continuous (stepSol a₁ a₂ T0 σ) := by
    unfold stepSol
    refine Continuous.if_le (continuous_iff_continuousAt.2 fun t => (hv t).continuousAt)
      (continuous_iff_continuousAt.2 fun t => (hp t).continuousAt) continuous_id
      continuous_const ?_
    intro t ht
    rw [ht]
    exact vocFrom_stepPV0 a₁ a₂ T0 σ
  refine ⟨hcont.continuousOn, fun t ht => ?_, fun t ht => ?_⟩
  · have hev : stepSol a₁ a₂ T0 σ =ᶠ[𝓝 t] vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) := by
      filter_upwards [eventually_lt_nhds ht.2] with s hs
      unfold stepSol
      simp only [hs.le, ↓reduceIte]
    have h := (hv t).congr_of_eventuallyEq hev
    rw [show stepSol a₁ a₂ T0 σ t = vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t from hev.eq_of_nhds]
    exact h
  · have hev : stepSol a₁ a₂ T0 σ =ᶠ[𝓝 t] pv a₂ σ := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      unfold stepSol
      simp only [not_le.2 hs, ↓reduceIte]
    have h := (hp t).congr_of_eventuallyEq hev
    rw [show stepSol a₁ a₂ T0 σ t = pv a₂ σ t from hev.eq_of_nhds]
    exact h

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g` and permanent `r > g` after
`T₀ ≥ 0`, there is exactly one bounded solution: it exists (`stepSol`), and every bounded solution
equals the forward present value `pvStep` at every date `t ≥ 0`. -/
theorem step_existsUnique (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {a₁ T0 : ℝ} (hT0 : 0 ≤ T0) :
    SolvesStep a₁ a₂ T0 σ (stepSol a₁ a₂ T0 σ) ∧ BddOn (stepSol a₁ a₂ T0 σ) ∧
      ∀ x, SolvesStep a₁ a₂ T0 σ x → BddOn x → ∀ t, 0 ≤ t → x t = pvStep a₁ a₂ T0 σ t := by
  have hS := stepSol_solvesStep ha₂ hσ hM a₁ T0
  have h0 : stepSol a₁ a₂ T0 σ 0 = stepPV0 a₁ a₂ T0 σ := by
    unfold stepSol
    simp only [hT0, ↓reduceIte, vocFrom_self]
  refine ⟨hS, (step_bddOn_iff ha₂ hσ hM hT0 hS).2 h0, fun x hx hb t ht => ?_⟩
  have hx0 := (step_bddOn_iff ha₂ hσ hM hT0 hx).1 hb
  rw [← stepSol_eq_pvStep hσ]
  rcases le_total t T0 with htT | htT
  · rw [step_before hσ hx ht htT, hx0]
    unfold stepSol
    simp only [htT, ↓reduceIte]
  · have h1 := step_sub_pv ha₂ hσ hM hT0 hx htT
    rw [hx0, sub_self, mul_zero, mul_zero, sub_eq_zero] at h1
    rw [h1]
    unfold stepSol
    rcases eq_or_lt_of_le htT with h | h
    · simp only [h.ge, ↓reduceIte]
      rw [← h, vocFrom_stepPV0]
    · simp only [not_le.2 h, ↓reduceIte]

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula, survey E6.2): with
`r - g = -1%` for 20 years and `+1%` after, the unique non-explosive initial debt-to-GDP ratio is
`∫₀^{20} e^{0.01τ} σ_τ dτ + e^{0.01·20} ∫_{20}^∞ e^{-0.01(τ-20)} σ_τ dτ`: the book's display with
FUTURE surplus ratios `σ_{t+τ}` (at `t = 0`). -/
theorem book_twenty_year_formula (σ : ℝ → ℝ) :
    stepPV0 (-0.01) 0.01 20 σ = (∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * σ τ) +
      exp (0.01 * 20) * ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * σ τ := by
  unfold stepPV0 pv
  rw [← integral_Ioi_comp_add (fun τ => exp (-0.01 * (τ - 20)) * σ τ) 20]
  congr 2
  · funext τ
    ring_nf
  · ring_nf
  · congr 1
    funext u
    ring_nf

/-- Cochrane (2023), §6.4.1, p. 196, the 20-year display as printed (at `t = 0`): it discounts
PAST surplus ratios `σ_{t-τ}`. -/
noncomputable def printed20 (σ : ℝ → ℝ) : ℝ :=
  (∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * σ (0 - τ)) +
    exp (0.01 * 20) * ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * σ (0 - τ)

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2): a surplus path that is zero from date 0 on but
positive in the past, `σ_v = min(1, max(0, -v))`. -/
noncomputable def pastOnly (v : ℝ) : ℝ := min 1 (max 0 (-v))

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2): the printed 20-year formula is wrong. For the
surplus path `pastOnly` (zero from date 0 on), the unique bounded solution starts at `x̂₀ = 0`, but
the printed formula is strictly positive. -/
theorem printed20_wrong :
    stepPV0 (-0.01) 0.01 20 pastOnly = 0 ∧ 0 < printed20 pastOnly := by
  have hc : Continuous pastOnly := by unfold pastOnly; fun_prop
  have hM : ∀ u, |pastOnly u| ≤ 1 := by
    intro u
    unfold pastOnly
    rw [abs_le]
    constructor
    · exact le_min (by norm_num) (le_trans (by norm_num) (le_max_left 0 (-u)))
    · exact min_le_left _ _
  have hz : ∀ t, 0 ≤ t → pastOnly t = 0 := by
    intro t ht
    unfold pastOnly
    rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
  refine ⟨?_, ?_⟩
  · have hS : SolvesStep (-0.01) 0.01 20 pastOnly (fun _ => 0) := by
      refine ⟨continuousOn_const, fun t ht => ?_, fun t ht => ?_⟩
      · rw [hz t ht.1.le, mul_zero, sub_zero]
        exact hasDerivAt_const t 0
      · rw [hz t (by linarith), mul_zero, sub_zero]
        exact hasDerivAt_const t 0
    have := (step_bddOn_iff (by norm_num) hc hM (by norm_num) hS).1
      ⟨0, fun _ _ => by simp⟩
    exact this.symm
  · unfold printed20
    have h1 : 0 < ∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * pastOnly (0 - τ) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        ((by fun_prop : Continuous fun τ => exp (0.01 * τ) * pastOnly (0 - τ)).intervalIntegrable
          _ _) (fun τ hτ => ?_) (by norm_num)
      refine mul_pos (exp_pos _) ?_
      unfold pastOnly
      rw [zero_sub, neg_neg, max_eq_right hτ.1.le]
      exact lt_min (by norm_num) hτ.1
    have h2 : 0 ≤ ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * pastOnly (0 - τ) := by
      refine setIntegral_nonneg measurableSet_Ioi fun τ _ => ?_
      refine mul_nonneg (exp_pos _).le ?_
      unfold pastOnly
      exact le_min (by norm_num) (le_max_left _ _)
    have h3 := exp_pos (0.01 * 20 : ℝ)
    nlinarith

/-! ### (D5) Discrete time -/

/-- Cochrane (2023), §6.4.1, p. 196 (discrete analogue of (6.4)): `x_{t+1} = γ x_t - w_t`, with
`γ = (1+r)/(1+g)`. -/
def SolvesD (γ : ℝ) (w x : ℕ → ℝ) : Prop := ∀ t, x (t + 1) = γ * x t - w t

/-- Cochrane (2023), §6.4.1, p. 196: a bounded sequence. -/
def BddD (x : ℕ → ℝ) : Prop := ∃ K, ∀ t, |x t| ≤ K

/-- Cochrane (2023), §6.4.1, p. 196: the discrete forward present value
`x̂_t = ∑_{j ≥ 0} w_{t+j}/γ^{j+1}`. -/
noncomputable def pvD (γ : ℝ) (w : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, w (t + j) / γ ^ (j + 1)

/-- Cochrane (2023), §6.4.1, p. 196: the discrete backward solution from `x₀`. -/
noncomputable def iterD (γ : ℝ) (w : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => γ * iterD γ w x0 t - w t

variable {γ : ℝ} {w y v : ℕ → ℝ}

/-- Cochrane (2023), §6.4.1, p. 196: `γ = (1+r)/(1+g) > 1` iff `r > g` (for `1 + g > 0`). -/
theorem gamma_gt_one_iff {r g : ℝ} (hg : 0 < 1 + g) : 1 < (1 + r) / (1 + g) ↔ g < r := by
  rw [one_lt_div hg]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §6.4.1, p. 196: the backward solution solves the discrete equation. -/
theorem iterD_solves (γ : ℝ) (w : ℕ → ℝ) (x0 : ℝ) : SolvesD γ w (iterD γ w x0) := fun _ => rfl

/-- Cochrane (2023), §6.4.1, p. 196: two discrete solutions differ by `γ^t (x₀ - z₀)`. -/
theorem solvesD_sub (hy : SolvesD γ w y) (hv : SolvesD γ w v) (t : ℕ) :
    y t - v t = γ ^ t * (y 0 - v 0) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hy n, hv n, pow_succ]
    linear_combination γ * ih

/-- Cochrane (2023), §6.4.1, p. 196: the terms of the discrete present value are bounded by
`(M/γ)(1/γ)^j`. -/
theorem abs_pvD_term_le (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t j : ℕ) :
    |w (t + j) / γ ^ (j + 1)| ≤ M / γ * (1 / γ) ^ j := by
  have hγ0 : 0 < γ := by linarith
  rw [abs_div, abs_of_pos (pow_pos hγ0 _), div_le_iff₀ (pow_pos hγ0 _)]
  calc |w (t + j)| ≤ M := hw _
    _ = M / γ * (1 / γ) ^ j * γ ^ (j + 1) := by
        rw [div_pow, one_pow, pow_succ]
        field_simp

/-- Cochrane (2023), §6.4.1, p. 196: for `γ > 1` and bounded `w` the discrete present value is an
absolutely convergent series. -/
theorem summable_pvD (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) :
    Summable (fun j : ℕ => w (t + j) / γ ^ (j + 1)) := by
  have hγ0 : 0 < γ := by linarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity)
    ((div_lt_one hγ0).2 hγ)).mul_left (M / γ)) (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact abs_pvD_term_le hγ hw t j

/-- Cochrane (2023), §6.4.1, p. 196: `|x̂_t| ≤ M/(γ - 1)`. -/
theorem abs_pvD_le (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) : |pvD γ w t| ≤ M / (γ - 1) := by
  have hγ0 : 0 < γ := by linarith
  have hq0 : (0 : ℝ) ≤ 1 / γ := by positivity
  have hq1 : 1 / γ < 1 := (div_lt_one hγ0).2 hγ
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (M / γ)
  have hn : Summable (fun j : ℕ => ‖w (t + j) / γ ^ (j + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => (Real.norm_eq_abs _).trans_le (abs_pvD_term_le hγ hw t j)) hg
  have hsum : ∑' j : ℕ, M / γ * (1 / γ) ^ j = M / (γ - 1) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    have : γ - 1 ≠ 0 := by linarith
    field_simp
  calc |pvD γ w t| = ‖∑' j : ℕ, w (t + j) / γ ^ (j + 1)‖ := rfl
    _ ≤ ∑' j : ℕ, ‖w (t + j) / γ ^ (j + 1)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, M / γ * (1 / γ) ^ j :=
        Summable.tsum_le_tsum (fun j => (Real.norm_eq_abs _).trans_le
          (abs_pvD_term_le hγ hw t j)) hn hg
    _ = M / (γ - 1) := hsum

/-- Cochrane (2023), §6.4.1, p. 196: the present value satisfies `x̂_t = (w_t + x̂_{t+1})/γ`. -/
theorem pvD_succ (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) :
    pvD γ w t = (w t + pvD γ w (t + 1)) / γ := by
  have hγ0 : γ ≠ 0 := by linarith
  unfold pvD
  rw [(summable_pvD hγ hw t).tsum_eq_zero_add]
  have : ∀ j : ℕ, w (t + (j + 1)) / γ ^ (j + 1 + 1) = w (t + 1 + j) / γ ^ (j + 1) / γ := by
    intro j
    rw [show t + (j + 1) = t + 1 + j by ring, pow_succ γ (j + 1)]
    field_simp
  simp_rw [this, tsum_div_const]
  simp only [add_zero, zero_add, pow_one]
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` the present value solves the discrete
equation. -/
theorem pvD_solves (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) : SolvesD γ w (pvD γ w) := by
  intro t
  have hγ0 : γ ≠ 0 := by linarith
  rw [pvD_succ hγ hw t]
  field_simp
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` a solution that does not start at the
present value explodes. -/
theorem tendsto_abs_of_ne_D (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y)
    (hne : y 0 ≠ pvD γ w 0) : Tendsto (fun t => |y t|) atTop atTop := by
  set d := |y 0 - pvD γ w 0| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hγ0 : 0 < γ := by linarith
  have hlow : ∀ t, γ ^ t * d + -(M / (γ - 1)) ≤ |y t| := by
    intro t
    have h1 := solvesD_sub hy (pvD_solves hγ hw) t
    have h2 := abs_pvD_le hγ hw t
    have h3 : γ ^ t * d = |y t - pvD γ w t| := by
      rw [h1, abs_mul, abs_of_pos (pow_pos hγ0 _)]
    have h4 := abs_sub (y t) (pvD γ w t)
    linarith
  exact tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hγ).atTop_mul_const hd))

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` a discrete solution is bounded iff it
starts at the present value. -/
theorem bddD_iff (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) :
    BddD y ↔ y 0 = pvD γ w 0 := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    obtain ⟨t, ht⟩ := ((tendsto_abs_of_ne_D hγ hw hy hne).eventually_gt_atTop K).exists
    linarith [hK t]
  · intro h
    refine ⟨M / (γ - 1), fun t => ?_⟩
    have := solvesD_sub hy (pvD_solves hγ hw) t
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact abs_pvD_le hγ hw t

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` the unique bounded solution is
`x_t = ∑_j w_{t+j}/γ^{j+1}` at every date. -/
theorem eq_pvD_of_bddD (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) (hb : BddD y)
    (t : ℕ) : y t = pvD γ w t := by
  have := solvesD_sub hy (pvD_solves hγ hw) t
  rw [(bddD_iff hγ hw hy).1 hb, sub_self, mul_zero, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D5, transversality): for `γ > 1`, `x_t/γ^t → 0` iff the
solution starts at the present value. -/
theorem tvcD_iff (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) :
    Tendsto (fun t => y t / γ ^ t) atTop (𝓝 0) ↔ y 0 = pvD γ w 0 := by
  have hγ0 : 0 < γ := by linarith
  have he : ∀ t, pvD γ w t / γ ^ t + (y 0 - pvD γ w 0) = y t / γ ^ t := by
    intro t
    have h1 := solvesD_sub hy (pvD_solves hγ hw) t
    have hp := (pow_pos hγ0 t).ne'
    field_simp
    linarith
  have hq : Tendsto (fun t : ℕ => (1 / γ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hγ0).2 hγ)
  have hpv : Tendsto (fun t => pvD γ w t / γ ^ t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => M / (γ - 1) * (1 / γ) ^ t) (fun t => ?_)
      (by simpa using hq.const_mul (M / (γ - 1)))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hγ0 _), div_pow, one_pow,
      ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (abs_pvD_le hγ hw t) (pow_pos hγ0 _).le
  have hlim : Tendsto (fun t => y t / γ ^ t) atTop (𝓝 (y 0 - pvD γ w 0)) := by
    have := hpv.add_const (y 0 - pvD γ w 0)
    rw [zero_add] at this
    exact this.congr he
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rw [h, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `0 ≤ γ < 1` every discrete solution is bounded,
`|x_t| ≤ |x₀| + M/(1 - γ)`. -/
theorem abs_le_of_lt_one (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y)
    (t : ℕ) : |y t| ≤ |y 0| + M / (1 - γ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hw 0)
  have h1γ : 0 < 1 - γ := by linarith
  have hB : 0 ≤ M / (1 - γ) := div_nonneg hM0 h1γ.le
  induction t with
  | zero => linarith
  | succ n ih =>
    rw [hy n]
    have hkey : γ * (M / (1 - γ)) + M = M / (1 - γ) := by
      field_simp
      ring
    calc |γ * y n - w n| ≤ |γ * y n| + |w n| := abs_sub _ _
      _ = γ * |y n| + |w n| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * (|y 0| + M / (1 - γ)) + M := by gcongr; exact hw n
      _ ≤ |y 0| + M / (1 - γ) := by nlinarith [abs_nonneg (y 0)]

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `0 ≤ γ < 1` any two discrete solutions converge. -/
theorem tendsto_sub_D (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hy : SolvesD γ w y) (hv : SolvesD γ w v) :
    Tendsto (fun t => y t - v t) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ).mul_const (y 0 - v 0)
  rw [zero_mul] at this
  exact this.congr fun t => (solvesD_sub hy hv t).symm

/-- Cochrane (2023), §6.4.1, p. 196 (D5, knife edge `γ = 1`): `x_t = x₀ - ∑_{j<t} w_j`. -/
theorem eq_of_one (hy : SolvesD 1 w y) (t : ℕ) : y t = y 0 - ∑ j ∈ Finset.range t, w j := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hy n, ih, Finset.sum_range_succ]
    ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5, knife edge): for `γ = 1` a solution is bounded iff
the partial sums of `w` are bounded. -/
theorem bddD_iff_one (hy : SolvesD 1 w y) :
    BddD y ↔ ∃ K, ∀ t, |∑ j ∈ Finset.range t, w j| ≤ K := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |y 0|, fun t => ?_⟩
    have h1 := eq_of_one hy t
    have : ∑ j ∈ Finset.range t, w j = y 0 - y t := by linarith
    rw [this]
    exact (abs_sub _ _).trans (by linarith [hK t])
  · rintro ⟨K, hK⟩
    refine ⟨|y 0| + K, fun t => ?_⟩
    rw [eq_of_one hy t]
    exact (abs_sub _ _).trans (by linarith [hK t])

/-- Cochrane (2023), §6.4.1, p. 196 (D5, nominal debt): for `γ > 1` the price level `P₀ > 0`
yields a bounded path from `x₀ = B₀/(P₀ y₀)` iff `P₀ = B₀/(y₀ x̂₀)`. -/
theorem nominal_determinacy_D (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) {B0 y0 P0 : ℝ} (hB0 : 0 < B0)
    (hy0 : 0 < y0) (hP0 : 0 < P0) :
    (∃ x, SolvesD γ w x ∧ x 0 = B0 / (P0 * y0) ∧ BddD x) ↔ P0 = B0 / (y0 * pvD γ w 0) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (bddD_iff hγ hw hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pvD γ w 0 := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pvD γ w 0 := by
      have : 0 < B0 / (y0 * pvD γ w 0) := hP ▸ hP0
      rcases div_pos_iff.1 this with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pvD γ w 0 := pos_of_mul_pos_right hpos hy0.le
    refine ⟨pvD γ w, pvD_solves hγ hw, ?_, ⟨_, abs_pvD_le hγ hw⟩⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), §6.4.1, p. 196 (D5, "indeterminacy, not infinity"): for `0 ≤ γ < 1` every
price level gives a bounded discrete debt-to-GDP path. -/
theorem nominal_indeterminacy_D (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hw : ∀ t, |w t| ≤ M)
    (B0 y0 P0 : ℝ) : ∃ x, SolvesD γ w x ∧ x 0 = B0 / (P0 * y0) ∧ BddD x :=
  ⟨iterD γ w (B0 / (P0 * y0)), iterD_solves γ w _, rfl,
    ⟨_, abs_le_of_lt_one hγ0 hγ hw (iterD_solves γ w _)⟩⟩

/-! ### (D6) Flows and the `r = g` discontinuity; numbers -/

/-- Cochrane (2023), §6.4.2, p. 198 (D6): a constant debt-to-GDP ratio `x*` solves (6.4) with a
constant surplus ratio `σ*` iff `σ* = (r - g) x*`. -/
theorem steady_state_iff (a xs ss : ℝ) :
    SolvesOn a (fun _ => ss) (fun _ => xs) ↔ ss = a * xs := by
  constructor
  · rintro ⟨-, h⟩
    have := (h 1 one_pos).unique (hasDerivAt_const (1 : ℝ) xs)
    linarith
  · intro h
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    rw [h, sub_self]
    exact hasDerivAt_const t xs

/-- Cochrane (2023), §6.4.2, p. 198 (D6): the steady-state surplus `(r - g) x*` is continuous in
`r - g`, in particular across `r = g`. -/
theorem steady_surplus_continuous (xs : ℝ) : Continuous (fun a : ℝ => a * xs) :=
  continuous_id.mul continuous_const

/-- Cochrane (2023), §6.4.2, p. 198 (D6, discrete): a constant `x*` solves the discrete equation
with constant `w*` iff `w* = (γ - 1) x*`. -/
theorem steady_state_iff_D (γ xs ws : ℝ) :
    SolvesD γ (fun _ => ws) (fun _ => xs) ↔ ws = (γ - 1) * xs := by
  constructor
  · intro h
    have := h 0
    linarith
  · intro h t
    rw [h]
    ring

/-- Cochrane (2023), §6.4.2, p. 198: at 100% debt-to-GDP, `r - g = ±0.01%` needs a steady surplus
of `±0.01%` of GDP. -/
theorem book_flow_basis_point :
    SolvesOn 0.0001 (fun _ => 0.0001) (fun _ => 1) ∧
      SolvesOn (-0.0001) (fun _ => -0.0001) (fun _ => 1) := by
  constructor <;> rw [steady_state_iff] <;> norm_num

/-- Cochrane (2023), §6.4.3, p. 199: at 100% debt-to-GDP, `r - g = -1%` funds a steady primary
deficit of 1% of GDP (and no more). -/
theorem book_one_percent_deficit (ss : ℝ) :
    SolvesOn (-0.01) (fun _ => ss) (fun _ => 1) ↔ ss = -0.01 := by
  rw [steady_state_iff]
  norm_num

/-- Cochrane (2023), §6.4.2, p. 198: with zero primary surpluses the debt-to-GDP ratio is
`x_t = e^{(r-g) t} x₀`. -/
theorem zero_surplus_path (hx : SolvesOn a (fun _ => 0) x) {t : ℝ} (ht : 0 ≤ t) :
    x t = exp (a * t) * x 0 := by
  rw [solvesOn_eq continuous_const hx ht]
  unfold vocFrom
  simp

/-- Cochrane (2023), §6.4.2, p. 198: with zero surpluses and `r - g = -0.01%`, 150% debt-to-GDP
falls to exactly 50% after `T = -log(0.5/1.5)/0.0001 = log 3/0.0001` years, while with
`r - g = +0.01%` it rises to exactly 450% over the same span. -/
theorem book_growth_out_of_debt {x z : ℝ → ℝ} (hx : SolvesOn (-0.0001) (fun _ => 0) x)
    (hz : SolvesOn 0.0001 (fun _ => 0) z) (hx0 : x 0 = 1.5) (hz0 : z 0 = 1.5) :
    -log (0.5 / 1.5) / 0.0001 = log 3 / 0.0001 ∧
      x (log 3 / 0.0001) = 0.5 ∧ z (log 3 / 0.0001) = 4.5 := by
  have hT : (0 : ℝ) ≤ log 3 / 0.0001 := div_nonneg (log_nonneg (by norm_num)) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (0.5 : ℝ) / 1.5 = 3⁻¹ by norm_num, log_inv, neg_neg]
  · rw [zero_surplus_path hx hT, hx0, show -0.0001 * (log 3 / 0.0001) = -log 3 by ring,
      exp_neg, exp_log (by norm_num)]
    norm_num
  · rw [zero_surplus_path hz hT, hz0, show 0.0001 * (log 3 / 0.0001) = log 3 by ring,
      exp_log (by norm_num)]
    norm_num

/-- Cochrane (2023), §6.4.2, p. 198: `1.0986 < log 3 < 1.0987`. -/
theorem log_three_bounds : (1.0986 : ℝ) < log 3 ∧ log 3 < 1.0987 := by
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  constructor
  · rw [lt_log_iff_exp_lt (by norm_num), show (1.0986 : ℝ) = 1 + 0.0986 by norm_num, exp_add]
    have hb := Real.exp_bound (x := 0.0986) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hu := (abs_le.1 hb).2
    have h0 := exp_pos (0.0986 : ℝ)
    nlinarith
  · rw [log_lt_iff_lt_exp (by norm_num), show (1.0987 : ℝ) = 1 + 0.0987 by norm_num, exp_add]
    have hb := Real.exp_bound (x := 0.0987) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hl := (abs_le.1 hb).1
    have h0 := exp_pos (1 : ℝ)
    nlinarith

/-- Cochrane (2023), §6.4.2, p. 198: the book's "11,000 years" is `log 3/0.0001`, strictly between
10,986 and 10,987 years. -/
theorem book_years_bounds : (10986 : ℝ) < log 3 / 0.0001 ∧ log 3 / 0.0001 < 10987 := by
  obtain ⟨h1, h2⟩ := log_three_bounds
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- Cochrane (2023), §6.4.2, p. 198: the book's rounded computation
`150 × e^{0.0001 × 11000} = 150 e^{1.1}` lies between 450.6 and 450.7 ("450%"). -/
theorem book_450_bounds :
    (450.6 : ℝ) < 150 * exp (0.0001 * 11000) ∧ 150 * exp (0.0001 * 11000) < 450.7 := by
  rw [show (0.0001 : ℝ) * 11000 = 1 + 0.1 by norm_num, exp_add]
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hb := Real.exp_bound (x := 0.1) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hl := (abs_le.1 hb).1
  have hu := (abs_le.1 hb).2
  have h0 := exp_pos (1 : ℝ)
  have h1 := exp_pos (0.1 : ℝ)
  constructor <;> nlinarith

/-- Cochrane (2023), §6.4.1, p. 196: with `r - g = -1%` and zero surpluses for 20 years, the
debt-to-GDP ratio falls to `e^{-0.2}` of its initial value. -/
theorem twenty_years_zero_surplus (hx : SolvesOn (-0.01) (fun _ => 0) x) :
    x 20 = exp (-0.2) * x 0 := by
  rw [zero_surplus_path hx (by norm_num)]
  norm_num

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2, rounding): `e^{-0.2}` is between 81.87% and
81.88%, not the stated 80%. -/
theorem exp_neg_two_tenths_bounds :
    (0.8187 : ℝ) < exp (-0.2) ∧ exp (-0.2) < 0.8188 ∧ exp (-0.2 : ℝ) ≠ 0.8 := by
  have hb := Real.exp_bound (x := -0.2) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hl := (abs_le.1 hb).1
  have hu := (abs_le.1 hb).2
  refine ⟨by linarith, by linarith, fun h => by linarith⟩

end Cochrane.FiscalConstraints.RvsG

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A debt limit with stochastic surpluses (Theorem S)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, pp. 196–197.

With permanent `r < g` the debt-to-GDP ratio follows `x_{t+1} = γ x_t − σ_t` with
`γ = (1 + r)/(1 + g) ∈ [0, 1)`, where `σ_t` is the surplus-to-GDP ratio. The book argues
that with an upper limit on the debt-to-GDP ratio and a stationary (unmanaged) surplus
process, "you eventually flip 100 heads in a row": the debt ratio eventually exceeds the
bound, so no initial value of debt is sustainable (p. 197).

## Main results

* `frequently_exceeds` (**Theorem S**): independent surpluses, bounded above, with a
  probability of a deficit of size at least `c` bounded away from zero, push the debt ratio
  above every level `M < c/(1 − γ)` infinitely often, almost surely, from every initial
  debt. The proof is the second Borel–Cantelli lemma applied to independent blocks of
  `k` consecutive bad draws.
* `not_sustainable`: hence the event "debt stays below the limit forever" has probability 0.
* `unbounded_of_unbounded_deficits`, `iid_unbounded`, `gaussian_iid_unbounded`: if large
  deficits have positive probability at every size (e.g. i.i.d. Gaussian surpluses), the debt
  ratio is almost surely unbounded above.
* `debtPath_le_of_bounded_deficits` (correction): if deficits are bounded, `σ_t ≥ −c`, the
  debt ratio never exceeds `max x₀ (c/(1 − γ))`. So "even if we limit the support of the
  surplus distribution ... the integral of the surplus eventually exceeds any bound" (p. 197)
  is false for bounds above `c/(1 − γ)`; it holds for bounds below `c/(1 − γ)` (Theorem S).
* `managedPath_le`: a managed surplus that rises just enough to avoid the boundary keeps debt
  below the limit from date 1 on (p. 197, "we must already imagine a managed surplus
  process").
-/

namespace Cochrane.FiscalConstraints.DebtLimitStochastic

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*}

/-- Cochrane (2023), (6.4) p. 196 in discrete time: the debt-to-GDP ratio
`x_{t+1} = γ x_t − σ_t`, `x_0 = x₀`, with `γ = (1 + r)/(1 + g)` and surplus ratio `σ_t`: on each
path `ω` it is the deterministic backward solution `RvsG.iterD` driven by `σ_t(ω)`. -/
noncomputable def debtPath (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  RvsG.iterD γ (fun s => σ s ω) x₀ t

/-- Cochrane (2023), (6.4) p. 196: the recursion of `debtPath`. -/
theorem debtPath_succ (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    debtPath γ x₀ σ (t + 1) ω = γ * debtPath γ x₀ σ t ω - σ t ω := rfl

/-- Cochrane (2023), p. 197: with surpluses bounded above by `K` and `0 ≤ γ < 1`, the debt
ratio is bounded below by `−(|x₀| + |K|/(1 − γ))`. -/
theorem debtPath_lower {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} {ω : Ω}
    (hK : ∀ t, σ t ω ≤ K) (t : ℕ) :
    -(|x₀| + |K| / (1 - γ)) ≤ debtPath γ x₀ σ t ω := by
  have h1 : 0 < 1 - γ := by linarith
  have hKd : 0 ≤ |K| / (1 - γ) := div_nonneg (abs_nonneg K) h1.le
  have hKe : |K| / (1 - γ) * (1 - γ) = |K| := div_mul_cancel₀ _ h1.ne'
  induction t with
  | zero =>
    change -(|x₀| + |K| / (1 - γ)) ≤ x₀
    linarith [neg_abs_le x₀]
  | succ t ih =>
    rw [debtPath_succ]
    have hσ := (hK t).trans (le_abs_self K)
    have h2 : γ * -(|x₀| + |K| / (1 - γ)) ≤ γ * debtPath γ x₀ σ t ω :=
      mul_le_mul_of_nonneg_left ih hγ0
    nlinarith [abs_nonneg x₀]

/-- Cochrane (2023), p. 197 ("flip 100 heads in a row"): after `k` consecutive deficits of
size at least `c`, `x_{t+k} ≥ γᵏ x_t + c (1 + γ + ⋯ + γᵏ⁻¹)`. -/
theorem debtPath_run {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) {σ : ℕ → Ω → ℝ} {ω : Ω} (t : ℕ) :
    ∀ k, (∀ j < k, σ (t + j) ω ≤ -c) →
      γ ^ k * debtPath γ x₀ σ t ω + c * ∑ i ∈ Finset.range k, γ ^ i ≤
        debtPath γ x₀ σ (t + k) ω := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hrun
    have hk := ih (fun j hj => hrun j (Nat.lt_succ_of_lt hj))
    have hlast := hrun k (Nat.lt_succ_self k)
    rw [← add_assoc, debtPath_succ, Finset.sum_range_succ', pow_succ]
    have hsum : ∑ i ∈ Finset.range k, γ ^ (i + 1) = γ * ∑ i ∈ Finset.range k, γ ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    have := mul_le_mul_of_nonneg_left hk hγ0
    nlinarith

/-- Cochrane (2023), p. 197: for any floor `−B` and any level `M < c/(1 − γ)` there is a run
length `k ≥ 1` such that `k` consecutive deficits of size `c` lift every debt ratio above the
floor to above `M`. -/
theorem exists_run_length {γ c M B : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) :
    ∃ k, 1 ≤ k ∧ ∀ x, -B ≤ x → M < γ ^ k * x + c * ∑ i ∈ Finset.range k, γ ^ i := by
  have h1 : 0 < 1 - γ := by linarith
  set D := c / (1 - γ) with hD
  have hlim : Tendsto (fun k : ℕ => γ ^ k * (D + B)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (D + B)
  have hev : ∀ᶠ k : ℕ in atTop, γ ^ k * (D + B) < D - M ∧ 1 ≤ k :=
    (hlim.eventually (gt_mem_nhds (by linarith))).and (eventually_ge_atTop 1)
  obtain ⟨k, hk, hk1⟩ := hev.exists
  refine ⟨k, hk1, fun x hx => ?_⟩
  have hgeo : c * ∑ i ∈ Finset.range k, γ ^ i = D * (1 - γ ^ k) := by
    have hne : γ - 1 ≠ 0 := by linarith
    rw [geom_sum_eq (by linarith : γ ≠ 1), hD]
    field_simp
    ring
  rw [hgeo]
  have hpk : 0 ≤ γ ^ k := pow_nonneg hγ0 k
  nlinarith [mul_le_mul_of_nonneg_left hx hpk]

/-- Cochrane (2023), p. 197: the event that the surpluses of block `n`, dates
`n k, …, n k + k − 1`, are all deficits of size at least `c`. -/
def badBlock (σ : ℕ → Ω → ℝ) (c : ℝ) (k n : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range k, σ (n * k + j) ⁻¹' Set.Iic (-c)

/-- Cochrane (2023), p. 197: block events are measurable. -/
theorem measurableSet_badBlock [MeasurableSpace Ω] {σ : ℕ → Ω → ℝ}
    (hσ : ∀ t, Measurable (σ t)) (c : ℝ) (k n : ℕ) : MeasurableSet (badBlock σ c k n) :=
  Finset.measurableSet_biInter _ fun _ _ => measurableSet_Iic.preimage (hσ _)

/-- Cochrane (2023), p. 197: the index map `(n, j) ↦ n k + j` is injective on `j < k`, so
different blocks use different dates. -/
theorem block_index_injOn (S : Finset ℕ) (k : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * k + p.2) ↑(S ×ˢ Finset.range k) := by
  intro p hp q hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hq
  have hk : 0 < k := by omega
  have h' : p.2 + k * p.1 = q.2 + k * q.1 := by
    simp only at h
    rw [mul_comm k p.1, mul_comm k q.1, add_comm p.2, add_comm q.2]
    exact h
  have hdiv := congrArg (· / k) h'
  have hmod := congrArg (· % k) h'
  simp only [Nat.add_mul_div_left _ _ hk, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hp.2, Nat.div_eq_of_lt hq.2, Nat.mod_eq_of_lt hp.2,
    Nat.mod_eq_of_lt hq.2, zero_add] at hdiv hmod
  exact Prod.ext hdiv hmod

/-- Cochrane (2023), p. 197: a union of blocks is an intersection of single-date events over
the image of the block indices. -/
theorem biInter_badBlock (σ : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (S : Finset ℕ) :
    (⋂ n ∈ S, badBlock σ c k n) =
      ⋂ i ∈ (S ×ˢ Finset.range k).image (fun p : ℕ × ℕ => p.1 * k + p.2),
        σ i ⁻¹' Set.Iic (-c) := by
  ext ω
  simp only [badBlock, Set.mem_iInter, Finset.mem_image, Finset.mem_product,
    Finset.mem_range, Prod.exists, forall_exists_index, and_imp]
  constructor
  · rintro h i n j hn hj rfl
    exact h n hn j hj
  · intro h n hn j hj
    exact h _ n j hn hj rfl

/-- Cochrane (2023), p. 197: the probability of a union of blocks is the product of the
single-date probabilities (independence of the surpluses). -/
theorem measure_biInter_badBlock [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hind : iIndepFun σ μ) (c : ℝ) (k : ℕ) (S : Finset ℕ) :
    μ (⋂ n ∈ S, badBlock σ c k n) =
      ∏ n ∈ S, ∏ j ∈ Finset.range k, μ (σ (n * k + j) ⁻¹' Set.Iic (-c)) := by
  rw [biInter_badBlock, hind.measure_inter_preimage_eq_mul _ (fun _ _ => measurableSet_Iic),
    Finset.prod_image (block_index_injOn S k), Finset.prod_product]

/-- Cochrane (2023), p. 197: the block events are mutually independent. -/
theorem iIndepSet_badBlock [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ μ) (c : ℝ) (k : ℕ) :
    iIndepSet (badBlock σ c k) μ := by
  rw [iIndepSet_iff_meas_biInter (measurableSet_badBlock hσ c k)]
  intro S
  rw [measure_biInter_badBlock hind]
  refine Finset.prod_congr rfl fun n _ => ?_
  have h := measure_biInter_badBlock hind c k {n}
  simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton] at h
  exact h.symm

/-- Cochrane (2023), p. 197: with probability at least `p` of a bad draw at every date, each
block has probability at least `pᵏ`, so the block probabilities have an infinite sum. -/
theorem tsum_badBlock_eq_top [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hind : iIndepFun σ μ) {c : ℝ} {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ μ (σ t ⁻¹' Set.Iic (-c))) (k : ℕ) :
    ∑' n, μ (badBlock σ c k n) = ⊤ := by
  have hle : ∀ n, p ^ k ≤ μ (badBlock σ c k n) := fun n => by
    have h := measure_biInter_badBlock hind c k {n}
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton] at h
    rw [h]
    calc p ^ k = ∏ _j ∈ Finset.range k, p := by simp
      _ ≤ _ := Finset.prod_le_prod fun j _ => hp _
  refine top_unique ?_
  rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (pow_ne_zero k hp0)]
  exact ENNReal.tsum_le_tsum hle

/-- **Theorem S** (Cochrane (2023), §6.4.1, p. 197, "you eventually flip 100 heads in a
row"). Let `0 ≤ γ < 1` (permanent `r < g`), let the surplus ratios `σ_t` be independent,
measurable, almost surely bounded above by `K`, and let every date carry probability at least
`p > 0` of a deficit of size at least `c`. Then from every initial debt ratio `x₀`, almost
surely the debt ratio exceeds every level `M < c/(1 − γ)` infinitely often. -/
theorem frequently_exceeds [MeasureSpace Ω] {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t))
    (hind : iIndepFun σ volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K) {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    ∀ᵐ ω, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  have : IsProbabilityMeasure (volume : Measure Ω) := hind.isProbabilityMeasure
  obtain ⟨k, hk1, hk⟩ := exists_run_length (B := |x₀| + |K| / (1 - γ)) hγ0 hγ1 hM
  have hL : volume (limsup (badBlock σ c k) atTop) = 1 :=
    measure_limsup_eq_one (measurableSet_badBlock hσ c k) (iIndepSet_badBlock hσ hind c k)
      (tsum_badBlock_eq_top hind hp0 hp k)
  have hae : ∀ᵐ ω, ω ∈ limsup (badBlock σ c k) atTop := by
    rw [ae_iff]
    have hm := MeasurableSet.measurableSet_limsup (measurableSet_badBlock hσ c k)
    have := (prob_compl_eq_zero_iff hm).mpr hL
    simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hK, hae] with ω hKω hω
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  rw [Filter.frequently_atTop] at hω ⊢
  intro N
  obtain ⟨n, hnN, hn⟩ := hω N
  refine ⟨n * k + k, ?_, ?_⟩
  · nlinarith
  · have hrun : ∀ j < k, σ (n * k + j) ω ≤ -c := fun j hj => by
      have := Set.mem_iInter₂.mp hn j (Finset.mem_range.mpr hj)
      simpa using this
    have h1 := debtPath_run (x₀ := x₀) hγ0 (n * k) k hrun
    have h2 := hk _ (debtPath_lower hγ0 hγ1 hKω (n * k))
    linarith

/-- Cochrane (2023), p. 197 ("no value of debt `b₀/y₀` is sustainable"): under Theorem S's
hypotheses the event that the debt ratio stays below the limit `M` forever has probability
zero, whatever the initial debt `x₀`. -/
theorem not_sustainable [MeasureSpace Ω] {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t))
    (hind : iIndepFun σ volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K) {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    volume {ω | ∀ t, debtPath γ x₀ σ t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [frequently_exceeds hγ0 hγ1 hM hσ hind hK hp0 hp] with ω hω hall
  obtain ⟨t, ht⟩ := hω.exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197 (an AR(1) "ranges over the entire real line"): if deficits of
every size have probability bounded away from zero at every date, the debt ratio is almost
surely unbounded above: it exceeds every level infinitely often. -/
theorem unbounded_of_unbounded_deficits [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    (hdef : ∀ c : ℝ, ∃ p : ENNReal, p ≠ 0 ∧ ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  have h1 : 0 < 1 - γ := by linarith
  have hn : ∀ n : ℕ, ∀ᵐ ω, ∃ᶠ t in atTop, (n : ℝ) < debtPath γ x₀ σ t ω := by
    intro n
    obtain ⟨p, hp0, hp⟩ := hdef ((n + 1) * (1 - γ))
    refine frequently_exceeds hγ0 hγ1 ?_ hσ hind hK hp0 hp
    rw [mul_div_assoc, div_self h1.ne', mul_one]
    linarith
  filter_upwards [ae_all_iff.2 hn] with ω hω M
  obtain ⟨n, hnM⟩ := exists_nat_gt M
  exact (hω n).mono fun t ht => hnM.trans ht

/-- Cochrane (2023), p. 197: i.i.d. surpluses (identically distributed and independent)
whose deficits are unbounded below in distribution make the debt ratio almost surely
unbounded above. -/
theorem iid_unbounded [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    (hdef : ∀ c : ℝ, volume (σ 0 ⁻¹' Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  refine unbounded_of_unbounded_deficits hγ0 hγ1 hσ hind hK fun c => ⟨_, hdef c, fun t => ?_⟩
  rw [(hident t).measure_mem_eq measurableSet_Iic]

/-- Cochrane (2023), p. 197: a Gaussian surplus (non-degenerate) puts positive probability on
deficits of every size. -/
theorem gaussian_deficit_pos [MeasureSpace Ω] {X : Ω → ℝ} (hX : Measurable X) {m : ℝ}
    {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map X volume = gaussianReal m v) (c : ℝ) :
    volume (X ⁻¹' Set.Iic (-c)) ≠ 0 := by
  rw [← Measure.map_apply hX measurableSet_Iic, hlaw]
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Iic] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197: i.i.d. Gaussian surplus shocks, truncated above at `K` almost
surely, make the debt ratio almost surely unbounded above (the discrete analogue of the
book's AR(1) argument). -/
theorem gaussian_iid_unbounded [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    {m : ℝ} {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map (σ 0) volume = gaussianReal m v) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω :=
  iid_unbounded hγ0 hγ1 hσ hind hident hK fun c => gaussian_deficit_pos (hσ 0) hv hlaw c

/-- Cochrane (2023), p. 197 (correction): with deficits bounded by `c` (`σ_t ≥ −c`), the debt
ratio never exceeds `max x₀ (c/(1 − γ))`, on every path. So bounded surplus support does NOT
make debt eventually exceed *any* bound; Theorem S needs the limit below `c/(1 − γ)`. -/
theorem debtPath_le_of_bounded_deficits {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} {ω : Ω} (hc : ∀ t, -c ≤ σ t ω) (t : ℕ) :
    debtPath γ x₀ σ t ω ≤ max x₀ (c / (1 - γ)) := by
  have h1 : 0 < 1 - γ := by linarith
  have hce : c / (1 - γ) * (1 - γ) = c := div_mul_cancel₀ _ h1.ne'
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    rw [debtPath_succ]
    have hm2 := le_max_right x₀ (c / (1 - γ))
    have h2 := mul_le_mul_of_nonneg_left ih hγ0
    have h3 := hc t
    rcases le_total (c / (1 - γ)) x₀ with h | h
    · rw [max_eq_left h] at h2 ⊢
      have hc' : c ≤ x₀ * (1 - γ) := by nlinarith
      nlinarith
    · rw [max_eq_right h] at h2 ⊢
      nlinarith

/-- Cochrane (2023), p. 197 (correction, counterexample to the printed claim): constant
deficits `σ_t = −c` with `c > 0` (a degenerate, bounded, stationary surplus) never push debt
above `max x₀ (c/(1 − γ))`; the level `max x₀ (c/(1 − γ)) + 1` is never reached. -/
theorem bounded_support_counterexample {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (t : ℕ)
    (ω : Ω) :
    debtPath γ x₀ (fun _ _ => -c) t ω < max x₀ (c / (1 - γ)) + 1 :=
  (debtPath_le_of_bounded_deficits (σ := fun _ _ => -c) (ω := ω) hγ0 hγ1 (fun _ => le_rfl)
    t).trans_lt (lt_add_one _)

/-- Cochrane (2023), p. 197 ("as debt starts to grow, the government increases surpluses so
as to avoid the boundary"): the managed path `x_{t+1} = min (γ x_t − ε_t) x̄`, generated by
the surplus `σ_t = ε_t + max 0 (γ x_t − ε_t − x̄)`. -/
noncomputable def managedPath (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar))

/-- Cochrane (2023), p. 197: the managed surplus keeps the debt ratio at or below the limit
`x̄` from date 1 on, for every shock path and every initial debt. -/
theorem managedPath_le (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    managedPath γ x₀ xbar ε (t + 1) ω ≤ xbar := by
  change γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)) ≤ xbar
  have := le_max_right 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)
  linarith

/-- Cochrane (2023), p. 197: the managed surplus departs from the unmanaged one only when the
boundary would otherwise be crossed: the extra surplus is zero whenever `γ x_t − ε_t ≤ x̄`. -/
theorem managedPath_eq_of_le {γ x₀ xbar : ℝ} {ε : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * managedPath γ x₀ xbar ε t ω - ε t ω ≤ xbar) :
    managedPath γ x₀ xbar ε (t + 1) ω = γ * managedPath γ x₀ xbar ε t ω - ε t ω := by
  change γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)) = _
  rw [max_eq_left (by linarith)]
  ring

end Cochrane.FiscalConstraints.DebtLimitStochastic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth theory, the transversality condition and `r < g`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.4, pp. 199–200.

The dynastic representative agent with utility `∫ e^{−δt} c_t^{1−γ}/(1−γ) dt` on a balanced
growth path `c_t = c₀ e^{g t}` has marginal utility `Λ_t = e^{−δt} c_t^{−γ}`, and the real
rate is its rate of decline, `r = δ + γ g` (6.6). The transversality condition for debt held
in a steady ratio to consumption, `lim e^{−δT} u'(c_T) b_T = 0`, holds exactly when `r > g`;
with `δ = 0` it holds iff `γ > 1` (p. 200). With population growth `n` and per-capita
consumption growing at `g − n`, `r = δ + γ (g − n)`, the transversality condition becomes
`r > g − n`, and `r < g` becomes compatible with it.

## Main results

* `hasDerivAt_log_marginalUtility`: (6.6) as an exact derivative, `−(d/dt) log Λ_t = δ + γ g`.
* `marginalUtility_ratio`: `Λ_τ/Λ_t = e^{−(δ+γg)(τ−t)}`, the discount factor of p. 203.
* `rate_gt_growth_iff`, `rate_gt_growth_of_standard`, `rate_lt_growth_iff`.
* `tvc_iff`: the TVC with a steady debt/consumption ratio holds iff `r > g`.
* `tvc_delta_zero_iff`: with `δ = 0` and `g > 0`, the TVC holds iff `γ > 1` (p. 200);
  `tvc_diverges_of_lt_one`: for `γ < 1` the TVC expression grows without bound.
* `rate_population`, `tvc_population_iff`, `population_allows_r_lt_g`: population growth
  (the criterion `r < g ⇔ δ + (γ − 1) g < γ n` is `DiscountGrowth.r_lt_g_population_iff`).
-/

namespace Cochrane.FiscalConstraints.GrowthTheoryTVC

open Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals
  (tendsto_const_mul_exp_zero_iff tendsto_const_mul_exp_atTop)

/-- Cochrane (2023), p. 199: balanced-growth consumption `c_t = c₀ e^{g t}`. -/
noncomputable def consumption (c₀ g t : ℝ) : ℝ := c₀ * Real.exp (g * t)

/-- Cochrane (2023), p. 199: discounted marginal utility `Λ_t = e^{−δt} c_t^{−γ}` of power
utility `c^{1−γ}/(1−γ)`. -/
noncomputable def marginalUtility (δ γ c₀ g t : ℝ) : ℝ :=
  Real.exp (-δ * t) * consumption c₀ g t ^ (-γ)

/-- Cochrane (2023), (6.6) p. 199: the consumer's real rate `r = δ + γ g`. -/
def rate (δ γ g : ℝ) : ℝ := δ + γ * g

/-- Cochrane (2023), p. 199: for `c₀ > 0`, `c_t^a = c₀^a e^{a g t}`. -/
theorem consumption_rpow {c₀ : ℝ} (hc : 0 < c₀) (g t a : ℝ) :
    consumption c₀ g t ^ a = c₀ ^ a * Real.exp (a * g * t) := by
  unfold consumption
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
  ring_nf

/-- Cochrane (2023), (6.6) p. 199: the log of discounted marginal utility is affine in time,
`log Λ_t = −γ log c₀ − (δ + γ g) t`. -/
theorem log_marginalUtility {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    Real.log (marginalUtility δ γ c₀ g t) = -γ * Real.log c₀ - rate δ γ g * t := by
  unfold marginalUtility rate
  rw [consumption_rpow hc, Real.log_mul (Real.exp_pos _).ne'
      (mul_pos (Real.rpow_pos_of_pos hc _) (Real.exp_pos _)).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_exp, Real.log_rpow hc]
  ring

/-- Cochrane (2023), (6.6) p. 199, as an exact derivative: the rate of decline of marginal
utility is `−(d/dt) log Λ_t = δ + γ g`, i.e. `(d/dt) log Λ_t = −(δ + γ g)`. -/
theorem hasDerivAt_log_marginalUtility {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    HasDerivAt (fun s => Real.log (marginalUtility δ γ c₀ g s)) (-rate δ γ g) t := by
  have h : (fun s => Real.log (marginalUtility δ γ c₀ g s)) =
      fun s => -γ * Real.log c₀ - rate δ γ g * s := by
    funext s; exact log_marginalUtility hc δ γ g s
  rw [h]
  have := ((hasDerivAt_id t).const_mul (rate δ γ g)).const_sub (-γ * Real.log c₀)
  simpa using this

/-- Cochrane (2023), (6.6) p. 199: discounted marginal utility is
`Λ_t = c₀^{−γ} e^{−(δ + γ g) t}`. -/
theorem marginalUtility_eq {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    marginalUtility δ γ c₀ g t = c₀ ^ (-γ) * Real.exp (-rate δ γ g * t) := by
  unfold marginalUtility rate
  rw [consumption_rpow hc, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- Cochrane (2023), p. 203: the marginal rate of substitution is the risk-free discount
factor, `Λ_τ/Λ_t = e^{−r (τ − t)}` with `r = δ + γ g`. -/
theorem marginalUtility_ratio {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t τ : ℝ) :
    marginalUtility δ γ c₀ g τ / marginalUtility δ γ c₀ g t =
      Real.exp (-rate δ γ g * (τ - t)) := by
  have h1 : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc _
  rw [marginalUtility_eq hc, marginalUtility_eq hc, mul_div_mul_left _ _ h1.ne',
    ← Real.exp_sub]
  congr 1
  ring

/-- Cochrane (2023), p. 199: `r > g` iff `δ + (γ − 1) g > 0`. -/
theorem rate_gt_growth_iff (δ γ g : ℝ) : g < rate δ γ g ↔ 0 < δ + (γ - 1) * g := by
  unfold rate; constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 199: `r < g` iff `δ < (1 − γ) g`. -/
theorem rate_lt_growth_iff (δ γ g : ℝ) : rate δ γ g < g ↔ δ < (1 - γ) * g := by
  unfold rate; constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 199 ("we usually think that `δ > 0` ... and that `γ ≥ 1`. Hence
`r > g`"), for non-negative growth. -/
theorem rate_gt_growth_of_standard {δ γ g : ℝ} (hδ : 0 < δ) (hγ : 1 ≤ γ) (hg : 0 ≤ g) :
    g < rate δ γ g := by
  rw [rate_gt_growth_iff]
  nlinarith

/-- Cochrane (2023), p. 199 ("one can deliver `r < g` with small `δ`, `γ < 1` and low `g`"):
for `γ < 1` and `g > 0`, every `0 ≤ δ < (1 − γ) g` gives `r < g`, and such `δ > 0` exist. -/
theorem rate_lt_growth_possible {γ g : ℝ} (hγ : γ < 1) (hg : 0 < g) :
    ∃ δ, 0 < δ ∧ rate δ γ g < g := by
  refine ⟨(1 - γ) * g / 2, by nlinarith, ?_⟩
  rw [rate_lt_growth_iff]
  nlinarith

/-- Cochrane (2023), p. 200: the transversality-condition term with `δ = 0`,
`u'(c_T) b_T = c_T^{1−γ} (b_T/c_T)`. -/
theorem tvc_term_identity {c b : ℝ} (hc : 0 < c) (γ : ℝ) :
    c ^ (-γ) * b = c ^ (1 - γ) * (b / c) := by
  rw [Real.rpow_sub hc, Real.rpow_one, Real.rpow_neg hc.le]
  field_simp

/-- Cochrane (2023), p. 200: the discounted value of debt held in the steady ratio
`b_T = κ c_T`, `e^{−δT} u'(c_T) b_T = κ c₀^{1−γ} e^{(−δ + (1−γ) g) T}`. -/
theorem tvc_term_eq {c₀ : ℝ} (hc : 0 < c₀) (δ γ g κ T : ℝ) :
    marginalUtility δ γ c₀ g T * (κ * consumption c₀ g T) =
      κ * c₀ ^ (1 - γ) * Real.exp ((-δ + (1 - γ) * g) * T) := by
  unfold marginalUtility
  have h := consumption_rpow hc g T (-γ)
  have h1 : consumption c₀ g T = c₀ * Real.exp (g * T) := rfl
  rw [h, h1, Real.rpow_sub hc, Real.rpow_one, Real.rpow_neg hc.le]
  have hexp : Real.exp ((-δ + (1 - γ) * g) * T) =
      Real.exp (-δ * T) * Real.exp (-γ * g * T) * Real.exp (g * T) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hc' : (c₀ ^ γ) ≠ 0 := (Real.rpow_pos_of_pos hc γ).ne'
  field_simp

/-- Cochrane (2023), p. 200: the transversality condition for debt in a steady positive
ratio `κ` to consumption, `lim_{T→∞} e^{−δT} u'(c_T) b_T = 0`, holds iff `r > g`. -/
theorem tvc_iff {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g : ℝ) :
    Tendsto (fun T => marginalUtility δ γ c₀ g T * (κ * consumption c₀ g T)) atTop (𝓝 0) ↔
      g < rate δ γ g := by
  have hK : 0 < κ * c₀ ^ (1 - γ) := mul_pos hκ (Real.rpow_pos_of_pos hc _)
  simp_rw [tvc_term_eq hc]
  rw [tendsto_const_mul_exp_zero_iff hK, rate_gt_growth_iff]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 200: with `δ = 0` and growth `g > 0`, a steady debt/consumption
ratio satisfies the transversality condition iff `γ > 1`. -/
theorem tvc_delta_zero_iff {c₀ κ γ g : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (hg : 0 < g) :
    Tendsto (fun T => marginalUtility 0 γ c₀ g T * (κ * consumption c₀ g T)) atTop (𝓝 0) ↔
      1 < γ := by
  rw [tvc_iff hc hκ, rate_gt_growth_iff]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Cochrane (2023), p. 200 ("for `γ < 1`, the right-hand side continues to grow"): with
`δ = 0`, `g > 0` and `γ < 1`, `u'(c_T) b_T → ∞` for a steady debt/consumption ratio. -/
theorem tvc_diverges_of_lt_one {c₀ κ γ g : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (hg : 0 < g)
    (hγ : γ < 1) :
    Tendsto (fun T => marginalUtility 0 γ c₀ g T * (κ * consumption c₀ g T)) atTop atTop := by
  have hK : 0 < κ * c₀ ^ (1 - γ) := mul_pos hκ (Real.rpow_pos_of_pos hc _)
  simp_rw [tvc_term_eq hc]
  exact tendsto_const_mul_exp_atTop hK (by nlinarith)

/-- Cochrane (2023), p. 200: with population growing at rate `n` and aggregate consumption at
`g`, per-capita consumption grows at `g − n` and the consumer's rate is
`r = δ + γ (g − n)`, as the exact rate of decline of marginal utility. -/
theorem rate_population {c₀ : ℝ} (hc : 0 < c₀) (δ γ g n t : ℝ) :
    HasDerivAt (fun s => Real.log (marginalUtility δ γ c₀ (g - n) s))
      (-(δ + γ * (g - n))) t :=
  hasDerivAt_log_marginalUtility hc δ γ (g - n) t

/-- Cochrane (2023), p. 200: with population growth the transversality condition for
per-capita debt in a steady ratio to per-capita consumption holds iff `r > g − n`, where
`r = δ + γ (g − n)`. -/
theorem tvc_population_iff {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g n : ℝ) :
    Tendsto (fun T => marginalUtility δ γ c₀ (g - n) T * (κ * consumption c₀ (g - n) T))
      atTop (𝓝 0) ↔ g - n < rate δ γ (g - n) :=
  tvc_iff hc hκ δ γ (g - n)

/-- Cochrane (2023), p. 200: with standard preferences (`δ > 0`, `γ = 1`), population growth
can deliver `r < g` for aggregate growth while the per-capita transversality condition holds:
`δ = 1%`, `g = 3%`, `n = 2%` give `r = 2% ∈ (g − n, g)`. -/
theorem population_allows_r_lt_g :
    rate (1 / 100) 1 (3 / 100 - 2 / 100) < 3 / 100 ∧
      3 / 100 - 2 / 100 < rate (1 / 100) 1 (3 / 100 - 2 / 100) := by
  unfold rate; norm_num

/-- Cochrane (2023), p. 200 ("population growth must eventually end"): with `n = 0` the
population formula reduces to (6.6). -/
theorem rate_population_zero (δ γ g : ℝ) : rate δ γ (g - 0) = rate δ γ g := by
  rw [sub_zero]

end Cochrane.FiscalConstraints.GrowthTheoryTVC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Liquidity, seigniorage and `r < g`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.5, pp. 200–203,
equations (6.7)–(6.13).

A government financed by non-interest-bearing money `M` with money demand `M V(i) = P y`
earns a return `−π` on its liabilities, below growth `g`, yet the value of money is a
well-defined present value when discounted at the real rate `r^f > g`. Money and nominal
debt `B` evolve by `d(M + B)/dt = i B − P s` (money-only: (6.7) `dM/dt = −P s`), the price level
by `dP/dt = π P` and output by `dy/dt = g y`.

## Main results

* `money_growth`: constant velocity gives `(1/M) dM/dt = π + g` (p. 201).
* `steady_state_deficit` (6.8) and `middle_term` (p. 202): `s/y + i M/(Py) = (r^f − g) M/(Py)`.
* `hasDerivAt_moneyRatio` (6.10) and `hasDerivAt_moneyRatio_rf` (6.11) as exact derivatives;
  `hasDerivAt_liabilityRatio` for money plus interest-bearing debt.
* The variation-of-constants identity behind (6.12) and (6.13) and the forward present value
  are the general `LinearODE.finite_horizon_identity` and `LinearODE.forward_present_value`.
* `eq_6_12`, `eq_6_13`: both finite-horizon representations hold on the same path.
* `eq_6_9`: with `r^f > g`, bounded flows and the transversality condition, the value of
  money and debt is the improper present-value integral (6.9) of surpluses plus seigniorage.
* `steady_6_12_explodes`: in the steady state the two terms of (6.12) diverge to `−∞` and `+∞`.
* `steady_6_13_converges`: both terms of (6.13) converge.
* `tvc_mrs_iff`, `return_discounted_terminal_explodes`: the transversality condition holds
  with the marginal rate of substitution, but the terminal term discounted at the ex-post
  return on money explodes (p. 203).
-/

namespace Cochrane.FiscalConstraints.MoneyLiquidity

open Filter Topology MeasureTheory
open Cochrane.FiscalConstraints.LinearODE (finite_horizon_identity forward_present_value)
open Cochrane.FiscalConstraints.ExpIntegrals (tvc_of_bounded)

/-- Cochrane (2023), p. 201: with constant velocity, `M V = P y`, `dP/dt = π P` and
`dy/dt = g y`, money grows at `π + g`: `dM/dt = (π + g) M`. -/
theorem money_growth {M P y : ℝ → ℝ} {V infl g t : ℝ} (hV : 0 < V)
    (hMV : ∀ τ, M τ * V = P τ * y τ) (hP : HasDerivAt P (infl * P t) t)
    (hy : HasDerivAt y (g * y t) t) : HasDerivAt M ((infl + g) * M t) t := by
  have hM : M = fun τ => P τ * y τ / V := by
    funext τ; rw [← hMV τ, mul_div_cancel_right₀ _ hV.ne']
  have h := (hP.mul hy).div_const V
  rw [hM]
  convert h using 1
  field_simp

/-- Cochrane (2023), (6.8) p. 201: if money finances deficits, `dM/dt = −P s` (6.7), and
money grows at `π + g`, then `(π + g) M/(P y) = −s/y`. -/
theorem steady_state_deficit {M P y s infl g : ℝ} (hP : P ≠ 0) (hy : y ≠ 0)
    (h67 : (infl + g) * M = -(P * s)) : (infl + g) * (M / (P * y)) = -(s / y) := by
  field_simp
  linear_combination h67

/-- Cochrane (2023), p. 202: with the steady-state deficit (6.8) and `i = r^f + π`, the middle
term of (6.9) is `s/y + i M/(Py) = (r^f − g) M/(Py)`. -/
theorem middle_term {m σ infl g rf i : ℝ} (hi : i = rf + infl)
    (h68 : (infl + g) * m = -σ) : σ + i * m = (rf - g) * m := by
  subst hi; linarith

/-- Cochrane (2023), p. 202 ("the seigniorage term is larger than the deficit term"): with
`r^f > g` and positive real money, seigniorage `i M/(Py)` exceeds the deficit `−s/y`. -/
theorem seigniorage_exceeds_deficit {m σ infl g rf i : ℝ} (hi : i = rf + infl)
    (h68 : (infl + g) * m = -σ) (hrg : g < rf) (hm : 0 < m) : -σ < i * m := by
  have := middle_term hi h68
  nlinarith

/-- Cochrane (2023), p. 201 ("the rate of return on government debt is `r = −π`, so
`r < g`"): in the steady state (6.8) with a deficit `s < 0` and positive real money, the
return on money `−π` is below growth `g`. -/
theorem money_return_lt_growth {m σ infl g : ℝ} (h68 : (infl + g) * m = -σ) (hσ : σ < 0)
    (hm : 0 < m) : -infl < g := by
  by_contra h
  push Not at h
  nlinarith

/-- Cochrane (2023), (6.10) p. 202 and footnote 1, as an exact derivative: with (6.7)
`dM/dt = −P s`, `dP/dt = π P` and `dy/dt = g y`, the money/GDP ratio `m = M/(P y)` satisfies
`dm/dt + m (π + g) = −s/y`. -/
theorem hasDerivAt_moneyRatio {M P y s infl g : ℝ → ℝ} {t : ℝ}
    (hM : HasDerivAt M (-(P t * s t)) t) (hP : HasDerivAt P (infl t * P t) t)
    (hy : HasDerivAt y (g t * y t) t) (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => M τ / (P τ * y τ))
      (-(s t / y t) - M t / (P t * y t) * (infl t + g t)) t := by
  have h := hM.div (hP.mul hy) (mul_ne_zero hP0 hy0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), (6.11) p. 202: with `i = r^f + π` the same law of motion reads
`dm/dt + m (i − r^f + g) = −s/y`. -/
theorem hasDerivAt_moneyRatio_rf {M P y s infl g i : ℝ → ℝ} {rf t : ℝ}
    (hi : i t = rf + infl t)
    (hM : HasDerivAt M (-(P t * s t)) t) (hP : HasDerivAt P (infl t * P t) t)
    (hy : HasDerivAt y (g t * y t) t) (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => M τ / (P τ * y τ))
      (-(s t / y t) - M t / (P t * y t) * (i t - rf + g t)) t := by
  have h := hasDerivAt_moneyRatio hM hP hy hP0 hy0
  rw [hi]
  convert h using 2
  ring

/-- Cochrane (2023), (6.9) p. 201, flow form with money and interest-bearing debt: if
`d(M + B)/dt = i B − P s`, the ratio `w = (M + B)/(P y)` satisfies
`dw/dt = (i − π − g) w − i M/(P y) − s/y`. -/
theorem hasDerivAt_liabilityRatio {M B P y s infl g i : ℝ → ℝ} {t : ℝ}
    (hW : HasDerivAt (fun τ => M τ + B τ) (i t * B t - P t * s t) t)
    (hP : HasDerivAt P (infl t * P t) t) (hy : HasDerivAt y (g t * y t) t)
    (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => (M τ + B τ) / (P τ * y τ))
      ((i t - infl t - g t) * ((M t + B t) / (P t * y t)) - i t * (M t / (P t * y t))
        - s t / y t) t := by
  have h := hW.div (hP.mul hy) (mul_ne_zero hP0 hy0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), (6.12) p. 202: integrating (6.10) forward at the money return,
`M_t/(P_t y_t) = ∫_t^T e^{(π+g)(τ−t)} s_τ/y_τ dτ + e^{(π+g)(T−t)} M_T/(P_T y_T)`, for constant
inflation `π` and growth `g`. -/
theorem eq_6_12 {M P y s : ℝ → ℝ} {infl g : ℝ}
    (hM : ∀ τ, HasDerivAt M (-(P τ * s τ)) τ) (hP : ∀ τ, HasDerivAt P (infl * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hs : Continuous s) (t T : ℝ) :
    M t / (P t * y t) = (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * (s τ / y τ)) +
      Real.exp ((infl + g) * (T - t)) * (M T / (P T * y T)) := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun τ => (hy τ).continuousAt
  have hf : Continuous fun τ => s τ / y τ := hs.div hyc hy0
  have hw : ∀ τ, HasDerivAt (fun x => M x / (P x * y x))
      (-(infl + g) * (M τ / (P τ * y τ)) - s τ / y τ) τ := fun τ => by
    have h := hasDerivAt_moneyRatio (g := fun _ => g) (infl := fun _ => infl) (hM τ) (hP τ)
      (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    ring
  have h := finite_horizon_identity hw hf t T
  simpa only [neg_neg] using h

/-- Cochrane (2023), (6.13) p. 203: integrating (6.11) forward at the real rate `r^f`, the
money/GDP ratio is the discounted value of surpluses plus seigniorage over `[t, T]` plus a
terminal term: `m_t = ∫_t^T e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ m_τ) dτ + e^{−(r^f−g)(T−t)} m_T`,
with `i_τ = r^f + π_τ`. -/
theorem eq_6_13 {M P y s infl : ℝ → ℝ} {g rf : ℝ}
    (hM : ∀ τ, HasDerivAt M (-(P τ * s τ)) τ) (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hs : Continuous s) (hinfl : Continuous infl) (t T : ℝ) :
    M t / (P t * y t) = (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) *
        (s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)))) +
      Real.exp (-(rf - g) * (T - t)) * (M T / (P T * y T)) := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun τ => (hy τ).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun τ => (hP τ).continuousAt
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun τ => (hM τ).continuousAt
  have hf : Continuous fun τ => s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)) :=
    (hs.div hyc hy0).add ((continuous_const.add hinfl).mul
      (hMc.div (hPc.mul hyc) fun τ => mul_ne_zero (hP0 τ) (hy0 τ)))
  have hw : ∀ τ, HasDerivAt (fun x => M x / (P x * y x))
      ((rf - g) * (M τ / (P τ * y τ)) -
        (s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)))) τ := fun τ => by
    have h := hasDerivAt_moneyRatio (g := fun _ => g) (hM τ) (hP τ) (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    ring
  exact finite_horizon_identity hw hf t T

/-- Cochrane (2023), (6.9) p. 201: the value of money and nominal debt as a fraction of GDP
is the present value, discounted at `r^f − g > 0`, of surpluses plus the interest saving on
money, `(M_t + B_t)/(P_t y_t) = ∫_t^∞ e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ M_τ/(P_τ y_τ)) dτ`,
given `i = r^f + π`, bounded continuous flows and the transversality condition. -/
theorem eq_6_9 {M B P y s infl i : ℝ → ℝ} {g rf K : ℝ} (hrg : g < rf)
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hK : ∀ τ, |s τ / y τ + i τ * (M τ / (P τ * y τ))| ≤ K) (t : ℝ)
    (htvc : Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T)))
      atTop (𝓝 0)) :
    (M t + B t) / (P t * y t) = ∫ τ in Set.Ioi t, Real.exp (-(rf - g) * (τ - t)) *
      (s τ / y τ + i τ * (M τ / (P τ * y τ))) := by
  have hw : ∀ τ, HasDerivAt (fun x => (M x + B x) / (P x * y x))
      ((rf - g) * ((M τ + B τ) / (P τ * y τ)) -
        (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ := fun τ => by
    have h := hasDerivAt_liabilityRatio (g := fun _ => g) (hW τ) (hP τ) (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    rw [hi τ]
    ring
  exact (forward_present_value (by linarith) hw hf hK t htvc).2

/-- Cochrane (2023), (6.9) p. 201: the value of debt is unique: two liability paths solving the
same flow equation and both satisfying the transversality condition coincide. -/
theorem present_value_unique {a K : ℝ} (ha : 0 < a) {w₁ w₂ f : ℝ → ℝ}
    (h₁ : ∀ τ, HasDerivAt w₁ (a * w₁ τ - f τ) τ) (h₂ : ∀ τ, HasDerivAt w₂ (a * w₂ τ - f τ) τ)
    (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K) (t : ℝ)
    (htvc₁ : Tendsto (fun T => Real.exp (-a * (T - t)) * w₁ T) atTop (𝓝 0))
    (htvc₂ : Tendsto (fun T => Real.exp (-a * (T - t)) * w₂ T) atTop (𝓝 0)) :
    w₁ t = w₂ t := by
  rw [(forward_present_value ha h₁ hf hK t htvc₁).2, (forward_present_value ha h₂ hf hK t htvc₂).2]

/-- Cochrane (2023), (6.12) p. 202 ("the terminal condition explodes ... the present value
integral also explodes negatively"): in a steady state with constant positive real money
`m̄`, constant deficit ratio `σ̄` and `π + g > 0`, satisfying (6.8), the present-value term of
(6.12) tends to `−∞` and the terminal term to `+∞`, while their sum is `m̄`. -/
theorem steady_6_12_explodes {m σ infl g : ℝ} (hm : 0 < m) (hk : 0 < infl + g)
    (h68 : (infl + g) * m = -σ) (t : ℝ) :
    (∀ T, (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) +
        Real.exp ((infl + g) * (T - t)) * m = m) ∧
      Tendsto (fun T => ∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) atTop atBot ∧
      Tendsto (fun T => Real.exp ((infl + g) * (T - t)) * m) atTop atTop := by
  have hw : ∀ τ, HasDerivAt (fun _ : ℝ => m) (-(infl + g) * m - σ) τ := fun τ => by
    convert hasDerivAt_const τ m using 1
    linarith
  have hid : ∀ T, (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) +
      Real.exp ((infl + g) * (T - t)) * m = m := fun T => by
    have h := finite_horizon_identity hw (continuous_const (y := σ)) t T
    simp only [neg_neg] at h
    exact h.symm
  have hterm : Tendsto (fun T => Real.exp ((infl + g) * (T - t)) * m) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => (infl + g) * (T - t)) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop hk
    exact (Real.tendsto_exp_atTop.comp h1).atTop_mul_const hm
  refine ⟨hid, ?_, hterm⟩
  have heq : (fun T => ∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) =
      fun T => m - Real.exp ((infl + g) * (T - t)) * m := by
    funext T; linarith [hid T]
  rw [heq]
  exact tendsto_atBot_add_const_left _ m (tendsto_neg_atTop_atBot.comp hterm)

/-- Cochrane (2023), (6.13) p. 203 ("both the present value and the terminal condition
converge"): in the steady state of (6.8) with `i = r^f + π` and `r^f > g`, the present-value
term of (6.13) tends to `m̄` and the terminal term to `0`. -/
theorem steady_6_13_converges {m σ infl g rf i : ℝ} (hi : i = rf + infl) (hrg : g < rf)
    (h68 : (infl + g) * m = -σ) (t : ℝ) :
    (∀ T, (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) +
        Real.exp (-(rf - g) * (T - t)) * m = m) ∧
      Tendsto (fun T => ∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) atTop
        (𝓝 m) ∧
      Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * m) atTop (𝓝 0) := by
  have hmid := middle_term hi h68
  have hw : ∀ τ, HasDerivAt (fun _ : ℝ => m) ((rf - g) * m - (σ + i * m)) τ := fun τ => by
    convert hasDerivAt_const τ m using 1
    linarith
  have hid : ∀ T, (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) +
      Real.exp (-(rf - g) * (T - t)) * m = m := fun T =>
    (finite_horizon_identity hw continuous_const t T).symm
  have hterm : Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * m) atTop (𝓝 0) :=
    tvc_of_bounded (C := |m|) (by linarith) (fun _ => le_rfl) t
  refine ⟨hid, ?_, hterm⟩
  have heq : (fun T => ∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) =
      fun T => m - Real.exp (-(rf - g) * (T - t)) * m := by
    funext T; linarith [hid T]
  rw [heq]
  simpa using (tendsto_const_nhds (x := m)).sub hterm

/-- Cochrane (2023), p. 203: the transversality condition with marginal-utility discounting.
With `M_T/P_T = m̄ y_T`, `y_T = y_t e^{g(T−t)}` and the marginal rate of substitution
`e^{−r^f(T−t)}`, `lim e^{−r^f(T−t)} M_T/P_T = 0` iff `r^f > g` (for `m̄ y_t > 0`). -/
theorem tvc_mrs_iff {m yt rf g t : ℝ} (hm : 0 < m * yt) :
    Tendsto (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
      atTop (𝓝 0) ↔ g < rf := by
  have heq : (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t))))) =
      (fun s => m * yt * Real.exp ((g - rf) * s)) ∘ (fun T => T - t) := by
    funext T
    simp only [Function.comp]
    rw [mul_comm (Real.exp _), mul_assoc m, mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  have hshift : Tendsto (fun T : ℝ => T - t) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  rw [heq]
  constructor
  · intro h
    have h2 : Tendsto (fun s => m * yt * Real.exp ((g - rf) * s)) atTop (𝓝 0) := by
      have := h.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
      refine this.congr fun s => ?_
      simp
    rw [ExpIntegrals.tendsto_const_mul_exp_zero_iff hm] at h2
    linarith
  · intro h
    exact ((ExpIntegrals.tendsto_const_mul_exp_zero_iff hm).mpr (by linarith)).comp hshift

/-- Cochrane (2023), p. 203 ("we discount using the consumer's marginal rate of
substitution"): power utility over `c = y = y₀ e^{g τ}` with discount rate `ρ` gives
`e^{−ρ(τ−t)} u'(c_τ)/u'(c_t) = e^{−r^f(τ−t)}` with `r^f = ρ + γ g`. -/
theorem mrs_eq_riskfree {y₀ : ℝ} (hy : 0 < y₀) (ρ γ g t τ : ℝ) :
    GrowthTheoryTVC.marginalUtility ρ γ y₀ g τ / GrowthTheoryTVC.marginalUtility ρ γ y₀ g t =
      Real.exp (-(ρ + γ * g) * (τ - t)) :=
  GrowthTheoryTVC.marginalUtility_ratio hy ρ γ g t τ

/-- Cochrane (2023), p. 203 ("even when the transversality condition holds, the terminal
condition does not necessarily hold discounting with the ex-post return"): with `r^f > g` and
`π + g > 0` (money's return `−π` below growth), the marginal-utility-discounted terminal value
of real money tends to `0` while the terminal value discounted at the return on money,
`e^{π(T−t)} M_T/P_T`, tends to `+∞`. -/
theorem return_discounted_terminal_explodes {m yt rf g infl t : ℝ} (hm : 0 < m * yt)
    (hrg : g < rf) (hk : 0 < infl + g) :
    Tendsto (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
        atTop (𝓝 0) ∧
      Tendsto (fun T => Real.exp (infl * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
        atTop atTop := by
  refine ⟨(tvc_mrs_iff hm).mpr hrg, ?_⟩
  have heq : (fun T => Real.exp (infl * (T - t)) * (m * (yt * Real.exp (g * (T - t))))) =
      (fun s => m * yt * Real.exp ((infl + g) * s)) ∘ (fun T => T - t) := by
    funext T
    simp only [Function.comp]
    rw [mul_comm (Real.exp _), mul_assoc m, mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  rw [heq]
  exact (ExpIntegrals.tendsto_const_mul_exp_atTop hm hk).comp
    (tendsto_atTop_add_const_right _ _ tendsto_id)

end Cochrane.FiscalConstraints.MoneyLiquidity

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discount rates versus rates of return

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.6, pp. 204–205,
equation (6.14).

One can always discount a one-period payoff by the ex-post return, `1 = E_t[R_{t+1}⁻¹ R_{t+1}]`,
and iterating gives the finite-horizon return-discounted value identity (6.14). Whether the
infinite-horizon version holds is a separate question: the sum and the terminal term need not
converge, even when the stochastic-discount-factor (SDF) present value does.

## Main results

* `one_eq_E_inv_mul`: `1 = E_t[R⁻¹ R]` for a nowhere-zero return.
* `eq_6_14_pathwise`: (6.14) holds state by state, `p_t = Σ_{j=1}^T (Π_{k≤j} R_{t+k}⁻¹) d_{t+j}
  + (Π_{k≤T} R_{t+k}⁻¹) p_{t+T}`, for any price and dividend paths with nonzero values.
* `eq_6_14`: hence its conditional-expectation form for an adapted price.
* `sdf_finite_horizon`, `sdf_finite_horizon_div`: the SDF version (p. 204, display above
  (6.14)) from one-period pricing, by the law of iterated expectations.
* `return_pv_iff_terminal`: if the return-discounted sum converges, the price equals it iff
  the return-discounted terminal term tends to zero (p. 204, "if the sum and terminal value
  converge").
* `linear_discount_factor_prices`: the linear discount factor `R_{t+1}/E_t(R_{t+1}²)` prices
  the return (p. 204).
-/

namespace Cochrane.FiscalConstraints.ReturnDiscounting

open Filter Topology

variable {Ω : Type*}

/-- Cochrane (2023), p. 204: the gross return from `s` to `s + 1`,
`R_{s+1} = (p_{s+1} + d_{s+1})/p_s`. -/
noncomputable def grossReturn (p d : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  (p (s + 1) ω + d (s + 1) ω) / p s ω

/-- Cochrane (2023), (6.14) p. 204: the return discount factor `Π_{k=1}^j R_{t+k}⁻¹`. -/
noncomputable def returnDiscount (p d : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range j, (grossReturn p d (t + k) ω)⁻¹

/-- Cochrane (2023), (6.14) p. 204: the return-discounted value of dividends over
`t + 1, …, t + T`. -/
noncomputable def returnPV (p d : ℕ → Ω → ℝ) (t T : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range T, returnDiscount p d t (j + 1) ω * d (t + j + 1) ω

/-- Cochrane (2023), p. 204: `1 = E_t[R_{t+1}⁻¹ R_{t+1}]` for a return that is nowhere zero. -/
theorem one_eq_E_inv_mul (𝔼 : ExpectationSystem Ω) (t : ℕ) {R : Ω → ℝ}
    (hR : ∀ ω, R ω ≠ 0) : 𝔼.E t (fun ω => (R ω)⁻¹ * R ω) = fun _ => 1 := by
  have h : (fun ω => (R ω)⁻¹ * R ω) = fun _ => (1 : ℝ) := by
    funext ω; exact inv_mul_cancel₀ (hR ω)
  rw [h, 𝔼.const]

/-- Cochrane (2023), (6.14) p. 204: one more period of return discounting,
`(Π_{k≤j+1} R⁻¹)(p_{t+j+1} + d_{t+j+1}) = (Π_{k≤j} R⁻¹) p_{t+j}`. -/
theorem returnDiscount_succ_mul {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t j : ℕ) (ω : Ω) :
    returnDiscount p d t (j + 1) ω * (p (t + j + 1) ω + d (t + j + 1) ω) =
      returnDiscount p d t j ω * p (t + j) ω := by
  unfold returnDiscount
  rw [Finset.prod_range_succ, grossReturn, inv_div, mul_assoc,
    div_mul_cancel₀ _ (hpd (t + j) ω)]

/-- Cochrane (2023), (6.14) p. 204, state by state: for price and dividend paths with
`p_{s+1} + d_{s+1} ≠ 0`,
`p_t = Σ_{j=1}^T (Π_{k=1}^j R_{t+k}⁻¹) d_{t+j} + (Π_{k=1}^T R_{t+k}⁻¹) p_{t+T}`. -/
theorem eq_6_14_pathwise {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t : ℕ) (ω : Ω) :
    ∀ T, p t ω = returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω := by
  intro T
  induction T with
  | zero => simp [returnPV, returnDiscount]
  | succ T ih =>
    rw [ih, returnPV, returnPV, Finset.sum_range_succ, ← returnDiscount_succ_mul hpd t T ω,
      ← add_assoc t T 1]
    ring

/-- Cochrane (2023), (6.14) p. 204: for an adapted price process the identity holds under
`E_t`: `p_t = E_t[Σ_{j=1}^T (Π R⁻¹) d_{t+j} + (Π R⁻¹) p_{t+T}]`. -/
theorem eq_6_14 (𝔼 : ExpectationSystem Ω) {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (hpa : 𝔼.Adapted p) (t T : ℕ) :
    p t = 𝔼.E t (fun ω => returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω) := by
  have h : (fun ω => returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω) = p t := by
    funext ω; exact (eq_6_14_pathwise hpd t ω T).symm
  rw [h, hpa t]

/-- Cochrane (2023), p. 204 (the SDF present value above (6.14)): if one-period pricing
`Λ_t p_t = E_t[Λ_{t+1}(p_{t+1} + d_{t+1})]` holds at every date, then for every horizon
`Λ_t p_t = E_t[Σ_{j=1}^T Λ_{t+j} d_{t+j} + Λ_{t+T} p_{t+T}]`. -/
theorem sdf_finite_horizon (𝔼 : ExpectationSystem Ω) {p d Λ : ℕ → Ω → ℝ}
    (hpr : ∀ s, Λ s * p s = 𝔼.E s (Λ (s + 1) * (p (s + 1) + d (s + 1)))) (t : ℕ) :
    ∀ T, Λ t * p t = 𝔼.E t (∑ j ∈ Finset.range T, Λ (t + j + 1) * d (t + j + 1) +
      Λ (t + T) * p (t + T)) := by
  intro T
  induction T with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, add_zero]
    rw [hpr t, 𝔼.E_E_self]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, map_add, map_add, map_add, hpr (t + T),
      𝔼.tower (Nat.le_add_right t T), ← add_assoc t T 1, mul_add, map_add]
    ring

/-- Cochrane (2023), p. 204: dividing by `Λ_t` (positive and known at `t`, with the pull-out
property), `p_t = E_t[Σ_{j=1}^T (Λ_{t+j}/Λ_t) d_{t+j} + (Λ_{t+T}/Λ_t) p_{t+T}]`. -/
theorem sdf_finite_horizon_div (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {p d Λ : ℕ → Ω → ℝ} (hΛ : ∀ s ω, Λ s ω ≠ 0)
    (hinv : ∀ s, 𝔼.E s (fun ω => (Λ s ω)⁻¹) = fun ω => (Λ s ω)⁻¹)
    (hpr : ∀ s, Λ s * p s = 𝔼.E s (Λ (s + 1) * (p (s + 1) + d (s + 1)))) (t T : ℕ) :
    p t = 𝔼.E t (fun ω => ∑ j ∈ Finset.range T, Λ (t + j + 1) ω / Λ t ω * d (t + j + 1) ω +
      Λ (t + T) ω / Λ t ω * p (t + T) ω) := by
  have h := congrArg (fun x => (fun ω => (Λ t ω)⁻¹) * x) (sdf_finite_horizon 𝔼 hpr t T)
  rw [← hpo t _ _ (hinv t)] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply] at hω
  rw [← mul_assoc, inv_mul_cancel₀ (hΛ t ω), one_mul] at hω
  rw [hω]
  refine congrFun (congrArg (𝔼.E t) ?_) ω
  funext ω'
  simp only [Pi.mul_apply, Pi.add_apply, Finset.sum_apply, div_eq_mul_inv]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · ring

/-- Cochrane (2023), p. 204 ("the present value discounted at the ex-post return is correct,
if the sum and terminal value converge"): if the return-discounted dividends are summable with
sum `S`, then the return-discounted terminal value converges to `p_t − S`, and `p_t = S` iff
that terminal value tends to zero. -/
theorem return_pv_iff_terminal {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t : ℕ) (ω : Ω) {S : ℝ}
    (hS : HasSum (fun j => returnDiscount p d t (j + 1) ω * d (t + j + 1) ω) S) :
    Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop (𝓝 (p t ω - S)) ∧
      (p t ω = S ↔
        Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop (𝓝 0)) := by
  have hpart : Tendsto (fun T => returnPV p d t T ω) atTop (𝓝 S) := hS.tendsto_sum_nat
  have heq : (fun T => returnDiscount p d t T ω * p (t + T) ω) =
      fun T => p t ω - returnPV p d t T ω := by
    funext T; linarith [eq_6_14_pathwise hpd t ω T]
  have hlim : Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop
      (𝓝 (p t ω - S)) := by
    rw [heq]; exact tendsto_const_nhds.sub hpart
  refine ⟨hlim, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [h, sub_self] at hlim; exact hlim
  · have := tendsto_nhds_unique hlim h
    linarith

/-- Cochrane (2023), p. 204: the linear one-period discount factor
`Λ_{t+1}/Λ_t = R_{t+1}/E_t(R_{t+1}²)` prices the return, `E_t[(R/E_t R²) R] = 1`, when
`E_t R²` is nowhere zero and its reciprocal is known at `t`. -/
theorem linear_discount_factor_prices (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) (t : ℕ)
    (R : Ω → ℝ) (hv : ∀ ω, 𝔼.E t (R * R) ω ≠ 0)
    (hinv : 𝔼.E t (fun ω => (𝔼.E t (R * R) ω)⁻¹) = fun ω => (𝔼.E t (R * R) ω)⁻¹) :
    𝔼.E t (fun ω => (𝔼.E t (R * R) ω)⁻¹ * R ω * R ω) = fun _ => 1 := by
  have h : (fun ω => (𝔼.E t (R * R) ω)⁻¹ * R ω * R ω) =
      (fun ω => (𝔼.E t (R * R) ω)⁻¹) * (R * R) := by
    funext ω; simp only [Pi.mul_apply]; ring
  rw [h, hpo t _ _ hinv]
  funext ω
  simp only [Pi.mul_apply]
  exact inv_mul_cancel₀ (hv ω)

end Cochrane.FiscalConstraints.ReturnDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregate uncertainty, `r < g` and present values

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207,
equations (6.15)–(6.18).

Consumption `c_t = y_t > 0` grows by i.i.d. factors `G_{t+1} = c_{t+1}/c_t`; the
representative consumer has power utility, so the SDF is `β^j (c_{t+j}/c_t)^{−γ}`. In an
`ExpectationSystem` with the pull-out property, "i.i.d. growth" is the hypothesis
`E_t[G_{t+1}^a] = mom a` (a constant) for every real `a` (`IIDGrowth`), and "`c_t^a` is known at
`t`" is `KnownPowers`.

## Main results

* `E_ratio_pow_mul`: `E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` known at `t`.
* `correct_term` (6.15): the correct summands are `(β mom(1−γ))^j κ`;
  `incorrect_term` (6.16): the summands with the expectation inside are
  `(β mom(−γ) mom 1)^j κ = ((1+g)/(1+r))^j κ`.
* `correct_finite_incorrect_explodes`: the correct present value converges while the
  incorrect one diverges whenever `β mom(1−γ) < 1 ≤ β mom(−γ) mom 1`.
* Lognormal growth: `lognormalMoment_eq_integral` (Gaussian moment generating function),
  `lognormal_correct`, `lognormal_incorrect` (corrected exponent `(γ²+1)σ²/2`),
  `printed_incorrect_wrong`, `region_nonempty_iff` (non-empty iff `γ > 0`),
  `printed_region_iff` (`γ > 1/2` with the printed exponent), `log_riskFree_lognormal`,
  `printed_bohn_rate_wrong`, `riskFree_lt_growth_iff`, `bohn_region`.
* (6.17): `eq_6_17` for any debt rolled over at the risk-free rate, `terminal_c`, `pv_term_c`,
  `bohn_pv_hasSum_iff` (infinite horizon iff `β E[G^{1−γ}] < 1`), `terminal_tendsto_iff`.
* (6.18): `eq_6_18_pathwise`, `eq_6_18`, `eq_6_18_diverges`.
* The two-state witness: `bohnTree` (an i.i.d. coin tree of any horizon), `bohnSystem_iid`,
  `bohn_numbers` (`r_f ≈ 0.83% < E g = 5%`, `β E[G^{−1}] ≈ 0.968 < 1`), `bohn_witness_6_17`,
  `bohn_witness_6_18`.
-/

namespace Cochrane.FiscalConstraints.AggregateUncertainty

open Filter Topology

variable {Ω : Type*}

/-- Cochrane (2023), p. 205: every power `c_t^a` of consumption is known at date `t`. -/
def KnownPowers (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ℝ) : Prop :=
  ∀ t (a : ℝ), 𝔼.E t (fun ω => c t ω ^ a) = fun ω => c t ω ^ a

/-- Cochrane (2023), p. 205: consumption growth `G_{t+1} = c_{t+1}/c_t`. -/
noncomputable def growth (c : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := c (t + 1) ω / c t ω

/-- Cochrane (2023), p. 205 ("consumption and GDP growth are independent over time"): for
dates `t < H`, `E_t[G_{t+1}^a] = mom a`, the same constant at every date and state. -/
def IIDGrowth (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ℝ) (mom : ℝ → ℝ) (H : ℕ) : Prop :=
  ∀ t, t < H → ∀ a : ℝ, 𝔼.E t (fun ω => growth c t ω ^ a) = fun _ => mom a

/-- Cochrane (2023), (6.15) p. 205: the consumption ratio `c_{t+j}/c_t`. -/
noncomputable def ratio (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ := c (t + j) ω / c t ω

/-- Cochrane (2023), (6.17) p. 207: the stochastic discount factor
`β^j (c_{t+j}/c_t)^{−γ}`. -/
noncomputable def pvDisc (β γ : ℝ) (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * ratio c t j ω ^ (-γ)

/-- Cochrane (2023), p. 206: the gross risk-free rate `1 + r = 1/(β E[G^{−γ}])`. -/
noncomputable def riskFreeGross (β γ : ℝ) (mom : ℝ → ℝ) : ℝ := (β * mom (-γ))⁻¹

/-- Cochrane (2023), p. 205: with the pull-out property, products of known variables are
known. -/
theorem known_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : 𝔼.E t x = x) (hy : 𝔼.E t y = y) :
    𝔼.E t (fun ω => x ω * y ω) = fun ω => x ω * y ω := by
  have h := hpo t x y hx
  rw [hy] at h
  exact h

/-- Cochrane (2023), (6.15) p. 205: `c_t/c_t = 1`. -/
theorem ratio_zero {c : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (h : c t ω ≠ 0) : ratio c t 0 ω = 1 := by
  simp [ratio, h]

/-- Cochrane (2023), (6.15) p. 205: `c_{t+j+1}/c_t = (c_{t+j}/c_t) G_{t+j+1}`. -/
theorem ratio_succ {c : ℕ → Ω → ℝ} {t j : ℕ} {ω : Ω} (h0 : c t ω ≠ 0) (h1 : c (t + j) ω ≠ 0) :
    ratio c t (j + 1) ω = ratio c t j ω * growth c (t + j) ω := by
  unfold ratio growth
  rw [← add_assoc]
  field_simp

/-- Cochrane (2023), (6.15) p. 205: consumption ratios are positive. -/
theorem ratio_pos {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (t j : ℕ) (ω : Ω) :
    0 < ratio c t j ω := div_pos (hpos _ _) (hpos _ _)

/-- Cochrane (2023), p. 205: consumption growth is positive. -/
theorem growth_pos {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (t : ℕ) (ω : Ω) :
    0 < growth c t ω := div_pos (hpos _ _) (hpos _ _)

/-- Cochrane (2023), (6.15) p. 205: powers of `c_{t+j}/c_t` are known at `t + j`. -/
theorem ratio_rpow_known (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) (t j : ℕ) (a : ℝ) :
    𝔼.E (t + j) (fun ω => ratio c t j ω ^ a) = fun ω => ratio c t j ω ^ a := by
  have h : (fun ω => ratio c t j ω ^ a) = fun ω => c (t + j) ω ^ a * c t ω ^ (-a) := by
    funext ω
    rw [ratio, Real.div_rpow (hpos _ _).le (hpos _ _).le, Real.rpow_neg (hpos _ _).le,
      div_eq_mul_inv]
  rw [h]
  exact known_mul 𝔼 hpo (hkp (t + j) a)
    (ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t j) (hkp t (-a)))

/-- Cochrane (2023), p. 205: one period of i.i.d. growth, `E_s[Y G_{s+1}^a] = mom a · Y` for
`Y` known at `s < H`. -/
theorem E_growth_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    {mom : ℝ → ℝ} {H : ℕ} (hiid : IIDGrowth 𝔼 c mom H) {s : ℕ} (hs : s < H) {Y : Ω → ℝ}
    (hY : 𝔼.E s Y = Y) (a : ℝ) :
    𝔼.E s (fun ω => Y ω * growth c s ω ^ a) = fun ω => mom a * Y ω := by
  have h := hpo s Y (fun ω => growth c s ω ^ a) hY
  rw [hiid s hs a] at h
  change 𝔼.E s (Y * fun ω => growth c s ω ^ a) = _
  rw [h]
  funext ω
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), (6.15) p. 205 (i.i.d. growth over `j` periods):
`E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` known at `t`, when `t + j ≤ H`. -/
theorem E_ratio_pow_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {t : ℕ} {X : Ω → ℝ} (hX : 𝔼.E t X = X) (a : ℝ) :
    ∀ j, t + j ≤ H →
      𝔼.E t (fun ω => ratio c t j ω ^ a * X ω) = fun ω => mom a ^ j * X ω := by
  intro j
  induction j with
  | zero =>
    intro _
    have h : (fun ω => ratio c t 0 ω ^ a * X ω) = X := by
      funext ω; rw [ratio_zero (hpos t ω).ne', Real.one_rpow, one_mul]
    rw [h, hX]
    funext ω
    simp
  | succ j ih =>
    intro hj
    have hY : 𝔼.E (t + j) (fun ω => ratio c t j ω ^ a * X ω) =
        fun ω => ratio c t j ω ^ a * X ω :=
      known_mul 𝔼 hpo (ratio_rpow_known 𝔼 hpo hpos hkp t j a)
        (ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t j) hX)
    have hfun : (fun ω => ratio c t (j + 1) ω ^ a * X ω) =
        fun ω => (ratio c t j ω ^ a * X ω) * growth c (t + j) ω ^ a := by
      funext ω
      rw [ratio_succ (hpos t ω).ne' (hpos (t + j) ω).ne',
        Real.mul_rpow (ratio_pos hpos t j ω).le (growth_pos hpos (t + j) ω).le]
      ring
    rw [hfun, ← 𝔼.tower (Nat.le_add_right t j), E_growth_mul 𝔼 hpo hiid (by omega) hY a]
    have hs : (fun ω => mom a * (ratio c t j ω ^ a * X ω)) =
        mom a • fun ω => ratio c t j ω ^ a * X ω := rfl
    rw [hs, 𝔼.E_smul, ih (by omega)]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), p. 206: the risk-free rate prices the one-period riskless bond,
`E_s[β G_{s+1}^{−γ}] (1 + r) = 1`, for `s < H`. -/
theorem riskFree_prices (𝔼 : ExpectationSystem Ω) {c : ℕ → Ω → ℝ} {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ : ℝ} (hβm : β * mom (-γ) ≠ 0) {s : ℕ} (hs : s < H) :
    𝔼.E s (fun ω => β * growth c s ω ^ (-γ) * riskFreeGross β γ mom) = fun _ => 1 := by
  have h : (fun ω => β * growth c s ω ^ (-γ) * riskFreeGross β γ mom) =
      (β * riskFreeGross β γ mom) • fun ω => growth c s ω ^ (-γ) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h, 𝔼.E_smul, hiid s hs]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, riskFreeGross]
  field_simp
  exact div_self hβm

/-! ### (6.15) and (6.16): the correct and the incorrect present value -/

/-- Cochrane (2023), (6.15) p. 205: the summand with `c = y` and a constant surplus ratio `κ`,
`β^j (u'(c_{t+j})/u'(c_t)) (y_{t+j}/y_t) κ`. -/
noncomputable def pvTerm (β γ κ : ℝ) (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * ratio c t j ω ^ (-γ) * ratio c t j ω * κ

/-- Cochrane (2023), (6.15) p. 205: the correct summands are `E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ =
(β mom(1−γ))^j κ`. -/
theorem correct_term (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ κ : ℝ) {t j : ℕ} (hj : t + j ≤ H) :
    𝔼.E t (pvTerm β γ κ c t j) = fun _ => (β * mom (1 - γ)) ^ j * κ := by
  have h : pvTerm β γ κ c t j = (β ^ j * κ) • fun ω => ratio c t j ω ^ (1 - γ) * 1 := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos hpos t j ω),
      Real.rpow_one]
    ring
  rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) (1 - γ) j hj]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.16) p. 205: the summands with the expectation moved inside,
`E_t[β^j (c_{t+j}/c_t)^{−γ}] E_t[c_{t+j}/c_t] κ = (β mom(−γ) mom 1)^j κ`. -/
theorem incorrect_term (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ κ : ℝ) {t j : ℕ} (hj : t + j ≤ H) (ω : Ω) :
    𝔼.E t (fun ω' => β ^ j * ratio c t j ω' ^ (-γ)) ω * 𝔼.E t (ratio c t j) ω * κ =
      (β * mom (-γ) * mom 1) ^ j * κ := by
  have h1 : (fun ω' => β ^ j * ratio c t j ω' ^ (-γ)) =
      β ^ j • fun ω' => ratio c t j ω' ^ (-γ) * 1 := by
    funext ω'; simp
  have h2 : ratio c t j = fun ω' => ratio c t j ω' ^ (1 : ℝ) * 1 := by
    funext ω'; simp
  rw [h1, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) (-γ) j hj, h2,
    E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) 1 j hj]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, mul_pow]

/-- Cochrane (2023), (6.16) p. 205: with `1 + g = E[G]` and `1 + r = 1/(β E[G^{−γ}])`, the
incorrect discount factor is `((1+g)/(1+r))^j`. -/
theorem incorrect_ratio_eq {β γ : ℝ} {mom : ℝ → ℝ} (j : ℕ) :
    (β * mom (-γ) * mom 1) ^ j = (mom 1 / riskFreeGross β γ mom) ^ j := by
  rw [riskFreeGross, div_inv_eq_mul]
  ring

/-- Cochrane (2023), pp. 205–206: a geometric series `Σ_{j≥1} q^j κ` with `κ ≠ 0` converges
iff `|q| < 1`. -/
theorem summable_geom_succ_iff {q κ : ℝ} (hκ : κ ≠ 0) :
    Summable (fun j : ℕ => q ^ (j + 1) * κ) ↔ |q| < 1 := by
  rw [summable_nat_add_iff 1 (f := fun j : ℕ => q ^ j * κ), summable_mul_right_iff hκ,
    summable_geometric_iff_norm_lt_one, Real.norm_eq_abs]

/-- Cochrane (2023), (6.15) p. 205: with i.i.d. growth at every date, the correct present
value `Σ_{j≥1} E_t[...]` converges iff `|β mom(1−γ)| < 1` (for `κ ≠ 0`). -/
theorem correct_pv_summable_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) ↔ |β * mom (1 - γ)| < 1 := by
  have h : (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) =
      fun j => (β * mom (1 - γ)) ^ (j + 1) * κ := by
    funext j
    rw [correct_term 𝔼 hpo hpos hkp (hiid (t + (j + 1))) β γ κ le_rfl]
  rw [h, summable_geom_succ_iff hκ]

/-- Cochrane (2023), (6.16) p. 205: the incorrect present value converges iff
`|β mom(−γ) mom 1| < 1`, i.e. iff `(1+g)/(1+r) < 1` (for `κ ≠ 0`). -/
theorem incorrect_pv_summable_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
        𝔼.E t (ratio c t (j + 1)) ω * κ) ↔ |β * mom (-γ) * mom 1| < 1 := by
  have h : (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
      𝔼.E t (ratio c t (j + 1)) ω * κ) = fun j => (β * mom (-γ) * mom 1) ^ (j + 1) * κ := by
    funext j
    exact incorrect_term 𝔼 hpo hpos hkp (hiid (t + (j + 1))) β γ κ le_rfl ω
  rw [h, summable_geom_succ_iff hκ]

/-- Cochrane (2023), p. 205 ("the true present value can converge while this mistaken one
explodes"): if `0 ≤ β mom(1−γ) < 1 ≤ β mom(−γ) mom 1` then the correct present value (6.15)
converges and the incorrect one (6.16) does not. -/
theorem correct_finite_incorrect_explodes (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) {β γ κ : ℝ} (hκ : κ ≠ 0)
    (hq0 : 0 ≤ β * mom (1 - γ)) (hq1 : β * mom (1 - γ) < 1)
    (hρ : 1 ≤ β * mom (-γ) * mom 1) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) ∧
      ¬ Summable (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
        𝔼.E t (ratio c t (j + 1)) ω * κ) := by
  rw [correct_pv_summable_iff 𝔼 hpo hpos hkp hiid β γ hκ t ω,
    incorrect_pv_summable_iff 𝔼 hpo hpos hkp hiid β γ hκ t ω, abs_of_nonneg hq0]
  refine ⟨hq1, fun h => ?_⟩
  have := le_abs_self (β * mom (-γ) * mom 1)
  linarith

/-! ### Lognormal growth -/

/-- Cochrane (2023), p. 205: the moment `E[G^a] = e^{a μ + v a²/2}` of lognormal growth with
`log G ~ N(μ, v)`. -/
noncomputable def lognormalMoment (μ v a : ℝ) : ℝ := Real.exp (a * μ + v * a ^ 2 / 2)

/-- Cochrane (2023), p. 205: the lognormal moment formula, proved from the Gaussian moment
generating function: `∫ (e^x)^a d N(μ, v) = e^{a μ + v a²/2}`. -/
theorem lognormalMoment_eq_integral (μ : ℝ) (v : NNReal) (a : ℝ) :
    ∫ x, Real.exp x ^ a ∂(ProbabilityTheory.gaussianReal μ v) = lognormalMoment μ v a := by
  have h : (fun x => Real.exp x ^ a) = fun x => Real.exp (a * x) := by
    funext x; rw [← Real.exp_mul, mul_comm]
  rw [h]
  have hm := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := μ) (v := v)) a
  rw [ProbabilityTheory.mgf] at hm
  rw [hm, lognormalMoment]
  ring_nf

/-- Cochrane (2023), p. 205: with `β = e^{−δ}`, the ratio of successive correct terms is
`β E[G^{1−γ}] = e^{−δ + (1−γ)μ + (1−γ)² v/2}`. -/
theorem lognormal_correct (δ γ μ v : ℝ) :
    Real.exp (-δ) * lognormalMoment μ v (1 - γ) =
      Real.exp (-δ + (1 - γ) * μ + (1 - γ) ^ 2 * v / 2) := by
  rw [lognormalMoment, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 206 (corrected): the ratio of successive incorrect terms is
`β E[G^{−γ}] E[G] = e^{−δ + (1−γ)μ + (γ²+1) v/2}`. -/
theorem lognormal_incorrect (δ γ μ v : ℝ) :
    Real.exp (-δ) * lognormalMoment μ v (-γ) * lognormalMoment μ v 1 =
      Real.exp (-δ + (1 - γ) * μ + (γ ^ 2 + 1) * v / 2) := by
  rw [lognormalMoment, lognormalMoment, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 206 (error in the book): the printed incorrect term
`e^{[(1−γ)g + γ²σ²/2] j}` drops the `σ²/2` of `E[c'/c]`; for `v = σ² ≠ 0` the true value
`E[G^{−γ}] E[G]` differs from the printed `e^{(1−γ)μ + γ² v/2}`. -/
theorem printed_incorrect_wrong (γ μ : ℝ) {v : ℝ} (hv : v ≠ 0) :
    lognormalMoment μ v (-γ) * lognormalMoment μ v 1 ≠
      Real.exp ((1 - γ) * μ + γ ^ 2 * v / 2) := by
  rw [lognormalMoment, lognormalMoment, ← Real.exp_add]
  intro h
  have := Real.exp_injective h
  apply hv
  linarith

/-- Cochrane (2023), p. 206: the log-ratio of the correct terms,
`A = −δ + (1−γ)μ + (1−γ)² v/2`. -/
noncomputable def correctExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + (1 - γ) ^ 2 * v / 2

/-- Cochrane (2023), p. 206 (corrected): the log-ratio of the incorrect terms,
`B = −δ + (1−γ)μ + (γ²+1) v/2`. -/
noncomputable def incorrectExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + (γ ^ 2 + 1) * v / 2

/-- Cochrane (2023), p. 206: the exponent printed in the book, `−δ + (1−γ)μ + γ² v/2`. -/
noncomputable def printedExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + γ ^ 2 * v / 2

/-- Cochrane (2023), p. 206 (corrected; "it is entirely possible"): for `v = σ² > 0` there is a
`δ` with the correct present value finite (`A < 0`) and the incorrect one explosive (`B > 0`)
iff `γ > 0`; the book's sufficient condition `γ > 1` is not needed. -/
theorem region_nonempty_iff (γ μ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∃ δ, correctExponent δ γ μ v < 0 ∧ 0 < incorrectExponent δ γ μ v) ↔ 0 < γ := by
  unfold correctExponent incorrectExponent
  constructor
  · rintro ⟨δ, h1, h2⟩
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    refine ⟨(1 - γ) * μ + ((1 - γ) ^ 2 + γ) * v / 2, ?_, ?_⟩ <;> nlinarith

/-- Cochrane (2023), p. 206: with the printed exponent the region is non-empty iff
`γ > 1/2` (for `v > 0`), so the printed formula would wrongly exclude `0 < γ ≤ 1/2`. -/
theorem printed_region_iff (γ μ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∃ δ, correctExponent δ γ μ v < 0 ∧ 0 < printedExponent δ γ μ v) ↔ 1 / 2 < γ := by
  unfold correctExponent printedExponent
  constructor
  · rintro ⟨δ, h1, h2⟩
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    refine ⟨(1 - γ) * μ + ((1 - γ) ^ 2 + (γ - 1 / 2)) * v / 2, ?_, ?_⟩ <;> nlinarith

/-- Cochrane (2023), p. 206: for every `γ > 0` and `v > 0` there are a mean growth `μ` and a
discount rate `δ > 0` in the region. -/
theorem region_pos_delta {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    ∃ μ δ, 0 < δ ∧ correctExponent δ γ μ v < 0 ∧ 0 < incorrectExponent δ γ μ v := by
  refine ⟨0, ((1 - γ) ^ 2 + γ) * v / 2, by positivity, ?_, ?_⟩ <;>
    simp only [correctExponent, incorrectExponent] <;> nlinarith

/-- Cochrane (2023), p. 206 (Bohn's risk-free rate, corrected): with `β = e^{−δ}` and
lognormal growth, `log(1 + r_f) = δ + γ μ − γ² v/2`. -/
theorem log_riskFree_lognormal (δ γ μ v : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) =
      δ + γ * μ - γ ^ 2 * v / 2 := by
  rw [riskFreeGross, lognormalMoment, ← Real.exp_add, ← Real.exp_neg, Real.log_exp]
  ring

/-- Cochrane (2023), p. 206: in terms of the log of mean gross growth `g_m = μ + v/2`,
`log(1 + r_f) = δ + γ g_m − γ(γ + 1) v/2`. -/
theorem log_riskFree_mean_growth (δ γ μ v : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) =
      δ + γ * Real.log (lognormalMoment μ v 1) - γ * (γ + 1) * v / 2 := by
  rw [log_riskFree_lognormal, lognormalMoment, Real.log_exp]
  ring

/-- Cochrane (2023), p. 206 (error in the book): the printed `r = δ + γ g − γ(γ − 1)σ²/2`
matches neither convention when `γ σ² ≠ 0`: not `g = μ` (true `δ + γμ − γ²σ²/2`), nor
`g = g_m` (true `δ + γ g_m − γ(γ+1)σ²/2`). -/
theorem printed_bohn_rate_wrong (δ μ : ℝ) {γ v : ℝ} (hγ : γ ≠ 0) (hv : v ≠ 0) :
    δ + γ * μ - γ * (γ - 1) * v / 2 ≠
        Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) ∧
      δ + γ * Real.log (lognormalMoment μ v 1) - γ * (γ - 1) * v / 2 ≠
        Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) := by
  rw [log_riskFree_lognormal, lognormalMoment, Real.log_exp]
  have hγv : γ * v ≠ 0 := mul_ne_zero hγ hv
  constructor
  · intro h; apply hγv; linarith
  · intro h; apply hγv; linarith

/-- Cochrane (2023), p. 206: the risk-free rate is below mean growth, `1 + r_f < E[G]`, iff
the incorrect present value explodes (`B > 0`): the two statements are the same. -/
theorem riskFree_lt_growth_iff (δ γ μ v : ℝ) :
    riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 ↔
      0 < incorrectExponent δ γ μ v := by
  have hR : riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) =
      Real.exp (δ + γ * μ - γ ^ 2 * v / 2) := by
    rw [← log_riskFree_lognormal δ γ μ v, Real.exp_log]
    rw [riskFreeGross]
    exact inv_pos.mpr (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  rw [hR, lognormalMoment, Real.exp_lt_exp, incorrectExponent]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), pp. 205–206 (Theorem B, lognormal form): for every `γ > 0` and `σ² > 0`
there are `μ` and `δ > 0` such that the correct present value converges
(`β E[G^{1−γ}] < 1`, `β = e^{−δ}`) while the risk-free rate is below mean growth. -/
theorem bohn_region {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    ∃ μ δ, 0 < δ ∧ Real.exp (-δ) * lognormalMoment μ v (1 - γ) < 1 ∧
      riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 := by
  obtain ⟨μ, δ, hδ, hA, hB⟩ := region_pos_delta hγ hv
  refine ⟨μ, δ, hδ, ?_, (riskFree_lt_growth_iff δ γ μ v).mpr hB⟩
  rw [lognormal_correct, Real.exp_lt_one_iff]
  exact hA

/-! ### (6.17): debt rolled over at the risk-free rate -/

/-- Cochrane (2023), (6.17) p. 207: rolling debt over at the risk-free rate: with
`β mom(−γ) R = 1` and `b` adapted, `E_t[D_{j+1} R b_{t+j}] = E_t[D_j b_{t+j}]` for
`t + j < H` ("the present value of borrowing and repaying `(1+r)` next period is zero"). -/
theorem rollover_step (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {b : ℕ → Ω → ℝ} (hb : 𝔼.Adapted b) {t j : ℕ} (hj : t + j < H) :
    𝔼.E t (fun ω => pvDisc β γ c t (j + 1) ω * (R * b (t + j) ω)) =
      𝔼.E t (fun ω => pvDisc β γ c t j ω * b (t + j) ω) := by
  have hY : 𝔼.E (t + j) (fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω) =
      fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω :=
    known_mul 𝔼 hpo (ratio_rpow_known 𝔼 hpo hpos hkp t j (-γ)) (hb (t + j))
  have hL : (fun ω => pvDisc β γ c t (j + 1) ω * (R * b (t + j) ω)) =
      (β ^ (j + 1) * R) •
        fun ω => (ratio c t j ω ^ (-γ) * b (t + j) ω) * growth c (t + j) ω ^ (-γ) := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [ratio_succ (hpos t ω).ne' (hpos (t + j) ω).ne',
      Real.mul_rpow (ratio_pos hpos t j ω).le (growth_pos hpos (t + j) ω).le]
    ring
  have hRt : (fun ω => pvDisc β γ c t j ω * b (t + j) ω) =
      β ^ j • fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω := by
    funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
  rw [hL, hRt, 𝔼.E_smul, 𝔼.E_smul, ← 𝔼.tower (Nat.le_add_right t j),
    E_growth_mul 𝔼 hpo hiid hj hY (-γ)]
  have hs : (fun ω => mom (-γ) * (ratio c t j ω ^ (-γ) * b (t + j) ω)) =
      mom (-γ) • fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω := rfl
  rw [hs, 𝔼.E_smul, smul_smul]
  congr 1
  linear_combination β ^ j * hR

/-- **(6.17)**, Cochrane (2023), p. 207: if debt `b` (adapted) is rolled over at the risk-free
rate, `s_{u+1} = R b_u − b_{u+1}` with `β E[G^{−γ}] R = 1`, then for `t + T ≤ H`
`b_t = E_t Σ_{j=1}^T β^j (c_{t+j}/c_t)^{−γ} s_{t+j} + E_t[β^T (c_{t+T}/c_t)^{−γ} b_{t+T}]`. -/
theorem eq_6_17 (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {b s : ℕ → Ω → ℝ} (hb : 𝔼.Adapted b) (hs : ∀ u ω, s (u + 1) ω = R * b u ω - b (u + 1) ω)
    (t : ℕ) : ∀ T, t + T ≤ H →
      b t = 𝔼.E t (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω)
        + 𝔼.E t (fun ω => pvDisc β γ c t T ω * b (t + T) ω) := by
  intro T
  induction T with
  | zero =>
    intro _
    have h0 : (fun ω => ∑ j ∈ Finset.range 0, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
        0 := by funext ω; simp
    have h1 : (fun ω => pvDisc β γ c t 0 ω * b (t + 0) ω) = b t := by
      funext ω; simp [pvDisc, ratio_zero (hpos t ω).ne']
    rw [h0, h1, map_zero, hb t, zero_add]
  | succ T ih =>
    intro hT
    rw [ih (by omega)]
    have hsplit : (fun ω => ∑ j ∈ Finset.range (T + 1),
        pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
        (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) +
          fun ω => pvDisc β γ c t (T + 1) ω * s (t + T + 1) ω := by
      funext ω; simp [Finset.sum_range_succ]
    have hcomb : (fun ω => pvDisc β γ c t (T + 1) ω * s (t + T + 1) ω) +
        (fun ω => pvDisc β γ c t (T + 1) ω * b (t + (T + 1)) ω) =
        fun ω => pvDisc β γ c t (T + 1) ω * (R * b (t + T) ω) := by
      funext ω
      simp only [Pi.add_apply]
      rw [hs (t + T) ω, ← add_assoc]
      ring
    have hstep := rollover_step 𝔼 hpo hpos hkp hiid hR hb (t := t) (j := T) (by omega)
    rw [hsplit, map_add, add_assoc, ← hstep, ← hcomb, map_add]

/-- Cochrane (2023), (6.17) p. 207: for the debt `b = c` (debt equal to GDP), the terminal
term is `E_t[β^T (c_{t+T}/c_t)^{−γ} c_{t+T}] = (β mom(1−γ))^T c_t`, for `t + T ≤ H`. -/
theorem terminal_c (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ : ℝ) {t T : ℕ} (hT : t + T ≤ H) :
    𝔼.E t (fun ω => pvDisc β γ c t T ω * c (t + T) ω) =
      fun ω => (β * mom (1 - γ)) ^ T * c t ω := by
  have hct : 𝔼.E t (c t) = c t := by
    have h := hkp t 1
    simp only [Real.rpow_one] at h
    exact h
  have h : (fun ω => pvDisc β γ c t T ω * c (t + T) ω) =
      β ^ T • fun ω => ratio c t T ω ^ (1 - γ) * c t ω := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos hpos t T ω),
      Real.rpow_one, ratio]
    field_simp [(hpos t ω).ne']
  rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid hct (1 - γ) T hT]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.17) p. 207: each term of the present value of the surpluses
`s_{t+j+1} = R c_{t+j} − c_{t+j+1}` is `E_t[β^{j+1} (c_{t+j+1}/c_t)^{−γ} s_{t+j+1}] =
q^j (1 − q) c_t`, `q = β mom(1−γ)`, for `t + j + 1 ≤ H`. -/
theorem pv_term_c (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {s : ℕ → Ω → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) {t j : ℕ}
    (hj : t + j + 1 ≤ H) :
    𝔼.E t (fun ω => pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
      fun ω => (β * mom (1 - γ)) ^ j * (1 - β * mom (1 - γ)) * c t ω := by
  have hca : 𝔼.Adapted c := fun u => by
    have h := hkp u 1
    simp only [Real.rpow_one] at h
    exact h
  have hfun : (fun ω => pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ c t (j + 1) ω * (R * c (t + j) ω)) -
        fun ω => pvDisc β γ c t (j + 1) ω * c (t + (j + 1)) ω := by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  rw [hfun, map_sub, rollover_step 𝔼 hpo hpos hkp hiid hR hca (by omega),
    terminal_c 𝔼 hpo hpos hkp hiid β γ (by omega),
    terminal_c 𝔼 hpo hpos hkp hiid β γ (by omega)]
  funext ω
  simp only [Pi.sub_apply, pow_succ]
  ring

/-- Cochrane (2023), (6.17) p. 207 ("the last term converges to zero, via the transversality
condition", made precise): the terminal term `(β mom(1−γ))^T c_t` tends to zero iff
`β mom(1−γ) < 1` (for `β mom(1−γ) ≥ 0` and `c_t > 0`). -/
theorem terminal_tendsto_iff {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) :
    Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0) ↔ q < 1 := by
  constructor
  · intro h
    have h2 : Tendsto (fun T : ℕ => q ^ T) atTop (𝓝 0) := by
      have := h.mul_const x⁻¹
      simp only [zero_mul] at this
      refine this.congr fun T => ?_
      field_simp
    rw [tendsto_pow_atTop_nhds_zero_iff, abs_of_nonneg hq] at h2
    exact h2
  · intro h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq h).mul_const x

/-- **(6.15) for Bohn's example**, Cochrane (2023), (6.17) p. 207, infinite horizon: with i.i.d.
growth at every date, debt equal to consumption, rolled over at the risk-free rate, equals the
infinite SDF present value of its surpluses, `Σ_{j≥1} E_t[β^j (c_{t+j}/c_t)^{−γ} s_{t+j}] = c_t`,
iff `β E[G^{1−γ}] < 1` (given `β E[G^{1−γ}] ≥ 0`). -/
theorem bohn_pv_hasSum_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {s : ℕ → Ω → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω)
    (hq0 : 0 ≤ β * mom (1 - γ)) (t : ℕ) (ω : Ω) :
    HasSum (fun j => 𝔼.E t (fun ω' => pvDisc β γ c t (j + 1) ω' * s (t + j + 1) ω') ω)
      (c t ω) ↔ β * mom (1 - γ) < 1 := by
  set q := β * mom (1 - γ) with hq
  have hterm : (fun j => 𝔼.E t (fun ω' => pvDisc β γ c t (j + 1) ω' * s (t + j + 1) ω') ω) =
      fun j => q ^ j * (1 - q) * c t ω := by
    funext j
    rw [pv_term_c 𝔼 hpo hpos hkp (hiid (t + j + 1)) hR hs le_rfl]
  have hc := hpos t ω
  rw [hterm]
  constructor
  · intro h
    by_contra hq1
    push Not at hq1
    rcases hq1.eq_or_lt with h1 | h1
    · have h0 : HasSum (fun j : ℕ => q ^ j * (1 - q) * c t ω) 0 := by
        rw [← h1]; simp
      have := h.unique h0
      linarith
    · have hlim := h.summable.tendsto_atTop_zero
      have hle : ∀ j : ℕ, q ^ j * (1 - q) * c t ω ≤ (1 - q) * c t ω := fun j => by
        have hp : 1 ≤ q ^ j := one_le_pow₀ h1.le
        have hneg : (1 - q) * c t ω < 0 := mul_neg_of_neg_of_pos (by linarith) hc
        nlinarith
      have := le_of_tendsto' hlim hle
      nlinarith
  · intro hq1
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right ((1 - q) * c t ω)
    have hval : (1 - q)⁻¹ * ((1 - q) * c t ω) = c t ω := by
      field_simp [(by linarith : (1 - q) ≠ 0)]
    rw [hval] at hg
    refine hg.congr_fun ?_
    intro j
    ring

/-! ### (6.18): discounting at the risk-free rate -/

/-- Cochrane (2023), p. 207: for the rollover surpluses the ex-post return on debt is the
risk-free rate, `(c_{u+1} + s_{u+1})/c_u = R`. -/
theorem bohn_grossReturn {c s : ℕ → Ω → ℝ} {R : ℝ} (hpos : ∀ t ω, 0 < c t ω)
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) (u : ℕ) (ω : Ω) :
    ReturnDiscounting.grossReturn c s u ω = R := by
  rw [ReturnDiscounting.grossReturn, hs u ω]
  field_simp [(hpos u ω).ne']
  ring

/-- **(6.18), pathwise**, Cochrane (2023), p. 207: discounting at the risk-free rate,
`c_t = Σ_{j=1}^T R^{−j} s_{t+j} + R^{−T} c_{t+T}`, and the present-value term equals
`c_t − R^{−T} c_{t+T}`. -/
theorem eq_6_18_pathwise {c s : ℕ → Ω → ℝ} {R : ℝ} (hR : R ≠ 0) (hpos : ∀ t ω, 0 < c t ω)
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) (t T : ℕ) (ω : Ω) :
    c t ω = (∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) +
        (R⁻¹) ^ T * c (t + T) ω ∧
      (∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
        c t ω - (R⁻¹) ^ T * c (t + T) ω := by
  have hdisc : ∀ j, ReturnDiscounting.returnDiscount c s t j ω = (R⁻¹) ^ j := fun j => by
    unfold ReturnDiscounting.returnDiscount
    simp [bohn_grossReturn hpos hs]
  have hpd : ∀ u ω', c (u + 1) ω' + s (u + 1) ω' ≠ 0 := fun u ω' => by
    rw [hs u ω']
    have := mul_ne_zero hR (hpos u ω').ne'
    intro h; apply this; linarith
  have h := ReturnDiscounting.eq_6_14_pathwise hpd t ω T
  simp only [ReturnDiscounting.returnPV, hdisc] at h
  exact ⟨h, by linarith⟩

/-- **(6.18)**, Cochrane (2023), p. 207: taking expectations with i.i.d. growth, the
return-discounted present value is `E_t[PV_T] = c_t (1 − (E[G]/R)^T)` and the terminal term
is `E_t[R^{−T} c_{t+T}] = c_t (E[G]/R)^T`, for `t + T ≤ H`. -/
theorem eq_6_18 (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {R : ℝ} (hR : R ≠ 0) {s : ℕ → Ω → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) {t T : ℕ} (hT : t + T ≤ H) :
    𝔼.E t (fun ω => (R⁻¹) ^ T * c (t + T) ω) = (fun ω => c t ω * (mom 1 / R) ^ T) ∧
      𝔼.E t (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
        fun ω => c t ω * (1 - (mom 1 / R) ^ T) := by
  have hct : 𝔼.E t (c t) = c t := by
    have h := hkp t 1
    simp only [Real.rpow_one] at h
    exact h
  have hterm : 𝔼.E t (fun ω => (R⁻¹) ^ T * c (t + T) ω) =
      fun ω => c t ω * (mom 1 / R) ^ T := by
    have h : (fun ω => (R⁻¹) ^ T * c (t + T) ω) =
        (R⁻¹) ^ T • fun ω => ratio c t T ω ^ (1 : ℝ) * c t ω := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, Real.rpow_one, ratio]
      field_simp [(hpos t ω).ne']
    rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid hct 1 T hT]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, div_pow, inv_pow]
    field_simp
  refine ⟨hterm, ?_⟩
  have hfun : (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
      c t - fun ω => (R⁻¹) ^ T * c (t + T) ω := by
    funext ω
    rw [Pi.sub_apply, (eq_6_18_pathwise hR hpos hs t T ω).2]
  rw [hfun, map_sub, hct, hterm]
  funext ω
  simp only [Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 207 ("with `r < g` the present value of cashflows term builds to
negative infinity, and the terminal value builds to positive infinity"): if
`0 < R < E[G]` and `c_t > 0` then `c_t (1 − (E[G]/R)^T) → −∞` and `c_t (E[G]/R)^T → +∞`. -/
theorem eq_6_18_diverges {R m x : ℝ} (hR : 0 < R) (hRm : R < m) (hx : 0 < x) :
    Tendsto (fun T : ℕ => x * (1 - (m / R) ^ T)) atTop atBot ∧
      Tendsto (fun T : ℕ => x * (m / R) ^ T) atTop atTop := by
  have h1 : 1 < m / R := by rw [lt_div_iff₀ hR]; linarith
  have hpow : Tendsto (fun T : ℕ => (m / R) ^ T) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h1
  have hterm : Tendsto (fun T : ℕ => x * (m / R) ^ T) atTop atTop :=
    hpow.const_mul_atTop hx
  refine ⟨?_, hterm⟩
  have heq : (fun T : ℕ => x * (1 - (m / R) ^ T)) = fun T => x - x * (m / R) ^ T := by
    funext T; ring
  rw [heq]
  exact tendsto_atBot_add_const_left _ x (tendsto_neg_atTop_atBot.comp hterm)

/-! ### The two-state witness -/

/-- Cochrane (2023), p. 206 (Bohn's example, two-state version): the date-`t` observation of a
sequence of `H` coin flips — the flips `0, …, t − 1` are revealed by date `t`. -/
def coinObsH (H t : ℕ) (ω : Fin H → Bool) : Fin H → Bool :=
  fun i => if (i : ℕ) < t then ω i else false

/-- Cochrane (2023), p. 206: two states `ω ~_t ω'` share the first `t` flips. -/
theorem coinObsH_eq_iff {H t : ℕ} {ω ω' : Fin H → Bool} :
    coinObsH H t ω = coinObsH H t ω' ↔ ∀ i : Fin H, (i : ℕ) < t → ω i = ω' i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [coinObsH, hi] using this
  · intro h
    funext i
    unfold coinObsH
    split_ifs with hi
    · exact h i hi
    · rfl

/-- Cochrane (2023), p. 206: the i.i.d. fair coin tree with horizon `H`: uniform probability on
`Fin H → Bool`, flip `i` revealed at date `i + 1`. -/
noncomputable def bohnTree (H : ℕ) : ExpectationsFiniteTree.FiniteTree (Fin H → Bool) where
  prob := fun _ => (1 / 2) ^ H
  prob_pos := fun _ => by positivity
  prob_sum := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]; norm_num
  info := fun t => Setoid.ker (coinObsH H t)
  refines := by
    intro s t hst a b h
    rw [Setoid.ker_def, coinObsH_eq_iff] at h ⊢
    exact fun i hi => h i (lt_of_lt_of_le hi hst)

/-- Cochrane (2023), p. 206: the expectation system of the coin tree. -/
noncomputable def bohnSystem (H : ℕ) : ExpectationSystem (Fin H → Bool) :=
  (bohnTree H).toExpectationSystem

/-- Cochrane (2023), p. 206: the coin tree has the pull-out property. -/
theorem bohnSystem_pullOut (H : ℕ) : (bohnSystem H).PullOut :=
  ExpectationsFiniteTree.finiteTree_pullOut (bohnTree H)

/-- Cochrane (2023), p. 206: flipping coin `i₀` (not yet revealed at `t`, since `t ≤ i₀`)
preserves the date-`t` information cell. -/
theorem info_flip {H t : ℕ} {i₀ : Fin H} (hi : t ≤ (i₀ : ℕ)) (ω ω' : Fin H → Bool) :
    (bohnTree H).info t (Function.update ω' i₀ (!ω' i₀)) ω ↔ (bohnTree H).info t ω' ω := by
  change Setoid.ker _ _ _ ↔ Setoid.ker _ _ _
  rw [Setoid.ker_def, Setoid.ker_def, coinObsH_eq_iff, coinObsH_eq_iff]
  have hu : ∀ i : Fin H, (i : ℕ) < t → Function.update ω' i₀ (!ω' i₀) i = ω' i := by
    intro i hit
    rw [Function.update_of_ne]
    intro h; rw [h] at hit; omega
  constructor
  · intro h i hit; rw [← hu i hit]; exact h i hit
  · intro h i hit; rw [hu i hit]; exact h i hit

/-- Cochrane (2023), p. 206: in the coin tree, a function of the not-yet-revealed coin
`i₀ ≥ t` has date-`t` expectation `(f true + f false)/2` — the coin is fair and independent
of the past. -/
theorem bohnTree_condE_coin {H t : ℕ} {i₀ : Fin H} (hi : t ≤ (i₀ : ℕ)) (f : Bool → ℝ)
    (ω : Fin H → Bool) :
    (bohnTree H).condE t (fun ω' => f (ω' i₀)) ω = (f true + f false) / 2 := by
  classical
  set T := bohnTree H with hT
  let flip : Equiv.Perm (Fin H → Bool) :=
    Function.Involutive.toPerm (fun ω' => Function.update ω' i₀ (!ω' i₀)) (fun ω' => by
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h])
  have hflip : ∀ ω', flip ω' = Function.update ω' i₀ (!ω' i₀) := fun _ => rfl
  have hprob : ∀ ω', T.prob ω' = (1 / 2) ^ H := fun _ => rfl
  have hnum : T.num t (fun ω' => f (ω' i₀)) ω =
      ∑ ω', if T.info t ω' ω then T.prob ω' * f (!ω' i₀) else 0 := by
    unfold ExpectationsFiniteTree.FiniteTree.num
    rw [← Equiv.sum_comp flip]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [hflip, info_flip hi, hprob, hprob]
    simp
  have h2 : 2 * T.num t (fun ω' => f (ω' i₀)) ω = (f true + f false) * T.mass t ω := by
    have hn1 : T.num t (fun ω' => f (ω' i₀)) ω =
        ∑ ω', if T.info t ω' ω then T.prob ω' * f (ω' i₀) else 0 := rfl
    rw [two_mul]
    nth_rewrite 1 [hn1]
    rw [hnum, ← Finset.sum_add_distrib]
    unfold ExpectationsFiniteTree.FiniteTree.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    by_cases h : T.info t ω' ω
    · simp only [h, ↓reduceIte]
      cases ω' i₀ <;> simp <;> ring
    · simp [h]
  unfold ExpectationsFiniteTree.FiniteTree.condE
  have hm := T.mass_pos t ω
  field_simp
  linarith

/-- Cochrane (2023), p. 206: the two growth states, `G = 5/4` (heads) or `G = 17/20`
(tails). -/
noncomputable def bohnGrowth (b : Bool) : ℝ := if b then 5 / 4 else 17 / 20

/-- Cochrane (2023), p. 206: two-state growth is positive. -/
theorem bohnGrowth_pos (b : Bool) : 0 < bohnGrowth b := by
  cases b <;> norm_num [bohnGrowth]

/-- Cochrane (2023), p. 206: consumption in the coin tree, `c_t = Π_{i < t} G(ω_i)` with
`c_0 = 1`. -/
noncomputable def bohnC (H t : ℕ) (ω : Fin H → Bool) : ℝ :=
  ∏ i : Fin H, if (i : ℕ) < t then bohnGrowth (ω i) else 1

/-- Cochrane (2023), p. 206: consumption is positive. -/
theorem bohnC_pos (H t : ℕ) (ω : Fin H → Bool) : 0 < bohnC H t ω := by
  unfold bohnC
  refine Finset.prod_pos fun i _ => ?_
  split_ifs
  · exact bohnGrowth_pos _
  · exact one_pos

/-- Cochrane (2023), p. 206: before the horizon, consumption growth is the coin's growth,
`c_{t+1}/c_t = G(ω_t)`. -/
theorem bohnC_growth {H t : ℕ} (ht : t < H) (ω : Fin H → Bool) :
    growth (bohnC H) t ω = bohnGrowth (ω ⟨t, ht⟩) := by
  unfold growth
  rw [div_eq_iff (bohnC_pos H t ω).ne']
  have hG : (∏ i : Fin H, if (⟨t, ht⟩ : Fin H) = i then bohnGrowth (ω i) else 1) =
      bohnGrowth (ω ⟨t, ht⟩) := by
    rw [Finset.prod_ite_eq]; simp
  unfold bohnC
  rw [mul_comm, ← hG, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < t
  · have hne : (⟨t, ht⟩ : Fin H) ≠ i := fun h => by rw [← h] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, hne]
  · by_cases h2 : (i : ℕ) = t
    · have heq : (⟨t, ht⟩ : Fin H) = i := Fin.ext h2.symm
      simp [h2, heq]
    · have h3 : ¬ (i : ℕ) < t + 1 := by omega
      have hne : (⟨t, ht⟩ : Fin H) ≠ i := fun h => h2 (by rw [← h])
      simp [h1, h3, hne]

/-- Cochrane (2023), p. 206: powers of consumption are known in the coin tree. -/
theorem bohnSystem_knownPowers (H : ℕ) : KnownPowers (bohnSystem H) (bohnC H) := by
  intro t a
  funext ω
  change (bohnTree H).condE t _ ω = _
  refine (bohnTree H).condE_of_const_on_cell fun ω' h => ?_
  change Setoid.ker _ _ _ at h
  rw [Setoid.ker_def, coinObsH_eq_iff] at h
  have : bohnC H t ω' = bohnC H t ω := by
    unfold bohnC
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [h i hi]
    · rfl
  rw [this]

/-- Cochrane (2023), p. 206: the moments of two-state growth,
`E[G^a] = ((5/4)^a + (17/20)^a)/2`. -/
noncomputable def bohnMom (a : ℝ) : ℝ := (bohnGrowth true ^ a + bohnGrowth false ^ a) / 2

/-- Cochrane (2023), p. 206: the coin tree has i.i.d. growth before its horizon, with moments
`bohnMom`. -/
theorem bohnSystem_iid (H : ℕ) : IIDGrowth (bohnSystem H) (bohnC H) bohnMom H := by
  intro t ht a
  funext ω
  have hfun : (fun ω' => growth (bohnC H) t ω' ^ a) =
      fun ω' => (fun b => bohnGrowth b ^ a) (ω' ⟨t, ht⟩) := by
    funext ω'; rw [bohnC_growth ht]
  change (bohnTree H).condE t _ ω = _
  rw [hfun]
  exact bohnTree_condE_coin (i₀ := ⟨t, ht⟩) (le_refl t) (fun b => bohnGrowth b ^ a) ω

/-- Cochrane (2023), p. 206: the two-state numbers (all exact): `E[G] = 21/20`,
`E[G^{−1}] = 84/85`, `E[G^{−2}] = 7312/7225`. -/
theorem bohnMom_values :
    bohnMom 1 = 21 / 20 ∧ bohnMom (-1) = 84 / 85 ∧ bohnMom (-2) = 7312 / 7225 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bohnMom, bohnGrowth]; norm_num
  · simp only [bohnMom, bohnGrowth, ↓reduceIte, Bool.false_eq_true, Real.rpow_neg_one]
    norm_num
  · simp only [bohnMom, bohnGrowth, ↓reduceIte, Bool.false_eq_true]
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_two,
      Real.rpow_two]
    norm_num

/-- Cochrane (2023), pp. 205–207 (Theorem B, two-state witness): with `β = 49/50`, `γ = 2`
and `G ∈ {17/20, 5/4}` equally likely, the risk-free rate `1 + r_f = 361250/358288 ≈ 1.0083`
is below mean growth `E[G] = 1.05` (`r_f < g`), while `β E[G^{1−γ}] = 4116/4250 ≈ 0.968 < 1`
(the correct present value converges), so the incorrect present value explodes:
`β E[G^{−γ}] E[G] > 1`. -/
theorem bohn_numbers :
    riskFreeGross (49 / 50) 2 bohnMom = 361250 / 358288 ∧
      riskFreeGross (49 / 50) 2 bohnMom < bohnMom 1 ∧
      (49 / 50 : ℝ) * bohnMom (1 - 2) = 4116 / 4250 ∧
      (49 / 50 : ℝ) * bohnMom (1 - 2) < 1 ∧
      1 < (49 / 50 : ℝ) * bohnMom (-2) * bohnMom 1 := by
  obtain ⟨h1, hm1, hm2⟩ := bohnMom_values
  have hR : riskFreeGross (49 / 50) 2 bohnMom = 361250 / 358288 := by
    rw [riskFreeGross, hm2]; norm_num
  have hq : (49 / 50 : ℝ) * bohnMom (1 - 2) = 4116 / 4250 := by
    rw [show (1 : ℝ) - 2 = -1 by norm_num, hm1]; norm_num
  refine ⟨hR, ?_, hq, ?_, ?_⟩
  · rw [hR, h1]; norm_num
  · rw [hq]; norm_num
  · rw [hm2, h1]; norm_num

/-- Cochrane (2023), (6.17) p. 207, two-state witness: in the coin tree of any horizon
`H ≥ T`, for debt `b = c` rolled over at the risk-free rate `R`, (6.17) holds at date 0
with genuine uncertainty, and the terminal term is `(4116/4250)^T` (`c_0 = 1`), which tends to
zero as `T → ∞`. -/
theorem bohn_witness_6_17 {H T : ℕ} (hT : T ≤ H) {s : ℕ → (Fin H → Bool) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) :
    bohnC H 0 = (bohnSystem H).E 0 (fun ω => ∑ j ∈ Finset.range T,
        pvDisc (49 / 50) 2 (bohnC H) 0 (j + 1) ω * s (0 + j + 1) ω) +
      (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) ∧
    (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) =
      (fun _ => (4116 / 4250 : ℝ) ^ T) ∧
    Tendsto (fun T : ℕ => (4116 / 4250 : ℝ) ^ T) atTop (𝓝 0) := by
  have hR : (49 / 50 : ℝ) * bohnMom (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
    rw [riskFreeGross, bohnMom_values.2.2]
    norm_num
  have hca : (bohnSystem H).Adapted (bohnC H) := fun u => by
    have h := bohnSystem_knownPowers H u 1
    simp only [Real.rpow_one] at h
    exact h
  have hc0 : ∀ ω, bohnC H 0 ω = 1 := fun ω => by simp [bohnC]
  refine ⟨eq_6_17 (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) hR hca hs 0 T (by omega), ?_, ?_⟩
  · rw [terminal_c (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ (by omega)]
    funext ω
    rw [hc0, mul_one, bohn_numbers.2.2.1]
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Cochrane (2023), (6.18) p. 207, two-state witness: in the coin tree of any horizon
`H ≥ T`, discounting at the risk-free rate `R = 361250/358288`, the expected present value of
the rollover surpluses is `1 − ((21/20)/R)^T` and the expected terminal term is
`((21/20)/R)^T`; since `R < 21/20` (`r_f < g`) these tend to `−∞` and `+∞`. -/
theorem bohn_witness_6_18 {H T : ℕ} (hT : T ≤ H) {s : ℕ → (Fin H → Bool) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) :
    (bohnSystem H).E 0 (fun ω => ∑ j ∈ Finset.range T,
        (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ (j + 1) * s (0 + j + 1) ω) =
      (fun _ => 1 - ((21 / 20) / (361250 / 358288)) ^ T) ∧
    (bohnSystem H).E 0 (fun ω => (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ T * bohnC H (0 + T) ω) =
      (fun _ => ((21 / 20) / (361250 / 358288)) ^ T) ∧
    Tendsto (fun T : ℕ => 1 * (1 - ((21 / 20 : ℝ) / (361250 / 358288)) ^ T)) atTop atBot ∧
    Tendsto (fun T : ℕ => 1 * ((21 / 20 : ℝ) / (361250 / 358288)) ^ T) atTop atTop := by
  obtain ⟨hR, hRm, -, -, -⟩ := bohn_numbers
  have hR0 : riskFreeGross (49 / 50) 2 bohnMom ≠ 0 := by rw [hR]; norm_num
  have hc0 : ∀ ω, bohnC H 0 ω = 1 := fun ω => by simp [bohnC]
  obtain ⟨h1, h2⟩ := eq_6_18 (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
    (bohnSystem_knownPowers H) (bohnSystem_iid H) hR0 hs (t := 0) (T := T) (by omega)
  have hm1 : bohnMom 1 = 21 / 20 := bohnMom_values.1
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; funext ω; rw [hc0, hm1, hR, one_mul]
  · rw [h1]; funext ω; rw [hc0, hm1, hR, one_mul]
  · exact eq_6_18_diverges (by norm_num) (by norm_num) one_pos

/-- Cochrane (2023), (6.15)–(6.16) pp. 205–206, two-state witness: in the coin tree of any
horizon `H ≥ j`, the `j`-th correct summand (constant surplus ratio `κ`) is
`(4116/4250)^j κ`, while the `j`-th summand with the expectation inside is `ρ^j κ` with
`ρ = β E[G^{−2}] E[G] > 1`: the correct terms shrink geometrically, the incorrect ones grow. -/
theorem bohn_witness_terms {H j : ℕ} (hj : j ≤ H) (κ : ℝ) (ω : Fin H → Bool) :
    (bohnSystem H).E 0 (pvTerm (49 / 50) 2 κ (bohnC H) 0 j) ω = (4116 / 4250) ^ j * κ ∧
      (bohnSystem H).E 0 (fun ω' => (49 / 50) ^ j * ratio (bohnC H) 0 j ω' ^ (-2 : ℝ)) ω *
          (bohnSystem H).E 0 (ratio (bohnC H) 0 j) ω * κ =
        ((49 / 50) * (7312 / 7225) * (21 / 20)) ^ j * κ ∧
      1 < (49 / 50 : ℝ) * (7312 / 7225) * (21 / 20) := by
  obtain ⟨hm1, -, hm2⟩ := bohnMom_values
  refine ⟨?_, ?_, by norm_num⟩
  · rw [correct_term (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ κ (by omega), bohn_numbers.2.2.1]
  · rw [incorrect_term (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ κ (by omega), hm1, hm2]

end Cochrane.FiscalConstraints.AggregateUncertainty

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the Chapter 6 developments

Cochrane (2023), Chapter 6, *Fiscal constraints*, §6.2 and §6.4 (pp. 191–207). The chapter was
formalised in two independent chains; this module proves that their objects agree where the
book talks about the same thing.

## Main results

* `forward_integral_eq_pv`, `forward_present_value_eq_pv`: the forward present value of (6.9)
  (`LinearODE.forward_present_value`, used in `MoneyLiquidity`) is `RvsG.pv`, the present value
  of §6.4.1 (pp. 196, 201).
* `valueOfDebt_eq_pv`: the value of debt (6.2) after substituting (6.1)/(6.6) is `RvsG.pv` of a
  constant surplus ratio, discounted at `r − g` (pp. 191, 195).
* `marginalValue_consumption`, `euler_iff_rate`, `rate_population_lt_growth_iff`: the
  first-order condition of §6.2 (`DiscountGrowth`) and of §6.4.4 (`GrowthTheoryTVC`) are the
  same equation (6.1) = (6.6) (pp. 191, 199–200).
* `growth_tvc_term_eq_levels`, `growth_tvc_iff_levels_tvc`, `steady_debt_is_pv`,
  `growth_tvc_from_rvsg`: the growth-theory TVC of p. 200 is the TVC in levels of §6.4.1
  (`RvsG.tvc_levels_iff`) for debt in a steady ratio to output; `r > g` makes the steady ratio
  the present value (p. 196).
* `debt_gdp_solvesD`, `debtPath_solvesD`, `debtPath_abs_le`, `gaussian_not_bddD`: the stochastic
  debt path of Theorem S is, path by path, the discrete solution of (6.4) studied in `RvsG`
  (D5). With bounded surpluses every path is bounded (D5, "indeterminacy, not infinity"); with
  i.i.d. Gaussian surpluses almost every path is unbounded (Theorem S, p. 197).
* `deterministic_rf_lt_g_iff`, `rf_lt_g_pv_finite_needs_risk`: without risk, `r_f < g` is
  exactly divergence of the present value (Theorem D of `RvsG`); with lognormal growth risk the
  two separate (Bohn's case, pp. 205–206).
-/

namespace Cochrane.FiscalConstraints.Links

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.AggregateUncertainty (riskFreeGross lognormalMoment)

/-! ### Forward present values (§6.4.1 and §6.4.5) -/

/-- Cochrane (2023), (6.9) p. 201 and §6.4.1 p. 196: the forward integral of (6.9),
`∫_t^∞ e^{−a(τ−t)} f_τ dτ`, is the present value `RvsG.pv a f t = ∫₀^∞ e^{−a u} f_{t+u} du`. -/
theorem forward_integral_eq_pv (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ∫ τ in Set.Ioi t, exp (-a * (τ - t)) * f τ = RvsG.pv a f t := by
  have h := ExpIntegrals.integral_Ioi_comp_add (fun τ => exp (-a * (τ - t)) * f τ) t
  simp only [add_sub_cancel_left] at h
  unfold RvsG.pv
  exact h.symm

/-- Cochrane (2023), (6.9) p. 201 and §6.4.1 p. 196: a solution of `w' = a w − f` on `ℝ`
satisfying the transversality condition from `t` equals the present value `RvsG.pv a f t` of
§6.4.1 (for `a = r − g > 0` and bounded continuous `f`). -/
theorem forward_present_value_eq_pv {a K : ℝ} (ha : 0 < a) {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K)
    (t : ℝ) (htvc : Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    w t = RvsG.pv a f t := by
  rw [(LinearODE.forward_present_value ha hw hf hK t htvc).2, forward_integral_eq_pv]

/-- Cochrane (2023), (6.2) p. 191 and (6.3) p. 195: the value of debt with `r = δ + γ g`
substituted, `σ/(δ + (γ − 1) g)`, is the present value `RvsG.pv` of the constant surplus
ratio `σ` discounted at `r − g > 0`. -/
theorem valueOfDebt_eq_pv {σ δ γ g : ℝ} (h : g < GrowthTheoryTVC.rate δ γ g) (t : ℝ) :
    DiscountGrowth.valueOfDebt σ δ γ g =
      RvsG.pv (GrowthTheoryTVC.rate δ γ g - g) (fun _ => σ) t := by
  rw [RvsG.pv_const (sub_pos.2 h)]
  rfl

/-! ### The consumer's first-order condition: (6.1) = (6.6) -/

/-- Cochrane (2023), (6.1) p. 191 and (6.6) p. 199: the marginal value of a unit invested at `r`
(`DiscountGrowth.marginalValue`) along balanced growth is discounted marginal utility
(`GrowthTheoryTVC.marginalUtility`) times `e^{r t}`. -/
theorem marginalValue_consumption (δ γ r c₀ g t : ℝ) :
    DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) t =
      GrowthTheoryTVC.marginalUtility δ γ c₀ g t * exp (r * t) := rfl

/-- Cochrane (2023), (6.1) p. 191 and (6.6) p. 199: along `c_t = c₀ e^{g t}` the first-order
condition of §6.2 (the marginal value is constant) holds iff `r` is the rate of §6.4.4,
`r = δ + γ g`. -/
theorem euler_iff_rate {c₀ : ℝ} (hc₀ : 0 < c₀) (δ γ r g : ℝ) :
    (∀ t, DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) t =
        DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) 0) ↔
      r = GrowthTheoryTVC.rate δ γ g :=
  DiscountGrowth.euler_exponential_iff hc₀ δ γ r g

/-- Cochrane (2023), p. 200 ("population growth `n` allows `r < g` more easily"): with
`r = δ + γ (g − n)`, `r < g` iff `δ + (γ − 1) g < γ n` (`DiscountGrowth.r_lt_g_population_iff`
for the rate of `GrowthTheoryTVC`). -/
theorem rate_population_lt_growth_iff (δ γ g n : ℝ) :
    GrowthTheoryTVC.rate δ γ (g - n) < g ↔ δ + (γ - 1) * g < γ * n :=
  DiscountGrowth.r_lt_g_population_iff rfl

/-! ### The transversality condition: §6.4.4 vs §6.4.1 -/

/-- Cochrane (2023), pp. 196 and 200: the growth-theory TVC term for debt `b_T = κ c_T` is
`c₀^{−γ}` times the §6.4.1 levels term `e^{−r T} b_T` with `r = (r − g) + g` and
`b_T = κ · c₀ e^{g T}`. -/
theorem growth_tvc_term_eq_levels {c₀ : ℝ} (hc : 0 < c₀) (δ γ g κ T : ℝ) :
    GrowthTheoryTVC.marginalUtility δ γ c₀ g T * (κ * GrowthTheoryTVC.consumption c₀ g T) =
      c₀ ^ (-γ) * (exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) := by
  rw [GrowthTheoryTVC.marginalUtility_eq hc, sub_add_cancel]
  unfold GrowthTheoryTVC.consumption
  ring

/-- Cochrane (2023), pp. 196 and 200: for debt in a steady positive ratio `κ` to output, the
§6.4.1 transversality condition in levels, `e^{−r T} b_T → 0`, holds iff `r > g`, exactly the
growth-theory condition `GrowthTheoryTVC.tvc_iff`. -/
theorem growth_tvc_iff_levels_tvc {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g : ℝ) :
    Tendsto (fun T => exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) atTop (𝓝 0) ↔ g < GrowthTheoryTVC.rate δ γ g := by
  have hp : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc _
  have e : ∀ T, exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) * (κ * (c₀ * exp (g * T))) =
      (c₀ ^ (-γ))⁻¹ * (GrowthTheoryTVC.marginalUtility δ γ c₀ g T *
        (κ * GrowthTheoryTVC.consumption c₀ g T)) := by
    intro T
    rw [growth_tvc_term_eq_levels hc]
    exact (inv_mul_cancel_left₀ hp.ne' _).symm
  rw [tendsto_congr e, ← GrowthTheoryTVC.tvc_iff hc hκ δ γ g]
  constructor
  · intro h
    have h2 := h.const_mul (c₀ ^ (-γ))
    rw [mul_zero] at h2
    exact h2.congr fun T => mul_inv_cancel_left₀ hp.ne' _
  · intro h
    have h2 := h.const_mul (c₀ ^ (-γ))⁻¹
    rwa [mul_zero] at h2

/-- Cochrane (2023), §6.4.1 p. 196 and §6.4.2 p. 198: debt held in a steady ratio `κ` solves
(6.4) with the steady surplus ratio `(r − g) κ`, and for `r > g` it equals the present value of
those surpluses. -/
theorem steady_debt_is_pv {κ δ γ g : ℝ} (h : g < GrowthTheoryTVC.rate δ γ g) :
    RvsG.SolvesOn (GrowthTheoryTVC.rate δ γ g - g)
        (fun _ => (GrowthTheoryTVC.rate δ γ g - g) * κ) (fun _ => κ) ∧
      κ = RvsG.pv (GrowthTheoryTVC.rate δ γ g - g)
        (fun _ => (GrowthTheoryTVC.rate δ γ g - g) * κ) 0 := by
  refine ⟨(RvsG.steady_state_iff _ _ _).2 rfl, ?_⟩
  rw [RvsG.pv_const (sub_pos.2 h)]
  exact (mul_div_cancel_left₀ κ (sub_pos.2 h).ne').symm

/-- Cochrane (2023), pp. 196 and 200: for `r > g` the growth-theory TVC for a steady debt ratio
follows from §6.4.1 alone (`RvsG.tvc_levels_iff` and `steady_debt_is_pv`), independently of
`GrowthTheoryTVC.tvc_iff`. -/
theorem growth_tvc_from_rvsg {c₀ κ δ γ g : ℝ} (hc : 0 < c₀)
    (h : g < GrowthTheoryTVC.rate δ γ g) :
    Tendsto (fun T => exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) atTop (𝓝 0) := by
  obtain ⟨hx, h0⟩ := steady_debt_is_pv (κ := κ) h
  exact (RvsG.tvc_levels_iff hc.ne' (sub_pos.2 h) continuous_const
    (M := |(GrowthTheoryTVC.rate δ γ g - g) * κ|) (fun _ => le_rfl) hx).2 h0

/-! ### Discrete debt dynamics: Theorem D (D5) vs Theorem S -/

/-- Cochrane (2023), (6.4) p. 196: the discrete debt/GDP recursion of `LinearODE` is a solution
of the discrete equation `RvsG.SolvesD` with `γ = (1 + r)/(1 + g)`. -/
theorem debt_gdp_solvesD {b y s : ℕ → ℝ} {r g : ℝ}
    (hb : ∀ t, b (t + 1) = (1 + r) * b t - s (t + 1))
    (hy : ∀ t, y (t + 1) = (1 + g) * y t) (hy0 : ∀ t, y t ≠ 0) (hg : 1 + g ≠ 0) :
    RvsG.SolvesD ((1 + r) / (1 + g)) (fun t => s (t + 1) / y (t + 1)) (fun t => b t / y t) :=
  fun t => LinearODE.debt_gdp_discrete hb hy hy0 hg t

/-- Cochrane (2023), (6.4) p. 196 and p. 197: every path of the stochastic debt ratio of
Theorem S solves the discrete equation (6.4) of `RvsG` (D5). -/
theorem debtPath_solvesD {Ω : Type*} (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (ω : Ω) :
    RvsG.SolvesD γ (fun t => σ t ω) (fun t => DebtLimitStochastic.debtPath γ x₀ σ t ω) :=
  RvsG.iterD_solves γ _ x₀

/-- Cochrane (2023), pp. 196–197 (D5 applied path by path): with `r < g` (`0 ≤ γ < 1`) and
surpluses bounded by `M` on a path, the debt ratio on that path stays within
`|x₀| + M/(1 − γ)`: bounded surpluses give the indeterminacy branch of Theorem D, never the
explosion of Theorem S. -/
theorem debtPath_abs_le {Ω : Type*} {γ x₀ M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} {ω : Ω} (hM : ∀ t, |σ t ω| ≤ M) (t : ℕ) :
    |DebtLimitStochastic.debtPath γ x₀ σ t ω| ≤ |x₀| + M / (1 - γ) :=
  RvsG.abs_le_of_lt_one hγ0 hγ1 hM (debtPath_solvesD γ x₀ σ ω) t

/-- Cochrane (2023), p. 197 vs p. 196: with `r < g` and i.i.d. Gaussian surpluses (truncated
above), almost every debt path is NOT bounded in the sense of `RvsG.BddD`, although every path
with bounded surpluses is (`debtPath_abs_le`): Theorem S lives outside Theorem D's hypotheses. -/
theorem gaussian_not_bddD {Ω : Type*} [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    {m : ℝ} {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map (σ 0) volume = gaussianReal m v) :
    ∀ᵐ ω, ¬ RvsG.BddD (fun t => DebtLimitStochastic.debtPath γ x₀ σ t ω) := by
  filter_upwards [DebtLimitStochastic.gaussian_iid_unbounded hγ0 hγ1 hσ hind hident hK hv
    hlaw] with ω hω
  rintro ⟨B, hB⟩
  obtain ⟨t, ht⟩ := (hω B).exists
  exact absurd ((le_abs_self _).trans (hB t)) (not_le.mpr ht)

/-! ### `r_f < g` with and without risk: Theorem D vs §6.4.7 -/

/-- Cochrane (2023), pp. 195–196 and 205–206: without growth risk (`σ² = 0`) the risk-free
rate is below growth iff the correct present-value ratio `β E[G^{1−γ}]` exceeds one, i.e. iff
the present value of a growing surplus diverges: the deterministic `r < g` of Theorem D. -/
theorem deterministic_rf_lt_g_iff (δ γ μ : ℝ) :
    riskFreeGross (exp (-δ)) γ (lognormalMoment μ 0) < lognormalMoment μ 0 1 ↔
      1 < exp (-δ) * lognormalMoment μ 0 (1 - γ) := by
  rw [AggregateUncertainty.riskFree_lt_growth_iff, AggregateUncertainty.lognormal_correct,
    AggregateUncertainty.incorrectExponent, Real.one_lt_exp_iff]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), pp. 196 and 205–206: under perfect foresight `r_f < g` rules out a finite
present value (`β E[G^{1−γ}] < 1` fails), but with lognormal growth risk (`σ² > 0`, `γ > 0`)
there are `μ` and `δ > 0` with a finite present value and `r_f < E[G]` (Bohn's case). -/
theorem rf_lt_g_pv_finite_needs_risk {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    (∀ δ μ, riskFreeGross (exp (-δ)) γ (lognormalMoment μ 0) < lognormalMoment μ 0 1 →
        ¬ exp (-δ) * lognormalMoment μ 0 (1 - γ) < 1) ∧
      ∃ μ δ, 0 < δ ∧ exp (-δ) * lognormalMoment μ v (1 - γ) < 1 ∧
        riskFreeGross (exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 :=
  ⟨fun δ μ h => not_lt.mpr ((deterministic_rf_lt_g_iff δ γ μ).1 h).le,
    AggregateUncertainty.bohn_region hγ hv⟩

end Cochrane.FiscalConstraints.Links

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

namespace Cochrane.FiscalConstraints.ExpectationsMeasure

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

end Cochrane.FiscalConstraints.ExpectationsMeasure

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

namespace Cochrane.FiscalConstraints.ExpectationsMeasureIID

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

end Cochrane.FiscalConstraints.ExpectationsMeasureIID

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregate uncertainty on a genuine i.i.d. growth process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207,
equations (6.15)–(6.18), re-proved on a genuine infinite-horizon probability space.

The state space is `Ω = ℕ → ℝ` with the product law `ν^ℕ` (`ExpectationsMeasureIID.iidSystem`),
the shocks are the coordinates `ε_t(ω) = ω_t`, and `𝓕_t = σ(ε_0, …, ε_t)`. Consumption is
`c_t = ∏_{i < t} g(ε_{i+1})` (`cons`), so growth `G_{t+1} = c_{t+1}/c_t = g(ε_{t+1})` is i.i.d.
with law `g_* ν`, positive, and has every moment `mom a = ∫ g^a dν` (`GrowthLaw`). Expectations
are Mathlib's conditional expectations, statements hold almost everywhere, and present values
are genuine infinite sums, both as sums of expectations and as the expectation of the infinite
sum (`condExp_tsum`).

## Main results

* `E_past_mul_future`: a date-`t` variable times a function of the future: integrable, and
  `E_t[X F] = X E[F]` (independence). `integral_ratioPow`: `E[(c_{t+j}/c_t)^a] = (mom a)^j`.
* `meas_iidGrowth` (the a.e. form of `AggregateUncertainty.IIDGrowth` at every date),
  `E_ratio_rpow_mul`.
* (6.15)/(6.16): `correct_term`, `incorrect_term`, `correct_pv_summable_iff`,
  `incorrect_pv_summable_iff`, `correct_finite_incorrect_explodes`, and the expectation of the
  infinite sum `E_tsum_correct_pv`.
* (6.17): `rollover_step`, `eq_6_17`, `terminal_c`, `pv_term_c`, `bohn_pv_hasSum_iff`, and
  `E_tsum_bohn_pv` (`c_t = E_t Σ_{j ≥ 1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`, a genuine expected
  infinite present value).
* (6.18): `eq_6_18`, `eq_6_18_diverges_ae`, `riskFree_prices`.
* The two-state Bohn example as an infinite i.i.d. coin process: `bohnG`, `bohnGrowthLaw`,
  `bohn_mom` (its moments are `AggregateUncertainty.bohnMom`), `bohn_infinite_witness`,
  `bohn_infinite_6_18`.
* Links: `MeasIIDGrowth.toCore` (the a.e. hypothesis gives the core `IIDGrowth` on a finite
  full-support system), `bohnTree_measIIDGrowth` (the coin tree satisfies it through
  `TreeBridge`), `link_correct_term`, `link_terminal_c`, `link_pv_term_c` (the infinite-process
  values equal the coin-tree values of `AggregateUncertainty`).
-/

namespace Cochrane.FiscalConstraints.AggregateUncertaintyMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID AggregateUncertainty

variable (ν : ProbabilityMeasure ℝ) (g : ℝ → ℝ)

/-- Cochrane (2023), p. 205: the law of i.i.d. growth `G = g(ε)`: `g` is measurable and positive,
and every power `G^a` has a finite mean. -/
structure GrowthLaw where
  /-- `g` is measurable. -/
  meas : Measurable g
  /-- growth is positive. -/
  pos : ∀ x, 0 < g x
  /-- every moment `E[G^a]` is finite. -/
  integrable : ∀ a : ℝ, Integrable (fun x => g x ^ a) (ν : Measure ℝ)

/-- Cochrane (2023), p. 205: consumption `c_t = ∏_{i < t} g(ε_{i+1})`, `c_0 = 1`. -/
noncomputable def cons (t : ℕ) (ω : ℕ → ℝ) : ℝ := ∏ i ∈ Finset.range t, g (ω (i + 1))

/-- Cochrane (2023), p. 205: the moments of growth, `mom a = E[G^a] = ∫ g^a dν`. -/
noncomputable def mom (a : ℝ) : ℝ := ∫ x, g x ^ a ∂(ν : Measure ℝ)

/-- Cochrane (2023), p. 205: the product `∏_{i < j} g(ε_{t+i+1})^a`, which is
`(c_{t+j}/c_t)^a` (`ratio_rpow`). -/
noncomputable def ratioPow (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Finset.range j, g (ω (t + i + 1)) ^ a

variable {ν g}

/-- Cochrane (2023), p. 205: consumption is positive. -/
theorem cons_pos (hG : GrowthLaw ν g) (t : ℕ) (ω : ℕ → ℝ) : 0 < cons g t ω :=
  Finset.prod_pos fun _ _ => hG.pos _

/-- Cochrane (2023), p. 205: `c_{t+j} = c_t ∏_{i<j} g(ε_{t+i+1})`. -/
theorem cons_add (t j : ℕ) (ω : ℕ → ℝ) :
    cons g (t + j) ω = cons g t ω * ∏ i ∈ Finset.range j, g (ω (t + i + 1)) := by
  unfold cons
  rw [Finset.prod_range_add]

/-- Cochrane (2023), p. 205: `c_0 = 1`. -/
theorem cons_zero (ω : ℕ → ℝ) : cons g 0 ω = 1 := by simp [cons]

/-- Cochrane (2023), p. 205: consumption growth is the i.i.d. factor, `G_{t+1} = g(ε_{t+1})`. -/
theorem growth_cons (hG : GrowthLaw ν g) (t : ℕ) (ω : ℕ → ℝ) :
    growth (cons g) t ω = g (ω (t + 1)) := by
  unfold growth
  rw [cons_add t 1 ω, Finset.prod_range_one, add_zero]
  field_simp [(cons_pos hG t ω).ne']

/-- Cochrane (2023), p. 205: `c_{t+j}/c_t = ∏_{i<j} g(ε_{t+i+1})`. -/
theorem ratio_cons (hG : GrowthLaw ν g) (t j : ℕ) (ω : ℕ → ℝ) :
    ratio (cons g) t j ω = ∏ i ∈ Finset.range j, g (ω (t + i + 1)) := by
  unfold ratio
  rw [cons_add]
  field_simp [(cons_pos hG t ω).ne']

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a = ∏_{i<j} g(ε_{t+i+1})^a`. -/
theorem ratio_rpow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) :
    ratio (cons g) t j ω ^ a = ratioPow g a t j ω := by
  rw [ratio_cons hG, ratioPow, Real.finsetProd_rpow _ _ (fun i _ => (hG.pos _).le)]

/-- Cochrane (2023), p. 205: `c_t^a = ∏_{i<t} g(ε_{i+1})^a`. -/
theorem cons_rpow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    cons g t ω ^ a = ratioPow g a 0 t ω := by
  have h := ratio_rpow hG a 0 t ω
  rwa [ratio, cons_zero, div_one, zero_add] at h

/-- Cochrane (2023), p. 205: one more period of growth, `ratioPow` recursion. -/
theorem ratioPow_succ (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) :
    ratioPow g a t (j + 1) ω = ratioPow g a t j ω * g (ω (t + j + 1)) ^ a := by
  rw [ratioPow, Finset.prod_range_succ]
  rfl

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a` is known at `t + j`. -/
theorem measurable_ratioPow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Measurable[(iidSystem ν).𝓕 (t + j)] (ratioPow g a t j) :=
  Finset.measurable_prod _ fun i hi => (hG.meas.pow_const a).comp
    (measurable_shock ν (by rw [Finset.mem_range] at hi; omega))

/-- Cochrane (2023), p. 205: consumption is known at `t`. -/
theorem measurable_cons (hG : GrowthLaw ν g) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (cons g t) :=
  Finset.measurable_prod _ fun i hi => hG.meas.comp
    (measurable_shock ν (by rw [Finset.mem_range] at hi; omega))

/-- Cochrane (2023), p. 205: the shock `ε_k` with `k > t` is measurable for the future. -/
theorem measurable_coord_future {t k : ℕ} (hk : t < k) :
    Measurable[futureSigma t] (fun ω : ℕ → ℝ => ω k) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Ioi t) => coordSigma i) k hk)

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a` depends only on shocks after `t`. -/
theorem measurable_ratioPow_future (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Measurable[futureSigma t] (ratioPow g a t j) :=
  Finset.measurable_prod _ fun _ _ => (hG.meas.pow_const a).comp
    (measurable_coord_future (by omega))

/-- Cochrane (2023), p. 205: a function of one shock with an integrable law is integrable. -/
theorem integrable_coord_fun {f : ℝ → ℝ} (hf : Integrable f (ν : Measure ℝ)) (k : ℕ) :
    Integrable (fun ω : ℕ → ℝ => f (ω k)) (iidSystem ν).μ :=
  (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) k).integrable_comp_of_integrable
    hf

variable (ν) in
/-- Cochrane (2023), p. 205: **independence of the past and the future**: a date-`t` variable
times a function of the shocks after `t` is integrable, its mean is the product of the means, and
`E_t[X F] = X E[F]` a.e. -/
theorem E_past_mul_future {t : ℕ} {X F : (ℕ → ℝ) → ℝ}
    (hX : StronglyMeasurable[(iidSystem ν).𝓕 t] X) (hF : StronglyMeasurable[futureSigma t] F)
    (hXi : Integrable X (iidSystem ν).μ) (hFi : Integrable F (iidSystem ν).μ) :
    Integrable (X * F) (iidSystem ν).μ ∧
      ∫ ω, (X * F) ω ∂(iidSystem ν).μ =
        (∫ ω, X ω ∂(iidSystem ν).μ) * ∫ ω, F ω ∂(iidSystem ν).μ ∧
      (iidSystem ν).E t (X * F) =ᵐ[(iidSystem ν).μ]
        X * fun _ => ∫ ω, F ω ∂(iidSystem ν).μ := by
  have hind : IndepFun X F (iidSystem ν).μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_future ν t).symm
      hX.measurable.comap_le) hF.measurable.comap_le
  have hint : Integrable (X * F) (iidSystem ν).μ := hind.integrable_mul hXi hFi
  refine ⟨hint, hind.integral_mul_eq_mul_integral hXi.1 hFi.1, ?_⟩
  refine (condExp_mul_of_stronglyMeasurable_left hX hint hFi).trans ?_
  filter_upwards [E_future ν t hF] with ω h
  simp only [Pi.mul_apply, h]

/-- Cochrane (2023), p. 205: **i.i.d. growth over `j` periods**: `(c_{t+j}/c_t)^a` is integrable
with mean `(mom a)^j`. -/
theorem integral_ratioPow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) :
    ∀ j, Integrable (ratioPow g a t j) (iidSystem ν).μ ∧
      ∫ ω, ratioPow g a t j ω ∂(iidSystem ν).μ = mom ν g a ^ j := by
  intro j
  induction j with
  | zero =>
    have h : ratioPow g a t 0 = fun _ => 1 := by funext ω; simp [ratioPow]
    rw [h]
    simp
  | succ j ih =>
    have hfun : ratioPow g a t (j + 1) =
        ratioPow g a t j * fun ω => g (ω (t + j + 1)) ^ a := by
      funext ω; rw [ratioPow_succ]; rfl
    have hF : StronglyMeasurable[futureSigma (t + j)] (fun ω : ℕ → ℝ => g (ω (t + j + 1)) ^ a) :=
      ((hG.meas.pow_const a).comp (measurable_coord_future (by omega))).stronglyMeasurable
    obtain ⟨h1, h2, -⟩ := E_past_mul_future ν (measurable_ratioPow hG a t j).stronglyMeasurable
      hF ih.1 (integrable_coord_fun (hG.integrable a) _)
    rw [hfun]
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, integral_shock_fun ν _ (hG.meas.pow_const a), pow_succ]
    rfl

/-- Cochrane (2023), p. 205: powers of consumption are integrable. -/
theorem integrable_cons_rpow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) :
    Integrable (fun ω => cons g t ω ^ a) (iidSystem ν).μ := by
  have h : (fun ω => cons g t ω ^ a) = ratioPow g a 0 t := funext (cons_rpow hG a t)
  rw [h]
  exact (integral_ratioPow hG a 0 t).1

/-- Cochrane (2023), (6.15) p. 205 (i.i.d. growth over `j` periods, a.e.):
`E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` integrable and known at `t`; the product is
integrable. -/
theorem E_ratio_rpow_mul (hG : GrowthLaw ν g) (a : ℝ) {t : ℕ} {X : (ℕ → ℝ) → ℝ}
    (hX : StronglyMeasurable[(iidSystem ν).𝓕 t] X) (hXi : Integrable X (iidSystem ν).μ)
    (j : ℕ) :
    Integrable (fun ω => ratio (cons g) t j ω ^ a * X ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => ratio (cons g) t j ω ^ a * X ω) =ᵐ[(iidSystem ν).μ]
        fun ω => mom ν g a ^ j * X ω := by
  have hfun : (fun ω => ratio (cons g) t j ω ^ a * X ω) = X * ratioPow g a t j := by
    funext ω; rw [ratio_rpow hG, Pi.mul_apply, mul_comm]
  obtain ⟨h1, -, h3⟩ := E_past_mul_future ν hX
    (measurable_ratioPow_future hG a t j).stronglyMeasurable hXi (integral_ratioPow hG a t j).1
  rw [hfun]
  refine ⟨h1, h3.trans (Eventually.of_forall fun ω => ?_)⟩
  simp only [Pi.mul_apply, (integral_ratioPow hG a t j).2]
  ring

/-- Cochrane (2023), p. 205: **the i.i.d. process has i.i.d. growth at every date** (the a.e.
form of `AggregateUncertainty.IIDGrowth`): `E_t[G_{t+1}^a] = mom a`. -/
theorem meas_iidGrowth (hG : GrowthLaw ν g) (t : ℕ) (a : ℝ) :
    (iidSystem ν).E t (fun ω => growth (cons g) t ω ^ a) =ᵐ[(iidSystem ν).μ]
      fun _ => mom ν g a := by
  have hfun : (fun ω => growth (cons g) t ω ^ a) =
      fun ω => ratio (cons g) t 1 ω ^ a * (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [growth_cons hG, ratio_cons hG, Finset.prod_range_one, add_zero, mul_one]
  rw [hfun]
  refine (E_ratio_rpow_mul hG a stronglyMeasurable_const (integrable_const 1) 1).2.trans ?_
  exact Eventually.of_forall fun ω => by simp


/-- Cochrane (2023), (6.15) p. 205: `E_t[(c_{t+j}/c_t)^a] = (mom a)^j` a.e., and the power is
integrable. -/
theorem E_ratio_rpow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Integrable (fun ω => ratio (cons g) t j ω ^ a) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => ratio (cons g) t j ω ^ a) =ᵐ[(iidSystem ν).μ]
        fun _ => mom ν g a ^ j := by
  have h := E_ratio_rpow_mul hG a (t := t) stronglyMeasurable_const (integrable_const 1) j
  simp only [mul_one] at h
  exact h

/-! ### A general lemma: expectation of an absolutely summable series -/

/-- Cochrane (2023), (6.15) p. 205 (genuine infinite horizon): if the terms `f_i` are integrable
and `Σ E|f_i| < ∞`, then the series converges absolutely almost surely and `E_t` passes through
the infinite sum, `E_t Σ f_i = Σ E_t f_i` a.e. (from Mathlib's `condExp_tsum`). -/
theorem E_tsum_of_summable_integral {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) {f : ℕ → Ω → ℝ} (hf : ∀ i, Integrable (f i) S.μ)
    (hs : Summable fun i => ∫ ω, |f i ω| ∂S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, Summable fun i => f i ω) ∧
      S.E t (fun ω => ∑' i, f i ω) =ᵐ[S.μ] fun ω => ∑' i, S.E t (f i) ω := by
  have hl : ∀ i, ∫⁻ ω, ‖f i ω‖ₑ ∂S.μ = ENNReal.ofReal (∫ ω, |f i ω| ∂S.μ) := fun i => by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf i)]
    simp only [Real.norm_eq_abs]
  have hne : ∑' i, ∫⁻ ω, ‖f i ω‖ₑ ∂S.μ ≠ ⊤ := by
    simp only [hl]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun ω => abs_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨?_, condExp_tsum (fun i => (hf i).1) hne⟩
  have hm : AEMeasurable (fun ω => ∑' i, ‖f i ω‖ₑ) S.μ :=
    AEMeasurable.tsum fun i => (hf i).1.enorm
  have hlt : ∫⁻ ω, ∑' i, ‖f i ω‖ₑ ∂S.μ ≠ ⊤ := by
    rw [lintegral_tsum fun i => (hf i).1.enorm]
    exact hne
  filter_upwards [ae_lt_top' hm hlt] with ω hω
  refine Summable.of_nnnorm ?_
  rw [← ENNReal.tsum_coe_ne_top_iff_summable]
  exact hω.ne

/-! ### (6.15) and (6.16) on the i.i.d. process -/

/-- Cochrane (2023), (6.15) p. 205: a constant surplus ratio's discounted term is integrable. -/
theorem integrable_pvTerm (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    Integrable (pvTerm β γ κ (cons g) t j) (iidSystem ν).μ := by
  have h : pvTerm β γ κ (cons g) t j =
      (β ^ j * κ) • fun ω => ratio (cons g) t j ω ^ (1 - γ) * (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t j ω),
      Real.rpow_one]
    ring
  rw [h]
  simp only [mul_one]
  exact (E_ratio_rpow hG (1 - γ) t j).1.smul _

/-- Cochrane (2023), (6.15) p. 205, a.e. on the i.i.d. process: the correct summands are
`E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ = (β mom(1−γ))^j κ`. -/
theorem correct_term (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    (iidSystem ν).E t (pvTerm β γ κ (cons g) t j) =ᵐ[(iidSystem ν).μ]
      fun _ => (β * mom ν g (1 - γ)) ^ j * κ := by
  have h : pvTerm β γ κ (cons g) t j =
      (β ^ j * κ) • fun ω => ratio (cons g) t j ω ^ (1 - γ) * (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t j ω),
      Real.rpow_one]
    ring
  rw [h]
  simp only [mul_one]
  refine ((iidSystem ν).E_smul _ _ t).trans ?_
  filter_upwards [(E_ratio_rpow hG (1 - γ) t j).2] with ω hω
  simp only [Pi.smul_apply, smul_eq_mul, hω, mul_pow]
  ring

/-- Cochrane (2023), (6.16) p. 205, a.e. on the i.i.d. process: the summands with the
expectation moved inside are `E_t[β^j (c_{t+j}/c_t)^{−γ}] E_t[c_{t+j}/c_t] κ =
(β mom(−γ) mom 1)^j κ`. -/
theorem incorrect_term (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (iidSystem ν).E t (fun ω' => β ^ j * ratio (cons g) t j ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t j) ω * κ =
        (β * mom ν g (-γ) * mom ν g 1) ^ j * κ := by
  have h1 : (fun ω' => β ^ j * ratio (cons g) t j ω' ^ (-γ)) =
      β ^ j • fun ω' => ratio (cons g) t j ω' ^ (-γ) := by
    funext ω'; simp
  have hb := (E_ratio_rpow hG 1 t j).2
  simp only [Real.rpow_one] at hb
  rw [h1]
  filter_upwards [(iidSystem ν).E_smul (β ^ j) _ t, (E_ratio_rpow hG (-γ) t j).2, hb]
    with ω hs ha hb'
  rw [hs, Pi.smul_apply, ha, hb', smul_eq_mul, mul_pow, mul_pow]

/-- Cochrane (2023), (6.15) p. 205, on the i.i.d. process: almost surely the correct present
value `Σ_{j≥1} E_t[...]` converges iff `|β mom(1−γ)| < 1` (for `κ ≠ 0`). -/
theorem correct_pv_summable_iff (hG : GrowthLaw ν g) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (Summable (fun j => (iidSystem ν).E t (pvTerm β γ κ (cons g) t (j + 1)) ω) ↔
        |β * mom ν g (1 - γ)| < 1) := by
  filter_upwards [ae_all_iff.2 fun j => correct_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  exact summable_geom_succ_iff hκ

/-- Cochrane (2023), (6.16) p. 205, on the i.i.d. process: almost surely the incorrect present
value converges iff `|β mom(−γ) mom 1| < 1` (for `κ ≠ 0`). -/
theorem incorrect_pv_summable_iff (hG : GrowthLaw ν g) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (Summable (fun j => (iidSystem ν).E t
          (fun ω' => β ^ (j + 1) * ratio (cons g) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t (j + 1)) ω * κ) ↔
        |β * mom ν g (-γ) * mom ν g 1| < 1) := by
  filter_upwards [ae_all_iff.2 fun j => incorrect_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  exact summable_geom_succ_iff hκ

/-- Cochrane (2023), p. 205 ("the true present value can converge while this mistaken one
explodes"), on the i.i.d. process: if `0 ≤ β mom(1−γ) < 1 ≤ β mom(−γ) mom 1` then almost surely
the correct present value (6.15) converges and the incorrect one (6.16) does not. -/
theorem correct_finite_incorrect_explodes (hG : GrowthLaw ν g) {β γ κ : ℝ} (hκ : κ ≠ 0)
    (hq0 : 0 ≤ β * mom ν g (1 - γ)) (hq1 : β * mom ν g (1 - γ) < 1)
    (hρ : 1 ≤ β * mom ν g (-γ) * mom ν g 1) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      Summable (fun j => (iidSystem ν).E t (pvTerm β γ κ (cons g) t (j + 1)) ω) ∧
      ¬ Summable (fun j => (iidSystem ν).E t
          (fun ω' => β ^ (j + 1) * ratio (cons g) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t (j + 1)) ω * κ) := by
  filter_upwards [correct_pv_summable_iff hG β γ hκ t, incorrect_pv_summable_iff hG β γ hκ t]
    with ω h1 h2
  rw [h1, h2, abs_of_nonneg hq0]
  refine ⟨hq1, fun h => ?_⟩
  have := le_abs_self (β * mom ν g (-γ) * mom ν g 1)
  linarith

/-- Cochrane (2023), p. 205: the moments of positive growth are positive. -/
theorem mom_pos (hG : GrowthLaw ν g) (a : ℝ) : 0 < mom ν g a := by
  unfold mom
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.rpow_pos_of_pos (hG.pos x) a).le)
    (hG.integrable a)]
  have hs : Function.support (fun x => g x ^ a) = Set.univ :=
    Set.eq_univ_of_forall fun x => (Real.rpow_pos_of_pos (hG.pos x) a).ne'
  rw [hs, measure_univ]
  exact one_pos

/-- **(6.15), genuine infinite horizon**, Cochrane (2023), p. 205: on the i.i.d. process with
`β ≥ 0` and `β mom(1−γ) < 1`, the discounted surplus stream `Σ_{j≥1} β^j (c_{t+j}/c_t)^{1−γ} κ`
converges almost surely and its conditional expectation is
`E_t Σ_{j≥1} (...) = Σ_{j≥1} E_t(...) = q κ/(1 − q)`, `q = β mom(1−γ)`. -/
theorem E_tsum_correct_pv (hG : GrowthLaw ν g) {β γ : ℝ} (κ : ℝ) (hβ : 0 ≤ β)
    (hq1 : β * mom ν g (1 - γ) < 1) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem ν).μ, Summable fun j => pvTerm β γ κ (cons g) t (j + 1) ω) ∧
      (iidSystem ν).E t (fun ω => ∑' j, pvTerm β γ κ (cons g) t (j + 1) ω)
        =ᵐ[(iidSystem ν).μ]
        fun _ => β * mom ν g (1 - γ) * κ / (1 - β * mom ν g (1 - γ)) := by
  set q := β * mom ν g (1 - γ) with hq
  have hq0 : 0 ≤ q := mul_nonneg hβ (mom_pos hG _).le
  have habs : ∀ j, ∫ ω, |pvTerm β γ κ (cons g) t (j + 1) ω| ∂(iidSystem ν).μ =
      q ^ (j + 1) * |κ| := fun j => by
    have hfun : (fun ω => |pvTerm β γ κ (cons g) t (j + 1) ω|) =
        fun ω => (β ^ (j + 1) * |κ|) * ratioPow g (1 - γ) t (j + 1) ω := by
      funext ω
      rw [← ratio_rpow hG, show (1 : ℝ) - γ = -γ + 1 by ring,
        Real.rpow_add (ratio_pos (cons_pos hG) t (j + 1) ω), Real.rpow_one, pvTerm, abs_mul,
        abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ _),
        abs_of_pos (Real.rpow_pos_of_pos (ratio_pos (cons_pos hG) t (j + 1) ω) _),
        abs_of_pos (ratio_pos (cons_pos hG) t (j + 1) ω)]
      ring
    rw [hfun, integral_const_mul, (integral_ratioPow hG (1 - γ) t (j + 1)).2, hq, mul_pow]
    ring
  have hsum : Summable fun j => ∫ ω, |pvTerm β γ κ (cons g) t (j + 1) ω| ∂(iidSystem ν).μ := by
    simp only [habs]
    exact ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)).mul_right _
  obtain ⟨hs, he⟩ := E_tsum_of_summable_integral (iidSystem ν)
    (fun j => integrable_pvTerm hG β γ κ t (j + 1)) hsum t
  refine ⟨hs, he.trans ?_⟩
  filter_upwards [ae_all_iff.2 fun j => correct_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  rw [tsum_mul_right]
  have h1 : ∑' j : ℕ, q ^ (j + 1) = q * (1 - q)⁻¹ := by
    simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    ring
  rw [h1]
  field_simp [(by linarith : (1 - q) ≠ 0)]

/-! ### (6.17) on the i.i.d. process -/

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: rolling debt over at the risk-free
rate, `β mom(−γ) R = 1`. For adapted debt `b` whose discounted value
`(c_{t+j}/c_t)^{−γ} b_{t+j}` is integrable, `β^{j+1}(c_{t+j+1}/c_t)^{−γ} R b_{t+j}` is integrable
and `E_t[D_{j+1} R b_{t+j}] = E_t[D_j b_{t+j}]` a.e. -/
theorem rollover_step (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {b : ℕ → (ℕ → ℝ) → ℝ} (hb : StronglyAdapted (iidSystem ν).𝓕 b) {t j : ℕ}
    (hbi : Integrable (fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω) (iidSystem ν).μ) :
    Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω))
        (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω))
        =ᵐ[(iidSystem ν).μ] (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω)
        := by
  set Y : (ℕ → ℝ) → ℝ := fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω with hY
  set F : (ℕ → ℝ) → ℝ := fun ω => g (ω (t + j + 1)) ^ (-γ) with hF
  have hYm : StronglyMeasurable[(iidSystem ν).𝓕 (t + j)] Y := by
    have h : Y = ratioPow g (-γ) t j * b (t + j) := by
      funext ω; simp only [hY, Pi.mul_apply]; rw [ratio_rpow hG]
    rw [h]
    exact (measurable_ratioPow hG (-γ) t j).stronglyMeasurable.mul (hb (t + j))
  have hFm : StronglyMeasurable[futureSigma (t + j)] F :=
    ((hG.meas.pow_const _).comp (measurable_coord_future (by omega))).stronglyMeasurable
  have hFi : Integrable F (iidSystem ν).μ := integrable_coord_fun (hG.integrable _) _
  have hFint : ∫ ω, F ω ∂(iidSystem ν).μ = mom ν g (-γ) :=
    integral_shock_fun ν _ (hG.meas.pow_const _)
  obtain ⟨hI, -, hE⟩ := E_past_mul_future ν hYm hFm hbi hFi
  have hL : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω)) =
      (β ^ (j + 1) * R) • (Y * F) := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hY, hF]
    rw [ratio_succ (cons_pos hG t ω).ne' (cons_pos hG (t + j) ω).ne',
      Real.mul_rpow (ratio_pos (cons_pos hG) t j ω).le
        (growth_pos (cons_pos hG) (t + j) ω).le, growth_cons hG]
    ring
  have hRt : (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω) = β ^ j • Y := by
    funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul, hY]; ring
  rw [hL, hRt]
  refine ⟨hI.smul _, ?_⟩
  have h1 : (iidSystem ν).E t (Y * F) =ᵐ[(iidSystem ν).μ] mom ν g (-γ) • (iidSystem ν).E t Y := by
    refine ((iidSystem ν).E_tower (Nat.le_add_right t j) (Y * F)).symm.trans ?_
    refine ((iidSystem ν).E_congr hE t).trans ?_
    have hfun : (Y * fun _ => ∫ ω, F ω ∂(iidSystem ν).μ) = mom ν g (-γ) • Y := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hFint]; ring
    rw [hfun]
    exact (iidSystem ν).E_smul _ _ t
  filter_upwards [(iidSystem ν).E_smul (β ^ (j + 1) * R) (Y * F) t, h1,
    (iidSystem ν).E_smul (β ^ j) Y t] with ω e1 e2 e3
  rw [e1, e3, Pi.smul_apply, e2]
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination β ^ j * (iidSystem ν).E t Y ω * hR

/-- **(6.17)**, Cochrane (2023), p. 207, on the i.i.d. process: if adapted debt `b` (with
integrable discounted values) is rolled over at the risk-free rate, `s_{u+1} = R b_u − b_{u+1}`,
`β mom(−γ) R = 1`, then for every horizon `T`, a.e.
`b_t = E_t Σ_{j=1}^T β^j (c_{t+j}/c_t)^{−γ} s_{t+j} + E_t[β^T (c_{t+T}/c_t)^{−γ} b_{t+T}]`. -/
theorem eq_6_17 (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {b s : ℕ → (ℕ → ℝ) → ℝ} (hb : StronglyAdapted (iidSystem ν).𝓕 b)
    (hs : ∀ u ω, s (u + 1) ω = R * b u ω - b (u + 1) ω) (t : ℕ)
    (hbi : ∀ j, Integrable (fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω) (iidSystem ν).μ)
    (T : ℕ) :
    b t =ᵐ[(iidSystem ν).μ]
      (iidSystem ν).E t (fun ω => ∑ j ∈ Finset.range T,
          pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) +
        (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t T ω * b (t + T) ω) := by
  have hDi : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω)
      (iidSystem ν).μ := fun j => by
    have h : (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω) =
        β ^ j • fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω := by
      funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
    rw [h]
    exact (hbi j).smul _
  have hterm : ∀ j, (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω)) -
        fun ω => pvDisc β γ (cons g) t (j + 1) ω * b (t + (j + 1)) ω := fun j => by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  have hti : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
      (iidSystem ν).μ := fun j => by
    rw [hterm j]
    exact (rollover_step hG hR hb (hbi j)).1.sub (hDi (j + 1))
  induction T with
  | zero =>
    have h0 : (fun ω => ∑ j ∈ Finset.range 0,
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) = 0 := by funext ω; simp
    have h1 : (fun ω => pvDisc β γ (cons g) t 0 ω * b (t + 0) ω) = b t := by
      funext ω; simp [pvDisc, ratio_zero (cons_pos hG t ω).ne']
    have hbt : Integrable (b t) (iidSystem ν).μ := by rw [← h1]; exact hDi 0
    rw [h0, h1, (iidSystem ν).E_zero, (iidSystem ν).E_of_stronglyMeasurable (hb t) hbt, zero_add]
  | succ T ih =>
    have hsplit : (fun ω => ∑ j ∈ Finset.range (T + 1),
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
        (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) +
          fun ω => pvDisc β γ (cons g) t (T + 1) ω * s (t + T + 1) ω := by
      funext ω; simp [Finset.sum_range_succ]
    have hSi : Integrable (fun ω => ∑ j ∈ Finset.range T,
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) (iidSystem ν).μ :=
      integrable_finsetSum _ fun j _ => hti j
    rw [hsplit]
    have hstep := (rollover_step hG hR hb (hbi T)).2
    have hsub := (iidSystem ν).E_sub (rollover_step hG hR hb (hbi T)).1 (hDi (T + 1)) t
    rw [← hterm T] at hsub
    filter_upwards [ih, (iidSystem ν).E_add hSi (hti T) t, hsub, hstep] with ω e0 e1 e2 e3
    rw [e0, Pi.add_apply, Pi.add_apply, e1, Pi.add_apply, e2, Pi.sub_apply, e3]
    ring

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: for debt `b = c`, the discounted
debt `(c_{t+j}/c_t)^{−γ} c_{t+j} = c_t (c_{t+j}/c_t)^{1−γ}` is integrable and
`E_t[β^T (c_{t+T}/c_t)^{−γ} c_{t+T}] = (β mom(1−γ))^T c_t` a.e. -/
theorem terminal_c (hG : GrowthLaw ν g) (β γ : ℝ) (t T : ℕ) :
    Integrable (fun ω => ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t T ω * cons g (t + T) ω)
        =ᵐ[(iidSystem ν).μ] fun ω => (β * mom ν g (1 - γ)) ^ T * cons g t ω := by
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hkey : ∀ ω, ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω =
      ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := fun ω => by
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t T ω),
      Real.rpow_one, ratio]
    field_simp [(cons_pos hG t ω).ne']
  obtain ⟨hI, hE⟩ := E_ratio_rpow_mul hG (1 - γ) (measurable_cons hG t).stronglyMeasurable hct T
  have h1 : (fun ω => ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω) =
      fun ω => ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := funext hkey
  refine ⟨h1 ▸ hI, ?_⟩
  have h : (fun ω => pvDisc β γ (cons g) t T ω * cons g (t + T) ω) =
      β ^ T • fun ω => ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, hkey]
  rw [h]
  filter_upwards [(iidSystem ν).E_smul (β ^ T) _ t, hE] with ω e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: each term of the present value of the
rollover surpluses `s_{u+1} = R c_u − c_{u+1}` is integrable, with
`E_t[β^{j+1}(c_{t+j+1}/c_t)^{−γ} s_{t+j+1}] = q^j (1 − q) c_t` a.e., `q = β mom(1−γ)`. -/
theorem pv_term_c (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {s : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω)
    (t j : ℕ) :
    Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ]
        fun ω => (β * mom ν g (1 - γ)) ^ j * (1 - β * mom ν g (1 - γ)) * cons g t ω := by
  have hca : StronglyAdapted (iidSystem ν).𝓕 (cons g) :=
    fun u => (measurable_cons hG u).stronglyMeasurable
  have hfun : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω)) -
        fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω := by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  obtain ⟨hI1, hE1⟩ := rollover_step hG hR hca (terminal_c hG β γ t j).1
  have hI2 : Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
      (iidSystem ν).μ := by
    have h : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω) =
        β ^ (j + 1) • fun ω => ratio (cons g) t (j + 1) ω ^ (-γ) * cons g (t + (j + 1)) ω := by
      funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
    rw [h]
    exact (terminal_c hG β γ t (j + 1)).1.smul _
  rw [hfun]
  refine ⟨hI1.sub hI2, ?_⟩
  filter_upwards [(iidSystem ν).E_sub hI1 hI2 t, hE1, (terminal_c hG β γ t j).2,
    (terminal_c hG β γ t (j + 1)).2] with ω e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, e4, pow_succ]
  ring

/-- Cochrane (2023), (6.17) p. 207: for `q ≥ 0` and `x > 0`, `Σ_j q^j (1 − q) x` has sum `x` iff
`q < 1`. -/
theorem hasSum_geom_iff {q x : ℝ} (hq0 : 0 ≤ q) (hx : 0 < x) :
    HasSum (fun j : ℕ => q ^ j * (1 - q) * x) x ↔ q < 1 := by
  constructor
  · intro h
    by_contra hq1
    push Not at hq1
    rcases hq1.eq_or_lt with h1 | h1
    · have h0 : HasSum (fun j : ℕ => q ^ j * (1 - q) * x) 0 := by
        rw [← h1]; simp
      have := h.unique h0
      linarith
    · have hlim := h.summable.tendsto_atTop_zero
      have hle : ∀ j : ℕ, q ^ j * (1 - q) * x ≤ (1 - q) * x := fun j => by
        have hp : 1 ≤ q ^ j := one_le_pow₀ h1.le
        have hneg : (1 - q) * x < 0 := mul_neg_of_neg_of_pos (by linarith) hx
        nlinarith
      have := le_of_tendsto' hlim hle
      nlinarith
  · intro hq1
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right ((1 - q) * x)
    have hval : (1 - q)⁻¹ * ((1 - q) * x) = x := by
      field_simp [(by linarith : (1 - q) ≠ 0)]
    rw [hval] at hg
    refine hg.congr_fun ?_
    intro j
    ring

/-- **(6.15) for Bohn's example**, Cochrane (2023), (6.17) p. 207, on the i.i.d. process: almost
surely, debt equal to consumption rolled over at the risk-free rate equals the sum of the
expected discounted surpluses, `Σ_{j≥1} E_t[β^j (c_{t+j}/c_t)^{−γ} s_{t+j}] = c_t`, iff
`β E[G^{1−γ}] < 1` (for `β ≥ 0`). -/
theorem bohn_pv_hasSum_iff (hG : GrowthLaw ν g) {β γ R : ℝ} (hβ : 0 ≤ β)
    (hR : β * mom ν g (-γ) * R = 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (HasSum (fun j => (iidSystem ν).E t
          (fun ω' => pvDisc β γ (cons g) t (j + 1) ω' * s (t + j + 1) ω') ω) (cons g t ω) ↔
        β * mom ν g (1 - γ) < 1) := by
  filter_upwards [ae_all_iff.2 fun j => (pv_term_c hG hR hs t j).2] with ω hω
  simp only [hω]
  exact hasSum_geom_iff (mul_nonneg hβ (mom_pos hG _).le) (cons_pos hG t ω)

/-- **(6.17), genuine infinite horizon**, Cochrane (2023), p. 207, on the i.i.d. process: with
`β > 0` and `β E[G^{1−γ}] < 1`, the discounted rollover surpluses
`Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}` converge absolutely almost surely and debt is the
conditional expectation of this infinite sum: `c_t = E_t Σ_{j≥1} (...)` a.e. -/
theorem E_tsum_bohn_pv (hG : GrowthLaw ν g) {β γ R : ℝ} (hβ : 0 < β)
    (hR : β * mom ν g (-γ) * R = 1) (hq1 : β * mom ν g (1 - γ) < 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem ν).μ,
        Summable fun j => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem ν).E t (fun ω => ∑' j, pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ] cons g t := by
  set q := β * mom ν g (1 - γ) with hq
  have hq0 : 0 ≤ q := mul_nonneg hβ.le (mom_pos hG _).le
  have hRpos : 0 < R := by
    have hm := mom_pos hG (-γ)
    by_contra h
    push Not at h
    have : β * mom ν g (-γ) * R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hβ hm).le h
    linarith
  have hca : StronglyAdapted (iidSystem ν).𝓕 (cons g) :=
    fun u => (measurable_cons hG u).stronglyMeasurable
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hDpos : ∀ j ω, 0 < pvDisc β γ (cons g) t j ω := fun j ω =>
    mul_pos (pow_pos hβ _) (Real.rpow_pos_of_pos (ratio_pos (cons_pos hG) t j ω) _)
  have hA : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω))
      (iidSystem ν).μ ∧ ∫ ω, pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω)
        ∂(iidSystem ν).μ = q ^ j * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    obtain ⟨hI, hE⟩ := rollover_step hG hR hca (terminal_c hG β γ t j).1
    refine ⟨hI, ?_⟩
    rw [← (iidSystem ν).integral_E t, integral_congr_ae (hE.trans (terminal_c hG β γ t j).2),
      integral_const_mul]
  have hB : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
      (iidSystem ν).μ ∧ ∫ ω, pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω
        ∂(iidSystem ν).μ = q ^ (j + 1) * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    have hI : Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
        (iidSystem ν).μ := by
      have h : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω) =
          β ^ (j + 1) • fun ω => ratio (cons g) t (j + 1) ω ^ (-γ) * cons g (t + (j + 1)) ω := by
        funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
      rw [h]
      exact (terminal_c hG β γ t (j + 1)).1.smul _
    refine ⟨hI, ?_⟩
    rw [← (iidSystem ν).integral_E t, integral_congr_ae (terminal_c hG β γ t (j + 1)).2,
      integral_const_mul]
  have hbound : ∀ j, ∫ ω, |pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω| ∂(iidSystem ν).μ
      ≤ (q ^ j + q ^ (j + 1)) * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    rw [add_mul, ← (hA j).2, ← (hB j).2, ← integral_add (hA j).1 (hB j).1]
    refine integral_mono ((pv_term_c hG hR hs t j).1.abs) ((hA j).1.add (hB j).1) fun ω => ?_
    rw [hs (t + j) ω, ← add_assoc, abs_mul, abs_of_pos (hDpos _ ω)]
    have h1 := hDpos (j + 1) ω
    have h2 := cons_pos hG (t + j) ω
    have h3 := cons_pos hG (t + j + 1) ω
    have h4 : |R * cons g (t + j) ω - cons g (t + j + 1) ω| ≤
        R * cons g (t + j) ω + cons g (t + j + 1) ω := by
      rw [abs_le]; constructor <;> nlinarith
    calc pvDisc β γ (cons g) t (j + 1) ω * |R * cons g (t + j) ω - cons g (t + j + 1) ω|
        ≤ pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω + cons g (t + j + 1) ω) :=
          mul_le_mul_of_nonneg_left h4 h1.le
      _ = _ := by ring
  have hsum : Summable fun j =>
      ∫ ω, |pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω| ∂(iidSystem ν).μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => abs_nonneg _) hbound ?_
    refine ((summable_geometric_of_lt_one hq0 hq1).add ?_).mul_right _
    exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)
  obtain ⟨hS, hE⟩ := E_tsum_of_summable_integral (iidSystem ν)
    (fun j => (pv_term_c hG hR hs t j).1) hsum t
  refine ⟨hS, hE.trans ?_⟩
  filter_upwards [ae_all_iff.2 fun j => (pv_term_c hG hR hs t j).2] with ω hω
  simp only [hω]
  exact ((hasSum_geom_iff hq0 (cons_pos hG t ω)).2 hq1).tsum_eq

/-! ### (6.18) and the risk-free rate on the i.i.d. process -/

/-- Cochrane (2023), p. 206, on the i.i.d. process: the risk-free rate prices the one-period
riskless bond, `E_t[β G_{t+1}^{−γ}] (1 + r) = 1` a.e. -/
theorem riskFree_prices (hG : GrowthLaw ν g) {β γ : ℝ} (hβ : β ≠ 0) (t : ℕ) :
    (iidSystem ν).E t (fun ω => β * growth (cons g) t ω ^ (-γ) * riskFreeGross β γ (mom ν g))
      =ᵐ[(iidSystem ν).μ] fun _ => 1 := by
  have hβm : β * mom ν g (-γ) ≠ 0 := mul_ne_zero hβ (mom_pos hG _).ne'
  have h : (fun ω => β * growth (cons g) t ω ^ (-γ) * riskFreeGross β γ (mom ν g)) =
      (β * riskFreeGross β γ (mom ν g)) • fun ω => growth (cons g) t ω ^ (-γ) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h]
  filter_upwards [(iidSystem ν).E_smul (β * riskFreeGross β γ (mom ν g)) _ t,
    meas_iidGrowth hG t (-γ)] with ω e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, riskFreeGross]
  field_simp
  exact div_self (mom_pos hG _).ne'

/-- **(6.18)**, Cochrane (2023), p. 207, on the i.i.d. process: discounting the rollover
surpluses at the risk-free rate `R ≠ 0`, a.e. the expected terminal term is
`E_t[R^{−T} c_{t+T}] = c_t (E[G]/R)^T` and the expected present value is
`E_t[Σ_{j=1}^T R^{−j} s_{t+j}] = c_t (1 − (E[G]/R)^T)`. -/
theorem eq_6_18 (hG : GrowthLaw ν g) {R : ℝ} (hR : R ≠ 0) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t T : ℕ) :
    (iidSystem ν).E t (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =ᵐ[(iidSystem ν).μ]
        (fun ω => cons g t ω * (mom ν g 1 / R) ^ T) ∧
      (iidSystem ν).E t (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ] fun ω => cons g t ω * (1 - (mom ν g 1 / R) ^ T) := by
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hkey : (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =
      (R⁻¹) ^ T • fun ω => ratio (cons g) t T ω ^ (1 : ℝ) * cons g t ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, Real.rpow_one, ratio]
    field_simp [(cons_pos hG t ω).ne']
  obtain ⟨hI, hE⟩ := E_ratio_rpow_mul hG 1 (measurable_cons hG t).stronglyMeasurable hct T
  have hterm : (iidSystem ν).E t (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =ᵐ[(iidSystem ν).μ]
      fun ω => cons g t ω * (mom ν g 1 / R) ^ T := by
    rw [hkey]
    filter_upwards [(iidSystem ν).E_smul ((R⁻¹) ^ T) _ t, hE] with ω e1 e2
    rw [e1, Pi.smul_apply, e2, smul_eq_mul, div_pow, inv_pow]
    field_simp
  refine ⟨hterm, ?_⟩
  have hfun : (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
      cons g t - fun ω => (R⁻¹) ^ T * cons g (t + T) ω := by
    funext ω
    rw [Pi.sub_apply, (eq_6_18_pathwise hR (cons_pos hG) hs t T ω).2]
  have hTi : Integrable (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) (iidSystem ν).μ := by
    rw [hkey]; exact hI.smul _
  rw [hfun]
  filter_upwards [(iidSystem ν).E_sub hct hTi t, hterm] with ω e1 e2
  rw [e1, Pi.sub_apply, (iidSystem ν).E_of_stronglyMeasurable
    (measurable_cons hG t).stronglyMeasurable hct, e2]
  ring

/-- **(6.18) on the i.i.d. process**, Cochrane (2023), p. 207 ("the present value of cashflows
term builds to negative infinity, and the terminal value builds to positive infinity"): if
`0 < R < E[G]` (`r < g`), then almost surely `E_t[Σ_{j=1}^T R^{−j} s_{t+j}] → −∞` and
`E_t[R^{−T} c_{t+T}] → +∞` as `T → ∞`. -/
theorem eq_6_18_diverges_ae (hG : GrowthLaw ν g) {R : ℝ} (hR0 : 0 < R) (hRg : R < mom ν g 1)
    {s : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      Tendsto (fun T => (iidSystem ν).E t
          (fun ω' => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem ν).E t
          (fun ω' => (R⁻¹) ^ T * cons g (t + T) ω') ω) atTop atTop := by
  have h := fun T => eq_6_18 hG hR0.ne' hs t T
  filter_upwards [ae_all_iff.2 fun T => (h T).1, ae_all_iff.2 fun T => (h T).2] with ω h1 h2
  simp only [h1, h2]
  obtain ⟨d1, d2⟩ := eq_6_18_diverges hR0 hRg (cons_pos hG t ω)
  exact ⟨d1, by simpa only [mul_comm] using d2⟩

/-! ### Bohn's two-state example as an infinite i.i.d. coin process -/

/-- Cochrane (2023), p. 206 (Bohn's example): growth driven by a fair `±1` coin,
`G = 5/4` on heads (`ε ≥ 0`) and `G = 17/20` on tails. -/
noncomputable def bohnG (x : ℝ) : ℝ := if 0 ≤ x then 5 / 4 else 17 / 20

/-- Cochrane (2023), p. 206: two-state coin growth is a growth law (measurable, positive,
bounded moments). -/
theorem bohnGrowthLaw : GrowthLaw coin bohnG where
  meas := by
    unfold bohnG
    exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
      measurable_const
  pos := fun x => by unfold bohnG; split_ifs <;> norm_num
  integrable := fun _ => by
    change Integrable _ coinMeasure
    unfold coinMeasure
    exact ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
      (by simp)

/-- Cochrane (2023), p. 206: the moments of the infinite coin process are the two-state moments
of `AggregateUncertainty`, `E[G^a] = ((5/4)^a + (17/20)^a)/2`. -/
theorem bohn_mom : mom coin bohnG = bohnMom := by
  funext a
  rw [mom, integral_coin]
  simp [bohnG, bohnMom, bohnGrowth]

/-- Cochrane (2023), p. 206: the risk-free rate `R = 361250/358288` satisfies
`β E[G^{−γ}] R = 1` for the coin process (`β = 49/50`, `γ = 2`). -/
theorem bohn_hR :
    (49 / 50 : ℝ) * mom coin bohnG (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
  rw [bohn_mom, riskFreeGross, bohnMom_values.2.2]
  norm_num

/-- Cochrane (2023), pp. 205–207 (**Theorem B on a genuine infinite i.i.d. process**): with
`β = 49/50`, `γ = 2`, growth `G ∈ {17/20, 5/4}` driven by i.i.d. fair coins on `ℕ → ℝ`, every
history has probability zero; the risk-free rate is below mean growth; for every `κ ≠ 0` the
correct present value converges and the incorrect one explodes a.s.; and debt equal to
consumption rolled over at the risk-free rate is the expectation of its infinite discounted
surplus stream, `c_t = E_t Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`, with the stream converging
a.s. -/
theorem bohn_infinite_witness {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω) (t : ℕ) :
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
    riskFreeGross (49 / 50) 2 (mom coin bohnG) < mom coin bohnG 1 ∧
    (∀ κ : ℝ, κ ≠ 0 → ∀ᵐ ω ∂(iidSystem coin).μ,
      Summable (fun j => (iidSystem coin).E t (pvTerm (49 / 50) 2 κ (cons bohnG) t (j + 1)) ω) ∧
      ¬ Summable (fun j => (iidSystem coin).E t
          (fun ω' => (49 / 50) ^ (j + 1) * ratio (cons bohnG) t (j + 1) ω' ^ (-2 : ℝ)) ω *
        (iidSystem coin).E t (ratio (cons bohnG) t (j + 1)) ω * κ)) ∧
    (∀ᵐ ω ∂(iidSystem coin).μ,
        Summable fun j => pvDisc (49 / 50) 2 (cons bohnG) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem coin).E t
          (fun ω => ∑' j, pvDisc (49 / 50) 2 (cons bohnG) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem coin).μ] cons bohnG t := by
  obtain ⟨-, hRm, hq, hq1, hρ⟩ := bohn_numbers
  rw [← bohn_mom] at hRm hq hq1 hρ
  have hρ' : 1 ≤ (49 / 50 : ℝ) * mom coin bohnG (-2) * mom coin bohnG 1 := hρ.le
  have hq0 : 0 ≤ (49 / 50 : ℝ) * mom coin bohnG (1 - 2) := by rw [hq]; norm_num
  refine ⟨iid_singleton coin_mean coin_var one_pos, by rw [bohn_mom] at hRm ⊢; exact hRm,
    fun κ hκ => correct_finite_incorrect_explodes bohnGrowthLaw hκ hq0 hq1 hρ' t, ?_⟩
  exact E_tsum_bohn_pv bohnGrowthLaw (by norm_num) bohn_hR hq1 hs t

/-- Cochrane (2023), (6.18) p. 207, **Bohn's example on the infinite coin process**: discounting
the rollover surpluses at the risk-free rate `R = 361250/358288 < E[G] = 21/20`, almost surely
the expected present value tends to `−∞` and the expected terminal value to `+∞`. -/
theorem bohn_infinite_6_18 {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      Tendsto (fun T => (iidSystem coin).E t (fun ω' => ∑ j ∈ Finset.range T,
          (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem coin).E t (fun ω' =>
          (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ T * cons bohnG (t + T) ω') ω) atTop atTop := by
  obtain ⟨hR, hRm, -, -, -⟩ := bohn_numbers
  have hR0 : 0 < riskFreeGross (49 / 50) 2 bohnMom := by rw [hR]; norm_num
  have hRm' : riskFreeGross (49 / 50) 2 bohnMom < mom coin bohnG 1 := by
    rw [bohn_mom]; exact hRm
  exact eq_6_18_diverges_ae bohnGrowthLaw hR0 hRm' hs t

/-! ### Links to the core and coin-tree versions -/

/-- Cochrane (2023), p. 205: **i.i.d. growth in the measure-theoretic setting** — for dates
`t < H`, `E_t[G_{t+1}^a] = m a` almost everywhere (the a.e. form of
`AggregateUncertainty.IIDGrowth`). -/
def MeasIIDGrowth {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (c : ℕ → Ω → ℝ) (m : ℝ → ℝ) (H : ℕ) : Prop :=
  ∀ t, t < H → ∀ a : ℝ, S.E t (fun ω => growth c t ω ^ a) =ᵐ[S.μ] fun _ => m a

/-- Cochrane (2023), p. 205 (**link to the core**): on a finite discrete state space with full
support, the a.e. hypothesis is exactly the core `IIDGrowth` of the bridged system, so every
core theorem of `AggregateUncertainty` applies to it. -/
theorem MeasIIDGrowth.toCore {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω} (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {c : ℕ → Ω → ℝ} {m : ℝ → ℝ} {H : ℕ} (h : MeasIIDGrowth S c m H) :
    IIDGrowth (S.toExpectationSystem hfull) c m H :=
  fun t ht a => S.eq_of_ae_eq hfull (h t ht a)

/-- Cochrane (2023), p. 205: the genuine i.i.d. process satisfies `MeasIIDGrowth` at every
horizon, with moments `mom a = ∫ g^a dν`. -/
theorem iid_measIIDGrowth (hG : GrowthLaw ν g) (H : ℕ) :
    MeasIIDGrowth (iidSystem ν) (cons g) (mom ν g) H :=
  fun t _ a => meas_iidGrowth hG t a

/-- Cochrane (2023), p. 206 (**link to the coin tree**): the coin tree `bohnTree H`, viewed as
a measure-theoretic system through `TreeBridge.treeSystem`, satisfies `MeasIIDGrowth` with the
same moments `bohnMom` as the infinite coin process (`bohn_mom`). -/
theorem bohnTree_measIIDGrowth (H : ℕ) :
    MeasIIDGrowth (ExpectationsMeasure.TreeBridge.treeSystem (bohnTree H)) (bohnC H) bohnMom H :=
  fun t ht a => by
    rw [ExpectationsMeasure.TreeBridge.treeSystem_E]
    have h := bohnSystem_iid H t ht a
    rw [bohnSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at h
    rw [h]

/-- Cochrane (2023), (6.15) p. 205 (**link**): for `j ≤ H`, the `j`-th correct summand of the
infinite coin process equals, almost surely, the `j`-th correct summand of the coin tree of
horizon `H` (both are `(4116/4250)^j κ`). -/
theorem link_correct_term {H j : ℕ} (hj : j ≤ H) (κ : ℝ) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (pvTerm (49 / 50) 2 κ (cons bohnG) 0 j) ω =
        (bohnSystem H).E 0 (pvTerm (49 / 50) 2 κ (bohnC H) 0 j) ω' := by
  filter_upwards [correct_term bohnGrowthLaw (49 / 50) 2 κ 0 j] with ω h
  rw [h, (bohn_witness_terms hj κ ω').1, bohn_mom, bohn_numbers.2.2.1]

/-- Cochrane (2023), (6.17) p. 207 (**link**): for `T ≤ H`, the expected terminal term of the
infinite coin process equals, almost surely, the coin-tree value (both are `(4116/4250)^T`). -/
theorem link_terminal_c {H T : ℕ} (hT : T ≤ H) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (fun ω => pvDisc (49 / 50) 2 (cons bohnG) 0 T ω * cons bohnG (0 + T) ω)
          ω =
        (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) ω'
        := by
  have hcore := AggregateUncertainty.terminal_c (bohnSystem H) (bohnSystem_pullOut H)
    (bohnC_pos H) (bohnSystem_knownPowers H) (bohnSystem_iid H) (49 / 50) 2 (t := 0) (T := T)
    (by omega)
  filter_upwards [(AggregateUncertaintyMeasure.terminal_c bohnGrowthLaw (49 / 50) 2 0 T).2]
    with ω h
  rw [h, hcore, bohn_mom, cons_zero]
  simp [bohnC]

/-- Cochrane (2023), (6.17) p. 207 (**link**): for `j + 1 ≤ H`, each expected discounted
rollover surplus of the infinite coin process equals, almost surely, the coin-tree value (both
are `q^j (1 − q)` with `q = 4116/4250`, `c_0 = 1`). -/
theorem link_pv_term_c {H j : ℕ} (hj : j + 1 ≤ H) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω)
    {s' : ℕ → (Fin H → Bool) → ℝ}
    (hs' : ∀ u ω, s' (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (fun ω => pvDisc (49 / 50) 2 (cons bohnG) 0 (j + 1) ω * s (0 + j + 1) ω)
          ω =
        (bohnSystem H).E 0
          (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 (j + 1) ω * s' (0 + j + 1) ω) ω' := by
  have hRc : (49 / 50 : ℝ) * bohnMom (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
    rw [riskFreeGross, bohnMom_values.2.2]; norm_num
  have hcore := AggregateUncertainty.pv_term_c (bohnSystem H) (bohnSystem_pullOut H)
    (bohnC_pos H) (bohnSystem_knownPowers H) (bohnSystem_iid H) hRc hs' (t := 0) (j := j)
    (by omega)
  filter_upwards [(AggregateUncertaintyMeasure.pv_term_c bohnGrowthLaw bohn_hR hs 0 j).2]
    with ω h
  rw [h, hcore, bohn_mom, cons_zero]
  simp [bohnC]

end Cochrane.FiscalConstraints.AggregateUncertaintyMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A genuine lognormal i.i.d. growth process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207
(lognormal consumption growth, Bohn's example, (6.15)–(6.18)).

The process: `ε_t` i.i.d. `N(μ, v)` on `Ω = ℕ → ℝ` (`ν = gaussianReal μ v`, product law
`ν^ℕ`), consumption `c_t = exp(ε_1 + ⋯ + ε_t)`, so log growth `log G_{t+1} = ε_{t+1}` is
i.i.d. normal and growth `G_{t+1} = exp ε_{t+1}` is i.i.d. with the lognormal law
`lognormalLaw μ v = exp_* N(μ, v)`. Every lognormal result of `AggregateUncertainty` (which
were statements about the numbers `lognormalMoment`) is proved here about this process, with
Mathlib conditional expectations, almost surely.

## Main results

* The process: `gaussianProb`, `lognormalGrowthLaw`, `lognormalLaw`, `map_growth`
  (each `G_{t+1}` has the lognormal law), `map_log_growth` (log growth is `N(μ, v)`),
  `iIndepFun_growth` (growth rates are independent), `lognormal_mom`
  (`E[G^a] = e^{aμ + v a²/2}`), `lognormal_E_growth`.
* (6.15)/(6.16) on the process: `lognormal_correct_term`, `lognormal_incorrect_term` (the
  corrected exponent `(γ² + 1) v/2`), `lognormal_printed_incorrect_wrong` (the printed exponent is
  wrong for the process), `lognormal_correct_pv_summable_iff`,
  `lognormal_incorrect_pv_summable_iff`.
* `lognormal_region_iff`: there are `μ, δ` making the correct present value converge and the
  incorrect one explode a.s. on the process iff `γ > 0`; `lognormal_bohn_region` adds
  `δ > 0` and `r_f < g`.
* (6.17)/(6.18) on the process: `lognormal_riskFree_prices`, `lognormal_log_riskFree`,
  `lognormal_E_tsum_bohn_pv` (`c_t = E_t Σ_{j≥1} (...)`), `lognormal_eq_6_18_diverges`.
-/

namespace Cochrane.FiscalConstraints.LognormalGrowthMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID AggregateUncertaintyMeasure
open AggregateUncertainty (growth ratio pvTerm pvDisc riskFreeGross lognormalMoment
  correctExponent incorrectExponent)

/-- Cochrane (2023), p. 205: the normal law `N(μ, v)` of log growth, as a probability measure. -/
noncomputable def gaussianProb (μ : ℝ) (v : NNReal) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal μ v, inferInstance⟩

/-- Cochrane (2023), p. 205: the lognormal law of growth, `exp_* N(μ, v)`. -/
noncomputable def lognormalLaw (μ : ℝ) (v : NNReal) : Measure ℝ :=
  (gaussianReal μ v).map Real.exp

/-- Cochrane (2023), p. 205: `G = exp ε` with `ε ~ N(μ, v)` is a growth law: measurable,
positive, and every moment `E[G^a] = E[e^{aε}]` is finite (Gaussian moment generating
function). -/
theorem lognormalGrowthLaw (μ : ℝ) (v : NNReal) : GrowthLaw (gaussianProb μ v) Real.exp where
  meas := Real.measurable_exp
  pos := Real.exp_pos
  integrable := fun a => by
    have h : (fun x => Real.exp x ^ a) = fun x => Real.exp (a * x) := by
      funext x; rw [← Real.exp_mul, mul_comm]
    rw [h]
    exact integrable_exp_mul_gaussianReal a

/-- Cochrane (2023), p. 205: the moments of the lognormal process are the lognormal moments,
`E[G^a] = e^{aμ + v a²/2}`. -/
theorem lognormal_mom (μ : ℝ) (v : NNReal) :
    mom (gaussianProb μ v) Real.exp = lognormalMoment μ v := by
  funext a
  exact AggregateUncertainty.lognormalMoment_eq_integral μ v a

/-- Cochrane (2023), p. 205: consumption is `c_t = exp(ε_1 + ⋯ + ε_t)`. -/
theorem cons_exp (t : ℕ) (ω : ℕ → ℝ) :
    cons Real.exp t ω = Real.exp (∑ i ∈ Finset.range t, ω (i + 1)) := by
  rw [cons, Real.exp_sum]

/-- Cochrane (2023), p. 205: **log growth is i.i.d. normal**: `log G_{t+1} = ε_{t+1}`, whose law
is `N(μ, v)`. -/
theorem map_log_growth (μ : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (fun ω => Real.log (growth (cons Real.exp) t ω)) (iidSystem (gaussianProb μ v)).μ
      = gaussianReal μ v := by
  have h : (fun ω : ℕ → ℝ => Real.log (growth (cons Real.exp) t ω)) = fun ω => ω (t + 1) := by
    funext ω
    rw [growth_cons (lognormalGrowthLaw μ v), Real.log_exp]
  rw [h]
  exact Measure.infinitePi_map_eval _ (t + 1)

/-- Cochrane (2023), p. 205: **each growth rate has the lognormal law**,
`G_{t+1} ~ exp_* N(μ, v)`. -/
theorem map_growth (μ : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (fun ω => growth (cons Real.exp) t ω) (iidSystem (gaussianProb μ v)).μ =
      lognormalLaw μ v := by
  have h : (fun ω : ℕ → ℝ => growth (cons Real.exp) t ω) =
      Real.exp ∘ fun ω => ω (t + 1) := by
    funext ω
    rw [growth_cons (lognormalGrowthLaw μ v)]
    rfl
  rw [h, ← Measure.map_map Real.measurable_exp (measurable_pi_apply (t + 1))]
  change Measure.map Real.exp (Measure.map (fun ω : ℕ → ℝ => ω (t + 1))
    (Measure.infinitePi fun _ => gaussianReal μ v)) = _
  rw [Measure.infinitePi_map_eval]
  rfl

/-- Cochrane (2023), p. 205: **the growth rates are mutually independent**, so
`(G_{t+1})_t` is an i.i.d. lognormal sequence. -/
theorem iIndepFun_growth (μ : ℝ) (v : NNReal) :
    iIndepFun (fun t ω => growth (cons Real.exp) t ω) (iidSystem (gaussianProb μ v)).μ := by
  have h0 : iIndepFun (fun i (ω : ℕ → ℝ) => Real.exp (ω i))
      (Measure.infinitePi fun _ => gaussianReal μ v) :=
    iIndepFun_infinitePi (P := fun _ => gaussianReal μ v) (X := fun _ => Real.exp)
      (fun _ => Real.measurable_exp)
  have h1 := h0.precomp (g := fun t => t + 1) (fun a b h => by simpa using h)
  have h : (fun t ω => growth (cons Real.exp) t ω) = fun t (ω : ℕ → ℝ) => Real.exp (ω (t + 1)) := by
    funext t ω
    rw [growth_cons (lognormalGrowthLaw μ v)]
  rw [h]
  exact h1

/-- Cochrane (2023), p. 205: on the lognormal process, `E_t[G_{t+1}^a] = e^{aμ + v a²/2}` a.e. -/
theorem lognormal_E_growth (μ : ℝ) (v : NNReal) (t : ℕ) (a : ℝ) :
    (iidSystem (gaussianProb μ v)).E t (fun ω => growth (cons Real.exp) t ω ^ a)
      =ᵐ[(iidSystem (gaussianProb μ v)).μ] fun _ => lognormalMoment μ v a := by
  rw [← lognormal_mom]
  exact meas_iidGrowth (lognormalGrowthLaw μ v) t a

/-- Cochrane (2023), (6.15) p. 205, on the lognormal process with `β = e^{−δ}`: the correct
summands are `E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ = (e^{A})^j κ`, `A = −δ + (1−γ)μ + (1−γ)² v/2`. -/
theorem lognormal_correct_term (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t j : ℕ) :
    (iidSystem (gaussianProb μ v)).E t (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t j)
      =ᵐ[(iidSystem (gaussianProb μ v)).μ]
      fun _ => Real.exp (correctExponent δ γ μ v) ^ j * κ := by
  filter_upwards [correct_term (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ κ t j] with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_correct, correctExponent]

/-- Cochrane (2023), (6.16) p. 206 (corrected), on the lognormal process: the summands with the
expectation inside are `(e^{B})^j κ`, `B = −δ + (1−γ)μ + (γ² + 1) v/2`. -/
theorem lognormal_incorrect_term (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t j : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (iidSystem (gaussianProb μ v)).E t
          (fun ω' => Real.exp (-δ) ^ j * ratio (cons Real.exp) t j ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t j) ω * κ =
        Real.exp (incorrectExponent δ γ μ v) ^ j * κ := by
  filter_upwards [incorrect_term (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ κ t j] with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_incorrect, incorrectExponent]

/-- Cochrane (2023), p. 206 (**error in the book, on the process**): for `v ≠ 0`, the product of
the one-period forecasts `E_t[G^{−γ}] E_t[G]` is a.s. not the printed `e^{(1−γ)μ + γ² v/2}`. -/
theorem lognormal_printed_incorrect_wrong (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (γ : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (iidSystem (gaussianProb μ v)).E t (fun ω' => growth (cons Real.exp) t ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (fun ω' => growth (cons Real.exp) t ω' ^ (1 : ℝ)) ω ≠
        Real.exp ((1 - γ) * μ + γ ^ 2 * v / 2) := by
  filter_upwards [lognormal_E_growth μ v t (-γ), lognormal_E_growth μ v t 1] with ω h1 h2
  rw [h1, h2]
  exact AggregateUncertainty.printed_incorrect_wrong γ μ (by exact_mod_cast hv)

/-- Cochrane (2023), (6.15) p. 205, on the lognormal process: almost surely the correct present
value converges iff `A = −δ + (1−γ)μ + (1−γ)² v/2 < 0` (for `κ ≠ 0`). -/
theorem lognormal_correct_pv_summable_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Summable (fun j => (iidSystem (gaussianProb μ v)).E t
          (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t (j + 1)) ω) ↔
        correctExponent δ γ μ v < 0) := by
  filter_upwards [correct_pv_summable_iff (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ hκ t]
    with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_correct, abs_of_pos (Real.exp_pos _),
    Real.exp_lt_one_iff, correctExponent]

/-- Cochrane (2023), (6.16) p. 206 (corrected), on the lognormal process: almost surely the
incorrect present value converges iff `B = −δ + (1−γ)μ + (γ² + 1) v/2 < 0` (for `κ ≠ 0`). -/
theorem lognormal_incorrect_pv_summable_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ}
    (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Summable (fun j => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => Real.exp (-δ) ^ (j + 1) * ratio (cons Real.exp) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t (j + 1)) ω * κ) ↔
        incorrectExponent δ γ μ v < 0) := by
  filter_upwards [incorrect_pv_summable_iff (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ hκ t]
    with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_incorrect, abs_of_pos (Real.exp_pos _),
    Real.exp_lt_one_iff, incorrectExponent]

/-- Cochrane (2023), p. 206: the event "the correct present value (6.15) converges and the
incorrect one (6.16) does not" on the lognormal process. -/
def Explodes (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : Prop :=
  Summable (fun j => (iidSystem (gaussianProb μ v)).E t
      (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t (j + 1)) ω) ∧
    ¬ Summable (fun j => (iidSystem (gaussianProb μ v)).E t
        (fun ω' => Real.exp (-δ) ^ (j + 1) * ratio (cons Real.exp) t (j + 1) ω' ^ (-γ)) ω *
      (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t (j + 1)) ω * κ)

/-- Cochrane (2023), p. 206, on the lognormal process: almost surely, the correct present value
converges while the incorrect one explodes iff `A < 0 ≤ B`. -/
theorem lognormal_explodes_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Explodes μ v δ γ κ t ω ↔
        correctExponent δ γ μ v < 0 ∧ 0 ≤ incorrectExponent δ γ μ v) := by
  filter_upwards [lognormal_correct_pv_summable_iff μ v δ γ hκ t,
    lognormal_incorrect_pv_summable_iff μ v δ γ hκ t] with ω h1 h2
  rw [Explodes, h1, h2, not_lt]

/-- Cochrane (2023), p. 206 (corrected; "it is entirely possible", **on the lognormal process**):
for `v = σ² > 0` and `κ ≠ 0`, there are a mean log growth `μ` and a discount rate `δ` such that,
almost surely, the correct present value converges and the incorrect one explodes, iff
`γ > 0`. -/
theorem lognormal_region_iff (γ : ℝ) {v : NNReal} (hv : v ≠ 0) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    (∃ μ δ, ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ, Explodes μ v δ γ κ t ω) ↔ 0 < γ := by
  have hv' : (0 : ℝ) < v := by
    have h := pos_iff_ne_zero.2 hv
    exact_mod_cast h
  constructor
  · rintro ⟨μ, δ, h⟩
    obtain ⟨ω, h1, h2⟩ := (h.and (lognormal_explodes_iff μ v δ γ hκ t)).exists
    obtain ⟨hA, hB⟩ := h2.1 h1
    simp only [correctExponent, incorrectExponent] at hA hB
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    obtain ⟨μ, δ, -, hA, hB⟩ := AggregateUncertainty.region_pos_delta hγ hv'
    refine ⟨μ, δ, ?_⟩
    filter_upwards [lognormal_explodes_iff μ v δ γ hκ t] with ω h
    exact h.2 ⟨hA, hB.le⟩

/-- Cochrane (2023), pp. 205–206 (**Theorem B, lognormal form, on the process**): for every
`γ > 0` and `v > 0` there are `μ` and `δ > 0` such that on the lognormal process the risk-free
rate is below mean growth and, almost surely, the correct present value converges while the
incorrect one explodes. -/
theorem lognormal_bohn_region {γ : ℝ} (hγ : 0 < γ) {v : NNReal} (hv : v ≠ 0) {κ : ℝ}
    (hκ : κ ≠ 0) (t : ℕ) :
    ∃ μ δ, 0 < δ ∧
      riskFreeGross (Real.exp (-δ)) γ (mom (gaussianProb μ v) Real.exp) <
        mom (gaussianProb μ v) Real.exp 1 ∧
      ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ, Explodes μ v δ γ κ t ω := by
  have hv' : (0 : ℝ) < v := by
    have h := pos_iff_ne_zero.2 hv
    exact_mod_cast h
  obtain ⟨μ, δ, hδ, hA, hB⟩ := AggregateUncertainty.region_pos_delta hγ hv'
  refine ⟨μ, δ, hδ, ?_, ?_⟩
  · rw [lognormal_mom]
    exact (AggregateUncertainty.riskFree_lt_growth_iff δ γ μ v).2 hB
  · filter_upwards [lognormal_explodes_iff μ v δ γ hκ t] with ω h
    exact h.2 ⟨hA, hB.le⟩

/-- Cochrane (2023), p. 206, on the lognormal process: the risk-free rate prices the riskless
bond, `E_t[e^{−δ} G_{t+1}^{−γ}] (1 + r_f) = 1` a.e. -/
theorem lognormal_riskFree_prices (μ : ℝ) (v : NNReal) (δ γ : ℝ) (t : ℕ) :
    (iidSystem (gaussianProb μ v)).E t (fun ω => Real.exp (-δ) * growth (cons Real.exp) t ω ^ (-γ) *
        riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v))
      =ᵐ[(iidSystem (gaussianProb μ v)).μ] fun _ => 1 := by
  rw [← lognormal_mom]
  exact riskFree_prices (lognormalGrowthLaw μ v) (Real.exp_pos _).ne' t

/-- Cochrane (2023), p. 206 (Bohn's risk-free rate, corrected, for the process):
`log(1 + r_f) = δ + γ μ − γ² v/2`. -/
theorem lognormal_log_riskFree (μ : ℝ) (v : NNReal) (δ γ : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (mom (gaussianProb μ v) Real.exp)) =
      δ + γ * μ - γ ^ 2 * v / 2 := by
  rw [lognormal_mom]
  exact AggregateUncertainty.log_riskFree_lognormal δ γ μ v

/-- **(6.17), genuine infinite horizon, lognormal process**, Cochrane (2023), p. 207: with
`β = e^{−δ}` and `A = −δ + (1−γ)μ + (1−γ)² v/2 < 0`, debt equal to consumption rolled over at
the risk-free rate is the conditional expectation of its infinite discounted surplus stream,
which converges a.s.: `c_t = E_t Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`. -/
theorem lognormal_E_tsum_bohn_pv (μ : ℝ) (v : NNReal) {δ γ : ℝ}
    (hA : correctExponent δ γ μ v < 0) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) *
      cons Real.exp u ω - cons Real.exp (u + 1) ω) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
        Summable fun j => pvDisc (Real.exp (-δ)) γ (cons Real.exp) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem (gaussianProb μ v)).E t
          (fun ω => ∑' j, pvDisc (Real.exp (-δ)) γ (cons Real.exp) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem (gaussianProb μ v)).μ] cons Real.exp t := by
  have hR : Real.exp (-δ) * mom (gaussianProb μ v) Real.exp (-γ) *
      riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) = 1 := by
    rw [lognormal_mom, riskFreeGross]
    have : Real.exp (-δ) * lognormalMoment μ v (-γ) ≠ 0 :=
      mul_ne_zero (Real.exp_pos _).ne' (Real.exp_pos _).ne'
    field_simp
    exact div_self (by unfold lognormalMoment; exact (Real.exp_pos _).ne')
  have hq : Real.exp (-δ) * mom (gaussianProb μ v) Real.exp (1 - γ) < 1 := by
    rw [lognormal_mom, AggregateUncertainty.lognormal_correct, Real.exp_lt_one_iff]
    exact hA
  exact E_tsum_bohn_pv (lognormalGrowthLaw μ v) (Real.exp_pos _) hR hq hs t

/-- **(6.18) on the lognormal process**, Cochrane (2023), p. 207 ("the present value of
cashflows term builds to negative infinity, and the terminal value builds to positive
infinity"): if `0 < R < E[G]` (`r < g`), then almost surely
`E_t[Σ_{j=1}^T R^{−j} s_{t+j}] → −∞` and `E_t[R^{−T} c_{t+T}] → +∞` as `T → ∞`. -/
theorem lognormal_eq_6_18_diverges (μ : ℝ) (v : NNReal) {R : ℝ} (hR0 : 0 < R)
    (hRg : R < lognormalMoment μ v 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons Real.exp u ω - cons Real.exp (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      Tendsto (fun T => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => (R⁻¹) ^ T * cons Real.exp (t + T) ω') ω) atTop atTop := by
  have h := fun T => eq_6_18 (lognormalGrowthLaw μ v) hR0.ne' hs t T
  filter_upwards [ae_all_iff.2 fun T => (h T).1, ae_all_iff.2 fun T => (h T).2] with ω h1 h2
  simp only [h1, h2, lognormal_mom]
  obtain ⟨d1, d2⟩ := AggregateUncertainty.eq_6_18_diverges hR0 hRg
    (cons_pos (lognormalGrowthLaw μ v) t ω)
  exact ⟨d1, by simpa only [mul_comm] using d2⟩

end Cochrane.FiscalConstraints.LognormalGrowthMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Debt limits with genuine i.i.d. surplus processes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, pp. 196–197.

The surplus ratios are the coordinates `σ_t(ω) = ω_t` of the i.i.d. product space
`(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID` (law `ν` at every date), with the natural filtration.
The debt ratio `x_{t+1} = γ x_t − σ_t` (`DebtLimitStochastic.debtPath`) is then an adapted
process on a genuine infinite-horizon probability space.

## Main results

* `debtPath_adapted`: the debt ratio `x_{t+1}` is known at `t`.
* `iid_frequently_exceeds`, `iid_not_sustainable` (**Theorem S on the i.i.d. process**, second
  Borel–Cantelli lemma): for any law `ν` bounded above with `ν(−∞, −c] > 0`.
* `iid_unbounded_core`: the core `DebtLimitStochastic.iid_unbounded` applied to the process.
* `coin_debt_dichotomy` (the bounded-support correction on a genuine process): with fair `±1`
  coin surpluses, debt a.s. never exceeds `max x₀ (1/(1 − γ))`, yet a.s. exceeds every
  `M < 1/(1 − γ)` infinitely often.
* `gaussian_not_ae_bounded_above`, `gaussian_iid_unbounded_vacuous` (**correction**): a
  non-degenerate Gaussian surplus is not a.s. bounded above, so the hypotheses of
  `DebtLimitStochastic.gaussian_iid_unbounded` can never hold; that theorem is vacuous.
* `iid_unbounded_of_integrable` (the corrected theorem, **no upper bound needed**): for i.i.d.
  integrable surpluses with deficits of every size, the debt ratio is a.s. unbounded above. The
  proof uses Markov's inequality, independence of `σ_{t+1}` from `𝓕_t`, and Kolmogorov's 0-1 law.
* `gaussian_process_unbounded`, `gaussian_process_not_sustainable`: **i.i.d. Gaussian surpluses
  as a process** make the debt ratio a.s. unbounded above, so no debt limit is sustainable.
* `managed_adapted`, `managedPath_le_process`: the managed surplus is an adapted process that
  keeps debt below the limit.
-/

namespace Cochrane.FiscalConstraints.DebtLimitStochasticMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic LognormalGrowthMeasure
open AggregateUncertaintyMeasure (integrable_coord_fun measurable_coord_future)

/-! ### General facts about the debt recursion -/

/-- Cochrane (2023), (6.4) p. 196: the debt ratio `x_t` is measurable for any σ-algebra for which
the surpluses `σ_0, …, σ_{t−1}` are measurable. -/
theorem measurable_debtPath {Ω : Type*} {m : MeasurableSpace Ω} (γ x₀ : ℝ) {σ : ℕ → Ω → ℝ} :
    ∀ t, (∀ s < t, Measurable[m] (σ s)) → Measurable[m] (debtPath γ x₀ σ t) := by
  intro t
  induction t with
  | zero => intro _; exact measurable_const
  | succ t ih =>
    intro h
    have h1 := ih fun s hs => h s (Nat.lt_succ_of_lt hs)
    have h2 := h t (Nat.lt_succ_self t)
    have hf : debtPath γ x₀ σ (t + 1) = fun ω => γ * debtPath γ x₀ σ t ω - σ t ω := by
      funext ω; exact debtPath_succ γ x₀ σ t ω
    rw [hf]
    exact (h1.const_mul γ).sub h2

/-- Cochrane (2023), (6.4) p. 196: restarting the recursion at date `N`,
`x_{N+k} = γ^k x_N + y_k` where `y` solves the same recursion from `y_0 = 0` driven by
`σ_N, σ_{N+1}, …`. -/
theorem debtPath_shift {Ω : Type*} (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∀ k, debtPath γ x₀ σ (N + k) ω =
      γ ^ k * debtPath γ x₀ σ N ω + debtPath γ 0 (fun s => σ (N + s)) k ω := by
  intro k
  induction k with
  | zero => change _ = _ * _ + 0; simp
  | succ k ih =>
    rw [← add_assoc, debtPath_succ, debtPath_succ, ih, pow_succ]
    ring

/-- Cochrane (2023), p. 197: a frequently-true property is shift invariant. -/
theorem frequently_shift_iff {p : ℕ → Prop} (N : ℕ) :
    (∃ᶠ t in atTop, p t) ↔ ∃ᶠ k in atTop, p (N + k) := by
  rw [frequently_atTop, frequently_atTop]
  constructor
  · intro h a
    obtain ⟨t, ht, hp⟩ := h (N + a)
    exact ⟨t - N, by omega, by rwa [show N + (t - N) = t by omega]⟩
  · intro h a
    obtain ⟨k, hk, hp⟩ := h a
    exact ⟨N + k, by omega, hp⟩

/-- Cochrane (2023), p. 197: "`z_t` gets within `1/(m+1)` of `a` from above infinitely often,
for every `m`" is unchanged by a perturbation that vanishes at infinity. -/
theorem frequently_near_of_tendsto {z z' : ℕ → ℝ} (hzz : Tendsto (fun t => z t - z' t) atTop (𝓝 0))
    {a : ℝ} (h : ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z t) (m : ℕ) :
    ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z' t := by
  have hpos : (0 : ℝ) < 1 / (2 * (m : ℝ) + 2) := by positivity
  have hev : ∀ᶠ t in atTop, |z t - z' t| < 1 / (2 * (m : ℝ) + 2) := by
    refine (hzz.eventually (Metric.ball_mem_nhds 0 hpos)).mono fun t ht => ?_
    rw [Real.dist_0_eq_abs] at ht
    exact ht
  have hf := h (2 * m + 1)
  refine (hf.and_eventually hev).mono fun t ht => ?_
  obtain ⟨h1, h2⟩ := ht
  rw [abs_lt] at h2
  have e1 : (1 : ℝ) / ((((2 * m + 1 : ℕ)) : ℝ) + 1) = 1 / (2 * (m : ℝ) + 2) := by
    push_cast; ring_nf
  rw [e1] at h1
  have e2 : 1 / (2 * (m : ℝ) + 2) + 1 / (2 * (m : ℝ) + 2) = 1 / ((m : ℝ) + 1) := by
    field_simp; ring
  linarith

/-- Cochrane (2023), p. 197: the event "frequently near or above `a`" for a sequence of
`m'`-measurable variables is `m'`-measurable. -/
theorem measurableSet_frequently_near {Ω : Type*} {m' : MeasurableSpace Ω} {y : ℕ → Ω → ℝ}
    (hy : ∀ k, Measurable[m'] (y k)) (a : ℝ) :
    MeasurableSet[m'] {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
  have h : {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} =
      ⋂ m : ℕ, ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {ω | a - 1 / ((m : ℝ) + 1) < y k ω} := by
    ext ω
    simp [frequently_atTop]
  rw [h]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iUnion
    fun k => MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hy k)

/-! ### The i.i.d. surplus process -/

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), (6.4) p. 196: on the i.i.d. process the debt ratio `x_{t+1}` is known at
date `t` (it depends on `σ_0, …, σ_t`), so `x` is adapted and predetermined. -/
theorem debtPath_adapted (γ x₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (debtPath γ x₀ shock (t + 1)) :=
  measurable_debtPath γ x₀ (t + 1) fun _ hs => measurable_shock ν (by omega)

/-- Cochrane (2023), p. 197: the coordinate surpluses are independent under `ν^ℕ`. -/
theorem iIndepFun_shock : iIndepFun shock (iidSystem ν).μ :=
  iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
    (fun _ => measurable_id)

/-- Cochrane (2023), p. 197: each surplus has law `ν`: `P(σ_t ∈ A) = ν(A)`. -/
theorem measure_shock_preimage (t : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (iidSystem ν).μ (shock t ⁻¹' A) = (ν : Measure ℝ) A :=
  (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t).measure_preimage
    hA.nullMeasurableSet

/-- **Theorem S on the i.i.d. process**, Cochrane (2023), §6.4.1, p. 197: if the surplus law
`ν` is a.s. bounded above by `K` and puts positive probability on deficits of size at least
`c`, then for `0 ≤ γ < 1` and every `M < c/(1 − γ)`, from every initial debt ratio, almost surely
the debt ratio exceeds `M` infinitely often. -/
theorem iid_frequently_exceeds {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K)
    (hp : (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  let _ : MeasureSpace (ℕ → ℝ) := @MeasureSpace.mk (ℕ → ℝ) MeasurableSpace.pi (iidSystem ν).μ
  exact frequently_exceeds hγ0 hγ1 hM (fun t => measurable_pi_apply t) iIndepFun_shock
    (fun t => (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t
      ).quasiMeasurePreserving.ae hK) hp
    (fun t => (measure_shock_preimage t measurableSet_Iic).ge)

/-- Cochrane (2023), p. 197 ("no value of debt is sustainable"), on the i.i.d. process: under the
hypotheses of `iid_frequently_exceeds`, the event that debt stays at or below `M` forever has
probability zero. -/
theorem iid_not_sustainable {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K)
    (hp : (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    (iidSystem ν).μ {ω | ∀ t, debtPath γ x₀ shock t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [iid_frequently_exceeds hγ0 hγ1 hM hK hp] with ω hω hall
  obtain ⟨t, ht⟩ := hω.exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197 (correction, **on a genuine process**): with i.i.d. fair `±1` coin
surpluses and `0 ≤ γ < 1`, almost surely the debt ratio never exceeds `max x₀ (1/(1 − γ))` (so
bounded support does not make debt exceed every bound), yet almost surely it exceeds every
`M < 1/(1 − γ)` infinitely often (Theorem S). -/
theorem coin_debt_dichotomy {γ x₀ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∀ᵐ ω ∂(iidSystem coin).μ, ∀ t, debtPath γ x₀ shock t ω ≤ max x₀ (1 / (1 - γ))) ∧
      ∀ M < 1 / (1 - γ), ∀ᵐ ω ∂(iidSystem coin).μ,
        ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  constructor
  · filter_upwards [ae_all_iff.2 (shock_ae_bdd coin coin_bdd)] with ω hω t
    exact debtPath_le_of_bounded_deficits hγ0 hγ1 (fun s => (abs_le.1 (hω s)).1) t
  · intro M hM
    have hK : ∀ᵐ x ∂(coin : Measure ℝ), x ≤ 1 :=
      coin_bdd.mono fun x h => (abs_le.1 h).2
    have hp : (coin : Measure ℝ) (Set.Iic (-1)) ≠ 0 := by
      change coinMeasure (Set.Iic (-1)) ≠ 0
      simp only [coinMeasure, Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply' _ measurableSet_Iic, Set.indicator, Set.mem_Iic, smul_eq_mul]
      norm_num
    exact iid_frequently_exceeds hγ0 hγ1 hM hK hp

/-- Cochrane (2023), p. 197 (**link**: the core `DebtLimitStochastic.iid_unbounded` on the
genuine process): if the surplus law `ν` is a.s. bounded above and puts positive mass on deficits
of every size, the core theorem applies to the coordinate surpluses of `ν^ℕ` and the debt ratio
is a.s. unbounded above. -/
theorem iid_unbounded_core {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K) (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  let _ : MeasureSpace (ℕ → ℝ) := @MeasureSpace.mk (ℕ → ℝ) MeasurableSpace.pi (iidSystem ν).μ
  have hmap : ∀ t, Measure.map (shock t) (iidSystem ν).μ = (ν : Measure ℝ) := fun t =>
    Measure.infinitePi_map_eval _ t
  refine DebtLimitStochastic.iid_unbounded hγ0 hγ1 (fun t => measurable_pi_apply t)
    iIndepFun_shock (fun t => ⟨(measurable_pi_apply t).aemeasurable,
      (measurable_pi_apply 0).aemeasurable, (hmap t).trans (hmap 0).symm⟩)
    (fun t => (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t
      ).quasiMeasurePreserving.ae hK) fun c => ?_
  exact (measure_shock_preimage 0 measurableSet_Iic).trans_ne (hdef c)

/-! ### Gaussian surpluses: the correction -/

/-- Cochrane (2023), p. 197 (**correction**): a non-degenerate Gaussian surplus is not almost
surely bounded above: `P(σ > K) > 0` for every `K`. -/
theorem gaussian_not_ae_bounded_above {Ω : Type*} [MeasureSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    (hlaw : Measure.map X volume = gaussianReal m v) (K : ℝ) :
    ¬ ∀ᵐ ω, X ω ≤ K := by
  intro h
  have h0 : volume (X ⁻¹' Set.Ioi K) = 0 := by
    rw [ae_iff] at h
    have hs : {ω | ¬ X ω ≤ K} = X ⁻¹' Set.Ioi K := by ext ω; simp
    rwa [hs] at h
  rw [← Measure.map_apply hX measurableSet_Ioi, hlaw] at h0
  have h2 := gaussianReal_absolutelyContinuous' m hv h0
  rw [Real.volume_Ioi] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (**correction**: `DebtLimitStochastic.gaussian_iid_unbounded` is
vacuous): if `σ_0` is non-degenerate Gaussian, the hypothesis "`σ_t ≤ K` a.s. at every date" of
that theorem is false for every `K`. -/
theorem gaussian_iid_unbounded_vacuous {Ω : Type*} [MeasureSpace Ω] {σ : ℕ → Ω → ℝ}
    (hσ : Measurable (σ 0)) {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    (hlaw : Measure.map (σ 0) volume = gaussianReal m v) (K : ℝ) :
    ¬ ∀ t, ∀ᵐ ω, σ t ω ≤ K :=
  fun h => gaussian_not_ae_bounded_above hσ hv hlaw K (h 0)

/-! ### The corrected theorem: i.i.d. surpluses unbounded below, no upper bound -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. surpluses (`E|σ| = m₁`), every debt ratio
is integrable with `E|x_t| ≤ |x₀| + m₁/(1 − γ)`. -/
theorem integral_abs_debtPath_le (hint : Integrable id (ν : Measure ℝ)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ : ℝ) :
    ∀ t, Integrable (debtPath γ x₀ shock t) (iidSystem ν).μ ∧
      ∫ ω, |debtPath γ x₀ shock t ω| ∂(iidSystem ν).μ ≤
        |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  have hm0 : 0 ≤ ∫ x, |x| ∂(ν : Measure ℝ) := integral_nonneg fun x => abs_nonneg x
  have hsh : ∀ s, Integrable (shock s) (iidSystem ν).μ := fun s =>
    integrable_coord_fun (f := id) hint s
  have hsa : ∀ s, ∫ ω, |shock s ω| ∂(iidSystem ν).μ = ∫ x, |x| ∂(ν : Measure ℝ) := fun s =>
    integral_shock_fun ν s (f := fun x => |x|) continuous_abs.measurable
  intro t
  induction t with
  | zero =>
    refine ⟨integrable_const x₀, ?_⟩
    change ∫ _, |x₀| ∂(iidSystem ν).μ ≤ _
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : 0 ≤ (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := div_nonneg hm0 h1.le
    linarith
  | succ t ih =>
    have hf : debtPath γ x₀ shock (t + 1) = fun ω => γ * debtPath γ x₀ shock t ω - shock t ω := by
      funext ω; exact debtPath_succ γ x₀ shock t ω
    have hI : Integrable (debtPath γ x₀ shock (t + 1)) (iidSystem ν).μ := by
      rw [hf]; exact (ih.1.const_mul γ).sub (hsh t)
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |debtPath γ x₀ shock (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (γ * |debtPath γ x₀ shock t ω| + |shock t ω|) ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul γ).add (hsh t).abs) fun ω => ?_
      rw [hf]
      calc |γ * debtPath γ x₀ shock t ω - shock t ω|
          ≤ |γ * debtPath γ x₀ shock t ω| + |shock t ω| := abs_sub _ _
        _ = γ * |debtPath γ x₀ shock t ω| + |shock t ω| := by
          rw [abs_mul, abs_of_nonneg hγ0]
    rw [integral_add (ih.1.abs.const_mul γ) (hsh t).abs, integral_const_mul, hsa] at hle
    have key : γ * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + ∫ x, |x| ∂(ν : Measure ℝ)
        ≤ |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := by
      have e : (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) * (1 - γ) = ∫ x, |x| ∂(ν : Measure ℝ) :=
        div_mul_cancel₀ _ h1.ne'
      nlinarith [abs_nonneg x₀]
    nlinarith [mul_le_mul_of_nonneg_left ih.2 hγ0]

/-- Cochrane (2023), p. 197: with integrable i.i.d. surpluses and deficits of every size, the
probability that the debt ratio exceeds `M` at date `t + 2` is bounded below uniformly in `t`:
`P(x_{t+2} > M) ≥ ν(−∞, −L] / 2` for `L = M + γ D + 1`, `D = 2 C + 1`,
`C = |x₀| + E|σ|/(1 − γ)` (Markov's inequality and independence of `σ_{t+1}` from `𝓕_t`). -/
theorem prob_exceeds_ge (hint : Integrable id (ν : Measure ℝ)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ M : ℝ) (t : ℕ) :
    (ν : Measure ℝ) (Set.Iic (-(M + γ * (2 * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + 1)
        + 1))) * ENNReal.ofReal (1 / 2) ≤
      (iidSystem ν).μ {ω | M < debtPath γ x₀ shock (t + 2) ω} := by
  set C := |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) with hC
  set D := 2 * C + 1 with hD
  set L := M + γ * D + 1 with hL
  have h1 : 0 < 1 - γ := by linarith
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _)
    (div_nonneg (integral_nonneg fun x => abs_nonneg x) h1.le)
  have hD0 : 0 < D := by linarith
  obtain ⟨hI, hbound⟩ := integral_abs_debtPath_le hint hγ0 hγ1 x₀ (t + 1)
  set A := {ω : ℕ → ℝ | -D < debtPath γ x₀ shock (t + 1) ω} with hA
  set B := {ω : ℕ → ℝ | ω (t + 1) ≤ -L} with hB
  have hAm : MeasurableSet[(iidSystem ν).𝓕 t] A :=
    measurableSet_lt measurable_const (debtPath_adapted ν γ x₀ t)
  have hBm : MeasurableSet[futureSigma t] B :=
    measurableSet_le (measurable_coord_future (by omega)) measurable_const
  have hind := (Indep_iff _ _ _).1 (indep_future ν t) B A hBm hAm
  have hsub : B ∩ A ⊆ {ω | M < debtPath γ x₀ shock (t + 2) ω} := by
    rintro ω ⟨hb, ha⟩
    simp only [Set.mem_ofPred_eq, hB, hA] at hb ha ⊢
    rw [show t + 2 = (t + 1) + 1 by rfl, debtPath_succ]
    change M < γ * debtPath γ x₀ shock (t + 1) ω - ω (t + 1)
    nlinarith [mul_le_mul_of_nonneg_left ha.le hγ0]
  have hBval : (iidSystem ν).μ B = (ν : Measure ℝ) (Set.Iic (-L)) :=
    measure_shock_preimage (t + 1) measurableSet_Iic
  have hAval : ENNReal.ofReal (1 / 2) ≤ (iidSystem ν).μ A := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (iidSystem ν).μ)
      (Eventually.of_forall fun ω => abs_nonneg (debtPath γ x₀ shock (t + 1) ω)) hI.abs D
    have hreal : (iidSystem ν).μ.real {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} ≤ 1 / 2 := by
      have : D * (iidSystem ν).μ.real {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} ≤ C :=
        hmk.trans hbound
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hpr := measureReal_nonneg (μ := (iidSystem ν).μ)
        (s := {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|})
      nlinarith
    have hcompl : Aᶜ ⊆ {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} := by
      intro ω hω
      simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
      rw [le_abs]; right; linarith
    have hAc : (iidSystem ν).μ.real Aᶜ ≤ 1 / 2 := (measureReal_mono hcompl).trans hreal
    have hAm' : MeasurableSet A := (iidSystem ν).𝓕.le t _ hAm
    rw [measureReal_compl hAm', probReal_univ] at hAc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2)
      ≤ (iidSystem ν).μ B * (iidSystem ν).μ A := by rw [hBval]; gcongr
    _ = (iidSystem ν).μ (B ∩ A) := hind.symm
    _ ≤ _ := measure_mono hsub

/-- Cochrane (2023), p. 197: if the events `A_{t+2}` all have probability at least `q`, then
"`A_t` infinitely often" has probability at least `q` (continuity from above). -/
theorem le_measure_frequently {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet (A t)) {q : ENNReal}
    (hq : ∀ t, q ≤ μ (A (t + 2))) : q ≤ μ {ω | ∃ᶠ t in atTop, ω ∈ A t} := by
  set B : ℕ → Set Ω := fun N => ⋃ t, ⋃ (_ : N ≤ t), A t with hBdef
  have hset : {ω | ∃ᶠ t in atTop, ω ∈ A t} = ⋂ N, B N := by
    ext ω
    simp [hBdef, frequently_atTop]
  have hanti : Antitone B := fun N N' h ω hω => by
    simp only [hBdef, Set.mem_iUnion] at hω ⊢
    obtain ⟨t, ht, h'⟩ := hω
    exact ⟨t, h.trans ht, h'⟩
  have hBm : ∀ N, NullMeasurableSet (B N) μ := fun N =>
    (MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => hA t).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top μ _⟩
  rw [hset]
  refine ge_of_tendsto' hlim fun N => ?_
  calc q ≤ μ (A (N + 2)) := hq N
    _ ≤ μ (B N) := measure_mono (Set.subset_biUnion_of_mem (u := A) (by omega : N ≤ N + 2))

/-- **The debt ratio is a.s. unbounded above for i.i.d. surpluses that are integrable and
unbounded below** — no upper bound on surpluses is needed (Cochrane (2023), p. 197: "an AR(1)
ranges over the entire real line", corrected discrete i.i.d. version). For `0 ≤ γ < 1` and every
initial debt `x₀`, almost surely `x_t` exceeds every level infinitely often. Proof: the events
"`x_t` comes within `1/(m+1)` of `M` infinitely often" are tail events (`debtPath_shift`), have
probability at least `ν(−∞, −L]/2 > 0` (`prob_exceeds_ge`), hence probability one by
Kolmogorov's 0-1 law. -/
theorem iid_unbounded_of_integrable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  set E : ℝ → Set (ℕ → ℝ) := fun a =>
    {ω | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock t ω} with hE
  have hmeas : ∀ t, Measurable (debtPath γ x₀ shock t) := fun t =>
    measurable_debtPath γ x₀ t fun s _ => measurable_pi_apply s
  -- the events are tail events
  have htail : ∀ a, MeasurableSet[limsup coordSigma atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → ℝ) → ℝ := fun k => debtPath γ 0 (fun s => shock (N + s)) k with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, coordSigma i] (y k) := fun k =>
      measurable_debtPath γ 0 k fun s _ => Measurable.of_comap_le
        (le_iSup₂ (f := fun i (_ : i ≥ N) => coordSigma i) (N + s) (by omega))
    have heq : E a = {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock t ω) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock (N + k) ω :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => debtPath γ x₀ shock (N + k) ω - y k ω) atTop (𝓝 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const
          (debtPath γ x₀ shock N ω)
        rw [zero_mul] at h
        refine h.congr fun k => ?_
        rw [debtPath_shift]
        simp only [hy]
        ring
      have hdiff' : Tendsto (fun k => y k ω - debtPath γ x₀ shock (N + k) ω) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near hym a
  -- each event has positive probability
  have hpos : ∀ a, (iidSystem ν).μ (E a) ≠ 0 := by
    intro a
    set c := a + γ * (2 * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + 1) + 1
    have hq := fun t => prob_exceeds_ge hint hγ0 hγ1 x₀ a t
    have hfreq := le_measure_frequently (μ := (iidSystem ν).μ)
      (A := fun t => {ω | a < debtPath γ x₀ shock t ω})
      (fun t => measurableSet_lt measurable_const (hmeas t)) hq
    have hsub : {ω | ∃ᶠ t in atTop, ω ∈ {ω' | a < debtPath γ x₀ shock t ω'}} ⊆ E a := by
      intro ω hω m
      refine hω.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    have := (hfreq.trans (measure_mono hsub)).trans_eq h0
    rw [nonpos_iff_eq_zero, mul_eq_zero] at this
    rcases this with h | h
    · exact hdef c h
    · rw [ENNReal.ofReal_eq_zero] at h
      norm_num at h
  -- Kolmogorov's 0-1 law
  have hone : ∀ n : ℕ, ∀ᵐ ω ∂(iidSystem ν).μ, ω ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop coordSigma_le (iIndep_coord ν)
      (htail n) with h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le coordSigma_le)) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ω hω M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hω n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

/-! ### i.i.d. Gaussian surpluses as a process -/

/-- Cochrane (2023), p. 197: a non-degenerate Gaussian law puts positive mass on deficits of
every size. -/
theorem gaussian_Iic_ne_zero (m : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal m v (Set.Iic (-c)) ≠ 0 := by
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Iic] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (**i.i.d. Gaussian surpluses as a process**): with surpluses
`σ_t` i.i.d. `N(m, v)`, `v ≠ 0`, on `ℕ → ℝ`, and `0 ≤ γ < 1`, the debt ratio is almost surely
unbounded above: it exceeds every level infinitely often, from every initial debt. -/
theorem gaussian_process_unbounded (m : ℝ) {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb m v)).μ, ∀ M : ℝ,
      ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  have hint : Integrable id (gaussianReal m v) := by
    have h := memLp_id_gaussianReal (μ := m) (v := v) 1
    rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
    exact h
  exact iid_unbounded_of_integrable (ν := gaussianProb m v) hint (gaussian_Iic_ne_zero m hv)
    hγ0 hγ1 x₀

/-- Cochrane (2023), p. 197 ("no value of debt is sustainable", **Gaussian process**): with
i.i.d. non-degenerate Gaussian surpluses, for every debt limit `M` the event that debt stays
at or below `M` forever has probability zero. -/
theorem gaussian_process_not_sustainable (m : ℝ) {v : NNReal} (hv : v ≠ 0) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ M : ℝ) :
    (iidSystem (gaussianProb m v)).μ {ω | ∀ t, debtPath γ x₀ shock t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussian_process_unbounded m hv hγ0 hγ1 x₀] with ω hω hall
  obtain ⟨t, ht⟩ := (hω M).exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197: on the Gaussian process every surplus has the Gaussian law, so the
process satisfies the law hypothesis of `DebtLimitStochastic.gaussian_iid_unbounded` but, by
`gaussian_iid_unbounded_vacuous`, never its upper-bound hypothesis; `gaussian_process_unbounded`
is the theorem that actually applies. -/
theorem gaussian_process_law (m : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (shock t) (iidSystem (gaussianProb m v)).μ = gaussianReal m v :=
  Measure.infinitePi_map_eval _ t

/-! ### The managed surplus as an adapted process -/

/-- Cochrane (2023), p. 197: the managed surplus `σ_t = ε_t + max 0 (γ x_t − ε_t − x̄)`. -/
noncomputable def managedSurplus (γ x₀ xbar : ℝ) (ε : ℕ → (ℕ → ℝ) → ℝ) (t : ℕ)
    (ω : ℕ → ℝ) : ℝ :=
  ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)

variable (ν) in
/-- Cochrane (2023), p. 197 ("we must already imagine a managed surplus process"): with
i.i.d. shocks `ε_t = ω_t`, the managed debt ratio `x_t` and the managed surplus `σ_t` are known
at date `t`: the management rule is a genuine adapted policy. -/
theorem managed_adapted (γ x₀ xbar : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (managedPath γ x₀ xbar shock t) ∧
      Measurable[(iidSystem ν).𝓕 t] (managedSurplus γ x₀ xbar shock t) := by
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (managedPath γ x₀ xbar shock t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hs := measurable_shock ν (Nat.le_succ t)
      have hf : managedPath γ x₀ xbar shock (t + 1) = fun ω =>
          γ * managedPath γ x₀ xbar shock t ω -
            (shock t ω + max 0 (γ * managedPath γ x₀ xbar shock t ω - shock t ω - xbar)) := rfl
      rw [hf]
      exact (ih'.const_mul γ).sub (hs.add (measurable_const.max
        (((ih'.const_mul γ).sub hs).sub measurable_const)))
  refine ⟨hx t, ?_⟩
  have hs := measurable_shock ν (le_refl t)
  exact hs.add (measurable_const.max (((hx t).const_mul γ).sub hs |>.sub measurable_const))

/-- Cochrane (2023), p. 197: on the i.i.d. process the managed surplus keeps the debt ratio at
or below the limit `x̄` from date 1 on, on every path. -/
theorem managedPath_le_process (γ x₀ xbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    managedPath γ x₀ xbar shock (t + 1) ω ≤ xbar :=
  managedPath_le γ x₀ xbar shock t ω

end Cochrane.FiscalConstraints.DebtLimitStochasticMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of the money-and-debt solution with the forward value (6.9)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.5, pp. 201–203,
equation (6.9).

`MoneyLiquidity.eq_6_9` and `MoneyLiquidity.present_value_unique` show that a path of money and
debt solving the flow equation `d(M + B)/dt = i B − P s` and the transversality condition is
the forward present value (6.9), and that it is unique. This module proves the converse,
existence, under the weakest natural hypothesis, and the equivalences.

The liability ratio `w = (M + B)/(P y)` obeys `w' = a w − f` with `a = r^f − g` and the flow
`f = s/y + i M/(P y)`. The natural hypothesis is that the forward present value exists as an
improper integral: `∫₀^T e^{−aτ} f_τ dτ → L` (`ImproperPV`). No sign of `a` and no bound on `f`
is needed.

## Main results

* `fwdValue`: the forward value `ŵ_t = e^{at}(L − ∫₀^t e^{−aτ} f_τ dτ)`;
  `tendsto_finite_pv`: `ŵ_t = lim_T ∫_t^T e^{−a(τ−t)} f_τ dτ` at every date.
* `fwdValue_hasDerivAt`, `fwdValue_tvc`: it solves the flow equation and satisfies the
  transversality condition at every date (existence).
* `tvc_iff`: a solution satisfies the transversality condition iff it equals the forward value
  at that date; `eq_fwdValue_of_tvc`, `existsUnique_tvc` (uniqueness of the whole path).
* `exists_tvc_iff`: a solution with the transversality condition exists iff the improper
  present value converges.
* `fwdValue_eq_integral`: under Lebesgue integrability the forward value is the Bochner
  integral `∫_t^∞ e^{−a(τ−t)} f_τ dτ`; `integrable_of_bdd` (the setting of
  `MoneyLiquidity.eq_6_9`: `r^f > g`, bounded flows).
* For money and debt: `money_debt_exists` (debt `B = P y ŵ − M` solves the flow equation, has
  the value (6.9) and satisfies the transversality condition), `money_debt_unique`,
  `money_debt_tvc_iff`, `money_debt_exists_iff`, `eq_6_9_exists` (the bounded case of (6.9)).
-/

namespace Cochrane.FiscalConstraints.TidyR5MoneyExistence

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.LinearODE

/-- Cochrane (2023), (6.9) p. 201: the forward present value of the flow `f` discounted at `a`
converges as an improper integral to `L`: `∫₀^T e^{−aτ} f_τ dτ → L` as `T → ∞`. -/
def ImproperPV (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) atTop (𝓝 L)

/-- Cochrane (2023), (6.9) p. 201: the forward value `ŵ_t = e^{at}(L − ∫₀^t e^{−aτ} f_τ dτ)`
(the variation-of-constants solution through `(0, L)`). -/
noncomputable def fwdValue (a : ℝ) (f : ℝ → ℝ) (L t : ℝ) : ℝ := vocFrom a f 0 L t

/-- Cochrane (2023), (6.9) p. 201: the forward value written out. -/
theorem fwdValue_eq (a : ℝ) (f : ℝ → ℝ) (L t : ℝ) :
    fwdValue a f L t = exp (a * t) * (L - ∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) := by
  unfold fwdValue vocFrom
  rw [mul_zero, exp_zero, one_mul]

variable {a L K : ℝ} {f w : ℝ → ℝ}

/-- Cochrane (2023), (6.13) p. 203: the finite-horizon present value from `t` to `T` is
`e^{at}(∫₀^T e^{−aτ} f − ∫₀^t e^{−aτ} f)`. -/
theorem finite_pv_eq (hf : Continuous f) (t T : ℝ) :
    ∫ τ in t..T, exp (-a * (τ - t)) * f τ =
      exp (a * t) * ((∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) -
        ∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) := by
  have hc : Continuous fun τ => exp (-a * τ) * f τ := by fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 T)
    (hc.intervalIntegrable 0 t), ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), (6.9) p. 201: when the improper present value converges, the forward value
at every date `t` is the limit of the finite-horizon present values,
`ŵ_t = lim_{T→∞} ∫_t^T e^{−a(τ−t)} f_τ dτ`. -/
theorem tendsto_finite_pv (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => ∫ τ in t..T, exp (-a * (τ - t)) * f τ) atTop
      (𝓝 (fwdValue a f L t)) := by
  simp_rw [finite_pv_eq hf t, fwdValue_eq]
  exact (hL.sub_const _).const_mul _

/-- Cochrane (2023), (6.9) p. 201 (existence, the flow equation): the forward value solves
`w' = a w − f` at every date. -/
theorem fwdValue_hasDerivAt (hf : Continuous f) (L τ : ℝ) :
    HasDerivAt (fwdValue a f L) (a * fwdValue a f L τ - f τ) τ :=
  vocFrom_hasDerivAt a hf 0 L τ

/-- Cochrane (2023), (6.12)–(6.13) pp. 202–203: for any solution of `w' = a w − f`, the
discounted terminal value is `e^{−a(T−t)} w_T = w_t − ∫_t^T e^{−a(τ−t)} f_τ dτ`. -/
theorem terminal_eq (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    exp (-a * (T - t)) * w T = w t - ∫ τ in t..T, exp (-a * (τ - t)) * f τ := by
  have := finite_horizon_identity hw hf t T
  linarith

/-- Cochrane (2023), (6.9) p. 201: for any solution, the discounted terminal value converges to
`w_t − ŵ_t`. -/
theorem tendsto_terminal (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 (w t - fwdValue a f L t)) := by
  simp_rw [terminal_eq hw hf t]
  exact (tendsto_finite_pv hf hL t).const_sub _

/-- Cochrane (2023), (6.9) p. 201 (**the iff**): a solution of the flow equation satisfies the
transversality condition `e^{−a(T−t)} w_T → 0` iff its value at `t` is the forward value (6.9). -/
theorem tvc_iff (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0) ↔ w t = fwdValue a f L t := by
  have h := tendsto_terminal hw hf hL t
  constructor
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith
  · intro he
    rwa [he, sub_self] at h

/-- Cochrane (2023), (6.9) p. 201 (**existence**, the transversality condition): the forward
value satisfies the transversality condition at every date. -/
theorem fwdValue_tvc (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * fwdValue a f L T) atTop (𝓝 0) :=
  (tvc_iff (fwdValue_hasDerivAt hf L) hf hL t).2 rfl

/-- Cochrane (2023), (6.9) p. 201 (uniqueness of the whole path): a solution satisfying the
transversality condition at one date `t` is the forward value at every date. -/
theorem eq_fwdValue_of_tvc (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) {t : ℝ}
    (htvc : Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    w = fwdValue a f L := by
  have ht := (tvc_iff hw hf hL t).1 htvc
  funext T
  rw [vocFrom_eq_of_global hw hf t T, vocFrom_eq_of_global (fwdValue_hasDerivAt hf L) hf t T,
    ht]

/-- Cochrane (2023), (6.9) p. 201 (**existence and uniqueness**): when the improper present
value converges, there is exactly one solution of the flow equation satisfying the
transversality condition at `t`, the forward value. -/
theorem existsUnique_tvc (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    ∃! w : ℝ → ℝ, (∀ τ, HasDerivAt w (a * w τ - f τ) τ) ∧
      Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0) :=
  ⟨fwdValue a f L, ⟨fwdValue_hasDerivAt hf L, fwdValue_tvc hf hL t⟩,
    fun _ hw => eq_fwdValue_of_tvc hw.1 hf hL hw.2⟩

/-- Cochrane (2023), (6.9) p. 201 (**the existence iff**): a solution of the flow equation
satisfying the transversality condition exists iff the forward present value converges as an
improper integral. -/
theorem exists_tvc_iff (hf : Continuous f) (t : ℝ) :
    (∃ w : ℝ → ℝ, (∀ τ, HasDerivAt w (a * w τ - f τ) τ) ∧
      Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) ↔ ∃ L, ImproperPV a f L := by
  constructor
  · rintro ⟨w, hw, htvc⟩
    have hJ : Tendsto (fun T => ∫ τ in t..T, exp (-a * (τ - t)) * f τ) atTop (𝓝 (w t)) := by
      have h := htvc.const_sub (w t)
      rw [sub_zero] at h
      refine h.congr fun T => ?_
      rw [terminal_eq hw hf t T]
      ring
    refine ⟨(∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) + exp (-a * t) * w t, ?_⟩
    have he : ∀ T, ∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ = (∫ τ in (0 : ℝ)..t,
        exp (-a * τ) * f τ) + exp (-a * t) * ∫ τ in t..T, exp (-a * (τ - t)) * f τ := by
      intro T
      rw [finite_pv_eq hf t T]
      have e : exp (-a * t) * exp (a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
      generalize (∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) = I1
      generalize (∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) = I2
      linear_combination (-(I1 - I2)) * e
    exact ((hJ.const_mul _).const_add _).congr fun T => (he T).symm
  · rintro ⟨L, hL⟩
    exact ⟨fwdValue a f L, fwdValue_hasDerivAt hf L, fwdValue_tvc hf hL t⟩

/-- Cochrane (2023), (6.9) p. 201: a continuous flow whose discounted value is integrable on
`(0, ∞)` is integrable on every `(c, ∞)`. -/
theorem integrableOn_Ioi_of (hf : Continuous f)
    (hint : IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0)) (c : ℝ) :
    IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi c) := by
  have hc : Continuous fun τ => exp (-a * τ) * f τ := by fun_prop
  refine ((hc.integrableOn_Icc (a := min c 0) (b := 0)).union hint).mono_set fun τ hτ => ?_
  rcases le_or_gt τ 0 with h | h
  · exact Or.inl ⟨le_trans (min_le_left _ _) (le_of_lt hτ), h⟩
  · exact Or.inr h

/-- Cochrane (2023), (6.9) p. 201: under Lebesgue integrability of the discounted flow, the
improper present value converges to `∫₀^∞ e^{−aτ} f_τ dτ`, and the forward value at every date
is the Bochner integral `ŵ_t = ∫_t^∞ e^{−a(τ−t)} f_τ dτ`. -/
theorem fwdValue_eq_integral (hf : Continuous f)
    (hint : IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0)) :
    ImproperPV a f (∫ τ in Set.Ioi (0 : ℝ), exp (-a * τ) * f τ) ∧
      ∀ t, fwdValue a f (∫ τ in Set.Ioi (0 : ℝ), exp (-a * τ) * f τ) t =
        ∫ τ in Set.Ioi t, exp (-a * (τ - t)) * f τ := by
  refine ⟨intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id, fun t => ?_⟩
  rw [fwdValue_eq, ExpIntegrals.integral_Ioi_sub_interval (integrableOn_Ioi_of hf hint) t,
    ← integral_const_mul]
  congr 1
  funext τ
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), (6.9) p. 201 (the setting of `MoneyLiquidity.eq_6_9`): with `a = r^f − g > 0`
and a bounded continuous flow, the discounted flow is integrable on `(0, ∞)`. -/
theorem integrable_of_bdd (ha : 0 < a) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K) :
    IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0) :=
  ExpIntegrals.integrableOn_exp_mul_bdd ha hf hK 0

/-! ### Money and debt -/

variable {M B P y s infl i : ℝ → ℝ} {g rf : ℝ}

/-- Cochrane (2023), (6.9) p. 201: for any money-and-debt path solving the flow equation
`d(M + B)/dt = i B − P s`, with `dP/dt = π P`, `dy/dt = g y` and `i = r^f + π`, the liability
ratio `w = (M + B)/(P y)` solves `w' = (r^f − g) w − (s/y + i M/(P y))`. -/
theorem ratio_hasDerivAt (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ) (τ : ℝ) :
    HasDerivAt (fun x => (M x + B x) / (P x * y x))
      ((rf - g) * ((M τ + B τ) / (P τ * y τ)) - (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ := by
  have h := MoneyLiquidity.hasDerivAt_liabilityRatio (g := fun _ => g) (hW τ) (hP τ) (hy τ)
    (hP0 τ) (hy0 τ)
  convert h using 1
  rw [hi τ]
  ring

/-- Cochrane (2023), (6.9) p. 201: with debt `B = P y W − M`, the liability ratio
`(M + B)/(P y)` is `W`. -/
theorem ratio_of_debt (W : ℝ → ℝ) {t : ℝ} (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    (M t + (P t * y t * W t - M t)) / (P t * y t) = W t := by
  have := mul_ne_zero hP0 hy0
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201: if a ratio path `W` solves
`W' = (r^f − g) W − (s/y + i M/(P y))`, with `dP/dt = π P`, `dy/dt = g y` and `i = r^f + π`, then
debt `B = P y W − M` solves the flow equation `d(M + B)/dt = i B − P s`. -/
theorem flow_of_debt {W : ℝ → ℝ} {τ : ℝ} (hP : HasDerivAt P (infl τ * P τ) τ)
    (hy : HasDerivAt y (g * y τ) τ) (hP0 : P τ ≠ 0) (hy0 : y τ ≠ 0) (hi : i τ = rf + infl τ)
    (hW : HasDerivAt W ((rf - g) * W τ - (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ) :
    HasDerivAt (fun x => M x + (P x * y x * W x - M x))
      (i τ * (P τ * y τ * W τ - M τ) - P τ * s τ) τ := by
  have hMB : (fun x => M x + (P x * y x * W x - M x)) = fun x => P x * y x * W x := by
    funext x; ring
  rw [hMB]
  refine ((hP.mul hy).mul hW).congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [hi]
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201 (**existence for money and debt**): given money `M`, the price
level, output and the surplus, with `i = r^f + π` and a convergent improper present value `L` of
`f = s/y + i M/(P y)` discounted at `r^f − g`, the debt path `B = P y ŵ − M` solves the flow
equation `d(M + B)/dt = i B − P s` at every date, its liability ratio is the forward value (6.9)
at every date, and it satisfies the transversality condition at every date. -/
theorem money_debt_exists (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) :
    let B := fun τ => P τ * y τ *
      fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L τ - M τ
    (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      (∀ t, (M t + B t) / (P t * y t) =
        fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L t) ∧
      ∀ t, Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
        (𝓝 0) := by
  intro B
  set F := fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)) with hF
  have hratio : ∀ t, (M t + B t) / (P t * y t) = fwdValue (rf - g) F L t := fun t =>
    ratio_of_debt (fwdValue (rf - g) F L) (hP0 t) (hy0 t)
  refine ⟨fun τ => flow_of_debt (hP τ) (hy τ) (hP0 τ) (hy0 τ) (hi τ)
    (fwdValue_hasDerivAt (a := rf - g) hf L τ), hratio, fun t => ?_⟩
  simp_rw [hratio]
  exact fwdValue_tvc hf hL t

/-- Cochrane (2023), (6.9) p. 201 (**the iff for money and debt**): for a money-and-debt path
solving the flow equation, the transversality condition at `t` holds iff the value of money and
debt at `t` is the forward value (6.9). -/
theorem money_debt_tvc_iff
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) (t : ℝ) :
    Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop (𝓝 0) ↔
      (M t + B t) / (P t * y t) =
        fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L t :=
  tvc_iff (w := fun x => (M x + B x) / (P x * y x))
    (ratio_hasDerivAt hW hP hy hP0 hy0 hi) hf hL t

/-- Cochrane (2023), (6.9) p. 201 (**uniqueness for money and debt**): any debt path solving the
flow equation and the transversality condition at one date is the debt of `money_debt_exists`,
`B = P y ŵ − M`, at every date. -/
theorem money_debt_unique
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) {t : ℝ}
    (htvc : Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
      (𝓝 0)) :
    B = fun τ => P τ * y τ *
      fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L τ - M τ := by
  have h := eq_fwdValue_of_tvc (w := fun x => (M x + B x) / (P x * y x))
    (ratio_hasDerivAt hW hP hy hP0 hy0 hi) hf hL htvc
  funext τ
  have hτ := congrFun h τ
  have h1 := hP0 τ
  have h2 := hy0 τ
  change (M τ + B τ) / (P τ * y τ) = _ at hτ
  rw [← hτ]
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201 (**the existence iff for money and debt**): given money, prices,
output and surpluses, a debt path solving the flow equation and the transversality condition at
`t` exists iff the present value of `s/y + i M/(P y)` discounted at `r^f − g` converges as an
improper integral. -/
theorem money_debt_exists_iff (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (t : ℝ) :
    (∃ B : ℝ → ℝ, (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop (𝓝 0))
      ↔ ∃ L, ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L := by
  constructor
  · rintro ⟨B, hW, htvc⟩
    exact (exists_tvc_iff hf t).1 ⟨_, ratio_hasDerivAt hW hP hy hP0 hy0 hi, htvc⟩
  · rintro ⟨L, hL⟩
    obtain ⟨h1, -, h3⟩ := money_debt_exists hP hy hP0 hy0 hi hf hL
    exact ⟨_, h1, h3 t⟩

/-- Cochrane (2023), (6.9) p. 201 (**existence in the setting of `MoneyLiquidity.eq_6_9`**): with
`r^f > g`, `i = r^f + π` and a bounded continuous flow `s/y + i M/(P y)`, there is a debt path
solving the flow equation and the transversality condition at every date, whose value of money
and debt is the Bochner present value (6.9),
`(M_t + B_t)/(P_t y_t) = ∫_t^∞ e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ M_τ/(P_τ y_τ)) dτ`, at every
date. -/
theorem eq_6_9_exists (hrg : g < rf) (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hK : ∀ τ, |s τ / y τ + i τ * (M τ / (P τ * y τ))| ≤ K) :
    ∃ B : ℝ → ℝ, (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      (∀ t, Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
        (𝓝 0)) ∧
      ∀ t, (M t + B t) / (P t * y t) = ∫ τ in Set.Ioi t, exp (-(rf - g) * (τ - t)) *
        (s τ / y τ + i τ * (M τ / (P τ * y τ))) := by
  have hint := integrable_of_bdd (sub_pos.2 hrg) hf hK
  obtain ⟨hL, hrep⟩ := fwdValue_eq_integral hf hint
  obtain ⟨h1, h2, h3⟩ := money_debt_exists hP hy hP0 hy0 hi hf hL
  exact ⟨_, h1, h3, fun t => (h2 t).trans (hrep t)⟩

end Cochrane.FiscalConstraints.TidyR5MoneyExistence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Temporary `r < g` with finitely many regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 196 ("if the
`r < g` opportunity fades away, fiscal theory reemerges").

`RvsG` proves the corrected 20-year formula for two regimes (`RvsG.step_existsUnique`). Here
`r − g` is piecewise constant with any finite number of regimes: `a₀` on `[T₀, T₁)`, `a₁` on
`[T₁, T₂)`, …, `a_{n−1}` on `[T_{n−1}, T_n)` and `a_n` on `[T_n, ∞)`, with `0 = T₀ ≤ T₁ ≤ ⋯ ≤ T_n`.
The rates before the last switch have any signs; the last one is positive (`r > g` after).

The proof first treats a general time-varying `r − g` with a continuous cumulative rate
`A(t) = ∫₀^t (r − g)` that is differentiable off a countable set and eventually linear with
positive slope (`SolvesGen`). Every solution is `x_t = e^{A(t)}(x₀ − ∫₀^t e^{−A(v)} σ_v dv)`
(`eq_vocA`, by the fundamental theorem of calculus off a countable set), and the sustainable debt is
`x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`.

## Main results

* General rate: `gen_solves`, `gen_bddOn`, `gen_bddOn_iff`, `gen_tendsto_abs_of_ne`,
  `gen_existsUnique`, `gen_tvc_iff`, `gSol_eq_integral`
  (`x̂_t = ∫_t^∞ exp(−∫_t^v (r − g)) σ_v dv`).
* Finitely many regimes: the cumulative rate `cum` and its regime formulas (`cum_eq_regime`,
  `cum_eq_last`, `cum_hasDerivAt_regime`, `cum_hasDerivAt_last`); the solution concept
  `SolvesPW`; `pw_existsUnique` (exactly one bounded solution), `pw_bddOn_iff` (bounded iff
  `x₀ = x̂₀`), `pw_tendsto_abs_of_ne` (every other solution explodes), `pw_tvc_iff` (the
  transversality condition iff `x₀ = x̂₀`), `pw_nominal_determinacy` (exactly one `P₀`).
* `pwPV0_eq_sum`: the general 20-year formula,
  `x̂₀ = ∑_{k<n} e^{−A(T_k)} ∫_{T_k}^{T_{k+1}} e^{−a_k(v−T_k)} σ_v dv + e^{−A(T_n)} x̂^{(n)}_{T_n}`,
  with `A(T_k) = ∑_{j<k} a_j (T_{j+1} − T_j)` and `x̂^{(n)}` the present value at the last rate.
* `pw_unique_iff_last_pos`: a bounded solution is unique for every bounded surplus iff `r > g` in
  the last regime, whatever the signs before.
* `solvesStep_iff`, `pwPV0_two_regime`: the two-regime case is `RvsG.SolvesStep` and
  `RvsG.stepPV0`.
-/

namespace Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals Cochrane.FiscalConstraints.RvsG

/-! ### A general time-varying `r − g` -/

/-- Cochrane (2023), eq. (6.4), p. 196, with time-varying `r − g = ρ(t)`: `x` is continuous on
`[0, ∞)` and solves `x' = ρ(t) x − σ` at every `t > 0` outside the exceptional set `S` (the switch
dates). -/
def SolvesGen (ρ : ℝ → ℝ) (S : Set ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ∀ t, 0 < t → t ∉ S → HasDerivAt x (ρ t * x t - σ t) t

/-- Cochrane (2023), eq. (6.5), p. 196, with time-varying `r − g`: the backward solution from
`x₀` with cumulative rate `A`, `x_t = e^{A(t)}(x₀ − ∫₀^t e^{−A(v)} σ_v dv)`. -/
noncomputable def vocA (A σ : ℝ → ℝ) (x0 t : ℝ) : ℝ :=
  exp (A t) * (x0 - ∫ v in (0 : ℝ)..t, exp (-A v) * σ v)

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable initial debt-to-GDP ratio with time-varying
`r − g`, `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
noncomputable def pvA (A σ : ℝ → ℝ) : ℝ := ∫ v in Set.Ioi (0 : ℝ), exp (-A v) * σ v

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution, the backward solution started
at `x̂₀`. -/
noncomputable def gSol (A σ : ℝ → ℝ) (t : ℝ) : ℝ := vocA A σ (pvA A σ) t

variable {A ρ σ x : ℝ → ℝ} {S : Set ℝ} {Tn ab M : ℝ}

/-- Cochrane (2023), eq. (6.4), p. 196: the backward solution solves `x' = r x − σ` at every
date where the cumulative rate has derivative `r`. -/
theorem vocA_hasDerivAt (hσ : Continuous σ) (hAc : Continuous A) (x0 : ℝ) {t r : ℝ}
    (hA : HasDerivAt A r t) : HasDerivAt (vocA A σ x0) (r * vocA A σ x0 t - σ t) t := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := hA.exp.mul (hI.const_sub x0)
  unfold vocA
  refine h.congr_deriv ?_
  have : exp (A t) * exp (-A t) = 1 := by rw [← exp_add]; simp
  linear_combination (-(σ t)) * this

/-- Cochrane (2023), eq. (6.5), p. 196: the backward solution is continuous. -/
theorem vocA_continuous (hσ : Continuous σ) (hAc : Continuous A) (x0 : ℝ) :
    Continuous (vocA A σ x0) := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI : Continuous fun t => ∫ v in (0 : ℝ)..t, exp (-A v) * σ v :=
    continuous_iff_continuousAt.2 fun t =>
      (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  unfold vocA
  fun_prop

/-- Cochrane (2023), eq. (6.5), p. 196: the backward solution starts at `x₀`. -/
theorem vocA_zero (hA0 : A 0 = 0) (x0 : ℝ) : vocA A σ x0 0 = x0 := by
  unfold vocA
  rw [hA0, exp_zero, intervalIntegral.integral_same, sub_zero, one_mul]

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions differ by `e^{A(t)}(x₀ − z₀)`. -/
theorem vocA_sub (x0 z0 t : ℝ) : vocA A σ x0 t - vocA A σ z0 t = exp (A t) * (x0 - z0) := by
  unfold vocA
  ring

/-- Cochrane (2023), eq. (6.5), p. 196 (**uniqueness with time-varying `r − g`**): every solution
on `[0, ∞)` is the backward solution from its initial value, when the cumulative rate is
continuous with derivative `ρ` off a countable set `S`. -/
theorem eq_vocA (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hx : SolvesGen ρ S σ x) {t : ℝ} (ht : 0 ≤ t) : x t = vocA A σ (x 0) t := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI : Continuous fun t => ∫ v in (0 : ℝ)..t, exp (-A v) * σ v :=
    continuous_iff_continuousAt.2 fun t =>
      (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  set g : ℝ → ℝ := fun u => exp (-A u) * x u + ∫ v in (0 : ℝ)..u, exp (-A v) * σ v with hg
  have hgc : ContinuousOn g (Set.Icc 0 t) :=
    ((by fun_prop : Continuous fun u => exp (-A u)).continuousOn.mul
      (hx.1.mono Set.Icc_subset_Ici_self)).add hI.continuousOn
  have hgd : ∀ u ∈ Set.Ioo 0 t \ S, HasDerivAt g 0 u := by
    rintro u ⟨hu, huS⟩
    have h1 := (hAd u hu.1 huS).neg.exp
    have h2 := hx.2 u hu.1 huS
    have h3 := (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
    refine ((h1.mul h2).add h3).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le g (fun _ => (0 : ℝ)) ht hS hgc hgd
    intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hftc
  have h' : exp (-A t) * x t + (∫ v in (0 : ℝ)..t, exp (-A v) * σ v) - x 0 = 0 := by
    have hg0 : g 0 = x 0 := by
      simp only [hg, hA0, neg_zero, exp_zero, one_mul, intervalIntegral.integral_same, add_zero]
    have : g t - g 0 = 0 := hftc.symm
    rw [hg0] at this
    exact this
  have hE : exp (A t) * exp (-A t) = 1 := by rw [← exp_add]; simp
  unfold vocA
  linear_combination (exp (A t)) * h' + (-(x t)) * hE

/-- Cochrane (2023), §6.4.1, p. 196: if `r − g` is eventually constant at `ā > 0` (after `T_n`)
and surpluses are continuous and bounded, the discounted surpluses `e^{−A(v)} σ_v` are integrable
on every `(c, ∞)`. -/
theorem integrableOn_expA (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) (c : ℝ) :
    IntegrableOn (fun v => exp (-A v) * σ v) (Set.Ioi c) := by
  have h1 : IntegrableOn (fun v => exp (-A v) * σ v) (Set.Ioi (max c Tn)) := by
    have := (integrableOn_exp_mul_bdd ha hσ hM (max c Tn)).const_mul (exp (-A Tn + ab * Tn))
    refine IntegrableOn.congr_fun this (fun v hv => ?_) measurableSet_Ioi
    have hv' : Tn ≤ v := le_trans (le_max_right _ _) (le_of_lt hv)
    rw [hAT v hv', ← mul_assoc, ← exp_add]
    congr 2
    ring
  have h2 : IntegrableOn (fun v => exp (-A v) * σ v) (Set.Icc c (max c Tn)) :=
    (by fun_prop : Continuous fun v => exp (-A v) * σ v).integrableOn_Icc
  refine (h2.union h1).mono_set fun v hv => ?_
  rcases le_or_gt v (max c Tn) with h | h
  · exact Or.inl ⟨le_of_lt hv, h⟩
  · exact Or.inr h

/-- Cochrane (2023), §6.4.1, p. 196 (the forward formula at every date): the forward-looking
solution is `x̂_t = ∫_t^∞ exp(−(A(v) − A(t))) σ_v dv`, i.e. surpluses discounted at the cumulated
`r − g` between `t` and `v`. -/
theorem gSol_eq_integral (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) (t : ℝ) :
    gSol A σ t = ∫ v in Set.Ioi t, exp (-(A v - A t)) * σ v := by
  unfold gSol vocA pvA
  rw [integral_Ioi_sub_interval (integrableOn_expA hAc hσ hM hAT ha) t, ← integral_const_mul]
  congr 1
  funext v
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the forward-looking solution is the
constant-rate present value `RvsG.pv ā σ t`. -/
theorem gSol_eq_pv (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) {t : ℝ} (ht : Tn ≤ t) :
    gSol A σ t = pv ab σ t := by
  rw [gSol_eq_integral hAc hσ hM hAT ha t, pv]
  rw [← integral_Ioi_comp_add (fun v => exp (-(A v - A t)) * σ v) t]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  rw [hAT (t + u) (by linarith), hAT t ht]
  congr 2
  ring

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution is continuous. -/
theorem gSol_continuous (hσ : Continuous σ) (hAc : Continuous A) : Continuous (gSol A σ) :=
  vocA_continuous hσ hAc _

/-- Cochrane (2023), §6.4.1, p. 196 (existence): the forward-looking solution is bounded on
`[0, ∞)`. -/
theorem gen_bddOn (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) : BddOn (gSol A σ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Tn)).exists_bound_of_continuousOn
    (gSol_continuous hσ hAc).continuousOn
  refine ⟨max C (M / ab), fun t ht => ?_⟩
  rcases le_total t Tn with h | h
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · rw [gSol_eq_pv hAc hσ hM hAT ha h]
    exact (abs_pv_le ha hM t).trans (le_max_right _ _)

/-- Cochrane (2023), §6.4.1, p. 196 (existence): the forward-looking solution solves the
equation with time-varying `r − g`. -/
theorem gen_solves (hAc : Continuous A) (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t)
    (hσ : Continuous σ) : SolvesGen ρ S σ (gSol A σ) :=
  ⟨(gSol_continuous hσ hAc).continuousOn, fun t ht htS => vocA_hasDerivAt hσ hAc _ (hAd t ht htS)⟩

/-- Cochrane (2023), §6.4.1, p. 196: every solution differs from the forward-looking one by
`e^{A(t)}(x₀ − x̂₀)`. -/
theorem gen_sub (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hx : SolvesGen ρ S σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t - gSol A σ t = exp (A t) * (x 0 - pvA A σ) := by
  rw [eq_vocA hS hAc hA0 hAd hσ hx ht, gSol, vocA_sub]

/-- Cochrane (2023), §6.4.1, p. 196 ("values of debt different from this forward-looking integral
lead to explosions"), time-varying `r − g`: a solution not starting at `x̂₀` explodes. -/
theorem gen_tendsto_abs_of_ne (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) (hne : x 0 ≠ pvA A σ) :
    Tendsto (fun t => |x t|) atTop atTop := by
  set d := |x 0 - pvA A σ| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hlow : ∀ t, max 0 Tn ≤ t →
      exp (A Tn + ab * (t - Tn)) * d + -(M / ab) ≤ |x t| := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
    have htn : Tn ≤ t := le_trans (le_max_right _ _) ht
    have h1 := gen_sub hS hAc hA0 hAd hσ hx ht0
    have h2 := abs_pv_le ha hM t
    rw [← gSol_eq_pv hAc hσ hM hAT ha htn] at h2
    have h3 : exp (A Tn + ab * (t - Tn)) * d = |x t - gSol A σ t| := by
      rw [h1, abs_mul, abs_of_pos (exp_pos _), hAT t htn]
    have h4 := abs_sub (x t) (gSol A σ t)
    linarith
  have hlim : Tendsto (fun t => exp (A Tn + ab * (t - Tn)) * d + -(M / ab)) atTop atTop := by
    have h1 : Tendsto (fun t => A Tn + ab * (t - Tn)) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_atTop_add_const_right _ (-Tn) tendsto_id).const_mul_atTop ha)
    exact tendsto_atTop_add_const_right _ _ ((tendsto_exp_atTop.comp h1).atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop (max 0 Tn)).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196, time-varying `r − g`: a solution is bounded iff it starts at
the sustainable value `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
theorem gen_bddOn_iff (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) : BddOn x ↔ x 0 = pvA A σ := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (gen_tendsto_abs_of_ne hS hAc hA0 hAd hσ hM hAT ha hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    obtain ⟨K, hK⟩ := gen_bddOn hAc hσ hM hAT ha
    refine ⟨K, fun t ht => ?_⟩
    have := gen_sub hS hAc hA0 hAd hσ hx ht
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact hK t ht

/-- Cochrane (2023), §6.4.1, p. 196 (**existence and uniqueness**, time-varying `r − g`): there is
a bounded solution, and every bounded solution is the forward-looking one at every date
`t ≥ 0`. -/
theorem gen_existsUnique (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) :
    SolvesGen ρ S σ (gSol A σ) ∧ BddOn (gSol A σ) ∧
      ∀ x, SolvesGen ρ S σ x → BddOn x → ∀ t, 0 ≤ t → x t = gSol A σ t := by
  refine ⟨gen_solves hAc hAd hσ, gen_bddOn hAc hσ hM hAT ha, fun x hx hb t ht => ?_⟩
  have := gen_sub hS hAc hA0 hAd hσ hx ht
  rw [(gen_bddOn_iff hS hAc hA0 hAd hσ hM hAT ha hx).1 hb, sub_self, mul_zero, sub_eq_zero]
    at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (**transversality**, time-varying `r − g`): the discounted
debt-to-GDP ratio `e^{−A(t)} x_t` (debt discounted at the cumulated real rate, relative to
GDP) tends to `0` iff `x₀ = x̂₀`. -/
theorem gen_tvc_iff (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) :
    Tendsto (fun t => exp (-A t) * x t) atTop (𝓝 0) ↔ x 0 = pvA A σ := by
  have hlimI := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_expA hAc hσ hM hAT ha 0) tendsto_id
  have hev : ∀ᶠ t in atTop,
      x 0 - (∫ v in (0 : ℝ)..t, exp (-A v) * σ v) = exp (-A t) * x t := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [eq_vocA hS hAc hA0 hAd hσ hx ht, vocA, ← mul_assoc, ← exp_add]
    simp
  have hlim : Tendsto (fun t => exp (-A t) * x t) atTop (𝓝 (x 0 - pvA A σ)) :=
    (hlimI.const_sub (x 0)).congr' hev
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-! ### Finitely many regimes -/

/-- Cochrane (2023), §6.4.1, p. 196: `t` clamped to `[lo, hi]`, `max lo (min t hi)`. -/
noncomputable def clampI (lo hi t : ℝ) : ℝ := max lo (min t hi)

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated `r − g` with `n` switches, rates `a k` on
`[T k, T (k+1))` for `k < n` and `a n` after `T n`: `A(t) = ∫₀^t (r − g)` written out. -/
noncomputable def cum (n : ℕ) (a T : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range n, a k * (clampI (T k) (T (k + 1)) t - T k)) + a n * (max t (T n) - T n)

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated `r − g` at the switch date `T j`,
`A(T_j) = ∑_{k<j} a_k (T_{k+1} − T_k)`. -/
noncomputable def cumAt (a T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, a k * (T (k + 1) - T k)

/-- Cochrane (2023), eq. (6.4), p. 196, with finitely many regimes: `x` is continuous on
`[0, ∞)`, solves `x' = a_j x − σ` on each `(T_j, T_{j+1})`, `j < n`, and `x' = a_n x − σ` after
`T_n`. -/
def SolvesPW (n : ℕ) (a T : ℕ → ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    (∀ j < n, ∀ t ∈ Set.Ioo (T j) (T (j + 1)), HasDerivAt x (a j * x t - σ t) t) ∧
    ∀ t, T n < t → HasDerivAt x (a n * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable initial debt-to-GDP ratio with finitely
many regimes, `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
noncomputable def pwPV0 (n : ℕ) (a T : ℕ → ℝ) (σ : ℝ → ℝ) : ℝ := pvA (cum n a T) σ

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution with finitely many regimes. -/
noncomputable def pwSol (n : ℕ) (a T : ℕ → ℝ) (σ : ℝ → ℝ) : ℝ → ℝ := gSol (cum n a T) σ

variable {n : ℕ} {a T : ℕ → ℝ}

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated rate is continuous. -/
theorem cum_continuous (n : ℕ) (a T : ℕ → ℝ) : Continuous (cum n a T) := by
  unfold cum clampI
  fun_prop

/-- Cochrane (2023), §6.4.1, p. 196: on the closed regime `[T_j, T_{j+1}]`, `j < n`, the cumulated
rate is `A(T_j) + a_j (t − T_j)`. -/
theorem cum_eq_regime (hT : Monotone T) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Icc (T j) (T (j + 1))) : cum n a T t = cumAt a T j + a j * (t - T j) := by
  unfold cum cumAt
  rw [← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ n by omega), Finset.sum_range_succ]
  have h1 : ∑ k ∈ Finset.range j, a k * (clampI (T k) (T (k + 1)) t - T k) =
      ∑ k ∈ Finset.range j, a k * (T (k + 1) - T k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ j := Finset.mem_range.1 hk
    have e1 : T (k + 1) ≤ t := (hT hk').trans ht.1
    have e2 : T k ≤ T (k + 1) := hT (Nat.le_succ k)
    unfold clampI
    rw [min_eq_right e1, max_eq_right e2]
  have h2 : ∑ k ∈ Finset.Ico (j + 1) n, a k * (clampI (T k) (T (k + 1)) t - T k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : j + 1 ≤ k := (Finset.mem_Ico.1 hk).1
    have e1 : t ≤ T k := ht.2.trans (hT hk')
    have e2 : t ≤ T (k + 1) := e1.trans (hT (Nat.le_succ k))
    unfold clampI
    rw [min_eq_left e2, max_eq_left e1, sub_self, mul_zero]
  have h3 : clampI (T j) (T (j + 1)) t = t := by
    unfold clampI
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have h4 : max t (T n) = T n := max_eq_right (ht.2.trans (hT (show j + 1 ≤ n by omega)))
  rw [h1, h2, h3, h4]
  ring

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the cumulated rate is
`A(T_n) + a_n (t − T_n)`. -/
theorem cum_eq_last (hT : Monotone T) {t : ℝ} (ht : T n ≤ t) :
    cum n a T t = cumAt a T n + a n * (t - T n) := by
  unfold cum cumAt
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
    have e1 : T (k + 1) ≤ t := (hT hk').trans ht
    unfold clampI
    rw [min_eq_right e1, max_eq_right (hT (Nat.le_succ k))]
  · rw [max_eq_left ht]

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated rate starts at `A(0) = 0` when `T₀ = 0`. -/
theorem cum_zero (hT : Monotone T) (hT0 : T 0 = 0) : cum n a T 0 = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [cum_eq_last hT (le_of_eq hT0), hT0]
    simp [cumAt]
  · rw [cum_eq_regime hT hn ⟨le_of_eq hT0, hT0 ▸ hT (Nat.zero_le 1)⟩, hT0]
    simp [cumAt]

/-- Cochrane (2023), §6.4.1, p. 196: inside the regime `(T_j, T_{j+1})`, `j < n`, the cumulated
rate has derivative `a_j`. -/
theorem cum_hasDerivAt_regime (hT : Monotone T) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Ioo (T j) (T (j + 1))) : HasDerivAt (cum n a T) (a j) t := by
  have hlin : HasDerivAt (fun s => cumAt a T j + a j * (s - T j)) (a j) t := by
    simpa using (((hasDerivAt_id t).sub_const (T j)).const_mul (a j)).const_add (cumAt a T j)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact cum_eq_regime hT hj ⟨hs.1.le, hs.2.le⟩

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the cumulated rate has derivative
`a_n`. -/
theorem cum_hasDerivAt_last (hT : Monotone T) {t : ℝ} (ht : T n < t) :
    HasDerivAt (cum n a T) (a n) t := by
  have hlin : HasDerivAt (fun s => cumAt a T n + a n * (s - T n)) (a n) t := by
    simpa using (((hasDerivAt_id t).sub_const (T n)).const_mul (a n)).const_add (cumAt a T n)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact cum_eq_last hT (le_of_lt hs)

/-- Cochrane (2023), §6.4.1, p. 196: a date `t > 0` that is not a switch date lies inside one
regime `(T_j, T_{j+1})`, `j < n`, or after the last switch. -/
theorem regime_cases (hT0 : T 0 = 0) {t : ℝ} (ht : 0 < t)
    (htS : t ∉ Set.range T) :
    (∃ j < n, t ∈ Set.Ioo (T j) (T (j + 1))) ∨ T n < t := by
  classical
  have hne : ∀ k, T k ≠ t := fun k h => htS ⟨k, h⟩
  by_cases h : ∃ j, j < n ∧ t < T (j + 1)
  · left
    refine ⟨Nat.find h, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2⟩
    have hle : T (Nat.find h) ≤ t := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
      · rw [h0, hT0]; exact ht.le
      · obtain ⟨j', hj'⟩ : ∃ j', Nat.find h = j' + 1 := ⟨Nat.find h - 1, by omega⟩
        have hmin := Nat.find_min h (show j' < Nat.find h by omega)
        have hj'n : j' < n := by have := (Nat.find_spec h).1; omega
        rw [hj']
        push Not at hmin
        exact hmin hj'n
    exact lt_of_le_of_ne hle (hne _)
  · right
    push Not at h
    have hle : T n ≤ t := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, hT0]; exact ht.le
      · have := h (n - 1) (by omega)
        rwa [show n - 1 + 1 = n by omega] at this
    exact lt_of_le_of_ne hle (hne _)

/-- Cochrane (2023), §6.4.1, p. 196: off the switch dates, for `t > 0`, the cumulated rate has
derivative `deriv A t` (it is differentiable there). -/
theorem cum_hasDerivAt_off (hT : Monotone T) (hT0 : T 0 = 0) {t : ℝ} (ht : 0 < t)
    (htS : t ∉ Set.range T) : HasDerivAt (cum n a T) (deriv (cum n a T) t) t := by
  rcases regime_cases (n := n) hT0 ht htS with ⟨j, hj, hjt⟩ | h
  · exact (cum_hasDerivAt_regime hT hj hjt).differentiableAt.hasDerivAt
  · exact (cum_hasDerivAt_last hT h).differentiableAt.hasDerivAt

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch, `A(t) = A(T_n) + a_n (t − T_n)`. -/
theorem cum_after (hT : Monotone T) (t : ℝ) (ht : T n ≤ t) :
    cum n a T t = cum n a T (T n) + a n * (t - T n) := by
  rw [cum_eq_last hT ht, cum_eq_last hT le_rfl, sub_self, mul_zero, add_zero]

/-- Cochrane (2023), §6.4.1, p. 196: a regime-by-regime solution is a solution with time-varying
`r − g` (off the switch dates). -/
theorem solvesPW_toGen (hT : Monotone T) (hT0 : T 0 = 0) (hx : SolvesPW n a T σ x) :
    SolvesGen (deriv (cum n a T)) (Set.range T) σ x := by
  refine ⟨hx.1, fun t ht htS => ?_⟩
  rcases regime_cases (n := n) hT0 ht htS with ⟨j, hj, hjt⟩ | h
  · rw [(cum_hasDerivAt_regime hT hj hjt).deriv]
    exact hx.2.1 j hj t hjt
  · rw [(cum_hasDerivAt_last hT h).deriv]
    exact hx.2.2 t h

/-- Cochrane (2023), §6.4.1, p. 196 (**existence**): the forward-looking solution solves the
regime-by-regime equation. -/
theorem pwSol_solvesPW (hT : Monotone T) (hσ : Continuous σ) :
    SolvesPW n a T σ (pwSol n a T σ) :=
  ⟨(gSol_continuous hσ (cum_continuous n a T)).continuousOn,
    fun _ hj _ ht => vocA_hasDerivAt hσ (cum_continuous n a T) _ (cum_hasDerivAt_regime hT hj ht),
    fun _ ht => vocA_hasDerivAt hσ (cum_continuous n a T) _ (cum_hasDerivAt_last hT ht)⟩

/-- Cochrane (2023), §6.4.1, p. 196 (**bounded iff sustainable**): with any rates before the last
switch and `r > g` after it, a solution is bounded iff it starts at `x̂₀`. -/
theorem pw_bddOn_iff (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x) : BddOn x ↔ x 0 = pwPV0 n a T σ :=
  gen_bddOn_iff (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx)

/-- Cochrane (2023), §6.4.1, p. 196 ("values of debt different from this forward-looking integral
lead to explosions"), finitely many regimes: a solution not starting at `x̂₀` explodes. -/
theorem pw_tendsto_abs_of_ne (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n)
    (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x)
    (hne : x 0 ≠ pwPV0 n a T σ) : Tendsto (fun t => |x t|) atTop atTop :=
  gen_tendsto_abs_of_ne (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx) hne

/-- Cochrane (2023), §6.4.1, p. 196 (**existence and uniqueness of the sustainable debt**): with
finitely many regimes of any signs and `r > g` after the last switch, the forward-looking solution
is a bounded solution, and every bounded solution equals it at every date `t ≥ 0`. -/
theorem pw_existsUnique (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) :
    SolvesPW n a T σ (pwSol n a T σ) ∧ BddOn (pwSol n a T σ) ∧
      ∀ x, SolvesPW n a T σ x → BddOn x → ∀ t, 0 ≤ t → x t = pwSol n a T σ t := by
  have h := gen_existsUnique (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
  exact ⟨pwSol_solvesPW hT hσ, h.2.1, fun x hx hb t ht =>
    h.2.2 x (solvesPW_toGen hT hT0 hx) hb t ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (**transversality**, finitely many regimes): the debt-to-GDP
ratio discounted at the cumulated `r − g`, `e^{−A(t)} x_t`, tends to `0` iff `x₀ = x̂₀`. -/
theorem pw_tvc_iff (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x) :
    Tendsto (fun t => exp (-cum n a T t) * x t) atTop (𝓝 0) ↔ x 0 = pwPV0 n a T σ :=
  gen_tvc_iff (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx)

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable debt at every date is the forward integral
`x̂_t = ∫_t^∞ exp(−(A(v) − A(t))) σ_v dv`. -/
theorem pwSol_eq_integral (hT : Monotone T) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    pwSol n a T σ t = ∫ v in Set.Ioi t, exp (-(cum n a T v - cum n a T t)) * σ v :=
  gSol_eq_integral (cum_continuous n a T) hσ hM (cum_after hT) ha t

/-- Cochrane (2023), §6.4.1, p. 196 (**the general 20-year formula**): with finitely many regimes,
`x̂₀ = ∑_{k<n} e^{−A(T_k)} ∫_{T_k}^{T_{k+1}} e^{−a_k(v−T_k)} σ_v dv + e^{−A(T_n)} x̂^{(n)}_{T_n}`,
with `A(T_k) = ∑_{j<k} a_j (T_{j+1} − T_j)` and `x̂^{(n)}_{T_n} = ∫₀^∞ e^{−a_n u} σ_{T_n+u} du`. -/
theorem pwPV0_eq_sum (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) :
    pwPV0 n a T σ = (∑ k ∈ Finset.range n, exp (-cumAt a T k) *
        ∫ v in T k..T (k + 1), exp (-a k * (v - T k)) * σ v) +
      exp (-cumAt a T n) * pv (a n) σ (T n) := by
  have hint := integrableOn_expA (cum_continuous n a T) hσ hM (cum_after hT) ha
  have hsplit : pwPV0 n a T σ = (∫ v in (0 : ℝ)..T n, exp (-cum n a T v) * σ v) +
      ∫ v in Set.Ioi (T n), exp (-cum n a T v) * σ v := by
    rw [← integral_Ioi_sub_interval hint (T n)]
    unfold pwPV0 pvA
    ring
  have hc : Continuous fun v => exp (-cum n a T v) * σ v := by
    have := cum_continuous n a T
    fun_prop
  have hfin : (∫ v in (0 : ℝ)..T n, exp (-cum n a T v) * σ v) =
      ∑ k ∈ Finset.range n, exp (-cumAt a T k) *
        ∫ v in T k..T (k + 1), exp (-a k * (v - T k)) * σ v := by
    rw [← hT0, ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hc.intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (hT (Nat.le_succ k))] at hv
    rw [cum_eq_regime hT (Finset.mem_range.1 hk) hv, ← mul_assoc, ← exp_add]
    congr 2
    ring
  have htail : (∫ v in Set.Ioi (T n), exp (-cum n a T v) * σ v) =
      exp (-cumAt a T n) * pv (a n) σ (T n) := by
    have hpv : pv (a n) σ (T n) = ∫ v in Set.Ioi (T n), exp (-a n * (v - T n)) * σ v := by
      rw [pv, ← integral_Ioi_comp_add (fun v => exp (-a n * (v - T n)) * σ v) (T n)]
      congr 1
      funext u
      simp only [add_sub_cancel_left]
    rw [hpv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [cum_eq_last hT (le_of_lt hv), ← mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hsplit, hfin, htail]

/-- Cochrane (2023), §6.4.1, p. 196 (`r > g` in the last regime is necessary): if the last rate is
`a_n ≤ 0`, then with zero surpluses both `0` and `e^{A(t)}` are bounded solutions, and they
differ at date `0`. -/
theorem pw_not_unique_of_last_nonpos (hT : Monotone T) (ha : a n ≤ 0) :
    SolvesPW n a T (fun _ => 0) (fun t => exp (cum n a T t)) ∧
      BddOn (fun t => exp (cum n a T t)) ∧ SolvesPW n a T (fun _ => 0) (fun _ => 0) ∧
      BddOn (fun _ => (0 : ℝ)) ∧ exp (cum n a T 0) ≠ 0 := by
  have hc := cum_continuous n a T
  refine ⟨⟨(by fun_prop : Continuous fun t => exp (cum n a T t)).continuousOn,
    fun j hj t ht => ?_, fun t ht => ?_⟩, ?_, ⟨continuousOn_const, fun j _ t _ => ?_,
    fun t _ => ?_⟩, ⟨0, fun _ _ => by simp⟩, exp_ne_zero _⟩
  · refine (cum_hasDerivAt_regime hT hj ht).exp.congr_deriv ?_
    ring
  · refine (cum_hasDerivAt_last hT ht).exp.congr_deriv ?_
    ring
  · obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T n)).exists_bound_of_continuousOn
      (by fun_prop : Continuous fun t => exp (cum n a T t)).continuousOn
    refine ⟨max C (exp (cumAt a T n)), fun t ht => ?_⟩
    rcases le_total t (T n) with h | h
    · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
    · rw [abs_of_pos (exp_pos _), cum_eq_last hT h]
      refine le_trans ?_ (le_max_right _ _)
      exact exp_le_exp.2 (by nlinarith)
  · simpa using hasDerivAt_const t (0 : ℝ)
  · simpa using hasDerivAt_const t (0 : ℝ)

/-- Cochrane (2023), §6.4.1, p. 196 (**determinacy iff `r > g` in the last regime**): whatever
the signs of `r − g` before the last switch, bounded solutions are unique for every continuous
bounded surplus path iff the last rate is positive. -/
theorem pw_unique_iff_last_pos (hT : Monotone T) (hT0 : T 0 = 0) :
    (∀ σ : ℝ → ℝ, Continuous σ → (∃ M, ∀ u, |σ u| ≤ M) → ∀ x z, SolvesPW n a T σ x →
      SolvesPW n a T σ z → BddOn x → BddOn z → ∀ t, 0 ≤ t → x t = z t) ↔ 0 < a n := by
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    obtain ⟨h1, h2, h3, h4, h5⟩ := pw_not_unique_of_last_nonpos (a := a) hT hneg
    exact h5 (h _ continuous_const ⟨0, fun _ => by simp⟩ _ _ h1 h3 h2 h4 0 le_rfl)
  · rintro ha σ hσ ⟨M, hM⟩ x z hx hz hbx hbz t ht
    have h := (pw_existsUnique hT hT0 ha hσ hM).2.2
    rw [h x hx hbx t ht, h z hz hbz t ht]

/-- Cochrane (2023), §6.4.1, p. 196 (nominal determinacy with finitely many regimes): with nominal
debt `B₀ > 0`, `y₀ > 0`, `P₀ > 0` and `x₀ = B₀/(P₀ y₀)`, there is a bounded solution iff
`P₀ = B₀/(y₀ x̂₀)`. -/
theorem pw_nominal_determinacy (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n)
    (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {B0 y0 P0 : ℝ} (hB0 : 0 < B0) (hy0 : 0 < y0)
    (hP0 : 0 < P0) :
    (∃ x, SolvesPW n a T σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x) ↔
      P0 = B0 / (y0 * pwPV0 n a T σ) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (pw_bddOn_iff hT hT0 ha hσ hM hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pwPV0 n a T σ := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pwPV0 n a T σ := by
      have : 0 < B0 / (y0 * pwPV0 n a T σ) := hP ▸ hP0
      rcases div_pos_iff.1 this with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pwPV0 n a T σ := pos_of_mul_pos_right hpos hy0.le
    obtain ⟨h1, h2, -⟩ := pw_existsUnique hT hT0 ha hσ hM
    refine ⟨pwSol n a T σ, h1, ?_, h2⟩
    have h0 : pwSol n a T σ 0 = pwPV0 n a T σ := vocA_zero (cum_zero hT hT0) _
    rw [h0, hP]
    field_simp

/-! ### The two-regime case of `RvsG` -/

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime rates, `a₁` then `a₂`. -/
noncomputable def twoA (a₁ a₂ : ℝ) (k : ℕ) : ℝ := if k = 0 then a₁ else a₂

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime switch dates, `0` then `T₀`. -/
noncomputable def twoT (T0 : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else T0

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime dates are monotone when `T₀ ≥ 0`. -/
theorem twoT_monotone {T0 : ℝ} (hT0 : 0 ≤ T0) : Monotone (twoT T0) := by
  intro i j hij
  unfold twoT
  split_ifs <;> first | exact le_rfl | exact hT0 | omega

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime solution concept of `RvsG` is the case `n = 1`
of `SolvesPW`. -/
theorem solvesStep_iff (a₁ a₂ T0 : ℝ) (σ x : ℝ → ℝ) :
    SolvesStep a₁ a₂ T0 σ x ↔ SolvesPW 1 (twoA a₁ a₂) (twoT T0) σ x := by
  unfold SolvesStep SolvesPW twoA twoT
  simp only [Nat.lt_one_iff, forall_eq, ↓reduceIte, zero_add, one_ne_zero]

/-- Cochrane (2023), §6.4.1, p. 196 (the corrected 20-year formula is the case `n = 1`): the
general regime sum reduces to `RvsG.stepPV0`. -/
theorem pwPV0_two_regime {a₁ a₂ T0 : ℝ} (hT0 : 0 ≤ T0) (ha₂ : 0 < a₂) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) : pwPV0 1 (twoA a₁ a₂) (twoT T0) σ = stepPV0 a₁ a₂ T0 σ := by
  rw [pwPV0_eq_sum (twoT_monotone hT0) (by simp [twoT]) (by simpa [twoA] using ha₂) hσ hM]
  simp [cumAt, twoA, twoT, stepPV0]

end Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A Gaussian AR(1) surplus process and the debt limit

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197 ("Suppose we
generate the surplus by an AR(1) ... An AR(1) ranges over the entire real line, as does the
integral of an AR(1) ... the future debt-to-GDP ratio ... will eventually exceed any bound").

The book's continuous-time AR(1) needs Itô calculus; this module builds its discrete analogue on a
genuine probability space. On the i.i.d. product space `(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID`
the innovations are the coordinates `ε_t(ω) = ω_t`, `u = ExpectationsMeasureIID.ar1 ρ` is the
AR(1) `u₀ = ε₀`, `u_{t+1} = ρ u_t + ε_{t+1}`, and the surplus-to-GDP ratio is `σ_t = s̄ + u_t`
(`arSurplus`). With `ν = N(0, v)` the process is a Gaussian AR(1): `u_t ~ N(0, v ∑_{j≤t} ρ^{2j})`
(`ar1_hasLaw_gaussian`), `E_t u_{t+1} = ρ u_t` (`E_ar1_succ`). The debt-to-GDP ratio is
`x_{t+1} = γ x_t − σ_t` with `0 ≤ γ < 1` (permanent `r < g`).

## Main results

* `arDebt_adapted`: debt `x_{t+1}` is known at `t`.
* `integral_abs_ar1_le`, `integral_abs_arDebt_le`: uniform `L¹` bounds for `|ρ| < 1`.
* `prob_exceeds_ar`: `P(x_{t+2} > M) ≥ q > 0` uniformly in `t` (Markov's inequality and the
  independence of `ε_{t+1}` from `𝓕_t`).
* `arDebt_shift`, `dseq_tendsto`: restarted at `N`, debt is a function of the innovations after
  `N` plus a term that vanishes, so the events below are tail events.
* `ar1_unbounded_of_integrable` (Kolmogorov's 0-1 law): for integrable innovations with deficits of
  every size, debt is a.s. unbounded above.
* **`gaussian_ar1_unbounded`, `gaussian_ar1_not_sustainable`**: with a Gaussian AR(1) surplus
  (`|ρ| < 1`, `v ≠ 0`, any mean `s̄`), almost surely the debt-to-GDP ratio exceeds every level
  infinitely often, so no debt limit is sustainable; `gaussian_ar1_exp_unbounded` for
  `ρ = e^{−η}`, the decay of the book's `ds = −η(s − s̄)dt + σ dz` over one period.
* `arSurplus_not_ae_bdd_above`: the surplus is not bounded above, so Theorem S
  (`DebtLimitStochastic.frequently_exceeds`) does not apply and the 0-1 argument is needed.
-/

namespace Cochrane.FiscalConstraints.TidyR5GaussianAR1

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  LognormalGrowthMeasure
open AggregateUncertaintyMeasure (integrable_coord_fun measurable_coord_future)

/-- Cochrane (2023), p. 197: the AR(1) surplus-to-GDP ratio `σ_t = s̄ + u_t`, with
`u = ExpectationsMeasureIID.ar1 ρ`. -/
noncomputable def arSurplus (ρ sbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := sbar + ar1 ρ t ω

/-- Cochrane (2023), p. 197: the AR(1) law of motion pointwise,
`u_{t+1} = ρ u_t + ε_{t+1}`. -/
theorem ar1_succ_apply (ρ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    ar1 ρ (t + 1) ω = ρ * ar1 ρ t ω + ω (t + 1) := rfl

/-- Cochrane (2023), p. 197: the surplus is an AR(1) around `s̄`:
`σ_{t+1} − s̄ = ρ(σ_t − s̄) + ε_{t+1}`. -/
theorem arSurplus_succ (ρ sbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    arSurplus ρ sbar (t + 1) ω - sbar = ρ * (arSurplus ρ sbar t ω - sbar) + ω (t + 1) := by
  unfold arSurplus
  rw [ar1_succ_apply]
  ring

/-- Cochrane (2023), p. 197: the AR(1) is measurable. -/
theorem measurable_ar1 (ρ : ℝ) (t : ℕ) : Measurable (ar1 ρ t) := by
  induction t with
  | zero => exact measurable_pi_apply 0
  | succ t ih => exact (ih.const_mul ρ).add (measurable_pi_apply (t + 1))

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), p. 197: the AR(1) `u_t` is known at date `t`. -/
theorem measurable_ar1_F (ρ : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (ar1 ρ t) :=
  (ar1_adapted ν ρ t).measurable

variable (ν) in
/-- Cochrane (2023), (6.4) p. 196 and p. 197: with AR(1) surpluses the debt ratio `x_{t+1}` is
known at date `t`. -/
theorem arDebt_adapted (γ x₀ ρ sbar : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (debtPath γ x₀ (arSurplus ρ sbar) (t + 1)) :=
  measurable_debtPath γ x₀ (t + 1) fun s hs =>
    ((measurable_ar1_F ν ρ s).mono ((iidSystem ν).𝓕.mono (by omega)) le_rfl).const_add sbar

/-- Cochrane (2023), (6.4) p. 196: with AR(1) surpluses the debt ratio is measurable. -/
theorem measurable_arDebt (γ x₀ ρ sbar : ℝ) (t : ℕ) :
    Measurable (debtPath γ x₀ (arSurplus ρ sbar) t) :=
  measurable_debtPath γ x₀ t fun s _ => (measurable_ar1 ρ s).const_add sbar

/-! ### The Gaussian AR(1) -/

/-- Cochrane (2023), p. 197: the squared AR(1) coefficient `ρ²` as a nonnegative real. -/
def rho2 (ρ : ℝ) : NNReal := ⟨ρ ^ 2, sq_nonneg ρ⟩

/-- Cochrane (2023), p. 197: the variance of the Gaussian AR(1) at date `t`,
`v ∑_{j ≤ t} ρ^{2j}`. -/
noncomputable def arVar (ρ : ℝ) (v : NNReal) (t : ℕ) : NNReal :=
  v * ∑ j ∈ Finset.range (t + 1), rho2 ρ ^ j

/-- Cochrane (2023), p. 197 (**the process is a Gaussian AR(1)**): with innovations `N(0, v)`,
`u_t ~ N(0, v ∑_{j ≤ t} ρ^{2j})`. -/
theorem ar1_hasLaw_gaussian (ρ : ℝ) (v : NNReal) (t : ℕ) :
    HasLaw (ar1 ρ t) (gaussianReal 0 (arVar ρ v t)) (iidSystem (gaussianProb 0 v)).μ := by
  have hshock : ∀ k, HasLaw (fun ω : ℕ → ℝ => ω k) (gaussianReal 0 v)
      (iidSystem (gaussianProb 0 v)).μ := fun k =>
    ⟨(measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval _ k⟩
  induction t with
  | zero =>
    have h : arVar ρ v 0 = v := by simp [arVar]
    rw [h]
    exact hshock 0
  | succ t ih =>
    have h1 : HasLaw (fun ω => ρ * ar1 ρ t ω)
        (gaussianReal (ρ * 0) (rho2 ρ * arVar ρ v t))
        (iidSystem (gaussianProb 0 v)).μ :=
      HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul ρ⟩ ih
    have hind : IndepFun (fun ω => ρ * ar1 ρ t ω) (fun ω : ℕ → ℝ => ω (t + 1))
        (iidSystem (gaussianProb 0 v)).μ := by
      rw [IndepFun_iff_Indep]
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
        (indep_future (gaussianProb 0 v) t).symm ?_) ?_
      · exact (((measurable_ar1_F (gaussianProb 0 v) ρ t).const_mul ρ)).comap_le
      · exact (measurable_coord_future (Nat.lt_succ_self t)).comap_le
    have h := gaussianReal_add_gaussianReal_of_indepFun hind h1 (hshock (t + 1))
    have hv : arVar ρ v (t + 1) = rho2 ρ * arVar ρ v t + v := by
      unfold arVar
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    rw [mul_zero, zero_add] at h
    rw [hv]
    refine ⟨(measurable_ar1 ρ (t + 1)).aemeasurable, ?_⟩
    rw [← h]
    rfl

/-- Cochrane (2023), p. 197: the AR(1) variance is nonzero when the innovation variance is. -/
theorem arVar_ne_zero (ρ : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℕ) : arVar ρ v t ≠ 0 := by
  unfold arVar
  refine mul_ne_zero hv ?_
  rw [Finset.sum_range_succ']
  simp

/-- Cochrane (2023), p. 197 ("an AR(1) ranges over the entire real line"): a Gaussian AR(1)
surplus is not almost surely bounded above at any date, so the bounded-above hypothesis of
Theorem S (`DebtLimitStochastic.frequently_exceeds`) fails. -/
theorem arSurplus_not_ae_bdd_above (ρ sbar : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℕ) (K : ℝ) :
    ¬ ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, arSurplus ρ sbar t ω ≤ K := by
  intro h
  have h0 : (iidSystem (gaussianProb 0 v)).μ (ar1 ρ t ⁻¹' Set.Ioi (K - sbar)) = 0 := by
    rw [ae_iff] at h
    have hs : {ω | ¬ arSurplus ρ sbar t ω ≤ K} = ar1 ρ t ⁻¹' Set.Ioi (K - sbar) := by
      ext ω
      simp only [arSurplus, Set.mem_ofPred_eq, not_le, Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro h <;> linarith
    rwa [hs] at h
  rw [← Measure.map_apply (measurable_ar1 ρ t) measurableSet_Ioi,
    (ar1_hasLaw_gaussian ρ v t).map_eq] at h0
  have h2 := gaussianReal_absolutelyContinuous' 0 (arVar_ne_zero ρ hv t) h0
  rw [Real.volume_Ioi] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (the AR(1) forecast): with mean-zero integrable innovations,
`E_t u_{t+1} = ρ u_t` almost everywhere. -/
theorem E_ar1_succ (hint : Integrable id (ν : Measure ℝ)) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (ρ : ℝ) (t : ℕ) :
    (iidSystem ν).E t (ar1 ρ (t + 1)) =ᵐ[(iidSystem ν).μ] ρ • ar1 ρ t := by
  have hui : ∀ s, Integrable (ar1 ρ s) (iidSystem ν).μ := by
    intro s
    induction s with
    | zero => exact integrable_coord_fun (f := id) hint 0
    | succ s ih => exact (ih.const_mul ρ).add (integrable_coord_fun (f := id) hint (s + 1))
  have hsi : Integrable (shock (t + 1)) (iidSystem ν).μ :=
    integrable_coord_fun (f := id) hint (t + 1)
  rw [ar1_succ]
  filter_upwards [(iidSystem ν).E_add ((hui t).smul ρ) hsi t, (iidSystem ν).E_smul ρ (ar1 ρ t) t,
    E_shock ν t] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, hmean, add_zero,
    (iidSystem ν).E_of_stronglyMeasurable (ar1_adapted ν ρ t) (hui t)]

/-! ### `L¹` bounds and the uniform probability bound -/

/-- Cochrane (2023), p. 197: for `|ρ| < 1` and integrable innovations, every `u_t` is integrable
with `E|u_t| ≤ E|ε|/(1 − |ρ|)`. -/
theorem integral_abs_ar1_le (hint : Integrable id (ν : Measure ℝ)) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ t, Integrable (ar1 ρ t) (iidSystem ν).μ ∧
      ∫ ω, |ar1 ρ t ω| ∂(iidSystem ν).μ ≤ (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) := by
  have h1 : 0 < 1 - |ρ| := by linarith
  have hm0 : 0 ≤ ∫ x, |x| ∂(ν : Measure ℝ) := integral_nonneg fun x => abs_nonneg x
  have hsa : ∀ s, ∫ ω, |ω s| ∂(iidSystem ν).μ = ∫ x, |x| ∂(ν : Measure ℝ) := fun s =>
    integral_shock_fun ν s (f := fun x => |x|) continuous_abs.measurable
  have hsh : ∀ s, Integrable (fun ω : ℕ → ℝ => ω s) (iidSystem ν).μ := fun s =>
    integrable_coord_fun (f := id) hint s
  have hkey : (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) * (1 - |ρ|) = ∫ x, |x| ∂(ν : Measure ℝ) :=
    div_mul_cancel₀ _ h1.ne'
  intro t
  induction t with
  | zero =>
    refine ⟨hsh 0, ?_⟩
    change ∫ ω, |ω 0| ∂(iidSystem ν).μ ≤ _
    rw [hsa 0, le_div_iff₀ h1]
    nlinarith [abs_nonneg ρ]
  | succ t ih =>
    have hI : Integrable (ar1 ρ (t + 1)) (iidSystem ν).μ := (ih.1.const_mul ρ).add (hsh (t + 1))
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |ar1 ρ (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (|ρ| * |ar1 ρ t ω| + |ω (t + 1)|) ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul |ρ|).add (hsh (t + 1)).abs) fun ω => ?_
      rw [ar1_succ_apply]
      calc |ρ * ar1 ρ t ω + ω (t + 1)| ≤ |ρ * ar1 ρ t ω| + |ω (t + 1)| := abs_add_le _ _
        _ = |ρ| * |ar1 ρ t ω| + |ω (t + 1)| := by rw [abs_mul]
    rw [integral_add (ih.1.abs.const_mul |ρ|) (hsh (t + 1)).abs, integral_const_mul,
      hsa] at hle
    nlinarith [mul_le_mul_of_nonneg_left ih.2 (abs_nonneg ρ)]

/-- Cochrane (2023), p. 197: with AR(1) surpluses, `|ρ| < 1` and `0 ≤ γ < 1`, every debt ratio is
integrable with `E|x_t| ≤ |x₀| + (|s̄| + E|ε|/(1 − |ρ|))/(1 − γ)`. -/
theorem integral_abs_arDebt_le (hint : Integrable id (ν : Measure ℝ)) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ t, Integrable (debtPath γ x₀ (arSurplus ρ sbar) t) (iidSystem ν).μ ∧
      ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) t ω| ∂(iidSystem ν).μ ≤
        |x₀| + (|sbar| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|)) / (1 - γ) := by
  set Cu := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hCu
  have h1 : 0 < 1 - γ := by linarith
  have hCu0 : 0 ≤ Cu := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hB0 : 0 ≤ (|sbar| + Cu) / (1 - γ) := div_nonneg (by positivity) h1.le
  have hkey : (|sbar| + Cu) / (1 - γ) * (1 - γ) = |sbar| + Cu := div_mul_cancel₀ _ h1.ne'
  intro t
  induction t with
  | zero =>
    refine ⟨integrable_const x₀, ?_⟩
    change ∫ _, |x₀| ∂(iidSystem ν).μ ≤ _
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  | succ t ih =>
    obtain ⟨hu, hub⟩ := integral_abs_ar1_le hint hρ t
    have hf : debtPath γ x₀ (arSurplus ρ sbar) (t + 1) =
        fun ω => γ * debtPath γ x₀ (arSurplus ρ sbar) t ω - (sbar + ar1 ρ t ω) := by
      funext ω; exact debtPath_succ γ x₀ _ t ω
    have hsI : Integrable (fun ω => sbar + ar1 ρ t ω) (iidSystem ν).μ :=
      (integrable_const sbar).add hu
    have hI : Integrable (debtPath γ x₀ (arSurplus ρ sbar) (t + 1)) (iidSystem ν).μ := by
      rw [hf]; exact (ih.1.const_mul γ).sub hsI
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|))
          ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul γ).add
        ((integrable_const |sbar|).add hu.abs)) fun ω => ?_
      rw [hf]
      calc |γ * debtPath γ x₀ (arSurplus ρ sbar) t ω - (sbar + ar1 ρ t ω)|
          ≤ |γ * debtPath γ x₀ (arSurplus ρ sbar) t ω| + |sbar + ar1 ρ t ω| := abs_sub _ _
        _ ≤ γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|) := by
          rw [abs_mul, abs_of_nonneg hγ0]
          linarith [abs_add_le sbar (ar1 ρ t ω)]
    have e : ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|))
        ∂(iidSystem ν).μ = γ * ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) t ω| ∂(iidSystem ν).μ +
          (|sbar| + ∫ ω, |ar1 ρ t ω| ∂(iidSystem ν).μ) := by
      rw [integral_add (f := fun ω => γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω|)
        (g := fun ω => |sbar| + |ar1 ρ t ω|) (ih.1.abs.const_mul γ)
        ((integrable_const |sbar|).add hu.abs), integral_const_mul,
        integral_add (f := fun _ => |sbar|) (g := fun ω => |ar1 ρ t ω|)
        (integrable_const |sbar|) hu.abs]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [e] at hle
    nlinarith [mul_le_mul_of_nonneg_left ih.2 hγ0, abs_nonneg x₀]

/-- Cochrane (2023), p. 197: with AR(1) surpluses (`|ρ| < 1`), integrable innovations with
deficits of every size and `0 ≤ γ < 1`, the probability that debt exceeds `M` at date `t + 2` is
bounded below by a positive constant uniformly in `t`. Proof: `x_{t+2} = Z_t − s̄ − ε_{t+1}` with
`Z_t = γ x_{t+1} − ρ u_t` known at `t`; Markov's inequality gives `P(Z_t > −D) ≥ 1/2`, and
`ε_{t+1} ≤ −L` is independent of `𝓕_t`. -/
theorem prob_exceeds_ar (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar M : ℝ) :
    ∃ q : ENNReal, q ≠ 0 ∧ ∀ t, q ≤
      (iidSystem ν).μ {ω | M < debtPath γ x₀ (arSurplus ρ sbar) (t + 2) ω} := by
  set Cu := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hCu
  set Cx := |x₀| + (|sbar| + Cu) / (1 - γ) with hCx
  set C := γ * Cx + |ρ| * Cu with hC
  set D := 2 * C + 1 with hD
  set L := M + sbar + D + 1 with hL
  have hCu0 : 0 ≤ Cu := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hCx0 : 0 ≤ Cx := add_nonneg (abs_nonneg _) (div_nonneg (by positivity) (by linarith))
  have hC0 : 0 ≤ C := add_nonneg (mul_nonneg hγ0 hCx0) (mul_nonneg (abs_nonneg ρ) hCu0)
  have hD0 : 0 < D := by linarith
  refine ⟨(ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2),
    mul_ne_zero (hdef L) (by norm_num), fun t => ?_⟩
  obtain ⟨hIx, hbx⟩ := integral_abs_arDebt_le hint hγ0 hγ1 hρ x₀ sbar (t + 1)
  obtain ⟨hIu, hbu⟩ := integral_abs_ar1_le hint hρ t
  set Z : (ℕ → ℝ) → ℝ := fun ω =>
    γ * debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω - ρ * ar1 ρ t ω with hZ
  have hZi : Integrable Z (iidSystem ν).μ := (hIx.const_mul γ).sub (hIu.const_mul ρ)
  have hZb : ∫ ω, |Z ω| ∂(iidSystem ν).μ ≤ C := by
    have hle : ∫ ω, |Z ω| ∂(iidSystem ν).μ ≤ ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) (t + 1)
        ω| + |ρ| * |ar1 ρ t ω|) ∂(iidSystem ν).μ := by
      refine integral_mono hZi.abs ((hIx.abs.const_mul γ).add (hIu.abs.const_mul |ρ|))
        fun ω => ?_
      calc |Z ω| ≤ |γ * debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω| + |ρ * ar1 ρ t ω| :=
            abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hγ0]
    rw [integral_add (hIx.abs.const_mul γ) (hIu.abs.const_mul |ρ|), integral_const_mul,
      integral_const_mul] at hle
    nlinarith [mul_le_mul_of_nonneg_left hbx hγ0, mul_le_mul_of_nonneg_left hbu (abs_nonneg ρ)]
  have hZm : Measurable[(iidSystem ν).𝓕 t] Z :=
    ((arDebt_adapted ν γ x₀ ρ sbar t).const_mul γ).sub ((measurable_ar1_F ν ρ t).const_mul ρ)
  set A := {ω : ℕ → ℝ | -D < Z ω} with hA
  set B := {ω : ℕ → ℝ | ω (t + 1) ≤ -L} with hB
  have hAm : MeasurableSet[(iidSystem ν).𝓕 t] A := measurableSet_lt measurable_const hZm
  have hBm : MeasurableSet[futureSigma t] B :=
    measurableSet_le (measurable_coord_future (by omega)) measurable_const
  have hind := (Indep_iff _ _ _).1 (indep_future ν t) B A hBm hAm
  have hsub : B ∩ A ⊆ {ω | M < debtPath γ x₀ (arSurplus ρ sbar) (t + 2) ω} := by
    rintro ω ⟨hb, ha⟩
    simp only [Set.mem_ofPred_eq, hB, hA, hZ] at hb ha ⊢
    rw [show t + 2 = (t + 1) + 1 by rfl, debtPath_succ]
    have e : arSurplus ρ sbar (t + 1) ω = sbar + (ρ * ar1 ρ t ω + ω (t + 1)) := rfl
    rw [e]
    linarith
  have hBval : (iidSystem ν).μ B = (ν : Measure ℝ) (Set.Iic (-L)) :=
    measure_shock_preimage (t + 1) measurableSet_Iic
  have hAval : ENNReal.ofReal (1 / 2) ≤ (iidSystem ν).μ A := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (iidSystem ν).μ)
      (Eventually.of_forall fun ω => abs_nonneg (Z ω)) hZi.abs D
    have hreal : (iidSystem ν).μ.real {ω | D ≤ |Z ω|} ≤ 1 / 2 := by
      have : D * (iidSystem ν).μ.real {ω | D ≤ |Z ω|} ≤ C := hmk.trans hZb
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hpr := measureReal_nonneg (μ := (iidSystem ν).μ) (s := {ω | D ≤ |Z ω|})
      nlinarith
    have hcompl : Aᶜ ⊆ {ω | D ≤ |Z ω|} := by
      intro ω hω
      simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
      rw [le_abs]; right; linarith
    have hAc : (iidSystem ν).μ.real Aᶜ ≤ 1 / 2 := (measureReal_mono hcompl).trans hreal
    have hAm' : MeasurableSet A := (iidSystem ν).𝓕.le t _ hAm
    rw [measureReal_compl hAm', probReal_univ] at hAc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2)
      ≤ (iidSystem ν).μ B * (iidSystem ν).μ A := by rw [hBval]; gcongr
    _ = (iidSystem ν).μ (B ∩ A) := hind.symm
    _ ≤ _ := measure_mono hsub

/-! ### Tail events -/

/-- Cochrane (2023), p. 197: the AR(1) restarted at `N` from `0`, driven by `ε_{N+1}, ε_{N+2}, …`:
`w_0 = 0`, `w_{s+1} = ρ w_s + ε_{N+s+1}`. -/
noncomputable def ar1From (ρ : ℝ) (N : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | s + 1 => fun ω => ρ * ar1From ρ N s ω + ω (N + s + 1)

/-- Cochrane (2023), p. 197: the deterministic response of debt to the date-`N` AR(1) state,
`d_0 = 0`, `d_{k+1} = γ d_k − ρ^k`. -/
noncomputable def dseq (γ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => γ * dseq γ ρ k - ρ ^ k

/-- Cochrane (2023), p. 197: restarting the AR(1) at `N`, `u_{N+s} = ρ^s u_N + w_s`. -/
theorem ar1_shift (ρ : ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ∀ s, ar1 ρ (N + s) ω = ρ ^ s * ar1 ρ N ω + ar1From ρ N s ω := by
  intro s
  induction s with
  | zero => simp [ar1From]
  | succ s ih =>
    rw [← add_assoc, ar1_succ_apply, ih]
    change _ = _ + (ρ * ar1From ρ N s ω + ω (N + s + 1))
    ring

/-- Cochrane (2023), (6.4) p. 196 and p. 197: restarting the debt recursion at `N`,
`x_{N+k} = γ^k x_N + y_k + u_N d_k`, where `y` is the debt from `0` driven by the surpluses
`s̄ + w_s` (functions of the innovations after `N` only). -/
theorem arDebt_shift (γ x₀ ρ sbar : ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ∀ k, debtPath γ x₀ (arSurplus ρ sbar) (N + k) ω =
      γ ^ k * debtPath γ x₀ (arSurplus ρ sbar) N ω +
        debtPath γ 0 (fun s ω => sbar + ar1From ρ N s ω) k ω + ar1 ρ N ω * dseq γ ρ k := by
  intro k
  induction k with
  | zero => change _ = _ * _ + 0 + _ * 0; simp
  | succ k ih =>
    rw [← add_assoc, debtPath_succ, debtPath_succ, ih]
    unfold arSurplus
    rw [ar1_shift ρ N ω k]
    change _ = _ + _ + ar1 ρ N ω * (γ * dseq γ ρ k - ρ ^ k)
    ring

/-- Cochrane (2023), p. 197: `|d_{j+1}| ≤ (j + 1) m^j` with `m = max γ |ρ|`. -/
theorem abs_dseq_le {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (j : ℕ) :
    |dseq γ ρ (j + 1)| ≤ ((j : ℝ) + 1) * max γ |ρ| ^ j := by
  have hm0 : 0 ≤ max γ |ρ| := le_trans hγ0 (le_max_left _ _)
  induction j with
  | zero => simp [dseq]
  | succ j ih =>
    change |γ * dseq γ ρ (j + 1) - ρ ^ (j + 1)| ≤ _
    have h1 : |γ * dseq γ ρ (j + 1)| ≤ max γ |ρ| * (((j : ℝ) + 1) * max γ |ρ| ^ j) := by
      rw [abs_mul, abs_of_nonneg hγ0]
      exact mul_le_mul (le_max_left _ _) ih (abs_nonneg _) hm0
    have h2 : |ρ ^ (j + 1)| ≤ max γ |ρ| ^ (j + 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg ρ) (le_max_right _ _) _
    calc |γ * dseq γ ρ (j + 1) - ρ ^ (j + 1)| ≤ |γ * dseq γ ρ (j + 1)| + |ρ ^ (j + 1)| :=
          abs_sub _ _
      _ ≤ max γ |ρ| * (((j : ℝ) + 1) * max γ |ρ| ^ j) + max γ |ρ| ^ (j + 1) := add_le_add h1 h2
      _ = (((j + 1 : ℕ) : ℝ) + 1) * max γ |ρ| ^ (j + 1) := by push_cast; ring

/-- Cochrane (2023), p. 197: for `0 ≤ γ < 1` and `|ρ| < 1` the response `d_k` vanishes. -/
theorem dseq_tendsto {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hρ : |ρ| < 1) :
    Tendsto (dseq γ ρ) atTop (𝓝 0) := by
  have hm0 : 0 ≤ max γ |ρ| := le_trans hγ0 (le_max_left _ _)
  have hm1 : max γ |ρ| < 1 := max_lt hγ1 hρ
  have hb : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * max γ |ρ| ^ j) atTop (𝓝 0) := by
    have := (tendsto_self_mul_const_pow_of_lt_one hm0 hm1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hm0 hm1)
    rw [add_zero] at this
    refine this.congr fun j => ?_
    ring
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  exact squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans (abs_dseq_le hγ0 j)) hb

/-- Cochrane (2023), p. 197: the restarted AR(1) `w_s` depends only on the innovations from date
`N` on. -/
theorem measurable_ar1From (ρ : ℝ) (N : ℕ) :
    ∀ s, Measurable[⨆ i ≥ N, coordSigma i] (ar1From ρ N s) := by
  intro s
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
    exact (ih.const_mul ρ).add (Measurable.of_comap_le
      (le_iSup₂ (f := fun i (_ : i ≥ N) => coordSigma i) (N + s + 1) (by omega)))

/-- Cochrane (2023), p. 197 (**debt is a.s. unbounded above with AR(1) surpluses**): with
`u_{t+1} = ρ u_t + ε_{t+1}`, `|ρ| < 1`, i.i.d. integrable innovations with deficits of every size,
any mean `s̄` and `0 ≤ γ < 1`, almost surely the debt ratio exceeds every level infinitely often,
from every initial debt. The events are tail events (`arDebt_shift`, `dseq_tendsto`) of positive
probability (`prob_exceeds_ar`), hence of probability one by Kolmogorov's 0-1 law. -/
theorem ar1_unbounded_of_integrable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus ρ sbar) t ω := by
  set x := debtPath γ x₀ (arSurplus ρ sbar) with hx
  set E : ℝ → Set (ℕ → ℝ) := fun a =>
    {ω | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω} with hE
  have htail : ∀ a, MeasurableSet[limsup coordSigma atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → ℝ) → ℝ := fun k => debtPath γ 0 (fun s ω => sbar + ar1From ρ N s ω) k
      with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, coordSigma i] (y k) := fun k =>
      measurable_debtPath γ 0 k fun s _ => (measurable_ar1From ρ N s).const_add sbar
    have heq : E a = {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < x (N + k) ω :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => x (N + k) ω - y k ω) atTop (𝓝 0) := by
        have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (x N ω)
        have h2 := (dseq_tendsto hγ0 hγ1 hρ).const_mul (ar1 ρ N ω)
        rw [zero_mul] at h1
        rw [mul_zero] at h2
        have h3 := h1.add h2
        rw [add_zero] at h3
        refine h3.congr fun k => ?_
        rw [hx, arDebt_shift]
        simp only [hy]
        ring
      have hdiff' : Tendsto (fun k => y k ω - x (N + k) ω) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near hym a
  have hpos : ∀ a, (iidSystem ν).μ (E a) ≠ 0 := by
    intro a
    obtain ⟨q, hq0, hq⟩ := prob_exceeds_ar hint hdef hγ0 hγ1 hρ x₀ sbar a
    have hfreq := le_measure_frequently (μ := (iidSystem ν).μ)
      (A := fun t => {ω | a < x t ω})
      (fun t => measurableSet_lt measurable_const (measurable_arDebt γ x₀ ρ sbar t)) hq
    have hsub : {ω | ∃ᶠ t in atTop, ω ∈ {ω' | a < x t ω'}} ⊆ E a := by
      intro ω hω m
      refine hω.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    exact hq0 (nonpos_iff_eq_zero.1 ((hfreq.trans (measure_mono hsub)).trans_eq h0))
  have hone : ∀ n : ℕ, ∀ᵐ ω ∂(iidSystem ν).μ, ω ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop coordSigma_le (iIndep_coord ν)
      (htail n) with h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le coordSigma_le)) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ω hω M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hω n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

/-! ### The Gaussian AR(1) surplus -/

/-- Cochrane (2023), p. 197 (**Gaussian AR(1) surpluses: debt is a.s. unbounded above**): with
`σ_t = s̄ + u_t`, `u_{t+1} = ρ u_t + ε_{t+1}`, `|ρ| < 1`, `ε_t` i.i.d. `N(0, v)`, `v ≠ 0`, and
`0 ≤ γ < 1` (`r < g`), almost surely the debt-to-GDP ratio exceeds every level infinitely
often, from every initial debt. -/
theorem gaussian_ar1_unbounded {v : NNReal} (hv : v ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus ρ sbar) t ω := by
  have hint : Integrable id (gaussianReal 0 v) := by
    have h := memLp_id_gaussianReal (μ := 0) (v := v) 1
    rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
    exact h
  exact ar1_unbounded_of_integrable (ν := gaussianProb 0 v) hint (gaussian_Iic_ne_zero 0 hv)
    hγ0 hγ1 hρ x₀ sbar

/-- Cochrane (2023), p. 197 ("the initial value of debt ... is not sustainable", **Gaussian
AR(1)**): for every debt limit `M`, the event that debt stays at or below `M` forever has
probability zero. -/
theorem gaussian_ar1_not_sustainable {v : NNReal} (hv : v ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar M : ℝ) :
    (iidSystem (gaussianProb 0 v)).μ {ω | ∀ t, debtPath γ x₀ (arSurplus ρ sbar) t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussian_ar1_unbounded hv hγ0 hγ1 hρ x₀ sbar] with ω hω hall
  obtain ⟨t, ht⟩ := (hω M).exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197: the book's mean reversion `ds = −η(s − s̄)dt + σ dz` with `η > 0`
decays by `ρ = e^{−η}` per period; with this `ρ` and Gaussian innovations, debt is a.s.
unbounded above. -/
theorem gaussian_ar1_exp_unbounded {v : NNReal} (hv : v ≠ 0) {γ η : ℝ} (hη : 0 < η)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus (Real.exp (-η)) sbar) t ω := by
  have hρ : |Real.exp (-η)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  exact gaussian_ar1_unbounded hv hγ0 hγ1 hρ x₀ sbar

end Cochrane.FiscalConstraints.TidyR5GaussianAR1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Managed surpluses and the determinacy of the price level: the pathwise theory

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "with an
upper limit on debt-to-GDP ratio, we must already imagine a managed surplus process. As debt
starts to grow, the government increases surpluses so as to avoid the boundary ... A plan that
exceeds the bound by a finite amount will lead to an initial price-level rise ... We are back to
global determinacy of the price level". The book specifies no surplus rule. This module specifies
the natural class and proves the path-by-path facts; `TidyR6ManagedSurplusMeasure` adds the
probability.

The debt-to-GDP ratio is `x_{t+1} = γ x_t − σ_t` (`DebtLimitStochastic.debtPath`), with
`γ = (1 + r)/(1 + g)`, `0 < γ < 1` (permanent `r < g`), and `x₀ = B/(P₀ y₀)` set by the initial
price level. A *surplus rule* is `σ_t = F_t(x_t, ω)`, such as the linear rule
`s̄ + u_t + φ (x_t − b̄)` (`linRule`). Its *boundary-avoiding modification* raises the surplus
just enough to keep debt at or below the limit `x̄`: `x_{t+1} = min x̄ (γ x_t − F_t(x_t))`
(`avoidPath`, `avoidSurplus`); the two-sided version also cuts surpluses at a floor `x_{low}`
(`bandPath`, `bandSurplus`); the capped version respects a fiscal capacity `s_{max}`
(`cappedPath`, `cappedSurplus`).

Two readings of "the government manages surpluses":

* **feedback**: the rule responds to the *actual* debt, including debt revalued by the price
  level. Then every initial debt `x₀ ≤ x̄` is sustained on every path
  (`avoidPath_within_iff`, `bandPath_within_iff`, `cappedPath_within_iff`): the price level is
  NOT determined.
* **plan**: the surplus process is the one the rule generates along the government's planned
  debt path `m` from `m₀`, and does not respond to a revaluation of debt by the price level
  (the book's "absent a rise in future surpluses"). Then actual debt is
  `x_t = m_t + γᵗ (x₀ − m₀)` (`plan_debtPath`): `x₀ ≤ m₀` is sustained on every path
  (`plan_within_of_le`), while `x₀ > m₀` breaches the limit at any date the plan touches it
  (`plan_breach_high`), and `x₀ < m₀` breaches a floor the plan touches (`plan_breach_low`).

Also: `not_within_of_capacity` (no surplus rule with capacity `s_{max} < −(1 − γ) x̄` can keep
debt within the limit, on any path), `avoid_hits_of_rule_exceeds` (the modified rule touches
the limit whenever the unmodified rule would have crossed it), the link
`avoidPath_eq_managedPath` to `DebtLimitStochastic.managedPath`, and the price-level conversions.
-/

namespace Cochrane.FiscalConstraints.TidyR6ManagedSurplus

open DebtLimitStochastic

variable {Ω : Type*}

/-! ### Surplus rules and their boundary-avoiding modifications -/

/-- Cochrane (2023), (6.4) p. 196 and p. 197: debt under an unmodified surplus rule
`σ_t = F_t(x_t, ω)`: `x_{t+1} = γ x_t − F_t(x_t, ω)`, `x_0 = x₀`. -/
noncomputable def rulePath (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => γ * rulePath γ F x₀ t ω - F t (rulePath γ F x₀ t ω) ω

/-- Cochrane (2023), p. 197: the linear surplus rule `s_t = s̄ + u_t + φ (x_t − b̄)`: a mean
`s̄`, a shock `u_{t}` and a response `φ` to the deviation of debt from a target `b̄`. -/
def linRule (sbar φ bbar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) (ω : Ω) : ℝ :=
  sbar + u t ω + φ * (x - bbar)

/-- Cochrane (2023), p. 197: under the linear rule, next period's debt before any modification
is `(γ − φ) x − (s̄ − φ b̄ + u_t)`: the response `φ` lowers the effective root to `γ − φ`. -/
theorem linRule_response (γ sbar φ bbar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) (ω : Ω) :
    γ * x - linRule sbar φ bbar u t x ω = (γ - φ) * x - (sbar - φ * bbar + u t ω) := by
  unfold linRule
  ring

/-- Cochrane (2023), p. 197 ("as debt starts to grow, the government increases surpluses so as
to avoid the boundary"): debt under the boundary-avoiding modification of the rule `F`,
`x_{t+1} = min x̄ (γ x_t − F_t(x_t, ω))`. -/
noncomputable def avoidPath (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω =>
      min xbar (γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω)

/-- Cochrane (2023), p. 197: the boundary-avoiding surplus, the rule plus the extra surplus
`max 0 (γ x_t − F_t(x_t) − x̄)` needed to stay at or below `x̄`. -/
noncomputable def avoidSurplus (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  F t (avoidPath γ xbar F x₀ t ω) ω +
    max 0 (γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω - xbar)

/-- Cochrane (2023), p. 197: `min a y = y − max 0 (y − a)`, the cap as a subtracted excess. -/
theorem min_eq_sub_max (a y : ℝ) : min a y = y - max 0 (y - a) := by
  rcases le_total y a with h | h
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring

/-- Cochrane (2023), (6.4) p. 196: the modified path is the debt generated by the modified
surplus, `x_{t+1} = γ x_t − σ_t`. -/
theorem avoidPath_succ_eq (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar F x₀ (t + 1) ω =
      γ * avoidPath γ xbar F x₀ t ω - avoidSurplus γ xbar F x₀ t ω := by
  change min xbar _ = _
  rw [min_eq_sub_max, avoidSurplus]
  ring

/-- Cochrane (2023), p. 197: the modified surplus is the rule's surplus whenever the rule
alone stays within the limit; it departs from the rule only to avoid the boundary. -/
theorem avoidSurplus_eq_rule {γ xbar x₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω ≤ xbar) :
    avoidSurplus γ xbar F x₀ t ω = F t (avoidPath γ xbar F x₀ t ω) ω := by
  rw [avoidSurplus, max_eq_left (by linarith), add_zero]

/-- Cochrane (2023), p. 197: the modified surplus is never below the rule's surplus. -/
theorem rule_le_avoidSurplus (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    F t (avoidPath γ xbar F x₀ t ω) ω ≤ avoidSurplus γ xbar F x₀ t ω :=
  le_add_of_nonneg_right (le_max_left _ _)

/-- Cochrane (2023), p. 197: the earlier managed path `DebtLimitStochastic.managedPath` is the
boundary-avoiding modification of the exogenous rule `σ_t = ε_t` (no feedback on debt). -/
theorem avoidPath_eq_managedPath (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar (fun s _ ω' => ε s ω') x₀ t ω = managedPath γ x₀ xbar ε t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change min xbar (γ * avoidPath γ xbar (fun s _ ω' => ε s ω') x₀ t ω - ε t ω) =
      γ * managedPath γ x₀ xbar ε t ω -
        (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar))
    rw [ih, min_eq_sub_max]
    ring

/-- Cochrane (2023), p. 197: the two-sided modification keeps debt in the band `[x_{low}, x̄]`,
`x_{t+1} = max x_{low} (min x̄ (γ x_t − F_t(x_t, ω)))`. -/
noncomputable def bandPath (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => max xlow
      (min xbar (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: the two-sided surplus: the rule, plus the extra surplus that keeps
debt at or below `x̄`, minus the surplus cut that keeps debt at or above `x_{low}`. -/
noncomputable def bandSurplus (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  F t (bandPath γ xlow xbar F x₀ t ω) ω +
    max 0 (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω - xbar) -
    max 0 (xlow -
      min xbar (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: `max l z = z + max 0 (l − z)`, the floor as an added shortfall. -/
theorem max_eq_add_max (l z : ℝ) : max l z = z + max 0 (l - z) := by
  rcases le_total l z with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- Cochrane (2023), (6.4) p. 196: the band path is the debt generated by the band surplus. -/
theorem bandPath_succ_eq (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    bandPath γ xlow xbar F x₀ (t + 1) ω =
      γ * bandPath γ xlow xbar F x₀ t ω - bandSurplus γ xlow xbar F x₀ t ω := by
  change max xlow (min xbar _) = _
  rw [max_eq_add_max, bandSurplus, min_eq_sub_max xbar]
  ring

/-- Cochrane (2023), p. 197: debt under a boundary-avoiding rule with a fiscal capacity
`s_{max}`: `x_{t+1} = max (γ x_t − s_{max}) (min x̄ (γ x_t − F_t(x_t, ω)))`. -/
noncomputable def cappedPath (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => max (γ * cappedPath γ xbar smax F x₀ t ω - smax)
      (min xbar (γ * cappedPath γ xbar smax F x₀ t ω - F t (cappedPath γ xbar smax F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: the capped boundary-avoiding surplus
`min s_{max} (max F_t(x_t) (γ x_t − x̄))`: the government raises surpluses to avoid the boundary,
but never above its capacity `s_{max}`. -/
noncomputable def cappedSurplus (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  min smax (max (F t (cappedPath γ xbar smax F x₀ t ω) ω)
    (γ * cappedPath γ xbar smax F x₀ t ω - xbar))

/-- Cochrane (2023), (6.4) p. 196: the capped path is the debt generated by the capped
surplus. -/
theorem cappedPath_succ_eq (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    cappedPath γ xbar smax F x₀ (t + 1) ω =
      γ * cappedPath γ xbar smax F x₀ t ω - cappedSurplus γ xbar smax F x₀ t ω := by
  change max _ (min _ _) = _
  rw [cappedSurplus]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Cochrane (2023), p. 197: the capped surplus respects the capacity, `σ_t ≤ s_{max}`. -/
theorem cappedSurplus_le (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    cappedSurplus γ xbar smax F x₀ t ω ≤ smax :=
  min_le_left _ _

/-! ### Feedback: the rule responds to actual debt, and every debt below the limit survives -/

/-- Cochrane (2023), p. 197: the boundary-avoiding modification keeps debt at or below `x̄`
from date 1 on, for every rule, every initial debt and every path. -/
theorem avoidPath_le (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar F x₀ (t + 1) ω ≤ xbar :=
  min_le_left _ _

/-- Cochrane (2023), p. 197 (**feedback rules do not determine the price level**): under the
boundary-avoiding modification of ANY rule, debt stays within the limit forever iff the
initial debt is within it, `x₀ ≤ x̄`, on every path. -/
theorem avoidPath_within_iff (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (ω : Ω) :
    (∀ t, avoidPath γ xbar F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    cases t with
    | zero => exact h
    | succ t => exact avoidPath_le γ xbar F x₀ t ω

/-- Cochrane (2023), p. 197: the two-sided modification keeps debt in `[x_{low}, x̄]` from date 1
on, when `x_{low} ≤ x̄`. -/
theorem bandPath_mem {γ xlow xbar : ℝ} (hl : xlow ≤ xbar) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) :
    xlow ≤ bandPath γ xlow xbar F x₀ (t + 1) ω ∧ bandPath γ xlow xbar F x₀ (t + 1) ω ≤ xbar :=
  ⟨le_max_left _ _, max_le hl (min_le_left _ _)⟩

/-- Cochrane (2023), p. 197 (**two-sided feedback rules do not determine the price level**):
debt stays in the band forever iff the initial debt is in the band, on every path. -/
theorem bandPath_within_iff {γ xlow xbar : ℝ} (hl : xlow ≤ xbar) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ)
    (ω : Ω) :
    (∀ t, xlow ≤ bandPath γ xlow xbar F x₀ t ω ∧ bandPath γ xlow xbar F x₀ t ω ≤ xbar) ↔
      xlow ≤ x₀ ∧ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    cases t with
    | zero => exact h
    | succ t => exact bandPath_mem hl F x₀ t ω

/-- Cochrane (2023), p. 197 (**capacity, sufficiency**): with `0 ≤ γ` and capacity
`s_{max} ≥ −(1 − γ) x̄`, the capped boundary-avoiding rule keeps debt within the limit forever iff
`x₀ ≤ x̄`, on every path and for every rule `F`. -/
theorem cappedPath_within_iff {γ xbar smax : ℝ} (hγ0 : 0 ≤ γ) (hfeas : 0 ≤ (1 - γ) * xbar + smax)
    (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (ω : Ω) :
    (∀ t, cappedPath γ xbar smax F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    induction t with
    | zero => exact h
    | succ t ih =>
      change max _ (min _ _) ≤ xbar
      refine max_le ?_ (min_le_left _ _)
      nlinarith [mul_le_mul_of_nonneg_left ih hγ0]

/-- Cochrane (2023), p. 197 (**capacity, necessity**): if every surplus is at most `s_{max}` and
`s_{max} < −(1 − γ) x̄`, with `γ ≤ 1`, then debt cannot stay within the limit forever, on any
path and from any initial debt: even the maximal surplus cannot service debt at the limit. -/
theorem not_within_of_capacity {γ xbar smax x₀ : ℝ} (hγ1 : γ ≤ 1)
    (hcap : (1 - γ) * xbar + smax < 0) {σ : ℕ → Ω → ℝ} {ω : Ω} (hσ : ∀ t, σ t ω ≤ smax) :
    ¬ ∀ t, debtPath γ x₀ σ t ω ≤ xbar := by
  intro h
  set δ := -((1 - γ) * xbar + smax) with hδ
  have hδ0 : 0 < δ := by linarith
  have key : ∀ t : ℕ, xbar - debtPath γ x₀ σ t ω ≤ (xbar - x₀) - t * δ := by
    intro t
    induction t with
    | zero =>
      change xbar - x₀ ≤ _
      simp
    | succ t ih =>
      rw [debtPath_succ]
      have hy := sub_nonneg.2 (h t)
      have h1 : γ * (xbar - debtPath γ x₀ σ t ω) ≤ xbar - debtPath γ x₀ σ t ω := by
        nlinarith
      have h2 := hσ t
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((xbar - x₀) / δ)
  have hk := key n
  have hy := sub_nonneg.2 (h n)
  rw [div_lt_iff₀ hδ0] at hn
  linarith

/-! ### Plans: the surplus does not respond to a revaluation of debt -/

/-- Cochrane (2023), p. 197 ("a higher value of debt, induced by deflation"): if the surplus
process `σ` is the one generated along a planned debt path `m`, `m_{t+1} = γ m_t − σ_t`, then
actual debt from `x₀` is `x_t = m_t + γᵗ (x₀ − m₀)`: a revaluation of initial debt persists,
decaying at rate `γ`. -/
theorem plan_debtPath {γ x₀ : ℝ} {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (t : ℕ) :
    debtPath γ x₀ σ t ω = m t ω + γ ^ t * (x₀ - m 0 ω) := by
  induction t with
  | zero =>
    change x₀ = _
    ring
  | succ t ih =>
    rw [debtPath_succ, ih, hm, pow_succ]
    ring

/-- Cochrane (2023), p. 197: actual debt under the boundary-avoiding plan from `m₀`. -/
theorem avoid_plan_debtPath (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (m₀ x₀ : ℝ) (t : ℕ) (ω : Ω) :
    debtPath γ x₀ (avoidSurplus γ xbar F m₀) t ω =
      avoidPath γ xbar F m₀ t ω + γ ^ t * (x₀ - m₀) :=
  plan_debtPath (fun s => avoidPath_succ_eq γ xbar F m₀ s ω) t

/-- Cochrane (2023), p. 197: actual debt under the two-sided plan from `m₀`. -/
theorem band_plan_debtPath (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (m₀ x₀ : ℝ) (t : ℕ)
    (ω : Ω) :
    debtPath γ x₀ (bandSurplus γ xlow xbar F m₀) t ω =
      bandPath γ xlow xbar F m₀ t ω + γ ^ t * (x₀ - m₀) :=
  plan_debtPath (fun s => bandPath_succ_eq γ xlow xbar F m₀ s ω) t

/-- Cochrane (2023), p. 197 (inflation is not ruled out): if the planned path stays at or below
`x̄` and initial debt is at most the planned `m₀` (a higher price level), actual debt stays at or
below `x̄` forever, for `0 ≤ γ`. -/
theorem plan_within_of_le {γ xbar x₀ : ℝ} (hγ0 : 0 ≤ γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hle : ∀ t, m t ω ≤ xbar) (hx : x₀ ≤ m 0 ω)
    (t : ℕ) : debtPath γ x₀ σ t ω ≤ xbar := by
  rw [plan_debtPath hm]
  have h1 : γ ^ t * (x₀ - m 0 ω) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ0 t) (by linarith)
  linarith [hle t]

/-- Cochrane (2023), p. 197 ("a higher value of debt, induced by deflation, will push the
government over the boundary absent a rise in future surpluses"): for `0 < γ`, if initial debt
exceeds the planned `m₀`, actual debt exceeds `x̄` at every date at which the plan touches `x̄`. -/
theorem plan_breach_high {γ xbar x₀ : ℝ} (hγ : 0 < γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hx : m 0 ω < x₀) {t : ℕ} (ht : m t ω = xbar) :
    xbar < debtPath γ x₀ σ t ω := by
  rw [plan_debtPath hm, ht]
  have : 0 < γ ^ t * (x₀ - m 0 ω) := mul_pos (pow_pos hγ t) (by linarith)
  linarith

/-- Cochrane (2023), p. 197 (the mirror image): for `0 < γ`, if initial debt is below the
planned `m₀`, actual debt falls below `x_{low}` at every date at which the plan touches
`x_{low}`. -/
theorem plan_breach_low {γ xlow x₀ : ℝ} (hγ : 0 < γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hx : x₀ < m 0 ω) {t : ℕ} (ht : m t ω = xlow) :
    debtPath γ x₀ σ t ω < xlow := by
  rw [plan_debtPath hm, ht]
  have : γ ^ t * (x₀ - m 0 ω) < 0 := mul_neg_of_pos_of_neg (pow_pos hγ t) (by linarith)
  linarith

/-! ### When does the plan touch the limit? -/

/-- Cochrane (2023), p. 197: the boundary-avoiding modification touches the limit `x̄` at some
date `t ≥ 1` whenever the unmodified rule from the same initial debt would have reached or
crossed `x̄` at some date `t ≥ 1`: the two paths agree until the first such date. -/
theorem avoid_hits_of_rule_exceeds {γ xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {ω : Ω}
    (h : ∃ t, 1 ≤ t ∧ xbar ≤ rulePath γ F m₀ t ω) :
    ∃ t, 1 ≤ t ∧ avoidPath γ xbar F m₀ t ω = xbar := by
  classical
  obtain ⟨T, hT, hmin⟩ : ∃ T, (1 ≤ T ∧ xbar ≤ rulePath γ F m₀ T ω) ∧
      ∀ s < T, ¬ (1 ≤ s ∧ xbar ≤ rulePath γ F m₀ s ω) :=
    ⟨Nat.find h, Nat.find_spec h, fun s hs => Nat.find_min h hs⟩
  have heq : ∀ s < T, avoidPath γ xbar F m₀ s ω = rulePath γ F m₀ s ω := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have ih' := ih (by omega)
      have hlt : rulePath γ F m₀ (s + 1) ω < xbar :=
        not_le.mp (not_and.mp (hmin (s + 1) hs) (by omega))
      change min xbar (γ * avoidPath γ xbar F m₀ s ω - F s (avoidPath γ xbar F m₀ s ω) ω) = _
      rw [ih']
      exact min_eq_right hlt.le
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
  refine ⟨s + 1, hT.1, ?_⟩
  change min xbar (γ * avoidPath γ xbar F m₀ s ω - F s (avoidPath γ xbar F m₀ s ω) ω) = xbar
  rw [heq s (by omega)]
  exact min_eq_left hT.2

/-- Cochrane (2023), p. 197: the modified path is exactly at the limit next period whenever the
rule alone would carry debt to or above it. -/
theorem avoidPath_succ_eq_xbar {γ xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : xbar ≤ γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω) :
    avoidPath γ xbar F m₀ (t + 1) ω = xbar :=
  min_eq_left h

/-- Cochrane (2023), p. 197: the band path is at the upper edge next period whenever the rule
alone would carry debt to or above `x̄` (for `x_{low} ≤ x̄`). -/
theorem bandPath_succ_eq_xbar {γ xlow xbar m₀ : ℝ} (hl : xlow ≤ xbar) {F : ℕ → ℝ → Ω → ℝ}
    {t : ℕ} {ω : Ω}
    (h : xbar ≤ γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω) :
    bandPath γ xlow xbar F m₀ (t + 1) ω = xbar := by
  change max xlow (min xbar _) = xbar
  rw [min_eq_left h, max_eq_right hl]

/-- Cochrane (2023), p. 197: the band path is at the lower edge next period whenever the rule
alone would carry debt to or below `x_{low}`. -/
theorem bandPath_succ_eq_xlow {γ xlow xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω ≤ xlow) :
    bandPath γ xlow xbar F m₀ (t + 1) ω = xlow := by
  change max xlow (min xbar _) = xlow
  exact max_eq_left ((min_le_right _ _).trans h)

/-- Cochrane (2023), p. 197: the band path stays in `[x_{low}, x̄]` at every date when it starts
there. -/
theorem bandPath_mem_all {γ xlow xbar m₀ : ℝ} (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar)
    (F : ℕ → ℝ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    xlow ≤ bandPath γ xlow xbar F m₀ t ω ∧ bandPath γ xlow xbar F m₀ t ω ≤ xbar :=
  (bandPath_within_iff hl F m₀ ω).2 hm₀ t

/-- Cochrane (2023), p. 197: for `m ∈ [l, h]`, `a m` lies between `min (a l) (a h)` and
`max (a l) (a h)`, whatever the sign of `a`. -/
theorem mul_mem_minmax {a l h m : ℝ} (hlm : l ≤ m) (hmh : m ≤ h) :
    min (a * l) (a * h) ≤ a * m ∧ a * m ≤ max (a * l) (a * h) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlm ha),
      (mul_le_mul_of_nonneg_left hmh ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hmh ha),
      (mul_le_mul_of_nonpos_left hlm ha).trans (le_max_left _ _)⟩

/-! ### Price levels -/

/-- Cochrane (2023), p. 197: with GDP `y₀ > 0` and nominal debt `B`, initial real debt
`B/(P₀ y₀)` is at most `m > 0` iff `P₀ ≥ B/(y₀ m)`: a lower bound on debt is an upper bound on
the price level and vice versa. -/
theorem debt_le_iff_price_ge {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀)
    (hm : 0 < m) : B / (P₀ * y₀) ≤ m ↔ B / (y₀ * m) ≤ P₀ := by
  rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e]

/-- Cochrane (2023), p. 197: initial real debt `B/(P₀ y₀)` equals `m > 0` iff
`P₀ = B/(y₀ m)`. -/
theorem debt_eq_iff_price_eq {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀) (hm : 0 < m) :
    B / (P₀ * y₀) = m ↔ P₀ = B / (y₀ * m) := by
  rw [div_eq_iff (by positivity), eq_div_iff (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e, eq_comm]

/-- Cochrane (2023), p. 197: initial real debt `B/(P₀ y₀)` is at least `m > 0` iff
`P₀ ≤ B/(y₀ m)`. -/
theorem le_debt_iff_price_le {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀) (hm : 0 < m) :
    m ≤ B / (P₀ * y₀) ↔ P₀ ≤ B / (y₀ * m) := by
  rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e]

/-- Cochrane (2023), p. 197: the price level `B/(y₀ m)` is positive and carries initial real
debt exactly to `m`. -/
theorem price_spec {B y₀ m : ℝ} (hB : 0 < B) (hy : 0 < y₀) (hm : 0 < m) :
    0 < B / (y₀ * m) ∧ B / (B / (y₀ * m) * y₀) = m := by
  refine ⟨by positivity, ?_⟩
  field_simp

end Cochrane.FiscalConstraints.TidyR6ManagedSurplus

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Does a managed surplus restore global determinacy? (the i.i.d. and AR(1) processes)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "As debt
starts to grow, the government increases surpluses so as to avoid the boundary. A higher value of
debt, induced by deflation, will push the government over the boundary absent a rise in future
surpluses. A plan that exceeds the bound by a finite amount will lead to an initial price-level
rise ... We are back to global determinacy of the price level and fiscal theory."

The book specifies no rule. We take the linear rule `s_t = s̄ + u_t + φ (x_t − b̄)` (the band
results hold for every `φ`; the one-sided results take `φ ≥ 0`) (`TidyR6ManagedSurplus.linRule`) and
its boundary-avoiding modification, on a genuine probability space: `(ℕ → ℝ, ν^ℕ)` of
`ExpectationsMeasureIID` with innovations `ε_t(ω) = ω_t`, `u = ExpectationsMeasureIID.ar1 ρ` an
AR(1) with `|ρ| < 1` (i.i.d. surpluses are `ρ = 0`, `ar1_zero`; Gaussian AR(1) as in
`TidyR5GaussianAR1`), permanent `r < g` (`0 < γ < 1`), and initial real debt `x₀ = B/(P₀ y₀)`.
Equilibrium (the book's criterion): debt stays within the limit forever, almost surely
(`Sustainable`, `IsEqmPrice`).

## Verdict

* **Sustainability: TRUE.** The modified rule keeps debt at or below `x̄` on every path, and is
  an adapted policy (`plan_adapted`); the unmodified rule does not (`linear_rule_not_sustainable`
  for `0 ≤ φ ≤ γ`, extended to every `φ > γ − 1` by
  `TidyR6LinearRuleBounds.linear_rule_zero_prob`).
* **Deflation is ruled out: TRUE.** If surpluses follow the plan (they do not respond to a
  revaluation of debt by the price level), every initial debt above the plan's `m₀` breaches the
  limit almost surely (`plan_hits`, `plan_sustainable_iff`): `P₀ < P* = B/(y₀ m₀)` is not an
  equilibrium, and `P*` is (existence).
* **Global determinacy (uniqueness): FALSE.** Every `P₀ ≥ P*` is an equilibrium: the equilibrium
  set is exactly `[P*, ∞)` (`plan_eqm_price_iff`, `plan_price_not_unique`). With an upper limit
  only, an initial debt below the plan just melts away (`r < g`). `P*` is the least equilibrium
  price (`plan_price_isLeast`): the book's "the price level rises until the government is again
  able to keep debt below the boundary" is a selection, not a consequence.
* **Feedback rules are worse.** If the rule responds to actual (revalued) debt, every
  `P₀ ≥ B/(y₀ x̄)` is an equilibrium (`feedback_price_iff`), and with a band every `P₀` in an
  interval (`band_feedback_price_iff`, `band_feedback_price_not_unique`).
* **Corrected statement (global determinacy, TRUE):** a two-sided plan, which also cuts surpluses
  to keep debt above a floor `x_{low}` (a band `[x_{low}, x̄]` around the target), with shocks that
  reach both edges (deficits and surpluses of every size, e.g. Gaussian), determines the price
  level uniquely: the only sustainable initial debt is `m₀` (`band_sustainable_iff`) and the
  equilibrium price level exists and is unique, `P₀ = B/(y₀ m₀)` (`band_eqm_price_unique`), for
  every response `φ`. Gaussian AR(1) summaries: `gaussian_plan_verdict`, `gaussian_band_verdict`.

The continuous-time Ornstein–Uhlenbeck surplus of p. 197 needs Itô calculus, which Mathlib lacks;
it is replaced by its discrete analogue, the Gaussian AR(1) (`ρ = e^{−η}` per period in
`TidyR5GaussianAR1.gaussian_ar1_exp_unbounded`).
-/

namespace Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure

open MeasureTheory ProbabilityTheory Filter
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  LognormalGrowthMeasure TidyR5GaussianAR1 TidyR6ManagedSurplus

/-! ### Equilibrium notions -/

/-- Cochrane (2023), p. 197: initial debt `x₀` is sustainable under the surplus process `σ` if
debt stays at or below the limit `x̄` at every date, almost surely. -/
def Sustainable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ) (σ : ℕ → Ω → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t, debtPath γ x₀ σ t ω ≤ xbar

/-- Cochrane (2023), p. 197: initial debt `x₀` is sustainable in the band `[x_{low}, x̄]` under
`σ` if debt stays in the band at every date, almost surely. -/
def BandSustainable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (σ : ℕ → Ω → ℝ) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t, xlow ≤ debtPath γ x₀ σ t ω ∧ debtPath γ x₀ σ t ω ≤ xbar

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level for the surplus plan `σ`, given
nominal debt `B` and GDP `y₀`, if `P₀ > 0` and the initial debt `B/(P₀ y₀)` is sustainable. -/
def IsEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ) (σ : ℕ → Ω → ℝ)
    (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ Sustainable μ γ xbar σ (B / (P₀ * y₀))

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level for the plan `σ` with the band
`[x_{low}, x̄]`. -/
def IsBandEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (σ : ℕ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ BandSustainable μ γ xlow xbar σ (B / (P₀ * y₀))

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level under the boundary-avoiding
modification of the feedback rule `F`, which responds to the actual debt `B/(P₀ y₀)`. -/
def IsFeedbackEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ)
    (F : ℕ → ℝ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ ∀ᵐ ω ∂μ, ∀ t, avoidPath γ xbar F (B / (P₀ * y₀)) t ω ≤ xbar

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level under the two-sided
modification of the feedback rule `F`. -/
def IsBandFeedbackEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (F : ℕ → ℝ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ ∀ᵐ ω ∂μ, ∀ t, xlow ≤ bandPath γ xlow xbar F (B / (P₀ * y₀)) t ω ∧
    bandPath γ xlow xbar F (B / (P₀ * y₀)) t ω ≤ xbar

/-! ### The surplus process -/

/-- Cochrane (2023), p. 197: i.i.d. surplus shocks are the AR(1) with `ρ = 0`: `u_t = ε_t`. -/
theorem ar1_zero (t : ℕ) (ω : ℕ → ℝ) : ar1 0 t ω = ω t := by
  cases t with
  | zero => rfl
  | succ t =>
    change 0 * ar1 0 t ω + ω (t + 1) = ω (t + 1)
    ring

/-- Cochrane (2023), p. 197: the linear rule with i.i.d. shocks is the linear rule with the
`ρ = 0` AR(1). -/
theorem linRule_shock (sbar φ bbar : ℝ) :
    linRule sbar φ bbar shock = linRule sbar φ bbar (ar1 0) := by
  funext t x ω
  simp only [linRule, ar1_zero]
  rfl

/-- Cochrane (2023), p. 197: under the unmodified linear rule with AR(1) shocks, debt is the
debt of `DebtLimitStochastic.debtPath` with root `γ − φ` and AR(1) surplus around `s̄ − φ b̄`. -/
theorem rulePath_linRule (γ sbar φ bbar ρ x₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω =
      debtPath (γ - φ) x₀ (arSurplus ρ (sbar - φ * bbar)) t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change γ * rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω -
      linRule sbar φ bbar (ar1 ρ) t (rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω) ω = _
    rw [linRule_response, ih, debtPath_succ, arSurplus]

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), p. 197 ("we must already imagine a managed surplus process"): the
boundary-avoiding linear plan is an adapted policy: next period's debt `m_{t+1}` and the
surplus `σ_t` are known at date `t`. -/
theorem plan_adapted (γ xbar sbar φ bbar ρ m₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ (t + 1)) ∧
      Measurable[(iidSystem ν).𝓕 t] (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t) := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (avoidPath γ xbar F m₀ t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hu := (measurable_ar1_F ν ρ t).mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hf : avoidPath γ xbar F m₀ (t + 1) = fun ω => min xbar
          (γ * avoidPath γ xbar F m₀ t ω -
            (sbar + ar1 ρ t ω + φ * (avoidPath γ xbar F m₀ t ω - bbar))) := rfl
      rw [hf]
      exact measurable_const.min ((ih'.const_mul γ).sub
        ((hu.const_add sbar).add ((ih'.sub_const bbar).const_mul φ)))
  have hu := measurable_ar1_F ν ρ t
  have hFt : Measurable[(iidSystem ν).𝓕 t] (fun ω => F t (avoidPath γ xbar F m₀ t ω) ω) :=
    (hu.const_add sbar).add (((hx t).sub_const bbar).const_mul φ)
  refine ⟨?_, ?_⟩
  · have hf : avoidPath γ xbar F m₀ (t + 1) = fun ω => min xbar
        (γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω) := rfl
    rw [hf]
    exact measurable_const.min (((hx t).const_mul γ).sub hFt)
  · exact hFt.add (measurable_const.max ((((hx t).const_mul γ).sub hFt).sub measurable_const))

variable (ν) in
/-- Cochrane (2023), p. 197: the two-sided linear plan is an adapted policy as well. -/
theorem band_plan_adapted (γ xlow xbar sbar φ bbar ρ m₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t]
        (bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ (t + 1)) ∧
      Measurable[(iidSystem ν).𝓕 t]
        (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t) := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (bandPath γ xlow xbar F m₀ t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hu := (measurable_ar1_F ν ρ t).mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hf : bandPath γ xlow xbar F m₀ (t + 1) = fun ω => max xlow (min xbar
          (γ * bandPath γ xlow xbar F m₀ t ω -
            (sbar + ar1 ρ t ω + φ * (bandPath γ xlow xbar F m₀ t ω - bbar)))) := rfl
      rw [hf]
      exact measurable_const.max (measurable_const.min ((ih'.const_mul γ).sub
        ((hu.const_add sbar).add ((ih'.sub_const bbar).const_mul φ))))
  have hu := measurable_ar1_F ν ρ t
  have hFt : Measurable[(iidSystem ν).𝓕 t] (fun ω => F t (bandPath γ xlow xbar F m₀ t ω) ω) :=
    (hu.const_add sbar).add (((hx t).sub_const bbar).const_mul φ)
  have hy : Measurable[(iidSystem ν).𝓕 t]
      (fun ω => γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω) :=
    ((hx t).const_mul γ).sub hFt
  refine ⟨?_, ?_⟩
  · have hf : bandPath γ xlow xbar F m₀ (t + 1) = fun ω => max xlow (min xbar
        (γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω)) := rfl
    rw [hf]
    exact measurable_const.max (measurable_const.min hy)
  · exact (hFt.add (measurable_const.max (hy.sub measurable_const))).sub
      (measurable_const.max (measurable_const.sub (measurable_const.min hy)))

/-! ### Shocks of every size recur -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations putting mass on deficits of every
size and `|ρ| < 1`, almost surely the AR(1) falls below every level infinitely often (the
debt theorem `TidyR5GaussianAR1.ar1_unbounded_of_integrable` at `γ = 0`). -/
theorem ar1_frequently_le (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ K : ℝ, ∃ᶠ t in atTop, ar1 ρ t ω ≤ K := by
  have h := ar1_unbounded_of_integrable hint hdef (γ := 0) le_rfl zero_lt_one hρ 0 0
  filter_upwards [h] with ω hω K
  have h1 := (frequently_shift_iff 1).1 (hω (-K))
  refine h1.mono fun k hk => ?_
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, debtPath_succ, arSurplus] at hk
  linarith

/-- Cochrane (2023), p. 197: the law of `−ε` (the mirror image of the innovation law). -/
noncomputable def negLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ν.map fun x => -x

/-- Cochrane (2023), p. 197: flipping the sign of every innovation maps `ν^ℕ` to
`(negLaw ν)^ℕ`. -/
theorem map_neg_iid (ν : ProbabilityMeasure ℝ) :
    (iidSystem ν).μ.map (fun ω i => -ω i) = (iidSystem (negLaw ν)).μ := by
  change (Measure.infinitePi fun _ => (ν : Measure ℝ)).map (fun ω i => -ω i) =
    Measure.infinitePi fun _ => ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ)
  rw [Measure.infinitePi_map_pi _ (f := fun _ x => -x) (fun _ => measurable_neg)]
  rfl

/-- Cochrane (2023), p. 197: the AR(1) driven by `−ε` is `−u`. -/
theorem ar1_neg (ρ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ar1 ρ t (fun i => -ω i) = -ar1 ρ t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ρ * ar1 ρ t (fun i => -ω i) + -ω (t + 1) = -(ρ * ar1 ρ t ω + ω (t + 1))
    rw [ih]
    ring

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations putting mass on surpluses of
every size and `|ρ| < 1`, almost surely the AR(1) rises above every level infinitely often. -/
theorem ar1_frequently_ge (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ K : ℝ, ∃ᶠ t in atTop, K ≤ ar1 ρ t ω := by
  have hint' : Integrable id ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ) := by
    change Integrable id ((ν : Measure ℝ).map fun x => -x)
    rw [integrable_map_measure measurable_id.aestronglyMeasurable measurable_neg.aemeasurable]
    exact hint.neg
  have hdef' : ∀ c : ℝ, ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iic (-c)) ≠ 0 := by
    intro c
    change ((ν : Measure ℝ).map fun x => -x) (Set.Iic (-c)) ≠ 0
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    have e : (fun x : ℝ => -x) ⁻¹' Set.Iic (-c) = Set.Ici c := by
      ext x
      simp
    rw [e]
    exact hup c
  have h := ar1_frequently_le hint' hdef' hρ
  rw [← map_neg_iid] at h
  have hm : Measurable fun (ω : ℕ → ℝ) (i : ℕ) => -ω i :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).neg
  filter_upwards [ae_of_ae_map hm.aemeasurable h] with ω hω K
  refine (hω (-K)).mono fun t ht => ?_
  rw [ar1_neg] at ht
  linarith

/-! ### The plan touches the limit -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations with deficits of every size,
`|ρ| < 1`, `γ < 1` and any response `φ ≥ 0`, the boundary-avoiding linear plan almost surely
touches the limit `x̄` at some date. For `γ − φ ≥ 0` the unmodified rule would be a.s. unbounded
(`TidyR5GaussianAR1.ar1_unbounded_of_integrable`), and the plan meets `x̄` where the rule first
crosses it; for `γ − φ < 0` a large enough deficit shock carries the plan to `x̄` directly. -/
theorem plan_hits (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) (sbar bbar xbar m₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∃ t,
      avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xbar := by
  rcases le_or_gt 0 (γ - φ) with ha | ha
  · have h := ar1_unbounded_of_integrable hint hdef (γ := γ - φ) ha (by linarith) hρ m₀
      (sbar - φ * bbar)
    filter_upwards [h] with ω hω
    obtain ⟨t, ht, ht1⟩ := ((hω xbar).and_eventually (eventually_ge_atTop 1)).exists
    have hr : ∃ t, 1 ≤ t ∧ xbar ≤ rulePath γ (linRule sbar φ bbar (ar1 ρ)) m₀ t ω :=
      ⟨t, ht1, by rw [rulePath_linRule]; exact ht.le⟩
    obtain ⟨s, -, hs⟩ := avoid_hits_of_rule_exceeds hr
    exact ⟨s, hs⟩
  · filter_upwards [ar1_frequently_le hint hdef hρ] with ω hω
    obtain ⟨t, ht, ht1⟩ := ((hω ((γ - φ - 1) * xbar - (sbar - φ * bbar))).and_eventually
      (eventually_ge_atTop 1)).exists
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨s + 1 + 1, avoidPath_succ_eq_xbar ?_⟩
    rw [linRule_response]
    have hm := avoidPath_le γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ s ω
    have h1 := mul_le_mul_of_nonpos_left hm ha.le
    linarith

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations with deficits AND surpluses of
every size and `|ρ| < 1`, the two-sided linear plan from `m₀ ∈ [x_{low}, x̄]` almost surely touches
both edges of the band, for every response `φ` and every `γ`. -/
theorem band_hits (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ : ℝ} (hρ : |ρ| < 1)
    (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (sbar bbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (∃ t, bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xbar) ∧
      ∃ t, bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xlow := by
  filter_upwards [ar1_frequently_le hint hdef hρ, ar1_frequently_ge hint hup hρ] with ω hle hge
  set a := γ - φ
  set c := sbar - φ * bbar
  constructor
  · obtain ⟨t, ht⟩ := (hle (min (a * xlow) (a * xbar) - c - xbar)).exists
    refine ⟨t + 1, bandPath_succ_eq_xbar hl ?_⟩
    rw [linRule_response]
    have hb := bandPath_mem_all (γ := γ) hl hm₀ (linRule sbar φ bbar (ar1 ρ)) ω t
    have hmm := (mul_mem_minmax (a := a) hb.1 hb.2).1
    linarith
  · obtain ⟨t, ht⟩ := (hge (max (a * xlow) (a * xbar) - c - xlow)).exists
    refine ⟨t + 1, bandPath_succ_eq_xlow ?_⟩
    rw [linRule_response]
    have hb := bandPath_mem_all (γ := γ) hl hm₀ (linRule sbar φ bbar (ar1 ρ)) ω t
    have hmm := (mul_mem_minmax (a := a) hb.1 hb.2).2
    linarith

/-! ### One-sided plans: deflation is ruled out, inflation is not -/

/-- **Managed surplus, one-sided limit** (Cochrane (2023), p. 197). With i.i.d. integrable
innovations with deficits of every size, `|ρ| < 1`, `0 < γ < 1` (`r < g`), any response `φ ≥ 0`
and a plan from `m₀ ≤ x̄`: initial debt `x₀` is sustainable under the boundary-avoiding plan iff
`x₀ ≤ m₀`. A deflation (`x₀ > m₀`) breaches the limit almost surely; any inflation (`x₀ < m₀`)
is sustained on every path. -/
theorem plan_sustainable_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ : ℝ} (hm₀ : m₀ ≤ xbar) (x₀ : ℝ) :
    Sustainable (iidSystem ν).μ γ xbar (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔
      x₀ ≤ m₀ := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  constructor
  · intro h
    by_contra hx
    rw [not_le] at hx
    obtain ⟨ω, hω, t, ht⟩ := (h.and (plan_hits hint hdef hρ hγ1 hφ sbar bbar xbar m₀)).exists
    exact absurd (hω t) (not_le.2 (plan_breach_high hγ
      (fun s => avoidPath_succ_eq γ xbar F m₀ s ω) hx ht))
  · intro hx
    exact Eventually.of_forall fun ω t => plan_within_of_le hγ.le
      (fun s => avoidPath_succ_eq γ xbar F m₀ s ω)
      (fun s => (avoidPath_within_iff γ xbar F m₀ ω).2 hm₀ s) hx t

/-- **The equilibrium price levels under a one-sided managed plan** (Cochrane (2023), p. 197):
with nominal debt `B > 0`, GDP `y₀ > 0` and a plan from `0 < m₀ ≤ x̄`, `P₀` is an equilibrium
price level iff `P₀ ≥ P* = B/(y₀ m₀)`. -/
theorem plan_eqm_price_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) (P₀ : ℝ) :
    IsEqmPrice (iidSystem ν).μ γ xbar (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀)
        B y₀ P₀ ↔ B / (y₀ * m₀) ≤ P₀ := by
  constructor
  · rintro ⟨hP, hS⟩
    exact (debt_le_iff_price_ge hy hP hm₀p).1
      ((plan_sustainable_iff hint hdef hρ hγ hγ1 hφ hm₀ _).1 hS)
  · intro hP
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hm₀p)).trans_le hP
    exact ⟨hP0, (plan_sustainable_iff hint hdef hρ hγ hγ1 hφ hm₀ _).2
      ((debt_le_iff_price_ge hy hP0 hm₀p).2 hP)⟩

/-- Cochrane (2023), p. 197 ("a plan that exceeds the bound by a finite amount will lead to an
initial price-level rise ... until the government is again able to keep debt below the
boundary"): `P* = B/(y₀ m₀)` is the LEAST equilibrium price level. -/
theorem plan_price_isLeast (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    IsLeast {P₀ | IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀} (B / (y₀ * m₀)) :=
  ⟨(plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 le_rfl,
    fun _ hP => (plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).1 hP⟩

/-- **Correction** (Cochrane (2023), p. 197, "we are back to global determinacy of the price
level"): under a one-sided managed plan the equilibrium price level is NOT unique: `P*` and
`2 P*` are both equilibria. Only deflation is ruled out. -/
theorem plan_price_not_unique (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    ¬ ∃! P₀, IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hpos : 0 < B / (y₀ * m₀) := div_pos hB (mul_pos hy hm₀p)
  have h1 := hu _ ((plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 le_rfl)
  have h2 := hu (2 * (B / (y₀ * m₀)))
    ((plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 (by linarith))
  linarith

/-! ### Two-sided plans: global determinacy -/

/-- **Managed surplus, two-sided band: global determinacy** (Cochrane (2023), p. 197,
corrected). With i.i.d. integrable innovations with deficits and surpluses of every size,
`|ρ| < 1`, `0 < γ`, any response `φ`, a band `x_{low} ≤ x̄` and a plan from `m₀` in the band: the
only initial debt sustainable in the band under the plan is `x₀ = m₀`. -/
theorem band_sustainable_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (sbar bbar x₀ : ℝ) :
    BandSustainable (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔ x₀ = m₀ := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  constructor
  · intro h
    obtain ⟨ω, hω, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ :=
      (h.and (band_hits (φ := φ) (γ := γ) hint hdef hup hρ hl hm₀ sbar bbar)).exists
    have hm := fun s => bandPath_succ_eq γ xlow xbar F m₀ s ω
    rcases lt_trichotomy x₀ m₀ with hx | hx | hx
    · exact absurd (hω t₂).1 (not_le.2 (plan_breach_low hγ hm hx h₂))
    · exact hx
    · exact absurd (hω t₁).2 (not_le.2 (plan_breach_high hγ hm hx h₁))
  · rintro rfl
    refine Eventually.of_forall fun ω t => ?_
    rw [band_plan_debtPath, sub_self, mul_zero, add_zero]
    exact bandPath_mem_all hl hm₀ F ω t

/-- **Existence and uniqueness of the equilibrium price level under a two-sided managed plan**
(Cochrane (2023), p. 197, corrected): with `B > 0`, `y₀ > 0` and a plan from `m₀ > 0` in the
band, there is exactly one equilibrium price level, `P₀ = B/(y₀ m₀)`. -/
theorem band_eqm_price_unique (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ B y₀ : ℝ}
    (hρ : |ρ| < 1) (hγ : 0 < γ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    ∃! P₀, IsBandEqmPrice (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  obtain ⟨hpos, hspec⟩ := price_spec hB hy hm₀p
  refine ⟨B / (y₀ * m₀), ⟨hpos, ?_⟩, ?_⟩
  · rw [hspec]
    exact (band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar _).2 rfl
  · rintro P ⟨hP, hS⟩
    exact (debt_eq_iff_price_eq hy hP hm₀p).1
      ((band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar _).1 hS)

/-! ### Feedback rules: no determinacy -/

/-- Cochrane (2023), p. 197: on any probability space, under the boundary-avoiding modification
of ANY feedback rule, initial debt is sustainable iff `x₀ ≤ x̄`. -/
theorem feedback_sustainable_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) :
    (∀ᵐ ω ∂μ, ∀ t, avoidPath γ xbar F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := h.exists
    exact (avoidPath_within_iff γ xbar F x₀ ω).1 hω
  · intro hx
    exact Eventually.of_forall fun ω => (avoidPath_within_iff γ xbar F x₀ ω).2 hx

/-- **Correction** (Cochrane (2023), p. 197): if the managed surplus responds to the actual,
revalued debt, the equilibrium price levels are exactly `P₀ ≥ B/(y₀ x̄)`, for any rule `F` on
any probability space (`B > 0`, `y₀ > 0`, `x̄ > 0`). -/
theorem feedback_price_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hx : 0 < xbar) (P₀ : ℝ) :
    IsFeedbackEqmPrice μ γ xbar F B y₀ P₀ ↔ B / (y₀ * xbar) ≤ P₀ := by
  constructor
  · rintro ⟨hP, hS⟩
    exact (debt_le_iff_price_ge hy hP hx).1 ((feedback_sustainable_iff μ γ xbar F _).1 hS)
  · intro hP
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hx)).trans_le hP
    exact ⟨hP0, (feedback_sustainable_iff μ γ xbar F _).2
      ((debt_le_iff_price_ge hy hP0 hx).2 hP)⟩

/-- **Correction** (Cochrane (2023), p. 197): under a boundary-avoiding feedback rule the
equilibrium price level is not unique. -/
theorem feedback_price_not_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hx : 0 < xbar) :
    ¬ ∃! P₀, IsFeedbackEqmPrice μ γ xbar F B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hpos : 0 < B / (y₀ * xbar) := div_pos hB (mul_pos hy hx)
  have h1 := hu _ ((feedback_price_iff μ γ F hB hy hx _).2 le_rfl)
  have h2 := hu (2 * (B / (y₀ * xbar))) ((feedback_price_iff μ γ F hB hy hx _).2 (by linarith))
  linarith

/-- Cochrane (2023), p. 197: under the two-sided modification of ANY feedback rule, on any
probability space, the equilibrium price levels are exactly
`B/(y₀ x̄) ≤ P₀ ≤ B/(y₀ x_{low})` (`0 < x_{low} ≤ x̄`, `B > 0`, `y₀ > 0`). -/
theorem band_feedback_price_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xlow xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hlow : 0 < xlow) (hl : xlow ≤ xbar) (P₀ : ℝ) :
    IsBandFeedbackEqmPrice μ γ xlow xbar F B y₀ P₀ ↔
      B / (y₀ * xbar) ≤ P₀ ∧ P₀ ≤ B / (y₀ * xlow) := by
  have hxbar : 0 < xbar := hlow.trans_le hl
  constructor
  · rintro ⟨hP, hS⟩
    obtain ⟨ω, hω⟩ := hS.exists
    have h0 := (bandPath_within_iff hl F _ ω).1 hω
    exact ⟨(debt_le_iff_price_ge hy hP hxbar).1 h0.2, (le_debt_iff_price_le hy hP hlow).1 h0.1⟩
  · rintro ⟨h1, h2⟩
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hxbar)).trans_le h1
    refine ⟨hP0, Eventually.of_forall fun ω => (bandPath_within_iff hl F _ ω).2 ⟨?_, ?_⟩⟩
    · exact (le_debt_iff_price_le hy hP0 hlow).2 h2
    · exact (debt_le_iff_price_ge hy hP0 hxbar).2 h1

/-- **Correction** (Cochrane (2023), p. 197): even with a band, a feedback rule leaves the price
level indeterminate when `0 < x_{low} < x̄`: `B/(y₀ x̄)` and `B/(y₀ x_{low})` are distinct
equilibrium price levels. -/
theorem band_feedback_price_not_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xlow xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hlow : 0 < xlow) (hl : xlow < xbar) :
    ¬ ∃! P₀, IsBandFeedbackEqmPrice μ γ xlow xbar F B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hxbar : 0 < xbar := hlow.trans hl
  have hlt : B / (y₀ * xbar) < B / (y₀ * xlow) :=
    div_lt_div_of_pos_left hB (mul_pos hy hlow) (mul_lt_mul_of_pos_left hl hy)
  have h1 := hu (B / (y₀ * xbar))
    ((band_feedback_price_iff μ γ F hB hy hlow hl.le _).2 ⟨le_rfl, hlt.le⟩)
  have h2 := hu (B / (y₀ * xlow))
    ((band_feedback_price_iff μ γ F hB hy hlow hl.le _).2 ⟨hlt.le, le_rfl⟩)
  linarith

/-! ### Without the modification: Theorem S persists -/

/-- Cochrane (2023), p. 197: the UNMODIFIED linear rule with a response `0 ≤ φ ≤ γ < 1` does
not make any debt sustainable: with i.i.d. integrable innovations with deficits of every size
and `|ρ| < 1`, for every initial debt `x₀` and every limit `x̄`, debt stays at or below `x̄`
forever with probability zero. -/
theorem linear_rule_not_sustainable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : 0 ≤ φ) (hφγ : φ ≤ γ) (hγ1 : γ < 1) (sbar bbar x₀ xbar : ℝ) :
    (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ar1_unbounded_of_integrable hint hdef (γ := γ - φ) (by linarith)
    (by linarith) hρ x₀ (sbar - φ * bbar)] with ω hω hall
  obtain ⟨t, ht⟩ := (hω xbar).exists
  have := hall t
  rw [rulePath_linRule] at this
  exact absurd this (not_le.2 ht)

/-! ### Gaussian surpluses -/

/-- Cochrane (2023), p. 197: a non-degenerate Gaussian law puts positive mass on surpluses of
every size. -/
theorem gaussian_Ici_ne_zero (m : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal m v (Set.Ici c) ≠ 0 := by
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Ici] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197: Gaussian innovations `N(0, v)` are integrable. -/
theorem gaussian_integrable (v : NNReal) :
    Integrable id ((gaussianProb 0 v : ProbabilityMeasure ℝ) : Measure ℝ) := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) 1
  rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
  exact h

/-- **Verdict, one-sided limit, Gaussian AR(1) surpluses** (Cochrane (2023), §6.4.1, p. 197).
Surpluses `s_t = s̄ + u_t + φ (x_t − b̄)`, `u` a Gaussian AR(1) (`ε_t ~ N(0, v)`, `v ≠ 0`,
`|ρ| < 1`; `ρ = 0` is i.i.d.), `φ ≥ 0`, `0 < γ < 1`, boundary-avoiding modification, plan from
`0 < m₀ ≤ x̄`, `B > 0`, `y₀ > 0`:
(i) the plan keeps debt at or below `x̄` on every path (sustainability);
(ii) the equilibrium price levels are exactly `[B/(y₀ m₀), ∞)` (existence; deflation ruled out);
(iii) the equilibrium price level is NOT unique (no global determinacy);
(iv) if instead the rule responds to actual debt, the equilibrium price levels are exactly
`[B/(y₀ x̄), ∞)`. -/
theorem gaussian_plan_verdict {v : NNReal} (hv : v ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B) (hy : 0 < y₀)
    (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    (∀ ω t, avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ≤ xbar) ∧
    {P₀ | IsEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀} =
        Set.Ici (B / (y₀ * m₀)) ∧
    (¬ ∃! P₀, IsEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀) ∧
    {P₀ | IsFeedbackEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (linRule sbar φ bbar (ar1 ρ)) B y₀ P₀} = Set.Ici (B / (y₀ * xbar)) := by
  have hint := gaussian_integrable v
  have hdef := gaussian_Iic_ne_zero 0 hv
  refine ⟨fun ω => (avoidPath_within_iff γ xbar _ m₀ ω).2 hm₀, ?_,
    plan_price_not_unique hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀, ?_⟩
  · ext P₀
    exact plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ P₀
  · ext P₀
    exact feedback_price_iff _ γ _ hB hy (hm₀p.trans_le hm₀) P₀

/-- **Verdict, two-sided band, Gaussian AR(1) surpluses: global determinacy** (Cochrane (2023),
§6.4.1, p. 197, corrected statement). With the same surpluses and any response `φ`, a band
`x_{low} ≤ x̄` and a two-sided plan from `m₀ ∈ [x_{low}, x̄]`, `m₀ > 0`, `0 < γ`:
(i) debt stays in the band on every path; (ii) the only sustainable initial debt is `m₀`;
(iii) the equilibrium price level exists and is unique, `P₀ = B/(y₀ m₀)`. -/
theorem gaussian_band_verdict {v : NNReal} (hv : v ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) {xlow xbar m₀ B y₀ : ℝ} (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar)
    (hB : 0 < B) (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    (∀ ω t, xlow ≤ bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ∧
      bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ≤ xbar) ∧
    (∀ x₀, BandSustainable (iidSystem (gaussianProb 0 v)).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔ x₀ = m₀) ∧
    ∃! P₀, IsBandEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  have hint := gaussian_integrable v
  have hdef := gaussian_Iic_ne_zero 0 hv
  have hup := gaussian_Ici_ne_zero 0 hv
  exact ⟨fun ω t => bandPath_mem_all hl hm₀ _ ω t,
    fun x₀ => band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar x₀,
    band_eqm_price_unique hint hdef hup hρ hγ hl hm₀ hB hy hm₀p sbar bbar⟩

/-- Cochrane (2023), p. 197, **on the i.i.d. process**: with i.i.d. surplus shocks `ε_t ~ ν`
(integrable, deficits and surpluses of every size) and the two-sided linear plan
`s_t = s̄ + ε_t + φ (m_t − b̄)` modified to the band, the equilibrium price level exists and is
unique; with the one-sided plan the equilibrium price levels are exactly `[B/(y₀ m₀), ∞)`. -/
theorem iid_verdict (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {γ φ xlow xbar m₀ B y₀ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    (∃! P₀, IsBandEqmPrice (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar shock) m₀) B y₀ P₀) ∧
    {P₀ | IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar shock) m₀) B y₀ P₀} =
        Set.Ici (B / (y₀ * m₀)) := by
  have hρ : |(0 : ℝ)| < 1 := by norm_num
  rw [linRule_shock]
  refine ⟨band_eqm_price_unique hint hdef hup hρ hγ hl hm₀ hB hy hm₀p sbar bbar, ?_⟩
  ext P₀
  exact plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀.2 P₀

end Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The unmodified linear surplus rule for every response, and the managed plan below

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197.

Surpluses `s_t = s̄ + u_t + φ (x_t − b̄)` with `u` an AR(1) (`|ρ| < 1`, i.i.d. integrable
innovations `ν` with deficits of every size; Gaussian included) and `0 < γ < 1`. Without the
boundary-avoiding modification debt follows `x_{t+1} = (γ − φ) x_t − (s̄ − φ b̄ + u_t)`
(`TidyR6ManagedSurplusMeasure.rulePath_linRule`).

## Main results

* `linear_rule_ae_unbounded_above`, `linear_rule_zero_prob`: for every response `φ > γ − 1`
  (root `γ − φ < 1`; in particular every `φ ≥ 0`, including `φ > γ`, where the root is negative
  and debt oscillates), debt is almost surely unbounded above, so it stays below any limit with
  probability zero. For `γ − φ ≤ 0` the argument is pathwise (`unbounded_above_of_nonpos`): if
  debt stayed below `M`, then `(γ − φ) x_t ≥ (γ − φ) M`, and a large deficit shock lifts debt
  above `M`.
* `linear_rule_half_prob` (the other side): for `φ < γ − 1` (root `γ − φ > 1`, surpluses CUT
  sharply as debt rises) debt from a low enough initial value stays at or below zero forever
  with probability at least `1/2` (Markov's inequality on the discounted shock sum).
* `linear_rule_not_ae_sustainable`: for every `φ` and every initial debt, debt exceeds any limit
  at date 1 with positive probability, so no unmodified linear rule is sustainable almost surely.
* `plan_unbounded_below_of_frequently`, `plan_ae_unbounded_below`, `plan_debt_ae_unbounded_below`:
  the one-sided boundary-avoiding plan (any `φ`, any `γ`), and actual debt under it, are almost
  surely unbounded below when the innovations have surpluses of every size: the government
  accumulates assets without bound.
-/

namespace Cochrane.FiscalConstraints.TidyR6LinearRuleBounds

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  TidyR5GaussianAR1 TidyR6ManagedSurplus TidyR6ManagedSurplusMeasure

variable {ν : ProbabilityMeasure ℝ}

/-! ### Unmodified rule, root `γ − φ < 1`: unbounded above -/

/-- Cochrane (2023), p. 197: with root `a ≤ 0` (a response `φ ≥ γ`), on any path on which the
AR(1) falls below every level infinitely often, debt `x_{t+1} = a x_t − (c + u_t)` exceeds every
level at some date. -/
theorem unbounded_above_of_nonpos {a c ρ x₀ : ℝ} (ha : a ≤ 0) {ω : ℕ → ℝ}
    (hfreq : ∀ K : ℝ, ∃ᶠ t in atTop, ar1 ρ t ω ≤ K) (M : ℝ) :
    ∃ t, M < debtPath a x₀ (arSurplus ρ c) t ω := by
  by_contra hcon
  have hall : ∀ t, debtPath a x₀ (arSurplus ρ c) t ω ≤ M := fun t =>
    not_lt.1 fun h => hcon ⟨t, h⟩
  obtain ⟨t, ht⟩ := (hfreq ((a - 1) * M - c - 1)).exists
  have h1 := hall (t + 1)
  rw [debtPath_succ, arSurplus] at h1
  have h2 := mul_le_mul_of_nonpos_left (hall t) ha
  linarith

/-- Cochrane (2023), p. 197 (**unmodified linear rule, every response `φ > γ − 1`**): with
i.i.d. integrable innovations with deficits of every size and `|ρ| < 1`, debt under the
unmodified rule is almost surely unbounded above, from every initial debt. -/
theorem linear_rule_ae_unbounded_above (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : γ - 1 < φ) (sbar bbar x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ t,
      M < rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω := by
  rcases le_or_gt 0 (γ - φ) with ha | ha
  · filter_upwards [ar1_unbounded_of_integrable hint hdef (γ := γ - φ) ha (by linarith) hρ x₀
      (sbar - φ * bbar)] with ω hω M
    obtain ⟨t, ht⟩ := (hω M).exists
    exact ⟨t, by rw [rulePath_linRule]; exact ht⟩
  · filter_upwards [ar1_frequently_le hint hdef hρ] with ω hω M
    obtain ⟨t, ht⟩ := unbounded_above_of_nonpos (x₀ := x₀) (c := sbar - φ * bbar) ha.le hω M
    exact ⟨t, by rw [rulePath_linRule]; exact ht⟩

/-- Cochrane (2023), p. 197 (Theorem S for the unmodified linear rule, **every `φ > γ − 1`**,
extending `TidyR6ManagedSurplusMeasure.linear_rule_not_sustainable` beyond `φ ≤ γ`): debt stays
at or below any limit `x̄` forever with probability zero. -/
theorem linear_rule_zero_prob (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : γ - 1 < φ) (sbar bbar x₀ xbar : ℝ) :
    (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [linear_rule_ae_unbounded_above hint hdef hρ hφ sbar bbar x₀] with ω hω hall
  obtain ⟨t, ht⟩ := hω xbar
  exact absurd (hall t) (not_le.2 ht)

/-! ### Unmodified rule, root `γ − φ > 1`: positive probability -/

/-- Cochrane (2023), (6.4) p. 196: for a root `a ≠ 0`,
`x_t = aᵗ (x₀ − ∑_{s<t} a^{−(s+1)} w_s)` solves `x_{t+1} = a x_t − w_t`. -/
theorem debtPath_eq_discounted {a x₀ : ℝ} (ha : a ≠ 0) (w : ℕ → (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    ∀ t, debtPath a x₀ w t ω =
      a ^ t * (x₀ - ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * w s ω) := by
  intro t
  induction t with
  | zero =>
    change x₀ = _
    simp
  | succ t ih =>
    rw [debtPath_succ, ih, Finset.sum_range_succ, pow_succ]
    have e : a ^ t * a * (a⁻¹ ^ (t + 1) * w t ω) = w t ω := by
      rw [inv_pow, pow_succ]
      field_simp
    linear_combination e

/-- Cochrane (2023), p. 197 (**unmodified linear rule with a root above one**, `φ < γ − 1`): with
`a = γ − φ > 1`, i.i.d. integrable innovations, `|ρ| < 1`, and initial debt
`x₀ ≤ −(2 (|s̄ − φ b̄| + E|ε|/(1 − |ρ|))/(a − 1) + 1)`, debt stays at or below zero forever with
probability at least `1/2`. So the linear rule's sustainability depends on `φ`: zero
probability for `φ > γ − 1` (`linear_rule_zero_prob`), positive probability for `φ < γ − 1`. -/
theorem linear_rule_half_prob (hint : Integrable id (ν : Measure ℝ)) {ρ γ φ : ℝ}
    (hρ : |ρ| < 1) (hφ : φ < γ - 1) (sbar bbar x₀ : ℝ)
    (hx₀ : x₀ ≤ -(2 * ((|sbar - φ * bbar| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|)) /
      (γ - φ - 1)) + 1)) :
    ENNReal.ofReal (1 / 2) ≤
      (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ 0} := by
  set a := γ - φ with haDef
  set c := sbar - φ * bbar with hcDef
  set B := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hBdef
  set C := (|c| + B) / (a - 1) with hCdef
  set D := 2 * C + 1 with hDdef
  set μ := (iidSystem ν).μ with hμ
  have ha1 : 0 < a - 1 := by rw [haDef]; linarith
  have ha0 : 0 < a := by linarith
  have hr0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  have hr1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hB0 : 0 ≤ B := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hC0 : 0 ≤ C := div_nonneg (by positivity) ha1.le
  have hD0 : 0 < D := by linarith
  have hu := integral_abs_ar1_le hint hρ
  -- the discounted absolute shock sum up to `T`
  set S : ℕ → (ℕ → ℝ) → ℝ := fun T ω =>
    ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| with hS
  have hterm : ∀ s, Integrable (fun ω => a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω|) μ := fun s =>
    (((integrable_const c).add (hu s).1).abs).const_mul _
  have hSint : ∀ T, Integrable (S T) μ := fun T =>
    integrable_finsetSum _ fun s _ => hterm s
  have hgeo : ∀ T, ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) ≤ 1 / (a - 1) := by
    intro T
    have hsum : Summable fun s : ℕ => a⁻¹ ^ (s + 1) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left a⁻¹ |>.congr fun s => by ring
    calc ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) ≤ ∑' s, a⁻¹ ^ (s + 1) :=
          hsum.sum_le_tsum _ fun s _ => pow_nonneg hr0 _
      _ = a⁻¹ * (1 - a⁻¹)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
          exact tsum_congr fun s => by ring
      _ = 1 / (a - 1) := by field_simp
  have hSle : ∀ T, ∫ ω, S T ω ∂μ ≤ C := by
    intro T
    rw [show ∫ ω, S T ω ∂μ = ∑ s ∈ Finset.range T, ∫ ω, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ∂μ from
      integral_finsetSum _ fun s _ => hterm s]
    calc ∑ s ∈ Finset.range T, ∫ ω, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ∂μ
        ≤ ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) * (|c| + B) := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr0 _)
          calc ∫ ω, |c + ar1 ρ s ω| ∂μ ≤ ∫ ω, (|c| + |ar1 ρ s ω|) ∂μ :=
                integral_mono ((integrable_const c).add (hu s).1).abs
                  ((integrable_const _).add (hu s).1.abs) fun ω => abs_add_le _ _
            _ = |c| + ∫ ω, |ar1 ρ s ω| ∂μ := by
                rw [integral_add (integrable_const _) (hu s).1.abs]
                simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
                rfl
            _ ≤ |c| + B := by linarith [(hu s).2]
      _ = (∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1)) * (|c| + B) := by rw [Finset.sum_mul]
      _ ≤ 1 / (a - 1) * (|c| + B) := mul_le_mul_of_nonneg_right (hgeo T) (by positivity)
      _ = C := by rw [hCdef]; ring
  -- the events "debt at or below zero up to `T`"
  set E : ℕ → Set (ℕ → ℝ) := fun T =>
    {ω | ∀ t ≤ T, debtPath a x₀ (arSurplus ρ c) t ω ≤ 0} with hE
  have hsub : ∀ T, {ω | S T ω < D} ⊆ E T := by
    intro T ω hω t ht
    simp only [Set.mem_ofPred_eq] at hω
    rw [debtPath_eq_discounted ha0.ne']
    refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha0.le t) ?_
    have hmono : ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ≤ S T ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht) fun s _ _ =>
        mul_nonneg (pow_nonneg hr0 _) (abs_nonneg _)
    have habs : -(∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * arSurplus ρ c s ω) ≤
        ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [arSurplus]
      have := neg_abs_le (c + ar1 ρ s ω)
      nlinarith [pow_nonneg hr0 (s + 1)]
    linarith
  have hET : ∀ T, ENNReal.ofReal (1 / 2) ≤ μ (E T) := by
    intro T
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun s _ =>
        mul_nonneg (pow_nonneg hr0 (s + 1)) (abs_nonneg (c + ar1 ρ s ω))) (hSint T) D
    have hreal : μ.real {ω | D ≤ S T ω} ≤ 1 / 2 := by
      have h1 : D * μ.real {ω | D ≤ S T ω} ≤ C := hmk.trans (hSle T)
      have hpr := measureReal_nonneg (μ := μ) (s := {ω | D ≤ S T ω})
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hcompl : {ω | D ≤ S T ω}ᶜ = {ω | S T ω < D} := by
      ext ω
      simp
    have hm : MeasurableSet {ω | D ≤ S T ω} :=
      measurableSet_le measurable_const (Finset.measurable_sum _ fun s _ =>
        (continuous_abs.measurable.comp ((measurable_ar1 ρ s).const_add c)).const_mul _)
    have hlow : 1 / 2 ≤ μ.real {ω | S T ω < D} := by
      rw [← hcompl, measureReal_compl hm, probReal_univ]
      linarith
    calc ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (μ.real {ω | S T ω < D}) :=
          ENNReal.ofReal_le_ofReal hlow
      _ = μ {ω | S T ω < D} := ofReal_measureReal
      _ ≤ μ (E T) := measure_mono (hsub T)
  -- continuity from above
  have hEm : ∀ T, NullMeasurableSet (E T) μ := fun T => by
    have : E T = ⋂ t ∈ Finset.range (T + 1),
        {ω | debtPath a x₀ (arSurplus ρ c) t ω ≤ 0} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
    rw [this]
    exact (Finset.measurableSet_biInter _ fun t _ =>
      measurableSet_le (measurable_arDebt a x₀ ρ c t) measurable_const).nullMeasurableSet
  have hanti : Antitone E := fun T T' h ω hω t ht => hω t (ht.trans h)
  have hlim := tendsto_measure_iInter_atTop hEm hanti ⟨0, measure_ne_top μ _⟩
  have hinter : (⋂ T, E T) =
      {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ 0} := by
    ext ω
    simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq, rulePath_linRule]
    exact ⟨fun h t => h t t le_rfl, fun h T t _ => h t⟩
  rw [← hinter]
  exact ge_of_tendsto' hlim hET

/-- Cochrane (2023), p. 197: for EVERY response `φ` and every initial debt, the unmodified
linear rule carries debt above any limit `x̄` at date 1 with positive probability (deficit shocks
of every size), so no unmodified linear rule is sustainable almost surely. -/
theorem linear_rule_not_ae_sustainable (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (ρ γ φ sbar bbar x₀ xbar : ℝ) :
    ¬ ∀ᵐ ω ∂(iidSystem ν).μ, ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar := by
  intro h
  set K := γ * x₀ - (sbar + φ * (x₀ - bbar)) - xbar - 1 with hK
  have h1 : ∀ᵐ ω ∂(iidSystem ν).μ, ω ∉ shock 0 ⁻¹' Set.Iic K := by
    filter_upwards [h] with ω hω hmem
    have h1 := hω 1
    change γ * x₀ - (sbar + ω 0 + φ * (x₀ - bbar)) ≤ xbar at h1
    simp only [Set.mem_preimage, Set.mem_Iic, shock] at hmem
    linarith
  have h0 := (measure_eq_zero_iff_ae_notMem.2 h1)
  rw [measure_shock_preimage 0 measurableSet_Iic] at h0
  exact hdef (-K) (by rw [neg_neg]; exact h0)

/-! ### The one-sided plan is unbounded below -/

/-- Cochrane (2023), p. 197: on any path on which the AR(1) rises above every level infinitely
often, the one-sided boundary-avoiding plan is unbounded below, for every `γ` and every `φ`. -/
theorem plan_unbounded_below_of_frequently {γ φ ρ sbar bbar xbar m₀ : ℝ} {ω : ℕ → ℝ}
    (hfreq : ∀ K : ℝ, ∃ᶠ t in atTop, K ≤ ar1 ρ t ω) (L : ℝ) :
    ∃ t, avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω < L := by
  set F := linRule sbar φ bbar (ar1 ρ)
  set a := γ - φ
  set U := max xbar m₀
  by_contra hcon
  have hall : ∀ t, L ≤ avoidPath γ xbar F m₀ t ω := fun t => not_lt.1 fun h => hcon ⟨t, h⟩
  have hup : ∀ t, avoidPath γ xbar F m₀ t ω ≤ U := by
    intro t
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (avoidPath_le γ xbar F m₀ t ω).trans (le_max_left _ _)
  obtain ⟨t, ht⟩ := (hfreq (max (a * L) (a * U) - (sbar - φ * bbar) - L + 1)).exists
  have hmm := (mul_mem_minmax (a := a) (hall t) (hup t)).2
  have hstep : avoidPath γ xbar F m₀ (t + 1) ω ≤
      γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω := min_le_right _ _
  rw [linRule_response] at hstep
  have := hall (t + 1)
  linarith

/-- Cochrane (2023), p. 197 (**the one-sided managed plan is a.s. unbounded below**): with i.i.d.
integrable innovations with surpluses of every size and `|ρ| < 1`, for every `γ`, `φ` and `m₀`,
the plan almost surely falls below every level: the government accumulates assets without
bound. -/
theorem plan_ae_unbounded_below (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1)
    (γ φ sbar bbar xbar m₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ L : ℝ, ∃ t,
      avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω < L := by
  filter_upwards [ar1_frequently_ge hint hup hρ] with ω hω L
  exact plan_unbounded_below_of_frequently hω L

/-- Cochrane (2023), p. 197: actual debt `x_t = m_t + γᵗ (x₀ − m₀)` under the one-sided plan,
from any initial debt `x₀`, is almost surely unbounded below too (`0 ≤ γ ≤ 1`). -/
theorem plan_debt_ae_unbounded_below (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ : ℝ} (hρ : |ρ| < 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (φ sbar bbar xbar m₀ x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ L : ℝ, ∃ t,
      debtPath γ x₀ (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) t ω < L := by
  filter_upwards [plan_ae_unbounded_below hint hup hρ γ φ sbar bbar xbar m₀] with ω hω L
  obtain ⟨t, ht⟩ := hω (L - |x₀ - m₀|)
  refine ⟨t, ?_⟩
  rw [avoid_plan_debtPath]
  have hp : γ ^ t ≤ 1 := pow_le_one₀ hγ0 hγ1
  have h1 : γ ^ t * (x₀ - m₀) ≤ |x₀ - m₀| := by
    calc γ ^ t * (x₀ - m₀) ≤ γ ^ t * |x₀ - m₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hγ0 t)
      _ ≤ 1 * |x₀ - m₀| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = |x₀ - m₀| := one_mul _
  linarith

end Cochrane.FiscalConstraints.TidyR6LinearRuleBounds

set_option linter.style.longLine false
#print axioms Cochrane.FiscalConstraints.SchurStable
#print axioms Cochrane.FiscalConstraints.disc
#print axioms Cochrane.FiscalConstraints.root₁
#print axioms Cochrane.FiscalConstraints.root₂
#print axioms Cochrane.FiscalConstraints.root_sum
#print axioms Cochrane.FiscalConstraints.root_prod
#print axioms Cochrane.FiscalConstraints.root_eq
#print axioms Cochrane.FiscalConstraints.normSq_root_of_neg
#print axioms Cochrane.FiscalConstraints.norm_root_of_nonneg
#print axioms Cochrane.FiscalConstraints.schurStable_iff_roots
#print axioms Cochrane.FiscalConstraints.chSeq
#print axioms Cochrane.FiscalConstraints.convSeq
#print axioms Cochrane.FiscalConstraints.convSeq_rec
#print axioms Cochrane.FiscalConstraints.chSeq_eq_convSeq
#print axioms Cochrane.FiscalConstraints.norm_convSeq_le
#print axioms Cochrane.FiscalConstraints.abs_chSeq_le
#print axioms Cochrane.FiscalConstraints.tendsto_chSeq
#print axioms Cochrane.FiscalConstraints.tr2
#print axioms Cochrane.FiscalConstraints.det2
#print axioms Cochrane.FiscalConstraints.tr2_eq_trace
#print axioms Cochrane.FiscalConstraints.det2_eq_det
#print axioms Cochrane.FiscalConstraints.sq_eq_cayleyHamilton
#print axioms Cochrane.FiscalConstraints.pow_succ_eq
#print axioms Cochrane.FiscalConstraints.abs_pow_entry_le
#print axioms Cochrane.FiscalConstraints.tendsto_pow_entry
#print axioms Cochrane.FiscalConstraints.BoundedSeq
#print axioms Cochrane.FiscalConstraints.homogeneous_iterate
#print axioms Cochrane.FiscalConstraints.abs_mulVec_le
#print axioms Cochrane.FiscalConstraints.homogeneous_eq_zero
#print axioms Cochrane.FiscalConstraints.eq_root_of_eq
#print axioms Cochrane.FiscalConstraints.exists_eigenvector
#print axioms Cochrane.FiscalConstraints.exists_bounded_homogeneous
#print axioms Cochrane.FiscalConstraints.ExpectationSystem
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.mk
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.E
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.const
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.mono
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.tower
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.known
#print axioms Cochrane.FiscalConstraints.perfectForesight
#print axioms Cochrane.FiscalConstraints.BoundedProc
#print axioms Cochrane.FiscalConstraints.BoundedVec
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.Adapted
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.IsAR1
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.E_neg
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.E_smul
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.E_E_self
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.abs_E_le
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.bounded_E
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.ar1_iterate
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forward_iterate
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forward_unique
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.E_tsum
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forwardSeries
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.PullOut
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.Solves
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.AdaptedVec
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.system_iterate
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.system_unique
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.system_not_unique
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.Determinate
#print axioms Cochrane.FiscalConstraints.ExpectationSystem.determinate_iff
#print axioms Cochrane.FiscalConstraints.perfectForesight_pullOut
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.FiscalConstraints.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.FiscalConstraints.ForwardSolution.Solves
#print axioms Cochrane.FiscalConstraints.ForwardSolution.E_of_known
#print axioms Cochrane.FiscalConstraints.ForwardSolution.solves_adapted
#print axioms Cochrane.FiscalConstraints.ForwardSolution.iterate_A15
#print axioms Cochrane.FiscalConstraints.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.FiscalConstraints.ForwardSolution.summable_A16
#print axioms Cochrane.FiscalConstraints.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.FiscalConstraints.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.FiscalConstraints.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.FiscalConstraints.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.FiscalConstraints.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.FiscalConstraints.ForwardSolution.ScalarEq
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalarSol
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalarSol_apply
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalarEq_iff
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalar_homog
#print axioms Cochrane.FiscalConstraints.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sunspotFamily
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.FiscalConstraints.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.FiscalConstraints.ForwardSolution.homog_solves
#print axioms Cochrane.FiscalConstraints.ForwardSolution.solves_add_homog
#print axioms Cochrane.FiscalConstraints.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.FiscalConstraints.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.FiscalConstraints.ForwardSolution.existsUnique_iff
#print axioms Cochrane.FiscalConstraints.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.FiscalConstraints.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.FiscalConstraints.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.FiscalConstraints.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.FiscalConstraints.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.FiscalConstraints.ForwardSolution.ar1_decay
#print axioms Cochrane.FiscalConstraints.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.FiscalConstraints.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.FiscalConstraints.ForwardSolution.predetermined_restriction
#print axioms Cochrane.FiscalConstraints.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.FiscalConstraints.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.FiscalConstraints.ForwardSolution.summable_geom_mul
#print axioms Cochrane.FiscalConstraints.ForwardSolution.abel_tsum
#print axioms Cochrane.FiscalConstraints.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.FiscalConstraints.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.FiscalConstraints.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.FiscalConstraints.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.FiscalConstraints.ForwardSolution.E_tsum_dom
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integrableOn_exp_neg_mul
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_exp_neg_mul_Ioi
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_exp_neg_mul_Ioi_zero
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.not_integrableOn_exp_neg_mul
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.exp_growth_eq
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integrableOn_exp_growth
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_exp_growth
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.not_integrableOn_exp_growth
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integrableOn_exp_mul_bdd
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.abs_integral_exp_mul_le
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_Ioi_comp_add
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_exp_shift
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.integral_Ioi_sub_interval
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.intervalIntegral_exp_neg_mul
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.tendsto_const_mul_exp_zero_iff
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.tendsto_const_mul_exp_atTop
#print axioms Cochrane.FiscalConstraints.ExpIntegrals.tvc_of_bounded
#print axioms Cochrane.FiscalConstraints.Laffer.pv_tax_eq
#print axioms Cochrane.FiscalConstraints.Laffer.pv_tax_not_integrable
#print axioms Cochrane.FiscalConstraints.Laffer.output_elasticity
#print axioms Cochrane.FiscalConstraints.Laffer.static_elasticity
#print axioms Cochrane.FiscalConstraints.Laffer.pv_elasticity
#print axioms Cochrane.FiscalConstraints.Laffer.pv_integral_elasticity
#print axioms Cochrane.FiscalConstraints.Laffer.pv_elasticity_zero_of
#print axioms Cochrane.FiscalConstraints.Laffer.pv_elasticity_nonpos_iff
#print axioms Cochrane.FiscalConstraints.Laffer.book_top_of_curve
#print axioms Cochrane.FiscalConstraints.Laffer.log_pv_hasDerivAt_g
#print axioms Cochrane.FiscalConstraints.Laffer.log_pv_hasDerivAt_r
#print axioms Cochrane.FiscalConstraints.Laffer.semi_elasticity_strictAntiOn
#print axioms Cochrane.FiscalConstraints.Laffer.log_tax_ratio_bounds
#print axioms Cochrane.FiscalConstraints.Laffer.book_growth_reduction_bounds
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.euler_discrete_iff
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.marginalValue
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.marginalValue_hasDerivAt
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.euler_continuous_iff
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.euler_exponential_iff
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_of_debt_eq
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_of_debt_not_integrable
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.valueOfDebt
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_indep_of_g
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_hasDerivAt
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_strictAntiOn
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.value_strictMonoOn
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.log_value_hasDerivAt
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.percapita_growth
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.euler_population_iff
#print axioms Cochrane.FiscalConstraints.DiscountGrowth.r_lt_g_population_iff
#print axioms Cochrane.FiscalConstraints.Crash.surplus1
#print axioms Cochrane.FiscalConstraints.Crash.IsEquilibrium
#print axioms Cochrane.FiscalConstraints.Crash.one_add_pos
#print axioms Cochrane.FiscalConstraints.Crash.fisher
#print axioms Cochrane.FiscalConstraints.Crash.valuation
#print axioms Cochrane.FiscalConstraints.Crash.isEquilibrium_iff
#print axioms Cochrane.FiscalConstraints.Crash.unconstrained_regime
#print axioms Cochrane.FiscalConstraints.Crash.constrained_regime
#print axioms Cochrane.FiscalConstraints.Crash.boundary_iff
#print axioms Cochrane.FiscalConstraints.Crash.boundary_iff_debt
#print axioms Cochrane.FiscalConstraints.Crash.price0
#print axioms Cochrane.FiscalConstraints.Crash.price1
#print axioms Cochrane.FiscalConstraints.Crash.price0_eq_left
#print axioms Cochrane.FiscalConstraints.Crash.price0_eq_right
#print axioms Cochrane.FiscalConstraints.Crash.eq_price0
#print axioms Cochrane.FiscalConstraints.Crash.isEquilibrium_price0
#print axioms Cochrane.FiscalConstraints.Crash.exists_equilibrium_iff
#print axioms Cochrane.FiscalConstraints.Crash.price0_unique
#print axioms Cochrane.FiscalConstraints.Crash.degenerate_equilibrium
#print axioms Cochrane.FiscalConstraints.Crash.degenerate_price0_ne
#print axioms Cochrane.FiscalConstraints.Crash.price0_antitoneOn_s0
#print axioms Cochrane.FiscalConstraints.Crash.price0_antitoneOn_i0
#print axioms Cochrane.FiscalConstraints.Crash.price0_monotone_debt
#print axioms Cochrane.FiscalConstraints.Crash.price1_monotoneOn_i0
#print axioms Cochrane.FiscalConstraints.Crash.continuousOn_price0_s0
#print axioms Cochrane.FiscalConstraints.Crash.continuousOn_price0_i0
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price0_s0_unconstrained
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price0_i0_unconstrained
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price1_i0_unconstrained
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price0_s0_constrained
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price0_i0_constrained
#print axioms Cochrane.FiscalConstraints.Crash.hasDerivAt_price1_i0_constrained
#print axioms Cochrane.FiscalConstraints.LinearODE.debt_gdp_ode
#print axioms Cochrane.FiscalConstraints.LinearODE.debt_gdp_discrete
#print axioms Cochrane.FiscalConstraints.LinearODE.vocFrom
#print axioms Cochrane.FiscalConstraints.LinearODE.vocFrom_self
#print axioms Cochrane.FiscalConstraints.LinearODE.vocFrom_hasDerivAt
#print axioms Cochrane.FiscalConstraints.LinearODE.eq_vocFrom
#print axioms Cochrane.FiscalConstraints.LinearODE.solution_unique
#print axioms Cochrane.FiscalConstraints.LinearODE.corrected_6_5
#print axioms Cochrane.FiscalConstraints.LinearODE.printed65
#print axioms Cochrane.FiscalConstraints.LinearODE.printed_6_5_wrong_exponent
#print axioms Cochrane.FiscalConstraints.LinearODE.printed_6_5_wrong_sign
#print axioms Cochrane.FiscalConstraints.LinearODE.finite_horizon_identity
#print axioms Cochrane.FiscalConstraints.LinearODE.vocFrom_eq_of_global
#print axioms Cochrane.FiscalConstraints.LinearODE.forward_present_value
#print axioms Cochrane.FiscalConstraints.RvsG.SolvesOn
#print axioms Cochrane.FiscalConstraints.RvsG.BddOn
#print axioms Cochrane.FiscalConstraints.RvsG.pv
#print axioms Cochrane.FiscalConstraints.RvsG.solvesOn_eq
#print axioms Cochrane.FiscalConstraints.RvsG.vocFrom_solvesOn
#print axioms Cochrane.FiscalConstraints.RvsG.vocFrom_sub
#print axioms Cochrane.FiscalConstraints.RvsG.pv_eq_voc
#print axioms Cochrane.FiscalConstraints.RvsG.abs_pv_le
#print axioms Cochrane.FiscalConstraints.RvsG.pv_hasDerivAt
#print axioms Cochrane.FiscalConstraints.RvsG.pv_solvesOn
#print axioms Cochrane.FiscalConstraints.RvsG.pv_bddOn
#print axioms Cochrane.FiscalConstraints.RvsG.pv_const
#print axioms Cochrane.FiscalConstraints.RvsG.pv_const_not_integrable
#print axioms Cochrane.FiscalConstraints.RvsG.sub_pv
#print axioms Cochrane.FiscalConstraints.RvsG.tendsto_abs_of_ne
#print axioms Cochrane.FiscalConstraints.RvsG.bddOn_iff
#print axioms Cochrane.FiscalConstraints.RvsG.eq_pv_of_bddOn
#print axioms Cochrane.FiscalConstraints.RvsG.existsUnique_bdd
#print axioms Cochrane.FiscalConstraints.RvsG.tvc_iff
#print axioms Cochrane.FiscalConstraints.RvsG.tvc_levels_iff
#print axioms Cochrane.FiscalConstraints.RvsG.nominal_determinacy
#print axioms Cochrane.FiscalConstraints.RvsG.abs_le_of_neg
#print axioms Cochrane.FiscalConstraints.RvsG.bddOn_of_neg
#print axioms Cochrane.FiscalConstraints.RvsG.tendsto_sub_of_neg
#print axioms Cochrane.FiscalConstraints.RvsG.nominal_indeterminacy
#print axioms Cochrane.FiscalConstraints.RvsG.tvc_fails_of_neg
#print axioms Cochrane.FiscalConstraints.RvsG.eq_of_zero
#print axioms Cochrane.FiscalConstraints.RvsG.bddOn_iff_zero
#print axioms Cochrane.FiscalConstraints.RvsG.not_bddOn_zero_const
#print axioms Cochrane.FiscalConstraints.RvsG.SolvesStep
#print axioms Cochrane.FiscalConstraints.RvsG.stepPV0
#print axioms Cochrane.FiscalConstraints.RvsG.pvStep
#print axioms Cochrane.FiscalConstraints.RvsG.stepSol
#print axioms Cochrane.FiscalConstraints.RvsG.vocFrom_sub_from
#print axioms Cochrane.FiscalConstraints.RvsG.vocFrom_stepPV0
#print axioms Cochrane.FiscalConstraints.RvsG.step_after
#print axioms Cochrane.FiscalConstraints.RvsG.step_before
#print axioms Cochrane.FiscalConstraints.RvsG.step_sub_pv
#print axioms Cochrane.FiscalConstraints.RvsG.step_tendsto_abs_of_ne
#print axioms Cochrane.FiscalConstraints.RvsG.step_bddOn_iff
#print axioms Cochrane.FiscalConstraints.RvsG.vocFrom_stepPV0_eq
#print axioms Cochrane.FiscalConstraints.RvsG.stepSol_eq_pvStep
#print axioms Cochrane.FiscalConstraints.RvsG.stepSol_solvesStep
#print axioms Cochrane.FiscalConstraints.RvsG.step_existsUnique
#print axioms Cochrane.FiscalConstraints.RvsG.book_twenty_year_formula
#print axioms Cochrane.FiscalConstraints.RvsG.printed20
#print axioms Cochrane.FiscalConstraints.RvsG.pastOnly
#print axioms Cochrane.FiscalConstraints.RvsG.printed20_wrong
#print axioms Cochrane.FiscalConstraints.RvsG.SolvesD
#print axioms Cochrane.FiscalConstraints.RvsG.BddD
#print axioms Cochrane.FiscalConstraints.RvsG.pvD
#print axioms Cochrane.FiscalConstraints.RvsG.iterD
#print axioms Cochrane.FiscalConstraints.RvsG.gamma_gt_one_iff
#print axioms Cochrane.FiscalConstraints.RvsG.iterD_solves
#print axioms Cochrane.FiscalConstraints.RvsG.solvesD_sub
#print axioms Cochrane.FiscalConstraints.RvsG.abs_pvD_term_le
#print axioms Cochrane.FiscalConstraints.RvsG.summable_pvD
#print axioms Cochrane.FiscalConstraints.RvsG.abs_pvD_le
#print axioms Cochrane.FiscalConstraints.RvsG.pvD_succ
#print axioms Cochrane.FiscalConstraints.RvsG.pvD_solves
#print axioms Cochrane.FiscalConstraints.RvsG.tendsto_abs_of_ne_D
#print axioms Cochrane.FiscalConstraints.RvsG.bddD_iff
#print axioms Cochrane.FiscalConstraints.RvsG.eq_pvD_of_bddD
#print axioms Cochrane.FiscalConstraints.RvsG.tvcD_iff
#print axioms Cochrane.FiscalConstraints.RvsG.abs_le_of_lt_one
#print axioms Cochrane.FiscalConstraints.RvsG.tendsto_sub_D
#print axioms Cochrane.FiscalConstraints.RvsG.eq_of_one
#print axioms Cochrane.FiscalConstraints.RvsG.bddD_iff_one
#print axioms Cochrane.FiscalConstraints.RvsG.nominal_determinacy_D
#print axioms Cochrane.FiscalConstraints.RvsG.nominal_indeterminacy_D
#print axioms Cochrane.FiscalConstraints.RvsG.steady_state_iff
#print axioms Cochrane.FiscalConstraints.RvsG.steady_surplus_continuous
#print axioms Cochrane.FiscalConstraints.RvsG.steady_state_iff_D
#print axioms Cochrane.FiscalConstraints.RvsG.book_flow_basis_point
#print axioms Cochrane.FiscalConstraints.RvsG.book_one_percent_deficit
#print axioms Cochrane.FiscalConstraints.RvsG.zero_surplus_path
#print axioms Cochrane.FiscalConstraints.RvsG.book_growth_out_of_debt
#print axioms Cochrane.FiscalConstraints.RvsG.log_three_bounds
#print axioms Cochrane.FiscalConstraints.RvsG.book_years_bounds
#print axioms Cochrane.FiscalConstraints.RvsG.book_450_bounds
#print axioms Cochrane.FiscalConstraints.RvsG.twenty_years_zero_surplus
#print axioms Cochrane.FiscalConstraints.RvsG.exp_neg_two_tenths_bounds
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.debtPath
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.debtPath_succ
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.debtPath_lower
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.debtPath_run
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.exists_run_length
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.badBlock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.measurableSet_badBlock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.block_index_injOn
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.biInter_badBlock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.measure_biInter_badBlock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.iIndepSet_badBlock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.tsum_badBlock_eq_top
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.frequently_exceeds
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.not_sustainable
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.unbounded_of_unbounded_deficits
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.iid_unbounded
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.gaussian_deficit_pos
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.gaussian_iid_unbounded
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.debtPath_le_of_bounded_deficits
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.bounded_support_counterexample
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.managedPath
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.managedPath_le
#print axioms Cochrane.FiscalConstraints.DebtLimitStochastic.managedPath_eq_of_le
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.consumption
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.marginalUtility
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.consumption_rpow
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.log_marginalUtility
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.hasDerivAt_log_marginalUtility
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.marginalUtility_eq
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.marginalUtility_ratio
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_gt_growth_iff
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_lt_growth_iff
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_gt_growth_of_standard
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_lt_growth_possible
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_term_identity
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_term_eq
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_iff
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_delta_zero_iff
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_diverges_of_lt_one
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_population
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.tvc_population_iff
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.population_allows_r_lt_g
#print axioms Cochrane.FiscalConstraints.GrowthTheoryTVC.rate_population_zero
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.money_growth
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.steady_state_deficit
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.middle_term
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.seigniorage_exceeds_deficit
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.money_return_lt_growth
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.hasDerivAt_moneyRatio
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.hasDerivAt_moneyRatio_rf
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.hasDerivAt_liabilityRatio
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.eq_6_12
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.eq_6_13
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.eq_6_9
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.present_value_unique
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.steady_6_12_explodes
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.steady_6_13_converges
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.tvc_mrs_iff
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.mrs_eq_riskfree
#print axioms Cochrane.FiscalConstraints.MoneyLiquidity.return_discounted_terminal_explodes
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.grossReturn
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.returnDiscount
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.returnPV
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.one_eq_E_inv_mul
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.returnDiscount_succ_mul
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.eq_6_14_pathwise
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.eq_6_14
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.sdf_finite_horizon
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.sdf_finite_horizon_div
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.return_pv_iff_terminal
#print axioms Cochrane.FiscalConstraints.ReturnDiscounting.linear_discount_factor_prices
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.KnownPowers
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.growth
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.IIDGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.ratio
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.pvDisc
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.riskFreeGross
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.known_mul
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.ratio_zero
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.ratio_succ
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.ratio_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.growth_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.ratio_rpow_known
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.E_growth_mul
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.E_ratio_pow_mul
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.riskFree_prices
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.pvTerm
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.correct_term
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.incorrect_term
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.incorrect_ratio_eq
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.summable_geom_succ_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.correct_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.incorrect_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.correct_finite_incorrect_explodes
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.lognormalMoment
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.lognormalMoment_eq_integral
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.lognormal_correct
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.lognormal_incorrect
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.printed_incorrect_wrong
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.correctExponent
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.incorrectExponent
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.printedExponent
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.region_nonempty_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.printed_region_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.region_pos_delta
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.log_riskFree_lognormal
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.log_riskFree_mean_growth
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.printed_bohn_rate_wrong
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.riskFree_lt_growth_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_region
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.rollover_step
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.eq_6_17
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.terminal_c
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.pv_term_c
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.terminal_tendsto_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_pv_hasSum_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_grossReturn
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.eq_6_18_pathwise
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.eq_6_18
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.eq_6_18_diverges
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.coinObsH
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.coinObsH_eq_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnTree
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnSystem
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnSystem_pullOut
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.info_flip
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnTree_condE_coin
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnGrowth_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnC
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnC_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnC_growth
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnSystem_knownPowers
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnMom
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnSystem_iid
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohnMom_values
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_numbers
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_witness_6_17
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_witness_6_18
#print axioms Cochrane.FiscalConstraints.AggregateUncertainty.bohn_witness_terms
#print axioms Cochrane.FiscalConstraints.Links.forward_integral_eq_pv
#print axioms Cochrane.FiscalConstraints.Links.forward_present_value_eq_pv
#print axioms Cochrane.FiscalConstraints.Links.valueOfDebt_eq_pv
#print axioms Cochrane.FiscalConstraints.Links.marginalValue_consumption
#print axioms Cochrane.FiscalConstraints.Links.euler_iff_rate
#print axioms Cochrane.FiscalConstraints.Links.rate_population_lt_growth_iff
#print axioms Cochrane.FiscalConstraints.Links.growth_tvc_term_eq_levels
#print axioms Cochrane.FiscalConstraints.Links.growth_tvc_iff_levels_tvc
#print axioms Cochrane.FiscalConstraints.Links.steady_debt_is_pv
#print axioms Cochrane.FiscalConstraints.Links.growth_tvc_from_rvsg
#print axioms Cochrane.FiscalConstraints.Links.debt_gdp_solvesD
#print axioms Cochrane.FiscalConstraints.Links.debtPath_solvesD
#print axioms Cochrane.FiscalConstraints.Links.debtPath_abs_le
#print axioms Cochrane.FiscalConstraints.Links.gaussian_not_bddD
#print axioms Cochrane.FiscalConstraints.Links.deterministic_rf_lt_g_iff
#print axioms Cochrane.FiscalConstraints.Links.rf_lt_g_pv_finite_needs_risk
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.mk
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.P
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.𝓕
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.μ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddProc
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.integrable
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_add
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_sub
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_smul
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_const
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_zero
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_mono
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_tower
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.integrable_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_of_stronglyMeasurable
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_of_aestronglyMeasurable
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_known
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_E_self
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_congr
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.integral_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_pullOut
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.abs_E_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.of_stronglyMeasurable
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.const
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.add
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.smul
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.sub
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.mul
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_mul_innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.E_hasSum
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.discSum
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.discSum_succ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.discSum_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.discSum_rec
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.aestronglyMeasurable_discSum
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.Solves
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forwardSol
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forwardSol_adapted
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forwardSol_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.iterate_homog
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.forward_unique
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.existsUnique_forward
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot_succ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot_adapted
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot_solves
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.solves_add
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.sunspot_not_predictable
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.not_unique_of_one_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.solves_zero
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.unique_iff
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.existsUnique_iff
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.BddRV.sq
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.ar1_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.ar1_E_sq_dev
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.ar1_condVar
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.ar1_condVar_closed
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.eq_of_ae_eq
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.le_of_ae_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.ELin
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.trivialFirst
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.sum_prob_condE
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeMeasure
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeMeasure_singleton
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeMeasure_univ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeProb
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.integral_treeProb
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeFiltration
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.stronglyMeasurable_condE
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeSystem_fullSupport
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeSystem_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasure.TreeBridge.treeSystem_toExpectationSystem_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iidProb
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iidSystem
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.shock
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.measurable_shock
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coordSigma
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.futureSigma
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coordSigma_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.futureSigma_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iIndep_coord
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.filtration_le_past
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.indep_future
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_future
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.measurable_future_fun
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.integral_shock_fun
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_shock_fun
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_shock
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_shock_sq
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.shock_ae_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_shock_zero
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.E_shock_sq_eq
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.condVar_shock
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.shock_not_ae_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.singleton_lt_one
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.exists_singleton_le
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_singleton
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_countable_null
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_not_finitely_supported
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_news
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_existsUnique_iff
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_sunspot
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.ar1
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.ar1_succ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.ar1_adapted
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.ar1_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_ar1_E
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_ar1_condVar
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.iid_ar1_condVar_closed
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coinMeasure
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coinMeasure_univ
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coin
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.integral_coin
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coin_mean
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coin_var
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coin_bdd
#print axioms Cochrane.FiscalConstraints.ExpectationsMeasureIID.coin_economy
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.GrowthLaw
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.GrowthLaw.mk
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.GrowthLaw.meas
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.GrowthLaw.pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.GrowthLaw.integrable
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.cons
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.mom
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.ratioPow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.cons_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.cons_add
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.cons_zero
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.growth_cons
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.ratio_cons
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.ratio_rpow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.cons_rpow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.ratioPow_succ
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.measurable_ratioPow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.measurable_cons
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.measurable_coord_future
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.measurable_ratioPow_future
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.integrable_coord_fun
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_past_mul_future
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.integral_ratioPow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.integrable_cons_rpow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_ratio_rpow_mul
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.meas_iidGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_ratio_rpow
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_tsum_of_summable_integral
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.integrable_pvTerm
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.correct_term
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.incorrect_term
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.correct_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.incorrect_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.correct_finite_incorrect_explodes
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.mom_pos
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_tsum_correct_pv
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.rollover_step
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.eq_6_17
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.terminal_c
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.pv_term_c
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.hasSum_geom_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohn_pv_hasSum_iff
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.E_tsum_bohn_pv
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.riskFree_prices
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.eq_6_18
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.eq_6_18_diverges_ae
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohnG
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohnGrowthLaw
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohn_mom
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohn_hR
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohn_infinite_witness
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohn_infinite_6_18
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.MeasIIDGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.MeasIIDGrowth.toCore
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.iid_measIIDGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.bohnTree_measIIDGrowth
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.link_correct_term
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.link_terminal_c
#print axioms Cochrane.FiscalConstraints.AggregateUncertaintyMeasure.link_pv_term_c
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.gaussianProb
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormalLaw
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormalGrowthLaw
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_mom
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.cons_exp
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.map_log_growth
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.map_growth
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.iIndepFun_growth
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_E_growth
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_correct_term
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_incorrect_term
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_printed_incorrect_wrong
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_correct_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_incorrect_pv_summable_iff
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.Explodes
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_explodes_iff
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_region_iff
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_bohn_region
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_riskFree_prices
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_log_riskFree
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_E_tsum_bohn_pv
#print axioms Cochrane.FiscalConstraints.LognormalGrowthMeasure.lognormal_eq_6_18_diverges
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.measurable_debtPath
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.debtPath_shift
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.frequently_shift_iff
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.frequently_near_of_tendsto
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.measurableSet_frequently_near
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.debtPath_adapted
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.iIndepFun_shock
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.measure_shock_preimage
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.iid_frequently_exceeds
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.iid_not_sustainable
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.coin_debt_dichotomy
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.iid_unbounded_core
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_not_ae_bounded_above
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_iid_unbounded_vacuous
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.integral_abs_debtPath_le
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.prob_exceeds_ge
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.le_measure_frequently
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.iid_unbounded_of_integrable
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_Iic_ne_zero
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_process_unbounded
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_process_not_sustainable
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.gaussian_process_law
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.managedSurplus
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.managed_adapted
#print axioms Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.managedPath_le_process
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.ImproperPV
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.fwdValue
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.fwdValue_eq
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.finite_pv_eq
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.tendsto_finite_pv
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.fwdValue_hasDerivAt
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.terminal_eq
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.tendsto_terminal
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.tvc_iff
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.fwdValue_tvc
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.eq_fwdValue_of_tvc
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.existsUnique_tvc
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.exists_tvc_iff
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.integrableOn_Ioi_of
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.fwdValue_eq_integral
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.integrable_of_bdd
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.ratio_hasDerivAt
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.ratio_of_debt
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.flow_of_debt
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.money_debt_exists
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.money_debt_tvc_iff
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.money_debt_unique
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.money_debt_exists_iff
#print axioms Cochrane.FiscalConstraints.TidyR5MoneyExistence.eq_6_9_exists
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.SolvesGen
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.vocA
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pvA
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gSol
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.vocA_hasDerivAt
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.vocA_continuous
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.vocA_zero
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.vocA_sub
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.eq_vocA
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.integrableOn_expA
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gSol_eq_integral
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gSol_eq_pv
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gSol_continuous
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_bddOn
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_solves
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_sub
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_tendsto_abs_of_ne
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_bddOn_iff
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_existsUnique
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.gen_tvc_iff
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.clampI
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cumAt
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.SolvesPW
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwPV0
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwSol
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_continuous
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_eq_regime
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_eq_last
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_zero
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_hasDerivAt_regime
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_hasDerivAt_last
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.regime_cases
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_hasDerivAt_off
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.cum_after
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.solvesPW_toGen
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwSol_solvesPW
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_bddOn_iff
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_tendsto_abs_of_ne
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_existsUnique
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_tvc_iff
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwSol_eq_integral
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwPV0_eq_sum
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_not_unique_of_last_nonpos
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_unique_iff_last_pos
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pw_nominal_determinacy
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.twoA
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.twoT
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.twoT_monotone
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.solvesStep_iff
#print axioms Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG.pwPV0_two_regime
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arSurplus
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.ar1_succ_apply
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arSurplus_succ
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.measurable_ar1
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.measurable_ar1_F
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arDebt_adapted
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.measurable_arDebt
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.rho2
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arVar
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.ar1_hasLaw_gaussian
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arVar_ne_zero
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arSurplus_not_ae_bdd_above
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.E_ar1_succ
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.integral_abs_ar1_le
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.integral_abs_arDebt_le
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.prob_exceeds_ar
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.ar1From
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.dseq
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.ar1_shift
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.arDebt_shift
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.abs_dseq_le
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.dseq_tendsto
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.measurable_ar1From
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.ar1_unbounded_of_integrable
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.gaussian_ar1_unbounded
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.gaussian_ar1_not_sustainable
#print axioms Cochrane.FiscalConstraints.TidyR5GaussianAR1.gaussian_ar1_exp_unbounded
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.rulePath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.linRule
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.linRule_response
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidSurplus
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.min_eq_sub_max
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath_succ_eq
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidSurplus_eq_rule
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.rule_le_avoidSurplus
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath_eq_managedPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandSurplus
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.max_eq_add_max
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_succ_eq
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.cappedPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.cappedSurplus
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.cappedPath_succ_eq
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.cappedSurplus_le
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath_le
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath_within_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_mem
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_within_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.cappedPath_within_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.not_within_of_capacity
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.plan_debtPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoid_plan_debtPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.band_plan_debtPath
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.plan_within_of_le
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.plan_breach_high
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.plan_breach_low
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoid_hits_of_rule_exceeds
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.avoidPath_succ_eq_xbar
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_succ_eq_xbar
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_succ_eq_xlow
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.bandPath_mem_all
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.mul_mem_minmax
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.debt_le_iff_price_ge
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.debt_eq_iff_price_eq
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.le_debt_iff_price_le
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplus.price_spec
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.Sustainable
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.BandSustainable
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.IsEqmPrice
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.IsBandEqmPrice
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.IsFeedbackEqmPrice
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.IsBandFeedbackEqmPrice
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.ar1_zero
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.linRule_shock
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.rulePath_linRule
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_adapted
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_plan_adapted
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.ar1_frequently_le
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.negLaw
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.map_neg_iid
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.ar1_neg
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.ar1_frequently_ge
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_hits
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_hits
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_sustainable_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_eqm_price_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_price_isLeast
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.plan_price_not_unique
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_sustainable_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_eqm_price_unique
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.feedback_sustainable_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.feedback_price_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.feedback_price_not_unique
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_feedback_price_iff
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.band_feedback_price_not_unique
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.linear_rule_not_sustainable
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.gaussian_Ici_ne_zero
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.gaussian_integrable
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.gaussian_plan_verdict
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.gaussian_band_verdict
#print axioms Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure.iid_verdict
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.unbounded_above_of_nonpos
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.linear_rule_ae_unbounded_above
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.linear_rule_zero_prob
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.debtPath_eq_discounted
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.linear_rule_half_prob
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.linear_rule_not_ae_sustainable
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.plan_unbounded_below_of_frequently
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.plan_ae_unbounded_below
#print axioms Cochrane.FiscalConstraints.TidyR6LinearRuleBounds.plan_debt_ae_unbounded_below
