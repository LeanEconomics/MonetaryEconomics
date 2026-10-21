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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
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

namespace Cochrane.Monetarism

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

end Cochrane.Monetarism

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

namespace Cochrane.Monetarism

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

end Cochrane.Monetarism

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

namespace Cochrane.Monetarism.ExpectationsFiniteTree

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

end Cochrane.Monetarism.ExpectationsFiniteTree

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

namespace Cochrane.Monetarism.ForwardSolution

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

end Cochrane.Monetarism.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibria and regimes: money demand and the government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.1 (pp. 434–435), and the
precise claims of Chapter 11 (§11.1–11.3, pp. 314–319) and §14.1 (p. 342) on open-market
operations, elastic currency and helicopter drops.

Conventions. Processes are `ℕ → Ω → ℝ` for an arbitrary `ExpectationSystem` (so every result
holds under perfect foresight and under genuine uncertainty). `N t` is the money carried into
date `t`, the book's `M_{t−1}` (so the book's `M_{t+j}` is `N (t + j + 1)`), `Bm t` is the
book's `B_{t−1}`, `Λ` the (real) stochastic discount factor level and `P` the price level. The
infinite sums `E_t ∑_{j≥0} …` of (19.2)–(19.3) are stated as limits of the conditional
expectations of the partial sums, multiplied through by the known `Λ_t > 0`.

## Main results

* (19.1) `QuantityEq`. (19.2) ⇔ (19.3): the summation-by-parts identity `sum_by_parts` (any
  horizon `T`), `eq192_iff_eq193` (equivalence under the money transversality condition), and
  `tail_tendsto_zero_of_book_tvc` (the book's money TVC `E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0` implies the
  one used, for `i ≥ 0`, `M ≥ 0`).
* The valuation equation from the flow constraint: `flow_value_recursion`,
  `flow_pv_iff_tvc` ((19.2) holds iff the bond transversality condition holds) and
  `flow_eq193_of_tvc`.
* §19.1 regimes (survey NI-7): `seigniorage_indep_price` (under (19.1) the seigniorage term of
  (19.3) does not involve `P`), `ni7` (monetary and fiscal regimes observationally equivalent:
  every equilibrium is the unique equilibrium of an active-money/passive-fiscal regime and of an
  active-fiscal/passive-money regime, with identical observables), `double_passive`
  (indeterminacy), `double_active_iff` (overdetermination), `passive_surplus_realises`
  (a passive surplus rule exists for every target value of debt).
* Ch11: V1 `spread_term_eq_zero_iff`, `partial111_of_no_spread`, `omo_irrelevant` (with
  `i = i^m` an open-market swap leaves the price level unchanged); V3 `spread_existsUnique`
  (money demand met by the spread); V4 `omo_equivalence` (both regimes describe the same fall in
  money, rise in bonds and rise in surpluses); V5 `elastic_currency`.
* §14.1, p. 342 (V11), helicopter magnitudes: `ftpl_price_ratio`, `quantity_price_ratio`,
  `helicopter_fiscal`, `helicopter_fiscal_approx`, `helicopter_monetarist`,
  `helicopter_cash_share`, `helicopter_bond_loss`.
-/

namespace Cochrane.Monetarism.Regimes

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15 tendsto_partial_A16)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.1) and the summation by parts (19.2) ⇔ (19.3) -/

/-- Cochrane (2023), eq. (19.1), p. 434 (and (11.2), p. 315, with `i = i^m`): money demand
`M_t V_t = P_t y_t` at every date and in every state. -/
def QuantityEq (M V P y : ℕ → Ω → ℝ) : Prop := ∀ t, M t * V t = P t * y t

/-- Cochrane (2023), §3.4 and eq. (19.3), p. 434 (`1/(1 + i_t) = E_t[Λ_{t+1}P_t/(Λ_tP_{t+1})]`):
the one-period nominal bond is priced by the stochastic discount factor, written for the value
of a dollar `Λ_t/P_t` as `E_t(Λ_{t+1}/P_{t+1}) = (Λ_t/P_t)/(1 + i_t)`. -/
def BondPricing (Λ P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (Λ (t + 1) / P (t + 1)) = Λ t / P t / (1 + i t)

/-- Cochrane (2023), eq. (19.2), p. 434, multiplied through by the known `Λ_t`: the date-`t`
partial sum `∑_{j<T} E_t[Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s_{t+j})]` (with
`M_{t+j} = N_{t+j+1}`). -/
noncomputable def partial192 (Λ P N s : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T,
    𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j)))

/-- Cochrane (2023), eq. (19.3), p. 434, multiplied through by the known `Λ_t`: the date-`t`
partial sum `∑_{j<T} E_t[Λ_{t+j}(i_{t+j}/(1 + i_{t+j}) · M_{t+j}/P_{t+j} + s_{t+j})]`. -/
noncomputable def partial193 (Λ P N i s : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T,
    𝔼.E t (Λ (t + j) * (i (t + j) / (1 + i (t + j)) * N (t + j + 1) / P (t + j) + s (t + j)))

/-- Cochrane (2023), eq. (19.3), p. 434 (the step behind the summation by parts): for `t ≤ k`,
`E_t[Λ_{k+1}M_k/P_{k+1}] = E_t[M_k(Λ_k/P_k)/(1 + i_k)]`, since `M_k` is known at `k`. -/
theorem E_next_value (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (hBP : BondPricing 𝔼 Λ P i)
    (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1)) {t k : ℕ} (htk : t ≤ k) :
    𝔼.E t (Λ (k + 1) * N (k + 1) / P (k + 1)) =
      𝔼.E t (N (k + 1) * (Λ k / P k / (1 + i k))) := by
  have h1 : Λ (k + 1) * N (k + 1) / P (k + 1) = N (k + 1) * (Λ (k + 1) / P (k + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [h1, ← 𝔼.tower htk, hPO k _ _ (hN k), hBP k]

/-- Cochrane (2023), eq. (19.3), p. 434: the one-period form of the summation by parts,
`E_t[Λ_{k+1}M_k/P_{k+1}] = E_t[Λ_kM_k/P_k − Λ_k(i_k/(1 + i_k))M_k/P_k]`. -/
theorem step_identity (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (hBP : BondPricing 𝔼 Λ P i)
    (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1)) (hi : ∀ t ω, 1 + i t ω ≠ 0) {t k : ℕ}
    (htk : t ≤ k) :
    𝔼.E t (Λ (k + 1) * N (k + 1) / P (k + 1)) =
      𝔼.E t (Λ k * N (k + 1) / P k - Λ k * (i k / (1 + i k) * N (k + 1) / P k)) := by
  rw [E_next_value 𝔼 hPO hBP hN htk]
  congr 1
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  have h := hi k ω
  have key : (1 + i k ω)⁻¹ + i k ω * (1 + i k ω)⁻¹ = 1 := by
    field_simp
  simp only [div_eq_mul_inv]
  linear_combination (Λ k ω * N (k + 1) ω * (P k ω)⁻¹) * key

/-- Cochrane (2023), (19.2)–(19.3), p. 434, the summation by parts at every horizon `T`:
`∑_{j<T} E_t[Λ(ΔM/P + s)] + Λ_tM_{t−1}/P_t = ∑_{j<T} E_t[Λ(iM/((1+i)P) + s)]
  + E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}]`. -/
theorem sum_by_parts (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (s : ℕ → Ω → ℝ)
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) (t T : ℕ) :
    partial192 𝔼 Λ P N s t T + Λ t * N t / P t =
      partial193 𝔼 Λ P N i s t T + 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) := by
  induction T with
  | zero =>
    simp only [partial192, partial193, Finset.range_zero, Finset.sum_empty, zero_add, add_zero]
    have h1 : Λ t * N t / P t = N t * (Λ t / P t) := by
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO t _ _ (hNa t), hφ t]
  | succ T ih =>
    simp only [partial192, partial193, Finset.sum_range_succ] at ih ⊢
    rw [← add_assoc t T 1, step_identity 𝔼 hPO hBP hN hi (Nat.le_add_right t T)]
    have hDA : 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) +
        𝔼.E t (Λ (t + T) * ((N (t + T + 1) - N (t + T)) / P (t + T) + s (t + T))) =
        𝔼.E t (Λ (t + T) * (i (t + T) / (1 + i (t + T)) * N (t + T + 1) / P (t + T) +
          s (t + T))) +
        𝔼.E t (Λ (t + T) * N (t + T + 1) / P (t + T) -
          Λ (t + T) * (i (t + T) / (1 + i (t + T)) * N (t + T + 1) / P (t + T))) := by
      rw [← map_add, ← map_add]
      congr 1
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
      ring
    linear_combination ih + hDA

/-- Cochrane (2023), eqs. (19.2) and (19.3), p. 434: given the bond-pricing condition and the
money transversality condition `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0`, the valuation equation in
the form (19.2) `B_{t−1}/P_t = E_t∑(Λ_{t+j}/Λ_t)(ΔM_{t+j}/P_{t+j} + s_{t+j})` holds if and only if
it holds in the form (19.3) `(B_{t−1} + M_{t−1})/P_t = E_t∑(Λ_{t+j}/Λ_t)(iM/((1+i)P) + s)`
(both multiplied through by `Λ_t`). -/
theorem eq192_iff_eq193 (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (s Bm : ℕ → Ω → ℝ)
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) {t : ℕ} {ω : Ω}
    (hTVC : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => partial192 𝔼 Λ P N s t T ω) atTop (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => partial193 𝔼 Λ P N i s t T ω) atTop
        (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) := by
  have hid : ∀ T, partial193 𝔼 Λ P N i s t T ω = partial192 𝔼 Λ P N s t T ω +
      Λ t ω * N t ω / P t ω - 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω := by
    intro T
    have h := congrFun (sum_by_parts 𝔼 hPO s hBP hφ hNa hN hi t T) ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply] at h
    linarith
  have hval : Λ t ω * (Bm t ω + N t ω) / P t ω =
      Λ t ω * Bm t ω / P t ω + Λ t ω * N t ω / P t ω - 0 := by ring
  constructor
  · intro h
    rw [hval]
    exact ((h.add_const _).sub hTVC).congr fun T => (hid T).symm
  · intro h
    have h2 := (h.sub_const (Λ t ω * N t ω / P t ω)).add hTVC
    have hv : Λ t ω * (Bm t ω + N t ω) / P t ω - Λ t ω * N t ω / P t ω + 0 =
        Λ t ω * Bm t ω / P t ω := by ring
    rw [hv] at h2
    refine h2.congr fun T => ?_
    rw [hid T]
    ring

/-- Cochrane (2023), §19.1, p. 434 (the money transversality condition
`E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0`): with `i ≥ 0` and nonnegative money and value of a dollar, the
book's form of the condition implies the form `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0` used in
`eq192_iff_eq193`, because `0 ≤ E_t[Λ_{k+1}M_k/P_{k+1}] ≤ E_t[Λ_kM_k/P_k]`. -/
theorem tail_tendsto_zero_of_book_tvc (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi0 : ∀ t ω, 0 ≤ i t ω) (hpos : ∀ t ω, 0 ≤ N (t + 1) ω * (Λ t ω / P t ω)) {t : ℕ}
    {ω : Ω}
    (hbook : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T + 1) / P (t + T)) ω) atTop
      (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  refine squeeze_zero (fun T => ?_) (fun T => ?_) hbook
  · rw [← add_assoc, E_next_value 𝔼 hPO hBP hN (Nat.le_add_right t T)]
    have h0 : (0 : Ω → ℝ) ≤ N (t + T + 1) * (Λ (t + T) / P (t + T) / (1 + i (t + T))) :=
      fun ω' => by
        simp only [Pi.zero_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
        have h1 : 0 < 1 + i (t + T) ω' := by linarith [hi0 (t + T) ω']
        have h2 := hpos (t + T) ω'
        have e : N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω' / (1 + i (t + T) ω')) =
            N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') / (1 + i (t + T) ω') := by ring
        rw [e]
        exact div_nonneg h2 h1.le
    have := 𝔼.mono t h0 ω
    rwa [map_zero] at this
  · rw [← add_assoc, E_next_value 𝔼 hPO hBP hN (Nat.le_add_right t T)]
    have hle : N (t + T + 1) * (Λ (t + T) / P (t + T) / (1 + i (t + T))) ≤
        Λ (t + T) * N (t + T + 1) / P (t + T) := fun ω' => by
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
      have h1 : 1 ≤ 1 + i (t + T) ω' := by linarith [hi0 (t + T) ω']
      have h2 := hpos (t + T) ω'
      have e1 : N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω' / (1 + i (t + T) ω')) =
          N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') / (1 + i (t + T) ω') := by ring
      have e2 : Λ (t + T) ω' * N (t + T + 1) ω' / P (t + T) ω' =
          N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') := by ring
      rw [e1, e2]
      exact div_le_self h2 h1
    exact 𝔼.mono t hle ω

/-! ### The valuation equation from the flow constraint -/

/-- Cochrane (2023), p. 439 (government flow constraint, and §3.4): with `Bm t = B_{t−1}` and
`N t = M_{t−1}`, `B_{t−1} + M_{t−1} = P_ts_t + Q_tB_t + M_t` at every date. (For the household of
§19.3, `s` is replaced by `s + c − y`.) -/
def Flow (Bm N P s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Bm t + N t = P t * s t + Q t * Bm (t + 1) + N (t + 1)

/-- Cochrane (2023), (19.2), p. 434, the one-period step: the flow constraint with
`Q_t = 1/(1 + i_t)` and the bond-pricing condition give
`Λ_tB_{t−1}/P_t = Λ_t(ΔM_t/P_t + s_t) + E_t[Λ_{t+1}B_t/P_{t+1}]`. -/
theorem flow_value_recursion (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) (t : ℕ) :
    Λ t * Bm t / P t = Λ t * ((N (t + 1) - N t) / P t + s t) +
      𝔼.E t (Λ (t + 1) * Bm (t + 1) / P (t + 1)) := by
  have hE : 𝔼.E t (Λ (t + 1) * Bm (t + 1) / P (t + 1)) =
      Bm (t + 1) * (Λ t / P t / (1 + i t)) := by
    have h1 : Λ (t + 1) * Bm (t + 1) / P (t + 1) = Bm (t + 1) * (Λ (t + 1) / P (t + 1)) := by
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO t _ _ (hB t), hBP t]
  rw [hE]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  have hf := congrFun (hflow t) ω
  simp only [Pi.add_apply, Pi.mul_apply] at hf
  rw [hQ t ω] at hf
  have h1 := hi t ω
  have h2 := hP t ω
  have hb : Bm t ω = P t ω * s t ω + 1 / (1 + i t ω) * Bm (t + 1) ω + N (t + 1) ω - N t ω := by
    linarith
  rw [hb]
  field_simp
  ring

/-- Cochrane (2023), (19.2), p. 434 and §3.4: given the flow constraint, the bond-pricing
condition and adapted debt, the valuation equation (19.2) holds at `(t, ω)` (as the limit of
the partial sums, multiplied by `Λ_t`) if and only if the bond transversality condition
`E_t[Λ_{t+T}B_{t+T−1}/P_{t+T}] → 0` holds there. -/
theorem flow_pv_iff_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => partial192 𝔼 Λ P N s t T ω) atTop (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  set x : ℕ → Ω → ℝ := fun k => Λ k * Bm k / P k with hx
  set d : ℕ → Ω → ℝ := fun k => Λ k * ((N (k + 1) - N k) / P k + s k) with hd
  have hrec : ∀ k, x k = d k + 𝔼.E k (x (k + 1)) := fun k =>
    flow_value_recursion 𝔼 hPO hBP hB hQ hi hP hflow k
  have hxa : 𝔼.Adapted x := fun k => by
    have h1 : x k = Bm k * (Λ k / P k) := by
      funext ω'
      simp only [hx, Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO k _ _ (hBa k), hφ k]
  have hda : 𝔼.Adapted d := fun k => by
    have h1 : d k = x k - 𝔼.E k (x (k + 1)) := by rw [hrec k]; abel
    rw [h1, map_sub, hxa k, 𝔼.E_E_self]
  have hsol : Solves 𝔼 1 d x := fun k => by rw [one_smul, add_comm]; exact hrec k
  have hpart : ∀ T, partial192 𝔼 Λ P N s t T ω = x t ω - 𝔼.E t (x (t + T)) ω := by
    intro T
    have h := congrFun (iterate_A15 𝔼 hda hsol t T) ω
    simp only [one_pow, one_smul, Pi.add_apply, Finset.sum_apply] at h
    simp only [partial192, Finset.sum_apply]
    linarith
  have hxt : x t ω = Λ t ω * Bm t ω / P t ω := rfl
  constructor
  · intro h
    have h2 := (tendsto_const_nhds (x := x t ω)).sub h
    rw [hxt, sub_self] at h2
    refine h2.congr fun T => ?_
    rw [hpart T, hxt]
    simp only [hx]
    ring
  · intro h
    have h2 := (tendsto_const_nhds (x := x t ω)).sub h
    rw [sub_zero, hxt] at h2
    exact h2.congr fun T => (hpart T).symm

/-- Cochrane (2023), (19.3), p. 434: from the flow constraint, the bond-pricing condition, the
bond transversality condition and the money transversality condition, the valuation equation
holds in the form (19.3), `(B_{t−1} + M_{t−1})/P_t = E_t∑(Λ_{t+j}/Λ_t)(iM/((1+i)P) + s)`. -/
theorem flow_eq193_of_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => partial193 𝔼 Λ P N i s t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  (eq192_iff_eq193 𝔼 hPO s Bm hBP hφ hNa hN hi hmoney).mp
    ((flow_pv_iff_tvc 𝔼 hPO hBP hφ hBa hB hQ hi hP hflow t ω).mpr hbond)

/-! ### §19.1: monetary and fiscal regimes (survey NI-7) -/

/-- Cochrane (2023), (19.1) and (19.3), p. 434: under money demand `MV = Py` the seigniorage flow
`(i/(1 + i))M/P` of (19.3) equals `(i/(1 + i))y/V`; it does not involve the price level, so the
right-hand side of (19.3) is a real present value `W_t` set by policy. -/
theorem seigniorage_indep_price {M V P y i : ℝ} (hP : P ≠ 0) (hV : V ≠ 0)
    (hq : M * V = P * y) : i / (1 + i) * M / P = i / (1 + i) * y / V := by
  rw [div_eq_div_iff hP hV, mul_assoc, hq]
  ring

/-- Cochrane (2023), §19.1, p. 435: the government debt valuation equation in the form
`B_{t−1} + M_{t−1} = P_tW_t`, with `D_t = B_{t−1} + M_{t−1}` the nominal liabilities and `W_t` the
real present value of surpluses and seigniorage on the right of (19.3). -/
def Valuation (D W P : ℕ → Ω → ℝ) : Prop := ∀ t, D t = P t * W t

/-- Cochrane (2023), §19.1, p. 435: a process is strictly positive at every date and state. -/
def Pos (x : ℕ → Ω → ℝ) : Prop := ∀ t ω, 0 < x t ω

/-- Cochrane (2023), §19.1, p. 435, the active-money, passive-fiscal regime: the money supply
`Ms` is set and the price level clears the money market (19.1); surpluses then adjust so that
the valuation equation holds for that price level (`W = D/P`). -/
def MonetaryEqm (Ms V y P : ℕ → Ω → ℝ) : Prop := Pos P ∧ QuantityEq Ms V P y

/-- Cochrane (2023), §19.1, p. 435, the active-fiscal, passive-money regime: nominal liabilities
`D` and the present value `W` are set and the price level satisfies the valuation equation;
money is then supplied passively (`M = Py/V`). -/
def FiscalEqm (D W P : ℕ → Ω → ℝ) : Prop := Pos P ∧ Valuation D W P

/-- Cochrane (2023), §19.1, p. 435 ("the fiscal and monetary regimes are observationally
equivalent", survey NI-7): if `(P, M, D, W)` satisfies both equilibrium conditions (19.1) and
the valuation equation, then `P` is the unique equilibrium of the active-money regime with money
supply `M` (whose passive surpluses reproduce `W = D/P`), and the unique equilibrium of the
active-fiscal regime with `(D, W)` (whose passive money reproduces `M = Py/V`). -/
theorem ni7 {P M D W V y : ℕ → Ω → ℝ} (hP : Pos P) (hV : Pos V) (hy : Pos y) (hW : Pos W)
    (hq : QuantityEq M V P y) (hv : Valuation D W P) :
    (∀ P', MonetaryEqm M V y P' ↔ P' = P) ∧ (fun t => D t / P t) = W ∧
      (∀ P', FiscalEqm D W P' ↔ P' = P) ∧ (fun t => P t * y t / V t) = M := by
  refine ⟨fun P' => ⟨fun h => ?_, fun h => h ▸ ⟨hP, hq⟩⟩, ?_,
    fun P' => ⟨fun h => ?_, fun h => h ▸ ⟨hP, hv⟩⟩, ?_⟩
  · funext t ω
    have h1 := congrFun (h.2 t) ω
    have h2 := congrFun (hq t) ω
    simp only [Pi.mul_apply] at h1 h2
    have := hy t ω
    exact mul_right_cancel₀ this.ne' (by linarith)
  · funext t ω
    have h1 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1
    simp only [Pi.div_apply]
    rw [h1, mul_div_cancel_left₀ _ (hP t ω).ne']
  · funext t ω
    have h1 := congrFun (h.2 t) ω
    have h2 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1 h2
    have := hW t ω
    exact mul_right_cancel₀ this.ne' (by linarith)
  · funext t ω
    have h1 := congrFun (hq t) ω
    simp only [Pi.mul_apply] at h1
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [← h1, mul_div_cancel_right₀ _ (hV t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 ("if monetary and fiscal policy are both passive, then the
price level is undetermined"): with money supplied passively (`M = Py/V`) and surpluses adjusting
passively (`W = D/P`), every positive price-level process is an equilibrium. -/
theorem double_passive {D V y : ℕ → Ω → ℝ} (hV : Pos V) (P' : ℕ → Ω → ℝ) (hP' : Pos P') :
    QuantityEq (fun t => P' t * y t / V t) V P' y ∧ Valuation D (fun t => D t / P' t) P' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [div_mul_cancel₀ _ (hV t ω).ne']
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [mul_div_cancel₀ _ (hP' t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 (coordination): if money and fiscal policy are both active
(`M` and `(D, W)` both set), an equilibrium exists if and only if the two settings are
coordinated, `M_tV_tW_t = D_ty_t` at every date and state; otherwise the equations contradict. -/
theorem double_active_iff {Ms D W V y : ℕ → Ω → ℝ} (hD : Pos D) (hW : Pos W) :
    (∃ P, MonetaryEqm Ms V y P ∧ Valuation D W P) ↔ ∀ t ω, Ms t ω * V t ω * W t ω =
      D t ω * y t ω := by
  constructor
  · rintro ⟨P, ⟨-, hq⟩, hv⟩ t ω
    have h1 := congrFun (hq t) ω
    have h2 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1 h2
    rw [h1, h2]
    ring
  · intro h
    refine ⟨fun t ω => D t ω / W t ω, ⟨fun t ω => div_pos (hD t ω) (hW t ω), fun t => ?_⟩,
      fun t => ?_⟩
    · funext ω
      simp only [Pi.mul_apply]
      have := hW t ω
      field_simp
      linarith [h t ω]
    · funext ω
      simp only [Pi.mul_apply]
      rw [div_mul_cancel₀ _ (hW t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 ("the government must adjust surpluses ex-post so that the
government debt valuation equation holds"): the passive surplus rule
`s_t = W_t − βE_tW_{t+1}` that delivers a target real value `W` of the debt. -/
def passiveSurplus (β : ℝ) (W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := W t - β • 𝔼.E t (W (t + 1))

/-- Cochrane (2023), §19.1, p. 435: a passive fiscal policy exists for every target. For any
bounded adapted `W` (e.g. `W = D/P` for whatever price level occurs) and `|β| < 1`, the surplus
rule `passiveSurplus` is adapted and its present value `E_t∑βʲs_{t+j}` (limit of the partial
sums) equals `W_t`, so the valuation equation holds for any price level. -/
theorem passive_surplus_realises {β : ℝ} (hβ : |β| < 1) {W : ℕ → Ω → ℝ} (hWa : 𝔼.Adapted W)
    (hWb : BoundedProc W) :
    𝔼.Adapted (passiveSurplus 𝔼 β W) ∧ ∀ t ω,
      Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (passiveSurplus 𝔼 β W (t + j)) ω)
        atTop (𝓝 (W t ω)) := by
  have hsa : 𝔼.Adapted (passiveSurplus 𝔼 β W) := fun t => by
    simp only [passiveSurplus]
    rw [map_sub, map_smul, 𝔼.E_E_self, hWa t]
  have hsol : Solves 𝔼 β (passiveSurplus 𝔼 β W) W := fun t => by
    simp only [passiveSurplus]
    abel
  exact ⟨hsa, fun t ω => tendsto_partial_A16 𝔼 hβ hsa hsol hWb t ω⟩

/-! ### Chapter 11: open-market operations, the spread, elastic currency -/

/-- Cochrane (2023), eq. (11.1), p. 315: the date-`t` partial sum of the valuation equation with
interest-paying money, `∑_{j<T} βʲE_t[s + (i − i^m)/((1 + i)(1 + i^m)) · M/P]`. -/
noncomputable def partial111 (β : ℝ) (s i im M P : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T, β ^ j • 𝔼.E t (s (t + j) +
    (i (t + j) - im (t + j)) / ((1 + i (t + j)) * (1 + im (t + j))) * M (t + j) / P (t + j))

/-- Cochrane (2023), (11.1), p. 315, and V1 (pp. 316–317): with `1 + i > 0`, `1 + i^m > 0` and
positive real money, the seigniorage term `(i − i^m)/((1 + i)(1 + i^m)) · M/P` vanishes if and
only if money pays the market rate, `i = i^m`. -/
theorem spread_term_eq_zero_iff {i im M P : ℝ} (hi : 0 < 1 + i) (him : 0 < 1 + im)
    (hm : M / P ≠ 0) : (i - im) / ((1 + i) * (1 + im)) * M / P = 0 ↔ i = im := by
  rw [mul_div_assoc]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases div_eq_zero_iff.mp h1 with h2 | h2
      · linarith
      · exact absurd h2 (mul_pos hi him).ne'
    · exact absurd h1 hm
  · intro h
    rw [h, sub_self, zero_div, zero_mul]

/-- Cochrane (2023), (11.1), p. 315, V1: when money pays the market rate at every date
(`i = i^m`), the right-hand side of (11.1) is `∑ βʲE_ts_{t+j}`, whatever the money and price
paths. -/
theorem partial111_of_no_spread {β : ℝ} {s i im : ℕ → Ω → ℝ} (h : ∀ t, i t = im t)
    (M P : ℕ → Ω → ℝ) (t T : ℕ) :
    partial111 𝔼 β s i im M P t T = ∑ j ∈ Finset.range T, β ^ j • 𝔼.E t (s (t + j)) := by
  unfold partial111
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext ω
  simp [h]

/-- Cochrane (2023), §11.2, pp. 316–317, V1 ("an open-market operation swapping `M` for `B` has
no effect"): with `i = i^m` at every date, (11.1) depends on bonds and money only through
`B + M`. If `B_{t−1} + M_{t−1} = B'_{t−1} + M'_{t−1}` then, for any money paths, a price level
`P_t` satisfies (11.1) for `(B, M)` if and only if it does for `(B', M')`. -/
theorem omo_irrelevant {β : ℝ} {s i im : ℕ → Ω → ℝ} (h : ∀ t, i t = im t)
    (M M' P P' : ℕ → Ω → ℝ) {b m b' m' Pt : ℝ} (hsum : b + m = b' + m') (t : ℕ) (ω : Ω) :
    Tendsto (fun T => partial111 𝔼 β s i im M P t T ω) atTop (𝓝 ((b + m) / Pt)) ↔
      Tendsto (fun T => partial111 𝔼 β s i im M' P' t T ω) atTop (𝓝 ((b' + m') / Pt)) := by
  simp only [partial111_of_no_spread 𝔼 h, hsum]

/-- Cochrane (2023), §11.2, p. 317, V3 ("we can satisfy the money demand curve by letting the
interest-rate spread `i − i^m` vary … the price of money can be passive rather than the
quantity"): if velocity `V(i − i^m)` is strictly increasing in the spread and takes every
positive value, then for any money `M > 0` and nominal income `Py > 0` exactly one spread clears
the money market `M V(i − i^m) = Py`. -/
theorem spread_existsUnique {V : ℝ → ℝ} (hV : StrictMono V) (hsurj : ∀ v, 0 < v → ∃ x, V x = v)
    {M Py : ℝ} (hM : 0 < M) (hPy : 0 < Py) : ∃! x, M * V x = Py := by
  obtain ⟨x, hx⟩ := hsurj (Py / M) (div_pos hPy hM)
  refine ⟨x, show M * V x = Py by rw [hx]; field_simp, fun x' hx' => hV.injective ?_⟩
  rw [hx]
  field_simp
  linarith

/-- Cochrane (2023), §11.2, p. 318, V4 ("both theories describe an identical fall in money `M`,
rise in debt `B`, and a rise in surpluses `s`"): compare two equilibria `(P, M, D, W)` and
`(P', M', D, W')` with the same nominal liabilities `D = B + M` (a pure change of composition)
under rigid `M_tV = P_ty`. Money falls iff the price level falls iff the real value `W` of
surpluses rises; and bonds `B = D − M` rise iff money falls. The monetarist reading (less money,
passive fiscal tightening) and the fiscal reading (fiscal tightening, passive fall in money)
describe the same event. -/
theorem omo_equivalence {P M W P' M' W' D V y : ℕ → Ω → ℝ} (hP : Pos P) (hP' : Pos P')
    (hD : Pos D) (hV : Pos V) (hy : Pos y) (hq : QuantityEq M V P y)
    (hq' : QuantityEq M' V P' y) (hv : Valuation D W P) (hv' : Valuation D W' P') (t : ℕ)
    (ω : Ω) :
    (M' t ω < M t ω ↔ P' t ω < P t ω) ∧ (P' t ω < P t ω ↔ W t ω < W' t ω) ∧
      (D t ω - M t ω < D t ω - M' t ω ↔ M' t ω < M t ω) := by
  have h1 := congrFun (hq t) ω
  have h1' := congrFun (hq' t) ω
  have h2 := congrFun (hv t) ω
  have h2' := congrFun (hv' t) ω
  simp only [Pi.mul_apply] at h1 h1' h2 h2'
  have hVp := hV t ω
  have hyp := hy t ω
  have hPp := hP t ω
  have hPp' := hP' t ω
  have hDp := hD t ω
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩⟩
  · by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hyp.le]
  · by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hVp.le]
  · by_contra hc
    push Not at hc
    have hWp : 0 < W t ω := by
      by_contra h0
      push Not at h0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hPp.le h0]
    nlinarith [mul_le_mul_of_nonneg_left hc hPp'.le, mul_lt_mul_of_pos_right h hWp]
  · by_contra hc
    push Not at hc
    have hWp : 0 < W t ω := by
      by_contra h0
      push Not at h0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hPp.le h0]
    nlinarith [mul_le_mul_of_nonneg_left hc hPp.le, mul_lt_mul_of_pos_left h hPp']

/-- Cochrane (2023), §11.3, p. 318, V5 ("elastic currency": "any `P` is consistent with this
policy"): if the central bank issues `M_t = P_ty_t/V_t` for whatever price level occurs, the
money market clears for every positive price-level process; money demand then places no
restriction on `P`, which the valuation equation alone determines (`ni7`). -/
theorem elastic_currency {V y : ℕ → Ω → ℝ} (hV : Pos V) (P : ℕ → Ω → ℝ) :
    QuantityEq (fun t => P t * y t / V t) V P y := fun t => by
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply]
  rw [div_mul_cancel₀ _ (hV t ω).ne']

/-! ### §14.1, p. 342 (V11): helicopter magnitudes -/

/-- Cochrane (2023), §14.1, p. 342, the fiscal-theory answer: with the real value of surpluses
`W` unchanged, the valuation equation `D = PW` makes the price level proportional to nominal
liabilities, `P'/P = D'/D`. -/
theorem ftpl_price_ratio {D D' P P' W : ℝ} (hD : 0 < D) (hW : 0 < W) (hv : D = P * W)
    (hv' : D' = P' * W) : P' / P = D' / D := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hv
    exact hD.ne' hv
  rw [hv, hv', mul_div_mul_right _ _ hW.ne']

/-- Cochrane (2023), §14.1, p. 342, the monetarist answer: with velocity and output unchanged,
`MV = Py` makes the price level proportional to money, `P'/P = M'/M`. -/
theorem quantity_price_ratio {M M' V y P P' : ℝ} (hM : 0 < M) (hV : 0 < V) (hy : 0 < y)
    (hq : M * V = P * y) (hq' : M' * V = P' * y) : P' / P = M' / M := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hq
    exact (mul_pos hM hV).ne' hq
  rw [div_eq_div_iff hP hM.ne']
  have : P' * y * M = M' * V * M := by rw [hq']
  have h2 : M' * (P * y) = M' * (M * V) := by rw [hq]
  nlinarith

/-- Cochrane (2023), §14.1, p. 342 ("Overall treasury debt just got diluted 1%"): $100,000 of
bonds and $1,000 of cash per household plus a $1,000 drop raise nominal liabilities, hence the
price level, by the factor `1 + 1/101`. -/
theorem helicopter_fiscal : ((100000 + 1000 + 1000 : ℝ) / (100000 + 1000)) = 1 + 1 / 101 := by
  norm_num

/-- Cochrane (2023), §14.1, p. 342 ("a fiscal theory answer is, 1%"): the exact rise `1/101` is
within one hundredth of a percentage point of 1%. -/
theorem helicopter_fiscal_approx : |(1 : ℝ) / 101 - 1 / 100| < 1 / 10000 := by
  rw [abs_lt]
  constructor <;> norm_num

/-- Cochrane (2023), §14.1, p. 342 ("The monetarist answer is 100%. The money supply doubles, so
the price level must double"): cash goes from $1,000 to $2,000. -/
theorem helicopter_monetarist : ((1000 + 1000 : ℝ) / 1000) = 2 := by norm_num

/-- Cochrane (2023), §14.1, p. 342: after the doubling, $2,000 of cash is 1% of the now $200,000
nominal income per household. -/
theorem helicopter_cash_share : (2000 : ℝ) / (2 * 100000) = 1 / 100 := by norm_num

/-- Cochrane (2023), §14.1, p. 342 ("this doubling of the price level wipes out half of the real
value of $100,000 of treasury savings … the present value of taxes have declined $50,000"). -/
theorem helicopter_bond_loss : (100000 : ℝ) - 100000 / 2 = 50000 := by norm_num

end Cochrane.Monetarism.Regimes

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interest-elastic money demand and multiple equilibria (Cagan with rational expectations)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.2, pp. 436–438,
eqs. (19.4)–(19.8). Adapted from the Woodford Chapter 2 project (`MoneyGrowth`, the Cagan
equation (A.28)–(A.29)); everything holds for an arbitrary `ExpectationSystem`.

Notation: `a = αv > 0` is the semi-elasticity of money demand (the book's `αv`), `y`, `r`
constants, `m`, `p` log money and log price level, `θ = (1 + a)/a > 1` (`theta`), and the
forcing `x_t = m_t − y + ar` (`forcing`).

## Main results

* (19.4) `eq194_iff_log` (levels ⇔ logs); (19.5) `md_fisher_iff_cagan`, `cagan_iff_expect`,
  `cagan_iff_solves` (the forward form `p_t = θ⁻¹E_tp_{t+1} + (1 − θ⁻¹)x_t`), `theta_gt_one`.
* (19.6) `steady_state_iff`, `steady_state_strictMono_r` (higher `r`, higher `p`).
* (19.7) `eq197_iff`; the solution family `caganFamily`, `caganFamily_closed`
  (`p_t − p̄ = θᵗ(p₀ − p̄) + ∑ θ^{t−j}δ_j`), `caganFamily_solves` (every `p₀` and every
  expectational error with `E_tδ_{t+1} = 0`), `eq_caganFamily` (every solution is a member);
  explosions: `pf_path`, `pf_explodes`, `expected_path`, `expected_explodes`,
  `bounded_iff_steady`; multiplicity: `pf_solutions_uncountable`, `coin_sunspot_solves`,
  `coin_sunspot_ne_steady` (sunspots under genuine uncertainty).
* (19.8) `eq198_finite`, `eq198` (the limit term exists iff the series converges), for bounded
  money `eq198_bounded_money`, `limit_zero_iff_bounded` (the limit term vanishes iff the
  solution is the bounded one), `bounded_existsUnique`.
* Fiscal theory selects `P₀` (p. 437): `fiscal_selects_P0`, `fiscal_path_existsUnique`,
  `fiscal_path_bounded_iff` (the selected path is explosive except for one value of `B₋₁`).
* Stochastic version (p. 438): `innov`, `valuation_split`, `stochastic_selection` (the
  valuation equation picks unexpected inflation; with expected inflation it determines `B_t`).
-/

namespace Cochrane.Monetarism.CaganRE

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15 summable_A16 existsUnique_bounded
  solves_adapted E_of_known forwardSeries_bounded_abs)
open Cochrane.Monetarism.ExpectationsFiniteTree (coinSystem coinShock coinShock_measurable
  coinShock_mean_zero coinTree)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.4)–(19.5) -/

/-- Cochrane (2023), eq. (19.4), p. 436: money demand `M_t = P_t y V^{−αi_t}` holds in levels iff
it holds in logs, `m_t − p_t − y = −αi_t v` (`v = log V`). -/
theorem eq194_iff_log {M P Y V α i : ℝ} (hM : 0 < M) (hP : 0 < P) (hY : 0 < Y) (hV : 0 < V) :
    M = P * Y * V ^ (-α * i) ↔
      Real.log M - Real.log P - Real.log Y = -α * i * Real.log V := by
  have hR : 0 < P * Y * V ^ (-α * i) := by positivity
  have hlog : Real.log (P * Y * V ^ (-α * i)) =
      Real.log P + Real.log Y + -α * i * Real.log V := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hP.ne' hY.ne',
      Real.log_rpow hV]
  constructor
  · intro h
    rw [h, hlog]
    ring
  · intro h
    have : Real.log M = Real.log (P * Y * V ^ (-α * i)) := by rw [hlog]; linarith
    rw [← Real.exp_log hM, ← Real.exp_log hR, this]

/-- Cochrane (2023), eq. (19.4), p. 436, in logs: `m_t − p_t − y = −a i_t` with `a = αv`. -/
def MoneyDemand (a y : ℝ) (m p i : ℕ → Ω → ℝ) : Prop := ∀ t ω, m t ω - p t ω - y = -a * i t ω

/-- Cochrane (2023), p. 436: the Fisher equation `i_t = r + E_tp_{t+1} − p_t`. -/
def Fisher (r : ℝ) (p i : ℕ → Ω → ℝ) : Prop := ∀ t ω, i t ω = r + 𝔼.E t (p (t + 1)) ω - p t ω

/-- Cochrane (2023), eq. (19.5), p. 436: `m_t − p_t − y = −a(r + E_tp_{t+1} − p_t)`. -/
def Cagan (a y r : ℝ) (m p : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, m t ω - p t ω - y = -a * (r + 𝔼.E t (p (t + 1)) ω - p t ω)

/-- Cochrane (2023), (19.4)–(19.5), p. 436: money demand and the Fisher equation hold iff the
Cagan equation (19.5) and the Fisher equation hold. -/
theorem md_fisher_iff_cagan {a y r : ℝ} {m p i : ℕ → Ω → ℝ} :
    MoneyDemand a y m p i ∧ Fisher 𝔼 r p i ↔ Cagan 𝔼 a y r m p ∧ Fisher 𝔼 r p i := by
  constructor
  · rintro ⟨hmd, hf⟩
    exact ⟨fun t ω => by rw [hmd t ω, hf t ω], hf⟩
  · rintro ⟨hc, hf⟩
    exact ⟨fun t ω => by rw [hc t ω, hf t ω], hf⟩

/-- Cochrane (2023), p. 437: `θ ≡ (1 + αv)/(αv)`. -/
noncomputable def theta (a : ℝ) : ℝ := (1 + a) / a

/-- Cochrane (2023), p. 437: `θ > 1` for `a = αv > 0`. -/
theorem theta_gt_one {a : ℝ} (ha : 0 < a) : 1 < theta a := by
  unfold theta
  rw [one_lt_div ha]
  linarith

/-- Cochrane (2023), p. 437: `θ⁻¹ = a/(1 + a)`. -/
theorem theta_inv {a : ℝ} : (theta a)⁻¹ = a / (1 + a) := by
  unfold theta
  rw [inv_div]

/-- Cochrane (2023), p. 437: `|θ⁻¹| < 1` for `a > 0`. -/
theorem abs_theta_inv_lt_one {a : ℝ} (ha : 0 < a) : |(theta a)⁻¹| < 1 := by
  rw [theta_inv, abs_of_pos (by positivity), div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), eq. (19.5), second line, p. 436:
`E_tp_{t+1} = ((1 + a)/a)p_t − (m_t − y)/a − r`. -/
theorem cagan_iff_expect {a y r : ℝ} (ha : a ≠ 0) {m p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r m p ↔
      ∀ t ω, 𝔼.E t (p (t + 1)) ω = theta a * p t ω - (m t ω - y) / a - r := by
  unfold theta
  constructor
  · intro h t ω
    have := h t ω
    field_simp
    linarith
  · intro h t ω
    have := h t ω
    field_simp at this
    linarith

/-- Cochrane (2023), (19.8), p. 437: the forcing `x_t = m_t − y + ar` (`ar` = the book's
`αvr`). -/
def forcing (a y r : ℝ) (m : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => m t ω - y + a * r

/-- Cochrane (2023), eq. (19.8), first lines, p. 437: the Cagan equation is the forward equation
`p_t = θ⁻¹E_tp_{t+1} + (1 − θ⁻¹)x_t`. -/
theorem cagan_iff_solves {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r m p ↔
      Solves 𝔼 (theta a)⁻¹ (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) p := by
  rw [theta_inv]
  have h1 : (1 + a) ≠ 0 := by linarith
  constructor
  · intro h t
    funext ω
    have := h t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, forcing]
    field_simp
    linarith
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, forcing] at this
    field_simp at this
    linarith

/-- Cochrane (2023), (19.8), p. 437: the forcing is adapted when money is. -/
theorem forcing_adapted {a y r : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m) :
    𝔼.Adapted (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) := fun t => by
  change 𝔼.E t ((1 - (theta a)⁻¹) • forcing a y r m t) = (1 - (theta a)⁻¹) • forcing a y r m t
  have h : forcing a y r m t = m t + fun _ => -y + a * r := by
    funext ω
    simp only [forcing, Pi.add_apply]
    ring
  rw [map_smul, h, map_add, hm t, 𝔼.const]

/-! ### (19.6)–(19.7): constant money -/

/-- Cochrane (2023), eq. (19.6), p. 436: the steady-state price level `p̄ = m − y + αvr`. -/
def pbar (a y r mbar : ℝ) : ℝ := mbar - y + a * r

/-- Cochrane (2023), eq. (19.6), p. 436: with constant money `m`, a constant price level `c`
solves (19.5) iff `c = m − y + αvr`. -/
theorem steady_state_iff [Nonempty Ω] {a y r mbar c : ℝ} :
    Cagan 𝔼 a y r (fun _ _ => mbar) (fun _ _ => c) ↔ c = pbar a y r mbar := by
  unfold pbar
  have hE : ∀ t ω, 𝔼.E t (fun _ => c) ω = c := fun t ω => by rw [𝔼.const]
  constructor
  · intro h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := h 0 ω
    rw [hE] at this
    linarith
  · intro h t ω
    rw [hE, h]
    ring

/-- Cochrane (2023), p. 436 ("The steady-state price level is higher as the real interest rate
is higher"): `r ↦ m − y + αvr` is strictly increasing for `αv > 0`. -/
theorem steady_state_strictMono_r {a y mbar : ℝ} (ha : 0 < a) :
    StrictMono (fun r => pbar a y r mbar) := fun r r' h => by
  unfold pbar
  nlinarith

/-- Cochrane (2023), eq. (19.7), p. 436: with constant money, the equilibrium price levels are
exactly the processes with `E_tp_{t+1} − p̄ = θ(p_t − p̄)`. -/
theorem eq197_iff {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r (fun _ _ => mbar) p ↔
      ∀ t ω, 𝔼.E t (p (t + 1)) ω - pbar a y r mbar = theta a * (p t ω - pbar a y r mbar) := by
  rw [cagan_iff_expect 𝔼 ha.ne']
  unfold theta pbar
  constructor
  · intro h t ω
    rw [h t ω]
    field_simp
    ring
  · intro h t ω
    have := h t ω
    field_simp at this ⊢
    linarith

/-- Cochrane (2023), p. 437: the family `p_0` given and
`p_{t+1} − p̄ = θ(p_t − p̄) + δ_{t+1}`. -/
noncomputable def caganFamily (θ pb : ℝ) (p0 : Ω → ℝ) (δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p0
  | t + 1 => fun ω => pb + θ * (caganFamily θ pb p0 δ t ω - pb) + δ (t + 1) ω

omit 𝔼 in
/-- Cochrane (2023), p. 437, the full set of solutions in closed form:
`p_t − p̄ = θᵗ(p_0 − p̄) + ∑_{j=1}^t θ^{t−j}δ_j` (written with `k = t − j`). -/
theorem caganFamily_closed (θ pb : ℝ) (p0 : Ω → ℝ) (δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    caganFamily θ pb p0 δ t ω =
      pb + θ ^ t * (p0 ω - pb) + ∑ k ∈ Finset.range t, θ ^ k * δ (t - k) ω := by
  induction t with
  | zero => simp [caganFamily]
  | succ t ih =>
    simp only [caganFamily]
    have hs : ∀ k ∈ Finset.range t, θ * (θ ^ k * δ (t - k) ω) =
        θ ^ (k + 1) * δ (t + 1 - (k + 1)) ω := fun k _ => by
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [ih, Finset.sum_range_succ', ← Finset.sum_congr rfl hs, ← Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero, pow_succ]
    ring

/-- Cochrane (2023), p. 437: the family is adapted when `p_0` and `δ` are. -/
theorem caganFamily_adapted {θ pb : ℝ} {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδ : 𝔼.Adapted δ) : 𝔼.Adapted (caganFamily θ pb p0 δ) := by
  intro t
  induction t with
  | zero => exact hp0
  | succ t ih =>
    have h : caganFamily θ pb p0 δ (t + 1) =
        (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + δ (t + 1) := by
      funext ω
      simp only [caganFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, map_add, map_add, map_smul, 𝔼.const, E_of_known 𝔼 (Nat.le_succ t) ih, hδ (t + 1)]

/-- Cochrane (2023), p. 437: one step of the family, conditional expectation:
`E_tp_{t+1} − p̄ = θ(p_t − p̄) + E_tδ_{t+1}`. -/
theorem caganFamily_E_succ {θ pb : ℝ} {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδ : 𝔼.Adapted δ) (t : ℕ) :
    𝔼.E t (caganFamily θ pb p0 δ (t + 1)) =
      (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + 𝔼.E t (δ (t + 1)) := by
  have h : caganFamily θ pb p0 δ (t + 1) =
      (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + δ (t + 1) := by
    funext ω
    simp only [caganFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, map_add, map_add, map_smul, 𝔼.const, caganFamily_adapted 𝔼 hp0 hδ t]

/-- Cochrane (2023), p. 437 ("the model restricts `E_tδ_{t+1} = 0`, but the expectational error
`δ_{t+1}` can take any value ex-post"): for every initial `p_0` known at date 0 and every adapted
`δ` with `E_tδ_{t+1} = 0`, the family solves (19.5) with constant money. -/
theorem caganFamily_solves {a y r mbar : ℝ} (ha : 0 < a) {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ}
    (hp0 : 𝔼.E 0 p0 = p0) (hδ : 𝔼.Adapted δ) (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    Cagan 𝔼 a y r (fun _ _ => mbar) (caganFamily (theta a) (pbar a y r mbar) p0 δ) := by
  rw [eq197_iff 𝔼 ha]
  intro t ω
  rw [caganFamily_E_succ 𝔼 hp0 hδ t, hmd t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- Cochrane (2023), p. 437 ("the full set of solutions"): every solution of (19.5) with
constant money is the member of the family with its own `p_0` and expectational errors
`δ_{t+1} = p_{t+1} − E_tp_{t+1}`, which satisfy `E_tδ_{t+1} = 0`. -/
theorem eq_caganFamily {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) :
    (∀ t, 𝔼.E t (p (t + 1) - 𝔼.E t (p (t + 1))) = 0) ∧
      p = caganFamily (theta a) (pbar a y r mbar) (p 0)
        (fun t => p t - 𝔼.E (t - 1) (p t)) := by
  refine ⟨fun t => by rw [map_sub, 𝔼.E_E_self, sub_self], ?_⟩
  have h197 := (eq197_iff 𝔼 ha).mp hp
  funext t ω
  induction t generalizing ω with
  | zero => rfl
  | succ t ih =>
    simp only [caganFamily, ← ih, Nat.add_sub_cancel, Pi.sub_apply]
    have := h197 t ω
    linarith

/-- Cochrane (2023), p. 437, under perfect foresight: every solution with constant money is
`p_t = p̄ + θᵗ(p_0 − p̄)`. -/
theorem pf_path {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Unit → ℝ}
    (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p) (t : ℕ) :
    p t () = pbar a y r mbar + theta a ^ t * (p 0 () - pbar a y r mbar) := by
  have h197 := (eq197_iff perfectForesight ha).mp hp
  induction t with
  | zero => simp
  | succ t ih =>
    have := h197 t ()
    change p (t + 1) () - _ = _ at this
    have e : p (t + 1) () = pbar a y r mbar + theta a * (p t () - pbar a y r mbar) := by
      linarith
    rw [e, ih, pow_succ]
    ring

/-- Cochrane (2023), p. 437 ("The alternative solutions are explosive"): under perfect foresight
every solution with `p_0 ≠ p̄` explodes, `|p_t − p̄| → ∞`. -/
theorem pf_explodes {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Unit → ℝ}
    (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p) (h0 : p 0 () ≠ pbar a y r mbar) :
    Tendsto (fun t => |p t () - pbar a y r mbar|) atTop atTop := by
  have hc : 0 < |p 0 () - pbar a y r mbar| := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (theta_gt_one ha)
  refine (hpow.atTop_mul_const hc).congr fun t => ?_
  rw [pf_path ha hp t, add_sub_cancel_left, abs_mul, abs_pow,
    abs_of_pos (by linarith [theta_gt_one ha] : (0 : ℝ) < theta a)]

/-- Cochrane (2023), p. 437 ("At any date for `p_t ≠ p̄`, people expect explosive hyperinflation
or hyperdeflation"): for every solution, `E_0p_t = p̄ + θᵗ(p_0 − p̄)`. -/
theorem expected_path {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) (hp0 : 𝔼.E 0 (p 0) = p 0) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (p t) ω = pbar a y r mbar + theta a ^ t * (p 0 ω - pbar a y r mbar) := by
  have h197 := (eq197_iff 𝔼 ha).mp hp
  induction t generalizing ω with
  | zero => rw [hp0]; simp
  | succ t ih =>
    have hEt : 𝔼.E t (p (t + 1)) = (fun _ => pbar a y r mbar - theta a * pbar a y r mbar) +
        theta a • p t := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [h197 t ω']
    rw [← 𝔼.tower (Nat.zero_le t), hEt, map_add, map_smul, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ih ω, pow_succ]
    ring

/-- Cochrane (2023), p. 437: every solution with `p_0 ≠ p̄` (in state `ω`) has an expected price
path that explodes, `|E_0p_t − p̄| → ∞`. -/
theorem expected_explodes {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) (hp0 : 𝔼.E 0 (p 0) = p 0) {ω : Ω}
    (h0 : p 0 ω ≠ pbar a y r mbar) :
    Tendsto (fun t => |𝔼.E 0 (p t) ω - pbar a y r mbar|) atTop atTop := by
  have hc : 0 < |p 0 ω - pbar a y r mbar| := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (theta_gt_one ha)
  refine (hpow.atTop_mul_const hc).congr fun t => ?_
  rw [expected_path 𝔼 ha hp hp0 t ω, add_sub_cancel_left, abs_mul, abs_pow,
    abs_of_pos (by linarith [theta_gt_one ha] : (0 : ℝ) < theta a)]

/-- Cochrane (2023), p. 437 ("all but `p_t ≡ p̄` explode"): a solution with constant money is
bounded if and only if it is the steady state. -/
theorem bounded_iff_steady {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) :
    BoundedProc p ↔ p = fun _ _ => pbar a y r mbar := by
  constructor
  · intro hb
    have hs := (cagan_iff_solves 𝔼 ha).mp hp
    have hss : Cagan 𝔼 a y r (fun _ _ => mbar) (fun _ _ => pbar a y r mbar) := by
      intro t ω
      rw [𝔼.const]
      unfold pbar
      ring
    have hs2 := (cagan_iff_solves 𝔼 ha).mp hss
    exact 𝔼.forward_unique (abs_theta_inv_lt_one ha) hs hs2 hb
      ⟨|pbar a y r mbar|, fun _ _ => le_refl _⟩
  · rintro rfl
    exact ⟨|pbar a y r mbar|, fun _ _ => le_refl _⟩

/-- Cochrane (2023), p. 437 ("There is a family of solutions"): under perfect foresight with
constant money the set of equilibrium price paths is uncountable (one for each `p_0 ∈ ℝ`). -/
theorem pf_solutions_uncountable {a y r mbar : ℝ} (ha : 0 < a) :
    ¬ {p : ℕ → Unit → ℝ | Cagan perfectForesight a y r (fun _ _ => mbar) p}.Countable := by
  intro hcount
  let f : ℝ → ℕ → Unit → ℝ := fun c t _ => pbar a y r mbar + theta a ^ t * (c - pbar a y r mbar)
  have hmaps : Set.MapsTo f Set.univ
      {p : ℕ → Unit → ℝ | Cagan perfectForesight a y r (fun _ _ => mbar) p} := by
    intro c _
    refine (eq197_iff perfectForesight ha).mpr fun t u => ?_
    change f c (t + 1) u - _ = _
    simp only [f, pow_succ]
    ring
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrFun h 0) ()
    simpa [f] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), p. 437 (genuine uncertainty): on the coin-flip tree the shocks are
adapted. -/
theorem coinShock_adapted : coinSystem.Adapted coinShock := fun t => by
  funext ω
  rw [coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h

/-- Cochrane (2023), p. 437 ("the expectational error `δ_{t+1}` can take any value ex-post"):
under genuine uncertainty (two coin flips), the family started at `p_0 = p̄` with the coin-flip
errors `δ` solves (19.5) with constant money. -/
theorem coin_sunspot_solves {a y r mbar : ℝ} (ha : 0 < a) :
    Cagan coinSystem a y r (fun _ _ => mbar)
      (caganFamily (theta a) (pbar a y r mbar) (fun _ => pbar a y r mbar) coinShock) :=
  caganFamily_solves coinSystem ha (coinSystem.const 0 _) coinShock_adapted coinShock_mean_zero

/-- Cochrane (2023), p. 437: that sunspot solution is not the steady state even though it starts
at `p̄`: after heads at date 1 the price level is `p̄ + 1`. -/
theorem coin_sunspot_ne_steady (θ pb : ℝ) :
    caganFamily θ pb (fun _ => pb) coinShock 1 (true, true) = pb + 1 := by
  simp [caganFamily, coinShock]

/-! ### (19.8): the forward solution -/

/-- Cochrane (2023), eq. (19.8), p. 437, at a finite horizon `T`:
`p_t = (1 − θ⁻¹)∑_{j<T} θ^{−j}E_tx_{t+j} + θ^{−T}E_tp_{t+T}`. -/
theorem eq198_finite {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hp : Cagan 𝔼 a y r m p) (t T : ℕ) (ω : Ω) :
    p t ω = (1 - (theta a)⁻¹) * ∑ j ∈ Finset.range T,
      (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω +
      (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω := by
  have h := congrFun (iterate_A15 𝔼 (forcing_adapted 𝔼 hm) ((cagan_iff_solves 𝔼 ha).mp hp)
    t T) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_smul] at h
  rw [h, Finset.mul_sum]
  have hs : ∑ j ∈ Finset.range T, (theta a)⁻¹ ^ j *
      ((1 - (theta a)⁻¹) * 𝔼.E t (forcing a y r m (t + j)) ω) =
      ∑ j ∈ Finset.range T, (1 - (theta a)⁻¹) *
        ((theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

/-- Cochrane (2023), eq. (19.8), p. 437 ("there is again no reason to set to zero the last
term"): for any solution, the limit term `lim θ^{−T}E_tp_{t+T}` equals `L` if and only if the
forward series `(1 − θ⁻¹)∑θ^{−j}E_tx_{t+j}` converges to `p_t − L`. -/
theorem eq198 {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hp : Cagan 𝔼 a y r m p) (t : ℕ) (ω : Ω) (L : ℝ) :
    Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop (𝓝 L) ↔
      Tendsto (fun T => (1 - (theta a)⁻¹) * ∑ j ∈ Finset.range T,
        (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω) atTop (𝓝 (p t ω - L)) := by
  have hid := eq198_finite 𝔼 ha hm hp t
  constructor
  · intro h
    exact (tendsto_const_nhds.sub h).congr fun T => by rw [hid T ω]; ring
  · intro h
    have h2 := tendsto_const_nhds (x := p t ω) |>.sub h
    rw [sub_sub_cancel] at h2
    exact h2.congr fun T => by rw [hid T ω]; ring

/-- Cochrane (2023), eq. (19.8), p. 437, for bounded money: the series converges for every
solution, so the limit term exists and equals `p_t` minus the forward series. -/
theorem eq198_bounded_money {a y r K : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hK : ∀ t ω, |m t ω| ≤ K) (hp : Cagan 𝔼 a y r m p) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop
      (𝓝 (p t ω - (1 - (theta a)⁻¹) *
        ∑' j, (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω)) := by
  have hx : ∀ t ω, |forcing a y r m t ω| ≤ K + |y| + |a * r| := fun t ω => by
    simp only [forcing]
    have := hK t ω
    have h1 := abs_add_le (m t ω - y) (a * r)
    have h2 := abs_sub (m t ω) y
    have h3 := abs_mul a r
    linarith
  have hsum := summable_A16 𝔼 (abs_theta_inv_lt_one ha) hx t ω
  rw [eq198 𝔼 ha hm hp t ω, sub_sub_cancel]
  exact hsum.hasSum.tendsto_sum_nat.const_mul _

/-- Cochrane (2023), (19.8), p. 437 ("It is tempting to set the last term … to zero and to
declare a unique forward-looking equilibrium"): for bounded money, the limit term vanishes at
every date and state if and only if the solution is bounded. -/
theorem limit_zero_iff_bounded {a y r K : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ}
    (hm : 𝔼.Adapted m) (hK : ∀ t ω, |m t ω| ≤ K) (hp : Cagan 𝔼 a y r m p) :
    (∀ t ω, Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop (𝓝 0)) ↔
      BoundedProc p := by
  have hθ := abs_theta_inv_lt_one ha
  have hu : ∀ t ω, |((1 - (theta a)⁻¹) • forcing a y r m t) ω| ≤
      |1 - (theta a)⁻¹| * (K + |y| + |a * r|) := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, forcing]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := hK t ω
    have h1 := abs_add_le (m t ω - y) (a * r)
    have h2 := abs_sub (m t ω) y
    have h3 := abs_mul a r
    linarith
  constructor
  · intro h
    have heq : p = 𝔼.forwardSeries (theta a)⁻¹ (fun t => (1 - (theta a)⁻¹) • forcing a y r m t)
        := by
      funext t ω
      have h1 := tendsto_nhds_unique (h t ω) (eq198_bounded_money 𝔼 ha hm hK hp t ω)
      have h2 : p t ω = (1 - (theta a)⁻¹) *
          ∑' j, (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω := by linarith
      rw [h2, ← tsum_mul_left]
      simp only [ExpectationSystem.forwardSeries, map_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_congr fun j => by ring
    rw [heq]
    exact forwardSeries_bounded_abs 𝔼 hθ hu
  · rintro ⟨M, hM⟩ t ω
    refine squeeze_zero_norm (a := fun T => |(theta a)⁻¹| ^ T * M) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω)
        (pow_nonneg (abs_nonneg _) T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hθ).mul_const M

/-- Cochrane (2023), p. 437 ("most papers simply pick the bounded solution"): for bounded adapted
money there is exactly one bounded solution of (19.5). -/
theorem bounded_existsUnique {a y r : ℝ} (ha : 0 < a) {m : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hmb : BoundedProc m) : ∃! p, BoundedProc p ∧ Cagan 𝔼 a y r m p := by
  obtain ⟨K, hK⟩ := hmb
  have hub : BoundedProc (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) :=
    ⟨|1 - (theta a)⁻¹| * (K + |y| + |a * r|), fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, forcing]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := hK t ω
      have h1 := abs_add_le (m t ω - y) (a * r)
      have h2 := abs_sub (m t ω) y
      have h3 := abs_mul a r
      linarith⟩
  obtain ⟨p, hp, hu⟩ := existsUnique_bounded 𝔼 (abs_theta_inv_lt_one ha) hub
    (forcing_adapted 𝔼 hm)
  exact ⟨p, ⟨hp.1, (cagan_iff_solves 𝔼 ha).mpr hp.2⟩,
    fun q hq => hu q ⟨hq.1, (cagan_iff_solves 𝔼 ha).mp hq.2⟩⟩

/-! ### Fiscal theory selects `P₀` (pp. 437–438) -/

/-- Cochrane (2023), p. 437 ("This condition picks the one missing element, `P_0`"): with
`B_{−1} > 0` and present value of surpluses `∑βʲs_j = S > 0`, exactly one positive `P_0`
satisfies `B_{−1}/P_0 = ∑βʲs_j`. -/
theorem fiscal_selects_P0 {β B S : ℝ} {s : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hB : 0 < B) (hS : 0 < S) : ∃! P0 : ℝ, 0 < P0 ∧ B / P0 = ∑' j, β ^ j * s j := by
  rw [hs.tsum_eq]
  refine ⟨B / S, ⟨div_pos hB hS, by field_simp⟩, fun P0 hP0 => ?_⟩
  have := hP0.1
  rw [eq_div_iff hS.ne', ← hP0.2]
  field_simp

/-- Cochrane (2023), pp. 437–438 ("we now fully determine the price level"): under perfect
foresight with constant money, there is exactly one price path satisfying (19.5) and the
valuation equation `B_{−1}/P_0 = ∑βʲs_j` (with `P_0 = e^{p_0}`). -/
theorem fiscal_path_existsUnique {a y r mbar β B S : ℝ} {s : ℕ → ℝ} (ha : 0 < a)
    (hs : HasSum (fun j => β ^ j * s j) S) (hB : 0 < B) (hS : 0 < S) :
    ∃! p : ℕ → Unit → ℝ, Cagan perfectForesight a y r (fun _ _ => mbar) p ∧
      B / Real.exp (p 0 ()) = ∑' j, β ^ j * s j := by
  rw [hs.tsum_eq]
  refine ⟨fun t _ => pbar a y r mbar + theta a ^ t * (Real.log (B / S) - pbar a y r mbar),
    ⟨(eq197_iff perfectForesight ha).mpr fun t u => ?_, ?_⟩, fun q hq => ?_⟩
  · change (pbar a y r mbar + theta a ^ (t + 1) * _) - _ = _
    rw [pow_succ]
    ring
  · simp only [pow_zero, one_mul, add_sub_cancel, Real.exp_log (div_pos hB hS)]
    field_simp
  · have h0 : q 0 () = Real.log (B / S) := by
      have h := hq.2
      have hE : Real.exp (q 0 ()) = B / S := by
        rw [eq_div_iff hS.ne', ← h]
        field_simp
      rw [← hE, Real.log_exp]
    funext t u
    rw [pf_path ha hq.1 t, h0]

/-- Cochrane (2023), p. 438 ("The solution picked in this way will generically be one of the
explosive solutions"): the fiscally selected path is bounded if and only if
`B_{−1} = e^{p̄}∑βʲs_j`; for every other value of the initial debt it explodes. -/
theorem fiscal_path_bounded_iff {a y r mbar B S : ℝ} (ha : 0 < a) (hB : 0 < B) (hS : 0 < S)
    {p : ℕ → Unit → ℝ} (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p)
    (hv : B / Real.exp (p 0 ()) = S) :
    BoundedProc p ↔ B = S * Real.exp (pbar a y r mbar) := by
  have hE : Real.exp (p 0 ()) = B / S := by
    rw [eq_div_iff hS.ne', ← hv]
    field_simp
  rw [bounded_iff_steady perfectForesight ha hp]
  constructor
  · intro h
    have h0 := congrFun (congrFun h 0) ()
    rw [h0] at hE
    rw [hE]
    field_simp
  · intro h
    have h0 : p 0 () = pbar a y r mbar := by
      rw [← Real.log_exp (p 0 ()), hE, h, mul_div_cancel_left₀ _ hS.ne', Real.log_exp]
    funext t u
    rw [pf_path ha hp t, h0, sub_self, mul_zero, add_zero]

/-! ### The stochastic version (p. 438) -/

/-- Cochrane (2023), p. 438 (notation `ΔE_{t+1} = E_{t+1} − E_t`): the innovation. -/
def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), p. 438: for variables known at `t + 1`, an equation holds iff it holds in
innovations and in date-`t` expectation. -/
theorem valuation_split {t : ℕ} {X V : Ω → ℝ} (hX : 𝔼.E (t + 1) X = X)
    (hV : 𝔼.E (t + 1) V = V) : X = V ↔ innov 𝔼 t X = innov 𝔼 t V ∧ 𝔼.E t X = 𝔼.E t V := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have e1 : X = innov 𝔼 t X + 𝔼.E t X := by rw [innov, hX]; abel
    have e2 : V = innov 𝔼 t V + 𝔼.E t V := by rw [innov, hV]; abel
    rw [e1, e2, h1, h2]

/-- Cochrane (2023), p. 438: the stochastic valuation equation
`(B_t/P_t)(P_t/P_{t+1}) = E_{t+1}∑βʲs_{t+1+j}` (with `b = B_t/P_t` known at `t`, `R = P_t/P_{t+1}`
known at `t + 1`, `V` the present value known at `t + 1`) holds iff
`b·ΔE_{t+1}R = ΔE_{t+1}V` ("picks unexpected inflation") and `b·E_tR = E_tV`. Hence where
`b ≠ 0` unexpected inflation is `ΔE_{t+1}V/b`, and where `E_tR ≠ 0` real debt sales are
`b = E_tV/E_tR` ("with expected inflation picked by (19.7) determines nominal bond sales"). -/
theorem stochastic_selection (hPO : 𝔼.PullOut) {t : ℕ} {b R V : Ω → ℝ} (hb : 𝔼.E t b = b)
    (hR : 𝔼.E (t + 1) R = R) (hV : 𝔼.E (t + 1) V = V) :
    (b * R = V ↔ b * innov 𝔼 t R = innov 𝔼 t V ∧ b * 𝔼.E t R = 𝔼.E t V) ∧
      (b * R = V → ∀ ω, b ω ≠ 0 → innov 𝔼 t R ω = innov 𝔼 t V ω / b ω) ∧
      (b * R = V → ∀ ω, 𝔼.E t R ω ≠ 0 → b ω = 𝔼.E t V ω / 𝔼.E t R ω) := by
  have hb1 : 𝔼.E (t + 1) b = b := E_of_known 𝔼 (Nat.le_succ t) hb
  have hbR : 𝔼.E (t + 1) (b * R) = b * R := by rw [hPO _ _ _ hb1, hR]
  have hinn : innov 𝔼 t (b * R) = b * innov 𝔼 t R := by
    simp only [innov]
    rw [hPO _ _ _ hb1, hPO _ _ _ hb, mul_sub]
  have hEt : 𝔼.E t (b * R) = b * 𝔼.E t R := hPO _ _ _ hb
  have key : b * R = V ↔ b * innov 𝔼 t R = innov 𝔼 t V ∧ b * 𝔼.E t R = 𝔼.E t V := by
    rw [valuation_split 𝔼 hbR hV, hinn, hEt]
  refine ⟨key, fun h ω hω => ?_, fun h ω hω => ?_⟩
  · have := congrFun ((key.mp h).1) ω
    simp only [Pi.mul_apply] at this
    rw [← this]
    field_simp
  · have := congrFun ((key.mp h).2) ω
    simp only [Pi.mul_apply] at this
    rw [← this]
    field_simp

end Cochrane.Monetarism.CaganRE

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in the utility function

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 438–445,
eqs. (19.9)–(19.23) and Figure 19.1.

## Main results

* Budget constraints (19.10)–(19.12): `HHFlow`, `hhFlow_iff_flow`, `eq1911_iff_tvc` (the present
  value budget constraint (19.11) holds iff the transversality condition does), `eq1912_of_tvc`,
  `equilibrium_valuation` (with `c = y` the household's (19.12) is the government's (19.3)).
* First-order conditions (19.13)–(19.14), from the time-0 problem of footnote 1 (perfect
  foresight, genuine infinite horizon, no Lagrange-multiplier theorem assumed): `Feasible`,
  `Optimal`, `tsum_modify_two`, `perturb_le`, `foc_cc`, `foc_mc`, `foc_1913_1914` (with
  `λ = u_c(c_0, m_0)`, as in the footnote); sufficiency under concavity: `concave_le_tangent`,
  `supergradient_of_concave`, `optimal_of_foc`.
* Footnote 1 under uncertainty, on a finite event tree (genuine infinite horizon): `FootnoteTree`
  (`TAdapted`, `dateCost`, `dateUtil`, `TFeasible`, `TOptimal`, `cell`, `cell_adapted`,
  `sum_perturb_cell`, `perturb_adapted`, `tperturb_le`), node first-order conditions by
  cost-neutral perturbations at a node, `tree_foc_cc`, `tree_foc_mc`, `tree_foc_1913_1914`,
  `lambda_const`, and sufficiency under concavity `tree_optimal_of_foc`.
* Knownness of `Λ_t/P_t` and `P_t/u_c(t)`: `known_mul`, `known_inv`, `known_div` (with
  pull-out, products, reciprocals of nowhere-zero and quotients of known variables are known, on
  any state space), `known_prod`, `functionsKnown_of_fintype` (on a finite state space, every
  function of a known variable is known), `known_div_of_fintype` (no nonvanishing needed), and
  versions without the knownness hypotheses, on any state space: `eq1911_iff_tvc_adapted`,
  `eq1912_of_tvc_adapted`, `value_of_money_iterated_adapted`, `value_of_money_limit_adapted`.
* (19.15)–(19.16) and the value of money: `convenience_identity`
  (`1 = u_m/u_c + E_tβu_c'P/(u_cP')`), `value_recursion`, `value_of_money_iterated` (the iterated
  formula of p. 441), `value_of_money_limit`; money demand `lm_unique`, `lm_exists`.
* Separable perfect foresight (19.17)–(19.19): `price_ratio_eq`, `eq1918_iff`, `IsMIUPath`,
  `steady_state_path_iff`, `steady_state_inflation`, `steady_state_existsUnique`; the second
  (zero-rate) steady state `zero_rate_iff`, `deflation_approx`, satiation
  `satiation_absorbing`, `limit_rate_zero`, `money_demand_correspondence`.
* Power utility (19.20)–(19.23): `hasDerivAt_power`, `power_money_demand`, `power_um_ratio`,
  `IsPowerPath`, `eq1922`, `eq1922_exact`, `eq1922_partial_delta`, `eq1922_partial_mu`,
  `eq1922_approx`; calibration `calib_unit`, `calib_ten`, `calib_ten_gamma_one`,
  `calib_ten_gamma_two` (imprecision: `θ ≈ 0.01` needs `γ = 1`), `calib_interest_cost`;
  (19.23) `nextX`, `eq1923_iff`, `inflation_eq1923`.
* Figure 19.1 (`δ = µ = 0.2`, `γ = 2`, `θ = 0.01`): `fig191_steady`, `fig191_xbar_bounds`
  (`x̄ ≈ 5.53`), `nextX_hasDerivAt`, `slope_gt_one` (cuts from below), `fig191_slope`
  (`1.88`), `fig191_pole` (pole at `x = 10`), `deflation_limit` (`P_{t+1}/P_t → 1/(1 + δ)`).
* Survey error E13: `e13_corrected` (the deflationary steady state attracts, `x̄` exists and
  `x_{t+1}/x_t → β/(1 + µ) < 1`, iff `1 + µ > β`, not `1 + µ > 1/β`), `e13_printed_fails`.
* p. 445: `fiscal_determines_path` (active fiscal policy pins `P_0`, hence the whole path).
-/

namespace Cochrane.Monetarism.MoneyInUtility

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.10)–(19.12): budget constraints -/

/-- Cochrane (2023), eq. (19.10), p. 439: the household's period budget constraint
`B_{t−1} + M_{t−1} + P_t(y_t − c_t) = Q_tB_t + M_t + P_ts_t` (`Bm t = B_{t−1}`,
`N t = M_{t−1}`). -/
def HHFlow (Bm N P y c s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Bm t + N t + P t * (y t - c t) = Q t * Bm (t + 1) + N (t + 1) + P t * s t

/-- Cochrane (2023), (19.10), p. 439: the household constraint is the government's flow
constraint with surplus replaced by `s + c − y`. -/
theorem hhFlow_iff_flow {Bm N P y c s Q : ℕ → Ω → ℝ} :
    HHFlow Bm N P y c s Q ↔ Regimes.Flow Bm N P (fun t => s t + c t - y t) Q := by
  constructor
  · intro h t
    rw [← sub_eq_zero]
    have := h t
    rw [← sub_eq_zero] at this
    rw [← this]
    ring
  · intro h t
    rw [← sub_eq_zero]
    have := h t
    rw [← sub_eq_zero] at this
    rw [← this]
    ring

/-- Cochrane (2023), eq. (19.11), p. 439 ("their optimal choices include transversality
conditions. Thereby the household must satisfy the present value budget constraints"): given
the period constraint (19.10) and bond pricing, (19.11) holds (as the limit of partial sums,
multiplied by `Λ_t`) if and only if the transversality condition
`E_t[Λ_{t+T}B_{t+T−1}/P_{t+T}] → 0` holds. -/
theorem eq1911_iff_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => Regimes.partial192 𝔼 Λ P N (fun k => s k + c k - y k) t T ω) atTop
        (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) :=
  Regimes.flow_pv_iff_tvc 𝔼 hPO hBP hφ hBa hB hQ hi hP (hhFlow_iff_flow.mp hflow) t ω

/-- Cochrane (2023), eq. (19.12), p. 439: with both transversality conditions the household's
present-value budget constraint holds in the form (19.12). -/
theorem eq1912_of_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => Regimes.partial193 𝔼 Λ P N i (fun k => s k + c k - y k) t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  Regimes.flow_eq193_of_tvc 𝔼 hPO hBP hφ hBa hB hNa hN hQ hi hP (hhFlow_iff_flow.mp hflow)
    hbond hmoney

/-- Cochrane (2023), p. 440 ("The eventual government debt valuation equation results from the
consumer's budget constraint, and equilibrium `c_t = y_t`"): with `c = y` the household's
(19.12) is the government's valuation equation (19.3). -/
theorem equilibrium_valuation {Λ P N i y s : ℕ → Ω → ℝ} (t T : ℕ) :
    Regimes.partial193 𝔼 Λ P N i (fun k => s k + y k - y k) t T =
      Regimes.partial193 𝔼 Λ P N i s t T := by
  simp only [add_sub_cancel_right]

/-! ### (19.13)–(19.14): first-order conditions of the time-0 problem (footnote 1) -/

/-- Cochrane (2023), p. 440, footnote 1 (perfect foresight): a plan of consumption `c` and real
money `m = M/P` is feasible when its cost `∑ q_t(c_t + ι_tm_t)` converges and is at most wealth
`W`; `q_t = Λ_t/Λ_0` and `ι_t = i_t/(1 + i_t)`. -/
def Feasible (q ι : ℕ → ℝ) (W : ℝ) (c m : ℕ → ℝ) : Prop :=
  Summable (fun t => q t * (c t + ι t * m t)) ∧ ∑' t, q t * (c t + ι t * m t) ≤ W

/-- Cochrane (2023), (19.9), p. 439 and footnote 1, p. 440: an optimal plan maximises
`∑βᵗu(c_t, m_t)` over feasible plans with summable utility. -/
def Optimal (β : ℝ) (u : ℝ → ℝ → ℝ) (q ι : ℕ → ℝ) (W : ℝ) (c m : ℕ → ℝ) : Prop :=
  Feasible q ι W c m ∧ Summable (fun t => β ^ t * u (c t) (m t)) ∧
    ∀ c' m', Feasible q ι W c' m' → Summable (fun t => β ^ t * u (c' t) (m' t)) →
      ∑' t, β ^ t * u (c' t) (m' t) ≤ ∑' t, β ^ t * u (c t) (m t)

/-- Cochrane (2023), footnote 1, p. 440 (perturbation tool): changing a summable sequence at two
dates keeps it summable and changes its sum by the two changes. -/
theorem tsum_modify_two {f g : ℕ → ℝ} {t s : ℕ} (hts : t ≠ s)
    (hfg : ∀ k, k ≠ t → k ≠ s → g k = f k) (hf : Summable f) :
    Summable g ∧ ∑' k, g k = ∑' k, f k + (g t - f t) + (g s - f s) := by
  have hz : ∀ k ∉ ({t, s} : Finset ℕ), (g - f) k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hfg k hk.1 hk.2]
  have hs : Summable (g - f) := summable_of_ne_finset_zero hz
  have hg : g = f + (g - f) := by abel
  refine ⟨hg ▸ hf.add hs, ?_⟩
  have e1 : ∑' k, (f + (g - f)) k = ∑' k, f k + ∑' k, (g - f) k :=
    (hf.hasSum.add hs.hasSum).tsum_eq
  rw [hg, e1, tsum_eq_sum hz, Finset.sum_pair hts]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), footnote 1, p. 440: a cost-neutral change of an optimal plan at two dates
`t ≠ s` cannot raise utility at those dates. -/
theorem perturb_le {β W : ℝ} {u : ℝ → ℝ → ℝ} {q ι c m c' m' : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m) {t s : ℕ} (hts : t ≠ s)
    (hc : ∀ k, k ≠ t → k ≠ s → c' k = c k) (hm : ∀ k, k ≠ t → k ≠ s → m' k = m k)
    (hcost : q t * (c' t + ι t * m' t) + q s * (c' s + ι s * m' s) =
      q t * (c t + ι t * m t) + q s * (c s + ι s * m s)) :
    β ^ t * u (c' t) (m' t) + β ^ s * u (c' s) (m' s) ≤
      β ^ t * u (c t) (m t) + β ^ s * u (c s) (m s) := by
  obtain ⟨⟨hfs, hfW⟩, hus, hmax⟩ := hopt
  have h1 := tsum_modify_two (f := fun k => q k * (c k + ι k * m k))
    (g := fun k => q k * (c' k + ι k * m' k)) hts
    (fun k hkt hks => by simp only [hc k hkt hks, hm k hkt hks]) hfs
  have h2 := tsum_modify_two (f := fun k => β ^ k * u (c k) (m k))
    (g := fun k => β ^ k * u (c' k) (m' k)) hts
    (fun k hkt hks => by simp only [hc k hkt hks, hm k hkt hks]) hus
  have hfeas : Feasible q ι W c' m' := ⟨h1.1, by rw [h1.2]; linarith⟩
  have := hmax c' m' hfeas h2.1
  rw [h2.2] at this
  linarith

/-- Cochrane (2023), eq. (19.13), p. 440 (cross-date form): at an optimum, for dates `t ≠ s`,
`βᵗu_c(t)q_s = βˢu_c(s)q_t` (shift consumption between `t` and `s` at constant cost). -/
theorem foc_cc {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k)) {t s : ℕ}
    (hts : t ≠ s) : β ^ t * uc (c t) (m t) * q s = β ^ s * uc (c s) (m s) * q t := by
  set D : ℝ → ℝ := fun ε => β ^ t * u (c t + ε * q s) (m t) + β ^ s * u (c s - ε * q t) (m s)
    with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := perturb_le (c' := Function.update (Function.update c t (c t + ε * q s)) s
      (c s - ε * q t)) (m' := m) hopt hts (fun k hkt hks => by
        simp [Function.update_of_ne hks, Function.update_of_ne hkt]) (fun _ _ _ => rfl)
      (by simp [Function.update_of_ne hts]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => c t + ε * q s) (q s) 0 := by
    simpa using (hasDerivAt_mul_const (q s)).const_add (c t)
  have hd2 : HasDerivAt (fun ε => c s - ε * q t) (-q t) 0 := by
    simpa using (hasDerivAt_mul_const (q t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t + ε * q s) (m t)) (uc (c t) (m t) * q s) 0 :=
    HasDerivAt.comp_of_eq 0 (huc t) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * q t) (m s)) (uc (c s) (m s) * -q t) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s) hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (uc (c t) (m t) * q s) +
      β ^ s * (uc (c s) (m s) * -q t)) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440 (cross-date form): at an optimum, for dates
`t ≠ s`, `βᵗu_m(t)q_s = βˢu_c(s)q_tι_t` (trade real money at `t` against consumption at `s`). -/
theorem foc_mc {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) {t s : ℕ}
    (hts : t ≠ s) : β ^ t * um (c t) (m t) * q s = β ^ s * uc (c s) (m s) * q t * ι t := by
  set D : ℝ → ℝ := fun ε =>
    β ^ t * u (c t) (m t + ε * q s) + β ^ s * u (c s - ε * (q t * ι t)) (m s) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := perturb_le (c' := Function.update c s (c s - ε * (q t * ι t)))
      (m' := Function.update m t (m t + ε * q s)) hopt hts
      (fun k _ hks => by simp [Function.update_of_ne hks])
      (fun k hkt _ => by simp [Function.update_of_ne hkt])
      (by simp [Function.update_of_ne hts, Function.update_of_ne hts.symm]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => m t + ε * q s) (q s) 0 := by
    simpa using (hasDerivAt_mul_const (q s)).const_add (m t)
  have hd2 : HasDerivAt (fun ε => c s - ε * (q t * ι t)) (-(q t * ι t)) 0 := by
    simpa using (hasDerivAt_mul_const (q t * ι t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t) (m t + ε * q s)) (um (c t) (m t) * q s) 0 :=
    HasDerivAt.comp_of_eq 0 (hum t) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * (q t * ι t)) (m s))
      (uc (c s) (m s) * -(q t * ι t)) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s) hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (um (c t) (m t) * q s) +
      β ^ s * (uc (c s) (m s) * -(q t * ι t))) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, and footnote 1: at an optimal plan of the
time-0 problem (with `q_0 = Λ_0/Λ_0 = 1`, `q_1 > 0`), with the multiplier
`λ = u_c(c_0, M_0/P_0)`, `βᵗu_c(c_t, M_t/P_t) = λΛ_t/Λ_0` and
`βᵗu_m(c_t, M_t/P_t) = λ(Λ_t/Λ_0) i_t/(1 + i_t)` at every date. -/
theorem foc_1913_1914 {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m) (hq0 : q 0 = 1) (hq1 : 0 < q 1)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) (t : ℕ) :
    β ^ t * uc (c t) (m t) = uc (c 0) (m 0) * q t ∧
      β ^ t * um (c t) (m t) = uc (c 0) (m 0) * q t * ι t := by
  have hc : ∀ k, β ^ k * uc (c k) (m k) = uc (c 0) (m 0) * q k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hq0]
    · have := foc_cc hopt huc (Nat.pos_iff_ne_zero.mp hk)
      rw [hq0] at this
      simpa using this
  refine ⟨hc t, ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 := foc_mc hopt huc hum (t := 0) (s := 1) zero_ne_one
    have h2 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h1 h2 ⊢
    rw [h2] at h1
    have : um (c 0) (m 0) * q 1 = uc (c 0) (m 0) * q 0 * ι 0 * q 1 := by rw [hq0] at h1 ⊢; linarith
    rw [hq0] at this ⊢
    exact mul_right_cancel₀ hq1.ne' (by linarith)
  · have := foc_mc hopt huc hum (Nat.pos_iff_ne_zero.mp ht) (s := 0)
    rw [hq0] at this
    simpa using this

/-- Cochrane (2023), footnote 1, p. 440 (concave utility; restated from the Cochrane
IntertemporalModel project): for `g` concave on `ℝ` with derivative `d` at `x`, the tangent
line lies above the graph. -/
theorem concave_le_tangent {g : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ g) {x d : ℝ}
    (hg : HasDerivAt g d x) (y : ℝ) : g y ≤ g x + d * (y - x) := by
  rcases lt_trichotomy y x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst h
    simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h hg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Cochrane (2023), footnote 1, p. 440 (concave utility): if `u(c, m)` is jointly concave and
differentiable at `(c₀, m₀)` with partial derivatives `u_c`, `u_m`, then
`u(c, m) ≤ u(c₀, m₀) + u_c(c − c₀) + u_m(m − m₀)`. -/
theorem supergradient_of_concave {u : ℝ → ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {c0 m0 : ℝ}
    (hconc : ConcaveOn ℝ Set.univ (fun z : ℝ × ℝ => u z.1 z.2))
    (hd : HasFDerivAt (fun z : ℝ × ℝ => u z.1 z.2) L (c0, m0)) (c m : ℝ) :
    u c m ≤ u c0 m0 + L (1, 0) * (c - c0) + L (0, 1) * (m - m0) := by
  set g : ℝ → ℝ := fun τ => u (c0 + τ * (c - c0)) (m0 + τ * (m - m0)) with hgdef
  have hgc : ConcaveOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := hconc.2 (Set.mem_univ (c0 + x * (c - c0), m0 + x * (m - m0)))
      (Set.mem_univ (c0 + y * (c - c0), m0 + y * (m - m0))) ha hb hab
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
    simp only [hgdef, smul_eq_mul]
    convert this using 2
    · linear_combination (-c0) * hab
    · linear_combination (-m0) * hab
  have hpath : HasDerivAt (fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0)))
      (c - c0, m - m0) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => c0 + τ * (c - c0)) (c - c0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (c - c0)).const_add c0
    have h2 : HasDerivAt (fun τ : ℝ => m0 + τ * (m - m0)) (m - m0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (m - m0)).const_add m0
    exact h1.prodMk h2
  have hd' : HasFDerivAt (fun z : ℝ × ℝ => u z.1 z.2) L
      ((fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0))) 0) := by simpa using hd
  have hg0 : HasDerivAt ((fun z : ℝ × ℝ => u z.1 z.2) ∘
      fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0))) (L (c - c0, m - m0)) 0 :=
    hd'.comp_hasDerivAt (0 : ℝ) hpath
  have hg : HasDerivAt g (L (c - c0, m - m0)) 0 := hg0
  have h := concave_le_tangent hgc hg 1
  have hlin : L (c - c0, m - m0) = L (1, 0) * (c - c0) + L (0, 1) * (m - m0) := by
    have e : ((c - c0, m - m0) : ℝ × ℝ) = (c - c0) • ((1 : ℝ), (0 : ℝ)) +
        (m - m0) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  simp only [hgdef, one_mul, zero_mul, add_zero, add_sub_cancel] at h
  rw [hlin] at h
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440 (sufficiency): if utility is
concave in the sense of the supergradient inequality at the plan (`supergradient_of_concave`),
`β ≥ 0`, the first-order conditions `βᵗu_c = λq_t`, `βᵗu_m = λq_tι_t` hold with `λ ≥ 0`, and the
budget binds, then the plan is optimal. -/
theorem optimal_of_foc {β W lam : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam)
    (hsup : ∀ k c' m', u c' m' ≤ u (c k) (m k) + uc (c k) (m k) * (c' - c k) +
      um (c k) (m k) * (m' - m k))
    (hfoc : ∀ k, β ^ k * uc (c k) (m k) = lam * q k ∧
      β ^ k * um (c k) (m k) = lam * q k * ι k)
    (hfeas : Feasible q ι W c m) (hbind : ∑' t, q t * (c t + ι t * m t) = W)
    (hus : Summable (fun t => β ^ t * u (c t) (m t))) : Optimal β u q ι W c m := by
  refine ⟨hfeas, hus, fun c' m' hf' hu' => ?_⟩
  have hpt : ∀ k, β ^ k * u (c' k) (m' k) ≤ β ^ k * u (c k) (m k) +
      lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)) := by
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hsup k (c' k) (m' k)) (pow_nonneg hβ k)
    have h2 := hfoc k
    have e : β ^ k * (u (c k) (m k) + uc (c k) (m k) * (c' k - c k) +
        um (c k) (m k) * (m' k - m k)) = β ^ k * u (c k) (m k) +
        lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)) := by
      linear_combination (c' k - c k) * h2.1 + (m' k - m k) * h2.2
    linarith
  have hR : HasSum (fun k => β ^ k * u (c k) (m k) +
      lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)))
      (∑' k, β ^ k * u (c k) (m k) + lam * (∑' k, q k * (c' k + ι k * m' k) -
        ∑' k, q k * (c k + ι k * m k))) :=
    hus.hasSum.add ((hf'.1.hasSum.sub hfeas.1.hasSum).mul_left lam)
  have hle := hasSum_le hpt hu'.hasSum hR
  have : lam * (∑' k, q k * (c' k + ι k * m' k) - ∑' k, q k * (c k + ι k * m k)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hf'.2])
  linarith

/-! ### (19.15)–(19.16): bond prices, money demand and the value of money -/

/-- Cochrane (2023), p. 441: from (19.15) `1/(1 + i_t) = E_t[βu_c(t+1)P_t/(u_c(t)P_{t+1})]` and
(19.16) `u_m/u_c = i/(1 + i)`, `1 = u_m(t)/u_c(t) + E_t[βu_c(t+1)P_t/(u_c(t)P_{t+1})]`. -/
theorem convenience_identity {ratio i EQ : ℝ} (hi : 1 + i ≠ 0) (h1915 : EQ = 1 / (1 + i))
    (h1916 : ratio = i / (1 + i)) : 1 = ratio + EQ := by
  rw [h1915, h1916]
  field_simp
  ring

/-- Cochrane (2023), (19.15)–(19.16), p. 441: the value of a dollar `v_t = u_c(t)/P_t` satisfies
`v_t = u_m(t)/P_t + βE_tv_{t+1}`. -/
theorem value_recursion (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) :
    Solves 𝔼 β (fun t => um t / P t) (fun t => uc t / P t) := by
  intro t
  have e : β • (uc (t + 1) / uc t * (P t / P (t + 1))) = (P t / uc t) * (β • (uc (t + 1) /
      P (t + 1))) := by
    funext ω
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul]
    ring
  have h := h1915 t
  rw [e, hPO t _ _ (hk t), map_smul] at h
  funext ω
  have hω := congrFun h ω
  have h16 := h1916 t ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
    Pi.add_apply] at hω ⊢
  set X := 𝔼.E t (uc (t + 1) / P (t + 1)) ω with hXdef
  have h1 := huc t ω
  have h2 := hP t ω
  have h3 := hi t ω
  have hX : β * X = uc t ω / P t ω / (1 + i t ω) := by
    field_simp at hω ⊢
    linarith
  have hum : um t ω = uc t ω * (i t ω / (1 + i t ω)) := by
    field_simp at h16 ⊢
    linarith
  rw [hX, hum]
  field_simp

/-- Cochrane (2023), p. 441 ("Iterating, we can state an asset-pricing view of the value of
money"): `u_c(t)/P_t = E_t∑_{j≤T}βʲu_m(t+j)/P_{t+j} + β^{T+1}E_t[u_c(t+T+1)/P_{t+T+1}]`. -/
theorem value_of_money_iterated (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted (fun t => uc t / P t))
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t T : ℕ) :
    uc t / P t = ∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (um (t + j) / P (t + j)) +
      β ^ (T + 1) • 𝔼.E t (uc (t + T + 1) / P (t + T + 1)) := by
  have hs := value_recursion 𝔼 hPO hk huc hP hi h1915 h1916
  have hwa : 𝔼.Adapted (fun t => um t / P t) := fun k => by
    have hsk := hs k
    simp only at hsk
    have e : um k / P k = uc k / P k - β • 𝔼.E k (uc (k + 1) / P (k + 1)) := by
      rw [hsk]; abel
    change 𝔼.E k (um k / P k) = um k / P k
    have hvk := hv k
    simp only at hvk
    rw [e, map_sub, map_smul, 𝔼.E_E_self, hvk]
  rw [iterate_A15 𝔼 hwa hs t (T + 1), add_comm, ← add_assoc]

/-- Cochrane (2023), p. 441 ("An additional dollar, held forever, costs `1/P_t`. It generates a
stream of benefits"): if `βᵀE_t[u_c(t+T)/P_{t+T}] → 0`, the value of a dollar is the present value
of its liquidity dividends, `u_c(t)/P_t = lim ∑_{j<T}βʲE_t[u_m(t+j)/P_{t+j}]`. -/
theorem value_of_money_limit (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted (fun t => uc t / P t))
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T => β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω) atTop
      (𝓝 (uc t ω / P t ω)) := by
  have hs := value_recursion 𝔼 hPO hk huc hP hi h1915 h1916
  have hwa : 𝔼.Adapted (fun t => um t / P t) := fun k => by
    have hsk := hs k
    simp only at hsk
    have e : um k / P k = uc k / P k - β • 𝔼.E k (uc (k + 1) / P (k + 1)) := by
      rw [hsk]; abel
    change 𝔼.E k (um k / P k) = um k / P k
    have hvk := hv k
    simp only at hvk
    rw [e, map_sub, map_smul, 𝔼.E_E_self, hvk]
  have hid : ∀ T, ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω =
      uc t ω / P t ω - β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω := by
    intro T
    have h := congrFun (iterate_A15 𝔼 hwa hs t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.div_apply] at h
    linarith
  have h2 := (tendsto_const_nhds (x := uc t ω / P t ω)).sub htvc
  rw [sub_zero] at h2
  exact h2.congr fun T => (hid T).symm

/-- Cochrane (2023), (19.16), p. 441 (money demand `M_t = P_tL(y_t, i_t)`; restated from the
Woodford Chapter 2 project): if `u_m/u_c` is strictly decreasing in real balances, the
money-demand equation `u_m/u_c(y, m) = i/(1 + i)` has at most one positive solution. -/
theorem lm_unique {R : ℝ → ℝ} (hanti : StrictAntiOn R (Set.Ioi 0)) {Δ m₁ m₂ : ℝ}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (e₁ : R m₁ = Δ) (e₂ : R m₂ = Δ) : m₁ = m₂ :=
  hanti.injOn h₁ h₂ (e₁.trans e₂.symm)

/-- Cochrane (2023), (19.16), p. 441 (restated from the Woodford Chapter 2 project): if
`u_m/u_c` is continuous, unbounded as real balances vanish and tends to `0` for large balances,
money demand `u_m/u_c(y, m) = Δ` has a positive solution for every `Δ > 0`. -/
theorem lm_exists {R : ℝ → ℝ} (hcont : ContinuousOn R (Set.Ioi 0))
    (h0 : Tendsto R (𝓝[>] 0) atTop) (hinf : Tendsto R atTop (𝓝 0)) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ m, 0 < m ∧ R m = Δ := by
  have e₁ : ∀ᶠ m in 𝓝[>] (0 : ℝ), Δ < R m ∧ m ∈ Set.Ioi 0 :=
    (h0.eventually (eventually_gt_atTop Δ)).and self_mem_nhdsWithin
  have e₂ : ∀ᶠ m in atTop, R m < Δ ∧ 0 < m :=
    (hinf.eventually (gt_mem_nhds hΔ)).and (eventually_gt_atTop 0)
  obtain ⟨m₁, hR₁, hm₁⟩ := e₁.exists
  obtain ⟨m₂, hR₂, hm₂⟩ := e₂.exists
  have hsub : Set.uIcc m₁ m₂ ⊆ Set.Ioi 0 := fun x hx => by
    rcases Set.mem_uIcc.mp hx with h | h
    · exact lt_of_lt_of_le (Set.mem_Ioi.mp hm₁) h.1
    · exact lt_of_lt_of_le hm₂ h.1
  have hmem : Δ ∈ Set.uIcc (R m₁) (R m₂) := Set.mem_uIcc.mpr (Or.inr ⟨hR₂.le, hR₁.le⟩)
  obtain ⟨m, hm, hRm⟩ := intermediate_value_uIcc (hcont.mono hsub) hmem
  exact ⟨m, hsub hm, hRm⟩

/-! ### (19.17)–(19.19): separable utility, perfect foresight -/

/-- Cochrane (2023), eq. (19.18), p. 442: with real balances `m = M/P`,
`P_t/P_{t+1} = (m_{t+1}/m_t)(M_t/M_{t+1})`. -/
theorem price_ratio_eq {M M' P P' : ℝ} (hM : M ≠ 0) (hM' : M' ≠ 0) (hP : P ≠ 0)
    (hP' : P' ≠ 0) : P / P' = (M' / P') / (M / P) * (M / M') := by
  field_simp

/-- Cochrane (2023), eqs. (19.17)–(19.18), p. 442: with separable utility, constant consumption
`c = y` and perfect foresight, `1/(1 + i_t) = βP_t/P_{t+1}`, so (19.17)
`u_m(m_t)/u_c(y) = 1 − 1/(1 + i_t)` is the difference equation (19.18)
`u_m(m_t)/u_c(y) = 1 − β(m_{t+1}/m_t)(M_t/M_{t+1})`. -/
theorem eq1918_iff {β ucy umt i M M' P P' : ℝ} (hM : M ≠ 0) (hM' : M' ≠ 0) (hP : P ≠ 0)
    (hP' : P' ≠ 0) (h1915 : 1 / (1 + i) = β * (P / P')) :
    umt / ucy = 1 - 1 / (1 + i) ↔
      umt / ucy = 1 - β * ((M' / P') / (M / P)) * (M / M') := by
  rw [h1915, price_ratio_eq hM hM' hP hP', mul_assoc]

/-- Cochrane (2023), eq. (19.18), p. 442: a perfect-foresight path of positive real balances
`m_t = M_t/P_t` for separable utility, given the money path `M` and `u_c(y) = ucy`. -/
def IsMIUPath (β ucy : ℝ) (um : ℝ → ℝ) (M m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ um (m t) / ucy = 1 - β * (m (t + 1) / m t) * (M t / M (t + 1))

/-- Cochrane (2023), eq. (19.19), p. 442: with money growth `M_{t+1}/M_t = 1 + µ`, constant real
balances `m` form a path iff `u_m(m)/u_c(y) = 1 − β/(1 + µ)`. -/
theorem steady_state_path_iff {β ucy μg m : ℝ} {um : ℝ → ℝ} {M : ℕ → ℝ} (hm : 0 < m)
    (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = μg * M t) :
    IsMIUPath β ucy um M (fun _ => m) ↔ um m / ucy = 1 - β / μg := by
  have hμ : μg ≠ 0 := by
    intro h
    have := hg 0
    rw [h, zero_mul] at this
    exact (hM 1).ne' this
  constructor
  · intro h
    rw [(h 0).2, hg 0]
    field_simp [(hM 0).ne']
  · intro h t
    refine ⟨hm, ?_⟩
    rw [h, hg t]
    field_simp [(hM t).ne']

/-- Cochrane (2023), eq. (19.19), p. 442 ("prices are proportional to money over time, and
inflation equals the money growth rate"): with constant real balances `m = M_t/P_t`,
`P_{t+1}/P_t = M_{t+1}/M_t = 1 + µ`. -/
theorem steady_state_inflation {μg m Mt Pt Pt' : ℝ} (hm : 0 < m) (hMt : 0 < Mt)
    (h0 : m = Mt / Pt) (h1 : m = μg * Mt / Pt') : Pt' / Pt = μg := by
  have hμ : μg ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_div] at h1
    exact hm.ne' h1
  have hPt : Pt = Mt / m := by rw [h0]; field_simp [hMt.ne']
  have hPt' : Pt' = μg * Mt / m := by
    have hP' : Pt' ≠ 0 := by
      rintro rfl
      rw [div_zero] at h1
      exact hm.ne' h1
    rw [h1]
    field_simp
  rw [hPt, hPt']
  field_simp

/-- Cochrane (2023), eq. (19.19), p. 442: if `u_m` is continuous and strictly decreasing on
`(0, ∞)` and `u_m/u_c(y)` takes values on both sides of `1 − β/(1 + µ)`, the inflationary steady
state of real balances exists and is unique. -/
theorem steady_state_existsUnique {β ucy μg a b : ℝ} {um : ℝ → ℝ} (hucy : 0 < ucy)
    (hcont : ContinuousOn um (Set.Ioi 0)) (hanti : StrictAntiOn um (Set.Ioi 0)) (ha : 0 < a)
    (hab : a ≤ b) (hva : 1 - β / μg ≤ um a / ucy) (hvb : um b / ucy ≤ 1 - β / μg) :
    ∃! m, 0 < m ∧ um m / ucy = 1 - β / μg := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hc : ContinuousOn (fun z => um z / ucy) (Set.Icc a b) :=
    (hcont.mono hsub).div_const ucy
  obtain ⟨m, hm, hv⟩ := intermediate_value_Icc' hab hc ⟨hvb, hva⟩
  refine ⟨m, ⟨hsub hm, hv⟩, fun m' hm' => ?_⟩
  have e : um m' = um m := by
    have := hm'.2.trans hv.symm
    field_simp at this
    exact this
  exact hanti.injOn hm'.1 (hsub hm) e

/-- Cochrane (2023), p. 443 ("At zero nominal rates `i_t = 0`, we have `u_m = 0` … (19.18)
becomes `P_{t+1}/P_t = β`"): with `u_c > 0`, (19.16) and the bond price
`1/(1 + i) = βP_t/P_{t+1}`, `u_m = 0` iff `i = 0` iff `P_{t+1}/P_t = β`. -/
theorem zero_rate_iff {β ucy umt i P P' : ℝ} (hucy : 0 < ucy) (hi : 0 < 1 + i) (hP : 0 < P)
    (hP' : 0 < P') (h1916 : umt / ucy = i / (1 + i))
    (h1915 : 1 / (1 + i) = β * (P / P')) :
    (umt = 0 ↔ i = 0) ∧ (i = 0 ↔ P' / P = β) := by
  constructor
  · constructor
    · intro h
      rw [h, zero_div] at h1916
      rcases div_eq_zero_iff.mp h1916.symm with h | h
      · exact h
      · exact absurd h hi.ne'
    · intro h
      rw [h, zero_div, div_eq_zero_iff] at h1916
      exact h1916.resolve_right hucy.ne'
  · constructor
    · intro h
      rw [h, add_zero, div_one] at h1915
      field_simp at h1915 ⊢
      linarith
    · intro h
      have : β * (P / P') = 1 := by
        rw [← h]
        field_simp
      rw [this] at h1915
      have := (div_eq_one_iff_eq hi.ne').mp h1915
      linarith

/-- Cochrane (2023), p. 443 ("with `β = 1/(1 + δ)`, `π_{t+1} ≈ −δ`"): the deflation rate
`P_{t+1}/P_t − 1 = 1/(1 + δ) − 1` has derivative `−1` in `δ` at `δ = 0`, and equals
`−δ/(1 + δ)`. -/
theorem deflation_approx :
    HasDerivAt (fun δ : ℝ => 1 / (1 + δ) - 1) (-1) 0 ∧
      ∀ δ : ℝ, 1 + δ ≠ 0 → 1 / (1 + δ) - 1 = -δ / (1 + δ) := by
  refine ⟨?_, fun δ hδ => by field_simp; ring⟩
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.sub_const 1
  simpa [one_div] using h2

/-- Cochrane (2023), p. 443 ("we arrive at zero interest rates in finite time and stay there"):
with satiation `u_m(m) = 0` for `m ≥ m_sat` and money growth `1 + µ ≥ β`, once a path of (19.18)
reaches `m_sat` it stays above it, real balances grow at `(1 + µ)/β` and `u_m = 0` (`i = 0`)
at every later date. -/
theorem satiation_absorbing {β ucy μg msat : ℝ} {um : ℝ → ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hμβ : β ≤ μg) (hsat : ∀ x, msat ≤ x → um x = 0) (hM : ∀ t, 0 < M t)
    (hg : ∀ t, M (t + 1) = μg * M t) (hpath : IsMIUPath β ucy um M m) {t0 : ℕ}
    (ht0 : msat ≤ m t0) :
    ∀ n, msat ≤ m (t0 + n) ∧ um (m (t0 + n)) = 0 ∧
      m (t0 + n + 1) = μg / β * m (t0 + n) := by
  have hμ : 0 < μg := lt_of_lt_of_le hβ hμβ
  have step : ∀ k, msat ≤ m k → m (k + 1) = μg / β * m k ∧ msat ≤ m (k + 1) := by
    intro k hk
    have hp := hpath k
    rw [hsat _ hk, zero_div, hg k] at hp
    have hmk := hp.1
    have hMk := hM k
    have e : m (k + 1) = μg / β * m k := by
      have h2 : β * (m (k + 1) / m k) * (M k / (μg * M k)) = 1 := by linarith [hp.2]
      field_simp at h2
      field_simp
      linarith
    refine ⟨e, ?_⟩
    rw [e]
    have : 1 ≤ μg / β := (one_le_div hβ).mpr hμβ
    nlinarith
  intro n
  induction n with
  | zero => exact ⟨ht0, hsat _ ht0, (step t0 ht0).1⟩
  | succ n ih =>
    have h1 := (step (t0 + n) ih.1).2
    rw [show t0 + (n + 1) = t0 + n + 1 by ring]
    exact ⟨h1, hsat _ h1, (step _ h1).1⟩

/-- Cochrane (2023), p. 443 ("if `lim_{m→∞} u_m(m) = 0`, zero interest rates are a limiting
case, and the economy slowly drifts down to it"): along a path with `m_t → ∞` and (19.16),
`i_t → 0`. -/
theorem limit_rate_zero {ucy : ℝ} {um : ℝ → ℝ} {m i : ℕ → ℝ} (hum : Tendsto um atTop (𝓝 0))
    (hm : Tendsto m atTop atTop) (hi : ∀ t, 0 < 1 + i t)
    (h1916 : ∀ t, um (m t) / ucy = i t / (1 + i t)) : Tendsto i atTop (𝓝 0) := by
  set ι := fun t => um (m t) / ucy with hι
  have hιlim : Tendsto ι atTop (𝓝 0) := by
    have := (hum.comp hm).div_const ucy
    simpa [hι] using this
  have hfor : ∀ t, i t = ι t / (1 - ι t) := by
    intro t
    have h := h1916 t
    have h1 := hi t
    simp only [hι]
    rw [h]
    field_simp
    ring
  have hlim : Tendsto (fun t => ι t / (1 - ι t)) atTop (𝓝 (0 / (1 - 0))) :=
    hιlim.div (tendsto_const_nhds.sub hιlim) (by norm_num)
  rw [zero_div] at hlim
  exact hlim.congr fun t => (hfor t).symm

/-- Cochrane (2023), p. 443 ("The money demand curve becomes a correspondence `m ≥ m_sat`,
`i = 0`"): with satiation, at `i = 0` every `m ≥ m_sat` satisfies (19.16). -/
theorem money_demand_correspondence {ucy msat : ℝ} {um : ℝ → ℝ}
    (hsat : ∀ x, msat ≤ x → um x = 0) {m : ℝ} (hm : msat ≤ m) :
    um m / ucy = (0 : ℝ) / (1 + 0) := by
  rw [hsat m hm]
  simp

/-! ### (19.20)–(19.23): power utility -/

/-- Cochrane (2023), eq. (19.20), p. 443: for `γ ≠ 1` and `x > 0`, `x^{1−γ}/(1 − γ)` has
derivative `x^{−γ}`; hence `u_c = c^{−γ}` and `u_m = θm^{−γ}`. -/
theorem hasDerivAt_power {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => z ^ (1 - γ) / (1 - γ)) (x ^ (-γ)) x := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')).div_const (1 - γ)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  convert h using 1
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- Cochrane (2023), (19.20), p. 443: with power utility, `u_m/u_c = θm^{−γ}/y^{−γ} = θ(m/y)^{−γ}`
equals `θ(y/m)^γ = θ(Py/M)^γ`. -/
theorem power_um_ratio {θ γ m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    θ * m ^ (-γ) / y ^ (-γ) = θ * (y / m) ^ γ := by
  rw [mul_div_assoc, ← Real.div_rpow hm.le hy.le, Real.rpow_neg (by positivity),
    ← Real.inv_rpow (by positivity), inv_div]

/-- Cochrane (2023), (19.16) with (19.20), p. 443, and Online Appendix (3.4), p. 620 (the
inverse power money demand, a general lemma; formerly `PruningInflation.power_demand_iff`): for
`k, m > 0` and `γ ≠ 0`, `θm^{−γ} = k` iff `m = (k/θ)^{−1/γ}`. -/
theorem power_demand_iff {θ γ k m : ℝ} (hθ : 0 < θ) (hγ : γ ≠ 0) (hk : 0 < k) (hm : 0 < m) :
    θ * m ^ (-γ) = k ↔ m = (k / θ) ^ (-(1 / γ)) := by
  have hneg : -(1 / γ) = (-γ)⁻¹ := by field_simp
  constructor
  · intro h
    have h1 : m ^ (-γ) = k / θ := by rw [← h]; field_simp
    rw [hneg, ← h1, Real.rpow_rpow_inv hm.le (neg_ne_zero.mpr hγ)]
  · intro h
    rw [h, hneg, Real.rpow_inv_rpow (by positivity) (neg_ne_zero.mpr hγ)]
    field_simp

/-- Cochrane (2023), p. 443 ("Money demand is `M_t = P_ty_t(i_t/(θ(1 + i_t)))^{−1/γ}`"): for
`θ, γ, ι > 0`, `θ(m/y)^{−γ} = ι` iff `m = y(ι/θ)^{−1/γ}` (with `ι = i/(1 + i)`, `m = M/P`). -/
theorem power_money_demand {θ γ y m ι : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hy : 0 < y)
    (hm : 0 < m) (hι : 0 < ι) : θ * (m / y) ^ (-γ) = ι ↔ m = y * (ι / θ) ^ (-1 / γ) := by
  rw [power_demand_iff hθ hγ.ne' hι (div_pos hm hy), div_eq_iff hy.ne', neg_div]
  constructor <;> intro h <;> rw [h] <;> ring

/-- Cochrane (2023), eq. (19.21), p. 444, in terms of `x_t = P_ty/M_t` with money growth
`M_{t+1}/M_t = 1 + µ` (`μg = 1 + µ`): `θx_t^γ = 1 − β(x_t/x_{t+1})/(1 + µ)` (since
`m_{t+1}/m_t = x_t/x_{t+1}`). -/
def IsPowerPath (β θ γ μg : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ t, 0 < x t ∧ θ * x t ^ γ = 1 - β * (x t / x (t + 1)) / μg

/-- Cochrane (2023), eq. (19.22), p. 444: with `β = 1/(1 + δ)` the inflationary steady state of
(19.21) satisfies `θ(Py/M)^γ = 1 − 1/((1 + δ)(1 + µ))`. -/
theorem eq1922 {θ γ δ μ xb : ℝ} (hδ : 1 + δ ≠ 0) (hμ : 1 + μ ≠ 0) (hxb : 0 < xb) :
    IsPowerPath (1 / (1 + δ)) θ γ (1 + μ) (fun _ => xb) ↔
      θ * xb ^ γ = 1 - 1 / ((1 + δ) * (1 + μ)) := by
  constructor
  · intro h
    rw [(h 0).2]
    field_simp
  · intro h t
    refine ⟨hxb, ?_⟩
    rw [h]
    field_simp

/-- Cochrane (2023), (19.22), p. 444: exactly,
`1 − 1/((1 + δ)(1 + µ)) = (δ + µ + δµ)/((1 + δ)(1 + µ))`. -/
theorem eq1922_exact {δ μ : ℝ} (hδ : 1 + δ ≠ 0) (hμ : 1 + μ ≠ 0) :
    1 - 1 / ((1 + δ) * (1 + μ)) = (δ + μ + δ * μ) / ((1 + δ) * (1 + μ)) := by
  field_simp
  ring

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"): the derivative in `δ` at `δ = µ = 0` is `1`. -/
theorem eq1922_partial_delta :
    HasDerivAt (fun δ : ℝ => 1 - 1 / ((1 + δ) * (1 + 0))) 1 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.const_sub 1
  simpa [one_div] using h2

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"): the derivative in `µ` at `δ = µ = 0` is `1`. -/
theorem eq1922_partial_mu :
    HasDerivAt (fun μ : ℝ => 1 - 1 / ((1 + 0) * (1 + μ))) 1 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.const_sub 1
  simpa [one_div] using h2

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"), quantitatively: for `δ, µ ≥ 0` with
`δ + µ ≤ 1`, `0 ≤ (δ + µ) − [1 − 1/((1 + δ)(1 + µ))] ≤ (δ + µ)²`. -/
theorem eq1922_approx {δ μ : ℝ} (hδ : 0 ≤ δ) (hμ : 0 ≤ μ) (h1 : δ + μ ≤ 1) :
    0 ≤ (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) ∧
      (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) ≤ (δ + μ) ^ 2 := by
  have hD : 0 < (1 + δ) * (1 + μ) := by positivity
  have e : (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) =
      ((δ + μ) * (δ + μ + δ * μ) - δ * μ) / ((1 + δ) * (1 + μ)) := by
    field_simp
    ring
  rw [e]
  have hdm : 0 ≤ δ * μ := mul_nonneg hδ hμ
  constructor
  · apply div_nonneg _ hD.le
    nlinarith [sq_nonneg (δ - μ)]
  · rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_right h1 hdm, sq_nonneg (δ + μ),
      mul_nonneg (sq_nonneg (δ + μ)) (add_nonneg (add_nonneg hδ hμ) hdm)]

/-- Cochrane (2023), p. 444 ("for `Py/M ≈ 1`, we need `θ ≈ δ + µ`"): at `x̄ = 1`, `θ` equals the
right-hand side of (19.22). -/
theorem calib_unit {θ γ f : ℝ} (h : θ * (1 : ℝ) ^ γ = f) : θ = f := by
  rwa [Real.one_rpow, mul_one] at h

/-- Cochrane (2023), p. 444 ("For a more realistic `Py/M ≈ 10`"): at `x̄ = 10`,
`θ = f·10^{−γ}`. -/
theorem calib_ten {θ γ f : ℝ} (h : θ * (10 : ℝ) ^ γ = f) : θ = f * (10 : ℝ) ^ (-γ) := by
  rw [← h, Real.rpow_neg (by norm_num), mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-- Cochrane (2023), p. 444 ("we need `θ` on the order of 0.01"): with `δ + µ ≈ 0.1` this holds
for `γ = 1`: `θ = 0.1/10 = 0.01`. -/
theorem calib_ten_gamma_one {θ : ℝ} (h : θ * (10 : ℝ) ^ (1 : ℝ) = 1 / 10) : θ = 1 / 100 := by
  rw [Real.rpow_one] at h
  linarith

/-- Cochrane (2023), p. 444, imprecision: with the figure's `γ = 2` and `δ + µ ≈ 0.1`,
`Py/M = 10` requires `θ = 0.001`, not `0.01`. -/
theorem calib_ten_gamma_two {θ : ℝ} (h : θ * (10 : ℝ) ^ (2 : ℝ) = 1 / 10) : θ = 1 / 1000 := by
  rw [Real.rpow_two] at h
  linarith

/-- Cochrane (2023), p. 444 ("If we hold one tenth of a year's income as money, even a 5%
nominal interest rate generates interests costs … equal to one two hundredth of a year's
income"). -/
theorem calib_interest_cost (y : ℝ) : (5 / 100) * (y / 10) = y / 200 := by ring

/-- Cochrane (2023), eq. (19.23), p. 444: the map
`x ↦ x(1 − θx̄^γ)/(1 − θx^γ)`, `x = P_ty/M_t`. -/
noncomputable def nextX (θ γ xb x : ℝ) : ℝ := x * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ)

/-- Cochrane (2023), eq. (19.23), p. 444: given the steady state `θx̄^γ = 1 − β/(1 + µ)`, for
positive `x_t`, `x_{t+1}` the date-`t` equation of (19.21) holds iff `x_{t+1} = nextX x_t`
(positivity of `x_{t+1}` forces `1 − θx_t^γ ≠ 0`). -/
theorem eq1923_iff {β θ γ μg xb x x' : ℝ} (hβ : 0 < β) (hμ : 0 < μg) (hx : 0 < x)
    (hx' : 0 < x') (hxb : θ * xb ^ γ = 1 - β / μg) :
    θ * x ^ γ = 1 - β * (x / x') / μg ↔ x' = nextX θ γ xb x := by
  unfold nextX
  rw [hxb]
  constructor
  · intro h
    have h1 : 1 - θ * x ^ γ = β * x / (μg * x') := by rw [h]; field_simp; ring
    rw [h1]
    field_simp
    ring
  · intro h
    have := hβ.ne'
    rw [h]
    field_simp
    have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ this
    linear_combination (1 - θ * x ^ γ) * hb

/-- Cochrane (2023), p. 444 (`P_{t+1}/P_t = (1 + µ)(1 − θ(Py/M)^γ)/(1 − θ(P_ty/M_t)^γ)`): along
(19.23), `(x_{t+1}/x_t)(1 + µ) = (1 + µ)(1 − θx̄^γ)/(1 − θx_t^γ)`. -/
theorem inflation_eq1923 {θ γ μg xb x : ℝ} (hx : 0 < x) :
    nextX θ γ xb x / x * μg = μg * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ) := by
  unfold nextX
  field_simp

/-! ### Figure 19.1 -/

/-- Cochrane (2023), Figure 19.1, p. 444: `x̄ = √(275/9)`, the steady state for
`δ = µ = 0.2`, `γ = 2`, `θ = 0.01`. -/
noncomputable def xbar191 : ℝ := Real.sqrt (275 / 9)

/-- Cochrane (2023), Figure 19.1, p. 444: `x̄` solves (19.22) with `δ = µ = 0.2`, `γ = 2`,
`θ = 0.01`, and `θx̄^γ = 11/36`. -/
theorem fig191_steady :
    (1 / 100 : ℝ) * xbar191 ^ (2 : ℝ) = 1 - 1 / ((1 + 1 / 5) * (1 + 1 / 5)) ∧
      (1 / 100 : ℝ) * xbar191 ^ (2 : ℝ) = 11 / 36 := by
  rw [Real.rpow_two, xbar191, Real.sq_sqrt (by norm_num)]
  constructor <;> norm_num

/-- Cochrane (2023), Figure 19.1, p. 444: `5.52 < x̄ < 5.53`. -/
theorem fig191_xbar_bounds : (552 / 100 : ℝ) < xbar191 ∧ xbar191 < 553 / 100 := by
  unfold xbar191
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- Cochrane (2023), p. 444 ("the derivative of (19.23) is positive at `Py/M`"): for `x̄ > 0`
with `1 − θx̄^γ ≠ 0`, the slope of (19.23) at `x̄` is `1 + γθx̄^γ/(1 − θx̄^γ)`. -/
theorem nextX_hasDerivAt {θ γ xb : ℝ} (hxb : 0 < xb) (hK : 1 - θ * xb ^ γ ≠ 0) :
    HasDerivAt (nextX θ γ xb) (1 + γ * θ * xb ^ γ / (1 - θ * xb ^ γ)) xb := by
  set K := 1 - θ * xb ^ γ with hKdef
  have hnum : HasDerivAt (fun x => x * K) K xb := by
    simpa using (hasDerivAt_id xb).mul_const K
  have hden : HasDerivAt (fun x => 1 - θ * x ^ γ) (-(θ * (γ * xb ^ (γ - 1)))) xb := by
    simpa using ((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hxb.ne')).const_mul θ).const_sub 1
  have h := hnum.div hden hK
  have e : ((fun x => x * K) / fun x => 1 - θ * x ^ γ) = nextX θ γ xb := by
    funext x
    simp only [Pi.div_apply, nextX, hKdef]
  rw [e] at h
  convert h using 1
  rw [Real.rpow_sub_one hxb.ne', ← hKdef]
  field_simp
  ring

/-- Cochrane (2023), p. 444 ("The phase diagram cuts from below at the steady state … so
dynamics are unstable"): with `θ > 0`, `x̄ > 0` and `0 < 1 − θx̄^γ`, the slope exceeds one
for `γ > 0`. -/
theorem slope_gt_one {θ γ xb : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hK : 0 < 1 - θ * xb ^ γ) : 1 < 1 + γ * θ * xb ^ γ / (1 - θ * xb ^ γ) := by
  have : 0 < γ * θ * xb ^ γ / (1 - θ * xb ^ γ) := by
    have := Real.rpow_pos_of_pos hxb γ
    positivity
  linarith

/-- Cochrane (2023), Figure 19.1, p. 444 (survey: slope `1.88 > 1`): with the figure's numbers
the slope of (19.23) at `x̄` is exactly `47/25 = 1.88`. -/
theorem fig191_slope :
    HasDerivAt (nextX (1 / 100) 2 xbar191) (47 / 25) xbar191 := by
  have hpos : 0 < xbar191 := Real.sqrt_pos.mpr (by norm_num)
  have hs := fig191_steady.2
  have h := nextX_hasDerivAt (θ := 1 / 100) (γ := 2) hpos (by rw [hs]; norm_num)
  convert h using 1
  rw [mul_assoc, hs]
  norm_num

/-- Cochrane (2023), Figure 19.1, p. 444: the map (19.23) has its pole where `θx^γ = 1`; for
`θ = 0.01`, `γ = 2` at `x = 10`, and this is the only positive pole. -/
theorem fig191_pole : (1 / 100 : ℝ) * (10 : ℝ) ^ (2 : ℝ) = 1 ∧
    ∀ x : ℝ, 0 < x → (1 / 100 : ℝ) * x ^ (2 : ℝ) = 1 → x = 10 := by
  refine ⟨by rw [Real.rpow_two]; norm_num, fun x hx h => ?_⟩
  rw [Real.rpow_two] at h
  nlinarith

/-- Cochrane (2023), p. 444 ("in the limit `P_t/M_t → 0` … `lim P_{t+1}/P_t = 1/(1 + δ)`"): for
`γ > 0`, as `x → 0⁺` the gross inflation rate `(1 + µ)(1 − θx̄^γ)/(1 − θx^γ)` of (19.23) tends to
`(1 + µ)(1 − θx̄^γ)`, which equals `β = 1/(1 + δ)` at the steady state (19.22). -/
theorem deflation_limit {θ γ μg β xb : ℝ} (hγ : 0 < γ) (hxb : θ * xb ^ γ = 1 - β / μg)
    (hμ : μg ≠ 0) :
    Tendsto (fun x => μg * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ)) (𝓝[>] 0) (𝓝 β) := by
  have hc : ContinuousAt (fun x : ℝ => x ^ γ) 0 :=
    Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
  have h0 : (0 : ℝ) ^ γ = 0 := Real.zero_rpow hγ.ne'
  have hden : Tendsto (fun x : ℝ => 1 - θ * x ^ γ) (𝓝[>] 0) (𝓝 (1 - θ * 0)) := by
    have := (hc.tendsto.const_mul θ).const_sub 1
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_const_nhds (x := μg * (1 - θ * xb ^ γ))).div hden (by norm_num)
  have e : μg * (1 - θ * xb ^ γ) / (1 - θ * 0) = β := by
    rw [hxb, mul_zero, sub_zero, div_one]
    field_simp
    ring
  rw [e] at hlim
  exact hlim

/-- Cochrane (2023), pp. 444–445, survey error E13 (corrected): for `θ, γ > 0`, `β > 0`,
`1 + µ > 0`, the inflationary steady state `x̄ > 0` exists (`θx̄^γ = 1 − β/(1 + µ)`) iff
`1 + µ > β`, and then the ratio `x_{t+1}/x_t` near `x = 0` tends to `β/(1 + µ) < 1`, so the
deflationary steady state attracts; the condition is `1 + µ > β` (`µ > −δ/(1 + δ) ≈ −δ`),
not the printed `1 + µ > 1/β`. -/
theorem e13_corrected {θ γ β μg : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hμ : 0 < μg) :
    ((∃ xb, 0 < xb ∧ θ * xb ^ γ = 1 - β / μg) ↔ β < μg) ∧ (β / μg < 1 ↔ β < μg) := by
  refine ⟨⟨fun ⟨xb, hxb, h⟩ => ?_, fun h => ?_⟩, div_lt_one hμ⟩
  · have : 0 < θ * xb ^ γ := mul_pos hθ (Real.rpow_pos_of_pos hxb γ)
    have h2 : β / μg < 1 := by linarith
    exact (div_lt_one hμ).mp h2
  · have hpos : 0 < (1 - β / μg) / θ := by
      have : β / μg < 1 := (div_lt_one hμ).mpr h
      exact div_pos (by linarith) hθ
    refine ⟨((1 - β / μg) / θ) ^ γ⁻¹, Real.rpow_pos_of_pos hpos _, ?_⟩
    rw [Real.rpow_inv_rpow hpos.le hγ.ne']
    field_simp

/-- Cochrane (2023), p. 445, survey error E13: the printed condition `1 + µ > 1/β` is not
necessary: with `β = 5/6` (`δ = 0.2`) and zero money growth (`1 + µ = 1`) the corrected
condition `1 + µ > β` holds but the printed one fails. -/
theorem e13_printed_fails : (5 / 6 : ℝ) < 1 ∧ ¬ ((1 : ℝ) / (5 / 6) < 1) := by
  constructor <;> norm_num

/-- Cochrane (2023), p. 445 ("If we add back the government debt valuation equation … we obtain
a determinate price level"): with `B_{−1} + M_{−1} = D > 0` and real present value `S > 0`, the
valuation equation pins `P_0 = D/S`, hence `x_0 = P_0y/M_0`, and (19.23) then determines the
whole path: any two paths with the same valuation coincide. -/
theorem fiscal_determines_path {g : ℝ → ℝ} {D S y M0 : ℝ} (hS : 0 < S) {P0 P0' : ℝ}
    {x x' : ℕ → ℝ} (hv : D = P0 * S) (hv' : D = P0' * S) (hx0 : x 0 = P0 * y / M0)
    (hx0' : x' 0 = P0' * y / M0) (hx : ∀ t, x (t + 1) = g (x t))
    (hx' : ∀ t, x' (t + 1) = g (x' t)) : P0 = P0' ∧ x = x' := by
  have hP : P0 = P0' := mul_right_cancel₀ hS.ne' (hv.symm.trans hv')
  refine ⟨hP, funext fun t => ?_⟩
  induction t with
  | zero => rw [hx0, hx0', hP]
  | succ t ih => rw [hx t, hx' t, ih]

/-! ### Knownness of `Λ_t/P_t` and `P_t/u_c(t)` from adaptedness -/

/-- Cochrane (2023), §19.3, p. 441 (what "known at date `t`" allows): with the pull-out property,
the variables known at `t` are closed under products. -/
theorem known_mul (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hPO t a b ha, hb]

/-- Cochrane (2023), §19.3, p. 441, and §19.5.1, p. 449 (measurability bookkeeping): with the
pull-out property, the reciprocal of a nowhere-zero random variable known at `t` is known at `t`
(on any state space: `a·E_t(a⁻¹) = E_t(a·a⁻¹) = 1`). -/
theorem known_inv (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (ha0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp [ha0 ω]
  have h := hPO t a a⁻¹ ha
  rw [h1, 𝔼.const] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply, Pi.inv_apply] at hω ⊢
  have := ha0 ω
  field_simp
  linear_combination -hω

/-- Cochrane (2023), §19.3, p. 441 (`Λ_t/P_t` and `P_t/u_c(t)`), and §19.5.1, p. 449: a quotient
of random variables known at `t` with nowhere-zero denominator is known at `t`, on any state
space. -/
theorem known_div (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (hb0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv, known_mul 𝔼 hPO ha (known_inv 𝔼 hPO hb hb0)]

/-- Cochrane (2023), §19.3, p. 441: with the pull-out property, finite products of variables
known at `t` are known at `t`. -/
theorem known_prod (hPO : 𝔼.PullOut) {t : ℕ} {κ : Type*} (S : Finset κ) {g : κ → Ω → ℝ}
    (hg : ∀ k ∈ S, 𝔼.E t (g k) = g k) : 𝔼.E t (∏ k ∈ S, g k) = ∏ k ∈ S, g k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact 𝔼.const t 1
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, hPO t _ _ (hg k (Finset.mem_insert_self k S)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

/-- Cochrane (2023), §19.3, p. 441: on a finite state space with the pull-out property, every
function `f(a)` of a variable `a` known at `t` is known at `t` (Lagrange interpolation: `f(a)` is
a polynomial in `a`, and known variables form a unital subalgebra by `known_mul`). This covers
perfect foresight and every finite event tree. (Quotients with nonvanishing denominators are
known on any state space, `known_div`: the pull-out property gives more than the subalgebra
structure.) -/
theorem functionsKnown_of_fintype [Finite Ω] (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ}
    (ha : 𝔼.E t a = a) (f : ℝ → ℝ) :
    𝔼.E t (fun ω => f (a ω)) = fun ω => f (a ω) := by
  classical
  have := Fintype.ofFinite Ω
  set S : Finset ℝ := Finset.univ.image a with hS
  have hfac : ∀ v w : ℝ, 𝔼.E t ((1 / (v - w)) • a - fun _ => w / (v - w)) =
      (1 / (v - w)) • a - fun _ => w / (v - w) := fun v w => by
    rw [map_sub, map_smul, ha, 𝔼.const]
  have key : (fun ω => f (a ω)) = ∑ v ∈ S, f v • ∏ w ∈ S.erase v,
      ((1 / (v - w)) • a - fun _ => w / (v - w)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Pi.sub_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single (a ω)]
    · rw [Finset.prod_eq_one, mul_one]
      intro w hw
      have hne : a ω - w ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm
      field_simp
    · intro v _ hv
      rw [Finset.prod_eq_zero (i := a ω)
        (Finset.mem_erase.mpr ⟨Ne.symm hv, Finset.mem_image_of_mem a (Finset.mem_univ ω)⟩),
        mul_zero]
      ring
    · intro h
      exact absurd (Finset.mem_image_of_mem a (Finset.mem_univ ω)) h
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, known_prod 𝔼 hPO _ fun w _ => hfac v w]

/-- Cochrane (2023), §19.1 and §19.3 (the value of a dollar `Λ_t/P_t` and `P_t/u_c(t)`): on a
finite state space with pull-out, the quotient of two variables known at `t` is known at `t`. -/
theorem known_div_of_fintype [Finite Ω] (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ}
    (ha : 𝔼.E t a = a) (hb : 𝔼.E t b = b) : 𝔼.E t (a / b) = a / b := by
  have e : a / b = a * fun ω => (b ω)⁻¹ := by
    funext ω
    simp [div_eq_mul_inv]
  rw [e, hPO t a _ ha, functionsKnown_of_fintype 𝔼 hPO hb (fun r => r⁻¹)]

/-- Cochrane (2023), eq. (19.11), p. 439, on any state space: `eq1911_iff_tvc` with the
knownness of `Λ_t/P_t` derived (`known_div`) from adapted `Λ` and `P`. -/
theorem eq1911_iff_tvc_adapted (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hΛa : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => Regimes.partial192 𝔼 Λ P N (fun k => s k + c k - y k) t T ω) atTop
        (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) :=
  eq1911_iff_tvc 𝔼 hPO hBP (fun k => known_div 𝔼 hPO (hΛa k) (hPa k) (hP k)) hBa hB hQ hi
    hP hflow t ω

/-- Cochrane (2023), eq. (19.12), p. 439, on any state space: `eq1912_of_tvc` with the
knownness of `Λ_t/P_t` derived (`known_div`) from adapted `Λ` and `P`. -/
theorem eq1912_of_tvc_adapted (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hΛa : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => Regimes.partial193 𝔼 Λ P N i (fun k => s k + c k - y k) t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  eq1912_of_tvc 𝔼 hPO hBP (fun k => known_div 𝔼 hPO (hΛa k) (hPa k) (hP k)) hBa hB hNa hN
    hQ hi hP hflow hbond hmoney

/-- Cochrane (2023), (19.15)–(19.16), p. 441, on any state space: the iterated value of
money with the knownness of `u_c(t)/P_t` and `P_t/u_c(t)` derived (`known_div`) from adapted
`u_c` and `P`. -/
theorem value_of_money_iterated_adapted (hPO : 𝔼.PullOut) {β : ℝ}
    {uc um P i : ℕ → Ω → ℝ} (huca : 𝔼.Adapted uc) (hPa : 𝔼.Adapted P)
    (huc : ∀ t ω, uc t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t T : ℕ) :
    uc t / P t = ∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (um (t + j) / P (t + j)) +
      β ^ (T + 1) • 𝔼.E t (uc (t + T + 1) / P (t + T + 1)) :=
  value_of_money_iterated 𝔼 hPO (fun k => known_div 𝔼 hPO (huca k) (hPa k) (hP k))
    (fun k => known_div 𝔼 hPO (hPa k) (huca k) (huc k)) huc hP hi h1915 h1916 t T

/-- Cochrane (2023), p. 441, on any state space: `value_of_money_limit` with the knownness
hypotheses derived (`known_div`) from adapted `u_c` and `P`. -/
theorem value_of_money_limit_adapted (hPO : 𝔼.PullOut) {β : ℝ}
    {uc um P i : ℕ → Ω → ℝ} (huca : 𝔼.Adapted uc) (hPa : 𝔼.Adapted P)
    (huc : ∀ t ω, uc t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T => β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω) atTop
      (𝓝 (uc t ω / P t ω)) :=
  value_of_money_limit 𝔼 hPO (fun k => known_div 𝔼 hPO (huca k) (hPa k) (hP k))
    (fun k => known_div 𝔼 hPO (hPa k) (huca k) (huc k)) huc hP hi h1915 h1916 t ω htvc

/-! ### Footnote 1 under uncertainty: the time-0 problem on a finite event tree -/

namespace FootnoteTree

open ExpectationsFiniteTree

variable {Ω' : Type*} [Fintype Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`): a process is a function of the date-`t`
node, i.e. constant on the date-`t` information cells of the tree. -/
def TAdapted (x : ℕ → Ω' → ℝ) : Prop := ∀ t ω ω', T.info t ω' ω → x t ω' = x t ω

/-- Cochrane (2023), footnote 1, p. 440: the date-`t` cost
`∑_{x^t} pr(x^t)(Λ_t/Λ_0)(c_t + ι_tm_t)` (`q = Λ_t/Λ_0`, `ι = i/(1 + i)`, `m = M/P`). -/
noncomputable def dateCost (q ι c m : ℕ → Ω' → ℝ) (k : ℕ) : ℝ :=
  ∑ ω, T.prob ω * (q k ω * (c k ω + ι k ω * m k ω))

/-- Cochrane (2023), footnote 1, p. 440: the date-`t` term `∑_{x^t} βᵗpr(x^t)u(c_t, m_t)`. -/
noncomputable def dateUtil (β : ℝ) (u : ℝ → ℝ → ℝ) (c m : ℕ → Ω' → ℝ) (k : ℕ) : ℝ :=
  ∑ ω, T.prob ω * (β ^ k * u (c k ω) (m k ω))

/-- Cochrane (2023), footnote 1, p. 440: a node-contingent plan is feasible when it is adapted
and its present-value cost converges and is at most wealth `W`. -/
def TFeasible (q ι : ℕ → Ω' → ℝ) (W : ℝ) (c m : ℕ → Ω' → ℝ) : Prop :=
  TAdapted T c ∧ TAdapted T m ∧ Summable (dateCost T q ι c m) ∧
    ∑' k, dateCost T q ι c m k ≤ W

/-- Cochrane (2023), (19.9), p. 439 and footnote 1, p. 440: an optimal plan of the time-0
problem on the tree maximises `∑_t ∑_{x^t} βᵗpr(x^t)u` over feasible plans. -/
def TOptimal (β : ℝ) (u : ℝ → ℝ → ℝ) (q ι : ℕ → Ω' → ℝ) (W : ℝ) (c m : ℕ → Ω' → ℝ) : Prop :=
  TFeasible T q ι W c m ∧ Summable (dateUtil T β u c m) ∧
    ∀ c' m', TFeasible T q ι W c' m' → Summable (dateUtil T β u c' m') →
      ∑' k, dateUtil T β u c' m' k ≤ ∑' k, dateUtil T β u c m k

open Classical in
/-- Cochrane (2023), footnote 1, p. 440: the indicator of the date-`t` node (information cell)
containing `ω₀`. -/
noncomputable def cell (t : ℕ) (ω0 ω : Ω') : ℝ := if T.info t ω ω0 then 1 else 0

/-- Cochrane (2023), footnote 1, p. 440: the node indicator is a date-`t` variable. -/
theorem cell_adapted {t : ℕ} {ω0 ω ω' : Ω'} (h : T.info t ω' ω) :
    cell T t ω0 ω' = cell T t ω0 ω := by
  unfold cell
  by_cases h1 : T.info t ω ω0
  · have h2 : T.info t ω' ω0 := (T.info t).iseqv.trans h h1
    simp only [h1, h2, ↓reduceIte]
  · have h2 : ¬ T.info t ω' ω0 := fun h2 => h1 ((T.info t).iseqv.trans
      ((T.info t).iseqv.symm h) h2)
    simp only [h1, h2, ↓reduceIte]

/-- Cochrane (2023), footnote 1, p. 440: changing a date-`t` variable at one node changes the
date-`t` expectation by the node's probability times the change. -/
theorem sum_perturb_cell {t : ℕ} {ω0 : Ω'} (F : Ω' → ℝ → ℝ) (x : Ω' → ℝ)
    (hx : ∀ ω, T.info t ω ω0 → x ω = x ω0) (hF : ∀ ω, T.info t ω ω0 → F ω = F ω0) (d : ℝ) :
    ∑ ω, T.prob ω * F ω (x ω + d * cell T t ω0 ω) =
      ∑ ω, T.prob ω * F ω (x ω) + T.mass t ω0 * (F ω0 (x ω0 + d) - F ω0 (x ω0)) := by
  classical
  unfold FiniteTree.mass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold cell
  by_cases h : T.info t ω ω0
  · simp only [h, ↓reduceIte, mul_one, hx ω h, hF ω h]
    ring
  · simp only [h, ↓reduceIte, mul_zero, add_zero, zero_mul]

/-- Cochrane (2023), footnote 1, p. 440: perturbing a plan at the date-`t` node of `ω₀` and the
date-`s` node of `ω₁` keeps it adapted. -/
theorem perturb_adapted {x : ℕ → Ω' → ℝ} (hx : TAdapted T x) (t s : ℕ) (ω0 ω1 : Ω')
    (d e : ℝ) : TAdapted T (fun k ω => x k ω + (if k = t then d * cell T t ω0 ω else 0) +
      (if k = s then e * cell T s ω1 ω else 0)) := by
  intro k ω ω' h
  have h1 : (if k = t then d * cell T t ω0 ω' else 0) =
      (if k = t then d * cell T t ω0 ω else 0) := by
    split_ifs with hk
    · subst hk; rw [cell_adapted T h]
    · rfl
  have h2 : (if k = s then e * cell T s ω1 ω' else 0) =
      (if k = s then e * cell T s ω1 ω else 0) := by
    split_ifs with hk
    · subst hk; rw [cell_adapted T h]
    · rfl
  simp only
  rw [hx k ω ω' h, h1, h2]

/-- Cochrane (2023), footnote 1, p. 440: a cost-neutral change of an optimal plan at two dates
`t ≠ s` cannot raise the expected utility of those dates. -/
theorem tperturb_le {β W : ℝ} {u : ℝ → ℝ → ℝ} {q ι c m c' m' : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) {t s : ℕ} (hts : t ≠ s) (hca : TAdapted T c')
    (hma : TAdapted T m') (hc : ∀ k, k ≠ t → k ≠ s → c' k = c k)
    (hm : ∀ k, k ≠ t → k ≠ s → m' k = m k)
    (hcost : dateCost T q ι c' m' t + dateCost T q ι c' m' s =
      dateCost T q ι c m t + dateCost T q ι c m s) :
    dateUtil T β u c' m' t + dateUtil T β u c' m' s ≤
      dateUtil T β u c m t + dateUtil T β u c m s := by
  obtain ⟨⟨-, -, hfs, hfW⟩, hus, hmax⟩ := hopt
  have h1 := tsum_modify_two (f := dateCost T q ι c m) (g := dateCost T q ι c' m') hts
    (fun k hkt hks => by simp only [dateCost, hc k hkt hks, hm k hkt hks]) hfs
  have h2 := tsum_modify_two (f := dateUtil T β u c m) (g := dateUtil T β u c' m') hts
    (fun k hkt hks => by simp only [dateUtil, hc k hkt hks, hm k hkt hks]) hus
  have hfeas : TFeasible T q ι W c' m' := ⟨hca, hma, h1.1, by rw [h1.2]; linarith⟩
  have := hmax c' m' hfeas h2.1
  rw [h2.2] at this
  linarith

/-- Cochrane (2023), eq. (19.13), p. 440, under uncertainty (node form): at an optimum on the
tree, for nodes `x^t ∋ ω₀` and `x^s ∋ ω₁` at dates `t ≠ s`,
`βᵗu_c(x^t)q(x^s) = βˢu_c(x^s)q(x^t)` (shift consumption between the two nodes at constant
cost). -/
theorem tree_foc_cc {β W : ℝ} {u uc : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω)) {t s : ℕ}
    (hts : t ≠ s) (ω0 ω1 : Ω') :
    β ^ t * uc (c t ω0) (m t ω0) * q s ω1 = β ^ s * uc (c s ω1) (m s ω1) * q t ω0 := by
  have hca := hopt.1.1
  have hma := hopt.1.2.1
  set Mt := T.mass t ω0 with hMt
  set Ms := T.mass s ω1 with hMs
  have hMt0 : 0 < Mt := T.mass_pos t ω0
  have hMs0 : 0 < Ms := T.mass_pos s ω1
  set A := q s ω1 * Ms with hA
  set B := q t ω0 * Mt with hB
  set D : ℝ → ℝ := fun ε => Mt * (β ^ t * u (c t ω0 + ε * A) (m t ω0)) +
    Ms * (β ^ s * u (c s ω1 + -(ε * B)) (m s ω1)) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    set c' : ℕ → Ω' → ℝ := fun k ω => c k ω + (if k = t then ε * A * cell T t ω0 ω else 0) +
      (if k = s then -(ε * B) * cell T s ω1 ω else 0) with hc'
    have hut := sum_perturb_cell T (fun ω z => β ^ t * u z (m t ω)) (c t)
      (fun ω h => hca t ω0 ω h) (fun ω h => by funext z; rw [hma t ω0 ω h]) (ε * A)
    have hus := sum_perturb_cell T (fun ω z => β ^ s * u z (m s ω)) (c s)
      (fun ω h => hca s ω1 ω h) (fun ω h => by funext z; rw [hma s ω1 ω h]) (-(ε * B))
    have hkt := sum_perturb_cell T (fun ω z => q t ω * (z + ι t ω * m t ω)) (c t)
      (fun ω h => hca t ω0 ω h)
      (fun ω h => by funext z; rw [hq t ω0 ω h, hι t ω0 ω h, hma t ω0 ω h]) (ε * A)
    have hks := sum_perturb_cell T (fun ω z => q s ω * (z + ι s ω * m s ω)) (c s)
      (fun ω h => hca s ω1 ω h)
      (fun ω h => by funext z; rw [hq s ω1 ω h, hι s ω1 ω h, hma s ω1 ω h]) (-(ε * B))
    have h := tperturb_le T hopt hts (perturb_adapted T hca t s ω0 ω1 (ε * A) (-(ε * B)))
      hma (fun k hkt hks => by funext ω; simp [hkt, hks]) (fun _ _ _ => rfl) (by
        simp only [dateCost, hts, Ne.symm hts, ↓reduceIte, add_zero]
        rw [← hMt] at hkt
        rw [← hMs] at hks
        rw [hkt, hks]
        simp only [hA, hB]
        ring)
    simp only [dateUtil, hts, Ne.symm hts, ↓reduceIte, add_zero] at h
    rw [← hMt] at hut
    rw [← hMs] at hus
    rw [hut, hus] at h
    simp only [hD, zero_mul, add_zero, neg_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => c t ω0 + ε * A) A 0 := by
    simpa using (hasDerivAt_mul_const A).const_add (c t ω0)
  have hd2 : HasDerivAt (fun ε => c s ω1 + -(ε * B)) (-B) 0 := by
    simpa using ((hasDerivAt_mul_const B).neg).const_add (c s ω1)
  have hu1 : HasDerivAt (fun ε => u (c t ω0 + ε * A) (m t ω0)) (uc (c t ω0) (m t ω0) * A) 0 :=
    HasDerivAt.comp_of_eq 0 (huc t ω0) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s ω1 + -(ε * B)) (m s ω1))
      (uc (c s ω1) (m s ω1) * -B) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s ω1) hd2 (by simp)
  have hDd : HasDerivAt D (Mt * (β ^ t * (uc (c t ω0) (m t ω0) * A)) +
      Ms * (β ^ s * (uc (c s ω1) (m s ω1) * -B))) 0 :=
    ((hu1.const_mul _).const_mul _).add ((hu2.const_mul _).const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have h0 := hmax.hasDerivAt_eq_zero hDd
  have hfac : Mt * Ms * (β ^ t * uc (c t ω0) (m t ω0) * q s ω1 -
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0) = 0 := by
    rw [← h0, hA, hB]
    ring
  have := (mul_eq_zero.mp hfac).resolve_left (mul_pos hMt0 hMs0).ne'
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, under uncertainty (node form): at an optimum
on the tree, for nodes `x^t ∋ ω₀`, `x^s ∋ ω₁` at dates `t ≠ s`,
`βᵗu_m(x^t)q(x^s) = βˢu_c(x^s)q(x^t)ι(x^t)` (trade real money at one node against consumption at
the other). -/
theorem tree_foc_mc {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω))
    (hum : ∀ k ω, HasDerivAt (fun x => u (c k ω) x) (um (c k ω) (m k ω)) (m k ω)) {t s : ℕ}
    (hts : t ≠ s) (ω0 ω1 : Ω') :
    β ^ t * um (c t ω0) (m t ω0) * q s ω1 =
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0 * ι t ω0 := by
  have hca := hopt.1.1
  have hma := hopt.1.2.1
  set Mt := T.mass t ω0 with hMt
  set Ms := T.mass s ω1 with hMs
  have hMt0 : 0 < Mt := T.mass_pos t ω0
  have hMs0 : 0 < Ms := T.mass_pos s ω1
  set A := q s ω1 * Ms with hA
  set B := q t ω0 * ι t ω0 * Mt with hB
  set D : ℝ → ℝ := fun ε => Mt * (β ^ t * u (c t ω0) (m t ω0 + ε * A)) +
    Ms * (β ^ s * u (c s ω1 + -(ε * B)) (m s ω1)) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    set c' : ℕ → Ω' → ℝ := fun k ω => c k ω + (if k = t then 0 * cell T t ω0 ω else 0) +
      (if k = s then -(ε * B) * cell T s ω1 ω else 0) with hc'
    set m' : ℕ → Ω' → ℝ := fun k ω => m k ω + (if k = t then ε * A * cell T t ω0 ω else 0) +
      (if k = s then 0 * cell T s ω1 ω else 0) with hm'
    have hut := sum_perturb_cell T (fun ω z => β ^ t * u (c t ω) z) (m t)
      (fun ω h => hma t ω0 ω h) (fun ω h => by funext z; rw [hca t ω0 ω h]) (ε * A)
    have hus := sum_perturb_cell T (fun ω z => β ^ s * u z (m s ω)) (c s)
      (fun ω h => hca s ω1 ω h) (fun ω h => by funext z; rw [hma s ω1 ω h]) (-(ε * B))
    have hkt := sum_perturb_cell T (fun ω z => q t ω * (c t ω + ι t ω * z)) (m t)
      (fun ω h => hma t ω0 ω h)
      (fun ω h => by funext z; rw [hq t ω0 ω h, hι t ω0 ω h, hca t ω0 ω h]) (ε * A)
    have hks := sum_perturb_cell T (fun ω z => q s ω * (z + ι s ω * m s ω)) (c s)
      (fun ω h => hca s ω1 ω h)
      (fun ω h => by funext z; rw [hq s ω1 ω h, hι s ω1 ω h, hma s ω1 ω h]) (-(ε * B))
    have h := tperturb_le T hopt hts (perturb_adapted T hca t s ω0 ω1 0 (-(ε * B)))
      (perturb_adapted T hma t s ω0 ω1 (ε * A) 0)
      (fun k hkt hks => by funext ω; simp [hkt, hks])
      (fun k hkt hks => by funext ω; simp [hkt, hks]) (by
        simp only [dateCost, hts, Ne.symm hts, ↓reduceIte, add_zero, zero_mul]
        rw [← hMt] at hkt
        rw [← hMs] at hks
        rw [hkt, hks]
        simp only [hA, hB]
        ring)
    simp only [dateUtil, hts, Ne.symm hts, ↓reduceIte, add_zero, zero_mul] at h
    rw [← hMt] at hut
    rw [← hMs] at hus
    rw [hut, hus] at h
    simp only [hD, zero_mul, add_zero, neg_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => m t ω0 + ε * A) A 0 := by
    simpa using (hasDerivAt_mul_const A).const_add (m t ω0)
  have hd2 : HasDerivAt (fun ε => c s ω1 + -(ε * B)) (-B) 0 := by
    simpa using ((hasDerivAt_mul_const B).neg).const_add (c s ω1)
  have hu1 : HasDerivAt (fun ε => u (c t ω0) (m t ω0 + ε * A)) (um (c t ω0) (m t ω0) * A) 0 :=
    HasDerivAt.comp_of_eq 0 (hum t ω0) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s ω1 + -(ε * B)) (m s ω1))
      (uc (c s ω1) (m s ω1) * -B) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s ω1) hd2 (by simp)
  have hDd : HasDerivAt D (Mt * (β ^ t * (um (c t ω0) (m t ω0) * A)) +
      Ms * (β ^ s * (uc (c s ω1) (m s ω1) * -B))) 0 :=
    ((hu1.const_mul _).const_mul _).add ((hu2.const_mul _).const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have h0 := hmax.hasDerivAt_eq_zero hDd
  have hfac : Mt * Ms * (β ^ t * um (c t ω0) (m t ω0) * q s ω1 -
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0 * ι t ω0) = 0 := by
    rw [← h0, hA, hB]
    ring
  have := (mul_eq_zero.mp hfac).resolve_left (mul_pos hMt0 hMs0).ne'
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, and footnote 1, under uncertainty: at an
optimal plan of the time-0 problem on a finite event tree (with `q_0 = Λ_0/Λ_0 = 1` and
`q_1 > 0`), at every node `βᵗu_c(x^t) = λ(Λ_t/Λ_0)(x^t)` and
`βᵗu_m(x^t) = λ(Λ_t/Λ_0)(x^t) i_t/(1 + i_t)`, with `λ = u_c` at the date-0 node. -/
theorem tree_foc_1913_1914 {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (hq0 : ∀ ω, q 0 ω = 1) (hq1 : ∀ ω, 0 < q 1 ω)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω))
    (hum : ∀ k ω, HasDerivAt (fun x => u (c k ω) x) (um (c k ω) (m k ω)) (m k ω)) (t : ℕ)
    (ω : Ω') :
    β ^ t * uc (c t ω) (m t ω) = uc (c 0 ω) (m 0 ω) * q t ω ∧
      β ^ t * um (c t ω) (m t ω) = uc (c 0 ω) (m 0 ω) * q t ω * ι t ω := by
  have hc : ∀ k, β ^ k * uc (c k ω) (m k ω) = uc (c 0 ω) (m 0 ω) * q k ω := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hq0]
    · have := tree_foc_cc T hopt hq hι huc (Nat.pos_iff_ne_zero.mp hk) ω ω
      rw [hq0] at this
      simpa using this
  refine ⟨hc t, ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 := tree_foc_mc T hopt hq hι huc hum (t := 0) (s := 1) zero_ne_one ω ω
    have h2 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h1 h2 ⊢
    rw [h2, hq0] at h1
    rw [hq0]
    exact mul_right_cancel₀ (hq1 ω).ne' (by linarith)
  · have := tree_foc_mc T hopt hq hι huc hum (Nat.pos_iff_ne_zero.mp ht) (s := 0) ω ω
    rw [hq0] at this
    simpa using this

/-- Cochrane (2023), footnote 1, p. 440: when the date-0 information is trivial (one root node),
the multiplier `λ = u_c(c_0, M_0/P_0)` is the same in every state. -/
theorem lambda_const {c m : ℕ → Ω' → ℝ} (uc : ℝ → ℝ → ℝ) (hca : TAdapted T c)
    (hma : TAdapted T m) (htriv : ∀ a b, T.info 0 a b) (ω ω' : Ω') :
    uc (c 0 ω) (m 0 ω) = uc (c 0 ω') (m 0 ω') := by
  rw [hca 0 ω' ω (htriv ω ω'), hma 0 ω' ω (htriv ω ω')]

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, under uncertainty
(sufficiency): if utility satisfies the supergradient inequality at every node (joint concavity,
`supergradient_of_concave`), `β ≥ 0`, the node first-order conditions hold with `λ ≥ 0` and the
budget binds, then the adapted plan is optimal on the tree. -/
theorem tree_optimal_of_foc {β W lam : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hsup : ∀ k ω c' m', u c' m' ≤ u (c k ω) (m k ω) + uc (c k ω) (m k ω) * (c' - c k ω) +
      um (c k ω) (m k ω) * (m' - m k ω))
    (hfoc : ∀ k ω, β ^ k * uc (c k ω) (m k ω) = lam * q k ω ∧
      β ^ k * um (c k ω) (m k ω) = lam * q k ω * ι k ω)
    (hfeas : TFeasible T q ι W c m) (hbind : ∑' k, dateCost T q ι c m k = W)
    (hus : Summable (dateUtil T β u c m)) : TOptimal T β u q ι W c m := by
  refine ⟨hfeas, hus, fun c' m' hf' hu' => ?_⟩
  have hpt : ∀ k, dateUtil T β u c' m' k ≤ dateUtil T β u c m k +
      lam * (dateCost T q ι c' m' k - dateCost T q ι c m k) := by
    intro k
    unfold dateUtil dateCost
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hsup k ω (c' k ω) (m' k ω)) (pow_nonneg hβ k)
    have h2 := hfoc k ω
    have e : β ^ k * (u (c k ω) (m k ω) + uc (c k ω) (m k ω) * (c' k ω - c k ω) +
        um (c k ω) (m k ω) * (m' k ω - m k ω)) = β ^ k * u (c k ω) (m k ω) +
        lam * (q k ω * (c' k ω + ι k ω * m' k ω) - q k ω * (c k ω + ι k ω * m k ω)) := by
      linear_combination (c' k ω - c k ω) * h2.1 + (m' k ω - m k ω) * h2.2
    have hp := (T.prob_pos ω).le
    have h3 := mul_le_mul_of_nonneg_left (h1.trans_eq e) hp
    linarith
  have hR : HasSum (fun k => dateUtil T β u c m k +
      lam * (dateCost T q ι c' m' k - dateCost T q ι c m k))
      (∑' k, dateUtil T β u c m k + lam * (∑' k, dateCost T q ι c' m' k -
        ∑' k, dateCost T q ι c m k)) :=
    hus.hasSum.add ((hf'.2.2.1.hasSum.sub hfeas.2.2.1.hasSum).mul_left lam)
  have hle := hasSum_le hpt hu'.hasSum hR
  have : lam * (∑' k, dateCost T q ι c' m' k - ∑' k, dateCost T q ι c m k) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hf'.2.2.2])
  linarith

end FootnoteTree

end Cochrane.Monetarism.MoneyInUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary targeting dynamics: the global phase diagram of money in utility

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3.2, pp. 441–445
(eqs. (19.17)–(19.23), Figure 19.1). Restated from the Woodford Chapter 2 project
(`GlobalDynamics` survey lemma L5 and `MoneyTargetingDynamics`, Woodford (2003), §4.1,
eqs. (4.7)–(4.9), pp. 123–133), adapted to this namespace, plus the global dynamics of
Cochrane's power example. Perfect foresight throughout.

## Restated from the Woodford Chapter 2 project

* One-dimensional maps: `orbit_monotone_of_le`, `orbit_antitone_of_ge`, `fixed_of_tendsto`,
  `monotone_orbit_atTop_or_fixed`, `antitone_orbit_atBot_or_fixed`, `sign_near_of_deriv_pos`,
  `repelling_of_one_lt_abs_deriv`, `attracting_of_abs_deriv_lt_one`.
* General utility (19.17): `Ffun`, `Gfun`, `eq48_iff_fisher`. Separable utility (19.18):
  `sepF`, `sepMap`, `eq48_sep_iff`, `sepF_pos`, `sepF_strictMonoOn`, `sepF_tendsto_zero`,
  `sepMap_tendsto_zero` (the second steady state at zero real balances), `sepMap_fixed_iff`
  ((19.19)), `sep_exists_steady_state`, `sep_single_crossing` (cuts from below),
  `IsSepPath`, `sep_path_exists_unique` (one equilibrium per initial price level),
  `sep_inflation_path`, `sep_deflation_path`.
* Satiation (p. 443): `IsPath48`, `Satiation`, `satiated_path`, `money_tvc_violated`,
  `sep_deflation_violates_tvc`, `money_contraction_continuum`.
  (Woodford's Taylor-rule transversality section, E4, the Obstfeld–Rogoff section and the
  convexity counterexample E7 are not restated: they concern interest-rate rules, Appendix A3
  (chain B) and a Woodford-specific claim.)

## New for Cochrane

* `miuPath_iff_sepPath`: Cochrane's (19.18) with constant money growth is Woodford's separable
  map with `μ̄ = 1 + µ`, `c = u_c(y)`, `v' = u_m`.
* Power example (19.23), Figure 19.1: `nextX_fixed`, `nextX_pos`, `nextX_lt_iff`,
  `power_steady_repelling` (the inflationary steady state is unstable), `fig191_repelling`,
  `power_deflation_orbit` (every path started below `x̄` converges to the deflationary steady
  state `x = 0` with `x_{t+1}/x_t → β/(1 + µ)`), `power_deflation_inflation`
  (`P_{t+1}/P_t → β = 1/(1 + δ)`), `power_inflation_exits` (every path started above `x̄` reaches
  `θx^γ ≥ 1`, i.e. `u_m/u_c ≥ 1`, in finite time, so it is not an equilibrium).
* Survey error E13, globally: `e13_no_deflation_attractor` (if `1 + µ ≤ β` no path converges
  to `x = 0`); with `power_deflation_orbit` the deflationary steady state attracts iff
  `1 + µ > β`.
-/

namespace Cochrane.Monetarism.MoneyTargetingDynamics

open Filter Topology
open Cochrane.Monetarism.MoneyInUtility (nextX nextX_hasDerivAt slope_gt_one xbar191
  fig191_steady)

/-! ## L5: one-dimensional monotone maps -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
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

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), p. 127, "local indeterminacy near `Π**`"): if
`g(x*) = x*` and `|g'(x*)| < 1`, every orbit starting within `δ` of `x*` stays within `δ`,
never moves farther from `x*` than it started, and converges to `x*`. -/
theorem attracting_of_abs_deriv_lt_one {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : |d| < 1) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → |x 0 - xs| < δ →
      (∀ t, |x t - xs| < δ) ∧ (∀ t, |x t - xs| ≤ |x 0 - xs|) ∧
        Tendsto x atTop (𝓝 xs) := by
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
  refine ⟨fun t => (hbd t).2, fun t => ?_, ?_⟩
  · have hkt : k ^ t ≤ 1 := pow_le_one₀ hk0 hk1.le
    nlinarith [(hbd t).1, abs_nonneg (x 0 - xs)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (hbd t).1) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x 0 - xs|


/-! ## (4.7)–(4.8) -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7), p. 129: `F(m) = [U_c(ȳ, m) − U_m(ȳ, m)]m`. -/
def Ffun (Uc Um : ℝ → ℝ) (m : ℝ) : ℝ := (Uc m - Um m) * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7), p. 129: `G(m) = U_c(ȳ, m)m`. -/
def Gfun (Uc : ℝ → ℝ) (m : ℝ) : ℝ := Uc m * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7)–(4.8), p. 129, derivation: at a date with `m_t = M_t/P_t`,
`m_{t+1} = μ̄M_t/P_{t+1}`, the money-demand condition (3.3) `U_m/U_c = i/(1+i)` (`i^m = 0`), and
`U_c > 0`, `U_c − U_m > 0`, the perfect-foresight Fisher equation (1.21) holds iff
`U_c(m_{t+1})m_{t+1} = (μ̄/β)[U_c(m_t) − U_m(m_t)]m_t`, i.e. `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
theorem eq48_iff_fisher {β μ P P1 M m m1 i uc uc1 um : ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hP : 0 < P) (hP1 : 0 < P1) (hM : 0 < M) (huc : 0 < uc) (huc1 : 0 < uc1)
    (hgap : 0 < uc - um) (hm : m = M / P) (hm1 : m1 = μ * M / P1)
    (h33 : um / uc = i / (1 + i)) (hi : 0 < 1 + i) :
    (1 + i = β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹) ↔ uc1 * m1 = μ / β * ((uc - um) * m) := by
  have hi' : 1 + i = uc / (uc - um) := by
    rw [div_eq_div_iff huc.ne' hi.ne'] at h33
    rw [eq_div_iff hgap.ne']
    linarith
  have hR : β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹ = uc * P1 / (β * uc1 * P) := by
    field_simp
  have eL : uc1 * (μ * M / P1) = (β * uc1 * P) * (μ * M / (β * P * P1)) := by
    field_simp
  have eR : μ / β * ((uc - um) * (M / P)) = ((uc - um) * P1) * (μ * M / (β * P * P1)) := by
    field_simp
  rw [hi', hR, div_eq_div_iff hgap.ne' (by positivity), hm, hm1, eL, eR,
    mul_left_inj' (ne_of_gt (by positivity))]
  constructor
  · intro h
    exact mul_left_cancel₀ huc.ne' (by linarith [h])
  · intro h
    rw [h]; ring

/-! ## The separable case: Figure 2.5 -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, additively separable case: `F(m) = (c − v'(m))m`, where `c > 0` is
the (constant) marginal utility of consumption at `ȳ` and `v'(m) = U_m`. -/
def sepF (c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := (c - vp m) * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), Figure 2.5, p. 130: the graph `m ↦ G⁻¹((μ̄/β)F(m))` for `G(m) = cm`. -/
noncomputable def sepMap (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := μ / β * sepF c vp m / c

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 130: in the separable case `G(m) = cm` is linear and can be
inverted, so `G(m') = (μ̄/β)F(m)` iff `m'` is the value of the map of Figure 2.5. -/
theorem eq48_sep_iff {β μ c m m' : ℝ} {vp : ℝ → ℝ} (hc : 0 < c) :
    c * m' = μ / β * sepF c vp m ↔ m' = sepMap β μ c vp m := by
  unfold sepMap
  rw [eq_div_iff hc.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130: if `U_c − U_m = c − v'(m) > 0` for `m > 0`, then `F(m) > 0`. -/
theorem sepF_pos {c m : ℝ} {vp : ℝ → ℝ} (hgap : c - vp m > 0) (hm : 0 < m) : 0 < sepF c vp m :=
  mul_pos hgap hm

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "`F(m)` equals `m` times an increasing function of `m`": with `v'`
nonincreasing (concave `v`) and `c − v' > 0`, `F` is strictly increasing on `(0, ∞)`. -/
theorem sepF_strictMonoOn {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : StrictMonoOn (sepF c vp) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hvp : vp b ≤ vp a := hanti ha hb hab.le
  have h1 := hgap a ha'
  unfold sepF
  nlinarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "takes the limiting value `F(0) = 0`": under the hypotheses of
`sepF_strictMonoOn`, `F(m) → 0` as `m → 0⁺`. -/
theorem sepF_tendsto_zero {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepF c vp) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝 0) (𝓝 ((c - vp 1) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with m hm
    exact (sepF_pos (by linarith [hgap m hm]) hm).le
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with m hm hm1
    unfold sepF
    have : vp 1 ≤ vp m := hanti hm (Set.mem_Ioi.mpr one_pos) hm1.2.le
    have hm' : (0 : ℝ) < m := hm
    nlinarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "there is a second steady state, this time at zero real balances":
the map of Figure 2.5 tends to `0` as `m → 0⁺`. -/
theorem sepMap_tendsto_zero {β μ c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepMap β μ c vp) (𝓝[>] 0) (𝓝 0) := by
  have := ((sepF_tendsto_zero hanti hgap).const_mul (μ / β)).div_const c
  rw [mul_zero, zero_div] at this
  exact this

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130: the steady states of (4.8) are the `m > 0` with
`v'(m)/c = 1 − β/μ̄`, i.e. `U_m/U_c = Δ` at `1 + i = μ̄/β`, so `m* = L[ȳ, (μ̄ − β)/β]`. -/
theorem sepMap_fixed_iff {β μ c m : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hm : 0 < m) : sepMap β μ c vp m = m ↔ vp m = c * (1 - β / μ) := by
  unfold sepMap sepF
  rw [div_eq_iff hc.ne']
  constructor
  · intro h
    field_simp at h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130 and fn. 38: if `v'` is continuous on `(0, ∞)` and takes values on
both sides of `c(1 − β/μ̄)`, the steady state `m* > 0` exists. -/
theorem sep_exists_steady_state {β μ c a b : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hcont : ContinuousOn vp (Set.Ioi 0)) (ha : 0 < a) (hab : a ≤ b)
    (hva : c * (1 - β / μ) ≤ vp a) (hvb : vp b ≤ c * (1 - β / μ)) :
    ∃ ms, a ≤ ms ∧ ms ≤ b ∧ sepMap β μ c vp ms = ms := by
  obtain ⟨ms, hms, hv⟩ := intermediate_value_Icc' hab
    (hcont.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z)) ⟨hvb, hva⟩
  exact ⟨ms, hms.1, hms.2, (sepMap_fixed_iff hβ hμ hc (by linarith [hms.1])).mpr hv⟩

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "at this point the curve necessarily cuts the diagonal from below"
(single crossing, without any convexity): if `v'` is nonincreasing and `m*` is the only
`m > 0` with `v'(m) = v'(m*)` (e.g. `v'` strictly decreasing), then the map is below the
diagonal on `(0, m*)` and above it on `(m*, ∞)`. -/
theorem sep_single_crossing {β μ c ms : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hanti : AntitoneOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) :
    (∀ m, 0 < m → m < ms → sepMap β μ c vp m < m) ∧
      (∀ m, ms < m → m < sepMap β μ c vp m) := by
  have hv := (sepMap_fixed_iff hβ hμ hc hms).mp hfix
  have key : ∀ m, 0 < m →
      sepMap β μ c vp m - m = m * (c * (1 - β / μ) - vp m) * μ / (β * c) := by
    intro m _
    unfold sepMap sepF
    field_simp
    ring
  have hpos : ∀ m, 0 < m → 0 < m * μ / (β * c) := fun m hm => by positivity
  constructor
  · intro m hm hlt
    have h1 : vp ms ≤ vp m := hanti hm hms hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : c * (1 - β / μ) - vp m < 0 := by
      rw [← hv]; exact sub_neg.mpr (lt_of_le_of_ne h1 h2.symm)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]
  · intro m hlt
    have hm : 0 < m := by linarith
    have h1 : vp m ≤ vp ms := hanti hms hm hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : 0 < c * (1 - β / μ) - vp m := by
      rw [← hv]; exact sub_pos.mpr (lt_of_le_of_ne h1 h2)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 130: a perfect-foresight path of real balances in the separable
case: positive with `c m_{t+1} = (μ̄/β)F(m_t)` at all dates. -/
def IsSepPath (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, c * m (t + 1) = μ / β * sepF c vp (m t)

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "a distinct perfect-foresight equilibrium corresponding to each
possible value of `m₀`": from every `m₀ > 0` the orbit of the map is a path, and a path is the
orbit of its initial value. -/
theorem sep_path_exists_unique {β μ c : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hgap : ∀ m, 0 < m → vp m < c) {m0 : ℝ} (hm0 : 0 < m0) :
    IsSepPath β μ c vp (fun t => (sepMap β μ c vp)^[t] m0) ∧
      ∀ m : ℕ → ℝ, IsSepPath β μ c vp m → m 0 = m0 → m = fun t => (sepMap β μ c vp)^[t] m0 := by
  have hsucc : ∀ t, (sepMap β μ c vp)^[t + 1] m0 = sepMap β μ c vp ((sepMap β μ c vp)^[t] m0) :=
    fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < (sepMap β μ c vp)^[t] m0 := by
    intro t
    induction t with
    | zero => exact hm0
    | succ n ih =>
      rw [hsucc]
      have := sepF_pos (c := c) (vp := vp) (by linarith [hgap _ ih]) ih
      unfold sepMap
      positivity
  refine ⟨⟨hpos, fun t => (eq48_sep_iff hc).mpr (hsucc t)⟩, fun m hm h0 => funext fun t => ?_⟩
  induction t with
  | zero => exact h0
  | succ n ih => rw [(eq48_sep_iff hc).mp (hm.2 n), ih, hsucc]

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "if `m₀ < m*`, real balances must be expected to decrease over
time …, converging to zero asymptotically. This corresponds to a self-fulfilling inflation":
strictly decreasing, tending to `0`. -/
theorem sep_inflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : m 0 < ms) : StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).1
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, m t < ms ∧ m (t + 1) < m t := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ (hpath.1 0) h0⟩
    | succ n ih =>
      have h1 : m (n + 1) < ms := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ (hpath.1 _) h1⟩
  have hsa : StrictAnti m := strictAnti_nat_of_succ_lt fun t => (hstep t).2
  refine ⟨hsa, ?_⟩
  rcases antitone_orbit_atBot_or_fixed hrec hsa.antitone with h | ⟨L, hL, hbd, hfixL⟩
  · exfalso
    obtain ⟨t, ht⟩ := (h.eventually (eventually_le_atBot (0 : ℝ))).exists
    linarith [hpath.1 t]
  · have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (hpath.1 t).le)
    rcases hL0.lt_or_eq with hLpos | hL0
    · exfalso
      have hcL : ContinuousAt (sepMap β μ c vp) L := by
        have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
        unfold sepMap sepF
        exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
          continuousAt_const hc.ne'
      have hf := hfixL hcL
      have hLms : L < ms := lt_of_le_of_lt (hbd 0) h0
      have := hsc L hLpos hLms
      linarith
    · rw [← hL0] at hL; exact hL

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 131, "if instead `m₀ > m*`, real balances must increase over time,
eventually increasing without bound" (the self-fulfilling deflation of monetary targeting). -/
theorem sep_deflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : ms < m 0) : StrictMono m ∧ Tendsto m atTop atTop := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).2
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, ms < m t ∧ m t < m (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ h0⟩
    | succ n ih =>
      have h1 : ms < m (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ h1⟩
  have hsm : StrictMono m := strictMono_nat_of_lt_succ fun t => (hstep t).2
  refine ⟨hsm, ?_⟩
  rcases monotone_orbit_atTop_or_fixed hrec hsm.monotone with h | ⟨L, _, hbd, hfixL⟩
  · exact h
  · exfalso
    have hLpos : 0 < L := by linarith [hbd 0]
    have hcL : ContinuousAt (sepMap β μ c vp) L := by
      have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
      unfold sepMap sepF
      exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
        continuousAt_const hc.ne'
    have hf := hfixL hcL
    have := hsc L (by linarith [hbd 0])
    linarith


/-! ## (4.9): satiation and the transversality condition under monetary targeting -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 129, general (possibly nonseparable) utility: a perfect-foresight
path of real balances, positive with `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
def IsPath48 (β μ : ℝ) (Uc Um : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, Gfun Uc (m (t + 1)) = μ / β * Ffun Uc Um (m t)

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 131–132: satiation at `m̄`: for `m ≥ m̄`, `U_m = 0` and `U_c` is constant
(`F = G` there). -/
def Satiation (Uc Um : ℝ → ℝ) (msat : ℝ) : Prop := ∀ m, msat ≤ m → Um m = 0 ∧ Uc m = Uc msat

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 131, "(4.8) requires that `m_{t+1} = μ̄/β m_t` each period, after real
balances exceed the satiation level": with `G` strictly increasing, `μ̄ ≥ β` and satiation at
`m̄`, a path that reaches `m̄` at `t₀` satisfies `m_{t₀+n} = (μ̄/β)ⁿ m_{t₀} ≥ m̄` for all `n`. -/
theorem satiated_path {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β ≤ μ)
    (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat) (hmsat : 0 < msat)
    (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m) {t0 : ℕ}
    (ht0 : msat ≤ m t0) : ∀ n, msat ≤ m (t0 + n) ∧ m (t0 + n) = (μ / β) ^ n * m t0 := by
  intro n
  induction n with
  | zero => simp [ht0]
  | succ n ih =>
    have hs := hsat _ ih.1
    have heq := hpath.2 (t0 + n)
    unfold Gfun Ffun at heq
    rw [hs.1, hs.2, sub_zero] at heq
    have hratio : 1 ≤ μ / β := (one_le_div hβ).mpr hμβ
    have hge : msat ≤ m (t0 + n + 1) := by
      by_contra hcon
      push Not at hcon
      have h1 : Gfun Uc (m (t0 + n + 1)) < Gfun Uc msat :=
        hG (hpath.1 _) (Set.mem_Ioi.mpr hmsat) hcon
      unfold Gfun at h1
      rw [heq] at h1
      have h2 : Uc msat * msat ≤ Uc msat * m (t0 + n) := mul_le_mul_of_nonneg_left ih.1 hUc.le
      have h3 : Uc msat * m (t0 + n) ≤ μ / β * (Uc msat * m (t0 + n)) :=
        le_mul_of_one_le_left (by nlinarith [hpath.1 (t0 + n)]) hratio
      linarith
    have hs1 := hsat _ hge
    rw [hs1.2] at heq
    have hm1 : m (t0 + n + 1) = μ / β * m (t0 + n) :=
      mul_left_cancel₀ hUc.ne' (by rw [heq]; ring)
    refine ⟨by rw [← add_assoc]; exact hge, ?_⟩
    rw [← add_assoc, hm1, ih.2, pow_succ]
    ring

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.9), p. 132, "the transversality condition is violated in the case of
any such path": with `0 < β`, `μ̄ ≥ 1`, satiation at `m̄ > 0`, `G` strictly increasing and a path
reaching `m̄`, `β^T U_c(m_T)m_T = β^{t₀}μ̄^{T−t₀}U_c m_{t₀} ≥ β^{t₀}U_c m_{t₀} > 0` for `T ≥ t₀`, so
`β^T U_c(m_T) m_T` does not tend to `0`. -/
theorem money_tvc_violated {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat)
    (hmsat : 0 < msat) (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m)
    {t0 : ℕ} (ht0 : msat ≤ m t0) :
    (∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
        β ^ t0 * μ ^ n * Uc (m t0) * m t0) ∧
      ¬ Tendsto (fun T => β ^ T * Uc (m T) * m T) atTop (𝓝 0) := by
  have hsp := satiated_path hβ (by linarith) hsat hUc hmsat hG hpath ht0
  have hval : ∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
      β ^ t0 * μ ^ n * Uc (m t0) * m t0 := by
    intro n
    rw [(hsat _ (hsp n).1).2, (hsat _ ht0).2, (hsp n).2, pow_add, div_pow]
    field_simp
  refine ⟨hval, fun h => ?_⟩
  have hpos : 0 < β ^ t0 * Uc (m t0) * m t0 := by
    rw [(hsat _ ht0).2]; have := hpath.1 t0; positivity
  have hev : ∀ᶠ T in atTop, β ^ t0 * Uc (m t0) * m t0 ≤ β ^ T * Uc (m T) * m T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [hval n]
    have h1 : 1 ≤ μ ^ n := one_le_pow₀ hμ
    have : β ^ t0 * Uc (m t0) * m t0 * 1 ≤ β ^ t0 * Uc (m t0) * m t0 * μ ^ n :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    linarith
  have := ge_of_tendsto h hev
  linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 131–132, combined: in the separable model with satiation at `m̄`
(`v' = 0` on `[m̄, ∞)`) and `μ̄ ≥ 1`, every deflationary path (`m₀ > m*`) violates the
transversality condition (4.9), so it is not an equilibrium. -/
theorem sep_deflation_violates_tvc {β μ c ms msat : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0))
    (hcont : ContinuousOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hmsat : 0 < msat)
    (hsat : ∀ m, msat ≤ m → vp m = 0) (hpath : IsSepPath β μ c vp m) (h0 : ms < m 0) :
    ¬ Tendsto (fun T => β ^ T * (fun _ : ℝ => c) (m T) * m T) atTop (𝓝 0) := by
  have hdef := sep_deflation_path hβ (by linarith) hc hanti hcont hms hfix huniq hpath h0
  obtain ⟨t0, ht0⟩ := (hdef.2.eventually (eventually_ge_atTop msat)).exists
  refine (money_tvc_violated (Uc := fun _ => c) (Um := vp) hβ hβ1 hμ
    (fun m hm => ⟨hsat m hm, rfl⟩) hc hmsat
    (fun a _ b _ hab => by unfold Gfun; nlinarith) ⟨hpath.1, fun t => ?_⟩ ht0).2
  have := hpath.2 t
  unfold Gfun Ffun
  unfold sepF at this
  linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, "under the monetary targeting regime … the previous argument …
fails when `μ̄ < 1`. In this case, the transversality condition is satisfied by all of the
solutions to (4.8) that involve inflation rates eventually falling to the level `Π_t = β`, and
so a continuum of perfect-foresight equilibria … exists": with satiation at `m̄ > 0`, `U_c` constant
above `m̄` and `β < μ̄ < 1`, each `m₀ ≥ m̄` starts the path `m_t = (μ̄/β)^t m₀` of (4.8), distinct
for distinct `m₀`; along it inflation `μ̄m_t/m_{t+1}` equals `β`, the transversality condition
holds and the bound (3.4) converges. -/
theorem money_contraction_continuum {β μ msat ybar : ℝ} {Uc Um : ℝ → ℝ} (hβ : 0 < β)
    (hβμ : β < μ) (hμ1 : μ < 1) (hsat : Satiation Uc Um msat) {m0 : ℝ} (hm0 : msat ≤ m0)
    (hmsat : 0 < msat) :
    IsPath48 β μ Uc Um (fun t => (μ / β) ^ t * m0) ∧
      (∀ t, μ * ((μ / β) ^ t * m0) / ((μ / β) ^ (t + 1) * m0) = β) ∧
      Tendsto (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) atTop (𝓝 0) ∧
      Summable (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) := by
  have hm0pos : 0 < m0 := by linarith
  have hr : 1 ≤ μ / β := (one_le_div hβ).mpr hβμ.le
  have hge : ∀ t, msat ≤ (μ / β) ^ t * m0 := fun t =>
    le_trans hm0 (le_mul_of_one_le_left hm0pos.le (one_le_pow₀ hr))
  have hμ0 : 0 < μ := by linarith
  refine ⟨⟨fun t => by positivity, fun t => ?_⟩, fun t => ?_, ?_, ?_⟩
  · unfold Gfun Ffun
    rw [(hsat _ (hge t)).1, (hsat _ (hge (t + 1))).2, (hsat _ (hge t)).2]
    simp only [pow_succ]
    ring
  · rw [pow_succ]
    field_simp
  · have hcongr : (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) =
        fun T => μ ^ T * (Uc msat * m0) := by
      funext T
      rw [(hsat _ (hge T)).2, div_pow]
      field_simp
    rw [hcongr]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).mul_const (Uc msat * m0)
  · have hcongr : (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) = fun T => β ^ T * (Uc msat * ybar) := by
      funext T
      rw [(hsat _ (hge T)).1, (hsat _ (hge T)).2]
      ring
    rw [hcongr]
    exact (summable_geometric_of_lt_one hβ.le (by linarith)).mul_right _


/-! ## Cochrane's (19.18) is the separable map -/

/-- Cochrane (2023), eq. (19.18), p. 442: with money growth `M_{t+1} = (1 + µ)M_t`, a path of
(19.18) is exactly a path of the separable map with `μ̄ = 1 + µ`, `c = u_c(y)`, `v' = u_m`. -/
theorem miuPath_iff_sepPath {β ucy μg : ℝ} {um : ℝ → ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hucy : 0 < ucy) (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = μg * M t) :
    MoneyInUtility.IsMIUPath β ucy um M m ↔ IsSepPath β μg ucy um m := by
  have hμ : μg ≠ 0 := by
    intro h
    have := hg 0
    rw [h, zero_mul] at this
    exact (hM 1).ne' this
  constructor
  · intro h
    refine ⟨fun t => (h t).1, fun t => ?_⟩
    have h1 := (h t).2
    have hm := (h t).1
    have hMt := hM t
    rw [hg t] at h1
    unfold sepF
    have e : um (m t) = ucy * (1 - β * (m (t + 1) / m t) * (M t / (μg * M t))) := by
      field_simp at h1 ⊢
      linarith
    rw [e]
    field_simp
    ring
  · intro h t
    refine ⟨h.1 t, ?_⟩
    have h1 := h.2 t
    have hm := h.1 t
    have hMt := hM t
    rw [hg t]
    unfold sepF at h1
    field_simp
    field_simp at h1
    linarith

/-! ## The power example (19.23) and Figure 19.1 -/

/-- Cochrane (2023), eq. (19.23), p. 444: `x̄` is a fixed point of (19.23) when
`1 − θx̄^γ ≠ 0`. -/
theorem nextX_fixed {θ γ xb : ℝ} (hK : 1 - θ * xb ^ γ ≠ 0) : nextX θ γ xb xb = xb := by
  unfold nextX
  field_simp

/-- Cochrane (2023), eq. (19.23), p. 444: the map sends positive `x` with `θx^γ < 1` (the
domain where `u_m/u_c < 1`) to a positive value. -/
theorem nextX_pos {θ γ xb x : ℝ} (hK : 0 < 1 - θ * xb ^ γ) (hx : 0 < x) (hd : θ * x ^ γ < 1) :
    0 < nextX θ γ xb x := by
  unfold nextX
  exact div_pos (mul_pos hx hK) (by linarith)

/-- Cochrane (2023), Figure 19.1, p. 444 (single crossing): on the domain `θx^γ < 1`, (19.23)
lies below the diagonal exactly for `x < x̄` and above it exactly for `x > x̄`. -/
theorem nextX_lt_iff {θ γ xb x : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hx : 0 < x) (hd : θ * x ^ γ < 1) :
    (nextX θ γ xb x < x ↔ x < xb) ∧ (x < nextX θ γ xb x ↔ xb < x) := by
  have hD : 0 < 1 - θ * x ^ γ := by linarith
  have k1 : nextX θ γ xb x < x ↔ θ * x ^ γ < θ * xb ^ γ := by
    unfold nextX
    rw [div_lt_iff₀ hD]
    constructor <;> intro h <;> nlinarith
  have k2 : x < nextX θ γ xb x ↔ θ * xb ^ γ < θ * x ^ γ := by
    unfold nextX
    rw [lt_div_iff₀ hD]
    constructor <;> intro h <;> nlinarith
  have k3 : ∀ a b : ℝ, 0 < a → 0 < b → (θ * a ^ γ < θ * b ^ γ ↔ a < b) := fun a b ha hb =>
    ⟨fun h => (Real.rpow_lt_rpow_iff ha.le hb.le hγ).mp (lt_of_mul_lt_mul_left h hθ.le),
      fun h => mul_lt_mul_of_pos_left ((Real.rpow_lt_rpow_iff ha.le hb.le hγ).mpr h) hθ⟩
  exact ⟨k1.trans (k3 x xb hx hxb), k2.trans (k3 xb x hxb hx)⟩

/-- Cochrane (2023), p. 444 ("Therefore, `Py/M` is an unstable unique locally bounded
equilibrium"): for `θ, γ > 0`, `x̄ > 0`, `0 < 1 − θx̄^γ`, the steady state of (19.23) is
repelling: there is `δ > 0` such that every other path eventually lies at least `δ` away. -/
theorem power_steady_repelling {θ γ xb : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hK : 0 < 1 - θ * xb ^ γ) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = nextX θ γ xb (x t)) → x 0 ≠ xb →
      ∃ t, δ ≤ |x t - xb| := by
  have hs := slope_gt_one hθ hγ hxb hK
  exact repelling_of_one_lt_abs_deriv (nextX_fixed hK.ne') (nextX_hasDerivAt hxb hK.ne')
    (by rw [abs_of_pos (by linarith)]; exact hs)

/-- Cochrane (2023), Figure 19.1, p. 444: with `δ = µ = 0.2`, `γ = 2`, `θ = 0.01` the
inflationary steady state `x̄ ≈ 5.53` is repelling. -/
theorem fig191_repelling :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = nextX (1 / 100) 2 xbar191 (x t)) →
      x 0 ≠ xbar191 → ∃ t, δ ≤ |x t - xbar191| := by
  have hpos : 0 < xbar191 := Real.sqrt_pos.mpr (by norm_num)
  have hs := fig191_steady.2
  exact power_steady_repelling (by norm_num) (by norm_num) hpos (by rw [hs]; norm_num)

/-- Cochrane (2023), p. 444 ("The figure shows the second steady state at `P_ty/M_t = 0` …
This steady state is stable; multiple equilibria in this neighborhood stay nearby"): every
path of (19.23) started at `0 < x_0 < x̄` is strictly decreasing, stays positive, converges to
`0`, and `x_{t+1}/x_t → 1 − θx̄^γ` (`= β/(1 + µ)`). -/
theorem power_deflation_orbit {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ) (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t))
    (h0 : 0 < x 0) (h0' : x 0 < xb) :
    StrictAnti x ∧ (∀ t, 0 < x t) ∧ Tendsto x atTop (𝓝 0) ∧
      Tendsto (fun t => x (t + 1) / x t) atTop (𝓝 (1 - θ * xb ^ γ)) := by
  have hdom : ∀ z, 0 < z → z < xb → θ * z ^ γ < 1 := fun z hz hzb => by
    have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hz.le hzb hγ) hθ
    linarith
  have hinv : ∀ t, 0 < x t ∧ x t < xb ∧ x (t + 1) < x t := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0, h0', ?_⟩
      rw [hrec 0]
      exact ((nextX_lt_iff hθ hγ hxb h0 (hdom _ h0 h0')).1).mpr h0'
    | succ n ih =>
      have hp : 0 < x (n + 1) := by
        rw [hrec n]; exact nextX_pos hK ih.1 (hdom _ ih.1 ih.2.1)
      have hl : x (n + 1) < xb := lt_trans ih.2.2 ih.2.1
      refine ⟨hp, hl, ?_⟩
      rw [hrec (n + 1)]
      exact ((nextX_lt_iff hθ hγ hxb hp (hdom _ hp hl)).1).mpr hl
  have hsa : StrictAnti x := strictAnti_nat_of_succ_lt fun t => (hinv t).2.2
  have hlim : Tendsto x atTop (𝓝 0) := by
    rcases antitone_orbit_atBot_or_fixed hrec hsa.antitone with h | ⟨L, hL, hbd, hfixL⟩
    · exfalso
      obtain ⟨t, ht⟩ := (h.eventually (eventually_le_atBot (0 : ℝ))).exists
      linarith [(hinv t).1]
    · have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (hinv t).1.le)
      rcases hL0.lt_or_eq with hLpos | hL0
      · exfalso
        have hLxb : L < xb := lt_of_le_of_lt (hbd 0) h0'
        have hdL := hdom L hLpos hLxb
        have hcL : ContinuousAt (nextX θ γ xb) L := by
          have hc : ContinuousAt (fun z : ℝ => z ^ γ) L :=
            Real.continuousAt_rpow_const L γ (Or.inl hLpos.ne')
          unfold nextX
          exact (continuousAt_id.mul continuousAt_const).div
            (continuousAt_const.sub (continuousAt_const.mul hc)) (by linarith)
        have hf := hfixL hcL
        have := ((nextX_lt_iff hθ hγ hxb hLpos hdL).1).mpr hLxb
        linarith
      · rw [← hL0] at hL; exact hL
  refine ⟨hsa, fun t => (hinv t).1, hlim, ?_⟩
  have hratio : ∀ t, x (t + 1) / x t = (1 - θ * xb ^ γ) / (1 - θ * x t ^ γ) := by
    intro t
    have hxt := (hinv t).1
    rw [hrec t]
    unfold nextX
    field_simp
  have hc0 : Tendsto (fun t => x t ^ γ) atTop (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp hlim
    rwa [Real.zero_rpow hγ.ne'] at hc
  have hden : Tendsto (fun t => 1 - θ * x t ^ γ) atTop (𝓝 (1 - θ * 0)) :=
    (hc0.const_mul θ).const_sub 1
  rw [mul_zero, sub_zero] at hden
  have h2 := (tendsto_const_nhds (x := 1 - θ * xb ^ γ)).div hden one_ne_zero
  rw [div_one] at h2
  exact h2.congr fun t => (hratio t).symm

/-- Cochrane (2023), p. 444 (`lim P_{t+1}/P_t = 1/(1 + δ)`): along such a path, gross inflation
`P_{t+1}/P_t = (1 + µ)x_{t+1}/x_t` tends to `β` when `θx̄^γ = 1 − β/(1 + µ)`. -/
theorem power_deflation_inflation {θ γ xb β μg : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ) (hμ : μg ≠ 0) (hss : θ * xb ^ γ = 1 - β / μg)
    (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t)) (h0 : 0 < x 0) (h0' : x 0 < xb) :
    Tendsto (fun t => μg * (x (t + 1) / x t)) atTop (𝓝 β) := by
  have h := ((power_deflation_orbit hθ hγ hxb hK hrec h0 h0').2.2.2).const_mul μg
  have e : μg * (1 - θ * xb ^ γ) = β := by rw [hss]; field_simp; ring
  rwa [e] at h

/-- Cochrane (2023), Figure 19.1, p. 444 (paths to the right of `x̄`; cf. Online Appendix A3):
every path of (19.23) started at `x_0 > x̄` reaches `θx_t^γ ≥ 1` in finite time. There
`u_m/u_c = θx^γ ≥ 1 > i/(1 + i)`, so no such path is an equilibrium. -/
theorem power_inflation_exits {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ)
    (hrec : ∀ t, θ * x t ^ γ < 1 → x (t + 1) = nextX θ γ xb (x t)) (h0 : xb < x 0) :
    ∃ t, 1 ≤ θ * x t ^ γ := by
  by_contra hcon
  push Not at hcon
  have hrec' : ∀ t, x (t + 1) = nextX θ γ xb (x t) := fun t => hrec t (hcon t)
  have hinv : ∀ t, xb < x t ∧ x t < x (t + 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0, ?_⟩
      rw [hrec' 0]
      exact ((nextX_lt_iff hθ hγ hxb (by linarith) (hcon 0)).2).mpr h0
    | succ n ih =>
      have hl : xb < x (n + 1) := lt_trans ih.1 ih.2
      refine ⟨hl, ?_⟩
      rw [hrec' (n + 1)]
      exact ((nextX_lt_iff hθ hγ hxb (by linarith) (hcon _)).2).mpr hl
  have hsm : StrictMono x := strictMono_nat_of_lt_succ fun t => (hinv t).2
  rcases monotone_orbit_atTop_or_fixed hrec' hsm.monotone with h | ⟨L, hL, hbd, -⟩
  · have hr : Tendsto (fun t => θ * x t ^ γ) atTop atTop :=
      ((tendsto_rpow_atTop hγ).comp h).const_mul_atTop hθ
    obtain ⟨t, ht⟩ := (hr.eventually (eventually_ge_atTop 1)).exists
    linarith [hcon t]
  · have hLxb : xb < L := lt_of_lt_of_le h0 (hbd 0)
    have hLpos : 0 < L := lt_trans hxb hLxb
    have hid : ∀ t, x (t + 1) * (1 - θ * x t ^ γ) = x t * (1 - θ * xb ^ γ) := by
      intro t
      have hD : 1 - θ * x t ^ γ ≠ 0 := by linarith [hcon t]
      rw [hrec' t]
      unfold nextX
      field_simp
    have hc : Tendsto (fun t => x t ^ γ) atTop (𝓝 (L ^ γ)) :=
      (Real.continuousAt_rpow_const L γ (Or.inl hLpos.ne')).tendsto.comp hL
    have h1 : Tendsto (fun t => x (t + 1) * (1 - θ * x t ^ γ)) atTop
        (𝓝 (L * (1 - θ * L ^ γ))) :=
      ((tendsto_add_atTop_iff_nat 1).mpr hL).mul ((hc.const_mul θ).const_sub 1)
    have h2 : Tendsto (fun t => x t * (1 - θ * xb ^ γ)) atTop (𝓝 (L * (1 - θ * xb ^ γ))) :=
      hL.mul_const _
    have heq : L * (1 - θ * L ^ γ) = L * (1 - θ * xb ^ γ) :=
      tendsto_nhds_unique (h1.congr hid) h2
    have heq2 : θ * L ^ γ = θ * xb ^ γ := by
      have := mul_left_cancel₀ hLpos.ne' heq
      linarith
    have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hxb.le hLxb hγ) hθ
    linarith

/-- Cochrane (2023), pp. 444–445, survey error E13 (global form): if `1 − θx̄^γ = β/(1 + µ) ≥ 1`,
i.e. `1 + µ ≤ β`, no path of (19.23) staying in the domain `0 < x`, `θx^γ < 1` converges to the
deflationary steady state `x = 0`. With `power_deflation_orbit` (`1 + µ > β`), the zero-rate
steady state attracts iff `1 + µ > β`, not `1 + µ > 1/β` as printed. -/
theorem e13_no_deflation_attractor {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ)
    (hK1 : 1 ≤ 1 - θ * xb ^ γ) (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t))
    (hdom : ∀ t, 0 < x t ∧ θ * x t ^ γ < 1) : ¬ Tendsto x atTop (𝓝 0) := by
  have hstep : ∀ t, x t < x (t + 1) := by
    intro t
    have hx := (hdom t).1
    have hd := (hdom t).2
    have hpos : 0 < θ * x t ^ γ := mul_pos hθ (Real.rpow_pos_of_pos hx γ)
    rw [hrec t]
    unfold nextX
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hsm : StrictMono x := strictMono_nat_of_lt_succ hstep
  intro h
  have hge : ∀ t, x 0 ≤ x t := fun t => hsm.monotone (Nat.zero_le t)
  have := ge_of_tendsto h (Eventually.of_forall hge)
  linarith [(hdom 0).1]

end Cochrane.Monetarism.MoneyTargetingDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Unpleasant arithmetic and fiscal theory

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.6, pp. 456–457,
eqs. (19.39)–(19.40) (Sargent and Wallace (1981)). Perfect foresight, constant output `y` and
velocity `V`, constant discount factor `β`; present values are genuine `HasSum`s.

Notation: `N t = M_{t−1}`, money growth `g_t = M_t/M_{t−1}`, seigniorage
`σ_t = (M_t − M_{t−1})/P_t`.

## Main results

* (19.39): `seigniorage_eq` (`σ_t = (y/V)(1 − M_{t−1}/M_t)`), `inflation_eq_growth`
  (`P_t/P_{t−1} = M_t/M_{t−1}`), `seig_strictMono` (seigniorage increases with money growth),
  `seig_lt_bound`, `any_timing` (every seigniorage level below `y/V` is attained by some money
  growth).
* (19.40) with fixed surpluses: `seigniorage_pv` (the present value of seigniorage is fixed at
  `b_{−1} − ∑βʲs_j`), `unpleasant_shift` (less seigniorage now = exactly that much more present
  value later), `unpleasant_tradeoff` (some later date has more seigniorage),
  `unpleasant_money_growth` (lower money growth now forces higher money growth, hence higher
  inflation, later).
* Nominal vs real debt (p. 457): `nominal_debt_price` (`P_0 = B_{−1}/∑βʲs_j`, unique),
  `nominal_debt_price_anti` (a fall in the present value of surpluses raises `P_0` with no
  money at all), `disinflation_windfall` (a lower price level raises the real value of nominal
  debt, which surpluses must pay), `real_debt_no_price` (with real debt and no seigniorage the
  valuation equation restricts surpluses, not the price level).
-/

namespace Cochrane.Monetarism.UnpleasantArithmetic

open Filter Topology

/-- Cochrane (2023), (19.39)–(19.40), p. 456: seigniorage as a function of gross money growth
`g = M_t/M_{t−1}` under `M_tV = P_ty`: `σ(g) = (y/V)(1 − 1/g)`. -/
noncomputable def seig (y V g : ℝ) : ℝ := y / V * (1 - 1 / g)

/-- Cochrane (2023), eq. (19.39), p. 456: with `M_tV = P_ty`, seigniorage
`(M_t − M_{t−1})/P_t = (y/V)(1 − M_{t−1}/M_t)`. -/
theorem seigniorage_eq {Mt Mprev Pt y V : ℝ} (hM : 0 < Mt) (hV : 0 < V)
    (hP : 0 < Pt) (hq : Mt * V = Pt * y) : (Mt - Mprev) / Pt = seig y V (Mt / Mprev) := by
  unfold seig
  have hy : y = Mt * V / Pt := by field_simp; linarith
  rw [hy]
  field_simp

/-- Cochrane (2023), eq. (19.39), p. 456: with constant `y` and `V`, inflation equals money
growth, `P_t/P_{t−1} = M_t/M_{t−1}`. -/
theorem inflation_eq_growth {Mt Mprev Pt Pprev y V : ℝ} (hV : 0 < V) (hy : 0 < y)
    (hq : Mt * V = Pt * y) (hq' : Mprev * V = Pprev * y) (hMp : 0 < Mprev) :
    Pt / Pprev = Mt / Mprev := by
  have hPp : Pprev = Mprev * V / y := by field_simp; linarith
  have hPt : Pt = Mt * V / y := by field_simp; linarith
  rw [hPt, hPp]
  field_simp

/-- Cochrane (2023), p. 456 ("A monetary tightening can reduce current inflation by slowing
money growth"): seigniorage is strictly increasing in money growth on `(0, ∞)`. -/
theorem seig_strictMono {y V : ℝ} (hy : 0 < y) (hV : 0 < V) :
    StrictMonoOn (seig y V) (Set.Ioi 0) := by
  intro g hg g' hg' h
  have hg0 : (0 : ℝ) < g := hg
  unfold seig
  have : 1 / g' < 1 / g := one_div_lt_one_div_of_lt hg0 h
  have hc : 0 < y / V := div_pos hy hV
  nlinarith

/-- Cochrane (2023), p. 456: seigniorage is bounded by `y/V` (all money printed is at most the
whole money stock). -/
theorem seig_lt_bound {y V g : ℝ} (hy : 0 < y) (hV : 0 < V) (hg : 0 < g) : seig y V g < y / V := by
  unfold seig
  have : 0 < 1 / g := by positivity
  have hc : 0 < y / V := div_pos hy hV
  nlinarith

/-- Cochrane (2023), p. 456 ("the central bank can still decide when it will print more
money"): every seigniorage level `σ < y/V` is produced by exactly the money growth
`g = 1/(1 − Vσ/y) > 0`. -/
theorem any_timing {y V σ : ℝ} (hy : 0 < y) (hV : 0 < V) (hσ : σ < y / V) :
    ∃ g, 0 < g ∧ seig y V g = σ := by
  have hd : 0 < 1 - V * σ / y := by
    have : V * σ < y := by rwa [lt_div_iff₀ hV, mul_comm] at hσ
    have : V * σ / y < 1 := by rwa [div_lt_one hy]
    linarith
  refine ⟨1 / (1 - V * σ / y), by positivity, ?_⟩
  unfold seig
  field_simp
  ring

/-- Cochrane (2023), eq. (19.40), p. 456 ("the present value of seigniorage revenue counts"):
with fixed surpluses, `b_{−1} = ∑βʲ(s_j + σ_j)` fixes the present value of seigniorage at
`b_{−1} − ∑βʲs_j`. -/
theorem seigniorage_pv {β b S : ℝ} {s σ : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + σ j)) b) : HasSum (fun j => β ^ j * σ j) (b - S) := by
  have := hb.sub hs
  refine this.congr_fun fun j => ?_
  ring

/-- Cochrane (2023), p. 456 ("without a change in surpluses, the central bank will have to raise
later money growth … to preserve the present value of seigniorage revenue"): two seigniorage
paths consistent with (19.40) for the same `b_{−1}` and surpluses differ after date 0 in present
value by exactly the date-0 difference. -/
theorem unpleasant_shift {β b S : ℝ} {s σ σ' : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + σ j)) b)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b) :
    ∑' j, β ^ (j + 1) * σ' (j + 1) - ∑' j, β ^ (j + 1) * σ (j + 1) = σ 0 - σ' 0 := by
  have h1 := seigniorage_pv hs hb
  have h2 := seigniorage_pv hs hb'
  have e1 := h1.summable.tsum_eq_zero_add
  have e2 := h2.summable.tsum_eq_zero_add
  rw [h1.tsum_eq] at e1
  rw [h2.tsum_eq] at e2
  simp only [pow_zero, one_mul] at e1 e2
  linarith

/-- Cochrane (2023), p. 456 ("lowering money growth now forces higher money growth later"): if
date-0 seigniorage is lower, `σ'_0 < σ_0`, then seigniorage is higher at some later date. -/
theorem unpleasant_tradeoff {β b S : ℝ} (hβ : 0 < β) {s σ σ' : ℕ → ℝ}
    (hs : HasSum (fun j => β ^ j * s j) S) (hb : HasSum (fun j => β ^ j * (s j + σ j)) b)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b) (h0 : σ' 0 < σ 0) :
    ∃ j, 0 < j ∧ σ j < σ' j := by
  by_contra hcon
  push Not at hcon
  have h1 := seigniorage_pv hs hb
  have h2 := seigniorage_pv hs hb'
  have hle : (fun j => β ^ j * σ' j) ≤ fun j => β ^ j * σ j := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [pow_zero, one_mul]; exact h0.le
    · exact mul_le_mul_of_nonneg_left (hcon j hj) (pow_nonneg hβ.le j)
  have hlt : (fun j => β ^ j * σ' j) 0 < (fun j => β ^ j * σ j) 0 := by
    simp only [pow_zero, one_mul]; exact h0
  have := hasSum_lt hle hlt h2 h1
  linarith

/-- Cochrane (2023), p. 456, in money growth: if date-0 money growth is lower, `g'_0 < g_0`,
the seigniorage `σ = σ(g)` of (19.39) is lower at date 0, so money growth — and by
`inflation_eq_growth`, inflation — must be higher at some later date. -/
theorem unpleasant_money_growth {β b S y V : ℝ} (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V)
    {s g g' : ℕ → ℝ} (hg : ∀ j, 0 < g j) (hg' : ∀ j, 0 < g' j)
    (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + seig y V (g j))) b)
    (hb' : HasSum (fun j => β ^ j * (s j + seig y V (g' j))) b) (h0 : g' 0 < g 0) :
    ∃ j, 0 < j ∧ g j < g' j := by
  have hσ0 : seig y V (g' 0) < seig y V (g 0) := seig_strictMono hy hV (hg' 0) (hg 0) h0
  obtain ⟨j, hj, hlt⟩ := unpleasant_tradeoff hβ hs hb hb' hσ0
  refine ⟨j, hj, ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with h | h
  · exact absurd hlt (not_lt.mpr (seig_strictMono hy hV (hg' j) (hg j) h).le)
  · rw [h] at hlt
    exact lt_irrefl _ hlt

/-- Cochrane (2023), p. 457 ("the left-hand side in fiscal theory may be the real value of
nominal debt `B_{t−1}/P_t`"): with nominal debt `B_{−1} > 0`, no money (`M = 0`) and present
value of surpluses `S > 0`, the valuation equation has exactly one positive price level,
`P_0 = B_{−1}/S`. -/
theorem nominal_debt_price {B S : ℝ} (hB : 0 < B) (hS : 0 < S) :
    ∃! P, 0 < P ∧ B / P = S := by
  refine ⟨B / S, ⟨div_pos hB hS, by field_simp⟩, fun P hP => ?_⟩
  have := hP.1
  rw [eq_div_iff hS.ne', ← hP.2]
  field_simp

/-- Cochrane (2023), p. 457 ("a fall in the present value of surpluses `{s_{t+j}}` can generate a
higher price level `P_t` even with no money demand or seigniorage whatsoever"): `S ↦ B/S` is
strictly decreasing on `(0, ∞)`. -/
theorem nominal_debt_price_anti {B : ℝ} (hB : 0 < B) : StrictAntiOn (fun S => B / S) (Set.Ioi 0) :=
  fun _ hS _ _ h => div_lt_div_of_pos_left hB hS h

/-- Cochrane (2023), p. 457 ("to achieve a monetary tightening that lowers inflation,
governments must finance a real windfall to the holders of outstanding nominal bonds"): the real
value `B/P` of nominal debt, which the present value of surpluses must equal, is strictly larger
at a lower price level. -/
theorem disinflation_windfall {B P P' : ℝ} (hB : 0 < B) (hP' : 0 < P') (h : P' < P) :
    B / P < B / P' :=
  div_lt_div_of_pos_left hB hP' h

/-- Cochrane (2023), p. 456 ("the value on the left-hand side of (19.40) is unaffected by the
price level"): with real debt `b_{−1}` and no money, the valuation equation `b_{−1} = S` places no
restriction on the price level: if it holds, every positive `P_0` is consistent with it, and if
it fails no price level restores it. -/
theorem real_debt_no_price {b S : ℝ} :
    ((∃ P : ℝ, 0 < P ∧ b = S) ↔ b = S) ∧ (b = S → ∀ P : ℝ, 0 < P → b = S) := by
  exact ⟨⟨fun ⟨_, _, h⟩ => h, fun h => ⟨1, one_pos, h⟩⟩, fun h _ _ => h⟩

end Cochrane.Monetarism.UnpleasantArithmetic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Seigniorage, hyperinflation and monetary history

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.7 (pp. 457–458,
eq. (19.41)) and §19.8 (pp. 459–464), with the precise claim V2 of Chapter 11 (p. 317).
Steady states in continuous time are deterministic exponential paths with exact derivatives.

## Main results

* Steady-state seigniorage: `steady_seigniorage` (`−s/y = (1/(Py))dM/dt = (π + g)/V(r + π)`),
  `revenue`, `revenue_hasDerivAt`, `revenue_elasticity`
  (`d log(−s)/d log π = π/(π + g) − d log V/d log π`), `money_demand_elasticity`,
  `revenue_foc_iff` (the revenue maximum is where the velocity elasticity equals `π/(π + g)`),
  `e16_unit_iff` (survey E16: that is one only when `g = 0`), `revenue_deriv_pos_iff`,
  `laffer_decreasing` (past the point where the velocity elasticity exceeds `π/(π + g)`, more
  inflation yields less revenue).
* The Cagan example `V = e^{a(r+π)}`, `g = 0`: `cagRev`, `cagan_velocity_elasticity`
  (`= aπ`), `cagan_revenue_le` and `cagan_revenue_lt` (unique global maximum at `π = 1/a`),
  `cagan_example_two` (`a = 2` peaks at `π = 0.5`), `cagan_revenue_tendsto_zero`,
  `cagRev_strictMonoOn`, `cagRev_strictAntiOn`, `no_steady_state_above_max` (asking for more
  than the maximum leaves no steady state), `two_steady_states` (below the maximum there is one
  steady state on each side of the peak).
* Ch11 V2 (p. 317): `v2_price_level` (with `P_0 = D/(S + PV seigniorage)`), `v2_cagan` (raising
  money growth lowers `P_0` below the Laffer peak and raises it beyond).
* §19.8 Baumol–Tobin (p. 460): `btCost`, `bt_min` (square-root rule `M = √(A/i)` uniquely
  minimises `iM + A/M`), `bt_interest_elasticity` (`−1/2`), `bt_income_elasticity` (`1/2`),
  `bt_lm_slope` (unit LM slope); `cia_income_elasticity` (cash in advance: unit income
  elasticity, zero interest elasticity).
* §19.8, p. 462, survey E23: `e23_real_loss` (a 40% price rise devalues nominal debt by
  `1 − 1/1.4 = 2/7 ≈ 29%`, not 40%).
-/

namespace Cochrane.Monetarism.Seigniorage

open Filter Topology

/-! ### §19.7: steady-state seigniorage -/

/-- Cochrane (2023), eq. (19.41) and p. 458: in a steady state with `M_t = M_0e^{(π+g)t}`,
`P_t = P_0e^{πt}`, `y_t = y_0e^{gt}` and constant velocity `V = V(r + π)` with
`M_0V = P_0y_0`, money demand holds at every date, `dM/dt = (π + g)M_t`, and seigniorage as a
share of output is `(1/(P_ty_t))dM/dt = (π + g)/V`. -/
theorem steady_seigniorage {M0 P0 y0 π g V : ℝ} (hP0 : 0 < P0) (hy0 : 0 < y0) (hV : 0 < V)
    (hq : M0 * V = P0 * y0) (t : ℝ) :
    HasDerivAt (fun τ => M0 * Real.exp ((π + g) * τ))
        (M0 * Real.exp ((π + g) * t) * (π + g)) t ∧
      M0 * Real.exp ((π + g) * t) * V = P0 * Real.exp (π * t) * (y0 * Real.exp (g * t)) ∧
      1 / (P0 * Real.exp (π * t) * (y0 * Real.exp (g * t))) *
        (M0 * Real.exp ((π + g) * t) * (π + g)) = (π + g) / V := by
  have he : Real.exp ((π + g) * t) = Real.exp (π * t) * Real.exp (g * t) := by
    rw [← Real.exp_add]; ring_nf
  have hd : HasDerivAt (fun τ => M0 * Real.exp ((π + g) * τ))
      (M0 * (Real.exp ((π + g) * t) * (π + g))) t := by
    have h1 : HasDerivAt (fun τ => (π + g) * τ) (π + g) t := by
      simpa using (hasDerivAt_id t).const_mul (π + g)
    exact h1.exp.const_mul M0
  refine ⟨by rw [← mul_assoc] at hd; exact hd, ?_, ?_⟩
  · rw [he]
    have : M0 * V = P0 * y0 := hq
    linear_combination (Real.exp (π * t) * Real.exp (g * t)) * this
  · rw [he]
    have h1 := Real.exp_pos (π * t)
    have h2 := Real.exp_pos (g * t)
    have hM0 : M0 = P0 * y0 / V := by field_simp; linarith
    rw [hM0]
    field_simp

/-- Cochrane (2023), p. 458: steady-state seigniorage revenue as a share of output,
`R(π) = (π + g)/V(r + π)`. -/
noncomputable def revenue (V : ℝ → ℝ) (r g π : ℝ) : ℝ := (π + g) / V (r + π)

/-- Cochrane (2023), p. 458: the derivative of revenue in inflation,
`R'(π) = (V − (π + g)V')/V²`. -/
theorem revenue_hasDerivAt {V : ℝ → ℝ} {V' r g π : ℝ} (hV : HasDerivAt V V' (r + π))
    (hV0 : V (r + π) ≠ 0) :
    HasDerivAt (revenue V r g) ((V (r + π) - (π + g) * V') / V (r + π) ^ 2) π := by
  have hn : HasDerivAt (fun x => x + g) 1 π := by simpa using (hasDerivAt_id π).add_const g
  have hd : HasDerivAt (fun x => V (r + x)) V' π := HasDerivAt.comp_const_add r π hV
  have h := hn.div hd hV0
  have e : revenue V r g = (fun x => x + g) / fun x => V (r + x) := by
    funext x
    simp [revenue]
  rw [e]
  convert h using 1
  ring

/-- Cochrane (2023), p. 458: `d log(−s)/d log π = π/(π + g) − d log V/d log π`, i.e.
`πR'(π)/R(π) = π/(π + g) − πV'/V`. -/
theorem revenue_elasticity {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : V (r + π) ≠ 0)
    (hpg : π + g ≠ 0) :
    π * ((V (r + π) - (π + g) * V') / V (r + π) ^ 2) / revenue V r g π =
      π / (π + g) - π * V' / V (r + π) := by
  unfold revenue
  field_simp

/-- Cochrane (2023), p. 458 (`d log V/d log π = −d log(M/Py)/d log π`): the elasticity of money
demand `M/(Py) = 1/V` is minus the elasticity of velocity. -/
theorem money_demand_elasticity {V : ℝ → ℝ} {V' r π : ℝ} (hV : HasDerivAt V V' (r + π))
    (hV0 : V (r + π) ≠ 0) :
    HasDerivAt (fun x => 1 / V (r + x)) (-V' / V (r + π) ^ 2) π ∧
      π * (-V' / V (r + π) ^ 2) / (1 / V (r + π)) = -(π * V' / V (r + π)) := by
  have hd : HasDerivAt (fun x => V (r + x)) V' π := HasDerivAt.comp_const_add r π hV
  refine ⟨?_, by field_simp⟩
  have h := hd.inv hV0
  have e : (fun x => 1 / V (r + x)) = fun x => (V (r + x))⁻¹ := by
    funext x
    simp
  rw [e]
  convert h using 1

/-- Cochrane (2023), p. 458 ("Maximum revenue occurs where the elasticity of velocity is
roughly one"): for `π ≠ 0`, `π + g ≠ 0`, `V ≠ 0`, `R'(π) = 0` iff the velocity elasticity
`πV'/V` equals `π/(π + g)`. -/
theorem revenue_foc_iff {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : V (r + π) ≠ 0) (hπ : π ≠ 0)
    (hpg : π + g ≠ 0) :
    (V (r + π) - (π + g) * V') / V (r + π) ^ 2 = 0 ↔ π * V' / V (r + π) = π / (π + g) := by
  rw [div_eq_zero_iff, div_eq_div_iff hV0 hpg]
  constructor
  · rintro (h | h)
    · linear_combination (-π) * h
    · exact absurd h (pow_ne_zero 2 hV0)
  · intro h
    left
    have : π * (V' * (π + g) - V (r + π)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hπ
    · linarith

/-- Cochrane (2023), p. 458, survey E16: the revenue-maximising velocity elasticity
`π/(π + g)` equals one only when output does not grow (`g = 0`), hence "roughly one". -/
theorem e16_unit_iff {π g : ℝ} (hpg : π + g ≠ 0) : π / (π + g) = 1 ↔ g = 0 := by
  rw [div_eq_one_iff_eq hpg]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 458 ("If the rise in velocity is larger than the rise in inflation,
more inflation leads to less revenue"): for `π > 0`, `π + g > 0`, `V > 0`, revenue rises with
inflation iff the velocity elasticity is below `π/(π + g)`. -/
theorem revenue_deriv_pos_iff {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : 0 < V (r + π)) (hπ : 0 < π)
    (hpg : 0 < π + g) :
    0 < (V (r + π) - (π + g) * V') / V (r + π) ^ 2 ↔ π * V' / V (r + π) < π / (π + g) := by
  rw [div_pos_iff_of_pos_right (by positivity), div_lt_div_iff₀ hV0 hpg]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Cochrane (2023), pp. 457–458 ("Past a unit-elasticity point, printing more money produces
less seigniorage revenue … Seigniorage has a Laffer limit"): if from `π*` on velocity is
differentiable and positive, `π > 0`, `π + g > 0`, and the velocity elasticity exceeds
`π/(π + g)`, revenue is strictly decreasing on `[π*, ∞)`. -/
theorem laffer_decreasing {V V' : ℝ → ℝ} {r g ps : ℝ} (hps : 0 < ps) (hpg : 0 < ps + g)
    (hV : ∀ π, ps ≤ π → HasDerivAt V (V' (r + π)) (r + π) ∧ 0 < V (r + π))
    (hel : ∀ π, ps ≤ π → π / (π + g) < π * V' (r + π) / V (r + π)) :
    StrictAntiOn (revenue V r g) (Set.Ici ps) := by
  have hd : ∀ π, ps ≤ π → HasDerivAt (revenue V r g)
      ((V (r + π) - (π + g) * V' (r + π)) / V (r + π) ^ 2) π := fun π h =>
    revenue_hasDerivAt (hV π h).1 (hV π h).2.ne'
  refine strictAntiOn_of_deriv_neg (convex_Ici ps)
    (fun π h => (hd π h).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Ici] at h
  have h' : ps ≤ π := le_of_lt h
  rw [(hd π h').deriv]
  have hn := (revenue_deriv_pos_iff (V' := V' (r + π)) (g := g) (hV π h').2 (by linarith)
    (by linarith)).not
  have hne : (V (r + π) - (π + g) * V' (r + π)) / V (r + π) ^ 2 ≠ 0 := by
    intro h0
    have := (revenue_foc_iff (V' := V' (r + π)) (g := g) (hV π h').2.ne' (by linarith)
      (by linarith)).mp h0
    linarith [hel π h']
  push Not at hn
  exact lt_of_le_of_ne (hn.mpr (hel π h').le) hne

/-! ### The Cagan example `V = e^{a(r+π)}`, `g = 0` -/

/-- Cochrane (2023), p. 458 (Cagan example, survey item): revenue `π/e^{a(r+π)}`. -/
noncomputable def cagRev (a r π : ℝ) : ℝ := π / Real.exp (a * (r + π))

/-- Cochrane (2023), p. 458: `cagRev` is `revenue` with `V(x) = e^{ax}` and `g = 0`. -/
theorem cagRev_eq (a r π : ℝ) : cagRev a r π = revenue (fun x => Real.exp (a * x)) r 0 π := by
  simp [cagRev, revenue]

/-- Cochrane (2023), p. 458: for `V = e^{ax}` the elasticity of velocity is
`πV'(r + π)/V(r + π) = aπ`, so the first-order condition is `aπ = 1`. -/
theorem cagan_velocity_elasticity (a r π : ℝ) :
    HasDerivAt (fun x => Real.exp (a * x)) (a * Real.exp (a * (r + π))) (r + π) ∧
      π * (a * Real.exp (a * (r + π))) / Real.exp (a * (r + π)) = a * π := by
  refine ⟨?_, by field_simp⟩
  have h := ((hasDerivAt_id (r + π)).const_mul a).exp
  simpa [mul_comm] using h

/-- Cochrane (2023), p. 458 (Cagan example): the revenue is at most its value at `π = 1/a`. -/
theorem cagan_revenue_le {a : ℝ} (ha : 0 < a) (r π : ℝ) : cagRev a r π ≤ cagRev a r (1 / a) := by
  unfold cagRev
  rw [div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)]
  have e1 : Real.exp (a * (r + 1 / a)) = Real.exp (a * r) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; field_simp
  have e2 : Real.exp (a * (r + π)) = Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have h := Real.add_one_le_exp (a * π - 1)
  have hr := Real.exp_pos (a * r)
  have he := Real.exp_pos 1
  have key : a * π ≤ Real.exp (a * π - 1) := by linarith
  have : π ≤ 1 / a * Real.exp (a * π - 1) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
    linarith
  calc π * (Real.exp (a * r) * Real.exp 1) ≤
      1 / a * Real.exp (a * π - 1) * (Real.exp (a * r) * Real.exp 1) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 1 / a * (Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1)) := by ring

/-- Cochrane (2023), p. 458 (Cagan example): the maximum at `π = 1/a` is strict — every other
inflation rate yields strictly less revenue. -/
theorem cagan_revenue_lt {a : ℝ} (ha : 0 < a) (r : ℝ) {π : ℝ} (hπ : π ≠ 1 / a) :
    cagRev a r π < cagRev a r (1 / a) := by
  unfold cagRev
  rw [div_lt_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)]
  have e1 : Real.exp (a * (r + 1 / a)) = Real.exp (a * r) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; field_simp
  have e2 : Real.exp (a * (r + π)) = Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hne : a * π - 1 ≠ 0 := by
    intro h
    apply hπ
    field_simp
    linarith
  have h := Real.add_one_lt_exp hne
  have hr := Real.exp_pos (a * r)
  have he := Real.exp_pos 1
  have : π < 1 / a * Real.exp (a * π - 1) := by
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ ha]
    linarith
  calc π * (Real.exp (a * r) * Real.exp 1) <
      1 / a * Real.exp (a * π - 1) * (Real.exp (a * r) * Real.exp 1) :=
        mul_lt_mul_of_pos_right this (by positivity)
    _ = 1 / a * (Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1)) := by ring

/-- Cochrane (2023), p. 458 (survey numerical check: "argmax 0.5 for `a = 2`"): with `a = 2`
revenue peaks at `π = 1/2`. -/
theorem cagan_example_two (r π : ℝ) (hπ : π ≠ 1 / 2) : cagRev 2 r π < cagRev 2 r (1 / 2) :=
  cagan_revenue_lt (by norm_num) r hπ

/-- Cochrane (2023), p. 458 (Cagan example): revenue vanishes as inflation goes to infinity. -/
theorem cagan_revenue_tendsto_zero {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Tendsto (cagRev a r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun π : ℝ => (a * π) ^ (1 : ℕ) * Real.exp (-(a * π))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop ha)
  have h2 := h1.const_mul (Real.exp (-(a * r)) / a)
  rw [mul_zero] at h2
  refine h2.congr fun π => ?_
  unfold cagRev
  rw [show a * (r + π) = a * r + a * π by ring, Real.exp_add, Real.exp_neg, Real.exp_neg]
  field_simp

/-- Cochrane (2023), p. 458 (Cagan example): the derivative of revenue,
`(1 − aπ)/e^{a(r+π)}`. -/
theorem cagRev_hasDerivAt (a r π : ℝ) :
    HasDerivAt (cagRev a r) ((1 - a * π) / Real.exp (a * (r + π))) π := by
  have he : HasDerivAt (fun x => Real.exp (a * (r + x))) (Real.exp (a * (r + π)) * a) π := by
    have h := (((hasDerivAt_id π).const_add r).const_mul a).exp
    simpa using h
  have h := (hasDerivAt_id' π).div he (Real.exp_pos _).ne'
  have e : cagRev a r = (fun x => x) / fun x => Real.exp (a * (r + x)) := by
    funext x
    simp [cagRev]
  rw [e]
  convert h using 1
  field_simp

/-- Cochrane (2023), p. 458 (Cagan example): revenue strictly increases with inflation up to
the peak `1/a`. -/
theorem cagRev_strictMonoOn {a : ℝ} (ha : 0 < a) (r : ℝ) :
    StrictMonoOn (cagRev a r) (Set.Icc 0 (1 / a)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / a))
    (fun π _ => (cagRev_hasDerivAt a r π).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Icc] at h
  rw [(cagRev_hasDerivAt a r π).deriv]
  have : a * π < 1 := by
    have := h.2
    rw [lt_div_iff₀ ha] at this
    linarith
  exact div_pos (by linarith) (Real.exp_pos _)

/-- Cochrane (2023), p. 458 (Cagan example): beyond the peak `1/a`, revenue strictly decreases
with inflation. -/
theorem cagRev_strictAntiOn {a : ℝ} (ha : 0 < a) (r : ℝ) :
    StrictAntiOn (cagRev a r) (Set.Ici (1 / a)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici (1 / a))
    (fun π _ => (cagRev_hasDerivAt a r π).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Ici] at h
  rw [(cagRev_hasDerivAt a r π).deriv]
  have : 1 < a * π := by
    have := Set.mem_Ioi.mp h
    rw [div_lt_iff₀ ha] at this
    linarith
  exact div_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

/-- Cochrane (2023), p. 458 ("When the government then tries to squeeze one more cent of revenue
from the inflation tax, inflation jumps to infinity"): a revenue requirement above the maximum
has no steady state. -/
theorem no_steady_state_above_max {a r ρ : ℝ} (ha : 0 < a) (hρ : cagRev a r (1 / a) < ρ) :
    ∀ π, cagRev a r π ≠ ρ := fun π h => by
  have := cagan_revenue_le ha r π
  linarith

/-- Cochrane (2023), pp. 457–458: every revenue requirement strictly between `0` and the
maximum has a steady state below the peak and another beyond it (the Laffer curve has two
sides). -/
theorem two_steady_states {a r ρ : ℝ} (ha : 0 < a) (hρ0 : 0 < ρ)
    (hρ : ρ < cagRev a r (1 / a)) :
    (∃ π1, 0 < π1 ∧ π1 < 1 / a ∧ cagRev a r π1 = ρ) ∧
      ∃ π2, 1 / a < π2 ∧ cagRev a r π2 = ρ := by
  have hcont : Continuous (cagRev a r) := by
    unfold cagRev
    exact continuous_id.div (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.add continuous_id))) fun _ => (Real.exp_pos _).ne'
  have h0 : cagRev a r 0 = 0 := by simp [cagRev]
  have ha' : (0 : ℝ) ≤ 1 / a := by positivity
  constructor
  · obtain ⟨π1, hπ1, hv⟩ := intermediate_value_Icc ha' hcont.continuousOn
      ⟨by rw [h0]; exact hρ0.le, hρ.le⟩
    refine ⟨π1, lt_of_le_of_ne hπ1.1 ?_, lt_of_le_of_ne hπ1.2 ?_, hv⟩
    · rintro rfl; rw [h0] at hv; linarith
    · rintro rfl; linarith
  · obtain ⟨N, hN, hN'⟩ := ((cagan_revenue_tendsto_zero ha r).eventually
      (gt_mem_nhds hρ0)).and (eventually_gt_atTop (1 / a)) |>.exists
    obtain ⟨π2, hπ2, hv⟩ := intermediate_value_Icc' hN'.le hcont.continuousOn
      ⟨hN.le, hρ.le⟩
    refine ⟨π2, lt_of_le_of_ne hπ2.1 ?_, hv⟩
    rintro rfl; linarith

/-! ### Chapter 11, V2: seigniorage and the initial price level -/

/-- Cochrane (2023), §11.2, p. 317 (V2: "raising `M` adds future seigniorage revenue, which
lowers the initial price level"): with `P_0 = D/(S + Σ)`, `D > 0`, the initial price level is
strictly decreasing in the present value `Σ` of seigniorage (where `S + Σ > 0`). -/
theorem v2_price_level {D S : ℝ} (hD : 0 < D) {S1 S2 : ℝ} (h1 : 0 < S + S1) (h : S1 < S2) :
    D / (S + S2) < D / (S + S1) :=
  div_lt_div_of_pos_left hD h1 (by linarith)

/-- Cochrane (2023), §11.2, p. 317 (V2: "Once past the hyperinflationary point on the
inflation-tax Laffer curve, raising `M` lowers seigniorage revenue and creates both current and
future inflation"): in the Cagan example with `P_0 = D/(S + c·R(π))` (`c > 0` the present-value
factor, `S > 0`), raising steady money growth lowers `P_0` below the peak `1/a` and raises it
beyond. -/
theorem v2_cagan {a r D S c : ℝ} (ha : 0 < a) (hD : 0 < D) (hS : 0 < S) (hc : 0 < c) :
    (∀ π1 π2, 0 ≤ π1 → π1 < π2 → π2 ≤ 1 / a →
      D / (S + c * cagRev a r π2) < D / (S + c * cagRev a r π1)) ∧
    (∀ π1 π2, 1 / a ≤ π1 → π1 < π2 →
      D / (S + c * cagRev a r π1) < D / (S + c * cagRev a r π2)) := by
  have hnn : ∀ π, 0 ≤ π → 0 ≤ cagRev a r π := fun π h => div_nonneg h (Real.exp_pos _).le
  constructor
  · intro π1 π2 h1 h12 h2
    have := cagRev_strictMonoOn ha r ⟨h1, by linarith⟩ ⟨by linarith, h2⟩ h12
    exact v2_price_level hD (by nlinarith [hnn π1 h1]) (by nlinarith)
  · intro π1 π2 h1 h12
    have := cagRev_strictAntiOn ha r (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (by linarith)) h12
    have h0 : 0 ≤ π2 := by linarith [show (0 : ℝ) ≤ 1 / a by positivity]
    exact v2_price_level hD (by nlinarith [hnn π2 h0]) (by nlinarith)

/-! ### §19.8: Baumol–Tobin and cash in advance -/

/-- Cochrane (2023), §19.8, p. 460 (Allais–Baumol–Tobin inventory model): holding average cash
`M` costs forgone interest `iM` plus trips to the bank `A/M` (`A = bPy/2`). -/
noncomputable def btCost (i A M : ℝ) : ℝ := i * M + A / M

/-- Cochrane (2023), §19.8, p. 460: for `i, A > 0` the square-root rule `M* = √(A/i)` is the
unique minimiser of `iM + A/M` over `M > 0`. -/
theorem bt_min {i A : ℝ} (hi : 0 < i) (hA : 0 < A) :
    0 < Real.sqrt (A / i) ∧ ∀ M, 0 < M → btCost i A (Real.sqrt (A / i)) ≤ btCost i A M ∧
      (btCost i A M = btCost i A (Real.sqrt (A / i)) ↔ M = Real.sqrt (A / i)) := by
  set s := Real.sqrt i with hs
  set q := Real.sqrt A with hq
  have hs0 : 0 < s := Real.sqrt_pos.mpr hi
  have hq0 : 0 < q := Real.sqrt_pos.mpr hA
  have hss : s ^ 2 = i := Real.sq_sqrt hi.le
  have hqq : q ^ 2 = A := Real.sq_sqrt hA.le
  have hM : Real.sqrt (A / i) = q / s := by rw [Real.sqrt_div hA.le]
  have key : ∀ M, 0 < M → btCost i A M - btCost i A (q / s) = (s * M - q) ^ 2 / M := by
    intro M hM0
    unfold btCost
    rw [← hss, ← hqq]
    field_simp
    ring
  rw [hM]
  refine ⟨div_pos hq0 hs0, fun M hM0 => ⟨?_, ?_⟩⟩
  · have := key M hM0
    have : 0 ≤ (s * M - q) ^ 2 / M := div_nonneg (sq_nonneg _) hM0.le
    linarith
  · constructor
    · intro h
      have := key M hM0
      rw [h, sub_self] at this
      have h2 : (s * M - q) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp this.symm with h3 | h3
        · exact h3
        · exact absurd h3 hM0.ne'
      have : s * M = q := by nlinarith [sq_nonneg (s * M - q)]
      field_simp
      linarith
    · rintro rfl
      rfl

/-- Cochrane (2023), §19.8, p. 460 ("This model produces an interest … elasticity that [is] a
half"): `log M* = log √(K/i)` has derivative `−1/2` in `log i`. -/
theorem bt_interest_elasticity {K : ℝ} (hK : 0 < K) (x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.sqrt (K / Real.exp z))) (-1 / 2) x := by
  have e : (fun z => Real.log (Real.sqrt (K / Real.exp z))) = fun z => (Real.log K - z) / 2 := by
    funext z
    rw [Real.log_sqrt (div_nonneg hK.le (Real.exp_pos z).le),
      Real.log_div hK.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  have h := ((hasDerivAt_id x).const_sub (Real.log K)).div_const 2
  simpa [neg_div] using h

/-- Cochrane (2023), §19.8, p. 460 ("… and income elasticity that are each a half"):
`log √(Ky)` has derivative `1/2` in `log y`. -/
theorem bt_income_elasticity {K : ℝ} (hK : 0 < K) (x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.sqrt (K * Real.exp z))) (1 / 2) x := by
  have e : (fun z => Real.log (Real.sqrt (K * Real.exp z))) = fun z => (Real.log K + z) / 2 := by
    funext z
    rw [Real.log_sqrt (mul_nonneg hK.le (Real.exp_pos z).le),
      Real.log_mul hK.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  have h := ((hasDerivAt_id x).const_add (Real.log K)).div_const 2
  simpa using h

/-- Cochrane (2023), §19.8, p. 460 ("the slope of the LM curve is the ratio of income to
interest elasticities of money demand … This model gives a unit slope"). -/
theorem bt_lm_slope : (1 / 2 : ℝ) / |(-1 / 2 : ℝ)| = 1 := by norm_num [abs_of_neg]

/-- Cochrane (2023), §19.8, p. 460 ("the simple cash in advance model is notable as a theory
with a unit income and zero interest elasticity"): with `M = Py/V`, `log M` has derivative `1`
in `log y`, and does not depend on the interest rate. -/
theorem cia_income_elasticity {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun z => Real.log (c * Real.exp z)) 1 x := by
  have e : (fun z => Real.log (c * Real.exp z)) = fun z => Real.log c + z := by
    funext z
    rw [Real.log_mul hc.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  simpa using (hasDerivAt_id x).const_add (Real.log c)

/-- Cochrane (2023), §19.8, p. 462, survey E23: "The resulting 40% cumulative price-level rise
… devalued WWII debt by 40%" — a 40% rise in the price level lowers the real value of nominal
debt by `1 − 1/1.4 = 2/7 ≈ 28.6%`, not 40%. -/
theorem e23_real_loss : (1 : ℝ) - 1 / (14 / 10) = 2 / 7 ∧ (2 / 7 : ℝ) ≠ 4 / 10 ∧
    |(2 / 7 : ℝ) - 286 / 1000| < 1 / 1000 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [abs_lt]
  constructor <;> norm_num

end Cochrane.Monetarism.Seigniorage

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pruning deflationary equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3
"Pruning multiple monetary equilibria", §3.1 (pp. 612–618), with the money-in-utility model of
§19.3 (eqs. (19.10), (19.12), (19.18)–(19.23), pp. 439–445). Perfect foresight throughout,
as in the book ("so that initial inflation is the only indeterminacy").

Real balances relative to output are `m_t = M_t/(P_t y)`; the power utility (19.20) gives
`u_m/u_c = θ m^{−γ}`. The (19.23) map in `x = 1/m` is the canonical `MoneyInUtility.nextX`;
`Links` proves that the paths, steady states, deflations and explosions here are those of
`MoneyInUtility` and `MoneyTargetingDynamics` read in `m = 1/x`.

## Main results

* `foc_power_iff`, `ratio_of_foc` (19.18)/(19.21) and the p. 612 display:
  `m_{t+1}/m_t = (1+δ)(1+µ)(1 − θ x_t^γ)` with `x = 1/m = P y/M`; `eq1923_iff` is (19.23)
  (the map is conjugate by `m ↦ 1/m` to the canonical `MoneyInUtility.nextX`);
  `ratio_strictAntiOn`, `ratio_tendsto` give "↗ (1+δ)(1+µ) as `x ↘ 0`".
* Steady state: `steady_exists_unique`.
* Deflationary paths (`m₀ > m̄`): `deflation_growth`, `deflation_tendsto_atTop`,
  `deflation_path_exists`.
* The transversality condition, survey error **E17**: along a deflationary path
  `β^{T+1}M_T/(P_{T+1}y)` tends to zero iff `µ < 0` (`tvc_tendsto_zero_iff`); at `µ = 0` it
  converges to a positive constant (`tvc_mu_zero`), for `µ > 0` it diverges (`tvc_mu_pos`).
  The book's text says the objection "only applies to … µ > 0" and that for "µ ≤ 0"
  deflationary equilibria survive: false at `µ = 0`. For `β < 1 + µ < 1` deflationary
  equilibria form a continuum (`deflation_continuum`); for `1 + µ ≤ β` there are none
  (`no_deflation_of_le_beta`), so "−δ < µ < 0" must be `−δ/(1+δ) < µ < 0`
  (`survival_threshold`).
* §3.1.1 (no debt, satiation): `deflation_at_satiation`, (3.1) `flow_nodebt_iff`, the
  telescoped present-value identities `pv_finite`, `pv_finite_telescoped`,
  `final_money_eq`, the growing terminal term `tvc_term_growth`, `pv_surplus_tendsto_bot`,
  `no_eqm_positive_growth`, `passive_requires_negative_growth`, `tvc_iff_money_vanishes`,
  `tvc_limit`, `tvc_iff_pv`, and the determinate price level
  `price_level_determined`, `no_price_level_of_nonpos_pv`.
* §3.1.2 (open-market operations): `omo_total_debt`, `omo_real_debt_const`, `omo_bonds`,
  `omo_bonds_eventually_neg`, `omo_explode`, `omo_tvc`,
  `omo_pv`.
* §3.1.3 (valued money): the last-period first-order condition `last_period_foc`, its
  sufficiency `last_period_foc_sufficient`, the power case `last_period_power_demand`; the
  separable comparative static `separable_money_demand_rises`; the iterated budget constraint
  with interest `iterated_budget`.
-/

namespace Cochrane.Monetarism.PruningDeflation

open Filter Topology

/-! ## Primitives: power money-in-utility (19.20) and the difference equation (19.21) -/

/-- Cochrane (2023), eq. (19.20), p. 443: the marginal utility of money `θ m^{−γ}`. -/
noncomputable def umPow (θ γ m : ℝ) : ℝ := θ * m ^ (-γ)

/-- Cochrane (2023), eq. (19.20), p. 443: the marginal utility of consumption `c^{−γ}`. -/
noncomputable def ucPow (γ c : ℝ) : ℝ := c ^ (-γ)

/-- Cochrane (2023), eqs. (19.18)–(19.21), p. 444: with power utility,
`u_m(M/P)/u_c(y) = θ (M/(P y))^{−γ}`. -/
theorem um_div_uc_pow {θ γ M P y : ℝ} (hM : 0 < M) (hP : 0 < P) (hy : 0 < y) :
    umPow θ γ (M / P) / ucPow γ y = θ * (M / (P * y)) ^ (-γ) := by
  unfold umPow ucPow
  have h1 : M / (P * y) = (M / P) / y := by field_simp
  rw [h1, Real.div_rpow (by positivity) hy.le]
  ring

/-- Cochrane (2023), eq. (19.18), p. 442, with power utility (19.21), p. 444: the
money-demand condition `u_m/u_c = 1 − β P_t/P_{t+1}` in the power case. -/
theorem foc_power_iff {β θ γ M P P' y : ℝ} (hM : 0 < M) (hP : 0 < P) (hy : 0 < y) :
    umPow θ γ (M / P) / ucPow γ y = 1 - β * P / P' ↔
      θ * (M / (P * y)) ^ (-γ) = 1 - β * P / P' := by
  rw [um_div_uc_pow hM hP hy]

/-- Cochrane (2023), Online Appendix p. 612: the gross growth of real balances
`(1+µ)/β · (1 − θ m^{−γ})`, i.e. `(1+δ)(1+µ)(1 − θ x^γ)` with `x = 1/m`. -/
noncomputable def ratioMap (β μ θ γ m : ℝ) : ℝ := (1 + μ) / β * (1 - θ * m ^ (-γ)) * m

/-- Cochrane (2023), Online Appendix p. 612, display: from (19.21) with `M_{t+1} = (1+µ)M_t`,
`m_{t+1} = (1+µ)/β · (1 − θ m_t^{−γ}) m_t`, where `m_t = M_t/(P_t y)`. -/
theorem ratio_of_foc {β μ θ γ y : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hM : ∀ t, 0 < M t) (hP : ∀ t, 0 < P t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ)
    (hfoc : θ * (M t / (P t * y)) ^ (-γ) = 1 - β * P t / P (t + 1)) :
    M (t + 1) / (P (t + 1) * y) = ratioMap β μ θ γ (M t / (P t * y)) := by
  unfold ratioMap
  rw [hfoc, hgrow]
  have := hM t; have := hP t; have := hP (t + 1)
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 612: `(1+µ)/β = (1+δ)(1+µ)` when `β = 1/(1+δ)`. -/
theorem growth_factor_eq {β δ μ : ℝ} (hδ : 0 < 1 + δ) (hβ : β = 1 / (1 + δ)) :
    (1 + μ) / β = (1 + δ) * (1 + μ) := by
  rw [hβ]; field_simp

/-- Cochrane (2023), Online Appendix p. 612, "as `P_t y/M_t ↘ 0`, `(M_{t+1}/P_{t+1}y)/(M_t/P_t y)`
`↗ (1+δ)(1+µ)`": the gross growth `(1+µ)/β · (1 − θ x^γ)` is strictly decreasing in `x > 0`. -/
theorem ratio_strictAntiOn {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) :
    StrictAntiOn (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  have h1 : a ^ γ < b ^ γ := Real.rpow_lt_rpow (le_of_lt ha) hab hγ
  have h2 : 0 < (1 + μ) / β := div_pos hμ hβ
  simp only
  nlinarith [mul_lt_mul_of_pos_left h1 hθ]

/-- Cochrane (2023), Online Appendix p. 612: the limit `(1+µ)/β · (1 − θ x^γ) → (1+µ)/β` as
`x → 0⁺`. -/
theorem ratio_tendsto {β μ θ γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) (𝓝[>] 0) (𝓝 ((1 + μ) / β)) := by
  have hc : ContinuousAt (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) 0 :=
    continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_const.mul (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le))))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa [Real.zero_rpow hγ.ne'] using h

/-- Cochrane (2023), eq. (19.23), p. 444 (and (3.3), p. 619): in `x = P y/M = 1/m` the
difference equation reads `x_{t+1} = x_t (1 − θ x̄^γ)/(1 − θ x_t^γ)` with
`θ x̄^γ = 1 − β/(1+µ)` (19.22), i.e. the real-balance map is conjugate by `m ↦ 1/m` to the
canonical (19.23) map `MoneyInUtility.nextX`. -/
theorem eq1923_iff {β μ θ γ m m' xbar : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m)
    (hden : θ * (1 / m) ^ γ ≠ 1) (hss : θ * xbar ^ γ = 1 - β / (1 + μ)) :
    m' = ratioMap β μ θ γ m ↔ 1 / m' = MoneyInUtility.nextX θ γ xbar (1 / m) := by
  unfold MoneyInUtility.nextX
  have hinv : m ^ (-γ) = (1 / m) ^ γ := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  unfold ratioMap
  rw [hinv, hss]
  have hd : 1 - θ * (1 / m) ^ γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hden)
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have hm' : m' ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      have : 1 / m * (1 - (1 - β / (1 + μ))) / (1 - θ * (1 / m) ^ γ) ≠ 0 := by
        have : (1 - (1 - β / (1 + μ))) = β / (1 + μ) := by ring
        rw [this]
        exact div_ne_zero (mul_ne_zero (by positivity) (by positivity)) hd
      exact this h.symm
    field_simp at h
    field_simp
    linarith

/-! ## Steady states -/

/-- Cochrane (2023), eq. (19.19)/(19.22), p. 444: for `m > 0`, `m` is a fixed point of the
real-balance map iff `θ m^{−γ} = 1 − β/(1+µ)`. -/
theorem fixed_iff {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m) :
    ratioMap β μ θ γ m = m ↔ θ * m ^ (-γ) = 1 - β / (1 + μ) := by
  unfold ratioMap
  constructor
  · intro h
    have h1 : (1 + μ) / β * (1 - θ * m ^ (-γ)) = 1 := by
      have := mul_right_cancel₀ hm.ne' (h.trans (one_mul m).symm)
      exact this
    field_simp at h1
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (19.22), p. 444: when `β < 1 + µ` there is exactly one positive
inflationary steady state `m̄ = (θ/(1 − β/(1+µ)))^{1/γ}`. -/
theorem steady_exists_unique {β μ θ γ : ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) : ∃! ms : ℝ, 0 < ms ∧ θ * ms ^ (-γ) = 1 - β / (1 + μ) := by
  have hμ : 0 < 1 + μ := by linarith
  have hk : 0 < 1 - β / (1 + μ) := by
    rw [sub_pos, div_lt_one hμ]; exact hμβ
  refine ⟨(θ / (1 - β / (1 + μ))) ^ (1 / γ), ⟨by positivity, ?_⟩, ?_⟩
  · rw [← Real.rpow_mul (by positivity), show 1 / γ * -γ = -1 by field_simp,
      Real.rpow_neg_one]
    field_simp
  · rintro y ⟨hy, hyss⟩
    have h1 : y ^ (-γ) = (1 - β / (1 + μ)) / θ := by
      rw [eq_div_iff hθ.ne']; linarith
    have h2 : y = ((1 - β / (1 + μ)) / θ) ^ (-γ)⁻¹ := by
      rw [← h1, Real.rpow_rpow_inv hy.le (by linarith)]
    rw [h2, show (-γ)⁻¹ = -(1 / γ) by field_simp, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), inv_div]

/-! ## Paths of real balances -/

/-- Cochrane (2023), Online Appendix p. 612: a perfect-foresight path of real balances
`m_t = M_t/(P_t y) > 0` obeying (19.21) with constant money growth. -/
def IsMPath (β μ θ γ : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ m (t + 1) = ratioMap β μ θ γ (m t)

/-- Cochrane (2023), Online Appendix p. 612: along a deflationary path (`m₀ > m̄`) real balances
grow at least geometrically, `m_t ≥ rᵗ m₀` with `r = (1+µ)/β (1 − θ m₀^{−γ}) > 1`. -/
theorem deflation_growth {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    1 < (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) ∧
      ∀ t, m 0 ≤ m t ∧ ((1 + μ) / β * (1 - θ * m 0 ^ (-γ))) ^ t * m 0 ≤ m t := by
  set r := (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) with hr
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hlt : m 0 ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms h0 (by linarith)
  have hr1 : 1 < r := by
    have h1 : 1 - θ * ms ^ (-γ) < 1 - θ * m 0 ^ (-γ) := by nlinarith
    have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
    rw [hr]; nlinarith
  refine ⟨hr1, ?_⟩
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    have hm0 : 0 < m 0 := lt_trans hms h0
    have hmn : 0 < m n := (hpath n).1
    have hle : m n ^ (-γ) ≤ m 0 ^ (-γ) := Real.rpow_le_rpow_of_nonpos hm0 ih.1 (by linarith)
    have hstep : r * m n ≤ m (n + 1) := by
      rw [(hpath n).2]; unfold ratioMap
      have : (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) ≤ (1 + μ) / β * (1 - θ * m n ^ (-γ)) := by
        apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith
      rw [hr]; nlinarith
    constructor
    · nlinarith
    · rw [pow_succ]; nlinarith [pow_pos (lt_trans zero_lt_one hr1) n]

/-- Cochrane (2023), §19.3.2, p. 444, and Online Appendix p. 612: along a deflationary path
real balances grow without bound (`P_t y/M_t ↘ 0`). -/
theorem deflation_tendsto_atTop {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) : Tendsto m atTop atTop := by
  obtain ⟨hr1, hg⟩ := deflation_growth hβ hμ hθ hγ hms hss hpath h0
  have hm0 : 0 < m 0 := lt_trans hms h0
  exact tendsto_atTop_mono (fun t => (hg t).2)
    ((tendsto_pow_atTop_atTop_of_one_lt hr1).atTop_mul_const hm0)

/-- Cochrane (2023), §19.3.2, Figure 19.1, p. 444: every initial `m₀ > m̄` starts a unique
perfect-foresight path, and it is deflationary (`m_t → ∞`). -/
theorem deflation_path_exists {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (h0 : ms < m0) :
    ∃! m : ℕ → ℝ, IsMPath β μ θ γ m ∧ m 0 = m0 ∧ Tendsto m atTop atTop := by
  set m : ℕ → ℝ := fun t => (ratioMap β μ θ γ)^[t] m0 with hmdef
  have hsucc : ∀ t, m (t + 1) = ratioMap β μ θ γ (m t) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have habove : ∀ t, ms < m t := by
    intro t
    induction t with
    | zero => simpa [hmdef] using h0
    | succ n ih =>
      rw [hsucc]
      have hlt : m n ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms ih (by linarith)
      have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
      unfold ratioMap
      have h4 := mul_lt_mul_of_pos_left hlt hθ
      have h3 : 1 < (1 + μ) / β * (1 - θ * m n ^ (-γ)) := by nlinarith
      nlinarith
  have hpath : IsMPath β μ θ γ m := fun t => ⟨lt_trans hms (habove t), hsucc t⟩
  refine ⟨m, ⟨hpath, rfl, deflation_tendsto_atTop hβ hμ hθ hγ hms hss hpath h0⟩, ?_⟩
  rintro m' ⟨hp', h0', -⟩
  funext t
  induction t with
  | zero => rw [h0']; rfl
  | succ n ih => rw [(hp' n).2, hsucc, ih]

/-! ## The transversality condition along deflations (E17) -/

/-- Cochrane (2023), Online Appendix p. 613: the transversality term
`β^{T+1} M_T/(P_{T+1} y) = β^{T+1} m_{T+1}/(1+µ)` (with `M_{T+1} = (1+µ)M_T`). -/
noncomputable def tvcTerm (β μ : ℝ) (m : ℕ → ℝ) (T : ℕ) : ℝ := β ^ (T + 1) * m (T + 1) / (1 + μ)

/-- Cochrane (2023), Online Appendix p. 613: the transversality term in levels,
`β^{T+1}M_T/(P_{T+1}y) = tvcTerm`, when `M_{T+1} = (1+µ)M_T`. -/
theorem tvcTerm_eq {β μ y : ℝ} {M P : ℕ → ℝ} (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hP : ∀ t, 0 < P t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (T : ℕ) :
    β ^ (T + 1) * M T / (P (T + 1) * y) =
      tvcTerm β μ (fun t => M t / (P t * y)) T := by
  unfold tvcTerm
  dsimp only
  rw [hgrow]
  have := hP (T + 1)
  field_simp

/-- A general lemma (not in the book): `exp(−a/(1−a₀)) ≤ 1 − a` for `0 ≤ a ≤ a₀ < 1`. -/
theorem exp_le_one_sub {a a0 : ℝ} (ha : 0 ≤ a) (haa : a ≤ a0) (ha0 : a0 < 1) :
    Real.exp (-(a / (1 - a0))) ≤ 1 - a := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : Real.exp (-(a / (1 - a0))) ≤ Real.exp (-(a / (1 - a))) := by
    apply Real.exp_le_exp.mpr
    have : a / (1 - a) ≤ a / (1 - a0) :=
      div_le_div_of_nonneg_left ha (by linarith) (by linarith)
    linarith
  have h3 : 1 / (1 - a) ≤ Real.exp (a / (1 - a)) := by
    have := Real.add_one_le_exp (a / (1 - a))
    have h4 : a / (1 - a) + 1 = 1 / (1 - a) := by field_simp; ring
    linarith
  have h5 : Real.exp (-(a / (1 - a))) ≤ 1 - a := by
    rw [Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_left h3 h1.le
    rw [mul_one_div_cancel h1.ne'] at this
    linarith
  linarith

/-- Cochrane (2023), Online Appendix p. 613: the scaled real balances `W_T = β^T m_T` obey
`W_{T+1} = (1+µ)(1 − θ m_T^{−γ}) W_T` along any path. -/
theorem scaled_succ {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hpath : IsMPath β μ θ γ m)
    (T : ℕ) : β ^ (T + 1) * m (T + 1) = (1 + μ) * (1 - θ * m T ^ (-γ)) * (β ^ T * m T) := by
  rw [(hpath T).2]; unfold ratioMap; rw [pow_succ]; field_simp

/-- Cochrane (2023), Online Appendix p. 613, "If money growth is negative … this subtlety
vanishes": for `−1 < µ < 0` the transversality term tends to zero along every path. -/
theorem tvc_tendsto_zero_of_neg {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hμ0 : μ < 0) (hθ : 0 < θ) (hpath : IsMPath β μ θ γ m) :
    Tendsto (tvcTerm β μ m) atTop (𝓝 0) := by
  have hW : ∀ T, 0 < β ^ T * m T ∧ β ^ T * m T ≤ (1 + μ) ^ T * m 0 := by
    intro T
    induction T with
    | zero => simp [(hpath 0).1]
    | succ n ih =>
      have hpos : 0 < β ^ (n + 1) * m (n + 1) := by have := (hpath (n + 1)).1; positivity
      refine ⟨hpos, ?_⟩
      rw [scaled_succ hβ hpath n]
      rw [scaled_succ hβ hpath n] at hpos
      have hfac : 0 < 1 - θ * m n ^ (-γ) := by
        by_contra hcon
        push Not at hcon
        have : (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hμ.le hcon) ih.1.le
        linarith
      have hle : 1 - θ * m n ^ (-γ) ≤ 1 := by
        have := Real.rpow_pos_of_pos (hpath n).1 (-γ); nlinarith
      rw [pow_succ]
      have h1 : (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) ≤ (1 + μ) * (β ^ n * m n) := by
        have := mul_le_mul_of_nonneg_right hle ih.1.le
        nlinarith
      nlinarith [ih.2]
  have hlim : Tendsto (fun T => (1 + μ) ^ (T + 1) * m 0 / (1 + μ)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hμ.le (by linarith)).comp
      (tendsto_add_atTop_nat 1)).mul_const (m 0)
    simpa using this.div_const (1 + μ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun T => ?_)
    (fun T => ?_)
  · unfold tvcTerm; exact div_nonneg (hW (T + 1)).1.le hμ.le
  · unfold tvcTerm; exact div_le_div_of_nonneg_right (hW (T + 1)).2 hμ.le

/-- Cochrane (2023), Online Appendix p. 613: along a deflationary path (`m₀ > m̄`) the scaled
balances satisfy `β^T m_T ≥ C (1+µ)^T` for a constant `C > 0` (the product
`∏(1 − θ m_s^{−γ})` stays bounded away from zero because `θ m_s^{−γ}` decays geometrically). -/
theorem scaled_lower_bound {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    ∃ C, 0 < C ∧ ∀ T, C * (1 + μ) ^ T ≤ β ^ T * m T := by
  obtain ⟨hr1, hg⟩ := deflation_growth hβ hμ hθ hγ hms hss hpath h0
  set r := (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) with hr
  have hm0 : 0 < m 0 := lt_trans hms h0
  set a0 := θ * m 0 ^ (-γ) with ha0
  set ρ := r ^ (-γ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by linarith) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hr1 (by linarith)
  have ha0pos : 0 < a0 := by positivity
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have ha01 : a0 < 1 := by
    have : 1 < (1 + μ) / β * (1 - a0) := hr1
    have : 0 < 1 - a0 := by
      by_contra h; push Not at h; nlinarith
    linarith
  -- geometric decay of `a_t = θ m_t^{−γ}`
  have hdecay : ∀ t, θ * m t ^ (-γ) ≤ a0 * ρ ^ t := by
    intro t
    have h1 : m t ^ (-γ) ≤ (r ^ t * m 0) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hg t).2 (by linarith)
    have h2 : (r ^ t * m 0) ^ (-γ) = ρ ^ t * m 0 ^ (-γ) := by
      rw [Real.mul_rpow (by positivity) hm0.le, ← Real.rpow_natCast_mul (by linarith),
        mul_comm (t : ℝ), Real.rpow_mul_natCast (by linarith)]
    rw [h2] at h1
    rw [ha0]
    nlinarith
  have hat : ∀ t, 0 ≤ θ * m t ^ (-γ) ∧ θ * m t ^ (-γ) ≤ a0 := by
    intro t
    refine ⟨by have := Real.rpow_pos_of_pos (hpath t).1 (-γ); positivity, ?_⟩
    have := hdecay t
    have : ρ ^ t ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    nlinarith
  set η := 1 - a0 with hη
  have hηpos : 0 < η := by linarith
  -- induction on the product bound
  have hind : ∀ T, m 0 * (1 + μ) ^ T *
      Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) ≤ β ^ T * m T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [scaled_succ hβ hpath n, Finset.sum_range_succ, add_div, neg_add, Real.exp_add,
        pow_succ]
      have he := exp_le_one_sub (hat n).1 (hat n).2 ha01
      have hpos : 0 ≤ m 0 * (1 + μ) ^ n *
          Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η)) := by positivity
      calc m 0 * ((1 + μ) ^ n * (1 + μ)) *
            (Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η)) *
              Real.exp (-(θ * m n ^ (-γ) / η)))
          = (1 + μ) * Real.exp (-(θ * m n ^ (-γ) / η)) * (m 0 * (1 + μ) ^ n *
              Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η))) := by ring
        _ ≤ (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left he hμ.le) ih hpos
          have : 0 ≤ 1 - θ * m n ^ (-γ) := by linarith [(hat n).2]
          positivity
  -- the sum is bounded
  have hsum : ∀ T, ∑ s ∈ Finset.range T, θ * m s ^ (-γ) ≤ a0 / (1 - ρ) := by
    intro T
    calc ∑ s ∈ Finset.range T, θ * m s ^ (-γ) ≤ ∑ s ∈ Finset.range T, a0 * ρ ^ s :=
          Finset.sum_le_sum fun s _ => hdecay s
      _ = a0 * ((1 - ρ ^ T) / (1 - ρ)) := by
          rw [← Finset.mul_sum, geom_sum_eq hρ1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
      _ ≤ a0 / (1 - ρ) := by
          rw [mul_div_assoc']
          apply div_le_div_of_nonneg_right _ (by linarith)
          have : 0 ≤ ρ ^ T := by positivity
          nlinarith
  refine ⟨m 0 * Real.exp (-(a0 / (1 - ρ) / η)), by positivity, fun T => ?_⟩
  have hexp : Real.exp (-(a0 / (1 - ρ) / η)) ≤
      Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) := by
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right (hsum T) hηpos.le
    linarith
  calc m 0 * Real.exp (-(a0 / (1 - ρ) / η)) * (1 + μ) ^ T
      = m 0 * (1 + μ) ^ T * Real.exp (-(a0 / (1 - ρ) / η)) := by ring
    _ ≤ m 0 * (1 + μ) ^ T * Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ β ^ T * m T := hind T

/-- Cochrane (2023), Online Appendix p. 613, "if µ ≥ 0, real money holdings violate the
condition `lim β^{T+1}M_{t+T}/(P_{t+T+1}y) ≠ 0`" (survey E17: `µ = 0` included). -/
theorem tvc_not_tendsto_zero {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 ≤ μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    ¬ Tendsto (tvcTerm β μ m) atTop (𝓝 0) := by
  have hμ : 0 < 1 + μ := by linarith
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ hμ hθ hγ hms hss hpath h0
  intro h
  have hev : ∀ T, C / (1 + μ) ≤ tvcTerm β μ m T := by
    intro T
    unfold tvcTerm
    apply div_le_div_of_nonneg_right _ hμ.le
    have := hlow (T + 1)
    have : 1 ≤ (1 + μ) ^ (T + 1) := one_le_pow₀ (by linarith)
    nlinarith
  have := ge_of_tendsto' h hev
  have : 0 < C / (1 + μ) := div_pos hC hμ
  linarith

/-- Cochrane (2023), Online Appendix pp. 612–613, survey error **E17** (corrected): along
a deflationary path (`m₀ > m̄`) with `β < 1 + µ`, the transversality term tends to zero if
and only if `µ < 0`. -/
theorem tvc_tendsto_zero_iff {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    Tendsto (tvcTerm β μ m) atTop (𝓝 0) ↔ μ < 0 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact tvc_not_tendsto_zero hβ hcon hθ hγ hms hss hpath h0 h
  · intro h
    exact tvc_tendsto_zero_of_neg hβ (by linarith) h hθ hpath

/-- Cochrane (2023), Online Appendix p. 613 (survey E17): at `µ = 0` the transversality term
converges to a strictly positive constant along every deflationary path, so the condition is
violated although money does not grow. -/
theorem tvc_mu_zero {β θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + 0))
    (hpath : IsMPath β 0 θ γ m) (h0 : ms < m 0) :
    ∃ L, 0 < L ∧ Tendsto (tvcTerm β 0 m) atTop (𝓝 L) := by
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ (by norm_num) hθ hγ hms hss hpath h0
  have hanti : Antitone (fun T => β ^ T * m T) := by
    refine antitone_nat_of_succ_le fun n => ?_
    rw [scaled_succ hβ hpath n]
    have hp := Real.rpow_pos_of_pos (hpath n).1 (-γ)
    have : 0 < β ^ n * m n := by have := (hpath n).1; positivity
    have h := mul_pos (mul_pos hθ hp) this
    nlinarith
  have hbdd : BddBelow (Set.range fun T => β ^ T * m T) :=
    ⟨C, by rintro _ ⟨T, rfl⟩; simpa using hlow T⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ T, β ^ T * m T, ?_, ?_⟩
  · exact lt_of_lt_of_le hC (le_ciInf fun T => by simpa using hlow T)
  · have := hlim.comp (tendsto_add_atTop_nat 1)
    unfold tvcTerm
    simpa [Function.comp_def] using this

/-- Cochrane (2023), Online Appendix p. 613: for `µ > 0` the transversality term diverges to
`+∞` along every deflationary path ("real money holdings rise faster than the real rate"). -/
theorem tvc_mu_pos {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 < μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    Tendsto (tvcTerm β μ m) atTop atTop := by
  have hμ : 0 < 1 + μ := by linarith
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ hμ hθ hγ hms hss hpath h0
  have h1 : Tendsto (fun T => C * (1 + μ) ^ (T + 1) / (1 + μ)) atTop atTop :=
    (((tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).comp
      (tendsto_add_atTop_nat 1)).const_mul_atTop hC).atTop_div_const hμ
  exact tendsto_atTop_mono (fun T => div_le_div_of_nonneg_right (hlow (T + 1)) hμ.le) h1

/-- Cochrane (2023), Online Appendix p. 613, "If money growth is negative … we unequivocally
have multiple deflationary equilibria" (corrected range `β < 1 + µ < 1`): every `m₀ > m̄`
starts a deflationary path satisfying the transversality condition, and distinct `m₀` give
distinct paths — a continuum of equilibria. -/
theorem deflation_continuum {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ) (hμ1 : μ < 0)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) :
    ∃ path : ℝ → ℕ → ℝ, (∀ m0, ms < m0 → IsMPath β μ θ γ (path m0) ∧ path m0 0 = m0 ∧
      Tendsto (path m0) atTop atTop ∧ Tendsto (tvcTerm β μ (path m0)) atTop (𝓝 0)) ∧
      Set.InjOn path (Set.Ioi ms) := by
  have hμ : 0 < 1 + μ := by linarith
  have hex : ∀ m0 : ℝ, ∃ m : ℕ → ℝ, ms < m0 →
      IsMPath β μ θ γ m ∧ m 0 = m0 ∧ Tendsto m atTop atTop := by
    intro m0
    by_cases h : ms < m0
    · obtain ⟨m, hm, -⟩ := deflation_path_exists hβ hμ hθ hγ hms hss h
      exact ⟨m, fun _ => hm⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose path hpath using hex
  refine ⟨path, fun m0 h => ⟨(hpath m0 h).1, (hpath m0 h).2.1, (hpath m0 h).2.2,
    tvc_tendsto_zero_of_neg hβ hμ hμ1 hθ (hpath m0 h).1⟩, ?_⟩
  intro a ha b hb hab
  have h1 := (hpath a ha).2.1
  have h2 := (hpath b hb).2.1
  rw [← h1, ← h2, hab]

/-- Cochrane (2023), Online Appendix p. 613 and p. 617, "−δ < µ < 0" / "−δ ≤ µ < 0"
(corrected): when `1 + µ ≤ β` every path of real balances is strictly decreasing, so there is
no deflationary path at all. -/
theorem no_deflation_of_le_beta {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hμβ : 1 + μ ≤ β) (hθ : 0 < θ) (hpath : IsMPath β μ θ γ m) : StrictAnti m := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rw [(hpath n).2]
  unfold ratioMap
  have hp := Real.rpow_pos_of_pos (hpath n).1 (-γ)
  have hA : (1 + μ) / β ≤ 1 := (div_le_one hβ).mpr hμβ
  have hA0 : 0 < (1 + μ) / β := div_pos hμ hβ
  have hmn := (hpath n).1
  have hθp := mul_pos hθ hp
  have : (1 + μ) / β * (1 - θ * m n ^ (-γ)) < 1 := by nlinarith [mul_pos hA0 hθp]
  nlinarith

/-- Cochrane (2023), Online Appendix p. 613 (survey E17/E13): with `β = 1/(1+δ)`, the condition
for deflationary paths `β < 1 + µ` is `µ > −δ/(1+δ)`, not `µ > −δ`; e.g. `δ = 1`, `µ = −0.6`
satisfies `µ > −δ` but `1 + µ = 0.4 < β = 0.5`. -/
theorem survival_threshold {δ μ : ℝ} (hδ : 0 < 1 + δ) :
    1 / (1 + δ) < 1 + μ ↔ -δ / (1 + δ) < μ := by
  constructor
  · intro h
    rw [div_lt_iff₀ hδ]
    rw [div_lt_iff₀ hδ] at h
    nlinarith
  · intro h
    rw [div_lt_iff₀ hδ]
    rw [div_lt_iff₀ hδ] at h
    nlinarith

/-- Cochrane (2023), Online Appendix p. 613 (survey E17), numerical counterexample to
"−δ < µ < 0" sufficing: `δ = 1`, `µ = −0.6` has `−δ < µ < 0` but `1 + µ < 1/(1+δ)`. -/
theorem survival_counterexample :
    -(1 : ℝ) < -0.6 ∧ (-0.6 : ℝ) < 0 ∧ 1 + (-0.6 : ℝ) < 1 / (1 + 1) := by
  norm_num

/-! ## §3.1.1 No debt and satiation: "this is fiscal theory"

Index convention: `M 0 = M_{−1}` is initial money and `M (t + 1) = M_t` is money chosen at
date `t`; `P t = P_t`, `s t = s_t`. -/

/-- Cochrane (2023), Online Appendix p. 613 and §19.3.2, p. 443: with satiation (`u_m = 0`) the
money-demand condition (19.18) `u_m/u_c = 1 − βP_t/P_{t+1}` forces `P_{t+1} = βP_t`, and the
bond price `βP_t/P_{t+1} = 1/(1+i_t)` equals one (`i = 0`). -/
theorem deflation_at_satiation {β um uc P P' : ℝ} (hP' : 0 < P') (hum : um = 0)
    (hfoc : um / uc = 1 - β * P / P') : P' = β * P ∧ β * P / P' = 1 := by
  rw [hum, zero_div] at hfoc
  have h1 : β * P / P' = 1 := by linarith
  refine ⟨?_, h1⟩
  field_simp at h1
  linarith

/-- Cochrane (2023), eq. (3.1), p. 614: the household flow budget (19.10) with no debt and
`c_t = y`, `M_{t−1} + P_t(y − y) = M_t + P_ts_t`, is `(M_t − M_{t−1})/P_t = −s_t`. -/
theorem flow_nodebt_iff {Mprev Mt Pt y st : ℝ} (hP : 0 < Pt) :
    Mprev + Pt * (y - y) = Mt + Pt * st ↔ (Mt - Mprev) / Pt = -st := by
  rw [div_eq_iff hP.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 614: with `P_{t+1} = βP_t` the price level is `P_t = βᵗP_0`. -/
theorem price_geometric {β : ℝ} {P : ℕ → ℝ} (hP : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    P t = β ^ t * P 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [hP, ih, pow_succ]; ring

/-- Cochrane (2023), p. 614: under (3.1) and `P_{t+1} = βP_t`, each discounted surplus is minus
the money added, deflated by the initial price level: `β^j s_j = −(M_j − M_{j−1})/P_0`. -/
theorem discounted_surplus {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (j : ℕ) :
    β ^ j * s j = -((M (j + 1) - M j) / P 0) := by
  have h := hflow j
  rw [price_geometric hP j] at h
  have : s j = -((M (j + 1) - M j) / (β ^ j * P 0)) := by linarith
  rw [this]
  field_simp

/-- Cochrane (2023), eq. (19.12) at `i = 0`, p. 614, first display: under (3.1) and
`P_{t+1} = βP_t`, `M_{−1}/P_0 = ∑_{j≤T} βʲ s_j + β^{T+1} M_T/P_{T+1}` for every `T`. -/
theorem pv_finite {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1), β ^ j * s j + β ^ (T + 1) * M (T + 1) / P (T + 1) := by
  rw [Finset.sum_congr rfl fun j _ => discounted_surplus hβ hP0 hP hflow j, Finset.sum_neg_distrib,
    ← Finset.sum_div, Finset.sum_range_sub (fun j => M j), price_geometric hP (T + 1)]
  field_simp
  ring

/-- Cochrane (2023), p. 614, second and third displays: the same identity telescoped,
`M_{−1}/P_0 = ∑_{j≤T} −(M_j − M_{j−1})/P_0 + M_T/P_0` ("final money equals initial money plus
added money"), with `β^{T+1}M_T/P_{T+1} = M_T/P_0`. -/
theorem pv_finite_telescoped {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1), -((M (j + 1) - M j) / P 0) + M (T + 1) / P 0 ∧
      β ^ (T + 1) * M (T + 1) / P (T + 1) = M (T + 1) / P 0 := by
  constructor
  · rw [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_range_sub (fun j => M j)]
    ring
  · rw [price_geometric hP (T + 1)]
    field_simp

/-- Cochrane (2023), p. 614: "final money equals initial money plus added money",
`M_T = M_{−1} + ∑_{j≤T}(M_j − M_{j−1})`. -/
theorem final_money_eq (M : ℕ → ℝ) (T : ℕ) :
    M (T + 1) = M 0 + ∑ j ∈ Finset.range (T + 1), (M (j + 1) - M j) := by
  rw [Finset.sum_range_sub (fun j => M j)]
  ring

/-- Cochrane (2023), p. 614, "The final term grows at rate `(1+µ)^T`": with constant money
growth `M_t = (1+µ)M_{t−1}` and `P_{t+1} = βP_t`, `β^{T+1}M_T/P_{T+1} = (1+µ)^{T+1}M_{−1}/P_0`,
which diverges for `µ > 0`, `M_{−1} > 0`. -/
theorem tvc_term_growth {β μ : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hM : ∀ t, M (t + 1) = (1 + μ) * M t) :
    (∀ T, β ^ (T + 1) * M (T + 1) / P (T + 1) = (1 + μ) ^ (T + 1) * M 0 / P 0) ∧
      (0 < μ → 0 < M 0 →
        Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop atTop) := by
  have hMt : ∀ t, M t = (1 + μ) ^ t * M 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hM, ih, pow_succ]; ring
  have heq : ∀ T, β ^ (T + 1) * M (T + 1) / P (T + 1) = (1 + μ) ^ (T + 1) * M 0 / P 0 := by
    intro T
    rw [(pv_finite_telescoped (M := M) hβ hP0 hP T).2, hMt]
  refine ⟨heq, fun hμ hM0 => ?_⟩
  simp only [heq]
  exact (((tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).comp
    (tendsto_add_atTop_nat 1)).atTop_mul_const hM0).atTop_div_const hP0

/-- Cochrane (2023), p. 614, "The present value of surpluses explodes to negative infinity":
with helicopter money growth `µ > 0`, `M_{−1} > 0`, the partial sums `∑_{j≤T}βʲs_j → −∞`. -/
theorem pv_surplus_tendsto_bot {β μ : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hM : ∀ t, M (t + 1) = (1 + μ) * M t) (hμ : 0 < μ) (hM0 : 0 < M 0) :
    Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) atTop atBot := by
  have h := (tvc_term_growth hβ hP0 hP hM).2 hμ hM0
  have heq : (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) =
      fun T => M 0 / P 0 - β ^ (T + 1) * M (T + 1) / P (T + 1) := by
    funext T
    have := pv_finite hβ hP0 hP hflow T
    linarith
  rw [heq]
  exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp h)

/-- Cochrane (2023), p. 614, "there is no equilibrium initial price level, with perpetually
positive money growth, perpetually negative surpluses, and no liquidity value `u_m = 0`, whether
fiscal policy is active or passive": with `P_{t+1} = βP_t`, nondecreasing money and
`M_{−1} > 0`, the transversality condition `β^{T+1}M_T/P_{T+1} → 0` fails for every `P_0 > 0`. -/
theorem no_eqm_positive_growth {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hmono : Monotone M) (hM0 : 0 < M 0) :
    ¬ Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) := by
  intro h
  have hge : ∀ T, M 0 / P 0 ≤ β ^ (T + 1) * M (T + 1) / P (T + 1) := by
    intro T
    rw [(pv_finite_telescoped (M := M) hβ hP0 hP T).2]
    exact div_le_div_of_nonneg_right (hmono (Nat.zero_le _)) hP0.le
  have := ge_of_tendsto' h hge
  have : 0 < M 0 / P 0 := div_pos hM0 hP0
  linarith

/-- Cochrane (2023), p. 614, "a passive policy must have at some point positive surpluses …
we must in this model have a negative money growth rate `M_{t+1} − M_t < 0`": if the
transversality condition holds and `M_{−1} > 0`, some date has falling money and a positive
surplus. -/
theorem passive_requires_negative_growth {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hM0 : 0 < M 0) (htvc : Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0)) :
    ∃ t, M (t + 1) < M t ∧ 0 < s t := by
  by_contra hcon
  push Not at hcon
  have hmono : Monotone M := by
    refine monotone_nat_of_le_succ fun n => ?_
    by_contra h
    push Not at h
    have hPn : 0 < P n := by rw [price_geometric hP n]; positivity
    have hs : 0 < s n := by
      have := hflow n
      have : (M (n + 1) - M n) / P n < 0 := div_neg_of_neg_of_pos (by linarith) hPn
      linarith
    exact absurd hs (not_lt.mpr (hcon n h))
  exact no_eqm_positive_growth hβ hP0 hP hmono hM0 htvc

/-- Cochrane (2023), p. 615, "the nominal money supply is eventually constant or declining"
(made precise): with `P_{t+1} = βP_t` the transversality condition holds iff nominal money
converges to zero. (A money stock eventually constant at a positive level violates it.) -/
theorem tvc_iff_money_vanishes {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      Tendsto M atTop (𝓝 0) := by
  have heq : (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) = fun T => M (T + 1) / P 0 := by
    funext T; exact (pv_finite_telescoped (M := M) hβ hP0 hP T).2
  rw [heq, ← tendsto_add_atTop_iff_nat 1 (f := M)]
  constructor
  · intro h
    have := h.mul_const (P 0)
    simp only [zero_mul] at this
    refine this.congr fun T => ?_
    field_simp
  · intro h
    simpa using h.div_const (P 0)

/-- Cochrane (2023), eq. (19.12), p. 614: under (3.1) and `P_{t+1} = βP_t`, if the discounted
surpluses are summable, the transversality term converges to `M_{−1}/P_0 − ∑ βʲs_j`. -/
theorem tvc_limit {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hsum : Summable fun j => β ^ j * s j) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop
      (𝓝 (M 0 / P 0 - ∑' j, β ^ j * s j)) := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) atTop
      (𝓝 (∑' j, β ^ j * s j)) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq : (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) =
      fun T => M 0 / P 0 - ∑ j ∈ Finset.range (T + 1), β ^ j * s j := by
    funext T
    have := pv_finite hβ hP0 hP hflow T
    linarith
  rw [heq]
  exact tendsto_const_nhds.sub hpart

/-- Cochrane (2023), eq. (19.12), p. 614, infinite-horizon form: with summable discounted
surpluses, the transversality condition holds iff `M_{−1}/P_0 = ∑_{j≥0} βʲ s_j`. -/
theorem tvc_iff_pv {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hsum : Summable fun j => β ^ j * s j) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      M 0 / P 0 = ∑' j, β ^ j * s j := by
  have h := tvc_limit hβ hP0 hP hflow hsum
  constructor
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith
  · intro heq
    rw [heq, sub_self] at h
    exact h

/-- Cochrane (2023), pp. 614–615, "Such a government can have a determinate price level, even
with no money demand at all … the present value of surpluses must be positive": given
exogenous surpluses with summable present value `S > 0` and `M_{−1} > 0`, for each `P_0 > 0`
let the price level fall at rate `β` and money follow (3.1); the transversality condition then
holds iff `P_0 = M_{−1}/S`. -/
theorem price_level_determined {β : ℝ} {s : ℕ → ℝ} (hβ : 0 < β)
    (hsum : Summable fun j => β ^ j * s j) (hS : 0 < ∑' j, β ^ j * s j) {M P : ℕ → ℝ}
    (hP0 : 0 < P 0) (hP : ∀ t, P (t + 1) = β * P t)
    (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (hM0 : 0 < M 0) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      P 0 = M 0 / ∑' j, β ^ j * s j := by
  rw [tvc_iff_pv hβ hP0 hP hflow hsum]
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- Cochrane (2023), p. 615: if the present value of surpluses is not positive, no positive
initial price level satisfies the transversality condition (`M_{−1} > 0`). -/
theorem no_price_level_of_nonpos_pv {β : ℝ} {s : ℕ → ℝ} (hβ : 0 < β)
    (hsum : Summable fun j => β ^ j * s j) (hS : ∑' j, β ^ j * s j ≤ 0) {M P : ℕ → ℝ}
    (hP0 : 0 < P 0) (hP : ∀ t, P (t + 1) = β * P t)
    (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (hM0 : 0 < M 0) :
    ¬ Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) := by
  rw [tvc_iff_pv hβ hP0 hP hflow hsum]
  intro h
  have : 0 < M 0 / P 0 := div_pos hM0 hP0
  linarith

/-! ## §3.1.2 No violation with open-market operations

Here `D t = B_t + M_t` (book dating, from `t = 0`), `P t = P_t`, `s t = s_t`; the flow budget
with `Q = 1` at date `t + 1` is `D_t/P_{t+1} = D_{t+1}/P_{t+1} + s_{t+1}`. -/

/-- Cochrane (2023), §3.1.2, p. 615: with the surplus rule `s_{t+1} = (1−β)D_t/P_{t+1}`, total
nominal debt declines, `B_t + M_t = β(B_{t−1} + M_{t−1})`, hence `B_t + M_t = βᵗ(B_0 + M_0)`
(p. 616). -/
theorem omo_total_debt {β : ℝ} {D P s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hflow : ∀ t, D t / P (t + 1) = D (t + 1) / P (t + 1) + s (t + 1))
    (hs : ∀ t, s (t + 1) = (1 - β) * D t / P (t + 1)) :
    (∀ t, D (t + 1) = β * D t) ∧ ∀ t, D t = β ^ t * D 0 := by
  have h1 : ∀ t, D (t + 1) = β * D t := by
    intro t
    have h := hflow t
    rw [hs t] at h
    have := hP (t + 1)
    field_simp at h
    linarith
  refine ⟨h1, fun t => ?_⟩
  induction t with
  | zero => simp
  | succ n ih => rw [h1, ih, pow_succ]; ring

/-- Cochrane (2023), §3.1.2, p. 615: with `P_{t+1} = βP_t`, real total debt is constant,
`(B_t + M_t)/P_{t+1} = (B_{t−1} + M_{t−1})/P_t`. -/
theorem omo_real_debt_const {β : ℝ} {D P : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hD : ∀ t, D (t + 1) = β * D t) (hPβ : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    D (t + 1) / P (t + 2) = D t / P (t + 1) := by
  rw [hD, hPβ (t + 1)]
  have := hP (t + 1)
  field_simp

/-- Cochrane (2023), §3.1.2, p. 616: with money growing by open-market purchases,
`M_t = (1+µ)ᵗM_0`, bonds are `B_t = βᵗ(B_0 + M_0) − (1+µ)ᵗM_0`. -/
theorem omo_bonds {β μ : ℝ} {B M : ℕ → ℝ} (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) (t : ℕ) :
    B t = β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 := by
  have := hD t
  rw [hM t] at this
  linarith

/-- Cochrane (2023), §3.1.2, p. 616, "government debt becomes negative": if `β < 1 + µ` and
`M_0 > 0`, bonds are eventually negative. -/
theorem omo_bonds_eventually_neg {β μ : ℝ} {B M : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hM0 : 0 < M 0) (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) : ∀ᶠ t in atTop, B t < 0 := by
  have hμ : 0 < 1 + μ := by linarith
  have hq : Tendsto (fun t : ℕ => (β / (1 + μ)) ^ t * (B 0 + M 0) - M 0) atTop
      (𝓝 (0 * (B 0 + M 0) - M 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hβ hμ).le
      ((div_lt_one hμ).mpr hμβ)).mul_const _).sub_const _
  have hev := hq.eventually (gt_mem_nhds (by linarith : 0 * (B 0 + M 0) - M 0 < 0))
  filter_upwards [hev] with t ht
  rw [omo_bonds hD hM t]
  have hpos : 0 < (1 + μ) ^ t := pow_pos hμ t
  have : β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 =
      (1 + μ) ^ t * ((β / (1 + μ)) ^ t * (B 0 + M 0) - M 0) := by
    rw [div_pow]; field_simp
  rw [this]
  exact mul_neg_of_pos_of_neg hpos ht

/-- Cochrane (2023), §3.1.2, pp. 615–616, "the individual quantities of money and debt explode
in opposite directions": with `0 < β < 1`, `µ > 0`, `M_0 > 0`, `M_t → +∞` and `B_t → −∞`. -/
theorem omo_explode {β μ : ℝ} {B M : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hμ : 0 < μ)
    (hM0 : 0 < M 0) (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) :
    Tendsto M atTop atTop ∧ Tendsto B atTop atBot := by
  have hMt : Tendsto M atTop atTop := by
    have := (tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).atTop_mul_const
      hM0
    exact this.congr fun t => (hM t).symm
  refine ⟨hMt, ?_⟩
  have hb : Tendsto (fun t : ℕ => β ^ t * (B 0 + M 0)) atTop (𝓝 (0 * (B 0 + M 0))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const _
  have : B = fun t => β ^ t * (B 0 + M 0) + -M t := by
    funext t; have := hD t; linarith
  rw [this]
  exact Tendsto.add_atBot hb (tendsto_neg_atTop_atBot.comp hMt)

/-- Cochrane (2023), §3.1.2, p. 615, "the transversality condition holds": with `0 < β < 1`,
`P_t = βᵗP_0` and `B_t + M_t = βᵗ(B_0 + M_0)`, the term `β^{T+1}(B_T + M_T)/P_{T+1}` tends to zero
(it equals `βᵀ(B_0 + M_0)/P_0`). -/
theorem omo_tvc {β : ℝ} {D P : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP0 : 0 < P 0)
    (hPβ : ∀ t, P (t + 1) = β * P t) (hD : ∀ t, D t = β ^ t * D 0) :
    (∀ T, β ^ (T + 1) * D T / P (T + 1) = β ^ T * D 0 / P 0) ∧
      Tendsto (fun T => β ^ (T + 1) * D T / P (T + 1)) atTop (𝓝 0) := by
  have heq : ∀ T, β ^ (T + 1) * D T / P (T + 1) = β ^ T * D 0 / P 0 := by
    intro T
    rw [hD, price_geometric hPβ (T + 1)]
    field_simp
  refine ⟨heq, ?_⟩
  simp only [heq]
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (D 0)).div_const
    (P 0)

/-- Cochrane (2023), §3.1.2, p. 615: under the surplus rule and `P_{t+1} = βP_t`, the present
value budget holds: `(B_0 + M_0)/P_1 = ∑_{j≥0} βʲ s_{j+1}` (a genuine sum; the surplus is the
constant `(1−β)(B_0 + M_0)/P_1`). -/
theorem omo_pv {β : ℝ} {D P s : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP : ∀ t, 0 < P t)
    (hflow : ∀ t, D t / P (t + 1) = D (t + 1) / P (t + 1) + s (t + 1))
    (hs : ∀ t, s (t + 1) = (1 - β) * D t / P (t + 1)) (hPβ : ∀ t, P (t + 1) = β * P t) :
    HasSum (fun j => β ^ j * s (j + 1)) (D 0 / P 1) := by
  obtain ⟨hD1, -⟩ := omo_total_debt hP hflow hs
  have hconst : ∀ j, D j / P (j + 1) = D 0 / P 1 := by
    intro j
    induction j with
    | zero => rfl
    | succ n ih => rw [omo_real_debt_const hβ hP hD1 hPβ n, ih]
  have hsj : ∀ j, β ^ j * s (j + 1) = β ^ j * ((1 - β) * (D 0 / P 1)) := by
    intro j; rw [hs j, mul_div_assoc, hconst j]
  have hgeo := (hasSum_geometric_of_lt_one hβ.le hβ1).mul_right ((1 - β) * (D 0 / P 1))
  have h1 : (1 - β)⁻¹ * ((1 - β) * (D 0 / P 1)) = D 0 / P 1 := by
    field_simp [(by linarith : (1 - β) ≠ 0)]
  rw [h1] at hgeo
  exact hgeo.congr_fun fun j => (hsj j)

/-! ## §3.1.3 Optimality with valued money -/

/-- Cochrane (2023), eq. (3.2) and p. 616: the last-period first-order condition. If the
consumer's real resources are `w` and `(c*, m*) = (w − m*, m*)` maximizes `u(c, m)` on the
budget line `c + m = w`, and `u` is differentiable there, then `u_c = u_m`. -/
theorem last_period_foc {u : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {w ms : ℝ}
    (hu : HasFDerivAt u L (w - ms, ms)) (hmax : ∀ m, u (w - m, m) ≤ u (w - ms, ms)) :
    L (1, 0) = L (0, 1) := by
  have hpath : HasDerivAt (fun m : ℝ => (w - m, m)) ((-1 : ℝ), (1 : ℝ)) ms := by
    have h1 : HasDerivAt (fun m : ℝ => w - m) (-1) ms := by
      simpa using (hasDerivAt_id ms).const_sub w
    exact h1.prodMk (hasDerivAt_id ms)
  have hcomp : HasDerivAt (fun m => u (w - m, m)) (L ((-1 : ℝ), (1 : ℝ))) ms :=
    HasFDerivAt.comp_hasDerivAt (l := u) (l' := L) (f := fun m : ℝ => (w - m, m)) ms hu hpath
  have hmaxl : IsLocalMax (fun m => u (w - m, m)) ms := Filter.Eventually.of_forall hmax
  have h0 := hmaxl.hasDerivAt_eq_zero hcomp
  have hsplit : ((-1 : ℝ), (1 : ℝ)) = (-1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at h0
  linarith

/-- Cochrane (2023), p. 616 (sufficiency, under concavity in supergradient form): if
`u(c, m) ≤ u(c*, m*) + u_c(c − c*) + u_m(m − m*)` for all `(c, m)`, `u_c = u_m` and
`c* + m* = w`, then `(c*, m*)` maximizes `u` on the budget line `c + m = w`. -/
theorem last_period_foc_sufficient {u : ℝ × ℝ → ℝ} {cs ms uc um w : ℝ}
    (hsup : ∀ c m, u (c, m) ≤ u (cs, ms) + uc * (c - cs) + um * (m - ms)) (hfoc : uc = um)
    (hw : cs + ms = w) (m : ℝ) : u (w - m, m) ≤ u (cs, ms) := by
  have := hsup (w - m) m
  rw [hfoc] at this
  have h : um * (w - m - cs) + um * (m - ms) = 0 := by rw [← hw]; ring
  linarith

/-- Cochrane (2023), p. 616, "positive and finite marginal utility of consumption means
positive and finite … money demand", power case (19.20): for `c, m > 0`,
`u_c = c^{−γ} = θ m^{−γ} = u_m` iff `m = θ^{1/γ} c`. -/
theorem last_period_power_demand {θ γ c m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hc : 0 < c)
    (hm : 0 < m) : ucPow γ c = umPow θ γ m ↔ m = θ ^ (1 / γ) * c := by
  unfold ucPow umPow
  have hkey : (θ ^ (1 / γ) * c) ^ (-γ) = θ⁻¹ * c ^ (-γ) := by
    rw [Real.mul_rpow (by positivity) hc.le, ← Real.rpow_mul hθ.le,
      show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one]
  constructor
  · intro h
    have h1 : m ^ (-γ) = (θ ^ (1 / γ) * c) ^ (-γ) := by
      rw [hkey, h]; field_simp
    have h2 := congrArg (fun z => z ^ (-γ)⁻¹) h1
    rwa [Real.rpow_rpow_inv hm.le (by linarith),
      Real.rpow_rpow_inv (by positivity) (by linarith)] at h2
  · intro h
    rw [h, hkey]
    field_simp

/-- Cochrane (2023), p. 617, "higher consumption means the marginal utility of consumption
declines. Hence, the marginal utility of money must also decline, and desired real money
holdings must rise": with separable utility, `u_c` and `u_m` strictly decreasing, and
`u_m(m_i) = k·u_c(c_i)` (`k = i/(1+i) > 0`), `c₁ < c₂` implies `m₁ < m₂`. -/
theorem separable_money_demand_rises {uc um : ℝ → ℝ} {k c1 c2 m1 m2 : ℝ}
    (huc : StrictAntiOn uc (Set.Ioi 0)) (hum : StrictAntiOn um (Set.Ioi 0)) (hk : 0 < k)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hm1 : 0 < m1) (hm2 : 0 < m2) (h1 : um m1 = k * uc c1)
    (h2 : um m2 = k * uc c2) : m1 < m2 := by
  have hu : uc c2 < uc c1 := huc hc1 (lt_trans hc1 hc12) hc12
  have : um m2 < um m1 := by rw [h1, h2]; exact mul_lt_mul_of_pos_left hu hk
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with hlt | heq
  · have := hum hm2 hm1 hlt; linarith
  · rw [heq] at this; linarith

/-- Cochrane (2023), p. 616, the consumer's iterated budget constraint with money and interest:
if `M_{t−1} + P_t(y − c_t) = M_t + P_ts_t` and `1/(1+i_t) = βP_t/P_{t+1}`, then
`M_{−1}/P_0 = ∑_{j≤T} βʲ[i_j/(1+i_j)·M_j/P_j + s_j + c_j − y] + β^{T+1}M_T/P_{T+1}`. -/
theorem iterated_budget {β y : ℝ} {M P s c i : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hi : ∀ t, 1 + i t ≠ 0)
    (hflow : ∀ t, M t + P t * (y - c t) = M (t + 1) + P t * s t)
    (hQ : ∀ t, 1 / (1 + i t) = β * P t / P (t + 1)) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1),
        β ^ j * (i j / (1 + i j) * (M (j + 1) / P j) + s j + c j - y) +
      β ^ (T + 1) * M (T + 1) / P (T + 1) := by
  have hstep : ∀ j, M j / P j = (i j / (1 + i j) * (M (j + 1) / P j) + s j + c j - y) +
      β * (M (j + 1) / P (j + 1)) := by
    intro j
    have h1 : i j / (1 + i j) = 1 - β * P j / P (j + 1) := by
      rw [← hQ j]; field_simp [hi j]; ring
    have := hP j; have := hP (j + 1)
    have hf := hflow j
    have h2 : M j / P j = M (j + 1) / P j + s j + c j - y := by
      field_simp
      linarith
    rw [h2, h1]
    field_simp
    ring
  induction T with
  | zero =>
    rw [Finset.sum_range_one, hstep 0]
    ring
  | succ n ih =>
    have e := hstep (n + 1)
    rw [Finset.sum_range_succ, ih, mul_div_assoc, e]
    ring

end Cochrane.Monetarism.PruningDeflation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pruning inflationary equilibria: timing conventions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3, §3.2 and
§3.2.1 "Timing conventions in the inflationary equilibria", eqs. (3.3)–(3.5), pp. 618–621, with
(19.20)–(19.23), pp. 443–444. Perfect foresight.

Real balances relative to output `m_t = M_t/(P_t y) = M_t q_t/y`, where `q_t = 1/P_t ≥ 0` is the
value of money; `q_t = 0` (an infinite price level) is demonetisation and is `m_t = 0`.
With `A = (1+µ)/β = (1+δ)(1+µ)`, the map of (19.21) is `g(m) = A(1 − θm^{−γ})m`
(`PruningDeflation.ratioMap`), the demonetisation level is `m_p = θ^{1/γ}` (the pole
`x = θ^{−1/γ}` of (19.23)), and `m̄` is the inflationary steady state.

## Main results

* (3.3), "the price level eventually explodes to infinity in finite time":
  `finite_time_explosion`, `no_positive_path_below`, `explosion_x_form`.
* "there is not a continuum of inflationary equilibria, but a countable number": the equilibrium
  notion `IsEqm` (q-form, first-order condition at every date with valued money),
  `eqm_of_value` (from `q_t`), the terminal condition `terminal_balance`/`terminal_price`
  (`M_T = P_T y θ^{1/γ}`); the backward sequence `backward_exists`, `backward_unique`;
  the complete classification `eqm_initial_iff` (equilibrium initial real balances are
  `[m̄, ∞) ∪ {z_T : T ∈ ℕ}`), `eqm_demonetises`, `inflationary_initial_countable`,
  `backward_strictMono` (distinct `T`, distinct `P_0`), `backward_tendsto` (accumulating at
  `m̄`), `not_eqm_of_lt_wp`, `not_eqm_between`.
* (3.4)–(3.5): `md_discrete_iff`, `md_discrete_tendsto`, `md_cont_tendsto`,
  `md_ratio`, `md_ratio_tendsto`; the modified utility `modU`, its exact partial derivatives
  `modU_hasDerivAt_c`, `modU_hasDerivAt_m` (from `MoneyInUtility.hasDerivAt_power`), and
  `modified_foc_iff` (3.5); the inverse power demand is `MoneyInUtility.power_demand_iff`.
* p. 621: the new difference equation `new_map_of_foc`, steady state `new_fixed_iff`, the
  x-form `new_x_form`, positivity `new_map_pos` ("never goes to infinity in finite time"),
  `new_inflation_tendsto_zero`, `new_inflation_rate_tendsto`, and the continuum
  `new_inflationary_continuum`.
-/

namespace Cochrane.Monetarism.PruningInflation

open Filter Topology
open Cochrane.Monetarism.PruningDeflation
open Cochrane.Monetarism.MoneyInUtility (power_demand_iff hasDerivAt_power)

/-! ## The demonetisation level and the shape of the map -/

/-- Cochrane (2023), p. 619: the demonetisation level of real balances `m_p = θ^{1/γ}`
satisfies `θ m_p^{−γ} = 1`. -/
theorem wp_spec {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) : θ * (θ ^ (1 / γ)) ^ (-γ) = 1 := by
  rw [← Real.rpow_mul hθ.le, show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one]
  field_simp

/-- Cochrane (2023), p. 619: `g(m_p) = 0` — the value of money next period is zero. -/
theorem ratioMap_wp {β μ θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    ratioMap β μ θ γ (θ ^ (1 / γ)) = 0 := by
  unfold ratioMap; rw [wp_spec hθ hγ]; ring

/-- Cochrane (2023), p. 619: for `m > 0`, `θm^{−γ} ≤ 1` iff `m ≥ m_p`. -/
theorem le_one_iff {θ γ m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hm : 0 < m) :
    θ * m ^ (-γ) ≤ 1 ↔ θ ^ (1 / γ) ≤ m := by
  have hw := wp_spec hθ hγ
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := Real.rpow_lt_rpow_of_neg hm hcon (by linarith : -γ < 0)
    nlinarith
  · intro h
    have := Real.rpow_le_rpow_of_nonpos hwp h (by linarith : -γ ≤ 0)
    nlinarith

/-- Cochrane (2023), p. 619: below the demonetisation level the map is negative,
`0 < m < m_p ⇒ g(m) < 0` (a negative next-period value of money is impossible). -/
theorem ratioMap_neg {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hm : 0 < m) (hlt : m < θ ^ (1 / γ)) : ratioMap β μ θ γ m < 0 := by
  have h1 : 1 < θ * m ^ (-γ) := by
    by_contra hcon; push Not at hcon
    exact absurd ((le_one_iff hθ hγ hm).mp hcon) (not_le.mpr hlt)
  unfold ratioMap
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have : (1 + μ) / β * (1 - θ * m ^ (-γ)) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
  exact mul_neg_of_neg_of_pos this hm

/-- Cochrane (2023), Figure 19.1, p. 444: the map is strictly increasing on `[m_p, ∞)`. -/
theorem ratioMap_strictMonoOn {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) : StrictMonoOn (ratioMap β μ θ γ) (Set.Ici (θ ^ (1 / γ))) := by
  intro a ha b hb hab
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hwp ha
  have hb0 : 0 < b := lt_trans ha0 hab
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hfa : 0 ≤ 1 - θ * a ^ (-γ) := by linarith [(le_one_iff hθ hγ ha0).mpr ha]
  have hab' : b ^ (-γ) < a ^ (-γ) := Real.rpow_lt_rpow_of_neg ha0 hab (by linarith)
  have hfb : 1 - θ * a ^ (-γ) < 1 - θ * b ^ (-γ) := by nlinarith
  unfold ratioMap
  have h1 : (1 - θ * a ^ (-γ)) * a ≤ (1 - θ * a ^ (-γ)) * b :=
    mul_le_mul_of_nonneg_left hab.le hfa
  have h2 : (1 - θ * a ^ (-γ)) * b < (1 - θ * b ^ (-γ)) * b := mul_lt_mul_of_pos_right hfb hb0
  have := mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hA
  linarith

/-- Cochrane (2023), Figure 19.1, p. 444: the map is continuous on `(0, ∞)`. -/
theorem ratioMap_continuousOn {β μ θ γ : ℝ} :
    ContinuousOn (ratioMap β μ θ γ) (Set.Ioi 0) := by
  unfold ratioMap
  refine ContinuousOn.mul (continuousOn_const.mul (continuousOn_const.sub
    (continuousOn_const.mul ?_))) continuousOn_id
  exact fun x hx => (Real.continuousAt_rpow_const x (-γ)
    (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- Cochrane (2023), p. 444: the inflationary steady state lies above the demonetisation
level, `m_p < m̄`, when `β < 1 + µ`. -/
theorem wp_lt_ms {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) : θ ^ (1 / γ) < ms := by
  have h1 : θ * ms ^ (-γ) < 1 := by rw [hss]; have := div_pos hβ hμ; linarith
  rcases lt_or_ge (θ ^ (1 / γ)) ms with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h' | h'
    · have := Real.rpow_lt_rpow_of_neg hms h' (by linarith : -γ < 0)
      have hw := wp_spec hθ hγ
      nlinarith
    · rw [h', wp_spec hθ hγ] at h1; linarith

/-- Cochrane (2023), p. 444, "dynamics are unstable around `P y/M`": on `[m_p, m̄)` the map lies
below the diagonal, `g(m) < m`. -/
theorem ratioMap_lt_self {β μ θ γ ms m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm : 0 < m) (hlt : m < ms) :
    ratioMap β μ θ γ m < m := by
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have h1 : ms ^ (-γ) < m ^ (-γ) := Real.rpow_lt_rpow_of_neg hm hlt (by linarith)
  have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
  have h3 : (1 + μ) / β * (1 - θ * m ^ (-γ)) < 1 := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
  unfold ratioMap
  nlinarith

/-- Cochrane (2023), p. 444: on `[m̄, ∞)` the map lies on or above the diagonal. -/
theorem self_le_ratioMap {β μ θ γ ms m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hle : ms ≤ m) :
    m ≤ ratioMap β μ θ γ m := by
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hm : 0 < m := lt_of_lt_of_le hms hle
  have h1 : m ^ (-γ) ≤ ms ^ (-γ) := Real.rpow_le_rpow_of_nonpos hms hle (by linarith)
  have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
  have h3 : 1 ≤ (1 + μ) / β * (1 - θ * m ^ (-γ)) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le]
  unfold ratioMap
  nlinarith

/-- Cochrane (2023), p. 444: the only positive fixed point of the map is `m̄`. -/
theorem fixed_unique {β μ θ γ ms L : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hθ : 0 < θ) (hL : 0 < L)
    (hfix : ratioMap β μ θ γ L = L) : L = ms := by
  have h := (fixed_iff hβ hμ hL).mp hfix
  rcases lt_trichotomy L ms with h1 | h1 | h1
  · have := Real.rpow_lt_rpow_of_neg hL h1 (by linarith : -γ < 0); nlinarith
  · exact h1
  · have := Real.rpow_lt_rpow_of_neg hms h1 (by linarith : -γ < 0); nlinarith

/-! ## (3.3): finite-time explosion -/

/-- Cochrane (2023), eq. (3.3), p. 619, "For `P_0y/M_0 > P̄y/M`, the price level eventually
explodes to infinity in finite time. The denominator goes to zero or worse": every forward
orbit from `0 < m₀ < m̄` reaches `m_T ≤ m_p = θ^{1/γ}` (i.e. `1 − θx_T^γ ≤ 0`) at a finite
date, staying above `m_p` before. (Survey E22: the printed condition `P_0y/M_0 > PM/M`
should read `> P̄y/M`.) -/
theorem finite_time_explosion {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : 0 < m0)
    (hlt : m0 < ms) :
    ∃ T, (ratioMap β μ θ γ)^[T] m0 ≤ θ ^ (1 / γ) ∧
      ∀ t < T, θ ^ (1 / γ) < (ratioMap β μ θ γ)^[t] m0 := by
  set g := ratioMap β μ θ γ with hg
  set z : ℕ → ℝ := fun t => g^[t] m0 with hz
  have hzs : ∀ t, z (t + 1) = g (z t) := fun t => Function.iterate_succ_apply' _ _ _
  have hex : ∃ T, z T ≤ θ ^ (1 / γ) := by
    by_contra hcon
    push Not at hcon
    have hwp : 0 < θ ^ (1 / γ) := by positivity
    have hA : 0 < (1 + μ) / β := div_pos hμ hβ
    set r := (1 + μ) / β * (1 - θ * m0 ^ (-γ)) with hr
    have hm0wp : θ ^ (1 / γ) < m0 := by simpa [hz] using hcon 0
    have hr0 : 0 ≤ r := by
      have := (le_one_iff hθ hγ hm0).mpr hm0wp.le
      exact mul_nonneg hA.le (by linarith)
    have hr1 : r < 1 := by
      have h1 : ms ^ (-γ) < m0 ^ (-γ) := Real.rpow_lt_rpow_of_neg hm0 hlt (by linarith)
      have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
      rw [hr]; nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    have hbound : ∀ t, z t ≤ m0 ∧ z t ≤ r ^ t * m0 := by
      intro t
      induction t with
      | zero => simp [hz]
      | succ n ih =>
        have hzn : 0 < z n := lt_trans hwp (hcon n)
        have hle : m0 ^ (-γ) ≤ z n ^ (-γ) := Real.rpow_le_rpow_of_nonpos hzn ih.1 (by linarith)
        have hstep : z (n + 1) ≤ r * z n := by
          rw [hzs, hg]; unfold ratioMap
          have : (1 + μ) / β * (1 - θ * z n ^ (-γ)) ≤ r := by
            rw [hr]; apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith
          nlinarith
        constructor
        · nlinarith
        · rw [pow_succ]; nlinarith [pow_nonneg hr0 n]
    have hlim : Tendsto (fun t => r ^ t * m0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const m0
    obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds hwp)).exists
    linarith [(hbound t).2, hcon t]
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun t ht => ?_⟩
  have := Nat.find_min hex ht
  push Not at this
  exact this

/-- Cochrane (2023), eq. (3.3), p. 619: `m ≤ m_p` iff the denominator of (3.3) is non-positive,
`1 − θ x^γ ≤ 0` with `x = P y/M = 1/m`. -/
theorem explosion_x_form {θ γ m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hm : 0 < m) :
    m ≤ θ ^ (1 / γ) ↔ 1 - θ * (1 / m) ^ γ ≤ 0 := by
  have hinv : (1 / m) ^ γ = m ^ (-γ) := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  rw [hinv]
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  constructor
  · intro h
    have := Real.rpow_le_rpow_of_nonpos hm h (by linarith : -γ ≤ 0)
    have hw := wp_spec hθ hγ
    nlinarith
  · intro h
    by_contra hcon
    push Not at hcon
    have := (le_one_iff hθ hγ hm).mpr hcon.le
    have h2 : θ * m ^ (-γ) = 1 := by linarith
    have h3 := Real.rpow_lt_rpow_of_neg hwp hcon (by linarith : -γ < 0)
    have hw := wp_spec hθ hγ
    nlinarith

/-- Cochrane (2023), eq. (3.3), p. 619: no perfect-foresight path with valued money at every
date starts below the steady state, `¬(IsMPath m ∧ m₀ < m̄)`. -/
theorem no_positive_path_below {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) : ms ≤ m 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT, -⟩ := finite_time_explosion hβ hμ hθ hγ hss (hpath 0).1 hcon
  have horbit : ∀ t, m t = (ratioMap β μ θ γ)^[t] (m 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [(hpath n).2, ih, Function.iterate_succ_apply']
  rw [← horbit] at hT
  have hpos := (hpath (T + 1)).1
  rw [(hpath T).2] at hpos
  rcases hT.lt_or_eq with h | h
  · linarith [ratioMap_neg hβ hμ hθ hγ (hpath T).1 h]
  · rw [h, ratioMap_wp hθ hγ] at hpos; linarith

/-! ## Equilibria with demonetisation: countably many inflationary equilibria -/

/-- Cochrane (2023), §3.2.1, p. 619: a perfect-foresight equilibrium in real balances
`m_t = M_tq_t/y ≥ 0` (`q_t = 1/P_t` the value of money). While money is valued (`m_t > 0`) the
first-order condition (19.21) holds; once money is worthless it stays worthless. -/
def IsEqm (β μ θ γ : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 ≤ m t ∧ (0 < m t → m (t + 1) = ratioMap β μ θ γ (m t)) ∧ (m t = 0 → m (t + 1) = 0)

/-- Cochrane (2023), (19.21) in value-of-money form, p. 619: with `M_t = (1+µ)M_{t−1} > 0`,
`q_t ≥ 0`, the condition `θ(M_tq_t/y)^{−γ} = 1 − βq_{t+1}/q_t` whenever `q_t > 0` (a finite
price level), and `q_{t+1} = 0` after `q_t = 0`, the real balances `M_tq_t/y` form an `IsEqm`. -/
theorem eqm_of_value {β μ θ γ y : ℝ} {M q : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hM : ∀ t, 0 < M t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (hq : ∀ t, 0 ≤ q t)
    (hfoc : ∀ t, 0 < q t → θ * (M t * q t / y) ^ (-γ) = 1 - β * q (t + 1) / q t)
    (hzero : ∀ t, q t = 0 → q (t + 1) = 0) :
    IsEqm β μ θ γ (fun t => M t * q t / y) := by
  intro t
  have hMt := hM t
  refine ⟨by have := hq t; positivity, fun hpos => ?_, fun h0 => ?_⟩
  · have hqt : 0 < q t := by
      by_contra h; push Not at h
      have : q t = 0 := le_antisymm h (hq t)
      simp [this] at hpos
    unfold ratioMap
    dsimp only
    rw [hfoc t hqt, hgrow]
    field_simp
    ring
  · have hqt : q t = 0 := by
      have : M t * q t = 0 := by
        have := div_eq_zero_iff.mp h0
        rcases this with h | h
        · exact h
        · exact absurd h hy.ne'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hMt.ne'
      · exact h
    simp [hzero t hqt]

/-- Cochrane (2023), p. 619, "If consumers know that the price level will be infinite at time
`T + 1`, then money demand at time `T` is `M_T = P_T y θ^{1/γ}`": in an equilibrium with
`m_T > 0` and `m_{T+1} = 0`, `m_T = θ^{1/γ}`. -/
theorem terminal_balance {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (heqm : IsEqm β μ θ γ m) {T : ℕ} (hT : 0 < m T) (hT1 : m (T + 1) = 0) :
    m T = θ ^ (1 / γ) := by
  have h := (heqm T).2.1 hT
  rw [hT1] at h
  unfold ratioMap at h
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have h1 : θ * m T ^ (-γ) = 1 := by
    have : (1 + μ) / β * (1 - θ * m T ^ (-γ)) = 0 := by
      rcases mul_eq_zero.mp h.symm with h2 | h2
      · exact h2
      · exact absurd h2 hT.ne'
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 hA.ne'
    · linarith
  have h2 : m T ^ (-γ) = (θ ^ (1 / γ)) ^ (-γ) :=
    mul_left_cancel₀ hθ.ne' (h1.trans (wp_spec hθ hγ).symm)
  have h3 := congrArg (fun z => z ^ (-γ)⁻¹) h2
  rwa [Real.rpow_rpow_inv hT.le (by linarith),
    Real.rpow_rpow_inv (by positivity) (by linarith)] at h3

/-- Cochrane (2023), p. 619, "so the last period price level is `P_T = (M_T/y) θ^{−1/γ}`". -/
theorem terminal_price {θ γ y MT PT : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hP : 0 < PT)
    (h : MT / (PT * y) = θ ^ (1 / γ)) : PT = MT / y * θ ^ (-(1 / γ)) := by
  rw [Real.rpow_neg hθ.le, ← h]
  have : MT ≠ 0 := by
    intro h0; rw [h0, zero_div] at h; have : 0 < θ ^ (1 / γ) := by positivity
    linarith
  field_simp

/-- Cochrane (2023), p. 619, "We work back from this terminal condition": the backward
sequence `z_0 = m_p = θ^{1/γ}`, `g(z_{k+1}) = z_k`, `m_p ≤ z_k < m̄`. -/
def IsBackward (β μ θ γ ms : ℝ) (z : ℕ → ℝ) : Prop :=
  z 0 = θ ^ (1 / γ) ∧ (∀ k, ratioMap β μ θ γ (z (k + 1)) = z k) ∧
    ∀ k, θ ^ (1 / γ) ≤ z k ∧ z k < ms

/-- Cochrane (2023), p. 619: the backward recursion from the terminal condition is
well-defined: a backward sequence exists. -/
theorem backward_exists {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) :
    ∃ z, IsBackward β μ θ γ ms z := by
  set g := ratioMap β μ θ γ with hg
  set wp := θ ^ (1 / γ) with hwpdef
  have hwp : 0 < wp := by positivity
  have hwpms := wp_lt_ms hβ hμ hθ hγ hms hss
  have hgms : g ms = ms := (fixed_iff hβ hμ hms).mpr hss
  have hpre : ∀ y : ℝ, ∃ x : ℝ, y ∈ Set.Ico 0 ms → x ∈ Set.Ico wp ms ∧ g x = y := by
    intro y
    by_cases hy : y ∈ Set.Ico 0 ms
    · have hc : ContinuousOn g (Set.Icc wp ms) :=
        ratioMap_continuousOn.mono fun x hx => lt_of_lt_of_le hwp hx.1
      have hlo : g wp ≤ y := by rw [hg, ratioMap_wp hθ hγ]; exact hy.1
      have hhi : y ≤ g ms := by rw [hgms]; exact hy.2.le
      obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc hwpms.le hc ⟨hlo, hhi⟩
      refine ⟨x, fun _ => ⟨⟨hx.1, ?_⟩, hgx⟩⟩
      rcases hx.2.lt_or_eq with h | h
      · exact h
      · rw [h, hgms] at hgx; exact absurd hgx.symm (ne_of_lt hy.2)
    · exact ⟨0, fun h => absurd h hy⟩
  choose pre hpre using hpre
  set z : ℕ → ℝ := fun k => pre^[k] wp with hz
  have hzs : ∀ k, z (k + 1) = pre (z k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ k, z k ∈ Set.Ico wp ms := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hwpms⟩
    | succ n ih =>
      rw [hzs]; exact (hpre _ ⟨le_trans hwp.le ih.1, ih.2⟩).1
  refine ⟨z, rfl, fun k => ?_, fun k => hmem k⟩
  rw [hzs]
  exact (hpre _ ⟨le_trans hwp.le (hmem k).1, (hmem k).2⟩).2

/-- Cochrane (2023), p. 619: the backward sequence is unique (the map is injective on
`[m_p, ∞)`). -/
theorem backward_unique {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) {z z' : ℕ → ℝ} (hz : IsBackward β μ θ γ ms z)
    (hz' : IsBackward β μ θ γ ms z') : z = z' := by
  funext k
  induction k with
  | zero => rw [hz.1, hz'.1]
  | succ n ih =>
    have h : ratioMap β μ θ γ (z (n + 1)) = ratioMap β μ θ γ (z' (n + 1)) := by
      rw [hz.2.1, hz'.2.1, ih]
    exact (ratioMap_strictMonoOn hβ hμ hθ hγ).injOn (hz.2.2 (n + 1)).1 (hz'.2.2 (n + 1)).1 h

/-- Cochrane (2023), p. 619, "For each such `T` there is a different `P_0y/M_0`": the backward
sequence is strictly increasing. -/
theorem backward_strictMono {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) {z : ℕ → ℝ}
    (hz : IsBackward β μ θ γ ms z) : StrictMono z := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have h := ratioMap_lt_self hβ hμ hθ hγ hss (lt_of_lt_of_le hwp (hz.2.2 (k + 1)).1)
    (hz.2.2 (k + 1)).2
  rw [hz.2.1] at h
  exact h

/-- Cochrane (2023), p. 619 and Figure 3.1: the initial real balances of the inflationary
equilibria accumulate at the steady state, `z_T → m̄`. -/
theorem backward_tendsto {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) {z : ℕ → ℝ}
    (hz : IsBackward β μ θ γ ms z) : Tendsto z atTop (𝓝 ms) := by
  have hmono := (backward_strictMono hβ hμ hθ hγ hss hz).monotone
  have hbdd : BddAbove (Set.range z) := ⟨ms, by rintro _ ⟨k, rfl⟩; exact (hz.2.2 k).2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, z k with hL
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hL0 : 0 < L := lt_of_lt_of_le hwp (le_trans (hz.2.2 0).1 (le_ciSup hbdd 0))
  have hc : ContinuousAt (ratioMap β μ θ γ) L :=
    ratioMap_continuousOn.continuousAt (Ioi_mem_nhds hL0)
  have h1 : Tendsto (fun k => ratioMap β μ θ γ (z (k + 1))) atTop (𝓝 (ratioMap β μ θ γ L)) :=
    hc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun k => ratioMap β μ θ γ (z (k + 1))) atTop (𝓝 L) := by
    simpa only [hz.2.1] using hlim
  have hfix := tendsto_nhds_unique h1 h2
  rw [← fixed_unique hβ hμ hγ hms hss hθ hL0 hfix]
  exact hlim

/-- Cochrane (2023), p. 619: every equilibrium starting below the steady state demonetises in
finite time: there is `T` with `m_t > 0` for `t ≤ T`, `m_T = θ^{1/γ}`, `m_{T+1} = 0`, and the
initial balances equal the backward value `z_T`. -/
theorem eqm_demonetises {β μ θ γ ms : ℝ} {m z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (heqm : IsEqm β μ θ γ m) (h0 : 0 < m 0) (hlt : m 0 < ms) :
    ∃ T, (∀ t ≤ T, 0 < m t) ∧ m T = θ ^ (1 / γ) ∧ m (T + 1) = 0 ∧ m 0 = z T := by
  set g := ratioMap β μ θ γ with hg
  set wp := θ ^ (1 / γ) with hwpdef
  have hwp : 0 < wp := by positivity
  have hex : ∃ T, m T ≤ wp := by
    by_contra hcon
    push Not at hcon
    have hpath : IsMPath β μ θ γ m := fun t =>
      ⟨lt_trans hwp (hcon t), (heqm t).2.1 (lt_trans hwp (hcon t))⟩
    exact absurd (no_positive_path_below hβ hμ hθ hγ hss hpath) (not_le.mpr hlt)
  classical
  set T := Nat.find hex with hTdef
  have hTle : m T ≤ wp := Nat.find_spec hex
  have hbefore : ∀ t < T, wp < m t := fun t ht => by
    have := Nat.find_min hex ht; push Not at this; exact this
  have hTpos : 0 < m T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h]; exact h0
    · obtain ⟨n, hn⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
      have hn' : wp < m n := hbefore n (by omega)
      rw [hn, (heqm n).2.1 (lt_trans hwp hn')]
      have := (ratioMap_strictMonoOn hβ hμ hθ hγ) (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr hn'.le) hn'
      rw [ratioMap_wp hθ hγ] at this
      exact this
  have hTeq : m T = wp := by
    rcases hTle.lt_or_eq with h | h
    · have h1 := (heqm (T + 1)).1
      rw [(heqm T).2.1 hTpos] at h1
      linarith [ratioMap_neg hβ hμ hθ hγ hTpos h]
    · exact h
  have hT1 : m (T + 1) = 0 := by
    rw [(heqm T).2.1 hTpos, hTeq, hwpdef, ratioMap_wp hθ hγ]
  have hpos : ∀ t ≤ T, 0 < m t := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · exact lt_trans hwp (hbefore t h)
    · rw [h]; exact hTpos
  refine ⟨T, hpos, hTeq, hT1, ?_⟩
  have hback : ∀ k ≤ T, m (T - k) = z k := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, hTeq, hz.1]
    | succ n ih =>
      intro hn
      have hm1 : wp < m (T - (n + 1)) := hbefore _ (by omega)
      have hstep : ratioMap β μ θ γ (m (T - (n + 1))) = m (T - n) := by
        rw [← (heqm _).2.1 (lt_trans hwp hm1)]
        congr 1; omega
      rw [ih (by omega), ← hz.2.1 n] at hstep
      exact (ratioMap_strictMonoOn hβ hμ hθ hγ).injOn hm1.le (hz.2.2 (n + 1)).1 hstep
  simpa using hback T le_rfl

/-- Cochrane (2023), p. 619: conversely, for every `T` the path `m_t = z_{T−t}` (`t ≤ T`),
`m_t = 0` (`t > T`) is an equilibrium: valued money until `T`, demonetisation at `T + 1`. -/
theorem eqm_of_backward {β μ θ γ ms : ℝ} {z : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hz : IsBackward β μ θ γ ms z) (T : ℕ) :
    IsEqm β μ θ γ (fun t => if t ≤ T then z (T - t) else 0) := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  intro t
  by_cases ht : t ≤ T
  · have hzpos : 0 < z (T - t) := lt_of_lt_of_le hwp (hz.2.2 _).1
    simp only [ht, ↓reduceIte]
    refine ⟨hzpos.le, fun _ => ?_, fun h => absurd h hzpos.ne'⟩
    by_cases ht1 : t + 1 ≤ T
    · simp only [ht1, ↓reduceIte]
      have : T - t = (T - (t + 1)) + 1 := by omega
      rw [this, hz.2.1]
    · simp only [ht1, ↓reduceIte]
      have : T - t = 0 := by omega
      rw [this, hz.1, ratioMap_wp hθ hγ]
  · have ht1 : ¬ t + 1 ≤ T := by omega
    simp only [ht, ht1, ↓reduceIte]
    exact ⟨le_rfl, fun h => absurd h (lt_irrefl 0), by simp⟩

/-- Cochrane (2023), §19.3.2, p. 444, and p. 619: from `m₀ ≥ m̄` the forward orbit is an
equilibrium that never demonetises. -/
theorem eqm_of_ge {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : ms ≤ m0) :
    IsEqm β μ θ γ (fun t => (ratioMap β μ θ γ)^[t] m0) ∧
      ∀ t, ms ≤ (ratioMap β μ θ γ)^[t] m0 := by
  have hge : ∀ t, ms ≤ (ratioMap β μ θ γ)^[t] m0 := by
    intro t
    induction t with
    | zero => exact hm0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (self_le_ratioMap hβ hμ hθ hγ hms hss ih)
  refine ⟨fun t => ⟨le_trans hms.le (hge t), fun _ => Function.iterate_succ_apply' _ _ _,
    fun h => absurd h (ne_of_gt (lt_of_lt_of_le hms (hge t)))⟩, hge⟩

/-- Cochrane (2023), p. 619, "there is not a continuum of inflationary equilibria, but a
countable number": the complete classification. Positive initial real balances `m₀` start an
equilibrium iff `m₀ ≥ m̄` or `m₀ = z_T` for some `T`. -/
theorem eqm_initial_iff {β μ θ γ ms m0 : ℝ} {z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (hm0 : 0 < m0) :
    (∃ m, IsEqm β μ θ γ m ∧ m 0 = m0) ↔ ms ≤ m0 ∨ ∃ T, m0 = z T := by
  constructor
  · rintro ⟨m, heqm, rfl⟩
    rcases le_or_gt ms (m 0) with h | h
    · exact Or.inl h
    · obtain ⟨T, -, -, -, hT⟩ := eqm_demonetises hβ hμ hθ hγ hss hz heqm hm0 h
      exact Or.inr ⟨T, hT⟩
  · rintro (h | ⟨T, rfl⟩)
    · exact ⟨_, (eqm_of_ge hβ hμ hθ hγ hms hss h).1, rfl⟩
    · exact ⟨_, eqm_of_backward hθ hγ hz T, by simp⟩

/-- Cochrane (2023), p. 619: the set of initial real balances of inflationary equilibria
(`0 < m₀ < m̄`) is exactly the range of the backward sequence, hence countable. -/
theorem inflationary_initial_countable {β μ θ γ ms : ℝ} {z : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms)
    (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hz : IsBackward β μ θ γ ms z) :
    {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0} = Set.range z ∧
      {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0}.Countable := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hset : {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0} = Set.range z := by
    ext m0
    constructor
    · rintro ⟨h0, hlt, hex⟩
      rcases (eqm_initial_iff hβ hμ hθ hγ hms hss hz h0).mp hex with h | ⟨T, hT⟩
      · exact absurd h (not_le.mpr hlt)
      · exact ⟨T, hT.symm⟩
    · rintro ⟨T, rfl⟩
      have hzT : 0 < z T := lt_of_lt_of_le hwp (hz.2.2 T).1
      exact ⟨hzT, (hz.2.2 T).2,
        (eqm_initial_iff hβ hμ hθ hγ hms hss hz hzT).mpr (Or.inr ⟨T, rfl⟩)⟩
  exact ⟨hset, hset ▸ Set.countable_range z⟩

/-- Cochrane (2023), p. 619: initial real balances below the demonetisation level start no
equilibrium. -/
theorem not_eqm_of_lt_wp {β μ θ γ m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hm0 : 0 < m0) (hlt : m0 < θ ^ (1 / γ)) :
    ¬ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0 := by
  rintro ⟨m, heqm, rfl⟩
  have h1 := (heqm 1).1
  rw [(heqm 0).2.1 hm0] at h1
  linarith [ratioMap_neg hβ hμ hθ hγ hm0 hlt]

/-- Cochrane (2023), p. 619, "not a continuum": initial real balances strictly between the first
two backward values `z_0 = θ^{1/γ}` and `z_1` start no equilibrium; and the inflationary
initial values are a countable subset of the uncountable interval `(0, m̄)`. -/
theorem not_eqm_between {β μ θ γ ms m0 : ℝ} {z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (h1 : z 0 < m0) (h2 : m0 < z 1) :
    (¬ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0) ∧ ¬ (Set.Ioo 0 ms).Countable := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hm0 : 0 < m0 := lt_trans (by rw [hz.1]; exact hwp) h1
  have hmono := backward_strictMono hβ hμ hθ hγ hss hz
  refine ⟨fun hex => ?_, by rw [Cardinal.Real.Ioo_countable_iff]; linarith⟩
  rcases (eqm_initial_iff hβ hμ hθ hγ hms hss hz hm0).mp hex with h | ⟨T, hT⟩
  · linarith [(hz.2.2 1).2]
  · rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [hT, h0] at h1; exact lt_irrefl _ h1
    · have := hmono.monotone (Nat.one_le_iff_ne_zero.mpr h0.ne')
      rw [← hT] at this; linarith

/-! ## (3.4)–(3.5): discrete versus continuous money demand -/

/-- Cochrane (2023), eq. (3.4), p. 620: discrete-time money demand per unit of nominal income,
`M/(Py) = ((1/θ) i/(1+i))^{−1/γ}`. -/
noncomputable def mdDisc (θ γ i : ℝ) : ℝ := (1 / θ * (i / (1 + i))) ^ (-(1 / γ))

/-- Cochrane (2023), eq. (3.5), p. 620: continuous-time money demand per unit of nominal
income, `M/(Py) = (i/θ)^{−1/γ}`. -/
noncomputable def mdCont (θ γ i : ℝ) : ℝ := (i / θ) ^ (-(1 / γ))

/-- Cochrane (2023), eqs. (19.16), (19.20), (3.4), pp. 443, 620: with power utility and `c = y`,
`u_m/u_c = θ(M/(Py))^{−γ} = i/(1+i)` iff `M/(Py) = ((1/θ) i/(1+i))^{−1/γ}`. -/
theorem md_discrete_iff {θ γ i m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hi : 0 < i) (hm : 0 < m) :
    θ * m ^ (-γ) = i / (1 + i) ↔ m = mdDisc θ γ i := by
  unfold mdDisc
  rw [power_demand_iff hθ hγ.ne' (by positivity) hm, div_eq_mul_inv (i / (1 + i)), one_div,
    mul_comm]
  simp only [one_div]

/-- Cochrane (2023), p. 620, "As inflation and interest rates approach infinity, real money
demand `M_t/P_t` in (3.4) approaches a constant": `mdDisc → θ^{1/γ}` as `i → ∞`. -/
theorem md_discrete_tendsto {θ γ : ℝ} (hθ : 0 < θ) :
    Tendsto (mdDisc θ γ) atTop (𝓝 (θ ^ (1 / γ))) := by
  have h1 : Tendsto (fun i : ℝ => i / (1 + i)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun i : ℝ => (1 + i)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    have h2 : Tendsto (fun i : ℝ => 1 - (1 + i)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with i hi
    field_simp
    ring
  have h3 : Tendsto (fun i : ℝ => 1 / θ * (i / (1 + i))) atTop (𝓝 (1 / θ * 1)) :=
    h1.const_mul _
  have hc : ContinuousAt (fun x : ℝ => x ^ (-(1 / γ))) (1 / θ * 1) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))
  have h4 := hc.tendsto.comp h3
  have h5 : (1 / θ * 1) ^ (-(1 / γ)) = θ ^ (1 / γ) := by
    rw [mul_one, one_div, Real.inv_rpow hθ.le, Real.rpow_neg hθ.le, inv_inv]
  rw [h5] at h4
  exact h4

/-- Cochrane (2023), p. 620, "real money demand in (3.5) smoothly approaches zero":
`mdCont → 0` as `i → ∞`. -/
theorem md_cont_tendsto {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    Tendsto (mdCont θ γ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun i : ℝ => i / θ) atTop atTop :=
    tendsto_id.atTop_div_const hθ
  exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1 / γ)).comp h1

/-- Cochrane (2023), p. 620, "For small `i_t`, the difference between `i_t` and `i_t/(1+i_t)` is
minor": the ratio of (3.4) to (3.5) is `(1+i)^{1/γ}`. -/
theorem md_ratio {θ γ i : ℝ} (hθ : 0 < θ) (hi : 0 < i) :
    mdDisc θ γ i / mdCont θ γ i = (1 + i) ^ (1 / γ) := by
  unfold mdDisc mdCont
  have h : 1 / θ * (i / (1 + i)) = i / θ * (1 + i)⁻¹ := by field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + i), inv_inv]
  have : 0 < (i / θ) ^ (-(1 / γ)) := Real.rpow_pos_of_pos (by positivity) _
  field_simp

/-- Cochrane (2023), p. 620: the ratio of (3.4) to (3.5) tends to one as `i → 0⁺`. -/
theorem md_ratio_tendsto {θ γ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun i => mdDisc θ γ i / mdCont θ γ i) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun i : ℝ => (1 + i) ^ (1 / γ)) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero, Real.one_rpow] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with i hi
  exact (md_ratio hθ hi).symm

/-- Cochrane (2023), p. 620: the modified utility
`u(c, m) = c^{1−γ}/(1−γ) + θ/(1−γ)·(1/(1+i))·m^{1−γ}` (`m = M/P`). -/
noncomputable def modU (θ γ i c m : ℝ) : ℝ :=
  c ^ (1 - γ) / (1 - γ) + θ / (1 - γ) * (1 / (1 + i)) * m ^ (1 - γ)

/-- Cochrane (2023), p. 620: exact derivative of the modified utility in `c`:
`u_c = c^{−γ}` (`γ ≠ 1`, `c > 0`). -/
theorem modU_hasDerivAt_c {θ γ i c m : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun c => modU θ γ i c m) (c ^ (-γ)) c :=
  (hasDerivAt_power hγ hc).add_const (θ / (1 - γ) * (1 / (1 + i)) * m ^ (1 - γ))

/-- Cochrane (2023), p. 620: exact derivative of the modified utility in `m`:
`u_m = θ/(1+i)·m^{−γ}`. -/
theorem modU_hasDerivAt_m {θ γ i c m : ℝ} (hγ : γ ≠ 1) (hm : 0 < m) :
    HasDerivAt (fun m => modU θ γ i c m) (θ / (1 + i) * m ^ (-γ)) m := by
  have h := ((hasDerivAt_power hγ hm).const_mul (θ * (1 / (1 + i)))).const_add
    (c ^ (1 - γ) / (1 - γ))
  convert h using 1
  · funext z
    unfold modU
    ring
  · ring

/-- Cochrane (2023), eq. (3.5), p. 620, "Now, the first-order condition `u_m/u_c = i/(1+i)`
becomes, in equilibrium `c_t = y_t`, (3.5)": with the modified utility,
`u_m/u_c = i/(1+i)` iff `m = c (i/θ)^{−1/γ}`. -/
theorem modified_foc_iff {θ γ i c m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hi : 0 < i) (hc : 0 < c)
    (hm : 0 < m) : θ / (1 + i) * m ^ (-γ) / c ^ (-γ) = i / (1 + i) ↔ m = c * mdCont θ γ i := by
  have hcpos : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc _
  have h1 : θ / (1 + i) * m ^ (-γ) / c ^ (-γ) = i / (1 + i) ↔ θ * (m / c) ^ (-γ) = i := by
    rw [Real.div_rpow hm.le hc.le]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith
  rw [h1, power_demand_iff hθ hγ.ne' hi (div_pos hm hc), div_eq_iff hc.ne']
  unfold mdCont
  constructor <;> intro h <;> linarith

/-! ## p. 621: the new difference equation — no finite-time explosion -/

/-- Cochrane (2023), p. 621: the modified map `m ↦ A m/(1 + θm^{−γ})`, `A = (1+µ)/β`. -/
noncomputable def newMap (β μ θ γ m : ℝ) : ℝ := (1 + μ) / β * m / (1 + θ * m ^ (-γ))

/-- Cochrane (2023), p. 621, first display: with the modified utility the first-order
condition `θ(M_t/(P_ty))^{−γ} = (1/β)(P_{t+1}/P_t) − 1` and `M_{t+1} = (1+µ)M_t` give
`m_{t+1} = A m_t/(1 + θm_t^{−γ})`. -/
theorem new_map_of_foc {β μ θ γ y : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hy : 0 < y) (hM : ∀ t, 0 < M t) (hP : ∀ t, 0 < P t)
    (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ)
    (hfoc : θ * (M t / (P t * y)) ^ (-γ) = 1 / β * (P (t + 1) / P t) - 1) :
    M (t + 1) / (P (t + 1) * y) = newMap β μ θ γ (M t / (P t * y)) := by
  unfold newMap
  rw [hfoc, hgrow, show 1 + (1 / β * (P (t + 1) / P t) - 1) = P (t + 1) / (β * P t) by
    field_simp; ring]
  have := hM t; have := hP t; have := hP (t + 1)
  field_simp

/-- Cochrane (2023), p. 621: the steady state of the modified model,
`θ(M/(Py))^{−γ} = (1+δ)(1+µ) − 1`. -/
theorem new_fixed_iff {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hm : 0 < m) :
    newMap β μ θ γ m = m ↔ θ * m ^ (-γ) = (1 + μ) / β - 1 := by
  have hD : 0 < 1 + θ * m ^ (-γ) := by have := Real.rpow_pos_of_pos hm (-γ); positivity
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  unfold newMap
  rw [div_eq_iff hD.ne']
  constructor
  · intro h
    have : (1 + μ) / β = 1 + θ * m ^ (-γ) :=
      mul_right_cancel₀ hm.ne' (by linarith : (1 + μ) / β * m = (1 + θ * m ^ (-γ)) * m)
    linarith
  · intro h
    rw [show 1 + θ * m ^ (-γ) = (1 + μ) / β by linarith]
    ring

/-- Cochrane (2023), p. 621, display "in place of (19.23)": with `θ x̄^γ = A − 1`, the modified
map in `x = 1/m` is `x_{t+1} = x_t(1 + θx_t^γ)/(1 + θx̄^γ)`. -/
theorem new_x_form {β μ θ γ m xbar : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hm : 0 < m) (hss : θ * xbar ^ γ = (1 + μ) / β - 1) :
    1 / newMap β μ θ γ m = 1 / m * (1 + θ * (1 / m) ^ γ) / (1 + θ * xbar ^ γ) := by
  have hinv : m ^ (-γ) = (1 / m) ^ γ := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  unfold newMap
  rw [hinv, hss]
  have : 0 < (1 / m) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hμ' : (1 + μ) ≠ 0 := hμ.ne'
  rw [show 1 + ((1 + μ) / β - 1) = (1 + μ) / β by ring]
  field_simp

/-- Cochrane (2023), p. 621, "the price level never goes to infinity in finite time": the
modified map sends `(0, ∞)` into itself, so every `m₀ > 0` starts a path defined for all
dates. -/
theorem new_map_pos {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hm : 0 < m) :
    0 < newMap β μ θ γ m := by
  unfold newMap
  have := Real.rpow_pos_of_pos hm (-γ)
  positivity

/-- Cochrane (2023), p. 621, "a continuum of inflationary equilibria that go on forever": with
`A > 1`, from `0 < m₀ < m̄` real balances fall strictly and tend to zero, never reaching zero. -/
theorem new_inflation_tendsto_zero {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1)
    (hm0 : 0 < m0) (hlt : m0 < ms) :
    (∀ t, 0 < (newMap β μ θ γ)^[t] m0) ∧ StrictAnti (fun t => (newMap β μ θ γ)^[t] m0) ∧
      Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝 0) := by
  set g := newMap β μ θ γ with hg
  set z : ℕ → ℝ := fun t => g^[t] m0 with hz
  have hzs : ∀ t, z (t + 1) = g (z t) := fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < z t := by
    intro t
    induction t with
    | zero => simpa [hz] using hm0
    | succ n ih => rw [hzs]; exact new_map_pos hβ hμ hθ ih
  have hbelow : ∀ x, 0 < x → x < ms → g x < x := by
    intro x hx hxl
    have h1 : ms ^ (-γ) < x ^ (-γ) := Real.rpow_lt_rpow_of_neg hx hxl (by linarith)
    have h2 : (1 + μ) / β < 1 + θ * x ^ (-γ) := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    rw [hg]; unfold newMap
    have h3 : 0 < 1 + θ * x ^ (-γ) := by have := Real.rpow_pos_of_pos hx (-γ); positivity
    rw [div_lt_iff₀ h3]
    nlinarith
  have hstep : ∀ t, z t < ms ∧ z (t + 1) < z t := by
    intro t
    induction t with
    | zero =>
      have h0 : z 0 = m0 := rfl
      exact ⟨by rw [h0]; exact hlt, by rw [hzs, h0]; exact hbelow m0 hm0 hlt⟩
    | succ n ih =>
      have h1 : z (n + 1) < ms := lt_trans ih.2 ih.1
      exact ⟨h1, by rw [hzs (n + 1)]; exact hbelow _ (hpos _) h1⟩
  have hanti : StrictAnti z := strictAnti_nat_of_succ_lt fun n => (hstep n).2
  refine ⟨hpos, hanti, ?_⟩
  have hbdd : BddBelow (Set.range z) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (hpos k).le⟩
  have hlim := tendsto_atTop_ciInf hanti.antitone hbdd
  set L := ⨅ k, z k with hL
  have hL0 : 0 ≤ L := le_ciInf fun k => (hpos k).le
  rcases hL0.lt_or_eq with hL0 | hL0
  · exfalso
    have hc : ContinuousAt g L := by
      rw [hg]; unfold newMap
      have hcd : ContinuousAt (fun x : ℝ => 1 + θ * x ^ (-γ)) L :=
        continuousAt_const.add (continuousAt_const.mul
          (Real.continuousAt_rpow_const L (-γ) (Or.inl hL0.ne')))
      have := Real.rpow_pos_of_pos hL0 (-γ)
      exact ((continuousAt_const.mul continuousAt_id).div hcd (by positivity))
    have h1 : Tendsto (fun k => g (z k)) atTop (𝓝 (g L)) := hc.tendsto.comp hlim
    have h2 : Tendsto (fun k => g (z k)) atTop (𝓝 L) := by
      simpa only [← hzs] using (tendsto_add_atTop_iff_nat 1).mpr hlim
    have hfix := tendsto_nhds_unique h1 h2
    have hLlt : L < ms := lt_of_le_of_lt (ciInf_le hbdd 0) (hstep 0).1
    have := hbelow L hL0 hLlt
    linarith
  · rw [hL0]; exact hlim

/-- Cochrane (2023), p. 621: along these inflationary paths inflation
`P_{t+1}/P_t = (1+µ)m_t/m_{t+1} = β(1 + θm_t^{−γ})` rises without bound, but the price level is
finite at every date. -/
theorem new_inflation_rate_tendsto {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1)
    (hm0 : 0 < m0) (hlt : m0 < ms) :
    (∀ t, (1 + μ) * ((newMap β μ θ γ)^[t] m0) / ((newMap β μ θ γ)^[t + 1] m0) =
      β * (1 + θ * ((newMap β μ θ γ)^[t] m0) ^ (-γ))) ∧
    Tendsto (fun t => β * (1 + θ * ((newMap β μ θ γ)^[t] m0) ^ (-γ))) atTop atTop := by
  obtain ⟨hpos, -, hlim⟩ := new_inflation_tendsto_zero hβ hμ hθ hγ hss hm0 hlt
  refine ⟨fun t => ?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    have hw := hpos t
    set w := (newMap β μ θ γ)^[t] m0 with hwdef
    unfold newMap
    have := Real.rpow_pos_of_pos hw (-γ)
    field_simp
  · have hpos' : Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩
    have h1 : Tendsto (fun x : ℝ => x ^ (-γ)) (𝓝[>] 0) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h3 := (h1.comp hpos').const_mul_atTop hθ
    have h4 := tendsto_atTop_add_const_left atTop 1 h3
    exact h4.const_mul_atTop hβ

/-- Cochrane (2023), p. 621, "in particular a continuum of inflationary equilibria": every
`m₀ ∈ (0, m̄)` starts a distinct inflationary path with valued money at every date; the set of
such initial values, the interval `(0, m̄)`, is uncountable. -/
theorem new_inflationary_continuum {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1) :
    (∀ m0 ∈ Set.Ioo 0 ms, ∀ t, 0 < (newMap β μ θ γ)^[t] m0 ∧
      Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝 0)) ∧
      Set.InjOn (fun m0 => fun t => (newMap β μ θ γ)^[t] m0) (Set.Ioo 0 ms) ∧
      ¬ (Set.Ioo 0 ms).Countable := by
  refine ⟨fun m0 hm t => ⟨(new_inflation_tendsto_zero hβ hμ hθ hγ hss hm.1 hm.2).1 t,
    (new_inflation_tendsto_zero hβ hμ hθ hγ hss hm.1 hm.2).2.2⟩, ?_, ?_⟩
  · intro a _ b _ hab
    have := congrFun hab 0
    simpa using this
  · rw [Cardinal.Real.Ioo_countable_iff]; linarith

end Cochrane.Monetarism.PruningInflation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Obstfeld–Rogoff fix for inflationary equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3,
§3.2.2 "The Obstfeld-Rogoff fix for inflationary equilibria" and §3.2.3, eq. (3.6),
Figure 3.2, pp. 621–629. Perfect foresight, separable utility, constant endowment `y`, constant
money `M`; `u₁ = u'(y) > 0`, `v'` the marginal utility of real money.

Following the survey's modelling advice, everything is stated with the value of money
`q_t = 1/P_t ≥ 0`, so that an infinite price level is `q_t = 0`; real balances are `M q_t`.

## Main results

* (3.6): `eq36_iff_value` (levels ⇔ value-of-money form), `eq36_real` (real-balance form),
  the steady state `steady_iff` (`v'(m̿) = (1−β)u'(y)`) and the terminal condition
  `terminal_iff` (`v'(M/P_T) = u'(y)` when `P_{T+1} = ∞`).
* The redemption first-order condition at `T` (p. 626): `redemption_foc_zero`,
  `redemption_raises_balance` (`P_T < P̄`, `M/P_T > M/P̄`).
* Figure 3.2 (`u' = 1`, `M = 1`, `β = 1/2`, `v'(m) = m^{−1/2}`): `fig32_vp_eq_rpow`,
  `fig32_steady` (`m = 4`), `fig32_terminal` (`M/P̄ = 1`), the backward map `fig32_back`
  with `fig32_back_spec`, `fig32_eps0` (`1 + √3/2 ≈ 1.866`), `fig32_eps_half`
  (`(3 + 2√2)/4 ≈ 1.457`), `fig32_numbers`; survey error **E18**: the caption's
  `v(m) = m^{−1/2}` is decreasing (`e18_caption_decreasing`) and admits neither the steady
  state nor the terminal level (`e18_no_steady_state`), while `v(m) = 2√m` has `v' = m^{−1/2}`
  (`e18_correct_v`).
* Obstfeld and Rogoff's finite-price theorem (p. 624 quote): `IsORPath`, `or_balance_step`,
  `or_no_hyperinflation` — with one-way redemption, the arbitrage bound `q_t ≥ ε > 0` and
  (3.6), real balances never fall below the steady state, so no hyperinflation path exists.
  `two_way_steady` / `two_way_needs_sale`: the two-way conversion steady state at `q = ε` needs
  the government to sell money.
* Cochrane's demonetised equilibrium (pp. 625–627), the definitional dispute made explicit:
  `cochrane_sum_identity` and `cochrane_household_optimal` — with a one-time redemption of the
  money carried out of `T`, the path with `q_{T+1} = 0` and all money redeemed solves the
  price-taking household's problem (Walrasian equilibrium); `cochrane_violates_or_bound` — it
  violates Obstfeld and Rogoff's arbitrage bound; `standing_redemption_no_optimum` — if the
  redemption offer also stands for money acquired at `q = 0`, the household can always do
  strictly better, so under that (deviation/arbitrage) reading the path is not an equilibrium.
  Figure 3.2 instance: `fig32_v_supergradient`, `fig32_cochrane_path`,
  `fig32_cochrane_optimal` (the "ε = 0.5" path is household-optimal for every `T`).
-/

namespace Cochrane.Monetarism.ObstfeldRogoff

open Filter Topology

/-! ## Equation (3.6) -/

/-- Cochrane (2023), eq. (3.6), p. 623 (Obstfeld–Rogoff (1983) eq. (4)): in levels,
`u'(y)/P_t − v'(M/P_t)/P_t = βu'(y)/P_{t+1}` iff, with `q = 1/P`,
`(u'(y) − v'(Mq_t))q_t = βu'(y)q_{t+1}`. -/
theorem eq36_iff_value {β u1 M P P' : ℝ} {vp : ℝ → ℝ} :
    u1 / P - vp (M / P) / P = β * u1 / P' ↔
      (u1 - vp (M * (1 / P))) * (1 / P) = β * u1 * (1 / P') := by
  rw [show M * (1 / P) = M / P by ring,
    show (u1 - vp (M / P)) * (1 / P) = u1 / P - vp (M / P) / P by ring,
    show β * u1 * (1 / P') = β * u1 / P' by ring]

/-- Cochrane (2023), eq. (3.6), p. 623, in real balances `m_t = Mq_t`:
`(u'(y) − v'(m_t))m_t = βu'(y)m_{t+1}` (multiply the value form by `M`). -/
theorem eq36_real {β u1 M q q' : ℝ} {vp : ℝ → ℝ} (hM : 0 < M) :
    (u1 - vp (M * q)) * q = β * u1 * q' ↔ (u1 - vp (M * q)) * (M * q) = β * u1 * (M * q') := by
  constructor
  · intro h; rw [← mul_assoc, mul_comm _ M, mul_assoc, h]; ring
  · intro h
    have : M * ((u1 - vp (M * q)) * q) = M * (β * u1 * q') := by linarith [h]
    exact mul_left_cancel₀ hM.ne' this

/-- Cochrane (2023), p. 623: the steady state `P̿` of (3.6) with constant money:
`u'/P − v'(M/P)/P = βu'/P` iff `v'(M/P) = (1−β)u'(y)`. -/
theorem steady_iff {β u1 M P : ℝ} {vp : ℝ → ℝ} (hP : 0 < P) :
    u1 / P - vp (M / P) / P = β * u1 / P ↔ vp (M / P) = (1 - β) * u1 := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; rw [h]; field_simp; ring

/-- Cochrane (2023), p. 623, "The price level at time `T` is then `v'(M/P_T) = v'(M/P̄) = u'(y)`":
the value form of (3.6) at `T` with `q_{T+1} = 0` (`P_{T+1} = ∞`) and `q_T > 0` holds iff
`v'(Mq_T) = u'(y)`. -/
theorem terminal_iff {β u1 M qT : ℝ} {vp : ℝ → ℝ} (hq : 0 < qT) :
    (u1 - vp (M * qT)) * qT = β * u1 * 0 ↔ vp (M * qT) = u1 := by
  rw [mul_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact absurd h1 hq.ne'
  · intro h; rw [h]; ring

/-- Cochrane (2023), p. 626, display: with the redemption promise, the first-order condition at
`T` is `(u'(y) − v'(M/P_T))/P_T = max(βu'(y)/P̲, βu'(y)/P_{T+1})` with `P̲ = 1/ε`; in value form,
with `q_{T+1} = 0`, the right side is `βu'(y)ε`. -/
theorem redemption_foc_zero {β u1 ε : ℝ} (hβ : 0 < β) (hu : 0 < u1) (hε : 0 ≤ ε) :
    max (β * u1 * ε) (β * u1 * 0) = β * u1 * ε := by
  rw [mul_zero]
  exact max_eq_left (by positivity)

/-- Cochrane (2023), p. 626, "This effect gives a small decrease in the price level `P_T < P̄`
and `M/P_T > M/P̄`": if `v'` is strictly decreasing, `v'(m̄) = u'(y)`, and the terminal
condition with redemption `(u' − v'(m_T))m_T = βu'εM` holds with `ε > 0`, then `m_T > m̄`. -/
theorem redemption_raises_balance {β u1 ε M mT mbar : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β)
    (hu : 0 < u1) (hε : 0 < ε) (hM : 0 < M) (hmT : 0 < mT) (hmbar : 0 < mbar)
    (hanti : StrictAntiOn vp (Set.Ioi 0)) (hbar : vp mbar = u1)
    (hfoc : (u1 - vp mT) * mT = β * u1 * ε * M) : mbar < mT := by
  have hpos : 0 < (u1 - vp mT) * mT := by rw [hfoc]; positivity
  have h1 : vp mT < u1 := by
    by_contra h; push Not at h
    have : (u1 - vp mT) * mT ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hmT.le
    linarith
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have := hanti hmT hmbar h; linarith
  · rw [h, hbar] at h1; exact lt_irrefl _ h1

/-! ## Figure 3.2 -/

/-- Cochrane (2023), Figure 3.2, p. 624: the marginal utility of money `v'(m) = 1/√m`. -/
noncomputable def figVp (m : ℝ) : ℝ := 1 / Real.sqrt m

/-- Cochrane (2023), Figure 3.2, p. 624: `1/√m = m^{−1/2}` for `m > 0`. -/
theorem fig32_vp_eq_rpow {m : ℝ} (hm : 0 < m) : figVp m = m ^ (-(1 / 2 : ℝ)) := by
  unfold figVp
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hm.le, one_div]

/-- Cochrane (2023), Figure 3.2, p. 624: `v'` is strictly decreasing on `(0, ∞)`. -/
theorem fig32_vp_strictAnti : StrictAntiOn figVp (Set.Ioi 0) := by
  intro a ha b _ hab
  unfold figVp
  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h2 : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  exact one_div_lt_one_div_of_lt h1 h2

/-- Cochrane (2023), Figure 3.2, p. 624: with `u' = 1`, `β = 1/2`, the steady state of (3.6)
`v'(m) = (1−β)u'` is `m = 4` ("Steady state" line). -/
theorem fig32_steady {m : ℝ} (hm : 0 < m) : figVp m = (1 - 1 / 2) * 1 ↔ m = 4 := by
  unfold figVp
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  constructor
  · intro h
    have h1 : Real.sqrt m = 2 := by field_simp at h; linarith
    have := Real.sq_sqrt hm.le
    rw [h1] at this; linarith
  · intro h
    rw [h, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-- Cochrane (2023), Figure 3.2, p. 624: the terminal level `v'(M/P̄) = u'(y) = 1` is
`M/P̄ = 1` ("the lower horizontal line"). -/
theorem fig32_terminal {m : ℝ} (hm : 0 < m) : figVp m = 1 ↔ m = 1 := by
  unfold figVp
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  constructor
  · intro h
    have h1 : Real.sqrt m = 1 := by field_simp at h; linarith
    have := Real.sq_sqrt hm.le
    rw [h1] at this; linarith
  · intro h; rw [h, Real.sqrt_one]; norm_num

/-- Cochrane (2023), Figure 3.2, p. 624: the backward step of (3.6), `m − √m = m'/2`, solved by
`b(m') = ((1 + √(1 + 2m'))/2)²`. -/
noncomputable def fig32_back (m' : ℝ) : ℝ := ((1 + Real.sqrt (1 + 2 * m')) / 2) ^ 2

/-- Cochrane (2023), Figure 3.2, p. 624: for `m' ≥ 0`, `b(m')` is the unique `m ≥ 1/4` with
`(u' − v'(m))m = βu'm'`, i.e. `m − √m = m'/2`; moreover `b(m') ≥ 1`. -/
theorem fig32_back_spec {m' : ℝ} (hm' : 0 ≤ m') :
    1 ≤ fig32_back m' ∧ (1 - figVp (fig32_back m')) * fig32_back m' = 1 / 2 * 1 * m' ∧
      ∀ m, 1 / 4 ≤ m → (1 - figVp m) * m = 1 / 2 * 1 * m' → m = fig32_back m' := by
  have hr : 1 ≤ Real.sqrt (1 + 2 * m') := by
    have := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ 1 + 2 * m')
    rwa [Real.sqrt_one] at this
  have hr2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + 2 * m')
  set r := Real.sqrt (1 + 2 * m') with hrdef
  have hsq : Real.sqrt (fig32_back m') = (1 + r) / 2 := by
    unfold fig32_back
    exact Real.sqrt_sq (by linarith)
  have hb1 : 1 ≤ fig32_back m' := by unfold fig32_back; nlinarith
  refine ⟨hb1, ?_, ?_⟩
  · unfold figVp
    rw [hsq]
    unfold fig32_back
    rw [← hrdef]
    field_simp
    nlinarith
  · intro m hm h
    have hm0 : 0 < m := by linarith
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    have hsm := Real.sq_sqrt hm0.le
    unfold figVp at h
    have h1 : m - Real.sqrt m = m' / 2 := by
      have : (1 - 1 / Real.sqrt m) * m = m - Real.sqrt m := by
        field_simp; nlinarith
      linarith
    have hs2 : 1 / 2 ≤ Real.sqrt m := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hm
    have h2 : Real.sqrt m = (1 + r) / 2 := by
      have hq : (2 * Real.sqrt m - 1) ^ 2 = r ^ 2 := by nlinarith
      have h3 : 2 * Real.sqrt m - 1 = r := by
        have hr0 : 0 ≤ r := by linarith
        nlinarith [sq_nonneg (2 * Real.sqrt m - 1 - r), sq_nonneg (2 * Real.sqrt m - 1 + r)]
      linarith
    rw [← hsm, h2]
    unfold fig32_back
    rw [← hrdef]

/-- Cochrane (2023), Figure 3.2, p. 624, "ε = 0" line: `M/P_T = b(0) = 1` and the previous date
`M/P_{T−1} = b(1) = 1 + √3/2` (≈ 1.866). -/
theorem fig32_eps0 : fig32_back 0 = 1 ∧ fig32_back 1 = 1 + Real.sqrt 3 / 2 := by
  constructor
  · unfold fig32_back; norm_num
  · unfold fig32_back
    have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [show (1 : ℝ) + 2 * 1 = 3 by norm_num]
    nlinarith

/-- Cochrane (2023), Figure 3.2, p. 624, "ε = 0.5" line: with redemption value `Mε = 0.5` at
`T + 1`, the terminal condition `m_T − √m_T = βεM/u' = 1/4` gives `M/P_T = b(1/2) = (3 + 2√2)/4`
(≈ 1.457), above `M/P̄ = 1`. -/
theorem fig32_eps_half : fig32_back (1 / 2) = (3 + 2 * Real.sqrt 2) / 4 := by
  unfold fig32_back
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [show (1 : ℝ) + 2 * (1 / 2) = 2 by norm_num]
  nlinarith

/-- Cochrane (2023), Figure 3.2, p. 624: the plotted numbers, `1.866 < 1 + √3/2 < 1.8661` and
`1.457 < (3 + 2√2)/4 < 1.4572`; the redemption value is `Mε = 1 · 0.5`. -/
theorem fig32_numbers :
    (1.866 : ℝ) < 1 + Real.sqrt 3 / 2 ∧ 1 + Real.sqrt 3 / 2 < (1.8661 : ℝ) ∧
      (1.457 : ℝ) < (3 + 2 * Real.sqrt 2) / 4 ∧ (3 + 2 * Real.sqrt 2) / 4 < (1.4572 : ℝ) ∧
      (1 : ℝ) * 0.5 = 0.5 := by
  have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have p3 := Real.sqrt_nonneg 3
  have p2 := Real.sqrt_nonneg 2
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩ <;> nlinarith

/-- Cochrane (2023), Figure 3.2 caption, survey error **E18**: the caption's `v(m) = m^{−1/2}`
has derivative `−½ m^{−3/2} < 0`: money would have negative marginal utility. -/
theorem e18_caption_decreasing {m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1)) m ∧
      -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) < 0 := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hm.ne'), ?_⟩
  have := Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ) - 1)
  linarith

/-- Cochrane (2023), Figure 3.2 caption (E18): with `v(m) = m^{−1/2}` (so `v' < 0`) neither the
steady state `v'(m) = (1−β)u' = 1/2` nor the terminal level `v'(m) = u' = 1` has a positive
solution — the figure cannot be drawn from the caption's utility. -/
theorem e18_no_steady_state {m : ℝ} (hm : 0 < m) :
    -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) ≠ 1 / 2 ∧ -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) ≠ 1 := by
  have := (e18_caption_decreasing hm).2
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Figure 3.2 (E18, corrected): `v(m) = 2√m` has `v'(m) = m^{−1/2}`, the
marginal utility used for the plotted numbers. -/
theorem e18_correct_v {m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x => 2 * Real.sqrt x) (figVp m) m := by
  have h := (Real.hasDerivAt_sqrt hm.ne').const_mul 2
  convert h using 1
  unfold figVp
  have : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  field_simp

/-! ## Obstfeld and Rogoff's finite-price theorem -/

/-- Cochrane (2023), pp. 623–624 (Obstfeld–Rogoff (1983), p. 684): a perfect-foresight path
under one-way redemption at `ε`, in Obstfeld and Rogoff's sense: the value of money respects the
arbitrage bound `q_t ≥ ε` (`P_t ≤ P̲ = 1/ε`, finite at every date), money holdings `M_t > 0` can
only fall (dollars may be redeemed but are never sold), and (3.6) holds at every date with
`Mq` replaced by real balances `M_tq_t`. -/
def IsORPath (β u1 ε : ℝ) (vp : ℝ → ℝ) (q Mh : ℕ → ℝ) : Prop :=
  (∀ t, ε ≤ q t) ∧ (∀ t, 0 < Mh t) ∧ (∀ t, Mh (t + 1) ≤ Mh t) ∧
    ∀ t, (u1 - vp (Mh t * q t)) * q t = β * u1 * q (t + 1)

/-- Cochrane (2023), p. 624 (the step in Obstfeld–Rogoff's argument): along such a path real
balances `r_t = M_tq_t` satisfy `v'(r_t) < u'(y)` and
`βu'(y) r_{t+1} ≤ (u'(y) − v'(r_t)) r_t`. -/
theorem or_balance_step {β u1 ε : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} (hβ : 0 < β) (hu : 0 < u1)
    (hε : 0 < ε) (hpath : IsORPath β u1 ε vp q Mh) (t : ℕ) :
    vp (Mh t * q t) < u1 ∧
      β * u1 * (Mh (t + 1) * q (t + 1)) ≤ (u1 - vp (Mh t * q t)) * (Mh t * q t) := by
  obtain ⟨hq, hM, hdec, heq⟩ := hpath
  have hqt : 0 < q t := lt_of_lt_of_le hε (hq t)
  have hqt1 : 0 < q (t + 1) := lt_of_lt_of_le hε (hq (t + 1))
  have h1 : 0 < (u1 - vp (Mh t * q t)) * q t := by rw [heq t]; positivity
  have h2 : vp (Mh t * q t) < u1 := by
    by_contra h; push Not at h
    have : (u1 - vp (Mh t * q t)) * q t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hqt.le
    linarith
  refine ⟨h2, ?_⟩
  have h3 : (u1 - vp (Mh t * q t)) * (Mh t * q t) = Mh t * (β * u1 * q (t + 1)) := by
    rw [← heq t]; ring
  rw [h3]
  have := mul_le_mul_of_nonneg_right (hdec t) (by positivity : (0 : ℝ) ≤ β * u1 * q (t + 1))
  nlinarith

/-- Cochrane (2023), p. 624, Obstfeld and Rogoff's claim "Suppose that `{P_t}` is an equilibrium
path with `P_0 > P̿` … `{P_t}` is not an equilibrium path", in their finite-price sense: if `v'`
is strictly decreasing and continuous, `v'(m̿) = (1−β)u'(y)` (steady state) and
`v'(m̄) = u'(y)` (terminal level), then along every `IsORPath` real balances never fall below
`m̿`: `M_tq_t ≥ m̿` for all `t`. With `M_0 = M` this is `P_0 ≤ P̿ = M/m̿`. (The only role of
`ε > 0` is that it keeps every price level finite.) -/
theorem or_no_hyperinflation {β u1 ε mss mbar : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} (hβ : 0 < β)
    (hu : 0 < u1) (hε : 0 < ε) (hanti : StrictAntiOn vp (Set.Ioi 0))
    (hcont : ContinuousOn vp (Set.Ioi 0)) (hmss : 0 < mss) (hss : vp mss = (1 - β) * u1)
    (hmbar : 0 < mbar) (hbar : vp mbar = u1) (hpath : IsORPath β u1 ε vp q Mh) :
    ∀ t, mss ≤ Mh t * q t := by
  set r : ℕ → ℝ := fun t => Mh t * q t with hr
  have hrpos : ∀ t, 0 < r t := fun t =>
    mul_pos (hpath.2.1 t) (lt_of_lt_of_le hε (hpath.1 t))
  have hstep := or_balance_step hβ hu hε hpath
  -- real balances stay above the terminal level
  have habove : ∀ t, mbar < r t := by
    intro t
    have h := (hstep t).1
    by_contra hc; push Not at hc
    rcases hc.lt_or_eq with hc | hc
    · have := hanti (hrpos t) hmbar hc
      have : vp (r t) < u1 := h
      linarith
    · have : vp (r t) < u1 := h
      rw [hc, hbar] at this; exact lt_irrefl _ this
  -- below the steady state, real balances fall
  have hdown : ∀ x, 0 < x → x < mss → (u1 - vp x) * x < β * u1 * x := by
    intro x hx hxl
    have := hanti hx hmss hxl
    nlinarith
  intro t0
  by_contra hcon
  push Not at hcon
  set y : ℕ → ℝ := fun n => r (t0 + n) with hy
  have hfall : ∀ n, y n < mss ∧ y (n + 1) < y n := by
    intro n
    induction n with
    | zero =>
      have h1 := (hstep t0).2
      have h2 := hdown (r t0) (hrpos t0) hcon
      refine ⟨hcon, ?_⟩
      have : β * u1 * r (t0 + 1) < β * u1 * r t0 := lt_of_le_of_lt h1 h2
      exact lt_of_mul_lt_mul_left this (by positivity)
    | succ n ih =>
      have h0 : y (n + 1) < mss := lt_trans ih.2 ih.1
      have h1 := (hstep (t0 + (n + 1))).2
      have h2 := hdown (r (t0 + (n + 1))) (hrpos _) h0
      refine ⟨h0, ?_⟩
      have : β * u1 * r (t0 + (n + 1) + 1) < β * u1 * r (t0 + (n + 1)) := lt_of_le_of_lt h1 h2
      exact lt_of_mul_lt_mul_left this (by positivity)
  have hanti' : Antitone y := antitone_nat_of_succ_le fun n => (hfall n).2.le
  have hbdd : BddBelow (Set.range y) := ⟨mbar, by rintro _ ⟨n, rfl⟩; exact (habove _).le⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ n, y n with hL
  have hLbar : mbar ≤ L := le_ciInf fun n => (habove _).le
  have hL0 : 0 < L := lt_of_lt_of_le hmbar hLbar
  have hLss : L < mss := lt_of_le_of_lt (ciInf_le hbdd 0) (hfall 0).1
  have hc : ContinuousAt (fun x => (u1 - vp x) * x) L :=
    (continuousAt_const.sub (hcont.continuousAt (Ioi_mem_nhds hL0))).mul continuousAt_id
  have h1 : Tendsto (fun n => (u1 - vp (y n)) * y n) atTop (𝓝 ((u1 - vp L) * L)) :=
    hc.tendsto.comp hlim
  have h2 : Tendsto (fun n => β * u1 * y (n + 1)) atTop (𝓝 (β * u1 * L)) :=
    ((tendsto_add_atTop_iff_nat 1).mpr hlim).const_mul _
  have hle : β * u1 * L ≤ (u1 - vp L) * L :=
    le_of_tendsto_of_tendsto' h2 h1 fun n => by
      have := (hstep (t0 + n)).2
      simpa [hy, hr, add_assoc] using this
  have := hdown L hL0 hLss
  linarith

/-- Cochrane (2023), p. 624 and p. 625, "two-way conversion": if the government also sells money
at `P̲ = 1/ε`, the constant value `q = ε` with money holdings `m̿/ε` satisfies (3.6) — the
inflation stops and is an equilibrium. -/
theorem two_way_steady {β u1 ε mss : ℝ} {vp : ℝ → ℝ} (hε : 0 < ε)
    (hss : vp mss = (1 - β) * u1) :
    (u1 - vp (mss / ε * ε)) * ε = β * u1 * ε := by
  rw [div_mul_cancel₀ mss hε.ne', hss]; ring

/-- Cochrane (2023), p. 625, "Obstfeld and Rogoff's government refuses to increase the money
stock": when the backing is small, `Mε < m̿`, the two-way steady state needs money holdings
`m̿/ε > M`, i.e. the government must sell money — excluded by one-way redemption. -/
theorem two_way_needs_sale {ε M mss : ℝ} (hε : 0 < ε) (hsmall : M * ε < mss) : M < mss / ε := by
  rw [lt_div_iff₀ hε]; exact hsmall

/-! ## Cochrane's demonetised Walrasian equilibrium -/

/-- Cochrane (2023), pp. 625–627, the telescoping behind household optimality. Let `w_t` be the
value at `t + 1` of a dollar carried out of `t` (`w_t = q_{t+1}` for `t < T`, `w_T = ε`, the
redemption value, since `q_{T+1} = 0`). If `(u₁ − v'_t)q_t = βu₁w_t` for `t ≤ T` and the
deviations `d_t` of money holdings and `e_t` of consumption satisfy the budget identities
`e_0 = −q_0d_0`, `e_{t+1} = −q_{t+1}d_{t+1} + w_td_t`, then
`∑_{t≤n} βᵗ(u₁e_t + v'_tq_td_t) = −β^{n+1}u₁w_nd_n` for `n ≤ T`. -/
theorem cochrane_sum_identity {β u1 : ℝ} {T : ℕ} {q w vpt d e : ℕ → ℝ}
    (hfoc : ∀ t ≤ T, (u1 - vpt t) * q t = β * u1 * w t) (he0 : e 0 = -(q 0 * d 0))
    (he : ∀ t < T, e (t + 1) = -(q (t + 1) * d (t + 1)) + w t * d t) :
    ∀ n ≤ T, ∑ t ∈ Finset.range (n + 1), β ^ t * (u1 * e t + vpt t * q t * d t) =
      -(β ^ (n + 1) * u1 * w n * d n) := by
  intro n
  induction n with
  | zero =>
    intro h0
    rw [Finset.sum_range_one, he0]
    have := hfoc 0 h0
    have h : vpt 0 * q 0 = u1 * q 0 - β * u1 * w 0 := by linarith
    simp only [pow_zero, one_mul]
    linear_combination d 0 * h
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega), he k (by omega)]
    have := hfoc (k + 1) hk
    have h : vpt (k + 1) * q (k + 1) = u1 * q (k + 1) - β * u1 * w (k + 1) := by linarith
    rw [pow_succ]
    linear_combination (β ^ k * β) * d (k + 1) * h

/-- Cochrane (2023), pp. 625–627, "Given a price level sequence such that `P_{T+1} = ∞`, it is
optimal for consumers to sell all their money to the government … This is an equilibrium, in
the conventional definition of Walrasian equilibrium." Price-taking household problem with a
one-time redemption at `T + 1` of the money carried out of `T`: values `q_0, …, q_T > 0`,
`q_{T+1} = 0`; candidate plan `c_t = y`, money `M` held through `T`, all redeemed at `T + 1`
(financed by the tax `εM`). If `u` and `v` are concave (supergradient form at the candidate) and
(3.6) holds for `t < T` with the redemption condition at `T`, then every budget-feasible plan
`(c, H)` with `H_t ≥ 0` gives no more utility than the candidate. -/
theorem cochrane_household_optimal {β u1 ε y M : ℝ} {T : ℕ} {u v vp : ℝ → ℝ}
    {q c H : ℕ → ℝ} (hβ : 0 < β) (hq : ∀ t, 0 ≤ q t)
    (hu : ∀ x, u x ≤ u y + u1 * (x - y))
    (hv : ∀ t x, 0 ≤ x → v x ≤ v (M * q t) + vp (M * q t) * (x - M * q t))
    (hfoc : ∀ t < T, (u1 - vp (M * q t)) * q t = β * u1 * q (t + 1))
    (hfocT : (u1 - vp (M * q T)) * q T = β * u1 * ε)
    (hH : ∀ t, 0 ≤ H t)
    (hb0 : c 0 + q 0 * H 0 = y + q 0 * M)
    (hb : ∀ t < T, c (t + 1) + q (t + 1) * H (t + 1) = y + q (t + 1) * H t)
    (hbT : c (T + 1) = y + ε * H T - ε * M) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (u (c t) + v (q t * H t)) + β ^ (T + 1) * u (c (T + 1))
      ≤ ∑ t ∈ Finset.range (T + 1), β ^ t * (u y + v (q t * M)) + β ^ (T + 1) * u y := by
  set w : ℕ → ℝ := fun t => if t < T then q (t + 1) else ε with hw
  set d : ℕ → ℝ := fun t => H t - M with hd
  set e : ℕ → ℝ := fun t => c t - y with he
  have hfoc' : ∀ t ≤ T, (u1 - vp (M * q t)) * q t = β * u1 * w t := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · simp only [hw, h, ↓reduceIte]; exact hfoc t h
    · simp only [hw, h, lt_irrefl, ↓reduceIte]; exact hfocT
  have he0 : e 0 = -(q 0 * d 0) := by simp only [he, hd]; linarith
  have he' : ∀ t < T, e (t + 1) = -(q (t + 1) * d (t + 1)) + w t * d t := by
    intro t ht
    have := hb t ht
    simp only [he, hd, hw, ht, ↓reduceIte]
    linarith
  have hid := cochrane_sum_identity (vpt := fun t => vp (M * q t)) hfoc' he0 he' T le_rfl
  have hwT : w T = ε := by simp [hw]
  rw [hwT] at hid
  -- termwise concavity bounds
  have hterm : ∀ t, β ^ t * (u (c t) + v (q t * H t)) ≤ β ^ t * (u y + v (q t * M)) +
      β ^ t * (u1 * e t + vp (M * q t) * q t * d t) := by
    intro t
    have h1 := hu (c t)
    have h2 := hv t (q t * H t) (mul_nonneg (hq t) (hH t))
    have hp : 0 ≤ β ^ t := by positivity
    have : u (c t) + v (q t * H t) ≤ u y + v (q t * M) + (u1 * e t + vp (M * q t) * q t * d t) := by
      simp only [he, hd]
      rw [mul_comm (q t) M] at *
      nlinarith
    nlinarith
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (T + 1)) => hterm t
  rw [Finset.sum_add_distrib, hid] at hsum
  have hlast : β ^ (T + 1) * u (c (T + 1)) ≤ β ^ (T + 1) * u y + β ^ (T + 1) * u1 * ε * d T := by
    have h1 := hu (c (T + 1))
    have hp : 0 ≤ β ^ (T + 1) := by positivity
    have h2 : c (T + 1) - y = ε * d T := by simp only [hd]; rw [hbT]; ring
    rw [h2] at h1
    nlinarith
  linarith

/-- Cochrane (2023), pp. 626–627: Cochrane's equilibrium has `q_{T+1} = 0 < ε`, i.e.
`P_{T+1} = ∞ > P̲`, violating Obstfeld and Rogoff's arbitrage bound ("the market price of money
on date `T + 1` … will be at least `ε`"); so it is not an `IsORPath`. -/
theorem cochrane_violates_or_bound {β u1 ε : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} {T : ℕ}
    (hε : 0 < ε) (hqT : q (T + 1) = 0) : ¬ IsORPath β u1 ε vp q Mh := by
  intro h
  have := h.1 (T + 1)
  rw [hqT] at this
  linarith

/-- Cochrane (2023), p. 626 and Obstfeld–Rogoff (2021) as quoted on p. 627, "Any individual who
deviates … and instead carries $1 into period `T + 1` will be able to sell it … to the government
for ε": if the redemption offer also stands for dollars acquired at `T + 1`, where `q_{T+1} = 0`,
then for every budget-feasible choice at `T + 1`, `T + 2`, acquiring one more (free) dollar and
redeeming it is feasible and strictly better (with `u` strictly increasing): the price-taking
household has no optimum, so under this reading the demonetised path is not a Walrasian
equilibrium. This is the precise content of the dispute: Cochrane's equilibrium requires that
money bought at an infinite price level cannot be redeemed. -/
theorem standing_redemption_no_optimum {β ε R y2 : ℝ} {u : ℝ → ℝ} {v : ℝ → ℝ} (hβ : 0 < β)
    (hε : 0 < ε) (hu : StrictMono u) (c1 H1 : ℝ) (hb1 : c1 + 0 * H1 = R) :
    c1 + 0 * (H1 + 1) = R ∧
      β * (u c1 + v (0 * H1)) + β ^ 2 * u (y2 + ε * H1) <
        β * (u c1 + v (0 * (H1 + 1))) + β ^ 2 * u (y2 + ε * (H1 + 1)) := by
  refine ⟨by simpa using hb1, ?_⟩
  have h1 : u (y2 + ε * H1) < u (y2 + ε * (H1 + 1)) := hu (by nlinarith)
  simp only [zero_mul]
  have : 0 < β ^ 2 := by positivity
  nlinarith

/-- Cochrane (2023), Figure 3.2: `v(m) = 2√m` is concave in supergradient form,
`2√x ≤ 2√m₀ + v'(m₀)(x − m₀)` for `x ≥ 0`, `m₀ > 0`. -/
theorem fig32_v_supergradient {m0 x : ℝ} (hm0 : 0 < m0) (hx : 0 ≤ x) :
    2 * Real.sqrt x ≤ 2 * Real.sqrt m0 + figVp m0 * (x - m0) := by
  unfold figVp
  have hs : 0 < Real.sqrt m0 := Real.sqrt_pos.mpr hm0
  have h1 := Real.sq_sqrt hm0.le
  have h2 := Real.sq_sqrt hx
  have hr := Real.sqrt_nonneg x
  rw [← h1, ← h2]
  rw [← sub_nonneg]
  have : 2 * Real.sqrt m0 + 1 / Real.sqrt m0 * (Real.sqrt x ^ 2 - Real.sqrt m0 ^ 2) -
      2 * Real.sqrt x = (Real.sqrt x - Real.sqrt m0) ^ 2 / Real.sqrt m0 := by
    field_simp; ring
  rw [h1, h2] at this ⊢
  rw [this]
  positivity

/-- Cochrane (2023), Figure 3.2, "ε = 0.5" (Cochrane's equilibrium): for every `T`, the values
`q_t = M/P_t = b^{T+1−t}(1/2)` (`M = 1`, `t ≤ T`) are at least one, satisfy (3.6) for `t < T`,
and the redemption condition `(u' − v'(q_T))q_T = βu'ε` at `T` (`u' = 1`, `β = ε = 1/2`). -/
theorem fig32_cochrane_path (T : ℕ) :
    (∀ t ≤ T, 1 ≤ fig32_back^[T + 1 - t] (1 / 2)) ∧
      (∀ t < T, (1 - figVp (1 * fig32_back^[T + 1 - t] (1 / 2))) *
          fig32_back^[T + 1 - t] (1 / 2) = 1 / 2 * 1 * fig32_back^[T + 1 - (t + 1)] (1 / 2)) ∧
      (1 - figVp (1 * fig32_back^[T + 1 - T] (1 / 2))) * fig32_back^[T + 1 - T] (1 / 2) =
        1 / 2 * 1 * (1 / 2) := by
  have hge : ∀ n, 0 ≤ fig32_back^[n] (1 / 2) ∧ (0 < n → 1 ≤ fig32_back^[n] (1 / 2)) := by
    intro n
    induction n with
    | zero => exact ⟨by norm_num, fun h => absurd h (lt_irrefl 0)⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (fig32_back_spec ih.1).1
      exact ⟨by linarith, fun _ => this⟩
  refine ⟨fun t ht => (hge _).2 (by omega), fun t ht => ?_, ?_⟩
  · have hsplit : T + 1 - t = (T + 1 - (t + 1)) + 1 := by omega
    rw [one_mul, hsplit, Function.iterate_succ_apply']
    exact (fig32_back_spec (hge _).1).2.1
  · rw [show T + 1 - T = 0 + 1 by omega, Function.iterate_succ_apply', Function.iterate_zero_apply,
      one_mul]
    exact (fig32_back_spec (by norm_num)).2.1

/-- Cochrane (2023), pp. 624–627, Figure 3.2 instance of `cochrane_household_optimal`: with
`u(c) = c`, `v(m) = 2√m`, `M = 1`, `β = ε = 1/2`, for every `T` the demonetised path
`q_t = b^{T+1−t}(1/2)` (`t ≤ T`), `q_{T+1} = 0`, with all money redeemed at `T + 1`, is optimal
for the price-taking household among all budget-feasible plans. -/
theorem fig32_cochrane_optimal (T : ℕ) {y : ℝ} {c H : ℕ → ℝ} (hH : ∀ t, 0 ≤ H t)
    (hb0 : c 0 + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) 0 * H 0 =
      y + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) 0 * 1)
    (hb : ∀ t < T, c (t + 1) +
      (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) (t + 1) * H (t + 1) =
      y + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) (t + 1) * H t)
    (hbT : c (T + 1) = y + 1 / 2 * H T - 1 / 2 * 1) :
    ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * (c t + 2 * Real.sqrt
        ((fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) t * H t)) +
        (1 / 2 : ℝ) ^ (T + 1) * c (T + 1) ≤
      ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * (y + 2 * Real.sqrt
        ((fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) t * 1)) +
        (1 / 2 : ℝ) ^ (T + 1) * y := by
  set q : ℕ → ℝ := fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0 with hq
  obtain ⟨hge, hfoc, hfocT⟩ := fig32_cochrane_path T
  have hqT : ∀ t ≤ T, q t = fig32_back^[T + 1 - t] (1 / 2) := fun t ht => by
    simp only [hq, ht, ↓reduceIte]
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t
    by_cases ht : t ≤ T
    · rw [hqT t ht]; linarith [hge t ht]
    · simp only [hq, ht, ↓reduceIte, le_refl]
  have hpos : ∀ t ≤ T, 0 < 1 * q t := fun t ht => by rw [hqT t ht]; linarith [hge t ht]
  -- the concavity bound for `v` is needed only at dates `t ≤ T`; extend it trivially beyond
  have key := cochrane_household_optimal (β := 1 / 2) (u1 := 1) (ε := 1 / 2) (y := y) (M := 1)
    (T := T) (u := id) (v := fun x => 2 * Real.sqrt x)
    (vp := fun x => if 0 < x then figVp x else 0) (q := fun t => if t ≤ T then q t else 1)
    (c := c) (H := H) (by norm_num)
    (fun t => by by_cases ht : t ≤ T <;> simp only [ht, ↓reduceIte] <;> [exact hq0 t; norm_num])
    (fun x => by simp)
    (fun t x hx => by
      have hp : 0 < 1 * (if t ≤ T then q t else 1) := by
        by_cases ht : t ≤ T
        · simp only [ht, ↓reduceIte]; exact hpos t ht
        · simp only [ht, ↓reduceIte]; norm_num
      simp only [hp, ↓reduceIte]
      exact fig32_v_supergradient hp hx)
    (fun t ht => by
      have ht' : t ≤ T := ht.le
      have ht1 : t + 1 ≤ T := ht
      have hp := hpos t ht'
      simp only [ht', ht1, ↓reduceIte, hp]
      rw [hqT t ht', hqT (t + 1) ht1]
      have := hfoc t ht
      rw [one_mul] at this ⊢
      linarith)
    (by
      have hp := hpos T le_rfl
      simp only [le_refl, ↓reduceIte, hp]
      rw [hqT T le_rfl]
      have := hfocT
      rw [one_mul] at this ⊢
      linarith)
    hH
    (by simp only [Nat.zero_le, ↓reduceIte]; exact hb0)
    (fun t ht => by
      have ht1 : t + 1 ≤ T := ht
      simp only [ht1, ↓reduceIte]; exact hb t ht)
    hbT
  have hsum : ∀ (f : ℕ → ℝ → ℝ), ∑ t ∈ Finset.range (T + 1), f t (if t ≤ T then q t else 1) =
      ∑ t ∈ Finset.range (T + 1), f t (q t) := by
    intro f
    refine Finset.sum_congr rfl fun t ht => ?_
    have : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    simp only [this, ↓reduceIte]
  have e1 := hsum (fun t z => (1 / 2 : ℝ) ^ t * (id (c t) + 2 * Real.sqrt (z * H t)))
  have e2 := hsum (fun t z => (1 / 2 : ℝ) ^ t * (id y + 2 * Real.sqrt (z * 1)))
  rw [e1, e2] at key
  simpa using key

end Cochrane.Monetarism.ObstfeldRogoff

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonseparable utility and more indeterminacy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3, §3.2.4
"Nonseparable utility and more indeterminacy", eqs. (3.7)–(3.8) and pp. 629–632 (with the remark
on p. 445 of §19.3). Perfect foresight.

## Main results

* (3.7)–(3.8): `foc38_iff`; the "usual approximation, precise in continuous time": the exact
  derivative of the log discount factor `log(βu_c(ce^a, me^b)/u_c(c, m))` at `(0, 0)` is
  `−γa − ηb` with `γ = −cu_cc/u_c`, `η = −mu_cm/u_c` (`sdf_log_hasFDerivAt`), so
  `log(1 + r^f)` has derivative `γa + ηb` and value `log(1+δ)` (`rf_log_hasFDerivAt`). With
  log money growth the coefficient is `−mu_cm/u_c`; the printed `η = −u_cm/u_c` is the
  coefficient of a level change `Δm` (`sdf_level_hasDerivAt`). The continuous-time footnote:
  `ct_footnote`.
* Obstfeld (1984), `u = −c^{−a}m^{−b}`: exact partials `obs_uc`, `obs_um` (the printed
  `u_c = ac^{−a−1}m^{b}`, `u_m = bc^{a}m^{−b−1}` have sign typos: `obs_printed_typo`),
  `obs_mrs`, the first-order condition `obs_foc`, the equilibrium map `obs_map_iff`, the steady
  state `obs_steady_iff`, its relative form `obs_relative`.
* Linearisation, survey error **E19**: the exact derivative of `m_{t+1}/m_t` at `m̄` is
  `i/((1−b)m̄) = (b/a)(1+i)/((1−b)m̄²)` (`obs_ratio_hasDerivAt`), missing the factor
  `(1+δ)(1+µ) = 1+i` in print (`e19_printed_coefficient`); the map `m ↦ m_{t+1}` has slope
  `1 − i/(b−1)` (`obs_map_hasDerivAt`). The phase diagram cuts from above iff `b > 1`
  (`obs_cuts_from_above_iff`), but local stability holds iff `b > 1 + i/2`
  (`obs_stable_iff`); counterexample `b = 1.04`, `i = 0.1025` (`e19_counterexample`).
  General local dynamics: `local_contraction`, `local_repulsion` (corollaries of the orbit
  lemmas of `MoneyTargetingDynamics`); consequences:
  `obs_multiple_stable` (a continuum of convergent equilibria satisfying the TVC) and
  `obs_locally_unique` (`1 < b < 1 + i/2`: only the steady state stays nearby).
* CES money in utility (p. 632): `ces_uc`, `ces_um`, `ces_uc_form`, `ces_sdf`,
  `ces_sdf_const`, `ces_mrs`, `ces_money_demand_iff`, `ces_income_elasticity`,
  `ces_interest_elasticity`.
-/

namespace Cochrane.Monetarism.Nonseparable

open Filter Topology

/-! ## (3.7)–(3.8) and the discount factor -/

/-- Cochrane (2023), eq. (3.8), p. 630: `u_m/u_c = i/(1+i) = 1 − Q` with `Q = 1/(1+i)`. -/
theorem foc38_iff {i : ℝ} (hi : 1 + i ≠ 0) : i / (1 + i) = 1 - 1 / (1 + i) := by
  field_simp; ring

/-- Cochrane (2023), p. 630, "The usual approximation, precise in continuous time": with
`u_c` differentiable at `(c, m)` (derivative `L`, so `u_cc = L(1,0)`, `u_cm = L(0,1)`) and
positive there, the log discount factor `log(βu_c(ce^a, me^b)/u_c(c, m))` as a function of log
consumption growth `a` and log money growth `b` has exact derivative `−γa − ηb` at `(0, 0)`,
`γ = −cu_cc/u_c`, `η = −mu_cm/u_c`, and value `log β`. -/
theorem sdf_log_hasFDerivAt {β c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hβ : 0 < β)
    (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ =>
        Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) D (0, 0) ∧
      (∀ a b, D (a, b) = -(-(c * L (1, 0)) / Uc (c, m) * a) - -(m * L (0, 1)) / Uc (c, m) * b) ∧
      Real.log (β * Uc (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) / Uc (c, m)) =
        Real.log β := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => c * Real.exp p.1)
      (c • (Real.exp (0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) (0 : ℝ × ℝ) :=
    (hasFDerivAt_fst.exp).const_mul c
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => m * Real.exp p.2)
      (m • (Real.exp (0 : ℝ × ℝ).2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) (0 : ℝ × ℝ) :=
    (hasFDerivAt_snd.exp).const_mul m
  have hg := h1.prodMk h2
  have hU' : HasFDerivAt Uc L (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) := by
    simpa using hU
  have hcomp := hU'.comp (0 : ℝ × ℝ) hg
  have hf := hcomp.const_mul (β / Uc (c, m))
  have hval :
      β / Uc (c, m) * (Uc ∘ fun x : ℝ × ℝ => (c * Real.exp x.1, m * Real.exp x.2)) 0 = β := by
    simp only [Function.comp_apply, Prod.fst_zero, Prod.snd_zero, Real.exp_zero, mul_one]
    field_simp
  have hlog := hf.log (by rw [hval]; exact hβ.ne')
  have hfun : (fun p : ℝ × ℝ =>
      Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) =
      fun p => Real.log (β / Uc (c, m) *
        (Uc ∘ fun x : ℝ × ℝ => (c * Real.exp x.1, m * Real.exp x.2)) p) := by
    funext p; simp only [Function.comp_apply]; ring_nf
  rw [hfun]
  refine ⟨_, hlog, fun a b => ?_, ?_⟩
  · rw [hval]
    have hL : L (c * a, m * b) = c * a * L (1, 0) + m * b * L (0, 1) := by
      have : ((c * a, m * b) : ℝ × ℝ) =
          (c * a) • ((1 : ℝ), (0 : ℝ)) + (m * b) • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [Prod.fst_zero, Real.exp_zero, one_smul, Prod.snd_zero,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
      ContinuousLinearMap.coe_snd']
    rw [hL]
    field_simp
    ring
  · simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, mul_one]
    congr 1
    field_simp

/-- Cochrane (2023), p. 630, `r^f ≈ δ + γE_t(Δc_{t+1}) + ηE_t(Δm_{t+1})`, exact form under
perfect foresight: `log(1 + r^f) = −log(βu_c(ce^a, me^b)/u_c(c, m))` has value `log(1+δ)` at
`(0, 0)` when `β = 1/(1+δ)`, and derivative `γa + ηb`. -/
theorem rf_log_hasFDerivAt {β δ c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hδ : 0 < 1 + δ)
    (hβ : β = 1 / (1 + δ)) (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ =>
        -Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) D (0, 0) ∧
      (∀ a b, D (a, b) = -(c * L (1, 0)) / Uc (c, m) * a + -(m * L (0, 1)) / Uc (c, m) * b) ∧
      -Real.log (β * Uc (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) / Uc (c, m)) =
        Real.log (1 + δ) := by
  have hβ0 : 0 < β := by rw [hβ]; positivity
  obtain ⟨D, hD, hDab, hval⟩ := sdf_log_hasFDerivAt hβ0 hpos hU
  refine ⟨-D, hD.neg, fun a b => ?_, ?_⟩
  · change -(D (a, b)) = _
    rw [hDab]; ring
  · rw [hval, hβ, one_div, Real.log_inv, neg_neg]

/-- Cochrane (2023), p. 630 (survey note on the printed `η = −u_cm/u_c`): for a level change
`m' = m + b` the log discount factor has derivative `u_cm/u_c = −(−u_cm/u_c)` — the printed `η`
is the coefficient of a level change, while for log money growth (as in the footnote,
`m u_cm/u_c · dm/m`) it is `−m u_cm/u_c` (`sdf_log_hasFDerivAt`). -/
theorem sdf_level_hasDerivAt {β c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hβ : 0 < β)
    (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    HasDerivAt (fun b => Real.log (β * Uc (c, m + b) / Uc (c, m))) (L (0, 1) / Uc (c, m)) 0 := by
  have hpath : HasDerivAt (fun b : ℝ => (c, m + b)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const 0 c).prodMk ((hasDerivAt_id 0).const_add m)
  have hU' : HasFDerivAt Uc L (c, m + 0) := by simpa using hU
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := Uc) (l' := L) (f := fun b : ℝ => (c, m + b))
    (0 : ℝ) hU' hpath
  have hf := (hcomp.const_mul (β / Uc (c, m))).log (by
    simp only [Function.comp_apply, add_zero]; field_simp; exact hβ.ne')
  have hfun : (fun b => Real.log (β * Uc (c, m + b) / Uc (c, m))) =
      fun b => Real.log (β / Uc (c, m) * (Uc ∘ fun b : ℝ => (c, m + b)) b) := by
    funext b; simp only [Function.comp_apply]; ring_nf
  rw [hfun]
  convert hf using 1
  simp only [Function.comp_apply, add_zero]
  field_simp

/-- Cochrane (2023), p. 630, footnote 1: along differentiable paths `c(t), m(t) > 0`,
`d log(e^{−δt}u_c(c_t, m_t))/dt = −δ + (c u_cc/u_c)(ċ/c) + (m u_cm/u_c)(ṁ/m)`. -/
theorem ct_footnote {δ t c' m' : ℝ} {c m : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (hc : HasDerivAt c c' t) (hm : HasDerivAt m m' t) (hcpos : 0 < c t) (hmpos : 0 < m t)
    (hpos : 0 < Uc (c t, m t)) (hU : HasFDerivAt Uc L (c t, m t)) :
    HasDerivAt (fun s => Real.log (Real.exp (-δ * s) * Uc (c s, m s)))
      (-δ + c t * L (1, 0) / Uc (c t, m t) * (c' / c t) +
        m t * L (0, 1) / Uc (c t, m t) * (m' / m t)) t := by
  have hpath : HasDerivAt (fun s => (c s, m s)) (c', m') t := hc.prodMk hm
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := Uc) (l' := L) (f := fun s => (c s, m s)) t
    hU hpath
  have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * t) * (-δ * 1)) t :=
    ((hasDerivAt_id t).const_mul (-δ)).exp
  have hprod := he.mul hcomp
  have hne : Real.exp (-δ * t) * (Uc ∘ fun s => (c s, m s)) t ≠ 0 := by
    change Real.exp (-δ * t) * Uc (c t, m t) ≠ 0
    positivity
  have hlog := hprod.log hne
  have hL : L (c', m') = c' * L (1, 0) + m' * L (0, 1) := by
    have : ((c', m') : ℝ × ℝ) = c' • ((1 : ℝ), (0 : ℝ)) + m' • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  convert hlog using 1
  · rfl
  · change _ = (Real.exp (-δ * t) * (-δ * 1) * Uc (c t, m t) + Real.exp (-δ * t) * L (c', m')) /
      (Real.exp (-δ * t) * Uc (c t, m t))
    rw [hL]
    field_simp
    ring

/-! ## Obstfeld (1984): `u(c, m) = −c^{−a}m^{−b}` -/

/-- Cochrane (2023), p. 631: `u_c = a c^{−a−1}m^{−b}` for `u(c, m) = −c^{−a}m^{−b}`, `c > 0`. -/
theorem obs_uc {a b c m : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c => -(c ^ (-a) * m ^ (-b))) (a * c ^ (-a - 1) * m ^ (-b)) c := by
  have h := ((Real.hasDerivAt_rpow_const (p := -a) (Or.inl hc.ne')).mul_const (m ^ (-b))).neg
  convert h using 1
  ring

/-- Cochrane (2023), p. 631: `u_m = b c^{−a}m^{−b−1}`, `m > 0`. -/
theorem obs_um {a b c m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun m => -(c ^ (-a) * m ^ (-b))) (b * c ^ (-a) * m ^ (-b - 1)) m := by
  have h := ((Real.hasDerivAt_rpow_const (p := -b) (Or.inl hm.ne')).const_mul (c ^ (-a))).neg
  convert h using 1
  ring

/-- Cochrane (2023), p. 631 (typo): the printed partials `u_c = ac^{−a−1}m^{b}` and
`u_m = bc^{a}m^{−b−1}` disagree with the exact ones: at `a = b = 1`, `c = m = 2` the printed
`u_c` is `1/2` against `1/8`, and the printed `u_m` is `1/2` against `1/8`. -/
theorem obs_printed_typo :
    (1 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ) - 1) * (2 : ℝ) ^ (1 : ℝ) ≠
        1 * (2 : ℝ) ^ (-(1 : ℝ) - 1) * (2 : ℝ) ^ (-(1 : ℝ)) ∧
      (1 : ℝ) * (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ) - 1) ≠
        1 * (2 : ℝ) ^ (-(1 : ℝ)) * (2 : ℝ) ^ (-(1 : ℝ) - 1) := by
  have h1 : (2 : ℝ) ^ (-(1 : ℝ) - 1) = 1 / 4 := by
    rw [show -(1 : ℝ) - 1 = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
  have h2 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  rw [h1, h2, Real.rpow_one]
  norm_num

/-- Cochrane (2023), p. 631: the marginal rate of substitution `u_m/u_c = (b/a)(c/m)`. -/
theorem obs_mrs {a b c m : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) :
    b * c ^ (-a) * m ^ (-b - 1) / (a * c ^ (-a - 1) * m ^ (-b)) = b / a * (c / m) := by
  rw [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hm.ne']
  have : 0 < c ^ (-a) := Real.rpow_pos_of_pos hc _
  have : 0 < m ^ (-b) := Real.rpow_pos_of_pos hm _
  field_simp

/-- Cochrane (2023), p. 631: the ratio of marginal utilities of consumption across dates,
`u_c(c', m')/u_c(c, m) = (c'/c)^{−a−1}(m'/m)^{−b}`. -/
theorem obs_uc_ratio {a b c m c' m' : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) (hc' : 0 < c')
    (hm' : 0 < m') :
    a * c' ^ (-a - 1) * m' ^ (-b) / (a * c ^ (-a - 1) * m ^ (-b)) =
      (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) := by
  rw [Real.div_rpow hc'.le hc.le, Real.div_rpow hm'.le hm.le]
  have : 0 < c ^ (-a - 1) := Real.rpow_pos_of_pos hc _
  have : 0 < m ^ (-b) := Real.rpow_pos_of_pos hm _
  field_simp

/-- Cochrane (2023), p. 631, "the first-order conditions give
`c_tb/(m_ta) = 1 − β(c_{t+1}/c_t)^{−a−1}(m_{t+1}/m_t)^{−b}P_t/P_{t+1}`": (3.8) with (3.7) under
perfect foresight, `u_m/u_c = 1 − βu_c(t+1)/u_c(t)·P_t/P_{t+1}`, for this utility. -/
theorem obs_foc {a b c m c' m' β Pr : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) (hc' : 0 < c')
    (hm' : 0 < m') :
    b * c ^ (-a) * m ^ (-b - 1) / (a * c ^ (-a - 1) * m ^ (-b)) =
        1 - β * (a * c' ^ (-a - 1) * m' ^ (-b) / (a * c ^ (-a - 1) * m ^ (-b))) * Pr ↔
      c * b / (m * a) = 1 - β * (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) * Pr := by
  rw [obs_mrs ha hc hm, obs_uc_ratio ha hc hm hc' hm',
    show b / a * (c / m) = c * b / (m * a) by field_simp,
    show β * ((c' / c) ^ (-a - 1) * (m' / m) ^ (-b)) * Pr =
      β * (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) * Pr by ring]

/-- Cochrane (2023), p. 631: with `y = c = 1` and money growth `µ`
(`P_t/P_{t+1} = (m_{t+1}/m_t)/(1+µ)`), the first-order condition reads
`(b/a)(1/m_t) = 1 − (β/(1+µ))(m_{t+1}/m_t)^{1−b}`, and for `b ≠ 1` this is equivalent to
`m_{t+1}/m_t = [(1+µ)/β · (1 − b/(am_t))]^{1/(1−b)}`. -/
theorem obs_map_iff {a b β μ m m' : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hm : 0 < m) (hm' : 0 < m') (hmb : b / a < m) :
    (b / (m * a) = 1 - β * (m' / m) ^ (-b) * ((m' / m) / (1 + μ)) ↔
      b / a * (1 / m) = 1 - β / (1 + μ) * (m' / m) ^ (1 - b)) ∧
    (b / a * (1 / m) = 1 - β / (1 + μ) * (m' / m) ^ (1 - b) ↔
      m' / m = ((1 + μ) / β * (1 - b / a * (1 / m))) ^ (1 / (1 - b))) := by
  have hr : 0 < m' / m := div_pos hm' hm
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hpow : (m' / m) ^ (-b) * (m' / m) = (m' / m) ^ (1 - b) := by
    rw [show 1 - b = -b + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  constructor
  · rw [← hpow]
    constructor <;> intro h
    · field_simp at h ⊢; linarith
    · field_simp at h ⊢; linarith
  · constructor
    · intro h
      have h2 : (m' / m) ^ (1 - b) = (1 + μ) / β * (1 - b / a * (1 / m)) := by
        field_simp at h ⊢; linarith
      rw [← h2, show 1 / (1 - b) = (1 - b)⁻¹ by ring, Real.rpow_rpow_inv hr.le h1b]
    · intro h
      have hbase : 0 < (1 + μ) / β * (1 - b / a * (1 / m)) := by
        have : b / a * (1 / m) < 1 := by
          rw [mul_one_div, div_lt_one hm]; exact hmb
        have := div_pos hμ hβ
        nlinarith
      have h2 : (m' / m) ^ (1 - b) = (1 + μ) / β * (1 - b / a * (1 / m)) := by
        rw [h, show 1 / (1 - b) = (1 - b)⁻¹ by ring, Real.rpow_inv_rpow hbase.le h1b]
      rw [h2]
      field_simp
      ring

/-- Cochrane (2023), p. 631: the gross growth of real balances
`[(1+δ)(1+µ)(1 − b/(am))]^{1/(1−b)}`, with `A = (1+δ)(1+µ) = 1 + i`. -/
noncomputable def obsRatio (a b A m : ℝ) : ℝ := (A * (1 - b / a * (1 / m))) ^ (1 / (1 - b))

/-- Cochrane (2023), p. 631: the equilibrium map `m_t ↦ m_{t+1} = m_t·obsRatio(m_t)`. -/
noncomputable def obsMap (a b A m : ℝ) : ℝ := m * obsRatio a b A m

/-- Cochrane (2023), p. 631, "The steady state is `1 = (1+δ)(1+µ)(1 − (b/a)(1/m̄))`": for
`A > 1`, this holds iff `m̄ = (b/a)·A/(A − 1)`, and then `m̄` is a fixed point of the map. -/
theorem obs_steady_iff {a b A ms : ℝ} (ha : 0 < a) (hA : 1 < A) (hms : 0 < ms) :
    (A * (1 - b / a * (1 / ms)) = 1 ↔ ms = b / a * A / (A - 1)) ∧
      (A * (1 - b / a * (1 / ms)) = 1 → obsMap a b A ms = ms) := by
  have hA1 : A - 1 ≠ 0 := by linarith
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · field_simp at h ⊢; linarith
  · rw [h]
    have hb : b ≠ 0 := by
      intro hb; rw [hb] at h; simp at h; linarith
    field_simp
    ring
  · unfold obsMap obsRatio; rw [h, Real.one_rpow, mul_one]

/-- Cochrane (2023), p. 631, "In terms of the steady state": if `A(1 − b/(am̄)) = 1` then
`A(1 − b/(am)) = (1 − b/(am))/(1 − b/(am̄))`. -/
theorem obs_relative {a b A ms m : ℝ} (hss : A * (1 - b / a * (1 / ms)) = 1) :
    A * (1 - b / a * (1 / m)) = (1 - b / a * (1 / m)) / (1 - b / a * (1 / ms)) := by
  have h : 1 - b / a * (1 / ms) ≠ 0 := by intro h0; rw [h0, mul_zero] at hss; norm_num at hss
  have hA : A = 1 / (1 - b / a * (1 / ms)) := by rw [eq_div_iff h]; exact hss
  rw [hA]; field_simp

/-- Cochrane (2023), p. 631, linearisation (survey **E19**, corrected): with
`A(1 − b/(am̄)) = 1`, `b ≠ 1`, the exact derivative of `m_{t+1}/m_t` at `m̄` is
`(b/a)·A/((1−b)m̄²) = (A − 1)/((1−b)m̄) = i/((1−b)m̄)`. -/
theorem obs_ratio_hasDerivAt {a b A ms : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hms : 0 < ms)
    (hss : A * (1 - b / a * (1 / ms)) = 1) :
    HasDerivAt (obsRatio a b A) ((A - 1) / ((1 - b) * ms)) ms ∧
      (A - 1) / ((1 - b) * ms) = b / a * A / ((1 - b) * ms ^ 2) := by
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hinv : HasDerivAt (fun m : ℝ => 1 / m) (-(1 / ms ^ 2)) ms := by
    have := hasDerivAt_inv hms.ne'
    simpa [one_div] using this
  have hbase : HasDerivAt (fun m => A * (1 - b / a * (1 / m))) (A * -(b / a * -(1 / ms ^ 2)))
      ms := ((hinv.const_mul (b / a)).const_sub 1).const_mul A
  have hpow := hbase.rpow_const (p := 1 / (1 - b)) (Or.inl (by rw [hss]; norm_num))
  have hkey : A * (b / a) = (A - 1) * ms := by
    field_simp at hss ⊢; linarith
  constructor
  · unfold obsRatio
    convert hpow using 1
    rw [hss, Real.one_rpow, mul_one,
      show A * -(b / a * -(1 / ms ^ 2)) = A * (b / a) / ms ^ 2 by ring, hkey]
    field_simp
  · rw [show b / a * A = A * (b / a) by ring, hkey]
    field_simp

/-- Cochrane (2023), p. 631 (survey **E19**): the printed coefficient `(b/a)(1/(1−b))/m̄²` omits
the factor `A = (1+δ)(1+µ)`: the exact one is `A` times it, so they differ whenever `A ≠ 1`
(and `b ≠ 0`). -/
theorem e19_printed_coefficient {a b A ms : ℝ} (ha : 0 < a) (hb0 : b ≠ 0) (hb : b ≠ 1)
    (hms : 0 < ms) (hA : A ≠ 1) :
    b / a * A / ((1 - b) * ms ^ 2) = A * (b / a * (1 / (1 - b)) / ms ^ 2) ∧
      b / a * A / ((1 - b) * ms ^ 2) ≠ b / a * (1 / (1 - b)) / ms ^ 2 := by
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have e : b / a * A / ((1 - b) * ms ^ 2) = A * (b / a * (1 / (1 - b)) / ms ^ 2) := by
    field_simp
  refine ⟨e, fun h => hA ?_⟩
  have hne : b / a * (1 / (1 - b)) / ms ^ 2 ≠ 0 := by
    have : b / a ≠ 0 := div_ne_zero hb0 ha.ne'
    positivity
  rw [e] at h
  have h2 : (A - 1) * (b / a * (1 / (1 - b)) / ms ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 hne

/-- Cochrane (2023), p. 631–632: the map `m_t ↦ m_{t+1}` has exact slope
`1 + (A−1)/(1−b) = 1 − i/(b − 1)` at the steady state. -/
theorem obs_map_hasDerivAt {a b A ms : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hms : 0 < ms)
    (hss : A * (1 - b / a * (1 / ms)) = 1) :
    HasDerivAt (obsMap a b A) (1 - (A - 1) / (b - 1)) ms := by
  obtain ⟨hR, -⟩ := obs_ratio_hasDerivAt ha hb hms hss
  have hR1 : obsRatio a b A ms = 1 := by unfold obsRatio; rw [hss, Real.one_rpow]
  have h := (hasDerivAt_id' ms).mul hR
  have hfun : obsMap a b A = fun m => m * obsRatio a b A m := rfl
  rw [hfun]
  convert h using 1
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hb1 : (b - 1) ≠ 0 := sub_ne_zero.mpr hb
  rw [hR1]
  field_simp
  ring

/-- Cochrane (2023), p. 631, "The phase diagram … can cut from above rather than below": with
`i = A − 1 > 0`, the slope `1 − i/(b−1)` at the steady state is below one iff `b > 1`. -/
theorem obs_cuts_from_above_iff {b i : ℝ} (hi : 0 < i) (hb : b ≠ 1) :
    1 - i / (b - 1) < 1 ↔ 1 < b := by
  constructor
  · intro h
    by_contra hcon; push Not at hcon
    have hlt : b - 1 < 0 := by rcases hcon.lt_or_eq with h' | h' <;> [linarith; exact absurd h' hb]
    have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi hlt
    linarith
  · intro h
    have : 0 < i / (b - 1) := div_pos hi (by linarith)
    linarith

/-- Cochrane (2023), pp. 631–632, survey error **E19** (corrected): with `i > 0`, `b ≠ 1`, the
steady state is locally stable (`|slope| < 1`) iff `b > 1 + i/2` — not merely `b > 1`. -/
theorem obs_stable_iff {b i : ℝ} (hi : 0 < i) (hb : b ≠ 1) :
    |1 - i / (b - 1)| < 1 ↔ 1 + i / 2 < b := by
  rw [abs_lt]
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi (by linarith)
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; linarith
  · have hb1 : 0 < b - 1 := by linarith
    constructor
    · rintro ⟨h, -⟩
      have : i / (b - 1) < 2 := by linarith
      rw [div_lt_iff₀ hb1] at this
      linarith
    · intro h
      refine ⟨?_, by have := div_pos hi hb1; linarith⟩
      have : i / (b - 1) < 2 := by rw [div_lt_iff₀ hb1]; linarith
      linarith

/-- Cochrane (2023), p. 632, "negative for `b > 1`. In that case, dynamics are stable"
(survey **E19**, counterexample): `δ = µ = 0.05` gives `i = 1.05² − 1 = 0.1025`; with `b = 1.04`
the slope is `1 − i/(b−1) = −1.5625`, of modulus above one: unstable although `b > 1`. -/
theorem e19_counterexample :
    (1.05 : ℝ) * 1.05 - 1 = 0.1025 ∧ (1 : ℝ) < 1.04 ∧
      1 - (0.1025 : ℝ) / (1.04 - 1) = -1.5625 ∧ 1 < |1 - (0.1025 : ℝ) / (1.04 - 1)| := by
  have h : 1 - (0.1025 : ℝ) / (1.04 - 1) = -1.5625 := by norm_num
  refine ⟨by norm_num, by norm_num, h, ?_⟩
  rw [h]; norm_num [abs_of_neg]

/-! ## Local dynamics of one-dimensional maps -/

/-- A general lemma (not in the book; the orbit form is
`MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one`, of which this is the iterate form): a
fixed point `x` of a map differentiable there with `|f'(x)| < 1` is locally attracting: for `y`
in some ball around `x`, the orbit never gets farther from `x` than `y` is, and converges to
`x`. -/
theorem local_contraction {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) (hfix : f x = x)
    (hd : |d| < 1) :
    ∃ r, 0 < r ∧ ∀ y, |y - x| < r →
      (∀ t, |f^[t] y - x| ≤ |y - x|) ∧ Tendsto (fun t => f^[t] y) atTop (𝓝 x) := by
  obtain ⟨r, hr, h⟩ := MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one hfix hf hd
  refine ⟨r, hr, fun y hy => ?_⟩
  have h' := h (fun t => f^[t] y) (fun t => Function.iterate_succ_apply' f t y) (by simpa)
  exact ⟨fun t => by simpa using h'.2.1 t, h'.2.2⟩

/-- A general lemma (not in the book; a corollary of
`MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv`): a fixed point `x` with `|f'(x)| > 1` is
locally repelling: in some ball around `x`, the only orbit that stays in the ball forever is the
constant orbit at `x`. -/
theorem local_repulsion {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) (hfix : f x = x)
    (hd : 1 < |d|) :
    ∃ r, 0 < r ∧ ∀ y : ℕ → ℝ, (∀ t, y (t + 1) = f (y t)) → (∀ t, |y t - x| < r) →
      ∀ t, y t = x := by
  obtain ⟨r, hr, h⟩ := MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv hfix hf hd
  refine ⟨r, hr, fun y hy hin t => ?_⟩
  have h0 : y 0 = x := by
    by_contra hne
    obtain ⟨k, hk⟩ := h y hy hne
    linarith [hin k]
  induction t with
  | zero => exact h0
  | succ n ih => rw [hy n, ih, hfix]

/-- Cochrane (2023), pp. 631–632, "multiple stable equilibria that unquestionably satisfy the
transversality condition" (under the corrected condition `b > 1 + i/2`, E19): with `a > 0`,
`A = 1 + i`, `i > 0`, `A(1 − b/(am̄)) = 1`, there is `r > 0` such that every `m₀` within `r` of
`m̄` starts an orbit of the map that stays in `(b/a, ∞)` (so the first-order condition holds at
every date, `obs_map_iff`), converges to `m̄`, and satisfies the transversality condition
`βᵀ u_c m_T = βᵀ a m_T^{−b} m_T → 0`; distinct `m₀` give distinct equilibria. -/
theorem obs_multiple_stable {a b i β ms : ℝ} (ha : 0 < a) (hi : 0 < i) (hβ : 0 ≤ β)
    (hβ1 : β < 1) (hb : 1 + i / 2 < b) (hms : 0 < ms) (hss : (1 + i) * (1 - b / a * (1 / ms)) = 1) :
    ∃ r, 0 < r ∧ ∀ m0, |m0 - ms| < r →
      (∀ t, b / a < (obsMap a b (1 + i))^[t] m0) ∧
      Tendsto (fun t => (obsMap a b (1 + i))^[t] m0) atTop (𝓝 ms) ∧
      Tendsto (fun T => β ^ T * (a * ((obsMap a b (1 + i))^[T] m0) ^ (-b)) *
        (obsMap a b (1 + i))^[T] m0) atTop (𝓝 0) := by
  have hb1 : b ≠ 1 := by intro h; rw [h] at hb; linarith
  have hderiv := obs_map_hasDerivAt ha hb1 hms hss
  have hfix := (obs_steady_iff ha (by linarith : (1 : ℝ) < 1 + i) hms).2 hss
  have hstab : |1 - (1 + i - 1) / (b - 1)| < 1 := by
    rw [show 1 + i - 1 = i by ring]; exact (obs_stable_iff hi hb1).mpr hb
  obtain ⟨r, hr, hcon⟩ := local_contraction hderiv hfix hstab
  have hbams : b / a < ms := by
    have h1 : b / a * (1 / ms) < 1 := by
      have : 1 - b / a * (1 / ms) = 1 / (1 + i) := by
        rw [eq_div_iff (by positivity), mul_comm]; exact hss
      have : 0 < 1 / (1 + i) := by positivity
      linarith
    rw [mul_one_div, div_lt_one hms] at h1
    exact h1
  refine ⟨min r (ms - b / a), lt_min hr (by linarith), fun m0 hm0 => ?_⟩
  have hm0r : |m0 - ms| < r := lt_of_lt_of_le hm0 (min_le_left _ _)
  obtain ⟨hin, hlim⟩ := hcon m0 hm0r
  refine ⟨fun t => ?_, hlim, ?_⟩
  · have h1 := hin t
    have h2 : |m0 - ms| < ms - b / a := lt_of_lt_of_le hm0 (min_le_right _ _)
    have h3 := neg_abs_le ((obsMap a b (1 + i))^[t] m0 - ms)
    linarith
  · have hc : ContinuousAt (fun m : ℝ => a * m ^ (-b) * m) ms :=
      (continuousAt_const.mul (Real.continuousAt_rpow_const ms (-b) (Or.inl hms.ne'))).mul
        continuousAt_id
    have h1 := hc.tendsto.comp hlim
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul h1
    rw [zero_mul] at h2
    refine h2.congr fun T => ?_
    simp only [Function.comp_apply]
    ring

/-- Cochrane (2023), pp. 631–632 (E19): for `1 < b < 1 + i/2` (and for `b < 1`) the steady state
is locally unique: some neighbourhood of `m̄` contains no orbit other than the steady state. -/
theorem obs_locally_unique {a b i ms : ℝ} (ha : 0 < a) (hi : 0 < i) (hb1 : b ≠ 1)
    (hb : b < 1 + i / 2) (hms : 0 < ms) (hss : (1 + i) * (1 - b / a * (1 / ms)) = 1) :
    ∃ r, 0 < r ∧ ∀ m : ℕ → ℝ, (∀ t, m (t + 1) = obsMap a b (1 + i) (m t)) →
      (∀ t, |m t - ms| < r) → ∀ t, m t = ms := by
  have hderiv := obs_map_hasDerivAt ha hb1 hms hss
  have hfix := (obs_steady_iff ha (by linarith : (1 : ℝ) < 1 + i) hms).2 hss
  have hunst : 1 < |1 - (1 + i - 1) / (b - 1)| := by
    rw [show 1 + i - 1 = i by ring]
    have hne : 1 ≠ |1 - i / (b - 1)| := by
      intro h
      rcases lt_or_gt_of_ne hb1 with hlt | hgt
      · have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi (by linarith)
        rw [abs_of_pos (by linarith)] at h; linarith
      · have hb0 : 0 < b - 1 := by linarith
        have h2 : 2 < i / (b - 1) := by rw [lt_div_iff₀ hb0]; linarith
        rw [abs_of_neg (by linarith)] at h; linarith
    rcases (not_lt.mp (mt (obs_stable_iff hi hb1).mp (not_lt.mpr hb.le))).lt_or_eq with h | h
    · exact h
    · exact absurd h hne
  exact local_repulsion hderiv hfix hunst

/-! ## CES money in utility (p. 632) -/

/-- Cochrane (2023), p. 632: the CES utility
`u(c, m) = ([c^ρ + θm^ρ]^{(1−γ)/ρ} − 1)/(1 − γ)`, `m = M/P`. -/
noncomputable def cesU (ρ θ γ c m : ℝ) : ℝ := ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)

/-- Cochrane (2023), p. 632: `u_c = [c^ρ + θm^ρ]^{(1−γ−ρ)/ρ}c^{ρ−1}` (exact derivative,
`c, m > 0`, `θ > 0`, `ρ ≠ 0`, `γ ≠ 1`). -/
theorem ces_uc {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    HasDerivAt (fun c => cesU ρ θ γ c m)
      ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1)) c := by
  have hg : HasDerivAt (fun c => c ^ ρ + θ * m ^ ρ) (ρ * c ^ (ρ - 1)) c :=
    (Real.hasDerivAt_rpow_const (Or.inl hc.ne')).add_const _
  have hpos : 0 < c ^ ρ + θ * m ^ ρ := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ; positivity
  have h := ((hg.rpow_const (p := (1 - γ) / ρ) (Or.inl hpos.ne')).sub_const 1).div_const
    (1 - γ)
  have h1γ : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  change HasDerivAt (fun c => ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)) _ c
  convert h using 1
  rw [show (1 - γ) / ρ - 1 = (1 - γ - ρ) / ρ by field_simp]
  field_simp

/-- Cochrane (2023), p. 632: `u_m = [c^ρ + θm^ρ]^{(1−γ−ρ)/ρ}θm^{ρ−1}`. -/
theorem ces_um {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    HasDerivAt (fun m => cesU ρ θ γ c m)
      ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1))) m := by
  have hg : HasDerivAt (fun m => c ^ ρ + θ * m ^ ρ) (θ * (ρ * m ^ (ρ - 1))) m :=
    ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul θ).const_add _
  have hpos : 0 < c ^ ρ + θ * m ^ ρ := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ; positivity
  have h := ((hg.rpow_const (p := (1 - γ) / ρ) (Or.inl hpos.ne')).sub_const 1).div_const
    (1 - γ)
  have h1γ : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  change HasDerivAt (fun m => ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)) _ m
  convert h using 1
  rw [show (1 - γ) / ρ - 1 = (1 - γ - ρ) / ρ by field_simp]
  field_simp

/-- Cochrane (2023), p. 632, second line: `u_c(y, m) = [1 + θ(m/y)^ρ]^{(1−γ−ρ)/ρ} y^{−γ}`. -/
theorem ces_uc_form {ρ θ γ y m : ℝ} (hρ : ρ ≠ 0) (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m) :
    (y ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (ρ - 1) =
      (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (-γ) := by
  have hyρ : 0 < y ^ ρ := Real.rpow_pos_of_pos hy ρ
  have h1 : y ^ ρ + θ * m ^ ρ = y ^ ρ * (1 + θ * (m / y) ^ ρ) := by
    rw [Real.div_rpow hm.le hy.le]; field_simp
  have hpos : 0 ≤ 1 + θ * (m / y) ^ ρ := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ; positivity
  rw [h1, Real.mul_rpow hyρ.le hpos, ← Real.rpow_mul hy.le,
    show ρ * ((1 - γ - ρ) / ρ) = 1 - γ - ρ by field_simp]
  rw [mul_comm ((y ^ (1 - γ - ρ))), mul_assoc, ← Real.rpow_add hy,
    show 1 - γ - ρ + (ρ - 1) = -γ by ring]

/-- Cochrane (2023), p. 632, "so asset prices are driven by": the discount factor
`βu_c(t+1)/u_c(t) = β([1 + θ(m'/y')^ρ]/[1 + θ(m/y)^ρ])^{(1−γ−ρ)/ρ}(y'/y)^{−γ}`. -/
theorem ces_sdf {ρ θ γ β y m y' m' : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m) (hy' : 0 < y')
    (hm' : 0 < m') :
    β * ((1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) * y' ^ (-γ)) /
        ((1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (-γ)) =
      β * (1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) /
        (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * (y' / y) ^ (-γ) := by
  have h1 : 0 < (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hy _
  have := hm'; have := hy'
  rw [Real.div_rpow hy'.le hy.le]
  field_simp

/-- Cochrane (2023), p. 632, "With constant real money `M/(Py)`, we have the usual power utility
formula": if `m'/y' = m/y` the discount factor is `β(y'/y)^{−γ}`. -/
theorem ces_sdf_const {ρ θ γ β y m y' m' : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m)
    (hconst : m' / y' = m / y) :
    β * (1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) /
        (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * (y' / y) ^ (-γ) = β * (y' / y) ^ (-γ) := by
  have h1 : 0 < (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  rw [hconst]
  field_simp

/-- Cochrane (2023), p. 632: the CES marginal rate of substitution `u_m/u_c = θ(m/c)^{ρ−1}`. -/
theorem ces_mrs {ρ θ γ c m : ℝ} (hθ : 0 < θ) (hc : 0 < c) (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1)) /
        ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1)) = θ * (m / c) ^ (ρ - 1) := by
  have hpos : 0 < (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  have := Real.rpow_pos_of_pos hc (ρ - 1)
  rw [Real.div_rpow hm.le hc.le]
  field_simp

/-- Cochrane (2023), p. 632, "the money demand function (19.16) becomes
`M_t = P_ty_t((1/θ)i_t/(1+i_t))^{1/(ρ−1)}`": for `ρ ≠ 1`, `k = i/(1+i) > 0`,
`θ(m/c)^{ρ−1} = k` iff `m = c(k/θ)^{1/(ρ−1)}`. -/
theorem ces_money_demand_iff {ρ θ c m k : ℝ} (hρ : ρ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) (hk : 0 < k) :
    θ * (m / c) ^ (ρ - 1) = k ↔ m = c * (1 / θ * k) ^ (1 / (ρ - 1)) := by
  have hρ1 : (ρ - 1) ≠ 0 := sub_ne_zero.mpr hρ
  have hmc : 0 < m / c := div_pos hm hc
  constructor
  · intro h
    have h1 : (m / c) ^ (ρ - 1) = 1 / θ * k := by rw [← h]; field_simp
    rw [← h1, show 1 / (ρ - 1) = (ρ - 1)⁻¹ by ring, Real.rpow_rpow_inv hmc.le hρ1]
    field_simp
  · intro h
    have h1 : m / c = (1 / θ * k) ^ (1 / (ρ - 1)) := by rw [h]; field_simp
    rw [h1, show 1 / (ρ - 1) = (ρ - 1)⁻¹ by ring, Real.rpow_inv_rpow (by positivity) hρ1]
    field_simp

/-- Cochrane (2023), p. 632, "Here too we have a unit income elasticity": with `m = y·K` the
exact elasticity `d log m/d log y` equals one. -/
theorem ces_income_elasticity {K ly : ℝ} (hK : 0 < K) :
    HasDerivAt (fun l => Real.log (Real.exp l * K)) 1 ly := by
  have h : (fun l => Real.log (Real.exp l * K)) = fun l => l + Real.log K := by
    funext l; rw [Real.log_mul (Real.exp_pos l).ne' hK.ne', Real.log_exp]
  rw [h]
  simpa using (hasDerivAt_id ly).add_const (Real.log K)

/-- Cochrane (2023), p. 632, "and an interest elasticity governed by the separate parameter ρ":
with `m = c(k/θ)^{1/(ρ−1)}`, the exact elasticity `d log m/d log k` (`k = i/(1+i)`) is
`1/(ρ − 1)`. -/
theorem ces_interest_elasticity {ρ θ c lk : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    HasDerivAt (fun l => Real.log (c * (1 / θ * Real.exp l) ^ (1 / (ρ - 1)))) (1 / (ρ - 1)) lk := by
  have h : (fun l => Real.log (c * (1 / θ * Real.exp l) ^ (1 / (ρ - 1)))) =
      fun l => Real.log c + 1 / (ρ - 1) * (Real.log (1 / θ) + l) := by
    funext l
    have h1 : 0 < 1 / θ * Real.exp l := by positivity
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos h1 _).ne', Real.log_rpow h1,
      Real.log_mul (by positivity) (Real.exp_pos l).ne', Real.log_exp]
  rw [h]
  simpa using (((hasDerivAt_id lk).const_add (Real.log (1 / θ))).const_mul (1 / (ρ - 1))).const_add
    (Real.log c)

end Cochrane.Monetarism.Nonseparable

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cash-in-advance model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5, pp. 447–455.

Timing convention. `Bin t` and `Min t` are the nominal bonds and money the household brings
*into* date `t` (the book's `B_{t−1}`, `M_{t−1}`); the bonds and the overnight money chosen at
`t` are `Bin (t + 1)` and `Min (t + 1)` (the book's `B_t`, `M_t`). The flow budget (19.27) is
`Bin t + Min t + P_t(y_t − c_t) = Q_t Bin (t+1) + Min (t+1) + P_t s_t`.

## Contents

* **Stochastic present-value budget** (19.27)–(19.30), (19.34)–(19.35) for an arbitrary
  `ExpectationSystem`: from the flow budget and the nominal bond price
  `Λ_t Q_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, the TVC on bonds holds **iff** (19.29) holds, and the TVC
  (19.28) on bonds plus money holds **iff** (19.30) holds. Given (19.28), (19.29) holds iff the
  separate money TVC holds; an explicit path satisfies (19.27), (19.28), (19.30) but violates
  (19.29) (the book's "these conditions imply … two ways" needs the money TVC). The knownness
  lemmas `known_mul`, `known_inv`, `known_div` are `MoneyInUtility`'s, and `telescope` is the
  case `a = 1` of the core `ForwardSolution.iterate_A15`.
* **Money demand by optimisation** (19.33), (19.37), the L-shaped demand of p. 454, and the
  interest-rate sign (E14): the overnight-money choice is a linear programme with an L-shaped
  solution correspondence; `Q > 1` has no optimum.
* **Consumption Euler equation** (19.31)/(19.36) derived from optimality (perfect foresight;
  the problem is `MoneyInUtility.Optimal` without money, `isOptimalPlan_iff_optimal`):
  necessity by a two-date perturbation, sufficiency under concavity; (19.32) with genuine
  uncertainty; E15 (`Q = β` only with a constant price level); the `V ≠ 1` wedge.
* **The household problem on a finite event tree** (`TreeEuler`, genuine uncertainty, infinite
  horizon): node-level Euler necessity, sufficiency under concavity, (19.31) state by state, and
  (19.32) with `Λ_t = β^tu'(y_t)` derived from optimality.
* **Perfect-foresight equilibria** (constant endowment): the frictionless model, the valuation
  (19.38) (corrected to `(B_{t−1} + M_{t−1})/P_t`), uniqueness of the price level (p. 453), the
  worked case `P = (1 − β)B/s`, passive-fiscal indeterminacy; the monetary model, the standard
  equilibrium `P_t = M_tV/y`, the continuum of deflationary equilibria, real-money growth and the
  money TVC, and pruning by an active fiscal policy (pp. 453–454).
-/

namespace Cochrane.Monetarism.CashInAdvance

open Filter Topology

/-! ## Stochastic present-value budget constraint -/

namespace Stochastic

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

open Cochrane.Monetarism.MoneyInUtility (known_mul known_inv known_div)

/-- Cochrane (2023), (19.29)–(19.30), p. 449: the book's discounting `E_t[(Λ_{t+j}/Λ_t) f]`
equals `E_t[Λ_{t+j} f]/Λ_t` when `Λ_t` is known at `t` and positive (pull-out property). -/
theorem E_ratio (hPO : 𝔼.PullOut) {t : ℕ} {Λt Λj f : Ω → ℝ} (hΛ : 𝔼.E t Λt = Λt)
    (hΛ0 : ∀ ω, 0 < Λt ω) :
    𝔼.E t (Λj * f / Λt) = 𝔼.E t (Λj * f) / Λt := by
  have h : Λj * f / Λt = Λt⁻¹ * (Λj * f) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    ring
  rw [h, hPO t _ _ (known_inv 𝔼 hPO hΛ fun ω => (hΛ0 ω).ne')]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
  ring

/-- Cochrane (2023), (19.27)–(19.30), p. 449: **forward iteration with expectations.** If
`x_t = E_t x_{t+1} + g_t` at every date with `g` adapted, then for every horizon
`x_t = Σ_{j ≤ T} E_t g_{t+j} + E_t x_{t+T+1}` (law of iterated expectations; the case `a = 1`
of the core `ForwardSolution.iterate_A15`). -/
theorem telescope {x g : ℕ → Ω → ℝ} (hrec : ∀ t, x t = 𝔼.E t (x (t + 1)) + g t)
    (hg : ∀ t, 𝔼.E t (g t) = g t) (t : ℕ) :
    ∀ T, x t = ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) + 𝔼.E t (x (t + T + 1)) := by
  intro T
  have hsol : ForwardSolution.Solves 𝔼 1 g x := fun k => by rw [one_smul]; exact hrec k
  have h := ForwardSolution.iterate_A15 𝔼 hg hsol t (T + 1)
  simp only [one_pow, one_smul] at h
  exact h.trans (add_comm _ _)

/-- Cochrane (2023), (19.28)–(19.30), p. 449: **valuation iff transversality** (pointwise in the
state). Under `x_t = E_t x_{t+1} + g_t` with `g` adapted and `j ↦ E_t g_{t+j}(ω)` summable, the
transversality condition `E_t x_{t+T}(ω) → 0` holds iff `x_t(ω) = Σ_j E_t g_{t+j}(ω)`. -/
theorem pv_iff_tvc {x g : ℕ → Ω → ℝ} (hrec : ∀ t, x t = 𝔼.E t (x (t + 1)) + g t)
    (hg : ∀ t, 𝔼.E t (g t) = g t) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E t (g (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 0) ↔
      x t ω = ∑' j, 𝔼.E t (g (t + j)) ω := by
  have hpart : ∀ T, 𝔼.E t (x (t + (T + 1))) ω =
      x t ω - ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) ω := by
    intro T
    have h := congrFun (telescope 𝔼 hrec hg t T) ω
    rw [Pi.add_apply, Finset.sum_apply] at h
    rw [← add_assoc]
    linarith
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) ω) atTop
      (𝓝 (∑' j, 𝔼.E t (g (t + j)) ω)) :=
    (tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [hpart]
  constructor
  · intro h
    have h2 := hlim.const_sub (x t ω)
    have := tendsto_nhds_unique h h2
    linarith
  · intro h
    have h2 := hlim.const_sub (x t ω)
    rwa [← h, sub_self] at h2

variable (Λ P Q Bin Min s c y : ℕ → Ω → ℝ)

/-- Cochrane (2023), (19.29), p. 449: the date-`τ` flow in the money-creation form,
`Λ_τ((M_τ − M_{τ−1})/P_τ + s_τ + c_τ − y_τ)` (`M_τ = Min (τ+1)`, `M_{τ−1} = Min τ`). -/
noncomputable def gB : ℕ → Ω → ℝ := fun τ => Λ τ * ((Min (τ + 1) - Min τ) / P τ + s τ + c τ - y τ)

/-- Cochrane (2023), (19.30), p. 449: the date-`τ` flow in the interest-cost form,
`Λ_τ((1 − Q_τ) M_τ/P_τ + s_τ + c_τ − y_τ)`; `1 − Q_τ = i_τ/(1 + i_τ)` (`interest_cost_eq`). -/
noncomputable def gBM : ℕ → Ω → ℝ :=
  fun τ => Λ τ * ((1 - Q τ) * Min (τ + 1) / P τ + s τ + c τ - y τ)

/-- Cochrane (2023), (19.30), p. 449: with `Q = 1/(1 + i)`, `1 − Q = i/(1 + i)`. -/
theorem interest_cost_eq {Qv i : ℝ} (hi : 1 + i ≠ 0) (hQ : Qv = 1 / (1 + i)) :
    1 - Qv = i / (1 + i) := by
  rw [hQ]
  field_simp
  ring

variable {Λ P Q Bin Min s c y}

/-- Cochrane (2023), (19.27), (19.32), p. 449: the flow budget (19.27), multiplied by `Λ_t/P_t`,
with the nominal bond price `Λ_t Q_t/P_t = E_t(Λ_{t+1}/P_{t+1})` and bonds chosen at `t` known
at `t`, gives `Λ_t B_{t−1}/P_t = E_t(Λ_{t+1}B_t/P_{t+1}) + gB_t`. -/
theorem flow_step_B (hPO : 𝔼.PullOut) (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    Λ t * Bin t / P t = 𝔼.E t (Λ (t + 1) * Bin (t + 1) / P (t + 1)) + gB Λ P Min s c y t := by
  have h1 : Λ (t + 1) * Bin (t + 1) / P (t + 1) = Bin (t + 1) * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [h1, hPO t _ _ (hB t), ← hQ t]
  funext ω
  have hf := congrFun (hflow t) ω
  have hPω := hP t ω
  simp only [gB, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply] at hf ⊢
  field_simp
  linear_combination (Λ t ω) * hf

/-- Cochrane (2023), (19.27), (19.30), p. 449: in terms of bonds plus money,
`Λ_t(B_{t−1} + M_{t−1})/P_t = E_t(Λ_{t+1}(B_t + M_t)/P_{t+1}) + gBM_t`: holding money overnight
costs `(1 − Q_t)M_t`. -/
theorem flow_step_BM (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1))
    (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    Λ t * (Bin t + Min t) / P t =
      𝔼.E t (Λ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1)) + gBM Λ P Q Min s c y t := by
  have hBM : 𝔼.E t (Bin (t + 1) + Min (t + 1)) = Bin (t + 1) + Min (t + 1) := by
    rw [map_add, hB t, hM t]
  have h1 : Λ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1) =
      (Bin (t + 1) + Min (t + 1)) * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
    ring
  rw [h1, hPO t _ _ hBM, ← hQ t]
  funext ω
  have hf := congrFun (hflow t) ω
  have hPω := hP t ω
  simp only [gBM, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.one_apply] at hf ⊢
  field_simp
  linear_combination (Λ t ω) * hf

/-- Cochrane (2023), §19.5.1, p. 449 (measurability bookkeeping): if the discount factor, the
price level, money, surpluses, consumption and endowment are adapted (money chosen at `t` known at
`t`), the money-creation flow `gB` is adapted. -/
theorem gB_adapted (hPO : 𝔼.PullOut) (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hMa : 𝔼.Adapted Min) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s)
    (hc : 𝔼.Adapted c) (hy : 𝔼.Adapted y) (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    𝔼.E t (gB Λ P Min s c y t) = gB Λ P Min s c y t := by
  have hdiv : 𝔼.E t ((Min (t + 1) - Min t) / P t) = (Min (t + 1) - Min t) / P t :=
    known_div 𝔼 hPO (by rw [map_sub, hM t, hMa t]) (hPa t) (hP t)
  have hin : 𝔼.E t ((Min (t + 1) - Min t) / P t + s t + c t - y t) =
      (Min (t + 1) - Min t) / P t + s t + c t - y t := by
    rw [map_sub, map_add, map_add, hdiv, hs t, hc t, hy t]
  exact known_mul 𝔼 hPO (hΛ t) hin

/-- Cochrane (2023), §19.5.1, p. 449 (measurability bookkeeping): under the same adaptedness
hypotheses (and an adapted bond price), the interest-cost flow `gBM` is adapted. -/
theorem gBM_adapted (hPO : 𝔼.PullOut) (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hQa : 𝔼.Adapted Q) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s)
    (hc : 𝔼.Adapted c) (hy : 𝔼.Adapted y) (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    𝔼.E t (gBM Λ P Q Min s c y t) = gBM Λ P Q Min s c y t := by
  have h1Q : 𝔼.E t (1 - Q t) = 1 - Q t := by
    rw [map_sub, hQa t]
    congr 1
    exact 𝔼.const t 1
  have hdiv : 𝔼.E t ((1 - Q t) * Min (t + 1) / P t) = (1 - Q t) * Min (t + 1) / P t :=
    known_div 𝔼 hPO (known_mul 𝔼 hPO h1Q (hM t)) (hPa t) (hP t)
  have hin : 𝔼.E t ((1 - Q t) * Min (t + 1) / P t + s t + c t - y t) =
      (1 - Q t) * Min (t + 1) / P t + s t + c t - y t := by
    rw [map_sub, map_add, map_add, hdiv, hs t, hc t, hy t]
  exact known_mul 𝔼 hPO (hΛ t) hin

/-- Cochrane (2023), (19.28)–(19.29), p. 449: **present-value budget, seigniorage as money
creation.** Under the flow budget (19.27), the nominal bond price, adaptedness and the pull-out
property, with the flows summable, the bond transversality condition
`E_t[Λ_{t+T} B_{t+T−1}/P_{t+T}] → 0` holds iff
`Λ_t B_{t−1}/P_t = Σ_j E_t[Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s_{t+j} + c_{t+j} −
y_{t+j})]`. -/
theorem pv_19_29 (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P) (hMa : 𝔼.Adapted Min)
    (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s) (hc : 𝔼.Adapted c)
    (hy : 𝔼.Adapted y) (t : ℕ) (ω : Ω)
    (hsum : Summable fun j => 𝔼.E t (gB Λ P Min s c y (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Λ t ω * Bin t ω / P t ω = ∑' j, 𝔼.E t (gB Λ P Min s c y (t + j)) ω :=
  pv_iff_tvc 𝔼 (x := fun τ => Λ τ * Bin τ / P τ) (flow_step_B 𝔼 hPO hQ hB hP hflow)
    (gB_adapted 𝔼 hPO hΛ hPa hMa hM hs hc hy hP) t ω hsum

/-- Cochrane (2023), (19.28), (19.30), p. 449: **present-value budget, seigniorage as interest
saving.** Under the same hypotheses (bond price adapted), the transversality condition (19.28)
`E_t[Λ_{t+T}(B_{t+T−1} + M_{t+T−1})/P_{t+T}] → 0` holds iff
`Λ_t(B_{t−1} + M_{t−1})/P_t = Σ_j E_t[Λ_{t+j}((1 − Q_{t+j})M_{t+j}/P_{t+j} + s + c − y)]`. -/
theorem pv_19_30 (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P) (hQa : 𝔼.Adapted Q)
    (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s) (hc : 𝔼.Adapted c)
    (hy : 𝔼.Adapted y) (t : ℕ) (ω : Ω)
    (hsum : Summable fun j => 𝔼.E t (gBM Λ P Q Min s c y (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω) atTop
        (𝓝 0) ↔
      Λ t ω * (Bin t ω + Min t ω) / P t ω = ∑' j, 𝔼.E t (gBM Λ P Q Min s c y (t + j)) ω :=
  pv_iff_tvc 𝔼 (x := fun τ => Λ τ * (Bin τ + Min τ) / P τ)
    (flow_step_BM 𝔼 hPO hQ hB hM hP hflow) (gBM_adapted 𝔼 hPO hΛ hPa hQa hM hs hc hy hP) t ω hsum

/-- Cochrane (2023), (19.29)–(19.30), p. 449: the book's normalised form. With `Λ_t > 0`,
`x · B/P = S` is the same as `B/P = S/Λ_t`, i.e. `B_{t−1}/P_t = Σ_j E_t[(Λ_{t+j}/Λ_t)(…)]`
(see `E_ratio` for moving `1/Λ_t` inside `E_t`). -/
theorem normalise_iff {Λt X S : ℝ} (hΛt : 0 < Λt) : Λt * X = S ↔ X = S / Λt := by
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), (19.28)–(19.30), p. 449: given the transversality condition (19.28) on bonds
plus money, the bond transversality condition behind (19.29) holds **iff** the money
transversality condition `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0` holds. -/
theorem tvc_B_iff_money_tvc (t : ℕ) (ω : Ω)
    (hBM : Tendsto (fun T => 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω)
      atTop (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Min (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  have hsplit : ∀ T, 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω =
      𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω +
        𝔼.E t (Λ (t + T) * Min (t + T) / P (t + T)) ω := by
    intro T
    have h : Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T) =
        Λ (t + T) * Bin (t + T) / P (t + T) + Λ (t + T) * Min (t + T) / P (t + T) := by
      funext ω'
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
      ring
    rw [h, map_add, Pi.add_apply]
  simp_rw [hsplit] at hBM
  constructor
  · intro h
    have := hBM.sub h
    simp only [add_sub_cancel_left, sub_zero] at this
    exact this
  · intro h
    have := hBM.sub h
    simp only [add_sub_cancel_right, sub_zero] at this
    exact this

/-- Cochrane (2023), (19.27)–(19.30), p. 449: **the two present-value forms are not equivalent
without the money transversality condition.** Perfect foresight, `P ≡ 1`, `Λ_t = 2^{−t}`,
`Q ≡ 1/2` (so `Λ_tQ_t/P_t = Λ_{t+1}/P_{t+1}`), `c = y`, money `M_{t−1} = 2^t`, bonds
`B_{t−1} = −2^t`, surpluses `s_t = −2^t`. The flow (19.27) and the TVC (19.28) hold, every flow
term of (19.29) and (19.30) is zero, so (19.30) holds (`0 = 0`) but (19.29) fails
(`Λ_0B_{−1}/P_0 = −1 ≠ 0`); the money TVC fails (`Λ_tM_{t−1}/P_t = 1`). -/
theorem pv_19_29_needs_money_tvc :
    let Λ : ℕ → ℝ := fun t => (1 / 2) ^ t
    let Min : ℕ → ℝ := fun t => 2 ^ t
    let Bin : ℕ → ℝ := fun t => -2 ^ t
    let s : ℕ → ℝ := fun t => -2 ^ t
    (∀ t, Λ t * (1 / 2) / 1 = Λ (t + 1) / 1) ∧
      (∀ t, Bin t + Min t + 1 * 0 = 1 / 2 * Bin (t + 1) + Min (t + 1) + 1 * s t) ∧
      Tendsto (fun T => Λ T * (Bin T + Min T) / 1) atTop (𝓝 0) ∧
      (∀ τ, Λ τ * ((1 - 1 / 2) * Min (τ + 1) / 1 + s τ + 0) = 0) ∧
      (∀ τ, Λ τ * ((Min (τ + 1) - Min τ) / 1 + s τ + 0) = 0) ∧
      Λ 0 * Bin 0 / 1 ≠ 0 ∧
      ¬ Tendsto (fun T => Λ T * Min T / 1) atTop (𝓝 0) := by
  intro Λ Min Bin s
  have hone : ∀ t : ℕ, (1 / 2 : ℝ) ^ t * 2 ^ t = 1 := by
    intro t
    rw [← mul_pow]
    norm_num
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun τ => ?_, fun τ => ?_, ?_, ?_⟩
  · simp only [Λ, pow_succ]
  · simp only [Bin, Min, s, pow_succ]
    ring
  · have : (fun T => Λ T * (Bin T + Min T) / 1) = fun _ => (0 : ℝ) := by
      funext T
      simp only [Bin, Min]
      ring
    rw [this]
    exact tendsto_const_nhds
  · simp only [Min, s, pow_succ]
    ring
  · simp only [Min, s, pow_succ]
    ring
  · simp only [Λ, Bin]
    norm_num
  · have : (fun T => Λ T * Min T / 1) = fun _ => (1 : ℝ) := by
      funext T
      simp only [Λ, Min, div_one]
      exact hone T
    rw [this]
    intro h
    have := tendsto_nhds_unique tendsto_const_nhds h
    norm_num at this

/-- Cochrane (2023), (19.34), p. 450: with goods-market clearing `c = y` the money-creation flow
is `Λ_τ((M_τ − M_{τ−1})/P_τ + s_τ)`. -/
theorem gB_market_clearing (τ : ℕ) :
    gB Λ P Min s y y τ = Λ τ * ((Min (τ + 1) - Min τ) / P τ + s τ) := by
  funext ω
  simp only [gB, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), (19.35), p. 450: with `c = y` the interest-cost flow is
`Λ_τ((1 − Q_τ)M_τ/P_τ + s_τ) = Λ_τ(i_τ M_τ/((1 + i_τ)P_τ) + s_τ)` (`interest_cost_eq`). -/
theorem gBM_market_clearing (τ : ℕ) :
    gBM Λ P Q Min s y y τ = Λ τ * ((1 - Q τ) * Min (τ + 1) / P τ + s τ) := by
  funext ω
  simp only [gBM, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), (19.32), p. 450: **nominal bond price with genuine uncertainty.** If the
state-price density is `Λ_t = β^t u'(y_t)` (Fact 1, (19.31)) with `u'(y_t) > 0` adapted, the
price level is adapted and positive and `Λ_tQ_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, then
`Q_t = β E_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]`. -/
theorem bond_price_19_32 (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {uc : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hucA : 𝔼.Adapted uc) (hΛdef : ∀ t, Λ t = β ^ t • uc t)
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, 0 < P t ω)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1))) (t : ℕ) :
    Q t = β • 𝔼.E t (uc (t + 1) / uc t * (P t / P (t + 1))) := by
  have hΛpos : ∀ ω, Λ t ω ≠ 0 := by
    intro ω
    rw [hΛdef t]
    exact (mul_pos (pow_pos hβ t) (huc t ω)).ne'
  have hΛA : 𝔼.E t (Λ t) = Λ t := by
    rw [hΛdef t, map_smul, hucA t]
  have hk : 𝔼.E t (P t / Λ t) = P t / Λ t :=
    known_div 𝔼 hPO (hPa t) hΛA hΛpos
  have hinner : β • (uc (t + 1) / uc t * (P t / P (t + 1))) =
      P t / Λ t * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    have h1 := (huc t ω).ne'
    have h2 := (hP (t + 1) ω).ne'
    have h3 := (hP t ω).ne'
    have hb := (pow_pos hβ t).ne'
    simp only [hΛdef, Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul, pow_succ]
    field_simp
  rw [← map_smul, hinner, hPO t _ _ hk, ← hQ t]
  funext ω
  have h3 := (hP t ω).ne'
  have := hΛpos ω
  simp only [Pi.mul_apply, Pi.div_apply]
  field_simp

end Stochastic

/-! ## Money demand: the overnight-money choice -/

namespace MoneyDemand

/-- Cochrane (2023), (19.27), p. 449: the period-`t` nominal cost `Q(W − M) + M` of carrying
nominal wealth `W = B_t + M_t` into the next period as bonds `W − M` (price `Q`) and overnight
money `M`. Given consumption and next-period wealth, this is the only part of the budget (19.27)
that depends on the split between money and bonds. -/
def portfolioCost (Q W M : ℝ) : ℝ := Q * (W - M) + M

/-- Cochrane (2023), (19.24)–(19.26), pp. 448–449: overnight money `M` is optimal when it is
feasible (`M ≥ M_min`, the least money the constraints allow) and minimises the cost of carrying
wealth `W` among feasible choices. -/
def IsOptimalMoney (Q Mmin W M : ℝ) : Prop :=
  Mmin ≤ M ∧ ∀ M', Mmin ≤ M' → portfolioCost Q W M ≤ portfolioCost Q W M'

/-- Cochrane (2023), (19.30), p. 449: the cost is `QW + (1 − Q)M`; `1 − Q = i/(1 + i)` is the
interest cost of money. -/
theorem portfolioCost_eq (Q W M : ℝ) : portfolioCost Q W M = Q * W + (1 - Q) * M := by
  unfold portfolioCost
  ring

/-- Cochrane (2023), (19.33), (19.37), p. 454: **the money-demand correspondence.** `M` is an
optimal overnight money holding iff `Q ≤ 1` (non-negative nominal rate), `M ≥ M_min`, and
`M = M_min` whenever `Q < 1` (positive nominal rate). -/
theorem optimal_iff {Q Mmin W M : ℝ} :
    IsOptimalMoney Q Mmin W M ↔ Q ≤ 1 ∧ Mmin ≤ M ∧ (Q < 1 → M = Mmin) := by
  simp only [IsOptimalMoney, portfolioCost_eq]
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨?_, hM, fun hQ => ?_⟩
    · by_contra hQ
      push Not at hQ
      have := h (M + 1) (by linarith)
      nlinarith
    · have := h Mmin le_rfl
      have : (1 - Q) * (M - Mmin) ≤ 0 := by linarith
      have h2 : M - Mmin ≤ 0 := by
        by_contra h3
        push Not at h3
        have := mul_pos (by linarith : (0 : ℝ) < 1 - Q) h3
        linarith
      linarith
  · rintro ⟨hQ, hM, hb⟩
    refine ⟨hM, fun M' hM' => ?_⟩
    rcases lt_or_eq_of_le hQ with hQ | hQ
    · rw [hb hQ]
      have := mul_le_mul_of_nonneg_left hM' (by linarith : (0 : ℝ) ≤ 1 - Q)
      linarith
    · rw [hQ]
      simp

/-- Cochrane (2023), (19.33), (19.37), pp. 450–452: at a positive nominal rate (`Q < 1`) the
optimal overnight money holding is the minimum the constraints allow. -/
theorem optimal_iff_of_lt_one {Q Mmin W M : ℝ} (hQ : Q < 1) :
    IsOptimalMoney Q Mmin W M ↔ M = Mmin := by
  rw [optimal_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact h hQ
  · rintro rfl
    exact ⟨hQ.le, le_rfl, fun _ => rfl⟩

/-- Cochrane (2023), p. 454: **the L.** At a zero nominal rate (`Q = 1`) money demand is a
correspondence: every `M ≥ M_min` is optimal. -/
theorem optimal_iff_of_eq_one {Mmin W M : ℝ} : IsOptimalMoney 1 Mmin W M ↔ Mmin ≤ M := by
  rw [optimal_iff]
  constructor
  · rintro ⟨-, h, -⟩
    exact h
  · intro h
    exact ⟨le_rfl, h, fun h1 => absurd h1 (lt_irrefl 1)⟩

/-- Cochrane (2023), pp. 452, 454: at a negative nominal rate (`Q > 1`) the household can lower
its cost without bound by holding more money (and shorting bonds). -/
theorem unbounded_of_one_lt {Q Mmin W : ℝ} (hQ : 1 < Q) (K : ℝ) :
    ∃ M, Mmin ≤ M ∧ portfolioCost Q W M < K := by
  refine ⟨max Mmin ((K - Q * W) / (1 - Q)) + 1, by
    have := le_max_left Mmin ((K - Q * W) / (1 - Q)); linarith, ?_⟩
  have h1 : (K - Q * W) / (1 - Q) < max Mmin ((K - Q * W) / (1 - Q)) + 1 := by
    have := le_max_right Mmin ((K - Q * W) / (1 - Q)); linarith
  rw [div_lt_iff_of_neg (by linarith)] at h1
  rw [portfolioCost_eq]
  linarith

/-- Cochrane (2023), pp. 452–454: **no equilibrium with a negative nominal rate**: for `Q > 1`
there is no optimal money holding. -/
theorem no_optimum_of_one_lt {Q Mmin W M : ℝ} (hQ : 1 < Q) : ¬ IsOptimalMoney Q Mmin W M := by
  rw [optimal_iff]
  rintro ⟨h, -, -⟩
  linarith

/-- Cochrane (2023), (19.24)–(19.25), pp. 448–449: overnight money `M = M^d + P(y − c)` is
feasible for some `M^d` obeying the cash-in-advance constraint `Pc ≤ M^dV` iff
`M ≥ Pc/V + P(y − c)`: the monetary model's minimum overnight money. -/
theorem overnight_feasible_iff {P c y V M : ℝ} (hV : 0 < V) :
    (∃ Md, P * c ≤ Md * V ∧ M = Md + P * (y - c)) ↔ P * c / V + P * (y - c) ≤ M := by
  constructor
  · rintro ⟨Md, h1, rfl⟩
    have : P * c / V ≤ Md := by rw [div_le_iff₀ hV]; exact h1
    linarith
  · intro h
    refine ⟨M - P * (y - c), ?_, by ring⟩
    rw [← div_le_iff₀ hV]
    linarith

/-- Cochrane (2023), (19.24)–(19.25): at the market-clearing allocation `c = y` the monetary
model's minimum overnight money is `Py/V`. -/
theorem overnight_min_clear (P y V : ℝ) : P * y / V + P * (y - y) = P * y / V := by
  ring

/-- Cochrane (2023), (19.33), p. 450, **Fact 2**: in the monetary model with a positive nominal
rate (`Q < 1`) and `c = y`, optimal overnight money satisfies the quantity equation
`M_tV = P_ty_t`. -/
theorem fact2_19_33 {Q P y V W M : ℝ} (hV : 0 < V) (hQ : Q < 1)
    (hopt : IsOptimalMoney Q (P * y / V) W M) : M * V = P * y := by
  rw [(optimal_iff_of_lt_one hQ).1 hopt]
  field_simp

/-- Cochrane (2023), (19.37), p. 452, **frictionless Fact 2**: when money can be returned at
the end of the day the minimum overnight money is `0` (constraint (19.26)), so a positive nominal
rate (`Q < 1`) implies `M_t = 0`. -/
theorem fact_19_37 {Q W M : ℝ} (hQ : Q < 1) (hopt : IsOptimalMoney Q 0 W M) : M = 0 :=
  (optimal_iff_of_lt_one hQ).1 hopt

/-- Cochrane (2023), p. 454: **the L-shaped cash-in-advance money demand.** At `i = 0`
(`Q = 1`) any `M` with `MV ≥ Py` is optimal. -/
theorem L_shaped_demand {P y V W M : ℝ} (hV : 0 < V) :
    IsOptimalMoney 1 (P * y / V) W M ↔ P * y ≤ M * V := by
  rw [optimal_iff_of_eq_one, div_le_iff₀ hV]

/-- Cochrane (2023), pp. 450, 452: with `Q = 1/(1 + i)` and `1 + i > 0`, a positive nominal rate
is `Q < 1`. -/
theorem Q_lt_one_iff {i : ℝ} (hi : 0 < 1 + i) : 1 / (1 + i) < 1 ↔ 0 < i := by
  rw [div_lt_one hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 453 (**E14**): the nominal rate is non-negative iff `Q_t ≤ 1` (the book
prints `Q_t ≥ 1`). -/
theorem Q_le_one_iff {i : ℝ} (hi : 0 < 1 + i) : 1 / (1 + i) ≤ 1 ↔ 0 ≤ i := by
  rw [div_le_one hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 453 (**E14**): the printed condition `Q_t ≥ 1` says the nominal rate is
non-positive, the opposite of the intended non-negativity. -/
theorem E14_one_le_Q_iff {i : ℝ} (hi : 0 < 1 + i) : 1 ≤ 1 / (1 + i) ↔ i ≤ 0 := by
  rw [le_div_iff₀ hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), (19.30), p. 450 (the `V ≠ 1` wedge): at the binding minimum overnight money
`Pc/V + P(y − c)`, the date-`t` terms of the present-value budget (19.30) that involve
consumption are `(1 − Q)(Pc/V + P(y − c)) + P(c − y) = P(1 + (1 − Q)(1/V − 1))c − QPy`: the
effective price of consumption is `1 + (1 − Q)(1/V − 1)` per unit. -/
theorem binding_cost_wedge {P c y V Q : ℝ} (hV : V ≠ 0) :
    (1 - Q) * (P * c / V + P * (y - c)) + P * (c - y) =
      P * (1 + (1 - Q) * (1 / V - 1)) * c - Q * P * y := by
  field_simp
  ring

/-- Cochrane (2023), p. 450 ("cash overnight `M_t` will be unaffected"): the consumption wedge
`1 + (1 − Q)(1/V − 1)` equals `1` iff `Q = 1` (zero rate) or `V = 1`. So the no-distortion
argument for Fact 1 is exact only for `V = 1` (or `i = 0`). -/
theorem wedge_eq_one_iff {Q V : ℝ} (hV : V ≠ 0) :
    1 + (1 - Q) * (1 / V - 1) = 1 ↔ Q = 1 ∨ V = 1 := by
  constructor
  · intro h
    have h' : (1 - Q) * (1 / V - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h1 | h1
    · left; linarith
    · right
      field_simp at h1
      linarith
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

end MoneyDemand

/-! ## The consumption Euler equation (perfect foresight) -/

namespace Euler

/-- Cochrane (2023), §19.5.1, p. 448: lifetime utility `Σ_t β^t u(c_t)`. -/
noncomputable def lifetimeU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * u (c t)

/-- Cochrane (2023), (19.29)–(19.30), p. 449: a consumption plan is admissible when lifetime
utility and the present value `Σ_t p_tc_t` at prices `p` converge absolutely and
`Σ_t p_tc_t ≤ W` (the present-value budget with all non-consumption terms in `W`). -/
def Admissible (β : ℝ) (u : ℝ → ℝ) (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  Summable (fun t => β ^ t * u (c t)) ∧ Summable (fun t => p t * c t) ∧ ∑' t, p t * c t ≤ W

/-- Cochrane (2023), §19.5.1, p. 449: `c` maximises lifetime utility among admissible plans. -/
def IsOptimalPlan (β : ℝ) (u : ℝ → ℝ) (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  Admissible β u p W c ∧ ∀ c', Admissible β u p W c' → lifetimeU β u c' ≤ lifetimeU β u c

/-- Cochrane (2023), §19.5.1, p. 449, and footnote 1, p. 440: the consumption-only problem is the
money-in-utility time-0 problem `MoneyInUtility.Optimal` with utility independent of money and
a zero cost of money (`ι = 0`, `m = 0`), so the two-date perturbation machinery of
`MoneyInUtility` applies. -/
theorem isOptimalPlan_iff_optimal {β : ℝ} {u : ℝ → ℝ} {p : ℕ → ℝ} {W : ℝ} {c : ℕ → ℝ} :
    IsOptimalPlan β u p W c ↔
      MoneyInUtility.Optimal β (fun x _ => u x) p (fun _ => 0) W c (fun _ => 0) := by
  simp only [IsOptimalPlan, Admissible, lifetimeU, MoneyInUtility.Optimal,
    MoneyInUtility.Feasible, zero_mul, add_zero]
  constructor
  · rintro ⟨⟨hu, hs, hW⟩, hmax⟩
    exact ⟨⟨hs, hW⟩, hu, fun c' _ hf hu' => hmax c' ⟨hu', hf.1, hf.2⟩⟩
  · rintro ⟨⟨hs, hW⟩, hu, hmax⟩
    exact ⟨⟨hu, hs, hW⟩, fun c' hc' => hmax c' (fun _ => 0) ⟨hc'.2.1, hc'.2.2⟩ hc'.1⟩

/-- Cochrane (2023), (19.31), p. 450, **Fact 1, necessity**: at an optimal plan the marginal
rate of substitution between any two dates equals the price ratio:
`β^t u'(c_t) p_s = β^s u'(c_s) p_t` (perturb `c_t` by `εp_s` and `c_s` by `−εp_t`, at constant
cost, with `MoneyInUtility.perturb_le`). -/
theorem euler_necessary {β : ℝ} {u : ℝ → ℝ} {p c : ℕ → ℝ} {W : ℝ}
    (hopt : IsOptimalPlan β u p W c) {t s : ℕ} (hts : t ≠ s) {d1 d2 : ℝ}
    (h1 : HasDerivAt u d1 (c t)) (h2 : HasDerivAt u d2 (c s)) :
    β ^ t * d1 * p s = β ^ s * d2 * p t := by
  have hopt' := isOptimalPlan_iff_optimal.mp hopt
  set D : ℝ → ℝ := fun ε => β ^ t * u (c t + ε * p s) + β ^ s * u (c s - ε * p t) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := MoneyInUtility.perturb_le (c' := Function.update (Function.update c t
      (c t + ε * p s)) s (c s - ε * p t)) (m' := fun _ => 0) hopt' hts (fun k hkt hks => by
        simp [Function.update_of_ne hks, Function.update_of_ne hkt]) (fun _ _ _ => rfl)
      (by simp [Function.update_of_ne hts]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => c t + ε * p s) (p s) 0 := by
    simpa using (hasDerivAt_mul_const (p s)).const_add (c t)
  have hd2 : HasDerivAt (fun ε => c s - ε * p t) (-p t) 0 := by
    simpa using (hasDerivAt_mul_const (p t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t + ε * p s)) (d1 * p s) 0 :=
    HasDerivAt.comp_of_eq 0 h1 hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * p t)) (d2 * -p t) 0 :=
    HasDerivAt.comp_of_eq 0 h2 hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (d1 * p s) + β ^ s * (d2 * -p t)) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), §19.5.4, p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), **sufficiency**: if `u` lies below its tangent lines at the plan
(`u x ≤ u(c_τ) + u'_τ(x − c_τ)`, concavity), the first-order conditions
`β^τ u'_τ = λp_τ` hold with `λ ≥ 0`, `β ≥ 0`, and the budget binds, then the plan is optimal. -/
theorem euler_sufficient {β : ℝ} {u : ℝ → ℝ} {p c du : ℕ → ℝ} {W lam : ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (hconc : ∀ τ x, u x ≤ u (c τ) + du τ * (x - c τ))
    (hfoc : ∀ τ, β ^ τ * du τ = lam * p τ) (hadm : Admissible β u p W c)
    (hbind : ∑' τ, p τ * c τ = W) : IsOptimalPlan β u p W c := by
  refine ⟨hadm, fun c' hc' => ?_⟩
  have hle : ∀ τ, β ^ τ * u (c' τ) - β ^ τ * u (c τ) ≤ lam * (p τ * c' τ - p τ * c τ) := by
    intro τ
    have h := mul_le_mul_of_nonneg_left (hconc τ (c' τ)) (pow_nonneg hβ τ)
    have : lam * (p τ * c' τ - p τ * c τ) = β ^ τ * du τ * (c' τ - c τ) := by
      rw [hfoc τ]
      ring
    rw [this]
    nlinarith
  have hs1 : Summable (fun τ => β ^ τ * u (c' τ) - β ^ τ * u (c τ)) := hc'.1.sub hadm.1
  have hs2 : Summable (fun τ => lam * (p τ * c' τ - p τ * c τ)) :=
    (hc'.2.1.sub hadm.2.1).mul_left lam
  have htot := hs1.tsum_le_tsum hle hs2
  rw [hc'.1.tsum_sub hadm.1, tsum_mul_left, hc'.2.1.tsum_sub hadm.2.1] at htot
  unfold lifetimeU
  have : lam * (∑' τ, p τ * c' τ - ∑' τ, p τ * c τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hc'.2.2])
  linarith

/-- Cochrane (2023), (19.31), p. 450 and (19.36), p. 452, **Fact 1**: if consuming the endowment
`y` is optimal at the state prices `Λ > 0` and `u'(y_t) ≠ 0` (and `β > 0`), then
`β^j u'(y_{t+j})/u'(y_t) = Λ_{t+j}/Λ_t`. -/
theorem sdf_19_31 {β : ℝ} {u : ℝ → ℝ} {Λ y du : ℕ → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u Λ W y) (hΛ : ∀ t, 0 < Λ t)
    (hdu : ∀ t, HasDerivAt u (du t) (y t)) (hdu0 : ∀ t, du t ≠ 0) (t j : ℕ) :
    β ^ j * du (t + j) / du t = Λ (t + j) / Λ t := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have := hdu0 t
    have := (hΛ t).ne'
    simp only [pow_zero, one_mul, add_zero]
    field_simp
  · have h := euler_necessary hopt (s := t + j) (by omega) (hdu t) (hdu (t + j))
    have := hdu0 t
    have := (hΛ t).ne'
    rw [pow_add] at h
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [div_eq_div_iff (hdu0 t) (hΛ t).ne']
    have := mul_left_cancel₀ hb (by linear_combination h :
      β ^ t * (du t * Λ (t + j)) = β ^ t * (β ^ j * du (t + j) * Λ t))
    linarith

/-- Cochrane (2023), p. 450 and (19.36), p. 452: with a constant endowment, `Λ_{t+j}/Λ_t = β^j`. -/
theorem sdf_const_endowment {β : ℝ} {u : ℝ → ℝ} {Λ : ℕ → ℝ} {W ybar d : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u Λ W (fun _ => ybar)) (hΛ : ∀ t, 0 < Λ t)
    (hdu : HasDerivAt u d ybar) (hd0 : d ≠ 0) (t j : ℕ) :
    Λ (t + j) / Λ t = β ^ j := by
  have := sdf_19_31 (du := fun _ => d) hβ hopt hΛ (fun _ => hdu) (fun _ => hd0) t j
  rw [← this]
  field_simp

/-- Cochrane (2023), p. 450 (the `V ≠ 1` wedge): if consuming a constant endowment is optimal at
the effective consumption prices `Λ_tw_t` (`w_t = 1 + (1 − Q_t)(1/V − 1)`,
`MoneyDemand.binding_cost_wedge`), then `Λ_{t+1}/Λ_t = βw_t/w_{t+1}`; this equals `β` iff
`w_t = w_{t+1}`, which holds for `V = 1` (`MoneyDemand.wedge_eq_one_iff`) but not in general. -/
theorem sdf_wedge {β : ℝ} {u : ℝ → ℝ} {Λ w : ℕ → ℝ} {W ybar d : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u (fun t => Λ t * w t) W (fun _ => ybar)) (hΛ : ∀ t, 0 < Λ t)
    (hw : ∀ t, 0 < w t) (hdu : HasDerivAt u d ybar) (hd0 : d ≠ 0) (t : ℕ) :
    Λ (t + 1) / Λ t = β * w t / w (t + 1) := by
  have h := sdf_const_endowment hβ hopt (fun t => mul_pos (hΛ t) (hw t)) hdu hd0 t 1
  have := (hΛ t).ne'
  have := (hw t).ne'
  have := (hw (t + 1)).ne'
  simp only [pow_one] at h
  field_simp at h ⊢
  linear_combination h

end Euler

/-! ## The household problem on a finite event tree (genuine uncertainty) -/

namespace TreeEuler

open ExpectationsFiniteTree

variable {Ω : Type*} [Fintype Ω] (T : FiniteTree Ω)

/-- Cochrane (2023), §19.5.1, p. 448: a plan is measurable (date-`t` choices depend only on the
date-`t` information cell of the event tree). -/
def Meas (x : ℕ → Ω → ℝ) : Prop := ∀ t ω ω', T.info t ω ω' → x t ω = x t ω'

/-- Cochrane (2023), §19.5.1, p. 448: expected lifetime utility `E Σ_t β^t u(c_t)`. -/
noncomputable def expU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : ℝ :=
  ∑' t, β ^ t * ∑ ω, T.prob ω * u (c t ω)

/-- Cochrane (2023), (19.30), p. 449: the date-`t` present-value cost `E[Λ_tc_t]` of a
consumption plan at the state-price density `Λ`. -/
noncomputable def pvCost (Λ c : ℕ → Ω → ℝ) (t : ℕ) : ℝ := ∑ ω, T.prob ω * (Λ t ω * c t ω)

/-- Cochrane (2023), (19.24)–(19.30), pp. 448–449: **the cash-in-advance household's problem
on an event tree, present-value form.** With `V = 1` the binding overnight money
`Pc + P(y − c) = Py` does not depend on consumption (`cia_min_V1`), so, money and bonds chosen
optimally, the budget (19.30) — equivalent to the flow budget (19.27) plus the TVC (19.28) by
`Stochastic.pv_19_30` — reads `Σ_t E[Λ_tc_t] ≤ W` with every other term in `W`. A plan is
admissible when it is measurable, expected utility and present value converge absolutely, and
the budget holds. -/
def Admissible (β : ℝ) (u : ℝ → ℝ) (Λ : ℕ → Ω → ℝ) (W : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  Meas T c ∧ Summable (fun t => β ^ t * ∑ ω, T.prob ω * u (c t ω)) ∧
    Summable (pvCost T Λ c) ∧ ∑' t, pvCost T Λ c t ≤ W

/-- Cochrane (2023), §19.5.1, p. 449: `c` maximises expected utility among admissible plans. -/
def IsOptimal (β : ℝ) (u : ℝ → ℝ) (Λ : ℕ → Ω → ℝ) (W : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  Admissible T β u Λ W c ∧ ∀ c', Admissible T β u Λ W c' → expU T β u c' ≤ expU T β u c

/-- Cochrane (2023), (19.24)–(19.25), p. 448: with `V = 1` the minimum overnight money
`Pc/V + P(y − c)` is `Py`, independent of consumption (no monetary wedge, cf.
`MoneyDemand.wedge_eq_one_iff`). -/
theorem cia_min_V1 (P c y : ℝ) : P * c / 1 + P * (y - c) = P * y := by ring

/-- Cochrane (2023), (19.31), p. 450, **Fact 1 under uncertainty, necessity**: at an optimal
plan, for any two nodes `(t, ω₀)` and `(s, ω₁)` with `t ≠ s`,
`β^t u'(c_t(ω₀)) Λ_s(ω₁) = β^s u'(c_s(ω₁)) Λ_t(ω₀)` (state prices measurable and positive). The
proof raises consumption by `ε` on the date-`t` information cell of `ω₀` and lowers it on the
date-`s` cell of `ω₁` by the amount that leaves the present value unchanged. -/
theorem euler_necessary {β : ℝ} {u : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ} {W : ℝ}
    (hopt : IsOptimal T β u Λ W c) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    {t s : ℕ} (hts : t ≠ s) (ω₀ ω₁ : Ω) {d1 d2 : ℝ}
    (h1 : HasDerivAt u d1 (c t ω₀)) (h2 : HasDerivAt u d2 (c s ω₁)) :
    β ^ t * d1 * Λ s ω₁ = β ^ s * d2 * Λ t ω₀ := by
  classical
  have hcm := hopt.1.1
  have hmA := T.mass_pos t ω₀
  have hmB := T.mass_pos s ω₁
  have hΛA := hΛ t ω₀
  have hΛB := hΛ s ω₁
  set k := T.mass t ω₀ * Λ t ω₀ / (T.mass s ω₁ * Λ s ω₁) with hk
  -- the cell-perturbation identity (`MoneyInUtility.FootnoteTree.sum_perturb_cell`)
  have key : ∀ (r : ℕ) (ω₂ : Ω) (a : ℝ) (F : Ω → ℝ → ℝ),
      (∀ ω, T.info r ω ω₂ → F ω = F ω₂) →
      ∑ ω, T.prob ω * F ω (if T.info r ω ω₂ then a else 0) - ∑ ω, T.prob ω * F ω 0 =
        T.mass r ω₂ * (F ω₂ a - F ω₂ 0) := by
    intro r ω₂ a F hF
    have h := MoneyInUtility.FootnoteTree.sum_perturb_cell T (t := r) (ω0 := ω₂) F
      (fun _ => 0) (fun _ _ => rfl) hF a
    have e : ∀ ω, (if T.info r ω ω₂ then a else 0) =
        0 + a * MoneyInUtility.FootnoteTree.cell T r ω₂ ω := by
      intro ω
      unfold MoneyInUtility.FootnoteTree.cell
      split_ifs <;> simp
    simp only [e]
    simp only [zero_add] at h ⊢
    linarith
  let pert : ℝ → ℕ → Ω → ℝ := fun ε τ ω =>
    c τ ω + (if τ = t ∧ T.info t ω ω₀ then ε else 0) +
      (if τ = s ∧ T.info s ω ω₁ then -(ε * k) else 0)
  have hpt : ∀ ε ω, pert ε t ω = c t ω + (if T.info t ω ω₀ then ε else 0) := by
    intro ε ω
    simp [pert, hts]
  have hps : ∀ ε ω, pert ε s ω = c s ω + (if T.info s ω ω₁ then -(ε * k) else 0) := by
    intro ε ω
    simp [pert, Ne.symm hts]
  have hpo : ∀ ε τ ω, τ ≠ t → τ ≠ s → pert ε τ ω = c τ ω := by
    intro ε τ ω h1 h2
    simp [pert, h1, h2]
  -- the perturbed plan is measurable
  have hmeas : ∀ ε, Meas T (pert ε) := by
    intro ε τ ω ω' h
    have e1 : (τ = t ∧ T.info t ω ω₀) ↔ (τ = t ∧ T.info t ω' ω₀) := by
      constructor <;> rintro ⟨rfl, h'⟩ <;> refine ⟨rfl, ?_⟩
      · exact (T.info τ).trans ((T.info τ).symm h) h'
      · exact (T.info τ).trans h h'
    have e2 : (τ = s ∧ T.info s ω ω₁) ↔ (τ = s ∧ T.info s ω' ω₁) := by
      constructor <;> rintro ⟨rfl, h'⟩ <;> refine ⟨rfl, ?_⟩
      · exact (T.info τ).trans ((T.info τ).symm h) h'
      · exact (T.info τ).trans h h'
    simp only [pert]
    rw [hcm τ ω ω' h, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  -- cost differences, date by date
  have hcostt : ∀ ε, pvCost T Λ (pert ε) t - pvCost T Λ c t = T.mass t ω₀ * (Λ t ω₀ * ε) := by
    intro ε
    unfold pvCost
    simp only [hpt]
    have := key t ω₀ ε (fun ω x => Λ t ω * (c t ω + x)) (fun ω h => by
      funext x; simp only [hΛm t ω ω₀ h, hcm t ω ω₀ h])
    simp only [add_zero] at this
    rw [this]
    ring
  have hcosts : ∀ ε, pvCost T Λ (pert ε) s - pvCost T Λ c s =
      T.mass s ω₁ * (Λ s ω₁ * -(ε * k)) := by
    intro ε
    unfold pvCost
    simp only [hps]
    have := key s ω₁ (-(ε * k)) (fun ω x => Λ s ω * (c s ω + x)) (fun ω h => by
      funext x; simp only [hΛm s ω ω₁ h, hcm s ω ω₁ h])
    simp only [add_zero] at this
    rw [this]
    ring
  have hcosto : ∀ ε τ, τ ∉ ({t, s} : Finset ℕ) → pvCost T Λ (pert ε) τ - pvCost T Λ c τ = 0 := by
    intro ε τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
    unfold pvCost
    simp only [hpo ε τ _ hτ.1 hτ.2, sub_self]
  -- utility differences, date by date
  let φ : ℝ → ℝ := fun ε => β ^ t * (T.mass t ω₀ * u (c t ω₀ + ε)) +
    β ^ s * (T.mass s ω₁ * u (c s ω₁ + -(ε * k)))
  have hut : ∀ ε, β ^ t * ∑ ω, T.prob ω * u (pert ε t ω) - β ^ t * ∑ ω, T.prob ω * u (c t ω) =
      β ^ t * (T.mass t ω₀ * (u (c t ω₀ + ε) - u (c t ω₀))) := by
    intro ε
    simp only [hpt]
    have := key t ω₀ ε (fun ω x => u (c t ω + x)) (fun ω h => by
      funext x; simp only [hcm t ω ω₀ h])
    simp only [add_zero] at this
    rw [← mul_sub, this]
  have hus : ∀ ε, β ^ s * ∑ ω, T.prob ω * u (pert ε s ω) - β ^ s * ∑ ω, T.prob ω * u (c s ω) =
      β ^ s * (T.mass s ω₁ * (u (c s ω₁ + -(ε * k)) - u (c s ω₁))) := by
    intro ε
    simp only [hps]
    have := key s ω₁ (-(ε * k)) (fun ω x => u (c s ω + x)) (fun ω h => by
      funext x; simp only [hcm s ω ω₁ h])
    simp only [add_zero] at this
    rw [← mul_sub, this]
  have huo : ∀ ε τ, τ ∉ ({t, s} : Finset ℕ) →
      β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) - β ^ τ * ∑ ω, T.prob ω * u (c τ ω) = 0 := by
    intro ε τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
    simp only [hpo ε τ _ hτ.1 hτ.2, sub_self]
  -- admissibility and value of the perturbed plan
  have hadm : ∀ ε, Admissible T β u Λ W (pert ε) := by
    intro ε
    have hsd : Summable (fun τ => pvCost T Λ (pert ε) τ - pvCost T Λ c τ) :=
      summable_of_ne_finset_zero (hcosto ε)
    have hsum0 : ∑' τ, (pvCost T Λ (pert ε) τ - pvCost T Λ c τ) = 0 := by
      rw [tsum_eq_sum (hcosto ε), Finset.sum_pair hts, hcostt, hcosts, hk]
      field_simp
      ring
    have hud : Summable (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) := summable_of_ne_finset_zero (huo ε)
    refine ⟨hmeas ε, (hud.add hopt.1.2.1).congr fun τ => by ring,
      (hsd.add hopt.1.2.2.1).congr fun τ => by ring, ?_⟩
    have h := hsd.tsum_add hopt.1.2.2.1
    rw [show (fun τ => pvCost T Λ (pert ε) τ) =
        fun τ => (pvCost T Λ (pert ε) τ - pvCost T Λ c τ) + pvCost T Λ c τ from
          funext fun τ => by ring, h, hsum0, zero_add]
    exact hopt.1.2.2.2
  have hval : ∀ ε, expU T β u (pert ε) = expU T β u c + (φ ε - φ 0) := by
    intro ε
    have hud : Summable (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) := summable_of_ne_finset_zero (huo ε)
    have hsum : ∑' τ, (β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) = φ ε - φ 0 := by
      rw [tsum_eq_sum (huo ε), Finset.sum_pair hts, hut, hus]
      simp only [φ, add_zero, zero_mul, neg_zero]
      ring
    unfold expU
    rw [show (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω)) =
        fun τ => (β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
          β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) + β ^ τ * ∑ ω, T.prob ω * u (c τ ω) from
          funext fun τ => by ring, hud.tsum_add hopt.1.2.1, hsum]
    ring
  have hmax : IsLocalMax φ 0 := Filter.Eventually.of_forall fun ε => by
    have := hopt.2 (pert ε) (hadm ε)
    rw [hval ε] at this
    linarith
  have hd1 : HasDerivAt (fun ε => β ^ t * (T.mass t ω₀ * u (c t ω₀ + ε)))
      (β ^ t * (T.mass t ω₀ * d1)) 0 :=
    ((HasDerivAt.comp_const_add (c t ω₀) 0 (by simpa using h1)).const_mul _).const_mul _
  have hin : HasDerivAt (fun ε : ℝ => c s ω₁ + -(ε * k)) (-(1 * k)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const k).neg).const_add (c s ω₁)
  have h2' : HasDerivAt u d2 (c s ω₁ + -(0 * k)) := by simpa using h2
  have hd2 : HasDerivAt (fun ε => β ^ s * (T.mass s ω₁ * u (c s ω₁ + -(ε * k))))
      (β ^ s * (T.mass s ω₁ * (d2 * -(1 * k)))) 0 :=
    ((h2'.comp 0 hin).const_mul _).const_mul _
  have hder := hmax.hasDerivAt_eq_zero (HasDerivAt.add hd1 hd2)
  rw [hk] at hder
  field_simp at hder
  have hmA' := hmA.ne'
  have := mul_left_cancel₀ hmA' (by linear_combination hder :
    T.mass t ω₀ * (β ^ t * d1 * Λ s ω₁) = T.mass t ω₀ * (β ^ s * d2 * Λ t ω₀))
  exact this

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), **sufficiency under uncertainty**: if `u` lies below its tangent
lines at the plan, the node-by-node first-order conditions `β^τ u'(c_τ(ω)) = λΛ_τ(ω)` hold with
`λ ≥ 0`, `β ≥ 0`, and the present-value budget (which embodies the TVC, `Stochastic.pv_19_30`)
binds, then the plan is optimal. -/
theorem euler_sufficient {β : ℝ} {u : ℝ → ℝ} {Λ c du : ℕ → Ω → ℝ} {W lam : ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (hconc : ∀ τ ω x, u x ≤ u (c τ ω) + du τ ω * (x - c τ ω))
    (hfoc : ∀ τ ω, β ^ τ * du τ ω = lam * Λ τ ω) (hadm : Admissible T β u Λ W c)
    (hbind : ∑' τ, pvCost T Λ c τ = W) : IsOptimal T β u Λ W c := by
  refine ⟨hadm, fun c' hc' => ?_⟩
  have hle : ∀ τ, β ^ τ * ∑ ω, T.prob ω * u (c' τ ω) - β ^ τ * ∑ ω, T.prob ω * u (c τ ω) ≤
      lam * (pvCost T Λ c' τ - pvCost T Λ c τ) := by
    intro τ
    unfold pvCost
    rw [← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hp := (T.prob_pos ω).le
    have h := hconc τ ω (c' τ ω)
    have hb := pow_nonneg hβ τ
    have e : lam * (T.prob ω * (Λ τ ω * c' τ ω) - T.prob ω * (Λ τ ω * c τ ω)) =
        T.prob ω * (β ^ τ * du τ ω * (c' τ ω - c τ ω)) := by
      rw [hfoc τ ω]
      ring
    rw [e]
    have h2 : β ^ τ * (u (c' τ ω) - u (c τ ω)) ≤ β ^ τ * du τ ω * (c' τ ω - c τ ω) := by
      have := mul_le_mul_of_nonneg_left h hb
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 hp
    nlinarith
  have hs1 := hc'.2.1.sub hadm.2.1
  have hs2 := (hc'.2.2.1.sub hadm.2.2.1).mul_left lam
  have htot := hs1.tsum_le_tsum hle hs2
  rw [hc'.2.1.tsum_sub hadm.2.1, tsum_mul_left, hc'.2.2.1.tsum_sub hadm.2.2.1] at htot
  unfold expU
  have : lam * (∑' τ, pvCost T Λ c' τ - ∑' τ, pvCost T Λ c τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hc'.2.2.2])
  linarith

/-- Cochrane (2023), (19.31), p. 450, **Fact 1 under uncertainty**: if consuming the endowment
`y` is optimal at the state-price density `Λ > 0` (measurable), `β > 0` and `u'(y_t(ω)) ≠ 0`, then
state by state `Λ_{t+j}(ω)/Λ_t(ω) = β^j u'(y_{t+j}(ω))/u'(y_t(ω))`. -/
theorem sdf_19_31 {β : ℝ} {u : ℝ → ℝ} {Λ y uc : ℕ → Ω → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, uc t ω ≠ 0) (t j : ℕ) (ω : Ω) :
    Λ (t + j) ω / Λ t ω = β ^ j * uc (t + j) ω / uc t ω := by
  have h0 := (hΛ t ω).ne'
  have h1 := huc t ω
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [add_zero, pow_zero, one_mul]
    rw [div_self h0, div_self h1]
  · have h := euler_necessary T hopt hΛm hΛ (t := t) (s := t + j) (by omega) ω ω
      (hdu t ω) (hdu (t + j) ω)
    rw [pow_add] at h
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [div_eq_div_iff h0 h1]
    have := mul_left_cancel₀ hb (by linear_combination h :
      β ^ t * (uc t ω * Λ (t + j) ω) = β ^ t * (β ^ j * uc (t + j) ω * Λ t ω))
    linarith

/-- Cochrane (2023), (19.31), p. 450: with the normalisation `Λ_0 = u'(y_0)` (state prices are
defined up to scale), optimality of `y` gives `Λ_t = β^t u'(y_t)` at every node. -/
theorem sdf_eq {β : ℝ} {u : ℝ → ℝ} {Λ y uc : ℕ → Ω → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, uc t ω ≠ 0)
    (hnorm : Λ 0 = uc 0) (t : ℕ) : Λ t = β ^ t • uc t := by
  funext ω
  have h := sdf_19_31 T hβ hopt hΛm hΛ hdu huc 0 t ω
  rw [zero_add, hnorm] at h
  have := huc 0 ω
  rw [div_eq_div_iff this this] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ this (by linarith)

/-- Cochrane (2023), (19.32), p. 450, **bond price from household optimality under
uncertainty**: on a finite event tree, if consuming the endowment is optimal at state prices
`Λ` (normalised `Λ_0 = u'(y_0)`), `u'(y) > 0`, the price level is adapted and positive and the
nominal bond price is `Λ_tQ_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, then
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]`; `Λ_t = β^tu'(y_t)` is derived (`sdf_eq`),
not assumed. -/
theorem bond_price_from_optimality {β : ℝ} {u : ℝ → ℝ} {Λ y uc P Q : ℕ → Ω → ℝ} {W : ℝ}
    (hβ : 0 < β) (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, 0 < uc t ω)
    (hnorm : Λ 0 = uc 0) (hPa : T.toExpectationSystem.Adapted P) (hP : ∀ t ω, 0 < P t ω)
    (hQ : ∀ t, Λ t * Q t / P t = T.toExpectationSystem.E t (Λ (t + 1) / P (t + 1))) (t : ℕ) :
    Q t = β • T.toExpectationSystem.E t (uc (t + 1) / uc t * (P t / P (t + 1))) := by
  have hucA : T.toExpectationSystem.Adapted uc := by
    intro τ
    rw [FiniteTree.toExpectationSystem_E]
    funext ω
    refine T.condE_of_const_on_cell fun ω' h => ?_
    have hy : y τ ω' = y τ ω := hopt.1.1 τ ω' ω h
    have h1 := hdu τ ω'
    rw [hy] at h1
    exact h1.unique (hdu τ ω)
  exact Stochastic.bond_price_19_32 T.toExpectationSystem (finiteTree_pullOut T) hβ huc hucA
    (sdf_eq T hβ hopt hΛm hΛ hdu (fun t ω => (huc t ω).ne') hnorm) hPa hP hQ t

end TreeEuler


/-! ## Perfect-foresight equilibria with a constant endowment -/

namespace PF

/-- Cochrane (2023), (19.32), p. 450: with a constant endowment (`Λ_{t+1}/Λ_t = β`, Fact 1) the
nominal bond price is `Q_t = βP_t/P_{t+1}`. -/
noncomputable def bondPrice (β : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := β * P t / P (t + 1)

/-- Cochrane (2023), p. 450 (**E15**): with a constant endowment `Q_t = βP_t/P_{t+1}`, which
equals `β` iff the price level is constant between `t` and `t + 1` (the book's "`Q = β`"). -/
theorem bondPrice_eq_beta_iff {β : ℝ} {P : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t) (t : ℕ) :
    bondPrice β P t = β ↔ P (t + 1) = P t := by
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  unfold bondPrice
  rw [div_eq_iff h2]
  constructor
  · intro h
    have := mul_left_cancel₀ hβ.ne' (by linarith : β * P t = β * P (t + 1))
    linarith
  · intro h
    rw [h]

/-- Cochrane (2023), (19.32), p. 450: for a constant price level `Q_t = β`. -/
theorem bondPrice_const {β p : ℝ} (hp : p ≠ 0) (t : ℕ) : bondPrice β (fun _ => p) t = β := by
  unfold bondPrice
  field_simp

/-- Cochrane (2023), p. 454: along `P_t = β^tP_0` (deflation at the real rate) `Q_t = 1`, i.e.
`i_t = 0`. -/
theorem bondPrice_deflation {β P0 : ℝ} (hβ : 0 < β) (hP0 : 0 < P0) (t : ℕ) :
    bondPrice β (fun t => β ^ t * P0) t = 1 := by
  unfold bondPrice
  have := (pow_pos hβ t).ne'
  have := hP0.ne'
  change β * (β ^ t * P0) / (β ^ (t + 1) * P0) = 1
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), p. 454: along `P_t = P_{−1}(1+μ)^{t+1}` (the quantity-theory path)
`Q_t = β/(1 + μ)`, i.e. `1 + i = (1 + δ)(1 + μ)` with `1 + δ = 1/β`. -/
theorem bondPrice_growth {β c g : ℝ} (hc : c ≠ 0) (hg : g ≠ 0) (t : ℕ) :
    bondPrice β (fun t => c * g ^ (t + 1)) t = β / g := by
  unfold bondPrice
  have := pow_ne_zero (t + 1) hg
  change β * (c * g ^ (t + 1)) / (c * g ^ (t + 1 + 1)) = β / g
  rw [pow_succ g (t + 1)]
  field_simp

/-- Cochrane (2023), (19.28)–(19.30), p. 449 (deterministic version): if `z_t = z_{t+1} + f_t` and
`j ↦ f_{t+j}` is summable, then `z_T → 0` iff `z_t = Σ_j f_{t+j}`. -/
theorem pv_of_rec {z f : ℕ → ℝ} (hrec : ∀ t, z t = z (t + 1) + f t) (t : ℕ)
    (hs : Summable fun j => f (t + j)) :
    Tendsto z atTop (𝓝 0) ↔ z t = ∑' j, f (t + j) := by
  have hpart : ∀ n, z (t + n) = z t - ∑ j ∈ Finset.range n, f (t + j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, show t + (n + 1) = t + n + 1 by omega]
      have := hrec (t + n)
      linarith
  rw [← tendsto_add_atTop_iff_nat t]
  have hfun : (fun n => z (n + t)) = fun n => z t - ∑ j ∈ Finset.range n, f (t + j) :=
    funext fun n => by rw [add_comm, hpart]
  rw [hfun]
  have hlim := hs.hasSum.tendsto_sum_nat
  constructor
  · intro h
    have := tendsto_nhds_unique h (hlim.const_sub (z t))
    linarith
  · intro h
    have := hlim.const_sub (z t)
    rwa [← h, sub_self] at this

/-- Cochrane (2023), (19.27), p. 449 (perfect foresight, `c = y`, `Λ_t = β^t`): the flow budget
gives `β^t(B_{t−1} + M_{t−1})/P_t = β^{t+1}(B_t + M_t)/P_{t+1} + β^t(s_t + (1 − Q_t)M_t/P_t)`. -/
theorem rec_of_flow {β : ℝ} {P Bin Min s : ℕ → ℝ} (hpos : ∀ t, 0 < P t)
    (hflow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    β ^ t * (Bin t + Min t) / P t = β ^ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1) +
      β ^ t * (s t + (1 - bondPrice β P t) * Min (t + 1) / P t) := by
  have h1 := (hpos t).ne'
  have h2 := (hpos (t + 1)).ne'
  rw [hflow t]
  unfold bondPrice
  rw [pow_succ]
  field_simp
  ring

/-- Cochrane (2023), (19.35), p. 450 (perfect foresight): **valuation iff transversality.** Under
the flow budget, with `β > 0` and the flows summable, the TVC (19.28)
`β^T(B_{T−1} + M_{T−1})/P_T → 0` holds iff
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j(s_{t+j} + (1 − Q_{t+j})M_{t+j}/P_{t+j})`. -/
theorem valuation_iff {β : ℝ} {P Bin Min s : ℕ → ℝ} (hβ : 0 < β) (hpos : ∀ t, 0 < P t)
    (hflow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) (hs : Summable fun j =>
      β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) :
    Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0) ↔
      (Bin t + Min t) / P t = ∑' j,
        β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
  have hs' : Summable fun j => β ^ (t + j) *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) :=
    (hs.mul_left (β ^ t)).congr fun j => by rw [pow_add]; ring
  rw [pv_of_rec (f := fun τ => β ^ τ * (s τ + (1 - bondPrice β P τ) * Min (τ + 1) / P τ))
    (z := fun τ => β ^ τ * (Bin τ + Min τ) / P τ) (rec_of_flow hpos hflow) t hs']
  have hsum : ∑' j, β ^ (t + j) *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) =
      β ^ t * ∑' j, β ^ j *
        (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
    rw [← tsum_mul_left]
    congr 1
    funext j
    rw [pow_add]
    ring
  rw [hsum]
  have hb := (pow_pos hβ t).ne'
  have hp := (hpos t).ne'
  constructor
  · intro h
    have h' : β ^ t * ((Bin t + Min t) / P t) = β ^ t * ∑' j, β ^ j *
        (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hb h'
  · intro h
    rw [← h]
    ring

variable (β y V : ℝ) (P Bin Min s : ℕ → ℝ)

/-- Cochrane (2023), §19.5.4, pp. 449, 452: a perfect-foresight equilibrium of the
**frictionless** model with a constant endowment (`c = y`, `Λ_t = β^t` by (19.36),
`Q_t = βP_t/P_{t+1}`): positive prices; optimal overnight money, i.e. `M_t ≥ 0`, `Q_t ≤ 1` and
`Q_t < 1 ⇒ M_t = 0` (`frictionless_money_optimal`); the flow budget (19.27); and the
transversality condition (19.28). -/
structure FrictionlessEq where
  pos : ∀ t, 0 < P t
  money_nonneg : ∀ t, 0 ≤ Min (t + 1)
  rate_nonneg : ∀ t, bondPrice β P t ≤ 1
  no_money : ∀ t, bondPrice β P t < 1 → Min (t + 1) = 0
  flow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t
  tvc : Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0)

/-- Cochrane (2023), §19.5.2, pp. 449–450: a perfect-foresight equilibrium of the **monetary**
(cash-in-advance) model with a constant endowment `y` and velocity `V > 0`: positive prices;
optimal overnight money, i.e. `M_t ≥ P_ty/V` ((19.24)–(19.25) at `c = y`), `Q_t ≤ 1` and
`Q_t < 1 ⇒ M_t = P_ty/V` (`monetary_money_optimal`); the flow budget (19.27); and the
transversality condition (19.28). -/
structure MonetaryEq where
  pos : ∀ t, 0 < P t
  cia : ∀ t, P t * y / V ≤ Min (t + 1)
  rate_nonneg : ∀ t, bondPrice β P t ≤ 1
  binds : ∀ t, bondPrice β P t < 1 → Min (t + 1) = P t * y / V
  flow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t
  tvc : Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0)

variable {β y V P Bin Min s}

/-- Cochrane (2023), (19.37), p. 452: the money conditions of `FrictionlessEq` at date `t` are
exactly optimality of the overnight money holding with minimum `0` (any wealth `W`). -/
theorem frictionless_money_optimal_iff {W : ℝ} (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) 0 W (Min (t + 1)) ↔
      bondPrice β P t ≤ 1 ∧ 0 ≤ Min (t + 1) ∧ (bondPrice β P t < 1 → Min (t + 1) = 0) :=
  MoneyDemand.optimal_iff

/-- Cochrane (2023), (19.37), p. 452: in a frictionless equilibrium overnight money is optimal. -/
theorem frictionless_money_optimal (h : FrictionlessEq β P Bin Min s) (W : ℝ) (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) 0 W (Min (t + 1)) :=
  MoneyDemand.optimal_iff.2 ⟨h.rate_nonneg t, h.money_nonneg t, h.no_money t⟩

/-- Cochrane (2023), (19.33), p. 450: in a monetary equilibrium overnight money is optimal, with
minimum `P_ty/V`. -/
theorem monetary_money_optimal (h : MonetaryEq β y V P Bin Min s) (W : ℝ) (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) (P t * y / V) W (Min (t + 1)) :=
  MoneyDemand.optimal_iff.2 ⟨h.rate_nonneg t, h.cia t, h.binds t⟩

/-- Cochrane (2023), (19.33), p. 450, **Fact 2** in equilibrium: positive nominal rate ⇒
`M_tV = P_ty`. -/
theorem monetary_fact2 (h : MonetaryEq β y V P Bin Min s) (hV : 0 < V) {t : ℕ}
    (hQ : bondPrice β P t < 1) : Min (t + 1) * V = P t * y := by
  rw [h.binds t hQ]
  field_simp

/-- Cochrane (2023), (19.38), p. 452, **corrected**: in a frictionless equilibrium the seigniorage
term vanishes, `(1 − Q_t)M_t = 0` (either `M_t = 0` or `Q_t = 1`). -/
theorem frictionless_seigniorage_zero (h : FrictionlessEq β P Bin Min s) (t : ℕ) :
    (1 - bondPrice β P t) * Min (t + 1) = 0 := by
  rcases lt_or_eq_of_le (h.rate_nonneg t) with hQ | hQ
  · rw [h.no_money t hQ, mul_zero]
  · rw [hQ, sub_self, zero_mul]

/-- Cochrane (2023), (19.35), p. 450: in a monetary equilibrium the seigniorage term is
`(1 − Q_t)M_t/P_t = (1 − Q_t)y/V` (binding constraint, or `Q_t = 1`). -/
theorem monetary_seigniorage (h : MonetaryEq β y V P Bin Min s) (hV : 0 < V) (t : ℕ) :
    (1 - bondPrice β P t) * Min (t + 1) / P t = (1 - bondPrice β P t) * y / V := by
  have hp := (h.pos t).ne'
  have := hV.ne'
  rcases lt_or_eq_of_le (h.rate_nonneg t) with hQ | hQ
  · rw [h.binds t hQ]
    field_simp
  · rw [hQ]
    ring

/-- Cochrane (2023), (19.38), p. 452, **corrected**: in a frictionless equilibrium
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j s_{t+j}` (surpluses absolutely summable; individual surpluses
may be negative). The book prints `B_{t−1}/P_t` (see `printed_19_38_counterexample`). -/
theorem frictionless_valuation (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hs : Summable fun j => β ^ j * s (t + j)) :
    (Bin t + Min t) / P t = ∑' j, β ^ j * s (t + j) := by
  have hfun : (fun j => β ^ j *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) =
      fun j => β ^ j * s (t + j) := by
    funext j
    rw [mul_div_assoc, show (1 - bondPrice β P (t + j)) * (Min (t + j + 1) / P (t + j)) =
      (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j) by ring,
      frictionless_seigniorage_zero h (t + j), zero_div, add_zero]
  have := (valuation_iff hβ h.pos h.flow t (by rw [hfun]; exact hs)).1 h.tvc
  rwa [hfun] at this

/-- Cochrane (2023), (19.35), p. 450 in a monetary equilibrium:
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j(s_{t+j} + (1 − Q_{t+j})y/V)`. -/
theorem monetary_valuation (hβ : 0 < β) (hV : 0 < V) (h : MonetaryEq β y V P Bin Min s)
    (t : ℕ) (hs : Summable fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V)) :
    (Bin t + Min t) / P t = ∑' j, β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
  have hfun : (fun j => β ^ j *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) =
      fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
    funext j
    rw [monetary_seigniorage h hV (t + j)]
  have := (valuation_iff hβ h.pos h.flow t (by rw [hfun]; exact hs)).1 h.tvc
  rwa [hfun] at this

/-- Cochrane (2023), (19.38), p. 452: given the corrected valuation, the printed form
`B_{t−1}/P_t = Σ_j β^j s_{t+j}` holds iff `M_{t−1} = 0`. -/
theorem printed_19_38_iff (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hs : Summable fun j => β ^ j * s (t + j)) :
    Bin t / P t = ∑' j, β ^ j * s (t + j) ↔ Min t = 0 := by
  rw [← frictionless_valuation hβ h t hs]
  have hp := (h.pos t).ne'
  constructor
  · intro e
    field_simp at e
    linarith
  · intro e
    rw [e, add_zero]

/-- Cochrane (2023), (19.38), p. 452 (**printed form false when money is held at a zero rate**):
for `0 < β < 1`, `P_0, W > 0`, the zero-rate path `P_t = β^tP_0`, `B_{t−1} = M_{t−1} = Wβ^t/2`,
`s_t = W(1 − β)/P_0` is a frictionless equilibrium, but `B_{−1}/P_0 = W/(2P_0)` while
`Σ_j β^j s_j = W/P_0`. -/
theorem printed_19_38_counterexample (hβ0 : 0 < β) (hβ1 : β < 1) {P0 W : ℝ} (hP0 : 0 < P0)
    (hW : 0 < W) :
    FrictionlessEq β (fun t => β ^ t * P0) (fun t => W * β ^ t / 2) (fun t => W * β ^ t / 2)
        (fun _ => W * (1 - β) / P0) ∧
      W * β ^ 0 / 2 / (β ^ 0 * P0) ≠ ∑' j, β ^ j * (W * (1 - β) / P0) := by
  have hbp := bondPrice_deflation hβ0 hP0
  refine ⟨⟨fun t => mul_pos (pow_pos hβ0 t) hP0, fun t => by positivity,
    fun t => (hbp t).le, fun t ht => absurd ((hbp t) ▸ ht) (lt_irrefl 1), fun t => ?_, ?_⟩, ?_⟩
  · rw [hbp t, pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (W * β ^ T / 2 + W * β ^ T / 2) / (β ^ T * P0)) =
        fun T => W / P0 * β ^ T := by
      funext T
      have := (pow_pos hβ0 T).ne'
      field_simp
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (W / P0)
  · rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    have h1 : (1 - β) ≠ 0 := by linarith
    have hr : (1 - β)⁻¹ * (W * (1 - β) / P0) = W / P0 := by field_simp
    rw [hr]
    simp only [pow_zero, one_mul, mul_one]
    intro h
    have := hP0.ne'
    field_simp at h
    linarith

/-- Cochrane (2023), p. 453: **the frictionless price level is unique** given the government's
choices: two frictionless equilibria with the same `{B, M, s}` and `B_{t−1} + M_{t−1} ≠ 0` at
every date (surpluses absolutely summable) have the same price level. -/
theorem frictionless_price_unique (hβ : 0 < β) {P' : ℕ → ℝ} (h : FrictionlessEq β P Bin Min s)
    (h' : FrictionlessEq β P' Bin Min s) (hBM : ∀ t, Bin t + Min t ≠ 0)
    (hs : ∀ t, Summable fun j => β ^ j * s (t + j)) : P = P' := by
  funext t
  have e1 := frictionless_valuation hβ h t (hs t)
  have e2 := frictionless_valuation hβ h' t (hs t)
  rw [← e2] at e1
  have hp := (h.pos t).ne'
  have hp' := (h'.pos t).ne'
  field_simp at e1
  have := mul_left_cancel₀ (hBM t) (by linarith : (Bin t + Min t) * P' t = (Bin t + Min t) * P t)
  linarith

/-- Cochrane (2023), p. 453: in a frictionless equilibrium with `B_{t−1} + M_{t−1} > 0` the
present value of surpluses is positive and `P_t = (B_{t−1} + M_{t−1})/Σ_j β^j s_{t+j}`. -/
theorem frictionless_price_formula (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hBM : 0 < Bin t + Min t) (hs : Summable fun j => β ^ j * s (t + j)) :
    0 < ∑' j, β ^ j * s (t + j) ∧ P t = (Bin t + Min t) / ∑' j, β ^ j * s (t + j) := by
  have e := frictionless_valuation hβ h t hs
  have hpos : 0 < ∑' j, β ^ j * s (t + j) := by rw [← e]; exact div_pos hBM (h.pos t)
  refine ⟨hpos, ?_⟩
  rw [← e]
  have := (h.pos t).ne'
  field_simp

/-- Cochrane (2023), p. 453 ("rule out 0/0 problems"): with no debt, no money and no surpluses,
every constant positive price level is a frictionless equilibrium. -/
theorem zero_debt_indeterminate (hβ1 : β < 1) {P0 : ℝ} (hP0 : 0 < P0) :
    FrictionlessEq β (fun _ => P0) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  have hbp := bondPrice_const (β := β) hP0.ne'
  refine ⟨fun _ => hP0, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => by ring, ?_⟩
  simp

/-- Cochrane (2023), pp. 452–453: **the frictionless example.** With `0 < β < 1`, constant
nominal debt `B > 0`, no money and a constant surplus `s > 0`, the constant price level
`P = (1 − β)B/s` is a frictionless equilibrium (with `Q_t = β < 1`, so `M = 0` is optimal, and the
TVC `β^TB/P → 0`). -/
theorem example_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) {B sb : ℝ} (hB : 0 < B) (hs : 0 < sb) :
    FrictionlessEq β (fun _ => (1 - β) * B / sb) (fun _ => B) (fun _ => 0) (fun _ => sb) := by
  have hP : 0 < (1 - β) * B / sb := div_pos (mul_pos (by linarith) hB) hs
  have hbp := bondPrice_const (β := β) hP.ne'
  refine ⟨fun _ => hP, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => ?_, ?_⟩
  · rw [hbp t]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (B + 0) / ((1 - β) * B / sb)) =
        fun T => sb / (1 - β) * β ^ T := by
      funext T
      rw [add_zero]
      have : (1 - β) ≠ 0 := by linarith
      have := hB.ne'
      field_simp
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (sb / (1 - β))

/-- Cochrane (2023), pp. 452–453: **uniqueness in the example**: every frictionless equilibrium
with constant debt `B > 0`, no money and constant surplus `s` has `P_t = (1 − β)B/s`. -/
theorem example_unique (hβ0 : 0 < β) (hβ1 : β < 1) {B sb : ℝ} (hB : 0 < B)
    (h : FrictionlessEq β P (fun _ => B) (fun _ => 0) (fun _ => sb)) (t : ℕ) :
    P t = (1 - β) * B / sb := by
  have hsum : Summable fun j => β ^ j * (fun _ => sb) (t + j) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right sb |>.congr fun j => by ring
  have e := frictionless_valuation hβ0 h t hsum
  simp only [add_zero] at e
  rw [show (∑' j, β ^ j * sb) = sb / (1 - β) by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]; ring] at e
  have hp := (h.pos t).ne'
  have h1 : (1 - β) ≠ 0 := by linarith
  have hsb : sb ≠ 0 := by
    intro h0
    rw [h0, zero_div] at e
    exact (div_pos hB (h.pos t)).ne' e
  field_simp at e
  field_simp
  linarith

/-- Cochrane (2023), p. 453 (**E14**): in the example equilibrium `Q_t = β < 1`, so the printed
requirement "`Q_t ≥ 1`" fails in an equilibrium; the correct requirement is `Q_t ≤ 1`. -/
theorem E14_example (hβ1 : β < 1) {B sb : ℝ} (hP : (1 - β) * B / sb ≠ 0) (t : ℕ) :
    bondPrice β (fun _ => (1 - β) * B / sb) t < 1 ∧
      ¬ 1 ≤ bondPrice β (fun _ => (1 - β) * B / sb) t := by
  rw [bondPrice_const hP]
  exact ⟨hβ1, not_le.2 hβ1⟩

/-- Cochrane (2023), p. 453: a **passive** surplus rule `s_t = (1 − β)B/P_t` (surpluses respond to
the price level so as to validate it). -/
noncomputable def passiveSurplus (β B : ℝ) (P : ℕ → ℝ) : ℕ → ℝ := fun t => (1 - β) * B / P t

/-- Cochrane (2023), p. 453: **passive fiscal policy leaves the frictionless price level
undetermined**: under the passive rule every constant price level `P_0 > 0` is an equilibrium
(constant debt `B`, no money). -/
theorem passive_fiscal_indeterminate (hβ0 : 0 < β) (hβ1 : β < 1) {B : ℝ}
    {P0 : ℝ} (hP0 : 0 < P0) :
    FrictionlessEq β (fun _ => P0) (fun _ => B) (fun _ => 0)
      (passiveSurplus β B (fun _ => P0)) := by
  have hbp := bondPrice_const (β := β) hP0.ne'
  refine ⟨fun _ => hP0, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => ?_, ?_⟩
  · rw [hbp t]
    simp only [passiveSurplus]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (B + 0) / P0) = fun T => B / P0 * β ^ T := by
      funext T
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (B / P0)

/-- Cochrane (2023), §19.5.5, p. 454: **the standard monetary equilibrium.** With money
`M_{t−1} = M_{−1}(1+μ)^t`, `β ≤ 1 + μ`, real debt `b`, the price level `P_t = M_tV/y` and the
(passive) surplus `s = (b(1 − β) − μy/V)/(1 + μ)` form a monetary equilibrium. -/
theorem usual_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V) {μ Mm1 b : ℝ}
    (hμ : β ≤ 1 + μ) (hM : 0 < Mm1) :
    MonetaryEq β y V (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1))
      (fun t => b * (Mm1 * (1 + μ) ^ t * V / y)) (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)) := by
  have hg : 0 < 1 + μ := lt_of_lt_of_le hβ0 hμ
  have hc : 0 < Mm1 * V / y := by positivity
  have hbp := bondPrice_growth (β := β) hc.ne' hg.ne'
  refine ⟨fun t => by positivity, fun t => le_of_eq ?_, fun t => ?_, fun t _ => ?_,
    fun t => ?_, ?_⟩
  · field_simp
  · rw [hbp t, div_le_one hg]
    exact hμ
  · field_simp
  · rw [hbp t]
    have := hg.ne'
    have := hV.ne'
    have := hy.ne'
    rw [pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (b * (Mm1 * (1 + μ) ^ T * V / y) + Mm1 * (1 + μ) ^ T) /
        (Mm1 * V / y * (1 + μ) ^ (T + 1))) = fun T => (b + y / V) / (1 + μ) * β ^ T := by
      funext T
      have := (pow_pos hg T).ne'
      have := hg.ne'
      have := hV.ne'
      have := hy.ne'
      have := hM.ne'
      rw [pow_succ]
      field_simp
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul _

/-- Cochrane (2023), p. 454: along the standard path the nominal rate is positive (`Q < 1`, the
cash constraint binds) iff `1 + μ > β`; and `1/Q = (1/β)(1 + μ)`, i.e. `1 + i = (1 + δ)(1 + μ)`. -/
theorem usual_rate {μ c : ℝ} (hβ0 : 0 < β) (hc : c ≠ 0) (hg : 0 < 1 + μ) (t : ℕ) :
    (bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t < 1 ↔ β < 1 + μ) ∧
      1 / bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t = 1 / β * (1 + μ) := by
  rw [bondPrice_growth hc hg.ne']
  refine ⟨div_lt_one hg, ?_⟩
  have := hβ0.ne'
  have := hg.ne'
  field_simp

/-- Cochrane (2023), p. 454 ("Even the `MV = Py` equilibrium becomes indeterminate when money
growth is too low"): if `1 + μ < β` the quantity-theory path requires a negative nominal rate
(`Q > 1`), so it is not an equilibrium. -/
theorem usual_fails_low_growth {μ Mm1 : ℝ} (hg : 0 < 1 + μ) (hμ : 1 + μ < β)
    (hc : Mm1 * V / y ≠ 0) {Bin' s' : ℕ → ℝ} :
    ¬ MonetaryEq β y V (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1)) Bin'
      (fun t => Mm1 * (1 + μ) ^ t) s' := by
  intro h
  have := h.rate_nonneg 0
  rw [bondPrice_growth hc hg.ne', div_le_one hg] at this
  linarith

/-- Cochrane (2023), p. 450 (**E15**, explicit): along the standard monetary equilibrium
`Q_t = β/(1 + μ)`, which differs from the printed "`Q = β`" whenever `μ ≠ 0`. -/
theorem E15_counterexample {μ c : ℝ} (hβ0 : 0 < β) (hc : c ≠ 0) (hg : 0 < 1 + μ) (hμ : μ ≠ 0)
    (t : ℕ) : bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t ≠ β := by
  rw [bondPrice_growth hc hg.ne']
  intro h
  rw [div_eq_iff hg.ne'] at h
  have : β * μ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hβ0.ne' h1
  · exact hμ h1

/-- Cochrane (2023), p. 454: **deflationary equilibria for any money growth with `1 + μ ≥ β`.**
For every `P_0 > 0` with `P_0 ≤ M_0V/y` (`M_0 = M_{−1}(1 + μ)`) and any initial nominal wealth
`A_0`, the path `P_t = β^tP_0` (zero nominal rate) with money `M_{t−1} = M_{−1}(1+μ)^t`, debt
`B_{t−1} = A_0β^t − M_{t−1}` and the passive surplus `s = A_0(1 − β)/P_0` is a monetary
equilibrium: people happily hold ever larger real balances at a zero rate. -/
theorem deflation_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1)
    {μ Mm1 P0 A0 : ℝ} (hμ : β ≤ 1 + μ) (hM : 0 ≤ Mm1) (hP0 : 0 < P0)
    (hcap : P0 * y / V ≤ Mm1 * (1 + μ)) :
    MonetaryEq β y V (fun t => β ^ t * P0) (fun t => A0 * β ^ t - Mm1 * (1 + μ) ^ t)
      (fun t => Mm1 * (1 + μ) ^ t) (fun _ => A0 * (1 - β) / P0) := by
  have hg : 0 < 1 + μ := lt_of_lt_of_le hβ0 hμ
  have hbp := bondPrice_deflation hβ0 hP0
  refine ⟨fun t => mul_pos (pow_pos hβ0 t) hP0, fun t => ?_, fun t => (hbp t).le,
    fun t ht => absurd ((hbp t) ▸ ht) (lt_irrefl 1), fun t => ?_, ?_⟩
  · have hpow : β ^ t ≤ (1 + μ) ^ t := pow_le_pow_left₀ hβ0.le hμ t
    calc β ^ t * P0 * y / V = β ^ t * (P0 * y / V) := by ring
      _ ≤ β ^ t * (Mm1 * (1 + μ)) := mul_le_mul_of_nonneg_left hcap (pow_nonneg hβ0.le t)
      _ ≤ (1 + μ) ^ t * (Mm1 * (1 + μ)) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg hM hg.le)
      _ = Mm1 * (1 + μ) ^ (t + 1) := by rw [pow_succ]; ring
  · rw [hbp t, pow_succ, pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (A0 * β ^ T - Mm1 * (1 + μ) ^ T + Mm1 * (1 + μ) ^ T) /
        (β ^ T * P0)) = fun T => A0 / P0 * β ^ T := by
      funext T
      have := (pow_pos hβ0 T).ne'
      field_simp
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (A0 / P0)

/-- Cochrane (2023), p. 454: along the deflation `P_t = β^tP_0` with `M_t = M_{−1}(1+μ)^{t+1}`,
discounted real money is `β^tM_t/P_t = (1 + μ)^t M_0/P_0`. -/
theorem deflation_real_money {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0) (t : ℕ) :
    β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0) = Mm1 * (1 + μ) / P0 * (1 + μ) ^ t := by
  have := (pow_pos hβ0 t).ne'
  have := hP0.ne'
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), p. 454: in the deflationary equilibria discounted real money
`β^tM_t/P_t` grows strictly ("real money holdings grow faster than the interest rate") iff
`μ > 0` (`M_{−1}, P_0 > 0`, `1 + μ > 0`). -/
theorem deflation_real_money_grows_iff {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0)
    (hM : 0 < Mm1) (hg : 0 < 1 + μ) :
    StrictMono (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) ↔ 0 < μ := by
  have hfun : (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) =
      fun t => Mm1 * (1 + μ) / P0 * (1 + μ) ^ t :=
    funext fun t => deflation_real_money hβ0 hP0 t
  have hC : 0 < Mm1 * (1 + μ) / P0 := by positivity
  rw [hfun]
  constructor
  · intro h
    have := h (show (0 : ℕ) < 1 by norm_num)
    simp only [pow_zero, mul_one, pow_one] at this
    have := lt_of_mul_lt_mul_left (by simpa using this :
      Mm1 * (1 + μ) / P0 * 1 < Mm1 * (1 + μ) / P0 * (1 + μ)) hC.le
    linarith
  · intro hμ
    exact strictMono_nat_of_lt_succ fun n => mul_lt_mul_of_pos_left
      (pow_lt_pow_right₀ (by linarith) (Nat.lt_succ_self n)) hC

/-- Cochrane (2023), p. 454 and Online Appendix A3 (cf. E17): in the deflationary equilibria the
money transversality condition `β^tM_t/P_t → 0` holds iff `μ < 0`; it fails for every `μ ≥ 0`. -/
theorem deflation_money_tvc_iff {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0) (hM : 0 < Mm1)
    (hg : 0 < 1 + μ) :
    Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop (𝓝 0) ↔
      μ < 0 := by
  have hfun : (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) =
      fun t => Mm1 * (1 + μ) / P0 * (1 + μ) ^ t :=
    funext fun t => deflation_real_money hβ0 hP0 t
  have hC : 0 < Mm1 * (1 + μ) / P0 := by positivity
  rw [hfun]
  constructor
  · intro h
    have h2 := h.const_mul (Mm1 * (1 + μ) / P0)⁻¹
    simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at h2
    rw [tendsto_pow_atTop_nhds_zero_iff, abs_lt] at h2
    linarith [h2.2]
  · intro hμ
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le (by linarith)).const_mul
      (Mm1 * (1 + μ) / P0)
    simpa using this

/-- Cochrane (2023), p. 454: **an active fiscal policy prunes the deflationary equilibria.** Fix
the money path of the standard equilibrium (`M_{t−1} = M_{−1}(1+μ)^t`, `1 + μ > β`), its initial
nominal wealth `A_0 = B_{−1} + M_{−1} = M_{−1}(bV/y + 1)` (`b ≥ 0`) and its surplus
`s = (b(1 − β) − μy/V)/(1 + μ)` as an exogenous (active) sequence that does not respond to the
price level. Then there is no monetary equilibrium with a permanently zero nominal rate
(`Q_t = 1` for all `t`). -/
theorem active_fiscal_prunes (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hb : 0 ≤ b) {P' Bin' : ℕ → ℝ}
    (h : MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)))
    (hA : Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1))
    (hzero : ∀ t, bondPrice β P' t = 1) : False := by
  have hg : 0 < 1 + μ := lt_trans hβ0 hμ
  set sv := (b * (1 - β) - μ * y / V) / (1 + μ) with hsv
  have hsum : Summable fun j => β ^ j * ((fun _ => sv) (0 + j) +
      (1 - bondPrice β P' (0 + j)) * y / V) := by
    refine ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right sv).congr fun j => ?_
    simp only [hzero, sub_self, zero_mul, zero_div, add_zero]
  have e := monetary_valuation hβ0 hV h 0 hsum
  simp only [hzero, sub_self, zero_mul, zero_div, add_zero, zero_add] at e
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, hA] at e
  have hcia := h.cia 0
  simp only [zero_add, pow_one] at hcia
  have hP := h.pos 0
  have h1 : (1 - β) ≠ 0 := by linarith
  -- e : M(bV/y + 1)/P' 0 = (1 - β)⁻¹ * sv
  have key : Mm1 * V * (b * V + y) * (1 - β) * (1 + μ) =
      y * P' 0 * (b * V * (1 - β) - y * μ) := by
    rw [hsv] at e
    have := hV.ne'
    have := hy.ne'
    have := hg.ne'
    field_simp at e
    linear_combination e
  have hcia' : P' 0 * y ≤ Mm1 * (1 + μ) * V := by
    rw [div_le_iff₀ hV] at hcia
    linarith
  have hlhs : 0 < Mm1 * V * (b * V + y) * (1 - β) * (1 + μ) := by
    have : 0 < b * V + y := by nlinarith
    have : 0 < 1 - β := by linarith
    positivity
  rcases le_or_gt (b * V * (1 - β) - y * μ) 0 with hneg | hposv
  · have h3 : y * P' 0 * (b * V * (1 - β) - y * μ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  · have h5 : P' 0 * y * (b * V * (1 - β) - y * μ) ≤
        Mm1 * (1 + μ) * V * (b * V * (1 - β) - y * μ) :=
      mul_le_mul_of_nonneg_right hcia' hposv.le
    have hid : y * P' 0 * (b * V * (1 - β) - y * μ) =
        Mm1 * (1 + μ) * V * (b * V * (1 - β) - y * μ) + Mm1 * (1 + μ) * V * y * (1 - β + μ) := by
      rw [← key]
      ring
    have h7 : 0 < Mm1 * (1 + μ) * V * y * (1 - β + μ) := by
      have : 0 < 1 - β + μ := by linarith
      positivity
    have h8 : P' 0 * y * (b * V * (1 - β) - y * μ) = y * P' 0 * (b * V * (1 - β) - y * μ) := by
      ring
    linarith

/-- Cochrane (2023), §19.5.3, p. 451: **the same equilibrium supports either coordination
story.** In a monetary equilibrium with positive nominal rates at every date, the price level is
pinned by money, `P_t = M_tV/y` ("active money"), and at the same time by the debt valuation
equation, `P_t = (B_{t−1} + M_{t−1})/Σ_j β^j(s_{t+j} + (1 − Q_{t+j})y/V)` ("active fiscal"),
whenever `B_{t−1} + M_{t−1} > 0`. -/
theorem coordination (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V) (h : MonetaryEq β y V P Bin Min s)
    (hQ : ∀ t, bondPrice β P t < 1) (t : ℕ) (hBM : 0 < Bin t + Min t)
    (hs : Summable fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V)) :
    P t = Min (t + 1) * V / y ∧
      P t = (Bin t + Min t) /
        ∑' j, β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
  refine ⟨?_, ?_⟩
  · have := monetary_fact2 h hV (hQ t)
    have := hy.ne'
    field_simp
    linarith
  · rw [← monetary_valuation hβ hV h t hs]
    have := (h.pos t).ne'
    have := hBM.ne'
    field_simp

end PF

end Cochrane.Monetarism.CashInAdvance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, "Money in
continuous time", pp. 635–641, and Online Appendix A1, §1.6, pp. 567–569.

Deterministic paths `ℝ → ℝ` with `HasDerivAt`; present values are improper integrals over
`(t, ∞)` (`MeasureTheory.integral` on `Set.Ioi t` with `IntegrableOn`); transversality conditions
are explicit limits.

## Contents

* **Infrastructure**: forward integration in "iff" form (TVC ⇔ present value), the discount
  factor `Λ_t = e^{−∫_0^t r}` (`Λ' = −rΛ`), the nominal discount factor `Λ/P` (`(Λ/P)' = −iΛ/P`).
* **A1 §1.6, (1.31)–(1.37)** (restated from the Cochrane Generality project, Chapter 3 §3.6.4):
  money creation vs interest saving, the money TVC, ex-post discounting with `W` and `W^m`.
* **A4 p. 635, (4.5)**: the present-value budget with consumption, by integration plus TVC.
* **(4.1)–(4.4)**: the intertemporal and intratemporal first-order conditions, derived by
  differentiating the marginal-utility condition along the path (chain rule through `u_c(c, m)`).
* **CES utility (p. 636–637)**: special cases, exact derivatives `u_c`, `u_m`, `u_cc`, `u_cm`
  (`HasDerivAt`), (4.7), the elasticities.
* **CES limits (E20)**: `θ → 1` holds only for the normalised aggregator (the printed one diverges);
  `θ → ∞` with fixed `α` gives `min(c, m)` and `m/c → 1`; the printed `min(c, αm)`, `M/P = c/α`
  needs the coefficient `α^{−θ}`; and `M/P = c/α` means `V = α`, not `α = 1/V`.
* **(4.8)–(4.10)**, the interest cost `(m/c)(i − i^m) = α^ξ(i − i^m)^{1−ξ} → 0` iff `ξ < 1`.
* **IS curve with money (4.11)–(4.15), E21**: the exact equation
  `ẋ + (σ − ξ)(m/c)/(1 + A)·d(i − i^m)/dt = σ(i − π − δ)`, its first-order form at the steady state,
  the dropped `−δσ`, and the inconsistency of (4.15) with the discrete version of (4.13).
* **Hamiltonian (4.16)–(4.17)**: the constraint from `dM = (y − c − s)P dt`, the money-demand
  consequence `v'/u' = −µ̇/µ + δ + Ṗ/P = i`, and the TVC.
-/

namespace Cochrane.Monetarism.ContinuousTime

open Filter Topology MeasureTheory

/-! ## Forward integration -/

/-- Cochrane (2023), A1 (1.28), p. 566 (restated from the Cochrane Generality project): if
`G' = g` on `[t, ∞)` and `g` is integrable on `(t, ∞)`, then `G_T → G_t + ∫_t^∞ g`. -/
theorem tendsto_of_hasDerivAt {G g : ℝ → ℝ} {t : ℝ}
    (hG : ∀ τ, t ≤ τ → HasDerivAt G (g τ) τ) (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto G atTop (𝓝 (G t + ∫ τ in Set.Ioi t, g τ)) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id).const_add (G t)
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hT' : t ≤ id T := hT
  have hint : IntervalIntegrable g volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT').2 (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hG x (by rw [Set.uIcc_of_le hT] at hx; exact hx.1)) hint
  simp only [id]
  rw [hftc]
  ring

/-- Cochrane (2023), A1 (1.33)–(1.34), p. 567 (restated from the Cochrane Generality project):
**forward integration, iff form.** If `G' = −h` on `[t, ∞)` and `h` is integrable on `(t, ∞)`,
then `G_T → 0` iff `G_t = ∫_t^∞ h`. -/
theorem forward_iff {G h : ℝ → ℝ} {t : ℝ} (hG : ∀ τ, t ≤ τ → HasDerivAt G (-h τ) τ)
    (hh : IntegrableOn h (Set.Ioi t)) :
    Tendsto G atTop (𝓝 0) ↔ G t = ∫ τ in Set.Ioi t, h τ := by
  have hlim := tendsto_of_hasDerivAt (g := fun τ => -h τ) hG hh.neg
  rw [integral_neg] at hlim
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro he
    have : G t + -∫ τ in Set.Ioi t, h τ = 0 := by rw [he]; ring
    rwa [this] at hlim

/-- Cochrane (2023), A1 p. 567 (restated from the Cochrane Generality project): pulling the
constant `1/Λ_t` out of the present-value integral. -/
theorem integral_ratio_eq {Λ f : ℝ → ℝ} (t : ℝ) :
    ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ = (Λ t)⁻¹ * ∫ τ in Set.Ioi t, Λ τ * f τ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), A1 (1.33), p. 567 (restated from the Cochrane Generality project):
converting `N_tX = ∫_t^∞ NPf` (with `Λ = NP`) into `X/P_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
theorem real_form_iff {N P f : ℝ → ℝ} {X t : ℝ} (hN : 0 < N t) (hP : 0 < P t) :
    N t * X = ∫ τ in Set.Ioi t, N τ * P τ * f τ ↔
      X / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * f τ := by
  have h := integral_ratio_eq (Λ := fun τ => N τ * P τ) (f := f) t
  rw [h]
  have hNP : 0 < N t * P t := mul_pos hN hP
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hP.ne'] at e
    rw [e]
    field_simp

/-! ## Discount factors -/

/-- Cochrane (2023), A4 p. 635: **the discount factor `Λ_t = e^{−∫_0^t r_s ds}`** satisfies
`Λ' = −rΛ` when the real rate `r` is continuous. -/
theorem hasDerivAt_discount {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun u => Real.exp (-∫ s in (0 : ℝ)..u, r s))
      (-r t * Real.exp (-∫ s in (0 : ℝ)..t, r s)) t := by
  have h := (hr.integral_hasStrictDerivAt 0 t).hasDerivAt
  exact (HasDerivAt.exp (HasDerivAt.neg h)).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- Cochrane (2023), A4 p. 635 (`r_t = i_t − dP_t/P_t`): if `Λ' = −(i − Ṗ/P)Λ` and `P` is
differentiable and nonzero, the nominal discount factor obeys `(Λ/P)' = −i(Λ/P)`. -/
theorem hasDerivAt_nominal_discount {Λ P : ℝ → ℝ} {i dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i - dP / P τ) * Λ τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Λ x / P x) (-i * (Λ τ / P τ)) τ := by
  convert hΛ.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), A1 (1.35), p. 568 (restated from the Cochrane Generality project): if
`X' = iX` (the nominal value of the short-bond portfolio `X = PW`), then `(1/X)' = −i(1/X)`. -/
theorem inv_nominal_value {X : ℝ → ℝ} {i τ : ℝ} (hX : HasDerivAt X (i * X τ) τ)
    (hXτ : X τ ≠ 0) : HasDerivAt (fun u => 1 / X u) (-i * (1 / X τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hX hXτ
  convert h using 1
  field_simp
  ring

/-- Cochrane (2023), A1 p. 568: with `Λ = NP` and `N = 1/(PW)`, `Λ_τ/Λ_t = W_t/W_τ`. -/
theorem lambda_ratio_eq_W {P W : ℝ → ℝ} {t τ : ℝ} (hPt : P t ≠ 0) (hPτ : P τ ≠ 0)
    (hWt : W t ≠ 0) (hWτ : W τ ≠ 0) :
    (1 / (P τ * W τ) * P τ) / (1 / (P t * W t) * P t) = W t / W τ := by
  field_simp

/-! ## A1 §1.6: the valuation equation with money -/

/-- Cochrane (2023), A1 (1.31), p. 567: the nominal flow `dM = iB + i^mM − Ps − dB` in real
terms, `(B/P)i + (M/P)i^m = s + dB/P + dM/P`. -/
theorem flow_real {B M P s i im dB dM : ℝ} (hP : P ≠ 0)
    (hflow : dM = i * B + im * M - P * s - dB) :
    B / P * i + M / P * im = s + dB / P + dM / P := by
  rw [hflow]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.32), p. 567: with `i^m = 0`, along the flow the discounted debt obeys
`d(NB) = −NP(s + dM/P)` (`N = Λ/P`, `N' = −iN`). -/
theorem printing_hasDerivAt {N B P s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * B u) (-(N τ * P τ * (s τ + dM τ / P τ))) τ :=
  (hN.mul hB).congr_deriv (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), A1 (1.33), p. 567: **seigniorage as money creation.** With `i^m = 0`, the TVC
`Λ_TB_T/P_T → 0` holds iff `B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ`. -/
theorem money_printing_iff {N B P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * B T) atTop (𝓝 0) ↔
      B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ) := by
  rw [forward_iff (fun τ hτ => printing_hasDerivAt (hN τ hτ) (hB τ hτ) (hP τ hτ).ne'
    (hflow τ hτ)) hint]
  exact real_form_iff (f := fun τ => s τ + dM τ / P τ) hNt (hP t le_rfl)

/-- Cochrane (2023), A1 p. 567: with interest on money, along the flow
`d(N(M + B)) = −NP(s + (i − i^m)M/P)`. -/
theorem interest_hasDerivAt {N B M P s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ)
    (hM : HasDerivAt M (dM τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * (M u + B u))
      (-(N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul (HasDerivAt.add hM hB)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 (1.34), p. 567: **seigniorage as interest saving.** The TVC
`Λ_T(M_T + B_T)/P_T → 0` holds iff
`(M_t + B_t)/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ`. -/
theorem money_interest_iff {N B M P s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * (M T + B T)) atTop (𝓝 0) ↔
      (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => interest_hasDerivAt (hN τ hτ) (hB τ hτ) (hM τ hτ)
    (hP τ hτ).ne' (hflow τ hτ)) hint]
  exact real_form_iff (f := fun τ => s τ + (i τ - im τ) * M τ / P τ) hNt (hP t le_rfl)

/-- Cochrane (2023), A1 §1.6, p. 567: with `i^m = 0`, given (1.33), (1.34) holds **iff** the
money transversality condition `Λ_TM_T/P_T → 0` holds. -/
theorem printing_interest_iff_money_tvc {N B M P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint1 : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t))
    (hint2 : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - 0) * M τ / P τ)) (Set.Ioi t))
    (h133 : B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ)) :
    (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - 0) * M τ / P τ) ↔
      Tendsto (fun T => N T * M T) atTop (𝓝 0) := by
  have hBtvc := (money_printing_iff hN hNt hB hP hflow hint1).2 h133
  rw [← money_interest_iff (im := fun _ => 0) hN hNt hB hM hP
    (fun τ hτ => by rw [hflow τ hτ]; ring) hint2]
  constructor
  · intro h
    have := h.sub hBtvc
    rw [sub_zero] at this
    exact this.congr fun T => by ring
  · intro h
    have := h.add hBtvc
    rw [add_zero] at this
    exact this.congr fun T => by ring

/-- Cochrane (2023), A1 (1.36), p. 568: with `i^m = 0` and `(PW)' = iPW`,
`d(B/(PW)) = −(1/W)(s + dM/P)`; the price level itself need not be differentiable. -/
theorem printing_W_hasDerivAt {P W B s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * B u) (-(1 / W τ * (s τ + dM τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul hB).congr_deriv
    (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), A1 (1.36), p. 568: **ex-post discounting, money creation.** The TVC
`B_T/(P_TW_T) → 0` holds iff `B_t/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + dM_τ/P_τ) dτ`. -/
theorem money_printing_W_iff {P W B s i dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < W τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / W τ * (s τ + dM τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * W T) * B T) atTop (𝓝 0) ↔
      B t / P t = ∫ τ in Set.Ioi t, W t / W τ * (s τ + dM τ / P τ) := by
  rw [forward_iff (fun τ hτ => printing_W_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hB τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / W τ) (f := fun τ => s τ + dM τ / P τ) t
  have hc : ∫ τ in Set.Ioi t, W t / W τ * (s τ + dM τ / P τ) =
      ∫ τ in Set.Ioi t, 1 / W τ / (1 / W t) * (s τ + dM τ / P τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 568: with interest on money,
`d((B + M)/(PW)) = −(1/W)(s + (i − i^m)M/P)`. -/
theorem interest_W_hasDerivAt {P W B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * (B u + M u))
      (-(1 / W τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 p. 568: **ex-post discounting, interest saving.** The TVC
`(B_T + M_T)/(P_TW_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` (the rate dated `τ`; the
book prints `(i_t − i^m_t)`, see `printed_index_counterexample`). -/
theorem money_interest_W_iff {P W B M s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < W τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / W τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * W T) * (B T + M T)) atTop (𝓝 0) ↔
      (B t + M t) / P t = ∫ τ in Set.Ioi t, W t / W τ * (s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => interest_W_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hB τ hτ) (hM τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / W τ)
    (f := fun τ => s τ + (i τ - im τ) * M τ / P τ) t
  have hc : ∫ τ in Set.Ioi t, W t / W τ * (s τ + (i τ - im τ) * M τ / P τ) =
      ∫ τ in Set.Ioi t, 1 / W τ / (1 / W t) * (s τ + (i τ - im τ) * M τ / P τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 568 (index typo): the printed integrand `(i_t − i^m_t)M_τ/P_τ` (rate
dated `t`) is wrong. With `P ≡ 1`, `i ≡ 1`, `W_τ = e^τ`, `B ≡ 0`, `M ≡ 1`, `i^m_τ = e^{−τ}` and
`s = i^m` the flow holds, the correctly dated integral equals `(B_0 + M_0)/P_0 = 1`, the printed
one equals `1/2`. -/
theorem printed_index_counterexample :
    let im : ℝ → ℝ := fun τ => Real.exp (-τ)
    (∀ τ : ℝ, (0 : ℝ) = 1 * 0 + im τ * 1 - 1 * im τ - 0) ∧
      ∫ τ in Set.Ioi (0 : ℝ), Real.exp 0 / Real.exp τ * (im τ + (1 - im τ) * 1 / 1) = 1 ∧
      ∫ τ in Set.Ioi (0 : ℝ), Real.exp 0 / Real.exp τ * (im τ + (1 - im 0) * 1 / 1) = 1 / 2 := by
  intro im
  refine ⟨fun τ => by ring, ?_, ?_⟩
  · have : ∀ τ : ℝ, Real.exp 0 / Real.exp τ * (im τ + (1 - im τ) * 1 / 1) =
        Real.exp (-1 * τ) := by
      intro τ
      rw [Real.exp_zero, neg_one_mul, Real.exp_neg]
      ring
    simp_rw [this]
    rw [integral_exp_mul_Ioi (by norm_num) 0]
    norm_num
  · have : ∀ τ : ℝ, Real.exp 0 / Real.exp τ * (im τ + (1 - im 0) * 1 / 1) =
        Real.exp (-2 * τ) := by
      intro τ
      simp only [im, neg_zero, Real.exp_zero, sub_self, zero_mul, zero_div, add_zero]
      rw [show -2 * τ = -τ + -τ by ring, Real.exp_add, Real.exp_neg]
      ring
    simp_rw [this]
    rw [integral_exp_mul_Ioi (by norm_num) 0]
    norm_num

/-- Cochrane (2023), A1 (1.37), p. 569: if `PW^m` grows at the mixed rate
`(Bi + Mi^m)/(B + M)`, then along the flow `d((B + M)/(PW^m)) = −(s/W^m)`. -/
theorem mixed_hasDerivAt {P Wm B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hPτ : P τ ≠ 0) (hWτ : Wm τ ≠ 0) (hBM : B τ + M τ ≠ 0)
    (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * Wm u) * (B u + M u)) (-(1 / Wm τ * s τ)) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 (1.37), p. 569: **valuation with the mixed portfolio return.** The TVC
`(B_T + M_T)/(P_TW^m_T) → 0` holds iff `(B_t + M_t)/P_t = ∫_t^∞ (W^m_t/W^m_τ) s_τ dτ`. -/
theorem money_mixed_iff {P Wm B M s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < Wm τ)
    (hBM : ∀ τ, t ≤ τ → 0 < B τ + M τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / Wm τ * s τ) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * Wm T) * (B T + M T)) atTop (𝓝 0) ↔
      (B t + M t) / P t = ∫ τ in Set.Ioi t, Wm t / Wm τ * s τ := by
  rw [forward_iff (fun τ hτ => mixed_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hBM τ hτ).ne' (hB τ hτ) (hM τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / Wm τ) (f := s) t
  have hc : ∫ τ in Set.Ioi t, Wm t / Wm τ * s τ =
      ∫ τ in Set.Ioi t, 1 / Wm τ / (1 / Wm t) * s τ := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 569: the mixed nominal return `(Bi + Mi^m)/(B + M)` lies below `i`
when `i^m < i`, `M > 0`, `B ≥ 0`. -/
theorem mixed_rate_lt {B M i im : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (him : im < i) :
    (B * i + M * im) / (B + M) < i := by
  have hpos : 0 < B + M := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-! ## A4 p. 635: the present-value budget constraint with consumption -/

/-- Cochrane (2023), A4 p. 635: along the flow `d(B + M) = iB + i^mM + P(y − c − s)` and
`N' = −iN` (`N = Λ/P`), `d(N(B + M)) = −NP(c − y + s + (i − i^m)M/P)`. -/
theorem budget_hasDerivAt {N B M P s c y i im : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ)
    (hBM : HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - c τ - s τ)) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => N u * (B u + M u))
      (-(N τ * P τ * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul hBM).congr_deriv (by field_simp; ring)

/-- Cochrane (2023), A4 p. 635: **the present-value budget constraint is the present-value form of
the flow constraint.** Under `d(B + M) = iB + i^mM + P(y − c − s)` on `[0, ∞)`, `N' = −iN`,
`P > 0` and an integrable integrand, the TVC `Λ_T(B_T + M_T)/P_T → 0` holds iff
`(B_0 + M_0)/P_0 = ∫_0^∞ (Λ_t/Λ_0)(c_t − y_t + s_t + (i_t − i^m_t)M_t/P_t) dt`. -/
theorem pv_budget_iff {N B M P s c y i im : ℝ → ℝ}
    (hN : ∀ τ, 0 ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hN0 : 0 < N 0)
    (hBM : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - c τ - s τ)) τ)
    (hP : ∀ τ, 0 ≤ τ → 0 < P τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ))
      (Set.Ioi 0)) :
    Tendsto (fun T => N T * (B T + M T)) atTop (𝓝 0) ↔
      (B 0 + M 0) / P 0 = ∫ τ in Set.Ioi (0 : ℝ),
        N τ * P τ / (N 0 * P 0) * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => budget_hasDerivAt (hN τ hτ) (hBM τ hτ) (hP τ hτ).ne') hint]
  exact real_form_iff (f := fun τ => c τ - y τ + s τ + (i τ - im τ) * M τ / P τ) hN0
    (hP 0 le_rfl)

/-- Cochrane (2023), (4.5), p. 636: **the equilibrium valuation equation.** With `c = y`, the TVC
holds iff `(B_0 + M_0)/P_0 = ∫_0^∞ (Λ_t/Λ_0)(s_t + (i_t − i^m_t)M_t/P_t) dt`. -/
theorem valuation_4_5 {N B M P s y i im : ℝ → ℝ}
    (hN : ∀ τ, 0 ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hN0 : 0 < N 0)
    (hBM : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - y τ - s τ)) τ)
    (hP : ∀ τ, 0 ≤ τ → 0 < P τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi 0)) :
    Tendsto (fun T => N T * (B T + M T)) atTop (𝓝 0) ↔
      (B 0 + M 0) / P 0 = ∫ τ in Set.Ioi (0 : ℝ),
        N τ * P τ / (N 0 * P 0) * (s τ + (i τ - im τ) * M τ / P τ) := by
  have hint' : IntegrableOn
      (fun τ => N τ * P τ * (y τ - y τ + s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi 0) :=
    hint.congr_fun (fun τ _ => by simp only; ring) measurableSet_Ioi
  rw [pv_budget_iff hN hN0 hBM hP hint']
  have : (fun τ => N τ * P τ / (N 0 * P 0) * (y τ - y τ + s τ + (i τ - im τ) * M τ / P τ)) =
      fun τ => N τ * P τ / (N 0 * P 0) * (s τ + (i τ - im τ) * M τ / P τ) := by
    funext τ
    ring
  rw [this]

/-! ## First-order conditions (4.1)–(4.4) -/

/-- Cochrane (2023), A4 p. 635: `d/dt e^{−δt} = −δe^{−δt}`. -/
theorem hasDerivAt_expDisc (δ t : ℝ) :
    HasDerivAt (fun u => Real.exp (-(δ * u))) (-δ * Real.exp (-(δ * t))) t := by
  have h1 : HasDerivAt (fun u => -(δ * u)) (-δ) t :=
    (HasDerivAt.neg ((hasDerivAt_id' t).const_mul δ)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), A4 p. 635 (chain rule): along a path `(c_t, m_t)` the marginal utility
`u_c(c_t, m_t)` has time derivative `u_cc ċ + u_cm ṁ`, where `u_cc = L(1, 0)`, `u_cm = L(0, 1)` are
the partial derivatives of `u_c` (its Fréchet derivative is `L`). -/
theorem hasDerivAt_marginal_utility {c m : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    {t dc dm : ℝ} (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t)
    (hU : HasFDerivAt Uc L (c t, m t)) :
    HasDerivAt (fun u => Uc (c u, m u)) (dc * L (1, 0) + dm * L (0, 1)) t := by
  have h := hU.comp_hasDerivAt t (hc.prodMk hm)
  have hL : L (dc, dm) = dc * L (1, 0) + dm * L (0, 1) := by
    have : ((dc, dm) : ℝ × ℝ) = dc • ((1 : ℝ), (0 : ℝ)) + dm • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [← hL]
  exact h

/-- Cochrane (2023), (4.1), p. 635: **the intertemporal first-order condition.** If the
consumption first-order condition `e^{−δt}u_c(c_t, m_t) = λΛ_t` holds along the path and
`Λ' = −rΛ`, then `−(c u_cc/u_c)(ċ/c) − (m u_cm/u_c)(ṁ/m) = r − δ`. -/
theorem foc_4_1 {c m Λ : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {δ lam t dc dm r : ℝ}
    (hfoc : ∀ u, Real.exp (-(δ * u)) * Uc (c u, m u) = lam * Λ u)
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hU : HasFDerivAt Uc L (c t, m t))
    (hΛ : HasDerivAt Λ (-r * Λ t) t) (huc : Uc (c t, m t) ≠ 0) (hc0 : c t ≠ 0)
    (hm0 : m t ≠ 0) :
    -(c t * L (1, 0) / Uc (c t, m t)) * (dc / c t) -
        m t * L (0, 1) / Uc (c t, m t) * (dm / m t) = r - δ := by
  have hl : HasDerivAt (fun u => Real.exp (-(δ * u)) * Uc (c u, m u))
      (-δ * Real.exp (-(δ * t)) * Uc (c t, m t) +
        Real.exp (-(δ * t)) * (dc * L (1, 0) + dm * L (0, 1))) t :=
    HasDerivAt.mul (hasDerivAt_expDisc δ t) (hasDerivAt_marginal_utility hc hm hU)
  have heq : (fun u => Real.exp (-(δ * u)) * Uc (c u, m u)) = fun u => lam * Λ u :=
    funext hfoc
  rw [heq] at hl
  have hd := hl.unique (hΛ.const_mul lam)
  have hlam : lam * Λ t = Real.exp (-(δ * t)) * Uc (c t, m t) := (hfoc t).symm
  have he := (Real.exp_pos (-(δ * t))).ne'
  have key : dc * L (1, 0) + dm * L (0, 1) = (δ - r) * Uc (c t, m t) := by
    have h2 : Real.exp (-(δ * t)) * (dc * L (1, 0) + dm * L (0, 1)) =
        Real.exp (-(δ * t)) * ((δ - r) * Uc (c t, m t)) := by
      linear_combination hd - r * hlam
    exact mul_left_cancel₀ he h2
  field_simp
  linear_combination -key

/-- Cochrane (2023), (4.2) and (4.4), p. 636: **money demand.** From the consumption condition
`e^{−δt}u_c = λΛ_t` and the money condition `e^{−δt}u_m/P = λΛ_t(i − i^m)/P`,
`u_m/u_c = i − i^m`. -/
theorem foc_4_2 {e uc um lam Λ P i im : ℝ} (he : e ≠ 0) (huc : uc ≠ 0) (hP : P ≠ 0)
    (h1 : e * uc = lam * Λ) (h2 : e * um * (1 / P) = lam * Λ * (i - im) * (1 / P)) :
    um / uc = i - im := by
  rw [← h1] at h2
  field_simp at h2
  rw [h2]
  field_simp

/-- Cochrane (2023), (4.3), p. 636: **the equilibrium intertemporal condition**: with real rate
`r = i − π` (`π = Ṗ/P`) the condition (4.1) reads
`−(c u_cc/u_c)(ċ/c) − (m u_cm/u_c)(ṁ/m) = −δ + (i − π)`. -/
theorem foc_4_3 {c m Λ : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    {δ lam t dc dm i infl : ℝ}
    (hfoc : ∀ u, Real.exp (-(δ * u)) * Uc (c u, m u) = lam * Λ u)
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hU : HasFDerivAt Uc L (c t, m t))
    (hΛ : HasDerivAt Λ (-(i - infl) * Λ t) t) (huc : Uc (c t, m t) ≠ 0) (hc0 : c t ≠ 0)
    (hm0 : m t ≠ 0) :
    -(c t * L (1, 0) / Uc (c t, m t)) * (dc / c t) -
        m t * L (0, 1) / Uc (c t, m t) * (dm / m t) = -δ + (i - infl) := by
  rw [foc_4_1 hfoc hc hm hU hΛ huc hc0 hm0]
  ring

/-! ## CES utility (pp. 636–637) -/

/-- Cochrane (2023), p. 636: the CES aggregator `c^{1−θ} + αm^{1−θ}`. -/
noncomputable def cesX (α θ c m : ℝ) : ℝ := c ^ (1 - θ) + α * m ^ (1 - θ)

/-- Cochrane (2023), p. 636: CES money-in-utility
`u(c, m) = [c^{1−θ} + αm^{1−θ}]^{(1−γ)/(1−θ)}/(1 − γ)`. -/
noncomputable def cesU (α θ γ c m : ℝ) : ℝ := cesX α θ c m ^ ((1 - γ) / (1 - θ)) / (1 - γ)

/-- Cochrane (2023), p. 636: the aggregator is positive for `c, m > 0`, `α ≥ 0`. -/
theorem cesX_pos {α θ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) : 0 < cesX α θ c m := by
  unfold cesX
  have := Real.rpow_pos_of_pos hc (1 - θ)
  have := Real.rpow_pos_of_pos hm (1 - θ)
  positivity

/-- Cochrane (2023), p. 636: **perfect substitutes**, `θ = 0`: `u = [c + αm]^{1−γ}/(1 − γ)`. -/
theorem ces_perfect_substitutes (α γ c m : ℝ) :
    cesU α 0 γ c m = (c + α * m) ^ (1 - γ) / (1 - γ) := by
  simp [cesU, cesX]

/-- Cochrane (2023), p. 636: **separable case**, `θ = γ ≠ 1`: `u = [c^{1−γ} + αm^{1−γ}]/(1 − γ)`. -/
theorem ces_separable {α γ c m : ℝ} (hγ : γ ≠ 1) :
    cesU α γ γ c m = (c ^ (1 - γ) + α * m ^ (1 - γ)) / (1 - γ) := by
  have : (1 - γ) / (1 - γ) = 1 := div_self (sub_ne_zero.2 (Ne.symm hγ))
  simp only [cesU, cesX, this, Real.rpow_one]

/-- Cochrane (2023), p. 637: `x^{1−θ} = x·x^{−θ}` for `x > 0`. -/
theorem rpow_one_sub {x : ℝ} (hx : 0 < x) (θ : ℝ) : x ^ (1 - θ) = x * x ^ (-θ) := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]

/-- Cochrane (2023), p. 637: **`u_c = [c^{1−θ} + αm^{1−θ}]^{(θ−γ)/(1−θ)} c^{−θ}`** (`c, m > 0`,
`α ≥ 0`, `θ, γ ≠ 1`). -/
theorem hasDerivAt_cesU_c {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1)
    (hγ : γ ≠ 1) :
    HasDerivAt (fun x => cesU α θ γ x m)
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * c ^ (1 - θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have h2 := ((h1.add_const (α * m ^ (1 - θ))).rpow_const (p := (1 - γ) / (1 - θ))
    (Or.inl hX.ne')).div_const (1 - γ)
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have e2 : (1 - γ) / (1 - θ) - 1 = (θ - γ) / (1 - θ) := by field_simp; ring
  rw [e1, e2]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), p. 637: **`u_m = [c^{1−θ} + αm^{1−θ}]^{(θ−γ)/(1−θ)} αm^{−θ}`**. -/
theorem hasDerivAt_cesU_m {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1)
    (hγ : γ ≠ 1) :
    HasDerivAt (fun x => cesU α θ γ c x)
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * (α * m ^ (-θ))) m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * m ^ (1 - θ - 1)) m :=
    Real.hasDerivAt_rpow_const (Or.inl hm.ne')
  have h2 := (((h1.const_mul α).const_add (c ^ (1 - θ))).rpow_const (p := (1 - γ) / (1 - θ))
    (Or.inl hX.ne')).div_const (1 - γ)
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have e2 : (1 - γ) / (1 - θ) - 1 = (θ - γ) / (1 - θ) := by field_simp; ring
  rw [e1, e2]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), (4.7), p. 637: **`u_m/u_c = α(m/c)^{−θ}`**. -/
theorem ces_mrs_4_7 {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    cesX α θ c m ^ ((θ - γ) / (1 - θ)) * (α * m ^ (-θ)) /
        (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) = α * (m / c) ^ (-θ) := by
  have hX := Real.rpow_pos_of_pos (cesX_pos (θ := θ) hα hc hm) ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.div_rpow hm.le hc.le]
  field_simp

/-- Cochrane (2023), p. 637: **`u_cc`**: the derivative of `u_c` in `c` is
`(θ − γ)X^{(θ−γ)/(1−θ) − 1}c^{−θ}c^{−θ} − θX^{(θ−γ)/(1−θ)}c^{−θ−1}` (`X = c^{1−θ} + αm^{1−θ}`). -/
theorem hasDerivAt_ucc {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1) :
    HasDerivAt (fun x => cesX α θ x m ^ ((θ - γ) / (1 - θ)) * x ^ (-θ))
      ((θ - γ) * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * c ^ (-θ) * c ^ (-θ) -
        θ * cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ - 1)) c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * c ^ (1 - θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have h2 := (h1.add_const (α * m ^ (1 - θ))).rpow_const (p := (θ - γ) / (1 - θ))
    (Or.inl hX.ne')
  have h3 : HasDerivAt (fun x : ℝ => x ^ (-θ)) (-θ * c ^ (-θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  refine (h2.mul h3).congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [e1]
  simp only [cesX]
  field_simp
  ring

/-- Cochrane (2023), p. 637: **`u_cm`**: the derivative of `u_c` in `m` is
`(θ − γ)αX^{(θ−γ)/(1−θ) − 1}m^{−θ}c^{−θ}`. -/
theorem hasDerivAt_ucm {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1) :
    HasDerivAt (fun x => cesX α θ c x ^ ((θ - γ) / (1 - θ)) * c ^ (-θ))
      ((θ - γ) * α * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * m ^ (-θ) * c ^ (-θ)) m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * m ^ (1 - θ - 1)) m :=
    Real.hasDerivAt_rpow_const (Or.inl hm.ne')
  have h2 := (((h1.const_mul α).const_add (c ^ (1 - θ))).rpow_const (p := (θ - γ) / (1 - θ))
    (Or.inl hX.ne')).mul_const (c ^ (-θ))
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [e1]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), p. 637: **`u_cc/u_c = (θ − γ)c^{−θ}/(c^{1−θ} + αm^{1−θ}) − θc^{−1}`**. -/
theorem ces_ucc_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    ((θ - γ) * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * c ^ (-θ) * c ^ (-θ) -
        θ * cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ - 1)) /
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) =
      (θ - γ) * c ^ (-θ) / cesX α θ c m - θ / c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hXk := Real.rpow_pos_of_pos hX ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.rpow_sub_one hX.ne', Real.rpow_sub_one hc.ne']
  field_simp

/-- Cochrane (2023), p. 637: **`−c u_cc/u_c = (γc^{1−θ} + θαm^{1−θ})/(c^{1−θ} + αm^{1−θ})`**. -/
theorem ces_ucc_elasticity {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    -(c * ((θ - γ) * c ^ (-θ) / cesX α θ c m - θ / c)) =
      (γ * c ^ (1 - θ) + θ * α * m ^ (1 - θ)) / cesX α θ c m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  rw [rpow_one_sub hc]
  unfold cesX
  rw [rpow_one_sub hc]
  field_simp
  ring

/-- Cochrane (2023), p. 637: in ratio form,
`−c u_cc/u_c = γ(1 + (θ/γ)α(m/c)^{1−θ})/(1 + α(m/c)^{1−θ})` (`γ ≠ 0`). -/
theorem ces_ucc_elasticity_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m)
    (hγ : γ ≠ 0) :
    (γ * c ^ (1 - θ) + θ * α * m ^ (1 - θ)) / cesX α θ c m =
      γ * (1 + θ / γ * (α * (m / c) ^ (1 - θ))) / (1 + α * (m / c) ^ (1 - θ)) := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hcθ := Real.rpow_pos_of_pos hc (1 - θ)
  have hmθ := Real.rpow_pos_of_pos hm (1 - θ)
  rw [Real.div_rpow hm.le hc.le]
  unfold cesX at hX ⊢
  have h1 : 0 < 1 + α * (m ^ (1 - θ) / c ^ (1 - θ)) := by positivity
  field_simp

/-- Cochrane (2023), p. 637: **`m u_cm/u_c = (θ − γ)αm^{1−θ}/(c^{1−θ} + αm^{1−θ})`**. -/
theorem ces_ucm_elasticity {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    m * ((θ - γ) * α * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * m ^ (-θ) * c ^ (-θ)) /
        (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) =
      (θ - γ) * α * m ^ (1 - θ) / cesX α θ c m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hXk := Real.rpow_pos_of_pos hX ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.rpow_sub_one hX.ne', rpow_one_sub hm]
  field_simp

/-- Cochrane (2023), p. 637: in ratio form,
`m u_cm/u_c = (θ − γ)α(m/c)^{1−θ}/(1 + α(m/c)^{1−θ})`. -/
theorem ces_ucm_elasticity_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    (θ - γ) * α * m ^ (1 - θ) / cesX α θ c m =
      (θ - γ) * (α * (m / c) ^ (1 - θ)) / (1 + α * (m / c) ^ (1 - θ)) := by
  have hcθ := Real.rpow_pos_of_pos hc (1 - θ)
  have hmθ := Real.rpow_pos_of_pos hm (1 - θ)
  rw [Real.div_rpow hm.le hc.le]
  unfold cesX
  have h1 : 0 < 1 + α * (m ^ (1 - θ) / c ^ (1 - θ)) := by positivity
  have h2 : 0 < c ^ (1 - θ) + α * m ^ (1 - θ) := by positivity
  field_simp

/-- Cochrane (2023), p. 637 ("or, using (4.7)"): with money demand `α(m/c)^{−θ} = i − i^m`, the
interest cost satisfies `α(m/c)^{1−θ} = (m/c)(i − i^m)`; hence
`m u_cm/u_c = (θ − γ)(m/c)(i − i^m)/(1 + (m/c)(i − i^m))`. -/
theorem ces_A_eq {α θ c m ι : ℝ} (hc : 0 < c) (hm : 0 < m) (h47 : α * (m / c) ^ (-θ) = ι) :
    α * (m / c) ^ (1 - θ) = m / c * ι := by
  rw [rpow_one_sub (div_pos hm hc), ← h47]
  ring

/-! ## CES limits (E20) -/

/-- Cochrane (2023), (4.6), p. 636 (corrected): the **normalised** CES aggregator
`[(c^{1−θ} + αm^{1−θ})/(1 + α)]^{1/(1−θ)}` (a weighted power mean). -/
noncomputable def cesNorm (α θ c m : ℝ) : ℝ := (cesX α θ c m / (1 + α)) ^ (1 / (1 - θ))

/-- Cochrane (2023), (4.6), p. 636: `h ↦ log((c^h + αm^h)/(1 + α))` has derivative
`(log c + α log m)/(1 + α)` at `h = 0` (where it vanishes). -/
theorem log_mean_hasDerivAt {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    HasDerivAt (fun h : ℝ => Real.log ((c ^ h + α * m ^ h) / (1 + α)))
      ((Real.log c + α * Real.log m) / (1 + α)) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => c ^ h) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (Real.hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  have h2 : HasDerivAt (fun h : ℝ => m ^ h) (m ^ (0 : ℝ) * Real.log m) 0 :=
    (Real.hasStrictDerivAt_const_rpow hm 0).hasDerivAt
  have hF : HasDerivAt (fun h : ℝ => (c ^ h + α * m ^ h) / (1 + α))
      ((c ^ (0 : ℝ) * Real.log c + α * (m ^ (0 : ℝ) * Real.log m)) / (1 + α)) 0 :=
    (HasDerivAt.add h1 (h2.const_mul α)).div_const (1 + α)
  have hα1 : (1 + α) ≠ 0 := by positivity
  have hF0 : (c ^ (0 : ℝ) + α * m ^ (0 : ℝ)) / (1 + α) = 1 := by
    simp only [Real.rpow_zero, mul_one]
    field_simp
  have hl := hF.log (by rw [hF0]; norm_num)
  refine hl.congr_deriv ?_
  rw [hF0]
  simp only [Real.rpow_zero]
  field_simp

/-- Cochrane (2023), (4.6), p. 636, **corrected (E20)**: as `θ → 1` the normalised aggregator
converges to the Cobb–Douglas index `c^{1/(1+α)} m^{α/(1+α)}` (`c, m > 0`, `α ≥ 0`). -/
theorem ces_norm_limit {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesNorm α θ c m) (𝓝[≠] 1)
      (𝓝 (c ^ (1 / (1 + α)) * m ^ (α / (1 + α)))) := by
  set D := (Real.log c + α * Real.log m) / (1 + α) with hD
  have hslope := (log_mean_hasDerivAt hα hc hm).tendsto_slope_zero
  have hmap : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
        ((continuous_const.sub continuous_id).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_ne_zero.2 (Ne.symm hθ)
  have hexp := (Real.continuous_exp.tendsto D).comp (hslope.comp hmap)
  have hα1 : (1 + α) ≠ 0 := by positivity
  have hCD : c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) = Real.exp D := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hm, ← Real.exp_add, hD]
    congr 1
    field_simp
  rw [hCD]
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have h1 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hpos : 0 < (c ^ (1 - θ) + α * m ^ (1 - θ)) / (1 + α) := by
    have := Real.rpow_pos_of_pos hc (1 - θ)
    have := Real.rpow_pos_of_pos hm (1 - θ)
    positivity
  have hzero : Real.log ((c ^ (0 : ℝ) + α * m ^ (0 : ℝ)) / (1 + α)) = 0 := by
    simp only [Real.rpow_zero, mul_one]
    rw [div_self hα1, Real.log_one]
  simp only [Function.comp_apply, smul_eq_mul, zero_add, hzero, sub_zero]
  unfold cesNorm cesX
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  field_simp

/-- Cochrane (2023), (4.6), p. 636, **corrected (E20)**: utility built on the normalised
aggregator, `cesNorm^{1−γ}/(1 − γ)`, converges as `θ → 1` to the Cobb–Douglas utility
`[c^{1/(1+α)}m^{α/(1+α)}]^{1−γ}/(1 − γ)`. -/
theorem ces_norm_utility_limit {α γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesNorm α θ c m ^ (1 - γ) / (1 - γ)) (𝓝[≠] 1)
      (𝓝 ((c ^ (1 / (1 + α)) * m ^ (α / (1 + α))) ^ (1 - γ) / (1 - γ))) := by
  have hCD : 0 < c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) := by
    have := Real.rpow_pos_of_pos hc (1 / (1 + α))
    have := Real.rpow_pos_of_pos hm (α / (1 + α))
    positivity
  exact ((Real.continuousAt_rpow_const _ (1 - γ) (Or.inl hCD.ne')).tendsto.comp
    (ces_norm_limit hα hc hm)).div_const _

/-- Cochrane (2023), (4.6), p. 636: the printed (un-normalised) aggregator is
`(1 + α)^{1/(1−θ)}` times the normalised one (same preferences, different cardinal scale). -/
theorem ces_unnorm_eq {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (θ : ℝ) :
    cesX α θ c m ^ (1 / (1 - θ)) = (1 + α) ^ (1 / (1 - θ)) * cesNorm α θ c m := by
  unfold cesNorm
  have hX := cesX_pos (θ := θ) hα hc hm
  have hα1 : (0 : ℝ) < 1 + α := by positivity
  rw [← Real.mul_rpow hα1.le (div_nonneg hX.le hα1.le)]
  congr 1
  field_simp

/-- Cochrane (2023), (4.6), p. 636 (**E20**): with `α > 0` the printed aggregator
`(c^{1−θ} + αm^{1−θ})^{1/(1−θ)}` diverges to `+∞` as `θ → 1⁻`. -/
theorem ces_unnorm_diverges {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) (𝓝[<] 1) atTop := by
  have hmap : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
        ((continuous_const.sub continuous_id).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_pos.2 (Set.mem_Iio.1 hθ)
  have hinv : Tendsto (fun θ : ℝ => 1 / (1 - θ)) (𝓝[<] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hmap
  have hpow := (tendsto_rpow_atTop_of_base_gt_one (1 + α) (by linarith)).comp hinv
  have hnorm := (ces_norm_limit hα.le hc hm).mono_left (nhdsLT_le_nhdsNE 1)
  have hCD : 0 < c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) := by
    have := Real.rpow_pos_of_pos hc (1 / (1 + α))
    have := Real.rpow_pos_of_pos hm (α / (1 + α))
    positivity
  have := hpow.atTop_mul_pos hCD hnorm
  refine this.congr fun θ => ?_
  simp only [Function.comp_apply]
  exact (ces_unnorm_eq hα.le hc hm θ).symm

/-- Cochrane (2023), (4.6), p. 636 (**E20**): the printed aggregator has **no** finite limit as
`θ → 1` (`α > 0`), so the printed Cobb–Douglas limit holds only after normalising by `1 + α`. -/
theorem ces_unnorm_no_limit {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) (Lim : ℝ) :
    ¬ Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) (𝓝[≠] 1) (𝓝 Lim) := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop (ces_unnorm_diverges hα hc hm) Lim
    (h.mono_left (nhdsLT_le_nhdsNE 1))

/-- Cochrane (2023), p. 636 (**E20**): **the monetarist limit with fixed `α > 0` is `min(c, m)`**:
`(c^{1−θ} + αm^{1−θ})^{1/(1−θ)} → min(c, m)` as `θ → ∞`, not `min(c, αm)`. -/
theorem ces_limit_min {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) atTop (𝓝 (min c m)) := by
  set a := min c m with ha_def
  have ha : 0 < a := lt_min hc hm
  set k := min 1 α with hk_def
  have hk : 0 < k := lt_min one_pos hα
  have he : Tendsto (fun θ : ℝ => 1 / (1 - θ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => 1 - θ) atTop atBot :=
      (tendsto_atBot_add_const_left atTop 1
        (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot)).congr
        fun θ => by ring
    refine (tendsto_inv_atBot_zero.comp h1).congr fun θ => ?_
    simp only [Function.comp_apply, one_div]
  have hlim : ∀ b : ℝ, 0 < b → Tendsto (fun θ : ℝ => b ^ (1 / (1 - θ)) * a) atTop (𝓝 a) := by
    intro b hb
    have := ((Real.continuousAt_const_rpow hb.ne' (b := 0)).tendsto.comp he).mul_const a
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (1 + α) (by linarith)) (hlim k hk)
    ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with θ hθ
    have hq : 1 - θ < 0 := by linarith
    have he0 : 1 / (1 - θ) ≤ 0 := (one_div_neg.2 hq).le
    have hc' : c ^ (1 - θ) ≤ a ^ (1 - θ) := Real.rpow_le_rpow_of_nonpos ha (min_le_left c m) hq.le
    have hm' : m ^ (1 - θ) ≤ a ^ (1 - θ) := Real.rpow_le_rpow_of_nonpos ha (min_le_right c m) hq.le
    have hS : cesX α θ c m ≤ (1 + α) * a ^ (1 - θ) := by
      unfold cesX
      nlinarith
    have hX := cesX_pos (θ := θ) hα.le hc hm
    have h := Real.rpow_le_rpow_of_nonpos hX hS he0
    have hval : ((1 + α) * a ^ (1 - θ)) ^ (1 / (1 - θ)) = (1 + α) ^ (1 / (1 - θ)) * a := by
      rw [Real.mul_rpow (by linarith) (Real.rpow_pos_of_pos ha _).le, ← Real.rpow_mul ha.le,
        mul_one_div_cancel hq.ne, Real.rpow_one]
    rw [hval] at h
    exact h
  · filter_upwards [eventually_gt_atTop 1] with θ hθ
    have hq : 1 - θ < 0 := by linarith
    have he0 : 1 / (1 - θ) ≤ 0 := (one_div_neg.2 hq).le
    have haq := Real.rpow_pos_of_pos ha (1 - θ)
    have hS : k * a ^ (1 - θ) ≤ cesX α θ c m := by
      unfold cesX
      have hcq := Real.rpow_pos_of_pos hc (1 - θ)
      have hmq := Real.rpow_pos_of_pos hm (1 - θ)
      rcases le_total c m with hcm | hcm
      · have : a = c := min_eq_left hcm
        rw [this]
        have : k ≤ 1 := min_le_left 1 α
        nlinarith
      · have : a = m := min_eq_right hcm
        rw [this]
        have : k ≤ α := min_le_right 1 α
        nlinarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hS he0
    have hval : (k * a ^ (1 - θ)) ^ (1 / (1 - θ)) = k ^ (1 / (1 - θ)) * a := by
      rw [Real.mul_rpow hk.le haq.le, ← Real.rpow_mul ha.le, mul_one_div_cancel hq.ne,
        Real.rpow_one]
    rw [hval] at h
    exact h

/-- Cochrane (2023), p. 636: the coefficient `α^{−θ}` turns the aggregator into one with
coefficient `α^{−1}` on `(αm)^{1−θ}`: `α^{−θ}m^{1−θ} = α^{−1}(αm)^{1−θ}`. -/
theorem ces_coeff_rewrite {α m : ℝ} (hα : 0 < α) (hm : 0 < m) (θ : ℝ) :
    α ^ (-θ) * m ^ (1 - θ) = α⁻¹ * (α * m) ^ (1 - θ) := by
  rw [Real.mul_rpow hα.le hm.le, rpow_one_sub hα]
  field_simp

/-- Cochrane (2023), p. 636 (**E20**, corrected statement): to obtain the printed limit
`min(c, αm)` the coefficient on `m^{1−θ}` must be `α^{−θ}` (it must vary with `θ`):
`(c^{1−θ} + α^{−θ}m^{1−θ})^{1/(1−θ)} → min(c, αm)` as `θ → ∞`. -/
theorem ces_limit_min_corrected {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ : ℝ => (c ^ (1 - θ) + α ^ (-θ) * m ^ (1 - θ)) ^ (1 / (1 - θ))) atTop
      (𝓝 (min c (α * m))) := by
  have := ces_limit_min (α := α⁻¹) (inv_pos.2 hα) hc (mul_pos hα hm)
  refine this.congr fun θ => ?_
  unfold cesX
  rw [ces_coeff_rewrite hα hm]

/-- Cochrane (2023), (4.8), p. 637 (**E20**): with a fixed `α > 0` and interest differential
`i − i^m > 0`, money demand `m/c = α^{1/θ}(i − i^m)^{−1/θ}` tends to `1` as `θ → ∞`: the limit is
`M/P = c` (velocity one), not the printed `M/P = c/α`. -/
theorem demand_limit_fixed {α ι : ℝ} (hα : 0 < α) (hι : 0 < ι) :
    Tendsto (fun θ : ℝ => α ^ (1 / θ) * ι ^ (-(1 / θ))) atTop (𝓝 1) := by
  have h0 : Tendsto (fun θ : ℝ => 1 / θ) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have h0' : Tendsto (fun θ : ℝ => -(1 / θ)) atTop (𝓝 0) := by simpa using h0.neg
  have h1 := (Real.continuousAt_const_rpow hα.ne' (b := 0)).tendsto.comp h0
  have h2 := (Real.continuousAt_const_rpow hι.ne' (b := 0)).tendsto.comp h0'
  simpa using h1.mul h2

/-- Cochrane (2023), (4.7), p. 637, with the corrected coefficient `α^{−θ}` (**E20**): money
demand `α^{−θ}(m/c)^{−θ} = i − i^m` gives `m/c = α^{−1}(i − i^m)^{−1/θ}` (`θ > 0`). -/
theorem demand_corrected {α ι r θ : ℝ} (hα : 0 < α) (hr : 0 < r) (hθ : 0 < θ)
    (h : α ^ (-θ) * r ^ (-θ) = ι) : r = α⁻¹ * ι ^ (-(1 / θ)) := by
  rw [← Real.mul_rpow hα.le hr.le] at h
  have hθ0 := hθ.ne'
  have key : α * r = ι ^ (-(1 / θ)) := by
    rw [← h, ← Real.rpow_mul (by positivity)]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [← key]
  field_simp

/-- Cochrane (2023), p. 636 (**E20**, corrected): with the coefficient `α^{−θ}`, money demand
`α^{−1}(i − i^m)^{−1/θ} → 1/α` as `θ → ∞`, i.e. `M/P = c/α`. -/
theorem demand_corrected_limit {α ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun θ : ℝ => α⁻¹ * ι ^ (-(1 / θ))) atTop (𝓝 α⁻¹) := by
  have h00 : Tendsto (fun θ : ℝ => 1 / θ) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have h0 : Tendsto (fun θ : ℝ => -(1 / θ)) atTop (𝓝 0) := by simpa using h00.neg
  have h2 := (Real.continuousAt_const_rpow hι.ne' (b := 0)).tendsto.comp h0
  simpa using h2.const_mul α⁻¹

/-- Cochrane (2023), p. 636 ("`M_t/P_t = c_t/α`, i.e. `α = 1/V`", **E20**): with the quantity
equation `MV = Pc`, money demand `M/P = c/α` means velocity `V = α`. -/
theorem velocity_of_demand {α c M P V : ℝ} (hα : 0 < α) (hP : P ≠ 0) (hM : M ≠ 0)
    (hq : M * V = P * c) (hd : M / P = c / α) : V = α := by
  rw [div_eq_div_iff hP hα.ne'] at hd
  have : M * V = M * α := by rw [hq]; linarith
  exact mul_left_cancel₀ hM this

/-- Cochrane (2023), p. 636 (**E20**): given `V = α` (`velocity_of_demand`), the printed
`α = 1/V` holds only for `α = 1`. -/
theorem alpha_eq_inv_V_iff {α V : ℝ} (hα : 0 < α) (hV : V = α) : α = 1 / V ↔ α = 1 := by
  subst hV
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-! ## Money demand (4.8)–(4.10) and the interest cost -/

/-- Cochrane (2023), (4.7)–(4.8), pp. 637–638: for `θ > 0`, `α, i − i^m, m/c > 0`,
`α(m/c)^{−θ} = i − i^m` iff `m/c = (1/α)^{−ξ}(i − i^m)^{−ξ}` with `ξ = 1/θ`. -/
theorem demand_4_8 {α ι r θ : ℝ} (hα : 0 < α) (hι : 0 < ι) (hr : 0 < r) (hθ : 0 < θ) :
    α * r ^ (-θ) = ι ↔ r = (1 / α) ^ (-(1 / θ)) * ι ^ (-(1 / θ)) := by
  have hθ0 := hθ.ne'
  have hinv : ∀ x : ℝ, 0 < x → (x ^ (-θ)) ^ (-(1 / θ)) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hinv' : ∀ x : ℝ, 0 < x → (x ^ (-(1 / θ))) ^ (-θ) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le]
    have : -(1 / θ) * -θ = 1 := by field_simp
    rw [this, Real.rpow_one]
  constructor
  · intro h
    have h1 : r ^ (-θ) = ι / α := by rw [← h]; field_simp
    have h2 := congrArg (fun x : ℝ => x ^ (-(1 / θ))) h1
    rw [hinv r hr, Real.div_rpow hι.le hα.le] at h2
    rw [h2, Real.div_rpow zero_le_one hα.le, Real.one_rpow]
    field_simp
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_pos_of_pos (by positivity) _).le
      (Real.rpow_pos_of_pos hι _).le, hinv' _ (by positivity), hinv' _ hι]
    field_simp

/-- Cochrane (2023), (4.9)–(4.10), p. 638: if `m_t/c_t = Kι_t^{−ξ}` and the steady state obeys
`m/c = Kι^{−ξ}` (`K > 0`, `ι_t, ι > 0`), then `m_t/c_t = (m/c)(ι_t/ι)^{−ξ}`, eliminating `α`. -/
theorem demand_4_10 {K ξ ιt ι rt rs : ℝ} (hι : 0 < ι) (hιt : 0 < ιt)
    (ht : rt = K * ιt ^ (-ξ)) (hs : rs = K * ι ^ (-ξ)) : rt = rs * (ιt / ι) ^ (-ξ) := by
  rw [ht, hs, Real.div_rpow hιt.le hι.le]
  have := (Real.rpow_pos_of_pos hι (-ξ)).ne'
  field_simp

/-- Cochrane (2023), p. 638: **the interest cost of holding money**: along (4.8),
`(m/c)(i − i^m) = α^ξ(i − i^m)^{1−ξ}`. -/
theorem interest_cost_formula {α ξ ι : ℝ} (hι : 0 < ι) :
    α ^ ξ * ι ^ (-ξ) * ι = α ^ ξ * ι ^ (1 - ξ) := by
  rw [rpow_one_sub hι]
  ring

/-- Cochrane (2023), p. 638: the interest cost `α^ξ(i − i^m)^{1−ξ}` (`α > 0`) tends to zero as
`i − i^m → 0⁺` **iff** `ξ < 1` (the book states the "if" direction). -/
theorem interest_cost_tendsto_iff {α ξ : ℝ} (hα : 0 < α) :
    Tendsto (fun ι : ℝ => α ^ ξ * ι ^ (1 - ξ)) (𝓝[>] 0) (𝓝 0) ↔ ξ < 1 := by
  constructor
  · intro h
    by_contra hξ
    push Not at hξ
    have hαξ := Real.rpow_pos_of_pos hα ξ
    have hev : ∀ᶠ ι in 𝓝[>] (0 : ℝ), α ^ ξ ≤ α ^ ξ * ι ^ (1 - ξ) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ι hι
      have : 1 ≤ ι ^ (1 - ξ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hι.1 hι.2.le (by linarith)
      nlinarith
    have := ge_of_tendsto h hev
    linarith
  · intro hξ
    have hc := (Real.continuousAt_rpow_const 0 (1 - ξ) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul (α ^ ξ)

/-! ## The IS curve with money (4.11)–(4.15), E21 -/

/-- Cochrane (2023), (4.11), pp. 638–639 ("prettier"): with `A = α(m/c)^{1−θ}`,
`γ(1 + (θ/γ)A)/(1 + A)·ĉ − (θ − γ)(A/(1 + A))·m̂ = γĉ + (θ − γ)(A/(1 + A))(ĉ − m̂)`. -/
theorem is_prettier {γ θ A ch mh : ℝ} (hγ : γ ≠ 0) (hA : 1 + A ≠ 0) :
    γ * (1 + θ / γ * A) / (1 + A) * ch - (θ - γ) * (A / (1 + A)) * mh =
      γ * ch + (θ - γ) * (A / (1 + A)) * (ch - mh) := by
  field_simp
  ring

/-- Cochrane (2023), (4.12), p. 639: dividing (4.11) by `γ` (`σ = 1/γ`, `ξ = 1/θ`):
`ĉ + ((σ − ξ)/ξ)(A/(1 + A))(ĉ − m̂) = −δσ + σ(i − π)`. -/
theorem is_4_12 {γ θ A ch mh δ i infl : ℝ} (hγ : γ ≠ 0) (hθ : θ ≠ 0) (hA : 1 + A ≠ 0)
    (h411 : γ * (1 + θ / γ * A) / (1 + A) * ch - (θ - γ) * (A / (1 + A)) * mh =
      -δ + (i - infl)) :
    ch + (1 / γ - 1 / θ) / (1 / θ) * (A / (1 + A)) * (ch - mh) =
      -δ * (1 / γ) + 1 / γ * (i - infl) := by
  rw [is_prettier hγ hA] at h411
  have key : ch + (1 / γ - 1 / θ) / (1 / θ) * (A / (1 + A)) * (ch - mh) -
      (-δ * (1 / γ) + 1 / γ * (i - infl)) =
      1 / γ * (γ * ch + (θ - γ) * (A / (1 + A)) * (ch - mh) - (-δ + (i - infl))) := by
    field_simp
  rw [h411, sub_self, mul_zero] at key
  linarith

/-- Cochrane (2023), p. 639 (differentiating the money-demand curve): along
`m_t/c_t = Kι_t^{−ξ}` (`ι = i − i^m`) with differentiable positive paths,
`ċ/c − ṁ/m = ξ ι̇/ι`. -/
theorem demand_log_deriv {m c ι : ℝ → ℝ} {K ξ t dm dc dι : ℝ}
    (hdem : ∀ u, m u / c u = K * ι u ^ (-ξ)) (hm : HasDerivAt m dm t) (hc : HasDerivAt c dc t)
    (hι : HasDerivAt ι dι t) (hm0 : 0 < m t) (hc0 : 0 < c t) (hι0 : 0 < ι t) :
    dc / c t - dm / m t = ξ * (dι / ι t) := by
  have h1 : HasDerivAt (fun u => m u / c u) ((dm * c t - m t * dc) / c t ^ 2) t :=
    hm.div hc hc0.ne'
  have h2 : HasDerivAt (fun u => K * ι u ^ (-ξ)) (K * (dι * (-ξ) * ι t ^ (-ξ - 1))) t :=
    (hι.rpow_const (Or.inl hι0.ne')).const_mul K
  have heq : (fun u => m u / c u) = fun u => K * ι u ^ (-ξ) := funext hdem
  rw [heq] at h1
  have hd := h1.unique h2
  have hK : m t / c t = K * ι t ^ (-ξ) := hdem t
  rw [Real.rpow_sub_one hι0.ne'] at hd
  have hr : K * (dι * -ξ * (ι t ^ (-ξ) / ι t)) = m t / c t * (dι * -ξ / ι t) := by
    rw [hK]
    ring
  rw [hr] at hd
  have hm1 := hm0.ne'
  have hc1 := hc0.ne'
  have hι1 := hι0.ne'
  have key : dc / c t - dm / m t - ξ * (dι / ι t) =
      -(c t / m t) * ((dm * c t - m t * dc) / c t ^ 2 - m t / c t * (dι * -ξ / ι t)) := by
    field_simp
    ring
  rw [hd, sub_self, mul_zero] at key
  linarith

/-- Cochrane (2023), p. 639, `x = log c`: `ẋ = ċ/c`. -/
theorem log_consumption_deriv {c : ℝ → ℝ} {t dc : ℝ} (hc : HasDerivAt c dc t) (hc0 : 0 < c t) :
    HasDerivAt (fun u => Real.log (c u)) (dc / c t) t :=
  hc.log hc0.ne'

/-- Cochrane (2023), p. 639, **the exact IS curve with money (E21)**: from (4.12), the
money-demand relation `ĉ − m̂ = ξι̇/ι` and `A = (m/c)ι`,
`ĉ + (σ − ξ)((m/c)/(1 + A))ι̇ = σ(i − π − δ)`; the book's last display and (4.13) drop `−δσ`. -/
theorem is_exact {σ ξ ch mh ι dι mc A δ i infl : ℝ} (hξ : ξ ≠ 0) (hι : ι ≠ 0)
    (hA : 1 + A ≠ 0) (hAdef : A = mc * ι)
    (h412 : ch + (σ - ξ) / ξ * (A / (1 + A)) * (ch - mh) = -δ * σ + σ * (i - infl))
    (hdem : ch - mh = ξ * (dι / ι)) :
    ch + (σ - ξ) * (mc / (1 + A)) * dι = σ * (i - infl - δ) := by
  rw [hdem] at h412
  have key : ch + (σ - ξ) * (mc / (1 + A)) * dι - σ * (i - infl - δ) =
      ch + (σ - ξ) / ξ * (A / (1 + A)) * (ξ * (dι / ι)) - (-δ * σ + σ * (i - infl)) := by
    rw [hAdef] at hA ⊢
    field_simp
    ring
  rw [h412, sub_self] at key
  linarith

/-- Cochrane (2023), (4.11)–(4.13), pp. 638–639: **the IS curve with money, exact form**,
assembled: from (4.11) (i.e. (4.3) with the CES elasticities `ces_ucc_elasticity_ratio`,
`ces_ucm_elasticity_ratio`) and the money-demand derivative,
`ĉ + (σ − ξ)((m/c)/(1 + (m/c)(i − i^m)))·d(i − i^m)/dt = σ(i − π − δ)` with `σ = 1/γ`,
`ξ = 1/θ`. -/
theorem is_curve_exact {γ θ ch mh mc ι dι δ i infl : ℝ} (hγ : γ ≠ 0) (hθ : θ ≠ 0)
    (hι : ι ≠ 0) (hA : 1 + mc * ι ≠ 0)
    (h411 : γ * (1 + θ / γ * (mc * ι)) / (1 + mc * ι) * ch -
      (θ - γ) * (mc * ι / (1 + mc * ι)) * mh = -δ + (i - infl))
    (hdem : ch - mh = 1 / θ * (dι / ι)) :
    ch + (1 / γ - 1 / θ) * (mc / (1 + mc * ι)) * dι = 1 / γ * (i - infl - δ) :=
  is_exact (by positivity) hι hA rfl (is_4_12 hγ hθ hA h411) hdem

/-- Cochrane (2023), (4.13), p. 639 (first-order approximation): for any `K` differentiable at
`ῑ`, the term `K(ι)ι̇` has derivative `(dι, dι̇) ↦ K(ῑ)dι̇` at the steady state `(ῑ, 0)`: to first
order the coefficient on `d(i − i^m)/dt` is its steady-state value
`K(ῑ) = (m/c)/(1 + (m/c)(i − i^m))`. -/
theorem first_order_term {K : ℝ → ℝ} {K' ι0 : ℝ} (hK : HasDerivAt K K' ι0) :
    HasFDerivAt (fun p : ℝ × ℝ => K p.1 * p.2) (K ι0 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (ι0, 0) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => K p.1) (K' • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ι0, 0) := hK.comp_hasFDerivAt (ι0, 0) (hasFDerivAt_fst)
  have h2 := h1.mul (hasFDerivAt_snd (p := ((ι0, 0) : ℝ × ℝ)))
  convert h2 using 1
  ext <;> simp

/-- Cochrane (2023), (4.8), (4.13), p. 639: along money demand, the coefficient
`K(ι) = (m/c)(ι)/(1 + (m/c)(ι)ι)` with `(m/c)(ι) = α^ξι^{−ξ}` is differentiable at every
`ῑ > 0` (`α > 0`), so `first_order_term` applies. -/
theorem coefficient_differentiable {α ξ ι0 : ℝ} (hα : 0 < α) (hι : 0 < ι0) :
    DifferentiableAt ℝ (fun ι => α ^ ξ * ι ^ (-ξ) / (1 + α ^ ξ * ι ^ (-ξ) * ι)) ι0 := by
  have hr : DifferentiableAt ℝ (fun ι : ℝ => ι ^ (-ξ)) ι0 :=
    (Real.hasDerivAt_rpow_const (Or.inl hι.ne')).differentiableAt
  have hden : 1 + α ^ ξ * ι0 ^ (-ξ) * ι0 ≠ 0 := by
    have := Real.rpow_pos_of_pos hα ξ
    have := Real.rpow_pos_of_pos hι (-ξ)
    positivity
  exact (hr.const_mul _).div (((hr.const_mul _).mul differentiableAt_id).const_add 1) hden

/-- Cochrane (2023), (4.13), p. 639 ("approximating that the interest cost is small"): dropping
`1 + A` from the coefficient changes it by `(m/c)A/(1 + A) ∈ [0, (m/c)A]`, first order in the
interest cost `A = (m/c)(i − i^m)`. -/
theorem coefficient_gap {mc A : ℝ} (hmc : 0 ≤ mc) (hA : 0 ≤ A) :
    0 ≤ mc - mc / (1 + A) ∧ mc - mc / (1 + A) ≤ mc * A := by
  have h1 : (0 : ℝ) < 1 + A := by linarith
  have heq : mc - mc / (1 + A) = mc * A / (1 + A) := by field_simp; ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h1]
  nlinarith [mul_nonneg hmc hA]

/-- Cochrane (2023), (4.13), p. 639 (**E21**): at a steady state of the exact IS curve
(`ẋ = 0`, `ι̇ = 0`) the real rate is `i − π = δ`, so the printed (4.13) `ẋ + … = σ(i − π)`, which
would force `i = π`, fails there whenever `σδ ≠ 0`. -/
theorem E21_steady_state {σ ξ mc A i infl δ : ℝ} (hσ : σ ≠ 0) (hδ : δ ≠ 0)
    (hexact : (0 : ℝ) + (σ - ξ) * (mc / (1 + A)) * 0 = σ * (i - infl - δ)) :
    ¬ ((0 : ℝ) + (σ - ξ) * mc * 0 = σ * (i - infl)) := by
  intro hp
  simp only [mul_zero, add_zero] at hexact hp
  have h1 : i - infl - δ = 0 := by
    rcases mul_eq_zero.1 hexact.symm with h | h
    · exact absurd h hσ
    · exact h
  have h2 : i - infl = 0 := by
    rcases mul_eq_zero.1 hp.symm with h | h
    · exact absurd h hσ
    · exact h
  exact hδ (by linarith)

/-- Cochrane (2023), (4.13), p. 639 (**E21**, the repair): measured as deviations from a steady
state with `ī − π̄ = δ`, `σ(i − π − δ) = σ((i − ī) − (π − π̄))`, so (4.13) is correct only for
`i, π` read as deviations. -/
theorem E21_deviations {σ i infl δ ib πb : ℝ} (hss : ib - πb = δ) :
    σ * (i - infl - δ) = σ * ((i - ib) - (infl - πb)) := by
  rw [← hss]
  ring

/-- Cochrane (2023), (4.14), p. 640 (**E21**): in terms of `x = log c` and `m̃ = log m`, (4.12)
reads exactly `ẋ + ((σ − ξ)/ξ)(A/(1 + A))(ẋ − dm̃/dt) = σ(i − π − δ)`; (4.14) replaces
`A/(1 + A)` by `A = (m/c)(i − i^m)` and drops `−δσ`. -/
theorem is_4_14_exact {c m : ℝ → ℝ} {t dc dm dx dmt σ ξ A δ i infl : ℝ}
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hc0 : 0 < c t) (hm0 : 0 < m t)
    (hx : HasDerivAt (fun u => Real.log (c u)) dx t)
    (hmt : HasDerivAt (fun u => Real.log (m u)) dmt t)
    (h412 : dc / c t + (σ - ξ) / ξ * (A / (1 + A)) * (dc / c t - dm / m t) =
      -δ * σ + σ * (i - infl)) :
    dx + (σ - ξ) / ξ * (A / (1 + A)) * (dx - dmt) = σ * (i - infl - δ) := by
  rw [hx.unique (hc.log hc0.ne'), hmt.unique (hm.log hm0.ne'), h412]
  ring

/-- Cochrane (2023), (4.14), p. 640: replacing `A/(1 + A)` by `A` is a second-order change:
`0 ≤ A − A/(1 + A) ≤ A²` for `A ≥ 0`. -/
theorem A_ratio_gap {A : ℝ} (hA : 0 ≤ A) : 0 ≤ A - A / (1 + A) ∧ A - A / (1 + A) ≤ A ^ 2 := by
  have := coefficient_gap (mc := A) hA hA
  rw [sq]
  exact this

/-- Cochrane (2023), pp. 639–640 (**E21**, (4.15)): in the separable case `σ = ξ` the book's
discrete-time version of (4.13) reads `E_tx_{t+1} − x_t = σ(i_t − E_tπ_{t+1})` while (4.15) reads
`E_tx_{t+1} − x_t = σ(i_t − π_t)`; both hold only if `E_tπ_{t+1} = π_t`. So (4.15) should use
`E_tπ_{t+1}`. -/
theorem E21_discrete_inconsistent {σ ξ k k' Ex1 x dι dm i infl Einfl1 : ℝ} (hσξ : σ = ξ)
    (hσ : σ ≠ 0) (h413d : Ex1 - x + (σ - ξ) * k * dι = σ * (i - Einfl1))
    (h415 : Ex1 - x + (σ - ξ) / ξ * k' * ((Ex1 - x) - dm) = σ * (i - infl)) :
    Einfl1 = infl := by
  subst hσξ
  simp only [sub_self, zero_mul, zero_div, add_zero] at h413d h415
  rw [h413d] at h415
  have : σ * (infl - Einfl1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hσ
  · linarith

/-! ## The Hamiltonian approach (4.16)–(4.17) -/

/-- Cochrane (2023), (4.16), p. 640: from `dM = (y − c − s)P dt` and `m = M/P`,
`ṁ = (y − c − s) − mṖ/P`. -/
theorem constraint_4_16 {M P : ℝ → ℝ} {t dP y c s : ℝ}
    (hM : HasDerivAt M ((y - c - s) * P t) t) (hP : HasDerivAt P dP t) (hP0 : P t ≠ 0) :
    HasDerivAt (fun u => M u / P u) ((y - c - s) - M t / P t * (dP / P t)) t :=
  (hM.div hP hP0).congr_deriv (by field_simp)

/-- Cochrane (2023), p. 640: **money demand from the Hamiltonian first-order conditions**
`u'(c) = µ` and `µ̇ − δµ = −v'(m) + µṖ/P`: `v'(m)/u'(c) = −µ̇/µ + δ + Ṗ/P`. -/
theorem hamiltonian_money_demand {up vp μ dμ δ infl : ℝ} (h1 : up = μ)
    (h2 : dμ - δ * μ = -vp + μ * infl) (hμ : μ ≠ 0) :
    vp / up = -dμ / μ + δ + infl := by
  rw [h1]
  field_simp
  linarith

/-- Cochrane (2023), p. 640: with the real rate `r = δ − µ̇/µ` (consumption Euler equation) and
the Fisher relation `i = r + Ṗ/P`, the Hamiltonian money demand is `v'(m)/u'(c) = i`. -/
theorem hamiltonian_eq_i {up vp μ dμ δ infl r i : ℝ} (h1 : up = μ)
    (h2 : dμ - δ * μ = -vp + μ * infl) (hμ : μ ≠ 0) (hr : r = δ - dμ / μ) (hi : i = r + infl) :
    vp / up = i := by
  rw [hamiltonian_money_demand h1 h2 hμ, hi, hr]
  ring

/-- Cochrane (2023), p. 640: with constant consumption the costate `µ = u'(c̄)` is constant, so
`µ̇ = 0` and the real rate is `r = δ − µ̇/µ = δ`. -/
theorem constant_consumption_rate {μ : ℝ → ℝ} {up dμ t δ : ℝ} (hμ : ∀ u, μ u = up)
    (hd : HasDerivAt μ dμ t) : dμ = 0 ∧ δ - dμ / μ t = δ := by
  have hfun : μ = fun _ => up := funext hμ
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const t up)
  refine ⟨h0, ?_⟩
  rw [h0, zero_div, sub_zero]

/-- Cochrane (2023), (4.17), pp. 640–641: with `µ_t = u'(c_t)` the Hamiltonian transversality
condition `e^{−δt}m_tµ_t → 0` is the condition `e^{−δt}u'(c_t)m_t → 0`. -/
theorem tvc_4_17_iff {m μ c up : ℝ → ℝ} {δ : ℝ} (hμ : ∀ t, μ t = up (c t)) :
    Tendsto (fun t => Real.exp (-(δ * t)) * m t * μ t) atTop (𝓝 0) ↔
      Tendsto (fun t => Real.exp (-(δ * t)) * up (c t) * m t) atTop (𝓝 0) := by
  have : (fun t => Real.exp (-(δ * t)) * m t * μ t) =
      fun t => Real.exp (-(δ * t)) * up (c t) * m t := by
    funext t
    rw [hμ t]
    ring
  rw [this]

end Cochrane.Monetarism.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the Monetarism chains

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19 (pp. 433–462) and Online
Appendices A3 (pp. 612–634) and A4 (pp. 635–641). Cross-chain connection theorems: the same book
objects formalised in different modules, in different coordinates or in different models.

## Main results

* **Money in utility, two coordinate systems.** Cochrane's (19.23) map `MoneyInUtility.nextX`
  in `x = Py/M` and the Online Appendix real-balance map `PruningDeflation.ratioMap` in
  `m = M/(Py) = 1/x` are conjugate (`ratioMap_eq_one_div_nextX`); paths of (19.21) in either
  form coincide (`isMPath_iff_isPowerPath`), and both are Woodford's separable map
  (`isMIUPath_iff_isMPath`, through `MoneyTargetingDynamics.miuPath_iff_sepPath`).
* **E13 = E17.** The existence of the inflationary steady state (E13, p. 445), the existence of
  deflationary paths (E17, A3 p. 613) and the existence of a unique `m̄` are the one condition
  `1 + µ > β` (`e13_iff_e17`). Along the deflations the PruningDeflation path is the
  MoneyTargetingDynamics orbit to `x = 0`, with rate `β/(1 + µ)` (`deflation_rate`); the finite
  time explosion of A3 (3.3) is `MoneyTargetingDynamics.power_inflation_exits` read in `m`
  (`explosion_same_path`).
* **The money TVC across MIU and CIA.** The MIU transversality term along a deflation and the
  CIA discounted real money along the deflationary equilibria of p. 454 vanish under the same
  condition `µ < 0` (`deflation_tvc_miu_iff_cia`); the CIA deflations also exist at the boundary
  `1 + µ = β`, where the MIU has none (`cia_boundary_deflation`).
* **Present values.** The `Regimes` valuation equation in `tsum` form is the
  `CashInAdvance.Stochastic.pv_iff_tvc` engine applied to the flow constraint
  (`flow_pv_tsum_iff_tvc`).
* **Optimality.** CIA sufficiency for any concave `u` via `MoneyInUtility.concave_le_tangent`
  (`cia_euler_sufficient_of_concave`, `tree_euler_sufficient_of_concave`); the two finite-tree
  notions of a node-contingent plan coincide (`meas_iff_tAdapted`).
* **Discrete versus continuous first-order conditions.** (19.13)–(19.14) give (19.16) through the
  algebra of (4.2) (`miu_foc_money_demand`); (19.13) is the discrete form of (4.1)
  (`miu_foc_log_growth`); the per-period interest cost `i/(1 + i)` per unit time tends to `i`
  (`interest_cost_continuous_limit`).
* **CES.** The A3 (p. 632) and A4 (p. 636) CES utilities differ by a constant
  (`ces_nonsep_eq_ct`), so their marginal utilities agree (`ces_uc_nonsep_eq_ct`,
  `ces_um_nonsep_eq_ct`); the A4 money demand is the inverse power demand
  (`demand_4_8_eq_power_demand`).
* **Cagan, seigniorage and fiscal selection.** Cagan velocity and revenue are the Seigniorage
  Cagan example (`cagan_steady_revenue`); the fiscally selected Cagan path is the bounded one iff
  money and fiscal policy are coordinated as in NI-7 (`cagan_ni7`); discrete unpleasant-arithmetic
  seigniorage is steady-state revenue (`seig_eq_revenue`); the Regimes and CIA passive surplus
  rules agree (`passiveSurplus_regimes_eq_cia`).
-/

namespace Cochrane.Monetarism.Links

open Filter Topology

/-! ## Money in utility: `x = Py/M` versus `m = M/(Py)` -/

/-- A general lemma: `(1/z)^γ = z^{−γ}` for `z > 0` (the change of coordinates `x = 1/m` of
Cochrane (2023), (19.23), p. 444, and Online Appendix p. 612). -/
theorem one_div_rpow_eq {z γ : ℝ} (hz : 0 < z) : (1 / z) ^ γ = z ^ (-γ) := by
  rw [Real.rpow_neg hz.le, one_div, Real.inv_rpow hz.le]

/-- Cochrane (2023), eq. (19.23), p. 444, and Online Appendix p. 612: the real-balance map
`m ↦ (1+µ)/β (1 − θm^{−γ}) m` is the canonical (19.23) map `nextX` conjugated by `m ↦ 1/m`,
`ratioMap(m) = 1/nextX(1/m)`, with `x̄` the steady state (19.22). -/
theorem ratioMap_eq_one_div_nextX {β μ θ γ m xb : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m)
    (hden : θ * (1 / m) ^ γ ≠ 1) (hss : θ * xb ^ γ = 1 - β / (1 + μ)) :
    PruningDeflation.ratioMap β μ θ γ m = 1 / MoneyInUtility.nextX θ γ xb (1 / m) := by
  have h := (PruningDeflation.eq1923_iff (m' := PruningDeflation.ratioMap β μ θ γ m) hβ hμ hm
    hden hss).mp rfl
  rw [← h, one_div_one_div]

/-- Cochrane (2023), eq. (19.21), p. 444, and Online Appendix p. 612: a path of real balances
`m = M/(Py)` of the Online Appendix (`IsMPath`) is exactly a path `x = 1/m` of (19.21) in
Chapter 19's form (`IsPowerPath`, money growth `1 + µ`). -/
theorem isMPath_iff_isPowerPath {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) :
    PruningDeflation.IsMPath β μ θ γ m ↔
      MoneyInUtility.IsPowerPath β θ γ (1 + μ) (fun t => 1 / m t) := by
  constructor
  · intro h t
    obtain ⟨h0, h1⟩ := h t
    have h0' := (h (t + 1)).1
    refine ⟨one_div_pos.mpr h0, ?_⟩
    have e1 : (1 / m t) / (1 / m (t + 1)) = m (t + 1) / m t := by field_simp
    have e2 : m (t + 1) / m t = (1 + μ) / β * (1 - θ * m t ^ (-γ)) := by
      rw [h1]
      unfold PruningDeflation.ratioMap
      field_simp
    simp only
    rw [one_div_rpow_eq h0, e1, e2]
    field_simp
    ring
  · intro h t
    obtain ⟨h0, h1⟩ := h t
    have hm0 : 0 < m t := one_div_pos.mp h0
    have hm1 : 0 < m (t + 1) := one_div_pos.mp (h (t + 1)).1
    refine ⟨hm0, ?_⟩
    have e1 : (1 / m t) / (1 / m (t + 1)) = m (t + 1) / m t := by field_simp
    simp only at h1
    rw [one_div_rpow_eq hm0, e1] at h1
    unfold PruningDeflation.ratioMap
    rw [h1]
    field_simp
    ring

/-- Cochrane (2023), eq. (19.18), p. 442, with power utility (19.20), p. 443, and Online
Appendix p. 612: with constant output `y`, `u_c(y) = y^{−γ}`, `u_m(z) = θz^{−γ}` and money
growth `1 + µ`, a path of real balances `M/P = y·m` of (19.18) (`MoneyInUtility.IsMIUPath`) is
exactly a path of the Online Appendix map in `m = M/(Py)` (`IsMPath`). The bridge is
Woodford's separable map, `MoneyTargetingDynamics.miuPath_iff_sepPath`. -/
theorem isMIUPath_iff_isMPath {β μ θ γ y : ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hy : 0 < y) (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = (1 + μ) * M t) :
    MoneyInUtility.IsMIUPath β (y ^ (-γ)) (fun z => θ * z ^ (-γ)) M (fun t => y * m t) ↔
      PruningDeflation.IsMPath β μ θ γ m := by
  have hc : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hy _
  rw [MoneyTargetingDynamics.miuPath_iff_sepPath hβ hc hM hg]
  have hcy : y ^ (-γ) * y ≠ 0 := (mul_pos hc hy).ne'
  constructor
  · rintro ⟨hpos, hrec⟩ t
    have hm : 0 < m t := (mul_pos_iff_of_pos_left hy).mp (hpos t)
    refine ⟨hm, ?_⟩
    have h := hrec t
    unfold MoneyTargetingDynamics.sepF at h
    simp only at h
    rw [Real.mul_rpow hy.le hm.le] at h
    unfold PruningDeflation.ratioMap
    exact mul_left_cancel₀ hcy (by linear_combination h)
  · intro h
    refine ⟨fun t => mul_pos hy (h t).1, fun t => ?_⟩
    obtain ⟨hm, h1⟩ := h t
    unfold MoneyTargetingDynamics.sepF
    simp only
    rw [Real.mul_rpow hy.le hm.le, h1]
    unfold PruningDeflation.ratioMap
    ring

/-! ## E13 (p. 445) and E17 (A3 p. 613): one condition `1 + µ > β` -/

/-- Cochrane (2023), pp. 444–445 (survey E13) and Online Appendix p. 613 (survey E17): for
`θ, γ, β > 0` and `1 + µ > 0` the following are each equivalent to `β < 1 + µ`: the inflationary
steady state `x̄ > 0` of (19.22) exists (`MoneyInUtility.e13_corrected`); a deflationary path of
real balances (`m_t → ∞`) exists (`PruningDeflation.deflation_path_exists`,
`no_deflation_of_le_beta`); the steady state `m̄ = 1/x̄` exists and is unique
(`PruningDeflation.steady_exists_unique`). The printed conditions `1 + µ > 1/β` (E13) and
`µ > −δ` (E17) are both this single condition misprinted. -/
theorem e13_iff_e17 {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) :
    ((∃ xb, 0 < xb ∧ θ * xb ^ γ = 1 - β / (1 + μ)) ↔ β < 1 + μ) ∧
      ((∃ m : ℕ → ℝ, PruningDeflation.IsMPath β μ θ γ m ∧ Tendsto m atTop atTop) ↔
        β < 1 + μ) ∧
      ((∃! ms : ℝ, 0 < ms ∧ θ * ms ^ (-γ) = 1 - β / (1 + μ)) ↔ β < 1 + μ) := by
  have h1 := (MoneyInUtility.e13_corrected (β := β) hθ hγ hμ).1
  refine ⟨h1, ⟨fun ⟨m, hp, hT⟩ => ?_, fun h => ?_⟩, ⟨fun ⟨ms, ⟨hms, hss⟩, _⟩ => ?_,
    fun h => PruningDeflation.steady_exists_unique hβ h hθ hγ⟩⟩
  · by_contra hle
    push Not at hle
    have hanti := PruningDeflation.no_deflation_of_le_beta hβ hμ hle hθ hp
    obtain ⟨t, ht⟩ := (hT.eventually (eventually_gt_atTop (m 0))).exists
    linarith [hanti.antitone (Nat.zero_le t)]
  · obtain ⟨ms, ⟨hms, hss⟩, -⟩ := PruningDeflation.steady_exists_unique hβ h hθ hγ
    obtain ⟨m, ⟨hp, -, hT⟩, -⟩ := PruningDeflation.deflation_path_exists hβ hμ hθ hγ hms hss
      (lt_add_one ms)
    exact ⟨m, hp, hT⟩
  · exact h1.mp ⟨1 / ms, one_div_pos.mpr hms, by rw [one_div_rpow_eq hms, hss]⟩

/-- Cochrane (2023), p. 444 ("This steady state is stable … `lim P_{t+1}/P_t = 1/(1 + δ)`") and
Online Appendix p. 612: along a deflationary path of real balances (`m₀ > m̄`) the inverse
`x_t = 1/m_t = P_ty/M_t` follows the canonical (19.23) map with `x̄ = 1/m̄`, converges to the
deflationary steady state `x = 0`, and `x_{t+1}/x_t → β/(1 + µ)`; the rate comes from
`MoneyTargetingDynamics.power_deflation_orbit`. -/
theorem deflation_rate {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : PruningDeflation.IsMPath β μ θ γ m) (h0 : ms < m 0) :
    (∀ t, 1 / m (t + 1) = MoneyInUtility.nextX θ γ (1 / ms) (1 / m t)) ∧
      Tendsto (fun t => 1 / m t) atTop (𝓝 0) ∧
      Tendsto (fun t => (1 / m (t + 1)) / (1 / m t)) atTop (𝓝 (β / (1 + μ))) := by
  have hμ : 0 < 1 + μ := lt_trans hβ hμβ
  have hxb : θ * (1 / ms) ^ γ = 1 - β / (1 + μ) := by rw [one_div_rpow_eq hms, hss]
  have hgrow := PruningDeflation.deflation_growth hβ hμ hθ hγ hms hss hpath h0
  have hm0 : 0 < m 0 := lt_trans hms h0
  have hlt : ∀ t, θ * (1 / m t) ^ γ < 1 := by
    intro t
    have hmt : 0 < m t := (hpath t).1
    have h1 : m t ^ (-γ) ≤ m 0 ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hm0 (hgrow.2 t).1 (by linarith)
    have h2 : m 0 ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms h0 (by linarith)
    have h3 : 0 < β / (1 + μ) := div_pos hβ hμ
    rw [one_div_rpow_eq hmt]
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le, mul_lt_mul_of_pos_left h2 hθ]
  have hrec : ∀ t, 1 / m (t + 1) = MoneyInUtility.nextX θ γ (1 / ms) (1 / m t) := fun t =>
    (PruningDeflation.eq1923_iff hβ hμ (hpath t).1 (hlt t).ne hxb).mp (hpath t).2
  have hK : 0 < 1 - θ * (1 / ms) ^ γ := by rw [hxb]; have := div_pos hβ hμ; linarith
  have horb := MoneyTargetingDynamics.power_deflation_orbit (x := fun t => 1 / m t) hθ hγ
    (one_div_pos.mpr hms) hK hrec (one_div_pos.mpr hm0) (one_div_lt_one_div_of_lt hms h0)
  refine ⟨hrec, horb.2.2.1, ?_⟩
  have e : 1 - θ * (1 / ms) ^ γ = β / (1 + μ) := by rw [hxb]; ring
  rw [← e]
  exact horb.2.2.2

/-- Cochrane (2023), Online Appendix eq. (3.3), p. 619 ("the price level eventually explodes to
infinity in finite time"), and Figure 19.1, p. 444: from `0 < m₀ < m̄` the real-balance orbit
reaches the demonetisation region at a finite date `T`, i.e. `x_T = 1/m_T` has `θx_T^γ ≥ 1`
(`u_m/u_c ≥ 1`, the exit of `MoneyTargetingDynamics.power_inflation_exits`), and before `T` the
orbit `x_t = 1/m_t` is the orbit of the canonical (19.23) map inside its domain `θx^γ < 1`. -/
theorem explosion_same_path {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : 0 < m0)
    (hlt : m0 < ms) :
    ∃ T, 0 < (PruningDeflation.ratioMap β μ θ γ)^[T] m0 ∧
      1 ≤ θ * (1 / (PruningDeflation.ratioMap β μ θ γ)^[T] m0) ^ γ ∧
      ∀ t < T, θ * (1 / (PruningDeflation.ratioMap β μ θ γ)^[t] m0) ^ γ < 1 ∧
        1 / (PruningDeflation.ratioMap β μ θ γ)^[t + 1] m0 =
          MoneyInUtility.nextX θ γ (1 / ms) (1 / (PruningDeflation.ratioMap β μ θ γ)^[t] m0) := by
  set g := PruningDeflation.ratioMap β μ θ γ with hg
  obtain ⟨T, hT, hbefore⟩ := PruningInflation.finite_time_explosion hβ hμ hθ hγ hss hm0 hlt
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hxb : θ * (1 / ms) ^ γ = 1 - β / (1 + μ) := by rw [one_div_rpow_eq hms, hss]
  -- above the demonetisation level the map is positive and `θx^γ < 1`
  have habove : ∀ z, θ ^ (1 / γ) < z → 0 < g z ∧ θ * (1 / z) ^ γ < 1 := by
    intro z hz
    have hz0 : 0 < z := lt_trans hwp hz
    have h1 : z ^ (-γ) < (θ ^ (1 / γ)) ^ (-γ) := Real.rpow_lt_rpow_of_neg hwp hz (by linarith)
    have h2 := PruningInflation.wp_spec hθ hγ
    have h3 : θ * z ^ (-γ) < 1 := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    refine ⟨?_, by rw [one_div_rpow_eq hz0]; exact h3⟩
    rw [hg]
    unfold PruningDeflation.ratioMap
    have : 0 < 1 - θ * z ^ (-γ) := by linarith
    have := div_pos hμ hβ
    positivity
  have hposT : 0 < g^[T] m0 := by
    rcases Nat.eq_zero_or_pos T with rfl | hT0
    · simpa using hm0
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      rw [Function.iterate_succ_apply']
      exact (habove _ (hbefore k (by omega))).1
  refine ⟨T, hposT, ?_, fun t ht => ⟨(habove _ (hbefore t ht)).2, ?_⟩⟩
  · have h := (PruningInflation.explosion_x_form hθ hγ hposT).mp hT
    linarith
  · have hz := hbefore t ht
    rw [Function.iterate_succ_apply']
    exact (PruningDeflation.eq1923_iff hβ hμ (lt_trans hwp hz) (habove _ hz).2.ne hxb).mp rfl

/-! ## The money TVC along deflations: MIU (A3 p. 613) and CIA (p. 454) -/

/-- Cochrane (2023), Online Appendix pp. 612–613 (E17) and p. 454 (`CashInAdvance.PF`): the
transversality condition fails along the money-in-utility deflations exactly when it fails along
the cash-in-advance deflationary equilibria: both vanish iff `µ < 0`, so the MIU TVC term
`β^{T+1}M_T/(P_{T+1}y)` tends to zero iff the CIA discounted real money `β^tM_t/P_t` does. -/
theorem deflation_tvc_miu_iff_cia {β μ θ γ ms Mm1 P0 : ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hμβ : β < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms)
    (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hpath : PruningDeflation.IsMPath β μ θ γ m)
    (h0 : ms < m 0) (hP0 : 0 < P0) (hM : 0 < Mm1) :
    (Tendsto (PruningDeflation.tvcTerm β μ m) atTop (𝓝 0) ↔ μ < 0) ∧
      (Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop (𝓝 0) ↔
        μ < 0) ∧
      (Tendsto (PruningDeflation.tvcTerm β μ m) atTop (𝓝 0) ↔
        Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop
          (𝓝 0)) := by
  have h1 := PruningDeflation.tvc_tendsto_zero_iff hβ hμβ hθ hγ hms hss hpath h0
  have h2 := CashInAdvance.PF.deflation_money_tvc_iff (μ := μ) hβ hP0 hM (lt_trans hβ hμβ)
  exact ⟨h1, h2, h1.trans h2.symm⟩

/-- Cochrane (2023), p. 454 versus pp. 444–445 and A3 p. 613: at the boundary `1 + µ = β` the
cash-in-advance model still has its zero-rate deflationary equilibria (`P_t = β^tP_0`,
`CashInAdvance.PF.deflation_equilibrium`, for `P_0 ≤ M_0V/y`), while the money-in-utility model
has no deflationary path of real balances at all (`e13_iff_e17`): the CIA condition is
`1 + µ ≥ β`, the MIU condition the strict `1 + µ > β`. -/
theorem cia_boundary_deflation {β μ θ γ y V Mm1 P0 A0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hγ : 0 < γ) (hb : 1 + μ = β) (hM : 0 ≤ Mm1) (hP0 : 0 < P0)
    (hcap : P0 * y / V ≤ Mm1 * (1 + μ)) :
    CashInAdvance.PF.MonetaryEq β y V (fun t => β ^ t * P0)
        (fun t => A0 * β ^ t - Mm1 * (1 + μ) ^ t) (fun t => Mm1 * (1 + μ) ^ t)
        (fun _ => A0 * (1 - β) / P0) ∧
      ¬ ∃ m : ℕ → ℝ, PruningDeflation.IsMPath β μ θ γ m ∧ Tendsto m atTop atTop := by
  refine ⟨CashInAdvance.PF.deflation_equilibrium hβ0 hβ1 hb.ge hM hP0 hcap, fun h => ?_⟩
  have := ((e13_iff_e17 hβ0 (by rw [hb]; exact hβ0) hθ hγ).2.1).mp h
  linarith

/-! ## Present values: the Regimes flow constraint and the CIA forward-iteration engine -/

/-- Cochrane (2023), (19.2), p. 434, and (19.28)–(19.30), p. 449: the valuation equation of
`Regimes` (stated there as a limit of partial sums, `Regimes.flow_pv_iff_tvc`) in `tsum` form:
given the flow constraint, bond pricing and adapted debt, and summable discounted flows, the
bond transversality condition holds iff `Λ_tB_{t−1}/P_t = ∑_j E_t[Λ_{t+j}(ΔM/P + s)_{t+j}]`.
This is the `CashInAdvance.Stochastic.pv_iff_tvc` engine applied to `Regimes`' recursion. -/
theorem flow_pv_tsum_iff_tvc {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut)
    {Λ P N i Bm Q s : ℕ → Ω → ℝ} (hBP : Regimes.BondPricing 𝔼 Λ P i)
    (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t) (hBa : 𝔼.Adapted Bm)
    (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hflow : Regimes.Flow Bm N P s Q)
    (t : ℕ) (ω : Ω)
    (hs : Summable fun j =>
      𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j))) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Λ t ω * Bm t ω / P t ω =
        ∑' j, 𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j))) ω := by
  set x : ℕ → Ω → ℝ := fun k => Λ k * Bm k / P k with hx
  set d : ℕ → Ω → ℝ := fun k => Λ k * ((N (k + 1) - N k) / P k + s k) with hd
  have hrec : ∀ k, x k = d k + 𝔼.E k (x (k + 1)) := fun k =>
    Regimes.flow_value_recursion 𝔼 hPO hBP hB hQ hi hP hflow k
  have hxa : 𝔼.Adapted x := fun k => by
    have h1 : x k = Bm k * (Λ k / P k) := by
      funext ω'
      simp only [hx, Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO k _ _ (hBa k), hφ k]
  have hda : ∀ k, 𝔼.E k (d k) = d k := fun k => by
    have h1 : d k = x k - 𝔼.E k (x (k + 1)) := by rw [hrec k]; abel
    rw [h1, map_sub, hxa k, 𝔼.E_E_self]
  exact CashInAdvance.Stochastic.pv_iff_tvc 𝔼 (x := x) (g := d) (fun k => by rw [hrec k]; abel)
    hda t ω hs

/-! ## Optimality: shared concavity and finite-tree machinery -/

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are necessary
and sufficient") with footnote 1, p. 440: the cash-in-advance sufficiency theorem
`CashInAdvance.Euler.euler_sufficient` holds for any concave differentiable `u`, its
supporting-line hypothesis supplied by `MoneyInUtility.concave_le_tangent`. -/
theorem cia_euler_sufficient_of_concave {β W lam : ℝ} {u : ℝ → ℝ} {p c du : ℕ → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hconc : ConcaveOn ℝ Set.univ u)
    (hdu : ∀ τ, HasDerivAt u (du τ) (c τ)) (hfoc : ∀ τ, β ^ τ * du τ = lam * p τ)
    (hadm : CashInAdvance.Euler.Admissible β u p W c) (hbind : ∑' τ, p τ * c τ = W) :
    CashInAdvance.Euler.IsOptimalPlan β u p W c :=
  CashInAdvance.Euler.euler_sufficient hβ hlam
    (fun τ x => MoneyInUtility.concave_le_tangent hconc (hdu τ) x) hfoc hadm hbind

/-- Cochrane (2023), p. 453, under uncertainty (`CashInAdvance.TreeEuler.euler_sufficient`), with
footnote 1, p. 440: for concave differentiable `u` the supporting-line hypothesis holds at every
node (`MoneyInUtility.concave_le_tangent`). -/
theorem tree_euler_sufficient_of_concave {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {β W lam : ℝ} {u : ℝ → ℝ} {Λ c du : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hconc : ConcaveOn ℝ Set.univ u)
    (hdu : ∀ τ ω, HasDerivAt u (du τ ω) (c τ ω)) (hfoc : ∀ τ ω, β ^ τ * du τ ω = lam * Λ τ ω)
    (hadm : CashInAdvance.TreeEuler.Admissible T β u Λ W c)
    (hbind : ∑' τ, CashInAdvance.TreeEuler.pvCost T Λ c τ = W) :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ W c :=
  CashInAdvance.TreeEuler.euler_sufficient T hβ hlam
    (fun τ ω x => MoneyInUtility.concave_le_tangent hconc (hdu τ ω) x) hfoc hadm hbind

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`) and §19.5.1, p. 448: the two finite-tree
notions of a node-contingent plan, `CashInAdvance.TreeEuler.Meas` and
`MoneyInUtility.FootnoteTree.TAdapted`, coincide. -/
theorem meas_iff_tAdapted {Ω : Type*} [Fintype Ω] (T : ExpectationsFiniteTree.FiniteTree Ω)
    (x : ℕ → Ω → ℝ) :
    CashInAdvance.TreeEuler.Meas T x ↔ MoneyInUtility.FootnoteTree.TAdapted T x :=
  ⟨fun h t ω ω' hw => h t ω' ω hw, fun h t ω ω' hw => h t ω' ω hw⟩

/-! ## Discrete (19.13)–(19.16) and continuous-time (4.1)–(4.4) first-order conditions -/

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, give (19.16), p. 441, through the
continuous-time algebra of (4.2)/(4.4), p. 636: at an optimum of the footnote-1 problem
(`MoneyInUtility.foc_1913_1914`), `u_m/u_c = ι_t = i_t/(1 + i_t)`, which is
`ContinuousTime.foc_4_2` with discounting `β^t`, state price `q_t`, `P = 1` and `i^m = 0`. -/
theorem miu_foc_money_demand {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hβ : 0 < β) (hopt : MoneyInUtility.Optimal β u q ι W c m) (hq0 : q 0 = 1)
    (hq1 : 0 < q 1) (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) (t : ℕ)
    (hu0 : uc (c t) (m t) ≠ 0) :
    um (c t) (m t) / uc (c t) (m t) = ι t := by
  obtain ⟨h1, h2⟩ := MoneyInUtility.foc_1913_1914 hopt hq0 hq1 huc hum t
  have h := ContinuousTime.foc_4_2 (pow_pos hβ t).ne' hu0 one_ne_zero h1
    (by rw [h2]; ring : β ^ t * um (c t) (m t) * (1 / 1) =
      uc (c 0) (m 0) * q t * (ι t - 0) * (1 / 1))
  rw [h, sub_zero]

/-- Cochrane (2023), eq. (19.13), p. 440, versus (4.1), p. 635: with `β = e^{−δ}` and state
prices `q_t = Λ_t/Λ_0 = e^{−R_t}` (`R_t` the cumulated real rate), the discrete first-order
condition `βᵗu_c(t) = λq_t` (`MoneyInUtility.foc_1913_1914`, `λ > 0`) says
`log u_c(t+1) − log u_c(t) = δ − (R_{t+1} − R_t)`, the discrete form of (4.1),
`d log u_c/dt = δ − r` (`ContinuousTime.foc_4_1`). -/
theorem miu_foc_log_growth {δ lam : ℝ} {R uct : ℕ → ℝ} (hlam : 0 < lam)
    (h : ∀ t, Real.exp (-δ) ^ t * uct t = lam * Real.exp (-R t)) (t : ℕ) :
    Real.log (uct (t + 1)) - Real.log (uct t) = δ - (R (t + 1) - R t) := by
  have e : ∀ k, uct k = lam * Real.exp (δ * k - R k) := by
    intro k
    have hk := h k
    rw [← Real.exp_nat_mul] at hk
    have hpos := Real.exp_pos (↑k * -δ)
    have e1 : Real.exp (δ * k - R k) = Real.exp (-R k) / Real.exp (↑k * -δ) := by
      rw [← Real.exp_sub]
      ring_nf
    rw [e1, mul_div_assoc', eq_div_iff hpos.ne', ← hk]
    ring
  rw [e (t + 1), e t, Real.log_mul hlam.ne' (Real.exp_pos _).ne',
    Real.log_mul hlam.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  push_cast
  ring

/-- Cochrane (2023), (19.16), p. 441, and (4.2), p. 636 (`i^m = 0`), the continuous-time limit:
with period length `h` and `1 + i_h = e^{ih}`, the per-period interest cost of money
`ι_h = i_h/(1 + i_h) = 1 − e^{−ih}` per unit of time tends to the continuous-time rate `i`, so
the discrete `u_m/u_c = i/(1 + i)` (per period) becomes `u_m/u_c = i` (per unit time). -/
theorem interest_cost_continuous_limit (i : ℝ) :
    Tendsto (fun h => (1 - Real.exp (-(i * h))) / h) (𝓝[>] 0) (𝓝 i) := by
  have h1 : HasDerivAt (fun h : ℝ => -(i * h)) (-(i * 1)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul i).neg
  have hd : HasDerivAt (fun h : ℝ => 1 - Real.exp (-(i * h))) i 0 := by
    convert (h1.exp).const_sub 1 using 1
    simp
  refine (hd.tendsto_slope_zero_right).congr fun h => ?_
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
  ring

/-! ## CES money in utility: Online Appendix A3 (p. 632) and A4 (p. 636) -/

/-- Cochrane (2023), Online Appendix p. 632 versus p. 636: the A3 CES utility
`([c^ρ + θm^ρ]^{(1−γ)/ρ} − 1)/(1 − γ)` is the A4 CES utility
`[c^{1−θ'} + αm^{1−θ'}]^{(1−γ)/(1−θ')}/(1 − γ)` with `α = θ`, `θ' = 1 − ρ`, minus the constant
`1/(1 − γ)`. -/
theorem ces_nonsep_eq_ct (ρ θ γ c m : ℝ) :
    Nonseparable.cesU ρ θ γ c m = ContinuousTime.cesU θ (1 - ρ) γ c m - 1 / (1 - γ) := by
  unfold Nonseparable.cesU ContinuousTime.cesU ContinuousTime.cesX
  rw [sub_sub_cancel]
  ring

/-- Cochrane (2023), pp. 632 and 637: the A3 and A4 formulas for `u_c` agree
(`Nonseparable.ces_uc`, `ContinuousTime.hasDerivAt_cesU_c`, by uniqueness of the derivative). -/
theorem ces_uc_nonsep_eq_ct {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1) =
      ContinuousTime.cesX θ (1 - ρ) c m ^ ((1 - ρ - γ) / (1 - (1 - ρ))) * c ^ (-(1 - ρ)) := by
  have h1 := Nonseparable.ces_uc hρ hγ hθ hc hm
  have h2 := (ContinuousTime.hasDerivAt_cesU_c (α := θ) (θ := 1 - ρ) (γ := γ) hθ.le hc hm
    (by intro h; exact hρ (by linarith)) hγ).sub_const (1 / (1 - γ))
  refine h1.unique ?_
  convert h2 using 1
  funext x
  exact ces_nonsep_eq_ct ρ θ γ x m

/-- Cochrane (2023), pp. 632 and 637: the A3 and A4 formulas for `u_m` agree
(`Nonseparable.ces_um`, `ContinuousTime.hasDerivAt_cesU_m`). -/
theorem ces_um_nonsep_eq_ct {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1)) =
      ContinuousTime.cesX θ (1 - ρ) c m ^ ((1 - ρ - γ) / (1 - (1 - ρ))) *
        (θ * m ^ (-(1 - ρ))) := by
  have h1 := Nonseparable.ces_um hρ hγ hθ hc hm
  have h2 := (ContinuousTime.hasDerivAt_cesU_m (α := θ) (θ := 1 - ρ) (γ := γ) hθ.le hc hm
    (by intro h; exact hρ (by linarith)) hγ).sub_const (1 / (1 - γ))
  refine h1.unique ?_
  convert h2 using 1
  funext x
  exact ces_nonsep_eq_ct ρ θ γ c x

/-- Cochrane (2023), (4.8), p. 638, and (19.16)/(19.20), p. 443: the A4 money demand
`m/c = (1/α)^{−1/θ}(i − i^m)^{−1/θ}` (`ContinuousTime.demand_4_8`) is the inverse power demand
`(ι/α)^{−1/θ}` of `MoneyInUtility.power_demand_iff`. -/
theorem demand_4_8_eq_power_demand {α ι θ : ℝ} (hα : 0 < α) (hι : 0 < ι) :
    (1 / α) ^ (-(1 / θ)) * ι ^ (-(1 / θ)) = (ι / α) ^ (-(1 / θ)) := by
  rw [← Real.mul_rpow (by positivity) hι.le]
  congr 1
  ring

/-! ## Cagan money demand, seigniorage and fiscal selection -/

/-- Cochrane (2023), (19.4)–(19.5), p. 436, and p. 458: along a perfect-foresight Cagan path
with steady inflation `p_{t+1} = p_t + π`, velocity `Py/M = e^{p+y−m}` is `e^{a(r+π)}` (the
Cagan example `V(r + π) = e^{a(r+π)}` of `Seigniorage`), and seigniorage per unit of output
`π·M/(Py)` is `Seigniorage.cagRev a r π`. -/
theorem cagan_steady_revenue {a y r π : ℝ} {m p : ℕ → Unit → ℝ}
    (hC : CaganRE.Cagan perfectForesight a y r m p) (hπ : ∀ t, p (t + 1) () = p t () + π)
    (t : ℕ) :
    Real.exp (p t () + y - m t ()) = Real.exp (a * (r + π)) ∧
      π * Real.exp (m t () - p t () - y) = Seigniorage.cagRev a r π := by
  have h : m t () - p t () - y = -a * (r + p (t + 1) () - p t ()) := hC t ()
  rw [hπ t] at h
  have e1 : p t () + y - m t () = a * (r + π) := by linarith
  have e2 : m t () - p t () - y = -(a * (r + π)) := by linarith
  refine ⟨by rw [e1], ?_⟩
  rw [e2, Real.exp_neg, Seigniorage.cagRev, div_eq_mul_inv]

/-- Cochrane (2023), §19.1, p. 435 (survey NI-7) and pp. 437–438: in the Cagan model with
constant money `m̄`, the fiscally selected price path (`B_{−1}/P_0 = ∑βʲs_j = S`) is the bounded,
monetarist one exactly when monetary and fiscal policy are coordinated in the sense of
`Regimes.double_active_iff`: an active money supply `e^{m̄}` with velocity `e^{ar}` and an
active fiscal policy `(B, S)` have a common price level. -/
theorem cagan_ni7 {a y r mbar B S : ℝ} (ha : 0 < a) (hB : 0 < B) (hS : 0 < S)
    {p : ℕ → Unit → ℝ} (hp : CaganRE.Cagan perfectForesight a y r (fun _ _ => mbar) p)
    (hv : B / Real.exp (p 0 ()) = S) :
    BoundedProc p ↔ ∃ P : ℕ → Unit → ℝ,
      Regimes.MonetaryEqm (fun _ _ => Real.exp mbar) (fun _ _ => Real.exp (a * r))
        (fun _ _ => Real.exp y) P ∧ Regimes.Valuation (fun _ _ => B) (fun _ _ => S) P := by
  rw [CaganRE.fiscal_path_bounded_iff ha hB hS hp hv,
    Regimes.double_active_iff (fun _ _ => hB) (fun _ _ => hS)]
  unfold CaganRE.pbar
  rw [Real.exp_add, Real.exp_sub]
  have hy := Real.exp_pos y
  constructor
  · intro h _ _
    rw [h]
    field_simp
  · intro h
    have := h 0 ()
    field_simp
    linarith

/-- Cochrane (2023), (19.39)–(19.40), p. 456, and p. 458: the discrete seigniorage of
`UnpleasantArithmetic` with gross money growth `1 + n` and constant velocity, scaled by `1 + n`,
is output times the steady-state revenue `(π + g)/V` of `Seigniorage` at `π = n`, `g = 0`. -/
theorem seig_eq_revenue {y V n r : ℝ} (hn : 1 + n ≠ 0) :
    UnpleasantArithmetic.seig y V (1 + n) * (1 + n) =
      y * Seigniorage.revenue (fun _ => V) r 0 n := by
  unfold UnpleasantArithmetic.seig Seigniorage.revenue
  field_simp
  ring

/-- Cochrane (2023), §19.1, p. 435, and p. 453: under perfect foresight with a constant price
level `P_0` and target real debt `B/P_0`, the passive surplus rule of `Regimes`
(`s_t = W_t − βE_tW_{t+1}`) is the cash-in-advance passive surplus `(1 − β)B/P_0`. -/
theorem passiveSurplus_regimes_eq_cia (β B P0 : ℝ) (t : ℕ) :
    Regimes.passiveSurplus perfectForesight β (fun _ _ => B / P0) t =
      fun _ => CashInAdvance.PF.passiveSurplus β B (fun _ => P0) t := by
  funext u
  change B / P0 - β * (B / P0) = (1 - β) * B / P0
  ring

end Cochrane.Monetarism.Links

set_option linter.style.longLine false
#print axioms Cochrane.Monetarism.SchurStable
#print axioms Cochrane.Monetarism.discQ
#print axioms Cochrane.Monetarism.root₁
#print axioms Cochrane.Monetarism.root₂
#print axioms Cochrane.Monetarism.root_sum
#print axioms Cochrane.Monetarism.root_prod
#print axioms Cochrane.Monetarism.root_eq
#print axioms Cochrane.Monetarism.normSq_root_of_neg
#print axioms Cochrane.Monetarism.norm_root_of_nonneg
#print axioms Cochrane.Monetarism.schurStable_iff_roots
#print axioms Cochrane.Monetarism.chSeq
#print axioms Cochrane.Monetarism.convSeq
#print axioms Cochrane.Monetarism.convSeq_rec
#print axioms Cochrane.Monetarism.chSeq_eq_convSeq
#print axioms Cochrane.Monetarism.norm_convSeq_le
#print axioms Cochrane.Monetarism.abs_chSeq_le
#print axioms Cochrane.Monetarism.tendsto_chSeq
#print axioms Cochrane.Monetarism.tr2
#print axioms Cochrane.Monetarism.det2
#print axioms Cochrane.Monetarism.tr2_eq_trace
#print axioms Cochrane.Monetarism.det2_eq_det
#print axioms Cochrane.Monetarism.sq_eq_cayleyHamilton
#print axioms Cochrane.Monetarism.pow_succ_eq
#print axioms Cochrane.Monetarism.abs_pow_entry_le
#print axioms Cochrane.Monetarism.tendsto_pow_entry
#print axioms Cochrane.Monetarism.BoundedSeq
#print axioms Cochrane.Monetarism.homogeneous_iterate
#print axioms Cochrane.Monetarism.abs_mulVec_le
#print axioms Cochrane.Monetarism.homogeneous_eq_zero
#print axioms Cochrane.Monetarism.eq_root_of_eq
#print axioms Cochrane.Monetarism.exists_eigenvector
#print axioms Cochrane.Monetarism.exists_bounded_homogeneous
#print axioms Cochrane.Monetarism.ExpectationSystem
#print axioms Cochrane.Monetarism.ExpectationSystem.mk
#print axioms Cochrane.Monetarism.ExpectationSystem.E
#print axioms Cochrane.Monetarism.ExpectationSystem.const
#print axioms Cochrane.Monetarism.ExpectationSystem.mono
#print axioms Cochrane.Monetarism.ExpectationSystem.tower
#print axioms Cochrane.Monetarism.ExpectationSystem.known
#print axioms Cochrane.Monetarism.perfectForesight
#print axioms Cochrane.Monetarism.BoundedProc
#print axioms Cochrane.Monetarism.BoundedVec
#print axioms Cochrane.Monetarism.ExpectationSystem.Adapted
#print axioms Cochrane.Monetarism.ExpectationSystem.IsAR1
#print axioms Cochrane.Monetarism.ExpectationSystem.E_neg
#print axioms Cochrane.Monetarism.ExpectationSystem.E_smul
#print axioms Cochrane.Monetarism.ExpectationSystem.E_E_self
#print axioms Cochrane.Monetarism.ExpectationSystem.abs_E_le
#print axioms Cochrane.Monetarism.ExpectationSystem.bounded_E
#print axioms Cochrane.Monetarism.ExpectationSystem.ar1_iterate
#print axioms Cochrane.Monetarism.ExpectationSystem.forward_iterate
#print axioms Cochrane.Monetarism.ExpectationSystem.forward_unique
#print axioms Cochrane.Monetarism.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.Monetarism.ExpectationSystem.E_tsum
#print axioms Cochrane.Monetarism.ExpectationSystem.forwardSeries
#print axioms Cochrane.Monetarism.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.Monetarism.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.Monetarism.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.Monetarism.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.Monetarism.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.Monetarism.ExpectationSystem.PullOut
#print axioms Cochrane.Monetarism.ExpectationSystem.Solves
#print axioms Cochrane.Monetarism.ExpectationSystem.AdaptedVec
#print axioms Cochrane.Monetarism.ExpectationSystem.system_iterate
#print axioms Cochrane.Monetarism.ExpectationSystem.system_unique
#print axioms Cochrane.Monetarism.ExpectationSystem.system_not_unique
#print axioms Cochrane.Monetarism.ExpectationSystem.Determinate
#print axioms Cochrane.Monetarism.ExpectationSystem.determinate_iff
#print axioms Cochrane.Monetarism.perfectForesight_pullOut
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.Monetarism.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.Monetarism.ForwardSolution.Solves
#print axioms Cochrane.Monetarism.ForwardSolution.E_of_known
#print axioms Cochrane.Monetarism.ForwardSolution.solves_adapted
#print axioms Cochrane.Monetarism.ForwardSolution.iterate_A15
#print axioms Cochrane.Monetarism.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.Monetarism.ForwardSolution.summable_A16
#print axioms Cochrane.Monetarism.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.Monetarism.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.Monetarism.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.Monetarism.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.Monetarism.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.Monetarism.ForwardSolution.ScalarEq
#print axioms Cochrane.Monetarism.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.Monetarism.ForwardSolution.scalarSol
#print axioms Cochrane.Monetarism.ForwardSolution.scalarSol_apply
#print axioms Cochrane.Monetarism.ForwardSolution.scalarEq_iff
#print axioms Cochrane.Monetarism.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.Monetarism.ForwardSolution.scalar_homog
#print axioms Cochrane.Monetarism.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.Monetarism.ForwardSolution.sunspotFamily
#print axioms Cochrane.Monetarism.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.Monetarism.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.Monetarism.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.Monetarism.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.Monetarism.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.Monetarism.ForwardSolution.homog_solves
#print axioms Cochrane.Monetarism.ForwardSolution.solves_add_homog
#print axioms Cochrane.Monetarism.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.Monetarism.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.Monetarism.ForwardSolution.existsUnique_iff
#print axioms Cochrane.Monetarism.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.Monetarism.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.Monetarism.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.Monetarism.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.Monetarism.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.Monetarism.ForwardSolution.ar1_decay
#print axioms Cochrane.Monetarism.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.Monetarism.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.Monetarism.ForwardSolution.predetermined_restriction
#print axioms Cochrane.Monetarism.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.Monetarism.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.Monetarism.ForwardSolution.summable_geom_mul
#print axioms Cochrane.Monetarism.ForwardSolution.abel_tsum
#print axioms Cochrane.Monetarism.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.Monetarism.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.Monetarism.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.Monetarism.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.Monetarism.ForwardSolution.E_tsum_dom
#print axioms Cochrane.Monetarism.Regimes.QuantityEq
#print axioms Cochrane.Monetarism.Regimes.BondPricing
#print axioms Cochrane.Monetarism.Regimes.partial192
#print axioms Cochrane.Monetarism.Regimes.partial193
#print axioms Cochrane.Monetarism.Regimes.E_next_value
#print axioms Cochrane.Monetarism.Regimes.step_identity
#print axioms Cochrane.Monetarism.Regimes.sum_by_parts
#print axioms Cochrane.Monetarism.Regimes.eq192_iff_eq193
#print axioms Cochrane.Monetarism.Regimes.tail_tendsto_zero_of_book_tvc
#print axioms Cochrane.Monetarism.Regimes.Flow
#print axioms Cochrane.Monetarism.Regimes.flow_value_recursion
#print axioms Cochrane.Monetarism.Regimes.flow_pv_iff_tvc
#print axioms Cochrane.Monetarism.Regimes.flow_eq193_of_tvc
#print axioms Cochrane.Monetarism.Regimes.seigniorage_indep_price
#print axioms Cochrane.Monetarism.Regimes.Valuation
#print axioms Cochrane.Monetarism.Regimes.Pos
#print axioms Cochrane.Monetarism.Regimes.MonetaryEqm
#print axioms Cochrane.Monetarism.Regimes.FiscalEqm
#print axioms Cochrane.Monetarism.Regimes.ni7
#print axioms Cochrane.Monetarism.Regimes.double_passive
#print axioms Cochrane.Monetarism.Regimes.double_active_iff
#print axioms Cochrane.Monetarism.Regimes.passiveSurplus
#print axioms Cochrane.Monetarism.Regimes.passive_surplus_realises
#print axioms Cochrane.Monetarism.Regimes.partial111
#print axioms Cochrane.Monetarism.Regimes.spread_term_eq_zero_iff
#print axioms Cochrane.Monetarism.Regimes.partial111_of_no_spread
#print axioms Cochrane.Monetarism.Regimes.omo_irrelevant
#print axioms Cochrane.Monetarism.Regimes.spread_existsUnique
#print axioms Cochrane.Monetarism.Regimes.omo_equivalence
#print axioms Cochrane.Monetarism.Regimes.elastic_currency
#print axioms Cochrane.Monetarism.Regimes.ftpl_price_ratio
#print axioms Cochrane.Monetarism.Regimes.quantity_price_ratio
#print axioms Cochrane.Monetarism.Regimes.helicopter_fiscal
#print axioms Cochrane.Monetarism.Regimes.helicopter_fiscal_approx
#print axioms Cochrane.Monetarism.Regimes.helicopter_monetarist
#print axioms Cochrane.Monetarism.Regimes.helicopter_cash_share
#print axioms Cochrane.Monetarism.Regimes.helicopter_bond_loss
#print axioms Cochrane.Monetarism.CaganRE.eq194_iff_log
#print axioms Cochrane.Monetarism.CaganRE.MoneyDemand
#print axioms Cochrane.Monetarism.CaganRE.Fisher
#print axioms Cochrane.Monetarism.CaganRE.Cagan
#print axioms Cochrane.Monetarism.CaganRE.md_fisher_iff_cagan
#print axioms Cochrane.Monetarism.CaganRE.theta
#print axioms Cochrane.Monetarism.CaganRE.theta_gt_one
#print axioms Cochrane.Monetarism.CaganRE.theta_inv
#print axioms Cochrane.Monetarism.CaganRE.abs_theta_inv_lt_one
#print axioms Cochrane.Monetarism.CaganRE.cagan_iff_expect
#print axioms Cochrane.Monetarism.CaganRE.forcing
#print axioms Cochrane.Monetarism.CaganRE.cagan_iff_solves
#print axioms Cochrane.Monetarism.CaganRE.forcing_adapted
#print axioms Cochrane.Monetarism.CaganRE.pbar
#print axioms Cochrane.Monetarism.CaganRE.steady_state_iff
#print axioms Cochrane.Monetarism.CaganRE.steady_state_strictMono_r
#print axioms Cochrane.Monetarism.CaganRE.eq197_iff
#print axioms Cochrane.Monetarism.CaganRE.caganFamily
#print axioms Cochrane.Monetarism.CaganRE.caganFamily_closed
#print axioms Cochrane.Monetarism.CaganRE.caganFamily_adapted
#print axioms Cochrane.Monetarism.CaganRE.caganFamily_E_succ
#print axioms Cochrane.Monetarism.CaganRE.caganFamily_solves
#print axioms Cochrane.Monetarism.CaganRE.eq_caganFamily
#print axioms Cochrane.Monetarism.CaganRE.pf_path
#print axioms Cochrane.Monetarism.CaganRE.pf_explodes
#print axioms Cochrane.Monetarism.CaganRE.expected_path
#print axioms Cochrane.Monetarism.CaganRE.expected_explodes
#print axioms Cochrane.Monetarism.CaganRE.bounded_iff_steady
#print axioms Cochrane.Monetarism.CaganRE.pf_solutions_uncountable
#print axioms Cochrane.Monetarism.CaganRE.coinShock_adapted
#print axioms Cochrane.Monetarism.CaganRE.coin_sunspot_solves
#print axioms Cochrane.Monetarism.CaganRE.coin_sunspot_ne_steady
#print axioms Cochrane.Monetarism.CaganRE.eq198_finite
#print axioms Cochrane.Monetarism.CaganRE.eq198
#print axioms Cochrane.Monetarism.CaganRE.eq198_bounded_money
#print axioms Cochrane.Monetarism.CaganRE.limit_zero_iff_bounded
#print axioms Cochrane.Monetarism.CaganRE.bounded_existsUnique
#print axioms Cochrane.Monetarism.CaganRE.fiscal_selects_P0
#print axioms Cochrane.Monetarism.CaganRE.fiscal_path_existsUnique
#print axioms Cochrane.Monetarism.CaganRE.fiscal_path_bounded_iff
#print axioms Cochrane.Monetarism.CaganRE.innov
#print axioms Cochrane.Monetarism.CaganRE.valuation_split
#print axioms Cochrane.Monetarism.CaganRE.stochastic_selection
#print axioms Cochrane.Monetarism.MoneyInUtility.HHFlow
#print axioms Cochrane.Monetarism.MoneyInUtility.hhFlow_iff_flow
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1911_iff_tvc
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1912_of_tvc
#print axioms Cochrane.Monetarism.MoneyInUtility.equilibrium_valuation
#print axioms Cochrane.Monetarism.MoneyInUtility.Feasible
#print axioms Cochrane.Monetarism.MoneyInUtility.Optimal
#print axioms Cochrane.Monetarism.MoneyInUtility.tsum_modify_two
#print axioms Cochrane.Monetarism.MoneyInUtility.perturb_le
#print axioms Cochrane.Monetarism.MoneyInUtility.foc_cc
#print axioms Cochrane.Monetarism.MoneyInUtility.foc_mc
#print axioms Cochrane.Monetarism.MoneyInUtility.foc_1913_1914
#print axioms Cochrane.Monetarism.MoneyInUtility.concave_le_tangent
#print axioms Cochrane.Monetarism.MoneyInUtility.supergradient_of_concave
#print axioms Cochrane.Monetarism.MoneyInUtility.optimal_of_foc
#print axioms Cochrane.Monetarism.MoneyInUtility.convenience_identity
#print axioms Cochrane.Monetarism.MoneyInUtility.value_recursion
#print axioms Cochrane.Monetarism.MoneyInUtility.value_of_money_iterated
#print axioms Cochrane.Monetarism.MoneyInUtility.value_of_money_limit
#print axioms Cochrane.Monetarism.MoneyInUtility.lm_unique
#print axioms Cochrane.Monetarism.MoneyInUtility.lm_exists
#print axioms Cochrane.Monetarism.MoneyInUtility.price_ratio_eq
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1918_iff
#print axioms Cochrane.Monetarism.MoneyInUtility.IsMIUPath
#print axioms Cochrane.Monetarism.MoneyInUtility.steady_state_path_iff
#print axioms Cochrane.Monetarism.MoneyInUtility.steady_state_inflation
#print axioms Cochrane.Monetarism.MoneyInUtility.steady_state_existsUnique
#print axioms Cochrane.Monetarism.MoneyInUtility.zero_rate_iff
#print axioms Cochrane.Monetarism.MoneyInUtility.deflation_approx
#print axioms Cochrane.Monetarism.MoneyInUtility.satiation_absorbing
#print axioms Cochrane.Monetarism.MoneyInUtility.limit_rate_zero
#print axioms Cochrane.Monetarism.MoneyInUtility.money_demand_correspondence
#print axioms Cochrane.Monetarism.MoneyInUtility.hasDerivAt_power
#print axioms Cochrane.Monetarism.MoneyInUtility.power_um_ratio
#print axioms Cochrane.Monetarism.MoneyInUtility.power_demand_iff
#print axioms Cochrane.Monetarism.MoneyInUtility.power_money_demand
#print axioms Cochrane.Monetarism.MoneyInUtility.IsPowerPath
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1922
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1922_exact
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1922_partial_delta
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1922_partial_mu
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1922_approx
#print axioms Cochrane.Monetarism.MoneyInUtility.calib_unit
#print axioms Cochrane.Monetarism.MoneyInUtility.calib_ten
#print axioms Cochrane.Monetarism.MoneyInUtility.calib_ten_gamma_one
#print axioms Cochrane.Monetarism.MoneyInUtility.calib_ten_gamma_two
#print axioms Cochrane.Monetarism.MoneyInUtility.calib_interest_cost
#print axioms Cochrane.Monetarism.MoneyInUtility.nextX
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1923_iff
#print axioms Cochrane.Monetarism.MoneyInUtility.inflation_eq1923
#print axioms Cochrane.Monetarism.MoneyInUtility.xbar191
#print axioms Cochrane.Monetarism.MoneyInUtility.fig191_steady
#print axioms Cochrane.Monetarism.MoneyInUtility.fig191_xbar_bounds
#print axioms Cochrane.Monetarism.MoneyInUtility.nextX_hasDerivAt
#print axioms Cochrane.Monetarism.MoneyInUtility.slope_gt_one
#print axioms Cochrane.Monetarism.MoneyInUtility.fig191_slope
#print axioms Cochrane.Monetarism.MoneyInUtility.fig191_pole
#print axioms Cochrane.Monetarism.MoneyInUtility.deflation_limit
#print axioms Cochrane.Monetarism.MoneyInUtility.e13_corrected
#print axioms Cochrane.Monetarism.MoneyInUtility.e13_printed_fails
#print axioms Cochrane.Monetarism.MoneyInUtility.fiscal_determines_path
#print axioms Cochrane.Monetarism.MoneyInUtility.known_mul
#print axioms Cochrane.Monetarism.MoneyInUtility.known_inv
#print axioms Cochrane.Monetarism.MoneyInUtility.known_div
#print axioms Cochrane.Monetarism.MoneyInUtility.known_prod
#print axioms Cochrane.Monetarism.MoneyInUtility.functionsKnown_of_fintype
#print axioms Cochrane.Monetarism.MoneyInUtility.known_div_of_fintype
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1911_iff_tvc_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.eq1912_of_tvc_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.value_of_money_iterated_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.value_of_money_limit_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.TAdapted
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.dateCost
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.dateUtil
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.TFeasible
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.TOptimal
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.cell
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.cell_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.sum_perturb_cell
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.perturb_adapted
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.tperturb_le
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.tree_foc_cc
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.tree_foc_mc
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.tree_foc_1913_1914
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.lambda_const
#print axioms Cochrane.Monetarism.MoneyInUtility.FootnoteTree.tree_optimal_of_foc
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.orbit_monotone_of_le
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.orbit_antitone_of_ge
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.fixed_of_tendsto
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.monotone_orbit_atTop_or_fixed
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.antitone_orbit_atBot_or_fixed
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sign_near_of_deriv_pos
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.Ffun
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.Gfun
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.eq48_iff_fisher
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepF
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepMap
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.eq48_sep_iff
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepF_pos
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepF_strictMonoOn
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepF_tendsto_zero
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepMap_tendsto_zero
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sepMap_fixed_iff
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_exists_steady_state
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_single_crossing
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.IsSepPath
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_path_exists_unique
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_inflation_path
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_deflation_path
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.IsPath48
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.Satiation
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.satiated_path
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.money_tvc_violated
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.sep_deflation_violates_tvc
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.money_contraction_continuum
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.miuPath_iff_sepPath
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.nextX_fixed
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.nextX_pos
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.nextX_lt_iff
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.power_steady_repelling
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.fig191_repelling
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.power_deflation_orbit
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.power_deflation_inflation
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.power_inflation_exits
#print axioms Cochrane.Monetarism.MoneyTargetingDynamics.e13_no_deflation_attractor
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.seig
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.seigniorage_eq
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.inflation_eq_growth
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.seig_strictMono
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.seig_lt_bound
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.any_timing
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.seigniorage_pv
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.unpleasant_shift
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.unpleasant_tradeoff
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.unpleasant_money_growth
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.nominal_debt_price
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.nominal_debt_price_anti
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.disinflation_windfall
#print axioms Cochrane.Monetarism.UnpleasantArithmetic.real_debt_no_price
#print axioms Cochrane.Monetarism.Seigniorage.steady_seigniorage
#print axioms Cochrane.Monetarism.Seigniorage.revenue
#print axioms Cochrane.Monetarism.Seigniorage.revenue_hasDerivAt
#print axioms Cochrane.Monetarism.Seigniorage.revenue_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.money_demand_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.revenue_foc_iff
#print axioms Cochrane.Monetarism.Seigniorage.e16_unit_iff
#print axioms Cochrane.Monetarism.Seigniorage.revenue_deriv_pos_iff
#print axioms Cochrane.Monetarism.Seigniorage.laffer_decreasing
#print axioms Cochrane.Monetarism.Seigniorage.cagRev
#print axioms Cochrane.Monetarism.Seigniorage.cagRev_eq
#print axioms Cochrane.Monetarism.Seigniorage.cagan_velocity_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.cagan_revenue_le
#print axioms Cochrane.Monetarism.Seigniorage.cagan_revenue_lt
#print axioms Cochrane.Monetarism.Seigniorage.cagan_example_two
#print axioms Cochrane.Monetarism.Seigniorage.cagan_revenue_tendsto_zero
#print axioms Cochrane.Monetarism.Seigniorage.cagRev_hasDerivAt
#print axioms Cochrane.Monetarism.Seigniorage.cagRev_strictMonoOn
#print axioms Cochrane.Monetarism.Seigniorage.cagRev_strictAntiOn
#print axioms Cochrane.Monetarism.Seigniorage.no_steady_state_above_max
#print axioms Cochrane.Monetarism.Seigniorage.two_steady_states
#print axioms Cochrane.Monetarism.Seigniorage.v2_price_level
#print axioms Cochrane.Monetarism.Seigniorage.v2_cagan
#print axioms Cochrane.Monetarism.Seigniorage.btCost
#print axioms Cochrane.Monetarism.Seigniorage.bt_min
#print axioms Cochrane.Monetarism.Seigniorage.bt_interest_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.bt_income_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.bt_lm_slope
#print axioms Cochrane.Monetarism.Seigniorage.cia_income_elasticity
#print axioms Cochrane.Monetarism.Seigniorage.e23_real_loss
#print axioms Cochrane.Monetarism.PruningDeflation.umPow
#print axioms Cochrane.Monetarism.PruningDeflation.ucPow
#print axioms Cochrane.Monetarism.PruningDeflation.um_div_uc_pow
#print axioms Cochrane.Monetarism.PruningDeflation.foc_power_iff
#print axioms Cochrane.Monetarism.PruningDeflation.ratioMap
#print axioms Cochrane.Monetarism.PruningDeflation.ratio_of_foc
#print axioms Cochrane.Monetarism.PruningDeflation.growth_factor_eq
#print axioms Cochrane.Monetarism.PruningDeflation.ratio_strictAntiOn
#print axioms Cochrane.Monetarism.PruningDeflation.ratio_tendsto
#print axioms Cochrane.Monetarism.PruningDeflation.eq1923_iff
#print axioms Cochrane.Monetarism.PruningDeflation.fixed_iff
#print axioms Cochrane.Monetarism.PruningDeflation.steady_exists_unique
#print axioms Cochrane.Monetarism.PruningDeflation.IsMPath
#print axioms Cochrane.Monetarism.PruningDeflation.deflation_growth
#print axioms Cochrane.Monetarism.PruningDeflation.deflation_tendsto_atTop
#print axioms Cochrane.Monetarism.PruningDeflation.deflation_path_exists
#print axioms Cochrane.Monetarism.PruningDeflation.tvcTerm
#print axioms Cochrane.Monetarism.PruningDeflation.tvcTerm_eq
#print axioms Cochrane.Monetarism.PruningDeflation.exp_le_one_sub
#print axioms Cochrane.Monetarism.PruningDeflation.scaled_succ
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_tendsto_zero_of_neg
#print axioms Cochrane.Monetarism.PruningDeflation.scaled_lower_bound
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_not_tendsto_zero
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_tendsto_zero_iff
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_mu_zero
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_mu_pos
#print axioms Cochrane.Monetarism.PruningDeflation.deflation_continuum
#print axioms Cochrane.Monetarism.PruningDeflation.no_deflation_of_le_beta
#print axioms Cochrane.Monetarism.PruningDeflation.survival_threshold
#print axioms Cochrane.Monetarism.PruningDeflation.survival_counterexample
#print axioms Cochrane.Monetarism.PruningDeflation.deflation_at_satiation
#print axioms Cochrane.Monetarism.PruningDeflation.flow_nodebt_iff
#print axioms Cochrane.Monetarism.PruningDeflation.price_geometric
#print axioms Cochrane.Monetarism.PruningDeflation.discounted_surplus
#print axioms Cochrane.Monetarism.PruningDeflation.pv_finite
#print axioms Cochrane.Monetarism.PruningDeflation.pv_finite_telescoped
#print axioms Cochrane.Monetarism.PruningDeflation.final_money_eq
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_term_growth
#print axioms Cochrane.Monetarism.PruningDeflation.pv_surplus_tendsto_bot
#print axioms Cochrane.Monetarism.PruningDeflation.no_eqm_positive_growth
#print axioms Cochrane.Monetarism.PruningDeflation.passive_requires_negative_growth
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_iff_money_vanishes
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_limit
#print axioms Cochrane.Monetarism.PruningDeflation.tvc_iff_pv
#print axioms Cochrane.Monetarism.PruningDeflation.price_level_determined
#print axioms Cochrane.Monetarism.PruningDeflation.no_price_level_of_nonpos_pv
#print axioms Cochrane.Monetarism.PruningDeflation.omo_total_debt
#print axioms Cochrane.Monetarism.PruningDeflation.omo_real_debt_const
#print axioms Cochrane.Monetarism.PruningDeflation.omo_bonds
#print axioms Cochrane.Monetarism.PruningDeflation.omo_bonds_eventually_neg
#print axioms Cochrane.Monetarism.PruningDeflation.omo_explode
#print axioms Cochrane.Monetarism.PruningDeflation.omo_tvc
#print axioms Cochrane.Monetarism.PruningDeflation.omo_pv
#print axioms Cochrane.Monetarism.PruningDeflation.last_period_foc
#print axioms Cochrane.Monetarism.PruningDeflation.last_period_foc_sufficient
#print axioms Cochrane.Monetarism.PruningDeflation.last_period_power_demand
#print axioms Cochrane.Monetarism.PruningDeflation.separable_money_demand_rises
#print axioms Cochrane.Monetarism.PruningDeflation.iterated_budget
#print axioms Cochrane.Monetarism.PruningInflation.wp_spec
#print axioms Cochrane.Monetarism.PruningInflation.ratioMap_wp
#print axioms Cochrane.Monetarism.PruningInflation.le_one_iff
#print axioms Cochrane.Monetarism.PruningInflation.ratioMap_neg
#print axioms Cochrane.Monetarism.PruningInflation.ratioMap_strictMonoOn
#print axioms Cochrane.Monetarism.PruningInflation.ratioMap_continuousOn
#print axioms Cochrane.Monetarism.PruningInflation.wp_lt_ms
#print axioms Cochrane.Monetarism.PruningInflation.ratioMap_lt_self
#print axioms Cochrane.Monetarism.PruningInflation.self_le_ratioMap
#print axioms Cochrane.Monetarism.PruningInflation.fixed_unique
#print axioms Cochrane.Monetarism.PruningInflation.finite_time_explosion
#print axioms Cochrane.Monetarism.PruningInflation.explosion_x_form
#print axioms Cochrane.Monetarism.PruningInflation.no_positive_path_below
#print axioms Cochrane.Monetarism.PruningInflation.IsEqm
#print axioms Cochrane.Monetarism.PruningInflation.eqm_of_value
#print axioms Cochrane.Monetarism.PruningInflation.terminal_balance
#print axioms Cochrane.Monetarism.PruningInflation.terminal_price
#print axioms Cochrane.Monetarism.PruningInflation.IsBackward
#print axioms Cochrane.Monetarism.PruningInflation.backward_exists
#print axioms Cochrane.Monetarism.PruningInflation.backward_unique
#print axioms Cochrane.Monetarism.PruningInflation.backward_strictMono
#print axioms Cochrane.Monetarism.PruningInflation.backward_tendsto
#print axioms Cochrane.Monetarism.PruningInflation.eqm_demonetises
#print axioms Cochrane.Monetarism.PruningInflation.eqm_of_backward
#print axioms Cochrane.Monetarism.PruningInflation.eqm_of_ge
#print axioms Cochrane.Monetarism.PruningInflation.eqm_initial_iff
#print axioms Cochrane.Monetarism.PruningInflation.inflationary_initial_countable
#print axioms Cochrane.Monetarism.PruningInflation.not_eqm_of_lt_wp
#print axioms Cochrane.Monetarism.PruningInflation.not_eqm_between
#print axioms Cochrane.Monetarism.PruningInflation.mdDisc
#print axioms Cochrane.Monetarism.PruningInflation.mdCont
#print axioms Cochrane.Monetarism.PruningInflation.md_discrete_iff
#print axioms Cochrane.Monetarism.PruningInflation.md_discrete_tendsto
#print axioms Cochrane.Monetarism.PruningInflation.md_cont_tendsto
#print axioms Cochrane.Monetarism.PruningInflation.md_ratio
#print axioms Cochrane.Monetarism.PruningInflation.md_ratio_tendsto
#print axioms Cochrane.Monetarism.PruningInflation.modU
#print axioms Cochrane.Monetarism.PruningInflation.modU_hasDerivAt_c
#print axioms Cochrane.Monetarism.PruningInflation.modU_hasDerivAt_m
#print axioms Cochrane.Monetarism.PruningInflation.modified_foc_iff
#print axioms Cochrane.Monetarism.PruningInflation.newMap
#print axioms Cochrane.Monetarism.PruningInflation.new_map_of_foc
#print axioms Cochrane.Monetarism.PruningInflation.new_fixed_iff
#print axioms Cochrane.Monetarism.PruningInflation.new_x_form
#print axioms Cochrane.Monetarism.PruningInflation.new_map_pos
#print axioms Cochrane.Monetarism.PruningInflation.new_inflation_tendsto_zero
#print axioms Cochrane.Monetarism.PruningInflation.new_inflation_rate_tendsto
#print axioms Cochrane.Monetarism.PruningInflation.new_inflationary_continuum
#print axioms Cochrane.Monetarism.ObstfeldRogoff.eq36_iff_value
#print axioms Cochrane.Monetarism.ObstfeldRogoff.eq36_real
#print axioms Cochrane.Monetarism.ObstfeldRogoff.steady_iff
#print axioms Cochrane.Monetarism.ObstfeldRogoff.terminal_iff
#print axioms Cochrane.Monetarism.ObstfeldRogoff.redemption_foc_zero
#print axioms Cochrane.Monetarism.ObstfeldRogoff.redemption_raises_balance
#print axioms Cochrane.Monetarism.ObstfeldRogoff.figVp
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_vp_eq_rpow
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_vp_strictAnti
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_steady
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_terminal
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_back
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_back_spec
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_eps0
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_eps_half
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_numbers
#print axioms Cochrane.Monetarism.ObstfeldRogoff.e18_caption_decreasing
#print axioms Cochrane.Monetarism.ObstfeldRogoff.e18_no_steady_state
#print axioms Cochrane.Monetarism.ObstfeldRogoff.e18_correct_v
#print axioms Cochrane.Monetarism.ObstfeldRogoff.IsORPath
#print axioms Cochrane.Monetarism.ObstfeldRogoff.or_balance_step
#print axioms Cochrane.Monetarism.ObstfeldRogoff.or_no_hyperinflation
#print axioms Cochrane.Monetarism.ObstfeldRogoff.two_way_steady
#print axioms Cochrane.Monetarism.ObstfeldRogoff.two_way_needs_sale
#print axioms Cochrane.Monetarism.ObstfeldRogoff.cochrane_sum_identity
#print axioms Cochrane.Monetarism.ObstfeldRogoff.cochrane_household_optimal
#print axioms Cochrane.Monetarism.ObstfeldRogoff.cochrane_violates_or_bound
#print axioms Cochrane.Monetarism.ObstfeldRogoff.standing_redemption_no_optimum
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_v_supergradient
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_cochrane_path
#print axioms Cochrane.Monetarism.ObstfeldRogoff.fig32_cochrane_optimal
#print axioms Cochrane.Monetarism.Nonseparable.foc38_iff
#print axioms Cochrane.Monetarism.Nonseparable.sdf_log_hasFDerivAt
#print axioms Cochrane.Monetarism.Nonseparable.rf_log_hasFDerivAt
#print axioms Cochrane.Monetarism.Nonseparable.sdf_level_hasDerivAt
#print axioms Cochrane.Monetarism.Nonseparable.ct_footnote
#print axioms Cochrane.Monetarism.Nonseparable.obs_uc
#print axioms Cochrane.Monetarism.Nonseparable.obs_um
#print axioms Cochrane.Monetarism.Nonseparable.obs_printed_typo
#print axioms Cochrane.Monetarism.Nonseparable.obs_mrs
#print axioms Cochrane.Monetarism.Nonseparable.obs_uc_ratio
#print axioms Cochrane.Monetarism.Nonseparable.obs_foc
#print axioms Cochrane.Monetarism.Nonseparable.obs_map_iff
#print axioms Cochrane.Monetarism.Nonseparable.obsRatio
#print axioms Cochrane.Monetarism.Nonseparable.obsMap
#print axioms Cochrane.Monetarism.Nonseparable.obs_steady_iff
#print axioms Cochrane.Monetarism.Nonseparable.obs_relative
#print axioms Cochrane.Monetarism.Nonseparable.obs_ratio_hasDerivAt
#print axioms Cochrane.Monetarism.Nonseparable.e19_printed_coefficient
#print axioms Cochrane.Monetarism.Nonseparable.obs_map_hasDerivAt
#print axioms Cochrane.Monetarism.Nonseparable.obs_cuts_from_above_iff
#print axioms Cochrane.Monetarism.Nonseparable.obs_stable_iff
#print axioms Cochrane.Monetarism.Nonseparable.e19_counterexample
#print axioms Cochrane.Monetarism.Nonseparable.local_contraction
#print axioms Cochrane.Monetarism.Nonseparable.local_repulsion
#print axioms Cochrane.Monetarism.Nonseparable.obs_multiple_stable
#print axioms Cochrane.Monetarism.Nonseparable.obs_locally_unique
#print axioms Cochrane.Monetarism.Nonseparable.cesU
#print axioms Cochrane.Monetarism.Nonseparable.ces_uc
#print axioms Cochrane.Monetarism.Nonseparable.ces_um
#print axioms Cochrane.Monetarism.Nonseparable.ces_uc_form
#print axioms Cochrane.Monetarism.Nonseparable.ces_sdf
#print axioms Cochrane.Monetarism.Nonseparable.ces_sdf_const
#print axioms Cochrane.Monetarism.Nonseparable.ces_mrs
#print axioms Cochrane.Monetarism.Nonseparable.ces_money_demand_iff
#print axioms Cochrane.Monetarism.Nonseparable.ces_income_elasticity
#print axioms Cochrane.Monetarism.Nonseparable.ces_interest_elasticity
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.E_ratio
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.telescope
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.pv_iff_tvc
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gB
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gBM
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.interest_cost_eq
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.flow_step_B
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.flow_step_BM
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gB_adapted
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gBM_adapted
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.pv_19_29
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.pv_19_30
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.normalise_iff
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.tvc_B_iff_money_tvc
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.pv_19_29_needs_money_tvc
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gB_market_clearing
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.gBM_market_clearing
#print axioms Cochrane.Monetarism.CashInAdvance.Stochastic.bond_price_19_32
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.portfolioCost
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.IsOptimalMoney
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.portfolioCost_eq
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.optimal_iff
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.optimal_iff_of_lt_one
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.optimal_iff_of_eq_one
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.unbounded_of_one_lt
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.no_optimum_of_one_lt
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.overnight_feasible_iff
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.overnight_min_clear
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.fact2_19_33
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.fact_19_37
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.L_shaped_demand
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.Q_lt_one_iff
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.Q_le_one_iff
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.E14_one_le_Q_iff
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.binding_cost_wedge
#print axioms Cochrane.Monetarism.CashInAdvance.MoneyDemand.wedge_eq_one_iff
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.lifetimeU
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.Admissible
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.IsOptimalPlan
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.isOptimalPlan_iff_optimal
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.euler_necessary
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.euler_sufficient
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.sdf_19_31
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.sdf_const_endowment
#print axioms Cochrane.Monetarism.CashInAdvance.Euler.sdf_wedge
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.Meas
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.expU
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.pvCost
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.Admissible
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.IsOptimal
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.cia_min_V1
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.euler_necessary
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.euler_sufficient
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.sdf_19_31
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.sdf_eq
#print axioms Cochrane.Monetarism.CashInAdvance.TreeEuler.bond_price_from_optimality
#print axioms Cochrane.Monetarism.CashInAdvance.PF.bondPrice
#print axioms Cochrane.Monetarism.CashInAdvance.PF.bondPrice_eq_beta_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.bondPrice_const
#print axioms Cochrane.Monetarism.CashInAdvance.PF.bondPrice_deflation
#print axioms Cochrane.Monetarism.CashInAdvance.PF.bondPrice_growth
#print axioms Cochrane.Monetarism.CashInAdvance.PF.pv_of_rec
#print axioms Cochrane.Monetarism.CashInAdvance.PF.rec_of_flow
#print axioms Cochrane.Monetarism.CashInAdvance.PF.valuation_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.mk
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.pos
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.money_nonneg
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.rate_nonneg
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.no_money
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.flow
#print axioms Cochrane.Monetarism.CashInAdvance.PF.FrictionlessEq.tvc
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.mk
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.pos
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.cia
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.rate_nonneg
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.binds
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.flow
#print axioms Cochrane.Monetarism.CashInAdvance.PF.MonetaryEq.tvc
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_money_optimal_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_money_optimal
#print axioms Cochrane.Monetarism.CashInAdvance.PF.monetary_money_optimal
#print axioms Cochrane.Monetarism.CashInAdvance.PF.monetary_fact2
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_seigniorage_zero
#print axioms Cochrane.Monetarism.CashInAdvance.PF.monetary_seigniorage
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_valuation
#print axioms Cochrane.Monetarism.CashInAdvance.PF.monetary_valuation
#print axioms Cochrane.Monetarism.CashInAdvance.PF.printed_19_38_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.printed_19_38_counterexample
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_price_unique
#print axioms Cochrane.Monetarism.CashInAdvance.PF.frictionless_price_formula
#print axioms Cochrane.Monetarism.CashInAdvance.PF.zero_debt_indeterminate
#print axioms Cochrane.Monetarism.CashInAdvance.PF.example_equilibrium
#print axioms Cochrane.Monetarism.CashInAdvance.PF.example_unique
#print axioms Cochrane.Monetarism.CashInAdvance.PF.E14_example
#print axioms Cochrane.Monetarism.CashInAdvance.PF.passiveSurplus
#print axioms Cochrane.Monetarism.CashInAdvance.PF.passive_fiscal_indeterminate
#print axioms Cochrane.Monetarism.CashInAdvance.PF.usual_equilibrium
#print axioms Cochrane.Monetarism.CashInAdvance.PF.usual_rate
#print axioms Cochrane.Monetarism.CashInAdvance.PF.usual_fails_low_growth
#print axioms Cochrane.Monetarism.CashInAdvance.PF.E15_counterexample
#print axioms Cochrane.Monetarism.CashInAdvance.PF.deflation_equilibrium
#print axioms Cochrane.Monetarism.CashInAdvance.PF.deflation_real_money
#print axioms Cochrane.Monetarism.CashInAdvance.PF.deflation_real_money_grows_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.deflation_money_tvc_iff
#print axioms Cochrane.Monetarism.CashInAdvance.PF.active_fiscal_prunes
#print axioms Cochrane.Monetarism.CashInAdvance.PF.coordination
#print axioms Cochrane.Monetarism.ContinuousTime.tendsto_of_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.forward_iff
#print axioms Cochrane.Monetarism.ContinuousTime.integral_ratio_eq
#print axioms Cochrane.Monetarism.ContinuousTime.real_form_iff
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_discount
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_nominal_discount
#print axioms Cochrane.Monetarism.ContinuousTime.inv_nominal_value
#print axioms Cochrane.Monetarism.ContinuousTime.lambda_ratio_eq_W
#print axioms Cochrane.Monetarism.ContinuousTime.flow_real
#print axioms Cochrane.Monetarism.ContinuousTime.printing_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.money_printing_iff
#print axioms Cochrane.Monetarism.ContinuousTime.interest_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.money_interest_iff
#print axioms Cochrane.Monetarism.ContinuousTime.printing_interest_iff_money_tvc
#print axioms Cochrane.Monetarism.ContinuousTime.printing_W_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.money_printing_W_iff
#print axioms Cochrane.Monetarism.ContinuousTime.interest_W_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.money_interest_W_iff
#print axioms Cochrane.Monetarism.ContinuousTime.printed_index_counterexample
#print axioms Cochrane.Monetarism.ContinuousTime.mixed_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.money_mixed_iff
#print axioms Cochrane.Monetarism.ContinuousTime.mixed_rate_lt
#print axioms Cochrane.Monetarism.ContinuousTime.budget_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.pv_budget_iff
#print axioms Cochrane.Monetarism.ContinuousTime.valuation_4_5
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_expDisc
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_marginal_utility
#print axioms Cochrane.Monetarism.ContinuousTime.foc_4_1
#print axioms Cochrane.Monetarism.ContinuousTime.foc_4_2
#print axioms Cochrane.Monetarism.ContinuousTime.foc_4_3
#print axioms Cochrane.Monetarism.ContinuousTime.cesX
#print axioms Cochrane.Monetarism.ContinuousTime.cesU
#print axioms Cochrane.Monetarism.ContinuousTime.cesX_pos
#print axioms Cochrane.Monetarism.ContinuousTime.ces_perfect_substitutes
#print axioms Cochrane.Monetarism.ContinuousTime.ces_separable
#print axioms Cochrane.Monetarism.ContinuousTime.rpow_one_sub
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_cesU_c
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_cesU_m
#print axioms Cochrane.Monetarism.ContinuousTime.ces_mrs_4_7
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_ucc
#print axioms Cochrane.Monetarism.ContinuousTime.hasDerivAt_ucm
#print axioms Cochrane.Monetarism.ContinuousTime.ces_ucc_ratio
#print axioms Cochrane.Monetarism.ContinuousTime.ces_ucc_elasticity
#print axioms Cochrane.Monetarism.ContinuousTime.ces_ucc_elasticity_ratio
#print axioms Cochrane.Monetarism.ContinuousTime.ces_ucm_elasticity
#print axioms Cochrane.Monetarism.ContinuousTime.ces_ucm_elasticity_ratio
#print axioms Cochrane.Monetarism.ContinuousTime.ces_A_eq
#print axioms Cochrane.Monetarism.ContinuousTime.cesNorm
#print axioms Cochrane.Monetarism.ContinuousTime.log_mean_hasDerivAt
#print axioms Cochrane.Monetarism.ContinuousTime.ces_norm_limit
#print axioms Cochrane.Monetarism.ContinuousTime.ces_norm_utility_limit
#print axioms Cochrane.Monetarism.ContinuousTime.ces_unnorm_eq
#print axioms Cochrane.Monetarism.ContinuousTime.ces_unnorm_diverges
#print axioms Cochrane.Monetarism.ContinuousTime.ces_unnorm_no_limit
#print axioms Cochrane.Monetarism.ContinuousTime.ces_limit_min
#print axioms Cochrane.Monetarism.ContinuousTime.ces_coeff_rewrite
#print axioms Cochrane.Monetarism.ContinuousTime.ces_limit_min_corrected
#print axioms Cochrane.Monetarism.ContinuousTime.demand_limit_fixed
#print axioms Cochrane.Monetarism.ContinuousTime.demand_corrected
#print axioms Cochrane.Monetarism.ContinuousTime.demand_corrected_limit
#print axioms Cochrane.Monetarism.ContinuousTime.velocity_of_demand
#print axioms Cochrane.Monetarism.ContinuousTime.alpha_eq_inv_V_iff
#print axioms Cochrane.Monetarism.ContinuousTime.demand_4_8
#print axioms Cochrane.Monetarism.ContinuousTime.demand_4_10
#print axioms Cochrane.Monetarism.ContinuousTime.interest_cost_formula
#print axioms Cochrane.Monetarism.ContinuousTime.interest_cost_tendsto_iff
#print axioms Cochrane.Monetarism.ContinuousTime.is_prettier
#print axioms Cochrane.Monetarism.ContinuousTime.is_4_12
#print axioms Cochrane.Monetarism.ContinuousTime.demand_log_deriv
#print axioms Cochrane.Monetarism.ContinuousTime.log_consumption_deriv
#print axioms Cochrane.Monetarism.ContinuousTime.is_exact
#print axioms Cochrane.Monetarism.ContinuousTime.is_curve_exact
#print axioms Cochrane.Monetarism.ContinuousTime.first_order_term
#print axioms Cochrane.Monetarism.ContinuousTime.coefficient_differentiable
#print axioms Cochrane.Monetarism.ContinuousTime.coefficient_gap
#print axioms Cochrane.Monetarism.ContinuousTime.E21_steady_state
#print axioms Cochrane.Monetarism.ContinuousTime.E21_deviations
#print axioms Cochrane.Monetarism.ContinuousTime.is_4_14_exact
#print axioms Cochrane.Monetarism.ContinuousTime.A_ratio_gap
#print axioms Cochrane.Monetarism.ContinuousTime.E21_discrete_inconsistent
#print axioms Cochrane.Monetarism.ContinuousTime.constraint_4_16
#print axioms Cochrane.Monetarism.ContinuousTime.hamiltonian_money_demand
#print axioms Cochrane.Monetarism.ContinuousTime.hamiltonian_eq_i
#print axioms Cochrane.Monetarism.ContinuousTime.constant_consumption_rate
#print axioms Cochrane.Monetarism.ContinuousTime.tvc_4_17_iff
#print axioms Cochrane.Monetarism.Links.one_div_rpow_eq
#print axioms Cochrane.Monetarism.Links.ratioMap_eq_one_div_nextX
#print axioms Cochrane.Monetarism.Links.isMPath_iff_isPowerPath
#print axioms Cochrane.Monetarism.Links.isMIUPath_iff_isMPath
#print axioms Cochrane.Monetarism.Links.e13_iff_e17
#print axioms Cochrane.Monetarism.Links.deflation_rate
#print axioms Cochrane.Monetarism.Links.explosion_same_path
#print axioms Cochrane.Monetarism.Links.deflation_tvc_miu_iff_cia
#print axioms Cochrane.Monetarism.Links.cia_boundary_deflation
#print axioms Cochrane.Monetarism.Links.flow_pv_tsum_iff_tvc
#print axioms Cochrane.Monetarism.Links.cia_euler_sufficient_of_concave
#print axioms Cochrane.Monetarism.Links.tree_euler_sufficient_of_concave
#print axioms Cochrane.Monetarism.Links.meas_iff_tAdapted
#print axioms Cochrane.Monetarism.Links.miu_foc_money_demand
#print axioms Cochrane.Monetarism.Links.miu_foc_log_growth
#print axioms Cochrane.Monetarism.Links.interest_cost_continuous_limit
#print axioms Cochrane.Monetarism.Links.ces_nonsep_eq_ct
#print axioms Cochrane.Monetarism.Links.ces_uc_nonsep_eq_ct
#print axioms Cochrane.Monetarism.Links.ces_um_nonsep_eq_ct
#print axioms Cochrane.Monetarism.Links.demand_4_8_eq_power_demand
#print axioms Cochrane.Monetarism.Links.cagan_steady_revenue
#print axioms Cochrane.Monetarism.Links.cagan_ni7
#print axioms Cochrane.Monetarism.Links.seig_eq_revenue
#print axioms Cochrane.Monetarism.Links.passiveSurplus_regimes_eq_cia
