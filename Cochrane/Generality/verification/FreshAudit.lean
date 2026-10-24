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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
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

namespace Cochrane.Generality

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

end Cochrane.Generality

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

namespace Cochrane.Generality

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

end Cochrane.Generality

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

namespace Cochrane.Generality.ExpectationsFiniteTree

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

end Cochrane.Generality.ExpectationsFiniteTree

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

namespace Cochrane.Generality.ForwardSolution

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

end Cochrane.Generality.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.1, pp. 52–53, eqs.
(3.1)–(3.3), and Online Appendix A1, §1.2.1, pp. 559–561, eqs. (1.14)–(1.16), (1.19), the
forward-guidance display and the roll-over display.

## Setting

Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and `E_t` is an arbitrary
`ExpectationSystem` (perfect foresight or genuine uncertainty). Discounting uses one-period
stochastic discount factors `m t = Λ_{t+1}/Λ_t` (known at `t + 1`); the multi-period factor is
`sdf m t n = ∏_{k<n} m (t+k) = Λ_{t+n}/Λ_t`. The book's §3.1 case is the constant factor
`m ≡ β` (`sdf_const`), for which `sdf m t n = βⁿ`; everything below holds for a general `m`
(which §3.3 needs).

Debt: `B t j` is `B_{t−1}^{(t+j)}`, the face value of zero-coupon bonds outstanding at the end of
date `t − 1` that come due at `t + j`; so `B_t^{(t+j)} = B (t+1) (j−1)`. `Q t j` is
`Q_t^{(t+j)}`, the date-`t` price of a bond due at `t + j`.

## Main results

* Discounting machinery (restated from the Woodford Chapter 2 project, `AssetPricing` and
  `IntertemporalBudget`, adapted to signed surpluses): `sdf`, `MonotoneConvergence`, `pv`,
  `telescope`, and the general valuation theorem `flow_tvc_iff_pv`: for an adapted real debt
  value `x`, the flow `x_t = s_t + E_t[m_t x_{t+1}]` at every date plus the transversality
  condition `lim_N E_t[sdf_N x_{t+N}] = 0` at every date hold iff
  `x_t = ∑_n E_t[sdf_n s_{t+n}]` at every date, for signed surpluses with absolutely summable
  present values. `E_tsum_abs`, `pv_eq_E_tsum`: `E_t` may be taken outside the sum.
* (3.1): `ZeroPrice`, `zeroPrice_real`, `zeroPrice_zero`, `zeroPrice_recursive`; under perfect
  foresight `zeroPrice_pf_prod` (the term structure is the product of one-period prices).
* (3.2)–(3.3) with a finite maximum maturity: `FlowLT`, `flowLT_iff_value` (exact algebra),
  `flowLT_iff_recursion` (uses (3.1)), `valuationLT_iff` (flow + TVC ⟺ (3.3) at all dates), and
  survey error E28: the book's converse "derive (3.2) from (3.3)" needs (3.1)
  (`valuationLT_not_imp_flow`).
* (3.2)–(3.3) with a geometric maturity structure `B_{t−1}^{(t+j)} = ωʲ b_t`, genuine infinite
  sums: `GeomFlow`, `geomFlow_iff_recursion`, `valuationGeom_iff`.
* A1 (1.14)–(1.16), (1.19): `geom_value`, `pv_const_value`, `steady_state_1_15`,
  `price_jump_perm`, `price_jump_of_valuation`, `price_jump_lt_one_iff`, `price_jump_omega_zero`,
  `price_jump_perpetuity`, numerical checks; the forward-guidance closed form `price_jump_fg`,
  `fg_tendsto_zero`,
  `fg_drop_antitone_T`, `fg_drop_strictMonoOn_omega`; transitory and mean-reverting rises
  (`annuity_mono_rates`, `price_le_of_annuity_le`, `meanReverting_le_perm`); roll-over
  `geom_rollover` and `steady_flow_iff_1_15`; the knife edge `geom_knife_edge` (no trading iff
  `P_ts_t = ωᵗb_0`), `knife_edge_surplus_known`, `geom_needs_tending`.
-/

namespace Cochrane.Generality.LongTermDebt

open Filter Topology

variable {Ω : Type*}

/-! ### Stochastic discount factors (restated from the Woodford Chapter 2 project) -/

/-- Cochrane (2023), §3.3, p. 55 (and §3.1, p. 53 with `m ≡ β`): the multi-period discount
factor `Λ_{t+n}/Λ_t = ∏_{k<n} m_{t+k}` built from one-period factors `m s = Λ_{s+1}/Λ_s`
(restated from the Woodford Chapter 2 project). -/
def sdf (m : ℕ → Ω → ℝ) (t n : ℕ) : Ω → ℝ := ∏ k ∈ Finset.range n, m (t + k)

/-- Cochrane (2023), p. 55: `Λ_t/Λ_t = 1`. -/
@[simp] theorem sdf_zero (m : ℕ → Ω → ℝ) (t : ℕ) : sdf m t 0 = 1 := by
  simp [sdf]

/-- Cochrane (2023), p. 55: `Λ_{t+n+1}/Λ_t = (Λ_{t+n}/Λ_t)(Λ_{t+n+1}/Λ_{t+n})`. -/
theorem sdf_succ (m : ℕ → Ω → ℝ) (t n : ℕ) : sdf m t (n + 1) = sdf m t n * m (t + n) := by
  simp [sdf, Finset.prod_range_succ]

/-- Cochrane (2023), p. 55: `Λ_{t+n+1}/Λ_t = (Λ_{t+1}/Λ_t)(Λ_{t+1+n}/Λ_{t+1})`. -/
theorem sdf_succ' (m : ℕ → Ω → ℝ) (t n : ℕ) : sdf m t (n + 1) = m t * sdf m (t + 1) n := by
  rw [sdf, Finset.prod_range_succ', sdf, add_zero, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show t + (k + 1) = t + 1 + k by omega]

/-- Cochrane (2023), p. 55: the one-period factor is `Λ_{t+1}/Λ_t`. -/
@[simp] theorem sdf_one (m : ℕ → Ω → ℝ) (t : ℕ) : sdf m t 1 = m t := by
  simp [sdf]

/-- Cochrane (2023), p. 55: `Λ_{t+n+k}/Λ_t = (Λ_{t+n}/Λ_t)(Λ_{t+n+k}/Λ_{t+n})`. -/
theorem sdf_add (m : ℕ → Ω → ℝ) (t n k : ℕ) :
    sdf m t (n + k) = sdf m t n * sdf m (t + n) k := by
  simp only [sdf, Finset.prod_range_add, add_assoc]

/-- Cochrane (2023), §3.1, p. 53: with the constant discount factor `m ≡ β` of the
frictionless constant-real-rate model, `Λ_{t+n}/Λ_t = βⁿ`. -/
theorem sdf_const (β : ℝ) (t n : ℕ) : sdf (fun _ _ => β : ℕ → Ω → ℝ) t n = fun _ => β ^ n := by
  funext ω
  simp [sdf, Finset.prod_apply]

/-- Cochrane (2023), p. 55: nonnegative one-period factors give nonnegative discount factors. -/
theorem sdf_nonneg {m : ℕ → Ω → ℝ} (hm : ∀ s ω, 0 ≤ m s ω) (t n : ℕ) (ω : Ω) :
    0 ≤ sdf m t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_nonneg fun k _ => hm (t + k) ω

/-- Cochrane (2023), p. 55: positive one-period factors give positive discount factors. -/
theorem sdf_pos {m : ℕ → Ω → ℝ} (hm : ∀ s ω, 0 < m s ω) (t n : ℕ) (ω : Ω) :
    0 < sdf m t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_pos fun k _ => hm (t + k) ω

variable (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 55 (information accumulates): a variable known at `s` is known at
every later date. -/
theorem known_of_le {s T : ℕ} (h : s ≤ T) {x : Ω → ℝ} (hx : 𝔼.E s x = x) : 𝔼.E T x = x :=
  calc 𝔼.E T x = 𝔼.E T (𝔼.E s x) := by rw [hx]
    _ = 𝔼.E s x := 𝔼.known h x
    _ = x := hx

/-- Cochrane (2023), p. 55 (pull-out): the product of two date-`t` variables is known at `t`. -/
theorem known_mul (hP : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hP t a b ha, hb]

/-- Cochrane (2023), p. 55: expectations of nonnegative variables are nonnegative. -/
theorem E_nonneg {t : ℕ} {x : Ω → ℝ} (hx : ∀ ω, 0 ≤ x ω) (ω : Ω) : 0 ≤ 𝔼.E t x ω := by
  have h := 𝔼.mono t (show (0 : Ω → ℝ) ≤ x from hx) ω
  simpa using h

/-- Cochrane (2023), p. 55: `|E_t x| ≤ E_t |x|`. -/
theorem abs_E_le_E_abs (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    |𝔼.E t x ω| ≤ 𝔼.E t (fun ω' => |x ω'|) ω := by
  rw [abs_le]
  constructor
  · have h := 𝔼.mono t (show -(fun ω' => |x ω'|) ≤ x from fun ω' => by
      simp only [Pi.neg_apply]; exact neg_abs_le _) ω
    rw [map_neg] at h
    simpa using h
  · exact 𝔼.mono t (show x ≤ fun ω' => |x ω'| from fun ω' => le_abs_self _) ω

/-- Cochrane (2023), p. 55: `Λ_{t+n}/Λ_t` is known at `t + n` when each `m s` is known at
`s + 1`. -/
theorem sdf_known (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (t n : ℕ) : 𝔼.E (t + n) (sdf m t n) = sdf m t n := by
  induction n with
  | zero =>
    rw [sdf_zero]
    exact 𝔼.const (t + 0) 1
  | succ n ih =>
    rw [sdf_succ, ← add_assoc]
    exact known_mul 𝔼 hP (known_of_le 𝔼 (Nat.le_succ _) ih) (hm (t + n))

/-- Cochrane (2023), p. 55 (pull-out and the law of iterated expectations):
`E_t[(Λ_{t+n}/Λ_t) E_{t+n} Y] = E_t[(Λ_{t+n}/Λ_t) Y]`. -/
theorem E_sdf_mul_E (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (t n : ℕ) (Y : Ω → ℝ) :
    𝔼.E t (sdf m t n * 𝔼.E (t + n) Y) = 𝔼.E t (sdf m t n * Y) := by
  rw [← hP (t + n) _ _ (sdf_known 𝔼 hP hm t n), 𝔼.tower (Nat.le_add_right t n)]

/-! ### Conditional monotone convergence and present values -/

/-- Cochrane (2023), p. 53 and p. 55 (the interchange of `E_t` and infinite sums behind
(3.3) and (3.5), survey E29): conditional monotone convergence. Not implied by the
`ExpectationSystem` axioms, so it is a hypothesis; it holds for perfect foresight and for every
finite event tree (restated from the Woodford Chapter 2 project). -/
def MonotoneConvergence (𝔼 : ExpectationSystem Ω) : Prop :=
  ∀ t (f : ℕ → Ω → ℝ), (∀ k ω, 0 ≤ f k ω) → (∀ ω, Summable fun k => f k ω) →
    ∀ ω, HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω)

/-- Cochrane (2023), p. 55: perfect foresight satisfies conditional monotone convergence. -/
theorem perfectForesight_monotoneConvergence : MonotoneConvergence perfectForesight :=
  fun _ _ _ hs ω => (hs ω).hasSum

/-- Cochrane (2023), p. 55: every finite event tree satisfies conditional monotone
convergence, so the results hold under genuine uncertainty. -/
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

/-- Cochrane (2023), p. 55: `E_t` commutes with a series of random variables that converges
absolutely in every state (split into positive and negative parts, then conditional monotone
convergence). -/
theorem E_tsum_abs (hMC : MonotoneConvergence 𝔼) (t : ℕ) {f : ℕ → Ω → ℝ}
    (hf : ∀ ω, Summable fun k => |f k ω|) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω) := by
  set fp : ℕ → Ω → ℝ := fun k ω' => max (f k ω') 0 with hfp
  set fn : ℕ → Ω → ℝ := fun k ω' => max (-f k ω') 0 with hfn
  have hfp0 : ∀ k ω', 0 ≤ fp k ω' := fun _ _ => le_max_right _ _
  have hfn0 : ∀ k ω', 0 ≤ fn k ω' := fun _ _ => le_max_right _ _
  have hsp : ∀ ω', Summable fun k => fp k ω' := fun ω' =>
    Summable.of_nonneg_of_le (fun k => hfp0 k ω')
      (fun k => max_le (le_abs_self _) (abs_nonneg _)) (hf ω')
  have hsn : ∀ ω', Summable fun k => fn k ω' := fun ω' =>
    Summable.of_nonneg_of_le (fun k => hfn0 k ω')
      (fun k => max_le (neg_le_abs _) (abs_nonneg _)) (hf ω')
  have hsplit : ∀ k, f k = fp k - fn k := fun k => by
    funext ω'
    simp [hfp, hfn, max_zero_sub_max_neg_zero_eq_self]
  have hsum : (fun ω' => ∑' k, f k ω') =
      (fun ω' => ∑' k, fp k ω') - fun ω' => ∑' k, fn k ω' := by
    funext ω'
    rw [Pi.sub_apply, ← (hsp ω').tsum_sub (hsn ω')]
    exact tsum_congr fun k => congrFun (hsplit k) ω'
  rw [hsum, map_sub, Pi.sub_apply]
  convert (hMC t fp hfp0 hsp ω).sub (hMC t fn hfn0 hsn ω) using 1
  funext k
  rw [hsplit k, map_sub, Pi.sub_apply]

/-- Cochrane (2023), eqs. (3.3), (3.5), pp. 53, 55: the date-`t` present value
`∑_{n ≥ 0} E_t[(Λ_{t+n}/Λ_t) s_{t+n}]` of a real surplus stream, as a genuine infinite sum in
each state (summability is an explicit hypothesis wherever it is used). -/
noncomputable def pv (m s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' n, 𝔼.E t (sdf m t n * s (t + n)) ω

/-- Cochrane (2023), pp. 53, 55 (survey E29): the surplus stream has absolutely summable
present values, `∑_n E_t[(Λ_{t+n}/Λ_t)|s_{t+n}|] < ∞` at every date and in every state.
Surpluses are signed, so absolute (not mere) summability is assumed. -/
def SurplusSummable (m s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun n => 𝔼.E t (sdf m t n * fun ω' => |s (t + n) ω'|) ω

/-- Cochrane (2023), pp. 53, 55: `|E_t[sdf·s]| ≤ E_t[sdf·|s|]` for nonnegative discount
factors. -/
theorem abs_E_sdf_mul_le {m : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω) (s : ℕ → Ω → ℝ)
    (t n : ℕ) (ω : Ω) :
    |𝔼.E t (sdf m t n * s (t + n)) ω| ≤ 𝔼.E t (sdf m t n * fun ω' => |s (t + n) ω'|) ω := by
  have h : (fun ω' => |(sdf m t n * s (t + n)) ω'|) = sdf m t n * fun ω' => |s (t + n) ω'| :=
    funext fun ω' => by
      simp only [Pi.mul_apply, abs_mul, abs_of_nonneg (sdf_nonneg hm0 t n ω')]
  rw [← h]
  exact abs_E_le_E_abs 𝔼 t _ ω

/-- Cochrane (2023), pp. 53, 55: absolutely summable surpluses have a summable present-value
series at every date and in every state. -/
theorem summable_pv {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * s (t + n)) ω :=
  Summable.of_norm_bounded (hs t ω) fun n => by
    rw [Real.norm_eq_abs]; exact abs_E_sdf_mul_le 𝔼 hm0 s t n ω

/-- Cochrane (2023), pp. 53, 55: `E_t` may be taken outside the present-value sum,
`∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}] = E_t ∑_n (Λ_{t+n}/Λ_t)s_{t+n}` (the book's notation), whenever
the discounted surplus series converges absolutely in every state. -/
theorem pv_eq_E_tsum (hMC : MonotoneConvergence 𝔼) {m s : ℕ → Ω → ℝ} (t : ℕ)
    (habs : ∀ ω, Summable fun n => |sdf m t n ω * s (t + n) ω|) :
    pv 𝔼 m s t = 𝔼.E t (fun ω => ∑' n, sdf m t n ω * s (t + n) ω) := by
  funext ω
  exact (E_tsum_abs 𝔼 hMC t (f := fun n => sdf m t n * s (t + n)) habs ω).tsum_eq

/-- Cochrane (2023), p. 55 (restated from the Woodford Chapter 2 project): for a nonnegative
stream `Y` whose date-`(t+N)` present value converges in every state,
`E_t[sdf_N ∑_n E_{t+N}[sdf Y]] = ∑_k E_t[sdf_{k+N} Y_{t+k+N}]`. -/
theorem hasSum_E_sdf_mul_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m Y : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hY : ∀ s ω, 0 ≤ Y s ω) (t N : ℕ)
    (hs : ∀ ω, Summable fun n => 𝔼.E (t + N) (sdf m (t + N) n * Y (t + N + n)) ω) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (sdf m t (k + N) * Y (t + (k + N))) ω)
      (𝔼.E t (sdf m t N * pv 𝔼 m Y (t + N)) ω) := by
  set f : ℕ → Ω → ℝ :=
    fun n => sdf m t N * 𝔼.E (t + N) (sdf m (t + N) n * Y (t + N + n)) with hf
  have hf0 : ∀ k ω, 0 ≤ f k ω := fun k ω =>
    mul_nonneg (sdf_nonneg hm0 t N ω)
      (E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hm0 _ _ ω') (hY _ ω')) ω)
  have hfs : ∀ ω, Summable fun k => f k ω := fun ω => (hs ω).mul_left (sdf m t N ω)
  have hsum : sdf m t N * pv 𝔼 m Y (t + N) = fun ω' => ∑' k, f k ω' := by
    funext ω'
    simp only [hf, pv, Pi.mul_apply, tsum_mul_left]
  rw [hsum]
  convert hMC t f hf0 hfs ω using 1
  funext k
  simp only [hf]
  rw [E_sdf_mul_E 𝔼 hP hm, ← mul_assoc, ← sdf_add, add_assoc, add_comm N k]

/-- Cochrane (2023), p. 55: the positive part `max s 0` of the surplus. -/
def posPart (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => max (s k ω) 0

/-- Cochrane (2023), p. 55: the negative part `max (−s) 0` of the surplus (a deficit). -/
def negPart (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => max (-s k ω) 0

/-- Cochrane (2023), p. 55: `s = s⁺ − s⁻`. -/
theorem posPart_sub_negPart (s : ℕ → Ω → ℝ) (k : ℕ) : posPart s k - negPart s k = s k := by
  funext ω
  simp [posPart, negPart, max_zero_sub_max_neg_zero_eq_self]

/-- Cochrane (2023), p. 55: absolutely summable surpluses have summable positive-part present
values. -/
theorem summable_posPart {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * posPart s (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hm0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hs t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, posPart]
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
    (sdf_nonneg hm0 t n ω')

/-- Cochrane (2023), p. 55: absolutely summable surpluses have summable negative-part present
values. -/
theorem summable_negPart {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * negPart s (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hm0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hs t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, negPart]
  exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _))
    (sdf_nonneg hm0 t n ω')

/-- Cochrane (2023), p. 55: the present-value terms of `s` split as those of `s⁺` minus those
of `s⁻`. -/
theorem E_sdf_mul_split (m s : ℕ → Ω → ℝ) (t n : ℕ) :
    𝔼.E t (sdf m t n * s (t + n)) =
      𝔼.E t (sdf m t n * posPart s (t + n)) - 𝔼.E t (sdf m t n * negPart s (t + n)) := by
  rw [← map_sub, ← mul_sub, posPart_sub_negPart]

/-- Cochrane (2023), p. 55, for signed surpluses (restated from the Woodford Chapter 2
project): `E_t[sdf_N · pv_{t+N}] = ∑_k E_t[sdf_{k+N} s_{t+k+N}]`, the tail of the date-`t`
present value. -/
theorem hasSum_E_sdf_mul_pv_signed (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m s : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t N : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (sdf m t (k + N) * s (t + (k + N))) ω)
      (𝔼.E t (sdf m t N * pv 𝔼 m s (t + N)) ω) := by
  have hp := hasSum_E_sdf_mul_pv 𝔼 hMC hP hm hm0 (Y := posPart s)
    (fun _ _ => le_max_right _ _) t N (summable_posPart 𝔼 hm0 hs (t + N)) ω
  have hn := hasSum_E_sdf_mul_pv 𝔼 hMC hP hm hm0 (Y := negPart s)
    (fun _ _ => le_max_right _ _) t N (summable_negPart 𝔼 hm0 hs (t + N)) ω
  have hpv : pv 𝔼 m s (t + N) = pv 𝔼 m (posPart s) (t + N) - pv 𝔼 m (negPart s) (t + N) := by
    funext ω'
    simp only [pv, Pi.sub_apply]
    rw [← (summable_posPart 𝔼 hm0 hs (t + N) ω').tsum_sub
      (summable_negPart 𝔼 hm0 hs (t + N) ω')]
    refine tsum_congr fun n => ?_
    rw [E_sdf_mul_split 𝔼 m s (t + N) n]
    rfl
  rw [hpv, mul_sub, map_sub]
  convert hp.sub hn using 1
  funext k
  rw [E_sdf_mul_split 𝔼 m s t (k + N)]
  rfl

/-- Cochrane (2023), p. 55: the present value is known at its date. -/
theorem E_pv_self (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) : 𝔼.E t (pv 𝔼 m s t) = pv 𝔼 m s t := by
  funext ω
  have h := hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t 0 ω
  simp only [sdf_zero, one_mul, add_zero] at h
  exact h.tsum_eq.symm

/-! ### Flow, transversality and present value -/

/-- Cochrane (2023), p. 55 (the flow condition in real terms): `x_t = s_t + E_t[m_t x_{t+1}]`
at every date, where `x_t` is the real value of debt at the start of date `t`. -/
def FlowRec (m s x : ℕ → Ω → ℝ) : Prop := ∀ t, x t = s t + 𝔼.E t (m t * x (t + 1))

/-- Cochrane (2023), p. 55: the transversality condition `lim_N E_t[(Λ_{t+N}/Λ_t)x_{t+N}] = 0`
looking forward from date `t`. -/
def TVC (m x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N => 𝔼.E t (sdf m t N * x (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 55: the slack `x_t − s_t − E_t[m_t x_{t+1}]` in the date-`t` flow. -/
def slack (m s x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := x t - s t - 𝔼.E t (m t * x (t + 1))

/-- Cochrane (2023), p. 53 ("iterating forward") and p. 55, as an exact identity: for `x`
known at `t`, `x_t − ∑_{n<N} E_t[sdf_n s_{t+n}] − E_t[sdf_N x_{t+N}]` is the discounted sum of
flow slacks `∑_{n<N} E_t[sdf_n slack_{t+n}]`. -/
theorem telescope (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) {t : ℕ} (hx : 𝔼.E t (x t) = x t) (N : ℕ) (ω : Ω) :
    x t ω - ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω
      - 𝔼.E t (sdf m t N * x (t + N)) ω
      = ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * slack 𝔼 m s x (t + n)) ω := by
  induction N with
  | zero => simp [hx]
  | succ N ih =>
    have key : 𝔼.E t (sdf m t N * slack 𝔼 m s x (t + N)) =
        𝔼.E t (sdf m t N * x (t + N)) - 𝔼.E t (sdf m t N * s (t + N)) -
          𝔼.E t (sdf m t (N + 1) * x (t + (N + 1))) := by
      simp only [slack, mul_sub, map_sub]
      rw [E_sdf_mul_E 𝔼 hP hm, ← mul_assoc, ← sdf_succ, add_assoc]
    have k := congrFun key ω
    simp only [Pi.sub_apply] at k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, k]
    linarith

/-- Cochrane (2023), p. 53 and p. 55 (from flow to present value): if the real debt value is
known at `t`, the flow condition holds at all dates from `t` on and the transversality
condition holds at `t`, then `x_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]`, with the series
convergent. -/
theorem hasSum_of_flow_tvc (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) {t : ℕ} (hx : 𝔼.E t (x t) = x t)
    (hflow : ∀ n, x (t + n) = s (t + n) + 𝔼.E (t + n) (m (t + n) * x (t + n + 1)))
    (htvc : TVC 𝔼 m x t) (ω : Ω) :
    HasSum (fun n => 𝔼.E t (sdf m t n * s (t + n)) ω) (x t ω) := by
  have hsl : ∀ n, slack 𝔼 m s x (t + n) = 0 := fun n => by
    funext ω'
    have h := congrFun (hflow n) ω'
    simp only [slack, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h ⊢
    linarith
  have hpart : ∀ N, ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω =
      x t ω - 𝔼.E t (sdf m t N * x (t + N)) ω := by
    intro N
    have h := telescope 𝔼 hP (s := s) hm hx N ω
    simp only [hsl, mul_zero, map_zero, Pi.zero_apply, Finset.sum_const_zero] at h
    linarith
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω) atTop
      (𝓝 (x t ω)) := by
    simp_rw [hpart]
    simpa using (tendsto_const_nhds (x := x t ω)).sub (htvc ω)
  have hsum := summable_pv 𝔼 hm0 hs t ω
  rw [tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat]
  exact hsum.hasSum

/-- Cochrane (2023), p. 53 ("derive the flow from the present value at two adjacent dates")
and p. 55: if `x_t` equals the present value at every date, the flow condition holds. -/
theorem flow_of_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hx : ∀ t, x t = pv 𝔼 m s t) : FlowRec 𝔼 m s x := by
  intro t
  funext ω
  have h1 := hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t 1 ω
  simp only [sdf_one] at h1
  have hsum := summable_pv 𝔼 hm0 hs t ω
  rw [hx t, hx (t + 1), Pi.add_apply]
  simp only [pv]
  rw [hsum.tsum_eq_zero_add, ← h1.tsum_eq]
  simp only [sdf_zero, one_mul, add_zero, hsa t]

/-- Cochrane (2023), p. 55: if `x_t` equals the present value at every date, the
transversality condition holds at every date (the discounted value is the tail of a
convergent series). -/
theorem tvc_of_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (hx : ∀ t, x t = pv 𝔼 m s t) (t : ℕ) : TVC 𝔼 m x t := by
  intro ω
  have heq : ∀ N, 𝔼.E t (sdf m t N * x (t + N)) ω =
      ∑' k, 𝔼.E t (sdf m t (k + N) * s (t + (k + N))) ω := fun N => by
    rw [hx (t + N)]
    exact (hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t N ω).tsum_eq.symm
  simp_rw [heq]
  exact tendsto_sum_nat_add fun n => 𝔼.E t (sdf m t n * s (t + n)) ω

/-- Cochrane (2023), p. 53 (the step from (3.2) to (3.3) and back) and p. 55, eq. (3.5): for
an adapted real debt value `x`, nonnegative one-period discount factors known one period ahead,
adapted surpluses with absolutely summable present values, and `E_t` with pull-out and
conditional monotone convergence: the flow condition at every date plus the transversality
condition at every date hold iff `x_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` at every date. -/
theorem flow_tvc_iff_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hx : 𝔼.Adapted x) :
    (FlowRec 𝔼 m s x ∧ ∀ t, TVC 𝔼 m x t) ↔ ∀ t, x t = pv 𝔼 m s t := by
  constructor
  · rintro ⟨hflow, htvc⟩ t
    funext ω
    exact (hasSum_of_flow_tvc 𝔼 hP hm hm0 hs (hx t) (fun n => hflow (t + n)) (htvc t)
      ω).tsum_eq.symm
  · intro hpv
    exact ⟨flow_of_pv 𝔼 hMC hP hm hm0 hsa hs hpv, tvc_of_pv 𝔼 hMC hP hm hm0 hs hpv⟩


/-! ### Zero-coupon bond prices (3.1) -/

/-- Cochrane (2023), eq. (3.1), p. 53, with a general discount factor (p. 55):
`Q_t^{(t+j)} = E_t[(Λ_{t+j}/Λ_t) P_t/P_{t+j}]`; the book's case is `m ≡ β`
(`zeroPrice_const_iff`). -/
def ZeroPrice (m P : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ t j, Q t j = 𝔼.E t (sdf m t j * fun ξ => P t ξ / P (t + j) ξ)

/-- Cochrane (2023), eq. (3.1), p. 53: with `m ≡ β`, `ZeroPrice` is exactly
`Q_t^{(t+j)} = E_t[βʲ P_t/P_{t+j}]`. -/
theorem zeroPrice_const_iff (β : ℝ) (P : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) :
    ZeroPrice 𝔼 (fun _ _ => β) P Q ↔
      ∀ t j, Q t j = 𝔼.E t (fun ξ => β ^ j * (P t ξ / P (t + j) ξ)) := by
  simp only [ZeroPrice, sdf_const]
  rfl

/-- Cochrane (2023), eq. (3.1), p. 53, in real terms: the real price `Q_t^{(t+j)}/P_t` of a
nominal bond, `E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
noncomputable def realPrice (m P : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  𝔼.E t (sdf m t j * fun ξ => (P (t + j) ξ)⁻¹)

/-- Cochrane (2023), eq. (3.1), p. 53: given (3.1) and a price level known at `t`,
`Q_t^{(t+j)} = P_t E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
theorem zeroPrice_eq_mul (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) (j : ℕ) :
    Q t j = P t * realPrice 𝔼 m P t j := by
  rw [hQ t j, realPrice, ← hP t (P t) _ hPa]
  congr 1
  funext ξ
  simp only [Pi.mul_apply, div_eq_mul_inv]
  ring

/-- Cochrane (2023), eq. (3.1), p. 53: `Q_t^{(t+j)}/P_t = E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
theorem zeroPrice_real (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) (j : ℕ) {ξ : Ω}
    (hP0 : P t ξ ≠ 0) : Q t j ξ / P t ξ = realPrice 𝔼 m P t j ξ := by
  rw [zeroPrice_eq_mul 𝔼 hP hQ hPa j, Pi.mul_apply]
  field_simp

/-- Cochrane (2023), eq. (3.1), p. 53: maturing bonds are worth their face value,
`Q_t^{(t)} = 1`. -/
theorem zeroPrice_zero {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hQ : ZeroPrice 𝔼 m P Q)
    {t : ℕ} (hP0 : ∀ ξ, P t ξ ≠ 0) : Q t 0 = 1 := by
  rw [hQ t 0, sdf_zero, one_mul]
  have h : (fun ξ => P t ξ / P (t + 0) ξ) = fun _ => (1 : ℝ) := by
    funext ξ
    simp [hP0 ξ]
  rw [h, 𝔼.const]
  rfl

/-- Cochrane (2023), eq. (3.1), p. 53: real bond prices are nonnegative when discount factors
are nonnegative and the price level is positive. -/
theorem realPrice_nonneg {m P : ℕ → Ω → ℝ} (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hPpos : ∀ s ξ, 0 < P s ξ) (t j : ℕ) (ξ : Ω) : 0 ≤ realPrice 𝔼 m P t j ξ :=
  E_nonneg 𝔼 (fun ξ' => mul_nonneg (sdf_nonneg hm0 t j ξ')
    (inv_nonneg.mpr (hPpos (t + j) ξ').le)) ξ

/-- Cochrane (2023), eq. (3.1), p. 53 (tower property and pull-out): real bond prices obey
the recursion `Q_t^{(t+j+1)}/P_t = E_t[(Λ_{t+1}/Λ_t) Q_{t+1}^{(t+j+1)}/P_{t+1}]`. -/
theorem realPrice_succ (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (P : ℕ → Ω → ℝ) (t j : ℕ) :
    realPrice 𝔼 m P t (j + 1) = 𝔼.E t (m t * realPrice 𝔼 m P (t + 1) j) := by
  rw [realPrice, realPrice, ← hP (t + 1) (m t) _ (hm t), 𝔼.tower (Nat.le_succ t), sdf_succ',
    mul_assoc]
  congr 3
  funext ξ
  rw [show t + (j + 1) = t + 1 + j by omega]

/-- Cochrane (2023), eq. (3.1), p. 53: the recursive form of bond pricing,
`Q_t^{(t+j+1)} = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1}) Q_{t+1}^{(t+j+1)}]` (with `m ≡ β`:
`Q_t^{(t+j+1)} = βE_t[(P_t/P_{t+1})Q_{t+1}^{(t+j+1)}]`). -/
theorem zeroPrice_recursive (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t j : ℕ) :
    Q t (j + 1) = 𝔼.E t (m t * (fun ξ => P t ξ / P (t + 1) ξ) * Q (t + 1) j) := by
  rw [zeroPrice_eq_mul 𝔼 hP hQ (hPa t), realPrice_succ 𝔼 hP hm, ← hP t (P t) _ (hPa t)]
  congr 1
  funext ξ
  rw [zeroPrice_eq_mul 𝔼 hP hQ (hPa (t + 1)) j]
  have := hP0 (t + 1) ξ
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), eq. (3.1), p. 53, under perfect foresight: the term structure is the
product of one-period prices, `Q_t^{(t+j)} = ∏_{k<j} Q_{t+k}^{(t+k+1)}`. -/
theorem zeroPrice_pf_prod {m P : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0) (t j : ℕ) :
    Q t j = ∏ k ∈ Finset.range j, Q (t + k) 1 := by
  induction j with
  | zero =>
    rw [zeroPrice_zero perfectForesight hQ (hP0 t), Finset.prod_range_zero]
  | succ j ih =>
    rw [Finset.prod_range_succ, ← ih]
    funext ξ
    have h1 := congrFun (hQ t (j + 1)) ξ
    have h2 := congrFun (hQ t j) ξ
    have h3 := congrFun (hQ (t + j) 1) ξ
    simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_one] at h1 h2 h3
    rw [Pi.mul_apply, h1, h2, h3, sdf_succ, Pi.mul_apply]
    have := hP0 (t + j) ξ
    rw [show t + (j + 1) = t + j + 1 by omega]
    field_simp

/-- Cochrane (2023), p. 56 and eq. (3.1), p. 53, under perfect foresight: with the one-period
interest rate defined by `Q_t^{(t+1)} = 1/(1+i_t)`, `Q_t^{(t+j)} = ∏_{k<j} 1/(1+i_{t+k})`. -/
theorem zeroPrice_pf_rates {m P i : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hi : ∀ s, Q s 1 = fun ξ => (1 + i s ξ)⁻¹) (t j : ℕ) :
    Q t j = fun ξ => ∏ k ∈ Finset.range j, (1 + i (t + k) ξ)⁻¹ := by
  rw [zeroPrice_pf_prod hQ hP0 t j]
  funext ξ
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun k _ => by rw [hi]

/-- Cochrane (2023), p. 53 ("this event means future inflation rather than current
inflation"): under perfect foresight with `m ≡ β > 0`, a bond price below `βʲ` is the same
thing as a price level that rises between `t` and `t + j`. -/
theorem zeroPrice_lt_iff_inflation {β : ℝ} (hβ : 0 < β) {P : ℕ → Unit → ℝ}
    {Q : ℕ → ℕ → Unit → ℝ} (hQ : ZeroPrice perfectForesight (fun _ _ => β) P Q)
    (hPpos : ∀ s ξ, 0 < P s ξ) (t j : ℕ) (ξ : Unit) :
    Q t j ξ < β ^ j ↔ P t ξ < P (t + j) ξ := by
  have h := congrFun (hQ t j) ξ
  simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_const] at h
  rw [h, mul_lt_iff_lt_one_right (pow_pos hβ j), div_lt_one (hPpos _ ξ)]

/-! ### Long-term debt with a finite maximum maturity: (3.2)–(3.3) -/

/-- Cochrane (2023), §3.1, p. 53: no bonds of maturity beyond `K` periods are outstanding,
`B_{t−1}^{(t+j)} = 0` for `j > K` (survey E29: the base case, in which every sum over
maturities is finite). -/
def MaxMaturity (K : ℕ) (B : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, K < j → B t j = 0

/-- Cochrane (2023), eq. (3.2), p. 53: the flow condition with long-term debt,
`B_{t−1}^{(t)} = P_ts_t + ∑_{j≥1} Q_t^{(t+j)}(B_t^{(t+j)} − B_{t−1}^{(t+j)})`, where
`B_t^{(t+j)} = B (t+1) (j−1)`; with maximum maturity `K` the sum runs over `j = 1, …, K+1`. -/
def FlowLT (K : ℕ) (P s : ℕ → Ω → ℝ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  B t 0 = P t * s t + ∑ j ∈ Finset.range (K + 1), Q t (j + 1) * (B (t + 1) j - B t (j + 1))

/-- Cochrane (2023), eq. (3.3), p. 53: the nominal market value
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` of the debt outstanding at the start of date `t`. -/
def mktValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (K + 1), Q t j * B t j

/-- Cochrane (2023), eq. (3.2), p. 53: the date-`t` nominal value
`∑_{j≥1} Q_t^{(t+j)} B_t^{(t+j)}` of the debt carried into date `t + 1`. -/
def purchaseValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (K + 1), Q t (j + 1) * B (t + 1) j

/-- Cochrane (2023), eq. (3.3), p. 53: the real market value of the debt,
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}/P_t`. -/
noncomputable def realValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ξ => mktValue K Q B t ξ / P t ξ

/-- Cochrane (2023), eq. (3.2), p. 53, rearranged (exact algebra, no pricing assumption beyond
`Q_t^{(t)} = 1`): the flow condition holds iff the real market value of the debt equals the
surplus plus the real value of the debt carried forward. -/
theorem flowLT_iff_value {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) {t : ℕ} (hQ0 : Q t 0 = 1) (hP0 : ∀ ξ, P t ξ ≠ 0) :
    FlowLT K P s Q B t ↔
      realValue K Q B P t = s t + fun ξ => purchaseValue K Q B t ξ / P t ξ := by
  have hsplit : ∀ ξ, mktValue K Q B t ξ =
      B t 0 ξ + ∑ j ∈ Finset.range (K + 1), Q t (j + 1) ξ * B t (j + 1) ξ := by
    intro ξ
    simp only [mktValue, Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_range_succ', Finset.sum_range_succ (fun j => Q t (j + 1) ξ * B t (j + 1) ξ),
      hK t (K + 1) (by omega), hQ0]
    simp only [Pi.one_apply, Pi.zero_apply, mul_zero, add_zero, one_mul]
    ring
  have hflow : FlowLT K P s Q B t ↔ ∀ ξ, B t 0 ξ = P t ξ * s t ξ +
      (purchaseValue K Q B t ξ - ∑ j ∈ Finset.range (K + 1), Q t (j + 1) ξ * B t (j + 1) ξ) := by
    constructor
    · intro h ξ
      have h1 := congrFun h ξ
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Pi.sub_apply] at h1
      rw [h1, purchaseValue, Finset.sum_apply, ← Finset.sum_sub_distrib]
      simp only [Pi.mul_apply, mul_sub]
    · intro h
      funext ξ
      have h1 := h ξ
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Pi.sub_apply]
      rw [h1, purchaseValue, Finset.sum_apply, ← Finset.sum_sub_distrib]
      simp only [Pi.mul_apply, mul_sub]
  rw [hflow]
  constructor
  · intro h
    funext ξ
    have h1 := h ξ
    have h2 := hsplit ξ
    have := hP0 ξ
    simp only [realValue, Pi.add_apply]
    field_simp
    linarith
  · intro h ξ
    have h1 := congrFun h ξ
    have h2 := hsplit ξ
    have := hP0 ξ
    simp only [realValue, Pi.add_apply] at h1
    field_simp at h1
    linarith

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53: given bond pricing (3.1), the real value of the
debt carried into `t + 1` is `E_t[(Λ_{t+1}/Λ_t) × (real market value at t + 1)]`. -/
theorem purchaseValue_real (hP : 𝔼.PullOut) {K : ℕ} {m P : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hQ : ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) {t : ℕ}
    (hB1 : ∀ j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    (fun ξ => purchaseValue K Q B t ξ / P t ξ) =
      𝔼.E t (m t * realValue K Q B P (t + 1)) := by
  have hfun : m t * realValue K Q B P (t + 1) =
      ∑ j ∈ Finset.range (K + 1), B (t + 1) j * (m t * realPrice 𝔼 m P (t + 1) j) := by
    funext ξ
    simp only [Pi.mul_apply, realValue, mktValue, Finset.sum_apply, Finset.sum_div,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← zeroPrice_real 𝔼 hP hQ (hPa (t + 1)) j (hP0 (t + 1) ξ)]
    ring
  rw [hfun, map_sum]
  funext ξ
  simp only [purchaseValue, Finset.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP t _ _ (hB1 j), ← realPrice_succ 𝔼 hP hm, Pi.mul_apply, Pi.mul_apply,
    ← zeroPrice_real 𝔼 hP hQ (hPa t) (j + 1) (hP0 t ξ)]
  ring

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53: given bond pricing (3.1), the flow condition
(3.2) at date `t` is equivalent to the real recursion
`v_t = s_t + E_t[(Λ_{t+1}/Λ_t)v_{t+1}]` for the real market value `v` of the debt. -/
theorem flowLT_iff_recursion (hP : 𝔼.PullOut) {K : ℕ} {m P s : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hK : MaxMaturity K B)
    (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) {t : ℕ}
    (hB1 : ∀ j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    FlowLT K P s Q B t ↔
      realValue K Q B P t = s t + 𝔼.E t (m t * realValue K Q B P (t + 1)) := by
  rw [flowLT_iff_value hK (zeroPrice_zero 𝔼 hQ (hP0 t)) (hP0 t),
    purchaseValue_real 𝔼 hP hm hQ hPa hP0 hB1]

/-- Cochrane (2023), eq. (3.3), p. 53: given (3.1), the real market value of debt is known at
its date when the holdings `B_{t−1}^{(t+j)}` are. -/
theorem realValue_adapted (hP : 𝔼.PullOut) {K : ℕ} {m P : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j) :
    𝔼.Adapted (realValue K Q B P) := by
  intro t
  have hfun : realValue K Q B P t =
      ∑ j ∈ Finset.range (K + 1), B t j * realPrice 𝔼 m P t j := by
    funext ξ
    simp only [realValue, mktValue, Finset.sum_apply, Finset.sum_div, Pi.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← zeroPrice_real 𝔼 hP hQ (hPa t) j (hP0 t ξ)]
    ring
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP t _ _ (hBt t j), realPrice, 𝔼.E_E_self]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, and survey E28–E29: with a finite maximum
maturity, bond prices given by (3.1), a positive adapted price level, holdings known when
chosen, adapted surpluses with absolutely summable present values, and `E_t` with pull-out and
conditional monotone convergence, the flow condition (3.2) at every date plus the
transversality condition at every date hold iff the valuation equation (3.3)
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` holds at every date. -/
theorem valuationLT_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {K : ℕ}
    {m P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s) (hs : SurplusSummable 𝔼 m s)
    (hK : MaxMaturity K B) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j)
    (hB1 : ∀ t j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    ((∀ t, FlowLT K P s Q B t) ∧ ∀ t, TVC 𝔼 m (realValue K Q B P) t) ↔
      ∀ t, realValue K Q B P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs (realValue_adapted 𝔼 hP hQ hPa hP0 hBt)]
  have h : (∀ t, FlowLT K P s Q B t) ↔ FlowRec 𝔼 m s (realValue K Q B P) :=
    forall_congr' fun t => flowLT_iff_recursion 𝔼 hP hm hK hQ hPa hP0 (hB1 t)
  rw [h]

/-- Cochrane (2023), eq. (3.3), p. 53: with `m ≡ β` the present value is
`∑_n βⁿ E_t s_{t+n}`. -/
theorem pv_const (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pv 𝔼 (fun _ _ => β) s t = fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  funext ξ
  simp only [pv, sdf_const]
  refine tsum_congr fun n => ?_
  have h : ((fun _ => β ^ n) * s (t + n) : Ω → ℝ) = β ^ n • s (t + n) := by
    funext ξ'
    simp
  rw [h, map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, exactly as printed (constant real rate,
`R = β⁻¹`, `0 ≤ β`): with a finite maximum maturity, (3.1) `Q_t^{(t+j)} = E_t[βʲP_t/P_{t+j}]`,
the flow (3.2) at every date and the transversality condition
`lim_N βᴺ E_t[v_{t+N}] = 0` at every date hold iff (3.3)
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_n βⁿE_t s_{t+n}` at every date. -/
theorem valuationLT_iff_const (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {K : ℕ}
    {β : ℝ} (hβ : 0 ≤ β) {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 (fun _ _ => β) s) (hK : MaxMaturity K B)
    (hQ : ∀ t j, Q t j = 𝔼.E t (fun ξ => β ^ j * (P t ξ / P (t + j) ξ)))
    (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j)
    (hB1 : ∀ t j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    ((∀ t, FlowLT K P s Q B t) ∧
        ∀ t ξ, Tendsto (fun N => β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ) atTop (𝓝 0)) ↔
      ∀ t ξ, realValue K Q B P t ξ = ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  have hiff := valuationLT_iff 𝔼 hMC hP (m := fun _ _ => β) (fun s => 𝔼.const (s + 1) β)
    (fun _ _ => hβ) hsa hs hK ((zeroPrice_const_iff 𝔼 β P Q).mpr hQ) hPa hP0 hBt hB1
  have htvc : ∀ t, TVC 𝔼 (fun _ _ => β) (realValue K Q B P) t ↔
      ∀ ξ, Tendsto (fun N => β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ) atTop (𝓝 0) := by
    intro t
    refine forall_congr' fun ξ => ?_
    have h : ∀ N, 𝔼.E t (sdf (fun _ _ => β) t N * realValue K Q B P (t + N)) ξ =
        β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ := fun N => by
      have h' : (sdf (fun _ _ => β) t N * realValue K Q B P (t + N) : Ω → ℝ) =
          β ^ N • realValue K Q B P (t + N) := by
        rw [sdf_const]
        funext ξ'
        simp
      rw [h', map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [h]
  simp_rw [← htvc, hiff, pv_const, funext_iff]

/-- Cochrane (2023), p. 53 (survey E28): "we can derive (3.2) from (3.3) by considering its
value at two adjacent dates" is false without the bond-pricing equation (3.1). Under perfect
foresight with `β = 1/2`, `P ≡ 1`, `s ≡ 1`, maximum maturity one, `B_{t−1}^{(t)} = 0`,
`B_{t−1}^{(t+1)} = 1`, and the price `Q_t^{(t+1)} = 2` (instead of `β = 1/2`), the valuation
equation (3.3) and the transversality condition hold at every date while the flow condition
(3.2) fails at every date. -/
theorem valuationLT_not_imp_flow :
    ∃ (P s : ℕ → Unit → ℝ) (Q B : ℕ → ℕ → Unit → ℝ),
      MaxMaturity 1 B ∧
      (∀ t, realValue 1 Q B P t = pv perfectForesight (fun _ _ => (1 / 2 : ℝ)) s t) ∧
      (∀ t, TVC perfectForesight (fun _ _ => (1 / 2 : ℝ)) (realValue 1 Q B P) t) ∧
      (∀ t, ¬ FlowLT 1 P s Q B t) ∧
      ¬ ZeroPrice perfectForesight (fun _ _ => (1 / 2 : ℝ)) P Q := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ j _ => if j = 1 then 2 else (1 / 2) ^ j,
    fun _ j _ => if j = 1 then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t j hj
    funext ξ
    simp only [show j ≠ 1 by omega, ↓reduceIte]
    rfl
  · intro t
    funext ξ
    rw [pv_const]
    simp only [realValue, mktValue, perfectForesight, LinearMap.id_apply, mul_one]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    simp
    norm_num
  · intro t ξ
    have h : ∀ N, perfectForesight.E t (sdf (fun _ _ => (1 / 2 : ℝ)) t N *
        realValue 1 (fun _ j _ => if j = 1 then 2 else (1 / 2) ^ j)
          (fun _ j _ => if j = 1 then 1 else 0) (fun _ _ => 1) (t + N)) ξ =
        2 * (1 / 2) ^ N := fun N => by
      simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_const, realValue,
        mktValue]
      simp
      ring
    simp_rw [h]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
  · intro t h
    have h1 := congrFun h ()
    simp [Finset.sum_range_succ] at h1
    norm_num at h1
  · intro h
    have h1 := congrFun (h 0 1) ()
    simp [perfectForesight] at h1
    norm_num at h1


/-! ### Geometric maturity structure (A1 §1.2.1) with genuine infinite sums -/

/-- Cochrane (2023), A1 §1.2.1, p. 559: the geometric maturity structure
`B_{t−1}^{(t+j)} = ωʲ b_t` (written `w` here, since `ω` names states), with `b_t = B_{t−1}`. -/
def geomDebt (w : ℝ) (b : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ := fun t j ξ => w ^ j * b t ξ

/-- Cochrane (2023), eq. (3.2), p. 53, with the geometric structure of A1 p. 559:
`b_t = P_ts_t + ∑_{j≥0} Q_t^{(t+j+1)}(ωʲ b_{t+1} − ω^{j+1} b_t)`. -/
def GeomFlow (w : ℝ) (P s b : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ξ, b t ξ = P t ξ * s t ξ +
    ∑' j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ)

/-- Cochrane (2023), A1 eq. (1.14), p. 559: the nominal value `∑_j ωʲ Q_t^{(t+j)}` of the
geometric portfolio per unit of `b_t`. -/
noncomputable def annuity (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => ∑' j, w ^ j * Q t j ξ

/-- Cochrane (2023), eq. (3.3), p. 53, with the geometric structure: the real market value
`∑_j Q_t^{(t+j)} ωʲ b_t/P_t` of the debt. -/
noncomputable def geomValue (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (b P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => annuity w Q t ξ * b t ξ / P t ξ

/-- Cochrane (2023), eq. (3.3), p. 53: the geometric real market value is
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t` with `B_{t−1}^{(t+j)} = ωʲb_t`. -/
theorem geomValue_eq_tsum (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (b P : ℕ → Ω → ℝ) (t : ℕ) (ξ : Ω) :
    geomValue w Q b P t ξ = (∑' j, Q t j ξ * geomDebt w b t j ξ) / P t ξ := by
  simp only [geomValue, annuity, geomDebt]
  rw [← tsum_mul_right]
  congr 1
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), A1 eq. (1.14), p. 559: the real value `∑_j ωʲ Q_t^{(t+j)}/P_t` of the
geometric portfolio per unit of `b_t`. -/
noncomputable def realAnnuity (w : ℝ) (m P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => ∑' j, w ^ j * realPrice 𝔼 m P t j ξ

/-- Cochrane (2023), eq. (3.1), p. 53, and A1 p. 559: with (3.1), the nominal annuity value
divided by `P_t` is the real annuity value. -/
theorem annuity_div (hP : 𝔼.PullOut) {w : ℝ} {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) {ξ : Ω} (hP0 : P t ξ ≠ 0) :
    annuity w Q t ξ / P t ξ = realAnnuity 𝔼 w m P t ξ := by
  simp only [annuity, realAnnuity]
  rw [← tsum_div_const]
  exact tsum_congr fun j => by
    rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ hPa j hP0]

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53, geometric case (conditional monotone
convergence): the nominal value of the debt carried into `t + 1` per unit of `b_{t+1}`,
`∑_j ωʲ Q_t^{(t+j+1)}`, converges to `P_t E_t[(Λ_{t+1}/Λ_t) × (real annuity at t + 1)]`. -/
theorem hasSum_shift (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ} (hw : 0 ≤ w)
    {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hPpos : ∀ s ξ, 0 < P s ξ) (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ)
    (t : ℕ) (ξ : Ω) :
    HasSum (fun j => w ^ j * Q t (j + 1) ξ)
      (P t ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ) := by
  set f : ℕ → Ω → ℝ := fun j => m t * fun ξ' => w ^ j * realPrice 𝔼 m P (t + 1) j ξ' with hf
  have hf0 : ∀ j ξ', 0 ≤ f j ξ' := fun j ξ' =>
    mul_nonneg (hm0 t ξ') (mul_nonneg (pow_nonneg hw j)
      (realPrice_nonneg 𝔼 hm0 hPpos (t + 1) j ξ'))
  have hrp : ∀ ξ' j, w ^ j * realPrice 𝔼 m P (t + 1) j ξ' =
      w ^ j * Q (t + 1) j ξ' / P (t + 1) ξ' := fun ξ' j => by
    rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ (hPa (t + 1)) j (hPpos (t + 1) ξ').ne']
  have hfs : ∀ ξ', Summable fun j => f j ξ' := fun ξ' => by
    have h := ((hQs (t + 1) ξ').div_const (P (t + 1) ξ')).mul_left (m t ξ')
    refine h.congr fun j => ?_
    simp only [hf, Pi.mul_apply, hrp]
  have hMCf := hMC t f hf0 hfs ξ
  have hsum : (fun ξ' => ∑' j, f j ξ') = m t * realAnnuity 𝔼 w m P (t + 1) := by
    funext ξ'
    simp only [hf, Pi.mul_apply, realAnnuity, tsum_mul_left]
  rw [hsum] at hMCf
  have hterm : ∀ j, 𝔼.E t (f j) ξ = w ^ j * Q t (j + 1) ξ / P t ξ := fun j => by
    have h' : f j = w ^ j • (m t * realPrice 𝔼 m P (t + 1) j) := by
      funext ξ'
      simp only [hf, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h', map_smul, ← realPrice_succ 𝔼 hP hm, Pi.smul_apply, smul_eq_mul,
      ← zeroPrice_real 𝔼 hP hQ (hPa t) (j + 1) (hPpos t ξ).ne']
    ring
  simp_rw [hterm] at hMCf
  convert hMCf.mul_left (P t ξ) using 1
  funext j
  have := (hPpos t ξ).ne'
  field_simp

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53, with the geometric maturity structure of A1
p. 559: given (3.1), the flow condition at date `t` is equivalent to the real recursion
`v_t = s_t + E_t[(Λ_{t+1}/Λ_t)v_{t+1}]` for the real market value of the debt. -/
theorem geomFlow_iff_recursion (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hQ : ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ) {t : ℕ}
    (hb1 : 𝔼.E t (b (t + 1)) = b (t + 1)) :
    GeomFlow w P s b Q t ↔
      geomValue w Q b P t = s t + 𝔼.E t (m t * geomValue w Q b P (t + 1)) := by
  have hE : 𝔼.E t (m t * geomValue w Q b P (t + 1)) =
      b (t + 1) * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) := by
    rw [← hP t _ _ hb1]
    congr 1
    funext ξ
    simp only [Pi.mul_apply, geomValue]
    rw [mul_div_right_comm, annuity_div 𝔼 hP hQ (hPa (t + 1)) (hPpos (t + 1) ξ).ne']
    ring
  rw [hE]
  have key : ∀ ξ, (b t ξ = P t ξ * s t ξ +
      ∑' j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ)) ↔
      geomValue w Q b P t ξ =
        s t ξ + b (t + 1) ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ := by
    intro ξ
    set S := P t ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ with hS
    have hsh := hasSum_shift 𝔼 hMC hP hw hm hm0 hQ hPa hPpos hQs t ξ
    have h1 : HasSum (fun j => Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ))
        (b (t + 1) ξ * S - w * b t ξ * S) := by
      convert (hsh.mul_left (b (t + 1) ξ)).sub (hsh.mul_left (w * b t ξ)) using 1
      funext j
      ring
    have hann : annuity w Q t ξ = 1 + w * S := by
      simp only [annuity]
      rw [(hQs t ξ).tsum_eq_zero_add, zeroPrice_zero 𝔼 hQ (fun ξ' => (hPpos t ξ').ne'),
        show S = ∑' j, w ^ j * Q t (j + 1) ξ from hsh.tsum_eq.symm, ← tsum_mul_left]
      simp only [pow_zero, Pi.one_apply, one_mul]
      congr 1
      exact tsum_congr fun j => by ring
    have hP0 := (hPpos t ξ).ne'
    rw [h1.tsum_eq, geomValue, hann, hS]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      field_simp at h
      linear_combination h
  constructor
  · intro h
    funext ξ
    exact (key ξ).mp (h ξ)
  · intro h ξ
    exact (key ξ).mpr (congrFun h ξ)

/-- Cochrane (2023), eq. (3.3), p. 53, geometric case: the real market value of the debt is
known at its date when `b_t` is. -/
theorem geomValue_adapted (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ) (hb : 𝔼.Adapted b) :
    𝔼.Adapted (geomValue w Q b P) := by
  intro t
  have hfun : geomValue w Q b P t = b t * realAnnuity 𝔼 w m P t := by
    funext ξ
    simp only [geomValue, Pi.mul_apply]
    rw [mul_div_right_comm, annuity_div 𝔼 hP hQ (hPa t) (hPpos t ξ).ne', mul_comm]
  have hA : 𝔼.E t (realAnnuity 𝔼 w m P t) = realAnnuity 𝔼 w m P t := by
    set g : ℕ → Ω → ℝ := fun j ξ => w ^ j * realPrice 𝔼 m P t j ξ with hg
    have hg0 : ∀ j ξ, 0 ≤ g j ξ := fun j ξ =>
      mul_nonneg (pow_nonneg hw j) (realPrice_nonneg 𝔼 hm0 hPpos t j ξ)
    have hgs : ∀ ξ, Summable fun j => g j ξ := fun ξ => by
      refine ((hQs t ξ).div_const (P t ξ)).congr fun j => ?_
      simp only [hg]
      rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ (hPa t) j (hPpos t ξ).ne']
    funext ξ
    have h := hMC t g hg0 hgs ξ
    have hEg : ∀ j, 𝔼.E t (g j) ξ = g j ξ := fun j => by
      have h' : g j = w ^ j • realPrice 𝔼 m P t j := by
        funext ξ'
        simp [hg]
      rw [h', map_smul, realPrice, 𝔼.E_E_self]
    simp_rw [hEg] at h
    exact h.tsum_eq.symm
  rw [hfun, hP t _ _ (hb t), hA]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, with the geometric maturity structure of A1
§1.2.1 (genuine infinite sums over maturities): given (3.1), the flow condition at every date
plus the transversality condition at every date hold iff the valuation equation
`∑_j Q_t^{(t+j)}ωʲb_t/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` holds at every date. -/
theorem valuationGeom_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hPpos : ∀ s ξ, 0 < P s ξ) (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ)
    (hb : 𝔼.Adapted b) (hb1 : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) :
    ((∀ t, GeomFlow w P s b Q t) ∧ ∀ t, TVC 𝔼 m (geomValue w Q b P) t) ↔
      ∀ t, geomValue w Q b P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs
    (geomValue_adapted 𝔼 hMC hP hw hm0 hQ hPa hPpos hQs hb)]
  have h : (∀ t, GeomFlow w P s b Q t) ↔ FlowRec 𝔼 m s (geomValue w Q b P) :=
    forall_congr' fun t => geomFlow_iff_recursion 𝔼 hMC hP hw hm hm0 hQ hPa hPpos hQs (hb1 t)
  rw [h]


/-! ### A1 §1.2.1: exact formulas for one-time interest-rate changes -/

/-- Cochrane (2023), A1 p. 559 ("the bond price is then `Q_t^{(t+j)} = 1/(1+i)ʲ`"): under
perfect foresight with (3.1) and a constant one-period rate `i`, the term structure is flat,
`Q_t^{(t+j)} = 1/(1+i)ʲ`. -/
theorem zeroPrice_pf_const_rate {m P : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ} {i : ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hi : ∀ s, Q s 1 = fun _ => (1 + i)⁻¹) (t j : ℕ) : Q t j = fun _ => ((1 + i) ^ j)⁻¹ := by
  rw [zeroPrice_pf_rates hQ hP0 (i := fun _ _ => i) hi t j]
  funext ξ
  rw [Finset.prod_const, Finset.card_range, inv_pow]

/-- Cochrane (2023), A1 (1.14), p. 559: for `0 ≤ ω < 1 + i`,
`∑_j ωʲ/(1+i)ʲ = (1+i)/(1+i−ω)`. -/
theorem geom_value {i w : ℝ} (hw : 0 ≤ w) (hwi : w < 1 + i) :
    HasSum (fun j : ℕ => w ^ j / (1 + i) ^ j) ((1 + i) / (1 + i - w)) := by
  have h1 : 0 < 1 + i := by linarith
  have h := hasSum_geometric_of_lt_one (div_nonneg hw h1.le) ((div_lt_one h1).mpr hwi)
  rw [one_sub_div h1.ne', inv_div] at h
  convert h using 1
  funext j
  rw [div_pow]

/-- Cochrane (2023), A1 (1.14), p. 559, right-hand side: with constant surpluses and
`β = 1/(1+r)`, `r > 0`, the present value is `∑_j βʲ s = (1+r)s/r`. -/
theorem pv_const_value {r : ℝ} (hr : 0 < r) (s : ℝ) :
    HasSum (fun j : ℕ => (1 / (1 + r)) ^ j * s) ((1 + r) / r * s) := by
  have h1 : 0 < 1 + r := by linarith
  have h := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ 1 / (1 + r))
    ((div_lt_one h1).mpr (by linarith))).mul_right s
  have hq : (1 - 1 / (1 + r))⁻¹ = (1 + r) / r := by
    rw [one_sub_div h1.ne', inv_div, add_sub_cancel_left]
  rwa [hq] at h

/-- Cochrane (2023), A1 eq. (1.14), p. 559: with a constant rate `i` (`Q_0^{(j)} = 1/(1+i)ʲ`),
geometric debt `B_{−1}^{(j)} = ωʲB_{−1}` and constant surpluses, the valuation equation
`∑_j Q_0^{(j)}ωʲB_{−1}/P_0 = ∑_j βʲ s`, `β = 1/(1+r)`, reads
`(1+i)/(1+i−ω) · B_{−1}/P_0 = (1+r)s/r`. -/
theorem valuation_1_14 {r i w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwi : w < 1 + i)
    (Bm P0 s : ℝ) :
    (∑' j : ℕ, ((1 + i) ^ j)⁻¹ * (w ^ j * Bm) / P0 = ∑' j : ℕ, (1 / (1 + r)) ^ j * s) ↔
      (1 + i) / (1 + i - w) * (Bm / P0) = (1 + r) / r * s := by
  rw [(pv_const_value hr s).tsum_eq]
  have h := ((geom_value hw hwi).mul_right (Bm / P0)).tsum_eq
  rw [← h]
  constructor <;> intro hh <;> rw [← hh] <;> exact tsum_congr fun j => by ring

/-- Cochrane (2023), A1 eq. (1.15), p. 559: in the steady state with `i = r`,
`(1+r)/(1+r−ω) · B/P = (1+r)s/r` iff `B/P = (1+r−ω)s/r`. -/
theorem steady_state_1_15 {r w : ℝ} (hr : 0 < r) (hwr : w < 1 + r) (B P s : ℝ) :
    (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s ↔ B / P = (1 + r - w) * s / r := by
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + r) ≠ 0 := by linarith
  constructor
  · intro h
    have e : B / P = (1 + r - w) / (1 + r) * ((1 + r) / (1 + r - w) * (B / P)) := by
      field_simp
    rw [e, h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), A1 eq. (1.16), p. 559: the price-level ratio
`P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))` after a permanent unexpected rate rise from `r` to
`i`. -/
noncomputable def jumpRatio (r i w : ℝ) : ℝ := (1 + i) * (1 + r - w) / ((1 + r) * (1 + i - w))

/-- Cochrane (2023), A1 eqs. (1.14)–(1.16), p. 559: if the steady-state valuation (1.15) held
at `P` and the valuation (1.14) at the new rate `i` holds at `P_0` (same `B`, same constant
surplus `s ≠ 0`), then `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))`. -/
theorem price_jump_perm {r i w B P P0 s : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwr : w < 1 + r)
    (hwi : w < 1 + i) (hs : s ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (h14 : (1 + i) / (1 + i - w) * (B / P0) = (1 + r) / r * s)
    (h15 : (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s) :
    P0 / P = jumpRatio r i w := by
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have h3 : (1 + r) ≠ 0 := by linarith
  have hr0 : r ≠ 0 := hr.ne'
  have e15 : B / P = (1 + r - w) * s / r := (steady_state_1_15 hr hwr B P s).mp h15
  have e14 : B / P0 = (1 + r) * (1 + i - w) * s / ((1 + i) * r) := by
    have hi0 : (1 + i) ≠ 0 := by linarith
    have e : B / P0 = (1 + i - w) / (1 + i) * ((1 + i) / (1 + i - w) * (B / P0)) := by
      field_simp
    rw [e, h14]
    field_simp
  have hB : B ≠ 0 := by
    rintro rfl
    rw [zero_div, eq_comm, div_eq_zero_iff] at e15
    rcases e15 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h1 h'
      · exact hs h'
    · exact hr0 h
  have hratio : P0 / P = (B / P) / (B / P0) := by field_simp
  have hi0 : (1 + i) ≠ 0 := by linarith
  rw [hratio, e15, e14, jumpRatio]
  field_simp

/-- Cochrane (2023), A1 (1.14)–(1.16), p. 559, general form (no sign conditions; any common
right-hand side `s`, e.g. the present value of surpluses): the valuation equations before
((1.15)) and after ((1.14)) the permanent rise, with the same debt, give `P_0/P = jumpRatio`.
`price_jump_perm` is the case `s = (1+r)s₀/r`. -/
theorem price_jump_of_valuation {r i w B P P0 s : ℝ} (hB : B ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (hr : 1 + r ≠ 0) (hri : 1 + r - w ≠ 0) (hii : 1 + i - w ≠ 0)
    (h14 : (1 + i) / (1 + i - w) * (B / P0) = s) (h15 : (1 + r) / (1 + r - w) * (B / P) = s) :
    P0 / P = jumpRatio r i w := by
  rw [← h15] at h14
  unfold jumpRatio
  field_simp at h14 ⊢
  linear_combination -h14

/-- Cochrane (2023), A1 eq. (1.16), p. 559: `P_0/P − 1 = −ω(i−r)/((1+r)(1+i−ω))`. -/
theorem jumpRatio_sub_one {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) :
    jumpRatio r i w - 1 = -(w * (i - r) / ((1 + r) * (1 + i - w))) := by
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have h3 : (1 + r) ≠ 0 := by linarith
  unfold jumpRatio
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.16), p. 559, and §3.1, p. 53 ("a rise in nominal interest rates
with no change in surpluses … can result in a lower price level"): for `0 ≤ ω < 1 + r` and
`ω < 1 + i`, the price level jumps down, `P_0 < P`, iff the rate rises (`i > r`) and there is
long-term debt (`ω > 0`). -/
theorem price_jump_lt_one_iff {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) :
    jumpRatio r i w < 1 ↔ 0 < w ∧ r < i := by
  rw [← sub_neg, jumpRatio_sub_one hw hwr hwi, neg_neg_iff_pos]
  have hd : 0 < (1 + r) * (1 + i - w) := mul_pos (by linarith) (by linarith)
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    rcases hw.lt_or_eq with hw' | hw'
    · exact ⟨hw', by nlinarith⟩
    · rw [← hw'] at h
      simp at h
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 (by linarith)

/-- Cochrane (2023), A1 p. 560: with one-period debt (`ω = 0`) there is no jump, `P_0 = P`. -/
theorem price_jump_omega_zero {r i : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) :
    jumpRatio r i 0 = 1 := by
  unfold jumpRatio
  rw [sub_zero, sub_zero, mul_comm (1 + i)]
  exact div_self (mul_ne_zero hr.ne' hi.ne')

/-- Cochrane (2023), A1 eq. (1.16), p. 559: with long-term debt a rate cut (`i < r`) raises
the price level, `P_0 > P`. -/
theorem price_jump_gt_one {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hwi : w < 1 + i)
    (hir : i < r) : 1 < jumpRatio r i w := by
  rw [← sub_pos, jumpRatio_sub_one hw.le hwr hwi, neg_pos]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hw (by linarith))
    (mul_pos (by linarith) (by linarith))

/-- Cochrane (2023), A1 eq. (1.16), p. 559: the jump is larger with longer debt: for `i > r`,
`P_0/P` is strictly decreasing in `ω` on `[0, 1 + r)`. -/
theorem jumpRatio_strictAntiOn_omega {r i : ℝ} (hr : 0 < 1 + r) (hir : r < i) :
    StrictAntiOn (fun w => jumpRatio r i w) (Set.Ico 0 (1 + r)) := by
  intro w1 hw1 w2 hw2 h12
  simp only
  have hw1i : w1 < 1 + i := by linarith [hw1.2]
  have hw2i : w2 < 1 + i := by linarith [hw2.2]
  rw [← sub_lt_sub_iff_right 1, jumpRatio_sub_one hw1.1 hw1.2 hw1i,
    jumpRatio_sub_one hw2.1 hw2.2 hw2i, neg_lt_neg_iff,
    div_lt_div_iff₀ (mul_pos hr (by linarith)) (mul_pos hr (by linarith))]
  have key : w2 * (i - r) * ((1 + r) * (1 + i - w1)) - w1 * (i - r) * ((1 + r) * (1 + i - w2)) =
      (i - r) * (1 + r) * (1 + i) * (w2 - w1) := by ring
  have hpos : 0 < (i - r) * (1 + r) * (1 + i) * (w2 - w1) :=
    mul_pos (mul_pos (mul_pos (by linarith) hr) (by linarith)) (by linarith)
  linarith

/-- Cochrane (2023), A1 eq. (1.19), p. 560: for a perpetuity (`ω = 1`),
`P_0 = (1+i)r/((1+r)i) · P`. -/
theorem price_jump_perpetuity (r i : ℝ) :
    jumpRatio r i 1 = (1 + i) * r / ((1 + r) * i) := by
  unfold jumpRatio
  ring_nf

/-- Cochrane (2023), A1 p. 560 ("a rise in interest rates from `r = 3%` to `i = 4%` occasions a
25% price level drop"): in discrete time, (1.19) gives `P_0/P = 78/103`, a drop of
`25/103 ≈ 24.27%`; the exact 25% is the continuous-time (1.20) value `r/i = 3/4`. -/
theorem perpetuity_example :
    jumpRatio 0.03 0.04 1 = 78 / 103 ∧ 1 - jumpRatio 0.03 0.04 1 = 25 / 103 ∧
      (0.2427 : ℝ) < 25 / 103 ∧ (25 / 103 : ℝ) < 0.2428 ∧ (1 : ℝ) - 0.03 / 0.04 = 0.25 := by
  unfold jumpRatio
  norm_num

/-- Cochrane (2023), A1 p. 560 ("with `ω = 0.8`, the permanent interest-rate rise graphed in
Figure 3.1 leads to a 3.5% price level drop"), survey E15: at the figure's rates `r = 2%`,
`i = 3%`, the exact (1.16) gives `P_0/P = 1133/1173`, a drop of `40/1173 ≈ 3.41%`, not 3.5%. -/
theorem omega_08_example :
    jumpRatio 0.02 0.03 0.8 = 1133 / 1173 ∧ 1 - jumpRatio 0.02 0.03 0.8 = 40 / 1173 ∧
      (0.0341 : ℝ) < 40 / 1173 ∧ (40 / 1173 : ℝ) < 0.0342 := by
  unfold jumpRatio
  norm_num

/-! ### Forward guidance (A1 p. 560) -/

/-- Cochrane (2023), A1 p. 560: zero-coupon prices when the rate is `r` before `T` and `i` from
`T` on: `Q_0^{(j)} = 1/(1+r)ʲ` for `j ≤ T` and `1/((1+r)^T(1+i)^{j−T})` for `j > T`. -/
noncomputable def fgPrice (r i : ℝ) (T j : ℕ) : ℝ :=
  if j ≤ T then ((1 + r) ^ j)⁻¹ else ((1 + r) ^ T)⁻¹ * ((1 + i) ^ (j - T))⁻¹

/-- Cochrane (2023), A1 p. 560: `fgPrice` is the term structure `∏_{k<j} 1/(1+i_k)` of the
announced path `i_k = r` for `k < T`, `i_k = i` for `k ≥ T` (cf. `zeroPrice_pf_rates`). -/
theorem fgPrice_eq_prod (r i : ℝ) (T j : ℕ) :
    fgPrice r i T j = ∏ k ∈ Finset.range j, (1 + if k < T then r else i)⁻¹ := by
  unfold fgPrice
  split_ifs with hj
  · rw [Finset.prod_congr rfl (g := fun _ => (1 + r)⁻¹) fun k hk => by
      rw [Finset.mem_range] at hk
      simp only [show k < T by omega, ↓reduceIte], Finset.prod_const, Finset.card_range,
      inv_pow]
  · obtain ⟨d, rfl⟩ : ∃ d, j = T + d := ⟨j - T, by omega⟩
    rw [Finset.prod_range_add, show T + d - T = d by omega]
    rw [Finset.prod_congr rfl (s₁ := Finset.range T) (g := fun _ => (1 + r)⁻¹) fun k hk => by
      rw [Finset.mem_range] at hk
      simp only [hk, ↓reduceIte], Finset.prod_const, Finset.card_range, inv_pow]
    rw [Finset.prod_congr rfl (s₁ := Finset.range d) (g := fun _ => (1 + i)⁻¹) fun k _ => by
      simp only [show ¬ T + k < T by omega, ↓reduceIte], Finset.prod_const, Finset.card_range,
      inv_pow]

/-- Cochrane (2023), A1 p. 560: the value of the geometric portfolio under forward guidance,
`∑_{j≤T} ωʲ/(1+r)ʲ + ∑_{j>T} ω^T/(1+r)^T · ω^{j−T}/(1+i)^{j−T}
= (1 − a^{T+1})/(1 − a) + a^T c/(1 − c)` with `a = ω/(1+r)`, `c = ω/(1+i)`. -/
theorem fg_value {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) (T : ℕ) :
    HasSum (fun j => w ^ j * fgPrice r i T j)
      ((1 - (w / (1 + r)) ^ (T + 1)) / (1 - w / (1 + r)) +
        (w / (1 + r)) ^ T * ((w / (1 + i)) / (1 - w / (1 + i)))) := by
  have hr1 : 0 < 1 + r := by linarith
  have hi1 : 0 < 1 + i := by linarith
  set a := w / (1 + r) with ha
  set c := w / (1 + i) with hc
  have ha1 : a < 1 := (div_lt_one hr1).mpr hwr
  have hc0 : 0 ≤ c := div_nonneg hw hi1.le
  have hc1 : c < 1 := (div_lt_one hi1).mpr hwi
  rw [← hasSum_nat_add_iff' (T + 1)]
  have hhead : ∑ j ∈ Finset.range (T + 1), w ^ j * fgPrice r i T j =
      (1 - a ^ (T + 1)) / (1 - a) := by
    have he : (1 - a ^ (T + 1)) / (1 - a) = (a ^ (T + 1) - 1) / (a - 1) := by
      rw [← neg_sub, ← neg_sub a, neg_div_neg_eq]
    rw [he, ← geom_sum_eq ha1.ne]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [fgPrice, show j ≤ T by omega, ↓reduceIte, ha, div_eq_mul_inv, mul_pow, inv_pow]
  rw [hhead, add_sub_cancel_left]
  have hgeo := ((hasSum_geometric_of_lt_one hc0 hc1).mul_left (a ^ T * c))
  convert hgeo using 1
  · funext k
    simp only [fgPrice, show ¬ k + (T + 1) ≤ T by omega, ↓reduceIte,
      show k + (T + 1) - T = k + 1 by omega, ha, hc, div_pow]
    field_simp
    ring
  · rw [mul_assoc, div_eq_mul_inv]

/-- Cochrane (2023), A1 p. 560 (forward-guidance display and "with a bit of algebra"): if the
steady-state valuation `(1+r)/(1+r−ω) · B/P = V` held and, after the announcement at `0` that
the rate rises from `r` to `i` at `T`, the valuation `(fg value) · B/P_0 = V` holds (same `B`,
`V ≠ 0`), then `P_0/P − 1 = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`, generalising
(1.16) (the case `T = 0`). -/
theorem price_jump_fg {r i w B P P0 V : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i)
    (T : ℕ) (hV : V ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (hfg : (∑' j, w ^ j * fgPrice r i T j) * (B / P0) = V)
    (hss : (1 + r) / (1 + r - w) * (B / P) = V) :
    P0 / P - 1 = (w / (1 + r)) ^ T * (jumpRatio r i w - 1) := by
  have hr1 : 0 < 1 + r := by linarith
  have hi1 : 0 < 1 + i := by linarith
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have hr0 : (1 + r) ≠ 0 := hr1.ne'
  have hi0 : (1 + i) ≠ 0 := hi1.ne'
  rw [(fg_value hw hwr hwi T).tsum_eq] at hfg
  set a := w / (1 + r) with ha
  set c := w / (1 + i) with hc
  have ha1 : 1 - a ≠ 0 := by
    rw [ha, one_sub_div hr0]; exact div_ne_zero h1 hr0
  have hc1 : 1 - c ≠ 0 := by
    rw [hc, one_sub_div hi0]; exact div_ne_zero h2 hi0
  set S := (1 - a ^ (T + 1)) / (1 - a) + a ^ T * (c / (1 - c)) with hS
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfg
    exact hV hfg.symm
  have hB : B ≠ 0 := by
    rintro rfl
    rw [zero_div, mul_zero] at hss
    exact hV hss.symm
  have hBP : B / P = V * (1 - a) := by
    rw [← hss, ha, one_sub_div hr0]
    field_simp
  have hBP0 : B / P0 = V / S := by
    rw [← hfg]
    field_simp
  have hratio : P0 / P = S * (1 - a) := by
    have e : P0 / P = (B / P) / (B / P0) := by field_simp
    rw [e, hBP, hBP0]
    field_simp
  have hj : jumpRatio r i w = (1 - a) / (1 - c) := by
    rw [jumpRatio, ha, hc, one_sub_div hr0, one_sub_div hi0]
    field_simp
  rw [hratio, hj, hS]
  field_simp
  ring

/-- Cochrane (2023), A1 p. 560–561: the forward-guidance price-level drop
`1 − P_0/P = (ω/(1+r))^T · ω(i−r)/((1+r)(1+i−ω))`. -/
noncomputable def fgDrop (r i w : ℝ) (T : ℕ) : ℝ :=
  (w / (1 + r)) ^ T * (w * (i - r) / ((1 + r) * (1 + i - w)))

/-- Cochrane (2023), A1 p. 560: `(ω/(1+r))^T [(1.16) − 1] = −fgDrop`. -/
theorem fg_eq_neg_drop {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) (T : ℕ) :
    (w / (1 + r)) ^ T * (jumpRatio r i w - 1) = -fgDrop r i w T := by
  rw [jumpRatio_sub_one hw hwr hwi, fgDrop]
  ring

/-- Cochrane (2023), A1 p. 561 ("As `T → ∞`, the downward price-level jump goes to zero"). -/
theorem fg_tendsto_zero {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) :
    Tendsto (fun T : ℕ => (w / (1 + r)) ^ T * (jumpRatio r i w - 1)) atTop (𝓝 0) := by
  have hr1 : 0 < 1 + r := by linarith
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hw hr1.le)
    ((div_lt_one hr1).mpr hwr)).mul_const (jumpRatio r i w - 1)

/-- Cochrane (2023), A1 p. 561 ("The price level `P_0` still jumps – forward guidance works"):
with long-term debt (`0 < ω < 1 + r`) and a rise `i > r` announced for any date `T`, the price
level jumps down on announcement. -/
theorem fg_drop_pos {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hri : r < i) (T : ℕ) :
    0 < fgDrop r i w T := by
  have hr1 : 0 < 1 + r := by linarith
  exact mul_pos (pow_pos (div_pos hw hr1) T)
    (div_pos (mul_pos hw (by linarith)) (mul_pos hr1 (by linarith)))

/-- Cochrane (2023), A1 p. 561 ("Longer `T` … give a smaller price-level jump"): for `i ≥ r`
the drop is antitone in the announcement horizon `T`. -/
theorem fg_drop_antitone_T {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hri : r ≤ i) :
    Antitone (fun T => fgDrop r i w T) := by
  have hr1 : 0 < 1 + r := by linarith
  have hk : 0 ≤ w * (i - r) / ((1 + r) * (1 + i - w)) :=
    div_nonneg (mul_nonneg hw (by linarith)) (mul_pos hr1 (by linarith)).le
  intro T1 T2 h
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (div_nonneg hw hr1.le)
    ((div_le_one hr1).mpr hwr.le) h) hk

/-- Cochrane (2023), A1 p. 561: for `0 < ω` and `i > r` the drop is strictly decreasing in
`T`. -/
theorem fg_drop_strictAnti_T {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hri : r < i) :
    StrictAnti (fun T => fgDrop r i w T) := by
  have hr1 : 0 < 1 + r := by linarith
  have hk : 0 < w * (i - r) / ((1 + r) * (1 + i - w)) :=
    div_pos (mul_pos hw (by linarith)) (mul_pos hr1 (by linarith))
  intro T1 T2 h
  exact mul_lt_mul_of_pos_right (pow_lt_pow_right_of_lt_one₀ (div_pos hw hr1)
    ((div_lt_one hr1).mpr hwr) h) hk

/-- Cochrane (2023), A1 p. 561 ("shorter maturity structures — lower ω — give a smaller
price-level jump"): for `i > r` the drop is strictly increasing in `ω` on `[0, 1 + r)`. -/
theorem fg_drop_strictMonoOn_omega {r i : ℝ} (hr : 0 < 1 + r) (hri : r < i) (T : ℕ) :
    StrictMonoOn (fun w => fgDrop r i w T) (Set.Ico 0 (1 + r)) := by
  intro w1 hw1 w2 hw2 h12
  simp only [fgDrop]
  have hw2p : 0 < w2 := lt_of_le_of_lt hw1.1 h12
  have hd1 : 0 < (1 + r) * (1 + i - w1) := mul_pos hr (by linarith [hw1.2])
  have hd2 : 0 < (1 + r) * (1 + i - w2) := mul_pos hr (by linarith [hw2.2])
  have hg : w1 * (i - r) / ((1 + r) * (1 + i - w1)) < w2 * (i - r) / ((1 + r) * (1 + i - w2)) := by
    rw [div_lt_div_iff₀ hd1 hd2]
    have key : w2 * (i - r) * ((1 + r) * (1 + i - w1)) -
        w1 * (i - r) * ((1 + r) * (1 + i - w2)) = (i - r) * (1 + r) * (1 + i) * (w2 - w1) := by
      ring
    have hpos : 0 < (i - r) * (1 + r) * (1 + i) * (w2 - w1) :=
      mul_pos (mul_pos (mul_pos (by linarith) hr) (by linarith [hw2.2])) (by linarith)
    linarith
  have hg1 : 0 ≤ w1 * (i - r) / ((1 + r) * (1 + i - w1)) :=
    div_nonneg (mul_nonneg hw1.1 (by linarith)) hd1.le
  have hp : (w1 / (1 + r)) ^ T ≤ (w2 / (1 + r)) ^ T :=
    pow_le_pow_left₀ (div_nonneg hw1.1 hr.le) (div_le_div_of_nonneg_right h12.le hr.le) T
  calc (w1 / (1 + r)) ^ T * (w1 * (i - r) / ((1 + r) * (1 + i - w1)))
      ≤ (w2 / (1 + r)) ^ T * (w1 * (i - r) / ((1 + r) * (1 + i - w1))) :=
        mul_le_mul_of_nonneg_right hp hg1
    _ < (w2 / (1 + r)) ^ T * (w2 * (i - r) / ((1 + r) * (1 + i - w2))) :=
        mul_lt_mul_of_pos_left hg (pow_pos (div_pos hw2p hr) T)

/-! ### Transitory rate rises (A1 p. 560) -/

/-- Cochrane (2023), A1 p. 560 ("monetary policy changes in interest rates are not permanent
… each factor reducing the size of the effect"): a pointwise lower path of one-period rates
`i'_k ≤ i_k` (with `1 + i'_k > 0`) gives a weakly higher value
`∑_j ωʲ∏_{k<j}(1+i_k)⁻¹` of the geometric portfolio. -/
theorem annuity_mono_rates {w : ℝ} (hw : 0 ≤ w) {i i' : ℕ → ℝ} (hi' : ∀ k, 0 < 1 + i' k)
    (hle : ∀ k, i' k ≤ i k)
    (hs' : Summable fun j => w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹) :
    ∑' j, w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ ≤
      ∑' j, w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹ := by
  have hpos : ∀ k, 0 < 1 + i k := fun k => lt_of_lt_of_le (hi' k) (by linarith [hle k])
  have hterm : ∀ j, w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ ≤
      w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹ := fun j =>
    mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => (inv_pos.mpr (hpos k)).le)
      (fun k _ => (inv_le_inv₀ (hpos k) (hi' k)).mpr (by linarith [hle k]))) (pow_nonneg hw j)
  have h0 : ∀ j, 0 ≤ w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ := fun j =>
    mul_nonneg (pow_nonneg hw j) (Finset.prod_nonneg fun k _ => (inv_pos.mpr (hpos k)).le)
  exact Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le h0 hterm hs') hs'

/-- Cochrane (2023), A1 p. 560: with the same debt `B > 0` and the same positive present value
of surpluses `V`, a higher portfolio value per unit of debt `A ≤ A'` in the valuation equation
`A · B/P_0 = V` means a higher price level, `P_0 ≤ P_0'`. -/
theorem price_le_of_annuity_le {A A' B V P0 P0' : ℝ} (hA : 0 < A) (hAA : A ≤ A') (hB : 0 < B)
    (hP0 : 0 < P0) (hP0' : 0 < P0') (h : A * (B / P0) = V) (h' : A' * (B / P0') = V) :
    P0 ≤ P0' := by
  have e : A * (B / P0) = A' * (B / P0') := h.trans h'.symm
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hP0.ne' hP0'.ne'] at e
  by_contra hlt
  push Not at hlt
  have h1 : A * B * P0' < A' * B * P0 := by
    have hAB : 0 < A * B := mul_pos hA hB
    calc A * B * P0' < A * B * P0 := mul_lt_mul_of_pos_left hlt hAB
      _ ≤ A' * B * P0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAA hB.le) hP0.le
  linarith

/-- Cochrane (2023), A1 p. 560 ("A mean-reverting interest-rate rise has a smaller effect
still"): the mean-reverting path `i_k = r + (i − r)φᵏ`, `0 ≤ φ ≤ 1`, `r ≤ i`, lies below the
permanent rise `i`, so (by `annuity_mono_rates` and `price_le_of_annuity_le`) its price-level
drop is no larger. -/
theorem meanReverting_le_perm {r i φ : ℝ} (hri : r ≤ i) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (k : ℕ) :
    r ≤ r + (i - r) * φ ^ k ∧ r + (i - r) * φ ^ k ≤ i := by
  have h1 : 0 ≤ φ ^ k := pow_nonneg hφ0 k
  have h2 : φ ^ k ≤ 1 := pow_le_one₀ hφ0 hφ1
  constructor <;> nlinarith

/-! ### Roll-over of a geometric maturity structure (A1 p. 561) -/

/-- Cochrane (2023), A1 p. 561: bond sales under the geometric structure,
`B_t^{(t+j)} − B_{t−1}^{(t+j)} = ω^{j−1}b_{t+1} − ωʲb_t` (here with `j + 1` for `j`). -/
theorem geom_rollover (w : ℝ) (b : ℕ → Ω → ℝ) (t j : ℕ) (ξ : Ω) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * b (t + 1) ξ -
      w ^ (j + 1) * b t ξ := rfl

/-- Cochrane (2023), A1 p. 561: to maintain a steady state `b_{t+1} = b_t = B`, the government
sells `ω^{j−1}(1−ω)B = ((1−ω)/ω) B_{t−1}^{(t+j)}` of each maturity (`ω ≠ 0`). -/
theorem geom_rollover_steady {w : ℝ} (hw : w ≠ 0) {b : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω}
    (hb : b (t + 1) ξ = b t ξ) (j : ℕ) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * (1 - w) * b t ξ ∧
      geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ =
        (1 - w) / w * geomDebt w b t (j + 1) ξ := by
  rw [geom_rollover, hb]
  simp only [geomDebt]
  constructor
  · ring
  · field_simp
    ring

/-- Cochrane (2023), A1 pp. 559 and 561: in the steady state (constant `P`, `B`, rate `r > 0`,
so `Q^{(j)} = 1/(1+r)ʲ`), the geometric flow condition
`B = Ps + ∑_j Q^{(j+1)}(ωʲB − ω^{j+1}B)` (the roll-over of p. 561) holds iff the steady-state
valuation (1.15) `(1+r)/(1+r−ω) · B/P = (1+r)s/r` holds. -/
theorem steady_flow_iff_1_15 {r w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwr : w < 1 + r)
    {B P s : ℝ} (hP : P ≠ 0) :
    B = P * s + ∑' j : ℕ, ((1 + r) ^ (j + 1))⁻¹ * (w ^ j * B - w ^ (j + 1) * B) ↔
      (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s := by
  have hr1 : 0 < 1 + r := by linarith
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have hsum : ∑' j : ℕ, ((1 + r) ^ (j + 1))⁻¹ * (w ^ j * B - w ^ (j + 1) * B) =
      (1 - w) * B / (1 + r - w) := by
    have h := ((geom_value (i := r) hw hwr).mul_left ((1 - w) * B / (1 + r))).tsum_eq
    rw [← show (1 - w) * B / (1 + r) * ((1 + r) / (1 + r - w)) = (1 - w) * B / (1 + r - w) by
      field_simp, ← h]
    refine tsum_congr fun j => ?_
    rw [pow_succ]
    field_simp
    ring
  rw [hsum]
  have hr0 : r ≠ 0 := hr.ne'
  have hr1' : (1 + r) ≠ 0 := hr1.ne'
  rw [steady_state_1_15 hr hwr B P s]
  constructor
  · intro h
    have e : B * r = (1 + r - w) * s * P := by
      have h' : B * (1 + r - w) = P * s * (1 + r - w) + (1 - w) * B := by
        rw [div_eq_mul_inv] at h
        calc B * (1 + r - w) = (P * s + (1 - w) * B * (1 + r - w)⁻¹) * (1 + r - w) := by
              rw [← h]
          _ = P * s * (1 + r - w) + (1 - w) * B := by field_simp
      linear_combination h'
    rw [div_eq_div_iff hP hr0]
    linear_combination e
  · intro h
    rw [div_eq_div_iff hP hr0] at h
    have e : P * s = r * B / (1 + r - w) := by
      rw [eq_div_iff h1]
      linear_combination -h
    rw [e, ← add_div, eq_div_iff h1]
    ring

/-! ### When a geometric maturity structure needs tending (A1 p. 561) -/

/-- Cochrane (2023), A1 p. 561: under the geometric structure the net issuance of each
maturity is `B_t^{(t+j+1)} − B_{t−1}^{(t+j+1)} = ωʲ(b_{t+1} − ωb_t)`. -/
theorem geom_issuance (w : ℝ) (b : ℕ → Ω → ℝ) (t j : ℕ) (ξ : Ω) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * (b (t + 1) ξ - w * b t ξ) := by
  simp only [geomDebt]
  ring

/-- Cochrane (2023), A1 p. 561 ("needs tending"): the government never trades, neither issuing
nor repurchasing any outstanding maturity, `B_t^{(t+j)} = B_{t−1}^{(t+j)}` for all `j ≥ 1`;
maturing debt is paid off from surpluses alone. -/
def NoTrade (B : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j ξ, B (t + 1) j ξ = B t (j + 1) ξ

/-- Cochrane (2023), A1 p. 561: the geometric structure is preserved with no trading iff the
face value shrinks geometrically, `b_{t+1} = ωb_t`. -/
theorem geom_noTrade_iff (w : ℝ) (b : ℕ → Ω → ℝ) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, b (t + 1) ξ = w * b t ξ := by
  constructor
  · intro h t ξ
    have := h t 0 ξ
    simpa [geomDebt] using this
  · intro h t j ξ
    simp only [geomDebt, h t ξ]
    ring

/-- Cochrane (2023), A1 p. 561: no trading means `b_t = ωᵗ b_0` at every date. -/
theorem geom_noTrade_iff_path (w : ℝ) (b : ℕ → Ω → ℝ) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, b t ξ = w ^ t * b 0 ξ := by
  rw [geom_noTrade_iff]
  constructor
  · intro h t ξ
    induction t with
    | zero => simp
    | succ t ih => rw [h t ξ, ih, pow_succ]; ring
  · intro h t ξ
    rw [h (t + 1) ξ, h t ξ, pow_succ]
    ring

/-- Cochrane (2023), eq. (3.2), p. 53, geometric case: the flow condition reads
`b_t = P_ts_t + (b_{t+1} − ωb_t)∑_j ωʲQ_t^{(t+j+1)}`. -/
theorem geomFlow_iff_issuance {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} {t : ℕ} :
    GeomFlow w P s b Q t ↔ ∀ ξ, b t ξ = P t ξ * s t ξ +
      (b (t + 1) ξ - w * b t ξ) * ∑' j, w ^ j * Q t (j + 1) ξ := by
  refine forall_congr' fun ξ => ?_
  rw [← tsum_mul_left]
  have h : ∀ j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ) =
      (b (t + 1) ξ - w * b t ξ) * (w ^ j * Q t (j + 1) ξ) := fun j => by ring
  simp_rw [h]

/-- Cochrane (2023), A1 p. 561 ("A geometric maturity structure needs tending, except in a
knife edge case that surpluses are also nonstochastic and geometric"), made precise: if the
geometric flow condition holds at every date and the value `∑_j ωʲQ_t^{(t+j+1)}` of the debt
carried forward per unit is never zero (e.g. positive bond prices), then the government never
needs to trade iff nominal surpluses are `P_ts_t = ωᵗb_0` at every date. -/
theorem geom_knife_edge {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hflow : ∀ t, GeomFlow w P s b Q t) (hS : ∀ t ξ, ∑' j, w ^ j * Q t (j + 1) ξ ≠ 0) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, P t ξ * s t ξ = w ^ t * b 0 ξ := by
  constructor
  · intro hnt t ξ
    have hf := geomFlow_iff_issuance.mp (hflow t) ξ
    have h1 := (geom_noTrade_iff w b).mp hnt t ξ
    have h2 := (geom_noTrade_iff_path w b).mp hnt t ξ
    rw [h1, sub_self, zero_mul, add_zero] at hf
    rw [← hf, h2]
  · intro hs
    rw [geom_noTrade_iff_path]
    intro t ξ
    induction t with
    | zero => simp
    | succ t ih =>
      have hf := geomFlow_iff_issuance.mp (hflow t) ξ
      rw [hs t ξ, ih] at hf
      have hz : (b (t + 1) ξ - w * (w ^ t * b 0 ξ)) * ∑' j, w ^ j * Q t (j + 1) ξ = 0 := by
        linarith
      rcases mul_eq_zero.mp hz with h | h
      · rw [pow_succ]
        linarith
      · exact absurd h (hS t ξ)

/-- Cochrane (2023), A1 p. 561 ("nonstochastic"): in the knife-edge case nominal surpluses are
known at date 0 (`E_0[P_ts_t] = P_ts_t`) whenever `b_0` is. -/
theorem knife_edge_surplus_known (𝔼 : ExpectationSystem Ω) {w : ℝ} {P s b : ℕ → Ω → ℝ}
    {Q : ℕ → ℕ → Ω → ℝ} (hflow : ∀ t, GeomFlow w P s b Q t) (hnt : NoTrade (geomDebt w b))
    (hb0 : 𝔼.E 0 (b 0) = b 0) (t : ℕ) : 𝔼.E 0 (P t * s t) = P t * s t := by
  have h : P t * s t = w ^ t • b 0 := by
    funext ξ
    have hf := geomFlow_iff_issuance.mp (hflow t) ξ
    rw [(geom_noTrade_iff w b).mp hnt t ξ, sub_self, zero_mul, add_zero] at hf
    rw [Pi.mul_apply, ← hf, Pi.smul_apply, smul_eq_mul, (geom_noTrade_iff_path w b).mp hnt t ξ]
  rw [h, map_smul, hb0]

/-- Cochrane (2023), A1 p. 561 ("To see the needed bond sales"): outside the knife edge — if at
some date and state `P_ts_t ≠ ωᵗb_0` — the government must issue or repurchase debt at some
date: some `B_t^{(t+j)} − B_{t−1}^{(t+j)} = ω^{j−1}(b_{t+1} − ωb_t) ≠ 0`. -/
theorem geom_needs_tending {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hflow : ∀ t, GeomFlow w P s b Q t) (hS : ∀ t ξ, ∑' j, w ^ j * Q t (j + 1) ξ ≠ 0)
    (hne : ∃ t ξ, P t ξ * s t ξ ≠ w ^ t * b 0 ξ) :
    ∃ t j ξ, geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨t, ξ, hne⟩ := hne
  exact hne ((geom_knife_edge hflow hS).mp (fun t j ξ => sub_eq_zero.mp (h t j ξ)) t ξ)

end Cochrane.Generality.LongTermDebt

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ratios to GDP and a focus on inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.2, pp. 54–55, eq. (3.4)
and the three unnumbered displays.

The valuation equation `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` (with `m ≡ β` the book's
`E_t ∑ βʲ s_{t+j}`, `LongTermDebt.pv_const`) is rewritten by dividing by a variable known at
`t`: real GDP `y_t > 0` or nominal debt `B_{t−1} > 0`. The only property of `E_t` used is the
pull-out property for date-`t` variables; no inverse `1/y_t` is assumed to be known.

Notation: `D t` is `B_{t−1}`, the nominal one-period debt outstanding at the start of `t`.

## Main results

* `E_div_known`: `E_t[W/z] = E_t[W]/z` for `z` known at `t`, `z ≠ 0`.
* `valuation_gdp_iff` (p. 54): `B_{t−1}/P_t = PV` iff
  `B_{t−1}/(P_ty_t) = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})]`.
* `valuation_per_dollar_iff` (3.4): iff `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}/B_{t−1}]`;
  `valuation_per_dollar_const` is (3.4) exactly as printed.
* `valuation_per_dollar_gdp_iff` (p. 55): iff
  `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] / (B_{t−1}/y_t)`.
* `E_innov_zero` (p. 54): `E_t(E_{t+1} − E_t)X = 0`; `E_innov_pv_zero` for `X = ∑ βʲs_{t+j}`.
* `flow_gdp_iff`: the flow condition in ratios to GDP.
* `gdp_growth_mono` (p. 54, "more growth means greater surpluses"): with given nonnegative
  surplus-to-GDP ratios, faster growth raises the debt-to-GDP valuation.
-/

namespace Cochrane.Generality.Ratios

open LongTermDebt

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §3.2, p. 54 ("multiplying and dividing by real GDP `y_t`"): for `z` known
at `t` and nonzero, `E_t[W/z] = E_t[W]/z` (pull-out applied to `W = z·(W/z)`). -/
theorem E_div_known (hP : 𝔼.PullOut) {t : ℕ} {z : Ω → ℝ} (hz : 𝔼.E t z = z)
    (hz0 : ∀ ξ, z ξ ≠ 0) (W : Ω → ℝ) (ξ : Ω) :
    𝔼.E t (fun ξ' => W ξ' / z ξ') ξ = 𝔼.E t W ξ / z ξ := by
  have hW : W = z * fun ξ' => W ξ' / z ξ' := by
    funext ξ'
    simp only [Pi.mul_apply]
    field_simp [hz0 ξ']
  have h := congrFun (hP t z (fun ξ' => W ξ' / z ξ') hz) ξ
  rw [← hW, Pi.mul_apply] at h
  rw [h]
  field_simp [hz0 ξ]

/-- Cochrane (2023), §3.2, p. 54: the growth-adjusted term
`(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})` of the debt-to-GDP valuation. -/
noncomputable def gdpTerm (m y s : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  sdf m t j * fun ξ => y (t + j) ξ / y t ξ * (s (t + j) ξ / y (t + j) ξ)

/-- Cochrane (2023), §3.2, p. 54: with GDP known at `t` and positive at all dates,
`E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] = E_t[(Λ_{t+j}/Λ_t)s_{t+j}]/y_t`. -/
theorem E_gdpTerm (hP : 𝔼.PullOut) {m y s : ℕ → Ω → ℝ} {t : ℕ} (hy : 𝔼.E t (y t) = y t)
    (hy0 : ∀ k ξ, y k ξ ≠ 0) (j : ℕ) (ξ : Ω) :
    𝔼.E t (gdpTerm m y s t j) ξ = 𝔼.E t (sdf m t j * s (t + j)) ξ / y t ξ := by
  have h : gdpTerm m y s t j = fun ξ' => (sdf m t j * s (t + j)) ξ' / y t ξ' := by
    funext ξ'
    simp only [gdpTerm, Pi.mul_apply]
    have := hy0 (t + j) ξ'
    have := hy0 t ξ'
    field_simp
  rw [h, E_div_known 𝔼 hP hy (hy0 t)]

/-- Cochrane (2023), §3.2, p. 54 (first display): the valuation equation
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` holds iff its debt-to-GDP form
`B_{t−1}/(P_ty_t) = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})]` holds. -/
theorem valuation_gdp_iff (hP : 𝔼.PullOut) {m y s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, D t ξ / (P t ξ * y t ξ) = ∑' j, 𝔼.E t (gdpTerm m y s t j) ξ := by
  refine forall_congr' fun ξ => ?_
  simp_rw [E_gdpTerm 𝔼 hP hy hy0]
  rw [tsum_div_const, pv, div_mul_eq_div_div]
  exact ⟨fun h => by rw [h], fun h => (div_left_inj' (hy0 t ξ)).mp h⟩

/-- Cochrane (2023), eq. (3.4), p. 54: with nominal debt `B_{t−1}` known at `t` and nonzero,
the valuation equation holds iff `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}/B_{t−1}]`, the value of
one dollar. -/
theorem valuation_per_dollar_iff (hP : 𝔼.PullOut) {m s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hD : 𝔼.E t (D t) = D t) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, 1 / P t ξ = ∑' j, 𝔼.E t (fun ξ' => (sdf m t j * s (t + j)) ξ' / D t ξ') ξ := by
  refine forall_congr' fun ξ => ?_
  simp_rw [E_div_known 𝔼 hP hD hD0]
  rw [tsum_div_const, pv]
  have h0 := hD0 ξ
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [eq_div_iff h0] at h
    rw [← h]
    field_simp

/-- Cochrane (2023), eq. (3.4), p. 54, exactly as printed (`m ≡ β`):
`B_{t−1}/P_t = ∑_j βʲE_t s_{t+j}` iff `1/P_t = ∑_j βʲ E_t[s_{t+j}/B_{t−1}]`. -/
theorem valuation_per_dollar_const (hP : 𝔼.PullOut) (β : ℝ) {s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hD : 𝔼.E t (D t) = D t) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ξ) ↔
      ∀ ξ, 1 / P t ξ = ∑' j, β ^ j * 𝔼.E t (fun ξ' => s (t + j) ξ' / D t ξ') ξ := by
  have h := valuation_per_dollar_iff 𝔼 hP (m := fun _ _ => β) (s := s) (P := P) hD hD0
  rw [pv_const] at h
  convert h using 3 with ξ ξ
  refine tsum_congr fun j => ?_
  rw [E_div_known 𝔼 hP hD hD0, E_div_known 𝔼 hP hD hD0, sdf_const]
  have h' : ((fun _ => β ^ j) * s (t + j) : Ω → ℝ) = β ^ j • s (t + j) := by
    funext ξ'
    simp
  rw [h', map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Cochrane (2023), §3.2, p. 55 (last display): with GDP and nominal debt known at `t` and
nonzero, the valuation equation holds iff
`1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] / (B_{t−1}/y_t)`. -/
theorem valuation_per_dollar_gdp_iff (hP : 𝔼.PullOut) {m y s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, 1 / P t ξ = (∑' j, 𝔼.E t (gdpTerm m y s t j) ξ) / (D t ξ / y t ξ) := by
  rw [valuation_gdp_iff 𝔼 hP hy hy0]
  refine forall_congr' fun ξ => ?_
  have h0 := hD0 ξ
  have h1 := hy0 t ξ
  constructor
  · intro h
    rw [← h]
    by_cases hp : P t ξ = 0
    · simp [hp]
    · field_simp
  · intro h
    rw [eq_div_iff (div_ne_zero h0 h1)] at h
    rw [← h]
    by_cases hp : P t ξ = 0
    · simp [hp]
    · field_simp

/-- Cochrane (2023), §3.2, p. 54: "There can be no expected shocks to the present value of
surpluses", `E_t[(E_{t+1} − E_t)X] = 0` for every random variable `X`. -/
theorem E_innov_zero (t : ℕ) (X : Ω → ℝ) : 𝔼.E t (𝔼.E (t + 1) X - 𝔼.E t X) = 0 := by
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), §3.2, p. 54: `E_t(E_{t+1} − E_t)∑_j βʲs_{t+j} = 0`, with the sum taken
state by state. -/
theorem E_innov_pv_zero (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E t (𝔼.E (t + 1) (fun ξ => ∑' j, β ^ j * s (t + j) ξ) -
      𝔼.E t (fun ξ => ∑' j, β ^ j * s (t + j) ξ)) = 0 :=
  E_innov_zero 𝔼 t _

/-- Cochrane (2023), §3.2, p. 54 (the flow condition in ratios to GDP): with GDP known at `t`
and positive, `x_t = s_t + E_t[m_t x_{t+1}]` iff
`x_t/y_t = s_t/y_t + E_t[m_t (y_{t+1}/y_t)(x_{t+1}/y_{t+1})]`. -/
theorem flow_gdp_iff (hP : 𝔼.PullOut) {m y s x : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) :
    (∀ ξ, x t ξ = s t ξ + 𝔼.E t (m t * x (t + 1)) ξ) ↔
      ∀ ξ, x t ξ / y t ξ = s t ξ / y t ξ +
        𝔼.E t (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ')) ξ := by
  have h : ∀ ξ, 𝔼.E t (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ'))
      ξ = 𝔼.E t (m t * x (t + 1)) ξ / y t ξ := fun ξ => by
    have e : (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ')) =
        fun ξ' => (m t * x (t + 1)) ξ' / y t ξ' := by
      funext ξ'
      simp only [Pi.mul_apply]
      have := hy0 (t + 1) ξ'
      have := hy0 t ξ'
      field_simp
    rw [e, E_div_known 𝔼 hP hy (hy0 t)]
  refine forall_congr' fun ξ => ?_
  rw [h, ← add_div]
  exact ⟨fun e => by rw [e], fun e => (div_left_inj' (hy0 t ξ)).mp e⟩

/-- Cochrane (2023), §3.2, p. 54 ("More growth means greater surpluses, with surplus-to-GDP
ratios"): under perfect foresight with `0 ≤ β`, nonnegative surplus-to-GDP ratios `σ_j` and
summable valuations, a growth path `g'_j ≥ g_j` (`g_j = y_{t+j}/y_t`) gives a weakly larger
debt-to-GDP valuation `∑_j βʲ g_j σ_j`. -/
theorem gdp_growth_mono {β : ℝ} (hβ : 0 ≤ β) {g g' σ : ℕ → ℝ} (hσ : ∀ j, 0 ≤ σ j)
    (hg : ∀ j, g j ≤ g' j) (hs' : Summable fun j => β ^ j * g' j * σ j)
    (hs : Summable fun j => β ^ j * g j * σ j) :
    ∑' j, β ^ j * g j * σ j ≤ ∑' j, β ^ j * g' j * σ j :=
  Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hg j) (pow_nonneg hβ j)) (hσ j)) hs hs'

end Cochrane.Generality.Ratios

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Risk and discounting

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.3, pp. 55–57, eqs.
(3.5)–(3.8) and the unnumbered displays.

Discounting uses one-period factors `m t = Λ_{t+1}/Λ_t` (known at `t + 1`), and the
multi-period factor `sdf m t n = Λ_{t+n}/Λ_t` (`sdf_eq_ratio`); the machinery
(`pv`, `TVC`, `flow_tvc_iff_pv`) is in `LongTermDebt`. `D t` is `B_{t−1}`, the nominal
one-period debt outstanding at the start of `t`, and `x_t = B_{t−1}/P_t`.

## Main results

* `sdf_eq_ratio`, `sdf_marginal_utility`: `∏_{k<n} m_{t+k} = Λ_{t+n}/Λ_t`, and with
  `Λ_t = βᵗu'(c_t)` the factor `βⁿu'(c_{t+n})/u'(c_t)`.
* `flowOne_iff_rec` (p. 55): with `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`, the flow
  `B_{t−1}/P_t = s_t + Q_tB_t/P_t` is `x_t = s_t + E_t[m_tx_{t+1}]`; `tvc_lambda_iff`: the TVC
  in the book's form `lim E_t[Λ_TB_{T−1}/(Λ_tP_T)] = 0`.
* `valuation_sdf_iff` (3.5): flow + TVC at every date ⟺ `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)
  s_{t+j}]` at every date (signed surpluses, absolutely summable); `pv_lambda` the printed
  form; `price_eq_of_valuation`, `price_unique`: the valuation equation determines `P_t`.
* `inv_return_sdf`, `inv_return_expost` (p. 56): `1 = E_t[R⁻¹_{t+1}R_{t+1}]` under every
  `ExpectationSystem` ("using any set of probabilities").
* `flow_expost` (p. 56): `B_{t−1}/P_t = s_t + R⁻¹_{t+1}B_t/P_{t+1}` with
  `R_{t+1} = (1/Q_t)P_t/P_{t+1}`, `expostReturn_rate`: `= (1+i_t)P_t/P_{t+1}`.
* `expost_iterate` (3.6), finite horizon, with the terminal product up to `T` (survey E12);
  `expost_tendsto_iff`, `expost_pv`: the infinite sum converges to `x_t` iff the terminal
  term vanishes; `expost_E_tendsto_iff`, `expost_pv_E`, `expost_flow_E`: the same after
  taking `E_t` under any expectation system.
* `pf_expost_inv_eq_sdf`: under perfect foresight the ex-post discount factor is `m`.
* `expost_may_diverge` (p. 56): an economy in which (3.5), the flow and the TVC hold at every
  date while along a realised path the ex-post present value (3.6) diverges to `−∞` and its
  terminal term to `+∞`.
* `finiteTree_expost_pv`: on every finite event tree, (3.5) with its flow and TVC force (3.6)
  to converge absolutely in every state (all states have positive probability), via
  `finiteTree_info_stable`, `finiteTree_eventually_known`; the explosion needs a
  zero-probability path.
* (3.7)–(3.8): `portfolioReturn`, `flowLT_iff_3_8`, and `expostLT_pv` (p. 57).
-/

namespace Cochrane.Generality.StochasticDiscount

open Filter Topology LongTermDebt

variable {Ω : Type*}

/-! ### The discount factor as a ratio of marginal utilities -/

/-- Cochrane (2023), §3.3, p. 55: if the one-period factors are `m_s = Λ_{s+1}/Λ_s` with
`Λ ≠ 0`, the multi-period factor is `Λ_{t+n}/Λ_t`. -/
theorem sdf_eq_ratio {Λ m : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t n : ℕ) :
    sdf m t n = fun ξ => Λ (t + n) ξ / Λ t ξ := by
  induction n with
  | zero =>
    funext ξ
    simp [hΛ t ξ]
  | succ n ih =>
    rw [sdf_succ, ih, hm]
    funext ξ
    simp only [Pi.mul_apply]
    have := hΛ (t + n) ξ
    rw [show t + (n + 1) = t + n + 1 by omega]
    field_simp

/-- Cochrane (2023), §3.3, p. 55: with `Λ_t = βᵗu'(c_t)`, `β > 0`, positive marginal utility
`u'(c_t)`, the one-period factor is `β u'(c_{t+1})/u'(c_t)` and the multi-period factor is
`Λ_{t+n}/Λ_t = βⁿ u'(c_{t+n})/u'(c_t)`. -/
theorem sdf_marginal_utility {β : ℝ} (hβ : 0 < β) {up : ℕ → Ω → ℝ} (hup : ∀ s ξ, 0 < up s ξ)
    (t n : ℕ) :
    sdf (fun s ξ => β * up (s + 1) ξ / up s ξ) t n =
      fun ξ => β ^ n * up (t + n) ξ / up t ξ := by
  have h := sdf_eq_ratio (Λ := fun s ξ => β ^ s * up s ξ) (m := fun s ξ => β * up (s + 1) ξ /
    up s ξ) (fun s ξ => (mul_pos (pow_pos hβ s) (hup s ξ)).ne') (fun s => by
      funext ξ
      have := (hup s ξ).ne'
      have := hβ.ne'
      field_simp
      ring) t n
  rw [h]
  funext ξ
  have := (hup t ξ).ne'
  have := hβ.ne'
  rw [pow_add]
  field_simp

/-! ### One-period debt: the flow, the transversality condition and (3.5) -/

variable (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §3.3, p. 55: the one-period nominal bond price
`Q_t = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]`. -/
noncomputable def bondPrice (m P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (m t * fun ξ => P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), §3.3, p. 55 (the flow condition (2.5) with a bond price `Q`):
`B_{t−1}/P_t = s_t + Q_tB_t/P_t`. -/
def FlowOne (Q P s D : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ξ, D t ξ / P t ξ = s t ξ + Q t ξ * D (t + 1) ξ / P t ξ

/-- Cochrane (2023), §3.3, p. 55: the real value `x_t = B_{t−1}/P_t` of the debt. -/
noncomputable def realDebt (D P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ξ => D t ξ / P t ξ

/-- Cochrane (2023), §3.3, p. 55: with the bond price `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`,
`P_t` known at `t`, `B_t` known at `t` and `P ≠ 0`, the flow condition is
`x_t = s_t + E_t[(Λ_{t+1}/Λ_t)x_{t+1}]`. -/
theorem flowOne_iff_rec (hP : 𝔼.PullOut) {m P s D : ℕ → Ω → ℝ} {t : ℕ}
    (hPa : 𝔼.E t (P t) = P t) (hD1 : 𝔼.E t (D (t + 1)) = D (t + 1)) (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    FlowOne (bondPrice 𝔼 m P) P s D t ↔
      realDebt D P t = s t + 𝔼.E t (m t * realDebt D P (t + 1)) := by
  have hQ : ∀ ξ, bondPrice 𝔼 m P t ξ * D (t + 1) ξ / P t ξ =
      𝔼.E t (m t * realDebt D P (t + 1)) ξ := by
    intro ξ
    have e1 : (m t * fun ξ' => P t ξ' / P (t + 1) ξ') =
        P t * (m t * fun ξ' => (P (t + 1) ξ')⁻¹) := by
      funext ξ'
      simp only [Pi.mul_apply, div_eq_mul_inv]
      ring
    have e2 : (m t * realDebt D P (t + 1)) = D (t + 1) * (m t * fun ξ' => (P (t + 1) ξ')⁻¹) := by
      funext ξ'
      simp only [Pi.mul_apply, realDebt, div_eq_mul_inv]
      ring
    rw [bondPrice, e1, hP t _ _ hPa, e2, hP t _ _ hD1]
    simp only [Pi.mul_apply]
    have := hP0 t ξ
    field_simp
  constructor
  · intro h
    funext ξ
    rw [Pi.add_apply, ← hQ ξ]
    exact h ξ
  · intro h ξ
    have := congrFun h ξ
    rw [Pi.add_apply, ← hQ ξ] at this
    exact this

/-- Cochrane (2023), §3.3, p. 55: the transversality condition in the book's form,
`lim_T E_t[Λ_T B_{T−1}/(Λ_t P_T)] = 0`, is `TVC` for the factors `m_s = Λ_{s+1}/Λ_s`. -/
theorem tvc_lambda_iff {Λ m D P : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t : ℕ) :
    TVC 𝔼 m (realDebt D P) t ↔ ∀ ξ, Tendsto
      (fun N => 𝔼.E t (fun ξ' => Λ (t + N) ξ' * D (t + N) ξ' / (Λ t ξ' * P (t + N) ξ')) ξ)
      atTop (𝓝 0) := by
  refine forall_congr' fun ξ => ?_
  have h : ∀ N, (sdf m t N * realDebt D P (t + N)) =
      fun ξ' => Λ (t + N) ξ' * D (t + N) ξ' / (Λ t ξ' * P (t + N) ξ') := fun N => by
    rw [sdf_eq_ratio hΛ hm]
    funext ξ'
    simp only [Pi.mul_apply, realDebt]
    rw [div_mul_div_comm]
  simp_rw [h]

/-- Cochrane (2023), eq. (3.5), p. 55, printed form: the present value is
`∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]`. -/
theorem pv_lambda {Λ m s : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t : ℕ) :
    pv 𝔼 m s t = fun ξ => ∑' j, 𝔼.E t (fun ξ' => Λ (t + j) ξ' / Λ t ξ' * s (t + j) ξ') ξ := by
  funext ξ
  simp only [pv, sdf_eq_ratio hΛ hm]
  rfl

/-- Cochrane (2023), eq. (3.5), p. 55: with the bond price `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`,
nonnegative factors known one period ahead, adapted surpluses with absolutely summable present
values, an adapted price level `P ≠ 0`, debt `B_t` chosen at `t`, a real debt value known at
its date, and `E_t` with pull-out and conditional monotone convergence: the flow condition at
every date plus the transversality condition at every date hold iff the stochastically
discounted valuation formula `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` holds at every
date (signed surpluses). -/
theorem valuation_sdf_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m P s D : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hsa : 𝔼.Adapted s) (hs : SurplusSummable 𝔼 m s) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hD1 : ∀ t, 𝔼.E t (D (t + 1)) = D (t + 1))
    (hx : 𝔼.Adapted (realDebt D P)) :
    ((∀ t, FlowOne (bondPrice 𝔼 m P) P s D t) ∧ ∀ t, TVC 𝔼 m (realDebt D P) t) ↔
      ∀ t, realDebt D P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs hx]
  have h : (∀ t, FlowOne (bondPrice 𝔼 m P) P s D t) ↔ FlowRec 𝔼 m s (realDebt D P) :=
    forall_congr' fun t => flowOne_iff_rec 𝔼 hP (hPa t) (hD1 t) hP0
  rw [h]

/-- Cochrane (2023), eq. (3.5), p. 55 (the price level is determined): if the valuation
formula holds and the present value is nonzero, `P_t = B_{t−1}/∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]`. -/
theorem price_eq_of_valuation {m s D P : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω} (hD : D t ξ ≠ 0)
    (hP0 : P t ξ ≠ 0) (hval : realDebt D P t ξ = pv 𝔼 m s t ξ) :
    P t ξ = D t ξ / pv 𝔼 m s t ξ := by
  rw [← hval, realDebt]
  field_simp

/-- Cochrane (2023), eq. (3.5), p. 55: given the debt `B_{t−1} ≠ 0`, the surpluses and the
discount factors, two nonzero price levels satisfying the valuation formula coincide. -/
theorem price_unique {m s D P P' : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω} (hD : D t ξ ≠ 0)
    (hP0 : P t ξ ≠ 0) (hP0' : P' t ξ ≠ 0) (hval : realDebt D P t ξ = pv 𝔼 m s t ξ)
    (hval' : realDebt D P' t ξ = pv 𝔼 m s t ξ) : P t ξ = P' t ξ := by
  rw [price_eq_of_valuation 𝔼 hD hP0 hval, price_eq_of_valuation 𝔼 hD hP0' hval']

/-! ### Ex-post returns as discount factors -/

/-- Cochrane (2023), §3.3, p. 56: `1 = R⁻¹_{t+1}R_{t+1}` state by state (the inverse return is
an ex-post discount factor). -/
theorem inv_return_expost {R : Ω → ℝ} (hR : ∀ ξ, R ξ ≠ 0) : (fun ξ => (R ξ)⁻¹ * R ξ) = 1 := by
  funext ξ
  simp [hR ξ]

/-- Cochrane (2023), §3.3, p. 56: `1 = E_t(R⁻¹_{t+1}R_{t+1})` for every `ExpectationSystem`
("using any set of probabilities"): the inverse return is an ex-ante discount factor. -/
theorem inv_return_sdf (t : ℕ) {R : Ω → ℝ} (hR : ∀ ξ, R ξ ≠ 0) :
    𝔼.E t (fun ξ => (R ξ)⁻¹ * R ξ) = 1 := by
  rw [inv_return_expost hR]
  exact 𝔼.const t 1

/-- Cochrane (2023), §3.3, p. 56: the ex-post real return from `t` to `t + 1` on one-period
debt, `R_{t+1} = (1/Q_t)(P_t/P_{t+1})`. -/
noncomputable def expostReturn (Q P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => (Q t ξ)⁻¹ * (P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), §3.3, pp. 55–56: with `Q_t = 1/(1+i_t)`,
`R_{t+1} = (1+i_t)P_t/P_{t+1}`. -/
theorem expostReturn_rate {Q P i : ℕ → Ω → ℝ} {t : ℕ}
    (hQi : Q t = fun ξ => (1 + i t ξ)⁻¹) :
    expostReturn Q P t = fun ξ => (1 + i t ξ) * (P t ξ / P (t + 1) ξ) := by
  funext ξ
  simp [expostReturn, hQi]

/-- Cochrane (2023), §3.3, p. 56: the flow condition `B_{t−1}/P_t = s_t + Q_tB_t/P_t` (for any
bond price `Q ≠ 0`) is, state by state, `B_{t−1}/P_t = s_t + R⁻¹_{t+1}B_t/P_{t+1}`. -/
theorem flow_expost {Q P s D : ℕ → Ω → ℝ} {t : ℕ} (hQ0 : ∀ ξ, Q t ξ ≠ 0)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    FlowOne Q P s D t ↔
      ∀ ξ, realDebt D P t ξ = s t ξ + (expostReturn Q P t ξ)⁻¹ * realDebt D P (t + 1) ξ := by
  refine forall_congr' fun ξ => ?_
  have h : (expostReturn Q P t ξ)⁻¹ * realDebt D P (t + 1) ξ = Q t ξ * D (t + 1) ξ / P t ξ := by
    have := hQ0 ξ
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    simp only [expostReturn, realDebt]
    field_simp
  rw [h, realDebt]

/-- Cochrane (2023), §3.3, p. 56: a process satisfying the ex-post flow
`x_t = s_t + g_t x_{t+1}` state by state, where `g_t = R⁻¹_{t+1}` is the realised one-period
discount factor. -/
def ExPostFlow (g s x : ℕ → Ω → ℝ) : Prop := ∀ t ξ, x t ξ = s t ξ + g t ξ * x (t + 1) ξ

/-- Cochrane (2023), eq. (3.6), p. 56, finite horizon (survey E12: the terminal product runs to
`T`, not `j`): `x_t = ∑_{j<T}(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j} + (∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}`
state by state. -/
theorem expost_iterate {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t T : ℕ) (ξ : Ω) :
    x t ξ = ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ + sdf g t T ξ * x (t + T) ξ := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, h (t + T) ξ, sdf_succ, Pi.mul_apply,
      show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), eq. (3.6), p. 56: state by state, the ex-post present-value partial sums
converge to `x_t` iff the terminal term `(∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}` tends to zero. -/
theorem expost_tendsto_iff {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t : ℕ) (ξ : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ) atTop (𝓝 (x t ξ)) ↔
      Tendsto (fun T => sdf g t T ξ * x (t + T) ξ) atTop (𝓝 0) := by
  have e : ∀ T, sdf g t T ξ * x (t + T) ξ =
      x t ξ - ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ := fun T => by
    rw [expost_iterate h t T ξ]
    ring
  simp_rw [e]
  constructor
  · intro hl
    simpa using (tendsto_const_nhds (x := x t ξ)).sub hl
  · intro hl
    have := (tendsto_const_nhds (x := x t ξ)).sub hl
    simp only [sub_sub_cancel, sub_zero] at this
    exact this

/-- Cochrane (2023), §3.3, p. 56 (the present value with ex-post returns): if in state `ξ` the
terminal term vanishes and the series converges (absolutely), then
`B_{t−1}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}`. -/
theorem expost_pv {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t : ℕ) (ξ : Ω)
    (hsum : Summable fun j => sdf g t j ξ * s (t + j) ξ)
    (hterm : Tendsto (fun T => sdf g t T ξ * x (t + T) ξ) atTop (𝓝 0)) :
    x t ξ = ∑' j, sdf g t j ξ * s (t + j) ξ :=
  tendsto_nhds_unique ((expost_tendsto_iff h t ξ).mpr hterm) hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), §3.3, p. 56 ("This equation holds ex-post, so it also holds ex-ante"):
for every `ExpectationSystem` and `x_t` known at `t`, the partial sums
`∑_{j<T}E_t[(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]` converge to `x_t` iff the expected terminal term
`E_t[(∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}]` tends to zero. -/
theorem expost_E_tendsto_iff {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (ξ : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E t (sdf g t j * s (t + j)) ξ) atTop
        (𝓝 (x t ξ)) ↔
      Tendsto (fun T => 𝔼.E t (sdf g t T * x (t + T)) ξ) atTop (𝓝 0) := by
  have e : ∀ T, 𝔼.E t (sdf g t T * x (t + T)) ξ =
      x t ξ - ∑ j ∈ Finset.range T, 𝔼.E t (sdf g t j * s (t + j)) ξ := fun T => by
    have hfun : x t = ∑ j ∈ Finset.range T, sdf g t j * s (t + j) + sdf g t T * x (t + T) := by
      funext ξ'
      rw [expost_iterate h t T ξ', Pi.add_apply, Finset.sum_apply]
      rfl
    have := congrFun (congrArg (𝔼.E t) hfun) ξ
    rw [hx, map_add, map_sum, Pi.add_apply, Finset.sum_apply] at this
    linarith
  simp_rw [e]
  constructor
  · intro hl
    simpa using (tendsto_const_nhds (x := x t ξ)).sub hl
  · intro hl
    have := (tendsto_const_nhds (x := x t ξ)).sub hl
    simp only [sub_sub_cancel, sub_zero] at this
    exact this

/-- Cochrane (2023), §3.3, p. 56 (displayed present value with ex-post returns): if the
expected terminal term goes to zero and the series of expectations converges (absolutely), then
`B_{t−1}/P_t = ∑_j E_t[(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]` under any `ExpectationSystem`; if
moreover the ex-post series converges absolutely in every state and `E_t` satisfies
conditional monotone convergence, this is `E_t[∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]`. -/
theorem expost_pv_E {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (ξ : Ω)
    (hsum : Summable fun j => 𝔼.E t (sdf g t j * s (t + j)) ξ)
    (hterm : Tendsto (fun T => 𝔼.E t (sdf g t T * x (t + T)) ξ) atTop (𝓝 0)) :
    x t ξ = ∑' j, 𝔼.E t (sdf g t j * s (t + j)) ξ ∧
      (MonotoneConvergence 𝔼 → (∀ ξ', Summable fun j => |sdf g t j ξ' * s (t + j) ξ'|) →
        x t ξ = 𝔼.E t (fun ξ' => ∑' j, sdf g t j ξ' * s (t + j) ξ') ξ) := by
  have h1 : x t ξ = ∑' j, 𝔼.E t (sdf g t j * s (t + j)) ξ :=
    tendsto_nhds_unique ((expost_E_tendsto_iff 𝔼 h hx ξ).mpr hterm)
      hsum.hasSum.tendsto_sum_nat
  refine ⟨h1, fun hMC habs => ?_⟩
  rw [h1]
  exact (E_tsum_abs 𝔼 hMC t (f := fun j => sdf g t j * s (t + j)) habs ξ).tsum_eq

/-- Cochrane (2023), §3.3, p. 56: taking `E_t` of the ex-post flow, `x_t = s_t + E_t[R⁻¹_{t+1}
x_{t+1}]` under any `ExpectationSystem` when `x_t` and `s_t` are known at `t`. -/
theorem expost_flow_E {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (hs : 𝔼.E t (s t) = s t) :
    x t = s t + 𝔼.E t (g t * x (t + 1)) := by
  have hfun : x t = s t + g t * x (t + 1) := by
    funext ξ
    exact h t ξ
  conv_lhs => rw [← hx, hfun, map_add, hs]

/-- Cochrane (2023), §3.3, p. 56, under perfect foresight: with the bond price
`Q_t = (Λ_{t+1}/Λ_t)P_t/P_{t+1}`, `m ≠ 0`, `P ≠ 0`, the ex-post discount factor `R⁻¹_{t+1}`
is exactly `m_t`, so (3.6) and (3.5) coincide. -/
theorem pf_expost_inv_eq_sdf {m P : ℕ → Unit → ℝ} (hm : ∀ s ξ, m s ξ ≠ 0)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    (fun ξ => (expostReturn (bondPrice perfectForesight m P) P t ξ)⁻¹) = m t := by
  funext ξ
  have := hm t ξ
  have := hP0 t ξ
  have := hP0 (t + 1) ξ
  simp only [expostReturn, bondPrice, perfectForesight, LinearMap.id_apply, Pi.mul_apply]
  field_simp

/-! ### (3.6) may explode while (3.5) is well defined -/

/-- Cochrane (2023), §3.3, p. 56 (example): the belief map of the "peso" information set-up
on `Option ℕ` (state `some n`: a fiscal regime switch at date `n`; `none`: no switch ever).
At date `t` a switch at `n ≤ t` is known; otherwise agents are certain the switch comes at
`t + 1`. -/
def pesoPt (t : ℕ) : Option ℕ → Option ℕ
  | some n => if n ≤ t then some n else some (t + 1)
  | none => some (t + 1)

/-- Cochrane (2023), §3.3, p. 56 (example): a switch at `n ≤ t` is known at `t`. -/
theorem pesoPt_some_le {t n : ℕ} (h : n ≤ t) : pesoPt t (some n) = some n := by
  simp [pesoPt, h]

/-- Cochrane (2023), §3.3, p. 56 (example): before the switch, agents believe it comes at
`t + 1`. -/
theorem pesoPt_some_gt {t n : ℕ} (h : t < n) : pesoPt t (some n) = some (t + 1) := by
  simp [pesoPt, show ¬ n ≤ t by omega]

/-- Cochrane (2023), §3.3, p. 56 (example): on the never-switch path, agents believe the switch
comes at `t + 1`. -/
theorem pesoPt_none (t : ℕ) : pesoPt t none = some (t + 1) := rfl

/-- Cochrane (2023), §3.3, p. 56 (example): later beliefs do not change the believed state
of an earlier date's belief. -/
theorem pesoPt_pt {s t : ℕ} (h : s ≤ t) (ξ : Option ℕ) : pesoPt t (pesoPt s ξ) = pesoPt s ξ := by
  have key : pesoPt t (some (s + 1)) = some (s + 1) := by
    rcases Nat.lt_or_ge t (s + 1) with h1 | h1
    · rw [pesoPt_some_gt h1, show t = s by omega]
    · exact pesoPt_some_le h1
  cases ξ with
  | none => rw [pesoPt_none, key]
  | some n =>
    rcases Nat.lt_or_ge s n with h1 | h1
    · rw [pesoPt_some_gt h1, key]
    · rw [pesoPt_some_le h1, pesoPt_some_le (h1.trans h)]

/-- Cochrane (2023), §3.3, p. 56 (example): an earlier belief evaluated at a later belief is
the earlier belief. -/
theorem pesoPt_pt' {s t : ℕ} (h : s ≤ t) (ξ : Option ℕ) :
    pesoPt s (pesoPt t ξ) = pesoPt s ξ := by
  cases ξ with
  | none => rw [pesoPt_none, pesoPt_none, pesoPt_some_gt (by omega)]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, pesoPt_some_gt (by omega), pesoPt_some_gt (by omega)]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 ("using any set of probabilities"): the expectation system
`E_t x = x ∘ pesoPt t` of the peso example. -/
def pesoSystem : ExpectationSystem (Option ℕ) where
  E := fun t => LinearMap.funLeft ℝ ℝ (pesoPt t)
  const := fun _ _ => rfl
  mono := fun _ _ _ h ξ => h _
  tower := fun h x => by
    funext ξ
    simp only [LinearMap.funLeft_apply, pesoPt_pt h]
  known := fun h x => by
    funext ξ
    simp only [LinearMap.funLeft_apply, pesoPt_pt' h]

/-- Cochrane (2023), §3.3, p. 56 (example): `E_t x (ξ) = x (pesoPt t ξ)`. -/
theorem pesoSystem_E (t : ℕ) (x : Option ℕ → ℝ) (ξ : Option ℕ) :
    pesoSystem.E t x ξ = x (pesoPt t ξ) := rfl

/-- Cochrane (2023), §3.3, p. 56 (example): the peso system has the pull-out property. -/
theorem pesoSystem_pullOut : pesoSystem.PullOut := by
  intro t a y ha
  funext ξ
  have h := congrFun ha ξ
  simp only [pesoSystem_E] at h
  simp only [pesoSystem_E, Pi.mul_apply, h]

/-- Cochrane (2023), §3.3, p. 56 (example): the peso system satisfies conditional monotone
convergence. -/
theorem pesoSystem_monotoneConvergence : MonotoneConvergence pesoSystem := by
  intro t f _ hs ξ
  simp only [pesoSystem_E]
  exact (hs _).hasSum

/-- Cochrane (2023), §3.3, p. 56 (example): surpluses `−1` before the switch and `2` from the
switch date on. -/
def pesoS (t : ℕ) : Option ℕ → ℝ
  | some n => if n ≤ t then 2 else -1
  | none => -1

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value, `4` after the switch and `1`
before. -/
def pesoX (t : ℕ) : Option ℕ → ℝ
  | some n => if n ≤ t then 4 else 1
  | none => 1

/-- Cochrane (2023), §3.3, p. 56 (example): the values of `pesoX` and `pesoS` after and
before the switch. -/
theorem peso_values (t n : ℕ) :
    (n ≤ t → pesoX t (some n) = 4 ∧ pesoS t (some n) = 2) ∧
      (t < n → pesoX t (some n) = 1 ∧ pesoS t (some n) = -1) ∧
      pesoX t none = 1 ∧ pesoS t none = -1 := by
  refine ⟨fun h => ?_, fun h => ?_, rfl, rfl⟩
  · simp [pesoX, pesoS, h]
  · simp [pesoX, pesoS, show ¬ n ≤ t by omega]

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value is known at its date. -/
theorem pesoX_adapted : pesoSystem.Adapted pesoX := by
  intro t
  funext ξ
  rw [pesoSystem_E]
  cases ξ with
  | none => rw [pesoPt_none, (peso_values t (t + 1)).2.1 (by omega) |>.1, (peso_values t 0).2.2.1]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, (peso_values t (t + 1)).2.1 (by omega) |>.1,
        (peso_values t n).2.1 h1 |>.1]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 (example): surpluses are known at their date. -/
theorem pesoS_adapted : pesoSystem.Adapted pesoS := by
  intro t
  funext ξ
  rw [pesoSystem_E]
  cases ξ with
  | none => rw [pesoPt_none, (peso_values t (t + 1)).2.1 (by omega) |>.2, (peso_values t 0).2.2.2]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, (peso_values t (t + 1)).2.1 (by omega) |>.2,
        (peso_values t n).2.1 h1 |>.2]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 (example): the flow `x_t = s_t + ½E_t x_{t+1}` holds in every
state at every date. -/
theorem pesoX_flow (t : ℕ) (ξ : Option ℕ) :
    pesoX t ξ = pesoS t ξ + 1 / 2 * pesoX (t + 1) (pesoPt t ξ) := by
  have hsw : pesoX (t + 1) (some (t + 1)) = 4 := ((peso_values (t + 1) (t + 1)).1 le_rfl).1
  cases ξ with
  | none =>
    rw [pesoPt_none, hsw, (peso_values t 0).2.2.1, (peso_values t 0).2.2.2]
    norm_num
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, hsw, ((peso_values t n).2.1 h1).1, ((peso_values t n).2.1 h1).2]
      norm_num
    · rw [pesoPt_some_le h1, ((peso_values t n).1 h1).1, ((peso_values t n).1 h1).2,
        ((peso_values (t + 1) n).1 (by omega)).1]
      norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value lies in `[1, 4]`. -/
theorem pesoX_bounds (t : ℕ) (ξ : Option ℕ) : 1 ≤ pesoX t ξ ∧ pesoX t ξ ≤ 4 := by
  cases ξ with
  | none => simp [pesoX]
  | some n =>
    simp only [pesoX]
    split_ifs <;> norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): `|s| ≤ 2`. -/
theorem pesoS_abs_le (t : ℕ) (ξ : Option ℕ) : |pesoS t ξ| ≤ 2 := by
  cases ξ with
  | none => norm_num [pesoS]
  | some n =>
    simp only [pesoS]
    split_ifs <;> norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): the nominal price level `P_t = 1/x_t` with
one unit of nominal debt `B_{t−1} = 1` outstanding. -/
noncomputable def pesoP (t : ℕ) (ξ : Option ℕ) : ℝ := (pesoX t ξ)⁻¹

/-- Cochrane (2023), §3.3, p. 56 (example): along the never-switch path the realised ex-post
return on debt is `R_{t+1} = 1/2`. -/
theorem pesoReturn_none (t : ℕ) :
    expostReturn (bondPrice pesoSystem (fun _ _ => 1 / 2) pesoP) pesoP t none = 1 / 2 := by
  simp only [expostReturn, bondPrice, pesoSystem_E, Pi.mul_apply, pesoP, pesoPt, pesoX,
    show ¬ t + 1 ≤ t by omega, le_refl, ↓reduceIte]
  norm_num

/-- Cochrane (2023), §3.3, p. 56: "It is possible that the present value is well defined using
marginal utility or the discount factor as in (3.5), but the present value and terminal
condition using ex-post returns (3.6) explode." In the peso economy (risk-neutral discount
factor `1/2`, one unit of nominal one-period debt, `P_t = 1/x_t`, bond price
`Q_t = E_t[½P_t/P_{t+1}]`, expectations `pesoSystem` with pull-out and conditional monotone
convergence): the flow condition, the transversality condition and the valuation formula (3.5)
hold at every date in every state, surpluses have absolutely summable present values; but along
the realised never-switch path the ex-post flow holds with `R⁻¹_{t+1} = 2`, and the ex-post
present-value partial sums of (3.6) tend to `−∞` while the terminal term tends to `+∞`.
(Along that path, agents at every date assign probability one to a switch next period.) -/
theorem expost_may_diverge :
    let m : ℕ → Option ℕ → ℝ := fun _ _ => 1 / 2
    let D : ℕ → Option ℕ → ℝ := fun _ _ => 1
    let g : ℕ → Option ℕ → ℝ :=
      fun t ξ => (expostReturn (bondPrice pesoSystem m pesoP) pesoP t ξ)⁻¹
    (∀ t, FlowOne (bondPrice pesoSystem m pesoP) pesoP pesoS D t) ∧
      (∀ t, TVC pesoSystem m (realDebt D pesoP) t) ∧
      (∀ t, realDebt D pesoP t = pv pesoSystem m pesoS t) ∧
      SurplusSummable pesoSystem m pesoS ∧
      ExPostFlow g pesoS (realDebt D pesoP) ∧
      (∀ t, g t none = 2) ∧
      Tendsto (fun T => ∑ j ∈ Finset.range T, sdf g 0 j none * pesoS j none) atTop atBot ∧
      Tendsto (fun T => sdf g 0 T none * realDebt D pesoP T none) atTop atTop := by
  intro m D g
  have hxeq : realDebt D pesoP = pesoX := by
    funext t ξ
    simp [realDebt, D, pesoP]
  have hPpos : ∀ s ξ, 0 < pesoP s ξ := fun s ξ =>
    inv_pos.mpr (lt_of_lt_of_le one_pos (pesoX_bounds s ξ).1)
  have hP0 : ∀ s ξ, pesoP s ξ ≠ 0 := fun s ξ => (hPpos s ξ).ne'
  have hPa : pesoSystem.Adapted pesoP := by
    intro t
    funext ξ
    have h := congrFun (pesoX_adapted t) ξ
    simp only [pesoSystem_E] at h
    simp only [pesoSystem_E, pesoP, h]
  have hmE : ∀ s, pesoSystem.E (s + 1) (m s) = m s := fun s => pesoSystem.const (s + 1) (1 / 2)
  have hm0 : ∀ s ξ, 0 ≤ m s ξ := fun _ _ => by norm_num [m]
  have hsdf : ∀ t n, sdf m t n = fun _ => (1 / 2 : ℝ) ^ n := fun t n => sdf_const _ t n
  have hD1 : ∀ t, pesoSystem.E t (D (t + 1)) = D (t + 1) := fun t => pesoSystem.const t 1
  -- the flow condition
  have hflow : ∀ t, FlowOne (bondPrice pesoSystem m pesoP) pesoP pesoS D t := by
    intro t
    rw [flowOne_iff_rec pesoSystem pesoSystem_pullOut (hPa t) (hD1 t) hP0, hxeq]
    funext ξ
    rw [Pi.add_apply, pesoSystem_E, Pi.mul_apply]
    exact pesoX_flow t ξ
  -- surplus summability
  have hss : SurplusSummable pesoSystem m pesoS := by
    intro t ξ
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 2)
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      exact mul_nonneg (by positivity) (abs_nonneg _)
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      have := pesoS_abs_le (t + n) (pesoPt t ξ)
      have hp : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      nlinarith
  -- the transversality condition
  have htvc : ∀ t, TVC pesoSystem m (realDebt D pesoP) t := by
    intro t ξ
    rw [hxeq]
    have hlim : Tendsto (fun N : ℕ => 4 * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 4
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hlim
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      exact mul_nonneg (by positivity) (by linarith [(pesoX_bounds (t + N) (pesoPt t ξ)).1])
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      have := (pesoX_bounds (t + N) (pesoPt t ξ)).2
      have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
      nlinarith
  -- the valuation formula (3.5)
  have hxa : pesoSystem.Adapted (realDebt D pesoP) := by rw [hxeq]; exact pesoX_adapted
  have hval := ((flow_tvc_iff_pv pesoSystem pesoSystem_monotoneConvergence pesoSystem_pullOut
    hmE hm0 pesoS_adapted hss hxa).mp ⟨fun t => (flowOne_iff_rec pesoSystem pesoSystem_pullOut
      (hPa t) (hD1 t) hP0).mp (hflow t), htvc⟩)
  -- the ex-post flow
  have hQ0 : ∀ t ξ, bondPrice pesoSystem m pesoP t ξ ≠ 0 := by
    intro t ξ
    simp only [bondPrice, pesoSystem_E, Pi.mul_apply, m]
    exact (mul_pos (by norm_num) (div_pos (hPpos _ _) (hPpos _ _))).ne'
  have hexp : ExPostFlow g pesoS (realDebt D pesoP) := fun t ξ =>
    (flow_expost (hQ0 t) hP0).mp (hflow t) ξ
  have hg : ∀ t, g t none = 2 := fun t => by
    simp only [g, m]
    rw [pesoReturn_none]
    norm_num
  have hsdfg : ∀ j, sdf g 0 j none = 2 ^ j := fun j => by
    simp only [sdf, Finset.prod_apply, zero_add, hg, Finset.prod_const, Finset.card_range]
  refine ⟨hflow, htvc, hval, hss, hexp, hg, ?_, ?_⟩
  · have e : ∀ T, ∑ j ∈ Finset.range T, sdf g 0 j none * pesoS j none =
        -(2 : ℝ) ^ T + 1 := fun T => by
      simp only [hsdfg, pesoS, mul_neg, mul_one, Finset.sum_neg_distrib]
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      ring
    simp_rw [e]
    exact (tendsto_neg_atTop_atBot.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).atBot_add
      tendsto_const_nhds
  · have e : ∀ T, sdf g 0 T none * realDebt D pesoP T none = (2 : ℝ) ^ T := fun T => by
      rw [hsdfg, hxeq]
      simp [pesoX]
    simp_rw [e]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)

/-! ### On a finite event tree (3.6) cannot explode -/

/-- Cochrane (2023), §3.3, p. 56 (finite trees): on a finite event tree a variable is known at
`t` iff it is constant on the date-`t` information cells. -/
theorem finiteTree_known_iff {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    (t : ℕ) (y : Ω' → ℝ) :
    T.toExpectationSystem.E t y = y ↔ ∀ a b, T.info t a b → y a = y b := by
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  constructor
  · intro h a b hab
    rw [← h]
    exact T.condE_congr y hab
  · intro h
    funext ξ
    exact T.condE_of_const_on_cell fun ξ' h' => h ξ' ξ h'

/-- Cochrane (2023), §3.3, p. 56 (finite trees): information on a finite tree stops being
refined after some date `T₀` (the set of indistinguishable pairs is a decreasing sequence of
finite sets). -/
theorem finiteTree_info_stable {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') :
    ∃ T0, ∀ t, T0 ≤ t → ∀ a b, T.info t a b ↔ T.info T0 a b := by
  classical
  let F : ℕ → Finset (Ω' × Ω') := fun t => Finset.univ.filter fun p => T.info t p.1 p.2
  have hsub : ∀ {u v : ℕ}, u ≤ v → F v ⊆ F u := fun huv p hp => by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact T.refines huv _ _ hp
  have hex : ∃ k, ∃ t, (F t).card = k := ⟨(F 0).card, 0, rfl⟩
  obtain ⟨T0, hT0⟩ := Nat.find_spec hex
  refine ⟨T0, fun t ht a b => ⟨fun h => T.refines ht a b h, fun h => ?_⟩⟩
  have hmin : Nat.find hex ≤ (F t).card := Nat.find_min' hex ⟨t, rfl⟩
  have heq : F t = F T0 := Finset.eq_of_subset_of_card_le (hsub ht) (by omega)
  have hmem : (a, b) ∈ F T0 := by simp [F, h]
  rw [← heq] at hmem
  simpa [F] using hmem

/-- Cochrane (2023), §3.3, p. 56 (finite trees): after the date `T₀` at which information stops
being refined, whatever will be known is already known. -/
theorem finiteTree_eventually_known {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') :
    ∃ T0, ∀ t k, T0 ≤ t → t ≤ k → ∀ y, T.toExpectationSystem.E k y = y →
      T.toExpectationSystem.E t y = y := by
  obtain ⟨T0, hT0⟩ := finiteTree_info_stable T
  refine ⟨T0, fun t k ht htk y hy => ?_⟩
  rw [finiteTree_known_iff] at hy ⊢
  intro a b hab
  exact hy a b ((hT0 k (ht.trans htk) a b).mpr ((hT0 t ht a b).mp hab))

/-- Cochrane (2023), §3.3, p. 56: the flow condition `B_{t−1}/P_t = s_t + Q_tB_t/P_t` at every
date gives the ex-post flow with `R⁻¹_{t+1} = (expostReturn Q P t)⁻¹` in every state, also
where `Q_t = 0` (then both discount factors are zero). -/
theorem expostFlow_of_flowOne {Q P s D : ℕ → Ω → ℝ} (hflow : ∀ t, FlowOne Q P s D t)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    ExPostFlow (fun t ξ => (expostReturn Q P t ξ)⁻¹) s (realDebt D P) := by
  intro t ξ
  have h := hflow t ξ
  by_cases hQ : Q t ξ = 0
  · simpa [expostReturn, realDebt, hQ] using h
  · simp only [expostReturn, realDebt]
    rw [h]
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    field_simp

/-- Cochrane (2023), §3.3, p. 56, the precise true statement behind "(3.6) may explode" on a
finite event tree (genuine uncertainty, every state of positive probability): if the flow
condition with SDF bond prices `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]` and the transversality
condition hold at every date (hence (3.5), `valuation_sdf_iff`), then in every state and at
every date the ex-post present value (3.6) with discount factors
`g_t = R⁻¹_{t+1}`, `R_{t+1} = (1/Q_t)P_t/P_{t+1}`, converges
absolutely, its terminal term tends to zero, and
`B_{t−1}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}`. So the explosion of `expost_may_diverge`
can only happen along a path to which the expectation system gives zero probability. -/
theorem finiteTree_expost_pv {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {m P s D : ℕ → Ω' → ℝ} (hm : ∀ k, T.toExpectationSystem.E (k + 1) (m k) = m k)
    (hm0 : ∀ k ξ, 0 ≤ m k ξ) (hsa : T.toExpectationSystem.Adapted s)
    (hs : SurplusSummable T.toExpectationSystem m s) (hPa : T.toExpectationSystem.Adapted P)
    (hP0 : ∀ k ξ, P k ξ ≠ 0)
    (hflow : ∀ t, FlowOne (bondPrice T.toExpectationSystem m P) P s D t)
    (htvc : ∀ t, TVC T.toExpectationSystem m (realDebt D P) t)
    (hx : T.toExpectationSystem.Adapted (realDebt D P)) {g : ℕ → Ω' → ℝ}
    (hgdef : g = fun k ξ' => (expostReturn (bondPrice T.toExpectationSystem m P) P k ξ')⁻¹)
    (t : ℕ) (ξ : Ω') :
    Summable (fun j => |sdf g t j ξ * s (t + j) ξ|) ∧
      Tendsto (fun N => sdf g t N ξ * realDebt D P (t + N) ξ) atTop (𝓝 0) ∧
      realDebt D P t ξ = ∑' j, sdf g t j ξ * s (t + j) ξ := by
  have hPO := ExpectationsFiniteTree.finiteTree_pullOut T
  obtain ⟨T0, hT0⟩ := finiteTree_eventually_known T
  -- after `T₀` the ex-post discount factor is the SDF
  have hg : ∀ k, T0 ≤ k → g k = m k := by
    intro k hk
    funext ξ'
    have hz : T.toExpectationSystem.E k (m k * fun ξ => P k ξ / P (k + 1) ξ) =
        m k * fun ξ => P k ξ / P (k + 1) ξ := by
      refine hT0 k (k + 1) hk (Nat.le_succ k) _ ?_
      rw [finiteTree_known_iff]
      intro a b hab
      have h1 := (finiteTree_known_iff T (k + 1) (m k)).mp (hm k) a b hab
      have h2 := (finiteTree_known_iff T k (P k)).mp (hPa k) a b
        (T.refines (Nat.le_succ k) a b hab)
      have h3 := (finiteTree_known_iff T (k + 1) (P (k + 1))).mp (hPa (k + 1)) a b hab
      simp only [Pi.mul_apply, h1, h2, h3]
    have hQ : bondPrice T.toExpectationSystem m P k ξ' = m k ξ' * (P k ξ' / P (k + 1) ξ') := by
      rw [bondPrice, hz]
      rfl
    have ha : P k ξ' / P (k + 1) ξ' ≠ 0 := div_ne_zero (hP0 _ _) (hP0 _ _)
    simp only [hgdef, expostReturn, hQ]
    by_cases hmz : m k ξ' = 0
    · simp [hmz]
    · have := hP0 k ξ'
      have := hP0 (k + 1) ξ'
      field_simp
  have hsdfg : ∀ k, T0 ≤ k → ∀ n, sdf g k n = sdf m k n := by
    intro k hk n
    simp only [sdf]
    exact Finset.prod_congr rfl fun j _ => hg (k + j) (by omega)
  -- after `T₀` conditional expectations of later-known variables are pathwise values
  have hE : ∀ k, T0 ≤ k → ∀ n (y : Ω' → ℝ), T.toExpectationSystem.E (k + n) y = y →
      T.toExpectationSystem.E k y = y := fun k hk n y hy =>
    hT0 k (k + n) hk (by omega) y hy
  have habs : ∀ k n, T.toExpectationSystem.E (k + n) (fun ξ => |s (k + n) ξ|) =
      fun ξ => |s (k + n) ξ| := by
    intro k n
    rw [finiteTree_known_iff]
    intro a b hab
    rw [(finiteTree_known_iff T _ _).mp (hsa (k + n)) a b hab]
  have hpath_s : ∀ k, T0 ≤ k → ∀ n, T.toExpectationSystem.E k
      (sdf m k n * fun ξ => |s (k + n) ξ|) ξ = sdf m k n ξ * |s (k + n) ξ| := by
    intro k hk n
    rw [hE k hk n _ (known_mul _ hPO (sdf_known _ hPO hm k n) (habs k n))]
    rfl
  have hpath_x : ∀ k, T0 ≤ k → ∀ N, T.toExpectationSystem.E k
      (sdf m k N * realDebt D P (k + N)) ξ = sdf m k N ξ * realDebt D P (k + N) ξ := by
    intro k hk N
    rw [hE k hk N _ (known_mul _ hPO (sdf_known _ hPO hm k N) (hx (k + N)))]
    rfl
  -- pass from `t` to `t₁ = max t T₀`
  obtain ⟨d, hd⟩ : ∃ d, t + d = max t T0 := ⟨max t T0 - t, by omega⟩
  have ht1 : T0 ≤ max t T0 := le_max_right _ _
  have hsum1 : Summable fun n => sdf m (max t T0) n ξ * |s (max t T0 + n) ξ| :=
    (hs (max t T0) ξ).congr fun n => hpath_s _ ht1 n
  have hterm1 : Tendsto (fun N => sdf m (max t T0) N ξ * realDebt D P (max t T0 + N) ξ) atTop
      (𝓝 0) := (htvc (max t T0) ξ).congr fun N => hpath_x _ ht1 N
  have hsplit : ∀ n, sdf g t (n + d) ξ = sdf g t d ξ * sdf m (max t T0) n ξ := by
    intro n
    rw [add_comm n d, sdf_add, hd, hsdfg _ ht1]
    rfl
  have hA : Summable fun n => |sdf g t (n + d) ξ * s (t + (n + d)) ξ| := by
    refine (hsum1.mul_left |sdf g t d ξ|).congr fun n => ?_
    have h0 : |sdf m (max t T0) n ξ| = sdf m (max t T0) n ξ :=
      abs_of_nonneg (sdf_nonneg hm0 (max t T0) n ξ)
    have e : sdf g t (n + d) ξ * s (t + (n + d)) ξ =
        sdf g t d ξ * (sdf m (max t T0) n ξ * s (max t T0 + n) ξ) := by
      rw [hsplit, show t + (n + d) = max t T0 + n by omega, mul_assoc]
    simp only [e, abs_mul, h0]
  have hsumA := (summable_nat_add_iff (f := fun j => |sdf g t j ξ * s (t + j) ξ|) d).mp hA
  have hB : Tendsto (fun N : ℕ => sdf g t (N + d) ξ * realDebt D P (t + (N + d)) ξ) atTop
      (𝓝 (0 : ℝ)) := by
    have h1 : (fun N => sdf g t (N + d) ξ * realDebt D P (t + (N + d)) ξ) =
        fun N => sdf g t d ξ * (sdf m (max t T0) N ξ * realDebt D P (max t T0 + N) ξ) := by
      funext N
      rw [hsplit, show t + (N + d) = max t T0 + N by omega, mul_assoc]
    rw [h1]
    have h2 := hterm1.const_mul (sdf g t d ξ)
    rwa [mul_zero] at h2
  have hterm := (tendsto_add_atTop_iff_nat
    (f := fun N => sdf g t N ξ * realDebt D P (t + N) ξ) d).mp hB
  have hflowg : ExPostFlow g s (realDebt D P) := by
    rw [hgdef]
    exact expostFlow_of_flowOne hflow hP0
  exact ⟨hsumA, hterm, expost_pv hflowg t ξ hsumA.of_abs hterm⟩

/-! ### Long-term debt: the portfolio return (3.7) and the flow identity (3.8) -/

/-- Cochrane (2023), eq. (3.7), p. 56: the ex-post real return on the whole debt portfolio,
`R_{t+1} = ∑_jQ_{t+1}^{(t+1+j)}B_t^{(t+1+j)} / ∑_jQ_t^{(t+1+j)}B_t^{(t+1+j)} · P_t/P_{t+1}`
(maximum maturity `K`). -/
noncomputable def portfolioReturn (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ξ => mktValue K Q B (t + 1) ξ / purchaseValue K Q B t ξ * (P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), eqs. (3.2), (3.7)–(3.8), pp. 53, 56–57: with maximum maturity `K`,
maturing bonds worth face value, `P ≠ 0`, and a nonzero market value of the debt at `t + 1`,
the flow condition (3.2) holds iff the flow identity with the portfolio return (3.8)
`∑_jQ_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = s_t + R⁻¹_{t+1}∑_jQ_{t+1}^{(t+1+j)}B_t^{(t+1+j)}/P_{t+1}`
holds (exact, no pricing assumption). -/
theorem flowLT_iff_3_8 {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) {t : ℕ} (hQ0 : Q t 0 = 1) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hV : ∀ ξ, mktValue K Q B (t + 1) ξ ≠ 0) :
    FlowLT K P s Q B t ↔ ∀ ξ, realValue K Q B P t ξ =
      s t ξ + (portfolioReturn K Q B P t ξ)⁻¹ * realValue K Q B P (t + 1) ξ := by
  rw [flowLT_iff_value hK hQ0 (hP0 t), funext_iff]
  refine forall_congr' fun ξ => ?_
  have h : (portfolioReturn K Q B P t ξ)⁻¹ * realValue K Q B P (t + 1) ξ =
      purchaseValue K Q B t ξ / P t ξ := by
    have := hV ξ
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    simp only [portfolioReturn, realValue]
    by_cases hp : purchaseValue K Q B t ξ = 0
    · simp [hp]
    · field_simp
  rw [Pi.add_apply, h]

/-- Cochrane (2023), p. 57 ("We iterate again"): with long-term debt, if (3.2) holds at every
date and the market value of the debt is never zero, then in every state where the terminal
term vanishes and the series converges absolutely,
`∑_jQ_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}` with the portfolio
return (3.7). -/
theorem expostLT_pv {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) (hQ0 : ∀ t, Q t 0 = 1) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hV : ∀ t ξ, mktValue K Q B t ξ ≠ 0) (hflow : ∀ t, FlowLT K P s Q B t) (t : ℕ) (ξ : Ω)
    (hsum : Summable fun j =>
      sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t j ξ * s (t + j) ξ)
    (hterm : Tendsto (fun T => sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t T ξ *
      realValue K Q B P (t + T) ξ) atTop (𝓝 0)) :
    realValue K Q B P t ξ =
      ∑' j, sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t j ξ * s (t + j) ξ := by
  have h : ExPostFlow (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) s (realValue K Q B P) :=
    fun k ξ' => (flowLT_iff_3_8 hK (hQ0 k) hP0 (hV (k + 1))).mp (hflow k) ξ'
  exact expost_pv h t ξ hsum hterm

end Cochrane.Generality.StochasticDiscount

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in the government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.4, pp. 57–62.

Timing convention: `B t` and `M t` are the book's `B_{t−1}` and `M_{t−1}`, the nominal bonds and
non-interest-bearing money held from period `t − 1` into period `t`; `i t` is the book's `i_t`, the
rate on the bonds `B (t + 1)` sold at date `t`. `Λ` is a positive stochastic discount factor and
bonds are priced by `1/(1 + i_t) = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]` (p. 55).

## Main results

* `telescope`, `pv_iff_tvc`: for `Y_t = c_t + E_t Y_{t+1}` (signed `c`), the partial-sum identity
  and: given (absolute) summability, the present-value relation holds iff the terminal term
  `E_t Y_{t+T} → 0`.
* `E_next`: the nominal Euler equation `E_t[Λ_{t+1} D/P_{t+1}] = Λ_t D/((1+i_t)P_t)` for `D`
  known at `t` (needs the pull-out property).
* `pv_book_iff`: the general flow-to-valuation theorem in the book's form, both directions.
* (3.12) and its second form: `pv_3_12`, `pv_3_12b`; footnote 2 weight `weight_identity`.
* (3.10), (3.11): `pv_3_10`, `pv_3_11` (each: valuation ⇔ its own transversality condition).
* Survey error E13 ("these equivalent expressions", p. 57): `tvc_split`, `pv_3_10_iff_3_11`
  (equivalent under the money transversality condition), `pv_3_10_iff_money_tvc` (given (3.11),
  (3.10) holds iff the money transversality condition holds), and the counterexample
  `money_bubble` ((3.11) holds at every date, (3.10) at none).
* (3.13)–(3.15): `exPostReturn`, `flow_3_14`, `iterate_discount`, `pv_discount_iff`,
  `pv_3_15_finite`, `pv_3_15_iff`.
* (3.16), the zero bound, and survey error E14: `zero_bound_valuation` (from (3.10)),
  `full_interest_valuation` (`i = i^m`), `zero_bound_beta`, `zero_bound_E_outside`,
  `zero_bound_flow_total`, and `zero_bound_not_from_3_11` (the printed derivation "following
  (3.11)" fails without the money transversality condition).
* §3.4.2: `seigniorage_offset_term`, `seigniorage_offset_valuation`, `seigniorage_offset_flow`,
  `full_interest_split_irrelevant`, `passive_split`, and the arithmetic `seigniorage_2019`,
  `seigniorage_1980s`.
-/

namespace Cochrane.Generality.Money

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Telescoping and the transversality condition -/

/-- Cochrane (2023), footnote 1, p. 58 ("and iterate"): if `Y_t = c_t + E_t Y_{t+1}` with `Y`
adapted, then `Y_t = ∑_{j<T} E_t c_{t+j} + E_t Y_{t+T}`. -/
theorem telescope {Y c : ℕ → Ω → ℝ} (hYa : 𝔼.Adapted Y)
    (hY : ∀ t, Y t = c t + 𝔼.E t (Y (t + 1))) (t T : ℕ) :
    Y t = ∑ j ∈ Finset.range T, 𝔼.E t (c (t + j)) + 𝔼.E t (Y (t + T)) := by
  induction T with
  | zero => simp [hYa t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have h := congrArg (𝔼.E t) (hY (t + T))
    rw [map_add, 𝔼.tower (Nat.le_add_right t T)] at h
    rw [h, ← add_assoc t T 1]

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: for `Y_t = c_t + E_t Y_{t+1}` and a summable
series `∑_j E_t c_{t+j}` (in `ℝ`, summable means absolutely summable; the `c` are signed), the
transversality condition `E_t Y_{t+T} → 0` holds iff `Y_t = ∑_j E_t c_{t+j}`. -/
theorem pv_iff_tvc {Y c : ℕ → Ω → ℝ} (hYa : 𝔼.Adapted Y)
    (hY : ∀ t, Y t = c t + 𝔼.E t (Y (t + 1))) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E t (c (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop (𝓝 0) ↔
      Y t ω = ∑' j, 𝔼.E t (c (t + j)) ω := by
  have he : ∀ T, 𝔼.E t (Y (t + T)) ω =
      Y t ω - ∑ j ∈ Finset.range T, 𝔼.E t (c (t + j)) ω := by
    intro T
    have h := congrFun (telescope 𝔼 hYa hY t T) ω
    simp only [Pi.add_apply, Finset.sum_apply] at h
    linarith
  have hlim : Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop
      (𝓝 (Y t ω - ∑' j, 𝔼.E t (c (t + j)) ω)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-! ### The money economy -/

/-- Cochrane (2023), p. 55: bonds are priced by the stochastic discount factor,
`Q_t = 1/(1 + i_t) = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]`. -/
def BondEuler (Λ P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / (1 + i t ω)) =
    𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * (P t ω / P (t + 1) ω))

variable (Λ P i M B : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.3–3.4, pp. 55–59: the standing assumptions. `Λ > 0` is the stochastic
discount factor, `P > 0` the price level; the nominal discount factor `Λ_t/P_t` and `Λ_t⁻¹` are
known at `t`; bonds and money are known at `t` and predetermined (`B (t+1)`, `M (t+1)` are chosen
at `t`); `1 + i_t > 0`; bonds are priced by the stochastic discount factor (p. 55); and the
conditional expectations have the pull-out property. -/
structure Standing where
  pullOut : 𝔼.PullOut
  disc_pos : ∀ t ω, 0 < Λ t ω
  price_pos : ∀ t ω, 0 < P t ω
  nominal_adapted : 𝔼.Adapted (fun t ω => Λ t ω / P t ω)
  disc_inv_adapted : 𝔼.Adapted (fun t ω => (Λ t ω)⁻¹)
  bonds_adapted : 𝔼.Adapted B
  money_adapted : 𝔼.Adapted M
  bonds_pre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)
  money_pre : ∀ t, 𝔼.E t (M (t + 1)) = M (t + 1)
  rate_gt : ∀ t ω, -1 < i t ω
  euler : BondEuler 𝔼 Λ P i

variable {Λ P i M B}

/-- Cochrane (2023), (3.9), p. 57: the flow condition with non-interest-bearing money,
`B_{t−1} + M_{t−1} = P_t s_t + B_t/(1 + i_t) + M_t`. -/
def Flow39 (P s i M B : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, B t ω + M t ω = P t ω * s t ω + B (t + 1) ω / (1 + i t ω) + M (t + 1) ω

/-- Cochrane (2023), p. 58: the flow condition when money pays interest `i^m` (discount basis),
`B_{t−1} + M_{t−1} = P_t s_t + B_t/(1 + i_t) + M_t/(1 + i^m_t)`. -/
def FlowIm (P s i im M B : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, B t ω + M t ω =
    P t ω * s t ω + B (t + 1) ω / (1 + i t ω) + M (t + 1) ω / (1 + im t ω)

/-- Cochrane (2023), pp. 57–58: (3.9) is the flow condition with `i^m = 0`. -/
theorem flow39_iff_flowIm (P s i M B : ℕ → Ω → ℝ) :
    Flow39 P s i M B ↔ FlowIm P s i (fun _ _ => 0) M B := by
  simp only [Flow39, FlowIm, add_zero, div_one]

/-- Cochrane (2023), (3.10)–(3.12), pp. 58–59: the present-value relation
`X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) d_{t+j}]` for the nominal liabilities `X`. -/
def PVRel (Λ P X d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  X t ω / P t ω = ∑' j, 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω

/-- Cochrane (2023), p. 55: the transversality condition `lim_T E_t[Λ_{t+T} X_{t+T}/P_{t+T}] = 0`
(the book divides by the positive date-`t` constant `Λ_t`). -/
def TVC (Λ P X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  Tendsto (fun T => 𝔼.E t (fun ω' => Λ (t + T) ω' * (X (t + T) ω' / P (t + T) ω')) ω) atTop
    (𝓝 0)

/-- Cochrane (2023), (3.10)–(3.12): summability of the present-value series. -/
def PVSummable (Λ d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  Summable fun j => 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω

/-- Cochrane (2023), (3.10), p. 58: the integrand `s_t + i_t M_t/((1 + i_t) P_t)` (book indices;
here `M (t + 1)` is the money held overnight from `t`). -/
noncomputable def term10 (P s i M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + i t ω / (1 + i t ω) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), (3.11), p. 58: the integrand `s_t + ΔM_t/P_t`. -/
noncomputable def term11 (P s M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (M (t + 1) ω - M t ω) / P t ω

/-- Cochrane (2023), (3.12), p. 59: the integrand
`s_t + (i_t − i^m_t)/((1 + i_t)(1 + i^m_t)) · M_t/P_t`. -/
noncomputable def term12 (P s i im M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (i t ω - im t ω) / ((1 + i t ω) * (1 + im t ω)) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), second display after (3.12), p. 59: the integrand
`s_t + (M_t/(1 + i^m_t) − M_{t−1})/P_t`. -/
noncomputable def term12b (P s im M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (M (t + 1) ω / (1 + im t ω) - M t ω) / P t ω

/-- Cochrane (2023), footnote 2, p. 59: `1/(1 + i^m) − 1/(1 + i) = (i − i^m)/((1 + i)(1 + i^m))`. -/
theorem weight_identity {x y : ℝ} (hx : 1 + x ≠ 0) (hy : 1 + y ≠ 0) :
    1 / (1 + y) - 1 / (1 + x) = (x - y) / ((1 + x) * (1 + y)) := by
  field_simp
  ring

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: the nominal Euler equation: for `D` known at
`t`, `E_t[Λ_{t+1} D/P_{t+1}] = Λ_t D/((1 + i_t) P_t)`. -/
theorem E_next (hS : Standing 𝔼 Λ P i M B) (t : ℕ) {D : Ω → ℝ} (hD : 𝔼.E t D = D) :
    𝔼.E t (fun ω => Λ (t + 1) ω * (D ω / P (t + 1) ω)) =
      fun ω => Λ t ω * (D ω / (1 + i t ω) / P t ω) := by
  have hξ : 𝔼.E t (fun ω => Λ t ω / P t ω) = fun ω => Λ t ω / P t ω := hS.nominal_adapted t
  have hk : 𝔼.E t (D * fun ω => Λ t ω / P t ω) = D * fun ω => Λ t ω / P t ω := by
    rw [hS.pullOut t D _ hD, hξ]
  have he : (fun ω => Λ (t + 1) ω * (D ω / P (t + 1) ω)) =
      (D * fun ω => Λ t ω / P t ω) * fun ω => Λ (t + 1) ω / Λ t ω * (P t ω / P (t + 1) ω) := by
    funext ω
    have h1 := (hS.disc_pos t ω).ne'
    have h2 := (hS.price_pos t ω).ne'
    have h3 := (hS.price_pos (t + 1) ω).ne'
    simp only [Pi.mul_apply]
    field_simp
  rw [he, hS.pullOut t _ _ hk, ← hS.euler t]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 := (hS.price_pos t ω).ne'
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), p. 55: `E_t[(Λ_{t+j}/Λ_t) d] = Λ_t⁻¹ E_t[Λ_{t+j} d]` (pull-out of the known
`Λ_t⁻¹`). -/
theorem E_ratio (hS : Standing 𝔼 Λ P i M B) (t j : ℕ) (d : ℕ → Ω → ℝ) (ω : Ω) :
    𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω =
      (Λ t ω)⁻¹ * 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω := by
  have hk : 𝔼.E t (fun ω' => (Λ t ω')⁻¹) = fun ω' => (Λ t ω')⁻¹ := hS.disc_inv_adapted t
  have he : (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') =
      (fun ω' => (Λ t ω')⁻¹) * fun ω' => Λ (t + j) ω' * d (t + j) ω' := by
    funext ω'
    simp only [Pi.mul_apply]
    ring
  rw [he, hS.pullOut t _ _ hk]
  rfl

/-- Cochrane (2023), p. 55: the real value `Λ_t X_t/P_t` of liabilities `X` known at `t` is known
at `t`. -/
theorem adapted_val (hS : Standing 𝔼 Λ P i M B) {X : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X) :
    𝔼.Adapted (fun t ω => Λ t ω * (X t ω / P t ω)) := by
  intro t
  have hξ : 𝔼.E t (fun ω => Λ t ω / P t ω) = fun ω => Λ t ω / P t ω := hS.nominal_adapted t
  have he : (fun ω => Λ t ω * (X t ω / P t ω)) = X t * fun ω => Λ t ω / P t ω := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  change 𝔼.E t (fun ω => Λ t ω * (X t ω / P t ω)) = fun ω => Λ t ω * (X t ω / P t ω)
  rw [he, hS.pullOut t _ _ (hX t), hξ]

/-- Cochrane (2023), pp. 55–59 (the general valuation theorem, both directions): if the real
value of the liabilities `X` obeys the flow recursion
`Λ_t X_t/P_t = Λ_t d_t + E_t[Λ_{t+1} X_{t+1}/P_{t+1}]` and the present-value series is summable,
then the transversality condition holds iff `X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) d_{t+j}]`. -/
theorem pv_book_iff (hS : Standing 𝔼 Λ P i M B) {X d : ℕ → Ω → ℝ} (hXa : 𝔼.Adapted X)
    (hrec : ∀ t, (fun ω => Λ t ω * (X t ω / P t ω)) = (fun ω => Λ t ω * d t ω) +
      𝔼.E t (fun ω => Λ (t + 1) ω * (X (t + 1) ω / P (t + 1) ω)))
    (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ d t ω) :
    TVC 𝔼 Λ P X t ω ↔ PVRel 𝔼 Λ P X d t ω := by
  have hrel : ∀ j, 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω =
      Λ t ω * 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω := by
    intro j
    rw [E_ratio 𝔼 hS t j d ω]
    have := (hS.disc_pos t ω).ne'
    field_simp
  have hsum' : Summable fun j => 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω :=
    (hsum.mul_left (Λ t ω)).congr fun j => (hrel j).symm
  have key := pv_iff_tvc 𝔼 (Y := fun t ω => Λ t ω * (X t ω / P t ω))
    (c := fun t ω => Λ t ω * d t ω) (adapted_val 𝔼 hS hXa) hrec t ω hsum'
  unfold TVC PVRel
  refine key.trans ?_
  change Λ t ω * (X t ω / P t ω) =
      ∑' j, 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω ↔ _
  rw [tsum_congr hrel, tsum_mul_left]
  exact mul_right_inj' (hS.disc_pos t ω).ne'

/-! ### Equations (3.10)–(3.12) -/

/-- Cochrane (2023), footnote 2, p. 59: the flow recursion behind (3.12). -/
theorem rec_3_12 (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) :
    (fun ω => Λ t ω * ((B + M) t ω / P t ω)) =
      (fun ω => Λ t ω * term12 P s i im M t ω) +
        𝔼.E t (fun ω => Λ (t + 1) ω * ((B + M) (t + 1) ω / P (t + 1) ω)) := by
  have hD : 𝔼.E t ((B + M) (t + 1)) = (B + M) (t + 1) := by
    simp only [Pi.add_apply, map_add, hS.bonds_pre, hS.money_pre]
  rw [E_next 𝔼 hS t hD]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 : 1 + im t ω ≠ 0 := by linarith [hm t ω]
  have h3 := (hS.price_pos t ω).ne'
  simp only [Pi.add_apply, term12]
  rw [hf t ω]
  field_simp
  ring

/-- Cochrane (2023), footnote 1 (second), p. 59: the flow recursion behind the second form of
(3.12). -/
theorem rec_3_12b (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) :
    (fun ω => Λ t ω * (B t ω / P t ω)) =
      (fun ω => Λ t ω * term12b P s im M t ω) +
        𝔼.E t (fun ω => Λ (t + 1) ω * (B (t + 1) ω / P (t + 1) ω)) := by
  rw [E_next 𝔼 hS t (hS.bonds_pre t)]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 : 1 + im t ω ≠ 0 := by linarith [hm t ω]
  have h3 := (hS.price_pos t ω).ne'
  have hb : B t ω = P t ω * s t ω + B (t + 1) ω / (1 + i t ω) +
      M (t + 1) ω / (1 + im t ω) - M t ω := by linarith [hf t ω]
  simp only [Pi.add_apply, term12b]
  rw [hb]
  field_simp
  ring

/-- Cochrane (2023), (3.12), p. 59: with interest on money, the flow condition and the
transversality condition on `B + M` are equivalent to
`(B_{t−1} + M_{t−1})/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + (i − i^m)/((1+i)(1+i^m)) M/P)]`. -/
theorem pv_3_12 (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ (term12 P s i im M) t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) (term12 P s i im M) t ω :=
  pv_book_iff 𝔼 hS (fun t => by simp only [Pi.add_apply, map_add, hS.bonds_adapted t,
    hS.money_adapted t]) (rec_3_12 𝔼 hS hm hf) t ω hsum

/-- Cochrane (2023), second display after (3.12), p. 59: with interest on money, the flow
condition and the transversality condition on `B` alone are equivalent to
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + (M_{t+j}/(1+i^m_{t+j}) − M_{t+j−1})/P_{t+j})]`. -/
theorem pv_3_12b (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ (term12b P s im M) t ω) :
    TVC 𝔼 Λ P B t ω ↔ PVRel 𝔼 Λ P B (term12b P s im M) t ω :=
  pv_book_iff 𝔼 hS hS.bonds_adapted (rec_3_12b 𝔼 hS hm hf) t ω hsum

/-- Cochrane (2023), (3.10) and (3.12), p. 59: with `i^m = 0` the integrand of (3.12) is that of
(3.10). -/
theorem term12_zero (P s i M : ℕ → Ω → ℝ) :
    term12 P s i (fun _ _ => 0) M = term10 P s i M := by
  funext t ω
  simp only [term12, term10, sub_zero, add_zero, mul_one]

/-- Cochrane (2023), (3.11) and (3.12), p. 59: with `i^m = 0` the second form of (3.12) is
(3.11). -/
theorem term12b_zero (P s M : ℕ → Ω → ℝ) :
    term12b P s (fun _ _ => 0) M = term11 P s M := by
  funext t ω
  simp only [term12b, term11, add_zero, div_one]

/-- Cochrane (2023), (3.10), p. 58 (with footnote 1): given the flow (3.9), the transversality
condition on `B + M` holds iff `(B_{t−1} + M_{t−1})/P_t =
∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + i_{t+j}M_{t+j}/((1+i_{t+j})P_{t+j}))]`. -/
theorem pv_3_10 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ)
    (ω : Ω) (hsum : PVSummable 𝔼 Λ (term10 P s i M) t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω := by
  rw [← term12_zero] at hsum ⊢
  exact pv_3_12 𝔼 hS (fun _ _ => by norm_num) ((flow39_iff_flowIm P s i M B).mp hf) t ω hsum

/-- Cochrane (2023), (3.11), p. 58 (with footnote 1): given the flow (3.9), the transversality
condition on `B` alone holds iff
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + ΔM_{t+j}/P_{t+j})]`. -/
theorem pv_3_11 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ)
    (ω : Ω) (hsum : PVSummable 𝔼 Λ (term11 P s M) t ω) :
    TVC 𝔼 Λ P B t ω ↔ PVRel 𝔼 Λ P B (term11 P s M) t ω := by
  rw [← term12b_zero] at hsum ⊢
  exact pv_3_12b 𝔼 hS (fun _ _ => by norm_num) ((flow39_iff_flowIm P s i M B).mp hf) t ω hsum

/-! ### Survey error E13: (3.10) and (3.11) are equivalent only under the money TVC -/

/-- Cochrane (2023), p. 57 (E13): the terminal term of (3.10) is the terminal term of (3.11) plus
the money terminal term `E_t[Λ_{t+T} M_{t+T}/P_{t+T}]`. -/
theorem tvc_split (t T : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => Λ (t + T) ω' * ((B + M) (t + T) ω' / P (t + T) ω')) ω =
      𝔼.E t (fun ω' => Λ (t + T) ω' * (B (t + T) ω' / P (t + T) ω')) ω +
        𝔼.E t (fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω')) ω := by
  have he : (fun ω' => Λ (t + T) ω' * ((B + M) (t + T) ω' / P (t + T) ω')) =
      (fun ω' => Λ (t + T) ω' * (B (t + T) ω' / P (t + T) ω')) +
        fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω') := by
    funext ω'
    simp only [Pi.add_apply]
    ring
  rw [he, map_add, Pi.add_apply]

/-- Cochrane (2023), p. 57, "these equivalent expressions" (survey E13, corrected): under the
money transversality condition `E_t[Λ_{t+T} M_{t+T}/P_{t+T}] → 0`, (3.10) holds iff (3.11) holds. -/
theorem pv_3_10_iff_3_11 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B)
    (t : ℕ) (ω : Ω) (h10 : PVSummable 𝔼 Λ (term10 P s i M) t ω)
    (h11 : PVSummable 𝔼 Λ (term11 P s M) t ω) (hM : TVC 𝔼 Λ P M t ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω ↔ PVRel 𝔼 Λ P B (term11 P s M) t ω := by
  rw [← pv_3_10 𝔼 hS hf t ω h10, ← pv_3_11 𝔼 hS hf t ω h11]
  unfold TVC at hM ⊢
  simp_rw [tvc_split 𝔼 t _ ω]
  constructor
  · intro h
    simpa using h.sub hM
  · intro h
    simpa using h.add hM

/-- Cochrane (2023), p. 57 (survey E13): if (3.11) holds, then (3.10) holds iff the money
transversality condition holds. -/
theorem pv_3_10_iff_money_tvc (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : Flow39 P s i M B) (t : ℕ) (ω : Ω) (h10 : PVSummable 𝔼 Λ (term10 P s i M) t ω)
    (h11 : PVSummable 𝔼 Λ (term11 P s M) t ω) (h311 : PVRel 𝔼 Λ P B (term11 P s M) t ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω ↔ TVC 𝔼 Λ P M t ω := by
  rw [← pv_3_10 𝔼 hS hf t ω h10]
  have hB := (pv_3_11 𝔼 hS hf t ω h11).mpr h311
  unfold TVC at hB ⊢
  simp_rw [tvc_split 𝔼 t _ ω]
  constructor
  · intro h
    simpa using h.sub hB
  · intro h
    simpa using hB.add h

/-- Cochrane (2023), p. 57 (survey E13, counterexample): a perfect-foresight economy (a money
bubble: real money balances grow at the interest rate) satisfying the standing assumptions and
the flow (3.9), in which (3.11) holds at every date while (3.10) fails at every date, and the
money transversality condition fails. Here `Λ_t = βᵗ`, `P ≡ 1`, `1 + i = β⁻¹`, `B ≡ 0`,
`M_{t−1} = β⁻ᵗ`, `s_t = M_{t−1} − M_t`. -/
theorem money_bubble {β : ℝ} (hβ0 : 0 < β) :
    ∃ Λ P i M B s : ℕ → Unit → ℝ, Standing perfectForesight Λ P i M B ∧ Flow39 P s i M B ∧
      (∀ t, PVSummable perfectForesight Λ (term10 P s i M) t ()) ∧
      (∀ t, PVSummable perfectForesight Λ (term11 P s M) t ()) ∧
      (∀ t, PVRel perfectForesight Λ P B (term11 P s M) t ()) ∧
      (∀ t, ¬ PVRel perfectForesight Λ P (B + M) (term10 P s i M) t ()) ∧
      (∀ t, ¬ TVC perfectForesight Λ P M t ()) := by
  have hβ : β ≠ 0 := hβ0.ne'
  set Λ : ℕ → Unit → ℝ := fun t _ => β ^ t
  set P : ℕ → Unit → ℝ := fun _ _ => 1
  set i : ℕ → Unit → ℝ := fun _ _ => β⁻¹ - 1
  set M : ℕ → Unit → ℝ := fun t _ => β⁻¹ ^ t
  set B : ℕ → Unit → ℝ := fun _ _ => 0
  set s : ℕ → Unit → ℝ := fun t _ => β⁻¹ ^ t - β⁻¹ ^ (t + 1)
  have h10 : ∀ t ω, term10 P s i M t ω = 0 := by
    intro t ω
    simp only [term10, P, i, M, s, pow_succ]
    field_simp
    ring
  have h11 : ∀ t ω, term11 P s M t ω = 0 := by
    intro t ω
    simp only [term11, P, M, s]
    ring
  have hz10 : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * term10 P s i M (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [h10, mul_zero]
    rfl
  have hz11 : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * term11 P s M (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [h11, mul_zero]
    rfl
  refine ⟨Λ, P, i, M, B, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { pullOut := perfectForesight_pullOut
        disc_pos := fun t _ => pow_pos hβ0 t
        price_pos := fun _ _ => one_pos
        nominal_adapted := fun _ => rfl
        disc_inv_adapted := fun _ => rfl
        bonds_adapted := fun _ => rfl
        money_adapted := fun _ => rfl
        bonds_pre := fun _ => rfl
        money_pre := fun _ => rfl
        rate_gt := fun _ _ => by
          have : 0 < β⁻¹ := inv_pos.mpr hβ0
          simp only [i]
          linarith
        euler := fun t => by
          funext ω
          change 1 / (1 + (β⁻¹ - 1)) = β ^ (t + 1) / β ^ t * (1 / 1)
          rw [pow_succ]
          field_simp
          ring }
  · intro t ω
    simp only [P, B, s, M, pow_succ]
    ring
  · intro t
    unfold PVSummable
    rw [hz10 t]
    exact summable_zero
  · intro t
    unfold PVSummable
    rw [hz11 t]
    exact summable_zero
  · intro t
    unfold PVRel
    rw [hz11 t, tsum_zero]
    simp [B]
  · intro t
    unfold PVRel
    rw [hz10 t, tsum_zero]
    simp only [Pi.add_apply, B, M, P, zero_add, div_one]
    exact pow_ne_zero t (inv_ne_zero hβ)
  · intro t h
    unfold TVC at h
    have hc : (fun T => perfectForesight.E t
        (fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω')) ()) = fun _ => 1 := by
      funext T
      change β ^ (t + T) * (β⁻¹ ^ (t + T) / 1) = 1
      rw [div_one, ← mul_pow, mul_inv_cancel₀ hβ, one_pow]
    rw [hc] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### Ex-post returns, (3.13)–(3.15) -/

/-- Cochrane (2023), (3.13), p. 59: the ex-post real return from `t` to `t + 1` on the portfolio
of bonds and money, `R_{t+1} = (B_t + M_t)P_t/((Q_t B_t + M_t)P_{t+1})`, `Q_t = 1/(1 + i_t)`. -/
noncomputable def exPostReturn (P i M B : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (B (t + 1) ω + M (t + 1) ω) * P t ω /
    ((B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) * P (t + 1) ω)

/-- Cochrane (2023), (3.14), p. 59: the flow (3.9) written with the ex-post return,
`(B_{t−1} + M_{t−1})/P_t = s_t + (Q_tB_t + M_t)/P_t = s_t + R_{t+1}⁻¹(B_t + M_t)/P_{t+1}`. -/
theorem flow_3_14 {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ) (ω : Ω)
    (hP0 : P t ω ≠ 0) (hP1 : P (t + 1) ω ≠ 0) (hBM : B (t + 1) ω + M (t + 1) ω ≠ 0) :
    (B t ω + M t ω) / P t ω = s t ω + (B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) / P t ω ∧
      (B t ω + M t ω) / P t ω = s t ω + 1 / exPostReturn P i M B t ω *
        ((B (t + 1) ω + M (t + 1) ω) / P (t + 1) ω) := by
  have h1 : (B t ω + M t ω) / P t ω =
      s t ω + (B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) / P t ω := by
    rw [hf t ω]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  rw [h1, exPostReturn]
  field_simp

/-- Cochrane (2023), (3.15) and (3.6), pp. 56, 59: iterating `x_t = a_t + b_t x_{t+1}` gives
`x_t = ∑_{j<T} (∏_{k<j} b_{t+k}) a_{t+j} + (∏_{k<T} b_{t+k}) x_{t+T}` (pathwise, exact). -/
theorem iterate_discount {x a b : ℕ → ℝ} (h : ∀ t, x t = a t + b t * x (t + 1)) (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) +
      (∏ k ∈ Finset.range T, b (t + k)) * x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, Finset.prod_range_succ, h (t + T), ← add_assoc t T 1]
    ring

/-- Cochrane (2023), (3.15), p. 59: if the discounted series is summable, the pathwise
present-value relation `x_t = ∑_j (∏_{k<j} b_{t+k}) a_{t+j}` holds iff the discounted terminal
value `(∏_{k<T} b_{t+k}) x_{t+T}` tends to zero. -/
theorem pv_discount_iff {x a b : ℕ → ℝ} (h : ∀ t, x t = a t + b t * x (t + 1)) (t : ℕ)
    (hs : Summable fun j => (∏ k ∈ Finset.range j, b (t + k)) * a (t + j)) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, b (t + k)) * x (t + T)) atTop (𝓝 0) ↔
      x t = ∑' j, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) := by
  have he : ∀ T, (∏ k ∈ Finset.range T, b (t + k)) * x (t + T) =
      x t - ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) := by
    intro T
    have := iterate_discount h t T
    linarith
  have hlim : Tendsto (fun T => (∏ k ∈ Finset.range T, b (t + k)) * x (t + T)) atTop
      (𝓝 (x t - ∑' j, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j))) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h1
    rwa [h1, sub_self] at hlim

/-- Cochrane (2023), (3.15), p. 59, finite horizon: along every path,
`(B_{t−1} + M_{t−1})/P_t = ∑_{j<T} (∏_{k=1}^{j} R_{t+k}⁻¹) s_{t+j}
  + (∏_{k=1}^{T} R_{t+k}⁻¹)(B_{t+T−1} + M_{t+T−1})/P_{t+T}`. -/
theorem pv_3_15_finite {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (ω : Ω)
    (hP : ∀ t, P t ω ≠ 0) (hBM : ∀ t, B (t + 1) ω + M (t + 1) ω ≠ 0) (t T : ℕ) :
    (B t ω + M t ω) / P t ω =
      ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) *
        s (t + j) ω +
      (∏ k ∈ Finset.range T, 1 / exPostReturn P i M B (t + k) ω) *
        ((B (t + T) ω + M (t + T) ω) / P (t + T) ω) :=
  iterate_discount (x := fun t => (B t ω + M t ω) / P t ω) (a := fun t => s t ω)
    (fun t => (flow_3_14 hf t ω (hP t) (hP (t + 1)) (hBM t)).2) t T

/-- Cochrane (2023), (3.15), p. 59: along every path, the ex-post-return present value
`(B_{t−1} + M_{t−1})/P_t = ∑_j (∏_{k=1}^{j} R_{t+k}⁻¹) s_{t+j}` holds iff the ex-post discounted
terminal value tends to zero (given summability). -/
theorem pv_3_15_iff {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (ω : Ω)
    (hP : ∀ t, P t ω ≠ 0) (hBM : ∀ t, B (t + 1) ω + M (t + 1) ω ≠ 0) (t : ℕ)
    (hs : Summable fun j => (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) *
      s (t + j) ω) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, 1 / exPostReturn P i M B (t + k) ω) *
        ((B (t + T) ω + M (t + T) ω) / P (t + T) ω)) atTop (𝓝 0) ↔
      (B t ω + M t ω) / P t ω =
        ∑' j, (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) * s (t + j) ω :=
  pv_discount_iff (x := fun t => (B t ω + M t ω) / P t ω) (a := fun t => s t ω)
    (fun t => (flow_3_14 hf t ω (hP t) (hP (t + 1)) (hBM t)).2) t hs

/-! ### The zero bound, (3.16), and survey error E14 -/

/-- Cochrane (2023), §3.4.1, p. 59: at the zero bound `i = 0` money and bonds are perfect
substitutes: the flow (3.9) involves only `B + M`. -/
theorem zero_bound_flow_total {s : ℕ → Ω → ℝ} (hi : ∀ t ω, i t ω = 0) :
    Flow39 P s i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + (B + M) (t + 1) ω := by
  simp only [Flow39, Pi.add_apply, hi, add_zero, div_one]
  constructor <;> intro h t ω <;> linarith [h t ω]

/-- Cochrane (2023), (3.16), p. 59, derived (correctly) from (3.10) (survey E14): at the zero
bound `i = 0` the integrand of (3.10) is the surplus, so the valuation reads
`(B_{t−1} + M_{t−1})/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) s_{t+j}]`, equivalent to the transversality
condition on `B + M`. -/
theorem zero_bound_valuation (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : Flow39 P s i M B) (hi : ∀ t ω, i t ω = 0) (t : ℕ) (ω : Ω)
    (hsum : PVSummable 𝔼 Λ s t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) s t ω := by
  have he : term10 P s i M = s := by
    funext t ω
    simp only [term10, hi, zero_div, zero_mul, add_zero]
  rw [← he] at hsum ⊢
  exact pv_3_10 𝔼 hS hf t ω hsum

/-- Cochrane (2023), p. 60: with full interest on money, `i^m = i`, the integrand of (3.12) is the
surplus, and (3.16) holds as at the zero bound. -/
theorem full_interest_valuation (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : FlowIm P s i i M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ s t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) s t ω := by
  have he : term12 P s i i M = s := by
    funext t ω
    simp only [term12, sub_self, zero_div, zero_mul, add_zero]
  rw [← he] at hsum ⊢
  exact pv_3_12 𝔼 hS hS.rate_gt hf t ω hsum

/-- Cochrane (2023), (3.16), p. 59, with the book's discounting `Λ_{t+j}/Λ_t = βʲ` (deterministic
`Λ_t = βᵗ`): the right-hand side is `∑_j βʲ E_t s_{t+j}`. -/
theorem zero_bound_beta {β : ℝ} (hβ : β ≠ 0) (hΛ : ∀ t ω, Λ t ω = β ^ t) (X s : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    PVRel 𝔼 Λ P X s t ω ↔ X t ω / P t ω = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω := by
  unfold PVRel
  have he : ∀ j, (fun ω' => Λ (t + j) ω' / Λ t ω' * s (t + j) ω') = β ^ j • s (t + j) := by
    intro j
    funext ω'
    simp only [hΛ, Pi.smul_apply, smul_eq_mul, pow_add]
    field_simp
  simp_rw [he, map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), (3.16), p. 59, with the expectation outside the sum as printed: for bounded
surpluses and `0 ≤ β < 1`, `∑_j βʲ E_t s_{t+j} = E_t ∑_j βʲ s_{t+j}`. -/
theorem zero_bound_E_outside {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ K) (t : ℕ) (ω : Ω) :
    ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω = 𝔼.E t (fun ω' => ∑' j, β ^ j * s (t + j) ω') ω := by
  have hb : ∀ k ω', |(β ^ k • s (t + k)) ω'| ≤ β ^ k * K := by
    intro k ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + k) ω') (pow_nonneg hβ0 k)
  have h := 𝔼.E_tsum hβ0 hβ1 hb t ω
  simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
  rw [h]

/-- Cochrane (2023), p. 59, "Following (3.11), we still have (3.16)" (survey E14, counterexample):
a perfect-foresight economy at the zero bound (Friedman-rule deflation `P_t = βᵗ`, `Λ_t = βᵗ`,
constant money `m ≠ 0`, no bonds, no surpluses) that satisfies the standing assumptions, the flow
(3.9) and (3.11) at every date, but violates (3.16) at every date. (3.16) follows from (3.10), not
from (3.11); the two differ by the money transversality condition. -/
theorem zero_bound_not_from_3_11 {β m : ℝ} (hβ0 : 0 < β) (hm : m ≠ 0) :
    ∃ Λ P i M B s : ℕ → Unit → ℝ, Standing perfectForesight Λ P i M B ∧ Flow39 P s i M B ∧
      (∀ t ω, i t ω = 0) ∧ (∀ t, PVRel perfectForesight Λ P B (term11 P s M) t ()) ∧
      (∀ t, ¬ PVRel perfectForesight Λ P (B + M) s t ()) := by
  have hβ : β ≠ 0 := hβ0.ne'
  set Λ : ℕ → Unit → ℝ := fun t _ => β ^ t
  set P : ℕ → Unit → ℝ := fun t _ => β ^ t
  set M : ℕ → Unit → ℝ := fun _ _ => m
  set z : ℕ → Unit → ℝ := fun _ _ => 0
  have hz : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * z (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [z, mul_zero]
    rfl
  have h11 : term11 P z M = z := by
    funext t ω
    simp only [term11, z, M, sub_self, zero_div, add_zero]
  refine ⟨Λ, P, z, M, z, z, ?_, ?_, fun _ _ => rfl, ?_, ?_⟩
  · exact
      { pullOut := perfectForesight_pullOut
        disc_pos := fun t _ => pow_pos hβ0 t
        price_pos := fun t _ => pow_pos hβ0 t
        nominal_adapted := fun _ => rfl
        disc_inv_adapted := fun _ => rfl
        bonds_adapted := fun _ => rfl
        money_adapted := fun _ => rfl
        bonds_pre := fun _ => rfl
        money_pre := fun _ => rfl
        rate_gt := fun _ _ => by simp only [z]; norm_num
        euler := fun t => by
          funext ω
          change 1 / (1 + 0) = β ^ (t + 1) / β ^ t * (β ^ t / β ^ (t + 1))
          rw [add_zero]
          have h1 : β ^ t ≠ 0 := pow_ne_zero t hβ
          have h2 : β ^ (t + 1) ≠ 0 := pow_ne_zero (t + 1) hβ
          field_simp }
  · intro t ω
    simp only [z, M]
    ring
  · intro t
    unfold PVRel
    rw [h11, hz t, tsum_zero]
    simp [z]
  · intro t
    unfold PVRel
    rw [hz t, tsum_zero]
    simp only [Pi.add_apply, z, M, P, zero_add]
    exact div_ne_zero hm (pow_ne_zero t hβ)

/-! ### Seigniorage, §3.4.2 -/

/-- Cochrane (2023), p. 60: the surplus net of seigniorage counted as an interest saving,
`s_t − i_tM_t/((1 + i_t)P_t)` ("the rest of the government spends seigniorage"). -/
noncomputable def offsetSurplus (P s i M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω - i t ω / (1 + i t ω) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), p. 60: if the rest of the government spends seigniorage, the integrand of
(3.10) is the surplus `s` exclusive of seigniorage. -/
theorem seigniorage_offset_term (P s i M : ℕ → Ω → ℝ) :
    term10 P (offsetSurplus P s i M) i M = s := by
  funext t ω
  simp only [term10, offsetSurplus]
  ring

/-- Cochrane (2023), p. 60, "any seigniorage effect of monetary policy vanishes": with offsetting
surpluses, (3.10) is the money-free valuation `(B + M)/P = ∑_j E_t[(Λ_{t+j}/Λ_t) s_{t+j}]`,
whatever the path of money. -/
theorem seigniorage_offset_valuation (P s i M B : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P (offsetSurplus P s i M) i M) t ω ↔
      PVRel 𝔼 Λ P (B + M) s t ω := by
  rw [seigniorage_offset_term]

/-- Cochrane (2023), p. 60: with offsetting surpluses the flow condition involves only total debt,
`B_{t−1} + M_{t−1} = P_t s_t + (B_t + M_t)/(1 + i_t)`. -/
theorem seigniorage_offset_flow (P s i M B : ℕ → Ω → ℝ) (hP : ∀ t ω, P t ω ≠ 0)
    (hi : ∀ t ω, 1 + i t ω ≠ 0) :
    Flow39 P (offsetSurplus P s i M) i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + (B + M) (t + 1) ω / (1 + i t ω) := by
  have key : ∀ t ω, P t ω * offsetSurplus P s i M t ω + B (t + 1) ω / (1 + i t ω) +
      M (t + 1) ω = P t ω * s t ω + (B + M) (t + 1) ω / (1 + i t ω) := by
    intro t ω
    have h1 := hP t ω
    have h2 := hi t ω
    simp only [offsetSurplus, Pi.add_apply]
    field_simp
    ring
  simp only [Flow39, Pi.add_apply]
  constructor
  · intro h t ω
    rw [h t ω, key t ω]
    simp only [Pi.add_apply]
  · intro h t ω
    rw [h t ω, key t ω]
    simp only [Pi.add_apply]

/-- Cochrane (2023), pp. 60–62: with full interest on money (`i^m = i`) only total debt matters:
two splits of the same total `B + M` satisfy the flow condition together, and the valuation
integrand is the surplus, so the central bank can passively supply any money demanded. -/
theorem full_interest_split_irrelevant (P s i : ℕ → Ω → ℝ) {M₁ B₁ M₂ B₂ : ℕ → Ω → ℝ}
    (htot : B₁ + M₁ = B₂ + M₂) :
    (FlowIm P s i i M₁ B₁ ↔ FlowIm P s i i M₂ B₂) ∧ term12 P s i i M₁ = s ∧
      term12 P s i i M₂ = s := by
  have key : ∀ (M B : ℕ → Ω → ℝ), FlowIm P s i i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + ((B + M) (t + 1) ω) / (1 + i t ω) := by
    intro M B
    simp only [FlowIm, Pi.add_apply, add_div, add_assoc]
  refine ⟨by rw [key, key, htot], ?_, ?_⟩ <;>
  · funext t ω
    simp only [term12, sub_self, zero_div, zero_mul, add_zero]

/-- Cochrane (2023), p. 61: a passive money supply. Given total nominal debt `D` and money demand
`MV = Py` (`V ≠ 0`), the split `M = Py/V`, `B = D − M` meets money demand and leaves total debt
unchanged. -/
theorem passive_split (D P y : ℕ → Ω → ℝ) {V : ℝ} (hV : V ≠ 0) :
    (∀ t ω, (fun t ω => P t ω * y t ω / V) t ω * V = P t ω * y t ω) ∧
      ((fun t ω => D t ω - P t ω * y t ω / V) + fun t ω => P t ω * y t ω / V) = D := by
  refine ⟨fun t ω => by field_simp, ?_⟩
  funext t ω
  simp only [Pi.add_apply]
  ring

/-- Cochrane (2023), p. 60, U.S. 2019 (dollar amounts in billions): seigniorage counted as interest
savings `2% × 1500 = 30`, which is `3%` of a `1000` deficit, under `1%` of `5000` spending and
`0.15%` of a `20000` GDP; `5% × 1500 = 75`; a one-point rate rise gives `1% × 1500 = 15`. -/
theorem seigniorage_2019 :
    (2 / 100 : ℝ) * 1500 = 30 ∧ (30 : ℝ) / 1000 = 3 / 100 ∧ (30 : ℝ) / 5000 < 1 / 100 ∧
      (30 : ℝ) / 20000 = 15 / 10000 ∧ (5 / 100 : ℝ) * 1500 = 75 ∧ (1 / 100 : ℝ) * 1500 = 15 := by
  norm_num

/-- Cochrane (2023), pp. 60–61, U.S. early 1980s (billions): currency `100` over GDP `3000` is
`3.3%`; `10% × 100 = 10` of seigniorage is `0.33%` of GDP and less than a tenth of a `200`
deficit; debt `1000` is a third of GDP. The stated "$200 billion or 5% of GDP" is inconsistent
with the stated GDP: `200/3000 = 6.7%`. -/
theorem seigniorage_1980s :
    (100 : ℝ) / 3000 = 1 / 30 ∧ (10 / 100 : ℝ) * 100 = 10 ∧ (10 : ℝ) / 3000 = 1 / 300 ∧
      (10 : ℝ) / 200 < 1 / 10 ∧ (1000 : ℝ) / 3000 = 1 / 3 ∧ (200 : ℝ) / 3000 = 1 / 15 ∧
      (5 / 100 : ℝ) < 1 / 15 := by
  norm_num

end Cochrane.Generality.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linearized flow, present-value, and bond-return identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, pp. 62–71, and Online
Appendix A1.2–A1.3, pp. 556–564.

## The nonlinear identities and their exact linearization (A1.2)

* (1.4)–(1.6): `marketValue`, `overnightValue`, `nominalReturn`, `flow_value_identity`.
* (1.7)–(1.8): `flow_gdp`, `pv_gdp_finite`, `pv_gdp_iff`.
* (1.9): `log_flow_identity`.
* (1.10)–(1.13): `logFlow`, `logFlow_hasFDerivAt` (exact derivative at the steady state),
  `rho_eq` (`ρ = e^{−(r−g)}`, survey E11; the printed `e^{r−g}` of p. 63 is wrong:
  `printed_rho_eq_iff`, `printed_rho_lt_one_iff`), `rho_lt_one_iff`, `logFlow_hasFDerivAt_rho`,
  `constant_1_11`, `constant_zero_of_rg`, `tangent_1_11`; the scaling of the surplus `stilde_eq`.

## The linear model (§3.5) on an arbitrary `ExpectationSystem`

* (3.17): `Flow317`; `LinearEconomy` (bounded "stationary" processes, `0 < ρ < 1`).
* (3.18): `pv_318`; (3.19): `pv_318_E`, `pv_319_iff`, `terminal_of_bounded`, `pv_319`,
  `pv_319_E_outside`, and the `ρ = 1` version in deviations from the mean `pv_rho_one`.
* p. 64: `price_expected_return`.
* Innovations `innov` (`ΔE_{t+1} = E_{t+1} − E_t`): `innov_apply`, `innov_known`, `abs_innov_le`,
  `summable_innov`; `innov_pv` and (3.20) `innov_identity_3_20`.
* A1.3: `return_indep_weights` (1.21), `geomQ` (1.23), `geomQ_short`, `geomQ_perpetuity`,
  `geom_portfolio_return`, `bondReturn_hasFDerivAt` (1.22, exact coefficient `ω/(1+i)`),
  `bondReturn_steady` and `omega_hat_eq_iff` (survey E15).
* The linear bond identity with free parameter `ω̂` (`= ω/(1+i)` for the exact derivative, `= ω`
  in (1.24)): `BondRet`, `BondPriceOK`, `bondPrice_forward` (`q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`),
  survey E16 `printed_bondPrice_iff`, `printed_bondPrice_counterexample`; (3.21)/(1.25)
  `bondReturn_innov`, `bondReturn_innov_real`; `EH_bond`; (3.22) `weighted_inflation_identity`.
* Special cases: `short_debt_return_known`, `short_debt_EH`, `innov_r_zero`,
  `special_constant_short` (§3.5.2, (3.27)), `special_varying_short`, `special_constant_long`
  (3.23), `identity_3_24`, `identity_3_25`, `monetary_disinflation` (3.28),
  `perpetuity_no_discount_terms` (§3.5.4), `weights_close`, `scaling_ratio`.
* Sequences and Figure 3.1: `perm_inflation_equiv`, `zero_current_inflation_possible`,
  `disinflation_seq`, `fig31_jump`, `fig31_value`, `fig31_path`, `expected_rise_no_jump`,
  `announcement_jump`, `disinflation_monotone_omega`, `disinflation_monotone_length`; the exact
  nonlinear jump of A1 (1.14)–(1.16) is `LongTermDebt.jumpRatio` (`LongTermDebt.geom_value`,
  `LongTermDebt.price_jump_of_valuation`, 3.41% in `LongTermDebt.omega_08_example`);
  `fig31_log` (log drop 3.47%, the text's "3.5%"), `fig31_linear_exact_coeff` (3.48% with
  `ω̂ = ω/(1+i)`) (survey E15).
-/

namespace Cochrane.Generality.LogLinearIdentities

open Filter Topology

/-! ### The nonlinear flow and present-value identities (A1.2) -/

/-- Cochrane (2023), A1.2, p. 556: the nominal end-of-period market value of the debt,
`V_t = M_t + ∑_{j≥0} Q_t^{(t+1+j)} B_t^{(t+1+j)}` (`Q t n` is the date-`t` price of the zero-coupon
bond due at `n`, `B t n` the face value outstanding at the end of `t`). -/
noncomputable def marketValue (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  M t + ∑' j, Q t (t + 1 + j) * B t (t + 1 + j)

/-- Cochrane (2023), A1 (1.4), p. 557: the value at the beginning of `t + 1` of the debt held
overnight, `M_t + ∑_{j≥0} Q_{t+1}^{(t+1+j)} B_t^{(t+1+j)}`. -/
noncomputable def overnightValue (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  M t + ∑' j, Q (t + 1) (t + 1 + j) * B t (t + 1 + j)

/-- Cochrane (2023), A1 (1.4), p. 557: the nominal return on the government debt portfolio. -/
noncomputable def nominalReturn (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  overnightValue M Q B t / marketValue M Q B t

/-- Cochrane (2023), A1 (1.5)–(1.6), p. 557: the flow identity (1.5), overnight value equals
`P_{t+1}sp_{t+1} + V_{t+1}`, is exactly `V_t R^n_{t+1} = P_{t+1}sp_{t+1} + V_{t+1}`. -/
theorem flow_value_identity (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (P sp : ℕ → ℝ) (t : ℕ)
    (hV : marketValue M Q B t ≠ 0) :
    overnightValue M Q B t = P (t + 1) * sp (t + 1) + marketValue M Q B (t + 1) ↔
      marketValue M Q B t * nominalReturn M Q B t =
        P (t + 1) * sp (t + 1) + marketValue M Q B (t + 1) := by
  rw [nominalReturn, mul_div_cancel₀ _ hV]

/-- Cochrane (2023), A1 (1.7), p. 557: the flow identity in ratios to GDP,
`V_t/(P_t y_t) · R^n_{t+1}/(G_{t+1}Π_{t+1}) = sp_{t+1}/y_{t+1} + V_{t+1}/(P_{t+1}y_{t+1})`, with
`Π_{t+1} = P_{t+1}/P_t`, `G_{t+1} = y_{t+1}/y_t`. -/
theorem flow_gdp {V R P y sp : ℕ → ℝ} (t : ℕ) (hP : ∀ n, P n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (h16 : V t * R t = P (t + 1) * sp (t + 1) + V (t + 1)) :
    V t / (P t * y t) * (R t / (y (t + 1) / y t * (P (t + 1) / P t))) =
      sp (t + 1) / y (t + 1) + V (t + 1) / (P (t + 1) * y (t + 1)) := by
  have h1 := hP t
  have h2 := hP (t + 1)
  have h3 := hy t
  have h4 := hy (t + 1)
  have e : V t / (P t * y t) * (R t / (y (t + 1) / y t * (P (t + 1) / P t))) =
      V t * R t / (P (t + 1) * y (t + 1)) := by
    field_simp
  rw [e, h16]
  field_simp

/-- Cochrane (2023), A1 (1.8), p. 557, finite horizon: with `x_t = V_t/(P_ty_t)`, discount
`D_{t+1} = Π_{t+1}G_{t+1}/R^n_{t+1}` and `sy = sp/y`, the flow (1.7) iterates to
`x_t = ∑_{j<T} (∏_{k≤j} D_{t+1+k}) sy_{t+1+j} + (∏_{k<T} D_{t+1+k}) x_{t+T}`. -/
theorem pv_gdp_finite {x D sy : ℕ → ℝ} (h17 : ∀ n, x n = D (n + 1) * (sy (n + 1) + x (n + 1)))
    (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, D (t + k + 1)) *
        (D (t + j + 1) * sy (t + j + 1)) +
      (∏ k ∈ Finset.range T, D (t + k + 1)) * x (t + T) :=
  Money.iterate_discount (x := x) (a := fun n => D (n + 1) * sy (n + 1)) (b := fun n => D (n + 1))
    (fun n => by rw [h17 n]; ring) t T

/-- Cochrane (2023), A1 (1.8), p. 557 ("I assume here that the right-hand side converges.
Otherwise, keep the limiting debt term"): given summability, the nonlinear present-value identity
holds iff the discounted terminal debt/GDP ratio tends to zero. -/
theorem pv_gdp_iff {x D sy : ℕ → ℝ} (h17 : ∀ n, x n = D (n + 1) * (sy (n + 1) + x (n + 1)))
    (t : ℕ) (hs : Summable fun j => (∏ k ∈ Finset.range j, D (t + k + 1)) *
      (D (t + j + 1) * sy (t + j + 1))) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, D (t + k + 1)) * x (t + T)) atTop (𝓝 0) ↔
      x t = ∑' j, (∏ k ∈ Finset.range j, D (t + k + 1)) * (D (t + j + 1) * sy (t + j + 1)) :=
  Money.pv_discount_iff (x := x) (a := fun n => D (n + 1) * sy (n + 1)) (b := fun n => D (n + 1))
    (fun n => by rw [h17 n]; ring) t hs

/-- Cochrane (2023), A1 (1.9), p. 558: taking logs of (1.7),
`v_t + r^n_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`, where `v = log(V/(Py))`,
`r^n = log R^n`, `π = log Π`, `g = log G` (all exact, for positive values). -/
theorem log_flow_identity {x x' R Pi G sy : ℝ} (hx : 0 < x) (hx' : 0 < x') (hR : 0 < R)
    (hPi : 0 < Pi) (hG : 0 < G) (h17 : x * (R / (G * Pi)) = sy + x') :
    Real.log x + Real.log R - Real.log Pi - Real.log G =
      Real.log (sy + Real.exp (Real.log x')) := by
  rw [Real.exp_log hx', ← h17, Real.log_mul hx.ne' (div_pos hR (mul_pos hG hPi)).ne',
    Real.log_div hR.ne' (mul_pos hG hPi).ne', Real.log_mul hG.ne' hPi.ne']
  ring

/-- Cochrane (2023), A1 (1.9)–(1.10), p. 558: the right-hand side of the log flow identity as a
function of `(v_{t+1}, sy_{t+1})`: `log(sy + e^v)`. -/
noncomputable def logFlow (p : ℝ × ℝ) : ℝ := Real.log (p.2 + Real.exp p.1)

/-- Cochrane (2023), A1 (1.10)–(1.11), p. 558: the exact derivative of `log(sy + e^{v'})` at
`(v, sy)` is `(e^v/(e^v + sy), 1/(e^v + sy))`. -/
theorem logFlow_hasFDerivAt {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    HasFDerivAt logFlow ((Real.exp v / (Real.exp v + sy)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (1 / (Real.exp v + sy)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (v, sy) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.2 + Real.exp p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + Real.exp (v, sy).1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (v, sy) :=
    hasFDerivAt_snd.add hasFDerivAt_fst.exp
  have hne : (fun p : ℝ × ℝ => p.2 + Real.exp p.1) (v, sy) ≠ 0 := by
    simp only
    linarith
  refine (h1.log hne).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.11)–(1.12), p. 558 (and survey E11): at a steady state
`r − g = log((e^v + sy)/e^v)`, the coefficient `e^v/(e^v + sy)` equals `ρ = e^{−(r−g)}`. -/
theorem rho_eq {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    Real.exp v / (Real.exp v + sy) = Real.exp (-rg) := by
  rw [hss, Real.exp_neg, Real.exp_log (div_pos h (Real.exp_pos v)), inv_div]

/-- Cochrane (2023), p. 63 (survey E11): the printed `ρ = e^{r−g}` agrees with the correct
`ρ = e^{−(r−g)}` only when `r = g`. -/
theorem printed_rho_eq_iff (rg : ℝ) : Real.exp rg = Real.exp (-rg) ↔ rg = 0 := by
  rw [Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 63 ("everyone is so used to `ρ < 1`", survey E11): with the correct
`ρ = e^{−(r−g)}`, `ρ < 1` iff `r > g`, iff the steady-state surplus is positive. -/
theorem rho_lt_one_iff {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    (Real.exp (-rg) < 1 ↔ 0 < rg) ∧ (Real.exp (-rg) < 1 ↔ 0 < sy) := by
  refine ⟨by rw [Real.exp_lt_one_iff]; constructor <;> intro h <;> linarith, ?_⟩
  rw [← rho_eq h hss, div_lt_one h]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 63 (survey E11): the printed `e^{r−g}` is below one iff `r < g`, the
opposite of the steady state with positive surpluses. -/
theorem printed_rho_lt_one_iff (rg : ℝ) : Real.exp rg < 1 ↔ rg < 0 := Real.exp_lt_one_iff

/-- Cochrane (2023), A1 (1.11)–(1.12), p. 558: the exact derivative written with
`ρ = e^{−(r−g)}`: `D logFlow (v, sy) = ρ dv' + (ρ/e^v) dsy'`. -/
theorem logFlow_hasFDerivAt_rho {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    HasFDerivAt logFlow (Real.exp (-rg) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (Real.exp (-rg) / Real.exp v) • ContinuousLinearMap.snd ℝ ℝ ℝ) (v, sy) := by
  have hρ : Real.exp (-rg) / Real.exp v = 1 / (Real.exp v + sy) := by
    rw [← rho_eq h hss]
    field_simp
  rw [hρ, ← rho_eq h hss]
  exact logFlow_hasFDerivAt h

/-- Cochrane (2023), A1 (1.11), p. 558: the constant of the linearization,
`log(e^v + sy) − ρv − ρ sy/e^v = r − g + (1 − ρ)(v − 1)`. -/
theorem constant_1_11 {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    logFlow (v, sy) - Real.exp (-rg) * v - Real.exp (-rg) * (sy / Real.exp v) =
      rg + (1 - Real.exp (-rg)) * (v - 1) := by
  have hl : logFlow (v, sy) = v + rg := by
    rw [logFlow, hss, Real.log_div h.ne' (Real.exp_pos v).ne', Real.log_exp]
    simp only [add_comm sy]
    ring
  rw [hl, ← rho_eq h hss]
  have he := (Real.exp_pos v).ne'
  have hne := h.ne'
  field_simp
  ring

/-- Cochrane (2023), A1 p. 558 ("There is nothing wrong with expanding about `r = g`, `ρ = 1`, in
which case the constant in the identity is zero"). -/
theorem constant_zero_of_rg {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) (hrg : rg = 0) :
    logFlow (v, sy) - Real.exp (-rg) * v - Real.exp (-rg) * (sy / Real.exp v) = 0 ∧
      Real.exp (-rg) = 1 := by
  rw [constant_1_11 h hss, hrg, neg_zero, Real.exp_zero]
  ring_nf
  simp

/-- Cochrane (2023), A1 (1.11), p. 558: the right-hand side of (1.11),
`[r − g + (1 − ρ)(v − 1)] + ρv_{t+1} + ρ sy_{t+1}/e^v`, is exactly the first-order Taylor
polynomial (tangent) of `log(sy + e^{v'})` at the steady state. -/
theorem tangent_1_11 {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) (v' sy' : ℝ) :
    logFlow (v, sy) + (Real.exp (-rg) * (v' - v) + Real.exp (-rg) / Real.exp v * (sy' - sy)) =
      (rg + (1 - Real.exp (-rg)) * (v - 1)) + Real.exp (-rg) * v' +
        Real.exp (-rg) * (sy' / Real.exp v) := by
  rw [← constant_1_11 h hss]
  ring

/-- Cochrane (2023), p. 63 and A1 p. 558: the scaled surplus `s̃ = ρ sy/e^v` is the book's
`ρ/(V/(Py)) · s/y`, since `e^v` is the steady-state debt/GDP ratio `V/(Py)`. -/
theorem stilde_eq {ρ v VPy sy : ℝ} (hv : Real.exp v = VPy) :
    ρ * (sy / Real.exp v) = ρ / VPy * sy := by
  rw [hv]
  ring

/-! ### The linear model: (3.17)–(3.19) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), (3.17), p. 63: the linearized flow identity
`ρv_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` with real return `r = r^n − π`. -/
def Flow317 (ρ : ℝ) (v rn infl g sT : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, ρ * v (t + 1) ω = v t ω + (rn (t + 1) ω - infl (t + 1) ω) - g (t + 1) ω - sT (t + 1) ω

/-- Cochrane (2023), (3.18), p. 63: the flow "dividend" `s̃ + g − r` discounted in (3.18)–(3.19). -/
def zp (rn infl g sT : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := sT + g - (rn - infl)

/-- Cochrane (2023), (3.18), p. 63, exact and pathwise:
`v_t = ∑_{j=1}^{T} ρ^{j−1}(s̃_{t+j} + g_{t+j} − r_{t+j}) + ρ^T v_{t+T}`. -/
theorem pv_318 {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (t T : ℕ) (ω : Ω) :
    v t ω = ∑ j ∈ Finset.range T, ρ ^ j * zp rn infl g sT (t + j + 1) ω + ρ ^ T * v (t + T) ω := by
  have h := Money.iterate_discount (x := fun n => v n ω)
    (a := fun n => zp rn infl g sT (n + 1) ω) (b := fun _ => ρ)
    (fun n => by simp only [zp, Pi.add_apply, Pi.sub_apply]; linarith [hf n ω]) t T
  simp only [Finset.prod_const, Finset.card_range] at h
  exact h

/-- Cochrane (2023), (3.18), p. 63 ("it holds ex-post, so it holds ex-ante. We can take `E_t`"):
`v_t = ∑_{j<T} ρ^j E_t(s̃ + g − r)_{t+1+j} + ρ^T E_t v_{t+T}` for adapted `v`. -/
theorem pv_318_E {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (hv : 𝔼.Adapted v) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • 𝔼.E t (zp rn infl g sT (t + j + 1)) +
      ρ ^ T • 𝔼.E t (v (t + T)) := by
  have hfun : v t = ∑ j ∈ Finset.range T, ρ ^ j • zp rn infl g sT (t + j + 1) +
      ρ ^ T • v (t + T) := by
    funext ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact pv_318 hf t T ω
  have h := congrArg (𝔼.E t) hfun
  rw [hv t, map_add, map_sum, map_smul] at h
  simp only [map_smul] at h
  exact h

/-- Cochrane (2023), (3.19), p. 64: given summability, the infinite present-value identity
`v_t = ∑_{j≥1} ρ^{j−1} E_t(s̃ + g − r)_{t+j}` holds iff the terminal term
`ρ^T E_t v_{t+T}` vanishes. -/
theorem pv_319_iff {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (hv : 𝔼.Adapted v) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) ↔
      v t ω = ∑' j, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
  have he : ∀ T, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
    intro T
    have h := congrFun (pv_318_E 𝔼 hf hv t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  have hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 (v t ω - ∑' j, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-- Cochrane (2023), p. 64 ("The assumption or observation that debt/GDP is a stationary process
is enough"): for bounded `v` and `|ρ| < 1`, `ρ^T E_t v_{t+T} → 0`. -/
theorem terminal_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v)
    (t : ℕ) (ω : Ω) : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (a := fun T => |ρ| ^ T * K) (fun T => ?_) ?_
  · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK (t + T)) t ω) (pow_nonneg (abs_nonneg ρ) T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K

/-- Cochrane (2023), p. 64 ("If we use `ρ = 1`, then `E_t v_{t+T} → E(v)`, and equation (3.19)
continues to hold describing deviations from this mean"): with `ρ = 1`, if `E_t v_{t+T} → v̄`
and the series converges, `v_t − v̄ = ∑_j E_t(s̃ + g − r)_{t+1+j}`. -/
theorem pv_rho_one {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 1 v rn infl g sT)
    (hv : 𝔼.Adapted v) (t : ℕ) (ω : Ω) {vbar : ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (v (t + T)) ω) atTop (𝓝 vbar))
    (hs : Summable fun j => 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) :
    v t ω - vbar = ∑' j, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
  have he : ∀ T, ∑ j ∈ Finset.range T, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω =
      v t ω - 𝔼.E t (v (t + T)) ω := by
    intro T
    have h := congrFun (pv_318_E 𝔼 hf hv t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_pow,
      one_mul] at h
    linarith
  have h1 : Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
      atTop (𝓝 (v t ω - vbar)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hlim
  exact tendsto_nhds_unique h1 hs.hasSum.tendsto_sum_nat

variable (ρ : ℝ) (v rn infl g sT : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.5, pp. 63–65: the linear model with the standing assumptions used for the
innovation identities: (3.17) at every date, adapted processes, `0 < ρ < 1`, and bounded
("stationary", p. 64) debt, returns, inflation, growth and surpluses. -/
structure LinearEconomy where
  flow : Flow317 ρ v rn infl g sT
  v_adapted : 𝔼.Adapted v
  rn_adapted : 𝔼.Adapted rn
  infl_adapted : 𝔼.Adapted infl
  g_adapted : 𝔼.Adapted g
  s_adapted : 𝔼.Adapted sT
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  v_bdd : BoundedProc v
  rn_bdd : BoundedProc rn
  infl_bdd : BoundedProc infl
  g_bdd : BoundedProc g
  s_bdd : BoundedProc sT

variable {𝔼 ρ v rn infl g sT}

/-- Cochrane (2023), (3.18), p. 63: the discounted flow `s̃ + g − r` is bounded when its
components are. -/
theorem zp_bdd (hL : LinearEconomy 𝔼 ρ v rn infl g sT) :
    ∃ K, ∀ n ω, |zp rn infl g sT n ω| ≤ K := by
  obtain ⟨K1, h1⟩ := hL.s_bdd
  obtain ⟨K2, h2⟩ := hL.g_bdd
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  refine ⟨K1 + K2 + (K3 + K4), fun n ω => ?_⟩
  simp only [zp, Pi.add_apply, Pi.sub_apply]
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (h1 n ω)
    (h2 n ω))) ((abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))))

/-- Cochrane (2023), (3.18), p. 63: `s̃ + g − r` is adapted. -/
theorem zp_adapted (hL : LinearEconomy 𝔼 ρ v rn infl g sT) : 𝔼.Adapted (zp rn infl g sT) := by
  intro n
  simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub, hL.s_adapted n, hL.g_adapted n,
    hL.rn_adapted n, hL.infl_adapted n]

/-- Cochrane (2023), (3.19), p. 64: in the linear economy the infinite present-value identity
`v_t = ∑_{j≥1} ρ^{j−1} E_t(s̃_{t+j} + g_{t+j} − r_{t+j})` holds, as a genuine convergent sum. -/
theorem pv_319 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) (v t ω) := by
  obtain ⟨K, hK⟩ := zp_bdd hL
  have hs : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hL.rho_pos.le hL.rho_lt_one).mul_right K) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hL.rho_pos]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK _) t ω) (pow_nonneg hL.rho_pos.le j)
  have hρ : |ρ| < 1 := by rw [abs_of_pos hL.rho_pos]; exact hL.rho_lt_one
  have h := (pv_319_iff 𝔼 hL.flow hL.v_adapted t ω hs).mp
    (terminal_of_bounded 𝔼 hρ hL.v_bdd t ω)
  rw [h]
  exact hs.hasSum

/-- Cochrane (2023), (3.19), p. 64, with `E_t` outside the sum as printed:
`v_t = E_t ∑_{j≥1} ρ^{j−1}(s̃ + g − r)_{t+j}`. -/
theorem pv_319_E_outside (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    v t ω = 𝔼.E t (fun ω' => ∑' j, ρ ^ j * zp rn infl g sT (t + j + 1) ω') ω := by
  obtain ⟨K, hK⟩ := zp_bdd hL
  have hb : ∀ k ω', |(ρ ^ k • zp rn infl g sT (t + k + 1)) ω'| ≤ ρ ^ k * K := by
    intro k ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_of_pos hL.rho_pos]
    exact mul_le_mul_of_nonneg_left (hK _ ω') (pow_nonneg hL.rho_pos.le k)
  have h := 𝔼.E_tsum hL.rho_pos.le hL.rho_lt_one hb t ω
  simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
  rw [h]
  exact (pv_319 hL t ω).tsum_eq.symm

/-- Cochrane (2023), p. 64: the asset-pricing identity `p_t = E_t(d_{t+1} + p_{t+1})/E_t R_{t+1}`
for the return `R_{t+1} = (d_{t+1} + p_{t+1})/p_t`, given pull-out of the known `p_t⁻¹`. -/
theorem price_expected_return (hpo : 𝔼.PullOut) {p d : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted fun n ω => (p n ω)⁻¹) (t : ℕ) (ω : Ω) (hp0 : p t ω ≠ 0)
    (hR : 𝔼.E t (fun ω' => d (t + 1) ω' + p (t + 1) ω') ω ≠ 0) :
    p t ω = 𝔼.E t (fun ω' => d (t + 1) ω' + p (t + 1) ω') ω /
      𝔼.E t (fun ω' => (d (t + 1) ω' + p (t + 1) ω') / p t ω') ω := by
  have hk : 𝔼.E t (fun ω' => (p t ω')⁻¹) = fun ω' => (p t ω')⁻¹ := hp t
  have he : (fun ω' => (d (t + 1) ω' + p (t + 1) ω') / p t ω') =
      (fun ω' => (p t ω')⁻¹) * fun ω' => d (t + 1) ω' + p (t + 1) ω' := by
    funext ω'
    simp only [Pi.mul_apply]
    ring
  rw [he, hpo t _ _ hk, Pi.mul_apply]
  field_simp

/-! ### Innovations and the unexpected-inflation identity (3.20) -/

variable (𝔼) in
/-- Cochrane (2023), p. 64 and Notation p. xxv: the innovation operator
`ΔE_{t+1} = E_{t+1} − E_t`. -/
def innov (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), p. 64: `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    innov 𝔼 t x ω = 𝔼.E (t + 1) x ω - 𝔼.E t x ω := rfl

/-- Cochrane (2023), p. 65 ("Since `v_t` is known at time `t`, it usefully disappears from this
innovation accounting"): a variable known at `t` has no innovation at `t + 1`. -/
theorem innov_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  funext ω
  rw [innov_apply, ← hx, 𝔼.known (Nat.le_succ t), 𝔼.E_E_self, sub_self]
  rfl

/-- Cochrane (2023), p. 65: innovations of a variable bounded by `K` are bounded by `2K`. -/
theorem abs_innov_le {x : Ω → ℝ} {K : ℝ} (hx : ∀ ω, |x ω| ≤ K) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t x ω| ≤ 2 * K := by
  rw [innov_apply, two_mul]
  exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le hx _ ω) (𝔼.abs_E_le hx _ ω))

variable (𝔼) in
/-- Cochrane (2023), (3.20)–(3.22), p. 65: weighted sums of innovations of a bounded process
converge for summable weights. -/
theorem summable_innov {w : ℕ → ℝ} (hw : Summable w) {x : ℕ → Ω → ℝ} {K : ℝ}
    (hx : ∀ n ω, |x n ω| ≤ K) (f : ℕ → ℕ) (t : ℕ) (ω : Ω) :
    Summable fun j => w j * innov 𝔼 t (x (f j)) ω := by
  refine Summable.of_norm_bounded ((summable_abs_iff.mpr hw).mul_right (2 * K)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_innov_le (hx (f j)) t ω) (abs_nonneg _)

/-- Cochrane (2023), (3.20)–(3.22), p. 65: `∑ a^{j+1}` converges for `|a| < 1`. -/
theorem summable_pow_succ {a : ℝ} (ha : |a| < 1) : Summable fun j : ℕ => a ^ (j + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one ha)

/-- Cochrane (2023), p. 64, "Taking time `t + 1` innovations of (3.19)": the innovations of the
discounted flow sum to zero, `∑_{j≥0} ρ^j ΔE_{t+1}(s̃ + g − r)_{t+1+j} = 0`. -/
theorem innov_pv (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω) 0 := by
  have ha := pv_319 hL t ω
  have hb := pv_319 hL (t + 1) ω
  have hz := zp_adapted hL (t + 1)
  have hflow : v t ω - zp rn infl g sT (t + 1) ω = ρ * v (t + 1) ω := by
    simp only [zp, Pi.add_apply, Pi.sub_apply]
    linarith [hL.flow t ω]
  have hb' : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + j + 1)) ω) (v t ω) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero]
    rw [hz, hflow]
    convert hb.mul_left ρ using 1
    funext j
    rw [show t + (j + 1) + 1 = t + 1 + j + 1 by omega, pow_succ]
    ring
  have h := hb'.sub ha
  rw [sub_self] at h
  convert h using 1
  funext j
  rw [innov_apply]
  ring

/-- Cochrane (2023), (3.20), p. 65, the unexpected-inflation identity:
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}
  − ∑_{j≥0} ρ^j ΔE_{t+1}g_{t+1+j} + ∑_{j≥1} ρ^j ΔE_{t+1}r_{t+1+j}`. -/
theorem innov_identity_3_20 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h := (innov_pv hL t ω).tsum_eq
  have hgeo : Summable fun j : ℕ => ρ ^ j :=
    summable_geometric_of_lt_one hL.rho_pos.le hL.rho_lt_one
  obtain ⟨K1, h1⟩ := hL.s_bdd
  obtain ⟨K2, h2⟩ := hL.g_bdd
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hr : ∀ n ω, |(rn - infl) n ω| ≤ K3 + K4 := fun n ω =>
    (abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))
  have hs := summable_innov 𝔼 hgeo h1 (fun j => t + j + 1) t ω
  have hg := summable_innov 𝔼 hgeo h2 (fun j => t + j + 1) t ω
  have hR := summable_innov 𝔼 hgeo hr (fun j => t + j + 1) t ω
  have hsplit : ∀ j, ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω =
      ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω + ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω -
        ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω := by
    intro j
    simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub]
    ring
  rw [tsum_congr hsplit, (hs.add hg).tsum_sub hR, hs.tsum_add hg] at h
  have hr0 : ∑' j, ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω =
      (innov 𝔼 t (rn (t + 1)) ω - innov 𝔼 t (infl (t + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
    rw [hR.tsum_eq_zero_add]
    congr 1
    simp only [pow_zero, one_mul, add_zero, Pi.sub_apply, map_sub]
  rw [hr0] at h
  linarith

/-! ### The bond return (A1.3) -/

/-- Cochrane (2023), A1 (1.21), p. 562 ("at the steady state … all portfolios of bonds give the
same return"): at steady-state prices `Q^{(j+1)} = (1+i)^{−(j+1)}`, the portfolio with any
maturity weights `w_j` earns `1 + i`. -/
theorem return_indep_weights {i : ℝ} (w : ℕ → ℝ)
    (hden : ∑' j, w j / (1 + i) ^ (j + 1) ≠ 0) :
    (∑' j, w j / (1 + i) ^ j) / ∑' j, w j / (1 + i) ^ (j + 1) = 1 + i := by
  have hi : 1 + i ≠ 0 := by
    intro h0
    apply hden
    simp [h0]
  have he : ∑' j, w j / (1 + i) ^ j = (1 + i) * ∑' j, w j / (1 + i) ^ (j + 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_succ]
    field_simp
  rw [he, mul_div_assoc, div_self hden, mul_one]

/-- Cochrane (2023), A1 (1.23), p. 563: the steady-state price of the geometric portfolio,
`Q = ∑_{j≥1} ω^{j−1}/(1+i)^j = 1/(1 + i − ω)`, for `|ω| < |1 + i|`. -/
theorem geomQ {i ω : ℝ} (h : |ω| < |1 + i|) :
    ∑' j : ℕ, ω ^ j / (1 + i) ^ (j + 1) = 1 / (1 + i - ω) := by
  have := ForwardSolution.tsum_geometric_ratio (A := 1 + i) (B := ω) 1 h
  simpa only [one_mul] using this

/-- Cochrane (2023), A1 p. 563: one-period bonds (`ω = 0`) give `Q = 1/(1+i)`. -/
theorem geomQ_short {i : ℝ} (hi : 0 < 1 + i) :
    ∑' j : ℕ, (0 : ℝ) ^ j / (1 + i) ^ (j + 1) = 1 / (1 + i) := by
  rw [geomQ (by rw [abs_zero]; exact abs_pos.mpr hi.ne'), sub_zero]

/-- Cochrane (2023), A1 p. 563: perpetuities (`ω = 1`) give `Q = 1/i` (for `i > 0`). -/
theorem geomQ_perpetuity {i : ℝ} (hi : 0 < i) :
    ∑' j : ℕ, (1 : ℝ) ^ j / (1 + i) ^ (j + 1) = 1 / i := by
  rw [geomQ (by rw [abs_one, abs_of_pos (by linarith)]; linarith)]
  ring_nf

/-- Cochrane (2023), A1 p. 563 (first display): with geometric weights `ω^j` and the maturing bond
priced at one, the numerator of (1.21) is `1 + ω Q_{t+1}`:
`∑_{k≥0} ω^k x_k = 1 + ω ∑_{m≥0} ω^m x_{m+1}` when `x_0 = 1`. -/
theorem geom_portfolio_return {ω : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = 1)
    (hs : Summable fun k => ω ^ k * x k) :
    ∑' k, ω ^ k * x k = 1 + ω * ∑' m, ω ^ m * x (m + 1) := by
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left, pow_zero, one_mul, hx0]
  congr 1
  refine tsum_congr fun m => ?_
  rw [pow_succ]
  ring

/-- Cochrane (2023), A1 (1.22), p. 563: the log bond return as a function of
`(q_{t+1}, q_t)`, `r^n_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t`. -/
noncomputable def bondReturn (ω : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (1 + ω * Real.exp p.1) - p.2

/-- Cochrane (2023), A1 (1.22), p. 563: the exact derivative of the log bond return at the
steady state `q = log Q`: coefficient `ωQ/(1 + ωQ)` on `q_{t+1}` and `−1` on `q_t`. -/
theorem bondReturn_hasFDerivAt {ω Q : ℝ} (hQ : 0 < Q) (h : 0 < 1 + ω * Q) :
    HasFDerivAt (bondReturn ω) ((ω * Q / (1 + ω * Q)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) (Real.log Q, Real.log Q) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => 1 + ω * Real.exp p.1)
      (ω • (Real.exp (Real.log Q, Real.log Q).1 • ContinuousLinearMap.fst ℝ ℝ ℝ))
      (Real.log Q, Real.log Q) :=
    (hasFDerivAt_fst.exp.const_mul ω).const_add 1
  have hne : (fun p : ℝ × ℝ => 1 + ω * Real.exp p.1) (Real.log Q, Real.log Q) ≠ 0 := by
    simp only [Real.exp_log hQ]
    exact h.ne'
  refine ((h1.log hne).sub hasFDerivAt_snd).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Real.exp_log hQ]
  field_simp

/-- Cochrane (2023), A1 (1.22)–(1.23), p. 563: at `Q = 1/(1 + i − ω)` the constant of the
bond-return linearization is `log((1 + ωQ)/Q) = log(1 + i)` and the coefficient is
`ωQ/(1 + ωQ) = ω/(1 + i)`. -/
theorem bondReturn_steady {i ω : ℝ} (h : 0 < 1 + i - ω) (hi : 0 < 1 + i) :
    bondReturn ω (Real.log (1 / (1 + i - ω)), Real.log (1 / (1 + i - ω))) = Real.log (1 + i) ∧
      ω * (1 / (1 + i - ω)) / (1 + ω * (1 / (1 + i - ω))) = ω / (1 + i) := by
  have hQ : 0 < 1 / (1 + i - ω) := one_div_pos.mpr h
  have hne := h.ne'
  have hine := hi.ne'
  have hnum : 1 + ω * (1 / (1 + i - ω)) = (1 + i) / (1 + i - ω) := by
    field_simp
    ring
  constructor
  · rw [bondReturn, Real.exp_log hQ, hnum, Real.log_div hine hne, Real.log_div one_ne_zero hne,
      Real.log_one]
    ring
  · rw [hnum]
    field_simp

/-- Cochrane (2023), A1 (1.22)–(1.24), p. 563 (survey E15): the exact first-order coefficient
`ω/(1 + i)` equals the approximation `ω` of (1.24) only if `ω = 0` or `i = 0`. -/
theorem omega_hat_eq_iff {i ω : ℝ} (hi : 0 < 1 + i) : ω / (1 + i) = ω ↔ ω = 0 ∨ i = 0 := by
  rw [div_eq_iff hi.ne']
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply hc.2
    have : ω * i = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hc.1
    · exact h0
  · rintro (h | h) <;> simp [h]

/-- Cochrane (2023), A1 (1.22)/(1.24), p. 563, in deviations from the steady state: the linear
bond-return identity `r^n_{t+1} = ω̂ q_{t+1} − q_t` (`ω̂ = ω/(1+i)` for the exact derivative,
`ω̂ = ω` in (1.24)). -/
def BondRet (ωh : ℝ) (q rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, rn (t + 1) ω = ωh * q (t + 1) ω - q t ω

variable (𝔼) in
/-- Cochrane (2023), A1 (1.24)–(1.25), p. 564: a bounded adapted log bond price with `|ω̂| < 1`. -/
def BondPriceOK (ωh : ℝ) (q : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted q ∧ BoundedProc q ∧ |ωh| < 1

/-- Cochrane (2023), A1 p. 564 (the corrected box formula, survey E16): for a bounded log bond
price and `|ω̂| < 1`, iterating (1.24) forward gives `q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`. -/
theorem bondPrice_forward {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hq : BoundedProc q) (hω : |ωh| < 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-q t ω) := by
  obtain ⟨K, hK⟩ := hq
  have hrec : ∀ n, q n ω = -rn (n + 1) ω + ωh * q (n + 1) ω := fun n => by
    rw [hret n ω]; ring
  have hs : Summable fun j => (∏ k ∈ Finset.range j, ωh) * -rn (t + j + 1) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right (|ωh| * K + K))
      fun j => ?_
    rw [Finset.prod_const, Finset.card_range, Real.norm_eq_abs, abs_mul, abs_neg, abs_pow,
      hret]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) j)
    refine (abs_sub _ _).trans (add_le_add ?_ (hK _ ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK _ ω) (abs_nonneg _)
  have hterm : Tendsto (fun T => (∏ k ∈ Finset.range T, ωh) * q (t + T) ω) atTop (𝓝 0) := by
    simp only [Finset.prod_const, Finset.card_range]
    simpa [perfectForesight] using terminal_of_bounded perfectForesight hω
      (v := fun n _ => q n ω) ⟨K, fun n _ => hK n ω⟩ t ()
  have h := (Money.pv_discount_iff (x := fun n => q n ω) (a := fun n => -rn (n + 1) ω)
    (b := fun _ => ωh) hrec t hs).mp hterm
  simp only [Finset.prod_const, Finset.card_range] at h hs
  have h2 : HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-(∑' j, ωh ^ j * -rn (t + j + 1) ω)) := by
    have := hs.hasSum.neg
    convert this using 1
    funext j
    ring
  rw [← h] at h2
  exact h2

/-- Cochrane (2023), A1 p. 561 box and p. 564 (survey E16): the printed
`q_t = −∑_{j≥1} ω̂^j r^n_{t+j}` holds (for bounded `q`, `|ω̂| < 1`) only where `q_t = 0`. -/
theorem printed_bondPrice_iff {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hq : BoundedProc q) (hω : |ωh| < 1) (t : ℕ) (ω : Ω) :
    q t ω = -∑' j, ωh ^ (j + 1) * rn (t + j + 1) ω ↔ q t ω = 0 := by
  have h := (bondPrice_forward hret hq hω t ω).tsum_eq
  have he : ∑' j, ωh ^ (j + 1) * rn (t + j + 1) ω = ωh * -q t ω := by
    rw [← h, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have h1 : ωh ≠ 1 := by
    intro h1
    rw [h1, abs_one] at hω
    exact lt_irrefl _ hω
  rw [he]
  constructor
  · intro h2
    have : (1 - ωh) * q t ω = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exact absurd (by linarith) h1
    · exact h3
  · intro h2
    rw [h2]
    ring

/-- Cochrane (2023), A1 p. 561 box and p. 564 (survey E16, counterexample): with `ω̂ = 1/2`,
`q ≡ 1`, `r^n ≡ −1/2` satisfies (1.24) but violates the printed formula. -/
theorem printed_bondPrice_counterexample :
    BondRet (1 / 2) (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => -1 / 2) ∧
      (1 : ℝ) ≠ -∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * (-1 / 2) := by
  have hret : BondRet (1 / 2) (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => -1 / 2) := by
    intro t ω
    norm_num
  refine ⟨hret, fun h => ?_⟩
  have := (printed_bondPrice_iff hret ⟨1, fun _ _ => by norm_num⟩
    (by rw [abs_of_pos (by norm_num)]; norm_num) 0 ()).mp h
  norm_num at this

/-- Cochrane (2023), A1 p. 564: under the expectations hypothesis `E_t r^n_{t+1} = i_t`,
equivalently `ω̂ E_t q_{t+1} − q_t = i_t`. -/
theorem EH_bond {ωh : ℝ} {q rn i : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hq : 𝔼.Adapted q)
    (t : ℕ) : 𝔼.E t (rn (t + 1)) = i t ↔ ωh • 𝔼.E t (q (t + 1)) - q t = i t := by
  have he : rn (t + 1) = ωh • q (t + 1) - q t := by
    funext ω
    rw [hret t ω]
    rfl
  rw [he, map_sub, map_smul, hq t]

/-- Cochrane (2023), A1 (1.24), p. 563: the bond return `r^n_{t+1} = ω̂q_{t+1} − q_t` is bounded
when `q` is. -/
theorem rn_bound {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) {K : ℝ}
    (hK : ∀ n ω, |q n ω| ≤ K) (n : ℕ) (ω : Ω) : |rn (n + 1) ω| ≤ |ωh| * K + K := by
  rw [hret]
  refine (abs_sub _ _).trans (add_le_add ?_ (hK n ω))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hK _ ω) (abs_nonneg _)

/-- Cochrane (2023), (3.21) and A1 (1.25), p. 564: the bond-return innovation identity
`ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}r^n_{t+1+j}`. -/
theorem bondReturn_innov {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω := by
  obtain ⟨hqa, ⟨K, hK⟩, hω⟩ := hok
  have hfwd : q (t + 1) = fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω' := by
    funext ω'
    have h := (bondPrice_forward hret ⟨K, hK⟩ hω (t + 1) ω').tsum_eq
    have e : ∑' j, ωh ^ j * rn (t + j + 2) ω' = ∑' j, ωh ^ j * rn (t + 1 + j + 1) ω' :=
      tsum_congr fun j => by rw [show t + 1 + j + 1 = t + j + 2 by omega]
    rw [e, h, neg_neg]
  have hu : Summable fun j : ℕ => |ωh| ^ j * (|ωh| * K + K) :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right _
  have hb : ∀ j ω', |(ωh ^ j • rn (t + j + 2)) ω'| ≤ |ωh| ^ j * (|ωh| * K + K) := by
    intro j ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (rn_bound hret hK (t + j + 1) ω') (pow_nonneg
      (abs_nonneg _) j)
  have hE : ∀ s, 𝔼.E s (q (t + 1)) ω = -∑' j, ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := by
    intro s
    have h := ForwardSolution.E_tsum_dom 𝔼 hu hb s ω
    simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
    rw [hfwd, show (fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω') =
      -(fun ω' => ∑' j, ωh ^ j * rn (t + j + 2) ω') from rfl, map_neg, Pi.neg_apply, h]
  have hsum : ∀ s, Summable fun j => ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := fun s =>
    Summable.of_norm_bounded hu fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => rn_bound hret hK (t + j + 1) ω')
        s ω) (pow_nonneg (abs_nonneg _) j)
  have hrn : rn (t + 1) = ωh • q (t + 1) - q t := by
    funext ω'
    rw [hret t ω']
    rfl
  have hq0 : innov 𝔼 t (q t) = 0 := innov_known (hqa t)
  have key : ∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh * (∑' j, ωh ^ j * 𝔼.E (t + 1) (rn (t + j + 2)) ω -
        ∑' j, ωh ^ j * 𝔼.E t (rn (t + j + 2)) ω) := by
    rw [← (hsum (t + 1)).tsum_sub (hsum t), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [innov_apply, pow_succ]
    ring
  rw [hrn, map_sub, map_smul, hq0, sub_zero, Pi.smul_apply, smul_eq_mul, innov_apply, hE, hE,
    key]
  ring

/-- Cochrane (2023), (3.21), p. 65, second form: `ΔE_{t+1}r^n_{t+1}
= −∑_{j≥1} ω̂^j ΔE_{t+1}(r_{t+1+j} + π_{t+1+j})` with `r = r^n − π`. -/
theorem bondReturn_innov_real {ωh : ℝ} {q rn infl' : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) *
      innov 𝔼 t ((rn (t + j + 2) - infl' (t + j + 2)) + infl' (t + j + 2)) ω := by
  rw [bondReturn_innov hret hok t ω]
  simp only [sub_add_cancel]

/-! ### The weighted inflation identity (3.22) and special cases -/

/-- Cochrane (2023), (3.22), p. 65: eliminating the bond return between (3.20) and (3.21),
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = −∑ ρ^j ΔE_{t+1}s̃_{t+1+j} − ∑ ρ^j ΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1} (ρ^j − ω̂^j) ΔE_{t+1}r_{t+1+j}`. -/
theorem weighted_inflation_identity (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
          innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h20 := innov_identity_3_20 hL t ω
  have h21 := bondReturn_innov hret hok t ω
  have hω := hok.2.2
  have hρ : |ρ| < 1 := by rw [abs_of_pos hL.rho_pos]; exact hL.rho_lt_one
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hr : ∀ n ω, |(rn - infl) n ω| ≤ K3 + K4 := fun n ω =>
    (abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))
  have hRρ := summable_innov 𝔼 (summable_pow_succ hρ) hr (fun j => t + j + 2) t ω
  have hRω := summable_innov 𝔼 (summable_pow_succ hω) hr (fun j => t + j + 2) t ω
  have hPiω := summable_innov 𝔼 (summable_pow_succ hω) h4 (fun j => t + j + 2) t ω
  have hPi0 := summable_innov 𝔼 (summable_geometric_of_abs_lt_one hω) h4 (fun j => t + j + 1) t ω
  have hsplit : ∀ j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω +
        ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    intro j
    simp only [Pi.sub_apply, map_sub]
    ring
  rw [tsum_congr hsplit, hRω.tsum_add hPiω] at h21
  have hL0 : ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    rw [hPi0.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    rfl
  have hdiff : ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
      innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω =
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω := by
    rw [← Summable.tsum_sub
      (f := fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω) hRρ hRω]
    refine tsum_congr fun j => ?_
    simp only [Pi.sub_apply]
    ring
  rw [hL0, hdiff]
  change _ = -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
      (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
      (∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω)
  linarith

/-- Cochrane (2023), p. 65–66 ("With one-period debt `ω = 0`, `r^n_{t+1} = i_t` and is known
ahead of time"): with `ω̂ = 0` the bond return is known at `t` and has no innovation. -/
theorem short_debt_return_known {q rn : ℕ → Ω → ℝ} (hret : BondRet 0 q rn)
    (hq : 𝔼.Adapted q) (t : ℕ) :
    𝔼.E t (rn (t + 1)) = rn (t + 1) ∧ innov 𝔼 t (rn (t + 1)) = 0 := by
  have he : rn (t + 1) = -q t := by
    funext ω
    rw [hret t ω, zero_mul, zero_sub]
    rfl
  have hk : 𝔼.E t (rn (t + 1)) = rn (t + 1) := by rw [he, map_neg, hq t]
  exact ⟨hk, innov_known hk⟩

/-- Cochrane (2023), p. 65–66 and A1 p. 564: with one-period debt and the expectations
hypothesis, `r^n_{t+1} = i_t`. -/
theorem short_debt_EH {q rn i : ℕ → Ω → ℝ} (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (t : ℕ)
    (hEH : 𝔼.E t (rn (t + 1)) = i t) : rn (t + 1) = i t := by
  rw [← hEH, (short_debt_return_known hret hq t).1]

/-- Cochrane (2023), p. 66 ("A constant expected return occurs with `E_t r_{t+1} = 0`"): with
constant expected real returns, real returns beyond `t + 1` have no innovation at `t + 1`. -/
theorem innov_r_zero {rn infl : ℕ → Ω → ℝ} (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0)
    (t j : ℕ) : innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
  have h1 : 𝔼.E (t + 1) (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
    rw [← 𝔼.tower (show t + 1 ≤ t + j + 1 by omega), hc (t + j + 1), map_zero]
  have h2 : 𝔼.E t (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
    rw [← 𝔼.tower (show t ≤ t + j + 1 by omega), hc (t + j + 1), map_zero]
  simp only [innov, LinearMap.sub_apply, h1, h2, sub_zero]

/-- Cochrane (2023), §3.5.2, p. 66, and (3.27), p. 69: with constant expected returns, one-period
debt (`ω̂ = 0`) and no growth, `ΔE_{t+1}π_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem special_constant_short (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {q : ℕ → Ω → ℝ}
    (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero, (short_debt_return_known hret hq t).2] at h
  exact h

/-- Cochrane (2023), p. 67: with time-varying expected returns, one-period debt and no growth,
`ΔE_{t+1}π_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j} + ∑_{j≥1} ρ^j ΔE_{t+1}r_{t+1+j}`. -/
theorem special_varying_short (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {q : ℕ → Ω → ℝ}
    (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (hg : ∀ n ω, g n ω = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) +
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero,
    (short_debt_return_known hret hq t).2] at h
  exact h

/-- Cochrane (2023), (3.23), p. 67: with constant expected returns and no growth,
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem special_constant_long (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q)
    (hg : ∀ n ω, g n ω = 0) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := weighted_inflation_identity hL hret hok t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.24), p. 68: with constant expected returns and no growth,
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem identity_3_24 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.25), p. 68: with constant expected returns,
`ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}π_{t+1+j}`. -/
theorem identity_3_25 {ωh : ℝ} {q rn infl : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  rw [bondReturn_innov_real (infl' := infl) hret hok t ω]
  congr 1
  refine tsum_congr fun j => ?_
  rw [map_add, innov_r_zero hc, zero_add]

/-- Cochrane (2023), (3.28), p. 69: a monetary policy change with no change in surpluses
(`ΔE_{t+1}s̃_{t+1+j} = 0`), constant expected returns and no growth gives
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = 0`, hence `ΔE_{t+1}π_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}π_{t+1+j}`. -/
theorem monetary_disinflation (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q)
    (hg : ∀ n ω, g n ω = 0) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω = 0 ∧
      innov 𝔼 t (infl (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  have h := special_constant_long hL hret hok hg hc t ω
  simp only [hs, mul_zero, tsum_zero, neg_zero] at h
  refine ⟨h, ?_⟩
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hPi0 := summable_innov 𝔼 (summable_geometric_of_abs_lt_one hok.2.2) h4
    (fun j => t + j + 1) t ω
  rw [hPi0.tsum_eq_zero_add] at h
  simp only [pow_zero, one_mul, add_zero] at h
  change innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω = 0
    at h
  linarith

/-- Cochrane (2023), §3.5.4, p. 71: with perpetuities, `ρ = ω̂`, the discount-rate terms drop out
of (3.22): `∑ ω̂^j ΔE_{t+1}π_{t+1+j} = −∑ ρ^j ΔE_{t+1}s̃_{t+1+j} − ∑ ρ^j ΔE_{t+1}g_{t+1+j}`. -/
theorem perpetuity_no_discount_terms (hL : LinearEconomy 𝔼 ρ v rn infl g sT)
    {q : ℕ → Ω → ℝ} (hret : BondRet ρ q rn) (hok : BondPriceOK 𝔼 ρ q) (t : ℕ) (ω : Ω) :
    ∑' j, ρ ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        ∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω := by
  have h := weighted_inflation_identity hL hret hok t ω
  simp only [sub_self, zero_mul, tsum_zero, add_zero] at h
  exact h

/-- Cochrane (2023), pp. 70–71 ("the difference between `ρ^j` and `(ρ^j − ω^j)` only affects the
first few terms"): the weights differ by `ω^j ≤ 0.8^j`, below `1%` from `j = 21` on. -/
theorem weights_close {ρ ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 0.8) (j : ℕ) :
    |ρ ^ j - (ρ ^ j - ω ^ j)| = ω ^ j ∧ ω ^ j ≤ 0.8 ^ j ∧
      (21 ≤ j → (0.8 : ℝ) ^ j < 0.01) := by
  refine ⟨by rw [sub_sub_cancel, abs_of_nonneg (pow_nonneg hω0 j)],
    pow_le_pow_left₀ hω0 hω j, fun hj => ?_⟩
  calc (0.8 : ℝ) ^ j ≤ 0.8 ^ 21 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    _ < 0.01 := by norm_num

/-- Cochrane (2023), p. 66 ("When debt is 100% of GDP … it takes four times as much actual
surplus-to-GDP to produce the same effect as when debt is 25% of GDP"): equal scaled surpluses
`ρ sy/(V/Py)` at debt ratios `1` and `1/4` require `sy₁ = 4 sy₂`. -/
theorem scaling_ratio {ρ sy₁ sy₂ : ℝ} (hρ : ρ ≠ 0) (h : ρ * (sy₁ / 1) = ρ * (sy₂ / (1 / 4))) :
    sy₁ = 4 * sy₂ := by
  have := mul_left_cancel₀ hρ h
  rw [div_one] at this
  rw [this]
  ring

/-! ### Sequences of innovations and Figure 3.1 -/

/-- Cochrane (2023), p. 67 ("with `ω = 0.7`, a permanent 1% rise in inflation soaks up the same
surplus as a `1/(1 − 0.7) = 3.3%` price-level jump"): `∑_{j≥0} ω^j = 1/(1 − ω)`, and
`1/(1 − 0.7) = 10/3 ∈ (3.33, 3.34)`. -/
theorem perm_inflation_equiv {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) :
    ∑' j : ℕ, ω ^ j = 1 / (1 - ω) ∧ (1 : ℝ) / (1 - 0.7) = 10 / 3 ∧
      (3.33 : ℝ) < 10 / 3 ∧ (10 / 3 : ℝ) < 3.34 := by
  refine ⟨by rw [tsum_geometric_of_lt_one h0 h1, one_div], by norm_num, by norm_num,
    by norm_num⟩

/-- Cochrane (2023), p. 67 ("It is even possible that the fiscal shock comes with no
contemporaneous inflation at all"): for `0 < ω < 1` and any fiscal shock `S`, there is an
inflation-innovation path with `x_0 = 0` and `∑ ω^j x_j = S` (namely
`x_j = S(1 − ω)/ω`, `j ≥ 1`). -/
theorem zero_current_inflation_possible {ω : ℝ} (h0 : 0 < ω) (h1 : ω < 1) (S : ℝ) :
    ∃ x : ℕ → ℝ, x 0 = 0 ∧ HasSum (fun j => ω ^ j * x j) S := by
  set c := S * (1 - ω) / ω
  refine ⟨fun j => if j = 0 then 0 else c, by simp, ?_⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, ↓reduceIte, sub_zero,
    Nat.add_one_ne_zero, ↓reduceIte]
  have hg := (hasSum_geometric_of_lt_one h0.le h1).mul_left (ω * c)
  convert hg using 1
  · funext j
    rw [pow_succ]
    ring
  · have : ω ≠ 0 := h0.ne'
    have : 1 - ω ≠ 0 := by linarith
    simp only [c]
    field_simp

/-- Cochrane (2023), (3.28), p. 69, on a sequence of innovations `x_j = ΔE_{t+1}π_{t+1+j}`:
`∑ ω^j x_j = 0` gives `x_0 = −∑_{j≥1} ω^j x_j`. -/
theorem disinflation_seq {ω : ℝ} {x : ℕ → ℝ} (hs : Summable fun j => ω ^ j * x j)
    (h : ∑' j, ω ^ j * x j = 0) : x 0 = -∑' j, ω ^ (j + 1) * x (j + 1) := by
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul] at h
  linarith

/-- Cochrane (2023), p. 69 and Figure 3.1: an unexpected permanent rise (`x_j = 1` for `j ≥ 1`)
with no surplus change forces the initial jump `x_0 = −ω/(1 − ω)`. -/
theorem fig31_jump {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) {x : ℕ → ℝ} (hx : ∀ j, x (j + 1) = 1)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) :
    x 0 = -(ω / (1 - ω)) := by
  rw [disinflation_seq hs h]
  simp only [hx, mul_one]
  rw [show (fun j : ℕ => ω ^ (j + 1)) = fun j => ω * ω ^ j from funext fun j => pow_succ' ω j,
    tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Cochrane (2023), p. 69 and Figure 3.1: with `ω = 0.8` the initial jump is `−4` (percent), and
it is a genuine solution: the path `x_0 = −4`, `x_j = 1` satisfies `∑ 0.8^j x_j = 0`. -/
theorem fig31_value :
    (0.8 : ℝ) / (1 - 0.8) = 4 ∧
      HasSum (fun j : ℕ => (0.8 : ℝ) ^ j * (if j = 0 then -4 else 1)) 0 := by
  refine ⟨by norm_num, ?_⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, ↓reduceIte,
    Nat.add_one_ne_zero, ↓reduceIte, mul_one]
  have hg := (hasSum_geometric_of_lt_one (r := (0.8 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (0.8 : ℝ)
  convert hg using 1
  · funext j
    rw [pow_succ']
  · norm_num

/-- Cochrane (2023), Figure 3.1, p. 70: the log price level relative to its pre-shock path,
`p_n = ∑_{k<n} x_k`, is `−ω/(1 − ω)` on impact and then rises by one per period. -/
theorem fig31_path {ω : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = -(ω / (1 - ω))) (hx : ∀ j, x (j + 1) = 1)
    (n : ℕ) : ∑ k ∈ Finset.range (n + 1), x k = -(ω / (1 - ω)) + n := by
  induction n with
  | zero => simp [hx0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hx n]
    push_cast
    ring

/-- Cochrane (2023), p. 70 ("If the interest-rate rise is completely expected … The long-term bond
case follows exactly the same path as the short-term bond case"): if the news at `t + 1` does not
change expected future inflation (`x_j = 0`, `j ≥ 1`) and surpluses do not change, there is no
price-level jump, whatever `ω`. -/
theorem expected_rise_no_jump {ω : ℝ} {x : ℕ → ℝ} (hx : ∀ j, x (j + 1) = 0)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) : x 0 = 0 := by
  rw [disinflation_seq hs h]
  simp [hx]

/-- Cochrane (2023), p. 69–70 ("announced `k` periods ahead"): if the news at `t + 1` raises
inflation by one from `k ≥ 1` periods later on (`x_j = 0` for `1 ≤ j < k`, `x_j = 1` for
`j ≥ k`), the jump on announcement is `x_0 = −ω^k/(1 − ω)`. -/
theorem announcement_jump {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) {k : ℕ} (hk : 1 ≤ k) {x : ℕ → ℝ}
    (hx : ∀ j, 1 ≤ j → x j = if j < k then 0 else 1)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) :
    x 0 = -(ω ^ k / (1 - ω)) := by
  have hs' := (summable_nat_add_iff 1).mpr hs
  rw [disinflation_seq hs h]
  congr 1
  have hval : ∀ j, ω ^ (j + 1) * x (j + 1) = if j + 1 < k then 0 else ω ^ (j + 1) := by
    intro j
    rw [hx (j + 1) (by omega)]
    split_ifs <;> ring
  have hsk : Summable fun j => if j + 1 < k then (0 : ℝ) else ω ^ (j + 1) :=
    hs'.congr fun j => hval j
  rw [tsum_congr hval, ← hsk.sum_add_tsum_nat_add (k - 1)]
  rw [Finset.sum_eq_zero fun j hj => by
    rw [Finset.mem_range] at hj
    simp only [show j + 1 < k by omega, ↓reduceIte], zero_add]
  have he : ∀ j, (if j + (k - 1) + 1 < k then (0 : ℝ) else ω ^ (j + (k - 1) + 1)) =
      ω ^ k * ω ^ j := by
    intro j
    simp only [show ¬ (j + (k - 1) + 1 < k) by omega, ↓reduceIte]
    rw [← pow_add]
    congr 1
    omega
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Cochrane (2023), p. 69 ("The deflationary effect is larger if there is more long-term debt
outstanding, if `ω` is larger"): the jump size `ω/(1 − ω)` is strictly increasing on `[0, 1)`. -/
theorem disinflation_monotone_omega :
    StrictMonoOn (fun ω : ℝ => ω / (1 - ω)) (Set.Ico 0 1) := by
  intro a ha b hb hab
  simp only
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hb1 : 0 < 1 - b := by linarith [hb.2]
  rw [div_lt_div_iff₀ ha1 hb1]
  nlinarith

/-- Cochrane (2023), p. 69 ("A credible, persistent interest-rate rise – more terms
`ΔE_{t+1}π_{t+1+j}` – … has a stronger disinflationary effect"): a rise lasting `n` periods gives
the jump `−∑_{j=1}^{n} ω^j`, strictly larger in size for longer rises when `ω > 0`. -/
theorem disinflation_monotone_length {ω : ℝ} (h0 : 0 < ω) :
    StrictMono fun n => ∑ j ∈ Finset.range n, ω ^ (j + 1) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [Finset.sum_range_succ]
  linarith [pow_pos h0 (n + 1)]

/-- Cochrane (2023), A1 p. 560 (survey E15): the exact *log* price drop
`−log(P_0/P) = −log(1133/1173)` lies in `(3.46%, 3.48%)`, which is the text's "3.5%". -/
theorem fig31_log :
    0.0346 < -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) ∧
      -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) < 0.0348 := by
  rw [LongTermDebt.omega_08_example.1]
  have hx0 : (0 : ℝ) < 40 / 1173 := by norm_num
  have hx : |(40 / 1173 : ℝ)| < 1 := by rw [abs_of_pos hx0]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have e : (1 : ℝ) - 40 / 1173 = 1133 / 1173 := by norm_num
  rw [e, abs_of_pos hx0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Cochrane (2023), §3.5.3 and A1 (1.22) (survey E15): the linearized jump with the printed
weight `ω = 0.8` is `4%` (Figure 3.1), while with the exact first-order weight
`ω̂ = ω/(1+i)` at `i = 3%` it is `ω̂/(1 − ω̂) = ω/(1 + i − ω) = 80/23 ≈ 3.48%`. -/
theorem fig31_linear_exact_coeff :
    (0.8 : ℝ) / (1 - 0.8) = 4 ∧ (0.8 / 1.03 : ℝ) / (1 - 0.8 / 1.03) = 80 / 23 ∧
      (3.47 : ℝ) < 80 / 23 ∧ (80 / 23 : ℝ) < 3.48 := by
  norm_num

end Cochrane.Generality.LogLinearIdentities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# State variables: the simplest fiscal-theory model by undetermined coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.9.1, pp. 576–577.

The model (1.47)–(1.50): `i_t = E_t π_{t+1}`, `ρv_{t+1} = v_t + i_t − π_{t+1} − s_{t+1}`,
`i_t = u_{i,t}`, `s_t = u_{s,t}`, with AR(1) disturbances.

## Main results

* `Eqm` (the equilibrium conditions), `eqm_solves` (taking `E_t` of (1.48) gives the forward
  equation `v_t = ρ E_t v_{t+1} + E_t s_{t+1}`), `eqm_infl`.
* Existence and uniqueness with bounded debt: `vstar`, `vstar_apply`, `inflStar`, `msv_exists`,
  `msv_v_unique`, `msv_unique`, `msv_determinacy` (an equilibrium has bounded `v` iff `v` is the
  forward solution).
* Survey error E24: the general corrected formula `msv_infl_innov`
  (`π_{t+1} = i_t − ΔE_{t+1}∑_j ρʲ s_{t+1+j}`, minus, not plus); the AR(1) closed forms
  `vstar_ar1`, `msv_solution` (`v_t = η_s u_{s,t}/(1 − ρη_s)`,
  `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`), `msv_solution_is_eqm`; the printed sign fails:
  `msv_printed_not_eqm`, with a genuine-uncertainty case `msv_printed_fails_coin`.
* Undetermined coefficients (p. 577): `GuessOK`, `msv_coeffs_iff` (the guess works iff
  `A = [[1, 0], [0, η_s/(1−ρη_s)]]`, `B = [[0, −1/(1−ρη_s)], [0, 0]]`, under `ρ ≠ 0`,
  `ρη_i ≠ 1`, `ρη_s ≠ 1`), `msv_coeffs_printed_fails` (the printed `B_{πs} = +1/(1−ρη_s)`).
* The explosive root (restated from the Woodford Chapter 4 project, `Fiscal.lean`): `dRec`,
  `eq_dRec`, `abs_rec_le`, `rec_bounded`, `rec_unbounded`; `msv_debt_rec` (debt follows `dRec`
  with `γ = ρ⁻¹ > 1`), `msv_debt_not_bibo`, `msv_deviation_iterate` and
  `msv_deviation_explodes` (a non-fundamental debt path diverges like `ρ⁻ᵏ` in expectation).
-/

namespace Cochrane.Generality.MSV

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), A1 (1.47)–(1.50), p. 576: `(π, v)` is an equilibrium of the simplest model
given the disturbances `u_i = i` and `u_s = s`: both adapted, `i_t = E_t π_{t+1}` (1.47) and
`ρv_{t+1} = v_t + i_t − π_{t+1} − s_{t+1}` (1.48). -/
def Eqm (ρ : ℝ) (ui us infl v : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted infl ∧ 𝔼.Adapted v ∧ (∀ t, 𝔼.E t (infl (t + 1)) = ui t) ∧
    ∀ t ω, ρ * v (t + 1) ω = v t ω + ui t ω - infl (t + 1) ω - us (t + 1) ω

/-- Cochrane (2023), A1 (1.47)–(1.48), p. 576: taking `E_t` of (1.48) and using (1.47) gives the
forward equation `v_t = ρ E_t v_{t+1} + E_t s_{t+1}`. -/
theorem eqm_solves {ρ : ℝ} {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (h : Eqm 𝔼 ρ ui us infl v) :
    ForwardSolution.Solves 𝔼 ρ (fun t => 𝔼.E t (us (t + 1))) v := by
  obtain ⟨-, hv, h47, h48⟩ := h
  intro t
  have hfun : ρ • v (t + 1) = v t + ui t - infl (t + 1) - us (t + 1) := by
    funext ω
    exact h48 t ω
  have hE := congrArg (𝔼.E t) hfun
  rw [map_smul, map_sub, map_sub, map_add, hv t, hui t, h47 t] at hE
  rw [hE]
  abel

/-- Cochrane (2023), A1 (1.48), p. 576: in an equilibrium, inflation is
`π_{t+1} = v_t + i_t − s_{t+1} − ρv_{t+1}`. -/
theorem eqm_infl {ρ : ℝ} {ui us infl v : ℕ → Ω → ℝ} (h : Eqm 𝔼 ρ ui us infl v) (t : ℕ)
    (ω : Ω) : infl (t + 1) ω = v t ω + ui t ω - us (t + 1) ω - ρ * v (t + 1) ω := by
  linarith [h.2.2.2 t ω]

/-- Cochrane (2023), A1 p. 576: the forward solution for debt,
`v*_t = ∑_{k≥0} ρᵏ E_t s_{t+1+k}`. -/
noncomputable def vstar (ρ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries ρ (fun t => 𝔼.E t (us (t + 1)))

/-- Cochrane (2023), A1 p. 576: `v*_t = ∑_k ρᵏ E_t s_{t+k+1}` (law of iterated expectations). -/
theorem vstar_apply (ρ : ℝ) (us : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    vstar 𝔼 ρ us t ω = ∑' k, ρ ^ k * 𝔼.E t (us (t + k + 1)) ω := by
  unfold vstar ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  rw [𝔼.tower (Nat.le_add_right t k)]

/-- Cochrane (2023), A1 p. 576: the forcing `E_t s_{t+1}` is adapted and bounded by the bound
of `s`. -/
theorem forcing_ok {us : ℕ → Ω → ℝ} {K : ℝ} (hus : ∀ t ω, |us t ω| ≤ K) :
    𝔼.Adapted (fun t => 𝔼.E t (us (t + 1))) ∧ ∀ t ω, |𝔼.E t (us (t + 1)) ω| ≤ K :=
  ⟨fun t => 𝔼.E_E_self t _, fun t ω => 𝔼.abs_E_le (hus (t + 1)) t ω⟩

/-- Cochrane (2023), A1 p. 576: the equilibrium inflation built from the forward solution,
`π*_{t+1} = v*_t + i_t − s_{t+1} − ρv*_{t+1}` (`π*_0 = 0`; date-0 inflation is not determined by
the model). -/
noncomputable def inflStar (ρ : ℝ) (ui us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => fun ω => vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω

/-- Cochrane (2023), A1 p. 576 ("We know the answer already"): for bounded adapted
disturbances and `|ρ| < 1`, the forward solution and its inflation form a bounded equilibrium. -/
theorem msv_exists {ρ K : ℝ} (hρ : |ρ| < 1) {ui us : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (hus : 𝔼.Adapted us) (huib : BoundedProc ui) (husb : ∀ t ω, |us t ω| ≤ K) :
    Eqm 𝔼 ρ ui us (inflStar 𝔼 ρ ui us) (vstar 𝔼 ρ us) ∧ BoundedProc (vstar 𝔼 ρ us) ∧
      BoundedProc (inflStar 𝔼 ρ ui us) := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 hρ hwb hwa
  have hva := ForwardSolution.forwardSeries_adapted_abs 𝔼 hρ hwb
  have hvb := ForwardSolution.forwardSeries_bounded_abs 𝔼 hρ hwb
  change ForwardSolution.Solves 𝔼 ρ _ (vstar 𝔼 ρ us) at hsol
  change 𝔼.Adapted (vstar 𝔼 ρ us) at hva
  change BoundedProc (vstar 𝔼 ρ us) at hvb
  refine ⟨⟨?_, hva, ?_, ?_⟩, hvb, ?_⟩
  · intro t
    rcases t with _ | t
    · exact map_zero _
    · have he : inflStar 𝔼 ρ ui us (t + 1) =
          vstar 𝔼 ρ us t + ui t - us (t + 1) - ρ • vstar 𝔼 ρ us (t + 1) := by
        funext ω
        rfl
      rw [he, map_sub, map_sub, map_add, map_smul, ForwardSolution.E_of_known 𝔼
        (Nat.le_succ t) (hva t), ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hui t),
        hus (t + 1), hva (t + 1)]
  · intro t
    have he : inflStar 𝔼 ρ ui us (t + 1) =
        vstar 𝔼 ρ us t + ui t - us (t + 1) - ρ • vstar 𝔼 ρ us (t + 1) := by
      funext ω
      rfl
    rw [he, map_sub, map_sub, map_add, map_smul, hva t, hui t, hsol t]
    beta_reduce
    abel
  · intro t ω
    change ρ * vstar 𝔼 ρ us (t + 1) ω = vstar 𝔼 ρ us t ω + ui t ω -
      (vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω) - us (t + 1) ω
    ring
  · obtain ⟨Kv, hKv⟩ := hvb
    obtain ⟨Ki, hKi⟩ := huib
    refine ⟨|Kv| + |Ki| + |K| + |ρ| * |Kv|, fun t ω => ?_⟩
    rcases t with _ | t
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      positivity
    · change |vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω| ≤ _
      have h1 := (hKv t ω).trans (le_abs_self Kv)
      have h2 := (hKi t ω).trans (le_abs_self Ki)
      have h3 := (husb (t + 1) ω).trans (le_abs_self K)
      have h4 : |ρ * vstar 𝔼 ρ us (t + 1) ω| ≤ |ρ| * |Kv| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hKv (t + 1) ω).trans (le_abs_self Kv))
          (abs_nonneg ρ)
      calc _ ≤ |vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| :=
            abs_sub _ _
        _ ≤ |vstar 𝔼 ρ us t ω + ui t ω| + |us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| := by
            gcongr
            exact abs_sub _ _
        _ ≤ |vstar 𝔼 ρ us t ω| + |ui t ω| + |us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| := by
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by linarith

/-- Cochrane (2023), A1 p. 576–577 (uniqueness): in any equilibrium with bounded debt, debt is
the forward solution `v = v*`. -/
theorem msv_v_unique {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) :
    v = vstar 𝔼 ρ us := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 hρ hwb hwa (eqm_solves 𝔼 hui h) hvb

/-- Cochrane (2023), A1 p. 576–577: two equilibria with bounded debt have the same debt and the
same inflation `π_{t+1}` at every date. -/
theorem msv_unique {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl₁ v₁ infl₂ v₂ : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h₁ : Eqm 𝔼 ρ ui us infl₁ v₁)
    (h₂ : Eqm 𝔼 ρ ui us infl₂ v₂) (hb₁ : BoundedProc v₁) (hb₂ : BoundedProc v₂) :
    v₁ = v₂ ∧ ∀ t, infl₁ (t + 1) = infl₂ (t + 1) := by
  have e₁ := msv_v_unique 𝔼 hρ hui husb h₁ hb₁
  have e₂ := msv_v_unique 𝔼 hρ hui husb h₂ hb₂
  refine ⟨e₁.trans e₂.symm, fun t => funext fun ω => ?_⟩
  rw [eqm_infl 𝔼 h₁, eqm_infl 𝔼 h₂, e₁, e₂]

/-- Cochrane (2023), A1 p. 577 ("Determinacy comes here from the assumption that `v_t` is a
time-invariant function of the state variables", made precise): an equilibrium has bounded debt
iff its debt is the forward solution. -/
theorem msv_determinacy {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) :
    BoundedProc v ↔ v = vstar 𝔼 ρ us := by
  refine ⟨msv_v_unique 𝔼 hρ hui husb h, fun he => ?_⟩
  rw [he]
  exact ForwardSolution.forwardSeries_bounded_abs 𝔼 hρ (forcing_ok 𝔼 husb).2

/-- Cochrane (2023), A1 p. 576 (survey E24, corrected): in any equilibrium with bounded debt,
`π_{t+1} = i_t − ΔE_{t+1} ∑_{j≥0} ρʲ s_{t+1+j}`, where the innovation is
`∑_j ρʲ E_{t+1}s_{t+1+j} − ∑_j ρʲ E_t s_{t+1+j}` (the book prints `+`). -/
theorem msv_infl_innov {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (hus : 𝔼.Adapted us) (husb : ∀ t ω, |us t ω| ≤ K)
    (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = ui t ω - (∑' j, ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω -
      ∑' j, ρ ^ j * 𝔼.E t (us (t + 1 + j)) ω) := by
  have hv := msv_v_unique 𝔼 hρ hui husb h hvb
  have hsum : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right K)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (husb _) _ ω) (pow_nonneg (abs_nonneg _) j)
  have h1 : ∑' j, ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω =
      us (t + 1) ω + ρ * vstar 𝔼 ρ us (t + 1) ω := by
    rw [hsum.tsum_eq_zero_add, vstar_apply, ← tsum_mul_left, pow_zero, one_mul, add_zero,
      hus (t + 1)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [pow_succ, show t + 1 + (k + 1) = t + 1 + k + 1 by omega]
    ring
  have h2 : ∑' j, ρ ^ j * 𝔼.E t (us (t + 1 + j)) ω = vstar 𝔼 ρ us t ω := by
    rw [vstar_apply]
    refine tsum_congr fun k => ?_
    rw [show t + 1 + k = t + k + 1 by omega]
  rw [h1, h2, eqm_infl 𝔼 h, hv]
  ring

/-- Cochrane (2023), A1 p. 576: with an AR(1) surplus `E_t s_{t+1} = η_s s_t`, `|ρη_s| < 1`, the
forward solution is `v*_t = η_s s_t/(1 − ρη_s)`. -/
theorem vstar_ar1 {ρ ηs : ℝ} (hρη : |ρ * ηs| < 1) {us : ℕ → Ω → ℝ} (har : 𝔼.IsAR1 ηs us)
    (t : ℕ) (ω : Ω) : vstar 𝔼 ρ us t ω = ηs / (1 - ρ * ηs) * us t ω := by
  rw [vstar_apply]
  have he : ∀ k, ρ ^ k * 𝔼.E t (us (t + k + 1)) ω = ηs * us t ω * (ρ * ηs) ^ k := by
    intro k
    rw [show t + k + 1 = t + (k + 1) by omega, 𝔼.ar1_iterate har, Pi.smul_apply, smul_eq_mul,
      mul_pow, pow_succ]
    ring
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, div_eq_mul_inv]
  ring

/-- Cochrane (2023), A1 p. 576 (survey E24, corrected closed forms): with AR(1) surpluses, in any
equilibrium with bounded debt, `v_t = η_s u_{s,t}/(1 − ρη_s)` and
`π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`, `ε_{s,t+1} = u_{s,t+1} − η_s u_{s,t}`. -/
theorem msv_solution {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) :
    (∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω) ∧
      ∀ t ω, infl (t + 1) ω = ui t ω - (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) := by
  have hv := msv_v_unique 𝔼 hρ hui husb h hvb
  have hvt : ∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω := fun t ω => by
    rw [hv, vstar_ar1 𝔼 hρη har]
  refine ⟨hvt, fun t ω => ?_⟩
  have hne : 1 - ρ * ηs ≠ 0 := by
    intro h0
    have : ρ * ηs = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  have hne2 : 1 - ηs * ρ ≠ 0 := by rwa [mul_comm]
  rw [eqm_infl 𝔼 h, hvt, hvt]
  field_simp
  ring

/-- Cochrane (2023), A1 p. 576: the corrected closed forms are an equilibrium (with bounded debt),
for bounded adapted `u_i` and bounded AR(1) `u_s`. -/
theorem msv_solution_is_eqm {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (huib : BoundedProc ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K) :
    ∃ infl v : ℕ → Ω → ℝ, Eqm 𝔼 ρ ui us infl v ∧ BoundedProc v ∧
      (∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω) ∧
      ∀ t ω, infl (t + 1) ω = ui t ω - (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) := by
  obtain ⟨he, hvb, -⟩ := msv_exists 𝔼 hρ hui har.1 huib husb
  obtain ⟨h1, h2⟩ := msv_solution 𝔼 hρ hρη hui har husb he hvb
  exact ⟨_, _, he, hvb, h1, h2⟩

/-- Cochrane (2023), A1 p. 576 (survey E24): the printed `π_{t+1} = u_{i,t} + ε_{s,t+1}/(1 − ρη_s)`
is not the inflation of any equilibrium with bounded debt as soon as some surplus shock
`ε_{s,t+1}` is nonzero. -/
theorem msv_printed_not_eqm {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K)
    (hprinted : ∀ t ω, infl (t + 1) ω = ui t ω + (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs))
    (hshock : ∃ t ω, us (t + 1) ω - ηs * us t ω ≠ 0) :
    ¬ (Eqm 𝔼 ρ ui us infl v ∧ BoundedProc v) := by
  rintro ⟨h, hvb⟩
  obtain ⟨t, ω, hε⟩ := hshock
  have hc := (msv_solution 𝔼 hρ hρη hui har husb h hvb).2 t ω
  rw [hprinted t ω] at hc
  have hne : 1 - ρ * ηs ≠ 0 := by
    intro h0
    have : ρ * ηs = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  have : (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) = 0 := by linarith
  rcases div_eq_zero_iff.mp this with h0 | h0
  · exact hε h0
  · exact hne h0

/-- Cochrane (2023), A1 p. 576: the i.i.d. coin-flip surplus `u_s = coinAR1 0` is bounded by one. -/
theorem coin_bdd (t : ℕ) (ω : Bool × Bool) : |ExpectationsFiniteTree.coinAR1 0 t ω| ≤ 1 := by
  rcases t with _ | t
  · simp [ExpectationsFiniteTree.coinAR1]
  · simp only [ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
      ExpectationsFiniteTree.coinShock]
    split_ifs <;> norm_num

/-- Cochrane (2023), A1 p. 576 (survey E24, genuine-uncertainty instance): on the coin-flip tree
with `ρ = 1/2`, `u_i = 0` and i.i.d. surplus shocks `u_s = ε_s = ±1`, the corrected solution is a
bounded equilibrium, while no bounded-debt equilibrium has the printed inflation. -/
theorem msv_printed_fails_coin {infl v : ℕ → Bool × Bool → ℝ}
    (hprinted : ∀ t ω, infl (t + 1) ω = 0 + (ExpectationsFiniteTree.coinAR1 0 (t + 1) ω -
      0 * ExpectationsFiniteTree.coinAR1 0 t ω) / (1 - 1 / 2 * 0)) :
    (∃ infl' v' : ℕ → Bool × Bool → ℝ,
      Eqm ExpectationsFiniteTree.coinSystem (1 / 2) 0 (ExpectationsFiniteTree.coinAR1 0) infl' v'
        ∧ BoundedProc v') ∧
      ¬ (Eqm ExpectationsFiniteTree.coinSystem (1 / 2) 0 (ExpectationsFiniteTree.coinAR1 0)
        infl v ∧ BoundedProc v) := by
  have hρ : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hρη : |(1 / 2 : ℝ) * 0| < 1 := by norm_num
  have hui : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  have har := ExpectationsFiniteTree.coinAR1_isAR1 0
  refine ⟨?_, msv_printed_not_eqm _ hρ hρη hui har coin_bdd hprinted ⟨0, (true, true), ?_⟩⟩
  · obtain ⟨infl', v', he, hvb, -⟩ := msv_solution_is_eqm _ hρ hρη hui ⟨0, fun _ _ => by simp⟩
      har coin_bdd
    exact ⟨infl', v', he, hvb⟩
  · rw [(ExpectationsFiniteTree.coinAR1_nondegenerate 0).1]
    norm_num

/-! ### Undetermined coefficients (p. 577) -/

/-- Cochrane (2023), A1 p. 576–577: the guess `π_{t+1} = A_{πi}u_{i,t} + A_{πs}u_{s,t} +
B_{πi}ε_{i,t+1} + B_{πs}ε_{s,t+1}`, `v_t = A_{vi}u_{i,t} + A_{vs}u_{s,t} + B_{vi}ε_{i,t+1} +
B_{vs}ε_{s,t+1}` satisfies (1.47) (with `E_t ε_{t+1} = 0`) and (1.48) (with
`u_{t+1} = ηu_t + ε_{t+1}` and free date-`t+2` shocks) for all values of states and shocks. -/
def GuessOK (ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs : ℝ) : Prop :=
  (∀ ui us : ℝ, aπi * ui + aπs * us = ui) ∧
    ∀ ui us ei es ei' es' : ℝ,
      (aπi * ui + aπs * us + bπi * ei + bπs * es) - (avi * ui + avs * us + bvi * ei + bvs * es) =
        -ρ * (avi * (ηi * ui + ei) + avs * (ηs * us + es) + bvi * ei' + bvs * es') + ui -
          (ηs * us + es)

/-- Cochrane (2023), A1 p. 577 ("Solving, we find the right answer"), corrected (survey E24): the
guess works iff `A = [[1, 0], [0, η_s/(1−ρη_s)]]` and `B = [[0, −1/(1−ρη_s)], [0, 0]]`
(assuming `ρ ≠ 0`, `ρη_i ≠ 1`, `ρη_s ≠ 1`). -/
theorem msv_coeffs_iff {ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs : ℝ} (hρ : ρ ≠ 0)
    (hi : ρ * ηi ≠ 1) (hs : ρ * ηs ≠ 1) :
    GuessOK ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs ↔
      aπi = 1 ∧ aπs = 0 ∧ avi = 0 ∧ avs = ηs / (1 - ρ * ηs) ∧ bπi = 0 ∧
        bπs = -(1 / (1 - ρ * ηs)) ∧ bvi = 0 ∧ bvs = 0 := by
  have hs' : 1 - ρ * ηs ≠ 0 := fun h => hs (by linarith)
  have hi' : 1 - ρ * ηi ≠ 0 := fun h => hi (by linarith)
  constructor
  · rintro ⟨h1, h2⟩
    have a1 : aπi = 1 := by simpa using h1 1 0
    have a2 : aπs = 0 := by simpa using h1 0 1
    have d1 : bvi = 0 := by
      have := h2 0 0 0 0 1 0
      simp only [mul_zero, add_zero, sub_zero, zero_add, mul_one] at this
      rcases mul_eq_zero.mp (show ρ * bvi = 0 by linarith) with h | h
      · exact absurd h hρ
      · exact h
    have d2 : bvs = 0 := by
      have := h2 0 0 0 0 0 1
      simp only [mul_zero, add_zero, sub_zero, zero_add, mul_one] at this
      rcases mul_eq_zero.mp (show ρ * bvs = 0 by linarith) with h | h
      · exact absurd h hρ
      · exact h
    have c1 : avi = 0 := by
      have := h2 1 0 0 0 0 0
      simp only [mul_zero, add_zero, sub_zero, mul_one] at this
      rw [a1] at this
      have : avi * (1 - ρ * ηi) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hi'
    have c2 : avs = ηs / (1 - ρ * ηs) := by
      have := h2 0 1 0 0 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [a2] at this
      rw [eq_div_iff hs']
      linarith
    have b1 : bπi = 0 := by
      have := h2 0 0 1 0 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [c1, d1] at this
      linarith
    have b2 : bπs = -(1 / (1 - ρ * ηs)) := by
      have := h2 0 0 0 1 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [c2, d2] at this
      field_simp
      field_simp at this
      linarith
    exact ⟨a1, a2, c1, c2, b1, b2, d1, d2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fun ui us => by ring, fun ui us ei es ei' es' => ?_⟩
    field_simp
    ring

/-- Cochrane (2023), A1 p. 577 (survey E24): the printed coefficient `B_{πs} = +1/(1 − ρη_s)`
(with the other printed entries) fails the undetermined-coefficients conditions. -/
theorem msv_coeffs_printed_fails {ρ ηi ηs : ℝ} (hρ : ρ ≠ 0) (hi : ρ * ηi ≠ 1)
    (hs : ρ * ηs ≠ 1) :
    ¬ GuessOK ρ ηi ηs 1 0 0 (1 / (1 - ρ * ηs)) 0 (ηs / (1 - ρ * ηs)) 0 0 := by
  intro h
  have := ((msv_coeffs_iff hρ hi hs).mp h).2.2.2.2.2.1
  have hs' : 1 - ρ * ηs ≠ 0 := fun h => hs (by linarith)
  have h2 : 1 / (1 - ρ * ηs) = 0 := by linarith
  exact one_div_ne_zero hs' h2

/-! ### The explosive root (restated from the Woodford Chapter 4 project) -/

/-- Cochrane (2023), A1 (1.48), p. 576 (restated from the Woodford Chapter 4 project, (4.5)): the
path generated recursively from `d_0` and inputs `u_t`: `d_{t+1} = γ d_t + u_t`. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Cochrane (2023), A1 p. 576 (restated from the Woodford Chapter 4 project): a solution of
`d_{t+1} = γ d_t + u_t` is determined by `d_0`: it is `dRec`. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 2/4 projects): a stable
scalar recursion `x_{t+1} = λx_t + u_t`, `|λ| < 1`, with bounded inputs stays bounded. -/
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

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 4 project): for `|γ| < 1` the
scalar recursion `d_{t+1} = γd_t + u_t` is bounded-input-bounded-state. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 4 project): for `|γ| ≥ 1` the
scalar recursion is not bounded-input-bounded-state: with `s = sign γ` and inputs
`u_t = ε s^{t+1}`, the path from `d_0 = 0` satisfies `|d_t| ≥ εt`. -/
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

/-- Cochrane (2023), A1 (1.48), p. 576: in any equilibrium, debt follows the recursion `dRec` with
the explosive root `γ = ρ⁻¹` and inputs `ρ⁻¹(i_t − π_{t+1} − s_{t+1})`. -/
theorem msv_debt_rec {ρ : ℝ} (hρ : ρ ≠ 0) {ui us infl v : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 ρ ui us infl v) :
    v = dRec ρ⁻¹ (fun t ω => ρ⁻¹ * (ui t ω - infl (t + 1) ω - us (t + 1) ω)) (v 0) := by
  refine eq_dRec fun t => funext fun ω => ?_
  have := h.2.2.2 t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith

/-- Cochrane (2023), A1 p. 577: since `|ρ⁻¹| ≥ 1` for `0 < |ρ| ≤ 1`, the debt recursion
`d_{t+1} = ρ⁻¹d_t + u_t` is not bounded-input-bounded-state: bounded inputs can produce
`|d_t| ≥ εt`. Boundedness of debt is therefore a genuine restriction. -/
theorem msv_debt_not_bibo {ρ ε : ℝ} (hρ0 : ρ ≠ 0) (hρ : |ρ| ≤ 1) (hε : 0 ≤ ε)
    {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d (t + 1) = ρ⁻¹ • d t +
      fun _ => ε * (if 0 ≤ ρ⁻¹ then (1 : ℝ) else -1) ^ (t + 1))
    (h0 : d 0 = 0) : ∀ t ω, ε * t ≤ |d t ω| := by
  have hγ : 1 ≤ |ρ⁻¹| := by
    rw [abs_inv]
    exact one_le_inv_iff₀.mpr ⟨abs_pos.mpr hρ0, hρ⟩
  exact rec_unbounded hγ hε hd h0

/-- Cochrane (2023), A1 p. 577: the deviation `d = v − v*` of an equilibrium debt path from the
forward solution obeys `d_s = ρᵏ E_s d_{s+k}`, i.e. `E_s d_{s+k} = ρ⁻ᵏ d_s`. -/
theorem msv_deviation_iterate {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (s k : ℕ) :
    v s - vstar 𝔼 ρ us s = ρ ^ k • 𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  have h1 := eqm_solves 𝔼 hui h
  have h2 := ForwardSolution.forwardSeries_solves_abs 𝔼 hρ hwb hwa
  have hd : ∀ t, (v - vstar 𝔼 ρ us) t = ρ • 𝔼.E t ((v - vstar 𝔼 ρ us) (t + 1)) := by
    intro t
    simp only [Pi.sub_apply, map_sub, smul_sub]
    rw [h1 t]
    unfold vstar
    rw [h2 t]
    abel
  exact 𝔼.forward_iterate hd s k

/-- Cochrane (2023), A1 p. 577 (the explosive root `ρ⁻¹`): if an equilibrium's debt differs from the
forward solution at some date and state, its expected deviation explodes,
`|E_s(v_{s+k} − v*_{s+k})| = |ρ|⁻ᵏ|v_s − v*_s| → ∞`. -/
theorem msv_deviation_explodes {ρ K : ℝ} (hρ0 : ρ ≠ 0) (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (s : ℕ)
    (ω : Ω) (hne : v s ω ≠ vstar 𝔼 ρ us s ω) :
    Tendsto (fun k => |𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) ω|) atTop atTop := by
  have he : ∀ k, |𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) ω| =
      |ρ⁻¹| ^ k * |v s ω - vstar 𝔼 ρ us s ω| := by
    intro k
    have h1 := congrFun (msv_deviation_iterate 𝔼 hρ hui husb h s k) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, abs_mul, abs_pow, ← mul_assoc, ← mul_pow, abs_inv, inv_mul_cancel₀
      (abs_ne_zero.mpr hρ0), one_pow, one_mul]
  simp_rw [he]
  have hγ : 1 < |ρ⁻¹| := by
    rw [abs_inv]
    exact one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hρ0, hρ⟩
  exact (tendsto_pow_atTop_atTop_of_one_lt hγ).atTop_mul_const (abs_pos.mpr (sub_ne_zero.mpr hne))

end Cochrane.Generality.MSV

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous time with short-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6 (box p. 71) and §3.6.1,
pp. 71–74, and Online Appendix A1.4, pp. 564–565.

All paths are deterministic (perfect foresight) functions `ℝ → ℝ`. From a date `t` on, the real
value of government debt `V = B/P` obeys the flow identity (3.30) `V' = (i − π)V − s` with
`π = P'/P`, which we derive from the nominal flow (3.29) `B' = iB − Ps`. Writing `r = i − π` and
`D(t, τ) = exp(−∫_t^τ r)` we prove, for a real rate continuous on `[t, ∞)` and an absolutely
integrable discounted surplus stream `D(t, ·)s`:

* the finite-horizon identity `D(t,T)V(T) = V(t) − ∫_t^T D(t,τ)s(τ)dτ`;
* the valuation equation (3.31) `V(t) = ∫_t^∞ D(t,τ)s(τ)dτ` holds **iff** the transversality
  condition `D(t,T)V(T) → 0` holds;
* the present-value path solves the flow identity and the transversality condition (existence),
  every solution of the flow identity is the present value plus a bubble `c/D(t,·)`, and the
  bubble vanishes iff the transversality condition holds (uniqueness);
* the price level is determined, `P(t) = B(t)/∫D s`, there is no positive price level when the
  present value of surpluses is not positive, and news about surpluses moves the price level by
  the ratio of present values (jumps);
* the discount factor `Λ` with `Λ'/Λ = −r` gives `Λ(τ)/Λ(t) = D(t,τ)`; the A1 (1.26) identities;
  the "work up or down" chains of A1.4 for `Λ` and for the ex-post return `W` (3.32)–(3.33),
  including the closed form `W(t)/W(0) = exp(∫_0^t i)P(0)/P(t)`;
* the constant-rate special case of p. 74 and the constant-surplus value `s/r`.

Price levels may jump at the initial date `t`: all paths are only required to be continuous on
`[t, ∞)` and differentiable on `(t, ∞)`.
-/

namespace Cochrane.Generality.ContinuousShort

open MeasureTheory Filter Topology

/-! ## Cumulated rates and the discount function -/

/-- Cochrane (2023), §3.6.1, p. 74: the cumulated rate `∫_t^τ r(u) du`. -/
noncomputable def cumRate (r : ℝ → ℝ) (t τ : ℝ) : ℝ := ∫ u in t..τ, r u

/-- Cochrane (2023), §3.6.1, p. 74: the discount function `D(t, τ) = exp(−∫_t^τ r)`, i.e. the
risk-neutral `Λ_τ/Λ_t` with instantaneous real rate `r`. -/
noncomputable def disc (r : ℝ → ℝ) (t τ : ℝ) : ℝ := Real.exp (-cumRate r t τ)

/-- Cochrane (2023), eq. (3.30), p. 73: the real value `V` obeys the flow identity
`V' = rV − s` on `[t, ∞)`: continuous on `[t, ∞)` (it may jump at `t` from earlier values) and
differentiable on `(t, ∞)`. -/
def FlowOn (r s V : ℝ → ℝ) (t : ℝ) : Prop :=
  ContinuousOn V (Set.Ici t) ∧ ∀ τ, t < τ → HasDerivAt V (r τ * V τ - s τ) τ

/-- Cochrane (2023), §3.6.1 and A1.4, p. 564: the transversality condition
`lim_{T→∞} D(t,T)V(T) = 0`. -/
def TVC (r V : ℝ → ℝ) (t : ℝ) : Prop :=
  Tendsto (fun T => disc r t T * V T) atTop (𝓝 0)

/-- Cochrane (2023), eq. (3.31), p. 73: the present value `∫_t^∞ D(t,τ)s(τ)dτ` of surpluses. -/
noncomputable def pv (r s : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in Set.Ioi t, disc r t τ * s τ

/-- Cochrane (2023), eq. (3.31), p. 73: the discounted surplus stream is (absolutely) integrable on
`(t, ∞)`, so that the present value is a genuine improper integral. -/
def PVIntegrable (r s : ℝ → ℝ) (t : ℝ) : Prop :=
  IntegrableOn (fun τ => disc r t τ * s τ) (Set.Ioi t)

/-- Cochrane (2023), §3.6.1: a function continuous on `[t, ∞)` is interval integrable on every
`[a, b]` with `t ≤ a`. -/
lemma intervalIntegrable_of_ici {f : ℝ → ℝ} {t a b : ℝ} (hf : ContinuousOn f (Set.Ici t))
    (ha : t ≤ a) (hb : t ≤ b) : IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine hf.mono fun x hx => ?_
  rcases Set.mem_uIcc.1 hx with h | h
  · exact le_trans ha h.1
  · exact le_trans hb h.1

/-- Cochrane (2023), §3.6.1: the cumulated rate is differentiable on `(t, ∞)` with derivative
`r`. -/
lemma hasDerivAt_cumRate {r : ℝ → ℝ} {t τ : ℝ} (hr : ContinuousOn r (Set.Ici t)) (hτ : t < τ) :
    HasDerivAt (cumRate r t) (r τ) τ := by
  have hopen : ContinuousOn r (Set.Ioi t) := hr.mono Set.Ioi_subset_Ici_self
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_of_ici hr le_rfl hτ.le)
    (hopen.stronglyMeasurableAtFilter isOpen_Ioi τ hτ)
    (hr.continuousAt (Ici_mem_nhds hτ))

/-- Cochrane (2023), §3.6.1: the cumulated rate is continuous on `[t, ∞)`. -/
lemma continuousOn_cumRate {r : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t)) :
    ContinuousOn (cumRate r t) (Set.Ici t) := by
  intro x hx
  have hx' : t ≤ x := hx
  have h1 : ContinuousOn (cumRate r t) (Set.uIcc t (x + 1)) :=
    intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_of_ici hr le_rfl (by linarith)) Set.left_mem_uIcc
  have hmem : x ∈ Set.uIcc t (x + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨hx', by linarith⟩
  refine (h1 x hmem).mono_of_mem_nhdsWithin ?_
  rw [Set.uIcc_of_le (by linarith)]
  have : Set.Ici t ∩ Set.Iic (x + 1) ∈ 𝓝[Set.Ici t] x :=
    inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  simpa [Set.Ici_inter_Iic] using this

/-- Cochrane (2023), §3.6.1: `∫_t^t r = 0`. -/
@[simp] lemma cumRate_self (r : ℝ → ℝ) (t : ℝ) : cumRate r t t = 0 := by
  simp [cumRate]

/-- Cochrane (2023), §3.6.1: cumulated rates add over adjacent intervals. -/
lemma cumRate_add {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : cumRate r t a + cumRate r a b = cumRate r t b :=
  intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_of_ici hr le_rfl ha)
    (intervalIntegrable_of_ici hr ha (ha.trans hab))

/-- Cochrane (2023), p. 74: with a constant rate `c`, `∫_t^τ c = c(τ − t)`. -/
lemma cumRate_const (c t τ : ℝ) : cumRate (fun _ => c) t τ = c * (τ - t) := by
  simp [cumRate, mul_comm]

/-- Cochrane (2023), §3.6.1: the discount function is positive. -/
lemma disc_pos (r : ℝ → ℝ) (t τ : ℝ) : 0 < disc r t τ := Real.exp_pos _

/-- Cochrane (2023), §3.6.1: `D(t, t) = 1`. -/
@[simp] lemma disc_self (r : ℝ → ℝ) (t : ℝ) : disc r t t = 1 := by
  simp [disc]

/-- Cochrane (2023), §3.6.1: the discount function is multiplicative,
`D(t,a)D(a,b) = D(t,b)` (`Λ_a/Λ_t · Λ_b/Λ_a = Λ_b/Λ_t`). -/
lemma disc_mul {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : disc r t a * disc r a b = disc r t b := by
  rw [disc, disc, disc, ← Real.exp_add, ← cumRate_add hr ha hab, neg_add]

/-- Cochrane (2023), §3.6.1: `D(a, b) = D(t, b)/D(t, a)` for `t ≤ a ≤ b`. -/
lemma disc_eq_div {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : disc r a b = disc r t b / disc r t a := by
  rw [← disc_mul hr ha hab]
  field_simp [(disc_pos r t a).ne']

/-- Cochrane (2023), p. 74: with a constant real rate, `Λ_τ/Λ_t = e^{−r(τ−t)}`. -/
lemma disc_const (c t τ : ℝ) : disc (fun _ => c) t τ = Real.exp (-(c * (τ - t))) := by
  rw [disc, cumRate_const]

/-- Cochrane (2023), §3.6.1: `d/dτ D(t,τ) = −r(τ)D(t,τ)` on `(t, ∞)`. -/
lemma hasDerivAt_disc {r : ℝ → ℝ} {t τ : ℝ} (hr : ContinuousOn r (Set.Ici t)) (hτ : t < τ) :
    HasDerivAt (disc r t) (-(r τ) * disc r t τ) τ := by
  have h := ((hasDerivAt_cumRate hr hτ).neg).exp
  have e : (fun x => Real.exp ((-cumRate r t) x)) = disc r t := rfl
  rw [e] at h
  convert h using 1
  simp only [disc, Pi.neg_apply]
  ring

/-- Cochrane (2023), §3.6.1: the discount function is continuous on `[t, ∞)`. -/
lemma continuousOn_disc {r : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t)) :
    ContinuousOn (disc r t) (Set.Ici t) :=
  Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr).neg

/-- Cochrane (2023), §3.6.1: a function continuous on `[t, ∞)` with zero derivative on `(t, ∞)`
is constant on `[t, ∞)` (via the fundamental theorem of calculus). -/
lemma eq_of_hasDerivAt_zero {f : ℝ → ℝ} {t : ℝ} (hc : ContinuousOn f (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt f 0 τ) {τ : ℝ} (hτ : t ≤ τ) : f τ = f t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ
    (hc.mono Set.Icc_subset_Ici_self) (fun x hx => hd x hx.1) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- Cochrane (2023), §3.6.1–§3.6.3, pp. 74–78: translating dates or maturities,
`∫_0^∞ f(x + j)dj = ∫_x^∞ f(u)du`. -/
theorem integral_Ioi_shift (f : ℝ → ℝ) (x : ℝ) :
    ∫ j in Set.Ioi 0, f (x + j) = ∫ u in Set.Ioi x, f u := by
  have hE : MeasurableEmbedding (fun j : ℝ => x + j) :=
    (Homeomorph.addLeft x).isClosedEmbedding.measurableEmbedding
  have h := hE.setIntegral_map (μ := volume) f (Set.Ioi x)
  rw [Measure.IsAddLeftInvariant.map_add_left_eq_self] at h
  rw [h]
  congr 1
  ext j
  simp

/-! ## The valuation equation (3.31) and the transversality condition -/

variable {r s V : ℝ → ℝ} {t : ℝ}

/-- Cochrane (2023), A1.4, p. 564: along the flow identity (3.30),
`d/dτ [D(t,τ)V(τ)] = −D(t,τ)s(τ)` ("`d(Λ_t B_t/P_t) = −s_tΛ_t dt`"). -/
theorem hasDerivAt_disc_mul (hr : ContinuousOn r (Set.Ici t)) (hV : FlowOn r s V t) {τ : ℝ}
    (hτ : t < τ) : HasDerivAt (fun x => disc r t x * V x) (-(disc r t τ * s τ)) τ := by
  have h := (hasDerivAt_disc hr hτ).mul (hV.2 τ hτ)
  convert h using 1
  ring

/-- Cochrane (2023), A1.4, p. 564: the finite-horizon present-value identity
`D(t,T)V(T) = V(t) − ∫_t^T D(t,τ)s(τ)dτ`, obtained by integrating (3.30) on `[t, T]`. -/
theorem pv_finite (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) {T : ℝ} (hT : t ≤ T) :
    disc r t T * V T = V t - ∫ τ in t..T, disc r t τ * s τ := by
  have hc : ContinuousOn (fun x => disc r t x * V x) (Set.Icc t T) :=
    ((continuousOn_disc hr).mul hV.1).mono Set.Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun x => -(disc r t x * s x)) volume t T :=
    intervalIntegrable_of_ici (((continuousOn_disc hr).mul hs).neg) le_rfl hT
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc
    (fun x hx => hasDerivAt_disc_mul hr hV hx.1) hint
  rw [intervalIntegral.integral_neg, disc_self, one_mul] at h
  linarith

/-- Cochrane (2023), eq. (3.31) and A1.4: along any solution of the flow identity, the
discounted terminal value converges, `D(t,T)V(T) → V(t) − ∫_t^∞ D(t,τ)s(τ)dτ`. -/
theorem tendsto_disc_mul (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) :
    Tendsto (fun T => disc r t T * V T) atTop (𝓝 (V t - pv r s t)) := by
  have h := (intervalIntegral_tendsto_integral_Ioi t hI tendsto_id).const_sub (V t)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [pv_finite hr hs hV hT]
  rfl

/-- Cochrane (2023), eq. (3.31), p. 73, and A1.4, pp. 564–565 ("work up or down"): along the flow
identity (3.30), the valuation equation `V(t) = ∫_t^∞ D(t,τ)s(τ)dτ` holds **iff** the
transversality condition `D(t,T)V(T) → 0` holds. -/
theorem valuation_iff_tvc (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) : V t = pv r s t ↔ TVC r V t := by
  have h := tendsto_disc_mul hr hs hV hI
  constructor
  · intro he
    rw [he, sub_self] at h
    exact h
  · intro htvc
    have := tendsto_nhds_unique h htvc
    linarith

/-- Cochrane (2023), §3.6.1: absolute integrability of the discounted surpluses from `t` implies
it from every later date `a ≥ t`. -/
theorem pvIntegrable_of_le (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) {a : ℝ}
    (ha : t ≤ a) : PVIntegrable r s a := by
  have h : IntegrableOn (fun τ => disc r t τ * s τ / disc r t a) (Set.Ioi a) :=
    (hI.mono_set (Set.Ioi_subset_Ioi ha)).div_const _
  refine h.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
  rw [disc_eq_div hr ha (le_of_lt hτ)]
  ring

/-- Cochrane (2023), §3.6.1: the present value at a later date `a ≥ t`,
`∫_a^∞ D(a,τ)s = (∫_t^∞ D(t,τ)s − ∫_t^a D(t,τ)s)/D(t,a)`. -/
theorem pv_eq_of_le (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) {a : ℝ}
    (ha : t ≤ a) : pv r s a = (pv r s t - ∫ τ in t..a, disc r t τ * s τ) / disc r t a := by
  have h1 : pv r s a = (∫ τ in Set.Ioi a, disc r t τ * s τ) / disc r t a := by
    rw [pv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    rw [disc_eq_div hr ha (le_of_lt hτ)]
    ring
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hI ha, pv]
  ring

/-- Cochrane (2023), §3.6.1: the closed form of the present-value path,
`pv(τ) = exp(∫_t^τ r)·(pv(t) − ∫_t^τ D(t,u)s(u)du)` on `[t, ∞)`. -/
theorem pv_eqOn_closed (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) :
    Set.EqOn (pv r s) (fun τ => Real.exp (cumRate r t τ) *
      (pv r s t - cumRate (fun u => disc r t u * s u) t τ)) (Set.Ici t) := by
  intro τ hτ
  rw [pv_eq_of_le hr hI hτ, disc, Real.exp_neg, div_inv_eq_mul, mul_comm]
  rfl

/-- Cochrane (2023), eq. (3.31), existence: the present-value path `τ ↦ ∫_τ^∞ D(τ,u)s(u)du`
solves the flow identity (3.30) on `[t, ∞)`. -/
theorem flowOn_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) : FlowOn r s (pv r s) t := by
  have hDs : ContinuousOn (fun u => disc r t u * s u) (Set.Ici t) := (continuousOn_disc hr).mul hs
  have hE := pv_eqOn_closed hr hI
  refine ⟨?_, fun τ hτ => ?_⟩
  · refine ContinuousOn.congr ?_ hE
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr)).mul
      (continuousOn_const.sub (continuousOn_cumRate hDs))
  · have h1 : HasDerivAt (fun x => Real.exp (cumRate r t x)) (Real.exp (cumRate r t τ) * r τ) τ :=
      (hasDerivAt_cumRate hr hτ).exp
    have h2 := h1.mul ((hasDerivAt_cumRate hDs hτ).const_sub (pv r s t))
    have hev : pv r s =ᶠ[𝓝 τ] (fun τ => Real.exp (cumRate r t τ) *
        (pv r s t - cumRate (fun u => disc r t u * s u) t τ)) := by
      filter_upwards [Ioi_mem_nhds hτ] with x hx
      exact hE (Set.mem_Ici.2 (le_of_lt hx))
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [hE (Set.mem_Ici.2 (le_of_lt hτ))]
    have hED : Real.exp (cumRate r t τ) * disc r t τ = 1 := by
      rw [disc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination (-(s τ)) * hED

/-- Cochrane (2023), eq. (3.31), existence: the present-value path satisfies the transversality
condition. -/
theorem tvc_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) : TVC r (pv r s) t := by
  have h := tendsto_disc_mul hr hs (flowOn_pv hr hs hI) hI
  rwa [sub_self] at h

/-- Cochrane (2023), §3.6.1: a solution of the flow identity on `[t, ∞)` also solves it on
`[a, ∞)` for every `a ≥ t`. -/
theorem FlowOn.mono (hV : FlowOn r s V t) {a : ℝ} (ha : t ≤ a) : FlowOn r s V a :=
  ⟨hV.1.mono (Set.Ici_subset_Ici.2 ha), fun τ hτ => hV.2 τ (lt_of_le_of_lt ha hτ)⟩

/-- Cochrane (2023), §3.6.1: the transversality condition at `t` implies it at every later date
`a ≥ t` (`D(a,T) = D(t,T)/D(t,a)`). -/
theorem TVC.mono (hr : ContinuousOn r (Set.Ici t)) (hT : TVC r V t) {a : ℝ} (ha : t ≤ a) :
    TVC r V a := by
  have h := hT.div_const (disc r t a)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [disc_eq_div hr ha hT]
  ring

/-- Cochrane (2023), eq. (3.31), p. 73, uniqueness: every solution of the flow identity (3.30)
that satisfies the transversality condition equals the present value of surpluses at every date
`τ ≥ t`, `V(τ) = ∫_τ^∞ D(τ,u)s(u)du`. -/
theorem eqOn_pv_of_tvc (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hT : TVC r V t) (hI : PVIntegrable r s t) :
    Set.EqOn V (pv r s) (Set.Ici t) := by
  intro a ha
  have ha' : t ≤ a := ha
  exact (valuation_iff_tvc (hr.mono (Set.Ici_subset_Ici.2 ha'))
    (hs.mono (Set.Ici_subset_Ici.2 ha')) (hV.mono ha') (pvIntegrable_of_le hr hI ha')).2
    (hT.mono hr ha')

/-- Cochrane (2023), eqs. (3.30)–(3.31), existence and uniqueness: the present-value path solves
the flow identity with the transversality condition, and any two such solutions coincide on
`[t, ∞)`. -/
theorem exists_unique_flow_tvc (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) :
    (FlowOn r s (pv r s) t ∧ TVC r (pv r s) t) ∧
      ∀ V₁ V₂ : ℝ → ℝ, FlowOn r s V₁ t → TVC r V₁ t → FlowOn r s V₂ t → TVC r V₂ t →
        Set.EqOn V₁ V₂ (Set.Ici t) := by
  refine ⟨⟨flowOn_pv hr hs hI, tvc_pv hr hs hI⟩, fun V₁ V₂ h1 t1 h2 t2 τ hτ => ?_⟩
  rw [eqOn_pv_of_tvc hr hs h1 t1 hI hτ, eqOn_pv_of_tvc hr hs h2 t2 hI hτ]

/-- Cochrane (2023), §3.6.1, A1.4: every solution of the flow identity is the present value plus
a "bubble" growing at the real rate: `V(τ) = pv(τ) + (V(t) − pv(t))/D(t,τ)` on `[t, ∞)`. -/
theorem flow_general_solution (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {τ : ℝ}
    (hτ : t ≤ τ) : V τ = pv r s τ + (V t - pv r s t) / disc r t τ := by
  have h1 := pv_finite hr hs hV hτ
  rw [pv_eq_of_le hr hI hτ]
  have hD := (disc_pos r t τ).ne'
  field_simp
  linarith

/-- Cochrane (2023), §3.6.1: the bubble paths `pv + c·exp(∫_t^· r)` solve the flow identity
(3.30) for every constant `c`. -/
theorem flowOn_bubble (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) (c : ℝ) :
    FlowOn r s (fun τ => pv r s τ + c * Real.exp (cumRate r t τ)) t := by
  have hP := flowOn_pv hr hs hI
  refine ⟨hP.1.add (continuousOn_const.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr))), fun τ hτ => ?_⟩
  have h := (hP.2 τ hτ).add (((hasDerivAt_cumRate hr hτ).exp).const_mul c)
  convert h using 1
  ring

/-- Cochrane (2023), A1.4 and A1.5 (cf. E23): a bubble path satisfies the transversality
condition iff the bubble is zero. -/
theorem tvc_bubble_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) (c : ℝ) :
    TVC r (fun τ => pv r s τ + c * Real.exp (cumRate r t τ)) t ↔ c = 0 := by
  have hP := tvc_pv hr hs hI
  have h : Tendsto (fun T => disc r t T * (pv r s T + c * Real.exp (cumRate r t T))) atTop
      (𝓝 c) := by
    have h2 := hP.add_const c
    rw [zero_add] at h2
    refine h2.congr' (Eventually.of_forall fun T => ?_)
    have hED : disc r t T * Real.exp (cumRate r t T) = 1 := by
      rw [disc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination (-c) * hED
  constructor
  · intro htvc
    exact tendsto_nhds_unique h htvc
  · rintro rfl
    exact h

/-- Cochrane (2023), eq. (3.31), uniqueness: a solution of the flow identity satisfies the
transversality condition iff it coincides with the present-value path on `[t, ∞)`. -/
theorem tvc_iff_eqOn_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) :
    TVC r V t ↔ Set.EqOn V (pv r s) (Set.Ici t) := by
  refine ⟨fun hT => eqOn_pv_of_tvc hr hs hV hT hI, fun h => ?_⟩
  exact (valuation_iff_tvc hr hs hV hI).1 (h (Set.mem_Ici.2 le_rfl))

/-- Cochrane (2023), A1.4, p. 564 ("work … down"): a path equal to the present value of
surpluses at every date `τ ≥ t` solves the flow identity (3.30) and the transversality
condition. -/
theorem flowOn_tvc_of_eqOn_pv (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t)
    (h : Set.EqOn V (pv r s) (Set.Ici t)) : FlowOn r s V t ∧ TVC r V t := by
  have hP := flowOn_pv hr hs hI
  refine ⟨⟨hP.1.congr h, fun τ hτ => ?_⟩, ?_⟩
  · have hev : V =ᶠ[𝓝 τ] pv r s := by
      filter_upwards [Ioi_mem_nhds hτ] with x hx
      exact h (Set.mem_Ici.2 (le_of_lt hx))
    rw [h (Set.mem_Ici.2 (le_of_lt hτ))]
    exact (hP.2 τ hτ).congr_of_eventuallyEq hev
  · refine (tvc_pv hr hs hI).congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    rw [h (Set.mem_Ici.2 hT)]

/-- Cochrane (2023), eqs. (3.30)–(3.31) and A1.4, pp. 564–565 (the flow and present-value
relations are equivalent, "work either up or down"): a path equals the present value of surpluses
at every date `τ ≥ t` iff it solves the flow identity (3.30) with the transversality
condition. -/
theorem eqOn_pv_iff_flowOn_tvc (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) :
    Set.EqOn V (pv r s) (Set.Ici t) ↔ FlowOn r s V t ∧ TVC r V t :=
  ⟨flowOn_tvc_of_eqOn_pv hr hs hI, fun h => eqOn_pv_of_tvc hr hs h.1 h.2 hI⟩

/-! ## Price-level determination and jumps -/

/-- Cochrane (2023), eq. (3.31), p. 73: price-level determination. Given predetermined nominal
debt `B(t) ≠ 0` and a nonzero present value of surpluses, a price level `P(t)` is consistent with
a path of real debt solving the flow identity (3.30) and the transversality condition with
`V(t) = B(t)/P(t)` **iff** `P(t) = B(t)/∫_t^∞ D(t,τ)s(τ)dτ`. -/
theorem price_level_determined (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {B0 P0 : ℝ} (hB : B0 ≠ 0)
    (hpv : pv r s t ≠ 0) :
    (∃ V : ℝ → ℝ, FlowOn r s V t ∧ TVC r V t ∧ V t = B0 / P0) ↔ P0 = B0 / pv r s t := by
  constructor
  · rintro ⟨V, hV, hT, hVt⟩
    have h := (valuation_iff_tvc hr hs hV hI).2 hT
    rw [hVt] at h
    have hP0 : P0 ≠ 0 := by
      rintro rfl
      rw [div_zero] at h
      exact hpv h.symm
    field_simp
    rw [← h]
    field_simp
  · intro hP
    refine ⟨pv r s, flowOn_pv hr hs hI, tvc_pv hr hs hI, ?_⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), eq. (3.31): with positive nominal debt and a positive present value of
surpluses the equilibrium price level `B(t)/∫D s` is positive. -/
theorem price_level_pos {B0 : ℝ} (hB : 0 < B0) (hpv : 0 < pv r s t) : 0 < B0 / pv r s t :=
  div_pos hB hpv

/-- Cochrane (2023), eq. (3.31): with positive nominal debt and a nonpositive present value of
surpluses there is no positive price level consistent with the flow identity and the
transversality condition. -/
theorem no_positive_price_level (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {B0 : ℝ} (hB : 0 < B0)
    (hpv : pv r s t ≤ 0) :
    ¬ ∃ P0 : ℝ, 0 < P0 ∧ ∃ V : ℝ → ℝ, FlowOn r s V t ∧ TVC r V t ∧ V t = B0 / P0 := by
  rintro ⟨P0, hP0, V, hV, hT, hVt⟩
  have h := (valuation_iff_tvc hr hs hV hI).2 hT
  have : 0 < B0 / P0 := div_pos hB hP0
  linarith

/-- Cochrane (2023), §3.6.1, p. 73 ("a diffusion or jump on the right-hand side … shows up in a
diffusion or jump in the price level"): nominal debt `B(t)` is predetermined, so news that changes
the real rates and surpluses from `(r₁, s₁)` to `(r₂, s₂)` moves the price level at `t` by the
ratio of present values, `P₂(t)/P₁(t) = pv₁/pv₂`. -/
theorem price_jump_ratio {r₁ s₁ r₂ s₂ : ℝ → ℝ} (hr₁ : ContinuousOn r₁ (Set.Ici t))
    (hs₁ : ContinuousOn s₁ (Set.Ici t)) (hI₁ : PVIntegrable r₁ s₁ t)
    (hr₂ : ContinuousOn r₂ (Set.Ici t)) (hs₂ : ContinuousOn s₂ (Set.Ici t))
    (hI₂ : PVIntegrable r₂ s₂ t) {B0 P₁ P₂ : ℝ} (hB : B0 ≠ 0) (hpv₁ : pv r₁ s₁ t ≠ 0)
    (hpv₂ : pv r₂ s₂ t ≠ 0)
    (h₁ : ∃ V : ℝ → ℝ, FlowOn r₁ s₁ V t ∧ TVC r₁ V t ∧ V t = B0 / P₁)
    (h₂ : ∃ V : ℝ → ℝ, FlowOn r₂ s₂ V t ∧ TVC r₂ V t ∧ V t = B0 / P₂) :
    P₂ / P₁ = pv r₁ s₁ t / pv r₂ s₂ t := by
  rw [(price_level_determined hr₁ hs₁ hI₁ hB hpv₁).1 h₁,
    (price_level_determined hr₂ hs₂ hI₂ hB hpv₂).1 h₂]
  field_simp

/-! ## The nominal flow (3.29) and the real flow (3.30) -/

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73: the nominal flow `B' = iB − Ps` implies the real
flow `V' = (i − π)V − s` for `V = B/P`, `π = P'/P` (quotient rule). -/
theorem hasDerivAt_real_of_nominal {i s B P : ℝ → ℝ} {dP τ : ℝ}
    (hB : HasDerivAt B (i τ * B τ - P τ * s τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => B x / P x) ((i τ - dP / P τ) * (B τ / P τ) - s τ) τ := by
  convert hB.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73, converse: the real flow for `V = B/P` implies
the nominal flow `B' = iB − Ps`. -/
theorem hasDerivAt_nominal_of_real {i s B P : ℝ → ℝ} {dP τ : ℝ}
    (hV : HasDerivAt (fun x => B x / P x) ((i τ - dP / P τ) * (B τ / P τ) - s τ) τ)
    (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ := by
  have h := hV.mul hP
  have hev : B =ᶠ[𝓝 τ] fun x => B x / P x * P x := by
    filter_upwards [hP.continuousAt.eventually_ne hP0] with x hx
    field_simp
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp
  ring

/-- Cochrane (2023), p. 73: the ex-post real return on short-term debt,
`dR = i dt + d(1/P)/(1/P)`, equals `(i − π)dt`: `(1/P)' = −π·(1/P)`. -/
theorem hasDerivAt_inv_price {P : ℝ → ℝ} {dP τ : ℝ} (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => 1 / P x) (-(dP / P τ) * (1 / P τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hP hP0
  convert h using 1
  field_simp
  ring

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73: nominal paths `B, P` (continuous on `[t, ∞)`, `P`
positive, the price level free to jump at `t`) obeying the nominal flow (3.29) on `(t, ∞)` give a
real value `B/P` obeying the flow identity (3.30) with real rate `i − P'/P`. -/
theorem flowOn_of_nominal {i s B P dP : ℝ → ℝ} (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hB : ∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => B τ / P τ) t :=
  ⟨hBc.div hPc fun x hx => (hPpos x hx).ne', fun τ hτ =>
    hasDerivAt_real_of_nominal (hB τ hτ) (hP τ hτ) (hPpos τ hτ.le).ne'⟩

/-- Cochrane (2023), eqs. (3.29)–(3.31): with nominal paths obeying (3.29), the transversality
condition on `B/P` and nonzero debt and present value, the price level at `t` is
`P(t) = B(t)/∫_t^∞ D(t,τ)s(τ)dτ` with `D` built from the real rate `i − π`. -/
theorem price_level_of_nominal {i s B P dP : ℝ → ℝ}
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hBc : ContinuousOn B (Set.Ici t)) (hPc : ContinuousOn P (Set.Ici t))
    (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hB : ∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ)
    (hT : TVC (fun τ => i τ - dP τ / P τ) (fun τ => B τ / P τ) t) (hB0 : B t ≠ 0)
    (hpv : pv (fun τ => i τ - dP τ / P τ) s t ≠ 0) :
    P t = B t / pv (fun τ => i τ - dP τ / P τ) s t :=
  (price_level_determined hr hs hI hB0 hpv).1
    ⟨_, flowOn_of_nominal hBc hPc hPpos hB hP, hT, rfl⟩

/-- Cochrane (2023), eqs. (3.29) and (3.31), A1.4, pp. 564–565: for a positive price path
differentiable on `(t, ∞)` (free to jump at `t`) and a nominal debt path continuous on
`[t, ∞)`, the valuation equation `B(τ)/P(τ) = ∫_τ^∞ D(τ,u)s(u)du` at every date `τ ≥ t` holds
iff the nominal flow (3.29) `B' = iB − Ps` holds on `(t, ∞)` together with the transversality
condition, where `D` discounts at the real rate `i − P'/P`. -/
theorem nominal_pv_iff_flow {i s B P dP : ℝ → ℝ}
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hBc : ContinuousOn B (Set.Ici t)) (hPc : ContinuousOn P (Set.Ici t))
    (hPpos : ∀ τ, t ≤ τ → 0 < P τ) (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    Set.EqOn (fun τ => B τ / P τ) (pv (fun τ => i τ - dP τ / P τ) s) (Set.Ici t) ↔
      (∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ) ∧
        TVC (fun τ => i τ - dP τ / P τ) (fun τ => B τ / P τ) t := by
  rw [eqOn_pv_iff_flowOn_tvc hr hs hI]
  constructor
  · rintro ⟨hF, hT⟩
    exact ⟨fun τ hτ => hasDerivAt_nominal_of_real (hF.2 τ hτ) (hP τ hτ) (hPpos τ hτ.le).ne', hT⟩
  · rintro ⟨hB, hT⟩
    exact ⟨flowOn_of_nominal hBc hPc hPpos hB hP, hT⟩

/-! ## Discount factors, A1 (1.26), and the A1.4 chains -/

/-- Cochrane (2023), §3.6.1, p. 74, and A1 (1.26), p. 564: a (deterministic) discount factor with
`Λ'/Λ = −r` on `(t, ∞)` satisfies `Λ(τ)/Λ(t) = exp(−∫_t^τ r)`, i.e. `Λ(τ) = Λ(t)D(t,τ)`. -/
theorem discountFactor_eq (hr : ContinuousOn r (Set.Ici t)) {Λ : ℝ → ℝ}
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    {τ : ℝ} (hτ : t ≤ τ) : Λ τ = Λ t * disc r t τ := by
  have hc : ContinuousOn (fun x => Λ x * Real.exp (cumRate r t x)) (Set.Ici t) :=
    hΛc.mul (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr))
  have hd : ∀ x, t < x → HasDerivAt (fun x => Λ x * Real.exp (cumRate r t x)) 0 x := by
    intro x hx
    convert (hΛ x hx).mul (hasDerivAt_cumRate hr hx).exp using 1
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [cumRate_self, Real.exp_zero, mul_one] at h
  rw [← h, disc, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Cochrane (2023), A1 (1.26), first line, p. 564: `r = −Λ'/Λ` is the same statement as
`Λ' = −rΛ` (for `Λ ≠ 0`). -/
theorem rate_eq_neg_logDeriv {Λ0 dΛ r0 : ℝ} (hΛ : Λ0 ≠ 0) : r0 = -(dΛ / Λ0) ↔ dΛ = -r0 * Λ0 := by
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), A1 (1.26), second line, p. 564: with `Λ' = −(i − π)Λ` and `π = P'/P`, the
nominal discount factor `Λ/P` satisfies `(Λ/P)' = −i·(Λ/P)`. -/
theorem hasDerivAt_nominal_discount {i Λ P : ℝ → ℝ} {dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i τ - dP / P τ) * Λ τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Λ x / P x) (-(i τ) * (Λ τ / P τ)) τ := by
  convert hΛ.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), A1 (1.26), third line, p. 564 ("a few lines of algebra starting from
(3.33)"): with `W' = (i − π)W` and `π = P'/P`, `(1/(PW))' = −i·(1/(PW))`. -/
theorem hasDerivAt_inv_PW {i W P : ℝ → ℝ} {dP τ : ℝ}
    (hW : HasDerivAt W ((i τ - dP / P τ) * W τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hW0 : W τ ≠ 0) :
    HasDerivAt (fun x => 1 / (P x * W x)) (-(i τ) * (1 / (P τ * W τ))) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div (hP.mul hW) (mul_ne_zero hP0 hW0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), A1.4, pp. 564–565 ("work either up or down"), discount-factor chain: with
`Λ' = −rΛ` and `Λ ≠ 0`, the flow `V' = rV − s` holds iff `d(ΛV) = −Λs`. -/
theorem flow_iff_Lambda {Λ : ℝ → ℝ} {τ : ℝ} (hΛ : HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ τ ≠ 0) :
    HasDerivAt V (r τ * V τ - s τ) τ ↔
      HasDerivAt (fun x => Λ x * V x) (-(Λ τ * s τ)) τ := by
  constructor
  · intro hV
    convert hΛ.mul hV using 1
    ring
  · intro h
    have hq := h.div hΛ hΛ0
    have hev : V =ᶠ[𝓝 τ] fun x => Λ x * V x / Λ x := by
      filter_upwards [hΛ.continuousAt.eventually_ne hΛ0] with x hx
      field_simp
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
    ring

/-- Cochrane (2023), A1.4, pp. 564–565, nominal discount-factor chain: with
`Λ' = −(i − π)Λ`, `π = P'/P`, the nominal flow (3.29) `B' = iB − Ps` holds iff
`d(Λ B/P) = −Λ s`. -/
theorem nominal_flow_iff_Lambda {i s B P Λ : ℝ → ℝ} {dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i τ - dP / P τ) * Λ τ) τ) (hΛ0 : Λ τ ≠ 0) (hP : HasDerivAt P dP τ)
    (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ ↔
      HasDerivAt (fun x => Λ x * (B x / P x)) (-(Λ τ * s τ)) τ := by
  rw [← flow_iff_Lambda (r := fun τ => i τ - dP / P τ) (V := fun x => B x / P x) hΛ hΛ0]
  exact ⟨fun h => hasDerivAt_real_of_nominal h hP hP0,
    fun h => hasDerivAt_nominal_of_real h hP hP0⟩

/-- Cochrane (2023), A1.4, p. 565, ex-post return chain: with `W' = rW` and `W ≠ 0`, the flow
`V' = rV − s` holds iff `d(V/W) = −s/W`. -/
theorem flow_iff_W {W : ℝ → ℝ} {τ : ℝ} (hW : HasDerivAt W (r τ * W τ) τ) (hW0 : W τ ≠ 0) :
    HasDerivAt V (r τ * V τ - s τ) τ ↔ HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ := by
  constructor
  · intro hV
    convert hV.div hW hW0 using 1
    field_simp
    ring
  · intro h
    have hq := h.mul hW
    have hev : V =ᶠ[𝓝 τ] fun x => V x / W x * W x := by
      filter_upwards [hW.continuousAt.eventually_ne hW0] with x hx
      field_simp
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
    ring

/-- Cochrane (2023), A1.4, p. 565, nominal ex-post return chain: with `W' = (i − π)W`,
`π = P'/P`, the nominal flow (3.29) holds iff `d((B/P)/W) = −s/W`. -/
theorem nominal_flow_iff_W {i s B P W : ℝ → ℝ} {dP τ : ℝ}
    (hW : HasDerivAt W ((i τ - dP / P τ) * W τ) τ) (hW0 : W τ ≠ 0) (hP : HasDerivAt P dP τ)
    (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ ↔
      HasDerivAt (fun x => B x / P x / W x) (-(s τ / W τ)) τ := by
  rw [← flow_iff_W (r := fun τ => i τ - dP / P τ) (V := fun x => B x / P x) hW hW0]
  exact ⟨fun h => hasDerivAt_real_of_nominal h hP hP0,
    fun h => hasDerivAt_nominal_of_real h hP hP0⟩

/-! ## The ex-post return `W` (3.32)–(3.33) -/

/-- Cochrane (2023), eq. (3.33), p. 74: the cumulative ex-post real return on government debt,
`W' = (i − π)W` with `π = P'/P`, has the closed form `W(τ)/W(t₀) = exp(∫_{t₀}^τ i)·P(t₀)/P(τ)`
(both paths continuous on `[t₀, ∞)`, so the price level may jump at `t₀`). -/
theorem W_closed_form {i P W dP : ℝ → ℝ} {t₀ : ℝ} (hi : ContinuousOn i (Set.Ici t₀))
    (hPc : ContinuousOn P (Set.Ici t₀)) (hWc : ContinuousOn W (Set.Ici t₀))
    (hP : ∀ τ, t₀ < τ → HasDerivAt P (dP τ) τ)
    (hW : ∀ τ, t₀ < τ → HasDerivAt W ((i τ - dP τ / P τ) * W τ) τ)
    (hP0 : ∀ τ, t₀ ≤ τ → P τ ≠ 0) (hW0 : W t₀ ≠ 0) {τ : ℝ} (hτ : t₀ ≤ τ) :
    W τ / W t₀ = Real.exp (cumRate i t₀ τ) * P t₀ / P τ := by
  have hc : ContinuousOn (fun x => W x * P x * Real.exp (-cumRate i t₀ x)) (Set.Ici t₀) :=
    (hWc.mul hPc).mul (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hi).neg)
  have hd : ∀ x, t₀ < x →
      HasDerivAt (fun x => W x * P x * Real.exp (-cumRate i t₀ x)) 0 x := by
    intro x hx
    have hPx := hP0 x hx.le
    convert ((hW x hx).mul (hP x hx)).mul (hasDerivAt_cumRate hi hx).neg.exp using 1
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [cumRate_self, neg_zero, Real.exp_zero, mul_one] at h
  have hPτ := hP0 τ hτ
  have hE : Real.exp (-cumRate i t₀ τ) * Real.exp (cumRate i t₀ τ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp
  linear_combination (Real.exp (cumRate i t₀ τ)) * h - W τ * P τ * hE

/-- Cochrane (2023), eqs. (3.32)–(3.33): discounting at the ex-post return is discounting at the
real rate: if `W' = rW` on `(t, ∞)` with `W` continuous and nonzero on `[t, ∞)`, then
`W(t)/W(τ) = D(t,τ)`. -/
theorem disc_eq_W_ratio (hr : ContinuousOn r (Set.Ici t)) {W : ℝ → ℝ}
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) {τ : ℝ} (hτ : t ≤ τ) : disc r t τ = W t / W τ := by
  have hc : ContinuousOn (fun x => W x * disc r t x) (Set.Ici t) := hWc.mul (continuousOn_disc hr)
  have hd : ∀ x, t < x → HasDerivAt (fun x => W x * disc r t x) 0 x := by
    intro x hx
    convert (hW x hx).mul (hasDerivAt_disc hr hx) using 1
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [disc_self, mul_one] at h
  have := hW0 τ hτ
  field_simp
  linarith

/-- Cochrane (2023), eq. (3.32), p. 74, and A1.4, p. 565: discounting at the ex-post return `W`
(`W' = rW`, `W ≠ 0`), along the flow identity, `V(t)/W(t) = ∫_t^∞ s(τ)/W(τ)dτ` holds iff
`V(T)/W(T) → 0`. -/
theorem valuation_W_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {W : ℝ → ℝ}
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    V t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔ Tendsto (fun T => V T / W T) atTop (𝓝 0) := by
  have hWt := hW0 t le_rfl
  have hint : ∫ τ in Set.Ioi t, s τ / W τ = pv r s t / W t := by
    rw [pv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    have hWτ := hW0 τ (le_of_lt hτ)
    rw [disc_eq_W_ratio hr hWc hW hW0 (le_of_lt hτ)]
    field_simp
  have hlim : Tendsto (fun T => V T / W T) atTop (𝓝 0) ↔ TVC r V t := by
    have hcongr : (fun T => V T / W T) =ᶠ[atTop] fun T => disc r t T * V T / W t := by
      filter_upwards [eventually_ge_atTop t] with T hT
      have hWT := hW0 T hT
      rw [disc_eq_W_ratio hr hWc hW hW0 hT]
      field_simp
    rw [tendsto_congr' hcongr, TVC]
    constructor
    · intro h
      have h2 := h.mul_const (W t)
      rw [zero_mul] at h2
      refine h2.congr (fun T => ?_)
      field_simp
    · intro h
      have h2 := h.div_const (W t)
      rwa [zero_div] at h2
  rw [hint, hlim, ← valuation_iff_tvc hr hs hV hI]
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), eq. (3.31) with a generic discount factor (box p. 71, eq. (3.31) p. 73):
with `Λ' = −rΛ`, `Λ > 0`, along the flow identity, `V(t) = ∫_t^∞ (Λ(τ)/Λ(t))s(τ)dτ` holds iff
`Λ(T)V(T) → 0`. -/
theorem valuation_Lambda_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {Λ : ℝ → ℝ}
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ t ≠ 0) :
    V t = ∫ τ in Set.Ioi t, Λ τ / Λ t * s τ ↔ Tendsto (fun T => Λ T * V T) atTop (𝓝 0) := by
  have hint : ∫ τ in Set.Ioi t, Λ τ / Λ t * s τ = pv r s t := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    rw [discountFactor_eq hr hΛc hΛ (le_of_lt hτ)]
    field_simp
  have hlim : Tendsto (fun T => Λ T * V T) atTop (𝓝 0) ↔ TVC r V t := by
    have hcongr : (fun T => Λ T * V T) =ᶠ[atTop] fun T => Λ t * (disc r t T * V T) := by
      filter_upwards [eventually_ge_atTop t] with T hT
      rw [discountFactor_eq hr hΛc hΛ hT]
      ring
    rw [tendsto_congr' hcongr, TVC]
    constructor
    · intro h
      have h2 := h.const_mul (Λ t)⁻¹
      rw [mul_zero] at h2
      refine h2.congr (fun T => ?_)
      field_simp
    · intro h
      have h2 := h.const_mul (Λ t)
      rwa [mul_zero] at h2
  rw [hint, hlim, valuation_iff_tvc hr hs hV hI]

/-! ## Constant real rate (p. 74) -/

/-- Cochrane (2023), p. 74: with a constant real rate `c`, the present value is
`∫_t^∞ e^{−c(τ−t)}s(τ)dτ`. -/
theorem pv_const_rate (c : ℝ) (s : ℝ → ℝ) (t : ℝ) :
    pv (fun _ => c) s t = ∫ τ in Set.Ioi t, Real.exp (-(c * (τ - t))) * s τ := by
  simp only [pv, disc_const]

/-- Cochrane (2023), p. 74: with a constant real rate `c > 0` a constant surplus `s₀` is
integrably discounted. -/
theorem pvIntegrable_const {c : ℝ} (hc : 0 < c) (s₀ t : ℝ) :
    PVIntegrable (fun _ => c) (fun _ => s₀) t := by
  have h : IntegrableOn (fun τ => s₀ * Real.exp (c * t) * Real.exp (-c * τ)) (Set.Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  refine h.congr_fun (fun τ _ => ?_) measurableSet_Ioi
  simp only [disc_const]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 74 and A1 (1.17): with a constant real rate `c > 0` and a constant
surplus `s₀`, the present value of surpluses is `s₀/c`. -/
theorem pv_const_const {c : ℝ} (hc : 0 < c) (s₀ t : ℝ) :
    pv (fun _ => c) (fun _ => s₀) t = s₀ / c := by
  have h1 : pv (fun _ => c) (fun _ => s₀) t =
      ∫ τ in Set.Ioi t, s₀ * Real.exp (c * t) * Real.exp (-c * τ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
    simp only [disc_const]
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [h1, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  have hE : Real.exp (c * t) * Real.exp (-(c * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [neg_mul]
  field_simp
  linear_combination s₀ * hE

/-- Cochrane (2023), p. 74: with a constant real rate `c > 0` and constant surplus `s₀`, the
unique solution of the flow identity with the transversality condition is the constant
`V = s₀/c`, so `B(t)/P(t) = s₀/c`. -/
theorem value_const_const {c : ℝ} (hc : 0 < c) {s₀ : ℝ}
    (hV : FlowOn (fun _ => c) (fun _ => s₀) V t) (hT : TVC (fun _ => c) V t) {τ : ℝ}
    (hτ : t ≤ τ) : V τ = s₀ / c := by
  rw [eqOn_pv_of_tvc continuousOn_const continuousOn_const hV hT (pvIntegrable_const hc s₀ t) hτ,
    pv_const_const hc]

end Cochrane.Generality.ContinuousShort

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous time with long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6 (box pp. 71–72) and
§3.6.2, pp. 74–75; Online Appendix A1.2.1 (continuous-time geometric maturity, pp. 559–561) and
A1.5, pp. 565–566.

Deterministic (perfect-foresight) paths. A geometric maturity structure is a bundle of
government bonds paying the nominal coupon flow `e^{−ω(u−t)}` at date `u ≥ t`; `B(t)` is the
number of bundles outstanding (so the debt density due at date `m` is `B(t)e^{−ω(m−t)}`, which is
the book's `ϖe^{−ϖj}B_t` up to the constant `ϖ`). We prove:

* the bundle price `Q(t) = ∫_t^∞ exp(−∫_t^u i)e^{−ω(u−t)}du` solves `Q' = (i + ω)Q − 1`, is the
  unique solution with its transversality condition, is positive, equals `1/(i + ω)` for a
  constant rate, and in the book's normalisation `ωQ → 1` as `ω → ∞` (instantaneous debt, E20);
* the flow (3.34) for the geometric structure reduces to `Q(B' + ωB) = B − Ps`; the market value
  `QB` then obeys the short-debt flow `(QB)' = i·QB − Ps`, and `V = QB/P` obeys (3.38)–(3.39)
  `V' = (R − π)V − s` with `R = (1 + Q' − ωQ)/Q` the ex-post nominal return, `R = i` under the
  bond-pricing equation; the same for an arbitrary finite portfolio of bonds (3.37);
* the valuation equations (3.35)–(3.36) iff the transversality condition, and the price level;
* A1.5: the integrated form of (1.27) with its limit term, (1.28) **with the transversality
  condition as a hypothesis**, and the counterexample showing that (1.27) does not imply the
  vanishing of the limit (E23); `V/W` is nonincreasing when surpluses are nonnegative; the
  stock-price analogue (1.29)–(1.30); `(ΛW)' = 0` and `ΛV = ∫Λs`; jumps leave `V/W` unchanged,
  with `W⁺/W⁻ = V⁺/V⁻` (the printed `dW/W = dP/P` has the wrong sign for short debt);
* A1.2.1: the steady state, the price jump `P(0)/P(0⁻) = (r + ω)/(i + ω)` (1.17)–(1.18) for an
  unexpected permanent rise of the nominal rate, with an explicit post-jump equilibrium path,
  the perpetuity case `r/i` (1.20), the instantaneous-debt limit (no jump), and forward guidance
  `P(0)/P(0⁻) − 1 = e^{−(r+ω)T}((r + ω)/(i + ω) − 1)` with its comparative statics.
-/

namespace Cochrane.Generality.ContinuousLong

open MeasureTheory Filter Topology Cochrane.Generality.ContinuousShort

/-! ## The geometric bond bundle and its price -/

/-- Cochrane (2023), A1.2.1, p. 559–560, and eq. (3.47): the nominal price at `t` of a bundle
paying the coupon flow `e^{−ω(u−t)}` at `u ≥ t`, discounted at the nominal rate `i`:
`Q(t) = ∫_t^∞ exp(−∫_t^u (i + ω))du`. -/
noncomputable def bondPrice (i : ℝ → ℝ) (ω t : ℝ) : ℝ := pv (fun u => i u + ω) (fun _ => 1) t

/-- Cochrane (2023), A1.2.1: the discounted coupons of the bundle are integrable on `(t, ∞)`. -/
def BondIntegrable (i : ℝ → ℝ) (ω t : ℝ) : Prop := PVIntegrable (fun u => i u + ω) (fun _ => 1) t

/-- Cochrane (2023), A1.2.1: `∫_t^u (i + ω) = ∫_t^u i + ω(u − t)`. -/
theorem cumRate_add_const {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) {u : ℝ}
    (hu : t ≤ u) : cumRate (fun x => i x + ω) t u = cumRate i t u + ω * (u - t) := by
  rw [cumRate, intervalIntegral.integral_add (intervalIntegrable_of_ici hi le_rfl hu)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, cumRate]
  ring

/-- Cochrane (2023), A1.2.1, p. 559: the bundle's discount factor is the zero-coupon price
`exp(−∫_t^u i)` times the geometric coupon `e^{−ω(u−t)}`. -/
theorem disc_add_const {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) {u : ℝ}
    (hu : t ≤ u) :
    disc (fun x => i x + ω) t u = disc i t u * Real.exp (-(ω * (u - t))) := by
  rw [disc, disc, cumRate_add_const hi ω hu, ← Real.exp_add, neg_add]

/-- Cochrane (2023), eq. (3.35) and A1.2.1, p. 559: the nominal market value of one bundle is
`∫_t^∞ Q_t^{(u)} e^{−ω(u−t)}du`, zero-coupon prices `Q_t^{(u)} = exp(−∫_t^u i)` weighted by the
geometric maturity structure. -/
theorem bondPrice_eq {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) :
    bondPrice i ω t = ∫ u in Set.Ioi t, disc i t u * Real.exp (-(ω * (u - t))) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [mul_one, disc_add_const hi ω (le_of_lt hu)]

/-- Cochrane (2023), A1.2.1: if `i + ω ≥ c > 0` on `[t, ∞)` the bundle price is a convergent
integral (e.g. any nonnegative nominal rate with `ω > 0`). -/
theorem bondIntegrable_of_ge {i : ℝ → ℝ} {ω c t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hc : 0 < c) (hge : ∀ u, t ≤ u → c ≤ i u + ω) : BondIntegrable i ω t := by
  have hri : ContinuousOn (fun u => i u + ω) (Set.Ici t) := hi.add continuousOn_const
  have hg : IntegrableOn (fun u => Real.exp (c * t) * Real.exp (-c * u)) (Set.Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (((continuousOn_disc hri).mul continuousOn_const).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : t ≤ u := le_of_lt hu
    rw [mul_one, Real.norm_eq_abs, abs_of_pos (disc_pos _ _ _), disc, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h := intervalIntegral.integral_mono_on hu' intervalIntegrable_const
      (intervalIntegrable_of_ici hri le_rfl hu') (fun x hx => hge x hx.1)
    have h' : c * (u - t) ≤ cumRate (fun u => i u + ω) t u := by
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      rw [cumRate]
      linarith
    linarith

/-- Cochrane (2023), eq. (3.47) context and A1.2.1: the bundle price solves the bond-pricing
equation `Q' = (i + ω)Q − 1` on `[t, ∞)` (survey `ct_bond_price_ode`). -/
theorem bondPrice_flow {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) :
    FlowOn (fun u => i u + ω) (fun _ => 1) (bondPrice i ω) t :=
  flowOn_pv (hi.add continuousOn_const) continuousOn_const hQ

/-- Cochrane (2023), A1.2.1: the bundle price satisfies its transversality condition. -/
theorem bondPrice_tvc {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) : TVC (fun u => i u + ω) (bondPrice i ω) t :=
  tvc_pv (hi.add continuousOn_const) continuousOn_const hQ

/-- Cochrane (2023), A1.2.1: the bundle price is the unique solution of `Q' = (i + ω)Q − 1`
satisfying the transversality condition `exp(−∫_t^T (i + ω))Q(T) → 0`. -/
theorem bondPrice_unique {i Q : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) (hF : FlowOn (fun u => i u + ω) (fun _ => 1) Q t)
    (hT : TVC (fun u => i u + ω) Q t) : Set.EqOn Q (bondPrice i ω) (Set.Ici t) :=
  eqOn_pv_of_tvc (hi.add continuousOn_const) continuousOn_const hF hT hQ

/-- Cochrane (2023), eq. (3.47) and A1 (1.17): with a constant nominal rate `i₀`, `i₀ + ω > 0`,
the bundle price is `Q = 1/(i₀ + ω)`. -/
theorem bondPrice_const {i₀ ω : ℝ} (h : 0 < i₀ + ω) (t : ℝ) :
    bondPrice (fun _ => i₀) ω t = 1 / (i₀ + ω) :=
  pv_const_const h 1 t

/-- Cochrane (2023), A1 (1.17): with a constant nominal rate, `i₀ + ω > 0`, the bundle price is a
convergent integral. -/
theorem bondIntegrable_const {i₀ ω : ℝ} (h : 0 < i₀ + ω) (t : ℝ) :
    BondIntegrable (fun _ => i₀) ω t :=
  pvIntegrable_const h 1 t

/-- Cochrane (2023), A1.2.1: the bundle price is positive. -/
theorem bondPrice_pos {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) : 0 < bondPrice i ω t := by
  have hri : ContinuousOn (fun u => i u + ω) (Set.Ici t) := hi.add continuousOn_const
  have hcont : ContinuousOn (fun u => disc (fun u => i u + ω) t u * 1) (Set.Ici t) :=
    (continuousOn_disc hri).mul continuousOn_const
  have h1 : 0 < ∫ u in t..t + 1, disc (fun u => i u + ω) t u * 1 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_of_ici hcont le_rfl (by linarith))
      (fun u _ => by rw [mul_one]; exact disc_pos _ _ _) (by linarith)
  have h2 : 0 ≤ ∫ u in Set.Ioi (t + 1), disc (fun u => i u + ω) t u * 1 :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => by rw [mul_one]; exact (disc_pos _ _ _).le)
  have h3 := intervalIntegral.integral_interval_add_Ioi hQ
    (hQ.mono_set (Set.Ioi_subset_Ioi (by linarith : t ≤ t + 1)))
  rw [bondPrice, pv, ← h3]
  linarith

/-- Cochrane (2023), A1.2.1, p. 560 ("`ϖ = ∞` is instantaneous debt") and E20: in the book's
normalisation (debt density `ϖe^{−ϖj}B`), the value of a bundle per unit of debt due is
`ωQ = ω/(i₀ + ω) → 1` as `ω → ∞`, the value of instantaneous (short-term) debt; the perpetuity
is `ω = 0`, not short-term debt. -/
theorem tendsto_book_bondValue (i₀ : ℝ) :
    Tendsto (fun ω : ℝ => ω * (1 / (i₀ + ω))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ω : ℝ => i₀ + ω) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h : Tendsto (fun ω : ℝ => 1 - i₀ / (i₀ + ω)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop h1)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (-i₀)] with ω hω
  have hω1 : i₀ + ω ≠ 0 := by linarith
  field_simp
  ring

/-! ## The flow (3.34) with a geometric maturity structure, and (3.37)–(3.39) -/

/-- Cochrane (2023), eq. (3.34) and Notation p. xxvi (E31): with geometric maturity structure the
nominal debt due at date `m` held at `t` has density `B(t)e^{−ω(m−t)}`. -/
noncomputable def debtDensity (B : ℝ → ℝ) (ω t m : ℝ) : ℝ := B t * Real.exp (-(ω * (m - t)))

/-- Cochrane (2023), eq. (3.34): the debt due at `t` itself (`m = t`) is `B(t)`, the coupon flow
the government pays at `t`. -/
theorem debtDensity_self (B : ℝ → ℝ) (ω t : ℝ) : debtDensity B ω t t = B t := by
  simp [debtDensity]

/-- Cochrane (2023), eq. (3.34): net sales `dB_t^{(m)}` of debt due at `m`: the time derivative of
the density is `(B' + ωB)e^{−ω(m−t)}` (geometric roll-over, A1 p. 561). -/
theorem hasDerivAt_debtDensity {B : ℝ → ℝ} {dB ω τ : ℝ} (hB : HasDerivAt B dB τ) (m : ℝ) :
    HasDerivAt (fun x => debtDensity B ω x m) ((dB + ω * B τ) * Real.exp (-(ω * (m - τ)))) τ := by
  have h3 : HasDerivAt (fun x => -(ω * (m - x))) ω τ :=
    ((((hasDerivAt_id τ).const_sub m).const_mul ω).neg).congr_deriv (by ring)
  change HasDerivAt (fun x => B x * Real.exp (-(ω * (m - x)))) _ τ
  convert hB.mul h3.exp using 1
  ring

/-- Cochrane (2023), eq. (3.34), p. 74, geometric case: the value of net debt sales
`∫ Q_t^{(m)} dB_t^{(m)} dm` equals `Q(t)(B'(t) + ωB(t))`, so the flow (3.34)
`B_t^{(t)} = P_t s_t + ∫Q dB` is `Q(B' + ωB) = B − Ps`. -/
theorem flow_LT_geometric {i B P s : ℝ → ℝ} {ω τ dB : ℝ} (hi : ContinuousOn i (Set.Ici τ)) :
    (debtDensity B ω τ τ = P τ * s τ +
        ∫ m in Set.Ioi τ, disc i τ m * ((dB + ω * B τ) * Real.exp (-(ω * (m - τ))))) ↔
      bondPrice i ω τ * (dB + ω * B τ) = B τ - P τ * s τ := by
  have h : ∫ m in Set.Ioi τ, disc i τ m * ((dB + ω * B τ) * Real.exp (-(ω * (m - τ)))) =
      bondPrice i ω τ * (dB + ω * B τ) := by
    rw [bondPrice_eq hi ω, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi (fun m _ => ?_)
    ring
  rw [h, debtDensity_self]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), eqs. (3.34) and (3.37)–(3.38): the nominal market value `QB` of a geometric
portfolio obeying the flow `Q(B' + ωB) = B − Ps` grows by the coupon plus capital gain net of
decay, `(QB)' = (1 + Q' − ωQ)B − Ps`, for any differentiable price path `Q`. -/
theorem hasDerivAt_nominal_value {Q B P s : ℝ → ℝ} {ω dQ dB τ : ℝ} (hQ : HasDerivAt Q dQ τ)
    (hB : HasDerivAt B dB τ) (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) :
    HasDerivAt (fun x => Q x * B x) ((1 + dQ - ω * Q τ) * B τ - P τ * s τ) τ := by
  convert hQ.mul hB using 1
  linear_combination (-1 : ℝ) * hflow

/-- Cochrane (2023), eqs. (3.37)–(3.39), pp. 75: for any differentiable bond-price path, the real
market value `V = QB/P` obeys `V' = (R − π)V − s` with the ex-post nominal portfolio return
`R = (1 + Q' − ωQ)/Q` (coupon yield plus capital gain, `dR^n = (dt + dQ)/Q − ω dt`, (3.47)) and
`π = P'/P`: the value grows at its ex-post real return less surpluses. -/
theorem hasDerivAt_value_LT {Q B P s : ℝ → ℝ} {ω dQ dB dP τ : ℝ} (hQ : HasDerivAt Q dQ τ)
    (hB : HasDerivAt B dB τ) (hP : HasDerivAt P dP τ)
    (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) (hQ0 : Q τ ≠ 0) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Q x * B x / P x)
      (((1 + dQ - ω * Q τ) / Q τ - dP / P τ) * (Q τ * B τ / P τ) - s τ) τ := by
  convert (hasDerivAt_nominal_value hQ hB hflow).div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), eq. (3.47): under the bond-pricing equation `Q' = (i + ω)Q − 1` the ex-post
nominal return on the geometric bundle is the short rate, `(1 + Q' − ωQ)/Q = i`. -/
theorem nominalReturn_eq {i₀ ω Q₀ dQ : ℝ} (hQ0 : Q₀ ≠ 0) (hdQ : dQ = (i₀ + ω) * Q₀ - 1) :
    (1 + dQ - ω * Q₀) / Q₀ = i₀ := by
  rw [hdQ]
  field_simp
  ring

/-- Cochrane (2023), eq. (3.39) with the bond-pricing equation: the nominal market value obeys
the short-debt flow (3.29), `(QB)' = i·QB − Ps`. -/
theorem hasDerivAt_nominal_value_priced {i Q B P s : ℝ → ℝ} {ω dB τ : ℝ}
    (hQ : HasDerivAt Q ((i τ + ω) * Q τ - 1) τ) (hB : HasDerivAt B dB τ)
    (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) :
    HasDerivAt (fun x => Q x * B x) (i τ * (Q τ * B τ) - P τ * s τ) τ := by
  convert hasDerivAt_nominal_value hQ hB hflow using 1
  ring

/-- Cochrane (2023), eq. (3.39), p. 75: with nominal debt `B` in geometric bundles priced by
`Q = bondPrice i ω` and obeying the flow (3.34) on `(t, ∞)`, and a positive price level (free to
jump at `t`), the real market value `V = QB/P` solves the flow identity `V' = (i − π)V − s` on
`[t, ∞)` — the same equation as with short-term debt (3.30). -/
theorem flowOn_value_LT {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => bondPrice i ω τ * B τ / P τ) t := by
  have hF := bondPrice_flow hi hQ
  exact flowOn_of_nominal (B := fun τ => bondPrice i ω τ * B τ) (hF.1.mul hBc) hPc hPpos
    (fun τ hτ => hasDerivAt_nominal_value_priced (hF.2 τ hτ) (hB τ hτ) (hflow τ hτ)) hP

/-- Cochrane (2023), eq. (3.35), p. 75: with long-term debt, along the flow identity (3.39), the
valuation equation `QB/P = ∫_t^∞ D(t,τ)s(τ)dτ` holds iff the transversality condition holds
(the real rate is `i − π`). -/
theorem valuation_LT_iff {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ) :
    bondPrice i ω t * B t / P t = pv (fun τ => i τ - dP τ / P τ) s t ↔
      TVC (fun τ => i τ - dP τ / P τ) (fun τ => bondPrice i ω τ * B τ / P τ) t :=
  valuation_iff_tvc hr hs (flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow) hI

/-- Cochrane (2023), eq. (3.35): price-level determination with long-term debt. With the flow
(3.34), the transversality condition, and nonzero debt and present value,
`P(t) = Q(t)B(t)/∫_t^∞ D(t,τ)s(τ)dτ`: the bond price `Q(t)` enters the price level. -/
theorem price_level_LT {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ)
    (hT : TVC (fun τ => i τ - dP τ / P τ) (fun τ => bondPrice i ω τ * B τ / P τ) t)
    (hB0 : B t ≠ 0) (hpv : pv (fun τ => i τ - dP τ / P τ) s t ≠ 0) :
    P t = bondPrice i ω t * B t / pv (fun τ => i τ - dP τ / P τ) s t :=
  (price_level_determined hr hs hI (mul_ne_zero (bondPrice_pos hi hQ).ne' hB0) hpv).1
    ⟨_, flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow, hT, rfl⟩

/-- Cochrane (2023), eq. (3.36), p. 75: with long-term debt, discounting at the cumulative real
return `W` on the government bond portfolio (`W' = (i − π)W`, `W ≠ 0`),
`V(t)/W(t) = ∫_t^∞ s/W` holds iff `V(T)/W(T) → 0`. -/
theorem valuation_LT_W_iff {i s B P dP dB W : ℝ → ℝ} {ω t : ℝ}
    (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ)
    (hWc : ContinuousOn W (Set.Ici t))
    (hW : ∀ τ, t < τ → HasDerivAt W ((i τ - dP τ / P τ) * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    bondPrice i ω t * B t / P t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔
      Tendsto (fun T => bondPrice i ω T * B T / P T / W T) atTop (𝓝 0) :=
  valuation_W_iff hr hs (flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow) hI hWc hW hW0

/-- Cochrane (2023), eqs. (3.37)–(3.38), p. 75, an arbitrary finite portfolio: bonds `k ∈ S` with
prices `Q_k`, quantities `B_k` and nominal coupon flows `c_k`, financed by the flow
`Σ c_k B_k = Ps + Σ Q_k B_k'`. Then the real market value `V = Σ Q_k B_k/P` obeys
`V' = Σ(Q_k' + c_k)B_k/P − πV − s` (value grows by coupons and capital gains less surpluses). -/
theorem hasDerivAt_value_portfolio {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ}
    {dQ dB : ι → ℝ} {P s : ℝ → ℝ} {dP τ : ℝ} (hQ : ∀ k ∈ S, HasDerivAt (Q k) (dQ k) τ)
    (hB : ∀ k ∈ S, HasDerivAt (B k) (dB k) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hflow : ∑ k ∈ S, c k τ * B k τ = P τ * s τ + ∑ k ∈ S, Q k τ * dB k) :
    HasDerivAt (fun x => (∑ k ∈ S, Q k x * B k x) / P x)
      ((∑ k ∈ S, (dQ k + c k τ) * B k τ) / P τ -
        dP / P τ * ((∑ k ∈ S, Q k τ * B k τ) / P τ) - s τ) τ := by
  have hsum : HasDerivAt (fun x => ∑ k ∈ S, Q k x * B k x)
      (∑ k ∈ S, (dQ k * B k τ + Q k τ * dB k)) τ := by
    have := HasDerivAt.fun_sum (u := S) (fun k hk => (hQ k hk).mul (hB k hk))
    exact this
  have hval : ∑ k ∈ S, (dQ k * B k τ + Q k τ * dB k) =
      ∑ k ∈ S, (dQ k + c k τ) * B k τ - P τ * s τ := by
    simp only [add_mul, Finset.sum_add_distrib]
    linarith
  convert hsum.div hP hP0 using 1
  rw [hval]
  field_simp
  ring

/-- Cochrane (2023), eq. (3.37), p. 75: the portfolio's coupon-plus-capital-gain flow is the
value-weighted sum of the individual bond returns `(Q_k' + c_k)/Q_k` with weights
`Q_k B_k`. -/
theorem portfolio_return_weights {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ} {dQ : ι → ℝ}
    {τ : ℝ} (hQ0 : ∀ k ∈ S, Q k τ ≠ 0) :
    ∑ k ∈ S, (dQ k + c k τ) * B k τ =
      ∑ k ∈ S, (dQ k + c k τ) / Q k τ * (Q k τ * B k τ) := by
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have := hQ0 k hk
  field_simp

/-- Cochrane (2023), eq. (3.39), p. 75, finite portfolio priced under perfect foresight: if every
bond satisfies `Q_k' = iQ_k − c_k`, the portfolio's ex-post nominal return is `i` and
`V' = (i − π)V − s`. -/
theorem hasDerivAt_value_portfolio_priced {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ}
    {dB : ι → ℝ} {i P s : ℝ → ℝ} {dP τ : ℝ}
    (hQ : ∀ k ∈ S, HasDerivAt (Q k) (i τ * Q k τ - c k τ) τ)
    (hB : ∀ k ∈ S, HasDerivAt (B k) (dB k) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hflow : ∑ k ∈ S, c k τ * B k τ = P τ * s τ + ∑ k ∈ S, Q k τ * dB k) :
    HasDerivAt (fun x => (∑ k ∈ S, Q k x * B k x) / P x)
      ((i τ - dP / P τ) * ((∑ k ∈ S, Q k τ * B k τ) / P τ) - s τ) τ := by
  convert hasDerivAt_value_portfolio S hQ hB hP hP0 hflow using 1
  have : ∑ k ∈ S, (i τ * Q k τ - c k τ + c k τ) * B k τ = i τ * ∑ k ∈ S, Q k τ * B k τ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [this]
  field_simp

/-! ## A1.5: the ex-post return as discount factor -/

/-- Cochrane (2023), A1.5, (1.27)–(1.28), p. 566 (the "Integrating" line, with its limit term):
if `d(V/W) = −(s/W)dt` on `(t, ∞)` (`V/W` continuous on `[t, ∞)`) and `s/W` is integrable, then
`V(T)/W(T) → V(t)/W(t) − ∫_t^∞ s/W`. -/
theorem A15_integrated {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hsW : ContinuousOn (fun x => s x / W x) (Set.Ici t))
    (hI : IntegrableOn (fun x => s x / W x) (Set.Ioi t)) :
    Tendsto (fun T => V T / W T) atTop (𝓝 (V t / W t - ∫ τ in Set.Ioi t, s τ / W τ)) := by
  have h := (intervalIntegral_tendsto_integral_Ioi t hI tendsto_id).const_sub (V t / W t)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (hG.mono Set.Icc_subset_Ici_self) (fun x hx => hdG x hx.1)
    (intervalIntegrable_of_ici hsW.neg le_rfl hT)
  rw [intervalIntegral.integral_neg] at hF
  simp only [id]
  linarith

/-- Cochrane (2023), A1.5, eq. (1.28), p. 566, corrected (E23): along `d(V/W) = −(s/W)dt`,
`V(t)/W(t) = ∫_t^∞ s/W` holds **iff** the transversality condition `V(T)/W(T) → 0` holds; the
limit is an assumption, not a consequence of (1.27). -/
theorem A15_valuation_iff {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hsW : ContinuousOn (fun x => s x / W x) (Set.Ici t))
    (hI : IntegrableOn (fun x => s x / W x) (Set.Ioi t)) :
    V t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔ Tendsto (fun T => V T / W T) atTop (𝓝 0) := by
  have h := A15_integrated hG hdG hsW hI
  constructor
  · intro he
    rw [he, sub_self] at h
    exact h
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith

/-- Cochrane (2023), A1.5, p. 566, E23: "From (1.27), V grows more slowly than W, so the limit is
zero" is false. Counterexample: `r = 1`, `s ≡ 0`, `W = V = e^τ`. Then `V' = rV − s` (1.27),
`W' = rW`, `d(V/W) = 0 = −s/W`, `s/W` is integrable, yet `V(T)/W(T) → 1 ≠ 0` and
`V(0)/W(0) = 1 ≠ 0 = ∫_0^∞ s/W`. -/
theorem A15_counterexample :
    ∃ r s V W : ℝ → ℝ, FlowOn r s V 0 ∧ (∀ τ, HasDerivAt W (r τ * W τ) τ) ∧ (∀ τ, 0 < W τ) ∧
      (∀ τ, HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ) ∧
      IntegrableOn (fun x => s x / W x) (Set.Ioi 0) ∧
      V 0 / W 0 ≠ ∫ τ in Set.Ioi (0 : ℝ), s τ / W τ ∧
      Tendsto (fun T => V T / W T) atTop (𝓝 1) := by
  refine ⟨fun _ => 1, fun _ => 0, Real.exp, Real.exp, ⟨Real.continuous_exp.continuousOn,
    fun τ _ => ?_⟩, fun τ => ?_, Real.exp_pos, fun τ => ?_, ?_, ?_, ?_⟩
  · convert Real.hasDerivAt_exp τ using 1
    ring
  · convert Real.hasDerivAt_exp τ using 1
    ring
  · have hev : (fun x => Real.exp x / Real.exp x) =ᶠ[𝓝 τ] fun _ => (1 : ℝ) :=
      Eventually.of_forall fun x => div_self (Real.exp_pos x).ne'
    convert (hasDerivAt_const τ (1 : ℝ)).congr_of_eventuallyEq hev using 1
    simp
  · simp only [zero_div]
    exact integrableOn_zero
  · simp
  · refine tendsto_const_nhds.congr (fun T => ?_)
    rw [div_self (Real.exp_pos T).ne']

/-- Cochrane (2023), A1.5, p. 566, E23 in general: for any real rate and surplus stream, every
bubble path `pv + κ·exp(∫_t^· r)` with `κ ≠ 0` solves the flow identity (1.27)/(3.39) but violates
both the transversality condition and the valuation equation (1.28). -/
theorem bubble_not_valuation {r s : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {κ : ℝ} (hκ : κ ≠ 0) :
    FlowOn r s (fun τ => pv r s τ + κ * Real.exp (cumRate r t τ)) t ∧
      ¬ TVC r (fun τ => pv r s τ + κ * Real.exp (cumRate r t τ)) t ∧
      pv r s t + κ * Real.exp (cumRate r t t) ≠ pv r s t := by
  refine ⟨flowOn_bubble hr hs hI κ, fun h => hκ ((tvc_bubble_iff hr hs hI κ).1 h), ?_⟩
  rw [cumRate_self, Real.exp_zero, mul_one]
  intro h
  exact hκ (by linarith)

/-- Cochrane (2023), A1.5, p. 566, the correct content of "V grows more slowly than W": with
nonnegative surpluses and positive `W`, `d(V/W) = −(s/W)dt ≤ 0`, so `V/W` is nonincreasing on
`[t, ∞)` (it need not tend to zero, see `A15_counterexample`). -/
theorem V_over_W_antitone {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hs : ∀ τ, t < τ → 0 ≤ s τ) (hW : ∀ τ, t < τ → 0 < W τ) :
    AntitoneOn (fun x => V x / W x) (Set.Ici t) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici t) hG (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx
    exact (hdG x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hx
    rw [(hdG x hx).deriv]
    have := div_nonneg (hs x hx) (hW x hx).le
    linarith

/-- Cochrane (2023), A1.5, eq. (1.29), p. 566: the ex-post return on a stock with price `p` and
dividend `d`, `dW/W = (d/p)dt + dp/p`, is the statement `p' = Rp − d` with `R = d/p + p'/p`. -/
theorem stock_return_iff {R₀ d₀ p₀ dp : ℝ} (hp : p₀ ≠ 0) :
    dp = R₀ * p₀ - d₀ ↔ R₀ = d₀ / p₀ + dp / p₀ := by
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), A1.5, eq. (1.30), p. 566: a stock price `p` with dividends `d`, growing at
its ex-post return `R` (`p' = Rp − d`), discounted by the cumulative return `W' = RW`:
`p(t)/W(t) = ∫_t^∞ d/W` holds iff `p(T)/W(T) → 0`. -/
theorem stock_price_valuation {R d p W : ℝ → ℝ} {t : ℝ} (hR : ContinuousOn R (Set.Ici t))
    (hd : ContinuousOn d (Set.Ici t)) (hp : FlowOn R d p t) (hI : PVIntegrable R d t)
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (R τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    p t / W t = ∫ τ in Set.Ioi t, d τ / W τ ↔ Tendsto (fun T => p T / W T) atTop (𝓝 0) :=
  valuation_W_iff hR hd hp hI hWc hW hW0

/-- Cochrane (2023), A1.5, p. 566: the basic pricing relation `E_t[d(Λ_tW_t)] = 0`
(deterministic): with `Λ' = −rΛ` and `W' = rW`, `ΛW` is constant on `[t, ∞)`. -/
theorem Lambda_W_const {r Λ W : ℝ → ℝ} {t : ℝ} (hΛc : ContinuousOn Λ (Set.Ici t))
    (hWc : ContinuousOn W (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ) {τ : ℝ} (hτ : t ≤ τ) :
    Λ τ * W τ = Λ t * W t := by
  refine eq_of_hasDerivAt_zero (hΛc.mul hWc) (fun x hx => ?_) hτ
  convert (hΛ x hx).mul (hW x hx) using 1
  ring

/-- Cochrane (2023), A1.5, p. 566 (last lines): with `Λ' = −rΛ`, the flow identity gives
`d(ΛV) = −Λs` and, with the transversality condition `Λ(T)V(T) → 0`,
`Λ(t)V(t) = ∫_t^∞ Λ(τ)s(τ)dτ`. -/
theorem Lambda_valuation {r s V Λ : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hV : FlowOn r s V t) (hI : PVIntegrable r s t)
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ t ≠ 0) (hT : Tendsto (fun T => Λ T * V T) atTop (𝓝 0)) :
    (∀ τ, t < τ → HasDerivAt (fun x => Λ x * V x) (-(Λ τ * s τ)) τ) ∧
      Λ t * V t = ∫ τ in Set.Ioi t, Λ τ * s τ := by
  refine ⟨fun τ hτ => (flow_iff_Lambda (hΛ τ hτ) ?_).1 (hV.2 τ hτ), ?_⟩
  · rw [discountFactor_eq hr hΛc hΛ hτ.le]
    exact mul_ne_zero hΛ0 (disc_pos r t τ).ne'
  · rw [(valuation_Lambda_iff hr hs hV hI hΛc hΛ hΛ0).2 hT, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
    field_simp

/-- Cochrane (2023), A1.5, p. 566 ("At the jump points d(V_t/W_t) = 0"): with nominal debt `B`
predetermined across a jump of the bond price `Q⁻ → Q⁺` and of the price level `P⁻ → P⁺`, the
cumulative return jumps by the real bond return `(Q⁺/P⁺)/(Q⁻/P⁻)`; then `V/W` does not jump, and
`W⁺/W⁻ = V⁺/V⁻` (the jump of `W` equals that of `V`). -/
theorem jump_V_over_W {Qm Qp Pm Pp B Wm : ℝ} (hQm : Qm ≠ 0) (hQp : Qp ≠ 0) (hPm : Pm ≠ 0)
    (hPp : Pp ≠ 0) (hWm : Wm ≠ 0) (hB : B ≠ 0) :
    Qp * B / Pp / (Wm * (Qp / Pp / (Qm / Pm))) = Qm * B / Pm / Wm ∧
      Wm * (Qp / Pp / (Qm / Pm)) / Wm = Qp * B / Pp / (Qm * B / Pm) := by
  constructor <;> field_simp

/-- Cochrane (2023), A1.5, p. 566, imprecision: the printed jump relation `dW/W = dP/P` has the
wrong sign. With short-term debt (`Q = 1`) the return jumps by `W⁺/W⁻ = P⁻/P⁺`, so for any
genuine jump `P⁺ ≠ P⁻` the proportional jumps of `W` and of `P` have opposite signs. -/
theorem jump_short_return_sign {Pm Pp : ℝ} (hPm : 0 < Pm) (hPp : 0 < Pp) (hne : Pm ≠ Pp) :
    (Pm / Pp - 1) * (Pp / Pm - 1) < 0 := by
  have h : (Pm / Pp - 1) * (Pp / Pm - 1) = -((Pm - Pp) ^ 2 / (Pm * Pp)) := by
    field_simp
    ring
  rw [h, neg_neg_iff_pos]
  have hsub : Pm - Pp ≠ 0 := sub_ne_zero.2 hne
  exact div_pos (by positivity) (mul_pos hPm hPp)

/-! ## A1.2.1 (continuous time): steady state and price-level jumps -/

/-- Cochrane (2023), A1.2.1, pp. 559–561: the steady state with a constant real rate `r > 0`, zero
inflation (`i = r`), constant surplus `s₀` and price level `P̄ ≠ 0`. With `Q̄ = 1/(r + ω)` (which
solves `Q' = (r + ω)Q − 1` with `Q' = 0`), a constant debt level `B̄` obeys the flow
`Q̄(0 + ωB̄) = B̄ − P̄s₀` iff `B̄ = s₀(r + ω)P̄/r`; it then satisfies the valuation
`Q̄B̄/P̄ = s₀/r = ∫_t^∞ e^{−r(τ−t)}s₀dτ`, and the government sells `ωB̄` new bundles per unit time
(the roll-over of A1 p. 561). -/
theorem steady_state_LT {r ω s₀ Pbar Bbar : ℝ} (hr : 0 < r) (hrω : 0 < r + ω) (hP : Pbar ≠ 0)
    (t : ℝ) :
    (0 = (r + ω) * (1 / (r + ω)) - 1) ∧
      (1 / (r + ω) * (0 + ω * Bbar) = Bbar - Pbar * s₀ ↔ Bbar = s₀ * (r + ω) * Pbar / r) ∧
      (Bbar = s₀ * (r + ω) * Pbar / r →
        bondPrice (fun _ => r) ω t * Bbar / Pbar = pv (fun _ => r) (fun _ => s₀) t) := by
  refine ⟨by field_simp; ring, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · field_simp at h
    field_simp
    linarith
  · rw [h]
    field_simp
    ring
  · rw [bondPrice_const hrω, pv_const_const hr, h]
    field_simp

/-- Cochrane (2023), A1.2.1, eqs. (1.17)–(1.18): the price-level jump from the valuation
equation. If nominal debt `B ≠ 0` is predetermined and the real value of surpluses `v ≠ 0` is the
same before and after the news, `Q⁻B/P⁻ = v = Q₀B/P₀`, then `P₀/P⁻ = Q₀/Q⁻`. -/
theorem price_jump_of_valuation {Qm Q0 B Pm P0 v : ℝ} (hv : v ≠ 0) (hB : B ≠ 0) (hQm : Qm ≠ 0)
    (hPm : Pm ≠ 0) (hpre : Qm * B / Pm = v) (hpost : Q0 * B / P0 = v) : P0 / Pm = Q0 / Qm := by
  have hP0 : P0 ≠ 0 := by
    rintro rfl
    rw [div_zero] at hpost
    exact hv hpost.symm
  rw [← hpost] at hpre
  field_simp at hpre ⊢
  linear_combination hpre

/-- Cochrane (2023), A1.2.1, eq. (1.18), p. 560: an unexpected permanent rise of the nominal rate
from `r` to `i` at date 0, with a constant real rate `r > 0` (so inflation `i − r`) and constant
surplus `s₀ ≠ 0`. Before: the steady state, valuation `Q⁻B/P⁻ = s₀/r` with `Q⁻ = 1/(r + ω)`.
After: any path `V` solving the flow identity with the transversality condition and
`V(0) = Q(0)B/P(0)`, `Q(0) = 1/(i + ω)` the new bundle price. Then `P(0)/P(0⁻) = (r+ω)/(i+ω)`. -/
theorem price_jump_permanent {r i ω s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r)
    (hrω : 0 < r + ω) (hiω : 0 < i + ω) (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) ω 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hT : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fun _ => i) ω 0 * B / P0) :
    P0 / Pm = (r + ω) / (i + ω) := by
  have hv := value_const_const hr hV hT (le_refl 0)
  rw [pv_const_const hr, bondPrice_const hrω] at hpre
  rw [bondPrice_const hiω] at hV0
  rw [price_jump_of_valuation (div_ne_zero hs hr.ne') hB (by positivity) hPm hpre
    (hV0 ▸ hv)]
  field_simp

/-- Cochrane (2023), A1.2.1, eq. (1.18): the post-jump equilibrium exists. With `P̄ > 0`, let
`P(τ) = P̄((r+ω)/(i+ω))e^{(i−r)τ}` (inflation `i − r`) and `B(τ) = s₀(i + ω)P(τ)/r`. Then `B(0)` is
the predetermined steady-state debt `s₀(r+ω)P̄/r`, the geometric flow (3.34) holds with the bundle
price `Q = 1/(i + ω)`, and `V = QB/P` solves the flow identity with real rate `r` and satisfies
the transversality condition. -/
theorem post_jump_equilibrium {r i ω s₀ Pbar : ℝ} (hr : 0 < r) (hiω : 0 < i + ω)
    (hrω : 0 < r + ω) (hP : 0 < Pbar) :
    (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * 0)) / r =
        s₀ * (r + ω) * Pbar / r) ∧
      (∀ τ, HasDerivAt (fun x => Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * x))
        ((i - r) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) τ) ∧
      (∀ τ, bondPrice (fun _ => i) ω τ *
          ((i - r) * (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) +
            ω * (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r)) =
        s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r -
          Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ) * s₀) ∧
      FlowOn (fun _ => r) (fun _ => s₀) (fun τ => bondPrice (fun _ => i) ω τ *
        (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
          (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 ∧
      TVC (fun _ => r) (fun τ => bondPrice (fun _ => i) ω τ *
        (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
          (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 := by
  have hV : ∀ τ, bondPrice (fun _ => i) ω τ *
      (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
        (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) = s₀ / r := by
    intro τ
    rw [bondPrice_const hiω]
    have := Real.exp_pos ((i - r) * τ)
    field_simp
  have hF : FlowOn (fun _ => r) (fun _ => s₀) (fun τ => bondPrice (fun _ => i) ω τ *
      (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
        (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 := by
    simp only [hV]
    refine ⟨continuousOn_const, fun τ _ => ?_⟩
    convert hasDerivAt_const τ (s₀ / r) using 1
    field_simp
    ring
  refine ⟨?_, fun τ => ?_, fun τ => ?_, hF, ?_⟩
  · rw [mul_zero, Real.exp_zero]
    field_simp
  · have h := (((hasDerivAt_id τ).const_mul (i - r)).exp).const_mul (Pbar * ((r + ω) / (i + ω)))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  · rw [bondPrice_const hiω]
    field_simp
    ring
  · refine (valuation_iff_tvc continuousOn_const continuousOn_const hF
      (pvIntegrable_const hr s₀ 0)).1 ?_
    rw [hV, pv_const_const hr]

/-- Cochrane (2023), A1.2.1, eq. (1.20), p. 560: for a perpetuity (`ω = 0`) the permanent rate
rise gives `P(0) = (r/i)P(0⁻)`. -/
theorem price_jump_perpetuity {r i s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r) (hi : 0 < i)
    (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) 0 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hT : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fun _ => i) 0 0 * B / P0) : P0 = r / i * Pm := by
  have h := price_jump_permanent hr (by linarith) (by linarith) hs hB hPm hpre hV hT hV0
  rw [add_zero, add_zero] at h
  field_simp at h ⊢
  linarith

/-- Cochrane (2023), A1.2.1, p. 560: "a rise in interest rates from `r = 3%` to `i = 4%`
occasions a 25% price level drop" for a perpetuity: `r/i = 3/4`. -/
theorem price_jump_perpetuity_numeric : ((0.03 : ℝ) + 0) / ((0.04 : ℝ) + 0) = 3 / 4 := by
  norm_num

/-- Cochrane (2023), A1.2.1, p. 560 and E20: for instantaneous (short-term) debt, `ω → ∞`, the
jump ratio `(r + ω)/(i + ω) → 1`: no price-level jump ("`ϖ = ∞` … `P₀ = P` and there is no
downward jump"). -/
theorem price_jump_tendsto_one (r i : ℝ) :
    Tendsto (fun ω : ℝ => (r + ω) / (i + ω)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ω : ℝ => i + ω) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h : Tendsto (fun ω : ℝ => 1 - (i - r) / (i + ω)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop h1)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (-i)] with ω hω
  have hω1 : i + ω ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), A1.2.1, p. 560 ("The price level P₀ jumps down as the interest-rate rises"):
for `r < i` and `r + ω > 0` the jump ratio lies in `(0, 1)`. -/
theorem price_jump_lt_one {r i ω : ℝ} (hri : r < i) (hrω : 0 < r + ω) :
    0 < (r + ω) / (i + ω) ∧ (r + ω) / (i + ω) < 1 := by
  have hiω : 0 < i + ω := by linarith
  refine ⟨div_pos hrω hiω, (div_lt_one hiω).2 (by linarith)⟩

/-- Cochrane (2023), A1.2.1, p. 560 ("governments maintain much shorter maturity structures …
reducing the size of the effect"): for `r ≤ i` the ratio `(r+ω)/(i+ω)` is nondecreasing in `ω`,
so shorter maturity (larger `ω`) means a smaller downward jump. -/
theorem price_jump_mono {r i ω₁ ω₂ : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω₁) (hω : ω₁ ≤ ω₂) :
    (r + ω₁) / (i + ω₁) ≤ (r + ω₂) / (i + ω₂) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### Forward guidance (A1 p. 561) -/

/-- Cochrane (2023), A1.2.1, p. 561: the forward-guidance path of the nominal rate, `r` until
`T` and `i` after (announced at date 0). -/
noncomputable def fgRate (r i T u : ℝ) : ℝ := if u ≤ T then r else i

/-- Cochrane (2023), A1.2.1, p. 561: the cumulated bundle rate under forward guidance up to
`u ∈ [0, T]` is `(r + ω)u`. -/
theorem cumRate_fg_le {r i T ω u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    cumRate (fun x => fgRate r i T x + ω) 0 u = (r + ω) * u := by
  rw [cumRate, intervalIntegral.integral_congr (g := fun _ => r + ω) (fun x hx => ?_),
    intervalIntegral.integral_const, smul_eq_mul]
  · ring
  · rw [Set.uIcc_of_le hu] at hx
    simp only [fgRate, hx.2.trans huT, ↓reduceIte]

/-- Cochrane (2023), A1.2.1, p. 561: the cumulated bundle rate under forward guidance up to
`u ≥ T ≥ 0` is `(r + ω)T + (i + ω)(u − T)`. -/
theorem cumRate_fg_ge {r i T ω u : ℝ} (hT : 0 ≤ T) (hTu : T ≤ u) :
    cumRate (fun x => fgRate r i T x + ω) 0 u = (r + ω) * T + (i + ω) * (u - T) := by
  have h1 : IntervalIntegrable (fun x => fgRate r i T x + ω) volume 0 T := by
    refine (intervalIntegrable_const (c := r + ω)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    simp only [fgRate, hx.2, ↓reduceIte]
  have h2 : IntervalIntegrable (fun x => fgRate r i T x + ω) volume T u := by
    refine (intervalIntegrable_const (c := i + ω)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hTu] at hx
    simp only [fgRate, not_le.2 hx.1, ↓reduceIte]
  have e2 : ∫ x in T..u, fgRate r i T x + ω = ∫ _ in T..u, i + ω := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hTu] at hx
    simp only [fgRate, not_le.2 hx.1, ↓reduceIte]
  rw [cumRate, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, e2,
    intervalIntegral.integral_const, smul_eq_mul]
  have e1 := cumRate_fg_le (r := r) (i := i) (ω := ω) hT le_rfl
  rw [cumRate] at e1
  rw [e1]
  ring

/-- Cochrane (2023), A1.2.1, p. 561: the bundle price at date 0 under forward guidance,
`Q(0) = (1 − e^{−(r+ω)T})/(r + ω) + e^{−(r+ω)T}/(i + ω)` (the bracket of the book's continuous
forward-guidance valuation equation). -/
theorem bondPrice_fg {r i T ω : ℝ} (hT : 0 ≤ T) (hrω : 0 < r + ω) (hiω : 0 < i + ω) :
    bondPrice (fgRate r i T) ω 0 =
      (1 - Real.exp (-(r + ω) * T)) / (r + ω) + Real.exp (-(r + ω) * T) / (i + ω) := by
  set f : ℝ → ℝ := fun u => disc (fun x => fgRate r i T x + ω) 0 u * 1 with hf
  have hleft : ∀ u, 0 ≤ u → u ≤ T → f u = Real.exp (-(r + ω) * u) := by
    intro u hu huT
    simp only [hf, mul_one, disc, cumRate_fg_le hu huT]
    ring_nf
  have hright : ∀ u, T ≤ u →
      f u = Real.exp ((i - r) * T) * Real.exp (-(i + ω) * u) := by
    intro u hu
    simp only [hf, mul_one, disc, cumRate_fg_ge hT hu, ← Real.exp_add]
    ring_nf
  have hR : IntegrableOn f (Set.Ioi T) := by
    exact IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (a := -(i + ω)) (by linarith) T).const_mul
        (Real.exp ((i - r) * T))) (fun u hu => (hright u (le_of_lt hu)).symm) measurableSet_Ioi
  have hL : IntervalIntegrable f volume 0 T := by
    refine ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(r + ω) * u)).intervalIntegrable
      0 T).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    exact (hleft x hx.1.le hx.2).symm
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hL hR
  have eL : ∫ u in (0 : ℝ)..T, f u = (1 - Real.exp (-(r + ω) * T)) / (r + ω) := by
    rw [intervalIntegral.integral_congr (g := fun u => Real.exp (-(r + ω) * u)) (fun x hx => ?_)]
    · rw [← intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_mul_Ioi (by linarith) 0) hT,
        integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith), mul_zero,
        Real.exp_zero]
      field_simp
    · rw [Set.uIcc_of_le hT] at hx
      exact hleft x hx.1 hx.2
  have eR : ∫ u in Set.Ioi T, f u = Real.exp (-(r + ω) * T) / (i + ω) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hright u (le_of_lt hu)),
      integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    have hE : Real.exp ((i - r) * T) * Real.exp (-(i + ω) * T) = Real.exp (-(r + ω) * T) := by
      rw [← Real.exp_add]
      ring_nf
    rw [← hE]
    field_simp
  rw [bondPrice, pv, ← hsplit, eL, eR]

/-- Cochrane (2023), A1.2.1, p. 561: forward guidance. The nominal rate is announced at date 0 to
rise from `r` to `i` at `T ≥ 0`, with a constant real rate `r > 0`, constant surplus `s₀ ≠ 0`,
and the pre-announcement steady state `Q⁻B/P⁻ = s₀/r`, `Q⁻ = 1/(r + ω)`. For any post-news path
solving the flow identity with the transversality condition and `V(0) = Q(0)B/P(0)`, `Q(0)` the
forward-guidance bundle price:
`P(0)/P(0⁻) − 1 = e^{−(r+ω)T}((r + ω)/(i + ω) − 1)`. -/
theorem price_jump_fg {r i T ω s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hrω : 0 < r + ω) (hiω : 0 < i + ω) (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) ω 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hTv : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fgRate r i T) ω 0 * B / P0) :
    P0 / Pm - 1 = Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1) := by
  have hv := value_const_const hr hV hTv (le_refl 0)
  rw [pv_const_const hr, bondPrice_const hrω] at hpre
  rw [price_jump_of_valuation (div_ne_zero hs hr.ne') hB (by positivity) hPm hpre (hV0 ▸ hv),
    bondPrice_fg hT hrω hiω]
  field_simp
  ring

/-- Cochrane (2023), A1.2.1, p. 561: with `T = 0` the forward-guidance formula is the immediate
permanent rise (1.18). -/
theorem fg_jump_at_zero (r i ω : ℝ) :
    Real.exp (-(r + ω) * 0) * ((r + ω) / (i + ω) - 1) = (r + ω) / (i + ω) - 1 := by
  simp

/-- Cochrane (2023), A1.2.1, p. 561 ("As T → ∞, the downward price-level jump goes to zero"). -/
theorem fg_jump_tendsto_zero {r i ω : ℝ} (hrω : 0 < r + ω) :
    Tendsto (fun T => Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun T => Real.exp (-(r + ω) * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  simpa using h.mul_const ((r + ω) / (i + ω) - 1)

/-- Cochrane (2023), A1.2.1, p. 561 ("forward guidance works"): for `r < i` the price level still
jumps down at date 0, by `e^{−(r+ω)T}(i − r)/(i + ω) > 0`. -/
theorem fg_jump_neg {r i ω T : ℝ} (hri : r < i) (hrω : 0 < r + ω) :
    Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1) =
        -(Real.exp (-(r + ω) * T) * ((i - r) / (i + ω))) ∧
      0 < Real.exp (-(r + ω) * T) * ((i - r) / (i + ω)) := by
  have hiω : 0 < i + ω := by linarith
  refine ⟨by field_simp; ring, mul_pos (Real.exp_pos _) (div_pos (by linarith) hiω)⟩

/-- Cochrane (2023), A1.2.1, p. 561 ("Longer T … give a smaller price-level jump"): the size of
the jump `e^{−(r+ω)T}(i − r)/(i + ω)` is nonincreasing in the announcement horizon `T`. -/
theorem fg_jump_antitone_T {r i ω T₁ T₂ : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω) (hT : T₁ ≤ T₂) :
    Real.exp (-(r + ω) * T₂) * ((i - r) / (i + ω)) ≤
      Real.exp (-(r + ω) * T₁) * ((i - r) / (i + ω)) := by
  have hiω : 0 < i + ω := by linarith
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith))
    (div_nonneg (by linarith) hiω.le)

/-- Cochrane (2023), A1.2.1, p. 561 ("shorter maturity structures — lower ω or larger ϖ — give a
smaller price-level jump"): for `T ≥ 0` the size of the jump is nonincreasing in `ω`. -/
theorem fg_jump_antitone_ω {r i ω₁ ω₂ T : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω₁) (hω : ω₁ ≤ ω₂)
    (hT : 0 ≤ T) :
    Real.exp (-(r + ω₂) * T) * ((i - r) / (i + ω₂)) ≤
      Real.exp (-(r + ω₁) * T) * ((i - r) / (i + ω₁)) := by
  have hiω : 0 < i + ω₁ := by linarith
  refine mul_le_mul (Real.exp_le_exp.2 (by nlinarith))
    (div_le_div_of_nonneg_left (by linarith) hiω (by linarith))
    (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le

/-! ## (3.34)–(3.39) for an arbitrary continuum of maturities

The book's general maturity structure: at date `x` the government owes the nominal density
`b(x, m)` of zero-coupon debt due at date `m` (the book's `B_x^{(m)}`), priced at `q(x, m)` (the
book's `Q_x^{(m)}`), and the market value is `∫_0^∞ q(x, x+j)b(x, x+j)dj`. The book differentiates
this integral without stating any regularity. We state it explicitly (`MaturityRegularAt`):
joint differentiability of `q` and `b` in `(date, maturity)` with partials `(qt, qm)`, `(bt, bm)`;
integrability of the value, of new issues and of the maturity-direction derivative; decay of
the value density at long maturities; and a locally uniform integrable bound on the date
derivative (the hypotheses of Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
`bt(x, m)` is the book's `dB_x^{(m)}/dx` (sales of the bond due at `m`), `qt/q` its return. -/

/-- Cochrane (2023), §3.6.2, p. 75: the linear map `(u, v) ↦ a·u + c·v`, the derivative of a
function of `(date, maturity)` with partial derivatives `a` and `c`. -/
noncomputable def partialsCLM (a c : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + c • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), §3.6.2: `partialsCLM a c (u, v) = a·u + c·v`. -/
theorem partialsCLM_apply (a c u v : ℝ) : partialsCLM a c (u, v) = a * u + c * v := by
  simp [partialsCLM]

/-- Cochrane (2023), §3.6.2: along a fixed time to maturity `j`, `d/dx f(x, x+j) = f_t + f_m`. -/
theorem hasDerivAt_diag {f ft fm : ℝ → ℝ → ℝ} {x j : ℝ}
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) (partialsCLM (ft x (x + j)) (fm x (x + j)))
      (x, x + j)) :
    HasDerivAt (fun y => f y (y + j)) (ft x (x + j) + fm x (x + j)) x := by
  have hl : HasDerivAt (fun y : ℝ => (y, y + j)) ((1 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_id' x).prodMk ((hasDerivAt_id' x).add_const j)
  have := h.comp_hasDerivAt x hl
  rw [partialsCLM_apply] at this
  simpa [Function.comp_def] using this

/-- Cochrane (2023), §3.6.2: at a fixed date `x`, `d/dj f(x, x+j) = f_m`. -/
theorem hasDerivAt_maturity {f ft fm : ℝ → ℝ → ℝ} {x j : ℝ}
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) (partialsCLM (ft x (x + j)) (fm x (x + j)))
      (x, x + j)) :
    HasDerivAt (fun k => f x (x + k)) (fm x (x + j)) j := by
  have hl : HasDerivAt (fun k : ℝ => (x, x + k)) ((0 : ℝ), (1 : ℝ)) j :=
    (hasDerivAt_const j x).prodMk ((hasDerivAt_id' j).const_add x)
  have := h.comp_hasDerivAt j hl
  rw [partialsCLM_apply] at this
  simpa [Function.comp_def] using this

/-- Cochrane (2023), eq. (3.35), p. 74–75: the nominal market value of the debt,
`∫_0^∞ Q_x^{(x+j)}B_x^{(x+j)}dj`. -/
noncomputable def mktValue (q b : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, q x (x + j) * b x (x + j)

/-- Cochrane (2023), eq. (3.34), p. 74: the value of net debt sales `∫_0^∞ Q dB dj`. -/
noncomputable def issuanceValue (q bt : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, q x (x + j) * bt x (x + j)

/-- Cochrane (2023), eq. (3.37), p. 75: the nominal capital gain on the portfolio,
`∫_0^∞ (dQ_x^{(x+j)}/dx)B_x^{(x+j)}dj`. -/
noncomputable def capitalGain (qt b : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, qt x (x + j) * b x (x + j)

/-- Cochrane (2023), eq. (3.37), p. 75: the value-weighted nominal return on the portfolio. -/
noncomputable def valueWeightedReturn (q b qt : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  capitalGain qt b x / mktValue q b x

/-- Cochrane (2023), §3.6.2, regularity left implicit by the book: the conditions at date `τ`
under which the market value `∫_0^∞ q b dj` may be differentiated under the integral sign —
joint differentiability on a neighbourhood `s` of `τ`, integrability of the value, of new issues
and of the maturity derivative, decay at long maturities, measurability of the capital gain and
an integrable bound on the date derivative uniformly over `s`. -/
def MaturityRegularAt (q b qt qm bt bm : ℝ → ℝ → ℝ) (τ : ℝ) : Prop :=
  ∃ s ∈ 𝓝 τ, ∃ bound : ℝ → ℝ,
    (∀ x ∈ s, ∀ j, 0 ≤ j → HasFDerivAt (fun p : ℝ × ℝ => q p.1 p.2)
      (partialsCLM (qt x (x + j)) (qm x (x + j))) (x, x + j)) ∧
    (∀ x ∈ s, ∀ j, 0 ≤ j → HasFDerivAt (fun p : ℝ × ℝ => b p.1 p.2)
      (partialsCLM (bt x (x + j)) (bm x (x + j))) (x, x + j)) ∧
    IntegrableOn (fun j => q τ (τ + j) * b τ (τ + j)) (Set.Ioi 0) ∧
    IntegrableOn (fun j => q τ (τ + j) * bt τ (τ + j)) (Set.Ioi 0) ∧
    AEStronglyMeasurable (fun j => qt τ (τ + j) * b τ (τ + j)) (volume.restrict (Set.Ioi 0)) ∧
    IntegrableOn (fun j => qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j))
      (Set.Ioi 0) ∧
    Tendsto (fun j => q τ (τ + j) * b τ (τ + j)) atTop (𝓝 0) ∧
    IntegrableOn bound (Set.Ioi 0) ∧
    ∀ j, 0 < j → ∀ x ∈ s, ‖(qt x (x + j) + qm x (x + j)) * b x (x + j) +
      q x (x + j) * (bt x (x + j) + bm x (x + j))‖ ≤ bound j

/-- Cochrane (2023), eqs. (3.37)–(3.38), p. 75, general maturity structure: under
`MaturityRegularAt`, the market value is differentiable with
`d/dx ∫q b = ∫(∂_x q)b + ∫q ∂_x b − q(τ,τ)b(τ,τ)`: capital gains plus net sales minus the debt
maturing now. -/
theorem hasDerivAt_mktValue {q b qt qm bt bm : ℝ → ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) :
    HasDerivAt (mktValue q b)
      (capitalGain qt b τ + issuanceValue q bt τ - q τ τ * b τ τ) τ := by
  obtain ⟨s, hs, bound, hq, hb, hI, hIss, hCGm, hM, hlim, hbI, hbd⟩ := h
  have hτs : τ ∈ s := mem_of_mem_nhds hs
  have hG : ∀ x ∈ s, ∀ j, 0 ≤ j → HasDerivAt (fun y => q y (y + j) * b y (y + j))
      ((qt x (x + j) + qm x (x + j)) * b x (x + j) +
        q x (x + j) * (bt x (x + j) + bm x (x + j))) x :=
    fun x hx j hj => (hasDerivAt_diag (hq x hx j hj)).mul (hasDerivAt_diag (hb x hx j hj))
  have hGm : ∀ x ∈ s, ∀ j, 0 ≤ j → HasDerivAt (fun k => q x (x + k) * b x (x + k))
      (qm x (x + j) * b x (x + j) + q x (x + j) * bm x (x + j)) j :=
    fun x hx j hj => (hasDerivAt_maturity (hq x hx j hj)).mul (hasDerivAt_maturity (hb x hx j hj))
  have hcont : ∀ x ∈ s, ContinuousOn (fun j => q x (x + j) * b x (x + j)) (Set.Ici 0) :=
    fun x hx j hj => (hGm x hx j hj).continuousAt.continuousWithinAt
  have hmeas : ∀ᶠ x in 𝓝 τ, AEStronglyMeasurable (fun j => q x (x + j) * b x (x + j))
      (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [hs] with x hx
    exact ((hcont x hx).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hsplit : (fun j => (qt τ (τ + j) + qm τ (τ + j)) * b τ (τ + j) +
      q τ (τ + j) * (bt τ (τ + j) + bm τ (τ + j))) = fun j =>
      (qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j)) +
        (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j)) := by
    funext j
    ring
  have hF'meas : AEStronglyMeasurable (fun j => (qt τ (τ + j) + qm τ (τ + j)) * b τ (τ + j) +
      q τ (τ + j) * (bt τ (τ + j) + bm τ (τ + j))) (volume.restrict (Set.Ioi 0)) := by
    rw [hsplit]
    exact (hCGm.add hIss.aestronglyMeasurable).add hM.aestronglyMeasurable
  obtain ⟨hTint, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := fun x j => q x (x + j) * b x (x + j))
    (F' := fun x j => (qt x (x + j) + qm x (x + j)) * b x (x + j) +
      q x (x + j) * (bt x (x + j) + bm x (x + j))) (bound := bound) hs hmeas hI hF'meas
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun j hj x hx => hbd j hj x hx))
    hbI ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun j hj x hx => hG x hx j (le_of_lt hj)))
  have hTint' : IntegrableOn (fun j => (qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j)) +
      (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j))) (Set.Ioi 0) := by
    rw [← hsplit]
    exact hTint
  have hA : IntegrableOn (fun j => qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j))
      (Set.Ioi 0) := by
    have := hTint'.sub hM
    refine this.congr_fun (fun j _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hCG : IntegrableOn (fun j => qt τ (τ + j) * b τ (τ + j)) (Set.Ioi 0) := by
    have := hA.sub hIss
    refine this.congr_fun (fun j _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hMval : ∫ j in Set.Ioi 0, (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j)) =
      0 - q τ (τ + 0) * b τ (τ + 0) :=
    integral_Ioi_of_hasDerivAt_of_tendsto (hcont τ hτs 0 (Set.mem_Ici.2 le_rfl))
      (fun j hj => hGm τ hτs j (le_of_lt hj)) hM hlim
  refine hD.congr_deriv ?_
  rw [hsplit, integral_add hA hM, integral_add hCG hIss, hMval, add_zero]
  unfold capitalGain issuanceValue
  ring

/-- Cochrane (2023), eqs. (3.34) and (3.38), p. 75, general maturity structure: if the maturing
bond is worth its face value, `q(τ,τ) = 1`, and the flow (3.34)
`B_τ^{(τ)} = P_τ s_τ + ∫Q dB dj` holds, then `d/dx ∫q b = ∫(∂_x q)b − P s`. -/
theorem hasDerivAt_mktValue_flow {q b qt qm bt bm : ℝ → ℝ → ℝ} {P s : ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) :
    HasDerivAt (mktValue q b) (capitalGain qt b τ - P τ * s τ) τ := by
  refine (hasDerivAt_mktValue h).congr_deriv ?_
  rw [hmat, hflow]
  ring

/-- Cochrane (2023), eq. (3.37), p. 75: the value-weighted return is the average of the
individual bond returns `(∂_x Q^{(m)})/Q^{(m)}` with weights `Q^{(m)}B^{(m)}/∫QB`. -/
theorem valueWeightedReturn_eq {q b qt : ℝ → ℝ → ℝ} {τ : ℝ}
    (hq0 : ∀ j, 0 < j → q τ (τ + j) ≠ 0) :
    valueWeightedReturn q b qt τ = ∫ j in Set.Ioi 0,
      qt τ (τ + j) / q τ (τ + j) * (q τ (τ + j) * b τ (τ + j) / mktValue q b τ) := by
  rw [valueWeightedReturn, capitalGain, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi (fun j hj => ?_)
  have := hq0 j hj
  field_simp

/-- Cochrane (2023), eq. (3.39), p. 75, general maturity structure: the real value
`V = ∫QB dj/P` obeys `dV = −s dt + V dR` with `dR = R − π`, `R` the value-weighted nominal
return (3.37) and `π = P'/P`. -/
theorem hasDerivAt_value_general {q b qt qm bt bm : ℝ → ℝ → ℝ} {P s : ℝ → ℝ} {τ dP : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) (hP : HasDerivAt P dP τ)
    (hA : mktValue q b τ ≠ 0) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => mktValue q b x / P x)
      ((valueWeightedReturn q b qt τ - dP / P τ) * (mktValue q b τ / P τ) - s τ) τ := by
  convert (hasDerivAt_mktValue_flow h hmat hflow).div hP hP0 using 1
  rw [valueWeightedReturn]
  field_simp
  ring

/-- Cochrane (2023), §3.6.2 under perfect foresight: zero-coupon bond prices
`q(x, m) = exp(−∫_x^m i)` satisfy `∂_x q = i(x)q`, `∂_m q = −i(m)q` and `q(m, m) = 1`. -/
theorem zeroPrice_partials {i : ℝ → ℝ} (hi : Continuous i) (x m : ℝ) :
    HasDerivAt (fun y => disc i y m) (i x * disc i x m) x ∧
      HasDerivAt (fun y => disc i x y) (-(i m) * disc i x m) m ∧ disc i m m = 1 := by
  refine ⟨?_, ?_, disc_self i m⟩
  · have h1 : HasDerivAt (fun y => ∫ u in y..m, i u) (-(i x)) x :=
      intervalIntegral.integral_hasDerivAt_left (hi.intervalIntegrable _ _)
        (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
    refine h1.neg.exp.congr_deriv ?_
    simp only [disc, cumRate, Pi.neg_apply]
    ring
  · have h1 : HasDerivAt (fun y => ∫ u in x..y, i u) (i m) m :=
      intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable _ _)
        (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
    refine h1.neg.exp.congr_deriv ?_
    simp only [disc, cumRate, Pi.neg_apply]
    ring

/-- Cochrane (2023), eq. (3.39) with perfect-foresight pricing: if `∂_x q = i q` for all bonds
outstanding, the capital gain is `i·∫q b`, i.e. the value-weighted nominal return is `i`. -/
theorem capitalGain_priced {q b qt : ℝ → ℝ → ℝ} {i : ℝ → ℝ} {τ : ℝ}
    (hprice : ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j)) :
    capitalGain qt b τ = i τ * mktValue q b τ := by
  rw [capitalGain, mktValue, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun j hj => ?_)
  rw [hprice j hj]
  ring

/-- Cochrane (2023), eqs. (3.34), (3.38)–(3.39) with perfect-foresight pricing, general
maturity structure: the nominal market value obeys the short-debt flow (3.29),
`d/dx ∫q b = i ∫q b − P s`. -/
theorem hasDerivAt_mktValue_priced {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s : ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hprice : ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) :
    HasDerivAt (mktValue q b) (i τ * mktValue q b τ - P τ * s τ) τ := by
  have := hasDerivAt_mktValue_flow h hmat hflow
  rwa [capitalGain_priced hprice] at this

/-- Cochrane (2023), eq. (3.39), general maturity structure: with regularity on `[t, ∞)`,
maturing bonds at par, perfect-foresight pricing and the flow (3.34) on `(t, ∞)`, and a positive
price level (free to jump at `t`), the real value `V = ∫q b dj/P` solves the flow identity
`V' = (i − π)V − s` on `[t, ∞)`. -/
theorem flowOn_value_general {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s dP : ℝ → ℝ} {t : ℝ}
    (hreg : ∀ τ, t ≤ τ → MaturityRegularAt q b qt qm bt bm τ)
    (hmat : ∀ τ, t ≤ τ → q τ τ = 1)
    (hprice : ∀ τ, t ≤ τ → ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : ∀ τ, t ≤ τ → b τ τ = P τ * s τ + issuanceValue q bt τ)
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => mktValue q b τ / P τ) t := by
  have hD : ∀ τ, t ≤ τ → HasDerivAt (mktValue q b) (i τ * mktValue q b τ - P τ * s τ) τ :=
    fun τ hτ => hasDerivAt_mktValue_priced (hreg τ hτ) (hmat τ hτ) (hprice τ hτ) (hflow τ hτ)
  exact flowOn_of_nominal (B := mktValue q b)
    (fun τ hτ => (hD τ hτ).continuousAt.continuousWithinAt) hPc hPpos
    (fun τ hτ => hD τ hτ.le) hP

/-- Cochrane (2023), eq. (3.35), p. 75, general maturity structure: along the flow, the
valuation equation `∫Q B dj/P = ∫_t^∞ D(t,τ)s(τ)dτ` holds iff the transversality condition
holds; and then the price level is `P(t) = ∫Q B dj/∫D s`. -/
theorem valuation_general_iff {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s dP : ℝ → ℝ} {t : ℝ}
    (hreg : ∀ τ, t ≤ τ → MaturityRegularAt q b qt qm bt bm τ)
    (hmat : ∀ τ, t ≤ τ → q τ τ = 1)
    (hprice : ∀ τ, t ≤ τ → ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : ∀ τ, t ≤ τ → b τ τ = P τ * s τ + issuanceValue q bt τ)
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ)
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t) :
    (mktValue q b t / P t = pv (fun τ => i τ - dP τ / P τ) s t ↔
      TVC (fun τ => i τ - dP τ / P τ) (fun τ => mktValue q b τ / P τ) t) ∧
    (TVC (fun τ => i τ - dP τ / P τ) (fun τ => mktValue q b τ / P τ) t →
      mktValue q b t ≠ 0 → pv (fun τ => i τ - dP τ / P τ) s t ≠ 0 →
      P t = mktValue q b t / pv (fun τ => i τ - dP τ / P τ) s t) := by
  have hF := flowOn_value_general hreg hmat hprice hflow hPc hPpos hP
  refine ⟨valuation_iff_tvc hr hs hF hI, fun hT hA hpv => ?_⟩
  exact (price_level_determined hr hs hI hA hpv).1 ⟨_, hF, hT, rfl⟩

/-- Cochrane (2023), §3.6.2 and A1.2.1, geometric special case: with zero-coupon prices
`exp(−∫_x^m i)` and the density `b(x, m) = B(x)e^{−ω(m−x)}`, the general market value is the
bundle value, `∫q b dj = Q(x)B(x)`. -/
theorem mktValue_geometric {i B : ℝ → ℝ} {ω x : ℝ} (hi : ContinuousOn i (Set.Ici x)) :
    mktValue (fun y m => disc i y m) (fun y m => B y * Real.exp (-(ω * (m - y)))) x =
      bondPrice i ω x * B x := by
  have h := integral_Ioi_shift (fun u => disc i x u * (B x * Real.exp (-(ω * (u - x))))) x
  rw [mktValue]
  rw [h, bondPrice_eq hi, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  ring

/-- Cochrane (2023), (3.34), geometric special case: with net sales of the bond due at `m` equal
to `(B' + ωB)e^{−ω(m−x)}` (`hasDerivAt_debtDensity`), the general flow (3.34)
`b(τ,τ) = Ps + ∫q ∂_x b dj` is the geometric flow `Q(B' + ωB) = B − Ps`. -/
theorem flow_general_geometric_iff {i B dB P s : ℝ → ℝ} {ω τ : ℝ}
    (hi : ContinuousOn i (Set.Ici τ)) :
    ((fun y m => B y * Real.exp (-(ω * (m - y)))) τ τ = P τ * s τ +
        issuanceValue (fun y m => disc i y m)
          (fun y m => (dB y + ω * B y) * Real.exp (-(ω * (m - y)))) τ) ↔
      bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ := by
  have h : issuanceValue (fun y m => disc i y m)
      (fun y m => (dB y + ω * B y) * Real.exp (-(ω * (m - y)))) τ =
      bondPrice i ω τ * (dB τ + ω * B τ) :=
    mktValue_geometric (B := fun y => dB y + ω * B y) hi
  rw [h]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), §3.6.2, finite-portfolio special case: if the debt density is a finite
combination `b(x, m) = Σ_k B_k(x)φ_k(m)` of fixed coupon schedules `φ_k` (bond `k` pays
`φ_k(m)` at `m`), the market value is `Σ_k Q_k(x)B_k(x)` with `Q_k(x) = ∫_0^∞ q(x,x+j)φ_k(x+j)dj`;
the same formula with `B_k'` gives the value of net sales. -/
theorem mktValue_finite {ι : Type*} (S : Finset ι) (q : ℝ → ℝ → ℝ) (Bk φ : ι → ℝ → ℝ) (x : ℝ)
    (hint : ∀ k ∈ S, IntegrableOn (fun j => q x (x + j) * φ k (x + j)) (Set.Ioi 0)) :
    mktValue q (fun y m => ∑ k ∈ S, Bk k y * φ k m) x =
      ∑ k ∈ S, (∫ j in Set.Ioi 0, q x (x + j) * φ k (x + j)) * Bk k x := by
  rw [mktValue]
  have he : (fun j => q x (x + j) * ∑ k ∈ S, Bk k x * φ k (x + j)) =
      fun j => ∑ k ∈ S, q x (x + j) * φ k (x + j) * Bk k x := by
    funext j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [he, integral_finsetSum S (fun k hk => (hint k hk).mul_const _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_mul_const]

/-- Cochrane (2023), (3.34), finite-portfolio special case: with `b = Σ_k B_kφ_k` and net sales
`∂_x b = Σ_k B_k'φ_k`, the general flow (3.34) is the finite-portfolio flow
`Σ_k φ_k(τ)B_k(τ) = P s + Σ_k Q_k B_k'` of `hasDerivAt_value_portfolio` (coupon `c_k = φ_k`). -/
theorem flow_general_finite_iff {ι : Type*} (S : Finset ι) (q : ℝ → ℝ → ℝ)
    (Bk dBk φ : ι → ℝ → ℝ) (P s : ℝ → ℝ) (τ : ℝ)
    (hint : ∀ k ∈ S, IntegrableOn (fun j => q τ (τ + j) * φ k (τ + j)) (Set.Ioi 0)) :
    ((fun y m => ∑ k ∈ S, Bk k y * φ k m) τ τ = P τ * s τ +
        issuanceValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ) ↔
      ∑ k ∈ S, φ k τ * Bk k τ = P τ * s τ +
        ∑ k ∈ S, (∫ j in Set.Ioi 0, q τ (τ + j) * φ k (τ + j)) * dBk k τ := by
  have h := mktValue_finite S q dBk φ τ hint
  rw [show issuanceValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ =
    mktValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ from rfl, h]
  beta_reduce
  rw [Finset.sum_congr rfl (fun k _ => mul_comm (Bk k τ) (φ k τ))]

end Cochrane.Generality.ContinuousLong

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linearised identities in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, pp. 76–79.

All paths are deterministic (`ℝ → ℝ`), differentiable where stated; infinite-horizon present
values are genuine improper integrals over `(t, ∞)` with integrability as an explicit hypothesis
(signed integrands: absolute integrability). The book's innovations `Δ_t` are formalised as the
difference between two perfect-foresight paths ("old" and "new") from the news date `t` on.

* A valuation engine: `G' = g` on `[t, ∞)` with `g` integrable gives `G(T) → G(t) + ∫_t^∞ g`;
  for `V' = rV − f` and a discount factor `Λ' = −rΛ`, the transversality condition
  `Λ(T)V(T) → 0` holds **iff** `V(t) = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`; uniqueness and existence.
* (3.39)–(3.40): steady state `s = rV`; the exact derivative of the flow map at the steady state.
* (3.41)–(3.43): the linearised value identity, iff the TVC, in the book's shifted form
  `∫_0^∞ e^{−rτ} x_{t+τ} dτ` (with the integrand index corrected, E21); the shift itself is
  `ContinuousShort.integral_Ioi_shift`.
* p. 76: `dR^n = dR + π dt` (nominal and real returns of a nominal asset).
* p. 77: AR(1) surpluses `ds = −ηs dt` (corrected, E18), present value `s/(r+η)`, news `σ/(r+η)`.
* (3.47): bond price `Q = 1/(ω+y)`, the holding return as the limit of the discrete return, and
  `dR^n = y dt + dQ/Q`.
* (3.48): exact derivative of the bond-return identity at the steady state; the book's
  intermediate line has the wrong sign (E19).
* (3.49): forward solution of (3.48), unique under the TVC (or boundedness).
* (3.46), (3.50), (3.51): news identities between two equilibria; the `ω → ∞` short-debt limit
  (the book says `ω = 0`, E20) and the `ω = 0` perpetuity counterexample.
-/

namespace Cochrane.Generality.ContinuousLinear

open Filter Topology MeasureTheory

/-! ## The valuation engine -/

/-- Cochrane (2023), §3.6, pp. 73–76 (integrating a flow forward): if `G' = g` on `[t, ∞)` and `g`
is integrable on `(t, ∞)`, then `G(T) → G(t) + ∫_t^∞ g`. -/
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

/-- Cochrane (2023), §3.6, p. 74: the tail of a convergent improper integral vanishes,
`∫_T^∞ g → 0` as `T → ∞`. -/
theorem tendsto_integral_Ioi_zero {g : ℝ → ℝ} {t : ℝ} (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto (fun T => ∫ τ in Set.Ioi T, g τ) atTop (𝓝 0) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id)
  have h := (tendsto_const_nhds (x := ∫ τ in Set.Ioi t, g τ)).sub hI
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have := intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Set.Ioi_subset_Ioi hT))
  simp only [id]
  linarith

/-- Cochrane (2023), (3.29)–(3.31), pp. 73–74: along `V' = rV − f` and `Λ' = −rΛ`, the
discounted value obeys `(ΛV)' = −Λf`. -/
theorem discounted_hasDerivAt {Λ V r f : ℝ → ℝ} {τ : ℝ}
    (hΛ : HasDerivAt Λ (-(r τ) * Λ τ) τ) (hV : HasDerivAt V (r τ * V τ - f τ) τ) :
    HasDerivAt (fun u => Λ u * V u) (-(Λ τ * f τ)) τ := by
  have h := hΛ.mul hV
  convert h using 1
  ring

/-- Cochrane (2023), (3.31), pp. 73–74: along `V' = rV − f` with discount factor `Λ' = −rΛ` and
`Λf` integrable, the discounted value converges: `Λ(T)V(T) → Λ(t)V(t) − ∫_t^∞ Λf`. -/
theorem discounted_tendsto {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Λ T * V T) atTop (𝓝 (Λ t * V t - ∫ τ in Set.Ioi t, Λ τ * f τ)) := by
  have h := tendsto_of_hasDerivAt (G := fun u => Λ u * V u) (g := fun u => -(Λ u * f u))
    (fun τ hτ => discounted_hasDerivAt (hΛ τ hτ) (hV τ hτ)) hint.neg
  rw [integral_neg] at h
  simpa [sub_eq_add_neg] using h

/-- Cochrane (2023), (3.31), p. 74: `∫_t^∞ (Λ_τ/Λ_t) f_τ dτ = (1/Λ_t) ∫_t^∞ Λ_τ f_τ dτ`. -/
theorem integral_ratio_eq {Λ f : ℝ → ℝ} (t : ℝ) :
    ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ = (Λ t)⁻¹ * ∫ τ in Set.Ioi t, Λ τ * f τ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), (3.31) and A1.4, pp. 74, 564–565: **valuation iff transversality.**
If `V' = rV − f` and `Λ' = −rΛ` on `[t, ∞)`, `Λ_t > 0` and `Λf` is integrable, then the TVC
`Λ(T)V(T) → 0` holds iff `V_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
theorem tvc_iff_valuation {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛt : 0 < Λ t)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Λ T * V T) atTop (𝓝 0) ↔
      V t = ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ := by
  have hlim := discounted_tendsto hΛ hV hint
  rw [integral_ratio_eq]
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    field_simp
    linarith
  · intro hv
    have : Λ t * V t - ∫ τ in Set.Ioi t, Λ τ * f τ = 0 := by
      rw [hv]; field_simp; ring
    rwa [this] at hlim

/-- Cochrane (2023), (3.31), p. 74: under the TVC the valuation equation holds at **every**
date `t' ≥ t`. -/
theorem valuation_every_date {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, t ≤ τ → 0 < Λ τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t))
    (htvc : Tendsto (fun T => Λ T * V T) atTop (𝓝 0)) (t' : ℝ) (ht' : t ≤ t') :
    V t' = ∫ τ in Set.Ioi t', Λ τ / Λ t' * f τ :=
  (tvc_iff_valuation (fun τ hτ => hΛ τ (le_trans ht' hτ)) (hΛpos t' ht')
    (fun τ hτ => hV τ (le_trans ht' hτ)) (hint.mono_set (Set.Ioi_subset_Ioi ht'))).1 htvc

/-- Cochrane (2023), (3.31), p. 74: **uniqueness**: two solutions of `V' = rV − f` satisfying the
TVC coincide on `[t, ∞)`. -/
theorem valuation_unique {Λ V W r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, t ≤ τ → 0 < Λ τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hW : ∀ τ, t ≤ τ → HasDerivAt W (r τ * W τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t))
    (hV0 : Tendsto (fun T => Λ T * V T) atTop (𝓝 0))
    (hW0 : Tendsto (fun T => Λ T * W T) atTop (𝓝 0)) (t' : ℝ) (ht' : t ≤ t') : V t' = W t' := by
  rw [valuation_every_date hΛ hΛpos hV hint hV0 t' ht',
    valuation_every_date hΛ hΛpos hW hint hW0 t' ht']

/-- Cochrane (2023), (3.31), p. 74: **existence**: if `Λ > 0`, `Λ' = −rΛ` everywhere, `Λf` is
continuous and integrable on every half-line, then `V_t := ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ` solves
`V' = rV − f` and the TVC. -/
theorem valuation_exists {Λ r f : ℝ → ℝ}
    (hΛ : ∀ τ, HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, 0 < Λ τ)
    (hc : Continuous fun τ => Λ τ * f τ)
    (hint : ∀ a, IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi a)) :
    (∀ τ, HasDerivAt (fun u => ∫ x in Set.Ioi u, Λ x / Λ u * f x)
      (r τ * (∫ x in Set.Ioi τ, Λ x / Λ τ * f x) - f τ) τ) ∧
    Tendsto (fun T => Λ T * ∫ x in Set.Ioi T, Λ x / Λ T * f x) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun τ => Λ τ * f τ with hg
  have hF : ∀ u, ∫ x in Set.Ioi u, g x = (∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x := by
    intro u
    rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint u)]
    ring
  have hV : ∀ u, ∫ x in Set.Ioi u, Λ x / Λ u * f x =
      (Λ u)⁻¹ * ((∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x) := by
    intro u; rw [integral_ratio_eq, hF]
  refine ⟨fun τ => ?_, ?_⟩
  · have hP := HasDerivAt.sub (hasDerivAt_const τ (∫ x in Set.Ioi 0, g x))
      (hc.integral_hasStrictDerivAt 0 τ).hasDerivAt
    rw [zero_sub] at hP
    have hI : HasDerivAt (fun u => (Λ u)⁻¹) (-(-(r τ) * Λ τ) / (Λ τ) ^ 2) τ :=
      (hΛ τ).inv (hΛpos τ).ne'
    have h := hI.mul hP
    rw [show (fun u => ∫ x in Set.Ioi u, Λ x / Λ u * f x) =
      fun u => (Λ u)⁻¹ * ((∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x) from funext hV,
      hV τ]
    convert h using 1
    have hΛne := (hΛpos τ).ne'
    simp only [hg, Pi.sub_apply]
    field_simp
    ring
  · have h := tendsto_integral_Ioi_zero (hint 0)
    refine h.congr' ?_
    filter_upwards with T
    rw [integral_ratio_eq, ← mul_assoc, mul_inv_cancel₀ (hΛpos T).ne', one_mul]

/-! ## Exponential discounting and the book's shifted integrals -/

/-- Cochrane (2023), p. 74: the constant-rate discount factor `Λ_τ = e^{−rτ}` obeys
`Λ' = −rΛ`. -/
theorem hasDerivAt_expDisc (r τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(r * u))) (-r * Real.exp (-(r * τ))) τ := by
  have h1 : HasDerivAt (fun u => -(r * u)) (-r) τ :=
    (HasDerivAt.neg ((hasDerivAt_id' τ).const_mul r)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), p. 74: `Λ_τ/Λ_t = e^{−r(τ−t)}` for `Λ_τ = e^{−rτ}`. -/
theorem expDisc_ratio (r t τ : ℝ) :
    Real.exp (-(r * τ)) / Real.exp (-(r * t)) = Real.exp (-(r * (τ - t))) := by
  rw [← Real.exp_sub]; ring_nf

/-- Cochrane (2023), p. 74 (constant real rate): if `V' = rV − f` on `[t, ∞)` with `r`
constant and `e^{−rτ} f_τ` integrable, then the TVC `e^{−rT}V_T → 0` holds iff
`V_t = ∫_0^∞ e^{−rτ} f_{t+τ} dτ`. -/
theorem const_rate_tvc_iff {V f : ℝ → ℝ} {r t : ℝ}
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(r * T)) * V T) atTop (𝓝 0) ↔
      V t = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * f (t + τ) := by
  have h := tvc_iff_valuation (Λ := fun u => Real.exp (-(r * u))) (r := fun _ => r)
    (fun τ _ => hasDerivAt_expDisc r τ) (Real.exp_pos _) hV hint
  rw [h]
  have : ∫ τ in Set.Ioi t, Real.exp (-(r * τ)) / Real.exp (-(r * t)) * f τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * f (t + τ) := by
    rw [← ContinuousShort.integral_Ioi_shift]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [expDisc_ratio, add_sub_cancel_left]
  rw [this]

/-- Cochrane (2023), (3.41)–(3.43), p. 76: shifting preserves integrability on half-lines:
`g` integrable on `(t, ∞)` gives `τ ↦ g(t+τ)` integrable on `(0, ∞)`. -/
theorem integrableOn_shift {g : ℝ → ℝ} {t : ℝ} (hg : IntegrableOn g (Set.Ioi t)) :
    IntegrableOn (fun τ => g (t + τ)) (Set.Ioi 0) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) t).integrableOn_comp_preimage
    (measurableEmbedding_addLeft t) (f := g) (s := Set.Ioi t)
  have hpre : (fun x => t + x) ⁻¹' Set.Ioi t = Set.Ioi 0 := by ext x; simp
  rw [hpre] at h
  exact h.2 hg

/-- Cochrane (2023), (3.43), p. 76: `e^{−aτ} g_τ` integrable on `(t, ∞)` gives
`τ ↦ e^{−aτ} g_{t+τ}` integrable on `(0, ∞)`. -/
theorem integrableOn_shift_weighted {g : ℝ → ℝ} {a t : ℝ}
    (hg : IntegrableOn (fun τ => Real.exp (-(a * τ)) * g τ) (Set.Ioi t)) :
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * g (t + τ)) (Set.Ioi 0) := by
  have h := (integrableOn_shift hg).const_mul (Real.exp (a * t))
  refine IntegrableOn.congr_fun h (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), (3.43), p. 76: `(Λ_t)⁻¹ ∫_t^∞ Λ_τ g_τ dτ = ∫_0^∞ e^{−aτ} g_{t+τ} dτ` for
`Λ_τ = e^{−aτ}`. -/
theorem shift_weighted (g : ℝ → ℝ) (a t : ℝ) :
    (Real.exp (-(a * t)))⁻¹ * ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * g τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * g (t + τ) := by
  have h := integral_ratio_eq (Λ := fun τ => Real.exp (-(a * τ))) (f := g) t
  rw [← h, ← ContinuousShort.integral_Ioi_shift]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [expDisc_ratio, add_sub_cancel_left]

/-- Cochrane (2023), (3.43), p. 76: linearity of a weighted integral,
`∫ w(a − c) = ∫ wa − ∫ wc`, under integrability of both pieces. -/
theorem integral_weighted_sub {w a c : ℝ → ℝ} {S : Set ℝ}
    (ha : IntegrableOn (fun τ => w τ * a τ) S) (hc : IntegrableOn (fun τ => w τ * c τ) S) :
    ∫ τ in S, w τ * (a τ - c τ) = (∫ τ in S, w τ * a τ) - ∫ τ in S, w τ * c τ := by
  rw [← integral_sub ha hc]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-! ## (3.39)–(3.43): the linearised flow and value identities -/

/-- Cochrane (2023), (3.39)–(3.40), p. 76: a constant value `V̄` with constant return `r` and
constant surplus `s̄` solves the flow `V' = V·R' − s` (here `R'` is the instantaneous real return)
iff `s̄ = rV̄`. -/
theorem steady_state_iff (Vbar r sbar : ℝ) :
    (∀ τ : ℝ, HasDerivAt (fun _ : ℝ => Vbar) (Vbar * r - sbar) τ) ↔ sbar = r * Vbar := by
  constructor
  · intro h
    have := (hasDerivAt_const (0 : ℝ) Vbar).unique (h 0)
    linarith
  · intro h τ
    have : Vbar * r - sbar = 0 := by rw [h]; ring
    rw [this]
    exact hasDerivAt_const τ Vbar

/-- Cochrane (2023), (3.40), p. 76: the exact derivative of the flow map `(V, R', s) ↦ V R' − s`
of (3.39) at the steady state `(V̄, r, rV̄)` is `(dV, dR', ds) ↦ r dV + V̄ dR' − ds`. -/
theorem flow_hasFDerivAt (Vbar r : ℝ) :
    ∃ L : ℝ × ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1 * x.2.1 - x.2.2) L (Vbar, r, r * Vbar) ∧
        ∀ h : ℝ × ℝ × ℝ, L h = r * h.1 + Vbar * h.2.1 - h.2.2 := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.snd
  refine ⟨_, (h1.mul h2).sub h3, fun h => ?_⟩
  simp
  ring

/-- Cochrane (2023), (3.40), p. 76: the flow (3.39) equals its linearisation (3.40) plus the
second-order remainder `(V − V̄)(R' − r)`; exact identity, valid when `s̄ = rV̄`. -/
theorem flow_remainder (V Vbar ret r s : ℝ) :
    V * ret - s = (-s + Vbar * (ret - r) + r * V) + (V - Vbar) * (ret - r) := by ring

/-- Cochrane (2023), p. 76: the deviation form of (3.40): with `s̄ = rV̄`,
`−s + V̄(R' − r) + rV = −(s − s̄) + V̄(R' − r) + r(V − V̄)`. -/
theorem flow_deviation_form (V Vbar ret r s : ℝ) :
    -s + Vbar * (ret - r) + r * V = -(s - r * Vbar) + Vbar * (ret - r) + r * (V - Vbar) := by
  ring

/-- Cochrane (2023), (3.42), p. 76: dividing the linearised flow (3.40) by `V̄`, `v = V/V̄` and
`s̃ = s/V̄` obey `v' = rv + (R' − r) − s̃`. -/
theorem normalised_flow {V ret s : ℝ → ℝ} {Vbar r τ : ℝ} (hVbar : Vbar ≠ 0)
    (hV : HasDerivAt V (-s τ + Vbar * (ret τ - r) + r * V τ) τ) :
    HasDerivAt (fun u => V u / Vbar) (r * (V τ / Vbar) + (ret τ - r) - s τ / Vbar) τ :=
  (hV.div_const Vbar).congr_deriv (by field_simp; ring)

/-- Cochrane (2023), (3.43), p. 76: **the linearised value identity iff the TVC.** If
`v' = rv + (R' − r) − s̃` on `[t, ∞)` and `e^{−rτ}(s̃ − (R' − r))` is integrable, then
`e^{−rT}v_T → 0` iff `v_t = ∫_0^∞ e^{−rτ}(s̃_{t+τ} − (R'_{t+τ} − r)) dτ`. -/
theorem linear_value_iff {v ret s : ℝ → ℝ} {r t : ℝ}
    (hv : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (ret τ - r) - s τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (ret τ - r))) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s (t + τ) - (ret (t + τ) - r)) :=
  const_rate_tvc_iff (f := fun τ => s τ - (ret τ - r))
    (fun τ hτ => (hv τ hτ).congr_deriv (by ring)) hint

/-- Cochrane (2023), (3.43), p. 76: under the TVC, with the two pieces separately integrable,
`v_t = ∫_0^∞ e^{−rτ} s̃_{t+τ} dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r) dτ` (the integrand index is
`t+τ`, cf. E21). -/
theorem linear_value_split {v ret s : ℝ → ℝ} {r t : ℝ}
    (hv : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (ret τ - r) - s τ) τ)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t))
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (ret τ - r)) (Set.Ioi t))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)) :
    v t = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s (t + τ)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (ret (t + τ) - r) := by
  have hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (ret τ - r))) (Set.Ioi t) :=
    (hs.sub hR).congr_fun (fun τ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  rw [(linear_value_iff hv hint).1 htvc]
  exact integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => s (t + τ)) (c := fun τ => ret (t + τ) - r)
    (integrableOn_shift_weighted hs) (integrableOn_shift_weighted (g := fun τ => ret τ - r) hR)

/-- Cochrane (2023), (3.41), p. 76: the linearised value identity in levels: if `V` solves the
linearised flow (3.40) on `[t, ∞)` and `e^{−rT}V_T → 0`, then
`V_t/V̄ = ∫_0^∞ e^{−rτ} s_{t+τ}/V̄ dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r) dτ` (printed integrand index
`dR_t` corrected to `dR_{t+τ}`, E21). -/
theorem value_identity_341 {V ret s : ℝ → ℝ} {Vbar r t : ℝ} (hVbar : Vbar ≠ 0)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (-s τ + Vbar * (ret τ - r) + r * V τ) τ)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t))
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (ret τ - r)) (Set.Ioi t))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * V T) atTop (𝓝 0)) :
    V t / Vbar = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s (t + τ) / Vbar)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (ret (t + τ) - r) := by
  have hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ / Vbar)) (Set.Ioi t) :=
    IntegrableOn.congr_fun (hs.div_const Vbar) (fun τ _ => by ring) measurableSet_Ioi
  have htvc' : Tendsto (fun T => Real.exp (-(r * T)) * (V T / Vbar)) atTop (𝓝 0) := by
    have := htvc.div_const Vbar
    rw [zero_div] at this
    exact this.congr fun T => by ring
  exact linear_value_split (v := fun u => V u / Vbar) (s := fun u => s u / Vbar)
    (fun τ hτ => normalised_flow hVbar (hV τ hτ)) hs' hR htvc'

/-! ## p. 76: nominal and real returns -/

/-- Cochrane (2023), p. 76: `dR = dR^n − π dt`: if a nominal value `X` grows at the nominal return
`R^n` and the price level at the inflation rate `π`, the real value `X/P` grows at `R^n − π`. -/
theorem real_return_of_nominal {X P : ℝ → ℝ} {Rn infl τ : ℝ}
    (hX : HasDerivAt X (Rn * X τ) τ) (hP : HasDerivAt P (infl * P τ) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => X u / P u) ((Rn - infl) * (X τ / P τ)) τ :=
  (hX.div hP hPτ).congr_deriv (by field_simp)

/-- Cochrane (2023), p. 76: `d(1/P)/(1/P) = −dP/P` when the price level has no jumps. -/
theorem inv_price_growth {P : ℝ → ℝ} {infl τ : ℝ} (hP : HasDerivAt P (infl * P τ) τ)
    (hPτ : P τ ≠ 0) : HasDerivAt (fun u => 1 / P u) (-infl * (1 / P τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hP hPτ
  exact h.congr_deriv (by field_simp; ring)

/-! ## p. 77: AR(1) surpluses (E18) -/

/-- Cochrane (2023), p. 77 (corrected, E18): `s_τ = e^{−ητ}s_0` solves `ds = −ηs dt`. -/
theorem ar1_hasDerivAt (η s0 τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(η * u)) * s0) (-η * (Real.exp (-(η * τ)) * s0)) τ :=
  ((hasDerivAt_expDisc η τ).mul_const s0).congr_deriv (by ring)

/-- Cochrane (2023), p. 77: every solution of `s' = −ηs` is `s_τ = e^{−ητ}s_0` (so
`E_t s_{t+τ} = e^{−ητ}s_t` with no constant, E18). -/
theorem ar1_unique {s : ℝ → ℝ} {η : ℝ} (hs : ∀ τ, HasDerivAt s (-η * s τ) τ) (τ : ℝ) :
    s τ = Real.exp (-(η * τ)) * s 0 := by
  have hG : ∀ u, HasDerivAt (fun x => Real.exp (η * x) * s x) 0 u := by
    intro u
    have he : HasDerivAt (fun x => Real.exp (η * x)) (η * Real.exp (η * u)) u :=
      (HasDerivAt.exp ((hasDerivAt_id' u).const_mul η)).congr_deriv (by ring)
    exact (he.mul (hs u)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt)
    (fun u => (hG u).deriv) τ 0
  simp only [mul_zero, Real.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Real.exp_add]
  simp

/-- Cochrane (2023), p. 77 (E18): the printed `E_t s_{t+τ} = e^{−ητ}s_t + s̄` is inconsistent with
`ds = −ηs dt` unless `s̄ = 0`: for `η ≠ 0`, `s̄ ≠ 0` the path `e^{−ητ}s_0 + s̄` never satisfies the
AR(1) law of motion. -/
theorem ar1_printed_not_solution {η s0 c : ℝ} (hη : η ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    ¬ HasDerivAt (fun u => Real.exp (-(η * u)) * s0 + c)
      (-η * (Real.exp (-(η * τ)) * s0 + c)) τ := by
  intro h
  have h2 := (ar1_hasDerivAt η s0 τ).add_const c
  have := h.unique h2
  have : η * c = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact hη h
  · exact hc h

/-- Cochrane (2023), p. 77: the AR(1) present-value integrand `e^{−rτ}e^{−ητ}s_0` is integrable
on `(0, ∞)` when `r + η > 0`. -/
theorem ar1_integrable {r η s0 : ℝ} (h : 0 < r + η) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0)) (Set.Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (a := -(r + η)) (by linarith) 0).mul_const s0
  refine IntegrableOn.congr_fun hi (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 77: the AR(1) present value
`∫_0^∞ e^{−rτ} e^{−ητ} s_t dτ = s_t/(r + η)` (for `r + η > 0`). -/
theorem ar1_pv {r η s0 : ℝ} (h : 0 < r + η) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0) = s0 / (r + η) := by
  have hI := integral_exp_mul_Ioi (a := -(r + η)) (by linarith) 0
  have : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r + η) * τ)) * s0 := by
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [this, hI]
  have hne : r + η ≠ 0 := h.ne'
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Cochrane (2023), p. 77: **news about an AR(1) surplus.** If the surplus follows `ds = −ηs dt`
on the old and on the new perfect-foresight path, and the news raises `s_t` by `σ`, the present
value of surpluses rises by `σ/(r + η)`. -/
theorem ar1_news {r η σ : ℝ} {sOld sNew : ℝ → ℝ} (h : 0 < r + η)
    (hOld : ∀ τ, HasDerivAt sOld (-η * sOld τ) τ) (hNew : ∀ τ, HasDerivAt sNew (-η * sNew τ) τ)
    (hσ : sNew 0 - sOld 0 = σ) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * sNew τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * sOld τ = σ / (r + η) := by
  have e1 : (fun τ => Real.exp (-(r * τ)) * sNew τ) =
      fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * sNew 0) :=
    funext fun τ => by rw [ar1_unique hNew τ]
  have e0 : (fun τ => Real.exp (-(r * τ)) * sOld τ) =
      fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * sOld 0) :=
    funext fun τ => by rw [ar1_unique hOld τ]
  rw [e1, e0, ar1_pv h, ar1_pv h, ← hσ]
  ring

/-! ## (3.47): bond prices and returns with geometric maturity -/

/-- Cochrane (2023), p. 77: the price of a bond with coupons `e^{−ωτ}` at yield `y` is
`Q = ∫_0^∞ e^{−τy} e^{−ωτ} dτ = 1/(ω + y)` (for `ω + y > 0`). -/
theorem bond_price_yield {ω y : ℝ} (h : 0 < ω + y) :
    ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(ω * τ)) = 1 / (ω + y) := by
  have hI := integral_exp_mul_Ioi (a := -(ω + y)) (by linarith) 0
  have : ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(ω * τ)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(ω + y) * τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  rw [this, hI]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Cochrane (2023), (3.47), pp. 77–78: the holding return over `[t, t+Δ]` of a geometric bond,
`(Δ + e^{−ωΔ} Q_{t+Δ} − Q_t)/(Q_t Δ)`, converges as `Δ → 0` to the instantaneous return
`(1 + Q')/Q − ω` (the first form of (3.47)). -/
theorem holding_return_tendsto {Q : ℝ → ℝ} {Q' ω t : ℝ} (hQ : HasDerivAt Q Q' t)
    (hQt : Q t ≠ 0) :
    Tendsto (fun Δ => (Δ + Real.exp (-(ω * Δ)) * Q (t + Δ) - Q t) / (Q t * Δ)) (𝓝[≠] 0)
      (𝓝 ((1 + Q') / Q t - ω)) := by
  have hQs : HasDerivAt (fun Δ => Q (t + Δ)) Q' 0 :=
    HasDerivAt.comp_const_add t 0 (by rwa [add_zero])
  have hφ : HasDerivAt (fun Δ => Δ + Real.exp (-(ω * Δ)) * Q (t + Δ))
      (1 + (-ω * Real.exp (-(ω * 0)) * Q (t + 0) + Real.exp (-(ω * 0)) * Q')) 0 :=
    HasDerivAt.add (hasDerivAt_id' 0) ((hasDerivAt_expDisc ω 0).mul hQs)
  have h := (hφ.tendsto_slope_zero).div_const (Q t)
  simp only [mul_zero, neg_zero, Real.exp_zero, add_zero, zero_add, one_mul, mul_one] at h
  have hlim : (1 + (-ω * Q t + Q')) / Q t = (1 + Q') / Q t - ω := by field_simp; ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have hΔ' : Δ ≠ 0 := hΔ
  simp only [smul_eq_mul]
  field_simp

/-- Cochrane (2023), (3.47), p. 78: when `Q_t = 1/(ω + y_t)`, the instantaneous return is
`(1 + Q')/Q − ω = y + Q'/Q` (the second form of (3.47)). -/
theorem return_eq_yield {Q Q' ω y : ℝ} (hQ : Q = 1 / (ω + y)) :
    (1 + Q') / Q - ω = y + Q' / Q := by
  subst hQ
  field_simp
  ring

/-- Cochrane (2023), p. 78: the return definition (3.47) is equivalent to the identity
`Q dR^n = 1 dt + dQ − ωQ dt`. -/
theorem return_identity_iff {Q Q' ω Rn : ℝ} (hQ : Q ≠ 0) :
    Rn = (1 + Q') / Q - ω ↔ Q * Rn = 1 + Q' - ω * Q := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp; linarith

/-! ## (3.48)–(3.49): the linearised bond price (E19) -/

/-- Cochrane (2023), p. 78: the steady state `R^n = r`, `dQ = 0`, `Q̄ = 1/(r + ω)` satisfies the
bond-return identity `Q R^n − 1 − Q' + ωQ = 0`. -/
theorem bond_steady_state {r ω : ℝ} (h : r + ω ≠ 0) :
    1 / (r + ω) * r - 1 - 0 + ω * (1 / (r + ω)) = 0 := by
  field_simp; ring

/-- Cochrane (2023), p. 78: the exact derivative of the bond-return map
`(Q, Q', R^n) ↦ Q R^n − 1 − Q' + ωQ` at the steady state `(Q̄, 0, r)`, `Q̄ = 1/(r+ω)`, is
`(dQ, dQ', dR^n) ↦ (r + ω) dQ − dQ' + Q̄ dR^n`. -/
theorem bond_hasFDerivAt (r ω : ℝ) :
    ∃ L : ℝ × ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1 * x.2.2 - 1 - x.2.1 + ω * x.1) L
        (1 / (r + ω), 0, r) ∧
        ∀ h : ℝ × ℝ × ℝ, L h = (r + ω) * h.1 - h.2.1 + 1 / (r + ω) * h.2.2 := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.snd
  refine ⟨_, (((h1.mul h3).sub_const 1).sub h2).add (h1.const_mul ω), fun h => ?_⟩
  simp
  ring

/-- Cochrane (2023), (3.48), p. 78: the linearised bond identity
`(r+ω)(Q − Q̄) − Q' + Q̄(R^n − r) = 0` is equivalent, with `q = Q/Q̄`, `q' = Q'/Q̄`, to
`q' = (R^n − r) + (ω + r)(q − 1)`. -/
theorem bond_linear_iff {r ω Q Q' Rn : ℝ} (h : 0 < r + ω) :
    (r + ω) * (Q - 1 / (r + ω)) - Q' + 1 / (r + ω) * (Rn - r) = 0 ↔
      Q' / (1 / (r + ω)) = (Rn - r) + (ω + r) * (Q / (1 / (r + ω)) - 1) := by
  have hne : r + ω ≠ 0 := h.ne'
  constructor
  · intro h0
    field_simp
    field_simp at h0
    linarith
  · intro h0
    field_simp at h0
    field_simp
    linarith

/-- Cochrane (2023), p. 78 (corrected, E19): (3.48) is equivalent to
`R^n − r = q' + (r + ω)(1 − q)`. -/
theorem bond_linear_corrected_line {r ω q q' Rn : ℝ} :
    q' = (Rn - r) + (ω + r) * (q - 1) ↔ Rn - r = q' + (r + ω) * (1 - q) := by
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 78 (E19): the printed intermediate line
`R^n − r = q' − (r + ω)(1 − q)` together with (3.48) forces `q = 1`, so it is not equivalent to
(3.48) off the steady state. -/
theorem printed_line_forces_steady {r ω q q' Rn : ℝ} (h : r + ω ≠ 0)
    (h348 : q' = (Rn - r) + (ω + r) * (q - 1)) (hprinted : Rn - r = q' - (r + ω) * (1 - q)) :
    q = 1 := by
  have : (r + ω) * (q - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 h
  · linarith

/-- Cochrane (2023), p. 78 (E19): a point satisfying (3.48) but violating the printed line:
`q = 2`, `R^n = r`, `q' = r + ω`. -/
theorem printed_line_counterexample {r ω : ℝ} (h : 0 < r + ω) :
    (r + ω) = (r - r) + (ω + r) * (2 - 1) ∧ ¬ (r - r = (r + ω) - (r + ω) * (1 - 2)) := by
  constructor
  · ring
  · intro h'; linarith

/-- Cochrane (2023), (3.49), p. 78: **the bond price forward solution iff the TVC.** If
`q' = (R^n − r) + (ω + r)(q − 1)` on `[t, ∞)` and `e^{−(r+ω)τ}(R^n_τ − r)` is integrable, then
`e^{−(r+ω)T}(q_T − 1) → 0` iff `q_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r) dτ`. -/
theorem bond_price_forward_iff {q Rn : ℝ → ℝ} {r ω t : ℝ}
    (hq : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-((r + ω) * T)) * (q T - 1)) atTop (𝓝 0) ↔
      q t = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) := by
  have hx : ∀ τ, t ≤ τ → HasDerivAt (fun u => q u - 1)
      ((r + ω) * (q τ - 1) - (-(Rn τ - r))) τ :=
    fun τ hτ => ((hq τ hτ).sub_const 1).congr_deriv (by ring)
  have hint' : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (-(Rn τ - r))) (Set.Ioi t) :=
    hint.neg.congr_fun (fun τ _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
  rw [const_rate_tvc_iff (V := fun u => q u - 1) (f := fun τ => -(Rn τ - r)) hx hint']
  have : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * -(Rn (t + τ) - r) =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [this]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 78: a path bounded on `[t, ∞)` satisfies the transversality condition
`e^{−aT}x_T → 0` for every `a > 0`. -/
theorem tvc_of_bounded {x : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (hb : ∀ T, t ≤ T → |x T| ≤ K) :
    Tendsto (fun T => Real.exp (-(a * T)) * x T) atTop (𝓝 0) := by
  have he : Tendsto (fun T => Real.exp (-(a * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have hK := he.mul_const K
  rw [zero_mul] at hK
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb T hT) (Real.exp_pos _).le

/-- Cochrane (2023), (3.49), p. 78: **uniqueness**: every solution of (3.48) that is bounded on
`[t, ∞)` is the forward solution (3.49), at every date `t' ≥ t` (`r + ω > 0`). -/
theorem bond_price_forward_bounded {q Rn : ℝ → ℝ} {r ω t K : ℝ} (h : 0 < r + ω)
    (hq : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t))
    (hb : ∀ T, t ≤ T → |q T| ≤ K) (t' : ℝ) (ht' : t ≤ t') :
    q t' = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t' + τ) - r) := by
  refine (bond_price_forward_iff (fun τ hτ => hq τ (le_trans ht' hτ))
    (hint.mono_set (Set.Ioi_subset_Ioi ht'))).1 ?_
  refine tvc_of_bounded (t := t) (K := K + 1) h fun T hT => ?_
  have := hb T hT
  calc |q T - 1| ≤ |q T| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ K + 1 := by rw [abs_one]; linarith

/-- Cochrane (2023), (3.49), p. 78: the forward-solution bond price
`q^F_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r) dτ`. -/
noncomputable def bondForward (r ω : ℝ) (Rn : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r)

/-- Cochrane (2023), (3.49), p. 78: **existence**: for a continuous return path with
`|R^n − r| ≤ K`, the forward solution solves (3.48) at every date and is bounded,
`|q^F − 1| ≤ K/(r + ω)`; with `bond_price_forward_bounded` it is the unique bounded solution. -/
theorem bondForward_spec {Rn : ℝ → ℝ} {r ω K : ℝ} (h : 0 < r + ω) (hc : Continuous Rn)
    (hb : ∀ τ, |Rn τ - r| ≤ K) :
    (∀ τ, HasDerivAt (bondForward r ω Rn)
      ((Rn τ - r) + (r + ω) * (bondForward r ω Rn τ - 1)) τ) ∧
    ∀ τ, |bondForward r ω Rn τ - 1| ≤ K / (r + ω) := by
  set a := r + ω with ha
  have hmeas : ∀ u : ℝ, AEStronglyMeasurable (fun τ => Real.exp (-(a * τ)) * (Rn τ - r))
      (volume.restrict (Set.Ioi u)) := fun u =>
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (hc.sub continuous_const)).aestronglyMeasurable
  have hdom : ∀ u : ℝ, IntegrableOn (fun τ => Real.exp (-(a * τ)) * (Rn τ - r)) (Set.Ioi u) := by
    intro u
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -a) (by linarith) u).const_mul K)
      (hmeas u) (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm K, neg_mul]
    exact mul_le_mul_of_nonneg_left (hb τ) (Real.exp_pos _).le
  have hint : ∀ u : ℝ,
      IntegrableOn (fun τ => Real.exp (-(a * τ)) * (-(Rn τ - r))) (Set.Ioi u) := fun u =>
    (hdom u).neg.congr_fun (fun τ _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
  obtain ⟨hd, -⟩ := valuation_exists (Λ := fun u => Real.exp (-(a * u))) (r := fun _ => a)
    (f := fun τ => -(Rn τ - r)) (fun τ => hasDerivAt_expDisc a τ) (fun τ => Real.exp_pos _)
    (by fun_prop) hint
  have heq : ∀ u, bondForward r ω Rn u =
      1 + ∫ x in Set.Ioi u, Real.exp (-(a * x)) / Real.exp (-(a * u)) * -(Rn x - r) := by
    intro u
    rw [bondForward, integral_ratio_eq, shift_weighted (fun τ => -(Rn τ - r)) a u]
    rw [← ha]
    have : ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * -(Rn (u + τ) - r) =
        -∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * (Rn (u + τ) - r) := by
      rw [← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only
      ring
    rw [this]
    ring
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [show bondForward r ω Rn = fun u =>
      1 + ∫ x in Set.Ioi u, Real.exp (-(a * x)) / Real.exp (-(a * u)) * -(Rn x - r) from
      funext heq]
    exact ((hd τ).const_add 1).congr_deriv (by beta_reduce; ring)
  · have hbound : ‖∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)‖ ≤
        ∫ x in Set.Ioi 0, K * Real.exp (-a * x) := by
      refine norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul K)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm K, neg_mul]
      exact mul_le_mul_of_nonneg_left (hb (τ + x)) (Real.exp_pos _).le
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
    simp only [mul_zero, Real.exp_zero] at hbound
    have hval : K * (-1 / -a) = K / a := by field_simp
    rw [hval, Real.norm_eq_abs] at hbound
    rw [bondForward, ← ha]
    calc |1 - (∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)) - 1|
        = |∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)| := by
          rw [show ∀ z : ℝ, 1 - z - 1 = -z from fun z => by ring, abs_neg]
      _ ≤ K / a := hbound

/-! ## The value of debt at the news date and the unexpected bond return -/

/-- Cochrane (2023), (3.35), (3.46), pp. 75–77: the exact derivative of the value of debt
`V = Q·b` (bond price times real face value), normalised by `V̄ = Q̄ b̄`, at the steady state:
`(dQ, db) ↦ dQ/Q̄ + db/b̄`, i.e. `v − 1 = (q − 1) + (β − 1)` to first order. -/
theorem value_hasFDerivAt {Qbar bbar : ℝ} (hQ : Qbar ≠ 0) (hb : bbar ≠ 0) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ => x.1 * x.2 * (1 / (Qbar * bbar))) L (Qbar, bbar) ∧
        ∀ h : ℝ × ℝ, L h = h.1 / Qbar + h.2 / bbar := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      ((Qbar, bbar) : ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((Qbar, bbar) : ℝ × ℝ) := hasFDerivAt_snd
  refine ⟨_, HasFDerivAt.mul_const (HasFDerivAt.mul h1 h2) (1 / (Qbar * bbar)), fun h => ?_⟩
  simp
  field_simp
  ring

/-- Cochrane (2023), pp. 75–77: the exact decomposition
`Qb/(Q̄b̄) − 1 = (q − 1) + (β − 1) + (q − 1)(β − 1)` with `q = Q/Q̄`, `β = b/b̄`; the last term is
the second-order remainder dropped by the linearisation. -/
theorem value_remainder {Q b Qbar bbar : ℝ} (hQ : Qbar ≠ 0) (hb : bbar ≠ 0) :
    Q * b / (Qbar * bbar) - 1 =
      (Q / Qbar - 1) + (b / bbar - 1) + (Q / Qbar - 1) * (b / bbar - 1) := by
  field_simp
  ring

/-- Cochrane (2023), pp. 77–78: **the unexpected bond return is the bond-price jump.** On the
combined path (old price `Q₀` before the news date `t`, new price `Q₁` from `t` on), the holding
return over `[t − h, t + h]`, `(2h + e^{−2ωh}Q₁(t+h) − Q₀(t−h))/Q₀(t−h)`, converges as `h → 0`
to `(Q₁(t) − Q₀(t))/Q₀(t)`: the coupon accrual vanishes and only the revaluation remains. -/
theorem news_return_tendsto {Q₀ Q₁ : ℝ → ℝ} {ω t : ℝ} (h₀ : ContinuousAt Q₀ t)
    (h₁ : ContinuousAt Q₁ t) (hpos : Q₀ t ≠ 0) :
    Tendsto (fun h => (2 * h + Real.exp (-(ω * (2 * h))) * Q₁ (t + h) - Q₀ (t - h)) / Q₀ (t - h))
      (𝓝 0) (𝓝 ((Q₁ t - Q₀ t) / Q₀ t)) := by
  have hp : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add t
  have hm : Tendsto (fun h : ℝ => t - h) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_sub t
  have hQ1 := h₁.tendsto.comp hp
  have hQ0 := h₀.tendsto.comp hm
  have he : Tendsto (fun h : ℝ => Real.exp (-(ω * (2 * h)))) (𝓝 0) (𝓝 1) := by
    have : Continuous fun h : ℝ => Real.exp (-(ω * (2 * h))) := by fun_prop
    simpa using this.tendsto 0
  have h2 : Tendsto (fun h : ℝ => 2 * h) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2
  have hnum := (h2.add (he.mul hQ1)).sub hQ0
  have hlim := hnum.div hQ0 hpos
  rw [zero_add, one_mul] at hlim
  exact hlim

/-! ## News between two perfect-foresight equilibria: (3.46), (3.50), (3.51) -/

namespace Eqm

variable (r ω t : ℝ) (v q b Rn infl s : ℝ → ℝ)

/-- Cochrane (2023), (3.42)–(3.43), (3.47)–(3.49), pp. 76–78: a perfect-foresight path of the
linearised model from date `t` on: value `v`, bond price `q`, linearised real face value `b`
(predetermined: `B` is predetermined and `P` does not jump), nominal bond return `R^n`,
inflation `π` (`infl`), surplus `s̃`; real return `R' = R^n − π` (p. 76). Fields: the flow (3.42),
the bond identity (3.48), the value split `v = q + b − 1` at `t` (`value_hasFDerivAt`), the two
transversality conditions and integrability of the discounted pieces. -/
structure LinearEqm where
  flow : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (Rn τ - infl τ - r) - s τ) τ
  bond : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ
  value : v t = q t + b t - 1
  tvcV : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)
  tvcQ : Tendsto (fun T => Real.exp (-((r + ω) * T)) * (q T - 1)) atTop (𝓝 0)
  intS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t)
  intR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (Rn τ - infl τ - r)) (Set.Ioi t)
  intN : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t)

end Eqm

/-- Cochrane (2023), p. 76: the steady state `v = q = b = 1`, `R^n = r`, `π = 0`, `s̃ = r` is a
linearised equilibrium (for `r > 0`), so `Eqm.LinearEqm` is inhabited. -/
theorem steady_state_eqm {r ω t : ℝ} (hr : 0 < r) :
    Eqm.LinearEqm r ω t (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => r) (fun _ => 0)
      (fun _ => r) := by
  have hz : ∀ f : ℝ → ℝ, (∀ τ, f τ = 0) → IntegrableOn f (Set.Ioi t) := fun f hf =>
    IntegrableOn.congr_fun (integrableOn_zero (s := Set.Ioi t) (μ := volume))
      (fun τ _ => (hf τ).symm) measurableSet_Ioi
  refine ⟨fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring),
    fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring), by ring,
    tvc_of_bounded (t := t) (K := 1) hr (fun T _ => by simp), ?_, ?_,
    hz _ (fun τ => by ring), hz _ (fun τ => by ring)⟩
  · simp
  · refine IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) t).mul_const r) (fun τ _ => ?_)
      measurableSet_Ioi
    simp only [neg_mul]

/-- Cochrane (2023), (3.43), p. 76: in a linearised equilibrium,
`v_t = ∫_0^∞ e^{−rτ}s̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r)dτ`. -/
theorem eqm_value {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ}
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    v t = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s (t + τ)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Rn (t + τ) - infl (t + τ) - r) :=
  linear_value_split (ret := fun τ => Rn τ - infl τ) E.flow E.intS E.intR E.tvcV

/-- Cochrane (2023), (3.49), p. 78: in a linearised equilibrium,
`q_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r)dτ`. -/
theorem eqm_bond {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ}
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    q t = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) :=
  (bond_price_forward_iff E.bond E.intN).1 E.tvcQ

/-- Cochrane (2023), (3.51), p. 78: with `ω ≥ 0`, the real-return term discounted at `r + ω`
is integrable (shifted form). -/
theorem eqm_int_real_bond {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ} (hω : 0 ≤ ω)
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - infl (t + τ) - r))
      (Set.Ioi 0) := by
  have hR := integrableOn_shift_weighted (g := fun τ => Rn τ - infl τ - r) E.intR
  have hm : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-(ω * τ)))
      (volume.restrict (Set.Ioi 0)) := by
    have : Continuous fun τ : ℝ => Real.exp (-(ω * τ)) := by fun_prop
    exact this.aestronglyMeasurable
  have hbd : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖Real.exp (-(ω * τ))‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_)
    have hτ' : (0 : ℝ) < τ := hτ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  refine IntegrableOn.congr_fun (Integrable.bdd_mul hR hm hbd) (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), (3.50)–(3.51), p. 78: with `ω ≥ 0`, inflation discounted at `r + ω` is
integrable (shifted form): `π = (R^n − r) − (R^n − π − r)`. -/
theorem eqm_int_infl {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ} (hω : 0 ≤ ω)
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * infl (t + τ)) (Set.Ioi 0) := by
  have hN := integrableOn_shift_weighted (g := fun τ => Rn τ - r) E.intN
  refine IntegrableOn.congr_fun (hN.sub (eqm_int_real_bond hω E)) (fun τ _ => ?_)
    measurableSet_Ioi
  simp only [Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 77: `Δ_t dv_t = Δ_t dR^n_t`: with the real face value predetermined
(`B` predetermined, no price-level jump), the news-date jump in the value of debt equals the
jump in the bond price, i.e. the unexpected bond return (`news_return_tendsto`). -/
theorem news_value_eq_bond {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    v₁ t - v₀ t = q₁ t - q₀ t := by
  rw [E₁.value, E₀.value, hb]; ring

/-- Cochrane (2023), (3.46), p. 77: **the value news identity.** Between an old and a new
equilibrium that share the predetermined face value at `t`, the unexpected bond return
`Δq_t` equals the news in discounted surpluses minus the news in discounted real returns:
`Δq_t = ∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ`. -/
theorem news_value {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    q₁ t - q₀ t =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  rw [← news_value_eq_bond E₀ E₁ hb, eqm_value E₁, eqm_value E₀]
  have hS := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => s₁ (t + τ)) (c := fun τ => s₀ (t + τ)) (S := Set.Ioi 0)
    (integrableOn_shift_weighted E₁.intS) (integrableOn_shift_weighted E₀.intS)
  have hR := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => Rn₁ (t + τ) - infl₁ (t + τ) - r)
    (c := fun τ => Rn₀ (t + τ) - infl₀ (t + τ) - r) (S := Set.Ioi 0)
    (integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR)
    (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR)
  have hR' : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ) - r) - (Rn₀ (t + τ) - infl₀ (t + τ) - r)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  beta_reduce at hS hR
  linarith

/-- Cochrane (2023), (3.50), p. 78: **the bond-return news identity.**
`Δq_t = −∫_0^∞ e^{−(r+ω)τ}ΔR^n_{t+τ}dτ`. -/
theorem news_bond {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    q₁ t - q₀ t =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn₁ (t + τ) - Rn₀ (t + τ)) := by
  rw [eqm_bond E₁, eqm_bond E₀]
  have hN := integral_weighted_sub (w := fun τ => Real.exp (-((r + ω) * τ)))
    (a := fun τ => Rn₁ (t + τ) - r) (c := fun τ => Rn₀ (t + τ) - r) (S := Set.Ioi 0)
    (integrableOn_shift_weighted (g := fun τ => Rn₁ τ - r) E₁.intN)
    (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - r) E₀.intN)
  have hN' : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
      ((Rn₁ (t + τ) - r) - (Rn₀ (t + τ) - r)) =
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn₁ (t + τ) - Rn₀ (t + τ)) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  beta_reduce at hN
  linarith

/-- Cochrane (2023), (3.50), p. 78: the second form,
`Δq_t = −∫_0^∞ e^{−(r+ω)τ}(ΔR'_{t+τ} + Δπ_{t+τ})dτ` (`dR^n = dR + π dt`). -/
theorem news_bond_real {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    q₁ t - q₀ t =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) +
          (infl₁ (t + τ) - infl₀ (t + τ))) := by
  rw [news_bond E₀ E₁]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), (3.51), p. 78: **the weighted-inflation identity.** For `ω ≥ 0`,
`∫_0^∞ e^{−(r+ω)τ}Δπ_{t+τ}dτ = −∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ
  + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})ΔR'_{t+τ}dτ`. -/
theorem news_weighted_inflation {r ω t : ℝ}
    {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ} (hω : 0 ≤ ω)
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  have hV := news_value E₀ E₁ hb
  have hB := news_bond_real E₀ E₁
  -- integrability of the shifted pieces
  have iR : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR).sub
        (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iM : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((eqm_int_real_bond hω E₁).sub (eqm_int_real_bond hω E₀)) (fun τ _ => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iP : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      (infl₁ (t + τ) - infl₀ (t + τ))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun ((eqm_int_infl hω E₁).sub (eqm_int_infl hω E₀))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hsplitB : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) +
          (infl₁ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) +
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) := by
    rw [← integral_add iM iP]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have hsplitW : ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) -
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    rw [← integral_sub iR iM]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [hsplitW]
  rw [hsplitB] at hB
  linarith

/-- Cochrane (2023), pp. 78–79: if the bond price does not move at the news date (`Δq_t = 0`, as
for instantaneous debt, whose value is pinned at par), any fiscal news is exactly matched by
news in discounted real returns:
`∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ = ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ`. -/
theorem short_debt_news {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) (hq : q₁ t = q₀ t) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  have := news_value E₀ E₁ hb
  rw [hq, sub_self] at this
  linarith

/-! ## Short-term debt is `ω → ∞`, not `ω = 0` (E20) -/

/-- Cochrane (2023), (3.51), p. 78: a measurable inflation news path bounded by `K` on `(0, ∞)`
gives a genuinely integrable left-hand side of (3.51) whenever `r + ω > 0`. -/
theorem short_limit_integrable {dπ : ℝ → ℝ} {r ω K : ℝ} (h : 0 < r + ω)
    (hm : AEStronglyMeasurable dπ (volume.restrict (Set.Ioi 0)))
    (hb : ∀ τ, 0 < τ → |dπ τ| ≤ K) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * dπ τ) (Set.Ioi 0) := by
  have hint := (integrableOn_exp_mul_Ioi (a := -(r + ω)) (by linarith) 0).const_mul K
  have hc : Continuous fun τ : ℝ => Real.exp (-((r + ω) * τ)) := by fun_prop
  refine Integrable.mono' hint (hc.aestronglyMeasurable.mul hm)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le

/-- Cochrane (2023), pp. 78–79 (E20): **the short-debt limit.** For a family of inflation news
paths uniformly bounded by `K` on `(0, ∞)`, the left-hand side of (3.51),
`∫_0^∞ e^{−(r+ω)τ}Δπ^ω_τ dτ`, tends to `0` as `ω → ∞` (instantaneous debt). -/
theorem short_limit {dπ : ℝ → ℝ → ℝ} {r K : ℝ}
    (hb : ∀ ω τ, 0 < τ → |dπ ω τ| ≤ K) :
    Tendsto (fun ω => ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ) atTop (𝓝 0) := by
  have hK : Tendsto (fun ω : ℝ => K / (r + ω)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ r tendsto_id)
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_gt_atTop (-r)] with ω hω
  have ha : 0 < r + ω := by linarith
  have hint := (integrableOn_exp_mul_Ioi (a := -(r + ω)) (by linarith) 0).const_mul K
  have hbound : ‖∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ‖ ≤
      ∫ τ in Set.Ioi 0, K * Real.exp (-(r + ω) * τ) := by
    refine norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm K]
    exact mul_le_mul_of_nonneg_left (hb ω τ hτ) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
  simp only [mul_zero, Real.exp_zero] at hbound
  have hval : K * (-1 / -(r + ω)) = K / (r + ω) := by field_simp
  rw [hval] at hbound
  exact hbound

/-- Cochrane (2023), pp. 78–79 (E20): the single-path version: for bounded measurable inflation
news, `∫_0^∞ e^{−(r+ω)τ}Δπ_τ dτ → 0` as `ω → ∞`. -/
theorem short_limit_single {dπ : ℝ → ℝ} {r K : ℝ} (hb : ∀ τ, 0 < τ → |dπ τ| ≤ K) :
    Tendsto (fun ω => ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ τ) atTop (𝓝 0) :=
  short_limit (dπ := fun _ => dπ) (fun _ => hb)

/-- Cochrane (2023), pp. 78–79 (E20): in the limit `ω → ∞` the weighted-inflation identity
(3.51) becomes `∫_0^∞ e^{−rτ}Δs̃_τ dτ = ∫_0^∞ e^{−rτ}ΔR'_τ dτ`: if (3.51) holds for all large `ω`
with inflation news uniformly bounded, the fiscal news equals the discount-rate news. -/
theorem short_debt_limit_identity {dπ : ℝ → ℝ → ℝ} {ds dR : ℝ → ℝ} {r K : ℝ}
    (hb : ∀ ω τ, 0 < τ → |dπ ω τ| ≤ K)
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * dR τ) (Set.Ioi 0))
    (hid : ∀ᶠ ω in atTop, ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * dR τ := by
  set A := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ
  set B := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * dR τ
  have hL := short_limit (r := r) hb
  have hconv : ∀ ω τ, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ =
      (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ) := by
    intro ω τ
    have : Real.exp (-((r + ω) * τ)) = Real.exp (-(ω * τ)) * Real.exp (-(r * τ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hD : Tendsto (fun ω => ∫ τ in Set.Ioi 0,
      (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ)) atTop (𝓝 B) := by
    have hlim : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), Tendsto (fun ω =>
        (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ)) atTop
        (𝓝 (Real.exp (-(r * τ)) * dR τ)) := by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_)
      have he : Tendsto (fun ω => Real.exp (-(ω * τ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hτ)
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).mul_const
        (Real.exp (-(r * τ)) * dR τ)
      simpa using this
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => ‖Real.exp (-(r * τ)) * dR τ‖) ?_ ?_ hR.norm hlim
    · refine Eventually.of_forall fun ω => ?_
      have hc : Continuous fun τ : ℝ => 1 - Real.exp (-(ω * τ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hR.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 0] with ω hω
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_)
      rw [norm_mul]
      have h1 : ‖1 - Real.exp (-(ω * τ))‖ ≤ 1 := by
        have hpos := Real.exp_pos (-(ω * τ))
        have hle : Real.exp (-(ω * τ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      calc ‖1 - Real.exp (-(ω * τ))‖ * ‖Real.exp (-(r * τ)) * dR τ‖
          ≤ 1 * ‖Real.exp (-(r * τ)) * dR τ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖Real.exp (-(r * τ)) * dR τ‖ := one_mul _
  have hR' : Tendsto (fun ω => -A + ∫ τ in Set.Ioi 0,
      (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ) atTop (𝓝 (-A + B)) := by
    refine (hD.const_add (-A)).congr fun ω => ?_
    congr 1
    exact integral_congr_ae (ae_of_all _ fun τ => (hconv ω τ).symm)
  have hL' := hL.congr' (hid.mono fun ω h => h)
  have := tendsto_nhds_unique hL' hR'
  linarith

/-- Cochrane (2023), pp. 78–79 (E20): at `ω = 0` (a perpetuity, coupons `e^{−0·τ} = 1`, price
`1/y`) the left-hand side of (3.51) is **not** zero in general: for `Δπ ≡ 1` it equals
`1/r ≠ 0`. -/
theorem perpetuity_lhs_ne_zero {r : ℝ} (hr : 0 < r) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) = 1 / r ∧
      ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) ≠ 0 := by
  have hI := integral_exp_mul_Ioi (a := -r) (by linarith) 0
  have h : ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) = 1 / r := by
    have : ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) =
        ∫ τ in Set.Ioi 0, Real.exp (-r * τ) := by
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only [add_zero, mul_one, neg_mul]
    rw [this, hI]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  refine ⟨h, ?_⟩
  rw [h]
  exact (one_div_pos.2 hr).ne'

/-- Cochrane (2023), p. 77 and A1 p. 560: `ω = 0` is the perpetuity: the bond price is `1/y`. -/
theorem perpetuity_price {y : ℝ} (hy : 0 < y) :
    ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(0 * τ)) = 1 / y := by
  have := bond_price_yield (ω := 0) (y := y) (by linarith)
  rwa [zero_add] at this

/-- Cochrane (2023), p. 77 and A1 p. 560: `ω → ∞` is instantaneous debt: the bond price
`1/(ω + y) → 0` while the value of the coupon stream per unit of price, `ω/(ω + y)`, tends to `1`
(the bond matures instantly). -/
theorem instantaneous_limit (y : ℝ) :
    Tendsto (fun ω : ℝ => 1 / (ω + y)) atTop (𝓝 0) ∧
      Tendsto (fun ω : ℝ => ω / (ω + y)) atTop (𝓝 1) := by
  have hT : Tendsto (fun ω : ℝ => ω + y) atTop atTop := tendsto_atTop_add_const_right _ y tendsto_id
  have h1 : Tendsto (fun ω : ℝ => 1 / (ω + y)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hT
  refine ⟨h1, ?_⟩
  have h2 : Tendsto (fun ω : ℝ => 1 - y * (1 / (ω + y))) atTop (𝓝 1) := by
    simpa using (h1.const_mul y).const_sub 1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (-y)] with ω hω
  have : ω + y ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), p. 78: inflation news at the single instant `t` contributes nothing to the
left-hand side of (3.51): changing `Δπ` at one date leaves the integral unchanged. -/
theorem lhs_ignores_one_date {dπ dπ' : ℝ → ℝ} {r ω τ₀ : ℝ} (h : ∀ τ, τ ≠ τ₀ → dπ' τ = dπ τ) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ' τ =
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ τ := by
  have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ τ₀ := by
    rw [ae_iff]
    simp
  refine integral_congr_ae (ae_restrict_of_ae (hne.mono fun τ hτ => ?_))
  simp only [h τ hτ]

end Cochrane.Generality.ContinuousLinear

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.4, pp. 79–80, and
Online Appendix A1.6, pp. 567–569.

Deterministic paths. Nominal debt `B` and money `M` are differentiable with derivatives `dB`,
`dM`; the nominal flow condition (3.52)/(1.31) is `dM = iB + i^m M − Ps − dB`. Discounting uses a
*nominal* discount factor `N = Λ/P` with `N' = −iN` (the definition of the nominal rate, A1
(1.26)); the real discount factor is `Λ = NP`. The price level need not be differentiable: only
`N` (or `PW`) is, as A1 p. 568 remarks.

* (3.52)/(1.31) in real terms.
* (1.32)–(1.33), (3.53): `B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ` **iff** the TVC
  `Λ_T B_T/P_T → 0` (`i^m = 0`).
* (1.34), (3.54): `(M_t + B_t)/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` iff the TVC on
  `M + B`.
* The two are equivalent iff the money TVC `Λ_T M_T/P_T → 0` holds; an explicit path satisfies
  (3.53) but not (3.54).
* (1.35)–(1.36): ex-post discounting with the cumulative return `W` (`(PW)' = i PW`),
  `B/P = ∫ (W_t/W_τ)(s + dM/P)` and `(B+M)/P = ∫ (W_t/W_τ)(s + (i_τ − i^m_τ)M_τ/P_τ)`; with the
  printed index `(i_t − i^m_t)` (E21) the formula is false (explicit counterexample).
* (1.37), (3.55): with the mixed portfolio return `W^m`, `(B+M)/P = ∫ (W^m_t/W^m_τ) s dτ`.
-/

namespace Cochrane.Generality.ContinuousMoney

open Filter Topology MeasureTheory
open Cochrane.Generality.ContinuousLinear

/-! ## The flow condition and discount factors -/

/-- Cochrane (2023), (3.52), p. 79 and A1 (1.31), p. 567: the nominal flow condition
`dM = iB + i^m M − Ps − dB` in real terms:
`(B/P) i + (M/P) i^m = s + dB/P + dM/P`. -/
theorem flow_real {B M P s i im dB dM : ℝ} (hP : P ≠ 0)
    (hflow : dM = i * B + im * M - P * s - dB) :
    B / P * i + M / P * im = s + dB / P + dM / P := by
  rw [hflow]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.26), p. 564: with a real discount factor `Λ' = −rΛ` and inflation
`P' = πP`, the nominal discount factor `Λ/P` obeys `(Λ/P)' = −(r + π)(Λ/P)`: the nominal rate is
`i = r + π`. (The constant-rate case of `ContinuousShort.hasDerivAt_nominal_discount`.) -/
theorem nominal_discount_of_real {Λ P : ℝ → ℝ} {r infl τ : ℝ}
    (hΛ : HasDerivAt Λ (-r * Λ τ) τ) (hP : HasDerivAt P (infl * P τ) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => Λ u / P u) (-(r + infl) * (Λ τ / P τ)) τ :=
  ContinuousShort.hasDerivAt_nominal_discount (i := fun _ => r + infl)
    (hΛ.congr_deriv (by field_simp; ring)) hP hPτ

/-- Cochrane (2023), A1 (1.35), p. 568: if the nominal value of the short-term bond portfolio
`X = PW` grows at `i` (`X' = iX`), then `1/(PW)` is a nominal discount factor:
`(1/X)' = −i (1/X)` (`ContinuousShort.hasDerivAt_inv_price` with `X' = iX`). -/
theorem inv_nominal_value {X : ℝ → ℝ} {i τ : ℝ} (hX : HasDerivAt X (i * X τ) τ) (hXτ : X τ ≠ 0) :
    HasDerivAt (fun u => 1 / X u) (-i * (1 / X τ)) τ :=
  (ContinuousShort.hasDerivAt_inv_price hX hXτ).congr_deriv (by field_simp)

/-- Cochrane (2023), A1 p. 568: with `Λ = NP` and `N = 1/(PW)`, `Λ_τ/Λ_t = W_t/W_τ`. -/
theorem lambda_ratio_eq_W {P W : ℝ → ℝ} {t τ : ℝ} (hPt : P t ≠ 0) (hPτ : P τ ≠ 0)
    (hWt : W t ≠ 0) (hWτ : W τ ≠ 0) :
    (1 / (P τ * W τ) * P τ) / (1 / (P t * W t) * P t) = W t / W τ := by
  field_simp

/-- Cochrane (2023), (3.31), A1.6, pp. 74, 567: the forward-integration step in "iff" form:
if `G' = −h` on `[t, ∞)` and `h` is integrable on `(t, ∞)`, then `G_T → 0` iff
`G_t = ∫_t^∞ h`. -/
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

/-- Cochrane (2023), (3.53), A1 (1.33): converting `N_t X_t = ∫_t^∞ Λ f` (with `Λ = NP`) into
`X_t/P_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
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

/-! ## (3.53): seigniorage as money creation -/

/-- Cochrane (2023), A1 (1.32), p. 567: with `i^m = 0`, along the flow condition the discounted
real debt obeys `d(N B) = −N P (s + dM/P) dt`. -/
theorem printing_hasDerivAt {N B P s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * B u) (-(N τ * P τ * (s τ + dM τ / P τ))) τ :=
  (hN.mul hB).congr_deriv (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), (3.53), p. 79 and A1 (1.33), p. 567: **seigniorage as money creation.**
With `i^m = 0`, nominal discount `N' = −iN` (`Λ = NP`), the flow (3.52) on `[t, ∞)` and
`Λ(s + dM/P)` integrable: the TVC `Λ_T B_T/P_T → 0` holds iff
`B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ`. -/
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

/-! ## (3.54): seigniorage as interest saving -/

/-- Cochrane (2023), A1 p. 567: along the flow (3.52) with interest on money,
`d(N(M + B)) = −N P (s + (i − i^m) M/P) dt`. -/
theorem interest_hasDerivAt {N B M P s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ)
    (hM : HasDerivAt M (dM τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * (M u + B u))
      (-(N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul (HasDerivAt.add hM hB)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), (3.54), p. 79 and A1 (1.34), p. 567: **seigniorage as interest saving.**
With money paying `i^m`, the TVC `Λ_T(M_T + B_T)/P_T → 0` holds iff
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

/-- Cochrane (2023), §3.6.4 and A1.6 (continuous analogue of E13): with `i^m = 0`, if the
money-creation valuation (3.53) holds, then the interest-saving valuation (3.54) holds **iff**
the money transversality condition `Λ_T M_T/P_T → 0` holds. -/
theorem printing_interest_iff_money_tvc {N B M P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint1 : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t))
    (hint2 : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - 0) * M τ / P τ)) (Set.Ioi t))
    (h353 : B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ)) :
    (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - 0) * M τ / P τ) ↔
      Tendsto (fun T => N T * M T) atTop (𝓝 0) := by
  have hBtvc := (money_printing_iff hN hNt hB hP hflow hint1).2 h353
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

/-- Cochrane (2023), §3.6.4 and A1.6 (E13 analogue): the two valuation equations are **not**
equivalent without the money TVC. With `P ≡ 1`, `i ≡ ι` (any `ι`, e.g. `ι > 0`), `i^m = 0`,
`N_τ = e^{−ιτ}`, no bonds, `M_τ = e^{ιτ}` and `s_τ = −ι e^{ιτ}` (money-financed deficits), the
flow (3.52) holds, the money-creation valuation (3.53) holds (`0 = 0`), but the interest-saving
valuation (3.54) fails (`e^{ιt} ≠ 0`). -/
theorem printing_without_interest_example (ι t : ℝ) :
    let N : ℝ → ℝ := fun τ => Real.exp (-(ι * τ))
    let M : ℝ → ℝ := fun τ => Real.exp (ι * τ)
    let s : ℝ → ℝ := fun τ => -(ι * Real.exp (ι * τ))
    (∀ τ, HasDerivAt N (-ι * N τ) τ) ∧ (∀ τ, HasDerivAt M (ι * M τ) τ) ∧
      (∀ τ, ι * M τ = ι * 0 + 0 * M τ - 1 * s τ - 0) ∧
      (0 : ℝ) / 1 = ∫ τ in Set.Ioi t, N τ * 1 / (N t * 1) * (s τ + ι * M τ / 1) ∧
      (M t + 0) / 1 ≠ ∫ τ in Set.Ioi t, N τ * 1 / (N t * 1) * (s τ + (ι - 0) * M τ / 1) := by
  intro N M s
  have hzero : ∀ τ, s τ + ι * M τ / 1 = 0 := fun τ => by simp only [s, M]; ring
  have hzero' : ∀ τ, s τ + (ι - 0) * M τ / 1 = 0 := fun τ => by simp only [s, M]; ring
  refine ⟨fun τ => hasDerivAt_expDisc ι τ, fun τ => ?_, fun τ => by simp only [s]; ring,
    ?_, ?_⟩
  · exact (HasDerivAt.exp ((hasDerivAt_id' τ).const_mul ι)).congr_deriv (by simp only [M]; ring)
  · simp only [hzero, mul_zero, integral_zero]
    norm_num
  · simp only [hzero', mul_zero, integral_zero]
    simp only [M, add_zero, div_one]
    exact (Real.exp_pos _).ne'

/-! ## (1.35)–(1.36): ex-post discounting with the cumulative return `W` -/

/-- Cochrane (2023), A1 (1.36), p. 568: with `i^m = 0`, if the nominal value `PW` of the
short-term bond portfolio grows at `i`, then `d(B/(PW)) = −(1/W)(s + dM/P) dt`; the price level
itself need not be differentiable. -/
theorem printing_W_hasDerivAt {P W B s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * B u) (-(1 / W τ * (s τ + dM τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul hB).congr_deriv
    (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), §3.6.4, p. 79 and A1 (1.36), p. 568: **ex-post discounting, money
creation.** With `(PW)' = i PW`, `i^m = 0`, the flow (3.52) and `(s + dM/P)/W` integrable, the TVC
`B_T/(P_T W_T) → 0` holds iff `B_t/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + dM_τ/P_τ) dτ`. -/
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

/-- Cochrane (2023), A1 p. 568: along the flow with interest on money,
`d((B + M)/(PW)) = −(1/W)(s + (i − i^m)M/P) dt`. -/
theorem interest_W_hasDerivAt {P W B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * (B u + M u))
      (-(1 / W τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), §3.6.4, p. 79 and A1 p. 568: **ex-post discounting, interest saving.**
The TVC `(B_T + M_T)/(P_T W_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` (integrand dated `τ`; the book
prints `(i_t − i^m_t)`, E21, see `printed_index_counterexample`). -/
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

/-- Cochrane (2023), p. 79 and A1 p. 568 (E21): the printed integrand `(i_t − i^m_t)M_τ/P_τ`
(rate dated `t`) is wrong. With `P ≡ 1`, `i ≡ 1`, `W_τ = e^τ`, `B ≡ 0`, `M ≡ 1`, `i^m_τ = e^{−τ}`
and `s = i^m` the flow (3.52) holds, `(B_0 + M_0)/P_0 = 1` equals the correctly dated integral,
while the printed one equals `1/2`. -/
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

/-! ## (1.37), (3.55): the mixed bond-and-money portfolio return -/

/-- Cochrane (2023), (3.55), p. 80 and A1 (1.37), p. 569: if the nominal value `PW^m` of the
whole government portfolio grows at the mixed rate `(Bi + Mi^m)/(B + M)`, then along the flow
`d((B + M)/(PW^m)) = −(s/W^m) dt`. -/
theorem mixed_hasDerivAt {P Wm B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hPτ : P τ ≠ 0) (hWτ : Wm τ ≠ 0) (hBM : B τ + M τ ≠ 0)
    (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * Wm u) * (B u + M u)) (-(1 / Wm τ * s τ)) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), (3.55), p. 80 and A1 (1.37), p. 569: **valuation with the mixed portfolio
return.** With `(PW^m)' = ((Bi + Mi^m)/(B + M)) PW^m`, `B + M > 0`, the flow (3.52) and `s/W^m`
integrable, the TVC `(B_T + M_T)/(P_T W^m_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W^m_t/W^m_τ) s_τ dτ`: seigniorage is folded into the discount rate. -/
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

/-- Cochrane (2023), §3.6.4, p. 80: the mixed nominal return `(Bi + Mi^m)/(B + M)` lies below
the bond rate `i` when `i^m < i` and `M > 0`, `B ≥ 0`: money lets the government borrow at
lower rates. -/
theorem mixed_rate_lt {B M i im : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (him : im < i) :
    (B * i + M * im) / (B + M) < i := by
  have hpos : 0 < B + M := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

end Cochrane.Generality.ContinuousMoney

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the Chapter 3 developments

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, *Generality*, §§3.1–3.6
(pp. 53–80), and Online Appendix A1 (pp. 557–569). The chapter was formalised in four
independent chains (long-term debt and stochastic discounting; money and the log-linear
identities; continuous time with short and long debt; continuous linearised identities and
money). This module proves that their objects agree where the book talks about the same thing.

## Main results

* Discrete valuation machinery: the money chain's present-value relation and transversality
  condition (`Money.PVRel`, `Money.TVC`, levels of `Λ`) are the long-term-debt chain's
  `LongTermDebt.pv` and `LongTermDebt.TVC` with one-period factor `m_t = Λ_{t+1}/Λ_t`
  (`pvRel_iff_pv`, `tvc_money_iff_tvc`); the money chain's undiscounted recursion is
  `LongTermDebt.FlowRec` with `m ≡ 1` (`flowRec_one_iff`, `tvc_one_iff`).
* (3.5) with `Λ_t = βᵗ` is the constant-`β` valuation of (3.3) and Chapter 2 (`sdf_ratio_pow`,
  `pv_beta_pow`, `pv_lambda_beta`, `valuation_sdf_beta_iff`).
* Short-term debt as a special case: the geometric maturity structure with `ω = 0` is one-period
  debt, and `LongTermDebt.valuationGeom_iff` at `ω = 0` is exactly
  `StochasticDiscount.valuation_sdf_iff` (`annuity_zero`, `geomValue_zero`, `geomFlow_zero_iff`,
  `zeroPrice_one_eq_bondPrice`, `geomFlow_zero_iff_flowOne`, `valuationGeom_zero_iff`); in
  continuous time it is the limit `ϖ → ∞` (`short_debt_limits`), and the discrete jump ratio at
  `ω = e^{−ϖ}` has the same limit (`jumpRatio_tendsto_short`).
* Weights: the discrete (3.22) weights `ω̂ʲ`, `ρʲ` and the continuous (3.51) weights
  `e^{−(r+ϖ)τ}`, `e^{−rτ}` agree on the integer grid with `ω = e^{−ϖ}`, `1 + i = e^r`,
  `ρ = e^{−r}`, `ω̂ = ω/(1+i)` (`bond_coeff_exp`, `weights_322_351`, `omega_disc_endpoints`).
* Discretisation limits: with period length `h`, the discrete geometric annuity `h·(1+i)/(1+i−ω)`
  tends to the continuous bond price `1/(i+ϖ)` that solves `Q' = (i+ϖ)Q − 1`
  (`annuity_tendsto_bondPrice`), and the discrete jump ratio (1.16) tends to the continuous
  (1.18) `(r+ϖ)/(i+ϖ)` (`jumpRatio_tendsto_continuous`).
* E15 reconciled in one statement (`e15_reconciled`): exact proportional drop 3.41%, exact log
  drop in (3.46%, 3.48%), linear drop 4% with weight `ω`, 3.48% with the exact weight `ω/(1+i)`.
* Innovations: `Ratios.E_innov_zero` is `E_t ΔE_{t+1} = 0` for `LogLinearIdentities.innov`
  (`E_innov_eq_zero`); `LogLinearIdentities.geomQ` is `LongTermDebt.geom_value/(1+i)`
  (`geomQ_eq_geom_value_div`).
* Continuous engines: the general-discount-factor engine of `ContinuousLinear` applied to
  `Λ = ContinuousShort.disc r t` gives the valuation/TVC equivalence of `ContinuousShort` for
  every continuous rate (`hasDerivAt_disc_of_continuous`, `tvc_iff_pv_of_engine`); the constant-
  rate discount factors agree (`expDisc_ratio_eq_disc`).
* E13 in discrete and continuous time (`e13_discrete_and_continuous`).
* (3.26), p. 68, prints the scaled surplus `s̃` inside the nonlinear valuation equation; with
  `s̃ = κs` the printed equation is compatible with (3.3) only if `κ = 1` or the value of debt is
  zero (`eq_3_26_printed_iff`).
-/

namespace Cochrane.Generality.Links

open Filter Topology MeasureTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Discrete valuation machinery: `Money` versus `LongTermDebt` -/

/-- Cochrane (2023), (3.5) and (3.10)–(3.12), pp. 55–59: the money chain's present-value
relation `X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)d_{t+j}]` is the long-term-debt chain's present value
with one-period factor `m_s = Λ_{s+1}/Λ_s`. -/
theorem pvRel_iff_pv {Λ P X d : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0) (t : ℕ) (ω : Ω) :
    Money.PVRel 𝔼 Λ P X d t ω ↔
      X t ω / P t ω = LongTermDebt.pv 𝔼 (fun s ξ => Λ (s + 1) ξ / Λ s ξ) d t ω := by
  rw [StochasticDiscount.pv_lambda 𝔼 hΛ (fun _ => rfl) t]
  rfl

/-- Cochrane (2023), p. 55: under the money chain's standing assumptions, its transversality
condition `E_t[Λ_{t+T}X_{t+T}/P_{t+T}] → 0` (in every state) is the long-term-debt chain's
`E_t[(Λ_{t+T}/Λ_t)x_{t+T}] → 0` for the real value `x = X/P` and `m_s = Λ_{s+1}/Λ_s`. -/
theorem tvc_money_iff_tvc {Λ P i M B X : ℕ → Ω → ℝ} (hS : Money.Standing 𝔼 Λ P i M B)
    (t : ℕ) :
    (∀ ω, Money.TVC 𝔼 Λ P X t ω) ↔
      LongTermDebt.TVC 𝔼 (fun s ξ => Λ (s + 1) ξ / Λ s ξ) (fun s ξ => X s ξ / P s ξ) t := by
  have hΛ : ∀ s ξ, Λ s ξ ≠ 0 := fun s ξ => (hS.disc_pos s ξ).ne'
  have key : ∀ N ω, 𝔼.E t (LongTermDebt.sdf (fun s ξ => Λ (s + 1) ξ / Λ s ξ) t N *
      (fun s ξ => X s ξ / P s ξ) (t + N)) ω =
      (Λ t ω)⁻¹ * 𝔼.E t (fun ω' => Λ (t + N) ω' * (X (t + N) ω' / P (t + N) ω')) ω := by
    intro N ω
    rw [StochasticDiscount.sdf_eq_ratio hΛ (fun _ => rfl) t N]
    exact Money.E_ratio 𝔼 hS t N (fun s ξ => X s ξ / P s ξ) ω
  unfold LongTermDebt.TVC Money.TVC
  simp_rw [key]
  constructor
  · intro h ω
    simpa using (h ω).const_mul (Λ t ω)⁻¹
  · intro h ω
    simpa [mul_inv_cancel_left₀ (hΛ t ω)] using (h ω).const_mul (Λ t ω)

/-- Cochrane (2023), footnote 1, p. 58, and p. 55: the money chain's recursion
`Y_t = c_t + E_tY_{t+1}` (used in `Money.telescope`, `Money.pv_iff_tvc`) is the long-term-debt
flow condition `LongTermDebt.FlowRec` with the one-period factor `m ≡ 1`. -/
theorem flowRec_one_iff {Y c : ℕ → Ω → ℝ} :
    LongTermDebt.FlowRec 𝔼 (fun _ _ => 1) c Y ↔ ∀ t, Y t = c t + 𝔼.E t (Y (t + 1)) := by
  have h1 : ∀ x : Ω → ℝ, (fun _ : Ω => (1 : ℝ)) * x = x := fun x => funext fun _ => one_mul _
  simp only [LongTermDebt.FlowRec, h1]

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: with `m ≡ 1` the long-term-debt
transversality condition is the money chain's `E_tY_{t+T} → 0` (`Money.pv_iff_tvc`). -/
theorem tvc_one_iff {Y : ℕ → Ω → ℝ} (t : ℕ) :
    LongTermDebt.TVC 𝔼 (fun _ _ => 1) Y t ↔
      ∀ ω, Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop (𝓝 0) := by
  have h2 : ∀ x : Ω → ℝ, (fun _ : Ω => (1 : ℝ)) * x = x := fun x => funext fun _ => one_mul _
  simp only [LongTermDebt.TVC, LongTermDebt.sdf_const, one_pow, h2]

/-! ### (3.5) with `Λ_t = βᵗ`: the constant-`β` valuation -/

/-- Cochrane (2023), p. 55: with `Λ_t = βᵗ`, `β ≠ 0`, the one-period factor `Λ_{t+1}/Λ_t` is the
constant `β`. -/
theorem sdf_ratio_pow {β : ℝ} (hβ : β ≠ 0) :
    (fun s (_ : Ω) => β ^ (s + 1) / β ^ s) = fun _ _ => β := by
  funext s _
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), (3.5), p. 55, with `Λ_t = βᵗ`: the present value is (3.3)'s
`∑_n βⁿE_ts_{t+n}`. -/
theorem pv_beta_pow {β : ℝ} (hβ : β ≠ 0) (s : ℕ → Ω → ℝ) (t : ℕ) :
    LongTermDebt.pv 𝔼 (fun s (_ : Ω) => β ^ (s + 1) / β ^ s) s t =
      fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  rw [sdf_ratio_pow hβ]
  exact LongTermDebt.pv_const 𝔼 β s t

/-- Cochrane (2023), (3.5), p. 55, as printed with `Λ_t = βᵗ`:
`∑_j E_t[(β^{t+j}/βᵗ)s_{t+j}] = ∑_j βʲE_ts_{t+j}`, the right-hand side of (3.3) and (2.7). -/
theorem pv_lambda_beta {β : ℝ} (hβ : β ≠ 0) (s : ℕ → Ω → ℝ) (t : ℕ) :
    (fun ξ => ∑' j, 𝔼.E t (fun ξ' => β ^ (t + j) / β ^ t * s (t + j) ξ') ξ) =
      fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  have h := StochasticDiscount.pv_lambda 𝔼 (Λ := fun s (_ : Ω) => β ^ s)
    (m := fun s (_ : Ω) => β ^ (s + 1) / β ^ s) (s := s) (fun s _ => pow_ne_zero s hβ)
    (fun _ => rfl) t
  rw [← h]
  exact pv_beta_pow 𝔼 hβ s t

/-- Cochrane (2023), (3.5), p. 55, specialised to `Λ_t = βᵗ` (`m ≡ β`, `0 ≤ β`): the flow with
the bond price `Q_t = E_t[βP_t/P_{t+1}]` and the transversality condition at every date hold iff
`B_{t−1}/P_t = ∑_n βⁿE_ts_{t+n}` at every date — the constant-`β` valuation of (3.3)
(`LongTermDebt.valuationLT_iff_const`) and of Chapter 2 for one-period debt. -/
theorem valuation_sdf_beta_iff (hMC : LongTermDebt.MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {β : ℝ} (hβ : 0 ≤ β) {P s D : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hs : LongTermDebt.SurplusSummable 𝔼 (fun _ _ => β) s) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hD1 : ∀ t, 𝔼.E t (D (t + 1)) = D (t + 1))
    (hx : 𝔼.Adapted (StochasticDiscount.realDebt D P)) :
    ((∀ t, StochasticDiscount.FlowOne (StochasticDiscount.bondPrice 𝔼 (fun _ _ => β) P) P s D t)
        ∧ ∀ t, LongTermDebt.TVC 𝔼 (fun _ _ => β) (StochasticDiscount.realDebt D P) t) ↔
      ∀ t, StochasticDiscount.realDebt D P t = fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  rw [StochasticDiscount.valuation_sdf_iff 𝔼 hMC hP (fun s => 𝔼.const (s + 1) β)
    (fun _ _ => hβ) hsa hs hPa hP0 hD1 hx]
  simp only [LongTermDebt.pv_const]

/-! ### Short-term debt as the `ω = 0` case of geometric debt -/

/-- Cochrane (2023), A1 (1.14), p. 559: with `ω = 0` the geometric portfolio is the maturing
bond only, `∑_j 0ʲQ_t^{(t+j)} = Q_t^{(t)}`. -/
theorem annuity_zero (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : LongTermDebt.annuity 0 Q t = Q t 0 := by
  funext ξ
  simp only [LongTermDebt.annuity]
  rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
  simp

/-- Cochrane (2023), A1 p. 559 and (3.1): with `ω = 0` and bonds priced by (3.1)
(`Q_t^{(t)} = 1`), the real value of geometric debt is `b_t/P_t`, the real value of one-period
debt of Chapter 2. -/
theorem geomValue_zero {m P b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    LongTermDebt.geomValue 0 Q b P t = StochasticDiscount.realDebt b P t := by
  funext ξ
  simp only [LongTermDebt.geomValue, annuity_zero, LongTermDebt.zeroPrice_zero 𝔼 hQ (hP0 t),
    StochasticDiscount.realDebt, Pi.one_apply, one_mul]

/-- Cochrane (2023), (3.2), p. 53, with the geometric structure at `ω = 0`: the flow is the
one-period flow `b_t = P_ts_t + Q_t^{(t+1)}b_{t+1}`. -/
theorem geomFlow_zero_iff {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (t : ℕ) :
    LongTermDebt.GeomFlow 0 P s b Q t ↔ ∀ ξ, b t ξ = P t ξ * s t ξ + Q t 1 ξ * b (t + 1) ξ := by
  have h : ∀ ξ, ∑' j, Q t (j + 1) ξ * ((0 : ℝ) ^ j * b (t + 1) ξ - 0 ^ (j + 1) * b t ξ) =
      Q t 1 ξ * b (t + 1) ξ := by
    intro ξ
    rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  simp only [LongTermDebt.GeomFlow, h]

/-- Cochrane (2023), (3.1) and p. 55: the price of the bond maturing next period is the
one-period bond price, `Q_t^{(t+1)} = E_t[m_tP_t/P_{t+1}]`. -/
theorem zeroPrice_one_eq_bondPrice {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q) (t : ℕ) :
    Q t 1 = StochasticDiscount.bondPrice 𝔼 m P t := by
  rw [hQ t 1, LongTermDebt.sdf_one]
  rfl

/-- Cochrane (2023), (3.2), p. 53, and §3.3, p. 55: for `ω = 0`, the geometric flow is the
one-period flow `B_{t−1}/P_t = s_t + Q_tB_t/P_t` of `StochasticDiscount.FlowOne`. -/
theorem geomFlow_zero_iff_flowOne {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    LongTermDebt.GeomFlow 0 P s b Q t ↔ StochasticDiscount.FlowOne (fun t => Q t 1) P s b t := by
  rw [geomFlow_zero_iff]
  unfold StochasticDiscount.FlowOne
  refine forall_congr' fun ξ => ?_
  have hp := hP0 t ξ
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    field_simp at h
    linarith

/-- Cochrane (2023), (3.1)–(3.3), p. 53, and (3.5), p. 55: **short-term debt is the `ω = 0`
case.** The geometric-maturity valuation theorem `LongTermDebt.valuationGeom_iff` at `ω = 0` is
exactly the one-period stochastic-discount valuation theorem
`StochasticDiscount.valuation_sdf_iff`: flow with `Q_t = E_t[m_tP_t/P_{t+1}]` plus TVC at every
date iff `B_{t−1}/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` at every date. -/
theorem valuationGeom_zero_iff (hMC : LongTermDebt.MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s)
    (hs : LongTermDebt.SurplusSummable 𝔼 m s) (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hb : 𝔼.Adapted b) (hb1 : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) :
    ((∀ t, StochasticDiscount.FlowOne (StochasticDiscount.bondPrice 𝔼 m P) P s b t) ∧
        ∀ t, LongTermDebt.TVC 𝔼 m (StochasticDiscount.realDebt b P) t) ↔
      ∀ t, StochasticDiscount.realDebt b P t = LongTermDebt.pv 𝔼 m s t := by
  have hP0 : ∀ s ξ, P s ξ ≠ 0 := fun s ξ => (hPpos s ξ).ne'
  have hQs : ∀ t ξ, Summable fun j => (0 : ℝ) ^ j * Q t j ξ := fun t ξ =>
    (hasSum_single 0 fun j hj => by simp [zero_pow hj]).summable
  have h := LongTermDebt.valuationGeom_iff 𝔼 hMC hP le_rfl hm hm0 hsa hs hQ hPa hPpos hQs hb hb1
  have hv : LongTermDebt.geomValue 0 Q b P = StochasticDiscount.realDebt b P :=
    funext (geomValue_zero 𝔼 hQ hP0)
  have hQ1 : (fun t => Q t 1) = StochasticDiscount.bondPrice 𝔼 m P :=
    funext (zeroPrice_one_eq_bondPrice 𝔼 hQ)
  rw [hv] at h
  simp only [geomFlow_zero_iff_flowOne hP0, hQ1] at h
  exact h

/-- Cochrane (2023), A1 p. 560 ("`ϖ = ∞` is instantaneous debt") and E20, discrete and
continuous: with discrete geometric decay `ω = e^{−ϖ}`, the exact discrete jump ratio (1.16)
tends to `1` as `ϖ → ∞` (its value at `ω = 0`, `LongTermDebt.price_jump_omega_zero`). -/
theorem jumpRatio_tendsto_short {r i : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) :
    Tendsto (fun ϖ : ℝ => LongTermDebt.jumpRatio r i (Real.exp (-ϖ))) atTop (𝓝 1) := by
  have he : Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hc : ContinuousAt (fun w => LongTermDebt.jumpRatio r i w) 0 := by
    unfold LongTermDebt.jumpRatio
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero hr.ne' (by rw [sub_zero]; exact hi.ne'))
  have h := hc.tendsto.comp he
  rwa [LongTermDebt.price_jump_omega_zero hr hi] at h

/-- Cochrane (2023), A1 pp. 559–560 and pp. 78–79 (E20): short-term debt is `ω = 0` in discrete
time and `ϖ → ∞` in continuous time. In continuous time the book-normalised bundle value
`ϖQ = ϖ/(i₀ + ϖ)` tends to `1` (`ContinuousLong.bondPrice`) and the jump ratio
`(r+ϖ)/(i+ϖ)` of (1.18) tends to `1`; the discrete decay `e^{−ϖ}` tends to `0` and the discrete
jump ratio is `1` at `ω = 0`. -/
theorem short_debt_limits {r i i₀ : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) (t : ℝ) :
    Tendsto (fun ϖ : ℝ => ϖ * ContinuousLong.bondPrice (fun _ => i₀) ϖ t) atTop (𝓝 1) ∧
      Tendsto (fun ϖ : ℝ => (r + ϖ) / (i + ϖ)) atTop (𝓝 1) ∧
      Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) ∧
      LongTermDebt.jumpRatio r i 0 = 1 := by
  refine ⟨?_, ContinuousLong.price_jump_tendsto_one r i, Real.tendsto_exp_neg_atTop_nhds_zero,
    LongTermDebt.price_jump_omega_zero hr hi⟩
  refine (ContinuousLong.tendsto_book_bondValue i₀).congr' ?_
  filter_upwards [eventually_gt_atTop (-i₀)] with ϖ hϖ
  rw [ContinuousLong.bondPrice_const (by linarith) t]

/-! ### Discrete (3.22) and continuous (3.51) weights -/

/-- Cochrane (2023), A1 (1.22), p. 563, and (3.47), p. 77: with discrete decay `ω = e^{−ϖ}` and
a steady-state nominal rate `1 + i = e^r` (no inflation), the exact discrete coefficient
`ω̂ = ω/(1+i)` is the continuous `e^{−(r+ϖ)}`. -/
theorem bond_coeff_exp (r ϖ : ℝ) : Real.exp (-ϖ) / Real.exp r = Real.exp (-(r + ϖ)) := by
  rw [← Real.exp_sub]
  ring_nf

/-- Cochrane (2023), (3.22), p. 65, and (3.51), p. 78: on the integer grid the discrete weights
agree with the continuous ones under `ω̂ = e^{−ϖ}/e^r` and `ρ = e^{−r}` (the log-linear `ρ` of
`LogLinearIdentities.rho_eq` with no growth): the inflation weight `ω̂ʲ = e^{−(r+ϖ)j}`, the
surplus weight `ρʲ = e^{−rj}`, and the discount-rate weight
`ρ^{j+1} − ω̂^{j+1} = e^{−r(j+1)} − e^{−(r+ϖ)(j+1)}`. -/
theorem weights_322_351 (r ϖ : ℝ) (j : ℕ) :
    (Real.exp (-ϖ) / Real.exp r) ^ j = Real.exp (-((r + ϖ) * j)) ∧
      Real.exp (-r) ^ j = Real.exp (-(r * j)) ∧
      Real.exp (-r) ^ (j + 1) - (Real.exp (-ϖ) / Real.exp r) ^ (j + 1) =
        Real.exp (-(r * ((j + 1 : ℕ) : ℝ))) - Real.exp (-((r + ϖ) * ((j + 1 : ℕ) : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bond_coeff_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  · rw [← Real.exp_nat_mul]
    congr 1
    ring
  · rw [bond_coeff_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 2 <;> ring

/-- Cochrane (2023), A1 p. 560 and E20: under `ω = e^{−ϖ}` the perpetuity `ϖ = 0` is `ω = 1`,
short-term debt `ϖ → ∞` is `ω → 0`, and `ω̂ = e^{−(r+ϖ)} → 0` as well. -/
theorem omega_disc_endpoints (r : ℝ) :
    Real.exp (-(0 : ℝ)) = 1 ∧ Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) ∧
      Tendsto (fun ϖ : ℝ => Real.exp (-ϖ) / Real.exp r) atTop (𝓝 0) := by
  refine ⟨by simp, Real.tendsto_exp_neg_atTop_nhds_zero, ?_⟩
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero.div_const (Real.exp r)

/-! ### Discretisation limits: annuity and jump ratio -/

/-- Cochrane (2023), §3.6.2 and A1.2.1 (auxiliary): `(e^{ah} − e^{bh})/h → a − b` as `h → 0`. -/
theorem tendsto_slope_exp_sub (a b : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (a * h) - Real.exp (b * h)) / h) (𝓝[≠] 0) (𝓝 (a - b)) := by
  have ha : HasDerivAt (fun h : ℝ => Real.exp (a * h)) a 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul a).exp).congr_deriv (by simp)
  have hb : HasDerivAt (fun h : ℝ => Real.exp (b * h)) b 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul b).exp).congr_deriv (by simp)
  have h := (HasDerivAt.sub ha hb).tendsto_slope_zero
  simpa [div_eq_inv_mul] using h

/-- Cochrane (2023), A1 (1.14), p. 559, and (3.47)/A1 (1.17), pp. 77, 560: **the discrete
geometric annuity converges to the continuous bond price.** With period length `h > 0`,
per-period gross rate `1 + i_h = e^{ih}` and decay `ω_h = e^{−ϖh}`, the value of the geometric
portfolio per unit of coupon flow, `h·∑_j ω_hʲ/(1+i_h)ʲ = h(1+i_h)/(1+i_h−ω_h)`
(`LongTermDebt.geom_value`), tends to `ContinuousLong.bondPrice = 1/(i+ϖ)`, the solution of
`Q' = (i+ϖ)Q − 1`, as `h → 0`. -/
theorem annuity_tendsto_bondPrice {i ϖ : ℝ} (hiϖ : 0 < i + ϖ) (t : ℝ) :
    Tendsto (fun h : ℝ => h * ∑' j : ℕ, Real.exp (-ϖ * h) ^ j / Real.exp (i * h) ^ j)
      (𝓝[>] 0) (𝓝 (ContinuousLong.bondPrice (fun _ => i) ϖ t)) := by
  rw [ContinuousLong.bondPrice_const hiϖ t]
  have hs := (tendsto_slope_exp_sub i (-ϖ)).mono_left
    (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  have hex : Tendsto (fun h : ℝ => Real.exp (i * h)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun h : ℝ => Real.exp (i * h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := hex.div hs (by rw [sub_neg_eq_add]; exact hiϖ.ne')
  rw [sub_neg_eq_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hlt : Real.exp (-ϖ * h) < 1 + (Real.exp (i * h) - 1) := by
    rw [add_sub_cancel]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos hiϖ hh'])
  have g := LongTermDebt.geom_value (Real.exp_pos (-ϖ * h)).le hlt
  rw [add_sub_cancel] at g
  rw [g.tsum_eq]
  change Real.exp (i * h) / ((Real.exp (i * h) - Real.exp (-ϖ * h)) / h) =
    h * (Real.exp (i * h) / (Real.exp (i * h) - Real.exp (-ϖ * h)))
  rw [div_div_eq_mul_div]
  ring

/-- Cochrane (2023), A1 (1.16), p. 559, and (1.18), p. 560: **the discrete jump ratio converges
to the continuous one.** With period length `h`, `1 + r_h = e^{rh}`, `1 + i_h = e^{ih}` and
`ω_h = e^{−ϖh}`, the exact discrete ratio `LongTermDebt.jumpRatio r_h i_h ω_h` tends to
`(r+ϖ)/(i+ϖ)`, the continuous ratio of `ContinuousLong.price_jump_permanent`, as `h → 0`. -/
theorem jumpRatio_tendsto_continuous {r i ϖ : ℝ} (hiϖ : i + ϖ ≠ 0) :
    Tendsto (fun h : ℝ => LongTermDebt.jumpRatio (Real.exp (r * h) - 1) (Real.exp (i * h) - 1)
      (Real.exp (-ϖ * h))) (𝓝[≠] 0) (𝓝 ((r + ϖ) / (i + ϖ))) := by
  have hexp : ∀ c : ℝ, Tendsto (fun h : ℝ => Real.exp (c * h)) (𝓝[≠] 0) (𝓝 1) := fun c => by
    have hc : Continuous fun h : ℝ => Real.exp (c * h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnum := (hexp i).mul (tendsto_slope_exp_sub r (-ϖ))
  have hden := (hexp r).mul (tendsto_slope_exp_sub i (-ϖ))
  have hlim := hnum.div hden (by rw [one_mul, sub_neg_eq_add]; exact hiϖ)
  rw [one_mul, one_mul, sub_neg_eq_add, sub_neg_eq_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := hh
  have e1 : ∀ x : ℝ, 1 + (x - 1) = x := fun x => by ring
  simp only [Pi.div_apply, LongTermDebt.jumpRatio, e1]
  rw [mul_div_assoc', mul_div_assoc', div_div_div_cancel_right₀ hh']

/-! ### E15 reconciled -/

/-- Cochrane (2023), A1 p. 560 and Figure 3.1, p. 69 (survey E15), one consistent statement set
at the figure's `r = 2%`, `i = 3%`, `ω = 0.8`: the exact proportional drop `1 − P_0/P` is
`40/1173 ∈ (3.41%, 3.42%)`; the exact log drop `−log(P_0/P)` is in `(3.46%, 3.48%)` (the text's
"3.5%"); the linear drop is `ω/(1−ω) = 4` (percent, Figure 3.1) with the printed weight `ω` and
`ω̂/(1−ω̂) = 80/23 ∈ (3.47, 3.48)` with the exact first-order weight `ω̂ = ω/(1+i)`. -/
theorem e15_reconciled :
    1 - LongTermDebt.jumpRatio 0.02 0.03 0.8 = 40 / 1173 ∧ (0.0341 : ℝ) < 40 / 1173 ∧
      (40 / 1173 : ℝ) < 0.0342 ∧ 0.0346 < -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) ∧
      -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) < 0.0348 ∧ (0.8 : ℝ) / (1 - 0.8) = 4 ∧
      (0.8 / 1.03 : ℝ) / (1 - 0.8 / 1.03) = 80 / 23 ∧ (3.47 : ℝ) < 80 / 23 ∧
      (80 / 23 : ℝ) < 3.48 :=
  ⟨LongTermDebt.omega_08_example.2.1, LongTermDebt.omega_08_example.2.2.1,
    LongTermDebt.omega_08_example.2.2.2, LogLinearIdentities.fig31_log.1,
    LogLinearIdentities.fig31_log.2, LogLinearIdentities.fig31_linear_exact_coeff⟩

/-! ### Innovations and bond prices -/

/-- Cochrane (2023), p. 54 and p. 64: `E_t ΔE_{t+1}X = 0` for the innovation operator
`LogLinearIdentities.innov` (this is `Ratios.E_innov_zero`). -/
theorem E_innov_eq_zero (t : ℕ) (X : Ω → ℝ) : 𝔼.E t (LogLinearIdentities.innov 𝔼 t X) = 0 :=
  Ratios.E_innov_zero 𝔼 t X

/-- Cochrane (2023), A1 (1.14) and (1.23), pp. 559, 563: the bond price of the geometric
portfolio `Q = ∑_j ωʲ/(1+i)^{j+1}` (`LogLinearIdentities.geomQ`) is the value
`∑_j ωʲ/(1+i)ʲ` of `LongTermDebt.geom_value` divided by `1 + i`. -/
theorem geomQ_eq_geom_value_div {i w : ℝ} (hw : 0 ≤ w) (hwi : w < 1 + i) :
    ∑' j : ℕ, w ^ j / (1 + i) ^ (j + 1) = (∑' j : ℕ, w ^ j / (1 + i) ^ j) / (1 + i) := by
  have hi : 0 < 1 + i := by linarith
  have habs : |w| < |1 + i| := by rw [abs_of_nonneg hw, abs_of_pos hi]; exact hwi
  rw [(LongTermDebt.geom_value hw hwi).tsum_eq, LogLinearIdentities.geomQ habs]
  have h1 : 1 + i - w ≠ 0 := by linarith
  field_simp

/-! ### The two continuous-time valuation engines -/

/-- Cochrane (2023), §3.6.1, p. 74: for a rate continuous on all of `ℝ`, the discount function
`D(t,·) = exp(−∫_t^· r)` satisfies `D' = −rD` at every date (so it is a discount factor in the
sense of `ContinuousLinear.tvc_iff_valuation`). -/
theorem hasDerivAt_disc_of_continuous {r : ℝ → ℝ} (hr : Continuous r) (t τ : ℝ) :
    HasDerivAt (ContinuousShort.disc r t) (-(r τ) * ContinuousShort.disc r t τ) τ := by
  have h1 : HasDerivAt (fun u => ContinuousShort.cumRate r t u) (r τ) τ :=
    (hr.integral_hasStrictDerivAt t τ).hasDerivAt
  have h2 := h1.neg.exp
  have h3 : HasDerivAt (ContinuousShort.disc r t)
      (Real.exp (-ContinuousShort.cumRate r t τ) * -(r τ)) τ := h2
  exact h3.congr_deriv (by rw [mul_comm]; rfl)

/-- Cochrane (2023), (3.31), p. 73, and A1.4, pp. 564–565: **the two engines agree.** Applying
the general discount-factor engine `ContinuousLinear.tvc_iff_valuation` to `Λ = D(t,·)` gives
`ContinuousShort`'s statement: along `V' = rV − s` on `[t, ∞)` with a continuous rate and
integrable discounted surpluses, the TVC `D(t,T)V(T) → 0` holds iff
`V(t) = ContinuousShort.pv r s t` (cf. `ContinuousShort.valuation_iff_tvc`, which instead
assumes `s` continuous and allows `V` to be only right-continuous at `t`). -/
theorem tvc_iff_pv_of_engine {r s V : ℝ → ℝ} {t : ℝ} (hr : Continuous r)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - s τ) τ)
    (hI : ContinuousShort.PVIntegrable r s t) :
    ContinuousShort.TVC r V t ↔ V t = ContinuousShort.pv r s t := by
  have h := ContinuousLinear.tvc_iff_valuation (Λ := ContinuousShort.disc r t) (r := r)
    (fun τ _ => hasDerivAt_disc_of_continuous hr t τ) (ContinuousShort.disc_pos r t t) hV hI
  simp only [ContinuousShort.disc_self, div_one] at h
  exact h

/-- Cochrane (2023), p. 74: the constant-rate discount factors of the two continuous chains
agree, `e^{−cτ}/e^{−ct} = D(t,τ)` for the constant rate `c`. -/
theorem expDisc_ratio_eq_disc (c t τ : ℝ) :
    Real.exp (-(c * τ)) / Real.exp (-(c * t)) = ContinuousShort.disc (fun _ => c) t τ := by
  rw [ContinuousLinear.expDisc_ratio, ContinuousShort.disc_const]

/-! ### E13 in discrete and continuous time -/

/-- Cochrane (2023), p. 57 and §3.6.4/A1.6, pp. 79, 567–569 (survey E13, both time settings):
the "seigniorage" valuation with `ΔM/P` and the "interest-saving" valuation with `iM/P` are not
equivalent without the money transversality condition. Discrete time (`Money.money_bubble`): a
perfect-foresight economy satisfying the standing assumptions and (3.9) in which (3.11) holds and
(3.10) fails at every date. Continuous time (`ContinuousMoney.printing_without_interest_example`):
with `P ≡ 1`, `N = e^{−ιτ}`, `M = e^{ιτ}`, `s = −ιe^{ιτ}`, (3.53) holds and (3.54) fails. In both,
real money grows at the interest rate. -/
theorem e13_discrete_and_continuous {β : ℝ} (hβ0 : 0 < β) (ι t : ℝ) :
    (∃ Λ P i M B s : ℕ → Unit → ℝ, Money.Standing perfectForesight Λ P i M B ∧
      Money.Flow39 P s i M B ∧
      (∀ t, Money.PVRel perfectForesight Λ P B (Money.term11 P s M) t ()) ∧
      (∀ t, ¬ Money.PVRel perfectForesight Λ P (B + M) (Money.term10 P s i M) t ())) ∧
    ((0 : ℝ) / 1 = ∫ τ in Set.Ioi t, Real.exp (-(ι * τ)) * 1 / (Real.exp (-(ι * t)) * 1) *
        (-(ι * Real.exp (ι * τ)) + ι * Real.exp (ι * τ) / 1) ∧
      (Real.exp (ι * t) + 0) / 1 ≠ ∫ τ in Set.Ioi t, Real.exp (-(ι * τ)) * 1 /
        (Real.exp (-(ι * t)) * 1) *
          (-(ι * Real.exp (ι * τ)) + (ι - 0) * Real.exp (ι * τ) / 1)) := by
  obtain ⟨Λ, P, i, M, B, s, h1, h2, -, -, h5, h6, -⟩ := Money.money_bubble hβ0
  have hc := ContinuousMoney.printing_without_interest_example ι t
  exact ⟨⟨Λ, P, i, M, B, s, h1, h2, h5, h6⟩, hc.2.2.2.1, hc.2.2.2.2⟩

/-! ### The misprint in (3.26) -/

/-- Cochrane (2023), (3.26), p. 68: the book prints the nonlinear valuation equation with the
*scaled* surplus `s̃` (`s̃ = ρ/(V/(Py))·s/y`, p. 63) on the right; the nonlinear equation is (3.3)
with `s` (`LongTermDebt.valuationLT_iff_const`). If (3.3) holds and `s̃ = κs` with a constant
scale `κ`, the printed (3.26) holds iff `κ = 1` or the value of debt is zero. -/
theorem eq_3_26_printed_iff {β κ : ℝ} {s : ℕ → Ω → ℝ} {x : Ω → ℝ} (t : ℕ) (ξ : Ω)
    (h33 : x ξ = ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ) :
    x ξ = ∑' n, β ^ n * 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ ↔ κ = 1 ∨ x ξ = 0 := by
  have e : ∀ n, 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ = κ * 𝔼.E t (s (t + n)) ξ := fun n =>
    congrFun (map_smul (𝔼.E t) κ (s (t + n))) ξ
  have hsum : ∑' n, β ^ n * 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ = κ * x ξ := by
    rw [h33, ← tsum_mul_left]
    exact tsum_congr fun n => by rw [e]; ring
  rw [hsum]
  constructor
  · intro h
    have h' : (κ - 1) * x ξ = 0 := by linarith
    rcases mul_eq_zero.mp h' with h0 | h0
    · left; linarith
    · right; exact h0
  · rintro (h0 | h0)
    · rw [h0, one_mul]
    · rw [h0, mul_zero]

end Cochrane.Generality.Links

set_option linter.style.longLine false
#print axioms Cochrane.Generality.SchurStable
#print axioms Cochrane.Generality.discQ
#print axioms Cochrane.Generality.root₁
#print axioms Cochrane.Generality.root₂
#print axioms Cochrane.Generality.root_sum
#print axioms Cochrane.Generality.root_prod
#print axioms Cochrane.Generality.root_eq
#print axioms Cochrane.Generality.normSq_root_of_neg
#print axioms Cochrane.Generality.norm_root_of_nonneg
#print axioms Cochrane.Generality.schurStable_iff_roots
#print axioms Cochrane.Generality.chSeq
#print axioms Cochrane.Generality.convSeq
#print axioms Cochrane.Generality.convSeq_rec
#print axioms Cochrane.Generality.chSeq_eq_convSeq
#print axioms Cochrane.Generality.norm_convSeq_le
#print axioms Cochrane.Generality.abs_chSeq_le
#print axioms Cochrane.Generality.tendsto_chSeq
#print axioms Cochrane.Generality.tr2
#print axioms Cochrane.Generality.det2
#print axioms Cochrane.Generality.tr2_eq_trace
#print axioms Cochrane.Generality.det2_eq_det
#print axioms Cochrane.Generality.sq_eq_cayleyHamilton
#print axioms Cochrane.Generality.pow_succ_eq
#print axioms Cochrane.Generality.abs_pow_entry_le
#print axioms Cochrane.Generality.tendsto_pow_entry
#print axioms Cochrane.Generality.BoundedSeq
#print axioms Cochrane.Generality.homogeneous_iterate
#print axioms Cochrane.Generality.abs_mulVec_le
#print axioms Cochrane.Generality.homogeneous_eq_zero
#print axioms Cochrane.Generality.eq_root_of_eq
#print axioms Cochrane.Generality.exists_eigenvector
#print axioms Cochrane.Generality.exists_bounded_homogeneous
#print axioms Cochrane.Generality.ExpectationSystem
#print axioms Cochrane.Generality.ExpectationSystem.mk
#print axioms Cochrane.Generality.ExpectationSystem.E
#print axioms Cochrane.Generality.ExpectationSystem.const
#print axioms Cochrane.Generality.ExpectationSystem.mono
#print axioms Cochrane.Generality.ExpectationSystem.tower
#print axioms Cochrane.Generality.ExpectationSystem.known
#print axioms Cochrane.Generality.perfectForesight
#print axioms Cochrane.Generality.BoundedProc
#print axioms Cochrane.Generality.BoundedVec
#print axioms Cochrane.Generality.ExpectationSystem.Adapted
#print axioms Cochrane.Generality.ExpectationSystem.IsAR1
#print axioms Cochrane.Generality.ExpectationSystem.E_neg
#print axioms Cochrane.Generality.ExpectationSystem.E_smul
#print axioms Cochrane.Generality.ExpectationSystem.E_E_self
#print axioms Cochrane.Generality.ExpectationSystem.abs_E_le
#print axioms Cochrane.Generality.ExpectationSystem.bounded_E
#print axioms Cochrane.Generality.ExpectationSystem.ar1_iterate
#print axioms Cochrane.Generality.ExpectationSystem.forward_iterate
#print axioms Cochrane.Generality.ExpectationSystem.forward_unique
#print axioms Cochrane.Generality.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.Generality.ExpectationSystem.E_tsum
#print axioms Cochrane.Generality.ExpectationSystem.forwardSeries
#print axioms Cochrane.Generality.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.Generality.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.Generality.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.Generality.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.Generality.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.Generality.ExpectationSystem.PullOut
#print axioms Cochrane.Generality.ExpectationSystem.Solves
#print axioms Cochrane.Generality.ExpectationSystem.AdaptedVec
#print axioms Cochrane.Generality.ExpectationSystem.system_iterate
#print axioms Cochrane.Generality.ExpectationSystem.system_unique
#print axioms Cochrane.Generality.ExpectationSystem.system_not_unique
#print axioms Cochrane.Generality.ExpectationSystem.Determinate
#print axioms Cochrane.Generality.ExpectationSystem.determinate_iff
#print axioms Cochrane.Generality.perfectForesight_pullOut
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.Generality.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.Generality.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.Generality.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.Generality.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.Generality.ForwardSolution.Solves
#print axioms Cochrane.Generality.ForwardSolution.E_of_known
#print axioms Cochrane.Generality.ForwardSolution.solves_adapted
#print axioms Cochrane.Generality.ForwardSolution.iterate_A15
#print axioms Cochrane.Generality.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.Generality.ForwardSolution.summable_A16
#print axioms Cochrane.Generality.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.Generality.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.Generality.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.Generality.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.Generality.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.Generality.ForwardSolution.ScalarEq
#print axioms Cochrane.Generality.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.Generality.ForwardSolution.scalarSol
#print axioms Cochrane.Generality.ForwardSolution.scalarSol_apply
#print axioms Cochrane.Generality.ForwardSolution.scalarEq_iff
#print axioms Cochrane.Generality.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.Generality.ForwardSolution.scalar_homog
#print axioms Cochrane.Generality.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.Generality.ForwardSolution.sunspotFamily
#print axioms Cochrane.Generality.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.Generality.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.Generality.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.Generality.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.Generality.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.Generality.ForwardSolution.homog_solves
#print axioms Cochrane.Generality.ForwardSolution.solves_add_homog
#print axioms Cochrane.Generality.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.Generality.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.Generality.ForwardSolution.existsUnique_iff
#print axioms Cochrane.Generality.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.Generality.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.Generality.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.Generality.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.Generality.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.Generality.ForwardSolution.ar1_decay
#print axioms Cochrane.Generality.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.Generality.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.Generality.ForwardSolution.predetermined_restriction
#print axioms Cochrane.Generality.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.Generality.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.Generality.ForwardSolution.summable_geom_mul
#print axioms Cochrane.Generality.ForwardSolution.abel_tsum
#print axioms Cochrane.Generality.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.Generality.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.Generality.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.Generality.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.Generality.ForwardSolution.E_tsum_dom
#print axioms Cochrane.Generality.LongTermDebt.sdf
#print axioms Cochrane.Generality.LongTermDebt.sdf_zero
#print axioms Cochrane.Generality.LongTermDebt.sdf_succ
#print axioms Cochrane.Generality.LongTermDebt.sdf_succ'
#print axioms Cochrane.Generality.LongTermDebt.sdf_one
#print axioms Cochrane.Generality.LongTermDebt.sdf_add
#print axioms Cochrane.Generality.LongTermDebt.sdf_const
#print axioms Cochrane.Generality.LongTermDebt.sdf_nonneg
#print axioms Cochrane.Generality.LongTermDebt.sdf_pos
#print axioms Cochrane.Generality.LongTermDebt.known_of_le
#print axioms Cochrane.Generality.LongTermDebt.known_mul
#print axioms Cochrane.Generality.LongTermDebt.E_nonneg
#print axioms Cochrane.Generality.LongTermDebt.abs_E_le_E_abs
#print axioms Cochrane.Generality.LongTermDebt.sdf_known
#print axioms Cochrane.Generality.LongTermDebt.E_sdf_mul_E
#print axioms Cochrane.Generality.LongTermDebt.MonotoneConvergence
#print axioms Cochrane.Generality.LongTermDebt.perfectForesight_monotoneConvergence
#print axioms Cochrane.Generality.LongTermDebt.finiteTree_monotoneConvergence
#print axioms Cochrane.Generality.LongTermDebt.E_tsum_abs
#print axioms Cochrane.Generality.LongTermDebt.pv
#print axioms Cochrane.Generality.LongTermDebt.SurplusSummable
#print axioms Cochrane.Generality.LongTermDebt.abs_E_sdf_mul_le
#print axioms Cochrane.Generality.LongTermDebt.summable_pv
#print axioms Cochrane.Generality.LongTermDebt.pv_eq_E_tsum
#print axioms Cochrane.Generality.LongTermDebt.hasSum_E_sdf_mul_pv
#print axioms Cochrane.Generality.LongTermDebt.posPart
#print axioms Cochrane.Generality.LongTermDebt.negPart
#print axioms Cochrane.Generality.LongTermDebt.posPart_sub_negPart
#print axioms Cochrane.Generality.LongTermDebt.summable_posPart
#print axioms Cochrane.Generality.LongTermDebt.summable_negPart
#print axioms Cochrane.Generality.LongTermDebt.E_sdf_mul_split
#print axioms Cochrane.Generality.LongTermDebt.hasSum_E_sdf_mul_pv_signed
#print axioms Cochrane.Generality.LongTermDebt.E_pv_self
#print axioms Cochrane.Generality.LongTermDebt.FlowRec
#print axioms Cochrane.Generality.LongTermDebt.TVC
#print axioms Cochrane.Generality.LongTermDebt.slack
#print axioms Cochrane.Generality.LongTermDebt.telescope
#print axioms Cochrane.Generality.LongTermDebt.hasSum_of_flow_tvc
#print axioms Cochrane.Generality.LongTermDebt.flow_of_pv
#print axioms Cochrane.Generality.LongTermDebt.tvc_of_pv
#print axioms Cochrane.Generality.LongTermDebt.flow_tvc_iff_pv
#print axioms Cochrane.Generality.LongTermDebt.ZeroPrice
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_const_iff
#print axioms Cochrane.Generality.LongTermDebt.realPrice
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_eq_mul
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_real
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_zero
#print axioms Cochrane.Generality.LongTermDebt.realPrice_nonneg
#print axioms Cochrane.Generality.LongTermDebt.realPrice_succ
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_recursive
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_pf_prod
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_pf_rates
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_lt_iff_inflation
#print axioms Cochrane.Generality.LongTermDebt.MaxMaturity
#print axioms Cochrane.Generality.LongTermDebt.FlowLT
#print axioms Cochrane.Generality.LongTermDebt.mktValue
#print axioms Cochrane.Generality.LongTermDebt.purchaseValue
#print axioms Cochrane.Generality.LongTermDebt.realValue
#print axioms Cochrane.Generality.LongTermDebt.flowLT_iff_value
#print axioms Cochrane.Generality.LongTermDebt.purchaseValue_real
#print axioms Cochrane.Generality.LongTermDebt.flowLT_iff_recursion
#print axioms Cochrane.Generality.LongTermDebt.realValue_adapted
#print axioms Cochrane.Generality.LongTermDebt.valuationLT_iff
#print axioms Cochrane.Generality.LongTermDebt.pv_const
#print axioms Cochrane.Generality.LongTermDebt.valuationLT_iff_const
#print axioms Cochrane.Generality.LongTermDebt.valuationLT_not_imp_flow
#print axioms Cochrane.Generality.LongTermDebt.geomDebt
#print axioms Cochrane.Generality.LongTermDebt.GeomFlow
#print axioms Cochrane.Generality.LongTermDebt.annuity
#print axioms Cochrane.Generality.LongTermDebt.geomValue
#print axioms Cochrane.Generality.LongTermDebt.geomValue_eq_tsum
#print axioms Cochrane.Generality.LongTermDebt.realAnnuity
#print axioms Cochrane.Generality.LongTermDebt.annuity_div
#print axioms Cochrane.Generality.LongTermDebt.hasSum_shift
#print axioms Cochrane.Generality.LongTermDebt.geomFlow_iff_recursion
#print axioms Cochrane.Generality.LongTermDebt.geomValue_adapted
#print axioms Cochrane.Generality.LongTermDebt.valuationGeom_iff
#print axioms Cochrane.Generality.LongTermDebt.zeroPrice_pf_const_rate
#print axioms Cochrane.Generality.LongTermDebt.geom_value
#print axioms Cochrane.Generality.LongTermDebt.pv_const_value
#print axioms Cochrane.Generality.LongTermDebt.valuation_1_14
#print axioms Cochrane.Generality.LongTermDebt.steady_state_1_15
#print axioms Cochrane.Generality.LongTermDebt.jumpRatio
#print axioms Cochrane.Generality.LongTermDebt.price_jump_perm
#print axioms Cochrane.Generality.LongTermDebt.price_jump_of_valuation
#print axioms Cochrane.Generality.LongTermDebt.jumpRatio_sub_one
#print axioms Cochrane.Generality.LongTermDebt.price_jump_lt_one_iff
#print axioms Cochrane.Generality.LongTermDebt.price_jump_omega_zero
#print axioms Cochrane.Generality.LongTermDebt.price_jump_gt_one
#print axioms Cochrane.Generality.LongTermDebt.jumpRatio_strictAntiOn_omega
#print axioms Cochrane.Generality.LongTermDebt.price_jump_perpetuity
#print axioms Cochrane.Generality.LongTermDebt.perpetuity_example
#print axioms Cochrane.Generality.LongTermDebt.omega_08_example
#print axioms Cochrane.Generality.LongTermDebt.fgPrice
#print axioms Cochrane.Generality.LongTermDebt.fgPrice_eq_prod
#print axioms Cochrane.Generality.LongTermDebt.fg_value
#print axioms Cochrane.Generality.LongTermDebt.price_jump_fg
#print axioms Cochrane.Generality.LongTermDebt.fgDrop
#print axioms Cochrane.Generality.LongTermDebt.fg_eq_neg_drop
#print axioms Cochrane.Generality.LongTermDebt.fg_tendsto_zero
#print axioms Cochrane.Generality.LongTermDebt.fg_drop_pos
#print axioms Cochrane.Generality.LongTermDebt.fg_drop_antitone_T
#print axioms Cochrane.Generality.LongTermDebt.fg_drop_strictAnti_T
#print axioms Cochrane.Generality.LongTermDebt.fg_drop_strictMonoOn_omega
#print axioms Cochrane.Generality.LongTermDebt.annuity_mono_rates
#print axioms Cochrane.Generality.LongTermDebt.price_le_of_annuity_le
#print axioms Cochrane.Generality.LongTermDebt.meanReverting_le_perm
#print axioms Cochrane.Generality.LongTermDebt.geom_rollover
#print axioms Cochrane.Generality.LongTermDebt.geom_rollover_steady
#print axioms Cochrane.Generality.LongTermDebt.steady_flow_iff_1_15
#print axioms Cochrane.Generality.LongTermDebt.geom_issuance
#print axioms Cochrane.Generality.LongTermDebt.NoTrade
#print axioms Cochrane.Generality.LongTermDebt.geom_noTrade_iff
#print axioms Cochrane.Generality.LongTermDebt.geom_noTrade_iff_path
#print axioms Cochrane.Generality.LongTermDebt.geomFlow_iff_issuance
#print axioms Cochrane.Generality.LongTermDebt.geom_knife_edge
#print axioms Cochrane.Generality.LongTermDebt.knife_edge_surplus_known
#print axioms Cochrane.Generality.LongTermDebt.geom_needs_tending
#print axioms Cochrane.Generality.Ratios.E_div_known
#print axioms Cochrane.Generality.Ratios.gdpTerm
#print axioms Cochrane.Generality.Ratios.E_gdpTerm
#print axioms Cochrane.Generality.Ratios.valuation_gdp_iff
#print axioms Cochrane.Generality.Ratios.valuation_per_dollar_iff
#print axioms Cochrane.Generality.Ratios.valuation_per_dollar_const
#print axioms Cochrane.Generality.Ratios.valuation_per_dollar_gdp_iff
#print axioms Cochrane.Generality.Ratios.E_innov_zero
#print axioms Cochrane.Generality.Ratios.E_innov_pv_zero
#print axioms Cochrane.Generality.Ratios.flow_gdp_iff
#print axioms Cochrane.Generality.Ratios.gdp_growth_mono
#print axioms Cochrane.Generality.StochasticDiscount.sdf_eq_ratio
#print axioms Cochrane.Generality.StochasticDiscount.sdf_marginal_utility
#print axioms Cochrane.Generality.StochasticDiscount.bondPrice
#print axioms Cochrane.Generality.StochasticDiscount.FlowOne
#print axioms Cochrane.Generality.StochasticDiscount.realDebt
#print axioms Cochrane.Generality.StochasticDiscount.flowOne_iff_rec
#print axioms Cochrane.Generality.StochasticDiscount.tvc_lambda_iff
#print axioms Cochrane.Generality.StochasticDiscount.pv_lambda
#print axioms Cochrane.Generality.StochasticDiscount.valuation_sdf_iff
#print axioms Cochrane.Generality.StochasticDiscount.price_eq_of_valuation
#print axioms Cochrane.Generality.StochasticDiscount.price_unique
#print axioms Cochrane.Generality.StochasticDiscount.inv_return_expost
#print axioms Cochrane.Generality.StochasticDiscount.inv_return_sdf
#print axioms Cochrane.Generality.StochasticDiscount.expostReturn
#print axioms Cochrane.Generality.StochasticDiscount.expostReturn_rate
#print axioms Cochrane.Generality.StochasticDiscount.flow_expost
#print axioms Cochrane.Generality.StochasticDiscount.ExPostFlow
#print axioms Cochrane.Generality.StochasticDiscount.expost_iterate
#print axioms Cochrane.Generality.StochasticDiscount.expost_tendsto_iff
#print axioms Cochrane.Generality.StochasticDiscount.expost_pv
#print axioms Cochrane.Generality.StochasticDiscount.expost_E_tendsto_iff
#print axioms Cochrane.Generality.StochasticDiscount.expost_pv_E
#print axioms Cochrane.Generality.StochasticDiscount.expost_flow_E
#print axioms Cochrane.Generality.StochasticDiscount.pf_expost_inv_eq_sdf
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt_some_le
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt_some_gt
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt_none
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt_pt
#print axioms Cochrane.Generality.StochasticDiscount.pesoPt_pt'
#print axioms Cochrane.Generality.StochasticDiscount.pesoSystem
#print axioms Cochrane.Generality.StochasticDiscount.pesoSystem_E
#print axioms Cochrane.Generality.StochasticDiscount.pesoSystem_pullOut
#print axioms Cochrane.Generality.StochasticDiscount.pesoSystem_monotoneConvergence
#print axioms Cochrane.Generality.StochasticDiscount.pesoS
#print axioms Cochrane.Generality.StochasticDiscount.pesoX
#print axioms Cochrane.Generality.StochasticDiscount.peso_values
#print axioms Cochrane.Generality.StochasticDiscount.pesoX_adapted
#print axioms Cochrane.Generality.StochasticDiscount.pesoS_adapted
#print axioms Cochrane.Generality.StochasticDiscount.pesoX_flow
#print axioms Cochrane.Generality.StochasticDiscount.pesoX_bounds
#print axioms Cochrane.Generality.StochasticDiscount.pesoS_abs_le
#print axioms Cochrane.Generality.StochasticDiscount.pesoP
#print axioms Cochrane.Generality.StochasticDiscount.pesoReturn_none
#print axioms Cochrane.Generality.StochasticDiscount.expost_may_diverge
#print axioms Cochrane.Generality.StochasticDiscount.finiteTree_known_iff
#print axioms Cochrane.Generality.StochasticDiscount.finiteTree_info_stable
#print axioms Cochrane.Generality.StochasticDiscount.finiteTree_eventually_known
#print axioms Cochrane.Generality.StochasticDiscount.expostFlow_of_flowOne
#print axioms Cochrane.Generality.StochasticDiscount.finiteTree_expost_pv
#print axioms Cochrane.Generality.StochasticDiscount.portfolioReturn
#print axioms Cochrane.Generality.StochasticDiscount.flowLT_iff_3_8
#print axioms Cochrane.Generality.StochasticDiscount.expostLT_pv
#print axioms Cochrane.Generality.Money.telescope
#print axioms Cochrane.Generality.Money.pv_iff_tvc
#print axioms Cochrane.Generality.Money.BondEuler
#print axioms Cochrane.Generality.Money.Standing
#print axioms Cochrane.Generality.Money.Standing.mk
#print axioms Cochrane.Generality.Money.Standing.pullOut
#print axioms Cochrane.Generality.Money.Standing.disc_pos
#print axioms Cochrane.Generality.Money.Standing.price_pos
#print axioms Cochrane.Generality.Money.Standing.nominal_adapted
#print axioms Cochrane.Generality.Money.Standing.disc_inv_adapted
#print axioms Cochrane.Generality.Money.Standing.bonds_adapted
#print axioms Cochrane.Generality.Money.Standing.money_adapted
#print axioms Cochrane.Generality.Money.Standing.bonds_pre
#print axioms Cochrane.Generality.Money.Standing.money_pre
#print axioms Cochrane.Generality.Money.Standing.rate_gt
#print axioms Cochrane.Generality.Money.Standing.euler
#print axioms Cochrane.Generality.Money.Flow39
#print axioms Cochrane.Generality.Money.FlowIm
#print axioms Cochrane.Generality.Money.flow39_iff_flowIm
#print axioms Cochrane.Generality.Money.PVRel
#print axioms Cochrane.Generality.Money.TVC
#print axioms Cochrane.Generality.Money.PVSummable
#print axioms Cochrane.Generality.Money.term10
#print axioms Cochrane.Generality.Money.term11
#print axioms Cochrane.Generality.Money.term12
#print axioms Cochrane.Generality.Money.term12b
#print axioms Cochrane.Generality.Money.weight_identity
#print axioms Cochrane.Generality.Money.E_next
#print axioms Cochrane.Generality.Money.E_ratio
#print axioms Cochrane.Generality.Money.adapted_val
#print axioms Cochrane.Generality.Money.pv_book_iff
#print axioms Cochrane.Generality.Money.rec_3_12
#print axioms Cochrane.Generality.Money.rec_3_12b
#print axioms Cochrane.Generality.Money.pv_3_12
#print axioms Cochrane.Generality.Money.pv_3_12b
#print axioms Cochrane.Generality.Money.term12_zero
#print axioms Cochrane.Generality.Money.term12b_zero
#print axioms Cochrane.Generality.Money.pv_3_10
#print axioms Cochrane.Generality.Money.pv_3_11
#print axioms Cochrane.Generality.Money.tvc_split
#print axioms Cochrane.Generality.Money.pv_3_10_iff_3_11
#print axioms Cochrane.Generality.Money.pv_3_10_iff_money_tvc
#print axioms Cochrane.Generality.Money.money_bubble
#print axioms Cochrane.Generality.Money.exPostReturn
#print axioms Cochrane.Generality.Money.flow_3_14
#print axioms Cochrane.Generality.Money.iterate_discount
#print axioms Cochrane.Generality.Money.pv_discount_iff
#print axioms Cochrane.Generality.Money.pv_3_15_finite
#print axioms Cochrane.Generality.Money.pv_3_15_iff
#print axioms Cochrane.Generality.Money.zero_bound_flow_total
#print axioms Cochrane.Generality.Money.zero_bound_valuation
#print axioms Cochrane.Generality.Money.full_interest_valuation
#print axioms Cochrane.Generality.Money.zero_bound_beta
#print axioms Cochrane.Generality.Money.zero_bound_E_outside
#print axioms Cochrane.Generality.Money.zero_bound_not_from_3_11
#print axioms Cochrane.Generality.Money.offsetSurplus
#print axioms Cochrane.Generality.Money.seigniorage_offset_term
#print axioms Cochrane.Generality.Money.seigniorage_offset_valuation
#print axioms Cochrane.Generality.Money.seigniorage_offset_flow
#print axioms Cochrane.Generality.Money.full_interest_split_irrelevant
#print axioms Cochrane.Generality.Money.passive_split
#print axioms Cochrane.Generality.Money.seigniorage_2019
#print axioms Cochrane.Generality.Money.seigniorage_1980s
#print axioms Cochrane.Generality.LogLinearIdentities.marketValue
#print axioms Cochrane.Generality.LogLinearIdentities.overnightValue
#print axioms Cochrane.Generality.LogLinearIdentities.nominalReturn
#print axioms Cochrane.Generality.LogLinearIdentities.flow_value_identity
#print axioms Cochrane.Generality.LogLinearIdentities.flow_gdp
#print axioms Cochrane.Generality.LogLinearIdentities.pv_gdp_finite
#print axioms Cochrane.Generality.LogLinearIdentities.pv_gdp_iff
#print axioms Cochrane.Generality.LogLinearIdentities.log_flow_identity
#print axioms Cochrane.Generality.LogLinearIdentities.logFlow
#print axioms Cochrane.Generality.LogLinearIdentities.logFlow_hasFDerivAt
#print axioms Cochrane.Generality.LogLinearIdentities.rho_eq
#print axioms Cochrane.Generality.LogLinearIdentities.printed_rho_eq_iff
#print axioms Cochrane.Generality.LogLinearIdentities.rho_lt_one_iff
#print axioms Cochrane.Generality.LogLinearIdentities.printed_rho_lt_one_iff
#print axioms Cochrane.Generality.LogLinearIdentities.logFlow_hasFDerivAt_rho
#print axioms Cochrane.Generality.LogLinearIdentities.constant_1_11
#print axioms Cochrane.Generality.LogLinearIdentities.constant_zero_of_rg
#print axioms Cochrane.Generality.LogLinearIdentities.tangent_1_11
#print axioms Cochrane.Generality.LogLinearIdentities.stilde_eq
#print axioms Cochrane.Generality.LogLinearIdentities.Flow317
#print axioms Cochrane.Generality.LogLinearIdentities.zp
#print axioms Cochrane.Generality.LogLinearIdentities.pv_318
#print axioms Cochrane.Generality.LogLinearIdentities.pv_318_E
#print axioms Cochrane.Generality.LogLinearIdentities.pv_319_iff
#print axioms Cochrane.Generality.LogLinearIdentities.terminal_of_bounded
#print axioms Cochrane.Generality.LogLinearIdentities.pv_rho_one
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.mk
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.flow
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.v_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.rn_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.infl_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.g_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.s_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.rho_pos
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.rho_lt_one
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.v_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.rn_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.infl_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.g_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.LinearEconomy.s_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.zp_bdd
#print axioms Cochrane.Generality.LogLinearIdentities.zp_adapted
#print axioms Cochrane.Generality.LogLinearIdentities.pv_319
#print axioms Cochrane.Generality.LogLinearIdentities.pv_319_E_outside
#print axioms Cochrane.Generality.LogLinearIdentities.price_expected_return
#print axioms Cochrane.Generality.LogLinearIdentities.innov
#print axioms Cochrane.Generality.LogLinearIdentities.innov_apply
#print axioms Cochrane.Generality.LogLinearIdentities.innov_known
#print axioms Cochrane.Generality.LogLinearIdentities.abs_innov_le
#print axioms Cochrane.Generality.LogLinearIdentities.summable_innov
#print axioms Cochrane.Generality.LogLinearIdentities.summable_pow_succ
#print axioms Cochrane.Generality.LogLinearIdentities.innov_pv
#print axioms Cochrane.Generality.LogLinearIdentities.innov_identity_3_20
#print axioms Cochrane.Generality.LogLinearIdentities.return_indep_weights
#print axioms Cochrane.Generality.LogLinearIdentities.geomQ
#print axioms Cochrane.Generality.LogLinearIdentities.geomQ_short
#print axioms Cochrane.Generality.LogLinearIdentities.geomQ_perpetuity
#print axioms Cochrane.Generality.LogLinearIdentities.geom_portfolio_return
#print axioms Cochrane.Generality.LogLinearIdentities.bondReturn
#print axioms Cochrane.Generality.LogLinearIdentities.bondReturn_hasFDerivAt
#print axioms Cochrane.Generality.LogLinearIdentities.bondReturn_steady
#print axioms Cochrane.Generality.LogLinearIdentities.omega_hat_eq_iff
#print axioms Cochrane.Generality.LogLinearIdentities.BondRet
#print axioms Cochrane.Generality.LogLinearIdentities.BondPriceOK
#print axioms Cochrane.Generality.LogLinearIdentities.bondPrice_forward
#print axioms Cochrane.Generality.LogLinearIdentities.printed_bondPrice_iff
#print axioms Cochrane.Generality.LogLinearIdentities.printed_bondPrice_counterexample
#print axioms Cochrane.Generality.LogLinearIdentities.EH_bond
#print axioms Cochrane.Generality.LogLinearIdentities.rn_bound
#print axioms Cochrane.Generality.LogLinearIdentities.bondReturn_innov
#print axioms Cochrane.Generality.LogLinearIdentities.bondReturn_innov_real
#print axioms Cochrane.Generality.LogLinearIdentities.weighted_inflation_identity
#print axioms Cochrane.Generality.LogLinearIdentities.short_debt_return_known
#print axioms Cochrane.Generality.LogLinearIdentities.short_debt_EH
#print axioms Cochrane.Generality.LogLinearIdentities.innov_r_zero
#print axioms Cochrane.Generality.LogLinearIdentities.special_constant_short
#print axioms Cochrane.Generality.LogLinearIdentities.special_varying_short
#print axioms Cochrane.Generality.LogLinearIdentities.special_constant_long
#print axioms Cochrane.Generality.LogLinearIdentities.identity_3_24
#print axioms Cochrane.Generality.LogLinearIdentities.identity_3_25
#print axioms Cochrane.Generality.LogLinearIdentities.monetary_disinflation
#print axioms Cochrane.Generality.LogLinearIdentities.perpetuity_no_discount_terms
#print axioms Cochrane.Generality.LogLinearIdentities.weights_close
#print axioms Cochrane.Generality.LogLinearIdentities.scaling_ratio
#print axioms Cochrane.Generality.LogLinearIdentities.perm_inflation_equiv
#print axioms Cochrane.Generality.LogLinearIdentities.zero_current_inflation_possible
#print axioms Cochrane.Generality.LogLinearIdentities.disinflation_seq
#print axioms Cochrane.Generality.LogLinearIdentities.fig31_jump
#print axioms Cochrane.Generality.LogLinearIdentities.fig31_value
#print axioms Cochrane.Generality.LogLinearIdentities.fig31_path
#print axioms Cochrane.Generality.LogLinearIdentities.expected_rise_no_jump
#print axioms Cochrane.Generality.LogLinearIdentities.announcement_jump
#print axioms Cochrane.Generality.LogLinearIdentities.disinflation_monotone_omega
#print axioms Cochrane.Generality.LogLinearIdentities.disinflation_monotone_length
#print axioms Cochrane.Generality.LogLinearIdentities.fig31_log
#print axioms Cochrane.Generality.LogLinearIdentities.fig31_linear_exact_coeff
#print axioms Cochrane.Generality.MSV.Eqm
#print axioms Cochrane.Generality.MSV.eqm_solves
#print axioms Cochrane.Generality.MSV.eqm_infl
#print axioms Cochrane.Generality.MSV.vstar
#print axioms Cochrane.Generality.MSV.vstar_apply
#print axioms Cochrane.Generality.MSV.forcing_ok
#print axioms Cochrane.Generality.MSV.inflStar
#print axioms Cochrane.Generality.MSV.msv_exists
#print axioms Cochrane.Generality.MSV.msv_v_unique
#print axioms Cochrane.Generality.MSV.msv_unique
#print axioms Cochrane.Generality.MSV.msv_determinacy
#print axioms Cochrane.Generality.MSV.msv_infl_innov
#print axioms Cochrane.Generality.MSV.vstar_ar1
#print axioms Cochrane.Generality.MSV.msv_solution
#print axioms Cochrane.Generality.MSV.msv_solution_is_eqm
#print axioms Cochrane.Generality.MSV.msv_printed_not_eqm
#print axioms Cochrane.Generality.MSV.coin_bdd
#print axioms Cochrane.Generality.MSV.msv_printed_fails_coin
#print axioms Cochrane.Generality.MSV.GuessOK
#print axioms Cochrane.Generality.MSV.msv_coeffs_iff
#print axioms Cochrane.Generality.MSV.msv_coeffs_printed_fails
#print axioms Cochrane.Generality.MSV.dRec
#print axioms Cochrane.Generality.MSV.eq_dRec
#print axioms Cochrane.Generality.MSV.abs_rec_le
#print axioms Cochrane.Generality.MSV.rec_bounded
#print axioms Cochrane.Generality.MSV.rec_unbounded
#print axioms Cochrane.Generality.MSV.msv_debt_rec
#print axioms Cochrane.Generality.MSV.msv_debt_not_bibo
#print axioms Cochrane.Generality.MSV.msv_deviation_iterate
#print axioms Cochrane.Generality.MSV.msv_deviation_explodes
#print axioms Cochrane.Generality.ContinuousShort.cumRate
#print axioms Cochrane.Generality.ContinuousShort.disc
#print axioms Cochrane.Generality.ContinuousShort.FlowOn
#print axioms Cochrane.Generality.ContinuousShort.TVC
#print axioms Cochrane.Generality.ContinuousShort.pv
#print axioms Cochrane.Generality.ContinuousShort.PVIntegrable
#print axioms Cochrane.Generality.ContinuousShort.intervalIntegrable_of_ici
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_cumRate
#print axioms Cochrane.Generality.ContinuousShort.continuousOn_cumRate
#print axioms Cochrane.Generality.ContinuousShort.cumRate_self
#print axioms Cochrane.Generality.ContinuousShort.cumRate_add
#print axioms Cochrane.Generality.ContinuousShort.cumRate_const
#print axioms Cochrane.Generality.ContinuousShort.disc_pos
#print axioms Cochrane.Generality.ContinuousShort.disc_self
#print axioms Cochrane.Generality.ContinuousShort.disc_mul
#print axioms Cochrane.Generality.ContinuousShort.disc_eq_div
#print axioms Cochrane.Generality.ContinuousShort.disc_const
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_disc
#print axioms Cochrane.Generality.ContinuousShort.continuousOn_disc
#print axioms Cochrane.Generality.ContinuousShort.eq_of_hasDerivAt_zero
#print axioms Cochrane.Generality.ContinuousShort.integral_Ioi_shift
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_disc_mul
#print axioms Cochrane.Generality.ContinuousShort.pv_finite
#print axioms Cochrane.Generality.ContinuousShort.tendsto_disc_mul
#print axioms Cochrane.Generality.ContinuousShort.valuation_iff_tvc
#print axioms Cochrane.Generality.ContinuousShort.pvIntegrable_of_le
#print axioms Cochrane.Generality.ContinuousShort.pv_eq_of_le
#print axioms Cochrane.Generality.ContinuousShort.pv_eqOn_closed
#print axioms Cochrane.Generality.ContinuousShort.flowOn_pv
#print axioms Cochrane.Generality.ContinuousShort.tvc_pv
#print axioms Cochrane.Generality.ContinuousShort.FlowOn.mono
#print axioms Cochrane.Generality.ContinuousShort.TVC.mono
#print axioms Cochrane.Generality.ContinuousShort.eqOn_pv_of_tvc
#print axioms Cochrane.Generality.ContinuousShort.exists_unique_flow_tvc
#print axioms Cochrane.Generality.ContinuousShort.flow_general_solution
#print axioms Cochrane.Generality.ContinuousShort.flowOn_bubble
#print axioms Cochrane.Generality.ContinuousShort.tvc_bubble_iff
#print axioms Cochrane.Generality.ContinuousShort.tvc_iff_eqOn_pv
#print axioms Cochrane.Generality.ContinuousShort.flowOn_tvc_of_eqOn_pv
#print axioms Cochrane.Generality.ContinuousShort.eqOn_pv_iff_flowOn_tvc
#print axioms Cochrane.Generality.ContinuousShort.price_level_determined
#print axioms Cochrane.Generality.ContinuousShort.price_level_pos
#print axioms Cochrane.Generality.ContinuousShort.no_positive_price_level
#print axioms Cochrane.Generality.ContinuousShort.price_jump_ratio
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_real_of_nominal
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_nominal_of_real
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_inv_price
#print axioms Cochrane.Generality.ContinuousShort.flowOn_of_nominal
#print axioms Cochrane.Generality.ContinuousShort.price_level_of_nominal
#print axioms Cochrane.Generality.ContinuousShort.nominal_pv_iff_flow
#print axioms Cochrane.Generality.ContinuousShort.discountFactor_eq
#print axioms Cochrane.Generality.ContinuousShort.rate_eq_neg_logDeriv
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_nominal_discount
#print axioms Cochrane.Generality.ContinuousShort.hasDerivAt_inv_PW
#print axioms Cochrane.Generality.ContinuousShort.flow_iff_Lambda
#print axioms Cochrane.Generality.ContinuousShort.nominal_flow_iff_Lambda
#print axioms Cochrane.Generality.ContinuousShort.flow_iff_W
#print axioms Cochrane.Generality.ContinuousShort.nominal_flow_iff_W
#print axioms Cochrane.Generality.ContinuousShort.W_closed_form
#print axioms Cochrane.Generality.ContinuousShort.disc_eq_W_ratio
#print axioms Cochrane.Generality.ContinuousShort.valuation_W_iff
#print axioms Cochrane.Generality.ContinuousShort.valuation_Lambda_iff
#print axioms Cochrane.Generality.ContinuousShort.pv_const_rate
#print axioms Cochrane.Generality.ContinuousShort.pvIntegrable_const
#print axioms Cochrane.Generality.ContinuousShort.pv_const_const
#print axioms Cochrane.Generality.ContinuousShort.value_const_const
#print axioms Cochrane.Generality.ContinuousLong.bondPrice
#print axioms Cochrane.Generality.ContinuousLong.BondIntegrable
#print axioms Cochrane.Generality.ContinuousLong.cumRate_add_const
#print axioms Cochrane.Generality.ContinuousLong.disc_add_const
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_eq
#print axioms Cochrane.Generality.ContinuousLong.bondIntegrable_of_ge
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_flow
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_tvc
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_unique
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_const
#print axioms Cochrane.Generality.ContinuousLong.bondIntegrable_const
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_pos
#print axioms Cochrane.Generality.ContinuousLong.tendsto_book_bondValue
#print axioms Cochrane.Generality.ContinuousLong.debtDensity
#print axioms Cochrane.Generality.ContinuousLong.debtDensity_self
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_debtDensity
#print axioms Cochrane.Generality.ContinuousLong.flow_LT_geometric
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_nominal_value
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_value_LT
#print axioms Cochrane.Generality.ContinuousLong.nominalReturn_eq
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_nominal_value_priced
#print axioms Cochrane.Generality.ContinuousLong.flowOn_value_LT
#print axioms Cochrane.Generality.ContinuousLong.valuation_LT_iff
#print axioms Cochrane.Generality.ContinuousLong.price_level_LT
#print axioms Cochrane.Generality.ContinuousLong.valuation_LT_W_iff
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_value_portfolio
#print axioms Cochrane.Generality.ContinuousLong.portfolio_return_weights
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_value_portfolio_priced
#print axioms Cochrane.Generality.ContinuousLong.A15_integrated
#print axioms Cochrane.Generality.ContinuousLong.A15_valuation_iff
#print axioms Cochrane.Generality.ContinuousLong.A15_counterexample
#print axioms Cochrane.Generality.ContinuousLong.bubble_not_valuation
#print axioms Cochrane.Generality.ContinuousLong.V_over_W_antitone
#print axioms Cochrane.Generality.ContinuousLong.stock_return_iff
#print axioms Cochrane.Generality.ContinuousLong.stock_price_valuation
#print axioms Cochrane.Generality.ContinuousLong.Lambda_W_const
#print axioms Cochrane.Generality.ContinuousLong.Lambda_valuation
#print axioms Cochrane.Generality.ContinuousLong.jump_V_over_W
#print axioms Cochrane.Generality.ContinuousLong.jump_short_return_sign
#print axioms Cochrane.Generality.ContinuousLong.steady_state_LT
#print axioms Cochrane.Generality.ContinuousLong.price_jump_of_valuation
#print axioms Cochrane.Generality.ContinuousLong.price_jump_permanent
#print axioms Cochrane.Generality.ContinuousLong.post_jump_equilibrium
#print axioms Cochrane.Generality.ContinuousLong.price_jump_perpetuity
#print axioms Cochrane.Generality.ContinuousLong.price_jump_perpetuity_numeric
#print axioms Cochrane.Generality.ContinuousLong.price_jump_tendsto_one
#print axioms Cochrane.Generality.ContinuousLong.price_jump_lt_one
#print axioms Cochrane.Generality.ContinuousLong.price_jump_mono
#print axioms Cochrane.Generality.ContinuousLong.fgRate
#print axioms Cochrane.Generality.ContinuousLong.cumRate_fg_le
#print axioms Cochrane.Generality.ContinuousLong.cumRate_fg_ge
#print axioms Cochrane.Generality.ContinuousLong.bondPrice_fg
#print axioms Cochrane.Generality.ContinuousLong.price_jump_fg
#print axioms Cochrane.Generality.ContinuousLong.fg_jump_at_zero
#print axioms Cochrane.Generality.ContinuousLong.fg_jump_tendsto_zero
#print axioms Cochrane.Generality.ContinuousLong.fg_jump_neg
#print axioms Cochrane.Generality.ContinuousLong.fg_jump_antitone_T
#print axioms Cochrane.Generality.ContinuousLong.fg_jump_antitone_ω
#print axioms Cochrane.Generality.ContinuousLong.partialsCLM
#print axioms Cochrane.Generality.ContinuousLong.partialsCLM_apply
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_diag
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_maturity
#print axioms Cochrane.Generality.ContinuousLong.mktValue
#print axioms Cochrane.Generality.ContinuousLong.issuanceValue
#print axioms Cochrane.Generality.ContinuousLong.capitalGain
#print axioms Cochrane.Generality.ContinuousLong.valueWeightedReturn
#print axioms Cochrane.Generality.ContinuousLong.MaturityRegularAt
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_mktValue
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_mktValue_flow
#print axioms Cochrane.Generality.ContinuousLong.valueWeightedReturn_eq
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_value_general
#print axioms Cochrane.Generality.ContinuousLong.zeroPrice_partials
#print axioms Cochrane.Generality.ContinuousLong.capitalGain_priced
#print axioms Cochrane.Generality.ContinuousLong.hasDerivAt_mktValue_priced
#print axioms Cochrane.Generality.ContinuousLong.flowOn_value_general
#print axioms Cochrane.Generality.ContinuousLong.valuation_general_iff
#print axioms Cochrane.Generality.ContinuousLong.mktValue_geometric
#print axioms Cochrane.Generality.ContinuousLong.flow_general_geometric_iff
#print axioms Cochrane.Generality.ContinuousLong.mktValue_finite
#print axioms Cochrane.Generality.ContinuousLong.flow_general_finite_iff
#print axioms Cochrane.Generality.ContinuousLinear.tendsto_of_hasDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.tendsto_integral_Ioi_zero
#print axioms Cochrane.Generality.ContinuousLinear.discounted_hasDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.discounted_tendsto
#print axioms Cochrane.Generality.ContinuousLinear.integral_ratio_eq
#print axioms Cochrane.Generality.ContinuousLinear.tvc_iff_valuation
#print axioms Cochrane.Generality.ContinuousLinear.valuation_every_date
#print axioms Cochrane.Generality.ContinuousLinear.valuation_unique
#print axioms Cochrane.Generality.ContinuousLinear.valuation_exists
#print axioms Cochrane.Generality.ContinuousLinear.hasDerivAt_expDisc
#print axioms Cochrane.Generality.ContinuousLinear.expDisc_ratio
#print axioms Cochrane.Generality.ContinuousLinear.const_rate_tvc_iff
#print axioms Cochrane.Generality.ContinuousLinear.integrableOn_shift
#print axioms Cochrane.Generality.ContinuousLinear.integrableOn_shift_weighted
#print axioms Cochrane.Generality.ContinuousLinear.shift_weighted
#print axioms Cochrane.Generality.ContinuousLinear.integral_weighted_sub
#print axioms Cochrane.Generality.ContinuousLinear.steady_state_iff
#print axioms Cochrane.Generality.ContinuousLinear.flow_hasFDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.flow_remainder
#print axioms Cochrane.Generality.ContinuousLinear.flow_deviation_form
#print axioms Cochrane.Generality.ContinuousLinear.normalised_flow
#print axioms Cochrane.Generality.ContinuousLinear.linear_value_iff
#print axioms Cochrane.Generality.ContinuousLinear.linear_value_split
#print axioms Cochrane.Generality.ContinuousLinear.value_identity_341
#print axioms Cochrane.Generality.ContinuousLinear.real_return_of_nominal
#print axioms Cochrane.Generality.ContinuousLinear.inv_price_growth
#print axioms Cochrane.Generality.ContinuousLinear.ar1_hasDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.ar1_unique
#print axioms Cochrane.Generality.ContinuousLinear.ar1_printed_not_solution
#print axioms Cochrane.Generality.ContinuousLinear.ar1_integrable
#print axioms Cochrane.Generality.ContinuousLinear.ar1_pv
#print axioms Cochrane.Generality.ContinuousLinear.ar1_news
#print axioms Cochrane.Generality.ContinuousLinear.bond_price_yield
#print axioms Cochrane.Generality.ContinuousLinear.holding_return_tendsto
#print axioms Cochrane.Generality.ContinuousLinear.return_eq_yield
#print axioms Cochrane.Generality.ContinuousLinear.return_identity_iff
#print axioms Cochrane.Generality.ContinuousLinear.bond_steady_state
#print axioms Cochrane.Generality.ContinuousLinear.bond_hasFDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.bond_linear_iff
#print axioms Cochrane.Generality.ContinuousLinear.bond_linear_corrected_line
#print axioms Cochrane.Generality.ContinuousLinear.printed_line_forces_steady
#print axioms Cochrane.Generality.ContinuousLinear.printed_line_counterexample
#print axioms Cochrane.Generality.ContinuousLinear.bond_price_forward_iff
#print axioms Cochrane.Generality.ContinuousLinear.tvc_of_bounded
#print axioms Cochrane.Generality.ContinuousLinear.bond_price_forward_bounded
#print axioms Cochrane.Generality.ContinuousLinear.bondForward
#print axioms Cochrane.Generality.ContinuousLinear.bondForward_spec
#print axioms Cochrane.Generality.ContinuousLinear.value_hasFDerivAt
#print axioms Cochrane.Generality.ContinuousLinear.value_remainder
#print axioms Cochrane.Generality.ContinuousLinear.news_return_tendsto
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.mk
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.flow
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.bond
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.value
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.tvcV
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.tvcQ
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.intS
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.intR
#print axioms Cochrane.Generality.ContinuousLinear.Eqm.LinearEqm.intN
#print axioms Cochrane.Generality.ContinuousLinear.steady_state_eqm
#print axioms Cochrane.Generality.ContinuousLinear.eqm_value
#print axioms Cochrane.Generality.ContinuousLinear.eqm_bond
#print axioms Cochrane.Generality.ContinuousLinear.eqm_int_real_bond
#print axioms Cochrane.Generality.ContinuousLinear.eqm_int_infl
#print axioms Cochrane.Generality.ContinuousLinear.news_value_eq_bond
#print axioms Cochrane.Generality.ContinuousLinear.news_value
#print axioms Cochrane.Generality.ContinuousLinear.news_bond
#print axioms Cochrane.Generality.ContinuousLinear.news_bond_real
#print axioms Cochrane.Generality.ContinuousLinear.news_weighted_inflation
#print axioms Cochrane.Generality.ContinuousLinear.short_debt_news
#print axioms Cochrane.Generality.ContinuousLinear.short_limit_integrable
#print axioms Cochrane.Generality.ContinuousLinear.short_limit
#print axioms Cochrane.Generality.ContinuousLinear.short_limit_single
#print axioms Cochrane.Generality.ContinuousLinear.short_debt_limit_identity
#print axioms Cochrane.Generality.ContinuousLinear.perpetuity_lhs_ne_zero
#print axioms Cochrane.Generality.ContinuousLinear.perpetuity_price
#print axioms Cochrane.Generality.ContinuousLinear.instantaneous_limit
#print axioms Cochrane.Generality.ContinuousLinear.lhs_ignores_one_date
#print axioms Cochrane.Generality.ContinuousMoney.flow_real
#print axioms Cochrane.Generality.ContinuousMoney.nominal_discount_of_real
#print axioms Cochrane.Generality.ContinuousMoney.inv_nominal_value
#print axioms Cochrane.Generality.ContinuousMoney.lambda_ratio_eq_W
#print axioms Cochrane.Generality.ContinuousMoney.forward_iff
#print axioms Cochrane.Generality.ContinuousMoney.real_form_iff
#print axioms Cochrane.Generality.ContinuousMoney.printing_hasDerivAt
#print axioms Cochrane.Generality.ContinuousMoney.money_printing_iff
#print axioms Cochrane.Generality.ContinuousMoney.interest_hasDerivAt
#print axioms Cochrane.Generality.ContinuousMoney.money_interest_iff
#print axioms Cochrane.Generality.ContinuousMoney.printing_interest_iff_money_tvc
#print axioms Cochrane.Generality.ContinuousMoney.printing_without_interest_example
#print axioms Cochrane.Generality.ContinuousMoney.printing_W_hasDerivAt
#print axioms Cochrane.Generality.ContinuousMoney.money_printing_W_iff
#print axioms Cochrane.Generality.ContinuousMoney.interest_W_hasDerivAt
#print axioms Cochrane.Generality.ContinuousMoney.money_interest_W_iff
#print axioms Cochrane.Generality.ContinuousMoney.printed_index_counterexample
#print axioms Cochrane.Generality.ContinuousMoney.mixed_hasDerivAt
#print axioms Cochrane.Generality.ContinuousMoney.money_mixed_iff
#print axioms Cochrane.Generality.ContinuousMoney.mixed_rate_lt
#print axioms Cochrane.Generality.Links.pvRel_iff_pv
#print axioms Cochrane.Generality.Links.tvc_money_iff_tvc
#print axioms Cochrane.Generality.Links.flowRec_one_iff
#print axioms Cochrane.Generality.Links.tvc_one_iff
#print axioms Cochrane.Generality.Links.sdf_ratio_pow
#print axioms Cochrane.Generality.Links.pv_beta_pow
#print axioms Cochrane.Generality.Links.pv_lambda_beta
#print axioms Cochrane.Generality.Links.valuation_sdf_beta_iff
#print axioms Cochrane.Generality.Links.annuity_zero
#print axioms Cochrane.Generality.Links.geomValue_zero
#print axioms Cochrane.Generality.Links.geomFlow_zero_iff
#print axioms Cochrane.Generality.Links.zeroPrice_one_eq_bondPrice
#print axioms Cochrane.Generality.Links.geomFlow_zero_iff_flowOne
#print axioms Cochrane.Generality.Links.valuationGeom_zero_iff
#print axioms Cochrane.Generality.Links.jumpRatio_tendsto_short
#print axioms Cochrane.Generality.Links.short_debt_limits
#print axioms Cochrane.Generality.Links.bond_coeff_exp
#print axioms Cochrane.Generality.Links.weights_322_351
#print axioms Cochrane.Generality.Links.omega_disc_endpoints
#print axioms Cochrane.Generality.Links.tendsto_slope_exp_sub
#print axioms Cochrane.Generality.Links.annuity_tendsto_bondPrice
#print axioms Cochrane.Generality.Links.jumpRatio_tendsto_continuous
#print axioms Cochrane.Generality.Links.e15_reconciled
#print axioms Cochrane.Generality.Links.E_innov_eq_zero
#print axioms Cochrane.Generality.Links.geomQ_eq_geom_value_div
#print axioms Cochrane.Generality.Links.hasDerivAt_disc_of_continuous
#print axioms Cochrane.Generality.Links.tvc_iff_pv_of_engine
#print axioms Cochrane.Generality.Links.expDisc_ratio_eq_disc
#print axioms Cochrane.Generality.Links.e13_discrete_and_continuous
#print axioms Cochrane.Generality.Links.eq_3_26_printed_iff
