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
